-- Prove2me | solution 1 for syracuse_descends_range_948586_952586
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:21:59.404919+00:00
-- url     : https://prove2.me/submissions/8cb08c10-9f29-456d-891f-c020a49c5c34

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


theorem B3964933 : Blo 948586 3964933 := bbase (se 4 (by rfl) ⟨371712, by rfl⟩ : syracuseStep 3964933 = 743425) (by norm_num)
theorem B1015913 : Blo 948586 1015913 := bbase (se 2 (by rfl) ⟨380967, by rfl⟩ : syracuseStep 1015913 = 761935) (by norm_num)
theorem B1605757 : Blo 948586 1605757 := bbase (se 3 (by rfl) ⟨301079, by rfl⟩ : syracuseStep 1605757 = 602159) (by norm_num)
theorem B1605845 : Blo 948586 1605845 := bbase (se 7 (by rfl) ⟨18818, by rfl⟩ : syracuseStep 1605845 = 37637) (by norm_num)
theorem B3211541 : Blo 948586 3211541 := bbase (se 6 (by rfl) ⟨75270, by rfl⟩ : syracuseStep 3211541 = 150541) (by norm_num)
theorem B1016101 : Blo 948586 1016101 := bbase (se 4 (by rfl) ⟨95259, by rfl⟩ : syracuseStep 1016101 = 190519) (by norm_num)
theorem B1605973 : Blo 948586 1605973 := bbase (se 10 (by rfl) ⟨2352, by rfl⟩ : syracuseStep 1605973 = 4705) (by norm_num)
theorem B4882837 : Blo 948586 4882837 := bbase (se 6 (by rfl) ⟨114441, by rfl⟩ : syracuseStep 4882837 = 228883) (by norm_num)
theorem B1606061 : Blo 948586 1606061 := bbase (se 3 (by rfl) ⟨301136, by rfl⟩ : syracuseStep 1606061 = 602273) (by norm_num)
theorem B1081817 : Blo 948586 1081817 := bbase (se 2 (by rfl) ⟨405681, by rfl⟩ : syracuseStep 1081817 = 811363) (by norm_num)
theorem B1802749 : Blo 948586 1802749 := bbase (se 3 (by rfl) ⟨338015, by rfl⟩ : syracuseStep 1802749 = 676031) (by norm_num)
theorem B2032133 : Blo 948586 2032133 := bbase (se 4 (by rfl) ⟨190512, by rfl⟩ : syracuseStep 2032133 = 381025) (by norm_num)
theorem B1606189 : Blo 948586 1606189 := bbase (se 3 (by rfl) ⟨301160, by rfl⟩ : syracuseStep 1606189 = 602321) (by norm_num)
theorem B1606277 : Blo 948586 1606277 := bbase (se 4 (by rfl) ⟨150588, by rfl⟩ : syracuseStep 1606277 = 301177) (by norm_num)
theorem B1802893 : Blo 948586 1802893 := bbase (se 3 (by rfl) ⟨338042, by rfl⟩ : syracuseStep 1802893 = 676085) (by norm_num)
theorem B4063925 : Blo 948586 4063925 := bbase (se 5 (by rfl) ⟨190496, by rfl⟩ : syracuseStep 4063925 = 380993) (by norm_num)
theorem B3211973 : Blo 948586 3211973 := bbase (se 4 (by rfl) ⟨301122, by rfl⟩ : syracuseStep 3211973 = 602245) (by norm_num)
theorem B2032373 : Blo 948586 2032373 := bbase (se 5 (by rfl) ⟨95267, by rfl⟩ : syracuseStep 2032373 = 190535) (by norm_num)
theorem B1606405 : Blo 948586 1606405 := bbase (se 4 (by rfl) ⟨150600, by rfl⟩ : syracuseStep 1606405 = 301201) (by norm_num)
theorem B3605269 : Blo 948586 3605269 := bbase (se 6 (by rfl) ⟨84498, by rfl⟩ : syracuseStep 3605269 = 168997) (by norm_num)
theorem B1803053 : Blo 948586 1803053 := bbase (se 3 (by rfl) ⟨338072, by rfl⟩ : syracuseStep 1803053 = 676145) (by norm_num)
theorem B4817717 : Blo 948586 4817717 := bbase (se 5 (by rfl) ⟨225830, by rfl⟩ : syracuseStep 4817717 = 451661) (by norm_num)
theorem B1606493 : Blo 948586 1606493 := bbase (se 3 (by rfl) ⟨301217, by rfl⟩ : syracuseStep 1606493 = 602435) (by norm_num)
theorem B1737629 : Blo 948586 1737629 := bbase (se 3 (by rfl) ⟨325805, by rfl⟩ : syracuseStep 1737629 = 651611) (by norm_num)
theorem B4064165 : Blo 948586 4064165 := bbase (se 4 (by rfl) ⟨381015, by rfl⟩ : syracuseStep 4064165 = 762031) (by norm_num)
theorem B1803197 : Blo 948586 1803197 := bbase (se 3 (by rfl) ⟨338099, by rfl⟩ : syracuseStep 1803197 = 676199) (by norm_num)
theorem B1606621 : Blo 948586 1606621 := bbase (se 3 (by rfl) ⟨301241, by rfl⟩ : syracuseStep 1606621 = 602483) (by norm_num)
theorem B1606709 : Blo 948586 1606709 := bbase (se 5 (by rfl) ⟨75314, by rfl⟩ : syracuseStep 1606709 = 150629) (by norm_num)
theorem B3605573 : Blo 948586 3605573 := bbase (se 4 (by rfl) ⟨338022, by rfl⟩ : syracuseStep 3605573 = 676045) (by norm_num)
theorem B1016921 : Blo 948586 1016921 := bbase (se 2 (by rfl) ⟨381345, by rfl⟩ : syracuseStep 1016921 = 762691) (by norm_num)
theorem B6095989 : Blo 948586 6095989 := bbase (se 5 (by rfl) ⟨285749, by rfl⟩ : syracuseStep 6095989 = 571499) (by norm_num)
theorem B3212405 : Blo 948586 3212405 := bbase (se 5 (by rfl) ⟨150581, by rfl⟩ : syracuseStep 3212405 = 301163) (by norm_num)
theorem B1606837 : Blo 948586 1606837 := bbase (se 5 (by rfl) ⟨75320, by rfl⟩ : syracuseStep 1606837 = 150641) (by norm_num)
theorem B1803485 : Blo 948586 1803485 := bbase (se 3 (by rfl) ⟨338153, by rfl⟩ : syracuseStep 1803485 = 676307) (by norm_num)
theorem B2032877 : Blo 948586 2032877 := bbase (se 3 (by rfl) ⟨381164, by rfl⟩ : syracuseStep 2032877 = 762329) (by norm_num)
theorem B2032885 : Blo 948586 2032885 := bbase (se 5 (by rfl) ⟨95291, by rfl⟩ : syracuseStep 2032885 = 190583) (by norm_num)
theorem B1606925 : Blo 948586 1606925 := bbase (se 3 (by rfl) ⟨301298, by rfl⟩ : syracuseStep 1606925 = 602597) (by norm_num)
theorem B10257749 : Blo 948586 10257749 := bbase (se 12 (by rfl) ⟨3756, by rfl⟩ : syracuseStep 10257749 = 7513) (by norm_num)
theorem B1803637 : Blo 948586 1803637 := bbase (se 5 (by rfl) ⟨84545, by rfl⟩ : syracuseStep 1803637 = 169091) (by norm_num)
theorem B1607053 : Blo 948586 1607053 := bbase (se 3 (by rfl) ⟨301322, by rfl⟩ : syracuseStep 1607053 = 602645) (by norm_num)
theorem B8455637 : Blo 948586 8455637 := bbase (se 7 (by rfl) ⟨99089, by rfl⟩ : syracuseStep 8455637 = 198179) (by norm_num)
theorem B1607141 : Blo 948586 1607141 := bbase (se 4 (by rfl) ⟨150669, by rfl⟩ : syracuseStep 1607141 = 301339) (by norm_num)
theorem B3212837 : Blo 948586 3212837 := bbase (se 4 (by rfl) ⟨301203, by rfl⟩ : syracuseStep 3212837 = 602407) (by norm_num)
theorem B1607269 : Blo 948586 1607269 := bbase (se 4 (by rfl) ⟨150681, by rfl⟩ : syracuseStep 1607269 = 301363) (by norm_num)
theorem B1803941 : Blo 948586 1803941 := bbase (se 4 (by rfl) ⟨169119, by rfl⟩ : syracuseStep 1803941 = 338239) (by norm_num)
theorem B1607357 : Blo 948586 1607357 := bbase (se 3 (by rfl) ⟨301379, by rfl⟩ : syracuseStep 1607357 = 602759) (by norm_num)
theorem B2164429 : Blo 948586 2164429 := bbase (se 3 (by rfl) ⟨405830, by rfl⟩ : syracuseStep 2164429 = 811661) (by norm_num)
theorem B7309045 : Blo 948586 7309045 := bbase (se 5 (by rfl) ⟨342611, by rfl⟩ : syracuseStep 7309045 = 685223) (by norm_num)
theorem B1607485 : Blo 948586 1607485 := bbase (se 3 (by rfl) ⟨301403, by rfl⟩ : syracuseStep 1607485 = 602807) (by norm_num)
theorem B1083241 : Blo 948586 1083241 := bbase (se 2 (by rfl) ⟨406215, by rfl⟩ : syracuseStep 1083241 = 812431) (by norm_num)
theorem B3901301 : Blo 948586 3901301 := bbase (se 5 (by rfl) ⟨182873, by rfl⟩ : syracuseStep 3901301 = 365747) (by norm_num)
theorem B1083277 : Blo 948586 1083277 := bbase (se 3 (by rfl) ⟨203114, by rfl⟩ : syracuseStep 1083277 = 406229) (by norm_num)
theorem B3213269 : Blo 948586 3213269 := bbase (se 7 (by rfl) ⟨37655, by rfl⟩ : syracuseStep 3213269 = 75311) (by norm_num)
theorem B4819013 : Blo 948586 4819013 := bbase (se 4 (by rfl) ⟨451782, by rfl⟩ : syracuseStep 4819013 = 903565) (by norm_num)
theorem B4950245 : Blo 948586 4950245 := bbase (se 4 (by rfl) ⟨464085, by rfl⟩ : syracuseStep 4950245 = 928171) (by norm_num)
theorem B2034013 : Blo 948586 2034013 := bbase (se 3 (by rfl) ⟨381377, by rfl⟩ : syracuseStep 2034013 = 762755) (by norm_num)
theorem B3213701 : Blo 948586 3213701 := bbase (se 4 (by rfl) ⟨301284, by rfl⟩ : syracuseStep 3213701 = 602569) (by norm_num)
theorem B1804693 : Blo 948586 1804693 := bbase (se 6 (by rfl) ⟨42297, by rfl⟩ : syracuseStep 1804693 = 84595) (by norm_num)
theorem B1739293 : Blo 948586 1739293 := bbase (se 3 (by rfl) ⟨326117, by rfl⟩ : syracuseStep 1739293 = 652235) (by norm_num)
theorem B1804837 : Blo 948586 1804837 := bbase (se 4 (by rfl) ⟨169203, by rfl⟩ : syracuseStep 1804837 = 338407) (by norm_num)
theorem B1804997 : Blo 948586 1804997 := bbase (se 4 (by rfl) ⟨169218, by rfl⟩ : syracuseStep 1804997 = 338437) (by norm_num)
theorem B2034389 : Blo 948586 2034389 := bbase (se 7 (by rfl) ⟨23840, by rfl⟩ : syracuseStep 2034389 = 47681) (by norm_num)
theorem B1084153 : Blo 948586 1084153 := bbase (se 2 (by rfl) ⟨406557, by rfl⟩ : syracuseStep 1084153 = 813115) (by norm_num)
theorem B3214133 : Blo 948586 3214133 := bbase (se 5 (by rfl) ⟨150662, by rfl⟩ : syracuseStep 3214133 = 301325) (by norm_num)
theorem B1805141 : Blo 948586 1805141 := bbase (se 9 (by rfl) ⟨5288, by rfl⟩ : syracuseStep 1805141 = 10577) (by norm_num)
theorem B13863829 : Blo 948586 13863829 := bbase (se 6 (by rfl) ⟨324933, by rfl⟩ : syracuseStep 13863829 = 649867) (by norm_num)
theorem B3050405 : Blo 948586 3050405 := bbase (se 4 (by rfl) ⟨285975, by rfl⟩ : syracuseStep 3050405 = 571951) (by norm_num)
theorem B1805429 : Blo 948586 1805429 := bbase (se 5 (by rfl) ⟨84629, by rfl⟩ : syracuseStep 1805429 = 169259) (by norm_num)
theorem B3607685 : Blo 948586 3607685 := bbase (se 4 (by rfl) ⟨338220, by rfl⟩ : syracuseStep 3607685 = 676441) (by norm_num)
theorem B4066453 : Blo 948586 4066453 := bbase (se 6 (by rfl) ⟨95307, by rfl⟩ : syracuseStep 4066453 = 190615) (by norm_num)
theorem B3214565 : Blo 948586 3214565 := bbase (se 4 (by rfl) ⟨301365, by rfl⟩ : syracuseStep 3214565 = 602731) (by norm_num)
theorem B1805581 : Blo 948586 1805581 := bbase (se 3 (by rfl) ⟨338546, by rfl⟩ : syracuseStep 1805581 = 677093) (by norm_num)
theorem B2198869 : Blo 948586 2198869 := bbase (se 11 (by rfl) ⟨1610, by rfl⟩ : syracuseStep 2198869 = 3221) (by norm_num)
theorem B4820309 : Blo 948586 4820309 := bbase (se 11 (by rfl) ⟨3530, by rfl⟩ : syracuseStep 4820309 = 7061) (by norm_num)
theorem B3607973 : Blo 948586 3607973 := bbase (se 4 (by rfl) ⟨338247, by rfl⟩ : syracuseStep 3607973 = 676495) (by norm_num)
theorem B6852053 : Blo 948586 6852053 := bbase (se 7 (by rfl) ⟨80297, by rfl⟩ : syracuseStep 6852053 = 160595) (by norm_num)
theorem B1805885 : Blo 948586 1805885 := bbase (se 3 (by rfl) ⟨338603, by rfl⟩ : syracuseStep 1805885 = 677207) (by norm_num)
theorem B7212725 : Blo 948586 7212725 := bbase (se 5 (by rfl) ⟨338096, by rfl⟩ : syracuseStep 7212725 = 676193) (by norm_num)
theorem B1085185 : Blo 948586 1085185 := bbase (se 2 (by rfl) ⟨406944, by rfl⟩ : syracuseStep 1085185 = 813889) (by norm_num)
theorem B14094485 : Blo 948586 14094485 := bbase (se 6 (by rfl) ⟨330339, by rfl⟩ : syracuseStep 14094485 = 660679) (by norm_num)
theorem B3051685 : Blo 948586 3051685 := bbase (se 4 (by rfl) ⟨286095, by rfl⟩ : syracuseStep 3051685 = 572191) (by norm_num)
theorem B1806637 : Blo 948586 1806637 := bbase (se 3 (by rfl) ⟨338744, by rfl⟩ : syracuseStep 1806637 = 677489) (by norm_num)
theorem B2134349 : Blo 948586 2134349 := bbase (se 3 (by rfl) ⟨400190, by rfl⟩ : syracuseStep 2134349 = 800381) (by norm_num)
theorem B2134421 : Blo 948586 2134421 := bbase (se 6 (by rfl) ⟨50025, by rfl⟩ : syracuseStep 2134421 = 100051) (by norm_num)
theorem B1806781 : Blo 948586 1806781 := bbase (se 3 (by rfl) ⟨338771, by rfl⟩ : syracuseStep 1806781 = 677543) (by norm_num)
theorem B2134493 : Blo 948586 2134493 := bbase (se 3 (by rfl) ⟨400217, by rfl⟩ : syracuseStep 2134493 = 800435) (by norm_num)
theorem B1446365 : Blo 948586 1446365 := bbase (se 3 (by rfl) ⟨271193, by rfl⟩ : syracuseStep 1446365 = 542387) (by norm_num)
theorem B1085977 : Blo 948586 1085977 := bbase (se 2 (by rfl) ⟨407241, by rfl⟩ : syracuseStep 1085977 = 814483) (by norm_num)
theorem B2134565 : Blo 948586 2134565 := bbase (se 4 (by rfl) ⟨200115, by rfl⟩ : syracuseStep 2134565 = 400231) (by norm_num)
theorem B3609157 : Blo 948586 3609157 := bbase (se 4 (by rfl) ⟨338358, by rfl⟩ : syracuseStep 3609157 = 676717) (by norm_num)
theorem B1806941 : Blo 948586 1806941 := bbase (se 3 (by rfl) ⟨338801, by rfl⟩ : syracuseStep 1806941 = 677603) (by norm_num)
theorem B4067941 : Blo 948586 4067941 := bbase (se 4 (by rfl) ⟨381369, by rfl⟩ : syracuseStep 4067941 = 762739) (by norm_num)
theorem B4821605 : Blo 948586 4821605 := bbase (se 4 (by rfl) ⟨452025, by rfl⟩ : syracuseStep 4821605 = 904051) (by norm_num)
theorem B2134637 : Blo 948586 2134637 := bbase (se 3 (by rfl) ⟨400244, by rfl⟩ : syracuseStep 2134637 = 800489) (by norm_num)
theorem B4067957 : Blo 948586 4067957 := bbase (se 5 (by rfl) ⟨190685, by rfl⟩ : syracuseStep 4067957 = 381371) (by norm_num)
theorem B2134709 : Blo 948586 2134709 := bbase (se 5 (by rfl) ⟨100064, by rfl⟩ : syracuseStep 2134709 = 200129) (by norm_num)
theorem B1807085 : Blo 948586 1807085 := bbase (se 3 (by rfl) ⟨338828, by rfl⟩ : syracuseStep 1807085 = 677657) (by norm_num)
theorem B2134781 : Blo 948586 2134781 := bbase (se 3 (by rfl) ⟨400271, by rfl⟩ : syracuseStep 2134781 = 800543) (by norm_num)
theorem B2134853 : Blo 948586 2134853 := bbase (se 4 (by rfl) ⟨200142, by rfl⟩ : syracuseStep 2134853 = 400285) (by norm_num)
theorem B3609461 : Blo 948586 3609461 := bbase (se 5 (by rfl) ⟨169193, by rfl⟩ : syracuseStep 3609461 = 338387) (by norm_num)
theorem B2134925 : Blo 948586 2134925 := bbase (se 3 (by rfl) ⟨400298, by rfl⟩ : syracuseStep 2134925 = 800597) (by norm_num)
theorem B2134997 : Blo 948586 2134997 := bbase (se 7 (by rfl) ⟨25019, by rfl⟩ : syracuseStep 2134997 = 50039) (by norm_num)
theorem B1807373 : Blo 948586 1807373 := bbase (se 3 (by rfl) ⟨338882, by rfl⟩ : syracuseStep 1807373 = 677765) (by norm_num)
theorem B2135069 : Blo 948586 2135069 := bbase (se 3 (by rfl) ⟨400325, by rfl⟩ : syracuseStep 2135069 = 800651) (by norm_num)
theorem B2135141 : Blo 948586 2135141 := bbase (se 4 (by rfl) ⟨200169, by rfl⟩ : syracuseStep 2135141 = 400339) (by norm_num)
theorem B1807525 : Blo 948586 1807525 := bbase (se 4 (by rfl) ⟨169455, by rfl⟩ : syracuseStep 1807525 = 338911) (by norm_num)
theorem B2135213 : Blo 948586 2135213 := bbase (se 3 (by rfl) ⟨400352, by rfl⟩ : syracuseStep 2135213 = 800705) (by norm_num)
theorem B2888885 : Blo 948586 2888885 := bbase (se 5 (by rfl) ⟨135416, by rfl⟩ : syracuseStep 2888885 = 270833) (by norm_num)
theorem B2135285 : Blo 948586 2135285 := bbase (se 5 (by rfl) ⟨100091, by rfl⟩ : syracuseStep 2135285 = 200183) (by norm_num)
theorem B1545493 : Blo 948586 1545493 := bbase (se 6 (by rfl) ⟨36222, by rfl⟩ : syracuseStep 1545493 = 72445) (by norm_num)
theorem B1283365 : Blo 948586 1283365 := bbase (se 4 (by rfl) ⟨120315, by rfl⟩ : syracuseStep 1283365 = 240631) (by norm_num)
theorem B2135357 : Blo 948586 2135357 := bbase (se 3 (by rfl) ⟨400379, by rfl⟩ : syracuseStep 2135357 = 800759) (by norm_num)
theorem B4560229 : Blo 948586 4560229 := bbase (se 4 (by rfl) ⟨427521, by rfl⟩ : syracuseStep 4560229 = 855043) (by norm_num)
theorem B1217917 : Blo 948586 1217917 := bbase (se 3 (by rfl) ⟨228359, by rfl⟩ : syracuseStep 1217917 = 456719) (by norm_num)
theorem B2135429 : Blo 948586 2135429 := bbase (se 4 (by rfl) ⟨200196, by rfl⟩ : syracuseStep 2135429 = 400393) (by norm_num)
theorem B2135501 : Blo 948586 2135501 := bbase (se 3 (by rfl) ⟨400406, by rfl⟩ : syracuseStep 2135501 = 800813) (by norm_num)
theorem B1807829 : Blo 948586 1807829 := bbase (se 7 (by rfl) ⟨21185, by rfl⟩ : syracuseStep 1807829 = 42371) (by norm_num)
theorem B2135573 : Blo 948586 2135573 := bbase (se 6 (by rfl) ⟨50052, by rfl⟩ : syracuseStep 2135573 = 100105) (by norm_num)
theorem B2135645 : Blo 948586 2135645 := bbase (se 3 (by rfl) ⟨400433, by rfl⟩ : syracuseStep 2135645 = 800867) (by norm_num)
theorem B2135717 : Blo 948586 2135717 := bbase (se 4 (by rfl) ⟨200223, by rfl⟩ : syracuseStep 2135717 = 400447) (by norm_num)
theorem B1709741 : Blo 948586 1709741 := bbase (se 3 (by rfl) ⟨320576, by rfl⟩ : syracuseStep 1709741 = 641153) (by norm_num)
theorem B1218277 : Blo 948586 1218277 := bbase (se 4 (by rfl) ⟨114213, by rfl⟩ : syracuseStep 1218277 = 228427) (by norm_num)
theorem B2135789 : Blo 948586 2135789 := bbase (se 3 (by rfl) ⟨400460, by rfl⟩ : syracuseStep 2135789 = 800921) (by norm_num)
theorem B2135861 : Blo 948586 2135861 := bbase (se 5 (by rfl) ⟨100118, by rfl⟩ : syracuseStep 2135861 = 200237) (by norm_num)
theorem B2135933 : Blo 948586 2135933 := bbase (se 3 (by rfl) ⟨400487, by rfl⟩ : syracuseStep 2135933 = 800975) (by norm_num)
theorem B1709957 : Blo 948586 1709957 := bbase (se 4 (by rfl) ⟨160308, by rfl⟩ : syracuseStep 1709957 = 320617) (by norm_num)
theorem B989069 : Blo 948586 989069 := bbase (se 3 (by rfl) ⟨185450, by rfl⟩ : syracuseStep 989069 = 370901) (by norm_num)
theorem B2136005 : Blo 948586 2136005 := bbase (se 4 (by rfl) ⟨200250, by rfl⟩ : syracuseStep 2136005 = 400501) (by norm_num)
theorem B1710029 : Blo 948586 1710029 := bbase (se 3 (by rfl) ⟨320630, by rfl⟩ : syracuseStep 1710029 = 641261) (by norm_num)
theorem B2136077 : Blo 948586 2136077 := bbase (se 3 (by rfl) ⟨400514, by rfl⟩ : syracuseStep 2136077 = 801029) (by norm_num)
theorem B1710109 : Blo 948586 1710109 := bbase (se 3 (by rfl) ⟨320645, by rfl⟩ : syracuseStep 1710109 = 641291) (by norm_num)
theorem B2136149 : Blo 948586 2136149 := bbase (se 8 (by rfl) ⟨12516, by rfl⟩ : syracuseStep 2136149 = 25033) (by norm_num)
theorem B1710173 : Blo 948586 1710173 := bbase (se 3 (by rfl) ⟨320657, by rfl⟩ : syracuseStep 1710173 = 641315) (by norm_num)
theorem B3479669 : Blo 948586 3479669 := bbase (se 5 (by rfl) ⟨163109, by rfl⟩ : syracuseStep 3479669 = 326219) (by norm_num)
theorem B2136221 : Blo 948586 2136221 := bbase (se 3 (by rfl) ⟨400541, by rfl⟩ : syracuseStep 2136221 = 801083) (by norm_num)
theorem B2136293 : Blo 948586 2136293 := bbase (se 4 (by rfl) ⟨200277, by rfl⟩ : syracuseStep 2136293 = 400555) (by norm_num)
theorem B1448165 : Blo 948586 1448165 := bbase (se 4 (by rfl) ⟨135765, by rfl⟩ : syracuseStep 1448165 = 271531) (by norm_num)
theorem B5773589 : Blo 948586 5773589 := bbase (se 6 (by rfl) ⟨135318, by rfl⟩ : syracuseStep 5773589 = 270637) (by norm_num)
theorem B2136365 : Blo 948586 2136365 := bbase (se 3 (by rfl) ⟨400568, by rfl⟩ : syracuseStep 2136365 = 801137) (by norm_num)
theorem B2136437 : Blo 948586 2136437 := bbase (se 5 (by rfl) ⟨100145, by rfl⟩ : syracuseStep 2136437 = 200291) (by norm_num)
theorem B1710461 : Blo 948586 1710461 := bbase (se 3 (by rfl) ⟨320711, by rfl⟩ : syracuseStep 1710461 = 641423) (by norm_num)
theorem B2136509 : Blo 948586 2136509 := bbase (se 3 (by rfl) ⟨400595, by rfl⟩ : syracuseStep 2136509 = 801191) (by norm_num)
theorem B2136581 : Blo 948586 2136581 := bbase (se 4 (by rfl) ⟨200304, by rfl⟩ : syracuseStep 2136581 = 400609) (by norm_num)
theorem B2136653 : Blo 948586 2136653 := bbase (se 3 (by rfl) ⟨400622, by rfl⟩ : syracuseStep 2136653 = 801245) (by norm_num)
theorem B2136725 : Blo 948586 2136725 := bbase (se 6 (by rfl) ⟨50079, by rfl⟩ : syracuseStep 2136725 = 100159) (by norm_num)
theorem B989869 : Blo 948586 989869 := bbase (se 3 (by rfl) ⟨185600, by rfl⟩ : syracuseStep 989869 = 371201) (by norm_num)
theorem B2136797 : Blo 948586 2136797 := bbase (se 3 (by rfl) ⟨400649, by rfl⟩ : syracuseStep 2136797 = 801299) (by norm_num)
theorem B2136869 : Blo 948586 2136869 := bbase (se 4 (by rfl) ⟨200331, by rfl⟩ : syracuseStep 2136869 = 400663) (by norm_num)
theorem B2136941 : Blo 948586 2136941 := bbase (se 3 (by rfl) ⟨400676, by rfl⟩ : syracuseStep 2136941 = 801353) (by norm_num)
theorem B2137013 : Blo 948586 2137013 := bbase (se 5 (by rfl) ⟨100172, by rfl⟩ : syracuseStep 2137013 = 200345) (by norm_num)
theorem B3611573 : Blo 948586 3611573 := bbase (se 5 (by rfl) ⟨169292, by rfl⟩ : syracuseStep 3611573 = 338585) (by norm_num)
theorem B2137085 : Blo 948586 2137085 := bbase (se 3 (by rfl) ⟨400703, by rfl⟩ : syracuseStep 2137085 = 801407) (by norm_num)
theorem B2137157 : Blo 948586 2137157 := bbase (se 4 (by rfl) ⟨200358, by rfl⟩ : syracuseStep 2137157 = 400717) (by norm_num)
theorem B3251285 : Blo 948586 3251285 := bbase (se 8 (by rfl) ⟨19050, by rfl⟩ : syracuseStep 3251285 = 38101) (by norm_num)
theorem B2137229 : Blo 948586 2137229 := bbase (se 3 (by rfl) ⟨400730, by rfl⟩ : syracuseStep 2137229 = 801461) (by norm_num)
theorem B2137301 : Blo 948586 2137301 := bbase (se 7 (by rfl) ⟨25046, by rfl⟩ : syracuseStep 2137301 = 50093) (by norm_num)
theorem B3611861 : Blo 948586 3611861 := bbase (se 7 (by rfl) ⟨42326, by rfl⟩ : syracuseStep 3611861 = 84653) (by norm_num)
theorem B2137373 : Blo 948586 2137373 := bbase (se 3 (by rfl) ⟨400757, by rfl⟩ : syracuseStep 2137373 = 801515) (by norm_num)
theorem B2137445 : Blo 948586 2137445 := bbase (se 4 (by rfl) ⟨200385, by rfl⟩ : syracuseStep 2137445 = 400771) (by norm_num)
theorem B2891173 : Blo 948586 2891173 := bbase (se 4 (by rfl) ⟨271047, by rfl⟩ : syracuseStep 2891173 = 542095) (by norm_num)
theorem B2137517 : Blo 948586 2137517 := bbase (se 3 (by rfl) ⟨400784, by rfl⟩ : syracuseStep 2137517 = 801569) (by norm_num)
theorem B2137589 : Blo 948586 2137589 := bbase (se 5 (by rfl) ⟨100199, by rfl⟩ : syracuseStep 2137589 = 200399) (by norm_num)
theorem B2137661 : Blo 948586 2137661 := bbase (se 3 (by rfl) ⟨400811, by rfl⟩ : syracuseStep 2137661 = 801623) (by norm_num)
theorem B2137733 : Blo 948586 2137733 := bbase (se 4 (by rfl) ⟨200412, by rfl⟩ : syracuseStep 2137733 = 400825) (by norm_num)
theorem B1351333 : Blo 948586 1351333 := bbase (se 4 (by rfl) ⟨126687, by rfl⟩ : syracuseStep 1351333 = 253375) (by norm_num)
theorem B1711781 : Blo 948586 1711781 := bbase (se 4 (by rfl) ⟨160479, by rfl⟩ : syracuseStep 1711781 = 320959) (by norm_num)
theorem B2137805 : Blo 948586 2137805 := bbase (se 3 (by rfl) ⟨400838, by rfl⟩ : syracuseStep 2137805 = 801677) (by norm_num)
theorem B2137877 : Blo 948586 2137877 := bbase (se 6 (by rfl) ⟨50106, by rfl⟩ : syracuseStep 2137877 = 100213) (by norm_num)
theorem B991033 : Blo 948586 991033 := bbase (se 2 (by rfl) ⟨371637, by rfl⟩ : syracuseStep 991033 = 743275) (by norm_num)
theorem B2137949 : Blo 948586 2137949 := bbase (se 3 (by rfl) ⟨400865, by rfl⟩ : syracuseStep 2137949 = 801731) (by norm_num)
theorem B2138021 : Blo 948586 2138021 := bbase (se 4 (by rfl) ⟨200439, by rfl⟩ : syracuseStep 2138021 = 400879) (by norm_num)
theorem B2138093 : Blo 948586 2138093 := bbase (se 3 (by rfl) ⟨400892, by rfl⟩ : syracuseStep 2138093 = 801785) (by norm_num)
theorem B1351669 : Blo 948586 1351669 := bbase (se 5 (by rfl) ⟨63359, by rfl⟩ : syracuseStep 1351669 = 126719) (by norm_num)
theorem B6168565 : Blo 948586 6168565 := bbase (se 5 (by rfl) ⟨289151, by rfl⟩ : syracuseStep 6168565 = 578303) (by norm_num)
theorem B7315445 : Blo 948586 7315445 := bbase (se 5 (by rfl) ⟨342911, by rfl⟩ : syracuseStep 7315445 = 685823) (by norm_num)
theorem B1220617 : Blo 948586 1220617 := bbase (se 2 (by rfl) ⟨457731, by rfl⟩ : syracuseStep 1220617 = 915463) (by norm_num)
theorem B2138165 : Blo 948586 2138165 := bbase (se 5 (by rfl) ⟨100226, by rfl⟩ : syracuseStep 2138165 = 200453) (by norm_num)
theorem B2138237 : Blo 948586 2138237 := bbase (se 3 (by rfl) ⟨400919, by rfl⟩ : syracuseStep 2138237 = 801839) (by norm_num)
theorem B9117845 : Blo 948586 9117845 := bbase (se 6 (by rfl) ⟨213699, by rfl⟩ : syracuseStep 9117845 = 427399) (by norm_num)
theorem B2138309 : Blo 948586 2138309 := bbase (se 4 (by rfl) ⟨200466, by rfl⟩ : syracuseStep 2138309 = 400933) (by norm_num)
theorem B1351885 : Blo 948586 1351885 := bbase (se 3 (by rfl) ⟨253478, by rfl⟩ : syracuseStep 1351885 = 506957) (by norm_num)
theorem B2138381 : Blo 948586 2138381 := bbase (se 3 (by rfl) ⟨400946, by rfl⟩ : syracuseStep 2138381 = 801893) (by norm_num)
theorem B6103349 : Blo 948586 6103349 := bbase (se 5 (by rfl) ⟨286094, by rfl⟩ : syracuseStep 6103349 = 572189) (by norm_num)
theorem B2138453 : Blo 948586 2138453 := bbase (se 10 (by rfl) ⟨3132, by rfl⟩ : syracuseStep 2138453 = 6265) (by norm_num)
theorem B2892133 : Blo 948586 2892133 := bbase (se 4 (by rfl) ⟨271137, by rfl⟩ : syracuseStep 2892133 = 542275) (by norm_num)
theorem B3613045 : Blo 948586 3613045 := bbase (se 5 (by rfl) ⟨169361, by rfl⟩ : syracuseStep 3613045 = 338723) (by norm_num)
theorem B1286533 : Blo 948586 1286533 := bbase (se 4 (by rfl) ⟨120612, by rfl⟩ : syracuseStep 1286533 = 241225) (by norm_num)
theorem B2138525 : Blo 948586 2138525 := bbase (se 3 (by rfl) ⟨400973, by rfl⟩ : syracuseStep 2138525 = 801947) (by norm_num)
theorem B8135093 : Blo 948586 8135093 := bbase (se 5 (by rfl) ⟨381332, by rfl⟩ : syracuseStep 8135093 = 762665) (by norm_num)
theorem B2138597 : Blo 948586 2138597 := bbase (se 4 (by rfl) ⟨200493, by rfl⟩ : syracuseStep 2138597 = 400987) (by norm_num)
theorem B14623253 : Blo 948586 14623253 := bbase (se 6 (by rfl) ⟨342732, by rfl⟩ : syracuseStep 14623253 = 685465) (by norm_num)
theorem B2138669 : Blo 948586 2138669 := bbase (se 3 (by rfl) ⟨401000, by rfl⟩ : syracuseStep 2138669 = 802001) (by norm_num)
theorem B1352261 : Blo 948586 1352261 := bbase (se 4 (by rfl) ⟨126774, by rfl⟩ : syracuseStep 1352261 = 253549) (by norm_num)
theorem B2138741 : Blo 948586 2138741 := bbase (se 5 (by rfl) ⟨100253, by rfl⟩ : syracuseStep 2138741 = 200507) (by norm_num)
theorem B3613349 : Blo 948586 3613349 := bbase (se 4 (by rfl) ⟨338751, by rfl⟩ : syracuseStep 3613349 = 677503) (by norm_num)
theorem B5415605 : Blo 948586 5415605 := bbase (se 5 (by rfl) ⟨253856, by rfl⟩ : syracuseStep 5415605 = 507713) (by norm_num)
theorem B2138813 : Blo 948586 2138813 := bbase (se 3 (by rfl) ⟨401027, by rfl⟩ : syracuseStep 2138813 = 802055) (by norm_num)
theorem B2138885 : Blo 948586 2138885 := bbase (se 4 (by rfl) ⟨200520, by rfl⟩ : syracuseStep 2138885 = 401041) (by norm_num)
theorem B5219093 : Blo 948586 5219093 := bbase (se 6 (by rfl) ⟨122322, by rfl⟩ : syracuseStep 5219093 = 244645) (by norm_num)
theorem B2138957 : Blo 948586 2138957 := bbase (se 3 (by rfl) ⟨401054, by rfl⟩ : syracuseStep 2138957 = 802109) (by norm_num)
theorem B6595445 : Blo 948586 6595445 := bbase (se 5 (by rfl) ⟨309161, by rfl⟩ : syracuseStep 6595445 = 618323) (by norm_num)
theorem B2139029 : Blo 948586 2139029 := bbase (se 6 (by rfl) ⟨50133, by rfl⟩ : syracuseStep 2139029 = 100267) (by norm_num)
theorem B2139101 : Blo 948586 2139101 := bbase (se 3 (by rfl) ⟨401081, by rfl⟩ : syracuseStep 2139101 = 802163) (by norm_num)
theorem B2401285 : Blo 948586 2401285 := bbase (se 4 (by rfl) ⟨225120, by rfl⟩ : syracuseStep 2401285 = 450241) (by norm_num)
theorem B2139173 : Blo 948586 2139173 := bbase (se 4 (by rfl) ⟨200547, by rfl⟩ : syracuseStep 2139173 = 401095) (by norm_num)
theorem B2139245 : Blo 948586 2139245 := bbase (se 3 (by rfl) ⟨401108, by rfl⟩ : syracuseStep 2139245 = 802217) (by norm_num)
theorem B2401397 : Blo 948586 2401397 := bbase (se 5 (by rfl) ⟨112565, by rfl⟩ : syracuseStep 2401397 = 225131) (by norm_num)
theorem B4564133 : Blo 948586 4564133 := bbase (se 4 (by rfl) ⟨427887, by rfl⟩ : syracuseStep 4564133 = 855775) (by norm_num)
theorem B2139317 : Blo 948586 2139317 := bbase (se 5 (by rfl) ⟨100280, by rfl⟩ : syracuseStep 2139317 = 200561) (by norm_num)
theorem B4334789 : Blo 948586 4334789 := bbase (se 4 (by rfl) ⟨406386, by rfl⟩ : syracuseStep 4334789 = 812773) (by norm_num)
theorem B2172101 : Blo 948586 2172101 := bbase (se 4 (by rfl) ⟨203634, by rfl⟩ : syracuseStep 2172101 = 407269) (by norm_num)
theorem B9250037 : Blo 948586 9250037 := bbase (se 5 (by rfl) ⟨433595, by rfl⟩ : syracuseStep 9250037 = 867191) (by norm_num)
theorem B2139389 : Blo 948586 2139389 := bbase (se 3 (by rfl) ⟨401135, by rfl⟩ : syracuseStep 2139389 = 802271) (by norm_num)
theorem B2401589 : Blo 948586 2401589 := bbase (se 5 (by rfl) ⟨112574, by rfl⟩ : syracuseStep 2401589 = 225149) (by norm_num)
theorem B2139461 : Blo 948586 2139461 := bbase (se 4 (by rfl) ⟨200574, by rfl⟩ : syracuseStep 2139461 = 401149) (by norm_num)
theorem B2139533 : Blo 948586 2139533 := bbase (se 3 (by rfl) ⟨401162, by rfl⟩ : syracuseStep 2139533 = 802325) (by norm_num)
theorem B1222033 : Blo 948586 1222033 := bbase (se 2 (by rfl) ⟨458262, by rfl⟩ : syracuseStep 1222033 = 916525) (by norm_num)
theorem B2139605 : Blo 948586 2139605 := bbase (se 7 (by rfl) ⟨25073, by rfl⟩ : syracuseStep 2139605 = 50147) (by norm_num)
theorem B2139677 : Blo 948586 2139677 := bbase (se 3 (by rfl) ⟨401189, by rfl⟩ : syracuseStep 2139677 = 802379) (by norm_num)
theorem B2139749 : Blo 948586 2139749 := bbase (se 4 (by rfl) ⟨200601, by rfl⟩ : syracuseStep 2139749 = 401203) (by norm_num)
theorem B6497909 : Blo 948586 6497909 := bbase (se 5 (by rfl) ⟨304589, by rfl⟩ : syracuseStep 6497909 = 609179) (by norm_num)
theorem B2401933 : Blo 948586 2401933 := bbase (se 3 (by rfl) ⟨450362, by rfl⟩ : syracuseStep 2401933 = 900725) (by norm_num)
theorem B1713805 : Blo 948586 1713805 := bbase (se 3 (by rfl) ⟨321338, by rfl⟩ : syracuseStep 1713805 = 642677) (by norm_num)
theorem B2139821 : Blo 948586 2139821 := bbase (se 3 (by rfl) ⟨401216, by rfl⟩ : syracuseStep 2139821 = 802433) (by norm_num)
theorem B2139893 : Blo 948586 2139893 := bbase (se 5 (by rfl) ⟨100307, by rfl⟩ : syracuseStep 2139893 = 200615) (by norm_num)
theorem B2402045 : Blo 948586 2402045 := bbase (se 3 (by rfl) ⟨450383, by rfl⟩ : syracuseStep 2402045 = 900767) (by norm_num)
theorem B1713973 : Blo 948586 1713973 := bbase (se 5 (by rfl) ⟨80342, by rfl⟩ : syracuseStep 1713973 = 160685) (by norm_num)
theorem B2139965 : Blo 948586 2139965 := bbase (se 3 (by rfl) ⟨401243, by rfl⟩ : syracuseStep 2139965 = 802487) (by norm_num)
theorem B2140037 : Blo 948586 2140037 := bbase (se 4 (by rfl) ⟨200628, by rfl⟩ : syracuseStep 2140037 = 401257) (by norm_num)
theorem B1157005 : Blo 948586 1157005 := bbase (se 3 (by rfl) ⟨216938, by rfl⟩ : syracuseStep 1157005 = 433877) (by norm_num)
theorem B2467757 : Blo 948586 2467757 := bbase (se 3 (by rfl) ⟨462704, by rfl⟩ : syracuseStep 2467757 = 925409) (by norm_num)
theorem B2402237 : Blo 948586 2402237 := bbase (se 3 (by rfl) ⟨450419, by rfl⟩ : syracuseStep 2402237 = 900839) (by norm_num)
theorem B2140109 : Blo 948586 2140109 := bbase (se 3 (by rfl) ⟨401270, by rfl⟩ : syracuseStep 2140109 = 802541) (by norm_num)
theorem B1353685 : Blo 948586 1353685 := bbase (se 7 (by rfl) ⟨15863, by rfl⟩ : syracuseStep 1353685 = 31727) (by norm_num)
theorem B2140181 : Blo 948586 2140181 := bbase (se 6 (by rfl) ⟨50160, by rfl⟩ : syracuseStep 2140181 = 100321) (by norm_num)
theorem B2140253 : Blo 948586 2140253 := bbase (se 3 (by rfl) ⟨401297, by rfl⟩ : syracuseStep 2140253 = 802595) (by norm_num)
theorem B2140325 : Blo 948586 2140325 := bbase (se 4 (by rfl) ⟨200655, by rfl⟩ : syracuseStep 2140325 = 401311) (by norm_num)
theorem B2140397 : Blo 948586 2140397 := bbase (se 3 (by rfl) ⟨401324, by rfl⟩ : syracuseStep 2140397 = 802649) (by norm_num)
theorem B2402581 : Blo 948586 2402581 := bbase (se 6 (by rfl) ⟨56310, by rfl⟩ : syracuseStep 2402581 = 112621) (by norm_num)
theorem B2140469 : Blo 948586 2140469 := bbase (se 5 (by rfl) ⟨100334, by rfl⟩ : syracuseStep 2140469 = 200669) (by norm_num)
theorem B1714549 : Blo 948586 1714549 := bbase (se 5 (by rfl) ⟨80369, by rfl⟩ : syracuseStep 1714549 = 160739) (by norm_num)
theorem B2140541 : Blo 948586 2140541 := bbase (se 3 (by rfl) ⟨401351, by rfl⟩ : syracuseStep 2140541 = 802703) (by norm_num)
theorem B2402693 : Blo 948586 2402693 := bbase (se 4 (by rfl) ⟨225252, by rfl⟩ : syracuseStep 2402693 = 450505) (by norm_num)
theorem B2140613 : Blo 948586 2140613 := bbase (se 4 (by rfl) ⟨200682, by rfl⟩ : syracuseStep 2140613 = 401365) (by norm_num)
theorem B2140685 : Blo 948586 2140685 := bbase (se 3 (by rfl) ⟨401378, by rfl⟩ : syracuseStep 2140685 = 802757) (by norm_num)
theorem B1354277 : Blo 948586 1354277 := bbase (se 4 (by rfl) ⟨126963, by rfl⟩ : syracuseStep 1354277 = 253927) (by norm_num)
theorem B2402885 : Blo 948586 2402885 := bbase (se 4 (by rfl) ⟨225270, by rfl⟩ : syracuseStep 2402885 = 450541) (by norm_num)
theorem B4336213 : Blo 948586 4336213 := bbase (se 8 (by rfl) ⟨25407, by rfl⟩ : syracuseStep 4336213 = 50815) (by norm_num)
theorem B2140757 : Blo 948586 2140757 := bbase (se 8 (by rfl) ⟨12543, by rfl⟩ : syracuseStep 2140757 = 25087) (by norm_num)
theorem B5778037 : Blo 948586 5778037 := bbase (se 5 (by rfl) ⟨270845, by rfl⟩ : syracuseStep 5778037 = 541691) (by norm_num)
theorem B1354357 : Blo 948586 1354357 := bbase (se 5 (by rfl) ⟨63485, by rfl⟩ : syracuseStep 1354357 = 126971) (by norm_num)
theorem B2140829 : Blo 948586 2140829 := bbase (se 3 (by rfl) ⟨401405, by rfl⟩ : syracuseStep 2140829 = 802811) (by norm_num)
theorem B2140901 : Blo 948586 2140901 := bbase (se 4 (by rfl) ⟨200709, by rfl⟩ : syracuseStep 2140901 = 401419) (by norm_num)
theorem B3615461 : Blo 948586 3615461 := bbase (se 4 (by rfl) ⟨338949, by rfl⟩ : syracuseStep 3615461 = 677899) (by norm_num)
theorem B1354477 : Blo 948586 1354477 := bbase (se 3 (by rfl) ⟨253964, by rfl⟩ : syracuseStep 1354477 = 507929) (by norm_num)
theorem B2140973 : Blo 948586 2140973 := bbase (se 3 (by rfl) ⟨401432, by rfl⟩ : syracuseStep 2140973 = 802865) (by norm_num)
theorem B3418949 : Blo 948586 3418949 := bbase (se 4 (by rfl) ⟨320526, by rfl⟩ : syracuseStep 3418949 = 641053) (by norm_num)
theorem B1354573 : Blo 948586 1354573 := bbase (se 3 (by rfl) ⟨253982, by rfl⟩ : syracuseStep 1354573 = 507965) (by norm_num)
theorem B2141045 : Blo 948586 2141045 := bbase (se 5 (by rfl) ⟨100361, by rfl⟩ : syracuseStep 2141045 = 200723) (by norm_num)
theorem B2403229 : Blo 948586 2403229 := bbase (se 3 (by rfl) ⟨450605, by rfl⟩ : syracuseStep 2403229 = 901211) (by norm_num)
theorem B2141117 : Blo 948586 2141117 := bbase (se 3 (by rfl) ⟨401459, by rfl⟩ : syracuseStep 2141117 = 802919) (by norm_num)
theorem B1715189 : Blo 948586 1715189 := bbase (se 5 (by rfl) ⟨80399, by rfl⟩ : syracuseStep 1715189 = 160799) (by norm_num)
theorem B2141189 : Blo 948586 2141189 := bbase (se 4 (by rfl) ⟨200736, by rfl⟩ : syracuseStep 2141189 = 401473) (by norm_num)
theorem B3615749 : Blo 948586 3615749 := bbase (se 4 (by rfl) ⟨338976, by rfl⟩ : syracuseStep 3615749 = 677953) (by norm_num)
theorem B2403341 : Blo 948586 2403341 := bbase (se 3 (by rfl) ⟨450626, by rfl⟩ : syracuseStep 2403341 = 901253) (by norm_num)
theorem B2894869 : Blo 948586 2894869 := bbase (se 6 (by rfl) ⟨67848, by rfl⟩ : syracuseStep 2894869 = 135697) (by norm_num)
theorem B2141261 : Blo 948586 2141261 := bbase (se 3 (by rfl) ⟨401486, by rfl⟩ : syracuseStep 2141261 = 802973) (by norm_num)
theorem B4566149 : Blo 948586 4566149 := bbase (se 4 (by rfl) ⟨428076, by rfl⟩ : syracuseStep 4566149 = 856153) (by norm_num)
theorem B2141333 : Blo 948586 2141333 := bbase (se 6 (by rfl) ⟨50187, by rfl⟩ : syracuseStep 2141333 = 100375) (by norm_num)
theorem B1715357 : Blo 948586 1715357 := bbase (se 3 (by rfl) ⟨321629, by rfl⟩ : syracuseStep 1715357 = 643259) (by norm_num)
theorem B2403533 : Blo 948586 2403533 := bbase (se 3 (by rfl) ⟨450662, by rfl⟩ : syracuseStep 2403533 = 901325) (by norm_num)
theorem B2141405 : Blo 948586 2141405 := bbase (se 3 (by rfl) ⟨401513, by rfl⟩ : syracuseStep 2141405 = 803027) (by norm_num)
theorem B7220501 : Blo 948586 7220501 := bbase (se 6 (by rfl) ⟨169230, by rfl⟩ : syracuseStep 7220501 = 338461) (by norm_num)
theorem B2141477 : Blo 948586 2141477 := bbase (se 4 (by rfl) ⟨200763, by rfl⟩ : syracuseStep 2141477 = 401527) (by norm_num)
theorem B1355069 : Blo 948586 1355069 := bbase (se 3 (by rfl) ⟨254075, by rfl⟩ : syracuseStep 1355069 = 508151) (by norm_num)
theorem B2141549 : Blo 948586 2141549 := bbase (se 3 (by rfl) ⟨401540, by rfl⟩ : syracuseStep 2141549 = 803081) (by norm_num)
theorem B2436493 : Blo 948586 2436493 := bbase (se 3 (by rfl) ⟨456842, by rfl⟩ : syracuseStep 2436493 = 913685) (by norm_num)
theorem B2141621 : Blo 948586 2141621 := bbase (se 5 (by rfl) ⟨100388, by rfl⟩ : syracuseStep 2141621 = 200777) (by norm_num)
theorem B962005 : Blo 948586 962005 := bbase (se 7 (by rfl) ⟨11273, by rfl⟩ : syracuseStep 962005 = 22547) (by norm_num)
theorem B2141693 : Blo 948586 2141693 := bbase (se 3 (by rfl) ⟨401567, by rfl⟩ : syracuseStep 2141693 = 803135) (by norm_num)
theorem B2403877 : Blo 948586 2403877 := bbase (se 4 (by rfl) ⟨225363, by rfl⟩ : syracuseStep 2403877 = 450727) (by norm_num)
theorem B2141765 : Blo 948586 2141765 := bbase (se 4 (by rfl) ⟨200790, by rfl⟩ : syracuseStep 2141765 = 401581) (by norm_num)
theorem B2141837 : Blo 948586 2141837 := bbase (se 3 (by rfl) ⟨401594, by rfl⟩ : syracuseStep 2141837 = 803189) (by norm_num)
theorem B2403989 : Blo 948586 2403989 := bbase (se 6 (by rfl) ⟨56343, by rfl⟩ : syracuseStep 2403989 = 112687) (by norm_num)
theorem B2141909 : Blo 948586 2141909 := bbase (se 7 (by rfl) ⟨25100, by rfl⟩ : syracuseStep 2141909 = 50201) (by norm_num)
theorem B1191677 : Blo 948586 1191677 := bbase (se 3 (by rfl) ⟨223439, by rfl⟩ : syracuseStep 1191677 = 446879) (by norm_num)
theorem B962329 : Blo 948586 962329 := bbase (se 2 (by rfl) ⟨360873, by rfl⟩ : syracuseStep 962329 = 721747) (by norm_num)
theorem B2141981 : Blo 948586 2141981 := bbase (se 3 (by rfl) ⟨401621, by rfl⟩ : syracuseStep 2141981 = 803243) (by norm_num)
theorem B2404181 : Blo 948586 2404181 := bbase (se 9 (by rfl) ⟨7043, by rfl⟩ : syracuseStep 2404181 = 14087) (by norm_num)
theorem B2142053 : Blo 948586 2142053 := bbase (se 4 (by rfl) ⟨200817, by rfl⟩ : syracuseStep 2142053 = 401635) (by norm_num)
theorem B1355621 : Blo 948586 1355621 := bbase (se 4 (by rfl) ⟨127089, by rfl⟩ : syracuseStep 1355621 = 254179) (by norm_num)
theorem B4566901 : Blo 948586 4566901 := bbase (se 5 (by rfl) ⟨214073, by rfl⟩ : syracuseStep 4566901 = 428147) (by norm_num)
theorem B2142125 : Blo 948586 2142125 := bbase (se 3 (by rfl) ⟨401648, by rfl⟩ : syracuseStep 2142125 = 803297) (by norm_num)
theorem B17313749 : Blo 948586 17313749 := bbase (se 7 (by rfl) ⟨202895, by rfl⟩ : syracuseStep 17313749 = 405791) (by norm_num)
theorem B2142197 : Blo 948586 2142197 := bbase (se 5 (by rfl) ⟨100415, by rfl⟩ : syracuseStep 2142197 = 200831) (by norm_num)
theorem B2142269 : Blo 948586 2142269 := bbase (se 3 (by rfl) ⟨401675, by rfl⟩ : syracuseStep 2142269 = 803351) (by norm_num)
theorem B3420229 : Blo 948586 3420229 := bbase (se 4 (by rfl) ⟨320646, by rfl⟩ : syracuseStep 3420229 = 641293) (by norm_num)
theorem B1650797 : Blo 948586 1650797 := bbase (se 3 (by rfl) ⟨309524, by rfl⟩ : syracuseStep 1650797 = 619049) (by norm_num)
theorem B2142341 : Blo 948586 2142341 := bbase (se 4 (by rfl) ⟨200844, by rfl⟩ : syracuseStep 2142341 = 401689) (by norm_num)
theorem B2404525 : Blo 948586 2404525 := bbase (se 3 (by rfl) ⟨450848, by rfl⟩ : syracuseStep 2404525 = 901697) (by norm_num)
theorem B2142413 : Blo 948586 2142413 := bbase (se 3 (by rfl) ⟨401702, by rfl⟩ : syracuseStep 2142413 = 803405) (by norm_num)
theorem B2142485 : Blo 948586 2142485 := bbase (se 6 (by rfl) ⟨50214, by rfl⟩ : syracuseStep 2142485 = 100429) (by norm_num)
theorem B2404637 : Blo 948586 2404637 := bbase (se 3 (by rfl) ⟨450869, by rfl⟩ : syracuseStep 2404637 = 901739) (by norm_num)
theorem B2142557 : Blo 948586 2142557 := bbase (se 3 (by rfl) ⟨401729, by rfl⟩ : syracuseStep 2142557 = 803459) (by norm_num)
theorem B8106389 : Blo 948586 8106389 := bbase (se 6 (by rfl) ⟨189993, by rfl⟩ : syracuseStep 8106389 = 379987) (by norm_num)
theorem B2142629 : Blo 948586 2142629 := bbase (se 4 (by rfl) ⟨200871, by rfl⟩ : syracuseStep 2142629 = 401743) (by norm_num)
theorem B2404829 : Blo 948586 2404829 := bbase (se 3 (by rfl) ⟨450905, by rfl⟩ : syracuseStep 2404829 = 901811) (by norm_num)
theorem B2142701 : Blo 948586 2142701 := bbase (se 3 (by rfl) ⟨401756, by rfl⟩ : syracuseStep 2142701 = 803513) (by norm_num)
theorem B2568709 : Blo 948586 2568709 := bbase (se 4 (by rfl) ⟨240816, by rfl⟩ : syracuseStep 2568709 = 481633) (by norm_num)
theorem B2142773 : Blo 948586 2142773 := bbase (se 5 (by rfl) ⟨100442, by rfl⟩ : syracuseStep 2142773 = 200885) (by norm_num)
theorem B2142845 : Blo 948586 2142845 := bbase (se 3 (by rfl) ⟨401783, by rfl⟩ : syracuseStep 2142845 = 803567) (by norm_num)
theorem B2142917 : Blo 948586 2142917 := bbase (se 4 (by rfl) ⟨200898, by rfl⟩ : syracuseStep 2142917 = 401797) (by norm_num)
theorem B2142989 : Blo 948586 2142989 := bbase (se 3 (by rfl) ⟨401810, by rfl⟩ : syracuseStep 2142989 = 803621) (by norm_num)
theorem B2405173 : Blo 948586 2405173 := bbase (se 5 (by rfl) ⟨112742, by rfl⟩ : syracuseStep 2405173 = 225485) (by norm_num)
theorem B1520461 : Blo 948586 1520461 := bbase (se 3 (by rfl) ⟨285086, by rfl⟩ : syracuseStep 1520461 = 570173) (by norm_num)
theorem B2143061 : Blo 948586 2143061 := bbase (se 9 (by rfl) ⟨6278, by rfl⟩ : syracuseStep 2143061 = 12557) (by norm_num)
theorem B2143133 : Blo 948586 2143133 := bbase (se 3 (by rfl) ⟨401837, by rfl⟩ : syracuseStep 2143133 = 803675) (by norm_num)
theorem B2405285 : Blo 948586 2405285 := bbase (se 4 (by rfl) ⟨225495, by rfl⟩ : syracuseStep 2405285 = 450991) (by norm_num)
theorem B2143205 : Blo 948586 2143205 := bbase (se 4 (by rfl) ⟨200925, by rfl⟩ : syracuseStep 2143205 = 401851) (by norm_num)
theorem B2143277 : Blo 948586 2143277 := bbase (se 3 (by rfl) ⟨401864, by rfl⟩ : syracuseStep 2143277 = 803729) (by norm_num)
theorem B2405477 : Blo 948586 2405477 := bbase (se 4 (by rfl) ⟨225513, by rfl⟩ : syracuseStep 2405477 = 451027) (by norm_num)
theorem B2929829 : Blo 948586 2929829 := bbase (se 4 (by rfl) ⟨274671, by rfl⟩ : syracuseStep 2929829 = 549343) (by norm_num)
theorem B3257605 : Blo 948586 3257605 := bbase (se 4 (by rfl) ⟨305400, by rfl⟩ : syracuseStep 3257605 = 610801) (by norm_num)
theorem B1127689 : Blo 948586 1127689 := bbase (se 2 (by rfl) ⟨422883, by rfl⟩ : syracuseStep 1127689 = 845767) (by norm_num)
theorem B2405821 : Blo 948586 2405821 := bbase (se 3 (by rfl) ⟨451091, by rfl⟩ : syracuseStep 2405821 = 902183) (by norm_num)
theorem B1521173 : Blo 948586 1521173 := bbase (se 6 (by rfl) ⟨35652, by rfl⟩ : syracuseStep 1521173 = 71305) (by norm_num)
theorem B1422893 : Blo 948586 1422893 := bbase (se 3 (by rfl) ⟨266792, by rfl⟩ : syracuseStep 1422893 = 533585) (by norm_num)
theorem B2405933 : Blo 948586 2405933 := bbase (se 3 (by rfl) ⟨451112, by rfl⟩ : syracuseStep 2405933 = 902225) (by norm_num)
theorem B1422917 : Blo 948586 1422917 := bbase (se 4 (by rfl) ⟨133398, by rfl⟩ : syracuseStep 1422917 = 266797) (by norm_num)
theorem B1422941 : Blo 948586 1422941 := bbase (se 3 (by rfl) ⟨266801, by rfl⟩ : syracuseStep 1422941 = 533603) (by norm_num)
theorem B1422965 : Blo 948586 1422965 := bbase (se 5 (by rfl) ⟨66701, by rfl⟩ : syracuseStep 1422965 = 133403) (by norm_num)
theorem B1029757 : Blo 948586 1029757 := bbase (se 3 (by rfl) ⟨193079, by rfl⟩ : syracuseStep 1029757 = 386159) (by norm_num)
theorem B1422989 : Blo 948586 1422989 := bbase (se 3 (by rfl) ⟨266810, by rfl⟩ : syracuseStep 1422989 = 533621) (by norm_num)
theorem B1423013 : Blo 948586 1423013 := bbase (se 4 (by rfl) ⟨133407, by rfl⟩ : syracuseStep 1423013 = 266815) (by norm_num)
theorem B1423037 : Blo 948586 1423037 := bbase (se 3 (by rfl) ⟨266819, by rfl⟩ : syracuseStep 1423037 = 533639) (by norm_num)
theorem B1423061 : Blo 948586 1423061 := bbase (se 7 (by rfl) ⟨16676, by rfl⟩ : syracuseStep 1423061 = 33353) (by norm_num)
theorem B1423085 : Blo 948586 1423085 := bbase (se 3 (by rfl) ⟨266828, by rfl⟩ : syracuseStep 1423085 = 533657) (by norm_num)
theorem B2406125 : Blo 948586 2406125 := bbase (se 3 (by rfl) ⟨451148, by rfl⟩ : syracuseStep 2406125 = 902297) (by norm_num)
theorem B2569973 : Blo 948586 2569973 := bbase (se 5 (by rfl) ⟨120467, by rfl⟩ : syracuseStep 2569973 = 240935) (by norm_num)
theorem B1423109 : Blo 948586 1423109 := bbase (se 4 (by rfl) ⟨133416, by rfl⟩ : syracuseStep 1423109 = 266833) (by norm_num)
theorem B964369 : Blo 948586 964369 := bbase (se 2 (by rfl) ⟨361638, by rfl⟩ : syracuseStep 964369 = 723277) (by norm_num)
theorem B1423133 : Blo 948586 1423133 := bbase (se 3 (by rfl) ⟨266837, by rfl⟩ : syracuseStep 1423133 = 533675) (by norm_num)
theorem B964381 : Blo 948586 964381 := bbase (se 3 (by rfl) ⟨180821, by rfl⟩ : syracuseStep 964381 = 361643) (by norm_num)
theorem B1423157 : Blo 948586 1423157 := bbase (se 5 (by rfl) ⟨66710, by rfl⟩ : syracuseStep 1423157 = 133421) (by norm_num)
theorem B1423181 : Blo 948586 1423181 := bbase (se 3 (by rfl) ⟨266846, by rfl⟩ : syracuseStep 1423181 = 533693) (by norm_num)
theorem B1423205 : Blo 948586 1423205 := bbase (se 4 (by rfl) ⟨133425, by rfl⟩ : syracuseStep 1423205 = 266851) (by norm_num)
theorem B1423229 : Blo 948586 1423229 := bbase (se 3 (by rfl) ⟨266855, by rfl⟩ : syracuseStep 1423229 = 533711) (by norm_num)
theorem B1423253 : Blo 948586 1423253 := bbase (se 6 (by rfl) ⟨33357, by rfl⟩ : syracuseStep 1423253 = 66715) (by norm_num)
theorem B1423277 : Blo 948586 1423277 := bbase (se 3 (by rfl) ⟨266864, by rfl⟩ : syracuseStep 1423277 = 533729) (by norm_num)
theorem B1423301 : Blo 948586 1423301 := bbase (se 4 (by rfl) ⟨133434, by rfl⟩ : syracuseStep 1423301 = 266869) (by norm_num)
theorem B1423325 : Blo 948586 1423325 := bbase (se 3 (by rfl) ⟨266873, by rfl⟩ : syracuseStep 1423325 = 533747) (by norm_num)
theorem B1423349 : Blo 948586 1423349 := bbase (se 5 (by rfl) ⟨66719, by rfl⟩ : syracuseStep 1423349 = 133439) (by norm_num)
theorem B1423373 : Blo 948586 1423373 := bbase (se 3 (by rfl) ⟨266882, by rfl⟩ : syracuseStep 1423373 = 533765) (by norm_num)
theorem B1423397 : Blo 948586 1423397 := bbase (se 4 (by rfl) ⟨133443, by rfl⟩ : syracuseStep 1423397 = 266887) (by norm_num)
theorem B1423421 : Blo 948586 1423421 := bbase (se 3 (by rfl) ⟨266891, by rfl⟩ : syracuseStep 1423421 = 533783) (by norm_num)
theorem B2406469 : Blo 948586 2406469 := bbase (se 4 (by rfl) ⟨225606, by rfl⟩ : syracuseStep 2406469 = 451213) (by norm_num)
theorem B1423445 : Blo 948586 1423445 := bbase (se 8 (by rfl) ⟨8340, by rfl⟩ : syracuseStep 1423445 = 16681) (by norm_num)
theorem B1423469 : Blo 948586 1423469 := bbase (se 3 (by rfl) ⟨266900, by rfl⟩ : syracuseStep 1423469 = 533801) (by norm_num)
theorem B1423493 : Blo 948586 1423493 := bbase (se 4 (by rfl) ⟨133452, by rfl⟩ : syracuseStep 1423493 = 266905) (by norm_num)
theorem B1423517 : Blo 948586 1423517 := bbase (se 3 (by rfl) ⟨266909, by rfl⟩ : syracuseStep 1423517 = 533819) (by norm_num)
theorem B1423541 : Blo 948586 1423541 := bbase (se 5 (by rfl) ⟨66728, by rfl⟩ : syracuseStep 1423541 = 133457) (by norm_num)
theorem B1521845 : Blo 948586 1521845 := bbase (se 5 (by rfl) ⟨71336, by rfl⟩ : syracuseStep 1521845 = 142673) (by norm_num)
theorem B2406581 : Blo 948586 2406581 := bbase (se 5 (by rfl) ⟨112808, by rfl⟩ : syracuseStep 2406581 = 225617) (by norm_num)
theorem B1423565 : Blo 948586 1423565 := bbase (se 3 (by rfl) ⟨266918, by rfl⟩ : syracuseStep 1423565 = 533837) (by norm_num)
theorem B1423589 : Blo 948586 1423589 := bbase (se 4 (by rfl) ⟨133461, by rfl⟩ : syracuseStep 1423589 = 266923) (by norm_num)
theorem B1423613 : Blo 948586 1423613 := bbase (se 3 (by rfl) ⟨266927, by rfl⟩ : syracuseStep 1423613 = 533855) (by norm_num)
theorem B1423637 : Blo 948586 1423637 := bbase (se 6 (by rfl) ⟨33366, by rfl⟩ : syracuseStep 1423637 = 66733) (by norm_num)
theorem B1423661 : Blo 948586 1423661 := bbase (se 3 (by rfl) ⟨266936, by rfl⟩ : syracuseStep 1423661 = 533873) (by norm_num)
theorem B1423685 : Blo 948586 1423685 := bbase (se 4 (by rfl) ⟨133470, by rfl⟩ : syracuseStep 1423685 = 266941) (by norm_num)
theorem B1423709 : Blo 948586 1423709 := bbase (se 3 (by rfl) ⟨266945, by rfl⟩ : syracuseStep 1423709 = 533891) (by norm_num)
theorem B1423733 : Blo 948586 1423733 := bbase (se 5 (by rfl) ⟨66737, by rfl⟩ : syracuseStep 1423733 = 133475) (by norm_num)
theorem B2406773 : Blo 948586 2406773 := bbase (se 5 (by rfl) ⟨112817, by rfl⟩ : syracuseStep 2406773 = 225635) (by norm_num)
theorem B1423757 : Blo 948586 1423757 := bbase (se 3 (by rfl) ⟨266954, by rfl⟩ : syracuseStep 1423757 = 533909) (by norm_num)
theorem B1423781 : Blo 948586 1423781 := bbase (se 4 (by rfl) ⟨133479, by rfl⟩ : syracuseStep 1423781 = 266959) (by norm_num)
theorem B1423805 : Blo 948586 1423805 := bbase (se 3 (by rfl) ⟨266963, by rfl⟩ : syracuseStep 1423805 = 533927) (by norm_num)
theorem B2701765 : Blo 948586 2701765 := bbase (se 4 (by rfl) ⟨253290, by rfl⟩ : syracuseStep 2701765 = 506581) (by norm_num)
theorem B1423829 : Blo 948586 1423829 := bbase (se 7 (by rfl) ⟨16685, by rfl⟩ : syracuseStep 1423829 = 33371) (by norm_num)
theorem B1423853 : Blo 948586 1423853 := bbase (se 3 (by rfl) ⟨266972, by rfl⟩ : syracuseStep 1423853 = 533945) (by norm_num)
theorem B1423877 : Blo 948586 1423877 := bbase (se 4 (by rfl) ⟨133488, by rfl⟩ : syracuseStep 1423877 = 266977) (by norm_num)
theorem B1423901 : Blo 948586 1423901 := bbase (se 3 (by rfl) ⟨266981, by rfl⟩ : syracuseStep 1423901 = 533963) (by norm_num)
theorem B1423925 : Blo 948586 1423925 := bbase (se 5 (by rfl) ⟨66746, by rfl⟩ : syracuseStep 1423925 = 133493) (by norm_num)
theorem B1423949 : Blo 948586 1423949 := bbase (se 3 (by rfl) ⟨266990, by rfl⟩ : syracuseStep 1423949 = 533981) (by norm_num)
theorem B1423973 : Blo 948586 1423973 := bbase (se 4 (by rfl) ⟨133497, by rfl⟩ : syracuseStep 1423973 = 266995) (by norm_num)
theorem B1423997 : Blo 948586 1423997 := bbase (se 3 (by rfl) ⟨266999, by rfl⟩ : syracuseStep 1423997 = 533999) (by norm_num)
theorem B1424021 : Blo 948586 1424021 := bbase (se 6 (by rfl) ⟨33375, by rfl⟩ : syracuseStep 1424021 = 66751) (by norm_num)
theorem B1424045 : Blo 948586 1424045 := bbase (se 3 (by rfl) ⟨267008, by rfl⟩ : syracuseStep 1424045 = 534017) (by norm_num)
theorem B1522357 : Blo 948586 1522357 := bbase (se 5 (by rfl) ⟨71360, by rfl⟩ : syracuseStep 1522357 = 142721) (by norm_num)
theorem B1424069 : Blo 948586 1424069 := bbase (se 4 (by rfl) ⟨133506, by rfl⟩ : syracuseStep 1424069 = 267013) (by norm_num)
theorem B2407117 : Blo 948586 2407117 := bbase (se 3 (by rfl) ⟨451334, by rfl⟩ : syracuseStep 2407117 = 902669) (by norm_num)
theorem B1424093 : Blo 948586 1424093 := bbase (se 3 (by rfl) ⟨267017, by rfl⟩ : syracuseStep 1424093 = 534035) (by norm_num)
theorem B1424117 : Blo 948586 1424117 := bbase (se 5 (by rfl) ⟨66755, by rfl⟩ : syracuseStep 1424117 = 133511) (by norm_num)
theorem B1424141 : Blo 948586 1424141 := bbase (se 3 (by rfl) ⟨267026, by rfl⟩ : syracuseStep 1424141 = 534053) (by norm_num)
theorem B10828565 : Blo 948586 10828565 := bbase (se 6 (by rfl) ⟨253794, by rfl⟩ : syracuseStep 10828565 = 507589) (by norm_num)
theorem B1424165 : Blo 948586 1424165 := bbase (se 4 (by rfl) ⟨133515, by rfl⟩ : syracuseStep 1424165 = 267031) (by norm_num)
theorem B1424189 : Blo 948586 1424189 := bbase (se 3 (by rfl) ⟨267035, by rfl⟩ : syracuseStep 1424189 = 534071) (by norm_num)
theorem B2407229 : Blo 948586 2407229 := bbase (se 3 (by rfl) ⟨451355, by rfl⟩ : syracuseStep 2407229 = 902711) (by norm_num)
theorem B1424213 : Blo 948586 1424213 := bbase (se 9 (by rfl) ⟨4172, by rfl⟩ : syracuseStep 1424213 = 8345) (by norm_num)
theorem B1424237 : Blo 948586 1424237 := bbase (se 3 (by rfl) ⟨267044, by rfl⟩ : syracuseStep 1424237 = 534089) (by norm_num)
theorem B1424261 : Blo 948586 1424261 := bbase (se 4 (by rfl) ⟨133524, by rfl⟩ : syracuseStep 1424261 = 267049) (by norm_num)
theorem B4111253 : Blo 948586 4111253 := bbase (se 6 (by rfl) ⟨96357, by rfl⟩ : syracuseStep 4111253 = 192715) (by norm_num)
theorem B1424285 : Blo 948586 1424285 := bbase (se 3 (by rfl) ⟨267053, by rfl⟩ : syracuseStep 1424285 = 534107) (by norm_num)
theorem B1424309 : Blo 948586 1424309 := bbase (se 5 (by rfl) ⟨66764, by rfl⟩ : syracuseStep 1424309 = 133529) (by norm_num)
theorem B1424333 : Blo 948586 1424333 := bbase (se 3 (by rfl) ⟨267062, by rfl⟩ : syracuseStep 1424333 = 534125) (by norm_num)
theorem B1424357 : Blo 948586 1424357 := bbase (se 4 (by rfl) ⟨133533, by rfl⟩ : syracuseStep 1424357 = 267067) (by norm_num)
theorem B2407421 : Blo 948586 2407421 := bbase (se 3 (by rfl) ⟨451391, by rfl⟩ : syracuseStep 2407421 = 902783) (by norm_num)
theorem B1424381 : Blo 948586 1424381 := bbase (se 3 (by rfl) ⟨267071, by rfl⟩ : syracuseStep 1424381 = 534143) (by norm_num)
theorem B1424405 : Blo 948586 1424405 := bbase (se 6 (by rfl) ⟨33384, by rfl⟩ : syracuseStep 1424405 = 66769) (by norm_num)
theorem B1424429 : Blo 948586 1424429 := bbase (se 3 (by rfl) ⟨267080, by rfl⟩ : syracuseStep 1424429 = 534161) (by norm_num)
theorem B1424453 : Blo 948586 1424453 := bbase (se 4 (by rfl) ⟨133542, by rfl⟩ : syracuseStep 1424453 = 267085) (by norm_num)
theorem B2473037 : Blo 948586 2473037 := bbase (se 3 (by rfl) ⟨463694, by rfl⟩ : syracuseStep 2473037 = 927389) (by norm_num)
theorem B15416405 : Blo 948586 15416405 := bbase (se 8 (by rfl) ⟨90330, by rfl⟩ : syracuseStep 15416405 = 180661) (by norm_num)
theorem B1424477 : Blo 948586 1424477 := bbase (se 3 (by rfl) ⟨267089, by rfl⟩ : syracuseStep 1424477 = 534179) (by norm_num)
theorem B1424501 : Blo 948586 1424501 := bbase (se 5 (by rfl) ⟨66773, by rfl⟩ : syracuseStep 1424501 = 133547) (by norm_num)
theorem B1522813 : Blo 948586 1522813 := bbase (se 3 (by rfl) ⟨285527, by rfl⟩ : syracuseStep 1522813 = 571055) (by norm_num)
theorem B1424525 : Blo 948586 1424525 := bbase (se 3 (by rfl) ⟨267098, by rfl⟩ : syracuseStep 1424525 = 534197) (by norm_num)
theorem B1981597 : Blo 948586 1981597 := bbase (se 3 (by rfl) ⟨371549, by rfl⟩ : syracuseStep 1981597 = 743099) (by norm_num)
theorem B1424549 : Blo 948586 1424549 := bbase (se 4 (by rfl) ⟨133551, by rfl⟩ : syracuseStep 1424549 = 267103) (by norm_num)
theorem B1424573 : Blo 948586 1424573 := bbase (se 3 (by rfl) ⟨267107, by rfl⟩ : syracuseStep 1424573 = 534215) (by norm_num)
theorem B1424597 : Blo 948586 1424597 := bbase (se 7 (by rfl) ⟨16694, by rfl⟩ : syracuseStep 1424597 = 33389) (by norm_num)
theorem B3849445 : Blo 948586 3849445 := bbase (se 4 (by rfl) ⟨360885, by rfl⟩ : syracuseStep 3849445 = 721771) (by norm_num)
theorem B1424621 : Blo 948586 1424621 := bbase (se 3 (by rfl) ⟨267116, by rfl⟩ : syracuseStep 1424621 = 534233) (by norm_num)
theorem B1424645 : Blo 948586 1424645 := bbase (se 4 (by rfl) ⟨133560, by rfl⟩ : syracuseStep 1424645 = 267121) (by norm_num)
theorem B1424669 : Blo 948586 1424669 := bbase (se 3 (by rfl) ⟨267125, by rfl⟩ : syracuseStep 1424669 = 534251) (by norm_num)
theorem B1424693 : Blo 948586 1424693 := bbase (se 5 (by rfl) ⟨66782, by rfl⟩ : syracuseStep 1424693 = 133565) (by norm_num)
theorem B1424717 : Blo 948586 1424717 := bbase (se 3 (by rfl) ⟨267134, by rfl⟩ : syracuseStep 1424717 = 534269) (by norm_num)
theorem B2407765 : Blo 948586 2407765 := bbase (se 11 (by rfl) ⟨1763, by rfl⟩ : syracuseStep 2407765 = 3527) (by norm_num)
theorem B1424741 : Blo 948586 1424741 := bbase (se 4 (by rfl) ⟨133569, by rfl⟩ : syracuseStep 1424741 = 267139) (by norm_num)
theorem B1097069 : Blo 948586 1097069 := bbase (se 3 (by rfl) ⟨205700, by rfl⟩ : syracuseStep 1097069 = 411401) (by norm_num)
theorem B1424765 : Blo 948586 1424765 := bbase (se 3 (by rfl) ⟨267143, by rfl⟩ : syracuseStep 1424765 = 534287) (by norm_num)
theorem B1424789 : Blo 948586 1424789 := bbase (se 6 (by rfl) ⟨33393, by rfl⟩ : syracuseStep 1424789 = 66787) (by norm_num)
theorem B1424813 : Blo 948586 1424813 := bbase (se 3 (by rfl) ⟨267152, by rfl⟩ : syracuseStep 1424813 = 534305) (by norm_num)
theorem B1424837 : Blo 948586 1424837 := bbase (se 4 (by rfl) ⟨133578, by rfl⟩ : syracuseStep 1424837 = 267157) (by norm_num)
theorem B2407877 : Blo 948586 2407877 := bbase (se 4 (by rfl) ⟨225738, by rfl⟩ : syracuseStep 2407877 = 451477) (by norm_num)
theorem B1424861 : Blo 948586 1424861 := bbase (se 3 (by rfl) ⟨267161, by rfl⟩ : syracuseStep 1424861 = 534323) (by norm_num)
theorem B1424885 : Blo 948586 1424885 := bbase (se 5 (by rfl) ⟨66791, by rfl⟩ : syracuseStep 1424885 = 133583) (by norm_num)
theorem B1424909 : Blo 948586 1424909 := bbase (se 3 (by rfl) ⟨267170, by rfl⟩ : syracuseStep 1424909 = 534341) (by norm_num)
theorem B1424933 : Blo 948586 1424933 := bbase (se 4 (by rfl) ⟨133587, by rfl⟩ : syracuseStep 1424933 = 267175) (by norm_num)
theorem B1424957 : Blo 948586 1424957 := bbase (se 3 (by rfl) ⟨267179, by rfl⟩ : syracuseStep 1424957 = 534359) (by norm_num)
theorem B1424981 : Blo 948586 1424981 := bbase (se 8 (by rfl) ⟨8349, by rfl⟩ : syracuseStep 1424981 = 16699) (by norm_num)
theorem B1425005 : Blo 948586 1425005 := bbase (se 3 (by rfl) ⟨267188, by rfl⟩ : syracuseStep 1425005 = 534377) (by norm_num)
theorem B1425029 : Blo 948586 1425029 := bbase (se 4 (by rfl) ⟨133596, by rfl⟩ : syracuseStep 1425029 = 267193) (by norm_num)
theorem B2408069 : Blo 948586 2408069 := bbase (se 4 (by rfl) ⟨225756, by rfl⟩ : syracuseStep 2408069 = 451513) (by norm_num)
theorem B1425053 : Blo 948586 1425053 := bbase (se 3 (by rfl) ⟨267197, by rfl⟩ : syracuseStep 1425053 = 534395) (by norm_num)
theorem B1425077 : Blo 948586 1425077 := bbase (se 5 (by rfl) ⟨66800, by rfl⟩ : syracuseStep 1425077 = 133601) (by norm_num)
theorem B1425101 : Blo 948586 1425101 := bbase (se 3 (by rfl) ⟨267206, by rfl⟩ : syracuseStep 1425101 = 534413) (by norm_num)
theorem B1425125 : Blo 948586 1425125 := bbase (se 4 (by rfl) ⟨133605, by rfl⟩ : syracuseStep 1425125 = 267211) (by norm_num)
theorem B1097465 : Blo 948586 1097465 := bbase (se 2 (by rfl) ⟨411549, by rfl⟩ : syracuseStep 1097465 = 823099) (by norm_num)
theorem B1425149 : Blo 948586 1425149 := bbase (se 3 (by rfl) ⟨267215, by rfl⟩ : syracuseStep 1425149 = 534431) (by norm_num)
theorem B1425173 : Blo 948586 1425173 := bbase (se 6 (by rfl) ⟨33402, by rfl⟩ : syracuseStep 1425173 = 66805) (by norm_num)
theorem B1523485 : Blo 948586 1523485 := bbase (se 3 (by rfl) ⟨285653, by rfl⟩ : syracuseStep 1523485 = 571307) (by norm_num)
theorem B1425197 : Blo 948586 1425197 := bbase (se 3 (by rfl) ⟨267224, by rfl⟩ : syracuseStep 1425197 = 534449) (by norm_num)
theorem B1425221 : Blo 948586 1425221 := bbase (se 4 (by rfl) ⟨133614, by rfl⟩ : syracuseStep 1425221 = 267229) (by norm_num)
theorem B1425245 : Blo 948586 1425245 := bbase (se 3 (by rfl) ⟨267233, by rfl⟩ : syracuseStep 1425245 = 534467) (by norm_num)
theorem B1425269 : Blo 948586 1425269 := bbase (se 5 (by rfl) ⟨66809, by rfl⟩ : syracuseStep 1425269 = 133619) (by norm_num)
theorem B1425293 : Blo 948586 1425293 := bbase (se 3 (by rfl) ⟨267242, by rfl⟩ : syracuseStep 1425293 = 534485) (by norm_num)
theorem B2703269 : Blo 948586 2703269 := bbase (se 4 (by rfl) ⟨253431, by rfl⟩ : syracuseStep 2703269 = 506863) (by norm_num)
theorem B1425317 : Blo 948586 1425317 := bbase (se 4 (by rfl) ⟨133623, by rfl⟩ : syracuseStep 1425317 = 267247) (by norm_num)
theorem B1425341 : Blo 948586 1425341 := bbase (se 3 (by rfl) ⟨267251, by rfl⟩ : syracuseStep 1425341 = 534503) (by norm_num)
theorem B1425365 : Blo 948586 1425365 := bbase (se 7 (by rfl) ⟨16703, by rfl⟩ : syracuseStep 1425365 = 33407) (by norm_num)
theorem B2408413 : Blo 948586 2408413 := bbase (se 3 (by rfl) ⟨451577, by rfl⟩ : syracuseStep 2408413 = 903155) (by norm_num)
theorem B1425389 : Blo 948586 1425389 := bbase (se 3 (by rfl) ⟨267260, by rfl⟩ : syracuseStep 1425389 = 534521) (by norm_num)
theorem B1425413 : Blo 948586 1425413 := bbase (se 4 (by rfl) ⟨133632, by rfl⟩ : syracuseStep 1425413 = 267265) (by norm_num)
theorem B1425437 : Blo 948586 1425437 := bbase (se 3 (by rfl) ⟨267269, by rfl⟩ : syracuseStep 1425437 = 534539) (by norm_num)
theorem B1425461 : Blo 948586 1425461 := bbase (se 5 (by rfl) ⟨66818, by rfl⟩ : syracuseStep 1425461 = 133637) (by norm_num)
theorem B1425485 : Blo 948586 1425485 := bbase (se 3 (by rfl) ⟨267278, by rfl⟩ : syracuseStep 1425485 = 534557) (by norm_num)
theorem B2408525 : Blo 948586 2408525 := bbase (se 3 (by rfl) ⟨451598, by rfl⟩ : syracuseStep 2408525 = 903197) (by norm_num)
theorem B1425509 : Blo 948586 1425509 := bbase (se 4 (by rfl) ⟨133641, by rfl⟩ : syracuseStep 1425509 = 267283) (by norm_num)
theorem B1425533 : Blo 948586 1425533 := bbase (se 3 (by rfl) ⟨267287, by rfl⟩ : syracuseStep 1425533 = 534575) (by norm_num)
theorem B1425557 : Blo 948586 1425557 := bbase (se 6 (by rfl) ⟨33411, by rfl⟩ : syracuseStep 1425557 = 66823) (by norm_num)
theorem B1425581 : Blo 948586 1425581 := bbase (se 3 (by rfl) ⟨267296, by rfl⟩ : syracuseStep 1425581 = 534593) (by norm_num)
theorem B1425605 : Blo 948586 1425605 := bbase (se 4 (by rfl) ⟨133650, by rfl⟩ : syracuseStep 1425605 = 267301) (by norm_num)
theorem B1523909 : Blo 948586 1523909 := bbase (se 4 (by rfl) ⟨142866, by rfl⟩ : syracuseStep 1523909 = 285733) (by norm_num)
theorem B1425629 : Blo 948586 1425629 := bbase (se 3 (by rfl) ⟨267305, by rfl⟩ : syracuseStep 1425629 = 534611) (by norm_num)
theorem B1425653 : Blo 948586 1425653 := bbase (se 5 (by rfl) ⟨66827, by rfl⟩ : syracuseStep 1425653 = 133655) (by norm_num)
theorem B1425677 : Blo 948586 1425677 := bbase (se 3 (by rfl) ⟨267314, by rfl⟩ : syracuseStep 1425677 = 534629) (by norm_num)
theorem B2408717 : Blo 948586 2408717 := bbase (se 3 (by rfl) ⟨451634, by rfl⟩ : syracuseStep 2408717 = 903269) (by norm_num)
theorem B1425701 : Blo 948586 1425701 := bbase (se 4 (by rfl) ⟨133659, by rfl⟩ : syracuseStep 1425701 = 267319) (by norm_num)
theorem B4112693 : Blo 948586 4112693 := bbase (se 5 (by rfl) ⟨192782, by rfl⟩ : syracuseStep 4112693 = 385565) (by norm_num)
theorem B1425725 : Blo 948586 1425725 := bbase (se 3 (by rfl) ⟨267323, by rfl⟩ : syracuseStep 1425725 = 534647) (by norm_num)
theorem B1425749 : Blo 948586 1425749 := bbase (se 10 (by rfl) ⟨2088, by rfl⟩ : syracuseStep 1425749 = 4177) (by norm_num)
theorem B1425773 : Blo 948586 1425773 := bbase (se 3 (by rfl) ⟨267332, by rfl⟩ : syracuseStep 1425773 = 534665) (by norm_num)
theorem B1425797 : Blo 948586 1425797 := bbase (se 4 (by rfl) ⟨133668, by rfl⟩ : syracuseStep 1425797 = 267337) (by norm_num)
theorem B1425821 : Blo 948586 1425821 := bbase (se 3 (by rfl) ⟨267341, by rfl⟩ : syracuseStep 1425821 = 534683) (by norm_num)
theorem B1425845 : Blo 948586 1425845 := bbase (se 5 (by rfl) ⟨66836, by rfl⟩ : syracuseStep 1425845 = 133673) (by norm_num)
theorem B1425869 : Blo 948586 1425869 := bbase (se 3 (by rfl) ⟨267350, by rfl⟩ : syracuseStep 1425869 = 534701) (by norm_num)
theorem B1425893 : Blo 948586 1425893 := bbase (se 4 (by rfl) ⟨133677, by rfl⟩ : syracuseStep 1425893 = 267355) (by norm_num)
theorem B1524197 : Blo 948586 1524197 := bbase (se 4 (by rfl) ⟨142893, by rfl⟩ : syracuseStep 1524197 = 285787) (by norm_num)
theorem B1425917 : Blo 948586 1425917 := bbase (se 3 (by rfl) ⟨267359, by rfl⟩ : syracuseStep 1425917 = 534719) (by norm_num)
theorem B1425941 : Blo 948586 1425941 := bbase (se 6 (by rfl) ⟨33420, by rfl⟩ : syracuseStep 1425941 = 66841) (by norm_num)
theorem B1425965 : Blo 948586 1425965 := bbase (se 3 (by rfl) ⟨267368, by rfl⟩ : syracuseStep 1425965 = 534737) (by norm_num)
theorem B5423669 : Blo 948586 5423669 := bbase (se 5 (by rfl) ⟨254234, by rfl⟩ : syracuseStep 5423669 = 508469) (by norm_num)
theorem B1425989 : Blo 948586 1425989 := bbase (se 4 (by rfl) ⟨133686, by rfl⟩ : syracuseStep 1425989 = 267373) (by norm_num)
theorem B1426013 : Blo 948586 1426013 := bbase (se 3 (by rfl) ⟨267377, by rfl⟩ : syracuseStep 1426013 = 534755) (by norm_num)
theorem B2409061 : Blo 948586 2409061 := bbase (se 4 (by rfl) ⟨225849, by rfl⟩ : syracuseStep 2409061 = 451699) (by norm_num)
theorem B1426037 : Blo 948586 1426037 := bbase (se 5 (by rfl) ⟨66845, by rfl⟩ : syracuseStep 1426037 = 133691) (by norm_num)
theorem B1426061 : Blo 948586 1426061 := bbase (se 3 (by rfl) ⟨267386, by rfl⟩ : syracuseStep 1426061 = 534773) (by norm_num)
theorem B1983133 : Blo 948586 1983133 := bbase (se 3 (by rfl) ⟨371837, by rfl⟩ : syracuseStep 1983133 = 743675) (by norm_num)
theorem B1426085 : Blo 948586 1426085 := bbase (se 4 (by rfl) ⟨133695, by rfl⟩ : syracuseStep 1426085 = 267391) (by norm_num)
theorem B1426109 : Blo 948586 1426109 := bbase (se 3 (by rfl) ⟨267395, by rfl⟩ : syracuseStep 1426109 = 534791) (by norm_num)
theorem B1426133 : Blo 948586 1426133 := bbase (se 7 (by rfl) ⟨16712, by rfl⟩ : syracuseStep 1426133 = 33425) (by norm_num)
theorem B2409173 : Blo 948586 2409173 := bbase (se 7 (by rfl) ⟨28232, by rfl⟩ : syracuseStep 2409173 = 56465) (by norm_num)
theorem B1426157 : Blo 948586 1426157 := bbase (se 3 (by rfl) ⟨267404, by rfl⟩ : syracuseStep 1426157 = 534809) (by norm_num)
theorem B1426181 : Blo 948586 1426181 := bbase (se 4 (by rfl) ⟨133704, by rfl⟩ : syracuseStep 1426181 = 267409) (by norm_num)
theorem B1426205 : Blo 948586 1426205 := bbase (se 3 (by rfl) ⟨267413, by rfl⟩ : syracuseStep 1426205 = 534827) (by norm_num)
theorem B1426229 : Blo 948586 1426229 := bbase (se 5 (by rfl) ⟨66854, by rfl⟩ : syracuseStep 1426229 = 133709) (by norm_num)
theorem B1426253 : Blo 948586 1426253 := bbase (se 3 (by rfl) ⟨267422, by rfl⟩ : syracuseStep 1426253 = 534845) (by norm_num)
theorem B1426277 : Blo 948586 1426277 := bbase (se 4 (by rfl) ⟨133713, by rfl⟩ : syracuseStep 1426277 = 267427) (by norm_num)
theorem B2311021 : Blo 948586 2311021 := bbase (se 3 (by rfl) ⟨433316, by rfl⟩ : syracuseStep 2311021 = 866633) (by norm_num)
theorem B1426301 : Blo 948586 1426301 := bbase (se 3 (by rfl) ⟨267431, by rfl⟩ : syracuseStep 1426301 = 534863) (by norm_num)
theorem B1426325 : Blo 948586 1426325 := bbase (se 6 (by rfl) ⟨33429, by rfl⟩ : syracuseStep 1426325 = 66859) (by norm_num)
theorem B2409365 : Blo 948586 2409365 := bbase (se 6 (by rfl) ⟨56469, by rfl⟩ : syracuseStep 2409365 = 112939) (by norm_num)
theorem B1426349 : Blo 948586 1426349 := bbase (se 3 (by rfl) ⟨267440, by rfl⟩ : syracuseStep 1426349 = 534881) (by norm_num)
theorem B1426373 : Blo 948586 1426373 := bbase (se 4 (by rfl) ⟨133722, by rfl⟩ : syracuseStep 1426373 = 267445) (by norm_num)
theorem B1426397 : Blo 948586 1426397 := bbase (se 3 (by rfl) ⟨267449, by rfl⟩ : syracuseStep 1426397 = 534899) (by norm_num)
theorem B1426421 : Blo 948586 1426421 := bbase (se 5 (by rfl) ⟨66863, by rfl⟩ : syracuseStep 1426421 = 133727) (by norm_num)
theorem B1426445 : Blo 948586 1426445 := bbase (se 3 (by rfl) ⟨267458, by rfl⟩ : syracuseStep 1426445 = 534917) (by norm_num)
theorem B1426469 : Blo 948586 1426469 := bbase (se 4 (by rfl) ⟨133731, by rfl⟩ : syracuseStep 1426469 = 267463) (by norm_num)
theorem B1426493 : Blo 948586 1426493 := bbase (se 3 (by rfl) ⟨267467, by rfl⟩ : syracuseStep 1426493 = 534935) (by norm_num)
theorem B1426517 : Blo 948586 1426517 := bbase (se 8 (by rfl) ⟨8358, by rfl⟩ : syracuseStep 1426517 = 16717) (by norm_num)
theorem B1426541 : Blo 948586 1426541 := bbase (se 3 (by rfl) ⟨267476, by rfl⟩ : syracuseStep 1426541 = 534953) (by norm_num)
theorem B1426565 : Blo 948586 1426565 := bbase (se 4 (by rfl) ⟨133740, by rfl⟩ : syracuseStep 1426565 = 267481) (by norm_num)
theorem B1426589 : Blo 948586 1426589 := bbase (se 3 (by rfl) ⟨267485, by rfl⟩ : syracuseStep 1426589 = 534971) (by norm_num)
theorem B1426613 : Blo 948586 1426613 := bbase (se 5 (by rfl) ⟨66872, by rfl⟩ : syracuseStep 1426613 = 133745) (by norm_num)
theorem B1426637 : Blo 948586 1426637 := bbase (se 3 (by rfl) ⟨267494, by rfl⟩ : syracuseStep 1426637 = 534989) (by norm_num)
theorem B1426661 : Blo 948586 1426661 := bbase (se 4 (by rfl) ⟨133749, by rfl⟩ : syracuseStep 1426661 = 267499) (by norm_num)
theorem B2409709 : Blo 948586 2409709 := bbase (se 3 (by rfl) ⟨451820, by rfl⟩ : syracuseStep 2409709 = 903641) (by norm_num)
theorem B1426685 : Blo 948586 1426685 := bbase (se 3 (by rfl) ⟨267503, by rfl⟩ : syracuseStep 1426685 = 535007) (by norm_num)
theorem B1524997 : Blo 948586 1524997 := bbase (se 4 (by rfl) ⟨142968, by rfl⟩ : syracuseStep 1524997 = 285937) (by norm_num)
theorem B1426709 : Blo 948586 1426709 := bbase (se 6 (by rfl) ⟨33438, by rfl⟩ : syracuseStep 1426709 = 66877) (by norm_num)
theorem B7718165 : Blo 948586 7718165 := bbase (se 6 (by rfl) ⟨180894, by rfl⟩ : syracuseStep 7718165 = 361789) (by norm_num)
theorem B1426733 : Blo 948586 1426733 := bbase (se 3 (by rfl) ⟨267512, by rfl⟩ : syracuseStep 1426733 = 535025) (by norm_num)
theorem B1426757 : Blo 948586 1426757 := bbase (se 4 (by rfl) ⟨133758, by rfl⟩ : syracuseStep 1426757 = 267517) (by norm_num)
theorem B1426781 : Blo 948586 1426781 := bbase (se 3 (by rfl) ⟨267521, by rfl⟩ : syracuseStep 1426781 = 535043) (by norm_num)
theorem B2409821 : Blo 948586 2409821 := bbase (se 3 (by rfl) ⟨451841, by rfl⟩ : syracuseStep 2409821 = 903683) (by norm_num)
theorem B1426805 : Blo 948586 1426805 := bbase (se 5 (by rfl) ⟨66881, by rfl⟩ : syracuseStep 1426805 = 133763) (by norm_num)
theorem B1426829 : Blo 948586 1426829 := bbase (se 3 (by rfl) ⟨267530, by rfl⟩ : syracuseStep 1426829 = 535061) (by norm_num)
theorem B1426853 : Blo 948586 1426853 := bbase (se 4 (by rfl) ⟨133767, by rfl⟩ : syracuseStep 1426853 = 267535) (by norm_num)
theorem B1426877 : Blo 948586 1426877 := bbase (se 3 (by rfl) ⟨267539, by rfl⟩ : syracuseStep 1426877 = 535079) (by norm_num)
theorem B1623493 : Blo 948586 1623493 := bbase (se 4 (by rfl) ⟨152202, by rfl⟩ : syracuseStep 1623493 = 304405) (by norm_num)
theorem B3851717 : Blo 948586 3851717 := bbase (se 4 (by rfl) ⟨361098, by rfl⟩ : syracuseStep 3851717 = 722197) (by norm_num)
theorem B2704853 : Blo 948586 2704853 := bbase (se 7 (by rfl) ⟨31697, by rfl⟩ : syracuseStep 2704853 = 63395) (by norm_num)
theorem B1426901 : Blo 948586 1426901 := bbase (se 7 (by rfl) ⟨16721, by rfl⟩ : syracuseStep 1426901 = 33443) (by norm_num)
theorem B1426925 : Blo 948586 1426925 := bbase (se 3 (by rfl) ⟨267548, by rfl⟩ : syracuseStep 1426925 = 535097) (by norm_num)
theorem B1426949 : Blo 948586 1426949 := bbase (se 4 (by rfl) ⟨133776, by rfl⟩ : syracuseStep 1426949 = 267553) (by norm_num)
theorem B1426973 : Blo 948586 1426973 := bbase (se 3 (by rfl) ⟨267557, by rfl⟩ : syracuseStep 1426973 = 535115) (by norm_num)
theorem B2410013 : Blo 948586 2410013 := bbase (se 3 (by rfl) ⟨451877, by rfl⟩ : syracuseStep 2410013 = 903755) (by norm_num)
theorem B1426997 : Blo 948586 1426997 := bbase (se 5 (by rfl) ⟨66890, by rfl⟩ : syracuseStep 1426997 = 133781) (by norm_num)
theorem B1427021 : Blo 948586 1427021 := bbase (se 3 (by rfl) ⟨267566, by rfl⟩ : syracuseStep 1427021 = 535133) (by norm_num)
theorem B1427045 : Blo 948586 1427045 := bbase (se 4 (by rfl) ⟨133785, by rfl⟩ : syracuseStep 1427045 = 267571) (by norm_num)
theorem B1427069 : Blo 948586 1427069 := bbase (se 3 (by rfl) ⟨267575, by rfl⟩ : syracuseStep 1427069 = 535151) (by norm_num)
theorem B1427093 : Blo 948586 1427093 := bbase (se 6 (by rfl) ⟨33447, by rfl⟩ : syracuseStep 1427093 = 66895) (by norm_num)
theorem B1427117 : Blo 948586 1427117 := bbase (se 3 (by rfl) ⟨267584, by rfl⟩ : syracuseStep 1427117 = 535169) (by norm_num)
theorem B1427141 : Blo 948586 1427141 := bbase (se 4 (by rfl) ⟨133794, by rfl⟩ : syracuseStep 1427141 = 267589) (by norm_num)
theorem B5424853 : Blo 948586 5424853 := bbase (se 7 (by rfl) ⟨63572, by rfl⟩ : syracuseStep 5424853 = 127145) (by norm_num)
theorem B1427165 : Blo 948586 1427165 := bbase (se 3 (by rfl) ⟨267593, by rfl⟩ : syracuseStep 1427165 = 535187) (by norm_num)
theorem B1427189 : Blo 948586 1427189 := bbase (se 5 (by rfl) ⟨66899, by rfl⟩ : syracuseStep 1427189 = 133799) (by norm_num)
theorem B1427213 : Blo 948586 1427213 := bbase (se 3 (by rfl) ⟨267602, by rfl⟩ : syracuseStep 1427213 = 535205) (by norm_num)
theorem B1427237 : Blo 948586 1427237 := bbase (se 4 (by rfl) ⟨133803, by rfl⟩ : syracuseStep 1427237 = 267607) (by norm_num)
theorem B1525549 : Blo 948586 1525549 := bbase (se 3 (by rfl) ⟨286040, by rfl⟩ : syracuseStep 1525549 = 572081) (by norm_num)
theorem B2443061 : Blo 948586 2443061 := bbase (se 5 (by rfl) ⟨114518, by rfl⟩ : syracuseStep 2443061 = 229037) (by norm_num)
theorem B1427261 : Blo 948586 1427261 := bbase (se 3 (by rfl) ⟨267611, by rfl⟩ : syracuseStep 1427261 = 535223) (by norm_num)
theorem B1427285 : Blo 948586 1427285 := bbase (se 9 (by rfl) ⟨4181, by rfl⟩ : syracuseStep 1427285 = 8363) (by norm_num)
theorem B1427309 : Blo 948586 1427309 := bbase (se 3 (by rfl) ⟨267620, by rfl⟩ : syracuseStep 1427309 = 535241) (by norm_num)
theorem B2410357 : Blo 948586 2410357 := bbase (se 5 (by rfl) ⟨112985, by rfl⟩ : syracuseStep 2410357 = 225971) (by norm_num)
theorem B1427333 : Blo 948586 1427333 := bbase (se 4 (by rfl) ⟨133812, by rfl⟩ : syracuseStep 1427333 = 267625) (by norm_num)
theorem B1427357 : Blo 948586 1427357 := bbase (se 3 (by rfl) ⟨267629, by rfl⟩ : syracuseStep 1427357 = 535259) (by norm_num)
theorem B1427381 : Blo 948586 1427381 := bbase (se 5 (by rfl) ⟨66908, by rfl⟩ : syracuseStep 1427381 = 133817) (by norm_num)
theorem B1427405 : Blo 948586 1427405 := bbase (se 3 (by rfl) ⟨267638, by rfl⟩ : syracuseStep 1427405 = 535277) (by norm_num)
theorem B1427429 : Blo 948586 1427429 := bbase (se 4 (by rfl) ⟨133821, by rfl⟩ : syracuseStep 1427429 = 267643) (by norm_num)
theorem B2410469 : Blo 948586 2410469 := bbase (se 4 (by rfl) ⟨225981, by rfl⟩ : syracuseStep 2410469 = 451963) (by norm_num)
theorem B1427453 : Blo 948586 1427453 := bbase (se 3 (by rfl) ⟨267647, by rfl⟩ : syracuseStep 1427453 = 535295) (by norm_num)
theorem B2672645 : Blo 948586 2672645 := bbase (se 4 (by rfl) ⟨250560, by rfl⟩ : syracuseStep 2672645 = 501121) (by norm_num)
theorem B1427477 : Blo 948586 1427477 := bbase (se 6 (by rfl) ⟨33456, by rfl⟩ : syracuseStep 1427477 = 66913) (by norm_num)
theorem B1427501 : Blo 948586 1427501 := bbase (se 3 (by rfl) ⟨267656, by rfl⟩ : syracuseStep 1427501 = 535313) (by norm_num)
theorem B1525805 : Blo 948586 1525805 := bbase (se 3 (by rfl) ⟨286088, by rfl⟩ : syracuseStep 1525805 = 572177) (by norm_num)
theorem B1427525 : Blo 948586 1427525 := bbase (se 4 (by rfl) ⟨133830, by rfl⟩ : syracuseStep 1427525 = 267661) (by norm_num)
theorem B1427549 : Blo 948586 1427549 := bbase (se 3 (by rfl) ⟨267665, by rfl⟩ : syracuseStep 1427549 = 535331) (by norm_num)
theorem B2705525 : Blo 948586 2705525 := bbase (se 5 (by rfl) ⟨126821, by rfl⟩ : syracuseStep 2705525 = 253643) (by norm_num)
theorem B1427573 : Blo 948586 1427573 := bbase (se 5 (by rfl) ⟨66917, by rfl⟩ : syracuseStep 1427573 = 133835) (by norm_num)
theorem B1427597 : Blo 948586 1427597 := bbase (se 3 (by rfl) ⟨267674, by rfl⟩ : syracuseStep 1427597 = 535349) (by norm_num)
theorem B1067161 : Blo 948586 1067161 := bbase (se 2 (by rfl) ⟨400185, by rfl⟩ : syracuseStep 1067161 = 800371) (by norm_num)
theorem B1853597 : Blo 948586 1853597 := bbase (se 3 (by rfl) ⟨347549, by rfl⟩ : syracuseStep 1853597 = 695099) (by norm_num)
theorem B1427621 : Blo 948586 1427621 := bbase (se 4 (by rfl) ⟨133839, by rfl⟩ : syracuseStep 1427621 = 267679) (by norm_num)
theorem B2410661 : Blo 948586 2410661 := bbase (se 4 (by rfl) ⟨225999, by rfl⟩ : syracuseStep 2410661 = 451999) (by norm_num)
theorem B1067197 : Blo 948586 1067197 := bbase (se 3 (by rfl) ⟨200099, by rfl⟩ : syracuseStep 1067197 = 400199) (by norm_num)
theorem B1427645 : Blo 948586 1427645 := bbase (se 3 (by rfl) ⟨267683, by rfl⟩ : syracuseStep 1427645 = 535367) (by norm_num)
theorem B1427669 : Blo 948586 1427669 := bbase (se 7 (by rfl) ⟨16730, by rfl⟩ : syracuseStep 1427669 = 33461) (by norm_num)
theorem B1067233 : Blo 948586 1067233 := bbase (se 2 (by rfl) ⟨400212, by rfl⟩ : syracuseStep 1067233 = 800425) (by norm_num)
theorem B1427693 : Blo 948586 1427693 := bbase (se 3 (by rfl) ⟨267692, by rfl⟩ : syracuseStep 1427693 = 535385) (by norm_num)
theorem B8669429 : Blo 948586 8669429 := bbase (se 5 (by rfl) ⟨406379, by rfl⟩ : syracuseStep 8669429 = 812759) (by norm_num)
theorem B1067269 : Blo 948586 1067269 := bbase (se 4 (by rfl) ⟨100056, by rfl⟩ : syracuseStep 1067269 = 200113) (by norm_num)
theorem B1427717 : Blo 948586 1427717 := bbase (se 4 (by rfl) ⟨133848, by rfl⟩ : syracuseStep 1427717 = 267697) (by norm_num)
theorem B1427741 : Blo 948586 1427741 := bbase (se 3 (by rfl) ⟨267701, by rfl⟩ : syracuseStep 1427741 = 535403) (by norm_num)
theorem B1067305 : Blo 948586 1067305 := bbase (se 2 (by rfl) ⟨400239, by rfl⟩ : syracuseStep 1067305 = 800479) (by norm_num)
theorem B1427765 : Blo 948586 1427765 := bbase (se 5 (by rfl) ⟨66926, by rfl⟩ : syracuseStep 1427765 = 133853) (by norm_num)
theorem B1067341 : Blo 948586 1067341 := bbase (se 3 (by rfl) ⟨200126, by rfl⟩ : syracuseStep 1067341 = 400253) (by norm_num)
theorem B1427789 : Blo 948586 1427789 := bbase (se 3 (by rfl) ⟨267710, by rfl⟩ : syracuseStep 1427789 = 535421) (by norm_num)
theorem B1427813 : Blo 948586 1427813 := bbase (se 4 (by rfl) ⟨133857, by rfl⟩ : syracuseStep 1427813 = 267715) (by norm_num)
theorem B2279789 : Blo 948586 2279789 := bbase (se 3 (by rfl) ⟨427460, by rfl⟩ : syracuseStep 2279789 = 854921) (by norm_num)
theorem B1067377 : Blo 948586 1067377 := bbase (se 2 (by rfl) ⟨400266, by rfl⟩ : syracuseStep 1067377 = 800533) (by norm_num)
theorem B1427837 : Blo 948586 1427837 := bbase (se 3 (by rfl) ⟨267719, by rfl⟩ : syracuseStep 1427837 = 535439) (by norm_num)
theorem B1067413 : Blo 948586 1067413 := bbase (se 6 (by rfl) ⟨25017, by rfl⟩ : syracuseStep 1067413 = 50035) (by norm_num)
theorem B1427861 : Blo 948586 1427861 := bbase (se 6 (by rfl) ⟨33465, by rfl⟩ : syracuseStep 1427861 = 66931) (by norm_num)
theorem B2279845 : Blo 948586 2279845 := bbase (se 4 (by rfl) ⟨213735, by rfl⟩ : syracuseStep 2279845 = 427471) (by norm_num)
theorem B1427885 : Blo 948586 1427885 := bbase (se 3 (by rfl) ⟨267728, by rfl⟩ : syracuseStep 1427885 = 535457) (by norm_num)
theorem B1067449 : Blo 948586 1067449 := bbase (se 2 (by rfl) ⟨400293, by rfl⟩ : syracuseStep 1067449 = 800587) (by norm_num)
theorem B1427909 : Blo 948586 1427909 := bbase (se 4 (by rfl) ⟨133866, by rfl⟩ : syracuseStep 1427909 = 267733) (by norm_num)
theorem B1067485 : Blo 948586 1067485 := bbase (se 3 (by rfl) ⟨200153, by rfl⟩ : syracuseStep 1067485 = 400307) (by norm_num)
theorem B1427933 : Blo 948586 1427933 := bbase (se 3 (by rfl) ⟨267737, by rfl⟩ : syracuseStep 1427933 = 535475) (by norm_num)
theorem B4573685 : Blo 948586 4573685 := bbase (se 5 (by rfl) ⟨214391, by rfl⟩ : syracuseStep 4573685 = 428783) (by norm_num)
theorem B1427957 : Blo 948586 1427957 := bbase (se 5 (by rfl) ⟨66935, by rfl⟩ : syracuseStep 1427957 = 133871) (by norm_num)
theorem B2411005 : Blo 948586 2411005 := bbase (se 3 (by rfl) ⟨452063, by rfl⟩ : syracuseStep 2411005 = 904127) (by norm_num)
theorem B1067521 : Blo 948586 1067521 := bbase (se 2 (by rfl) ⟨400320, by rfl⟩ : syracuseStep 1067521 = 800641) (by norm_num)
theorem B1427981 : Blo 948586 1427981 := bbase (se 3 (by rfl) ⟨267746, by rfl⟩ : syracuseStep 1427981 = 535493) (by norm_num)
theorem B1067557 : Blo 948586 1067557 := bbase (se 4 (by rfl) ⟨100083, by rfl⟩ : syracuseStep 1067557 = 200167) (by norm_num)
theorem B2705957 : Blo 948586 2705957 := bbase (se 4 (by rfl) ⟨253683, by rfl⟩ : syracuseStep 2705957 = 507367) (by norm_num)
theorem B1428005 : Blo 948586 1428005 := bbase (se 4 (by rfl) ⟨133875, by rfl⟩ : syracuseStep 1428005 = 267751) (by norm_num)
theorem B1428029 : Blo 948586 1428029 := bbase (se 3 (by rfl) ⟨267755, by rfl⟩ : syracuseStep 1428029 = 535511) (by norm_num)
theorem B1067593 : Blo 948586 1067593 := bbase (se 2 (by rfl) ⟨400347, by rfl⟩ : syracuseStep 1067593 = 800695) (by norm_num)
theorem B3525205 : Blo 948586 3525205 := bbase (se 8 (by rfl) ⟨20655, by rfl⟩ : syracuseStep 3525205 = 41311) (by norm_num)
theorem B1428053 : Blo 948586 1428053 := bbase (se 8 (by rfl) ⟨8367, by rfl⟩ : syracuseStep 1428053 = 16735) (by norm_num)
theorem B1067629 : Blo 948586 1067629 := bbase (se 3 (by rfl) ⟨200180, by rfl⟩ : syracuseStep 1067629 = 400361) (by norm_num)
theorem B1428077 : Blo 948586 1428077 := bbase (se 3 (by rfl) ⟨267764, by rfl⟩ : syracuseStep 1428077 = 535529) (by norm_num)
theorem B2411117 : Blo 948586 2411117 := bbase (se 3 (by rfl) ⟨452084, by rfl⟩ : syracuseStep 2411117 = 904169) (by norm_num)
theorem B1428101 : Blo 948586 1428101 := bbase (se 4 (by rfl) ⟨133884, by rfl⟩ : syracuseStep 1428101 = 267769) (by norm_num)
theorem B1067665 : Blo 948586 1067665 := bbase (se 2 (by rfl) ⟨400374, by rfl⟩ : syracuseStep 1067665 = 800749) (by norm_num)
theorem B1428125 : Blo 948586 1428125 := bbase (se 3 (by rfl) ⟨267773, by rfl⟩ : syracuseStep 1428125 = 535547) (by norm_num)
theorem B1067701 : Blo 948586 1067701 := bbase (se 5 (by rfl) ⟨50048, by rfl⟩ : syracuseStep 1067701 = 100097) (by norm_num)
theorem B1428149 : Blo 948586 1428149 := bbase (se 5 (by rfl) ⟨66944, by rfl⟩ : syracuseStep 1428149 = 133889) (by norm_num)
theorem B1428173 : Blo 948586 1428173 := bbase (se 3 (by rfl) ⟨267782, by rfl⟩ : syracuseStep 1428173 = 535565) (by norm_num)
theorem B1067737 : Blo 948586 1067737 := bbase (se 2 (by rfl) ⟨400401, by rfl⟩ : syracuseStep 1067737 = 800803) (by norm_num)
theorem B1428197 : Blo 948586 1428197 := bbase (se 4 (by rfl) ⟨133893, by rfl⟩ : syracuseStep 1428197 = 267787) (by norm_num)
theorem B1067773 : Blo 948586 1067773 := bbase (se 3 (by rfl) ⟨200207, by rfl⟩ : syracuseStep 1067773 = 400415) (by norm_num)
theorem B1428221 : Blo 948586 1428221 := bbase (se 3 (by rfl) ⟨267791, by rfl⟩ : syracuseStep 1428221 = 535583) (by norm_num)
theorem B1428245 : Blo 948586 1428245 := bbase (se 6 (by rfl) ⟨33474, by rfl⟩ : syracuseStep 1428245 = 66949) (by norm_num)
theorem B1067809 : Blo 948586 1067809 := bbase (se 2 (by rfl) ⟨400428, by rfl⟩ : syracuseStep 1067809 = 800857) (by norm_num)
theorem B1428269 : Blo 948586 1428269 := bbase (se 3 (by rfl) ⟨267800, by rfl⟩ : syracuseStep 1428269 = 535601) (by norm_num)
theorem B1067845 : Blo 948586 1067845 := bbase (se 4 (by rfl) ⟨100110, by rfl⟩ : syracuseStep 1067845 = 200221) (by norm_num)
theorem B1428293 : Blo 948586 1428293 := bbase (se 4 (by rfl) ⟨133902, by rfl⟩ : syracuseStep 1428293 = 267805) (by norm_num)
theorem B1428317 : Blo 948586 1428317 := bbase (se 3 (by rfl) ⟨267809, by rfl⟩ : syracuseStep 1428317 = 535619) (by norm_num)
theorem B1067881 : Blo 948586 1067881 := bbase (se 2 (by rfl) ⟨400455, by rfl⟩ : syracuseStep 1067881 = 800911) (by norm_num)
theorem B7228277 : Blo 948586 7228277 := bbase (se 5 (by rfl) ⟨338825, by rfl⟩ : syracuseStep 7228277 = 677651) (by norm_num)
theorem B1428341 : Blo 948586 1428341 := bbase (se 5 (by rfl) ⟨66953, by rfl⟩ : syracuseStep 1428341 = 133907) (by norm_num)
theorem B4803461 : Blo 948586 4803461 := bbase (se 4 (by rfl) ⟨450324, by rfl⟩ : syracuseStep 4803461 = 900649) (by norm_num)
theorem B1067917 : Blo 948586 1067917 := bbase (se 3 (by rfl) ⟨200234, by rfl⟩ : syracuseStep 1067917 = 400469) (by norm_num)
theorem B1428365 : Blo 948586 1428365 := bbase (se 3 (by rfl) ⟨267818, by rfl⟩ : syracuseStep 1428365 = 535637) (by norm_num)
theorem B1428389 : Blo 948586 1428389 := bbase (se 4 (by rfl) ⟨133911, by rfl⟩ : syracuseStep 1428389 = 267823) (by norm_num)
theorem B1067953 : Blo 948586 1067953 := bbase (se 2 (by rfl) ⟨400482, by rfl⟩ : syracuseStep 1067953 = 800965) (by norm_num)
theorem B1428413 : Blo 948586 1428413 := bbase (se 3 (by rfl) ⟨267827, by rfl⟩ : syracuseStep 1428413 = 535655) (by norm_num)
theorem B1067989 : Blo 948586 1067989 := bbase (se 7 (by rfl) ⟨12515, by rfl⟩ : syracuseStep 1067989 = 25031) (by norm_num)
theorem B1428437 : Blo 948586 1428437 := bbase (se 7 (by rfl) ⟨16739, by rfl⟩ : syracuseStep 1428437 = 33479) (by norm_num)
theorem B1428461 : Blo 948586 1428461 := bbase (se 3 (by rfl) ⟨267836, by rfl⟩ : syracuseStep 1428461 = 535673) (by norm_num)
theorem B1068025 : Blo 948586 1068025 := bbase (se 2 (by rfl) ⟨400509, by rfl⟩ : syracuseStep 1068025 = 801019) (by norm_num)
theorem B1428485 : Blo 948586 1428485 := bbase (se 4 (by rfl) ⟨133920, by rfl⟩ : syracuseStep 1428485 = 267841) (by norm_num)
theorem B1068061 : Blo 948586 1068061 := bbase (se 3 (by rfl) ⟨200261, by rfl⟩ : syracuseStep 1068061 = 400523) (by norm_num)
theorem B1428509 : Blo 948586 1428509 := bbase (se 3 (by rfl) ⟨267845, by rfl⟩ : syracuseStep 1428509 = 535691) (by norm_num)
theorem B1428533 : Blo 948586 1428533 := bbase (se 5 (by rfl) ⟨66962, by rfl⟩ : syracuseStep 1428533 = 133925) (by norm_num)
theorem B1068097 : Blo 948586 1068097 := bbase (se 2 (by rfl) ⟨400536, by rfl⟩ : syracuseStep 1068097 = 801073) (by norm_num)
theorem B1428557 : Blo 948586 1428557 := bbase (se 3 (by rfl) ⟨267854, by rfl⟩ : syracuseStep 1428557 = 535709) (by norm_num)
theorem B1068133 : Blo 948586 1068133 := bbase (se 4 (by rfl) ⟨100137, by rfl⟩ : syracuseStep 1068133 = 200275) (by norm_num)
theorem B1428581 : Blo 948586 1428581 := bbase (se 4 (by rfl) ⟨133929, by rfl⟩ : syracuseStep 1428581 = 267859) (by norm_num)
theorem B1428605 : Blo 948586 1428605 := bbase (se 3 (by rfl) ⟨267863, by rfl⟩ : syracuseStep 1428605 = 535727) (by norm_num)
theorem B1068169 : Blo 948586 1068169 := bbase (se 2 (by rfl) ⟨400563, by rfl⟩ : syracuseStep 1068169 = 801127) (by norm_num)
theorem B1428629 : Blo 948586 1428629 := bbase (se 6 (by rfl) ⟨33483, by rfl⟩ : syracuseStep 1428629 = 66967) (by norm_num)
theorem B1068205 : Blo 948586 1068205 := bbase (se 3 (by rfl) ⟨200288, by rfl⟩ : syracuseStep 1068205 = 400577) (by norm_num)
theorem B1428653 : Blo 948586 1428653 := bbase (se 3 (by rfl) ⟨267872, by rfl⟩ : syracuseStep 1428653 = 535745) (by norm_num)
theorem B3427525 : Blo 948586 3427525 := bbase (se 4 (by rfl) ⟨321330, by rfl⟩ : syracuseStep 3427525 = 642661) (by norm_num)
theorem B1428677 : Blo 948586 1428677 := bbase (se 4 (by rfl) ⟨133938, by rfl⟩ : syracuseStep 1428677 = 267877) (by norm_num)
theorem B1068241 : Blo 948586 1068241 := bbase (se 2 (by rfl) ⟨400590, by rfl⟩ : syracuseStep 1068241 = 801181) (by norm_num)
theorem B1428701 : Blo 948586 1428701 := bbase (se 3 (by rfl) ⟨267881, by rfl⟩ : syracuseStep 1428701 = 535763) (by norm_num)
theorem B1068277 : Blo 948586 1068277 := bbase (se 5 (by rfl) ⟨50075, by rfl⟩ : syracuseStep 1068277 = 100151) (by norm_num)
theorem B1428725 : Blo 948586 1428725 := bbase (se 5 (by rfl) ⟨66971, by rfl⟩ : syracuseStep 1428725 = 133943) (by norm_num)
theorem B1428749 : Blo 948586 1428749 := bbase (se 3 (by rfl) ⟨267890, by rfl⟩ : syracuseStep 1428749 = 535781) (by norm_num)
theorem B2706709 : Blo 948586 2706709 := bbase (se 6 (by rfl) ⟨63438, by rfl⟩ : syracuseStep 2706709 = 126877) (by norm_num)
theorem B1068313 : Blo 948586 1068313 := bbase (se 2 (by rfl) ⟨400617, by rfl⟩ : syracuseStep 1068313 = 801235) (by norm_num)
theorem B1428773 : Blo 948586 1428773 := bbase (se 4 (by rfl) ⟨133947, by rfl⟩ : syracuseStep 1428773 = 267895) (by norm_num)
theorem B1068349 : Blo 948586 1068349 := bbase (se 3 (by rfl) ⟨200315, by rfl⟩ : syracuseStep 1068349 = 400631) (by norm_num)
theorem B1428797 : Blo 948586 1428797 := bbase (se 3 (by rfl) ⟨267899, by rfl⟩ : syracuseStep 1428797 = 535799) (by norm_num)
theorem B1428821 : Blo 948586 1428821 := bbase (se 11 (by rfl) ⟨1046, by rfl⟩ : syracuseStep 1428821 = 2093) (by norm_num)
theorem B1625437 : Blo 948586 1625437 := bbase (se 3 (by rfl) ⟨304769, by rfl⟩ : syracuseStep 1625437 = 609539) (by norm_num)
theorem B1068385 : Blo 948586 1068385 := bbase (se 2 (by rfl) ⟨400644, by rfl⟩ : syracuseStep 1068385 = 801289) (by norm_num)
theorem B1428845 : Blo 948586 1428845 := bbase (se 3 (by rfl) ⟨267908, by rfl⟩ : syracuseStep 1428845 = 535817) (by norm_num)
theorem B1068421 : Blo 948586 1068421 := bbase (se 4 (by rfl) ⟨100164, by rfl⟩ : syracuseStep 1068421 = 200329) (by norm_num)
theorem B1428869 : Blo 948586 1428869 := bbase (se 4 (by rfl) ⟨133956, by rfl⟩ : syracuseStep 1428869 = 267913) (by norm_num)
theorem B2280845 : Blo 948586 2280845 := bbase (se 3 (by rfl) ⟨427658, by rfl⟩ : syracuseStep 2280845 = 855317) (by norm_num)
theorem B1068457 : Blo 948586 1068457 := bbase (se 2 (by rfl) ⟨400671, by rfl⟩ : syracuseStep 1068457 = 801343) (by norm_num)
theorem B1068493 : Blo 948586 1068493 := bbase (se 3 (by rfl) ⟨200342, by rfl⟩ : syracuseStep 1068493 = 400685) (by norm_num)
theorem B1068529 : Blo 948586 1068529 := bbase (se 2 (by rfl) ⟨400698, by rfl⟩ : syracuseStep 1068529 = 801397) (by norm_num)
theorem B1068565 : Blo 948586 1068565 := bbase (se 6 (by rfl) ⟨25044, by rfl⟩ : syracuseStep 1068565 = 50089) (by norm_num)
theorem B1068601 : Blo 948586 1068601 := bbase (se 2 (by rfl) ⟨400725, by rfl⟩ : syracuseStep 1068601 = 801451) (by norm_num)
theorem B1068637 : Blo 948586 1068637 := bbase (se 3 (by rfl) ⟨200369, by rfl⟩ : syracuseStep 1068637 = 400739) (by norm_num)
theorem B1068673 : Blo 948586 1068673 := bbase (se 2 (by rfl) ⟨400752, by rfl⟩ : syracuseStep 1068673 = 801505) (by norm_num)
theorem B3853973 : Blo 948586 3853973 := bbase (se 6 (by rfl) ⟨90327, by rfl⟩ : syracuseStep 3853973 = 180655) (by norm_num)
theorem B1068709 : Blo 948586 1068709 := bbase (se 4 (by rfl) ⟨100191, by rfl⟩ : syracuseStep 1068709 = 200383) (by norm_num)
theorem B6082229 : Blo 948586 6082229 := bbase (se 5 (by rfl) ⟨285104, by rfl⟩ : syracuseStep 6082229 = 570209) (by norm_num)
theorem B1068745 : Blo 948586 1068745 := bbase (se 2 (by rfl) ⟨400779, by rfl⟩ : syracuseStep 1068745 = 801559) (by norm_num)
theorem B1068781 : Blo 948586 1068781 := bbase (se 3 (by rfl) ⟨200396, by rfl⟩ : syracuseStep 1068781 = 400793) (by norm_num)
theorem B1068817 : Blo 948586 1068817 := bbase (se 2 (by rfl) ⟨400806, by rfl⟩ : syracuseStep 1068817 = 801613) (by norm_num)
theorem B1068853 : Blo 948586 1068853 := bbase (se 5 (by rfl) ⟨50102, by rfl⟩ : syracuseStep 1068853 = 100205) (by norm_num)
theorem B1068889 : Blo 948586 1068889 := bbase (se 2 (by rfl) ⟨400833, by rfl⟩ : syracuseStep 1068889 = 801667) (by norm_num)
theorem B1068925 : Blo 948586 1068925 := bbase (se 3 (by rfl) ⟨200423, by rfl⟩ : syracuseStep 1068925 = 400847) (by norm_num)
theorem B1068961 : Blo 948586 1068961 := bbase (se 2 (by rfl) ⟨400860, by rfl⟩ : syracuseStep 1068961 = 801721) (by norm_num)
theorem B1068997 : Blo 948586 1068997 := bbase (se 4 (by rfl) ⟨100218, by rfl⟩ : syracuseStep 1068997 = 200437) (by norm_num)
theorem B1069033 : Blo 948586 1069033 := bbase (se 2 (by rfl) ⟨400887, by rfl⟩ : syracuseStep 1069033 = 801775) (by norm_num)
theorem B1069069 : Blo 948586 1069069 := bbase (se 3 (by rfl) ⟨200450, by rfl⟩ : syracuseStep 1069069 = 400901) (by norm_num)
theorem B16240661 : Blo 948586 16240661 := bbase (se 6 (by rfl) ⟨380640, by rfl⟩ : syracuseStep 16240661 = 761281) (by norm_num)
theorem B1069105 : Blo 948586 1069105 := bbase (se 2 (by rfl) ⟨400914, by rfl⟩ : syracuseStep 1069105 = 801829) (by norm_num)
theorem B1069141 : Blo 948586 1069141 := bbase (se 8 (by rfl) ⟨6264, by rfl⟩ : syracuseStep 1069141 = 12529) (by norm_num)
theorem B1069177 : Blo 948586 1069177 := bbase (se 2 (by rfl) ⟨400941, by rfl⟩ : syracuseStep 1069177 = 801883) (by norm_num)
theorem B4804757 : Blo 948586 4804757 := bbase (se 6 (by rfl) ⟨112611, by rfl⟩ : syracuseStep 4804757 = 225223) (by norm_num)
theorem B1069213 : Blo 948586 1069213 := bbase (se 3 (by rfl) ⟨200477, by rfl⟩ : syracuseStep 1069213 = 400955) (by norm_num)
theorem B1069249 : Blo 948586 1069249 := bbase (se 2 (by rfl) ⟨400968, by rfl⟩ : syracuseStep 1069249 = 801937) (by norm_num)
theorem B1069285 : Blo 948586 1069285 := bbase (se 4 (by rfl) ⟨100245, by rfl⟩ : syracuseStep 1069285 = 200491) (by norm_num)
theorem B1069321 : Blo 948586 1069321 := bbase (se 2 (by rfl) ⟨400995, by rfl⟩ : syracuseStep 1069321 = 801991) (by norm_num)
theorem B1069357 : Blo 948586 1069357 := bbase (se 3 (by rfl) ⟨200504, by rfl⟩ : syracuseStep 1069357 = 401009) (by norm_num)
theorem B1069393 : Blo 948586 1069393 := bbase (se 2 (by rfl) ⟨401022, by rfl⟩ : syracuseStep 1069393 = 802045) (by norm_num)
theorem B1069429 : Blo 948586 1069429 := bbase (se 5 (by rfl) ⟨50129, by rfl⟩ : syracuseStep 1069429 = 100259) (by norm_num)
theorem B1069465 : Blo 948586 1069465 := bbase (se 2 (by rfl) ⟨401049, by rfl⟩ : syracuseStep 1069465 = 802099) (by norm_num)
theorem B1069501 : Blo 948586 1069501 := bbase (se 3 (by rfl) ⟨200531, by rfl⟩ : syracuseStep 1069501 = 401063) (by norm_num)
theorem B1200577 : Blo 948586 1200577 := bbase (se 2 (by rfl) ⟨450216, by rfl⟩ : syracuseStep 1200577 = 900433) (by norm_num)
theorem B1069537 : Blo 948586 1069537 := bbase (se 2 (by rfl) ⟨401076, by rfl⟩ : syracuseStep 1069537 = 802153) (by norm_num)
theorem B1069573 : Blo 948586 1069573 := bbase (se 4 (by rfl) ⟨100272, by rfl⟩ : syracuseStep 1069573 = 200545) (by norm_num)
theorem B5788181 : Blo 948586 5788181 := bbase (se 6 (by rfl) ⟨135660, by rfl⟩ : syracuseStep 5788181 = 271321) (by norm_num)
theorem B1200673 : Blo 948586 1200673 := bbase (se 2 (by rfl) ⟨450252, by rfl⟩ : syracuseStep 1200673 = 900505) (by norm_num)
theorem B1069609 : Blo 948586 1069609 := bbase (se 2 (by rfl) ⟨401103, by rfl⟩ : syracuseStep 1069609 = 802207) (by norm_num)
theorem B1069645 : Blo 948586 1069645 := bbase (se 3 (by rfl) ⟨200558, by rfl⟩ : syracuseStep 1069645 = 401117) (by norm_num)
theorem B1069681 : Blo 948586 1069681 := bbase (se 2 (by rfl) ⟨401130, by rfl⟩ : syracuseStep 1069681 = 802261) (by norm_num)
theorem B1069717 : Blo 948586 1069717 := bbase (se 6 (by rfl) ⟨25071, by rfl⟩ : syracuseStep 1069717 = 50143) (by norm_num)
theorem B1069753 : Blo 948586 1069753 := bbase (se 2 (by rfl) ⟨401157, by rfl⟩ : syracuseStep 1069753 = 802315) (by norm_num)
theorem B1200845 : Blo 948586 1200845 := bbase (se 3 (by rfl) ⟨225158, by rfl⟩ : syracuseStep 1200845 = 450317) (by norm_num)
theorem B1069789 : Blo 948586 1069789 := bbase (se 3 (by rfl) ⟨200585, by rfl⟩ : syracuseStep 1069789 = 401171) (by norm_num)
theorem B1069825 : Blo 948586 1069825 := bbase (se 2 (by rfl) ⟨401184, by rfl⟩ : syracuseStep 1069825 = 802369) (by norm_num)
theorem B1200901 : Blo 948586 1200901 := bbase (se 4 (by rfl) ⟨112584, by rfl⟩ : syracuseStep 1200901 = 225169) (by norm_num)
theorem B1069861 : Blo 948586 1069861 := bbase (se 4 (by rfl) ⟨100299, by rfl⟩ : syracuseStep 1069861 = 200599) (by norm_num)
theorem B1069897 : Blo 948586 1069897 := bbase (se 2 (by rfl) ⟨401211, by rfl⟩ : syracuseStep 1069897 = 802423) (by norm_num)
theorem B1200997 : Blo 948586 1200997 := bbase (se 4 (by rfl) ⟨112593, by rfl⟩ : syracuseStep 1200997 = 225187) (by norm_num)
theorem B1069933 : Blo 948586 1069933 := bbase (se 3 (by rfl) ⟨200612, by rfl⟩ : syracuseStep 1069933 = 401225) (by norm_num)
theorem B3855221 : Blo 948586 3855221 := bbase (se 5 (by rfl) ⟨180713, by rfl⟩ : syracuseStep 3855221 = 361427) (by norm_num)
theorem B1069969 : Blo 948586 1069969 := bbase (se 2 (by rfl) ⟨401238, by rfl⟩ : syracuseStep 1069969 = 802477) (by norm_num)
theorem B1070005 : Blo 948586 1070005 := bbase (se 5 (by rfl) ⟨50156, by rfl⟩ : syracuseStep 1070005 = 100313) (by norm_num)
theorem B1070041 : Blo 948586 1070041 := bbase (se 2 (by rfl) ⟨401265, by rfl⟩ : syracuseStep 1070041 = 802531) (by norm_num)
theorem B1070077 : Blo 948586 1070077 := bbase (se 3 (by rfl) ⟨200639, by rfl⟩ : syracuseStep 1070077 = 401279) (by norm_num)
theorem B1201169 : Blo 948586 1201169 := bbase (se 2 (by rfl) ⟨450438, by rfl⟩ : syracuseStep 1201169 = 900877) (by norm_num)
theorem B1070113 : Blo 948586 1070113 := bbase (se 2 (by rfl) ⟨401292, by rfl⟩ : syracuseStep 1070113 = 802585) (by norm_num)
theorem B1070149 : Blo 948586 1070149 := bbase (se 4 (by rfl) ⟨100326, by rfl⟩ : syracuseStep 1070149 = 200653) (by norm_num)
theorem B1201225 : Blo 948586 1201225 := bbase (se 2 (by rfl) ⟨450459, by rfl⟩ : syracuseStep 1201225 = 900919) (by norm_num)
theorem B1070185 : Blo 948586 1070185 := bbase (se 2 (by rfl) ⟨401319, by rfl⟩ : syracuseStep 1070185 = 802639) (by norm_num)
theorem B4052101 : Blo 948586 4052101 := bbase (se 4 (by rfl) ⟨379884, by rfl⟩ : syracuseStep 4052101 = 759769) (by norm_num)
theorem B1070221 : Blo 948586 1070221 := bbase (se 3 (by rfl) ⟨200666, by rfl⟩ : syracuseStep 1070221 = 401333) (by norm_num)
theorem B1201321 : Blo 948586 1201321 := bbase (se 2 (by rfl) ⟨450495, by rfl⟩ : syracuseStep 1201321 = 900991) (by norm_num)
theorem B1070257 : Blo 948586 1070257 := bbase (se 2 (by rfl) ⟨401346, by rfl⟩ : syracuseStep 1070257 = 802693) (by norm_num)
theorem B1070293 : Blo 948586 1070293 := bbase (se 7 (by rfl) ⟨12542, by rfl⟩ : syracuseStep 1070293 = 25085) (by norm_num)
theorem B1070329 : Blo 948586 1070329 := bbase (se 2 (by rfl) ⟨401373, by rfl⟩ : syracuseStep 1070329 = 802747) (by norm_num)
theorem B1070365 : Blo 948586 1070365 := bbase (se 3 (by rfl) ⟨200693, by rfl⟩ : syracuseStep 1070365 = 401387) (by norm_num)
theorem B1070401 : Blo 948586 1070401 := bbase (se 2 (by rfl) ⟨401400, by rfl⟩ : syracuseStep 1070401 = 802801) (by norm_num)
theorem B1201493 : Blo 948586 1201493 := bbase (se 16 (by rfl) ⟨27, by rfl⟩ : syracuseStep 1201493 = 55) (by norm_num)
theorem B32986453 : Blo 948586 32986453 := bbase (se 17 (by rfl) ⟨377, by rfl⟩ : syracuseStep 32986453 = 755) (by norm_num)
theorem B1070437 : Blo 948586 1070437 := bbase (se 4 (by rfl) ⟨100353, by rfl⟩ : syracuseStep 1070437 = 200707) (by norm_num)
theorem B1070473 : Blo 948586 1070473 := bbase (se 2 (by rfl) ⟨401427, by rfl⟩ : syracuseStep 1070473 = 802855) (by norm_num)
theorem B1201549 : Blo 948586 1201549 := bbase (se 3 (by rfl) ⟨225290, by rfl⟩ : syracuseStep 1201549 = 450581) (by norm_num)
theorem B4806053 : Blo 948586 4806053 := bbase (se 4 (by rfl) ⟨450567, by rfl⟩ : syracuseStep 4806053 = 901135) (by norm_num)
theorem B1070509 : Blo 948586 1070509 := bbase (se 3 (by rfl) ⟨200720, by rfl⟩ : syracuseStep 1070509 = 401441) (by norm_num)
theorem B1070545 : Blo 948586 1070545 := bbase (se 2 (by rfl) ⟨401454, by rfl⟩ : syracuseStep 1070545 = 802909) (by norm_num)
theorem B1201645 : Blo 948586 1201645 := bbase (se 3 (by rfl) ⟨225308, by rfl⟩ : syracuseStep 1201645 = 450617) (by norm_num)
theorem B1070581 : Blo 948586 1070581 := bbase (se 5 (by rfl) ⟨50183, by rfl⟩ : syracuseStep 1070581 = 100367) (by norm_num)
theorem B1070617 : Blo 948586 1070617 := bbase (se 2 (by rfl) ⟨401481, by rfl⟩ : syracuseStep 1070617 = 802963) (by norm_num)
theorem B1070653 : Blo 948586 1070653 := bbase (se 3 (by rfl) ⟨200747, by rfl⟩ : syracuseStep 1070653 = 401495) (by norm_num)
theorem B4576837 : Blo 948586 4576837 := bbase (se 4 (by rfl) ⟨429078, by rfl⟩ : syracuseStep 4576837 = 858157) (by norm_num)
theorem B1070689 : Blo 948586 1070689 := bbase (se 2 (by rfl) ⟨401508, by rfl⟩ : syracuseStep 1070689 = 803017) (by norm_num)
theorem B1070725 : Blo 948586 1070725 := bbase (se 4 (by rfl) ⟨100380, by rfl⟩ : syracuseStep 1070725 = 200761) (by norm_num)
theorem B1201817 : Blo 948586 1201817 := bbase (se 2 (by rfl) ⟨450681, by rfl⟩ : syracuseStep 1201817 = 901363) (by norm_num)
theorem B1070761 : Blo 948586 1070761 := bbase (se 2 (by rfl) ⟨401535, by rfl⟩ : syracuseStep 1070761 = 803071) (by norm_num)
theorem B1562285 : Blo 948586 1562285 := bbase (se 3 (by rfl) ⟨292928, by rfl⟩ : syracuseStep 1562285 = 585857) (by norm_num)
theorem B1070797 : Blo 948586 1070797 := bbase (se 3 (by rfl) ⟨200774, by rfl⟩ : syracuseStep 1070797 = 401549) (by norm_num)
theorem B1201873 : Blo 948586 1201873 := bbase (se 2 (by rfl) ⟨450702, by rfl⟩ : syracuseStep 1201873 = 901405) (by norm_num)
theorem B2283221 : Blo 948586 2283221 := bbase (se 7 (by rfl) ⟨26756, by rfl⟩ : syracuseStep 2283221 = 53513) (by norm_num)
theorem B1070833 : Blo 948586 1070833 := bbase (se 2 (by rfl) ⟨401562, by rfl⟩ : syracuseStep 1070833 = 803125) (by norm_num)
theorem B1070869 : Blo 948586 1070869 := bbase (se 6 (by rfl) ⟨25098, by rfl⟩ : syracuseStep 1070869 = 50197) (by norm_num)
theorem B1201969 : Blo 948586 1201969 := bbase (se 2 (by rfl) ⟨450738, by rfl⟩ : syracuseStep 1201969 = 901477) (by norm_num)
theorem B1070905 : Blo 948586 1070905 := bbase (se 2 (by rfl) ⟨401589, by rfl⟩ : syracuseStep 1070905 = 803179) (by norm_num)
theorem B1070941 : Blo 948586 1070941 := bbase (se 3 (by rfl) ⟨200801, by rfl⟩ : syracuseStep 1070941 = 401603) (by norm_num)
theorem B1070977 : Blo 948586 1070977 := bbase (se 2 (by rfl) ⟨401616, by rfl⟩ : syracuseStep 1070977 = 803233) (by norm_num)
theorem B1071013 : Blo 948586 1071013 := bbase (se 4 (by rfl) ⟨100407, by rfl⟩ : syracuseStep 1071013 = 200815) (by norm_num)
theorem B1071049 : Blo 948586 1071049 := bbase (se 2 (by rfl) ⟨401643, by rfl⟩ : syracuseStep 1071049 = 803287) (by norm_num)
theorem B2742229 : Blo 948586 2742229 := bbase (se 7 (by rfl) ⟨32135, by rfl⟩ : syracuseStep 2742229 = 64271) (by norm_num)
theorem B1202141 : Blo 948586 1202141 := bbase (se 3 (by rfl) ⟨225401, by rfl⟩ : syracuseStep 1202141 = 450803) (by norm_num)
theorem B1071085 : Blo 948586 1071085 := bbase (se 3 (by rfl) ⟨200828, by rfl⟩ : syracuseStep 1071085 = 401657) (by norm_num)
theorem B1071121 : Blo 948586 1071121 := bbase (se 2 (by rfl) ⟨401670, by rfl⟩ : syracuseStep 1071121 = 803341) (by norm_num)
theorem B1202197 : Blo 948586 1202197 := bbase (se 6 (by rfl) ⟨28176, by rfl⟩ : syracuseStep 1202197 = 56353) (by norm_num)
theorem B2709557 : Blo 948586 2709557 := bbase (se 5 (by rfl) ⟨127010, by rfl⟩ : syracuseStep 2709557 = 254021) (by norm_num)
theorem B1071157 : Blo 948586 1071157 := bbase (se 5 (by rfl) ⟨50210, by rfl⟩ : syracuseStep 1071157 = 100421) (by norm_num)
theorem B49305685 : Blo 948586 49305685 := bbase (se 8 (by rfl) ⟨288900, by rfl⟩ : syracuseStep 49305685 = 577801) (by norm_num)
theorem B2283605 : Blo 948586 2283605 := bbase (se 8 (by rfl) ⟨13380, by rfl⟩ : syracuseStep 2283605 = 26761) (by norm_num)
theorem B1071193 : Blo 948586 1071193 := bbase (se 2 (by rfl) ⟨401697, by rfl⟩ : syracuseStep 1071193 = 803395) (by norm_num)
theorem B1202293 : Blo 948586 1202293 := bbase (se 5 (by rfl) ⟨56357, by rfl⟩ : syracuseStep 1202293 = 112715) (by norm_num)
theorem B1071229 : Blo 948586 1071229 := bbase (se 3 (by rfl) ⟨200855, by rfl⟩ : syracuseStep 1071229 = 401711) (by norm_num)
theorem B17356949 : Blo 948586 17356949 := bbase (se 6 (by rfl) ⟨406803, by rfl⟩ : syracuseStep 17356949 = 813607) (by norm_num)
theorem B1628309 : Blo 948586 1628309 := bbase (se 6 (by rfl) ⟨38163, by rfl⟩ : syracuseStep 1628309 = 76327) (by norm_num)
theorem B1071265 : Blo 948586 1071265 := bbase (se 2 (by rfl) ⟨401724, by rfl⟩ : syracuseStep 1071265 = 803449) (by norm_num)
theorem B1071301 : Blo 948586 1071301 := bbase (se 4 (by rfl) ⟨100434, by rfl⟩ : syracuseStep 1071301 = 200869) (by norm_num)
theorem B1071337 : Blo 948586 1071337 := bbase (se 2 (by rfl) ⟨401751, by rfl⟩ : syracuseStep 1071337 = 803503) (by norm_num)
theorem B1071373 : Blo 948586 1071373 := bbase (se 3 (by rfl) ⟨200882, by rfl⟩ : syracuseStep 1071373 = 401765) (by norm_num)
theorem B2283805 : Blo 948586 2283805 := bbase (se 3 (by rfl) ⟨428213, by rfl⟩ : syracuseStep 2283805 = 856427) (by norm_num)
theorem B1202465 : Blo 948586 1202465 := bbase (se 2 (by rfl) ⟨450924, by rfl⟩ : syracuseStep 1202465 = 901849) (by norm_num)
theorem B1071409 : Blo 948586 1071409 := bbase (se 2 (by rfl) ⟨401778, by rfl⟩ : syracuseStep 1071409 = 803557) (by norm_num)
theorem B1071445 : Blo 948586 1071445 := bbase (se 10 (by rfl) ⟨1569, by rfl⟩ : syracuseStep 1071445 = 3139) (by norm_num)
theorem B1202521 : Blo 948586 1202521 := bbase (se 2 (by rfl) ⟨450945, by rfl⟩ : syracuseStep 1202521 = 901891) (by norm_num)
theorem B2677093 : Blo 948586 2677093 := bbase (se 4 (by rfl) ⟨250977, by rfl⟩ : syracuseStep 2677093 = 501955) (by norm_num)
theorem B1071481 : Blo 948586 1071481 := bbase (se 2 (by rfl) ⟨401805, by rfl⟩ : syracuseStep 1071481 = 803611) (by norm_num)
theorem B1071517 : Blo 948586 1071517 := bbase (se 3 (by rfl) ⟨200909, by rfl⟩ : syracuseStep 1071517 = 401819) (by norm_num)
theorem B1202617 : Blo 948586 1202617 := bbase (se 2 (by rfl) ⟨450981, by rfl⟩ : syracuseStep 1202617 = 901963) (by norm_num)
theorem B1071553 : Blo 948586 1071553 := bbase (se 2 (by rfl) ⟨401832, by rfl⟩ : syracuseStep 1071553 = 803665) (by norm_num)
theorem B1071589 : Blo 948586 1071589 := bbase (se 4 (by rfl) ⟨100461, by rfl⟩ : syracuseStep 1071589 = 200923) (by norm_num)
theorem B1071625 : Blo 948586 1071625 := bbase (se 2 (by rfl) ⟨401859, by rfl⟩ : syracuseStep 1071625 = 803719) (by norm_num)
theorem B1759781 : Blo 948586 1759781 := bbase (se 4 (by rfl) ⟨164979, by rfl⟩ : syracuseStep 1759781 = 329959) (by norm_num)
theorem B3201605 : Blo 948586 3201605 := bbase (se 4 (by rfl) ⟨300150, by rfl⟩ : syracuseStep 3201605 = 600301) (by norm_num)
theorem B1202789 : Blo 948586 1202789 := bbase (se 4 (by rfl) ⟨112761, by rfl⟩ : syracuseStep 1202789 = 225523) (by norm_num)
theorem B1202845 : Blo 948586 1202845 := bbase (se 3 (by rfl) ⟨225533, by rfl⟩ : syracuseStep 1202845 = 451067) (by norm_num)
theorem B1825445 : Blo 948586 1825445 := bbase (se 4 (by rfl) ⟨171135, by rfl⟩ : syracuseStep 1825445 = 342271) (by norm_num)
theorem B4807349 : Blo 948586 4807349 := bbase (se 5 (by rfl) ⟨225344, by rfl⟩ : syracuseStep 4807349 = 450689) (by norm_num)
theorem B1202941 : Blo 948586 1202941 := bbase (se 3 (by rfl) ⟨225551, by rfl⟩ : syracuseStep 1202941 = 451103) (by norm_num)
theorem B1203113 : Blo 948586 1203113 := bbase (se 2 (by rfl) ⟨451167, by rfl⟩ : syracuseStep 1203113 = 902335) (by norm_num)
theorem B1203169 : Blo 948586 1203169 := bbase (se 2 (by rfl) ⟨451188, by rfl⟩ : syracuseStep 1203169 = 902377) (by norm_num)
theorem B3202037 : Blo 948586 3202037 := bbase (se 5 (by rfl) ⟨150095, by rfl⟩ : syracuseStep 3202037 = 300191) (by norm_num)
theorem B1203265 : Blo 948586 1203265 := bbase (se 2 (by rfl) ⟨451224, by rfl⟩ : syracuseStep 1203265 = 902449) (by norm_num)
theorem B2710741 : Blo 948586 2710741 := bbase (se 7 (by rfl) ⟨31766, by rfl⟩ : syracuseStep 2710741 = 63533) (by norm_num)
theorem B1203437 : Blo 948586 1203437 := bbase (se 3 (by rfl) ⟨225644, by rfl⟩ : syracuseStep 1203437 = 451289) (by norm_num)
theorem B1203493 : Blo 948586 1203493 := bbase (se 4 (by rfl) ⟨112827, by rfl⟩ : syracuseStep 1203493 = 225655) (by norm_num)
theorem B2710901 : Blo 948586 2710901 := bbase (se 5 (by rfl) ⟨127073, by rfl⟩ : syracuseStep 2710901 = 254147) (by norm_num)
theorem B1203589 : Blo 948586 1203589 := bbase (se 4 (by rfl) ⟨112836, by rfl⟩ : syracuseStep 1203589 = 225673) (by norm_num)
theorem B2416013 : Blo 948586 2416013 := bbase (se 3 (by rfl) ⟨453002, by rfl⟩ : syracuseStep 2416013 = 906005) (by norm_num)
theorem B3202469 : Blo 948586 3202469 := bbase (se 4 (by rfl) ⟨300231, by rfl⟩ : syracuseStep 3202469 = 600463) (by norm_num)
theorem B1236397 : Blo 948586 1236397 := bbase (se 3 (by rfl) ⟨231824, by rfl⟩ : syracuseStep 1236397 = 463649) (by norm_num)
theorem B3431909 : Blo 948586 3431909 := bbase (se 4 (by rfl) ⟨321741, by rfl⟩ : syracuseStep 3431909 = 643483) (by norm_num)
theorem B1203761 : Blo 948586 1203761 := bbase (se 2 (by rfl) ⟨451410, by rfl⟩ : syracuseStep 1203761 = 902821) (by norm_num)
theorem B2711141 : Blo 948586 2711141 := bbase (se 4 (by rfl) ⟨254169, by rfl⟩ : syracuseStep 2711141 = 508339) (by norm_num)
theorem B1203817 : Blo 948586 1203817 := bbase (se 2 (by rfl) ⟨451431, by rfl⟩ : syracuseStep 1203817 = 902863) (by norm_num)
theorem B1072769 : Blo 948586 1072769 := bbase (se 2 (by rfl) ⟨402288, by rfl⟩ : syracuseStep 1072769 = 804577) (by norm_num)
theorem B1203913 : Blo 948586 1203913 := bbase (se 2 (by rfl) ⟨451467, by rfl⟩ : syracuseStep 1203913 = 902935) (by norm_num)
theorem B1236709 : Blo 948586 1236709 := bbase (se 4 (by rfl) ⟨115941, by rfl⟩ : syracuseStep 1236709 = 231883) (by norm_num)
theorem B1924885 : Blo 948586 1924885 := bbase (se 6 (by rfl) ⟨45114, by rfl⟩ : syracuseStep 1924885 = 90229) (by norm_num)
theorem B2711333 : Blo 948586 2711333 := bbase (se 4 (by rfl) ⟨254187, by rfl⟩ : syracuseStep 2711333 = 508375) (by norm_num)
theorem B2285381 : Blo 948586 2285381 := bbase (se 4 (by rfl) ⟨214254, by rfl⟩ : syracuseStep 2285381 = 428509) (by norm_num)
theorem B3202901 : Blo 948586 3202901 := bbase (se 9 (by rfl) ⟨9383, by rfl⟩ : syracuseStep 3202901 = 18767) (by norm_num)
theorem B1204085 : Blo 948586 1204085 := bbase (se 5 (by rfl) ⟨56441, by rfl⟩ : syracuseStep 1204085 = 112883) (by norm_num)
theorem B1204141 : Blo 948586 1204141 := bbase (se 3 (by rfl) ⟨225776, by rfl⟩ : syracuseStep 1204141 = 451553) (by norm_num)
theorem B4808645 : Blo 948586 4808645 := bbase (se 4 (by rfl) ⟨450810, by rfl⟩ : syracuseStep 4808645 = 901621) (by norm_num)
theorem B1204237 : Blo 948586 1204237 := bbase (se 3 (by rfl) ⟨225794, by rfl⟩ : syracuseStep 1204237 = 451589) (by norm_num)
theorem B4055093 : Blo 948586 4055093 := bbase (se 5 (by rfl) ⟨190082, by rfl⟩ : syracuseStep 4055093 = 380165) (by norm_num)
theorem B1204409 : Blo 948586 1204409 := bbase (se 2 (by rfl) ⟨451653, by rfl⟩ : syracuseStep 1204409 = 903307) (by norm_num)
theorem B1204465 : Blo 948586 1204465 := bbase (se 2 (by rfl) ⟨451674, by rfl⟩ : syracuseStep 1204465 = 903349) (by norm_num)
theorem B3203333 : Blo 948586 3203333 := bbase (se 4 (by rfl) ⟨300312, by rfl⟩ : syracuseStep 3203333 = 600625) (by norm_num)
theorem B1204561 : Blo 948586 1204561 := bbase (se 2 (by rfl) ⟨451710, by rfl⟩ : syracuseStep 1204561 = 903421) (by norm_num)
theorem B1204733 : Blo 948586 1204733 := bbase (se 3 (by rfl) ⟨225887, by rfl⟩ : syracuseStep 1204733 = 451775) (by norm_num)
theorem B1204789 : Blo 948586 1204789 := bbase (se 5 (by rfl) ⟨56474, by rfl⟩ : syracuseStep 1204789 = 112949) (by norm_num)
theorem B1204885 : Blo 948586 1204885 := bbase (se 6 (by rfl) ⟨28239, by rfl⟩ : syracuseStep 1204885 = 56479) (by norm_num)
theorem B3203765 : Blo 948586 3203765 := bbase (se 5 (by rfl) ⟨150176, by rfl⟩ : syracuseStep 3203765 = 300353) (by norm_num)
theorem B2712325 : Blo 948586 2712325 := bbase (se 4 (by rfl) ⟨254280, by rfl⟩ : syracuseStep 2712325 = 508561) (by norm_num)
theorem B1205057 : Blo 948586 1205057 := bbase (se 2 (by rfl) ⟨451896, by rfl⟩ : syracuseStep 1205057 = 903793) (by norm_num)
theorem B1205113 : Blo 948586 1205113 := bbase (se 2 (by rfl) ⟨451917, by rfl⟩ : syracuseStep 1205113 = 903835) (by norm_num)
theorem B1205209 : Blo 948586 1205209 := bbase (se 2 (by rfl) ⟨451953, by rfl⟩ : syracuseStep 1205209 = 903907) (by norm_num)
theorem B4056101 : Blo 948586 4056101 := bbase (se 4 (by rfl) ⟨380259, by rfl⟩ : syracuseStep 4056101 = 760519) (by norm_num)
theorem B3204197 : Blo 948586 3204197 := bbase (se 4 (by rfl) ⟨300393, by rfl⟩ : syracuseStep 3204197 = 600787) (by norm_num)
theorem B1205381 : Blo 948586 1205381 := bbase (se 4 (by rfl) ⟨113004, by rfl⟩ : syracuseStep 1205381 = 226009) (by norm_num)
theorem B1205437 : Blo 948586 1205437 := bbase (se 3 (by rfl) ⟨226019, by rfl⟩ : syracuseStep 1205437 = 452039) (by norm_num)
theorem B4809941 : Blo 948586 4809941 := bbase (se 7 (by rfl) ⟨56366, by rfl⟩ : syracuseStep 4809941 = 112733) (by norm_num)
theorem B2286805 : Blo 948586 2286805 := bbase (se 7 (by rfl) ⟨26798, by rfl⟩ : syracuseStep 2286805 = 53597) (by norm_num)
theorem B1205533 : Blo 948586 1205533 := bbase (se 3 (by rfl) ⟨226037, by rfl⟩ : syracuseStep 1205533 = 452075) (by norm_num)
theorem B976249 : Blo 948586 976249 := bbase (se 2 (by rfl) ⟨366093, by rfl⟩ : syracuseStep 976249 = 732187) (by norm_num)
theorem B1926605 : Blo 948586 1926605 := bbase (se 3 (by rfl) ⟨361238, by rfl⟩ : syracuseStep 1926605 = 722477) (by norm_num)
theorem B3204629 : Blo 948586 3204629 := bbase (se 6 (by rfl) ⟨75108, by rfl⟩ : syracuseStep 3204629 = 150217) (by norm_num)
theorem B3860021 : Blo 948586 3860021 := bbase (se 5 (by rfl) ⟨180938, by rfl⟩ : syracuseStep 3860021 = 361877) (by norm_num)
theorem B1140365 : Blo 948586 1140365 := bbase (se 3 (by rfl) ⟨213818, by rfl⟩ : syracuseStep 1140365 = 427637) (by norm_num)
theorem B9135989 : Blo 948586 9135989 := bbase (se 5 (by rfl) ⟨428249, by rfl⟩ : syracuseStep 9135989 = 856499) (by norm_num)
theorem B2287477 : Blo 948586 2287477 := bbase (se 5 (by rfl) ⟨107225, by rfl⟩ : syracuseStep 2287477 = 214451) (by norm_num)
theorem B3205061 : Blo 948586 3205061 := bbase (se 4 (by rfl) ⟨300474, by rfl⟩ : syracuseStep 3205061 = 600949) (by norm_num)
theorem B2287709 : Blo 948586 2287709 := bbase (se 3 (by rfl) ⟨428945, by rfl⟩ : syracuseStep 2287709 = 857891) (by norm_num)
theorem B5564533 : Blo 948586 5564533 := bbase (se 5 (by rfl) ⟨260837, by rfl⟩ : syracuseStep 5564533 = 521675) (by norm_num)
theorem B2287757 : Blo 948586 2287757 := bbase (se 3 (by rfl) ⟨428954, by rfl⟩ : syracuseStep 2287757 = 857909) (by norm_num)
theorem B1140961 : Blo 948586 1140961 := bbase (se 2 (by rfl) ⟨427860, by rfl⟩ : syracuseStep 1140961 = 855721) (by norm_num)
theorem B3041525 : Blo 948586 3041525 := bbase (se 5 (by rfl) ⟨142571, by rfl⟩ : syracuseStep 3041525 = 285143) (by norm_num)
theorem B1141057 : Blo 948586 1141057 := bbase (se 2 (by rfl) ⟨427896, by rfl⟩ : syracuseStep 1141057 = 855793) (by norm_num)
theorem B3205493 : Blo 948586 3205493 := bbase (se 5 (by rfl) ⟨150257, by rfl⟩ : syracuseStep 3205493 = 300515) (by norm_num)
theorem B4811237 : Blo 948586 4811237 := bbase (se 4 (by rfl) ⟨451053, by rfl⟩ : syracuseStep 4811237 = 902107) (by norm_num)
theorem B1927837 : Blo 948586 1927837 := bbase (se 3 (by rfl) ⟨361469, by rfl⟩ : syracuseStep 1927837 = 722939) (by norm_num)
theorem B2026205 : Blo 948586 2026205 := bbase (se 3 (by rfl) ⟨379913, by rfl⟩ : syracuseStep 2026205 = 759827) (by norm_num)
theorem B4057877 : Blo 948586 4057877 := bbase (se 6 (by rfl) ⟨95106, by rfl⟩ : syracuseStep 4057877 = 190213) (by norm_num)
theorem B3205925 : Blo 948586 3205925 := bbase (se 4 (by rfl) ⟨300555, by rfl⟩ : syracuseStep 3205925 = 601111) (by norm_num)
theorem B2026453 : Blo 948586 2026453 := bbase (se 7 (by rfl) ⟨23747, by rfl⟩ : syracuseStep 2026453 = 47495) (by norm_num)
theorem B1928357 : Blo 948586 1928357 := bbase (se 4 (by rfl) ⟨180783, by rfl⟩ : syracuseStep 1928357 = 361567) (by norm_num)
theorem B3206357 : Blo 948586 3206357 := bbase (se 7 (by rfl) ⟨37574, by rfl⟩ : syracuseStep 3206357 = 75149) (by norm_num)
theorem B1600789 : Blo 948586 1600789 := bbase (se 6 (by rfl) ⟨37518, by rfl⟩ : syracuseStep 1600789 = 75037) (by norm_num)
theorem B3042613 : Blo 948586 3042613 := bbase (se 5 (by rfl) ⟨142622, by rfl⟩ : syracuseStep 3042613 = 285245) (by norm_num)
theorem B1600877 : Blo 948586 1600877 := bbase (se 3 (by rfl) ⟨300164, by rfl⟩ : syracuseStep 1600877 = 600329) (by norm_num)
theorem B1142201 : Blo 948586 1142201 := bbase (se 2 (by rfl) ⟨428325, by rfl⟩ : syracuseStep 1142201 = 856651) (by norm_num)
theorem B2026957 : Blo 948586 2026957 := bbase (se 3 (by rfl) ⟨380054, by rfl⟩ : syracuseStep 2026957 = 760109) (by norm_num)
theorem B1601005 : Blo 948586 1601005 := bbase (se 3 (by rfl) ⟨300188, by rfl⟩ : syracuseStep 1601005 = 600377) (by norm_num)
theorem B1601093 : Blo 948586 1601093 := bbase (se 4 (by rfl) ⟨150102, by rfl⟩ : syracuseStep 1601093 = 300205) (by norm_num)
theorem B1830493 : Blo 948586 1830493 := bbase (se 3 (by rfl) ⟨343217, by rfl⟩ : syracuseStep 1830493 = 686435) (by norm_num)
theorem B3206789 : Blo 948586 3206789 := bbase (se 4 (by rfl) ⟨300636, by rfl⟩ : syracuseStep 3206789 = 601273) (by norm_num)
theorem B1601221 : Blo 948586 1601221 := bbase (se 4 (by rfl) ⟨150114, by rfl⟩ : syracuseStep 1601221 = 300229) (by norm_num)
theorem B4812533 : Blo 948586 4812533 := bbase (se 5 (by rfl) ⟨225587, by rfl⟩ : syracuseStep 4812533 = 451175) (by norm_num)
theorem B1142533 : Blo 948586 1142533 := bbase (se 4 (by rfl) ⟨107112, by rfl⟩ : syracuseStep 1142533 = 214225) (by norm_num)
theorem B1601309 : Blo 948586 1601309 := bbase (se 3 (by rfl) ⟨300245, by rfl⟩ : syracuseStep 1601309 = 600491) (by norm_num)
theorem B1601437 : Blo 948586 1601437 := bbase (se 3 (by rfl) ⟨300269, by rfl⟩ : syracuseStep 1601437 = 600539) (by norm_num)
theorem B1601525 : Blo 948586 1601525 := bbase (se 5 (by rfl) ⟨75071, by rfl⟩ : syracuseStep 1601525 = 150143) (by norm_num)
theorem B3207221 : Blo 948586 3207221 := bbase (se 5 (by rfl) ⟨150338, by rfl⟩ : syracuseStep 3207221 = 300677) (by norm_num)
theorem B7204949 : Blo 948586 7204949 := bbase (se 8 (by rfl) ⟨42216, by rfl⟩ : syracuseStep 7204949 = 84433) (by norm_num)
theorem B1601653 : Blo 948586 1601653 := bbase (se 5 (by rfl) ⟨75077, by rfl⟩ : syracuseStep 1601653 = 150155) (by norm_num)
theorem B3338437 : Blo 948586 3338437 := bbase (se 4 (by rfl) ⟨312978, by rfl⟩ : syracuseStep 3338437 = 625957) (by norm_num)
theorem B1601741 : Blo 948586 1601741 := bbase (se 3 (by rfl) ⟨300326, by rfl⟩ : syracuseStep 1601741 = 600653) (by norm_num)
theorem B2027845 : Blo 948586 2027845 := bbase (se 4 (by rfl) ⟨190110, by rfl⟩ : syracuseStep 2027845 = 380221) (by norm_num)
theorem B1601869 : Blo 948586 1601869 := bbase (se 3 (by rfl) ⟨300350, by rfl⟩ : syracuseStep 1601869 = 600701) (by norm_num)
theorem B1929557 : Blo 948586 1929557 := bbase (se 10 (by rfl) ⟨2826, by rfl⟩ : syracuseStep 1929557 = 5653) (by norm_num)
theorem B1601957 : Blo 948586 1601957 := bbase (se 4 (by rfl) ⟨150183, by rfl⟩ : syracuseStep 1601957 = 300367) (by norm_num)
theorem B1143229 : Blo 948586 1143229 := bbase (se 3 (by rfl) ⟨214355, by rfl⟩ : syracuseStep 1143229 = 428711) (by norm_num)
theorem B3043781 : Blo 948586 3043781 := bbase (se 4 (by rfl) ⟨285354, by rfl⟩ : syracuseStep 3043781 = 570709) (by norm_num)
theorem B3207653 : Blo 948586 3207653 := bbase (se 4 (by rfl) ⟨300717, by rfl⟩ : syracuseStep 3207653 = 601435) (by norm_num)
theorem B1143277 : Blo 948586 1143277 := bbase (se 3 (by rfl) ⟨214364, by rfl⟩ : syracuseStep 1143277 = 428729) (by norm_num)
theorem B1602085 : Blo 948586 1602085 := bbase (se 4 (by rfl) ⟨150195, by rfl⟩ : syracuseStep 1602085 = 300391) (by norm_num)
theorem B1602173 : Blo 948586 1602173 := bbase (se 3 (by rfl) ⟨300407, by rfl⟩ : syracuseStep 1602173 = 600815) (by norm_num)
theorem B1602301 : Blo 948586 1602301 := bbase (se 3 (by rfl) ⟨300431, by rfl⟩ : syracuseStep 1602301 = 600863) (by norm_num)
theorem B2028341 : Blo 948586 2028341 := bbase (se 5 (by rfl) ⟨95078, by rfl⟩ : syracuseStep 2028341 = 190157) (by norm_num)
theorem B5206837 : Blo 948586 5206837 := bbase (se 5 (by rfl) ⟨244070, by rfl⟩ : syracuseStep 5206837 = 488141) (by norm_num)
theorem B1602389 : Blo 948586 1602389 := bbase (se 9 (by rfl) ⟨4694, by rfl⟩ : syracuseStep 1602389 = 9389) (by norm_num)
theorem B5403509 : Blo 948586 5403509 := bbase (se 5 (by rfl) ⟨253289, by rfl⟩ : syracuseStep 5403509 = 506579) (by norm_num)
theorem B3208085 : Blo 948586 3208085 := bbase (se 6 (by rfl) ⟨75189, by rfl⟩ : syracuseStep 3208085 = 150379) (by norm_num)
theorem B1602517 : Blo 948586 1602517 := bbase (se 7 (by rfl) ⟨18779, by rfl⟩ : syracuseStep 1602517 = 37559) (by norm_num)
theorem B4813829 : Blo 948586 4813829 := bbase (se 4 (by rfl) ⟨451296, by rfl⟩ : syracuseStep 4813829 = 902593) (by norm_num)
theorem B1602605 : Blo 948586 1602605 := bbase (se 3 (by rfl) ⟨300488, by rfl⟩ : syracuseStep 1602605 = 600977) (by norm_num)
theorem B1602733 : Blo 948586 1602733 := bbase (se 3 (by rfl) ⟨300512, by rfl⟩ : syracuseStep 1602733 = 601025) (by norm_num)
theorem B1602821 : Blo 948586 1602821 := bbase (se 4 (by rfl) ⟨150264, by rfl⟩ : syracuseStep 1602821 = 300529) (by norm_num)
theorem B3601685 : Blo 948586 3601685 := bbase (se 6 (by rfl) ⟨84414, by rfl⟩ : syracuseStep 3601685 = 168829) (by norm_num)
theorem B3470629 : Blo 948586 3470629 := bbase (se 4 (by rfl) ⟨325371, by rfl⟩ : syracuseStep 3470629 = 650743) (by norm_num)
theorem B3208517 : Blo 948586 3208517 := bbase (se 4 (by rfl) ⟨300798, by rfl⟩ : syracuseStep 3208517 = 601597) (by norm_num)
theorem B1013077 : Blo 948586 1013077 := bbase (se 13 (by rfl) ⟨185, by rfl⟩ : syracuseStep 1013077 = 371) (by norm_num)
theorem B1602949 : Blo 948586 1602949 := bbase (se 4 (by rfl) ⟨150276, by rfl⟩ : syracuseStep 1602949 = 300553) (by norm_num)
theorem B1603037 : Blo 948586 1603037 := bbase (se 3 (by rfl) ⟨300569, by rfl⟩ : syracuseStep 1603037 = 601139) (by norm_num)
theorem B1144325 : Blo 948586 1144325 := bbase (se 4 (by rfl) ⟨107280, by rfl⟩ : syracuseStep 1144325 = 214561) (by norm_num)
theorem B1603165 : Blo 948586 1603165 := bbase (se 3 (by rfl) ⟨300593, by rfl⟩ : syracuseStep 1603165 = 601187) (by norm_num)
theorem B2029229 : Blo 948586 2029229 := bbase (se 3 (by rfl) ⟨380480, by rfl⟩ : syracuseStep 2029229 = 760961) (by norm_num)
theorem B1603253 : Blo 948586 1603253 := bbase (se 5 (by rfl) ⟨75152, by rfl⟩ : syracuseStep 1603253 = 150305) (by norm_num)
theorem B3208949 : Blo 948586 3208949 := bbase (se 5 (by rfl) ⟨150419, by rfl⟩ : syracuseStep 3208949 = 300839) (by norm_num)
theorem B1013521 : Blo 948586 1013521 := bbase (se 2 (by rfl) ⟨380070, by rfl⟩ : syracuseStep 1013521 = 760141) (by norm_num)
theorem B2029349 : Blo 948586 2029349 := bbase (se 4 (by rfl) ⟨190251, by rfl⟩ : syracuseStep 2029349 = 380503) (by norm_num)
theorem B1603381 : Blo 948586 1603381 := bbase (se 5 (by rfl) ⟨75158, by rfl⟩ : syracuseStep 1603381 = 150317) (by norm_num)
theorem B1013581 : Blo 948586 1013581 := bbase (se 3 (by rfl) ⟨190046, by rfl⟩ : syracuseStep 1013581 = 380093) (by norm_num)
theorem B1603469 : Blo 948586 1603469 := bbase (se 3 (by rfl) ⟨300650, by rfl⟩ : syracuseStep 1603469 = 601301) (by norm_num)
theorem B1603597 : Blo 948586 1603597 := bbase (se 3 (by rfl) ⟨300674, by rfl⟩ : syracuseStep 1603597 = 601349) (by norm_num)
theorem B1603685 : Blo 948586 1603685 := bbase (se 4 (by rfl) ⟨150345, by rfl⟩ : syracuseStep 1603685 = 300691) (by norm_num)
theorem B1013897 : Blo 948586 1013897 := bbase (se 2 (by rfl) ⟨380211, by rfl⟩ : syracuseStep 1013897 = 760423) (by norm_num)
theorem B3209381 : Blo 948586 3209381 := bbase (se 4 (by rfl) ⟨300879, by rfl⟩ : syracuseStep 3209381 = 601759) (by norm_num)
theorem B1603813 : Blo 948586 1603813 := bbase (se 4 (by rfl) ⟨150357, by rfl⟩ : syracuseStep 1603813 = 300715) (by norm_num)
theorem B3045637 : Blo 948586 3045637 := bbase (se 4 (by rfl) ⟨285528, by rfl⟩ : syracuseStep 3045637 = 571057) (by norm_num)
theorem B4815125 : Blo 948586 4815125 := bbase (se 6 (by rfl) ⟨112854, by rfl⟩ : syracuseStep 4815125 = 225709) (by norm_num)
theorem B1603901 : Blo 948586 1603901 := bbase (se 3 (by rfl) ⟨300731, by rfl⟩ : syracuseStep 1603901 = 601463) (by norm_num)
theorem B2029981 : Blo 948586 2029981 := bbase (se 3 (by rfl) ⟨380621, by rfl⟩ : syracuseStep 2029981 = 761243) (by norm_num)
theorem B1604029 : Blo 948586 1604029 := bbase (se 3 (by rfl) ⟨300755, by rfl⟩ : syracuseStep 1604029 = 601511) (by norm_num)
theorem B1604117 : Blo 948586 1604117 := bbase (se 6 (by rfl) ⟨37596, by rfl⟩ : syracuseStep 1604117 = 75193) (by norm_num)
theorem B1014341 : Blo 948586 1014341 := bbase (se 4 (by rfl) ⟨95094, by rfl⟩ : syracuseStep 1014341 = 190189) (by norm_num)
theorem B3209813 : Blo 948586 3209813 := bbase (se 8 (by rfl) ⟨18807, by rfl⟩ : syracuseStep 3209813 = 37615) (by norm_num)
theorem B1014401 : Blo 948586 1014401 := bbase (se 2 (by rfl) ⟨380400, by rfl⟩ : syracuseStep 1014401 = 760801) (by norm_num)
theorem B1604245 : Blo 948586 1604245 := bbase (se 6 (by rfl) ⟨37599, by rfl⟩ : syracuseStep 1604245 = 75199) (by norm_num)
theorem B1604333 : Blo 948586 1604333 := bbase (se 3 (by rfl) ⟨300812, by rfl⟩ : syracuseStep 1604333 = 601625) (by norm_num)
theorem B1800949 : Blo 948586 1800949 := bbase (se 5 (by rfl) ⟨84419, by rfl⟩ : syracuseStep 1800949 = 168839) (by norm_num)
theorem B1014529 : Blo 948586 1014529 := bbase (se 2 (by rfl) ⟨380448, by rfl⟩ : syracuseStep 1014529 = 760897) (by norm_num)
theorem B1604461 : Blo 948586 1604461 := bbase (se 3 (by rfl) ⟨300836, by rfl⟩ : syracuseStep 1604461 = 601673) (by norm_num)
theorem B1801109 : Blo 948586 1801109 := bbase (se 6 (by rfl) ⟨42213, by rfl⟩ : syracuseStep 1801109 = 84427) (by norm_num)
theorem B1604549 : Blo 948586 1604549 := bbase (se 4 (by rfl) ⟨150426, by rfl⟩ : syracuseStep 1604549 = 300853) (by norm_num)
theorem B4062149 : Blo 948586 4062149 := bbase (se 4 (by rfl) ⟨380826, by rfl⟩ : syracuseStep 4062149 = 761653) (by norm_num)
theorem B3210245 : Blo 948586 3210245 := bbase (se 4 (by rfl) ⟨300960, by rfl⟩ : syracuseStep 3210245 = 601921) (by norm_num)
theorem B5405717 : Blo 948586 5405717 := bbase (se 6 (by rfl) ⟨126696, by rfl⟩ : syracuseStep 5405717 = 253393) (by norm_num)
theorem B1801253 : Blo 948586 1801253 := bbase (se 4 (by rfl) ⟨168867, by rfl⟩ : syracuseStep 1801253 = 337735) (by norm_num)
theorem B1604677 : Blo 948586 1604677 := bbase (se 4 (by rfl) ⟨150438, by rfl⟩ : syracuseStep 1604677 = 300877) (by norm_num)
theorem B1604765 : Blo 948586 1604765 := bbase (se 3 (by rfl) ⟨300893, by rfl⟩ : syracuseStep 1604765 = 601787) (by norm_num)
theorem B1014973 : Blo 948586 1014973 := bbase (se 3 (by rfl) ⟨190307, by rfl⟩ : syracuseStep 1014973 = 380615) (by norm_num)
theorem B2030869 : Blo 948586 2030869 := bbase (se 6 (by rfl) ⟨47598, by rfl⟩ : syracuseStep 2030869 = 95197) (by norm_num)
theorem B1604893 : Blo 948586 1604893 := bbase (se 3 (by rfl) ⟨300917, by rfl⟩ : syracuseStep 1604893 = 601835) (by norm_num)
theorem B1015093 : Blo 948586 1015093 := bbase (se 5 (by rfl) ⟨47582, by rfl⟩ : syracuseStep 1015093 = 95165) (by norm_num)
theorem B1801541 : Blo 948586 1801541 := bbase (se 4 (by rfl) ⟨168894, by rfl⟩ : syracuseStep 1801541 = 337789) (by norm_num)
theorem B3603797 : Blo 948586 3603797 := bbase (se 11 (by rfl) ⟨2639, by rfl⟩ : syracuseStep 3603797 = 5279) (by norm_num)
theorem B1604981 : Blo 948586 1604981 := bbase (se 5 (by rfl) ⟨75233, by rfl⟩ : syracuseStep 1604981 = 150467) (by norm_num)
theorem B2030989 : Blo 948586 2030989 := bbase (se 3 (by rfl) ⟨380810, by rfl⟩ : syracuseStep 2030989 = 761621) (by norm_num)
theorem B3210677 : Blo 948586 3210677 := bbase (se 5 (by rfl) ⟨150500, by rfl⟩ : syracuseStep 3210677 = 301001) (by norm_num)
theorem B2194877 : Blo 948586 2194877 := bbase (se 3 (by rfl) ⟨411539, by rfl⟩ : syracuseStep 2194877 = 823079) (by norm_num)
theorem B1801693 : Blo 948586 1801693 := bbase (se 3 (by rfl) ⟨337817, by rfl⟩ : syracuseStep 1801693 = 675635) (by norm_num)
theorem B1605109 : Blo 948586 1605109 := bbase (se 5 (by rfl) ⟨75239, by rfl⟩ : syracuseStep 1605109 = 150479) (by norm_num)
theorem B4816421 : Blo 948586 4816421 := bbase (se 4 (by rfl) ⟨451539, by rfl⟩ : syracuseStep 4816421 = 903079) (by norm_num)
theorem B1015345 : Blo 948586 1015345 := bbase (se 2 (by rfl) ⟨380754, by rfl⟩ : syracuseStep 1015345 = 761509) (by norm_num)
theorem B1015349 : Blo 948586 1015349 := bbase (se 5 (by rfl) ⟨47594, by rfl⟩ : syracuseStep 1015349 = 95189) (by norm_num)
theorem B1605197 : Blo 948586 1605197 := bbase (se 3 (by rfl) ⟨300974, by rfl⟩ : syracuseStep 1605197 = 601949) (by norm_num)
theorem B3046997 : Blo 948586 3046997 := bbase (se 8 (by rfl) ⟨17853, by rfl⟩ : syracuseStep 3046997 = 35707) (by norm_num)
theorem B3604085 : Blo 948586 3604085 := bbase (se 5 (by rfl) ⟨168941, by rfl⟩ : syracuseStep 3604085 = 337883) (by norm_num)
theorem B2031245 : Blo 948586 2031245 := bbase (se 3 (by rfl) ⟨380858, by rfl⟩ : syracuseStep 2031245 = 761717) (by norm_num)
theorem B1605325 : Blo 948586 1605325 := bbase (se 3 (by rfl) ⟨300998, by rfl⟩ : syracuseStep 1605325 = 601997) (by norm_num)
theorem B1801997 : Blo 948586 1801997 := bbase (se 3 (by rfl) ⟨337874, by rfl⟩ : syracuseStep 1801997 = 675749) (by norm_num)
theorem B1605413 : Blo 948586 1605413 := bbase (se 4 (by rfl) ⟨150507, by rfl⟩ : syracuseStep 1605413 = 301015) (by norm_num)
theorem B3211109 : Blo 948586 3211109 := bbase (se 4 (by rfl) ⟨301041, by rfl⟩ : syracuseStep 3211109 = 602083) (by norm_num)
theorem B1605541 : Blo 948586 1605541 := bbase (se 4 (by rfl) ⟨150519, by rfl⟩ : syracuseStep 1605541 = 301039) (by norm_num)
theorem B1605629 : Blo 948586 1605629 := bbase (se 3 (by rfl) ⟨301055, by rfl⟩ : syracuseStep 1605629 = 602111) (by norm_num)
theorem B950275 : Blo 948586 950275 := bstep (se 1 (by rfl) ⟨712706, by rfl⟩ : syracuseStep 950275 = 1425413) B1425413
theorem B1605649 : Blo 948586 1605649 := bstep (se 2 (by rfl) ⟨602118, by rfl⟩ : syracuseStep 1605649 = 1204237) B1204237
theorem B950291 : Blo 948586 950291 := bstep (se 1 (by rfl) ⟨712718, by rfl⟩ : syracuseStep 950291 = 1425437) B1425437
theorem B950307 : Blo 948586 950307 := bstep (se 1 (by rfl) ⟨712730, by rfl⟩ : syracuseStep 950307 = 1425461) B1425461
theorem B950323 : Blo 948586 950323 := bstep (se 1 (by rfl) ⟨712742, by rfl⟩ : syracuseStep 950323 = 1425485) B1425485
theorem B1605683 : Blo 948586 1605683 := bstep (se 1 (by rfl) ⟨1204262, by rfl⟩ : syracuseStep 1605683 = 2408525) B2408525
theorem B28508213 : Blo 948586 28508213 := bstep (se 5 (by rfl) ⟨1336322, by rfl⟩ : syracuseStep 28508213 = 2672645) B2672645
theorem B950339 : Blo 948586 950339 := bstep (se 1 (by rfl) ⟨712754, by rfl⟩ : syracuseStep 950339 = 1425509) B1425509
theorem B950355 : Blo 948586 950355 := bstep (se 1 (by rfl) ⟨712766, by rfl⟩ : syracuseStep 950355 = 1425533) B1425533
theorem B950371 : Blo 948586 950371 := bstep (se 1 (by rfl) ⟨712778, by rfl⟩ : syracuseStep 950371 = 1425557) B1425557
theorem B950387 : Blo 948586 950387 := bstep (se 1 (by rfl) ⟨712790, by rfl⟩ : syracuseStep 950387 = 1425581) B1425581
theorem B950403 : Blo 948586 950403 := bstep (se 1 (by rfl) ⟨712802, by rfl⟩ : syracuseStep 950403 = 1425605) B1425605
theorem B1015939 : Blo 948586 1015939 := bstep (se 1 (by rfl) ⟨761954, by rfl⟩ : syracuseStep 1015939 = 1523909) B1523909
theorem B950419 : Blo 948586 950419 := bstep (se 1 (by rfl) ⟨712814, by rfl⟩ : syracuseStep 950419 = 1425629) B1425629
theorem B950435 : Blo 948586 950435 := bstep (se 1 (by rfl) ⟨712826, by rfl⟩ : syracuseStep 950435 = 1425653) B1425653
theorem B950451 : Blo 948586 950451 := bstep (se 1 (by rfl) ⟨712838, by rfl⟩ : syracuseStep 950451 = 1425677) B1425677
theorem B1605811 : Blo 948586 1605811 := bstep (se 1 (by rfl) ⟨1204358, by rfl⟩ : syracuseStep 1605811 = 2408717) B2408717
theorem B950467 : Blo 948586 950467 := bstep (se 1 (by rfl) ⟨712850, by rfl⟩ : syracuseStep 950467 = 1425701) B1425701
theorem B950483 : Blo 948586 950483 := bstep (se 1 (by rfl) ⟨712862, by rfl⟩ : syracuseStep 950483 = 1425725) B1425725
theorem B950499 : Blo 948586 950499 := bstep (se 1 (by rfl) ⟨712874, by rfl⟩ : syracuseStep 950499 = 1425749) B1425749
theorem B950515 : Blo 948586 950515 := bstep (se 1 (by rfl) ⟨712886, by rfl⟩ : syracuseStep 950515 = 1425773) B1425773
theorem B950531 : Blo 948586 950531 := bstep (se 1 (by rfl) ⟨712898, by rfl⟩ : syracuseStep 950531 = 1425797) B1425797
theorem B1802513 : Blo 948586 1802513 := bstep (se 2 (by rfl) ⟨675942, by rfl⟩ : syracuseStep 1802513 = 1351885) B1351885
theorem B950547 : Blo 948586 950547 := bstep (se 1 (by rfl) ⟨712910, by rfl⟩ : syracuseStep 950547 = 1425821) B1425821
theorem B950563 : Blo 948586 950563 := bstep (se 1 (by rfl) ⟨712922, by rfl⟩ : syracuseStep 950563 = 1425845) B1425845
theorem B950579 : Blo 948586 950579 := bstep (se 1 (by rfl) ⟨712934, by rfl⟩ : syracuseStep 950579 = 1425869) B1425869
theorem B1605953 : Blo 948586 1605953 := bstep (se 2 (by rfl) ⟨602232, by rfl⟩ : syracuseStep 1605953 = 1204465) B1204465
theorem B950595 : Blo 948586 950595 := bstep (se 1 (by rfl) ⟨712946, by rfl⟩ : syracuseStep 950595 = 1425893) B1425893
theorem B950611 : Blo 948586 950611 := bstep (se 1 (by rfl) ⟨712958, by rfl⟩ : syracuseStep 950611 = 1425917) B1425917
theorem B950627 : Blo 948586 950627 := bstep (se 1 (by rfl) ⟨712970, by rfl⟩ : syracuseStep 950627 = 1425941) B1425941
theorem B950643 : Blo 948586 950643 := bstep (se 1 (by rfl) ⟨712982, by rfl⟩ : syracuseStep 950643 = 1425965) B1425965
theorem B950659 : Blo 948586 950659 := bstep (se 1 (by rfl) ⟨712994, by rfl⟩ : syracuseStep 950659 = 1425989) B1425989
theorem B950675 : Blo 948586 950675 := bstep (se 1 (by rfl) ⟨713006, by rfl⟩ : syracuseStep 950675 = 1426013) B1426013
theorem B950691 : Blo 948586 950691 := bstep (se 1 (by rfl) ⟨713018, by rfl⟩ : syracuseStep 950691 = 1426037) B1426037
theorem B950707 : Blo 948586 950707 := bstep (se 1 (by rfl) ⟨713030, by rfl⟩ : syracuseStep 950707 = 1426061) B1426061
theorem B1606081 : Blo 948586 1606081 := bstep (se 2 (by rfl) ⟨602280, by rfl⟩ : syracuseStep 1606081 = 1204561) B1204561
theorem B950723 : Blo 948586 950723 := bstep (se 1 (by rfl) ⟨713042, by rfl⟩ : syracuseStep 950723 = 1426085) B1426085
theorem B950739 : Blo 948586 950739 := bstep (se 1 (by rfl) ⟨713054, by rfl⟩ : syracuseStep 950739 = 1426109) B1426109
theorem B950755 : Blo 948586 950755 := bstep (se 1 (by rfl) ⟨713066, by rfl⟩ : syracuseStep 950755 = 1426133) B1426133
theorem B1606115 : Blo 948586 1606115 := bstep (se 1 (by rfl) ⟨1204586, by rfl⟩ : syracuseStep 1606115 = 2409173) B2409173
theorem B3211757 : Blo 948586 3211757 := bstep (se 3 (by rfl) ⟨602204, by rfl⟩ : syracuseStep 3211757 = 1204409) B1204409
theorem B4817393 : Blo 948586 4817393 := bstep (se 2 (by rfl) ⟨1806522, by rfl⟩ : syracuseStep 4817393 = 3613045) B3613045
theorem B950771 : Blo 948586 950771 := bstep (se 1 (by rfl) ⟨713078, by rfl⟩ : syracuseStep 950771 = 1426157) B1426157
theorem B950787 : Blo 948586 950787 := bstep (se 1 (by rfl) ⟨713090, by rfl⟩ : syracuseStep 950787 = 1426181) B1426181
theorem B950803 : Blo 948586 950803 := bstep (se 1 (by rfl) ⟨713102, by rfl⟩ : syracuseStep 950803 = 1426205) B1426205
theorem B950819 : Blo 948586 950819 := bstep (se 1 (by rfl) ⟨713114, by rfl⟩ : syracuseStep 950819 = 1426229) B1426229
theorem B3211811 : Blo 948586 3211811 := bstep (se 1 (by rfl) ⟨2408858, by rfl⟩ : syracuseStep 3211811 = 4817717) B4817717
theorem B950835 : Blo 948586 950835 := bstep (se 1 (by rfl) ⟨713126, by rfl⟩ : syracuseStep 950835 = 1426253) B1426253
theorem B950851 : Blo 948586 950851 := bstep (se 1 (by rfl) ⟨713138, by rfl⟩ : syracuseStep 950851 = 1426277) B1426277
theorem B950867 : Blo 948586 950867 := bstep (se 1 (by rfl) ⟨713150, by rfl⟩ : syracuseStep 950867 = 1426301) B1426301
theorem B950883 : Blo 948586 950883 := bstep (se 1 (by rfl) ⟨713162, by rfl⟩ : syracuseStep 950883 = 1426325) B1426325
theorem B1606243 : Blo 948586 1606243 := bstep (se 1 (by rfl) ⟨1204682, by rfl⟩ : syracuseStep 1606243 = 2409365) B2409365
theorem B950899 : Blo 948586 950899 := bstep (se 1 (by rfl) ⟨713174, by rfl⟩ : syracuseStep 950899 = 1426349) B1426349
theorem B950915 : Blo 948586 950915 := bstep (se 1 (by rfl) ⟨713186, by rfl⟩ : syracuseStep 950915 = 1426373) B1426373
theorem B950931 : Blo 948586 950931 := bstep (se 1 (by rfl) ⟨713198, by rfl⟩ : syracuseStep 950931 = 1426397) B1426397
theorem B950947 : Blo 948586 950947 := bstep (se 1 (by rfl) ⟨713210, by rfl⟩ : syracuseStep 950947 = 1426421) B1426421
theorem B950963 : Blo 948586 950963 := bstep (se 1 (by rfl) ⟨713222, by rfl⟩ : syracuseStep 950963 = 1426445) B1426445
theorem B950979 : Blo 948586 950979 := bstep (se 1 (by rfl) ⟨713234, by rfl⟩ : syracuseStep 950979 = 1426469) B1426469
theorem B950995 : Blo 948586 950995 := bstep (se 1 (by rfl) ⟨713246, by rfl⟩ : syracuseStep 950995 = 1426493) B1426493
theorem B951011 : Blo 948586 951011 := bstep (se 1 (by rfl) ⟨713258, by rfl⟩ : syracuseStep 951011 = 1426517) B1426517
theorem B1606385 : Blo 948586 1606385 := bstep (se 2 (by rfl) ⟨602394, by rfl⟩ : syracuseStep 1606385 = 1204789) B1204789
theorem B951027 : Blo 948586 951027 := bstep (se 1 (by rfl) ⟨713270, by rfl⟩ : syracuseStep 951027 = 1426541) B1426541
theorem B951043 : Blo 948586 951043 := bstep (se 1 (by rfl) ⟨713282, by rfl⟩ : syracuseStep 951043 = 1426565) B1426565
theorem B951059 : Blo 948586 951059 := bstep (se 1 (by rfl) ⟨713294, by rfl⟩ : syracuseStep 951059 = 1426589) B1426589
theorem B951075 : Blo 948586 951075 := bstep (se 1 (by rfl) ⟨713306, by rfl⟩ : syracuseStep 951075 = 1426613) B1426613
theorem B3212081 : Blo 948586 3212081 := bstep (se 2 (by rfl) ⟨1204530, by rfl⟩ : syracuseStep 3212081 = 2409061) B2409061
theorem B951091 : Blo 948586 951091 := bstep (se 1 (by rfl) ⟨713318, by rfl⟩ : syracuseStep 951091 = 1426637) B1426637
theorem B951107 : Blo 948586 951107 := bstep (se 1 (by rfl) ⟨713330, by rfl⟩ : syracuseStep 951107 = 1426661) B1426661
theorem B951123 : Blo 948586 951123 := bstep (se 1 (by rfl) ⟨713342, by rfl⟩ : syracuseStep 951123 = 1426685) B1426685
theorem B951139 : Blo 948586 951139 := bstep (se 1 (by rfl) ⟨713354, by rfl⟩ : syracuseStep 951139 = 1426709) B1426709
theorem B5145443 : Blo 948586 5145443 := bstep (se 1 (by rfl) ⟨3859082, by rfl⟩ : syracuseStep 5145443 = 7718165) B7718165
theorem B1606513 : Blo 948586 1606513 := bstep (se 2 (by rfl) ⟨602442, by rfl⟩ : syracuseStep 1606513 = 1204885) B1204885
theorem B951155 : Blo 948586 951155 := bstep (se 1 (by rfl) ⟨713366, by rfl⟩ : syracuseStep 951155 = 1426733) B1426733
theorem B951171 : Blo 948586 951171 := bstep (se 1 (by rfl) ⟨713378, by rfl⟩ : syracuseStep 951171 = 1426757) B1426757
theorem B951187 : Blo 948586 951187 := bstep (se 1 (by rfl) ⟨713390, by rfl⟩ : syracuseStep 951187 = 1426781) B1426781
theorem B1606547 : Blo 948586 1606547 := bstep (se 1 (by rfl) ⟨1204910, by rfl⟩ : syracuseStep 1606547 = 2409821) B2409821
theorem B951203 : Blo 948586 951203 := bstep (se 1 (by rfl) ⟨713402, by rfl⟩ : syracuseStep 951203 = 1426805) B1426805
theorem B951219 : Blo 948586 951219 := bstep (se 1 (by rfl) ⟨713414, by rfl⟩ : syracuseStep 951219 = 1426829) B1426829
theorem B951235 : Blo 948586 951235 := bstep (se 1 (by rfl) ⟨713426, by rfl⟩ : syracuseStep 951235 = 1426853) B1426853
theorem B951251 : Blo 948586 951251 := bstep (se 1 (by rfl) ⟨713438, by rfl⟩ : syracuseStep 951251 = 1426877) B1426877
theorem B1803235 : Blo 948586 1803235 := bstep (se 1 (by rfl) ⟨1352426, by rfl⟩ : syracuseStep 1803235 = 2704853) B2704853
theorem B951267 : Blo 948586 951267 := bstep (se 1 (by rfl) ⟨713450, by rfl⟩ : syracuseStep 951267 = 1426901) B1426901
theorem B951283 : Blo 948586 951283 := bstep (se 1 (by rfl) ⟨713462, by rfl⟩ : syracuseStep 951283 = 1426925) B1426925
theorem B951299 : Blo 948586 951299 := bstep (se 1 (by rfl) ⟨713474, by rfl⟩ : syracuseStep 951299 = 1426949) B1426949
theorem B951315 : Blo 948586 951315 := bstep (se 1 (by rfl) ⟨713486, by rfl⟩ : syracuseStep 951315 = 1426973) B1426973
theorem B1606675 : Blo 948586 1606675 := bstep (se 1 (by rfl) ⟨1205006, by rfl⟩ : syracuseStep 1606675 = 2410013) B2410013
theorem B951331 : Blo 948586 951331 := bstep (se 1 (by rfl) ⟨713498, by rfl⟩ : syracuseStep 951331 = 1426997) B1426997
theorem B951347 : Blo 948586 951347 := bstep (se 1 (by rfl) ⟨713510, by rfl⟩ : syracuseStep 951347 = 1427021) B1427021
theorem B951363 : Blo 948586 951363 := bstep (se 1 (by rfl) ⟨713522, by rfl⟩ : syracuseStep 951363 = 1427045) B1427045
theorem B951379 : Blo 948586 951379 := bstep (se 1 (by rfl) ⟨713534, by rfl⟩ : syracuseStep 951379 = 1427069) B1427069
theorem B951395 : Blo 948586 951395 := bstep (se 1 (by rfl) ⟨713546, by rfl⟩ : syracuseStep 951395 = 1427093) B1427093
theorem B951411 : Blo 948586 951411 := bstep (se 1 (by rfl) ⟨713558, by rfl⟩ : syracuseStep 951411 = 1427117) B1427117
theorem B951427 : Blo 948586 951427 := bstep (se 1 (by rfl) ⟨713570, by rfl⟩ : syracuseStep 951427 = 1427141) B1427141
theorem B951443 : Blo 948586 951443 := bstep (se 1 (by rfl) ⟨713582, by rfl⟩ : syracuseStep 951443 = 1427165) B1427165
theorem B1606817 : Blo 948586 1606817 := bstep (se 2 (by rfl) ⟨602556, by rfl⟩ : syracuseStep 1606817 = 1205113) B1205113
theorem B951459 : Blo 948586 951459 := bstep (se 1 (by rfl) ⟨713594, by rfl⟩ : syracuseStep 951459 = 1427189) B1427189
theorem B951475 : Blo 948586 951475 := bstep (se 1 (by rfl) ⟨713606, by rfl⟩ : syracuseStep 951475 = 1427213) B1427213
theorem B951491 : Blo 948586 951491 := bstep (se 1 (by rfl) ⟨713618, by rfl⟩ : syracuseStep 951491 = 1427237) B1427237
theorem B951507 : Blo 948586 951507 := bstep (se 1 (by rfl) ⟨713630, by rfl⟩ : syracuseStep 951507 = 1427261) B1427261
theorem B951523 : Blo 948586 951523 := bstep (se 1 (by rfl) ⟨713642, by rfl⟩ : syracuseStep 951523 = 1427285) B1427285
theorem B951539 : Blo 948586 951539 := bstep (se 1 (by rfl) ⟨713654, by rfl⟩ : syracuseStep 951539 = 1427309) B1427309
theorem B951555 : Blo 948586 951555 := bstep (se 1 (by rfl) ⟨713666, by rfl⟩ : syracuseStep 951555 = 1427333) B1427333
theorem B4064525 : Blo 948586 4064525 := bstep (se 3 (by rfl) ⟨762098, by rfl⟩ : syracuseStep 4064525 = 1524197) B1524197
theorem B951571 : Blo 948586 951571 := bstep (se 1 (by rfl) ⟨713678, by rfl⟩ : syracuseStep 951571 = 1427357) B1427357
theorem B1606945 : Blo 948586 1606945 := bstep (se 2 (by rfl) ⟨602604, by rfl⟩ : syracuseStep 1606945 = 1205209) B1205209
theorem B951587 : Blo 948586 951587 := bstep (se 1 (by rfl) ⟨713690, by rfl⟩ : syracuseStep 951587 = 1427381) B1427381
theorem B951603 : Blo 948586 951603 := bstep (se 1 (by rfl) ⟨713702, by rfl⟩ : syracuseStep 951603 = 1427405) B1427405
theorem B951619 : Blo 948586 951619 := bstep (se 1 (by rfl) ⟨713714, by rfl⟩ : syracuseStep 951619 = 1427429) B1427429
theorem B1606979 : Blo 948586 1606979 := bstep (se 1 (by rfl) ⟨1205234, by rfl⟩ : syracuseStep 1606979 = 2410469) B2410469
theorem B3212621 : Blo 948586 3212621 := bstep (se 3 (by rfl) ⟨602366, by rfl⟩ : syracuseStep 3212621 = 1204733) B1204733
theorem B951635 : Blo 948586 951635 := bstep (se 1 (by rfl) ⟨713726, by rfl⟩ : syracuseStep 951635 = 1427453) B1427453
theorem B951651 : Blo 948586 951651 := bstep (se 1 (by rfl) ⟨713738, by rfl⟩ : syracuseStep 951651 = 1427477) B1427477
theorem B951667 : Blo 948586 951667 := bstep (se 1 (by rfl) ⟨713750, by rfl⟩ : syracuseStep 951667 = 1427501) B1427501
theorem B1017203 : Blo 948586 1017203 := bstep (se 1 (by rfl) ⟨762902, by rfl⟩ : syracuseStep 1017203 = 1525805) B1525805
theorem B951683 : Blo 948586 951683 := bstep (se 1 (by rfl) ⟨713762, by rfl⟩ : syracuseStep 951683 = 1427525) B1427525
theorem B3212675 : Blo 948586 3212675 := bstep (se 1 (by rfl) ⟨2409506, by rfl⟩ : syracuseStep 3212675 = 4819013) B4819013
theorem B951699 : Blo 948586 951699 := bstep (se 1 (by rfl) ⟨713774, by rfl⟩ : syracuseStep 951699 = 1427549) B1427549
theorem B1803683 : Blo 948586 1803683 := bstep (se 1 (by rfl) ⟨1352762, by rfl⟩ : syracuseStep 1803683 = 2705525) B2705525
theorem B951715 : Blo 948586 951715 := bstep (se 1 (by rfl) ⟨713786, by rfl⟩ : syracuseStep 951715 = 1427573) B1427573
theorem B951731 : Blo 948586 951731 := bstep (se 1 (by rfl) ⟨713798, by rfl⟩ : syracuseStep 951731 = 1427597) B1427597
theorem B951747 : Blo 948586 951747 := bstep (se 1 (by rfl) ⟨713810, by rfl⟩ : syracuseStep 951747 = 1427621) B1427621
theorem B1607107 : Blo 948586 1607107 := bstep (se 1 (by rfl) ⟨1205330, by rfl⟩ : syracuseStep 1607107 = 2410661) B2410661
theorem B951763 : Blo 948586 951763 := bstep (se 1 (by rfl) ⟨713822, by rfl⟩ : syracuseStep 951763 = 1427645) B1427645
theorem B951779 : Blo 948586 951779 := bstep (se 1 (by rfl) ⟨713834, by rfl⟩ : syracuseStep 951779 = 1427669) B1427669
theorem B8127985 : Blo 948586 8127985 := bstep (se 2 (by rfl) ⟨3047994, by rfl⟩ : syracuseStep 8127985 = 6095989) B6095989
theorem B951795 : Blo 948586 951795 := bstep (se 1 (by rfl) ⟨713846, by rfl⟩ : syracuseStep 951795 = 1427693) B1427693
theorem B951811 : Blo 948586 951811 := bstep (se 1 (by rfl) ⟨713858, by rfl⟩ : syracuseStep 951811 = 1427717) B1427717
theorem B3606029 : Blo 948586 3606029 := bstep (se 3 (by rfl) ⟨676130, by rfl⟩ : syracuseStep 3606029 = 1352261) B1352261
theorem B951827 : Blo 948586 951827 := bstep (se 1 (by rfl) ⟨713870, by rfl⟩ : syracuseStep 951827 = 1427741) B1427741
theorem B951843 : Blo 948586 951843 := bstep (se 1 (by rfl) ⟨713882, by rfl⟩ : syracuseStep 951843 = 1427765) B1427765
theorem B951859 : Blo 948586 951859 := bstep (se 1 (by rfl) ⟨713894, by rfl⟩ : syracuseStep 951859 = 1427789) B1427789
theorem B951875 : Blo 948586 951875 := bstep (se 1 (by rfl) ⟨713906, by rfl⟩ : syracuseStep 951875 = 1427813) B1427813
theorem B1607249 : Blo 948586 1607249 := bstep (se 2 (by rfl) ⟨602718, by rfl⟩ : syracuseStep 1607249 = 1205437) B1205437
theorem B951891 : Blo 948586 951891 := bstep (se 1 (by rfl) ⟨713918, by rfl⟩ : syracuseStep 951891 = 1427837) B1427837
theorem B951907 : Blo 948586 951907 := bstep (se 1 (by rfl) ⟨713930, by rfl⟩ : syracuseStep 951907 = 1427861) B1427861
theorem B3049073 : Blo 948586 3049073 := bstep (se 2 (by rfl) ⟨1143402, by rfl⟩ : syracuseStep 3049073 = 2286805) B2286805
theorem B951923 : Blo 948586 951923 := bstep (se 1 (by rfl) ⟨713942, by rfl⟩ : syracuseStep 951923 = 1427885) B1427885
theorem B951939 : Blo 948586 951939 := bstep (se 1 (by rfl) ⟨713954, by rfl⟩ : syracuseStep 951939 = 1427909) B1427909
theorem B3212945 : Blo 948586 3212945 := bstep (se 2 (by rfl) ⟨1204854, by rfl⟩ : syracuseStep 3212945 = 2409709) B2409709
theorem B951955 : Blo 948586 951955 := bstep (se 1 (by rfl) ⟨713966, by rfl⟩ : syracuseStep 951955 = 1427933) B1427933
theorem B3049123 : Blo 948586 3049123 := bstep (se 1 (by rfl) ⟨2286842, by rfl⟩ : syracuseStep 3049123 = 4573685) B4573685
theorem B951971 : Blo 948586 951971 := bstep (se 1 (by rfl) ⟨713978, by rfl⟩ : syracuseStep 951971 = 1427957) B1427957
theorem B951987 : Blo 948586 951987 := bstep (se 1 (by rfl) ⟨713990, by rfl⟩ : syracuseStep 951987 = 1427981) B1427981
theorem B1803971 : Blo 948586 1803971 := bstep (se 1 (by rfl) ⟨1352978, by rfl⟩ : syracuseStep 1803971 = 2705957) B2705957
theorem B952003 : Blo 948586 952003 := bstep (se 1 (by rfl) ⟨714002, by rfl⟩ : syracuseStep 952003 = 1428005) B1428005
theorem B1607377 : Blo 948586 1607377 := bstep (se 2 (by rfl) ⟨602766, by rfl⟩ : syracuseStep 1607377 = 1205533) B1205533
theorem B952019 : Blo 948586 952019 := bstep (se 1 (by rfl) ⟨714014, by rfl⟩ : syracuseStep 952019 = 1428029) B1428029
theorem B952035 : Blo 948586 952035 := bstep (se 1 (by rfl) ⟨714026, by rfl⟩ : syracuseStep 952035 = 1428053) B1428053
theorem B952051 : Blo 948586 952051 := bstep (se 1 (by rfl) ⟨714038, by rfl⟩ : syracuseStep 952051 = 1428077) B1428077
theorem B1607411 : Blo 948586 1607411 := bstep (se 1 (by rfl) ⟨1205558, by rfl⟩ : syracuseStep 1607411 = 2411117) B2411117
theorem B952067 : Blo 948586 952067 := bstep (se 1 (by rfl) ⟨714050, by rfl⟩ : syracuseStep 952067 = 1428101) B1428101
theorem B952083 : Blo 948586 952083 := bstep (se 1 (by rfl) ⟨714062, by rfl⟩ : syracuseStep 952083 = 1428125) B1428125
theorem B952099 : Blo 948586 952099 := bstep (se 1 (by rfl) ⟨714074, by rfl⟩ : syracuseStep 952099 = 1428149) B1428149
theorem B952115 : Blo 948586 952115 := bstep (se 1 (by rfl) ⟨714086, by rfl⟩ : syracuseStep 952115 = 1428173) B1428173
theorem B952131 : Blo 948586 952131 := bstep (se 1 (by rfl) ⟨714098, by rfl⟩ : syracuseStep 952131 = 1428197) B1428197
theorem B952147 : Blo 948586 952147 := bstep (se 1 (by rfl) ⟨714110, by rfl⟩ : syracuseStep 952147 = 1428221) B1428221
theorem B952163 : Blo 948586 952163 := bstep (se 1 (by rfl) ⟨714122, by rfl⟩ : syracuseStep 952163 = 1428245) B1428245
theorem B952179 : Blo 948586 952179 := bstep (se 1 (by rfl) ⟨714134, by rfl⟩ : syracuseStep 952179 = 1428269) B1428269
theorem B952195 : Blo 948586 952195 := bstep (se 1 (by rfl) ⟨714146, by rfl⟩ : syracuseStep 952195 = 1428293) B1428293
theorem B952211 : Blo 948586 952211 := bstep (se 1 (by rfl) ⟨714158, by rfl⟩ : syracuseStep 952211 = 1428317) B1428317
theorem B4818851 : Blo 948586 4818851 := bstep (se 1 (by rfl) ⟨3614138, by rfl⟩ : syracuseStep 4818851 = 7228277) B7228277
theorem B952227 : Blo 948586 952227 := bstep (se 1 (by rfl) ⟨714170, by rfl⟩ : syracuseStep 952227 = 1428341) B1428341
theorem B2164657 : Blo 948586 2164657 := bstep (se 2 (by rfl) ⟨811746, by rfl⟩ : syracuseStep 2164657 = 1623493) B1623493
theorem B952243 : Blo 948586 952243 := bstep (se 1 (by rfl) ⟨714182, by rfl⟩ : syracuseStep 952243 = 1428365) B1428365
theorem B2033603 : Blo 948586 2033603 := bstep (se 1 (by rfl) ⟨1525202, by rfl⟩ : syracuseStep 2033603 = 3050405) B3050405
theorem B952259 : Blo 948586 952259 := bstep (se 1 (by rfl) ⟨714194, by rfl⟩ : syracuseStep 952259 = 1428389) B1428389
theorem B952275 : Blo 948586 952275 := bstep (se 1 (by rfl) ⟨714206, by rfl⟩ : syracuseStep 952275 = 1428413) B1428413
theorem B952291 : Blo 948586 952291 := bstep (se 1 (by rfl) ⟨714218, by rfl⟩ : syracuseStep 952291 = 1428437) B1428437
theorem B952307 : Blo 948586 952307 := bstep (se 1 (by rfl) ⟨714230, by rfl⟩ : syracuseStep 952307 = 1428461) B1428461
theorem B952323 : Blo 948586 952323 := bstep (se 1 (by rfl) ⟨714242, by rfl⟩ : syracuseStep 952323 = 1428485) B1428485
theorem B952339 : Blo 948586 952339 := bstep (se 1 (by rfl) ⟨714254, by rfl⟩ : syracuseStep 952339 = 1428509) B1428509
theorem B952355 : Blo 948586 952355 := bstep (se 1 (by rfl) ⟨714266, by rfl⟩ : syracuseStep 952355 = 1428533) B1428533
theorem B952371 : Blo 948586 952371 := bstep (se 1 (by rfl) ⟨714278, by rfl⟩ : syracuseStep 952371 = 1428557) B1428557
theorem B23169077 : Blo 948586 23169077 := bstep (se 5 (by rfl) ⟨1086050, by rfl⟩ : syracuseStep 23169077 = 2172101) B2172101
theorem B952387 : Blo 948586 952387 := bstep (se 1 (by rfl) ⟨714290, by rfl⟩ : syracuseStep 952387 = 1428581) B1428581
theorem B952403 : Blo 948586 952403 := bstep (se 1 (by rfl) ⟨714302, by rfl⟩ : syracuseStep 952403 = 1428605) B1428605
theorem B952419 : Blo 948586 952419 := bstep (se 1 (by rfl) ⟨714314, by rfl⟩ : syracuseStep 952419 = 1428629) B1428629
theorem B952435 : Blo 948586 952435 := bstep (se 1 (by rfl) ⟨714326, by rfl⟩ : syracuseStep 952435 = 1428653) B1428653
theorem B952451 : Blo 948586 952451 := bstep (se 1 (by rfl) ⟨714338, by rfl⟩ : syracuseStep 952451 = 1428677) B1428677
theorem B952467 : Blo 948586 952467 := bstep (se 1 (by rfl) ⟨714350, by rfl⟩ : syracuseStep 952467 = 1428701) B1428701
theorem B952483 : Blo 948586 952483 := bstep (se 1 (by rfl) ⟨714362, by rfl⟩ : syracuseStep 952483 = 1428725) B1428725
theorem B3213485 : Blo 948586 3213485 := bstep (se 3 (by rfl) ⟨602528, by rfl⟩ : syracuseStep 3213485 = 1205057) B1205057
theorem B952499 : Blo 948586 952499 := bstep (se 1 (by rfl) ⟨714374, by rfl⟩ : syracuseStep 952499 = 1428749) B1428749
theorem B952515 : Blo 948586 952515 := bstep (se 1 (by rfl) ⟨714386, by rfl⟩ : syracuseStep 952515 = 1428773) B1428773
theorem B12159173 : Blo 948586 12159173 := bstep (se 4 (by rfl) ⟨1139922, by rfl⟩ : syracuseStep 12159173 = 2279845) B2279845
theorem B952531 : Blo 948586 952531 := bstep (se 1 (by rfl) ⟨714398, by rfl⟩ : syracuseStep 952531 = 1428797) B1428797
theorem B3213539 : Blo 948586 3213539 := bstep (se 1 (by rfl) ⟨2410154, by rfl⟩ : syracuseStep 3213539 = 4820309) B4820309
theorem B952547 : Blo 948586 952547 := bstep (se 1 (by rfl) ⟨714410, by rfl⟩ : syracuseStep 952547 = 1428821) B1428821
theorem B952563 : Blo 948586 952563 := bstep (se 1 (by rfl) ⟨714422, by rfl⟩ : syracuseStep 952563 = 1428845) B1428845
theorem B952579 : Blo 948586 952579 := bstep (se 1 (by rfl) ⟨714434, by rfl⟩ : syracuseStep 952579 = 1428869) B1428869
theorem B2885905 : Blo 948586 2885905 := bstep (se 2 (by rfl) ⟨1082214, by rfl⟩ : syracuseStep 2885905 = 2164429) B2164429
theorem B2034065 : Blo 948586 2034065 := bstep (se 2 (by rfl) ⟨762774, by rfl⟩ : syracuseStep 2034065 = 1525549) B1525549
theorem B1444321 : Blo 948586 1444321 := bstep (se 2 (by rfl) ⟨541620, by rfl⟩ : syracuseStep 1444321 = 1083241) B1083241
theorem B3049969 : Blo 948586 3049969 := bstep (se 2 (by rfl) ⟨1143738, by rfl⟩ : syracuseStep 3049969 = 2287477) B2287477
theorem B3213809 : Blo 948586 3213809 := bstep (se 2 (by rfl) ⟨1205178, by rfl⟩ : syracuseStep 3213809 = 2410357) B2410357
theorem B1542673 : Blo 948586 1542673 := bstep (se 2 (by rfl) ⟨578502, by rfl⟩ : syracuseStep 1542673 = 1157005) B1157005
theorem B6097477 : Blo 948586 6097477 := bstep (se 4 (by rfl) ⟨571638, by rfl⟩ : syracuseStep 6097477 = 1143277) B1143277
theorem B1804913 : Blo 948586 1804913 := bstep (se 2 (by rfl) ⟨676842, by rfl⟩ : syracuseStep 1804913 = 1353685) B1353685
theorem B4819661 : Blo 948586 4819661 := bstep (se 3 (by rfl) ⟨903686, by rfl⟩ : syracuseStep 4819661 = 1807373) B1807373
theorem B9276229 : Blo 948586 9276229 := bstep (se 4 (by rfl) ⟨869646, by rfl⟩ : syracuseStep 9276229 = 1739293) B1739293
theorem B3214349 : Blo 948586 3214349 := bstep (se 3 (by rfl) ⟨602690, by rfl⟩ : syracuseStep 3214349 = 1205381) B1205381
theorem B3214403 : Blo 948586 3214403 := bstep (se 1 (by rfl) ⟨2410802, by rfl⟩ : syracuseStep 3214403 = 4821605) B4821605
theorem B7703693 : Blo 948586 7703693 := bstep (se 3 (by rfl) ⟨1444442, by rfl⟩ : syracuseStep 7703693 = 2888885) B2888885
theorem B3214673 : Blo 948586 3214673 := bstep (se 2 (by rfl) ⟨1205502, by rfl⟩ : syracuseStep 3214673 = 2411005) B2411005
theorem B1805809 : Blo 948586 1805809 := bstep (se 2 (by rfl) ⟨677178, by rfl⟩ : syracuseStep 1805809 = 1354357) B1354357
theorem B1805969 : Blo 948586 1805969 := bstep (se 2 (by rfl) ⟨677238, by rfl⟩ : syracuseStep 1805969 = 1354477) B1354477
theorem B1445537 : Blo 948586 1445537 := bstep (se 2 (by rfl) ⟨542076, by rfl⟩ : syracuseStep 1445537 = 1084153) B1084153
theorem B11702069 : Blo 948586 11702069 := bstep (se 5 (by rfl) ⟨548534, by rfl⟩ : syracuseStep 11702069 = 1097069) B1097069
theorem B18485105 : Blo 948586 18485105 := bstep (se 2 (by rfl) ⟨6931914, by rfl⟩ : syracuseStep 18485105 = 13863829) B13863829
theorem B22548365 : Blo 948586 22548365 := bstep (se 3 (by rfl) ⟨4227818, by rfl⟩ : syracuseStep 22548365 = 8455637) B8455637
theorem B3051533 : Blo 948586 3051533 := bstep (se 3 (by rfl) ⟨572162, by rfl⟩ : syracuseStep 3051533 = 1144325) B1144325
theorem B1806371 : Blo 948586 1806371 := bstep (se 1 (by rfl) ⟨1354778, by rfl⟩ : syracuseStep 1806371 = 2709557) B2709557
theorem B11571299 : Blo 948586 11571299 := bstep (se 1 (by rfl) ⟨8678474, by rfl⟩ : syracuseStep 11571299 = 17356949) B17356949
theorem B10293389 : Blo 948586 10293389 := bstep (se 3 (by rfl) ⟨1930010, by rfl⟩ : syracuseStep 10293389 = 3860021) B3860021
theorem B2134385 : Blo 948586 2134385 := bstep (se 2 (by rfl) ⟨800394, by rfl⟩ : syracuseStep 2134385 = 1600789) B1600789
theorem B3608945 : Blo 948586 3608945 := bstep (se 2 (by rfl) ⟨1353354, by rfl⟩ : syracuseStep 3608945 = 2706709) B2706709
theorem B2134403 : Blo 948586 2134403 := bstep (se 1 (by rfl) ⟨1600802, by rfl⟩ : syracuseStep 2134403 = 3201605) B3201605
theorem B1216963 : Blo 948586 1216963 := bstep (se 1 (by rfl) ⟨912722, by rfl⟩ : syracuseStep 1216963 = 1825445) B1825445
theorem B2167249 : Blo 948586 2167249 := bstep (se 2 (by rfl) ⟨812718, by rfl⟩ : syracuseStep 2167249 = 1625437) B1625437
theorem B3248657 : Blo 948586 3248657 := bstep (se 2 (by rfl) ⟨1218246, by rfl⟩ : syracuseStep 3248657 = 2436493) B2436493
theorem B12325445 : Blo 948586 12325445 := bstep (se 4 (by rfl) ⟨1155510, by rfl⟩ : syracuseStep 12325445 = 2311021) B2311021
theorem B1282673 : Blo 948586 1282673 := bstep (se 2 (by rfl) ⟨481002, by rfl⟩ : syracuseStep 1282673 = 962005) B962005
theorem B6853261 : Blo 948586 6853261 := bstep (se 3 (by rfl) ⟨1284986, by rfl⟩ : syracuseStep 6853261 = 2569973) B2569973
theorem B2134673 : Blo 948586 2134673 := bstep (se 2 (by rfl) ⟨800502, by rfl⟩ : syracuseStep 2134673 = 1601005) B1601005
theorem B2134691 : Blo 948586 2134691 := bstep (se 1 (by rfl) ⟨1601018, by rfl⟩ : syracuseStep 2134691 = 3202037) B3202037
theorem B2167523 : Blo 948586 2167523 := bstep (se 1 (by rfl) ⟨1625642, by rfl⟩ : syracuseStep 2167523 = 3251285) B3251285
theorem B1807267 : Blo 948586 1807267 := bstep (se 1 (by rfl) ⟨1355450, by rfl⟩ : syracuseStep 1807267 = 2710901) B2710901
theorem B2134961 : Blo 948586 2134961 := bstep (se 2 (by rfl) ⟨800610, by rfl⟩ : syracuseStep 2134961 = 1601221) B1601221
theorem B1610675 : Blo 948586 1610675 := bstep (se 1 (by rfl) ⟨1208006, by rfl⟩ : syracuseStep 1610675 = 2416013) B2416013
theorem B2134979 : Blo 948586 2134979 := bstep (se 1 (by rfl) ⟨1601234, by rfl⟩ : syracuseStep 2134979 = 3202469) B3202469
theorem B1446913 : Blo 948586 1446913 := bstep (se 2 (by rfl) ⟨542592, by rfl⟩ : syracuseStep 1446913 = 1085185) B1085185
theorem B4559885 : Blo 948586 4559885 := bstep (se 3 (by rfl) ⟨854978, by rfl⟩ : syracuseStep 4559885 = 1709957) B1709957
theorem B1283105 : Blo 948586 1283105 := bstep (se 2 (by rfl) ⟨481164, by rfl⟩ : syracuseStep 1283105 = 962329) B962329
theorem B1807427 : Blo 948586 1807427 := bstep (se 1 (by rfl) ⟨1355570, by rfl⟩ : syracuseStep 1807427 = 2711141) B2711141
theorem B4560077 : Blo 948586 4560077 := bstep (se 3 (by rfl) ⟨855014, by rfl⟩ : syracuseStep 4560077 = 1710029) B1710029
theorem B2135249 : Blo 948586 2135249 := bstep (se 2 (by rfl) ⟨800718, by rfl⟩ : syracuseStep 2135249 = 1601437) B1601437
theorem B2135267 : Blo 948586 2135267 := bstep (se 1 (by rfl) ⟨1601450, by rfl⟩ : syracuseStep 2135267 = 3202901) B3202901
theorem B4560305 : Blo 948586 4560305 := bstep (se 2 (by rfl) ⟨1710114, by rfl⟩ : syracuseStep 4560305 = 3420229) B3420229
theorem B2135537 : Blo 948586 2135537 := bstep (se 2 (by rfl) ⟨800826, by rfl⟩ : syracuseStep 2135537 = 1601653) B1601653
theorem B2135555 : Blo 948586 2135555 := bstep (se 1 (by rfl) ⟨1601666, by rfl⟩ : syracuseStep 2135555 = 3203333) B3203333
theorem B4068899 : Blo 948586 4068899 := bstep (se 1 (by rfl) ⟨3051674, by rfl⟩ : syracuseStep 4068899 = 6103349) B6103349
theorem B4560461 : Blo 948586 4560461 := bstep (se 3 (by rfl) ⟨855086, by rfl⟩ : syracuseStep 4560461 = 1710173) B1710173
theorem B2135825 : Blo 948586 2135825 := bstep (se 2 (by rfl) ⟨800934, by rfl⟩ : syracuseStep 2135825 = 1601869) B1601869
theorem B2135843 : Blo 948586 2135843 := bstep (se 1 (by rfl) ⟨1601882, by rfl⟩ : syracuseStep 2135843 = 3203765) B3203765
theorem B3610403 : Blo 948586 3610403 := bstep (se 1 (by rfl) ⟨2707802, by rfl⟩ : syracuseStep 3610403 = 5415605) B5415605
theorem B3479395 : Blo 948586 3479395 := bstep (se 1 (by rfl) ⟨2609546, by rfl⟩ : syracuseStep 3479395 = 5219093) B5219093
theorem B4396963 : Blo 948586 4396963 := bstep (se 1 (by rfl) ⟨3297722, by rfl⟩ : syracuseStep 4396963 = 6595445) B6595445
theorem B2136113 : Blo 948586 2136113 := bstep (se 2 (by rfl) ⟨801042, by rfl⟩ : syracuseStep 2136113 = 1602085) B1602085
theorem B2136131 : Blo 948586 2136131 := bstep (se 1 (by rfl) ⟨1602098, by rfl⟩ : syracuseStep 2136131 = 3204197) B3204197
theorem B2889859 : Blo 948586 2889859 := bstep (se 1 (by rfl) ⟨2167394, by rfl⟩ : syracuseStep 2889859 = 4334789) B4334789
theorem B6166691 : Blo 948586 6166691 := bstep (se 1 (by rfl) ⟨4625018, by rfl⟩ : syracuseStep 6166691 = 9250037) B9250037
theorem B5413189 : Blo 948586 5413189 := bstep (se 4 (by rfl) ⟨507486, by rfl⟩ : syracuseStep 5413189 = 1014973) B1014973
theorem B2136401 : Blo 948586 2136401 := bstep (se 2 (by rfl) ⟨801150, by rfl⟩ : syracuseStep 2136401 = 1602301) B1602301
theorem B2136419 : Blo 948586 2136419 := bstep (se 1 (by rfl) ⟨1602314, by rfl⟩ : syracuseStep 2136419 = 3204629) B3204629
theorem B4331939 : Blo 948586 4331939 := bstep (se 1 (by rfl) ⟨3248954, by rfl⟩ : syracuseStep 4331939 = 6497909) B6497909
theorem B21142037 : Blo 948586 21142037 := bstep (se 6 (by rfl) ⟨495516, by rfl⟩ : syracuseStep 21142037 = 991033) B991033
theorem B2136689 : Blo 948586 2136689 := bstep (se 2 (by rfl) ⟨801258, by rfl⟩ : syracuseStep 2136689 = 1602517) B1602517
theorem B1645171 : Blo 948586 1645171 := bstep (se 1 (by rfl) ⟨1233878, by rfl⟩ : syracuseStep 1645171 = 2467757) B2467757
theorem B2136707 : Blo 948586 2136707 := bstep (se 1 (by rfl) ⟨1602530, by rfl⟩ : syracuseStep 2136707 = 3205061) B3205061
theorem B8133317 : Blo 948586 8133317 := bstep (se 4 (by rfl) ⟨762498, by rfl⟩ : syracuseStep 8133317 = 1524997) B1524997
theorem B3611405 : Blo 948586 3611405 := bstep (se 3 (by rfl) ⟨677138, by rfl⟩ : syracuseStep 3611405 = 1354277) B1354277
theorem B2136977 : Blo 948586 2136977 := bstep (se 2 (by rfl) ⟨801366, by rfl⟩ : syracuseStep 2136977 = 1602733) B1602733
theorem B2136995 : Blo 948586 2136995 := bstep (se 1 (by rfl) ⟨1602746, by rfl⟩ : syracuseStep 2136995 = 3205493) B3205493
theorem B1711153 : Blo 948586 1711153 := bstep (se 2 (by rfl) ⟨641682, by rfl⟩ : syracuseStep 1711153 = 1283365) B1283365
theorem B4627505 : Blo 948586 4627505 := bstep (se 2 (by rfl) ⟨1735314, by rfl⟩ : syracuseStep 4627505 = 3470629) B3470629
theorem B1350769 : Blo 948586 1350769 := bstep (se 2 (by rfl) ⟨506538, by rfl⟩ : syracuseStep 1350769 = 1013077) B1013077
theorem B43981937 : Blo 948586 43981937 := bstep (se 2 (by rfl) ⟨16493226, by rfl⟩ : syracuseStep 43981937 = 32986453) B32986453
theorem B1350803 : Blo 948586 1350803 := bstep (se 1 (by rfl) ⟨1013102, by rfl⟩ : syracuseStep 1350803 = 2026205) B2026205
theorem B2137265 : Blo 948586 2137265 := bstep (se 2 (by rfl) ⟨801474, by rfl⟩ : syracuseStep 2137265 = 1602949) B1602949
theorem B2137283 : Blo 948586 2137283 := bstep (se 1 (by rfl) ⟨1602962, by rfl⟩ : syracuseStep 2137283 = 3205925) B3205925
theorem B6495557 : Blo 948586 6495557 := bstep (se 4 (by rfl) ⟨608958, by rfl⟩ : syracuseStep 6495557 = 1217917) B1217917
theorem B6102449 : Blo 948586 6102449 := bstep (se 2 (by rfl) ⟨2288418, by rfl⟩ : syracuseStep 6102449 = 4576837) B4576837
theorem B1285571 : Blo 948586 1285571 := bstep (se 1 (by rfl) ⟨964178, by rfl⟩ : syracuseStep 1285571 = 1928357) B1928357
theorem B2137553 : Blo 948586 2137553 := bstep (se 2 (by rfl) ⟨801582, by rfl⟩ : syracuseStep 2137553 = 1603165) B1603165
theorem B2137571 : Blo 948586 2137571 := bstep (se 1 (by rfl) ⟨1603178, by rfl⟩ : syracuseStep 2137571 = 3206357) B3206357
theorem B1351361 : Blo 948586 1351361 := bstep (se 2 (by rfl) ⟨506760, by rfl⟩ : syracuseStep 1351361 = 1013521) B1013521
theorem B1285841 : Blo 948586 1285841 := bstep (se 2 (by rfl) ⟨482190, by rfl⟩ : syracuseStep 1285841 = 964381) B964381
theorem B2137841 : Blo 948586 2137841 := bstep (se 2 (by rfl) ⟨801690, by rfl⟩ : syracuseStep 2137841 = 1603381) B1603381
theorem B2137859 : Blo 948586 2137859 := bstep (se 1 (by rfl) ⟨1603394, by rfl⟩ : syracuseStep 2137859 = 3206789) B3206789
theorem B1351441 : Blo 948586 1351441 := bstep (se 2 (by rfl) ⟨506790, by rfl⟩ : syracuseStep 1351441 = 1013581) B1013581
theorem B11542499 : Blo 948586 11542499 := bstep (se 1 (by rfl) ⟨8656874, by rfl⟩ : syracuseStep 11542499 = 17313749) B17313749
theorem B2138129 : Blo 948586 2138129 := bstep (se 2 (by rfl) ⟨801798, by rfl⟩ : syracuseStep 2138129 = 1603597) B1603597
theorem B2138147 : Blo 948586 2138147 := bstep (se 1 (by rfl) ⟨1603610, by rfl⟩ : syracuseStep 2138147 = 3207221) B3207221
theorem B65740913 : Blo 948586 65740913 := bstep (se 2 (by rfl) ⟨24652842, by rfl⟩ : syracuseStep 65740913 = 49305685) B49305685
theorem B1286371 : Blo 948586 1286371 := bstep (se 1 (by rfl) ⟨964778, by rfl⟩ : syracuseStep 1286371 = 1929557) B1929557
theorem B5415173 : Blo 948586 5415173 := bstep (se 4 (by rfl) ⟨507672, by rfl⟩ : syracuseStep 5415173 = 1015345) B1015345
theorem B2138417 : Blo 948586 2138417 := bstep (se 2 (by rfl) ⟨801906, by rfl⟩ : syracuseStep 2138417 = 1603813) B1603813
theorem B2138435 : Blo 948586 2138435 := bstep (se 1 (by rfl) ⟨1603826, by rfl⟩ : syracuseStep 2138435 = 3207653) B3207653
theorem B1352227 : Blo 948586 1352227 := bstep (se 1 (by rfl) ⟨1014170, by rfl⟩ : syracuseStep 1352227 = 2028341) B2028341
theorem B2138705 : Blo 948586 2138705 := bstep (se 2 (by rfl) ⟨802014, by rfl⟩ : syracuseStep 2138705 = 1604029) B1604029
theorem B2138723 : Blo 948586 2138723 := bstep (se 1 (by rfl) ⟨1604042, by rfl⟩ : syracuseStep 2138723 = 3208085) B3208085
theorem B3613517 : Blo 948586 3613517 := bstep (se 3 (by rfl) ⟨677534, by rfl⟩ : syracuseStep 3613517 = 1355069) B1355069
theorem B2401123 : Blo 948586 2401123 := bstep (se 1 (by rfl) ⟨1800842, by rfl⟩ : syracuseStep 2401123 = 3601685) B3601685
theorem B2138993 : Blo 948586 2138993 := bstep (se 2 (by rfl) ⟨802122, by rfl⟩ : syracuseStep 2138993 = 1604245) B1604245
theorem B2139011 : Blo 948586 2139011 := bstep (se 1 (by rfl) ⟨1604258, by rfl⟩ : syracuseStep 2139011 = 3208517) B3208517
theorem B1319825 : Blo 948586 1319825 := bstep (se 2 (by rfl) ⟨494934, by rfl⟩ : syracuseStep 1319825 = 989869) B989869
theorem B2401265 : Blo 948586 2401265 := bstep (se 2 (by rfl) ⟨900474, by rfl⟩ : syracuseStep 2401265 = 1800949) B1800949
theorem B1352705 : Blo 948586 1352705 := bstep (se 2 (by rfl) ⟨507264, by rfl⟩ : syracuseStep 1352705 = 1014529) B1014529
theorem B1352819 : Blo 948586 1352819 := bstep (se 1 (by rfl) ⟨1014614, by rfl⟩ : syracuseStep 1352819 = 2029229) B2029229
theorem B2139281 : Blo 948586 2139281 := bstep (se 2 (by rfl) ⟨802230, by rfl⟩ : syracuseStep 2139281 = 1604461) B1604461
theorem B2139299 : Blo 948586 2139299 := bstep (se 1 (by rfl) ⟨1604474, by rfl⟩ : syracuseStep 2139299 = 3208949) B3208949
theorem B1352899 : Blo 948586 1352899 := bstep (se 1 (by rfl) ⟨1014674, by rfl⟩ : syracuseStep 1352899 = 2029349) B2029349
theorem B2139569 : Blo 948586 2139569 := bstep (se 2 (by rfl) ⟨802338, by rfl⟩ : syracuseStep 2139569 = 1604677) B1604677
theorem B2139587 : Blo 948586 2139587 := bstep (se 1 (by rfl) ⟨1604690, by rfl⟩ : syracuseStep 2139587 = 3209381) B3209381
theorem B3614321 : Blo 948586 3614321 := bstep (se 2 (by rfl) ⟨1355370, by rfl⟩ : syracuseStep 3614321 = 2710741) B2710741
theorem B2860717 : Blo 948586 2860717 := bstep (se 3 (by rfl) ⟨536384, by rfl⟩ : syracuseStep 2860717 = 1072769) B1072769
theorem B2139857 : Blo 948586 2139857 := bstep (se 2 (by rfl) ⟨802446, by rfl⟩ : syracuseStep 2139857 = 1604893) B1604893
theorem B2139875 : Blo 948586 2139875 := bstep (se 1 (by rfl) ⟨1604906, by rfl⟩ : syracuseStep 2139875 = 3209813) B3209813
theorem B1353457 : Blo 948586 1353457 := bstep (se 2 (by rfl) ⟨507546, by rfl⟩ : syracuseStep 1353457 = 1015093) B1015093
theorem B7219043 : Blo 948586 7219043 := bstep (se 1 (by rfl) ⟨5414282, by rfl⟩ : syracuseStep 7219043 = 10828565) B10828565
theorem B1648529 : Blo 948586 1648529 := bstep (se 2 (by rfl) ⟨618198, by rfl⟩ : syracuseStep 1648529 = 1236397) B1236397
theorem B2402257 : Blo 948586 2402257 := bstep (se 2 (by rfl) ⟨900846, by rfl⟩ : syracuseStep 2402257 = 1801693) B1801693
theorem B2926573 : Blo 948586 2926573 := bstep (se 3 (by rfl) ⟨548732, by rfl⟩ : syracuseStep 2926573 = 1097465) B1097465
theorem B2140145 : Blo 948586 2140145 := bstep (se 2 (by rfl) ⟨802554, by rfl⟩ : syracuseStep 2140145 = 1605109) B1605109
theorem B2140163 : Blo 948586 2140163 := bstep (se 1 (by rfl) ⟨1605122, by rfl⟩ : syracuseStep 2140163 = 3210245) B3210245
theorem B1648691 : Blo 948586 1648691 := bstep (se 1 (by rfl) ⟨1236518, by rfl⟩ : syracuseStep 1648691 = 2473037) B2473037
theorem B5777477 : Blo 948586 5777477 := bstep (se 4 (by rfl) ⟨541638, by rfl⟩ : syracuseStep 5777477 = 1083277) B1083277
theorem B2402531 : Blo 948586 2402531 := bstep (se 1 (by rfl) ⟨1801898, by rfl⟩ : syracuseStep 2402531 = 3603797) B3603797
theorem B3614989 : Blo 948586 3614989 := bstep (se 3 (by rfl) ⟨677810, by rfl⟩ : syracuseStep 3614989 = 1355621) B1355621
theorem B2140433 : Blo 948586 2140433 := bstep (se 2 (by rfl) ⟨802662, by rfl⟩ : syracuseStep 2140433 = 1605325) B1605325
theorem B2140451 : Blo 948586 2140451 := bstep (se 1 (by rfl) ⟨1605338, by rfl⟩ : syracuseStep 2140451 = 3210677) B3210677
theorem B1648945 : Blo 948586 1648945 := bstep (se 2 (by rfl) ⟨618354, by rfl⟩ : syracuseStep 1648945 = 1236709) B1236709
theorem B2566513 : Blo 948586 2566513 := bstep (se 2 (by rfl) ⟨962442, by rfl⟩ : syracuseStep 2566513 = 1924885) B1924885
theorem B2402723 : Blo 948586 2402723 := bstep (se 1 (by rfl) ⟨1802042, by rfl⟩ : syracuseStep 2402723 = 3604085) B3604085
theorem B1354163 : Blo 948586 1354163 := bstep (se 1 (by rfl) ⟨1015622, by rfl⟩ : syracuseStep 1354163 = 2031245) B2031245
theorem B2140721 : Blo 948586 2140721 := bstep (se 2 (by rfl) ⟨802770, by rfl⟩ : syracuseStep 2140721 = 1605541) B1605541
theorem B2140739 : Blo 948586 2140739 := bstep (se 1 (by rfl) ⟨1605554, by rfl⟩ : syracuseStep 2140739 = 3211109) B3211109
theorem B19507853 : Blo 948586 19507853 := bstep (se 3 (by rfl) ⟨3657722, by rfl⟩ : syracuseStep 19507853 = 7315445) B7315445
theorem B21146309 : Blo 948586 21146309 := bstep (se 4 (by rfl) ⟨1982466, by rfl⟩ : syracuseStep 21146309 = 3964933) B3964933
theorem B2141009 : Blo 948586 2141009 := bstep (se 2 (by rfl) ⟨802878, by rfl⟩ : syracuseStep 2141009 = 1605757) B1605757
theorem B2141027 : Blo 948586 2141027 := bstep (se 1 (by rfl) ⟨1605770, by rfl⟩ : syracuseStep 2141027 = 3211541) B3211541
theorem B3615779 : Blo 948586 3615779 := bstep (se 1 (by rfl) ⟨2711834, by rfl⟩ : syracuseStep 3615779 = 5423669) B5423669
theorem B1354801 : Blo 948586 1354801 := bstep (se 2 (by rfl) ⟨508050, by rfl⟩ : syracuseStep 1354801 = 1016101) B1016101
theorem B2141297 : Blo 948586 2141297 := bstep (se 2 (by rfl) ⟨802986, by rfl⟩ : syracuseStep 2141297 = 1605973) B1605973
theorem B2141315 : Blo 948586 2141315 := bstep (se 1 (by rfl) ⟨1605986, by rfl⟩ : syracuseStep 2141315 = 3211973) B3211973
theorem B1354915 : Blo 948586 1354915 := bstep (se 1 (by rfl) ⟨1016186, by rfl⟩ : syracuseStep 1354915 = 2032373) B2032373
theorem B1158419 : Blo 948586 1158419 := bstep (se 1 (by rfl) ⟨868814, by rfl⟩ : syracuseStep 1158419 = 1737629) B1737629
theorem B2403665 : Blo 948586 2403665 := bstep (se 2 (by rfl) ⟨901374, by rfl⟩ : syracuseStep 2403665 = 1802749) B1802749
theorem B2403715 : Blo 948586 2403715 := bstep (se 1 (by rfl) ⟨1802786, by rfl⟩ : syracuseStep 2403715 = 3605573) B3605573
theorem B2141585 : Blo 948586 2141585 := bstep (se 2 (by rfl) ⟨803094, by rfl⟩ : syracuseStep 2141585 = 1606189) B1606189
theorem B2141603 : Blo 948586 2141603 := bstep (se 1 (by rfl) ⟨1606202, by rfl⟩ : syracuseStep 2141603 = 3212405) B3212405
theorem B2403857 : Blo 948586 2403857 := bstep (se 2 (by rfl) ⟨901446, by rfl⟩ : syracuseStep 2403857 = 1802893) B1802893
theorem B2141873 : Blo 948586 2141873 := bstep (se 2 (by rfl) ⟨803202, by rfl⟩ : syracuseStep 2141873 = 1606405) B1606405
theorem B3616433 : Blo 948586 3616433 := bstep (se 2 (by rfl) ⟨1356162, by rfl⟩ : syracuseStep 3616433 = 2712325) B2712325
theorem B2141891 : Blo 948586 2141891 := bstep (se 1 (by rfl) ⟨1606418, by rfl⟩ : syracuseStep 2141891 = 3212837) B3212837
theorem B2600867 : Blo 948586 2600867 := bstep (se 1 (by rfl) ⟨1950650, by rfl⟩ : syracuseStep 2600867 = 3901301) B3901301
theorem B2142161 : Blo 948586 2142161 := bstep (se 2 (by rfl) ⟨803310, by rfl⟩ : syracuseStep 2142161 = 1606621) B1606621
theorem B2142179 : Blo 948586 2142179 := bstep (se 1 (by rfl) ⟨1606634, by rfl⟩ : syracuseStep 2142179 = 3213269) B3213269
theorem B5419021 : Blo 948586 5419021 := bstep (se 3 (by rfl) ⟨1016066, by rfl⟩ : syracuseStep 5419021 = 2032133) B2032133
theorem B5779619 : Blo 948586 5779619 := bstep (se 1 (by rfl) ⟨4334714, by rfl⟩ : syracuseStep 5779619 = 8669429) B8669429
theorem B2142449 : Blo 948586 2142449 := bstep (se 2 (by rfl) ⟨803418, by rfl⟩ : syracuseStep 2142449 = 1606837) B1606837
theorem B1519859 : Blo 948586 1519859 := bstep (se 1 (by rfl) ⟨1139894, by rfl⟩ : syracuseStep 1519859 = 2279789) B2279789
theorem B2142467 : Blo 948586 2142467 := bstep (se 1 (by rfl) ⟨1606850, by rfl⟩ : syracuseStep 2142467 = 3213701) B3213701
theorem B1356259 : Blo 948586 1356259 := bstep (se 1 (by rfl) ⟨1017194, by rfl⟩ : syracuseStep 1356259 = 2034389) B2034389
theorem B2404849 : Blo 948586 2404849 := bstep (se 2 (by rfl) ⟨901818, by rfl⟩ : syracuseStep 2404849 = 1803637) B1803637
theorem B2142737 : Blo 948586 2142737 := bstep (se 2 (by rfl) ⟨803526, by rfl⟩ : syracuseStep 2142737 = 1607053) B1607053
theorem B2142755 : Blo 948586 2142755 := bstep (se 1 (by rfl) ⟨1607066, by rfl⟩ : syracuseStep 2142755 = 3214133) B3214133
theorem B6861509 : Blo 948586 6861509 := bstep (se 4 (by rfl) ⟨643266, by rfl⟩ : syracuseStep 6861509 = 1286533) B1286533
theorem B2405123 : Blo 948586 2405123 := bstep (se 1 (by rfl) ⟨1803842, by rfl⟩ : syracuseStep 2405123 = 3607685) B3607685
theorem B2143025 : Blo 948586 2143025 := bstep (se 2 (by rfl) ⟨803634, by rfl⟩ : syracuseStep 2143025 = 1607269) B1607269
theorem B2143043 : Blo 948586 2143043 := bstep (se 1 (by rfl) ⟨1607282, by rfl⟩ : syracuseStep 2143043 = 3214565) B3214565
theorem B2405315 : Blo 948586 2405315 := bstep (se 1 (by rfl) ⟨1803986, by rfl⟩ : syracuseStep 2405315 = 3607973) B3607973
theorem B4568035 : Blo 948586 4568035 := bstep (se 1 (by rfl) ⟨3426026, by rfl⟩ : syracuseStep 4568035 = 6852053) B6852053
theorem B9745393 : Blo 948586 9745393 := bstep (se 2 (by rfl) ⟨3654522, by rfl⟩ : syracuseStep 9745393 = 7309045) B7309045
theorem B2143313 : Blo 948586 2143313 := bstep (se 2 (by rfl) ⟨803742, by rfl⟩ : syracuseStep 2143313 = 1607485) B1607485
theorem B2569315 : Blo 948586 2569315 := bstep (se 1 (by rfl) ⟨1926986, by rfl⟩ : syracuseStep 2569315 = 3853973) B3853973
theorem B10827107 : Blo 948586 10827107 := bstep (se 1 (by rfl) ⟨8120330, by rfl⟩ : syracuseStep 10827107 = 16240661) B16240661
theorem B7419377 : Blo 948586 7419377 := bstep (se 2 (by rfl) ⟨2782266, by rfl⟩ : syracuseStep 7419377 = 5564533) B5564533
theorem B1422881 : Blo 948586 1422881 := bstep (se 2 (by rfl) ⟨533580, by rfl⟩ : syracuseStep 1422881 = 1067161) B1067161
theorem B1422899 : Blo 948586 1422899 := bstep (se 1 (by rfl) ⟨1067174, by rfl⟩ : syracuseStep 1422899 = 2134349) B2134349
theorem B1422929 : Blo 948586 1422929 := bstep (se 2 (by rfl) ⟨533598, by rfl⟩ : syracuseStep 1422929 = 1067197) B1067197
theorem B1422947 : Blo 948586 1422947 := bstep (se 1 (by rfl) ⟨1067210, by rfl⟩ : syracuseStep 1422947 = 2134421) B2134421
theorem B1422977 : Blo 948586 1422977 := bstep (se 2 (by rfl) ⟨533616, by rfl⟩ : syracuseStep 1422977 = 1067233) B1067233
theorem B1521281 : Blo 948586 1521281 := bstep (se 2 (by rfl) ⟨570480, by rfl⟩ : syracuseStep 1521281 = 1140961) B1140961
theorem B1422995 : Blo 948586 1422995 := bstep (se 1 (by rfl) ⟨1067246, by rfl⟩ : syracuseStep 1422995 = 2134493) B2134493
theorem B964243 : Blo 948586 964243 := bstep (se 1 (by rfl) ⟨723182, by rfl⟩ : syracuseStep 964243 = 1446365) B1446365
theorem B1423025 : Blo 948586 1423025 := bstep (se 2 (by rfl) ⟨533634, by rfl⟩ : syracuseStep 1423025 = 1067269) B1067269
theorem B1423043 : Blo 948586 1423043 := bstep (se 1 (by rfl) ⟨1067282, by rfl⟩ : syracuseStep 1423043 = 2134565) B2134565
theorem B1423073 : Blo 948586 1423073 := bstep (se 2 (by rfl) ⟨533652, by rfl⟩ : syracuseStep 1423073 = 1067305) B1067305
theorem B1423091 : Blo 948586 1423091 := bstep (se 1 (by rfl) ⟨1067318, by rfl⟩ : syracuseStep 1423091 = 2134637) B2134637
theorem B7812877 : Blo 948586 7812877 := bstep (se 3 (by rfl) ⟨1464914, by rfl⟩ : syracuseStep 7812877 = 2929829) B2929829
theorem B1423121 : Blo 948586 1423121 := bstep (se 2 (by rfl) ⟨533670, by rfl⟩ : syracuseStep 1423121 = 1067341) B1067341
theorem B1423139 : Blo 948586 1423139 := bstep (se 1 (by rfl) ⟨1067354, by rfl⟩ : syracuseStep 1423139 = 2134709) B2134709
theorem B1423169 : Blo 948586 1423169 := bstep (se 2 (by rfl) ⟨533688, by rfl⟩ : syracuseStep 1423169 = 1067377) B1067377
theorem B1423187 : Blo 948586 1423187 := bstep (se 1 (by rfl) ⟨1067390, by rfl⟩ : syracuseStep 1423187 = 2134781) B2134781
theorem B1423217 : Blo 948586 1423217 := bstep (se 2 (by rfl) ⟨533706, by rfl⟩ : syracuseStep 1423217 = 1067413) B1067413
theorem B2406257 : Blo 948586 2406257 := bstep (se 2 (by rfl) ⟨902346, by rfl⟩ : syracuseStep 2406257 = 1804693) B1804693
theorem B1423235 : Blo 948586 1423235 := bstep (se 1 (by rfl) ⟨1067426, by rfl⟩ : syracuseStep 1423235 = 2134853) B2134853
theorem B1423265 : Blo 948586 1423265 := bstep (se 2 (by rfl) ⟨533724, by rfl⟩ : syracuseStep 1423265 = 1067449) B1067449
theorem B2406307 : Blo 948586 2406307 := bstep (se 1 (by rfl) ⟨1804730, by rfl⟩ : syracuseStep 2406307 = 3609461) B3609461
theorem B2570147 : Blo 948586 2570147 := bstep (se 1 (by rfl) ⟨1927610, by rfl⟩ : syracuseStep 2570147 = 3855221) B3855221
theorem B1423283 : Blo 948586 1423283 := bstep (se 1 (by rfl) ⟨1067462, by rfl⟩ : syracuseStep 1423283 = 2134925) B2134925
theorem B30816197 : Blo 948586 30816197 := bstep (se 4 (by rfl) ⟨2889018, by rfl⟩ : syracuseStep 30816197 = 5778037) B5778037
theorem B5421005 : Blo 948586 5421005 := bstep (se 3 (by rfl) ⟨1016438, by rfl⟩ : syracuseStep 5421005 = 2032877) B2032877
theorem B1423313 : Blo 948586 1423313 := bstep (se 2 (by rfl) ⟨533742, by rfl⟩ : syracuseStep 1423313 = 1067485) B1067485
theorem B1423331 : Blo 948586 1423331 := bstep (se 1 (by rfl) ⟨1067498, by rfl⟩ : syracuseStep 1423331 = 2134997) B2134997
theorem B1423361 : Blo 948586 1423361 := bstep (se 2 (by rfl) ⟨533760, by rfl⟩ : syracuseStep 1423361 = 1067521) B1067521
theorem B1423379 : Blo 948586 1423379 := bstep (se 1 (by rfl) ⟨1067534, by rfl⟩ : syracuseStep 1423379 = 2135069) B2135069
theorem B1423409 : Blo 948586 1423409 := bstep (se 2 (by rfl) ⟨533778, by rfl⟩ : syracuseStep 1423409 = 1067557) B1067557
theorem B2406449 : Blo 948586 2406449 := bstep (se 2 (by rfl) ⟨902418, by rfl⟩ : syracuseStep 2406449 = 1804837) B1804837
theorem B1423427 : Blo 948586 1423427 := bstep (se 1 (by rfl) ⟨1067570, by rfl⟩ : syracuseStep 1423427 = 2135141) B2135141
theorem B1423457 : Blo 948586 1423457 := bstep (se 2 (by rfl) ⟨533796, by rfl⟩ : syracuseStep 1423457 = 1067593) B1067593
theorem B5781617 : Blo 948586 5781617 := bstep (se 2 (by rfl) ⟨2168106, by rfl⟩ : syracuseStep 5781617 = 4336213) B4336213
theorem B4700273 : Blo 948586 4700273 := bstep (se 2 (by rfl) ⟨1762602, by rfl⟩ : syracuseStep 4700273 = 3525205) B3525205
theorem B1423475 : Blo 948586 1423475 := bstep (se 1 (by rfl) ⟨1067606, by rfl⟩ : syracuseStep 1423475 = 2135213) B2135213
theorem B1423505 : Blo 948586 1423505 := bstep (se 2 (by rfl) ⟨533814, by rfl⟩ : syracuseStep 1423505 = 1067629) B1067629
theorem B1423523 : Blo 948586 1423523 := bstep (se 1 (by rfl) ⟨1067642, by rfl⟩ : syracuseStep 1423523 = 2135285) B2135285
theorem B1423553 : Blo 948586 1423553 := bstep (se 2 (by rfl) ⟨533832, by rfl⟩ : syracuseStep 1423553 = 1067665) B1067665
theorem B2570449 : Blo 948586 2570449 := bstep (se 2 (by rfl) ⟨963918, by rfl⟩ : syracuseStep 2570449 = 1927837) B1927837
theorem B1423571 : Blo 948586 1423571 := bstep (se 1 (by rfl) ⟨1067678, by rfl⟩ : syracuseStep 1423571 = 2135357) B2135357
theorem B1423601 : Blo 948586 1423601 := bstep (se 2 (by rfl) ⟨533850, by rfl⟩ : syracuseStep 1423601 = 1067701) B1067701
theorem B1423619 : Blo 948586 1423619 := bstep (se 1 (by rfl) ⟨1067714, by rfl⟩ : syracuseStep 1423619 = 2135429) B2135429
theorem B1423649 : Blo 948586 1423649 := bstep (se 2 (by rfl) ⟨533868, by rfl⟩ : syracuseStep 1423649 = 1067737) B1067737
theorem B1423667 : Blo 948586 1423667 := bstep (se 1 (by rfl) ⟨1067750, by rfl⟩ : syracuseStep 1423667 = 2135501) B2135501
theorem B1423697 : Blo 948586 1423697 := bstep (se 2 (by rfl) ⟨533886, by rfl⟩ : syracuseStep 1423697 = 1067773) B1067773
theorem B1423715 : Blo 948586 1423715 := bstep (se 1 (by rfl) ⟨1067786, by rfl⟩ : syracuseStep 1423715 = 2135573) B2135573
theorem B1423745 : Blo 948586 1423745 := bstep (se 2 (by rfl) ⟨533904, by rfl⟩ : syracuseStep 1423745 = 1067809) B1067809
theorem B1423763 : Blo 948586 1423763 := bstep (se 1 (by rfl) ⟨1067822, by rfl⟩ : syracuseStep 1423763 = 2135645) B2135645
theorem B1423793 : Blo 948586 1423793 := bstep (se 2 (by rfl) ⟨533922, by rfl⟩ : syracuseStep 1423793 = 1067845) B1067845
theorem B1423811 : Blo 948586 1423811 := bstep (se 1 (by rfl) ⟨1067858, by rfl⟩ : syracuseStep 1423811 = 2135717) B2135717
theorem B1423841 : Blo 948586 1423841 := bstep (se 2 (by rfl) ⟨533940, by rfl⟩ : syracuseStep 1423841 = 1067881) B1067881
theorem B1522147 : Blo 948586 1522147 := bstep (se 1 (by rfl) ⟨1141610, by rfl⟩ : syracuseStep 1522147 = 2283221) B2283221
theorem B1423859 : Blo 948586 1423859 := bstep (se 1 (by rfl) ⟨1067894, by rfl⟩ : syracuseStep 1423859 = 2135789) B2135789
theorem B10271245 : Blo 948586 10271245 := bstep (se 3 (by rfl) ⟨1925858, by rfl⟩ : syracuseStep 10271245 = 3851717) B3851717
theorem B1423889 : Blo 948586 1423889 := bstep (se 2 (by rfl) ⟨533958, by rfl⟩ : syracuseStep 1423889 = 1067917) B1067917
theorem B1423907 : Blo 948586 1423907 := bstep (se 1 (by rfl) ⟨1067930, by rfl⟩ : syracuseStep 1423907 = 2135861) B2135861
theorem B1423937 : Blo 948586 1423937 := bstep (se 2 (by rfl) ⟨533976, by rfl⟩ : syracuseStep 1423937 = 1067953) B1067953
theorem B1423955 : Blo 948586 1423955 := bstep (se 1 (by rfl) ⟨1067966, by rfl⟩ : syracuseStep 1423955 = 2135933) B2135933
theorem B2701937 : Blo 948586 2701937 := bstep (se 2 (by rfl) ⟨1013226, by rfl⟩ : syracuseStep 2701937 = 2026453) B2026453
theorem B1423985 : Blo 948586 1423985 := bstep (se 2 (by rfl) ⟨533994, by rfl⟩ : syracuseStep 1423985 = 1067989) B1067989
theorem B1424003 : Blo 948586 1424003 := bstep (se 1 (by rfl) ⟨1068002, by rfl⟩ : syracuseStep 1424003 = 2136005) B2136005
theorem B1424033 : Blo 948586 1424033 := bstep (se 2 (by rfl) ⟨534012, by rfl⟩ : syracuseStep 1424033 = 1068025) B1068025
theorem B1424051 : Blo 948586 1424051 := bstep (se 1 (by rfl) ⟨1068038, by rfl⟩ : syracuseStep 1424051 = 2136077) B2136077
theorem B1424081 : Blo 948586 1424081 := bstep (se 2 (by rfl) ⟨534030, by rfl⟩ : syracuseStep 1424081 = 1068061) B1068061
theorem B1424099 : Blo 948586 1424099 := bstep (se 1 (by rfl) ⟨1068074, by rfl⟩ : syracuseStep 1424099 = 2136149) B2136149
theorem B1522403 : Blo 948586 1522403 := bstep (se 1 (by rfl) ⟨1141802, by rfl⟩ : syracuseStep 1522403 = 2283605) B2283605
theorem B1424129 : Blo 948586 1424129 := bstep (se 2 (by rfl) ⟨534048, by rfl⟩ : syracuseStep 1424129 = 1068097) B1068097
theorem B1424147 : Blo 948586 1424147 := bstep (se 1 (by rfl) ⟨1068110, by rfl⟩ : syracuseStep 1424147 = 2136221) B2136221
theorem B71219989 : Blo 948586 71219989 := bstep (se 6 (by rfl) ⟨1669218, by rfl⟩ : syracuseStep 71219989 = 3338437) B3338437
theorem B1424177 : Blo 948586 1424177 := bstep (se 2 (by rfl) ⟨534066, by rfl⟩ : syracuseStep 1424177 = 1068133) B1068133
theorem B1424195 : Blo 948586 1424195 := bstep (se 1 (by rfl) ⟨1068146, by rfl⟩ : syracuseStep 1424195 = 2136293) B2136293
theorem B965443 : Blo 948586 965443 := bstep (se 1 (by rfl) ⟨724082, by rfl⟩ : syracuseStep 965443 = 1448165) B1448165
theorem B1424225 : Blo 948586 1424225 := bstep (se 2 (by rfl) ⟨534084, by rfl⟩ : syracuseStep 1424225 = 1068169) B1068169
theorem B3849059 : Blo 948586 3849059 := bstep (se 1 (by rfl) ⟨2886794, by rfl⟩ : syracuseStep 3849059 = 5773589) B5773589
theorem B5421937 : Blo 948586 5421937 := bstep (se 2 (by rfl) ⟨2033226, by rfl⟩ : syracuseStep 5421937 = 4066453) B4066453
theorem B1424243 : Blo 948586 1424243 := bstep (se 1 (by rfl) ⟨1068182, by rfl⟩ : syracuseStep 1424243 = 2136365) B2136365
theorem B1424273 : Blo 948586 1424273 := bstep (se 2 (by rfl) ⟨534102, by rfl⟩ : syracuseStep 1424273 = 1068205) B1068205
theorem B1424291 : Blo 948586 1424291 := bstep (se 1 (by rfl) ⟨1068218, by rfl⟩ : syracuseStep 1424291 = 2136437) B2136437
theorem B4570033 : Blo 948586 4570033 := bstep (se 2 (by rfl) ⟨1713762, by rfl⟩ : syracuseStep 4570033 = 3427525) B3427525
theorem B1424321 : Blo 948586 1424321 := bstep (se 2 (by rfl) ⟨534120, by rfl⟩ : syracuseStep 1424321 = 1068241) B1068241
theorem B1424339 : Blo 948586 1424339 := bstep (se 1 (by rfl) ⟨1068254, by rfl⟩ : syracuseStep 1424339 = 2136509) B2136509
theorem B1424369 : Blo 948586 1424369 := bstep (se 2 (by rfl) ⟨534138, by rfl⟩ : syracuseStep 1424369 = 1068277) B1068277
theorem B1424387 : Blo 948586 1424387 := bstep (se 1 (by rfl) ⟨1068290, by rfl⟩ : syracuseStep 1424387 = 2136581) B2136581
theorem B2407441 : Blo 948586 2407441 := bstep (se 2 (by rfl) ⟨902790, by rfl⟩ : syracuseStep 2407441 = 1805581) B1805581
theorem B1424417 : Blo 948586 1424417 := bstep (se 2 (by rfl) ⟨534156, by rfl⟩ : syracuseStep 1424417 = 1068313) B1068313
theorem B1424435 : Blo 948586 1424435 := bstep (se 1 (by rfl) ⟨1068326, by rfl⟩ : syracuseStep 1424435 = 2136653) B2136653
theorem B7224389 : Blo 948586 7224389 := bstep (se 4 (by rfl) ⟨677286, by rfl⟩ : syracuseStep 7224389 = 1354573) B1354573
theorem B1424465 : Blo 948586 1424465 := bstep (se 2 (by rfl) ⟨534174, by rfl⟩ : syracuseStep 1424465 = 1068349) B1068349
theorem B1424483 : Blo 948586 1424483 := bstep (se 1 (by rfl) ⟨1068362, by rfl⟩ : syracuseStep 1424483 = 2136725) B2136725
theorem B1424513 : Blo 948586 1424513 := bstep (se 2 (by rfl) ⟨534192, by rfl⟩ : syracuseStep 1424513 = 1068385) B1068385
theorem B1424531 : Blo 948586 1424531 := bstep (se 1 (by rfl) ⟨1068398, by rfl⟩ : syracuseStep 1424531 = 2136797) B2136797
theorem B1424561 : Blo 948586 1424561 := bstep (se 2 (by rfl) ⟨534210, by rfl⟩ : syracuseStep 1424561 = 1068421) B1068421
theorem B1424579 : Blo 948586 1424579 := bstep (se 1 (by rfl) ⟨1068434, by rfl⟩ : syracuseStep 1424579 = 2136869) B2136869
theorem B1424609 : Blo 948586 1424609 := bstep (se 2 (by rfl) ⟨534228, by rfl⟩ : syracuseStep 1424609 = 1068457) B1068457
theorem B1424627 : Blo 948586 1424627 := bstep (se 1 (by rfl) ⟨1068470, by rfl⟩ : syracuseStep 1424627 = 2136941) B2136941
theorem B2702609 : Blo 948586 2702609 := bstep (se 2 (by rfl) ⟨1013478, by rfl⟩ : syracuseStep 2702609 = 2026957) B2026957
theorem B1424657 : Blo 948586 1424657 := bstep (se 2 (by rfl) ⟨534246, by rfl⟩ : syracuseStep 1424657 = 1068493) B1068493
theorem B1424675 : Blo 948586 1424675 := bstep (se 1 (by rfl) ⟨1068506, by rfl⟩ : syracuseStep 1424675 = 2137013) B2137013
theorem B2407715 : Blo 948586 2407715 := bstep (se 1 (by rfl) ⟨1805786, by rfl⟩ : syracuseStep 2407715 = 3611573) B3611573
theorem B1424705 : Blo 948586 1424705 := bstep (se 2 (by rfl) ⟨534264, by rfl⟩ : syracuseStep 1424705 = 1068529) B1068529
theorem B1424723 : Blo 948586 1424723 := bstep (se 1 (by rfl) ⟨1068542, by rfl⟩ : syracuseStep 1424723 = 2137085) B2137085
theorem B1424753 : Blo 948586 1424753 := bstep (se 2 (by rfl) ⟨534282, by rfl⟩ : syracuseStep 1424753 = 1068565) B1068565
theorem B1424771 : Blo 948586 1424771 := bstep (se 1 (by rfl) ⟨1068578, by rfl⟩ : syracuseStep 1424771 = 2137157) B2137157
theorem B1424801 : Blo 948586 1424801 := bstep (se 2 (by rfl) ⟨534300, by rfl⟩ : syracuseStep 1424801 = 1068601) B1068601
theorem B1424819 : Blo 948586 1424819 := bstep (se 1 (by rfl) ⟨1068614, by rfl⟩ : syracuseStep 1424819 = 2137229) B2137229
theorem B1424849 : Blo 948586 1424849 := bstep (se 2 (by rfl) ⟨534318, by rfl⟩ : syracuseStep 1424849 = 1068637) B1068637
theorem B2440657 : Blo 948586 2440657 := bstep (se 2 (by rfl) ⟨915246, by rfl⟩ : syracuseStep 2440657 = 1830493) B1830493
theorem B1424867 : Blo 948586 1424867 := bstep (se 1 (by rfl) ⟨1068650, by rfl⟩ : syracuseStep 1424867 = 2137301) B2137301
theorem B2407907 : Blo 948586 2407907 := bstep (se 1 (by rfl) ⟨1805930, by rfl⟩ : syracuseStep 2407907 = 3611861) B3611861
theorem B1424897 : Blo 948586 1424897 := bstep (se 2 (by rfl) ⟨534336, by rfl⟩ : syracuseStep 1424897 = 1068673) B1068673
theorem B1424915 : Blo 948586 1424915 := bstep (se 1 (by rfl) ⟨1068686, by rfl⟩ : syracuseStep 1424915 = 2137373) B2137373
theorem B1424945 : Blo 948586 1424945 := bstep (se 2 (by rfl) ⟨534354, by rfl⟩ : syracuseStep 1424945 = 1068709) B1068709
theorem B1424963 : Blo 948586 1424963 := bstep (se 1 (by rfl) ⟨1068722, by rfl⟩ : syracuseStep 1424963 = 2137445) B2137445
theorem B1424993 : Blo 948586 1424993 := bstep (se 2 (by rfl) ⟨534372, by rfl⟩ : syracuseStep 1424993 = 1068745) B1068745
theorem B1425011 : Blo 948586 1425011 := bstep (se 1 (by rfl) ⟨1068758, by rfl⟩ : syracuseStep 1425011 = 2137517) B2137517
theorem B1425041 : Blo 948586 1425041 := bstep (se 2 (by rfl) ⟨534390, by rfl⟩ : syracuseStep 1425041 = 1068781) B1068781
theorem B1425059 : Blo 948586 1425059 := bstep (se 1 (by rfl) ⟨1068794, by rfl⟩ : syracuseStep 1425059 = 2137589) B2137589
theorem B1523377 : Blo 948586 1523377 := bstep (se 2 (by rfl) ⟨571266, by rfl⟩ : syracuseStep 1523377 = 1142533) B1142533
theorem B1425089 : Blo 948586 1425089 := bstep (se 2 (by rfl) ⟨534408, by rfl⟩ : syracuseStep 1425089 = 1068817) B1068817
theorem B2637517 : Blo 948586 2637517 := bstep (se 3 (by rfl) ⟨494534, by rfl⟩ : syracuseStep 2637517 = 989069) B989069
theorem B1425107 : Blo 948586 1425107 := bstep (se 1 (by rfl) ⟨1068830, by rfl⟩ : syracuseStep 1425107 = 2137661) B2137661
theorem B1425137 : Blo 948586 1425137 := bstep (se 2 (by rfl) ⟨534426, by rfl⟩ : syracuseStep 1425137 = 1068853) B1068853
theorem B1425155 : Blo 948586 1425155 := bstep (se 1 (by rfl) ⟨1068866, by rfl⟩ : syracuseStep 1425155 = 2137733) B2137733
theorem B1425185 : Blo 948586 1425185 := bstep (se 2 (by rfl) ⟨534444, by rfl⟩ : syracuseStep 1425185 = 1068889) B1068889
theorem B1425203 : Blo 948586 1425203 := bstep (se 1 (by rfl) ⟨1068902, by rfl⟩ : syracuseStep 1425203 = 2137805) B2137805
theorem B1425233 : Blo 948586 1425233 := bstep (se 2 (by rfl) ⟨534462, by rfl⟩ : syracuseStep 1425233 = 1068925) B1068925
theorem B1425251 : Blo 948586 1425251 := bstep (se 1 (by rfl) ⟨1068938, by rfl⟩ : syracuseStep 1425251 = 2137877) B2137877
theorem B1425281 : Blo 948586 1425281 := bstep (se 2 (by rfl) ⟨534480, by rfl⟩ : syracuseStep 1425281 = 1068961) B1068961
theorem B1425299 : Blo 948586 1425299 := bstep (se 1 (by rfl) ⟨1068974, by rfl⟩ : syracuseStep 1425299 = 2137949) B2137949
theorem B1425329 : Blo 948586 1425329 := bstep (se 2 (by rfl) ⟨534498, by rfl⟩ : syracuseStep 1425329 = 1068997) B1068997
theorem B1425347 : Blo 948586 1425347 := bstep (se 1 (by rfl) ⟨1069010, by rfl⟩ : syracuseStep 1425347 = 2138021) B2138021
theorem B1425377 : Blo 948586 1425377 := bstep (se 2 (by rfl) ⟨534516, by rfl⟩ : syracuseStep 1425377 = 1069033) B1069033
theorem B1425395 : Blo 948586 1425395 := bstep (se 1 (by rfl) ⟨1069046, by rfl⟩ : syracuseStep 1425395 = 2138093) B2138093
theorem B1425425 : Blo 948586 1425425 := bstep (se 2 (by rfl) ⟨534534, by rfl⟩ : syracuseStep 1425425 = 1069069) B1069069
theorem B2703395 : Blo 948586 2703395 := bstep (se 1 (by rfl) ⟨2027546, by rfl⟩ : syracuseStep 2703395 = 4055093) B4055093
theorem B1425443 : Blo 948586 1425443 := bstep (se 1 (by rfl) ⟨1069082, by rfl⟩ : syracuseStep 1425443 = 2138165) B2138165
theorem B1425473 : Blo 948586 1425473 := bstep (se 2 (by rfl) ⟨534552, by rfl⟩ : syracuseStep 1425473 = 1069105) B1069105
theorem B1425491 : Blo 948586 1425491 := bstep (se 1 (by rfl) ⟨1069118, by rfl⟩ : syracuseStep 1425491 = 2138237) B2138237
theorem B6078563 : Blo 948586 6078563 := bstep (se 1 (by rfl) ⟨4558922, by rfl⟩ : syracuseStep 6078563 = 9117845) B9117845
theorem B1425521 : Blo 948586 1425521 := bstep (se 2 (by rfl) ⟨534570, by rfl⟩ : syracuseStep 1425521 = 1069141) B1069141
theorem B1425539 : Blo 948586 1425539 := bstep (se 1 (by rfl) ⟨1069154, by rfl⟩ : syracuseStep 1425539 = 2138309) B2138309
theorem B1425569 : Blo 948586 1425569 := bstep (se 2 (by rfl) ⟨534588, by rfl⟩ : syracuseStep 1425569 = 1069177) B1069177
theorem B1425587 : Blo 948586 1425587 := bstep (se 1 (by rfl) ⟨1069190, by rfl⟩ : syracuseStep 1425587 = 2138381) B2138381
theorem B1425617 : Blo 948586 1425617 := bstep (se 2 (by rfl) ⟨534606, by rfl⟩ : syracuseStep 1425617 = 1069213) B1069213
theorem B1425635 : Blo 948586 1425635 := bstep (se 1 (by rfl) ⟨1069226, by rfl⟩ : syracuseStep 1425635 = 2138453) B2138453
theorem B1425665 : Blo 948586 1425665 := bstep (se 2 (by rfl) ⟨534624, by rfl⟩ : syracuseStep 1425665 = 1069249) B1069249
theorem B1425683 : Blo 948586 1425683 := bstep (se 1 (by rfl) ⟨1069262, by rfl⟩ : syracuseStep 1425683 = 2138525) B2138525
theorem B5423395 : Blo 948586 5423395 := bstep (se 1 (by rfl) ⟨4067546, by rfl⟩ : syracuseStep 5423395 = 8135093) B8135093
theorem B1425713 : Blo 948586 1425713 := bstep (se 2 (by rfl) ⟨534642, by rfl⟩ : syracuseStep 1425713 = 1069285) B1069285
theorem B1425731 : Blo 948586 1425731 := bstep (se 1 (by rfl) ⟨1069298, by rfl⟩ : syracuseStep 1425731 = 2138597) B2138597
theorem B1425761 : Blo 948586 1425761 := bstep (se 2 (by rfl) ⟨534660, by rfl⟩ : syracuseStep 1425761 = 1069321) B1069321
theorem B9748835 : Blo 948586 9748835 := bstep (se 1 (by rfl) ⟨7311626, by rfl⟩ : syracuseStep 9748835 = 14623253) B14623253
theorem B2703725 : Blo 948586 2703725 := bstep (se 3 (by rfl) ⟨506948, by rfl⟩ : syracuseStep 2703725 = 1013897) B1013897
theorem B1425779 : Blo 948586 1425779 := bstep (se 1 (by rfl) ⟨1069334, by rfl⟩ : syracuseStep 1425779 = 2138669) B2138669
theorem B4342157 : Blo 948586 4342157 := bstep (se 3 (by rfl) ⟨814154, by rfl⟩ : syracuseStep 4342157 = 1628309) B1628309
theorem B1425809 : Blo 948586 1425809 := bstep (se 2 (by rfl) ⟨534678, by rfl⟩ : syracuseStep 1425809 = 1069357) B1069357
theorem B2408849 : Blo 948586 2408849 := bstep (se 2 (by rfl) ⟨903318, by rfl⟩ : syracuseStep 2408849 = 1806637) B1806637
theorem B1425827 : Blo 948586 1425827 := bstep (se 1 (by rfl) ⟨1069370, by rfl⟩ : syracuseStep 1425827 = 2138741) B2138741
theorem B2703793 : Blo 948586 2703793 := bstep (se 2 (by rfl) ⟨1013922, by rfl⟩ : syracuseStep 2703793 = 2027845) B2027845
theorem B1425857 : Blo 948586 1425857 := bstep (se 2 (by rfl) ⟨534696, by rfl⟩ : syracuseStep 1425857 = 1069393) B1069393
theorem B2408899 : Blo 948586 2408899 := bstep (se 1 (by rfl) ⟨1806674, by rfl⟩ : syracuseStep 2408899 = 3613349) B3613349
theorem B1425875 : Blo 948586 1425875 := bstep (se 1 (by rfl) ⟨1069406, by rfl⟩ : syracuseStep 1425875 = 2138813) B2138813
theorem B1425905 : Blo 948586 1425905 := bstep (se 2 (by rfl) ⟨534714, by rfl⟩ : syracuseStep 1425905 = 1069429) B1069429
theorem B1425923 : Blo 948586 1425923 := bstep (se 1 (by rfl) ⟨1069442, by rfl⟩ : syracuseStep 1425923 = 2138885) B2138885
theorem B1425953 : Blo 948586 1425953 := bstep (se 2 (by rfl) ⟨534732, by rfl⟩ : syracuseStep 1425953 = 1069465) B1069465
theorem B1425971 : Blo 948586 1425971 := bstep (se 1 (by rfl) ⟨1069478, by rfl⟩ : syracuseStep 1425971 = 2138957) B2138957
theorem B1426001 : Blo 948586 1426001 := bstep (se 2 (by rfl) ⟨534750, by rfl⟩ : syracuseStep 1426001 = 1069501) B1069501
theorem B1524305 : Blo 948586 1524305 := bstep (se 2 (by rfl) ⟨571614, by rfl⟩ : syracuseStep 1524305 = 1143229) B1143229
theorem B2409041 : Blo 948586 2409041 := bstep (se 2 (by rfl) ⟨903390, by rfl⟩ : syracuseStep 2409041 = 1806781) B1806781
theorem B1426019 : Blo 948586 1426019 := bstep (se 1 (by rfl) ⟨1069514, by rfl⟩ : syracuseStep 1426019 = 2139029) B2139029
theorem B1426049 : Blo 948586 1426049 := bstep (se 2 (by rfl) ⟨534768, by rfl⟩ : syracuseStep 1426049 = 1069537) B1069537
theorem B1426067 : Blo 948586 1426067 := bstep (se 1 (by rfl) ⟨1069550, by rfl⟩ : syracuseStep 1426067 = 2139101) B2139101
theorem B3424945 : Blo 948586 3424945 := bstep (se 2 (by rfl) ⟨1284354, by rfl⟩ : syracuseStep 3424945 = 2568709) B2568709
theorem B1426097 : Blo 948586 1426097 := bstep (se 2 (by rfl) ⟨534786, by rfl⟩ : syracuseStep 1426097 = 1069573) B1069573
theorem B2704067 : Blo 948586 2704067 := bstep (se 1 (by rfl) ⟨2028050, by rfl⟩ : syracuseStep 2704067 = 4056101) B4056101
theorem B1426115 : Blo 948586 1426115 := bstep (se 1 (by rfl) ⟨1069586, by rfl⟩ : syracuseStep 1426115 = 2139173) B2139173
theorem B1426145 : Blo 948586 1426145 := bstep (se 2 (by rfl) ⟨534804, by rfl⟩ : syracuseStep 1426145 = 1069609) B1069609
theorem B1426163 : Blo 948586 1426163 := bstep (se 1 (by rfl) ⟨1069622, by rfl⟩ : syracuseStep 1426163 = 2139245) B2139245
theorem B1426193 : Blo 948586 1426193 := bstep (se 2 (by rfl) ⟨534822, by rfl⟩ : syracuseStep 1426193 = 1069645) B1069645
theorem B1426211 : Blo 948586 1426211 := bstep (se 1 (by rfl) ⟨1069658, by rfl⟩ : syracuseStep 1426211 = 2139317) B2139317
theorem B5423921 : Blo 948586 5423921 := bstep (se 2 (by rfl) ⟨2033970, by rfl⟩ : syracuseStep 5423921 = 4067941) B4067941
theorem B1426241 : Blo 948586 1426241 := bstep (se 2 (by rfl) ⟨534840, by rfl⟩ : syracuseStep 1426241 = 1069681) B1069681
theorem B1426259 : Blo 948586 1426259 := bstep (se 1 (by rfl) ⟨1069694, by rfl⟩ : syracuseStep 1426259 = 2139389) B2139389
theorem B1426289 : Blo 948586 1426289 := bstep (se 2 (by rfl) ⟨534858, by rfl⟩ : syracuseStep 1426289 = 1069717) B1069717
theorem B1426307 : Blo 948586 1426307 := bstep (se 1 (by rfl) ⟨1069730, by rfl⟩ : syracuseStep 1426307 = 2139461) B2139461
theorem B1426337 : Blo 948586 1426337 := bstep (se 2 (by rfl) ⟨534876, by rfl⟩ : syracuseStep 1426337 = 1069753) B1069753
theorem B1426355 : Blo 948586 1426355 := bstep (se 1 (by rfl) ⟨1069766, by rfl⟩ : syracuseStep 1426355 = 2139533) B2139533
theorem B1426385 : Blo 948586 1426385 := bstep (se 2 (by rfl) ⟨534894, by rfl⟩ : syracuseStep 1426385 = 1069789) B1069789
theorem B1426403 : Blo 948586 1426403 := bstep (se 1 (by rfl) ⟨1069802, by rfl⟩ : syracuseStep 1426403 = 2139605) B2139605
theorem B1426433 : Blo 948586 1426433 := bstep (se 2 (by rfl) ⟨534912, by rfl⟩ : syracuseStep 1426433 = 1069825) B1069825
theorem B1426451 : Blo 948586 1426451 := bstep (se 1 (by rfl) ⟨1069838, by rfl⟩ : syracuseStep 1426451 = 2139677) B2139677
theorem B1426481 : Blo 948586 1426481 := bstep (se 2 (by rfl) ⟨534930, by rfl⟩ : syracuseStep 1426481 = 1069861) B1069861
theorem B1426499 : Blo 948586 1426499 := bstep (se 1 (by rfl) ⟨1069874, by rfl⟩ : syracuseStep 1426499 = 2139749) B2139749
theorem B1426529 : Blo 948586 1426529 := bstep (se 2 (by rfl) ⟨534948, by rfl⟩ : syracuseStep 1426529 = 1069897) B1069897
theorem B1426547 : Blo 948586 1426547 := bstep (se 1 (by rfl) ⟨1069910, by rfl⟩ : syracuseStep 1426547 = 2139821) B2139821
theorem B1426577 : Blo 948586 1426577 := bstep (se 2 (by rfl) ⟨534966, by rfl⟩ : syracuseStep 1426577 = 1069933) B1069933
theorem B1426595 : Blo 948586 1426595 := bstep (se 1 (by rfl) ⟨1069946, by rfl⟩ : syracuseStep 1426595 = 2139893) B2139893
theorem B1426625 : Blo 948586 1426625 := bstep (se 2 (by rfl) ⟨534984, by rfl⟩ : syracuseStep 1426625 = 1069969) B1069969
theorem B1426643 : Blo 948586 1426643 := bstep (se 1 (by rfl) ⟨1069982, by rfl⟩ : syracuseStep 1426643 = 2139965) B2139965
theorem B1426673 : Blo 948586 1426673 := bstep (se 2 (by rfl) ⟨535002, by rfl⟩ : syracuseStep 1426673 = 1070005) B1070005
theorem B1426691 : Blo 948586 1426691 := bstep (se 1 (by rfl) ⟨1070018, by rfl⟩ : syracuseStep 1426691 = 2140037) B2140037
theorem B1426721 : Blo 948586 1426721 := bstep (se 2 (by rfl) ⟨535020, by rfl⟩ : syracuseStep 1426721 = 1070041) B1070041
theorem B1426739 : Blo 948586 1426739 := bstep (se 1 (by rfl) ⟨1070054, by rfl⟩ : syracuseStep 1426739 = 2140109) B2140109
theorem B1426769 : Blo 948586 1426769 := bstep (se 2 (by rfl) ⟨535038, by rfl⟩ : syracuseStep 1426769 = 1070077) B1070077
theorem B1426787 : Blo 948586 1426787 := bstep (se 1 (by rfl) ⟨1070090, by rfl⟩ : syracuseStep 1426787 = 2140181) B2140181
theorem B1426817 : Blo 948586 1426817 := bstep (se 2 (by rfl) ⟨535056, by rfl⟩ : syracuseStep 1426817 = 1070113) B1070113
theorem B6014341 : Blo 948586 6014341 := bstep (se 4 (by rfl) ⟨563844, by rfl⟩ : syracuseStep 6014341 = 1127689) B1127689
theorem B1426835 : Blo 948586 1426835 := bstep (se 1 (by rfl) ⟨1070126, by rfl⟩ : syracuseStep 1426835 = 2140253) B2140253
theorem B1525139 : Blo 948586 1525139 := bstep (se 1 (by rfl) ⟨1143854, by rfl⟩ : syracuseStep 1525139 = 2287709) B2287709
theorem B1426865 : Blo 948586 1426865 := bstep (se 2 (by rfl) ⟨535074, by rfl⟩ : syracuseStep 1426865 = 1070149) B1070149
theorem B1525171 : Blo 948586 1525171 := bstep (se 1 (by rfl) ⟨1143878, by rfl⟩ : syracuseStep 1525171 = 2287757) B2287757
theorem B1426883 : Blo 948586 1426883 := bstep (se 1 (by rfl) ⟨1070162, by rfl⟩ : syracuseStep 1426883 = 2140325) B2140325
theorem B1426913 : Blo 948586 1426913 := bstep (se 2 (by rfl) ⟨535092, by rfl⟩ : syracuseStep 1426913 = 1070185) B1070185
theorem B1426931 : Blo 948586 1426931 := bstep (se 1 (by rfl) ⟨1070198, by rfl⟩ : syracuseStep 1426931 = 2140397) B2140397
theorem B2704909 : Blo 948586 2704909 := bstep (se 3 (by rfl) ⟨507170, by rfl⟩ : syracuseStep 2704909 = 1014341) B1014341
theorem B1426961 : Blo 948586 1426961 := bstep (se 2 (by rfl) ⟨535110, by rfl⟩ : syracuseStep 1426961 = 1070221) B1070221
theorem B1426979 : Blo 948586 1426979 := bstep (se 1 (by rfl) ⟨1070234, by rfl⟩ : syracuseStep 1426979 = 2140469) B2140469
theorem B2410033 : Blo 948586 2410033 := bstep (se 2 (by rfl) ⟨903762, by rfl⟩ : syracuseStep 2410033 = 1807525) B1807525
theorem B1427009 : Blo 948586 1427009 := bstep (se 2 (by rfl) ⟨535128, by rfl⟩ : syracuseStep 1427009 = 1070257) B1070257
theorem B1427027 : Blo 948586 1427027 := bstep (se 1 (by rfl) ⟨1070270, by rfl⟩ : syracuseStep 1427027 = 2140541) B2140541
theorem B1427057 : Blo 948586 1427057 := bstep (se 2 (by rfl) ⟨535146, by rfl⟩ : syracuseStep 1427057 = 1070293) B1070293
theorem B1427075 : Blo 948586 1427075 := bstep (se 1 (by rfl) ⟨1070306, by rfl⟩ : syracuseStep 1427075 = 2140613) B2140613
theorem B1427105 : Blo 948586 1427105 := bstep (se 2 (by rfl) ⟨535164, by rfl⟩ : syracuseStep 1427105 = 1070329) B1070329
theorem B2705069 : Blo 948586 2705069 := bstep (se 3 (by rfl) ⟨507200, by rfl⟩ : syracuseStep 2705069 = 1014401) B1014401
theorem B4343473 : Blo 948586 4343473 := bstep (se 2 (by rfl) ⟨1628802, by rfl⟩ : syracuseStep 4343473 = 3257605) B3257605
theorem B1427123 : Blo 948586 1427123 := bstep (se 1 (by rfl) ⟨1070342, by rfl⟩ : syracuseStep 1427123 = 2140685) B2140685
theorem B1427153 : Blo 948586 1427153 := bstep (se 2 (by rfl) ⟨535182, by rfl⟩ : syracuseStep 1427153 = 1070365) B1070365
theorem B1427171 : Blo 948586 1427171 := bstep (se 1 (by rfl) ⟨1070378, by rfl⟩ : syracuseStep 1427171 = 2140757) B2140757
theorem B1427201 : Blo 948586 1427201 := bstep (se 2 (by rfl) ⟨535200, by rfl⟩ : syracuseStep 1427201 = 1070401) B1070401
theorem B1427219 : Blo 948586 1427219 := bstep (se 1 (by rfl) ⟨1070414, by rfl⟩ : syracuseStep 1427219 = 2140829) B2140829
theorem B46909205 : Blo 948586 46909205 := bstep (se 6 (by rfl) ⟨1099434, by rfl⟩ : syracuseStep 46909205 = 2198869) B2198869
theorem B6080305 : Blo 948586 6080305 := bstep (se 2 (by rfl) ⟨2280114, by rfl⟩ : syracuseStep 6080305 = 4560229) B4560229
theorem B1427249 : Blo 948586 1427249 := bstep (se 2 (by rfl) ⟨535218, by rfl⟩ : syracuseStep 1427249 = 1070437) B1070437
theorem B1427267 : Blo 948586 1427267 := bstep (se 1 (by rfl) ⟨1070450, by rfl⟩ : syracuseStep 1427267 = 2140901) B2140901
theorem B2410307 : Blo 948586 2410307 := bstep (se 1 (by rfl) ⟨1807730, by rfl⟩ : syracuseStep 2410307 = 3615461) B3615461
theorem B1427297 : Blo 948586 1427297 := bstep (se 2 (by rfl) ⟨535236, by rfl⟩ : syracuseStep 1427297 = 1070473) B1070473
theorem B2705251 : Blo 948586 2705251 := bstep (se 1 (by rfl) ⟨2028938, by rfl⟩ : syracuseStep 2705251 = 4057877) B4057877
theorem B1427315 : Blo 948586 1427315 := bstep (se 1 (by rfl) ⟨1070486, by rfl⟩ : syracuseStep 1427315 = 2140973) B2140973
theorem B2279299 : Blo 948586 2279299 := bstep (se 1 (by rfl) ⟨1709474, by rfl⟩ : syracuseStep 2279299 = 3418949) B3418949
theorem B1427345 : Blo 948586 1427345 := bstep (se 2 (by rfl) ⟨535254, by rfl⟩ : syracuseStep 1427345 = 1070509) B1070509
theorem B1427363 : Blo 948586 1427363 := bstep (se 1 (by rfl) ⟨1070522, by rfl⟩ : syracuseStep 1427363 = 2141045) B2141045
theorem B1427393 : Blo 948586 1427393 := bstep (se 2 (by rfl) ⟨535272, by rfl⟩ : syracuseStep 1427393 = 1070545) B1070545
theorem B1427411 : Blo 948586 1427411 := bstep (se 1 (by rfl) ⟨1070558, by rfl⟩ : syracuseStep 1427411 = 2141117) B2141117
theorem B1427441 : Blo 948586 1427441 := bstep (se 2 (by rfl) ⟨535290, by rfl⟩ : syracuseStep 1427441 = 1070581) B1070581
theorem B1427459 : Blo 948586 1427459 := bstep (se 1 (by rfl) ⟨1070594, by rfl⟩ : syracuseStep 1427459 = 2141189) B2141189
theorem B2410499 : Blo 948586 2410499 := bstep (se 1 (by rfl) ⟨1807874, by rfl⟩ : syracuseStep 2410499 = 3615749) B3615749
theorem B1427489 : Blo 948586 1427489 := bstep (se 2 (by rfl) ⟨535308, by rfl⟩ : syracuseStep 1427489 = 1070617) B1070617
theorem B1427507 : Blo 948586 1427507 := bstep (se 1 (by rfl) ⟨1070630, by rfl⟩ : syracuseStep 1427507 = 2141261) B2141261
theorem B1427537 : Blo 948586 1427537 := bstep (se 2 (by rfl) ⟨535326, by rfl⟩ : syracuseStep 1427537 = 1070653) B1070653
theorem B1427555 : Blo 948586 1427555 := bstep (se 1 (by rfl) ⟨1070666, by rfl⟩ : syracuseStep 1427555 = 2141333) B2141333
theorem B1427585 : Blo 948586 1427585 := bstep (se 2 (by rfl) ⟨535344, by rfl⟩ : syracuseStep 1427585 = 1070689) B1070689
theorem B1427603 : Blo 948586 1427603 := bstep (se 1 (by rfl) ⟨1070702, by rfl⟩ : syracuseStep 1427603 = 2141405) B2141405
theorem B1427633 : Blo 948586 1427633 := bstep (se 2 (by rfl) ⟨535362, by rfl⟩ : syracuseStep 1427633 = 1070725) B1070725
theorem B1427651 : Blo 948586 1427651 := bstep (se 1 (by rfl) ⟨1070738, by rfl⟩ : syracuseStep 1427651 = 2141477) B2141477
theorem B1427681 : Blo 948586 1427681 := bstep (se 2 (by rfl) ⟨535380, by rfl⟩ : syracuseStep 1427681 = 1070761) B1070761
theorem B1067251 : Blo 948586 1067251 := bstep (se 1 (by rfl) ⟨800438, by rfl⟩ : syracuseStep 1067251 = 1600877) B1600877
theorem B1427699 : Blo 948586 1427699 := bstep (se 1 (by rfl) ⟨1070774, by rfl⟩ : syracuseStep 1427699 = 2141549) B2141549
theorem B1427729 : Blo 948586 1427729 := bstep (se 2 (by rfl) ⟨535398, by rfl⟩ : syracuseStep 1427729 = 1070797) B1070797
theorem B1427747 : Blo 948586 1427747 := bstep (se 1 (by rfl) ⟨1070810, by rfl⟩ : syracuseStep 1427747 = 2141621) B2141621
theorem B1624369 : Blo 948586 1624369 := bstep (se 2 (by rfl) ⟨609138, by rfl⟩ : syracuseStep 1624369 = 1218277) B1218277
theorem B1427777 : Blo 948586 1427777 := bstep (se 2 (by rfl) ⟨535416, by rfl⟩ : syracuseStep 1427777 = 1070833) B1070833
theorem B1427795 : Blo 948586 1427795 := bstep (se 1 (by rfl) ⟨1070846, by rfl⟩ : syracuseStep 1427795 = 2141693) B2141693
theorem B1427825 : Blo 948586 1427825 := bstep (se 2 (by rfl) ⟨535434, by rfl⟩ : syracuseStep 1427825 = 1070869) B1070869
theorem B1067395 : Blo 948586 1067395 := bstep (se 1 (by rfl) ⟨800546, by rfl⟩ : syracuseStep 1067395 = 1601093) B1601093
theorem B1427843 : Blo 948586 1427843 := bstep (se 1 (by rfl) ⟨1070882, by rfl⟩ : syracuseStep 1427843 = 2141765) B2141765
theorem B1427873 : Blo 948586 1427873 := bstep (se 2 (by rfl) ⟨535452, by rfl⟩ : syracuseStep 1427873 = 1070905) B1070905
theorem B1427891 : Blo 948586 1427891 := bstep (se 1 (by rfl) ⟨1070918, by rfl⟩ : syracuseStep 1427891 = 2141837) B2141837
theorem B1427921 : Blo 948586 1427921 := bstep (se 2 (by rfl) ⟨535470, by rfl⟩ : syracuseStep 1427921 = 1070941) B1070941
theorem B1427939 : Blo 948586 1427939 := bstep (se 1 (by rfl) ⟨1070954, by rfl⟩ : syracuseStep 1427939 = 2141909) B2141909
theorem B1427969 : Blo 948586 1427969 := bstep (se 2 (by rfl) ⟨535488, by rfl⟩ : syracuseStep 1427969 = 1070977) B1070977
theorem B1067539 : Blo 948586 1067539 := bstep (se 1 (by rfl) ⟨800654, by rfl⟩ : syracuseStep 1067539 = 1601309) B1601309
theorem B1427987 : Blo 948586 1427987 := bstep (se 1 (by rfl) ⟨1070990, by rfl⟩ : syracuseStep 1427987 = 2141981) B2141981
theorem B1428017 : Blo 948586 1428017 := bstep (se 2 (by rfl) ⟨535506, by rfl⟩ : syracuseStep 1428017 = 1071013) B1071013
theorem B1428035 : Blo 948586 1428035 := bstep (se 1 (by rfl) ⟨1071026, by rfl⟩ : syracuseStep 1428035 = 2142053) B2142053
theorem B1428065 : Blo 948586 1428065 := bstep (se 2 (by rfl) ⟨535524, by rfl⟩ : syracuseStep 1428065 = 1071049) B1071049
theorem B3656305 : Blo 948586 3656305 := bstep (se 2 (by rfl) ⟨1371114, by rfl⟩ : syracuseStep 3656305 = 2742229) B2742229
theorem B1428083 : Blo 948586 1428083 := bstep (se 1 (by rfl) ⟨1071062, by rfl⟩ : syracuseStep 1428083 = 2142125) B2142125
theorem B4573837 : Blo 948586 4573837 := bstep (se 3 (by rfl) ⟨857594, by rfl⟩ : syracuseStep 4573837 = 1715189) B1715189
theorem B1428113 : Blo 948586 1428113 := bstep (se 2 (by rfl) ⟨535542, by rfl⟩ : syracuseStep 1428113 = 1071085) B1071085
theorem B1067683 : Blo 948586 1067683 := bstep (se 1 (by rfl) ⟨800762, by rfl⟩ : syracuseStep 1067683 = 1601525) B1601525
theorem B1428131 : Blo 948586 1428131 := bstep (se 1 (by rfl) ⟨1071098, by rfl⟩ : syracuseStep 1428131 = 2142197) B2142197
theorem B1428161 : Blo 948586 1428161 := bstep (se 2 (by rfl) ⟨535560, by rfl⟩ : syracuseStep 1428161 = 1071121) B1071121
theorem B2280145 : Blo 948586 2280145 := bstep (se 2 (by rfl) ⟨855054, by rfl⟩ : syracuseStep 2280145 = 1710109) B1710109
theorem B1428179 : Blo 948586 1428179 := bstep (se 1 (by rfl) ⟨1071134, by rfl⟩ : syracuseStep 1428179 = 2142269) B2142269
theorem B4803299 : Blo 948586 4803299 := bstep (se 1 (by rfl) ⟨3602474, by rfl⟩ : syracuseStep 4803299 = 7204949) B7204949
theorem B1428209 : Blo 948586 1428209 := bstep (se 2 (by rfl) ⟨535578, by rfl⟩ : syracuseStep 1428209 = 1071157) B1071157
theorem B1100531 : Blo 948586 1100531 := bstep (se 1 (by rfl) ⟨825398, by rfl⟩ : syracuseStep 1100531 = 1650797) B1650797
theorem B1428227 : Blo 948586 1428227 := bstep (se 1 (by rfl) ⟨1071170, by rfl⟩ : syracuseStep 1428227 = 2142341) B2142341
theorem B1428257 : Blo 948586 1428257 := bstep (se 2 (by rfl) ⟨535596, by rfl⟩ : syracuseStep 1428257 = 1071193) B1071193
theorem B1067827 : Blo 948586 1067827 := bstep (se 1 (by rfl) ⟨800870, by rfl⟩ : syracuseStep 1067827 = 1601741) B1601741
theorem B1428275 : Blo 948586 1428275 := bstep (se 1 (by rfl) ⟨1071206, by rfl⟩ : syracuseStep 1428275 = 2142413) B2142413
theorem B1428305 : Blo 948586 1428305 := bstep (se 2 (by rfl) ⟨535614, by rfl⟩ : syracuseStep 1428305 = 1071229) B1071229
theorem B1428323 : Blo 948586 1428323 := bstep (se 1 (by rfl) ⟨1071242, by rfl⟩ : syracuseStep 1428323 = 2142485) B2142485
theorem B1428353 : Blo 948586 1428353 := bstep (se 2 (by rfl) ⟨535632, by rfl⟩ : syracuseStep 1428353 = 1071265) B1071265
theorem B1428371 : Blo 948586 1428371 := bstep (se 1 (by rfl) ⟨1071278, by rfl⟩ : syracuseStep 1428371 = 2142557) B2142557
theorem B1428401 : Blo 948586 1428401 := bstep (se 2 (by rfl) ⟨535650, by rfl⟩ : syracuseStep 1428401 = 1071301) B1071301
theorem B1067971 : Blo 948586 1067971 := bstep (se 1 (by rfl) ⟨800978, by rfl⟩ : syracuseStep 1067971 = 1601957) B1601957
theorem B1428419 : Blo 948586 1428419 := bstep (se 1 (by rfl) ⟨1071314, by rfl⟩ : syracuseStep 1428419 = 2142629) B2142629
theorem B1428449 : Blo 948586 1428449 := bstep (se 2 (by rfl) ⟨535668, by rfl⟩ : syracuseStep 1428449 = 1071337) B1071337
theorem B1428467 : Blo 948586 1428467 := bstep (se 1 (by rfl) ⟨1071350, by rfl⟩ : syracuseStep 1428467 = 2142701) B2142701
theorem B1428497 : Blo 948586 1428497 := bstep (se 2 (by rfl) ⟨535686, by rfl⟩ : syracuseStep 1428497 = 1071373) B1071373
theorem B1428515 : Blo 948586 1428515 := bstep (se 1 (by rfl) ⟨1071386, by rfl⟩ : syracuseStep 1428515 = 2142773) B2142773
theorem B1428545 : Blo 948586 1428545 := bstep (se 2 (by rfl) ⟨535704, by rfl⟩ : syracuseStep 1428545 = 1071409) B1071409
theorem B1068115 : Blo 948586 1068115 := bstep (se 1 (by rfl) ⟨801086, by rfl⟩ : syracuseStep 1068115 = 1602173) B1602173
theorem B1428563 : Blo 948586 1428563 := bstep (se 1 (by rfl) ⟨1071422, by rfl⟩ : syracuseStep 1428563 = 2142845) B2142845
theorem B1428593 : Blo 948586 1428593 := bstep (se 2 (by rfl) ⟨535722, by rfl⟩ : syracuseStep 1428593 = 1071445) B1071445
theorem B1428611 : Blo 948586 1428611 := bstep (se 1 (by rfl) ⟨1071458, by rfl⟩ : syracuseStep 1428611 = 2142917) B2142917
theorem B1428641 : Blo 948586 1428641 := bstep (se 2 (by rfl) ⟨535740, by rfl⟩ : syracuseStep 1428641 = 1071481) B1071481
theorem B1428659 : Blo 948586 1428659 := bstep (se 1 (by rfl) ⟨1071494, by rfl⟩ : syracuseStep 1428659 = 2142989) B2142989
theorem B2706641 : Blo 948586 2706641 := bstep (se 2 (by rfl) ⟨1014990, by rfl⟩ : syracuseStep 2706641 = 2029981) B2029981
theorem B1428689 : Blo 948586 1428689 := bstep (se 2 (by rfl) ⟨535758, by rfl⟩ : syracuseStep 1428689 = 1071517) B1071517
theorem B1068259 : Blo 948586 1068259 := bstep (se 1 (by rfl) ⟨801194, by rfl⟩ : syracuseStep 1068259 = 1602389) B1602389
theorem B1428707 : Blo 948586 1428707 := bstep (se 1 (by rfl) ⟨1071530, by rfl⟩ : syracuseStep 1428707 = 2143061) B2143061
theorem B1428737 : Blo 948586 1428737 := bstep (se 2 (by rfl) ⟨535776, by rfl⟩ : syracuseStep 1428737 = 1071553) B1071553
theorem B1428755 : Blo 948586 1428755 := bstep (se 1 (by rfl) ⟨1071566, by rfl⟩ : syracuseStep 1428755 = 2143133) B2143133
theorem B1428785 : Blo 948586 1428785 := bstep (se 2 (by rfl) ⟨535794, by rfl⟩ : syracuseStep 1428785 = 1071589) B1071589
theorem B1428803 : Blo 948586 1428803 := bstep (se 1 (by rfl) ⟨1071602, by rfl⟩ : syracuseStep 1428803 = 2143205) B2143205
theorem B1428833 : Blo 948586 1428833 := bstep (se 2 (by rfl) ⟨535812, by rfl⟩ : syracuseStep 1428833 = 1071625) B1071625
theorem B1068403 : Blo 948586 1068403 := bstep (se 1 (by rfl) ⟨801302, by rfl⟩ : syracuseStep 1068403 = 1602605) B1602605
theorem B1428851 : Blo 948586 1428851 := bstep (se 1 (by rfl) ⟨1071638, by rfl⟩ : syracuseStep 1428851 = 2143277) B2143277
theorem B1068547 : Blo 948586 1068547 := bstep (se 1 (by rfl) ⟨801410, by rfl⟩ : syracuseStep 1068547 = 1602821) B1602821
theorem B4804109 : Blo 948586 4804109 := bstep (se 3 (by rfl) ⟨900770, by rfl⟩ : syracuseStep 4804109 = 1801541) B1801541
theorem B1068691 : Blo 948586 1068691 := bstep (se 1 (by rfl) ⟨801518, by rfl⟩ : syracuseStep 1068691 = 1603037) B1603037
theorem B6082253 : Blo 948586 6082253 := bstep (se 3 (by rfl) ⟨1140422, by rfl⟩ : syracuseStep 6082253 = 2280845) B2280845
theorem B46157525 : Blo 948586 46157525 := bstep (se 7 (by rfl) ⟨540908, by rfl⟩ : syracuseStep 46157525 = 1081817) B1081817
theorem B1068835 : Blo 948586 1068835 := bstep (se 1 (by rfl) ⟨801626, by rfl⟩ : syracuseStep 1068835 = 1603253) B1603253
theorem B1068979 : Blo 948586 1068979 := bstep (se 1 (by rfl) ⟨801734, by rfl⟩ : syracuseStep 1068979 = 1603469) B1603469
theorem B1069123 : Blo 948586 1069123 := bstep (se 1 (by rfl) ⟨801842, by rfl⟩ : syracuseStep 1069123 = 1603685) B1603685
theorem B2707597 : Blo 948586 2707597 := bstep (se 3 (by rfl) ⟨507674, by rfl⟩ : syracuseStep 2707597 = 1015349) B1015349
theorem B2642129 : Blo 948586 2642129 := bstep (se 2 (by rfl) ⟨990798, by rfl⟩ : syracuseStep 2642129 = 1981597) B1981597
theorem B1069267 : Blo 948586 1069267 := bstep (se 1 (by rfl) ⟨801950, by rfl⟩ : syracuseStep 1069267 = 1603901) B1603901
theorem B5132593 : Blo 948586 5132593 := bstep (se 2 (by rfl) ⟨1924722, by rfl⟩ : syracuseStep 5132593 = 3849445) B3849445
theorem B1069411 : Blo 948586 1069411 := bstep (se 1 (by rfl) ⟨802058, by rfl⟩ : syracuseStep 1069411 = 1604117) B1604117
theorem B2707825 : Blo 948586 2707825 := bstep (se 2 (by rfl) ⟨1015434, by rfl⟩ : syracuseStep 2707825 = 2030869) B2030869
theorem B1069555 : Blo 948586 1069555 := bstep (se 1 (by rfl) ⟨802166, by rfl⟩ : syracuseStep 1069555 = 1604333) B1604333
theorem B2707985 : Blo 948586 2707985 := bstep (se 2 (by rfl) ⟨1015494, by rfl⟩ : syracuseStep 2707985 = 2030989) B2030989
theorem B3854897 : Blo 948586 3854897 := bstep (se 2 (by rfl) ⟨1445586, by rfl⟩ : syracuseStep 3854897 = 2891173) B2891173
theorem B1200739 : Blo 948586 1200739 := bstep (se 1 (by rfl) ⟨900554, by rfl⟩ : syracuseStep 1200739 = 1801109) B1801109
theorem B2740835 : Blo 948586 2740835 := bstep (se 1 (by rfl) ⟨2055626, by rfl⟩ : syracuseStep 2740835 = 4111253) B4111253
theorem B1069699 : Blo 948586 1069699 := bstep (se 1 (by rfl) ⟨802274, by rfl⟩ : syracuseStep 1069699 = 1604549) B1604549
theorem B2708099 : Blo 948586 2708099 := bstep (se 1 (by rfl) ⟨2031074, by rfl⟩ : syracuseStep 2708099 = 4062149) B4062149
theorem B1200835 : Blo 948586 1200835 := bstep (se 1 (by rfl) ⟨900626, by rfl⟩ : syracuseStep 1200835 = 1801253) B1801253
theorem B10277603 : Blo 948586 10277603 := bstep (se 1 (by rfl) ⟨7708202, by rfl⟩ : syracuseStep 10277603 = 15416405) B15416405
theorem B7230221 : Blo 948586 7230221 := bstep (se 3 (by rfl) ⟨1355666, by rfl⟩ : syracuseStep 7230221 = 2711333) B2711333
theorem B1069843 : Blo 948586 1069843 := bstep (se 1 (by rfl) ⟨802382, by rfl⟩ : syracuseStep 1069843 = 1604765) B1604765
theorem B1069987 : Blo 948586 1069987 := bstep (se 1 (by rfl) ⟨802490, by rfl⟩ : syracuseStep 1069987 = 1604981) B1604981
theorem B1463251 : Blo 948586 1463251 := bstep (se 1 (by rfl) ⟨1097438, by rfl⟩ : syracuseStep 1463251 = 2194877) B2194877
theorem B1070131 : Blo 948586 1070131 := bstep (se 1 (by rfl) ⟨802598, by rfl⟩ : syracuseStep 1070131 = 1605197) B1605197
theorem B1201331 : Blo 948586 1201331 := bstep (se 1 (by rfl) ⟨900998, by rfl⟩ : syracuseStep 1201331 = 1801997) B1801997
theorem B1070275 : Blo 948586 1070275 := bstep (se 1 (by rfl) ⟨802706, by rfl⟩ : syracuseStep 1070275 = 1605413) B1605413
theorem B1070419 : Blo 948586 1070419 := bstep (se 1 (by rfl) ⟨802814, by rfl⟩ : syracuseStep 1070419 = 1605629) B1605629
theorem B1627489 : Blo 948586 1627489 := bstep (se 2 (by rfl) ⟨610308, by rfl⟩ : syracuseStep 1627489 = 1220617) B1220617
theorem B1070563 : Blo 948586 1070563 := bstep (se 1 (by rfl) ⟨802922, by rfl⟩ : syracuseStep 1070563 = 1605845) B1605845
theorem B2741795 : Blo 948586 2741795 := bstep (se 1 (by rfl) ⟨2056346, by rfl⟩ : syracuseStep 2741795 = 4112693) B4112693
theorem B2709101 : Blo 948586 2709101 := bstep (se 3 (by rfl) ⟨507956, by rfl⟩ : syracuseStep 2709101 = 1015913) B1015913
theorem B1070707 : Blo 948586 1070707 := bstep (se 1 (by rfl) ⟨803030, by rfl⟩ : syracuseStep 1070707 = 1606061) B1606061
theorem B1070851 : Blo 948586 1070851 := bstep (se 1 (by rfl) ⟨803138, by rfl⟩ : syracuseStep 1070851 = 1606277) B1606277
theorem B2709283 : Blo 948586 2709283 := bstep (se 1 (by rfl) ⟨2031962, by rfl⟩ : syracuseStep 2709283 = 4063925) B4063925
theorem B3856177 : Blo 948586 3856177 := bstep (se 2 (by rfl) ⟨1446066, by rfl⟩ : syracuseStep 3856177 = 2892133) B2892133
theorem B6510449 : Blo 948586 6510449 := bstep (se 2 (by rfl) ⟨2441418, by rfl⟩ : syracuseStep 6510449 = 4882837) B4882837
theorem B1202035 : Blo 948586 1202035 := bstep (se 1 (by rfl) ⟨901526, by rfl⟩ : syracuseStep 1202035 = 1803053) B1803053
theorem B1070995 : Blo 948586 1070995 := bstep (se 1 (by rfl) ⟨803246, by rfl⟩ : syracuseStep 1070995 = 1606493) B1606493
theorem B2709443 : Blo 948586 2709443 := bstep (se 1 (by rfl) ⟨2032082, by rfl⟩ : syracuseStep 2709443 = 4064165) B4064165
theorem B1202131 : Blo 948586 1202131 := bstep (se 1 (by rfl) ⟨901598, by rfl⟩ : syracuseStep 1202131 = 1803197) B1803197
theorem B1071139 : Blo 948586 1071139 := bstep (se 1 (by rfl) ⟨803354, by rfl⟩ : syracuseStep 1071139 = 1606709) B1606709
theorem B1071283 : Blo 948586 1071283 := bstep (se 1 (by rfl) ⟨803462, by rfl⟩ : syracuseStep 1071283 = 1606925) B1606925
theorem B16275653 : Blo 948586 16275653 := bstep (se 4 (by rfl) ⟨1525842, by rfl⟩ : syracuseStep 16275653 = 3051685) B3051685
theorem B2644177 : Blo 948586 2644177 := bstep (se 2 (by rfl) ⟨991566, by rfl⟩ : syracuseStep 2644177 = 1983133) B1983133
theorem B6838499 : Blo 948586 6838499 := bstep (se 1 (by rfl) ⟨5128874, by rfl⟩ : syracuseStep 6838499 = 10257749) B10257749
theorem B1071427 : Blo 948586 1071427 := bstep (se 1 (by rfl) ⟨803570, by rfl⟩ : syracuseStep 1071427 = 1607141) B1607141
theorem B4807025 : Blo 948586 4807025 := bstep (se 2 (by rfl) ⟨1802634, by rfl⟩ : syracuseStep 4807025 = 3605269) B3605269
theorem B1202627 : Blo 948586 1202627 := bstep (se 1 (by rfl) ⟨901970, by rfl⟩ : syracuseStep 1202627 = 1803941) B1803941
theorem B1071571 : Blo 948586 1071571 := bstep (se 1 (by rfl) ⟨803678, by rfl⟩ : syracuseStep 1071571 = 1607357) B1607357
theorem B1628707 : Blo 948586 1628707 := bstep (se 1 (by rfl) ⟨1221530, by rfl⟩ : syracuseStep 1628707 = 2443061) B2443061
theorem B3201713 : Blo 948586 3201713 := bstep (se 2 (by rfl) ⟨1200642, by rfl⟩ : syracuseStep 3201713 = 2401285) B2401285
theorem B1235731 : Blo 948586 1235731 := bstep (se 1 (by rfl) ⟨926798, by rfl⟩ : syracuseStep 1235731 = 1853597) B1853597
theorem B12180293 : Blo 948586 12180293 := bstep (se 4 (by rfl) ⟨1141902, by rfl⟩ : syracuseStep 12180293 = 2283805) B2283805
theorem B2710513 : Blo 948586 2710513 := bstep (se 2 (by rfl) ⟨1016442, by rfl⟩ : syracuseStep 2710513 = 2032885) B2032885
theorem B6085637 : Blo 948586 6085637 := bstep (se 4 (by rfl) ⟨570528, by rfl⟩ : syracuseStep 6085637 = 1141057) B1141057
theorem B1203331 : Blo 948586 1203331 := bstep (se 1 (by rfl) ⟨902498, by rfl⟩ : syracuseStep 1203331 = 1804997) B1804997
theorem B1301665 : Blo 948586 1301665 := bstep (se 2 (by rfl) ⟨488124, by rfl⟩ : syracuseStep 1301665 = 976249) B976249
theorem B1629377 : Blo 948586 1629377 := bstep (se 2 (by rfl) ⟨611016, by rfl⟩ : syracuseStep 1629377 = 1222033) B1222033
theorem B14277829 : Blo 948586 14277829 := bstep (se 4 (by rfl) ⟨1338546, by rfl⟩ : syracuseStep 14277829 = 2677093) B2677093
theorem B3202253 : Blo 948586 3202253 := bstep (se 3 (by rfl) ⟨600422, by rfl⟩ : syracuseStep 3202253 = 1200845) B1200845
theorem B1203427 : Blo 948586 1203427 := bstep (se 1 (by rfl) ⟨902570, by rfl⟩ : syracuseStep 1203427 = 1805141) B1805141
theorem B3202307 : Blo 948586 3202307 := bstep (se 1 (by rfl) ⟨2401730, by rfl⟩ : syracuseStep 3202307 = 4803461) B4803461
theorem B3202577 : Blo 948586 3202577 := bstep (se 2 (by rfl) ⟨1200966, by rfl⟩ : syracuseStep 3202577 = 2401933) B2401933
theorem B7233137 : Blo 948586 7233137 := bstep (se 2 (by rfl) ⟨2712426, by rfl⟩ : syracuseStep 7233137 = 5424853) B5424853
theorem B1203923 : Blo 948586 1203923 := bstep (se 1 (by rfl) ⟨902942, by rfl⟩ : syracuseStep 1203923 = 1805885) B1805885
theorem B2285297 : Blo 948586 2285297 := bstep (se 2 (by rfl) ⟨856986, by rfl⟩ : syracuseStep 2285297 = 1713973) B1713973
theorem B4054819 : Blo 948586 4054819 := bstep (se 1 (by rfl) ⟨3041114, by rfl⟩ : syracuseStep 4054819 = 6082229) B6082229
theorem B4808483 : Blo 948586 4808483 := bstep (se 1 (by rfl) ⟨3606362, by rfl⟩ : syracuseStep 4808483 = 7212725) B7212725
theorem B3203117 : Blo 948586 3203117 := bstep (se 3 (by rfl) ⟨600584, by rfl⟩ : syracuseStep 3203117 = 1201169) B1201169
theorem B3203171 : Blo 948586 3203171 := bstep (se 1 (by rfl) ⟨2402378, by rfl⟩ : syracuseStep 3203171 = 4804757) B4804757
theorem B9396323 : Blo 948586 9396323 := bstep (se 1 (by rfl) ⟨7047242, by rfl⟩ : syracuseStep 9396323 = 14094485) B14094485
theorem B5791877 : Blo 948586 5791877 := bstep (se 4 (by rfl) ⟨542988, by rfl⟩ : syracuseStep 5791877 = 1085977) B1085977
theorem B2711789 : Blo 948586 2711789 := bstep (se 3 (by rfl) ⟨508460, by rfl⟩ : syracuseStep 2711789 = 1016921) B1016921
theorem B3858787 : Blo 948586 3858787 := bstep (se 1 (by rfl) ⟨2894090, by rfl⟩ : syracuseStep 3858787 = 5788181) B5788181
theorem B3203441 : Blo 948586 3203441 := bstep (se 2 (by rfl) ⟨1201290, by rfl⟩ : syracuseStep 3203441 = 2402581) B2402581
theorem B1204627 : Blo 948586 1204627 := bstep (se 1 (by rfl) ⟨903470, by rfl⟩ : syracuseStep 1204627 = 1806941) B1806941
theorem B2711971 : Blo 948586 2711971 := bstep (se 1 (by rfl) ⟨2033978, by rfl⟩ : syracuseStep 2711971 = 4067957) B4067957
theorem B2712017 : Blo 948586 2712017 := bstep (se 2 (by rfl) ⟨1017006, by rfl⟩ : syracuseStep 2712017 = 2034013) B2034013
theorem B2286065 : Blo 948586 2286065 := bstep (se 2 (by rfl) ⟨857274, by rfl⟩ : syracuseStep 2286065 = 1714549) B1714549
theorem B1204723 : Blo 948586 1204723 := bstep (se 1 (by rfl) ⟨903542, by rfl⟩ : syracuseStep 1204723 = 1807085) B1807085
theorem B4809293 : Blo 948586 4809293 := bstep (se 3 (by rfl) ⟨901742, by rfl⟩ : syracuseStep 4809293 = 1803485) B1803485
theorem B3203981 : Blo 948586 3203981 := bstep (se 3 (by rfl) ⟨600746, by rfl⟩ : syracuseStep 3203981 = 1201493) B1201493
theorem B3204035 : Blo 948586 3204035 := bstep (se 1 (by rfl) ⟨2403026, by rfl⟩ : syracuseStep 3204035 = 4806053) B4806053
theorem B8119237 : Blo 948586 8119237 := bstep (se 4 (by rfl) ⟨761178, by rfl⟩ : syracuseStep 8119237 = 1522357) B1522357
theorem B1205219 : Blo 948586 1205219 := bstep (se 1 (by rfl) ⟨903914, by rfl⟩ : syracuseStep 1205219 = 1807829) B1807829
theorem B1139827 : Blo 948586 1139827 := bstep (se 1 (by rfl) ⟨854870, by rfl⟩ : syracuseStep 1139827 = 1709741) B1709741
theorem B1041523 : Blo 948586 1041523 := bstep (se 1 (by rfl) ⟨781142, by rfl⟩ : syracuseStep 1041523 = 1562285) B1562285
theorem B5137613 : Blo 948586 5137613 := bstep (se 3 (by rfl) ⟨963302, by rfl⟩ : syracuseStep 5137613 = 1926605) B1926605
theorem B3204305 : Blo 948586 3204305 := bstep (se 2 (by rfl) ⟨1201614, by rfl⟩ : syracuseStep 3204305 = 2403229) B2403229
theorem B3859825 : Blo 948586 3859825 := bstep (se 2 (by rfl) ⟨1447434, by rfl⟩ : syracuseStep 3859825 = 2894869) B2894869
theorem B2319779 : Blo 948586 2319779 := bstep (se 1 (by rfl) ⟨1739834, by rfl⟩ : syracuseStep 2319779 = 3479669) B3479669
theorem B1140307 : Blo 948586 1140307 := bstep (se 1 (by rfl) ⟨855230, by rfl⟩ : syracuseStep 1140307 = 1710461) B1710461
theorem B1173187 : Blo 948586 1173187 := bstep (se 1 (by rfl) ⟨879890, by rfl⟩ : syracuseStep 1173187 = 1759781) B1759781
theorem B3040973 : Blo 948586 3040973 := bstep (se 3 (by rfl) ⟨570182, by rfl⟩ : syracuseStep 3040973 = 1140365) B1140365
theorem B3204845 : Blo 948586 3204845 := bstep (se 3 (by rfl) ⟨600908, by rfl⟩ : syracuseStep 3204845 = 1201817) B1201817
theorem B4056817 : Blo 948586 4056817 := bstep (se 2 (by rfl) ⟨1521306, by rfl⟩ : syracuseStep 4056817 = 3042613) B3042613
theorem B3204899 : Blo 948586 3204899 := bstep (se 1 (by rfl) ⟨2403674, by rfl⟩ : syracuseStep 3204899 = 4807349) B4807349
theorem B3205169 : Blo 948586 3205169 := bstep (se 2 (by rfl) ⟨1201938, by rfl⟩ : syracuseStep 3205169 = 2403877) B2403877
theorem B2287939 : Blo 948586 2287939 := bstep (se 1 (by rfl) ⟨1715954, by rfl⟩ : syracuseStep 2287939 = 3431909) B3431909
theorem B1141187 : Blo 948586 1141187 := bstep (se 1 (by rfl) ⟨855890, by rfl⟩ : syracuseStep 1141187 = 1711781) B1711781
theorem B6089201 : Blo 948586 6089201 := bstep (se 2 (by rfl) ⟨2283450, by rfl⟩ : syracuseStep 6089201 = 4566901) B4566901
theorem B3205709 : Blo 948586 3205709 := bstep (se 3 (by rfl) ⟨601070, by rfl⟩ : syracuseStep 3205709 = 1202141) B1202141
theorem B3205763 : Blo 948586 3205763 := bstep (se 1 (by rfl) ⟨2404322, by rfl⟩ : syracuseStep 3205763 = 4808645) B4808645
theorem B3206033 : Blo 948586 3206033 := bstep (se 2 (by rfl) ⟨1202262, by rfl⟩ : syracuseStep 3206033 = 2404525) B2404525
theorem B1600769 : Blo 948586 1600769 := bstep (se 2 (by rfl) ⟨600288, by rfl⟩ : syracuseStep 1600769 = 1200577) B1200577
theorem B13200653 : Blo 948586 13200653 := bstep (se 3 (by rfl) ⟨2475122, by rfl⟩ : syracuseStep 13200653 = 4950245) B4950245
theorem B1600897 : Blo 948586 1600897 := bstep (se 2 (by rfl) ⟨600336, by rfl⟩ : syracuseStep 1600897 = 1200673) B1200673
theorem B1600931 : Blo 948586 1600931 := bstep (se 1 (by rfl) ⟨1200698, by rfl⟩ : syracuseStep 1600931 = 2401397) B2401397
theorem B3206573 : Blo 948586 3206573 := bstep (se 3 (by rfl) ⟨601232, by rfl⟩ : syracuseStep 3206573 = 1202465) B1202465
theorem B4812209 : Blo 948586 4812209 := bstep (se 2 (by rfl) ⟨1804578, by rfl⟩ : syracuseStep 4812209 = 3609157) B3609157
theorem B3042755 : Blo 948586 3042755 := bstep (se 1 (by rfl) ⟨2282066, by rfl⟩ : syracuseStep 3042755 = 4564133) B4564133
theorem B3206627 : Blo 948586 3206627 := bstep (se 1 (by rfl) ⟨2404970, by rfl⟩ : syracuseStep 3206627 = 4809941) B4809941
theorem B1601059 : Blo 948586 1601059 := bstep (se 1 (by rfl) ⟨1200794, by rfl⟩ : syracuseStep 1601059 = 2401589) B2401589
theorem B1601201 : Blo 948586 1601201 := bstep (se 2 (by rfl) ⟨600450, by rfl⟩ : syracuseStep 1601201 = 1200901) B1200901
theorem B6942449 : Blo 948586 6942449 := bstep (se 2 (by rfl) ⟨2603418, by rfl⟩ : syracuseStep 6942449 = 5206837) B5206837
theorem B3206897 : Blo 948586 3206897 := bstep (se 2 (by rfl) ⟨1202586, by rfl⟩ : syracuseStep 3206897 = 2405173) B2405173
theorem B2027281 : Blo 948586 2027281 := bstep (se 2 (by rfl) ⟨760230, by rfl⟩ : syracuseStep 2027281 = 1520461) B1520461
theorem B1601329 : Blo 948586 1601329 := bstep (se 2 (by rfl) ⟨600498, by rfl⟩ : syracuseStep 1601329 = 1200997) B1200997
theorem B1601363 : Blo 948586 1601363 := bstep (se 1 (by rfl) ⟨1201022, by rfl⟩ : syracuseStep 1601363 = 2402045) B2402045
theorem B6090659 : Blo 948586 6090659 := bstep (se 1 (by rfl) ⟨4567994, by rfl⟩ : syracuseStep 6090659 = 9135989) B9135989
theorem B1601491 : Blo 948586 1601491 := bstep (se 1 (by rfl) ⟨1201118, by rfl⟩ : syracuseStep 1601491 = 2402237) B2402237
theorem B1601633 : Blo 948586 1601633 := bstep (se 2 (by rfl) ⟨600612, by rfl⟩ : syracuseStep 1601633 = 1201225) B1201225
theorem B2027683 : Blo 948586 2027683 := bstep (se 1 (by rfl) ⟨1520762, by rfl⟩ : syracuseStep 2027683 = 3041525) B3041525
theorem B5402801 : Blo 948586 5402801 := bstep (se 2 (by rfl) ⟨2026050, by rfl⟩ : syracuseStep 5402801 = 4052101) B4052101
theorem B1601761 : Blo 948586 1601761 := bstep (se 2 (by rfl) ⟨600660, by rfl⟩ : syracuseStep 1601761 = 1201321) B1201321
theorem B1601795 : Blo 948586 1601795 := bstep (se 1 (by rfl) ⟨1201346, by rfl⟩ : syracuseStep 1601795 = 2402693) B2402693
theorem B3207437 : Blo 948586 3207437 := bstep (se 3 (by rfl) ⟨601394, by rfl⟩ : syracuseStep 3207437 = 1202789) B1202789
theorem B3207491 : Blo 948586 3207491 := bstep (se 1 (by rfl) ⟨2405618, by rfl⟩ : syracuseStep 3207491 = 4811237) B4811237
theorem B2060657 : Blo 948586 2060657 := bstep (se 2 (by rfl) ⟨772746, by rfl⟩ : syracuseStep 2060657 = 1545493) B1545493
theorem B1601923 : Blo 948586 1601923 := bstep (se 1 (by rfl) ⟨1201442, by rfl⟩ : syracuseStep 1601923 = 2402885) B2402885
theorem B1602065 : Blo 948586 1602065 := bstep (se 2 (by rfl) ⟨600774, by rfl⟩ : syracuseStep 1602065 = 1201549) B1201549
theorem B3207761 : Blo 948586 3207761 := bstep (se 2 (by rfl) ⟨1202910, by rfl⟩ : syracuseStep 3207761 = 2405821) B2405821
theorem B1602193 : Blo 948586 1602193 := bstep (se 2 (by rfl) ⟨600822, by rfl⟩ : syracuseStep 1602193 = 1201645) B1201645
theorem B1602227 : Blo 948586 1602227 := bstep (se 1 (by rfl) ⟨1201670, by rfl⟩ : syracuseStep 1602227 = 2403341) B2403341
theorem B3044099 : Blo 948586 3044099 := bstep (se 1 (by rfl) ⟨2283074, by rfl⟩ : syracuseStep 3044099 = 4566149) B4566149
theorem B1143571 : Blo 948586 1143571 := bstep (se 1 (by rfl) ⟨857678, by rfl⟩ : syracuseStep 1143571 = 1715357) B1715357
theorem B1602355 : Blo 948586 1602355 := bstep (se 1 (by rfl) ⟨1201766, by rfl⟩ : syracuseStep 1602355 = 2403533) B2403533
theorem B1373009 : Blo 948586 1373009 := bstep (se 2 (by rfl) ⟨514878, by rfl⟩ : syracuseStep 1373009 = 1029757) B1029757
theorem B4813667 : Blo 948586 4813667 := bstep (se 1 (by rfl) ⟨3610250, by rfl⟩ : syracuseStep 4813667 = 7220501) B7220501
theorem B1602497 : Blo 948586 1602497 := bstep (se 2 (by rfl) ⟨600936, by rfl⟩ : syracuseStep 1602497 = 1201873) B1201873
theorem B1602625 : Blo 948586 1602625 := bstep (se 2 (by rfl) ⟨600984, by rfl⟩ : syracuseStep 1602625 = 1201969) B1201969
theorem B1602659 : Blo 948586 1602659 := bstep (se 1 (by rfl) ⟨1201994, by rfl⟩ : syracuseStep 1602659 = 2403989) B2403989
theorem B3208301 : Blo 948586 3208301 := bstep (se 3 (by rfl) ⟨601556, by rfl⟩ : syracuseStep 3208301 = 1203113) B1203113
theorem B3208355 : Blo 948586 3208355 := bstep (se 1 (by rfl) ⟨2406266, by rfl⟩ : syracuseStep 3208355 = 4812533) B4812533
theorem B1602787 : Blo 948586 1602787 := bstep (se 1 (by rfl) ⟨1202090, by rfl⟩ : syracuseStep 1602787 = 2404181) B2404181
theorem B12711221 : Blo 948586 12711221 := bstep (se 5 (by rfl) ⟨595838, by rfl⟩ : syracuseStep 12711221 = 1191677) B1191677
theorem B1602929 : Blo 948586 1602929 := bstep (se 2 (by rfl) ⟨601098, by rfl⟩ : syracuseStep 1602929 = 1202197) B1202197
theorem B3208625 : Blo 948586 3208625 := bstep (se 2 (by rfl) ⟨1203234, by rfl⟩ : syracuseStep 3208625 = 2406469) B2406469
theorem B1603057 : Blo 948586 1603057 := bstep (se 2 (by rfl) ⟨601146, by rfl⟩ : syracuseStep 1603057 = 1202293) B1202293
theorem B1603091 : Blo 948586 1603091 := bstep (se 1 (by rfl) ⟨1202318, by rfl⟩ : syracuseStep 1603091 = 2404637) B2404637
theorem B5404259 : Blo 948586 5404259 := bstep (se 1 (by rfl) ⟨4053194, by rfl⟩ : syracuseStep 5404259 = 8106389) B8106389
theorem B2029187 : Blo 948586 2029187 := bstep (se 1 (by rfl) ⟨1521890, by rfl⟩ : syracuseStep 2029187 = 3043781) B3043781
theorem B4814477 : Blo 948586 4814477 := bstep (se 3 (by rfl) ⟨902714, by rfl⟩ : syracuseStep 4814477 = 1805429) B1805429
theorem B1603219 : Blo 948586 1603219 := bstep (se 1 (by rfl) ⟨1202414, by rfl⟩ : syracuseStep 1603219 = 2404829) B2404829
theorem B4060849 : Blo 948586 4060849 := bstep (se 2 (by rfl) ⟨1522818, by rfl⟩ : syracuseStep 4060849 = 3045637) B3045637
theorem B1603361 : Blo 948586 1603361 := bstep (se 2 (by rfl) ⟨601260, by rfl⟩ : syracuseStep 1603361 = 1202521) B1202521
theorem B1603489 : Blo 948586 1603489 := bstep (se 2 (by rfl) ⟨601308, by rfl⟩ : syracuseStep 1603489 = 1202617) B1202617
theorem B3602339 : Blo 948586 3602339 := bstep (se 1 (by rfl) ⟨2701754, by rfl⟩ : syracuseStep 3602339 = 5403509) B5403509
theorem B3602353 : Blo 948586 3602353 := bstep (se 2 (by rfl) ⟨1350882, by rfl⟩ : syracuseStep 3602353 = 2701765) B2701765
theorem B1603523 : Blo 948586 1603523 := bstep (se 1 (by rfl) ⟨1202642, by rfl⟩ : syracuseStep 1603523 = 2405285) B2405285
theorem B3209165 : Blo 948586 3209165 := bstep (se 3 (by rfl) ⟨601718, by rfl⟩ : syracuseStep 3209165 = 1203437) B1203437
theorem B3209219 : Blo 948586 3209219 := bstep (se 1 (by rfl) ⟨2406914, by rfl⟩ : syracuseStep 3209219 = 4813829) B4813829
theorem B1603651 : Blo 948586 1603651 := bstep (se 1 (by rfl) ⟨1202738, by rfl⟩ : syracuseStep 1603651 = 2405477) B2405477
theorem B9140293 : Blo 948586 9140293 := bstep (se 4 (by rfl) ⟨856902, by rfl⟩ : syracuseStep 9140293 = 1713805) B1713805
theorem B1603793 : Blo 948586 1603793 := bstep (se 2 (by rfl) ⟨601422, by rfl⟩ : syracuseStep 1603793 = 1202845) B1202845
theorem B3209489 : Blo 948586 3209489 := bstep (se 2 (by rfl) ⟨1203558, by rfl⟩ : syracuseStep 3209489 = 2407117) B2407117
theorem B1603921 : Blo 948586 1603921 := bstep (se 2 (by rfl) ⟨601470, by rfl⟩ : syracuseStep 1603921 = 1202941) B1202941
theorem B1014115 : Blo 948586 1014115 := bstep (se 1 (by rfl) ⟨760586, by rfl⟩ : syracuseStep 1014115 = 1521173) B1521173
theorem B948595 : Blo 948586 948595 := bstep (se 1 (by rfl) ⟨711446, by rfl⟩ : syracuseStep 948595 = 1422893) B1422893
theorem B1603955 : Blo 948586 1603955 := bstep (se 1 (by rfl) ⟨1202966, by rfl⟩ : syracuseStep 1603955 = 2405933) B2405933
theorem B948611 : Blo 948586 948611 := bstep (se 1 (by rfl) ⟨711458, by rfl⟩ : syracuseStep 948611 = 1422917) B1422917
theorem B948627 : Blo 948586 948627 := bstep (se 1 (by rfl) ⟨711470, by rfl⟩ : syracuseStep 948627 = 1422941) B1422941
theorem B948643 : Blo 948586 948643 := bstep (se 1 (by rfl) ⟨711482, by rfl⟩ : syracuseStep 948643 = 1422965) B1422965
theorem B948659 : Blo 948586 948659 := bstep (se 1 (by rfl) ⟨711494, by rfl⟩ : syracuseStep 948659 = 1422989) B1422989
theorem B948675 : Blo 948586 948675 := bstep (se 1 (by rfl) ⟨711506, by rfl⟩ : syracuseStep 948675 = 1423013) B1423013
theorem B948691 : Blo 948586 948691 := bstep (se 1 (by rfl) ⟨711518, by rfl⟩ : syracuseStep 948691 = 1423037) B1423037
theorem B948707 : Blo 948586 948707 := bstep (se 1 (by rfl) ⟨711530, by rfl⟩ : syracuseStep 948707 = 1423061) B1423061
theorem B3045869 : Blo 948586 3045869 := bstep (se 3 (by rfl) ⟨571100, by rfl⟩ : syracuseStep 3045869 = 1142201) B1142201
theorem B948723 : Blo 948586 948723 := bstep (se 1 (by rfl) ⟨711542, by rfl⟩ : syracuseStep 948723 = 1423085) B1423085
theorem B1604083 : Blo 948586 1604083 := bstep (se 1 (by rfl) ⟨1203062, by rfl⟩ : syracuseStep 1604083 = 2406125) B2406125
theorem B948739 : Blo 948586 948739 := bstep (se 1 (by rfl) ⟨711554, by rfl⟩ : syracuseStep 948739 = 1423109) B1423109
theorem B948755 : Blo 948586 948755 := bstep (se 1 (by rfl) ⟨711566, by rfl⟩ : syracuseStep 948755 = 1423133) B1423133
theorem B948771 : Blo 948586 948771 := bstep (se 1 (by rfl) ⟨711578, by rfl⟩ : syracuseStep 948771 = 1423157) B1423157
theorem B948787 : Blo 948586 948787 := bstep (se 1 (by rfl) ⟨711590, by rfl⟩ : syracuseStep 948787 = 1423181) B1423181
theorem B948803 : Blo 948586 948803 := bstep (se 1 (by rfl) ⟨711602, by rfl⟩ : syracuseStep 948803 = 1423205) B1423205
theorem B948819 : Blo 948586 948819 := bstep (se 1 (by rfl) ⟨711614, by rfl⟩ : syracuseStep 948819 = 1423229) B1423229
theorem B948835 : Blo 948586 948835 := bstep (se 1 (by rfl) ⟨711626, by rfl⟩ : syracuseStep 948835 = 1423253) B1423253
theorem B948851 : Blo 948586 948851 := bstep (se 1 (by rfl) ⟨711638, by rfl⟩ : syracuseStep 948851 = 1423277) B1423277
theorem B1604225 : Blo 948586 1604225 := bstep (se 2 (by rfl) ⟨601584, by rfl⟩ : syracuseStep 1604225 = 1203169) B1203169
theorem B948867 : Blo 948586 948867 := bstep (se 1 (by rfl) ⟨711650, by rfl⟩ : syracuseStep 948867 = 1423301) B1423301
theorem B948883 : Blo 948586 948883 := bstep (se 1 (by rfl) ⟨711662, by rfl⟩ : syracuseStep 948883 = 1423325) B1423325
theorem B948899 : Blo 948586 948899 := bstep (se 1 (by rfl) ⟨711674, by rfl⟩ : syracuseStep 948899 = 1423349) B1423349
theorem B948915 : Blo 948586 948915 := bstep (se 1 (by rfl) ⟨711686, by rfl⟩ : syracuseStep 948915 = 1423373) B1423373
theorem B948931 : Blo 948586 948931 := bstep (se 1 (by rfl) ⟨711698, by rfl⟩ : syracuseStep 948931 = 1423397) B1423397
theorem B948947 : Blo 948586 948947 := bstep (se 1 (by rfl) ⟨711710, by rfl⟩ : syracuseStep 948947 = 1423421) B1423421
theorem B948963 : Blo 948586 948963 := bstep (se 1 (by rfl) ⟨711722, by rfl⟩ : syracuseStep 948963 = 1423445) B1423445
theorem B948979 : Blo 948586 948979 := bstep (se 1 (by rfl) ⟨711734, by rfl⟩ : syracuseStep 948979 = 1423469) B1423469
theorem B1604353 : Blo 948586 1604353 := bstep (se 2 (by rfl) ⟨601632, by rfl⟩ : syracuseStep 1604353 = 1203265) B1203265
theorem B948995 : Blo 948586 948995 := bstep (se 1 (by rfl) ⟨711746, by rfl⟩ : syracuseStep 948995 = 1423493) B1423493
theorem B5143301 : Blo 948586 5143301 := bstep (se 4 (by rfl) ⟨482184, by rfl⟩ : syracuseStep 5143301 = 964369) B964369
theorem B949011 : Blo 948586 949011 := bstep (se 1 (by rfl) ⟨711758, by rfl⟩ : syracuseStep 949011 = 1423517) B1423517
theorem B949027 : Blo 948586 949027 := bstep (se 1 (by rfl) ⟨711770, by rfl⟩ : syracuseStep 949027 = 1423541) B1423541
theorem B1014563 : Blo 948586 1014563 := bstep (se 1 (by rfl) ⟨760922, by rfl⟩ : syracuseStep 1014563 = 1521845) B1521845
theorem B1604387 : Blo 948586 1604387 := bstep (se 1 (by rfl) ⟨1203290, by rfl⟩ : syracuseStep 1604387 = 2406581) B2406581
theorem B3210029 : Blo 948586 3210029 := bstep (se 3 (by rfl) ⟨601880, by rfl⟩ : syracuseStep 3210029 = 1203761) B1203761
theorem B949043 : Blo 948586 949043 := bstep (se 1 (by rfl) ⟨711782, by rfl⟩ : syracuseStep 949043 = 1423565) B1423565
theorem B949059 : Blo 948586 949059 := bstep (se 1 (by rfl) ⟨711794, by rfl⟩ : syracuseStep 949059 = 1423589) B1423589
theorem B2030417 : Blo 948586 2030417 := bstep (se 2 (by rfl) ⟨761406, by rfl⟩ : syracuseStep 2030417 = 1522813) B1522813
theorem B949075 : Blo 948586 949075 := bstep (se 1 (by rfl) ⟨711806, by rfl⟩ : syracuseStep 949075 = 1423613) B1423613
theorem B949091 : Blo 948586 949091 := bstep (se 1 (by rfl) ⟨711818, by rfl⟩ : syracuseStep 949091 = 1423637) B1423637
theorem B3210083 : Blo 948586 3210083 := bstep (se 1 (by rfl) ⟨2407562, by rfl⟩ : syracuseStep 3210083 = 4815125) B4815125
theorem B949107 : Blo 948586 949107 := bstep (se 1 (by rfl) ⟨711830, by rfl⟩ : syracuseStep 949107 = 1423661) B1423661
theorem B949123 : Blo 948586 949123 := bstep (se 1 (by rfl) ⟨711842, by rfl⟩ : syracuseStep 949123 = 1423685) B1423685
theorem B949139 : Blo 948586 949139 := bstep (se 1 (by rfl) ⟨711854, by rfl⟩ : syracuseStep 949139 = 1423709) B1423709
theorem B949155 : Blo 948586 949155 := bstep (se 1 (by rfl) ⟨711866, by rfl⟩ : syracuseStep 949155 = 1423733) B1423733
theorem B1604515 : Blo 948586 1604515 := bstep (se 1 (by rfl) ⟨1203386, by rfl⟩ : syracuseStep 1604515 = 2406773) B2406773
theorem B949171 : Blo 948586 949171 := bstep (se 1 (by rfl) ⟨711878, by rfl⟩ : syracuseStep 949171 = 1423757) B1423757
theorem B949187 : Blo 948586 949187 := bstep (se 1 (by rfl) ⟨711890, by rfl⟩ : syracuseStep 949187 = 1423781) B1423781
theorem B949203 : Blo 948586 949203 := bstep (se 1 (by rfl) ⟨711902, by rfl⟩ : syracuseStep 949203 = 1423805) B1423805
theorem B949219 : Blo 948586 949219 := bstep (se 1 (by rfl) ⟨711914, by rfl⟩ : syracuseStep 949219 = 1423829) B1423829
theorem B949235 : Blo 948586 949235 := bstep (se 1 (by rfl) ⟨711926, by rfl⟩ : syracuseStep 949235 = 1423853) B1423853
theorem B949251 : Blo 948586 949251 := bstep (se 1 (by rfl) ⟨711938, by rfl⟩ : syracuseStep 949251 = 1423877) B1423877
theorem B949267 : Blo 948586 949267 := bstep (se 1 (by rfl) ⟨711950, by rfl⟩ : syracuseStep 949267 = 1423901) B1423901
theorem B949283 : Blo 948586 949283 := bstep (se 1 (by rfl) ⟨711962, by rfl⟩ : syracuseStep 949283 = 1423925) B1423925
theorem B1604657 : Blo 948586 1604657 := bstep (se 2 (by rfl) ⟨601746, by rfl⟩ : syracuseStep 1604657 = 1203493) B1203493
theorem B949299 : Blo 948586 949299 := bstep (se 1 (by rfl) ⟨711974, by rfl⟩ : syracuseStep 949299 = 1423949) B1423949
theorem B949315 : Blo 948586 949315 := bstep (se 1 (by rfl) ⟨711986, by rfl⟩ : syracuseStep 949315 = 1423973) B1423973
theorem B949331 : Blo 948586 949331 := bstep (se 1 (by rfl) ⟨711998, by rfl⟩ : syracuseStep 949331 = 1423997) B1423997
theorem B949347 : Blo 948586 949347 := bstep (se 1 (by rfl) ⟨712010, by rfl⟩ : syracuseStep 949347 = 1424021) B1424021
theorem B3210353 : Blo 948586 3210353 := bstep (se 2 (by rfl) ⟨1203882, by rfl⟩ : syracuseStep 3210353 = 2407765) B2407765
theorem B949363 : Blo 948586 949363 := bstep (se 1 (by rfl) ⟨712022, by rfl⟩ : syracuseStep 949363 = 1424045) B1424045
theorem B949379 : Blo 948586 949379 := bstep (se 1 (by rfl) ⟨712034, by rfl⟩ : syracuseStep 949379 = 1424069) B1424069
theorem B949395 : Blo 948586 949395 := bstep (se 1 (by rfl) ⟨712046, by rfl⟩ : syracuseStep 949395 = 1424093) B1424093
theorem B949411 : Blo 948586 949411 := bstep (se 1 (by rfl) ⟨712058, by rfl⟩ : syracuseStep 949411 = 1424117) B1424117
theorem B1604785 : Blo 948586 1604785 := bstep (se 2 (by rfl) ⟨601794, by rfl⟩ : syracuseStep 1604785 = 1203589) B1203589
theorem B949427 : Blo 948586 949427 := bstep (se 1 (by rfl) ⟨712070, by rfl⟩ : syracuseStep 949427 = 1424141) B1424141
theorem B949443 : Blo 948586 949443 := bstep (se 1 (by rfl) ⟨712082, by rfl⟩ : syracuseStep 949443 = 1424165) B1424165
theorem B949459 : Blo 948586 949459 := bstep (se 1 (by rfl) ⟨712094, by rfl⟩ : syracuseStep 949459 = 1424189) B1424189
theorem B1604819 : Blo 948586 1604819 := bstep (se 1 (by rfl) ⟨1203614, by rfl⟩ : syracuseStep 1604819 = 2407229) B2407229
theorem B949475 : Blo 948586 949475 := bstep (se 1 (by rfl) ⟨712106, by rfl⟩ : syracuseStep 949475 = 1424213) B1424213
theorem B949491 : Blo 948586 949491 := bstep (se 1 (by rfl) ⟨712118, by rfl⟩ : syracuseStep 949491 = 1424237) B1424237
theorem B949507 : Blo 948586 949507 := bstep (se 1 (by rfl) ⟨712130, by rfl⟩ : syracuseStep 949507 = 1424261) B1424261
theorem B949523 : Blo 948586 949523 := bstep (se 1 (by rfl) ⟨712142, by rfl⟩ : syracuseStep 949523 = 1424285) B1424285
theorem B949539 : Blo 948586 949539 := bstep (se 1 (by rfl) ⟨712154, by rfl⟩ : syracuseStep 949539 = 1424309) B1424309
theorem B949555 : Blo 948586 949555 := bstep (se 1 (by rfl) ⟨712166, by rfl⟩ : syracuseStep 949555 = 1424333) B1424333
theorem B949571 : Blo 948586 949571 := bstep (se 1 (by rfl) ⟨712178, by rfl⟩ : syracuseStep 949571 = 1424357) B1424357
theorem B949587 : Blo 948586 949587 := bstep (se 1 (by rfl) ⟨712190, by rfl⟩ : syracuseStep 949587 = 1424381) B1424381
theorem B1604947 : Blo 948586 1604947 := bstep (se 1 (by rfl) ⟨1203710, by rfl⟩ : syracuseStep 1604947 = 2407421) B2407421
theorem B3603811 : Blo 948586 3603811 := bstep (se 1 (by rfl) ⟨2702858, by rfl⟩ : syracuseStep 3603811 = 5405717) B5405717
theorem B949603 : Blo 948586 949603 := bstep (se 1 (by rfl) ⟨712202, by rfl⟩ : syracuseStep 949603 = 1424405) B1424405
theorem B949619 : Blo 948586 949619 := bstep (se 1 (by rfl) ⟨712214, by rfl⟩ : syracuseStep 949619 = 1424429) B1424429
theorem B949635 : Blo 948586 949635 := bstep (se 1 (by rfl) ⟨712226, by rfl⟩ : syracuseStep 949635 = 1424453) B1424453
theorem B949651 : Blo 948586 949651 := bstep (se 1 (by rfl) ⟨712238, by rfl⟩ : syracuseStep 949651 = 1424477) B1424477
theorem B949667 : Blo 948586 949667 := bstep (se 1 (by rfl) ⟨712250, by rfl⟩ : syracuseStep 949667 = 1424501) B1424501
theorem B949683 : Blo 948586 949683 := bstep (se 1 (by rfl) ⟨712262, by rfl⟩ : syracuseStep 949683 = 1424525) B1424525
theorem B949699 : Blo 948586 949699 := bstep (se 1 (by rfl) ⟨712274, by rfl⟩ : syracuseStep 949699 = 1424549) B1424549
theorem B949715 : Blo 948586 949715 := bstep (se 1 (by rfl) ⟨712286, by rfl⟩ : syracuseStep 949715 = 1424573) B1424573
theorem B1605089 : Blo 948586 1605089 := bstep (se 2 (by rfl) ⟨601908, by rfl⟩ : syracuseStep 1605089 = 1203817) B1203817
theorem B949731 : Blo 948586 949731 := bstep (se 1 (by rfl) ⟨712298, by rfl⟩ : syracuseStep 949731 = 1424597) B1424597
theorem B949747 : Blo 948586 949747 := bstep (se 1 (by rfl) ⟨712310, by rfl⟩ : syracuseStep 949747 = 1424621) B1424621
theorem B949763 : Blo 948586 949763 := bstep (se 1 (by rfl) ⟨712322, by rfl⟩ : syracuseStep 949763 = 1424645) B1424645
theorem B6094349 : Blo 948586 6094349 := bstep (se 3 (by rfl) ⟨1142690, by rfl⟩ : syracuseStep 6094349 = 2285381) B2285381
theorem B949779 : Blo 948586 949779 := bstep (se 1 (by rfl) ⟨712334, by rfl⟩ : syracuseStep 949779 = 1424669) B1424669
theorem B949795 : Blo 948586 949795 := bstep (se 1 (by rfl) ⟨712346, by rfl⟩ : syracuseStep 949795 = 1424693) B1424693
theorem B1801777 : Blo 948586 1801777 := bstep (se 2 (by rfl) ⟨675666, by rfl⟩ : syracuseStep 1801777 = 1351333) B1351333
theorem B949811 : Blo 948586 949811 := bstep (se 1 (by rfl) ⟨712358, by rfl⟩ : syracuseStep 949811 = 1424717) B1424717
theorem B949827 : Blo 948586 949827 := bstep (se 1 (by rfl) ⟨712370, by rfl⟩ : syracuseStep 949827 = 1424741) B1424741
theorem B949843 : Blo 948586 949843 := bstep (se 1 (by rfl) ⟨712382, by rfl⟩ : syracuseStep 949843 = 1424765) B1424765
theorem B1605217 : Blo 948586 1605217 := bstep (se 2 (by rfl) ⟨601956, by rfl⟩ : syracuseStep 1605217 = 1203913) B1203913
theorem B949859 : Blo 948586 949859 := bstep (se 1 (by rfl) ⟨712394, by rfl⟩ : syracuseStep 949859 = 1424789) B1424789
theorem B949875 : Blo 948586 949875 := bstep (se 1 (by rfl) ⟨712406, by rfl⟩ : syracuseStep 949875 = 1424813) B1424813
theorem B949891 : Blo 948586 949891 := bstep (se 1 (by rfl) ⟨712418, by rfl⟩ : syracuseStep 949891 = 1424837) B1424837
theorem B1605251 : Blo 948586 1605251 := bstep (se 1 (by rfl) ⟨1203938, by rfl⟩ : syracuseStep 1605251 = 2407877) B2407877
theorem B3210893 : Blo 948586 3210893 := bstep (se 3 (by rfl) ⟨602042, by rfl⟩ : syracuseStep 3210893 = 1204085) B1204085
theorem B949907 : Blo 948586 949907 := bstep (se 1 (by rfl) ⟨712430, by rfl⟩ : syracuseStep 949907 = 1424861) B1424861
theorem B949923 : Blo 948586 949923 := bstep (se 1 (by rfl) ⟨712442, by rfl⟩ : syracuseStep 949923 = 1424885) B1424885
theorem B949939 : Blo 948586 949939 := bstep (se 1 (by rfl) ⟨712454, by rfl⟩ : syracuseStep 949939 = 1424909) B1424909
theorem B949955 : Blo 948586 949955 := bstep (se 1 (by rfl) ⟨712466, by rfl⟩ : syracuseStep 949955 = 1424933) B1424933
theorem B3210947 : Blo 948586 3210947 := bstep (se 1 (by rfl) ⟨2408210, by rfl⟩ : syracuseStep 3210947 = 4816421) B4816421
theorem B2031313 : Blo 948586 2031313 := bstep (se 2 (by rfl) ⟨761742, by rfl⟩ : syracuseStep 2031313 = 1523485) B1523485
theorem B949971 : Blo 948586 949971 := bstep (se 1 (by rfl) ⟨712478, by rfl⟩ : syracuseStep 949971 = 1424957) B1424957
theorem B949987 : Blo 948586 949987 := bstep (se 1 (by rfl) ⟨712490, by rfl⟩ : syracuseStep 949987 = 1424981) B1424981
theorem B2031331 : Blo 948586 2031331 := bstep (se 1 (by rfl) ⟨1523498, by rfl⟩ : syracuseStep 2031331 = 3046997) B3046997
theorem B950003 : Blo 948586 950003 := bstep (se 1 (by rfl) ⟨712502, by rfl⟩ : syracuseStep 950003 = 1425005) B1425005
theorem B950019 : Blo 948586 950019 := bstep (se 1 (by rfl) ⟨712514, by rfl⟩ : syracuseStep 950019 = 1425029) B1425029
theorem B1605379 : Blo 948586 1605379 := bstep (se 1 (by rfl) ⟨1204034, by rfl⟩ : syracuseStep 1605379 = 2408069) B2408069
theorem B950035 : Blo 948586 950035 := bstep (se 1 (by rfl) ⟨712526, by rfl⟩ : syracuseStep 950035 = 1425053) B1425053
theorem B950051 : Blo 948586 950051 := bstep (se 1 (by rfl) ⟨712538, by rfl⟩ : syracuseStep 950051 = 1425077) B1425077
theorem B950067 : Blo 948586 950067 := bstep (se 1 (by rfl) ⟨712550, by rfl⟩ : syracuseStep 950067 = 1425101) B1425101
theorem B950083 : Blo 948586 950083 := bstep (se 1 (by rfl) ⟨712562, by rfl⟩ : syracuseStep 950083 = 1425125) B1425125
theorem B950099 : Blo 948586 950099 := bstep (se 1 (by rfl) ⟨712574, by rfl⟩ : syracuseStep 950099 = 1425149) B1425149
theorem B950115 : Blo 948586 950115 := bstep (se 1 (by rfl) ⟨712586, by rfl⟩ : syracuseStep 950115 = 1425173) B1425173
theorem B950131 : Blo 948586 950131 := bstep (se 1 (by rfl) ⟨712598, by rfl⟩ : syracuseStep 950131 = 1425197) B1425197
theorem B950147 : Blo 948586 950147 := bstep (se 1 (by rfl) ⟨712610, by rfl⟩ : syracuseStep 950147 = 1425221) B1425221
theorem B1605521 : Blo 948586 1605521 := bstep (se 2 (by rfl) ⟨602070, by rfl⟩ : syracuseStep 1605521 = 1204141) B1204141
theorem B950163 : Blo 948586 950163 := bstep (se 1 (by rfl) ⟨712622, by rfl⟩ : syracuseStep 950163 = 1425245) B1425245
theorem B950179 : Blo 948586 950179 := bstep (se 1 (by rfl) ⟨712634, by rfl⟩ : syracuseStep 950179 = 1425269) B1425269
theorem B950195 : Blo 948586 950195 := bstep (se 1 (by rfl) ⟨712646, by rfl⟩ : syracuseStep 950195 = 1425293) B1425293
theorem B1802179 : Blo 948586 1802179 := bstep (se 1 (by rfl) ⟨1351634, by rfl⟩ : syracuseStep 1802179 = 2703269) B2703269
theorem B950211 : Blo 948586 950211 := bstep (se 1 (by rfl) ⟨712658, by rfl⟩ : syracuseStep 950211 = 1425317) B1425317
theorem B3211217 : Blo 948586 3211217 := bstep (se 2 (by rfl) ⟨1204206, by rfl⟩ : syracuseStep 3211217 = 2408413) B2408413
theorem B950227 : Blo 948586 950227 := bstep (se 1 (by rfl) ⟨712670, by rfl⟩ : syracuseStep 950227 = 1425341) B1425341
theorem B950243 : Blo 948586 950243 := bstep (se 1 (by rfl) ⟨712682, by rfl⟩ : syracuseStep 950243 = 1425365) B1425365
theorem B1802225 : Blo 948586 1802225 := bstep (se 2 (by rfl) ⟨675834, by rfl⟩ : syracuseStep 1802225 = 1351669) B1351669
theorem B8224753 : Blo 948586 8224753 := bstep (se 2 (by rfl) ⟨3084282, by rfl⟩ : syracuseStep 8224753 = 6168565) B6168565
theorem B950259 : Blo 948586 950259 := bstep (se 1 (by rfl) ⟨712694, by rfl⟩ : syracuseStep 950259 = 1425389) B1425389
theorem B950283 : Blo 948586 950283 := bstep (se 1 (by rfl) ⟨712712, by rfl⟩ : syracuseStep 950283 = 1425425) B1425425
theorem B1802263 : Blo 948586 1802263 := bstep (se 1 (by rfl) ⟨1351697, by rfl⟩ : syracuseStep 1802263 = 2703395) B2703395
theorem B950295 : Blo 948586 950295 := bstep (se 1 (by rfl) ⟨712721, by rfl⟩ : syracuseStep 950295 = 1425443) B1425443
theorem B19005475 : Blo 948586 19005475 := bstep (se 1 (by rfl) ⟨14254106, by rfl⟩ : syracuseStep 19005475 = 28508213) B28508213
theorem B950315 : Blo 948586 950315 := bstep (se 1 (by rfl) ⟨712736, by rfl⟩ : syracuseStep 950315 = 1425473) B1425473
theorem B950327 : Blo 948586 950327 := bstep (se 1 (by rfl) ⟨712745, by rfl⟩ : syracuseStep 950327 = 1425491) B1425491
theorem B950347 : Blo 948586 950347 := bstep (se 1 (by rfl) ⟨712760, by rfl⟩ : syracuseStep 950347 = 1425521) B1425521
theorem B950359 : Blo 948586 950359 := bstep (se 1 (by rfl) ⟨712769, by rfl⟩ : syracuseStep 950359 = 1425539) B1425539
theorem B950379 : Blo 948586 950379 := bstep (se 1 (by rfl) ⟨712784, by rfl⟩ : syracuseStep 950379 = 1425569) B1425569
theorem B950391 : Blo 948586 950391 := bstep (se 1 (by rfl) ⟨712793, by rfl⟩ : syracuseStep 950391 = 1425587) B1425587
theorem B950411 : Blo 948586 950411 := bstep (se 1 (by rfl) ⟨712808, by rfl⟩ : syracuseStep 950411 = 1425617) B1425617
theorem B950423 : Blo 948586 950423 := bstep (se 1 (by rfl) ⟨712817, by rfl⟩ : syracuseStep 950423 = 1425635) B1425635
theorem B950443 : Blo 948586 950443 := bstep (se 1 (by rfl) ⟨712832, by rfl⟩ : syracuseStep 950443 = 1425665) B1425665
theorem B950455 : Blo 948586 950455 := bstep (se 1 (by rfl) ⟨712841, by rfl⟩ : syracuseStep 950455 = 1425683) B1425683
theorem B950475 : Blo 948586 950475 := bstep (se 1 (by rfl) ⟨712856, by rfl⟩ : syracuseStep 950475 = 1425713) B1425713
theorem B950487 : Blo 948586 950487 := bstep (se 1 (by rfl) ⟨712865, by rfl⟩ : syracuseStep 950487 = 1425731) B1425731
theorem B950507 : Blo 948586 950507 := bstep (se 1 (by rfl) ⟨712880, by rfl⟩ : syracuseStep 950507 = 1425761) B1425761
theorem B1802483 : Blo 948586 1802483 := bstep (se 1 (by rfl) ⟨1351862, by rfl⟩ : syracuseStep 1802483 = 2703725) B2703725
theorem B950519 : Blo 948586 950519 := bstep (se 1 (by rfl) ⟨712889, by rfl⟩ : syracuseStep 950519 = 1425779) B1425779
theorem B950539 : Blo 948586 950539 := bstep (se 1 (by rfl) ⟨712904, by rfl⟩ : syracuseStep 950539 = 1425809) B1425809
theorem B1605899 : Blo 948586 1605899 := bstep (se 1 (by rfl) ⟨1204424, by rfl⟩ : syracuseStep 1605899 = 2408849) B2408849
theorem B950551 : Blo 948586 950551 := bstep (se 1 (by rfl) ⟨712913, by rfl⟩ : syracuseStep 950551 = 1425827) B1425827
theorem B950571 : Blo 948586 950571 := bstep (se 1 (by rfl) ⟨712928, by rfl⟩ : syracuseStep 950571 = 1425857) B1425857
theorem B950583 : Blo 948586 950583 := bstep (se 1 (by rfl) ⟨712937, by rfl⟩ : syracuseStep 950583 = 1425875) B1425875
theorem B950603 : Blo 948586 950603 := bstep (se 1 (by rfl) ⟨712952, by rfl⟩ : syracuseStep 950603 = 1425905) B1425905
theorem B3211595 : Blo 948586 3211595 := bstep (se 1 (by rfl) ⟨2408696, by rfl⟩ : syracuseStep 3211595 = 4817393) B4817393
theorem B950615 : Blo 948586 950615 := bstep (se 1 (by rfl) ⟨712961, by rfl⟩ : syracuseStep 950615 = 1425923) B1425923
theorem B950635 : Blo 948586 950635 := bstep (se 1 (by rfl) ⟨712976, by rfl⟩ : syracuseStep 950635 = 1425953) B1425953
theorem B950647 : Blo 948586 950647 := bstep (se 1 (by rfl) ⟨712985, by rfl⟩ : syracuseStep 950647 = 1425971) B1425971
theorem B950667 : Blo 948586 950667 := bstep (se 1 (by rfl) ⟨713000, by rfl⟩ : syracuseStep 950667 = 1426001) B1426001
theorem B1606027 : Blo 948586 1606027 := bstep (se 1 (by rfl) ⟨1204520, by rfl⟩ : syracuseStep 1606027 = 2409041) B2409041
theorem B950679 : Blo 948586 950679 := bstep (se 1 (by rfl) ⟨713009, by rfl⟩ : syracuseStep 950679 = 1426019) B1426019
theorem B950699 : Blo 948586 950699 := bstep (se 1 (by rfl) ⟨713024, by rfl⟩ : syracuseStep 950699 = 1426049) B1426049
theorem B950711 : Blo 948586 950711 := bstep (se 1 (by rfl) ⟨713033, by rfl⟩ : syracuseStep 950711 = 1426067) B1426067
theorem B950731 : Blo 948586 950731 := bstep (se 1 (by rfl) ⟨713048, by rfl⟩ : syracuseStep 950731 = 1426097) B1426097
theorem B1802711 : Blo 948586 1802711 := bstep (se 1 (by rfl) ⟨1352033, by rfl⟩ : syracuseStep 1802711 = 2704067) B2704067
theorem B950743 : Blo 948586 950743 := bstep (se 1 (by rfl) ⟨713057, by rfl⟩ : syracuseStep 950743 = 1426115) B1426115
theorem B5145049 : Blo 948586 5145049 := bstep (se 2 (by rfl) ⟨1929393, by rfl⟩ : syracuseStep 5145049 = 3858787) B3858787
theorem B950763 : Blo 948586 950763 := bstep (se 1 (by rfl) ⟨713072, by rfl⟩ : syracuseStep 950763 = 1426145) B1426145
theorem B950775 : Blo 948586 950775 := bstep (se 1 (by rfl) ⟨713081, by rfl⟩ : syracuseStep 950775 = 1426163) B1426163
theorem B950795 : Blo 948586 950795 := bstep (se 1 (by rfl) ⟨713096, by rfl⟩ : syracuseStep 950795 = 1426193) B1426193
theorem B950807 : Blo 948586 950807 := bstep (se 1 (by rfl) ⟨713105, by rfl⟩ : syracuseStep 950807 = 1426211) B1426211
theorem B1606169 : Blo 948586 1606169 := bstep (se 2 (by rfl) ⟨602313, by rfl⟩ : syracuseStep 1606169 = 1204627) B1204627
theorem B950827 : Blo 948586 950827 := bstep (se 1 (by rfl) ⟨713120, by rfl⟩ : syracuseStep 950827 = 1426241) B1426241
theorem B950839 : Blo 948586 950839 := bstep (se 1 (by rfl) ⟨713129, by rfl⟩ : syracuseStep 950839 = 1426259) B1426259
theorem B3605057 : Blo 948586 3605057 := bstep (se 2 (by rfl) ⟨1351896, by rfl⟩ : syracuseStep 3605057 = 2703793) B2703793
theorem B950859 : Blo 948586 950859 := bstep (se 1 (by rfl) ⟨713144, by rfl⟩ : syracuseStep 950859 = 1426289) B1426289
theorem B950871 : Blo 948586 950871 := bstep (se 1 (by rfl) ⟨713153, by rfl⟩ : syracuseStep 950871 = 1426307) B1426307
theorem B3211865 : Blo 948586 3211865 := bstep (se 2 (by rfl) ⟨1204449, by rfl⟩ : syracuseStep 3211865 = 2408899) B2408899
theorem B950891 : Blo 948586 950891 := bstep (se 1 (by rfl) ⟨713168, by rfl⟩ : syracuseStep 950891 = 1426337) B1426337
theorem B950903 : Blo 948586 950903 := bstep (se 1 (by rfl) ⟨713177, by rfl⟩ : syracuseStep 950903 = 1426355) B1426355
theorem B950923 : Blo 948586 950923 := bstep (se 1 (by rfl) ⟨713192, by rfl⟩ : syracuseStep 950923 = 1426385) B1426385
theorem B950935 : Blo 948586 950935 := bstep (se 1 (by rfl) ⟨713201, by rfl⟩ : syracuseStep 950935 = 1426403) B1426403
theorem B1606297 : Blo 948586 1606297 := bstep (se 2 (by rfl) ⟨602361, by rfl⟩ : syracuseStep 1606297 = 1204723) B1204723
theorem B950955 : Blo 948586 950955 := bstep (se 1 (by rfl) ⟨713216, by rfl⟩ : syracuseStep 950955 = 1426433) B1426433
theorem B950967 : Blo 948586 950967 := bstep (se 1 (by rfl) ⟨713225, by rfl⟩ : syracuseStep 950967 = 1426451) B1426451
theorem B950987 : Blo 948586 950987 := bstep (se 1 (by rfl) ⟨713240, by rfl⟩ : syracuseStep 950987 = 1426481) B1426481
theorem B950999 : Blo 948586 950999 := bstep (se 1 (by rfl) ⟨713249, by rfl⟩ : syracuseStep 950999 = 1426499) B1426499
theorem B1802969 : Blo 948586 1802969 := bstep (se 2 (by rfl) ⟨676113, by rfl⟩ : syracuseStep 1802969 = 1352227) B1352227
theorem B951019 : Blo 948586 951019 := bstep (se 1 (by rfl) ⟨713264, by rfl⟩ : syracuseStep 951019 = 1426529) B1426529
theorem B951031 : Blo 948586 951031 := bstep (se 1 (by rfl) ⟨713273, by rfl⟩ : syracuseStep 951031 = 1426547) B1426547
theorem B951051 : Blo 948586 951051 := bstep (se 1 (by rfl) ⟨713288, by rfl⟩ : syracuseStep 951051 = 1426577) B1426577
theorem B951063 : Blo 948586 951063 := bstep (se 1 (by rfl) ⟨713297, by rfl⟩ : syracuseStep 951063 = 1426595) B1426595
theorem B951083 : Blo 948586 951083 := bstep (se 1 (by rfl) ⟨713312, by rfl⟩ : syracuseStep 951083 = 1426625) B1426625
theorem B951095 : Blo 948586 951095 := bstep (se 1 (by rfl) ⟨713321, by rfl⟩ : syracuseStep 951095 = 1426643) B1426643
theorem B951115 : Blo 948586 951115 := bstep (se 1 (by rfl) ⟨713336, by rfl⟩ : syracuseStep 951115 = 1426673) B1426673
theorem B951127 : Blo 948586 951127 := bstep (se 1 (by rfl) ⟨713345, by rfl⟩ : syracuseStep 951127 = 1426691) B1426691
theorem B951147 : Blo 948586 951147 := bstep (se 1 (by rfl) ⟨713360, by rfl⟩ : syracuseStep 951147 = 1426721) B1426721
theorem B951159 : Blo 948586 951159 := bstep (se 1 (by rfl) ⟨713369, by rfl⟩ : syracuseStep 951159 = 1426739) B1426739
theorem B951179 : Blo 948586 951179 := bstep (se 1 (by rfl) ⟨713384, by rfl⟩ : syracuseStep 951179 = 1426769) B1426769
theorem B951191 : Blo 948586 951191 := bstep (se 1 (by rfl) ⟨713393, by rfl⟩ : syracuseStep 951191 = 1426787) B1426787
theorem B951211 : Blo 948586 951211 := bstep (se 1 (by rfl) ⟨713408, by rfl⟩ : syracuseStep 951211 = 1426817) B1426817
theorem B951223 : Blo 948586 951223 := bstep (se 1 (by rfl) ⟨713417, by rfl⟩ : syracuseStep 951223 = 1426835) B1426835
theorem B1016759 : Blo 948586 1016759 := bstep (se 1 (by rfl) ⟨762569, by rfl⟩ : syracuseStep 1016759 = 1525139) B1525139
theorem B951243 : Blo 948586 951243 := bstep (se 1 (by rfl) ⟨713432, by rfl⟩ : syracuseStep 951243 = 1426865) B1426865
theorem B951255 : Blo 948586 951255 := bstep (se 1 (by rfl) ⟨713441, by rfl⟩ : syracuseStep 951255 = 1426883) B1426883
theorem B951275 : Blo 948586 951275 := bstep (se 1 (by rfl) ⟨713456, by rfl⟩ : syracuseStep 951275 = 1426913) B1426913
theorem B951287 : Blo 948586 951287 := bstep (se 1 (by rfl) ⟨713465, by rfl⟩ : syracuseStep 951287 = 1426931) B1426931
theorem B951307 : Blo 948586 951307 := bstep (se 1 (by rfl) ⟨713480, by rfl⟩ : syracuseStep 951307 = 1426961) B1426961
theorem B951319 : Blo 948586 951319 := bstep (se 1 (by rfl) ⟨713489, by rfl⟩ : syracuseStep 951319 = 1426979) B1426979
theorem B951339 : Blo 948586 951339 := bstep (se 1 (by rfl) ⟨713504, by rfl⟩ : syracuseStep 951339 = 1427009) B1427009
theorem B951351 : Blo 948586 951351 := bstep (se 1 (by rfl) ⟨713513, by rfl⟩ : syracuseStep 951351 = 1427027) B1427027
theorem B951371 : Blo 948586 951371 := bstep (se 1 (by rfl) ⟨713528, by rfl⟩ : syracuseStep 951371 = 1427057) B1427057
theorem B2032715 : Blo 948586 2032715 := bstep (se 1 (by rfl) ⟨1524536, by rfl⟩ : syracuseStep 2032715 = 3049073) B3049073
theorem B951383 : Blo 948586 951383 := bstep (se 1 (by rfl) ⟨713537, by rfl⟩ : syracuseStep 951383 = 1427075) B1427075
theorem B951403 : Blo 948586 951403 := bstep (se 1 (by rfl) ⟨713552, by rfl⟩ : syracuseStep 951403 = 1427105) B1427105
theorem B1803379 : Blo 948586 1803379 := bstep (se 1 (by rfl) ⟨1352534, by rfl⟩ : syracuseStep 1803379 = 2705069) B2705069
theorem B951415 : Blo 948586 951415 := bstep (se 1 (by rfl) ⟨713561, by rfl⟩ : syracuseStep 951415 = 1427123) B1427123
theorem B951435 : Blo 948586 951435 := bstep (se 1 (by rfl) ⟨713576, by rfl⟩ : syracuseStep 951435 = 1427153) B1427153
theorem B951447 : Blo 948586 951447 := bstep (se 1 (by rfl) ⟨713585, by rfl⟩ : syracuseStep 951447 = 1427171) B1427171
theorem B951467 : Blo 948586 951467 := bstep (se 1 (by rfl) ⟨713600, by rfl⟩ : syracuseStep 951467 = 1427201) B1427201
theorem B50136245 : Blo 948586 50136245 := bstep (se 5 (by rfl) ⟨2350136, by rfl⟩ : syracuseStep 50136245 = 4700273) B4700273
theorem B951479 : Blo 948586 951479 := bstep (se 1 (by rfl) ⟨713609, by rfl⟩ : syracuseStep 951479 = 1427219) B1427219
theorem B951499 : Blo 948586 951499 := bstep (se 1 (by rfl) ⟨713624, by rfl⟩ : syracuseStep 951499 = 1427249) B1427249
theorem B951511 : Blo 948586 951511 := bstep (se 1 (by rfl) ⟨713633, by rfl⟩ : syracuseStep 951511 = 1427267) B1427267
theorem B1606871 : Blo 948586 1606871 := bstep (se 1 (by rfl) ⟨1205153, by rfl⟩ : syracuseStep 1606871 = 2410307) B2410307
theorem B951531 : Blo 948586 951531 := bstep (se 1 (by rfl) ⟨713648, by rfl⟩ : syracuseStep 951531 = 1427297) B1427297
theorem B951543 : Blo 948586 951543 := bstep (se 1 (by rfl) ⟨713657, by rfl⟩ : syracuseStep 951543 = 1427315) B1427315
theorem B951563 : Blo 948586 951563 := bstep (se 1 (by rfl) ⟨713672, by rfl⟩ : syracuseStep 951563 = 1427345) B1427345
theorem B951575 : Blo 948586 951575 := bstep (se 1 (by rfl) ⟨713681, by rfl⟩ : syracuseStep 951575 = 1427363) B1427363
theorem B3212567 : Blo 948586 3212567 := bstep (se 1 (by rfl) ⟨2409425, by rfl⟩ : syracuseStep 3212567 = 4818851) B4818851
theorem B951595 : Blo 948586 951595 := bstep (se 1 (by rfl) ⟨713696, by rfl⟩ : syracuseStep 951595 = 1427393) B1427393
theorem B951607 : Blo 948586 951607 := bstep (se 1 (by rfl) ⟨713705, by rfl⟩ : syracuseStep 951607 = 1427411) B1427411
theorem B951627 : Blo 948586 951627 := bstep (se 1 (by rfl) ⟨713720, by rfl⟩ : syracuseStep 951627 = 1427441) B1427441
theorem B951639 : Blo 948586 951639 := bstep (se 1 (by rfl) ⟨713729, by rfl⟩ : syracuseStep 951639 = 1427459) B1427459
theorem B1606999 : Blo 948586 1606999 := bstep (se 1 (by rfl) ⟨1205249, by rfl⟩ : syracuseStep 1606999 = 2410499) B2410499
theorem B951659 : Blo 948586 951659 := bstep (se 1 (by rfl) ⟨713744, by rfl⟩ : syracuseStep 951659 = 1427489) B1427489
theorem B951671 : Blo 948586 951671 := bstep (se 1 (by rfl) ⟨713753, by rfl⟩ : syracuseStep 951671 = 1427507) B1427507
theorem B951691 : Blo 948586 951691 := bstep (se 1 (by rfl) ⟨713768, by rfl⟩ : syracuseStep 951691 = 1427537) B1427537
theorem B951703 : Blo 948586 951703 := bstep (se 1 (by rfl) ⟨713777, by rfl⟩ : syracuseStep 951703 = 1427555) B1427555
theorem B951723 : Blo 948586 951723 := bstep (se 1 (by rfl) ⟨713792, by rfl⟩ : syracuseStep 951723 = 1427585) B1427585
theorem B951735 : Blo 948586 951735 := bstep (se 1 (by rfl) ⟨713801, by rfl⟩ : syracuseStep 951735 = 1427603) B1427603
theorem B951755 : Blo 948586 951755 := bstep (se 1 (by rfl) ⟨713816, by rfl⟩ : syracuseStep 951755 = 1427633) B1427633
theorem B951767 : Blo 948586 951767 := bstep (se 1 (by rfl) ⟨713825, by rfl⟩ : syracuseStep 951767 = 1427651) B1427651
theorem B951787 : Blo 948586 951787 := bstep (se 1 (by rfl) ⟨713840, by rfl⟩ : syracuseStep 951787 = 1427681) B1427681
theorem B951799 : Blo 948586 951799 := bstep (se 1 (by rfl) ⟨713849, by rfl⟩ : syracuseStep 951799 = 1427699) B1427699
theorem B951819 : Blo 948586 951819 := bstep (se 1 (by rfl) ⟨713864, by rfl⟩ : syracuseStep 951819 = 1427729) B1427729
theorem B951831 : Blo 948586 951831 := bstep (se 1 (by rfl) ⟨713873, by rfl⟩ : syracuseStep 951831 = 1427747) B1427747
theorem B951851 : Blo 948586 951851 := bstep (se 1 (by rfl) ⟨713888, by rfl⟩ : syracuseStep 951851 = 1427777) B1427777
theorem B4064813 : Blo 948586 4064813 := bstep (se 3 (by rfl) ⟨762152, by rfl⟩ : syracuseStep 4064813 = 1524305) B1524305
theorem B951863 : Blo 948586 951863 := bstep (se 1 (by rfl) ⟨713897, by rfl⟩ : syracuseStep 951863 = 1427795) B1427795
theorem B951883 : Blo 948586 951883 := bstep (se 1 (by rfl) ⟨713912, by rfl⟩ : syracuseStep 951883 = 1427825) B1427825
theorem B951895 : Blo 948586 951895 := bstep (se 1 (by rfl) ⟨713921, by rfl⟩ : syracuseStep 951895 = 1427843) B1427843
theorem B1803865 : Blo 948586 1803865 := bstep (se 2 (by rfl) ⟨676449, by rfl⟩ : syracuseStep 1803865 = 1352899) B1352899
theorem B7308893 : Blo 948586 7308893 := bstep (se 3 (by rfl) ⟨1370417, by rfl⟩ : syracuseStep 7308893 = 2740835) B2740835
theorem B951915 : Blo 948586 951915 := bstep (se 1 (by rfl) ⟨713936, by rfl⟩ : syracuseStep 951915 = 1427873) B1427873
theorem B951927 : Blo 948586 951927 := bstep (se 1 (by rfl) ⟨713945, by rfl⟩ : syracuseStep 951927 = 1427891) B1427891
theorem B951947 : Blo 948586 951947 := bstep (se 1 (by rfl) ⟨713960, by rfl⟩ : syracuseStep 951947 = 1427921) B1427921
theorem B951959 : Blo 948586 951959 := bstep (se 1 (by rfl) ⟨713969, by rfl⟩ : syracuseStep 951959 = 1427939) B1427939
theorem B951979 : Blo 948586 951979 := bstep (se 1 (by rfl) ⟨713984, by rfl⟩ : syracuseStep 951979 = 1427969) B1427969
theorem B951991 : Blo 948586 951991 := bstep (se 1 (by rfl) ⟨713993, by rfl⟩ : syracuseStep 951991 = 1427987) B1427987
theorem B952011 : Blo 948586 952011 := bstep (se 1 (by rfl) ⟨714008, by rfl⟩ : syracuseStep 952011 = 1428017) B1428017
theorem B952023 : Blo 948586 952023 := bstep (se 1 (by rfl) ⟨714017, by rfl⟩ : syracuseStep 952023 = 1428035) B1428035
theorem B952043 : Blo 948586 952043 := bstep (se 1 (by rfl) ⟨714032, by rfl⟩ : syracuseStep 952043 = 1428065) B1428065
theorem B952055 : Blo 948586 952055 := bstep (se 1 (by rfl) ⟨714041, by rfl⟩ : syracuseStep 952055 = 1428083) B1428083
theorem B952075 : Blo 948586 952075 := bstep (se 1 (by rfl) ⟨714056, by rfl⟩ : syracuseStep 952075 = 1428113) B1428113
theorem B952087 : Blo 948586 952087 := bstep (se 1 (by rfl) ⟨714065, by rfl⟩ : syracuseStep 952087 = 1428131) B1428131
theorem B952107 : Blo 948586 952107 := bstep (se 1 (by rfl) ⟨714080, by rfl⟩ : syracuseStep 952107 = 1428161) B1428161
theorem B3213107 : Blo 948586 3213107 := bstep (se 1 (by rfl) ⟨2409830, by rfl⟩ : syracuseStep 3213107 = 4819661) B4819661
theorem B952119 : Blo 948586 952119 := bstep (se 1 (by rfl) ⟨714089, by rfl⟩ : syracuseStep 952119 = 1428179) B1428179
theorem B5146433 : Blo 948586 5146433 := bstep (se 2 (by rfl) ⟨1929912, by rfl⟩ : syracuseStep 5146433 = 3859825) B3859825
theorem B952139 : Blo 948586 952139 := bstep (se 1 (by rfl) ⟨714104, by rfl⟩ : syracuseStep 952139 = 1428209) B1428209
theorem B952151 : Blo 948586 952151 := bstep (se 1 (by rfl) ⟨714113, by rfl⟩ : syracuseStep 952151 = 1428227) B1428227
theorem B952171 : Blo 948586 952171 := bstep (se 1 (by rfl) ⟨714128, by rfl⟩ : syracuseStep 952171 = 1428257) B1428257
theorem B952183 : Blo 948586 952183 := bstep (se 1 (by rfl) ⟨714137, by rfl⟩ : syracuseStep 952183 = 1428275) B1428275
theorem B952203 : Blo 948586 952203 := bstep (se 1 (by rfl) ⟨714152, by rfl⟩ : syracuseStep 952203 = 1428305) B1428305
theorem B952215 : Blo 948586 952215 := bstep (se 1 (by rfl) ⟨714161, by rfl⟩ : syracuseStep 952215 = 1428323) B1428323
theorem B2033561 : Blo 948586 2033561 := bstep (se 2 (by rfl) ⟨762585, by rfl⟩ : syracuseStep 2033561 = 1525171) B1525171
theorem B952235 : Blo 948586 952235 := bstep (se 1 (by rfl) ⟨714176, by rfl⟩ : syracuseStep 952235 = 1428353) B1428353
theorem B952247 : Blo 948586 952247 := bstep (se 1 (by rfl) ⟨714185, by rfl⟩ : syracuseStep 952247 = 1428371) B1428371
theorem B952267 : Blo 948586 952267 := bstep (se 1 (by rfl) ⟨714200, by rfl⟩ : syracuseStep 952267 = 1428401) B1428401
theorem B952279 : Blo 948586 952279 := bstep (se 1 (by rfl) ⟨714209, by rfl⟩ : syracuseStep 952279 = 1428419) B1428419
theorem B952299 : Blo 948586 952299 := bstep (se 1 (by rfl) ⟨714224, by rfl⟩ : syracuseStep 952299 = 1428449) B1428449
theorem B952311 : Blo 948586 952311 := bstep (se 1 (by rfl) ⟨714233, by rfl⟩ : syracuseStep 952311 = 1428467) B1428467
theorem B952331 : Blo 948586 952331 := bstep (se 1 (by rfl) ⟨714248, by rfl⟩ : syracuseStep 952331 = 1428497) B1428497
theorem B3606545 : Blo 948586 3606545 := bstep (se 2 (by rfl) ⟨1352454, by rfl⟩ : syracuseStep 3606545 = 2704909) B2704909
theorem B952343 : Blo 948586 952343 := bstep (se 1 (by rfl) ⟨714257, by rfl⟩ : syracuseStep 952343 = 1428515) B1428515
theorem B952363 : Blo 948586 952363 := bstep (se 1 (by rfl) ⟨714272, by rfl⟩ : syracuseStep 952363 = 1428545) B1428545
theorem B952375 : Blo 948586 952375 := bstep (se 1 (by rfl) ⟨714281, by rfl⟩ : syracuseStep 952375 = 1428563) B1428563
theorem B3213377 : Blo 948586 3213377 := bstep (se 2 (by rfl) ⟨1205016, by rfl⟩ : syracuseStep 3213377 = 2410033) B2410033
theorem B952395 : Blo 948586 952395 := bstep (se 1 (by rfl) ⟨714296, by rfl⟩ : syracuseStep 952395 = 1428593) B1428593
theorem B952407 : Blo 948586 952407 := bstep (se 1 (by rfl) ⟨714305, by rfl⟩ : syracuseStep 952407 = 1428611) B1428611
theorem B952427 : Blo 948586 952427 := bstep (se 1 (by rfl) ⟨714320, by rfl⟩ : syracuseStep 952427 = 1428641) B1428641
theorem B952439 : Blo 948586 952439 := bstep (se 1 (by rfl) ⟨714329, by rfl⟩ : syracuseStep 952439 = 1428659) B1428659
theorem B1804427 : Blo 948586 1804427 := bstep (se 1 (by rfl) ⟨1353320, by rfl⟩ : syracuseStep 1804427 = 2706641) B2706641
theorem B952459 : Blo 948586 952459 := bstep (se 1 (by rfl) ⟨714344, by rfl⟩ : syracuseStep 952459 = 1428689) B1428689
theorem B952471 : Blo 948586 952471 := bstep (se 1 (by rfl) ⟨714353, by rfl⟩ : syracuseStep 952471 = 1428707) B1428707
theorem B952491 : Blo 948586 952491 := bstep (se 1 (by rfl) ⟨714368, by rfl⟩ : syracuseStep 952491 = 1428737) B1428737
theorem B952503 : Blo 948586 952503 := bstep (se 1 (by rfl) ⟨714377, by rfl⟩ : syracuseStep 952503 = 1428755) B1428755
theorem B952523 : Blo 948586 952523 := bstep (se 1 (by rfl) ⟨714392, by rfl⟩ : syracuseStep 952523 = 1428785) B1428785
theorem B952535 : Blo 948586 952535 := bstep (se 1 (by rfl) ⟨714401, by rfl⟩ : syracuseStep 952535 = 1428803) B1428803
theorem B4065497 : Blo 948586 4065497 := bstep (se 2 (by rfl) ⟨1524561, by rfl⟩ : syracuseStep 4065497 = 3049123) B3049123
theorem B952555 : Blo 948586 952555 := bstep (se 1 (by rfl) ⟨714416, by rfl⟩ : syracuseStep 952555 = 1428833) B1428833
theorem B952567 : Blo 948586 952567 := bstep (se 1 (by rfl) ⟨714425, by rfl⟩ : syracuseStep 952567 = 1428851) B1428851
theorem B5409089 : Blo 948586 5409089 := bstep (se 2 (by rfl) ⟨2028408, by rfl⟩ : syracuseStep 5409089 = 4056817) B4056817
theorem B1804609 : Blo 948586 1804609 := bstep (se 2 (by rfl) ⟨676728, by rfl⟩ : syracuseStep 1804609 = 1353457) B1353457
theorem B6490469 : Blo 948586 6490469 := bstep (se 4 (by rfl) ⟨608481, by rfl⟩ : syracuseStep 6490469 = 1216963) B1216963
theorem B22219157 : Blo 948586 22219157 := bstep (se 6 (by rfl) ⟨520761, by rfl⟩ : syracuseStep 22219157 = 1041523) B1041523
theorem B3607001 : Blo 948586 3607001 := bstep (se 2 (by rfl) ⟨1352625, by rfl⟩ : syracuseStep 3607001 = 2705251) B2705251
theorem B30771683 : Blo 948586 30771683 := bstep (se 1 (by rfl) ⟨23078762, by rfl⟩ : syracuseStep 30771683 = 46157525) B46157525
theorem B7801379 : Blo 948586 7801379 := bstep (se 1 (by rfl) ⟨5851034, by rfl⟩ : syracuseStep 7801379 = 11702069) B11702069
theorem B2886209 : Blo 948586 2886209 := bstep (se 2 (by rfl) ⟨1082328, by rfl⟩ : syracuseStep 2886209 = 2164657) B2164657
theorem B3213917 : Blo 948586 3213917 := bstep (se 3 (by rfl) ⟨602609, by rfl⟩ : syracuseStep 3213917 = 1205219) B1205219
theorem B3607213 : Blo 948586 3607213 := bstep (se 3 (by rfl) ⟨676352, by rfl⟩ : syracuseStep 3607213 = 1352705) B1352705
theorem B2034355 : Blo 948586 2034355 := bstep (se 1 (by rfl) ⟨1525766, by rfl⟩ : syracuseStep 2034355 = 3051533) B3051533
theorem B8227589 : Blo 948586 8227589 := bstep (se 4 (by rfl) ⟨771336, by rfl⟩ : syracuseStep 8227589 = 1542673) B1542673
theorem B3607517 : Blo 948586 3607517 := bstep (se 3 (by rfl) ⟨676409, by rfl⟩ : syracuseStep 3607517 = 1352819) B1352819
theorem B2165771 : Blo 948586 2165771 := bstep (se 1 (by rfl) ⟨1624328, by rfl⟩ : syracuseStep 2165771 = 3248657) B3248657
theorem B1805323 : Blo 948586 1805323 := bstep (se 1 (by rfl) ⟨1353992, by rfl⟩ : syracuseStep 1805323 = 2707985) B2707985
theorem B4819985 : Blo 948586 4819985 := bstep (se 2 (by rfl) ⟨1807494, by rfl⟩ : syracuseStep 4819985 = 3614989) B3614989
theorem B2165825 : Blo 948586 2165825 := bstep (se 2 (by rfl) ⟨812184, by rfl⟩ : syracuseStep 2165825 = 1624369) B1624369
theorem B2198593 : Blo 948586 2198593 := bstep (se 2 (by rfl) ⟨824472, by rfl⟩ : syracuseStep 2198593 = 1648945) B1648945
theorem B1805399 : Blo 948586 1805399 := bstep (se 1 (by rfl) ⟨1354049, by rfl⟩ : syracuseStep 1805399 = 2708099) B2708099
theorem B3050585 : Blo 948586 3050585 := bstep (se 2 (by rfl) ⟨1143969, by rfl⟩ : syracuseStep 3050585 = 2287939) B2287939
theorem B1445015 : Blo 948586 1445015 := bstep (se 1 (by rfl) ⟨1083761, by rfl⟩ : syracuseStep 1445015 = 2167523) B2167523
theorem B6851735 : Blo 948586 6851735 := bstep (se 1 (by rfl) ⟨5138801, by rfl⟩ : syracuseStep 6851735 = 10277603) B10277603
theorem B4820147 : Blo 948586 4820147 := bstep (se 1 (by rfl) ⟨3615110, by rfl⟩ : syracuseStep 4820147 = 7230221) B7230221
theorem B4066625 : Blo 948586 4066625 := bstep (se 2 (by rfl) ⟨1524984, by rfl⟩ : syracuseStep 4066625 = 3049969) B3049969
theorem B8129969 : Blo 948586 8129969 := bstep (se 2 (by rfl) ⟨3048738, by rfl⟩ : syracuseStep 8129969 = 6097477) B6097477
theorem B1806067 : Blo 948586 1806067 := bstep (se 1 (by rfl) ⟨1354550, by rfl⟩ : syracuseStep 1806067 = 2709101) B2709101
theorem B12160813 : Blo 948586 12160813 := bstep (se 3 (by rfl) ⟨2280152, by rfl⟩ : syracuseStep 12160813 = 4560305) B4560305
theorem B1806295 : Blo 948586 1806295 := bstep (se 1 (by rfl) ⟨1354721, by rfl⟩ : syracuseStep 1806295 = 2709443) B2709443
theorem B1806401 : Blo 948586 1806401 := bstep (se 2 (by rfl) ⟨677400, by rfl⟩ : syracuseStep 1806401 = 1354801) B1354801
theorem B10850435 : Blo 948586 10850435 := bstep (se 1 (by rfl) ⟨8137826, by rfl⟩ : syracuseStep 10850435 = 16275653) B16275653
theorem B4558999 : Blo 948586 4558999 := bstep (se 1 (by rfl) ⟨3419249, by rfl⟩ : syracuseStep 4558999 = 6838499) B6838499
theorem B1806553 : Blo 948586 1806553 := bstep (se 2 (by rfl) ⟨677457, by rfl⟩ : syracuseStep 1806553 = 1354915) B1354915
theorem B14094691 : Blo 948586 14094691 := bstep (se 1 (by rfl) ⟨10571018, by rfl⟩ : syracuseStep 14094691 = 21142037) B21142037
theorem B2134475 : Blo 948586 2134475 := bstep (se 1 (by rfl) ⟨1600856, by rfl⟩ : syracuseStep 2134475 = 3201713) B3201713
theorem B2134529 : Blo 948586 2134529 := bstep (se 2 (by rfl) ⟨800448, by rfl⟩ : syracuseStep 2134529 = 1600897) B1600897
theorem B3085003 : Blo 948586 3085003 := bstep (se 1 (by rfl) ⟨2313752, by rfl⟩ : syracuseStep 3085003 = 4627505) B4627505
theorem B2134745 : Blo 948586 2134745 := bstep (se 2 (by rfl) ⟨800529, by rfl⟩ : syracuseStep 2134745 = 1601059) B1601059
theorem B1086251 : Blo 948586 1086251 := bstep (se 1 (by rfl) ⟨814688, by rfl⟩ : syracuseStep 1086251 = 1629377) B1629377
theorem B2134835 : Blo 948586 2134835 := bstep (se 1 (by rfl) ⟨1601126, by rfl⟩ : syracuseStep 2134835 = 3202253) B3202253
theorem B2134871 : Blo 948586 2134871 := bstep (se 1 (by rfl) ⟨1601153, by rfl⟩ : syracuseStep 2134871 = 3202307) B3202307
theorem B4068299 : Blo 948586 4068299 := bstep (se 1 (by rfl) ⟨3051224, by rfl⟩ : syracuseStep 4068299 = 6102449) B6102449
theorem B2135051 : Blo 948586 2135051 := bstep (se 1 (by rfl) ⟨1601288, by rfl⟩ : syracuseStep 2135051 = 3202577) B3202577
theorem B2135105 : Blo 948586 2135105 := bstep (se 2 (by rfl) ⟨800664, by rfl⟩ : syracuseStep 2135105 = 1601329) B1601329
theorem B4822091 : Blo 948586 4822091 := bstep (se 1 (by rfl) ⟨3616568, by rfl⟩ : syracuseStep 4822091 = 7233137) B7233137
theorem B2135321 : Blo 948586 2135321 := bstep (se 2 (by rfl) ⟨800745, by rfl⟩ : syracuseStep 2135321 = 1601491) B1601491
theorem B2135411 : Blo 948586 2135411 := bstep (se 1 (by rfl) ⟨1601558, by rfl⟩ : syracuseStep 2135411 = 3203117) B3203117
theorem B2135447 : Blo 948586 2135447 := bstep (se 1 (by rfl) ⟨1601585, by rfl⟩ : syracuseStep 2135447 = 3203171) B3203171
theorem B6264215 : Blo 948586 6264215 := bstep (se 1 (by rfl) ⟨4698161, by rfl⟩ : syracuseStep 6264215 = 9396323) B9396323
theorem B1807859 : Blo 948586 1807859 := bstep (se 1 (by rfl) ⟨1355894, by rfl⟩ : syracuseStep 1807859 = 2711789) B2711789
theorem B3610115 : Blo 948586 3610115 := bstep (se 1 (by rfl) ⟨2707586, by rfl⟩ : syracuseStep 3610115 = 5415173) B5415173
theorem B3610129 : Blo 948586 3610129 := bstep (se 2 (by rfl) ⟨1353798, by rfl⟩ : syracuseStep 3610129 = 2707597) B2707597
theorem B2135627 : Blo 948586 2135627 := bstep (se 1 (by rfl) ⟨1601720, by rfl⟩ : syracuseStep 2135627 = 3203441) B3203441
theorem B2135681 : Blo 948586 2135681 := bstep (se 2 (by rfl) ⟨800880, by rfl⟩ : syracuseStep 2135681 = 1601761) B1601761
theorem B1808011 : Blo 948586 1808011 := bstep (se 1 (by rfl) ⟨1356008, by rfl⟩ : syracuseStep 1808011 = 2712017) B2712017
theorem B3610433 : Blo 948586 3610433 := bstep (se 2 (by rfl) ⟨1353912, by rfl⟩ : syracuseStep 3610433 = 2707825) B2707825
theorem B2135897 : Blo 948586 2135897 := bstep (se 2 (by rfl) ⟨800961, by rfl⟩ : syracuseStep 2135897 = 1601923) B1601923
theorem B2135987 : Blo 948586 2135987 := bstep (se 1 (by rfl) ⟨1601990, by rfl⟩ : syracuseStep 2135987 = 3203981) B3203981
theorem B2889665 : Blo 948586 2889665 := bstep (se 2 (by rfl) ⟨1083624, by rfl⟩ : syracuseStep 2889665 = 2167249) B2167249
theorem B2136023 : Blo 948586 2136023 := bstep (se 1 (by rfl) ⟨1602017, by rfl⟩ : syracuseStep 2136023 = 3204035) B3204035
theorem B1808345 : Blo 948586 1808345 := bstep (se 2 (by rfl) ⟨678129, by rfl⟩ : syracuseStep 1808345 = 1356259) B1356259
theorem B2136203 : Blo 948586 2136203 := bstep (se 1 (by rfl) ⟨1602152, by rfl⟩ : syracuseStep 2136203 = 3204305) B3204305
theorem B2136257 : Blo 948586 2136257 := bstep (se 2 (by rfl) ⟨801096, by rfl⟩ : syracuseStep 2136257 = 1602193) B1602193
theorem B2136473 : Blo 948586 2136473 := bstep (se 2 (by rfl) ⟨801177, by rfl⟩ : syracuseStep 2136473 = 1602355) B1602355
theorem B3611101 : Blo 948586 3611101 := bstep (se 3 (by rfl) ⟨677081, by rfl⟩ : syracuseStep 3611101 = 1354163) B1354163
theorem B2136563 : Blo 948586 2136563 := bstep (se 1 (by rfl) ⟨1602422, by rfl⟩ : syracuseStep 2136563 = 3204845) B3204845
theorem B2136599 : Blo 948586 2136599 := bstep (se 1 (by rfl) ⟨1602449, by rfl⟩ : syracuseStep 2136599 = 3204899) B3204899
theorem B2136779 : Blo 948586 2136779 := bstep (se 1 (by rfl) ⟨1602584, by rfl⟩ : syracuseStep 2136779 = 3205169) B3205169
theorem B2136833 : Blo 948586 2136833 := bstep (se 2 (by rfl) ⟨801312, by rfl⟩ : syracuseStep 2136833 = 1602625) B1602625
theorem B2137049 : Blo 948586 2137049 := bstep (se 2 (by rfl) ⟨801393, by rfl⟩ : syracuseStep 2137049 = 1602787) B1602787
theorem B2137139 : Blo 948586 2137139 := bstep (se 1 (by rfl) ⟨1602854, by rfl⟩ : syracuseStep 2137139 = 3205709) B3205709
theorem B2137175 : Blo 948586 2137175 := bstep (se 1 (by rfl) ⟨1602881, by rfl⟩ : syracuseStep 2137175 = 3205763) B3205763
theorem B2169985 : Blo 948586 2169985 := bstep (se 2 (by rfl) ⟨813744, by rfl⟩ : syracuseStep 2169985 = 1627489) B1627489
theorem B14097539 : Blo 948586 14097539 := bstep (se 1 (by rfl) ⟨10573154, by rfl⟩ : syracuseStep 14097539 = 21146309) B21146309
theorem B2137355 : Blo 948586 2137355 := bstep (se 1 (by rfl) ⟨1603016, by rfl⟩ : syracuseStep 2137355 = 3206033) B3206033
theorem B2137409 : Blo 948586 2137409 := bstep (se 2 (by rfl) ⟨801528, by rfl⟩ : syracuseStep 2137409 = 1603057) B1603057
theorem B2137625 : Blo 948586 2137625 := bstep (se 2 (by rfl) ⟨801609, by rfl⟩ : syracuseStep 2137625 = 1603219) B1603219
theorem B5414465 : Blo 948586 5414465 := bstep (se 2 (by rfl) ⟨2030424, by rfl⟩ : syracuseStep 5414465 = 4060849) B4060849
theorem B2137715 : Blo 948586 2137715 := bstep (se 1 (by rfl) ⟨1603286, by rfl⟩ : syracuseStep 2137715 = 3206573) B3206573
theorem B2137751 : Blo 948586 2137751 := bstep (se 1 (by rfl) ⟨1603313, by rfl⟩ : syracuseStep 2137751 = 3206627) B3206627
theorem B3612377 : Blo 948586 3612377 := bstep (se 2 (by rfl) ⟨1354641, by rfl⟩ : syracuseStep 3612377 = 2709283) B2709283
theorem B13016837 : Blo 948586 13016837 := bstep (se 4 (by rfl) ⟨1220328, by rfl⟩ : syracuseStep 13016837 = 2440657) B2440657
theorem B2137931 : Blo 948586 2137931 := bstep (se 1 (by rfl) ⟨1603448, by rfl⟩ : syracuseStep 2137931 = 3206897) B3206897
theorem B2137985 : Blo 948586 2137985 := bstep (se 2 (by rfl) ⟨801744, by rfl⟩ : syracuseStep 2137985 = 1603489) B1603489
theorem B2138201 : Blo 948586 2138201 := bstep (se 2 (by rfl) ⟨801825, by rfl⟩ : syracuseStep 2138201 = 1603651) B1603651
theorem B2138291 : Blo 948586 2138291 := bstep (se 1 (by rfl) ⟨1603718, by rfl⟩ : syracuseStep 2138291 = 3207437) B3207437
theorem B2138327 : Blo 948586 2138327 := bstep (se 1 (by rfl) ⟨1603745, by rfl⟩ : syracuseStep 2138327 = 3207491) B3207491
theorem B2138507 : Blo 948586 2138507 := bstep (se 1 (by rfl) ⟨1603880, by rfl⟩ : syracuseStep 2138507 = 3207761) B3207761
theorem B7217585 : Blo 948586 7217585 := bstep (se 2 (by rfl) ⟨2706594, by rfl⟩ : syracuseStep 7217585 = 5413189) B5413189
theorem B2138561 : Blo 948586 2138561 := bstep (se 2 (by rfl) ⟨801960, by rfl⟩ : syracuseStep 2138561 = 1603921) B1603921
theorem B1352153 : Blo 948586 1352153 := bstep (se 2 (by rfl) ⟨507057, by rfl⟩ : syracuseStep 1352153 = 1014115) B1014115
theorem B2138777 : Blo 948586 2138777 := bstep (se 2 (by rfl) ⟨802041, by rfl⟩ : syracuseStep 2138777 = 1604083) B1604083
theorem B2171609 : Blo 948586 2171609 := bstep (se 2 (by rfl) ⟨814353, by rfl⟩ : syracuseStep 2171609 = 1628707) B1628707
theorem B3089117 : Blo 948586 3089117 := bstep (se 3 (by rfl) ⟨579209, by rfl⟩ : syracuseStep 3089117 = 1158419) B1158419
theorem B2138867 : Blo 948586 2138867 := bstep (se 1 (by rfl) ⟨1604150, by rfl⟩ : syracuseStep 2138867 = 3208301) B3208301
theorem B2138903 : Blo 948586 2138903 := bstep (se 1 (by rfl) ⟨1604177, by rfl⟩ : syracuseStep 2138903 = 3208355) B3208355
theorem B7218071 : Blo 948586 7218071 := bstep (se 1 (by rfl) ⟨5413553, by rfl⟩ : syracuseStep 7218071 = 10827107) B10827107
theorem B2139083 : Blo 948586 2139083 := bstep (se 1 (by rfl) ⟨1604312, by rfl⟩ : syracuseStep 2139083 = 3208625) B3208625
theorem B2139137 : Blo 948586 2139137 := bstep (se 2 (by rfl) ⟨802176, by rfl⟩ : syracuseStep 2139137 = 1604353) B1604353
theorem B1647641 : Blo 948586 1647641 := bstep (se 2 (by rfl) ⟨617865, by rfl⟩ : syracuseStep 1647641 = 1235731) B1235731
theorem B1352791 : Blo 948586 1352791 := bstep (se 1 (by rfl) ⟨1014593, by rfl⟩ : syracuseStep 1352791 = 2029187) B2029187
theorem B1287257 : Blo 948586 1287257 := bstep (se 2 (by rfl) ⟨482721, by rfl⟩ : syracuseStep 1287257 = 965443) B965443
theorem B2139353 : Blo 948586 2139353 := bstep (se 2 (by rfl) ⟨802257, by rfl⟩ : syracuseStep 2139353 = 1604515) B1604515
theorem B2401559 : Blo 948586 2401559 := bstep (se 1 (by rfl) ⟨1801169, by rfl⟩ : syracuseStep 2401559 = 3602339) B3602339
theorem B1713431 : Blo 948586 1713431 := bstep (se 1 (by rfl) ⟨1285073, by rfl⟩ : syracuseStep 1713431 = 2570147) B2570147
theorem B2139443 : Blo 948586 2139443 := bstep (se 1 (by rfl) ⟨1604582, by rfl⟩ : syracuseStep 2139443 = 3209165) B3209165
theorem B3614003 : Blo 948586 3614003 := bstep (se 1 (by rfl) ⟨2710502, by rfl⟩ : syracuseStep 3614003 = 5421005) B5421005
theorem B3614017 : Blo 948586 3614017 := bstep (se 2 (by rfl) ⟨1355256, by rfl⟩ : syracuseStep 3614017 = 2710513) B2710513
theorem B2139479 : Blo 948586 2139479 := bstep (se 1 (by rfl) ⟨1604609, by rfl⟩ : syracuseStep 2139479 = 3209219) B3209219
theorem B2139659 : Blo 948586 2139659 := bstep (se 1 (by rfl) ⟨1604744, by rfl⟩ : syracuseStep 2139659 = 3209489) B3209489
theorem B2139713 : Blo 948586 2139713 := bstep (se 2 (by rfl) ⟨802392, by rfl⟩ : syracuseStep 2139713 = 1604785) B1604785
theorem B2139929 : Blo 948586 2139929 := bstep (se 2 (by rfl) ⟨802473, by rfl⟩ : syracuseStep 2139929 = 1604947) B1604947
theorem B2140019 : Blo 948586 2140019 := bstep (se 1 (by rfl) ⟨1605014, by rfl⟩ : syracuseStep 2140019 = 3210029) B3210029
theorem B1353611 : Blo 948586 1353611 := bstep (se 1 (by rfl) ⟨1015208, by rfl⟩ : syracuseStep 1353611 = 2030417) B2030417
theorem B2566039 : Blo 948586 2566039 := bstep (se 1 (by rfl) ⟨1924529, by rfl⟩ : syracuseStep 2566039 = 3849059) B3849059
theorem B2140055 : Blo 948586 2140055 := bstep (se 1 (by rfl) ⟨1605041, by rfl⟩ : syracuseStep 2140055 = 3210083) B3210083
theorem B2402369 : Blo 948586 2402369 := bstep (se 2 (by rfl) ⟨900888, by rfl⟩ : syracuseStep 2402369 = 1801777) B1801777
theorem B2140235 : Blo 948586 2140235 := bstep (se 1 (by rfl) ⟨1605176, by rfl⟩ : syracuseStep 2140235 = 3210353) B3210353
theorem B2140289 : Blo 948586 2140289 := bstep (se 2 (by rfl) ⟨802608, by rfl⟩ : syracuseStep 2140289 = 1605217) B1605217
theorem B3516689 : Blo 948586 3516689 := bstep (se 2 (by rfl) ⟨1318758, by rfl⟩ : syracuseStep 3516689 = 2637517) B2637517
theorem B49293613 : Blo 948586 49293613 := bstep (se 3 (by rfl) ⟨9242552, by rfl⟩ : syracuseStep 49293613 = 18485105) B18485105
theorem B2140505 : Blo 948586 2140505 := bstep (se 2 (by rfl) ⟨802689, by rfl⟩ : syracuseStep 2140505 = 1605379) B1605379
theorem B2140595 : Blo 948586 2140595 := bstep (se 1 (by rfl) ⟨1605446, by rfl⟩ : syracuseStep 2140595 = 3210893) B3210893
theorem B2140631 : Blo 948586 2140631 := bstep (se 1 (by rfl) ⟨1605473, by rfl⟩ : syracuseStep 2140631 = 3210947) B3210947
theorem B15608389 : Blo 948586 15608389 := bstep (se 4 (by rfl) ⟨1463286, by rfl⟩ : syracuseStep 15608389 = 2926573) B2926573
theorem B2402905 : Blo 948586 2402905 := bstep (se 2 (by rfl) ⟨901089, by rfl⟩ : syracuseStep 2402905 = 1802179) B1802179
theorem B2140811 : Blo 948586 2140811 := bstep (se 1 (by rfl) ⟨1605608, by rfl⟩ : syracuseStep 2140811 = 3211217) B3211217
theorem B2140865 : Blo 948586 2140865 := bstep (se 2 (by rfl) ⟨802824, by rfl⟩ : syracuseStep 2140865 = 1605649) B1605649
theorem B1354585 : Blo 948586 1354585 := bstep (se 2 (by rfl) ⟨507969, by rfl⟩ : syracuseStep 1354585 = 1015939) B1015939
theorem B6499223 : Blo 948586 6499223 := bstep (se 1 (by rfl) ⟨4874417, by rfl⟩ : syracuseStep 6499223 = 9748835) B9748835
theorem B2141081 : Blo 948586 2141081 := bstep (se 2 (by rfl) ⟨802905, by rfl⟩ : syracuseStep 2141081 = 1605811) B1605811
theorem B2894771 : Blo 948586 2894771 := bstep (se 1 (by rfl) ⟨2171078, by rfl⟩ : syracuseStep 2894771 = 4342157) B4342157
theorem B1715161 : Blo 948586 1715161 := bstep (se 2 (by rfl) ⟨643185, by rfl⟩ : syracuseStep 1715161 = 1286371) B1286371
theorem B2141171 : Blo 948586 2141171 := bstep (se 1 (by rfl) ⟨1605878, by rfl⟩ : syracuseStep 2141171 = 3211757) B3211757
theorem B2141207 : Blo 948586 2141207 := bstep (se 1 (by rfl) ⟨1605905, by rfl⟩ : syracuseStep 2141207 = 3211811) B3211811
theorem B2141387 : Blo 948586 2141387 := bstep (se 1 (by rfl) ⟨1606040, by rfl⟩ : syracuseStep 2141387 = 3212081) B3212081
theorem B3615947 : Blo 948586 3615947 := bstep (se 1 (by rfl) ⟨2711960, by rfl⟩ : syracuseStep 3615947 = 5423921) B5423921
theorem B3615961 : Blo 948586 3615961 := bstep (se 2 (by rfl) ⟨1355985, by rfl⟩ : syracuseStep 3615961 = 2711971) B2711971
theorem B2141441 : Blo 948586 2141441 := bstep (se 2 (by rfl) ⟨803040, by rfl⟩ : syracuseStep 2141441 = 1606081) B1606081
theorem B2141657 : Blo 948586 2141657 := bstep (se 2 (by rfl) ⟨803121, by rfl⟩ : syracuseStep 2141657 = 1606243) B1606243
theorem B2141747 : Blo 948586 2141747 := bstep (se 1 (by rfl) ⟨1606310, by rfl⟩ : syracuseStep 2141747 = 3212621) B3212621
theorem B4566593 : Blo 948586 4566593 := bstep (se 2 (by rfl) ⟨1712472, by rfl⟩ : syracuseStep 4566593 = 3424945) B3424945
theorem B2141783 : Blo 948586 2141783 := bstep (se 1 (by rfl) ⟨1606337, by rfl⟩ : syracuseStep 2141783 = 3212675) B3212675
theorem B2404019 : Blo 948586 2404019 := bstep (se 1 (by rfl) ⟨1803014, by rfl⟩ : syracuseStep 2404019 = 3606029) B3606029
theorem B2141963 : Blo 948586 2141963 := bstep (se 1 (by rfl) ⟨1606472, by rfl⟩ : syracuseStep 2141963 = 3212945) B3212945
theorem B2142017 : Blo 948586 2142017 := bstep (se 2 (by rfl) ⟨803256, by rfl⟩ : syracuseStep 2142017 = 1606513) B1606513
theorem B31272803 : Blo 948586 31272803 := bstep (se 1 (by rfl) ⟨23454602, by rfl⟩ : syracuseStep 31272803 = 46909205) B46909205
theorem B10825649 : Blo 948586 10825649 := bstep (se 2 (by rfl) ⟨4059618, by rfl⟩ : syracuseStep 10825649 = 8119237) B8119237
theorem B1355735 : Blo 948586 1355735 := bstep (se 1 (by rfl) ⟨1016801, by rfl⟩ : syracuseStep 1355735 = 2033603) B2033603
theorem B2404313 : Blo 948586 2404313 := bstep (se 2 (by rfl) ⟨901617, by rfl⟩ : syracuseStep 2404313 = 1803235) B1803235
theorem B2142233 : Blo 948586 2142233 := bstep (se 2 (by rfl) ⟨803337, by rfl⟩ : syracuseStep 2142233 = 1606675) B1606675
theorem B15446051 : Blo 948586 15446051 := bstep (se 1 (by rfl) ⟨11584538, by rfl⟩ : syracuseStep 15446051 = 23169077) B23169077
theorem B2142323 : Blo 948586 2142323 := bstep (se 1 (by rfl) ⟨1606742, by rfl⟩ : syracuseStep 2142323 = 3213485) B3213485
theorem B8106115 : Blo 948586 8106115 := bstep (se 1 (by rfl) ⟨6079586, by rfl⟩ : syracuseStep 8106115 = 12159173) B12159173
theorem B2142359 : Blo 948586 2142359 := bstep (se 1 (by rfl) ⟨1606769, by rfl⟩ : syracuseStep 2142359 = 3213539) B3213539
theorem B1519769 : Blo 948586 1519769 := bstep (se 2 (by rfl) ⟨569913, by rfl⟩ : syracuseStep 1519769 = 1139827) B1139827
theorem B1356043 : Blo 948586 1356043 := bstep (se 1 (by rfl) ⟨1017032, by rfl⟩ : syracuseStep 1356043 = 2034065) B2034065
theorem B3420461 : Blo 948586 3420461 := bstep (se 3 (by rfl) ⟨641336, by rfl⟩ : syracuseStep 3420461 = 1282673) B1282673
theorem B2142539 : Blo 948586 2142539 := bstep (se 1 (by rfl) ⟨1606904, by rfl⟩ : syracuseStep 2142539 = 3213809) B3213809
theorem B2142593 : Blo 948586 2142593 := bstep (se 2 (by rfl) ⟨803472, by rfl⟩ : syracuseStep 2142593 = 1606945) B1606945
theorem B2142809 : Blo 948586 2142809 := bstep (se 2 (by rfl) ⟨803553, by rfl⟩ : syracuseStep 2142809 = 1607107) B1607107
theorem B2142899 : Blo 948586 2142899 := bstep (se 1 (by rfl) ⟨1607174, by rfl⟩ : syracuseStep 2142899 = 3214349) B3214349
theorem B2142935 : Blo 948586 2142935 := bstep (se 1 (by rfl) ⟨1607201, by rfl⟩ : syracuseStep 2142935 = 3214403) B3214403
theorem B2143115 : Blo 948586 2143115 := bstep (se 1 (by rfl) ⟨1607336, by rfl⟩ : syracuseStep 2143115 = 3214673) B3214673
theorem B3814289 : Blo 948586 3814289 := bstep (se 2 (by rfl) ⟨1430358, by rfl⟩ : syracuseStep 3814289 = 2860717) B2860717
theorem B2143169 : Blo 948586 2143169 := bstep (se 2 (by rfl) ⟨803688, by rfl⟩ : syracuseStep 2143169 = 1607377) B1607377
theorem B3519533 : Blo 948586 3519533 := bstep (se 3 (by rfl) ⟨659912, by rfl⟩ : syracuseStep 3519533 = 1319825) B1319825
theorem B8107073 : Blo 948586 8107073 := bstep (se 2 (by rfl) ⟨3040152, by rfl⟩ : syracuseStep 8107073 = 6080305) B6080305
theorem B7714199 : Blo 948586 7714199 := bstep (se 1 (by rfl) ⟨5785649, by rfl⟩ : syracuseStep 7714199 = 11571299) B11571299
theorem B3421613 : Blo 948586 3421613 := bstep (se 3 (by rfl) ⟨641552, by rfl⟩ : syracuseStep 3421613 = 1283105) B1283105
theorem B6862259 : Blo 948586 6862259 := bstep (se 1 (by rfl) ⟨5146694, by rfl⟩ : syracuseStep 6862259 = 10293389) B10293389
theorem B1422923 : Blo 948586 1422923 := bstep (se 1 (by rfl) ⟨1067192, by rfl⟩ : syracuseStep 1422923 = 2134385) B2134385
theorem B2405963 : Blo 948586 2405963 := bstep (se 1 (by rfl) ⟨1804472, by rfl⟩ : syracuseStep 2405963 = 3608945) B3608945
theorem B1422935 : Blo 948586 1422935 := bstep (se 1 (by rfl) ⟨1067201, by rfl⟩ : syracuseStep 1422935 = 2134403) B2134403
theorem B1423001 : Blo 948586 1423001 := bstep (se 2 (by rfl) ⟨533625, by rfl⟩ : syracuseStep 1423001 = 1067251) B1067251
theorem B3847873 : Blo 948586 3847873 := bstep (se 2 (by rfl) ⟨1442952, by rfl⟩ : syracuseStep 3847873 = 2885905) B2885905
theorem B2569931 : Blo 948586 2569931 := bstep (se 1 (by rfl) ⟨1927448, by rfl⟩ : syracuseStep 2569931 = 3854897) B3854897
theorem B1423115 : Blo 948586 1423115 := bstep (se 1 (by rfl) ⟨1067336, by rfl⟩ : syracuseStep 1423115 = 2134673) B2134673
theorem B1423127 : Blo 948586 1423127 := bstep (se 1 (by rfl) ⟨1067345, by rfl⟩ : syracuseStep 1423127 = 2134691) B2134691
theorem B3422017 : Blo 948586 3422017 := bstep (se 2 (by rfl) ⟨1283256, by rfl⟩ : syracuseStep 3422017 = 2566513) B2566513
theorem B1423193 : Blo 948586 1423193 := bstep (se 2 (by rfl) ⟨533697, by rfl⟩ : syracuseStep 1423193 = 1067395) B1067395
theorem B1423307 : Blo 948586 1423307 := bstep (se 1 (by rfl) ⟨1067480, by rfl⟩ : syracuseStep 1423307 = 2134961) B2134961
theorem B1423319 : Blo 948586 1423319 := bstep (se 1 (by rfl) ⟨1067489, by rfl⟩ : syracuseStep 1423319 = 2134979) B2134979
theorem B1423385 : Blo 948586 1423385 := bstep (se 2 (by rfl) ⟨533769, by rfl⟩ : syracuseStep 1423385 = 1067539) B1067539
theorem B24393797 : Blo 948586 24393797 := bstep (se 4 (by rfl) ⟨2286918, by rfl⟩ : syracuseStep 24393797 = 4573837) B4573837
theorem B1423499 : Blo 948586 1423499 := bstep (se 1 (by rfl) ⟨1067624, by rfl⟩ : syracuseStep 1423499 = 2135249) B2135249
theorem B1423511 : Blo 948586 1423511 := bstep (se 1 (by rfl) ⟨1067633, by rfl⟩ : syracuseStep 1423511 = 2135267) B2135267
theorem B1423577 : Blo 948586 1423577 := bstep (se 2 (by rfl) ⟨533841, by rfl⟩ : syracuseStep 1423577 = 1067683) B1067683
theorem B1423691 : Blo 948586 1423691 := bstep (se 1 (by rfl) ⟨1067768, by rfl⟩ : syracuseStep 1423691 = 2135537) B2135537
theorem B1423703 : Blo 948586 1423703 := bstep (se 1 (by rfl) ⟨1067777, by rfl⟩ : syracuseStep 1423703 = 2135555) B2135555
theorem B1423769 : Blo 948586 1423769 := bstep (se 2 (by rfl) ⟨533913, by rfl⟩ : syracuseStep 1423769 = 1067827) B1067827
theorem B12368305 : Blo 948586 12368305 := bstep (se 2 (by rfl) ⟨4638114, by rfl⟩ : syracuseStep 12368305 = 9276229) B9276229
theorem B1423883 : Blo 948586 1423883 := bstep (se 1 (by rfl) ⟨1067912, by rfl⟩ : syracuseStep 1423883 = 2135825) B2135825
theorem B1423895 : Blo 948586 1423895 := bstep (se 1 (by rfl) ⟨1067921, by rfl⟩ : syracuseStep 1423895 = 2135843) B2135843
theorem B2406935 : Blo 948586 2406935 := bstep (se 1 (by rfl) ⟨1805201, by rfl⟩ : syracuseStep 2406935 = 3610403) B3610403
theorem B4340299 : Blo 948586 4340299 := bstep (se 1 (by rfl) ⟨3255224, by rfl⟩ : syracuseStep 4340299 = 6510449) B6510449
theorem B1423961 : Blo 948586 1423961 := bstep (se 2 (by rfl) ⟨533985, by rfl⟩ : syracuseStep 1423961 = 1067971) B1067971
theorem B1424075 : Blo 948586 1424075 := bstep (se 1 (by rfl) ⟨1068056, by rfl⟩ : syracuseStep 1424075 = 2136113) B2136113
theorem B1424087 : Blo 948586 1424087 := bstep (se 1 (by rfl) ⟨1068065, by rfl⟩ : syracuseStep 1424087 = 2136131) B2136131
theorem B4111127 : Blo 948586 4111127 := bstep (se 1 (by rfl) ⟨3083345, by rfl⟩ : syracuseStep 4111127 = 6166691) B6166691
theorem B1424153 : Blo 948586 1424153 := bstep (se 2 (by rfl) ⟨534057, by rfl⟩ : syracuseStep 1424153 = 1068115) B1068115
theorem B1424267 : Blo 948586 1424267 := bstep (se 1 (by rfl) ⟨1068200, by rfl⟩ : syracuseStep 1424267 = 2136401) B2136401
theorem B1424279 : Blo 948586 1424279 := bstep (se 1 (by rfl) ⟨1068209, by rfl⟩ : syracuseStep 1424279 = 2136419) B2136419
theorem B1424345 : Blo 948586 1424345 := bstep (se 2 (by rfl) ⟨534129, by rfl⟩ : syracuseStep 1424345 = 1068259) B1068259
theorem B1424459 : Blo 948586 1424459 := bstep (se 1 (by rfl) ⟨1068344, by rfl⟩ : syracuseStep 1424459 = 2136689) B2136689
theorem B1424471 : Blo 948586 1424471 := bstep (se 1 (by rfl) ⟨1068353, by rfl⟩ : syracuseStep 1424471 = 2136707) B2136707
theorem B5422211 : Blo 948586 5422211 := bstep (se 1 (by rfl) ⟨4066658, by rfl⟩ : syracuseStep 5422211 = 8133317) B8133317
theorem B1424537 : Blo 948586 1424537 := bstep (se 2 (by rfl) ⟨534201, by rfl⟩ : syracuseStep 1424537 = 1068403) B1068403
theorem B2407603 : Blo 948586 2407603 := bstep (se 1 (by rfl) ⟨1805702, by rfl⟩ : syracuseStep 2407603 = 3611405) B3611405
theorem B1424651 : Blo 948586 1424651 := bstep (se 1 (by rfl) ⟨1068488, by rfl⟩ : syracuseStep 1424651 = 2136977) B2136977
theorem B1424663 : Blo 948586 1424663 := bstep (se 1 (by rfl) ⟨1068497, by rfl⟩ : syracuseStep 1424663 = 2136995) B2136995
theorem B2407745 : Blo 948586 2407745 := bstep (se 2 (by rfl) ⟨902904, by rfl⟩ : syracuseStep 2407745 = 1805809) B1805809
theorem B1424729 : Blo 948586 1424729 := bstep (se 2 (by rfl) ⟨534273, by rfl⟩ : syracuseStep 1424729 = 1068547) B1068547
theorem B1424843 : Blo 948586 1424843 := bstep (se 1 (by rfl) ⟨1068632, by rfl⟩ : syracuseStep 1424843 = 2137265) B2137265
theorem B1424855 : Blo 948586 1424855 := bstep (se 1 (by rfl) ⟨1068641, by rfl⟩ : syracuseStep 1424855 = 2137283) B2137283
theorem B1424921 : Blo 948586 1424921 := bstep (se 2 (by rfl) ⟨534345, by rfl⟩ : syracuseStep 1424921 = 1068691) B1068691
theorem B1425035 : Blo 948586 1425035 := bstep (se 1 (by rfl) ⟨1068776, by rfl⟩ : syracuseStep 1425035 = 2137553) B2137553
theorem B1425047 : Blo 948586 1425047 := bstep (se 1 (by rfl) ⟨1068785, by rfl⟩ : syracuseStep 1425047 = 2137571) B2137571
theorem B2703041 : Blo 948586 2703041 := bstep (se 2 (by rfl) ⟨1013640, by rfl⟩ : syracuseStep 2703041 = 2027281) B2027281
theorem B1425113 : Blo 948586 1425113 := bstep (se 2 (by rfl) ⟨534417, by rfl⟩ : syracuseStep 1425113 = 1068835) B1068835
theorem B1425227 : Blo 948586 1425227 := bstep (se 1 (by rfl) ⟨1068920, by rfl⟩ : syracuseStep 1425227 = 2137841) B2137841
theorem B1523531 : Blo 948586 1523531 := bstep (se 1 (by rfl) ⟨1142648, by rfl⟩ : syracuseStep 1523531 = 2285297) B2285297
theorem B1425239 : Blo 948586 1425239 := bstep (se 1 (by rfl) ⟨1068929, by rfl⟩ : syracuseStep 1425239 = 2137859) B2137859
theorem B1425305 : Blo 948586 1425305 := bstep (se 2 (by rfl) ⟨534489, by rfl⟩ : syracuseStep 1425305 = 1068979) B1068979
theorem B1425419 : Blo 948586 1425419 := bstep (se 1 (by rfl) ⟨1069064, by rfl⟩ : syracuseStep 1425419 = 2138129) B2138129
theorem B7225361 : Blo 948586 7225361 := bstep (se 2 (by rfl) ⟨2709510, by rfl⟩ : syracuseStep 7225361 = 5419021) B5419021
theorem B1425431 : Blo 948586 1425431 := bstep (se 1 (by rfl) ⟨1069073, by rfl⟩ : syracuseStep 1425431 = 2138147) B2138147
theorem B43827275 : Blo 948586 43827275 := bstep (se 1 (by rfl) ⟨32870456, by rfl⟩ : syracuseStep 43827275 = 65740913) B65740913
theorem B1425497 : Blo 948586 1425497 := bstep (se 2 (by rfl) ⟨534561, by rfl⟩ : syracuseStep 1425497 = 1069123) B1069123
theorem B1425611 : Blo 948586 1425611 := bstep (se 1 (by rfl) ⟨1069208, by rfl⟩ : syracuseStep 1425611 = 2138417) B2138417
theorem B1425623 : Blo 948586 1425623 := bstep (se 1 (by rfl) ⟨1069217, by rfl⟩ : syracuseStep 1425623 = 2138435) B2138435
theorem B2703577 : Blo 948586 2703577 := bstep (se 2 (by rfl) ⟨1013841, by rfl⟩ : syracuseStep 2703577 = 2027683) B2027683
theorem B1425689 : Blo 948586 1425689 := bstep (se 2 (by rfl) ⟨534633, by rfl⟩ : syracuseStep 1425689 = 1069267) B1069267
theorem B1524043 : Blo 948586 1524043 := bstep (se 1 (by rfl) ⟨1143032, by rfl⟩ : syracuseStep 1524043 = 2286065) B2286065
theorem B1425803 : Blo 948586 1425803 := bstep (se 1 (by rfl) ⟨1069352, by rfl⟩ : syracuseStep 1425803 = 2138705) B2138705
theorem B1425815 : Blo 948586 1425815 := bstep (se 1 (by rfl) ⟨1069361, by rfl⟩ : syracuseStep 1425815 = 2138723) B2138723
theorem B1425881 : Blo 948586 1425881 := bstep (se 2 (by rfl) ⟨534705, by rfl⟩ : syracuseStep 1425881 = 1069411) B1069411
theorem B2409011 : Blo 948586 2409011 := bstep (se 1 (by rfl) ⟨1806758, by rfl⟩ : syracuseStep 2409011 = 3613517) B3613517
theorem B1425995 : Blo 948586 1425995 := bstep (se 1 (by rfl) ⟨1069496, by rfl⟩ : syracuseStep 1425995 = 2138993) B2138993
theorem B1426007 : Blo 948586 1426007 := bstep (se 1 (by rfl) ⟨1069505, by rfl⟩ : syracuseStep 1426007 = 2139011) B2139011
theorem B1426073 : Blo 948586 1426073 := bstep (se 2 (by rfl) ⟨534777, by rfl⟩ : syracuseStep 1426073 = 1069555) B1069555
theorem B1426187 : Blo 948586 1426187 := bstep (se 1 (by rfl) ⟨1069640, by rfl⟩ : syracuseStep 1426187 = 2139281) B2139281
theorem B1426199 : Blo 948586 1426199 := bstep (se 1 (by rfl) ⟨1069649, by rfl⟩ : syracuseStep 1426199 = 2139299) B2139299
theorem B3425075 : Blo 948586 3425075 := bstep (se 1 (by rfl) ⟨2568806, by rfl⟩ : syracuseStep 3425075 = 5137613) B5137613
theorem B1426265 : Blo 948586 1426265 := bstep (se 2 (by rfl) ⟨534849, by rfl⟩ : syracuseStep 1426265 = 1069699) B1069699
theorem B1426379 : Blo 948586 1426379 := bstep (se 1 (by rfl) ⟨1069784, by rfl⟩ : syracuseStep 1426379 = 2139569) B2139569
theorem B1426391 : Blo 948586 1426391 := bstep (se 1 (by rfl) ⟨1069793, by rfl⟩ : syracuseStep 1426391 = 2139587) B2139587
theorem B1426457 : Blo 948586 1426457 := bstep (se 2 (by rfl) ⟨534921, by rfl⟩ : syracuseStep 1426457 = 1069843) B1069843
theorem B1524761 : Blo 948586 1524761 := bstep (se 2 (by rfl) ⟨571785, by rfl⟩ : syracuseStep 1524761 = 1143571) B1143571
theorem B2409547 : Blo 948586 2409547 := bstep (se 1 (by rfl) ⟨1807160, by rfl⟩ : syracuseStep 2409547 = 3614321) B3614321
theorem B11551837 : Blo 948586 11551837 := bstep (se 3 (by rfl) ⟨2165969, by rfl⟩ : syracuseStep 11551837 = 4331939) B4331939
theorem B1426571 : Blo 948586 1426571 := bstep (se 1 (by rfl) ⟨1069928, by rfl⟩ : syracuseStep 1426571 = 2139857) B2139857
theorem B1426583 : Blo 948586 1426583 := bstep (se 1 (by rfl) ⟨1069937, by rfl⟩ : syracuseStep 1426583 = 2139875) B2139875
theorem B1426649 : Blo 948586 1426649 := bstep (se 2 (by rfl) ⟨534993, by rfl⟩ : syracuseStep 1426649 = 1069987) B1069987
theorem B2409689 : Blo 948586 2409689 := bstep (se 2 (by rfl) ⟨903633, by rfl⟩ : syracuseStep 2409689 = 1807267) B1807267
theorem B1099019 : Blo 948586 1099019 := bstep (se 1 (by rfl) ⟨824264, by rfl⟩ : syracuseStep 1099019 = 1648529) B1648529
theorem B1951001 : Blo 948586 1951001 := bstep (se 2 (by rfl) ⟨731625, by rfl⟩ : syracuseStep 1951001 = 1463251) B1463251
theorem B12993857 : Blo 948586 12993857 := bstep (se 2 (by rfl) ⟨4872696, by rfl⟩ : syracuseStep 12993857 = 9745393) B9745393
theorem B1426763 : Blo 948586 1426763 := bstep (se 1 (by rfl) ⟨1070072, by rfl⟩ : syracuseStep 1426763 = 2140145) B2140145
theorem B1426775 : Blo 948586 1426775 := bstep (se 1 (by rfl) ⟨1070081, by rfl⟩ : syracuseStep 1426775 = 2140163) B2140163
theorem B1099127 : Blo 948586 1099127 := bstep (se 1 (by rfl) ⟨824345, by rfl⟩ : syracuseStep 1099127 = 1648691) B1648691
theorem B3851651 : Blo 948586 3851651 := bstep (se 1 (by rfl) ⟨2888738, by rfl⟩ : syracuseStep 3851651 = 5777477) B5777477
theorem B1426841 : Blo 948586 1426841 := bstep (se 2 (by rfl) ⟨535065, by rfl⟩ : syracuseStep 1426841 = 1070131) B1070131
theorem B3425753 : Blo 948586 3425753 := bstep (se 2 (by rfl) ⟨1284657, by rfl⟩ : syracuseStep 3425753 = 2569315) B2569315
theorem B1426955 : Blo 948586 1426955 := bstep (se 1 (by rfl) ⟨1070216, by rfl⟩ : syracuseStep 1426955 = 2140433) B2140433
theorem B1426967 : Blo 948586 1426967 := bstep (se 1 (by rfl) ⟨1070225, by rfl⟩ : syracuseStep 1426967 = 2140451) B2140451
theorem B1427033 : Blo 948586 1427033 := bstep (se 2 (by rfl) ⟨535137, by rfl⟩ : syracuseStep 1427033 = 1070275) B1070275
theorem B1427147 : Blo 948586 1427147 := bstep (se 1 (by rfl) ⟨1070360, by rfl⟩ : syracuseStep 1427147 = 2140721) B2140721
theorem B1427159 : Blo 948586 1427159 := bstep (se 1 (by rfl) ⟨1070369, by rfl⟩ : syracuseStep 1427159 = 2140739) B2140739
theorem B1427225 : Blo 948586 1427225 := bstep (se 2 (by rfl) ⟨535209, by rfl⟩ : syracuseStep 1427225 = 1070419) B1070419
theorem B1427339 : Blo 948586 1427339 := bstep (se 1 (by rfl) ⟨1070504, by rfl⟩ : syracuseStep 1427339 = 2141009) B2141009
theorem B1427351 : Blo 948586 1427351 := bstep (se 1 (by rfl) ⟨1070513, by rfl⟩ : syracuseStep 1427351 = 2141027) B2141027
theorem B1427417 : Blo 948586 1427417 := bstep (se 2 (by rfl) ⟨535281, by rfl⟩ : syracuseStep 1427417 = 1070563) B1070563
theorem B2934749 : Blo 948586 2934749 := bstep (se 3 (by rfl) ⟨550265, by rfl⟩ : syracuseStep 2934749 = 1100531) B1100531
theorem B2410519 : Blo 948586 2410519 := bstep (se 1 (by rfl) ⟨1807889, by rfl⟩ : syracuseStep 2410519 = 3615779) B3615779
theorem B1427531 : Blo 948586 1427531 := bstep (se 1 (by rfl) ⟨1070648, by rfl⟩ : syracuseStep 1427531 = 2141297) B2141297
theorem B1427543 : Blo 948586 1427543 := bstep (se 1 (by rfl) ⟨1070657, by rfl⟩ : syracuseStep 1427543 = 2141315) B2141315
theorem B2705501 : Blo 948586 2705501 := bstep (se 3 (by rfl) ⟨507281, by rfl⟩ : syracuseStep 2705501 = 1014563) B1014563
theorem B1427609 : Blo 948586 1427609 := bstep (se 2 (by rfl) ⟨535353, by rfl⟩ : syracuseStep 1427609 = 1070707) B1070707
theorem B1067179 : Blo 948586 1067179 := bstep (se 1 (by rfl) ⟨800384, by rfl⟩ : syracuseStep 1067179 = 1600769) B1600769
theorem B8800435 : Blo 948586 8800435 := bstep (se 1 (by rfl) ⟨6600326, by rfl⟩ : syracuseStep 8800435 = 13200653) B13200653
theorem B1427723 : Blo 948586 1427723 := bstep (se 1 (by rfl) ⟨1070792, by rfl⟩ : syracuseStep 1427723 = 2141585) B2141585
theorem B1067287 : Blo 948586 1067287 := bstep (se 1 (by rfl) ⟨800465, by rfl⟩ : syracuseStep 1067287 = 1600931) B1600931
theorem B1427735 : Blo 948586 1427735 := bstep (se 1 (by rfl) ⟨1070801, by rfl⟩ : syracuseStep 1427735 = 2141603) B2141603
theorem B1427801 : Blo 948586 1427801 := bstep (se 2 (by rfl) ⟨535425, by rfl⟩ : syracuseStep 1427801 = 1070851) B1070851
theorem B1067467 : Blo 948586 1067467 := bstep (se 1 (by rfl) ⟨800600, by rfl⟩ : syracuseStep 1067467 = 1601201) B1601201
theorem B1427915 : Blo 948586 1427915 := bstep (se 1 (by rfl) ⟨1070936, by rfl⟩ : syracuseStep 1427915 = 2141873) B2141873
theorem B2410955 : Blo 948586 2410955 := bstep (se 1 (by rfl) ⟨1808216, by rfl⟩ : syracuseStep 2410955 = 3616433) B3616433
theorem B1427927 : Blo 948586 1427927 := bstep (se 1 (by rfl) ⟨1070945, by rfl⟩ : syracuseStep 1427927 = 2141891) B2141891
theorem B4639193 : Blo 948586 4639193 := bstep (se 2 (by rfl) ⟨1739697, by rfl⟩ : syracuseStep 4639193 = 3479395) B3479395
theorem B1427993 : Blo 948586 1427993 := bstep (se 2 (by rfl) ⟨535497, by rfl⟩ : syracuseStep 1427993 = 1070995) B1070995
theorem B1067575 : Blo 948586 1067575 := bstep (se 1 (by rfl) ⟨800681, by rfl⟩ : syracuseStep 1067575 = 1601363) B1601363
theorem B4803137 : Blo 948586 4803137 := bstep (se 2 (by rfl) ⟨1801176, by rfl⟩ : syracuseStep 4803137 = 3602353) B3602353
theorem B1428107 : Blo 948586 1428107 := bstep (se 1 (by rfl) ⟨1071080, by rfl⟩ : syracuseStep 1428107 = 2142161) B2142161
theorem B1428119 : Blo 948586 1428119 := bstep (se 1 (by rfl) ⟨1071089, by rfl⟩ : syracuseStep 1428119 = 2142179) B2142179
theorem B1428185 : Blo 948586 1428185 := bstep (se 2 (by rfl) ⟨535569, by rfl⟩ : syracuseStep 1428185 = 1071139) B1071139
theorem B1067755 : Blo 948586 1067755 := bstep (se 1 (by rfl) ⟨800816, by rfl⟩ : syracuseStep 1067755 = 1601633) B1601633
theorem B3853079 : Blo 948586 3853079 := bstep (se 1 (by rfl) ⟨2889809, by rfl⟩ : syracuseStep 3853079 = 5779619) B5779619
theorem B1428299 : Blo 948586 1428299 := bstep (se 1 (by rfl) ⟨1071224, by rfl⟩ : syracuseStep 1428299 = 2142449) B2142449
theorem B1067863 : Blo 948586 1067863 := bstep (se 1 (by rfl) ⟨800897, by rfl⟩ : syracuseStep 1067863 = 1601795) B1601795
theorem B1428311 : Blo 948586 1428311 := bstep (se 1 (by rfl) ⟨1071233, by rfl⟩ : syracuseStep 1428311 = 2142467) B2142467
theorem B3853145 : Blo 948586 3853145 := bstep (se 2 (by rfl) ⟨1444929, by rfl⟩ : syracuseStep 3853145 = 2889859) B2889859
theorem B1428377 : Blo 948586 1428377 := bstep (se 2 (by rfl) ⟨535641, by rfl⟩ : syracuseStep 1428377 = 1071283) B1071283
theorem B3427265 : Blo 948586 3427265 := bstep (se 2 (by rfl) ⟨1285224, by rfl⟩ : syracuseStep 3427265 = 2570449) B2570449
theorem B3525569 : Blo 948586 3525569 := bstep (se 2 (by rfl) ⟨1322088, by rfl⟩ : syracuseStep 3525569 = 2644177) B2644177
theorem B1068043 : Blo 948586 1068043 := bstep (se 1 (by rfl) ⟨801032, by rfl⟩ : syracuseStep 1068043 = 1602065) B1602065
theorem B1428491 : Blo 948586 1428491 := bstep (se 1 (by rfl) ⟨1071368, by rfl⟩ : syracuseStep 1428491 = 2142737) B2142737
theorem B1428503 : Blo 948586 1428503 := bstep (se 1 (by rfl) ⟨1071377, by rfl⟩ : syracuseStep 1428503 = 2142755) B2142755
theorem B1428569 : Blo 948586 1428569 := bstep (se 2 (by rfl) ⟨535713, by rfl⟩ : syracuseStep 1428569 = 1071427) B1071427
theorem B6081637 : Blo 948586 6081637 := bstep (se 4 (by rfl) ⟨570153, by rfl⟩ : syracuseStep 6081637 = 1140307) B1140307
theorem B1068151 : Blo 948586 1068151 := bstep (se 1 (by rfl) ⟨801113, by rfl⟩ : syracuseStep 1068151 = 1602227) B1602227
theorem B4574339 : Blo 948586 4574339 := bstep (se 1 (by rfl) ⟨3430754, by rfl⟩ : syracuseStep 4574339 = 6861509) B6861509
theorem B1428683 : Blo 948586 1428683 := bstep (se 1 (by rfl) ⟨1071512, by rfl⟩ : syracuseStep 1428683 = 2143025) B2143025
theorem B1428695 : Blo 948586 1428695 := bstep (se 1 (by rfl) ⟨1071521, by rfl⟩ : syracuseStep 1428695 = 2143043) B2143043
theorem B1428761 : Blo 948586 1428761 := bstep (se 2 (by rfl) ⟨535785, by rfl⟩ : syracuseStep 1428761 = 1071571) B1071571
theorem B1068331 : Blo 948586 1068331 := bstep (se 1 (by rfl) ⟨801248, by rfl⟩ : syracuseStep 1068331 = 1602497) B1602497
theorem B1428875 : Blo 948586 1428875 := bstep (se 1 (by rfl) ⟨1071656, by rfl⟩ : syracuseStep 1428875 = 2143313) B2143313
theorem B1068439 : Blo 948586 1068439 := bstep (se 1 (by rfl) ⟨801329, by rfl⟩ : syracuseStep 1068439 = 1602659) B1602659
theorem B17321485 : Blo 948586 17321485 := bstep (se 3 (by rfl) ⟨3247778, by rfl⟩ : syracuseStep 17321485 = 6495557) B6495557
theorem B8474147 : Blo 948586 8474147 := bstep (se 1 (by rfl) ⟨6355610, by rfl⟩ : syracuseStep 8474147 = 12711221) B12711221
theorem B1068619 : Blo 948586 1068619 := bstep (se 1 (by rfl) ⟨801464, by rfl⟩ : syracuseStep 1068619 = 1602929) B1602929
theorem B1068727 : Blo 948586 1068727 := bstep (se 1 (by rfl) ⟨801545, by rfl⟩ : syracuseStep 1068727 = 1603091) B1603091
theorem B7229249 : Blo 948586 7229249 := bstep (se 2 (by rfl) ⟨2710968, by rfl⟩ : syracuseStep 7229249 = 5421937) B5421937
theorem B3428189 : Blo 948586 3428189 := bstep (se 3 (by rfl) ⟨642785, by rfl⟩ : syracuseStep 3428189 = 1285571) B1285571
theorem B1068907 : Blo 948586 1068907 := bstep (se 1 (by rfl) ⟨801680, by rfl⟩ : syracuseStep 1068907 = 1603361) B1603361
theorem B1069015 : Blo 948586 1069015 := bstep (se 1 (by rfl) ⟨801761, by rfl⟩ : syracuseStep 1069015 = 1603523) B1603523
theorem B2281537 : Blo 948586 2281537 := bstep (se 2 (by rfl) ⟨855576, by rfl⟩ : syracuseStep 2281537 = 1711153) B1711153
theorem B3854411 : Blo 948586 3854411 := bstep (se 1 (by rfl) ⟨2890808, by rfl⟩ : syracuseStep 3854411 = 5781617) B5781617
theorem B1069195 : Blo 948586 1069195 := bstep (se 1 (by rfl) ⟨801896, by rfl⟩ : syracuseStep 1069195 = 1603793) B1603793
theorem B1069303 : Blo 948586 1069303 := bstep (se 1 (by rfl) ⟨801977, by rfl⟩ : syracuseStep 1069303 = 1603955) B1603955
theorem B1069483 : Blo 948586 1069483 := bstep (se 1 (by rfl) ⟨802112, by rfl⟩ : syracuseStep 1069483 = 1604225) B1604225
theorem B3854765 : Blo 948586 3854765 := bstep (se 3 (by rfl) ⟨722768, by rfl⟩ : syracuseStep 3854765 = 1445537) B1445537
theorem B4805081 : Blo 948586 4805081 := bstep (se 2 (by rfl) ⟨1801905, by rfl⟩ : syracuseStep 4805081 = 3603811) B3603811
theorem B3428867 : Blo 948586 3428867 := bstep (se 1 (by rfl) ⟨2571650, by rfl⟩ : syracuseStep 3428867 = 5143301) B5143301
theorem B1069591 : Blo 948586 1069591 := bstep (se 1 (by rfl) ⟨802193, by rfl⟩ : syracuseStep 1069591 = 1604387) B1604387
theorem B3428909 : Blo 948586 3428909 := bstep (se 3 (by rfl) ⟨642920, by rfl⟩ : syracuseStep 3428909 = 1285841) B1285841
theorem B1069771 : Blo 948586 1069771 := bstep (se 1 (by rfl) ⟨802328, by rfl⟩ : syracuseStep 1069771 = 1604657) B1604657
theorem B1069879 : Blo 948586 1069879 := bstep (se 1 (by rfl) ⟨802409, by rfl⟩ : syracuseStep 1069879 = 1604819) B1604819
theorem B2708417 : Blo 948586 2708417 := bstep (se 2 (by rfl) ⟨1015656, by rfl⟩ : syracuseStep 2708417 = 2031313) B2031313
theorem B2708441 : Blo 948586 2708441 := bstep (se 2 (by rfl) ⟨1015665, by rfl⟩ : syracuseStep 2708441 = 2031331) B2031331
theorem B1070059 : Blo 948586 1070059 := bstep (se 1 (by rfl) ⟨802544, by rfl⟩ : syracuseStep 1070059 = 1605089) B1605089
theorem B1070167 : Blo 948586 1070167 := bstep (se 1 (by rfl) ⟨802625, by rfl⟩ : syracuseStep 1070167 = 1605251) B1605251
theorem B6935645 : Blo 948586 6935645 := bstep (se 3 (by rfl) ⟨1300433, by rfl⟩ : syracuseStep 6935645 = 2600867) B2600867
theorem B1070347 : Blo 948586 1070347 := bstep (se 1 (by rfl) ⟨802760, by rfl⟩ : syracuseStep 1070347 = 1605521) B1605521
theorem B10966337 : Blo 948586 10966337 := bstep (se 2 (by rfl) ⟨4112376, by rfl⟩ : syracuseStep 10966337 = 8224753) B8224753
theorem B1201483 : Blo 948586 1201483 := bstep (se 1 (by rfl) ⟨901112, by rfl⟩ : syracuseStep 1201483 = 1802225) B1802225
theorem B1070455 : Blo 948586 1070455 := bstep (se 1 (by rfl) ⟨802841, by rfl⟩ : syracuseStep 1070455 = 1605683) B1605683
theorem B4052375 : Blo 948586 4052375 := bstep (se 1 (by rfl) ⟨3039281, by rfl⟩ : syracuseStep 4052375 = 6078563) B6078563
theorem B1070635 : Blo 948586 1070635 := bstep (se 1 (by rfl) ⟨802976, by rfl⟩ : syracuseStep 1070635 = 1605953) B1605953
theorem B1070743 : Blo 948586 1070743 := bstep (se 1 (by rfl) ⟨803057, by rfl⟩ : syracuseStep 1070743 = 1606115) B1606115
theorem B7231193 : Blo 948586 7231193 := bstep (se 2 (by rfl) ⟨2711697, by rfl⟩ : syracuseStep 7231193 = 5423395) B5423395
theorem B1070923 : Blo 948586 1070923 := bstep (se 1 (by rfl) ⟨803192, by rfl⟩ : syracuseStep 1070923 = 1606385) B1606385
theorem B3430295 : Blo 948586 3430295 := bstep (se 1 (by rfl) ⟨2572721, by rfl⟩ : syracuseStep 3430295 = 5145443) B5145443
theorem B1071031 : Blo 948586 1071031 := bstep (se 1 (by rfl) ⟨803273, by rfl⟩ : syracuseStep 1071031 = 1606547) B1606547
theorem B4806701 : Blo 948586 4806701 := bstep (se 3 (by rfl) ⟨901256, by rfl⟩ : syracuseStep 4806701 = 1802513) B1802513
theorem B1071211 : Blo 948586 1071211 := bstep (se 1 (by rfl) ⟨803408, by rfl⟩ : syracuseStep 1071211 = 1606817) B1606817
theorem B2709683 : Blo 948586 2709683 := bstep (se 1 (by rfl) ⟨2032262, by rfl⟩ : syracuseStep 2709683 = 4064525) B4064525
theorem B1071319 : Blo 948586 1071319 := bstep (se 1 (by rfl) ⟨803489, by rfl⟩ : syracuseStep 1071319 = 1606979) B1606979
theorem B1202455 : Blo 948586 1202455 := bstep (se 1 (by rfl) ⟨901841, by rfl⟩ : syracuseStep 1202455 = 1803683) B1803683
theorem B1071499 : Blo 948586 1071499 := bstep (se 1 (by rfl) ⟨803624, by rfl⟩ : syracuseStep 1071499 = 1607249) B1607249
theorem B3201497 : Blo 948586 3201497 := bstep (se 2 (by rfl) ⟨1200561, by rfl⟩ : syracuseStep 3201497 = 2401123) B2401123
theorem B1071607 : Blo 948586 1071607 := bstep (se 1 (by rfl) ⟨803705, by rfl⟩ : syracuseStep 1071607 = 1607411) B1607411
theorem B1203275 : Blo 948586 1203275 := bstep (se 1 (by rfl) ⟨902456, by rfl⟩ : syracuseStep 1203275 = 1804913) B1804913
theorem B3202199 : Blo 948586 3202199 := bstep (se 1 (by rfl) ⟨2401649, by rfl⟩ : syracuseStep 3202199 = 4803299) B4803299
theorem B8019121 : Blo 948586 8019121 := bstep (se 2 (by rfl) ⟨3007170, by rfl⟩ : syracuseStep 8019121 = 6014341) B6014341
theorem B10837313 : Blo 948586 10837313 := bstep (se 2 (by rfl) ⟨4063992, by rfl⟩ : syracuseStep 10837313 = 8127985) B8127985
theorem B8117597 : Blo 948586 8117597 := bstep (se 3 (by rfl) ⟨1522049, by rfl⟩ : syracuseStep 8117597 = 3044099) B3044099
theorem B5135795 : Blo 948586 5135795 := bstep (se 1 (by rfl) ⟨3851846, by rfl⟩ : syracuseStep 5135795 = 7703693) B7703693
theorem B3661357 : Blo 948586 3661357 := bstep (se 3 (by rfl) ⟨686504, by rfl⟩ : syracuseStep 3661357 = 1373009) B1373009
theorem B5791297 : Blo 948586 5791297 := bstep (se 2 (by rfl) ⟨2171736, by rfl⟩ : syracuseStep 5791297 = 4343473) B4343473
theorem B3202739 : Blo 948586 3202739 := bstep (se 1 (by rfl) ⟨2402054, by rfl⟩ : syracuseStep 3202739 = 4804109) B4804109
theorem B1203979 : Blo 948586 1203979 := bstep (se 1 (by rfl) ⟨902984, by rfl⟩ : syracuseStep 1203979 = 1805969) B1805969
theorem B4054835 : Blo 948586 4054835 := bstep (se 1 (by rfl) ⟨3041126, by rfl⟩ : syracuseStep 4054835 = 6082253) B6082253
theorem B3039065 : Blo 948586 3039065 := bstep (se 2 (by rfl) ⟨1139649, by rfl⟩ : syracuseStep 3039065 = 2279299) B2279299
theorem B15032243 : Blo 948586 15032243 := bstep (se 1 (by rfl) ⟨11274182, by rfl⟩ : syracuseStep 15032243 = 22548365) B22548365
theorem B3203009 : Blo 948586 3203009 := bstep (se 2 (by rfl) ⟨1201128, by rfl⟩ : syracuseStep 3203009 = 2402257) B2402257
theorem B1204247 : Blo 948586 1204247 := bstep (se 1 (by rfl) ⟨903185, by rfl⟩ : syracuseStep 1204247 = 1806371) B1806371
theorem B1761419 : Blo 948586 1761419 := bstep (se 1 (by rfl) ⟨1321064, by rfl⟩ : syracuseStep 1761419 = 2642129) B2642129
theorem B8216963 : Blo 948586 8216963 := bstep (se 1 (by rfl) ⟨6162722, by rfl⟩ : syracuseStep 8216963 = 12325445) B12325445
theorem B3203549 : Blo 948586 3203549 := bstep (se 3 (by rfl) ⟨600665, by rfl⟩ : syracuseStep 3203549 = 1201331) B1201331
theorem B8774245 : Blo 948586 8774245 := bstep (se 4 (by rfl) ⟨822585, by rfl⟩ : syracuseStep 8774245 = 1645171) B1645171
theorem B1073783 : Blo 948586 1073783 := bstep (se 1 (by rfl) ⟨805337, by rfl⟩ : syracuseStep 1073783 = 1610675) B1610675
theorem B1925761 : Blo 948586 1925761 := bstep (se 2 (by rfl) ⟨722160, by rfl⟩ : syracuseStep 1925761 = 1444321) B1444321
theorem B3039923 : Blo 948586 3039923 := bstep (se 1 (by rfl) ⟨2279942, by rfl⟩ : syracuseStep 3039923 = 4559885) B4559885
theorem B1204951 : Blo 948586 1204951 := bstep (se 1 (by rfl) ⟨903713, by rfl⟩ : syracuseStep 1204951 = 1807427) B1807427
theorem B3040051 : Blo 948586 3040051 := bstep (se 1 (by rfl) ⟨2280038, by rfl⟩ : syracuseStep 3040051 = 4560077) B4560077
theorem B4875073 : Blo 948586 4875073 := bstep (se 2 (by rfl) ⟨1828152, by rfl⟩ : syracuseStep 4875073 = 3656305) B3656305
theorem B3040193 : Blo 948586 3040193 := bstep (se 2 (by rfl) ⟨1140072, by rfl⟩ : syracuseStep 3040193 = 2280145) B2280145
theorem B2712541 : Blo 948586 2712541 := bstep (se 3 (by rfl) ⟨508601, by rfl⟩ : syracuseStep 2712541 = 1017203) B1017203
theorem B1827863 : Blo 948586 1827863 := bstep (se 1 (by rfl) ⟨1370897, by rfl⟩ : syracuseStep 1827863 = 2741795) B2741795
theorem B2712599 : Blo 948586 2712599 := bstep (se 1 (by rfl) ⟨2034449, by rfl⟩ : syracuseStep 2712599 = 4068899) B4068899
theorem B3040307 : Blo 948586 3040307 := bstep (se 1 (by rfl) ⟨2280230, by rfl⟩ : syracuseStep 3040307 = 4560461) B4560461
theorem B6186077 : Blo 948586 6186077 := bstep (se 3 (by rfl) ⟨1159889, by rfl⟩ : syracuseStep 6186077 = 2319779) B2319779
theorem B19785005 : Blo 948586 19785005 := bstep (se 3 (by rfl) ⟨3709688, by rfl⟩ : syracuseStep 19785005 = 7419377) B7419377
theorem B3204683 : Blo 948586 3204683 := bstep (se 1 (by rfl) ⟨2403512, by rfl⟩ : syracuseStep 3204683 = 4807025) B4807025
theorem B4056749 : Blo 948586 4056749 := bstep (se 3 (by rfl) ⟨760640, by rfl⟩ : syracuseStep 4056749 = 1521281) B1521281
theorem B3204953 : Blo 948586 3204953 := bstep (se 2 (by rfl) ⟨1201857, by rfl⟩ : syracuseStep 3204953 = 2403715) B2403715
theorem B4810589 : Blo 948586 4810589 := bstep (se 3 (by rfl) ⟨901985, by rfl⟩ : syracuseStep 4810589 = 1803971) B1803971
theorem B8120195 : Blo 948586 8120195 := bstep (se 1 (by rfl) ⟨6090146, by rfl⟩ : syracuseStep 8120195 = 12180293) B12180293
theorem B4057091 : Blo 948586 4057091 := bstep (se 1 (by rfl) ⟨3042818, by rfl⟩ : syracuseStep 4057091 = 6085637) B6085637
theorem B29321291 : Blo 948586 29321291 := bstep (se 1 (by rfl) ⟨21990968, by rfl⟩ : syracuseStep 29321291 = 43981937) B43981937
theorem B3205655 : Blo 948586 3205655 := bstep (se 1 (by rfl) ⟨2404241, by rfl⟩ : syracuseStep 3205655 = 4808483) B4808483
theorem B7694999 : Blo 948586 7694999 := bstep (se 1 (by rfl) ⟨5771249, by rfl⟩ : syracuseStep 7694999 = 11542499) B11542499
theorem B3861251 : Blo 948586 3861251 := bstep (se 1 (by rfl) ⟨2895938, by rfl⟩ : syracuseStep 3861251 = 5791877) B5791877
theorem B3206195 : Blo 948586 3206195 := bstep (se 1 (by rfl) ⟨2404646, by rfl⟩ : syracuseStep 3206195 = 4809293) B4809293
theorem B6843457 : Blo 948586 6843457 := bstep (se 2 (by rfl) ⟨2566296, by rfl⟩ : syracuseStep 6843457 = 5132593) B5132593
theorem B3206465 : Blo 948586 3206465 := bstep (se 2 (by rfl) ⟨1202424, by rfl⟩ : syracuseStep 3206465 = 2404849) B2404849
theorem B1600843 : Blo 948586 1600843 := bstep (se 1 (by rfl) ⟨1200632, by rfl⟩ : syracuseStep 1600843 = 2401265) B2401265
theorem B1600985 : Blo 948586 1600985 := bstep (se 2 (by rfl) ⟨600369, by rfl⟩ : syracuseStep 1600985 = 1200739) B1200739
theorem B9137681 : Blo 948586 9137681 := bstep (se 2 (by rfl) ⟨3426630, by rfl⟩ : syracuseStep 9137681 = 6853261) B6853261
theorem B1601113 : Blo 948586 1601113 := bstep (se 2 (by rfl) ⟨600417, by rfl⟩ : syracuseStep 1601113 = 1200835) B1200835
theorem B2027315 : Blo 948586 2027315 := bstep (se 1 (by rfl) ⟨1520486, by rfl⟩ : syracuseStep 2027315 = 3040973) B3040973
theorem B3043165 : Blo 948586 3043165 := bstep (se 3 (by rfl) ⟨570593, by rfl⟩ : syracuseStep 3043165 = 1141187) B1141187
theorem B3207005 : Blo 948586 3207005 := bstep (se 3 (by rfl) ⟨601313, by rfl⟩ : syracuseStep 3207005 = 1202627) B1202627
theorem B4812695 : Blo 948586 4812695 := bstep (se 1 (by rfl) ⟨3609521, by rfl⟩ : syracuseStep 4812695 = 7219043) B7219043
theorem B6090713 : Blo 948586 6090713 := bstep (se 2 (by rfl) ⟨2284017, by rfl⟩ : syracuseStep 6090713 = 4568035) B4568035
theorem B1929217 : Blo 948586 1929217 := bstep (se 2 (by rfl) ⟨723456, by rfl⟩ : syracuseStep 1929217 = 1446913) B1446913
theorem B1601687 : Blo 948586 1601687 := bstep (se 1 (by rfl) ⟨1201265, by rfl⟩ : syracuseStep 1601687 = 2402531) B2402531
theorem B1601815 : Blo 948586 1601815 := bstep (se 1 (by rfl) ⟨1201361, by rfl⟩ : syracuseStep 1601815 = 2402723) B2402723
theorem B4059467 : Blo 948586 4059467 := bstep (se 1 (by rfl) ⟨3044600, by rfl⟩ : syracuseStep 4059467 = 6089201) B6089201
theorem B13005235 : Blo 948586 13005235 := bstep (se 1 (by rfl) ⟨9753926, by rfl⟩ : syracuseStep 13005235 = 19507853) B19507853
theorem B1602443 : Blo 948586 1602443 := bstep (se 1 (by rfl) ⟨1201832, by rfl⟩ : syracuseStep 1602443 = 2403665) B2403665
theorem B3208139 : Blo 948586 3208139 := bstep (se 1 (by rfl) ⟨2406104, by rfl⟩ : syracuseStep 3208139 = 4812209) B4812209
theorem B2028503 : Blo 948586 2028503 := bstep (se 1 (by rfl) ⟨1521377, by rfl⟩ : syracuseStep 2028503 = 3042755) B3042755
theorem B1602571 : Blo 948586 1602571 := bstep (se 1 (by rfl) ⟨1201928, by rfl⟩ : syracuseStep 1602571 = 2403857) B2403857
theorem B10417169 : Blo 948586 10417169 := bstep (se 2 (by rfl) ⟨3906438, by rfl⟩ : syracuseStep 10417169 = 7812877) B7812877
theorem B5141569 : Blo 948586 5141569 := bstep (se 2 (by rfl) ⟨1928088, by rfl⟩ : syracuseStep 5141569 = 3856177) B3856177
theorem B1602713 : Blo 948586 1602713 := bstep (se 2 (by rfl) ⟨601017, by rfl⟩ : syracuseStep 1602713 = 1202035) B1202035
theorem B3208409 : Blo 948586 3208409 := bstep (se 2 (by rfl) ⟨1203153, by rfl⟩ : syracuseStep 3208409 = 2406307) B2406307
theorem B5862617 : Blo 948586 5862617 := bstep (se 2 (by rfl) ⟨2198481, by rfl⟩ : syracuseStep 5862617 = 4396963) B4396963
theorem B4060439 : Blo 948586 4060439 := bstep (se 1 (by rfl) ⟨3045329, by rfl⟩ : syracuseStep 4060439 = 6090659) B6090659
theorem B1602841 : Blo 948586 1602841 := bstep (se 2 (by rfl) ⟨601065, by rfl⟩ : syracuseStep 1602841 = 1202131) B1202131
theorem B12187057 : Blo 948586 12187057 := bstep (se 2 (by rfl) ⟨4570146, by rfl⟩ : syracuseStep 12187057 = 9140293) B9140293
theorem B3601867 : Blo 948586 3601867 := bstep (se 1 (by rfl) ⟨2701400, by rfl⟩ : syracuseStep 3601867 = 5402801) B5402801
theorem B1013239 : Blo 948586 1013239 := bstep (se 1 (by rfl) ⟨759929, by rfl⟩ : syracuseStep 1013239 = 1519859) B1519859
theorem B1373771 : Blo 948586 1373771 := bstep (se 1 (by rfl) ⟨1030328, by rfl⟩ : syracuseStep 1373771 = 2060657) B2060657
theorem B3602141 : Blo 948586 3602141 := bstep (se 3 (by rfl) ⟨675401, by rfl⟩ : syracuseStep 3602141 = 1350803) B1350803
theorem B1603415 : Blo 948586 1603415 := bstep (se 1 (by rfl) ⟨1202561, by rfl⟩ : syracuseStep 1603415 = 2405123) B2405123
theorem B3209111 : Blo 948586 3209111 := bstep (se 1 (by rfl) ⟨2406833, by rfl⟩ : syracuseStep 3209111 = 4813667) B4813667
theorem B1603543 : Blo 948586 1603543 := bstep (se 1 (by rfl) ⟨1202657, by rfl⟩ : syracuseStep 1603543 = 2405315) B2405315
theorem B2029529 : Blo 948586 2029529 := bstep (se 2 (by rfl) ⟨761073, by rfl⟩ : syracuseStep 2029529 = 1522147) B1522147
theorem B13694993 : Blo 948586 13694993 := bstep (se 2 (by rfl) ⟨5135622, by rfl⟩ : syracuseStep 13694993 = 10271245) B10271245
theorem B5142629 : Blo 948586 5142629 := bstep (se 4 (by rfl) ⟨482121, by rfl⟩ : syracuseStep 5142629 = 964243) B964243
theorem B6256997 : Blo 948586 6256997 := bstep (se 4 (by rfl) ⟨586593, by rfl⟩ : syracuseStep 6256997 = 1173187) B1173187
theorem B948587 : Blo 948586 948587 := bstep (se 1 (by rfl) ⟨711440, by rfl⟩ : syracuseStep 948587 = 1422881) B1422881
theorem B94959985 : Blo 948586 94959985 := bstep (se 2 (by rfl) ⟨35609994, by rfl⟩ : syracuseStep 94959985 = 71219989) B71219989
theorem B948599 : Blo 948586 948599 := bstep (se 1 (by rfl) ⟨711449, by rfl⟩ : syracuseStep 948599 = 1422899) B1422899
theorem B948619 : Blo 948586 948619 := bstep (se 1 (by rfl) ⟨711464, by rfl⟩ : syracuseStep 948619 = 1422929) B1422929
theorem B948631 : Blo 948586 948631 := bstep (se 1 (by rfl) ⟨711473, by rfl⟩ : syracuseStep 948631 = 1422947) B1422947
theorem B3602839 : Blo 948586 3602839 := bstep (se 1 (by rfl) ⟨2702129, by rfl⟩ : syracuseStep 3602839 = 5404259) B5404259
theorem B948651 : Blo 948586 948651 := bstep (se 1 (by rfl) ⟨711488, by rfl⟩ : syracuseStep 948651 = 1422977) B1422977
theorem B3209651 : Blo 948586 3209651 := bstep (se 1 (by rfl) ⟨2407238, by rfl⟩ : syracuseStep 3209651 = 4814477) B4814477
theorem B948663 : Blo 948586 948663 := bstep (se 1 (by rfl) ⟨711497, by rfl⟩ : syracuseStep 948663 = 1422995) B1422995
theorem B948683 : Blo 948586 948683 := bstep (se 1 (by rfl) ⟨711512, by rfl⟩ : syracuseStep 948683 = 1423025) B1423025
theorem B948695 : Blo 948586 948695 := bstep (se 1 (by rfl) ⟨711521, by rfl⟩ : syracuseStep 948695 = 1423043) B1423043
theorem B948715 : Blo 948586 948715 := bstep (se 1 (by rfl) ⟨711536, by rfl⟩ : syracuseStep 948715 = 1423073) B1423073
theorem B948727 : Blo 948586 948727 := bstep (se 1 (by rfl) ⟨711545, by rfl⟩ : syracuseStep 948727 = 1423091) B1423091
theorem B948747 : Blo 948586 948747 := bstep (se 1 (by rfl) ⟨711560, by rfl⟩ : syracuseStep 948747 = 1423121) B1423121
theorem B948759 : Blo 948586 948759 := bstep (se 1 (by rfl) ⟨711569, by rfl⟩ : syracuseStep 948759 = 1423139) B1423139
theorem B948779 : Blo 948586 948779 := bstep (se 1 (by rfl) ⟨711584, by rfl⟩ : syracuseStep 948779 = 1423169) B1423169
theorem B948791 : Blo 948586 948791 := bstep (se 1 (by rfl) ⟨711593, by rfl⟩ : syracuseStep 948791 = 1423187) B1423187
theorem B6093377 : Blo 948586 6093377 := bstep (se 2 (by rfl) ⟨2285016, by rfl⟩ : syracuseStep 6093377 = 4570033) B4570033
theorem B948811 : Blo 948586 948811 := bstep (se 1 (by rfl) ⟨711608, by rfl⟩ : syracuseStep 948811 = 1423217) B1423217
theorem B1604171 : Blo 948586 1604171 := bstep (se 1 (by rfl) ⟨1203128, by rfl⟩ : syracuseStep 1604171 = 2406257) B2406257
theorem B948823 : Blo 948586 948823 := bstep (se 1 (by rfl) ⟨711617, by rfl⟩ : syracuseStep 948823 = 1423235) B1423235
theorem B948843 : Blo 948586 948843 := bstep (se 1 (by rfl) ⟨711632, by rfl⟩ : syracuseStep 948843 = 1423265) B1423265
theorem B948855 : Blo 948586 948855 := bstep (se 1 (by rfl) ⟨711641, by rfl⟩ : syracuseStep 948855 = 1423283) B1423283
theorem B20544131 : Blo 948586 20544131 := bstep (se 1 (by rfl) ⟨15408098, by rfl⟩ : syracuseStep 20544131 = 30816197) B30816197
theorem B948875 : Blo 948586 948875 := bstep (se 1 (by rfl) ⟨711656, by rfl⟩ : syracuseStep 948875 = 1423313) B1423313
theorem B948887 : Blo 948586 948887 := bstep (se 1 (by rfl) ⟨711665, by rfl⟩ : syracuseStep 948887 = 1423331) B1423331
theorem B948907 : Blo 948586 948907 := bstep (se 1 (by rfl) ⟨711680, by rfl⟩ : syracuseStep 948907 = 1423361) B1423361
theorem B948919 : Blo 948586 948919 := bstep (se 1 (by rfl) ⟨711689, by rfl⟩ : syracuseStep 948919 = 1423379) B1423379
theorem B3209921 : Blo 948586 3209921 := bstep (se 2 (by rfl) ⟨1203720, by rfl⟩ : syracuseStep 3209921 = 2407441) B2407441
theorem B948939 : Blo 948586 948939 := bstep (se 1 (by rfl) ⟨711704, by rfl⟩ : syracuseStep 948939 = 1423409) B1423409
theorem B1604299 : Blo 948586 1604299 := bstep (se 1 (by rfl) ⟨1203224, by rfl⟩ : syracuseStep 1604299 = 2406449) B2406449
theorem B948951 : Blo 948586 948951 := bstep (se 1 (by rfl) ⟨711713, by rfl⟩ : syracuseStep 948951 = 1423427) B1423427
theorem B948971 : Blo 948586 948971 := bstep (se 1 (by rfl) ⟨711728, by rfl⟩ : syracuseStep 948971 = 1423457) B1423457
theorem B948983 : Blo 948586 948983 := bstep (se 1 (by rfl) ⟨711737, by rfl⟩ : syracuseStep 948983 = 1423475) B1423475
theorem B949003 : Blo 948586 949003 := bstep (se 1 (by rfl) ⟨711752, by rfl⟩ : syracuseStep 949003 = 1423505) B1423505
theorem B949015 : Blo 948586 949015 := bstep (se 1 (by rfl) ⟨711761, by rfl⟩ : syracuseStep 949015 = 1423523) B1423523
theorem B949035 : Blo 948586 949035 := bstep (se 1 (by rfl) ⟨711776, by rfl⟩ : syracuseStep 949035 = 1423553) B1423553
theorem B949047 : Blo 948586 949047 := bstep (se 1 (by rfl) ⟨711785, by rfl⟩ : syracuseStep 949047 = 1423571) B1423571
theorem B1801025 : Blo 948586 1801025 := bstep (se 2 (by rfl) ⟨675384, by rfl⟩ : syracuseStep 1801025 = 1350769) B1350769
theorem B949067 : Blo 948586 949067 := bstep (se 1 (by rfl) ⟨711800, by rfl⟩ : syracuseStep 949067 = 1423601) B1423601
theorem B949079 : Blo 948586 949079 := bstep (se 1 (by rfl) ⟨711809, by rfl⟩ : syracuseStep 949079 = 1423619) B1423619
theorem B1604441 : Blo 948586 1604441 := bstep (se 2 (by rfl) ⟨601665, by rfl⟩ : syracuseStep 1604441 = 1203331) B1203331
theorem B949099 : Blo 948586 949099 := bstep (se 1 (by rfl) ⟨711824, by rfl⟩ : syracuseStep 949099 = 1423649) B1423649
theorem B949111 : Blo 948586 949111 := bstep (se 1 (by rfl) ⟨711833, by rfl⟩ : syracuseStep 949111 = 1423667) B1423667
theorem B1735553 : Blo 948586 1735553 := bstep (se 2 (by rfl) ⟨650832, by rfl⟩ : syracuseStep 1735553 = 1301665) B1301665
theorem B949131 : Blo 948586 949131 := bstep (se 1 (by rfl) ⟨711848, by rfl⟩ : syracuseStep 949131 = 1423697) B1423697
theorem B949143 : Blo 948586 949143 := bstep (se 1 (by rfl) ⟨711857, by rfl⟩ : syracuseStep 949143 = 1423715) B1423715
theorem B949163 : Blo 948586 949163 := bstep (se 1 (by rfl) ⟨711872, by rfl⟩ : syracuseStep 949163 = 1423745) B1423745
theorem B19037105 : Blo 948586 19037105 := bstep (se 2 (by rfl) ⟨7138914, by rfl⟩ : syracuseStep 19037105 = 14277829) B14277829
theorem B949175 : Blo 948586 949175 := bstep (se 1 (by rfl) ⟨711881, by rfl⟩ : syracuseStep 949175 = 1423763) B1423763
theorem B949195 : Blo 948586 949195 := bstep (se 1 (by rfl) ⟨711896, by rfl⟩ : syracuseStep 949195 = 1423793) B1423793
theorem B949207 : Blo 948586 949207 := bstep (se 1 (by rfl) ⟨711905, by rfl⟩ : syracuseStep 949207 = 1423811) B1423811
theorem B1604569 : Blo 948586 1604569 := bstep (se 2 (by rfl) ⟨601713, by rfl⟩ : syracuseStep 1604569 = 1203427) B1203427
theorem B949227 : Blo 948586 949227 := bstep (se 1 (by rfl) ⟨711920, by rfl⟩ : syracuseStep 949227 = 1423841) B1423841
theorem B2030579 : Blo 948586 2030579 := bstep (se 1 (by rfl) ⟨1522934, by rfl⟩ : syracuseStep 2030579 = 3045869) B3045869
theorem B949239 : Blo 948586 949239 := bstep (se 1 (by rfl) ⟨711929, by rfl⟩ : syracuseStep 949239 = 1423859) B1423859
theorem B949259 : Blo 948586 949259 := bstep (se 1 (by rfl) ⟨711944, by rfl⟩ : syracuseStep 949259 = 1423889) B1423889
theorem B949271 : Blo 948586 949271 := bstep (se 1 (by rfl) ⟨711953, by rfl⟩ : syracuseStep 949271 = 1423907) B1423907
theorem B949291 : Blo 948586 949291 := bstep (se 1 (by rfl) ⟨711968, by rfl⟩ : syracuseStep 949291 = 1423937) B1423937
theorem B949303 : Blo 948586 949303 := bstep (se 1 (by rfl) ⟨711977, by rfl⟩ : syracuseStep 949303 = 1423955) B1423955
theorem B1801291 : Blo 948586 1801291 := bstep (se 1 (by rfl) ⟨1350968, by rfl⟩ : syracuseStep 1801291 = 2701937) B2701937
theorem B949323 : Blo 948586 949323 := bstep (se 1 (by rfl) ⟨711992, by rfl⟩ : syracuseStep 949323 = 1423985) B1423985
theorem B949335 : Blo 948586 949335 := bstep (se 1 (by rfl) ⟨712001, by rfl⟩ : syracuseStep 949335 = 1424003) B1424003
theorem B949355 : Blo 948586 949355 := bstep (se 1 (by rfl) ⟨712016, by rfl⟩ : syracuseStep 949355 = 1424033) B1424033
theorem B949367 : Blo 948586 949367 := bstep (se 1 (by rfl) ⟨712025, by rfl⟩ : syracuseStep 949367 = 1424051) B1424051
theorem B949387 : Blo 948586 949387 := bstep (se 1 (by rfl) ⟨712040, by rfl⟩ : syracuseStep 949387 = 1424081) B1424081
theorem B949399 : Blo 948586 949399 := bstep (se 1 (by rfl) ⟨712049, by rfl⟩ : syracuseStep 949399 = 1424099) B1424099
theorem B1014935 : Blo 948586 1014935 := bstep (se 1 (by rfl) ⟨761201, by rfl⟩ : syracuseStep 1014935 = 1522403) B1522403
theorem B949419 : Blo 948586 949419 := bstep (se 1 (by rfl) ⟨712064, by rfl⟩ : syracuseStep 949419 = 1424129) B1424129
theorem B3603629 : Blo 948586 3603629 := bstep (se 3 (by rfl) ⟨675680, by rfl⟩ : syracuseStep 3603629 = 1351361) B1351361
theorem B949431 : Blo 948586 949431 := bstep (se 1 (by rfl) ⟨712073, by rfl⟩ : syracuseStep 949431 = 1424147) B1424147
theorem B949451 : Blo 948586 949451 := bstep (se 1 (by rfl) ⟨712088, by rfl⟩ : syracuseStep 949451 = 1424177) B1424177
theorem B949463 : Blo 948586 949463 := bstep (se 1 (by rfl) ⟨712097, by rfl⟩ : syracuseStep 949463 = 1424195) B1424195
theorem B3210461 : Blo 948586 3210461 := bstep (se 3 (by rfl) ⟨601961, by rfl⟩ : syracuseStep 3210461 = 1203923) B1203923
theorem B949483 : Blo 948586 949483 := bstep (se 1 (by rfl) ⟨712112, by rfl⟩ : syracuseStep 949483 = 1424225) B1424225
theorem B949495 : Blo 948586 949495 := bstep (se 1 (by rfl) ⟨712121, by rfl⟩ : syracuseStep 949495 = 1424243) B1424243
theorem B949515 : Blo 948586 949515 := bstep (se 1 (by rfl) ⟨712136, by rfl⟩ : syracuseStep 949515 = 1424273) B1424273
theorem B949527 : Blo 948586 949527 := bstep (se 1 (by rfl) ⟨712145, by rfl⟩ : syracuseStep 949527 = 1424291) B1424291
theorem B949547 : Blo 948586 949547 := bstep (se 1 (by rfl) ⟨712160, by rfl⟩ : syracuseStep 949547 = 1424321) B1424321
theorem B18513197 : Blo 948586 18513197 := bstep (se 3 (by rfl) ⟨3471224, by rfl⟩ : syracuseStep 18513197 = 6942449) B6942449
theorem B949559 : Blo 948586 949559 := bstep (se 1 (by rfl) ⟨712169, by rfl⟩ : syracuseStep 949559 = 1424339) B1424339
theorem B949579 : Blo 948586 949579 := bstep (se 1 (by rfl) ⟨712184, by rfl⟩ : syracuseStep 949579 = 1424369) B1424369
theorem B949591 : Blo 948586 949591 := bstep (se 1 (by rfl) ⟨712193, by rfl⟩ : syracuseStep 949591 = 1424387) B1424387
theorem B949611 : Blo 948586 949611 := bstep (se 1 (by rfl) ⟨712208, by rfl⟩ : syracuseStep 949611 = 1424417) B1424417
theorem B949623 : Blo 948586 949623 := bstep (se 1 (by rfl) ⟨712217, by rfl⟩ : syracuseStep 949623 = 1424435) B1424435
theorem B4816259 : Blo 948586 4816259 := bstep (se 1 (by rfl) ⟨3612194, by rfl⟩ : syracuseStep 4816259 = 7224389) B7224389
theorem B949643 : Blo 948586 949643 := bstep (se 1 (by rfl) ⟨712232, by rfl⟩ : syracuseStep 949643 = 1424465) B1424465
theorem B949655 : Blo 948586 949655 := bstep (se 1 (by rfl) ⟨712241, by rfl⟩ : syracuseStep 949655 = 1424483) B1424483
theorem B949675 : Blo 948586 949675 := bstep (se 1 (by rfl) ⟨712256, by rfl⟩ : syracuseStep 949675 = 1424513) B1424513
theorem B949687 : Blo 948586 949687 := bstep (se 1 (by rfl) ⟨712265, by rfl⟩ : syracuseStep 949687 = 1424531) B1424531
theorem B949707 : Blo 948586 949707 := bstep (se 1 (by rfl) ⟨712280, by rfl⟩ : syracuseStep 949707 = 1424561) B1424561
theorem B949719 : Blo 948586 949719 := bstep (se 1 (by rfl) ⟨712289, by rfl⟩ : syracuseStep 949719 = 1424579) B1424579
theorem B949739 : Blo 948586 949739 := bstep (se 1 (by rfl) ⟨712304, by rfl⟩ : syracuseStep 949739 = 1424609) B1424609
theorem B949751 : Blo 948586 949751 := bstep (se 1 (by rfl) ⟨712313, by rfl⟩ : syracuseStep 949751 = 1424627) B1424627
theorem B1801739 : Blo 948586 1801739 := bstep (se 1 (by rfl) ⟨1351304, by rfl⟩ : syracuseStep 1801739 = 2702609) B2702609
theorem B949771 : Blo 948586 949771 := bstep (se 1 (by rfl) ⟨712328, by rfl⟩ : syracuseStep 949771 = 1424657) B1424657
theorem B949783 : Blo 948586 949783 := bstep (se 1 (by rfl) ⟨712337, by rfl⟩ : syracuseStep 949783 = 1424675) B1424675
theorem B1605143 : Blo 948586 1605143 := bstep (se 1 (by rfl) ⟨1203857, by rfl⟩ : syracuseStep 1605143 = 2407715) B2407715
theorem B949803 : Blo 948586 949803 := bstep (se 1 (by rfl) ⟨712352, by rfl⟩ : syracuseStep 949803 = 1424705) B1424705
theorem B949815 : Blo 948586 949815 := bstep (se 1 (by rfl) ⟨712361, by rfl⟩ : syracuseStep 949815 = 1424723) B1424723
theorem B2031169 : Blo 948586 2031169 := bstep (se 2 (by rfl) ⟨761688, by rfl⟩ : syracuseStep 2031169 = 1523377) B1523377
theorem B949835 : Blo 948586 949835 := bstep (se 1 (by rfl) ⟨712376, by rfl⟩ : syracuseStep 949835 = 1424753) B1424753
theorem B949847 : Blo 948586 949847 := bstep (se 1 (by rfl) ⟨712385, by rfl⟩ : syracuseStep 949847 = 1424771) B1424771
theorem B949867 : Blo 948586 949867 := bstep (se 1 (by rfl) ⟨712400, by rfl⟩ : syracuseStep 949867 = 1424801) B1424801
theorem B949879 : Blo 948586 949879 := bstep (se 1 (by rfl) ⟨712409, by rfl⟩ : syracuseStep 949879 = 1424819) B1424819
theorem B949899 : Blo 948586 949899 := bstep (se 1 (by rfl) ⟨712424, by rfl⟩ : syracuseStep 949899 = 1424849) B1424849
theorem B949911 : Blo 948586 949911 := bstep (se 1 (by rfl) ⟨712433, by rfl⟩ : syracuseStep 949911 = 1424867) B1424867
theorem B1605271 : Blo 948586 1605271 := bstep (se 1 (by rfl) ⟨1203953, by rfl⟩ : syracuseStep 1605271 = 2407907) B2407907
theorem B949931 : Blo 948586 949931 := bstep (se 1 (by rfl) ⟨712448, by rfl⟩ : syracuseStep 949931 = 1424897) B1424897
theorem B4062899 : Blo 948586 4062899 := bstep (se 1 (by rfl) ⟨3047174, by rfl⟩ : syracuseStep 4062899 = 6094349) B6094349
theorem B949943 : Blo 948586 949943 := bstep (se 1 (by rfl) ⟨712457, by rfl⟩ : syracuseStep 949943 = 1424915) B1424915
theorem B1801921 : Blo 948586 1801921 := bstep (se 2 (by rfl) ⟨675720, by rfl⟩ : syracuseStep 1801921 = 1351441) B1351441
theorem B949963 : Blo 948586 949963 := bstep (se 1 (by rfl) ⟨712472, by rfl⟩ : syracuseStep 949963 = 1424945) B1424945
theorem B949975 : Blo 948586 949975 := bstep (se 1 (by rfl) ⟨712481, by rfl⟩ : syracuseStep 949975 = 1424963) B1424963
theorem B5406425 : Blo 948586 5406425 := bstep (se 2 (by rfl) ⟨2027409, by rfl⟩ : syracuseStep 5406425 = 4054819) B4054819
theorem B949995 : Blo 948586 949995 := bstep (se 1 (by rfl) ⟨712496, by rfl⟩ : syracuseStep 949995 = 1424993) B1424993
theorem B950007 : Blo 948586 950007 := bstep (se 1 (by rfl) ⟨712505, by rfl⟩ : syracuseStep 950007 = 1425011) B1425011
theorem B950027 : Blo 948586 950027 := bstep (se 1 (by rfl) ⟨712520, by rfl⟩ : syracuseStep 950027 = 1425041) B1425041
theorem B950039 : Blo 948586 950039 := bstep (se 1 (by rfl) ⟨712529, by rfl⟩ : syracuseStep 950039 = 1425059) B1425059
theorem B950059 : Blo 948586 950059 := bstep (se 1 (by rfl) ⟨712544, by rfl⟩ : syracuseStep 950059 = 1425089) B1425089
theorem B950071 : Blo 948586 950071 := bstep (se 1 (by rfl) ⟨712553, by rfl⟩ : syracuseStep 950071 = 1425107) B1425107
theorem B950091 : Blo 948586 950091 := bstep (se 1 (by rfl) ⟨712568, by rfl⟩ : syracuseStep 950091 = 1425137) B1425137
theorem B950103 : Blo 948586 950103 := bstep (se 1 (by rfl) ⟨712577, by rfl⟩ : syracuseStep 950103 = 1425155) B1425155
theorem B950123 : Blo 948586 950123 := bstep (se 1 (by rfl) ⟨712592, by rfl⟩ : syracuseStep 950123 = 1425185) B1425185
theorem B950135 : Blo 948586 950135 := bstep (se 1 (by rfl) ⟨712601, by rfl⟩ : syracuseStep 950135 = 1425203) B1425203
theorem B950155 : Blo 948586 950155 := bstep (se 1 (by rfl) ⟨712616, by rfl⟩ : syracuseStep 950155 = 1425233) B1425233
theorem B950167 : Blo 948586 950167 := bstep (se 1 (by rfl) ⟨712625, by rfl⟩ : syracuseStep 950167 = 1425251) B1425251
theorem B950187 : Blo 948586 950187 := bstep (se 1 (by rfl) ⟨712640, by rfl⟩ : syracuseStep 950187 = 1425281) B1425281
theorem B950199 : Blo 948586 950199 := bstep (se 1 (by rfl) ⟨712649, by rfl⟩ : syracuseStep 950199 = 1425299) B1425299
theorem B950219 : Blo 948586 950219 := bstep (se 1 (by rfl) ⟨712664, by rfl⟩ : syracuseStep 950219 = 1425329) B1425329
theorem B950231 : Blo 948586 950231 := bstep (se 1 (by rfl) ⟨712673, by rfl⟩ : syracuseStep 950231 = 1425347) B1425347
theorem B950251 : Blo 948586 950251 := bstep (se 1 (by rfl) ⟨712688, by rfl⟩ : syracuseStep 950251 = 1425377) B1425377
theorem B950263 : Blo 948586 950263 := bstep (se 1 (by rfl) ⟨712697, by rfl⟩ : syracuseStep 950263 = 1425395) B1425395
theorem B950279 : Blo 948586 950279 := bstep (se 1 (by rfl) ⟨712709, by rfl⟩ : syracuseStep 950279 = 1425419) B1425419
theorem B4816907 : Blo 948586 4816907 := bstep (se 1 (by rfl) ⟨3612680, by rfl⟩ : syracuseStep 4816907 = 7225361) B7225361
theorem B950287 : Blo 948586 950287 := bstep (se 1 (by rfl) ⟨712715, by rfl⟩ : syracuseStep 950287 = 1425431) B1425431
theorem B950331 : Blo 948586 950331 := bstep (se 1 (by rfl) ⟨712748, by rfl⟩ : syracuseStep 950331 = 1425497) B1425497
theorem B3211325 : Blo 948586 3211325 := bstep (se 3 (by rfl) ⟨602123, by rfl⟩ : syracuseStep 3211325 = 1204247) B1204247
theorem B950407 : Blo 948586 950407 := bstep (se 1 (by rfl) ⟨712805, by rfl⟩ : syracuseStep 950407 = 1425611) B1425611
theorem B950415 : Blo 948586 950415 := bstep (se 1 (by rfl) ⟨712811, by rfl⟩ : syracuseStep 950415 = 1425623) B1425623
theorem B4817069 : Blo 948586 4817069 := bstep (se 3 (by rfl) ⟨903200, by rfl⟩ : syracuseStep 4817069 = 1806401) B1806401
theorem B950459 : Blo 948586 950459 := bstep (se 1 (by rfl) ⟨712844, by rfl⟩ : syracuseStep 950459 = 1425689) B1425689
theorem B950535 : Blo 948586 950535 := bstep (se 1 (by rfl) ⟨712901, by rfl⟩ : syracuseStep 950535 = 1425803) B1425803
theorem B950543 : Blo 948586 950543 := bstep (se 1 (by rfl) ⟨712907, by rfl⟩ : syracuseStep 950543 = 1425815) B1425815
theorem B3604769 : Blo 948586 3604769 := bstep (se 2 (by rfl) ⟨1351788, by rfl⟩ : syracuseStep 3604769 = 2703577) B2703577
theorem B950587 : Blo 948586 950587 := bstep (se 1 (by rfl) ⟨712940, by rfl⟩ : syracuseStep 950587 = 1425881) B1425881
theorem B1606007 : Blo 948586 1606007 := bstep (se 1 (by rfl) ⟨1204505, by rfl⟩ : syracuseStep 1606007 = 2409011) B2409011
theorem B950663 : Blo 948586 950663 := bstep (se 1 (by rfl) ⟨712997, by rfl⟩ : syracuseStep 950663 = 1425995) B1425995
theorem B950671 : Blo 948586 950671 := bstep (se 1 (by rfl) ⟨713003, by rfl⟩ : syracuseStep 950671 = 1426007) B1426007
theorem B2032057 : Blo 948586 2032057 := bstep (se 2 (by rfl) ⟨762021, by rfl⟩ : syracuseStep 2032057 = 1524043) B1524043
theorem B950715 : Blo 948586 950715 := bstep (se 1 (by rfl) ⟨713036, by rfl⟩ : syracuseStep 950715 = 1426073) B1426073
theorem B950791 : Blo 948586 950791 := bstep (se 1 (by rfl) ⟨713093, by rfl⟩ : syracuseStep 950791 = 1426187) B1426187
theorem B950799 : Blo 948586 950799 := bstep (se 1 (by rfl) ⟨713099, by rfl⟩ : syracuseStep 950799 = 1426199) B1426199
theorem B950843 : Blo 948586 950843 := bstep (se 1 (by rfl) ⟨713132, by rfl⟩ : syracuseStep 950843 = 1426265) B1426265
theorem B950919 : Blo 948586 950919 := bstep (se 1 (by rfl) ⟨713189, by rfl⟩ : syracuseStep 950919 = 1426379) B1426379
theorem B950927 : Blo 948586 950927 := bstep (se 1 (by rfl) ⟨713195, by rfl⟩ : syracuseStep 950927 = 1426391) B1426391
theorem B950971 : Blo 948586 950971 := bstep (se 1 (by rfl) ⟨713228, by rfl⟩ : syracuseStep 950971 = 1426457) B1426457
theorem B1016507 : Blo 948586 1016507 := bstep (se 1 (by rfl) ⟨762380, by rfl⟩ : syracuseStep 1016507 = 1524761) B1524761
theorem B951047 : Blo 948586 951047 := bstep (se 1 (by rfl) ⟨713285, by rfl⟩ : syracuseStep 951047 = 1426571) B1426571
theorem B951055 : Blo 948586 951055 := bstep (se 1 (by rfl) ⟨713291, by rfl⟩ : syracuseStep 951055 = 1426583) B1426583
theorem B33424163 : Blo 948586 33424163 := bstep (se 1 (by rfl) ⟨25068122, by rfl⟩ : syracuseStep 33424163 = 50136245) B50136245
theorem B11698993 : Blo 948586 11698993 := bstep (se 2 (by rfl) ⟨4387122, by rfl⟩ : syracuseStep 11698993 = 8774245) B8774245
theorem B951099 : Blo 948586 951099 := bstep (se 1 (by rfl) ⟨713324, by rfl⟩ : syracuseStep 951099 = 1426649) B1426649
theorem B1606459 : Blo 948586 1606459 := bstep (se 1 (by rfl) ⟨1204844, by rfl⟩ : syracuseStep 1606459 = 2409689) B2409689
theorem B951175 : Blo 948586 951175 := bstep (se 1 (by rfl) ⟨713381, by rfl⟩ : syracuseStep 951175 = 1426763) B1426763
theorem B951183 : Blo 948586 951183 := bstep (se 1 (by rfl) ⟨713387, by rfl⟩ : syracuseStep 951183 = 1426775) B1426775
theorem B951227 : Blo 948586 951227 := bstep (se 1 (by rfl) ⟨713420, by rfl⟩ : syracuseStep 951227 = 1426841) B1426841
theorem B1606601 : Blo 948586 1606601 := bstep (se 2 (by rfl) ⟨602475, by rfl⟩ : syracuseStep 1606601 = 1204951) B1204951
theorem B951303 : Blo 948586 951303 := bstep (se 1 (by rfl) ⟨713477, by rfl⟩ : syracuseStep 951303 = 1426955) B1426955
theorem B951311 : Blo 948586 951311 := bstep (se 1 (by rfl) ⟨713483, by rfl⟩ : syracuseStep 951311 = 1426967) B1426967
theorem B951355 : Blo 948586 951355 := bstep (se 1 (by rfl) ⟨713516, by rfl⟩ : syracuseStep 951355 = 1427033) B1427033
theorem B951431 : Blo 948586 951431 := bstep (se 1 (by rfl) ⟨713573, by rfl⟩ : syracuseStep 951431 = 1427147) B1427147
theorem B951439 : Blo 948586 951439 := bstep (se 1 (by rfl) ⟨713579, by rfl⟩ : syracuseStep 951439 = 1427159) B1427159
theorem B951483 : Blo 948586 951483 := bstep (se 1 (by rfl) ⟨713612, by rfl⟩ : syracuseStep 951483 = 1427225) B1427225
theorem B3605741 : Blo 948586 3605741 := bstep (se 3 (by rfl) ⟨676076, by rfl⟩ : syracuseStep 3605741 = 1352153) B1352153
theorem B951559 : Blo 948586 951559 := bstep (se 1 (by rfl) ⟨713669, by rfl⟩ : syracuseStep 951559 = 1427339) B1427339
theorem B951567 : Blo 948586 951567 := bstep (se 1 (by rfl) ⟨713675, by rfl⟩ : syracuseStep 951567 = 1427351) B1427351
theorem B951611 : Blo 948586 951611 := bstep (se 1 (by rfl) ⟨713708, by rfl⟩ : syracuseStep 951611 = 1427417) B1427417
theorem B951687 : Blo 948586 951687 := bstep (se 1 (by rfl) ⟨713765, by rfl⟩ : syracuseStep 951687 = 1427531) B1427531
theorem B951695 : Blo 948586 951695 := bstep (se 1 (by rfl) ⟨713771, by rfl⟩ : syracuseStep 951695 = 1427543) B1427543
theorem B3212729 : Blo 948586 3212729 := bstep (se 2 (by rfl) ⟨1204773, by rfl⟩ : syracuseStep 3212729 = 2409547) B2409547
theorem B951739 : Blo 948586 951739 := bstep (se 1 (by rfl) ⟨713804, by rfl⟩ : syracuseStep 951739 = 1427609) B1427609
theorem B1803721 : Blo 948586 1803721 := bstep (se 2 (by rfl) ⟨676395, by rfl⟩ : syracuseStep 1803721 = 1352791) B1352791
theorem B15402449 : Blo 948586 15402449 := bstep (se 2 (by rfl) ⟨5775918, by rfl⟩ : syracuseStep 15402449 = 11551837) B11551837
theorem B951815 : Blo 948586 951815 := bstep (se 1 (by rfl) ⟨713861, by rfl⟩ : syracuseStep 951815 = 1427723) B1427723
theorem B951823 : Blo 948586 951823 := bstep (se 1 (by rfl) ⟨713867, by rfl⟩ : syracuseStep 951823 = 1427735) B1427735
theorem B3606059 : Blo 948586 3606059 := bstep (se 1 (by rfl) ⟨2704544, by rfl⟩ : syracuseStep 3606059 = 5409089) B5409089
theorem B951867 : Blo 948586 951867 := bstep (se 1 (by rfl) ⟨713900, by rfl⟩ : syracuseStep 951867 = 1427801) B1427801
theorem B951943 : Blo 948586 951943 := bstep (se 1 (by rfl) ⟨713957, by rfl⟩ : syracuseStep 951943 = 1427915) B1427915
theorem B1607303 : Blo 948586 1607303 := bstep (se 1 (by rfl) ⟨1205477, by rfl⟩ : syracuseStep 1607303 = 2410955) B2410955
theorem B951951 : Blo 948586 951951 := bstep (se 1 (by rfl) ⟨713963, by rfl⟩ : syracuseStep 951951 = 1427927) B1427927
theorem B20514455 : Blo 948586 20514455 := bstep (se 1 (by rfl) ⟨15385841, by rfl⟩ : syracuseStep 20514455 = 30771683) B30771683
theorem B951995 : Blo 948586 951995 := bstep (se 1 (by rfl) ⟨713996, by rfl⟩ : syracuseStep 951995 = 1427993) B1427993
theorem B4818689 : Blo 948586 4818689 := bstep (se 2 (by rfl) ⟨1807008, by rfl⟩ : syracuseStep 4818689 = 3614017) B3614017
theorem B952071 : Blo 948586 952071 := bstep (se 1 (by rfl) ⟨714053, by rfl⟩ : syracuseStep 952071 = 1428107) B1428107
theorem B952079 : Blo 948586 952079 := bstep (se 1 (by rfl) ⟨714059, by rfl⟩ : syracuseStep 952079 = 1428119) B1428119
theorem B952123 : Blo 948586 952123 := bstep (se 1 (by rfl) ⟨714092, by rfl⟩ : syracuseStep 952123 = 1428185) B1428185
theorem B75171685 : Blo 948586 75171685 := bstep (se 4 (by rfl) ⟨7047345, by rfl⟩ : syracuseStep 75171685 = 14094691) B14094691
theorem B952199 : Blo 948586 952199 := bstep (se 1 (by rfl) ⟨714149, by rfl⟩ : syracuseStep 952199 = 1428299) B1428299
theorem B952207 : Blo 948586 952207 := bstep (se 1 (by rfl) ⟨714155, by rfl⟩ : syracuseStep 952207 = 1428311) B1428311
theorem B952251 : Blo 948586 952251 := bstep (se 1 (by rfl) ⟨714188, by rfl⟩ : syracuseStep 952251 = 1428377) B1428377
theorem B1443847 : Blo 948586 1443847 := bstep (se 1 (by rfl) ⟨1082885, by rfl⟩ : syracuseStep 1443847 = 2165771) B2165771
theorem B952327 : Blo 948586 952327 := bstep (se 1 (by rfl) ⟨714245, by rfl⟩ : syracuseStep 952327 = 1428491) B1428491
theorem B3213323 : Blo 948586 3213323 := bstep (se 1 (by rfl) ⟨2409992, by rfl⟩ : syracuseStep 3213323 = 4819985) B4819985
theorem B952335 : Blo 948586 952335 := bstep (se 1 (by rfl) ⟨714251, by rfl⟩ : syracuseStep 952335 = 1428503) B1428503
theorem B2033723 : Blo 948586 2033723 := bstep (se 1 (by rfl) ⟨1525292, by rfl⟩ : syracuseStep 2033723 = 3050585) B3050585
theorem B952379 : Blo 948586 952379 := bstep (se 1 (by rfl) ⟨714284, by rfl⟩ : syracuseStep 952379 = 1428569) B1428569
theorem B3049559 : Blo 948586 3049559 := bstep (se 1 (by rfl) ⟨2287169, by rfl⟩ : syracuseStep 3049559 = 4574339) B4574339
theorem B3213431 : Blo 948586 3213431 := bstep (se 1 (by rfl) ⟨2410073, by rfl⟩ : syracuseStep 3213431 = 4820147) B4820147
theorem B952455 : Blo 948586 952455 := bstep (se 1 (by rfl) ⟨714341, by rfl⟩ : syracuseStep 952455 = 1428683) B1428683
theorem B952463 : Blo 948586 952463 := bstep (se 1 (by rfl) ⟨714347, by rfl⟩ : syracuseStep 952463 = 1428695) B1428695
theorem B952507 : Blo 948586 952507 := bstep (se 1 (by rfl) ⟨714380, by rfl⟩ : syracuseStep 952507 = 1428761) B1428761
theorem B952583 : Blo 948586 952583 := bstep (se 1 (by rfl) ⟨714437, by rfl⟩ : syracuseStep 952583 = 1428875) B1428875
theorem B4819499 : Blo 948586 4819499 := bstep (se 1 (by rfl) ⟨3614624, by rfl⟩ : syracuseStep 4819499 = 7229249) B7229249
theorem B5409341 : Blo 948586 5409341 := bstep (se 3 (by rfl) ⟨1014251, by rfl⟩ : syracuseStep 5409341 = 2028503) B2028503
theorem B3214025 : Blo 948586 3214025 := bstep (se 2 (by rfl) ⟨1205259, by rfl⟩ : syracuseStep 3214025 = 2410519) B2410519
theorem B11733913 : Blo 948586 11733913 := bstep (se 2 (by rfl) ⟨4400217, by rfl⟩ : syracuseStep 11733913 = 8800435) B8800435
theorem B1805627 : Blo 948586 1805627 := bstep (se 1 (by rfl) ⟨1354220, by rfl⟩ : syracuseStep 1805627 = 2708441) B2708441
theorem B3214727 : Blo 948586 3214727 := bstep (se 1 (by rfl) ⟨2411045, by rfl⟩ : syracuseStep 3214727 = 4822091) B4822091
theorem B4623763 : Blo 948586 4623763 := bstep (se 1 (by rfl) ⟨3467822, by rfl⟩ : syracuseStep 4623763 = 6935645) B6935645
theorem B20811185 : Blo 948586 20811185 := bstep (se 2 (by rfl) ⟨7804194, by rfl⟩ : syracuseStep 20811185 = 15608389) B15608389
theorem B7310891 : Blo 948586 7310891 := bstep (se 1 (by rfl) ⟨5483168, by rfl⟩ : syracuseStep 7310891 = 10966337) B10966337
theorem B1806113 : Blo 948586 1806113 := bstep (se 2 (by rfl) ⟨677292, by rfl⟩ : syracuseStep 1806113 = 1354585) B1354585
theorem B4820795 : Blo 948586 4820795 := bstep (se 1 (by rfl) ⟨3615596, by rfl⟩ : syracuseStep 4820795 = 7231193) B7231193
theorem B4820957 : Blo 948586 4820957 := bstep (se 3 (by rfl) ⟨903929, by rfl⟩ : syracuseStep 4820957 = 1807859) B1807859
theorem B1806455 : Blo 948586 1806455 := bstep (se 1 (by rfl) ⟨1354841, by rfl⟩ : syracuseStep 1806455 = 2709683) B2709683
theorem B4821281 : Blo 948586 4821281 := bstep (se 2 (by rfl) ⟨1807980, by rfl⟩ : syracuseStep 4821281 = 3615961) B3615961
theorem B2134331 : Blo 948586 2134331 := bstep (se 1 (by rfl) ⟨1600748, by rfl⟩ : syracuseStep 2134331 = 3201497) B3201497
theorem B2134457 : Blo 948586 2134457 := bstep (se 2 (by rfl) ⟨800421, by rfl⟩ : syracuseStep 2134457 = 1600843) B1600843
theorem B2134799 : Blo 948586 2134799 := bstep (se 1 (by rfl) ⟨1601099, by rfl⟩ : syracuseStep 2134799 = 3202199) B3202199
theorem B2134817 : Blo 948586 2134817 := bstep (se 2 (by rfl) ⟨800556, by rfl⟩ : syracuseStep 2134817 = 1601113) B1601113
theorem B5411731 : Blo 948586 5411731 := bstep (se 1 (by rfl) ⟨4058798, by rfl⟩ : syracuseStep 5411731 = 8117597) B8117597
theorem B3609629 : Blo 948586 3609629 := bstep (se 3 (by rfl) ⟨676805, by rfl⟩ : syracuseStep 3609629 = 1353611) B1353611
theorem B3609643 : Blo 948586 3609643 := bstep (se 1 (by rfl) ⟨2707232, by rfl⟩ : syracuseStep 3609643 = 5414465) B5414465
theorem B2135159 : Blo 948586 2135159 := bstep (se 1 (by rfl) ⟨1601369, by rfl⟩ : syracuseStep 2135159 = 3202739) B3202739
theorem B4822253 : Blo 948586 4822253 := bstep (se 3 (by rfl) ⟨904172, by rfl⟩ : syracuseStep 4822253 = 1808345) B1808345
theorem B2135339 : Blo 948586 2135339 := bstep (se 1 (by rfl) ⟨1601504, by rfl⟩ : syracuseStep 2135339 = 3203009) B3203009
theorem B7214669 : Blo 948586 7214669 := bstep (se 3 (by rfl) ⟨1352750, by rfl⟩ : syracuseStep 7214669 = 2705501) B2705501
theorem B5477975 : Blo 948586 5477975 := bstep (se 1 (by rfl) ⟨4108481, by rfl⟩ : syracuseStep 5477975 = 8216963) B8216963
theorem B2135699 : Blo 948586 2135699 := bstep (se 1 (by rfl) ⟨1601774, by rfl⟩ : syracuseStep 2135699 = 3203549) B3203549
theorem B1808057 : Blo 948586 1808057 := bstep (se 2 (by rfl) ⟨678021, by rfl⟩ : syracuseStep 1808057 = 1356043) B1356043
theorem B2135753 : Blo 948586 2135753 := bstep (se 2 (by rfl) ⟨800907, by rfl⟩ : syracuseStep 2135753 = 1601815) B1601815
theorem B1447739 : Blo 948586 1447739 := bstep (se 1 (by rfl) ⟨1085804, by rfl⟩ : syracuseStep 1447739 = 2171609) B2171609
theorem B17340313 : Blo 948586 17340313 := bstep (se 2 (by rfl) ⟨6502617, by rfl⟩ : syracuseStep 17340313 = 13005235) B13005235
theorem B1218575 : Blo 948586 1218575 := bstep (se 1 (by rfl) ⟨913931, by rfl⟩ : syracuseStep 1218575 = 1827863) B1827863
theorem B1808399 : Blo 948586 1808399 := bstep (se 1 (by rfl) ⟨1356299, by rfl⟩ : syracuseStep 1808399 = 2712599) B2712599
theorem B17307917 : Blo 948586 17307917 := bstep (se 3 (by rfl) ⟨3245234, by rfl⟩ : syracuseStep 17307917 = 6490469) B6490469
theorem B2136455 : Blo 948586 2136455 := bstep (se 1 (by rfl) ⟨1602341, by rfl⟩ : syracuseStep 2136455 = 3204683) B3204683
theorem B59251085 : Blo 948586 59251085 := bstep (se 3 (by rfl) ⟨11109578, by rfl⟩ : syracuseStep 59251085 = 22219157) B22219157
theorem B2136635 : Blo 948586 2136635 := bstep (se 1 (by rfl) ⟨1602476, by rfl⟩ : syracuseStep 2136635 = 3204953) B3204953
theorem B5413463 : Blo 948586 5413463 := bstep (se 1 (by rfl) ⟨4060097, by rfl⟩ : syracuseStep 5413463 = 8120195) B8120195
theorem B2136761 : Blo 948586 2136761 := bstep (se 2 (by rfl) ⟨801285, by rfl⟩ : syracuseStep 2136761 = 1602571) B1602571
theorem B6855425 : Blo 948586 6855425 := bstep (se 2 (by rfl) ⟨2570784, by rfl⟩ : syracuseStep 6855425 = 5141569) B5141569
theorem B2137103 : Blo 948586 2137103 := bstep (se 1 (by rfl) ⟨1602827, by rfl⟩ : syracuseStep 2137103 = 3205655) B3205655
theorem B2137121 : Blo 948586 2137121 := bstep (se 2 (by rfl) ⟨801420, by rfl⟩ : syracuseStep 2137121 = 1602841) B1602841
theorem B4332815 : Blo 948586 4332815 := bstep (se 1 (by rfl) ⟨3249611, by rfl⟩ : syracuseStep 4332815 = 6499223) B6499223
theorem B2137463 : Blo 948586 2137463 := bstep (se 1 (by rfl) ⟨1603097, by rfl⟩ : syracuseStep 2137463 = 3206195) B3206195
theorem B2137643 : Blo 948586 2137643 := bstep (se 1 (by rfl) ⟨1603232, by rfl⟩ : syracuseStep 2137643 = 3206465) B3206465
theorem B4628141 : Blo 948586 4628141 := bstep (se 3 (by rfl) ⟨867776, by rfl⟩ : syracuseStep 4628141 = 1735553) B1735553
theorem B2138003 : Blo 948586 2138003 := bstep (se 1 (by rfl) ⟨1603502, by rfl⟩ : syracuseStep 2138003 = 3207005) B3207005
theorem B20848535 : Blo 948586 20848535 := bstep (se 1 (by rfl) ⟨15636401, by rfl⟩ : syracuseStep 20848535 = 31272803) B31272803
theorem B2138057 : Blo 948586 2138057 := bstep (se 2 (by rfl) ⟨801771, by rfl⟩ : syracuseStep 2138057 = 1603543) B1603543
theorem B7217099 : Blo 948586 7217099 := bstep (se 1 (by rfl) ⟨5412824, by rfl⟩ : syracuseStep 7217099 = 10825649) B10825649
theorem B10297367 : Blo 948586 10297367 := bstep (se 1 (by rfl) ⟨7723025, by rfl⟩ : syracuseStep 10297367 = 15446051) B15446051
theorem B5775533 : Blo 948586 5775533 := bstep (se 3 (by rfl) ⟨1082912, by rfl⟩ : syracuseStep 5775533 = 2165825) B2165825
theorem B16491073 : Blo 948586 16491073 := bstep (se 2 (by rfl) ⟨6184152, by rfl⟩ : syracuseStep 16491073 = 12368305) B12368305
theorem B2138759 : Blo 948586 2138759 := bstep (se 1 (by rfl) ⟨1604069, by rfl⟩ : syracuseStep 2138759 = 3208139) B3208139
theorem B2138939 : Blo 948586 2138939 := bstep (se 1 (by rfl) ⟨1604204, by rfl⟩ : syracuseStep 2138939 = 3208409) B3208409
theorem B3908411 : Blo 948586 3908411 := bstep (se 1 (by rfl) ⟨2931308, by rfl⟩ : syracuseStep 3908411 = 5862617) B5862617
theorem B2139065 : Blo 948586 2139065 := bstep (se 2 (by rfl) ⟨802149, by rfl⟩ : syracuseStep 2139065 = 1604299) B1604299
theorem B1713287 : Blo 948586 1713287 := bstep (se 1 (by rfl) ⟨1284965, by rfl⟩ : syracuseStep 1713287 = 2569931) B2569931
theorem B2401427 : Blo 948586 2401427 := bstep (se 1 (by rfl) ⟨1801070, by rfl⟩ : syracuseStep 2401427 = 3602141) B3602141
theorem B2139407 : Blo 948586 2139407 := bstep (se 1 (by rfl) ⟨1604555, by rfl⟩ : syracuseStep 2139407 = 3209111) B3209111
theorem B2139425 : Blo 948586 2139425 := bstep (se 2 (by rfl) ⟨802284, by rfl⟩ : syracuseStep 2139425 = 1604569) B1604569
theorem B1353019 : Blo 948586 1353019 := bstep (se 1 (by rfl) ⟨1014764, by rfl⟩ : syracuseStep 1353019 = 2029529) B2029529
theorem B16262531 : Blo 948586 16262531 := bstep (se 1 (by rfl) ⟨12196898, by rfl⟩ : syracuseStep 16262531 = 24393797) B24393797
theorem B2401721 : Blo 948586 2401721 := bstep (se 2 (by rfl) ⟨900645, by rfl⟩ : syracuseStep 2401721 = 1801291) B1801291
theorem B2893313 : Blo 948586 2893313 := bstep (se 2 (by rfl) ⟨1084992, by rfl⟩ : syracuseStep 2893313 = 2169985) B2169985
theorem B10692161 : Blo 948586 10692161 := bstep (se 2 (by rfl) ⟨4009560, by rfl⟩ : syracuseStep 10692161 = 8019121) B8019121
theorem B4171331 : Blo 948586 4171331 := bstep (se 1 (by rfl) ⟨3128498, by rfl⟩ : syracuseStep 4171331 = 6256997) B6256997
theorem B2139767 : Blo 948586 2139767 := bstep (se 1 (by rfl) ⟨1604825, by rfl⟩ : syracuseStep 2139767 = 3209651) B3209651
theorem B2139947 : Blo 948586 2139947 := bstep (se 1 (by rfl) ⟨1604960, by rfl⟩ : syracuseStep 2139947 = 3209921) B3209921
theorem B12691403 : Blo 948586 12691403 := bstep (se 1 (by rfl) ⟨9518552, by rfl⟩ : syracuseStep 12691403 = 19037105) B19037105
theorem B1353719 : Blo 948586 1353719 := bstep (se 1 (by rfl) ⟨1015289, by rfl⟩ : syracuseStep 1353719 = 2030579) B2030579
theorem B3614807 : Blo 948586 3614807 := bstep (se 1 (by rfl) ⟨2711105, by rfl⟩ : syracuseStep 3614807 = 5422211) B5422211
theorem B2402419 : Blo 948586 2402419 := bstep (se 1 (by rfl) ⟨1801814, by rfl⟩ : syracuseStep 2402419 = 3603629) B3603629
theorem B2140307 : Blo 948586 2140307 := bstep (se 1 (by rfl) ⟨1605230, by rfl⟩ : syracuseStep 2140307 = 3210461) B3210461
theorem B2140361 : Blo 948586 2140361 := bstep (se 2 (by rfl) ⟨802635, by rfl⟩ : syracuseStep 2140361 = 1605271) B1605271
theorem B2402561 : Blo 948586 2402561 := bstep (se 2 (by rfl) ⟨900960, by rfl⟩ : syracuseStep 2402561 = 1801921) B1801921
theorem B3615293 : Blo 948586 3615293 := bstep (se 3 (by rfl) ⟨677867, by rfl⟩ : syracuseStep 3615293 = 1355735) B1355735
theorem B2403017 : Blo 948586 2403017 := bstep (se 2 (by rfl) ⟨901131, by rfl⟩ : syracuseStep 2403017 = 1802263) B1802263
theorem B25340633 : Blo 948586 25340633 := bstep (se 2 (by rfl) ⟨9502737, by rfl⟩ : syracuseStep 25340633 = 19005475) B19005475
theorem B2141063 : Blo 948586 2141063 := bstep (se 1 (by rfl) ⟨1605797, by rfl⟩ : syracuseStep 2141063 = 3211595) B3211595
theorem B2403371 : Blo 948586 2403371 := bstep (se 1 (by rfl) ⟨1802528, by rfl⟩ : syracuseStep 2403371 = 3605057) B3605057
theorem B2141243 : Blo 948586 2141243 := bstep (se 1 (by rfl) ⟨1605932, by rfl⟩ : syracuseStep 2141243 = 3211865) B3211865
theorem B2141369 : Blo 948586 2141369 := bstep (se 2 (by rfl) ⟨803013, by rfl⟩ : syracuseStep 2141369 = 1606027) B1606027
theorem B6860065 : Blo 948586 6860065 := bstep (se 2 (by rfl) ⟨2572524, by rfl⟩ : syracuseStep 6860065 = 5145049) B5145049
theorem B1355143 : Blo 948586 1355143 := bstep (se 1 (by rfl) ⟨1016357, by rfl⟩ : syracuseStep 1355143 = 2032715) B2032715
theorem B2567681 : Blo 948586 2567681 := bstep (se 2 (by rfl) ⟨962880, by rfl⟩ : syracuseStep 2567681 = 1925761) B1925761
theorem B2141711 : Blo 948586 2141711 := bstep (se 1 (by rfl) ⟨1606283, by rfl⟩ : syracuseStep 2141711 = 3212567) B3212567
theorem B2141729 : Blo 948586 2141729 := bstep (se 2 (by rfl) ⟨803148, by rfl⟩ : syracuseStep 2141729 = 1606297) B1606297
theorem B8662571 : Blo 948586 8662571 := bstep (se 1 (by rfl) ⟨6496928, by rfl⟩ : syracuseStep 8662571 = 12993857) B12993857
theorem B2142071 : Blo 948586 2142071 := bstep (se 1 (by rfl) ⟨1606553, by rfl⟩ : syracuseStep 2142071 = 3213107) B3213107
theorem B1355707 : Blo 948586 1355707 := bstep (se 1 (by rfl) ⟨1016780, by rfl⟩ : syracuseStep 1355707 = 2033561) B2033561
theorem B3616721 : Blo 948586 3616721 := bstep (se 2 (by rfl) ⟨1356270, by rfl⟩ : syracuseStep 3616721 = 2712541) B2712541
theorem B2404363 : Blo 948586 2404363 := bstep (se 1 (by rfl) ⟨1803272, by rfl⟩ : syracuseStep 2404363 = 3606545) B3606545
theorem B2142251 : Blo 948586 2142251 := bstep (se 1 (by rfl) ⟨1606688, by rfl⟩ : syracuseStep 2142251 = 3213377) B3213377
theorem B2404505 : Blo 948586 2404505 := bstep (se 2 (by rfl) ⟨901689, by rfl⟩ : syracuseStep 2404505 = 1803379) B1803379
theorem B2404667 : Blo 948586 2404667 := bstep (se 1 (by rfl) ⟨1803500, by rfl⟩ : syracuseStep 2404667 = 3607001) B3607001
theorem B3092795 : Blo 948586 3092795 := bstep (se 1 (by rfl) ⟨2319596, by rfl⟩ : syracuseStep 3092795 = 4639193) B4639193
theorem B2863421 : Blo 948586 2863421 := bstep (se 3 (by rfl) ⟨536891, by rfl⟩ : syracuseStep 2863421 = 1073783) B1073783
theorem B2142611 : Blo 948586 2142611 := bstep (se 1 (by rfl) ⟨1606958, by rfl⟩ : syracuseStep 2142611 = 3213917) B3213917
theorem B2142665 : Blo 948586 2142665 := bstep (se 2 (by rfl) ⟨803499, by rfl⟩ : syracuseStep 2142665 = 1606999) B1606999
theorem B2568719 : Blo 948586 2568719 := bstep (se 1 (by rfl) ⟨1926539, by rfl⟩ : syracuseStep 2568719 = 3853079) B3853079
theorem B2568763 : Blo 948586 2568763 := bstep (se 1 (by rfl) ⟨1926572, by rfl⟩ : syracuseStep 2568763 = 3853145) B3853145
theorem B8237645 : Blo 948586 8237645 := bstep (se 3 (by rfl) ⟨1544558, by rfl⟩ : syracuseStep 8237645 = 3089117) B3089117
theorem B2405011 : Blo 948586 2405011 := bstep (se 1 (by rfl) ⟨1803758, by rfl⟩ : syracuseStep 2405011 = 3607517) B3607517
theorem B963343 : Blo 948586 963343 := bstep (se 1 (by rfl) ⟨722507, by rfl⟩ : syracuseStep 963343 = 1445015) B1445015
theorem B4567823 : Blo 948586 4567823 := bstep (se 1 (by rfl) ⟨3425867, by rfl⟩ : syracuseStep 4567823 = 6851735) B6851735
theorem B2896669 : Blo 948586 2896669 := bstep (se 3 (by rfl) ⟨543125, by rfl⟩ : syracuseStep 2896669 = 1086251) B1086251
theorem B2405153 : Blo 948586 2405153 := bstep (se 2 (by rfl) ⟨901932, by rfl⟩ : syracuseStep 2405153 = 1803865) B1803865
theorem B5419979 : Blo 948586 5419979 := bstep (se 1 (by rfl) ⟨4064984, by rfl⟩ : syracuseStep 5419979 = 8129969) B8129969
theorem B5649431 : Blo 948586 5649431 := bstep (se 1 (by rfl) ⟨4237073, by rfl⟩ : syracuseStep 5649431 = 8474147) B8474147
theorem B7222445 : Blo 948586 7222445 := bstep (se 3 (by rfl) ⟨1354208, by rfl⟩ : syracuseStep 7222445 = 2708417) B2708417
theorem B3421385 : Blo 948586 3421385 := bstep (se 2 (by rfl) ⟨1283019, by rfl⟩ : syracuseStep 3421385 = 2566039) B2566039
theorem B2569607 : Blo 948586 2569607 := bstep (se 1 (by rfl) ⟨1927205, by rfl⟩ : syracuseStep 2569607 = 3854411) B3854411
theorem B1422905 : Blo 948586 1422905 := bstep (se 2 (by rfl) ⟨533589, by rfl⟩ : syracuseStep 1422905 = 1067179) B1067179
theorem B2569843 : Blo 948586 2569843 := bstep (se 1 (by rfl) ⟨1927382, by rfl⟩ : syracuseStep 2569843 = 3854765) B3854765
theorem B1422983 : Blo 948586 1422983 := bstep (se 1 (by rfl) ⟨1067237, by rfl⟩ : syracuseStep 1422983 = 2134475) B2134475
theorem B1423019 : Blo 948586 1423019 := bstep (se 1 (by rfl) ⟨1067264, by rfl⟩ : syracuseStep 1423019 = 2134529) B2134529
theorem B1423049 : Blo 948586 1423049 := bstep (se 2 (by rfl) ⟨533643, by rfl⟩ : syracuseStep 1423049 = 1067287) B1067287
theorem B2406145 : Blo 948586 2406145 := bstep (se 2 (by rfl) ⟨902304, by rfl⟩ : syracuseStep 2406145 = 1804609) B1804609
theorem B1423163 : Blo 948586 1423163 := bstep (se 1 (by rfl) ⟨1067372, by rfl⟩ : syracuseStep 1423163 = 2134745) B2134745
theorem B1423223 : Blo 948586 1423223 := bstep (se 1 (by rfl) ⟨1067417, by rfl⟩ : syracuseStep 1423223 = 2134835) B2134835
theorem B1423247 : Blo 948586 1423247 := bstep (se 1 (by rfl) ⟨1067435, by rfl⟩ : syracuseStep 1423247 = 2134871) B2134871
theorem B1423289 : Blo 948586 1423289 := bstep (se 2 (by rfl) ⟨533733, by rfl⟩ : syracuseStep 1423289 = 1067467) B1067467
theorem B1423367 : Blo 948586 1423367 := bstep (se 1 (by rfl) ⟨1067525, by rfl⟩ : syracuseStep 1423367 = 2135051) B2135051
theorem B2930717 : Blo 948586 2930717 := bstep (se 3 (by rfl) ⟨549509, by rfl⟩ : syracuseStep 2930717 = 1099019) B1099019
theorem B1423403 : Blo 948586 1423403 := bstep (se 1 (by rfl) ⟨1067552, by rfl⟩ : syracuseStep 1423403 = 2135105) B2135105
theorem B4569149 : Blo 948586 4569149 := bstep (se 3 (by rfl) ⟨856715, by rfl⟩ : syracuseStep 4569149 = 1713431) B1713431
theorem B1423433 : Blo 948586 1423433 := bstep (se 2 (by rfl) ⟨533787, by rfl⟩ : syracuseStep 1423433 = 1067575) B1067575
theorem B1423547 : Blo 948586 1423547 := bstep (se 1 (by rfl) ⟨1067660, by rfl⟩ : syracuseStep 1423547 = 2135321) B2135321
theorem B1423607 : Blo 948586 1423607 := bstep (se 1 (by rfl) ⟨1067705, by rfl⟩ : syracuseStep 1423607 = 2135411) B2135411
theorem B2701583 : Blo 948586 2701583 := bstep (se 1 (by rfl) ⟨2026187, by rfl⟩ : syracuseStep 2701583 = 4052375) B4052375
theorem B1423631 : Blo 948586 1423631 := bstep (se 1 (by rfl) ⟨1067723, by rfl⟩ : syracuseStep 1423631 = 2135447) B2135447
theorem B4176143 : Blo 948586 4176143 := bstep (se 1 (by rfl) ⟨3132107, by rfl⟩ : syracuseStep 4176143 = 6264215) B6264215
theorem B1423673 : Blo 948586 1423673 := bstep (se 2 (by rfl) ⟨533877, by rfl⟩ : syracuseStep 1423673 = 1067755) B1067755
theorem B2931005 : Blo 948586 2931005 := bstep (se 3 (by rfl) ⟨549563, by rfl⟩ : syracuseStep 2931005 = 1099127) B1099127
theorem B2406743 : Blo 948586 2406743 := bstep (se 1 (by rfl) ⟨1805057, by rfl⟩ : syracuseStep 2406743 = 3610115) B3610115
theorem B10271069 : Blo 948586 10271069 := bstep (se 3 (by rfl) ⟨1925825, by rfl⟩ : syracuseStep 10271069 = 3851651) B3851651
theorem B1423751 : Blo 948586 1423751 := bstep (se 1 (by rfl) ⟨1067813, by rfl⟩ : syracuseStep 1423751 = 2135627) B2135627
theorem B1423787 : Blo 948586 1423787 := bstep (se 1 (by rfl) ⟨1067840, by rfl⟩ : syracuseStep 1423787 = 2135681) B2135681
theorem B1423817 : Blo 948586 1423817 := bstep (se 2 (by rfl) ⟨533931, by rfl⟩ : syracuseStep 1423817 = 1067863) B1067863
theorem B9124301 : Blo 948586 9124301 := bstep (se 3 (by rfl) ⟨1710806, by rfl⟩ : syracuseStep 9124301 = 3421613) B3421613
theorem B2406955 : Blo 948586 2406955 := bstep (se 1 (by rfl) ⟨1805216, by rfl⟩ : syracuseStep 2406955 = 3610433) B3610433
theorem B1423931 : Blo 948586 1423931 := bstep (se 1 (by rfl) ⟨1067948, by rfl⟩ : syracuseStep 1423931 = 2135897) B2135897
theorem B1423991 : Blo 948586 1423991 := bstep (se 1 (by rfl) ⟨1067993, by rfl⟩ : syracuseStep 1423991 = 2135987) B2135987
theorem B1424015 : Blo 948586 1424015 := bstep (se 1 (by rfl) ⟨1068011, by rfl⟩ : syracuseStep 1424015 = 2136023) B2136023
theorem B1424057 : Blo 948586 1424057 := bstep (se 2 (by rfl) ⟨534021, by rfl⟩ : syracuseStep 1424057 = 1068043) B1068043
theorem B2407097 : Blo 948586 2407097 := bstep (se 2 (by rfl) ⟨902661, by rfl⟩ : syracuseStep 2407097 = 1805323) B1805323
theorem B9124609 : Blo 948586 9124609 := bstep (se 2 (by rfl) ⟨3421728, by rfl⟩ : syracuseStep 9124609 = 6843457) B6843457
theorem B1424135 : Blo 948586 1424135 := bstep (se 1 (by rfl) ⟨1068101, by rfl⟩ : syracuseStep 1424135 = 2136203) B2136203
theorem B1424171 : Blo 948586 1424171 := bstep (se 1 (by rfl) ⟨1068128, by rfl⟩ : syracuseStep 1424171 = 2136257) B2136257
theorem B8108849 : Blo 948586 8108849 := bstep (se 2 (by rfl) ⟨3040818, by rfl⟩ : syracuseStep 8108849 = 6081637) B6081637
theorem B1424201 : Blo 948586 1424201 := bstep (se 2 (by rfl) ⟨534075, by rfl⟩ : syracuseStep 1424201 = 1068151) B1068151
theorem B1424315 : Blo 948586 1424315 := bstep (se 1 (by rfl) ⟨1068236, by rfl⟩ : syracuseStep 1424315 = 2136473) B2136473
theorem B1424375 : Blo 948586 1424375 := bstep (se 1 (by rfl) ⟨1068281, by rfl⟩ : syracuseStep 1424375 = 2136563) B2136563
theorem B26000389 : Blo 948586 26000389 := bstep (se 4 (by rfl) ⟨2437536, by rfl⟩ : syracuseStep 26000389 = 4875073) B4875073
theorem B1424399 : Blo 948586 1424399 := bstep (se 1 (by rfl) ⟨1068299, by rfl⟩ : syracuseStep 1424399 = 2136599) B2136599
theorem B1424441 : Blo 948586 1424441 := bstep (se 2 (by rfl) ⟨534165, by rfl⟩ : syracuseStep 1424441 = 1068331) B1068331
theorem B1424519 : Blo 948586 1424519 := bstep (se 1 (by rfl) ⟨1068389, by rfl⟩ : syracuseStep 1424519 = 2136779) B2136779
theorem B1424555 : Blo 948586 1424555 := bstep (se 1 (by rfl) ⟨1068416, by rfl⟩ : syracuseStep 1424555 = 2136833) B2136833
theorem B1424585 : Blo 948586 1424585 := bstep (se 2 (by rfl) ⟨534219, by rfl⟩ : syracuseStep 1424585 = 1068439) B1068439
theorem B1424699 : Blo 948586 1424699 := bstep (se 1 (by rfl) ⟨1068524, by rfl⟩ : syracuseStep 1424699 = 2137049) B2137049
theorem B1424759 : Blo 948586 1424759 := bstep (se 1 (by rfl) ⟨1068569, by rfl⟩ : syracuseStep 1424759 = 2137139) B2137139
theorem B1424783 : Blo 948586 1424783 := bstep (se 1 (by rfl) ⟨1068587, by rfl⟩ : syracuseStep 1424783 = 2137175) B2137175
theorem B1424825 : Blo 948586 1424825 := bstep (se 2 (by rfl) ⟨534309, by rfl⟩ : syracuseStep 1424825 = 1068619) B1068619
theorem B1424903 : Blo 948586 1424903 := bstep (se 1 (by rfl) ⟨1068677, by rfl⟩ : syracuseStep 1424903 = 2137355) B2137355
theorem B7224875 : Blo 948586 7224875 := bstep (se 1 (by rfl) ⟨5418656, by rfl⟩ : syracuseStep 7224875 = 10837313) B10837313
theorem B1424939 : Blo 948586 1424939 := bstep (se 1 (by rfl) ⟨1068704, by rfl⟩ : syracuseStep 1424939 = 2137409) B2137409
theorem B1424969 : Blo 948586 1424969 := bstep (se 2 (by rfl) ⟨534363, by rfl⟩ : syracuseStep 1424969 = 1068727) B1068727
theorem B3423863 : Blo 948586 3423863 := bstep (se 1 (by rfl) ⟨2567897, by rfl⟩ : syracuseStep 3423863 = 5135795) B5135795
theorem B2408089 : Blo 948586 2408089 := bstep (se 2 (by rfl) ⟨903033, by rfl⟩ : syracuseStep 2408089 = 1806067) B1806067
theorem B1425083 : Blo 948586 1425083 := bstep (se 1 (by rfl) ⟨1068812, by rfl⟩ : syracuseStep 1425083 = 2137625) B2137625
theorem B1425143 : Blo 948586 1425143 := bstep (se 1 (by rfl) ⟨1068857, by rfl⟩ : syracuseStep 1425143 = 2137715) B2137715
theorem B1425167 : Blo 948586 1425167 := bstep (se 1 (by rfl) ⟨1068875, by rfl⟩ : syracuseStep 1425167 = 2137751) B2137751
theorem B1425209 : Blo 948586 1425209 := bstep (se 2 (by rfl) ⟨534453, by rfl⟩ : syracuseStep 1425209 = 1068907) B1068907
theorem B2408251 : Blo 948586 2408251 := bstep (se 1 (by rfl) ⟨1806188, by rfl⟩ : syracuseStep 2408251 = 3612377) B3612377
theorem B2703223 : Blo 948586 2703223 := bstep (se 1 (by rfl) ⟨2027417, by rfl⟩ : syracuseStep 2703223 = 4054835) B4054835
theorem B1425287 : Blo 948586 1425287 := bstep (se 1 (by rfl) ⟨1068965, by rfl⟩ : syracuseStep 1425287 = 2137931) B2137931
theorem B1425323 : Blo 948586 1425323 := bstep (se 1 (by rfl) ⟨1068992, by rfl⟩ : syracuseStep 1425323 = 2137985) B2137985
theorem B1425353 : Blo 948586 1425353 := bstep (se 2 (by rfl) ⟨534507, by rfl⟩ : syracuseStep 1425353 = 1069015) B1069015
theorem B2408393 : Blo 948586 2408393 := bstep (se 2 (by rfl) ⟨903147, by rfl⟩ : syracuseStep 2408393 = 1806295) B1806295
theorem B2572289 : Blo 948586 2572289 := bstep (se 2 (by rfl) ⟨964608, by rfl⟩ : syracuseStep 2572289 = 1929217) B1929217
theorem B1425467 : Blo 948586 1425467 := bstep (se 1 (by rfl) ⟨1069100, by rfl⟩ : syracuseStep 1425467 = 2138201) B2138201
theorem B1425527 : Blo 948586 1425527 := bstep (se 1 (by rfl) ⟨1069145, by rfl⟩ : syracuseStep 1425527 = 2138291) B2138291
theorem B1425551 : Blo 948586 1425551 := bstep (se 1 (by rfl) ⟨1069163, by rfl⟩ : syracuseStep 1425551 = 2138327) B2138327
theorem B1425593 : Blo 948586 1425593 := bstep (se 2 (by rfl) ⟨534597, by rfl⟩ : syracuseStep 1425593 = 1069195) B1069195
theorem B6078665 : Blo 948586 6078665 := bstep (se 2 (by rfl) ⟨2279499, by rfl⟩ : syracuseStep 6078665 = 4558999) B4558999
theorem B1425671 : Blo 948586 1425671 := bstep (se 1 (by rfl) ⟨1069253, by rfl⟩ : syracuseStep 1425671 = 2138507) B2138507
theorem B2408737 : Blo 948586 2408737 := bstep (se 2 (by rfl) ⟨903276, by rfl⟩ : syracuseStep 2408737 = 1806553) B1806553
theorem B1425707 : Blo 948586 1425707 := bstep (se 1 (by rfl) ⟨1069280, by rfl⟩ : syracuseStep 1425707 = 2138561) B2138561
theorem B1425737 : Blo 948586 1425737 := bstep (se 2 (by rfl) ⟨534651, by rfl⟩ : syracuseStep 1425737 = 1069303) B1069303
theorem B1425851 : Blo 948586 1425851 := bstep (se 1 (by rfl) ⟨1069388, by rfl⟩ : syracuseStep 1425851 = 2138777) B2138777
theorem B1425911 : Blo 948586 1425911 := bstep (se 1 (by rfl) ⟨1069433, by rfl⟩ : syracuseStep 1425911 = 2138867) B2138867
theorem B1425935 : Blo 948586 1425935 := bstep (se 1 (by rfl) ⟨1069451, by rfl⟩ : syracuseStep 1425935 = 2138903) B2138903
theorem B1425977 : Blo 948586 1425977 := bstep (se 2 (by rfl) ⟨534741, by rfl⟩ : syracuseStep 1425977 = 1069483) B1069483
theorem B1426055 : Blo 948586 1426055 := bstep (se 1 (by rfl) ⟨1069541, by rfl⟩ : syracuseStep 1426055 = 2139083) B2139083
theorem B1426091 : Blo 948586 1426091 := bstep (se 1 (by rfl) ⟨1069568, by rfl⟩ : syracuseStep 1426091 = 2139137) B2139137
theorem B1098427 : Blo 948586 1098427 := bstep (se 1 (by rfl) ⟨823820, by rfl⟩ : syracuseStep 1098427 = 1647641) B1647641
theorem B1426121 : Blo 948586 1426121 := bstep (se 2 (by rfl) ⟨534795, by rfl⟩ : syracuseStep 1426121 = 1069591) B1069591
theorem B1426235 : Blo 948586 1426235 := bstep (se 1 (by rfl) ⟨1069676, by rfl⟩ : syracuseStep 1426235 = 2139353) B2139353
theorem B13190003 : Blo 948586 13190003 := bstep (se 1 (by rfl) ⟨9892502, by rfl⟩ : syracuseStep 13190003 = 19785005) B19785005
theorem B1426295 : Blo 948586 1426295 := bstep (se 1 (by rfl) ⟨1069721, by rfl⟩ : syracuseStep 1426295 = 2139443) B2139443
theorem B2409335 : Blo 948586 2409335 := bstep (se 1 (by rfl) ⟨1807001, by rfl⟩ : syracuseStep 2409335 = 3614003) B3614003
theorem B1426319 : Blo 948586 1426319 := bstep (se 1 (by rfl) ⟨1069739, by rfl⟩ : syracuseStep 1426319 = 2139479) B2139479
theorem B4113337 : Blo 948586 4113337 := bstep (se 2 (by rfl) ⟨1542501, by rfl⟩ : syracuseStep 4113337 = 3085003) B3085003
theorem B1426361 : Blo 948586 1426361 := bstep (se 2 (by rfl) ⟨534885, by rfl⟩ : syracuseStep 1426361 = 1069771) B1069771
theorem B1426439 : Blo 948586 1426439 := bstep (se 1 (by rfl) ⟨1069829, by rfl⟩ : syracuseStep 1426439 = 2139659) B2139659
theorem B1426475 : Blo 948586 1426475 := bstep (se 1 (by rfl) ⟨1069856, by rfl⟩ : syracuseStep 1426475 = 2139713) B2139713
theorem B1426505 : Blo 948586 1426505 := bstep (se 2 (by rfl) ⟨534939, by rfl⟩ : syracuseStep 1426505 = 1069879) B1069879
theorem B2704499 : Blo 948586 2704499 := bstep (se 1 (by rfl) ⟨2028374, by rfl⟩ : syracuseStep 2704499 = 4056749) B4056749
theorem B1426619 : Blo 948586 1426619 := bstep (se 1 (by rfl) ⟨1069964, by rfl⟩ : syracuseStep 1426619 = 2139929) B2139929
theorem B1426679 : Blo 948586 1426679 := bstep (se 1 (by rfl) ⟨1070009, by rfl⟩ : syracuseStep 1426679 = 2140019) B2140019
theorem B1426703 : Blo 948586 1426703 := bstep (se 1 (by rfl) ⟨1070027, by rfl⟩ : syracuseStep 1426703 = 2140055) B2140055
theorem B1426745 : Blo 948586 1426745 := bstep (se 2 (by rfl) ⟨535029, by rfl⟩ : syracuseStep 1426745 = 1070059) B1070059
theorem B2704727 : Blo 948586 2704727 := bstep (se 1 (by rfl) ⟨2028545, by rfl⟩ : syracuseStep 2704727 = 4057091) B4057091
theorem B1426823 : Blo 948586 1426823 := bstep (se 1 (by rfl) ⟨1070117, by rfl⟩ : syracuseStep 1426823 = 2140235) B2140235
theorem B19547527 : Blo 948586 19547527 := bstep (se 1 (by rfl) ⟨14660645, by rfl⟩ : syracuseStep 19547527 = 29321291) B29321291
theorem B1426859 : Blo 948586 1426859 := bstep (se 1 (by rfl) ⟨1070144, by rfl⟩ : syracuseStep 1426859 = 2140289) B2140289
theorem B1426889 : Blo 948586 1426889 := bstep (se 2 (by rfl) ⟨535083, by rfl⟩ : syracuseStep 1426889 = 1070167) B1070167
theorem B2344459 : Blo 948586 2344459 := bstep (se 1 (by rfl) ⟨1758344, by rfl⟩ : syracuseStep 2344459 = 3516689) B3516689
theorem B1427003 : Blo 948586 1427003 := bstep (se 1 (by rfl) ⟨1070252, by rfl⟩ : syracuseStep 1427003 = 2140505) B2140505
theorem B1427063 : Blo 948586 1427063 := bstep (se 1 (by rfl) ⟨1070297, by rfl⟩ : syracuseStep 1427063 = 2140595) B2140595
theorem B1427087 : Blo 948586 1427087 := bstep (se 1 (by rfl) ⟨1070315, by rfl⟩ : syracuseStep 1427087 = 2140631) B2140631
theorem B1427129 : Blo 948586 1427129 := bstep (se 2 (by rfl) ⟨535173, by rfl⟩ : syracuseStep 1427129 = 1070347) B1070347
theorem B1427207 : Blo 948586 1427207 := bstep (se 1 (by rfl) ⟨1070405, by rfl⟩ : syracuseStep 1427207 = 2140811) B2140811
theorem B5129999 : Blo 948586 5129999 := bstep (se 1 (by rfl) ⟨3847499, by rfl⟩ : syracuseStep 5129999 = 7694999) B7694999
theorem B1427243 : Blo 948586 1427243 := bstep (se 1 (by rfl) ⟨1070432, by rfl⟩ : syracuseStep 1427243 = 2140865) B2140865
theorem B1427273 : Blo 948586 1427273 := bstep (se 2 (by rfl) ⟨535227, by rfl⟩ : syracuseStep 1427273 = 1070455) B1070455
theorem B4802489 : Blo 948586 4802489 := bstep (se 2 (by rfl) ⟨1800933, by rfl⟩ : syracuseStep 4802489 = 3601867) B3601867
theorem B1427387 : Blo 948586 1427387 := bstep (se 1 (by rfl) ⟨1070540, by rfl⟩ : syracuseStep 1427387 = 2141081) B2141081
theorem B1427447 : Blo 948586 1427447 := bstep (se 1 (by rfl) ⟨1070585, by rfl⟩ : syracuseStep 1427447 = 2141171) B2141171
theorem B21940237 : Blo 948586 21940237 := bstep (se 3 (by rfl) ⟨4113794, by rfl⟩ : syracuseStep 21940237 = 8227589) B8227589
theorem B1427471 : Blo 948586 1427471 := bstep (se 1 (by rfl) ⟨1070603, by rfl⟩ : syracuseStep 1427471 = 2141207) B2141207
theorem B1427513 : Blo 948586 1427513 := bstep (se 2 (by rfl) ⟨535317, by rfl⟩ : syracuseStep 1427513 = 1070635) B1070635
theorem B1427591 : Blo 948586 1427591 := bstep (se 1 (by rfl) ⟨1070693, by rfl⟩ : syracuseStep 1427591 = 2141387) B2141387
theorem B2410631 : Blo 948586 2410631 := bstep (se 1 (by rfl) ⟨1807973, by rfl⟩ : syracuseStep 2410631 = 3615947) B3615947
theorem B1427627 : Blo 948586 1427627 := bstep (se 1 (by rfl) ⟨1070720, by rfl⟩ : syracuseStep 1427627 = 2141441) B2141441
theorem B2410681 : Blo 948586 2410681 := bstep (se 2 (by rfl) ⟨904005, by rfl⟩ : syracuseStep 2410681 = 1808011) B1808011
theorem B1427657 : Blo 948586 1427657 := bstep (se 2 (by rfl) ⟨535371, by rfl⟩ : syracuseStep 1427657 = 1070743) B1070743
theorem B5130497 : Blo 948586 5130497 := bstep (se 2 (by rfl) ⟨1923936, by rfl⟩ : syracuseStep 5130497 = 3847873) B3847873
theorem B1067323 : Blo 948586 1067323 := bstep (se 1 (by rfl) ⟨800492, by rfl⟩ : syracuseStep 1067323 = 1600985) B1600985
theorem B1427771 : Blo 948586 1427771 := bstep (se 1 (by rfl) ⟨1070828, by rfl⟩ : syracuseStep 1427771 = 2141657) B2141657
theorem B1427831 : Blo 948586 1427831 := bstep (se 1 (by rfl) ⟨1070873, by rfl⟩ : syracuseStep 1427831 = 2141747) B2141747
theorem B1427855 : Blo 948586 1427855 := bstep (se 1 (by rfl) ⟨1070891, by rfl⟩ : syracuseStep 1427855 = 2141783) B2141783
theorem B1427897 : Blo 948586 1427897 := bstep (se 2 (by rfl) ⟨535461, by rfl⟩ : syracuseStep 1427897 = 1070923) B1070923
theorem B7719389 : Blo 948586 7719389 := bstep (se 3 (by rfl) ⟨1447385, by rfl⟩ : syracuseStep 7719389 = 2894771) B2894771
theorem B1427975 : Blo 948586 1427975 := bstep (se 1 (by rfl) ⟨1070981, by rfl⟩ : syracuseStep 1427975 = 2141963) B2141963
theorem B1428011 : Blo 948586 1428011 := bstep (se 1 (by rfl) ⟨1071008, by rfl⟩ : syracuseStep 1428011 = 2142017) B2142017
theorem B1428041 : Blo 948586 1428041 := bstep (se 2 (by rfl) ⟨535515, by rfl⟩ : syracuseStep 1428041 = 1071031) B1071031
theorem B1428155 : Blo 948586 1428155 := bstep (se 1 (by rfl) ⟨1071116, by rfl⟩ : syracuseStep 1428155 = 2142233) B2142233
theorem B1428215 : Blo 948586 1428215 := bstep (se 1 (by rfl) ⟨1071161, by rfl⟩ : syracuseStep 1428215 = 2142323) B2142323
theorem B1067791 : Blo 948586 1067791 := bstep (se 1 (by rfl) ⟨800843, by rfl⟩ : syracuseStep 1067791 = 1601687) B1601687
theorem B1428239 : Blo 948586 1428239 := bstep (se 1 (by rfl) ⟨1071179, by rfl⟩ : syracuseStep 1428239 = 2142359) B2142359
theorem B1428281 : Blo 948586 1428281 := bstep (se 2 (by rfl) ⟨535605, by rfl⟩ : syracuseStep 1428281 = 1071211) B1071211
theorem B2280307 : Blo 948586 2280307 := bstep (se 1 (by rfl) ⟨1710230, by rfl⟩ : syracuseStep 2280307 = 3420461) B3420461
theorem B2706311 : Blo 948586 2706311 := bstep (se 1 (by rfl) ⟨2029733, by rfl⟩ : syracuseStep 2706311 = 4059467) B4059467
theorem B1428359 : Blo 948586 1428359 := bstep (se 1 (by rfl) ⟨1071269, by rfl⟩ : syracuseStep 1428359 = 2142539) B2142539
theorem B1428395 : Blo 948586 1428395 := bstep (se 1 (by rfl) ⟨1071296, by rfl⟩ : syracuseStep 1428395 = 2142593) B2142593
theorem B1428425 : Blo 948586 1428425 := bstep (se 2 (by rfl) ⟨535659, by rfl⟩ : syracuseStep 1428425 = 1071319) B1071319
theorem B1428539 : Blo 948586 1428539 := bstep (se 1 (by rfl) ⟨1071404, by rfl⟩ : syracuseStep 1428539 = 2142809) B2142809
theorem B2706493 : Blo 948586 2706493 := bstep (se 3 (by rfl) ⟨507467, by rfl⟩ : syracuseStep 2706493 = 1014935) B1014935
theorem B1428599 : Blo 948586 1428599 := bstep (se 1 (by rfl) ⟨1071449, by rfl⟩ : syracuseStep 1428599 = 2142899) B2142899
theorem B1428623 : Blo 948586 1428623 := bstep (se 1 (by rfl) ⟨1071467, by rfl⟩ : syracuseStep 1428623 = 2142935) B2142935
theorem B1428665 : Blo 948586 1428665 := bstep (se 2 (by rfl) ⟨535749, by rfl⟩ : syracuseStep 1428665 = 1071499) B1071499
theorem B4803785 : Blo 948586 4803785 := bstep (se 2 (by rfl) ⟨1801419, by rfl⟩ : syracuseStep 4803785 = 3602839) B3602839
theorem B1068295 : Blo 948586 1068295 := bstep (se 1 (by rfl) ⟨801221, by rfl⟩ : syracuseStep 1068295 = 1602443) B1602443
theorem B1428743 : Blo 948586 1428743 := bstep (se 1 (by rfl) ⟨1071557, by rfl⟩ : syracuseStep 1428743 = 2143115) B2143115
theorem B2542859 : Blo 948586 2542859 := bstep (se 1 (by rfl) ⟨1907144, by rfl⟩ : syracuseStep 2542859 = 3814289) B3814289
theorem B1428779 : Blo 948586 1428779 := bstep (se 1 (by rfl) ⟨1071584, by rfl⟩ : syracuseStep 1428779 = 2143169) B2143169
theorem B1428809 : Blo 948586 1428809 := bstep (se 2 (by rfl) ⟨535803, by rfl⟩ : syracuseStep 1428809 = 1071607) B1071607
theorem B2346355 : Blo 948586 2346355 := bstep (se 1 (by rfl) ⟨1759766, by rfl⟩ : syracuseStep 2346355 = 3519533) B3519533
theorem B5787065 : Blo 948586 5787065 := bstep (se 2 (by rfl) ⟨2170149, by rfl⟩ : syracuseStep 5787065 = 4340299) B4340299
theorem B1068475 : Blo 948586 1068475 := bstep (se 1 (by rfl) ⟨801356, by rfl⟩ : syracuseStep 1068475 = 1602713) B1602713
theorem B2706959 : Blo 948586 2706959 := bstep (se 1 (by rfl) ⟨2030219, by rfl⟩ : syracuseStep 2706959 = 4060439) B4060439
theorem B4574839 : Blo 948586 4574839 := bstep (se 1 (by rfl) ⟨3431129, by rfl⟩ : syracuseStep 4574839 = 6862259) B6862259
theorem B1068943 : Blo 948586 1068943 := bstep (se 1 (by rfl) ⟨801707, by rfl⟩ : syracuseStep 1068943 = 1603415) B1603415
theorem B9129995 : Blo 948586 9129995 := bstep (se 1 (by rfl) ⟨6847496, by rfl⟩ : syracuseStep 9129995 = 13694993) B13694993
theorem B3428419 : Blo 948586 3428419 := bstep (se 1 (by rfl) ⟨2571314, by rfl⟩ : syracuseStep 3428419 = 5142629) B5142629
theorem B1069447 : Blo 948586 1069447 := bstep (se 1 (by rfl) ⟨802085, by rfl⟩ : syracuseStep 1069447 = 1604171) B1604171
theorem B10834397 : Blo 948586 10834397 := bstep (se 3 (by rfl) ⟨2031449, by rfl⟩ : syracuseStep 10834397 = 4062899) B4062899
theorem B2740751 : Blo 948586 2740751 := bstep (se 1 (by rfl) ⟨2055563, by rfl⟩ : syracuseStep 2740751 = 4111127) B4111127
theorem B1200683 : Blo 948586 1200683 := bstep (se 1 (by rfl) ⟨900512, by rfl⟩ : syracuseStep 1200683 = 1801025) B1801025
theorem B1069627 : Blo 948586 1069627 := bstep (se 1 (by rfl) ⟨802220, by rfl⟩ : syracuseStep 1069627 = 1604441) B1604441
theorem B37606069 : Blo 948586 37606069 := bstep (se 5 (by rfl) ⟨1762784, by rfl⟩ : syracuseStep 37606069 = 3525569) B3525569
theorem B2708225 : Blo 948586 2708225 := bstep (se 2 (by rfl) ⟨1015584, by rfl⟩ : syracuseStep 2708225 = 2031169) B2031169
theorem B7721729 : Blo 948586 7721729 := bstep (se 2 (by rfl) ⟨2895648, by rfl⟩ : syracuseStep 7721729 = 5791297) B5791297
theorem B12342131 : Blo 948586 12342131 := bstep (se 1 (by rfl) ⟨9256598, by rfl⟩ : syracuseStep 12342131 = 18513197) B18513197
theorem B1201159 : Blo 948586 1201159 := bstep (se 1 (by rfl) ⟨900869, by rfl⟩ : syracuseStep 1201159 = 1801739) B1801739
theorem B1070095 : Blo 948586 1070095 := bstep (se 1 (by rfl) ⟨802571, by rfl⟩ : syracuseStep 1070095 = 1605143) B1605143
theorem B1201655 : Blo 948586 1201655 := bstep (se 1 (by rfl) ⟨901241, by rfl⟩ : syracuseStep 1201655 = 1802483) B1802483
theorem B1070599 : Blo 948586 1070599 := bstep (se 1 (by rfl) ⟨802949, by rfl⟩ : syracuseStep 1070599 = 1605899) B1605899
theorem B116872733 : Blo 948586 116872733 := bstep (se 3 (by rfl) ⟨21913637, by rfl⟩ : syracuseStep 116872733 = 43827275) B43827275
theorem B1201807 : Blo 948586 1201807 := bstep (se 1 (by rfl) ⟨901355, by rfl⟩ : syracuseStep 1201807 = 1802711) B1802711
theorem B1070779 : Blo 948586 1070779 := bstep (se 1 (by rfl) ⟨803084, by rfl⟩ : syracuseStep 1070779 = 1606169) B1606169
theorem B4052717 : Blo 948586 4052717 := bstep (se 3 (by rfl) ⟨759884, by rfl⟩ : syracuseStep 4052717 = 1519769) B1519769
theorem B1201979 : Blo 948586 1201979 := bstep (se 1 (by rfl) ⟨901484, by rfl⟩ : syracuseStep 1201979 = 1802969) B1802969
theorem B2283383 : Blo 948586 2283383 := bstep (se 1 (by rfl) ⟨1712537, by rfl⟩ : syracuseStep 2283383 = 3425075) B3425075
theorem B1071247 : Blo 948586 1071247 := bstep (se 1 (by rfl) ⟨803435, by rfl⟩ : syracuseStep 1071247 = 1606871) B1606871
theorem B1300667 : Blo 948586 1300667 := bstep (se 1 (by rfl) ⟨975500, by rfl⟩ : syracuseStep 1300667 = 1951001) B1951001
theorem B2709875 : Blo 948586 2709875 := bstep (se 1 (by rfl) ⟨2032406, by rfl⟩ : syracuseStep 2709875 = 4064813) B4064813
theorem B4872595 : Blo 948586 4872595 := bstep (se 1 (by rfl) ⟨3654446, by rfl⟩ : syracuseStep 4872595 = 7308893) B7308893
theorem B4053401 : Blo 948586 4053401 := bstep (se 2 (by rfl) ⟨1520025, by rfl⟩ : syracuseStep 4053401 = 3040051) B3040051
theorem B3430955 : Blo 948586 3430955 := bstep (se 1 (by rfl) ⟨2573216, by rfl⟩ : syracuseStep 3430955 = 5146433) B5146433
theorem B1202951 : Blo 948586 1202951 := bstep (se 1 (by rfl) ⟨902213, by rfl⟩ : syracuseStep 1202951 = 1804427) B1804427
theorem B2710331 : Blo 948586 2710331 := bstep (se 1 (by rfl) ⟨2032748, by rfl⟩ : syracuseStep 2710331 = 4065497) B4065497
theorem B5200919 : Blo 948586 5200919 := bstep (se 1 (by rfl) ⟨3900689, by rfl⟩ : syracuseStep 5200919 = 7801379) B7801379
theorem B3202091 : Blo 948586 3202091 := bstep (se 1 (by rfl) ⟨2401568, by rfl⟩ : syracuseStep 3202091 = 4803137) B4803137
theorem B1924139 : Blo 948586 1924139 := bstep (se 1 (by rfl) ⟨1443104, by rfl⟩ : syracuseStep 1924139 = 2886209) B2886209
theorem B2284843 : Blo 948586 2284843 := bstep (se 1 (by rfl) ⟨1713632, by rfl⟩ : syracuseStep 2284843 = 3427265) B3427265
theorem B1203599 : Blo 948586 1203599 := bstep (se 1 (by rfl) ⟨902699, by rfl⟩ : syracuseStep 1203599 = 1805399) B1805399
theorem B2711083 : Blo 948586 2711083 := bstep (se 1 (by rfl) ⟨2033312, by rfl⟩ : syracuseStep 2711083 = 4066625) B4066625
theorem B2711357 : Blo 948586 2711357 := bstep (se 3 (by rfl) ⟨508379, by rfl⟩ : syracuseStep 2711357 = 1016759) B1016759
theorem B2285459 : Blo 948586 2285459 := bstep (se 1 (by rfl) ⟨1714094, by rfl⟩ : syracuseStep 2285459 = 3428189) B3428189
theorem B7233623 : Blo 948586 7233623 := bstep (se 1 (by rfl) ⟨5425217, by rfl⟩ : syracuseStep 7233623 = 10850435) B10850435
theorem B3432685 : Blo 948586 3432685 := bstep (se 3 (by rfl) ⟨643628, by rfl⟩ : syracuseStep 3432685 = 1287257) B1287257
theorem B3203387 : Blo 948586 3203387 := bstep (se 1 (by rfl) ⟨2402540, by rfl⟩ : syracuseStep 3203387 = 4805081) B4805081
theorem B2285911 : Blo 948586 2285911 := bstep (se 1 (by rfl) ⟨1714433, by rfl⟩ : syracuseStep 2285911 = 3428867) B3428867
theorem B2285939 : Blo 948586 2285939 := bstep (se 1 (by rfl) ⟨1714454, by rfl⟩ : syracuseStep 2285939 = 3428909) B3428909
theorem B65724817 : Blo 948586 65724817 := bstep (se 2 (by rfl) ⟨24646806, by rfl⟩ : syracuseStep 65724817 = 49293613) B49293613
theorem B2712199 : Blo 948586 2712199 := bstep (se 1 (by rfl) ⟨2034149, by rfl⟩ : syracuseStep 2712199 = 4068299) B4068299
theorem B3203873 : Blo 948586 3203873 := bstep (se 2 (by rfl) ⟨1201452, by rfl⟩ : syracuseStep 3203873 = 2402905) B2402905
theorem B4809617 : Blo 948586 4809617 := bstep (se 2 (by rfl) ⟨1803606, by rfl⟩ : syracuseStep 4809617 = 3607213) B3607213
theorem B2712473 : Blo 948586 2712473 := bstep (se 2 (by rfl) ⟨1017177, by rfl⟩ : syracuseStep 2712473 = 2034355) B2034355
theorem B9135341 : Blo 948586 9135341 := bstep (se 3 (by rfl) ⟨1712876, by rfl⟩ : syracuseStep 9135341 = 3425753) B3425753
theorem B2286863 : Blo 948586 2286863 := bstep (se 1 (by rfl) ⟨1715147, by rfl⟩ : syracuseStep 2286863 = 3430295) B3430295
theorem B2286881 : Blo 948586 2286881 := bstep (se 2 (by rfl) ⟨857580, by rfl⟩ : syracuseStep 2286881 = 1715161) B1715161
theorem B1926443 : Blo 948586 1926443 := bstep (se 1 (by rfl) ⟨1444832, by rfl⟩ : syracuseStep 1926443 = 2889665) B2889665
theorem B3204467 : Blo 948586 3204467 := bstep (se 1 (by rfl) ⟨2403350, by rfl⟩ : syracuseStep 3204467 = 4806701) B4806701
theorem B3663389 : Blo 948586 3663389 := bstep (se 3 (by rfl) ⟨686885, by rfl⟩ : syracuseStep 3663389 = 1373771) B1373771
theorem B23095313 : Blo 948586 23095313 := bstep (se 2 (by rfl) ⟨8660742, by rfl⟩ : syracuseStep 23095313 = 17321485) B17321485
theorem B9398359 : Blo 948586 9398359 := bstep (se 1 (by rfl) ⟨7048769, by rfl⟩ : syracuseStep 9398359 = 14097539) B14097539
theorem B16214417 : Blo 948586 16214417 := bstep (se 2 (by rfl) ⟨6080406, by rfl⟩ : syracuseStep 16214417 = 12160813) B12160813
theorem B4057553 : Blo 948586 4057553 := bstep (se 2 (by rfl) ⟨1521582, by rfl⟩ : syracuseStep 4057553 = 3043165) B3043165
theorem B8677891 : Blo 948586 8677891 := bstep (se 1 (by rfl) ⟨6508418, by rfl⟩ : syracuseStep 8677891 = 13016837) B13016837
theorem B2026043 : Blo 948586 2026043 := bstep (se 1 (by rfl) ⟨1519532, by rfl⟩ : syracuseStep 2026043 = 3039065) B3039065
theorem B7825997 : Blo 948586 7825997 := bstep (se 3 (by rfl) ⟨1467374, by rfl⟩ : syracuseStep 7825997 = 2934749) B2934749
theorem B10021495 : Blo 948586 10021495 := bstep (se 1 (by rfl) ⟨7516121, by rfl⟩ : syracuseStep 10021495 = 15032243) B15032243
theorem B3042049 : Blo 948586 3042049 := bstep (se 2 (by rfl) ⟨1140768, by rfl⟩ : syracuseStep 3042049 = 2281537) B2281537
theorem B1174279 : Blo 948586 1174279 := bstep (se 1 (by rfl) ⟨880709, by rfl⟩ : syracuseStep 1174279 = 1761419) B1761419
theorem B10808153 : Blo 948586 10808153 := bstep (se 2 (by rfl) ⟨4053057, by rfl⟩ : syracuseStep 10808153 = 8106115) B8106115
theorem B4811723 : Blo 948586 4811723 := bstep (se 1 (by rfl) ⟨3608792, by rfl⟩ : syracuseStep 4811723 = 7217585) B7217585
theorem B11725829 : Blo 948586 11725829 := bstep (se 4 (by rfl) ⟨1099296, by rfl⟩ : syracuseStep 11725829 = 2198593) B2198593
theorem B2026615 : Blo 948586 2026615 := bstep (se 1 (by rfl) ⟨1519961, by rfl⟩ : syracuseStep 2026615 = 3039923) B3039923
theorem B4812047 : Blo 948586 4812047 := bstep (se 1 (by rfl) ⟨3609035, by rfl⟩ : syracuseStep 4812047 = 7218071) B7218071
theorem B2026795 : Blo 948586 2026795 := bstep (se 1 (by rfl) ⟨1520096, by rfl⟩ : syracuseStep 2026795 = 3040193) B3040193
theorem B2026871 : Blo 948586 2026871 := bstep (se 1 (by rfl) ⟨1520153, by rfl⟩ : syracuseStep 2026871 = 3040307) B3040307
theorem B4124051 : Blo 948586 4124051 := bstep (se 1 (by rfl) ⟨3093038, by rfl⟩ : syracuseStep 4124051 = 6186077) B6186077
theorem B1601039 : Blo 948586 1601039 := bstep (se 1 (by rfl) ⟨1200779, by rfl⟩ : syracuseStep 1601039 = 2401559) B2401559
theorem B3207059 : Blo 948586 3207059 := bstep (se 1 (by rfl) ⟨2405294, by rfl⟩ : syracuseStep 3207059 = 4810589) B4810589
theorem B1601579 : Blo 948586 1601579 := bstep (se 1 (by rfl) ⟨1201184, by rfl⟩ : syracuseStep 1601579 = 2402369) B2402369
theorem B1601977 : Blo 948586 1601977 := bstep (se 2 (by rfl) ⟨600741, by rfl⟩ : syracuseStep 1601977 = 1201483) B1201483
theorem B16249409 : Blo 948586 16249409 := bstep (se 2 (by rfl) ⟨6093528, by rfl⟩ : syracuseStep 16249409 = 12187057) B12187057
theorem B4813505 : Blo 948586 4813505 := bstep (se 2 (by rfl) ⟨1805064, by rfl⟩ : syracuseStep 4813505 = 3610129) B3610129
theorem B6091787 : Blo 948586 6091787 := bstep (se 1 (by rfl) ⟨4568840, by rfl⟩ : syracuseStep 6091787 = 9137681) B9137681
theorem B3044395 : Blo 948586 3044395 := bstep (se 1 (by rfl) ⟨2283296, by rfl⟩ : syracuseStep 3044395 = 4566593) B4566593
theorem B1602679 : Blo 948586 1602679 := bstep (se 1 (by rfl) ⟨1202009, by rfl⟩ : syracuseStep 1602679 = 2404019) B2404019
theorem B3208463 : Blo 948586 3208463 := bstep (se 1 (by rfl) ⟨2406347, by rfl⟩ : syracuseStep 3208463 = 4812695) B4812695
theorem B5403941 : Blo 948586 5403941 := bstep (se 4 (by rfl) ⟨506619, by rfl⟩ : syracuseStep 5403941 = 1013239) B1013239
theorem B1602875 : Blo 948586 1602875 := bstep (se 1 (by rfl) ⟨1202156, by rfl⟩ : syracuseStep 1602875 = 2404313) B2404313
theorem B4060475 : Blo 948586 4060475 := bstep (se 1 (by rfl) ⟨3045356, by rfl⟩ : syracuseStep 4060475 = 6090713) B6090713
theorem B41186677 : Blo 948586 41186677 := bstep (se 5 (by rfl) ⟨1930625, by rfl⟩ : syracuseStep 41186677 = 3861251) B3861251
theorem B3208733 : Blo 948586 3208733 := bstep (se 3 (by rfl) ⟨601637, by rfl⟩ : syracuseStep 3208733 = 1203275) B1203275
theorem B1603273 : Blo 948586 1603273 := bstep (se 2 (by rfl) ⟨601227, by rfl⟩ : syracuseStep 1603273 = 1202455) B1202455
theorem B126613313 : Blo 948586 126613313 := bstep (se 2 (by rfl) ⟨47479992, by rfl⟩ : syracuseStep 126613313 = 94959985) B94959985
theorem B4814801 : Blo 948586 4814801 := bstep (se 2 (by rfl) ⟨1805550, by rfl⟩ : syracuseStep 4814801 = 3611101) B3611101
theorem B6944779 : Blo 948586 6944779 := bstep (se 1 (by rfl) ⟨5208584, by rfl⟩ : syracuseStep 6944779 = 10417169) B10417169
theorem B5404715 : Blo 948586 5404715 := bstep (se 1 (by rfl) ⟨4053536, by rfl⟩ : syracuseStep 5404715 = 8107073) B8107073
theorem B5142799 : Blo 948586 5142799 := bstep (se 1 (by rfl) ⟨3857099, by rfl⟩ : syracuseStep 5142799 = 7714199) B7714199
theorem B948615 : Blo 948586 948615 := bstep (se 1 (by rfl) ⟨711461, by rfl⟩ : syracuseStep 948615 = 1422923) B1422923
theorem B1603975 : Blo 948586 1603975 := bstep (se 1 (by rfl) ⟨1202981, by rfl⟩ : syracuseStep 1603975 = 2405963) B2405963
theorem B948623 : Blo 948586 948623 := bstep (se 1 (by rfl) ⟨711467, by rfl⟩ : syracuseStep 948623 = 1422935) B1422935
theorem B948667 : Blo 948586 948667 := bstep (se 1 (by rfl) ⟨711500, by rfl⟩ : syracuseStep 948667 = 1423001) B1423001
theorem B948743 : Blo 948586 948743 := bstep (se 1 (by rfl) ⟨711557, by rfl⟩ : syracuseStep 948743 = 1423115) B1423115
theorem B948751 : Blo 948586 948751 := bstep (se 1 (by rfl) ⟨711563, by rfl⟩ : syracuseStep 948751 = 1423127) B1423127
theorem B948795 : Blo 948586 948795 := bstep (se 1 (by rfl) ⟨711596, by rfl⟩ : syracuseStep 948795 = 1423193) B1423193
theorem B948871 : Blo 948586 948871 := bstep (se 1 (by rfl) ⟨711653, by rfl⟩ : syracuseStep 948871 = 1423307) B1423307
theorem B948879 : Blo 948586 948879 := bstep (se 1 (by rfl) ⟨711659, by rfl⟩ : syracuseStep 948879 = 1423319) B1423319
theorem B948923 : Blo 948586 948923 := bstep (se 1 (by rfl) ⟨711692, by rfl⟩ : syracuseStep 948923 = 1423385) B1423385
theorem B948999 : Blo 948586 948999 := bstep (se 1 (by rfl) ⟨711749, by rfl⟩ : syracuseStep 948999 = 1423499) B1423499
theorem B949007 : Blo 948586 949007 := bstep (se 1 (by rfl) ⟨711755, by rfl⟩ : syracuseStep 949007 = 1423511) B1423511
theorem B949051 : Blo 948586 949051 := bstep (se 1 (by rfl) ⟨711788, by rfl⟩ : syracuseStep 949051 = 1423577) B1423577
theorem B949127 : Blo 948586 949127 := bstep (se 1 (by rfl) ⟨711845, by rfl⟩ : syracuseStep 949127 = 1423691) B1423691
theorem B949135 : Blo 948586 949135 := bstep (se 1 (by rfl) ⟨711851, by rfl⟩ : syracuseStep 949135 = 1423703) B1423703
theorem B3210137 : Blo 948586 3210137 := bstep (se 2 (by rfl) ⟨1203801, by rfl⟩ : syracuseStep 3210137 = 2407603) B2407603
theorem B949179 : Blo 948586 949179 := bstep (se 1 (by rfl) ⟨711884, by rfl⟩ : syracuseStep 949179 = 1423769) B1423769
theorem B18250757 : Blo 948586 18250757 := bstep (se 4 (by rfl) ⟨1711008, by rfl⟩ : syracuseStep 18250757 = 3422017) B3422017
theorem B949255 : Blo 948586 949255 := bstep (se 1 (by rfl) ⟨711941, by rfl⟩ : syracuseStep 949255 = 1423883) B1423883
theorem B949263 : Blo 948586 949263 := bstep (se 1 (by rfl) ⟨711947, by rfl⟩ : syracuseStep 949263 = 1423895) B1423895
theorem B1604623 : Blo 948586 1604623 := bstep (se 1 (by rfl) ⟨1203467, by rfl⟩ : syracuseStep 1604623 = 2406935) B2406935
theorem B4062251 : Blo 948586 4062251 := bstep (se 1 (by rfl) ⟨3046688, by rfl⟩ : syracuseStep 4062251 = 6093377) B6093377
theorem B949307 : Blo 948586 949307 := bstep (se 1 (by rfl) ⟨711980, by rfl⟩ : syracuseStep 949307 = 1423961) B1423961
theorem B13696087 : Blo 948586 13696087 := bstep (se 1 (by rfl) ⟨10272065, by rfl⟩ : syracuseStep 13696087 = 20544131) B20544131
theorem B949383 : Blo 948586 949383 := bstep (se 1 (by rfl) ⟨712037, by rfl⟩ : syracuseStep 949383 = 1424075) B1424075
theorem B949391 : Blo 948586 949391 := bstep (se 1 (by rfl) ⟨712043, by rfl⟩ : syracuseStep 949391 = 1424087) B1424087
theorem B949435 : Blo 948586 949435 := bstep (se 1 (by rfl) ⟨712076, by rfl⟩ : syracuseStep 949435 = 1424153) B1424153
theorem B949511 : Blo 948586 949511 := bstep (se 1 (by rfl) ⟨712133, by rfl⟩ : syracuseStep 949511 = 1424267) B1424267
theorem B949519 : Blo 948586 949519 := bstep (se 1 (by rfl) ⟨712139, by rfl⟩ : syracuseStep 949519 = 1424279) B1424279
theorem B949563 : Blo 948586 949563 := bstep (se 1 (by rfl) ⟨712172, by rfl⟩ : syracuseStep 949563 = 1424345) B1424345
theorem B949639 : Blo 948586 949639 := bstep (se 1 (by rfl) ⟨712229, by rfl⟩ : syracuseStep 949639 = 1424459) B1424459
theorem B949647 : Blo 948586 949647 := bstep (se 1 (by rfl) ⟨712235, by rfl⟩ : syracuseStep 949647 = 1424471) B1424471
theorem B4881809 : Blo 948586 4881809 := bstep (se 2 (by rfl) ⟨1830678, by rfl⟩ : syracuseStep 4881809 = 3661357) B3661357
theorem B949691 : Blo 948586 949691 := bstep (se 1 (by rfl) ⟨712268, by rfl⟩ : syracuseStep 949691 = 1424537) B1424537
theorem B5406173 : Blo 948586 5406173 := bstep (se 3 (by rfl) ⟨1013657, by rfl⟩ : syracuseStep 5406173 = 2027315) B2027315
theorem B949767 : Blo 948586 949767 := bstep (se 1 (by rfl) ⟨712325, by rfl⟩ : syracuseStep 949767 = 1424651) B1424651
theorem B949775 : Blo 948586 949775 := bstep (se 1 (by rfl) ⟨712331, by rfl⟩ : syracuseStep 949775 = 1424663) B1424663
theorem B1605163 : Blo 948586 1605163 := bstep (se 1 (by rfl) ⟨1203872, by rfl⟩ : syracuseStep 1605163 = 2407745) B2407745
theorem B949819 : Blo 948586 949819 := bstep (se 1 (by rfl) ⟨712364, by rfl⟩ : syracuseStep 949819 = 1424729) B1424729
theorem B3210839 : Blo 948586 3210839 := bstep (se 1 (by rfl) ⟨2408129, by rfl⟩ : syracuseStep 3210839 = 4816259) B4816259
theorem B949895 : Blo 948586 949895 := bstep (se 1 (by rfl) ⟨712421, by rfl⟩ : syracuseStep 949895 = 1424843) B1424843
theorem B949903 : Blo 948586 949903 := bstep (se 1 (by rfl) ⟨712427, by rfl⟩ : syracuseStep 949903 = 1424855) B1424855
theorem B1605305 : Blo 948586 1605305 := bstep (se 2 (by rfl) ⟨601989, by rfl⟩ : syracuseStep 1605305 = 1203979) B1203979
theorem B949947 : Blo 948586 949947 := bstep (se 1 (by rfl) ⟨712460, by rfl⟩ : syracuseStep 949947 = 1424921) B1424921
theorem B950023 : Blo 948586 950023 := bstep (se 1 (by rfl) ⟨712517, by rfl⟩ : syracuseStep 950023 = 1425035) B1425035
theorem B950031 : Blo 948586 950031 := bstep (se 1 (by rfl) ⟨712523, by rfl⟩ : syracuseStep 950031 = 1425047) B1425047
theorem B1802027 : Blo 948586 1802027 := bstep (se 1 (by rfl) ⟨1351520, by rfl⟩ : syracuseStep 1802027 = 2703041) B2703041
theorem B3604283 : Blo 948586 3604283 := bstep (se 1 (by rfl) ⟨2703212, by rfl⟩ : syracuseStep 3604283 = 5406425) B5406425
theorem B950075 : Blo 948586 950075 := bstep (se 1 (by rfl) ⟨712556, by rfl⟩ : syracuseStep 950075 = 1425113) B1425113
theorem B950151 : Blo 948586 950151 := bstep (se 1 (by rfl) ⟨712613, by rfl⟩ : syracuseStep 950151 = 1425227) B1425227
theorem B1015687 : Blo 948586 1015687 := bstep (se 1 (by rfl) ⟨761765, by rfl⟩ : syracuseStep 1015687 = 1523531) B1523531
theorem B950159 : Blo 948586 950159 := bstep (se 1 (by rfl) ⟨712619, by rfl⟩ : syracuseStep 950159 = 1425239) B1425239
theorem B950203 : Blo 948586 950203 := bstep (se 1 (by rfl) ⟨712652, by rfl⟩ : syracuseStep 950203 = 1425305) B1425305
theorem B3211271 : Blo 948586 3211271 := bstep (se 1 (by rfl) ⟨2408453, by rfl⟩ : syracuseStep 3211271 = 4816907) B4816907
theorem B950311 : Blo 948586 950311 := bstep (se 1 (by rfl) ⟨712733, by rfl⟩ : syracuseStep 950311 = 1425467) B1425467
theorem B950351 : Blo 948586 950351 := bstep (se 1 (by rfl) ⟨712763, by rfl⟩ : syracuseStep 950351 = 1425527) B1425527
theorem B950367 : Blo 948586 950367 := bstep (se 1 (by rfl) ⟨712775, by rfl⟩ : syracuseStep 950367 = 1425551) B1425551
theorem B3211379 : Blo 948586 3211379 := bstep (se 1 (by rfl) ⟨2408534, by rfl⟩ : syracuseStep 3211379 = 4817069) B4817069
theorem B950395 : Blo 948586 950395 := bstep (se 1 (by rfl) ⟨712796, by rfl⟩ : syracuseStep 950395 = 1425593) B1425593
theorem B950447 : Blo 948586 950447 := bstep (se 1 (by rfl) ⟨712835, by rfl⟩ : syracuseStep 950447 = 1425671) B1425671
theorem B950471 : Blo 948586 950471 := bstep (se 1 (by rfl) ⟨712853, by rfl⟩ : syracuseStep 950471 = 1425707) B1425707
theorem B950491 : Blo 948586 950491 := bstep (se 1 (by rfl) ⟨712868, by rfl⟩ : syracuseStep 950491 = 1425737) B1425737
theorem B950567 : Blo 948586 950567 := bstep (se 1 (by rfl) ⟨712925, by rfl⟩ : syracuseStep 950567 = 1425851) B1425851
theorem B950607 : Blo 948586 950607 := bstep (se 1 (by rfl) ⟨712955, by rfl⟩ : syracuseStep 950607 = 1425911) B1425911
theorem B950623 : Blo 948586 950623 := bstep (se 1 (by rfl) ⟨712967, by rfl⟩ : syracuseStep 950623 = 1425935) B1425935
theorem B950651 : Blo 948586 950651 := bstep (se 1 (by rfl) ⟨712988, by rfl⟩ : syracuseStep 950651 = 1425977) B1425977
theorem B3211649 : Blo 948586 3211649 := bstep (se 2 (by rfl) ⟨1204368, by rfl⟩ : syracuseStep 3211649 = 2408737) B2408737
theorem B950703 : Blo 948586 950703 := bstep (se 1 (by rfl) ⟨713027, by rfl⟩ : syracuseStep 950703 = 1426055) B1426055
theorem B950727 : Blo 948586 950727 := bstep (se 1 (by rfl) ⟨713045, by rfl⟩ : syracuseStep 950727 = 1426091) B1426091
theorem B3047881 : Blo 948586 3047881 := bstep (se 2 (by rfl) ⟨1142955, by rfl⟩ : syracuseStep 3047881 = 2285911) B2285911
theorem B950747 : Blo 948586 950747 := bstep (se 1 (by rfl) ⟨713060, by rfl⟩ : syracuseStep 950747 = 1426121) B1426121
theorem B22282775 : Blo 948586 22282775 := bstep (se 1 (by rfl) ⟨16712081, by rfl⟩ : syracuseStep 22282775 = 33424163) B33424163
theorem B950823 : Blo 948586 950823 := bstep (se 1 (by rfl) ⟨713117, by rfl⟩ : syracuseStep 950823 = 1426235) B1426235
theorem B950863 : Blo 948586 950863 := bstep (se 1 (by rfl) ⟨713147, by rfl⟩ : syracuseStep 950863 = 1426295) B1426295
theorem B1606223 : Blo 948586 1606223 := bstep (se 1 (by rfl) ⟨1204667, by rfl⟩ : syracuseStep 1606223 = 2409335) B2409335
theorem B950879 : Blo 948586 950879 := bstep (se 1 (by rfl) ⟨713159, by rfl⟩ : syracuseStep 950879 = 1426319) B1426319
theorem B950907 : Blo 948586 950907 := bstep (se 1 (by rfl) ⟨713180, by rfl⟩ : syracuseStep 950907 = 1426361) B1426361
theorem B950959 : Blo 948586 950959 := bstep (se 1 (by rfl) ⟨713219, by rfl⟩ : syracuseStep 950959 = 1426439) B1426439
theorem B950983 : Blo 948586 950983 := bstep (se 1 (by rfl) ⟨713237, by rfl⟩ : syracuseStep 950983 = 1426475) B1426475
theorem B951003 : Blo 948586 951003 := bstep (se 1 (by rfl) ⟨713252, by rfl⟩ : syracuseStep 951003 = 1426505) B1426505
theorem B1802999 : Blo 948586 1802999 := bstep (se 1 (by rfl) ⟨1352249, by rfl⟩ : syracuseStep 1802999 = 2704499) B2704499
theorem B21988097 : Blo 948586 21988097 := bstep (se 2 (by rfl) ⟨8245536, by rfl⟩ : syracuseStep 21988097 = 16491073) B16491073
theorem B951079 : Blo 948586 951079 := bstep (se 1 (by rfl) ⟨713309, by rfl⟩ : syracuseStep 951079 = 1426619) B1426619
theorem B951119 : Blo 948586 951119 := bstep (se 1 (by rfl) ⟨713339, by rfl⟩ : syracuseStep 951119 = 1426679) B1426679
theorem B951135 : Blo 948586 951135 := bstep (se 1 (by rfl) ⟨713351, by rfl⟩ : syracuseStep 951135 = 1426703) B1426703
theorem B951163 : Blo 948586 951163 := bstep (se 1 (by rfl) ⟨713372, by rfl⟩ : syracuseStep 951163 = 1426745) B1426745
theorem B1803151 : Blo 948586 1803151 := bstep (se 1 (by rfl) ⟨1352363, by rfl⟩ : syracuseStep 1803151 = 2704727) B2704727
theorem B951215 : Blo 948586 951215 := bstep (se 1 (by rfl) ⟨713411, by rfl⟩ : syracuseStep 951215 = 1426823) B1426823
theorem B951239 : Blo 948586 951239 := bstep (se 1 (by rfl) ⟨713429, by rfl⟩ : syracuseStep 951239 = 1426859) B1426859
theorem B951259 : Blo 948586 951259 := bstep (se 1 (by rfl) ⟨713444, by rfl⟩ : syracuseStep 951259 = 1426889) B1426889
theorem B6095837 : Blo 948586 6095837 := bstep (se 3 (by rfl) ⟨1142969, by rfl⟩ : syracuseStep 6095837 = 2285939) B2285939
theorem B951335 : Blo 948586 951335 := bstep (se 1 (by rfl) ⟨713501, by rfl⟩ : syracuseStep 951335 = 1427003) B1427003
theorem B15598657 : Blo 948586 15598657 := bstep (se 2 (by rfl) ⟨5849496, by rfl⟩ : syracuseStep 15598657 = 11698993) B11698993
theorem B951375 : Blo 948586 951375 := bstep (se 1 (by rfl) ⟨713531, by rfl⟩ : syracuseStep 951375 = 1427063) B1427063
theorem B951391 : Blo 948586 951391 := bstep (se 1 (by rfl) ⟨713543, by rfl⟩ : syracuseStep 951391 = 1427087) B1427087
theorem B951419 : Blo 948586 951419 := bstep (se 1 (by rfl) ⟨713564, by rfl⟩ : syracuseStep 951419 = 1427129) B1427129
theorem B3212459 : Blo 948586 3212459 := bstep (se 1 (by rfl) ⟨2409344, by rfl⟩ : syracuseStep 3212459 = 4818689) B4818689
theorem B951471 : Blo 948586 951471 := bstep (se 1 (by rfl) ⟨713603, by rfl⟩ : syracuseStep 951471 = 1427207) B1427207
theorem B951495 : Blo 948586 951495 := bstep (se 1 (by rfl) ⟨713621, by rfl⟩ : syracuseStep 951495 = 1427243) B1427243
theorem B951515 : Blo 948586 951515 := bstep (se 1 (by rfl) ⟨713636, by rfl⟩ : syracuseStep 951515 = 1427273) B1427273
theorem B951591 : Blo 948586 951591 := bstep (se 1 (by rfl) ⟨713693, by rfl⟩ : syracuseStep 951591 = 1427387) B1427387
theorem B951631 : Blo 948586 951631 := bstep (se 1 (by rfl) ⟨713723, by rfl⟩ : syracuseStep 951631 = 1427447) B1427447
theorem B951647 : Blo 948586 951647 := bstep (se 1 (by rfl) ⟨713735, by rfl⟩ : syracuseStep 951647 = 1427471) B1427471
theorem B951675 : Blo 948586 951675 := bstep (se 1 (by rfl) ⟨713756, by rfl⟩ : syracuseStep 951675 = 1427513) B1427513
theorem B6849917 : Blo 948586 6849917 := bstep (se 3 (by rfl) ⟨1284359, by rfl⟩ : syracuseStep 6849917 = 2568719) B2568719
theorem B2033039 : Blo 948586 2033039 := bstep (se 1 (by rfl) ⟨1524779, by rfl⟩ : syracuseStep 2033039 = 3049559) B3049559
theorem B951727 : Blo 948586 951727 := bstep (se 1 (by rfl) ⟨713795, by rfl⟩ : syracuseStep 951727 = 1427591) B1427591
theorem B1607087 : Blo 948586 1607087 := bstep (se 1 (by rfl) ⟨1205315, by rfl⟩ : syracuseStep 1607087 = 2410631) B2410631
theorem B951751 : Blo 948586 951751 := bstep (se 1 (by rfl) ⟨713813, by rfl⟩ : syracuseStep 951751 = 1427627) B1427627
theorem B951771 : Blo 948586 951771 := bstep (se 1 (by rfl) ⟨713828, by rfl⟩ : syracuseStep 951771 = 1427657) B1427657
theorem B951847 : Blo 948586 951847 := bstep (se 1 (by rfl) ⟨713885, by rfl⟩ : syracuseStep 951847 = 1427771) B1427771
theorem B951887 : Blo 948586 951887 := bstep (se 1 (by rfl) ⟨713915, by rfl⟩ : syracuseStep 951887 = 1427831) B1427831
theorem B951903 : Blo 948586 951903 := bstep (se 1 (by rfl) ⟨713927, by rfl⟩ : syracuseStep 951903 = 1427855) B1427855
theorem B951931 : Blo 948586 951931 := bstep (se 1 (by rfl) ⟨713948, by rfl⟩ : syracuseStep 951931 = 1427897) B1427897
theorem B5146259 : Blo 948586 5146259 := bstep (se 1 (by rfl) ⟨3859694, by rfl⟩ : syracuseStep 5146259 = 7719389) B7719389
theorem B951983 : Blo 948586 951983 := bstep (se 1 (by rfl) ⟨713987, by rfl⟩ : syracuseStep 951983 = 1427975) B1427975
theorem B3212999 : Blo 948586 3212999 := bstep (se 1 (by rfl) ⟨2409749, by rfl⟩ : syracuseStep 3212999 = 4819499) B4819499
theorem B952007 : Blo 948586 952007 := bstep (se 1 (by rfl) ⟨714005, by rfl⟩ : syracuseStep 952007 = 1428011) B1428011
theorem B3606227 : Blo 948586 3606227 := bstep (se 1 (by rfl) ⟨2704670, by rfl⟩ : syracuseStep 3606227 = 5409341) B5409341
theorem B952027 : Blo 948586 952027 := bstep (se 1 (by rfl) ⟨714020, by rfl⟩ : syracuseStep 952027 = 1428041) B1428041
theorem B1804025 : Blo 948586 1804025 := bstep (se 2 (by rfl) ⟨676509, by rfl⟩ : syracuseStep 1804025 = 1353019) B1353019
theorem B952103 : Blo 948586 952103 := bstep (se 1 (by rfl) ⟨714077, by rfl⟩ : syracuseStep 952103 = 1428155) B1428155
theorem B952143 : Blo 948586 952143 := bstep (se 1 (by rfl) ⟨714107, by rfl⟩ : syracuseStep 952143 = 1428215) B1428215
theorem B952159 : Blo 948586 952159 := bstep (se 1 (by rfl) ⟨714119, by rfl⟩ : syracuseStep 952159 = 1428239) B1428239
theorem B952187 : Blo 948586 952187 := bstep (se 1 (by rfl) ⟨714140, by rfl⟩ : syracuseStep 952187 = 1428281) B1428281
theorem B1804207 : Blo 948586 1804207 := bstep (se 1 (by rfl) ⟨1353155, by rfl⟩ : syracuseStep 1804207 = 2706311) B2706311
theorem B952239 : Blo 948586 952239 := bstep (se 1 (by rfl) ⟨714179, by rfl⟩ : syracuseStep 952239 = 1428359) B1428359
theorem B952263 : Blo 948586 952263 := bstep (se 1 (by rfl) ⟨714197, by rfl⟩ : syracuseStep 952263 = 1428395) B1428395
theorem B952283 : Blo 948586 952283 := bstep (se 1 (by rfl) ⟨714212, by rfl⟩ : syracuseStep 952283 = 1428425) B1428425
theorem B952359 : Blo 948586 952359 := bstep (se 1 (by rfl) ⟨714269, by rfl⟩ : syracuseStep 952359 = 1428539) B1428539
theorem B952399 : Blo 948586 952399 := bstep (se 1 (by rfl) ⟨714299, by rfl⟩ : syracuseStep 952399 = 1428599) B1428599
theorem B952415 : Blo 948586 952415 := bstep (se 1 (by rfl) ⟨714311, by rfl⟩ : syracuseStep 952415 = 1428623) B1428623
theorem B952443 : Blo 948586 952443 := bstep (se 1 (by rfl) ⟨714332, by rfl⟩ : syracuseStep 952443 = 1428665) B1428665
theorem B952495 : Blo 948586 952495 := bstep (se 1 (by rfl) ⟨714371, by rfl⟩ : syracuseStep 952495 = 1428743) B1428743
theorem B952519 : Blo 948586 952519 := bstep (se 1 (by rfl) ⟨714389, by rfl⟩ : syracuseStep 952519 = 1428779) B1428779
theorem B952539 : Blo 948586 952539 := bstep (se 1 (by rfl) ⟨714404, by rfl⟩ : syracuseStep 952539 = 1428809) B1428809
theorem B3213863 : Blo 948586 3213863 := bstep (se 1 (by rfl) ⟨2410397, by rfl⟩ : syracuseStep 3213863 = 4820795) B4820795
theorem B3213971 : Blo 948586 3213971 := bstep (se 1 (by rfl) ⟨2410478, by rfl⟩ : syracuseStep 3213971 = 4820957) B4820957
theorem B3214187 : Blo 948586 3214187 := bstep (se 1 (by rfl) ⟨2410640, by rfl⟩ : syracuseStep 3214187 = 4821281) B4821281
theorem B3214241 : Blo 948586 3214241 := bstep (se 2 (by rfl) ⟨1205340, by rfl⟩ : syracuseStep 3214241 = 2410681) B2410681
theorem B1805483 : Blo 948586 1805483 := bstep (se 1 (by rfl) ⟨1354112, by rfl⟩ : syracuseStep 1805483 = 2708225) B2708225
theorem B5147819 : Blo 948586 5147819 := bstep (se 1 (by rfl) ⟨3860864, by rfl⟩ : syracuseStep 5147819 = 7721729) B7721729
theorem B8228087 : Blo 948586 8228087 := bstep (se 1 (by rfl) ⟨6171065, by rfl⟩ : syracuseStep 8228087 = 12342131) B12342131
theorem B11570521 : Blo 948586 11570521 := bstep (se 2 (by rfl) ⟨4338945, by rfl⟩ : syracuseStep 11570521 = 8677891) B8677891
theorem B3214835 : Blo 948586 3214835 := bstep (se 1 (by rfl) ⟨2411126, by rfl⟩ : syracuseStep 3214835 = 4822253) B4822253
theorem B3608657 : Blo 948586 3608657 := bstep (se 2 (by rfl) ⟨1353246, by rfl⟩ : syracuseStep 3608657 = 2706493) B2706493
theorem B11538611 : Blo 948586 11538611 := bstep (se 1 (by rfl) ⟨8653958, by rfl⟩ : syracuseStep 11538611 = 17307917) B17307917
theorem B9146753 : Blo 948586 9146753 := bstep (se 2 (by rfl) ⟨3430032, by rfl⟩ : syracuseStep 9146753 = 6860065) B6860065
theorem B3608975 : Blo 948586 3608975 := bstep (se 1 (by rfl) ⟨2706731, by rfl⟩ : syracuseStep 3608975 = 5413463) B5413463
theorem B1806857 : Blo 948586 1806857 := bstep (se 2 (by rfl) ⟨677571, by rfl⟩ : syracuseStep 1806857 = 1355143) B1355143
theorem B6165017 : Blo 948586 6165017 := bstep (se 2 (by rfl) ⟨2311881, by rfl⟩ : syracuseStep 6165017 = 4623763) B4623763
theorem B1806887 : Blo 948586 1806887 := bstep (se 1 (by rfl) ⟨1355165, by rfl⟩ : syracuseStep 1806887 = 2710331) B2710331
theorem B2134727 : Blo 948586 2134727 := bstep (se 1 (by rfl) ⟨1601045, by rfl⟩ : syracuseStep 2134727 = 3202091) B3202091
theorem B1282759 : Blo 948586 1282759 := bstep (se 1 (by rfl) ⟨962069, by rfl⟩ : syracuseStep 1282759 = 1924139) B1924139
theorem B6099785 : Blo 948586 6099785 := bstep (se 2 (by rfl) ⟨2287419, by rfl⟩ : syracuseStep 6099785 = 4574839) B4574839
theorem B2888543 : Blo 948586 2888543 := bstep (se 1 (by rfl) ⟨2166407, by rfl⟩ : syracuseStep 2888543 = 4332815) B4332815
theorem B3085427 : Blo 948586 3085427 := bstep (se 1 (by rfl) ⟨2314070, by rfl⟩ : syracuseStep 3085427 = 4628141) B4628141
theorem B1807571 : Blo 948586 1807571 := bstep (se 1 (by rfl) ⟨1355678, by rfl⟩ : syracuseStep 1807571 = 2711357) B2711357
theorem B1807609 : Blo 948586 1807609 := bstep (se 2 (by rfl) ⟨677853, by rfl⟩ : syracuseStep 1807609 = 1355707) B1355707
theorem B13899023 : Blo 948586 13899023 := bstep (se 1 (by rfl) ⟨10424267, by rfl⟩ : syracuseStep 13899023 = 20848535) B20848535
theorem B3609917 : Blo 948586 3609917 := bstep (se 3 (by rfl) ⟨676859, by rfl⟩ : syracuseStep 3609917 = 1353719) B1353719
theorem B3249533 : Blo 948586 3249533 := bstep (se 3 (by rfl) ⟨609287, by rfl⟩ : syracuseStep 3249533 = 1218575) B1218575
theorem B4822415 : Blo 948586 4822415 := bstep (se 1 (by rfl) ⟨3616811, by rfl⟩ : syracuseStep 4822415 = 7233623) B7233623
theorem B29234677 : Blo 948586 29234677 := bstep (se 5 (by rfl) ⟨1370375, by rfl⟩ : syracuseStep 29234677 = 2740751) B2740751
theorem B2135591 : Blo 948586 2135591 := bstep (se 1 (by rfl) ⟨1601693, by rfl⟩ : syracuseStep 2135591 = 3203387) B3203387
theorem B2135915 : Blo 948586 2135915 := bstep (se 1 (by rfl) ⟨1601936, by rfl⟩ : syracuseStep 2135915 = 3203873) B3203873
theorem B2135969 : Blo 948586 2135969 := bstep (se 2 (by rfl) ⟨800988, by rfl⟩ : syracuseStep 2135969 = 1601977) B1601977
theorem B1808315 : Blo 948586 1808315 := bstep (se 1 (by rfl) ⟨1356236, by rfl⟩ : syracuseStep 1808315 = 2712473) B2712473
theorem B50141425 : Blo 948586 50141425 := bstep (se 2 (by rfl) ⟨18803034, by rfl⟩ : syracuseStep 50141425 = 37606069) B37606069
theorem B2136311 : Blo 948586 2136311 := bstep (se 1 (by rfl) ⟨1602233, by rfl⟩ : syracuseStep 2136311 = 3204467) B3204467
theorem B7215641 : Blo 948586 7215641 := bstep (se 2 (by rfl) ⟨2705865, by rfl⟩ : syracuseStep 7215641 = 5411731) B5411731
theorem B8460935 : Blo 948586 8460935 := bstep (se 1 (by rfl) ⟨6345701, by rfl⟩ : syracuseStep 8460935 = 12691403) B12691403
theorem B9149213 : Blo 948586 9149213 := bstep (se 3 (by rfl) ⟨1715477, by rfl⟩ : syracuseStep 9149213 = 3430955) B3430955
theorem B2136905 : Blo 948586 2136905 := bstep (se 2 (by rfl) ⟨801339, by rfl⟩ : syracuseStep 2136905 = 1602679) B1602679
theorem B1350695 : Blo 948586 1350695 := bstep (se 1 (by rfl) ⟨1013021, by rfl⟩ : syracuseStep 1350695 = 2026043) B2026043
theorem B5217331 : Blo 948586 5217331 := bstep (se 1 (by rfl) ⟨3912998, by rfl⟩ : syracuseStep 5217331 = 7825997) B7825997
theorem B1351247 : Blo 948586 1351247 := bstep (se 1 (by rfl) ⟨1013435, by rfl⟩ : syracuseStep 1351247 = 2026871) B2026871
theorem B2137697 : Blo 948586 2137697 := bstep (se 2 (by rfl) ⟨801636, by rfl⟩ : syracuseStep 2137697 = 1603273) B1603273
theorem B1711787 : Blo 948586 1711787 := bstep (se 1 (by rfl) ⟨1283840, by rfl⟩ : syracuseStep 1711787 = 2567681) B2567681
theorem B5775047 : Blo 948586 5775047 := bstep (se 1 (by rfl) ⟨4331285, by rfl⟩ : syracuseStep 5775047 = 8662571) B8662571
theorem B2138039 : Blo 948586 2138039 := bstep (se 1 (by rfl) ⟨1603529, by rfl⟩ : syracuseStep 2138039 = 3207059) B3207059
theorem B1908947 : Blo 948586 1908947 := bstep (se 1 (by rfl) ⟨1431710, by rfl⟩ : syracuseStep 1908947 = 2863421) B2863421
theorem B6857065 : Blo 948586 6857065 := bstep (se 2 (by rfl) ⟨2571399, by rfl⟩ : syracuseStep 6857065 = 5142799) B5142799
theorem B2138633 : Blo 948586 2138633 := bstep (se 2 (by rfl) ⟨801987, by rfl⟩ : syracuseStep 2138633 = 1603975) B1603975
theorem B6496793 : Blo 948586 6496793 := bstep (se 2 (by rfl) ⟨2436297, by rfl⟩ : syracuseStep 6496793 = 4872595) B4872595
theorem B3613319 : Blo 948586 3613319 := bstep (se 1 (by rfl) ⟨2709989, by rfl⟩ : syracuseStep 3613319 = 5419979) B5419979
theorem B2138975 : Blo 948586 2138975 := bstep (se 1 (by rfl) ⟨1604231, by rfl⟩ : syracuseStep 2138975 = 3208463) B3208463
theorem B1713071 : Blo 948586 1713071 := bstep (se 1 (by rfl) ⟨1284803, by rfl⟩ : syracuseStep 1713071 = 2569607) B2569607
theorem B12166145 : Blo 948586 12166145 := bstep (se 2 (by rfl) ⟨4562304, by rfl⟩ : syracuseStep 12166145 = 9124609) B9124609
theorem B2139155 : Blo 948586 2139155 := bstep (se 1 (by rfl) ⟨1604366, by rfl⟩ : syracuseStep 2139155 = 3208733) B3208733
theorem B2139497 : Blo 948586 2139497 := bstep (se 2 (by rfl) ⟨802311, by rfl⟩ : syracuseStep 2139497 = 1604623) B1604623
theorem B7218557 : Blo 948586 7218557 := bstep (se 3 (by rfl) ⟨1353479, by rfl⟩ : syracuseStep 7218557 = 2706959) B2706959
theorem B18261449 : Blo 948586 18261449 := bstep (se 2 (by rfl) ⟨6848043, by rfl⟩ : syracuseStep 18261449 = 13696087) B13696087
theorem B2140091 : Blo 948586 2140091 := bstep (se 1 (by rfl) ⟨1605068, by rfl⟩ : syracuseStep 2140091 = 3210137) B3210137
theorem B12167171 : Blo 948586 12167171 := bstep (se 1 (by rfl) ⟨9125378, by rfl⟩ : syracuseStep 12167171 = 18250757) B18250757
theorem B2140217 : Blo 948586 2140217 := bstep (se 2 (by rfl) ⟨802581, by rfl⟩ : syracuseStep 2140217 = 1605163) B1605163
theorem B3614777 : Blo 948586 3614777 := bstep (se 2 (by rfl) ⟨1355541, by rfl⟩ : syracuseStep 3614777 = 2711083) B2711083
theorem B3254539 : Blo 948586 3254539 := bstep (se 1 (by rfl) ⟨2440904, by rfl⟩ : syracuseStep 3254539 = 4881809) B4881809
theorem B2140559 : Blo 948586 2140559 := bstep (se 1 (by rfl) ⟨1605419, by rfl⟩ : syracuseStep 2140559 = 3210839) B3210839
theorem B1354249 : Blo 948586 1354249 := bstep (se 2 (by rfl) ⟨507843, by rfl⟩ : syracuseStep 1354249 = 1015687) B1015687
theorem B2402855 : Blo 948586 2402855 := bstep (se 1 (by rfl) ⟨1802141, by rfl⟩ : syracuseStep 2402855 = 3604283) B3604283
theorem B1714859 : Blo 948586 1714859 := bstep (se 1 (by rfl) ⟨1286144, by rfl⟩ : syracuseStep 1714859 = 2572289) B2572289
theorem B2140883 : Blo 948586 2140883 := bstep (se 1 (by rfl) ⟨1605662, by rfl⟩ : syracuseStep 2140883 = 3211325) B3211325
theorem B2403179 : Blo 948586 2403179 := bstep (se 1 (by rfl) ⟨1802384, by rfl⟩ : syracuseStep 2403179 = 3604769) B3604769
theorem B87633089 : Blo 948586 87633089 := bstep (se 2 (by rfl) ⟨32862408, by rfl⟩ : syracuseStep 87633089 = 65724817) B65724817
theorem B8793335 : Blo 948586 8793335 := bstep (se 1 (by rfl) ⟨6595001, by rfl⟩ : syracuseStep 8793335 = 13190003) B13190003
theorem B2403827 : Blo 948586 2403827 := bstep (se 1 (by rfl) ⟨1802870, by rfl⟩ : syracuseStep 2403827 = 3605741) B3605741
theorem B3616265 : Blo 948586 3616265 := bstep (se 2 (by rfl) ⟨1356099, by rfl⟩ : syracuseStep 3616265 = 2712199) B2712199
theorem B2141819 : Blo 948586 2141819 := bstep (se 1 (by rfl) ⟨1606364, by rfl⟩ : syracuseStep 2141819 = 3212729) B3212729
theorem B10268299 : Blo 948586 10268299 := bstep (se 1 (by rfl) ⟨7701224, by rfl⟩ : syracuseStep 10268299 = 15402449) B15402449
theorem B2404039 : Blo 948586 2404039 := bstep (se 1 (by rfl) ⟨1803029, by rfl⟩ : syracuseStep 2404039 = 3606059) B3606059
theorem B2141945 : Blo 948586 2141945 := bstep (se 2 (by rfl) ⟨803229, by rfl⟩ : syracuseStep 2141945 = 1606459) B1606459
theorem B13676303 : Blo 948586 13676303 := bstep (se 1 (by rfl) ⟨10257227, by rfl⟩ : syracuseStep 13676303 = 20514455) B20514455
theorem B3419999 : Blo 948586 3419999 := bstep (se 1 (by rfl) ⟨2564999, by rfl⟩ : syracuseStep 3419999 = 5129999) B5129999
theorem B5484449 : Blo 948586 5484449 := bstep (se 2 (by rfl) ⟨2056668, by rfl⟩ : syracuseStep 5484449 = 4113337) B4113337
theorem B2142215 : Blo 948586 2142215 := bstep (se 1 (by rfl) ⟨1606661, by rfl⟩ : syracuseStep 2142215 = 3213323) B3213323
theorem B1355815 : Blo 948586 1355815 := bstep (se 1 (by rfl) ⟨1016861, by rfl⟩ : syracuseStep 1355815 = 2033723) B2033723
theorem B2142287 : Blo 948586 2142287 := bstep (se 1 (by rfl) ⟨1606715, by rfl⟩ : syracuseStep 2142287 = 3213431) B3213431
theorem B2142683 : Blo 948586 2142683 := bstep (se 1 (by rfl) ⟨1607012, by rfl⟩ : syracuseStep 2142683 = 3214025) B3214025
theorem B26063369 : Blo 948586 26063369 := bstep (se 2 (by rfl) ⟨9773763, by rfl⟩ : syracuseStep 26063369 = 19547527) B19547527
theorem B2404961 : Blo 948586 2404961 := bstep (se 2 (by rfl) ⟨901860, by rfl⟩ : syracuseStep 2404961 = 1803721) B1803721
theorem B13873781 : Blo 948586 13873781 := bstep (se 5 (by rfl) ⟨650333, by rfl⟩ : syracuseStep 13873781 = 1300667) B1300667
theorem B3125945 : Blo 948586 3125945 := bstep (se 2 (by rfl) ⟨1172229, by rfl⟩ : syracuseStep 3125945 = 2344459) B2344459
theorem B2143151 : Blo 948586 2143151 := bstep (se 1 (by rfl) ⟨1607363, by rfl⟩ : syracuseStep 2143151 = 3214727) B3214727
theorem B13874123 : Blo 948586 13874123 := bstep (se 1 (by rfl) ⟨10405592, by rfl⟩ : syracuseStep 13874123 = 20811185) B20811185
theorem B12531145 : Blo 948586 12531145 := bstep (se 2 (by rfl) ⟨4699179, by rfl⟩ : syracuseStep 12531145 = 9398359) B9398359
theorem B1422887 : Blo 948586 1422887 := bstep (se 1 (by rfl) ⟨1067165, by rfl⟩ : syracuseStep 1422887 = 2134331) B2134331
theorem B1422971 : Blo 948586 1422971 := bstep (se 1 (by rfl) ⟨1067228, by rfl⟩ : syracuseStep 1422971 = 2134457) B2134457
theorem B7222931 : Blo 948586 7222931 := bstep (se 1 (by rfl) ⟨5417198, by rfl⟩ : syracuseStep 7222931 = 10834397) B10834397
theorem B1423097 : Blo 948586 1423097 := bstep (se 2 (by rfl) ⟨533661, by rfl⟩ : syracuseStep 1423097 = 1067323) B1067323
theorem B1423199 : Blo 948586 1423199 := bstep (se 1 (by rfl) ⟨1067399, by rfl⟩ : syracuseStep 1423199 = 2134799) B2134799
theorem B1423211 : Blo 948586 1423211 := bstep (se 1 (by rfl) ⟨1067408, by rfl⟩ : syracuseStep 1423211 = 2134817) B2134817
theorem B2406419 : Blo 948586 2406419 := bstep (se 1 (by rfl) ⟨1804814, by rfl⟩ : syracuseStep 2406419 = 3609629) B3609629
theorem B1423439 : Blo 948586 1423439 := bstep (se 1 (by rfl) ⟨1067579, by rfl⟩ : syracuseStep 1423439 = 2135159) B2135159
theorem B1423559 : Blo 948586 1423559 := bstep (se 1 (by rfl) ⟨1067669, by rfl⟩ : syracuseStep 1423559 = 2135339) B2135339
theorem B1423721 : Blo 948586 1423721 := bstep (se 2 (by rfl) ⟨533895, by rfl⟩ : syracuseStep 1423721 = 1067791) B1067791
theorem B3651983 : Blo 948586 3651983 := bstep (se 1 (by rfl) ⟨2738987, by rfl⟩ : syracuseStep 3651983 = 5477975) B5477975
theorem B1423799 : Blo 948586 1423799 := bstep (se 1 (by rfl) ⟨1067849, by rfl⟩ : syracuseStep 1423799 = 2135699) B2135699
theorem B1423835 : Blo 948586 1423835 := bstep (se 1 (by rfl) ⟨1067876, by rfl⟩ : syracuseStep 1423835 = 2135753) B2135753
theorem B2701811 : Blo 948586 2701811 := bstep (se 1 (by rfl) ⟨2026358, by rfl⟩ : syracuseStep 2701811 = 4052717) B4052717
theorem B965159 : Blo 948586 965159 := bstep (se 1 (by rfl) ⟨723869, by rfl⟩ : syracuseStep 965159 = 1447739) B1447739
theorem B1522255 : Blo 948586 1522255 := bstep (se 1 (by rfl) ⟨1141691, by rfl⟩ : syracuseStep 1522255 = 2283383) B2283383
theorem B2702153 : Blo 948586 2702153 := bstep (se 2 (by rfl) ⟨1013307, by rfl⟩ : syracuseStep 2702153 = 2026615) B2026615
theorem B1424303 : Blo 948586 1424303 := bstep (se 1 (by rfl) ⟨1068227, by rfl⟩ : syracuseStep 1424303 = 2136455) B2136455
theorem B39500723 : Blo 948586 39500723 := bstep (se 1 (by rfl) ⟨29625542, by rfl⟩ : syracuseStep 39500723 = 59251085) B59251085
theorem B2702267 : Blo 948586 2702267 := bstep (se 1 (by rfl) ⟨2026700, by rfl⟩ : syracuseStep 2702267 = 4053401) B4053401
theorem B1424393 : Blo 948586 1424393 := bstep (se 2 (by rfl) ⟨534147, by rfl⟩ : syracuseStep 1424393 = 1068295) B1068295
theorem B1424423 : Blo 948586 1424423 := bstep (se 1 (by rfl) ⟨1068317, by rfl⟩ : syracuseStep 1424423 = 2136635) B2136635
theorem B2702393 : Blo 948586 2702393 := bstep (se 2 (by rfl) ⟨1013397, by rfl⟩ : syracuseStep 2702393 = 2026795) B2026795
theorem B1424507 : Blo 948586 1424507 := bstep (se 1 (by rfl) ⟨1068380, by rfl⟩ : syracuseStep 1424507 = 2136761) B2136761
theorem B3128473 : Blo 948586 3128473 := bstep (se 2 (by rfl) ⟨1173177, by rfl⟩ : syracuseStep 3128473 = 2346355) B2346355
theorem B4570283 : Blo 948586 4570283 := bstep (se 1 (by rfl) ⟨3427712, by rfl⟩ : syracuseStep 4570283 = 6855425) B6855425
theorem B1424633 : Blo 948586 1424633 := bstep (se 2 (by rfl) ⟨534237, by rfl⟩ : syracuseStep 1424633 = 1068475) B1068475
theorem B1424735 : Blo 948586 1424735 := bstep (se 1 (by rfl) ⟨1068551, by rfl⟩ : syracuseStep 1424735 = 2137103) B2137103
theorem B1424747 : Blo 948586 1424747 := bstep (se 1 (by rfl) ⟨1068560, by rfl⟩ : syracuseStep 1424747 = 2137121) B2137121
theorem B1424975 : Blo 948586 1424975 := bstep (se 1 (by rfl) ⟨1068731, by rfl⟩ : syracuseStep 1424975 = 2137463) B2137463
theorem B1425095 : Blo 948586 1425095 := bstep (se 1 (by rfl) ⟨1068821, by rfl⟩ : syracuseStep 1425095 = 2137643) B2137643
theorem B1425257 : Blo 948586 1425257 := bstep (se 2 (by rfl) ⟨534471, by rfl⟩ : syracuseStep 1425257 = 1068943) B1068943
theorem B1425335 : Blo 948586 1425335 := bstep (se 1 (by rfl) ⟨1069001, by rfl⟩ : syracuseStep 1425335 = 2138003) B2138003
theorem B1523639 : Blo 948586 1523639 := bstep (se 1 (by rfl) ⟨1142729, by rfl⟩ : syracuseStep 1523639 = 2285459) B2285459
theorem B1425371 : Blo 948586 1425371 := bstep (se 1 (by rfl) ⟨1069028, by rfl⟩ : syracuseStep 1425371 = 2138057) B2138057
theorem B6864911 : Blo 948586 6864911 := bstep (se 1 (by rfl) ⟨5148683, by rfl⟩ : syracuseStep 6864911 = 10297367) B10297367
theorem B4571225 : Blo 948586 4571225 := bstep (se 2 (by rfl) ⟨1714209, by rfl⟩ : syracuseStep 4571225 = 3428419) B3428419
theorem B3850355 : Blo 948586 3850355 := bstep (se 1 (by rfl) ⟨2887766, by rfl⟩ : syracuseStep 3850355 = 5775533) B5775533
theorem B1425839 : Blo 948586 1425839 := bstep (se 1 (by rfl) ⟨1069379, by rfl⟩ : syracuseStep 1425839 = 2138759) B2138759
theorem B1425929 : Blo 948586 1425929 := bstep (se 2 (by rfl) ⟨534723, by rfl⟩ : syracuseStep 1425929 = 1069447) B1069447
theorem B1425959 : Blo 948586 1425959 := bstep (se 1 (by rfl) ⟨1069469, by rfl⟩ : syracuseStep 1425959 = 2138939) B2138939
theorem B2605607 : Blo 948586 2605607 := bstep (se 1 (by rfl) ⟨1954205, by rfl⟩ : syracuseStep 2605607 = 3908411) B3908411
theorem B1426043 : Blo 948586 1426043 := bstep (se 1 (by rfl) ⟨1069532, by rfl⟩ : syracuseStep 1426043 = 2139065) B2139065
theorem B13681325 : Blo 948586 13681325 := bstep (se 3 (by rfl) ⟨2565248, by rfl⟩ : syracuseStep 13681325 = 5130497) B5130497
theorem B3425017 : Blo 948586 3425017 := bstep (se 2 (by rfl) ⟨1284381, by rfl⟩ : syracuseStep 3425017 = 2568763) B2568763
theorem B1426169 : Blo 948586 1426169 := bstep (se 2 (by rfl) ⟨534813, by rfl⟩ : syracuseStep 1426169 = 1069627) B1069627
theorem B1426271 : Blo 948586 1426271 := bstep (se 1 (by rfl) ⟨1069703, by rfl⟩ : syracuseStep 1426271 = 2139407) B2139407
theorem B1524575 : Blo 948586 1524575 := bstep (se 1 (by rfl) ⟨1143431, by rfl⟩ : syracuseStep 1524575 = 2286863) B2286863
theorem B1426283 : Blo 948586 1426283 := bstep (se 1 (by rfl) ⟨1069712, by rfl⟩ : syracuseStep 1426283 = 2139425) B2139425
theorem B1524587 : Blo 948586 1524587 := bstep (se 1 (by rfl) ⟨1143440, by rfl⟩ : syracuseStep 1524587 = 2286881) B2286881
theorem B7226333 : Blo 948586 7226333 := bstep (se 3 (by rfl) ⟨1354937, by rfl⟩ : syracuseStep 7226333 = 2709875) B2709875
theorem B2442259 : Blo 948586 2442259 := bstep (se 1 (by rfl) ⟨1831694, by rfl⟩ : syracuseStep 2442259 = 3663389) B3663389
theorem B7128107 : Blo 948586 7128107 := bstep (se 1 (by rfl) ⟨5346080, by rfl⟩ : syracuseStep 7128107 = 10692161) B10692161
theorem B1426511 : Blo 948586 1426511 := bstep (se 1 (by rfl) ⟨1069883, by rfl⟩ : syracuseStep 1426511 = 2139767) B2139767
theorem B1426631 : Blo 948586 1426631 := bstep (se 1 (by rfl) ⟨1069973, by rfl⟩ : syracuseStep 1426631 = 2139947) B2139947
theorem B1426793 : Blo 948586 1426793 := bstep (se 2 (by rfl) ⟨535047, by rfl⟩ : syracuseStep 1426793 = 1070095) B1070095
theorem B2409871 : Blo 948586 2409871 := bstep (se 1 (by rfl) ⟨1807403, by rfl⟩ : syracuseStep 2409871 = 3614807) B3614807
theorem B1426871 : Blo 948586 1426871 := bstep (se 1 (by rfl) ⟨1070153, by rfl⟩ : syracuseStep 1426871 = 2140307) B2140307
theorem B1426907 : Blo 948586 1426907 := bstep (se 1 (by rfl) ⟨1070180, by rfl⟩ : syracuseStep 1426907 = 2140361) B2140361
theorem B2705035 : Blo 948586 2705035 := bstep (se 1 (by rfl) ⟨2028776, by rfl⟩ : syracuseStep 2705035 = 4057553) B4057553
theorem B2410195 : Blo 948586 2410195 := bstep (se 1 (by rfl) ⟨1807646, by rfl⟩ : syracuseStep 2410195 = 3615293) B3615293
theorem B16893755 : Blo 948586 16893755 := bstep (se 1 (by rfl) ⟨12670316, by rfl⟩ : syracuseStep 16893755 = 25340633) B25340633
theorem B1427375 : Blo 948586 1427375 := bstep (se 1 (by rfl) ⟨1070531, by rfl⟩ : syracuseStep 1427375 = 2141063) B2141063
theorem B7817219 : Blo 948586 7817219 := bstep (se 1 (by rfl) ⟨5862914, by rfl⟩ : syracuseStep 7817219 = 11725829) B11725829
theorem B1427465 : Blo 948586 1427465 := bstep (se 2 (by rfl) ⟨535299, by rfl⟩ : syracuseStep 1427465 = 1070599) B1070599
theorem B1427495 : Blo 948586 1427495 := bstep (se 1 (by rfl) ⟨1070621, by rfl⟩ : syracuseStep 1427495 = 2141243) B2141243
theorem B1427579 : Blo 948586 1427579 := bstep (se 1 (by rfl) ⟨1070684, by rfl⟩ : syracuseStep 1427579 = 2141369) B2141369
theorem B3426457 : Blo 948586 3426457 := bstep (se 2 (by rfl) ⟨1284921, by rfl⟩ : syracuseStep 3426457 = 2569843) B2569843
theorem B1427705 : Blo 948586 1427705 := bstep (se 2 (by rfl) ⟨535389, by rfl⟩ : syracuseStep 1427705 = 1070779) B1070779
theorem B1067359 : Blo 948586 1067359 := bstep (se 1 (by rfl) ⟨800519, by rfl⟩ : syracuseStep 1067359 = 1601039) B1601039
theorem B1427807 : Blo 948586 1427807 := bstep (se 1 (by rfl) ⟨1070855, by rfl⟩ : syracuseStep 1427807 = 2141711) B2141711
theorem B1427819 : Blo 948586 1427819 := bstep (se 1 (by rfl) ⟨1070864, by rfl⟩ : syracuseStep 1427819 = 2141729) B2141729
theorem B23120417 : Blo 948586 23120417 := bstep (se 2 (by rfl) ⟨8670156, by rfl⟩ : syracuseStep 23120417 = 17340313) B17340313
theorem B1428047 : Blo 948586 1428047 := bstep (se 1 (by rfl) ⟨1071035, by rfl⟩ : syracuseStep 1428047 = 2142071) B2142071
theorem B2411147 : Blo 948586 2411147 := bstep (se 1 (by rfl) ⟨1808360, by rfl⟩ : syracuseStep 2411147 = 3616721) B3616721
theorem B9259705 : Blo 948586 9259705 := bstep (se 2 (by rfl) ⟨3472389, by rfl⟩ : syracuseStep 9259705 = 6944779) B6944779
theorem B1067719 : Blo 948586 1067719 := bstep (se 1 (by rfl) ⟨800789, by rfl⟩ : syracuseStep 1067719 = 1601579) B1601579
theorem B1428167 : Blo 948586 1428167 := bstep (se 1 (by rfl) ⟨1071125, by rfl⟩ : syracuseStep 1428167 = 2142251) B2142251
theorem B1428329 : Blo 948586 1428329 := bstep (se 2 (by rfl) ⟨535623, by rfl⟩ : syracuseStep 1428329 = 1071247) B1071247
theorem B1428407 : Blo 948586 1428407 := bstep (se 1 (by rfl) ⟨1071305, by rfl⟩ : syracuseStep 1428407 = 2142611) B2142611
theorem B1428443 : Blo 948586 1428443 := bstep (se 1 (by rfl) ⟨1071332, by rfl⟩ : syracuseStep 1428443 = 2142665) B2142665
theorem B10832939 : Blo 948586 10832939 := bstep (se 1 (by rfl) ⟨8124704, by rfl⟩ : syracuseStep 10832939 = 16249409) B16249409
theorem B5491763 : Blo 948586 5491763 := bstep (se 1 (by rfl) ⟨4118822, by rfl⟩ : syracuseStep 5491763 = 8237645) B8237645
theorem B2280923 : Blo 948586 2280923 := bstep (se 1 (by rfl) ⟨1710692, by rfl⟩ : syracuseStep 2280923 = 3421385) B3421385
theorem B1068583 : Blo 948586 1068583 := bstep (se 1 (by rfl) ⟨801437, by rfl⟩ : syracuseStep 1068583 = 1602875) B1602875
theorem B2706983 : Blo 948586 2706983 := bstep (se 1 (by rfl) ⟨2030237, by rfl⟩ : syracuseStep 2706983 = 4060475) B4060475
theorem B1953811 : Blo 948586 1953811 := bstep (se 1 (by rfl) ⟨1465358, by rfl⟩ : syracuseStep 1953811 = 2930717) B2930717
theorem B1954003 : Blo 948586 1954003 := bstep (se 1 (by rfl) ⟨1465502, by rfl⟩ : syracuseStep 1954003 = 2931005) B2931005
theorem B6082867 : Blo 948586 6082867 := bstep (se 1 (by rfl) ⟨4562150, by rfl⟩ : syracuseStep 6082867 = 9124301) B9124301
theorem B2708167 : Blo 948586 2708167 := bstep (se 1 (by rfl) ⟨2031125, by rfl⟩ : syracuseStep 2708167 = 4062251) B4062251
theorem B4805405 : Blo 948586 4805405 := bstep (se 3 (by rfl) ⟨901013, by rfl⟩ : syracuseStep 4805405 = 1802027) B1802027
theorem B2282575 : Blo 948586 2282575 := bstep (se 1 (by rfl) ⟨1711931, by rfl⟩ : syracuseStep 2282575 = 3423863) B3423863
theorem B1070203 : Blo 948586 1070203 := bstep (se 1 (by rfl) ⟨802652, by rfl⟩ : syracuseStep 1070203 = 1605305) B1605305
theorem B4052443 : Blo 948586 4052443 := bstep (se 1 (by rfl) ⟨3039332, by rfl⟩ : syracuseStep 4052443 = 6078665) B6078665
theorem B1070671 : Blo 948586 1070671 := bstep (se 1 (by rfl) ⟨803003, by rfl⟩ : syracuseStep 1070671 = 1606007) B1606007
theorem B4576913 : Blo 948586 4576913 := bstep (se 2 (by rfl) ⟨1716342, by rfl⟩ : syracuseStep 4576913 = 3432685) B3432685
theorem B2709409 : Blo 948586 2709409 := bstep (se 2 (by rfl) ⟨1016028, by rfl⟩ : syracuseStep 2709409 = 2032057) B2032057
theorem B1071067 : Blo 948586 1071067 := bstep (se 1 (by rfl) ⟨803300, by rfl⟩ : syracuseStep 1071067 = 1606601) B1606601
theorem B1464569 : Blo 948586 1464569 := bstep (se 2 (by rfl) ⟨549213, by rfl⟩ : syracuseStep 1464569 = 1098427) B1098427
theorem B1071535 : Blo 948586 1071535 := bstep (se 1 (by rfl) ⟨803651, by rfl⟩ : syracuseStep 1071535 = 1607303) B1607303
theorem B3201659 : Blo 948586 3201659 := bstep (se 1 (by rfl) ⟨2401244, by rfl⟩ : syracuseStep 3201659 = 4802489) B4802489
theorem B3201821 : Blo 948586 3201821 := bstep (se 3 (by rfl) ⟨600341, by rfl⟩ : syracuseStep 3201821 = 1200683) B1200683
theorem B2710685 : Blo 948586 2710685 := bstep (se 3 (by rfl) ⟨508253, by rfl⟩ : syracuseStep 2710685 = 1016507) B1016507
theorem B3202523 : Blo 948586 3202523 := bstep (se 1 (by rfl) ⟨2401892, by rfl⟩ : syracuseStep 3202523 = 4803785) B4803785
theorem B1695239 : Blo 948586 1695239 := bstep (se 1 (by rfl) ⟨1271429, by rfl⟩ : syracuseStep 1695239 = 2542859) B2542859
theorem B1203751 : Blo 948586 1203751 := bstep (se 1 (by rfl) ⟨902813, by rfl⟩ : syracuseStep 1203751 = 1805627) B1805627
theorem B3858043 : Blo 948586 3858043 := bstep (se 1 (by rfl) ⟨2893532, by rfl⟩ : syracuseStep 3858043 = 5787065) B5787065
theorem B4873927 : Blo 948586 4873927 := bstep (se 1 (by rfl) ⟨3655445, by rfl⟩ : syracuseStep 4873927 = 7310891) B7310891
theorem B100228913 : Blo 948586 100228913 := bstep (se 2 (by rfl) ⟨37585842, by rfl⟩ : syracuseStep 100228913 = 75171685) B75171685
theorem B1204075 : Blo 948586 1204075 := bstep (se 1 (by rfl) ⟨903056, by rfl⟩ : syracuseStep 1204075 = 1806113) B1806113
theorem B6086663 : Blo 948586 6086663 := bstep (se 1 (by rfl) ⟨4564997, by rfl⟩ : syracuseStep 6086663 = 9129995) B9129995
theorem B1925129 : Blo 948586 1925129 := bstep (se 2 (by rfl) ⟨721923, by rfl⟩ : syracuseStep 1925129 = 1443847) B1443847
theorem B29253649 : Blo 948586 29253649 := bstep (se 2 (by rfl) ⟨10970118, by rfl⟩ : syracuseStep 29253649 = 21940237) B21940237
theorem B15065149 : Blo 948586 15065149 := bstep (se 3 (by rfl) ⟨2824715, by rfl⟩ : syracuseStep 15065149 = 5649431) B5649431
theorem B1204303 : Blo 948586 1204303 := bstep (se 1 (by rfl) ⟨903227, by rfl⟩ : syracuseStep 1204303 = 1806455) B1806455
theorem B3203225 : Blo 948586 3203225 := bstep (se 2 (by rfl) ⟨1201209, by rfl⟩ : syracuseStep 3203225 = 2402419) B2402419
theorem B5137181 : Blo 948586 5137181 := bstep (se 3 (by rfl) ⟨963221, by rfl⟩ : syracuseStep 5137181 = 1926443) B1926443
theorem B13361993 : Blo 948586 13361993 := bstep (se 2 (by rfl) ⟨5010747, by rfl⟩ : syracuseStep 13361993 = 10021495) B10021495
theorem B4056065 : Blo 948586 4056065 := bstep (se 2 (by rfl) ⟨1521024, by rfl⟩ : syracuseStep 4056065 = 3042049) B3042049
theorem B1565705 : Blo 948586 1565705 := bstep (se 2 (by rfl) ⟨587139, by rfl⟩ : syracuseStep 1565705 = 1174279) B1174279
theorem B77915155 : Blo 948586 77915155 := bstep (se 1 (by rfl) ⟨58436366, by rfl⟩ : syracuseStep 77915155 = 116872733) B116872733
theorem B4809779 : Blo 948586 4809779 := bstep (se 1 (by rfl) ⟨3607334, by rfl⟩ : syracuseStep 4809779 = 7214669) B7214669
theorem B1205371 : Blo 948586 1205371 := bstep (se 1 (by rfl) ⟨904028, by rfl⟩ : syracuseStep 1205371 = 1808057) B1808057
theorem B3040409 : Blo 948586 3040409 := bstep (se 2 (by rfl) ⟨1140153, by rfl⟩ : syracuseStep 3040409 = 2280307) B2280307
theorem B3204413 : Blo 948586 3204413 := bstep (se 3 (by rfl) ⟨600827, by rfl⟩ : syracuseStep 3204413 = 1201655) B1201655
theorem B1205599 : Blo 948586 1205599 := bstep (se 1 (by rfl) ⟨904199, by rfl⟩ : syracuseStep 1205599 = 1808399) B1808399
theorem B5137829 : Blo 948586 5137829 := bstep (se 4 (by rfl) ⟨481671, by rfl⟩ : syracuseStep 5137829 = 963343) B963343
theorem B3467279 : Blo 948586 3467279 := bstep (se 1 (by rfl) ⟨2600459, by rfl⟩ : syracuseStep 3467279 = 5200919) B5200919
theorem B62580869 : Blo 948586 62580869 := bstep (se 4 (by rfl) ⟨5866956, by rfl⟩ : syracuseStep 62580869 = 11733913) B11733913
theorem B3205277 : Blo 948586 3205277 := bstep (se 3 (by rfl) ⟨600989, by rfl⟩ : syracuseStep 3205277 = 1201979) B1201979
theorem B4811399 : Blo 948586 4811399 := bstep (se 1 (by rfl) ⟨3608549, by rfl⟩ : syracuseStep 4811399 = 7217099) B7217099
theorem B3205817 : Blo 948586 3205817 := bstep (se 2 (by rfl) ⟨1202181, by rfl⟩ : syracuseStep 3205817 = 2404363) B2404363
theorem B3206411 : Blo 948586 3206411 := bstep (se 1 (by rfl) ⟨2404808, by rfl⟩ : syracuseStep 3206411 = 4809617) B4809617
theorem B1142191 : Blo 948586 1142191 := bstep (se 1 (by rfl) ⟨856643, by rfl⟩ : syracuseStep 1142191 = 1713287) B1713287
theorem B1600951 : Blo 948586 1600951 := bstep (se 1 (by rfl) ⟨1200713, by rfl⟩ : syracuseStep 1600951 = 2401427) B2401427
theorem B6090227 : Blo 948586 6090227 := bstep (se 1 (by rfl) ⟨4567670, by rfl⟩ : syracuseStep 6090227 = 9135341) B9135341
theorem B3206681 : Blo 948586 3206681 := bstep (se 2 (by rfl) ⟨1202505, by rfl⟩ : syracuseStep 3206681 = 2405011) B2405011
theorem B10841687 : Blo 948586 10841687 := bstep (se 1 (by rfl) ⟨8131265, by rfl⟩ : syracuseStep 10841687 = 16262531) B16262531
theorem B1601147 : Blo 948586 1601147 := bstep (se 1 (by rfl) ⟨1200860, by rfl⟩ : syracuseStep 1601147 = 2401721) B2401721
theorem B1928875 : Blo 948586 1928875 := bstep (se 1 (by rfl) ⟨1446656, by rfl⟩ : syracuseStep 1928875 = 2893313) B2893313
theorem B3862225 : Blo 948586 3862225 := bstep (se 2 (by rfl) ⟨1448334, by rfl⟩ : syracuseStep 3862225 = 2896669) B2896669
theorem B2780887 : Blo 948586 2780887 := bstep (se 1 (by rfl) ⟨2085665, by rfl⟩ : syracuseStep 2780887 = 4171331) B4171331
theorem B1601545 : Blo 948586 1601545 := bstep (se 2 (by rfl) ⟨600579, by rfl⟩ : syracuseStep 1601545 = 1201159) B1201159
theorem B15396875 : Blo 948586 15396875 := bstep (se 1 (by rfl) ⟨11547656, by rfl⟩ : syracuseStep 15396875 = 23095313) B23095313
theorem B4059193 : Blo 948586 4059193 := bstep (se 2 (by rfl) ⟨1522197, by rfl⟩ : syracuseStep 4059193 = 3044395) B3044395
theorem B4812857 : Blo 948586 4812857 := bstep (se 2 (by rfl) ⟨1804821, by rfl⟩ : syracuseStep 4812857 = 3609643) B3609643
theorem B1601707 : Blo 948586 1601707 := bstep (se 1 (by rfl) ⟨1201280, by rfl⟩ : syracuseStep 1601707 = 2402561) B2402561
theorem B10809611 : Blo 948586 10809611 := bstep (se 1 (by rfl) ⟨8107208, by rfl⟩ : syracuseStep 10809611 = 16214417) B16214417
theorem B1602011 : Blo 948586 1602011 := bstep (se 1 (by rfl) ⟨1201508, by rfl⟩ : syracuseStep 1602011 = 2403017) B2403017
theorem B54915569 : Blo 948586 54915569 := bstep (se 2 (by rfl) ⟨20593338, by rfl⟩ : syracuseStep 54915569 = 41186677) B41186677
theorem B7205435 : Blo 948586 7205435 := bstep (se 1 (by rfl) ⟨5404076, by rfl⟩ : syracuseStep 7205435 = 10808153) B10808153
theorem B3207815 : Blo 948586 3207815 := bstep (se 1 (by rfl) ⟨2405861, by rfl⟩ : syracuseStep 3207815 = 4811723) B4811723
theorem B3207869 : Blo 948586 3207869 := bstep (se 3 (by rfl) ⟨601475, by rfl⟩ : syracuseStep 3207869 = 1202951) B1202951
theorem B1602247 : Blo 948586 1602247 := bstep (se 1 (by rfl) ⟨1201685, by rfl⟩ : syracuseStep 1602247 = 2403371) B2403371
theorem B3208031 : Blo 948586 3208031 := bstep (se 1 (by rfl) ⟨2406023, by rfl⟩ : syracuseStep 3208031 = 4812047) B4812047
theorem B1602409 : Blo 948586 1602409 := bstep (se 2 (by rfl) ⟨600903, by rfl⟩ : syracuseStep 1602409 = 1201807) B1201807
theorem B2749367 : Blo 948586 2749367 := bstep (se 1 (by rfl) ⟨2062025, by rfl⟩ : syracuseStep 2749367 = 4124051) B4124051
theorem B3208193 : Blo 948586 3208193 := bstep (se 2 (by rfl) ⟨1203072, by rfl⟩ : syracuseStep 3208193 = 2406145) B2406145
theorem B1603003 : Blo 948586 1603003 := bstep (se 1 (by rfl) ⟨1202252, by rfl⟩ : syracuseStep 1603003 = 2404505) B2404505
theorem B1603111 : Blo 948586 1603111 := bstep (se 1 (by rfl) ⟨1202333, by rfl⟩ : syracuseStep 1603111 = 2404667) B2404667
theorem B2061863 : Blo 948586 2061863 := bstep (se 1 (by rfl) ⟨1546397, by rfl⟩ : syracuseStep 2061863 = 3092795) B3092795
theorem B3209003 : Blo 948586 3209003 := bstep (se 1 (by rfl) ⟨2406752, by rfl⟩ : syracuseStep 3209003 = 4813505) B4813505
theorem B3045215 : Blo 948586 3045215 := bstep (se 1 (by rfl) ⟨2283911, by rfl⟩ : syracuseStep 3045215 = 4567823) B4567823
theorem B1603435 : Blo 948586 1603435 := bstep (se 1 (by rfl) ⟨1202576, by rfl⟩ : syracuseStep 1603435 = 2405153) B2405153
theorem B4061191 : Blo 948586 4061191 := bstep (se 1 (by rfl) ⟨3045893, by rfl⟩ : syracuseStep 4061191 = 6091787) B6091787
theorem B3209273 : Blo 948586 3209273 := bstep (se 2 (by rfl) ⟨1203477, by rfl⟩ : syracuseStep 3209273 = 2406955) B2406955
theorem B4814963 : Blo 948586 4814963 := bstep (se 1 (by rfl) ⟨3611222, by rfl⟩ : syracuseStep 4814963 = 7222445) B7222445
theorem B3602627 : Blo 948586 3602627 := bstep (se 1 (by rfl) ⟨2701970, by rfl⟩ : syracuseStep 3602627 = 5403941) B5403941
theorem B948603 : Blo 948586 948603 := bstep (se 1 (by rfl) ⟨711452, by rfl⟩ : syracuseStep 948603 = 1422905) B1422905
theorem B3209597 : Blo 948586 3209597 := bstep (se 3 (by rfl) ⟨601799, by rfl⟩ : syracuseStep 3209597 = 1203599) B1203599
theorem B948655 : Blo 948586 948655 := bstep (se 1 (by rfl) ⟨711491, by rfl⟩ : syracuseStep 948655 = 1422983) B1422983
theorem B948679 : Blo 948586 948679 := bstep (se 1 (by rfl) ⟨711509, by rfl⟩ : syracuseStep 948679 = 1423019) B1423019
theorem B948699 : Blo 948586 948699 := bstep (se 1 (by rfl) ⟨711524, by rfl⟩ : syracuseStep 948699 = 1423049) B1423049
theorem B948775 : Blo 948586 948775 := bstep (se 1 (by rfl) ⟨711581, by rfl⟩ : syracuseStep 948775 = 1423163) B1423163
theorem B84408875 : Blo 948586 84408875 := bstep (se 1 (by rfl) ⟨63306656, by rfl⟩ : syracuseStep 84408875 = 126613313) B126613313
theorem B948815 : Blo 948586 948815 := bstep (se 1 (by rfl) ⟨711611, by rfl⟩ : syracuseStep 948815 = 1423223) B1423223
theorem B948831 : Blo 948586 948831 := bstep (se 1 (by rfl) ⟨711623, by rfl⟩ : syracuseStep 948831 = 1423247) B1423247
theorem B948859 : Blo 948586 948859 := bstep (se 1 (by rfl) ⟨711644, by rfl⟩ : syracuseStep 948859 = 1423289) B1423289
theorem B3209867 : Blo 948586 3209867 := bstep (se 1 (by rfl) ⟨2407400, by rfl⟩ : syracuseStep 3209867 = 4814801) B4814801
theorem B948911 : Blo 948586 948911 := bstep (se 1 (by rfl) ⟨711683, by rfl⟩ : syracuseStep 948911 = 1423367) B1423367
theorem B34667185 : Blo 948586 34667185 := bstep (se 2 (by rfl) ⟨13000194, by rfl⟩ : syracuseStep 34667185 = 26000389) B26000389
theorem B948935 : Blo 948586 948935 := bstep (se 1 (by rfl) ⟨711701, by rfl⟩ : syracuseStep 948935 = 1423403) B1423403
theorem B3603143 : Blo 948586 3603143 := bstep (se 1 (by rfl) ⟨2702357, by rfl⟩ : syracuseStep 3603143 = 5404715) B5404715
theorem B3046099 : Blo 948586 3046099 := bstep (se 1 (by rfl) ⟨2284574, by rfl⟩ : syracuseStep 3046099 = 4569149) B4569149
theorem B948955 : Blo 948586 948955 := bstep (se 1 (by rfl) ⟨711716, by rfl⟩ : syracuseStep 948955 = 1423433) B1423433
theorem B949031 : Blo 948586 949031 := bstep (se 1 (by rfl) ⟨711773, by rfl⟩ : syracuseStep 949031 = 1423547) B1423547
theorem B949071 : Blo 948586 949071 := bstep (se 1 (by rfl) ⟨711803, by rfl⟩ : syracuseStep 949071 = 1423607) B1423607
theorem B1801055 : Blo 948586 1801055 := bstep (se 1 (by rfl) ⟨1350791, by rfl⟩ : syracuseStep 1801055 = 2701583) B2701583
theorem B949087 : Blo 948586 949087 := bstep (se 1 (by rfl) ⟨711815, by rfl⟩ : syracuseStep 949087 = 1423631) B1423631
theorem B2784095 : Blo 948586 2784095 := bstep (se 1 (by rfl) ⟨2088071, by rfl⟩ : syracuseStep 2784095 = 4176143) B4176143
theorem B949115 : Blo 948586 949115 := bstep (se 1 (by rfl) ⟨711836, by rfl⟩ : syracuseStep 949115 = 1423673) B1423673
theorem B1604495 : Blo 948586 1604495 := bstep (se 1 (by rfl) ⟨1203371, by rfl⟩ : syracuseStep 1604495 = 2406743) B2406743
theorem B6847379 : Blo 948586 6847379 := bstep (se 1 (by rfl) ⟨5135534, by rfl⟩ : syracuseStep 6847379 = 10271069) B10271069
theorem B949167 : Blo 948586 949167 := bstep (se 1 (by rfl) ⟨711875, by rfl⟩ : syracuseStep 949167 = 1423751) B1423751
theorem B949191 : Blo 948586 949191 := bstep (se 1 (by rfl) ⟨711893, by rfl⟩ : syracuseStep 949191 = 1423787) B1423787
theorem B949211 : Blo 948586 949211 := bstep (se 1 (by rfl) ⟨711908, by rfl⟩ : syracuseStep 949211 = 1423817) B1423817
theorem B949287 : Blo 948586 949287 := bstep (se 1 (by rfl) ⟨711965, by rfl⟩ : syracuseStep 949287 = 1423931) B1423931
theorem B3046457 : Blo 948586 3046457 := bstep (se 2 (by rfl) ⟨1142421, by rfl⟩ : syracuseStep 3046457 = 2284843) B2284843
theorem B949327 : Blo 948586 949327 := bstep (se 1 (by rfl) ⟨711995, by rfl⟩ : syracuseStep 949327 = 1423991) B1423991
theorem B949343 : Blo 948586 949343 := bstep (se 1 (by rfl) ⟨712007, by rfl⟩ : syracuseStep 949343 = 1424015) B1424015
theorem B949371 : Blo 948586 949371 := bstep (se 1 (by rfl) ⟨712028, by rfl⟩ : syracuseStep 949371 = 1424057) B1424057
theorem B1604731 : Blo 948586 1604731 := bstep (se 1 (by rfl) ⟨1203548, by rfl⟩ : syracuseStep 1604731 = 2407097) B2407097
theorem B949423 : Blo 948586 949423 := bstep (se 1 (by rfl) ⟨712067, by rfl⟩ : syracuseStep 949423 = 1424135) B1424135
theorem B949447 : Blo 948586 949447 := bstep (se 1 (by rfl) ⟨712085, by rfl⟩ : syracuseStep 949447 = 1424171) B1424171
theorem B5405899 : Blo 948586 5405899 := bstep (se 1 (by rfl) ⟨4054424, by rfl⟩ : syracuseStep 5405899 = 8108849) B8108849
theorem B949467 : Blo 948586 949467 := bstep (se 1 (by rfl) ⟨712100, by rfl⟩ : syracuseStep 949467 = 1424201) B1424201
theorem B949543 : Blo 948586 949543 := bstep (se 1 (by rfl) ⟨712157, by rfl⟩ : syracuseStep 949543 = 1424315) B1424315
theorem B949583 : Blo 948586 949583 := bstep (se 1 (by rfl) ⟨712187, by rfl⟩ : syracuseStep 949583 = 1424375) B1424375
theorem B949599 : Blo 948586 949599 := bstep (se 1 (by rfl) ⟨712199, by rfl⟩ : syracuseStep 949599 = 1424399) B1424399
theorem B949627 : Blo 948586 949627 := bstep (se 1 (by rfl) ⟨712220, by rfl⟩ : syracuseStep 949627 = 1424441) B1424441
theorem B949679 : Blo 948586 949679 := bstep (se 1 (by rfl) ⟨712259, by rfl⟩ : syracuseStep 949679 = 1424519) B1424519
theorem B949703 : Blo 948586 949703 := bstep (se 1 (by rfl) ⟨712277, by rfl⟩ : syracuseStep 949703 = 1424555) B1424555
theorem B949723 : Blo 948586 949723 := bstep (se 1 (by rfl) ⟨712292, by rfl⟩ : syracuseStep 949723 = 1424585) B1424585
theorem B3210785 : Blo 948586 3210785 := bstep (se 2 (by rfl) ⟨1204044, by rfl⟩ : syracuseStep 3210785 = 2408089) B2408089
theorem B949799 : Blo 948586 949799 := bstep (se 1 (by rfl) ⟨712349, by rfl⟩ : syracuseStep 949799 = 1424699) B1424699
theorem B949839 : Blo 948586 949839 := bstep (se 1 (by rfl) ⟨712379, by rfl⟩ : syracuseStep 949839 = 1424759) B1424759
theorem B949855 : Blo 948586 949855 := bstep (se 1 (by rfl) ⟨712391, by rfl⟩ : syracuseStep 949855 = 1424783) B1424783
theorem B949883 : Blo 948586 949883 := bstep (se 1 (by rfl) ⟨712412, by rfl⟩ : syracuseStep 949883 = 1424825) B1424825
theorem B3604115 : Blo 948586 3604115 := bstep (se 1 (by rfl) ⟨2703086, by rfl⟩ : syracuseStep 3604115 = 5406173) B5406173
theorem B949935 : Blo 948586 949935 := bstep (se 1 (by rfl) ⟨712451, by rfl⟩ : syracuseStep 949935 = 1424903) B1424903
theorem B4816583 : Blo 948586 4816583 := bstep (se 1 (by rfl) ⟨3612437, by rfl⟩ : syracuseStep 4816583 = 7224875) B7224875
theorem B949959 : Blo 948586 949959 := bstep (se 1 (by rfl) ⟨712469, by rfl⟩ : syracuseStep 949959 = 1424939) B1424939
theorem B949979 : Blo 948586 949979 := bstep (se 1 (by rfl) ⟨712484, by rfl⟩ : syracuseStep 949979 = 1424969) B1424969
theorem B3211001 : Blo 948586 3211001 := bstep (se 2 (by rfl) ⟨1204125, by rfl⟩ : syracuseStep 3211001 = 2408251) B2408251
theorem B950055 : Blo 948586 950055 := bstep (se 1 (by rfl) ⟨712541, by rfl⟩ : syracuseStep 950055 = 1425083) B1425083
theorem B3604297 : Blo 948586 3604297 := bstep (se 2 (by rfl) ⟨1351611, by rfl⟩ : syracuseStep 3604297 = 2703223) B2703223
theorem B950095 : Blo 948586 950095 := bstep (se 1 (by rfl) ⟨712571, by rfl⟩ : syracuseStep 950095 = 1425143) B1425143
theorem B950111 : Blo 948586 950111 := bstep (se 1 (by rfl) ⟨712583, by rfl⟩ : syracuseStep 950111 = 1425167) B1425167
theorem B950139 : Blo 948586 950139 := bstep (se 1 (by rfl) ⟨712604, by rfl⟩ : syracuseStep 950139 = 1425209) B1425209
theorem B950191 : Blo 948586 950191 := bstep (se 1 (by rfl) ⟨712643, by rfl⟩ : syracuseStep 950191 = 1425287) B1425287
theorem B950215 : Blo 948586 950215 := bstep (se 1 (by rfl) ⟨712661, by rfl⟩ : syracuseStep 950215 = 1425323) B1425323
theorem B950235 : Blo 948586 950235 := bstep (se 1 (by rfl) ⟨712676, by rfl⟩ : syracuseStep 950235 = 1425353) B1425353
theorem B1605595 : Blo 948586 1605595 := bstep (se 1 (by rfl) ⟨1204196, by rfl⟩ : syracuseStep 1605595 = 2408393) B2408393
theorem B3047483 : Blo 948586 3047483 := bstep (se 1 (by rfl) ⟨2285612, by rfl⟩ : syracuseStep 3047483 = 4571225) B4571225
theorem B20086865 : Blo 948586 20086865 := bstep (se 2 (by rfl) ⟨7532574, by rfl⟩ : syracuseStep 20086865 = 15065149) B15065149
theorem B10420325 : Blo 948586 10420325 := bstep (se 4 (by rfl) ⟨976905, by rfl⟩ : syracuseStep 10420325 = 1953811) B1953811
theorem B1605737 : Blo 948586 1605737 := bstep (se 2 (by rfl) ⟨602151, by rfl⟩ : syracuseStep 1605737 = 1204303) B1204303
theorem B950559 : Blo 948586 950559 := bstep (se 1 (by rfl) ⟨712919, by rfl⟩ : syracuseStep 950559 = 1425839) B1425839
theorem B950619 : Blo 948586 950619 := bstep (se 1 (by rfl) ⟨712964, by rfl⟩ : syracuseStep 950619 = 1425929) B1425929
theorem B950639 : Blo 948586 950639 := bstep (se 1 (by rfl) ⟨712979, by rfl⟩ : syracuseStep 950639 = 1425959) B1425959
theorem B1737071 : Blo 948586 1737071 := bstep (se 1 (by rfl) ⟨1302803, by rfl⟩ : syracuseStep 1737071 = 2605607) B2605607
theorem B950695 : Blo 948586 950695 := bstep (se 1 (by rfl) ⟨713021, by rfl⟩ : syracuseStep 950695 = 1426043) B1426043
theorem B950779 : Blo 948586 950779 := bstep (se 1 (by rfl) ⟨713084, by rfl⟩ : syracuseStep 950779 = 1426169) B1426169
theorem B950847 : Blo 948586 950847 := bstep (se 1 (by rfl) ⟨713135, by rfl⟩ : syracuseStep 950847 = 1426271) B1426271
theorem B1016383 : Blo 948586 1016383 := bstep (se 1 (by rfl) ⟨762287, by rfl⟩ : syracuseStep 1016383 = 1524575) B1524575
theorem B950855 : Blo 948586 950855 := bstep (se 1 (by rfl) ⟨713141, by rfl⟩ : syracuseStep 950855 = 1426283) B1426283
theorem B4063841 : Blo 948586 4063841 := bstep (se 2 (by rfl) ⟨1523940, by rfl⟩ : syracuseStep 4063841 = 3047881) B3047881
theorem B4063891 : Blo 948586 4063891 := bstep (se 1 (by rfl) ⟨3047918, by rfl⟩ : syracuseStep 4063891 = 6095837) B6095837
theorem B4817555 : Blo 948586 4817555 := bstep (se 1 (by rfl) ⟨3613166, by rfl⟩ : syracuseStep 4817555 = 7226333) B7226333
theorem B4752071 : Blo 948586 4752071 := bstep (se 1 (by rfl) ⟨3564053, by rfl⟩ : syracuseStep 4752071 = 7128107) B7128107
theorem B951007 : Blo 948586 951007 := bstep (se 1 (by rfl) ⟨713255, by rfl⟩ : syracuseStep 951007 = 1426511) B1426511
theorem B951087 : Blo 948586 951087 := bstep (se 1 (by rfl) ⟨713315, by rfl⟩ : syracuseStep 951087 = 1426631) B1426631
theorem B951195 : Blo 948586 951195 := bstep (se 1 (by rfl) ⟨713396, by rfl⟩ : syracuseStep 951195 = 1426793) B1426793
theorem B951247 : Blo 948586 951247 := bstep (se 1 (by rfl) ⟨713435, by rfl⟩ : syracuseStep 951247 = 1426871) B1426871
theorem B951271 : Blo 948586 951271 := bstep (se 1 (by rfl) ⟨713453, by rfl⟩ : syracuseStep 951271 = 1426907) B1426907
theorem B951583 : Blo 948586 951583 := bstep (se 1 (by rfl) ⟨713687, by rfl⟩ : syracuseStep 951583 = 1427375) B1427375
theorem B5211479 : Blo 948586 5211479 := bstep (se 1 (by rfl) ⟨3908609, by rfl⟩ : syracuseStep 5211479 = 7817219) B7817219
theorem B951643 : Blo 948586 951643 := bstep (se 1 (by rfl) ⟨713732, by rfl⟩ : syracuseStep 951643 = 1427465) B1427465
theorem B951663 : Blo 948586 951663 := bstep (se 1 (by rfl) ⟨713747, by rfl⟩ : syracuseStep 951663 = 1427495) B1427495
theorem B951719 : Blo 948586 951719 := bstep (se 1 (by rfl) ⟨713789, by rfl⟩ : syracuseStep 951719 = 1427579) B1427579
theorem B4818365 : Blo 948586 4818365 := bstep (se 3 (by rfl) ⟨903443, by rfl⟩ : syracuseStep 4818365 = 1806887) B1806887
theorem B1607161 : Blo 948586 1607161 := bstep (se 2 (by rfl) ⟨602685, by rfl⟩ : syracuseStep 1607161 = 1205371) B1205371
theorem B951803 : Blo 948586 951803 := bstep (se 1 (by rfl) ⟨713852, by rfl⟩ : syracuseStep 951803 = 1427705) B1427705
theorem B951871 : Blo 948586 951871 := bstep (se 1 (by rfl) ⟨713903, by rfl⟩ : syracuseStep 951871 = 1427807) B1427807
theorem B951879 : Blo 948586 951879 := bstep (se 1 (by rfl) ⟨713909, by rfl⟩ : syracuseStep 951879 = 1427819) B1427819
theorem B952031 : Blo 948586 952031 := bstep (se 1 (by rfl) ⟨714023, by rfl⟩ : syracuseStep 952031 = 1428047) B1428047
theorem B1607431 : Blo 948586 1607431 := bstep (se 1 (by rfl) ⟨1205573, by rfl⟩ : syracuseStep 1607431 = 2411147) B2411147
theorem B1607465 : Blo 948586 1607465 := bstep (se 2 (by rfl) ⟨602799, by rfl⟩ : syracuseStep 1607465 = 1205599) B1205599
theorem B952111 : Blo 948586 952111 := bstep (se 1 (by rfl) ⟨714083, by rfl⟩ : syracuseStep 952111 = 1428167) B1428167
theorem B3213161 : Blo 948586 3213161 := bstep (se 2 (by rfl) ⟨1204935, by rfl⟩ : syracuseStep 3213161 = 2409871) B2409871
theorem B36571013 : Blo 948586 36571013 := bstep (se 4 (by rfl) ⟨3428532, by rfl⟩ : syracuseStep 36571013 = 6857065) B6857065
theorem B952219 : Blo 948586 952219 := bstep (se 1 (by rfl) ⟨714164, by rfl⟩ : syracuseStep 952219 = 1428329) B1428329
theorem B952271 : Blo 948586 952271 := bstep (se 1 (by rfl) ⟨714203, by rfl⟩ : syracuseStep 952271 = 1428407) B1428407
theorem B952295 : Blo 948586 952295 := bstep (se 1 (by rfl) ⟨714221, by rfl⟩ : syracuseStep 952295 = 1428443) B1428443
theorem B3606713 : Blo 948586 3606713 := bstep (se 2 (by rfl) ⟨1352517, by rfl⟩ : syracuseStep 3606713 = 2705035) B2705035
theorem B7702781 : Blo 948586 7702781 := bstep (se 3 (by rfl) ⟨1444271, by rfl⟩ : syracuseStep 7702781 = 2888543) B2888543
theorem B3213593 : Blo 948586 3213593 := bstep (se 2 (by rfl) ⟨1205097, by rfl⟩ : syracuseStep 3213593 = 2410195) B2410195
theorem B4065565 : Blo 948586 4065565 := bstep (se 3 (by rfl) ⟨762293, by rfl⟩ : syracuseStep 4065565 = 1524587) B1524587
theorem B1804655 : Blo 948586 1804655 := bstep (se 1 (by rfl) ⟨1353491, by rfl⟩ : syracuseStep 1804655 = 2706983) B2706983
theorem B36997661 : Blo 948586 36997661 := bstep (se 3 (by rfl) ⟨6937061, by rfl⟩ : syracuseStep 36997661 = 13874123) B13874123
theorem B6097835 : Blo 948586 6097835 := bstep (se 1 (by rfl) ⟨4573376, by rfl⟩ : syracuseStep 6097835 = 9146753) B9146753
theorem B4066523 : Blo 948586 4066523 := bstep (se 1 (by rfl) ⟨3049892, by rfl⟩ : syracuseStep 4066523 = 6099785) B6099785
theorem B1805665 : Blo 948586 1805665 := bstep (se 2 (by rfl) ⟨677124, by rfl⟩ : syracuseStep 1805665 = 1354249) B1354249
theorem B2166355 : Blo 948586 2166355 := bstep (se 1 (by rfl) ⟨1624766, by rfl⟩ : syracuseStep 2166355 = 3249533) B3249533
theorem B3214943 : Blo 948586 3214943 := bstep (se 1 (by rfl) ⟨2411207, by rfl⟩ : syracuseStep 3214943 = 4822415) B4822415
theorem B3051275 : Blo 948586 3051275 := bstep (se 1 (by rfl) ⟨2288456, by rfl⟩ : syracuseStep 3051275 = 4576913) B4576913
theorem B2134439 : Blo 948586 2134439 := bstep (se 1 (by rfl) ⟨1600829, by rfl⟩ : syracuseStep 2134439 = 3201659) B3201659
theorem B5640623 : Blo 948586 5640623 := bstep (se 1 (by rfl) ⟨4230467, by rfl⟩ : syracuseStep 5640623 = 8460935) B8460935
theorem B2134547 : Blo 948586 2134547 := bstep (se 1 (by rfl) ⟨1600910, by rfl⟩ : syracuseStep 2134547 = 3201821) B3201821
theorem B6099475 : Blo 948586 6099475 := bstep (se 1 (by rfl) ⟨4574606, by rfl⟩ : syracuseStep 6099475 = 9149213) B9149213
theorem B2134601 : Blo 948586 2134601 := bstep (se 2 (by rfl) ⟨800475, by rfl⟩ : syracuseStep 2134601 = 1600951) B1600951
theorem B1807123 : Blo 948586 1807123 := bstep (se 1 (by rfl) ⟨1355342, by rfl⟩ : syracuseStep 1807123 = 2710685) B2710685
theorem B3707849 : Blo 948586 3707849 := bstep (se 2 (by rfl) ⟨1390443, by rfl⟩ : syracuseStep 3707849 = 2780887) B2780887
theorem B2135015 : Blo 948586 2135015 := bstep (se 1 (by rfl) ⟨1601261, by rfl⟩ : syracuseStep 2135015 = 3202523) B3202523
theorem B66819275 : Blo 948586 66819275 := bstep (se 1 (by rfl) ⟨50114456, by rfl⟩ : syracuseStep 66819275 = 100228913) B100228913
theorem B1283419 : Blo 948586 1283419 := bstep (se 1 (by rfl) ⟨962564, by rfl⟩ : syracuseStep 1283419 = 1925129) B1925129
theorem B2135393 : Blo 948586 2135393 := bstep (se 2 (by rfl) ⟨800772, by rfl⟩ : syracuseStep 2135393 = 1601545) B1601545
theorem B1807753 : Blo 948586 1807753 := bstep (se 2 (by rfl) ⟨677907, by rfl⟩ : syracuseStep 1807753 = 1355815) B1355815
theorem B5412257 : Blo 948586 5412257 := bstep (se 2 (by rfl) ⟨2029596, by rfl⟩ : syracuseStep 5412257 = 4059193) B4059193
theorem B2135483 : Blo 948586 2135483 := bstep (se 1 (by rfl) ⟨1601612, by rfl⟩ : syracuseStep 2135483 = 3203225) B3203225
theorem B2135609 : Blo 948586 2135609 := bstep (se 2 (by rfl) ⟨800853, by rfl⟩ : syracuseStep 2135609 = 1601707) B1601707
theorem B4331195 : Blo 948586 4331195 := bstep (se 1 (by rfl) ⟨3248396, by rfl⟩ : syracuseStep 4331195 = 6496793) B6496793
theorem B10295029 : Blo 948586 10295029 := bstep (se 5 (by rfl) ⟨482579, by rfl⟩ : syracuseStep 10295029 = 965159) B965159
theorem B16685189 : Blo 948586 16685189 := bstep (se 4 (by rfl) ⟨1564236, by rfl⟩ : syracuseStep 16685189 = 3128473) B3128473
theorem B2136275 : Blo 948586 2136275 := bstep (se 1 (by rfl) ⟨1602206, by rfl⟩ : syracuseStep 2136275 = 3204413) B3204413
theorem B2136329 : Blo 948586 2136329 := bstep (se 2 (by rfl) ⟨801123, by rfl⟩ : syracuseStep 2136329 = 1602247) B1602247
theorem B3610889 : Blo 948586 3610889 := bstep (se 2 (by rfl) ⟨1354083, by rfl⟩ : syracuseStep 3610889 = 2708167) B2708167
theorem B2136545 : Blo 948586 2136545 := bstep (se 2 (by rfl) ⟨801204, by rfl⟩ : syracuseStep 2136545 = 1602409) B1602409
theorem B41720579 : Blo 948586 41720579 := bstep (se 1 (by rfl) ⟨31290434, by rfl⟩ : syracuseStep 41720579 = 62580869) B62580869
theorem B2136851 : Blo 948586 2136851 := bstep (se 1 (by rfl) ⟨1602638, by rfl⟩ : syracuseStep 2136851 = 3205277) B3205277
theorem B2137211 : Blo 948586 2137211 := bstep (se 1 (by rfl) ⟨1602908, by rfl⟩ : syracuseStep 2137211 = 3205817) B3205817
theorem B2137337 : Blo 948586 2137337 := bstep (se 2 (by rfl) ⟨801501, by rfl⟩ : syracuseStep 2137337 = 1603003) B1603003
theorem B2137481 : Blo 948586 2137481 := bstep (se 2 (by rfl) ⟨801555, by rfl⟩ : syracuseStep 2137481 = 1603111) B1603111
theorem B2137607 : Blo 948586 2137607 := bstep (se 1 (by rfl) ⟨1603205, by rfl⟩ : syracuseStep 2137607 = 3206411) B3206411
theorem B2137787 : Blo 948586 2137787 := bstep (se 1 (by rfl) ⟨1603340, by rfl⟩ : syracuseStep 2137787 = 3206681) B3206681
theorem B2137913 : Blo 948586 2137913 := bstep (se 2 (by rfl) ⟨801717, by rfl⟩ : syracuseStep 2137913 = 1603435) B1603435
theorem B9117535 : Blo 948586 9117535 := bstep (se 1 (by rfl) ⟨6838151, by rfl⟩ : syracuseStep 9117535 = 13676303) B13676303
theorem B3612545 : Blo 948586 3612545 := bstep (se 2 (by rfl) ⟨1354704, by rfl⟩ : syracuseStep 3612545 = 2709409) B2709409
theorem B10264583 : Blo 948586 10264583 := bstep (se 1 (by rfl) ⟨7698437, by rfl⟩ : syracuseStep 10264583 = 15396875) B15396875
theorem B5414921 : Blo 948586 5414921 := bstep (se 2 (by rfl) ⟨2030595, by rfl⟩ : syracuseStep 5414921 = 4061191) B4061191
theorem B66855233 : Blo 948586 66855233 := bstep (se 2 (by rfl) ⟨25070712, by rfl⟩ : syracuseStep 66855233 = 50141425) B50141425
theorem B36610379 : Blo 948586 36610379 := bstep (se 1 (by rfl) ⟨27457784, by rfl⟩ : syracuseStep 36610379 = 54915569) B54915569
theorem B17375579 : Blo 948586 17375579 := bstep (se 1 (by rfl) ⟨13031684, by rfl⟩ : syracuseStep 17375579 = 26063369) B26063369
theorem B9249187 : Blo 948586 9249187 := bstep (se 1 (by rfl) ⟨6936890, by rfl⟩ : syracuseStep 9249187 = 13873781) B13873781
theorem B2138543 : Blo 948586 2138543 := bstep (se 1 (by rfl) ⟨1603907, by rfl⟩ : syracuseStep 2138543 = 3207815) B3207815
theorem B2138579 : Blo 948586 2138579 := bstep (se 1 (by rfl) ⟨1603934, by rfl⟩ : syracuseStep 2138579 = 3207869) B3207869
theorem B2138687 : Blo 948586 2138687 := bstep (se 1 (by rfl) ⟨1604015, by rfl⟩ : syracuseStep 2138687 = 3208031) B3208031
theorem B2138795 : Blo 948586 2138795 := bstep (se 1 (by rfl) ⟨1604096, by rfl⟩ : syracuseStep 2138795 = 3208193) B3208193
theorem B2139335 : Blo 948586 2139335 := bstep (se 1 (by rfl) ⟨1604501, by rfl⟩ : syracuseStep 2139335 = 3209003) B3209003
theorem B2139515 : Blo 948586 2139515 := bstep (se 1 (by rfl) ⟨1604636, by rfl⟩ : syracuseStep 2139515 = 3209273) B3209273
theorem B6956441 : Blo 948586 6956441 := bstep (se 2 (by rfl) ⟨2608665, by rfl⟩ : syracuseStep 6956441 = 5217331) B5217331
theorem B2401751 : Blo 948586 2401751 := bstep (se 1 (by rfl) ⟨1801313, by rfl⟩ : syracuseStep 2401751 = 3602627) B3602627
theorem B2139641 : Blo 948586 2139641 := bstep (se 2 (by rfl) ⟨802365, by rfl⟩ : syracuseStep 2139641 = 1604731) B1604731
theorem B2139731 : Blo 948586 2139731 := bstep (se 1 (by rfl) ⟨1604798, by rfl⟩ : syracuseStep 2139731 = 3209597) B3209597
theorem B2434655 : Blo 948586 2434655 := bstep (se 1 (by rfl) ⟨1825991, by rfl⟩ : syracuseStep 2434655 = 3651983) B3651983
theorem B56272583 : Blo 948586 56272583 := bstep (se 1 (by rfl) ⟨42204437, by rfl⟩ : syracuseStep 56272583 = 84408875) B84408875
theorem B2139911 : Blo 948586 2139911 := bstep (se 1 (by rfl) ⟨1604933, by rfl⟩ : syracuseStep 2139911 = 3209867) B3209867
theorem B4564765 : Blo 948586 4564765 := bstep (se 3 (by rfl) ⟨855893, by rfl⟩ : syracuseStep 4564765 = 1711787) B1711787
theorem B2402095 : Blo 948586 2402095 := bstep (se 1 (by rfl) ⟨1801571, by rfl⟩ : syracuseStep 2402095 = 3603143) B3603143
theorem B4564919 : Blo 948586 4564919 := bstep (se 1 (by rfl) ⟨3423689, by rfl⟩ : syracuseStep 4564919 = 6847379) B6847379
theorem B6498569 : Blo 948586 6498569 := bstep (se 2 (by rfl) ⟨2436963, by rfl⟩ : syracuseStep 6498569 = 4873927) B4873927
theorem B2140523 : Blo 948586 2140523 := bstep (se 1 (by rfl) ⟨1605392, by rfl⟩ : syracuseStep 2140523 = 3210785) B3210785
theorem B2402743 : Blo 948586 2402743 := bstep (se 1 (by rfl) ⟨1802057, by rfl⟩ : syracuseStep 2402743 = 3604115) B3604115
theorem B2140667 : Blo 948586 2140667 := bstep (se 1 (by rfl) ⟨1605500, by rfl⟩ : syracuseStep 2140667 = 3211001) B3211001
theorem B2140793 : Blo 948586 2140793 := bstep (se 2 (by rfl) ⟨802797, by rfl⟩ : syracuseStep 2140793 = 1605595) B1605595
theorem B2140847 : Blo 948586 2140847 := bstep (se 1 (by rfl) ⟨1605635, by rfl⟩ : syracuseStep 2140847 = 3211271) B3211271
theorem B39004865 : Blo 948586 39004865 := bstep (se 2 (by rfl) ⟨14626824, by rfl⟩ : syracuseStep 39004865 = 29253649) B29253649
theorem B2566903 : Blo 948586 2566903 := bstep (se 1 (by rfl) ⟨1925177, by rfl⟩ : syracuseStep 2566903 = 3850355) B3850355
theorem B2140919 : Blo 948586 2140919 := bstep (se 1 (by rfl) ⟨1605689, by rfl⟩ : syracuseStep 2140919 = 3211379) B3211379
theorem B2141099 : Blo 948586 2141099 := bstep (se 1 (by rfl) ⟨1605824, by rfl⟩ : syracuseStep 2141099 = 3211649) B3211649
theorem B14855183 : Blo 948586 14855183 := bstep (se 1 (by rfl) ⟨11141387, by rfl⟩ : syracuseStep 14855183 = 22282775) B22282775
theorem B9120883 : Blo 948586 9120883 := bstep (se 1 (by rfl) ⟨6840662, by rfl⟩ : syracuseStep 9120883 = 13681325) B13681325
theorem B14658731 : Blo 948586 14658731 := bstep (se 1 (by rfl) ⟨10994048, by rfl⟩ : syracuseStep 14658731 = 21988097) B21988097
theorem B5090525 : Blo 948586 5090525 := bstep (se 3 (by rfl) ⟨954473, by rfl⟩ : syracuseStep 5090525 = 1908947) B1908947
theorem B2141639 : Blo 948586 2141639 := bstep (se 1 (by rfl) ⟨1606229, by rfl⟩ : syracuseStep 2141639 = 3212459) B3212459
theorem B4566611 : Blo 948586 4566611 := bstep (se 1 (by rfl) ⟨3424958, by rfl⟩ : syracuseStep 4566611 = 6849917) B6849917
theorem B4566689 : Blo 948586 4566689 := bstep (se 2 (by rfl) ⟨1712508, by rfl⟩ : syracuseStep 4566689 = 3425017) B3425017
theorem B2141999 : Blo 948586 2141999 := bstep (se 1 (by rfl) ⟨1606499, by rfl⟩ : syracuseStep 2141999 = 3212999) B3212999
theorem B2404151 : Blo 948586 2404151 := bstep (se 1 (by rfl) ⟨1803113, by rfl⟩ : syracuseStep 2404151 = 3606227) B3606227
theorem B2404201 : Blo 948586 2404201 := bstep (se 2 (by rfl) ⟨901575, by rfl⟩ : syracuseStep 2404201 = 1803151) B1803151
theorem B103886873 : Blo 948586 103886873 := bstep (se 2 (by rfl) ⟨38957577, by rfl⟩ : syracuseStep 103886873 = 77915155) B77915155
theorem B3256345 : Blo 948586 3256345 := bstep (se 2 (by rfl) ⟨1221129, by rfl⟩ : syracuseStep 3256345 = 2442259) B2442259
theorem B15413611 : Blo 948586 15413611 := bstep (se 1 (by rfl) ⟨11560208, by rfl⟩ : syracuseStep 15413611 = 23120417) B23120417
theorem B2142575 : Blo 948586 2142575 := bstep (se 1 (by rfl) ⟨1606931, by rfl⟩ : syracuseStep 2142575 = 3213863) B3213863
theorem B2142647 : Blo 948586 2142647 := bstep (se 1 (by rfl) ⟨1606985, by rfl⟩ : syracuseStep 2142647 = 3213971) B3213971
theorem B2142791 : Blo 948586 2142791 := bstep (se 1 (by rfl) ⟨1607093, by rfl⟩ : syracuseStep 2142791 = 3214187) B3214187
theorem B2142827 : Blo 948586 2142827 := bstep (se 1 (by rfl) ⟨1607120, by rfl⟩ : syracuseStep 2142827 = 3214241) B3214241
theorem B7221959 : Blo 948586 7221959 := bstep (se 1 (by rfl) ⟨5416469, by rfl⟩ : syracuseStep 7221959 = 10832939) B10832939
theorem B5485391 : Blo 948586 5485391 := bstep (se 1 (by rfl) ⟨4114043, by rfl⟩ : syracuseStep 5485391 = 8228087) B8228087
theorem B1520615 : Blo 948586 1520615 := bstep (se 1 (by rfl) ⟨1140461, by rfl⟩ : syracuseStep 1520615 = 2280923) B2280923
theorem B2143223 : Blo 948586 2143223 := bstep (se 1 (by rfl) ⟨1607417, by rfl⟩ : syracuseStep 2143223 = 3214835) B3214835
theorem B2405609 : Blo 948586 2405609 := bstep (se 2 (by rfl) ⟨902103, by rfl⟩ : syracuseStep 2405609 = 1804207) B1804207
theorem B2405771 : Blo 948586 2405771 := bstep (se 1 (by rfl) ⟨1804328, by rfl⟩ : syracuseStep 2405771 = 3608657) B3608657
theorem B4568609 : Blo 948586 4568609 := bstep (se 2 (by rfl) ⟨1713228, by rfl⟩ : syracuseStep 4568609 = 3426457) B3426457
theorem B2405983 : Blo 948586 2405983 := bstep (se 1 (by rfl) ⟨1804487, by rfl⟩ : syracuseStep 2405983 = 3608975) B3608975
theorem B4339385 : Blo 948586 4339385 := bstep (se 2 (by rfl) ⟨1627269, by rfl⟩ : syracuseStep 4339385 = 3254539) B3254539
theorem B4110011 : Blo 948586 4110011 := bstep (se 1 (by rfl) ⟨3082508, by rfl⟩ : syracuseStep 4110011 = 6165017) B6165017
theorem B1423145 : Blo 948586 1423145 := bstep (se 2 (by rfl) ⟨533679, by rfl⟩ : syracuseStep 1423145 = 1067359) B1067359
theorem B1423151 : Blo 948586 1423151 := bstep (se 1 (by rfl) ⟨1067363, by rfl⟩ : syracuseStep 1423151 = 2134727) B2134727
theorem B2406611 : Blo 948586 2406611 := bstep (se 1 (by rfl) ⟨1804958, by rfl⟩ : syracuseStep 2406611 = 3609917) B3609917
theorem B1423625 : Blo 948586 1423625 := bstep (se 2 (by rfl) ⟨533859, by rfl⟩ : syracuseStep 1423625 = 1067719) B1067719
theorem B1423727 : Blo 948586 1423727 := bstep (se 1 (by rfl) ⟨1067795, by rfl⟩ : syracuseStep 1423727 = 2135591) B2135591
theorem B5421437 : Blo 948586 5421437 := bstep (se 3 (by rfl) ⟨1016519, by rfl⟩ : syracuseStep 5421437 = 2033039) B2033039
theorem B1423943 : Blo 948586 1423943 := bstep (se 1 (by rfl) ⟨1067957, by rfl⟩ : syracuseStep 1423943 = 2135915) B2135915
theorem B1423979 : Blo 948586 1423979 := bstep (se 1 (by rfl) ⟨1067984, by rfl⟩ : syracuseStep 1423979 = 2135969) B2135969
theorem B1424207 : Blo 948586 1424207 := bstep (se 1 (by rfl) ⟨1068155, by rfl⟩ : syracuseStep 1424207 = 2136311) B2136311
theorem B1424603 : Blo 948586 1424603 := bstep (se 1 (by rfl) ⟨1068452, by rfl⟩ : syracuseStep 1424603 = 2136905) B2136905
theorem B1424777 : Blo 948586 1424777 := bstep (se 2 (by rfl) ⟨534291, by rfl⟩ : syracuseStep 1424777 = 1068583) B1068583
theorem B2571833 : Blo 948586 2571833 := bstep (se 2 (by rfl) ⟨964437, by rfl⟩ : syracuseStep 2571833 = 1928875) B1928875
theorem B1130159 : Blo 948586 1130159 := bstep (se 1 (by rfl) ⟨847619, by rfl⟩ : syracuseStep 1130159 = 1695239) B1695239
theorem B1425131 : Blo 948586 1425131 := bstep (se 1 (by rfl) ⟨1068848, by rfl⟩ : syracuseStep 1425131 = 2137697) B2137697
theorem B3850031 : Blo 948586 3850031 := bstep (se 1 (by rfl) ⟨2887523, by rfl⟩ : syracuseStep 3850031 = 5775047) B5775047
theorem B1425359 : Blo 948586 1425359 := bstep (se 1 (by rfl) ⟨1069019, by rfl⟩ : syracuseStep 1425359 = 2138039) B2138039
theorem B2605337 : Blo 948586 2605337 := bstep (se 2 (by rfl) ⟨977001, by rfl⟩ : syracuseStep 2605337 = 1954003) B1954003
theorem B1425755 : Blo 948586 1425755 := bstep (se 1 (by rfl) ⟨1069316, by rfl⟩ : syracuseStep 1425755 = 2138633) B2138633
theorem B8110489 : Blo 948586 8110489 := bstep (se 2 (by rfl) ⟨3041433, by rfl⟩ : syracuseStep 8110489 = 6082867) B6082867
theorem B2408879 : Blo 948586 2408879 := bstep (se 1 (by rfl) ⟨1806659, by rfl⟩ : syracuseStep 2408879 = 3613319) B3613319
theorem B3424787 : Blo 948586 3424787 := bstep (se 1 (by rfl) ⟨2568590, by rfl⟩ : syracuseStep 3424787 = 5137181) B5137181
theorem B1425983 : Blo 948586 1425983 := bstep (se 1 (by rfl) ⟨1069487, by rfl⟩ : syracuseStep 1425983 = 2138975) B2138975
theorem B8110763 : Blo 948586 8110763 := bstep (se 1 (by rfl) ⟨6083072, by rfl⟩ : syracuseStep 8110763 = 12166145) B12166145
theorem B2704043 : Blo 948586 2704043 := bstep (se 1 (by rfl) ⟨2028032, by rfl⟩ : syracuseStep 2704043 = 4056065) B4056065
theorem B1426103 : Blo 948586 1426103 := bstep (se 1 (by rfl) ⟨1069577, by rfl⟩ : syracuseStep 1426103 = 2139155) B2139155
theorem B1426331 : Blo 948586 1426331 := bstep (se 1 (by rfl) ⟨1069748, by rfl⟩ : syracuseStep 1426331 = 2139497) B2139497
theorem B3425219 : Blo 948586 3425219 := bstep (se 1 (by rfl) ⟨2568914, by rfl⟩ : syracuseStep 3425219 = 5137829) B5137829
theorem B12174299 : Blo 948586 12174299 := bstep (se 1 (by rfl) ⟨9130724, by rfl⟩ : syracuseStep 12174299 = 18261449) B18261449
theorem B1426727 : Blo 948586 1426727 := bstep (se 1 (by rfl) ⟨1070045, by rfl⟩ : syracuseStep 1426727 = 2140091) B2140091
theorem B8111447 : Blo 948586 8111447 := bstep (se 1 (by rfl) ⟨6083585, by rfl⟩ : syracuseStep 8111447 = 12167171) B12167171
theorem B2311519 : Blo 948586 2311519 := bstep (se 1 (by rfl) ⟨1733639, by rfl⟩ : syracuseStep 2311519 = 3467279) B3467279
theorem B1426811 : Blo 948586 1426811 := bstep (se 1 (by rfl) ⟨1070108, by rfl⟩ : syracuseStep 1426811 = 2140217) B2140217
theorem B2409851 : Blo 948586 2409851 := bstep (se 1 (by rfl) ⟨1807388, by rfl⟩ : syracuseStep 2409851 = 3614777) B3614777
theorem B1426937 : Blo 948586 1426937 := bstep (se 2 (by rfl) ⟨535101, by rfl⟩ : syracuseStep 1426937 = 1070203) B1070203
theorem B1427039 : Blo 948586 1427039 := bstep (se 1 (by rfl) ⟨1070279, by rfl⟩ : syracuseStep 1427039 = 2140559) B2140559
theorem B2410145 : Blo 948586 2410145 := bstep (se 2 (by rfl) ⟨903804, by rfl⟩ : syracuseStep 2410145 = 1807609) B1807609
theorem B1427255 : Blo 948586 1427255 := bstep (se 1 (by rfl) ⟨1070441, by rfl⟩ : syracuseStep 1427255 = 2140883) B2140883
theorem B38979569 : Blo 948586 38979569 := bstep (se 2 (by rfl) ⟨14617338, by rfl⟩ : syracuseStep 38979569 = 29234677) B29234677
theorem B1427561 : Blo 948586 1427561 := bstep (se 2 (by rfl) ⟨535335, by rfl⟩ : syracuseStep 1427561 = 1070671) B1070671
theorem B4802813 : Blo 948586 4802813 := bstep (se 3 (by rfl) ⟨900527, by rfl⟩ : syracuseStep 4802813 = 1801055) B1801055
theorem B2410843 : Blo 948586 2410843 := bstep (se 1 (by rfl) ⟨1808132, by rfl⟩ : syracuseStep 2410843 = 3616265) B3616265
theorem B7227791 : Blo 948586 7227791 := bstep (se 1 (by rfl) ⟨5420843, by rfl⟩ : syracuseStep 7227791 = 10841687) B10841687
theorem B1067431 : Blo 948586 1067431 := bstep (se 1 (by rfl) ⟨800573, by rfl⟩ : syracuseStep 1067431 = 1601147) B1601147
theorem B1427879 : Blo 948586 1427879 := bstep (se 1 (by rfl) ⟨1070909, by rfl⟩ : syracuseStep 1427879 = 2141819) B2141819
theorem B105335261 : Blo 948586 105335261 := bstep (se 3 (by rfl) ⟨19750361, by rfl⟩ : syracuseStep 105335261 = 39500723) B39500723
theorem B1427963 : Blo 948586 1427963 := bstep (se 1 (by rfl) ⟨1070972, by rfl⟩ : syracuseStep 1427963 = 2141945) B2141945
theorem B2279999 : Blo 948586 2279999 := bstep (se 1 (by rfl) ⟨1709999, by rfl⟩ : syracuseStep 2279999 = 3419999) B3419999
theorem B3656299 : Blo 948586 3656299 := bstep (se 1 (by rfl) ⟨2742224, by rfl⟩ : syracuseStep 3656299 = 5484449) B5484449
theorem B1428089 : Blo 948586 1428089 := bstep (se 2 (by rfl) ⟨535533, by rfl⟩ : syracuseStep 1428089 = 1071067) B1071067
theorem B1428143 : Blo 948586 1428143 := bstep (se 1 (by rfl) ⟨1071107, by rfl⟩ : syracuseStep 1428143 = 2142215) B2142215
theorem B1428191 : Blo 948586 1428191 := bstep (se 1 (by rfl) ⟨1071143, by rfl⟩ : syracuseStep 1428191 = 2142287) B2142287
theorem B1068007 : Blo 948586 1068007 := bstep (se 1 (by rfl) ⟨801005, by rfl⟩ : syracuseStep 1068007 = 1602011) B1602011
theorem B1428455 : Blo 948586 1428455 := bstep (se 1 (by rfl) ⟨1071341, by rfl⟩ : syracuseStep 1428455 = 2142683) B2142683
theorem B4803623 : Blo 948586 4803623 := bstep (se 1 (by rfl) ⟨3602717, by rfl⟩ : syracuseStep 4803623 = 7205435) B7205435
theorem B2083963 : Blo 948586 2083963 := bstep (se 1 (by rfl) ⟨1562972, by rfl⟩ : syracuseStep 2083963 = 3125945) B3125945
theorem B1428713 : Blo 948586 1428713 := bstep (se 2 (by rfl) ⟨535767, by rfl⟩ : syracuseStep 1428713 = 1071535) B1071535
theorem B1428767 : Blo 948586 1428767 := bstep (se 1 (by rfl) ⟨1071575, by rfl⟩ : syracuseStep 1428767 = 2143151) B2143151
theorem B46222913 : Blo 948586 46222913 := bstep (se 2 (by rfl) ⟨17333592, by rfl⟩ : syracuseStep 46222913 = 34667185) B34667185
theorem B20598533 : Blo 948586 20598533 := bstep (se 4 (by rfl) ⟨1931112, by rfl⟩ : syracuseStep 20598533 = 3862225) B3862225
theorem B1856063 : Blo 948586 1856063 := bstep (se 1 (by rfl) ⟨1392047, by rfl⟩ : syracuseStep 1856063 = 2784095) B2784095
theorem B1069663 : Blo 948586 1069663 := bstep (se 1 (by rfl) ⟨802247, by rfl⟩ : syracuseStep 1069663 = 1604495) B1604495
theorem B4805729 : Blo 948586 4805729 := bstep (se 2 (by rfl) ⟨1802148, by rfl⟩ : syracuseStep 4805729 = 3604297) B3604297
theorem B4576607 : Blo 948586 4576607 := bstep (se 1 (by rfl) ⟨3432455, by rfl⟩ : syracuseStep 4576607 = 6864911) B6864911
theorem B1070815 : Blo 948586 1070815 := bstep (se 1 (by rfl) ⟨803111, by rfl⟩ : syracuseStep 1070815 = 1606223) B1606223
theorem B1071391 : Blo 948586 1071391 := bstep (se 1 (by rfl) ⟨803543, by rfl⟩ : syracuseStep 1071391 = 1607087) B1607087
theorem B1202683 : Blo 948586 1202683 := bstep (se 1 (by rfl) ⟨902012, by rfl⟩ : syracuseStep 1202683 = 1804025) B1804025
theorem B11262503 : Blo 948586 11262503 := bstep (se 1 (by rfl) ⟨8446877, by rfl⟩ : syracuseStep 11262503 = 16893755) B16893755
theorem B20798209 : Blo 948586 20798209 := bstep (se 2 (by rfl) ⟨7799328, by rfl⟩ : syracuseStep 20798209 = 15598657) B15598657
theorem B4807997 : Blo 948586 4807997 := bstep (se 3 (by rfl) ⟨901499, by rfl⟩ : syracuseStep 4807997 = 1802999) B1802999
theorem B3661175 : Blo 948586 3661175 := bstep (se 1 (by rfl) ⟨2745881, by rfl⟩ : syracuseStep 3661175 = 5491763) B5491763
theorem B1203655 : Blo 948586 1203655 := bstep (se 1 (by rfl) ⟨902741, by rfl⟩ : syracuseStep 1203655 = 1805483) B1805483
theorem B3431879 : Blo 948586 3431879 := bstep (se 1 (by rfl) ⟨2573909, by rfl⟩ : syracuseStep 3431879 = 5147819) B5147819
theorem B7692407 : Blo 948586 7692407 := bstep (se 1 (by rfl) ⟨5769305, by rfl⟩ : syracuseStep 7692407 = 11538611) B11538611
theorem B1204571 : Blo 948586 1204571 := bstep (se 1 (by rfl) ⟨903428, by rfl⟩ : syracuseStep 1204571 = 1806857) B1806857
theorem B3203603 : Blo 948586 3203603 := bstep (se 1 (by rfl) ⟨2402702, by rfl⟩ : syracuseStep 3203603 = 4805405) B4805405
theorem B2056951 : Blo 948586 2056951 := bstep (se 1 (by rfl) ⟨1542713, by rfl⟩ : syracuseStep 2056951 = 3085427) B3085427
theorem B1205047 : Blo 948586 1205047 := bstep (se 1 (by rfl) ⟨903785, by rfl⟩ : syracuseStep 1205047 = 1807571) B1807571
theorem B9266015 : Blo 948586 9266015 := bstep (se 1 (by rfl) ⟨6949511, by rfl⟩ : syracuseStep 9266015 = 13899023) B13899023
theorem B12346273 : Blo 948586 12346273 := bstep (se 2 (by rfl) ⟨4629852, by rfl⟩ : syracuseStep 12346273 = 9259705) B9259705
theorem B6841381 : Blo 948586 6841381 := bstep (se 4 (by rfl) ⟨641379, by rfl⟩ : syracuseStep 6841381 = 1282759) B1282759
theorem B1205543 : Blo 948586 1205543 := bstep (se 1 (by rfl) ⟨904157, by rfl⟩ : syracuseStep 1205543 = 1808315) B1808315
theorem B976379 : Blo 948586 976379 := bstep (se 1 (by rfl) ⟨732284, by rfl⟩ : syracuseStep 976379 = 1464569) B1464569
theorem B4810427 : Blo 948586 4810427 := bstep (se 1 (by rfl) ⟨3607820, by rfl⟩ : syracuseStep 4810427 = 7215641) B7215641
theorem B13723357 : Blo 948586 13723357 := bstep (se 3 (by rfl) ⟨2573129, by rfl⟩ : syracuseStep 13723357 = 5146259) B5146259
theorem B15427361 : Blo 948586 15427361 := bstep (se 2 (by rfl) ⟨5785260, by rfl⟩ : syracuseStep 15427361 = 11570521) B11570521
theorem B13691065 : Blo 948586 13691065 := bstep (se 2 (by rfl) ⟨5134149, by rfl⟩ : syracuseStep 13691065 = 10268299) B10268299
theorem B8120573 : Blo 948586 8120573 := bstep (se 3 (by rfl) ⟨1522607, by rfl⟩ : syracuseStep 8120573 = 3045215) B3045215
theorem B3205385 : Blo 948586 3205385 := bstep (se 2 (by rfl) ⟨1202019, by rfl⟩ : syracuseStep 3205385 = 2404039) B2404039
theorem B4057775 : Blo 948586 4057775 := bstep (se 1 (by rfl) ⟨3043331, by rfl⟩ : syracuseStep 4057775 = 6086663) B6086663
theorem B8907995 : Blo 948586 8907995 := bstep (se 1 (by rfl) ⟨6680996, by rfl⟩ : syracuseStep 8907995 = 13361993) B13361993
theorem B1142047 : Blo 948586 1142047 := bstep (se 1 (by rfl) ⟨856535, by rfl⟩ : syracuseStep 1142047 = 1713071) B1713071
theorem B1043803 : Blo 948586 1043803 := bstep (se 1 (by rfl) ⟨782852, by rfl⟩ : syracuseStep 1043803 = 1565705) B1565705
theorem B3206519 : Blo 948586 3206519 := bstep (se 1 (by rfl) ⟨2404889, by rfl⟩ : syracuseStep 3206519 = 4809779) B4809779
theorem B2026939 : Blo 948586 2026939 := bstep (se 1 (by rfl) ⟨1520204, by rfl⟩ : syracuseStep 2026939 = 3040409) B3040409
theorem B4812371 : Blo 948586 4812371 := bstep (se 1 (by rfl) ⟨3609278, by rfl⟩ : syracuseStep 4812371 = 7218557) B7218557
theorem B3043433 : Blo 948586 3043433 := bstep (se 2 (by rfl) ⟨1141287, by rfl⟩ : syracuseStep 3043433 = 2282575) B2282575
theorem B1601903 : Blo 948586 1601903 := bstep (se 1 (by rfl) ⟨1201427, by rfl⟩ : syracuseStep 1601903 = 2402855) B2402855
theorem B3207599 : Blo 948586 3207599 := bstep (se 1 (by rfl) ⟨2405699, by rfl⟩ : syracuseStep 3207599 = 4811399) B4811399
theorem B1143239 : Blo 948586 1143239 := bstep (se 1 (by rfl) ⟨857429, by rfl⟩ : syracuseStep 1143239 = 1714859) B1714859
theorem B1602119 : Blo 948586 1602119 := bstep (se 1 (by rfl) ⟨1201589, by rfl⟩ : syracuseStep 1602119 = 2403179) B2403179
theorem B16708193 : Blo 948586 16708193 := bstep (se 2 (by rfl) ⟨6265572, by rfl⟩ : syracuseStep 16708193 = 12531145) B12531145
theorem B5403257 : Blo 948586 5403257 := bstep (se 2 (by rfl) ⟨2026221, by rfl⟩ : syracuseStep 5403257 = 4052443) B4052443
theorem B58422059 : Blo 948586 58422059 := bstep (se 1 (by rfl) ⟨43816544, by rfl⟩ : syracuseStep 58422059 = 87633089) B87633089
theorem B5862223 : Blo 948586 5862223 := bstep (se 1 (by rfl) ⟨4396667, by rfl⟩ : syracuseStep 5862223 = 8793335) B8793335
theorem B6091685 : Blo 948586 6091685 := bstep (se 4 (by rfl) ⟨571095, by rfl⟩ : syracuseStep 6091685 = 1142191) B1142191
theorem B1602551 : Blo 948586 1602551 := bstep (se 1 (by rfl) ⟨1201913, by rfl⟩ : syracuseStep 1602551 = 2403827) B2403827
theorem B4060151 : Blo 948586 4060151 := bstep (se 1 (by rfl) ⟨3045113, by rfl⟩ : syracuseStep 4060151 = 6090227) B6090227
theorem B3208571 : Blo 948586 3208571 := bstep (se 1 (by rfl) ⟨2406428, by rfl⟩ : syracuseStep 3208571 = 4812857) B4812857
theorem B3601853 : Blo 948586 3601853 := bstep (se 3 (by rfl) ⟨675347, by rfl⟩ : syracuseStep 3601853 = 1350695) B1350695
theorem B8123885 : Blo 948586 8123885 := bstep (se 3 (by rfl) ⟨1523228, by rfl⟩ : syracuseStep 8123885 = 3046457) B3046457
theorem B7206407 : Blo 948586 7206407 := bstep (se 1 (by rfl) ⟨5404805, by rfl⟩ : syracuseStep 7206407 = 10809611) B10809611
theorem B1603307 : Blo 948586 1603307 := bstep (se 1 (by rfl) ⟨1202480, by rfl⟩ : syracuseStep 1603307 = 2404961) B2404961
theorem B12187421 : Blo 948586 12187421 := bstep (se 3 (by rfl) ⟨2285141, by rfl⟩ : syracuseStep 12187421 = 4570283) B4570283
theorem B1832911 : Blo 948586 1832911 := bstep (se 1 (by rfl) ⟨1374683, by rfl⟩ : syracuseStep 1832911 = 2749367) B2749367
theorem B2029673 : Blo 948586 2029673 := bstep (se 2 (by rfl) ⟨761127, by rfl⟩ : syracuseStep 2029673 = 1522255) B1522255
theorem B4061465 : Blo 948586 4061465 := bstep (se 2 (by rfl) ⟨1523049, by rfl⟩ : syracuseStep 4061465 = 3046099) B3046099
theorem B948591 : Blo 948586 948591 := bstep (se 1 (by rfl) ⟨711443, by rfl⟩ : syracuseStep 948591 = 1422887) B1422887
theorem B1374575 : Blo 948586 1374575 := bstep (se 1 (by rfl) ⟨1030931, by rfl⟩ : syracuseStep 1374575 = 2061863) B2061863
theorem B948647 : Blo 948586 948647 := bstep (se 1 (by rfl) ⟨711485, by rfl⟩ : syracuseStep 948647 = 1422971) B1422971
theorem B4815287 : Blo 948586 4815287 := bstep (se 1 (by rfl) ⟨3611465, by rfl⟩ : syracuseStep 4815287 = 7222931) B7222931
theorem B948731 : Blo 948586 948731 := bstep (se 1 (by rfl) ⟨711548, by rfl⟩ : syracuseStep 948731 = 1423097) B1423097
theorem B948799 : Blo 948586 948799 := bstep (se 1 (by rfl) ⟨711599, by rfl⟩ : syracuseStep 948799 = 1423199) B1423199
theorem B948807 : Blo 948586 948807 := bstep (se 1 (by rfl) ⟨711605, by rfl⟩ : syracuseStep 948807 = 1423211) B1423211
theorem B1604279 : Blo 948586 1604279 := bstep (se 1 (by rfl) ⟨1203209, by rfl⟩ : syracuseStep 1604279 = 2406419) B2406419
theorem B948959 : Blo 948586 948959 := bstep (se 1 (by rfl) ⟨711719, by rfl⟩ : syracuseStep 948959 = 1423439) B1423439
theorem B3209975 : Blo 948586 3209975 := bstep (se 1 (by rfl) ⟨2407481, by rfl⟩ : syracuseStep 3209975 = 4814963) B4814963
theorem B949039 : Blo 948586 949039 := bstep (se 1 (by rfl) ⟨711779, by rfl⟩ : syracuseStep 949039 = 1423559) B1423559
theorem B3603325 : Blo 948586 3603325 := bstep (se 3 (by rfl) ⟨675623, by rfl⟩ : syracuseStep 3603325 = 1351247) B1351247
theorem B949147 : Blo 948586 949147 := bstep (se 1 (by rfl) ⟨711860, by rfl⟩ : syracuseStep 949147 = 1423721) B1423721
theorem B7207865 : Blo 948586 7207865 := bstep (se 2 (by rfl) ⟨2702949, by rfl⟩ : syracuseStep 7207865 = 5405899) B5405899
theorem B949199 : Blo 948586 949199 := bstep (se 1 (by rfl) ⟨711899, by rfl⟩ : syracuseStep 949199 = 1423799) B1423799
theorem B949223 : Blo 948586 949223 := bstep (se 1 (by rfl) ⟨711917, by rfl⟩ : syracuseStep 949223 = 1423835) B1423835
theorem B1801207 : Blo 948586 1801207 := bstep (se 1 (by rfl) ⟨1350905, by rfl⟩ : syracuseStep 1801207 = 2701811) B2701811
theorem B1801435 : Blo 948586 1801435 := bstep (se 1 (by rfl) ⟨1351076, by rfl⟩ : syracuseStep 1801435 = 2702153) B2702153
theorem B949535 : Blo 948586 949535 := bstep (se 1 (by rfl) ⟨712151, by rfl⟩ : syracuseStep 949535 = 1424303) B1424303
theorem B1801511 : Blo 948586 1801511 := bstep (se 1 (by rfl) ⟨1351133, by rfl⟩ : syracuseStep 1801511 = 2702267) B2702267
theorem B949595 : Blo 948586 949595 := bstep (se 1 (by rfl) ⟨712196, by rfl⟩ : syracuseStep 949595 = 1424393) B1424393
theorem B949615 : Blo 948586 949615 := bstep (se 1 (by rfl) ⟨712211, by rfl⟩ : syracuseStep 949615 = 1424423) B1424423
theorem B1801595 : Blo 948586 1801595 := bstep (se 1 (by rfl) ⟨1351196, by rfl⟩ : syracuseStep 1801595 = 2702393) B2702393
theorem B1605001 : Blo 948586 1605001 := bstep (se 2 (by rfl) ⟨601875, by rfl⟩ : syracuseStep 1605001 = 1203751) B1203751
theorem B949671 : Blo 948586 949671 := bstep (se 1 (by rfl) ⟨712253, by rfl⟩ : syracuseStep 949671 = 1424507) B1424507
theorem B5144057 : Blo 948586 5144057 := bstep (se 2 (by rfl) ⟨1929021, by rfl⟩ : syracuseStep 5144057 = 3858043) B3858043
theorem B949755 : Blo 948586 949755 := bstep (se 1 (by rfl) ⟨712316, by rfl⟩ : syracuseStep 949755 = 1424633) B1424633
theorem B949823 : Blo 948586 949823 := bstep (se 1 (by rfl) ⟨712367, by rfl⟩ : syracuseStep 949823 = 1424735) B1424735
theorem B949831 : Blo 948586 949831 := bstep (se 1 (by rfl) ⟨712373, by rfl⟩ : syracuseStep 949831 = 1424747) B1424747
theorem B949983 : Blo 948586 949983 := bstep (se 1 (by rfl) ⟨712487, by rfl⟩ : syracuseStep 949983 = 1424975) B1424975
theorem B950063 : Blo 948586 950063 := bstep (se 1 (by rfl) ⟨712547, by rfl⟩ : syracuseStep 950063 = 1425095) B1425095
theorem B3211055 : Blo 948586 3211055 := bstep (se 1 (by rfl) ⟨2408291, by rfl⟩ : syracuseStep 3211055 = 4816583) B4816583
theorem B1605433 : Blo 948586 1605433 := bstep (se 2 (by rfl) ⟨602037, by rfl⟩ : syracuseStep 1605433 = 1204075) B1204075
theorem B950171 : Blo 948586 950171 := bstep (se 1 (by rfl) ⟨712628, by rfl⟩ : syracuseStep 950171 = 1425257) B1425257
theorem B950223 : Blo 948586 950223 := bstep (se 1 (by rfl) ⟨712667, by rfl⟩ : syracuseStep 950223 = 1425335) B1425335
theorem B1015759 : Blo 948586 1015759 := bstep (se 1 (by rfl) ⟨761819, by rfl⟩ : syracuseStep 1015759 = 1523639) B1523639
theorem B950247 : Blo 948586 950247 := bstep (se 1 (by rfl) ⟨712685, by rfl⟩ : syracuseStep 950247 = 1425371) B1425371
theorem B2031655 : Blo 948586 2031655 := bstep (se 1 (by rfl) ⟨1523741, by rfl⟩ : syracuseStep 2031655 = 3047483) B3047483
theorem B6946883 : Blo 948586 6946883 := bstep (se 1 (by rfl) ⟨5210162, by rfl⟩ : syracuseStep 6946883 = 10420325) B10420325
theorem B17367173 : Blo 948586 17367173 := bstep (se 4 (by rfl) ⟨1628172, by rfl⟩ : syracuseStep 17367173 = 3256345) B3256345
theorem B1736891 : Blo 948586 1736891 := bstep (se 1 (by rfl) ⟨1302668, by rfl⟩ : syracuseStep 1736891 = 2605337) B2605337
theorem B950503 : Blo 948586 950503 := bstep (se 1 (by rfl) ⟨712877, by rfl⟩ : syracuseStep 950503 = 1425755) B1425755
theorem B1605919 : Blo 948586 1605919 := bstep (se 1 (by rfl) ⟨1204439, by rfl⟩ : syracuseStep 1605919 = 2408879) B2408879
theorem B950655 : Blo 948586 950655 := bstep (se 1 (by rfl) ⟨712991, by rfl⟩ : syracuseStep 950655 = 1425983) B1425983
theorem B3211703 : Blo 948586 3211703 := bstep (se 1 (by rfl) ⟨2408777, by rfl⟩ : syracuseStep 3211703 = 4817555) B4817555
theorem B5407175 : Blo 948586 5407175 := bstep (se 1 (by rfl) ⟨4055381, by rfl⟩ : syracuseStep 5407175 = 8110763) B8110763
theorem B950735 : Blo 948586 950735 := bstep (se 1 (by rfl) ⟨713051, by rfl⟩ : syracuseStep 950735 = 1426103) B1426103
theorem B10813985 : Blo 948586 10813985 := bstep (se 2 (by rfl) ⟨4055244, by rfl⟩ : syracuseStep 10813985 = 8110489) B8110489
theorem B950887 : Blo 948586 950887 := bstep (se 1 (by rfl) ⟨713165, by rfl⟩ : syracuseStep 950887 = 1426331) B1426331
theorem B951151 : Blo 948586 951151 := bstep (se 1 (by rfl) ⟨713363, by rfl⟩ : syracuseStep 951151 = 1426727) B1426727
theorem B5407631 : Blo 948586 5407631 := bstep (se 1 (by rfl) ⟨4055723, by rfl⟩ : syracuseStep 5407631 = 8111447) B8111447
theorem B3212189 : Blo 948586 3212189 := bstep (se 3 (by rfl) ⟨602285, by rfl⟩ : syracuseStep 3212189 = 1204571) B1204571
theorem B951207 : Blo 948586 951207 := bstep (se 1 (by rfl) ⟨713405, by rfl⟩ : syracuseStep 951207 = 1426811) B1426811
theorem B1606567 : Blo 948586 1606567 := bstep (se 1 (by rfl) ⟨1204925, by rfl⟩ : syracuseStep 1606567 = 2409851) B2409851
theorem B3212243 : Blo 948586 3212243 := bstep (se 1 (by rfl) ⟨2409182, by rfl⟩ : syracuseStep 3212243 = 4818365) B4818365
theorem B951291 : Blo 948586 951291 := bstep (se 1 (by rfl) ⟨713468, by rfl⟩ : syracuseStep 951291 = 1426937) B1426937
theorem B951359 : Blo 948586 951359 := bstep (se 1 (by rfl) ⟨713519, by rfl⟩ : syracuseStep 951359 = 1427039) B1427039
theorem B1606729 : Blo 948586 1606729 := bstep (se 2 (by rfl) ⟨602523, by rfl⟩ : syracuseStep 1606729 = 1205047) B1205047
theorem B1606763 : Blo 948586 1606763 := bstep (se 1 (by rfl) ⟨1205072, by rfl⟩ : syracuseStep 1606763 = 2410145) B2410145
theorem B3048637 : Blo 948586 3048637 := bstep (se 3 (by rfl) ⟨571619, by rfl⟩ : syracuseStep 3048637 = 1143239) B1143239
theorem B951503 : Blo 948586 951503 := bstep (se 1 (by rfl) ⟨713627, by rfl⟩ : syracuseStep 951503 = 1427255) B1427255
theorem B24380675 : Blo 948586 24380675 := bstep (se 1 (by rfl) ⟨18285506, by rfl⟩ : syracuseStep 24380675 = 36571013) B36571013
theorem B25986379 : Blo 948586 25986379 := bstep (se 1 (by rfl) ⟨19489784, by rfl⟩ : syracuseStep 25986379 = 38979569) B38979569
theorem B951707 : Blo 948586 951707 := bstep (se 1 (by rfl) ⟨713780, by rfl⟩ : syracuseStep 951707 = 1427561) B1427561
theorem B4818527 : Blo 948586 4818527 := bstep (se 1 (by rfl) ⟨3613895, by rfl⟩ : syracuseStep 4818527 = 7227791) B7227791
theorem B951919 : Blo 948586 951919 := bstep (se 1 (by rfl) ⟨713939, by rfl⟩ : syracuseStep 951919 = 1427879) B1427879
theorem B70223507 : Blo 948586 70223507 := bstep (se 1 (by rfl) ⟨52667630, by rfl⟩ : syracuseStep 70223507 = 105335261) B105335261
theorem B951975 : Blo 948586 951975 := bstep (se 1 (by rfl) ⟨713981, by rfl⟩ : syracuseStep 951975 = 1427963) B1427963
theorem B952059 : Blo 948586 952059 := bstep (se 1 (by rfl) ⟨714044, by rfl⟩ : syracuseStep 952059 = 1428089) B1428089
theorem B7210781 : Blo 948586 7210781 := bstep (se 3 (by rfl) ⟨1352021, by rfl⟩ : syracuseStep 7210781 = 2704043) B2704043
theorem B952095 : Blo 948586 952095 := bstep (se 1 (by rfl) ⟨714071, by rfl⟩ : syracuseStep 952095 = 1428143) B1428143
theorem B3082025 : Blo 948586 3082025 := bstep (se 2 (by rfl) ⟨1155759, by rfl⟩ : syracuseStep 3082025 = 2311519) B2311519
theorem B952127 : Blo 948586 952127 := bstep (se 1 (by rfl) ⟨714095, by rfl⟩ : syracuseStep 952127 = 1428191) B1428191
theorem B4065223 : Blo 948586 4065223 := bstep (se 1 (by rfl) ⟨3048917, by rfl⟩ : syracuseStep 4065223 = 6097835) B6097835
theorem B952303 : Blo 948586 952303 := bstep (se 1 (by rfl) ⟨714227, by rfl⟩ : syracuseStep 952303 = 1428455) B1428455
theorem B952475 : Blo 948586 952475 := bstep (se 1 (by rfl) ⟨714356, by rfl⟩ : syracuseStep 952475 = 1428713) B1428713
theorem B952511 : Blo 948586 952511 := bstep (se 1 (by rfl) ⟨714383, by rfl⟩ : syracuseStep 952511 = 1428767) B1428767
theorem B24709373 : Blo 948586 24709373 := bstep (se 3 (by rfl) ⟨4633007, by rfl⟩ : syracuseStep 24709373 = 9266015) B9266015
theorem B13732355 : Blo 948586 13732355 := bstep (se 1 (by rfl) ⟨10299266, by rfl⟩ : syracuseStep 13732355 = 20598533) B20598533
theorem B18254753 : Blo 948586 18254753 := bstep (se 2 (by rfl) ⟨6845532, by rfl⟩ : syracuseStep 18254753 = 13691065) B13691065
theorem B3214457 : Blo 948586 3214457 := bstep (se 2 (by rfl) ⟨1205421, by rfl⟩ : syracuseStep 3214457 = 2410843) B2410843
theorem B3214781 : Blo 948586 3214781 := bstep (se 3 (by rfl) ⟨602771, by rfl⟩ : syracuseStep 3214781 = 1205543) B1205543
theorem B13897277 : Blo 948586 13897277 := bstep (se 3 (by rfl) ⟨2605739, by rfl⟩ : syracuseStep 13897277 = 5211479) B5211479
theorem B3051071 : Blo 948586 3051071 := bstep (se 1 (by rfl) ⟨2288303, by rfl⟩ : syracuseStep 3051071 = 4576607) B4576607
theorem B3608171 : Blo 948586 3608171 := bstep (se 1 (by rfl) ⟨2706128, by rfl⟩ : syracuseStep 3608171 = 5412257) B5412257
theorem B2887463 : Blo 948586 2887463 := bstep (se 1 (by rfl) ⟨2165597, by rfl⟩ : syracuseStep 2887463 = 4331195) B4331195
theorem B12161177 : Blo 948586 12161177 := bstep (se 2 (by rfl) ⟨4560441, by rfl⟩ : syracuseStep 12161177 = 9120883) B9120883
theorem B6492413 : Blo 948586 6492413 := bstep (se 3 (by rfl) ⟨1217327, by rfl⟩ : syracuseStep 6492413 = 2434655) B2434655
theorem B2888473 : Blo 948586 2888473 := bstep (se 2 (by rfl) ⟨1083177, by rfl⟩ : syracuseStep 2888473 = 2166355) B2166355
theorem B3609947 : Blo 948586 3609947 := bstep (se 1 (by rfl) ⟨2707460, by rfl⟩ : syracuseStep 3609947 = 5414921) B5414921
theorem B44570155 : Blo 948586 44570155 := bstep (se 1 (by rfl) ⟨33427616, by rfl⟩ : syracuseStep 44570155 = 66855233) B66855233
theorem B2135735 : Blo 948586 2135735 := bstep (se 1 (by rfl) ⟨1601801, by rfl⟩ : syracuseStep 2135735 = 3203603) B3203603
theorem B20551481 : Blo 948586 20551481 := bstep (se 2 (by rfl) ⟨7706805, by rfl⟩ : syracuseStep 20551481 = 15413611) B15413611
theorem B8132633 : Blo 948586 8132633 := bstep (se 2 (by rfl) ⟨3049737, by rfl⟩ : syracuseStep 8132633 = 6099475) B6099475
theorem B5413715 : Blo 948586 5413715 := bstep (se 1 (by rfl) ⟨4060286, by rfl⟩ : syracuseStep 5413715 = 8120573) B8120573
theorem B2136923 : Blo 948586 2136923 := bstep (se 1 (by rfl) ⟨1602692, by rfl⟩ : syracuseStep 2136923 = 3205385) B3205385
theorem B4332379 : Blo 948586 4332379 := bstep (se 1 (by rfl) ⟨3249284, by rfl⟩ : syracuseStep 4332379 = 6498569) B6498569
theorem B1711225 : Blo 948586 1711225 := bstep (se 2 (by rfl) ⟨641709, by rfl⟩ : syracuseStep 1711225 = 1283419) B1283419
theorem B9903455 : Blo 948586 9903455 := bstep (se 1 (by rfl) ⟨7427591, by rfl⟩ : syracuseStep 9903455 = 14855183) B14855183
theorem B9772487 : Blo 948586 9772487 := bstep (se 1 (by rfl) ⟨7329365, by rfl⟩ : syracuseStep 9772487 = 14658731) B14658731
theorem B2137679 : Blo 948586 2137679 := bstep (se 1 (by rfl) ⟨1603259, by rfl⟩ : syracuseStep 2137679 = 3206519) B3206519
theorem B2138399 : Blo 948586 2138399 := bstep (se 1 (by rfl) ⟨1603799, by rfl⟩ : syracuseStep 2138399 = 3207599) B3207599
theorem B2139047 : Blo 948586 2139047 := bstep (se 1 (by rfl) ⟨1604285, by rfl⟩ : syracuseStep 2139047 = 3208571) B3208571
theorem B2401235 : Blo 948586 2401235 := bstep (se 1 (by rfl) ⟨1800926, by rfl⟩ : syracuseStep 2401235 = 3601853) B3601853
theorem B5415923 : Blo 948586 5415923 := bstep (se 1 (by rfl) ⟨4061942, by rfl⟩ : syracuseStep 5415923 = 8123885) B8123885
theorem B27730945 : Blo 948586 27730945 := bstep (se 2 (by rfl) ⟨10399104, by rfl⟩ : syracuseStep 27730945 = 20798209) B20798209
theorem B2892923 : Blo 948586 2892923 := bstep (se 1 (by rfl) ⟨2169692, by rfl⟩ : syracuseStep 2892923 = 4339385) B4339385
theorem B2401609 : Blo 948586 2401609 := bstep (se 2 (by rfl) ⟨900603, by rfl⟩ : syracuseStep 2401609 = 1801207) B1801207
theorem B1353115 : Blo 948586 1353115 := bstep (se 1 (by rfl) ⟨1014836, by rfl⟩ : syracuseStep 1353115 = 2029673) B2029673
theorem B3614291 : Blo 948586 3614291 := bstep (se 1 (by rfl) ⟨2710718, by rfl⟩ : syracuseStep 3614291 = 5421437) B5421437
theorem B2401913 : Blo 948586 2401913 := bstep (se 2 (by rfl) ⟨900717, by rfl⟩ : syracuseStep 2401913 = 1801435) B1801435
theorem B2139983 : Blo 948586 2139983 := bstep (se 1 (by rfl) ⟨1604987, by rfl⟩ : syracuseStep 2139983 = 3209975) B3209975
theorem B2140001 : Blo 948586 2140001 := bstep (se 2 (by rfl) ⟨802500, by rfl⟩ : syracuseStep 2140001 = 1605001) B1605001
theorem B8136733 : Blo 948586 8136733 := bstep (se 3 (by rfl) ⟨1525637, by rfl⟩ : syracuseStep 8136733 = 3051275) B3051275
theorem B10266749 : Blo 948586 10266749 := bstep (se 3 (by rfl) ⟨1925015, by rfl⟩ : syracuseStep 10266749 = 3850031) B3850031
theorem B1714555 : Blo 948586 1714555 := bstep (se 1 (by rfl) ⟨1285916, by rfl⟩ : syracuseStep 1714555 = 2571833) B2571833
theorem B2140577 : Blo 948586 2140577 := bstep (se 2 (by rfl) ⟨802716, by rfl⟩ : syracuseStep 2140577 = 1605433) B1605433
theorem B5417381 : Blo 948586 5417381 := bstep (se 4 (by rfl) ⟨507879, by rfl⟩ : syracuseStep 5417381 = 1015759) B1015759
theorem B9775525 : Blo 948586 9775525 := bstep (se 4 (by rfl) ⟨916455, by rfl⟩ : syracuseStep 9775525 = 1832911) B1832911
theorem B2140703 : Blo 948586 2140703 := bstep (se 1 (by rfl) ⟨1605527, by rfl⟩ : syracuseStep 2140703 = 3211055) B3211055
theorem B1158047 : Blo 948586 1158047 := bstep (se 1 (by rfl) ⟨868535, by rfl⟩ : syracuseStep 1158047 = 1737071) B1737071
theorem B12332249 : Blo 948586 12332249 := bstep (se 2 (by rfl) ⟨4624593, by rfl⟩ : syracuseStep 12332249 = 9249187) B9249187
theorem B1355177 : Blo 948586 1355177 := bstep (se 2 (by rfl) ⟨508191, by rfl⟩ : syracuseStep 1355177 = 1016383) B1016383
theorem B5418521 : Blo 948586 5418521 := bstep (se 2 (by rfl) ⟨2031945, by rfl⟩ : syracuseStep 5418521 = 4063891) B4063891
theorem B2142107 : Blo 948586 2142107 := bstep (se 1 (by rfl) ⟨1606580, by rfl⟩ : syracuseStep 2142107 = 3213161) B3213161
theorem B9121841 : Blo 948586 9121841 := bstep (se 2 (by rfl) ⟨3420690, by rfl⟩ : syracuseStep 9121841 = 6841381) B6841381
theorem B2404475 : Blo 948586 2404475 := bstep (se 1 (by rfl) ⟨1803356, by rfl⟩ : syracuseStep 2404475 = 3606713) B3606713
theorem B2142395 : Blo 948586 2142395 := bstep (se 1 (by rfl) ⟨1606796, by rfl⟩ : syracuseStep 2142395 = 3213593) B3213593
theorem B2142881 : Blo 948586 2142881 := bstep (se 2 (by rfl) ⟨803580, by rfl⟩ : syracuseStep 2142881 = 1607161) B1607161
theorem B18297809 : Blo 948586 18297809 := bstep (se 2 (by rfl) ⟨6861678, by rfl⟩ : syracuseStep 18297809 = 13723357) B13723357
theorem B2143241 : Blo 948586 2143241 := bstep (se 2 (by rfl) ⟨803715, by rfl⟩ : syracuseStep 2143241 = 1607431) B1607431
theorem B30815275 : Blo 948586 30815275 := bstep (se 1 (by rfl) ⟨23111456, by rfl⟩ : syracuseStep 30815275 = 46222913) B46222913
theorem B2143295 : Blo 948586 2143295 := bstep (se 1 (by rfl) ⟨1607471, by rfl⟩ : syracuseStep 2143295 = 3214943) B3214943
theorem B1422959 : Blo 948586 1422959 := bstep (se 1 (by rfl) ⟨1067219, by rfl⟩ : syracuseStep 1422959 = 2134439) B2134439
theorem B1423031 : Blo 948586 1423031 := bstep (se 1 (by rfl) ⟨1067273, by rfl⟩ : syracuseStep 1423031 = 2134547) B2134547
theorem B5420753 : Blo 948586 5420753 := bstep (se 2 (by rfl) ⟨2032782, by rfl⟩ : syracuseStep 5420753 = 4065565) B4065565
theorem B1423067 : Blo 948586 1423067 := bstep (se 1 (by rfl) ⟨1067300, by rfl⟩ : syracuseStep 1423067 = 2134601) B2134601
theorem B1423241 : Blo 948586 1423241 := bstep (se 2 (by rfl) ⟨533715, by rfl⟩ : syracuseStep 1423241 = 1067431) B1067431
theorem B2471899 : Blo 948586 2471899 := bstep (se 1 (by rfl) ⟨1853924, by rfl⟩ : syracuseStep 2471899 = 3707849) B3707849
theorem B1423343 : Blo 948586 1423343 := bstep (se 1 (by rfl) ⟨1067507, by rfl⟩ : syracuseStep 1423343 = 2135015) B2135015
theorem B44546183 : Blo 948586 44546183 := bstep (se 1 (by rfl) ⟨33409637, by rfl⟩ : syracuseStep 44546183 = 66819275) B66819275
theorem B1423595 : Blo 948586 1423595 := bstep (se 1 (by rfl) ⟨1067696, by rfl⟩ : syracuseStep 1423595 = 2135393) B2135393
theorem B1423655 : Blo 948586 1423655 := bstep (se 1 (by rfl) ⟨1067741, by rfl⟩ : syracuseStep 1423655 = 2135483) B2135483
theorem B3422537 : Blo 948586 3422537 := bstep (se 2 (by rfl) ⟨1283451, by rfl⟩ : syracuseStep 3422537 = 2566903) B2566903
theorem B1423739 : Blo 948586 1423739 := bstep (se 1 (by rfl) ⟨1067804, by rfl⟩ : syracuseStep 1423739 = 2135609) B2135609
theorem B1424009 : Blo 948586 1424009 := bstep (se 2 (by rfl) ⟨534003, by rfl⟩ : syracuseStep 1424009 = 1068007) B1068007
theorem B2603677 : Blo 948586 2603677 := bstep (se 3 (by rfl) ⟨488189, by rfl⟩ : syracuseStep 2603677 = 976379) B976379
theorem B11123459 : Blo 948586 11123459 := bstep (se 1 (by rfl) ⟨8342594, by rfl⟩ : syracuseStep 11123459 = 16685189) B16685189
theorem B1424183 : Blo 948586 1424183 := bstep (se 1 (by rfl) ⟨1068137, by rfl⟩ : syracuseStep 1424183 = 2136275) B2136275
theorem B2407259 : Blo 948586 2407259 := bstep (se 1 (by rfl) ⟨1805444, by rfl⟩ : syracuseStep 2407259 = 3610889) B3610889
theorem B1424219 : Blo 948586 1424219 := bstep (se 1 (by rfl) ⟨1068164, by rfl⟩ : syracuseStep 1424219 = 2136329) B2136329
theorem B1424363 : Blo 948586 1424363 := bstep (se 1 (by rfl) ⟨1068272, by rfl⟩ : syracuseStep 1424363 = 2136545) B2136545
theorem B1522729 : Blo 948586 1522729 := bstep (se 2 (by rfl) ⟨571023, by rfl⟩ : syracuseStep 1522729 = 1142047) B1142047
theorem B1391737 : Blo 948586 1391737 := bstep (se 2 (by rfl) ⟨521901, by rfl⟩ : syracuseStep 1391737 = 1043803) B1043803
theorem B2407553 : Blo 948586 2407553 := bstep (se 2 (by rfl) ⟨902832, by rfl⟩ : syracuseStep 2407553 = 1805665) B1805665
theorem B1424567 : Blo 948586 1424567 := bstep (se 1 (by rfl) ⟨1068425, by rfl⟩ : syracuseStep 1424567 = 2136851) B2136851
theorem B150060221 : Blo 948586 150060221 := bstep (se 3 (by rfl) ⟨28136291, by rfl⟩ : syracuseStep 150060221 = 56272583) B56272583
theorem B2702585 : Blo 948586 2702585 := bstep (se 2 (by rfl) ⟨1013469, by rfl⟩ : syracuseStep 2702585 = 2026939) B2026939
theorem B1424807 : Blo 948586 1424807 := bstep (se 1 (by rfl) ⟨1068605, by rfl⟩ : syracuseStep 1424807 = 2137211) B2137211
theorem B1424891 : Blo 948586 1424891 := bstep (se 1 (by rfl) ⟨1068668, by rfl⟩ : syracuseStep 1424891 = 2137337) B2137337
theorem B65846789 : Blo 948586 65846789 := bstep (se 4 (by rfl) ⟨6173136, by rfl⟩ : syracuseStep 65846789 = 12346273) B12346273
theorem B2440783 : Blo 948586 2440783 := bstep (se 1 (by rfl) ⟨1830587, by rfl⟩ : syracuseStep 2440783 = 3661175) B3661175
theorem B1424987 : Blo 948586 1424987 := bstep (se 1 (by rfl) ⟨1068740, by rfl⟩ : syracuseStep 1424987 = 2137481) B2137481
theorem B1425071 : Blo 948586 1425071 := bstep (se 1 (by rfl) ⟨1068803, by rfl⟩ : syracuseStep 1425071 = 2137607) B2137607
theorem B1425191 : Blo 948586 1425191 := bstep (se 1 (by rfl) ⟨1068893, by rfl⟩ : syracuseStep 1425191 = 2137787) B2137787
theorem B1425275 : Blo 948586 1425275 := bstep (se 1 (by rfl) ⟨1068956, by rfl⟩ : syracuseStep 1425275 = 2137913) B2137913
theorem B2408363 : Blo 948586 2408363 := bstep (se 1 (by rfl) ⟨1806272, by rfl⟩ : syracuseStep 2408363 = 3612545) B3612545
theorem B5128271 : Blo 948586 5128271 := bstep (se 1 (by rfl) ⟨3846203, by rfl⟩ : syracuseStep 5128271 = 7692407) B7692407
theorem B11583719 : Blo 948586 11583719 := bstep (se 1 (by rfl) ⟨8687789, by rfl⟩ : syracuseStep 11583719 = 17375579) B17375579
theorem B1425695 : Blo 948586 1425695 := bstep (se 1 (by rfl) ⟨1069271, by rfl⟩ : syracuseStep 1425695 = 2138543) B2138543
theorem B1425719 : Blo 948586 1425719 := bstep (se 1 (by rfl) ⟨1069289, by rfl⟩ : syracuseStep 1425719 = 2138579) B2138579
theorem B1425791 : Blo 948586 1425791 := bstep (se 1 (by rfl) ⟨1069343, by rfl⟩ : syracuseStep 1425791 = 2138687) B2138687
theorem B1425863 : Blo 948586 1425863 := bstep (se 1 (by rfl) ⟨1069397, by rfl⟩ : syracuseStep 1425863 = 2138795) B2138795
theorem B1426217 : Blo 948586 1426217 := bstep (se 2 (by rfl) ⟨534831, by rfl⟩ : syracuseStep 1426217 = 1069663) B1069663
theorem B1426223 : Blo 948586 1426223 := bstep (se 1 (by rfl) ⟨1069667, by rfl⟩ : syracuseStep 1426223 = 2139335) B2139335
theorem B1426343 : Blo 948586 1426343 := bstep (se 1 (by rfl) ⟨1069757, by rfl⟩ : syracuseStep 1426343 = 2139515) B2139515
theorem B4637627 : Blo 948586 4637627 := bstep (se 1 (by rfl) ⟨3478220, by rfl⟩ : syracuseStep 4637627 = 6956441) B6956441
theorem B1426427 : Blo 948586 1426427 := bstep (se 1 (by rfl) ⟨1069820, by rfl⟩ : syracuseStep 1426427 = 2139641) B2139641
theorem B2409497 : Blo 948586 2409497 := bstep (se 2 (by rfl) ⟨903561, by rfl⟩ : syracuseStep 2409497 = 1807123) B1807123
theorem B1426487 : Blo 948586 1426487 := bstep (se 1 (by rfl) ⟨1069865, by rfl⟩ : syracuseStep 1426487 = 2139731) B2139731
theorem B7816297 : Blo 948586 7816297 := bstep (se 2 (by rfl) ⟨2931111, by rfl⟩ : syracuseStep 7816297 = 5862223) B5862223
theorem B1426607 : Blo 948586 1426607 := bstep (se 1 (by rfl) ⟨1069955, by rfl⟩ : syracuseStep 1426607 = 2139911) B2139911
theorem B30033341 : Blo 948586 30033341 := bstep (se 3 (by rfl) ⟨5631251, by rfl⟩ : syracuseStep 30033341 = 11262503) B11262503
theorem B6079997 : Blo 948586 6079997 := bstep (se 3 (by rfl) ⟨1139999, by rfl⟩ : syracuseStep 6079997 = 2279999) B2279999
theorem B1427015 : Blo 948586 1427015 := bstep (se 1 (by rfl) ⟨1070261, by rfl⟩ : syracuseStep 1427015 = 2140523) B2140523
theorem B1427111 : Blo 948586 1427111 := bstep (se 1 (by rfl) ⟨1070333, by rfl⟩ : syracuseStep 1427111 = 2140667) B2140667
theorem B1427195 : Blo 948586 1427195 := bstep (se 1 (by rfl) ⟨1070396, by rfl⟩ : syracuseStep 1427195 = 2140793) B2140793
theorem B2705183 : Blo 948586 2705183 := bstep (se 1 (by rfl) ⟨2028887, by rfl⟩ : syracuseStep 2705183 = 4057775) B4057775
theorem B1427231 : Blo 948586 1427231 := bstep (se 1 (by rfl) ⟨1070423, by rfl⟩ : syracuseStep 1427231 = 2140847) B2140847
theorem B26003243 : Blo 948586 26003243 := bstep (se 1 (by rfl) ⟨19502432, by rfl⟩ : syracuseStep 26003243 = 39004865) B39004865
theorem B1427279 : Blo 948586 1427279 := bstep (se 1 (by rfl) ⟨1070459, by rfl⟩ : syracuseStep 1427279 = 2140919) B2140919
theorem B2410337 : Blo 948586 2410337 := bstep (se 2 (by rfl) ⟨903876, by rfl⟩ : syracuseStep 2410337 = 1807753) B1807753
theorem B1427399 : Blo 948586 1427399 := bstep (se 1 (by rfl) ⟨1070549, by rfl⟩ : syracuseStep 1427399 = 2141099) B2141099
theorem B3393683 : Blo 948586 3393683 := bstep (se 1 (by rfl) ⟨2545262, by rfl⟩ : syracuseStep 3393683 = 5090525) B5090525
theorem B1427753 : Blo 948586 1427753 := bstep (se 2 (by rfl) ⟨535407, by rfl⟩ : syracuseStep 1427753 = 1070815) B1070815
theorem B1427759 : Blo 948586 1427759 := bstep (se 1 (by rfl) ⟨1070819, by rfl⟩ : syracuseStep 1427759 = 2141639) B2141639
theorem B1427999 : Blo 948586 1427999 := bstep (se 1 (by rfl) ⟨1070999, by rfl⟩ : syracuseStep 1427999 = 2141999) B2141999
theorem B69257915 : Blo 948586 69257915 := bstep (se 1 (by rfl) ⟨51943436, by rfl⟩ : syracuseStep 69257915 = 103886873) B103886873
theorem B1067935 : Blo 948586 1067935 := bstep (se 1 (by rfl) ⟨800951, by rfl⟩ : syracuseStep 1067935 = 1601903) B1601903
theorem B1428383 : Blo 948586 1428383 := bstep (se 1 (by rfl) ⟨1071287, by rfl⟩ : syracuseStep 1428383 = 2142575) B2142575
theorem B1428431 : Blo 948586 1428431 := bstep (se 1 (by rfl) ⟨1071323, by rfl⟩ : syracuseStep 1428431 = 2142647) B2142647
theorem B1428521 : Blo 948586 1428521 := bstep (se 2 (by rfl) ⟨535695, by rfl⟩ : syracuseStep 1428521 = 1071391) B1071391
theorem B1068079 : Blo 948586 1068079 := bstep (se 1 (by rfl) ⟨801059, by rfl⟩ : syracuseStep 1068079 = 1602119) B1602119
theorem B1428527 : Blo 948586 1428527 := bstep (se 1 (by rfl) ⟨1071395, by rfl⟩ : syracuseStep 1428527 = 2142791) B2142791
theorem B1428551 : Blo 948586 1428551 := bstep (se 1 (by rfl) ⟨1071413, by rfl⟩ : syracuseStep 1428551 = 2142827) B2142827
theorem B38948039 : Blo 948586 38948039 := bstep (se 1 (by rfl) ⟨29211029, by rfl⟩ : syracuseStep 38948039 = 58422059) B58422059
theorem B3656927 : Blo 948586 3656927 := bstep (se 1 (by rfl) ⟨2742695, by rfl⟩ : syracuseStep 3656927 = 5485391) B5485391
theorem B1068367 : Blo 948586 1068367 := bstep (se 1 (by rfl) ⟨801275, by rfl⟩ : syracuseStep 1068367 = 1602551) B1602551
theorem B2706767 : Blo 948586 2706767 := bstep (se 1 (by rfl) ⟨2030075, by rfl⟩ : syracuseStep 2706767 = 4060151) B4060151
theorem B1428815 : Blo 948586 1428815 := bstep (se 1 (by rfl) ⟨1071611, by rfl⟩ : syracuseStep 1428815 = 2143223) B2143223
theorem B4804271 : Blo 948586 4804271 := bstep (se 1 (by rfl) ⟨3603203, by rfl⟩ : syracuseStep 4804271 = 7206407) B7206407
theorem B2740007 : Blo 948586 2740007 := bstep (se 1 (by rfl) ⟨2055005, by rfl⟩ : syracuseStep 2740007 = 4110011) B4110011
theorem B1068871 : Blo 948586 1068871 := bstep (se 1 (by rfl) ⟨801653, by rfl⟩ : syracuseStep 1068871 = 1603307) B1603307
theorem B4804433 : Blo 948586 4804433 := bstep (se 2 (by rfl) ⟨1801662, by rfl⟩ : syracuseStep 4804433 = 3603325) B3603325
theorem B2707643 : Blo 948586 2707643 := bstep (se 1 (by rfl) ⟨2030732, by rfl⟩ : syracuseStep 2707643 = 4061465) B4061465
theorem B1069519 : Blo 948586 1069519 := bstep (se 1 (by rfl) ⟨802139, by rfl⟩ : syracuseStep 1069519 = 1604279) B1604279
theorem B4805243 : Blo 948586 4805243 := bstep (se 1 (by rfl) ⟨3603932, by rfl⟩ : syracuseStep 4805243 = 7207865) B7207865
theorem B1201007 : Blo 948586 1201007 := bstep (se 1 (by rfl) ⟨900755, by rfl⟩ : syracuseStep 1201007 = 1801511) B1801511
theorem B1201063 : Blo 948586 1201063 := bstep (se 1 (by rfl) ⟨900797, by rfl⟩ : syracuseStep 1201063 = 1801595) B1801595
theorem B3429371 : Blo 948586 3429371 := bstep (se 1 (by rfl) ⟨2572028, by rfl⟩ : syracuseStep 3429371 = 5144057) B5144057
theorem B13391243 : Blo 948586 13391243 := bstep (se 1 (by rfl) ⟨10043432, by rfl⟩ : syracuseStep 13391243 = 20086865) B20086865
theorem B1070491 : Blo 948586 1070491 := bstep (se 1 (by rfl) ⟨802868, by rfl⟩ : syracuseStep 1070491 = 1605737) B1605737
theorem B8115821 : Blo 948586 8115821 := bstep (se 3 (by rfl) ⟨1521716, by rfl⟩ : syracuseStep 8115821 = 3043433) B3043433
theorem B2283191 : Blo 948586 2283191 := bstep (se 1 (by rfl) ⟨1712393, by rfl⟩ : syracuseStep 2283191 = 3424787) B3424787
theorem B2709227 : Blo 948586 2709227 := bstep (se 1 (by rfl) ⟨2031920, by rfl⟩ : syracuseStep 2709227 = 4063841) B4063841
theorem B3168047 : Blo 948586 3168047 := bstep (se 1 (by rfl) ⟨2376035, by rfl⟩ : syracuseStep 3168047 = 4752071) B4752071
theorem B2283479 : Blo 948586 2283479 := bstep (se 1 (by rfl) ⟨1712609, by rfl⟩ : syracuseStep 2283479 = 3425219) B3425219
theorem B8116199 : Blo 948586 8116199 := bstep (se 1 (by rfl) ⟨6087149, by rfl⟩ : syracuseStep 8116199 = 12174299) B12174299
theorem B2742601 : Blo 948586 2742601 := bstep (se 2 (by rfl) ⟨1028475, by rfl⟩ : syracuseStep 2742601 = 2056951) B2056951
theorem B1071643 : Blo 948586 1071643 := bstep (se 1 (by rfl) ⟨803732, by rfl⟩ : syracuseStep 1071643 = 1607465) B1607465
theorem B3201875 : Blo 948586 3201875 := bstep (se 1 (by rfl) ⟨2401406, by rfl⟩ : syracuseStep 3201875 = 4802813) B4802813
theorem B1203103 : Blo 948586 1203103 := bstep (se 1 (by rfl) ⟨902327, by rfl⟩ : syracuseStep 1203103 = 1804655) B1804655
theorem B24665107 : Blo 948586 24665107 := bstep (se 1 (by rfl) ⟨18498830, by rfl⟩ : syracuseStep 24665107 = 36997661) B36997661
theorem B3202415 : Blo 948586 3202415 := bstep (se 1 (by rfl) ⟨2401811, by rfl⟩ : syracuseStep 3202415 = 4803623) B4803623
theorem B2711015 : Blo 948586 2711015 := bstep (se 1 (by rfl) ⟨2033261, by rfl⟩ : syracuseStep 2711015 = 4066523) B4066523
theorem B6086353 : Blo 948586 6086353 := bstep (se 2 (by rfl) ⟨2282382, by rfl⟩ : syracuseStep 6086353 = 4564765) B4564765
theorem B3202793 : Blo 948586 3202793 := bstep (se 2 (by rfl) ⟨1201047, by rfl⟩ : syracuseStep 3202793 = 2402095) B2402095
theorem B3760415 : Blo 948586 3760415 := bstep (se 1 (by rfl) ⟨2820311, by rfl⟩ : syracuseStep 3760415 = 5640623) B5640623
theorem B1237375 : Blo 948586 1237375 := bstep (se 1 (by rfl) ⟨928031, by rfl⟩ : syracuseStep 1237375 = 1856063) B1856063
theorem B3203657 : Blo 948586 3203657 := bstep (se 2 (by rfl) ⟨1201371, by rfl⟩ : syracuseStep 3203657 = 2402743) B2402743
theorem B3203819 : Blo 948586 3203819 := bstep (se 1 (by rfl) ⟨2402864, by rfl⟩ : syracuseStep 3203819 = 4805729) B4805729
theorem B4875065 : Blo 948586 4875065 := bstep (se 2 (by rfl) ⟨1828149, by rfl⟩ : syracuseStep 4875065 = 3656299) B3656299
theorem B12182957 : Blo 948586 12182957 := bstep (se 3 (by rfl) ⟨2284304, by rfl⟩ : syracuseStep 12182957 = 4568609) B4568609
theorem B2778617 : Blo 948586 2778617 := bstep (se 2 (by rfl) ⟨1041981, by rfl⟩ : syracuseStep 2778617 = 2083963) B2083963
theorem B27813719 : Blo 948586 27813719 := bstep (se 1 (by rfl) ⟨20860289, by rfl⟩ : syracuseStep 27813719 = 41720579) B41720579
theorem B3205331 : Blo 948586 3205331 := bstep (se 1 (by rfl) ⟨2403998, by rfl⟩ : syracuseStep 3205331 = 4807997) B4807997
theorem B2287919 : Blo 948586 2287919 := bstep (se 1 (by rfl) ⟨1715939, by rfl⟩ : syracuseStep 2287919 = 3431879) B3431879
theorem B3205601 : Blo 948586 3205601 := bstep (se 2 (by rfl) ⟨1202100, by rfl⟩ : syracuseStep 3205601 = 2404201) B2404201
theorem B6843055 : Blo 948586 6843055 := bstep (se 1 (by rfl) ⟨5132291, by rfl⟩ : syracuseStep 6843055 = 10264583) B10264583
theorem B24406919 : Blo 948586 24406919 := bstep (se 1 (by rfl) ⟨18305189, by rfl⟩ : syracuseStep 24406919 = 36610379) B36610379
theorem B20540749 : Blo 948586 20540749 := bstep (se 3 (by rfl) ⟨3851390, by rfl⟩ : syracuseStep 20540749 = 7702781) B7702781
theorem B3665533 : Blo 948586 3665533 := bstep (se 3 (by rfl) ⟨687287, by rfl⟩ : syracuseStep 3665533 = 1374575) B1374575
theorem B1601167 : Blo 948586 1601167 := bstep (se 1 (by rfl) ⟨1200875, by rfl⟩ : syracuseStep 1601167 = 2401751) B2401751
theorem B3206951 : Blo 948586 3206951 := bstep (se 1 (by rfl) ⟨2405213, by rfl⟩ : syracuseStep 3206951 = 4810427) B4810427
theorem B10284907 : Blo 948586 10284907 := bstep (se 1 (by rfl) ⟨7713680, by rfl⟩ : syracuseStep 10284907 = 15427361) B15427361
theorem B3043279 : Blo 948586 3043279 := bstep (se 1 (by rfl) ⟨2282459, by rfl⟩ : syracuseStep 3043279 = 4564919) B4564919
theorem B3207977 : Blo 948586 3207977 := bstep (se 2 (by rfl) ⟨1202991, by rfl⟩ : syracuseStep 3207977 = 2405983) B2405983
theorem B13726705 : Blo 948586 13726705 := bstep (se 2 (by rfl) ⟨5147514, by rfl⟩ : syracuseStep 13726705 = 10295029) B10295029
theorem B3044407 : Blo 948586 3044407 := bstep (se 1 (by rfl) ⟨2283305, by rfl⟩ : syracuseStep 3044407 = 4566611) B4566611
theorem B3208247 : Blo 948586 3208247 := bstep (se 1 (by rfl) ⟨2406185, by rfl⟩ : syracuseStep 3208247 = 4812371) B4812371
theorem B3044459 : Blo 948586 3044459 := bstep (se 1 (by rfl) ⟨2283344, by rfl⟩ : syracuseStep 3044459 = 4566689) B4566689
theorem B1602767 : Blo 948586 1602767 := bstep (se 1 (by rfl) ⟨1202075, by rfl⟩ : syracuseStep 1602767 = 2404151) B2404151
theorem B11138795 : Blo 948586 11138795 := bstep (se 1 (by rfl) ⟨8354096, by rfl⟩ : syracuseStep 11138795 = 16708193) B16708193
theorem B3602171 : Blo 948586 3602171 := bstep (se 1 (by rfl) ⟨2701628, by rfl⟩ : syracuseStep 3602171 = 5403257) B5403257
theorem B4814639 : Blo 948586 4814639 := bstep (se 1 (by rfl) ⟨3610979, by rfl⟩ : syracuseStep 4814639 = 7221959) B7221959
theorem B23754653 : Blo 948586 23754653 := bstep (se 3 (by rfl) ⟨4453997, by rfl⟩ : syracuseStep 23754653 = 8907995) B8907995
theorem B4061123 : Blo 948586 4061123 := bstep (se 1 (by rfl) ⟨3045842, by rfl⟩ : syracuseStep 4061123 = 6091685) B6091685
theorem B1013743 : Blo 948586 1013743 := bstep (se 1 (by rfl) ⟨760307, by rfl⟩ : syracuseStep 1013743 = 1520615) B1520615
theorem B1603577 : Blo 948586 1603577 := bstep (se 2 (by rfl) ⟨601341, by rfl⟩ : syracuseStep 1603577 = 1202683) B1202683
theorem B1603739 : Blo 948586 1603739 := bstep (se 1 (by rfl) ⟨1202804, by rfl⟩ : syracuseStep 1603739 = 2405609) B2405609
theorem B1603847 : Blo 948586 1603847 := bstep (se 1 (by rfl) ⟨1202885, by rfl⟩ : syracuseStep 1603847 = 2405771) B2405771
theorem B8124947 : Blo 948586 8124947 := bstep (se 1 (by rfl) ⟨6093710, by rfl⟩ : syracuseStep 8124947 = 12187421) B12187421
theorem B948763 : Blo 948586 948763 := bstep (se 1 (by rfl) ⟨711572, by rfl⟩ : syracuseStep 948763 = 1423145) B1423145
theorem B948767 : Blo 948586 948767 := bstep (se 1 (by rfl) ⟨711575, by rfl⟩ : syracuseStep 948767 = 1423151) B1423151
theorem B1604407 : Blo 948586 1604407 := bstep (se 1 (by rfl) ⟨1203305, by rfl⟩ : syracuseStep 1604407 = 2406611) B2406611
theorem B949083 : Blo 948586 949083 := bstep (se 1 (by rfl) ⟨711812, by rfl⟩ : syracuseStep 949083 = 1423625) B1423625
theorem B949151 : Blo 948586 949151 := bstep (se 1 (by rfl) ⟨711863, by rfl⟩ : syracuseStep 949151 = 1423727) B1423727
theorem B3210191 : Blo 948586 3210191 := bstep (se 1 (by rfl) ⟨2407643, by rfl⟩ : syracuseStep 3210191 = 4815287) B4815287
theorem B949295 : Blo 948586 949295 := bstep (se 1 (by rfl) ⟨711971, by rfl⟩ : syracuseStep 949295 = 1423943) B1423943
theorem B949319 : Blo 948586 949319 := bstep (se 1 (by rfl) ⟨711989, by rfl⟩ : syracuseStep 949319 = 1423979) B1423979
theorem B3013757 : Blo 948586 3013757 := bstep (se 3 (by rfl) ⟨565079, by rfl⟩ : syracuseStep 3013757 = 1130159) B1130159
theorem B949471 : Blo 948586 949471 := bstep (se 1 (by rfl) ⟨712103, by rfl⟩ : syracuseStep 949471 = 1424207) B1424207
theorem B1604873 : Blo 948586 1604873 := bstep (se 2 (by rfl) ⟨601827, by rfl⟩ : syracuseStep 1604873 = 1203655) B1203655
theorem B949735 : Blo 948586 949735 := bstep (se 1 (by rfl) ⟨712301, by rfl⟩ : syracuseStep 949735 = 1424603) B1424603
theorem B949851 : Blo 948586 949851 := bstep (se 1 (by rfl) ⟨712388, by rfl⟩ : syracuseStep 949851 = 1424777) B1424777
theorem B12156713 : Blo 948586 12156713 := bstep (se 2 (by rfl) ⟨4558767, by rfl⟩ : syracuseStep 12156713 = 9117535) B9117535
theorem B950087 : Blo 948586 950087 := bstep (se 1 (by rfl) ⟨712565, by rfl⟩ : syracuseStep 950087 = 1425131) B1425131
theorem B950239 : Blo 948586 950239 := bstep (se 1 (by rfl) ⟨712679, by rfl⟩ : syracuseStep 950239 = 1425359) B1425359
theorem B950463 : Blo 948586 950463 := bstep (se 1 (by rfl) ⟨712847, by rfl⟩ : syracuseStep 950463 = 1425695) B1425695
theorem B950479 : Blo 948586 950479 := bstep (se 1 (by rfl) ⟨712859, by rfl⟩ : syracuseStep 950479 = 1425719) B1425719
theorem B950527 : Blo 948586 950527 := bstep (se 1 (by rfl) ⟨712895, by rfl⟩ : syracuseStep 950527 = 1425791) B1425791
theorem B3604783 : Blo 948586 3604783 := bstep (se 1 (by rfl) ⟨2703587, by rfl⟩ : syracuseStep 3604783 = 5407175) B5407175
theorem B950575 : Blo 948586 950575 := bstep (se 1 (by rfl) ⟨712931, by rfl⟩ : syracuseStep 950575 = 1425863) B1425863
theorem B7209323 : Blo 948586 7209323 := bstep (se 1 (by rfl) ⟨5406992, by rfl⟩ : syracuseStep 7209323 = 10813985) B10813985
theorem B950811 : Blo 948586 950811 := bstep (se 1 (by rfl) ⟨713108, by rfl⟩ : syracuseStep 950811 = 1426217) B1426217
theorem B950815 : Blo 948586 950815 := bstep (se 1 (by rfl) ⟨713111, by rfl⟩ : syracuseStep 950815 = 1426223) B1426223
theorem B3605087 : Blo 948586 3605087 := bstep (se 1 (by rfl) ⟨2703815, by rfl⟩ : syracuseStep 3605087 = 5407631) B5407631
theorem B950895 : Blo 948586 950895 := bstep (se 1 (by rfl) ⟨713171, by rfl⟩ : syracuseStep 950895 = 1426343) B1426343
theorem B950951 : Blo 948586 950951 := bstep (se 1 (by rfl) ⟨713213, by rfl⟩ : syracuseStep 950951 = 1426427) B1426427
theorem B1606331 : Blo 948586 1606331 := bstep (se 1 (by rfl) ⟨1204748, by rfl⟩ : syracuseStep 1606331 = 2409497) B2409497
theorem B950991 : Blo 948586 950991 := bstep (se 1 (by rfl) ⟨713243, by rfl⟩ : syracuseStep 950991 = 1426487) B1426487
theorem B951071 : Blo 948586 951071 := bstep (se 1 (by rfl) ⟨713303, by rfl⟩ : syracuseStep 951071 = 1426607) B1426607
theorem B16253783 : Blo 948586 16253783 := bstep (se 1 (by rfl) ⟨12190337, by rfl⟩ : syracuseStep 16253783 = 24380675) B24380675
theorem B20022227 : Blo 948586 20022227 := bstep (se 1 (by rfl) ⟨15016670, by rfl⟩ : syracuseStep 20022227 = 30033341) B30033341
theorem B951343 : Blo 948586 951343 := bstep (se 1 (by rfl) ⟨713507, by rfl⟩ : syracuseStep 951343 = 1427015) B1427015
theorem B3212351 : Blo 948586 3212351 := bstep (se 1 (by rfl) ⟨2409263, by rfl⟩ : syracuseStep 3212351 = 4818527) B4818527
theorem B951407 : Blo 948586 951407 := bstep (se 1 (by rfl) ⟨713555, by rfl⟩ : syracuseStep 951407 = 1427111) B1427111
theorem B951463 : Blo 948586 951463 := bstep (se 1 (by rfl) ⟨713597, by rfl⟩ : syracuseStep 951463 = 1427195) B1427195
theorem B1803455 : Blo 948586 1803455 := bstep (se 1 (by rfl) ⟨1352591, by rfl⟩ : syracuseStep 1803455 = 2705183) B2705183
theorem B951487 : Blo 948586 951487 := bstep (se 1 (by rfl) ⟨713615, by rfl⟩ : syracuseStep 951487 = 1427231) B1427231
theorem B17335495 : Blo 948586 17335495 := bstep (se 1 (by rfl) ⟨13001621, by rfl⟩ : syracuseStep 17335495 = 26003243) B26003243
theorem B951519 : Blo 948586 951519 := bstep (se 1 (by rfl) ⟨713639, by rfl⟩ : syracuseStep 951519 = 1427279) B1427279
theorem B1606891 : Blo 948586 1606891 := bstep (se 1 (by rfl) ⟨1205168, by rfl⟩ : syracuseStep 1606891 = 2410337) B2410337
theorem B951599 : Blo 948586 951599 := bstep (se 1 (by rfl) ⟨713699, by rfl⟩ : syracuseStep 951599 = 1427399) B1427399
theorem B2262455 : Blo 948586 2262455 := bstep (se 1 (by rfl) ⟨1696841, by rfl⟩ : syracuseStep 2262455 = 3393683) B3393683
theorem B10421729 : Blo 948586 10421729 := bstep (se 2 (by rfl) ⟨3908148, by rfl⟩ : syracuseStep 10421729 = 7816297) B7816297
theorem B951835 : Blo 948586 951835 := bstep (se 1 (by rfl) ⟨713876, by rfl⟩ : syracuseStep 951835 = 1427753) B1427753
theorem B951839 : Blo 948586 951839 := bstep (se 1 (by rfl) ⟨713879, by rfl⟩ : syracuseStep 951839 = 1427759) B1427759
theorem B4064849 : Blo 948586 4064849 := bstep (se 2 (by rfl) ⟨1524318, by rfl⟩ : syracuseStep 4064849 = 3048637) B3048637
theorem B951999 : Blo 948586 951999 := bstep (se 1 (by rfl) ⟨713999, by rfl⟩ : syracuseStep 951999 = 1427999) B1427999
theorem B46171943 : Blo 948586 46171943 := bstep (se 1 (by rfl) ⟨34628957, by rfl⟩ : syracuseStep 46171943 = 69257915) B69257915
theorem B952255 : Blo 948586 952255 := bstep (se 1 (by rfl) ⟨714191, by rfl⟩ : syracuseStep 952255 = 1428383) B1428383
theorem B952287 : Blo 948586 952287 := bstep (se 1 (by rfl) ⟨714215, by rfl⟩ : syracuseStep 952287 = 1428431) B1428431
theorem B952347 : Blo 948586 952347 := bstep (se 1 (by rfl) ⟨714260, by rfl⟩ : syracuseStep 952347 = 1428521) B1428521
theorem B952351 : Blo 948586 952351 := bstep (se 1 (by rfl) ⟨714263, by rfl⟩ : syracuseStep 952351 = 1428527) B1428527
theorem B952367 : Blo 948586 952367 := bstep (se 1 (by rfl) ⟨714275, by rfl⟩ : syracuseStep 952367 = 1428551) B1428551
theorem B1804511 : Blo 948586 1804511 := bstep (se 1 (by rfl) ⟨1353383, by rfl⟩ : syracuseStep 1804511 = 2706767) B2706767
theorem B952543 : Blo 948586 952543 := bstep (se 1 (by rfl) ⟨714407, by rfl⟩ : syracuseStep 952543 = 1428815) B1428815
theorem B2034047 : Blo 948586 2034047 := bstep (se 1 (by rfl) ⟨1525535, by rfl⟩ : syracuseStep 2034047 = 3051071) B3051071
theorem B10848977 : Blo 948586 10848977 := bstep (se 2 (by rfl) ⟨4068366, by rfl⟩ : syracuseStep 10848977 = 8136733) B8136733
theorem B1805095 : Blo 948586 1805095 := bstep (se 1 (by rfl) ⟨1353821, by rfl⟩ : syracuseStep 1805095 = 2707643) B2707643
theorem B4328275 : Blo 948586 4328275 := bstep (se 1 (by rfl) ⟨3246206, by rfl⟩ : syracuseStep 4328275 = 6492413) B6492413
theorem B5410547 : Blo 948586 5410547 := bstep (se 1 (by rfl) ⟨4057910, by rfl⟩ : syracuseStep 5410547 = 8115821) B8115821
theorem B1806151 : Blo 948586 1806151 := bstep (se 1 (by rfl) ⟨1354613, by rfl⟩ : syracuseStep 1806151 = 2709227) B2709227
theorem B13700987 : Blo 948586 13700987 := bstep (se 1 (by rfl) ⟨10275740, by rfl⟩ : syracuseStep 13700987 = 20551481) B20551481
theorem B5410799 : Blo 948586 5410799 := bstep (se 1 (by rfl) ⟨4058099, by rfl⟩ : syracuseStep 5410799 = 8116199) B8116199
theorem B2134583 : Blo 948586 2134583 := bstep (se 1 (by rfl) ⟨1600937, by rfl⟩ : syracuseStep 2134583 = 3201875) B3201875
theorem B3609143 : Blo 948586 3609143 := bstep (se 1 (by rfl) ⟨2706857, by rfl⟩ : syracuseStep 3609143 = 5413715) B5413715
theorem B4887377 : Blo 948586 4887377 := bstep (se 2 (by rfl) ⟨1832766, by rfl⟩ : syracuseStep 4887377 = 3665533) B3665533
theorem B2134889 : Blo 948586 2134889 := bstep (se 2 (by rfl) ⟨800583, by rfl⟩ : syracuseStep 2134889 = 1601167) B1601167
theorem B2134943 : Blo 948586 2134943 := bstep (se 1 (by rfl) ⟨1601207, by rfl⟩ : syracuseStep 2134943 = 3202415) B3202415
theorem B1807343 : Blo 948586 1807343 := bstep (se 1 (by rfl) ⟨1355507, by rfl⟩ : syracuseStep 1807343 = 2711015) B2711015
theorem B2135195 : Blo 948586 2135195 := bstep (se 1 (by rfl) ⟨1601396, by rfl⟩ : syracuseStep 2135195 = 3202793) B3202793
theorem B2135771 : Blo 948586 2135771 := bstep (se 1 (by rfl) ⟨1601828, by rfl⟩ : syracuseStep 2135771 = 3203657) B3203657
theorem B2135879 : Blo 948586 2135879 := bstep (se 1 (by rfl) ⟨1601909, by rfl⟩ : syracuseStep 2135879 = 3203819) B3203819
theorem B3250043 : Blo 948586 3250043 := bstep (se 1 (by rfl) ⟨2437532, by rfl⟩ : syracuseStep 3250043 = 4875065) B4875065
theorem B3610615 : Blo 948586 3610615 := bstep (se 1 (by rfl) ⟨2707961, by rfl⟩ : syracuseStep 3610615 = 5415923) B5415923
theorem B2136887 : Blo 948586 2136887 := bstep (se 1 (by rfl) ⟨1602665, by rfl⟩ : syracuseStep 2136887 = 3205331) B3205331
theorem B3611587 : Blo 948586 3611587 := bstep (se 1 (by rfl) ⟨2708690, by rfl⟩ : syracuseStep 3611587 = 5417381) B5417381
theorem B2137067 : Blo 948586 2137067 := bstep (se 1 (by rfl) ⟨1602800, by rfl⟩ : syracuseStep 2137067 = 3205601) B3205601
theorem B7216613 : Blo 948586 7216613 := bstep (se 4 (by rfl) ⟨676557, by rfl⟩ : syracuseStep 7216613 = 1353115) B1353115
theorem B3612347 : Blo 948586 3612347 := bstep (se 1 (by rfl) ⟨2709260, by rfl⟩ : syracuseStep 3612347 = 5418521) B5418521
theorem B2137967 : Blo 948586 2137967 := bstep (se 1 (by rfl) ⟨1603475, by rfl⟩ : syracuseStep 2137967 = 3206951) B3206951
theorem B1351657 : Blo 948586 1351657 := bstep (se 2 (by rfl) ⟨506871, by rfl⟩ : syracuseStep 1351657 = 1013743) B1013743
theorem B2138651 : Blo 948586 2138651 := bstep (se 1 (by rfl) ⟨1603988, by rfl⟩ : syracuseStep 2138651 = 3207977) B3207977
theorem B12198539 : Blo 948586 12198539 := bstep (se 1 (by rfl) ⟨9148904, by rfl⟩ : syracuseStep 12198539 = 18297809) B18297809
theorem B2138831 : Blo 948586 2138831 := bstep (se 1 (by rfl) ⟨1604123, by rfl⟩ : syracuseStep 2138831 = 3208247) B3208247
theorem B2139209 : Blo 948586 2139209 := bstep (se 2 (by rfl) ⟨802203, by rfl⟩ : syracuseStep 2139209 = 1604407) B1604407
theorem B3613805 : Blo 948586 3613805 := bstep (se 3 (by rfl) ⟨677588, by rfl⟩ : syracuseStep 3613805 = 1355177) B1355177
theorem B5776505 : Blo 948586 5776505 := bstep (se 2 (by rfl) ⟨2166189, by rfl⟩ : syracuseStep 5776505 = 4332379) B4332379
theorem B3613835 : Blo 948586 3613835 := bstep (se 1 (by rfl) ⟨2710376, by rfl⟩ : syracuseStep 3613835 = 5420753) B5420753
theorem B2401447 : Blo 948586 2401447 := bstep (se 1 (by rfl) ⟨1801085, by rfl⟩ : syracuseStep 2401447 = 3602171) B3602171
theorem B15836435 : Blo 948586 15836435 := bstep (se 1 (by rfl) ⟨11877326, by rfl⟩ : syracuseStep 15836435 = 23754653) B23754653
theorem B29697455 : Blo 948586 29697455 := bstep (se 1 (by rfl) ⟨22273091, by rfl⟩ : syracuseStep 29697455 = 44546183) B44546183
theorem B5416631 : Blo 948586 5416631 := bstep (se 1 (by rfl) ⟨4062473, by rfl⟩ : syracuseStep 5416631 = 8124947) B8124947
theorem B7415639 : Blo 948586 7415639 := bstep (se 1 (by rfl) ⟨5561729, by rfl⟩ : syracuseStep 7415639 = 11123459) B11123459
theorem B2140127 : Blo 948586 2140127 := bstep (se 1 (by rfl) ⟨1605095, by rfl⟩ : syracuseStep 2140127 = 3210191) B3210191
theorem B2009171 : Blo 948586 2009171 := bstep (se 1 (by rfl) ⟨1506878, by rfl⟩ : syracuseStep 2009171 = 3013757) B3013757
theorem B3254377 : Blo 948586 3254377 := bstep (se 2 (by rfl) ⟨1220391, by rfl⟩ : syracuseStep 3254377 = 2440783) B2440783
theorem B8104475 : Blo 948586 8104475 := bstep (se 1 (by rfl) ⟨6078356, by rfl⟩ : syracuseStep 8104475 = 12156713) B12156713
theorem B4631255 : Blo 948586 4631255 := bstep (se 1 (by rfl) ⟨3473441, by rfl⟩ : syracuseStep 4631255 = 6946883) B6946883
theorem B3418847 : Blo 948586 3418847 := bstep (se 1 (by rfl) ⟨2564135, by rfl⟩ : syracuseStep 3418847 = 5128271) B5128271
theorem B11578115 : Blo 948586 11578115 := bstep (se 1 (by rfl) ⟨8683586, by rfl⟩ : syracuseStep 11578115 = 17367173) B17367173
theorem B1157927 : Blo 948586 1157927 := bstep (se 1 (by rfl) ⟨868445, by rfl⟩ : syracuseStep 1157927 = 1736891) B1736891
theorem B2141135 : Blo 948586 2141135 := bstep (se 1 (by rfl) ⟨1605851, by rfl⟩ : syracuseStep 2141135 = 3211703) B3211703
theorem B2141225 : Blo 948586 2141225 := bstep (se 2 (by rfl) ⟨802959, by rfl⟩ : syracuseStep 2141225 = 1605919) B1605919
theorem B2141459 : Blo 948586 2141459 := bstep (se 1 (by rfl) ⟨1606094, by rfl⟩ : syracuseStep 2141459 = 3212189) B3212189
theorem B3091751 : Blo 948586 3091751 := bstep (se 1 (by rfl) ⟨2318813, by rfl⟩ : syracuseStep 3091751 = 4637627) B4637627
theorem B2141495 : Blo 948586 2141495 := bstep (se 1 (by rfl) ⟨1606121, by rfl⟩ : syracuseStep 2141495 = 3212243) B3212243
theorem B2142089 : Blo 948586 2142089 := bstep (se 2 (by rfl) ⟨803283, by rfl⟩ : syracuseStep 2142089 = 1606567) B1606567
theorem B36974593 : Blo 948586 36974593 := bstep (se 2 (by rfl) ⟨13865472, by rfl⟩ : syracuseStep 36974593 = 27730945) B27730945
theorem B2142305 : Blo 948586 2142305 := bstep (se 2 (by rfl) ⟨803364, by rfl⟩ : syracuseStep 2142305 = 1606729) B1606729
theorem B9154903 : Blo 948586 9154903 := bstep (se 1 (by rfl) ⟨6866177, by rfl⟩ : syracuseStep 9154903 = 13732355) B13732355
theorem B34648505 : Blo 948586 34648505 := bstep (se 2 (by rfl) ⟨12993189, by rfl⟩ : syracuseStep 34648505 = 25986379) B25986379
theorem B12169835 : Blo 948586 12169835 := bstep (se 1 (by rfl) ⟨9127376, by rfl⟩ : syracuseStep 12169835 = 18254753) B18254753
theorem B6599333 : Blo 948586 6599333 := bstep (se 4 (by rfl) ⟨618687, by rfl⟩ : syracuseStep 6599333 = 1237375) B1237375
theorem B2142971 : Blo 948586 2142971 := bstep (se 1 (by rfl) ⟨1607228, by rfl⟩ : syracuseStep 2142971 = 3214457) B3214457
theorem B25965359 : Blo 948586 25965359 := bstep (se 1 (by rfl) ⟨19474019, by rfl⟩ : syracuseStep 25965359 = 38948039) B38948039
theorem B2437951 : Blo 948586 2437951 := bstep (se 1 (by rfl) ⟨1828463, by rfl⟩ : syracuseStep 2437951 = 3656927) B3656927
theorem B2143187 : Blo 948586 2143187 := bstep (se 1 (by rfl) ⟨1607390, by rfl⟩ : syracuseStep 2143187 = 3214781) B3214781
theorem B2405447 : Blo 948586 2405447 := bstep (se 1 (by rfl) ⟨1804085, by rfl⟩ : syracuseStep 2405447 = 3608171) B3608171
theorem B5420297 : Blo 948586 5420297 := bstep (se 2 (by rfl) ⟨2032611, by rfl⟩ : syracuseStep 5420297 = 4065223) B4065223
theorem B8107451 : Blo 948586 8107451 := bstep (se 1 (by rfl) ⟨6080588, by rfl⟩ : syracuseStep 8107451 = 12161177) B12161177
theorem B2406631 : Blo 948586 2406631 := bstep (se 1 (by rfl) ⟨1804973, by rfl⟩ : syracuseStep 2406631 = 3609947) B3609947
theorem B9124073 : Blo 948586 9124073 := bstep (se 2 (by rfl) ⟨3421527, by rfl⟩ : syracuseStep 9124073 = 6843055) B6843055
theorem B8927495 : Blo 948586 8927495 := bstep (se 1 (by rfl) ⟨6695621, by rfl⟩ : syracuseStep 8927495 = 13391243) B13391243
theorem B1423823 : Blo 948586 1423823 := bstep (se 1 (by rfl) ⟨1067867, by rfl⟩ : syracuseStep 1423823 = 2135735) B2135735
theorem B1522127 : Blo 948586 1522127 := bstep (se 1 (by rfl) ⟨1141595, by rfl⟩ : syracuseStep 1522127 = 2283191) B2283191
theorem B2112031 : Blo 948586 2112031 := bstep (se 1 (by rfl) ⟨1584023, by rfl⟩ : syracuseStep 2112031 = 3168047) B3168047
theorem B1423913 : Blo 948586 1423913 := bstep (se 2 (by rfl) ⟨533967, by rfl⟩ : syracuseStep 1423913 = 1067935) B1067935
theorem B1522319 : Blo 948586 1522319 := bstep (se 1 (by rfl) ⟨1141739, by rfl⟩ : syracuseStep 1522319 = 2283479) B2283479
theorem B5421755 : Blo 948586 5421755 := bstep (se 1 (by rfl) ⟨4066316, by rfl⟩ : syracuseStep 5421755 = 8132633) B8132633
theorem B1424105 : Blo 948586 1424105 := bstep (se 2 (by rfl) ⟨534039, by rfl⟩ : syracuseStep 1424105 = 1068079) B1068079
theorem B1424489 : Blo 948586 1424489 := bstep (se 2 (by rfl) ⟨534183, by rfl⟩ : syracuseStep 1424489 = 1068367) B1068367
theorem B1424615 : Blo 948586 1424615 := bstep (se 1 (by rfl) ⟨1068461, by rfl⟩ : syracuseStep 1424615 = 2136923) B2136923
theorem B6602303 : Blo 948586 6602303 := bstep (se 1 (by rfl) ⟨4951727, by rfl⟩ : syracuseStep 6602303 = 9903455) B9903455
theorem B1425119 : Blo 948586 1425119 := bstep (se 1 (by rfl) ⟨1068839, by rfl⟩ : syracuseStep 1425119 = 2137679) B2137679
theorem B1425161 : Blo 948586 1425161 := bstep (se 2 (by rfl) ⟨534435, by rfl⟩ : syracuseStep 1425161 = 1068871) B1068871
theorem B13713209 : Blo 948586 13713209 := bstep (se 2 (by rfl) ⟨5142453, by rfl⟩ : syracuseStep 13713209 = 10284907) B10284907
theorem B1425599 : Blo 948586 1425599 := bstep (se 1 (by rfl) ⟨1069199, by rfl⟩ : syracuseStep 1425599 = 2138399) B2138399
theorem B2506943 : Blo 948586 2506943 := bstep (se 1 (by rfl) ⟨1880207, by rfl⟩ : syracuseStep 2506943 = 3760415) B3760415
theorem B1426025 : Blo 948586 1426025 := bstep (se 2 (by rfl) ⟨534759, by rfl⟩ : syracuseStep 1426025 = 1069519) B1069519
theorem B1426031 : Blo 948586 1426031 := bstep (se 1 (by rfl) ⟨1069523, by rfl⟩ : syracuseStep 1426031 = 2139047) B2139047
theorem B9126533 : Blo 948586 9126533 := bstep (se 4 (by rfl) ⟨855612, by rfl⟩ : syracuseStep 9126533 = 1711225) B1711225
theorem B1852411 : Blo 948586 1852411 := bstep (se 1 (by rfl) ⟨1389308, by rfl⟩ : syracuseStep 1852411 = 2778617) B2778617
theorem B3851297 : Blo 948586 3851297 := bstep (se 2 (by rfl) ⟨1444236, by rfl⟩ : syracuseStep 3851297 = 2888473) B2888473
theorem B2409527 : Blo 948586 2409527 := bstep (se 1 (by rfl) ⟨1807145, by rfl⟩ : syracuseStep 2409527 = 3614291) B3614291
theorem B1426655 : Blo 948586 1426655 := bstep (se 1 (by rfl) ⟨1069991, by rfl⟩ : syracuseStep 1426655 = 2139983) B2139983
theorem B1426667 : Blo 948586 1426667 := bstep (se 1 (by rfl) ⟨1070000, by rfl⟩ : syracuseStep 1426667 = 2140001) B2140001
theorem B18302273 : Blo 948586 18302273 := bstep (se 2 (by rfl) ⟨6863352, by rfl⟩ : syracuseStep 18302273 = 13726705) B13726705
theorem B1525279 : Blo 948586 1525279 := bstep (se 1 (by rfl) ⟨1143959, by rfl⟩ : syracuseStep 1525279 = 2287919) B2287919
theorem B1427051 : Blo 948586 1427051 := bstep (se 1 (by rfl) ⟨1070288, by rfl⟩ : syracuseStep 1427051 = 2140577) B2140577
theorem B1427135 : Blo 948586 1427135 := bstep (se 1 (by rfl) ⟨1070351, by rfl⟩ : syracuseStep 1427135 = 2140703) B2140703
theorem B1427321 : Blo 948586 1427321 := bstep (se 2 (by rfl) ⟨535245, by rfl⟩ : syracuseStep 1427321 = 1070491) B1070491
theorem B16271279 : Blo 948586 16271279 := bstep (se 1 (by rfl) ⟨12203459, by rfl⟩ : syracuseStep 16271279 = 24406919) B24406919
theorem B59426873 : Blo 948586 59426873 := bstep (se 2 (by rfl) ⟨22285077, by rfl⟩ : syracuseStep 59426873 = 44570155) B44570155
theorem B1428071 : Blo 948586 1428071 := bstep (se 1 (by rfl) ⟨1071053, by rfl⟩ : syracuseStep 1428071 = 2142107) B2142107
theorem B3295865 : Blo 948586 3295865 := bstep (se 2 (by rfl) ⟨1235949, by rfl⟩ : syracuseStep 3295865 = 2471899) B2471899
theorem B6081227 : Blo 948586 6081227 := bstep (se 1 (by rfl) ⟨4560920, by rfl⟩ : syracuseStep 6081227 = 9121841) B9121841
theorem B1428263 : Blo 948586 1428263 := bstep (se 1 (by rfl) ⟨1071197, by rfl⟩ : syracuseStep 1428263 = 2142395) B2142395
theorem B3656801 : Blo 948586 3656801 := bstep (se 2 (by rfl) ⟨1371300, by rfl⟩ : syracuseStep 3656801 = 2742601) B2742601
theorem B1428587 : Blo 948586 1428587 := bstep (se 1 (by rfl) ⟨1071440, by rfl⟩ : syracuseStep 1428587 = 2142881) B2142881
theorem B1428827 : Blo 948586 1428827 := bstep (se 1 (by rfl) ⟨1071620, by rfl⟩ : syracuseStep 1428827 = 2143241) B2143241
theorem B1428857 : Blo 948586 1428857 := bstep (se 2 (by rfl) ⟨535821, by rfl⟩ : syracuseStep 1428857 = 1071643) B1071643
theorem B1428863 : Blo 948586 1428863 := bstep (se 1 (by rfl) ⟨1071647, by rfl⟩ : syracuseStep 1428863 = 2143295) B2143295
theorem B1068511 : Blo 948586 1068511 := bstep (se 1 (by rfl) ⟨801383, by rfl⟩ : syracuseStep 1068511 = 1602767) B1602767
theorem B7425863 : Blo 948586 7425863 := bstep (se 1 (by rfl) ⟨5569397, by rfl⟩ : syracuseStep 7425863 = 11138795) B11138795
theorem B2707415 : Blo 948586 2707415 := bstep (se 1 (by rfl) ⟨2030561, by rfl⟩ : syracuseStep 2707415 = 4061123) B4061123
theorem B1069051 : Blo 948586 1069051 := bstep (se 1 (by rfl) ⟨801788, by rfl⟩ : syracuseStep 1069051 = 1603577) B1603577
theorem B32886809 : Blo 948586 32886809 := bstep (se 2 (by rfl) ⟨12332553, by rfl⟩ : syracuseStep 32886809 = 24665107) B24665107
theorem B1069159 : Blo 948586 1069159 := bstep (se 1 (by rfl) ⟨801869, by rfl⟩ : syracuseStep 1069159 = 1603739) B1603739
theorem B1855649 : Blo 948586 1855649 := bstep (se 2 (by rfl) ⟨695868, by rfl⟩ : syracuseStep 1855649 = 1391737) B1391737
theorem B1069231 : Blo 948586 1069231 := bstep (se 1 (by rfl) ⟨801923, by rfl⟩ : syracuseStep 1069231 = 1603847) B1603847
theorem B2281691 : Blo 948586 2281691 := bstep (se 1 (by rfl) ⟨1711268, by rfl⟩ : syracuseStep 2281691 = 3422537) B3422537
theorem B1069915 : Blo 948586 1069915 := bstep (se 1 (by rfl) ⟨802436, by rfl⟩ : syracuseStep 1069915 = 1604873) B1604873
theorem B8115137 : Blo 948586 8115137 := bstep (se 2 (by rfl) ⟨3043176, by rfl⟩ : syracuseStep 8115137 = 6086353) B6086353
theorem B43897859 : Blo 948586 43897859 := bstep (se 1 (by rfl) ⟨32923394, by rfl⟩ : syracuseStep 43897859 = 65846789) B65846789
theorem B2708873 : Blo 948586 2708873 := bstep (se 2 (by rfl) ⟨1015827, by rfl⟩ : syracuseStep 2708873 = 2031655) B2031655
theorem B7722479 : Blo 948586 7722479 := bstep (se 1 (by rfl) ⟨5791859, by rfl⟩ : syracuseStep 7722479 = 11583719) B11583719
theorem B1071175 : Blo 948586 1071175 := bstep (se 1 (by rfl) ⟨803381, by rfl⟩ : syracuseStep 1071175 = 1606763) B1606763
theorem B4053331 : Blo 948586 4053331 := bstep (se 1 (by rfl) ⟨3039998, by rfl⟩ : syracuseStep 4053331 = 6079997) B6079997
theorem B46815671 : Blo 948586 46815671 := bstep (se 1 (by rfl) ⟨35111753, by rfl⟩ : syracuseStep 46815671 = 70223507) B70223507
theorem B4807187 : Blo 948586 4807187 := bstep (se 1 (by rfl) ⟨3605390, by rfl⟩ : syracuseStep 4807187 = 7210781) B7210781
theorem B2054683 : Blo 948586 2054683 := bstep (se 1 (by rfl) ⟨1541012, by rfl⟩ : syracuseStep 2054683 = 3082025) B3082025
theorem B16472915 : Blo 948586 16472915 := bstep (se 1 (by rfl) ⟨12354686, by rfl⟩ : syracuseStep 16472915 = 24709373) B24709373
theorem B3202145 : Blo 948586 3202145 := bstep (se 2 (by rfl) ⟨1200804, by rfl⟩ : syracuseStep 3202145 = 2401609) B2401609
theorem B3202685 : Blo 948586 3202685 := bstep (se 3 (by rfl) ⟨600503, by rfl⟩ : syracuseStep 3202685 = 1201007) B1201007
theorem B9264851 : Blo 948586 9264851 := bstep (se 1 (by rfl) ⟨6948638, by rfl⟩ : syracuseStep 9264851 = 13897277) B13897277
theorem B3202847 : Blo 948586 3202847 := bstep (se 1 (by rfl) ⟨2402135, by rfl⟩ : syracuseStep 3202847 = 4804271) B4804271
theorem B1924975 : Blo 948586 1924975 := bstep (se 1 (by rfl) ⟨1443731, by rfl⟩ : syracuseStep 1924975 = 2887463) B2887463
theorem B3202955 : Blo 948586 3202955 := bstep (se 1 (by rfl) ⟨2402216, by rfl⟩ : syracuseStep 3202955 = 4804433) B4804433
theorem B3203495 : Blo 948586 3203495 := bstep (se 1 (by rfl) ⟨2402621, by rfl⟩ : syracuseStep 3203495 = 4805243) B4805243
theorem B2286073 : Blo 948586 2286073 := bstep (se 2 (by rfl) ⟨857277, by rfl⟩ : syracuseStep 2286073 = 1714555) B1714555
theorem B13034033 : Blo 948586 13034033 := bstep (se 2 (by rfl) ⟨4887762, by rfl⟩ : syracuseStep 13034033 = 9775525) B9775525
theorem B2286247 : Blo 948586 2286247 := bstep (se 1 (by rfl) ⟨1714685, by rfl⟩ : syracuseStep 2286247 = 3429371) B3429371
theorem B27387665 : Blo 948586 27387665 := bstep (se 2 (by rfl) ⟨10270374, by rfl⟩ : syracuseStep 27387665 = 20540749) B20540749
theorem B6514991 : Blo 948586 6514991 := bstep (se 1 (by rfl) ⟨4886243, by rfl⟩ : syracuseStep 6514991 = 9772487) B9772487
theorem B4057705 : Blo 948586 4057705 := bstep (se 2 (by rfl) ⟨1521639, by rfl⟩ : syracuseStep 4057705 = 3043279) B3043279
theorem B8121221 : Blo 948586 8121221 := bstep (se 4 (by rfl) ⟨761364, by rfl⟩ : syracuseStep 8121221 = 1522729) B1522729
theorem B1600823 : Blo 948586 1600823 := bstep (se 1 (by rfl) ⟨1200617, by rfl⟩ : syracuseStep 1600823 = 2401235) B2401235
theorem B1928615 : Blo 948586 1928615 := bstep (se 1 (by rfl) ⟨1446461, by rfl⟩ : syracuseStep 1928615 = 2892923) B2892923
theorem B8121971 : Blo 948586 8121971 := bstep (se 1 (by rfl) ⟨6091478, by rfl⟩ : syracuseStep 8121971 = 12182957) B12182957
theorem B1601275 : Blo 948586 1601275 := bstep (se 1 (by rfl) ⟨1200956, by rfl⟩ : syracuseStep 1601275 = 2401913) B2401913
theorem B1601417 : Blo 948586 1601417 := bstep (se 2 (by rfl) ⟨600531, by rfl⟩ : syracuseStep 1601417 = 1201063) B1201063
theorem B18542479 : Blo 948586 18542479 := bstep (se 1 (by rfl) ⟨13906859, by rfl⟩ : syracuseStep 18542479 = 27813719) B27813719
theorem B41087033 : Blo 948586 41087033 := bstep (se 2 (by rfl) ⟨15407637, by rfl⟩ : syracuseStep 41087033 = 30815275) B30815275
theorem B4059209 : Blo 948586 4059209 := bstep (se 2 (by rfl) ⟨1522203, by rfl⟩ : syracuseStep 4059209 = 3044407) B3044407
theorem B6844499 : Blo 948586 6844499 := bstep (se 1 (by rfl) ⟨5133374, by rfl⟩ : syracuseStep 6844499 = 10266749) B10266749
theorem B8221499 : Blo 948586 8221499 := bstep (se 1 (by rfl) ⟨6166124, by rfl⟩ : syracuseStep 8221499 = 12332249) B12332249
theorem B1602983 : Blo 948586 1602983 := bstep (se 1 (by rfl) ⟨1202237, by rfl⟩ : syracuseStep 1602983 = 2404475) B2404475
theorem B7206893 : Blo 948586 7206893 := bstep (se 3 (by rfl) ⟨1351292, by rfl⟩ : syracuseStep 7206893 = 2702585) B2702585
theorem B2029639 : Blo 948586 2029639 := bstep (se 1 (by rfl) ⟨1522229, by rfl⟩ : syracuseStep 2029639 = 3044459) B3044459
theorem B3471569 : Blo 948586 3471569 := bstep (se 2 (by rfl) ⟨1301838, by rfl⟩ : syracuseStep 3471569 = 2603677) B2603677
theorem B948639 : Blo 948586 948639 := bstep (se 1 (by rfl) ⟨711479, by rfl⟩ : syracuseStep 948639 = 1422959) B1422959
theorem B948687 : Blo 948586 948687 := bstep (se 1 (by rfl) ⟨711515, by rfl⟩ : syracuseStep 948687 = 1423031) B1423031
theorem B948711 : Blo 948586 948711 := bstep (se 1 (by rfl) ⟨711533, by rfl⟩ : syracuseStep 948711 = 1423067) B1423067
theorem B3209759 : Blo 948586 3209759 := bstep (se 1 (by rfl) ⟨2407319, by rfl⟩ : syracuseStep 3209759 = 4814639) B4814639
theorem B1604137 : Blo 948586 1604137 := bstep (se 2 (by rfl) ⟨601551, by rfl⟩ : syracuseStep 1604137 = 1203103) B1203103
theorem B948827 : Blo 948586 948827 := bstep (se 1 (by rfl) ⟨711620, by rfl⟩ : syracuseStep 948827 = 1423241) B1423241
theorem B948895 : Blo 948586 948895 := bstep (se 1 (by rfl) ⟨711671, by rfl⟩ : syracuseStep 948895 = 1423343) B1423343
theorem B949063 : Blo 948586 949063 := bstep (se 1 (by rfl) ⟨711797, by rfl⟩ : syracuseStep 949063 = 1423595) B1423595
theorem B949103 : Blo 948586 949103 := bstep (se 1 (by rfl) ⟨711827, by rfl⟩ : syracuseStep 949103 = 1423655) B1423655
theorem B949159 : Blo 948586 949159 := bstep (se 1 (by rfl) ⟨711869, by rfl⟩ : syracuseStep 949159 = 1423739) B1423739
theorem B12352501 : Blo 948586 12352501 := bstep (se 5 (by rfl) ⟨579023, by rfl⟩ : syracuseStep 12352501 = 1158047) B1158047
theorem B949339 : Blo 948586 949339 := bstep (se 1 (by rfl) ⟨712004, by rfl⟩ : syracuseStep 949339 = 1424009) B1424009
theorem B949455 : Blo 948586 949455 := bstep (se 1 (by rfl) ⟨712091, by rfl⟩ : syracuseStep 949455 = 1424183) B1424183
theorem B949479 : Blo 948586 949479 := bstep (se 1 (by rfl) ⟨712109, by rfl⟩ : syracuseStep 949479 = 1424219) B1424219
theorem B1604839 : Blo 948586 1604839 := bstep (se 1 (by rfl) ⟨1203629, by rfl⟩ : syracuseStep 1604839 = 2407259) B2407259
theorem B949575 : Blo 948586 949575 := bstep (se 1 (by rfl) ⟨712181, by rfl⟩ : syracuseStep 949575 = 1424363) B1424363
theorem B1605035 : Blo 948586 1605035 := bstep (se 1 (by rfl) ⟨1203776, by rfl⟩ : syracuseStep 1605035 = 2407553) B2407553
theorem B7306685 : Blo 948586 7306685 := bstep (se 3 (by rfl) ⟨1370003, by rfl⟩ : syracuseStep 7306685 = 2740007) B2740007
theorem B949711 : Blo 948586 949711 := bstep (se 1 (by rfl) ⟨712283, by rfl⟩ : syracuseStep 949711 = 1424567) B1424567
theorem B100040147 : Blo 948586 100040147 := bstep (se 1 (by rfl) ⟨75030110, by rfl⟩ : syracuseStep 100040147 = 150060221) B150060221
theorem B949871 : Blo 948586 949871 := bstep (se 1 (by rfl) ⟨712403, by rfl⟩ : syracuseStep 949871 = 1424807) B1424807
theorem B949927 : Blo 948586 949927 := bstep (se 1 (by rfl) ⟨712445, by rfl⟩ : syracuseStep 949927 = 1424891) B1424891
theorem B949991 : Blo 948586 949991 := bstep (se 1 (by rfl) ⟨712493, by rfl⟩ : syracuseStep 949991 = 1424987) B1424987
theorem B950047 : Blo 948586 950047 := bstep (se 1 (by rfl) ⟨712535, by rfl⟩ : syracuseStep 950047 = 1425071) B1425071
theorem B950127 : Blo 948586 950127 := bstep (se 1 (by rfl) ⟨712595, by rfl⟩ : syracuseStep 950127 = 1425191) B1425191
theorem B950183 : Blo 948586 950183 := bstep (se 1 (by rfl) ⟨712637, by rfl⟩ : syracuseStep 950183 = 1425275) B1425275
theorem B1605575 : Blo 948586 1605575 := bstep (se 1 (by rfl) ⟨1204181, by rfl⟩ : syracuseStep 1605575 = 2408363) B2408363
theorem B950399 : Blo 948586 950399 := bstep (se 1 (by rfl) ⟨712799, by rfl⟩ : syracuseStep 950399 = 1425599) B1425599
theorem B950683 : Blo 948586 950683 := bstep (se 1 (by rfl) ⟨713012, by rfl⟩ : syracuseStep 950683 = 1426025) B1426025
theorem B950687 : Blo 948586 950687 := bstep (se 1 (by rfl) ⟨713015, by rfl⟩ : syracuseStep 950687 = 1426031) B1426031
theorem B4948397 : Blo 948586 4948397 := bstep (se 3 (by rfl) ⟨927824, by rfl⟩ : syracuseStep 4948397 = 1855649) B1855649
theorem B6685181 : Blo 948586 6685181 := bstep (se 3 (by rfl) ⟨1253471, by rfl⟩ : syracuseStep 6685181 = 2506943) B2506943
theorem B1606351 : Blo 948586 1606351 := bstep (se 1 (by rfl) ⟨1204763, by rfl⟩ : syracuseStep 1606351 = 2409527) B2409527
theorem B951103 : Blo 948586 951103 := bstep (se 1 (by rfl) ⟨713327, by rfl⟩ : syracuseStep 951103 = 1426655) B1426655
theorem B951111 : Blo 948586 951111 := bstep (se 1 (by rfl) ⟨713333, by rfl⟩ : syracuseStep 951111 = 1426667) B1426667
theorem B3048329 : Blo 948586 3048329 := bstep (se 2 (by rfl) ⟨1143123, by rfl⟩ : syracuseStep 3048329 = 2286247) B2286247
theorem B1508303 : Blo 948586 1508303 := bstep (se 1 (by rfl) ⟨1131227, by rfl⟩ : syracuseStep 1508303 = 2262455) B2262455
theorem B6947819 : Blo 948586 6947819 := bstep (se 1 (by rfl) ⟨5210864, by rfl⟩ : syracuseStep 6947819 = 10421729) B10421729
theorem B951367 : Blo 948586 951367 := bstep (se 1 (by rfl) ⟨713525, by rfl⟩ : syracuseStep 951367 = 1427051) B1427051
theorem B951423 : Blo 948586 951423 := bstep (se 1 (by rfl) ⟨713567, by rfl⟩ : syracuseStep 951423 = 1427135) B1427135
theorem B951547 : Blo 948586 951547 := bstep (se 1 (by rfl) ⟨713660, by rfl⟩ : syracuseStep 951547 = 1427321) B1427321
theorem B10847519 : Blo 948586 10847519 := bstep (se 1 (by rfl) ⟨8135639, by rfl⟩ : syracuseStep 10847519 = 16271279) B16271279
theorem B39617915 : Blo 948586 39617915 := bstep (se 1 (by rfl) ⟨29713436, by rfl⟩ : syracuseStep 39617915 = 59426873) B59426873
theorem B952047 : Blo 948586 952047 := bstep (se 1 (by rfl) ⟨714035, by rfl⟩ : syracuseStep 952047 = 1428071) B1428071
theorem B2197243 : Blo 948586 2197243 := bstep (se 1 (by rfl) ⟨1647932, by rfl⟩ : syracuseStep 2197243 = 3295865) B3295865
theorem B17598221 : Blo 948586 17598221 := bstep (se 3 (by rfl) ⟨3299666, by rfl⟩ : syracuseStep 17598221 = 6599333) B6599333
theorem B952175 : Blo 948586 952175 := bstep (se 1 (by rfl) ⟨714131, by rfl⟩ : syracuseStep 952175 = 1428263) B1428263
theorem B2033705 : Blo 948586 2033705 := bstep (se 2 (by rfl) ⟨762639, by rfl⟩ : syracuseStep 2033705 = 1525279) B1525279
theorem B952391 : Blo 948586 952391 := bstep (se 1 (by rfl) ⟨714293, by rfl⟩ : syracuseStep 952391 = 1428587) B1428587
theorem B952551 : Blo 948586 952551 := bstep (se 1 (by rfl) ⟨714413, by rfl⟩ : syracuseStep 952551 = 1428827) B1428827
theorem B952571 : Blo 948586 952571 := bstep (se 1 (by rfl) ⟨714428, by rfl⟩ : syracuseStep 952571 = 1428857) B1428857
theorem B952575 : Blo 948586 952575 := bstep (se 1 (by rfl) ⟨714431, by rfl⟩ : syracuseStep 952575 = 1428863) B1428863
theorem B3607031 : Blo 948586 3607031 := bstep (se 1 (by rfl) ⟨2705273, by rfl⟩ : syracuseStep 3607031 = 5410547) B5410547
theorem B4950575 : Blo 948586 4950575 := bstep (se 1 (by rfl) ⟨3712931, by rfl⟩ : syracuseStep 4950575 = 7425863) B7425863
theorem B12192389 : Blo 948586 12192389 := bstep (se 4 (by rfl) ⟨1143036, by rfl⟩ : syracuseStep 12192389 = 2286073) B2286073
theorem B1804943 : Blo 948586 1804943 := bstep (se 1 (by rfl) ⟨1353707, by rfl⟩ : syracuseStep 1804943 = 2707415) B2707415
theorem B3607199 : Blo 948586 3607199 := bstep (se 1 (by rfl) ⟨2705399, by rfl⟩ : syracuseStep 3607199 = 5410799) B5410799
theorem B21924539 : Blo 948586 21924539 := bstep (se 1 (by rfl) ⟨16443404, by rfl⟩ : syracuseStep 21924539 = 32886809) B32886809
theorem B5410091 : Blo 948586 5410091 := bstep (se 1 (by rfl) ⟨4057568, by rfl⟩ : syracuseStep 5410091 = 8115137) B8115137
theorem B29265239 : Blo 948586 29265239 := bstep (se 1 (by rfl) ⟨21948929, by rfl⟩ : syracuseStep 29265239 = 43897859) B43897859
theorem B5410273 : Blo 948586 5410273 := bstep (se 2 (by rfl) ⟨2028852, by rfl⟩ : syracuseStep 5410273 = 4057705) B4057705
theorem B1805915 : Blo 948586 1805915 := bstep (se 1 (by rfl) ⟨1354436, by rfl⟩ : syracuseStep 1805915 = 2708873) B2708873
theorem B5148319 : Blo 948586 5148319 := bstep (se 1 (by rfl) ⟨3861239, by rfl⟩ : syracuseStep 5148319 = 7722479) B7722479
theorem B5771033 : Blo 948586 5771033 := bstep (se 2 (by rfl) ⟨2164137, by rfl⟩ : syracuseStep 5771033 = 4328275) B4328275
theorem B2166695 : Blo 948586 2166695 := bstep (se 1 (by rfl) ⟨1625021, by rfl⟩ : syracuseStep 2166695 = 3250043) B3250043
theorem B10981943 : Blo 948586 10981943 := bstep (se 1 (by rfl) ⟨8236457, by rfl⟩ : syracuseStep 10981943 = 16472915) B16472915
theorem B2134763 : Blo 948586 2134763 := bstep (se 1 (by rfl) ⟨1601072, by rfl⟩ : syracuseStep 2134763 = 3202145) B3202145
theorem B2135033 : Blo 948586 2135033 := bstep (se 2 (by rfl) ⟨800637, by rfl⟩ : syracuseStep 2135033 = 1601275) B1601275
theorem B2135123 : Blo 948586 2135123 := bstep (se 1 (by rfl) ⟨1601342, by rfl⟩ : syracuseStep 2135123 = 3202685) B3202685
theorem B2135231 : Blo 948586 2135231 := bstep (se 1 (by rfl) ⟨1601423, by rfl⟩ : syracuseStep 2135231 = 3202847) B3202847
theorem B2135303 : Blo 948586 2135303 := bstep (se 1 (by rfl) ⟨1601477, by rfl⟩ : syracuseStep 2135303 = 3202955) B3202955
theorem B2135663 : Blo 948586 2135663 := bstep (se 1 (by rfl) ⟨1601747, by rfl⟩ : syracuseStep 2135663 = 3203495) B3203495
theorem B8689355 : Blo 948586 8689355 := bstep (se 1 (by rfl) ⟨6517016, by rfl⟩ : syracuseStep 8689355 = 13034033) B13034033
theorem B8132359 : Blo 948586 8132359 := bstep (se 1 (by rfl) ⟨6099269, by rfl⟩ : syracuseStep 8132359 = 12198539) B12198539
theorem B10557623 : Blo 948586 10557623 := bstep (se 1 (by rfl) ⟨7918217, by rfl⟩ : syracuseStep 10557623 = 15836435) B15836435
theorem B3250601 : Blo 948586 3250601 := bstep (se 2 (by rfl) ⟨1218975, by rfl⟩ : syracuseStep 3250601 = 2437951) B2437951
theorem B3611087 : Blo 948586 3611087 := bstep (se 1 (by rfl) ⟨2708315, by rfl⟩ : syracuseStep 3611087 = 5416631) B5416631
theorem B18258443 : Blo 948586 18258443 := bstep (se 1 (by rfl) ⟨13693832, by rfl⟩ : syracuseStep 18258443 = 27387665) B27387665
theorem B3087503 : Blo 948586 3087503 := bstep (se 1 (by rfl) ⟨2315627, by rfl⟩ : syracuseStep 3087503 = 4631255) B4631255
theorem B5414147 : Blo 948586 5414147 := bstep (se 1 (by rfl) ⟨4060610, by rfl⟩ : syracuseStep 5414147 = 8121221) B8121221
theorem B3087805 : Blo 948586 3087805 := bstep (se 3 (by rfl) ⟨578963, by rfl⟩ : syracuseStep 3087805 = 1157927) B1157927
theorem B5414647 : Blo 948586 5414647 := bstep (se 1 (by rfl) ⟨4060985, by rfl⟩ : syracuseStep 5414647 = 8121971) B8121971
theorem B4562999 : Blo 948586 4562999 := bstep (se 1 (by rfl) ⟨3422249, by rfl⟩ : syracuseStep 4562999 = 6844499) B6844499
theorem B17310239 : Blo 948586 17310239 := bstep (se 1 (by rfl) ⟨12982679, by rfl⟩ : syracuseStep 17310239 = 25965359) B25965359
theorem B5480999 : Blo 948586 5480999 := bstep (se 1 (by rfl) ⟨4110749, by rfl⟩ : syracuseStep 5480999 = 8221499) B8221499
theorem B2138849 : Blo 948586 2138849 := bstep (se 2 (by rfl) ⟨802068, by rfl⟩ : syracuseStep 2138849 = 1604137) B1604137
theorem B3613531 : Blo 948586 3613531 := bstep (se 1 (by rfl) ⟨2710148, by rfl⟩ : syracuseStep 3613531 = 5420297) B5420297
theorem B2139785 : Blo 948586 2139785 := bstep (se 2 (by rfl) ⟨802419, by rfl⟩ : syracuseStep 2139785 = 1604839) B1604839
theorem B2139839 : Blo 948586 2139839 := bstep (se 1 (by rfl) ⟨1604879, by rfl⟩ : syracuseStep 2139839 = 3209759) B3209759
theorem B3614503 : Blo 948586 3614503 := bstep (se 1 (by rfl) ⟨2710877, by rfl⟩ : syracuseStep 3614503 = 5421755) B5421755
theorem B66693431 : Blo 948586 66693431 := bstep (se 1 (by rfl) ⟨50020073, by rfl⟩ : syracuseStep 66693431 = 100040147) B100040147
theorem B4401535 : Blo 948586 4401535 := bstep (se 1 (by rfl) ⟨3301151, by rfl⟩ : syracuseStep 4401535 = 6602303) B6602303
theorem B2566633 : Blo 948586 2566633 := bstep (se 2 (by rfl) ⟨962487, by rfl⟩ : syracuseStep 2566633 = 1924975) B1924975
theorem B2403391 : Blo 948586 2403391 := bstep (se 1 (by rfl) ⟨1802543, by rfl⟩ : syracuseStep 2403391 = 3605087) B3605087
theorem B13348151 : Blo 948586 13348151 := bstep (se 1 (by rfl) ⟨10011113, by rfl⟩ : syracuseStep 13348151 = 20022227) B20022227
theorem B2567531 : Blo 948586 2567531 := bstep (se 1 (by rfl) ⟨1925648, by rfl⟩ : syracuseStep 2567531 = 3851297) B3851297
theorem B2141567 : Blo 948586 2141567 := bstep (se 1 (by rfl) ⟨1606175, by rfl⟩ : syracuseStep 2141567 = 3212351) B3212351
theorem B12201515 : Blo 948586 12201515 := bstep (se 1 (by rfl) ⟨9151136, by rfl⟩ : syracuseStep 12201515 = 18302273) B18302273
theorem B30781295 : Blo 948586 30781295 := bstep (se 1 (by rfl) ⟨23085971, by rfl⟩ : syracuseStep 30781295 = 46171943) B46171943
theorem B2469881 : Blo 948586 2469881 := bstep (se 2 (by rfl) ⟨926205, by rfl⟩ : syracuseStep 2469881 = 1852411) B1852411
theorem B1356031 : Blo 948586 1356031 := bstep (se 1 (by rfl) ⟨1017023, by rfl⟩ : syracuseStep 1356031 = 2034047) B2034047
theorem B23113993 : Blo 948586 23113993 := bstep (se 2 (by rfl) ⟨8667747, by rfl⟩ : syracuseStep 23113993 = 17335495) B17335495
theorem B2142521 : Blo 948586 2142521 := bstep (se 2 (by rfl) ⟨803445, by rfl⟩ : syracuseStep 2142521 = 1606891) B1606891
theorem B2437867 : Blo 948586 2437867 := bstep (se 1 (by rfl) ⟨1828400, by rfl⟩ : syracuseStep 2437867 = 3656801) B3656801
theorem B4339169 : Blo 948586 4339169 := bstep (se 2 (by rfl) ⟨1627188, by rfl⟩ : syracuseStep 4339169 = 3254377) B3254377
theorem B1521127 : Blo 948586 1521127 := bstep (se 1 (by rfl) ⟨1140845, by rfl⟩ : syracuseStep 1521127 = 2281691) B2281691
theorem B1423055 : Blo 948586 1423055 := bstep (se 1 (by rfl) ⟨1067291, by rfl⟩ : syracuseStep 1423055 = 2134583) B2134583
theorem B2406095 : Blo 948586 2406095 := bstep (se 1 (by rfl) ⟨1804571, by rfl⟩ : syracuseStep 2406095 = 3609143) B3609143
theorem B3258251 : Blo 948586 3258251 := bstep (se 1 (by rfl) ⟨2443688, by rfl⟩ : syracuseStep 3258251 = 4887377) B4887377
theorem B1423259 : Blo 948586 1423259 := bstep (se 1 (by rfl) ⟨1067444, by rfl⟩ : syracuseStep 1423259 = 2134889) B2134889
theorem B1423295 : Blo 948586 1423295 := bstep (se 1 (by rfl) ⟨1067471, by rfl⟩ : syracuseStep 1423295 = 2134943) B2134943
theorem B1423463 : Blo 948586 1423463 := bstep (se 1 (by rfl) ⟨1067597, by rfl⟩ : syracuseStep 1423463 = 2135195) B2135195
theorem B2406793 : Blo 948586 2406793 := bstep (se 2 (by rfl) ⟨902547, by rfl⟩ : syracuseStep 2406793 = 1805095) B1805095
theorem B1423847 : Blo 948586 1423847 := bstep (se 1 (by rfl) ⟨1067885, by rfl⟩ : syracuseStep 1423847 = 2135771) B2135771
theorem B1423919 : Blo 948586 1423919 := bstep (se 1 (by rfl) ⟨1067939, by rfl⟩ : syracuseStep 1423919 = 2135879) B2135879
theorem B31210447 : Blo 948586 31210447 := bstep (se 1 (by rfl) ⟨23407835, by rfl⟩ : syracuseStep 31210447 = 46815671) B46815671
theorem B1424591 : Blo 948586 1424591 := bstep (se 1 (by rfl) ⟨1068443, by rfl⟩ : syracuseStep 1424591 = 2136887) B2136887
theorem B1424681 : Blo 948586 1424681 := bstep (se 2 (by rfl) ⟨534255, by rfl⟩ : syracuseStep 1424681 = 1068511) B1068511
theorem B1424711 : Blo 948586 1424711 := bstep (se 1 (by rfl) ⟨1068533, by rfl⟩ : syracuseStep 1424711 = 2137067) B2137067
theorem B2408201 : Blo 948586 2408201 := bstep (se 2 (by rfl) ⟨903075, by rfl⟩ : syracuseStep 2408201 = 1806151) B1806151
theorem B2408231 : Blo 948586 2408231 := bstep (se 1 (by rfl) ⟨1806173, by rfl⟩ : syracuseStep 2408231 = 3612347) B3612347
theorem B6176567 : Blo 948586 6176567 := bstep (se 1 (by rfl) ⟨4632425, by rfl⟩ : syracuseStep 6176567 = 9264851) B9264851
theorem B24723305 : Blo 948586 24723305 := bstep (se 2 (by rfl) ⟨9271239, by rfl⟩ : syracuseStep 24723305 = 18542479) B18542479
theorem B1425311 : Blo 948586 1425311 := bstep (se 1 (by rfl) ⟨1068983, by rfl⟩ : syracuseStep 1425311 = 2137967) B2137967
theorem B1425401 : Blo 948586 1425401 := bstep (se 2 (by rfl) ⟨534525, by rfl⟩ : syracuseStep 1425401 = 1069051) B1069051
theorem B49299457 : Blo 948586 49299457 := bstep (se 2 (by rfl) ⟨18487296, by rfl⟩ : syracuseStep 49299457 = 36974593) B36974593
theorem B1425545 : Blo 948586 1425545 := bstep (se 2 (by rfl) ⟨534579, by rfl⟩ : syracuseStep 1425545 = 1069159) B1069159
theorem B5357789 : Blo 948586 5357789 := bstep (se 3 (by rfl) ⟨1004585, by rfl⟩ : syracuseStep 5357789 = 2009171) B2009171
theorem B1425641 : Blo 948586 1425641 := bstep (se 2 (by rfl) ⟨534615, by rfl⟩ : syracuseStep 1425641 = 1069231) B1069231
theorem B1425767 : Blo 948586 1425767 := bstep (se 1 (by rfl) ⟨1069325, by rfl⟩ : syracuseStep 1425767 = 2138651) B2138651
theorem B12206537 : Blo 948586 12206537 := bstep (se 2 (by rfl) ⟨4577451, by rfl⟩ : syracuseStep 12206537 = 9154903) B9154903
theorem B1425887 : Blo 948586 1425887 := bstep (se 1 (by rfl) ⟨1069415, by rfl⟩ : syracuseStep 1425887 = 2138831) B2138831
theorem B1426139 : Blo 948586 1426139 := bstep (se 1 (by rfl) ⟨1069604, by rfl⟩ : syracuseStep 1426139 = 2139209) B2139209
theorem B2409203 : Blo 948586 2409203 := bstep (se 1 (by rfl) ⟨1806902, by rfl⟩ : syracuseStep 2409203 = 3613805) B3613805
theorem B3851003 : Blo 948586 3851003 := bstep (se 1 (by rfl) ⟨2888252, by rfl⟩ : syracuseStep 3851003 = 5776505) B5776505
theorem B2409223 : Blo 948586 2409223 := bstep (se 1 (by rfl) ⟨1806917, by rfl⟩ : syracuseStep 2409223 = 3613835) B3613835
theorem B1426553 : Blo 948586 1426553 := bstep (se 2 (by rfl) ⟨534957, by rfl⟩ : syracuseStep 1426553 = 1069915) B1069915
theorem B1426751 : Blo 948586 1426751 := bstep (se 1 (by rfl) ⟨1070063, by rfl⟩ : syracuseStep 1426751 = 2140127) B2140127
theorem B4343327 : Blo 948586 4343327 := bstep (se 1 (by rfl) ⟨3257495, by rfl⟩ : syracuseStep 4343327 = 6514991) B6514991
theorem B2279231 : Blo 948586 2279231 := bstep (se 1 (by rfl) ⟨1709423, by rfl⟩ : syracuseStep 2279231 = 3418847) B3418847
theorem B7718743 : Blo 948586 7718743 := bstep (se 1 (by rfl) ⟨5789057, by rfl⟩ : syracuseStep 7718743 = 11578115) B11578115
theorem B1427423 : Blo 948586 1427423 := bstep (se 1 (by rfl) ⟨1070567, by rfl⟩ : syracuseStep 1427423 = 2141135) B2141135
theorem B1427483 : Blo 948586 1427483 := bstep (se 1 (by rfl) ⟨1070612, by rfl⟩ : syracuseStep 1427483 = 2141225) B2141225
theorem B1427639 : Blo 948586 1427639 := bstep (se 1 (by rfl) ⟨1070729, by rfl⟩ : syracuseStep 1427639 = 2141459) B2141459
theorem B1067215 : Blo 948586 1067215 := bstep (se 1 (by rfl) ⟨800411, by rfl⟩ : syracuseStep 1067215 = 1600823) B1600823
theorem B1427663 : Blo 948586 1427663 := bstep (se 1 (by rfl) ⟨1070747, by rfl⟩ : syracuseStep 1427663 = 2141495) B2141495
theorem B1067611 : Blo 948586 1067611 := bstep (se 1 (by rfl) ⟨800708, by rfl⟩ : syracuseStep 1067611 = 1601417) B1601417
theorem B1428059 : Blo 948586 1428059 := bstep (se 1 (by rfl) ⟨1071044, by rfl⟩ : syracuseStep 1428059 = 2142089) B2142089
theorem B2706139 : Blo 948586 2706139 := bstep (se 1 (by rfl) ⟨2029604, by rfl⟩ : syracuseStep 2706139 = 4059209) B4059209
theorem B1428203 : Blo 948586 1428203 := bstep (se 1 (by rfl) ⟨1071152, by rfl⟩ : syracuseStep 1428203 = 2142305) B2142305
theorem B2706185 : Blo 948586 2706185 := bstep (se 2 (by rfl) ⟨1014819, by rfl⟩ : syracuseStep 2706185 = 2029639) B2029639
theorem B1428233 : Blo 948586 1428233 := bstep (se 2 (by rfl) ⟨535587, by rfl⟩ : syracuseStep 1428233 = 1071175) B1071175
theorem B8113223 : Blo 948586 8113223 := bstep (se 1 (by rfl) ⟨6084917, by rfl⟩ : syracuseStep 8113223 = 12169835) B12169835
theorem B1428647 : Blo 948586 1428647 := bstep (se 1 (by rfl) ⟨1071485, by rfl⟩ : syracuseStep 1428647 = 2142971) B2142971
theorem B1428791 : Blo 948586 1428791 := bstep (se 1 (by rfl) ⟨1071593, by rfl⟩ : syracuseStep 1428791 = 2143187) B2143187
theorem B2739577 : Blo 948586 2739577 := bstep (se 2 (by rfl) ⟨1027341, by rfl⟩ : syracuseStep 2739577 = 2054683) B2054683
theorem B1068655 : Blo 948586 1068655 := bstep (se 1 (by rfl) ⟨801491, by rfl⟩ : syracuseStep 1068655 = 1602983) B1602983
theorem B16470001 : Blo 948586 16470001 := bstep (se 2 (by rfl) ⟨6176250, by rfl⟩ : syracuseStep 16470001 = 12352501) B12352501
theorem B4804595 : Blo 948586 4804595 := bstep (se 1 (by rfl) ⟨3603446, by rfl⟩ : syracuseStep 4804595 = 7206893) B7206893
theorem B2314379 : Blo 948586 2314379 := bstep (se 1 (by rfl) ⟨1735784, by rfl⟩ : syracuseStep 2314379 = 3471569) B3471569
theorem B6082715 : Blo 948586 6082715 := bstep (se 1 (by rfl) ⟨4562036, by rfl⟩ : syracuseStep 6082715 = 9124073) B9124073
theorem B5951663 : Blo 948586 5951663 := bstep (se 1 (by rfl) ⟨4463747, by rfl⟩ : syracuseStep 5951663 = 8927495) B8927495
theorem B1070023 : Blo 948586 1070023 := bstep (se 1 (by rfl) ⟨802517, by rfl⟩ : syracuseStep 1070023 = 1605035) B1605035
theorem B4871123 : Blo 948586 4871123 := bstep (se 1 (by rfl) ⟨3653342, by rfl⟩ : syracuseStep 4871123 = 7306685) B7306685
theorem B1070383 : Blo 948586 1070383 := bstep (se 1 (by rfl) ⟨802787, by rfl⟩ : syracuseStep 1070383 = 1605575) B1605575
theorem B4806215 : Blo 948586 4806215 := bstep (se 1 (by rfl) ⟨3604661, by rfl⟩ : syracuseStep 4806215 = 7209323) B7209323
theorem B4806377 : Blo 948586 4806377 := bstep (se 2 (by rfl) ⟨1802391, by rfl⟩ : syracuseStep 4806377 = 3604783) B3604783
theorem B6084355 : Blo 948586 6084355 := bstep (se 1 (by rfl) ⟨4563266, by rfl⟩ : syracuseStep 6084355 = 9126533) B9126533
theorem B1070887 : Blo 948586 1070887 := bstep (se 1 (by rfl) ⟨803165, by rfl⟩ : syracuseStep 1070887 = 1606331) B1606331
theorem B10835855 : Blo 948586 10835855 := bstep (se 1 (by rfl) ⟨8126891, by rfl⟩ : syracuseStep 10835855 = 16253783) B16253783
theorem B1202303 : Blo 948586 1202303 := bstep (se 1 (by rfl) ⟨901727, by rfl⟩ : syracuseStep 1202303 = 1803455) B1803455
theorem B2709899 : Blo 948586 2709899 := bstep (se 1 (by rfl) ⟨2032424, by rfl⟩ : syracuseStep 2709899 = 4064849) B4064849
theorem B1203007 : Blo 948586 1203007 := bstep (se 1 (by rfl) ⟨902255, by rfl⟩ : syracuseStep 1203007 = 1804511) B1804511
theorem B3201929 : Blo 948586 3201929 := bstep (se 2 (by rfl) ⟨1200723, by rfl⟩ : syracuseStep 3201929 = 2401447) B2401447
theorem B4054151 : Blo 948586 4054151 := bstep (se 1 (by rfl) ⟨3040613, by rfl⟩ : syracuseStep 4054151 = 6081227) B6081227
theorem B7232651 : Blo 948586 7232651 := bstep (se 1 (by rfl) ⟨5424488, by rfl⟩ : syracuseStep 7232651 = 10848977) B10848977
theorem B9133991 : Blo 948586 9133991 := bstep (se 1 (by rfl) ⟨6850493, by rfl⟩ : syracuseStep 9133991 = 13700987) B13700987
theorem B1204895 : Blo 948586 1204895 := bstep (se 1 (by rfl) ⟨903671, by rfl⟩ : syracuseStep 1204895 = 1807343) B1807343
theorem B79193213 : Blo 948586 79193213 := bstep (se 3 (by rfl) ⟨14848727, by rfl⟩ : syracuseStep 79193213 = 29697455) B29697455
theorem B3204791 : Blo 948586 3204791 := bstep (se 1 (by rfl) ⟨2403593, by rfl⟩ : syracuseStep 3204791 = 4807187) B4807187
theorem B20571893 : Blo 948586 20571893 := bstep (se 5 (by rfl) ⟨964307, by rfl⟩ : syracuseStep 20571893 = 1928615) B1928615
theorem B4811075 : Blo 948586 4811075 := bstep (se 1 (by rfl) ⟨3608306, by rfl⟩ : syracuseStep 4811075 = 7216613) B7216613
theorem B4943759 : Blo 948586 4943759 := bstep (se 1 (by rfl) ⟨3707819, by rfl⟩ : syracuseStep 4943759 = 7415639) B7415639
theorem B5402983 : Blo 948586 5402983 := bstep (se 1 (by rfl) ⟨4052237, by rfl⟩ : syracuseStep 5402983 = 8104475) B8104475
theorem B4059517 : Blo 948586 4059517 := bstep (se 3 (by rfl) ⟨761159, by rfl⟩ : syracuseStep 4059517 = 1522319) B1522319
theorem B2061167 : Blo 948586 2061167 := bstep (se 1 (by rfl) ⟨1545875, by rfl⟩ : syracuseStep 2061167 = 3091751) B3091751
theorem B4814153 : Blo 948586 4814153 := bstep (se 2 (by rfl) ⟨1805307, by rfl⟩ : syracuseStep 4814153 = 3610615) B3610615
theorem B27391355 : Blo 948586 27391355 := bstep (se 1 (by rfl) ⟨20543516, by rfl⟩ : syracuseStep 27391355 = 41087033) B41087033
theorem B23099003 : Blo 948586 23099003 := bstep (se 1 (by rfl) ⟨17324252, by rfl⟩ : syracuseStep 23099003 = 34648505) B34648505
theorem B3208841 : Blo 948586 3208841 := bstep (se 2 (by rfl) ⟨1203315, by rfl⟩ : syracuseStep 3208841 = 2406631) B2406631
theorem B5404441 : Blo 948586 5404441 := bstep (se 2 (by rfl) ⟨2026665, by rfl⟩ : syracuseStep 5404441 = 4053331) B4053331
theorem B2816041 : Blo 948586 2816041 := bstep (se 2 (by rfl) ⟨1056015, by rfl⟩ : syracuseStep 2816041 = 2112031) B2112031
theorem B1603631 : Blo 948586 1603631 := bstep (se 1 (by rfl) ⟨1202723, by rfl⟩ : syracuseStep 1603631 = 2405447) B2405447
theorem B5404967 : Blo 948586 5404967 := bstep (se 1 (by rfl) ⟨4053725, by rfl⟩ : syracuseStep 5404967 = 8107451) B8107451
theorem B4815449 : Blo 948586 4815449 := bstep (se 2 (by rfl) ⟨1805793, by rfl⟩ : syracuseStep 4815449 = 3611587) B3611587
theorem B949215 : Blo 948586 949215 := bstep (se 1 (by rfl) ⟨711911, by rfl⟩ : syracuseStep 949215 = 1423823) B1423823
theorem B1014751 : Blo 948586 1014751 := bstep (se 1 (by rfl) ⟨761063, by rfl⟩ : syracuseStep 1014751 = 1522127) B1522127
theorem B949275 : Blo 948586 949275 := bstep (se 1 (by rfl) ⟨711956, by rfl⟩ : syracuseStep 949275 = 1423913) B1423913
theorem B949403 : Blo 948586 949403 := bstep (se 1 (by rfl) ⟨712052, by rfl⟩ : syracuseStep 949403 = 1424105) B1424105
theorem B949659 : Blo 948586 949659 := bstep (se 1 (by rfl) ⟨712244, by rfl⟩ : syracuseStep 949659 = 1424489) B1424489
theorem B949743 : Blo 948586 949743 := bstep (se 1 (by rfl) ⟨712307, by rfl⟩ : syracuseStep 949743 = 1424615) B1424615
theorem B950079 : Blo 948586 950079 := bstep (se 1 (by rfl) ⟨712559, by rfl⟩ : syracuseStep 950079 = 1425119) B1425119
theorem B950107 : Blo 948586 950107 := bstep (se 1 (by rfl) ⟨712580, by rfl⟩ : syracuseStep 950107 = 1425161) B1425161
theorem B9142139 : Blo 948586 9142139 := bstep (se 1 (by rfl) ⟨6856604, by rfl⟩ : syracuseStep 9142139 = 13713209) B13713209
theorem B7208837 : Blo 948586 7208837 := bstep (se 4 (by rfl) ⟨675828, by rfl⟩ : syracuseStep 7208837 = 1351657) B1351657
theorem B65732609 : Blo 948586 65732609 := bstep (se 2 (by rfl) ⟨24649728, by rfl⟩ : syracuseStep 65732609 = 49299457) B49299457
theorem B950363 : Blo 948586 950363 := bstep (se 1 (by rfl) ⟨712772, by rfl⟩ : syracuseStep 950363 = 1425545) B1425545
theorem B3571859 : Blo 948586 3571859 := bstep (se 1 (by rfl) ⟨2678894, by rfl⟩ : syracuseStep 3571859 = 5357789) B5357789
theorem B950427 : Blo 948586 950427 := bstep (se 1 (by rfl) ⟨712820, by rfl⟩ : syracuseStep 950427 = 1425641) B1425641
theorem B950511 : Blo 948586 950511 := bstep (se 1 (by rfl) ⟨712883, by rfl⟩ : syracuseStep 950511 = 1425767) B1425767
theorem B950591 : Blo 948586 950591 := bstep (se 1 (by rfl) ⟨712943, by rfl⟩ : syracuseStep 950591 = 1425887) B1425887
theorem B4456787 : Blo 948586 4456787 := bstep (se 1 (by rfl) ⟨3342590, by rfl⟩ : syracuseStep 4456787 = 6685181) B6685181
theorem B950759 : Blo 948586 950759 := bstep (se 1 (by rfl) ⟨713069, by rfl⟩ : syracuseStep 950759 = 1426139) B1426139
theorem B1606135 : Blo 948586 1606135 := bstep (se 1 (by rfl) ⟨1204601, by rfl⟩ : syracuseStep 1606135 = 2409203) B2409203
theorem B2032219 : Blo 948586 2032219 := bstep (se 1 (by rfl) ⟨1524164, by rfl⟩ : syracuseStep 2032219 = 3048329) B3048329
theorem B951035 : Blo 948586 951035 := bstep (se 1 (by rfl) ⟨713276, by rfl⟩ : syracuseStep 951035 = 1426553) B1426553
theorem B951167 : Blo 948586 951167 := bstep (se 1 (by rfl) ⟨713375, by rfl⟩ : syracuseStep 951167 = 1426751) B1426751
theorem B3212297 : Blo 948586 3212297 := bstep (se 2 (by rfl) ⟨1204611, by rfl⟩ : syracuseStep 3212297 = 2409223) B2409223
theorem B4818041 : Blo 948586 4818041 := bstep (se 2 (by rfl) ⟨1806765, by rfl⟩ : syracuseStep 4818041 = 3613531) B3613531
theorem B11732147 : Blo 948586 11732147 := bstep (se 1 (by rfl) ⟨8799110, by rfl⟩ : syracuseStep 11732147 = 17598221) B17598221
theorem B951615 : Blo 948586 951615 := bstep (se 1 (by rfl) ⟨713711, by rfl⟩ : syracuseStep 951615 = 1427423) B1427423
theorem B951655 : Blo 948586 951655 := bstep (se 1 (by rfl) ⟨713741, by rfl⟩ : syracuseStep 951655 = 1427483) B1427483
theorem B951759 : Blo 948586 951759 := bstep (se 1 (by rfl) ⟨713819, by rfl⟩ : syracuseStep 951759 = 1427639) B1427639
theorem B951775 : Blo 948586 951775 := bstep (se 1 (by rfl) ⟨713831, by rfl⟩ : syracuseStep 951775 = 1427663) B1427663
theorem B952039 : Blo 948586 952039 := bstep (se 1 (by rfl) ⟨714029, by rfl⟩ : syracuseStep 952039 = 1428059) B1428059
theorem B3213053 : Blo 948586 3213053 := bstep (se 3 (by rfl) ⟨602447, by rfl⟩ : syracuseStep 3213053 = 1204895) B1204895
theorem B8128259 : Blo 948586 8128259 := bstep (se 1 (by rfl) ⟨6096194, by rfl⟩ : syracuseStep 8128259 = 12192389) B12192389
theorem B14616359 : Blo 948586 14616359 := bstep (se 1 (by rfl) ⟨10962269, by rfl⟩ : syracuseStep 14616359 = 21924539) B21924539
theorem B952135 : Blo 948586 952135 := bstep (se 1 (by rfl) ⟨714101, by rfl⟩ : syracuseStep 952135 = 1428203) B1428203
theorem B1804123 : Blo 948586 1804123 := bstep (se 1 (by rfl) ⟨1353092, by rfl⟩ : syracuseStep 1804123 = 2706185) B2706185
theorem B952155 : Blo 948586 952155 := bstep (se 1 (by rfl) ⟨714116, by rfl⟩ : syracuseStep 952155 = 1428233) B1428233
theorem B5408815 : Blo 948586 5408815 := bstep (se 1 (by rfl) ⟨4056611, by rfl⟩ : syracuseStep 5408815 = 8113223) B8113223
theorem B952431 : Blo 948586 952431 := bstep (se 1 (by rfl) ⟨714323, by rfl⟩ : syracuseStep 952431 = 1428647) B1428647
theorem B3606727 : Blo 948586 3606727 := bstep (se 1 (by rfl) ⟨2705045, by rfl⟩ : syracuseStep 3606727 = 5410091) B5410091
theorem B952527 : Blo 948586 952527 := bstep (se 1 (by rfl) ⟨714395, by rfl⟩ : syracuseStep 952527 = 1428791) B1428791
theorem B4819337 : Blo 948586 4819337 := bstep (se 2 (by rfl) ⟨1807251, by rfl⟩ : syracuseStep 4819337 = 3614503) B3614503
theorem B10291657 : Blo 948586 10291657 := bstep (se 2 (by rfl) ⟨3859371, by rfl⟩ : syracuseStep 10291657 = 7718743) B7718743
theorem B1444463 : Blo 948586 1444463 := bstep (se 1 (by rfl) ⟨1083347, by rfl⟩ : syracuseStep 1444463 = 2166695) B2166695
theorem B3967775 : Blo 948586 3967775 := bstep (se 1 (by rfl) ⟨2975831, by rfl⟩ : syracuseStep 3967775 = 5951663) B5951663
theorem B5868713 : Blo 948586 5868713 := bstep (se 2 (by rfl) ⟨2200767, by rfl⟩ : syracuseStep 5868713 = 4401535) B4401535
theorem B3247415 : Blo 948586 3247415 := bstep (se 1 (by rfl) ⟨2435561, by rfl⟩ : syracuseStep 3247415 = 4871123) B4871123
theorem B3608185 : Blo 948586 3608185 := bstep (se 2 (by rfl) ⟨1353069, by rfl⟩ : syracuseStep 3608185 = 2706139) B2706139
theorem B1806599 : Blo 948586 1806599 := bstep (se 1 (by rfl) ⟨1354949, by rfl⟩ : syracuseStep 1806599 = 2709899) B2709899
theorem B2167067 : Blo 948586 2167067 := bstep (se 1 (by rfl) ⟨1625300, by rfl⟩ : syracuseStep 2167067 = 3250601) B3250601
theorem B2134619 : Blo 948586 2134619 := bstep (se 1 (by rfl) ⟨1600964, by rfl⟩ : syracuseStep 2134619 = 3201929) B3201929
theorem B7213697 : Blo 948586 7213697 := bstep (se 2 (by rfl) ⟨2705136, by rfl⟩ : syracuseStep 7213697 = 5410273) B5410273
theorem B4821767 : Blo 948586 4821767 := bstep (se 1 (by rfl) ⟨3616325, by rfl⟩ : syracuseStep 4821767 = 7232651) B7232651
theorem B3609431 : Blo 948586 3609431 := bstep (se 1 (by rfl) ⟨2707073, by rfl⟩ : syracuseStep 3609431 = 5414147) B5414147
theorem B5412005 : Blo 948586 5412005 := bstep (se 4 (by rfl) ⟨507375, by rfl⟩ : syracuseStep 5412005 = 1014751) B1014751
theorem B21960001 : Blo 948586 21960001 := bstep (se 2 (by rfl) ⟨8235000, by rfl⟩ : syracuseStep 21960001 = 16470001) B16470001
theorem B11540159 : Blo 948586 11540159 := bstep (se 1 (by rfl) ⟨8655119, by rfl⟩ : syracuseStep 11540159 = 17310239) B17310239
theorem B5412689 : Blo 948586 5412689 := bstep (se 2 (by rfl) ⟨2029758, by rfl⟩ : syracuseStep 5412689 = 4059517) B4059517
theorem B52795475 : Blo 948586 52795475 := bstep (se 1 (by rfl) ⟨39596606, by rfl⟩ : syracuseStep 52795475 = 79193213) B79193213
theorem B2136527 : Blo 948586 2136527 := bstep (se 1 (by rfl) ⟨1602395, by rfl⟩ : syracuseStep 2136527 = 3204791) B3204791
theorem B1711687 : Blo 948586 1711687 := bstep (se 1 (by rfl) ⟨1283765, by rfl⟩ : syracuseStep 1711687 = 2567531) B2567531
theorem B8134343 : Blo 948586 8134343 := bstep (se 1 (by rfl) ⟨6100757, by rfl⟩ : syracuseStep 8134343 = 12201515) B12201515
theorem B20520863 : Blo 948586 20520863 := bstep (se 1 (by rfl) ⟨15390647, by rfl⟩ : syracuseStep 20520863 = 30781295) B30781295
theorem B1646587 : Blo 948586 1646587 := bstep (se 1 (by rfl) ⟨1234940, by rfl⟩ : syracuseStep 1646587 = 2469881) B2469881
theorem B18260903 : Blo 948586 18260903 := bstep (se 1 (by rfl) ⟨13695677, by rfl⟩ : syracuseStep 18260903 = 27391355) B27391355
theorem B2892779 : Blo 948586 2892779 := bstep (se 1 (by rfl) ⟨2169584, by rfl⟩ : syracuseStep 2892779 = 4339169) B4339169
theorem B2139227 : Blo 948586 2139227 := bstep (se 1 (by rfl) ⟨1604420, by rfl⟩ : syracuseStep 2139227 = 3208841) B3208841
theorem B2172167 : Blo 948586 2172167 := bstep (se 1 (by rfl) ⟨1629125, by rfl⟩ : syracuseStep 2172167 = 3258251) B3258251
theorem B7219529 : Blo 948586 7219529 := bstep (se 2 (by rfl) ⟨2707323, by rfl⟩ : syracuseStep 7219529 = 5414647) B5414647
theorem B13183357 : Blo 948586 13183357 := bstep (se 3 (by rfl) ⟨2471879, by rfl⟩ : syracuseStep 13183357 = 4943759) B4943759
theorem B8137691 : Blo 948586 8137691 := bstep (se 1 (by rfl) ⟨6103268, by rfl⟩ : syracuseStep 8137691 = 12206537) B12206537
theorem B6171677 : Blo 948586 6171677 := bstep (se 3 (by rfl) ⟨1157189, by rfl⟩ : syracuseStep 6171677 = 2314379) B2314379
theorem B4631879 : Blo 948586 4631879 := bstep (se 1 (by rfl) ⟨3473909, by rfl⟩ : syracuseStep 4631879 = 6947819) B6947819
theorem B2141801 : Blo 948586 2141801 := bstep (se 2 (by rfl) ⟨803175, by rfl⟩ : syracuseStep 2141801 = 1606351) B1606351
theorem B2895551 : Blo 948586 2895551 := bstep (se 1 (by rfl) ⟨2171663, by rfl⟩ : syracuseStep 2895551 = 4343327) B4343327
theorem B1519487 : Blo 948586 1519487 := bstep (se 1 (by rfl) ⟨1139615, by rfl⟩ : syracuseStep 1519487 = 2279231) B2279231
theorem B2404687 : Blo 948586 2404687 := bstep (se 1 (by rfl) ⟨1803515, by rfl⟩ : syracuseStep 2404687 = 3607031) B3607031
theorem B2404799 : Blo 948586 2404799 := bstep (se 1 (by rfl) ⟨1803599, by rfl⟩ : syracuseStep 2404799 = 3607199) B3607199
theorem B10269341 : Blo 948586 10269341 := bstep (se 3 (by rfl) ⟨1925501, by rfl⟩ : syracuseStep 10269341 = 3851003) B3851003
theorem B19510159 : Blo 948586 19510159 := bstep (se 1 (by rfl) ⟨14632619, by rfl⟩ : syracuseStep 19510159 = 29265239) B29265239
theorem B2929657 : Blo 948586 2929657 := bstep (se 2 (by rfl) ⟨1098621, by rfl⟩ : syracuseStep 2929657 = 2197243) B2197243
theorem B3847355 : Blo 948586 3847355 := bstep (se 1 (by rfl) ⟨2885516, by rfl⟩ : syracuseStep 3847355 = 5771033) B5771033
theorem B1422953 : Blo 948586 1422953 := bstep (se 2 (by rfl) ⟨533607, by rfl⟩ : syracuseStep 1422953 = 1067215) B1067215
theorem B7321295 : Blo 948586 7321295 := bstep (se 1 (by rfl) ⟨5490971, by rfl⟩ : syracuseStep 7321295 = 10981943) B10981943
theorem B1423175 : Blo 948586 1423175 := bstep (se 1 (by rfl) ⟨1067381, by rfl⟩ : syracuseStep 1423175 = 2134763) B2134763
theorem B3422177 : Blo 948586 3422177 := bstep (se 2 (by rfl) ⟨1283316, by rfl⟩ : syracuseStep 3422177 = 2566633) B2566633
theorem B1423355 : Blo 948586 1423355 := bstep (se 1 (by rfl) ⟨1067516, by rfl⟩ : syracuseStep 1423355 = 2135033) B2135033
theorem B1423415 : Blo 948586 1423415 := bstep (se 1 (by rfl) ⟨1067561, by rfl⟩ : syracuseStep 1423415 = 2135123) B2135123
theorem B1423481 : Blo 948586 1423481 := bstep (se 2 (by rfl) ⟨533805, by rfl⟩ : syracuseStep 1423481 = 1067611) B1067611
theorem B1423487 : Blo 948586 1423487 := bstep (se 1 (by rfl) ⟨1067615, by rfl⟩ : syracuseStep 1423487 = 2135231) B2135231
theorem B1423535 : Blo 948586 1423535 := bstep (se 1 (by rfl) ⟨1067651, by rfl⟩ : syracuseStep 1423535 = 2135303) B2135303
theorem B1423775 : Blo 948586 1423775 := bstep (se 1 (by rfl) ⟨1067831, by rfl⟩ : syracuseStep 1423775 = 2135663) B2135663
theorem B7223903 : Blo 948586 7223903 := bstep (se 1 (by rfl) ⟨5417927, by rfl⟩ : syracuseStep 7223903 = 10835855) B10835855
theorem B422591093 : Blo 948586 422591093 := bstep (se 5 (by rfl) ⟨19808957, by rfl⟩ : syracuseStep 422591093 = 39617915) B39617915
theorem B2407391 : Blo 948586 2407391 := bstep (se 1 (by rfl) ⟨1805543, by rfl⟩ : syracuseStep 2407391 = 3611087) B3611087
theorem B12172295 : Blo 948586 12172295 := bstep (se 1 (by rfl) ⟨9129221, by rfl⟩ : syracuseStep 12172295 = 18258443) B18258443
theorem B3652769 : Blo 948586 3652769 := bstep (se 2 (by rfl) ⟨1369788, by rfl⟩ : syracuseStep 3652769 = 2739577) B2739577
theorem B1424873 : Blo 948586 1424873 := bstep (se 2 (by rfl) ⟨534327, by rfl⟩ : syracuseStep 1424873 = 1068655) B1068655
theorem B6864425 : Blo 948586 6864425 := bstep (se 2 (by rfl) ⟨2574159, by rfl⟩ : syracuseStep 6864425 = 5148319) B5148319
theorem B5423213 : Blo 948586 5423213 := bstep (se 3 (by rfl) ⟨1016852, by rfl⟩ : syracuseStep 5423213 = 2033705) B2033705
theorem B30818657 : Blo 948586 30818657 := bstep (se 2 (by rfl) ⟨11556996, by rfl⟩ : syracuseStep 30818657 = 23113993) B23113993
theorem B3653999 : Blo 948586 3653999 := bstep (se 1 (by rfl) ⟨2740499, by rfl⟩ : syracuseStep 3653999 = 5480999) B5480999
theorem B1425899 : Blo 948586 1425899 := bstep (se 1 (by rfl) ⟨1069424, by rfl⟩ : syracuseStep 1425899 = 2138849) B2138849
theorem B1426523 : Blo 948586 1426523 := bstep (se 1 (by rfl) ⟨1069892, by rfl⟩ : syracuseStep 1426523 = 2139785) B2139785
theorem B1426559 : Blo 948586 1426559 := bstep (se 1 (by rfl) ⟨1069919, by rfl⟩ : syracuseStep 1426559 = 2139839) B2139839
theorem B13714595 : Blo 948586 13714595 := bstep (se 1 (by rfl) ⟨10285946, by rfl⟩ : syracuseStep 13714595 = 20571893) B20571893
theorem B1426697 : Blo 948586 1426697 := bstep (se 2 (by rfl) ⟨535011, by rfl⟩ : syracuseStep 1426697 = 1070023) B1070023
theorem B1427177 : Blo 948586 1427177 := bstep (se 2 (by rfl) ⟨535191, by rfl⟩ : syracuseStep 1427177 = 1070383) B1070383
theorem B8898767 : Blo 948586 8898767 := bstep (se 1 (by rfl) ⟨6674075, by rfl⟩ : syracuseStep 8898767 = 13348151) B13348151
theorem B1427711 : Blo 948586 1427711 := bstep (se 1 (by rfl) ⟨1070783, by rfl⟩ : syracuseStep 1427711 = 2141567) B2141567
theorem B8112473 : Blo 948586 8112473 := bstep (se 2 (by rfl) ⟨3042177, by rfl⟩ : syracuseStep 8112473 = 6084355) B6084355
theorem B1427849 : Blo 948586 1427849 := bstep (se 2 (by rfl) ⟨535443, by rfl⟩ : syracuseStep 1427849 = 1070887) B1070887
theorem B3754721 : Blo 948586 3754721 := bstep (se 2 (by rfl) ⟨1408020, by rfl⟩ : syracuseStep 3754721 = 2816041) B2816041
theorem B1428347 : Blo 948586 1428347 := bstep (se 1 (by rfl) ⟨1071260, by rfl⟩ : syracuseStep 1428347 = 2142521) B2142521
theorem B1069087 : Blo 948586 1069087 := bstep (se 1 (by rfl) ⟨801815, by rfl⟩ : syracuseStep 1069087 = 1603631) B1603631
theorem B4117073 : Blo 948586 4117073 := bstep (se 2 (by rfl) ⟨1543902, by rfl⟩ : syracuseStep 4117073 = 3087805) B3087805
theorem B4117711 : Blo 948586 4117711 := bstep (se 1 (by rfl) ⟨3088283, by rfl⟩ : syracuseStep 4117711 = 6176567) B6176567
theorem B4805891 : Blo 948586 4805891 := bstep (se 1 (by rfl) ⟨3604418, by rfl⟩ : syracuseStep 4805891 = 7208837) B7208837
theorem B3298931 : Blo 948586 3298931 := bstep (se 1 (by rfl) ⟨2474198, by rfl⟩ : syracuseStep 3298931 = 4948397) B4948397
theorem B1005535 : Blo 948586 1005535 := bstep (se 1 (by rfl) ⟨754151, by rfl⟩ : syracuseStep 1005535 = 1508303) B1508303
theorem B7231679 : Blo 948586 7231679 := bstep (se 1 (by rfl) ⟨5423759, by rfl⟩ : syracuseStep 7231679 = 10847519) B10847519
theorem B7232165 : Blo 948586 7232165 := bstep (se 4 (by rfl) ⟨678015, by rfl⟩ : syracuseStep 7232165 = 1356031) B1356031
theorem B3300383 : Blo 948586 3300383 := bstep (se 1 (by rfl) ⟨2475287, by rfl⟩ : syracuseStep 3300383 = 4950575) B4950575
theorem B5496445 : Blo 948586 5496445 := bstep (se 3 (by rfl) ⟨1030583, by rfl⟩ : syracuseStep 5496445 = 2061167) B2061167
theorem B3203063 : Blo 948586 3203063 := bstep (se 1 (by rfl) ⟨2402297, by rfl⟩ : syracuseStep 3203063 = 4804595) B4804595
theorem B4055143 : Blo 948586 4055143 := bstep (se 1 (by rfl) ⟨3041357, by rfl⟩ : syracuseStep 4055143 = 6082715) B6082715
theorem B3204143 : Blo 948586 3204143 := bstep (se 1 (by rfl) ⟨2403107, by rfl⟩ : syracuseStep 3204143 = 4806215) B4806215
theorem B5792903 : Blo 948586 5792903 := bstep (se 1 (by rfl) ⟨4344677, by rfl⟩ : syracuseStep 5792903 = 8689355) B8689355
theorem B3204251 : Blo 948586 3204251 := bstep (se 1 (by rfl) ⟨2403188, by rfl⟩ : syracuseStep 3204251 = 4806377) B4806377
theorem B13001957 : Blo 948586 13001957 := bstep (se 4 (by rfl) ⟨1218933, by rfl⟩ : syracuseStep 13001957 = 2437867) B2437867
theorem B3204521 : Blo 948586 3204521 := bstep (se 2 (by rfl) ⟨1201695, by rfl⟩ : syracuseStep 3204521 = 2403391) B2403391
theorem B7038415 : Blo 948586 7038415 := bstep (se 1 (by rfl) ⟨5278811, by rfl⟩ : syracuseStep 7038415 = 10557623) B10557623
theorem B2058335 : Blo 948586 2058335 := bstep (se 1 (by rfl) ⟨1543751, by rfl⟩ : syracuseStep 2058335 = 3087503) B3087503
theorem B6089327 : Blo 948586 6089327 := bstep (se 1 (by rfl) ⟨4566995, by rfl⟩ : syracuseStep 6089327 = 9133991) B9133991
theorem B3041999 : Blo 948586 3041999 := bstep (se 1 (by rfl) ⟨2281499, by rfl⟩ : syracuseStep 3041999 = 4562999) B4562999
theorem B3206141 : Blo 948586 3206141 := bstep (se 3 (by rfl) ⟨601151, by rfl⟩ : syracuseStep 3206141 = 1202303) B1202303
theorem B7203977 : Blo 948586 7203977 := bstep (se 2 (by rfl) ⟨2701491, by rfl⟩ : syracuseStep 7203977 = 5402983) B5402983
theorem B44462287 : Blo 948586 44462287 := bstep (se 1 (by rfl) ⟨33346715, by rfl⟩ : syracuseStep 44462287 = 66693431) B66693431
theorem B3207383 : Blo 948586 3207383 := bstep (se 1 (by rfl) ⟨2405537, by rfl⟩ : syracuseStep 3207383 = 4811075) B4811075
theorem B4813181 : Blo 948586 4813181 := bstep (se 3 (by rfl) ⟨902471, by rfl⟩ : syracuseStep 4813181 = 1804943) B1804943
theorem B2028169 : Blo 948586 2028169 := bstep (se 2 (by rfl) ⟨760563, by rfl⟩ : syracuseStep 2028169 = 1521127) B1521127
theorem B10843145 : Blo 948586 10843145 := bstep (se 2 (by rfl) ⟨4066179, by rfl⟩ : syracuseStep 10843145 = 8132359) B8132359
theorem B7205921 : Blo 948586 7205921 := bstep (se 2 (by rfl) ⟨2702220, by rfl⟩ : syracuseStep 7205921 = 5404441) B5404441
theorem B10811069 : Blo 948586 10811069 := bstep (se 3 (by rfl) ⟨2027075, by rfl⟩ : syracuseStep 10811069 = 4054151) B4054151
theorem B3209057 : Blo 948586 3209057 := bstep (se 2 (by rfl) ⟨1203396, by rfl⟩ : syracuseStep 3209057 = 2406793) B2406793
theorem B3209435 : Blo 948586 3209435 := bstep (se 1 (by rfl) ⟨2407076, by rfl⟩ : syracuseStep 3209435 = 4814153) B4814153
theorem B15399335 : Blo 948586 15399335 := bstep (se 1 (by rfl) ⟨11549501, by rfl⟩ : syracuseStep 15399335 = 23099003) B23099003
theorem B1604009 : Blo 948586 1604009 := bstep (se 2 (by rfl) ⟨601503, by rfl⟩ : syracuseStep 1604009 = 1203007) B1203007
theorem B948703 : Blo 948586 948703 := bstep (se 1 (by rfl) ⟨711527, by rfl⟩ : syracuseStep 948703 = 1423055) B1423055
theorem B1604063 : Blo 948586 1604063 := bstep (se 1 (by rfl) ⟨1203047, by rfl⟩ : syracuseStep 1604063 = 2406095) B2406095
theorem B948839 : Blo 948586 948839 := bstep (se 1 (by rfl) ⟨711629, by rfl⟩ : syracuseStep 948839 = 1423259) B1423259
theorem B41613929 : Blo 948586 41613929 := bstep (se 2 (by rfl) ⟨15605223, by rfl⟩ : syracuseStep 41613929 = 31210447) B31210447
theorem B948863 : Blo 948586 948863 := bstep (se 1 (by rfl) ⟨711647, by rfl⟩ : syracuseStep 948863 = 1423295) B1423295
theorem B948975 : Blo 948586 948975 := bstep (se 1 (by rfl) ⟨711731, by rfl⟩ : syracuseStep 948975 = 1423463) B1423463
theorem B3603311 : Blo 948586 3603311 := bstep (se 1 (by rfl) ⟨2702483, by rfl⟩ : syracuseStep 3603311 = 5404967) B5404967
theorem B4815773 : Blo 948586 4815773 := bstep (se 3 (by rfl) ⟨902957, by rfl⟩ : syracuseStep 4815773 = 1805915) B1805915
theorem B949231 : Blo 948586 949231 := bstep (se 1 (by rfl) ⟨711923, by rfl⟩ : syracuseStep 949231 = 1423847) B1423847
theorem B949279 : Blo 948586 949279 := bstep (se 1 (by rfl) ⟨711959, by rfl⟩ : syracuseStep 949279 = 1423919) B1423919
theorem B3210299 : Blo 948586 3210299 := bstep (se 1 (by rfl) ⟨2407724, by rfl⟩ : syracuseStep 3210299 = 4815449) B4815449
theorem B949727 : Blo 948586 949727 := bstep (se 1 (by rfl) ⟨712295, by rfl⟩ : syracuseStep 949727 = 1424591) B1424591
theorem B949787 : Blo 948586 949787 := bstep (se 1 (by rfl) ⟨712340, by rfl⟩ : syracuseStep 949787 = 1424681) B1424681
theorem B949807 : Blo 948586 949807 := bstep (se 1 (by rfl) ⟨712355, by rfl⟩ : syracuseStep 949807 = 1424711) B1424711
theorem B1605467 : Blo 948586 1605467 := bstep (se 1 (by rfl) ⟨1204100, by rfl⟩ : syracuseStep 1605467 = 2408201) B2408201
theorem B1605487 : Blo 948586 1605487 := bstep (se 1 (by rfl) ⟨1204115, by rfl⟩ : syracuseStep 1605487 = 2408231) B2408231
theorem B16482203 : Blo 948586 16482203 := bstep (se 1 (by rfl) ⟨12361652, by rfl⟩ : syracuseStep 16482203 = 24723305) B24723305
theorem B6094759 : Blo 948586 6094759 := bstep (se 1 (by rfl) ⟨4571069, by rfl⟩ : syracuseStep 6094759 = 9142139) B9142139
theorem B950207 : Blo 948586 950207 := bstep (se 1 (by rfl) ⟨712655, by rfl⟩ : syracuseStep 950207 = 1425311) B1425311
theorem B950267 : Blo 948586 950267 := bstep (se 1 (by rfl) ⟨712700, by rfl⟩ : syracuseStep 950267 = 1425401) B1425401
theorem B5406857 : Blo 948586 5406857 := bstep (se 2 (by rfl) ⟨2027571, by rfl⟩ : syracuseStep 5406857 = 4055143) B4055143
theorem B20545771 : Blo 948586 20545771 := bstep (se 1 (by rfl) ⟨15409328, by rfl⟩ : syracuseStep 20545771 = 30818657) B30818657
theorem B950599 : Blo 948586 950599 := bstep (se 1 (by rfl) ⟨712949, by rfl⟩ : syracuseStep 950599 = 1425899) B1425899
theorem B951015 : Blo 948586 951015 := bstep (se 1 (by rfl) ⟨713261, by rfl⟩ : syracuseStep 951015 = 1426523) B1426523
theorem B3212027 : Blo 948586 3212027 := bstep (se 1 (by rfl) ⟨2409020, by rfl⟩ : syracuseStep 3212027 = 4818041) B4818041
theorem B951039 : Blo 948586 951039 := bstep (se 1 (by rfl) ⟨713279, by rfl⟩ : syracuseStep 951039 = 1426559) B1426559
theorem B9143063 : Blo 948586 9143063 := bstep (se 1 (by rfl) ⟨6857297, by rfl⟩ : syracuseStep 9143063 = 13714595) B13714595
theorem B951131 : Blo 948586 951131 := bstep (se 1 (by rfl) ⟨713348, by rfl⟩ : syracuseStep 951131 = 1426697) B1426697
theorem B951451 : Blo 948586 951451 := bstep (se 1 (by rfl) ⟨713588, by rfl⟩ : syracuseStep 951451 = 1427177) B1427177
theorem B5932511 : Blo 948586 5932511 := bstep (se 1 (by rfl) ⟨4449383, by rfl⟩ : syracuseStep 5932511 = 8898767) B8898767
theorem B951807 : Blo 948586 951807 := bstep (se 1 (by rfl) ⟨713855, by rfl⟩ : syracuseStep 951807 = 1427711) B1427711
theorem B10978861 : Blo 948586 10978861 := bstep (se 3 (by rfl) ⟨2058536, by rfl⟩ : syracuseStep 10978861 = 4117073) B4117073
theorem B5408315 : Blo 948586 5408315 := bstep (se 1 (by rfl) ⟨4056236, by rfl⟩ : syracuseStep 5408315 = 8112473) B8112473
theorem B951899 : Blo 948586 951899 := bstep (se 1 (by rfl) ⟨713924, by rfl⟩ : syracuseStep 951899 = 1427849) B1427849
theorem B3212891 : Blo 948586 3212891 := bstep (se 1 (by rfl) ⟨2409668, by rfl⟩ : syracuseStep 3212891 = 4819337) B4819337
theorem B952231 : Blo 948586 952231 := bstep (se 1 (by rfl) ⟨714173, by rfl⟩ : syracuseStep 952231 = 1428347) B1428347
theorem B2164943 : Blo 948586 2164943 := bstep (se 1 (by rfl) ⟨1623707, by rfl⟩ : syracuseStep 2164943 = 3247415) B3247415
theorem B7211753 : Blo 948586 7211753 := bstep (se 2 (by rfl) ⟨2704407, by rfl⟩ : syracuseStep 7211753 = 5408815) B5408815
theorem B1444711 : Blo 948586 1444711 := bstep (se 1 (by rfl) ⟨1083533, by rfl⟩ : syracuseStep 1444711 = 2167067) B2167067
theorem B3214511 : Blo 948586 3214511 := bstep (se 1 (by rfl) ⟨2410883, by rfl⟩ : syracuseStep 3214511 = 4821767) B4821767
theorem B10816901 : Blo 948586 10816901 := bstep (se 4 (by rfl) ⟨1014084, by rfl⟩ : syracuseStep 10816901 = 2028169) B2028169
theorem B3608003 : Blo 948586 3608003 := bstep (se 1 (by rfl) ⟨2706002, by rfl⟩ : syracuseStep 3608003 = 5412005) B5412005
theorem B2199287 : Blo 948586 2199287 := bstep (se 1 (by rfl) ⟨1649465, by rfl⟩ : syracuseStep 2199287 = 3298931) B3298931
theorem B3608459 : Blo 948586 3608459 := bstep (se 1 (by rfl) ⟨2706344, by rfl⟩ : syracuseStep 3608459 = 5412689) B5412689
theorem B35196983 : Blo 948586 35196983 := bstep (se 1 (by rfl) ⟨26397737, by rfl⟩ : syracuseStep 35196983 = 52795475) B52795475
theorem B4821119 : Blo 948586 4821119 := bstep (se 1 (by rfl) ⟨3615839, by rfl⟩ : syracuseStep 4821119 = 7231679) B7231679
theorem B4821443 : Blo 948586 4821443 := bstep (se 1 (by rfl) ⟨3616082, by rfl⟩ : syracuseStep 4821443 = 7232165) B7232165
theorem B2200255 : Blo 948586 2200255 := bstep (se 1 (by rfl) ⟨1650191, by rfl⟩ : syracuseStep 2200255 = 3300383) B3300383
theorem B2135375 : Blo 948586 2135375 := bstep (se 1 (by rfl) ⟨1601531, by rfl⟩ : syracuseStep 2135375 = 3203063) B3203063
theorem B2136095 : Blo 948586 2136095 := bstep (se 1 (by rfl) ⟨1602071, by rfl⟩ : syracuseStep 2136095 = 3204143) B3204143
theorem B2136167 : Blo 948586 2136167 := bstep (se 1 (by rfl) ⟨1602125, by rfl⟩ : syracuseStep 2136167 = 3204251) B3204251
theorem B1448111 : Blo 948586 1448111 := bstep (se 1 (by rfl) ⟨1086083, by rfl⟩ : syracuseStep 1448111 = 2172167) B2172167
theorem B2136347 : Blo 948586 2136347 := bstep (se 1 (by rfl) ⟨1602260, by rfl⟩ : syracuseStep 2136347 = 3204521) B3204521
theorem B3906209 : Blo 948586 3906209 := bstep (se 2 (by rfl) ⟨1464828, by rfl⟩ : syracuseStep 3906209 = 2929657) B2929657
theorem B2137427 : Blo 948586 2137427 := bstep (se 1 (by rfl) ⟨1603070, by rfl⟩ : syracuseStep 2137427 = 3206141) B3206141
theorem B3087919 : Blo 948586 3087919 := bstep (se 1 (by rfl) ⟨2315939, by rfl⟩ : syracuseStep 3087919 = 4631879) B4631879
theorem B2138255 : Blo 948586 2138255 := bstep (se 1 (by rfl) ⟨1603691, by rfl⟩ : syracuseStep 2138255 = 3207383) B3207383
theorem B2564903 : Blo 948586 2564903 := bstep (se 1 (by rfl) ⟨1923677, by rfl⟩ : syracuseStep 2564903 = 3847355) B3847355
theorem B2139371 : Blo 948586 2139371 := bstep (se 1 (by rfl) ⟨1604528, by rfl⟩ : syracuseStep 2139371 = 3209057) B3209057
theorem B2139623 : Blo 948586 2139623 := bstep (se 1 (by rfl) ⟨1604717, by rfl⟩ : syracuseStep 2139623 = 3209435) B3209435
theorem B10266223 : Blo 948586 10266223 := bstep (se 1 (by rfl) ⟨7699667, by rfl⟩ : syracuseStep 10266223 = 15399335) B15399335
theorem B2402207 : Blo 948586 2402207 := bstep (se 1 (by rfl) ⟨1801655, by rfl⟩ : syracuseStep 2402207 = 3603311) B3603311
theorem B2140199 : Blo 948586 2140199 := bstep (se 1 (by rfl) ⟨1605149, by rfl⟩ : syracuseStep 2140199 = 3210299) B3210299
theorem B2435179 : Blo 948586 2435179 := bstep (se 1 (by rfl) ⟨1826384, by rfl⟩ : syracuseStep 2435179 = 3652769) B3652769
theorem B2140649 : Blo 948586 2140649 := bstep (se 2 (by rfl) ⟨802743, by rfl⟩ : syracuseStep 2140649 = 1605487) B1605487
theorem B10988135 : Blo 948586 10988135 := bstep (se 1 (by rfl) ⟨8241101, by rfl⟩ : syracuseStep 10988135 = 16482203) B16482203
theorem B43821739 : Blo 948586 43821739 := bstep (se 1 (by rfl) ⟨32866304, by rfl⟩ : syracuseStep 43821739 = 65732609) B65732609
theorem B3615475 : Blo 948586 3615475 := bstep (se 1 (by rfl) ⟨2711606, by rfl⟩ : syracuseStep 3615475 = 5423213) B5423213
theorem B2435999 : Blo 948586 2435999 := bstep (se 1 (by rfl) ⟨1826999, by rfl⟩ : syracuseStep 2435999 = 3653999) B3653999
theorem B2141513 : Blo 948586 2141513 := bstep (se 2 (by rfl) ⟨803067, by rfl⟩ : syracuseStep 2141513 = 1606135) B1606135
theorem B2141531 : Blo 948586 2141531 := bstep (se 1 (by rfl) ⟨1606148, by rfl⟩ : syracuseStep 2141531 = 3212297) B3212297
theorem B2142035 : Blo 948586 2142035 := bstep (se 1 (by rfl) ⟨1606526, by rfl⟩ : syracuseStep 2142035 = 3213053) B3213053
theorem B5418839 : Blo 948586 5418839 := bstep (se 1 (by rfl) ⟨4064129, by rfl⟩ : syracuseStep 5418839 = 8128259) B8128259
theorem B9744239 : Blo 948586 9744239 := bstep (se 1 (by rfl) ⟨7308179, by rfl⟩ : syracuseStep 9744239 = 14616359) B14616359
theorem B962975 : Blo 948586 962975 := bstep (se 1 (by rfl) ⟨722231, by rfl⟩ : syracuseStep 962975 = 1444463) B1444463
theorem B2503147 : Blo 948586 2503147 := bstep (se 1 (by rfl) ⟨1877360, by rfl⟩ : syracuseStep 2503147 = 3754721) B3754721
theorem B9384553 : Blo 948586 9384553 := bstep (se 2 (by rfl) ⟨3519207, by rfl⟩ : syracuseStep 9384553 = 7038415) B7038415
theorem B3912475 : Blo 948586 3912475 := bstep (se 1 (by rfl) ⟨2934356, by rfl⟩ : syracuseStep 3912475 = 5868713) B5868713
theorem B2405497 : Blo 948586 2405497 := bstep (se 2 (by rfl) ⟨902061, by rfl⟩ : syracuseStep 2405497 = 1804123) B1804123
theorem B1423079 : Blo 948586 1423079 := bstep (se 1 (by rfl) ⟨1067309, by rfl⟩ : syracuseStep 1423079 = 2134619) B2134619
theorem B17577809 : Blo 948586 17577809 := bstep (se 2 (by rfl) ⟨6591678, by rfl⟩ : syracuseStep 17577809 = 13183357) B13183357
theorem B2406287 : Blo 948586 2406287 := bstep (se 1 (by rfl) ⟨1804715, by rfl⟩ : syracuseStep 2406287 = 3609431) B3609431
theorem B1424351 : Blo 948586 1424351 := bstep (se 1 (by rfl) ⟨1068263, by rfl⟩ : syracuseStep 1424351 = 2136527) B2136527
theorem B5422895 : Blo 948586 5422895 := bstep (se 1 (by rfl) ⟨4067171, by rfl⟩ : syracuseStep 5422895 = 8134343) B8134343
theorem B13680575 : Blo 948586 13680575 := bstep (se 1 (by rfl) ⟨10260431, by rfl⟩ : syracuseStep 13680575 = 20520863) B20520863
theorem B1425449 : Blo 948586 1425449 := bstep (se 2 (by rfl) ⟨534543, by rfl⟩ : syracuseStep 1425449 = 1069087) B1069087
theorem B12173935 : Blo 948586 12173935 := bstep (se 1 (by rfl) ⟨9130451, by rfl⟩ : syracuseStep 12173935 = 18260903) B18260903
theorem B1426151 : Blo 948586 1426151 := bstep (se 1 (by rfl) ⟨1069613, by rfl⟩ : syracuseStep 1426151 = 2139227) B2139227
theorem B8667971 : Blo 948586 8667971 := bstep (se 1 (by rfl) ⟨6500978, by rfl⟩ : syracuseStep 8667971 = 13001957) B13001957
theorem B5490281 : Blo 948586 5490281 := bstep (se 2 (by rfl) ⟨2058855, by rfl⟩ : syracuseStep 5490281 = 4117711) B4117711
theorem B29280001 : Blo 948586 29280001 := bstep (se 2 (by rfl) ⟨10980000, by rfl⟩ : syracuseStep 29280001 = 21960001) B21960001
theorem B5425127 : Blo 948586 5425127 := bstep (se 1 (by rfl) ⟨4068845, by rfl⟩ : syracuseStep 5425127 = 8137691) B8137691
theorem B4114451 : Blo 948586 4114451 := bstep (se 1 (by rfl) ⟨3085838, by rfl⟩ : syracuseStep 4114451 = 6171677) B6171677
theorem B4802651 : Blo 948586 4802651 := bstep (se 1 (by rfl) ⟨3601988, by rfl⟩ : syracuseStep 4802651 = 7203977) B7203977
theorem B1427867 : Blo 948586 1427867 := bstep (se 1 (by rfl) ⟨1070900, by rfl⟩ : syracuseStep 1427867 = 2141801) B2141801
theorem B7228763 : Blo 948586 7228763 := bstep (se 1 (by rfl) ⟨5421572, by rfl⟩ : syracuseStep 7228763 = 10843145) B10843145
theorem B4803947 : Blo 948586 4803947 := bstep (se 1 (by rfl) ⟨3602960, by rfl⟩ : syracuseStep 4803947 = 7205921) B7205921
theorem B2281451 : Blo 948586 2281451 := bstep (se 1 (by rfl) ⟨1711088, by rfl⟩ : syracuseStep 2281451 = 3422177) B3422177
theorem B1069339 : Blo 948586 1069339 := bstep (se 1 (by rfl) ⟨802004, by rfl⟩ : syracuseStep 1069339 = 1604009) B1604009
theorem B1069375 : Blo 948586 1069375 := bstep (se 1 (by rfl) ⟨802031, by rfl⟩ : syracuseStep 1069375 = 1604063) B1604063
theorem B27742619 : Blo 948586 27742619 := bstep (se 1 (by rfl) ⟨20806964, by rfl⟩ : syracuseStep 27742619 = 41613929) B41613929
theorem B281727395 : Blo 948586 281727395 := bstep (se 1 (by rfl) ⟨211295546, by rfl⟩ : syracuseStep 281727395 = 422591093) B422591093
theorem B8114863 : Blo 948586 8114863 := bstep (se 1 (by rfl) ⟨6086147, by rfl⟩ : syracuseStep 8114863 = 12172295) B12172295
theorem B2282249 : Blo 948586 2282249 := bstep (se 2 (by rfl) ⟨855843, by rfl⟩ : syracuseStep 2282249 = 1711687) B1711687
theorem B7328593 : Blo 948586 7328593 := bstep (se 2 (by rfl) ⟨2748222, by rfl⟩ : syracuseStep 7328593 = 5496445) B5496445
theorem B4576283 : Blo 948586 4576283 := bstep (se 1 (by rfl) ⟨3432212, by rfl⟩ : syracuseStep 4576283 = 6864425) B6864425
theorem B1070311 : Blo 948586 1070311 := bstep (se 1 (by rfl) ⟨802733, by rfl⟩ : syracuseStep 1070311 = 1605467) B1605467
theorem B2381239 : Blo 948586 2381239 := bstep (se 1 (by rfl) ⟨1785929, by rfl⟩ : syracuseStep 2381239 = 3571859) B3571859
theorem B7821431 : Blo 948586 7821431 := bstep (se 1 (by rfl) ⟨5866073, by rfl⟩ : syracuseStep 7821431 = 11732147) B11732147
theorem B2709625 : Blo 948586 2709625 := bstep (se 2 (by rfl) ⟨1016109, by rfl⟩ : syracuseStep 2709625 = 2032219) B2032219
theorem B237132197 : Blo 948586 237132197 := bstep (se 4 (by rfl) ⟨22231143, by rfl⟩ : syracuseStep 237132197 = 44462287) B44462287
theorem B2645183 : Blo 948586 2645183 := bstep (se 1 (by rfl) ⟨1983887, by rfl⟩ : syracuseStep 2645183 = 3967775) B3967775
theorem B1204399 : Blo 948586 1204399 := bstep (se 1 (by rfl) ⟨903299, by rfl⟩ : syracuseStep 1204399 = 1806599) B1806599
theorem B4808969 : Blo 948586 4808969 := bstep (se 2 (by rfl) ⟨1803363, by rfl⟩ : syracuseStep 4808969 = 3606727) B3606727
theorem B4809131 : Blo 948586 4809131 := bstep (se 1 (by rfl) ⟨3606848, by rfl⟩ : syracuseStep 4809131 = 7213697) B7213697
theorem B13722209 : Blo 948586 13722209 := bstep (se 2 (by rfl) ⟨5145828, by rfl⟩ : syracuseStep 13722209 = 10291657) B10291657
theorem B3203927 : Blo 948586 3203927 := bstep (se 1 (by rfl) ⟨2402945, by rfl⟩ : syracuseStep 3203927 = 4805891) B4805891
theorem B47539061 : Blo 948586 47539061 := bstep (se 5 (by rfl) ⟨2228393, by rfl⟩ : syracuseStep 47539061 = 4456787) B4456787
theorem B7693439 : Blo 948586 7693439 := bstep (se 1 (by rfl) ⟨5770079, by rfl⟩ : syracuseStep 7693439 = 11540159) B11540159
theorem B4810913 : Blo 948586 4810913 := bstep (se 2 (by rfl) ⟨1804092, by rfl⟩ : syracuseStep 4810913 = 3608185) B3608185
theorem B3206249 : Blo 948586 3206249 := bstep (se 2 (by rfl) ⟨1202343, by rfl⟩ : syracuseStep 3206249 = 2404687) B2404687
theorem B1928519 : Blo 948586 1928519 := bstep (se 1 (by rfl) ⟨1446389, by rfl⟩ : syracuseStep 1928519 = 2892779) B2892779
theorem B3861935 : Blo 948586 3861935 := bstep (se 1 (by rfl) ⟨2896451, by rfl⟩ : syracuseStep 3861935 = 5792903) B5792903
theorem B26013545 : Blo 948586 26013545 := bstep (se 2 (by rfl) ⟨9755079, by rfl⟩ : syracuseStep 26013545 = 19510159) B19510159
theorem B1372223 : Blo 948586 1372223 := bstep (se 1 (by rfl) ⟨1029167, by rfl⟩ : syracuseStep 1372223 = 2058335) B2058335
theorem B4813019 : Blo 948586 4813019 := bstep (se 1 (by rfl) ⟨3609764, by rfl⟩ : syracuseStep 4813019 = 7219529) B7219529
theorem B4059551 : Blo 948586 4059551 := bstep (se 1 (by rfl) ⟨3044663, by rfl⟩ : syracuseStep 4059551 = 6089327) B6089327
theorem B2027999 : Blo 948586 2027999 := bstep (se 1 (by rfl) ⟨1520999, by rfl⟩ : syracuseStep 2027999 = 3041999) B3041999
theorem B1930367 : Blo 948586 1930367 := bstep (se 1 (by rfl) ⟨1447775, by rfl⟩ : syracuseStep 1930367 = 2895551) B2895551
theorem B1012991 : Blo 948586 1012991 := bstep (se 1 (by rfl) ⟨759743, by rfl⟩ : syracuseStep 1012991 = 1519487) B1519487
theorem B1340713 : Blo 948586 1340713 := bstep (se 2 (by rfl) ⟨502767, by rfl⟩ : syracuseStep 1340713 = 1005535) B1005535
theorem B3208787 : Blo 948586 3208787 := bstep (se 1 (by rfl) ⟨2406590, by rfl⟩ : syracuseStep 3208787 = 4813181) B4813181
theorem B1603199 : Blo 948586 1603199 := bstep (se 1 (by rfl) ⟨1202399, by rfl⟩ : syracuseStep 1603199 = 2404799) B2404799
theorem B6846227 : Blo 948586 6846227 := bstep (se 1 (by rfl) ⟨5134670, by rfl⟩ : syracuseStep 6846227 = 10269341) B10269341
theorem B948635 : Blo 948586 948635 := bstep (se 1 (by rfl) ⟨711476, by rfl⟩ : syracuseStep 948635 = 1422953) B1422953
theorem B7207379 : Blo 948586 7207379 := bstep (se 1 (by rfl) ⟨5405534, by rfl⟩ : syracuseStep 7207379 = 10811069) B10811069
theorem B4880863 : Blo 948586 4880863 := bstep (se 1 (by rfl) ⟨3660647, by rfl⟩ : syracuseStep 4880863 = 7321295) B7321295
theorem B948783 : Blo 948586 948783 := bstep (se 1 (by rfl) ⟨711587, by rfl⟩ : syracuseStep 948783 = 1423175) B1423175
theorem B948903 : Blo 948586 948903 := bstep (se 1 (by rfl) ⟨711677, by rfl⟩ : syracuseStep 948903 = 1423355) B1423355
theorem B948943 : Blo 948586 948943 := bstep (se 1 (by rfl) ⟨711707, by rfl⟩ : syracuseStep 948943 = 1423415) B1423415
theorem B948987 : Blo 948586 948987 := bstep (se 1 (by rfl) ⟨711740, by rfl⟩ : syracuseStep 948987 = 1423481) B1423481
theorem B948991 : Blo 948586 948991 := bstep (se 1 (by rfl) ⟨711743, by rfl⟩ : syracuseStep 948991 = 1423487) B1423487
theorem B949023 : Blo 948586 949023 := bstep (se 1 (by rfl) ⟨711767, by rfl⟩ : syracuseStep 949023 = 1423535) B1423535
theorem B949183 : Blo 948586 949183 := bstep (se 1 (by rfl) ⟨711887, by rfl⟩ : syracuseStep 949183 = 1423775) B1423775
theorem B4815935 : Blo 948586 4815935 := bstep (se 1 (by rfl) ⟨3611951, by rfl⟩ : syracuseStep 4815935 = 7223903) B7223903
theorem B3210515 : Blo 948586 3210515 := bstep (se 1 (by rfl) ⟨2407886, by rfl⟩ : syracuseStep 3210515 = 4815773) B4815773
theorem B1604927 : Blo 948586 1604927 := bstep (se 1 (by rfl) ⟨1203695, by rfl⟩ : syracuseStep 1604927 = 2407391) B2407391
theorem B949915 : Blo 948586 949915 := bstep (se 1 (by rfl) ⟨712436, by rfl⟩ : syracuseStep 949915 = 1424873) B1424873
theorem B8126345 : Blo 948586 8126345 := bstep (se 2 (by rfl) ⟨3047379, by rfl⟩ : syracuseStep 8126345 = 6094759) B6094759
theorem B8781797 : Blo 948586 8781797 := bstep (se 4 (by rfl) ⟨823293, by rfl⟩ : syracuseStep 8781797 = 1646587) B1646587
theorem B950299 : Blo 948586 950299 := bstep (se 1 (by rfl) ⟨712724, by rfl⟩ : syracuseStep 950299 = 1425449) B1425449
theorem B3604571 : Blo 948586 3604571 := bstep (se 1 (by rfl) ⟨2703428, by rfl⟩ : syracuseStep 3604571 = 5406857) B5406857
theorem B1605865 : Blo 948586 1605865 := bstep (se 2 (by rfl) ⟨602199, by rfl⟩ : syracuseStep 1605865 = 1204399) B1204399
theorem B27394361 : Blo 948586 27394361 := bstep (se 2 (by rfl) ⟨10272885, by rfl⟩ : syracuseStep 27394361 = 20545771) B20545771
theorem B950767 : Blo 948586 950767 := bstep (se 1 (by rfl) ⟨713075, by rfl⟩ : syracuseStep 950767 = 1426151) B1426151
theorem B6095375 : Blo 948586 6095375 := bstep (se 1 (by rfl) ⟨4571531, by rfl⟩ : syracuseStep 6095375 = 9143063) B9143063
theorem B3605543 : Blo 948586 3605543 := bstep (se 1 (by rfl) ⟨2704157, by rfl⟩ : syracuseStep 3605543 = 5408315) B5408315
theorem B1443295 : Blo 948586 1443295 := bstep (se 1 (by rfl) ⟨1082471, by rfl⟩ : syracuseStep 1443295 = 2164943) B2164943
theorem B951911 : Blo 948586 951911 := bstep (se 1 (by rfl) ⟨713933, by rfl⟩ : syracuseStep 951911 = 1427867) B1427867
theorem B4819175 : Blo 948586 4819175 := bstep (se 1 (by rfl) ⟨3614381, by rfl⟩ : syracuseStep 4819175 = 7228763) B7228763
theorem B7211267 : Blo 948586 7211267 := bstep (se 1 (by rfl) ⟨5408450, by rfl⟩ : syracuseStep 7211267 = 10816901) B10816901
theorem B23464655 : Blo 948586 23464655 := bstep (se 1 (by rfl) ⟨17598491, by rfl⟩ : syracuseStep 23464655 = 35196983) B35196983
theorem B3214079 : Blo 948586 3214079 := bstep (se 1 (by rfl) ⟨2410559, by rfl⟩ : syracuseStep 3214079 = 4821119) B4821119
theorem B3246905 : Blo 948586 3246905 := bstep (se 2 (by rfl) ⟨1217589, by rfl⟩ : syracuseStep 3246905 = 2435179) B2435179
theorem B3214295 : Blo 948586 3214295 := bstep (se 1 (by rfl) ⟨2410721, by rfl⟩ : syracuseStep 3214295 = 4821443) B4821443
theorem B20515837 : Blo 948586 20515837 := bstep (se 3 (by rfl) ⟨3846719, by rfl⟩ : syracuseStep 20515837 = 7693439) B7693439
theorem B3050855 : Blo 948586 3050855 := bstep (se 1 (by rfl) ⟨2288141, by rfl⟩ : syracuseStep 3050855 = 4576283) B4576283
theorem B58428985 : Blo 948586 58428985 := bstep (se 2 (by rfl) ⟨21910869, by rfl⟩ : syracuseStep 58428985 = 43821739) B43821739
theorem B4820633 : Blo 948586 4820633 := bstep (se 2 (by rfl) ⟨1807737, by rfl⟩ : syracuseStep 4820633 = 3615475) B3615475
theorem B5214287 : Blo 948586 5214287 := bstep (se 1 (by rfl) ⟨3910715, by rfl⟩ : syracuseStep 5214287 = 7821431) B7821431
theorem B9148139 : Blo 948586 9148139 := bstep (se 1 (by rfl) ⟨6861104, by rfl⟩ : syracuseStep 9148139 = 13722209) B13722209
theorem B2135951 : Blo 948586 2135951 := bstep (se 1 (by rfl) ⟨1601963, by rfl⟩ : syracuseStep 2135951 = 3203927) B3203927
theorem B31692707 : Blo 948586 31692707 := bstep (se 1 (by rfl) ⟨23769530, by rfl⟩ : syracuseStep 31692707 = 47539061) B47539061
theorem B10819817 : Blo 948586 10819817 := bstep (se 2 (by rfl) ⟨4057431, by rfl⟩ : syracuseStep 10819817 = 8114863) B8114863
theorem B5216633 : Blo 948586 5216633 := bstep (se 2 (by rfl) ⟨1956237, by rfl⟩ : syracuseStep 5216633 = 3912475) B3912475
theorem B9771457 : Blo 948586 9771457 := bstep (se 2 (by rfl) ⟨3664296, by rfl⟩ : syracuseStep 9771457 = 7328593) B7328593
theorem B2137499 : Blo 948586 2137499 := bstep (se 1 (by rfl) ⟨1603124, by rfl⟩ : syracuseStep 2137499 = 3206249) B3206249
theorem B1285679 : Blo 948586 1285679 := bstep (se 1 (by rfl) ⟨964259, by rfl⟩ : syracuseStep 1285679 = 1928519) B1928519
theorem B3612559 : Blo 948586 3612559 := bstep (se 1 (by rfl) ⟨2709419, by rfl⟩ : syracuseStep 3612559 = 5418839) B5418839
theorem B17342363 : Blo 948586 17342363 := bstep (se 1 (by rfl) ⟨13006772, by rfl⟩ : syracuseStep 17342363 = 26013545) B26013545
theorem B3612833 : Blo 948586 3612833 := bstep (se 2 (by rfl) ⟨1354812, by rfl⟩ : syracuseStep 3612833 = 2709625) B2709625
theorem B1351999 : Blo 948586 1351999 := bstep (se 1 (by rfl) ⟨1013999, by rfl⟩ : syracuseStep 1351999 = 2027999) B2027999
theorem B1286911 : Blo 948586 1286911 := bstep (se 1 (by rfl) ⟨965183, by rfl⟩ : syracuseStep 1286911 = 1930367) B1930367
theorem B2139191 : Blo 948586 2139191 := bstep (se 1 (by rfl) ⟨1604393, by rfl⟩ : syracuseStep 2139191 = 3208787) B3208787
theorem B4564151 : Blo 948586 4564151 := bstep (se 1 (by rfl) ⟨3423113, by rfl⟩ : syracuseStep 4564151 = 6846227) B6846227
theorem B2140343 : Blo 948586 2140343 := bstep (se 1 (by rfl) ⟨1605257, by rfl⟩ : syracuseStep 2140343 = 3210515) B3210515
theorem B3615263 : Blo 948586 3615263 := bstep (se 1 (by rfl) ⟨2711447, by rfl⟩ : syracuseStep 3615263 = 5422895) B5422895
theorem B5417563 : Blo 948586 5417563 := bstep (se 1 (by rfl) ⟨4063172, by rfl⟩ : syracuseStep 5417563 = 8126345) B8126345
theorem B9120383 : Blo 948586 9120383 := bstep (se 1 (by rfl) ⟨6840287, by rfl⟩ : syracuseStep 9120383 = 13680575) B13680575
theorem B2141351 : Blo 948586 2141351 := bstep (se 1 (by rfl) ⟨1606013, by rfl⟩ : syracuseStep 2141351 = 3212027) B3212027
theorem B5778647 : Blo 948586 5778647 := bstep (se 1 (by rfl) ⟨4333985, by rfl⟩ : syracuseStep 5778647 = 8667971) B8667971
theorem B16231913 : Blo 948586 16231913 := bstep (se 2 (by rfl) ⟨6086967, by rfl⟩ : syracuseStep 16231913 = 12173935) B12173935
theorem B2141927 : Blo 948586 2141927 := bstep (se 1 (by rfl) ⟨1606445, by rfl⟩ : syracuseStep 2141927 = 3212891) B3212891
theorem B2567933 : Blo 948586 2567933 := bstep (se 3 (by rfl) ⟨481487, by rfl⟩ : syracuseStep 2567933 = 962975) B962975
theorem B3616751 : Blo 948586 3616751 := bstep (se 1 (by rfl) ⟨2712563, by rfl⟩ : syracuseStep 3616751 = 5425127) B5425127
theorem B2143007 : Blo 948586 2143007 := bstep (se 1 (by rfl) ⟨1607255, by rfl⟩ : syracuseStep 2143007 = 3214511) B3214511
theorem B2405335 : Blo 948586 2405335 := bstep (se 1 (by rfl) ⟨1804001, by rfl⟩ : syracuseStep 2405335 = 3608003) B3608003
theorem B39040001 : Blo 948586 39040001 := bstep (se 2 (by rfl) ⟨14640000, by rfl⟩ : syracuseStep 39040001 = 29280001) B29280001
theorem B26031269 : Blo 948586 26031269 := bstep (se 4 (by rfl) ⟨2440431, by rfl⟩ : syracuseStep 26031269 = 4880863) B4880863
theorem B2405639 : Blo 948586 2405639 := bstep (se 1 (by rfl) ⟨1804229, by rfl⟩ : syracuseStep 2405639 = 3608459) B3608459
theorem B702199637 : Blo 948586 702199637 := bstep (se 9 (by rfl) ⟨2057225, by rfl⟩ : syracuseStep 702199637 = 4114451) B4114451
theorem B1521499 : Blo 948586 1521499 := bstep (se 1 (by rfl) ⟨1141124, by rfl⟩ : syracuseStep 1521499 = 2282249) B2282249
theorem B1423583 : Blo 948586 1423583 := bstep (se 1 (by rfl) ⟨1067687, by rfl⟩ : syracuseStep 1423583 = 2135375) B2135375
theorem B46938773 : Blo 948586 46938773 := bstep (se 6 (by rfl) ⟨1100127, by rfl⟩ : syracuseStep 46938773 = 2200255) B2200255
theorem B1424063 : Blo 948586 1424063 := bstep (se 1 (by rfl) ⟨1068047, by rfl⟩ : syracuseStep 1424063 = 2136095) B2136095
theorem B1424111 : Blo 948586 1424111 := bstep (se 1 (by rfl) ⟨1068083, by rfl⟩ : syracuseStep 1424111 = 2136167) B2136167
theorem B965407 : Blo 948586 965407 := bstep (se 1 (by rfl) ⟨724055, by rfl⟩ : syracuseStep 965407 = 1448111) B1448111
theorem B1424231 : Blo 948586 1424231 := bstep (se 1 (by rfl) ⟨1068173, by rfl⟩ : syracuseStep 1424231 = 2136347) B2136347
theorem B158088131 : Blo 948586 158088131 := bstep (se 1 (by rfl) ⟨118566098, by rfl⟩ : syracuseStep 158088131 = 237132197) B237132197
theorem B2604139 : Blo 948586 2604139 := bstep (se 1 (by rfl) ⟨1953104, by rfl⟩ : syracuseStep 2604139 = 3906209) B3906209
theorem B1424951 : Blo 948586 1424951 := bstep (se 1 (by rfl) ⟨1068713, by rfl⟩ : syracuseStep 1424951 = 2137427) B2137427
theorem B1425503 : Blo 948586 1425503 := bstep (se 1 (by rfl) ⟨1069127, by rfl⟩ : syracuseStep 1425503 = 2138255) B2138255
theorem B1425785 : Blo 948586 1425785 := bstep (se 2 (by rfl) ⟨534669, by rfl⟩ : syracuseStep 1425785 = 1069339) B1069339
theorem B1425833 : Blo 948586 1425833 := bstep (se 2 (by rfl) ⟨534687, by rfl⟩ : syracuseStep 1425833 = 1069375) B1069375
theorem B1426247 : Blo 948586 1426247 := bstep (se 1 (by rfl) ⟨1069685, by rfl⟩ : syracuseStep 1426247 = 2139371) B2139371
theorem B1426415 : Blo 948586 1426415 := bstep (se 1 (by rfl) ⟨1069811, by rfl⟩ : syracuseStep 1426415 = 2139623) B2139623
theorem B1426799 : Blo 948586 1426799 := bstep (se 1 (by rfl) ⟨1070099, by rfl⟩ : syracuseStep 1426799 = 2140199) B2140199
theorem B1427081 : Blo 948586 1427081 := bstep (se 2 (by rfl) ⟨535155, by rfl⟩ : syracuseStep 1427081 = 1070311) B1070311
theorem B1427099 : Blo 948586 1427099 := bstep (se 1 (by rfl) ⟨1070324, by rfl⟩ : syracuseStep 1427099 = 2140649) B2140649
theorem B1787617 : Blo 948586 1787617 := bstep (se 2 (by rfl) ⟨670356, by rfl⟩ : syracuseStep 1787617 = 1340713) B1340713
theorem B7325423 : Blo 948586 7325423 := bstep (se 1 (by rfl) ⟨5494067, by rfl⟩ : syracuseStep 7325423 = 10988135) B10988135
theorem B1427675 : Blo 948586 1427675 := bstep (se 1 (by rfl) ⟨1070756, by rfl⟩ : syracuseStep 1427675 = 2141513) B2141513
theorem B1427687 : Blo 948586 1427687 := bstep (se 1 (by rfl) ⟨1070765, by rfl⟩ : syracuseStep 1427687 = 2141531) B2141531
theorem B2574623 : Blo 948586 2574623 := bstep (se 1 (by rfl) ⟨1930967, by rfl⟩ : syracuseStep 2574623 = 3861935) B3861935
theorem B1428023 : Blo 948586 1428023 := bstep (se 1 (by rfl) ⟨1071017, by rfl⟩ : syracuseStep 1428023 = 2142035) B2142035
theorem B2706367 : Blo 948586 2706367 := bstep (se 1 (by rfl) ⟨2029775, by rfl⟩ : syracuseStep 2706367 = 4059551) B4059551
theorem B1068799 : Blo 948586 1068799 := bstep (se 1 (by rfl) ⟨801599, by rfl⟩ : syracuseStep 1068799 = 1603199) B1603199
theorem B11718539 : Blo 948586 11718539 := bstep (se 1 (by rfl) ⟨8788904, by rfl⟩ : syracuseStep 11718539 = 17577809) B17577809
theorem B4804919 : Blo 948586 4804919 := bstep (se 1 (by rfl) ⟨3603689, by rfl⟩ : syracuseStep 4804919 = 7207379) B7207379
theorem B4117225 : Blo 948586 4117225 := bstep (se 2 (by rfl) ⟨1543959, by rfl⟩ : syracuseStep 4117225 = 3087919) B3087919
theorem B1069951 : Blo 948586 1069951 := bstep (se 1 (by rfl) ⟨802463, by rfl⟩ : syracuseStep 1069951 = 1604927) B1604927
theorem B6083869 : Blo 948586 6083869 := bstep (se 3 (by rfl) ⟨1140725, by rfl⟩ : syracuseStep 6083869 = 2281451) B2281451
theorem B5854531 : Blo 948586 5854531 := bstep (se 1 (by rfl) ⟨4390898, by rfl⟩ : syracuseStep 5854531 = 8781797) B8781797
theorem B3659261 : Blo 948586 3659261 := bstep (se 3 (by rfl) ⟨686111, by rfl⟩ : syracuseStep 3659261 = 1372223) B1372223
theorem B3955007 : Blo 948586 3955007 := bstep (se 1 (by rfl) ⟨2966255, by rfl⟩ : syracuseStep 3955007 = 5932511) B5932511
theorem B73980317 : Blo 948586 73980317 := bstep (se 3 (by rfl) ⟨13871309, by rfl⟩ : syracuseStep 73980317 = 27742619) B27742619
theorem B3201767 : Blo 948586 3201767 := bstep (se 1 (by rfl) ⟨2401325, by rfl⟩ : syracuseStep 3201767 = 4802651) B4802651
theorem B4807835 : Blo 948586 4807835 := bstep (se 1 (by rfl) ⟨3605876, by rfl⟩ : syracuseStep 4807835 = 7211753) B7211753
theorem B14638481 : Blo 948586 14638481 := bstep (se 2 (by rfl) ⟨5489430, by rfl⟩ : syracuseStep 14638481 = 10978861) B10978861
theorem B6839741 : Blo 948586 6839741 := bstep (se 3 (by rfl) ⟨1282451, by rfl⟩ : syracuseStep 6839741 = 2564903) B2564903
theorem B13688297 : Blo 948586 13688297 := bstep (se 2 (by rfl) ⟨5133111, by rfl⟩ : syracuseStep 13688297 = 10266223) B10266223
theorem B3202631 : Blo 948586 3202631 := bstep (se 1 (by rfl) ⟨2401973, by rfl⟩ : syracuseStep 3202631 = 4803947) B4803947
theorem B1466191 : Blo 948586 1466191 := bstep (se 1 (by rfl) ⟨1099643, by rfl⟩ : syracuseStep 1466191 = 2199287) B2199287
theorem B10805237 : Blo 948586 10805237 := bstep (se 5 (by rfl) ⟨506495, by rfl⟩ : syracuseStep 10805237 = 1012991) B1012991
theorem B187818263 : Blo 948586 187818263 := bstep (se 1 (by rfl) ⟨140863697, by rfl⟩ : syracuseStep 187818263 = 281727395) B281727395
theorem B1926281 : Blo 948586 1926281 := bstep (se 2 (by rfl) ⟨722355, by rfl⟩ : syracuseStep 1926281 = 1444711) B1444711
theorem B14640749 : Blo 948586 14640749 := bstep (se 3 (by rfl) ⟨2745140, by rfl⟩ : syracuseStep 14640749 = 5490281) B5490281
theorem B1763455 : Blo 948586 1763455 := bstep (se 1 (by rfl) ⟨1322591, by rfl⟩ : syracuseStep 1763455 = 2645183) B2645183
theorem B3205979 : Blo 948586 3205979 := bstep (se 1 (by rfl) ⟨2404484, by rfl⟩ : syracuseStep 3205979 = 4808969) B4808969
theorem B3206087 : Blo 948586 3206087 := bstep (se 1 (by rfl) ⟨2404565, by rfl⟩ : syracuseStep 3206087 = 4809131) B4809131
theorem B3337529 : Blo 948586 3337529 := bstep (se 2 (by rfl) ⟨1251573, by rfl⟩ : syracuseStep 3337529 = 2503147) B2503147
theorem B12512737 : Blo 948586 12512737 := bstep (se 2 (by rfl) ⟨4692276, by rfl⟩ : syracuseStep 12512737 = 9384553) B9384553
theorem B1601471 : Blo 948586 1601471 := bstep (se 1 (by rfl) ⟨1201103, by rfl⟩ : syracuseStep 1601471 = 2402207) B2402207
theorem B3207275 : Blo 948586 3207275 := bstep (se 1 (by rfl) ⟨2405456, by rfl⟩ : syracuseStep 3207275 = 4810913) B4810913
theorem B3207329 : Blo 948586 3207329 := bstep (se 2 (by rfl) ⟨1202748, by rfl⟩ : syracuseStep 3207329 = 2405497) B2405497
theorem B3174985 : Blo 948586 3174985 := bstep (se 2 (by rfl) ⟨1190619, by rfl⟩ : syracuseStep 3174985 = 2381239) B2381239
theorem B3208679 : Blo 948586 3208679 := bstep (se 1 (by rfl) ⟨2406509, by rfl⟩ : syracuseStep 3208679 = 4813019) B4813019
theorem B948719 : Blo 948586 948719 := bstep (se 1 (by rfl) ⟨711539, by rfl⟩ : syracuseStep 948719 = 1423079) B1423079
theorem B1604191 : Blo 948586 1604191 := bstep (se 1 (by rfl) ⟨1203143, by rfl⟩ : syracuseStep 1604191 = 2406287) B2406287
theorem B25983989 : Blo 948586 25983989 := bstep (se 5 (by rfl) ⟨1217999, by rfl⟩ : syracuseStep 25983989 = 2435999) B2435999
theorem B949567 : Blo 948586 949567 := bstep (se 1 (by rfl) ⟨712175, by rfl⟩ : syracuseStep 949567 = 1424351) B1424351
theorem B3210623 : Blo 948586 3210623 := bstep (se 1 (by rfl) ⟨2407967, by rfl⟩ : syracuseStep 3210623 = 4815935) B4815935
theorem B25984637 : Blo 948586 25984637 := bstep (se 3 (by rfl) ⟨4872119, by rfl⟩ : syracuseStep 25984637 = 9744239) B9744239
theorem B950335 : Blo 948586 950335 := bstep (se 1 (by rfl) ⟨712751, by rfl⟩ : syracuseStep 950335 = 1425503) B1425503
theorem B950523 : Blo 948586 950523 := bstep (se 1 (by rfl) ⟨712892, by rfl⟩ : syracuseStep 950523 = 1425785) B1425785
theorem B950555 : Blo 948586 950555 := bstep (se 1 (by rfl) ⟨712916, by rfl⟩ : syracuseStep 950555 = 1425833) B1425833
theorem B4063583 : Blo 948586 4063583 := bstep (se 1 (by rfl) ⟨3047687, by rfl⟩ : syracuseStep 4063583 = 6095375) B6095375
theorem B1802665 : Blo 948586 1802665 := bstep (se 2 (by rfl) ⟨675999, by rfl⟩ : syracuseStep 1802665 = 1351999) B1351999
theorem B950831 : Blo 948586 950831 := bstep (se 1 (by rfl) ⟨713123, by rfl⟩ : syracuseStep 950831 = 1426247) B1426247
theorem B950943 : Blo 948586 950943 := bstep (se 1 (by rfl) ⟨713207, by rfl⟩ : syracuseStep 950943 = 1426415) B1426415
theorem B951199 : Blo 948586 951199 := bstep (se 1 (by rfl) ⟨713399, by rfl⟩ : syracuseStep 951199 = 1426799) B1426799
theorem B951387 : Blo 948586 951387 := bstep (se 1 (by rfl) ⟨713540, by rfl⟩ : syracuseStep 951387 = 1427081) B1427081
theorem B951399 : Blo 948586 951399 := bstep (se 1 (by rfl) ⟨713549, by rfl⟩ : syracuseStep 951399 = 1427099) B1427099
theorem B4883615 : Blo 948586 4883615 := bstep (se 1 (by rfl) ⟨3662711, by rfl⟩ : syracuseStep 4883615 = 7325423) B7325423
theorem B951783 : Blo 948586 951783 := bstep (se 1 (by rfl) ⟨713837, by rfl⟩ : syracuseStep 951783 = 1427675) B1427675
theorem B951791 : Blo 948586 951791 := bstep (se 1 (by rfl) ⟨713843, by rfl⟩ : syracuseStep 951791 = 1427687) B1427687
theorem B3212783 : Blo 948586 3212783 := bstep (se 1 (by rfl) ⟨2409587, by rfl⟩ : syracuseStep 3212783 = 4819175) B4819175
theorem B952015 : Blo 948586 952015 := bstep (se 1 (by rfl) ⟨714011, by rfl⟩ : syracuseStep 952015 = 1428023) B1428023
theorem B2164603 : Blo 948586 2164603 := bstep (se 1 (by rfl) ⟨1623452, by rfl⟩ : syracuseStep 2164603 = 3246905) B3246905
theorem B2033903 : Blo 948586 2033903 := bstep (se 1 (by rfl) ⟨1525427, by rfl⟩ : syracuseStep 2033903 = 3050855) B3050855
theorem B3213755 : Blo 948586 3213755 := bstep (se 1 (by rfl) ⟨2410316, by rfl⟩ : syracuseStep 3213755 = 4820633) B4820633
theorem B3476191 : Blo 948586 3476191 := bstep (se 1 (by rfl) ⟨2607143, by rfl⟩ : syracuseStep 3476191 = 5214287) B5214287
theorem B6098759 : Blo 948586 6098759 := bstep (se 1 (by rfl) ⟨4574069, by rfl⟩ : syracuseStep 6098759 = 9148139) B9148139
theorem B3608489 : Blo 948586 3608489 := bstep (se 2 (by rfl) ⟨1353183, by rfl⟩ : syracuseStep 3608489 = 2706367) B2706367
theorem B7213211 : Blo 948586 7213211 := bstep (se 1 (by rfl) ⟨5409908, by rfl⟩ : syracuseStep 7213211 = 10819817) B10819817
theorem B3477755 : Blo 948586 3477755 := bstep (se 1 (by rfl) ⟨2608316, by rfl⟩ : syracuseStep 3477755 = 5216633) B5216633
theorem B49320211 : Blo 948586 49320211 := bstep (se 1 (by rfl) ⟨36990158, by rfl⟩ : syracuseStep 49320211 = 73980317) B73980317
theorem B2134511 : Blo 948586 2134511 := bstep (se 1 (by rfl) ⟨1600883, by rfl⟩ : syracuseStep 2134511 = 3201767) B3201767
theorem B4559827 : Blo 948586 4559827 := bstep (se 1 (by rfl) ⟨3419870, by rfl⟩ : syracuseStep 4559827 = 6839741) B6839741
theorem B2135087 : Blo 948586 2135087 := bstep (se 1 (by rfl) ⟨1601315, by rfl⟩ : syracuseStep 2135087 = 3202631) B3202631
theorem B39032117 : Blo 948586 39032117 := bstep (se 5 (by rfl) ⟨1829630, by rfl⟩ : syracuseStep 39032117 = 3659261) B3659261
theorem B125212175 : Blo 948586 125212175 := bstep (se 1 (by rfl) ⟨93909131, by rfl⟩ : syracuseStep 125212175 = 187818263) B187818263
theorem B1284187 : Blo 948586 1284187 := bstep (se 1 (by rfl) ⟨963140, by rfl⟩ : syracuseStep 1284187 = 1926281) B1926281
theorem B4233313 : Blo 948586 4233313 := bstep (se 2 (by rfl) ⟨1587492, by rfl⟩ : syracuseStep 4233313 = 3174985) B3174985
theorem B7806041 : Blo 948586 7806041 := bstep (se 2 (by rfl) ⟨2927265, by rfl⟩ : syracuseStep 7806041 = 5854531) B5854531
theorem B2137319 : Blo 948586 2137319 := bstep (se 1 (by rfl) ⟨1602989, by rfl⟩ : syracuseStep 2137319 = 3205979) B3205979
theorem B2137391 : Blo 948586 2137391 := bstep (se 1 (by rfl) ⟨1603043, by rfl⟩ : syracuseStep 2137391 = 3206087) B3206087
theorem B10821275 : Blo 948586 10821275 := bstep (se 1 (by rfl) ⟨8115956, by rfl⟩ : syracuseStep 10821275 = 16231913) B16231913
theorem B1711955 : Blo 948586 1711955 := bstep (se 1 (by rfl) ⟨1283966, by rfl⟩ : syracuseStep 1711955 = 2567933) B2567933
theorem B2138183 : Blo 948586 2138183 := bstep (se 1 (by rfl) ⟨1603637, by rfl⟩ : syracuseStep 2138183 = 3207275) B3207275
theorem B2138219 : Blo 948586 2138219 := bstep (se 1 (by rfl) ⟨1603664, by rfl⟩ : syracuseStep 2138219 = 3207329) B3207329
theorem B26026667 : Blo 948586 26026667 := bstep (se 1 (by rfl) ⟨19520000, by rfl⟩ : syracuseStep 26026667 = 39040001) B39040001
theorem B2138921 : Blo 948586 2138921 := bstep (se 2 (by rfl) ⟨802095, by rfl⟩ : syracuseStep 2138921 = 1604191) B1604191
theorem B2139119 : Blo 948586 2139119 := bstep (se 1 (by rfl) ⟨1604339, by rfl⟩ : syracuseStep 2139119 = 3208679) B3208679
theorem B1287209 : Blo 948586 1287209 := bstep (se 2 (by rfl) ⟨482703, by rfl⟩ : syracuseStep 1287209 = 965407) B965407
theorem B468133091 : Blo 948586 468133091 := bstep (se 1 (by rfl) ⟨351099818, by rfl⟩ : syracuseStep 468133091 = 702199637) B702199637
theorem B105392087 : Blo 948586 105392087 := bstep (se 1 (by rfl) ⟨79044065, by rfl⟩ : syracuseStep 105392087 = 158088131) B158088131
theorem B2140415 : Blo 948586 2140415 := bstep (se 1 (by rfl) ⟨1605311, by rfl⟩ : syracuseStep 2140415 = 3210623) B3210623
theorem B2403047 : Blo 948586 2403047 := bstep (se 1 (by rfl) ⟨1802285, by rfl⟩ : syracuseStep 2403047 = 3604571) B3604571
theorem B18262907 : Blo 948586 18262907 := bstep (se 1 (by rfl) ⟨13697180, by rfl⟩ : syracuseStep 18262907 = 27394361) B27394361
theorem B2141153 : Blo 948586 2141153 := bstep (se 2 (by rfl) ⟨802932, by rfl⟩ : syracuseStep 2141153 = 1605865) B1605865
theorem B2403695 : Blo 948586 2403695 := bstep (se 1 (by rfl) ⟨1802771, by rfl⟩ : syracuseStep 2403695 = 3605543) B3605543
theorem B15643103 : Blo 948586 15643103 := bstep (se 1 (by rfl) ⟨11732327, by rfl⟩ : syracuseStep 15643103 = 23464655) B23464655
theorem B2142719 : Blo 948586 2142719 := bstep (se 1 (by rfl) ⟨1607039, by rfl⟩ : syracuseStep 2142719 = 3214079) B3214079
theorem B2142863 : Blo 948586 2142863 := bstep (se 1 (by rfl) ⟨1607147, by rfl⟩ : syracuseStep 2142863 = 3214295) B3214295
theorem B7812359 : Blo 948586 7812359 := bstep (se 1 (by rfl) ⟨5859269, by rfl⟩ : syracuseStep 7812359 = 11718539) B11718539
theorem B7223417 : Blo 948586 7223417 := bstep (se 2 (by rfl) ⟨2708781, by rfl⟩ : syracuseStep 7223417 = 5417563) B5417563
theorem B1423967 : Blo 948586 1423967 := bstep (se 1 (by rfl) ⟨1067975, by rfl⟩ : syracuseStep 1423967 = 2135951) B2135951
theorem B6863525 : Blo 948586 6863525 := bstep (se 4 (by rfl) ⟨643455, by rfl⟩ : syracuseStep 6863525 = 1286911) B1286911
theorem B2636671 : Blo 948586 2636671 := bstep (se 1 (by rfl) ⟨1977503, by rfl⟩ : syracuseStep 2636671 = 3955007) B3955007
theorem B77905313 : Blo 948586 77905313 := bstep (se 2 (by rfl) ⟨29214492, by rfl⟩ : syracuseStep 77905313 = 58428985) B58428985
theorem B1424999 : Blo 948586 1424999 := bstep (se 1 (by rfl) ⟨1068749, by rfl⟩ : syracuseStep 1424999 = 2137499) B2137499
theorem B9125531 : Blo 948586 9125531 := bstep (se 1 (by rfl) ⟨6844148, by rfl⟩ : syracuseStep 9125531 = 13688297) B13688297
theorem B1425065 : Blo 948586 1425065 := bstep (se 2 (by rfl) ⟨534399, by rfl⟩ : syracuseStep 1425065 = 1068799) B1068799
theorem B2408555 : Blo 948586 2408555 := bstep (se 1 (by rfl) ⟨1806416, by rfl⟩ : syracuseStep 2408555 = 3612833) B3612833
theorem B1426127 : Blo 948586 1426127 := bstep (se 1 (by rfl) ⟨1069595, by rfl⟩ : syracuseStep 1426127 = 2139191) B2139191
theorem B6865661 : Blo 948586 6865661 := bstep (se 3 (by rfl) ⟨1287311, by rfl⟩ : syracuseStep 6865661 = 2574623) B2574623
theorem B5489633 : Blo 948586 5489633 := bstep (se 2 (by rfl) ⟨2058612, by rfl⟩ : syracuseStep 5489633 = 4117225) B4117225
theorem B1426601 : Blo 948586 1426601 := bstep (se 2 (by rfl) ⟨534975, by rfl⟩ : syracuseStep 1426601 = 1069951) B1069951
theorem B1426895 : Blo 948586 1426895 := bstep (se 1 (by rfl) ⟨1070171, by rfl⟩ : syracuseStep 1426895 = 2140343) B2140343
theorem B2410175 : Blo 948586 2410175 := bstep (se 1 (by rfl) ⟨1807631, by rfl⟩ : syracuseStep 2410175 = 3615263) B3615263
theorem B8111825 : Blo 948586 8111825 := bstep (se 2 (by rfl) ⟨3041934, by rfl⟩ : syracuseStep 8111825 = 6083869) B6083869
theorem B6080255 : Blo 948586 6080255 := bstep (se 1 (by rfl) ⟨4560191, by rfl⟩ : syracuseStep 6080255 = 9120383) B9120383
theorem B1427567 : Blo 948586 1427567 := bstep (se 1 (by rfl) ⟨1070675, by rfl⟩ : syracuseStep 1427567 = 2141351) B2141351
theorem B3852431 : Blo 948586 3852431 := bstep (se 1 (by rfl) ⟨2889323, by rfl⟩ : syracuseStep 3852431 = 5778647) B5778647
theorem B1427951 : Blo 948586 1427951 := bstep (se 1 (by rfl) ⟨1070963, by rfl⟩ : syracuseStep 1427951 = 2141927) B2141927
theorem B66734597 : Blo 948586 66734597 := bstep (se 4 (by rfl) ⟨6256368, by rfl⟩ : syracuseStep 66734597 = 12512737) B12512737
theorem B1067647 : Blo 948586 1067647 := bstep (se 1 (by rfl) ⟨800735, by rfl⟩ : syracuseStep 1067647 = 1601471) B1601471
theorem B2411167 : Blo 948586 2411167 := bstep (se 1 (by rfl) ⟨1808375, by rfl⟩ : syracuseStep 2411167 = 3616751) B3616751
theorem B1428671 : Blo 948586 1428671 := bstep (se 1 (by rfl) ⟨1071503, by rfl⟩ : syracuseStep 1428671 = 2143007) B2143007
theorem B13028609 : Blo 948586 13028609 := bstep (se 2 (by rfl) ⟨4885728, by rfl⟩ : syracuseStep 13028609 = 9771457) B9771457
theorem B17354179 : Blo 948586 17354179 := bstep (se 1 (by rfl) ⟨13015634, by rfl⟩ : syracuseStep 17354179 = 26031269) B26031269
theorem B8900077 : Blo 948586 8900077 := bstep (se 3 (by rfl) ⟨1668764, by rfl⟩ : syracuseStep 8900077 = 3337529) B3337529
theorem B3428477 : Blo 948586 3428477 := bstep (se 3 (by rfl) ⟨642839, by rfl⟩ : syracuseStep 3428477 = 1285679) B1285679
theorem B7819685 : Blo 948586 7819685 := bstep (se 4 (by rfl) ⟨733095, by rfl⟩ : syracuseStep 7819685 = 1466191) B1466191
theorem B17322659 : Blo 948586 17322659 := bstep (se 1 (by rfl) ⟨12991994, by rfl⟩ : syracuseStep 17322659 = 25983989) B25983989
theorem B17323091 : Blo 948586 17323091 := bstep (se 1 (by rfl) ⟨12992318, by rfl⟩ : syracuseStep 17323091 = 25984637) B25984637
theorem B4807511 : Blo 948586 4807511 := bstep (se 1 (by rfl) ⟨3605633, by rfl⟩ : syracuseStep 4807511 = 7211267) B7211267
theorem B1924393 : Blo 948586 1924393 := bstep (se 2 (by rfl) ⟨721647, by rfl⟩ : syracuseStep 1924393 = 1443295) B1443295
theorem B2383489 : Blo 948586 2383489 := bstep (se 2 (by rfl) ⟨893808, by rfl⟩ : syracuseStep 2383489 = 1787617) B1787617
theorem B2351273 : Blo 948586 2351273 := bstep (se 2 (by rfl) ⟨881727, by rfl⟩ : syracuseStep 2351273 = 1763455) B1763455
theorem B3203279 : Blo 948586 3203279 := bstep (se 1 (by rfl) ⟨2402459, by rfl⟩ : syracuseStep 3203279 = 4804919) B4804919
theorem B21128471 : Blo 948586 21128471 := bstep (se 1 (by rfl) ⟨15846353, by rfl⟩ : syracuseStep 21128471 = 31692707) B31692707
theorem B27354449 : Blo 948586 27354449 := bstep (se 2 (by rfl) ⟨10257918, by rfl⟩ : syracuseStep 27354449 = 20515837) B20515837
theorem B3205223 : Blo 948586 3205223 := bstep (se 1 (by rfl) ⟨2403917, by rfl⟩ : syracuseStep 3205223 = 4807835) B4807835
theorem B9758987 : Blo 948586 9758987 := bstep (se 1 (by rfl) ⟨7319240, by rfl⟩ : syracuseStep 9758987 = 14638481) B14638481
theorem B11561575 : Blo 948586 11561575 := bstep (se 1 (by rfl) ⟨8671181, by rfl⟩ : syracuseStep 11561575 = 17342363) B17342363
theorem B7203491 : Blo 948586 7203491 := bstep (se 1 (by rfl) ⟨5402618, by rfl⟩ : syracuseStep 7203491 = 10805237) B10805237
theorem B13888741 : Blo 948586 13888741 := bstep (se 4 (by rfl) ⟨1302069, by rfl⟩ : syracuseStep 13888741 = 2604139) B2604139
theorem B3042767 : Blo 948586 3042767 := bstep (se 1 (by rfl) ⟨2282075, by rfl⟩ : syracuseStep 3042767 = 4564151) B4564151
theorem B9760499 : Blo 948586 9760499 := bstep (se 1 (by rfl) ⟨7320374, by rfl⟩ : syracuseStep 9760499 = 14640749) B14640749
theorem B3207113 : Blo 948586 3207113 := bstep (se 2 (by rfl) ⟨1202667, by rfl⟩ : syracuseStep 3207113 = 2405335) B2405335
theorem B2028665 : Blo 948586 2028665 := bstep (se 2 (by rfl) ⟨760749, by rfl⟩ : syracuseStep 2028665 = 1521499) B1521499
theorem B1603759 : Blo 948586 1603759 := bstep (se 1 (by rfl) ⟨1202819, by rfl⟩ : syracuseStep 1603759 = 2405639) B2405639
theorem B949055 : Blo 948586 949055 := bstep (se 1 (by rfl) ⟨711791, by rfl⟩ : syracuseStep 949055 = 1423583) B1423583
theorem B31292515 : Blo 948586 31292515 := bstep (se 1 (by rfl) ⟨23469386, by rfl⟩ : syracuseStep 31292515 = 46938773) B46938773
theorem B949375 : Blo 948586 949375 := bstep (se 1 (by rfl) ⟨712031, by rfl⟩ : syracuseStep 949375 = 1424063) B1424063
theorem B949407 : Blo 948586 949407 := bstep (se 1 (by rfl) ⟨712055, by rfl⟩ : syracuseStep 949407 = 1424111) B1424111
theorem B949487 : Blo 948586 949487 := bstep (se 1 (by rfl) ⟨712115, by rfl⟩ : syracuseStep 949487 = 1424231) B1424231
theorem B949967 : Blo 948586 949967 := bstep (se 1 (by rfl) ⟨712475, by rfl⟩ : syracuseStep 949967 = 1424951) B1424951
theorem B4816745 : Blo 948586 4816745 := bstep (se 2 (by rfl) ⟨1806279, by rfl⟩ : syracuseStep 4816745 = 3612559) B3612559
theorem B1605703 : Blo 948586 1605703 := bstep (se 1 (by rfl) ⟨1204277, by rfl⟩ : syracuseStep 1605703 = 2408555) B2408555
theorem B950751 : Blo 948586 950751 := bstep (se 1 (by rfl) ⟨713063, by rfl⟩ : syracuseStep 950751 = 1426127) B1426127
theorem B9274013 : Blo 948586 9274013 := bstep (se 3 (by rfl) ⟨1738877, by rfl⟩ : syracuseStep 9274013 = 3477755) B3477755
theorem B951067 : Blo 948586 951067 := bstep (se 1 (by rfl) ⟨713300, by rfl⟩ : syracuseStep 951067 = 1426601) B1426601
theorem B951263 : Blo 948586 951263 := bstep (se 1 (by rfl) ⟨713447, by rfl⟩ : syracuseStep 951263 = 1426895) B1426895
theorem B1606783 : Blo 948586 1606783 := bstep (se 1 (by rfl) ⟨1205087, by rfl⟩ : syracuseStep 1606783 = 2410175) B2410175
theorem B5407883 : Blo 948586 5407883 := bstep (se 1 (by rfl) ⟨4055912, by rfl⟩ : syracuseStep 5407883 = 8111825) B8111825
theorem B41714941 : Blo 948586 41714941 := bstep (se 3 (by rfl) ⟨7821551, by rfl⟩ : syracuseStep 41714941 = 15643103) B15643103
theorem B951711 : Blo 948586 951711 := bstep (se 1 (by rfl) ⟨713783, by rfl⟩ : syracuseStep 951711 = 1427567) B1427567
theorem B951967 : Blo 948586 951967 := bstep (se 1 (by rfl) ⟨713975, by rfl⟩ : syracuseStep 951967 = 1427951) B1427951
theorem B952447 : Blo 948586 952447 := bstep (se 1 (by rfl) ⟨714335, by rfl⟩ : syracuseStep 952447 = 1428671) B1428671
theorem B8685739 : Blo 948586 8685739 := bstep (se 1 (by rfl) ⟨6514304, by rfl⟩ : syracuseStep 8685739 = 13028609) B13028609
theorem B2886137 : Blo 948586 2886137 := bstep (se 2 (by rfl) ⟨1082301, by rfl⟩ : syracuseStep 2886137 = 2164603) B2164603
theorem B4065839 : Blo 948586 4065839 := bstep (se 1 (by rfl) ⟨3049379, by rfl⟩ : syracuseStep 4065839 = 6098759) B6098759
theorem B5213123 : Blo 948586 5213123 := bstep (se 1 (by rfl) ⟨3909842, by rfl⟩ : syracuseStep 5213123 = 7819685) B7819685
theorem B5409773 : Blo 948586 5409773 := bstep (se 3 (by rfl) ⟨1014332, by rfl⟩ : syracuseStep 5409773 = 2028665) B2028665
theorem B26021411 : Blo 948586 26021411 := bstep (se 1 (by rfl) ⟨19516058, by rfl⟩ : syracuseStep 26021411 = 39032117) B39032117
theorem B3214889 : Blo 948586 3214889 := bstep (se 2 (by rfl) ⟨1205583, by rfl⟩ : syracuseStep 3214889 = 2411167) B2411167
theorem B18518321 : Blo 948586 18518321 := bstep (se 2 (by rfl) ⟨6944370, by rfl⟩ : syracuseStep 18518321 = 13888741) B13888741
theorem B23138905 : Blo 948586 23138905 := bstep (se 2 (by rfl) ⟨8677089, by rfl⟩ : syracuseStep 23138905 = 17354179) B17354179
theorem B11866769 : Blo 948586 11866769 := bstep (se 2 (by rfl) ⟨4450038, by rfl⟩ : syracuseStep 11866769 = 8900077) B8900077
theorem B7214183 : Blo 948586 7214183 := bstep (se 1 (by rfl) ⟨5410637, by rfl⟩ : syracuseStep 7214183 = 10821275) B10821275
theorem B2135519 : Blo 948586 2135519 := bstep (se 1 (by rfl) ⟨1601639, by rfl⟩ : syracuseStep 2135519 = 3203279) B3203279
theorem B312088727 : Blo 948586 312088727 := bstep (se 1 (by rfl) ⟨234066545, by rfl⟩ : syracuseStep 312088727 = 468133091) B468133091
theorem B70261391 : Blo 948586 70261391 := bstep (se 1 (by rfl) ⟨52696043, by rfl⟩ : syracuseStep 70261391 = 105392087) B105392087
theorem B2136815 : Blo 948586 2136815 := bstep (se 1 (by rfl) ⟨1602611, by rfl⟩ : syracuseStep 2136815 = 3205223) B3205223
theorem B2138075 : Blo 948586 2138075 := bstep (se 1 (by rfl) ⟨1603556, by rfl⟩ : syracuseStep 2138075 = 3207113) B3207113
theorem B1712249 : Blo 948586 1712249 := bstep (se 2 (by rfl) ⟨642093, by rfl⟩ : syracuseStep 1712249 = 1284187) B1284187
theorem B5644417 : Blo 948586 5644417 := bstep (se 2 (by rfl) ⟨2116656, by rfl⟩ : syracuseStep 5644417 = 4233313) B4233313
theorem B2138345 : Blo 948586 2138345 := bstep (se 2 (by rfl) ⟨801879, by rfl⟩ : syracuseStep 2138345 = 1603759) B1603759
theorem B3515561 : Blo 948586 3515561 := bstep (se 2 (by rfl) ⟨1318335, by rfl⟩ : syracuseStep 3515561 = 2636671) B2636671
theorem B41723353 : Blo 948586 41723353 := bstep (se 2 (by rfl) ⟨15646257, by rfl⟩ : syracuseStep 41723353 = 31292515) B31292515
theorem B2565857 : Blo 948586 2565857 := bstep (se 2 (by rfl) ⟨962196, by rfl⟩ : syracuseStep 2565857 = 1924393) B1924393
theorem B6270061 : Blo 948586 6270061 := bstep (se 3 (by rfl) ⟨1175636, by rfl⟩ : syracuseStep 6270061 = 2351273) B2351273
theorem B2403553 : Blo 948586 2403553 := bstep (se 2 (by rfl) ⟨901332, by rfl⟩ : syracuseStep 2403553 = 1802665) B1802665
theorem B3255743 : Blo 948586 3255743 := bstep (se 1 (by rfl) ⟨2441807, by rfl⟩ : syracuseStep 3255743 = 4883615) B4883615
theorem B2141855 : Blo 948586 2141855 := bstep (se 1 (by rfl) ⟨1606391, by rfl⟩ : syracuseStep 2141855 = 3212783) B3212783
theorem B2568287 : Blo 948586 2568287 := bstep (se 1 (by rfl) ⟨1926215, by rfl⟩ : syracuseStep 2568287 = 3852431) B3852431
theorem B1355935 : Blo 948586 1355935 := bstep (se 1 (by rfl) ⟨1016951, by rfl⟩ : syracuseStep 1355935 = 2033903) B2033903
theorem B2142503 : Blo 948586 2142503 := bstep (se 1 (by rfl) ⟨1606877, by rfl⟩ : syracuseStep 2142503 = 3213755) B3213755
theorem B2405659 : Blo 948586 2405659 := bstep (se 1 (by rfl) ⟨1804244, by rfl⟩ : syracuseStep 2405659 = 3608489) B3608489
theorem B1423007 : Blo 948586 1423007 := bstep (se 1 (by rfl) ⟨1067255, by rfl⟩ : syracuseStep 1423007 = 2134511) B2134511
theorem B11548439 : Blo 948586 11548439 := bstep (se 1 (by rfl) ⟨8661329, by rfl⟩ : syracuseStep 11548439 = 17322659) B17322659
theorem B1423391 : Blo 948586 1423391 := bstep (se 1 (by rfl) ⟨1067543, by rfl⟩ : syracuseStep 1423391 = 2135087) B2135087
theorem B11548727 : Blo 948586 11548727 := bstep (se 1 (by rfl) ⟨8661545, by rfl⟩ : syracuseStep 11548727 = 17323091) B17323091
theorem B15415433 : Blo 948586 15415433 := bstep (se 2 (by rfl) ⟨5780787, by rfl⟩ : syracuseStep 15415433 = 11561575) B11561575
theorem B1423529 : Blo 948586 1423529 := bstep (se 2 (by rfl) ⟨533823, by rfl⟩ : syracuseStep 1423529 = 1067647) B1067647
theorem B4634921 : Blo 948586 4634921 := bstep (se 2 (by rfl) ⟨1738095, by rfl⟩ : syracuseStep 4634921 = 3476191) B3476191
theorem B83474783 : Blo 948586 83474783 := bstep (se 1 (by rfl) ⟨62606087, by rfl⟩ : syracuseStep 83474783 = 125212175) B125212175
theorem B1424879 : Blo 948586 1424879 := bstep (se 1 (by rfl) ⟨1068659, by rfl⟩ : syracuseStep 1424879 = 2137319) B2137319
theorem B1424927 : Blo 948586 1424927 := bstep (se 1 (by rfl) ⟨1068695, by rfl⟩ : syracuseStep 1424927 = 2137391) B2137391
theorem B1425455 : Blo 948586 1425455 := bstep (se 1 (by rfl) ⟨1069091, by rfl⟩ : syracuseStep 1425455 = 2138183) B2138183
theorem B1425479 : Blo 948586 1425479 := bstep (se 1 (by rfl) ⟨1069109, by rfl⟩ : syracuseStep 1425479 = 2138219) B2138219
theorem B17351111 : Blo 948586 17351111 := bstep (se 1 (by rfl) ⟨13013333, by rfl⟩ : syracuseStep 17351111 = 26026667) B26026667
theorem B1425947 : Blo 948586 1425947 := bstep (se 1 (by rfl) ⟨1069460, by rfl⟩ : syracuseStep 1425947 = 2138921) B2138921
theorem B1426079 : Blo 948586 1426079 := bstep (se 1 (by rfl) ⟨1069559, by rfl⟩ : syracuseStep 1426079 = 2139119) B2139119
theorem B18236299 : Blo 948586 18236299 := bstep (se 1 (by rfl) ⟨13677224, by rfl⟩ : syracuseStep 18236299 = 27354449) B27354449
theorem B6079769 : Blo 948586 6079769 := bstep (se 2 (by rfl) ⟨2279913, by rfl⟩ : syracuseStep 6079769 = 4559827) B4559827
theorem B1426943 : Blo 948586 1426943 := bstep (se 1 (by rfl) ⟨1070207, by rfl⟩ : syracuseStep 1426943 = 2140415) B2140415
theorem B6505991 : Blo 948586 6505991 := bstep (se 1 (by rfl) ⟨4879493, by rfl⟩ : syracuseStep 6505991 = 9758987) B9758987
theorem B4802327 : Blo 948586 4802327 := bstep (se 1 (by rfl) ⟨3601745, by rfl⟩ : syracuseStep 4802327 = 7203491) B7203491
theorem B12175271 : Blo 948586 12175271 := bstep (se 1 (by rfl) ⟨9131453, by rfl⟩ : syracuseStep 12175271 = 18262907) B18262907
theorem B1427435 : Blo 948586 1427435 := bstep (se 1 (by rfl) ⟨1070576, by rfl⟩ : syracuseStep 1427435 = 2141153) B2141153
theorem B6506999 : Blo 948586 6506999 := bstep (se 1 (by rfl) ⟨4880249, by rfl⟩ : syracuseStep 6506999 = 9760499) B9760499
theorem B1428479 : Blo 948586 1428479 := bstep (se 1 (by rfl) ⟨1071359, by rfl⟩ : syracuseStep 1428479 = 2142719) B2142719
theorem B1428575 : Blo 948586 1428575 := bstep (se 1 (by rfl) ⟨1071431, by rfl⟩ : syracuseStep 1428575 = 2142863) B2142863
theorem B4575683 : Blo 948586 4575683 := bstep (se 1 (by rfl) ⟨3431762, by rfl⟩ : syracuseStep 4575683 = 6863525) B6863525
theorem B6083687 : Blo 948586 6083687 := bstep (se 1 (by rfl) ⟨4562765, by rfl⟩ : syracuseStep 6083687 = 9125531) B9125531
theorem B2709055 : Blo 948586 2709055 := bstep (se 1 (by rfl) ⟨2031791, by rfl⟩ : syracuseStep 2709055 = 4063583) B4063583
theorem B4577107 : Blo 948586 4577107 := bstep (se 1 (by rfl) ⟨3432830, by rfl⟩ : syracuseStep 4577107 = 6865661) B6865661
theorem B3659755 : Blo 948586 3659755 := bstep (se 1 (by rfl) ⟨2744816, by rfl⟩ : syracuseStep 3659755 = 5489633) B5489633
theorem B4053503 : Blo 948586 4053503 := bstep (se 1 (by rfl) ⟨3040127, by rfl⟩ : syracuseStep 4053503 = 6080255) B6080255
theorem B44489731 : Blo 948586 44489731 := bstep (se 1 (by rfl) ⟨33367298, by rfl⟩ : syracuseStep 44489731 = 66734597) B66734597
theorem B2285651 : Blo 948586 2285651 := bstep (se 1 (by rfl) ⟨1714238, by rfl⟩ : syracuseStep 2285651 = 3428477) B3428477
theorem B4808807 : Blo 948586 4808807 := bstep (se 1 (by rfl) ⟨3606605, by rfl⟩ : syracuseStep 4808807 = 7213211) B7213211
theorem B3432557 : Blo 948586 3432557 := bstep (se 3 (by rfl) ⟨643604, by rfl⟩ : syracuseStep 3432557 = 1287209) B1287209
theorem B3205007 : Blo 948586 3205007 := bstep (se 1 (by rfl) ⟨2403755, by rfl⟩ : syracuseStep 3205007 = 4807511) B4807511
theorem B5204027 : Blo 948586 5204027 := bstep (se 1 (by rfl) ⟨3903020, by rfl⟩ : syracuseStep 5204027 = 7806041) B7806041
theorem B1141303 : Blo 948586 1141303 := bstep (se 1 (by rfl) ⟨855977, by rfl⟩ : syracuseStep 1141303 = 1711955) B1711955
theorem B65760281 : Blo 948586 65760281 := bstep (se 2 (by rfl) ⟨24660105, by rfl⟩ : syracuseStep 65760281 = 49320211) B49320211
theorem B14085647 : Blo 948586 14085647 := bstep (se 1 (by rfl) ⟨10564235, by rfl⟩ : syracuseStep 14085647 = 21128471) B21128471
theorem B1602031 : Blo 948586 1602031 := bstep (se 1 (by rfl) ⟨1201523, by rfl⟩ : syracuseStep 1602031 = 2403047) B2403047
theorem B1602463 : Blo 948586 1602463 := bstep (se 1 (by rfl) ⟨1201847, by rfl⟩ : syracuseStep 1602463 = 2403695) B2403695
theorem B2028511 : Blo 948586 2028511 := bstep (se 1 (by rfl) ⟨1521383, by rfl⟩ : syracuseStep 2028511 = 3042767) B3042767
theorem B12711941 : Blo 948586 12711941 := bstep (se 4 (by rfl) ⟨1191744, by rfl⟩ : syracuseStep 12711941 = 2383489) B2383489
theorem B5208239 : Blo 948586 5208239 := bstep (se 1 (by rfl) ⟨3906179, by rfl⟩ : syracuseStep 5208239 = 7812359) B7812359
theorem B4815611 : Blo 948586 4815611 := bstep (se 1 (by rfl) ⟨3611708, by rfl⟩ : syracuseStep 4815611 = 7223417) B7223417
theorem B949311 : Blo 948586 949311 := bstep (se 1 (by rfl) ⟨711983, by rfl⟩ : syracuseStep 949311 = 1423967) B1423967
theorem B51936875 : Blo 948586 51936875 := bstep (se 1 (by rfl) ⟨38952656, by rfl⟩ : syracuseStep 51936875 = 77905313) B77905313
theorem B949999 : Blo 948586 949999 := bstep (se 1 (by rfl) ⟨712499, by rfl⟩ : syracuseStep 949999 = 1424999) B1424999
theorem B950043 : Blo 948586 950043 := bstep (se 1 (by rfl) ⟨712532, by rfl⟩ : syracuseStep 950043 = 1425065) B1425065
theorem B3211163 : Blo 948586 3211163 := bstep (se 1 (by rfl) ⟨2408372, by rfl⟩ : syracuseStep 3211163 = 4816745) B4816745
theorem B950303 : Blo 948586 950303 := bstep (se 1 (by rfl) ⟨712727, by rfl⟩ : syracuseStep 950303 = 1425455) B1425455
theorem B950319 : Blo 948586 950319 := bstep (se 1 (by rfl) ⟨712739, by rfl⟩ : syracuseStep 950319 = 1425479) B1425479
theorem B950631 : Blo 948586 950631 := bstep (se 1 (by rfl) ⟨712973, by rfl⟩ : syracuseStep 950631 = 1425947) B1425947
theorem B950719 : Blo 948586 950719 := bstep (se 1 (by rfl) ⟨713039, by rfl⟩ : syracuseStep 950719 = 1426079) B1426079
theorem B3605255 : Blo 948586 3605255 := bstep (se 1 (by rfl) ⟨2703941, by rfl⟩ : syracuseStep 3605255 = 5407883) B5407883
theorem B951295 : Blo 948586 951295 := bstep (se 1 (by rfl) ⟨713471, by rfl⟩ : syracuseStep 951295 = 1426943) B1426943
theorem B24315065 : Blo 948586 24315065 := bstep (se 2 (by rfl) ⟨9118149, by rfl⟩ : syracuseStep 24315065 = 18236299) B18236299
theorem B46269629 : Blo 948586 46269629 := bstep (se 3 (by rfl) ⟨8675555, by rfl⟩ : syracuseStep 46269629 = 17351111) B17351111
theorem B951623 : Blo 948586 951623 := bstep (se 1 (by rfl) ⟨713717, by rfl⟩ : syracuseStep 951623 = 1427435) B1427435
theorem B3475415 : Blo 948586 3475415 := bstep (se 1 (by rfl) ⟨2606561, by rfl⟩ : syracuseStep 3475415 = 5213123) B5213123
theorem B3606515 : Blo 948586 3606515 := bstep (se 1 (by rfl) ⟨2704886, by rfl⟩ : syracuseStep 3606515 = 5409773) B5409773
theorem B952319 : Blo 948586 952319 := bstep (se 1 (by rfl) ⟨714239, by rfl⟩ : syracuseStep 952319 = 1428479) B1428479
theorem B952383 : Blo 948586 952383 := bstep (se 1 (by rfl) ⟨714287, by rfl⟩ : syracuseStep 952383 = 1428575) B1428575
theorem B16223165 : Blo 948586 16223165 := bstep (se 3 (by rfl) ⟨3041843, by rfl⟩ : syracuseStep 16223165 = 6083687) B6083687
theorem B3050455 : Blo 948586 3050455 := bstep (se 1 (by rfl) ⟨2287841, by rfl⟩ : syracuseStep 3050455 = 4575683) B4575683
theorem B8360081 : Blo 948586 8360081 := bstep (se 2 (by rfl) ⟨3135030, by rfl⟩ : syracuseStep 8360081 = 6270061) B6270061
theorem B1807913 : Blo 948586 1807913 := bstep (se 2 (by rfl) ⟨677967, by rfl⟩ : syracuseStep 1807913 = 1355935) B1355935
theorem B2136041 : Blo 948586 2136041 := bstep (se 2 (by rfl) ⟨801015, by rfl⟩ : syracuseStep 2136041 = 1602031) B1602031
theorem B1710571 : Blo 948586 1710571 := bstep (se 1 (by rfl) ⟨1282928, by rfl⟩ : syracuseStep 1710571 = 2565857) B2565857
theorem B2136617 : Blo 948586 2136617 := bstep (se 2 (by rfl) ⟨801231, by rfl⟩ : syracuseStep 2136617 = 1602463) B1602463
theorem B2136671 : Blo 948586 2136671 := bstep (se 1 (by rfl) ⟨1602503, by rfl⟩ : syracuseStep 2136671 = 3205007) B3205007
theorem B3612073 : Blo 948586 3612073 := bstep (se 2 (by rfl) ⟨1354527, by rfl⟩ : syracuseStep 3612073 = 2709055) B2709055
theorem B2170495 : Blo 948586 2170495 := bstep (se 1 (by rfl) ⟨1627871, by rfl⟩ : syracuseStep 2170495 = 3255743) B3255743
theorem B6102809 : Blo 948586 6102809 := bstep (se 2 (by rfl) ⟨2288553, by rfl⟩ : syracuseStep 6102809 = 4577107) B4577107
theorem B1712191 : Blo 948586 1712191 := bstep (se 1 (by rfl) ⟨1284143, by rfl⟩ : syracuseStep 1712191 = 2568287) B2568287
theorem B59319641 : Blo 948586 59319641 := bstep (se 2 (by rfl) ⟨22244865, by rfl⟩ : syracuseStep 59319641 = 44489731) B44489731
theorem B3089947 : Blo 948586 3089947 := bstep (se 1 (by rfl) ⟨2317460, by rfl⟩ : syracuseStep 3089947 = 4634921) B4634921
theorem B55649855 : Blo 948586 55649855 := bstep (se 1 (by rfl) ⟨41737391, by rfl⟩ : syracuseStep 55649855 = 83474783) B83474783
theorem B2140775 : Blo 948586 2140775 := bstep (se 1 (by rfl) ⟨1605581, by rfl⟩ : syracuseStep 2140775 = 3211163) B3211163
theorem B2140937 : Blo 948586 2140937 := bstep (se 2 (by rfl) ⟨802851, by rfl⟩ : syracuseStep 2140937 = 1605703) B1605703
theorem B9153485 : Blo 948586 9153485 := bstep (se 3 (by rfl) ⟨1716278, by rfl⟩ : syracuseStep 9153485 = 3432557) B3432557
theorem B4337327 : Blo 948586 4337327 := bstep (se 1 (by rfl) ⟨3252995, by rfl⟩ : syracuseStep 4337327 = 6505991) B6505991
theorem B2142377 : Blo 948586 2142377 := bstep (se 2 (by rfl) ⟨803391, by rfl⟩ : syracuseStep 2142377 = 1606783) B1606783
theorem B4337999 : Blo 948586 4337999 := bstep (se 1 (by rfl) ⟨3253499, by rfl⟩ : syracuseStep 4337999 = 6506999) B6506999
theorem B55619921 : Blo 948586 55619921 := bstep (se 2 (by rfl) ⟨20857470, by rfl⟩ : syracuseStep 55619921 = 41714941) B41714941
theorem B17347607 : Blo 948586 17347607 := bstep (se 1 (by rfl) ⟨13010705, by rfl⟩ : syracuseStep 17347607 = 26021411) B26021411
theorem B2143259 : Blo 948586 2143259 := bstep (se 1 (by rfl) ⟨1607444, by rfl⟩ : syracuseStep 2143259 = 3214889) B3214889
theorem B11580985 : Blo 948586 11580985 := bstep (se 2 (by rfl) ⟨4342869, by rfl⟩ : syracuseStep 11580985 = 8685739) B8685739
theorem B7911179 : Blo 948586 7911179 := bstep (se 1 (by rfl) ⟨5933384, by rfl⟩ : syracuseStep 7911179 = 11866769) B11866769
theorem B1521737 : Blo 948586 1521737 := bstep (se 2 (by rfl) ⟨570651, by rfl⟩ : syracuseStep 1521737 = 1141303) B1141303
theorem B1423679 : Blo 948586 1423679 := bstep (se 1 (by rfl) ⟨1067759, by rfl⟩ : syracuseStep 1423679 = 2135519) B2135519
theorem B208059151 : Blo 948586 208059151 := bstep (se 1 (by rfl) ⟨156044363, by rfl⟩ : syracuseStep 208059151 = 312088727) B312088727
theorem B2702335 : Blo 948586 2702335 := bstep (se 1 (by rfl) ⟨2026751, by rfl⟩ : syracuseStep 2702335 = 4053503) B4053503
theorem B46840927 : Blo 948586 46840927 := bstep (se 1 (by rfl) ⟨35130695, by rfl⟩ : syracuseStep 46840927 = 70261391) B70261391
theorem B1424543 : Blo 948586 1424543 := bstep (se 1 (by rfl) ⟨1068407, by rfl⟩ : syracuseStep 1424543 = 2136815) B2136815
theorem B1425383 : Blo 948586 1425383 := bstep (se 1 (by rfl) ⟨1069037, by rfl⟩ : syracuseStep 1425383 = 2138075) B2138075
theorem B1523767 : Blo 948586 1523767 := bstep (se 1 (by rfl) ⟨1142825, by rfl⟩ : syracuseStep 1523767 = 2285651) B2285651
theorem B1425563 : Blo 948586 1425563 := bstep (se 1 (by rfl) ⟨1069172, by rfl⟩ : syracuseStep 1425563 = 2138345) B2138345
theorem B13877405 : Blo 948586 13877405 := bstep (se 3 (by rfl) ⟨2602013, by rfl⟩ : syracuseStep 13877405 = 5204027) B5204027
theorem B2343707 : Blo 948586 2343707 := bstep (se 1 (by rfl) ⟨1757780, by rfl⟩ : syracuseStep 2343707 = 3515561) B3515561
theorem B30851873 : Blo 948586 30851873 := bstep (se 2 (by rfl) ⟨11569452, by rfl⟩ : syracuseStep 30851873 = 23138905) B23138905
theorem B2704681 : Blo 948586 2704681 := bstep (se 2 (by rfl) ⟨1014255, by rfl⟩ : syracuseStep 2704681 = 2028511) B2028511
theorem B9390431 : Blo 948586 9390431 := bstep (se 1 (by rfl) ⟨7042823, by rfl⟩ : syracuseStep 9390431 = 14085647) B14085647
theorem B1427903 : Blo 948586 1427903 := bstep (se 1 (by rfl) ⟨1070927, by rfl⟩ : syracuseStep 1427903 = 2141855) B2141855
theorem B1428335 : Blo 948586 1428335 := bstep (se 1 (by rfl) ⟨1071251, by rfl⟩ : syracuseStep 1428335 = 2142503) B2142503
theorem B8474627 : Blo 948586 8474627 := bstep (se 1 (by rfl) ⟨6355970, by rfl⟩ : syracuseStep 8474627 = 12711941) B12711941
theorem B10276955 : Blo 948586 10276955 := bstep (se 1 (by rfl) ⟨7707716, by rfl⟩ : syracuseStep 10276955 = 15415433) B15415433
theorem B34624583 : Blo 948586 34624583 := bstep (se 1 (by rfl) ⟨25968437, by rfl⟩ : syracuseStep 34624583 = 51936875) B51936875
theorem B7525889 : Blo 948586 7525889 := bstep (se 2 (by rfl) ⟨2822208, by rfl⟩ : syracuseStep 7525889 = 5644417) B5644417
theorem B6182675 : Blo 948586 6182675 := bstep (se 1 (by rfl) ⟨4637006, by rfl⟩ : syracuseStep 6182675 = 9274013) B9274013
theorem B4053179 : Blo 948586 4053179 := bstep (se 1 (by rfl) ⟨3039884, by rfl⟩ : syracuseStep 4053179 = 6079769) B6079769
theorem B3201551 : Blo 948586 3201551 := bstep (se 1 (by rfl) ⟨2401163, by rfl⟩ : syracuseStep 3201551 = 4802327) B4802327
theorem B8116847 : Blo 948586 8116847 := bstep (se 1 (by rfl) ⟨6087635, by rfl⟩ : syracuseStep 8116847 = 12175271) B12175271
theorem B1924091 : Blo 948586 1924091 := bstep (se 1 (by rfl) ⟨1443068, by rfl⟩ : syracuseStep 1924091 = 2886137) B2886137
theorem B2710559 : Blo 948586 2710559 := bstep (se 1 (by rfl) ⟨2032919, by rfl⟩ : syracuseStep 2710559 = 4065839) B4065839
theorem B55631137 : Blo 948586 55631137 := bstep (se 2 (by rfl) ⟨20861676, by rfl⟩ : syracuseStep 55631137 = 41723353) B41723353
theorem B12345547 : Blo 948586 12345547 := bstep (se 1 (by rfl) ⟨9259160, by rfl⟩ : syracuseStep 12345547 = 18518321) B18518321
theorem B4809455 : Blo 948586 4809455 := bstep (se 1 (by rfl) ⟨3607091, by rfl⟩ : syracuseStep 4809455 = 7214183) B7214183
theorem B3204737 : Blo 948586 3204737 := bstep (se 2 (by rfl) ⟨1201776, by rfl⟩ : syracuseStep 3204737 = 2403553) B2403553
theorem B3205871 : Blo 948586 3205871 := bstep (se 1 (by rfl) ⟨2404403, by rfl⟩ : syracuseStep 3205871 = 4808807) B4808807
theorem B1141499 : Blo 948586 1141499 := bstep (se 1 (by rfl) ⟨856124, by rfl⟩ : syracuseStep 1141499 = 1712249) B1712249
theorem B3207545 : Blo 948586 3207545 := bstep (se 2 (by rfl) ⟨1202829, by rfl⟩ : syracuseStep 3207545 = 2405659) B2405659
theorem B43840187 : Blo 948586 43840187 := bstep (se 1 (by rfl) ⟨32880140, by rfl⟩ : syracuseStep 43840187 = 65760281) B65760281
theorem B4879673 : Blo 948586 4879673 := bstep (se 2 (by rfl) ⟨1829877, by rfl⟩ : syracuseStep 4879673 = 3659755) B3659755
theorem B948671 : Blo 948586 948671 := bstep (se 1 (by rfl) ⟨711503, by rfl⟩ : syracuseStep 948671 = 1423007) B1423007
theorem B7698959 : Blo 948586 7698959 := bstep (se 1 (by rfl) ⟨5774219, by rfl⟩ : syracuseStep 7698959 = 11548439) B11548439
theorem B948927 : Blo 948586 948927 := bstep (se 1 (by rfl) ⟨711695, by rfl⟩ : syracuseStep 948927 = 1423391) B1423391
theorem B7699151 : Blo 948586 7699151 := bstep (se 1 (by rfl) ⟨5774363, by rfl⟩ : syracuseStep 7699151 = 11548727) B11548727
theorem B949019 : Blo 948586 949019 := bstep (se 1 (by rfl) ⟨711764, by rfl⟩ : syracuseStep 949019 = 1423529) B1423529
theorem B3472159 : Blo 948586 3472159 := bstep (se 1 (by rfl) ⟨2604119, by rfl⟩ : syracuseStep 3472159 = 5208239) B5208239
theorem B3210407 : Blo 948586 3210407 := bstep (se 1 (by rfl) ⟨2407805, by rfl⟩ : syracuseStep 3210407 = 4815611) B4815611
theorem B949919 : Blo 948586 949919 := bstep (se 1 (by rfl) ⟨712439, by rfl⟩ : syracuseStep 949919 = 1424879) B1424879
theorem B949951 : Blo 948586 949951 := bstep (se 1 (by rfl) ⟨712463, by rfl⟩ : syracuseStep 949951 = 1424927) B1424927
theorem B2031689 : Blo 948586 2031689 := bstep (se 2 (by rfl) ⟨761883, by rfl⟩ : syracuseStep 2031689 = 1523767) B1523767
theorem B950375 : Blo 948586 950375 := bstep (se 1 (by rfl) ⟨712781, by rfl⟩ : syracuseStep 950375 = 1425563) B1425563
theorem B6260287 : Blo 948586 6260287 := bstep (se 1 (by rfl) ⟨4695215, by rfl⟩ : syracuseStep 6260287 = 9390431) B9390431
theorem B951935 : Blo 948586 951935 := bstep (se 1 (by rfl) ⟨713951, by rfl⟩ : syracuseStep 951935 = 1427903) B1427903
theorem B3606241 : Blo 948586 3606241 := bstep (se 2 (by rfl) ⟨1352340, by rfl⟩ : syracuseStep 3606241 = 2704681) B2704681
theorem B952223 : Blo 948586 952223 := bstep (se 1 (by rfl) ⟨714167, by rfl⟩ : syracuseStep 952223 = 1428335) B1428335
theorem B10815443 : Blo 948586 10815443 := bstep (se 1 (by rfl) ⟨8111582, by rfl⟩ : syracuseStep 10815443 = 16223165) B16223165
theorem B6851303 : Blo 948586 6851303 := bstep (se 1 (by rfl) ⟨5138477, by rfl⟩ : syracuseStep 6851303 = 10276955) B10276955
theorem B5573387 : Blo 948586 5573387 := bstep (se 1 (by rfl) ⟨4180040, by rfl⟩ : syracuseStep 5573387 = 8360081) B8360081
theorem B5017259 : Blo 948586 5017259 := bstep (se 1 (by rfl) ⟨3762944, by rfl⟩ : syracuseStep 5017259 = 7525889) B7525889
theorem B4067273 : Blo 948586 4067273 := bstep (se 2 (by rfl) ⟨1525227, by rfl⟩ : syracuseStep 4067273 = 3050455) B3050455
theorem B2134367 : Blo 948586 2134367 := bstep (se 1 (by rfl) ⟨1600775, by rfl⟩ : syracuseStep 2134367 = 3201551) B3201551
theorem B5411231 : Blo 948586 5411231 := bstep (se 1 (by rfl) ⟨4058423, by rfl⟩ : syracuseStep 5411231 = 8116847) B8116847
theorem B1282727 : Blo 948586 1282727 := bstep (se 1 (by rfl) ⟨962045, by rfl⟩ : syracuseStep 1282727 = 1924091) B1924091
theorem B1807039 : Blo 948586 1807039 := bstep (se 1 (by rfl) ⟨1355279, by rfl⟩ : syracuseStep 1807039 = 2710559) B2710559
theorem B4068539 : Blo 948586 4068539 := bstep (se 1 (by rfl) ⟨3051404, by rfl⟩ : syracuseStep 4068539 = 6102809) B6102809
theorem B37099903 : Blo 948586 37099903 := bstep (se 1 (by rfl) ⟨27824927, by rfl⟩ : syracuseStep 37099903 = 55649855) B55649855
theorem B2136491 : Blo 948586 2136491 := bstep (se 1 (by rfl) ⟨1602368, by rfl⟩ : syracuseStep 2136491 = 3204737) B3204737
theorem B2137247 : Blo 948586 2137247 := bstep (se 1 (by rfl) ⟨1602935, by rfl⟩ : syracuseStep 2137247 = 3205871) B3205871
theorem B6102323 : Blo 948586 6102323 := bstep (se 1 (by rfl) ⟨4576742, by rfl⟩ : syracuseStep 6102323 = 9153485) B9153485
theorem B2891551 : Blo 948586 2891551 := bstep (se 1 (by rfl) ⟨2168663, by rfl⟩ : syracuseStep 2891551 = 4337327) B4337327
theorem B2891999 : Blo 948586 2891999 := bstep (se 1 (by rfl) ⟨2168999, by rfl⟩ : syracuseStep 2891999 = 4337999) B4337999
theorem B2138363 : Blo 948586 2138363 := bstep (se 1 (by rfl) ⟨1603772, by rfl⟩ : syracuseStep 2138363 = 3207545) B3207545
theorem B11575973 : Blo 948586 11575973 := bstep (se 4 (by rfl) ⟨1085247, by rfl⟩ : syracuseStep 11575973 = 2170495) B2170495
theorem B3253115 : Blo 948586 3253115 := bstep (se 1 (by rfl) ⟨2439836, by rfl⟩ : syracuseStep 3253115 = 4879673) B4879673
theorem B4629545 : Blo 948586 4629545 := bstep (se 2 (by rfl) ⟨1736079, by rfl⟩ : syracuseStep 4629545 = 3472159) B3472159
theorem B2140271 : Blo 948586 2140271 := bstep (se 1 (by rfl) ⟨1605203, by rfl⟩ : syracuseStep 2140271 = 3210407) B3210407
theorem B9251603 : Blo 948586 9251603 := bstep (se 1 (by rfl) ⟨6938702, by rfl⟩ : syracuseStep 9251603 = 13877405) B13877405
theorem B16460729 : Blo 948586 16460729 := bstep (se 2 (by rfl) ⟨6172773, by rfl⟩ : syracuseStep 16460729 = 12345547) B12345547
theorem B2403503 : Blo 948586 2403503 := bstep (se 1 (by rfl) ⟨1802627, by rfl⟩ : syracuseStep 2403503 = 3605255) B3605255
theorem B30846419 : Blo 948586 30846419 := bstep (se 1 (by rfl) ⟨23134814, by rfl⟩ : syracuseStep 30846419 = 46269629) B46269629
theorem B2404343 : Blo 948586 2404343 := bstep (se 1 (by rfl) ⟨1803257, by rfl⟩ : syracuseStep 2404343 = 3606515) B3606515
theorem B5649751 : Blo 948586 5649751 := bstep (se 1 (by rfl) ⟨4237313, by rfl⟩ : syracuseStep 5649751 = 8474627) B8474627
theorem B23083055 : Blo 948586 23083055 := bstep (se 1 (by rfl) ⟨17312291, by rfl⟩ : syracuseStep 23083055 = 34624583) B34624583
theorem B158185709 : Blo 948586 158185709 := bstep (se 3 (by rfl) ⟨29659820, by rfl⟩ : syracuseStep 158185709 = 59319641) B59319641
theorem B1424027 : Blo 948586 1424027 := bstep (se 1 (by rfl) ⟨1068020, by rfl⟩ : syracuseStep 1424027 = 2136041) B2136041
theorem B2702119 : Blo 948586 2702119 := bstep (se 1 (by rfl) ⟨2026589, by rfl⟩ : syracuseStep 2702119 = 4053179) B4053179
theorem B1424411 : Blo 948586 1424411 := bstep (se 1 (by rfl) ⟨1068308, by rfl⟩ : syracuseStep 1424411 = 2136617) B2136617
theorem B1424447 : Blo 948586 1424447 := bstep (se 1 (by rfl) ⟨1068335, by rfl⟩ : syracuseStep 1424447 = 2136671) B2136671
theorem B1427183 : Blo 948586 1427183 := bstep (se 1 (by rfl) ⟨1070387, by rfl⟩ : syracuseStep 1427183 = 2140775) B2140775
theorem B1427291 : Blo 948586 1427291 := bstep (se 1 (by rfl) ⟨1070468, by rfl⟩ : syracuseStep 1427291 = 2140937) B2140937
theorem B1428251 : Blo 948586 1428251 := bstep (se 1 (by rfl) ⟨1071188, by rfl⟩ : syracuseStep 1428251 = 2142377) B2142377
theorem B37079947 : Blo 948586 37079947 := bstep (se 1 (by rfl) ⟨27809960, by rfl⟩ : syracuseStep 37079947 = 55619921) B55619921
theorem B2280761 : Blo 948586 2280761 := bstep (se 2 (by rfl) ⟨855285, by rfl⟩ : syracuseStep 2280761 = 1710571) B1710571
theorem B1428839 : Blo 948586 1428839 := bstep (se 1 (by rfl) ⟨1071629, by rfl⟩ : syracuseStep 1428839 = 2143259) B2143259
theorem B5132639 : Blo 948586 5132639 := bstep (se 1 (by rfl) ⟨3849479, by rfl⟩ : syracuseStep 5132639 = 7698959) B7698959
theorem B74174849 : Blo 948586 74174849 := bstep (se 2 (by rfl) ⟨27815568, by rfl⟩ : syracuseStep 74174849 = 55631137) B55631137
theorem B5132767 : Blo 948586 5132767 := bstep (se 1 (by rfl) ⟨3849575, by rfl⟩ : syracuseStep 5132767 = 7699151) B7699151
theorem B2282921 : Blo 948586 2282921 := bstep (se 2 (by rfl) ⟨856095, by rfl⟩ : syracuseStep 2282921 = 1712191) B1712191
theorem B1562471 : Blo 948586 1562471 := bstep (se 1 (by rfl) ⟨1171853, by rfl⟩ : syracuseStep 1562471 = 2343707) B2343707
theorem B20567915 : Blo 948586 20567915 := bstep (se 1 (by rfl) ⟨15425936, by rfl⟩ : syracuseStep 20567915 = 30851873) B30851873
theorem B16210043 : Blo 948586 16210043 := bstep (se 1 (by rfl) ⟨12157532, by rfl⟩ : syracuseStep 16210043 = 24315065) B24315065
theorem B2316943 : Blo 948586 2316943 := bstep (se 1 (by rfl) ⟨1737707, by rfl⟩ : syracuseStep 2316943 = 3475415) B3475415
theorem B4119929 : Blo 948586 4119929 := bstep (se 2 (by rfl) ⟨1544973, by rfl⟩ : syracuseStep 4119929 = 3089947) B3089947
theorem B1205275 : Blo 948586 1205275 := bstep (se 1 (by rfl) ⟨903956, by rfl⟩ : syracuseStep 1205275 = 1807913) B1807913
theorem B4121783 : Blo 948586 4121783 := bstep (se 1 (by rfl) ⟨3091337, by rfl⟩ : syracuseStep 4121783 = 6182675) B6182675
theorem B3206303 : Blo 948586 3206303 := bstep (se 1 (by rfl) ⟨2404727, by rfl⟩ : syracuseStep 3206303 = 4809455) B4809455
theorem B3043997 : Blo 948586 3043997 := bstep (se 3 (by rfl) ⟨570749, by rfl⟩ : syracuseStep 3043997 = 1141499) B1141499
theorem B61765253 : Blo 948586 61765253 := bstep (se 4 (by rfl) ⟨5790492, by rfl⟩ : syracuseStep 61765253 = 11580985) B11580985
theorem B29226791 : Blo 948586 29226791 := bstep (se 1 (by rfl) ⟨21920093, by rfl⟩ : syracuseStep 29226791 = 43840187) B43840187
theorem B11565071 : Blo 948586 11565071 := bstep (se 1 (by rfl) ⟨8673803, by rfl⟩ : syracuseStep 11565071 = 17347607) B17347607
theorem B277412201 : Blo 948586 277412201 := bstep (se 2 (by rfl) ⟨104029575, by rfl⟩ : syracuseStep 277412201 = 208059151) B208059151
theorem B5274119 : Blo 948586 5274119 := bstep (se 1 (by rfl) ⟨3955589, by rfl⟩ : syracuseStep 5274119 = 7911179) B7911179
theorem B3603113 : Blo 948586 3603113 := bstep (se 2 (by rfl) ⟨1351167, by rfl⟩ : syracuseStep 3603113 = 2702335) B2702335
theorem B1014491 : Blo 948586 1014491 := bstep (se 1 (by rfl) ⟨760868, by rfl⟩ : syracuseStep 1014491 = 1521737) B1521737
theorem B62454569 : Blo 948586 62454569 := bstep (se 2 (by rfl) ⟨23420463, by rfl⟩ : syracuseStep 62454569 = 46840927) B46840927
theorem B949119 : Blo 948586 949119 := bstep (se 1 (by rfl) ⟨711839, by rfl⟩ : syracuseStep 949119 = 1423679) B1423679
theorem B4816097 : Blo 948586 4816097 := bstep (se 2 (by rfl) ⟨1806036, by rfl⟩ : syracuseStep 4816097 = 3612073) B3612073
theorem B949695 : Blo 948586 949695 := bstep (se 1 (by rfl) ⟨712271, by rfl⟩ : syracuseStep 949695 = 1424543) B1424543
theorem B950255 : Blo 948586 950255 := bstep (se 1 (by rfl) ⟨712691, by rfl⟩ : syracuseStep 950255 = 1425383) B1425383
theorem B951455 : Blo 948586 951455 := bstep (se 1 (by rfl) ⟨713591, by rfl⟩ : syracuseStep 951455 = 1427183) B1427183
theorem B951527 : Blo 948586 951527 := bstep (se 1 (by rfl) ⟨713645, by rfl⟩ : syracuseStep 951527 = 1427291) B1427291
theorem B7210295 : Blo 948586 7210295 := bstep (se 1 (by rfl) ⟨5407721, by rfl⟩ : syracuseStep 7210295 = 10815443) B10815443
theorem B1607033 : Blo 948586 1607033 := bstep (se 2 (by rfl) ⟨602637, by rfl⟩ : syracuseStep 1607033 = 1205275) B1205275
theorem B952167 : Blo 948586 952167 := bstep (se 1 (by rfl) ⟨714125, by rfl⟩ : syracuseStep 952167 = 1428251) B1428251
theorem B952559 : Blo 948586 952559 := bstep (se 1 (by rfl) ⟨714419, by rfl⟩ : syracuseStep 952559 = 1428839) B1428839
theorem B3344839 : Blo 948586 3344839 := bstep (se 1 (by rfl) ⟨2508629, by rfl⟩ : syracuseStep 3344839 = 5017259) B5017259
theorem B49449899 : Blo 948586 49449899 := bstep (se 1 (by rfl) ⟨37087424, by rfl⟩ : syracuseStep 49449899 = 74174849) B74174849
theorem B3607487 : Blo 948586 3607487 := bstep (se 1 (by rfl) ⟨2705615, by rfl⟩ : syracuseStep 3607487 = 5411231) B5411231
theorem B12357029 : Blo 948586 12357029 := bstep (se 4 (by rfl) ⟨1158471, by rfl⟩ : syracuseStep 12357029 = 2316943) B2316943
theorem B197759717 : Blo 948586 197759717 := bstep (se 4 (by rfl) ⟨18539973, by rfl⟩ : syracuseStep 197759717 = 37079947) B37079947
theorem B4068215 : Blo 948586 4068215 := bstep (se 1 (by rfl) ⟨3051161, by rfl⟩ : syracuseStep 4068215 = 6102323) B6102323
theorem B2168743 : Blo 948586 2168743 := bstep (se 1 (by rfl) ⟨1626557, by rfl⟩ : syracuseStep 2168743 = 3253115) B3253115
theorem B3086363 : Blo 948586 3086363 := bstep (se 1 (by rfl) ⟨2314772, by rfl⟩ : syracuseStep 3086363 = 4629545) B4629545
theorem B14064317 : Blo 948586 14064317 := bstep (se 3 (by rfl) ⟨2637059, by rfl⟩ : syracuseStep 14064317 = 5274119) B5274119
theorem B6167735 : Blo 948586 6167735 := bstep (se 1 (by rfl) ⟨4625801, by rfl⟩ : syracuseStep 6167735 = 9251603) B9251603
theorem B2137535 : Blo 948586 2137535 := bstep (se 1 (by rfl) ⟨1603151, by rfl⟩ : syracuseStep 2137535 = 3206303) B3206303
theorem B7710047 : Blo 948586 7710047 := bstep (se 1 (by rfl) ⟨5782535, by rfl⟩ : syracuseStep 7710047 = 11565071) B11565071
theorem B105457139 : Blo 948586 105457139 := bstep (se 1 (by rfl) ⟨79092854, by rfl⟩ : syracuseStep 105457139 = 158185709) B158185709
theorem B2402075 : Blo 948586 2402075 := bstep (se 1 (by rfl) ⟨1801556, by rfl⟩ : syracuseStep 2402075 = 3603113) B3603113
theorem B5417837 : Blo 948586 5417837 := bstep (se 3 (by rfl) ⟨1015844, by rfl⟩ : syracuseStep 5417837 = 2031689) B2031689
theorem B3420605 : Blo 948586 3420605 := bstep (se 3 (by rfl) ⟨641363, by rfl⟩ : syracuseStep 3420605 = 1282727) B1282727
theorem B4567535 : Blo 948586 4567535 := bstep (se 1 (by rfl) ⟨3425651, by rfl⟩ : syracuseStep 4567535 = 6851303) B6851303
theorem B3715591 : Blo 948586 3715591 := bstep (se 1 (by rfl) ⟨2786693, by rfl⟩ : syracuseStep 3715591 = 5573387) B5573387
theorem B1520507 : Blo 948586 1520507 := bstep (se 1 (by rfl) ⟨1140380, by rfl⟩ : syracuseStep 1520507 = 2280761) B2280761
theorem B1422911 : Blo 948586 1422911 := bstep (se 1 (by rfl) ⟨1067183, by rfl⟩ : syracuseStep 1422911 = 2134367) B2134367
theorem B3421759 : Blo 948586 3421759 := bstep (se 1 (by rfl) ⟨2566319, by rfl⟩ : syracuseStep 3421759 = 5132639) B5132639
theorem B1521947 : Blo 948586 1521947 := bstep (se 1 (by rfl) ⟨1141460, by rfl⟩ : syracuseStep 1521947 = 2282921) B2282921
theorem B13711943 : Blo 948586 13711943 := bstep (se 1 (by rfl) ⟨10283957, by rfl⟩ : syracuseStep 13711943 = 20567915) B20567915
theorem B1424327 : Blo 948586 1424327 := bstep (se 1 (by rfl) ⟨1068245, by rfl⟩ : syracuseStep 1424327 = 2136491) B2136491
theorem B77938109 : Blo 948586 77938109 := bstep (se 3 (by rfl) ⟨14613395, by rfl⟩ : syracuseStep 77938109 = 29226791) B29226791
theorem B1424831 : Blo 948586 1424831 := bstep (se 1 (by rfl) ⟨1068623, by rfl⟩ : syracuseStep 1424831 = 2137247) B2137247
theorem B1425575 : Blo 948586 1425575 := bstep (se 1 (by rfl) ⟨1069181, by rfl⟩ : syracuseStep 1425575 = 2138363) B2138363
theorem B7717315 : Blo 948586 7717315 := bstep (se 1 (by rfl) ⟨5787986, by rfl⟩ : syracuseStep 7717315 = 11575973) B11575973
theorem B2409385 : Blo 948586 2409385 := bstep (se 2 (by rfl) ⟨903519, by rfl⟩ : syracuseStep 2409385 = 1807039) B1807039
theorem B1426847 : Blo 948586 1426847 := bstep (se 1 (by rfl) ⟨1070135, by rfl⟩ : syracuseStep 1426847 = 2140271) B2140271
theorem B2705309 : Blo 948586 2705309 := bstep (se 3 (by rfl) ⟨507245, by rfl⟩ : syracuseStep 2705309 = 1014491) B1014491
theorem B166545517 : Blo 948586 166545517 := bstep (se 3 (by rfl) ⟨31227284, by rfl⟩ : syracuseStep 166545517 = 62454569) B62454569
theorem B20564279 : Blo 948586 20564279 := bstep (se 1 (by rfl) ⟨15423209, by rfl⟩ : syracuseStep 20564279 = 30846419) B30846419
theorem B49466537 : Blo 948586 49466537 := bstep (se 2 (by rfl) ⟨18549951, by rfl⟩ : syracuseStep 49466537 = 37099903) B37099903
theorem B41176835 : Blo 948586 41176835 := bstep (se 1 (by rfl) ⟨30882626, by rfl⟩ : syracuseStep 41176835 = 61765253) B61765253
theorem B15388703 : Blo 948586 15388703 := bstep (se 1 (by rfl) ⟨11541527, by rfl⟩ : syracuseStep 15388703 = 23083055) B23083055
theorem B3855401 : Blo 948586 3855401 := bstep (se 2 (by rfl) ⟨1445775, by rfl⟩ : syracuseStep 3855401 = 2891551) B2891551
theorem B8347049 : Blo 948586 8347049 := bstep (se 2 (by rfl) ⟨3130143, by rfl⟩ : syracuseStep 8347049 = 6260287) B6260287
theorem B4808321 : Blo 948586 4808321 := bstep (se 2 (by rfl) ⟨1803120, by rfl⟩ : syracuseStep 4808321 = 3606241) B3606241
theorem B2712359 : Blo 948586 2712359 := bstep (se 1 (by rfl) ⟨2034269, by rfl⟩ : syracuseStep 2712359 = 4068539) B4068539
theorem B1041647 : Blo 948586 1041647 := bstep (se 1 (by rfl) ⟨781235, by rfl⟩ : syracuseStep 1041647 = 1562471) B1562471
theorem B10806695 : Blo 948586 10806695 := bstep (se 1 (by rfl) ⟨8105021, by rfl⟩ : syracuseStep 10806695 = 16210043) B16210043
theorem B2746619 : Blo 948586 2746619 := bstep (se 1 (by rfl) ⟨2059964, by rfl⟩ : syracuseStep 2746619 = 4119929) B4119929
theorem B1927999 : Blo 948586 1927999 := bstep (se 1 (by rfl) ⟨1445999, by rfl⟩ : syracuseStep 1927999 = 2891999) B2891999
theorem B6843689 : Blo 948586 6843689 := bstep (se 2 (by rfl) ⟨2566383, by rfl⟩ : syracuseStep 6843689 = 5132767) B5132767
theorem B2747855 : Blo 948586 2747855 := bstep (se 1 (by rfl) ⟨2060891, by rfl⟩ : syracuseStep 2747855 = 4121783) B4121783
theorem B7533001 : Blo 948586 7533001 := bstep (se 2 (by rfl) ⟨2824875, by rfl⟩ : syracuseStep 7533001 = 5649751) B5649751
theorem B10973819 : Blo 948586 10973819 := bstep (se 1 (by rfl) ⟨8230364, by rfl⟩ : syracuseStep 10973819 = 16460729) B16460729
theorem B1602335 : Blo 948586 1602335 := bstep (se 1 (by rfl) ⟨1201751, by rfl⟩ : syracuseStep 1602335 = 2403503) B2403503
theorem B1602895 : Blo 948586 1602895 := bstep (se 1 (by rfl) ⟨1202171, by rfl⟩ : syracuseStep 1602895 = 2404343) B2404343
theorem B2029331 : Blo 948586 2029331 := bstep (se 1 (by rfl) ⟨1521998, by rfl⟩ : syracuseStep 2029331 = 3043997) B3043997
theorem B3602825 : Blo 948586 3602825 := bstep (se 2 (by rfl) ⟨1351059, by rfl⟩ : syracuseStep 3602825 = 2702119) B2702119
theorem B184941467 : Blo 948586 184941467 := bstep (se 1 (by rfl) ⟨138706100, by rfl⟩ : syracuseStep 184941467 = 277412201) B277412201
theorem B949351 : Blo 948586 949351 := bstep (se 1 (by rfl) ⟨712013, by rfl⟩ : syracuseStep 949351 = 1424027) B1424027
theorem B949607 : Blo 948586 949607 := bstep (se 1 (by rfl) ⟨712205, by rfl⟩ : syracuseStep 949607 = 1424411) B1424411
theorem B949631 : Blo 948586 949631 := bstep (se 1 (by rfl) ⟨712223, by rfl⟩ : syracuseStep 949631 = 1424447) B1424447
theorem B3210731 : Blo 948586 3210731 := bstep (se 1 (by rfl) ⟨2408048, by rfl⟩ : syracuseStep 3210731 = 4816097) B4816097
theorem B10846061 : Blo 948586 10846061 := bstep (se 3 (by rfl) ⟨2033636, by rfl⟩ : syracuseStep 10846061 = 4067273) B4067273
theorem B950383 : Blo 948586 950383 := bstep (se 1 (by rfl) ⟨712787, by rfl⟩ : syracuseStep 950383 = 1425575) B1425575
theorem B10289753 : Blo 948586 10289753 := bstep (se 2 (by rfl) ⟨3858657, by rfl⟩ : syracuseStep 10289753 = 7717315) B7717315
theorem B951231 : Blo 948586 951231 := bstep (se 1 (by rfl) ⟨713423, by rfl⟩ : syracuseStep 951231 = 1426847) B1426847
theorem B3212513 : Blo 948586 3212513 := bstep (se 2 (by rfl) ⟨1204692, by rfl⟩ : syracuseStep 3212513 = 2409385) B2409385
theorem B1803539 : Blo 948586 1803539 := bstep (se 1 (by rfl) ⟨1352654, by rfl⟩ : syracuseStep 1803539 = 2705309) B2705309
theorem B29263517 : Blo 948586 29263517 := bstep (se 3 (by rfl) ⟨5486909, by rfl⟩ : syracuseStep 29263517 = 10973819) B10973819
theorem B32966599 : Blo 948586 32966599 := bstep (se 1 (by rfl) ⟨24724949, by rfl⟩ : syracuseStep 32966599 = 49449899) B49449899
theorem B10259135 : Blo 948586 10259135 := bstep (se 1 (by rfl) ⟨7694351, by rfl⟩ : syracuseStep 10259135 = 15388703) B15388703
theorem B9376211 : Blo 948586 9376211 := bstep (se 1 (by rfl) ⟨7032158, by rfl⟩ : syracuseStep 9376211 = 14064317) B14064317
theorem B5411549 : Blo 948586 5411549 := bstep (se 3 (by rfl) ⟨1014665, by rfl⟩ : syracuseStep 5411549 = 2029331) B2029331
theorem B1808239 : Blo 948586 1808239 := bstep (se 1 (by rfl) ⟨1356179, by rfl⟩ : syracuseStep 1808239 = 2712359) B2712359
theorem B4954121 : Blo 948586 4954121 := bstep (se 2 (by rfl) ⟨1857795, by rfl⟩ : syracuseStep 4954121 = 3715591) B3715591
theorem B2137193 : Blo 948586 2137193 := bstep (se 2 (by rfl) ⟨801447, by rfl⟩ : syracuseStep 2137193 = 1602895) B1602895
theorem B3611891 : Blo 948586 3611891 := bstep (se 1 (by rfl) ⟨2708918, by rfl⟩ : syracuseStep 3611891 = 5417837) B5417837
theorem B4562345 : Blo 948586 4562345 := bstep (se 2 (by rfl) ⟨1710879, by rfl⟩ : syracuseStep 4562345 = 3421759) B3421759
theorem B4562459 : Blo 948586 4562459 := bstep (se 1 (by rfl) ⟨3421844, by rfl⟩ : syracuseStep 4562459 = 6843689) B6843689
theorem B2891657 : Blo 948586 2891657 := bstep (se 2 (by rfl) ⟨1084371, by rfl⟩ : syracuseStep 2891657 = 2168743) B2168743
theorem B2401883 : Blo 948586 2401883 := bstep (se 1 (by rfl) ⟨1801412, by rfl⟩ : syracuseStep 2401883 = 3602825) B3602825
theorem B2140487 : Blo 948586 2140487 := bstep (se 1 (by rfl) ⟨1605365, by rfl⟩ : syracuseStep 2140487 = 3210731) B3210731
theorem B13709519 : Blo 948586 13709519 := bstep (se 1 (by rfl) ⟨10282139, by rfl⟩ : syracuseStep 13709519 = 20564279) B20564279
theorem B2404991 : Blo 948586 2404991 := bstep (se 1 (by rfl) ⟨1803743, by rfl⟩ : syracuseStep 2404991 = 3607487) B3607487
theorem B32977691 : Blo 948586 32977691 := bstep (se 1 (by rfl) ⟨24733268, by rfl⟩ : syracuseStep 32977691 = 49466537) B49466537
theorem B8238019 : Blo 948586 8238019 := bstep (se 1 (by rfl) ⟨6178514, by rfl⟩ : syracuseStep 8238019 = 12357029) B12357029
theorem B131839811 : Blo 948586 131839811 := bstep (se 1 (by rfl) ⟨98879858, by rfl⟩ : syracuseStep 131839811 = 197759717) B197759717
theorem B2570267 : Blo 948586 2570267 := bstep (se 1 (by rfl) ⟨1927700, by rfl⟩ : syracuseStep 2570267 = 3855401) B3855401
theorem B2570665 : Blo 948586 2570665 := bstep (se 2 (by rfl) ⟨963999, by rfl⟩ : syracuseStep 2570665 = 1927999) B1927999
theorem B4111823 : Blo 948586 4111823 := bstep (se 1 (by rfl) ⟨3083867, by rfl⟩ : syracuseStep 4111823 = 6167735) B6167735
theorem B1425023 : Blo 948586 1425023 := bstep (se 1 (by rfl) ⟨1068767, by rfl⟩ : syracuseStep 1425023 = 2137535) B2137535
theorem B10044001 : Blo 948586 10044001 := bstep (se 2 (by rfl) ⟨3766500, by rfl⟩ : syracuseStep 10044001 = 7533001) B7533001
theorem B70304759 : Blo 948586 70304759 := bstep (se 1 (by rfl) ⟨52728569, by rfl⟩ : syracuseStep 70304759 = 105457139) B105457139
theorem B2280403 : Blo 948586 2280403 := bstep (se 1 (by rfl) ⟨1710302, by rfl⟩ : syracuseStep 2280403 = 3420605) B3420605
theorem B1068223 : Blo 948586 1068223 := bstep (se 1 (by rfl) ⟨801167, by rfl⟩ : syracuseStep 1068223 = 1602335) B1602335
theorem B71356565 : Blo 948586 71356565 := bstep (se 6 (by rfl) ⟨1672419, by rfl⟩ : syracuseStep 71356565 = 3344839) B3344839
theorem B123294311 : Blo 948586 123294311 := bstep (se 1 (by rfl) ⟨92470733, by rfl⟩ : syracuseStep 123294311 = 184941467) B184941467
theorem B51958739 : Blo 948586 51958739 := bstep (se 1 (by rfl) ⟨38969054, by rfl⟩ : syracuseStep 51958739 = 77938109) B77938109
theorem B7230707 : Blo 948586 7230707 := bstep (se 1 (by rfl) ⟨5423030, by rfl⟩ : syracuseStep 7230707 = 10846061) B10846061
theorem B4806863 : Blo 948586 4806863 := bstep (se 1 (by rfl) ⟨3605147, by rfl⟩ : syracuseStep 4806863 = 7210295) B7210295
theorem B1071355 : Blo 948586 1071355 := bstep (se 1 (by rfl) ⟨803516, by rfl⟩ : syracuseStep 1071355 = 1607033) B1607033
theorem B27451223 : Blo 948586 27451223 := bstep (se 1 (by rfl) ⟨20588417, by rfl⟩ : syracuseStep 27451223 = 41176835) B41176835
theorem B222060689 : Blo 948586 222060689 := bstep (se 2 (by rfl) ⟨83272758, by rfl⟩ : syracuseStep 222060689 = 166545517) B166545517
theorem B2712143 : Blo 948586 2712143 := bstep (se 1 (by rfl) ⟨2034107, by rfl⟩ : syracuseStep 2712143 = 4068215) B4068215
theorem B2777725 : Blo 948586 2777725 := bstep (se 3 (by rfl) ⟨520823, by rfl⟩ : syracuseStep 2777725 = 1041647) B1041647
theorem B2057575 : Blo 948586 2057575 := bstep (se 1 (by rfl) ⟨1543181, by rfl⟩ : syracuseStep 2057575 = 3086363) B3086363
theorem B5564699 : Blo 948586 5564699 := bstep (se 1 (by rfl) ⟨4173524, by rfl⟩ : syracuseStep 5564699 = 8347049) B8347049
theorem B3205547 : Blo 948586 3205547 := bstep (se 1 (by rfl) ⟨2404160, by rfl⟩ : syracuseStep 3205547 = 4808321) B4808321
theorem B4058525 : Blo 948586 4058525 := bstep (se 3 (by rfl) ⟨760973, by rfl⟩ : syracuseStep 4058525 = 1521947) B1521947
theorem B5140031 : Blo 948586 5140031 := bstep (se 1 (by rfl) ⟨3855023, by rfl⟩ : syracuseStep 5140031 = 7710047) B7710047
theorem B7204463 : Blo 948586 7204463 := bstep (se 1 (by rfl) ⟨5403347, by rfl⟩ : syracuseStep 7204463 = 10806695) B10806695
theorem B1601383 : Blo 948586 1601383 := bstep (se 1 (by rfl) ⟨1201037, by rfl⟩ : syracuseStep 1601383 = 2402075) B2402075
theorem B1831079 : Blo 948586 1831079 := bstep (se 1 (by rfl) ⟨1373309, by rfl⟩ : syracuseStep 1831079 = 2746619) B2746619
theorem B1831903 : Blo 948586 1831903 := bstep (se 1 (by rfl) ⟨1373927, by rfl⟩ : syracuseStep 1831903 = 2747855) B2747855
theorem B3045023 : Blo 948586 3045023 := bstep (se 1 (by rfl) ⟨2283767, by rfl⟩ : syracuseStep 3045023 = 4567535) B4567535
theorem B1013671 : Blo 948586 1013671 := bstep (se 1 (by rfl) ⟨760253, by rfl⟩ : syracuseStep 1013671 = 1520507) B1520507
theorem B948607 : Blo 948586 948607 := bstep (se 1 (by rfl) ⟨711455, by rfl⟩ : syracuseStep 948607 = 1422911) B1422911
theorem B9141295 : Blo 948586 9141295 := bstep (se 1 (by rfl) ⟨6855971, by rfl⟩ : syracuseStep 9141295 = 13711943) B13711943
theorem B949551 : Blo 948586 949551 := bstep (se 1 (by rfl) ⟨712163, by rfl⟩ : syracuseStep 949551 = 1424327) B1424327
theorem B949887 : Blo 948586 949887 := bstep (se 1 (by rfl) ⟨712415, by rfl⟩ : syracuseStep 949887 = 1424831) B1424831
theorem B190284173 : Blo 948586 190284173 := bstep (se 3 (by rfl) ⟨35678282, by rfl⟩ : syracuseStep 190284173 = 71356565) B71356565
theorem B3607699 : Blo 948586 3607699 := bstep (se 1 (by rfl) ⟨2705774, by rfl⟩ : syracuseStep 3607699 = 5411549) B5411549
theorem B34639159 : Blo 948586 34639159 := bstep (se 1 (by rfl) ⟨25979369, by rfl⟩ : syracuseStep 34639159 = 51958739) B51958739
theorem B14814533 : Blo 948586 14814533 := bstep (se 4 (by rfl) ⟨1388862, by rfl⟩ : syracuseStep 14814533 = 2777725) B2777725
theorem B4820471 : Blo 948586 4820471 := bstep (se 1 (by rfl) ⟨3615353, by rfl⟩ : syracuseStep 4820471 = 7230707) B7230707
theorem B12162149 : Blo 948586 12162149 := bstep (se 4 (by rfl) ⟨1140201, by rfl⟩ : syracuseStep 12162149 = 2280403) B2280403
theorem B2135177 : Blo 948586 2135177 := bstep (se 2 (by rfl) ⟨800691, by rfl⟩ : syracuseStep 2135177 = 1601383) B1601383
theorem B9770149 : Blo 948586 9770149 := bstep (se 4 (by rfl) ⟨915951, by rfl⟩ : syracuseStep 9770149 = 1831903) B1831903
theorem B1808095 : Blo 948586 1808095 := bstep (se 1 (by rfl) ⟨1356071, by rfl⟩ : syracuseStep 1808095 = 2712143) B2712143
theorem B10984025 : Blo 948586 10984025 := bstep (se 2 (by rfl) ⟨4119009, by rfl⟩ : syracuseStep 10984025 = 8238019) B8238019
theorem B3709799 : Blo 948586 3709799 := bstep (se 1 (by rfl) ⟨2782349, by rfl⟩ : syracuseStep 3709799 = 5564699) B5564699
theorem B2137031 : Blo 948586 2137031 := bstep (se 1 (by rfl) ⟨1602773, by rfl⟩ : syracuseStep 2137031 = 3205547) B3205547
theorem B1351561 : Blo 948586 1351561 := bstep (se 2 (by rfl) ⟨506835, by rfl⟩ : syracuseStep 1351561 = 1013671) B1013671
theorem B1220719 : Blo 948586 1220719 := bstep (se 1 (by rfl) ⟨915539, by rfl⟩ : syracuseStep 1220719 = 1831079) B1831079
theorem B10822733 : Blo 948586 10822733 := bstep (se 3 (by rfl) ⟨2029262, by rfl⟩ : syracuseStep 10822733 = 4058525) B4058525
theorem B87893207 : Blo 948586 87893207 := bstep (se 1 (by rfl) ⟨65919905, by rfl⟩ : syracuseStep 87893207 = 131839811) B131839811
theorem B1713511 : Blo 948586 1713511 := bstep (se 1 (by rfl) ⟨1285133, by rfl⟩ : syracuseStep 1713511 = 2570267) B2570267
theorem B13706749 : Blo 948586 13706749 := bstep (se 3 (by rfl) ⟨2570015, by rfl⟩ : syracuseStep 13706749 = 5140031) B5140031
theorem B7711085 : Blo 948586 7711085 := bstep (se 3 (by rfl) ⟨1445828, by rfl⟩ : syracuseStep 7711085 = 2891657) B2891657
theorem B6859835 : Blo 948586 6859835 := bstep (se 1 (by rfl) ⟨5144876, by rfl⟩ : syracuseStep 6859835 = 10289753) B10289753
theorem B46869839 : Blo 948586 46869839 := bstep (se 1 (by rfl) ⟨35152379, by rfl⟩ : syracuseStep 46869839 = 70304759) B70304759
theorem B2141675 : Blo 948586 2141675 := bstep (se 1 (by rfl) ⟨1606256, by rfl⟩ : syracuseStep 2141675 = 3212513) B3212513
theorem B19509011 : Blo 948586 19509011 := bstep (se 1 (by rfl) ⟨14631758, by rfl⟩ : syracuseStep 19509011 = 29263517) B29263517
theorem B43955465 : Blo 948586 43955465 := bstep (se 2 (by rfl) ⟨16483299, by rfl⟩ : syracuseStep 43955465 = 32966599) B32966599
theorem B82196207 : Blo 948586 82196207 := bstep (se 1 (by rfl) ⟨61647155, by rfl⟩ : syracuseStep 82196207 = 123294311) B123294311
theorem B1424297 : Blo 948586 1424297 := bstep (se 2 (by rfl) ⟨534111, by rfl⟩ : syracuseStep 1424297 = 1068223) B1068223
theorem B1424795 : Blo 948586 1424795 := bstep (se 1 (by rfl) ⟨1068596, by rfl⟩ : syracuseStep 1424795 = 2137193) B2137193
theorem B2407927 : Blo 948586 2407927 := bstep (se 1 (by rfl) ⟨1805945, by rfl⟩ : syracuseStep 2407927 = 3611891) B3611891
theorem B18300815 : Blo 948586 18300815 := bstep (se 1 (by rfl) ⟨13725611, by rfl⟩ : syracuseStep 18300815 = 27451223) B27451223
theorem B1426991 : Blo 948586 1426991 := bstep (se 1 (by rfl) ⟨1070243, by rfl⟩ : syracuseStep 1426991 = 2140487) B2140487
theorem B4802975 : Blo 948586 4802975 := bstep (se 1 (by rfl) ⟨3602231, by rfl⟩ : syracuseStep 4802975 = 7204463) B7204463
theorem B2410985 : Blo 948586 2410985 := bstep (se 2 (by rfl) ⟨904119, by rfl⟩ : syracuseStep 2410985 = 1808239) B1808239
theorem B1428473 : Blo 948586 1428473 := bstep (se 2 (by rfl) ⟨535677, by rfl⟩ : syracuseStep 1428473 = 1071355) B1071355
theorem B3427553 : Blo 948586 3427553 := bstep (se 2 (by rfl) ⟨1285332, by rfl⟩ : syracuseStep 3427553 = 2570665) B2570665
theorem B2741215 : Blo 948586 2741215 := bstep (se 1 (by rfl) ⟨2055911, by rfl⟩ : syracuseStep 2741215 = 4111823) B4111823
theorem B13392001 : Blo 948586 13392001 := bstep (se 2 (by rfl) ⟨5022000, by rfl⟩ : syracuseStep 13392001 = 10044001) B10044001
theorem B1202359 : Blo 948586 1202359 := bstep (se 1 (by rfl) ⟨901769, by rfl⟩ : syracuseStep 1202359 = 1803539) B1803539
theorem B6839423 : Blo 948586 6839423 := bstep (se 1 (by rfl) ⟨5129567, by rfl⟩ : syracuseStep 6839423 = 10259135) B10259135
theorem B2743433 : Blo 948586 2743433 := bstep (se 2 (by rfl) ⟨1028787, by rfl⟩ : syracuseStep 2743433 = 2057575) B2057575
theorem B6250807 : Blo 948586 6250807 := bstep (se 1 (by rfl) ⟨4688105, by rfl⟩ : syracuseStep 6250807 = 9376211) B9376211
theorem B3302747 : Blo 948586 3302747 := bstep (se 1 (by rfl) ⟨2477060, by rfl⟩ : syracuseStep 3302747 = 4954121) B4954121
theorem B3204575 : Blo 948586 3204575 := bstep (se 1 (by rfl) ⟨2403431, by rfl⟩ : syracuseStep 3204575 = 4806863) B4806863
theorem B3041563 : Blo 948586 3041563 := bstep (se 1 (by rfl) ⟨2281172, by rfl⟩ : syracuseStep 3041563 = 4562345) B4562345
theorem B3041639 : Blo 948586 3041639 := bstep (se 1 (by rfl) ⟨2281229, by rfl⟩ : syracuseStep 3041639 = 4562459) B4562459
theorem B148040459 : Blo 948586 148040459 := bstep (se 1 (by rfl) ⟨111030344, by rfl⟩ : syracuseStep 148040459 = 222060689) B222060689
theorem B1601255 : Blo 948586 1601255 := bstep (se 1 (by rfl) ⟨1200941, by rfl⟩ : syracuseStep 1601255 = 2401883) B2401883
theorem B9139679 : Blo 948586 9139679 := bstep (se 1 (by rfl) ⟨6854759, by rfl⟩ : syracuseStep 9139679 = 13709519) B13709519
theorem B1603327 : Blo 948586 1603327 := bstep (se 1 (by rfl) ⟨1202495, by rfl⟩ : syracuseStep 1603327 = 2404991) B2404991
theorem B21985127 : Blo 948586 21985127 := bstep (se 1 (by rfl) ⟨16488845, by rfl⟩ : syracuseStep 21985127 = 32977691) B32977691
theorem B2030015 : Blo 948586 2030015 := bstep (se 1 (by rfl) ⟨1522511, by rfl⟩ : syracuseStep 2030015 = 3045023) B3045023
theorem B12188393 : Blo 948586 12188393 := bstep (se 2 (by rfl) ⟨4570647, by rfl⟩ : syracuseStep 12188393 = 9141295) B9141295
theorem B950015 : Blo 948586 950015 := bstep (se 1 (by rfl) ⟨712511, by rfl⟩ : syracuseStep 950015 = 1425023) B1425023
theorem B951327 : Blo 948586 951327 := bstep (se 1 (by rfl) ⟨713495, by rfl⟩ : syracuseStep 951327 = 1426991) B1426991
theorem B1607323 : Blo 948586 1607323 := bstep (se 1 (by rfl) ⟨1205492, by rfl⟩ : syracuseStep 1607323 = 2410985) B2410985
theorem B952315 : Blo 948586 952315 := bstep (se 1 (by rfl) ⟨714236, by rfl⟩ : syracuseStep 952315 = 1428473) B1428473
theorem B3213647 : Blo 948586 3213647 := bstep (se 1 (by rfl) ⟨2410235, by rfl⟩ : syracuseStep 3213647 = 4820471) B4820471
theorem B117214573 : Blo 948586 117214573 := bstep (se 3 (by rfl) ⟨21977732, by rfl⟩ : syracuseStep 117214573 = 43955465) B43955465
theorem B4559615 : Blo 948586 4559615 := bstep (se 1 (by rfl) ⟨3419711, by rfl⟩ : syracuseStep 4559615 = 6839423) B6839423
theorem B7215155 : Blo 948586 7215155 := bstep (se 1 (by rfl) ⟨5411366, by rfl⟩ : syracuseStep 7215155 = 10822733) B10822733
theorem B58595471 : Blo 948586 58595471 := bstep (se 1 (by rfl) ⟨43946603, by rfl⟩ : syracuseStep 58595471 = 87893207) B87893207
theorem B2201831 : Blo 948586 2201831 := bstep (se 1 (by rfl) ⟨1651373, by rfl⟩ : syracuseStep 2201831 = 3302747) B3302747
theorem B2136383 : Blo 948586 2136383 := bstep (se 1 (by rfl) ⟨1602287, by rfl⟩ : syracuseStep 2136383 = 3204575) B3204575
theorem B2137769 : Blo 948586 2137769 := bstep (se 2 (by rfl) ⟨801663, by rfl⟩ : syracuseStep 2137769 = 1603327) B1603327
theorem B54797471 : Blo 948586 54797471 := bstep (se 1 (by rfl) ⟨41098103, by rfl⟩ : syracuseStep 54797471 = 82196207) B82196207
theorem B14656751 : Blo 948586 14656751 := bstep (se 1 (by rfl) ⟨10992563, by rfl⟩ : syracuseStep 14656751 = 21985127) B21985127
theorem B1353343 : Blo 948586 1353343 := bstep (se 1 (by rfl) ⟨1015007, by rfl⟩ : syracuseStep 1353343 = 2030015) B2030015
theorem B12200543 : Blo 948586 12200543 := bstep (se 1 (by rfl) ⟨9150407, by rfl⟩ : syracuseStep 12200543 = 18300815) B18300815
theorem B126856115 : Blo 948586 126856115 := bstep (se 1 (by rfl) ⟨95142086, by rfl⟩ : syracuseStep 126856115 = 190284173) B190284173
theorem B8334409 : Blo 948586 8334409 := bstep (se 2 (by rfl) ⟨3125403, by rfl⟩ : syracuseStep 8334409 = 6250807) B6250807
theorem B8108099 : Blo 948586 8108099 := bstep (se 1 (by rfl) ⟨6081074, by rfl⟩ : syracuseStep 8108099 = 12162149) B12162149
theorem B1423451 : Blo 948586 1423451 := bstep (se 1 (by rfl) ⟨1067588, by rfl⟩ : syracuseStep 1423451 = 2135177) B2135177
theorem B46185545 : Blo 948586 46185545 := bstep (se 2 (by rfl) ⟨17319579, by rfl⟩ : syracuseStep 46185545 = 34639159) B34639159
theorem B2473199 : Blo 948586 2473199 := bstep (se 1 (by rfl) ⟨1854899, by rfl⟩ : syracuseStep 2473199 = 3709799) B3709799
theorem B1424687 : Blo 948586 1424687 := bstep (se 1 (by rfl) ⟨1068515, by rfl⟩ : syracuseStep 1424687 = 2137031) B2137031
theorem B20562893 : Blo 948586 20562893 := bstep (se 3 (by rfl) ⟨3855542, by rfl⟩ : syracuseStep 20562893 = 7711085) B7711085
theorem B3654953 : Blo 948586 3654953 := bstep (se 2 (by rfl) ⟨1370607, by rfl⟩ : syracuseStep 3654953 = 2741215) B2741215
theorem B13026865 : Blo 948586 13026865 := bstep (se 2 (by rfl) ⟨4885074, by rfl⟩ : syracuseStep 13026865 = 9770149) B9770149
theorem B4573223 : Blo 948586 4573223 := bstep (se 1 (by rfl) ⟨3429917, by rfl⟩ : syracuseStep 4573223 = 6859835) B6859835
theorem B31246559 : Blo 948586 31246559 := bstep (se 1 (by rfl) ⟨23434919, by rfl⟩ : syracuseStep 31246559 = 46869839) B46869839
theorem B2410793 : Blo 948586 2410793 := bstep (se 2 (by rfl) ⟨904047, by rfl⟩ : syracuseStep 2410793 = 1808095) B1808095
theorem B1427783 : Blo 948586 1427783 := bstep (se 1 (by rfl) ⟨1070837, by rfl⟩ : syracuseStep 1427783 = 2141675) B2141675
theorem B1067503 : Blo 948586 1067503 := bstep (se 1 (by rfl) ⟨800627, by rfl⟩ : syracuseStep 1067503 = 1601255) B1601255
theorem B39505421 : Blo 948586 39505421 := bstep (se 3 (by rfl) ⟨7407266, by rfl⟩ : syracuseStep 39505421 = 14814533) B14814533
theorem B1627625 : Blo 948586 1627625 := bstep (se 2 (by rfl) ⟨610359, by rfl⟩ : syracuseStep 1627625 = 1220719) B1220719
theorem B3201983 : Blo 948586 3201983 := bstep (se 1 (by rfl) ⟨2401487, by rfl⟩ : syracuseStep 3201983 = 4802975) B4802975
theorem B2284681 : Blo 948586 2284681 := bstep (se 2 (by rfl) ⟨856755, by rfl⟩ : syracuseStep 2284681 = 1713511) B1713511
theorem B18275665 : Blo 948586 18275665 := bstep (se 2 (by rfl) ⟨6853374, by rfl⟩ : syracuseStep 18275665 = 13706749) B13706749
theorem B4055417 : Blo 948586 4055417 := bstep (se 2 (by rfl) ⟨1520781, by rfl⟩ : syracuseStep 4055417 = 3041563) B3041563
theorem B4810265 : Blo 948586 4810265 := bstep (se 2 (by rfl) ⟨1803849, by rfl⟩ : syracuseStep 4810265 = 3607699) B3607699
theorem B1828955 : Blo 948586 1828955 := bstep (se 1 (by rfl) ⟨1371716, by rfl⟩ : syracuseStep 1828955 = 2743433) B2743433
theorem B29290733 : Blo 948586 29290733 := bstep (se 3 (by rfl) ⟨5492012, by rfl⟩ : syracuseStep 29290733 = 10984025) B10984025
theorem B2027759 : Blo 948586 2027759 := bstep (se 1 (by rfl) ⟨1520819, by rfl⟩ : syracuseStep 2027759 = 3041639) B3041639
theorem B98693639 : Blo 948586 98693639 := bstep (se 1 (by rfl) ⟨74020229, by rfl⟩ : syracuseStep 98693639 = 148040459) B148040459
theorem B13006007 : Blo 948586 13006007 := bstep (se 1 (by rfl) ⟨9754505, by rfl⟩ : syracuseStep 13006007 = 19509011) B19509011
theorem B17856001 : Blo 948586 17856001 := bstep (se 2 (by rfl) ⟨6696000, by rfl⟩ : syracuseStep 17856001 = 13392001) B13392001
theorem B1603145 : Blo 948586 1603145 := bstep (se 2 (by rfl) ⟨601179, by rfl⟩ : syracuseStep 1603145 = 1202359) B1202359
theorem B9140141 : Blo 948586 9140141 := bstep (se 3 (by rfl) ⟨1713776, by rfl⟩ : syracuseStep 9140141 = 3427553) B3427553
theorem B6093119 : Blo 948586 6093119 := bstep (se 1 (by rfl) ⟨4569839, by rfl⟩ : syracuseStep 6093119 = 9139679) B9139679
theorem B8125595 : Blo 948586 8125595 := bstep (se 1 (by rfl) ⟨6094196, by rfl⟩ : syracuseStep 8125595 = 12188393) B12188393
theorem B949531 : Blo 948586 949531 := bstep (se 1 (by rfl) ⟨712148, by rfl⟩ : syracuseStep 949531 = 1424297) B1424297
theorem B3210569 : Blo 948586 3210569 := bstep (se 2 (by rfl) ⟨1203963, by rfl⟩ : syracuseStep 3210569 = 2407927) B2407927
theorem B949863 : Blo 948586 949863 := bstep (se 1 (by rfl) ⟨712397, by rfl⟩ : syracuseStep 949863 = 1424795) B1424795
theorem B1802081 : Blo 948586 1802081 := bstep (se 2 (by rfl) ⟨675780, by rfl⟩ : syracuseStep 1802081 = 1351561) B1351561
theorem B5407357 : Blo 948586 5407357 := bstep (se 3 (by rfl) ⟨1013879, by rfl⟩ : syracuseStep 5407357 = 2027759) B2027759
theorem B3048815 : Blo 948586 3048815 := bstep (se 1 (by rfl) ⟨2286611, by rfl⟩ : syracuseStep 3048815 = 4573223) B4573223
theorem B1607195 : Blo 948586 1607195 := bstep (se 1 (by rfl) ⟨1205396, by rfl⟩ : syracuseStep 1607195 = 2410793) B2410793
theorem B951855 : Blo 948586 951855 := bstep (se 1 (by rfl) ⟨713891, by rfl⟩ : syracuseStep 951855 = 1427783) B1427783
theorem B17369153 : Blo 948586 17369153 := bstep (se 2 (by rfl) ⟨6513432, by rfl⟩ : syracuseStep 17369153 = 13026865) B13026865
theorem B1804457 : Blo 948586 1804457 := bstep (se 2 (by rfl) ⟨676671, by rfl⟩ : syracuseStep 1804457 = 1353343) B1353343
theorem B39063647 : Blo 948586 39063647 := bstep (se 1 (by rfl) ⟨29297735, by rfl⟩ : syracuseStep 39063647 = 58595471) B58595471
theorem B11112545 : Blo 948586 11112545 := bstep (se 2 (by rfl) ⟨4167204, by rfl⟩ : syracuseStep 11112545 = 8334409) B8334409
theorem B2134655 : Blo 948586 2134655 := bstep (se 1 (by rfl) ⟨1600991, by rfl⟩ : syracuseStep 2134655 = 3201983) B3201983
theorem B9771167 : Blo 948586 9771167 := bstep (se 1 (by rfl) ⟨7328375, by rfl⟩ : syracuseStep 9771167 = 14656751) B14656751
theorem B1219303 : Blo 948586 1219303 := bstep (se 1 (by rfl) ⟨914477, by rfl⟩ : syracuseStep 1219303 = 1828955) B1828955
theorem B8133695 : Blo 948586 8133695 := bstep (se 1 (by rfl) ⟨6100271, by rfl⟩ : syracuseStep 8133695 = 12200543) B12200543
theorem B5417063 : Blo 948586 5417063 := bstep (se 1 (by rfl) ⟨4062797, by rfl⟩ : syracuseStep 5417063 = 8125595) B8125595
theorem B1648799 : Blo 948586 1648799 := bstep (se 1 (by rfl) ⟨1236599, by rfl⟩ : syracuseStep 1648799 = 2473199) B2473199
theorem B2140379 : Blo 948586 2140379 := bstep (se 1 (by rfl) ⟨1605284, by rfl⟩ : syracuseStep 2140379 = 3210569) B3210569
theorem B13708595 : Blo 948586 13708595 := bstep (se 1 (by rfl) ⟨10281446, by rfl⟩ : syracuseStep 13708595 = 20562893) B20562893
theorem B2436635 : Blo 948586 2436635 := bstep (se 1 (by rfl) ⟨1827476, by rfl⟩ : syracuseStep 2436635 = 3654953) B3654953
theorem B2142431 : Blo 948586 2142431 := bstep (se 1 (by rfl) ⟨1606823, by rfl⟩ : syracuseStep 2142431 = 3213647) B3213647
theorem B2143097 : Blo 948586 2143097 := bstep (se 2 (by rfl) ⟨803661, by rfl⟩ : syracuseStep 2143097 = 1607323) B1607323
theorem B1423337 : Blo 948586 1423337 := bstep (se 2 (by rfl) ⟨533751, by rfl⟩ : syracuseStep 1423337 = 1067503) B1067503
theorem B4340333 : Blo 948586 4340333 := bstep (se 3 (by rfl) ⟨813812, by rfl⟩ : syracuseStep 4340333 = 1627625) B1627625
theorem B1424255 : Blo 948586 1424255 := bstep (se 1 (by rfl) ⟨1068191, by rfl⟩ : syracuseStep 1424255 = 2136383) B2136383
theorem B156286097 : Blo 948586 156286097 := bstep (se 2 (by rfl) ⟨58607286, by rfl⟩ : syracuseStep 156286097 = 117214573) B117214573
theorem B1425179 : Blo 948586 1425179 := bstep (se 1 (by rfl) ⟨1068884, by rfl⟩ : syracuseStep 1425179 = 2137769) B2137769
theorem B2703611 : Blo 948586 2703611 := bstep (se 1 (by rfl) ⟨2027708, by rfl⟩ : syracuseStep 2703611 = 4055417) B4055417
theorem B23808001 : Blo 948586 23808001 := bstep (se 2 (by rfl) ⟨8928000, by rfl⟩ : syracuseStep 23808001 = 17856001) B17856001
theorem B8670671 : Blo 948586 8670671 := bstep (se 1 (by rfl) ⟨6503003, by rfl⟩ : syracuseStep 8670671 = 13006007) B13006007
theorem B1068763 : Blo 948586 1068763 := bstep (se 1 (by rfl) ⟨801572, by rfl⟩ : syracuseStep 1068763 = 1603145) B1603145
theorem B24367553 : Blo 948586 24367553 := bstep (se 2 (by rfl) ⟨9137832, by rfl⟩ : syracuseStep 24367553 = 18275665) B18275665
theorem B30790363 : Blo 948586 30790363 := bstep (se 1 (by rfl) ⟨23092772, by rfl⟩ : syracuseStep 30790363 = 46185545) B46185545
theorem B1201387 : Blo 948586 1201387 := bstep (se 1 (by rfl) ⟨901040, by rfl⟩ : syracuseStep 1201387 = 1802081) B1802081
theorem B20831039 : Blo 948586 20831039 := bstep (se 1 (by rfl) ⟨15623279, by rfl⟩ : syracuseStep 20831039 = 31246559) B31246559
theorem B26336947 : Blo 948586 26336947 := bstep (se 1 (by rfl) ⟨19752710, by rfl⟩ : syracuseStep 26336947 = 39505421) B39505421
theorem B3039743 : Blo 948586 3039743 := bstep (se 1 (by rfl) ⟨2279807, by rfl⟩ : syracuseStep 3039743 = 4559615) B4559615
theorem B4810103 : Blo 948586 4810103 := bstep (se 1 (by rfl) ⟨3607577, by rfl⟩ : syracuseStep 4810103 = 7215155) B7215155
theorem B1467887 : Blo 948586 1467887 := bstep (se 1 (by rfl) ⟨1100915, by rfl⟩ : syracuseStep 1467887 = 2201831) B2201831
theorem B36531647 : Blo 948586 36531647 := bstep (se 1 (by rfl) ⟨27398735, by rfl⟩ : syracuseStep 36531647 = 54797471) B54797471
theorem B3206843 : Blo 948586 3206843 := bstep (se 1 (by rfl) ⟨2405132, by rfl⟩ : syracuseStep 3206843 = 4810265) B4810265
theorem B84570743 : Blo 948586 84570743 := bstep (se 1 (by rfl) ⟨63428057, by rfl⟩ : syracuseStep 84570743 = 126856115) B126856115
theorem B19527155 : Blo 948586 19527155 := bstep (se 1 (by rfl) ⟨14645366, by rfl⟩ : syracuseStep 19527155 = 29290733) B29290733
theorem B65795759 : Blo 948586 65795759 := bstep (se 1 (by rfl) ⟨49346819, by rfl⟩ : syracuseStep 65795759 = 98693639) B98693639
theorem B6093427 : Blo 948586 6093427 := bstep (se 1 (by rfl) ⟨4570070, by rfl⟩ : syracuseStep 6093427 = 9140141) B9140141
theorem B5405399 : Blo 948586 5405399 := bstep (se 1 (by rfl) ⟨4054049, by rfl⟩ : syracuseStep 5405399 = 8108099) B8108099
theorem B948967 : Blo 948586 948967 := bstep (se 1 (by rfl) ⟨711725, by rfl⟩ : syracuseStep 948967 = 1423451) B1423451
theorem B3046241 : Blo 948586 3046241 := bstep (se 2 (by rfl) ⟨1142340, by rfl⟩ : syracuseStep 3046241 = 2284681) B2284681
theorem B4062079 : Blo 948586 4062079 := bstep (se 1 (by rfl) ⟨3046559, by rfl⟩ : syracuseStep 4062079 = 6093119) B6093119
theorem B949791 : Blo 948586 949791 := bstep (se 1 (by rfl) ⟨712343, by rfl⟩ : syracuseStep 949791 = 1424687) B1424687
theorem B1802407 : Blo 948586 1802407 := bstep (se 1 (by rfl) ⟨1351805, by rfl⟩ : syracuseStep 1802407 = 2703611) B2703611
theorem B7209809 : Blo 948586 7209809 := bstep (se 2 (by rfl) ⟨2703678, by rfl⟩ : syracuseStep 7209809 = 5407357) B5407357
theorem B2032543 : Blo 948586 2032543 := bstep (se 1 (by rfl) ⟨1524407, by rfl⟩ : syracuseStep 2032543 = 3048815) B3048815
theorem B7408363 : Blo 948586 7408363 := bstep (se 1 (by rfl) ⟨5556272, by rfl⟩ : syracuseStep 7408363 = 11112545) B11112545
theorem B3611375 : Blo 948586 3611375 := bstep (se 1 (by rfl) ⟨2708531, by rfl⟩ : syracuseStep 3611375 = 5417063) B5417063
theorem B24354431 : Blo 948586 24354431 := bstep (se 1 (by rfl) ⟨18265823, by rfl⟩ : syracuseStep 24354431 = 36531647) B36531647
theorem B2137895 : Blo 948586 2137895 := bstep (se 1 (by rfl) ⟨1603421, by rfl⟩ : syracuseStep 2137895 = 3206843) B3206843
theorem B13018103 : Blo 948586 13018103 := bstep (se 1 (by rfl) ⟨9763577, by rfl⟩ : syracuseStep 13018103 = 19527155) B19527155
theorem B5416105 : Blo 948586 5416105 := bstep (se 2 (by rfl) ⟨2031039, by rfl⟩ : syracuseStep 5416105 = 4062079) B4062079
theorem B2893555 : Blo 948586 2893555 := bstep (se 1 (by rfl) ⟨2170166, by rfl⟩ : syracuseStep 2893555 = 4340333) B4340333
theorem B11579435 : Blo 948586 11579435 := bstep (se 1 (by rfl) ⟨8684576, by rfl⟩ : syracuseStep 11579435 = 17369153) B17369153
theorem B5780447 : Blo 948586 5780447 := bstep (se 1 (by rfl) ⟨4335335, by rfl⟩ : syracuseStep 5780447 = 8670671) B8670671
theorem B1423103 : Blo 948586 1423103 := bstep (se 1 (by rfl) ⟨1067327, by rfl⟩ : syracuseStep 1423103 = 2134655) B2134655
theorem B3914365 : Blo 948586 3914365 := bstep (se 3 (by rfl) ⟨733943, by rfl⟩ : syracuseStep 3914365 = 1467887) B1467887
theorem B5422463 : Blo 948586 5422463 := bstep (se 1 (by rfl) ⟨4066847, by rfl⟩ : syracuseStep 5422463 = 8133695) B8133695
theorem B1425017 : Blo 948586 1425017 := bstep (se 2 (by rfl) ⟨534381, by rfl⟩ : syracuseStep 1425017 = 1068763) B1068763
theorem B1099199 : Blo 948586 1099199 := bstep (se 1 (by rfl) ⟨824399, by rfl⟩ : syracuseStep 1099199 = 1648799) B1648799
theorem B1426919 : Blo 948586 1426919 := bstep (se 1 (by rfl) ⟨1070189, by rfl⟩ : syracuseStep 1426919 = 2140379) B2140379
theorem B1624423 : Blo 948586 1624423 := bstep (se 1 (by rfl) ⟨1218317, by rfl⟩ : syracuseStep 1624423 = 2436635) B2436635
theorem B1428287 : Blo 948586 1428287 := bstep (se 1 (by rfl) ⟨1071215, by rfl⟩ : syracuseStep 1428287 = 2142431) B2142431
theorem B56380495 : Blo 948586 56380495 := bstep (se 1 (by rfl) ⟨42285371, by rfl⟩ : syracuseStep 56380495 = 84570743) B84570743
theorem B1428731 : Blo 948586 1428731 := bstep (se 1 (by rfl) ⟨1071548, by rfl⟩ : syracuseStep 1428731 = 2143097) B2143097
theorem B1625737 : Blo 948586 1625737 := bstep (se 2 (by rfl) ⟨609651, by rfl⟩ : syracuseStep 1625737 = 1219303) B1219303
theorem B43863839 : Blo 948586 43863839 := bstep (se 1 (by rfl) ⟨32897879, by rfl⟩ : syracuseStep 43863839 = 65795759) B65795759
theorem B104190731 : Blo 948586 104190731 := bstep (se 1 (by rfl) ⟨78143048, by rfl⟩ : syracuseStep 104190731 = 156286097) B156286097
theorem B35115929 : Blo 948586 35115929 := bstep (se 2 (by rfl) ⟨13168473, by rfl⟩ : syracuseStep 35115929 = 26336947) B26336947
theorem B1071463 : Blo 948586 1071463 := bstep (se 1 (by rfl) ⟨803597, by rfl⟩ : syracuseStep 1071463 = 1607195) B1607195
theorem B31744001 : Blo 948586 31744001 := bstep (se 2 (by rfl) ⟨11904000, by rfl⟩ : syracuseStep 31744001 = 23808001) B23808001
theorem B26042431 : Blo 948586 26042431 := bstep (se 1 (by rfl) ⟨19531823, by rfl⟩ : syracuseStep 26042431 = 39063647) B39063647
theorem B16245035 : Blo 948586 16245035 := bstep (se 1 (by rfl) ⟨12183776, by rfl⟩ : syracuseStep 16245035 = 24367553) B24367553
theorem B6514111 : Blo 948586 6514111 := bstep (se 1 (by rfl) ⟨4885583, by rfl⟩ : syracuseStep 6514111 = 9771167) B9771167
theorem B13887359 : Blo 948586 13887359 := bstep (se 1 (by rfl) ⟨10415519, by rfl⟩ : syracuseStep 13887359 = 20831039) B20831039
theorem B2026495 : Blo 948586 2026495 := bstep (se 1 (by rfl) ⟨1519871, by rfl⟩ : syracuseStep 2026495 = 3039743) B3039743
theorem B4811885 : Blo 948586 4811885 := bstep (se 3 (by rfl) ⟨902228, by rfl⟩ : syracuseStep 4811885 = 1804457) B1804457
theorem B3206735 : Blo 948586 3206735 := bstep (se 1 (by rfl) ⟨2405051, by rfl⟩ : syracuseStep 3206735 = 4810103) B4810103
theorem B41053817 : Blo 948586 41053817 := bstep (se 2 (by rfl) ⟨15395181, by rfl⟩ : syracuseStep 41053817 = 30790363) B30790363
theorem B1601849 : Blo 948586 1601849 := bstep (se 2 (by rfl) ⟨600693, by rfl⟩ : syracuseStep 1601849 = 1201387) B1201387
theorem B9139063 : Blo 948586 9139063 := bstep (se 1 (by rfl) ⟨6854297, by rfl⟩ : syracuseStep 9139063 = 13708595) B13708595
theorem B8124569 : Blo 948586 8124569 := bstep (se 2 (by rfl) ⟨3046713, by rfl⟩ : syracuseStep 8124569 = 6093427) B6093427
theorem B948891 : Blo 948586 948891 := bstep (se 1 (by rfl) ⟨711668, by rfl⟩ : syracuseStep 948891 = 1423337) B1423337
theorem B3603599 : Blo 948586 3603599 := bstep (se 1 (by rfl) ⟨2702699, by rfl⟩ : syracuseStep 3603599 = 5405399) B5405399
theorem B2030827 : Blo 948586 2030827 := bstep (se 1 (by rfl) ⟨1523120, by rfl⟩ : syracuseStep 2030827 = 3046241) B3046241
theorem B949503 : Blo 948586 949503 := bstep (se 1 (by rfl) ⟨712127, by rfl⟩ : syracuseStep 949503 = 1424255) B1424255
theorem B950119 : Blo 948586 950119 := bstep (se 1 (by rfl) ⟨712589, by rfl⟩ : syracuseStep 950119 = 1425179) B1425179
theorem B951279 : Blo 948586 951279 := bstep (se 1 (by rfl) ⟨713459, by rfl⟩ : syracuseStep 951279 = 1426919) B1426919
theorem B952191 : Blo 948586 952191 := bstep (se 1 (by rfl) ⟨714143, by rfl⟩ : syracuseStep 952191 = 1428287) B1428287
theorem B8685481 : Blo 948586 8685481 := bstep (se 2 (by rfl) ⟨3257055, by rfl⟩ : syracuseStep 8685481 = 6514111) B6514111
theorem B952487 : Blo 948586 952487 := bstep (se 1 (by rfl) ⟨714365, by rfl⟩ : syracuseStep 952487 = 1428731) B1428731
theorem B2165897 : Blo 948586 2165897 := bstep (se 2 (by rfl) ⟨812211, by rfl⟩ : syracuseStep 2165897 = 1624423) B1624423
theorem B75173993 : Blo 948586 75173993 := bstep (se 2 (by rfl) ⟨28190247, by rfl⟩ : syracuseStep 75173993 = 56380495) B56380495
theorem B2167649 : Blo 948586 2167649 := bstep (se 2 (by rfl) ⟨812868, by rfl⟩ : syracuseStep 2167649 = 1625737) B1625737
theorem B2137823 : Blo 948586 2137823 := bstep (se 1 (by rfl) ⟨1603367, by rfl⟩ : syracuseStep 2137823 = 3206735) B3206735
theorem B27369211 : Blo 948586 27369211 := bstep (se 1 (by rfl) ⟨20526908, by rfl⟩ : syracuseStep 27369211 = 41053817) B41053817
theorem B5219153 : Blo 948586 5219153 := bstep (se 2 (by rfl) ⟨1957182, by rfl⟩ : syracuseStep 5219153 = 3914365) B3914365
theorem B5416379 : Blo 948586 5416379 := bstep (se 1 (by rfl) ⟨4062284, by rfl⟩ : syracuseStep 5416379 = 8124569) B8124569
theorem B2402399 : Blo 948586 2402399 := bstep (se 1 (by rfl) ⟨1801799, by rfl⟩ : syracuseStep 2402399 = 3603599) B3603599
theorem B3614975 : Blo 948586 3614975 := bstep (se 1 (by rfl) ⟨2711231, by rfl⟩ : syracuseStep 3614975 = 5422463) B5422463
theorem B2403209 : Blo 948586 2403209 := bstep (se 2 (by rfl) ⟨901203, by rfl⟩ : syracuseStep 2403209 = 1802407) B1802407
theorem B7221473 : Blo 948586 7221473 := bstep (se 2 (by rfl) ⟨2708052, by rfl⟩ : syracuseStep 7221473 = 5416105) B5416105
theorem B29242559 : Blo 948586 29242559 := bstep (se 1 (by rfl) ⟨21931919, by rfl⟩ : syracuseStep 29242559 = 43863839) B43863839
theorem B23410619 : Blo 948586 23410619 := bstep (se 1 (by rfl) ⟨17557964, by rfl⟩ : syracuseStep 23410619 = 35115929) B35115929
theorem B9877817 : Blo 948586 9877817 := bstep (se 2 (by rfl) ⟨3704181, by rfl⟩ : syracuseStep 9877817 = 7408363) B7408363
theorem B2931197 : Blo 948586 2931197 := bstep (se 3 (by rfl) ⟨549599, by rfl⟩ : syracuseStep 2931197 = 1099199) B1099199
theorem B2701993 : Blo 948586 2701993 := bstep (se 2 (by rfl) ⟨1013247, by rfl⟩ : syracuseStep 2701993 = 2026495) B2026495
theorem B2407583 : Blo 948586 2407583 := bstep (se 1 (by rfl) ⟨1805687, by rfl⟩ : syracuseStep 2407583 = 3611375) B3611375
theorem B16236287 : Blo 948586 16236287 := bstep (se 1 (by rfl) ⟨12177215, by rfl⟩ : syracuseStep 16236287 = 24354431) B24354431
theorem B1425263 : Blo 948586 1425263 := bstep (se 1 (by rfl) ⟨1068947, by rfl⟩ : syracuseStep 1425263 = 2137895) B2137895
theorem B10830023 : Blo 948586 10830023 := bstep (se 1 (by rfl) ⟨8122517, by rfl⟩ : syracuseStep 10830023 = 16245035) B16245035
theorem B9258239 : Blo 948586 9258239 := bstep (se 1 (by rfl) ⟨6943679, by rfl⟩ : syracuseStep 9258239 = 13887359) B13887359
theorem B7719623 : Blo 948586 7719623 := bstep (se 1 (by rfl) ⟨5789717, by rfl⟩ : syracuseStep 7719623 = 11579435) B11579435
theorem B1067899 : Blo 948586 1067899 := bstep (se 1 (by rfl) ⟨800924, by rfl⟩ : syracuseStep 1067899 = 1601849) B1601849
theorem B1428617 : Blo 948586 1428617 := bstep (se 2 (by rfl) ⟨535731, by rfl⟩ : syracuseStep 1428617 = 1071463) B1071463
theorem B3853631 : Blo 948586 3853631 := bstep (se 1 (by rfl) ⟨2890223, by rfl⟩ : syracuseStep 3853631 = 5780447) B5780447
theorem B2707769 : Blo 948586 2707769 := bstep (se 2 (by rfl) ⟨1015413, by rfl⟩ : syracuseStep 2707769 = 2030827) B2030827
theorem B34723241 : Blo 948586 34723241 := bstep (se 2 (by rfl) ⟨13021215, by rfl⟩ : syracuseStep 34723241 = 26042431) B26042431
theorem B4806539 : Blo 948586 4806539 := bstep (se 1 (by rfl) ⟨3604904, by rfl⟩ : syracuseStep 4806539 = 7209809) B7209809
theorem B3858073 : Blo 948586 3858073 := bstep (se 2 (by rfl) ⟨1446777, by rfl⟩ : syracuseStep 3858073 = 2893555) B2893555
theorem B69460487 : Blo 948586 69460487 := bstep (se 1 (by rfl) ⟨52095365, by rfl⟩ : syracuseStep 69460487 = 104190731) B104190731
theorem B10840229 : Blo 948586 10840229 := bstep (se 4 (by rfl) ⟨1016271, by rfl⟩ : syracuseStep 10840229 = 2032543) B2032543
theorem B21162667 : Blo 948586 21162667 := bstep (se 1 (by rfl) ⟨15872000, by rfl⟩ : syracuseStep 21162667 = 31744001) B31744001
theorem B8678735 : Blo 948586 8678735 := bstep (se 1 (by rfl) ⟨6509051, by rfl⟩ : syracuseStep 8678735 = 13018103) B13018103
theorem B12185417 : Blo 948586 12185417 := bstep (se 2 (by rfl) ⟨4569531, by rfl⟩ : syracuseStep 12185417 = 9139063) B9139063
theorem B3207923 : Blo 948586 3207923 := bstep (se 1 (by rfl) ⟨2405942, by rfl⟩ : syracuseStep 3207923 = 4811885) B4811885
theorem B948735 : Blo 948586 948735 := bstep (se 1 (by rfl) ⟨711551, by rfl⟩ : syracuseStep 948735 = 1423103) B1423103
theorem B950011 : Blo 948586 950011 := bstep (se 1 (by rfl) ⟨712508, by rfl⟩ : syracuseStep 950011 = 1425017) B1425017
theorem B5146415 : Blo 948586 5146415 := bstep (se 1 (by rfl) ⟨3859811, by rfl⟩ : syracuseStep 5146415 = 7719623) B7719623
theorem B952411 : Blo 948586 952411 := bstep (se 1 (by rfl) ⟨714308, by rfl⟩ : syracuseStep 952411 = 1428617) B1428617
theorem B1805179 : Blo 948586 1805179 := bstep (se 1 (by rfl) ⟨1353884, by rfl⟩ : syracuseStep 1805179 = 2707769) B2707769
theorem B1445099 : Blo 948586 1445099 := bstep (se 1 (by rfl) ⟨1083824, by rfl⟩ : syracuseStep 1445099 = 2167649) B2167649
theorem B28216889 : Blo 948586 28216889 := bstep (se 2 (by rfl) ⟨10581333, by rfl⟩ : syracuseStep 28216889 = 21162667) B21162667
theorem B31266101 : Blo 948586 31266101 := bstep (se 5 (by rfl) ⟨1465598, by rfl⟩ : syracuseStep 31266101 = 2931197) B2931197
theorem B46306991 : Blo 948586 46306991 := bstep (se 1 (by rfl) ⟨34730243, by rfl⟩ : syracuseStep 46306991 = 69460487) B69460487
theorem B3479435 : Blo 948586 3479435 := bstep (se 1 (by rfl) ⟨2609576, by rfl⟩ : syracuseStep 3479435 = 5219153) B5219153
theorem B3610919 : Blo 948586 3610919 := bstep (se 1 (by rfl) ⟨2708189, by rfl⟩ : syracuseStep 3610919 = 5416379) B5416379
theorem B5775725 : Blo 948586 5775725 := bstep (se 3 (by rfl) ⟨1082948, by rfl⟩ : syracuseStep 5775725 = 2165897) B2165897
theorem B2138615 : Blo 948586 2138615 := bstep (se 1 (by rfl) ⟨1603961, by rfl⟩ : syracuseStep 2138615 = 3207923) B3207923
theorem B15607079 : Blo 948586 15607079 := bstep (se 1 (by rfl) ⟨11705309, by rfl⟩ : syracuseStep 15607079 = 23410619) B23410619
theorem B10824191 : Blo 948586 10824191 := bstep (se 1 (by rfl) ⟨8118143, by rfl⟩ : syracuseStep 10824191 = 16236287) B16236287
theorem B7220015 : Blo 948586 7220015 := bstep (se 1 (by rfl) ⟨5415011, by rfl⟩ : syracuseStep 7220015 = 10830023) B10830023
theorem B6172159 : Blo 948586 6172159 := bstep (se 1 (by rfl) ⟨4629119, by rfl⟩ : syracuseStep 6172159 = 9258239) B9258239
theorem B2569087 : Blo 948586 2569087 := bstep (se 1 (by rfl) ⟨1926815, by rfl⟩ : syracuseStep 2569087 = 3853631) B3853631
theorem B11580641 : Blo 948586 11580641 := bstep (se 2 (by rfl) ⟨4342740, by rfl⟩ : syracuseStep 11580641 = 8685481) B8685481
theorem B50115995 : Blo 948586 50115995 := bstep (se 1 (by rfl) ⟨37586996, by rfl⟩ : syracuseStep 50115995 = 75173993) B75173993
theorem B23148827 : Blo 948586 23148827 := bstep (se 1 (by rfl) ⟨17361620, by rfl⟩ : syracuseStep 23148827 = 34723241) B34723241
theorem B1423865 : Blo 948586 1423865 := bstep (se 2 (by rfl) ⟨533949, by rfl⟩ : syracuseStep 1423865 = 1067899) B1067899
theorem B1425215 : Blo 948586 1425215 := bstep (se 1 (by rfl) ⟨1068911, by rfl⟩ : syracuseStep 1425215 = 2137823) B2137823
theorem B7226819 : Blo 948586 7226819 := bstep (se 1 (by rfl) ⟨5420114, by rfl⟩ : syracuseStep 7226819 = 10840229) B10840229
theorem B2409983 : Blo 948586 2409983 := bstep (se 1 (by rfl) ⟨1807487, by rfl⟩ : syracuseStep 2409983 = 3614975) B3614975
theorem B5785823 : Blo 948586 5785823 := bstep (se 1 (by rfl) ⟨4339367, by rfl⟩ : syracuseStep 5785823 = 8678735) B8678735
theorem B36492281 : Blo 948586 36492281 := bstep (se 2 (by rfl) ⟨13684605, by rfl⟩ : syracuseStep 36492281 = 27369211) B27369211
theorem B3204359 : Blo 948586 3204359 := bstep (se 1 (by rfl) ⟨2403269, by rfl⟩ : syracuseStep 3204359 = 4806539) B4806539
theorem B1601599 : Blo 948586 1601599 := bstep (se 1 (by rfl) ⟨1201199, by rfl⟩ : syracuseStep 1601599 = 2402399) B2402399
theorem B1602139 : Blo 948586 1602139 := bstep (se 1 (by rfl) ⟨1201604, by rfl⟩ : syracuseStep 1602139 = 2403209) B2403209
theorem B8123611 : Blo 948586 8123611 := bstep (se 1 (by rfl) ⟨6092708, by rfl⟩ : syracuseStep 8123611 = 12185417) B12185417
theorem B4814315 : Blo 948586 4814315 := bstep (se 1 (by rfl) ⟨3610736, by rfl⟩ : syracuseStep 4814315 = 7221473) B7221473
theorem B19495039 : Blo 948586 19495039 := bstep (se 1 (by rfl) ⟨14621279, by rfl⟩ : syracuseStep 19495039 = 29242559) B29242559
theorem B20576389 : Blo 948586 20576389 := bstep (se 4 (by rfl) ⟨1929036, by rfl⟩ : syracuseStep 20576389 = 3858073) B3858073
theorem B3602657 : Blo 948586 3602657 := bstep (se 2 (by rfl) ⟨1350996, by rfl⟩ : syracuseStep 3602657 = 2701993) B2701993
theorem B6585211 : Blo 948586 6585211 := bstep (se 1 (by rfl) ⟨4938908, by rfl⟩ : syracuseStep 6585211 = 9877817) B9877817
theorem B1605055 : Blo 948586 1605055 := bstep (se 1 (by rfl) ⟨1203791, by rfl⟩ : syracuseStep 1605055 = 2407583) B2407583
theorem B950175 : Blo 948586 950175 := bstep (se 1 (by rfl) ⟨712631, by rfl⟩ : syracuseStep 950175 = 1425263) B1425263
theorem B15401933 : Blo 948586 15401933 := bstep (se 3 (by rfl) ⟨2887862, by rfl⟩ : syracuseStep 15401933 = 5775725) B5775725
theorem B4817879 : Blo 948586 4817879 := bstep (se 1 (by rfl) ⟨3613409, by rfl⟩ : syracuseStep 4817879 = 7226819) B7226819
theorem B1606655 : Blo 948586 1606655 := bstep (se 1 (by rfl) ⟨1204991, by rfl⟩ : syracuseStep 1606655 = 2409983) B2409983
theorem B18811259 : Blo 948586 18811259 := bstep (se 1 (by rfl) ⟨14108444, by rfl⟩ : syracuseStep 18811259 = 28216889) B28216889
theorem B20844067 : Blo 948586 20844067 := bstep (se 1 (by rfl) ⟨15633050, by rfl⟩ : syracuseStep 20844067 = 31266101) B31266101
theorem B30871327 : Blo 948586 30871327 := bstep (se 1 (by rfl) ⟨23153495, by rfl⟩ : syracuseStep 30871327 = 46306991) B46306991
theorem B13701797 : Blo 948586 13701797 := bstep (se 4 (by rfl) ⟨1284543, by rfl⟩ : syracuseStep 13701797 = 2569087) B2569087
theorem B8229545 : Blo 948586 8229545 := bstep (se 2 (by rfl) ⟨3086079, by rfl⟩ : syracuseStep 8229545 = 6172159) B6172159
theorem B2135465 : Blo 948586 2135465 := bstep (se 2 (by rfl) ⟨800799, by rfl⟩ : syracuseStep 2135465 = 1601599) B1601599
theorem B2136185 : Blo 948586 2136185 := bstep (se 2 (by rfl) ⟨801069, by rfl⟩ : syracuseStep 2136185 = 1602139) B1602139
theorem B2136239 : Blo 948586 2136239 := bstep (se 1 (by rfl) ⟨1602179, by rfl⟩ : syracuseStep 2136239 = 3204359) B3204359
theorem B7216127 : Blo 948586 7216127 := bstep (se 1 (by rfl) ⟨5412095, by rfl⟩ : syracuseStep 7216127 = 10824191) B10824191
theorem B25993385 : Blo 948586 25993385 := bstep (se 2 (by rfl) ⟨9747519, by rfl⟩ : syracuseStep 25993385 = 19495039) B19495039
theorem B27435185 : Blo 948586 27435185 := bstep (se 2 (by rfl) ⟨10288194, by rfl⟩ : syracuseStep 27435185 = 20576389) B20576389
theorem B2401771 : Blo 948586 2401771 := bstep (se 1 (by rfl) ⟨1801328, by rfl⟩ : syracuseStep 2401771 = 3602657) B3602657
theorem B2140073 : Blo 948586 2140073 := bstep (se 2 (by rfl) ⟨802527, by rfl⟩ : syracuseStep 2140073 = 1605055) B1605055
theorem B24328187 : Blo 948586 24328187 := bstep (se 1 (by rfl) ⟨18246140, by rfl⟩ : syracuseStep 24328187 = 36492281) B36492281
theorem B2406905 : Blo 948586 2406905 := bstep (se 2 (by rfl) ⟨902589, by rfl⟩ : syracuseStep 2406905 = 1805179) B1805179
theorem B2407279 : Blo 948586 2407279 := bstep (se 1 (by rfl) ⟨1805459, by rfl⟩ : syracuseStep 2407279 = 3610919) B3610919
theorem B1425743 : Blo 948586 1425743 := bstep (se 1 (by rfl) ⟨1069307, by rfl⟩ : syracuseStep 1425743 = 2138615) B2138615
theorem B10404719 : Blo 948586 10404719 := bstep (se 1 (by rfl) ⟨7803539, by rfl⟩ : syracuseStep 10404719 = 15607079) B15607079
theorem B10831481 : Blo 948586 10831481 := bstep (se 2 (by rfl) ⟨4061805, by rfl⟩ : syracuseStep 10831481 = 8123611) B8123611
theorem B3853597 : Blo 948586 3853597 := bstep (se 3 (by rfl) ⟨722549, by rfl⟩ : syracuseStep 3853597 = 1445099) B1445099
theorem B7720427 : Blo 948586 7720427 := bstep (se 1 (by rfl) ⟨5790320, by rfl⟩ : syracuseStep 7720427 = 11580641) B11580641
theorem B33410663 : Blo 948586 33410663 := bstep (se 1 (by rfl) ⟨25057997, by rfl⟩ : syracuseStep 33410663 = 50115995) B50115995
theorem B3430943 : Blo 948586 3430943 := bstep (se 1 (by rfl) ⟨2573207, by rfl⟩ : syracuseStep 3430943 = 5146415) B5146415
theorem B3857215 : Blo 948586 3857215 := bstep (se 1 (by rfl) ⟨2892911, by rfl⟩ : syracuseStep 3857215 = 5785823) B5785823
theorem B2319623 : Blo 948586 2319623 := bstep (se 1 (by rfl) ⟨1739717, by rfl⟩ : syracuseStep 2319623 = 3479435) B3479435
theorem B4813343 : Blo 948586 4813343 := bstep (se 1 (by rfl) ⟨3610007, by rfl⟩ : syracuseStep 4813343 = 7220015) B7220015
theorem B3209543 : Blo 948586 3209543 := bstep (se 1 (by rfl) ⟨2407157, by rfl⟩ : syracuseStep 3209543 = 4814315) B4814315
theorem B8780281 : Blo 948586 8780281 := bstep (se 2 (by rfl) ⟨3292605, by rfl⟩ : syracuseStep 8780281 = 6585211) B6585211
theorem B15432551 : Blo 948586 15432551 := bstep (se 1 (by rfl) ⟨11574413, by rfl⟩ : syracuseStep 15432551 = 23148827) B23148827
theorem B949243 : Blo 948586 949243 := bstep (se 1 (by rfl) ⟨711932, by rfl⟩ : syracuseStep 949243 = 1423865) B1423865
theorem B950143 : Blo 948586 950143 := bstep (se 1 (by rfl) ⟨712607, by rfl⟩ : syracuseStep 950143 = 1425215) B1425215
theorem B950495 : Blo 948586 950495 := bstep (se 1 (by rfl) ⟨712871, by rfl⟩ : syracuseStep 950495 = 1425743) B1425743
theorem B3211919 : Blo 948586 3211919 := bstep (se 1 (by rfl) ⟨2408939, by rfl⟩ : syracuseStep 3211919 = 4817879) B4817879
theorem B5146951 : Blo 948586 5146951 := bstep (se 1 (by rfl) ⟨3860213, by rfl⟩ : syracuseStep 5146951 = 7720427) B7720427
theorem B46828165 : Blo 948586 46828165 := bstep (se 4 (by rfl) ⟨4390140, by rfl⟩ : syracuseStep 46828165 = 8780281) B8780281
theorem B27792089 : Blo 948586 27792089 := bstep (se 2 (by rfl) ⟨10422033, by rfl⟩ : syracuseStep 27792089 = 20844067) B20844067
theorem B41161769 : Blo 948586 41161769 := bstep (se 2 (by rfl) ⟨15435663, by rfl⟩ : syracuseStep 41161769 = 30871327) B30871327
theorem B18290123 : Blo 948586 18290123 := bstep (se 1 (by rfl) ⟨13717592, by rfl⟩ : syracuseStep 18290123 = 27435185) B27435185
theorem B1546415 : Blo 948586 1546415 := bstep (se 1 (by rfl) ⟨1159811, by rfl⟩ : syracuseStep 1546415 = 2319623) B2319623
theorem B2139695 : Blo 948586 2139695 := bstep (se 1 (by rfl) ⟨1604771, by rfl⟩ : syracuseStep 2139695 = 3209543) B3209543
theorem B10267955 : Blo 948586 10267955 := bstep (se 1 (by rfl) ⟨7700966, by rfl⟩ : syracuseStep 10267955 = 15401933) B15401933
theorem B7220987 : Blo 948586 7220987 := bstep (se 1 (by rfl) ⟨5415740, by rfl⟩ : syracuseStep 7220987 = 10831481) B10831481
theorem B5486363 : Blo 948586 5486363 := bstep (se 1 (by rfl) ⟨4114772, by rfl⟩ : syracuseStep 5486363 = 8229545) B8229545
theorem B1423643 : Blo 948586 1423643 := bstep (se 1 (by rfl) ⟨1067732, by rfl⟩ : syracuseStep 1423643 = 2135465) B2135465
theorem B1424123 : Blo 948586 1424123 := bstep (se 1 (by rfl) ⟨1068092, by rfl⟩ : syracuseStep 1424123 = 2136185) B2136185
theorem B1424159 : Blo 948586 1424159 := bstep (se 1 (by rfl) ⟨1068119, by rfl⟩ : syracuseStep 1424159 = 2136239) B2136239
theorem B1426715 : Blo 948586 1426715 := bstep (se 1 (by rfl) ⟨1070036, by rfl⟩ : syracuseStep 1426715 = 2140073) B2140073
theorem B6936479 : Blo 948586 6936479 := bstep (se 1 (by rfl) ⟨5202359, by rfl⟩ : syracuseStep 6936479 = 10404719) B10404719
theorem B1071103 : Blo 948586 1071103 := bstep (se 1 (by rfl) ⟨803327, by rfl⟩ : syracuseStep 1071103 = 1606655) B1606655
theorem B12540839 : Blo 948586 12540839 := bstep (se 1 (by rfl) ⟨9405629, by rfl⟩ : syracuseStep 12540839 = 18811259) B18811259
theorem B3202361 : Blo 948586 3202361 := bstep (se 2 (by rfl) ⟨1200885, by rfl⟩ : syracuseStep 3202361 = 2401771) B2401771
theorem B22273775 : Blo 948586 22273775 := bstep (se 1 (by rfl) ⟨16705331, by rfl⟩ : syracuseStep 22273775 = 33410663) B33410663
theorem B9134531 : Blo 948586 9134531 := bstep (se 1 (by rfl) ⟨6850898, by rfl⟩ : syracuseStep 9134531 = 13701797) B13701797
theorem B2287295 : Blo 948586 2287295 := bstep (se 1 (by rfl) ⟨1715471, by rfl⟩ : syracuseStep 2287295 = 3430943) B3430943
theorem B5138129 : Blo 948586 5138129 := bstep (se 2 (by rfl) ⟨1926798, by rfl⟩ : syracuseStep 5138129 = 3853597) B3853597
theorem B4810751 : Blo 948586 4810751 := bstep (se 1 (by rfl) ⟨3608063, by rfl⟩ : syracuseStep 4810751 = 7216127) B7216127
theorem B17328923 : Blo 948586 17328923 := bstep (se 1 (by rfl) ⟨12996692, by rfl⟩ : syracuseStep 17328923 = 25993385) B25993385
theorem B3208895 : Blo 948586 3208895 := bstep (se 1 (by rfl) ⟨2406671, by rfl⟩ : syracuseStep 3208895 = 4813343) B4813343
theorem B5142953 : Blo 948586 5142953 := bstep (se 2 (by rfl) ⟨1928607, by rfl⟩ : syracuseStep 5142953 = 3857215) B3857215
theorem B3209705 : Blo 948586 3209705 := bstep (se 2 (by rfl) ⟨1203639, by rfl⟩ : syracuseStep 3209705 = 2407279) B2407279
theorem B16218791 : Blo 948586 16218791 := bstep (se 1 (by rfl) ⟨12164093, by rfl⟩ : syracuseStep 16218791 = 24328187) B24328187
theorem B1604603 : Blo 948586 1604603 := bstep (se 1 (by rfl) ⟨1203452, by rfl⟩ : syracuseStep 1604603 = 2406905) B2406905
theorem B10288367 : Blo 948586 10288367 := bstep (se 1 (by rfl) ⟨7716275, by rfl⟩ : syracuseStep 10288367 = 15432551) B15432551
theorem B951143 : Blo 948586 951143 := bstep (se 1 (by rfl) ⟨713357, by rfl⟩ : syracuseStep 951143 = 1426715) B1426715
theorem B12193415 : Blo 948586 12193415 := bstep (se 1 (by rfl) ⟨9145061, by rfl⟩ : syracuseStep 12193415 = 18290123) B18290123
theorem B4624319 : Blo 948586 4624319 := bstep (se 1 (by rfl) ⟨3468239, by rfl⟩ : syracuseStep 4624319 = 6936479) B6936479
theorem B2134907 : Blo 948586 2134907 := bstep (se 1 (by rfl) ⟨1601180, by rfl⟩ : syracuseStep 2134907 = 3202361) B3202361
theorem B14849183 : Blo 948586 14849183 := bstep (se 1 (by rfl) ⟨11136887, by rfl⟩ : syracuseStep 14849183 = 22273775) B22273775
theorem B2139263 : Blo 948586 2139263 := bstep (se 1 (by rfl) ⟨1604447, by rfl⟩ : syracuseStep 2139263 = 3208895) B3208895
theorem B2139803 : Blo 948586 2139803 := bstep (se 1 (by rfl) ⟨1604852, by rfl⟩ : syracuseStep 2139803 = 3209705) B3209705
theorem B6858911 : Blo 948586 6858911 := bstep (se 1 (by rfl) ⟨5144183, by rfl⟩ : syracuseStep 6858911 = 10288367) B10288367
theorem B2141279 : Blo 948586 2141279 := bstep (se 1 (by rfl) ⟨1605959, by rfl⟩ : syracuseStep 2141279 = 3211919) B3211919
theorem B6862601 : Blo 948586 6862601 := bstep (se 2 (by rfl) ⟨2573475, by rfl⟩ : syracuseStep 6862601 = 5146951) B5146951
theorem B18528059 : Blo 948586 18528059 := bstep (se 1 (by rfl) ⟨13896044, by rfl⟩ : syracuseStep 18528059 = 27792089) B27792089
theorem B27441179 : Blo 948586 27441179 := bstep (se 1 (by rfl) ⟨20580884, by rfl⟩ : syracuseStep 27441179 = 41161769) B41161769
theorem B62437553 : Blo 948586 62437553 := bstep (se 2 (by rfl) ⟨23414082, by rfl⟩ : syracuseStep 62437553 = 46828165) B46828165
theorem B1030943 : Blo 948586 1030943 := bstep (se 1 (by rfl) ⟨773207, by rfl⟩ : syracuseStep 1030943 = 1546415) B1546415
theorem B1426463 : Blo 948586 1426463 := bstep (se 1 (by rfl) ⟨1069847, by rfl⟩ : syracuseStep 1426463 = 2139695) B2139695
theorem B13714541 : Blo 948586 13714541 := bstep (se 3 (by rfl) ⟨2571476, by rfl⟩ : syracuseStep 13714541 = 5142953) B5142953
theorem B1524863 : Blo 948586 1524863 := bstep (se 1 (by rfl) ⟨1143647, by rfl⟩ : syracuseStep 1524863 = 2287295) B2287295
theorem B3425419 : Blo 948586 3425419 := bstep (se 1 (by rfl) ⟨2569064, by rfl⟩ : syracuseStep 3425419 = 5138129) B5138129
theorem B11552615 : Blo 948586 11552615 := bstep (se 1 (by rfl) ⟨8664461, by rfl⟩ : syracuseStep 11552615 = 17328923) B17328923
theorem B33442237 : Blo 948586 33442237 := bstep (se 3 (by rfl) ⟨6270419, by rfl⟩ : syracuseStep 33442237 = 12540839) B12540839
theorem B1428137 : Blo 948586 1428137 := bstep (se 2 (by rfl) ⟨535551, by rfl⟩ : syracuseStep 1428137 = 1071103) B1071103
theorem B3657575 : Blo 948586 3657575 := bstep (se 1 (by rfl) ⟨2743181, by rfl⟩ : syracuseStep 3657575 = 5486363) B5486363
theorem B1069735 : Blo 948586 1069735 := bstep (se 1 (by rfl) ⟨802301, by rfl⟩ : syracuseStep 1069735 = 1604603) B1604603
theorem B6089687 : Blo 948586 6089687 := bstep (se 1 (by rfl) ⟨4567265, by rfl⟩ : syracuseStep 6089687 = 9134531) B9134531
theorem B3207167 : Blo 948586 3207167 := bstep (se 1 (by rfl) ⟨2405375, by rfl⟩ : syracuseStep 3207167 = 4810751) B4810751
theorem B6845303 : Blo 948586 6845303 := bstep (se 1 (by rfl) ⟨5133977, by rfl⟩ : syracuseStep 6845303 = 10267955) B10267955
theorem B4813991 : Blo 948586 4813991 := bstep (se 1 (by rfl) ⟨3610493, by rfl⟩ : syracuseStep 4813991 = 7220987) B7220987
theorem B949095 : Blo 948586 949095 := bstep (se 1 (by rfl) ⟨711821, by rfl⟩ : syracuseStep 949095 = 1423643) B1423643
theorem B10812527 : Blo 948586 10812527 := bstep (se 1 (by rfl) ⟨8109395, by rfl⟩ : syracuseStep 10812527 = 16218791) B16218791
theorem B949415 : Blo 948586 949415 := bstep (se 1 (by rfl) ⟨712061, by rfl⟩ : syracuseStep 949415 = 1424123) B1424123
theorem B949439 : Blo 948586 949439 := bstep (se 1 (by rfl) ⟨712079, by rfl⟩ : syracuseStep 949439 = 1424159) B1424159
theorem B950975 : Blo 948586 950975 := bstep (se 1 (by rfl) ⟨713231, by rfl⟩ : syracuseStep 950975 = 1426463) B1426463
theorem B9143027 : Blo 948586 9143027 := bstep (se 1 (by rfl) ⟨6857270, by rfl⟩ : syracuseStep 9143027 = 13714541) B13714541
theorem B7701743 : Blo 948586 7701743 := bstep (se 1 (by rfl) ⟨5776307, by rfl⟩ : syracuseStep 7701743 = 11552615) B11552615
theorem B952091 : Blo 948586 952091 := bstep (se 1 (by rfl) ⟨714068, by rfl⟩ : syracuseStep 952091 = 1428137) B1428137
theorem B8128943 : Blo 948586 8128943 := bstep (se 1 (by rfl) ⟨6096707, by rfl⟩ : syracuseStep 8128943 = 12193415) B12193415
theorem B3082879 : Blo 948586 3082879 := bstep (se 1 (by rfl) ⟨2312159, by rfl⟩ : syracuseStep 3082879 = 4624319) B4624319
theorem B4066301 : Blo 948586 4066301 := bstep (se 3 (by rfl) ⟨762431, by rfl⟩ : syracuseStep 4066301 = 1524863) B1524863
theorem B2138111 : Blo 948586 2138111 := bstep (se 1 (by rfl) ⟨1603583, by rfl⟩ : syracuseStep 2138111 = 3207167) B3207167
theorem B4563535 : Blo 948586 4563535 := bstep (se 1 (by rfl) ⟨3422651, by rfl⟩ : syracuseStep 4563535 = 6845303) B6845303
theorem B18294119 : Blo 948586 18294119 := bstep (se 1 (by rfl) ⟨13720589, by rfl⟩ : syracuseStep 18294119 = 27441179) B27441179
theorem B41625035 : Blo 948586 41625035 := bstep (se 1 (by rfl) ⟨31218776, by rfl⟩ : syracuseStep 41625035 = 62437553) B62437553
theorem B2438383 : Blo 948586 2438383 := bstep (se 1 (by rfl) ⟨1828787, by rfl⟩ : syracuseStep 2438383 = 3657575) B3657575
theorem B39597821 : Blo 948586 39597821 := bstep (se 3 (by rfl) ⟨7424591, by rfl⟩ : syracuseStep 39597821 = 14849183) B14849183
theorem B1423271 : Blo 948586 1423271 := bstep (se 1 (by rfl) ⟨1067453, by rfl⟩ : syracuseStep 1423271 = 2134907) B2134907
theorem B18300269 : Blo 948586 18300269 := bstep (se 3 (by rfl) ⟨3431300, by rfl⟩ : syracuseStep 18300269 = 6862601) B6862601
theorem B18268901 : Blo 948586 18268901 := bstep (se 4 (by rfl) ⟨1712709, by rfl⟩ : syracuseStep 18268901 = 3425419) B3425419
theorem B1426175 : Blo 948586 1426175 := bstep (se 1 (by rfl) ⟨1069631, by rfl⟩ : syracuseStep 1426175 = 2139263) B2139263
theorem B1426313 : Blo 948586 1426313 := bstep (se 2 (by rfl) ⟨534867, by rfl⟩ : syracuseStep 1426313 = 1069735) B1069735
theorem B1426535 : Blo 948586 1426535 := bstep (se 1 (by rfl) ⟨1069901, by rfl⟩ : syracuseStep 1426535 = 2139803) B2139803
theorem B4572607 : Blo 948586 4572607 := bstep (se 1 (by rfl) ⟨3429455, by rfl⟩ : syracuseStep 4572607 = 6858911) B6858911
theorem B1427519 : Blo 948586 1427519 := bstep (se 1 (by rfl) ⟨1070639, by rfl⟩ : syracuseStep 1427519 = 2141279) B2141279
theorem B44589649 : Blo 948586 44589649 := bstep (se 2 (by rfl) ⟨16721118, by rfl⟩ : syracuseStep 44589649 = 33442237) B33442237
theorem B49408157 : Blo 948586 49408157 := bstep (se 3 (by rfl) ⟨9264029, by rfl⟩ : syracuseStep 49408157 = 18528059) B18528059
theorem B4059791 : Blo 948586 4059791 := bstep (se 1 (by rfl) ⟨3044843, by rfl⟩ : syracuseStep 4059791 = 6089687) B6089687
theorem B2749181 : Blo 948586 2749181 := bstep (se 3 (by rfl) ⟨515471, by rfl⟩ : syracuseStep 2749181 = 1030943) B1030943
theorem B3209327 : Blo 948586 3209327 := bstep (se 1 (by rfl) ⟨2406995, by rfl⟩ : syracuseStep 3209327 = 4813991) B4813991
theorem B7208351 : Blo 948586 7208351 := bstep (se 1 (by rfl) ⟨5406263, by rfl⟩ : syracuseStep 7208351 = 10812527) B10812527
theorem B6095351 : Blo 948586 6095351 := bstep (se 1 (by rfl) ⟨4571513, by rfl⟩ : syracuseStep 6095351 = 9143027) B9143027
theorem B950783 : Blo 948586 950783 := bstep (se 1 (by rfl) ⟨713087, by rfl⟩ : syracuseStep 950783 = 1426175) B1426175
theorem B950875 : Blo 948586 950875 := bstep (se 1 (by rfl) ⟨713156, by rfl⟩ : syracuseStep 950875 = 1426313) B1426313
theorem B951023 : Blo 948586 951023 := bstep (se 1 (by rfl) ⟨713267, by rfl⟩ : syracuseStep 951023 = 1426535) B1426535
theorem B951679 : Blo 948586 951679 := bstep (se 1 (by rfl) ⟨713759, by rfl⟩ : syracuseStep 951679 = 1427519) B1427519
theorem B6096809 : Blo 948586 6096809 := bstep (se 2 (by rfl) ⟨2286303, by rfl⟩ : syracuseStep 6096809 = 4572607) B4572607
theorem B12196079 : Blo 948586 12196079 := bstep (se 1 (by rfl) ⟨9147059, by rfl⟩ : syracuseStep 12196079 = 18294119) B18294119
theorem B3251177 : Blo 948586 3251177 := bstep (se 2 (by rfl) ⟨1219191, by rfl⟩ : syracuseStep 3251177 = 2438383) B2438383
theorem B2139551 : Blo 948586 2139551 := bstep (se 1 (by rfl) ⟨1604663, by rfl⟩ : syracuseStep 2139551 = 3209327) B3209327
theorem B12200179 : Blo 948586 12200179 := bstep (se 1 (by rfl) ⟨9150134, by rfl⟩ : syracuseStep 12200179 = 18300269) B18300269
theorem B59452865 : Blo 948586 59452865 := bstep (se 2 (by rfl) ⟨22294824, by rfl⟩ : syracuseStep 59452865 = 44589649) B44589649
theorem B5419295 : Blo 948586 5419295 := bstep (se 1 (by rfl) ⟨4064471, by rfl⟩ : syracuseStep 5419295 = 8128943) B8128943
theorem B1425407 : Blo 948586 1425407 := bstep (se 1 (by rfl) ⟨1069055, by rfl⟩ : syracuseStep 1425407 = 2138111) B2138111
theorem B2706527 : Blo 948586 2706527 := bstep (se 1 (by rfl) ⟨2029895, by rfl⟩ : syracuseStep 2706527 = 4059791) B4059791
theorem B26398547 : Blo 948586 26398547 := bstep (se 1 (by rfl) ⟨19798910, by rfl⟩ : syracuseStep 26398547 = 39597821) B39597821
theorem B4805567 : Blo 948586 4805567 := bstep (se 1 (by rfl) ⟨3604175, by rfl⟩ : syracuseStep 4805567 = 7208351) B7208351
theorem B12179267 : Blo 948586 12179267 := bstep (se 1 (by rfl) ⟨9134450, by rfl⟩ : syracuseStep 12179267 = 18268901) B18268901
theorem B6084713 : Blo 948586 6084713 := bstep (se 2 (by rfl) ⟨2281767, by rfl⟩ : syracuseStep 6084713 = 4563535) B4563535
theorem B7331149 : Blo 948586 7331149 := bstep (se 3 (by rfl) ⟨1374590, by rfl⟩ : syracuseStep 7331149 = 2749181) B2749181
theorem B2710867 : Blo 948586 2710867 := bstep (se 1 (by rfl) ⟨2033150, by rfl⟩ : syracuseStep 2710867 = 4066301) B4066301
theorem B20537981 : Blo 948586 20537981 := bstep (se 3 (by rfl) ⟨3850871, by rfl⟩ : syracuseStep 20537981 = 7701743) B7701743
theorem B16442021 : Blo 948586 16442021 := bstep (se 4 (by rfl) ⟨1541439, by rfl⟩ : syracuseStep 16442021 = 3082879) B3082879
theorem B131755085 : Blo 948586 131755085 := bstep (se 3 (by rfl) ⟨24704078, by rfl⟩ : syracuseStep 131755085 = 49408157) B49408157
theorem B27750023 : Blo 948586 27750023 := bstep (se 1 (by rfl) ⟨20812517, by rfl⟩ : syracuseStep 27750023 = 41625035) B41625035
theorem B948847 : Blo 948586 948847 := bstep (se 1 (by rfl) ⟨711635, by rfl⟩ : syracuseStep 948847 = 1423271) B1423271
theorem B4063567 : Blo 948586 4063567 := bstep (se 1 (by rfl) ⟨3047675, by rfl⟩ : syracuseStep 4063567 = 6095351) B6095351
theorem B1804351 : Blo 948586 1804351 := bstep (se 1 (by rfl) ⟨1353263, by rfl⟩ : syracuseStep 1804351 = 2706527) B2706527
theorem B17599031 : Blo 948586 17599031 := bstep (se 1 (by rfl) ⟨13199273, by rfl⟩ : syracuseStep 17599031 = 26398547) B26398547
theorem B8130719 : Blo 948586 8130719 := bstep (se 1 (by rfl) ⟨6098039, by rfl⟩ : syracuseStep 8130719 = 12196079) B12196079
theorem B2167451 : Blo 948586 2167451 := bstep (se 1 (by rfl) ⟨1625588, by rfl⟩ : syracuseStep 2167451 = 3251177) B3251177
theorem B16258157 : Blo 948586 16258157 := bstep (se 3 (by rfl) ⟨3048404, by rfl⟩ : syracuseStep 16258157 = 6096809) B6096809
theorem B3612863 : Blo 948586 3612863 := bstep (se 1 (by rfl) ⟨2709647, by rfl⟩ : syracuseStep 3612863 = 5419295) B5419295
theorem B9774865 : Blo 948586 9774865 := bstep (se 2 (by rfl) ⟨3665574, by rfl⟩ : syracuseStep 9774865 = 7331149) B7331149
theorem B3614489 : Blo 948586 3614489 := bstep (se 2 (by rfl) ⟨1355433, by rfl⟩ : syracuseStep 3614489 = 2710867) B2710867
theorem B16266905 : Blo 948586 16266905 := bstep (se 2 (by rfl) ⟨6100089, by rfl⟩ : syracuseStep 16266905 = 12200179) B12200179
theorem B10961347 : Blo 948586 10961347 := bstep (se 1 (by rfl) ⟨8221010, by rfl⟩ : syracuseStep 10961347 = 16442021) B16442021
theorem B1426367 : Blo 948586 1426367 := bstep (se 1 (by rfl) ⟨1069775, by rfl⟩ : syracuseStep 1426367 = 2139551) B2139551
theorem B87836723 : Blo 948586 87836723 := bstep (se 1 (by rfl) ⟨65877542, by rfl⟩ : syracuseStep 87836723 = 131755085) B131755085
theorem B39635243 : Blo 948586 39635243 := bstep (se 1 (by rfl) ⟨29726432, by rfl⟩ : syracuseStep 39635243 = 59452865) B59452865
theorem B18500015 : Blo 948586 18500015 := bstep (se 1 (by rfl) ⟨13875011, by rfl⟩ : syracuseStep 18500015 = 27750023) B27750023
theorem B3203711 : Blo 948586 3203711 := bstep (se 1 (by rfl) ⟨2402783, by rfl⟩ : syracuseStep 3203711 = 4805567) B4805567
theorem B8119511 : Blo 948586 8119511 := bstep (se 1 (by rfl) ⟨6089633, by rfl⟩ : syracuseStep 8119511 = 12179267) B12179267
theorem B4056475 : Blo 948586 4056475 := bstep (se 1 (by rfl) ⟨3042356, by rfl⟩ : syracuseStep 4056475 = 6084713) B6084713
theorem B13691987 : Blo 948586 13691987 := bstep (se 1 (by rfl) ⟨10268990, by rfl⟩ : syracuseStep 13691987 = 20537981) B20537981
theorem B950271 : Blo 948586 950271 := bstep (se 1 (by rfl) ⟨712703, by rfl⟩ : syracuseStep 950271 = 1425407) B1425407
theorem B14615129 : Blo 948586 14615129 := bstep (se 2 (by rfl) ⟨5480673, by rfl⟩ : syracuseStep 14615129 = 10961347) B10961347
theorem B950911 : Blo 948586 950911 := bstep (se 1 (by rfl) ⟨713183, by rfl⟩ : syracuseStep 950911 = 1426367) B1426367
theorem B58557815 : Blo 948586 58557815 := bstep (se 1 (by rfl) ⟨43918361, by rfl⟩ : syracuseStep 58557815 = 87836723) B87836723
theorem B11732687 : Blo 948586 11732687 := bstep (se 1 (by rfl) ⟨8799515, by rfl⟩ : syracuseStep 11732687 = 17599031) B17599031
theorem B5408633 : Blo 948586 5408633 := bstep (se 2 (by rfl) ⟨2028237, by rfl⟩ : syracuseStep 5408633 = 4056475) B4056475
theorem B1444967 : Blo 948586 1444967 := bstep (se 1 (by rfl) ⟨1083725, by rfl⟩ : syracuseStep 1444967 = 2167451) B2167451
theorem B2135807 : Blo 948586 2135807 := bstep (se 1 (by rfl) ⟨1601855, by rfl⟩ : syracuseStep 2135807 = 3203711) B3203711
theorem B5413007 : Blo 948586 5413007 := bstep (se 1 (by rfl) ⟨4059755, by rfl⟩ : syracuseStep 5413007 = 8119511) B8119511
theorem B5418089 : Blo 948586 5418089 := bstep (se 2 (by rfl) ⟨2031783, by rfl⟩ : syracuseStep 5418089 = 4063567) B4063567
theorem B26423495 : Blo 948586 26423495 := bstep (se 1 (by rfl) ⟨19817621, by rfl⟩ : syracuseStep 26423495 = 39635243) B39635243
theorem B12333343 : Blo 948586 12333343 := bstep (se 1 (by rfl) ⟨9250007, by rfl⟩ : syracuseStep 12333343 = 18500015) B18500015
theorem B2405801 : Blo 948586 2405801 := bstep (se 2 (by rfl) ⟨902175, by rfl⟩ : syracuseStep 2405801 = 1804351) B1804351
theorem B5420479 : Blo 948586 5420479 := bstep (se 1 (by rfl) ⟨4065359, by rfl⟩ : syracuseStep 5420479 = 8130719) B8130719
theorem B2408575 : Blo 948586 2408575 := bstep (se 1 (by rfl) ⟨1806431, by rfl⟩ : syracuseStep 2408575 = 3612863) B3612863
theorem B2409659 : Blo 948586 2409659 := bstep (se 1 (by rfl) ⟨1807244, by rfl⟩ : syracuseStep 2409659 = 3614489) B3614489
theorem B9127991 : Blo 948586 9127991 := bstep (se 1 (by rfl) ⟨6845993, by rfl⟩ : syracuseStep 9127991 = 13691987) B13691987
theorem B13033153 : Blo 948586 13033153 := bstep (se 2 (by rfl) ⟨4887432, by rfl⟩ : syracuseStep 13033153 = 9774865) B9774865
theorem B10838771 : Blo 948586 10838771 := bstep (se 1 (by rfl) ⟨8129078, by rfl⟩ : syracuseStep 10838771 = 16258157) B16258157
theorem B10844603 : Blo 948586 10844603 := bstep (se 1 (by rfl) ⟨8133452, by rfl⟩ : syracuseStep 10844603 = 16266905) B16266905
theorem B3211433 : Blo 948586 3211433 := bstep (se 2 (by rfl) ⟨1204287, by rfl⟩ : syracuseStep 3211433 = 2408575) B2408575
theorem B1606439 : Blo 948586 1606439 := bstep (se 1 (by rfl) ⟨1204829, by rfl⟩ : syracuseStep 1606439 = 2409659) B2409659
theorem B3605755 : Blo 948586 3605755 := bstep (se 1 (by rfl) ⟨2704316, by rfl⟩ : syracuseStep 3605755 = 5408633) B5408633
theorem B3608671 : Blo 948586 3608671 := bstep (se 1 (by rfl) ⟨2706503, by rfl⟩ : syracuseStep 3608671 = 5413007) B5413007
theorem B3612059 : Blo 948586 3612059 := bstep (se 1 (by rfl) ⟨2709044, by rfl⟩ : syracuseStep 3612059 = 5418089) B5418089
theorem B17377537 : Blo 948586 17377537 := bstep (se 2 (by rfl) ⟨6516576, by rfl⟩ : syracuseStep 17377537 = 13033153) B13033153
theorem B9743419 : Blo 948586 9743419 := bstep (se 1 (by rfl) ⟨7307564, by rfl⟩ : syracuseStep 9743419 = 14615129) B14615129
theorem B39038543 : Blo 948586 39038543 := bstep (se 1 (by rfl) ⟨29278907, by rfl⟩ : syracuseStep 39038543 = 58557815) B58557815
theorem B963311 : Blo 948586 963311 := bstep (se 1 (by rfl) ⟨722483, by rfl⟩ : syracuseStep 963311 = 1444967) B1444967
theorem B1423871 : Blo 948586 1423871 := bstep (se 1 (by rfl) ⟨1067903, by rfl⟩ : syracuseStep 1423871 = 2135807) B2135807
theorem B7225847 : Blo 948586 7225847 := bstep (se 1 (by rfl) ⟨5419385, by rfl⟩ : syracuseStep 7225847 = 10838771) B10838771
theorem B7227305 : Blo 948586 7227305 := bstep (se 2 (by rfl) ⟨2710239, by rfl⟩ : syracuseStep 7227305 = 5420479) B5420479
theorem B17615663 : Blo 948586 17615663 := bstep (se 1 (by rfl) ⟨13211747, by rfl⟩ : syracuseStep 17615663 = 26423495) B26423495
theorem B7229735 : Blo 948586 7229735 := bstep (se 1 (by rfl) ⟨5422301, by rfl⟩ : syracuseStep 7229735 = 10844603) B10844603
theorem B7821791 : Blo 948586 7821791 := bstep (se 1 (by rfl) ⟨5866343, by rfl⟩ : syracuseStep 7821791 = 11732687) B11732687
theorem B24341309 : Blo 948586 24341309 := bstep (se 3 (by rfl) ⟨4563995, by rfl⟩ : syracuseStep 24341309 = 9127991) B9127991
theorem B16444457 : Blo 948586 16444457 := bstep (se 2 (by rfl) ⟨6166671, by rfl⟩ : syracuseStep 16444457 = 12333343) B12333343
theorem B1603867 : Blo 948586 1603867 := bstep (se 1 (by rfl) ⟨1202900, by rfl⟩ : syracuseStep 1603867 = 2405801) B2405801
theorem B4817231 : Blo 948586 4817231 := bstep (se 1 (by rfl) ⟨3612923, by rfl⟩ : syracuseStep 4817231 = 7225847) B7225847
theorem B4818203 : Blo 948586 4818203 := bstep (se 1 (by rfl) ⟨3613652, by rfl⟩ : syracuseStep 4818203 = 7227305) B7227305
theorem B4819823 : Blo 948586 4819823 := bstep (se 1 (by rfl) ⟨3614867, by rfl⟩ : syracuseStep 4819823 = 7229735) B7229735
theorem B23170049 : Blo 948586 23170049 := bstep (se 2 (by rfl) ⟨8688768, by rfl⟩ : syracuseStep 23170049 = 17377537) B17377537
theorem B5214527 : Blo 948586 5214527 := bstep (se 1 (by rfl) ⟨3910895, by rfl⟩ : syracuseStep 5214527 = 7821791) B7821791
theorem B16227539 : Blo 948586 16227539 := bstep (se 1 (by rfl) ⟨12170654, by rfl⟩ : syracuseStep 16227539 = 24341309) B24341309
theorem B26025695 : Blo 948586 26025695 := bstep (se 1 (by rfl) ⟨19519271, by rfl⟩ : syracuseStep 26025695 = 39038543) B39038543
theorem B2138489 : Blo 948586 2138489 := bstep (se 2 (by rfl) ⟨801933, by rfl⟩ : syracuseStep 2138489 = 1603867) B1603867
theorem B2140955 : Blo 948586 2140955 := bstep (se 1 (by rfl) ⟨1605716, by rfl⟩ : syracuseStep 2140955 = 3211433) B3211433
theorem B11743775 : Blo 948586 11743775 := bstep (se 1 (by rfl) ⟨8807831, by rfl⟩ : syracuseStep 11743775 = 17615663) B17615663
theorem B2568829 : Blo 948586 2568829 := bstep (se 3 (by rfl) ⟨481655, by rfl⟩ : syracuseStep 2568829 = 963311) B963311
theorem B12991225 : Blo 948586 12991225 := bstep (se 2 (by rfl) ⟨4871709, by rfl⟩ : syracuseStep 12991225 = 9743419) B9743419
theorem B2408039 : Blo 948586 2408039 := bstep (se 1 (by rfl) ⟨1806029, by rfl⟩ : syracuseStep 2408039 = 3612059) B3612059
theorem B10962971 : Blo 948586 10962971 := bstep (se 1 (by rfl) ⟨8222228, by rfl⟩ : syracuseStep 10962971 = 16444457) B16444457
theorem B1070959 : Blo 948586 1070959 := bstep (se 1 (by rfl) ⟨803219, by rfl⟩ : syracuseStep 1070959 = 1606439) B1606439
theorem B4807673 : Blo 948586 4807673 := bstep (se 2 (by rfl) ⟨1802877, by rfl⟩ : syracuseStep 4807673 = 3605755) B3605755
theorem B4811561 : Blo 948586 4811561 := bstep (se 2 (by rfl) ⟨1804335, by rfl⟩ : syracuseStep 4811561 = 3608671) B3608671
theorem B949247 : Blo 948586 949247 := bstep (se 1 (by rfl) ⟨711935, by rfl⟩ : syracuseStep 949247 = 1423871) B1423871
theorem B3211487 : Blo 948586 3211487 := bstep (se 1 (by rfl) ⟨2408615, by rfl⟩ : syracuseStep 3211487 = 4817231) B4817231
theorem B3212135 : Blo 948586 3212135 := bstep (se 1 (by rfl) ⟨2409101, by rfl⟩ : syracuseStep 3212135 = 4818203) B4818203
theorem B7308647 : Blo 948586 7308647 := bstep (se 1 (by rfl) ⟨5481485, by rfl⟩ : syracuseStep 7308647 = 10962971) B10962971
theorem B3213215 : Blo 948586 3213215 := bstep (se 1 (by rfl) ⟨2409911, by rfl⟩ : syracuseStep 3213215 = 4819823) B4819823
theorem B3476351 : Blo 948586 3476351 := bstep (se 1 (by rfl) ⟨2607263, by rfl⟩ : syracuseStep 3476351 = 5214527) B5214527
theorem B10818359 : Blo 948586 10818359 := bstep (se 1 (by rfl) ⟨8113769, by rfl⟩ : syracuseStep 10818359 = 16227539) B16227539
theorem B15446699 : Blo 948586 15446699 := bstep (se 1 (by rfl) ⟨11585024, by rfl⟩ : syracuseStep 15446699 = 23170049) B23170049
theorem B17350463 : Blo 948586 17350463 := bstep (se 1 (by rfl) ⟨13012847, by rfl⟩ : syracuseStep 17350463 = 26025695) B26025695
theorem B1425659 : Blo 948586 1425659 := bstep (se 1 (by rfl) ⟨1069244, by rfl⟩ : syracuseStep 1425659 = 2138489) B2138489
theorem B3425105 : Blo 948586 3425105 := bstep (se 2 (by rfl) ⟨1284414, by rfl⟩ : syracuseStep 3425105 = 2568829) B2568829
theorem B1427303 : Blo 948586 1427303 := bstep (se 1 (by rfl) ⟨1070477, by rfl⟩ : syracuseStep 1427303 = 2140955) B2140955
theorem B1427945 : Blo 948586 1427945 := bstep (se 2 (by rfl) ⟨535479, by rfl⟩ : syracuseStep 1427945 = 1070959) B1070959
theorem B17321633 : Blo 948586 17321633 := bstep (se 2 (by rfl) ⟨6495612, by rfl⟩ : syracuseStep 17321633 = 12991225) B12991225
theorem B3205115 : Blo 948586 3205115 := bstep (se 1 (by rfl) ⟨2403836, by rfl⟩ : syracuseStep 3205115 = 4807673) B4807673
theorem B3207707 : Blo 948586 3207707 := bstep (se 1 (by rfl) ⟨2405780, by rfl⟩ : syracuseStep 3207707 = 4811561) B4811561
theorem B7829183 : Blo 948586 7829183 := bstep (se 1 (by rfl) ⟨5871887, by rfl⟩ : syracuseStep 7829183 = 11743775) B11743775
theorem B1605359 : Blo 948586 1605359 := bstep (se 1 (by rfl) ⟨1204019, by rfl⟩ : syracuseStep 1605359 = 2408039) B2408039
theorem B950439 : Blo 948586 950439 := bstep (se 1 (by rfl) ⟨712829, by rfl⟩ : syracuseStep 950439 = 1425659) B1425659
theorem B951535 : Blo 948586 951535 := bstep (se 1 (by rfl) ⟨713651, by rfl⟩ : syracuseStep 951535 = 1427303) B1427303
theorem B951963 : Blo 948586 951963 := bstep (se 1 (by rfl) ⟨713972, by rfl⟩ : syracuseStep 951963 = 1427945) B1427945
theorem B7212239 : Blo 948586 7212239 := bstep (se 1 (by rfl) ⟨5409179, by rfl⟩ : syracuseStep 7212239 = 10818359) B10818359
theorem B20877821 : Blo 948586 20877821 := bstep (se 3 (by rfl) ⟨3914591, by rfl⟩ : syracuseStep 20877821 = 7829183) B7829183
theorem B2136743 : Blo 948586 2136743 := bstep (se 1 (by rfl) ⟨1602557, by rfl⟩ : syracuseStep 2136743 = 3205115) B3205115
theorem B2138471 : Blo 948586 2138471 := bstep (se 1 (by rfl) ⟨1603853, by rfl⟩ : syracuseStep 2138471 = 3207707) B3207707
theorem B10297799 : Blo 948586 10297799 := bstep (se 1 (by rfl) ⟨7723349, by rfl⟩ : syracuseStep 10297799 = 15446699) B15446699
theorem B2140991 : Blo 948586 2140991 := bstep (se 1 (by rfl) ⟨1605743, by rfl⟩ : syracuseStep 2140991 = 3211487) B3211487
theorem B2141423 : Blo 948586 2141423 := bstep (se 1 (by rfl) ⟨1606067, by rfl⟩ : syracuseStep 2141423 = 3212135) B3212135
theorem B2142143 : Blo 948586 2142143 := bstep (se 1 (by rfl) ⟨1606607, by rfl⟩ : syracuseStep 2142143 = 3213215) B3213215
theorem B11547755 : Blo 948586 11547755 := bstep (se 1 (by rfl) ⟨8660816, by rfl⟩ : syracuseStep 11547755 = 17321633) B17321633
theorem B1070239 : Blo 948586 1070239 := bstep (se 1 (by rfl) ⟨802679, by rfl⟩ : syracuseStep 1070239 = 1605359) B1605359
theorem B2283403 : Blo 948586 2283403 := bstep (se 1 (by rfl) ⟨1712552, by rfl⟩ : syracuseStep 2283403 = 3425105) B3425105
theorem B4872431 : Blo 948586 4872431 := bstep (se 1 (by rfl) ⟨3654323, by rfl⟩ : syracuseStep 4872431 = 7308647) B7308647
theorem B2317567 : Blo 948586 2317567 := bstep (se 1 (by rfl) ⟨1738175, by rfl⟩ : syracuseStep 2317567 = 3476351) B3476351
theorem B11566975 : Blo 948586 11566975 := bstep (se 1 (by rfl) ⟨8675231, by rfl⟩ : syracuseStep 11566975 = 17350463) B17350463
theorem B3090089 : Blo 948586 3090089 := bstep (se 2 (by rfl) ⟨1158783, by rfl⟩ : syracuseStep 3090089 = 2317567) B2317567
theorem B1424495 : Blo 948586 1424495 := bstep (se 1 (by rfl) ⟨1068371, by rfl⟩ : syracuseStep 1424495 = 2136743) B2136743
theorem B1425647 : Blo 948586 1425647 := bstep (se 1 (by rfl) ⟨1069235, by rfl⟩ : syracuseStep 1425647 = 2138471) B2138471
theorem B6865199 : Blo 948586 6865199 := bstep (se 1 (by rfl) ⟨5148899, by rfl⟩ : syracuseStep 6865199 = 10297799) B10297799
theorem B12993149 : Blo 948586 12993149 := bstep (se 3 (by rfl) ⟨2436215, by rfl⟩ : syracuseStep 12993149 = 4872431) B4872431
theorem B1426985 : Blo 948586 1426985 := bstep (se 2 (by rfl) ⟨535119, by rfl⟩ : syracuseStep 1426985 = 1070239) B1070239
theorem B1427327 : Blo 948586 1427327 := bstep (se 1 (by rfl) ⟨1070495, by rfl⟩ : syracuseStep 1427327 = 2140991) B2140991
theorem B1427615 : Blo 948586 1427615 := bstep (se 1 (by rfl) ⟨1070711, by rfl⟩ : syracuseStep 1427615 = 2141423) B2141423
theorem B1428095 : Blo 948586 1428095 := bstep (se 1 (by rfl) ⟨1071071, by rfl⟩ : syracuseStep 1428095 = 2142143) B2142143
theorem B15422633 : Blo 948586 15422633 := bstep (se 2 (by rfl) ⟨5783487, by rfl⟩ : syracuseStep 15422633 = 11566975) B11566975
theorem B4808159 : Blo 948586 4808159 := bstep (se 1 (by rfl) ⟨3606119, by rfl⟩ : syracuseStep 4808159 = 7212239) B7212239
theorem B13918547 : Blo 948586 13918547 := bstep (se 1 (by rfl) ⟨10438910, by rfl⟩ : syracuseStep 13918547 = 20877821) B20877821
theorem B3044537 : Blo 948586 3044537 := bstep (se 2 (by rfl) ⟨1141701, by rfl⟩ : syracuseStep 3044537 = 2283403) B2283403
theorem B7698503 : Blo 948586 7698503 := bstep (se 1 (by rfl) ⟨5773877, by rfl⟩ : syracuseStep 7698503 = 11547755) B11547755
theorem B950431 : Blo 948586 950431 := bstep (se 1 (by rfl) ⟨712823, by rfl⟩ : syracuseStep 950431 = 1425647) B1425647
theorem B951323 : Blo 948586 951323 := bstep (se 1 (by rfl) ⟨713492, by rfl⟩ : syracuseStep 951323 = 1426985) B1426985
theorem B951551 : Blo 948586 951551 := bstep (se 1 (by rfl) ⟨713663, by rfl⟩ : syracuseStep 951551 = 1427327) B1427327
theorem B951743 : Blo 948586 951743 := bstep (se 1 (by rfl) ⟨713807, by rfl⟩ : syracuseStep 951743 = 1427615) B1427615
theorem B952063 : Blo 948586 952063 := bstep (se 1 (by rfl) ⟨714047, by rfl⟩ : syracuseStep 952063 = 1428095) B1428095
theorem B9279031 : Blo 948586 9279031 := bstep (se 1 (by rfl) ⟨6959273, by rfl⟩ : syracuseStep 9279031 = 13918547) B13918547
theorem B8662099 : Blo 948586 8662099 := bstep (se 1 (by rfl) ⟨6496574, by rfl⟩ : syracuseStep 8662099 = 12993149) B12993149
theorem B8240237 : Blo 948586 8240237 := bstep (se 3 (by rfl) ⟨1545044, by rfl⟩ : syracuseStep 8240237 = 3090089) B3090089
theorem B5132335 : Blo 948586 5132335 := bstep (se 1 (by rfl) ⟨3849251, by rfl⟩ : syracuseStep 5132335 = 7698503) B7698503
theorem B4576799 : Blo 948586 4576799 := bstep (se 1 (by rfl) ⟨3432599, by rfl⟩ : syracuseStep 4576799 = 6865199) B6865199
theorem B10281755 : Blo 948586 10281755 := bstep (se 1 (by rfl) ⟨7711316, by rfl⟩ : syracuseStep 10281755 = 15422633) B15422633
theorem B3205439 : Blo 948586 3205439 := bstep (se 1 (by rfl) ⟨2404079, by rfl⟩ : syracuseStep 3205439 = 4808159) B4808159
theorem B2029691 : Blo 948586 2029691 := bstep (se 1 (by rfl) ⟨1522268, by rfl⟩ : syracuseStep 2029691 = 3044537) B3044537
theorem B949663 : Blo 948586 949663 := bstep (se 1 (by rfl) ⟨712247, by rfl⟩ : syracuseStep 949663 = 1424495) B1424495
theorem B3051199 : Blo 948586 3051199 := bstep (se 1 (by rfl) ⟨2288399, by rfl⟩ : syracuseStep 3051199 = 4576799) B4576799
theorem B6854503 : Blo 948586 6854503 := bstep (se 1 (by rfl) ⟨5140877, by rfl⟩ : syracuseStep 6854503 = 10281755) B10281755
theorem B2136959 : Blo 948586 2136959 := bstep (se 1 (by rfl) ⟨1602719, by rfl⟩ : syracuseStep 2136959 = 3205439) B3205439
theorem B1353127 : Blo 948586 1353127 := bstep (se 1 (by rfl) ⟨1014845, by rfl⟩ : syracuseStep 1353127 = 2029691) B2029691
theorem B11549465 : Blo 948586 11549465 := bstep (se 2 (by rfl) ⟨4331049, by rfl⟩ : syracuseStep 11549465 = 8662099) B8662099
theorem B12372041 : Blo 948586 12372041 := bstep (se 2 (by rfl) ⟨4639515, by rfl⟩ : syracuseStep 12372041 = 9279031) B9279031
theorem B5493491 : Blo 948586 5493491 := bstep (se 1 (by rfl) ⟨4120118, by rfl⟩ : syracuseStep 5493491 = 8240237) B8240237
theorem B6843113 : Blo 948586 6843113 := bstep (se 2 (by rfl) ⟨2566167, by rfl⟩ : syracuseStep 6843113 = 5132335) B5132335
theorem B1804169 : Blo 948586 1804169 := bstep (se 2 (by rfl) ⟨676563, by rfl⟩ : syracuseStep 1804169 = 1353127) B1353127
theorem B4068265 : Blo 948586 4068265 := bstep (se 2 (by rfl) ⟨1525599, by rfl⟩ : syracuseStep 4068265 = 3051199) B3051199
theorem B4562075 : Blo 948586 4562075 := bstep (se 1 (by rfl) ⟨3421556, by rfl⟩ : syracuseStep 4562075 = 6843113) B6843113
theorem B1424639 : Blo 948586 1424639 := bstep (se 1 (by rfl) ⟨1068479, by rfl⟩ : syracuseStep 1424639 = 2136959) B2136959
theorem B8248027 : Blo 948586 8248027 := bstep (se 1 (by rfl) ⟨6186020, by rfl⟩ : syracuseStep 8248027 = 12372041) B12372041
theorem B3662327 : Blo 948586 3662327 := bstep (se 1 (by rfl) ⟨2746745, by rfl⟩ : syracuseStep 3662327 = 5493491) B5493491
theorem B9139337 : Blo 948586 9139337 := bstep (se 2 (by rfl) ⟨3427251, by rfl⟩ : syracuseStep 9139337 = 6854503) B6854503
theorem B7699643 : Blo 948586 7699643 := bstep (se 1 (by rfl) ⟨5774732, by rfl⟩ : syracuseStep 7699643 = 11549465) B11549465
theorem B2441551 : Blo 948586 2441551 := bstep (se 1 (by rfl) ⟨1831163, by rfl⟩ : syracuseStep 2441551 = 3662327) B3662327
theorem B5424353 : Blo 948586 5424353 := bstep (se 2 (by rfl) ⟨2034132, by rfl⟩ : syracuseStep 5424353 = 4068265) B4068265
theorem B10997369 : Blo 948586 10997369 := bstep (se 2 (by rfl) ⟨4124013, by rfl⟩ : syracuseStep 10997369 = 8248027) B8248027
theorem B5133095 : Blo 948586 5133095 := bstep (se 1 (by rfl) ⟨3849821, by rfl⟩ : syracuseStep 5133095 = 7699643) B7699643
theorem B1202779 : Blo 948586 1202779 := bstep (se 1 (by rfl) ⟨902084, by rfl⟩ : syracuseStep 1202779 = 1804169) B1804169
theorem B3041383 : Blo 948586 3041383 := bstep (se 1 (by rfl) ⟨2281037, by rfl⟩ : syracuseStep 3041383 = 4562075) B4562075
theorem B6092891 : Blo 948586 6092891 := bstep (se 1 (by rfl) ⟨4569668, by rfl⟩ : syracuseStep 6092891 = 9139337) B9139337
theorem B949759 : Blo 948586 949759 := bstep (se 1 (by rfl) ⟨712319, by rfl⟩ : syracuseStep 949759 = 1424639) B1424639
theorem B3255401 : Blo 948586 3255401 := bstep (se 2 (by rfl) ⟨1220775, by rfl⟩ : syracuseStep 3255401 = 2441551) B2441551
theorem B3616235 : Blo 948586 3616235 := bstep (se 1 (by rfl) ⟨2712176, by rfl⟩ : syracuseStep 3616235 = 5424353) B5424353
theorem B3422063 : Blo 948586 3422063 := bstep (se 1 (by rfl) ⟨2566547, by rfl⟩ : syracuseStep 3422063 = 5133095) B5133095
theorem B7331579 : Blo 948586 7331579 := bstep (se 1 (by rfl) ⟨5498684, by rfl⟩ : syracuseStep 7331579 = 10997369) B10997369
theorem B4055177 : Blo 948586 4055177 := bstep (se 2 (by rfl) ⟨1520691, by rfl⟩ : syracuseStep 4055177 = 3041383) B3041383
theorem B1603705 : Blo 948586 1603705 := bstep (se 2 (by rfl) ⟨601389, by rfl⟩ : syracuseStep 1603705 = 1202779) B1202779
theorem B4061927 : Blo 948586 4061927 := bstep (se 1 (by rfl) ⟨3046445, by rfl⟩ : syracuseStep 4061927 = 6092891) B6092891
theorem B4887719 : Blo 948586 4887719 := bstep (se 1 (by rfl) ⟨3665789, by rfl⟩ : syracuseStep 4887719 = 7331579) B7331579
theorem B2138273 : Blo 948586 2138273 := bstep (se 2 (by rfl) ⟨801852, by rfl⟩ : syracuseStep 2138273 = 1603705) B1603705
theorem B2703451 : Blo 948586 2703451 := bstep (se 1 (by rfl) ⟨2027588, by rfl⟩ : syracuseStep 2703451 = 4055177) B4055177
theorem B2410823 : Blo 948586 2410823 := bstep (se 1 (by rfl) ⟨1808117, by rfl⟩ : syracuseStep 2410823 = 3616235) B3616235
theorem B2281375 : Blo 948586 2281375 := bstep (se 1 (by rfl) ⟨1711031, by rfl⟩ : syracuseStep 2281375 = 3422063) B3422063
theorem B2707951 : Blo 948586 2707951 := bstep (se 1 (by rfl) ⟨2030963, by rfl⟩ : syracuseStep 2707951 = 4061927) B4061927
theorem B8681069 : Blo 948586 8681069 := bstep (se 3 (by rfl) ⟨1627700, by rfl⟩ : syracuseStep 8681069 = 3255401) B3255401
theorem B3604601 : Blo 948586 3604601 := bstep (se 2 (by rfl) ⟨1351725, by rfl⟩ : syracuseStep 3604601 = 2703451) B2703451
theorem B1607215 : Blo 948586 1607215 := bstep (se 1 (by rfl) ⟨1205411, by rfl⟩ : syracuseStep 1607215 = 2410823) B2410823
theorem B3610601 : Blo 948586 3610601 := bstep (se 2 (by rfl) ⟨1353975, by rfl⟩ : syracuseStep 3610601 = 2707951) B2707951
theorem B3258479 : Blo 948586 3258479 := bstep (se 1 (by rfl) ⟨2443859, by rfl⟩ : syracuseStep 3258479 = 4887719) B4887719
theorem B1425515 : Blo 948586 1425515 := bstep (se 1 (by rfl) ⟨1069136, by rfl⟩ : syracuseStep 1425515 = 2138273) B2138273
theorem B5787379 : Blo 948586 5787379 := bstep (se 1 (by rfl) ⟨4340534, by rfl⟩ : syracuseStep 5787379 = 8681069) B8681069
theorem B3041833 : Blo 948586 3041833 := bstep (se 2 (by rfl) ⟨1140687, by rfl⟩ : syracuseStep 3041833 = 2281375) B2281375
theorem B950343 : Blo 948586 950343 := bstep (se 1 (by rfl) ⟨712757, by rfl⟩ : syracuseStep 950343 = 1425515) B1425515
theorem B2172319 : Blo 948586 2172319 := bstep (se 1 (by rfl) ⟨1629239, by rfl⟩ : syracuseStep 2172319 = 3258479) B3258479
theorem B2403067 : Blo 948586 2403067 := bstep (se 1 (by rfl) ⟨1802300, by rfl⟩ : syracuseStep 2403067 = 3604601) B3604601
theorem B2142953 : Blo 948586 2142953 := bstep (se 2 (by rfl) ⟨803607, by rfl⟩ : syracuseStep 2142953 = 1607215) B1607215
theorem B2407067 : Blo 948586 2407067 := bstep (se 1 (by rfl) ⟨1805300, by rfl⟩ : syracuseStep 2407067 = 3610601) B3610601
theorem B4055777 : Blo 948586 4055777 := bstep (se 2 (by rfl) ⟨1520916, by rfl⟩ : syracuseStep 4055777 = 3041833) B3041833
theorem B30866021 : Blo 948586 30866021 := bstep (se 4 (by rfl) ⟨2893689, by rfl⟩ : syracuseStep 30866021 = 5787379) B5787379
theorem B2703851 : Blo 948586 2703851 := bstep (se 1 (by rfl) ⟨2027888, by rfl⟩ : syracuseStep 2703851 = 4055777) B4055777
theorem B11585701 : Blo 948586 11585701 := bstep (se 4 (by rfl) ⟨1086159, by rfl⟩ : syracuseStep 11585701 = 2172319) B2172319
theorem B1428635 : Blo 948586 1428635 := bstep (se 1 (by rfl) ⟨1071476, by rfl⟩ : syracuseStep 1428635 = 2142953) B2142953
theorem B3204089 : Blo 948586 3204089 := bstep (se 2 (by rfl) ⟨1201533, by rfl⟩ : syracuseStep 3204089 = 2403067) B2403067
theorem B20577347 : Blo 948586 20577347 := bstep (se 1 (by rfl) ⟨15433010, by rfl⟩ : syracuseStep 20577347 = 30866021) B30866021
theorem B1604711 : Blo 948586 1604711 := bstep (se 1 (by rfl) ⟨1203533, by rfl⟩ : syracuseStep 1604711 = 2407067) B2407067
theorem B1802567 : Blo 948586 1802567 := bstep (se 1 (by rfl) ⟨1351925, by rfl⟩ : syracuseStep 1802567 = 2703851) B2703851
theorem B952423 : Blo 948586 952423 := bstep (se 1 (by rfl) ⟨714317, by rfl⟩ : syracuseStep 952423 = 1428635) B1428635
theorem B2136059 : Blo 948586 2136059 := bstep (se 1 (by rfl) ⟨1602044, by rfl⟩ : syracuseStep 2136059 = 3204089) B3204089
theorem B15447601 : Blo 948586 15447601 := bstep (se 2 (by rfl) ⟨5792850, by rfl⟩ : syracuseStep 15447601 = 11585701) B11585701
theorem B13718231 : Blo 948586 13718231 := bstep (se 1 (by rfl) ⟨10288673, by rfl⟩ : syracuseStep 13718231 = 20577347) B20577347
theorem B1069807 : Blo 948586 1069807 := bstep (se 1 (by rfl) ⟨802355, by rfl⟩ : syracuseStep 1069807 = 1604711) B1604711
theorem B9145487 : Blo 948586 9145487 := bstep (se 1 (by rfl) ⟨6859115, by rfl⟩ : syracuseStep 9145487 = 13718231) B13718231
theorem B1424039 : Blo 948586 1424039 := bstep (se 1 (by rfl) ⟨1068029, by rfl⟩ : syracuseStep 1424039 = 2136059) B2136059
theorem B1426409 : Blo 948586 1426409 := bstep (se 2 (by rfl) ⟨534903, by rfl⟩ : syracuseStep 1426409 = 1069807) B1069807
theorem B20596801 : Blo 948586 20596801 := bstep (se 2 (by rfl) ⟨7723800, by rfl⟩ : syracuseStep 20596801 = 15447601) B15447601
theorem B1201711 : Blo 948586 1201711 := bstep (se 1 (by rfl) ⟨901283, by rfl⟩ : syracuseStep 1201711 = 1802567) B1802567
theorem B950939 : Blo 948586 950939 := bstep (se 1 (by rfl) ⟨713204, by rfl⟩ : syracuseStep 950939 = 1426409) B1426409
theorem B6096991 : Blo 948586 6096991 := bstep (se 1 (by rfl) ⟨4572743, by rfl⟩ : syracuseStep 6096991 = 9145487) B9145487
theorem B27462401 : Blo 948586 27462401 := bstep (se 2 (by rfl) ⟨10298400, by rfl⟩ : syracuseStep 27462401 = 20596801) B20596801
theorem B1602281 : Blo 948586 1602281 := bstep (se 2 (by rfl) ⟨600855, by rfl⟩ : syracuseStep 1602281 = 1201711) B1201711
theorem B949359 : Blo 948586 949359 := bstep (se 1 (by rfl) ⟨712019, by rfl⟩ : syracuseStep 949359 = 1424039) B1424039
theorem B8129321 : Blo 948586 8129321 := bstep (se 2 (by rfl) ⟨3048495, by rfl⟩ : syracuseStep 8129321 = 6096991) B6096991
theorem B1068187 : Blo 948586 1068187 := bstep (se 1 (by rfl) ⟨801140, by rfl⟩ : syracuseStep 1068187 = 1602281) B1602281
theorem B18308267 : Blo 948586 18308267 := bstep (se 1 (by rfl) ⟨13731200, by rfl⟩ : syracuseStep 18308267 = 27462401) B27462401
theorem B5419547 : Blo 948586 5419547 := bstep (se 1 (by rfl) ⟨4064660, by rfl⟩ : syracuseStep 5419547 = 8129321) B8129321
theorem B1424249 : Blo 948586 1424249 := bstep (se 2 (by rfl) ⟨534093, by rfl⟩ : syracuseStep 1424249 = 1068187) B1068187
theorem B12205511 : Blo 948586 12205511 := bstep (se 1 (by rfl) ⟨9154133, by rfl⟩ : syracuseStep 12205511 = 18308267) B18308267
theorem B3613031 : Blo 948586 3613031 := bstep (se 1 (by rfl) ⟨2709773, by rfl⟩ : syracuseStep 3613031 = 5419547) B5419547
theorem B8137007 : Blo 948586 8137007 := bstep (se 1 (by rfl) ⟨6102755, by rfl⟩ : syracuseStep 8137007 = 12205511) B12205511
theorem B949499 : Blo 948586 949499 := bstep (se 1 (by rfl) ⟨712124, by rfl⟩ : syracuseStep 949499 = 1424249) B1424249
theorem B2408687 : Blo 948586 2408687 := bstep (se 1 (by rfl) ⟨1806515, by rfl⟩ : syracuseStep 2408687 = 3613031) B3613031
theorem B5424671 : Blo 948586 5424671 := bstep (se 1 (by rfl) ⟨4068503, by rfl⟩ : syracuseStep 5424671 = 8137007) B8137007
theorem B1605791 : Blo 948586 1605791 := bstep (se 1 (by rfl) ⟨1204343, by rfl⟩ : syracuseStep 1605791 = 2408687) B2408687
theorem B3616447 : Blo 948586 3616447 := bstep (se 1 (by rfl) ⟨2712335, by rfl⟩ : syracuseStep 3616447 = 5424671) B5424671
theorem B4821929 : Blo 948586 4821929 := bstep (se 2 (by rfl) ⟨1808223, by rfl⟩ : syracuseStep 4821929 = 3616447) B3616447
theorem B1070527 : Blo 948586 1070527 := bstep (se 1 (by rfl) ⟨802895, by rfl⟩ : syracuseStep 1070527 = 1605791) B1605791
theorem B3214619 : Blo 948586 3214619 := bstep (se 1 (by rfl) ⟨2410964, by rfl⟩ : syracuseStep 3214619 = 4821929) B4821929
theorem B1427369 : Blo 948586 1427369 := bstep (se 2 (by rfl) ⟨535263, by rfl⟩ : syracuseStep 1427369 = 1070527) B1070527
theorem B951579 : Blo 948586 951579 := bstep (se 1 (by rfl) ⟨713684, by rfl⟩ : syracuseStep 951579 = 1427369) B1427369
theorem B2143079 : Blo 948586 2143079 := bstep (se 1 (by rfl) ⟨1607309, by rfl⟩ : syracuseStep 2143079 = 3214619) B3214619
theorem B1428719 : Blo 948586 1428719 := bstep (se 1 (by rfl) ⟨1071539, by rfl⟩ : syracuseStep 1428719 = 2143079) B2143079
theorem B952479 : Blo 948586 952479 := bstep (se 1 (by rfl) ⟨714359, by rfl⟩ : syracuseStep 952479 = 1428719) B1428719

theorem C0 (j : ℕ) (h1 : 237146 ≤ j) (h2 : j ≤ 237845) : Blo 948586 (4 * j + 3) := by
  interval_cases j
  · exact B948587
  · exact B948591
  · exact B948595
  · exact B948599
  · exact B948603
  · exact B948607
  · exact B948611
  · exact B948615
  · exact B948619
  · exact B948623
  · exact B948627
  · exact B948631
  · exact B948635
  · exact B948639
  · exact B948643
  · exact B948647
  · exact B948651
  · exact B948655
  · exact B948659
  · exact B948663
  · exact B948667
  · exact B948671
  · exact B948675
  · exact B948679
  · exact B948683
  · exact B948687
  · exact B948691
  · exact B948695
  · exact B948699
  · exact B948703
  · exact B948707
  · exact B948711
  · exact B948715
  · exact B948719
  · exact B948723
  · exact B948727
  · exact B948731
  · exact B948735
  · exact B948739
  · exact B948743
  · exact B948747
  · exact B948751
  · exact B948755
  · exact B948759
  · exact B948763
  · exact B948767
  · exact B948771
  · exact B948775
  · exact B948779
  · exact B948783
  · exact B948787
  · exact B948791
  · exact B948795
  · exact B948799
  · exact B948803
  · exact B948807
  · exact B948811
  · exact B948815
  · exact B948819
  · exact B948823
  · exact B948827
  · exact B948831
  · exact B948835
  · exact B948839
  · exact B948843
  · exact B948847
  · exact B948851
  · exact B948855
  · exact B948859
  · exact B948863
  · exact B948867
  · exact B948871
  · exact B948875
  · exact B948879
  · exact B948883
  · exact B948887
  · exact B948891
  · exact B948895
  · exact B948899
  · exact B948903
  · exact B948907
  · exact B948911
  · exact B948915
  · exact B948919
  · exact B948923
  · exact B948927
  · exact B948931
  · exact B948935
  · exact B948939
  · exact B948943
  · exact B948947
  · exact B948951
  · exact B948955
  · exact B948959
  · exact B948963
  · exact B948967
  · exact B948971
  · exact B948975
  · exact B948979
  · exact B948983
  · exact B948987
  · exact B948991
  · exact B948995
  · exact B948999
  · exact B949003
  · exact B949007
  · exact B949011
  · exact B949015
  · exact B949019
  · exact B949023
  · exact B949027
  · exact B949031
  · exact B949035
  · exact B949039
  · exact B949043
  · exact B949047
  · exact B949051
  · exact B949055
  · exact B949059
  · exact B949063
  · exact B949067
  · exact B949071
  · exact B949075
  · exact B949079
  · exact B949083
  · exact B949087
  · exact B949091
  · exact B949095
  · exact B949099
  · exact B949103
  · exact B949107
  · exact B949111
  · exact B949115
  · exact B949119
  · exact B949123
  · exact B949127
  · exact B949131
  · exact B949135
  · exact B949139
  · exact B949143
  · exact B949147
  · exact B949151
  · exact B949155
  · exact B949159
  · exact B949163
  · exact B949167
  · exact B949171
  · exact B949175
  · exact B949179
  · exact B949183
  · exact B949187
  · exact B949191
  · exact B949195
  · exact B949199
  · exact B949203
  · exact B949207
  · exact B949211
  · exact B949215
  · exact B949219
  · exact B949223
  · exact B949227
  · exact B949231
  · exact B949235
  · exact B949239
  · exact B949243
  · exact B949247
  · exact B949251
  · exact B949255
  · exact B949259
  · exact B949263
  · exact B949267
  · exact B949271
  · exact B949275
  · exact B949279
  · exact B949283
  · exact B949287
  · exact B949291
  · exact B949295
  · exact B949299
  · exact B949303
  · exact B949307
  · exact B949311
  · exact B949315
  · exact B949319
  · exact B949323
  · exact B949327
  · exact B949331
  · exact B949335
  · exact B949339
  · exact B949343
  · exact B949347
  · exact B949351
  · exact B949355
  · exact B949359
  · exact B949363
  · exact B949367
  · exact B949371
  · exact B949375
  · exact B949379
  · exact B949383
  · exact B949387
  · exact B949391
  · exact B949395
  · exact B949399
  · exact B949403
  · exact B949407
  · exact B949411
  · exact B949415
  · exact B949419
  · exact B949423
  · exact B949427
  · exact B949431
  · exact B949435
  · exact B949439
  · exact B949443
  · exact B949447
  · exact B949451
  · exact B949455
  · exact B949459
  · exact B949463
  · exact B949467
  · exact B949471
  · exact B949475
  · exact B949479
  · exact B949483
  · exact B949487
  · exact B949491
  · exact B949495
  · exact B949499
  · exact B949503
  · exact B949507
  · exact B949511
  · exact B949515
  · exact B949519
  · exact B949523
  · exact B949527
  · exact B949531
  · exact B949535
  · exact B949539
  · exact B949543
  · exact B949547
  · exact B949551
  · exact B949555
  · exact B949559
  · exact B949563
  · exact B949567
  · exact B949571
  · exact B949575
  · exact B949579
  · exact B949583
  · exact B949587
  · exact B949591
  · exact B949595
  · exact B949599
  · exact B949603
  · exact B949607
  · exact B949611
  · exact B949615
  · exact B949619
  · exact B949623
  · exact B949627
  · exact B949631
  · exact B949635
  · exact B949639
  · exact B949643
  · exact B949647
  · exact B949651
  · exact B949655
  · exact B949659
  · exact B949663
  · exact B949667
  · exact B949671
  · exact B949675
  · exact B949679
  · exact B949683
  · exact B949687
  · exact B949691
  · exact B949695
  · exact B949699
  · exact B949703
  · exact B949707
  · exact B949711
  · exact B949715
  · exact B949719
  · exact B949723
  · exact B949727
  · exact B949731
  · exact B949735
  · exact B949739
  · exact B949743
  · exact B949747
  · exact B949751
  · exact B949755
  · exact B949759
  · exact B949763
  · exact B949767
  · exact B949771
  · exact B949775
  · exact B949779
  · exact B949783
  · exact B949787
  · exact B949791
  · exact B949795
  · exact B949799
  · exact B949803
  · exact B949807
  · exact B949811
  · exact B949815
  · exact B949819
  · exact B949823
  · exact B949827
  · exact B949831
  · exact B949835
  · exact B949839
  · exact B949843
  · exact B949847
  · exact B949851
  · exact B949855
  · exact B949859
  · exact B949863
  · exact B949867
  · exact B949871
  · exact B949875
  · exact B949879
  · exact B949883
  · exact B949887
  · exact B949891
  · exact B949895
  · exact B949899
  · exact B949903
  · exact B949907
  · exact B949911
  · exact B949915
  · exact B949919
  · exact B949923
  · exact B949927
  · exact B949931
  · exact B949935
  · exact B949939
  · exact B949943
  · exact B949947
  · exact B949951
  · exact B949955
  · exact B949959
  · exact B949963
  · exact B949967
  · exact B949971
  · exact B949975
  · exact B949979
  · exact B949983
  · exact B949987
  · exact B949991
  · exact B949995
  · exact B949999
  · exact B950003
  · exact B950007
  · exact B950011
  · exact B950015
  · exact B950019
  · exact B950023
  · exact B950027
  · exact B950031
  · exact B950035
  · exact B950039
  · exact B950043
  · exact B950047
  · exact B950051
  · exact B950055
  · exact B950059
  · exact B950063
  · exact B950067
  · exact B950071
  · exact B950075
  · exact B950079
  · exact B950083
  · exact B950087
  · exact B950091
  · exact B950095
  · exact B950099
  · exact B950103
  · exact B950107
  · exact B950111
  · exact B950115
  · exact B950119
  · exact B950123
  · exact B950127
  · exact B950131
  · exact B950135
  · exact B950139
  · exact B950143
  · exact B950147
  · exact B950151
  · exact B950155
  · exact B950159
  · exact B950163
  · exact B950167
  · exact B950171
  · exact B950175
  · exact B950179
  · exact B950183
  · exact B950187
  · exact B950191
  · exact B950195
  · exact B950199
  · exact B950203
  · exact B950207
  · exact B950211
  · exact B950215
  · exact B950219
  · exact B950223
  · exact B950227
  · exact B950231
  · exact B950235
  · exact B950239
  · exact B950243
  · exact B950247
  · exact B950251
  · exact B950255
  · exact B950259
  · exact B950263
  · exact B950267
  · exact B950271
  · exact B950275
  · exact B950279
  · exact B950283
  · exact B950287
  · exact B950291
  · exact B950295
  · exact B950299
  · exact B950303
  · exact B950307
  · exact B950311
  · exact B950315
  · exact B950319
  · exact B950323
  · exact B950327
  · exact B950331
  · exact B950335
  · exact B950339
  · exact B950343
  · exact B950347
  · exact B950351
  · exact B950355
  · exact B950359
  · exact B950363
  · exact B950367
  · exact B950371
  · exact B950375
  · exact B950379
  · exact B950383
  · exact B950387
  · exact B950391
  · exact B950395
  · exact B950399
  · exact B950403
  · exact B950407
  · exact B950411
  · exact B950415
  · exact B950419
  · exact B950423
  · exact B950427
  · exact B950431
  · exact B950435
  · exact B950439
  · exact B950443
  · exact B950447
  · exact B950451
  · exact B950455
  · exact B950459
  · exact B950463
  · exact B950467
  · exact B950471
  · exact B950475
  · exact B950479
  · exact B950483
  · exact B950487
  · exact B950491
  · exact B950495
  · exact B950499
  · exact B950503
  · exact B950507
  · exact B950511
  · exact B950515
  · exact B950519
  · exact B950523
  · exact B950527
  · exact B950531
  · exact B950535
  · exact B950539
  · exact B950543
  · exact B950547
  · exact B950551
  · exact B950555
  · exact B950559
  · exact B950563
  · exact B950567
  · exact B950571
  · exact B950575
  · exact B950579
  · exact B950583
  · exact B950587
  · exact B950591
  · exact B950595
  · exact B950599
  · exact B950603
  · exact B950607
  · exact B950611
  · exact B950615
  · exact B950619
  · exact B950623
  · exact B950627
  · exact B950631
  · exact B950635
  · exact B950639
  · exact B950643
  · exact B950647
  · exact B950651
  · exact B950655
  · exact B950659
  · exact B950663
  · exact B950667
  · exact B950671
  · exact B950675
  · exact B950679
  · exact B950683
  · exact B950687
  · exact B950691
  · exact B950695
  · exact B950699
  · exact B950703
  · exact B950707
  · exact B950711
  · exact B950715
  · exact B950719
  · exact B950723
  · exact B950727
  · exact B950731
  · exact B950735
  · exact B950739
  · exact B950743
  · exact B950747
  · exact B950751
  · exact B950755
  · exact B950759
  · exact B950763
  · exact B950767
  · exact B950771
  · exact B950775
  · exact B950779
  · exact B950783
  · exact B950787
  · exact B950791
  · exact B950795
  · exact B950799
  · exact B950803
  · exact B950807
  · exact B950811
  · exact B950815
  · exact B950819
  · exact B950823
  · exact B950827
  · exact B950831
  · exact B950835
  · exact B950839
  · exact B950843
  · exact B950847
  · exact B950851
  · exact B950855
  · exact B950859
  · exact B950863
  · exact B950867
  · exact B950871
  · exact B950875
  · exact B950879
  · exact B950883
  · exact B950887
  · exact B950891
  · exact B950895
  · exact B950899
  · exact B950903
  · exact B950907
  · exact B950911
  · exact B950915
  · exact B950919
  · exact B950923
  · exact B950927
  · exact B950931
  · exact B950935
  · exact B950939
  · exact B950943
  · exact B950947
  · exact B950951
  · exact B950955
  · exact B950959
  · exact B950963
  · exact B950967
  · exact B950971
  · exact B950975
  · exact B950979
  · exact B950983
  · exact B950987
  · exact B950991
  · exact B950995
  · exact B950999
  · exact B951003
  · exact B951007
  · exact B951011
  · exact B951015
  · exact B951019
  · exact B951023
  · exact B951027
  · exact B951031
  · exact B951035
  · exact B951039
  · exact B951043
  · exact B951047
  · exact B951051
  · exact B951055
  · exact B951059
  · exact B951063
  · exact B951067
  · exact B951071
  · exact B951075
  · exact B951079
  · exact B951083
  · exact B951087
  · exact B951091
  · exact B951095
  · exact B951099
  · exact B951103
  · exact B951107
  · exact B951111
  · exact B951115
  · exact B951119
  · exact B951123
  · exact B951127
  · exact B951131
  · exact B951135
  · exact B951139
  · exact B951143
  · exact B951147
  · exact B951151
  · exact B951155
  · exact B951159
  · exact B951163
  · exact B951167
  · exact B951171
  · exact B951175
  · exact B951179
  · exact B951183
  · exact B951187
  · exact B951191
  · exact B951195
  · exact B951199
  · exact B951203
  · exact B951207
  · exact B951211
  · exact B951215
  · exact B951219
  · exact B951223
  · exact B951227
  · exact B951231
  · exact B951235
  · exact B951239
  · exact B951243
  · exact B951247
  · exact B951251
  · exact B951255
  · exact B951259
  · exact B951263
  · exact B951267
  · exact B951271
  · exact B951275
  · exact B951279
  · exact B951283
  · exact B951287
  · exact B951291
  · exact B951295
  · exact B951299
  · exact B951303
  · exact B951307
  · exact B951311
  · exact B951315
  · exact B951319
  · exact B951323
  · exact B951327
  · exact B951331
  · exact B951335
  · exact B951339
  · exact B951343
  · exact B951347
  · exact B951351
  · exact B951355
  · exact B951359
  · exact B951363
  · exact B951367
  · exact B951371
  · exact B951375
  · exact B951379
  · exact B951383

theorem C1 (j : ℕ) (h1 : 237846 ≤ j) (h2 : j ≤ 238145) : Blo 948586 (4 * j + 3) := by
  interval_cases j
  · exact B951387
  · exact B951391
  · exact B951395
  · exact B951399
  · exact B951403
  · exact B951407
  · exact B951411
  · exact B951415
  · exact B951419
  · exact B951423
  · exact B951427
  · exact B951431
  · exact B951435
  · exact B951439
  · exact B951443
  · exact B951447
  · exact B951451
  · exact B951455
  · exact B951459
  · exact B951463
  · exact B951467
  · exact B951471
  · exact B951475
  · exact B951479
  · exact B951483
  · exact B951487
  · exact B951491
  · exact B951495
  · exact B951499
  · exact B951503
  · exact B951507
  · exact B951511
  · exact B951515
  · exact B951519
  · exact B951523
  · exact B951527
  · exact B951531
  · exact B951535
  · exact B951539
  · exact B951543
  · exact B951547
  · exact B951551
  · exact B951555
  · exact B951559
  · exact B951563
  · exact B951567
  · exact B951571
  · exact B951575
  · exact B951579
  · exact B951583
  · exact B951587
  · exact B951591
  · exact B951595
  · exact B951599
  · exact B951603
  · exact B951607
  · exact B951611
  · exact B951615
  · exact B951619
  · exact B951623
  · exact B951627
  · exact B951631
  · exact B951635
  · exact B951639
  · exact B951643
  · exact B951647
  · exact B951651
  · exact B951655
  · exact B951659
  · exact B951663
  · exact B951667
  · exact B951671
  · exact B951675
  · exact B951679
  · exact B951683
  · exact B951687
  · exact B951691
  · exact B951695
  · exact B951699
  · exact B951703
  · exact B951707
  · exact B951711
  · exact B951715
  · exact B951719
  · exact B951723
  · exact B951727
  · exact B951731
  · exact B951735
  · exact B951739
  · exact B951743
  · exact B951747
  · exact B951751
  · exact B951755
  · exact B951759
  · exact B951763
  · exact B951767
  · exact B951771
  · exact B951775
  · exact B951779
  · exact B951783
  · exact B951787
  · exact B951791
  · exact B951795
  · exact B951799
  · exact B951803
  · exact B951807
  · exact B951811
  · exact B951815
  · exact B951819
  · exact B951823
  · exact B951827
  · exact B951831
  · exact B951835
  · exact B951839
  · exact B951843
  · exact B951847
  · exact B951851
  · exact B951855
  · exact B951859
  · exact B951863
  · exact B951867
  · exact B951871
  · exact B951875
  · exact B951879
  · exact B951883
  · exact B951887
  · exact B951891
  · exact B951895
  · exact B951899
  · exact B951903
  · exact B951907
  · exact B951911
  · exact B951915
  · exact B951919
  · exact B951923
  · exact B951927
  · exact B951931
  · exact B951935
  · exact B951939
  · exact B951943
  · exact B951947
  · exact B951951
  · exact B951955
  · exact B951959
  · exact B951963
  · exact B951967
  · exact B951971
  · exact B951975
  · exact B951979
  · exact B951983
  · exact B951987
  · exact B951991
  · exact B951995
  · exact B951999
  · exact B952003
  · exact B952007
  · exact B952011
  · exact B952015
  · exact B952019
  · exact B952023
  · exact B952027
  · exact B952031
  · exact B952035
  · exact B952039
  · exact B952043
  · exact B952047
  · exact B952051
  · exact B952055
  · exact B952059
  · exact B952063
  · exact B952067
  · exact B952071
  · exact B952075
  · exact B952079
  · exact B952083
  · exact B952087
  · exact B952091
  · exact B952095
  · exact B952099
  · exact B952103
  · exact B952107
  · exact B952111
  · exact B952115
  · exact B952119
  · exact B952123
  · exact B952127
  · exact B952131
  · exact B952135
  · exact B952139
  · exact B952143
  · exact B952147
  · exact B952151
  · exact B952155
  · exact B952159
  · exact B952163
  · exact B952167
  · exact B952171
  · exact B952175
  · exact B952179
  · exact B952183
  · exact B952187
  · exact B952191
  · exact B952195
  · exact B952199
  · exact B952203
  · exact B952207
  · exact B952211
  · exact B952215
  · exact B952219
  · exact B952223
  · exact B952227
  · exact B952231
  · exact B952235
  · exact B952239
  · exact B952243
  · exact B952247
  · exact B952251
  · exact B952255
  · exact B952259
  · exact B952263
  · exact B952267
  · exact B952271
  · exact B952275
  · exact B952279
  · exact B952283
  · exact B952287
  · exact B952291
  · exact B952295
  · exact B952299
  · exact B952303
  · exact B952307
  · exact B952311
  · exact B952315
  · exact B952319
  · exact B952323
  · exact B952327
  · exact B952331
  · exact B952335
  · exact B952339
  · exact B952343
  · exact B952347
  · exact B952351
  · exact B952355
  · exact B952359
  · exact B952363
  · exact B952367
  · exact B952371
  · exact B952375
  · exact B952379
  · exact B952383
  · exact B952387
  · exact B952391
  · exact B952395
  · exact B952399
  · exact B952403
  · exact B952407
  · exact B952411
  · exact B952415
  · exact B952419
  · exact B952423
  · exact B952427
  · exact B952431
  · exact B952435
  · exact B952439
  · exact B952443
  · exact B952447
  · exact B952451
  · exact B952455
  · exact B952459
  · exact B952463
  · exact B952467
  · exact B952471
  · exact B952475
  · exact B952479
  · exact B952483
  · exact B952487
  · exact B952491
  · exact B952495
  · exact B952499
  · exact B952503
  · exact B952507
  · exact B952511
  · exact B952515
  · exact B952519
  · exact B952523
  · exact B952527
  · exact B952531
  · exact B952535
  · exact B952539
  · exact B952543
  · exact B952547
  · exact B952551
  · exact B952555
  · exact B952559
  · exact B952563
  · exact B952567
  · exact B952571
  · exact B952575
  · exact B952579
  · exact B952583

theorem solution (m : ℕ) (hlo : 948586 ≤ m) (hhi : m ≤ 952586) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 237146 ≤ j := by omega
    have hj2 : j ≤ 238145 := by omega
    have hb : Blo 948586 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 237846 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
