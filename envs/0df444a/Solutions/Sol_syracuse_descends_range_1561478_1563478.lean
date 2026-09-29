-- Prove2me | solution 1 for syracuse_descends_range_1561478_1563478
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:06:21.628639+00:00
-- url     : https://prove2.me/submissions/48fdd9c9-ac28-4771-a90e-3e34ff6b520f

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


theorem B3514373 : Blo 1561478 3514373 := bbase (se 4 (by rfl) ⟨329472, by rfl⟩ : syracuseStep 3514373 = 658945) (by norm_num)
theorem B2342933 : Blo 1561478 2342933 := bbase (se 6 (by rfl) ⟨54912, by rfl⟩ : syracuseStep 2342933 = 109825) (by norm_num)
theorem B6676501 : Blo 1561478 6676501 := bbase (se 6 (by rfl) ⟨156480, by rfl⟩ : syracuseStep 6676501 = 312961) (by norm_num)
theorem B2342957 : Blo 1561478 2342957 := bbase (se 3 (by rfl) ⟨439304, by rfl⟩ : syracuseStep 2342957 = 878609) (by norm_num)
theorem B3956789 : Blo 1561478 3956789 := bbase (se 5 (by rfl) ⟨185474, by rfl⟩ : syracuseStep 3956789 = 370949) (by norm_num)
theorem B2965565 : Blo 1561478 2965565 := bbase (se 3 (by rfl) ⟨556043, by rfl⟩ : syracuseStep 2965565 = 1112087) (by norm_num)
theorem B2342981 : Blo 1561478 2342981 := bbase (se 4 (by rfl) ⟨219654, by rfl⟩ : syracuseStep 2342981 = 439309) (by norm_num)
theorem B2637893 : Blo 1561478 2637893 := bbase (se 4 (by rfl) ⟨247302, by rfl⟩ : syracuseStep 2637893 = 494605) (by norm_num)
theorem B3514445 : Blo 1561478 3514445 := bbase (se 3 (by rfl) ⟨658958, by rfl⟩ : syracuseStep 3514445 = 1317917) (by norm_num)
theorem B2343005 : Blo 1561478 2343005 := bbase (se 3 (by rfl) ⟨439313, by rfl⟩ : syracuseStep 2343005 = 878627) (by norm_num)
theorem B2343029 : Blo 1561478 2343029 := bbase (se 5 (by rfl) ⟨109829, by rfl⟩ : syracuseStep 2343029 = 219659) (by norm_num)
theorem B2343053 : Blo 1561478 2343053 := bbase (se 3 (by rfl) ⟨439322, by rfl⟩ : syracuseStep 2343053 = 878645) (by norm_num)
theorem B3514517 : Blo 1561478 3514517 := bbase (se 6 (by rfl) ⟨82371, by rfl⟩ : syracuseStep 3514517 = 164743) (by norm_num)
theorem B2343077 : Blo 1561478 2343077 := bbase (se 4 (by rfl) ⟨219663, by rfl⟩ : syracuseStep 2343077 = 439327) (by norm_num)
theorem B2343101 : Blo 1561478 2343101 := bbase (se 3 (by rfl) ⟨439331, by rfl⟩ : syracuseStep 2343101 = 878663) (by norm_num)
theorem B2638021 : Blo 1561478 2638021 := bbase (se 4 (by rfl) ⟨247314, by rfl⟩ : syracuseStep 2638021 = 494629) (by norm_num)
theorem B2965709 : Blo 1561478 2965709 := bbase (se 3 (by rfl) ⟨556070, by rfl⟩ : syracuseStep 2965709 = 1112141) (by norm_num)
theorem B2343125 : Blo 1561478 2343125 := bbase (se 7 (by rfl) ⟨27458, by rfl⟩ : syracuseStep 2343125 = 54917) (by norm_num)
theorem B8560853 : Blo 1561478 8560853 := bbase (se 7 (by rfl) ⟨100322, by rfl⟩ : syracuseStep 8560853 = 200645) (by norm_num)
theorem B7512277 : Blo 1561478 7512277 := bbase (se 7 (by rfl) ⟨88034, by rfl⟩ : syracuseStep 7512277 = 176069) (by norm_num)
theorem B3514589 : Blo 1561478 3514589 := bbase (se 3 (by rfl) ⟨658985, by rfl⟩ : syracuseStep 3514589 = 1317971) (by norm_num)
theorem B2343149 : Blo 1561478 2343149 := bbase (se 3 (by rfl) ⟨439340, by rfl⟩ : syracuseStep 2343149 = 878681) (by norm_num)
theorem B3752189 : Blo 1561478 3752189 := bbase (se 3 (by rfl) ⟨703535, by rfl⟩ : syracuseStep 3752189 = 1407071) (by norm_num)
theorem B2343173 : Blo 1561478 2343173 := bbase (se 4 (by rfl) ⟨219672, by rfl⟩ : syracuseStep 2343173 = 439345) (by norm_num)
theorem B2343197 : Blo 1561478 2343197 := bbase (se 3 (by rfl) ⟨439349, by rfl⟩ : syracuseStep 2343197 = 878699) (by norm_num)
theorem B2638109 : Blo 1561478 2638109 := bbase (se 3 (by rfl) ⟨494645, by rfl⟩ : syracuseStep 2638109 = 989291) (by norm_num)
theorem B3514661 : Blo 1561478 3514661 := bbase (se 4 (by rfl) ⟨329499, by rfl⟩ : syracuseStep 3514661 = 658999) (by norm_num)
theorem B2343221 : Blo 1561478 2343221 := bbase (se 5 (by rfl) ⟨109838, by rfl⟩ : syracuseStep 2343221 = 219677) (by norm_num)
theorem B2343245 : Blo 1561478 2343245 := bbase (se 3 (by rfl) ⟨439358, by rfl⟩ : syracuseStep 2343245 = 878717) (by norm_num)
theorem B11870549 : Blo 1561478 11870549 := bbase (se 10 (by rfl) ⟨17388, by rfl⟩ : syracuseStep 11870549 = 34777) (by norm_num)
theorem B2343269 : Blo 1561478 2343269 := bbase (se 4 (by rfl) ⟨219681, by rfl⟩ : syracuseStep 2343269 = 439363) (by norm_num)
theorem B3514733 : Blo 1561478 3514733 := bbase (se 3 (by rfl) ⟨659012, by rfl⟩ : syracuseStep 3514733 = 1318025) (by norm_num)
theorem B2343293 : Blo 1561478 2343293 := bbase (se 3 (by rfl) ⟨439367, by rfl⟩ : syracuseStep 2343293 = 878735) (by norm_num)
theorem B2408837 : Blo 1561478 2408837 := bbase (se 4 (by rfl) ⟨225828, by rfl⟩ : syracuseStep 2408837 = 451657) (by norm_num)
theorem B7913861 : Blo 1561478 7913861 := bbase (se 4 (by rfl) ⟨741924, by rfl⟩ : syracuseStep 7913861 = 1483849) (by norm_num)
theorem B3957133 : Blo 1561478 3957133 := bbase (se 3 (by rfl) ⟨741962, by rfl⟩ : syracuseStep 3957133 = 1483925) (by norm_num)
theorem B2343317 : Blo 1561478 2343317 := bbase (se 6 (by rfl) ⟨54921, by rfl⟩ : syracuseStep 2343317 = 109843) (by norm_num)
theorem B2638237 : Blo 1561478 2638237 := bbase (se 3 (by rfl) ⟨494669, by rfl⟩ : syracuseStep 2638237 = 989339) (by norm_num)
theorem B4448677 : Blo 1561478 4448677 := bbase (se 4 (by rfl) ⟨417063, by rfl⟩ : syracuseStep 4448677 = 834127) (by norm_num)
theorem B5276069 : Blo 1561478 5276069 := bbase (se 4 (by rfl) ⟨494631, by rfl⟩ : syracuseStep 5276069 = 989263) (by norm_num)
theorem B2343341 : Blo 1561478 2343341 := bbase (se 3 (by rfl) ⟨439376, by rfl⟩ : syracuseStep 2343341 = 878753) (by norm_num)
theorem B3514805 : Blo 1561478 3514805 := bbase (se 5 (by rfl) ⟨164756, by rfl⟩ : syracuseStep 3514805 = 329513) (by norm_num)
theorem B2343365 : Blo 1561478 2343365 := bbase (se 4 (by rfl) ⟨219690, by rfl⟩ : syracuseStep 2343365 = 439381) (by norm_num)
theorem B2343389 : Blo 1561478 2343389 := bbase (se 3 (by rfl) ⟨439385, by rfl⟩ : syracuseStep 2343389 = 878771) (by norm_num)
theorem B2965997 : Blo 1561478 2965997 := bbase (se 3 (by rfl) ⟨556124, by rfl⟩ : syracuseStep 2965997 = 1112249) (by norm_num)
theorem B2343413 : Blo 1561478 2343413 := bbase (se 5 (by rfl) ⟨109847, by rfl⟩ : syracuseStep 2343413 = 219695) (by norm_num)
theorem B2638325 : Blo 1561478 2638325 := bbase (se 5 (by rfl) ⟨123671, by rfl⟩ : syracuseStep 2638325 = 247343) (by norm_num)
theorem B3514877 : Blo 1561478 3514877 := bbase (se 3 (by rfl) ⟨659039, by rfl⟩ : syracuseStep 3514877 = 1318079) (by norm_num)
theorem B3957245 : Blo 1561478 3957245 := bbase (se 3 (by rfl) ⟨741983, by rfl⟩ : syracuseStep 3957245 = 1483967) (by norm_num)
theorem B2343437 : Blo 1561478 2343437 := bbase (se 3 (by rfl) ⟨439394, by rfl⟩ : syracuseStep 2343437 = 878789) (by norm_num)
theorem B3752477 : Blo 1561478 3752477 := bbase (se 3 (by rfl) ⟨703589, by rfl⟩ : syracuseStep 3752477 = 1407179) (by norm_num)
theorem B2343461 : Blo 1561478 2343461 := bbase (se 4 (by rfl) ⟨219699, by rfl⟩ : syracuseStep 2343461 = 439399) (by norm_num)
theorem B2343485 : Blo 1561478 2343485 := bbase (se 3 (by rfl) ⟨439403, by rfl⟩ : syracuseStep 2343485 = 878807) (by norm_num)
theorem B3514949 : Blo 1561478 3514949 := bbase (se 4 (by rfl) ⟨329526, by rfl⟩ : syracuseStep 3514949 = 659053) (by norm_num)
theorem B4448837 : Blo 1561478 4448837 := bbase (se 4 (by rfl) ⟨417078, by rfl⟩ : syracuseStep 4448837 = 834157) (by norm_num)
theorem B2343509 : Blo 1561478 2343509 := bbase (se 8 (by rfl) ⟨13731, by rfl⟩ : syracuseStep 2343509 = 27463) (by norm_num)
theorem B2343533 : Blo 1561478 2343533 := bbase (se 3 (by rfl) ⟨439412, by rfl⟩ : syracuseStep 2343533 = 878825) (by norm_num)
theorem B1876613 : Blo 1561478 1876613 := bbase (se 4 (by rfl) ⟨175932, by rfl⟩ : syracuseStep 1876613 = 351865) (by norm_num)
theorem B2343557 : Blo 1561478 2343557 := bbase (se 4 (by rfl) ⟨219708, by rfl⟩ : syracuseStep 2343557 = 439417) (by norm_num)
theorem B2966149 : Blo 1561478 2966149 := bbase (se 4 (by rfl) ⟨278076, by rfl⟩ : syracuseStep 2966149 = 556153) (by norm_num)
theorem B3515021 : Blo 1561478 3515021 := bbase (se 3 (by rfl) ⟨659066, by rfl⟩ : syracuseStep 3515021 = 1318133) (by norm_num)
theorem B2343581 : Blo 1561478 2343581 := bbase (se 3 (by rfl) ⟨439421, by rfl⟩ : syracuseStep 2343581 = 878843) (by norm_num)
theorem B2343605 : Blo 1561478 2343605 := bbase (se 5 (by rfl) ⟨109856, by rfl⟩ : syracuseStep 2343605 = 219713) (by norm_num)
theorem B3957437 : Blo 1561478 3957437 := bbase (se 3 (by rfl) ⟨742019, by rfl⟩ : syracuseStep 3957437 = 1484039) (by norm_num)
theorem B2343629 : Blo 1561478 2343629 := bbase (se 3 (by rfl) ⟨439430, by rfl⟩ : syracuseStep 2343629 = 878861) (by norm_num)
theorem B3515093 : Blo 1561478 3515093 := bbase (se 7 (by rfl) ⟨41192, by rfl⟩ : syracuseStep 3515093 = 82385) (by norm_num)
theorem B2343653 : Blo 1561478 2343653 := bbase (se 4 (by rfl) ⟨219717, by rfl⟩ : syracuseStep 2343653 = 439435) (by norm_num)
theorem B11862773 : Blo 1561478 11862773 := bbase (se 5 (by rfl) ⟨556067, by rfl⟩ : syracuseStep 11862773 = 1112135) (by norm_num)
theorem B2343677 : Blo 1561478 2343677 := bbase (se 3 (by rfl) ⟨439439, by rfl⟩ : syracuseStep 2343677 = 878879) (by norm_num)
theorem B7504645 : Blo 1561478 7504645 := bbase (se 4 (by rfl) ⟨703560, by rfl⟩ : syracuseStep 7504645 = 1407121) (by norm_num)
theorem B2671373 : Blo 1561478 2671373 := bbase (se 3 (by rfl) ⟨500882, by rfl⟩ : syracuseStep 2671373 = 1001765) (by norm_num)
theorem B2343701 : Blo 1561478 2343701 := bbase (se 6 (by rfl) ⟨54930, by rfl⟩ : syracuseStep 2343701 = 109861) (by norm_num)
theorem B3515165 : Blo 1561478 3515165 := bbase (se 3 (by rfl) ⟨659093, by rfl⟩ : syracuseStep 3515165 = 1318187) (by norm_num)
theorem B7906085 : Blo 1561478 7906085 := bbase (se 4 (by rfl) ⟨741195, by rfl⟩ : syracuseStep 7906085 = 1482391) (by norm_num)
theorem B2343725 : Blo 1561478 2343725 := bbase (se 3 (by rfl) ⟨439448, by rfl⟩ : syracuseStep 2343725 = 878897) (by norm_num)
theorem B4449077 : Blo 1561478 4449077 := bbase (se 5 (by rfl) ⟨208550, by rfl⟩ : syracuseStep 4449077 = 417101) (by norm_num)
theorem B2343749 : Blo 1561478 2343749 := bbase (se 4 (by rfl) ⟨219726, by rfl⟩ : syracuseStep 2343749 = 439453) (by norm_num)
theorem B15008597 : Blo 1561478 15008597 := bbase (se 9 (by rfl) ⟨43970, by rfl⟩ : syracuseStep 15008597 = 87941) (by norm_num)
theorem B5276501 : Blo 1561478 5276501 := bbase (se 9 (by rfl) ⟨15458, by rfl⟩ : syracuseStep 5276501 = 30917) (by norm_num)
theorem B2343773 : Blo 1561478 2343773 := bbase (se 3 (by rfl) ⟨439457, by rfl⟩ : syracuseStep 2343773 = 878915) (by norm_num)
theorem B3515237 : Blo 1561478 3515237 := bbase (se 4 (by rfl) ⟨329553, by rfl⟩ : syracuseStep 3515237 = 659107) (by norm_num)
theorem B2343797 : Blo 1561478 2343797 := bbase (se 5 (by rfl) ⟨109865, by rfl⟩ : syracuseStep 2343797 = 219731) (by norm_num)
theorem B2343821 : Blo 1561478 2343821 := bbase (se 3 (by rfl) ⟨439466, by rfl⟩ : syracuseStep 2343821 = 878933) (by norm_num)
theorem B2343845 : Blo 1561478 2343845 := bbase (se 4 (by rfl) ⟨219735, by rfl⟩ : syracuseStep 2343845 = 439471) (by norm_num)
theorem B3515309 : Blo 1561478 3515309 := bbase (se 3 (by rfl) ⟨659120, by rfl⟩ : syracuseStep 3515309 = 1318241) (by norm_num)
theorem B2966453 : Blo 1561478 2966453 := bbase (se 5 (by rfl) ⟨139052, by rfl⟩ : syracuseStep 2966453 = 278105) (by norm_num)
theorem B2343869 : Blo 1561478 2343869 := bbase (se 3 (by rfl) ⟨439475, by rfl⟩ : syracuseStep 2343869 = 878951) (by norm_num)
theorem B2343893 : Blo 1561478 2343893 := bbase (se 7 (by rfl) ⟨27467, by rfl⟩ : syracuseStep 2343893 = 54935) (by norm_num)
theorem B3335141 : Blo 1561478 3335141 := bbase (se 4 (by rfl) ⟨312669, by rfl⟩ : syracuseStep 3335141 = 625339) (by norm_num)
theorem B2343917 : Blo 1561478 2343917 := bbase (se 3 (by rfl) ⟨439484, by rfl⟩ : syracuseStep 2343917 = 878969) (by norm_num)
theorem B3515381 : Blo 1561478 3515381 := bbase (se 5 (by rfl) ⟨164783, by rfl⟩ : syracuseStep 3515381 = 329567) (by norm_num)
theorem B4449269 : Blo 1561478 4449269 := bbase (se 5 (by rfl) ⟨208559, by rfl⟩ : syracuseStep 4449269 = 417119) (by norm_num)
theorem B2343941 : Blo 1561478 2343941 := bbase (se 4 (by rfl) ⟨219744, by rfl⟩ : syracuseStep 2343941 = 439489) (by norm_num)
theorem B2343965 : Blo 1561478 2343965 := bbase (se 3 (by rfl) ⟨439493, by rfl⟩ : syracuseStep 2343965 = 878987) (by norm_num)
theorem B12665909 : Blo 1561478 12665909 := bbase (se 5 (by rfl) ⟨593714, by rfl⟩ : syracuseStep 12665909 = 1187429) (by norm_num)
theorem B2343989 : Blo 1561478 2343989 := bbase (se 5 (by rfl) ⟨109874, by rfl⟩ : syracuseStep 2343989 = 219749) (by norm_num)
theorem B3515453 : Blo 1561478 3515453 := bbase (se 3 (by rfl) ⟨659147, by rfl⟩ : syracuseStep 3515453 = 1318295) (by norm_num)
theorem B2344013 : Blo 1561478 2344013 := bbase (se 3 (by rfl) ⟨439502, by rfl⟩ : syracuseStep 2344013 = 879005) (by norm_num)
theorem B2344037 : Blo 1561478 2344037 := bbase (se 4 (by rfl) ⟨219753, by rfl⟩ : syracuseStep 2344037 = 439507) (by norm_num)
theorem B5006453 : Blo 1561478 5006453 := bbase (se 5 (by rfl) ⟨234677, by rfl⟩ : syracuseStep 5006453 = 469355) (by norm_num)
theorem B2344061 : Blo 1561478 2344061 := bbase (se 3 (by rfl) ⟨439511, by rfl⟩ : syracuseStep 2344061 = 879023) (by norm_num)
theorem B3515525 : Blo 1561478 3515525 := bbase (se 4 (by rfl) ⟨329580, by rfl⟩ : syracuseStep 3515525 = 659161) (by norm_num)
theorem B2344085 : Blo 1561478 2344085 := bbase (se 6 (by rfl) ⟨54939, by rfl⟩ : syracuseStep 2344085 = 109879) (by norm_num)
theorem B2344109 : Blo 1561478 2344109 := bbase (se 3 (by rfl) ⟨439520, by rfl⟩ : syracuseStep 2344109 = 879041) (by norm_num)
theorem B2344133 : Blo 1561478 2344133 := bbase (se 4 (by rfl) ⟨219762, by rfl⟩ : syracuseStep 2344133 = 439525) (by norm_num)
theorem B3515597 : Blo 1561478 3515597 := bbase (se 3 (by rfl) ⟨659174, by rfl⟩ : syracuseStep 3515597 = 1318349) (by norm_num)
theorem B2344157 : Blo 1561478 2344157 := bbase (se 3 (by rfl) ⟨439529, by rfl⟩ : syracuseStep 2344157 = 879059) (by norm_num)
theorem B2344181 : Blo 1561478 2344181 := bbase (se 5 (by rfl) ⟨109883, by rfl⟩ : syracuseStep 2344181 = 219767) (by norm_num)
theorem B2344205 : Blo 1561478 2344205 := bbase (se 3 (by rfl) ⟨439538, by rfl⟩ : syracuseStep 2344205 = 879077) (by norm_num)
theorem B3515669 : Blo 1561478 3515669 := bbase (se 6 (by rfl) ⟨82398, by rfl⟩ : syracuseStep 3515669 = 164797) (by norm_num)
theorem B2344229 : Blo 1561478 2344229 := bbase (se 4 (by rfl) ⟨219771, by rfl⟩ : syracuseStep 2344229 = 439543) (by norm_num)
theorem B1877305 : Blo 1561478 1877305 := bbase (se 2 (by rfl) ⟨703989, by rfl⟩ : syracuseStep 1877305 = 1407979) (by norm_num)
theorem B2344253 : Blo 1561478 2344253 := bbase (se 3 (by rfl) ⟨439547, by rfl⟩ : syracuseStep 2344253 = 879095) (by norm_num)
theorem B2671949 : Blo 1561478 2671949 := bbase (se 3 (by rfl) ⟨500990, by rfl⟩ : syracuseStep 2671949 = 1001981) (by norm_num)
theorem B3335509 : Blo 1561478 3335509 := bbase (se 12 (by rfl) ⟨1221, by rfl⟩ : syracuseStep 3335509 = 2443) (by norm_num)
theorem B2344277 : Blo 1561478 2344277 := bbase (se 12 (by rfl) ⟨858, by rfl⟩ : syracuseStep 2344277 = 1717) (by norm_num)
theorem B3515741 : Blo 1561478 3515741 := bbase (se 3 (by rfl) ⟨659201, by rfl⟩ : syracuseStep 3515741 = 1318403) (by norm_num)
theorem B2344301 : Blo 1561478 2344301 := bbase (se 3 (by rfl) ⟨439556, by rfl⟩ : syracuseStep 2344301 = 879113) (by norm_num)
theorem B2344325 : Blo 1561478 2344325 := bbase (se 4 (by rfl) ⟨219780, by rfl⟩ : syracuseStep 2344325 = 439561) (by norm_num)
theorem B1877401 : Blo 1561478 1877401 := bbase (se 2 (by rfl) ⟨704025, by rfl⟩ : syracuseStep 1877401 = 1408051) (by norm_num)
theorem B2344349 : Blo 1561478 2344349 := bbase (se 3 (by rfl) ⟨439565, by rfl⟩ : syracuseStep 2344349 = 879131) (by norm_num)
theorem B3515813 : Blo 1561478 3515813 := bbase (se 4 (by rfl) ⟨329607, by rfl⟩ : syracuseStep 3515813 = 659215) (by norm_num)
theorem B2344373 : Blo 1561478 2344373 := bbase (se 5 (by rfl) ⟨109892, by rfl⟩ : syracuseStep 2344373 = 219785) (by norm_num)
theorem B2344397 : Blo 1561478 2344397 := bbase (se 3 (by rfl) ⟨439574, by rfl⟩ : syracuseStep 2344397 = 879149) (by norm_num)
theorem B2344421 : Blo 1561478 2344421 := bbase (se 4 (by rfl) ⟨219789, by rfl⟩ : syracuseStep 2344421 = 439579) (by norm_num)
theorem B3515885 : Blo 1561478 3515885 := bbase (se 3 (by rfl) ⟨659228, by rfl⟩ : syracuseStep 3515885 = 1318457) (by norm_num)
theorem B2344445 : Blo 1561478 2344445 := bbase (se 3 (by rfl) ⟨439583, by rfl⟩ : syracuseStep 2344445 = 879167) (by norm_num)
theorem B2344469 : Blo 1561478 2344469 := bbase (se 6 (by rfl) ⟨54948, by rfl⟩ : syracuseStep 2344469 = 109897) (by norm_num)
theorem B2344493 : Blo 1561478 2344493 := bbase (se 3 (by rfl) ⟨439592, by rfl⟩ : syracuseStep 2344493 = 879185) (by norm_num)
theorem B5629493 : Blo 1561478 5629493 := bbase (se 5 (by rfl) ⟨263882, by rfl⟩ : syracuseStep 5629493 = 527765) (by norm_num)
theorem B3515957 : Blo 1561478 3515957 := bbase (se 5 (by rfl) ⟨164810, by rfl⟩ : syracuseStep 3515957 = 329621) (by norm_num)
theorem B2344517 : Blo 1561478 2344517 := bbase (se 4 (by rfl) ⟨219798, by rfl⟩ : syracuseStep 2344517 = 439597) (by norm_num)
theorem B2344541 : Blo 1561478 2344541 := bbase (se 3 (by rfl) ⟨439601, by rfl⟩ : syracuseStep 2344541 = 879203) (by norm_num)
theorem B2344565 : Blo 1561478 2344565 := bbase (se 5 (by rfl) ⟨109901, by rfl⟩ : syracuseStep 2344565 = 219803) (by norm_num)
theorem B3516029 : Blo 1561478 3516029 := bbase (se 3 (by rfl) ⟨659255, by rfl⟩ : syracuseStep 3516029 = 1318511) (by norm_num)
theorem B2344589 : Blo 1561478 2344589 := bbase (se 3 (by rfl) ⟨439610, by rfl⟩ : syracuseStep 2344589 = 879221) (by norm_num)
theorem B5932709 : Blo 1561478 5932709 := bbase (se 4 (by rfl) ⟨556191, by rfl⟩ : syracuseStep 5932709 = 1112383) (by norm_num)
theorem B2967205 : Blo 1561478 2967205 := bbase (se 4 (by rfl) ⟨278175, by rfl⟩ : syracuseStep 2967205 = 556351) (by norm_num)
theorem B2344613 : Blo 1561478 2344613 := bbase (se 4 (by rfl) ⟨219807, by rfl⟩ : syracuseStep 2344613 = 439615) (by norm_num)
theorem B2344637 : Blo 1561478 2344637 := bbase (se 3 (by rfl) ⟨439619, by rfl⟩ : syracuseStep 2344637 = 879239) (by norm_num)
theorem B3516101 : Blo 1561478 3516101 := bbase (se 4 (by rfl) ⟨329634, by rfl⟩ : syracuseStep 3516101 = 659269) (by norm_num)
theorem B2344661 : Blo 1561478 2344661 := bbase (se 7 (by rfl) ⟨27476, by rfl⟩ : syracuseStep 2344661 = 54953) (by norm_num)
theorem B2344685 : Blo 1561478 2344685 := bbase (se 3 (by rfl) ⟨439628, by rfl⟩ : syracuseStep 2344685 = 879257) (by norm_num)
theorem B2344709 : Blo 1561478 2344709 := bbase (se 4 (by rfl) ⟨219816, by rfl⟩ : syracuseStep 2344709 = 439633) (by norm_num)
theorem B3516173 : Blo 1561478 3516173 := bbase (se 3 (by rfl) ⟨659282, by rfl⟩ : syracuseStep 3516173 = 1318565) (by norm_num)
theorem B2344733 : Blo 1561478 2344733 := bbase (se 3 (by rfl) ⟨439637, by rfl⟩ : syracuseStep 2344733 = 879275) (by norm_num)
theorem B2967349 : Blo 1561478 2967349 := bbase (se 5 (by rfl) ⟨139094, by rfl⟩ : syracuseStep 2967349 = 278189) (by norm_num)
theorem B2344757 : Blo 1561478 2344757 := bbase (se 5 (by rfl) ⟨109910, by rfl⟩ : syracuseStep 2344757 = 219821) (by norm_num)
theorem B1713997 : Blo 1561478 1713997 := bbase (se 3 (by rfl) ⟨321374, by rfl⟩ : syracuseStep 1713997 = 642749) (by norm_num)
theorem B2344781 : Blo 1561478 2344781 := bbase (se 3 (by rfl) ⟨439646, by rfl⟩ : syracuseStep 2344781 = 879293) (by norm_num)
theorem B3516245 : Blo 1561478 3516245 := bbase (se 9 (by rfl) ⟨10301, by rfl⟩ : syracuseStep 3516245 = 20603) (by norm_num)
theorem B2344805 : Blo 1561478 2344805 := bbase (se 4 (by rfl) ⟨219825, by rfl⟩ : syracuseStep 2344805 = 439651) (by norm_num)
theorem B2344829 : Blo 1561478 2344829 := bbase (se 3 (by rfl) ⟨439655, by rfl⟩ : syracuseStep 2344829 = 879311) (by norm_num)
theorem B16893845 : Blo 1561478 16893845 := bbase (se 6 (by rfl) ⟨395949, by rfl⟩ : syracuseStep 16893845 = 791899) (by norm_num)
theorem B2344853 : Blo 1561478 2344853 := bbase (se 6 (by rfl) ⟨54957, by rfl⟩ : syracuseStep 2344853 = 109915) (by norm_num)
theorem B3008405 : Blo 1561478 3008405 := bbase (se 6 (by rfl) ⟨70509, by rfl⟩ : syracuseStep 3008405 = 141019) (by norm_num)
theorem B3516317 : Blo 1561478 3516317 := bbase (se 3 (by rfl) ⟨659309, by rfl⟩ : syracuseStep 3516317 = 1318619) (by norm_num)
theorem B2344877 : Blo 1561478 2344877 := bbase (se 3 (by rfl) ⟨439664, by rfl⟩ : syracuseStep 2344877 = 879329) (by norm_num)
theorem B5932997 : Blo 1561478 5932997 := bbase (se 4 (by rfl) ⟨556218, by rfl⟩ : syracuseStep 5932997 = 1112437) (by norm_num)
theorem B2344901 : Blo 1561478 2344901 := bbase (se 4 (by rfl) ⟨219834, by rfl⟩ : syracuseStep 2344901 = 439669) (by norm_num)
theorem B4450261 : Blo 1561478 4450261 := bbase (se 7 (by rfl) ⟨52151, by rfl⟩ : syracuseStep 4450261 = 104303) (by norm_num)
theorem B2967509 : Blo 1561478 2967509 := bbase (se 7 (by rfl) ⟨34775, by rfl⟩ : syracuseStep 2967509 = 69551) (by norm_num)
theorem B2344925 : Blo 1561478 2344925 := bbase (se 3 (by rfl) ⟨439673, by rfl⟩ : syracuseStep 2344925 = 879347) (by norm_num)
theorem B3516389 : Blo 1561478 3516389 := bbase (se 4 (by rfl) ⟨329661, by rfl⟩ : syracuseStep 3516389 = 659323) (by norm_num)
theorem B2344949 : Blo 1561478 2344949 := bbase (se 5 (by rfl) ⟨109919, by rfl⟩ : syracuseStep 2344949 = 219839) (by norm_num)
theorem B1583101 : Blo 1561478 1583101 := bbase (se 3 (by rfl) ⟨296831, by rfl⟩ : syracuseStep 1583101 = 593663) (by norm_num)
theorem B2672645 : Blo 1561478 2672645 := bbase (se 4 (by rfl) ⟨250560, by rfl⟩ : syracuseStep 2672645 = 501121) (by norm_num)
theorem B5007365 : Blo 1561478 5007365 := bbase (se 4 (by rfl) ⟨469440, by rfl⟩ : syracuseStep 5007365 = 938881) (by norm_num)
theorem B1976329 : Blo 1561478 1976329 := bbase (se 2 (by rfl) ⟨741123, by rfl⟩ : syracuseStep 1976329 = 1482247) (by norm_num)
theorem B2344973 : Blo 1561478 2344973 := bbase (se 3 (by rfl) ⟨439682, by rfl⟩ : syracuseStep 2344973 = 879365) (by norm_num)
theorem B2344997 : Blo 1561478 2344997 := bbase (se 4 (by rfl) ⟨219843, by rfl⟩ : syracuseStep 2344997 = 439687) (by norm_num)
theorem B3516461 : Blo 1561478 3516461 := bbase (se 3 (by rfl) ⟨659336, by rfl⟩ : syracuseStep 3516461 = 1318673) (by norm_num)
theorem B7907381 : Blo 1561478 7907381 := bbase (se 5 (by rfl) ⟨370658, by rfl⟩ : syracuseStep 7907381 = 741317) (by norm_num)
theorem B2345021 : Blo 1561478 2345021 := bbase (se 3 (by rfl) ⟨439691, by rfl⟩ : syracuseStep 2345021 = 879383) (by norm_num)
theorem B2345045 : Blo 1561478 2345045 := bbase (se 8 (by rfl) ⟨13740, by rfl⟩ : syracuseStep 2345045 = 27481) (by norm_num)
theorem B2967653 : Blo 1561478 2967653 := bbase (se 4 (by rfl) ⟨278217, by rfl⟩ : syracuseStep 2967653 = 556435) (by norm_num)
theorem B2345069 : Blo 1561478 2345069 := bbase (se 3 (by rfl) ⟨439700, by rfl⟩ : syracuseStep 2345069 = 879401) (by norm_num)
theorem B3516533 : Blo 1561478 3516533 := bbase (se 5 (by rfl) ⟨164837, by rfl⟩ : syracuseStep 3516533 = 329675) (by norm_num)
theorem B2345093 : Blo 1561478 2345093 := bbase (se 4 (by rfl) ⟨219852, by rfl⟩ : syracuseStep 2345093 = 439705) (by norm_num)
theorem B2672797 : Blo 1561478 2672797 := bbase (se 3 (by rfl) ⟨501149, by rfl⟩ : syracuseStep 2672797 = 1002299) (by norm_num)
theorem B2345117 : Blo 1561478 2345117 := bbase (se 3 (by rfl) ⟨439709, by rfl⟩ : syracuseStep 2345117 = 879419) (by norm_num)
theorem B1878185 : Blo 1561478 1878185 := bbase (se 2 (by rfl) ⟨704319, by rfl⟩ : syracuseStep 1878185 = 1408639) (by norm_num)
theorem B1976501 : Blo 1561478 1976501 := bbase (se 5 (by rfl) ⟨92648, by rfl⟩ : syracuseStep 1976501 = 185297) (by norm_num)
theorem B13355189 : Blo 1561478 13355189 := bbase (se 5 (by rfl) ⟨626024, by rfl⟩ : syracuseStep 13355189 = 1252049) (by norm_num)
theorem B2345141 : Blo 1561478 2345141 := bbase (se 5 (by rfl) ⟨109928, by rfl⟩ : syracuseStep 2345141 = 219857) (by norm_num)
theorem B3516605 : Blo 1561478 3516605 := bbase (se 3 (by rfl) ⟨659363, by rfl⟩ : syracuseStep 3516605 = 1318727) (by norm_num)
theorem B2345165 : Blo 1561478 2345165 := bbase (se 3 (by rfl) ⟨439718, by rfl⟩ : syracuseStep 2345165 = 879437) (by norm_num)
theorem B2345189 : Blo 1561478 2345189 := bbase (se 4 (by rfl) ⟨219861, by rfl⟩ : syracuseStep 2345189 = 439723) (by norm_num)
theorem B1976557 : Blo 1561478 1976557 := bbase (se 3 (by rfl) ⟨370604, by rfl⟩ : syracuseStep 1976557 = 741209) (by norm_num)
theorem B2345213 : Blo 1561478 2345213 := bbase (se 3 (by rfl) ⟨439727, by rfl⟩ : syracuseStep 2345213 = 879455) (by norm_num)
theorem B3516677 : Blo 1561478 3516677 := bbase (se 4 (by rfl) ⟨329688, by rfl⟩ : syracuseStep 3516677 = 659377) (by norm_num)
theorem B13347125 : Blo 1561478 13347125 := bbase (se 5 (by rfl) ⟨625646, by rfl⟩ : syracuseStep 13347125 = 1251293) (by norm_num)
theorem B1583425 : Blo 1561478 1583425 := bbase (se 2 (by rfl) ⟨593784, by rfl⟩ : syracuseStep 1583425 = 1187569) (by norm_num)
theorem B1976653 : Blo 1561478 1976653 := bbase (se 3 (by rfl) ⟨370622, by rfl⟩ : syracuseStep 1976653 = 741245) (by norm_num)
theorem B3516749 : Blo 1561478 3516749 := bbase (se 3 (by rfl) ⟨659390, by rfl⟩ : syracuseStep 3516749 = 1318781) (by norm_num)
theorem B2967941 : Blo 1561478 2967941 := bbase (se 4 (by rfl) ⟨278244, by rfl⟩ : syracuseStep 2967941 = 556489) (by norm_num)
theorem B3516821 : Blo 1561478 3516821 := bbase (se 6 (by rfl) ⟨82425, by rfl⟩ : syracuseStep 3516821 = 164851) (by norm_num)
theorem B3516893 : Blo 1561478 3516893 := bbase (se 3 (by rfl) ⟨659417, by rfl⟩ : syracuseStep 3516893 = 1318835) (by norm_num)
theorem B1976825 : Blo 1561478 1976825 := bbase (se 2 (by rfl) ⟨741309, by rfl⟩ : syracuseStep 1976825 = 1482619) (by norm_num)
theorem B5270021 : Blo 1561478 5270021 := bbase (se 4 (by rfl) ⟨494064, by rfl⟩ : syracuseStep 5270021 = 988129) (by norm_num)
theorem B17132053 : Blo 1561478 17132053 := bbase (se 6 (by rfl) ⟨401532, by rfl⟩ : syracuseStep 17132053 = 803065) (by norm_num)
theorem B3754525 : Blo 1561478 3754525 := bbase (se 3 (by rfl) ⟨703973, by rfl⟩ : syracuseStep 3754525 = 1407947) (by norm_num)
theorem B2968093 : Blo 1561478 2968093 := bbase (se 3 (by rfl) ⟨556517, by rfl⟩ : syracuseStep 2968093 = 1113035) (by norm_num)
theorem B3516965 : Blo 1561478 3516965 := bbase (se 4 (by rfl) ⟨329715, by rfl⟩ : syracuseStep 3516965 = 659431) (by norm_num)
theorem B1976881 : Blo 1561478 1976881 := bbase (se 2 (by rfl) ⟨741330, by rfl⟩ : syracuseStep 1976881 = 1482661) (by norm_num)
theorem B3517037 : Blo 1561478 3517037 := bbase (se 3 (by rfl) ⟨659444, by rfl⟩ : syracuseStep 3517037 = 1318889) (by norm_num)
theorem B1976977 : Blo 1561478 1976977 := bbase (se 2 (by rfl) ⟨741366, by rfl⟩ : syracuseStep 1976977 = 1482733) (by norm_num)
theorem B3517109 : Blo 1561478 3517109 := bbase (se 5 (by rfl) ⟨164864, by rfl⟩ : syracuseStep 3517109 = 329729) (by norm_num)
theorem B3517181 : Blo 1561478 3517181 := bbase (se 3 (by rfl) ⟨659471, by rfl⟩ : syracuseStep 3517181 = 1318943) (by norm_num)
theorem B2255629 : Blo 1561478 2255629 := bbase (se 3 (by rfl) ⟨422930, by rfl⟩ : syracuseStep 2255629 = 845861) (by norm_num)
theorem B3337013 : Blo 1561478 3337013 := bbase (se 5 (by rfl) ⟨156422, by rfl⟩ : syracuseStep 3337013 = 312845) (by norm_num)
theorem B1977149 : Blo 1561478 1977149 := bbase (se 3 (by rfl) ⟨370715, by rfl⟩ : syracuseStep 1977149 = 741431) (by norm_num)
theorem B3517253 : Blo 1561478 3517253 := bbase (se 4 (by rfl) ⟨329742, by rfl⟩ : syracuseStep 3517253 = 659485) (by norm_num)
theorem B1977205 : Blo 1561478 1977205 := bbase (se 5 (by rfl) ⟨92681, by rfl⟩ : syracuseStep 1977205 = 185363) (by norm_num)
theorem B1583993 : Blo 1561478 1583993 := bbase (se 2 (by rfl) ⟨593997, by rfl⟩ : syracuseStep 1583993 = 1187995) (by norm_num)
theorem B3517325 : Blo 1561478 3517325 := bbase (se 3 (by rfl) ⟨659498, by rfl⟩ : syracuseStep 3517325 = 1318997) (by norm_num)
theorem B5270453 : Blo 1561478 5270453 := bbase (se 5 (by rfl) ⟨247052, by rfl⟩ : syracuseStep 5270453 = 494105) (by norm_num)
theorem B3337157 : Blo 1561478 3337157 := bbase (se 4 (by rfl) ⟨312858, by rfl⟩ : syracuseStep 3337157 = 625717) (by norm_num)
theorem B1977301 : Blo 1561478 1977301 := bbase (se 7 (by rfl) ⟨23171, by rfl⟩ : syracuseStep 1977301 = 46343) (by norm_num)
theorem B8899541 : Blo 1561478 8899541 := bbase (se 7 (by rfl) ⟨104291, by rfl⟩ : syracuseStep 8899541 = 208583) (by norm_num)
theorem B3517397 : Blo 1561478 3517397 := bbase (se 7 (by rfl) ⟨41219, by rfl⟩ : syracuseStep 3517397 = 82439) (by norm_num)
theorem B3517469 : Blo 1561478 3517469 := bbase (se 3 (by rfl) ⟨659525, by rfl⟩ : syracuseStep 3517469 = 1319051) (by norm_num)
theorem B4451365 : Blo 1561478 4451365 := bbase (se 4 (by rfl) ⟨417315, by rfl⟩ : syracuseStep 4451365 = 834631) (by norm_num)
theorem B6671429 : Blo 1561478 6671429 := bbase (se 4 (by rfl) ⟨625446, by rfl⟩ : syracuseStep 6671429 = 1250893) (by norm_num)
theorem B5934181 : Blo 1561478 5934181 := bbase (se 4 (by rfl) ⟨556329, by rfl⟩ : syracuseStep 5934181 = 1112659) (by norm_num)
theorem B3517541 : Blo 1561478 3517541 := bbase (se 4 (by rfl) ⟨329769, by rfl⟩ : syracuseStep 3517541 = 659539) (by norm_num)
theorem B2501741 : Blo 1561478 2501741 := bbase (se 3 (by rfl) ⟨469076, by rfl⟩ : syracuseStep 2501741 = 938153) (by norm_num)
theorem B1977473 : Blo 1561478 1977473 := bbase (se 2 (by rfl) ⟨741552, by rfl⟩ : syracuseStep 1977473 = 1483105) (by norm_num)
theorem B3517613 : Blo 1561478 3517613 := bbase (se 3 (by rfl) ⟨659552, by rfl⟩ : syracuseStep 3517613 = 1319105) (by norm_num)
theorem B1977529 : Blo 1561478 1977529 := bbase (se 2 (by rfl) ⟨741573, by rfl⟩ : syracuseStep 1977529 = 1483147) (by norm_num)
theorem B2223325 : Blo 1561478 2223325 := bbase (se 3 (by rfl) ⟨416873, by rfl⟩ : syracuseStep 2223325 = 833747) (by norm_num)
theorem B2501869 : Blo 1561478 2501869 := bbase (se 3 (by rfl) ⟨469100, by rfl⟩ : syracuseStep 2501869 = 938201) (by norm_num)
theorem B3517685 : Blo 1561478 3517685 := bbase (se 5 (by rfl) ⟨164891, by rfl⟩ : syracuseStep 3517685 = 329783) (by norm_num)
theorem B1977625 : Blo 1561478 1977625 := bbase (se 2 (by rfl) ⟨741609, by rfl⟩ : syracuseStep 1977625 = 1483219) (by norm_num)
theorem B3337517 : Blo 1561478 3337517 := bbase (se 3 (by rfl) ⟨625784, by rfl⟩ : syracuseStep 3337517 = 1251569) (by norm_num)
theorem B3517757 : Blo 1561478 3517757 := bbase (se 3 (by rfl) ⟨659579, by rfl⟩ : syracuseStep 3517757 = 1319159) (by norm_num)
theorem B7908677 : Blo 1561478 7908677 := bbase (se 4 (by rfl) ⟨741438, by rfl⟩ : syracuseStep 7908677 = 1482877) (by norm_num)
theorem B5008709 : Blo 1561478 5008709 := bbase (se 4 (by rfl) ⟨469566, by rfl⟩ : syracuseStep 5008709 = 939133) (by norm_num)
theorem B2223445 : Blo 1561478 2223445 := bbase (se 11 (by rfl) ⟨1628, by rfl⟩ : syracuseStep 2223445 = 3257) (by norm_num)
theorem B5270885 : Blo 1561478 5270885 := bbase (se 4 (by rfl) ⟨494145, by rfl⟩ : syracuseStep 5270885 = 988291) (by norm_num)
theorem B6671717 : Blo 1561478 6671717 := bbase (se 4 (by rfl) ⟨625473, by rfl⟩ : syracuseStep 6671717 = 1250947) (by norm_num)
theorem B8449429 : Blo 1561478 8449429 := bbase (se 6 (by rfl) ⟨198033, by rfl⟩ : syracuseStep 8449429 = 396067) (by norm_num)
theorem B5934485 : Blo 1561478 5934485 := bbase (se 6 (by rfl) ⟨139089, by rfl⟩ : syracuseStep 5934485 = 278179) (by norm_num)
theorem B2223541 : Blo 1561478 2223541 := bbase (se 5 (by rfl) ⟨104228, by rfl⟩ : syracuseStep 2223541 = 208457) (by norm_num)
theorem B1584569 : Blo 1561478 1584569 := bbase (se 2 (by rfl) ⟨594213, by rfl⟩ : syracuseStep 1584569 = 1188427) (by norm_num)
theorem B1977797 : Blo 1561478 1977797 := bbase (se 4 (by rfl) ⟨185418, by rfl⟩ : syracuseStep 1977797 = 370837) (by norm_num)
theorem B1756669 : Blo 1561478 1756669 := bbase (se 3 (by rfl) ⟨329375, by rfl⟩ : syracuseStep 1756669 = 658751) (by norm_num)
theorem B1977853 : Blo 1561478 1977853 := bbase (se 3 (by rfl) ⟨370847, by rfl⟩ : syracuseStep 1977853 = 741695) (by norm_num)
theorem B1756705 : Blo 1561478 1756705 := bbase (se 2 (by rfl) ⟨658764, by rfl⟩ : syracuseStep 1756705 = 1317529) (by norm_num)
theorem B1756741 : Blo 1561478 1756741 := bbase (se 4 (by rfl) ⟨164694, by rfl⟩ : syracuseStep 1756741 = 329389) (by norm_num)
theorem B1977949 : Blo 1561478 1977949 := bbase (se 3 (by rfl) ⟨370865, by rfl⟩ : syracuseStep 1977949 = 741731) (by norm_num)
theorem B1756777 : Blo 1561478 1756777 := bbase (se 2 (by rfl) ⟨658791, by rfl⟩ : syracuseStep 1756777 = 1317583) (by norm_num)
theorem B2502253 : Blo 1561478 2502253 := bbase (se 3 (by rfl) ⟨469172, by rfl⟩ : syracuseStep 2502253 = 938345) (by norm_num)
theorem B1756813 : Blo 1561478 1756813 := bbase (se 3 (by rfl) ⟨329402, by rfl⟩ : syracuseStep 1756813 = 658805) (by norm_num)
theorem B6336149 : Blo 1561478 6336149 := bbase (se 6 (by rfl) ⟨148503, by rfl⟩ : syracuseStep 6336149 = 297007) (by norm_num)
theorem B3165869 : Blo 1561478 3165869 := bbase (se 3 (by rfl) ⟨593600, by rfl⟩ : syracuseStep 3165869 = 1187201) (by norm_num)
theorem B1756849 : Blo 1561478 1756849 := bbase (se 2 (by rfl) ⟨658818, by rfl⟩ : syracuseStep 1756849 = 1317637) (by norm_num)
theorem B1756885 : Blo 1561478 1756885 := bbase (se 7 (by rfl) ⟨20588, by rfl⟩ : syracuseStep 1756885 = 41177) (by norm_num)
theorem B1756921 : Blo 1561478 1756921 := bbase (se 2 (by rfl) ⟨658845, by rfl⟩ : syracuseStep 1756921 = 1317691) (by norm_num)
theorem B1978121 : Blo 1561478 1978121 := bbase (se 2 (by rfl) ⟨741795, by rfl⟩ : syracuseStep 1978121 = 1483591) (by norm_num)
theorem B5271317 : Blo 1561478 5271317 := bbase (se 6 (by rfl) ⟨123546, by rfl⟩ : syracuseStep 5271317 = 247093) (by norm_num)
theorem B1756957 : Blo 1561478 1756957 := bbase (se 3 (by rfl) ⟨329429, by rfl⟩ : syracuseStep 1756957 = 658859) (by norm_num)
theorem B1756993 : Blo 1561478 1756993 := bbase (se 2 (by rfl) ⟨658872, by rfl⟩ : syracuseStep 1756993 = 1317745) (by norm_num)
theorem B1978177 : Blo 1561478 1978177 := bbase (se 2 (by rfl) ⟨741816, by rfl⟩ : syracuseStep 1978177 = 1483633) (by norm_num)
theorem B1757029 : Blo 1561478 1757029 := bbase (se 4 (by rfl) ⟨164721, by rfl⟩ : syracuseStep 1757029 = 329443) (by norm_num)
theorem B2502509 : Blo 1561478 2502509 := bbase (se 3 (by rfl) ⟨469220, by rfl⟩ : syracuseStep 2502509 = 938441) (by norm_num)
theorem B1757065 : Blo 1561478 1757065 := bbase (se 2 (by rfl) ⟨658899, by rfl⟩ : syracuseStep 1757065 = 1317799) (by norm_num)
theorem B1978273 : Blo 1561478 1978273 := bbase (se 2 (by rfl) ⟨741852, by rfl⟩ : syracuseStep 1978273 = 1483705) (by norm_num)
theorem B2224037 : Blo 1561478 2224037 := bbase (se 4 (by rfl) ⟨208503, by rfl⟩ : syracuseStep 2224037 = 417007) (by norm_num)
theorem B1691561 : Blo 1561478 1691561 := bbase (se 2 (by rfl) ⟨634335, by rfl⟩ : syracuseStep 1691561 = 1268671) (by norm_num)
theorem B1757101 : Blo 1561478 1757101 := bbase (se 3 (by rfl) ⟨329456, by rfl⟩ : syracuseStep 1757101 = 658913) (by norm_num)
theorem B1781677 : Blo 1561478 1781677 := bbase (se 3 (by rfl) ⟨334064, by rfl⟩ : syracuseStep 1781677 = 668129) (by norm_num)
theorem B1757137 : Blo 1561478 1757137 := bbase (se 2 (by rfl) ⟨658926, by rfl⟩ : syracuseStep 1757137 = 1317853) (by norm_num)
theorem B3952597 : Blo 1561478 3952597 := bbase (se 7 (by rfl) ⟨46319, by rfl⟩ : syracuseStep 3952597 = 92639) (by norm_num)
theorem B1757173 : Blo 1561478 1757173 := bbase (se 5 (by rfl) ⟨82367, by rfl⟩ : syracuseStep 1757173 = 164735) (by norm_num)
theorem B1757209 : Blo 1561478 1757209 := bbase (se 2 (by rfl) ⟨658953, by rfl⟩ : syracuseStep 1757209 = 1317907) (by norm_num)
theorem B4223029 : Blo 1561478 4223029 := bbase (se 5 (by rfl) ⟨197954, by rfl⟩ : syracuseStep 4223029 = 395909) (by norm_num)
theorem B1757245 : Blo 1561478 1757245 := bbase (se 3 (by rfl) ⟨329483, by rfl⟩ : syracuseStep 1757245 = 658967) (by norm_num)
theorem B3952709 : Blo 1561478 3952709 := bbase (se 4 (by rfl) ⟨370566, by rfl⟩ : syracuseStep 3952709 = 741133) (by norm_num)
theorem B1978445 : Blo 1561478 1978445 := bbase (se 3 (by rfl) ⟨370958, by rfl⟩ : syracuseStep 1978445 = 741917) (by norm_num)
theorem B2535509 : Blo 1561478 2535509 := bbase (se 8 (by rfl) ⟨14856, by rfl⟩ : syracuseStep 2535509 = 29713) (by norm_num)
theorem B6672469 : Blo 1561478 6672469 := bbase (se 8 (by rfl) ⟨39096, by rfl⟩ : syracuseStep 6672469 = 78193) (by norm_num)
theorem B1757281 : Blo 1561478 1757281 := bbase (se 2 (by rfl) ⟨658980, by rfl⟩ : syracuseStep 1757281 = 1317961) (by norm_num)
theorem B8900725 : Blo 1561478 8900725 := bbase (se 5 (by rfl) ⟨417221, by rfl⟩ : syracuseStep 8900725 = 834443) (by norm_num)
theorem B1757317 : Blo 1561478 1757317 := bbase (se 4 (by rfl) ⟨164748, by rfl⟩ : syracuseStep 1757317 = 329497) (by norm_num)
theorem B1978501 : Blo 1561478 1978501 := bbase (se 4 (by rfl) ⟨185484, by rfl⟩ : syracuseStep 1978501 = 370969) (by norm_num)
theorem B3338405 : Blo 1561478 3338405 := bbase (se 4 (by rfl) ⟨312975, by rfl⟩ : syracuseStep 3338405 = 625951) (by norm_num)
theorem B1757353 : Blo 1561478 1757353 := bbase (se 2 (by rfl) ⟨659007, by rfl⟩ : syracuseStep 1757353 = 1318015) (by norm_num)
theorem B5271749 : Blo 1561478 5271749 := bbase (se 4 (by rfl) ⟨494226, by rfl⟩ : syracuseStep 5271749 = 988453) (by norm_num)
theorem B1757389 : Blo 1561478 1757389 := bbase (se 3 (by rfl) ⟨329510, by rfl⟩ : syracuseStep 1757389 = 659021) (by norm_num)
theorem B1978597 : Blo 1561478 1978597 := bbase (se 4 (by rfl) ⟨185493, by rfl⟩ : syracuseStep 1978597 = 370987) (by norm_num)
theorem B1757425 : Blo 1561478 1757425 := bbase (se 2 (by rfl) ⟨659034, by rfl⟩ : syracuseStep 1757425 = 1318069) (by norm_num)
theorem B3952901 : Blo 1561478 3952901 := bbase (se 4 (by rfl) ⟨370584, by rfl⟩ : syracuseStep 3952901 = 741169) (by norm_num)
theorem B7131397 : Blo 1561478 7131397 := bbase (se 4 (by rfl) ⟨668568, by rfl⟩ : syracuseStep 7131397 = 1337137) (by norm_num)
theorem B2814221 : Blo 1561478 2814221 := bbase (se 3 (by rfl) ⟨527666, by rfl⟩ : syracuseStep 2814221 = 1055333) (by norm_num)
theorem B12022037 : Blo 1561478 12022037 := bbase (se 6 (by rfl) ⟨281766, by rfl⟩ : syracuseStep 12022037 = 563533) (by norm_num)
theorem B1757461 : Blo 1561478 1757461 := bbase (se 6 (by rfl) ⟨41190, by rfl⟩ : syracuseStep 1757461 = 82381) (by norm_num)
theorem B2855197 : Blo 1561478 2855197 := bbase (se 3 (by rfl) ⟨535349, by rfl⟩ : syracuseStep 2855197 = 1070699) (by norm_num)
theorem B1757497 : Blo 1561478 1757497 := bbase (se 2 (by rfl) ⟨659061, by rfl⟩ : syracuseStep 1757497 = 1318123) (by norm_num)
theorem B1757533 : Blo 1561478 1757533 := bbase (se 3 (by rfl) ⟨329537, by rfl⟩ : syracuseStep 1757533 = 659075) (by norm_num)
theorem B1757569 : Blo 1561478 1757569 := bbase (se 2 (by rfl) ⟨659088, by rfl⟩ : syracuseStep 1757569 = 1318177) (by norm_num)
theorem B1978769 : Blo 1561478 1978769 := bbase (se 2 (by rfl) ⟨742038, by rfl⟩ : syracuseStep 1978769 = 1484077) (by norm_num)
theorem B15020437 : Blo 1561478 15020437 := bbase (se 6 (by rfl) ⟨352041, by rfl⟩ : syracuseStep 15020437 = 704083) (by norm_num)
theorem B1667485 : Blo 1561478 1667485 := bbase (se 3 (by rfl) ⟨312653, by rfl⟩ : syracuseStep 1667485 = 625307) (by norm_num)
theorem B3338653 : Blo 1561478 3338653 := bbase (se 3 (by rfl) ⟨625997, by rfl⟩ : syracuseStep 3338653 = 1251995) (by norm_num)
theorem B1757605 : Blo 1561478 1757605 := bbase (se 4 (by rfl) ⟨164775, by rfl⟩ : syracuseStep 1757605 = 329551) (by norm_num)
theorem B1757641 : Blo 1561478 1757641 := bbase (se 2 (by rfl) ⟨659115, by rfl⟩ : syracuseStep 1757641 = 1318231) (by norm_num)
theorem B2224589 : Blo 1561478 2224589 := bbase (se 3 (by rfl) ⟨417110, by rfl⟩ : syracuseStep 2224589 = 834221) (by norm_num)
theorem B1782229 : Blo 1561478 1782229 := bbase (se 7 (by rfl) ⟨20885, by rfl⟩ : syracuseStep 1782229 = 41771) (by norm_num)
theorem B1757677 : Blo 1561478 1757677 := bbase (se 3 (by rfl) ⟨329564, by rfl⟩ : syracuseStep 1757677 = 659129) (by norm_num)
theorem B2535925 : Blo 1561478 2535925 := bbase (se 5 (by rfl) ⟨118871, by rfl⟩ : syracuseStep 2535925 = 237743) (by norm_num)
theorem B1757713 : Blo 1561478 1757713 := bbase (se 2 (by rfl) ⟨659142, by rfl⟩ : syracuseStep 1757713 = 1318285) (by norm_num)
theorem B1757749 : Blo 1561478 1757749 := bbase (se 5 (by rfl) ⟨82394, by rfl⟩ : syracuseStep 1757749 = 164789) (by norm_num)
theorem B1667665 : Blo 1561478 1667665 := bbase (se 2 (by rfl) ⟨625374, by rfl⟩ : syracuseStep 1667665 = 1250749) (by norm_num)
theorem B7909973 : Blo 1561478 7909973 := bbase (se 8 (by rfl) ⟨46347, by rfl⟩ : syracuseStep 7909973 = 92695) (by norm_num)
theorem B1757785 : Blo 1561478 1757785 := bbase (se 2 (by rfl) ⟨659169, by rfl⟩ : syracuseStep 1757785 = 1318339) (by norm_num)
theorem B3953245 : Blo 1561478 3953245 := bbase (se 3 (by rfl) ⟨741233, by rfl⟩ : syracuseStep 3953245 = 1482467) (by norm_num)
theorem B5272181 : Blo 1561478 5272181 := bbase (se 5 (by rfl) ⟨247133, by rfl⟩ : syracuseStep 5272181 = 494267) (by norm_num)
theorem B5345909 : Blo 1561478 5345909 := bbase (se 5 (by rfl) ⟨250589, by rfl⟩ : syracuseStep 5345909 = 501179) (by norm_num)
theorem B1757821 : Blo 1561478 1757821 := bbase (se 3 (by rfl) ⟨329591, by rfl⟩ : syracuseStep 1757821 = 659183) (by norm_num)
theorem B1757857 : Blo 1561478 1757857 := bbase (se 2 (by rfl) ⟨659196, by rfl⟩ : syracuseStep 1757857 = 1318393) (by norm_num)
theorem B7508645 : Blo 1561478 7508645 := bbase (se 4 (by rfl) ⟨703935, by rfl⟩ : syracuseStep 7508645 = 1407871) (by norm_num)
theorem B1757893 : Blo 1561478 1757893 := bbase (se 4 (by rfl) ⟨164802, by rfl⟩ : syracuseStep 1757893 = 329605) (by norm_num)
theorem B3953357 : Blo 1561478 3953357 := bbase (se 3 (by rfl) ⟨741254, by rfl⟩ : syracuseStep 3953357 = 1482509) (by norm_num)
theorem B2503381 : Blo 1561478 2503381 := bbase (se 7 (by rfl) ⟨29336, by rfl⟩ : syracuseStep 2503381 = 58673) (by norm_num)
theorem B1757929 : Blo 1561478 1757929 := bbase (se 2 (by rfl) ⟨659223, by rfl⟩ : syracuseStep 1757929 = 1318447) (by norm_num)
theorem B1757965 : Blo 1561478 1757965 := bbase (se 3 (by rfl) ⟨329618, by rfl⟩ : syracuseStep 1757965 = 659237) (by norm_num)
theorem B4223765 : Blo 1561478 4223765 := bbase (se 6 (by rfl) ⟨98994, by rfl⟩ : syracuseStep 4223765 = 197989) (by norm_num)
theorem B1758001 : Blo 1561478 1758001 := bbase (se 2 (by rfl) ⟨659250, by rfl⟩ : syracuseStep 1758001 = 1318501) (by norm_num)
theorem B6673205 : Blo 1561478 6673205 := bbase (se 5 (by rfl) ⟨312806, by rfl⟩ : syracuseStep 6673205 = 625613) (by norm_num)
theorem B2503477 : Blo 1561478 2503477 := bbase (se 5 (by rfl) ⟨117350, by rfl⟩ : syracuseStep 2503477 = 234701) (by norm_num)
theorem B1758037 : Blo 1561478 1758037 := bbase (se 9 (by rfl) ⟨5150, by rfl⟩ : syracuseStep 1758037 = 10301) (by norm_num)
theorem B12678005 : Blo 1561478 12678005 := bbase (se 5 (by rfl) ⟨594281, by rfl⟩ : syracuseStep 12678005 = 1188563) (by norm_num)
theorem B1758073 : Blo 1561478 1758073 := bbase (se 2 (by rfl) ⟨659277, by rfl⟩ : syracuseStep 1758073 = 1318555) (by norm_num)
theorem B1782649 : Blo 1561478 1782649 := bbase (se 2 (by rfl) ⟨668493, by rfl⟩ : syracuseStep 1782649 = 1336987) (by norm_num)
theorem B3953549 : Blo 1561478 3953549 := bbase (se 3 (by rfl) ⟨741290, by rfl⟩ : syracuseStep 3953549 = 1482581) (by norm_num)
theorem B3339157 : Blo 1561478 3339157 := bbase (se 6 (by rfl) ⟨78261, by rfl⟩ : syracuseStep 3339157 = 156523) (by norm_num)
theorem B1758109 : Blo 1561478 1758109 := bbase (se 3 (by rfl) ⟨329645, by rfl⟩ : syracuseStep 1758109 = 659291) (by norm_num)
theorem B1758145 : Blo 1561478 1758145 := bbase (se 2 (by rfl) ⟨659304, by rfl⟩ : syracuseStep 1758145 = 1318609) (by norm_num)
theorem B2503637 : Blo 1561478 2503637 := bbase (se 7 (by rfl) ⟨29339, by rfl⟩ : syracuseStep 2503637 = 58679) (by norm_num)
theorem B1758181 : Blo 1561478 1758181 := bbase (se 4 (by rfl) ⟨164829, by rfl⟩ : syracuseStep 1758181 = 329659) (by norm_num)
theorem B1758217 : Blo 1561478 1758217 := bbase (se 2 (by rfl) ⟨659331, by rfl⟩ : syracuseStep 1758217 = 1318663) (by norm_num)
theorem B1668109 : Blo 1561478 1668109 := bbase (se 3 (by rfl) ⟨312770, by rfl⟩ : syracuseStep 1668109 = 625541) (by norm_num)
theorem B5272613 : Blo 1561478 5272613 := bbase (se 4 (by rfl) ⟨494307, by rfl⟩ : syracuseStep 5272613 = 988615) (by norm_num)
theorem B1758253 : Blo 1561478 1758253 := bbase (se 3 (by rfl) ⟨329672, by rfl⟩ : syracuseStep 1758253 = 659345) (by norm_num)
theorem B1758289 : Blo 1561478 1758289 := bbase (se 2 (by rfl) ⟨659358, by rfl⟩ : syracuseStep 1758289 = 1318717) (by norm_num)
theorem B1758325 : Blo 1561478 1758325 := bbase (se 5 (by rfl) ⟨82421, by rfl⟩ : syracuseStep 1758325 = 164843) (by norm_num)
theorem B1668233 : Blo 1561478 1668233 := bbase (se 2 (by rfl) ⟨625587, by rfl⟩ : syracuseStep 1668233 = 1251175) (by norm_num)
theorem B1758361 : Blo 1561478 1758361 := bbase (se 2 (by rfl) ⟨659385, by rfl⟩ : syracuseStep 1758361 = 1318771) (by norm_num)
theorem B2815165 : Blo 1561478 2815165 := bbase (se 3 (by rfl) ⟨527843, by rfl⟩ : syracuseStep 2815165 = 1055687) (by norm_num)
theorem B2225341 : Blo 1561478 2225341 := bbase (se 3 (by rfl) ⟨417251, by rfl⟩ : syracuseStep 2225341 = 834503) (by norm_num)
theorem B1758397 : Blo 1561478 1758397 := bbase (se 3 (by rfl) ⟨329699, by rfl⟩ : syracuseStep 1758397 = 659399) (by norm_num)
theorem B5944517 : Blo 1561478 5944517 := bbase (se 4 (by rfl) ⟨557298, by rfl⟩ : syracuseStep 5944517 = 1114597) (by norm_num)
theorem B1758433 : Blo 1561478 1758433 := bbase (se 2 (by rfl) ⟨659412, by rfl⟩ : syracuseStep 1758433 = 1318825) (by norm_num)
theorem B2110693 : Blo 1561478 2110693 := bbase (se 4 (by rfl) ⟨197877, by rfl⟩ : syracuseStep 2110693 = 395755) (by norm_num)
theorem B3953893 : Blo 1561478 3953893 := bbase (se 4 (by rfl) ⟨370677, by rfl⟩ : syracuseStep 3953893 = 741355) (by norm_num)
theorem B2634997 : Blo 1561478 2634997 := bbase (se 5 (by rfl) ⟨123515, by rfl⟩ : syracuseStep 2634997 = 247031) (by norm_num)
theorem B6419717 : Blo 1561478 6419717 := bbase (se 4 (by rfl) ⟨601848, by rfl⟩ : syracuseStep 6419717 = 1203697) (by norm_num)
theorem B1758469 : Blo 1561478 1758469 := bbase (se 4 (by rfl) ⟨164856, by rfl⟩ : syracuseStep 1758469 = 329713) (by norm_num)
theorem B2110757 : Blo 1561478 2110757 := bbase (se 4 (by rfl) ⟨197883, by rfl⟩ : syracuseStep 2110757 = 395767) (by norm_num)
theorem B1758505 : Blo 1561478 1758505 := bbase (se 2 (by rfl) ⟨659439, by rfl⟩ : syracuseStep 1758505 = 1318879) (by norm_num)
theorem B2635085 : Blo 1561478 2635085 := bbase (se 3 (by rfl) ⟨494078, by rfl⟩ : syracuseStep 2635085 = 988157) (by norm_num)
theorem B1758541 : Blo 1561478 1758541 := bbase (se 3 (by rfl) ⟨329726, by rfl⟩ : syracuseStep 1758541 = 659453) (by norm_num)
theorem B3954005 : Blo 1561478 3954005 := bbase (se 16 (by rfl) ⟨90, by rfl⟩ : syracuseStep 3954005 = 181) (by norm_num)
theorem B1758577 : Blo 1561478 1758577 := bbase (se 2 (by rfl) ⟨659466, by rfl⟩ : syracuseStep 1758577 = 1318933) (by norm_num)
theorem B16258421 : Blo 1561478 16258421 := bbase (se 5 (by rfl) ⟨762113, by rfl⟩ : syracuseStep 16258421 = 1524227) (by norm_num)
theorem B1668485 : Blo 1561478 1668485 := bbase (se 4 (by rfl) ⟨156420, by rfl⟩ : syracuseStep 1668485 = 312841) (by norm_num)
theorem B1758613 : Blo 1561478 1758613 := bbase (se 6 (by rfl) ⟨41217, by rfl⟩ : syracuseStep 1758613 = 82435) (by norm_num)
theorem B5002661 : Blo 1561478 5002661 := bbase (se 4 (by rfl) ⟨468999, by rfl⟩ : syracuseStep 5002661 = 937999) (by norm_num)
theorem B1758649 : Blo 1561478 1758649 := bbase (se 2 (by rfl) ⟨659493, by rfl⟩ : syracuseStep 1758649 = 1318987) (by norm_num)
theorem B2635213 : Blo 1561478 2635213 := bbase (se 3 (by rfl) ⟨494102, by rfl⟩ : syracuseStep 2635213 = 988205) (by norm_num)
theorem B2110925 : Blo 1561478 2110925 := bbase (se 3 (by rfl) ⟨395798, by rfl⟩ : syracuseStep 2110925 = 791597) (by norm_num)
theorem B5273045 : Blo 1561478 5273045 := bbase (se 7 (by rfl) ⟨61793, by rfl⟩ : syracuseStep 5273045 = 123587) (by norm_num)
theorem B1758685 : Blo 1561478 1758685 := bbase (se 3 (by rfl) ⟨329753, by rfl⟩ : syracuseStep 1758685 = 659507) (by norm_num)
theorem B1758721 : Blo 1561478 1758721 := bbase (se 2 (by rfl) ⟨659520, by rfl⟩ : syracuseStep 1758721 = 1319041) (by norm_num)
theorem B3954197 : Blo 1561478 3954197 := bbase (se 6 (by rfl) ⟨92676, by rfl⟩ : syracuseStep 3954197 = 185353) (by norm_num)
theorem B22533653 : Blo 1561478 22533653 := bbase (se 6 (by rfl) ⟨528132, by rfl⟩ : syracuseStep 22533653 = 1056265) (by norm_num)
theorem B2635301 : Blo 1561478 2635301 := bbase (se 4 (by rfl) ⟨247059, by rfl⟩ : syracuseStep 2635301 = 494119) (by norm_num)
theorem B1758757 : Blo 1561478 1758757 := bbase (se 4 (by rfl) ⟨164883, by rfl⟩ : syracuseStep 1758757 = 329767) (by norm_num)
theorem B1758793 : Blo 1561478 1758793 := bbase (se 2 (by rfl) ⟨659547, by rfl⟩ : syracuseStep 1758793 = 1319095) (by norm_num)
theorem B1758829 : Blo 1561478 1758829 := bbase (se 3 (by rfl) ⟨329780, by rfl⟩ : syracuseStep 1758829 = 659561) (by norm_num)
theorem B1758865 : Blo 1561478 1758865 := bbase (se 2 (by rfl) ⟨659574, by rfl⟩ : syracuseStep 1758865 = 1319149) (by norm_num)
theorem B2635429 : Blo 1561478 2635429 := bbase (se 4 (by rfl) ⟨247071, by rfl⟩ : syracuseStep 2635429 = 494143) (by norm_num)
theorem B2815669 : Blo 1561478 2815669 := bbase (se 5 (by rfl) ⟨131984, by rfl⟩ : syracuseStep 2815669 = 263969) (by norm_num)
theorem B1758901 : Blo 1561478 1758901 := bbase (se 5 (by rfl) ⟨82448, by rfl⟩ : syracuseStep 1758901 = 164897) (by norm_num)
theorem B2537173 : Blo 1561478 2537173 := bbase (se 7 (by rfl) ⟨29732, by rfl⟩ : syracuseStep 2537173 = 59465) (by norm_num)
theorem B2635517 : Blo 1561478 2635517 := bbase (se 3 (by rfl) ⟨494159, by rfl⟩ : syracuseStep 2635517 = 988319) (by norm_num)
theorem B3807005 : Blo 1561478 3807005 := bbase (se 3 (by rfl) ⟨713813, by rfl⟩ : syracuseStep 3807005 = 1427627) (by norm_num)
theorem B1668929 : Blo 1561478 1668929 := bbase (se 2 (by rfl) ⟨625848, by rfl⟩ : syracuseStep 1668929 = 1251697) (by norm_num)
theorem B10016597 : Blo 1561478 10016597 := bbase (se 9 (by rfl) ⟨29345, by rfl⟩ : syracuseStep 10016597 = 58691) (by norm_num)
theorem B7911269 : Blo 1561478 7911269 := bbase (se 4 (by rfl) ⟨741681, by rfl⟩ : syracuseStep 7911269 = 1483363) (by norm_num)
theorem B3954541 : Blo 1561478 3954541 := bbase (se 3 (by rfl) ⟨741476, by rfl⟩ : syracuseStep 3954541 = 1482953) (by norm_num)
theorem B5928821 : Blo 1561478 5928821 := bbase (se 5 (by rfl) ⟨277913, by rfl⟩ : syracuseStep 5928821 = 555827) (by norm_num)
theorem B9025397 : Blo 1561478 9025397 := bbase (se 5 (by rfl) ⟨423065, by rfl⟩ : syracuseStep 9025397 = 846131) (by norm_num)
theorem B2635645 : Blo 1561478 2635645 := bbase (se 3 (by rfl) ⟨494183, by rfl⟩ : syracuseStep 2635645 = 988367) (by norm_num)
theorem B5273477 : Blo 1561478 5273477 := bbase (se 4 (by rfl) ⟨494388, by rfl⟩ : syracuseStep 5273477 = 988777) (by norm_num)
theorem B2635733 : Blo 1561478 2635733 := bbase (se 7 (by rfl) ⟨30887, by rfl⟩ : syracuseStep 2635733 = 61775) (by norm_num)
theorem B3954653 : Blo 1561478 3954653 := bbase (se 3 (by rfl) ⟨741497, by rfl⟩ : syracuseStep 3954653 = 1482995) (by norm_num)
theorem B3168229 : Blo 1561478 3168229 := bbase (se 4 (by rfl) ⟨297021, by rfl⟩ : syracuseStep 3168229 = 594043) (by norm_num)
theorem B6764581 : Blo 1561478 6764581 := bbase (se 4 (by rfl) ⟨634179, by rfl⟩ : syracuseStep 6764581 = 1268359) (by norm_num)
theorem B8902709 : Blo 1561478 8902709 := bbase (se 5 (by rfl) ⟨417314, by rfl⟩ : syracuseStep 8902709 = 834629) (by norm_num)
theorem B1669177 : Blo 1561478 1669177 := bbase (se 2 (by rfl) ⟨625941, by rfl⟩ : syracuseStep 1669177 = 1251883) (by norm_num)
theorem B2635861 : Blo 1561478 2635861 := bbase (se 8 (by rfl) ⟨15444, by rfl⟩ : syracuseStep 2635861 = 30889) (by norm_num)
theorem B5929109 : Blo 1561478 5929109 := bbase (se 6 (by rfl) ⟨138963, by rfl⟩ : syracuseStep 5929109 = 277927) (by norm_num)
theorem B3954845 : Blo 1561478 3954845 := bbase (se 3 (by rfl) ⟨741533, by rfl⟩ : syracuseStep 3954845 = 1483067) (by norm_num)
theorem B2635949 : Blo 1561478 2635949 := bbase (se 3 (by rfl) ⟨494240, by rfl⟩ : syracuseStep 2635949 = 988481) (by norm_num)
theorem B45037781 : Blo 1561478 45037781 := bbase (se 7 (by rfl) ⟨527786, by rfl⟩ : syracuseStep 45037781 = 1055573) (by norm_num)
theorem B2636077 : Blo 1561478 2636077 := bbase (se 3 (by rfl) ⟨494264, by rfl⟩ : syracuseStep 2636077 = 988529) (by norm_num)
theorem B5273909 : Blo 1561478 5273909 := bbase (se 5 (by rfl) ⟨247214, by rfl⟩ : syracuseStep 5273909 = 494429) (by norm_num)
theorem B2636165 : Blo 1561478 2636165 := bbase (se 4 (by rfl) ⟨247140, by rfl⟩ : syracuseStep 2636165 = 494281) (by norm_num)
theorem B3955189 : Blo 1561478 3955189 := bbase (se 5 (by rfl) ⟨185399, by rfl⟩ : syracuseStep 3955189 = 370799) (by norm_num)
theorem B2636293 : Blo 1561478 2636293 := bbase (se 4 (by rfl) ⟨247152, by rfl⟩ : syracuseStep 2636293 = 494305) (by norm_num)
theorem B2816549 : Blo 1561478 2816549 := bbase (se 4 (by rfl) ⟨264051, by rfl⟩ : syracuseStep 2816549 = 528103) (by norm_num)
theorem B3562069 : Blo 1561478 3562069 := bbase (se 8 (by rfl) ⟨20871, by rfl⟩ : syracuseStep 3562069 = 41743) (by norm_num)
theorem B2636381 : Blo 1561478 2636381 := bbase (se 3 (by rfl) ⟨494321, by rfl⟩ : syracuseStep 2636381 = 988643) (by norm_num)
theorem B3955301 : Blo 1561478 3955301 := bbase (se 4 (by rfl) ⟨370809, by rfl⟩ : syracuseStep 3955301 = 741619) (by norm_num)
theorem B2374261 : Blo 1561478 2374261 := bbase (se 5 (by rfl) ⟨111293, by rfl⟩ : syracuseStep 2374261 = 222587) (by norm_num)
theorem B3168893 : Blo 1561478 3168893 := bbase (se 3 (by rfl) ⟨594167, by rfl⟩ : syracuseStep 3168893 = 1188335) (by norm_num)
theorem B2636509 : Blo 1561478 2636509 := bbase (se 3 (by rfl) ⟨494345, by rfl⟩ : syracuseStep 2636509 = 988691) (by norm_num)
theorem B5274341 : Blo 1561478 5274341 := bbase (se 4 (by rfl) ⟨494469, by rfl⟩ : syracuseStep 5274341 = 988939) (by norm_num)
theorem B3955493 : Blo 1561478 3955493 := bbase (se 4 (by rfl) ⟨370827, by rfl⟩ : syracuseStep 3955493 = 741655) (by norm_num)
theorem B2636597 : Blo 1561478 2636597 := bbase (se 5 (by rfl) ⟨123590, by rfl⟩ : syracuseStep 2636597 = 247181) (by norm_num)
theorem B4225861 : Blo 1561478 4225861 := bbase (se 4 (by rfl) ⟨396174, by rfl⟩ : syracuseStep 4225861 = 792349) (by norm_num)
theorem B4225925 : Blo 1561478 4225925 := bbase (se 4 (by rfl) ⟨396180, by rfl⟩ : syracuseStep 4225925 = 792361) (by norm_num)
theorem B2636725 : Blo 1561478 2636725 := bbase (se 5 (by rfl) ⟨123596, by rfl⟩ : syracuseStep 2636725 = 247193) (by norm_num)
theorem B2636813 : Blo 1561478 2636813 := bbase (se 3 (by rfl) ⟨494402, by rfl⟩ : syracuseStep 2636813 = 988805) (by norm_num)
theorem B3513365 : Blo 1561478 3513365 := bbase (se 6 (by rfl) ⟨82344, by rfl⟩ : syracuseStep 3513365 = 164689) (by norm_num)
theorem B2964509 : Blo 1561478 2964509 := bbase (se 3 (by rfl) ⟨555845, by rfl⟩ : syracuseStep 2964509 = 1111691) (by norm_num)
theorem B2817053 : Blo 1561478 2817053 := bbase (se 3 (by rfl) ⟨528197, by rfl⟩ : syracuseStep 2817053 = 1056395) (by norm_num)
theorem B3513437 : Blo 1561478 3513437 := bbase (se 3 (by rfl) ⟨658769, by rfl⟩ : syracuseStep 3513437 = 1317539) (by norm_num)
theorem B7912565 : Blo 1561478 7912565 := bbase (se 5 (by rfl) ⟨370901, by rfl⟩ : syracuseStep 7912565 = 741803) (by norm_num)
theorem B3955837 : Blo 1561478 3955837 := bbase (se 3 (by rfl) ⟨741719, by rfl⟩ : syracuseStep 3955837 = 1483439) (by norm_num)
theorem B2636941 : Blo 1561478 2636941 := bbase (se 3 (by rfl) ⟨494426, by rfl⟩ : syracuseStep 2636941 = 988853) (by norm_num)
theorem B5274773 : Blo 1561478 5274773 := bbase (se 6 (by rfl) ⟨123627, by rfl⟩ : syracuseStep 5274773 = 247255) (by norm_num)
theorem B3513509 : Blo 1561478 3513509 := bbase (se 4 (by rfl) ⟨329391, by rfl⟩ : syracuseStep 3513509 = 658783) (by norm_num)
theorem B2170037 : Blo 1561478 2170037 := bbase (se 5 (by rfl) ⟨101720, by rfl⟩ : syracuseStep 2170037 = 203441) (by norm_num)
theorem B2637029 : Blo 1561478 2637029 := bbase (se 4 (by rfl) ⟨247221, by rfl⟩ : syracuseStep 2637029 = 494443) (by norm_num)
theorem B3513581 : Blo 1561478 3513581 := bbase (se 3 (by rfl) ⟨658796, by rfl⟩ : syracuseStep 3513581 = 1317593) (by norm_num)
theorem B3955949 : Blo 1561478 3955949 := bbase (se 3 (by rfl) ⟨741740, by rfl⟩ : syracuseStep 3955949 = 1483481) (by norm_num)
theorem B4447493 : Blo 1561478 4447493 := bbase (se 4 (by rfl) ⟨416952, by rfl⟩ : syracuseStep 4447493 = 833905) (by norm_num)
theorem B3513653 : Blo 1561478 3513653 := bbase (se 5 (by rfl) ⟨164702, by rfl⟩ : syracuseStep 3513653 = 329405) (by norm_num)
theorem B5930293 : Blo 1561478 5930293 := bbase (se 5 (by rfl) ⟨277982, by rfl⟩ : syracuseStep 5930293 = 555965) (by norm_num)
theorem B2342237 : Blo 1561478 2342237 := bbase (se 3 (by rfl) ⟨439169, by rfl⟩ : syracuseStep 2342237 = 878339) (by norm_num)
theorem B2637157 : Blo 1561478 2637157 := bbase (se 4 (by rfl) ⟨247233, by rfl⟩ : syracuseStep 2637157 = 494467) (by norm_num)
theorem B2342261 : Blo 1561478 2342261 := bbase (se 5 (by rfl) ⟨109793, by rfl⟩ : syracuseStep 2342261 = 219587) (by norm_num)
theorem B3513725 : Blo 1561478 3513725 := bbase (se 3 (by rfl) ⟨658823, by rfl⟩ : syracuseStep 3513725 = 1317647) (by norm_num)
theorem B2342285 : Blo 1561478 2342285 := bbase (se 3 (by rfl) ⟨439178, by rfl⟩ : syracuseStep 2342285 = 878357) (by norm_num)
theorem B2342309 : Blo 1561478 2342309 := bbase (se 4 (by rfl) ⟨219591, by rfl⟩ : syracuseStep 2342309 = 439183) (by norm_num)
theorem B5709221 : Blo 1561478 5709221 := bbase (se 4 (by rfl) ⟨535239, by rfl⟩ : syracuseStep 5709221 = 1070479) (by norm_num)
theorem B3956141 : Blo 1561478 3956141 := bbase (se 3 (by rfl) ⟨741776, by rfl⟩ : syracuseStep 3956141 = 1483553) (by norm_num)
theorem B2342333 : Blo 1561478 2342333 := bbase (se 3 (by rfl) ⟨439187, by rfl⟩ : syracuseStep 2342333 = 878375) (by norm_num)
theorem B2637245 : Blo 1561478 2637245 := bbase (se 3 (by rfl) ⟨494483, by rfl⟩ : syracuseStep 2637245 = 988967) (by norm_num)
theorem B3513797 : Blo 1561478 3513797 := bbase (se 4 (by rfl) ⟨329418, by rfl⟩ : syracuseStep 3513797 = 658837) (by norm_num)
theorem B2342357 : Blo 1561478 2342357 := bbase (se 7 (by rfl) ⟨27449, by rfl⟩ : syracuseStep 2342357 = 54899) (by norm_num)
theorem B2342381 : Blo 1561478 2342381 := bbase (se 3 (by rfl) ⟨439196, by rfl⟩ : syracuseStep 2342381 = 878393) (by norm_num)
theorem B2342405 : Blo 1561478 2342405 := bbase (se 4 (by rfl) ⟨219600, by rfl⟩ : syracuseStep 2342405 = 439201) (by norm_num)
theorem B3513869 : Blo 1561478 3513869 := bbase (se 3 (by rfl) ⟨658850, by rfl⟩ : syracuseStep 3513869 = 1317701) (by norm_num)
theorem B2342429 : Blo 1561478 2342429 := bbase (se 3 (by rfl) ⟨439205, by rfl⟩ : syracuseStep 2342429 = 878411) (by norm_num)
theorem B2342453 : Blo 1561478 2342453 := bbase (se 5 (by rfl) ⟨109802, by rfl⟩ : syracuseStep 2342453 = 219605) (by norm_num)
theorem B2637373 : Blo 1561478 2637373 := bbase (se 3 (by rfl) ⟨494507, by rfl⟩ : syracuseStep 2637373 = 989015) (by norm_num)
theorem B5275205 : Blo 1561478 5275205 := bbase (se 4 (by rfl) ⟨494550, by rfl⟩ : syracuseStep 5275205 = 989101) (by norm_num)
theorem B2342477 : Blo 1561478 2342477 := bbase (se 3 (by rfl) ⟨439214, by rfl⟩ : syracuseStep 2342477 = 878429) (by norm_num)
theorem B3513941 : Blo 1561478 3513941 := bbase (se 8 (by rfl) ⟨20589, by rfl⟩ : syracuseStep 3513941 = 41179) (by norm_num)
theorem B2342501 : Blo 1561478 2342501 := bbase (se 4 (by rfl) ⟨219609, by rfl⟩ : syracuseStep 2342501 = 439219) (by norm_num)
theorem B5930597 : Blo 1561478 5930597 := bbase (se 4 (by rfl) ⟨555993, by rfl⟩ : syracuseStep 5930597 = 1111987) (by norm_num)
theorem B2342525 : Blo 1561478 2342525 := bbase (se 3 (by rfl) ⟨439223, by rfl⟩ : syracuseStep 2342525 = 878447) (by norm_num)
theorem B2342549 : Blo 1561478 2342549 := bbase (se 6 (by rfl) ⟨54903, by rfl⟩ : syracuseStep 2342549 = 109807) (by norm_num)
theorem B2637461 : Blo 1561478 2637461 := bbase (se 6 (by rfl) ⟨61815, by rfl⟩ : syracuseStep 2637461 = 123631) (by norm_num)
theorem B3514013 : Blo 1561478 3514013 := bbase (se 3 (by rfl) ⟨658877, by rfl⟩ : syracuseStep 3514013 = 1317755) (by norm_num)
theorem B2342573 : Blo 1561478 2342573 := bbase (se 3 (by rfl) ⟨439232, by rfl⟩ : syracuseStep 2342573 = 878465) (by norm_num)
theorem B2342597 : Blo 1561478 2342597 := bbase (se 4 (by rfl) ⟨219618, by rfl⟩ : syracuseStep 2342597 = 439237) (by norm_num)
theorem B60866261 : Blo 1561478 60866261 := bbase (se 7 (by rfl) ⟨713276, by rfl⟩ : syracuseStep 60866261 = 1426553) (by norm_num)
theorem B2342621 : Blo 1561478 2342621 := bbase (se 3 (by rfl) ⟨439241, by rfl⟩ : syracuseStep 2342621 = 878483) (by norm_num)
theorem B3514085 : Blo 1561478 3514085 := bbase (se 4 (by rfl) ⟨329445, by rfl⟩ : syracuseStep 3514085 = 658891) (by norm_num)
theorem B3047141 : Blo 1561478 3047141 := bbase (se 4 (by rfl) ⟨285669, by rfl⟩ : syracuseStep 3047141 = 571339) (by norm_num)
theorem B2342645 : Blo 1561478 2342645 := bbase (se 5 (by rfl) ⟨109811, by rfl⟩ : syracuseStep 2342645 = 219623) (by norm_num)
theorem B3956485 : Blo 1561478 3956485 := bbase (se 4 (by rfl) ⟨370920, by rfl⟩ : syracuseStep 3956485 = 741841) (by norm_num)
theorem B2342669 : Blo 1561478 2342669 := bbase (se 3 (by rfl) ⟨439250, by rfl⟩ : syracuseStep 2342669 = 878501) (by norm_num)
theorem B2965261 : Blo 1561478 2965261 := bbase (se 3 (by rfl) ⟨555986, by rfl⟩ : syracuseStep 2965261 = 1111973) (by norm_num)
theorem B2637589 : Blo 1561478 2637589 := bbase (se 6 (by rfl) ⟨61818, by rfl⟩ : syracuseStep 2637589 = 123637) (by norm_num)
theorem B2342693 : Blo 1561478 2342693 := bbase (se 4 (by rfl) ⟨219627, by rfl⟩ : syracuseStep 2342693 = 439255) (by norm_num)
theorem B3514157 : Blo 1561478 3514157 := bbase (se 3 (by rfl) ⟨658904, by rfl⟩ : syracuseStep 3514157 = 1317809) (by norm_num)
theorem B2342717 : Blo 1561478 2342717 := bbase (se 3 (by rfl) ⟨439259, by rfl⟩ : syracuseStep 2342717 = 878519) (by norm_num)
theorem B2342741 : Blo 1561478 2342741 := bbase (se 9 (by rfl) ⟨6863, by rfl⟩ : syracuseStep 2342741 = 13727) (by norm_num)
theorem B2342765 : Blo 1561478 2342765 := bbase (se 3 (by rfl) ⟨439268, by rfl⟩ : syracuseStep 2342765 = 878537) (by norm_num)
theorem B2637677 : Blo 1561478 2637677 := bbase (se 3 (by rfl) ⟨494564, by rfl⟩ : syracuseStep 2637677 = 989129) (by norm_num)
theorem B3514229 : Blo 1561478 3514229 := bbase (se 5 (by rfl) ⟨164729, by rfl⟩ : syracuseStep 3514229 = 329459) (by norm_num)
theorem B3956597 : Blo 1561478 3956597 := bbase (se 5 (by rfl) ⟨185465, by rfl⟩ : syracuseStep 3956597 = 370931) (by norm_num)
theorem B2342789 : Blo 1561478 2342789 := bbase (se 4 (by rfl) ⟨219636, by rfl⟩ : syracuseStep 2342789 = 439273) (by norm_num)
theorem B3006341 : Blo 1561478 3006341 := bbase (se 4 (by rfl) ⟨281844, by rfl⟩ : syracuseStep 3006341 = 563689) (by norm_num)
theorem B25354133 : Blo 1561478 25354133 := bbase (se 6 (by rfl) ⟨594237, by rfl⟩ : syracuseStep 25354133 = 1188475) (by norm_num)
theorem B2342813 : Blo 1561478 2342813 := bbase (se 3 (by rfl) ⟨439277, by rfl⟩ : syracuseStep 2342813 = 878555) (by norm_num)
theorem B2965405 : Blo 1561478 2965405 := bbase (se 3 (by rfl) ⟨556013, by rfl⟩ : syracuseStep 2965405 = 1112027) (by norm_num)
theorem B2342837 : Blo 1561478 2342837 := bbase (se 5 (by rfl) ⟨109820, by rfl⟩ : syracuseStep 2342837 = 219641) (by norm_num)
theorem B3514301 : Blo 1561478 3514301 := bbase (se 3 (by rfl) ⟨658931, by rfl⟩ : syracuseStep 3514301 = 1317863) (by norm_num)
theorem B2342861 : Blo 1561478 2342861 := bbase (se 3 (by rfl) ⟨439286, by rfl⟩ : syracuseStep 2342861 = 878573) (by norm_num)
theorem B2342885 : Blo 1561478 2342885 := bbase (se 4 (by rfl) ⟨219645, by rfl⟩ : syracuseStep 2342885 = 439291) (by norm_num)
theorem B2637805 : Blo 1561478 2637805 := bbase (se 3 (by rfl) ⟨494588, by rfl⟩ : syracuseStep 2637805 = 989177) (by norm_num)
theorem B5275637 : Blo 1561478 5275637 := bbase (se 5 (by rfl) ⟨247295, by rfl⟩ : syracuseStep 5275637 = 494591) (by norm_num)
theorem B2342909 : Blo 1561478 2342909 := bbase (se 3 (by rfl) ⟨439295, by rfl⟩ : syracuseStep 2342909 = 878591) (by norm_num)
theorem B2342915 : Blo 1561478 2342915 := bstep (se 1 (by rfl) ⟨1757186, by rfl⟩ : syracuseStep 2342915 = 3514373) B3514373
theorem B2342945 : Blo 1561478 2342945 := bstep (se 2 (by rfl) ⟨878604, by rfl⟩ : syracuseStep 2342945 = 1757209) B1757209
theorem B2637859 : Blo 1561478 2637859 := bstep (se 1 (by rfl) ⟨1978394, by rfl⟩ : syracuseStep 2637859 = 3956789) B3956789
theorem B9019441 : Blo 1561478 9019441 := bstep (se 2 (by rfl) ⟨3382290, by rfl⟩ : syracuseStep 9019441 = 6764581) B6764581
theorem B2342963 : Blo 1561478 2342963 := bstep (se 1 (by rfl) ⟨1757222, by rfl⟩ : syracuseStep 2342963 = 3514445) B3514445
theorem B28508213 : Blo 1561478 28508213 := bstep (se 5 (by rfl) ⟨1336322, by rfl⟩ : syracuseStep 28508213 = 2672645) B2672645
theorem B2342993 : Blo 1561478 2342993 := bstep (se 2 (by rfl) ⟨878622, by rfl⟩ : syracuseStep 2342993 = 1757245) B1757245
theorem B2343011 : Blo 1561478 2343011 := bstep (se 1 (by rfl) ⟨1757258, by rfl⟩ : syracuseStep 2343011 = 3514517) B3514517
theorem B3514481 : Blo 1561478 3514481 := bstep (se 2 (by rfl) ⟨1317930, by rfl⟩ : syracuseStep 3514481 = 2635861) B2635861
theorem B8896625 : Blo 1561478 8896625 := bstep (se 2 (by rfl) ⟨3336234, by rfl⟩ : syracuseStep 8896625 = 6672469) B6672469
theorem B2343041 : Blo 1561478 2343041 := bstep (se 2 (by rfl) ⟨878640, by rfl⟩ : syracuseStep 2343041 = 1757281) B1757281
theorem B3514499 : Blo 1561478 3514499 := bstep (se 1 (by rfl) ⟨2635874, by rfl⟩ : syracuseStep 3514499 = 5271749) B5271749
theorem B2343059 : Blo 1561478 2343059 := bstep (se 1 (by rfl) ⟨1757294, by rfl⟩ : syracuseStep 2343059 = 3514589) B3514589
theorem B2343089 : Blo 1561478 2343089 := bstep (se 2 (by rfl) ⟨878658, by rfl⟩ : syracuseStep 2343089 = 1757317) B1757317
theorem B2638001 : Blo 1561478 2638001 := bstep (se 2 (by rfl) ⟨989250, by rfl⟩ : syracuseStep 2638001 = 1978501) B1978501
theorem B2343107 : Blo 1561478 2343107 := bstep (se 1 (by rfl) ⟨1757330, by rfl⟩ : syracuseStep 2343107 = 3514661) B3514661
theorem B5275853 : Blo 1561478 5275853 := bstep (se 3 (by rfl) ⟨989222, by rfl⟩ : syracuseStep 5275853 = 1978445) B1978445
theorem B3563729 : Blo 1561478 3563729 := bstep (se 2 (by rfl) ⟨1336398, by rfl⟩ : syracuseStep 3563729 = 2672797) B2672797
theorem B2343137 : Blo 1561478 2343137 := bstep (se 2 (by rfl) ⟨878676, by rfl⟩ : syracuseStep 2343137 = 1757353) B1757353
theorem B7913699 : Blo 1561478 7913699 := bstep (se 1 (by rfl) ⟨5935274, by rfl⟩ : syracuseStep 7913699 = 11870549) B11870549
theorem B2343155 : Blo 1561478 2343155 := bstep (se 1 (by rfl) ⟨1757366, by rfl⟩ : syracuseStep 2343155 = 3514733) B3514733
theorem B5275907 : Blo 1561478 5275907 := bstep (se 1 (by rfl) ⟨3956930, by rfl⟩ : syracuseStep 5275907 = 7913861) B7913861
theorem B2343185 : Blo 1561478 2343185 := bstep (se 2 (by rfl) ⟨878694, by rfl⟩ : syracuseStep 2343185 = 1757389) B1757389
theorem B2343203 : Blo 1561478 2343203 := bstep (se 1 (by rfl) ⟨1757402, by rfl⟩ : syracuseStep 2343203 = 3514805) B3514805
theorem B2638129 : Blo 1561478 2638129 := bstep (se 2 (by rfl) ⟨989298, by rfl⟩ : syracuseStep 2638129 = 1978597) B1978597
theorem B2343233 : Blo 1561478 2343233 := bstep (se 2 (by rfl) ⟨878712, by rfl⟩ : syracuseStep 2343233 = 1757425) B1757425
theorem B2343251 : Blo 1561478 2343251 := bstep (se 1 (by rfl) ⟨1757438, by rfl⟩ : syracuseStep 2343251 = 3514877) B3514877
theorem B2638163 : Blo 1561478 2638163 := bstep (se 1 (by rfl) ⟨1978622, by rfl⟩ : syracuseStep 2638163 = 3957245) B3957245
theorem B4448621 : Blo 1561478 4448621 := bstep (se 3 (by rfl) ⟨834116, by rfl⟩ : syracuseStep 4448621 = 1668233) B1668233
theorem B2343281 : Blo 1561478 2343281 := bstep (se 2 (by rfl) ⟨878730, by rfl⟩ : syracuseStep 2343281 = 1757461) B1757461
theorem B2343299 : Blo 1561478 2343299 := bstep (se 1 (by rfl) ⟨1757474, by rfl⟩ : syracuseStep 2343299 = 3514949) B3514949
theorem B2965891 : Blo 1561478 2965891 := bstep (se 1 (by rfl) ⟨2224418, by rfl⟩ : syracuseStep 2965891 = 4448837) B4448837
theorem B3514769 : Blo 1561478 3514769 := bstep (se 2 (by rfl) ⟨1318038, by rfl⟩ : syracuseStep 3514769 = 2636077) B2636077
theorem B2343329 : Blo 1561478 2343329 := bstep (se 2 (by rfl) ⟨878748, by rfl⟩ : syracuseStep 2343329 = 1757497) B1757497
theorem B3514787 : Blo 1561478 3514787 := bstep (se 1 (by rfl) ⟨2636090, by rfl⟩ : syracuseStep 3514787 = 5272181) B5272181
theorem B3563939 : Blo 1561478 3563939 := bstep (se 1 (by rfl) ⟨2672954, by rfl⟩ : syracuseStep 3563939 = 5345909) B5345909
theorem B2343347 : Blo 1561478 2343347 := bstep (se 1 (by rfl) ⟨1757510, by rfl⟩ : syracuseStep 2343347 = 3515021) B3515021
theorem B5005763 : Blo 1561478 5005763 := bstep (se 1 (by rfl) ⟨3754322, by rfl⟩ : syracuseStep 5005763 = 7508645) B7508645
theorem B2343377 : Blo 1561478 2343377 := bstep (se 2 (by rfl) ⟨878766, by rfl⟩ : syracuseStep 2343377 = 1757533) B1757533
theorem B2638291 : Blo 1561478 2638291 := bstep (se 1 (by rfl) ⟨1978718, by rfl⟩ : syracuseStep 2638291 = 3957437) B3957437
theorem B2343395 : Blo 1561478 2343395 := bstep (se 1 (by rfl) ⟨1757546, by rfl⟩ : syracuseStep 2343395 = 3515093) B3515093
theorem B2343425 : Blo 1561478 2343425 := bstep (se 2 (by rfl) ⟨878784, by rfl⟩ : syracuseStep 2343425 = 1757569) B1757569
theorem B5276177 : Blo 1561478 5276177 := bstep (se 2 (by rfl) ⟨1978566, by rfl⟩ : syracuseStep 5276177 = 3957133) B3957133
theorem B2343443 : Blo 1561478 2343443 := bstep (se 1 (by rfl) ⟨1757582, by rfl⟩ : syracuseStep 2343443 = 3515165) B3515165
theorem B4448803 : Blo 1561478 4448803 := bstep (se 1 (by rfl) ⟨3336602, by rfl⟩ : syracuseStep 4448803 = 6673205) B6673205
theorem B2966051 : Blo 1561478 2966051 := bstep (se 1 (by rfl) ⟨2224538, by rfl⟩ : syracuseStep 2966051 = 4449077) B4449077
theorem B5931569 : Blo 1561478 5931569 := bstep (se 2 (by rfl) ⟨2224338, by rfl⟩ : syracuseStep 5931569 = 4448677) B4448677
theorem B2343473 : Blo 1561478 2343473 := bstep (se 2 (by rfl) ⟨878802, by rfl⟩ : syracuseStep 2343473 = 1757605) B1757605
theorem B2343491 : Blo 1561478 2343491 := bstep (se 1 (by rfl) ⟨1757618, by rfl⟩ : syracuseStep 2343491 = 3515237) B3515237
theorem B2343521 : Blo 1561478 2343521 := bstep (se 2 (by rfl) ⟨878820, by rfl⟩ : syracuseStep 2343521 = 1757641) B1757641
theorem B2376305 : Blo 1561478 2376305 := bstep (se 2 (by rfl) ⟨891114, by rfl⟩ : syracuseStep 2376305 = 1782229) B1782229
theorem B2343539 : Blo 1561478 2343539 := bstep (se 1 (by rfl) ⟨1757654, by rfl⟩ : syracuseStep 2343539 = 3515309) B3515309
theorem B2343569 : Blo 1561478 2343569 := bstep (se 2 (by rfl) ⟨878838, by rfl⟩ : syracuseStep 2343569 = 1757677) B1757677
theorem B2343587 : Blo 1561478 2343587 := bstep (se 1 (by rfl) ⟨1757690, by rfl⟩ : syracuseStep 2343587 = 3515381) B3515381
theorem B3515057 : Blo 1561478 3515057 := bstep (se 2 (by rfl) ⟨1318146, by rfl⟩ : syracuseStep 3515057 = 2636293) B2636293
theorem B2343617 : Blo 1561478 2343617 := bstep (se 2 (by rfl) ⟨878856, by rfl⟩ : syracuseStep 2343617 = 1757713) B1757713
theorem B3515075 : Blo 1561478 3515075 := bstep (se 1 (by rfl) ⟨2636306, by rfl⟩ : syracuseStep 3515075 = 5272613) B5272613
theorem B7504589 : Blo 1561478 7504589 := bstep (se 3 (by rfl) ⟨1407110, by rfl⟩ : syracuseStep 7504589 = 2814221) B2814221
theorem B5006033 : Blo 1561478 5006033 := bstep (se 2 (by rfl) ⟨1877262, by rfl⟩ : syracuseStep 5006033 = 3754525) B3754525
theorem B3957457 : Blo 1561478 3957457 := bstep (se 2 (by rfl) ⟨1484046, by rfl⟩ : syracuseStep 3957457 = 2968093) B2968093
theorem B2343635 : Blo 1561478 2343635 := bstep (se 1 (by rfl) ⟨1757726, by rfl⟩ : syracuseStep 2343635 = 3515453) B3515453
theorem B2343665 : Blo 1561478 2343665 := bstep (se 2 (by rfl) ⟨878874, by rfl⟩ : syracuseStep 2343665 = 1757749) B1757749
theorem B2343683 : Blo 1561478 2343683 := bstep (se 1 (by rfl) ⟨1757762, by rfl⟩ : syracuseStep 2343683 = 3515525) B3515525
theorem B5628685 : Blo 1561478 5628685 := bstep (se 3 (by rfl) ⟨1055378, by rfl⟩ : syracuseStep 5628685 = 2110757) B2110757
theorem B2343713 : Blo 1561478 2343713 := bstep (se 2 (by rfl) ⟨878892, by rfl⟩ : syracuseStep 2343713 = 1757785) B1757785
theorem B2343731 : Blo 1561478 2343731 := bstep (se 1 (by rfl) ⟨1757798, by rfl⟩ : syracuseStep 2343731 = 3515597) B3515597
theorem B2343761 : Blo 1561478 2343761 := bstep (se 2 (by rfl) ⟨878910, by rfl⟩ : syracuseStep 2343761 = 1757821) B1757821
theorem B2343779 : Blo 1561478 2343779 := bstep (se 1 (by rfl) ⟨1757834, by rfl⟩ : syracuseStep 2343779 = 3515669) B3515669
theorem B2343809 : Blo 1561478 2343809 := bstep (se 2 (by rfl) ⟨878928, by rfl⟩ : syracuseStep 2343809 = 1757857) B1757857
theorem B2343827 : Blo 1561478 2343827 := bstep (se 1 (by rfl) ⟨1757870, by rfl⟩ : syracuseStep 2343827 = 3515741) B3515741
theorem B10838947 : Blo 1561478 10838947 := bstep (se 1 (by rfl) ⟨8129210, by rfl⟩ : syracuseStep 10838947 = 16258421) B16258421
theorem B2343857 : Blo 1561478 2343857 := bstep (se 2 (by rfl) ⟨878946, by rfl⟩ : syracuseStep 2343857 = 1757893) B1757893
theorem B3335107 : Blo 1561478 3335107 := bstep (se 1 (by rfl) ⟨2501330, by rfl⟩ : syracuseStep 3335107 = 5002661) B5002661
theorem B2343875 : Blo 1561478 2343875 := bstep (se 1 (by rfl) ⟨1757906, by rfl⟩ : syracuseStep 2343875 = 3515813) B3515813
theorem B3515345 : Blo 1561478 3515345 := bstep (se 2 (by rfl) ⟨1318254, by rfl⟩ : syracuseStep 3515345 = 2636509) B2636509
theorem B2343905 : Blo 1561478 2343905 := bstep (se 2 (by rfl) ⟨878964, by rfl⟩ : syracuseStep 2343905 = 1757929) B1757929
theorem B3515363 : Blo 1561478 3515363 := bstep (se 1 (by rfl) ⟨2636522, by rfl⟩ : syracuseStep 3515363 = 5273045) B5273045
theorem B2343923 : Blo 1561478 2343923 := bstep (se 1 (by rfl) ⟨1757942, by rfl⟩ : syracuseStep 2343923 = 3515885) B3515885
theorem B4449293 : Blo 1561478 4449293 := bstep (se 3 (by rfl) ⟨834242, by rfl⟩ : syracuseStep 4449293 = 1668485) B1668485
theorem B6423565 : Blo 1561478 6423565 := bstep (se 3 (by rfl) ⟨1204418, by rfl⟩ : syracuseStep 6423565 = 2408837) B2408837
theorem B7914509 : Blo 1561478 7914509 := bstep (se 3 (by rfl) ⟨1483970, by rfl⟩ : syracuseStep 7914509 = 2967941) B2967941
theorem B2343953 : Blo 1561478 2343953 := bstep (se 2 (by rfl) ⟨878982, by rfl⟩ : syracuseStep 2343953 = 1757965) B1757965
theorem B3007505 : Blo 1561478 3007505 := bstep (se 2 (by rfl) ⟨1127814, by rfl⟩ : syracuseStep 3007505 = 2255629) B2255629
theorem B3752995 : Blo 1561478 3752995 := bstep (se 1 (by rfl) ⟨2814746, by rfl⟩ : syracuseStep 3752995 = 5629493) B5629493
theorem B2343971 : Blo 1561478 2343971 := bstep (se 1 (by rfl) ⟨1757978, by rfl⟩ : syracuseStep 2343971 = 3515957) B3515957
theorem B5276717 : Blo 1561478 5276717 := bstep (se 3 (by rfl) ⟨989384, by rfl⟩ : syracuseStep 5276717 = 1978769) B1978769
theorem B2344001 : Blo 1561478 2344001 := bstep (se 2 (by rfl) ⟨879000, by rfl⟩ : syracuseStep 2344001 = 1758001) B1758001
theorem B2344019 : Blo 1561478 2344019 := bstep (se 1 (by rfl) ⟨1758014, by rfl⟩ : syracuseStep 2344019 = 3516029) B3516029
theorem B2344049 : Blo 1561478 2344049 := bstep (se 2 (by rfl) ⟨879018, by rfl⟩ : syracuseStep 2344049 = 1758037) B1758037
theorem B2344067 : Blo 1561478 2344067 := bstep (se 1 (by rfl) ⟨1758050, by rfl⟩ : syracuseStep 2344067 = 3516101) B3516101
theorem B2344097 : Blo 1561478 2344097 := bstep (se 2 (by rfl) ⟨879036, by rfl⟩ : syracuseStep 2344097 = 1758073) B1758073
theorem B2376865 : Blo 1561478 2376865 := bstep (se 2 (by rfl) ⟨891324, by rfl⟩ : syracuseStep 2376865 = 1782649) B1782649
theorem B2344115 : Blo 1561478 2344115 := bstep (se 1 (by rfl) ⟨1758086, by rfl⟩ : syracuseStep 2344115 = 3516173) B3516173
theorem B5629133 : Blo 1561478 5629133 := bstep (se 3 (by rfl) ⟨1055462, by rfl⟩ : syracuseStep 5629133 = 2110925) B2110925
theorem B5932237 : Blo 1561478 5932237 := bstep (se 3 (by rfl) ⟨1112294, by rfl⟩ : syracuseStep 5932237 = 2224589) B2224589
theorem B2344145 : Blo 1561478 2344145 := bstep (se 2 (by rfl) ⟨879054, by rfl⟩ : syracuseStep 2344145 = 1758109) B1758109
theorem B2344163 : Blo 1561478 2344163 := bstep (se 1 (by rfl) ⟨1758122, by rfl⟩ : syracuseStep 2344163 = 3516245) B3516245
theorem B6677731 : Blo 1561478 6677731 := bstep (se 1 (by rfl) ⟨5008298, by rfl⟩ : syracuseStep 6677731 = 10016597) B10016597
theorem B3515633 : Blo 1561478 3515633 := bstep (se 2 (by rfl) ⟨1318362, by rfl⟩ : syracuseStep 3515633 = 2636725) B2636725
theorem B2344193 : Blo 1561478 2344193 := bstep (se 2 (by rfl) ⟨879072, by rfl⟩ : syracuseStep 2344193 = 1758145) B1758145
theorem B3515651 : Blo 1561478 3515651 := bstep (se 1 (by rfl) ⟨2636738, by rfl⟩ : syracuseStep 3515651 = 5273477) B5273477
theorem B2344211 : Blo 1561478 2344211 := bstep (se 1 (by rfl) ⟨1758158, by rfl⟩ : syracuseStep 2344211 = 3516317) B3516317
theorem B2344241 : Blo 1561478 2344241 := bstep (se 2 (by rfl) ⟨879090, by rfl⟩ : syracuseStep 2344241 = 1758181) B1758181
theorem B2344259 : Blo 1561478 2344259 := bstep (se 1 (by rfl) ⟨1758194, by rfl⟩ : syracuseStep 2344259 = 3516389) B3516389
theorem B2344289 : Blo 1561478 2344289 := bstep (se 2 (by rfl) ⟨879108, by rfl⟩ : syracuseStep 2344289 = 1758217) B1758217
theorem B2344307 : Blo 1561478 2344307 := bstep (se 1 (by rfl) ⟨1758230, by rfl⟩ : syracuseStep 2344307 = 3516461) B3516461
theorem B2344337 : Blo 1561478 2344337 := bstep (se 2 (by rfl) ⟨879126, by rfl⟩ : syracuseStep 2344337 = 1758253) B1758253
theorem B2344355 : Blo 1561478 2344355 := bstep (se 1 (by rfl) ⟨1758266, by rfl⟩ : syracuseStep 2344355 = 3516533) B3516533
theorem B2344385 : Blo 1561478 2344385 := bstep (se 2 (by rfl) ⟨879144, by rfl⟩ : syracuseStep 2344385 = 1758289) B1758289
theorem B2344403 : Blo 1561478 2344403 := bstep (se 1 (by rfl) ⟨1758302, by rfl⟩ : syracuseStep 2344403 = 3516605) B3516605
theorem B30025187 : Blo 1561478 30025187 := bstep (se 1 (by rfl) ⟨22518890, by rfl⟩ : syracuseStep 30025187 = 45037781) B45037781
theorem B2344433 : Blo 1561478 2344433 := bstep (se 2 (by rfl) ⟨879162, by rfl⟩ : syracuseStep 2344433 = 1758325) B1758325
theorem B2344451 : Blo 1561478 2344451 := bstep (se 1 (by rfl) ⟨1758338, by rfl⟩ : syracuseStep 2344451 = 3516677) B3516677
theorem B3515921 : Blo 1561478 3515921 := bstep (se 2 (by rfl) ⟨1318470, by rfl⟩ : syracuseStep 3515921 = 2636941) B2636941
theorem B2344481 : Blo 1561478 2344481 := bstep (se 2 (by rfl) ⟨879180, by rfl⟩ : syracuseStep 2344481 = 1758361) B1758361
theorem B8898083 : Blo 1561478 8898083 := bstep (se 1 (by rfl) ⟨6673562, by rfl⟩ : syracuseStep 8898083 = 13347125) B13347125
theorem B3515939 : Blo 1561478 3515939 := bstep (se 1 (by rfl) ⟨2636954, by rfl⟩ : syracuseStep 3515939 = 5273909) B5273909
theorem B2344499 : Blo 1561478 2344499 := bstep (se 1 (by rfl) ⟨1758374, by rfl⟩ : syracuseStep 2344499 = 3516749) B3516749
theorem B3753553 : Blo 1561478 3753553 := bstep (se 2 (by rfl) ⟨1407582, by rfl⟩ : syracuseStep 3753553 = 2815165) B2815165
theorem B2967121 : Blo 1561478 2967121 := bstep (se 2 (by rfl) ⟨1112670, by rfl⟩ : syracuseStep 2967121 = 2225341) B2225341
theorem B2344529 : Blo 1561478 2344529 := bstep (se 2 (by rfl) ⟨879198, by rfl⟩ : syracuseStep 2344529 = 1758397) B1758397
theorem B2344547 : Blo 1561478 2344547 := bstep (se 1 (by rfl) ⟨1758410, by rfl⟩ : syracuseStep 2344547 = 3516821) B3516821
theorem B2344577 : Blo 1561478 2344577 := bstep (se 2 (by rfl) ⟨879216, by rfl⟩ : syracuseStep 2344577 = 1758433) B1758433
theorem B3335825 : Blo 1561478 3335825 := bstep (se 2 (by rfl) ⟨1250934, by rfl⟩ : syracuseStep 3335825 = 2501869) B2501869
theorem B2344595 : Blo 1561478 2344595 := bstep (se 1 (by rfl) ⟨1758446, by rfl⟩ : syracuseStep 2344595 = 3516893) B3516893
theorem B2344625 : Blo 1561478 2344625 := bstep (se 2 (by rfl) ⟨879234, by rfl⟩ : syracuseStep 2344625 = 1758469) B1758469
theorem B1877699 : Blo 1561478 1877699 := bstep (se 1 (by rfl) ⟨1408274, by rfl⟩ : syracuseStep 1877699 = 2816549) B2816549
theorem B2344643 : Blo 1561478 2344643 := bstep (se 1 (by rfl) ⟨1758482, by rfl⟩ : syracuseStep 2344643 = 3516965) B3516965
theorem B22537925 : Blo 1561478 22537925 := bstep (se 4 (by rfl) ⟨2112930, by rfl⟩ : syracuseStep 22537925 = 4225861) B4225861
theorem B2344673 : Blo 1561478 2344673 := bstep (se 2 (by rfl) ⟨879252, by rfl⟩ : syracuseStep 2344673 = 1758505) B1758505
theorem B7907057 : Blo 1561478 7907057 := bstep (se 2 (by rfl) ⟨2965146, by rfl⟩ : syracuseStep 7907057 = 5930293) B5930293
theorem B2344691 : Blo 1561478 2344691 := bstep (se 1 (by rfl) ⟨1758518, by rfl⟩ : syracuseStep 2344691 = 3517037) B3517037
theorem B2344721 : Blo 1561478 2344721 := bstep (se 2 (by rfl) ⟨879270, by rfl⟩ : syracuseStep 2344721 = 1758541) B1758541
theorem B2344739 : Blo 1561478 2344739 := bstep (se 1 (by rfl) ⟨1758554, by rfl⟩ : syracuseStep 2344739 = 3517109) B3517109
theorem B3516209 : Blo 1561478 3516209 := bstep (se 2 (by rfl) ⟨1318578, by rfl⟩ : syracuseStep 3516209 = 2637157) B2637157
theorem B2344769 : Blo 1561478 2344769 := bstep (se 2 (by rfl) ⟨879288, by rfl⟩ : syracuseStep 2344769 = 1758577) B1758577
theorem B3516227 : Blo 1561478 3516227 := bstep (se 1 (by rfl) ⟨2637170, by rfl⟩ : syracuseStep 3516227 = 5274341) B5274341
theorem B2344787 : Blo 1561478 2344787 := bstep (se 1 (by rfl) ⟨1758590, by rfl⟩ : syracuseStep 2344787 = 3517181) B3517181
theorem B11265905 : Blo 1561478 11265905 := bstep (se 2 (by rfl) ⟨4224714, by rfl⟩ : syracuseStep 11265905 = 8449429) B8449429
theorem B2344817 : Blo 1561478 2344817 := bstep (se 2 (by rfl) ⟨879306, by rfl⟩ : syracuseStep 2344817 = 1758613) B1758613
theorem B2344835 : Blo 1561478 2344835 := bstep (se 1 (by rfl) ⟨1758626, by rfl⟩ : syracuseStep 2344835 = 3517253) B3517253
theorem B2344865 : Blo 1561478 2344865 := bstep (se 2 (by rfl) ⟨879324, by rfl⟩ : syracuseStep 2344865 = 1758649) B1758649
theorem B2344883 : Blo 1561478 2344883 := bstep (se 1 (by rfl) ⟨1758662, by rfl⟩ : syracuseStep 2344883 = 3517325) B3517325
theorem B2344913 : Blo 1561478 2344913 := bstep (se 2 (by rfl) ⟨879342, by rfl⟩ : syracuseStep 2344913 = 1758685) B1758685
theorem B5933027 : Blo 1561478 5933027 := bstep (se 1 (by rfl) ⟨4449770, by rfl⟩ : syracuseStep 5933027 = 8899541) B8899541
theorem B2344931 : Blo 1561478 2344931 := bstep (se 1 (by rfl) ⟨1758698, by rfl⟩ : syracuseStep 2344931 = 3517397) B3517397
theorem B2344961 : Blo 1561478 2344961 := bstep (se 2 (by rfl) ⟨879360, by rfl⟩ : syracuseStep 2344961 = 1758721) B1758721
theorem B1976339 : Blo 1561478 1976339 := bstep (se 1 (by rfl) ⟨1482254, by rfl⟩ : syracuseStep 1976339 = 2964509) B2964509
theorem B1878035 : Blo 1561478 1878035 := bstep (se 1 (by rfl) ⟨1408526, by rfl⟩ : syracuseStep 1878035 = 2817053) B2817053
theorem B2344979 : Blo 1561478 2344979 := bstep (se 1 (by rfl) ⟨1758734, by rfl⟩ : syracuseStep 2344979 = 3517469) B3517469
theorem B2345009 : Blo 1561478 2345009 := bstep (se 2 (by rfl) ⟨879378, by rfl⟩ : syracuseStep 2345009 = 1758757) B1758757
theorem B63408181 : Blo 1561478 63408181 := bstep (se 5 (by rfl) ⟨2972258, by rfl⟩ : syracuseStep 63408181 = 5944517) B5944517
theorem B2345027 : Blo 1561478 2345027 := bstep (se 1 (by rfl) ⟨1758770, by rfl⟩ : syracuseStep 2345027 = 3517541) B3517541
theorem B10152013 : Blo 1561478 10152013 := bstep (se 3 (by rfl) ⟨1903502, by rfl⟩ : syracuseStep 10152013 = 3807005) B3807005
theorem B3516497 : Blo 1561478 3516497 := bstep (se 2 (by rfl) ⟨1318686, by rfl⟩ : syracuseStep 3516497 = 2637373) B2637373
theorem B2345057 : Blo 1561478 2345057 := bstep (se 2 (by rfl) ⟨879396, by rfl⟩ : syracuseStep 2345057 = 1758793) B1758793
theorem B3516515 : Blo 1561478 3516515 := bstep (se 1 (by rfl) ⟨2637386, by rfl⟩ : syracuseStep 3516515 = 5274773) B5274773
theorem B2345075 : Blo 1561478 2345075 := bstep (se 1 (by rfl) ⟨1758806, by rfl⟩ : syracuseStep 2345075 = 3517613) B3517613
theorem B10012805 : Blo 1561478 10012805 := bstep (se 4 (by rfl) ⟨938700, by rfl⟩ : syracuseStep 10012805 = 1877401) B1877401
theorem B3336337 : Blo 1561478 3336337 := bstep (se 2 (by rfl) ⟨1251126, by rfl⟩ : syracuseStep 3336337 = 2502253) B2502253
theorem B2345105 : Blo 1561478 2345105 := bstep (se 2 (by rfl) ⟨879414, by rfl⟩ : syracuseStep 2345105 = 1758829) B1758829
theorem B2345123 : Blo 1561478 2345123 := bstep (se 1 (by rfl) ⟨1758842, by rfl⟩ : syracuseStep 2345123 = 3517685) B3517685
theorem B4450477 : Blo 1561478 4450477 := bstep (se 3 (by rfl) ⟨834464, by rfl⟩ : syracuseStep 4450477 = 1668929) B1668929
theorem B2345153 : Blo 1561478 2345153 := bstep (se 2 (by rfl) ⟨879432, by rfl⟩ : syracuseStep 2345153 = 1758865) B1758865
theorem B2345171 : Blo 1561478 2345171 := bstep (se 1 (by rfl) ⟨1758878, by rfl⟩ : syracuseStep 2345171 = 3517757) B3517757
theorem B3754225 : Blo 1561478 3754225 := bstep (se 2 (by rfl) ⟨1407834, by rfl⟩ : syracuseStep 3754225 = 2815669) B2815669
theorem B2345201 : Blo 1561478 2345201 := bstep (se 2 (by rfl) ⟨879450, by rfl⟩ : syracuseStep 2345201 = 1758901) B1758901
theorem B3516785 : Blo 1561478 3516785 := bstep (se 2 (by rfl) ⟨1318794, by rfl⟩ : syracuseStep 3516785 = 2637589) B2637589
theorem B3516803 : Blo 1561478 3516803 := bstep (se 1 (by rfl) ⟨2637602, by rfl⟩ : syracuseStep 3516803 = 5275205) B5275205
theorem B40577507 : Blo 1561478 40577507 := bstep (se 1 (by rfl) ⟨30433130, by rfl⟩ : syracuseStep 40577507 = 60866261) B60866261
theorem B8899085 : Blo 1561478 8899085 := bstep (se 3 (by rfl) ⟨1668578, by rfl⟩ : syracuseStep 8899085 = 3337157) B3337157
theorem B16902755 : Blo 1561478 16902755 := bstep (se 1 (by rfl) ⟨12677066, by rfl⟩ : syracuseStep 16902755 = 25354133) B25354133
theorem B5270129 : Blo 1561478 5270129 := bstep (se 2 (by rfl) ⟨1976298, by rfl⟩ : syracuseStep 5270129 = 3952597) B3952597
theorem B5933681 : Blo 1561478 5933681 := bstep (se 2 (by rfl) ⟨2225130, by rfl⟩ : syracuseStep 5933681 = 4450261) B4450261
theorem B11864717 : Blo 1561478 11864717 := bstep (se 3 (by rfl) ⟨2224634, by rfl⟩ : syracuseStep 11864717 = 4449269) B4449269
theorem B3517073 : Blo 1561478 3517073 := bstep (se 2 (by rfl) ⟨1318902, by rfl⟩ : syracuseStep 3517073 = 2637805) B2637805
theorem B3517091 : Blo 1561478 3517091 := bstep (se 1 (by rfl) ⟨2637818, by rfl⟩ : syracuseStep 3517091 = 5275637) B5275637
theorem B1977043 : Blo 1561478 1977043 := bstep (se 1 (by rfl) ⟨1482782, by rfl⟩ : syracuseStep 1977043 = 2965565) B2965565
theorem B5630705 : Blo 1561478 5630705 := bstep (se 2 (by rfl) ⟨2111514, by rfl⟩ : syracuseStep 5630705 = 4223029) B4223029
theorem B1977139 : Blo 1561478 1977139 := bstep (se 1 (by rfl) ⟨1482854, by rfl⟩ : syracuseStep 1977139 = 2965709) B2965709
theorem B2501459 : Blo 1561478 2501459 := bstep (se 1 (by rfl) ⟨1876094, by rfl⟩ : syracuseStep 2501459 = 3752189) B3752189
theorem B8014691 : Blo 1561478 8014691 := bstep (se 1 (by rfl) ⟨6011018, by rfl⟩ : syracuseStep 8014691 = 12022037) B12022037
theorem B6761357 : Blo 1561478 6761357 := bstep (se 3 (by rfl) ⟨1267754, by rfl⟩ : syracuseStep 6761357 = 2535509) B2535509
theorem B3517361 : Blo 1561478 3517361 := bstep (se 2 (by rfl) ⟨1319010, by rfl⟩ : syracuseStep 3517361 = 2638021) B2638021
theorem B3517379 : Blo 1561478 3517379 := bstep (se 1 (by rfl) ⟨2638034, by rfl⟩ : syracuseStep 3517379 = 5276069) B5276069
theorem B2501651 : Blo 1561478 2501651 := bstep (se 1 (by rfl) ⟨1876238, by rfl⟩ : syracuseStep 2501651 = 3752477) B3752477
theorem B5008493 : Blo 1561478 5008493 := bstep (se 3 (by rfl) ⟨939092, by rfl⟩ : syracuseStep 5008493 = 1878185) B1878185
theorem B5270669 : Blo 1561478 5270669 := bstep (se 3 (by rfl) ⟨988250, by rfl⟩ : syracuseStep 5270669 = 1976501) B1976501
theorem B5786765 : Blo 1561478 5786765 := bstep (se 3 (by rfl) ⟨1085018, by rfl⟩ : syracuseStep 5786765 = 2170037) B2170037
theorem B7908515 : Blo 1561478 7908515 := bstep (se 1 (by rfl) ⟨5931386, by rfl⟩ : syracuseStep 7908515 = 11862773) B11862773
theorem B1780915 : Blo 1561478 1780915 := bstep (se 1 (by rfl) ⟨1335686, by rfl⟩ : syracuseStep 1780915 = 2671373) B2671373
theorem B5270723 : Blo 1561478 5270723 := bstep (se 1 (by rfl) ⟨3953042, by rfl⟩ : syracuseStep 5270723 = 7906085) B7906085
theorem B4451537 : Blo 1561478 4451537 := bstep (se 2 (by rfl) ⟨1669326, by rfl⟩ : syracuseStep 4451537 = 3338653) B3338653
theorem B3517649 : Blo 1561478 3517649 := bstep (se 2 (by rfl) ⟨1319118, by rfl⟩ : syracuseStep 3517649 = 2638237) B2638237
theorem B10005731 : Blo 1561478 10005731 := bstep (se 1 (by rfl) ⟨7504298, by rfl⟩ : syracuseStep 10005731 = 15008597) B15008597
theorem B3517667 : Blo 1561478 3517667 := bstep (se 1 (by rfl) ⟨2638250, by rfl⟩ : syracuseStep 3517667 = 5276501) B5276501
theorem B1977635 : Blo 1561478 1977635 := bstep (se 1 (by rfl) ⟨1483226, by rfl⟩ : syracuseStep 1977635 = 2966453) B2966453
theorem B22842737 : Blo 1561478 22842737 := bstep (se 2 (by rfl) ⟨8566026, by rfl⟩ : syracuseStep 22842737 = 17132053) B17132053
theorem B2223553 : Blo 1561478 2223553 := bstep (se 2 (by rfl) ⟨833832, by rfl⟩ : syracuseStep 2223553 = 1667665) B1667665
theorem B5270993 : Blo 1561478 5270993 := bstep (se 2 (by rfl) ⟨1976622, by rfl⟩ : syracuseStep 5270993 = 3953245) B3953245
theorem B4279811 : Blo 1561478 4279811 := bstep (se 1 (by rfl) ⟨3209858, by rfl⟩ : syracuseStep 4279811 = 6419717) B6419717
theorem B1756723 : Blo 1561478 1756723 := bstep (se 1 (by rfl) ⟨1317542, by rfl⟩ : syracuseStep 1756723 = 2635085) B2635085
theorem B1781299 : Blo 1561478 1781299 := bstep (se 1 (by rfl) ⟨1335974, by rfl⟩ : syracuseStep 1781299 = 2671949) B2671949
theorem B3337841 : Blo 1561478 3337841 := bstep (se 2 (by rfl) ⟨1251690, by rfl⟩ : syracuseStep 3337841 = 2503381) B2503381
theorem B10006193 : Blo 1561478 10006193 := bstep (se 2 (by rfl) ⟨3752322, by rfl⟩ : syracuseStep 10006193 = 7504645) B7504645
theorem B1756867 : Blo 1561478 1756867 := bstep (se 1 (by rfl) ⟨1317650, by rfl⟩ : syracuseStep 1756867 = 2635301) B2635301
theorem B1757011 : Blo 1561478 1757011 := bstep (se 1 (by rfl) ⟨1317758, by rfl⟩ : syracuseStep 1757011 = 2635517) B2635517
theorem B4452209 : Blo 1561478 4452209 := bstep (se 2 (by rfl) ⟨1669578, by rfl⟩ : syracuseStep 4452209 = 3339157) B3339157
theorem B3952547 : Blo 1561478 3952547 := bstep (se 1 (by rfl) ⟨2964410, by rfl⟩ : syracuseStep 3952547 = 5928821) B5928821
theorem B6016931 : Blo 1561478 6016931 := bstep (se 1 (by rfl) ⟨4512698, by rfl⟩ : syracuseStep 6016931 = 9025397) B9025397
theorem B7909325 : Blo 1561478 7909325 := bstep (se 3 (by rfl) ⟨1482998, by rfl⟩ : syracuseStep 7909325 = 2965997) B2965997
theorem B1757155 : Blo 1561478 1757155 := bstep (se 1 (by rfl) ⟨1317866, by rfl⟩ : syracuseStep 1757155 = 2635733) B2635733
theorem B1978339 : Blo 1561478 1978339 := bstep (se 1 (by rfl) ⟨1483754, by rfl⟩ : syracuseStep 1978339 = 2967509) B2967509
theorem B5271533 : Blo 1561478 5271533 := bstep (se 3 (by rfl) ⟨988412, by rfl⟩ : syracuseStep 5271533 = 1976825) B1976825
theorem B3338243 : Blo 1561478 3338243 := bstep (se 1 (by rfl) ⟨2503682, by rfl⟩ : syracuseStep 3338243 = 5007365) B5007365
theorem B2224145 : Blo 1561478 2224145 := bstep (se 2 (by rfl) ⟨834054, by rfl⟩ : syracuseStep 2224145 = 1668109) B1668109
theorem B5271587 : Blo 1561478 5271587 := bstep (se 1 (by rfl) ⟨3953690, by rfl⟩ : syracuseStep 5271587 = 7907381) B7907381
theorem B5935139 : Blo 1561478 5935139 := bstep (se 1 (by rfl) ⟨4451354, by rfl⟩ : syracuseStep 5935139 = 8902709) B8902709
theorem B5935153 : Blo 1561478 5935153 := bstep (se 2 (by rfl) ⟨2225682, by rfl⟩ : syracuseStep 5935153 = 4451365) B4451365
theorem B1978435 : Blo 1561478 1978435 := bstep (se 1 (by rfl) ⟨1483826, by rfl⟩ : syracuseStep 1978435 = 2967653) B2967653
theorem B3952739 : Blo 1561478 3952739 := bstep (se 1 (by rfl) ⟨2964554, by rfl⟩ : syracuseStep 3952739 = 5929109) B5929109
theorem B1757299 : Blo 1561478 1757299 := bstep (se 1 (by rfl) ⟨1317974, by rfl⟩ : syracuseStep 1757299 = 2635949) B2635949
theorem B1757443 : Blo 1561478 1757443 := bstep (se 1 (by rfl) ⟨1318082, by rfl⟩ : syracuseStep 1757443 = 2636165) B2636165
theorem B2814257 : Blo 1561478 2814257 := bstep (se 2 (by rfl) ⟨1055346, by rfl⟩ : syracuseStep 2814257 = 2110693) B2110693
theorem B5271857 : Blo 1561478 5271857 := bstep (se 2 (by rfl) ⟨1976946, by rfl⟩ : syracuseStep 5271857 = 3953893) B3953893
theorem B8450381 : Blo 1561478 8450381 := bstep (se 3 (by rfl) ⟨1584446, by rfl⟩ : syracuseStep 8450381 = 3168893) B3168893
theorem B16896397 : Blo 1561478 16896397 := bstep (se 3 (by rfl) ⟨3168074, by rfl⟩ : syracuseStep 16896397 = 6336149) B6336149
theorem B1757587 : Blo 1561478 1757587 := bstep (se 1 (by rfl) ⟨1318190, by rfl⟩ : syracuseStep 1757587 = 2636381) B2636381
theorem B2503073 : Blo 1561478 2503073 := bstep (se 2 (by rfl) ⟨938652, by rfl⟩ : syracuseStep 2503073 = 1877305) B1877305
theorem B1757731 : Blo 1561478 1757731 := bstep (se 1 (by rfl) ⟨1318298, by rfl⟩ : syracuseStep 1757731 = 2636597) B2636597
theorem B2224675 : Blo 1561478 2224675 := bstep (se 1 (by rfl) ⟨1668506, by rfl⟩ : syracuseStep 2224675 = 3337013) B3337013
theorem B1757875 : Blo 1561478 1757875 := bstep (se 1 (by rfl) ⟨1318406, by rfl⟩ : syracuseStep 1757875 = 2636813) B2636813
theorem B1667827 : Blo 1561478 1667827 := bstep (se 1 (by rfl) ⟨1250870, by rfl⟩ : syracuseStep 1667827 = 2501741) B2501741
theorem B1758019 : Blo 1561478 1758019 := bstep (se 1 (by rfl) ⟨1318514, by rfl⟩ : syracuseStep 1758019 = 2637029) B2637029
theorem B8893253 : Blo 1561478 8893253 := bstep (se 4 (by rfl) ⟨833742, by rfl⟩ : syracuseStep 8893253 = 1667485) B1667485
theorem B5272397 : Blo 1561478 5272397 := bstep (se 3 (by rfl) ⟨988574, by rfl⟩ : syracuseStep 5272397 = 1977149) B1977149
theorem B2225011 : Blo 1561478 2225011 := bstep (se 1 (by rfl) ⟨1668758, by rfl⟩ : syracuseStep 2225011 = 3337517) B3337517
theorem B5272451 : Blo 1561478 5272451 := bstep (se 1 (by rfl) ⟨3954338, by rfl⟩ : syracuseStep 5272451 = 7908677) B7908677
theorem B3339139 : Blo 1561478 3339139 := bstep (se 1 (by rfl) ⟨2504354, by rfl⟩ : syracuseStep 3339139 = 5008709) B5008709
theorem B1561491 : Blo 1561478 1561491 := bstep (se 1 (by rfl) ⟨1171118, by rfl⟩ : syracuseStep 1561491 = 2342237) B2342237
theorem B1561507 : Blo 1561478 1561507 := bstep (se 1 (by rfl) ⟨1171130, by rfl⟩ : syracuseStep 1561507 = 2342261) B2342261
theorem B1561523 : Blo 1561478 1561523 := bstep (se 1 (by rfl) ⟨1171142, by rfl⟩ : syracuseStep 1561523 = 2342285) B2342285
theorem B1561539 : Blo 1561478 1561539 := bstep (se 1 (by rfl) ⟨1171154, by rfl⟩ : syracuseStep 1561539 = 2342309) B2342309
theorem B3806147 : Blo 1561478 3806147 := bstep (se 1 (by rfl) ⟨2854610, by rfl⟩ : syracuseStep 3806147 = 5709221) B5709221
theorem B11858885 : Blo 1561478 11858885 := bstep (se 4 (by rfl) ⟨1111770, by rfl⟩ : syracuseStep 11858885 = 2223541) B2223541
theorem B6673357 : Blo 1561478 6673357 := bstep (se 3 (by rfl) ⟨1251254, by rfl⟩ : syracuseStep 6673357 = 2502509) B2502509
theorem B1561555 : Blo 1561478 1561555 := bstep (se 1 (by rfl) ⟨1171166, by rfl⟩ : syracuseStep 1561555 = 2342333) B2342333
theorem B1758163 : Blo 1561478 1758163 := bstep (se 1 (by rfl) ⟨1318622, by rfl⟩ : syracuseStep 1758163 = 2637245) B2637245
theorem B1561571 : Blo 1561478 1561571 := bstep (se 1 (by rfl) ⟨1171178, by rfl⟩ : syracuseStep 1561571 = 2342357) B2342357
theorem B4223981 : Blo 1561478 4223981 := bstep (se 3 (by rfl) ⟨791996, by rfl⟩ : syracuseStep 4223981 = 1583993) B1583993
theorem B1561587 : Blo 1561478 1561587 := bstep (se 1 (by rfl) ⟨1171190, by rfl⟩ : syracuseStep 1561587 = 2342381) B2342381
theorem B1561603 : Blo 1561478 1561603 := bstep (se 1 (by rfl) ⟨1171202, by rfl⟩ : syracuseStep 1561603 = 2342405) B2342405
theorem B11269133 : Blo 1561478 11269133 := bstep (se 3 (by rfl) ⟨2112962, by rfl⟩ : syracuseStep 11269133 = 4225925) B4225925
theorem B3953681 : Blo 1561478 3953681 := bstep (se 2 (by rfl) ⟨1482630, by rfl⟩ : syracuseStep 3953681 = 2965261) B2965261
theorem B1561619 : Blo 1561478 1561619 := bstep (se 1 (by rfl) ⟨1171214, by rfl⟩ : syracuseStep 1561619 = 2342429) B2342429
theorem B1561635 : Blo 1561478 1561635 := bstep (se 1 (by rfl) ⟨1171226, by rfl⟩ : syracuseStep 1561635 = 2342453) B2342453
theorem B1561651 : Blo 1561478 1561651 := bstep (se 1 (by rfl) ⟨1171238, by rfl⟩ : syracuseStep 1561651 = 2342477) B2342477
theorem B1561667 : Blo 1561478 1561667 := bstep (se 1 (by rfl) ⟨1171250, by rfl⟩ : syracuseStep 1561667 = 2342501) B2342501
theorem B3953731 : Blo 1561478 3953731 := bstep (se 1 (by rfl) ⟨2965298, by rfl⟩ : syracuseStep 3953731 = 5930597) B5930597
theorem B1561683 : Blo 1561478 1561683 := bstep (se 1 (by rfl) ⟨1171262, by rfl⟩ : syracuseStep 1561683 = 2342525) B2342525
theorem B1561699 : Blo 1561478 1561699 := bstep (se 1 (by rfl) ⟨1171274, by rfl⟩ : syracuseStep 1561699 = 2342549) B2342549
theorem B1758307 : Blo 1561478 1758307 := bstep (se 1 (by rfl) ⟨1318730, by rfl⟩ : syracuseStep 1758307 = 2637461) B2637461
theorem B4510829 : Blo 1561478 4510829 := bstep (se 3 (by rfl) ⟨845780, by rfl⟩ : syracuseStep 4510829 = 1691561) B1691561
theorem B2110579 : Blo 1561478 2110579 := bstep (se 1 (by rfl) ⟨1582934, by rfl⟩ : syracuseStep 2110579 = 3165869) B3165869
theorem B1561715 : Blo 1561478 1561715 := bstep (se 1 (by rfl) ⟨1171286, by rfl⟩ : syracuseStep 1561715 = 2342573) B2342573
theorem B1561731 : Blo 1561478 1561731 := bstep (se 1 (by rfl) ⟨1171298, by rfl⟩ : syracuseStep 1561731 = 2342597) B2342597
theorem B5272721 : Blo 1561478 5272721 := bstep (se 2 (by rfl) ⟨1977270, by rfl⟩ : syracuseStep 5272721 = 3954541) B3954541
theorem B1561747 : Blo 1561478 1561747 := bstep (se 1 (by rfl) ⟨1171310, by rfl⟩ : syracuseStep 1561747 = 2342621) B2342621
theorem B1561763 : Blo 1561478 1561763 := bstep (se 1 (by rfl) ⟨1171322, by rfl⟩ : syracuseStep 1561763 = 2342645) B2342645
theorem B1561779 : Blo 1561478 1561779 := bstep (se 1 (by rfl) ⟨1171334, by rfl⟩ : syracuseStep 1561779 = 2342669) B2342669
theorem B1561795 : Blo 1561478 1561795 := bstep (se 1 (by rfl) ⟨1171346, by rfl⟩ : syracuseStep 1561795 = 2342693) B2342693
theorem B3953873 : Blo 1561478 3953873 := bstep (se 2 (by rfl) ⟨1482702, by rfl⟩ : syracuseStep 3953873 = 2965405) B2965405
theorem B1561811 : Blo 1561478 1561811 := bstep (se 1 (by rfl) ⟨1171358, by rfl⟩ : syracuseStep 1561811 = 2342717) B2342717
theorem B1561827 : Blo 1561478 1561827 := bstep (se 1 (by rfl) ⟨1171370, by rfl⟩ : syracuseStep 1561827 = 2342741) B2342741
theorem B1561843 : Blo 1561478 1561843 := bstep (se 1 (by rfl) ⟨1171382, by rfl⟩ : syracuseStep 1561843 = 2342765) B2342765
theorem B1758451 : Blo 1561478 1758451 := bstep (se 1 (by rfl) ⟨1318838, by rfl⟩ : syracuseStep 1758451 = 2637677) B2637677
theorem B1561859 : Blo 1561478 1561859 := bstep (se 1 (by rfl) ⟨1171394, by rfl⟩ : syracuseStep 1561859 = 2342789) B2342789
theorem B2004227 : Blo 1561478 2004227 := bstep (se 1 (by rfl) ⟨1503170, by rfl⟩ : syracuseStep 2004227 = 3006341) B3006341
theorem B8893709 : Blo 1561478 8893709 := bstep (se 3 (by rfl) ⟨1667570, by rfl⟩ : syracuseStep 8893709 = 3335141) B3335141
theorem B1561875 : Blo 1561478 1561875 := bstep (se 1 (by rfl) ⟨1171406, by rfl⟩ : syracuseStep 1561875 = 2342813) B2342813
theorem B1561891 : Blo 1561478 1561891 := bstep (se 1 (by rfl) ⟨1171418, by rfl⟩ : syracuseStep 1561891 = 2342837) B2342837
theorem B4224305 : Blo 1561478 4224305 := bstep (se 2 (by rfl) ⟨1584114, by rfl⟩ : syracuseStep 4224305 = 3168229) B3168229
theorem B1561907 : Blo 1561478 1561907 := bstep (se 1 (by rfl) ⟨1171430, by rfl⟩ : syracuseStep 1561907 = 2342861) B2342861
theorem B1561923 : Blo 1561478 1561923 := bstep (se 1 (by rfl) ⟨1171442, by rfl⟩ : syracuseStep 1561923 = 2342885) B2342885
theorem B2110801 : Blo 1561478 2110801 := bstep (se 2 (by rfl) ⟨791550, by rfl⟩ : syracuseStep 2110801 = 1583101) B1583101
theorem B1561939 : Blo 1561478 1561939 := bstep (se 1 (by rfl) ⟨1171454, by rfl⟩ : syracuseStep 1561939 = 2342909) B2342909
theorem B2635105 : Blo 1561478 2635105 := bstep (se 2 (by rfl) ⟨988164, by rfl⟩ : syracuseStep 2635105 = 1976329) B1976329
theorem B1561955 : Blo 1561478 1561955 := bstep (se 1 (by rfl) ⟨1171466, by rfl⟩ : syracuseStep 1561955 = 2342933) B2342933
theorem B8902001 : Blo 1561478 8902001 := bstep (se 2 (by rfl) ⟨3338250, by rfl⟩ : syracuseStep 8902001 = 6676501) B6676501
theorem B1561971 : Blo 1561478 1561971 := bstep (se 1 (by rfl) ⟨1171478, by rfl⟩ : syracuseStep 1561971 = 2342957) B2342957
theorem B2635139 : Blo 1561478 2635139 := bstep (se 1 (by rfl) ⟨1976354, by rfl⟩ : syracuseStep 2635139 = 3952709) B3952709
theorem B1561987 : Blo 1561478 1561987 := bstep (se 1 (by rfl) ⟨1171490, by rfl⟩ : syracuseStep 1561987 = 2342981) B2342981
theorem B1758595 : Blo 1561478 1758595 := bstep (se 1 (by rfl) ⟨1318946, by rfl⟩ : syracuseStep 1758595 = 2637893) B2637893
theorem B1562003 : Blo 1561478 1562003 := bstep (se 1 (by rfl) ⟨1171502, by rfl⟩ : syracuseStep 1562003 = 2343005) B2343005
theorem B2225569 : Blo 1561478 2225569 := bstep (se 2 (by rfl) ⟨834588, by rfl⟩ : syracuseStep 2225569 = 1669177) B1669177
theorem B1562019 : Blo 1561478 1562019 := bstep (se 1 (by rfl) ⟨1171514, by rfl⟩ : syracuseStep 1562019 = 2343029) B2343029
theorem B1562035 : Blo 1561478 1562035 := bstep (se 1 (by rfl) ⟨1171526, by rfl⟩ : syracuseStep 1562035 = 2343053) B2343053
theorem B1562051 : Blo 1561478 1562051 := bstep (se 1 (by rfl) ⟨1171538, by rfl⟩ : syracuseStep 1562051 = 2343077) B2343077
theorem B2225603 : Blo 1561478 2225603 := bstep (se 1 (by rfl) ⟨1669202, by rfl⟩ : syracuseStep 2225603 = 3338405) B3338405
theorem B1562067 : Blo 1561478 1562067 := bstep (se 1 (by rfl) ⟨1171550, by rfl⟩ : syracuseStep 1562067 = 2343101) B2343101
theorem B1562083 : Blo 1561478 1562083 := bstep (se 1 (by rfl) ⟨1171562, by rfl⟩ : syracuseStep 1562083 = 2343125) B2343125
theorem B5707235 : Blo 1561478 5707235 := bstep (se 1 (by rfl) ⟨4280426, by rfl⟩ : syracuseStep 5707235 = 8560853) B8560853
theorem B11867633 : Blo 1561478 11867633 := bstep (se 2 (by rfl) ⟨4450362, by rfl⟩ : syracuseStep 11867633 = 8900725) B8900725
theorem B1562099 : Blo 1561478 1562099 := bstep (se 1 (by rfl) ⟨1171574, by rfl⟩ : syracuseStep 1562099 = 2343149) B2343149
theorem B2635267 : Blo 1561478 2635267 := bstep (se 1 (by rfl) ⟨1976450, by rfl⟩ : syracuseStep 2635267 = 3952901) B3952901
theorem B1562115 : Blo 1561478 1562115 := bstep (se 1 (by rfl) ⟨1171586, by rfl⟩ : syracuseStep 1562115 = 2343173) B2343173
theorem B1562131 : Blo 1561478 1562131 := bstep (se 1 (by rfl) ⟨1171598, by rfl⟩ : syracuseStep 1562131 = 2343197) B2343197
theorem B1758739 : Blo 1561478 1758739 := bstep (se 1 (by rfl) ⟨1319054, by rfl⟩ : syracuseStep 1758739 = 2638109) B2638109
theorem B1562147 : Blo 1561478 1562147 := bstep (se 1 (by rfl) ⟨1171610, by rfl⟩ : syracuseStep 1562147 = 2343221) B2343221
theorem B1562163 : Blo 1561478 1562163 := bstep (se 1 (by rfl) ⟨1171622, by rfl⟩ : syracuseStep 1562163 = 2343245) B2343245
theorem B1562179 : Blo 1561478 1562179 := bstep (se 1 (by rfl) ⟨1171634, by rfl⟩ : syracuseStep 1562179 = 2343269) B2343269
theorem B1562195 : Blo 1561478 1562195 := bstep (se 1 (by rfl) ⟨1171646, by rfl⟩ : syracuseStep 1562195 = 2343293) B2343293
theorem B1562211 : Blo 1561478 1562211 := bstep (se 1 (by rfl) ⟨1171658, by rfl⟩ : syracuseStep 1562211 = 2343317) B2343317
theorem B10016369 : Blo 1561478 10016369 := bstep (se 2 (by rfl) ⟨3756138, by rfl⟩ : syracuseStep 10016369 = 7512277) B7512277
theorem B1562227 : Blo 1561478 1562227 := bstep (se 1 (by rfl) ⟨1171670, by rfl⟩ : syracuseStep 1562227 = 2343341) B2343341
theorem B1562243 : Blo 1561478 1562243 := bstep (se 1 (by rfl) ⟨1171682, by rfl⟩ : syracuseStep 1562243 = 2343365) B2343365
theorem B13350541 : Blo 1561478 13350541 := bstep (se 3 (by rfl) ⟨2503226, by rfl⟩ : syracuseStep 13350541 = 5006453) B5006453
theorem B2635409 : Blo 1561478 2635409 := bstep (se 2 (by rfl) ⟨988278, by rfl⟩ : syracuseStep 2635409 = 1976557) B1976557
theorem B1562259 : Blo 1561478 1562259 := bstep (se 1 (by rfl) ⟨1171694, by rfl⟩ : syracuseStep 1562259 = 2343389) B2343389
theorem B1562275 : Blo 1561478 1562275 := bstep (se 1 (by rfl) ⟨1171706, by rfl⟩ : syracuseStep 1562275 = 2343413) B2343413
theorem B1758883 : Blo 1561478 1758883 := bstep (se 1 (by rfl) ⟨1319162, by rfl⟩ : syracuseStep 1758883 = 2638325) B2638325
theorem B5273261 : Blo 1561478 5273261 := bstep (se 3 (by rfl) ⟨988736, by rfl⟩ : syracuseStep 5273261 = 1977473) B1977473
theorem B9508529 : Blo 1561478 9508529 := bstep (se 2 (by rfl) ⟨3565698, by rfl⟩ : syracuseStep 9508529 = 7131397) B7131397
theorem B1562291 : Blo 1561478 1562291 := bstep (se 1 (by rfl) ⟨1171718, by rfl⟩ : syracuseStep 1562291 = 2343437) B2343437
theorem B1562307 : Blo 1561478 1562307 := bstep (se 1 (by rfl) ⟨1171730, by rfl⟩ : syracuseStep 1562307 = 2343461) B2343461
theorem B3806929 : Blo 1561478 3806929 := bstep (se 2 (by rfl) ⟨1427598, by rfl⟩ : syracuseStep 3806929 = 2855197) B2855197
theorem B1562323 : Blo 1561478 1562323 := bstep (se 1 (by rfl) ⟨1171742, by rfl⟩ : syracuseStep 1562323 = 2343485) B2343485
theorem B1562339 : Blo 1561478 1562339 := bstep (se 1 (by rfl) ⟨1171754, by rfl⟩ : syracuseStep 1562339 = 2343509) B2343509
theorem B5273315 : Blo 1561478 5273315 := bstep (se 1 (by rfl) ⟨3954986, by rfl⟩ : syracuseStep 5273315 = 7909973) B7909973
theorem B1562355 : Blo 1561478 1562355 := bstep (se 1 (by rfl) ⟨1171766, by rfl⟩ : syracuseStep 1562355 = 2343533) B2343533
theorem B2111233 : Blo 1561478 2111233 := bstep (se 2 (by rfl) ⟨791712, by rfl⟩ : syracuseStep 2111233 = 1583425) B1583425
theorem B1562371 : Blo 1561478 1562371 := bstep (se 1 (by rfl) ⟨1171778, by rfl⟩ : syracuseStep 1562371 = 2343557) B2343557
theorem B2635537 : Blo 1561478 2635537 := bstep (se 2 (by rfl) ⟨988326, by rfl⟩ : syracuseStep 2635537 = 1976653) B1976653
theorem B1562387 : Blo 1561478 1562387 := bstep (se 1 (by rfl) ⟨1171790, by rfl⟩ : syracuseStep 1562387 = 2343581) B2343581
theorem B1562403 : Blo 1561478 1562403 := bstep (se 1 (by rfl) ⟨1171802, by rfl⟩ : syracuseStep 1562403 = 2343605) B2343605
theorem B2635571 : Blo 1561478 2635571 := bstep (se 1 (by rfl) ⟨1976678, by rfl⟩ : syracuseStep 2635571 = 3953357) B3953357
theorem B1562419 : Blo 1561478 1562419 := bstep (se 1 (by rfl) ⟨1171814, by rfl⟩ : syracuseStep 1562419 = 2343629) B2343629
theorem B1562435 : Blo 1561478 1562435 := bstep (se 1 (by rfl) ⟨1171826, by rfl⟩ : syracuseStep 1562435 = 2343653) B2343653
theorem B1562451 : Blo 1561478 1562451 := bstep (se 1 (by rfl) ⟨1171838, by rfl⟩ : syracuseStep 1562451 = 2343677) B2343677
theorem B1562467 : Blo 1561478 1562467 := bstep (se 1 (by rfl) ⟨1171850, by rfl⟩ : syracuseStep 1562467 = 2343701) B2343701
theorem B2815843 : Blo 1561478 2815843 := bstep (se 1 (by rfl) ⟨2111882, by rfl⟩ : syracuseStep 2815843 = 4223765) B4223765
theorem B20027249 : Blo 1561478 20027249 := bstep (se 2 (by rfl) ⟨7510218, by rfl⟩ : syracuseStep 20027249 = 15020437) B15020437
theorem B1562483 : Blo 1561478 1562483 := bstep (se 1 (by rfl) ⟨1171862, by rfl⟩ : syracuseStep 1562483 = 2343725) B2343725
theorem B1562499 : Blo 1561478 1562499 := bstep (se 1 (by rfl) ⟨1171874, by rfl⟩ : syracuseStep 1562499 = 2343749) B2343749
theorem B1562515 : Blo 1561478 1562515 := bstep (se 1 (by rfl) ⟨1171886, by rfl⟩ : syracuseStep 1562515 = 2343773) B2343773
theorem B1562531 : Blo 1561478 1562531 := bstep (se 1 (by rfl) ⟨1171898, by rfl⟩ : syracuseStep 1562531 = 2343797) B2343797
theorem B2635699 : Blo 1561478 2635699 := bstep (se 1 (by rfl) ⟨1976774, by rfl⟩ : syracuseStep 2635699 = 3953549) B3953549
theorem B1562547 : Blo 1561478 1562547 := bstep (se 1 (by rfl) ⟨1171910, by rfl⟩ : syracuseStep 1562547 = 2343821) B2343821
theorem B1562563 : Blo 1561478 1562563 := bstep (se 1 (by rfl) ⟨1171922, by rfl⟩ : syracuseStep 1562563 = 2343845) B2343845
theorem B12662725 : Blo 1561478 12662725 := bstep (se 4 (by rfl) ⟨1187130, by rfl⟩ : syracuseStep 12662725 = 2374261) B2374261
theorem B1562579 : Blo 1561478 1562579 := bstep (se 1 (by rfl) ⟨1171934, by rfl⟩ : syracuseStep 1562579 = 2343869) B2343869
theorem B1562595 : Blo 1561478 1562595 := bstep (se 1 (by rfl) ⟨1171946, by rfl⟩ : syracuseStep 1562595 = 2343893) B2343893
theorem B1669091 : Blo 1561478 1669091 := bstep (se 1 (by rfl) ⟨1251818, by rfl⟩ : syracuseStep 1669091 = 2503637) B2503637
theorem B3381233 : Blo 1561478 3381233 := bstep (se 2 (by rfl) ⟨1267962, by rfl⟩ : syracuseStep 3381233 = 2535925) B2535925
theorem B5273585 : Blo 1561478 5273585 := bstep (se 2 (by rfl) ⟨1977594, by rfl⟩ : syracuseStep 5273585 = 3955189) B3955189
theorem B1562611 : Blo 1561478 1562611 := bstep (se 1 (by rfl) ⟨1171958, by rfl⟩ : syracuseStep 1562611 = 2343917) B2343917
theorem B1562627 : Blo 1561478 1562627 := bstep (se 1 (by rfl) ⟨1171970, by rfl⟩ : syracuseStep 1562627 = 2343941) B2343941
theorem B1562643 : Blo 1561478 1562643 := bstep (se 1 (by rfl) ⟨1171982, by rfl⟩ : syracuseStep 1562643 = 2343965) B2343965
theorem B8443939 : Blo 1561478 8443939 := bstep (se 1 (by rfl) ⟨6332954, by rfl⟩ : syracuseStep 8443939 = 12665909) B12665909
theorem B1562659 : Blo 1561478 1562659 := bstep (se 1 (by rfl) ⟨1171994, by rfl⟩ : syracuseStep 1562659 = 2343989) B2343989
theorem B1562675 : Blo 1561478 1562675 := bstep (se 1 (by rfl) ⟨1172006, by rfl⟩ : syracuseStep 1562675 = 2344013) B2344013
theorem B2635841 : Blo 1561478 2635841 := bstep (se 2 (by rfl) ⟨988440, by rfl⟩ : syracuseStep 2635841 = 1976881) B1976881
theorem B1562691 : Blo 1561478 1562691 := bstep (se 1 (by rfl) ⟨1172018, by rfl⟩ : syracuseStep 1562691 = 2344037) B2344037
theorem B1562707 : Blo 1561478 1562707 := bstep (se 1 (by rfl) ⟨1172030, by rfl⟩ : syracuseStep 1562707 = 2344061) B2344061
theorem B1562723 : Blo 1561478 1562723 := bstep (se 1 (by rfl) ⟨1172042, by rfl⟩ : syracuseStep 1562723 = 2344085) B2344085
theorem B4749425 : Blo 1561478 4749425 := bstep (se 2 (by rfl) ⟨1781034, by rfl⟩ : syracuseStep 4749425 = 3562069) B3562069
theorem B1562739 : Blo 1561478 1562739 := bstep (se 1 (by rfl) ⟨1172054, by rfl⟩ : syracuseStep 1562739 = 2344109) B2344109
theorem B1562755 : Blo 1561478 1562755 := bstep (se 1 (by rfl) ⟨1172066, by rfl⟩ : syracuseStep 1562755 = 2344133) B2344133
theorem B1562771 : Blo 1561478 1562771 := bstep (se 1 (by rfl) ⟨1172078, by rfl⟩ : syracuseStep 1562771 = 2344157) B2344157
theorem B1562787 : Blo 1561478 1562787 := bstep (se 1 (by rfl) ⟨1172090, by rfl⟩ : syracuseStep 1562787 = 2344181) B2344181
theorem B3954865 : Blo 1561478 3954865 := bstep (se 2 (by rfl) ⟨1483074, by rfl⟩ : syracuseStep 3954865 = 2966149) B2966149
theorem B1562803 : Blo 1561478 1562803 := bstep (se 1 (by rfl) ⟨1172102, by rfl⟩ : syracuseStep 1562803 = 2344205) B2344205
theorem B2635969 : Blo 1561478 2635969 := bstep (se 2 (by rfl) ⟨988488, by rfl⟩ : syracuseStep 2635969 = 1976977) B1976977
theorem B1562819 : Blo 1561478 1562819 := bstep (se 1 (by rfl) ⟨1172114, by rfl⟩ : syracuseStep 1562819 = 2344229) B2344229
theorem B1562835 : Blo 1561478 1562835 := bstep (se 1 (by rfl) ⟨1172126, by rfl⟩ : syracuseStep 1562835 = 2344253) B2344253
theorem B2636003 : Blo 1561478 2636003 := bstep (se 1 (by rfl) ⟨1977002, by rfl⟩ : syracuseStep 2636003 = 3954005) B3954005
theorem B1562851 : Blo 1561478 1562851 := bstep (se 1 (by rfl) ⟨1172138, by rfl⟩ : syracuseStep 1562851 = 2344277) B2344277
theorem B1562867 : Blo 1561478 1562867 := bstep (se 1 (by rfl) ⟨1172150, by rfl⟩ : syracuseStep 1562867 = 2344301) B2344301
theorem B1562883 : Blo 1561478 1562883 := bstep (se 1 (by rfl) ⟨1172162, by rfl⟩ : syracuseStep 1562883 = 2344325) B2344325
theorem B1562899 : Blo 1561478 1562899 := bstep (se 1 (by rfl) ⟨1172174, by rfl⟩ : syracuseStep 1562899 = 2344349) B2344349
theorem B1562915 : Blo 1561478 1562915 := bstep (se 1 (by rfl) ⟨1172186, by rfl⟩ : syracuseStep 1562915 = 2344373) B2344373
theorem B1562931 : Blo 1561478 1562931 := bstep (se 1 (by rfl) ⟨1172198, by rfl⟩ : syracuseStep 1562931 = 2344397) B2344397
theorem B1562947 : Blo 1561478 1562947 := bstep (se 1 (by rfl) ⟨1172210, by rfl⟩ : syracuseStep 1562947 = 2344421) B2344421
theorem B1562963 : Blo 1561478 1562963 := bstep (se 1 (by rfl) ⟨1172222, by rfl⟩ : syracuseStep 1562963 = 2344445) B2344445
theorem B2636131 : Blo 1561478 2636131 := bstep (se 1 (by rfl) ⟨1977098, by rfl⟩ : syracuseStep 2636131 = 3954197) B3954197
theorem B1562979 : Blo 1561478 1562979 := bstep (se 1 (by rfl) ⟨1172234, by rfl⟩ : syracuseStep 1562979 = 2344469) B2344469
theorem B15022435 : Blo 1561478 15022435 := bstep (se 1 (by rfl) ⟨11266826, by rfl⟩ : syracuseStep 15022435 = 22533653) B22533653
theorem B1562995 : Blo 1561478 1562995 := bstep (se 1 (by rfl) ⟨1172246, by rfl⟩ : syracuseStep 1562995 = 2344493) B2344493
theorem B1563011 : Blo 1561478 1563011 := bstep (se 1 (by rfl) ⟨1172258, by rfl⟩ : syracuseStep 1563011 = 2344517) B2344517
theorem B1563027 : Blo 1561478 1563027 := bstep (se 1 (by rfl) ⟨1172270, by rfl⟩ : syracuseStep 1563027 = 2344541) B2344541
theorem B1563043 : Blo 1561478 1563043 := bstep (se 1 (by rfl) ⟨1172282, by rfl⟩ : syracuseStep 1563043 = 2344565) B2344565
theorem B1563059 : Blo 1561478 1563059 := bstep (se 1 (by rfl) ⟨1172294, by rfl⟩ : syracuseStep 1563059 = 2344589) B2344589
theorem B3955139 : Blo 1561478 3955139 := bstep (se 1 (by rfl) ⟨2966354, by rfl⟩ : syracuseStep 3955139 = 5932709) B5932709
theorem B1563075 : Blo 1561478 1563075 := bstep (se 1 (by rfl) ⟨1172306, by rfl⟩ : syracuseStep 1563075 = 2344613) B2344613
theorem B1563091 : Blo 1561478 1563091 := bstep (se 1 (by rfl) ⟨1172318, by rfl⟩ : syracuseStep 1563091 = 2344637) B2344637
theorem B1563107 : Blo 1561478 1563107 := bstep (se 1 (by rfl) ⟨1172330, by rfl⟩ : syracuseStep 1563107 = 2344661) B2344661
theorem B4225517 : Blo 1561478 4225517 := bstep (se 3 (by rfl) ⟨792284, by rfl⟩ : syracuseStep 4225517 = 1584569) B1584569
theorem B2636273 : Blo 1561478 2636273 := bstep (se 2 (by rfl) ⟨988602, by rfl⟩ : syracuseStep 2636273 = 1977205) B1977205
theorem B1563123 : Blo 1561478 1563123 := bstep (se 1 (by rfl) ⟨1172342, by rfl⟩ : syracuseStep 1563123 = 2344685) B2344685
theorem B1563139 : Blo 1561478 1563139 := bstep (se 1 (by rfl) ⟨1172354, by rfl⟩ : syracuseStep 1563139 = 2344709) B2344709
theorem B5274125 : Blo 1561478 5274125 := bstep (se 3 (by rfl) ⟨988898, by rfl⟩ : syracuseStep 5274125 = 1977797) B1977797
theorem B1563155 : Blo 1561478 1563155 := bstep (se 1 (by rfl) ⟨1172366, by rfl⟩ : syracuseStep 1563155 = 2344733) B2344733
theorem B1563171 : Blo 1561478 1563171 := bstep (se 1 (by rfl) ⟨1172378, by rfl⟩ : syracuseStep 1563171 = 2344757) B2344757
theorem B1563187 : Blo 1561478 1563187 := bstep (se 1 (by rfl) ⟨1172390, by rfl⟩ : syracuseStep 1563187 = 2344781) B2344781
theorem B5274179 : Blo 1561478 5274179 := bstep (se 1 (by rfl) ⟨3955634, by rfl⟩ : syracuseStep 5274179 = 7911269) B7911269
theorem B1563203 : Blo 1561478 1563203 := bstep (se 1 (by rfl) ⟨1172402, by rfl⟩ : syracuseStep 1563203 = 2344805) B2344805
theorem B1563219 : Blo 1561478 1563219 := bstep (se 1 (by rfl) ⟨1172414, by rfl⟩ : syracuseStep 1563219 = 2344829) B2344829
theorem B11262563 : Blo 1561478 11262563 := bstep (se 1 (by rfl) ⟨8446922, by rfl⟩ : syracuseStep 11262563 = 16893845) B16893845
theorem B1563235 : Blo 1561478 1563235 := bstep (se 1 (by rfl) ⟨1172426, by rfl⟩ : syracuseStep 1563235 = 2344853) B2344853
theorem B2005603 : Blo 1561478 2005603 := bstep (se 1 (by rfl) ⟨1504202, by rfl⟩ : syracuseStep 2005603 = 3008405) B3008405
theorem B2636401 : Blo 1561478 2636401 := bstep (se 2 (by rfl) ⟨988650, by rfl⟩ : syracuseStep 2636401 = 1977301) B1977301
theorem B1563251 : Blo 1561478 1563251 := bstep (se 1 (by rfl) ⟨1172438, by rfl⟩ : syracuseStep 1563251 = 2344877) B2344877
theorem B3955331 : Blo 1561478 3955331 := bstep (se 1 (by rfl) ⟨2966498, by rfl⟩ : syracuseStep 3955331 = 5932997) B5932997
theorem B1563267 : Blo 1561478 1563267 := bstep (se 1 (by rfl) ⟨1172450, by rfl⟩ : syracuseStep 1563267 = 2344901) B2344901
theorem B2636435 : Blo 1561478 2636435 := bstep (se 1 (by rfl) ⟨1977326, by rfl⟩ : syracuseStep 2636435 = 3954653) B3954653
theorem B1563283 : Blo 1561478 1563283 := bstep (se 1 (by rfl) ⟨1172462, by rfl⟩ : syracuseStep 1563283 = 2344925) B2344925
theorem B1563299 : Blo 1561478 1563299 := bstep (se 1 (by rfl) ⟨1172474, by rfl⟩ : syracuseStep 1563299 = 2344949) B2344949
theorem B1563315 : Blo 1561478 1563315 := bstep (se 1 (by rfl) ⟨1172486, by rfl⟩ : syracuseStep 1563315 = 2344973) B2344973
theorem B1563331 : Blo 1561478 1563331 := bstep (se 1 (by rfl) ⟨1172498, by rfl⟩ : syracuseStep 1563331 = 2344997) B2344997
theorem B1563347 : Blo 1561478 1563347 := bstep (se 1 (by rfl) ⟨1172510, by rfl⟩ : syracuseStep 1563347 = 2345021) B2345021
theorem B1563363 : Blo 1561478 1563363 := bstep (se 1 (by rfl) ⟨1172522, by rfl⟩ : syracuseStep 1563363 = 2345045) B2345045
theorem B1563379 : Blo 1561478 1563379 := bstep (se 1 (by rfl) ⟨1172534, by rfl⟩ : syracuseStep 1563379 = 2345069) B2345069
theorem B1563395 : Blo 1561478 1563395 := bstep (se 1 (by rfl) ⟨1172546, by rfl⟩ : syracuseStep 1563395 = 2345093) B2345093
theorem B2636563 : Blo 1561478 2636563 := bstep (se 1 (by rfl) ⟨1977422, by rfl⟩ : syracuseStep 2636563 = 3954845) B3954845
theorem B1563411 : Blo 1561478 1563411 := bstep (se 1 (by rfl) ⟨1172558, by rfl⟩ : syracuseStep 1563411 = 2345117) B2345117
theorem B8903459 : Blo 1561478 8903459 := bstep (se 1 (by rfl) ⟨6677594, by rfl⟩ : syracuseStep 8903459 = 13355189) B13355189
theorem B1563427 : Blo 1561478 1563427 := bstep (se 1 (by rfl) ⟨1172570, by rfl⟩ : syracuseStep 1563427 = 2345141) B2345141
theorem B7912241 : Blo 1561478 7912241 := bstep (se 2 (by rfl) ⟨2967090, by rfl⟩ : syracuseStep 7912241 = 5934181) B5934181
theorem B1563443 : Blo 1561478 1563443 := bstep (se 1 (by rfl) ⟨1172582, by rfl⟩ : syracuseStep 1563443 = 2345165) B2345165
theorem B1563459 : Blo 1561478 1563459 := bstep (se 1 (by rfl) ⟨1172594, by rfl⟩ : syracuseStep 1563459 = 2345189) B2345189
theorem B5274449 : Blo 1561478 5274449 := bstep (se 2 (by rfl) ⟨1977918, by rfl⟩ : syracuseStep 5274449 = 3955837) B3955837
theorem B1563475 : Blo 1561478 1563475 := bstep (se 1 (by rfl) ⟨1172606, by rfl⟩ : syracuseStep 1563475 = 2345213) B2345213
theorem B2636705 : Blo 1561478 2636705 := bstep (se 2 (by rfl) ⟨988764, by rfl⟩ : syracuseStep 2636705 = 1977529) B1977529
theorem B13351877 : Blo 1561478 13351877 := bstep (se 4 (by rfl) ⟨1251738, by rfl⟩ : syracuseStep 13351877 = 2503477) B2503477
theorem B2964433 : Blo 1561478 2964433 := bstep (se 2 (by rfl) ⟨1111662, by rfl⟩ : syracuseStep 2964433 = 2223325) B2223325
theorem B3513329 : Blo 1561478 3513329 := bstep (se 2 (by rfl) ⟨1317498, by rfl⟩ : syracuseStep 3513329 = 2634997) B2634997
theorem B3513347 : Blo 1561478 3513347 := bstep (se 1 (by rfl) ⟨2635010, by rfl⟩ : syracuseStep 3513347 = 5270021) B5270021
theorem B5004301 : Blo 1561478 5004301 := bstep (se 3 (by rfl) ⟨938306, by rfl⟩ : syracuseStep 5004301 = 1876613) B1876613
theorem B2636833 : Blo 1561478 2636833 := bstep (se 2 (by rfl) ⟨988812, by rfl⟩ : syracuseStep 2636833 = 1977625) B1977625
theorem B2636867 : Blo 1561478 2636867 := bstep (se 1 (by rfl) ⟨1977650, by rfl⟩ : syracuseStep 2636867 = 3955301) B3955301
theorem B2964593 : Blo 1561478 2964593 := bstep (se 2 (by rfl) ⟨1111722, by rfl⟩ : syracuseStep 2964593 = 2223445) B2223445
theorem B4447345 : Blo 1561478 4447345 := bstep (se 2 (by rfl) ⟨1667754, by rfl⟩ : syracuseStep 4447345 = 3335509) B3335509
theorem B2636995 : Blo 1561478 2636995 := bstep (se 1 (by rfl) ⟨1977746, by rfl⟩ : syracuseStep 2636995 = 3955493) B3955493
theorem B3513617 : Blo 1561478 3513617 := bstep (se 2 (by rfl) ⟨1317606, by rfl⟩ : syracuseStep 3513617 = 2635213) B2635213
theorem B3513635 : Blo 1561478 3513635 := bstep (se 1 (by rfl) ⟨2635226, by rfl⟩ : syracuseStep 3513635 = 5270453) B5270453
theorem B2342225 : Blo 1561478 2342225 := bstep (se 2 (by rfl) ⟨878334, by rfl⟩ : syracuseStep 2342225 = 1756669) B1756669
theorem B2637137 : Blo 1561478 2637137 := bstep (se 2 (by rfl) ⟨988926, by rfl⟩ : syracuseStep 2637137 = 1977853) B1977853
theorem B2342243 : Blo 1561478 2342243 := bstep (se 1 (by rfl) ⟨1756682, by rfl⟩ : syracuseStep 2342243 = 3513365) B3513365
theorem B5274989 : Blo 1561478 5274989 := bstep (se 3 (by rfl) ⟨989060, by rfl⟩ : syracuseStep 5274989 = 1978121) B1978121
theorem B2342273 : Blo 1561478 2342273 := bstep (se 2 (by rfl) ⟨878352, by rfl⟩ : syracuseStep 2342273 = 1756705) B1756705
theorem B4447619 : Blo 1561478 4447619 := bstep (se 1 (by rfl) ⟨3335714, by rfl⟩ : syracuseStep 4447619 = 6671429) B6671429
theorem B2342291 : Blo 1561478 2342291 := bstep (se 1 (by rfl) ⟨1756718, by rfl⟩ : syracuseStep 2342291 = 3513437) B3513437
theorem B5275043 : Blo 1561478 5275043 := bstep (se 1 (by rfl) ⟨3956282, by rfl⟩ : syracuseStep 5275043 = 7912565) B7912565
theorem B2342321 : Blo 1561478 2342321 := bstep (se 2 (by rfl) ⟨878370, by rfl⟩ : syracuseStep 2342321 = 1756741) B1756741
theorem B2342339 : Blo 1561478 2342339 := bstep (se 1 (by rfl) ⟨1756754, by rfl⟩ : syracuseStep 2342339 = 3513509) B3513509
theorem B2637265 : Blo 1561478 2637265 := bstep (se 2 (by rfl) ⟨988974, by rfl⟩ : syracuseStep 2637265 = 1977949) B1977949
theorem B2342369 : Blo 1561478 2342369 := bstep (se 2 (by rfl) ⟨878388, by rfl⟩ : syracuseStep 2342369 = 1756777) B1756777
theorem B2342387 : Blo 1561478 2342387 := bstep (se 1 (by rfl) ⟨1756790, by rfl⟩ : syracuseStep 2342387 = 3513581) B3513581
theorem B2637299 : Blo 1561478 2637299 := bstep (se 1 (by rfl) ⟨1977974, by rfl⟩ : syracuseStep 2637299 = 3955949) B3955949
theorem B2964995 : Blo 1561478 2964995 := bstep (se 1 (by rfl) ⟨2223746, by rfl⟩ : syracuseStep 2964995 = 4447493) B4447493
theorem B2342417 : Blo 1561478 2342417 := bstep (se 2 (by rfl) ⟨878406, by rfl⟩ : syracuseStep 2342417 = 1756813) B1756813
theorem B2342435 : Blo 1561478 2342435 := bstep (se 1 (by rfl) ⟨1756826, by rfl⟩ : syracuseStep 2342435 = 3513653) B3513653
theorem B3513905 : Blo 1561478 3513905 := bstep (se 2 (by rfl) ⟨1317714, by rfl⟩ : syracuseStep 3513905 = 2635429) B2635429
theorem B3956273 : Blo 1561478 3956273 := bstep (se 2 (by rfl) ⟨1483602, by rfl⟩ : syracuseStep 3956273 = 2967205) B2967205
theorem B2342465 : Blo 1561478 2342465 := bstep (se 2 (by rfl) ⟨878424, by rfl⟩ : syracuseStep 2342465 = 1756849) B1756849
theorem B3513923 : Blo 1561478 3513923 := bstep (se 1 (by rfl) ⟨2635442, by rfl⟩ : syracuseStep 3513923 = 5270885) B5270885
theorem B4447811 : Blo 1561478 4447811 := bstep (se 1 (by rfl) ⟨3335858, by rfl⟩ : syracuseStep 4447811 = 6671717) B6671717
theorem B2342483 : Blo 1561478 2342483 := bstep (se 1 (by rfl) ⟨1756862, by rfl⟩ : syracuseStep 2342483 = 3513725) B3513725
theorem B3956323 : Blo 1561478 3956323 := bstep (se 1 (by rfl) ⟨2967242, by rfl⟩ : syracuseStep 3956323 = 5934485) B5934485
theorem B2342513 : Blo 1561478 2342513 := bstep (se 2 (by rfl) ⟨878442, by rfl⟩ : syracuseStep 2342513 = 1756885) B1756885
theorem B3382897 : Blo 1561478 3382897 := bstep (se 2 (by rfl) ⟨1268586, by rfl⟩ : syracuseStep 3382897 = 2537173) B2537173
theorem B2637427 : Blo 1561478 2637427 := bstep (se 1 (by rfl) ⟨1978070, by rfl⟩ : syracuseStep 2637427 = 3956141) B3956141
theorem B2342531 : Blo 1561478 2342531 := bstep (se 1 (by rfl) ⟨1756898, by rfl⟩ : syracuseStep 2342531 = 3513797) B3513797
theorem B33808013 : Blo 1561478 33808013 := bstep (se 3 (by rfl) ⟨6339002, by rfl⟩ : syracuseStep 33808013 = 12678005) B12678005
theorem B2342561 : Blo 1561478 2342561 := bstep (se 2 (by rfl) ⟨878460, by rfl⟩ : syracuseStep 2342561 = 1756921) B1756921
theorem B5275313 : Blo 1561478 5275313 := bstep (se 2 (by rfl) ⟨1978242, by rfl⟩ : syracuseStep 5275313 = 3956485) B3956485
theorem B2342579 : Blo 1561478 2342579 := bstep (se 1 (by rfl) ⟨1756934, by rfl⟩ : syracuseStep 2342579 = 3513869) B3513869
theorem B2342609 : Blo 1561478 2342609 := bstep (se 2 (by rfl) ⟨878478, by rfl⟩ : syracuseStep 2342609 = 1756957) B1756957
theorem B2342627 : Blo 1561478 2342627 := bstep (se 1 (by rfl) ⟨1756970, by rfl⟩ : syracuseStep 2342627 = 3513941) B3513941
theorem B3956465 : Blo 1561478 3956465 := bstep (se 2 (by rfl) ⟨1483674, by rfl⟩ : syracuseStep 3956465 = 2967349) B2967349
theorem B2342657 : Blo 1561478 2342657 := bstep (se 2 (by rfl) ⟨878496, by rfl⟩ : syracuseStep 2342657 = 1756993) B1756993
theorem B2637569 : Blo 1561478 2637569 := bstep (se 2 (by rfl) ⟨989088, by rfl⟩ : syracuseStep 2637569 = 1978177) B1978177
theorem B5930765 : Blo 1561478 5930765 := bstep (se 3 (by rfl) ⟨1112018, by rfl⟩ : syracuseStep 5930765 = 2224037) B2224037
theorem B2285329 : Blo 1561478 2285329 := bstep (se 2 (by rfl) ⟨856998, by rfl⟩ : syracuseStep 2285329 = 1713997) B1713997
theorem B2342675 : Blo 1561478 2342675 := bstep (se 1 (by rfl) ⟨1757006, by rfl⟩ : syracuseStep 2342675 = 3514013) B3514013
theorem B2342705 : Blo 1561478 2342705 := bstep (se 2 (by rfl) ⟨878514, by rfl⟩ : syracuseStep 2342705 = 1757029) B1757029
theorem B2342723 : Blo 1561478 2342723 := bstep (se 1 (by rfl) ⟨1757042, by rfl⟩ : syracuseStep 2342723 = 3514085) B3514085
theorem B2031427 : Blo 1561478 2031427 := bstep (se 1 (by rfl) ⟨1523570, by rfl⟩ : syracuseStep 2031427 = 3047141) B3047141
theorem B3514193 : Blo 1561478 3514193 := bstep (se 2 (by rfl) ⟨1317822, by rfl⟩ : syracuseStep 3514193 = 2635645) B2635645
theorem B2342753 : Blo 1561478 2342753 := bstep (se 2 (by rfl) ⟨878532, by rfl⟩ : syracuseStep 2342753 = 1757065) B1757065
theorem B3514211 : Blo 1561478 3514211 := bstep (se 1 (by rfl) ⟨2635658, by rfl⟩ : syracuseStep 3514211 = 5271317) B5271317
theorem B2342771 : Blo 1561478 2342771 := bstep (se 1 (by rfl) ⟨1757078, by rfl⟩ : syracuseStep 2342771 = 3514157) B3514157
theorem B2637697 : Blo 1561478 2637697 := bstep (se 2 (by rfl) ⟨989136, by rfl⟩ : syracuseStep 2637697 = 1978273) B1978273
theorem B2342801 : Blo 1561478 2342801 := bstep (se 2 (by rfl) ⟨878550, by rfl⟩ : syracuseStep 2342801 = 1757101) B1757101
theorem B2375569 : Blo 1561478 2375569 := bstep (se 2 (by rfl) ⟨890838, by rfl⟩ : syracuseStep 2375569 = 1781677) B1781677
theorem B2342819 : Blo 1561478 2342819 := bstep (se 1 (by rfl) ⟨1757114, by rfl⟩ : syracuseStep 2342819 = 3514229) B3514229
theorem B2637731 : Blo 1561478 2637731 := bstep (se 1 (by rfl) ⟨1978298, by rfl⟩ : syracuseStep 2637731 = 3956597) B3956597
theorem B2342849 : Blo 1561478 2342849 := bstep (se 2 (by rfl) ⟨878568, by rfl⟩ : syracuseStep 2342849 = 1757137) B1757137
theorem B2342867 : Blo 1561478 2342867 := bstep (se 1 (by rfl) ⟨1757150, by rfl⟩ : syracuseStep 2342867 = 3514301) B3514301
theorem B2342897 : Blo 1561478 2342897 := bstep (se 2 (by rfl) ⟨878586, by rfl⟩ : syracuseStep 2342897 = 1757173) B1757173
theorem B3514391 : Blo 1561478 3514391 := bstep (se 1 (by rfl) ⟨2635793, by rfl⟩ : syracuseStep 3514391 = 5271587) B5271587
theorem B3956759 : Blo 1561478 3956759 := bstep (se 1 (by rfl) ⟨2967569, by rfl⟩ : syracuseStep 3956759 = 5935139) B5935139
theorem B19005475 : Blo 1561478 19005475 := bstep (se 1 (by rfl) ⟨14254106, by rfl⟩ : syracuseStep 19005475 = 28508213) B28508213
theorem B5931053 : Blo 1561478 5931053 := bstep (se 3 (by rfl) ⟨1112072, by rfl⟩ : syracuseStep 5931053 = 2224145) B2224145
theorem B12025921 : Blo 1561478 12025921 := bstep (se 2 (by rfl) ⟨4509720, by rfl⟩ : syracuseStep 12025921 = 9019441) B9019441
theorem B7913537 : Blo 1561478 7913537 := bstep (se 2 (by rfl) ⟨2967576, by rfl⟩ : syracuseStep 7913537 = 5935153) B5935153
theorem B2342987 : Blo 1561478 2342987 := bstep (se 1 (by rfl) ⟨1757240, by rfl⟩ : syracuseStep 2342987 = 3514481) B3514481
theorem B5931083 : Blo 1561478 5931083 := bstep (se 1 (by rfl) ⟨4448312, by rfl⟩ : syracuseStep 5931083 = 8896625) B8896625
theorem B2342999 : Blo 1561478 2342999 := bstep (se 1 (by rfl) ⟨1757249, by rfl⟩ : syracuseStep 2342999 = 3514499) B3514499
theorem B2637913 : Blo 1561478 2637913 := bstep (se 2 (by rfl) ⟨989217, by rfl⟩ : syracuseStep 2637913 = 1978435) B1978435
theorem B2375819 : Blo 1561478 2375819 := bstep (se 1 (by rfl) ⟨1781864, by rfl⟩ : syracuseStep 2375819 = 3563729) B3563729
theorem B5275799 : Blo 1561478 5275799 := bstep (se 1 (by rfl) ⟨3956849, by rfl⟩ : syracuseStep 5275799 = 7913699) B7913699
theorem B2343065 : Blo 1561478 2343065 := bstep (se 2 (by rfl) ⟨878649, by rfl⟩ : syracuseStep 2343065 = 1757299) B1757299
theorem B4448449 : Blo 1561478 4448449 := bstep (se 2 (by rfl) ⟨1668168, by rfl⟩ : syracuseStep 4448449 = 3336337) B3336337
theorem B1876171 : Blo 1561478 1876171 := bstep (se 1 (by rfl) ⟨1407128, by rfl⟩ : syracuseStep 1876171 = 2814257) B2814257
theorem B3514571 : Blo 1561478 3514571 := bstep (se 1 (by rfl) ⟨2635928, by rfl⟩ : syracuseStep 3514571 = 5271857) B5271857
theorem B2965747 : Blo 1561478 2965747 := bstep (se 1 (by rfl) ⟨2224310, by rfl⟩ : syracuseStep 2965747 = 4448621) B4448621
theorem B3514625 : Blo 1561478 3514625 := bstep (se 2 (by rfl) ⟨1317984, by rfl⟩ : syracuseStep 3514625 = 2635969) B2635969
theorem B2343179 : Blo 1561478 2343179 := bstep (se 1 (by rfl) ⟨1757384, by rfl⟩ : syracuseStep 2343179 = 3514769) B3514769
theorem B137036053 : Blo 1561478 137036053 := bstep (se 6 (by rfl) ⟨3211782, by rfl⟩ : syracuseStep 137036053 = 6423565) B6423565
theorem B2343191 : Blo 1561478 2343191 := bstep (se 1 (by rfl) ⟨1757393, by rfl⟩ : syracuseStep 2343191 = 3514787) B3514787
theorem B5005633 : Blo 1561478 5005633 := bstep (se 2 (by rfl) ⟨1877112, by rfl⟩ : syracuseStep 5005633 = 3754225) B3754225
theorem B2343257 : Blo 1561478 2343257 := bstep (se 2 (by rfl) ⟨878721, by rfl⟩ : syracuseStep 2343257 = 1757443) B1757443
theorem B2343371 : Blo 1561478 2343371 := bstep (se 1 (by rfl) ⟨1757528, by rfl⟩ : syracuseStep 2343371 = 3515057) B3515057
theorem B2343383 : Blo 1561478 2343383 := bstep (se 1 (by rfl) ⟨1757537, by rfl⟩ : syracuseStep 2343383 = 3515075) B3515075
theorem B3514841 : Blo 1561478 3514841 := bstep (se 2 (by rfl) ⟨1318065, by rfl⟩ : syracuseStep 3514841 = 2636131) B2636131
theorem B20029913 : Blo 1561478 20029913 := bstep (se 2 (by rfl) ⟨7511217, by rfl⟩ : syracuseStep 20029913 = 15022435) B15022435
theorem B22528529 : Blo 1561478 22528529 := bstep (se 2 (by rfl) ⟨8448198, by rfl⟩ : syracuseStep 22528529 = 16896397) B16896397
theorem B2343449 : Blo 1561478 2343449 := bstep (se 2 (by rfl) ⟨878793, by rfl⟩ : syracuseStep 2343449 = 1757587) B1757587
theorem B3514931 : Blo 1561478 3514931 := bstep (se 1 (by rfl) ⟨2636198, by rfl⟩ : syracuseStep 3514931 = 5272397) B5272397
theorem B3514967 : Blo 1561478 3514967 := bstep (se 1 (by rfl) ⟨2636225, by rfl⟩ : syracuseStep 3514967 = 5272451) B5272451
theorem B11256421 : Blo 1561478 11256421 := bstep (se 4 (by rfl) ⟨1055289, by rfl⟩ : syracuseStep 11256421 = 2110579) B2110579
theorem B7905923 : Blo 1561478 7905923 := bstep (se 1 (by rfl) ⟨5929442, by rfl⟩ : syracuseStep 7905923 = 11858885) B11858885
theorem B2343563 : Blo 1561478 2343563 := bstep (se 1 (by rfl) ⟨1757672, by rfl⟩ : syracuseStep 2343563 = 3515345) B3515345
theorem B2343575 : Blo 1561478 2343575 := bstep (se 1 (by rfl) ⟨1757681, by rfl⟩ : syracuseStep 2343575 = 3515363) B3515363
theorem B2966195 : Blo 1561478 2966195 := bstep (se 1 (by rfl) ⟨2224646, by rfl⟩ : syracuseStep 2966195 = 4449293) B4449293
theorem B5276339 : Blo 1561478 5276339 := bstep (se 1 (by rfl) ⟨3957254, by rfl⟩ : syracuseStep 5276339 = 7914509) B7914509
theorem B7512755 : Blo 1561478 7512755 := bstep (se 1 (by rfl) ⟨5634566, by rfl⟩ : syracuseStep 7512755 = 11269133) B11269133
theorem B5931737 : Blo 1561478 5931737 := bstep (se 2 (by rfl) ⟨2224401, by rfl⟩ : syracuseStep 5931737 = 4448803) B4448803
theorem B2343641 : Blo 1561478 2343641 := bstep (se 2 (by rfl) ⟨878865, by rfl⟩ : syracuseStep 2343641 = 1757731) B1757731
theorem B2966233 : Blo 1561478 2966233 := bstep (se 2 (by rfl) ⟨1112337, by rfl⟩ : syracuseStep 2966233 = 2224675) B2224675
theorem B3515147 : Blo 1561478 3515147 := bstep (se 1 (by rfl) ⟨2636360, by rfl⟩ : syracuseStep 3515147 = 5272721) B5272721
theorem B3515201 : Blo 1561478 3515201 := bstep (se 2 (by rfl) ⟨1318200, by rfl⟩ : syracuseStep 3515201 = 2636401) B2636401
theorem B2343755 : Blo 1561478 2343755 := bstep (se 1 (by rfl) ⟨1757816, by rfl⟩ : syracuseStep 2343755 = 3515633) B3515633
theorem B2343767 : Blo 1561478 2343767 := bstep (se 1 (by rfl) ⟨1757825, by rfl⟩ : syracuseStep 2343767 = 3515651) B3515651
theorem B2343833 : Blo 1561478 2343833 := bstep (se 2 (by rfl) ⟨878937, by rfl⟩ : syracuseStep 2343833 = 1757875) B1757875
theorem B5276609 : Blo 1561478 5276609 := bstep (se 2 (by rfl) ⟨1978728, by rfl⟩ : syracuseStep 5276609 = 3957457) B3957457
theorem B2343947 : Blo 1561478 2343947 := bstep (se 1 (by rfl) ⟨1757960, by rfl⟩ : syracuseStep 2343947 = 3515921) B3515921
theorem B7504913 : Blo 1561478 7504913 := bstep (se 2 (by rfl) ⟨2814342, by rfl⟩ : syracuseStep 7504913 = 5628685) B5628685
theorem B5932055 : Blo 1561478 5932055 := bstep (se 1 (by rfl) ⟨4449041, by rfl⟩ : syracuseStep 5932055 = 8898083) B8898083
theorem B2343959 : Blo 1561478 2343959 := bstep (se 1 (by rfl) ⟨1757969, by rfl⟩ : syracuseStep 2343959 = 3515939) B3515939
theorem B3515417 : Blo 1561478 3515417 := bstep (se 2 (by rfl) ⟨1318281, by rfl⟩ : syracuseStep 3515417 = 2636563) B2636563
theorem B6677579 : Blo 1561478 6677579 := bstep (se 1 (by rfl) ⟨5008184, by rfl⟩ : syracuseStep 6677579 = 10016369) B10016369
theorem B2344025 : Blo 1561478 2344025 := bstep (se 2 (by rfl) ⟨879009, by rfl⟩ : syracuseStep 2344025 = 1758019) B1758019
theorem B9503837 : Blo 1561478 9503837 := bstep (se 3 (by rfl) ⟨1781969, by rfl⟩ : syracuseStep 9503837 = 3563939) B3563939
theorem B3515507 : Blo 1561478 3515507 := bstep (se 1 (by rfl) ⟨2636630, by rfl⟩ : syracuseStep 3515507 = 5273261) B5273261
theorem B15025283 : Blo 1561478 15025283 := bstep (se 1 (by rfl) ⟨11268962, by rfl⟩ : syracuseStep 15025283 = 22537925) B22537925
theorem B3515543 : Blo 1561478 3515543 := bstep (se 1 (by rfl) ⟨2636657, by rfl⟩ : syracuseStep 3515543 = 5273315) B5273315
theorem B2966681 : Blo 1561478 2966681 := bstep (se 2 (by rfl) ⟨1112505, by rfl⟩ : syracuseStep 2966681 = 2225011) B2225011
theorem B2344139 : Blo 1561478 2344139 := bstep (se 1 (by rfl) ⟨1758104, by rfl⟩ : syracuseStep 2344139 = 3516209) B3516209
theorem B2344151 : Blo 1561478 2344151 := bstep (se 1 (by rfl) ⟨1758113, by rfl⟩ : syracuseStep 2344151 = 3516227) B3516227
theorem B14451929 : Blo 1561478 14451929 := bstep (se 2 (by rfl) ⟨5419473, by rfl⟩ : syracuseStep 14451929 = 10838947) B10838947
theorem B8897809 : Blo 1561478 8897809 := bstep (se 2 (by rfl) ⟨3336678, by rfl⟩ : syracuseStep 8897809 = 6673357) B6673357
theorem B2344217 : Blo 1561478 2344217 := bstep (se 2 (by rfl) ⟨879081, by rfl⟩ : syracuseStep 2344217 = 1758163) B1758163
theorem B3515723 : Blo 1561478 3515723 := bstep (se 1 (by rfl) ⟨2636792, by rfl⟩ : syracuseStep 3515723 = 5273585) B5273585
theorem B11412829 : Blo 1561478 11412829 := bstep (se 3 (by rfl) ⟨2139905, by rfl⟩ : syracuseStep 11412829 = 4279811) B4279811
theorem B3515777 : Blo 1561478 3515777 := bstep (se 2 (by rfl) ⟨1318416, by rfl⟩ : syracuseStep 3515777 = 2636833) B2636833
theorem B2344331 : Blo 1561478 2344331 := bstep (se 1 (by rfl) ⟨1758248, by rfl⟩ : syracuseStep 2344331 = 3516497) B3516497
theorem B2344343 : Blo 1561478 2344343 := bstep (se 1 (by rfl) ⟨1758257, by rfl⟩ : syracuseStep 2344343 = 3516515) B3516515
theorem B2344409 : Blo 1561478 2344409 := bstep (se 2 (by rfl) ⟨879153, by rfl⟩ : syracuseStep 2344409 = 1758307) B1758307
theorem B2344523 : Blo 1561478 2344523 := bstep (se 1 (by rfl) ⟨1758392, by rfl⟩ : syracuseStep 2344523 = 3516785) B3516785
theorem B2344535 : Blo 1561478 2344535 := bstep (se 1 (by rfl) ⟨1758401, by rfl⟩ : syracuseStep 2344535 = 3516803) B3516803
theorem B3515993 : Blo 1561478 3515993 := bstep (se 2 (by rfl) ⟨1318497, by rfl⟩ : syracuseStep 3515993 = 2636995) B2636995
theorem B27051671 : Blo 1561478 27051671 := bstep (se 1 (by rfl) ⟨20288753, by rfl⟩ : syracuseStep 27051671 = 40577507) B40577507
theorem B2344601 : Blo 1561478 2344601 := bstep (se 2 (by rfl) ⟨879225, by rfl⟩ : syracuseStep 2344601 = 1758451) B1758451
theorem B5932723 : Blo 1561478 5932723 := bstep (se 1 (by rfl) ⟨4449542, by rfl⟩ : syracuseStep 5932723 = 8899085) B8899085
theorem B3516083 : Blo 1561478 3516083 := bstep (se 1 (by rfl) ⟨2637062, by rfl⟩ : syracuseStep 3516083 = 5274125) B5274125
theorem B3516119 : Blo 1561478 3516119 := bstep (se 1 (by rfl) ⟨2637089, by rfl⟩ : syracuseStep 3516119 = 5274179) B5274179
theorem B2344715 : Blo 1561478 2344715 := bstep (se 1 (by rfl) ⟨1758536, by rfl⟩ : syracuseStep 2344715 = 3517073) B3517073
theorem B2344727 : Blo 1561478 2344727 := bstep (se 1 (by rfl) ⟨1758545, by rfl⟩ : syracuseStep 2344727 = 3517091) B3517091
theorem B25356077 : Blo 1561478 25356077 := bstep (se 3 (by rfl) ⟨4754264, by rfl⟩ : syracuseStep 25356077 = 9508529) B9508529
theorem B3753803 : Blo 1561478 3753803 := bstep (se 1 (by rfl) ⟨2815352, by rfl⟩ : syracuseStep 3753803 = 5630705) B5630705
theorem B2344793 : Blo 1561478 2344793 := bstep (se 2 (by rfl) ⟨879297, by rfl⟩ : syracuseStep 2344793 = 1758595) B1758595
theorem B5007197 : Blo 1561478 5007197 := bstep (se 3 (by rfl) ⟨938849, by rfl⟩ : syracuseStep 5007197 = 1877699) B1877699
theorem B2967425 : Blo 1561478 2967425 := bstep (se 2 (by rfl) ⟨1112784, by rfl⟩ : syracuseStep 2967425 = 2225569) B2225569
theorem B3516299 : Blo 1561478 3516299 := bstep (se 1 (by rfl) ⟨2637224, by rfl⟩ : syracuseStep 3516299 = 5274449) B5274449
theorem B4507571 : Blo 1561478 4507571 := bstep (se 1 (by rfl) ⟨3380678, by rfl⟩ : syracuseStep 4507571 = 6761357) B6761357
theorem B3516353 : Blo 1561478 3516353 := bstep (se 2 (by rfl) ⟨1318632, by rfl⟩ : syracuseStep 3516353 = 2637265) B2637265
theorem B2344907 : Blo 1561478 2344907 := bstep (se 1 (by rfl) ⟨1758680, by rfl⟩ : syracuseStep 2344907 = 3517361) B3517361
theorem B2344919 : Blo 1561478 2344919 := bstep (se 1 (by rfl) ⟨1758689, by rfl⟩ : syracuseStep 2344919 = 3517379) B3517379
theorem B2344985 : Blo 1561478 2344985 := bstep (se 2 (by rfl) ⟨879369, by rfl⟩ : syracuseStep 2344985 = 1758739) B1758739
theorem B1976395 : Blo 1561478 1976395 := bstep (se 1 (by rfl) ⟨1482296, by rfl⟩ : syracuseStep 1976395 = 2964593) B2964593
theorem B2967691 : Blo 1561478 2967691 := bstep (se 1 (by rfl) ⟨2225768, by rfl⟩ : syracuseStep 2967691 = 4451537) B4451537
theorem B2345099 : Blo 1561478 2345099 := bstep (se 1 (by rfl) ⟨1758824, by rfl⟩ : syracuseStep 2345099 = 3517649) B3517649
theorem B6670487 : Blo 1561478 6670487 := bstep (se 1 (by rfl) ⟨5002865, by rfl⟩ : syracuseStep 6670487 = 10005731) B10005731
theorem B2345111 : Blo 1561478 2345111 := bstep (se 1 (by rfl) ⟨1758833, by rfl⟩ : syracuseStep 2345111 = 3517667) B3517667
theorem B3516569 : Blo 1561478 3516569 := bstep (se 2 (by rfl) ⟨1318713, by rfl⟩ : syracuseStep 3516569 = 2637427) B2637427
theorem B2345177 : Blo 1561478 2345177 := bstep (se 2 (by rfl) ⟨879441, by rfl⟩ : syracuseStep 2345177 = 1758883) B1758883
theorem B3516659 : Blo 1561478 3516659 := bstep (se 1 (by rfl) ⟨2637494, by rfl⟩ : syracuseStep 3516659 = 5274989) B5274989
theorem B3516695 : Blo 1561478 3516695 := bstep (se 1 (by rfl) ⟨2637521, by rfl⟩ : syracuseStep 3516695 = 5275043) B5275043
theorem B1976663 : Blo 1561478 1976663 := bstep (se 1 (by rfl) ⟨1482497, by rfl⟩ : syracuseStep 1976663 = 2964995) B2964995
theorem B17803637 : Blo 1561478 17803637 := bstep (se 5 (by rfl) ⟨834545, by rfl⟩ : syracuseStep 17803637 = 1669091) B1669091
theorem B22538675 : Blo 1561478 22538675 := bstep (se 1 (by rfl) ⟨16904006, by rfl⟩ : syracuseStep 22538675 = 33808013) B33808013
theorem B6670795 : Blo 1561478 6670795 := bstep (se 1 (by rfl) ⟨5003096, by rfl⟩ : syracuseStep 6670795 = 10006193) B10006193
theorem B3516875 : Blo 1561478 3516875 := bstep (se 1 (by rfl) ⟨2637656, by rfl⟩ : syracuseStep 3516875 = 5275313) B5275313
theorem B3754457 : Blo 1561478 3754457 := bstep (se 2 (by rfl) ⟨1407921, by rfl⟩ : syracuseStep 3754457 = 2815843) B2815843
theorem B3516929 : Blo 1561478 3516929 := bstep (se 2 (by rfl) ⟨1318848, by rfl⟩ : syracuseStep 3516929 = 2637697) B2637697
theorem B2968139 : Blo 1561478 2968139 := bstep (se 1 (by rfl) ⟨2226104, by rfl⟩ : syracuseStep 2968139 = 4452209) B4452209
theorem B11258585 : Blo 1561478 11258585 := bstep (se 2 (by rfl) ⟨4221969, by rfl⟩ : syracuseStep 11258585 = 8443939) B8443939
theorem B3517145 : Blo 1561478 3517145 := bstep (se 2 (by rfl) ⟨1318929, by rfl⟩ : syracuseStep 3517145 = 2637859) B2637859
theorem B5270237 : Blo 1561478 5270237 := bstep (se 3 (by rfl) ⟨988169, by rfl⟩ : syracuseStep 5270237 = 1976339) B1976339
theorem B6671069 : Blo 1561478 6671069 := bstep (se 3 (by rfl) ⟨1250825, by rfl⟩ : syracuseStep 6671069 = 2501651) B2501651
theorem B84544241 : Blo 1561478 84544241 := bstep (se 2 (by rfl) ⟨31704090, by rfl⟩ : syracuseStep 84544241 = 63408181) B63408181
theorem B13536017 : Blo 1561478 13536017 := bstep (se 2 (by rfl) ⟨5076006, by rfl⟩ : syracuseStep 13536017 = 10152013) B10152013
theorem B3517235 : Blo 1561478 3517235 := bstep (se 1 (by rfl) ⟨2637926, by rfl⟩ : syracuseStep 3517235 = 5275853) B5275853
theorem B3517271 : Blo 1561478 3517271 := bstep (se 1 (by rfl) ⟨2637953, by rfl⟩ : syracuseStep 3517271 = 5275907) B5275907
theorem B20032373 : Blo 1561478 20032373 := bstep (se 5 (by rfl) ⟨939017, by rfl⟩ : syracuseStep 20032373 = 1878035) B1878035
theorem B5933969 : Blo 1561478 5933969 := bstep (se 2 (by rfl) ⟨2225238, by rfl⟩ : syracuseStep 5933969 = 4450477) B4450477
theorem B12028877 : Blo 1561478 12028877 := bstep (se 3 (by rfl) ⟨2255414, by rfl⟩ : syracuseStep 12028877 = 4510829) B4510829
theorem B3337175 : Blo 1561478 3337175 := bstep (se 1 (by rfl) ⟨2502881, by rfl⟩ : syracuseStep 3337175 = 5005763) B5005763
theorem B3517451 : Blo 1561478 3517451 := bstep (se 1 (by rfl) ⟨2638088, by rfl⟩ : syracuseStep 3517451 = 5276177) B5276177
theorem B1977367 : Blo 1561478 1977367 := bstep (se 1 (by rfl) ⟨1483025, by rfl⟩ : syracuseStep 1977367 = 2966051) B2966051
theorem B3517505 : Blo 1561478 3517505 := bstep (se 2 (by rfl) ⟨1319064, by rfl⟩ : syracuseStep 3517505 = 2638129) B2638129
theorem B1584203 : Blo 1561478 1584203 := bstep (se 1 (by rfl) ⟨1188152, by rfl⟩ : syracuseStep 1584203 = 2376305) B2376305
theorem B3337355 : Blo 1561478 3337355 := bstep (se 1 (by rfl) ⟨2503016, by rfl⟩ : syracuseStep 3337355 = 5006033) B5006033
theorem B15011021 : Blo 1561478 15011021 := bstep (se 3 (by rfl) ⟨2814566, by rfl⟩ : syracuseStep 15011021 = 5629133) B5629133
theorem B3517721 : Blo 1561478 3517721 := bstep (se 2 (by rfl) ⟨1319145, by rfl⟩ : syracuseStep 3517721 = 2638291) B2638291
theorem B3517811 : Blo 1561478 3517811 := bstep (se 1 (by rfl) ⟨2638358, by rfl⟩ : syracuseStep 3517811 = 5276717) B5276717
theorem B5934667 : Blo 1561478 5934667 := bstep (se 1 (by rfl) ⟨4451000, by rfl⟩ : syracuseStep 5934667 = 8902001) B8902001
theorem B1756759 : Blo 1561478 1756759 := bstep (se 1 (by rfl) ⟨1317569, by rfl⟩ : syracuseStep 1756759 = 2635139) B2635139
theorem B20016791 : Blo 1561478 20016791 := bstep (se 1 (by rfl) ⟨15012593, by rfl⟩ : syracuseStep 20016791 = 30025187) B30025187
theorem B3804823 : Blo 1561478 3804823 := bstep (se 1 (by rfl) ⟨2853617, by rfl⟩ : syracuseStep 3804823 = 5707235) B5707235
theorem B2223769 : Blo 1561478 2223769 := bstep (se 2 (by rfl) ⟨833913, by rfl⟩ : syracuseStep 2223769 = 1667827) B1667827
theorem B1756939 : Blo 1561478 1756939 := bstep (se 1 (by rfl) ⟨1317704, by rfl⟩ : syracuseStep 1756939 = 2635409) B2635409
theorem B2223883 : Blo 1561478 2223883 := bstep (se 1 (by rfl) ⟨1667912, by rfl⟩ : syracuseStep 2223883 = 3335825) B3335825
theorem B5271371 : Blo 1561478 5271371 := bstep (se 1 (by rfl) ⟨3953528, by rfl⟩ : syracuseStep 5271371 = 7907057) B7907057
theorem B4452185 : Blo 1561478 4452185 := bstep (se 2 (by rfl) ⟨1669569, by rfl⟩ : syracuseStep 4452185 = 3339139) B3339139
theorem B5934941 : Blo 1561478 5934941 := bstep (se 3 (by rfl) ⟨1112801, by rfl⟩ : syracuseStep 5934941 = 2225603) B2225603
theorem B1757047 : Blo 1561478 1757047 := bstep (se 1 (by rfl) ⟨1317785, by rfl⟩ : syracuseStep 1757047 = 2635571) B2635571
theorem B3952577 : Blo 1561478 3952577 := bstep (se 2 (by rfl) ⟨1482216, by rfl⟩ : syracuseStep 3952577 = 2964433) B2964433
theorem B6672401 : Blo 1561478 6672401 := bstep (se 2 (by rfl) ⟨2502150, by rfl⟩ : syracuseStep 6672401 = 5004301) B5004301
theorem B1757227 : Blo 1561478 1757227 := bstep (se 1 (by rfl) ⟨1317920, by rfl⟩ : syracuseStep 1757227 = 2635841) B2635841
theorem B3166283 : Blo 1561478 3166283 := bstep (se 1 (by rfl) ⟨2374712, by rfl⟩ : syracuseStep 3166283 = 4749425) B4749425
theorem B5271641 : Blo 1561478 5271641 := bstep (se 2 (by rfl) ⟨1976865, by rfl⟩ : syracuseStep 5271641 = 3953731) B3953731
theorem B1757335 : Blo 1561478 1757335 := bstep (se 1 (by rfl) ⟨1318001, by rfl⟩ : syracuseStep 1757335 = 2636003) B2636003
theorem B7909649 : Blo 1561478 7909649 := bstep (se 2 (by rfl) ⟨2966118, by rfl⟩ : syracuseStep 7909649 = 5932237) B5932237
theorem B1757515 : Blo 1561478 1757515 := bstep (se 1 (by rfl) ⟨1318136, by rfl⟩ : syracuseStep 1757515 = 2636273) B2636273
theorem B7508375 : Blo 1561478 7508375 := bstep (se 1 (by rfl) ⟨5631281, by rfl⟩ : syracuseStep 7508375 = 11262563) B11262563
theorem B11268503 : Blo 1561478 11268503 := bstep (se 1 (by rfl) ⟨8451377, by rfl⟩ : syracuseStep 11268503 = 16902755) B16902755
theorem B7909811 : Blo 1561478 7909811 := bstep (se 1 (by rfl) ⟨5932358, by rfl⟩ : syracuseStep 7909811 = 11864717) B11864717
theorem B1757623 : Blo 1561478 1757623 := bstep (se 1 (by rfl) ⟨1318217, by rfl⟩ : syracuseStep 1757623 = 2636435) B2636435
theorem B2814401 : Blo 1561478 2814401 := bstep (se 2 (by rfl) ⟨1055400, by rfl⟩ : syracuseStep 2814401 = 2110801) B2110801
theorem B5935639 : Blo 1561478 5935639 := bstep (se 1 (by rfl) ⟨4451729, by rfl⟩ : syracuseStep 5935639 = 8903459) B8903459
theorem B1667639 : Blo 1561478 1667639 := bstep (se 1 (by rfl) ⟨1250729, by rfl⟩ : syracuseStep 1667639 = 2501459) B2501459
theorem B1757803 : Blo 1561478 1757803 := bstep (se 1 (by rfl) ⟨1318352, by rfl⟩ : syracuseStep 1757803 = 2636705) B2636705
theorem B8901251 : Blo 1561478 8901251 := bstep (se 1 (by rfl) ⟨6675938, by rfl⟩ : syracuseStep 8901251 = 13351877) B13351877
theorem B1757911 : Blo 1561478 1757911 := bstep (se 1 (by rfl) ⟨1318433, by rfl⟩ : syracuseStep 1757911 = 2636867) B2636867
theorem B3338995 : Blo 1561478 3338995 := bstep (se 1 (by rfl) ⟨2504246, by rfl⟩ : syracuseStep 3338995 = 5008493) B5008493
theorem B12669701 : Blo 1561478 12669701 := bstep (se 4 (by rfl) ⟨1187784, by rfl⟩ : syracuseStep 12669701 = 2375569) B2375569
theorem B5272343 : Blo 1561478 5272343 := bstep (se 1 (by rfl) ⟨3954257, by rfl⟩ : syracuseStep 5272343 = 7908515) B7908515
theorem B4510529 : Blo 1561478 4510529 := bstep (se 2 (by rfl) ⟨1691448, by rfl⟩ : syracuseStep 4510529 = 3382897) B3382897
theorem B1561483 : Blo 1561478 1561483 := bstep (se 1 (by rfl) ⟨1171112, by rfl⟩ : syracuseStep 1561483 = 2342225) B2342225
theorem B1758091 : Blo 1561478 1758091 := bstep (se 1 (by rfl) ⟨1318568, by rfl⟩ : syracuseStep 1758091 = 2637137) B2637137
theorem B1561495 : Blo 1561478 1561495 := bstep (se 1 (by rfl) ⟨1171121, by rfl⟩ : syracuseStep 1561495 = 2342243) B2342243
theorem B1561515 : Blo 1561478 1561515 := bstep (se 1 (by rfl) ⟨1171136, by rfl⟩ : syracuseStep 1561515 = 2342273) B2342273
theorem B1561527 : Blo 1561478 1561527 := bstep (se 1 (by rfl) ⟨1171145, by rfl⟩ : syracuseStep 1561527 = 2342291) B2342291
theorem B5075905 : Blo 1561478 5075905 := bstep (se 2 (by rfl) ⟨1903464, by rfl⟩ : syracuseStep 5075905 = 3806929) B3806929
theorem B1561547 : Blo 1561478 1561547 := bstep (se 1 (by rfl) ⟨1171160, by rfl⟩ : syracuseStep 1561547 = 2342321) B2342321
theorem B1561559 : Blo 1561478 1561559 := bstep (se 1 (by rfl) ⟨1171169, by rfl⟩ : syracuseStep 1561559 = 2342339) B2342339
theorem B1561579 : Blo 1561478 1561579 := bstep (se 1 (by rfl) ⟨1171184, by rfl⟩ : syracuseStep 1561579 = 2342369) B2342369
theorem B1561591 : Blo 1561478 1561591 := bstep (se 1 (by rfl) ⟨1171193, by rfl⟩ : syracuseStep 1561591 = 2342387) B2342387
theorem B1758199 : Blo 1561478 1758199 := bstep (se 1 (by rfl) ⟨1318649, by rfl⟩ : syracuseStep 1758199 = 2637299) B2637299
theorem B2814977 : Blo 1561478 2814977 := bstep (se 2 (by rfl) ⟨1055616, by rfl⟩ : syracuseStep 2814977 = 2111233) B2111233
theorem B1561611 : Blo 1561478 1561611 := bstep (se 1 (by rfl) ⟨1171208, by rfl⟩ : syracuseStep 1561611 = 2342417) B2342417
theorem B1561623 : Blo 1561478 1561623 := bstep (se 1 (by rfl) ⟨1171217, by rfl⟩ : syracuseStep 1561623 = 2342435) B2342435
theorem B1561643 : Blo 1561478 1561643 := bstep (se 1 (by rfl) ⟨1171232, by rfl⟩ : syracuseStep 1561643 = 2342465) B2342465
theorem B1561655 : Blo 1561478 1561655 := bstep (se 1 (by rfl) ⟨1171241, by rfl⟩ : syracuseStep 1561655 = 2342483) B2342483
theorem B1561675 : Blo 1561478 1561675 := bstep (se 1 (by rfl) ⟨1171256, by rfl⟩ : syracuseStep 1561675 = 2342513) B2342513
theorem B2225227 : Blo 1561478 2225227 := bstep (se 1 (by rfl) ⟨1668920, by rfl⟩ : syracuseStep 2225227 = 3337841) B3337841
theorem B1561687 : Blo 1561478 1561687 := bstep (se 1 (by rfl) ⟨1171265, by rfl⟩ : syracuseStep 1561687 = 2342531) B2342531
theorem B2708569 : Blo 1561478 2708569 := bstep (se 2 (by rfl) ⟨1015713, by rfl⟩ : syracuseStep 2708569 = 2031427) B2031427
theorem B1561707 : Blo 1561478 1561707 := bstep (se 1 (by rfl) ⟨1171280, by rfl⟩ : syracuseStep 1561707 = 2342561) B2342561
theorem B1561719 : Blo 1561478 1561719 := bstep (se 1 (by rfl) ⟨1171289, by rfl⟩ : syracuseStep 1561719 = 2342579) B2342579
theorem B1561739 : Blo 1561478 1561739 := bstep (se 1 (by rfl) ⟨1171304, by rfl⟩ : syracuseStep 1561739 = 2342609) B2342609
theorem B1561751 : Blo 1561478 1561751 := bstep (se 1 (by rfl) ⟨1171313, by rfl⟩ : syracuseStep 1561751 = 2342627) B2342627
theorem B1561771 : Blo 1561478 1561771 := bstep (se 1 (by rfl) ⟨1171328, by rfl⟩ : syracuseStep 1561771 = 2342657) B2342657
theorem B1758379 : Blo 1561478 1758379 := bstep (se 1 (by rfl) ⟨1318784, by rfl⟩ : syracuseStep 1758379 = 2637569) B2637569
theorem B3953843 : Blo 1561478 3953843 := bstep (se 1 (by rfl) ⟨2965382, by rfl⟩ : syracuseStep 3953843 = 5930765) B5930765
theorem B36066485 : Blo 1561478 36066485 := bstep (se 5 (by rfl) ⟨1690616, by rfl⟩ : syracuseStep 36066485 = 3381233) B3381233
theorem B1561783 : Blo 1561478 1561783 := bstep (se 1 (by rfl) ⟨1171337, by rfl⟩ : syracuseStep 1561783 = 2342675) B2342675
theorem B1561803 : Blo 1561478 1561803 := bstep (se 1 (by rfl) ⟨1171352, by rfl⟩ : syracuseStep 1561803 = 2342705) B2342705
theorem B1561815 : Blo 1561478 1561815 := bstep (se 1 (by rfl) ⟨1171361, by rfl⟩ : syracuseStep 1561815 = 2342723) B2342723
theorem B1561835 : Blo 1561478 1561835 := bstep (se 1 (by rfl) ⟨1171376, by rfl⟩ : syracuseStep 1561835 = 2342753) B2342753
theorem B1561847 : Blo 1561478 1561847 := bstep (se 1 (by rfl) ⟨1171385, by rfl⟩ : syracuseStep 1561847 = 2342771) B2342771
theorem B1561867 : Blo 1561478 1561867 := bstep (se 1 (by rfl) ⟨1171400, by rfl⟩ : syracuseStep 1561867 = 2342801) B2342801
theorem B2635031 : Blo 1561478 2635031 := bstep (se 1 (by rfl) ⟨1976273, by rfl⟩ : syracuseStep 2635031 = 3952547) B3952547
theorem B1561879 : Blo 1561478 1561879 := bstep (se 1 (by rfl) ⟨1171409, by rfl⟩ : syracuseStep 1561879 = 2342819) B2342819
theorem B1758487 : Blo 1561478 1758487 := bstep (se 1 (by rfl) ⟨1318865, by rfl⟩ : syracuseStep 1758487 = 2637731) B2637731
theorem B4011287 : Blo 1561478 4011287 := bstep (se 1 (by rfl) ⟨3008465, by rfl⟩ : syracuseStep 4011287 = 6016931) B6016931
theorem B1561899 : Blo 1561478 1561899 := bstep (se 1 (by rfl) ⟨1171424, by rfl⟩ : syracuseStep 1561899 = 2342849) B2342849
theorem B5272883 : Blo 1561478 5272883 := bstep (se 1 (by rfl) ⟨3954662, by rfl⟩ : syracuseStep 5272883 = 7909325) B7909325
theorem B1561911 : Blo 1561478 1561911 := bstep (se 1 (by rfl) ⟨1171433, by rfl⟩ : syracuseStep 1561911 = 2342867) B2342867
theorem B1561931 : Blo 1561478 1561931 := bstep (se 1 (by rfl) ⟨1171448, by rfl⟩ : syracuseStep 1561931 = 2342897) B2342897
theorem B1561943 : Blo 1561478 1561943 := bstep (se 1 (by rfl) ⟨1171457, by rfl⟩ : syracuseStep 1561943 = 2342915) B2342915
theorem B2225495 : Blo 1561478 2225495 := bstep (se 1 (by rfl) ⟨1669121, by rfl⟩ : syracuseStep 2225495 = 3338243) B3338243
theorem B1561963 : Blo 1561478 1561963 := bstep (se 1 (by rfl) ⟨1171472, by rfl⟩ : syracuseStep 1561963 = 2342945) B2342945
theorem B21378421 : Blo 1561478 21378421 := bstep (se 5 (by rfl) ⟨1002113, by rfl⟩ : syracuseStep 21378421 = 2004227) B2004227
theorem B1561975 : Blo 1561478 1561975 := bstep (se 1 (by rfl) ⟨1171481, by rfl⟩ : syracuseStep 1561975 = 2342963) B2342963
theorem B1561995 : Blo 1561478 1561995 := bstep (se 1 (by rfl) ⟨1171496, by rfl⟩ : syracuseStep 1561995 = 2342993) B2342993
theorem B2635159 : Blo 1561478 2635159 := bstep (se 1 (by rfl) ⟨1976369, by rfl⟩ : syracuseStep 2635159 = 3952739) B3952739
theorem B1562007 : Blo 1561478 1562007 := bstep (se 1 (by rfl) ⟨1171505, by rfl⟩ : syracuseStep 1562007 = 2343011) B2343011
theorem B1562027 : Blo 1561478 1562027 := bstep (se 1 (by rfl) ⟨1171520, by rfl⟩ : syracuseStep 1562027 = 2343041) B2343041
theorem B1562039 : Blo 1561478 1562039 := bstep (se 1 (by rfl) ⟨1171529, by rfl⟩ : syracuseStep 1562039 = 2343059) B2343059
theorem B1562059 : Blo 1561478 1562059 := bstep (se 1 (by rfl) ⟨1171544, by rfl⟩ : syracuseStep 1562059 = 2343089) B2343089
theorem B1758667 : Blo 1561478 1758667 := bstep (se 1 (by rfl) ⟨1319000, by rfl⟩ : syracuseStep 1758667 = 2638001) B2638001
theorem B1562071 : Blo 1561478 1562071 := bstep (se 1 (by rfl) ⟨1171553, by rfl⟩ : syracuseStep 1562071 = 2343107) B2343107
theorem B1562091 : Blo 1561478 1562091 := bstep (se 1 (by rfl) ⟨1171568, by rfl⟩ : syracuseStep 1562091 = 2343137) B2343137
theorem B1562103 : Blo 1561478 1562103 := bstep (se 1 (by rfl) ⟨1171577, by rfl⟩ : syracuseStep 1562103 = 2343155) B2343155
theorem B1562123 : Blo 1561478 1562123 := bstep (se 1 (by rfl) ⟨1171592, by rfl⟩ : syracuseStep 1562123 = 2343185) B2343185
theorem B1562135 : Blo 1561478 1562135 := bstep (se 1 (by rfl) ⟨1171601, by rfl⟩ : syracuseStep 1562135 = 2343203) B2343203
theorem B1562155 : Blo 1561478 1562155 := bstep (se 1 (by rfl) ⟨1171616, by rfl⟩ : syracuseStep 1562155 = 2343233) B2343233
theorem B5633587 : Blo 1561478 5633587 := bstep (se 1 (by rfl) ⟨4225190, by rfl⟩ : syracuseStep 5633587 = 8450381) B8450381
theorem B1562167 : Blo 1561478 1562167 := bstep (se 1 (by rfl) ⟨1171625, by rfl⟩ : syracuseStep 1562167 = 2343251) B2343251
theorem B1758775 : Blo 1561478 1758775 := bstep (se 1 (by rfl) ⟨1319081, by rfl⟩ : syracuseStep 1758775 = 2638163) B2638163
theorem B5273153 : Blo 1561478 5273153 := bstep (se 2 (by rfl) ⟨1977432, by rfl⟩ : syracuseStep 5273153 = 3954865) B3954865
theorem B1562187 : Blo 1561478 1562187 := bstep (se 1 (by rfl) ⟨1171640, by rfl⟩ : syracuseStep 1562187 = 2343281) B2343281
theorem B1562199 : Blo 1561478 1562199 := bstep (se 1 (by rfl) ⟨1171649, by rfl⟩ : syracuseStep 1562199 = 2343299) B2343299
theorem B1562219 : Blo 1561478 1562219 := bstep (se 1 (by rfl) ⟨1171664, by rfl⟩ : syracuseStep 1562219 = 2343329) B2343329
theorem B1562231 : Blo 1561478 1562231 := bstep (se 1 (by rfl) ⟨1171673, by rfl⟩ : syracuseStep 1562231 = 2343347) B2343347
theorem B1562251 : Blo 1561478 1562251 := bstep (se 1 (by rfl) ⟨1171688, by rfl⟩ : syracuseStep 1562251 = 2343377) B2343377
theorem B1562263 : Blo 1561478 1562263 := bstep (se 1 (by rfl) ⟨1171697, by rfl⟩ : syracuseStep 1562263 = 2343395) B2343395
theorem B1562283 : Blo 1561478 1562283 := bstep (se 1 (by rfl) ⟨1171712, by rfl⟩ : syracuseStep 1562283 = 2343425) B2343425
theorem B1562295 : Blo 1561478 1562295 := bstep (se 1 (by rfl) ⟨1171721, by rfl⟩ : syracuseStep 1562295 = 2343443) B2343443
theorem B3954379 : Blo 1561478 3954379 := bstep (se 1 (by rfl) ⟨2965784, by rfl⟩ : syracuseStep 3954379 = 5931569) B5931569
theorem B1562315 : Blo 1561478 1562315 := bstep (se 1 (by rfl) ⟨1171736, by rfl⟩ : syracuseStep 1562315 = 2343473) B2343473
theorem B1562327 : Blo 1561478 1562327 := bstep (se 1 (by rfl) ⟨1171745, by rfl⟩ : syracuseStep 1562327 = 2343491) B2343491
theorem B1562347 : Blo 1561478 1562347 := bstep (se 1 (by rfl) ⟨1171760, by rfl⟩ : syracuseStep 1562347 = 2343521) B2343521
theorem B1562359 : Blo 1561478 1562359 := bstep (se 1 (by rfl) ⟨1171769, by rfl⟩ : syracuseStep 1562359 = 2343539) B2343539
theorem B1562379 : Blo 1561478 1562379 := bstep (se 1 (by rfl) ⟨1171784, by rfl⟩ : syracuseStep 1562379 = 2343569) B2343569
theorem B1562391 : Blo 1561478 1562391 := bstep (se 1 (by rfl) ⟨1171793, by rfl⟩ : syracuseStep 1562391 = 2343587) B2343587
theorem B1562411 : Blo 1561478 1562411 := bstep (se 1 (by rfl) ⟨1171808, by rfl⟩ : syracuseStep 1562411 = 2343617) B2343617
theorem B5003059 : Blo 1561478 5003059 := bstep (se 1 (by rfl) ⟨3752294, by rfl⟩ : syracuseStep 5003059 = 7504589) B7504589
theorem B1562423 : Blo 1561478 1562423 := bstep (se 1 (by rfl) ⟨1171817, by rfl⟩ : syracuseStep 1562423 = 2343635) B2343635
theorem B1562443 : Blo 1561478 1562443 := bstep (se 1 (by rfl) ⟨1171832, by rfl⟩ : syracuseStep 1562443 = 2343665) B2343665
theorem B1562455 : Blo 1561478 1562455 := bstep (se 1 (by rfl) ⟨1171841, by rfl⟩ : syracuseStep 1562455 = 2343683) B2343683
theorem B3954521 : Blo 1561478 3954521 := bstep (se 2 (by rfl) ⟨1482945, by rfl⟩ : syracuseStep 3954521 = 2965891) B2965891
theorem B10696549 : Blo 1561478 10696549 := bstep (se 4 (by rfl) ⟨1002801, by rfl⟩ : syracuseStep 10696549 = 2005603) B2005603
theorem B1562475 : Blo 1561478 1562475 := bstep (se 1 (by rfl) ⟨1171856, by rfl⟩ : syracuseStep 1562475 = 2343713) B2343713
theorem B1562487 : Blo 1561478 1562487 := bstep (se 1 (by rfl) ⟨1171865, by rfl⟩ : syracuseStep 1562487 = 2343731) B2343731
theorem B5928835 : Blo 1561478 5928835 := bstep (se 1 (by rfl) ⟨4446626, by rfl⟩ : syracuseStep 5928835 = 8893253) B8893253
theorem B1562507 : Blo 1561478 1562507 := bstep (se 1 (by rfl) ⟨1171880, by rfl⟩ : syracuseStep 1562507 = 2343761) B2343761
theorem B1562519 : Blo 1561478 1562519 := bstep (se 1 (by rfl) ⟨1171889, by rfl⟩ : syracuseStep 1562519 = 2343779) B2343779
theorem B1562539 : Blo 1561478 1562539 := bstep (se 1 (by rfl) ⟨1171904, by rfl⟩ : syracuseStep 1562539 = 2343809) B2343809
theorem B1562551 : Blo 1561478 1562551 := bstep (se 1 (by rfl) ⟨1171913, by rfl⟩ : syracuseStep 1562551 = 2343827) B2343827
theorem B1562571 : Blo 1561478 1562571 := bstep (se 1 (by rfl) ⟨1171928, by rfl⟩ : syracuseStep 1562571 = 2343857) B2343857
theorem B1562583 : Blo 1561478 1562583 := bstep (se 1 (by rfl) ⟨1171937, by rfl⟩ : syracuseStep 1562583 = 2343875) B2343875
theorem B1562603 : Blo 1561478 1562603 := bstep (se 1 (by rfl) ⟨1171952, by rfl⟩ : syracuseStep 1562603 = 2343905) B2343905
theorem B2815987 : Blo 1561478 2815987 := bstep (se 1 (by rfl) ⟨2111990, by rfl⟩ : syracuseStep 2815987 = 4223981) B4223981
theorem B1562615 : Blo 1561478 1562615 := bstep (se 1 (by rfl) ⟨1171961, by rfl⟩ : syracuseStep 1562615 = 2343923) B2343923
theorem B2635787 : Blo 1561478 2635787 := bstep (se 1 (by rfl) ⟨1976840, by rfl⟩ : syracuseStep 2635787 = 3953681) B3953681
theorem B1562635 : Blo 1561478 1562635 := bstep (se 1 (by rfl) ⟨1171976, by rfl⟩ : syracuseStep 1562635 = 2343953) B2343953
theorem B2005003 : Blo 1561478 2005003 := bstep (se 1 (by rfl) ⟨1503752, by rfl⟩ : syracuseStep 2005003 = 3007505) B3007505
theorem B1562647 : Blo 1561478 1562647 := bstep (se 1 (by rfl) ⟨1171985, by rfl⟩ : syracuseStep 1562647 = 2343971) B2343971
theorem B1562667 : Blo 1561478 1562667 := bstep (se 1 (by rfl) ⟨1172000, by rfl⟩ : syracuseStep 1562667 = 2344001) B2344001
theorem B1562679 : Blo 1561478 1562679 := bstep (se 1 (by rfl) ⟨1172009, by rfl⟩ : syracuseStep 1562679 = 2344019) B2344019
theorem B1562699 : Blo 1561478 1562699 := bstep (se 1 (by rfl) ⟨1172024, by rfl⟩ : syracuseStep 1562699 = 2344049) B2344049
theorem B1562711 : Blo 1561478 1562711 := bstep (se 1 (by rfl) ⟨1172033, by rfl⟩ : syracuseStep 1562711 = 2344067) B2344067
theorem B5273693 : Blo 1561478 5273693 := bstep (se 3 (by rfl) ⟨988817, by rfl⟩ : syracuseStep 5273693 = 1977635) B1977635
theorem B1562731 : Blo 1561478 1562731 := bstep (se 1 (by rfl) ⟨1172048, by rfl⟩ : syracuseStep 1562731 = 2344097) B2344097
theorem B1562743 : Blo 1561478 1562743 := bstep (se 1 (by rfl) ⟨1172057, by rfl⟩ : syracuseStep 1562743 = 2344115) B2344115
theorem B2635915 : Blo 1561478 2635915 := bstep (se 1 (by rfl) ⟨1976936, by rfl⟩ : syracuseStep 2635915 = 3953873) B3953873
theorem B1562763 : Blo 1561478 1562763 := bstep (se 1 (by rfl) ⟨1172072, by rfl⟩ : syracuseStep 1562763 = 2344145) B2344145
theorem B1562775 : Blo 1561478 1562775 := bstep (se 1 (by rfl) ⟨1172081, by rfl⟩ : syracuseStep 1562775 = 2344163) B2344163
theorem B1562795 : Blo 1561478 1562795 := bstep (se 1 (by rfl) ⟨1172096, by rfl⟩ : syracuseStep 1562795 = 2344193) B2344193
theorem B5929139 : Blo 1561478 5929139 := bstep (se 1 (by rfl) ⟨4446854, by rfl⟩ : syracuseStep 5929139 = 8893709) B8893709
theorem B1562807 : Blo 1561478 1562807 := bstep (se 1 (by rfl) ⟨1172105, by rfl⟩ : syracuseStep 1562807 = 2344211) B2344211
theorem B2816203 : Blo 1561478 2816203 := bstep (se 1 (by rfl) ⟨2112152, by rfl⟩ : syracuseStep 2816203 = 4224305) B4224305
theorem B1562827 : Blo 1561478 1562827 := bstep (se 1 (by rfl) ⟨1172120, by rfl⟩ : syracuseStep 1562827 = 2344241) B2344241
theorem B1562839 : Blo 1561478 1562839 := bstep (se 1 (by rfl) ⟨1172129, by rfl⟩ : syracuseStep 1562839 = 2344259) B2344259
theorem B1562859 : Blo 1561478 1562859 := bstep (se 1 (by rfl) ⟨1172144, by rfl⟩ : syracuseStep 1562859 = 2344289) B2344289
theorem B1562871 : Blo 1561478 1562871 := bstep (se 1 (by rfl) ⟨1172153, by rfl⟩ : syracuseStep 1562871 = 2344307) B2344307
theorem B1562891 : Blo 1561478 1562891 := bstep (se 1 (by rfl) ⟨1172168, by rfl⟩ : syracuseStep 1562891 = 2344337) B2344337
theorem B1562903 : Blo 1561478 1562903 := bstep (se 1 (by rfl) ⟨1172177, by rfl⟩ : syracuseStep 1562903 = 2344355) B2344355
theorem B2636057 : Blo 1561478 2636057 := bstep (se 2 (by rfl) ⟨988521, by rfl⟩ : syracuseStep 2636057 = 1977043) B1977043
theorem B1562923 : Blo 1561478 1562923 := bstep (se 1 (by rfl) ⟨1172192, by rfl⟩ : syracuseStep 1562923 = 2344385) B2344385
theorem B1562935 : Blo 1561478 1562935 := bstep (se 1 (by rfl) ⟨1172201, by rfl⟩ : syracuseStep 1562935 = 2344403) B2344403
theorem B7911755 : Blo 1561478 7911755 := bstep (se 1 (by rfl) ⟨5933816, by rfl⟩ : syracuseStep 7911755 = 11867633) B11867633
theorem B1562955 : Blo 1561478 1562955 := bstep (se 1 (by rfl) ⟨1172216, by rfl⟩ : syracuseStep 1562955 = 2344433) B2344433
theorem B1562967 : Blo 1561478 1562967 := bstep (se 1 (by rfl) ⟨1172225, by rfl⟩ : syracuseStep 1562967 = 2344451) B2344451
theorem B1562987 : Blo 1561478 1562987 := bstep (se 1 (by rfl) ⟨1172240, by rfl⟩ : syracuseStep 1562987 = 2344481) B2344481
theorem B1562999 : Blo 1561478 1562999 := bstep (se 1 (by rfl) ⟨1172249, by rfl⟩ : syracuseStep 1562999 = 2344499) B2344499
theorem B1563019 : Blo 1561478 1563019 := bstep (se 1 (by rfl) ⟨1172264, by rfl⟩ : syracuseStep 1563019 = 2344529) B2344529
theorem B1563031 : Blo 1561478 1563031 := bstep (se 1 (by rfl) ⟨1172273, by rfl⟩ : syracuseStep 1563031 = 2344547) B2344547
theorem B2636185 : Blo 1561478 2636185 := bstep (se 2 (by rfl) ⟨988569, by rfl⟩ : syracuseStep 2636185 = 1977139) B1977139
theorem B1563051 : Blo 1561478 1563051 := bstep (se 1 (by rfl) ⟨1172288, by rfl⟩ : syracuseStep 1563051 = 2344577) B2344577
theorem B6674861 : Blo 1561478 6674861 := bstep (se 3 (by rfl) ⟨1251536, by rfl⟩ : syracuseStep 6674861 = 2503073) B2503073
theorem B1563063 : Blo 1561478 1563063 := bstep (se 1 (by rfl) ⟨1172297, by rfl⟩ : syracuseStep 1563063 = 2344595) B2344595
theorem B1563083 : Blo 1561478 1563083 := bstep (se 1 (by rfl) ⟨1172312, by rfl⟩ : syracuseStep 1563083 = 2344625) B2344625
theorem B1563095 : Blo 1561478 1563095 := bstep (se 1 (by rfl) ⟨1172321, by rfl⟩ : syracuseStep 1563095 = 2344643) B2344643
theorem B1563115 : Blo 1561478 1563115 := bstep (se 1 (by rfl) ⟨1172336, by rfl⟩ : syracuseStep 1563115 = 2344673) B2344673
theorem B1563127 : Blo 1561478 1563127 := bstep (se 1 (by rfl) ⟨1172345, by rfl⟩ : syracuseStep 1563127 = 2344691) B2344691
theorem B1563147 : Blo 1561478 1563147 := bstep (se 1 (by rfl) ⟨1172360, by rfl⟩ : syracuseStep 1563147 = 2344721) B2344721
theorem B1563159 : Blo 1561478 1563159 := bstep (se 1 (by rfl) ⟨1172369, by rfl⟩ : syracuseStep 1563159 = 2344739) B2344739
theorem B1563179 : Blo 1561478 1563179 := bstep (se 1 (by rfl) ⟨1172384, by rfl⟩ : syracuseStep 1563179 = 2344769) B2344769
theorem B1563191 : Blo 1561478 1563191 := bstep (se 1 (by rfl) ⟨1172393, by rfl⟩ : syracuseStep 1563191 = 2344787) B2344787
theorem B13351499 : Blo 1561478 13351499 := bstep (se 1 (by rfl) ⟨10013624, by rfl⟩ : syracuseStep 13351499 = 20027249) B20027249
theorem B7510603 : Blo 1561478 7510603 := bstep (se 1 (by rfl) ⟨5632952, by rfl⟩ : syracuseStep 7510603 = 11265905) B11265905
theorem B1563211 : Blo 1561478 1563211 := bstep (se 1 (by rfl) ⟨1172408, by rfl⟩ : syracuseStep 1563211 = 2344817) B2344817
theorem B1563223 : Blo 1561478 1563223 := bstep (se 1 (by rfl) ⟨1172417, by rfl⟩ : syracuseStep 1563223 = 2344835) B2344835
theorem B4446809 : Blo 1561478 4446809 := bstep (se 2 (by rfl) ⟨1667553, by rfl⟩ : syracuseStep 4446809 = 3335107) B3335107
theorem B1563243 : Blo 1561478 1563243 := bstep (se 1 (by rfl) ⟨1172432, by rfl⟩ : syracuseStep 1563243 = 2344865) B2344865
theorem B1563255 : Blo 1561478 1563255 := bstep (se 1 (by rfl) ⟨1172441, by rfl⟩ : syracuseStep 1563255 = 2344883) B2344883
theorem B1563275 : Blo 1561478 1563275 := bstep (se 1 (by rfl) ⟨1172456, by rfl⟩ : syracuseStep 1563275 = 2344913) B2344913
theorem B3955351 : Blo 1561478 3955351 := bstep (se 1 (by rfl) ⟨2966513, by rfl⟩ : syracuseStep 3955351 = 5933027) B5933027
theorem B1563287 : Blo 1561478 1563287 := bstep (se 1 (by rfl) ⟨1172465, by rfl⟩ : syracuseStep 1563287 = 2344931) B2344931
theorem B1563307 : Blo 1561478 1563307 := bstep (se 1 (by rfl) ⟨1172480, by rfl⟩ : syracuseStep 1563307 = 2344961) B2344961
theorem B1563319 : Blo 1561478 1563319 := bstep (se 1 (by rfl) ⟨1172489, by rfl⟩ : syracuseStep 1563319 = 2344979) B2344979
theorem B1563339 : Blo 1561478 1563339 := bstep (se 1 (by rfl) ⟨1172504, by rfl⟩ : syracuseStep 1563339 = 2345009) B2345009
theorem B1563351 : Blo 1561478 1563351 := bstep (se 1 (by rfl) ⟨1172513, by rfl⟩ : syracuseStep 1563351 = 2345027) B2345027
theorem B5003993 : Blo 1561478 5003993 := bstep (se 2 (by rfl) ⟨1876497, by rfl⟩ : syracuseStep 5003993 = 3752995) B3752995
theorem B1563371 : Blo 1561478 1563371 := bstep (se 1 (by rfl) ⟨1172528, by rfl⟩ : syracuseStep 1563371 = 2345057) B2345057
theorem B1563383 : Blo 1561478 1563383 := bstep (se 1 (by rfl) ⟨1172537, by rfl⟩ : syracuseStep 1563383 = 2345075) B2345075
theorem B6675203 : Blo 1561478 6675203 := bstep (se 1 (by rfl) ⟨5006402, by rfl⟩ : syracuseStep 6675203 = 10012805) B10012805
theorem B1563403 : Blo 1561478 1563403 := bstep (se 1 (by rfl) ⟨1172552, by rfl⟩ : syracuseStep 1563403 = 2345105) B2345105
theorem B1563415 : Blo 1561478 1563415 := bstep (se 1 (by rfl) ⟨1172561, by rfl⟩ : syracuseStep 1563415 = 2345123) B2345123
theorem B1563435 : Blo 1561478 1563435 := bstep (se 1 (by rfl) ⟨1172576, by rfl⟩ : syracuseStep 1563435 = 2345153) B2345153
theorem B1563447 : Blo 1561478 1563447 := bstep (se 1 (by rfl) ⟨1172585, by rfl⟩ : syracuseStep 1563447 = 2345171) B2345171
theorem B5929793 : Blo 1561478 5929793 := bstep (se 2 (by rfl) ⟨2223672, by rfl⟩ : syracuseStep 5929793 = 4447345) B4447345
theorem B1563467 : Blo 1561478 1563467 := bstep (se 1 (by rfl) ⟨1172600, by rfl⟩ : syracuseStep 1563467 = 2345201) B2345201
theorem B11860829 : Blo 1561478 11860829 := bstep (se 3 (by rfl) ⟨2223905, by rfl⟩ : syracuseStep 11860829 = 4447811) B4447811
theorem B3169153 : Blo 1561478 3169153 := bstep (se 2 (by rfl) ⟨1188432, by rfl⟩ : syracuseStep 3169153 = 2376865) B2376865
theorem B2374553 : Blo 1561478 2374553 := bstep (se 2 (by rfl) ⟨890457, by rfl⟩ : syracuseStep 2374553 = 1780915) B1780915
theorem B2636759 : Blo 1561478 2636759 := bstep (se 1 (by rfl) ⟨1977569, by rfl⟩ : syracuseStep 2636759 = 3955139) B3955139
theorem B8903641 : Blo 1561478 8903641 := bstep (se 2 (by rfl) ⟨3338865, by rfl⟩ : syracuseStep 8903641 = 6677731) B6677731
theorem B2817011 : Blo 1561478 2817011 := bstep (se 1 (by rfl) ⟨2112758, by rfl⟩ : syracuseStep 2817011 = 4225517) B4225517
theorem B3513419 : Blo 1561478 3513419 := bstep (se 1 (by rfl) ⟨2635064, by rfl⟩ : syracuseStep 3513419 = 5270129) B5270129
theorem B3955787 : Blo 1561478 3955787 := bstep (se 1 (by rfl) ⟨2966840, by rfl⟩ : syracuseStep 3955787 = 5933681) B5933681
theorem B2636887 : Blo 1561478 2636887 := bstep (se 1 (by rfl) ⟨1977665, by rfl⟩ : syracuseStep 2636887 = 3955331) B3955331
theorem B3513473 : Blo 1561478 3513473 := bstep (se 2 (by rfl) ⟨1317552, by rfl⟩ : syracuseStep 3513473 = 2635105) B2635105
theorem B5274827 : Blo 1561478 5274827 := bstep (se 1 (by rfl) ⟨3956120, by rfl⟩ : syracuseStep 5274827 = 7912241) B7912241
theorem B2964737 : Blo 1561478 2964737 := bstep (se 2 (by rfl) ⟨1111776, by rfl⟩ : syracuseStep 2964737 = 2223553) B2223553
theorem B2342219 : Blo 1561478 2342219 := bstep (se 1 (by rfl) ⟨1756664, by rfl⟩ : syracuseStep 2342219 = 3513329) B3513329
theorem B2342231 : Blo 1561478 2342231 := bstep (se 1 (by rfl) ⟨1756673, by rfl⟩ : syracuseStep 2342231 = 3513347) B3513347
theorem B3513689 : Blo 1561478 3513689 := bstep (se 2 (by rfl) ⟨1317633, by rfl⟩ : syracuseStep 3513689 = 2635267) B2635267
theorem B2342297 : Blo 1561478 2342297 := bstep (se 2 (by rfl) ⟨878361, by rfl⟩ : syracuseStep 2342297 = 1756723) B1756723
theorem B2375065 : Blo 1561478 2375065 := bstep (se 2 (by rfl) ⟨890649, by rfl⟩ : syracuseStep 2375065 = 1781299) B1781299
theorem B3513779 : Blo 1561478 3513779 := bstep (se 1 (by rfl) ⟨2635334, by rfl⟩ : syracuseStep 3513779 = 5270669) B5270669
theorem B3857843 : Blo 1561478 3857843 := bstep (se 1 (by rfl) ⟨2893382, by rfl⟩ : syracuseStep 3857843 = 5786765) B5786765
theorem B5004737 : Blo 1561478 5004737 := bstep (se 2 (by rfl) ⟨1876776, by rfl⟩ : syracuseStep 5004737 = 3753553) B3753553
theorem B3956161 : Blo 1561478 3956161 := bstep (se 2 (by rfl) ⟨1483560, by rfl⟩ : syracuseStep 3956161 = 2967121) B2967121
theorem B3513815 : Blo 1561478 3513815 := bstep (se 1 (by rfl) ⟨2635361, by rfl⟩ : syracuseStep 3513815 = 5270723) B5270723
theorem B5275097 : Blo 1561478 5275097 := bstep (se 2 (by rfl) ⟨1978161, by rfl⟩ : syracuseStep 5275097 = 3956323) B3956323
theorem B2342411 : Blo 1561478 2342411 := bstep (se 1 (by rfl) ⟨1756808, by rfl⟩ : syracuseStep 2342411 = 3513617) B3513617
theorem B17800721 : Blo 1561478 17800721 := bstep (se 2 (by rfl) ⟨6675270, by rfl⟩ : syracuseStep 17800721 = 13350541) B13350541
theorem B2342423 : Blo 1561478 2342423 := bstep (se 1 (by rfl) ⟨1756817, by rfl⟩ : syracuseStep 2342423 = 3513635) B3513635
theorem B15228491 : Blo 1561478 15228491 := bstep (se 1 (by rfl) ⟨11421368, by rfl⟩ : syracuseStep 15228491 = 22842737) B22842737
theorem B2965079 : Blo 1561478 2965079 := bstep (se 1 (by rfl) ⟨2223809, by rfl⟩ : syracuseStep 2965079 = 4447619) B4447619
theorem B2342489 : Blo 1561478 2342489 := bstep (se 2 (by rfl) ⟨878433, by rfl⟩ : syracuseStep 2342489 = 1756867) B1756867
theorem B21372509 : Blo 1561478 21372509 := bstep (se 3 (by rfl) ⟨4007345, by rfl⟩ : syracuseStep 21372509 = 8014691) B8014691
theorem B3513995 : Blo 1561478 3513995 := bstep (se 1 (by rfl) ⟨2635496, by rfl⟩ : syracuseStep 3513995 = 5270993) B5270993
theorem B3514049 : Blo 1561478 3514049 := bstep (se 2 (by rfl) ⟨1317768, by rfl⟩ : syracuseStep 3514049 = 2635537) B2635537
theorem B3047105 : Blo 1561478 3047105 := bstep (se 2 (by rfl) ⟨1142664, by rfl⟩ : syracuseStep 3047105 = 2285329) B2285329
theorem B2342603 : Blo 1561478 2342603 := bstep (se 1 (by rfl) ⟨1756952, by rfl⟩ : syracuseStep 2342603 = 3513905) B3513905
theorem B2637515 : Blo 1561478 2637515 := bstep (se 1 (by rfl) ⟨1978136, by rfl⟩ : syracuseStep 2637515 = 3956273) B3956273
theorem B2342615 : Blo 1561478 2342615 := bstep (se 1 (by rfl) ⟨1756961, by rfl⟩ : syracuseStep 2342615 = 3513923) B3513923
theorem B2342681 : Blo 1561478 2342681 := bstep (se 2 (by rfl) ⟨878505, by rfl⟩ : syracuseStep 2342681 = 1757011) B1757011
theorem B2637643 : Blo 1561478 2637643 := bstep (se 1 (by rfl) ⟨1978232, by rfl⟩ : syracuseStep 2637643 = 3956465) B3956465
theorem B10149725 : Blo 1561478 10149725 := bstep (se 3 (by rfl) ⟨1903073, by rfl⟩ : syracuseStep 10149725 = 3806147) B3806147
theorem B2342795 : Blo 1561478 2342795 := bstep (se 1 (by rfl) ⟨1757096, by rfl⟩ : syracuseStep 2342795 = 3514193) B3514193
theorem B2342807 : Blo 1561478 2342807 := bstep (se 1 (by rfl) ⟨1757105, by rfl⟩ : syracuseStep 2342807 = 3514211) B3514211
theorem B3514265 : Blo 1561478 3514265 := bstep (se 2 (by rfl) ⟨1317849, by rfl⟩ : syracuseStep 3514265 = 2635699) B2635699
theorem B16883633 : Blo 1561478 16883633 := bstep (se 2 (by rfl) ⟨6331362, by rfl⟩ : syracuseStep 16883633 = 12662725) B12662725
theorem B2342873 : Blo 1561478 2342873 := bstep (se 2 (by rfl) ⟨878577, by rfl⟩ : syracuseStep 2342873 = 1757155) B1757155
theorem B2637785 : Blo 1561478 2637785 := bstep (se 2 (by rfl) ⟨989169, by rfl⟩ : syracuseStep 2637785 = 1978339) B1978339
theorem B3514355 : Blo 1561478 3514355 := bstep (se 1 (by rfl) ⟨2635766, by rfl⟩ : syracuseStep 3514355 = 5271533) B5271533
theorem B4448267 : Blo 1561478 4448267 := bstep (se 1 (by rfl) ⟨3336200, by rfl⟩ : syracuseStep 4448267 = 6672401) B6672401
theorem B2342927 : Blo 1561478 2342927 := bstep (se 1 (by rfl) ⟨1757195, by rfl⟩ : syracuseStep 2342927 = 3514391) B3514391
theorem B2637839 : Blo 1561478 2637839 := bstep (se 1 (by rfl) ⟨1978379, by rfl⟩ : syracuseStep 2637839 = 3956759) B3956759
theorem B5275691 : Blo 1561478 5275691 := bstep (se 1 (by rfl) ⟨3956768, by rfl⟩ : syracuseStep 5275691 = 7913537) B7913537
theorem B20013101 : Blo 1561478 20013101 := bstep (se 3 (by rfl) ⟨3752456, by rfl⟩ : syracuseStep 20013101 = 7504913) B7504913
theorem B2342969 : Blo 1561478 2342969 := bstep (se 2 (by rfl) ⟨878613, by rfl⟩ : syracuseStep 2342969 = 1757227) B1757227
theorem B3514427 : Blo 1561478 3514427 := bstep (se 1 (by rfl) ⟨2635820, by rfl⟩ : syracuseStep 3514427 = 5271641) B5271641
theorem B2343047 : Blo 1561478 2343047 := bstep (se 1 (by rfl) ⟨1757285, by rfl⟩ : syracuseStep 2343047 = 3514571) B3514571
theorem B2343083 : Blo 1561478 2343083 := bstep (se 1 (by rfl) ⟨1757312, by rfl⟩ : syracuseStep 2343083 = 3514625) B3514625
theorem B3514553 : Blo 1561478 3514553 := bstep (se 2 (by rfl) ⟨1317957, by rfl⟩ : syracuseStep 3514553 = 2635915) B2635915
theorem B3956921 : Blo 1561478 3956921 := bstep (se 2 (by rfl) ⟨1483845, by rfl⟩ : syracuseStep 3956921 = 2967691) B2967691
theorem B2343113 : Blo 1561478 2343113 := bstep (se 2 (by rfl) ⟨878667, by rfl⟩ : syracuseStep 2343113 = 1757335) B1757335
theorem B42787061 : Blo 1561478 42787061 := bstep (se 5 (by rfl) ⟨2005643, by rfl⟩ : syracuseStep 42787061 = 4011287) B4011287
theorem B5931265 : Blo 1561478 5931265 := bstep (se 2 (by rfl) ⟨2224224, by rfl⟩ : syracuseStep 5931265 = 4448449) B4448449
theorem B5005583 : Blo 1561478 5005583 := bstep (se 1 (by rfl) ⟨3754187, by rfl⟩ : syracuseStep 5005583 = 7508375) B7508375
theorem B7512335 : Blo 1561478 7512335 := bstep (se 1 (by rfl) ⟨5634251, by rfl⟩ : syracuseStep 7512335 = 11268503) B11268503
theorem B1876267 : Blo 1561478 1876267 := bstep (se 1 (by rfl) ⟨1407200, by rfl⟩ : syracuseStep 1876267 = 2814401) B2814401
theorem B2343227 : Blo 1561478 2343227 := bstep (se 1 (by rfl) ⟨1757420, by rfl⟩ : syracuseStep 2343227 = 3514841) B3514841
theorem B13353275 : Blo 1561478 13353275 := bstep (se 1 (by rfl) ⟨10014956, by rfl⟩ : syracuseStep 13353275 = 20029913) B20029913
theorem B182714737 : Blo 1561478 182714737 := bstep (se 2 (by rfl) ⟨68518026, by rfl⟩ : syracuseStep 182714737 = 137036053) B137036053
theorem B2343287 : Blo 1561478 2343287 := bstep (se 1 (by rfl) ⟨1757465, by rfl⟩ : syracuseStep 2343287 = 3514931) B3514931
theorem B2343311 : Blo 1561478 2343311 := bstep (se 1 (by rfl) ⟨1757483, by rfl⟩ : syracuseStep 2343311 = 3514967) B3514967
theorem B2343353 : Blo 1561478 2343353 := bstep (se 2 (by rfl) ⟨878757, by rfl⟩ : syracuseStep 2343353 = 1757515) B1757515
theorem B2343431 : Blo 1561478 2343431 := bstep (se 1 (by rfl) ⟨1757573, by rfl⟩ : syracuseStep 2343431 = 3515147) B3515147
theorem B3514895 : Blo 1561478 3514895 := bstep (se 1 (by rfl) ⟨2636171, by rfl⟩ : syracuseStep 3514895 = 5272343) B5272343
theorem B3514913 : Blo 1561478 3514913 := bstep (se 2 (by rfl) ⟨1318092, by rfl⟩ : syracuseStep 3514913 = 2636185) B2636185
theorem B2343467 : Blo 1561478 2343467 := bstep (se 1 (by rfl) ⟨1757600, by rfl⟩ : syracuseStep 2343467 = 3515201) B3515201
theorem B3007019 : Blo 1561478 3007019 := bstep (se 1 (by rfl) ⟨2255264, by rfl⟩ : syracuseStep 3007019 = 4510529) B4510529
theorem B2343497 : Blo 1561478 2343497 := bstep (se 2 (by rfl) ⟨878811, by rfl⟩ : syracuseStep 2343497 = 1757623) B1757623
theorem B1876651 : Blo 1561478 1876651 := bstep (se 1 (by rfl) ⟨1407488, by rfl⟩ : syracuseStep 1876651 = 2814977) B2814977
theorem B2343611 : Blo 1561478 2343611 := bstep (se 1 (by rfl) ⟨1757708, by rfl⟩ : syracuseStep 2343611 = 3515417) B3515417
theorem B7914185 : Blo 1561478 7914185 := bstep (se 2 (by rfl) ⟨2967819, by rfl⟩ : syracuseStep 7914185 = 5935639) B5935639
theorem B2343671 : Blo 1561478 2343671 := bstep (se 1 (by rfl) ⟨1757753, by rfl⟩ : syracuseStep 2343671 = 3515507) B3515507
theorem B2343695 : Blo 1561478 2343695 := bstep (se 1 (by rfl) ⟨1757771, by rfl⟩ : syracuseStep 2343695 = 3515543) B3515543
theorem B24044323 : Blo 1561478 24044323 := bstep (se 1 (by rfl) ⟨18033242, by rfl⟩ : syracuseStep 24044323 = 36066485) B36066485
theorem B20292389 : Blo 1561478 20292389 := bstep (se 4 (by rfl) ⟨1902411, by rfl⟩ : syracuseStep 20292389 = 3804823) B3804823
theorem B15008561 : Blo 1561478 15008561 := bstep (se 2 (by rfl) ⟨5628210, by rfl⟩ : syracuseStep 15008561 = 11256421) B11256421
theorem B2343737 : Blo 1561478 2343737 := bstep (se 2 (by rfl) ⟨878901, by rfl⟩ : syracuseStep 2343737 = 1757803) B1757803
theorem B9634619 : Blo 1561478 9634619 := bstep (se 1 (by rfl) ⟨7225964, by rfl⟩ : syracuseStep 9634619 = 14451929) B14451929
theorem B3515255 : Blo 1561478 3515255 := bstep (se 1 (by rfl) ⟨2636441, by rfl⟩ : syracuseStep 3515255 = 5272883) B5272883
theorem B2343815 : Blo 1561478 2343815 := bstep (se 1 (by rfl) ⟨1757861, by rfl⟩ : syracuseStep 2343815 = 3515723) B3515723
theorem B2343851 : Blo 1561478 2343851 := bstep (se 1 (by rfl) ⟨1757888, by rfl⟩ : syracuseStep 2343851 = 3515777) B3515777
theorem B2343881 : Blo 1561478 2343881 := bstep (se 2 (by rfl) ⟨878955, by rfl⟩ : syracuseStep 2343881 = 1757911) B1757911
theorem B3515435 : Blo 1561478 3515435 := bstep (se 1 (by rfl) ⟨2636576, by rfl⟩ : syracuseStep 3515435 = 5273153) B5273153
theorem B2343995 : Blo 1561478 2343995 := bstep (se 1 (by rfl) ⟨1757996, by rfl⟩ : syracuseStep 2343995 = 3515993) B3515993
theorem B2344055 : Blo 1561478 2344055 := bstep (se 1 (by rfl) ⟨1758041, by rfl⟩ : syracuseStep 2344055 = 3516083) B3516083
theorem B2344079 : Blo 1561478 2344079 := bstep (se 1 (by rfl) ⟨1758059, by rfl⟩ : syracuseStep 2344079 = 3516119) B3516119
theorem B2344121 : Blo 1561478 2344121 := bstep (se 2 (by rfl) ⟨879045, by rfl⟩ : syracuseStep 2344121 = 1758091) B1758091
theorem B6767873 : Blo 1561478 6767873 := bstep (se 2 (by rfl) ⟨2537952, by rfl⟩ : syracuseStep 6767873 = 5075905) B5075905
theorem B2344199 : Blo 1561478 2344199 := bstep (se 1 (by rfl) ⟨1758149, by rfl⟩ : syracuseStep 2344199 = 3516299) B3516299
theorem B11871521 : Blo 1561478 11871521 := bstep (se 2 (by rfl) ⟨4451820, by rfl⟩ : syracuseStep 11871521 = 8903641) B8903641
theorem B2344235 : Blo 1561478 2344235 := bstep (se 1 (by rfl) ⟨1758176, by rfl⟩ : syracuseStep 2344235 = 3516353) B3516353
theorem B2344265 : Blo 1561478 2344265 := bstep (se 2 (by rfl) ⟨879099, by rfl⟩ : syracuseStep 2344265 = 1758199) B1758199
theorem B3515795 : Blo 1561478 3515795 := bstep (se 1 (by rfl) ⟨2636846, by rfl⟩ : syracuseStep 3515795 = 5273693) B5273693
theorem B2966969 : Blo 1561478 2966969 := bstep (se 2 (by rfl) ⟨1112613, by rfl⟩ : syracuseStep 2966969 = 2225227) B2225227
theorem B2344379 : Blo 1561478 2344379 := bstep (se 1 (by rfl) ⟨1758284, by rfl⟩ : syracuseStep 2344379 = 3516569) B3516569
theorem B3515849 : Blo 1561478 3515849 := bstep (se 2 (by rfl) ⟨1318443, by rfl⟩ : syracuseStep 3515849 = 2636887) B2636887
theorem B2344439 : Blo 1561478 2344439 := bstep (se 1 (by rfl) ⟨1758329, by rfl⟩ : syracuseStep 2344439 = 3516659) B3516659
theorem B2344463 : Blo 1561478 2344463 := bstep (se 1 (by rfl) ⟨1758347, by rfl⟩ : syracuseStep 2344463 = 3516695) B3516695
theorem B2344505 : Blo 1561478 2344505 := bstep (se 2 (by rfl) ⟨879189, by rfl⟩ : syracuseStep 2344505 = 1758379) B1758379
theorem B56993357 : Blo 1561478 56993357 := bstep (se 3 (by rfl) ⟨10686254, by rfl⟩ : syracuseStep 56993357 = 21372509) B21372509
theorem B4449907 : Blo 1561478 4449907 := bstep (se 1 (by rfl) ⟨3337430, by rfl⟩ : syracuseStep 4449907 = 6674861) B6674861
theorem B15025783 : Blo 1561478 15025783 := bstep (se 1 (by rfl) ⟨11269337, by rfl⟩ : syracuseStep 15025783 = 22538675) B22538675
theorem B2344583 : Blo 1561478 2344583 := bstep (se 1 (by rfl) ⟨1758437, by rfl⟩ : syracuseStep 2344583 = 3516875) B3516875
theorem B2344619 : Blo 1561478 2344619 := bstep (se 1 (by rfl) ⟨1758464, by rfl⟩ : syracuseStep 2344619 = 3516929) B3516929
theorem B11863745 : Blo 1561478 11863745 := bstep (se 2 (by rfl) ⟨4448904, by rfl⟩ : syracuseStep 11863745 = 8897809) B8897809
theorem B2344649 : Blo 1561478 2344649 := bstep (se 2 (by rfl) ⟨879243, by rfl⟩ : syracuseStep 2344649 = 1758487) B1758487
theorem B7505723 : Blo 1561478 7505723 := bstep (se 1 (by rfl) ⟨5629292, by rfl⟩ : syracuseStep 7505723 = 11258585) B11258585
theorem B3335995 : Blo 1561478 3335995 := bstep (se 1 (by rfl) ⟨2501996, by rfl⟩ : syracuseStep 3335995 = 5003993) B5003993
theorem B2344763 : Blo 1561478 2344763 := bstep (se 1 (by rfl) ⟨1758572, by rfl⟩ : syracuseStep 2344763 = 3517145) B3517145
theorem B60868421 : Blo 1561478 60868421 := bstep (se 4 (by rfl) ⟨5706414, by rfl⟩ : syracuseStep 60868421 = 11412829) B11412829
theorem B4450135 : Blo 1561478 4450135 := bstep (se 1 (by rfl) ⟨3337601, by rfl⟩ : syracuseStep 4450135 = 6675203) B6675203
theorem B2344823 : Blo 1561478 2344823 := bstep (se 1 (by rfl) ⟨1758617, by rfl⟩ : syracuseStep 2344823 = 3517235) B3517235
theorem B2344847 : Blo 1561478 2344847 := bstep (se 1 (by rfl) ⟨1758635, by rfl⟩ : syracuseStep 2344847 = 3517271) B3517271
theorem B7907219 : Blo 1561478 7907219 := bstep (se 1 (by rfl) ⟨5930414, by rfl⟩ : syracuseStep 7907219 = 11860829) B11860829
theorem B13354915 : Blo 1561478 13354915 := bstep (se 1 (by rfl) ⟨10016186, by rfl⟩ : syracuseStep 13354915 = 20032373) B20032373
theorem B2344889 : Blo 1561478 2344889 := bstep (se 2 (by rfl) ⟨879333, by rfl⟩ : syracuseStep 2344889 = 1758667) B1758667
theorem B1878007 : Blo 1561478 1878007 := bstep (se 1 (by rfl) ⟨1408505, by rfl⟩ : syracuseStep 1878007 = 2817011) B2817011
theorem B2344967 : Blo 1561478 2344967 := bstep (se 1 (by rfl) ⟨1758725, by rfl⟩ : syracuseStep 2344967 = 3517451) B3517451
theorem B33785869 : Blo 1561478 33785869 := bstep (se 3 (by rfl) ⟨6334850, by rfl⟩ : syracuseStep 33785869 = 12669701) B12669701
theorem B2345003 : Blo 1561478 2345003 := bstep (se 1 (by rfl) ⟨1758752, by rfl⟩ : syracuseStep 2345003 = 3517505) B3517505
theorem B2345033 : Blo 1561478 2345033 := bstep (se 2 (by rfl) ⟨879387, by rfl⟩ : syracuseStep 2345033 = 1758775) B1758775
theorem B12667013 : Blo 1561478 12667013 := bstep (se 4 (by rfl) ⟨1187532, by rfl⟩ : syracuseStep 12667013 = 2375065) B2375065
theorem B3516551 : Blo 1561478 3516551 := bstep (se 1 (by rfl) ⟨2637413, by rfl⟩ : syracuseStep 3516551 = 5274827) B5274827
theorem B1976491 : Blo 1561478 1976491 := bstep (se 1 (by rfl) ⟨1482368, by rfl⟩ : syracuseStep 1976491 = 2964737) B2964737
theorem B2345147 : Blo 1561478 2345147 := bstep (se 1 (by rfl) ⟨1758860, by rfl⟩ : syracuseStep 2345147 = 3517721) B3517721
theorem B11872493 : Blo 1561478 11872493 := bstep (se 3 (by rfl) ⟨2226092, by rfl⟩ : syracuseStep 11872493 = 4452185) B4452185
theorem B2345207 : Blo 1561478 2345207 := bstep (se 1 (by rfl) ⟨1758905, by rfl⟩ : syracuseStep 2345207 = 3517811) B3517811
theorem B3336491 : Blo 1561478 3336491 := bstep (se 1 (by rfl) ⟨2502368, by rfl⟩ : syracuseStep 3336491 = 5004737) B5004737
theorem B3516731 : Blo 1561478 3516731 := bstep (se 1 (by rfl) ⟨2637548, by rfl⟩ : syracuseStep 3516731 = 5275097) B5275097
theorem B1976719 : Blo 1561478 1976719 := bstep (se 1 (by rfl) ⟨1482539, by rfl⟩ : syracuseStep 1976719 = 2965079) B2965079
theorem B6670745 : Blo 1561478 6670745 := bstep (se 2 (by rfl) ⟨2501529, by rfl⟩ : syracuseStep 6670745 = 5003059) B5003059
theorem B3516857 : Blo 1561478 3516857 := bstep (se 2 (by rfl) ⟨1318821, by rfl⟩ : syracuseStep 3516857 = 2637643) B2637643
theorem B3754649 : Blo 1561478 3754649 := bstep (se 2 (by rfl) ⟨1407993, by rfl⟩ : syracuseStep 3754649 = 2815987) B2815987
theorem B25340633 : Blo 1561478 25340633 := bstep (se 2 (by rfl) ⟨9502737, by rfl⟩ : syracuseStep 25340633 = 19005475) B19005475
theorem B10693349 : Blo 1561478 10693349 := bstep (se 4 (by rfl) ⟨1002501, by rfl⟩ : syracuseStep 10693349 = 2005003) B2005003
theorem B16034561 : Blo 1561478 16034561 := bstep (se 2 (by rfl) ⟨6012960, by rfl⟩ : syracuseStep 16034561 = 12025921) B12025921
theorem B1583879 : Blo 1561478 1583879 := bstep (se 1 (by rfl) ⟨1187909, by rfl⟩ : syracuseStep 1583879 = 2375819) B2375819
theorem B3517199 : Blo 1561478 3517199 := bstep (se 1 (by rfl) ⟨2637899, by rfl⟩ : syracuseStep 3517199 = 5275799) B5275799
theorem B3517217 : Blo 1561478 3517217 := bstep (se 2 (by rfl) ⟨1318956, by rfl⟩ : syracuseStep 3517217 = 2637913) B2637913
theorem B2501561 : Blo 1561478 2501561 := bstep (se 2 (by rfl) ⟨938085, by rfl⟩ : syracuseStep 2501561 = 1876171) B1876171
theorem B3754937 : Blo 1561478 3754937 := bstep (se 2 (by rfl) ⟨1408101, by rfl⟩ : syracuseStep 3754937 = 2816203) B2816203
theorem B15019019 : Blo 1561478 15019019 := bstep (se 1 (by rfl) ⟨11264264, by rfl⟩ : syracuseStep 15019019 = 22528529) B22528529
theorem B5270615 : Blo 1561478 5270615 := bstep (se 1 (by rfl) ⟨3952961, by rfl⟩ : syracuseStep 5270615 = 7905923) B7905923
theorem B5934167 : Blo 1561478 5934167 := bstep (se 1 (by rfl) ⟨4450625, by rfl⟩ : syracuseStep 5934167 = 8901251) B8901251
theorem B1977463 : Blo 1561478 1977463 := bstep (se 1 (by rfl) ⟨1483097, by rfl⟩ : syracuseStep 1977463 = 2966195) B2966195
theorem B3517559 : Blo 1561478 3517559 := bstep (se 1 (by rfl) ⟨2638169, by rfl⟩ : syracuseStep 3517559 = 5276339) B5276339
theorem B14445701 : Blo 1561478 14445701 := bstep (se 4 (by rfl) ⟨1354284, by rfl⟩ : syracuseStep 14445701 = 2708569) B2708569
theorem B3517739 : Blo 1561478 3517739 := bstep (se 1 (by rfl) ⟨2638304, by rfl⟩ : syracuseStep 3517739 = 5276609) B5276609
theorem B4451719 : Blo 1561478 4451719 := bstep (se 1 (by rfl) ⟨3338789, by rfl⟩ : syracuseStep 4451719 = 6677579) B6677579
theorem B6335891 : Blo 1561478 6335891 := bstep (se 1 (by rfl) ⟨4751918, by rfl⟩ : syracuseStep 6335891 = 9503837) B9503837
theorem B10014137 : Blo 1561478 10014137 := bstep (se 2 (by rfl) ⟨3755301, by rfl⟩ : syracuseStep 10014137 = 7510603) B7510603
theorem B1977787 : Blo 1561478 1977787 := bstep (se 1 (by rfl) ⟨1483340, by rfl⟩ : syracuseStep 1977787 = 2966681) B2966681
theorem B1756687 : Blo 1561478 1756687 := bstep (se 1 (by rfl) ⟨1317515, by rfl⟩ : syracuseStep 1756687 = 2635031) B2635031
theorem B5271101 : Blo 1561478 5271101 := bstep (se 3 (by rfl) ⟨988331, by rfl⟩ : syracuseStep 5271101 = 1976663) B1976663
theorem B5934653 : Blo 1561478 5934653 := bstep (se 3 (by rfl) ⟨1112747, by rfl⟩ : syracuseStep 5934653 = 2225495) B2225495
theorem B4451993 : Blo 1561478 4451993 := bstep (se 2 (by rfl) ⟨1669497, by rfl⟩ : syracuseStep 4451993 = 3338995) B3338995
theorem B18034447 : Blo 1561478 18034447 := bstep (se 1 (by rfl) ⟨13525835, by rfl⟩ : syracuseStep 18034447 = 27051671) B27051671
theorem B16904051 : Blo 1561478 16904051 := bstep (se 1 (by rfl) ⟨12678038, by rfl⟩ : syracuseStep 16904051 = 25356077) B25356077
theorem B1978283 : Blo 1561478 1978283 := bstep (se 1 (by rfl) ⟨1483712, by rfl⟩ : syracuseStep 1978283 = 2967425) B2967425
theorem B1757191 : Blo 1561478 1757191 := bstep (se 1 (by rfl) ⟨1317893, by rfl⟩ : syracuseStep 1757191 = 2635787) B2635787
theorem B3952759 : Blo 1561478 3952759 := bstep (se 1 (by rfl) ⟨2964569, by rfl⟩ : syracuseStep 3952759 = 5929139) B5929139
theorem B1757371 : Blo 1561478 1757371 := bstep (se 1 (by rfl) ⟨1318028, by rfl⟩ : syracuseStep 1757371 = 2636057) B2636057
theorem B2502971 : Blo 1561478 2502971 := bstep (se 1 (by rfl) ⟨1877228, by rfl⟩ : syracuseStep 2502971 = 3754457) B3754457
theorem B8900999 : Blo 1561478 8900999 := bstep (se 1 (by rfl) ⟨6675749, by rfl⟩ : syracuseStep 8900999 = 13351499) B13351499
theorem B1978759 : Blo 1561478 1978759 := bstep (se 1 (by rfl) ⟨1484069, by rfl⟩ : syracuseStep 1978759 = 2968139) B2968139
theorem B20034013 : Blo 1561478 20034013 := bstep (se 3 (by rfl) ⟨3756377, by rfl⟩ : syracuseStep 20034013 = 7512755) B7512755
theorem B28504561 : Blo 1561478 28504561 := bstep (se 2 (by rfl) ⟨10689210, by rfl⟩ : syracuseStep 28504561 = 21378421) B21378421
theorem B9024011 : Blo 1561478 9024011 := bstep (se 1 (by rfl) ⟨6768008, by rfl⟩ : syracuseStep 9024011 = 13536017) B13536017
theorem B3953195 : Blo 1561478 3953195 := bstep (se 1 (by rfl) ⟨2964896, by rfl⟩ : syracuseStep 3953195 = 5929793) B5929793
theorem B1757839 : Blo 1561478 1757839 := bstep (se 1 (by rfl) ⟨1318379, by rfl⟩ : syracuseStep 1757839 = 2636759) B2636759
theorem B2224783 : Blo 1561478 2224783 := bstep (se 1 (by rfl) ⟨1668587, by rfl⟩ : syracuseStep 2224783 = 3337175) B3337175
theorem B2224903 : Blo 1561478 2224903 := bstep (se 1 (by rfl) ⟨1668677, by rfl⟩ : syracuseStep 2224903 = 3337355) B3337355
theorem B10007347 : Blo 1561478 10007347 := bstep (se 1 (by rfl) ⟨7505510, by rfl⟩ : syracuseStep 10007347 = 15011021) B15011021
theorem B1561479 : Blo 1561478 1561479 := bstep (se 1 (by rfl) ⟨1171109, by rfl⟩ : syracuseStep 1561479 = 2342219) B2342219
theorem B1561487 : Blo 1561478 1561487 := bstep (se 1 (by rfl) ⟨1171115, by rfl⟩ : syracuseStep 1561487 = 2342231) B2342231
theorem B7910297 : Blo 1561478 7910297 := bstep (se 2 (by rfl) ⟨2966361, by rfl⟩ : syracuseStep 7910297 = 5932723) B5932723
theorem B5272505 : Blo 1561478 5272505 := bstep (se 2 (by rfl) ⟨1977189, by rfl⟩ : syracuseStep 5272505 = 3954379) B3954379
theorem B1561531 : Blo 1561478 1561531 := bstep (se 1 (by rfl) ⟨1171148, by rfl⟩ : syracuseStep 1561531 = 2342297) B2342297
theorem B1561607 : Blo 1561478 1561607 := bstep (se 1 (by rfl) ⟨1171205, by rfl⟩ : syracuseStep 1561607 = 2342411) B2342411
theorem B11867147 : Blo 1561478 11867147 := bstep (se 1 (by rfl) ⟨8900360, by rfl⟩ : syracuseStep 11867147 = 17800721) B17800721
theorem B1561615 : Blo 1561478 1561615 := bstep (se 1 (by rfl) ⟨1171211, by rfl⟩ : syracuseStep 1561615 = 2342423) B2342423
theorem B1561659 : Blo 1561478 1561659 := bstep (se 1 (by rfl) ⟨1171244, by rfl⟩ : syracuseStep 1561659 = 2342489) B2342489
theorem B1561735 : Blo 1561478 1561735 := bstep (se 1 (by rfl) ⟨1171301, by rfl⟩ : syracuseStep 1561735 = 2342603) B2342603
theorem B1758343 : Blo 1561478 1758343 := bstep (se 1 (by rfl) ⟨1318757, by rfl⟩ : syracuseStep 1758343 = 2637515) B2637515
theorem B1561743 : Blo 1561478 1561743 := bstep (se 1 (by rfl) ⟨1171307, by rfl⟩ : syracuseStep 1561743 = 2342615) B2342615
theorem B901805237 : Blo 1561478 901805237 := bstep (se 5 (by rfl) ⟨42272120, by rfl⟩ : syracuseStep 901805237 = 84544241) B84544241
theorem B1561787 : Blo 1561478 1561787 := bstep (se 1 (by rfl) ⟨1171340, by rfl⟩ : syracuseStep 1561787 = 2342681) B2342681
theorem B1561863 : Blo 1561478 1561863 := bstep (se 1 (by rfl) ⟨1171397, by rfl⟩ : syracuseStep 1561863 = 2342795) B2342795
theorem B1561871 : Blo 1561478 1561871 := bstep (se 1 (by rfl) ⟨1171403, by rfl⟩ : syracuseStep 1561871 = 2342807) B2342807
theorem B2635051 : Blo 1561478 2635051 := bstep (se 1 (by rfl) ⟨1976288, by rfl⟩ : syracuseStep 2635051 = 3952577) B3952577
theorem B1561915 : Blo 1561478 1561915 := bstep (se 1 (by rfl) ⟨1171436, by rfl⟩ : syracuseStep 1561915 = 2342873) B2342873
theorem B1758523 : Blo 1561478 1758523 := bstep (se 1 (by rfl) ⟨1318892, by rfl⟩ : syracuseStep 1758523 = 2637785) B2637785
theorem B3954035 : Blo 1561478 3954035 := bstep (se 1 (by rfl) ⟨2965526, by rfl⟩ : syracuseStep 3954035 = 5931053) B5931053
theorem B2110855 : Blo 1561478 2110855 := bstep (se 1 (by rfl) ⟨1583141, by rfl⟩ : syracuseStep 2110855 = 3166283) B3166283
theorem B1561991 : Blo 1561478 1561991 := bstep (se 1 (by rfl) ⟨1171493, by rfl⟩ : syracuseStep 1561991 = 2342987) B2342987
theorem B3954055 : Blo 1561478 3954055 := bstep (se 1 (by rfl) ⟨2965541, by rfl⟩ : syracuseStep 3954055 = 5931083) B5931083
theorem B1561999 : Blo 1561478 1561999 := bstep (se 1 (by rfl) ⟨1171499, by rfl⟩ : syracuseStep 1561999 = 2342999) B2342999
theorem B2635193 : Blo 1561478 2635193 := bstep (se 2 (by rfl) ⟨988197, by rfl⟩ : syracuseStep 2635193 = 1976395) B1976395
theorem B1562043 : Blo 1561478 1562043 := bstep (se 1 (by rfl) ⟨1171532, by rfl⟩ : syracuseStep 1562043 = 2343065) B2343065
theorem B1562119 : Blo 1561478 1562119 := bstep (se 1 (by rfl) ⟨1171589, by rfl⟩ : syracuseStep 1562119 = 2343179) B2343179
theorem B5273099 : Blo 1561478 5273099 := bstep (se 1 (by rfl) ⟨3954824, by rfl⟩ : syracuseStep 5273099 = 7909649) B7909649
theorem B1562127 : Blo 1561478 1562127 := bstep (se 1 (by rfl) ⟨1171595, by rfl⟩ : syracuseStep 1562127 = 2343191) B2343191
theorem B1562171 : Blo 1561478 1562171 := bstep (se 1 (by rfl) ⟨1171628, by rfl⟩ : syracuseStep 1562171 = 2343257) B2343257
theorem B5273207 : Blo 1561478 5273207 := bstep (se 1 (by rfl) ⟨3954905, by rfl⟩ : syracuseStep 5273207 = 7909811) B7909811
theorem B1562247 : Blo 1561478 1562247 := bstep (se 1 (by rfl) ⟨1171685, by rfl⟩ : syracuseStep 1562247 = 2343371) B2343371
theorem B1562255 : Blo 1561478 1562255 := bstep (se 1 (by rfl) ⟨1171691, by rfl⟩ : syracuseStep 1562255 = 2343383) B2343383
theorem B3954329 : Blo 1561478 3954329 := bstep (se 2 (by rfl) ⟨1482873, by rfl⟩ : syracuseStep 3954329 = 2965747) B2965747
theorem B1562299 : Blo 1561478 1562299 := bstep (se 1 (by rfl) ⟨1171724, by rfl⟩ : syracuseStep 1562299 = 2343449) B2343449
theorem B6674177 : Blo 1561478 6674177 := bstep (se 2 (by rfl) ⟨2502816, by rfl⟩ : syracuseStep 6674177 = 5005633) B5005633
theorem B1562375 : Blo 1561478 1562375 := bstep (se 1 (by rfl) ⟨1171781, by rfl⟩ : syracuseStep 1562375 = 2343563) B2343563
theorem B1562383 : Blo 1561478 1562383 := bstep (se 1 (by rfl) ⟨1171787, by rfl⟩ : syracuseStep 1562383 = 2343575) B2343575
theorem B3954491 : Blo 1561478 3954491 := bstep (se 1 (by rfl) ⟨2965868, by rfl⟩ : syracuseStep 3954491 = 5931737) B5931737
theorem B1562427 : Blo 1561478 1562427 := bstep (se 1 (by rfl) ⟨1171820, by rfl⟩ : syracuseStep 1562427 = 2343641) B2343641
theorem B1562503 : Blo 1561478 1562503 := bstep (se 1 (by rfl) ⟨1171877, by rfl⟩ : syracuseStep 1562503 = 2343755) B2343755
theorem B1562511 : Blo 1561478 1562511 := bstep (se 1 (by rfl) ⟨1171883, by rfl⟩ : syracuseStep 1562511 = 2343767) B2343767
theorem B8894393 : Blo 1561478 8894393 := bstep (se 2 (by rfl) ⟨3335397, by rfl⟩ : syracuseStep 8894393 = 6670795) B6670795
theorem B1562555 : Blo 1561478 1562555 := bstep (se 1 (by rfl) ⟨1171916, by rfl⟩ : syracuseStep 1562555 = 2343833) B2343833
theorem B1562631 : Blo 1561478 1562631 := bstep (se 1 (by rfl) ⟨1171973, by rfl⟩ : syracuseStep 1562631 = 2343947) B2343947
theorem B3954703 : Blo 1561478 3954703 := bstep (se 1 (by rfl) ⟨2966027, by rfl⟩ : syracuseStep 3954703 = 5932055) B5932055
theorem B1562639 : Blo 1561478 1562639 := bstep (se 1 (by rfl) ⟨1171979, by rfl⟩ : syracuseStep 1562639 = 2343959) B2343959
theorem B1562683 : Blo 1561478 1562683 := bstep (se 1 (by rfl) ⟨1172012, by rfl⟩ : syracuseStep 1562683 = 2344025) B2344025
theorem B10016855 : Blo 1561478 10016855 := bstep (se 1 (by rfl) ⟨7512641, by rfl⟩ : syracuseStep 10016855 = 15025283) B15025283
theorem B16898165 : Blo 1561478 16898165 := bstep (se 5 (by rfl) ⟨792101, by rfl⟩ : syracuseStep 16898165 = 1584203) B1584203
theorem B162437237 : Blo 1561478 162437237 := bstep (se 5 (by rfl) ⟨7614245, by rfl⟩ : syracuseStep 162437237 = 15228491) B15228491
theorem B2635895 : Blo 1561478 2635895 := bstep (se 1 (by rfl) ⟨1976921, by rfl⟩ : syracuseStep 2635895 = 3953843) B3953843
theorem B1562759 : Blo 1561478 1562759 := bstep (se 1 (by rfl) ⟨1172069, by rfl⟩ : syracuseStep 1562759 = 2344139) B2344139
theorem B1562767 : Blo 1561478 1562767 := bstep (se 1 (by rfl) ⟨1172075, by rfl⟩ : syracuseStep 1562767 = 2344151) B2344151
theorem B1562811 : Blo 1561478 1562811 := bstep (se 1 (by rfl) ⟨1172108, by rfl⟩ : syracuseStep 1562811 = 2344217) B2344217
theorem B5273801 : Blo 1561478 5273801 := bstep (se 2 (by rfl) ⟨1977675, by rfl⟩ : syracuseStep 5273801 = 3955351) B3955351
theorem B1562887 : Blo 1561478 1562887 := bstep (se 1 (by rfl) ⟨1172165, by rfl⟩ : syracuseStep 1562887 = 2344331) B2344331
theorem B1562895 : Blo 1561478 1562895 := bstep (se 1 (by rfl) ⟨1172171, by rfl⟩ : syracuseStep 1562895 = 2344343) B2344343
theorem B3954977 : Blo 1561478 3954977 := bstep (se 2 (by rfl) ⟨1483116, by rfl⟩ : syracuseStep 3954977 = 2966233) B2966233
theorem B1562939 : Blo 1561478 1562939 := bstep (se 1 (by rfl) ⟨1172204, by rfl⟩ : syracuseStep 1562939 = 2344409) B2344409
theorem B1563015 : Blo 1561478 1563015 := bstep (se 1 (by rfl) ⟨1172261, by rfl⟩ : syracuseStep 1563015 = 2344523) B2344523
theorem B1563023 : Blo 1561478 1563023 := bstep (se 1 (by rfl) ⟨1172267, by rfl⟩ : syracuseStep 1563023 = 2344535) B2344535
theorem B1563067 : Blo 1561478 1563067 := bstep (se 1 (by rfl) ⟨1172300, by rfl⟩ : syracuseStep 1563067 = 2344601) B2344601
theorem B4225537 : Blo 1561478 4225537 := bstep (se 2 (by rfl) ⟨1584576, by rfl⟩ : syracuseStep 4225537 = 3169153) B3169153
theorem B1563143 : Blo 1561478 1563143 := bstep (se 1 (by rfl) ⟨1172357, by rfl⟩ : syracuseStep 1563143 = 2344715) B2344715
theorem B1563151 : Blo 1561478 1563151 := bstep (se 1 (by rfl) ⟨1172363, by rfl⟩ : syracuseStep 1563151 = 2344727) B2344727
theorem B2636347 : Blo 1561478 2636347 := bstep (se 1 (by rfl) ⟨1977260, by rfl⟩ : syracuseStep 2636347 = 3954521) B3954521
theorem B1563195 : Blo 1561478 1563195 := bstep (se 1 (by rfl) ⟨1172396, by rfl⟩ : syracuseStep 1563195 = 2344793) B2344793
theorem B3005047 : Blo 1561478 3005047 := bstep (se 1 (by rfl) ⟨2253785, by rfl⟩ : syracuseStep 3005047 = 4507571) B4507571
theorem B1563271 : Blo 1561478 1563271 := bstep (se 1 (by rfl) ⟨1172453, by rfl⟩ : syracuseStep 1563271 = 2344907) B2344907
theorem B1563279 : Blo 1561478 1563279 := bstep (se 1 (by rfl) ⟨1172459, by rfl⟩ : syracuseStep 1563279 = 2344919) B2344919
theorem B1563323 : Blo 1561478 1563323 := bstep (se 1 (by rfl) ⟨1172492, by rfl⟩ : syracuseStep 1563323 = 2344985) B2344985
theorem B2636489 : Blo 1561478 2636489 := bstep (se 2 (by rfl) ⟨988683, by rfl⟩ : syracuseStep 2636489 = 1977367) B1977367
theorem B1563399 : Blo 1561478 1563399 := bstep (se 1 (by rfl) ⟨1172549, by rfl⟩ : syracuseStep 1563399 = 2345099) B2345099
theorem B4446991 : Blo 1561478 4446991 := bstep (se 1 (by rfl) ⟨3335243, by rfl⟩ : syracuseStep 4446991 = 6670487) B6670487
theorem B1563407 : Blo 1561478 1563407 := bstep (se 1 (by rfl) ⟨1172555, by rfl⟩ : syracuseStep 1563407 = 2345111) B2345111
theorem B1563451 : Blo 1561478 1563451 := bstep (se 1 (by rfl) ⟨1172588, by rfl⟩ : syracuseStep 1563451 = 2345177) B2345177
theorem B4447037 : Blo 1561478 4447037 := bstep (se 3 (by rfl) ⟨833819, by rfl⟩ : syracuseStep 4447037 = 1667639) B1667639
theorem B5274503 : Blo 1561478 5274503 := bstep (se 1 (by rfl) ⟨3955877, by rfl⟩ : syracuseStep 5274503 = 7911755) B7911755
theorem B11869091 : Blo 1561478 11869091 := bstep (se 1 (by rfl) ⟨8901818, by rfl⟩ : syracuseStep 11869091 = 17803637) B17803637
theorem B2964539 : Blo 1561478 2964539 := bstep (se 1 (by rfl) ⟨2223404, by rfl⟩ : syracuseStep 2964539 = 4446809) B4446809
theorem B3513491 : Blo 1561478 3513491 := bstep (se 1 (by rfl) ⟨2635118, by rfl⟩ : syracuseStep 3513491 = 5270237) B5270237
theorem B4447379 : Blo 1561478 4447379 := bstep (se 1 (by rfl) ⟨3335534, by rfl⟩ : syracuseStep 4447379 = 6671069) B6671069
theorem B3513545 : Blo 1561478 3513545 := bstep (se 2 (by rfl) ⟨1317579, by rfl⟩ : syracuseStep 3513545 = 2635159) B2635159
theorem B5274881 : Blo 1561478 5274881 := bstep (se 2 (by rfl) ⟨1978080, by rfl⟩ : syracuseStep 5274881 = 3956161) B3956161
theorem B3955979 : Blo 1561478 3955979 := bstep (se 1 (by rfl) ⟨2966984, by rfl⟩ : syracuseStep 3955979 = 5933969) B5933969
theorem B8019251 : Blo 1561478 8019251 := bstep (se 1 (by rfl) ⟨6014438, by rfl⟩ : syracuseStep 8019251 = 12028877) B12028877
theorem B2342279 : Blo 1561478 2342279 := bstep (se 1 (by rfl) ⟨1756709, by rfl⟩ : syracuseStep 2342279 = 3513419) B3513419
theorem B2637191 : Blo 1561478 2637191 := bstep (se 1 (by rfl) ⟨1977893, by rfl⟩ : syracuseStep 2637191 = 3955787) B3955787
theorem B7511449 : Blo 1561478 7511449 := bstep (se 2 (by rfl) ⟨2816793, by rfl⟩ : syracuseStep 7511449 = 5633587) B5633587
theorem B2342315 : Blo 1561478 2342315 := bstep (se 1 (by rfl) ⟨1756736, by rfl⟩ : syracuseStep 2342315 = 3513473) B3513473
theorem B7912889 : Blo 1561478 7912889 := bstep (se 2 (by rfl) ⟨2967333, by rfl⟩ : syracuseStep 7912889 = 5934667) B5934667
theorem B2342345 : Blo 1561478 2342345 := bstep (se 2 (by rfl) ⟨878379, by rfl⟩ : syracuseStep 2342345 = 1756759) B1756759
theorem B10010141 : Blo 1561478 10010141 := bstep (se 3 (by rfl) ⟨1876901, by rfl⟩ : syracuseStep 10010141 = 3753803) B3753803
theorem B2965025 : Blo 1561478 2965025 := bstep (se 2 (by rfl) ⟨1111884, by rfl⟩ : syracuseStep 2965025 = 2223769) B2223769
theorem B2342459 : Blo 1561478 2342459 := bstep (se 1 (by rfl) ⟨1756844, by rfl⟩ : syracuseStep 2342459 = 3513689) B3513689
theorem B27065933 : Blo 1561478 27065933 := bstep (se 3 (by rfl) ⟨5074862, by rfl⟩ : syracuseStep 27065933 = 10149725) B10149725
theorem B13352525 : Blo 1561478 13352525 := bstep (se 3 (by rfl) ⟨2503598, by rfl⟩ : syracuseStep 13352525 = 5007197) B5007197
theorem B2342519 : Blo 1561478 2342519 := bstep (se 1 (by rfl) ⟨1756889, by rfl⟩ : syracuseStep 2342519 = 3513779) B3513779
theorem B2571895 : Blo 1561478 2571895 := bstep (se 1 (by rfl) ⟨1928921, by rfl⟩ : syracuseStep 2571895 = 3857843) B3857843
theorem B2342543 : Blo 1561478 2342543 := bstep (se 1 (by rfl) ⟨1756907, by rfl⟩ : syracuseStep 2342543 = 3513815) B3513815
theorem B2342585 : Blo 1561478 2342585 := bstep (se 2 (by rfl) ⟨878469, by rfl⟩ : syracuseStep 2342585 = 1756939) B1756939
theorem B2965177 : Blo 1561478 2965177 := bstep (se 2 (by rfl) ⟨1111941, by rfl⟩ : syracuseStep 2965177 = 2223883) B2223883
theorem B6332141 : Blo 1561478 6332141 := bstep (se 3 (by rfl) ⟨1187276, by rfl⟩ : syracuseStep 6332141 = 2374553) B2374553
theorem B2342663 : Blo 1561478 2342663 := bstep (se 1 (by rfl) ⟨1756997, by rfl⟩ : syracuseStep 2342663 = 3513995) B3513995
theorem B13344527 : Blo 1561478 13344527 := bstep (se 1 (by rfl) ⟨10008395, by rfl⟩ : syracuseStep 13344527 = 20016791) B20016791
theorem B2342699 : Blo 1561478 2342699 := bstep (se 1 (by rfl) ⟨1757024, by rfl⟩ : syracuseStep 2342699 = 3514049) B3514049
theorem B2031403 : Blo 1561478 2031403 := bstep (se 1 (by rfl) ⟨1523552, by rfl⟩ : syracuseStep 2031403 = 3047105) B3047105
theorem B14262065 : Blo 1561478 14262065 := bstep (se 2 (by rfl) ⟨5348274, by rfl⟩ : syracuseStep 14262065 = 10696549) B10696549
theorem B2342729 : Blo 1561478 2342729 := bstep (se 2 (by rfl) ⟨878523, by rfl⟩ : syracuseStep 2342729 = 1757047) B1757047
theorem B7905113 : Blo 1561478 7905113 := bstep (se 2 (by rfl) ⟨2964417, by rfl⟩ : syracuseStep 7905113 = 5928835) B5928835
theorem B3514247 : Blo 1561478 3514247 := bstep (se 1 (by rfl) ⟨2635685, by rfl⟩ : syracuseStep 3514247 = 5271371) B5271371
theorem B3956627 : Blo 1561478 3956627 := bstep (se 1 (by rfl) ⟨2967470, by rfl⟩ : syracuseStep 3956627 = 5934941) B5934941
theorem B2342843 : Blo 1561478 2342843 := bstep (se 1 (by rfl) ⟨1757132, by rfl⟩ : syracuseStep 2342843 = 3514265) B3514265
theorem B11255755 : Blo 1561478 11255755 := bstep (se 1 (by rfl) ⟨8441816, by rfl⟩ : syracuseStep 11255755 = 16883633) B16883633
theorem B2342903 : Blo 1561478 2342903 := bstep (se 1 (by rfl) ⟨1757177, by rfl⟩ : syracuseStep 2342903 = 3514355) B3514355
theorem B2965511 : Blo 1561478 2965511 := bstep (se 1 (by rfl) ⟨2224133, by rfl⟩ : syracuseStep 2965511 = 4448267) B4448267
theorem B2342921 : Blo 1561478 2342921 := bstep (se 2 (by rfl) ⟨878595, by rfl⟩ : syracuseStep 2342921 = 1757191) B1757191
theorem B45047825 : Blo 1561478 45047825 := bstep (se 2 (by rfl) ⟨16892934, by rfl⟩ : syracuseStep 45047825 = 33785869) B33785869
theorem B2342951 : Blo 1561478 2342951 := bstep (se 1 (by rfl) ⟨1757213, by rfl⟩ : syracuseStep 2342951 = 3514427) B3514427
theorem B2343035 : Blo 1561478 2343035 := bstep (se 1 (by rfl) ⟨1757276, by rfl⟩ : syracuseStep 2343035 = 3514553) B3514553
theorem B2637947 : Blo 1561478 2637947 := bstep (se 1 (by rfl) ⟨1978460, by rfl⟩ : syracuseStep 2637947 = 3956921) B3956921
theorem B7905437 : Blo 1561478 7905437 := bstep (se 3 (by rfl) ⟨1482269, by rfl⟩ : syracuseStep 7905437 = 2964539) B2964539
theorem B28524707 : Blo 1561478 28524707 := bstep (se 1 (by rfl) ⟨21393530, by rfl⟩ : syracuseStep 28524707 = 42787061) B42787061
theorem B2343161 : Blo 1561478 2343161 := bstep (se 2 (by rfl) ⟨878685, by rfl⟩ : syracuseStep 2343161 = 1757371) B1757371
theorem B2343263 : Blo 1561478 2343263 := bstep (se 1 (by rfl) ⟨1757447, by rfl⟩ : syracuseStep 2343263 = 3514895) B3514895
theorem B2343275 : Blo 1561478 2343275 := bstep (se 1 (by rfl) ⟨1757456, by rfl⟩ : syracuseStep 2343275 = 3514913) B3514913
theorem B5276123 : Blo 1561478 5276123 := bstep (se 1 (by rfl) ⟨3957092, by rfl⟩ : syracuseStep 5276123 = 7914185) B7914185
theorem B2638345 : Blo 1561478 2638345 := bstep (se 2 (by rfl) ⟨989379, by rfl⟩ : syracuseStep 2638345 = 1978759) B1978759
theorem B6423079 : Blo 1561478 6423079 := bstep (se 1 (by rfl) ⟨4817309, by rfl⟩ : syracuseStep 6423079 = 9634619) B9634619
theorem B2343503 : Blo 1561478 2343503 := bstep (se 1 (by rfl) ⟨1757627, by rfl⟩ : syracuseStep 2343503 = 3515255) B3515255
theorem B3515003 : Blo 1561478 3515003 := bstep (se 1 (by rfl) ⟨2636252, by rfl⟩ : syracuseStep 3515003 = 5272505) B5272505
theorem B2343623 : Blo 1561478 2343623 := bstep (se 1 (by rfl) ⟨1757717, by rfl⟩ : syracuseStep 2343623 = 3515435) B3515435
theorem B3515129 : Blo 1561478 3515129 := bstep (se 2 (by rfl) ⟨1318173, by rfl⟩ : syracuseStep 3515129 = 2636347) B2636347
theorem B8897309 : Blo 1561478 8897309 := bstep (se 3 (by rfl) ⟨1668245, by rfl⟩ : syracuseStep 8897309 = 3336491) B3336491
theorem B601203491 : Blo 1561478 601203491 := bstep (se 1 (by rfl) ⟨450902618, by rfl⟩ : syracuseStep 601203491 = 901805237) B901805237
theorem B2343785 : Blo 1561478 2343785 := bstep (se 2 (by rfl) ⟨878919, by rfl⟩ : syracuseStep 2343785 = 1757839) B1757839
theorem B2966377 : Blo 1561478 2966377 := bstep (se 2 (by rfl) ⟨1112391, by rfl⟩ : syracuseStep 2966377 = 2224783) B2224783
theorem B7914347 : Blo 1561478 7914347 := bstep (se 1 (by rfl) ⟨5935760, by rfl⟩ : syracuseStep 7914347 = 11871521) B11871521
theorem B40035221 : Blo 1561478 40035221 := bstep (se 6 (by rfl) ⟨938325, by rfl⟩ : syracuseStep 40035221 = 1876651) B1876651
theorem B2343863 : Blo 1561478 2343863 := bstep (se 1 (by rfl) ⟨1757897, by rfl⟩ : syracuseStep 2343863 = 3515795) B3515795
theorem B2343899 : Blo 1561478 2343899 := bstep (se 1 (by rfl) ⟨1757924, by rfl⟩ : syracuseStep 2343899 = 3515849) B3515849
theorem B3515399 : Blo 1561478 3515399 := bstep (se 1 (by rfl) ⟨2636549, by rfl⟩ : syracuseStep 3515399 = 5273099) B5273099
theorem B2966537 : Blo 1561478 2966537 := bstep (se 2 (by rfl) ⟨1112451, by rfl⟩ : syracuseStep 2966537 = 2224903) B2224903
theorem B37995571 : Blo 1561478 37995571 := bstep (se 1 (by rfl) ⟨28496678, by rfl⟩ : syracuseStep 37995571 = 56993357) B56993357
theorem B3515471 : Blo 1561478 3515471 := bstep (se 1 (by rfl) ⟨2636603, by rfl⟩ : syracuseStep 3515471 = 5273207) B5273207
theorem B6677903 : Blo 1561478 6677903 := bstep (se 1 (by rfl) ⟨5008427, by rfl⟩ : syracuseStep 6677903 = 10016855) B10016855
theorem B11265443 : Blo 1561478 11265443 := bstep (se 1 (by rfl) ⟨8449082, by rfl⟩ : syracuseStep 11265443 = 16898165) B16898165
theorem B108291491 : Blo 1561478 108291491 := bstep (se 1 (by rfl) ⟨81218618, by rfl⟩ : syracuseStep 108291491 = 162437237) B162437237
theorem B7906733 : Blo 1561478 7906733 := bstep (se 3 (by rfl) ⟨1482512, by rfl⟩ : syracuseStep 7906733 = 2965025) B2965025
theorem B2344367 : Blo 1561478 2344367 := bstep (se 1 (by rfl) ⟨1758275, by rfl⟩ : syracuseStep 2344367 = 3516551) B3516551
theorem B3515867 : Blo 1561478 3515867 := bstep (se 1 (by rfl) ⟨2636900, by rfl⟩ : syracuseStep 3515867 = 5273801) B5273801
theorem B7914995 : Blo 1561478 7914995 := bstep (se 1 (by rfl) ⟨5936246, by rfl⟩ : syracuseStep 7914995 = 11872493) B11872493
theorem B2344457 : Blo 1561478 2344457 := bstep (se 2 (by rfl) ⟨879171, by rfl⟩ : syracuseStep 2344457 = 1758343) B1758343
theorem B2344487 : Blo 1561478 2344487 := bstep (se 1 (by rfl) ⟨1758365, by rfl⟩ : syracuseStep 2344487 = 3516731) B3516731
theorem B2344571 : Blo 1561478 2344571 := bstep (se 1 (by rfl) ⟨1758428, by rfl⟩ : syracuseStep 2344571 = 3516857) B3516857
theorem B2344697 : Blo 1561478 2344697 := bstep (se 2 (by rfl) ⟨879261, by rfl⟩ : syracuseStep 2344697 = 1758523) B1758523
theorem B16893755 : Blo 1561478 16893755 := bstep (se 1 (by rfl) ⟨12670316, by rfl⟩ : syracuseStep 16893755 = 25340633) B25340633
theorem B7128899 : Blo 1561478 7128899 := bstep (se 1 (by rfl) ⟨5346674, by rfl⟩ : syracuseStep 7128899 = 10693349) B10693349
theorem B2344799 : Blo 1561478 2344799 := bstep (se 1 (by rfl) ⟨1758599, by rfl⟩ : syracuseStep 2344799 = 3517199) B3517199
theorem B2344811 : Blo 1561478 2344811 := bstep (se 1 (by rfl) ⟨1758608, by rfl⟩ : syracuseStep 2344811 = 3517217) B3517217
theorem B3516335 : Blo 1561478 3516335 := bstep (se 1 (by rfl) ⟨2637251, by rfl⟩ : syracuseStep 3516335 = 5274503) B5274503
theorem B16885709 : Blo 1561478 16885709 := bstep (se 3 (by rfl) ⟨3166070, by rfl⟩ : syracuseStep 16885709 = 6332141) B6332141
theorem B10012679 : Blo 1561478 10012679 := bstep (se 1 (by rfl) ⟨7509509, by rfl⟩ : syracuseStep 10012679 = 15019019) B15019019
theorem B2345039 : Blo 1561478 2345039 := bstep (se 1 (by rfl) ⟨1758779, by rfl⟩ : syracuseStep 2345039 = 3517559) B3517559
theorem B5933209 : Blo 1561478 5933209 := bstep (se 2 (by rfl) ⟨2224953, by rfl⟩ : syracuseStep 5933209 = 4449907) B4449907
theorem B3516587 : Blo 1561478 3516587 := bstep (se 1 (by rfl) ⟨2637440, by rfl⟩ : syracuseStep 3516587 = 5274881) B5274881
theorem B2345159 : Blo 1561478 2345159 := bstep (se 1 (by rfl) ⟨1758869, by rfl⟩ : syracuseStep 2345159 = 3517739) B3517739
theorem B24045929 : Blo 1561478 24045929 := bstep (se 2 (by rfl) ⟨9017223, by rfl⟩ : syracuseStep 24045929 = 18034447) B18034447
theorem B2967995 : Blo 1561478 2967995 := bstep (se 1 (by rfl) ⟨2225996, by rfl⟩ : syracuseStep 2967995 = 4451993) B4451993
theorem B5933513 : Blo 1561478 5933513 := bstep (se 2 (by rfl) ⟨2225067, by rfl⟩ : syracuseStep 5933513 = 4450135) B4450135
theorem B6670829 : Blo 1561478 6670829 := bstep (se 3 (by rfl) ⟨1250780, by rfl⟩ : syracuseStep 6670829 = 2501561) B2501561
theorem B10013165 : Blo 1561478 10013165 := bstep (se 3 (by rfl) ⟨1877468, by rfl⟩ : syracuseStep 10013165 = 3754937) B3754937
theorem B5270075 : Blo 1561478 5270075 := bstep (se 1 (by rfl) ⟨3952556, by rfl⟩ : syracuseStep 5270075 = 7905113) B7905113
theorem B3517127 : Blo 1561478 3517127 := bstep (se 1 (by rfl) ⟨2637845, by rfl⟩ : syracuseStep 3517127 = 5275691) B5275691
theorem B5270345 : Blo 1561478 5270345 := bstep (se 2 (by rfl) ⟨1976379, by rfl⟩ : syracuseStep 5270345 = 3952759) B3952759
theorem B3337055 : Blo 1561478 3337055 := bstep (se 1 (by rfl) ⟨2502791, by rfl⟩ : syracuseStep 3337055 = 5005583) B5005583
theorem B5008223 : Blo 1561478 5008223 := bstep (se 1 (by rfl) ⟨3756167, by rfl⟩ : syracuseStep 5008223 = 7512335) B7512335
theorem B5933999 : Blo 1561478 5933999 := bstep (se 1 (by rfl) ⟨4450499, by rfl⟩ : syracuseStep 5933999 = 8900999) B8900999
theorem B7908353 : Blo 1561478 7908353 := bstep (se 2 (by rfl) ⟨2965632, by rfl⟩ : syracuseStep 7908353 = 5931265) B5931265
theorem B6016007 : Blo 1561478 6016007 := bstep (se 1 (by rfl) ⟨4512005, by rfl⟩ : syracuseStep 6016007 = 9024011) B9024011
theorem B2501689 : Blo 1561478 2501689 := bstep (se 2 (by rfl) ⟨938133, by rfl⟩ : syracuseStep 2501689 = 1876267) B1876267
theorem B13528259 : Blo 1561478 13528259 := bstep (se 1 (by rfl) ⟨10146194, by rfl⟩ : syracuseStep 13528259 = 20292389) B20292389
theorem B10005707 : Blo 1561478 10005707 := bstep (se 1 (by rfl) ⟨7504280, by rfl⟩ : syracuseStep 10005707 = 15008561) B15008561
theorem B16026917 : Blo 1561478 16026917 := bstep (se 4 (by rfl) ⟨1502523, by rfl⟩ : syracuseStep 16026917 = 3005047) B3005047
theorem B13716773 : Blo 1561478 13716773 := bstep (se 4 (by rfl) ⟨1285947, by rfl⟩ : syracuseStep 13716773 = 2571895) B2571895
theorem B38006081 : Blo 1561478 38006081 := bstep (se 2 (by rfl) ⟨14252280, by rfl⟩ : syracuseStep 38006081 = 28504561) B28504561
theorem B1756795 : Blo 1561478 1756795 := bstep (se 1 (by rfl) ⟨1317596, by rfl⟩ : syracuseStep 1756795 = 2635193) B2635193
theorem B32059097 : Blo 1561478 32059097 := bstep (se 2 (by rfl) ⟨12022161, by rfl⟩ : syracuseStep 32059097 = 24044323) B24044323
theorem B7909163 : Blo 1561478 7909163 := bstep (se 1 (by rfl) ⟨5931872, by rfl⟩ : syracuseStep 7909163 = 11863745) B11863745
theorem B40578947 : Blo 1561478 40578947 := bstep (se 1 (by rfl) ⟨30434210, by rfl⟩ : syracuseStep 40578947 = 60868421) B60868421
theorem B5271479 : Blo 1561478 5271479 := bstep (se 1 (by rfl) ⟨3953609, by rfl⟩ : syracuseStep 5271479 = 7907219) B7907219
theorem B1757263 : Blo 1561478 1757263 := bstep (se 1 (by rfl) ⟨1317947, by rfl⟩ : syracuseStep 1757263 = 2635895) B2635895
theorem B2503099 : Blo 1561478 2503099 := bstep (se 1 (by rfl) ⟨1877324, by rfl⟩ : syracuseStep 2503099 = 3754649) B3754649
theorem B1757659 : Blo 1561478 1757659 := bstep (se 1 (by rfl) ⟨1318244, by rfl⟩ : syracuseStep 1757659 = 2636489) B2636489
theorem B2814473 : Blo 1561478 2814473 := bstep (se 2 (by rfl) ⟨1055427, by rfl⟩ : syracuseStep 2814473 = 2110855) B2110855
theorem B5272073 : Blo 1561478 5272073 := bstep (se 2 (by rfl) ⟨1977027, by rfl⟩ : syracuseStep 5272073 = 3954055) B3954055
theorem B5935625 : Blo 1561478 5935625 := bstep (se 2 (by rfl) ⟨2225859, by rfl⟩ : syracuseStep 5935625 = 4451719) B4451719
theorem B10015265 : Blo 1561478 10015265 := bstep (se 2 (by rfl) ⟨3755724, by rfl⟩ : syracuseStep 10015265 = 7511449) B7511449
theorem B17797805 : Blo 1561478 17797805 := bstep (se 3 (by rfl) ⟨3337088, by rfl⟩ : syracuseStep 17797805 = 6674177) B6674177
theorem B4223677 : Blo 1561478 4223677 := bstep (se 3 (by rfl) ⟨791939, by rfl⟩ : syracuseStep 4223677 = 1583879) B1583879
theorem B9630467 : Blo 1561478 9630467 := bstep (se 1 (by rfl) ⟨7222850, by rfl⟩ : syracuseStep 9630467 = 14445701) B14445701
theorem B20034377 : Blo 1561478 20034377 := bstep (se 2 (by rfl) ⟨7512891, by rfl⟩ : syracuseStep 20034377 = 15025783) B15025783
theorem B5346167 : Blo 1561478 5346167 := bstep (se 1 (by rfl) ⟨4009625, by rfl⟩ : syracuseStep 5346167 = 8019251) B8019251
theorem B3953569 : Blo 1561478 3953569 := bstep (se 2 (by rfl) ⟨1482588, by rfl⟩ : syracuseStep 3953569 = 2965177) B2965177
theorem B1561519 : Blo 1561478 1561519 := bstep (se 1 (by rfl) ⟨1171139, by rfl⟩ : syracuseStep 1561519 = 2342279) B2342279
theorem B1758127 : Blo 1561478 1758127 := bstep (se 1 (by rfl) ⟨1318595, by rfl⟩ : syracuseStep 1758127 = 2637191) B2637191
theorem B4223927 : Blo 1561478 4223927 := bstep (se 1 (by rfl) ⟨3167945, by rfl⟩ : syracuseStep 4223927 = 6335891) B6335891
theorem B1561543 : Blo 1561478 1561543 := bstep (se 1 (by rfl) ⟨1171157, by rfl⟩ : syracuseStep 1561543 = 2342315) B2342315
theorem B1561563 : Blo 1561478 1561563 := bstep (se 1 (by rfl) ⟨1171172, by rfl⟩ : syracuseStep 1561563 = 2342345) B2342345
theorem B6673427 : Blo 1561478 6673427 := bstep (se 1 (by rfl) ⟨5005070, by rfl⟩ : syracuseStep 6673427 = 10010141) B10010141
theorem B1561639 : Blo 1561478 1561639 := bstep (se 1 (by rfl) ⟨1171229, by rfl⟩ : syracuseStep 1561639 = 2342459) B2342459
theorem B18043955 : Blo 1561478 18043955 := bstep (se 1 (by rfl) ⟨13532966, by rfl⟩ : syracuseStep 18043955 = 27065933) B27065933
theorem B8901683 : Blo 1561478 8901683 := bstep (se 1 (by rfl) ⟨6676262, by rfl⟩ : syracuseStep 8901683 = 13352525) B13352525
theorem B2708537 : Blo 1561478 2708537 := bstep (se 2 (by rfl) ⟨1015701, by rfl⟩ : syracuseStep 2708537 = 2031403) B2031403
theorem B1561679 : Blo 1561478 1561679 := bstep (se 1 (by rfl) ⟨1171259, by rfl⟩ : syracuseStep 1561679 = 2342519) B2342519
theorem B1561695 : Blo 1561478 1561695 := bstep (se 1 (by rfl) ⟨1171271, by rfl⟩ : syracuseStep 1561695 = 2342543) B2342543
theorem B1561723 : Blo 1561478 1561723 := bstep (se 1 (by rfl) ⟨1171292, by rfl⟩ : syracuseStep 1561723 = 2342585) B2342585
theorem B1561775 : Blo 1561478 1561775 := bstep (se 1 (by rfl) ⟨1171331, by rfl⟩ : syracuseStep 1561775 = 2342663) B2342663
theorem B1561799 : Blo 1561478 1561799 := bstep (se 1 (by rfl) ⟨1171349, by rfl⟩ : syracuseStep 1561799 = 2342699) B2342699
theorem B9508043 : Blo 1561478 9508043 := bstep (se 1 (by rfl) ⟨7131032, by rfl⟩ : syracuseStep 9508043 = 14262065) B14262065
theorem B17806553 : Blo 1561478 17806553 := bstep (se 2 (by rfl) ⟨6677457, by rfl⟩ : syracuseStep 17806553 = 13354915) B13354915
theorem B1561819 : Blo 1561478 1561819 := bstep (se 1 (by rfl) ⟨1171364, by rfl⟩ : syracuseStep 1561819 = 2342729) B2342729
theorem B11269367 : Blo 1561478 11269367 := bstep (se 1 (by rfl) ⟨8452025, by rfl⟩ : syracuseStep 11269367 = 16904051) B16904051
theorem B1561895 : Blo 1561478 1561895 := bstep (se 1 (by rfl) ⟨1171421, by rfl⟩ : syracuseStep 1561895 = 2342843) B2342843
theorem B2504009 : Blo 1561478 2504009 := bstep (se 2 (by rfl) ⟨939003, by rfl⟩ : syracuseStep 2504009 = 1878007) B1878007
theorem B1561935 : Blo 1561478 1561935 := bstep (se 1 (by rfl) ⟨1171451, by rfl⟩ : syracuseStep 1561935 = 2342903) B2342903
theorem B1561951 : Blo 1561478 1561951 := bstep (se 1 (by rfl) ⟨1171463, by rfl⟩ : syracuseStep 1561951 = 2342927) B2342927
theorem B1758559 : Blo 1561478 1758559 := bstep (se 1 (by rfl) ⟨1318919, by rfl⟩ : syracuseStep 1758559 = 2637839) B2637839
theorem B5272937 : Blo 1561478 5272937 := bstep (se 2 (by rfl) ⟨1977351, by rfl⟩ : syracuseStep 5272937 = 3954703) B3954703
theorem B13342067 : Blo 1561478 13342067 := bstep (se 1 (by rfl) ⟨10006550, by rfl⟩ : syracuseStep 13342067 = 20013101) B20013101
theorem B1561979 : Blo 1561478 1561979 := bstep (se 1 (by rfl) ⟨1171484, by rfl⟩ : syracuseStep 1561979 = 2342969) B2342969
theorem B1562031 : Blo 1561478 1562031 := bstep (se 1 (by rfl) ⟨1171523, by rfl⟩ : syracuseStep 1562031 = 2343047) B2343047
theorem B1562055 : Blo 1561478 1562055 := bstep (se 1 (by rfl) ⟨1171541, by rfl⟩ : syracuseStep 1562055 = 2343083) B2343083
theorem B1562075 : Blo 1561478 1562075 := bstep (se 1 (by rfl) ⟨1171556, by rfl⟩ : syracuseStep 1562075 = 2343113) B2343113
theorem B1562151 : Blo 1561478 1562151 := bstep (se 1 (by rfl) ⟨1171613, by rfl⟩ : syracuseStep 1562151 = 2343227) B2343227
theorem B1668647 : Blo 1561478 1668647 := bstep (se 1 (by rfl) ⟨1251485, by rfl⟩ : syracuseStep 1668647 = 2502971) B2502971
theorem B8902183 : Blo 1561478 8902183 := bstep (se 1 (by rfl) ⟨6676637, by rfl⟩ : syracuseStep 8902183 = 13353275) B13353275
theorem B2635321 : Blo 1561478 2635321 := bstep (se 2 (by rfl) ⟨988245, by rfl⟩ : syracuseStep 2635321 = 1976491) B1976491
theorem B1562191 : Blo 1561478 1562191 := bstep (se 1 (by rfl) ⟨1171643, by rfl⟩ : syracuseStep 1562191 = 2343287) B2343287
theorem B1562207 : Blo 1561478 1562207 := bstep (se 1 (by rfl) ⟨1171655, by rfl⟩ : syracuseStep 1562207 = 2343311) B2343311
theorem B1562235 : Blo 1561478 1562235 := bstep (se 1 (by rfl) ⟨1171676, by rfl⟩ : syracuseStep 1562235 = 2343353) B2343353
theorem B1562287 : Blo 1561478 1562287 := bstep (se 1 (by rfl) ⟨1171715, by rfl⟩ : syracuseStep 1562287 = 2343431) B2343431
theorem B2635463 : Blo 1561478 2635463 := bstep (se 1 (by rfl) ⟨1976597, by rfl⟩ : syracuseStep 2635463 = 3953195) B3953195
theorem B1562311 : Blo 1561478 1562311 := bstep (se 1 (by rfl) ⟨1171733, by rfl⟩ : syracuseStep 1562311 = 2343467) B2343467
theorem B2004679 : Blo 1561478 2004679 := bstep (se 1 (by rfl) ⟨1503509, by rfl⟩ : syracuseStep 2004679 = 3007019) B3007019
theorem B1562331 : Blo 1561478 1562331 := bstep (se 1 (by rfl) ⟨1171748, by rfl⟩ : syracuseStep 1562331 = 2343497) B2343497
theorem B1562407 : Blo 1561478 1562407 := bstep (se 1 (by rfl) ⟨1171805, by rfl⟩ : syracuseStep 1562407 = 2343611) B2343611
theorem B243619649 : Blo 1561478 243619649 := bstep (se 2 (by rfl) ⟨91357368, by rfl⟩ : syracuseStep 243619649 = 182714737) B182714737
theorem B1562447 : Blo 1561478 1562447 := bstep (se 1 (by rfl) ⟨1171835, by rfl⟩ : syracuseStep 1562447 = 2343671) B2343671
theorem B1562463 : Blo 1561478 1562463 := bstep (se 1 (by rfl) ⟨1171847, by rfl⟩ : syracuseStep 1562463 = 2343695) B2343695
theorem B2635625 : Blo 1561478 2635625 := bstep (se 2 (by rfl) ⟨988359, by rfl⟩ : syracuseStep 2635625 = 1976719) B1976719
theorem B1562491 : Blo 1561478 1562491 := bstep (se 1 (by rfl) ⟨1171868, by rfl⟩ : syracuseStep 1562491 = 2343737) B2343737
theorem B1562543 : Blo 1561478 1562543 := bstep (se 1 (by rfl) ⟨1171907, by rfl⟩ : syracuseStep 1562543 = 2343815) B2343815
theorem B5273531 : Blo 1561478 5273531 := bstep (se 1 (by rfl) ⟨3955148, by rfl⟩ : syracuseStep 5273531 = 7910297) B7910297
theorem B1562567 : Blo 1561478 1562567 := bstep (se 1 (by rfl) ⟨1171925, by rfl⟩ : syracuseStep 1562567 = 2343851) B2343851
theorem B26712017 : Blo 1561478 26712017 := bstep (se 2 (by rfl) ⟨10017006, by rfl⟩ : syracuseStep 26712017 = 20034013) B20034013
theorem B1562587 : Blo 1561478 1562587 := bstep (se 1 (by rfl) ⟨1171940, by rfl⟩ : syracuseStep 1562587 = 2343881) B2343881
theorem B5634049 : Blo 1561478 5634049 := bstep (se 2 (by rfl) ⟨2112768, by rfl⟩ : syracuseStep 5634049 = 4225537) B4225537
theorem B7911431 : Blo 1561478 7911431 := bstep (se 1 (by rfl) ⟨5933573, by rfl⟩ : syracuseStep 7911431 = 11867147) B11867147
theorem B1562663 : Blo 1561478 1562663 := bstep (se 1 (by rfl) ⟨1171997, by rfl⟩ : syracuseStep 1562663 = 2343995) B2343995
theorem B1562703 : Blo 1561478 1562703 := bstep (se 1 (by rfl) ⟨1172027, by rfl⟩ : syracuseStep 1562703 = 2344055) B2344055
theorem B1562719 : Blo 1561478 1562719 := bstep (se 1 (by rfl) ⟨1172039, by rfl⟩ : syracuseStep 1562719 = 2344079) B2344079
theorem B1562747 : Blo 1561478 1562747 := bstep (se 1 (by rfl) ⟨1172060, by rfl⟩ : syracuseStep 1562747 = 2344121) B2344121
theorem B4511915 : Blo 1561478 4511915 := bstep (se 1 (by rfl) ⟨3383936, by rfl⟩ : syracuseStep 4511915 = 6767873) B6767873
theorem B1562799 : Blo 1561478 1562799 := bstep (se 1 (by rfl) ⟨1172099, by rfl⟩ : syracuseStep 1562799 = 2344199) B2344199
theorem B1562823 : Blo 1561478 1562823 := bstep (se 1 (by rfl) ⟨1172117, by rfl⟩ : syracuseStep 1562823 = 2344235) B2344235
theorem B1562843 : Blo 1561478 1562843 := bstep (se 1 (by rfl) ⟨1172132, by rfl⟩ : syracuseStep 1562843 = 2344265) B2344265
theorem B2636023 : Blo 1561478 2636023 := bstep (se 1 (by rfl) ⟨1977017, by rfl⟩ : syracuseStep 2636023 = 3954035) B3954035
theorem B1562919 : Blo 1561478 1562919 := bstep (se 1 (by rfl) ⟨1172189, by rfl⟩ : syracuseStep 1562919 = 2344379) B2344379
theorem B1562959 : Blo 1561478 1562959 := bstep (se 1 (by rfl) ⟨1172219, by rfl⟩ : syracuseStep 1562959 = 2344439) B2344439
theorem B1562975 : Blo 1561478 1562975 := bstep (se 1 (by rfl) ⟨1172231, by rfl⟩ : syracuseStep 1562975 = 2344463) B2344463
theorem B5929321 : Blo 1561478 5929321 := bstep (se 2 (by rfl) ⟨2223495, by rfl⟩ : syracuseStep 5929321 = 4446991) B4446991
theorem B1563003 : Blo 1561478 1563003 := bstep (se 1 (by rfl) ⟨1172252, by rfl⟩ : syracuseStep 1563003 = 2344505) B2344505
theorem B13343129 : Blo 1561478 13343129 := bstep (se 2 (by rfl) ⟨5003673, by rfl⟩ : syracuseStep 13343129 = 10007347) B10007347
theorem B1563055 : Blo 1561478 1563055 := bstep (se 1 (by rfl) ⟨1172291, by rfl⟩ : syracuseStep 1563055 = 2344583) B2344583
theorem B2636219 : Blo 1561478 2636219 := bstep (se 1 (by rfl) ⟨1977164, by rfl⟩ : syracuseStep 2636219 = 3954329) B3954329
theorem B1563079 : Blo 1561478 1563079 := bstep (se 1 (by rfl) ⟨1172309, by rfl⟩ : syracuseStep 1563079 = 2344619) B2344619
theorem B1563099 : Blo 1561478 1563099 := bstep (se 1 (by rfl) ⟨1172324, by rfl⟩ : syracuseStep 1563099 = 2344649) B2344649
theorem B7911917 : Blo 1561478 7911917 := bstep (se 3 (by rfl) ⟨1483484, by rfl⟩ : syracuseStep 7911917 = 2966969) B2966969
theorem B5003815 : Blo 1561478 5003815 := bstep (se 1 (by rfl) ⟨3752861, by rfl⟩ : syracuseStep 5003815 = 7505723) B7505723
theorem B2636327 : Blo 1561478 2636327 := bstep (se 1 (by rfl) ⟨1977245, by rfl⟩ : syracuseStep 2636327 = 3954491) B3954491
theorem B1563175 : Blo 1561478 1563175 := bstep (se 1 (by rfl) ⟨1172381, by rfl⟩ : syracuseStep 1563175 = 2344763) B2344763
theorem B1563215 : Blo 1561478 1563215 := bstep (se 1 (by rfl) ⟨1172411, by rfl⟩ : syracuseStep 1563215 = 2344823) B2344823
theorem B1563231 : Blo 1561478 1563231 := bstep (se 1 (by rfl) ⟨1172423, by rfl⟩ : syracuseStep 1563231 = 2344847) B2344847
theorem B5929595 : Blo 1561478 5929595 := bstep (se 1 (by rfl) ⟨4447196, by rfl⟩ : syracuseStep 5929595 = 8894393) B8894393
theorem B1563259 : Blo 1561478 1563259 := bstep (se 1 (by rfl) ⟨1172444, by rfl⟩ : syracuseStep 1563259 = 2344889) B2344889
theorem B1563311 : Blo 1561478 1563311 := bstep (se 1 (by rfl) ⟨1172483, by rfl⟩ : syracuseStep 1563311 = 2344967) B2344967
theorem B1563335 : Blo 1561478 1563335 := bstep (se 1 (by rfl) ⟨1172501, by rfl⟩ : syracuseStep 1563335 = 2345003) B2345003
theorem B1563355 : Blo 1561478 1563355 := bstep (se 1 (by rfl) ⟨1172516, by rfl⟩ : syracuseStep 1563355 = 2345033) B2345033
theorem B8444675 : Blo 1561478 8444675 := bstep (se 1 (by rfl) ⟨6333506, by rfl⟩ : syracuseStep 8444675 = 12667013) B12667013
theorem B1563431 : Blo 1561478 1563431 := bstep (se 1 (by rfl) ⟨1172573, by rfl⟩ : syracuseStep 1563431 = 2345147) B2345147
theorem B2636617 : Blo 1561478 2636617 := bstep (se 2 (by rfl) ⟨988731, by rfl⟩ : syracuseStep 2636617 = 1977463) B1977463
theorem B1563471 : Blo 1561478 1563471 := bstep (se 1 (by rfl) ⟨1172603, by rfl⟩ : syracuseStep 1563471 = 2345207) B2345207
theorem B2636651 : Blo 1561478 2636651 := bstep (se 1 (by rfl) ⟨1977488, by rfl⟩ : syracuseStep 2636651 = 3954977) B3954977
theorem B4447163 : Blo 1561478 4447163 := bstep (se 1 (by rfl) ⟨3335372, by rfl⟩ : syracuseStep 4447163 = 6670745) B6670745
theorem B17791973 : Blo 1561478 17791973 := bstep (se 4 (by rfl) ⟨1667997, by rfl⟩ : syracuseStep 17791973 = 3335995) B3335995
theorem B3513401 : Blo 1561478 3513401 := bstep (se 2 (by rfl) ⟨1317525, by rfl⟩ : syracuseStep 3513401 = 2635051) B2635051
theorem B10689707 : Blo 1561478 10689707 := bstep (se 1 (by rfl) ⟨8017280, by rfl⟩ : syracuseStep 10689707 = 16034561) B16034561
theorem B2964691 : Blo 1561478 2964691 := bstep (se 1 (by rfl) ⟨2223518, by rfl⟩ : syracuseStep 2964691 = 4447037) B4447037
theorem B2637049 : Blo 1561478 2637049 := bstep (se 2 (by rfl) ⟨988893, by rfl⟩ : syracuseStep 2637049 = 1977787) B1977787
theorem B7912727 : Blo 1561478 7912727 := bstep (se 1 (by rfl) ⟨5934545, by rfl⟩ : syracuseStep 7912727 = 11869091) B11869091
theorem B2342249 : Blo 1561478 2342249 := bstep (se 2 (by rfl) ⟨878343, by rfl⟩ : syracuseStep 2342249 = 1756687) B1756687
theorem B3513743 : Blo 1561478 3513743 := bstep (se 1 (by rfl) ⟨2635307, by rfl⟩ : syracuseStep 3513743 = 5270615) B5270615
theorem B3956111 : Blo 1561478 3956111 := bstep (se 1 (by rfl) ⟨2967083, by rfl⟩ : syracuseStep 3956111 = 5934167) B5934167
theorem B2342327 : Blo 1561478 2342327 := bstep (se 1 (by rfl) ⟨1756745, by rfl⟩ : syracuseStep 2342327 = 3513491) B3513491
theorem B2964919 : Blo 1561478 2964919 := bstep (se 1 (by rfl) ⟨2223689, by rfl⟩ : syracuseStep 2964919 = 4447379) B4447379
theorem B2342363 : Blo 1561478 2342363 := bstep (se 1 (by rfl) ⟨1756772, by rfl⟩ : syracuseStep 2342363 = 3513545) B3513545
theorem B2637319 : Blo 1561478 2637319 := bstep (se 1 (by rfl) ⟨1977989, by rfl⟩ : syracuseStep 2637319 = 3955979) B3955979
theorem B6676091 : Blo 1561478 6676091 := bstep (se 1 (by rfl) ⟨5007068, by rfl⟩ : syracuseStep 6676091 = 10014137) B10014137
theorem B5275259 : Blo 1561478 5275259 := bstep (se 1 (by rfl) ⟨3956444, by rfl⟩ : syracuseStep 5275259 = 7912889) B7912889
theorem B3514067 : Blo 1561478 3514067 := bstep (se 1 (by rfl) ⟨2635550, by rfl⟩ : syracuseStep 3514067 = 5271101) B5271101
theorem B3956435 : Blo 1561478 3956435 := bstep (se 1 (by rfl) ⟨2967326, by rfl⟩ : syracuseStep 3956435 = 5934653) B5934653
theorem B5275421 : Blo 1561478 5275421 := bstep (se 3 (by rfl) ⟨989141, by rfl⟩ : syracuseStep 5275421 = 1978283) B1978283
theorem B8896351 : Blo 1561478 8896351 := bstep (se 1 (by rfl) ⟨6672263, by rfl⟩ : syracuseStep 8896351 = 13344527) B13344527
theorem B2342831 : Blo 1561478 2342831 := bstep (se 1 (by rfl) ⟨1757123, by rfl⟩ : syracuseStep 2342831 = 3514247) B3514247
theorem B2637751 : Blo 1561478 2637751 := bstep (se 1 (by rfl) ⟨1978313, by rfl⟩ : syracuseStep 2637751 = 3956627) B3956627
theorem B15007673 : Blo 1561478 15007673 := bstep (se 2 (by rfl) ⟨5627877, by rfl⟩ : syracuseStep 15007673 = 11255755) B11255755
theorem B7512065 : Blo 1561478 7512065 := bstep (se 2 (by rfl) ⟨2817024, by rfl⟩ : syracuseStep 7512065 = 5634049) B5634049
theorem B30031883 : Blo 1561478 30031883 := bstep (se 1 (by rfl) ⟨22523912, by rfl⟩ : syracuseStep 30031883 = 45047825) B45047825
theorem B2343017 : Blo 1561478 2343017 := bstep (se 2 (by rfl) ⟨878631, by rfl⟩ : syracuseStep 2343017 = 1757263) B1757263
theorem B3514697 : Blo 1561478 3514697 := bstep (se 2 (by rfl) ⟨1318011, by rfl⟩ : syracuseStep 3514697 = 2636023) B2636023
theorem B3514715 : Blo 1561478 3514715 := bstep (se 1 (by rfl) ⟨2636036, by rfl⟩ : syracuseStep 3514715 = 5272073) B5272073
theorem B3957083 : Blo 1561478 3957083 := bstep (se 1 (by rfl) ⟨2967812, by rfl⟩ : syracuseStep 3957083 = 5935625) B5935625
theorem B6676843 : Blo 1561478 6676843 := bstep (se 1 (by rfl) ⟨5007632, by rfl⟩ : syracuseStep 6676843 = 10015265) B10015265
theorem B2343335 : Blo 1561478 2343335 := bstep (se 1 (by rfl) ⟨1757501, by rfl⟩ : syracuseStep 2343335 = 3515003) B3515003
theorem B7905761 : Blo 1561478 7905761 := bstep (se 2 (by rfl) ⟨2964660, by rfl⟩ : syracuseStep 7905761 = 5929321) B5929321
theorem B2343419 : Blo 1561478 2343419 := bstep (se 1 (by rfl) ⟨1757564, by rfl⟩ : syracuseStep 2343419 = 3515129) B3515129
theorem B5931539 : Blo 1561478 5931539 := bstep (se 1 (by rfl) ⟨4448654, by rfl⟩ : syracuseStep 5931539 = 8897309) B8897309
theorem B400802327 : Blo 1561478 400802327 := bstep (se 1 (by rfl) ⟨300601745, by rfl⟩ : syracuseStep 400802327 = 601203491) B601203491
theorem B25354781 : Blo 1561478 25354781 := bstep (se 3 (by rfl) ⟨4754021, by rfl⟩ : syracuseStep 25354781 = 9508043) B9508043
theorem B5276231 : Blo 1561478 5276231 := bstep (se 1 (by rfl) ⟨3957173, by rfl⟩ : syracuseStep 5276231 = 7914347) B7914347
theorem B26690147 : Blo 1561478 26690147 := bstep (se 1 (by rfl) ⟨20017610, by rfl⟩ : syracuseStep 26690147 = 40035221) B40035221
theorem B2343545 : Blo 1561478 2343545 := bstep (se 2 (by rfl) ⟨878829, by rfl⟩ : syracuseStep 2343545 = 1757659) B1757659
theorem B2343599 : Blo 1561478 2343599 := bstep (se 1 (by rfl) ⟨1757699, by rfl⟩ : syracuseStep 2343599 = 3515399) B3515399
theorem B4448951 : Blo 1561478 4448951 := bstep (se 1 (by rfl) ⟨3336713, by rfl⟩ : syracuseStep 4448951 = 6673427) B6673427
theorem B2343647 : Blo 1561478 2343647 := bstep (se 1 (by rfl) ⟨1757735, by rfl⟩ : syracuseStep 2343647 = 3515471) B3515471
theorem B42738445 : Blo 1561478 42738445 := bstep (se 3 (by rfl) ⟨8013458, by rfl⟩ : syracuseStep 42738445 = 16026917) B16026917
theorem B11871035 : Blo 1561478 11871035 := bstep (se 1 (by rfl) ⟨8903276, by rfl⟩ : syracuseStep 11871035 = 17806553) B17806553
theorem B7512911 : Blo 1561478 7512911 := bstep (se 1 (by rfl) ⟨5634683, by rfl⟩ : syracuseStep 7512911 = 11269367) B11269367
theorem B3515291 : Blo 1561478 3515291 := bstep (se 1 (by rfl) ⟨2636468, by rfl⟩ : syracuseStep 3515291 = 5272937) B5272937
theorem B2343911 : Blo 1561478 2343911 := bstep (se 1 (by rfl) ⟨1757933, by rfl⟩ : syracuseStep 2343911 = 3515867) B3515867
theorem B5276663 : Blo 1561478 5276663 := bstep (se 1 (by rfl) ⟨3957497, by rfl⟩ : syracuseStep 5276663 = 7914995) B7914995
theorem B3515489 : Blo 1561478 3515489 := bstep (se 2 (by rfl) ⟨1318308, by rfl⟩ : syracuseStep 3515489 = 2636617) B2636617
theorem B4752599 : Blo 1561478 4752599 := bstep (se 1 (by rfl) ⟨3564449, by rfl⟩ : syracuseStep 4752599 = 7128899) B7128899
theorem B2344169 : Blo 1561478 2344169 := bstep (se 2 (by rfl) ⟨879063, by rfl⟩ : syracuseStep 2344169 = 1758127) B1758127
theorem B2344223 : Blo 1561478 2344223 := bstep (se 1 (by rfl) ⟨1758167, by rfl⟩ : syracuseStep 2344223 = 3516335) B3516335
theorem B3515687 : Blo 1561478 3515687 := bstep (se 1 (by rfl) ⟨2636765, by rfl⟩ : syracuseStep 3515687 = 5273531) B5273531
theorem B11257139 : Blo 1561478 11257139 := bstep (se 1 (by rfl) ⟨8442854, by rfl⟩ : syracuseStep 11257139 = 16885709) B16885709
theorem B7505261 : Blo 1561478 7505261 := bstep (se 3 (by rfl) ⟨1407236, by rfl⟩ : syracuseStep 7505261 = 2814473) B2814473
theorem B50660761 : Blo 1561478 50660761 := bstep (se 2 (by rfl) ⟨18997785, by rfl⟩ : syracuseStep 50660761 = 37995571) B37995571
theorem B3335585 : Blo 1561478 3335585 := bstep (se 2 (by rfl) ⟨1250844, by rfl⟩ : syracuseStep 3335585 = 2501689) B2501689
theorem B4449725 : Blo 1561478 4449725 := bstep (se 3 (by rfl) ⟨834323, by rfl⟩ : syracuseStep 4449725 = 1668647) B1668647
theorem B2344391 : Blo 1561478 2344391 := bstep (se 1 (by rfl) ⟨1758293, by rfl⟩ : syracuseStep 2344391 = 3516587) B3516587
theorem B3007943 : Blo 1561478 3007943 := bstep (se 1 (by rfl) ⟨2255957, by rfl⟩ : syracuseStep 3007943 = 4511915) B4511915
theorem B3516065 : Blo 1561478 3516065 := bstep (se 2 (by rfl) ⟨1318524, by rfl⟩ : syracuseStep 3516065 = 2637049) B2637049
theorem B2344745 : Blo 1561478 2344745 := bstep (se 2 (by rfl) ⟨879279, by rfl⟩ : syracuseStep 2344745 = 1758559) B1758559
theorem B2344751 : Blo 1561478 2344751 := bstep (se 1 (by rfl) ⟨1758563, by rfl⟩ : syracuseStep 2344751 = 3517127) B3517127
theorem B5629783 : Blo 1561478 5629783 := bstep (se 1 (by rfl) ⟨4222337, by rfl⟩ : syracuseStep 5629783 = 8444675) B8444675
theorem B3516425 : Blo 1561478 3516425 := bstep (se 2 (by rfl) ⟨1318659, by rfl⟩ : syracuseStep 3516425 = 2637319) B2637319
theorem B6670471 : Blo 1561478 6670471 := bstep (se 1 (by rfl) ⟨5002853, by rfl⟩ : syracuseStep 6670471 = 10005707) B10005707
theorem B9144515 : Blo 1561478 9144515 := bstep (se 1 (by rfl) ⟨6858386, by rfl⟩ : syracuseStep 9144515 = 13716773) B13716773
theorem B2672905 : Blo 1561478 2672905 := bstep (se 2 (by rfl) ⟨1002339, by rfl⟩ : syracuseStep 2672905 = 2004679) B2004679
theorem B14256445 : Blo 1561478 14256445 := bstep (se 3 (by rfl) ⟨2673083, by rfl⟩ : syracuseStep 14256445 = 5346167) B5346167
theorem B4450727 : Blo 1561478 4450727 := bstep (se 1 (by rfl) ⟨3338045, by rfl⟩ : syracuseStep 4450727 = 6676091) B6676091
theorem B3516839 : Blo 1561478 3516839 := bstep (se 1 (by rfl) ⟨2637629, by rfl⟩ : syracuseStep 3516839 = 5275259) B5275259
theorem B3516947 : Blo 1561478 3516947 := bstep (se 1 (by rfl) ⟨2637710, by rfl⟩ : syracuseStep 3516947 = 5275421) B5275421
theorem B3517001 : Blo 1561478 3517001 := bstep (se 2 (by rfl) ⟨1318875, by rfl⟩ : syracuseStep 3517001 = 2637751) B2637751
theorem B27052631 : Blo 1561478 27052631 := bstep (se 1 (by rfl) ⟨20289473, by rfl⟩ : syracuseStep 27052631 = 40578947) B40578947
theorem B10005115 : Blo 1561478 10005115 := bstep (se 1 (by rfl) ⟨7503836, by rfl⟩ : syracuseStep 10005115 = 15007673) B15007673
theorem B7908029 : Blo 1561478 7908029 := bstep (se 3 (by rfl) ⟨1482755, by rfl⟩ : syracuseStep 7908029 = 2965511) B2965511
theorem B5270291 : Blo 1561478 5270291 := bstep (se 1 (by rfl) ⟨3952718, by rfl⟩ : syracuseStep 5270291 = 7905437) B7905437
theorem B19016471 : Blo 1561478 19016471 := bstep (se 1 (by rfl) ⟨14262353, by rfl⟩ : syracuseStep 19016471 = 28524707) B28524707
theorem B3517415 : Blo 1561478 3517415 := bstep (se 1 (by rfl) ⟨2638061, by rfl⟩ : syracuseStep 3517415 = 5276123) B5276123
theorem B11865203 : Blo 1561478 11865203 := bstep (se 1 (by rfl) ⟨8898902, by rfl⟩ : syracuseStep 11865203 = 17797805) B17797805
theorem B13356251 : Blo 1561478 13356251 := bstep (se 1 (by rfl) ⟨10017188, by rfl⟩ : syracuseStep 13356251 = 20034377) B20034377
theorem B3337465 : Blo 1561478 3337465 := bstep (se 2 (by rfl) ⟨1251549, by rfl⟩ : syracuseStep 3337465 = 2503099) B2503099
theorem B1977691 : Blo 1561478 1977691 := bstep (se 1 (by rfl) ⟨1483268, by rfl⟩ : syracuseStep 1977691 = 2966537) B2966537
theorem B3517793 : Blo 1561478 3517793 := bstep (se 2 (by rfl) ⟨1319172, by rfl⟩ : syracuseStep 3517793 = 2638345) B2638345
theorem B12029303 : Blo 1561478 12029303 := bstep (se 1 (by rfl) ⟨9021977, by rfl⟩ : syracuseStep 12029303 = 18043955) B18043955
theorem B5934455 : Blo 1561478 5934455 := bstep (se 1 (by rfl) ⟨4450841, by rfl⟩ : syracuseStep 5934455 = 8901683) B8901683
theorem B6671753 : Blo 1561478 6671753 := bstep (se 2 (by rfl) ⟨2501907, by rfl⟩ : syracuseStep 6671753 = 5003815) B5003815
theorem B8564105 : Blo 1561478 8564105 := bstep (se 2 (by rfl) ⟨3211539, by rfl⟩ : syracuseStep 8564105 = 6423079) B6423079
theorem B5631569 : Blo 1561478 5631569 := bstep (se 2 (by rfl) ⟨2111838, by rfl⟩ : syracuseStep 5631569 = 4223677) B4223677
theorem B4451935 : Blo 1561478 4451935 := bstep (se 1 (by rfl) ⟨3338951, by rfl⟩ : syracuseStep 4451935 = 6677903) B6677903
theorem B5271155 : Blo 1561478 5271155 := bstep (se 1 (by rfl) ⟨3953366, by rfl⟩ : syracuseStep 5271155 = 7906733) B7906733
theorem B1756975 : Blo 1561478 1756975 := bstep (se 1 (by rfl) ⟨1317731, by rfl⟩ : syracuseStep 1756975 = 2635463) B2635463
theorem B5271425 : Blo 1561478 5271425 := bstep (se 2 (by rfl) ⟨1976784, by rfl⟩ : syracuseStep 5271425 = 3953569) B3953569
theorem B1757083 : Blo 1561478 1757083 := bstep (se 1 (by rfl) ⟨1317812, by rfl⟩ : syracuseStep 1757083 = 2635625) B2635625
theorem B3952921 : Blo 1561478 3952921 := bstep (se 2 (by rfl) ⟨1482345, by rfl⟩ : syracuseStep 3952921 = 2964691) B2964691
theorem B1757479 : Blo 1561478 1757479 := bstep (se 1 (by rfl) ⟨1318109, by rfl⟩ : syracuseStep 1757479 = 2636219) B2636219
theorem B1978663 : Blo 1561478 1978663 := bstep (se 1 (by rfl) ⟨1483997, by rfl⟩ : syracuseStep 1978663 = 2967995) B2967995
theorem B1757551 : Blo 1561478 1757551 := bstep (se 1 (by rfl) ⟨1318163, by rfl⟩ : syracuseStep 1757551 = 2636327) B2636327
theorem B3953063 : Blo 1561478 3953063 := bstep (se 1 (by rfl) ⟨2964797, by rfl⟩ : syracuseStep 3953063 = 5929595) B5929595
theorem B2224703 : Blo 1561478 2224703 := bstep (se 1 (by rfl) ⟨1668527, by rfl⟩ : syracuseStep 2224703 = 3337055) B3337055
theorem B3338815 : Blo 1561478 3338815 := bstep (se 1 (by rfl) ⟨2504111, by rfl⟩ : syracuseStep 3338815 = 5008223) B5008223
theorem B1757767 : Blo 1561478 1757767 := bstep (se 1 (by rfl) ⟨1318325, by rfl⟩ : syracuseStep 1757767 = 2636651) B2636651
theorem B3953225 : Blo 1561478 3953225 := bstep (se 2 (by rfl) ⟨1482459, by rfl⟩ : syracuseStep 3953225 = 2964919) B2964919
theorem B5272235 : Blo 1561478 5272235 := bstep (se 1 (by rfl) ⟨3954176, by rfl⟩ : syracuseStep 5272235 = 7908353) B7908353
theorem B4010671 : Blo 1561478 4010671 := bstep (se 1 (by rfl) ⟨3008003, by rfl⟩ : syracuseStep 4010671 = 6016007) B6016007
theorem B1561499 : Blo 1561478 1561499 := bstep (se 1 (by rfl) ⟨1171124, by rfl⟩ : syracuseStep 1561499 = 2342249) B2342249
theorem B1561551 : Blo 1561478 1561551 := bstep (se 1 (by rfl) ⟨1171163, by rfl⟩ : syracuseStep 1561551 = 2342327) B2342327
theorem B1561575 : Blo 1561478 1561575 := bstep (se 1 (by rfl) ⟨1171181, by rfl⟩ : syracuseStep 1561575 = 2342363) B2342363
theorem B5272775 : Blo 1561478 5272775 := bstep (se 1 (by rfl) ⟨3954581, by rfl⟩ : syracuseStep 5272775 = 7909163) B7909163
theorem B1561887 : Blo 1561478 1561887 := bstep (se 1 (by rfl) ⟨1171415, by rfl⟩ : syracuseStep 1561887 = 2342831) B2342831
theorem B1561947 : Blo 1561478 1561947 := bstep (se 1 (by rfl) ⟨1171460, by rfl⟩ : syracuseStep 1561947 = 2342921) B2342921
theorem B1561967 : Blo 1561478 1561967 := bstep (se 1 (by rfl) ⟨1171475, by rfl⟩ : syracuseStep 1561967 = 2342951) B2342951
theorem B1562023 : Blo 1561478 1562023 := bstep (se 1 (by rfl) ⟨1171517, by rfl⟩ : syracuseStep 1562023 = 2343035) B2343035
theorem B1758631 : Blo 1561478 1758631 := bstep (se 1 (by rfl) ⟨1318973, by rfl⟩ : syracuseStep 1758631 = 2637947) B2637947
theorem B7222765 : Blo 1561478 7222765 := bstep (se 3 (by rfl) ⟨1354268, by rfl⟩ : syracuseStep 7222765 = 2708537) B2708537
theorem B1562107 : Blo 1561478 1562107 := bstep (se 1 (by rfl) ⟨1171580, by rfl⟩ : syracuseStep 1562107 = 2343161) B2343161
theorem B7910945 : Blo 1561478 7910945 := bstep (se 2 (by rfl) ⟨2966604, by rfl⟩ : syracuseStep 7910945 = 5933209) B5933209
theorem B1562175 : Blo 1561478 1562175 := bstep (se 1 (by rfl) ⟨1171631, by rfl⟩ : syracuseStep 1562175 = 2343263) B2343263
theorem B1562183 : Blo 1561478 1562183 := bstep (se 1 (by rfl) ⟨1171637, by rfl⟩ : syracuseStep 1562183 = 2343275) B2343275
theorem B1562335 : Blo 1561478 1562335 := bstep (se 1 (by rfl) ⟨1171751, by rfl⟩ : syracuseStep 1562335 = 2343503) B2343503
theorem B1562415 : Blo 1561478 1562415 := bstep (se 1 (by rfl) ⟨1171811, by rfl⟩ : syracuseStep 1562415 = 2343623) B2343623
theorem B6420311 : Blo 1561478 6420311 := bstep (se 1 (by rfl) ⟨4815233, by rfl⟩ : syracuseStep 6420311 = 9630467) B9630467
theorem B1562523 : Blo 1561478 1562523 := bstep (se 1 (by rfl) ⟨1171892, by rfl⟩ : syracuseStep 1562523 = 2343785) B2343785
theorem B1562575 : Blo 1561478 1562575 := bstep (se 1 (by rfl) ⟨1171931, by rfl⟩ : syracuseStep 1562575 = 2343863) B2343863
theorem B2815951 : Blo 1561478 2815951 := bstep (se 1 (by rfl) ⟨2111963, by rfl⟩ : syracuseStep 2815951 = 4223927) B4223927
theorem B1562599 : Blo 1561478 1562599 := bstep (se 1 (by rfl) ⟨1171949, by rfl⟩ : syracuseStep 1562599 = 2343899) B2343899
theorem B1669339 : Blo 1561478 1669339 := bstep (se 1 (by rfl) ⟨1252004, by rfl⟩ : syracuseStep 1669339 = 2504009) B2504009
theorem B8894711 : Blo 1561478 8894711 := bstep (se 1 (by rfl) ⟨6671033, by rfl⟩ : syracuseStep 8894711 = 13342067) B13342067
theorem B7510295 : Blo 1561478 7510295 := bstep (se 1 (by rfl) ⟨5632721, by rfl⟩ : syracuseStep 7510295 = 11265443) B11265443
theorem B72194327 : Blo 1561478 72194327 := bstep (se 1 (by rfl) ⟨54145745, by rfl⟩ : syracuseStep 72194327 = 108291491) B108291491
theorem B1562911 : Blo 1561478 1562911 := bstep (se 1 (by rfl) ⟨1172183, by rfl⟩ : syracuseStep 1562911 = 2344367) B2344367
theorem B1562971 : Blo 1561478 1562971 := bstep (se 1 (by rfl) ⟨1172228, by rfl⟩ : syracuseStep 1562971 = 2344457) B2344457
theorem B1562991 : Blo 1561478 1562991 := bstep (se 1 (by rfl) ⟨1172243, by rfl⟩ : syracuseStep 1562991 = 2344487) B2344487
theorem B1563047 : Blo 1561478 1563047 := bstep (se 1 (by rfl) ⟨1172285, by rfl⟩ : syracuseStep 1563047 = 2344571) B2344571
theorem B3955169 : Blo 1561478 3955169 := bstep (se 2 (by rfl) ⟨1483188, by rfl⟩ : syracuseStep 3955169 = 2966377) B2966377
theorem B1563131 : Blo 1561478 1563131 := bstep (se 1 (by rfl) ⟨1172348, by rfl⟩ : syracuseStep 1563131 = 2344697) B2344697
theorem B11262503 : Blo 1561478 11262503 := bstep (se 1 (by rfl) ⟨8446877, by rfl⟩ : syracuseStep 11262503 = 16893755) B16893755
theorem B162413099 : Blo 1561478 162413099 := bstep (se 1 (by rfl) ⟨121809824, by rfl⟩ : syracuseStep 162413099 = 243619649) B243619649
theorem B1563199 : Blo 1561478 1563199 := bstep (se 1 (by rfl) ⟨1172399, by rfl⟩ : syracuseStep 1563199 = 2344799) B2344799
theorem B1563207 : Blo 1561478 1563207 := bstep (se 1 (by rfl) ⟨1172405, by rfl⟩ : syracuseStep 1563207 = 2344811) B2344811
theorem B17808011 : Blo 1561478 17808011 := bstep (se 1 (by rfl) ⟨13356008, by rfl⟩ : syracuseStep 17808011 = 26712017) B26712017
theorem B6675119 : Blo 1561478 6675119 := bstep (se 1 (by rfl) ⟨5006339, by rfl⟩ : syracuseStep 6675119 = 10012679) B10012679
theorem B5274287 : Blo 1561478 5274287 := bstep (se 1 (by rfl) ⟨3955715, by rfl⟩ : syracuseStep 5274287 = 7911431) B7911431
theorem B1563359 : Blo 1561478 1563359 := bstep (se 1 (by rfl) ⟨1172519, by rfl⟩ : syracuseStep 1563359 = 2345039) B2345039
theorem B1563439 : Blo 1561478 1563439 := bstep (se 1 (by rfl) ⟨1172579, by rfl⟩ : syracuseStep 1563439 = 2345159) B2345159
theorem B16030619 : Blo 1561478 16030619 := bstep (se 1 (by rfl) ⟨12022964, by rfl⟩ : syracuseStep 16030619 = 24045929) B24045929
theorem B8895419 : Blo 1561478 8895419 := bstep (se 1 (by rfl) ⟨6671564, by rfl⟩ : syracuseStep 8895419 = 13343129) B13343129
theorem B3955675 : Blo 1561478 3955675 := bstep (se 1 (by rfl) ⟨2966756, by rfl⟩ : syracuseStep 3955675 = 5933513) B5933513
theorem B4447219 : Blo 1561478 4447219 := bstep (se 1 (by rfl) ⟨3335414, by rfl⟩ : syracuseStep 4447219 = 6670829) B6670829
theorem B6675443 : Blo 1561478 6675443 := bstep (se 1 (by rfl) ⟨5006582, by rfl⟩ : syracuseStep 6675443 = 10013165) B10013165
theorem B5274611 : Blo 1561478 5274611 := bstep (se 1 (by rfl) ⟨3955958, by rfl⟩ : syracuseStep 5274611 = 7911917) B7911917
theorem B3513383 : Blo 1561478 3513383 := bstep (se 1 (by rfl) ⟨2635037, by rfl⟩ : syracuseStep 3513383 = 5270075) B5270075
theorem B3513563 : Blo 1561478 3513563 := bstep (se 1 (by rfl) ⟨2635172, by rfl⟩ : syracuseStep 3513563 = 5270345) B5270345
theorem B3955999 : Blo 1561478 3955999 := bstep (se 1 (by rfl) ⟨2966999, by rfl⟩ : syracuseStep 3955999 = 5933999) B5933999
theorem B2964775 : Blo 1561478 2964775 := bstep (se 1 (by rfl) ⟨2223581, by rfl⟩ : syracuseStep 2964775 = 4447163) B4447163
theorem B11861315 : Blo 1561478 11861315 := bstep (se 1 (by rfl) ⟨8895986, by rfl⟩ : syracuseStep 11861315 = 17791973) B17791973
theorem B2342267 : Blo 1561478 2342267 := bstep (se 1 (by rfl) ⟨1756700, by rfl⟩ : syracuseStep 2342267 = 3513401) B3513401
theorem B11869577 : Blo 1561478 11869577 := bstep (se 2 (by rfl) ⟨4451091, by rfl⟩ : syracuseStep 11869577 = 8902183) B8902183
theorem B3513761 : Blo 1561478 3513761 := bstep (se 2 (by rfl) ⟨1317660, by rfl⟩ : syracuseStep 3513761 = 2635321) B2635321
theorem B7126471 : Blo 1561478 7126471 := bstep (se 1 (by rfl) ⟨5344853, by rfl⟩ : syracuseStep 7126471 = 10689707) B10689707
theorem B9018839 : Blo 1561478 9018839 := bstep (se 1 (by rfl) ⟨6764129, by rfl⟩ : syracuseStep 9018839 = 13528259) B13528259
theorem B2342393 : Blo 1561478 2342393 := bstep (se 2 (by rfl) ⟨878397, by rfl⟩ : syracuseStep 2342393 = 1756795) B1756795
theorem B5275151 : Blo 1561478 5275151 := bstep (se 1 (by rfl) ⟨3956363, by rfl⟩ : syracuseStep 5275151 = 7912727) B7912727
theorem B25337387 : Blo 1561478 25337387 := bstep (se 1 (by rfl) ⟨19003040, by rfl⟩ : syracuseStep 25337387 = 38006081) B38006081
theorem B2342495 : Blo 1561478 2342495 := bstep (se 1 (by rfl) ⟨1756871, by rfl⟩ : syracuseStep 2342495 = 3513743) B3513743
theorem B2637407 : Blo 1561478 2637407 := bstep (se 1 (by rfl) ⟨1978055, by rfl⟩ : syracuseStep 2637407 = 3956111) B3956111
theorem B11861801 : Blo 1561478 11861801 := bstep (se 2 (by rfl) ⟨4448175, by rfl⟩ : syracuseStep 11861801 = 8896351) B8896351
theorem B2342711 : Blo 1561478 2342711 := bstep (se 1 (by rfl) ⟨1757033, by rfl⟩ : syracuseStep 2342711 = 3514067) B3514067
theorem B2637623 : Blo 1561478 2637623 := bstep (se 1 (by rfl) ⟨1978217, by rfl⟩ : syracuseStep 2637623 = 3956435) B3956435
theorem B21372731 : Blo 1561478 21372731 := bstep (se 1 (by rfl) ⟨16029548, by rfl⟩ : syracuseStep 21372731 = 32059097) B32059097
theorem B3514319 : Blo 1561478 3514319 := bstep (se 1 (by rfl) ⟨2635739, by rfl⟩ : syracuseStep 3514319 = 5271479) B5271479
theorem B20021255 : Blo 1561478 20021255 := bstep (se 1 (by rfl) ⟨15015941, by rfl⟩ : syracuseStep 20021255 = 30031883) B30031883
theorem B2343131 : Blo 1561478 2343131 := bstep (se 1 (by rfl) ⟨1757348, by rfl⟩ : syracuseStep 2343131 = 3514697) B3514697
theorem B2343143 : Blo 1561478 2343143 := bstep (se 1 (by rfl) ⟨1757357, by rfl⟩ : syracuseStep 2343143 = 3514715) B3514715
theorem B2638055 : Blo 1561478 2638055 := bstep (se 1 (by rfl) ⟨1978541, by rfl⟩ : syracuseStep 2638055 = 3957083) B3957083
theorem B3563873 : Blo 1561478 3563873 := bstep (se 2 (by rfl) ⟨1336452, by rfl⟩ : syracuseStep 3563873 = 2672905) B2672905
theorem B2343305 : Blo 1561478 2343305 := bstep (se 2 (by rfl) ⟨878739, by rfl⟩ : syracuseStep 2343305 = 1757479) B1757479
theorem B2638217 : Blo 1561478 2638217 := bstep (se 2 (by rfl) ⟨989331, by rfl⟩ : syracuseStep 2638217 = 1978663) B1978663
theorem B17793431 : Blo 1561478 17793431 := bstep (se 1 (by rfl) ⟨13345073, by rfl⟩ : syracuseStep 17793431 = 26690147) B26690147
theorem B3514823 : Blo 1561478 3514823 := bstep (se 1 (by rfl) ⟨2636117, by rfl⟩ : syracuseStep 3514823 = 5272235) B5272235
theorem B2965967 : Blo 1561478 2965967 := bstep (se 1 (by rfl) ⟨2224475, by rfl⟩ : syracuseStep 2965967 = 4448951) B4448951
theorem B2343401 : Blo 1561478 2343401 := bstep (se 2 (by rfl) ⟨878775, by rfl⟩ : syracuseStep 2343401 = 1757551) B1757551
theorem B7914023 : Blo 1561478 7914023 := bstep (se 1 (by rfl) ⟨5935517, by rfl⟩ : syracuseStep 7914023 = 11871035) B11871035
theorem B12673597 : Blo 1561478 12673597 := bstep (se 3 (by rfl) ⟨2376299, by rfl⟩ : syracuseStep 12673597 = 4752599) B4752599
theorem B2343527 : Blo 1561478 2343527 := bstep (se 1 (by rfl) ⟨1757645, by rfl⟩ : syracuseStep 2343527 = 3515291) B3515291
theorem B2343659 : Blo 1561478 2343659 := bstep (se 1 (by rfl) ⟨1757744, by rfl⟩ : syracuseStep 2343659 = 3515489) B3515489
theorem B2343689 : Blo 1561478 2343689 := bstep (se 2 (by rfl) ⟨878883, by rfl⟩ : syracuseStep 2343689 = 1757767) B1757767
theorem B3515183 : Blo 1561478 3515183 := bstep (se 1 (by rfl) ⟨2636387, by rfl⟩ : syracuseStep 3515183 = 5272775) B5272775
theorem B2343791 : Blo 1561478 2343791 := bstep (se 1 (by rfl) ⟨1757843, by rfl⟩ : syracuseStep 2343791 = 3515687) B3515687
theorem B7504759 : Blo 1561478 7504759 := bstep (se 1 (by rfl) ⟨5628569, by rfl⟩ : syracuseStep 7504759 = 11257139) B11257139
theorem B2966483 : Blo 1561478 2966483 := bstep (se 1 (by rfl) ⟨2224862, by rfl⟩ : syracuseStep 2966483 = 4449725) B4449725
theorem B56984593 : Blo 1561478 56984593 := bstep (se 2 (by rfl) ⟨21369222, by rfl⟩ : syracuseStep 56984593 = 42738445) B42738445
theorem B2344043 : Blo 1561478 2344043 := bstep (se 1 (by rfl) ⟨1758032, by rfl⟩ : syracuseStep 2344043 = 3516065) B3516065
theorem B2344283 : Blo 1561478 2344283 := bstep (se 1 (by rfl) ⟨1758212, by rfl⟩ : syracuseStep 2344283 = 3516425) B3516425
theorem B30033341 : Blo 1561478 30033341 := bstep (se 3 (by rfl) ⟨5631251, by rfl⟩ : syracuseStep 30033341 = 11262503) B11262503
theorem B6096343 : Blo 1561478 6096343 := bstep (se 1 (by rfl) ⟨4572257, by rfl⟩ : syracuseStep 6096343 = 9144515) B9144515
theorem B5932541 : Blo 1561478 5932541 := bstep (se 3 (by rfl) ⟨1112351, by rfl⟩ : syracuseStep 5932541 = 2224703) B2224703
theorem B5006863 : Blo 1561478 5006863 := bstep (se 1 (by rfl) ⟨3755147, by rfl⟩ : syracuseStep 5006863 = 7510295) B7510295
theorem B48129551 : Blo 1561478 48129551 := bstep (se 1 (by rfl) ⟨36097163, by rfl⟩ : syracuseStep 48129551 = 72194327) B72194327
theorem B2344559 : Blo 1561478 2344559 := bstep (se 1 (by rfl) ⟨1758419, by rfl⟩ : syracuseStep 2344559 = 3516839) B3516839
theorem B4449953 : Blo 1561478 4449953 := bstep (se 2 (by rfl) ⟨1668732, by rfl⟩ : syracuseStep 4449953 = 3337465) B3337465
theorem B2344631 : Blo 1561478 2344631 := bstep (se 1 (by rfl) ⟨1758473, by rfl⟩ : syracuseStep 2344631 = 3516947) B3516947
theorem B108275399 : Blo 1561478 108275399 := bstep (se 1 (by rfl) ⟨81206549, by rfl⟩ : syracuseStep 108275399 = 162413099) B162413099
theorem B2344667 : Blo 1561478 2344667 := bstep (se 1 (by rfl) ⟨1758500, by rfl⟩ : syracuseStep 2344667 = 3517001) B3517001
theorem B11872007 : Blo 1561478 11872007 := bstep (se 1 (by rfl) ⟨8904005, by rfl⟩ : syracuseStep 11872007 = 17808011) B17808011
theorem B4450079 : Blo 1561478 4450079 := bstep (se 1 (by rfl) ⟨3337559, by rfl⟩ : syracuseStep 4450079 = 6675119) B6675119
theorem B3516191 : Blo 1561478 3516191 := bstep (se 1 (by rfl) ⟨2637143, by rfl⟩ : syracuseStep 3516191 = 5274287) B5274287
theorem B2344841 : Blo 1561478 2344841 := bstep (se 2 (by rfl) ⟨879315, by rfl⟩ : syracuseStep 2344841 = 1758631) B1758631
theorem B2344943 : Blo 1561478 2344943 := bstep (se 1 (by rfl) ⟨1758707, by rfl⟩ : syracuseStep 2344943 = 3517415) B3517415
theorem B4450295 : Blo 1561478 4450295 := bstep (se 1 (by rfl) ⟨3337721, by rfl⟩ : syracuseStep 4450295 = 6675443) B6675443
theorem B3516407 : Blo 1561478 3516407 := bstep (se 1 (by rfl) ⟨2637305, by rfl⟩ : syracuseStep 3516407 = 5274611) B5274611
theorem B7907543 : Blo 1561478 7907543 := bstep (se 1 (by rfl) ⟨5930657, by rfl⟩ : syracuseStep 7907543 = 11861315) B11861315
theorem B2345195 : Blo 1561478 2345195 := bstep (se 1 (by rfl) ⟨1758896, by rfl⟩ : syracuseStep 2345195 = 3517793) B3517793
theorem B3516767 : Blo 1561478 3516767 := bstep (se 1 (by rfl) ⟨2637575, by rfl⟩ : syracuseStep 3516767 = 5275151) B5275151
theorem B3754379 : Blo 1561478 3754379 := bstep (se 1 (by rfl) ⟨2815784, by rfl⟩ : syracuseStep 3754379 = 5631569) B5631569
theorem B7506377 : Blo 1561478 7506377 := bstep (se 2 (by rfl) ⟨2814891, by rfl⟩ : syracuseStep 7506377 = 5629783) B5629783
theorem B7907867 : Blo 1561478 7907867 := bstep (se 1 (by rfl) ⟨5930900, by rfl⟩ : syracuseStep 7907867 = 11861801) B11861801
theorem B14248487 : Blo 1561478 14248487 := bstep (se 1 (by rfl) ⟨10686365, by rfl⟩ : syracuseStep 14248487 = 21372731) B21372731
theorem B3754601 : Blo 1561478 3754601 := bstep (se 2 (by rfl) ⟨1407975, by rfl⟩ : syracuseStep 3754601 = 2815951) B2815951
theorem B5008043 : Blo 1561478 5008043 := bstep (se 1 (by rfl) ⟨3756032, by rfl⟩ : syracuseStep 5008043 = 7512065) B7512065
theorem B5270507 : Blo 1561478 5270507 := bstep (se 1 (by rfl) ⟨3952880, by rfl⟩ : syracuseStep 5270507 = 7905761) B7905761
theorem B267201551 : Blo 1561478 267201551 := bstep (se 1 (by rfl) ⟨200401163, by rfl⟩ : syracuseStep 267201551 = 400802327) B400802327
theorem B16903187 : Blo 1561478 16903187 := bstep (se 1 (by rfl) ⟨12677390, by rfl⟩ : syracuseStep 16903187 = 25354781) B25354781
theorem B5270561 : Blo 1561478 5270561 := bstep (se 2 (by rfl) ⟨1976460, by rfl⟩ : syracuseStep 5270561 = 3952921) B3952921
theorem B3517487 : Blo 1561478 3517487 := bstep (se 1 (by rfl) ⟨2638115, by rfl⟩ : syracuseStep 3517487 = 5276231) B5276231
theorem B19008593 : Blo 1561478 19008593 := bstep (se 2 (by rfl) ⟨7128222, by rfl⟩ : syracuseStep 19008593 = 14256445) B14256445
theorem B5008607 : Blo 1561478 5008607 := bstep (se 1 (by rfl) ⟨3756455, by rfl⟩ : syracuseStep 5008607 = 7512911) B7512911
theorem B3517775 : Blo 1561478 3517775 := bstep (se 1 (by rfl) ⟨2638331, by rfl⟩ : syracuseStep 3517775 = 5276663) B5276663
theorem B4451753 : Blo 1561478 4451753 := bstep (se 2 (by rfl) ⟨1669407, by rfl⟩ : syracuseStep 4451753 = 3338815) B3338815
theorem B13340153 : Blo 1561478 13340153 := bstep (se 2 (by rfl) ⟨5002557, by rfl⟩ : syracuseStep 13340153 = 10005115) B10005115
theorem B4280207 : Blo 1561478 4280207 := bstep (se 1 (by rfl) ⟨3210155, by rfl⟩ : syracuseStep 4280207 = 6420311) B6420311
theorem B3953033 : Blo 1561478 3953033 := bstep (se 2 (by rfl) ⟨1482387, by rfl⟩ : syracuseStep 3953033 = 2964775) B2964775
theorem B18035087 : Blo 1561478 18035087 := bstep (se 1 (by rfl) ⟨13526315, by rfl⟩ : syracuseStep 18035087 = 27052631) B27052631
theorem B5272019 : Blo 1561478 5272019 := bstep (se 1 (by rfl) ⟨3954014, by rfl⟩ : syracuseStep 5272019 = 7908029) B7908029
theorem B12677647 : Blo 1561478 12677647 := bstep (se 1 (by rfl) ⟨9508235, by rfl⟩ : syracuseStep 12677647 = 19016471) B19016471
theorem B67547681 : Blo 1561478 67547681 := bstep (se 2 (by rfl) ⟨25330380, by rfl⟩ : syracuseStep 67547681 = 50660761) B50660761
theorem B10687079 : Blo 1561478 10687079 := bstep (se 1 (by rfl) ⟨8015309, by rfl⟩ : syracuseStep 10687079 = 16030619) B16030619
theorem B9630353 : Blo 1561478 9630353 := bstep (se 2 (by rfl) ⟨3611382, by rfl⟩ : syracuseStep 9630353 = 7222765) B7222765
theorem B7910135 : Blo 1561478 7910135 := bstep (se 1 (by rfl) ⟨5932601, by rfl⟩ : syracuseStep 7910135 = 11865203) B11865203
theorem B5935913 : Blo 1561478 5935913 := bstep (se 2 (by rfl) ⟨2225967, by rfl⟩ : syracuseStep 5935913 = 4451935) B4451935
theorem B1561511 : Blo 1561478 1561511 := bstep (se 1 (by rfl) ⟨1171133, by rfl⟩ : syracuseStep 1561511 = 2342267) B2342267
theorem B1561595 : Blo 1561478 1561595 := bstep (se 1 (by rfl) ⟨1171196, by rfl⟩ : syracuseStep 1561595 = 2342393) B2342393
theorem B1561663 : Blo 1561478 1561663 := bstep (se 1 (by rfl) ⟨1171247, by rfl⟩ : syracuseStep 1561663 = 2342495) B2342495
theorem B1758271 : Blo 1561478 1758271 := bstep (se 1 (by rfl) ⟨1318703, by rfl⟩ : syracuseStep 1758271 = 2637407) B2637407
theorem B1561807 : Blo 1561478 1561807 := bstep (se 1 (by rfl) ⟨1171355, by rfl⟩ : syracuseStep 1561807 = 2342711) B2342711
theorem B1758415 : Blo 1561478 1758415 := bstep (se 1 (by rfl) ⟨1318811, by rfl⟩ : syracuseStep 1758415 = 2637623) B2637623
theorem B1562011 : Blo 1561478 1562011 := bstep (se 1 (by rfl) ⟨1171508, by rfl⟩ : syracuseStep 1562011 = 2343017) B2343017
theorem B8893961 : Blo 1561478 8893961 := bstep (se 2 (by rfl) ⟨3335235, by rfl⟩ : syracuseStep 8893961 = 6670471) B6670471
theorem B2635375 : Blo 1561478 2635375 := bstep (se 1 (by rfl) ⟨1976531, by rfl⟩ : syracuseStep 2635375 = 3953063) B3953063
theorem B1562223 : Blo 1561478 1562223 := bstep (se 1 (by rfl) ⟨1171667, by rfl⟩ : syracuseStep 1562223 = 2343335) B2343335
theorem B1562279 : Blo 1561478 1562279 := bstep (se 1 (by rfl) ⟨1171709, by rfl⟩ : syracuseStep 1562279 = 2343419) B2343419
theorem B3954359 : Blo 1561478 3954359 := bstep (se 1 (by rfl) ⟨2965769, by rfl⟩ : syracuseStep 3954359 = 5931539) B5931539
theorem B2635483 : Blo 1561478 2635483 := bstep (se 1 (by rfl) ⟨1976612, by rfl⟩ : syracuseStep 2635483 = 3953225) B3953225
theorem B1562363 : Blo 1561478 1562363 := bstep (se 1 (by rfl) ⟨1171772, by rfl⟩ : syracuseStep 1562363 = 2343545) B2343545
theorem B1562399 : Blo 1561478 1562399 := bstep (se 1 (by rfl) ⟨1171799, by rfl⟩ : syracuseStep 1562399 = 2343599) B2343599
theorem B8902457 : Blo 1561478 8902457 := bstep (se 2 (by rfl) ⟨3338421, by rfl⟩ : syracuseStep 8902457 = 6676843) B6676843
theorem B1562431 : Blo 1561478 1562431 := bstep (se 1 (by rfl) ⟨1171823, by rfl⟩ : syracuseStep 1562431 = 2343647) B2343647
theorem B1562607 : Blo 1561478 1562607 := bstep (se 1 (by rfl) ⟨1171955, by rfl⟩ : syracuseStep 1562607 = 2343911) B2343911
theorem B1562779 : Blo 1561478 1562779 := bstep (se 1 (by rfl) ⟨1172084, by rfl⟩ : syracuseStep 1562779 = 2344169) B2344169
theorem B1562815 : Blo 1561478 1562815 := bstep (se 1 (by rfl) ⟨1172111, by rfl⟩ : syracuseStep 1562815 = 2344223) B2344223
theorem B5347561 : Blo 1561478 5347561 := bstep (se 2 (by rfl) ⟨2005335, by rfl⟩ : syracuseStep 5347561 = 4010671) B4010671
theorem B5003507 : Blo 1561478 5003507 := bstep (se 1 (by rfl) ⟨3752630, by rfl⟩ : syracuseStep 5003507 = 7505261) B7505261
theorem B1562927 : Blo 1561478 1562927 := bstep (se 1 (by rfl) ⟨1172195, by rfl⟩ : syracuseStep 1562927 = 2344391) B2344391
theorem B2005295 : Blo 1561478 2005295 := bstep (se 1 (by rfl) ⟨1503971, by rfl⟩ : syracuseStep 2005295 = 3007943) B3007943
theorem B5273963 : Blo 1561478 5273963 := bstep (se 1 (by rfl) ⟨3955472, by rfl⟩ : syracuseStep 5273963 = 7910945) B7910945
theorem B8894893 : Blo 1561478 8894893 := bstep (se 3 (by rfl) ⟨1667792, by rfl⟩ : syracuseStep 8894893 = 3335585) B3335585
theorem B11868605 : Blo 1561478 11868605 := bstep (se 3 (by rfl) ⟨2225363, by rfl⟩ : syracuseStep 11868605 = 4450727) B4450727
theorem B8903141 : Blo 1561478 8903141 := bstep (se 4 (by rfl) ⟨834669, by rfl⟩ : syracuseStep 8903141 = 1669339) B1669339
theorem B1563163 : Blo 1561478 1563163 := bstep (se 1 (by rfl) ⟨1172372, by rfl⟩ : syracuseStep 1563163 = 2344745) B2344745
theorem B1563167 : Blo 1561478 1563167 := bstep (se 1 (by rfl) ⟨1172375, by rfl⟩ : syracuseStep 1563167 = 2344751) B2344751
theorem B5274233 : Blo 1561478 5274233 := bstep (se 2 (by rfl) ⟨1977837, by rfl⟩ : syracuseStep 5274233 = 3955675) B3955675
theorem B5929625 : Blo 1561478 5929625 := bstep (se 2 (by rfl) ⟨2223609, by rfl⟩ : syracuseStep 5929625 = 4447219) B4447219
theorem B5929807 : Blo 1561478 5929807 := bstep (se 1 (by rfl) ⟨4447355, by rfl⟩ : syracuseStep 5929807 = 8894711) B8894711
theorem B2636779 : Blo 1561478 2636779 := bstep (se 1 (by rfl) ⟨1977584, by rfl⟩ : syracuseStep 2636779 = 3955169) B3955169
theorem B5274665 : Blo 1561478 5274665 := bstep (se 2 (by rfl) ⟨1977999, by rfl⟩ : syracuseStep 5274665 = 3955999) B3955999
theorem B2636921 : Blo 1561478 2636921 := bstep (se 2 (by rfl) ⟨988845, by rfl⟩ : syracuseStep 2636921 = 1977691) B1977691
theorem B3513527 : Blo 1561478 3513527 := bstep (se 1 (by rfl) ⟨2635145, by rfl⟩ : syracuseStep 3513527 = 5270291) B5270291
theorem B9501961 : Blo 1561478 9501961 := bstep (se 2 (by rfl) ⟨3563235, by rfl⟩ : syracuseStep 9501961 = 7126471) B7126471
theorem B5930279 : Blo 1561478 5930279 := bstep (se 1 (by rfl) ⟨4447709, by rfl⟩ : syracuseStep 5930279 = 8895419) B8895419
theorem B2342255 : Blo 1561478 2342255 := bstep (se 1 (by rfl) ⟨1756691, by rfl⟩ : syracuseStep 2342255 = 3513383) B3513383
theorem B2342375 : Blo 1561478 2342375 := bstep (se 1 (by rfl) ⟨1756781, by rfl⟩ : syracuseStep 2342375 = 3513563) B3513563
theorem B8904167 : Blo 1561478 8904167 := bstep (se 1 (by rfl) ⟨6678125, by rfl⟩ : syracuseStep 8904167 = 13356251) B13356251
theorem B8019535 : Blo 1561478 8019535 := bstep (se 1 (by rfl) ⟨6014651, by rfl⟩ : syracuseStep 8019535 = 12029303) B12029303
theorem B3956303 : Blo 1561478 3956303 := bstep (se 1 (by rfl) ⟨2967227, by rfl⟩ : syracuseStep 3956303 = 5934455) B5934455
theorem B4447835 : Blo 1561478 4447835 := bstep (se 1 (by rfl) ⟨3335876, by rfl⟩ : syracuseStep 4447835 = 6671753) B6671753
theorem B5709403 : Blo 1561478 5709403 := bstep (se 1 (by rfl) ⟨4282052, by rfl⟩ : syracuseStep 5709403 = 8564105) B8564105
theorem B7913051 : Blo 1561478 7913051 := bstep (se 1 (by rfl) ⟨5934788, by rfl⟩ : syracuseStep 7913051 = 11869577) B11869577
theorem B2342507 : Blo 1561478 2342507 := bstep (se 1 (by rfl) ⟨1756880, by rfl⟩ : syracuseStep 2342507 = 3513761) B3513761
theorem B6012559 : Blo 1561478 6012559 := bstep (se 1 (by rfl) ⟨4509419, by rfl⟩ : syracuseStep 6012559 = 9018839) B9018839
theorem B16891591 : Blo 1561478 16891591 := bstep (se 1 (by rfl) ⟨12668693, by rfl⟩ : syracuseStep 16891591 = 25337387) B25337387
theorem B2342633 : Blo 1561478 2342633 := bstep (se 2 (by rfl) ⟨878487, by rfl⟩ : syracuseStep 2342633 = 1756975) B1756975
theorem B3514103 : Blo 1561478 3514103 := bstep (se 1 (by rfl) ⟨2635577, by rfl⟩ : syracuseStep 3514103 = 5271155) B5271155
theorem B2342777 : Blo 1561478 2342777 := bstep (se 2 (by rfl) ⟨878541, by rfl⟩ : syracuseStep 2342777 = 1757083) B1757083
theorem B3514283 : Blo 1561478 3514283 := bstep (se 1 (by rfl) ⟨2635712, by rfl⟩ : syracuseStep 3514283 = 5271425) B5271425
theorem B2342879 : Blo 1561478 2342879 := bstep (se 1 (by rfl) ⟨1757159, by rfl⟩ : syracuseStep 2342879 = 3514319) B3514319
theorem B2375915 : Blo 1561478 2375915 := bstep (se 1 (by rfl) ⟨1781936, by rfl⟩ : syracuseStep 2375915 = 3563873) B3563873
theorem B11862287 : Blo 1561478 11862287 := bstep (se 1 (by rfl) ⟨8896715, by rfl⟩ : syracuseStep 11862287 = 17793431) B17793431
theorem B2343215 : Blo 1561478 2343215 := bstep (se 1 (by rfl) ⟨1757411, by rfl⟩ : syracuseStep 2343215 = 3514823) B3514823
theorem B3514679 : Blo 1561478 3514679 := bstep (se 1 (by rfl) ⟨2636009, by rfl⟩ : syracuseStep 3514679 = 5272019) B5272019
theorem B45031787 : Blo 1561478 45031787 := bstep (se 1 (by rfl) ⟨33773840, by rfl⟩ : syracuseStep 45031787 = 67547681) B67547681
theorem B5276015 : Blo 1561478 5276015 := bstep (se 1 (by rfl) ⟨3957011, by rfl⟩ : syracuseStep 5276015 = 7914023) B7914023
theorem B3957275 : Blo 1561478 3957275 := bstep (se 1 (by rfl) ⟨2967956, by rfl⟩ : syracuseStep 3957275 = 5935913) B5935913
theorem B2343455 : Blo 1561478 2343455 := bstep (se 1 (by rfl) ⟨1757591, by rfl⟩ : syracuseStep 2343455 = 3515183) B3515183
theorem B20022227 : Blo 1561478 20022227 := bstep (se 1 (by rfl) ⟨15016670, by rfl⟩ : syracuseStep 20022227 = 30033341) B30033341
theorem B7906409 : Blo 1561478 7906409 := bstep (se 2 (by rfl) ⟨2964903, by rfl⟩ : syracuseStep 7906409 = 5929807) B5929807
theorem B2966635 : Blo 1561478 2966635 := bstep (se 1 (by rfl) ⟨2224976, by rfl⟩ : syracuseStep 2966635 = 4449953) B4449953
theorem B7914671 : Blo 1561478 7914671 := bstep (se 1 (by rfl) ⟨5936003, by rfl⟩ : syracuseStep 7914671 = 11872007) B11872007
theorem B2966719 : Blo 1561478 2966719 := bstep (se 1 (by rfl) ⟨2225039, by rfl⟩ : syracuseStep 2966719 = 4450079) B4450079
theorem B2344127 : Blo 1561478 2344127 := bstep (se 1 (by rfl) ⟨1758095, by rfl⟩ : syracuseStep 2344127 = 3516191) B3516191
theorem B3515705 : Blo 1561478 3515705 := bstep (se 2 (by rfl) ⟨1318389, by rfl⟩ : syracuseStep 3515705 = 2636779) B2636779
theorem B2966863 : Blo 1561478 2966863 := bstep (se 1 (by rfl) ⟨2225147, by rfl⟩ : syracuseStep 2966863 = 4450295) B4450295
theorem B2344271 : Blo 1561478 2344271 := bstep (se 1 (by rfl) ⟨1758203, by rfl⟩ : syracuseStep 2344271 = 3516407) B3516407
theorem B2344361 : Blo 1561478 2344361 := bstep (se 2 (by rfl) ⟨879135, by rfl⟩ : syracuseStep 2344361 = 1758271) B1758271
theorem B192374261 : Blo 1561478 192374261 := bstep (se 5 (by rfl) ⟨9017543, by rfl⟩ : syracuseStep 192374261 = 18035087) B18035087
theorem B3335671 : Blo 1561478 3335671 := bstep (se 1 (by rfl) ⟨2501753, by rfl⟩ : syracuseStep 3335671 = 5003507) B5003507
theorem B2344511 : Blo 1561478 2344511 := bstep (se 1 (by rfl) ⟨1758383, by rfl⟩ : syracuseStep 2344511 = 3516767) B3516767
theorem B3515975 : Blo 1561478 3515975 := bstep (se 1 (by rfl) ⟨2636981, by rfl⟩ : syracuseStep 3515975 = 5273963) B5273963
theorem B2344553 : Blo 1561478 2344553 := bstep (se 2 (by rfl) ⟨879207, by rfl⟩ : syracuseStep 2344553 = 1758415) B1758415
theorem B3516155 : Blo 1561478 3516155 := bstep (se 1 (by rfl) ⟨2637116, by rfl⟩ : syracuseStep 3516155 = 5274233) B5274233
theorem B8128457 : Blo 1561478 8128457 := bstep (se 2 (by rfl) ⟨3048171, by rfl⟩ : syracuseStep 8128457 = 6096343) B6096343
theorem B3516443 : Blo 1561478 3516443 := bstep (se 1 (by rfl) ⟨2637332, by rfl⟩ : syracuseStep 3516443 = 5274665) B5274665
theorem B2344991 : Blo 1561478 2344991 := bstep (se 1 (by rfl) ⟨1758743, by rfl⟩ : syracuseStep 2344991 = 3517487) B3517487
theorem B10692713 : Blo 1561478 10692713 := bstep (se 2 (by rfl) ⟨4009767, by rfl⟩ : syracuseStep 10692713 = 8019535) B8019535
theorem B7612537 : Blo 1561478 7612537 := bstep (se 2 (by rfl) ⟨2854701, by rfl⟩ : syracuseStep 7612537 = 5709403) B5709403
theorem B2345183 : Blo 1561478 2345183 := bstep (se 1 (by rfl) ⟨1758887, by rfl⟩ : syracuseStep 2345183 = 3517775) B3517775
theorem B22522121 : Blo 1561478 22522121 := bstep (se 2 (by rfl) ⟨8445795, by rfl⟩ : syracuseStep 22522121 = 16891591) B16891591
theorem B2967835 : Blo 1561478 2967835 := bstep (se 1 (by rfl) ⟨2225876, by rfl⟩ : syracuseStep 2967835 = 4451753) B4451753
theorem B11413885 : Blo 1561478 11413885 := bstep (se 3 (by rfl) ⟨2140103, by rfl⟩ : syracuseStep 11413885 = 4280207) B4280207
theorem B13347503 : Blo 1561478 13347503 := bstep (se 1 (by rfl) ⟨10010627, by rfl⟩ : syracuseStep 13347503 = 20021255) B20021255
theorem B1977311 : Blo 1561478 1977311 := bstep (se 1 (by rfl) ⟨1482983, by rfl⟩ : syracuseStep 1977311 = 2965967) B2965967
theorem B7130081 : Blo 1561478 7130081 := bstep (se 2 (by rfl) ⟨2673780, by rfl⟩ : syracuseStep 7130081 = 5347561) B5347561
theorem B16903529 : Blo 1561478 16903529 := bstep (se 2 (by rfl) ⟨6338823, by rfl⟩ : syracuseStep 16903529 = 12677647) B12677647
theorem B72183599 : Blo 1561478 72183599 := bstep (se 1 (by rfl) ⟨54137699, by rfl⟩ : syracuseStep 72183599 = 108275399) B108275399
theorem B10006345 : Blo 1561478 10006345 := bstep (se 2 (by rfl) ⟨3752379, by rfl⟩ : syracuseStep 10006345 = 7504759) B7504759
theorem B5934971 : Blo 1561478 5934971 := bstep (se 1 (by rfl) ⟨4451228, by rfl⟩ : syracuseStep 5934971 = 8902457) B8902457
theorem B5271695 : Blo 1561478 5271695 := bstep (se 1 (by rfl) ⟨3953771, by rfl⟩ : syracuseStep 5271695 = 7907543) B7907543
theorem B2502919 : Blo 1561478 2502919 := bstep (se 1 (by rfl) ⟨1877189, by rfl⟩ : syracuseStep 2502919 = 3754379) B3754379
theorem B5935427 : Blo 1561478 5935427 := bstep (se 1 (by rfl) ⟨4451570, by rfl⟩ : syracuseStep 5935427 = 8903141) B8903141
theorem B12669281 : Blo 1561478 12669281 := bstep (se 2 (by rfl) ⟨4750980, by rfl⟩ : syracuseStep 12669281 = 9501961) B9501961
theorem B5271911 : Blo 1561478 5271911 := bstep (se 1 (by rfl) ⟨3953933, by rfl⟩ : syracuseStep 5271911 = 7907867) B7907867
theorem B9498991 : Blo 1561478 9498991 := bstep (se 1 (by rfl) ⟨7124243, by rfl⟩ : syracuseStep 9498991 = 14248487) B14248487
theorem B2503067 : Blo 1561478 2503067 := bstep (se 1 (by rfl) ⟨1877300, by rfl⟩ : syracuseStep 2503067 = 3754601) B3754601
theorem B3953083 : Blo 1561478 3953083 := bstep (se 1 (by rfl) ⟨2964812, by rfl⟩ : syracuseStep 3953083 = 5929625) B5929625
theorem B3338695 : Blo 1561478 3338695 := bstep (se 1 (by rfl) ⟨2504021, by rfl⟩ : syracuseStep 3338695 = 5008043) B5008043
theorem B11268791 : Blo 1561478 11268791 := bstep (se 1 (by rfl) ⟨8451593, by rfl⟩ : syracuseStep 11268791 = 16903187) B16903187
theorem B1757947 : Blo 1561478 1757947 := bstep (se 1 (by rfl) ⟨1318460, by rfl⟩ : syracuseStep 1757947 = 2636921) B2636921
theorem B3339071 : Blo 1561478 3339071 := bstep (se 1 (by rfl) ⟨2504303, by rfl⟩ : syracuseStep 3339071 = 5008607) B5008607
theorem B8016745 : Blo 1561478 8016745 := bstep (se 2 (by rfl) ⟨3006279, by rfl⟩ : syracuseStep 8016745 = 6012559) B6012559
theorem B3953519 : Blo 1561478 3953519 := bstep (se 1 (by rfl) ⟨2965139, by rfl⟩ : syracuseStep 3953519 = 5930279) B5930279
theorem B1561503 : Blo 1561478 1561503 := bstep (se 1 (by rfl) ⟨1171127, by rfl⟩ : syracuseStep 1561503 = 2342255) B2342255
theorem B1561583 : Blo 1561478 1561583 := bstep (se 1 (by rfl) ⟨1171187, by rfl⟩ : syracuseStep 1561583 = 2342375) B2342375
theorem B5936111 : Blo 1561478 5936111 := bstep (se 1 (by rfl) ⟨4452083, by rfl⟩ : syracuseStep 5936111 = 8904167) B8904167
theorem B8893435 : Blo 1561478 8893435 := bstep (se 1 (by rfl) ⟨6670076, by rfl⟩ : syracuseStep 8893435 = 13340153) B13340153
theorem B1561671 : Blo 1561478 1561671 := bstep (se 1 (by rfl) ⟨1171253, by rfl⟩ : syracuseStep 1561671 = 2342507) B2342507
theorem B1561755 : Blo 1561478 1561755 := bstep (se 1 (by rfl) ⟨1171316, by rfl⟩ : syracuseStep 1561755 = 2342633) B2342633
theorem B7910621 : Blo 1561478 7910621 := bstep (se 3 (by rfl) ⟨1483241, by rfl⟩ : syracuseStep 7910621 = 2966483) B2966483
theorem B1561851 : Blo 1561478 1561851 := bstep (se 1 (by rfl) ⟨1171388, by rfl⟩ : syracuseStep 1561851 = 2342777) B2342777
theorem B1561919 : Blo 1561478 1561919 := bstep (se 1 (by rfl) ⟨1171439, by rfl⟩ : syracuseStep 1561919 = 2342879) B2342879
theorem B26703269 : Blo 1561478 26703269 := bstep (se 4 (by rfl) ⟨2503431, by rfl⟩ : syracuseStep 26703269 = 5006863) B5006863
theorem B1562087 : Blo 1561478 1562087 := bstep (se 1 (by rfl) ⟨1171565, by rfl⟩ : syracuseStep 1562087 = 2343131) B2343131
theorem B1562095 : Blo 1561478 1562095 := bstep (se 1 (by rfl) ⟨1171571, by rfl⟩ : syracuseStep 1562095 = 2343143) B2343143
theorem B1758703 : Blo 1561478 1758703 := bstep (se 1 (by rfl) ⟨1319027, by rfl⟩ : syracuseStep 1758703 = 2638055) B2638055
theorem B2635355 : Blo 1561478 2635355 := bstep (se 1 (by rfl) ⟨1976516, by rfl⟩ : syracuseStep 2635355 = 3953033) B3953033
theorem B1562203 : Blo 1561478 1562203 := bstep (se 1 (by rfl) ⟨1171652, by rfl⟩ : syracuseStep 1562203 = 2343305) B2343305
theorem B1758811 : Blo 1561478 1758811 := bstep (se 1 (by rfl) ⟨1319108, by rfl⟩ : syracuseStep 1758811 = 2638217) B2638217
theorem B1562267 : Blo 1561478 1562267 := bstep (se 1 (by rfl) ⟨1171700, by rfl⟩ : syracuseStep 1562267 = 2343401) B2343401
theorem B7124719 : Blo 1561478 7124719 := bstep (se 1 (by rfl) ⟨5343539, by rfl⟩ : syracuseStep 7124719 = 10687079) B10687079
theorem B1562351 : Blo 1561478 1562351 := bstep (se 1 (by rfl) ⟨1171763, by rfl⟩ : syracuseStep 1562351 = 2343527) B2343527
theorem B6420235 : Blo 1561478 6420235 := bstep (se 1 (by rfl) ⟨4815176, by rfl⟩ : syracuseStep 6420235 = 9630353) B9630353
theorem B1562439 : Blo 1561478 1562439 := bstep (se 1 (by rfl) ⟨1171829, by rfl⟩ : syracuseStep 1562439 = 2343659) B2343659
theorem B5273423 : Blo 1561478 5273423 := bstep (se 1 (by rfl) ⟨3955067, by rfl⟩ : syracuseStep 5273423 = 7910135) B7910135
theorem B1562459 : Blo 1561478 1562459 := bstep (se 1 (by rfl) ⟨1171844, by rfl⟩ : syracuseStep 1562459 = 2343689) B2343689
theorem B11859857 : Blo 1561478 11859857 := bstep (se 2 (by rfl) ⟨4447446, by rfl⟩ : syracuseStep 11859857 = 8894893) B8894893
theorem B1562527 : Blo 1561478 1562527 := bstep (se 1 (by rfl) ⟨1171895, by rfl⟩ : syracuseStep 1562527 = 2343791) B2343791
theorem B1562695 : Blo 1561478 1562695 := bstep (se 1 (by rfl) ⟨1172021, by rfl⟩ : syracuseStep 1562695 = 2344043) B2344043
theorem B16898129 : Blo 1561478 16898129 := bstep (se 2 (by rfl) ⟨6336798, by rfl⟩ : syracuseStep 16898129 = 12673597) B12673597
theorem B5347453 : Blo 1561478 5347453 := bstep (se 3 (by rfl) ⟨1002647, by rfl⟩ : syracuseStep 5347453 = 2005295) B2005295
theorem B1562855 : Blo 1561478 1562855 := bstep (se 1 (by rfl) ⟨1172141, by rfl⟩ : syracuseStep 1562855 = 2344283) B2344283
theorem B3955027 : Blo 1561478 3955027 := bstep (se 1 (by rfl) ⟨2966270, by rfl⟩ : syracuseStep 3955027 = 5932541) B5932541
theorem B5929307 : Blo 1561478 5929307 := bstep (se 1 (by rfl) ⟨4446980, by rfl⟩ : syracuseStep 5929307 = 8893961) B8893961
theorem B32086367 : Blo 1561478 32086367 := bstep (se 1 (by rfl) ⟨24064775, by rfl⟩ : syracuseStep 32086367 = 48129551) B48129551
theorem B1563039 : Blo 1561478 1563039 := bstep (se 1 (by rfl) ⟨1172279, by rfl⟩ : syracuseStep 1563039 = 2344559) B2344559
theorem B2636239 : Blo 1561478 2636239 := bstep (se 1 (by rfl) ⟨1977179, by rfl⟩ : syracuseStep 2636239 = 3954359) B3954359
theorem B1563087 : Blo 1561478 1563087 := bstep (se 1 (by rfl) ⟨1172315, by rfl⟩ : syracuseStep 1563087 = 2344631) B2344631
theorem B1563111 : Blo 1561478 1563111 := bstep (se 1 (by rfl) ⟨1172333, by rfl⟩ : syracuseStep 1563111 = 2344667) B2344667
theorem B1563227 : Blo 1561478 1563227 := bstep (se 1 (by rfl) ⟨1172420, by rfl⟩ : syracuseStep 1563227 = 2344841) B2344841
theorem B1563295 : Blo 1561478 1563295 := bstep (se 1 (by rfl) ⟨1172471, by rfl⟩ : syracuseStep 1563295 = 2344943) B2344943
theorem B75979457 : Blo 1561478 75979457 := bstep (se 2 (by rfl) ⟨28492296, by rfl⟩ : syracuseStep 75979457 = 56984593) B56984593
theorem B1563463 : Blo 1561478 1563463 := bstep (se 1 (by rfl) ⟨1172597, by rfl⟩ : syracuseStep 1563463 = 2345195) B2345195
theorem B7912403 : Blo 1561478 7912403 := bstep (se 1 (by rfl) ⟨5934302, by rfl⟩ : syracuseStep 7912403 = 11868605) B11868605
theorem B5004251 : Blo 1561478 5004251 := bstep (se 1 (by rfl) ⟨3753188, by rfl⟩ : syracuseStep 5004251 = 7506377) B7506377
theorem B3513671 : Blo 1561478 3513671 := bstep (se 1 (by rfl) ⟨2635253, by rfl⟩ : syracuseStep 3513671 = 5270507) B5270507
theorem B178134367 : Blo 1561478 178134367 := bstep (se 1 (by rfl) ⟨133600775, by rfl⟩ : syracuseStep 178134367 = 267201551) B267201551
theorem B3513707 : Blo 1561478 3513707 := bstep (se 1 (by rfl) ⟨2635280, by rfl⟩ : syracuseStep 3513707 = 5270561) B5270561
theorem B12672395 : Blo 1561478 12672395 := bstep (se 1 (by rfl) ⟨9504296, by rfl⟩ : syracuseStep 12672395 = 19008593) B19008593
theorem B2342351 : Blo 1561478 2342351 := bstep (se 1 (by rfl) ⟨1756763, by rfl⟩ : syracuseStep 2342351 = 3513527) B3513527
theorem B3513833 : Blo 1561478 3513833 := bstep (se 2 (by rfl) ⟨1317687, by rfl⟩ : syracuseStep 3513833 = 2635375) B2635375
theorem B3513977 : Blo 1561478 3513977 := bstep (se 2 (by rfl) ⟨1317741, by rfl⟩ : syracuseStep 3513977 = 2635483) B2635483
theorem B2637535 : Blo 1561478 2637535 := bstep (se 1 (by rfl) ⟨1978151, by rfl⟩ : syracuseStep 2637535 = 3956303) B3956303
theorem B2965223 : Blo 1561478 2965223 := bstep (se 1 (by rfl) ⟨2223917, by rfl⟩ : syracuseStep 2965223 = 4447835) B4447835
theorem B5275367 : Blo 1561478 5275367 := bstep (se 1 (by rfl) ⟨3956525, by rfl⟩ : syracuseStep 5275367 = 7913051) B7913051
theorem B2342735 : Blo 1561478 2342735 := bstep (se 1 (by rfl) ⟨1757051, by rfl⟩ : syracuseStep 2342735 = 3514103) B3514103
theorem B2342855 : Blo 1561478 2342855 := bstep (se 1 (by rfl) ⟨1757141, by rfl⟩ : syracuseStep 2342855 = 3514283) B3514283
theorem B3514463 : Blo 1561478 3514463 := bstep (se 1 (by rfl) ⟨2635847, by rfl⟩ : syracuseStep 3514463 = 5271695) B5271695
theorem B10150049 : Blo 1561478 10150049 := bstep (se 2 (by rfl) ⟨3806268, by rfl⟩ : syracuseStep 10150049 = 7612537) B7612537
theorem B2343119 : Blo 1561478 2343119 := bstep (se 1 (by rfl) ⟨1757339, by rfl⟩ : syracuseStep 2343119 = 3514679) B3514679
theorem B3956951 : Blo 1561478 3956951 := bstep (se 1 (by rfl) ⟨2967713, by rfl⟩ : syracuseStep 3956951 = 5935427) B5935427
theorem B8446187 : Blo 1561478 8446187 := bstep (se 1 (by rfl) ⟨6334640, by rfl⟩ : syracuseStep 8446187 = 12669281) B12669281
theorem B3514607 : Blo 1561478 3514607 := bstep (se 1 (by rfl) ⟨2635955, by rfl⟩ : syracuseStep 3514607 = 5271911) B5271911
theorem B2638183 : Blo 1561478 2638183 := bstep (se 1 (by rfl) ⟨1978637, by rfl⟩ : syracuseStep 2638183 = 3957275) B3957275
theorem B3957113 : Blo 1561478 3957113 := bstep (se 2 (by rfl) ⟨1483917, by rfl⟩ : syracuseStep 3957113 = 2967835) B2967835
theorem B7512527 : Blo 1561478 7512527 := bstep (se 1 (by rfl) ⟨5634395, by rfl⟩ : syracuseStep 7512527 = 11268791) B11268791
theorem B12665321 : Blo 1561478 12665321 := bstep (se 2 (by rfl) ⟨4749495, by rfl⟩ : syracuseStep 12665321 = 9498991) B9498991
theorem B3514985 : Blo 1561478 3514985 := bstep (se 2 (by rfl) ⟨1318119, by rfl⟩ : syracuseStep 3514985 = 2636239) B2636239
theorem B3957407 : Blo 1561478 3957407 := bstep (se 1 (by rfl) ⟨2968055, by rfl⟩ : syracuseStep 3957407 = 5936111) B5936111
theorem B5276447 : Blo 1561478 5276447 := bstep (se 1 (by rfl) ⟨3957335, by rfl⟩ : syracuseStep 5276447 = 7914671) B7914671
theorem B2343803 : Blo 1561478 2343803 := bstep (se 1 (by rfl) ⟨1757852, by rfl⟩ : syracuseStep 2343803 = 3515705) B3515705
theorem B17802179 : Blo 1561478 17802179 := bstep (se 1 (by rfl) ⟨13351634, by rfl⟩ : syracuseStep 17802179 = 26703269) B26703269
theorem B2343929 : Blo 1561478 2343929 := bstep (se 2 (by rfl) ⟨878973, by rfl⟩ : syracuseStep 2343929 = 1757947) B1757947
theorem B2343983 : Blo 1561478 2343983 := bstep (se 1 (by rfl) ⟨1757987, by rfl⟩ : syracuseStep 2343983 = 3515975) B3515975
theorem B2344103 : Blo 1561478 2344103 := bstep (se 1 (by rfl) ⟨1758077, by rfl⟩ : syracuseStep 2344103 = 3516155) B3516155
theorem B3515615 : Blo 1561478 3515615 := bstep (se 1 (by rfl) ⟨2636711, by rfl⟩ : syracuseStep 3515615 = 5273423) B5273423
theorem B7906571 : Blo 1561478 7906571 := bstep (se 1 (by rfl) ⟨5929928, by rfl⟩ : syracuseStep 7906571 = 11859857) B11859857
theorem B2344295 : Blo 1561478 2344295 := bstep (se 1 (by rfl) ⟨1758221, by rfl⟩ : syracuseStep 2344295 = 3516443) B3516443
theorem B11265419 : Blo 1561478 11265419 := bstep (se 1 (by rfl) ⟨8449064, by rfl⟩ : syracuseStep 11265419 = 16898129) B16898129
theorem B21390911 : Blo 1561478 21390911 := bstep (se 1 (by rfl) ⟨16043183, by rfl⟩ : syracuseStep 21390911 = 32086367) B32086367
theorem B8898335 : Blo 1561478 8898335 := bstep (se 1 (by rfl) ⟨6673751, by rfl⟩ : syracuseStep 8898335 = 13347503) B13347503
theorem B50652971 : Blo 1561478 50652971 := bstep (se 1 (by rfl) ⟨37989728, by rfl⟩ : syracuseStep 50652971 = 75979457) B75979457
theorem B3336167 : Blo 1561478 3336167 := bstep (se 1 (by rfl) ⟨2502125, by rfl⟩ : syracuseStep 3336167 = 5004251) B5004251
theorem B2344937 : Blo 1561478 2344937 := bstep (se 2 (by rfl) ⟨879351, by rfl⟩ : syracuseStep 2344937 = 1758703) B1758703
theorem B4753387 : Blo 1561478 4753387 := bstep (se 1 (by rfl) ⟨3565040, by rfl⟩ : syracuseStep 4753387 = 7130081) B7130081
theorem B2345081 : Blo 1561478 2345081 := bstep (se 2 (by rfl) ⟨879405, by rfl⟩ : syracuseStep 2345081 = 1758811) B1758811
theorem B8448263 : Blo 1561478 8448263 := bstep (se 1 (by rfl) ⟨6336197, by rfl⟩ : syracuseStep 8448263 = 12672395) B12672395
theorem B3516713 : Blo 1561478 3516713 := bstep (se 2 (by rfl) ⟨1318767, by rfl⟩ : syracuseStep 3516713 = 2637535) B2637535
theorem B1976815 : Blo 1561478 1976815 := bstep (se 1 (by rfl) ⟨1482611, by rfl⟩ : syracuseStep 1976815 = 2965223) B2965223
theorem B3516911 : Blo 1561478 3516911 := bstep (se 1 (by rfl) ⟨2637683, by rfl⟩ : syracuseStep 3516911 = 5275367) B5275367
theorem B48122399 : Blo 1561478 48122399 := bstep (se 1 (by rfl) ⟨36091799, by rfl⟩ : syracuseStep 48122399 = 72183599) B72183599
theorem B7129937 : Blo 1561478 7129937 := bstep (se 2 (by rfl) ⟨2673726, by rfl⟩ : syracuseStep 7129937 = 5347453) B5347453
theorem B7908191 : Blo 1561478 7908191 := bstep (se 1 (by rfl) ⟨5931143, by rfl⟩ : syracuseStep 7908191 = 11862287) B11862287
theorem B3517343 : Blo 1561478 3517343 := bstep (se 1 (by rfl) ⟨2638007, by rfl⟩ : syracuseStep 3517343 = 5276015) B5276015
theorem B5270777 : Blo 1561478 5270777 := bstep (se 2 (by rfl) ⟨1976541, by rfl⟩ : syracuseStep 5270777 = 3953083) B3953083
theorem B4451593 : Blo 1561478 4451593 := bstep (se 2 (by rfl) ⟨1669347, by rfl⟩ : syracuseStep 4451593 = 3338695) B3338695
theorem B13348151 : Blo 1561478 13348151 := bstep (se 1 (by rfl) ⟨10011113, by rfl⟩ : syracuseStep 13348151 = 20022227) B20022227
theorem B5270939 : Blo 1561478 5270939 := bstep (se 1 (by rfl) ⟨3953204, by rfl⟩ : syracuseStep 5270939 = 7906409) B7906409
theorem B128249507 : Blo 1561478 128249507 := bstep (se 1 (by rfl) ⟨96187130, by rfl⟩ : syracuseStep 128249507 = 192374261) B192374261
theorem B1756903 : Blo 1561478 1756903 := bstep (se 1 (by rfl) ⟨1317677, by rfl⟩ : syracuseStep 1756903 = 2635355) B2635355
theorem B5418971 : Blo 1561478 5418971 := bstep (se 1 (by rfl) ⟨4064228, by rfl⟩ : syracuseStep 5418971 = 8128457) B8128457
theorem B11857913 : Blo 1561478 11857913 := bstep (se 2 (by rfl) ⟨4446717, by rfl⟩ : syracuseStep 11857913 = 8893435) B8893435
theorem B13348901 : Blo 1561478 13348901 := bstep (se 4 (by rfl) ⟨1251459, by rfl⟩ : syracuseStep 13348901 = 2502919) B2502919
theorem B3952871 : Blo 1561478 3952871 := bstep (se 1 (by rfl) ⟨2964653, by rfl⟩ : syracuseStep 3952871 = 5929307) B5929307
theorem B3800199829 : Blo 1561478 3800199829 := bstep (se 6 (by rfl) ⟨89067183, by rfl⟩ : syracuseStep 3800199829 = 178134367) B178134367
theorem B11269019 : Blo 1561478 11269019 := bstep (se 1 (by rfl) ⟨8451764, by rfl⟩ : syracuseStep 11269019 = 16903529) B16903529
theorem B1561567 : Blo 1561478 1561567 := bstep (se 1 (by rfl) ⟨1171175, by rfl⟩ : syracuseStep 1561567 = 2342351) B2342351
theorem B9499625 : Blo 1561478 9499625 := bstep (se 2 (by rfl) ⟨3562359, by rfl⟩ : syracuseStep 9499625 = 7124719) B7124719
theorem B13341793 : Blo 1561478 13341793 := bstep (se 2 (by rfl) ⟨5003172, by rfl⟩ : syracuseStep 13341793 = 10006345) B10006345
theorem B25343093 : Blo 1561478 25343093 := bstep (se 5 (by rfl) ⟨1187957, by rfl⟩ : syracuseStep 25343093 = 2375915) B2375915
theorem B1561823 : Blo 1561478 1561823 := bstep (se 1 (by rfl) ⟨1171367, by rfl⟩ : syracuseStep 1561823 = 2342735) B2342735
theorem B5272829 : Blo 1561478 5272829 := bstep (se 3 (by rfl) ⟨988655, by rfl⟩ : syracuseStep 5272829 = 1977311) B1977311
theorem B1561903 : Blo 1561478 1561903 := bstep (se 1 (by rfl) ⟨1171427, by rfl⟩ : syracuseStep 1561903 = 2342855) B2342855
theorem B1562143 : Blo 1561478 1562143 := bstep (se 1 (by rfl) ⟨1171607, by rfl⟩ : syracuseStep 1562143 = 2343215) B2343215
theorem B30021191 : Blo 1561478 30021191 := bstep (se 1 (by rfl) ⟨22515893, by rfl⟩ : syracuseStep 30021191 = 45031787) B45031787
theorem B28513901 : Blo 1561478 28513901 := bstep (se 3 (by rfl) ⟨5346356, by rfl⟩ : syracuseStep 28513901 = 10692713) B10692713
theorem B1562303 : Blo 1561478 1562303 := bstep (se 1 (by rfl) ⟨1171727, by rfl⟩ : syracuseStep 1562303 = 2343455) B2343455
theorem B5273369 : Blo 1561478 5273369 := bstep (se 2 (by rfl) ⟨1977513, by rfl⟩ : syracuseStep 5273369 = 3955027) B3955027
theorem B15218513 : Blo 1561478 15218513 := bstep (se 2 (by rfl) ⟨5706942, by rfl⟩ : syracuseStep 15218513 = 11413885) B11413885
theorem B2226047 : Blo 1561478 2226047 := bstep (se 1 (by rfl) ⟨1669535, by rfl⟩ : syracuseStep 2226047 = 3339071) B3339071
theorem B2635679 : Blo 1561478 2635679 := bstep (se 1 (by rfl) ⟨1976759, by rfl⟩ : syracuseStep 2635679 = 3953519) B3953519
theorem B1562751 : Blo 1561478 1562751 := bstep (se 1 (by rfl) ⟨1172063, by rfl⟩ : syracuseStep 1562751 = 2344127) B2344127
theorem B5273747 : Blo 1561478 5273747 := bstep (se 1 (by rfl) ⟨3955310, by rfl⟩ : syracuseStep 5273747 = 7910621) B7910621
theorem B1562847 : Blo 1561478 1562847 := bstep (se 1 (by rfl) ⟨1172135, by rfl⟩ : syracuseStep 1562847 = 2344271) B2344271
theorem B1562907 : Blo 1561478 1562907 := bstep (se 1 (by rfl) ⟨1172180, by rfl⟩ : syracuseStep 1562907 = 2344361) B2344361
theorem B1563007 : Blo 1561478 1563007 := bstep (se 1 (by rfl) ⟨1172255, by rfl⟩ : syracuseStep 1563007 = 2344511) B2344511
theorem B1563035 : Blo 1561478 1563035 := bstep (se 1 (by rfl) ⟨1172276, by rfl⟩ : syracuseStep 1563035 = 2344553) B2344553
theorem B6674845 : Blo 1561478 6674845 := bstep (se 3 (by rfl) ⟨1251533, by rfl⟩ : syracuseStep 6674845 = 2503067) B2503067
theorem B10688993 : Blo 1561478 10688993 := bstep (se 2 (by rfl) ⟨4008372, by rfl⟩ : syracuseStep 10688993 = 8016745) B8016745
theorem B1563327 : Blo 1561478 1563327 := bstep (se 1 (by rfl) ⟨1172495, by rfl⟩ : syracuseStep 1563327 = 2344991) B2344991
theorem B3955513 : Blo 1561478 3955513 := bstep (se 2 (by rfl) ⟨1483317, by rfl⟩ : syracuseStep 3955513 = 2966635) B2966635
theorem B1563455 : Blo 1561478 1563455 := bstep (se 1 (by rfl) ⟨1172591, by rfl⟩ : syracuseStep 1563455 = 2345183) B2345183
theorem B15014747 : Blo 1561478 15014747 := bstep (se 1 (by rfl) ⟨11261060, by rfl⟩ : syracuseStep 15014747 = 22522121) B22522121
theorem B3955625 : Blo 1561478 3955625 := bstep (se 2 (by rfl) ⟨1483359, by rfl⟩ : syracuseStep 3955625 = 2966719) B2966719
theorem B3955817 : Blo 1561478 3955817 := bstep (se 2 (by rfl) ⟨1483431, by rfl⟩ : syracuseStep 3955817 = 2966863) B2966863
theorem B5274935 : Blo 1561478 5274935 := bstep (se 1 (by rfl) ⟨3956201, by rfl⟩ : syracuseStep 5274935 = 7912403) B7912403
theorem B4447561 : Blo 1561478 4447561 := bstep (se 2 (by rfl) ⟨1667835, by rfl⟩ : syracuseStep 4447561 = 3335671) B3335671
theorem B2342447 : Blo 1561478 2342447 := bstep (se 1 (by rfl) ⟨1756835, by rfl⟩ : syracuseStep 2342447 = 3513671) B3513671
theorem B2342471 : Blo 1561478 2342471 := bstep (se 1 (by rfl) ⟨1756853, by rfl⟩ : syracuseStep 2342471 = 3513707) B3513707
theorem B2342555 : Blo 1561478 2342555 := bstep (se 1 (by rfl) ⟨1756916, by rfl⟩ : syracuseStep 2342555 = 3513833) B3513833
theorem B8560313 : Blo 1561478 8560313 := bstep (se 2 (by rfl) ⟨3210117, by rfl⟩ : syracuseStep 8560313 = 6420235) B6420235
theorem B2342651 : Blo 1561478 2342651 := bstep (se 1 (by rfl) ⟨1756988, by rfl⟩ : syracuseStep 2342651 = 3513977) B3513977
theorem B3956647 : Blo 1561478 3956647 := bstep (se 1 (by rfl) ⟨2967485, by rfl⟩ : syracuseStep 3956647 = 5934971) B5934971
theorem B2342975 : Blo 1561478 2342975 := bstep (se 1 (by rfl) ⟨1757231, by rfl⟩ : syracuseStep 2342975 = 3514463) B3514463
theorem B6766699 : Blo 1561478 6766699 := bstep (se 1 (by rfl) ⟨5075024, by rfl⟩ : syracuseStep 6766699 = 10150049) B10150049
theorem B2637967 : Blo 1561478 2637967 := bstep (se 1 (by rfl) ⟨1978475, by rfl⟩ : syracuseStep 2637967 = 3956951) B3956951
theorem B2343071 : Blo 1561478 2343071 := bstep (se 1 (by rfl) ⟨1757303, by rfl⟩ : syracuseStep 2343071 = 3514607) B3514607
theorem B2638075 : Blo 1561478 2638075 := bstep (se 1 (by rfl) ⟨1978556, by rfl⟩ : syracuseStep 2638075 = 3957113) B3957113
theorem B2343323 : Blo 1561478 2343323 := bstep (se 1 (by rfl) ⟨1757492, by rfl⟩ : syracuseStep 2343323 = 3514985) B3514985
theorem B2638271 : Blo 1561478 2638271 := bstep (se 1 (by rfl) ⟨1978703, by rfl⟩ : syracuseStep 2638271 = 3957407) B3957407
theorem B7512679 : Blo 1561478 7512679 := bstep (se 1 (by rfl) ⟨5634509, by rfl⟩ : syracuseStep 7512679 = 11269019) B11269019
theorem B6333083 : Blo 1561478 6333083 := bstep (se 1 (by rfl) ⟨4749812, by rfl⟩ : syracuseStep 6333083 = 9499625) B9499625
theorem B2343743 : Blo 1561478 2343743 := bstep (se 1 (by rfl) ⟨1757807, by rfl⟩ : syracuseStep 2343743 = 3515615) B3515615
theorem B3515219 : Blo 1561478 3515219 := bstep (se 1 (by rfl) ⟨2636414, by rfl⟩ : syracuseStep 3515219 = 5272829) B5272829
theorem B5066933105 : Blo 1561478 5066933105 := bstep (se 2 (by rfl) ⟨1900099914, by rfl⟩ : syracuseStep 5066933105 = 3800199829) B3800199829
theorem B20014127 : Blo 1561478 20014127 := bstep (se 1 (by rfl) ⟨15010595, by rfl⟩ : syracuseStep 20014127 = 30021191) B30021191
theorem B3515579 : Blo 1561478 3515579 := bstep (se 1 (by rfl) ⟨2636684, by rfl⟩ : syracuseStep 3515579 = 5273369) B5273369
theorem B5932223 : Blo 1561478 5932223 := bstep (se 1 (by rfl) ⟨4449167, by rfl⟩ : syracuseStep 5932223 = 8898335) B8898335
theorem B33768647 : Blo 1561478 33768647 := bstep (se 1 (by rfl) ⟨25326485, by rfl⟩ : syracuseStep 33768647 = 50652971) B50652971
theorem B3515831 : Blo 1561478 3515831 := bstep (se 1 (by rfl) ⟨2636873, by rfl⟩ : syracuseStep 3515831 = 5273747) B5273747
theorem B2344475 : Blo 1561478 2344475 := bstep (se 1 (by rfl) ⟨1758356, by rfl⟩ : syracuseStep 2344475 = 3516713) B3516713
theorem B2344607 : Blo 1561478 2344607 := bstep (se 1 (by rfl) ⟨1758455, by rfl⟩ : syracuseStep 2344607 = 3516911) B3516911
theorem B32081599 : Blo 1561478 32081599 := bstep (se 1 (by rfl) ⟨24061199, by rfl⟩ : syracuseStep 32081599 = 48122399) B48122399
theorem B4753291 : Blo 1561478 4753291 := bstep (se 1 (by rfl) ⟨3564968, by rfl⟩ : syracuseStep 4753291 = 7129937) B7129937
theorem B2344895 : Blo 1561478 2344895 := bstep (se 1 (by rfl) ⟨1758671, by rfl⟩ : syracuseStep 2344895 = 3517343) B3517343
theorem B8898767 : Blo 1561478 8898767 := bstep (se 1 (by rfl) ⟨6674075, by rfl⟩ : syracuseStep 8898767 = 13348151) B13348151
theorem B3516623 : Blo 1561478 3516623 := bstep (se 1 (by rfl) ⟨2637467, by rfl⟩ : syracuseStep 3516623 = 5274935) B5274935
theorem B8899267 : Blo 1561478 8899267 := bstep (se 1 (by rfl) ⟨6674450, by rfl⟩ : syracuseStep 8899267 = 13348901) B13348901
theorem B5630791 : Blo 1561478 5630791 := bstep (se 1 (by rfl) ⟨4223093, by rfl⟩ : syracuseStep 5630791 = 8446187) B8446187
theorem B5008351 : Blo 1561478 5008351 := bstep (se 1 (by rfl) ⟨3756263, by rfl⟩ : syracuseStep 5008351 = 7512527) B7512527
theorem B3517577 : Blo 1561478 3517577 := bstep (se 2 (by rfl) ⟨1319091, by rfl⟩ : syracuseStep 3517577 = 2638183) B2638183
theorem B3517631 : Blo 1561478 3517631 := bstep (se 1 (by rfl) ⟨2638223, by rfl⟩ : syracuseStep 3517631 = 5276447) B5276447
theorem B8899793 : Blo 1561478 8899793 := bstep (se 2 (by rfl) ⟨3337422, by rfl⟩ : syracuseStep 8899793 = 6674845) B6674845
theorem B16895395 : Blo 1561478 16895395 := bstep (se 1 (by rfl) ⟨12671546, by rfl⟩ : syracuseStep 16895395 = 25343093) B25343093
theorem B5271047 : Blo 1561478 5271047 := bstep (se 1 (by rfl) ⟨3953285, by rfl⟩ : syracuseStep 5271047 = 7906571) B7906571
theorem B10145675 : Blo 1561478 10145675 := bstep (se 1 (by rfl) ⟨7609256, by rfl⟩ : syracuseStep 10145675 = 15218513) B15218513
theorem B1757119 : Blo 1561478 1757119 := bstep (se 1 (by rfl) ⟨1317839, by rfl⟩ : syracuseStep 1757119 = 2635679) B2635679
theorem B2224111 : Blo 1561478 2224111 := bstep (se 1 (by rfl) ⟨1668083, by rfl⟩ : syracuseStep 2224111 = 3336167) B3336167
theorem B17789057 : Blo 1561478 17789057 := bstep (se 2 (by rfl) ⟨6670896, by rfl⟩ : syracuseStep 17789057 = 13341793) B13341793
theorem B5632175 : Blo 1561478 5632175 := bstep (se 1 (by rfl) ⟨4224131, by rfl⟩ : syracuseStep 5632175 = 8448263) B8448263
theorem B5935457 : Blo 1561478 5935457 := bstep (se 2 (by rfl) ⟨2225796, by rfl⟩ : syracuseStep 5935457 = 4451593) B4451593
theorem B5272127 : Blo 1561478 5272127 := bstep (se 1 (by rfl) ⟨3954095, by rfl⟩ : syracuseStep 5272127 = 7908191) B7908191
theorem B5936125 : Blo 1561478 5936125 := bstep (se 3 (by rfl) ⟨1113023, by rfl⟩ : syracuseStep 5936125 = 2226047) B2226047
theorem B1561631 : Blo 1561478 1561631 := bstep (se 1 (by rfl) ⟨1171223, by rfl⟩ : syracuseStep 1561631 = 2342447) B2342447
theorem B1561647 : Blo 1561478 1561647 := bstep (se 1 (by rfl) ⟨1171235, by rfl⟩ : syracuseStep 1561647 = 2342471) B2342471
theorem B1561703 : Blo 1561478 1561703 := bstep (se 1 (by rfl) ⟨1171277, by rfl⟩ : syracuseStep 1561703 = 2342555) B2342555
theorem B5706875 : Blo 1561478 5706875 := bstep (se 1 (by rfl) ⟨4280156, by rfl⟩ : syracuseStep 5706875 = 8560313) B8560313
theorem B1561767 : Blo 1561478 1561767 := bstep (se 1 (by rfl) ⟨1171325, by rfl⟩ : syracuseStep 1561767 = 2342651) B2342651
theorem B25351397 : Blo 1561478 25351397 := bstep (se 4 (by rfl) ⟨2376693, by rfl⟩ : syracuseStep 25351397 = 4753387) B4753387
theorem B1562079 : Blo 1561478 1562079 := bstep (se 1 (by rfl) ⟨1171559, by rfl⟩ : syracuseStep 1562079 = 2343119) B2343119
theorem B2635247 : Blo 1561478 2635247 := bstep (se 1 (by rfl) ⟨1976435, by rfl⟩ : syracuseStep 2635247 = 3952871) B3952871
theorem B8443547 : Blo 1561478 8443547 := bstep (se 1 (by rfl) ⟨6332660, by rfl⟩ : syracuseStep 8443547 = 12665321) B12665321
theorem B1562535 : Blo 1561478 1562535 := bstep (se 1 (by rfl) ⟨1171901, by rfl⟩ : syracuseStep 1562535 = 2343803) B2343803
theorem B11868119 : Blo 1561478 11868119 := bstep (se 1 (by rfl) ⟨8901089, by rfl⟩ : syracuseStep 11868119 = 17802179) B17802179
theorem B2635753 : Blo 1561478 2635753 := bstep (se 2 (by rfl) ⟨988407, by rfl⟩ : syracuseStep 2635753 = 1976815) B1976815
theorem B1562619 : Blo 1561478 1562619 := bstep (se 1 (by rfl) ⟨1171964, by rfl⟩ : syracuseStep 1562619 = 2343929) B2343929
theorem B1562655 : Blo 1561478 1562655 := bstep (se 1 (by rfl) ⟨1171991, by rfl⟩ : syracuseStep 1562655 = 2343983) B2343983
theorem B1562735 : Blo 1561478 1562735 := bstep (se 1 (by rfl) ⟨1172051, by rfl⟩ : syracuseStep 1562735 = 2344103) B2344103
theorem B1562863 : Blo 1561478 1562863 := bstep (se 1 (by rfl) ⟨1172147, by rfl⟩ : syracuseStep 1562863 = 2344295) B2344295
theorem B7510279 : Blo 1561478 7510279 := bstep (se 1 (by rfl) ⟨5632709, by rfl⟩ : syracuseStep 7510279 = 11265419) B11265419
theorem B14260607 : Blo 1561478 14260607 := bstep (se 1 (by rfl) ⟨10695455, by rfl⟩ : syracuseStep 14260607 = 21390911) B21390911
theorem B5274017 : Blo 1561478 5274017 := bstep (se 2 (by rfl) ⟨1977756, by rfl⟩ : syracuseStep 5274017 = 3955513) B3955513
theorem B1563291 : Blo 1561478 1563291 := bstep (se 1 (by rfl) ⟨1172468, by rfl⟩ : syracuseStep 1563291 = 2344937) B2344937
theorem B1563387 : Blo 1561478 1563387 := bstep (se 1 (by rfl) ⟨1172540, by rfl⟩ : syracuseStep 1563387 = 2345081) B2345081
theorem B76037069 : Blo 1561478 76037069 := bstep (se 3 (by rfl) ⟨14256950, by rfl⟩ : syracuseStep 76037069 = 28513901) B28513901
theorem B7125995 : Blo 1561478 7125995 := bstep (se 1 (by rfl) ⟨5344496, by rfl⟩ : syracuseStep 7125995 = 10688993) B10688993
theorem B5930081 : Blo 1561478 5930081 := bstep (se 2 (by rfl) ⟨2223780, by rfl⟩ : syracuseStep 5930081 = 4447561) B4447561
theorem B10009831 : Blo 1561478 10009831 := bstep (se 1 (by rfl) ⟨7507373, by rfl⟩ : syracuseStep 10009831 = 15014747) B15014747
theorem B2637083 : Blo 1561478 2637083 := bstep (se 1 (by rfl) ⟨1977812, by rfl⟩ : syracuseStep 2637083 = 3955625) B3955625
theorem B2637211 : Blo 1561478 2637211 := bstep (se 1 (by rfl) ⟨1977908, by rfl⟩ : syracuseStep 2637211 = 3955817) B3955817
theorem B3513851 : Blo 1561478 3513851 := bstep (se 1 (by rfl) ⟨2635388, by rfl⟩ : syracuseStep 3513851 = 5270777) B5270777
theorem B3513959 : Blo 1561478 3513959 := bstep (se 1 (by rfl) ⟨2635469, by rfl⟩ : syracuseStep 3513959 = 5270939) B5270939
theorem B2342537 : Blo 1561478 2342537 := bstep (se 2 (by rfl) ⟨878451, by rfl⟩ : syracuseStep 2342537 = 1756903) B1756903
theorem B85499671 : Blo 1561478 85499671 := bstep (se 1 (by rfl) ⟨64124753, by rfl⟩ : syracuseStep 85499671 = 128249507) B128249507
theorem B5275529 : Blo 1561478 5275529 := bstep (se 2 (by rfl) ⟨1978323, by rfl⟩ : syracuseStep 5275529 = 3956647) B3956647
theorem B3612647 : Blo 1561478 3612647 := bstep (se 1 (by rfl) ⟨2709485, by rfl⟩ : syracuseStep 3612647 = 5418971) B5418971
theorem B7905275 : Blo 1561478 7905275 := bstep (se 1 (by rfl) ⟨5928956, by rfl⟩ : syracuseStep 7905275 = 11857913) B11857913
theorem B3956971 : Blo 1561478 3956971 := bstep (se 1 (by rfl) ⟨2967728, by rfl⟩ : syracuseStep 3956971 = 5935457) B5935457
theorem B3514751 : Blo 1561478 3514751 := bstep (se 1 (by rfl) ⟨2636063, by rfl⟩ : syracuseStep 3514751 = 5272127) B5272127
theorem B2343479 : Blo 1561478 2343479 := bstep (se 1 (by rfl) ⟨1757609, by rfl⟩ : syracuseStep 2343479 = 3515219) B3515219
theorem B3377955403 : Blo 1561478 3377955403 := bstep (se 1 (by rfl) ⟨2533466552, by rfl⟩ : syracuseStep 3377955403 = 5066933105) B5066933105
theorem B2343719 : Blo 1561478 2343719 := bstep (se 1 (by rfl) ⟨1757789, by rfl⟩ : syracuseStep 2343719 = 3515579) B3515579
theorem B22512431 : Blo 1561478 22512431 := bstep (se 1 (by rfl) ⟨16884323, by rfl⟩ : syracuseStep 22512431 = 33768647) B33768647
theorem B16900931 : Blo 1561478 16900931 := bstep (se 1 (by rfl) ⟨12675698, by rfl⟩ : syracuseStep 16900931 = 25351397) B25351397
theorem B2343887 : Blo 1561478 2343887 := bstep (se 1 (by rfl) ⟨1757915, by rfl⟩ : syracuseStep 2343887 = 3515831) B3515831
theorem B5629031 : Blo 1561478 5629031 := bstep (se 1 (by rfl) ⟨4221773, by rfl⟩ : syracuseStep 5629031 = 8443547) B8443547
theorem B6677801 : Blo 1561478 6677801 := bstep (se 2 (by rfl) ⟨2504175, by rfl⟩ : syracuseStep 6677801 = 5008351) B5008351
theorem B7914833 : Blo 1561478 7914833 := bstep (se 2 (by rfl) ⟨2968062, by rfl⟩ : syracuseStep 7914833 = 5936125) B5936125
theorem B5932511 : Blo 1561478 5932511 := bstep (se 1 (by rfl) ⟨4449383, by rfl⟩ : syracuseStep 5932511 = 8898767) B8898767
theorem B2344415 : Blo 1561478 2344415 := bstep (se 1 (by rfl) ⟨1758311, by rfl⟩ : syracuseStep 2344415 = 3516623) B3516623
theorem B3516011 : Blo 1561478 3516011 := bstep (se 1 (by rfl) ⟨2637008, by rfl⟩ : syracuseStep 3516011 = 5274017) B5274017
theorem B13346441 : Blo 1561478 13346441 := bstep (se 2 (by rfl) ⟨5004915, by rfl⟩ : syracuseStep 13346441 = 10009831) B10009831
theorem B3516281 : Blo 1561478 3516281 := bstep (se 2 (by rfl) ⟨1318605, by rfl⟩ : syracuseStep 3516281 = 2637211) B2637211
theorem B2345051 : Blo 1561478 2345051 := bstep (se 1 (by rfl) ⟨1758788, by rfl⟩ : syracuseStep 2345051 = 3517577) B3517577
theorem B2345087 : Blo 1561478 2345087 := bstep (se 1 (by rfl) ⟨1758815, by rfl⟩ : syracuseStep 2345087 = 3517631) B3517631
theorem B5933195 : Blo 1561478 5933195 := bstep (se 1 (by rfl) ⟨4449896, by rfl⟩ : syracuseStep 5933195 = 8899793) B8899793
theorem B3517019 : Blo 1561478 3517019 := bstep (se 1 (by rfl) ⟨2637764, by rfl⟩ : syracuseStep 3517019 = 5275529) B5275529
theorem B5270183 : Blo 1561478 5270183 := bstep (se 1 (by rfl) ⟨3952637, by rfl⟩ : syracuseStep 5270183 = 7905275) B7905275
theorem B3754783 : Blo 1561478 3754783 := bstep (se 1 (by rfl) ⟨2816087, by rfl⟩ : syracuseStep 3754783 = 5632175) B5632175
theorem B9022265 : Blo 1561478 9022265 := bstep (se 2 (by rfl) ⟨3383349, by rfl⟩ : syracuseStep 9022265 = 6766699) B6766699
theorem B3517289 : Blo 1561478 3517289 := bstep (se 2 (by rfl) ⟨1318983, by rfl⟩ : syracuseStep 3517289 = 2637967) B2637967
theorem B3517433 : Blo 1561478 3517433 := bstep (se 2 (by rfl) ⟨1319037, by rfl⟩ : syracuseStep 3517433 = 2638075) B2638075
theorem B10013705 : Blo 1561478 10013705 := bstep (se 2 (by rfl) ⟨3755139, by rfl⟩ : syracuseStep 10013705 = 7510279) B7510279
theorem B4222055 : Blo 1561478 4222055 := bstep (se 1 (by rfl) ⟨3166541, by rfl⟩ : syracuseStep 4222055 = 6333083) B6333083
theorem B3804583 : Blo 1561478 3804583 := bstep (se 1 (by rfl) ⟨2853437, by rfl⟩ : syracuseStep 3804583 = 5706875) B5706875
theorem B11865689 : Blo 1561478 11865689 := bstep (se 2 (by rfl) ⟨4449633, by rfl⟩ : syracuseStep 11865689 = 8899267) B8899267
theorem B1756831 : Blo 1561478 1756831 := bstep (se 1 (by rfl) ⟨1317623, by rfl⟩ : syracuseStep 1756831 = 2635247) B2635247
theorem B7507721 : Blo 1561478 7507721 := bstep (se 2 (by rfl) ⟨2815395, by rfl⟩ : syracuseStep 7507721 = 5630791) B5630791
theorem B9507071 : Blo 1561478 9507071 := bstep (se 1 (by rfl) ⟨7130303, by rfl⟩ : syracuseStep 9507071 = 14260607) B14260607
theorem B3953387 : Blo 1561478 3953387 := bstep (se 1 (by rfl) ⟨2965040, by rfl⟩ : syracuseStep 3953387 = 5930081) B5930081
theorem B90108773 : Blo 1561478 90108773 := bstep (se 4 (by rfl) ⟨8447697, by rfl⟩ : syracuseStep 90108773 = 16895395) B16895395
theorem B1758055 : Blo 1561478 1758055 := bstep (se 1 (by rfl) ⟨1318541, by rfl⟩ : syracuseStep 1758055 = 2637083) B2637083
theorem B42775465 : Blo 1561478 42775465 := bstep (se 2 (by rfl) ⟨16040799, by rfl⟩ : syracuseStep 42775465 = 32081599) B32081599
theorem B27055133 : Blo 1561478 27055133 := bstep (se 3 (by rfl) ⟨5072837, by rfl⟩ : syracuseStep 27055133 = 10145675) B10145675
theorem B1561691 : Blo 1561478 1561691 := bstep (se 1 (by rfl) ⟨1171268, by rfl⟩ : syracuseStep 1561691 = 2342537) B2342537
theorem B6337721 : Blo 1561478 6337721 := bstep (se 2 (by rfl) ⟨2376645, by rfl⟩ : syracuseStep 6337721 = 4753291) B4753291
theorem B1561983 : Blo 1561478 1561983 := bstep (se 1 (by rfl) ⟨1171487, by rfl⟩ : syracuseStep 1561983 = 2342975) B2342975
theorem B11859371 : Blo 1561478 11859371 := bstep (se 1 (by rfl) ⟨8894528, by rfl⟩ : syracuseStep 11859371 = 17789057) B17789057
theorem B1562047 : Blo 1561478 1562047 := bstep (se 1 (by rfl) ⟨1171535, by rfl⟩ : syracuseStep 1562047 = 2343071) B2343071
theorem B1562215 : Blo 1561478 1562215 := bstep (se 1 (by rfl) ⟨1171661, by rfl⟩ : syracuseStep 1562215 = 2343323) B2343323
theorem B1758847 : Blo 1561478 1758847 := bstep (se 1 (by rfl) ⟨1319135, by rfl⟩ : syracuseStep 1758847 = 2638271) B2638271
theorem B1562495 : Blo 1561478 1562495 := bstep (se 1 (by rfl) ⟨1171871, by rfl⟩ : syracuseStep 1562495 = 2343743) B2343743
theorem B13342751 : Blo 1561478 13342751 := bstep (se 1 (by rfl) ⟨10007063, by rfl⟩ : syracuseStep 13342751 = 20014127) B20014127
theorem B3954815 : Blo 1561478 3954815 := bstep (se 1 (by rfl) ⟨2966111, by rfl⟩ : syracuseStep 3954815 = 5932223) B5932223
theorem B10016905 : Blo 1561478 10016905 := bstep (se 2 (by rfl) ⟨3756339, by rfl⟩ : syracuseStep 10016905 = 7512679) B7512679
theorem B1562983 : Blo 1561478 1562983 := bstep (se 1 (by rfl) ⟨1172237, by rfl⟩ : syracuseStep 1562983 = 2344475) B2344475
theorem B1563071 : Blo 1561478 1563071 := bstep (se 1 (by rfl) ⟨1172303, by rfl⟩ : syracuseStep 1563071 = 2344607) B2344607
theorem B1563263 : Blo 1561478 1563263 := bstep (se 1 (by rfl) ⟨1172447, by rfl⟩ : syracuseStep 1563263 = 2344895) B2344895
theorem B7912079 : Blo 1561478 7912079 := bstep (se 1 (by rfl) ⟨5934059, by rfl⟩ : syracuseStep 7912079 = 11868119) B11868119
theorem B50691379 : Blo 1561478 50691379 := bstep (se 1 (by rfl) ⟨38018534, by rfl⟩ : syracuseStep 50691379 = 76037069) B76037069
theorem B4750663 : Blo 1561478 4750663 := bstep (se 1 (by rfl) ⟨3562997, by rfl⟩ : syracuseStep 4750663 = 7125995) B7125995
theorem B2342567 : Blo 1561478 2342567 := bstep (se 1 (by rfl) ⟨1756925, by rfl⟩ : syracuseStep 2342567 = 3513851) B3513851
theorem B3514031 : Blo 1561478 3514031 := bstep (se 1 (by rfl) ⟨2635523, by rfl⟩ : syracuseStep 3514031 = 5271047) B5271047
theorem B113999561 : Blo 1561478 113999561 := bstep (se 2 (by rfl) ⟨42749835, by rfl⟩ : syracuseStep 113999561 = 85499671) B85499671
theorem B2342639 : Blo 1561478 2342639 := bstep (se 1 (by rfl) ⟨1756979, by rfl⟩ : syracuseStep 2342639 = 3513959) B3513959
theorem B2342825 : Blo 1561478 2342825 := bstep (se 2 (by rfl) ⟨878559, by rfl⟩ : syracuseStep 2342825 = 1757119) B1757119
theorem B9633725 : Blo 1561478 9633725 := bstep (se 3 (by rfl) ⟨1806323, by rfl⟩ : syracuseStep 9633725 = 3612647) B3612647
theorem B3514337 : Blo 1561478 3514337 := bstep (se 2 (by rfl) ⟨1317876, by rfl⟩ : syracuseStep 3514337 = 2635753) B2635753
theorem B2965481 : Blo 1561478 2965481 := bstep (se 2 (by rfl) ⟨1112055, by rfl⟩ : syracuseStep 2965481 = 2224111) B2224111
theorem B2343167 : Blo 1561478 2343167 := bstep (se 1 (by rfl) ⟨1757375, by rfl⟩ : syracuseStep 2343167 = 3514751) B3514751
theorem B5275961 : Blo 1561478 5275961 := bstep (se 2 (by rfl) ⟨1978485, by rfl⟩ : syracuseStep 5275961 = 3956971) B3956971
theorem B16900589 : Blo 1561478 16900589 := bstep (se 3 (by rfl) ⟨3168860, by rfl⟩ : syracuseStep 16900589 = 6337721) B6337721
theorem B60072515 : Blo 1561478 60072515 := bstep (se 1 (by rfl) ⟨45054386, by rfl⟩ : syracuseStep 60072515 = 90108773) B90108773
theorem B3752687 : Blo 1561478 3752687 := bstep (se 1 (by rfl) ⟨2814515, by rfl⟩ : syracuseStep 3752687 = 5629031) B5629031
theorem B5276555 : Blo 1561478 5276555 := bstep (se 1 (by rfl) ⟨3957416, by rfl⟩ : syracuseStep 5276555 = 7914833) B7914833
theorem B7906247 : Blo 1561478 7906247 := bstep (se 1 (by rfl) ⟨5929685, by rfl⟩ : syracuseStep 7906247 = 11859371) B11859371
theorem B5006377 : Blo 1561478 5006377 := bstep (se 2 (by rfl) ⟨1877391, by rfl⟩ : syracuseStep 5006377 = 3754783) B3754783
theorem B2344007 : Blo 1561478 2344007 := bstep (se 1 (by rfl) ⟨1758005, by rfl⟩ : syracuseStep 2344007 = 3516011) B3516011
theorem B8897627 : Blo 1561478 8897627 := bstep (se 1 (by rfl) ⟨6673220, by rfl⟩ : syracuseStep 8897627 = 13346441) B13346441
theorem B2344073 : Blo 1561478 2344073 := bstep (se 2 (by rfl) ⟨879027, by rfl⟩ : syracuseStep 2344073 = 1758055) B1758055
theorem B57033953 : Blo 1561478 57033953 := bstep (se 2 (by rfl) ⟨21387732, by rfl⟩ : syracuseStep 57033953 = 42775465) B42775465
theorem B2344187 : Blo 1561478 2344187 := bstep (se 1 (by rfl) ⟨1758140, by rfl⟩ : syracuseStep 2344187 = 3516281) B3516281
theorem B2344679 : Blo 1561478 2344679 := bstep (se 1 (by rfl) ⟨1758509, by rfl⟩ : syracuseStep 2344679 = 3517019) B3517019
theorem B6334217 : Blo 1561478 6334217 := bstep (se 2 (by rfl) ⟨2375331, by rfl⟩ : syracuseStep 6334217 = 4750663) B4750663
theorem B6014843 : Blo 1561478 6014843 := bstep (se 1 (by rfl) ⟨4511132, by rfl⟩ : syracuseStep 6014843 = 9022265) B9022265
theorem B5072777 : Blo 1561478 5072777 := bstep (se 2 (by rfl) ⟨1902291, by rfl⟩ : syracuseStep 5072777 = 3804583) B3804583
theorem B2344859 : Blo 1561478 2344859 := bstep (se 1 (by rfl) ⟨1758644, by rfl⟩ : syracuseStep 2344859 = 3517289) B3517289
theorem B2344955 : Blo 1561478 2344955 := bstep (se 1 (by rfl) ⟨1758716, by rfl⟩ : syracuseStep 2344955 = 3517433) B3517433
theorem B60033149 : Blo 1561478 60033149 := bstep (se 3 (by rfl) ⟨11256215, by rfl⟩ : syracuseStep 60033149 = 22512431) B22512431
theorem B2345129 : Blo 1561478 2345129 := bstep (se 2 (by rfl) ⟨879423, by rfl⟩ : syracuseStep 2345129 = 1758847) B1758847
theorem B75999707 : Blo 1561478 75999707 := bstep (se 1 (by rfl) ⟨56999780, by rfl⟩ : syracuseStep 75999707 = 113999561) B113999561
theorem B1976987 : Blo 1561478 1976987 := bstep (se 1 (by rfl) ⟨1482740, by rfl⟩ : syracuseStep 1976987 = 2965481) B2965481
theorem B13355873 : Blo 1561478 13355873 := bstep (se 2 (by rfl) ⟨5008452, by rfl⟩ : syracuseStep 13355873 = 10016905) B10016905
theorem B11258813 : Blo 1561478 11258813 := bstep (se 3 (by rfl) ⟨2111027, by rfl⟩ : syracuseStep 11258813 = 4222055) B4222055
theorem B4503940537 : Blo 1561478 4503940537 := bstep (se 2 (by rfl) ⟨1688977701, by rfl⟩ : syracuseStep 4503940537 = 3377955403) B3377955403
theorem B4451867 : Blo 1561478 4451867 := bstep (se 1 (by rfl) ⟨3338900, by rfl⟩ : syracuseStep 4451867 = 6677801) B6677801
theorem B67588505 : Blo 1561478 67588505 := bstep (se 2 (by rfl) ⟨25345689, by rfl⟩ : syracuseStep 67588505 = 50691379) B50691379
theorem B45069149 : Blo 1561478 45069149 := bstep (se 3 (by rfl) ⟨8450465, by rfl⟩ : syracuseStep 45069149 = 16900931) B16900931
theorem B7910459 : Blo 1561478 7910459 := bstep (se 1 (by rfl) ⟨5932844, by rfl⟩ : syracuseStep 7910459 = 11865689) B11865689
theorem B1561711 : Blo 1561478 1561711 := bstep (se 1 (by rfl) ⟨1171283, by rfl⟩ : syracuseStep 1561711 = 2342567) B2342567
theorem B1561759 : Blo 1561478 1561759 := bstep (se 1 (by rfl) ⟨1171319, by rfl⟩ : syracuseStep 1561759 = 2342639) B2342639
theorem B1561883 : Blo 1561478 1561883 := bstep (se 1 (by rfl) ⟨1171412, by rfl⟩ : syracuseStep 1561883 = 2342825) B2342825
theorem B6338047 : Blo 1561478 6338047 := bstep (se 1 (by rfl) ⟨4753535, by rfl⟩ : syracuseStep 6338047 = 9507071) B9507071
theorem B1562319 : Blo 1561478 1562319 := bstep (se 1 (by rfl) ⟨1171739, by rfl⟩ : syracuseStep 1562319 = 2343479) B2343479
theorem B2635591 : Blo 1561478 2635591 := bstep (se 1 (by rfl) ⟨1976693, by rfl⟩ : syracuseStep 2635591 = 3953387) B3953387
theorem B1562479 : Blo 1561478 1562479 := bstep (se 1 (by rfl) ⟨1171859, by rfl⟩ : syracuseStep 1562479 = 2343719) B2343719
theorem B1562591 : Blo 1561478 1562591 := bstep (se 1 (by rfl) ⟨1171943, by rfl⟩ : syracuseStep 1562591 = 2343887) B2343887
theorem B18036755 : Blo 1561478 18036755 := bstep (se 1 (by rfl) ⟨13527566, by rfl⟩ : syracuseStep 18036755 = 27055133) B27055133
theorem B3955007 : Blo 1561478 3955007 := bstep (se 1 (by rfl) ⟨2966255, by rfl⟩ : syracuseStep 3955007 = 5932511) B5932511
theorem B1562943 : Blo 1561478 1562943 := bstep (se 1 (by rfl) ⟨1172207, by rfl⟩ : syracuseStep 1562943 = 2344415) B2344415
theorem B8895167 : Blo 1561478 8895167 := bstep (se 1 (by rfl) ⟨6671375, by rfl⟩ : syracuseStep 8895167 = 13342751) B13342751
theorem B1563367 : Blo 1561478 1563367 := bstep (se 1 (by rfl) ⟨1172525, by rfl⟩ : syracuseStep 1563367 = 2345051) B2345051
theorem B2636543 : Blo 1561478 2636543 := bstep (se 1 (by rfl) ⟨1977407, by rfl⟩ : syracuseStep 2636543 = 3954815) B3954815
theorem B1563391 : Blo 1561478 1563391 := bstep (se 1 (by rfl) ⟨1172543, by rfl⟩ : syracuseStep 1563391 = 2345087) B2345087
theorem B3955463 : Blo 1561478 3955463 := bstep (se 1 (by rfl) ⟨2966597, by rfl⟩ : syracuseStep 3955463 = 5933195) B5933195
theorem B5274719 : Blo 1561478 5274719 := bstep (se 1 (by rfl) ⟨3956039, by rfl⟩ : syracuseStep 5274719 = 7912079) B7912079
theorem B3513455 : Blo 1561478 3513455 := bstep (se 1 (by rfl) ⟨2635091, by rfl⟩ : syracuseStep 3513455 = 5270183) B5270183
theorem B6675803 : Blo 1561478 6675803 := bstep (se 1 (by rfl) ⟨5006852, by rfl⟩ : syracuseStep 6675803 = 10013705) B10013705
theorem B2342441 : Blo 1561478 2342441 := bstep (se 2 (by rfl) ⟨878415, by rfl⟩ : syracuseStep 2342441 = 1756831) B1756831
theorem B2342687 : Blo 1561478 2342687 := bstep (se 1 (by rfl) ⟨1757015, by rfl⟩ : syracuseStep 2342687 = 3514031) B3514031
theorem B5005147 : Blo 1561478 5005147 := bstep (se 1 (by rfl) ⟨3753860, by rfl⟩ : syracuseStep 5005147 = 7507721) B7507721
theorem B6422483 : Blo 1561478 6422483 := bstep (se 1 (by rfl) ⟨4816862, by rfl⟩ : syracuseStep 6422483 = 9633725) B9633725
theorem B2342891 : Blo 1561478 2342891 := bstep (se 1 (by rfl) ⟨1757168, by rfl⟩ : syracuseStep 2342891 = 3514337) B3514337
theorem B5931751 : Blo 1561478 5931751 := bstep (se 1 (by rfl) ⟨4448813, by rfl⟩ : syracuseStep 5931751 = 8897627) B8897627
theorem B6005254049 : Blo 1561478 6005254049 := bstep (se 2 (by rfl) ⟨2251970268, by rfl⟩ : syracuseStep 6005254049 = 4503940537) B4503940537
theorem B7505875 : Blo 1561478 7505875 := bstep (se 1 (by rfl) ⟨5629406, by rfl⟩ : syracuseStep 7505875 = 11258813) B11258813
theorem B3516479 : Blo 1561478 3516479 := bstep (se 1 (by rfl) ⟨2637359, by rfl⟩ : syracuseStep 3516479 = 5274719) B5274719
theorem B4450535 : Blo 1561478 4450535 := bstep (se 1 (by rfl) ⟨3337901, by rfl⟩ : syracuseStep 4450535 = 6675803) B6675803
theorem B2967911 : Blo 1561478 2967911 := bstep (se 1 (by rfl) ⟨2225933, by rfl⟩ : syracuseStep 2967911 = 4451867) B4451867
theorem B3517307 : Blo 1561478 3517307 := bstep (se 1 (by rfl) ⟨2637980, by rfl⟩ : syracuseStep 3517307 = 5275961) B5275961
theorem B45059003 : Blo 1561478 45059003 := bstep (se 1 (by rfl) ⟨33794252, by rfl⟩ : syracuseStep 45059003 = 67588505) B67588505
theorem B11267059 : Blo 1561478 11267059 := bstep (se 1 (by rfl) ⟨8450294, by rfl⟩ : syracuseStep 11267059 = 16900589) B16900589
theorem B3517703 : Blo 1561478 3517703 := bstep (se 1 (by rfl) ⟨2638277, by rfl⟩ : syracuseStep 3517703 = 5276555) B5276555
theorem B5270831 : Blo 1561478 5270831 := bstep (se 1 (by rfl) ⟨3953123, by rfl⟩ : syracuseStep 5270831 = 7906247) B7906247
theorem B38022635 : Blo 1561478 38022635 := bstep (se 1 (by rfl) ⟨28516976, by rfl⟩ : syracuseStep 38022635 = 57033953) B57033953
theorem B4222811 : Blo 1561478 4222811 := bstep (se 1 (by rfl) ⟨3167108, by rfl⟩ : syracuseStep 4222811 = 6334217) B6334217
theorem B4009895 : Blo 1561478 4009895 := bstep (se 1 (by rfl) ⟨3007421, by rfl⟩ : syracuseStep 4009895 = 6014843) B6014843
theorem B40022099 : Blo 1561478 40022099 := bstep (se 1 (by rfl) ⟨30016574, by rfl⟩ : syracuseStep 40022099 = 60033149) B60033149
theorem B5271965 : Blo 1561478 5271965 := bstep (se 3 (by rfl) ⟨988493, by rfl⟩ : syracuseStep 5271965 = 1976987) B1976987
theorem B1757695 : Blo 1561478 1757695 := bstep (se 1 (by rfl) ⟨1318271, by rfl⟩ : syracuseStep 1757695 = 2636543) B2636543
theorem B10007165 : Blo 1561478 10007165 := bstep (se 3 (by rfl) ⟨1876343, by rfl⟩ : syracuseStep 10007165 = 3752687) B3752687
theorem B8450729 : Blo 1561478 8450729 := bstep (se 2 (by rfl) ⟨3169023, by rfl⟩ : syracuseStep 8450729 = 6338047) B6338047
theorem B1561627 : Blo 1561478 1561627 := bstep (se 1 (by rfl) ⟨1171220, by rfl⟩ : syracuseStep 1561627 = 2342441) B2342441
theorem B6673529 : Blo 1561478 6673529 := bstep (se 2 (by rfl) ⟨2502573, by rfl⟩ : syracuseStep 6673529 = 5005147) B5005147
theorem B1561791 : Blo 1561478 1561791 := bstep (se 1 (by rfl) ⟨1171343, by rfl⟩ : syracuseStep 1561791 = 2342687) B2342687
theorem B4281655 : Blo 1561478 4281655 := bstep (se 1 (by rfl) ⟨3211241, by rfl⟩ : syracuseStep 4281655 = 6422483) B6422483
theorem B1561927 : Blo 1561478 1561927 := bstep (se 1 (by rfl) ⟨1171445, by rfl⟩ : syracuseStep 1561927 = 2342891) B2342891
theorem B1562111 : Blo 1561478 1562111 := bstep (se 1 (by rfl) ⟨1171583, by rfl⟩ : syracuseStep 1562111 = 2343167) B2343167
theorem B40048343 : Blo 1561478 40048343 := bstep (se 1 (by rfl) ⟨30036257, by rfl⟩ : syracuseStep 40048343 = 60072515) B60072515
theorem B30046099 : Blo 1561478 30046099 := bstep (se 1 (by rfl) ⟨22534574, by rfl⟩ : syracuseStep 30046099 = 45069149) B45069149
theorem B5273639 : Blo 1561478 5273639 := bstep (se 1 (by rfl) ⟨3955229, by rfl⟩ : syracuseStep 5273639 = 7910459) B7910459
theorem B1562671 : Blo 1561478 1562671 := bstep (se 1 (by rfl) ⟨1172003, by rfl⟩ : syracuseStep 1562671 = 2344007) B2344007
theorem B1562715 : Blo 1561478 1562715 := bstep (se 1 (by rfl) ⟨1172036, by rfl⟩ : syracuseStep 1562715 = 2344073) B2344073
theorem B1562791 : Blo 1561478 1562791 := bstep (se 1 (by rfl) ⟨1172093, by rfl⟩ : syracuseStep 1562791 = 2344187) B2344187
theorem B1563119 : Blo 1561478 1563119 := bstep (se 1 (by rfl) ⟨1172339, by rfl⟩ : syracuseStep 1563119 = 2344679) B2344679
theorem B3381851 : Blo 1561478 3381851 := bstep (se 1 (by rfl) ⟨2536388, by rfl⟩ : syracuseStep 3381851 = 5072777) B5072777
theorem B1563239 : Blo 1561478 1563239 := bstep (se 1 (by rfl) ⟨1172429, by rfl⟩ : syracuseStep 1563239 = 2344859) B2344859
theorem B1563303 : Blo 1561478 1563303 := bstep (se 1 (by rfl) ⟨1172477, by rfl⟩ : syracuseStep 1563303 = 2344955) B2344955
theorem B12024503 : Blo 1561478 12024503 := bstep (se 1 (by rfl) ⟨9018377, by rfl⟩ : syracuseStep 12024503 = 18036755) B18036755
theorem B6675169 : Blo 1561478 6675169 := bstep (se 2 (by rfl) ⟨2503188, by rfl⟩ : syracuseStep 6675169 = 5006377) B5006377
theorem B1563419 : Blo 1561478 1563419 := bstep (se 1 (by rfl) ⟨1172564, by rfl⟩ : syracuseStep 1563419 = 2345129) B2345129
theorem B2636671 : Blo 1561478 2636671 := bstep (se 1 (by rfl) ⟨1977503, by rfl⟩ : syracuseStep 2636671 = 3955007) B3955007
theorem B50666471 : Blo 1561478 50666471 := bstep (se 1 (by rfl) ⟨37999853, by rfl⟩ : syracuseStep 50666471 = 75999707) B75999707
theorem B5930111 : Blo 1561478 5930111 := bstep (se 1 (by rfl) ⟨4447583, by rfl⟩ : syracuseStep 5930111 = 8895167) B8895167
theorem B2636975 : Blo 1561478 2636975 := bstep (se 1 (by rfl) ⟨1977731, by rfl⟩ : syracuseStep 2636975 = 3955463) B3955463
theorem B8903915 : Blo 1561478 8903915 := bstep (se 1 (by rfl) ⟨6677936, by rfl⟩ : syracuseStep 8903915 = 13355873) B13355873
theorem B2342303 : Blo 1561478 2342303 := bstep (se 1 (by rfl) ⟨1756727, by rfl⟩ : syracuseStep 2342303 = 3513455) B3513455
theorem B3514121 : Blo 1561478 3514121 := bstep (se 2 (by rfl) ⟨1317795, by rfl⟩ : syracuseStep 3514121 = 2635591) B2635591
theorem B26681399 : Blo 1561478 26681399 := bstep (se 1 (by rfl) ⟨20011049, by rfl⟩ : syracuseStep 26681399 = 40022099) B40022099
theorem B3514643 : Blo 1561478 3514643 := bstep (se 1 (by rfl) ⟨2635982, by rfl⟩ : syracuseStep 3514643 = 5271965) B5271965
theorem B2343593 : Blo 1561478 2343593 := bstep (se 2 (by rfl) ⟨878847, by rfl⟩ : syracuseStep 2343593 = 1757695) B1757695
theorem B4449019 : Blo 1561478 4449019 := bstep (se 1 (by rfl) ⟨3336764, by rfl⟩ : syracuseStep 4449019 = 6673529) B6673529
theorem B26698895 : Blo 1561478 26698895 := bstep (se 1 (by rfl) ⟨20024171, by rfl⟩ : syracuseStep 26698895 = 40048343) B40048343
theorem B3515561 : Blo 1561478 3515561 := bstep (se 2 (by rfl) ⟨1318335, by rfl⟩ : syracuseStep 3515561 = 2636671) B2636671
theorem B3515759 : Blo 1561478 3515759 := bstep (se 1 (by rfl) ⟨2636819, by rfl⟩ : syracuseStep 3515759 = 5273639) B5273639
theorem B2344319 : Blo 1561478 2344319 := bstep (se 1 (by rfl) ⟨1758239, by rfl⟩ : syracuseStep 2344319 = 3516479) B3516479
theorem B2967023 : Blo 1561478 2967023 := bstep (se 1 (by rfl) ⟨2225267, by rfl⟩ : syracuseStep 2967023 = 4450535) B4450535
theorem B2254567 : Blo 1561478 2254567 := bstep (se 1 (by rfl) ⟨1690925, by rfl⟩ : syracuseStep 2254567 = 3381851) B3381851
theorem B2344871 : Blo 1561478 2344871 := bstep (se 1 (by rfl) ⟨1758653, by rfl⟩ : syracuseStep 2344871 = 3517307) B3517307
theorem B33777647 : Blo 1561478 33777647 := bstep (se 1 (by rfl) ⟨25333235, by rfl⟩ : syracuseStep 33777647 = 50666471) B50666471
theorem B2345135 : Blo 1561478 2345135 := bstep (se 1 (by rfl) ⟨1758851, by rfl⟩ : syracuseStep 2345135 = 3517703) B3517703
theorem B25348423 : Blo 1561478 25348423 := bstep (se 1 (by rfl) ⟨19011317, by rfl⟩ : syracuseStep 25348423 = 38022635) B38022635
theorem B40061465 : Blo 1561478 40061465 := bstep (se 2 (by rfl) ⟨15023049, by rfl⟩ : syracuseStep 40061465 = 30046099) B30046099
theorem B2673263 : Blo 1561478 2673263 := bstep (se 1 (by rfl) ⟨2004947, by rfl⟩ : syracuseStep 2673263 = 4009895) B4009895
theorem B8900225 : Blo 1561478 8900225 := bstep (se 2 (by rfl) ⟨3337584, by rfl⟩ : syracuseStep 8900225 = 6675169) B6675169
theorem B7909001 : Blo 1561478 7909001 := bstep (se 2 (by rfl) ⟨2965875, by rfl⟩ : syracuseStep 7909001 = 5931751) B5931751
theorem B1978607 : Blo 1561478 1978607 := bstep (se 1 (by rfl) ⟨1483955, by rfl⟩ : syracuseStep 1978607 = 2967911) B2967911
theorem B26685773 : Blo 1561478 26685773 := bstep (se 3 (by rfl) ⟨5003582, by rfl⟩ : syracuseStep 26685773 = 10007165) B10007165
theorem B8016335 : Blo 1561478 8016335 := bstep (se 1 (by rfl) ⟨6012251, by rfl⟩ : syracuseStep 8016335 = 12024503) B12024503
theorem B3953407 : Blo 1561478 3953407 := bstep (se 1 (by rfl) ⟨2965055, by rfl⟩ : syracuseStep 3953407 = 5930111) B5930111
theorem B1757983 : Blo 1561478 1757983 := bstep (se 1 (by rfl) ⟨1318487, by rfl⟩ : syracuseStep 1757983 = 2636975) B2636975
theorem B5935943 : Blo 1561478 5935943 := bstep (se 1 (by rfl) ⟨4451957, by rfl⟩ : syracuseStep 5935943 = 8903915) B8903915
theorem B11260829 : Blo 1561478 11260829 := bstep (se 3 (by rfl) ⟨2111405, by rfl⟩ : syracuseStep 11260829 = 4222811) B4222811
theorem B1561535 : Blo 1561478 1561535 := bstep (se 1 (by rfl) ⟨1171151, by rfl⟩ : syracuseStep 1561535 = 2342303) B2342303
theorem B10007833 : Blo 1561478 10007833 := bstep (se 2 (by rfl) ⟨3752937, by rfl⟩ : syracuseStep 10007833 = 7505875) B7505875
theorem B5633819 : Blo 1561478 5633819 := bstep (se 1 (by rfl) ⟨4225364, by rfl⟩ : syracuseStep 5633819 = 8450729) B8450729
theorem B4003502699 : Blo 1561478 4003502699 := bstep (se 1 (by rfl) ⟨3002627024, by rfl⟩ : syracuseStep 4003502699 = 6005254049) B6005254049
theorem B15022745 : Blo 1561478 15022745 := bstep (se 2 (by rfl) ⟨5633529, by rfl⟩ : syracuseStep 15022745 = 11267059) B11267059
theorem B5708873 : Blo 1561478 5708873 := bstep (se 2 (by rfl) ⟨2140827, by rfl⟩ : syracuseStep 5708873 = 4281655) B4281655
theorem B30039335 : Blo 1561478 30039335 := bstep (se 1 (by rfl) ⟨22529501, by rfl⟩ : syracuseStep 30039335 = 45059003) B45059003
theorem B3513887 : Blo 1561478 3513887 := bstep (se 1 (by rfl) ⟨2635415, by rfl⟩ : syracuseStep 3513887 = 5270831) B5270831
theorem B2342747 : Blo 1561478 2342747 := bstep (se 1 (by rfl) ⟨1757060, by rfl⟩ : syracuseStep 2342747 = 3514121) B3514121
theorem B2343095 : Blo 1561478 2343095 := bstep (se 1 (by rfl) ⟨1757321, by rfl⟩ : syracuseStep 2343095 = 3514643) B3514643
theorem B3957295 : Blo 1561478 3957295 := bstep (se 1 (by rfl) ⟨2967971, by rfl⟩ : syracuseStep 3957295 = 5935943) B5935943
theorem B5276285 : Blo 1561478 5276285 := bstep (se 3 (by rfl) ⟨989303, by rfl⟩ : syracuseStep 5276285 = 1978607) B1978607
theorem B2343707 : Blo 1561478 2343707 := bstep (se 1 (by rfl) ⟨1757780, by rfl⟩ : syracuseStep 2343707 = 3515561) B3515561
theorem B2343839 : Blo 1561478 2343839 := bstep (se 1 (by rfl) ⟨1757879, by rfl⟩ : syracuseStep 2343839 = 3515759) B3515759
theorem B5932025 : Blo 1561478 5932025 := bstep (se 2 (by rfl) ⟨2224509, by rfl⟩ : syracuseStep 5932025 = 4449019) B4449019
theorem B2343977 : Blo 1561478 2343977 := bstep (se 2 (by rfl) ⟨878991, by rfl⟩ : syracuseStep 2343977 = 1757983) B1757983
theorem B26707643 : Blo 1561478 26707643 := bstep (se 1 (by rfl) ⟨20030732, by rfl⟩ : syracuseStep 26707643 = 40061465) B40061465
theorem B5933483 : Blo 1561478 5933483 := bstep (se 1 (by rfl) ⟨4450112, by rfl⟩ : syracuseStep 5933483 = 8900225) B8900225
theorem B17787599 : Blo 1561478 17787599 := bstep (se 1 (by rfl) ⟨13340699, by rfl⟩ : syracuseStep 17787599 = 26681399) B26681399
theorem B5344223 : Blo 1561478 5344223 := bstep (se 1 (by rfl) ⟨4008167, by rfl⟩ : syracuseStep 5344223 = 8016335) B8016335
theorem B1978015 : Blo 1561478 1978015 := bstep (se 1 (by rfl) ⟨1483511, by rfl⟩ : syracuseStep 1978015 = 2967023) B2967023
theorem B5271209 : Blo 1561478 5271209 := bstep (se 2 (by rfl) ⟨1976703, by rfl⟩ : syracuseStep 5271209 = 3953407) B3953407
theorem B3755879 : Blo 1561478 3755879 := bstep (se 1 (by rfl) ⟨2816909, by rfl⟩ : syracuseStep 3755879 = 5633819) B5633819
theorem B1782175 : Blo 1561478 1782175 := bstep (se 1 (by rfl) ⟨1336631, by rfl⟩ : syracuseStep 1782175 = 2673263) B2673263
theorem B10015163 : Blo 1561478 10015163 := bstep (se 1 (by rfl) ⟨7511372, by rfl⟩ : syracuseStep 10015163 = 15022745) B15022745
theorem B3805915 : Blo 1561478 3805915 := bstep (se 1 (by rfl) ⟨2854436, by rfl⟩ : syracuseStep 3805915 = 5708873) B5708873
theorem B20026223 : Blo 1561478 20026223 := bstep (se 1 (by rfl) ⟨15019667, by rfl⟩ : syracuseStep 20026223 = 30039335) B30039335
theorem B30028877 : Blo 1561478 30028877 := bstep (se 3 (by rfl) ⟨5630414, by rfl⟩ : syracuseStep 30028877 = 11260829) B11260829
theorem B5272667 : Blo 1561478 5272667 := bstep (se 1 (by rfl) ⟨3954500, by rfl⟩ : syracuseStep 5272667 = 7909001) B7909001
theorem B1561831 : Blo 1561478 1561831 := bstep (se 1 (by rfl) ⟨1171373, by rfl⟩ : syracuseStep 1561831 = 2342747) B2342747
theorem B17790515 : Blo 1561478 17790515 := bstep (se 1 (by rfl) ⟨13342886, by rfl⟩ : syracuseStep 17790515 = 26685773) B26685773
theorem B33797897 : Blo 1561478 33797897 := bstep (se 2 (by rfl) ⟨12674211, by rfl⟩ : syracuseStep 33797897 = 25348423) B25348423
theorem B1562395 : Blo 1561478 1562395 := bstep (se 1 (by rfl) ⟨1171796, by rfl⟩ : syracuseStep 1562395 = 2343593) B2343593
theorem B17799263 : Blo 1561478 17799263 := bstep (se 1 (by rfl) ⟨13349447, by rfl⟩ : syracuseStep 17799263 = 26698895) B26698895
theorem B1562879 : Blo 1561478 1562879 := bstep (se 1 (by rfl) ⟨1172159, by rfl⟩ : syracuseStep 1562879 = 2344319) B2344319
theorem B1563247 : Blo 1561478 1563247 := bstep (se 1 (by rfl) ⟨1172435, by rfl⟩ : syracuseStep 1563247 = 2344871) B2344871
theorem B22518431 : Blo 1561478 22518431 := bstep (se 1 (by rfl) ⟨16888823, by rfl⟩ : syracuseStep 22518431 = 33777647) B33777647
theorem B1563423 : Blo 1561478 1563423 := bstep (se 1 (by rfl) ⟨1172567, by rfl⟩ : syracuseStep 1563423 = 2345135) B2345135
theorem B13343777 : Blo 1561478 13343777 := bstep (se 2 (by rfl) ⟨5003916, by rfl⟩ : syracuseStep 13343777 = 10007833) B10007833
theorem B2669001799 : Blo 1561478 2669001799 := bstep (se 1 (by rfl) ⟨2001751349, by rfl⟩ : syracuseStep 2669001799 = 4003502699) B4003502699
theorem B3006089 : Blo 1561478 3006089 := bstep (se 2 (by rfl) ⟨1127283, by rfl⟩ : syracuseStep 3006089 = 2254567) B2254567
theorem B2342591 : Blo 1561478 2342591 := bstep (se 1 (by rfl) ⟨1756943, by rfl⟩ : syracuseStep 2342591 = 3513887) B3513887
theorem B6676775 : Blo 1561478 6676775 := bstep (se 1 (by rfl) ⟨5007581, by rfl⟩ : syracuseStep 6676775 = 10015163) B10015163
theorem B2376233 : Blo 1561478 2376233 := bstep (se 2 (by rfl) ⟨891087, by rfl⟩ : syracuseStep 2376233 = 1782175) B1782175
theorem B3515111 : Blo 1561478 3515111 := bstep (se 1 (by rfl) ⟨2636333, by rfl⟩ : syracuseStep 3515111 = 5272667) B5272667
theorem B5276393 : Blo 1561478 5276393 := bstep (se 2 (by rfl) ⟨1978647, by rfl⟩ : syracuseStep 5276393 = 3957295) B3957295
theorem B3517523 : Blo 1561478 3517523 := bstep (se 1 (by rfl) ⟨2638142, by rfl⟩ : syracuseStep 3517523 = 5276285) B5276285
theorem B5074553 : Blo 1561478 5074553 := bstep (se 2 (by rfl) ⟨1902957, by rfl⟩ : syracuseStep 5074553 = 3805915) B3805915
theorem B17805095 : Blo 1561478 17805095 := bstep (se 1 (by rfl) ⟨13353821, by rfl⟩ : syracuseStep 17805095 = 26707643) B26707643
theorem B22531931 : Blo 1561478 22531931 := bstep (se 1 (by rfl) ⟨16898948, by rfl⟩ : syracuseStep 22531931 = 33797897) B33797897
theorem B11866175 : Blo 1561478 11866175 := bstep (se 1 (by rfl) ⟨8899631, by rfl⟩ : syracuseStep 11866175 = 17799263) B17799263
theorem B15012287 : Blo 1561478 15012287 := bstep (se 1 (by rfl) ⟨11259215, by rfl⟩ : syracuseStep 15012287 = 22518431) B22518431
theorem B11858399 : Blo 1561478 11858399 := bstep (se 1 (by rfl) ⟨8893799, by rfl⟩ : syracuseStep 11858399 = 17787599) B17787599
theorem B57005045 : Blo 1561478 57005045 := bstep (se 5 (by rfl) ⟨2672111, by rfl⟩ : syracuseStep 57005045 = 5344223) B5344223
theorem B2004059 : Blo 1561478 2004059 := bstep (se 1 (by rfl) ⟨1503044, by rfl⟩ : syracuseStep 2004059 = 3006089) B3006089
theorem B1561727 : Blo 1561478 1561727 := bstep (se 1 (by rfl) ⟨1171295, by rfl⟩ : syracuseStep 1561727 = 2342591) B2342591
theorem B2503919 : Blo 1561478 2503919 := bstep (se 1 (by rfl) ⟨1877939, by rfl⟩ : syracuseStep 2503919 = 3755879) B3755879
theorem B1562063 : Blo 1561478 1562063 := bstep (se 1 (by rfl) ⟨1171547, by rfl⟩ : syracuseStep 1562063 = 2343095) B2343095
theorem B1562471 : Blo 1561478 1562471 := bstep (se 1 (by rfl) ⟨1171853, by rfl⟩ : syracuseStep 1562471 = 2343707) B2343707
theorem B13350815 : Blo 1561478 13350815 := bstep (se 1 (by rfl) ⟨10013111, by rfl⟩ : syracuseStep 13350815 = 20026223) B20026223
theorem B1562559 : Blo 1561478 1562559 := bstep (se 1 (by rfl) ⟨1171919, by rfl⟩ : syracuseStep 1562559 = 2343839) B2343839
theorem B3954683 : Blo 1561478 3954683 := bstep (se 1 (by rfl) ⟨2966012, by rfl⟩ : syracuseStep 3954683 = 5932025) B5932025
theorem B1562651 : Blo 1561478 1562651 := bstep (se 1 (by rfl) ⟨1171988, by rfl⟩ : syracuseStep 1562651 = 2343977) B2343977
theorem B20019251 : Blo 1561478 20019251 := bstep (se 1 (by rfl) ⟨15014438, by rfl⟩ : syracuseStep 20019251 = 30028877) B30028877
theorem B11860343 : Blo 1561478 11860343 := bstep (se 1 (by rfl) ⟨8895257, by rfl⟩ : syracuseStep 11860343 = 17790515) B17790515
theorem B3558669065 : Blo 1561478 3558669065 := bstep (se 2 (by rfl) ⟨1334500899, by rfl⟩ : syracuseStep 3558669065 = 2669001799) B2669001799
theorem B3955655 : Blo 1561478 3955655 := bstep (se 1 (by rfl) ⟨2966741, by rfl⟩ : syracuseStep 3955655 = 5933483) B5933483
theorem B8895851 : Blo 1561478 8895851 := bstep (se 1 (by rfl) ⟨6671888, by rfl⟩ : syracuseStep 8895851 = 13343777) B13343777
theorem B2637353 : Blo 1561478 2637353 := bstep (se 2 (by rfl) ⟨989007, by rfl⟩ : syracuseStep 2637353 = 1978015) B1978015
theorem B3514139 : Blo 1561478 3514139 := bstep (se 1 (by rfl) ⟨2635604, by rfl⟩ : syracuseStep 3514139 = 5271209) B5271209
theorem B7905599 : Blo 1561478 7905599 := bstep (se 1 (by rfl) ⟨5929199, by rfl⟩ : syracuseStep 7905599 = 11858399) B11858399
theorem B2343407 : Blo 1561478 2343407 := bstep (se 1 (by rfl) ⟨1757555, by rfl⟩ : syracuseStep 2343407 = 3515111) B3515111
theorem B6677117 : Blo 1561478 6677117 := bstep (se 3 (by rfl) ⟨1251959, by rfl⟩ : syracuseStep 6677117 = 2503919) B2503919
theorem B38003363 : Blo 1561478 38003363 := bstep (se 1 (by rfl) ⟨28502522, by rfl⟩ : syracuseStep 38003363 = 57005045) B57005045
theorem B13346167 : Blo 1561478 13346167 := bstep (se 1 (by rfl) ⟨10009625, by rfl⟩ : syracuseStep 13346167 = 20019251) B20019251
theorem B7906895 : Blo 1561478 7906895 := bstep (se 1 (by rfl) ⟨5930171, by rfl⟩ : syracuseStep 7906895 = 11860343) B11860343
theorem B2372446043 : Blo 1561478 2372446043 := bstep (se 1 (by rfl) ⟨1779334532, by rfl⟩ : syracuseStep 2372446043 = 3558669065) B3558669065
theorem B2345015 : Blo 1561478 2345015 := bstep (se 1 (by rfl) ⟨1758761, by rfl⟩ : syracuseStep 2345015 = 3517523) B3517523
theorem B4451183 : Blo 1561478 4451183 := bstep (se 1 (by rfl) ⟨3338387, by rfl⟩ : syracuseStep 4451183 = 6676775) B6676775
theorem B5344157 : Blo 1561478 5344157 := bstep (se 3 (by rfl) ⟨1002029, by rfl⟩ : syracuseStep 5344157 = 2004059) B2004059
theorem B1584155 : Blo 1561478 1584155 := bstep (se 1 (by rfl) ⟨1188116, by rfl⟩ : syracuseStep 1584155 = 2376233) B2376233
theorem B3517595 : Blo 1561478 3517595 := bstep (se 1 (by rfl) ⟨2638196, by rfl⟩ : syracuseStep 3517595 = 5276393) B5276393
theorem B8900543 : Blo 1561478 8900543 := bstep (se 1 (by rfl) ⟨6675407, by rfl⟩ : syracuseStep 8900543 = 13350815) B13350815
theorem B1758235 : Blo 1561478 1758235 := bstep (se 1 (by rfl) ⟨1318676, by rfl⟩ : syracuseStep 1758235 = 2637353) B2637353
theorem B15021287 : Blo 1561478 15021287 := bstep (se 1 (by rfl) ⟨11265965, by rfl⟩ : syracuseStep 15021287 = 22531931) B22531931
theorem B7910783 : Blo 1561478 7910783 := bstep (se 1 (by rfl) ⟨5933087, by rfl⟩ : syracuseStep 7910783 = 11866175) B11866175
theorem B10008191 : Blo 1561478 10008191 := bstep (se 1 (by rfl) ⟨7506143, by rfl⟩ : syracuseStep 10008191 = 15012287) B15012287
theorem B2636455 : Blo 1561478 2636455 := bstep (se 1 (by rfl) ⟨1977341, by rfl⟩ : syracuseStep 2636455 = 3954683) B3954683
theorem B2637103 : Blo 1561478 2637103 := bstep (se 1 (by rfl) ⟨1977827, by rfl⟩ : syracuseStep 2637103 = 3955655) B3955655
theorem B5930567 : Blo 1561478 5930567 := bstep (se 1 (by rfl) ⟨4447925, by rfl⟩ : syracuseStep 5930567 = 8895851) B8895851
theorem B3383035 : Blo 1561478 3383035 := bstep (se 1 (by rfl) ⟨2537276, by rfl⟩ : syracuseStep 3383035 = 5074553) B5074553
theorem B2342759 : Blo 1561478 2342759 := bstep (se 1 (by rfl) ⟨1757069, by rfl⟩ : syracuseStep 2342759 = 3514139) B3514139
theorem B11870063 : Blo 1561478 11870063 := bstep (se 1 (by rfl) ⟨8902547, by rfl⟩ : syracuseStep 11870063 = 17805095) B17805095
theorem B3515273 : Blo 1561478 3515273 := bstep (se 2 (by rfl) ⟨1318227, by rfl⟩ : syracuseStep 3515273 = 2636455) B2636455
theorem B1581630695 : Blo 1561478 1581630695 := bstep (se 1 (by rfl) ⟨1186223021, by rfl⟩ : syracuseStep 1581630695 = 2372446043) B2372446043
theorem B2344313 : Blo 1561478 2344313 := bstep (se 2 (by rfl) ⟨879117, by rfl⟩ : syracuseStep 2344313 = 1758235) B1758235
theorem B3516137 : Blo 1561478 3516137 := bstep (se 2 (by rfl) ⟨1318551, by rfl⟩ : syracuseStep 3516137 = 2637103) B2637103
theorem B17794889 : Blo 1561478 17794889 := bstep (se 2 (by rfl) ⟨6673083, by rfl⟩ : syracuseStep 17794889 = 13346167) B13346167
theorem B2967455 : Blo 1561478 2967455 := bstep (se 1 (by rfl) ⟨2225591, by rfl⟩ : syracuseStep 2967455 = 4451183) B4451183
theorem B2345063 : Blo 1561478 2345063 := bstep (se 1 (by rfl) ⟨1758797, by rfl⟩ : syracuseStep 2345063 = 3517595) B3517595
theorem B5933695 : Blo 1561478 5933695 := bstep (se 1 (by rfl) ⟨4450271, by rfl⟩ : syracuseStep 5933695 = 8900543) B8900543
theorem B5270399 : Blo 1561478 5270399 := bstep (se 1 (by rfl) ⟨3952799, by rfl⟩ : syracuseStep 5270399 = 7905599) B7905599
theorem B4451411 : Blo 1561478 4451411 := bstep (se 1 (by rfl) ⟨3338558, by rfl⟩ : syracuseStep 4451411 = 6677117) B6677117
theorem B10014191 : Blo 1561478 10014191 := bstep (se 1 (by rfl) ⟨7510643, by rfl⟩ : syracuseStep 10014191 = 15021287) B15021287
theorem B5271263 : Blo 1561478 5271263 := bstep (se 1 (by rfl) ⟨3953447, by rfl⟩ : syracuseStep 5271263 = 7906895) B7906895
theorem B6672127 : Blo 1561478 6672127 := bstep (se 1 (by rfl) ⟨5004095, by rfl⟩ : syracuseStep 6672127 = 10008191) B10008191
theorem B18042853 : Blo 1561478 18042853 := bstep (se 4 (by rfl) ⟨1691517, by rfl⟩ : syracuseStep 18042853 = 3383035) B3383035
theorem B3953711 : Blo 1561478 3953711 := bstep (se 1 (by rfl) ⟨2965283, by rfl⟩ : syracuseStep 3953711 = 5930567) B5930567
theorem B14251085 : Blo 1561478 14251085 := bstep (se 3 (by rfl) ⟨2672078, by rfl⟩ : syracuseStep 14251085 = 5344157) B5344157
theorem B1561839 : Blo 1561478 1561839 := bstep (se 1 (by rfl) ⟨1171379, by rfl⟩ : syracuseStep 1561839 = 2342759) B2342759
theorem B4224413 : Blo 1561478 4224413 := bstep (se 3 (by rfl) ⟨792077, by rfl⟩ : syracuseStep 4224413 = 1584155) B1584155
theorem B1562271 : Blo 1561478 1562271 := bstep (se 1 (by rfl) ⟨1171703, by rfl⟩ : syracuseStep 1562271 = 2343407) B2343407
theorem B25335575 : Blo 1561478 25335575 := bstep (se 1 (by rfl) ⟨19001681, by rfl⟩ : syracuseStep 25335575 = 38003363) B38003363
theorem B5273855 : Blo 1561478 5273855 := bstep (se 1 (by rfl) ⟨3955391, by rfl⟩ : syracuseStep 5273855 = 7910783) B7910783
theorem B1563343 : Blo 1561478 1563343 := bstep (se 1 (by rfl) ⟨1172507, by rfl⟩ : syracuseStep 1563343 = 2345015) B2345015
theorem B7913375 : Blo 1561478 7913375 := bstep (se 1 (by rfl) ⟨5935031, by rfl⟩ : syracuseStep 7913375 = 11870063) B11870063
theorem B2343515 : Blo 1561478 2343515 := bstep (se 1 (by rfl) ⟨1757636, by rfl⟩ : syracuseStep 2343515 = 3515273) B3515273
theorem B11265101 : Blo 1561478 11265101 := bstep (se 3 (by rfl) ⟨2112206, by rfl⟩ : syracuseStep 11265101 = 4224413) B4224413
theorem B2344091 : Blo 1561478 2344091 := bstep (se 1 (by rfl) ⟨1758068, by rfl⟩ : syracuseStep 2344091 = 3516137) B3516137
theorem B11863259 : Blo 1561478 11863259 := bstep (se 1 (by rfl) ⟨8897444, by rfl⟩ : syracuseStep 11863259 = 17794889) B17794889
theorem B3515903 : Blo 1561478 3515903 := bstep (se 1 (by rfl) ⟨2636927, by rfl⟩ : syracuseStep 3515903 = 5273855) B5273855
theorem B2967607 : Blo 1561478 2967607 := bstep (se 1 (by rfl) ⟨2225705, by rfl⟩ : syracuseStep 2967607 = 4451411) B4451411
theorem B1054420463 : Blo 1561478 1054420463 := bstep (se 1 (by rfl) ⟨790815347, by rfl⟩ : syracuseStep 1054420463 = 1581630695) B1581630695
theorem B24057137 : Blo 1561478 24057137 := bstep (se 2 (by rfl) ⟨9021426, by rfl⟩ : syracuseStep 24057137 = 18042853) B18042853
theorem B2635807 : Blo 1561478 2635807 := bstep (se 1 (by rfl) ⟨1976855, by rfl⟩ : syracuseStep 2635807 = 3953711) B3953711
theorem B9500723 : Blo 1561478 9500723 := bstep (se 1 (by rfl) ⟨7125542, by rfl⟩ : syracuseStep 9500723 = 14251085) B14251085
theorem B7911593 : Blo 1561478 7911593 := bstep (se 2 (by rfl) ⟨2966847, by rfl⟩ : syracuseStep 7911593 = 5933695) B5933695
theorem B1562875 : Blo 1561478 1562875 := bstep (se 1 (by rfl) ⟨1172156, by rfl⟩ : syracuseStep 1562875 = 2344313) B2344313
theorem B16890383 : Blo 1561478 16890383 := bstep (se 1 (by rfl) ⟨12667787, by rfl⟩ : syracuseStep 16890383 = 25335575) B25335575
theorem B1563375 : Blo 1561478 1563375 := bstep (se 1 (by rfl) ⟨1172531, by rfl⟩ : syracuseStep 1563375 = 2345063) B2345063
theorem B3513599 : Blo 1561478 3513599 := bstep (se 1 (by rfl) ⟨2635199, by rfl⟩ : syracuseStep 3513599 = 5270399) B5270399
theorem B6676127 : Blo 1561478 6676127 := bstep (se 1 (by rfl) ⟨5007095, by rfl⟩ : syracuseStep 6676127 = 10014191) B10014191
theorem B8896169 : Blo 1561478 8896169 := bstep (se 2 (by rfl) ⟨3336063, by rfl⟩ : syracuseStep 8896169 = 6672127) B6672127
theorem B7913213 : Blo 1561478 7913213 := bstep (se 3 (by rfl) ⟨1483727, by rfl⟩ : syracuseStep 7913213 = 2967455) B2967455
theorem B3514175 : Blo 1561478 3514175 := bstep (se 1 (by rfl) ⟨2635631, by rfl⟩ : syracuseStep 3514175 = 5271263) B5271263
theorem B5275583 : Blo 1561478 5275583 := bstep (se 1 (by rfl) ⟨3956687, by rfl⟩ : syracuseStep 5275583 = 7913375) B7913375
theorem B3514409 : Blo 1561478 3514409 := bstep (se 2 (by rfl) ⟨1317903, by rfl⟩ : syracuseStep 3514409 = 2635807) B2635807
theorem B3956809 : Blo 1561478 3956809 := bstep (se 2 (by rfl) ⟨1483803, by rfl⟩ : syracuseStep 3956809 = 2967607) B2967607
theorem B2343935 : Blo 1561478 2343935 := bstep (se 1 (by rfl) ⟨1757951, by rfl⟩ : syracuseStep 2343935 = 3515903) B3515903
theorem B6333815 : Blo 1561478 6333815 := bstep (se 1 (by rfl) ⟨4750361, by rfl⟩ : syracuseStep 6333815 = 9500723) B9500723
theorem B4450751 : Blo 1561478 4450751 := bstep (se 1 (by rfl) ⟨3338063, by rfl⟩ : syracuseStep 4450751 = 6676127) B6676127
theorem B3517055 : Blo 1561478 3517055 := bstep (se 1 (by rfl) ⟨2637791, by rfl⟩ : syracuseStep 3517055 = 5275583) B5275583
theorem B7908839 : Blo 1561478 7908839 := bstep (se 1 (by rfl) ⟨5931629, by rfl⟩ : syracuseStep 7908839 = 11863259) B11863259
theorem B11260255 : Blo 1561478 11260255 := bstep (se 1 (by rfl) ⟨8445191, by rfl⟩ : syracuseStep 11260255 = 16890383) B16890383
theorem B1562343 : Blo 1561478 1562343 := bstep (se 1 (by rfl) ⟨1171757, by rfl⟩ : syracuseStep 1562343 = 2343515) B2343515
theorem B7510067 : Blo 1561478 7510067 := bstep (se 1 (by rfl) ⟨5632550, by rfl⟩ : syracuseStep 7510067 = 11265101) B11265101
theorem B1562727 : Blo 1561478 1562727 := bstep (se 1 (by rfl) ⟨1172045, by rfl⟩ : syracuseStep 1562727 = 2344091) B2344091
theorem B16038091 : Blo 1561478 16038091 := bstep (se 1 (by rfl) ⟨12028568, by rfl⟩ : syracuseStep 16038091 = 24057137) B24057137
theorem B2811787901 : Blo 1561478 2811787901 := bstep (se 3 (by rfl) ⟨527210231, by rfl⟩ : syracuseStep 2811787901 = 1054420463) B1054420463
theorem B5274395 : Blo 1561478 5274395 := bstep (se 1 (by rfl) ⟨3955796, by rfl⟩ : syracuseStep 5274395 = 7911593) B7911593
theorem B2342399 : Blo 1561478 2342399 := bstep (se 1 (by rfl) ⟨1756799, by rfl⟩ : syracuseStep 2342399 = 3513599) B3513599
theorem B5930779 : Blo 1561478 5930779 := bstep (se 1 (by rfl) ⟨4448084, by rfl⟩ : syracuseStep 5930779 = 8896169) B8896169
theorem B5275475 : Blo 1561478 5275475 := bstep (se 1 (by rfl) ⟨3956606, by rfl⟩ : syracuseStep 5275475 = 7913213) B7913213
theorem B2342783 : Blo 1561478 2342783 := bstep (se 1 (by rfl) ⟨1757087, by rfl⟩ : syracuseStep 2342783 = 3514175) B3514175
theorem B2342939 : Blo 1561478 2342939 := bstep (se 1 (by rfl) ⟨1757204, by rfl⟩ : syracuseStep 2342939 = 3514409) B3514409
theorem B5275745 : Blo 1561478 5275745 := bstep (se 2 (by rfl) ⟨1978404, by rfl⟩ : syracuseStep 5275745 = 3956809) B3956809
theorem B5006711 : Blo 1561478 5006711 := bstep (se 1 (by rfl) ⟨3755033, by rfl⟩ : syracuseStep 5006711 = 7510067) B7510067
theorem B2967167 : Blo 1561478 2967167 := bstep (se 1 (by rfl) ⟨2225375, by rfl⟩ : syracuseStep 2967167 = 4450751) B4450751
theorem B2344703 : Blo 1561478 2344703 := bstep (se 1 (by rfl) ⟨1758527, by rfl⟩ : syracuseStep 2344703 = 3517055) B3517055
theorem B3516263 : Blo 1561478 3516263 := bstep (se 1 (by rfl) ⟨2637197, by rfl⟩ : syracuseStep 3516263 = 5274395) B5274395
theorem B7907705 : Blo 1561478 7907705 := bstep (se 2 (by rfl) ⟨2965389, by rfl⟩ : syracuseStep 7907705 = 5930779) B5930779
theorem B3516983 : Blo 1561478 3516983 := bstep (se 1 (by rfl) ⟨2637737, by rfl⟩ : syracuseStep 3516983 = 5275475) B5275475
theorem B21384121 : Blo 1561478 21384121 := bstep (se 2 (by rfl) ⟨8019045, by rfl⟩ : syracuseStep 21384121 = 16038091) B16038091
theorem B4222543 : Blo 1561478 4222543 := bstep (se 1 (by rfl) ⟨3166907, by rfl⟩ : syracuseStep 4222543 = 6333815) B6333815
theorem B5272559 : Blo 1561478 5272559 := bstep (se 1 (by rfl) ⟨3954419, by rfl⟩ : syracuseStep 5272559 = 7908839) B7908839
theorem B1561599 : Blo 1561478 1561599 := bstep (se 1 (by rfl) ⟨1171199, by rfl⟩ : syracuseStep 1561599 = 2342399) B2342399
theorem B1561855 : Blo 1561478 1561855 := bstep (se 1 (by rfl) ⟨1171391, by rfl⟩ : syracuseStep 1561855 = 2342783) B2342783
theorem B15013673 : Blo 1561478 15013673 := bstep (se 2 (by rfl) ⟨5630127, by rfl⟩ : syracuseStep 15013673 = 11260255) B11260255
theorem B1562623 : Blo 1561478 1562623 := bstep (se 1 (by rfl) ⟨1171967, by rfl⟩ : syracuseStep 1562623 = 2343935) B2343935
theorem B1874525267 : Blo 1561478 1874525267 := bstep (se 1 (by rfl) ⟨1405893950, by rfl⟩ : syracuseStep 1874525267 = 2811787901) B2811787901
theorem B3515039 : Blo 1561478 3515039 := bstep (se 1 (by rfl) ⟨2636279, by rfl⟩ : syracuseStep 3515039 = 5272559) B5272559
theorem B2344175 : Blo 1561478 2344175 := bstep (se 1 (by rfl) ⟨1758131, by rfl⟩ : syracuseStep 2344175 = 3516263) B3516263
theorem B2344655 : Blo 1561478 2344655 := bstep (se 1 (by rfl) ⟨1758491, by rfl⟩ : syracuseStep 2344655 = 3516983) B3516983
theorem B1249683511 : Blo 1561478 1249683511 := bstep (se 1 (by rfl) ⟨937262633, by rfl⟩ : syracuseStep 1249683511 = 1874525267) B1874525267
theorem B5630057 : Blo 1561478 5630057 := bstep (se 2 (by rfl) ⟨2111271, by rfl⟩ : syracuseStep 5630057 = 4222543) B4222543
theorem B3517163 : Blo 1561478 3517163 := bstep (se 1 (by rfl) ⟨2637872, by rfl⟩ : syracuseStep 3517163 = 5275745) B5275745
theorem B3337807 : Blo 1561478 3337807 := bstep (se 1 (by rfl) ⟨2503355, by rfl⟩ : syracuseStep 3337807 = 5006711) B5006711
theorem B1978111 : Blo 1561478 1978111 := bstep (se 1 (by rfl) ⟨1483583, by rfl⟩ : syracuseStep 1978111 = 2967167) B2967167
theorem B28512161 : Blo 1561478 28512161 := bstep (se 2 (by rfl) ⟨10692060, by rfl⟩ : syracuseStep 28512161 = 21384121) B21384121
theorem B5271803 : Blo 1561478 5271803 := bstep (se 1 (by rfl) ⟨3953852, by rfl⟩ : syracuseStep 5271803 = 7907705) B7907705
theorem B1561959 : Blo 1561478 1561959 := bstep (se 1 (by rfl) ⟨1171469, by rfl⟩ : syracuseStep 1561959 = 2342939) B2342939
theorem B1563135 : Blo 1561478 1563135 := bstep (se 1 (by rfl) ⟨1172351, by rfl⟩ : syracuseStep 1563135 = 2344703) B2344703
theorem B10009115 : Blo 1561478 10009115 := bstep (se 1 (by rfl) ⟨7506836, by rfl⟩ : syracuseStep 10009115 = 15013673) B15013673
theorem B1666244681 : Blo 1561478 1666244681 := bstep (se 2 (by rfl) ⟨624841755, by rfl⟩ : syracuseStep 1666244681 = 1249683511) B1249683511
theorem B3514535 : Blo 1561478 3514535 := bstep (se 1 (by rfl) ⟨2635901, by rfl⟩ : syracuseStep 3514535 = 5271803) B5271803
theorem B2343359 : Blo 1561478 2343359 := bstep (se 1 (by rfl) ⟨1757519, by rfl⟩ : syracuseStep 2343359 = 3515039) B3515039
theorem B3753371 : Blo 1561478 3753371 := bstep (se 1 (by rfl) ⟨2815028, by rfl⟩ : syracuseStep 3753371 = 5630057) B5630057
theorem B2344775 : Blo 1561478 2344775 := bstep (se 1 (by rfl) ⟨1758581, by rfl⟩ : syracuseStep 2344775 = 3517163) B3517163
theorem B4450409 : Blo 1561478 4450409 := bstep (se 2 (by rfl) ⟨1668903, by rfl⟩ : syracuseStep 4450409 = 3337807) B3337807
theorem B19008107 : Blo 1561478 19008107 := bstep (se 1 (by rfl) ⟨14256080, by rfl⟩ : syracuseStep 19008107 = 28512161) B28512161
theorem B6672743 : Blo 1561478 6672743 := bstep (se 1 (by rfl) ⟨5004557, by rfl⟩ : syracuseStep 6672743 = 10009115) B10009115
theorem B1562783 : Blo 1561478 1562783 := bstep (se 1 (by rfl) ⟨1172087, by rfl⟩ : syracuseStep 1562783 = 2344175) B2344175
theorem B1563103 : Blo 1561478 1563103 := bstep (se 1 (by rfl) ⟨1172327, by rfl⟩ : syracuseStep 1563103 = 2344655) B2344655
theorem B2637481 : Blo 1561478 2637481 := bstep (se 2 (by rfl) ⟨989055, by rfl⟩ : syracuseStep 2637481 = 1978111) B1978111
theorem B2343023 : Blo 1561478 2343023 := bstep (se 1 (by rfl) ⟨1757267, by rfl⟩ : syracuseStep 2343023 = 3514535) B3514535
theorem B4448495 : Blo 1561478 4448495 := bstep (se 1 (by rfl) ⟨3336371, by rfl⟩ : syracuseStep 4448495 = 6672743) B6672743
theorem B2966939 : Blo 1561478 2966939 := bstep (se 1 (by rfl) ⟨2225204, by rfl⟩ : syracuseStep 2966939 = 4450409) B4450409
theorem B3516641 : Blo 1561478 3516641 := bstep (se 2 (by rfl) ⟨1318740, by rfl⟩ : syracuseStep 3516641 = 2637481) B2637481
theorem B1110829787 : Blo 1561478 1110829787 := bstep (se 1 (by rfl) ⟨833122340, by rfl⟩ : syracuseStep 1110829787 = 1666244681) B1666244681
theorem B2502247 : Blo 1561478 2502247 := bstep (se 1 (by rfl) ⟨1876685, by rfl⟩ : syracuseStep 2502247 = 3753371) B3753371
theorem B1562239 : Blo 1561478 1562239 := bstep (se 1 (by rfl) ⟨1171679, by rfl⟩ : syracuseStep 1562239 = 2343359) B2343359
theorem B1563183 : Blo 1561478 1563183 := bstep (se 1 (by rfl) ⟨1172387, by rfl⟩ : syracuseStep 1563183 = 2344775) B2344775
theorem B12672071 : Blo 1561478 12672071 := bstep (se 1 (by rfl) ⟨9504053, by rfl⟩ : syracuseStep 12672071 = 19008107) B19008107
theorem B2965663 : Blo 1561478 2965663 := bstep (se 1 (by rfl) ⟨2224247, by rfl⟩ : syracuseStep 2965663 = 4448495) B4448495
theorem B2344427 : Blo 1561478 2344427 := bstep (se 1 (by rfl) ⟨1758320, by rfl⟩ : syracuseStep 2344427 = 3516641) B3516641
theorem B8448047 : Blo 1561478 8448047 := bstep (se 1 (by rfl) ⟨6336035, by rfl⟩ : syracuseStep 8448047 = 12672071) B12672071
theorem B3336329 : Blo 1561478 3336329 := bstep (se 2 (by rfl) ⟨1251123, by rfl⟩ : syracuseStep 3336329 = 2502247) B2502247
theorem B1977959 : Blo 1561478 1977959 := bstep (se 1 (by rfl) ⟨1483469, by rfl⟩ : syracuseStep 1977959 = 2966939) B2966939
theorem B740553191 : Blo 1561478 740553191 := bstep (se 1 (by rfl) ⟨555414893, by rfl⟩ : syracuseStep 740553191 = 1110829787) B1110829787
theorem B1562015 : Blo 1561478 1562015 := bstep (se 1 (by rfl) ⟨1171511, by rfl⟩ : syracuseStep 1562015 = 2343023) B2343023
theorem B8896877 : Blo 1561478 8896877 := bstep (se 3 (by rfl) ⟨1668164, by rfl⟩ : syracuseStep 8896877 = 3336329) B3336329
theorem B493702127 : Blo 1561478 493702127 := bstep (se 1 (by rfl) ⟨370276595, by rfl⟩ : syracuseStep 493702127 = 740553191) B740553191
theorem B5632031 : Blo 1561478 5632031 := bstep (se 1 (by rfl) ⟨4224023, by rfl⟩ : syracuseStep 5632031 = 8448047) B8448047
theorem B3954217 : Blo 1561478 3954217 := bstep (se 2 (by rfl) ⟨1482831, by rfl⟩ : syracuseStep 3954217 = 2965663) B2965663
theorem B1562951 : Blo 1561478 1562951 := bstep (se 1 (by rfl) ⟨1172213, by rfl⟩ : syracuseStep 1562951 = 2344427) B2344427
theorem B5274557 : Blo 1561478 5274557 := bstep (se 3 (by rfl) ⟨988979, by rfl⟩ : syracuseStep 5274557 = 1977959) B1977959
theorem B5931251 : Blo 1561478 5931251 := bstep (se 1 (by rfl) ⟨4448438, by rfl⟩ : syracuseStep 5931251 = 8896877) B8896877
theorem B3516371 : Blo 1561478 3516371 := bstep (se 1 (by rfl) ⟨2637278, by rfl⟩ : syracuseStep 3516371 = 5274557) B5274557
theorem B3754687 : Blo 1561478 3754687 := bstep (se 1 (by rfl) ⟨2816015, by rfl⟩ : syracuseStep 3754687 = 5632031) B5632031
theorem B329134751 : Blo 1561478 329134751 := bstep (se 1 (by rfl) ⟨246851063, by rfl⟩ : syracuseStep 329134751 = 493702127) B493702127
theorem B5272289 : Blo 1561478 5272289 := bstep (se 2 (by rfl) ⟨1977108, by rfl⟩ : syracuseStep 5272289 = 3954217) B3954217
theorem B219423167 : Blo 1561478 219423167 := bstep (se 1 (by rfl) ⟨164567375, by rfl⟩ : syracuseStep 219423167 = 329134751) B329134751
theorem B3514859 : Blo 1561478 3514859 := bstep (se 1 (by rfl) ⟨2636144, by rfl⟩ : syracuseStep 3514859 = 5272289) B5272289
theorem B5006249 : Blo 1561478 5006249 := bstep (se 2 (by rfl) ⟨1877343, by rfl⟩ : syracuseStep 5006249 = 3754687) B3754687
theorem B2344247 : Blo 1561478 2344247 := bstep (se 1 (by rfl) ⟨1758185, by rfl⟩ : syracuseStep 2344247 = 3516371) B3516371
theorem B3954167 : Blo 1561478 3954167 := bstep (se 1 (by rfl) ⟨2965625, by rfl⟩ : syracuseStep 3954167 = 5931251) B5931251
theorem B2343239 : Blo 1561478 2343239 := bstep (se 1 (by rfl) ⟨1757429, by rfl⟩ : syracuseStep 2343239 = 3514859) B3514859
theorem B3337499 : Blo 1561478 3337499 := bstep (se 1 (by rfl) ⟨2503124, by rfl⟩ : syracuseStep 3337499 = 5006249) B5006249
theorem B146282111 : Blo 1561478 146282111 := bstep (se 1 (by rfl) ⟨109711583, by rfl⟩ : syracuseStep 146282111 = 219423167) B219423167
theorem B1562831 : Blo 1561478 1562831 := bstep (se 1 (by rfl) ⟨1172123, by rfl⟩ : syracuseStep 1562831 = 2344247) B2344247
theorem B2636111 : Blo 1561478 2636111 := bstep (se 1 (by rfl) ⟨1977083, by rfl⟩ : syracuseStep 2636111 = 3954167) B3954167
theorem B97521407 : Blo 1561478 97521407 := bstep (se 1 (by rfl) ⟨73141055, by rfl⟩ : syracuseStep 97521407 = 146282111) B146282111
theorem B1757407 : Blo 1561478 1757407 := bstep (se 1 (by rfl) ⟨1318055, by rfl⟩ : syracuseStep 1757407 = 2636111) B2636111
theorem B2224999 : Blo 1561478 2224999 := bstep (se 1 (by rfl) ⟨1668749, by rfl⟩ : syracuseStep 2224999 = 3337499) B3337499
theorem B1562159 : Blo 1561478 1562159 := bstep (se 1 (by rfl) ⟨1171619, by rfl⟩ : syracuseStep 1562159 = 2343239) B2343239
theorem B2343209 : Blo 1561478 2343209 := bstep (se 2 (by rfl) ⟨878703, by rfl⟩ : syracuseStep 2343209 = 1757407) B1757407
theorem B65014271 : Blo 1561478 65014271 := bstep (se 1 (by rfl) ⟨48760703, by rfl⟩ : syracuseStep 65014271 = 97521407) B97521407
theorem B11866661 : Blo 1561478 11866661 := bstep (se 4 (by rfl) ⟨1112499, by rfl⟩ : syracuseStep 11866661 = 2224999) B2224999
theorem B1562139 : Blo 1561478 1562139 := bstep (se 1 (by rfl) ⟨1171604, by rfl⟩ : syracuseStep 1562139 = 2343209) B2343209
theorem B7911107 : Blo 1561478 7911107 := bstep (se 1 (by rfl) ⟨5933330, by rfl⟩ : syracuseStep 7911107 = 11866661) B11866661
theorem B43342847 : Blo 1561478 43342847 := bstep (se 1 (by rfl) ⟨32507135, by rfl⟩ : syracuseStep 43342847 = 65014271) B65014271
theorem B28895231 : Blo 1561478 28895231 := bstep (se 1 (by rfl) ⟨21671423, by rfl⟩ : syracuseStep 28895231 = 43342847) B43342847
theorem B5274071 : Blo 1561478 5274071 := bstep (se 1 (by rfl) ⟨3955553, by rfl⟩ : syracuseStep 5274071 = 7911107) B7911107
theorem B3516047 : Blo 1561478 3516047 := bstep (se 1 (by rfl) ⟨2637035, by rfl⟩ : syracuseStep 3516047 = 5274071) B5274071
theorem B77053949 : Blo 1561478 77053949 := bstep (se 3 (by rfl) ⟨14447615, by rfl⟩ : syracuseStep 77053949 = 28895231) B28895231
theorem B2344031 : Blo 1561478 2344031 := bstep (se 1 (by rfl) ⟨1758023, by rfl⟩ : syracuseStep 2344031 = 3516047) B3516047
theorem B51369299 : Blo 1561478 51369299 := bstep (se 1 (by rfl) ⟨38526974, by rfl⟩ : syracuseStep 51369299 = 77053949) B77053949
theorem B34246199 : Blo 1561478 34246199 := bstep (se 1 (by rfl) ⟨25684649, by rfl⟩ : syracuseStep 34246199 = 51369299) B51369299
theorem B1562687 : Blo 1561478 1562687 := bstep (se 1 (by rfl) ⟨1172015, by rfl⟩ : syracuseStep 1562687 = 2344031) B2344031
theorem B91323197 : Blo 1561478 91323197 := bstep (se 3 (by rfl) ⟨17123099, by rfl⟩ : syracuseStep 91323197 = 34246199) B34246199
theorem B60882131 : Blo 1561478 60882131 := bstep (se 1 (by rfl) ⟨45661598, by rfl⟩ : syracuseStep 60882131 = 91323197) B91323197
theorem B40588087 : Blo 1561478 40588087 := bstep (se 1 (by rfl) ⟨30441065, by rfl⟩ : syracuseStep 40588087 = 60882131) B60882131
theorem B54117449 : Blo 1561478 54117449 := bstep (se 2 (by rfl) ⟨20294043, by rfl⟩ : syracuseStep 54117449 = 40588087) B40588087
theorem B36078299 : Blo 1561478 36078299 := bstep (se 1 (by rfl) ⟨27058724, by rfl⟩ : syracuseStep 36078299 = 54117449) B54117449
theorem B24052199 : Blo 1561478 24052199 := bstep (se 1 (by rfl) ⟨18039149, by rfl⟩ : syracuseStep 24052199 = 36078299) B36078299
theorem B64139197 : Blo 1561478 64139197 := bstep (se 3 (by rfl) ⟨12026099, by rfl⟩ : syracuseStep 64139197 = 24052199) B24052199
theorem B85518929 : Blo 1561478 85518929 := bstep (se 2 (by rfl) ⟨32069598, by rfl⟩ : syracuseStep 85518929 = 64139197) B64139197
theorem B57012619 : Blo 1561478 57012619 := bstep (se 1 (by rfl) ⟨42759464, by rfl⟩ : syracuseStep 57012619 = 85518929) B85518929
theorem B76016825 : Blo 1561478 76016825 := bstep (se 2 (by rfl) ⟨28506309, by rfl⟩ : syracuseStep 76016825 = 57012619) B57012619
theorem B50677883 : Blo 1561478 50677883 := bstep (se 1 (by rfl) ⟨38008412, by rfl⟩ : syracuseStep 50677883 = 76016825) B76016825
theorem B33785255 : Blo 1561478 33785255 := bstep (se 1 (by rfl) ⟨25338941, by rfl⟩ : syracuseStep 33785255 = 50677883) B50677883
theorem B22523503 : Blo 1561478 22523503 := bstep (se 1 (by rfl) ⟨16892627, by rfl⟩ : syracuseStep 22523503 = 33785255) B33785255
theorem B30031337 : Blo 1561478 30031337 := bstep (se 2 (by rfl) ⟨11261751, by rfl⟩ : syracuseStep 30031337 = 22523503) B22523503
theorem B20020891 : Blo 1561478 20020891 := bstep (se 1 (by rfl) ⟨15015668, by rfl⟩ : syracuseStep 20020891 = 30031337) B30031337
theorem B26694521 : Blo 1561478 26694521 := bstep (se 2 (by rfl) ⟨10010445, by rfl⟩ : syracuseStep 26694521 = 20020891) B20020891
theorem B17796347 : Blo 1561478 17796347 := bstep (se 1 (by rfl) ⟨13347260, by rfl⟩ : syracuseStep 17796347 = 26694521) B26694521
theorem B11864231 : Blo 1561478 11864231 := bstep (se 1 (by rfl) ⟨8898173, by rfl⟩ : syracuseStep 11864231 = 17796347) B17796347
theorem B7909487 : Blo 1561478 7909487 := bstep (se 1 (by rfl) ⟨5932115, by rfl⟩ : syracuseStep 7909487 = 11864231) B11864231
theorem B5272991 : Blo 1561478 5272991 := bstep (se 1 (by rfl) ⟨3954743, by rfl⟩ : syracuseStep 5272991 = 7909487) B7909487
theorem B3515327 : Blo 1561478 3515327 := bstep (se 1 (by rfl) ⟨2636495, by rfl⟩ : syracuseStep 3515327 = 5272991) B5272991
theorem B2343551 : Blo 1561478 2343551 := bstep (se 1 (by rfl) ⟨1757663, by rfl⟩ : syracuseStep 2343551 = 3515327) B3515327
theorem B1562367 : Blo 1561478 1562367 := bstep (se 1 (by rfl) ⟨1171775, by rfl⟩ : syracuseStep 1562367 = 2343551) B2343551

theorem C0 (j : ℕ) (h1 : 390369 ≤ j) (h2 : j ≤ 390868) : Blo 1561478 (4 * j + 3) := by
  interval_cases j
  · exact B1561479
  · exact B1561483
  · exact B1561487
  · exact B1561491
  · exact B1561495
  · exact B1561499
  · exact B1561503
  · exact B1561507
  · exact B1561511
  · exact B1561515
  · exact B1561519
  · exact B1561523
  · exact B1561527
  · exact B1561531
  · exact B1561535
  · exact B1561539
  · exact B1561543
  · exact B1561547
  · exact B1561551
  · exact B1561555
  · exact B1561559
  · exact B1561563
  · exact B1561567
  · exact B1561571
  · exact B1561575
  · exact B1561579
  · exact B1561583
  · exact B1561587
  · exact B1561591
  · exact B1561595
  · exact B1561599
  · exact B1561603
  · exact B1561607
  · exact B1561611
  · exact B1561615
  · exact B1561619
  · exact B1561623
  · exact B1561627
  · exact B1561631
  · exact B1561635
  · exact B1561639
  · exact B1561643
  · exact B1561647
  · exact B1561651
  · exact B1561655
  · exact B1561659
  · exact B1561663
  · exact B1561667
  · exact B1561671
  · exact B1561675
  · exact B1561679
  · exact B1561683
  · exact B1561687
  · exact B1561691
  · exact B1561695
  · exact B1561699
  · exact B1561703
  · exact B1561707
  · exact B1561711
  · exact B1561715
  · exact B1561719
  · exact B1561723
  · exact B1561727
  · exact B1561731
  · exact B1561735
  · exact B1561739
  · exact B1561743
  · exact B1561747
  · exact B1561751
  · exact B1561755
  · exact B1561759
  · exact B1561763
  · exact B1561767
  · exact B1561771
  · exact B1561775
  · exact B1561779
  · exact B1561783
  · exact B1561787
  · exact B1561791
  · exact B1561795
  · exact B1561799
  · exact B1561803
  · exact B1561807
  · exact B1561811
  · exact B1561815
  · exact B1561819
  · exact B1561823
  · exact B1561827
  · exact B1561831
  · exact B1561835
  · exact B1561839
  · exact B1561843
  · exact B1561847
  · exact B1561851
  · exact B1561855
  · exact B1561859
  · exact B1561863
  · exact B1561867
  · exact B1561871
  · exact B1561875
  · exact B1561879
  · exact B1561883
  · exact B1561887
  · exact B1561891
  · exact B1561895
  · exact B1561899
  · exact B1561903
  · exact B1561907
  · exact B1561911
  · exact B1561915
  · exact B1561919
  · exact B1561923
  · exact B1561927
  · exact B1561931
  · exact B1561935
  · exact B1561939
  · exact B1561943
  · exact B1561947
  · exact B1561951
  · exact B1561955
  · exact B1561959
  · exact B1561963
  · exact B1561967
  · exact B1561971
  · exact B1561975
  · exact B1561979
  · exact B1561983
  · exact B1561987
  · exact B1561991
  · exact B1561995
  · exact B1561999
  · exact B1562003
  · exact B1562007
  · exact B1562011
  · exact B1562015
  · exact B1562019
  · exact B1562023
  · exact B1562027
  · exact B1562031
  · exact B1562035
  · exact B1562039
  · exact B1562043
  · exact B1562047
  · exact B1562051
  · exact B1562055
  · exact B1562059
  · exact B1562063
  · exact B1562067
  · exact B1562071
  · exact B1562075
  · exact B1562079
  · exact B1562083
  · exact B1562087
  · exact B1562091
  · exact B1562095
  · exact B1562099
  · exact B1562103
  · exact B1562107
  · exact B1562111
  · exact B1562115
  · exact B1562119
  · exact B1562123
  · exact B1562127
  · exact B1562131
  · exact B1562135
  · exact B1562139
  · exact B1562143
  · exact B1562147
  · exact B1562151
  · exact B1562155
  · exact B1562159
  · exact B1562163
  · exact B1562167
  · exact B1562171
  · exact B1562175
  · exact B1562179
  · exact B1562183
  · exact B1562187
  · exact B1562191
  · exact B1562195
  · exact B1562199
  · exact B1562203
  · exact B1562207
  · exact B1562211
  · exact B1562215
  · exact B1562219
  · exact B1562223
  · exact B1562227
  · exact B1562231
  · exact B1562235
  · exact B1562239
  · exact B1562243
  · exact B1562247
  · exact B1562251
  · exact B1562255
  · exact B1562259
  · exact B1562263
  · exact B1562267
  · exact B1562271
  · exact B1562275
  · exact B1562279
  · exact B1562283
  · exact B1562287
  · exact B1562291
  · exact B1562295
  · exact B1562299
  · exact B1562303
  · exact B1562307
  · exact B1562311
  · exact B1562315
  · exact B1562319
  · exact B1562323
  · exact B1562327
  · exact B1562331
  · exact B1562335
  · exact B1562339
  · exact B1562343
  · exact B1562347
  · exact B1562351
  · exact B1562355
  · exact B1562359
  · exact B1562363
  · exact B1562367
  · exact B1562371
  · exact B1562375
  · exact B1562379
  · exact B1562383
  · exact B1562387
  · exact B1562391
  · exact B1562395
  · exact B1562399
  · exact B1562403
  · exact B1562407
  · exact B1562411
  · exact B1562415
  · exact B1562419
  · exact B1562423
  · exact B1562427
  · exact B1562431
  · exact B1562435
  · exact B1562439
  · exact B1562443
  · exact B1562447
  · exact B1562451
  · exact B1562455
  · exact B1562459
  · exact B1562463
  · exact B1562467
  · exact B1562471
  · exact B1562475
  · exact B1562479
  · exact B1562483
  · exact B1562487
  · exact B1562491
  · exact B1562495
  · exact B1562499
  · exact B1562503
  · exact B1562507
  · exact B1562511
  · exact B1562515
  · exact B1562519
  · exact B1562523
  · exact B1562527
  · exact B1562531
  · exact B1562535
  · exact B1562539
  · exact B1562543
  · exact B1562547
  · exact B1562551
  · exact B1562555
  · exact B1562559
  · exact B1562563
  · exact B1562567
  · exact B1562571
  · exact B1562575
  · exact B1562579
  · exact B1562583
  · exact B1562587
  · exact B1562591
  · exact B1562595
  · exact B1562599
  · exact B1562603
  · exact B1562607
  · exact B1562611
  · exact B1562615
  · exact B1562619
  · exact B1562623
  · exact B1562627
  · exact B1562631
  · exact B1562635
  · exact B1562639
  · exact B1562643
  · exact B1562647
  · exact B1562651
  · exact B1562655
  · exact B1562659
  · exact B1562663
  · exact B1562667
  · exact B1562671
  · exact B1562675
  · exact B1562679
  · exact B1562683
  · exact B1562687
  · exact B1562691
  · exact B1562695
  · exact B1562699
  · exact B1562703
  · exact B1562707
  · exact B1562711
  · exact B1562715
  · exact B1562719
  · exact B1562723
  · exact B1562727
  · exact B1562731
  · exact B1562735
  · exact B1562739
  · exact B1562743
  · exact B1562747
  · exact B1562751
  · exact B1562755
  · exact B1562759
  · exact B1562763
  · exact B1562767
  · exact B1562771
  · exact B1562775
  · exact B1562779
  · exact B1562783
  · exact B1562787
  · exact B1562791
  · exact B1562795
  · exact B1562799
  · exact B1562803
  · exact B1562807
  · exact B1562811
  · exact B1562815
  · exact B1562819
  · exact B1562823
  · exact B1562827
  · exact B1562831
  · exact B1562835
  · exact B1562839
  · exact B1562843
  · exact B1562847
  · exact B1562851
  · exact B1562855
  · exact B1562859
  · exact B1562863
  · exact B1562867
  · exact B1562871
  · exact B1562875
  · exact B1562879
  · exact B1562883
  · exact B1562887
  · exact B1562891
  · exact B1562895
  · exact B1562899
  · exact B1562903
  · exact B1562907
  · exact B1562911
  · exact B1562915
  · exact B1562919
  · exact B1562923
  · exact B1562927
  · exact B1562931
  · exact B1562935
  · exact B1562939
  · exact B1562943
  · exact B1562947
  · exact B1562951
  · exact B1562955
  · exact B1562959
  · exact B1562963
  · exact B1562967
  · exact B1562971
  · exact B1562975
  · exact B1562979
  · exact B1562983
  · exact B1562987
  · exact B1562991
  · exact B1562995
  · exact B1562999
  · exact B1563003
  · exact B1563007
  · exact B1563011
  · exact B1563015
  · exact B1563019
  · exact B1563023
  · exact B1563027
  · exact B1563031
  · exact B1563035
  · exact B1563039
  · exact B1563043
  · exact B1563047
  · exact B1563051
  · exact B1563055
  · exact B1563059
  · exact B1563063
  · exact B1563067
  · exact B1563071
  · exact B1563075
  · exact B1563079
  · exact B1563083
  · exact B1563087
  · exact B1563091
  · exact B1563095
  · exact B1563099
  · exact B1563103
  · exact B1563107
  · exact B1563111
  · exact B1563115
  · exact B1563119
  · exact B1563123
  · exact B1563127
  · exact B1563131
  · exact B1563135
  · exact B1563139
  · exact B1563143
  · exact B1563147
  · exact B1563151
  · exact B1563155
  · exact B1563159
  · exact B1563163
  · exact B1563167
  · exact B1563171
  · exact B1563175
  · exact B1563179
  · exact B1563183
  · exact B1563187
  · exact B1563191
  · exact B1563195
  · exact B1563199
  · exact B1563203
  · exact B1563207
  · exact B1563211
  · exact B1563215
  · exact B1563219
  · exact B1563223
  · exact B1563227
  · exact B1563231
  · exact B1563235
  · exact B1563239
  · exact B1563243
  · exact B1563247
  · exact B1563251
  · exact B1563255
  · exact B1563259
  · exact B1563263
  · exact B1563267
  · exact B1563271
  · exact B1563275
  · exact B1563279
  · exact B1563283
  · exact B1563287
  · exact B1563291
  · exact B1563295
  · exact B1563299
  · exact B1563303
  · exact B1563307
  · exact B1563311
  · exact B1563315
  · exact B1563319
  · exact B1563323
  · exact B1563327
  · exact B1563331
  · exact B1563335
  · exact B1563339
  · exact B1563343
  · exact B1563347
  · exact B1563351
  · exact B1563355
  · exact B1563359
  · exact B1563363
  · exact B1563367
  · exact B1563371
  · exact B1563375
  · exact B1563379
  · exact B1563383
  · exact B1563387
  · exact B1563391
  · exact B1563395
  · exact B1563399
  · exact B1563403
  · exact B1563407
  · exact B1563411
  · exact B1563415
  · exact B1563419
  · exact B1563423
  · exact B1563427
  · exact B1563431
  · exact B1563435
  · exact B1563439
  · exact B1563443
  · exact B1563447
  · exact B1563451
  · exact B1563455
  · exact B1563459
  · exact B1563463
  · exact B1563467
  · exact B1563471
  · exact B1563475

theorem solution (m : ℕ) (hlo : 1561478 ≤ m) (hhi : m ≤ 1563478) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 390369 ≤ j := by omega
    have hj2 : j ≤ 390868 := by omega
    have hb : Blo 1561478 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
