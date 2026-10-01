-- Prove2me | solution 1 for syracuse_descends_range_2163435_2165435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:17:39.926777+00:00
-- url     : https://prove2.me/submissions/53aa8980-f28f-4061-929c-1f75c159e058

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

theorem B2433865 : Blo 2163435 2433865 := bbase (se 2 (by rfl) ⟨912699, by rfl⟩ : syracuseStep 2433865 = 1825399) (by norm_num)
theorem B3245153 : Blo 2163435 3245153 := bstep (se 2 (by rfl) ⟨1216932, by rfl⟩ : syracuseStep 3245153 = 2433865) B2433865
theorem B2163435 : Blo 2163435 2163435 := bstep (se 1 (by rfl) ⟨1622576, by rfl⟩ : syracuseStep 2163435 = 3245153) B3245153
theorem B6244789 : Blo 2163435 6244789 := bbase (se 5 (by rfl) ⟨292724, by rfl⟩ : syracuseStep 6244789 = 585449) (by norm_num)
theorem B8326385 : Blo 2163435 8326385 := bstep (se 2 (by rfl) ⟨3122394, by rfl⟩ : syracuseStep 8326385 = 6244789) B6244789
theorem B5550923 : Blo 2163435 5550923 := bstep (se 1 (by rfl) ⟨4163192, by rfl⟩ : syracuseStep 5550923 = 8326385) B8326385
theorem B3700615 : Blo 2163435 3700615 := bstep (se 1 (by rfl) ⟨2775461, by rfl⟩ : syracuseStep 3700615 = 5550923) B5550923
theorem B4934153 : Blo 2163435 4934153 := bstep (se 2 (by rfl) ⟨1850307, by rfl⟩ : syracuseStep 4934153 = 3700615) B3700615
theorem B13157741 : Blo 2163435 13157741 := bstep (se 3 (by rfl) ⟨2467076, by rfl⟩ : syracuseStep 13157741 = 4934153) B4934153
theorem B8771827 : Blo 2163435 8771827 := bstep (se 1 (by rfl) ⟨6578870, by rfl⟩ : syracuseStep 8771827 = 13157741) B13157741
theorem B11695769 : Blo 2163435 11695769 := bstep (se 2 (by rfl) ⟨4385913, by rfl⟩ : syracuseStep 11695769 = 8771827) B8771827
theorem B7797179 : Blo 2163435 7797179 := bstep (se 1 (by rfl) ⟨5847884, by rfl⟩ : syracuseStep 7797179 = 11695769) B11695769
theorem B20792477 : Blo 2163435 20792477 := bstep (se 3 (by rfl) ⟨3898589, by rfl⟩ : syracuseStep 20792477 = 7797179) B7797179
theorem B13861651 : Blo 2163435 13861651 := bstep (se 1 (by rfl) ⟨10396238, by rfl⟩ : syracuseStep 13861651 = 20792477) B20792477
theorem B18482201 : Blo 2163435 18482201 := bstep (se 2 (by rfl) ⟨6930825, by rfl⟩ : syracuseStep 18482201 = 13861651) B13861651
theorem B12321467 : Blo 2163435 12321467 := bstep (se 1 (by rfl) ⟨9241100, by rfl⟩ : syracuseStep 12321467 = 18482201) B18482201
theorem B8214311 : Blo 2163435 8214311 := bstep (se 1 (by rfl) ⟨6160733, by rfl⟩ : syracuseStep 8214311 = 12321467) B12321467
theorem B5476207 : Blo 2163435 5476207 := bstep (se 1 (by rfl) ⟨4107155, by rfl⟩ : syracuseStep 5476207 = 8214311) B8214311
theorem B7301609 : Blo 2163435 7301609 := bstep (se 2 (by rfl) ⟨2738103, by rfl⟩ : syracuseStep 7301609 = 5476207) B5476207
theorem B4867739 : Blo 2163435 4867739 := bstep (se 1 (by rfl) ⟨3650804, by rfl⟩ : syracuseStep 4867739 = 7301609) B7301609
theorem B3245159 : Blo 2163435 3245159 := bstep (se 1 (by rfl) ⟨2433869, by rfl⟩ : syracuseStep 3245159 = 4867739) B4867739
theorem B2163439 : Blo 2163435 2163439 := bstep (se 1 (by rfl) ⟨1622579, by rfl⟩ : syracuseStep 2163439 = 3245159) B3245159
theorem B3245165 : Blo 2163435 3245165 := bbase (se 3 (by rfl) ⟨608468, by rfl⟩ : syracuseStep 3245165 = 1216937) (by norm_num)
theorem B2163443 : Blo 2163435 2163443 := bstep (se 1 (by rfl) ⟨1622582, by rfl⟩ : syracuseStep 2163443 = 3245165) B3245165
theorem B4867757 : Blo 2163435 4867757 := bbase (se 3 (by rfl) ⟨912704, by rfl⟩ : syracuseStep 4867757 = 1825409) (by norm_num)
theorem B3245171 : Blo 2163435 3245171 := bstep (se 1 (by rfl) ⟨2433878, by rfl⟩ : syracuseStep 3245171 = 4867757) B4867757
theorem B2163447 : Blo 2163435 2163447 := bstep (se 1 (by rfl) ⟨1622585, by rfl⟩ : syracuseStep 2163447 = 3245171) B3245171
theorem B3898613 : Blo 2163435 3898613 := bbase (se 5 (by rfl) ⟨182747, by rfl⟩ : syracuseStep 3898613 = 365495) (by norm_num)
theorem B2599075 : Blo 2163435 2599075 := bstep (se 1 (by rfl) ⟨1949306, by rfl⟩ : syracuseStep 2599075 = 3898613) B3898613
theorem B3465433 : Blo 2163435 3465433 := bstep (se 2 (by rfl) ⟨1299537, by rfl⟩ : syracuseStep 3465433 = 2599075) B2599075
theorem B4620577 : Blo 2163435 4620577 := bstep (se 2 (by rfl) ⟨1732716, by rfl⟩ : syracuseStep 4620577 = 3465433) B3465433
theorem B6160769 : Blo 2163435 6160769 := bstep (se 2 (by rfl) ⟨2310288, by rfl⟩ : syracuseStep 6160769 = 4620577) B4620577
theorem B4107179 : Blo 2163435 4107179 := bstep (se 1 (by rfl) ⟨3080384, by rfl⟩ : syracuseStep 4107179 = 6160769) B6160769
theorem B2738119 : Blo 2163435 2738119 := bstep (se 1 (by rfl) ⟨2053589, by rfl⟩ : syracuseStep 2738119 = 4107179) B4107179
theorem B3650825 : Blo 2163435 3650825 := bstep (se 2 (by rfl) ⟨1369059, by rfl⟩ : syracuseStep 3650825 = 2738119) B2738119
theorem B2433883 : Blo 2163435 2433883 := bstep (se 1 (by rfl) ⟨1825412, by rfl⟩ : syracuseStep 2433883 = 3650825) B3650825
theorem B3245177 : Blo 2163435 3245177 := bstep (se 2 (by rfl) ⟨1216941, by rfl⟩ : syracuseStep 3245177 = 2433883) B2433883
theorem B2163451 : Blo 2163435 2163451 := bstep (se 1 (by rfl) ⟨1622588, by rfl⟩ : syracuseStep 2163451 = 3245177) B3245177
theorem B20792629 : Blo 2163435 20792629 := bbase (se 5 (by rfl) ⟨974654, by rfl⟩ : syracuseStep 20792629 = 1949309) (by norm_num)
theorem B27723505 : Blo 2163435 27723505 := bstep (se 2 (by rfl) ⟨10396314, by rfl⟩ : syracuseStep 27723505 = 20792629) B20792629
theorem B36964673 : Blo 2163435 36964673 := bstep (se 2 (by rfl) ⟨13861752, by rfl⟩ : syracuseStep 36964673 = 27723505) B27723505
theorem B24643115 : Blo 2163435 24643115 := bstep (se 1 (by rfl) ⟨18482336, by rfl⟩ : syracuseStep 24643115 = 36964673) B36964673
theorem B16428743 : Blo 2163435 16428743 := bstep (se 1 (by rfl) ⟨12321557, by rfl⟩ : syracuseStep 16428743 = 24643115) B24643115
theorem B10952495 : Blo 2163435 10952495 := bstep (se 1 (by rfl) ⟨8214371, by rfl⟩ : syracuseStep 10952495 = 16428743) B16428743
theorem B7301663 : Blo 2163435 7301663 := bstep (se 1 (by rfl) ⟨5476247, by rfl⟩ : syracuseStep 7301663 = 10952495) B10952495
theorem B4867775 : Blo 2163435 4867775 := bstep (se 1 (by rfl) ⟨3650831, by rfl⟩ : syracuseStep 4867775 = 7301663) B7301663
theorem B3245183 : Blo 2163435 3245183 := bstep (se 1 (by rfl) ⟨2433887, by rfl⟩ : syracuseStep 3245183 = 4867775) B4867775
theorem B2163455 : Blo 2163435 2163455 := bstep (se 1 (by rfl) ⟨1622591, by rfl⟩ : syracuseStep 2163455 = 3245183) B3245183
theorem B3245189 : Blo 2163435 3245189 := bbase (se 4 (by rfl) ⟨304236, by rfl⟩ : syracuseStep 3245189 = 608473) (by norm_num)
theorem B2163459 : Blo 2163435 2163459 := bstep (se 1 (by rfl) ⟨1622594, by rfl⟩ : syracuseStep 2163459 = 3245189) B3245189
theorem B3650845 : Blo 2163435 3650845 := bbase (se 3 (by rfl) ⟨684533, by rfl⟩ : syracuseStep 3650845 = 1369067) (by norm_num)
theorem B4867793 : Blo 2163435 4867793 := bstep (se 2 (by rfl) ⟨1825422, by rfl⟩ : syracuseStep 4867793 = 3650845) B3650845
theorem B3245195 : Blo 2163435 3245195 := bstep (se 1 (by rfl) ⟨2433896, by rfl⟩ : syracuseStep 3245195 = 4867793) B4867793
theorem B2163463 : Blo 2163435 2163463 := bstep (se 1 (by rfl) ⟨1622597, by rfl⟩ : syracuseStep 2163463 = 3245195) B3245195
theorem B2433901 : Blo 2163435 2433901 := bbase (se 3 (by rfl) ⟨456356, by rfl⟩ : syracuseStep 2433901 = 912713) (by norm_num)
theorem B3245201 : Blo 2163435 3245201 := bstep (se 2 (by rfl) ⟨1216950, by rfl⟩ : syracuseStep 3245201 = 2433901) B2433901
theorem B2163467 : Blo 2163435 2163467 := bstep (se 1 (by rfl) ⟨1622600, by rfl⟩ : syracuseStep 2163467 = 3245201) B3245201
theorem B7301717 : Blo 2163435 7301717 := bbase (se 8 (by rfl) ⟨42783, by rfl⟩ : syracuseStep 7301717 = 85567) (by norm_num)
theorem B4867811 : Blo 2163435 4867811 := bstep (se 1 (by rfl) ⟨3650858, by rfl⟩ : syracuseStep 4867811 = 7301717) B7301717
theorem B3245207 : Blo 2163435 3245207 := bstep (se 1 (by rfl) ⟨2433905, by rfl⟩ : syracuseStep 3245207 = 4867811) B4867811
theorem B2163471 : Blo 2163435 2163471 := bstep (se 1 (by rfl) ⟨1622603, by rfl⟩ : syracuseStep 2163471 = 3245207) B3245207
theorem B3245213 : Blo 2163435 3245213 := bbase (se 3 (by rfl) ⟨608477, by rfl⟩ : syracuseStep 3245213 = 1216955) (by norm_num)
theorem B2163475 : Blo 2163435 2163475 := bstep (se 1 (by rfl) ⟨1622606, by rfl⟩ : syracuseStep 2163475 = 3245213) B3245213
theorem B4867829 : Blo 2163435 4867829 := bbase (se 5 (by rfl) ⟨228179, by rfl⟩ : syracuseStep 4867829 = 456359) (by norm_num)
theorem B3245219 : Blo 2163435 3245219 := bstep (se 1 (by rfl) ⟨2433914, by rfl⟩ : syracuseStep 3245219 = 4867829) B4867829
theorem B2163479 : Blo 2163435 2163479 := bstep (se 1 (by rfl) ⟨1622609, by rfl⟩ : syracuseStep 2163479 = 3245219) B3245219
theorem B15594677 : Blo 2163435 15594677 := bbase (se 5 (by rfl) ⟨731000, by rfl⟩ : syracuseStep 15594677 = 1462001) (by norm_num)
theorem B10396451 : Blo 2163435 10396451 := bstep (se 1 (by rfl) ⟨7797338, by rfl⟩ : syracuseStep 10396451 = 15594677) B15594677
theorem B27723869 : Blo 2163435 27723869 := bstep (se 3 (by rfl) ⟨5198225, by rfl⟩ : syracuseStep 27723869 = 10396451) B10396451
theorem B18482579 : Blo 2163435 18482579 := bstep (se 1 (by rfl) ⟨13861934, by rfl⟩ : syracuseStep 18482579 = 27723869) B27723869
theorem B12321719 : Blo 2163435 12321719 := bstep (se 1 (by rfl) ⟨9241289, by rfl⟩ : syracuseStep 12321719 = 18482579) B18482579
theorem B8214479 : Blo 2163435 8214479 := bstep (se 1 (by rfl) ⟨6160859, by rfl⟩ : syracuseStep 8214479 = 12321719) B12321719
theorem B5476319 : Blo 2163435 5476319 := bstep (se 1 (by rfl) ⟨4107239, by rfl⟩ : syracuseStep 5476319 = 8214479) B8214479
theorem B3650879 : Blo 2163435 3650879 := bstep (se 1 (by rfl) ⟨2738159, by rfl⟩ : syracuseStep 3650879 = 5476319) B5476319
theorem B2433919 : Blo 2163435 2433919 := bstep (se 1 (by rfl) ⟨1825439, by rfl⟩ : syracuseStep 2433919 = 3650879) B3650879
theorem B3245225 : Blo 2163435 3245225 := bstep (se 2 (by rfl) ⟨1216959, by rfl⟩ : syracuseStep 3245225 = 2433919) B2433919
theorem B2163483 : Blo 2163435 2163483 := bstep (se 1 (by rfl) ⟨1622612, by rfl⟩ : syracuseStep 2163483 = 3245225) B3245225
theorem B4620653 : Blo 2163435 4620653 := bbase (se 3 (by rfl) ⟨866372, by rfl⟩ : syracuseStep 4620653 = 1732745) (by norm_num)
theorem B3080435 : Blo 2163435 3080435 := bstep (se 1 (by rfl) ⟨2310326, by rfl⟩ : syracuseStep 3080435 = 4620653) B4620653
theorem B8214493 : Blo 2163435 8214493 := bstep (se 3 (by rfl) ⟨1540217, by rfl⟩ : syracuseStep 8214493 = 3080435) B3080435
theorem B10952657 : Blo 2163435 10952657 := bstep (se 2 (by rfl) ⟨4107246, by rfl⟩ : syracuseStep 10952657 = 8214493) B8214493
theorem B7301771 : Blo 2163435 7301771 := bstep (se 1 (by rfl) ⟨5476328, by rfl⟩ : syracuseStep 7301771 = 10952657) B10952657
theorem B4867847 : Blo 2163435 4867847 := bstep (se 1 (by rfl) ⟨3650885, by rfl⟩ : syracuseStep 4867847 = 7301771) B7301771
theorem B3245231 : Blo 2163435 3245231 := bstep (se 1 (by rfl) ⟨2433923, by rfl⟩ : syracuseStep 3245231 = 4867847) B4867847
theorem B2163487 : Blo 2163435 2163487 := bstep (se 1 (by rfl) ⟨1622615, by rfl⟩ : syracuseStep 2163487 = 3245231) B3245231
theorem B3245237 : Blo 2163435 3245237 := bbase (se 5 (by rfl) ⟨152120, by rfl⟩ : syracuseStep 3245237 = 304241) (by norm_num)
theorem B2163491 : Blo 2163435 2163491 := bstep (se 1 (by rfl) ⟨1622618, by rfl⟩ : syracuseStep 2163491 = 3245237) B3245237
theorem B5476349 : Blo 2163435 5476349 := bbase (se 3 (by rfl) ⟨1026815, by rfl⟩ : syracuseStep 5476349 = 2053631) (by norm_num)
theorem B3650899 : Blo 2163435 3650899 := bstep (se 1 (by rfl) ⟨2738174, by rfl⟩ : syracuseStep 3650899 = 5476349) B5476349
theorem B4867865 : Blo 2163435 4867865 := bstep (se 2 (by rfl) ⟨1825449, by rfl⟩ : syracuseStep 4867865 = 3650899) B3650899
theorem B3245243 : Blo 2163435 3245243 := bstep (se 1 (by rfl) ⟨2433932, by rfl⟩ : syracuseStep 3245243 = 4867865) B4867865
theorem B2163495 : Blo 2163435 2163495 := bstep (se 1 (by rfl) ⟨1622621, by rfl⟩ : syracuseStep 2163495 = 3245243) B3245243
theorem B2433937 : Blo 2163435 2433937 := bbase (se 2 (by rfl) ⟨912726, by rfl⟩ : syracuseStep 2433937 = 1825453) (by norm_num)
theorem B3245249 : Blo 2163435 3245249 := bstep (se 2 (by rfl) ⟨1216968, by rfl⟩ : syracuseStep 3245249 = 2433937) B2433937
theorem B2163499 : Blo 2163435 2163499 := bstep (se 1 (by rfl) ⟨1622624, by rfl⟩ : syracuseStep 2163499 = 3245249) B3245249
theorem B4107277 : Blo 2163435 4107277 := bbase (se 3 (by rfl) ⟨770114, by rfl⟩ : syracuseStep 4107277 = 1540229) (by norm_num)
theorem B5476369 : Blo 2163435 5476369 := bstep (se 2 (by rfl) ⟨2053638, by rfl⟩ : syracuseStep 5476369 = 4107277) B4107277
theorem B7301825 : Blo 2163435 7301825 := bstep (se 2 (by rfl) ⟨2738184, by rfl⟩ : syracuseStep 7301825 = 5476369) B5476369
theorem B4867883 : Blo 2163435 4867883 := bstep (se 1 (by rfl) ⟨3650912, by rfl⟩ : syracuseStep 4867883 = 7301825) B7301825
theorem B3245255 : Blo 2163435 3245255 := bstep (se 1 (by rfl) ⟨2433941, by rfl⟩ : syracuseStep 3245255 = 4867883) B4867883
theorem B2163503 : Blo 2163435 2163503 := bstep (se 1 (by rfl) ⟨1622627, by rfl⟩ : syracuseStep 2163503 = 3245255) B3245255
theorem B3245261 : Blo 2163435 3245261 := bbase (se 3 (by rfl) ⟨608486, by rfl⟩ : syracuseStep 3245261 = 1216973) (by norm_num)
theorem B2163507 : Blo 2163435 2163507 := bstep (se 1 (by rfl) ⟨1622630, by rfl⟩ : syracuseStep 2163507 = 3245261) B3245261
theorem B4867901 : Blo 2163435 4867901 := bbase (se 3 (by rfl) ⟨912731, by rfl⟩ : syracuseStep 4867901 = 1825463) (by norm_num)
theorem B3245267 : Blo 2163435 3245267 := bstep (se 1 (by rfl) ⟨2433950, by rfl⟩ : syracuseStep 3245267 = 4867901) B4867901
theorem B2163511 : Blo 2163435 2163511 := bstep (se 1 (by rfl) ⟨1622633, by rfl⟩ : syracuseStep 2163511 = 3245267) B3245267
theorem B3650933 : Blo 2163435 3650933 := bbase (se 5 (by rfl) ⟨171137, by rfl⟩ : syracuseStep 3650933 = 342275) (by norm_num)
theorem B2433955 : Blo 2163435 2433955 := bstep (se 1 (by rfl) ⟨1825466, by rfl⟩ : syracuseStep 2433955 = 3650933) B3650933
theorem B3245273 : Blo 2163435 3245273 := bstep (se 2 (by rfl) ⟨1216977, by rfl⟩ : syracuseStep 3245273 = 2433955) B2433955
theorem B2163515 : Blo 2163435 2163515 := bstep (se 1 (by rfl) ⟨1622636, by rfl⟩ : syracuseStep 2163515 = 3245273) B3245273
theorem B3465541 : Blo 2163435 3465541 := bbase (se 4 (by rfl) ⟨324894, by rfl⟩ : syracuseStep 3465541 = 649789) (by norm_num)
theorem B4620721 : Blo 2163435 4620721 := bstep (se 2 (by rfl) ⟨1732770, by rfl⟩ : syracuseStep 4620721 = 3465541) B3465541
theorem B6160961 : Blo 2163435 6160961 := bstep (se 2 (by rfl) ⟨2310360, by rfl⟩ : syracuseStep 6160961 = 4620721) B4620721
theorem B16429229 : Blo 2163435 16429229 := bstep (se 3 (by rfl) ⟨3080480, by rfl⟩ : syracuseStep 16429229 = 6160961) B6160961
theorem B10952819 : Blo 2163435 10952819 := bstep (se 1 (by rfl) ⟨8214614, by rfl⟩ : syracuseStep 10952819 = 16429229) B16429229
theorem B7301879 : Blo 2163435 7301879 := bstep (se 1 (by rfl) ⟨5476409, by rfl⟩ : syracuseStep 7301879 = 10952819) B10952819
theorem B4867919 : Blo 2163435 4867919 := bstep (se 1 (by rfl) ⟨3650939, by rfl⟩ : syracuseStep 4867919 = 7301879) B7301879
theorem B3245279 : Blo 2163435 3245279 := bstep (se 1 (by rfl) ⟨2433959, by rfl⟩ : syracuseStep 3245279 = 4867919) B4867919
theorem B2163519 : Blo 2163435 2163519 := bstep (se 1 (by rfl) ⟨1622639, by rfl⟩ : syracuseStep 2163519 = 3245279) B3245279
theorem B3245285 : Blo 2163435 3245285 := bbase (se 4 (by rfl) ⟨304245, by rfl⟩ : syracuseStep 3245285 = 608491) (by norm_num)
theorem B2163523 : Blo 2163435 2163523 := bstep (se 1 (by rfl) ⟨1622642, by rfl⟩ : syracuseStep 2163523 = 3245285) B3245285
theorem B6931109 : Blo 2163435 6931109 := bbase (se 4 (by rfl) ⟨649791, by rfl⟩ : syracuseStep 6931109 = 1299583) (by norm_num)
theorem B4620739 : Blo 2163435 4620739 := bstep (se 1 (by rfl) ⟨3465554, by rfl⟩ : syracuseStep 4620739 = 6931109) B6931109
theorem B6160985 : Blo 2163435 6160985 := bstep (se 2 (by rfl) ⟨2310369, by rfl⟩ : syracuseStep 6160985 = 4620739) B4620739
theorem B4107323 : Blo 2163435 4107323 := bstep (se 1 (by rfl) ⟨3080492, by rfl⟩ : syracuseStep 4107323 = 6160985) B6160985
theorem B2738215 : Blo 2163435 2738215 := bstep (se 1 (by rfl) ⟨2053661, by rfl⟩ : syracuseStep 2738215 = 4107323) B4107323
theorem B3650953 : Blo 2163435 3650953 := bstep (se 2 (by rfl) ⟨1369107, by rfl⟩ : syracuseStep 3650953 = 2738215) B2738215
theorem B4867937 : Blo 2163435 4867937 := bstep (se 2 (by rfl) ⟨1825476, by rfl⟩ : syracuseStep 4867937 = 3650953) B3650953
theorem B3245291 : Blo 2163435 3245291 := bstep (se 1 (by rfl) ⟨2433968, by rfl⟩ : syracuseStep 3245291 = 4867937) B4867937
theorem B2163527 : Blo 2163435 2163527 := bstep (se 1 (by rfl) ⟨1622645, by rfl⟩ : syracuseStep 2163527 = 3245291) B3245291
theorem B2433973 : Blo 2163435 2433973 := bbase (se 5 (by rfl) ⟨114092, by rfl⟩ : syracuseStep 2433973 = 228185) (by norm_num)
theorem B3245297 : Blo 2163435 3245297 := bstep (se 2 (by rfl) ⟨1216986, by rfl⟩ : syracuseStep 3245297 = 2433973) B2433973
theorem B2163531 : Blo 2163435 2163531 := bstep (se 1 (by rfl) ⟨1622648, by rfl⟩ : syracuseStep 2163531 = 3245297) B3245297
theorem B2738225 : Blo 2163435 2738225 := bbase (se 2 (by rfl) ⟨1026834, by rfl⟩ : syracuseStep 2738225 = 2053669) (by norm_num)
theorem B7301933 : Blo 2163435 7301933 := bstep (se 3 (by rfl) ⟨1369112, by rfl⟩ : syracuseStep 7301933 = 2738225) B2738225
theorem B4867955 : Blo 2163435 4867955 := bstep (se 1 (by rfl) ⟨3650966, by rfl⟩ : syracuseStep 4867955 = 7301933) B7301933
theorem B3245303 : Blo 2163435 3245303 := bstep (se 1 (by rfl) ⟨2433977, by rfl⟩ : syracuseStep 3245303 = 4867955) B4867955
theorem B2163535 : Blo 2163435 2163535 := bstep (se 1 (by rfl) ⟨1622651, by rfl⟩ : syracuseStep 2163535 = 3245303) B3245303
theorem B3245309 : Blo 2163435 3245309 := bbase (se 3 (by rfl) ⟨608495, by rfl⟩ : syracuseStep 3245309 = 1216991) (by norm_num)
theorem B2163539 : Blo 2163435 2163539 := bstep (se 1 (by rfl) ⟨1622654, by rfl⟩ : syracuseStep 2163539 = 3245309) B3245309
theorem B4867973 : Blo 2163435 4867973 := bbase (se 4 (by rfl) ⟨456372, by rfl⟩ : syracuseStep 4867973 = 912745) (by norm_num)
theorem B3245315 : Blo 2163435 3245315 := bstep (se 1 (by rfl) ⟨2433986, by rfl⟩ : syracuseStep 3245315 = 4867973) B4867973
theorem B2163543 : Blo 2163435 2163543 := bstep (se 1 (by rfl) ⟨1622657, by rfl⟩ : syracuseStep 2163543 = 3245315) B3245315
theorem B5198381 : Blo 2163435 5198381 := bbase (se 3 (by rfl) ⟨974696, by rfl⟩ : syracuseStep 5198381 = 1949393) (by norm_num)
theorem B3465587 : Blo 2163435 3465587 := bstep (se 1 (by rfl) ⟨2599190, by rfl⟩ : syracuseStep 3465587 = 5198381) B5198381
theorem B2310391 : Blo 2163435 2310391 := bstep (se 1 (by rfl) ⟨1732793, by rfl⟩ : syracuseStep 2310391 = 3465587) B3465587
theorem B3080521 : Blo 2163435 3080521 := bstep (se 2 (by rfl) ⟨1155195, by rfl⟩ : syracuseStep 3080521 = 2310391) B2310391
theorem B4107361 : Blo 2163435 4107361 := bstep (se 2 (by rfl) ⟨1540260, by rfl⟩ : syracuseStep 4107361 = 3080521) B3080521
theorem B5476481 : Blo 2163435 5476481 := bstep (se 2 (by rfl) ⟨2053680, by rfl⟩ : syracuseStep 5476481 = 4107361) B4107361
theorem B3650987 : Blo 2163435 3650987 := bstep (se 1 (by rfl) ⟨2738240, by rfl⟩ : syracuseStep 3650987 = 5476481) B5476481
theorem B2433991 : Blo 2163435 2433991 := bstep (se 1 (by rfl) ⟨1825493, by rfl⟩ : syracuseStep 2433991 = 3650987) B3650987
theorem B3245321 : Blo 2163435 3245321 := bstep (se 2 (by rfl) ⟨1216995, by rfl⟩ : syracuseStep 3245321 = 2433991) B2433991
theorem B2163547 : Blo 2163435 2163547 := bstep (se 1 (by rfl) ⟨1622660, by rfl⟩ : syracuseStep 2163547 = 3245321) B3245321
theorem B10952981 : Blo 2163435 10952981 := bbase (se 6 (by rfl) ⟨256710, by rfl⟩ : syracuseStep 10952981 = 513421) (by norm_num)
theorem B7301987 : Blo 2163435 7301987 := bstep (se 1 (by rfl) ⟨5476490, by rfl⟩ : syracuseStep 7301987 = 10952981) B10952981
theorem B4867991 : Blo 2163435 4867991 := bstep (se 1 (by rfl) ⟨3650993, by rfl⟩ : syracuseStep 4867991 = 7301987) B7301987
theorem B3245327 : Blo 2163435 3245327 := bstep (se 1 (by rfl) ⟨2433995, by rfl⟩ : syracuseStep 3245327 = 4867991) B4867991
theorem B2163551 : Blo 2163435 2163551 := bstep (se 1 (by rfl) ⟨1622663, by rfl⟩ : syracuseStep 2163551 = 3245327) B3245327
theorem B3245333 : Blo 2163435 3245333 := bbase (se 6 (by rfl) ⟨76062, by rfl⟩ : syracuseStep 3245333 = 152125) (by norm_num)
theorem B2163555 : Blo 2163435 2163555 := bstep (se 1 (by rfl) ⟨1622666, by rfl⟩ : syracuseStep 2163555 = 3245333) B3245333
theorem B3802493 : Blo 2163435 3802493 := bbase (se 3 (by rfl) ⟨712967, by rfl⟩ : syracuseStep 3802493 = 1425935) (by norm_num)
theorem B2534995 : Blo 2163435 2534995 := bstep (se 1 (by rfl) ⟨1901246, by rfl⟩ : syracuseStep 2534995 = 3802493) B3802493
theorem B13519973 : Blo 2163435 13519973 := bstep (se 4 (by rfl) ⟨1267497, by rfl⟩ : syracuseStep 13519973 = 2534995) B2534995
theorem B36053261 : Blo 2163435 36053261 := bstep (se 3 (by rfl) ⟨6759986, by rfl⟩ : syracuseStep 36053261 = 13519973) B13519973
theorem B24035507 : Blo 2163435 24035507 := bstep (se 1 (by rfl) ⟨18026630, by rfl⟩ : syracuseStep 24035507 = 36053261) B36053261
theorem B16023671 : Blo 2163435 16023671 := bstep (se 1 (by rfl) ⟨12017753, by rfl⟩ : syracuseStep 16023671 = 24035507) B24035507
theorem B10682447 : Blo 2163435 10682447 := bstep (se 1 (by rfl) ⟨8011835, by rfl⟩ : syracuseStep 10682447 = 16023671) B16023671
theorem B28486525 : Blo 2163435 28486525 := bstep (se 3 (by rfl) ⟨5341223, by rfl⟩ : syracuseStep 28486525 = 10682447) B10682447
theorem B37982033 : Blo 2163435 37982033 := bstep (se 2 (by rfl) ⟨14243262, by rfl⟩ : syracuseStep 37982033 = 28486525) B28486525
theorem B25321355 : Blo 2163435 25321355 := bstep (se 1 (by rfl) ⟨18991016, by rfl⟩ : syracuseStep 25321355 = 37982033) B37982033
theorem B16880903 : Blo 2163435 16880903 := bstep (se 1 (by rfl) ⟨12660677, by rfl⟩ : syracuseStep 16880903 = 25321355) B25321355
theorem B11253935 : Blo 2163435 11253935 := bstep (se 1 (by rfl) ⟨8440451, by rfl⟩ : syracuseStep 11253935 = 16880903) B16880903
theorem B30010493 : Blo 2163435 30010493 := bstep (se 3 (by rfl) ⟨5626967, by rfl⟩ : syracuseStep 30010493 = 11253935) B11253935
theorem B20006995 : Blo 2163435 20006995 := bstep (se 1 (by rfl) ⟨15005246, by rfl⟩ : syracuseStep 20006995 = 30010493) B30010493
theorem B26675993 : Blo 2163435 26675993 := bstep (se 2 (by rfl) ⟨10003497, by rfl⟩ : syracuseStep 26675993 = 20006995) B20006995
theorem B71135981 : Blo 2163435 71135981 := bstep (se 3 (by rfl) ⟨13337996, by rfl⟩ : syracuseStep 71135981 = 26675993) B26675993
theorem B47423987 : Blo 2163435 47423987 := bstep (se 1 (by rfl) ⟨35567990, by rfl⟩ : syracuseStep 47423987 = 71135981) B71135981
theorem B31615991 : Blo 2163435 31615991 := bstep (se 1 (by rfl) ⟨23711993, by rfl⟩ : syracuseStep 31615991 = 47423987) B47423987
theorem B21077327 : Blo 2163435 21077327 := bstep (se 1 (by rfl) ⟨15807995, by rfl⟩ : syracuseStep 21077327 = 31615991) B31615991
theorem B14051551 : Blo 2163435 14051551 := bstep (se 1 (by rfl) ⟨10538663, by rfl⟩ : syracuseStep 14051551 = 21077327) B21077327
theorem B18735401 : Blo 2163435 18735401 := bstep (se 2 (by rfl) ⟨7025775, by rfl⟩ : syracuseStep 18735401 = 14051551) B14051551
theorem B49961069 : Blo 2163435 49961069 := bstep (se 3 (by rfl) ⟨9367700, by rfl⟩ : syracuseStep 49961069 = 18735401) B18735401
theorem B33307379 : Blo 2163435 33307379 := bstep (se 1 (by rfl) ⟨24980534, by rfl⟩ : syracuseStep 33307379 = 49961069) B49961069
theorem B22204919 : Blo 2163435 22204919 := bstep (se 1 (by rfl) ⟨16653689, by rfl⟩ : syracuseStep 22204919 = 33307379) B33307379
theorem B14803279 : Blo 2163435 14803279 := bstep (se 1 (by rfl) ⟨11102459, by rfl⟩ : syracuseStep 14803279 = 22204919) B22204919
theorem B78950821 : Blo 2163435 78950821 := bstep (se 4 (by rfl) ⟨7401639, by rfl⟩ : syracuseStep 78950821 = 14803279) B14803279
theorem B105267761 : Blo 2163435 105267761 := bstep (se 2 (by rfl) ⟨39475410, by rfl⟩ : syracuseStep 105267761 = 78950821) B78950821
theorem B70178507 : Blo 2163435 70178507 := bstep (se 1 (by rfl) ⟨52633880, by rfl⟩ : syracuseStep 70178507 = 105267761) B105267761
theorem B46785671 : Blo 2163435 46785671 := bstep (se 1 (by rfl) ⟨35089253, by rfl⟩ : syracuseStep 46785671 = 70178507) B70178507
theorem B31190447 : Blo 2163435 31190447 := bstep (se 1 (by rfl) ⟨23392835, by rfl⟩ : syracuseStep 31190447 = 46785671) B46785671
theorem B20793631 : Blo 2163435 20793631 := bstep (se 1 (by rfl) ⟨15595223, by rfl⟩ : syracuseStep 20793631 = 31190447) B31190447
theorem B27724841 : Blo 2163435 27724841 := bstep (se 2 (by rfl) ⟨10396815, by rfl⟩ : syracuseStep 27724841 = 20793631) B20793631
theorem B18483227 : Blo 2163435 18483227 := bstep (se 1 (by rfl) ⟨13862420, by rfl⟩ : syracuseStep 18483227 = 27724841) B27724841
theorem B12322151 : Blo 2163435 12322151 := bstep (se 1 (by rfl) ⟨9241613, by rfl⟩ : syracuseStep 12322151 = 18483227) B18483227
theorem B8214767 : Blo 2163435 8214767 := bstep (se 1 (by rfl) ⟨6161075, by rfl⟩ : syracuseStep 8214767 = 12322151) B12322151
theorem B5476511 : Blo 2163435 5476511 := bstep (se 1 (by rfl) ⟨4107383, by rfl⟩ : syracuseStep 5476511 = 8214767) B8214767
theorem B3651007 : Blo 2163435 3651007 := bstep (se 1 (by rfl) ⟨2738255, by rfl⟩ : syracuseStep 3651007 = 5476511) B5476511
theorem B4868009 : Blo 2163435 4868009 := bstep (se 2 (by rfl) ⟨1825503, by rfl⟩ : syracuseStep 4868009 = 3651007) B3651007
theorem B3245339 : Blo 2163435 3245339 := bstep (se 1 (by rfl) ⟨2434004, by rfl⟩ : syracuseStep 3245339 = 4868009) B4868009
theorem B2163559 : Blo 2163435 2163559 := bstep (se 1 (by rfl) ⟨1622669, by rfl⟩ : syracuseStep 2163559 = 3245339) B3245339
theorem B2434009 : Blo 2163435 2434009 := bbase (se 2 (by rfl) ⟨912753, by rfl⟩ : syracuseStep 2434009 = 1825507) (by norm_num)
theorem B3245345 : Blo 2163435 3245345 := bstep (se 2 (by rfl) ⟨1217004, by rfl⟩ : syracuseStep 3245345 = 2434009) B2434009
theorem B2163563 : Blo 2163435 2163563 := bstep (se 1 (by rfl) ⟨1622672, by rfl⟩ : syracuseStep 2163563 = 3245345) B3245345
theorem B3080549 : Blo 2163435 3080549 := bbase (se 4 (by rfl) ⟨288801, by rfl⟩ : syracuseStep 3080549 = 577603) (by norm_num)
theorem B8214797 : Blo 2163435 8214797 := bstep (se 3 (by rfl) ⟨1540274, by rfl⟩ : syracuseStep 8214797 = 3080549) B3080549
theorem B5476531 : Blo 2163435 5476531 := bstep (se 1 (by rfl) ⟨4107398, by rfl⟩ : syracuseStep 5476531 = 8214797) B8214797
theorem B7302041 : Blo 2163435 7302041 := bstep (se 2 (by rfl) ⟨2738265, by rfl⟩ : syracuseStep 7302041 = 5476531) B5476531
theorem B4868027 : Blo 2163435 4868027 := bstep (se 1 (by rfl) ⟨3651020, by rfl⟩ : syracuseStep 4868027 = 7302041) B7302041
theorem B3245351 : Blo 2163435 3245351 := bstep (se 1 (by rfl) ⟨2434013, by rfl⟩ : syracuseStep 3245351 = 4868027) B4868027
theorem B2163567 : Blo 2163435 2163567 := bstep (se 1 (by rfl) ⟨1622675, by rfl⟩ : syracuseStep 2163567 = 3245351) B3245351
theorem B3245357 : Blo 2163435 3245357 := bbase (se 3 (by rfl) ⟨608504, by rfl⟩ : syracuseStep 3245357 = 1217009) (by norm_num)
theorem B2163571 : Blo 2163435 2163571 := bstep (se 1 (by rfl) ⟨1622678, by rfl⟩ : syracuseStep 2163571 = 3245357) B3245357
theorem B4868045 : Blo 2163435 4868045 := bbase (se 3 (by rfl) ⟨912758, by rfl⟩ : syracuseStep 4868045 = 1825517) (by norm_num)
theorem B3245363 : Blo 2163435 3245363 := bstep (se 1 (by rfl) ⟨2434022, by rfl⟩ : syracuseStep 3245363 = 4868045) B4868045
theorem B2163575 : Blo 2163435 2163575 := bstep (se 1 (by rfl) ⟨1622681, by rfl⟩ : syracuseStep 2163575 = 3245363) B3245363
theorem B2738281 : Blo 2163435 2738281 := bbase (se 2 (by rfl) ⟨1026855, by rfl⟩ : syracuseStep 2738281 = 2053711) (by norm_num)
theorem B3651041 : Blo 2163435 3651041 := bstep (se 2 (by rfl) ⟨1369140, by rfl⟩ : syracuseStep 3651041 = 2738281) B2738281
theorem B2434027 : Blo 2163435 2434027 := bstep (se 1 (by rfl) ⟨1825520, by rfl⟩ : syracuseStep 2434027 = 3651041) B3651041
theorem B3245369 : Blo 2163435 3245369 := bstep (se 2 (by rfl) ⟨1217013, by rfl⟩ : syracuseStep 3245369 = 2434027) B2434027
theorem B2163579 : Blo 2163435 2163579 := bstep (se 1 (by rfl) ⟨1622684, by rfl⟩ : syracuseStep 2163579 = 3245369) B3245369
theorem B2634697 : Blo 2163435 2634697 := bbase (se 2 (by rfl) ⟨988011, by rfl⟩ : syracuseStep 2634697 = 1976023) (by norm_num)
theorem B14051717 : Blo 2163435 14051717 := bstep (se 4 (by rfl) ⟨1317348, by rfl⟩ : syracuseStep 14051717 = 2634697) B2634697
theorem B9367811 : Blo 2163435 9367811 := bstep (se 1 (by rfl) ⟨7025858, by rfl⟩ : syracuseStep 9367811 = 14051717) B14051717
theorem B6245207 : Blo 2163435 6245207 := bstep (se 1 (by rfl) ⟨4683905, by rfl⟩ : syracuseStep 6245207 = 9367811) B9367811
theorem B4163471 : Blo 2163435 4163471 := bstep (se 1 (by rfl) ⟨3122603, by rfl⟩ : syracuseStep 4163471 = 6245207) B6245207
theorem B2775647 : Blo 2163435 2775647 := bstep (se 1 (by rfl) ⟨2081735, by rfl⟩ : syracuseStep 2775647 = 4163471) B4163471
theorem B7401725 : Blo 2163435 7401725 := bstep (se 3 (by rfl) ⟨1387823, by rfl⟩ : syracuseStep 7401725 = 2775647) B2775647
theorem B4934483 : Blo 2163435 4934483 := bstep (se 1 (by rfl) ⟨3700862, by rfl⟩ : syracuseStep 4934483 = 7401725) B7401725
theorem B3289655 : Blo 2163435 3289655 := bstep (se 1 (by rfl) ⟨2467241, by rfl⟩ : syracuseStep 3289655 = 4934483) B4934483
theorem B2193103 : Blo 2163435 2193103 := bstep (se 1 (by rfl) ⟨1644827, by rfl⟩ : syracuseStep 2193103 = 3289655) B3289655
theorem B2924137 : Blo 2163435 2924137 := bstep (se 2 (by rfl) ⟨1096551, by rfl⟩ : syracuseStep 2924137 = 2193103) B2193103
theorem B3898849 : Blo 2163435 3898849 := bstep (se 2 (by rfl) ⟨1462068, by rfl⟩ : syracuseStep 3898849 = 2924137) B2924137
theorem B5198465 : Blo 2163435 5198465 := bstep (se 2 (by rfl) ⟨1949424, by rfl⟩ : syracuseStep 5198465 = 3898849) B3898849
theorem B13862573 : Blo 2163435 13862573 := bstep (se 3 (by rfl) ⟨2599232, by rfl⟩ : syracuseStep 13862573 = 5198465) B5198465
theorem B9241715 : Blo 2163435 9241715 := bstep (se 1 (by rfl) ⟨6931286, by rfl⟩ : syracuseStep 9241715 = 13862573) B13862573
theorem B24644573 : Blo 2163435 24644573 := bstep (se 3 (by rfl) ⟨4620857, by rfl⟩ : syracuseStep 24644573 = 9241715) B9241715
theorem B16429715 : Blo 2163435 16429715 := bstep (se 1 (by rfl) ⟨12322286, by rfl⟩ : syracuseStep 16429715 = 24644573) B24644573
theorem B10953143 : Blo 2163435 10953143 := bstep (se 1 (by rfl) ⟨8214857, by rfl⟩ : syracuseStep 10953143 = 16429715) B16429715
theorem B7302095 : Blo 2163435 7302095 := bstep (se 1 (by rfl) ⟨5476571, by rfl⟩ : syracuseStep 7302095 = 10953143) B10953143
theorem B4868063 : Blo 2163435 4868063 := bstep (se 1 (by rfl) ⟨3651047, by rfl⟩ : syracuseStep 4868063 = 7302095) B7302095
theorem B3245375 : Blo 2163435 3245375 := bstep (se 1 (by rfl) ⟨2434031, by rfl⟩ : syracuseStep 3245375 = 4868063) B4868063
theorem B2163583 : Blo 2163435 2163583 := bstep (se 1 (by rfl) ⟨1622687, by rfl⟩ : syracuseStep 2163583 = 3245375) B3245375
theorem B3245381 : Blo 2163435 3245381 := bbase (se 4 (by rfl) ⟨304254, by rfl⟩ : syracuseStep 3245381 = 608509) (by norm_num)
theorem B2163587 : Blo 2163435 2163587 := bstep (se 1 (by rfl) ⟨1622690, by rfl⟩ : syracuseStep 2163587 = 3245381) B3245381
theorem B3651061 : Blo 2163435 3651061 := bbase (se 5 (by rfl) ⟨171143, by rfl⟩ : syracuseStep 3651061 = 342287) (by norm_num)
theorem B4868081 : Blo 2163435 4868081 := bstep (se 2 (by rfl) ⟨1825530, by rfl⟩ : syracuseStep 4868081 = 3651061) B3651061
theorem B3245387 : Blo 2163435 3245387 := bstep (se 1 (by rfl) ⟨2434040, by rfl⟩ : syracuseStep 3245387 = 4868081) B4868081
theorem B2163591 : Blo 2163435 2163591 := bstep (se 1 (by rfl) ⟨1622693, by rfl⟩ : syracuseStep 2163591 = 3245387) B3245387
theorem B2434045 : Blo 2163435 2434045 := bbase (se 3 (by rfl) ⟨456383, by rfl⟩ : syracuseStep 2434045 = 912767) (by norm_num)
theorem B3245393 : Blo 2163435 3245393 := bstep (se 2 (by rfl) ⟨1217022, by rfl⟩ : syracuseStep 3245393 = 2434045) B2434045
theorem B2163595 : Blo 2163435 2163595 := bstep (se 1 (by rfl) ⟨1622696, by rfl⟩ : syracuseStep 2163595 = 3245393) B3245393
theorem B7302149 : Blo 2163435 7302149 := bbase (se 4 (by rfl) ⟨684576, by rfl⟩ : syracuseStep 7302149 = 1369153) (by norm_num)
theorem B4868099 : Blo 2163435 4868099 := bstep (se 1 (by rfl) ⟨3651074, by rfl⟩ : syracuseStep 4868099 = 7302149) B7302149
theorem B3245399 : Blo 2163435 3245399 := bstep (se 1 (by rfl) ⟨2434049, by rfl⟩ : syracuseStep 3245399 = 4868099) B4868099
theorem B2163599 : Blo 2163435 2163599 := bstep (se 1 (by rfl) ⟨1622699, by rfl⟩ : syracuseStep 2163599 = 3245399) B3245399
theorem B3245405 : Blo 2163435 3245405 := bbase (se 3 (by rfl) ⟨608513, by rfl⟩ : syracuseStep 3245405 = 1217027) (by norm_num)
theorem B2163603 : Blo 2163435 2163603 := bstep (se 1 (by rfl) ⟨1622702, by rfl⟩ : syracuseStep 2163603 = 3245405) B3245405
theorem B4868117 : Blo 2163435 4868117 := bbase (se 6 (by rfl) ⟨114096, by rfl⟩ : syracuseStep 4868117 = 228193) (by norm_num)
theorem B3245411 : Blo 2163435 3245411 := bstep (se 1 (by rfl) ⟨2434058, by rfl⟩ : syracuseStep 3245411 = 4868117) B4868117
theorem B2163607 : Blo 2163435 2163607 := bstep (se 1 (by rfl) ⟨1622705, by rfl⟩ : syracuseStep 2163607 = 3245411) B3245411
theorem B8214965 : Blo 2163435 8214965 := bbase (se 5 (by rfl) ⟨385076, by rfl⟩ : syracuseStep 8214965 = 770153) (by norm_num)
theorem B5476643 : Blo 2163435 5476643 := bstep (se 1 (by rfl) ⟨4107482, by rfl⟩ : syracuseStep 5476643 = 8214965) B8214965
theorem B3651095 : Blo 2163435 3651095 := bstep (se 1 (by rfl) ⟨2738321, by rfl⟩ : syracuseStep 3651095 = 5476643) B5476643
theorem B2434063 : Blo 2163435 2434063 := bstep (se 1 (by rfl) ⟨1825547, by rfl⟩ : syracuseStep 2434063 = 3651095) B3651095
theorem B3245417 : Blo 2163435 3245417 := bstep (se 2 (by rfl) ⟨1217031, by rfl⟩ : syracuseStep 3245417 = 2434063) B2434063
theorem B2163611 : Blo 2163435 2163611 := bstep (se 1 (by rfl) ⟨1622708, by rfl⟩ : syracuseStep 2163611 = 3245417) B3245417
theorem B18735893 : Blo 2163435 18735893 := bbase (se 6 (by rfl) ⟨439122, by rfl⟩ : syracuseStep 18735893 = 878245) (by norm_num)
theorem B12490595 : Blo 2163435 12490595 := bstep (se 1 (by rfl) ⟨9367946, by rfl⟩ : syracuseStep 12490595 = 18735893) B18735893
theorem B8327063 : Blo 2163435 8327063 := bstep (se 1 (by rfl) ⟨6245297, by rfl⟩ : syracuseStep 8327063 = 12490595) B12490595
theorem B22205501 : Blo 2163435 22205501 := bstep (se 3 (by rfl) ⟨4163531, by rfl⟩ : syracuseStep 22205501 = 8327063) B8327063
theorem B14803667 : Blo 2163435 14803667 := bstep (se 1 (by rfl) ⟨11102750, by rfl⟩ : syracuseStep 14803667 = 22205501) B22205501
theorem B9869111 : Blo 2163435 9869111 := bstep (se 1 (by rfl) ⟨7401833, by rfl⟩ : syracuseStep 9869111 = 14803667) B14803667
theorem B6579407 : Blo 2163435 6579407 := bstep (se 1 (by rfl) ⟨4934555, by rfl⟩ : syracuseStep 6579407 = 9869111) B9869111
theorem B17545085 : Blo 2163435 17545085 := bstep (se 3 (by rfl) ⟨3289703, by rfl⟩ : syracuseStep 17545085 = 6579407) B6579407
theorem B11696723 : Blo 2163435 11696723 := bstep (se 1 (by rfl) ⟨8772542, by rfl⟩ : syracuseStep 11696723 = 17545085) B17545085
theorem B7797815 : Blo 2163435 7797815 := bstep (se 1 (by rfl) ⟨5848361, by rfl⟩ : syracuseStep 7797815 = 11696723) B11696723
theorem B5198543 : Blo 2163435 5198543 := bstep (se 1 (by rfl) ⟨3898907, by rfl⟩ : syracuseStep 5198543 = 7797815) B7797815
theorem B3465695 : Blo 2163435 3465695 := bstep (se 1 (by rfl) ⟨2599271, by rfl⟩ : syracuseStep 3465695 = 5198543) B5198543
theorem B2310463 : Blo 2163435 2310463 := bstep (se 1 (by rfl) ⟨1732847, by rfl⟩ : syracuseStep 2310463 = 3465695) B3465695
theorem B12322469 : Blo 2163435 12322469 := bstep (se 4 (by rfl) ⟨1155231, by rfl⟩ : syracuseStep 12322469 = 2310463) B2310463
theorem B8214979 : Blo 2163435 8214979 := bstep (se 1 (by rfl) ⟨6161234, by rfl⟩ : syracuseStep 8214979 = 12322469) B12322469
theorem B10953305 : Blo 2163435 10953305 := bstep (se 2 (by rfl) ⟨4107489, by rfl⟩ : syracuseStep 10953305 = 8214979) B8214979
theorem B7302203 : Blo 2163435 7302203 := bstep (se 1 (by rfl) ⟨5476652, by rfl⟩ : syracuseStep 7302203 = 10953305) B10953305
theorem B4868135 : Blo 2163435 4868135 := bstep (se 1 (by rfl) ⟨3651101, by rfl⟩ : syracuseStep 4868135 = 7302203) B7302203
theorem B3245423 : Blo 2163435 3245423 := bstep (se 1 (by rfl) ⟨2434067, by rfl⟩ : syracuseStep 3245423 = 4868135) B4868135
theorem B2163615 : Blo 2163435 2163615 := bstep (se 1 (by rfl) ⟨1622711, by rfl⟩ : syracuseStep 2163615 = 3245423) B3245423
theorem B3245429 : Blo 2163435 3245429 := bbase (se 5 (by rfl) ⟨152129, by rfl⟩ : syracuseStep 3245429 = 304259) (by norm_num)
theorem B2163619 : Blo 2163435 2163619 := bstep (se 1 (by rfl) ⟨1622714, by rfl⟩ : syracuseStep 2163619 = 3245429) B3245429
theorem B3080629 : Blo 2163435 3080629 := bbase (se 5 (by rfl) ⟨144404, by rfl⟩ : syracuseStep 3080629 = 288809) (by norm_num)
theorem B4107505 : Blo 2163435 4107505 := bstep (se 2 (by rfl) ⟨1540314, by rfl⟩ : syracuseStep 4107505 = 3080629) B3080629
theorem B5476673 : Blo 2163435 5476673 := bstep (se 2 (by rfl) ⟨2053752, by rfl⟩ : syracuseStep 5476673 = 4107505) B4107505
theorem B3651115 : Blo 2163435 3651115 := bstep (se 1 (by rfl) ⟨2738336, by rfl⟩ : syracuseStep 3651115 = 5476673) B5476673
theorem B4868153 : Blo 2163435 4868153 := bstep (se 2 (by rfl) ⟨1825557, by rfl⟩ : syracuseStep 4868153 = 3651115) B3651115
theorem B3245435 : Blo 2163435 3245435 := bstep (se 1 (by rfl) ⟨2434076, by rfl⟩ : syracuseStep 3245435 = 4868153) B4868153
theorem B2163623 : Blo 2163435 2163623 := bstep (se 1 (by rfl) ⟨1622717, by rfl⟩ : syracuseStep 2163623 = 3245435) B3245435
theorem B2434081 : Blo 2163435 2434081 := bbase (se 2 (by rfl) ⟨912780, by rfl⟩ : syracuseStep 2434081 = 1825561) (by norm_num)
theorem B3245441 : Blo 2163435 3245441 := bstep (se 2 (by rfl) ⟨1217040, by rfl⟩ : syracuseStep 3245441 = 2434081) B2434081
theorem B2163627 : Blo 2163435 2163627 := bstep (se 1 (by rfl) ⟨1622720, by rfl⟩ : syracuseStep 2163627 = 3245441) B3245441
theorem B5476693 : Blo 2163435 5476693 := bbase (se 10 (by rfl) ⟨8022, by rfl⟩ : syracuseStep 5476693 = 16045) (by norm_num)
theorem B7302257 : Blo 2163435 7302257 := bstep (se 2 (by rfl) ⟨2738346, by rfl⟩ : syracuseStep 7302257 = 5476693) B5476693
theorem B4868171 : Blo 2163435 4868171 := bstep (se 1 (by rfl) ⟨3651128, by rfl⟩ : syracuseStep 4868171 = 7302257) B7302257
theorem B3245447 : Blo 2163435 3245447 := bstep (se 1 (by rfl) ⟨2434085, by rfl⟩ : syracuseStep 3245447 = 4868171) B4868171
theorem B2163631 : Blo 2163435 2163631 := bstep (se 1 (by rfl) ⟨1622723, by rfl⟩ : syracuseStep 2163631 = 3245447) B3245447
theorem B3245453 : Blo 2163435 3245453 := bbase (se 3 (by rfl) ⟨608522, by rfl⟩ : syracuseStep 3245453 = 1217045) (by norm_num)
theorem B2163635 : Blo 2163435 2163635 := bstep (se 1 (by rfl) ⟨1622726, by rfl⟩ : syracuseStep 2163635 = 3245453) B3245453
theorem B4868189 : Blo 2163435 4868189 := bbase (se 3 (by rfl) ⟨912785, by rfl⟩ : syracuseStep 4868189 = 1825571) (by norm_num)
theorem B3245459 : Blo 2163435 3245459 := bstep (se 1 (by rfl) ⟨2434094, by rfl⟩ : syracuseStep 3245459 = 4868189) B4868189
theorem B2163639 : Blo 2163435 2163639 := bstep (se 1 (by rfl) ⟨1622729, by rfl⟩ : syracuseStep 2163639 = 3245459) B3245459
theorem B3651149 : Blo 2163435 3651149 := bbase (se 3 (by rfl) ⟨684590, by rfl⟩ : syracuseStep 3651149 = 1369181) (by norm_num)
theorem B2434099 : Blo 2163435 2434099 := bstep (se 1 (by rfl) ⟨1825574, by rfl⟩ : syracuseStep 2434099 = 3651149) B3651149
theorem B3245465 : Blo 2163435 3245465 := bstep (se 2 (by rfl) ⟨1217049, by rfl⟩ : syracuseStep 3245465 = 2434099) B2434099
theorem B2163643 : Blo 2163435 2163643 := bstep (se 1 (by rfl) ⟨1622732, by rfl⟩ : syracuseStep 2163643 = 3245465) B3245465
theorem B2634773 : Blo 2163435 2634773 := bbase (se 6 (by rfl) ⟨61752, by rfl⟩ : syracuseStep 2634773 = 123505) (by norm_num)
theorem B28104245 : Blo 2163435 28104245 := bstep (se 5 (by rfl) ⟨1317386, by rfl⟩ : syracuseStep 28104245 = 2634773) B2634773
theorem B18736163 : Blo 2163435 18736163 := bstep (se 1 (by rfl) ⟨14052122, by rfl⟩ : syracuseStep 18736163 = 28104245) B28104245
theorem B12490775 : Blo 2163435 12490775 := bstep (se 1 (by rfl) ⟨9368081, by rfl⟩ : syracuseStep 12490775 = 18736163) B18736163
theorem B8327183 : Blo 2163435 8327183 := bstep (se 1 (by rfl) ⟨6245387, by rfl⟩ : syracuseStep 8327183 = 12490775) B12490775
theorem B22205821 : Blo 2163435 22205821 := bstep (se 3 (by rfl) ⟨4163591, by rfl⟩ : syracuseStep 22205821 = 8327183) B8327183
theorem B29607761 : Blo 2163435 29607761 := bstep (se 2 (by rfl) ⟨11102910, by rfl⟩ : syracuseStep 29607761 = 22205821) B22205821
theorem B19738507 : Blo 2163435 19738507 := bstep (se 1 (by rfl) ⟨14803880, by rfl⟩ : syracuseStep 19738507 = 29607761) B29607761
theorem B26318009 : Blo 2163435 26318009 := bstep (se 2 (by rfl) ⟨9869253, by rfl⟩ : syracuseStep 26318009 = 19738507) B19738507
theorem B17545339 : Blo 2163435 17545339 := bstep (se 1 (by rfl) ⟨13159004, by rfl⟩ : syracuseStep 17545339 = 26318009) B26318009
theorem B23393785 : Blo 2163435 23393785 := bstep (se 2 (by rfl) ⟨8772669, by rfl⟩ : syracuseStep 23393785 = 17545339) B17545339
theorem B31191713 : Blo 2163435 31191713 := bstep (se 2 (by rfl) ⟨11696892, by rfl⟩ : syracuseStep 31191713 = 23393785) B23393785
theorem B20794475 : Blo 2163435 20794475 := bstep (se 1 (by rfl) ⟨15595856, by rfl⟩ : syracuseStep 20794475 = 31191713) B31191713
theorem B13862983 : Blo 2163435 13862983 := bstep (se 1 (by rfl) ⟨10397237, by rfl⟩ : syracuseStep 13862983 = 20794475) B20794475
theorem B18483977 : Blo 2163435 18483977 := bstep (se 2 (by rfl) ⟨6931491, by rfl⟩ : syracuseStep 18483977 = 13862983) B13862983
theorem B12322651 : Blo 2163435 12322651 := bstep (se 1 (by rfl) ⟨9241988, by rfl⟩ : syracuseStep 12322651 = 18483977) B18483977
theorem B16430201 : Blo 2163435 16430201 := bstep (se 2 (by rfl) ⟨6161325, by rfl⟩ : syracuseStep 16430201 = 12322651) B12322651
theorem B10953467 : Blo 2163435 10953467 := bstep (se 1 (by rfl) ⟨8215100, by rfl⟩ : syracuseStep 10953467 = 16430201) B16430201
theorem B7302311 : Blo 2163435 7302311 := bstep (se 1 (by rfl) ⟨5476733, by rfl⟩ : syracuseStep 7302311 = 10953467) B10953467
theorem B4868207 : Blo 2163435 4868207 := bstep (se 1 (by rfl) ⟨3651155, by rfl⟩ : syracuseStep 4868207 = 7302311) B7302311
theorem B3245471 : Blo 2163435 3245471 := bstep (se 1 (by rfl) ⟨2434103, by rfl⟩ : syracuseStep 3245471 = 4868207) B4868207
theorem B2163647 : Blo 2163435 2163647 := bstep (se 1 (by rfl) ⟨1622735, by rfl⟩ : syracuseStep 2163647 = 3245471) B3245471
theorem B3245477 : Blo 2163435 3245477 := bbase (se 4 (by rfl) ⟨304263, by rfl⟩ : syracuseStep 3245477 = 608527) (by norm_num)
theorem B2163651 : Blo 2163435 2163651 := bstep (se 1 (by rfl) ⟨1622738, by rfl⟩ : syracuseStep 2163651 = 3245477) B3245477
theorem B2738377 : Blo 2163435 2738377 := bbase (se 2 (by rfl) ⟨1026891, by rfl⟩ : syracuseStep 2738377 = 2053783) (by norm_num)
theorem B3651169 : Blo 2163435 3651169 := bstep (se 2 (by rfl) ⟨1369188, by rfl⟩ : syracuseStep 3651169 = 2738377) B2738377
theorem B4868225 : Blo 2163435 4868225 := bstep (se 2 (by rfl) ⟨1825584, by rfl⟩ : syracuseStep 4868225 = 3651169) B3651169
theorem B3245483 : Blo 2163435 3245483 := bstep (se 1 (by rfl) ⟨2434112, by rfl⟩ : syracuseStep 3245483 = 4868225) B4868225
theorem B2163655 : Blo 2163435 2163655 := bstep (se 1 (by rfl) ⟨1622741, by rfl⟩ : syracuseStep 2163655 = 3245483) B3245483
theorem B2434117 : Blo 2163435 2434117 := bbase (se 4 (by rfl) ⟨228198, by rfl⟩ : syracuseStep 2434117 = 456397) (by norm_num)
theorem B3245489 : Blo 2163435 3245489 := bstep (se 2 (by rfl) ⟨1217058, by rfl⟩ : syracuseStep 3245489 = 2434117) B2434117
theorem B2163659 : Blo 2163435 2163659 := bstep (se 1 (by rfl) ⟨1622744, by rfl⟩ : syracuseStep 2163659 = 3245489) B3245489
theorem B4107581 : Blo 2163435 4107581 := bbase (se 3 (by rfl) ⟨770171, by rfl⟩ : syracuseStep 4107581 = 1540343) (by norm_num)
theorem B2738387 : Blo 2163435 2738387 := bstep (se 1 (by rfl) ⟨2053790, by rfl⟩ : syracuseStep 2738387 = 4107581) B4107581
theorem B7302365 : Blo 2163435 7302365 := bstep (se 3 (by rfl) ⟨1369193, by rfl⟩ : syracuseStep 7302365 = 2738387) B2738387
theorem B4868243 : Blo 2163435 4868243 := bstep (se 1 (by rfl) ⟨3651182, by rfl⟩ : syracuseStep 4868243 = 7302365) B7302365
theorem B3245495 : Blo 2163435 3245495 := bstep (se 1 (by rfl) ⟨2434121, by rfl⟩ : syracuseStep 3245495 = 4868243) B4868243
theorem B2163663 : Blo 2163435 2163663 := bstep (se 1 (by rfl) ⟨1622747, by rfl⟩ : syracuseStep 2163663 = 3245495) B3245495
theorem B3245501 : Blo 2163435 3245501 := bbase (se 3 (by rfl) ⟨608531, by rfl⟩ : syracuseStep 3245501 = 1217063) (by norm_num)
theorem B2163667 : Blo 2163435 2163667 := bstep (se 1 (by rfl) ⟨1622750, by rfl⟩ : syracuseStep 2163667 = 3245501) B3245501
theorem B4868261 : Blo 2163435 4868261 := bbase (se 4 (by rfl) ⟨456399, by rfl⟩ : syracuseStep 4868261 = 912799) (by norm_num)
theorem B3245507 : Blo 2163435 3245507 := bstep (se 1 (by rfl) ⟨2434130, by rfl⟩ : syracuseStep 3245507 = 4868261) B4868261
theorem B2163671 : Blo 2163435 2163671 := bstep (se 1 (by rfl) ⟨1622753, by rfl⟩ : syracuseStep 2163671 = 3245507) B3245507
theorem B5476805 : Blo 2163435 5476805 := bbase (se 4 (by rfl) ⟨513450, by rfl⟩ : syracuseStep 5476805 = 1026901) (by norm_num)
theorem B3651203 : Blo 2163435 3651203 := bstep (se 1 (by rfl) ⟨2738402, by rfl⟩ : syracuseStep 3651203 = 5476805) B5476805
theorem B2434135 : Blo 2163435 2434135 := bstep (se 1 (by rfl) ⟨1825601, by rfl⟩ : syracuseStep 2434135 = 3651203) B3651203
theorem B3245513 : Blo 2163435 3245513 := bstep (se 2 (by rfl) ⟨1217067, by rfl⟩ : syracuseStep 3245513 = 2434135) B2434135
theorem B2163675 : Blo 2163435 2163675 := bstep (se 1 (by rfl) ⟨1622756, by rfl⟩ : syracuseStep 2163675 = 3245513) B3245513
theorem B5551541 : Blo 2163435 5551541 := bbase (se 5 (by rfl) ⟨260228, by rfl⟩ : syracuseStep 5551541 = 520457) (by norm_num)
theorem B3701027 : Blo 2163435 3701027 := bstep (se 1 (by rfl) ⟨2775770, by rfl⟩ : syracuseStep 3701027 = 5551541) B5551541
theorem B2467351 : Blo 2163435 2467351 := bstep (se 1 (by rfl) ⟨1850513, by rfl⟩ : syracuseStep 2467351 = 3701027) B3701027
theorem B3289801 : Blo 2163435 3289801 := bstep (se 2 (by rfl) ⟨1233675, by rfl⟩ : syracuseStep 3289801 = 2467351) B2467351
theorem B4386401 : Blo 2163435 4386401 := bstep (se 2 (by rfl) ⟨1644900, by rfl⟩ : syracuseStep 4386401 = 3289801) B3289801
theorem B2924267 : Blo 2163435 2924267 := bstep (se 1 (by rfl) ⟨2193200, by rfl⟩ : syracuseStep 2924267 = 4386401) B4386401
theorem B7798045 : Blo 2163435 7798045 := bstep (se 3 (by rfl) ⟨1462133, by rfl⟩ : syracuseStep 7798045 = 2924267) B2924267
theorem B10397393 : Blo 2163435 10397393 := bstep (se 2 (by rfl) ⟨3899022, by rfl⟩ : syracuseStep 10397393 = 7798045) B7798045
theorem B6931595 : Blo 2163435 6931595 := bstep (se 1 (by rfl) ⟨5198696, by rfl⟩ : syracuseStep 6931595 = 10397393) B10397393
theorem B4621063 : Blo 2163435 4621063 := bstep (se 1 (by rfl) ⟨3465797, by rfl⟩ : syracuseStep 4621063 = 6931595) B6931595
theorem B6161417 : Blo 2163435 6161417 := bstep (se 2 (by rfl) ⟨2310531, by rfl⟩ : syracuseStep 6161417 = 4621063) B4621063
theorem B4107611 : Blo 2163435 4107611 := bstep (se 1 (by rfl) ⟨3080708, by rfl⟩ : syracuseStep 4107611 = 6161417) B6161417
theorem B10953629 : Blo 2163435 10953629 := bstep (se 3 (by rfl) ⟨2053805, by rfl⟩ : syracuseStep 10953629 = 4107611) B4107611
theorem B7302419 : Blo 2163435 7302419 := bstep (se 1 (by rfl) ⟨5476814, by rfl⟩ : syracuseStep 7302419 = 10953629) B10953629
theorem B4868279 : Blo 2163435 4868279 := bstep (se 1 (by rfl) ⟨3651209, by rfl⟩ : syracuseStep 4868279 = 7302419) B7302419
theorem B3245519 : Blo 2163435 3245519 := bstep (se 1 (by rfl) ⟨2434139, by rfl⟩ : syracuseStep 3245519 = 4868279) B4868279
theorem B2163679 : Blo 2163435 2163679 := bstep (se 1 (by rfl) ⟨1622759, by rfl⟩ : syracuseStep 2163679 = 3245519) B3245519
theorem B3245525 : Blo 2163435 3245525 := bbase (se 7 (by rfl) ⟨38033, by rfl⟩ : syracuseStep 3245525 = 76067) (by norm_num)
theorem B2163683 : Blo 2163435 2163683 := bstep (se 1 (by rfl) ⟨1622762, by rfl⟩ : syracuseStep 2163683 = 3245525) B3245525
theorem B8215253 : Blo 2163435 8215253 := bbase (se 7 (by rfl) ⟨96272, by rfl⟩ : syracuseStep 8215253 = 192545) (by norm_num)
theorem B5476835 : Blo 2163435 5476835 := bstep (se 1 (by rfl) ⟨4107626, by rfl⟩ : syracuseStep 5476835 = 8215253) B8215253
theorem B3651223 : Blo 2163435 3651223 := bstep (se 1 (by rfl) ⟨2738417, by rfl⟩ : syracuseStep 3651223 = 5476835) B5476835
theorem B4868297 : Blo 2163435 4868297 := bstep (se 2 (by rfl) ⟨1825611, by rfl⟩ : syracuseStep 4868297 = 3651223) B3651223
theorem B3245531 : Blo 2163435 3245531 := bstep (se 1 (by rfl) ⟨2434148, by rfl⟩ : syracuseStep 3245531 = 4868297) B4868297
theorem B2163687 : Blo 2163435 2163687 := bstep (se 1 (by rfl) ⟨1622765, by rfl⟩ : syracuseStep 2163687 = 3245531) B3245531
theorem B2434153 : Blo 2163435 2434153 := bbase (se 2 (by rfl) ⟨912807, by rfl⟩ : syracuseStep 2434153 = 1825615) (by norm_num)
theorem B3245537 : Blo 2163435 3245537 := bstep (se 2 (by rfl) ⟨1217076, by rfl⟩ : syracuseStep 3245537 = 2434153) B2434153
theorem B2163691 : Blo 2163435 2163691 := bstep (se 1 (by rfl) ⟨1622768, by rfl⟩ : syracuseStep 2163691 = 3245537) B3245537
theorem B2467369 : Blo 2163435 2467369 := bbase (se 2 (by rfl) ⟨925263, by rfl⟩ : syracuseStep 2467369 = 1850527) (by norm_num)
theorem B3289825 : Blo 2163435 3289825 := bstep (se 2 (by rfl) ⟨1233684, by rfl⟩ : syracuseStep 3289825 = 2467369) B2467369
theorem B17545733 : Blo 2163435 17545733 := bstep (se 4 (by rfl) ⟨1644912, by rfl⟩ : syracuseStep 17545733 = 3289825) B3289825
theorem B11697155 : Blo 2163435 11697155 := bstep (se 1 (by rfl) ⟨8772866, by rfl⟩ : syracuseStep 11697155 = 17545733) B17545733
theorem B7798103 : Blo 2163435 7798103 := bstep (se 1 (by rfl) ⟨5848577, by rfl⟩ : syracuseStep 7798103 = 11697155) B11697155
theorem B5198735 : Blo 2163435 5198735 := bstep (se 1 (by rfl) ⟨3899051, by rfl⟩ : syracuseStep 5198735 = 7798103) B7798103
theorem B3465823 : Blo 2163435 3465823 := bstep (se 1 (by rfl) ⟨2599367, by rfl⟩ : syracuseStep 3465823 = 5198735) B5198735
theorem B4621097 : Blo 2163435 4621097 := bstep (se 2 (by rfl) ⟨1732911, by rfl⟩ : syracuseStep 4621097 = 3465823) B3465823
theorem B12322925 : Blo 2163435 12322925 := bstep (se 3 (by rfl) ⟨2310548, by rfl⟩ : syracuseStep 12322925 = 4621097) B4621097
theorem B8215283 : Blo 2163435 8215283 := bstep (se 1 (by rfl) ⟨6161462, by rfl⟩ : syracuseStep 8215283 = 12322925) B12322925
theorem B5476855 : Blo 2163435 5476855 := bstep (se 1 (by rfl) ⟨4107641, by rfl⟩ : syracuseStep 5476855 = 8215283) B8215283
theorem B7302473 : Blo 2163435 7302473 := bstep (se 2 (by rfl) ⟨2738427, by rfl⟩ : syracuseStep 7302473 = 5476855) B5476855
theorem B4868315 : Blo 2163435 4868315 := bstep (se 1 (by rfl) ⟨3651236, by rfl⟩ : syracuseStep 4868315 = 7302473) B7302473
theorem B3245543 : Blo 2163435 3245543 := bstep (se 1 (by rfl) ⟨2434157, by rfl⟩ : syracuseStep 3245543 = 4868315) B4868315
theorem B2163695 : Blo 2163435 2163695 := bstep (se 1 (by rfl) ⟨1622771, by rfl⟩ : syracuseStep 2163695 = 3245543) B3245543
theorem B3245549 : Blo 2163435 3245549 := bbase (se 3 (by rfl) ⟨608540, by rfl⟩ : syracuseStep 3245549 = 1217081) (by norm_num)
theorem B2163699 : Blo 2163435 2163699 := bstep (se 1 (by rfl) ⟨1622774, by rfl⟩ : syracuseStep 2163699 = 3245549) B3245549
theorem B4868333 : Blo 2163435 4868333 := bbase (se 3 (by rfl) ⟨912812, by rfl⟩ : syracuseStep 4868333 = 1825625) (by norm_num)
theorem B3245555 : Blo 2163435 3245555 := bstep (se 1 (by rfl) ⟨2434166, by rfl⟩ : syracuseStep 3245555 = 4868333) B4868333
theorem B2163703 : Blo 2163435 2163703 := bstep (se 1 (by rfl) ⟨1622777, by rfl⟩ : syracuseStep 2163703 = 3245555) B3245555
theorem B3080749 : Blo 2163435 3080749 := bbase (se 3 (by rfl) ⟨577640, by rfl⟩ : syracuseStep 3080749 = 1155281) (by norm_num)
theorem B4107665 : Blo 2163435 4107665 := bstep (se 2 (by rfl) ⟨1540374, by rfl⟩ : syracuseStep 4107665 = 3080749) B3080749
theorem B2738443 : Blo 2163435 2738443 := bstep (se 1 (by rfl) ⟨2053832, by rfl⟩ : syracuseStep 2738443 = 4107665) B4107665
theorem B3651257 : Blo 2163435 3651257 := bstep (se 2 (by rfl) ⟨1369221, by rfl⟩ : syracuseStep 3651257 = 2738443) B2738443
theorem B2434171 : Blo 2163435 2434171 := bstep (se 1 (by rfl) ⟨1825628, by rfl⟩ : syracuseStep 2434171 = 3651257) B3651257
theorem B3245561 : Blo 2163435 3245561 := bstep (se 2 (by rfl) ⟨1217085, by rfl⟩ : syracuseStep 3245561 = 2434171) B2434171
theorem B2163707 : Blo 2163435 2163707 := bstep (se 1 (by rfl) ⟨1622780, by rfl⟩ : syracuseStep 2163707 = 3245561) B3245561
theorem B4934773 : Blo 2163435 4934773 := bbase (se 5 (by rfl) ⟨231317, by rfl⟩ : syracuseStep 4934773 = 462635) (by norm_num)
theorem B6579697 : Blo 2163435 6579697 := bstep (se 2 (by rfl) ⟨2467386, by rfl⟩ : syracuseStep 6579697 = 4934773) B4934773
theorem B8772929 : Blo 2163435 8772929 := bstep (se 2 (by rfl) ⟨3289848, by rfl⟩ : syracuseStep 8772929 = 6579697) B6579697
theorem B5848619 : Blo 2163435 5848619 := bstep (se 1 (by rfl) ⟨4386464, by rfl⟩ : syracuseStep 5848619 = 8772929) B8772929
theorem B15596317 : Blo 2163435 15596317 := bstep (se 3 (by rfl) ⟨2924309, by rfl⟩ : syracuseStep 15596317 = 5848619) B5848619
theorem B83180357 : Blo 2163435 83180357 := bstep (se 4 (by rfl) ⟨7798158, by rfl⟩ : syracuseStep 83180357 = 15596317) B15596317
theorem B55453571 : Blo 2163435 55453571 := bstep (se 1 (by rfl) ⟨41590178, by rfl⟩ : syracuseStep 55453571 = 83180357) B83180357
theorem B36969047 : Blo 2163435 36969047 := bstep (se 1 (by rfl) ⟨27726785, by rfl⟩ : syracuseStep 36969047 = 55453571) B55453571
theorem B24646031 : Blo 2163435 24646031 := bstep (se 1 (by rfl) ⟨18484523, by rfl⟩ : syracuseStep 24646031 = 36969047) B36969047
theorem B16430687 : Blo 2163435 16430687 := bstep (se 1 (by rfl) ⟨12323015, by rfl⟩ : syracuseStep 16430687 = 24646031) B24646031
theorem B10953791 : Blo 2163435 10953791 := bstep (se 1 (by rfl) ⟨8215343, by rfl⟩ : syracuseStep 10953791 = 16430687) B16430687
theorem B7302527 : Blo 2163435 7302527 := bstep (se 1 (by rfl) ⟨5476895, by rfl⟩ : syracuseStep 7302527 = 10953791) B10953791
theorem B4868351 : Blo 2163435 4868351 := bstep (se 1 (by rfl) ⟨3651263, by rfl⟩ : syracuseStep 4868351 = 7302527) B7302527
theorem B3245567 : Blo 2163435 3245567 := bstep (se 1 (by rfl) ⟨2434175, by rfl⟩ : syracuseStep 3245567 = 4868351) B4868351
theorem B2163711 : Blo 2163435 2163711 := bstep (se 1 (by rfl) ⟨1622783, by rfl⟩ : syracuseStep 2163711 = 3245567) B3245567
theorem B3245573 : Blo 2163435 3245573 := bbase (se 4 (by rfl) ⟨304272, by rfl⟩ : syracuseStep 3245573 = 608545) (by norm_num)
theorem B2163715 : Blo 2163435 2163715 := bstep (se 1 (by rfl) ⟨1622786, by rfl⟩ : syracuseStep 2163715 = 3245573) B3245573
theorem B3651277 : Blo 2163435 3651277 := bbase (se 3 (by rfl) ⟨684614, by rfl⟩ : syracuseStep 3651277 = 1369229) (by norm_num)
theorem B4868369 : Blo 2163435 4868369 := bstep (se 2 (by rfl) ⟨1825638, by rfl⟩ : syracuseStep 4868369 = 3651277) B3651277
theorem B3245579 : Blo 2163435 3245579 := bstep (se 1 (by rfl) ⟨2434184, by rfl⟩ : syracuseStep 3245579 = 4868369) B4868369
theorem B2163719 : Blo 2163435 2163719 := bstep (se 1 (by rfl) ⟨1622789, by rfl⟩ : syracuseStep 2163719 = 3245579) B3245579
theorem B2434189 : Blo 2163435 2434189 := bbase (se 3 (by rfl) ⟨456410, by rfl⟩ : syracuseStep 2434189 = 912821) (by norm_num)
theorem B3245585 : Blo 2163435 3245585 := bstep (se 2 (by rfl) ⟨1217094, by rfl⟩ : syracuseStep 3245585 = 2434189) B2434189
theorem B2163723 : Blo 2163435 2163723 := bstep (se 1 (by rfl) ⟨1622792, by rfl⟩ : syracuseStep 2163723 = 3245585) B3245585
theorem B7302581 : Blo 2163435 7302581 := bbase (se 5 (by rfl) ⟨342308, by rfl⟩ : syracuseStep 7302581 = 684617) (by norm_num)
theorem B4868387 : Blo 2163435 4868387 := bstep (se 1 (by rfl) ⟨3651290, by rfl⟩ : syracuseStep 4868387 = 7302581) B7302581
theorem B3245591 : Blo 2163435 3245591 := bstep (se 1 (by rfl) ⟨2434193, by rfl⟩ : syracuseStep 3245591 = 4868387) B4868387
theorem B2163727 : Blo 2163435 2163727 := bstep (se 1 (by rfl) ⟨1622795, by rfl⟩ : syracuseStep 2163727 = 3245591) B3245591
theorem B3245597 : Blo 2163435 3245597 := bbase (se 3 (by rfl) ⟨608549, by rfl⟩ : syracuseStep 3245597 = 1217099) (by norm_num)
theorem B2163731 : Blo 2163435 2163731 := bstep (se 1 (by rfl) ⟨1622798, by rfl⟩ : syracuseStep 2163731 = 3245597) B3245597
theorem B4868405 : Blo 2163435 4868405 := bbase (se 5 (by rfl) ⟨228206, by rfl⟩ : syracuseStep 4868405 = 456413) (by norm_num)
theorem B3245603 : Blo 2163435 3245603 := bstep (se 1 (by rfl) ⟨2434202, by rfl⟩ : syracuseStep 3245603 = 4868405) B4868405
theorem B2163735 : Blo 2163435 2163735 := bstep (se 1 (by rfl) ⟨1622801, by rfl⟩ : syracuseStep 2163735 = 3245603) B3245603
theorem B31193045 : Blo 2163435 31193045 := bbase (se 7 (by rfl) ⟨365543, by rfl⟩ : syracuseStep 31193045 = 731087) (by norm_num)
theorem B20795363 : Blo 2163435 20795363 := bstep (se 1 (by rfl) ⟨15596522, by rfl⟩ : syracuseStep 20795363 = 31193045) B31193045
theorem B13863575 : Blo 2163435 13863575 := bstep (se 1 (by rfl) ⟨10397681, by rfl⟩ : syracuseStep 13863575 = 20795363) B20795363
theorem B9242383 : Blo 2163435 9242383 := bstep (se 1 (by rfl) ⟨6931787, by rfl⟩ : syracuseStep 9242383 = 13863575) B13863575
theorem B12323177 : Blo 2163435 12323177 := bstep (se 2 (by rfl) ⟨4621191, by rfl⟩ : syracuseStep 12323177 = 9242383) B9242383
theorem B8215451 : Blo 2163435 8215451 := bstep (se 1 (by rfl) ⟨6161588, by rfl⟩ : syracuseStep 8215451 = 12323177) B12323177
theorem B5476967 : Blo 2163435 5476967 := bstep (se 1 (by rfl) ⟨4107725, by rfl⟩ : syracuseStep 5476967 = 8215451) B8215451
theorem B3651311 : Blo 2163435 3651311 := bstep (se 1 (by rfl) ⟨2738483, by rfl⟩ : syracuseStep 3651311 = 5476967) B5476967
theorem B2434207 : Blo 2163435 2434207 := bstep (se 1 (by rfl) ⟨1825655, by rfl⟩ : syracuseStep 2434207 = 3651311) B3651311
theorem B3245609 : Blo 2163435 3245609 := bstep (se 2 (by rfl) ⟨1217103, by rfl⟩ : syracuseStep 3245609 = 2434207) B2434207
theorem B2163739 : Blo 2163435 2163739 := bstep (se 1 (by rfl) ⟨1622804, by rfl⟩ : syracuseStep 2163739 = 3245609) B3245609
theorem B2342125 : Blo 2163435 2342125 := bbase (se 3 (by rfl) ⟨439148, by rfl⟩ : syracuseStep 2342125 = 878297) (by norm_num)
theorem B12491333 : Blo 2163435 12491333 := bstep (se 4 (by rfl) ⟨1171062, by rfl⟩ : syracuseStep 12491333 = 2342125) B2342125
theorem B8327555 : Blo 2163435 8327555 := bstep (se 1 (by rfl) ⟨6245666, by rfl⟩ : syracuseStep 8327555 = 12491333) B12491333
theorem B5551703 : Blo 2163435 5551703 := bstep (se 1 (by rfl) ⟨4163777, by rfl⟩ : syracuseStep 5551703 = 8327555) B8327555
theorem B3701135 : Blo 2163435 3701135 := bstep (se 1 (by rfl) ⟨2775851, by rfl⟩ : syracuseStep 3701135 = 5551703) B5551703
theorem B2467423 : Blo 2163435 2467423 := bstep (se 1 (by rfl) ⟨1850567, by rfl⟩ : syracuseStep 2467423 = 3701135) B3701135
theorem B13159589 : Blo 2163435 13159589 := bstep (se 4 (by rfl) ⟨1233711, by rfl⟩ : syracuseStep 13159589 = 2467423) B2467423
theorem B35092237 : Blo 2163435 35092237 := bstep (se 3 (by rfl) ⟨6579794, by rfl⟩ : syracuseStep 35092237 = 13159589) B13159589
theorem B46789649 : Blo 2163435 46789649 := bstep (se 2 (by rfl) ⟨17546118, by rfl⟩ : syracuseStep 46789649 = 35092237) B35092237
theorem B31193099 : Blo 2163435 31193099 := bstep (se 1 (by rfl) ⟨23394824, by rfl⟩ : syracuseStep 31193099 = 46789649) B46789649
theorem B20795399 : Blo 2163435 20795399 := bstep (se 1 (by rfl) ⟨15596549, by rfl⟩ : syracuseStep 20795399 = 31193099) B31193099
theorem B13863599 : Blo 2163435 13863599 := bstep (se 1 (by rfl) ⟨10397699, by rfl⟩ : syracuseStep 13863599 = 20795399) B20795399
theorem B9242399 : Blo 2163435 9242399 := bstep (se 1 (by rfl) ⟨6931799, by rfl⟩ : syracuseStep 9242399 = 13863599) B13863599
theorem B6161599 : Blo 2163435 6161599 := bstep (se 1 (by rfl) ⟨4621199, by rfl⟩ : syracuseStep 6161599 = 9242399) B9242399
theorem B8215465 : Blo 2163435 8215465 := bstep (se 2 (by rfl) ⟨3080799, by rfl⟩ : syracuseStep 8215465 = 6161599) B6161599
theorem B10953953 : Blo 2163435 10953953 := bstep (se 2 (by rfl) ⟨4107732, by rfl⟩ : syracuseStep 10953953 = 8215465) B8215465
theorem B7302635 : Blo 2163435 7302635 := bstep (se 1 (by rfl) ⟨5476976, by rfl⟩ : syracuseStep 7302635 = 10953953) B10953953
theorem B4868423 : Blo 2163435 4868423 := bstep (se 1 (by rfl) ⟨3651317, by rfl⟩ : syracuseStep 4868423 = 7302635) B7302635
theorem B3245615 : Blo 2163435 3245615 := bstep (se 1 (by rfl) ⟨2434211, by rfl⟩ : syracuseStep 3245615 = 4868423) B4868423
theorem B2163743 : Blo 2163435 2163743 := bstep (se 1 (by rfl) ⟨1622807, by rfl⟩ : syracuseStep 2163743 = 3245615) B3245615
theorem B3245621 : Blo 2163435 3245621 := bbase (se 5 (by rfl) ⟨152138, by rfl⟩ : syracuseStep 3245621 = 304277) (by norm_num)
theorem B2163747 : Blo 2163435 2163747 := bstep (se 1 (by rfl) ⟨1622810, by rfl⟩ : syracuseStep 2163747 = 3245621) B3245621
theorem B5476997 : Blo 2163435 5476997 := bbase (se 4 (by rfl) ⟨513468, by rfl⟩ : syracuseStep 5476997 = 1026937) (by norm_num)
theorem B3651331 : Blo 2163435 3651331 := bstep (se 1 (by rfl) ⟨2738498, by rfl⟩ : syracuseStep 3651331 = 5476997) B5476997
theorem B4868441 : Blo 2163435 4868441 := bstep (se 2 (by rfl) ⟨1825665, by rfl⟩ : syracuseStep 4868441 = 3651331) B3651331
theorem B3245627 : Blo 2163435 3245627 := bstep (se 1 (by rfl) ⟨2434220, by rfl⟩ : syracuseStep 3245627 = 4868441) B4868441
theorem B2163751 : Blo 2163435 2163751 := bstep (se 1 (by rfl) ⟨1622813, by rfl⟩ : syracuseStep 2163751 = 3245627) B3245627
theorem B2434225 : Blo 2163435 2434225 := bbase (se 2 (by rfl) ⟨912834, by rfl⟩ : syracuseStep 2434225 = 1825669) (by norm_num)
theorem B3245633 : Blo 2163435 3245633 := bstep (se 2 (by rfl) ⟨1217112, by rfl⟩ : syracuseStep 3245633 = 2434225) B2434225
theorem B2163755 : Blo 2163435 2163755 := bstep (se 1 (by rfl) ⟨1622816, by rfl⟩ : syracuseStep 2163755 = 3245633) B3245633
theorem B2310617 : Blo 2163435 2310617 := bbase (se 2 (by rfl) ⟨866481, by rfl⟩ : syracuseStep 2310617 = 1732963) (by norm_num)
theorem B6161645 : Blo 2163435 6161645 := bstep (se 3 (by rfl) ⟨1155308, by rfl⟩ : syracuseStep 6161645 = 2310617) B2310617
theorem B4107763 : Blo 2163435 4107763 := bstep (se 1 (by rfl) ⟨3080822, by rfl⟩ : syracuseStep 4107763 = 6161645) B6161645
theorem B5477017 : Blo 2163435 5477017 := bstep (se 2 (by rfl) ⟨2053881, by rfl⟩ : syracuseStep 5477017 = 4107763) B4107763
theorem B7302689 : Blo 2163435 7302689 := bstep (se 2 (by rfl) ⟨2738508, by rfl⟩ : syracuseStep 7302689 = 5477017) B5477017
theorem B4868459 : Blo 2163435 4868459 := bstep (se 1 (by rfl) ⟨3651344, by rfl⟩ : syracuseStep 4868459 = 7302689) B7302689
theorem B3245639 : Blo 2163435 3245639 := bstep (se 1 (by rfl) ⟨2434229, by rfl⟩ : syracuseStep 3245639 = 4868459) B4868459
theorem B2163759 : Blo 2163435 2163759 := bstep (se 1 (by rfl) ⟨1622819, by rfl⟩ : syracuseStep 2163759 = 3245639) B3245639
theorem B3245645 : Blo 2163435 3245645 := bbase (se 3 (by rfl) ⟨608558, by rfl⟩ : syracuseStep 3245645 = 1217117) (by norm_num)
theorem B2163763 : Blo 2163435 2163763 := bstep (se 1 (by rfl) ⟨1622822, by rfl⟩ : syracuseStep 2163763 = 3245645) B3245645
theorem B4868477 : Blo 2163435 4868477 := bbase (se 3 (by rfl) ⟨912839, by rfl⟩ : syracuseStep 4868477 = 1825679) (by norm_num)
theorem B3245651 : Blo 2163435 3245651 := bstep (se 1 (by rfl) ⟨2434238, by rfl⟩ : syracuseStep 3245651 = 4868477) B4868477
theorem B2163767 : Blo 2163435 2163767 := bstep (se 1 (by rfl) ⟨1622825, by rfl⟩ : syracuseStep 2163767 = 3245651) B3245651
theorem B3651365 : Blo 2163435 3651365 := bbase (se 4 (by rfl) ⟨342315, by rfl⟩ : syracuseStep 3651365 = 684631) (by norm_num)
theorem B2434243 : Blo 2163435 2434243 := bstep (se 1 (by rfl) ⟨1825682, by rfl⟩ : syracuseStep 2434243 = 3651365) B3651365
theorem B3245657 : Blo 2163435 3245657 := bstep (se 2 (by rfl) ⟨1217121, by rfl⟩ : syracuseStep 3245657 = 2434243) B2434243
theorem B2163771 : Blo 2163435 2163771 := bstep (se 1 (by rfl) ⟨1622828, by rfl⟩ : syracuseStep 2163771 = 3245657) B3245657
theorem B3080845 : Blo 2163435 3080845 := bbase (se 3 (by rfl) ⟨577658, by rfl⟩ : syracuseStep 3080845 = 1155317) (by norm_num)
theorem B16431173 : Blo 2163435 16431173 := bstep (se 4 (by rfl) ⟨1540422, by rfl⟩ : syracuseStep 16431173 = 3080845) B3080845
theorem B10954115 : Blo 2163435 10954115 := bstep (se 1 (by rfl) ⟨8215586, by rfl⟩ : syracuseStep 10954115 = 16431173) B16431173
theorem B7302743 : Blo 2163435 7302743 := bstep (se 1 (by rfl) ⟨5477057, by rfl⟩ : syracuseStep 7302743 = 10954115) B10954115
theorem B4868495 : Blo 2163435 4868495 := bstep (se 1 (by rfl) ⟨3651371, by rfl⟩ : syracuseStep 4868495 = 7302743) B7302743
theorem B3245663 : Blo 2163435 3245663 := bstep (se 1 (by rfl) ⟨2434247, by rfl⟩ : syracuseStep 3245663 = 4868495) B4868495
theorem B2163775 : Blo 2163435 2163775 := bstep (se 1 (by rfl) ⟨1622831, by rfl⟩ : syracuseStep 2163775 = 3245663) B3245663
theorem B3245669 : Blo 2163435 3245669 := bbase (se 4 (by rfl) ⟨304281, by rfl⟩ : syracuseStep 3245669 = 608563) (by norm_num)
theorem B2163779 : Blo 2163435 2163779 := bstep (se 1 (by rfl) ⟨1622834, by rfl⟩ : syracuseStep 2163779 = 3245669) B3245669
theorem B3465965 : Blo 2163435 3465965 := bbase (se 3 (by rfl) ⟨649868, by rfl⟩ : syracuseStep 3465965 = 1299737) (by norm_num)
theorem B2310643 : Blo 2163435 2310643 := bstep (se 1 (by rfl) ⟨1732982, by rfl⟩ : syracuseStep 2310643 = 3465965) B3465965
theorem B3080857 : Blo 2163435 3080857 := bstep (se 2 (by rfl) ⟨1155321, by rfl⟩ : syracuseStep 3080857 = 2310643) B2310643
theorem B4107809 : Blo 2163435 4107809 := bstep (se 2 (by rfl) ⟨1540428, by rfl⟩ : syracuseStep 4107809 = 3080857) B3080857
theorem B2738539 : Blo 2163435 2738539 := bstep (se 1 (by rfl) ⟨2053904, by rfl⟩ : syracuseStep 2738539 = 4107809) B4107809
theorem B3651385 : Blo 2163435 3651385 := bstep (se 2 (by rfl) ⟨1369269, by rfl⟩ : syracuseStep 3651385 = 2738539) B2738539
theorem B4868513 : Blo 2163435 4868513 := bstep (se 2 (by rfl) ⟨1825692, by rfl⟩ : syracuseStep 4868513 = 3651385) B3651385
theorem B3245675 : Blo 2163435 3245675 := bstep (se 1 (by rfl) ⟨2434256, by rfl⟩ : syracuseStep 3245675 = 4868513) B4868513
theorem B2163783 : Blo 2163435 2163783 := bstep (se 1 (by rfl) ⟨1622837, by rfl⟩ : syracuseStep 2163783 = 3245675) B3245675
theorem B2434261 : Blo 2163435 2434261 := bbase (se 7 (by rfl) ⟨28526, by rfl⟩ : syracuseStep 2434261 = 57053) (by norm_num)
theorem B3245681 : Blo 2163435 3245681 := bstep (se 2 (by rfl) ⟨1217130, by rfl⟩ : syracuseStep 3245681 = 2434261) B2434261
theorem B2163787 : Blo 2163435 2163787 := bstep (se 1 (by rfl) ⟨1622840, by rfl⟩ : syracuseStep 2163787 = 3245681) B3245681
theorem B2738549 : Blo 2163435 2738549 := bbase (se 5 (by rfl) ⟨128369, by rfl⟩ : syracuseStep 2738549 = 256739) (by norm_num)
theorem B7302797 : Blo 2163435 7302797 := bstep (se 3 (by rfl) ⟨1369274, by rfl⟩ : syracuseStep 7302797 = 2738549) B2738549
theorem B4868531 : Blo 2163435 4868531 := bstep (se 1 (by rfl) ⟨3651398, by rfl⟩ : syracuseStep 4868531 = 7302797) B7302797
theorem B3245687 : Blo 2163435 3245687 := bstep (se 1 (by rfl) ⟨2434265, by rfl⟩ : syracuseStep 3245687 = 4868531) B4868531
theorem B2163791 : Blo 2163435 2163791 := bstep (se 1 (by rfl) ⟨1622843, by rfl⟩ : syracuseStep 2163791 = 3245687) B3245687
theorem B3245693 : Blo 2163435 3245693 := bbase (se 3 (by rfl) ⟨608567, by rfl⟩ : syracuseStep 3245693 = 1217135) (by norm_num)
theorem B2163795 : Blo 2163435 2163795 := bstep (se 1 (by rfl) ⟨1622846, by rfl⟩ : syracuseStep 2163795 = 3245693) B3245693
theorem B4868549 : Blo 2163435 4868549 := bbase (se 4 (by rfl) ⟨456426, by rfl⟩ : syracuseStep 4868549 = 912853) (by norm_num)
theorem B3245699 : Blo 2163435 3245699 := bstep (se 1 (by rfl) ⟨2434274, by rfl⟩ : syracuseStep 3245699 = 4868549) B4868549
theorem B2163799 : Blo 2163435 2163799 := bstep (se 1 (by rfl) ⟨1622849, by rfl⟩ : syracuseStep 2163799 = 3245699) B3245699
theorem B4386653 : Blo 2163435 4386653 := bbase (se 3 (by rfl) ⟨822497, by rfl⟩ : syracuseStep 4386653 = 1644995) (by norm_num)
theorem B2924435 : Blo 2163435 2924435 := bstep (se 1 (by rfl) ⟨2193326, by rfl⟩ : syracuseStep 2924435 = 4386653) B4386653
theorem B7798493 : Blo 2163435 7798493 := bstep (se 3 (by rfl) ⟨1462217, by rfl⟩ : syracuseStep 7798493 = 2924435) B2924435
theorem B5198995 : Blo 2163435 5198995 := bstep (se 1 (by rfl) ⟨3899246, by rfl⟩ : syracuseStep 5198995 = 7798493) B7798493
theorem B6931993 : Blo 2163435 6931993 := bstep (se 2 (by rfl) ⟨2599497, by rfl⟩ : syracuseStep 6931993 = 5198995) B5198995
theorem B9242657 : Blo 2163435 9242657 := bstep (se 2 (by rfl) ⟨3465996, by rfl⟩ : syracuseStep 9242657 = 6931993) B6931993
theorem B6161771 : Blo 2163435 6161771 := bstep (se 1 (by rfl) ⟨4621328, by rfl⟩ : syracuseStep 6161771 = 9242657) B9242657
theorem B4107847 : Blo 2163435 4107847 := bstep (se 1 (by rfl) ⟨3080885, by rfl⟩ : syracuseStep 4107847 = 6161771) B6161771
theorem B5477129 : Blo 2163435 5477129 := bstep (se 2 (by rfl) ⟨2053923, by rfl⟩ : syracuseStep 5477129 = 4107847) B4107847
theorem B3651419 : Blo 2163435 3651419 := bstep (se 1 (by rfl) ⟨2738564, by rfl⟩ : syracuseStep 3651419 = 5477129) B5477129
theorem B2434279 : Blo 2163435 2434279 := bstep (se 1 (by rfl) ⟨1825709, by rfl⟩ : syracuseStep 2434279 = 3651419) B3651419
theorem B3245705 : Blo 2163435 3245705 := bstep (se 2 (by rfl) ⟨1217139, by rfl⟩ : syracuseStep 3245705 = 2434279) B2434279
theorem B2163803 : Blo 2163435 2163803 := bstep (se 1 (by rfl) ⟨1622852, by rfl⟩ : syracuseStep 2163803 = 3245705) B3245705
theorem B10954277 : Blo 2163435 10954277 := bbase (se 4 (by rfl) ⟨1026963, by rfl⟩ : syracuseStep 10954277 = 2053927) (by norm_num)
theorem B7302851 : Blo 2163435 7302851 := bstep (se 1 (by rfl) ⟨5477138, by rfl⟩ : syracuseStep 7302851 = 10954277) B10954277
theorem B4868567 : Blo 2163435 4868567 := bstep (se 1 (by rfl) ⟨3651425, by rfl⟩ : syracuseStep 4868567 = 7302851) B7302851
theorem B3245711 : Blo 2163435 3245711 := bstep (se 1 (by rfl) ⟨2434283, by rfl⟩ : syracuseStep 3245711 = 4868567) B4868567
theorem B2163807 : Blo 2163435 2163807 := bstep (se 1 (by rfl) ⟨1622855, by rfl⟩ : syracuseStep 2163807 = 3245711) B3245711
theorem B3245717 : Blo 2163435 3245717 := bbase (se 6 (by rfl) ⟨76071, by rfl⟩ : syracuseStep 3245717 = 152143) (by norm_num)
theorem B2163811 : Blo 2163435 2163811 := bstep (se 1 (by rfl) ⟨1622858, by rfl⟩ : syracuseStep 2163811 = 3245717) B3245717
theorem B7402517 : Blo 2163435 7402517 := bbase (se 6 (by rfl) ⟨173496, by rfl⟩ : syracuseStep 7402517 = 346993) (by norm_num)
theorem B4935011 : Blo 2163435 4935011 := bstep (se 1 (by rfl) ⟨3701258, by rfl⟩ : syracuseStep 4935011 = 7402517) B7402517
theorem B13160029 : Blo 2163435 13160029 := bstep (se 3 (by rfl) ⟨2467505, by rfl⟩ : syracuseStep 13160029 = 4935011) B4935011
theorem B17546705 : Blo 2163435 17546705 := bstep (se 2 (by rfl) ⟨6580014, by rfl⟩ : syracuseStep 17546705 = 13160029) B13160029
theorem B11697803 : Blo 2163435 11697803 := bstep (se 1 (by rfl) ⟨8773352, by rfl⟩ : syracuseStep 11697803 = 17546705) B17546705
theorem B7798535 : Blo 2163435 7798535 := bstep (se 1 (by rfl) ⟨5848901, by rfl⟩ : syracuseStep 7798535 = 11697803) B11697803
theorem B5199023 : Blo 2163435 5199023 := bstep (se 1 (by rfl) ⟨3899267, by rfl⟩ : syracuseStep 5199023 = 7798535) B7798535
theorem B13864061 : Blo 2163435 13864061 := bstep (se 3 (by rfl) ⟨2599511, by rfl⟩ : syracuseStep 13864061 = 5199023) B5199023
theorem B9242707 : Blo 2163435 9242707 := bstep (se 1 (by rfl) ⟨6932030, by rfl⟩ : syracuseStep 9242707 = 13864061) B13864061
theorem B12323609 : Blo 2163435 12323609 := bstep (se 2 (by rfl) ⟨4621353, by rfl⟩ : syracuseStep 12323609 = 9242707) B9242707
theorem B8215739 : Blo 2163435 8215739 := bstep (se 1 (by rfl) ⟨6161804, by rfl⟩ : syracuseStep 8215739 = 12323609) B12323609
theorem B5477159 : Blo 2163435 5477159 := bstep (se 1 (by rfl) ⟨4107869, by rfl⟩ : syracuseStep 5477159 = 8215739) B8215739
theorem B3651439 : Blo 2163435 3651439 := bstep (se 1 (by rfl) ⟨2738579, by rfl⟩ : syracuseStep 3651439 = 5477159) B5477159
theorem B4868585 : Blo 2163435 4868585 := bstep (se 2 (by rfl) ⟨1825719, by rfl⟩ : syracuseStep 4868585 = 3651439) B3651439
theorem B3245723 : Blo 2163435 3245723 := bstep (se 1 (by rfl) ⟨2434292, by rfl⟩ : syracuseStep 3245723 = 4868585) B4868585
theorem B2163815 : Blo 2163435 2163815 := bstep (se 1 (by rfl) ⟨1622861, by rfl⟩ : syracuseStep 2163815 = 3245723) B3245723
theorem B2434297 : Blo 2163435 2434297 := bbase (se 2 (by rfl) ⟨912861, by rfl⟩ : syracuseStep 2434297 = 1825723) (by norm_num)
theorem B3245729 : Blo 2163435 3245729 := bstep (se 2 (by rfl) ⟨1217148, by rfl⟩ : syracuseStep 3245729 = 2434297) B2434297
theorem B2163819 : Blo 2163435 2163819 := bstep (se 1 (by rfl) ⟨1622864, by rfl⟩ : syracuseStep 2163819 = 3245729) B3245729
theorem B9242741 : Blo 2163435 9242741 := bbase (se 5 (by rfl) ⟨433253, by rfl⟩ : syracuseStep 9242741 = 866507) (by norm_num)
theorem B6161827 : Blo 2163435 6161827 := bstep (se 1 (by rfl) ⟨4621370, by rfl⟩ : syracuseStep 6161827 = 9242741) B9242741
theorem B8215769 : Blo 2163435 8215769 := bstep (se 2 (by rfl) ⟨3080913, by rfl⟩ : syracuseStep 8215769 = 6161827) B6161827
theorem B5477179 : Blo 2163435 5477179 := bstep (se 1 (by rfl) ⟨4107884, by rfl⟩ : syracuseStep 5477179 = 8215769) B8215769
theorem B7302905 : Blo 2163435 7302905 := bstep (se 2 (by rfl) ⟨2738589, by rfl⟩ : syracuseStep 7302905 = 5477179) B5477179
theorem B4868603 : Blo 2163435 4868603 := bstep (se 1 (by rfl) ⟨3651452, by rfl⟩ : syracuseStep 4868603 = 7302905) B7302905
theorem B3245735 : Blo 2163435 3245735 := bstep (se 1 (by rfl) ⟨2434301, by rfl⟩ : syracuseStep 3245735 = 4868603) B4868603
theorem B2163823 : Blo 2163435 2163823 := bstep (se 1 (by rfl) ⟨1622867, by rfl⟩ : syracuseStep 2163823 = 3245735) B3245735
theorem B3245741 : Blo 2163435 3245741 := bbase (se 3 (by rfl) ⟨608576, by rfl⟩ : syracuseStep 3245741 = 1217153) (by norm_num)
theorem B2163827 : Blo 2163435 2163827 := bstep (se 1 (by rfl) ⟨1622870, by rfl⟩ : syracuseStep 2163827 = 3245741) B3245741
theorem B4868621 : Blo 2163435 4868621 := bbase (se 3 (by rfl) ⟨912866, by rfl⟩ : syracuseStep 4868621 = 1825733) (by norm_num)
theorem B3245747 : Blo 2163435 3245747 := bstep (se 1 (by rfl) ⟨2434310, by rfl⟩ : syracuseStep 3245747 = 4868621) B4868621
theorem B2163831 : Blo 2163435 2163831 := bstep (se 1 (by rfl) ⟨1622873, by rfl⟩ : syracuseStep 2163831 = 3245747) B3245747
theorem B2738605 : Blo 2163435 2738605 := bbase (se 3 (by rfl) ⟨513488, by rfl⟩ : syracuseStep 2738605 = 1026977) (by norm_num)
theorem B3651473 : Blo 2163435 3651473 := bstep (se 2 (by rfl) ⟨1369302, by rfl⟩ : syracuseStep 3651473 = 2738605) B2738605
theorem B2434315 : Blo 2163435 2434315 := bstep (se 1 (by rfl) ⟨1825736, by rfl⟩ : syracuseStep 2434315 = 3651473) B3651473
theorem B3245753 : Blo 2163435 3245753 := bstep (se 2 (by rfl) ⟨1217157, by rfl⟩ : syracuseStep 3245753 = 2434315) B2434315
theorem B2163835 : Blo 2163435 2163835 := bstep (se 1 (by rfl) ⟨1622876, by rfl⟩ : syracuseStep 2163835 = 3245753) B3245753
theorem B13864213 : Blo 2163435 13864213 := bbase (se 6 (by rfl) ⟨324942, by rfl⟩ : syracuseStep 13864213 = 649885) (by norm_num)
theorem B18485617 : Blo 2163435 18485617 := bstep (se 2 (by rfl) ⟨6932106, by rfl⟩ : syracuseStep 18485617 = 13864213) B13864213
theorem B24647489 : Blo 2163435 24647489 := bstep (se 2 (by rfl) ⟨9242808, by rfl⟩ : syracuseStep 24647489 = 18485617) B18485617
theorem B16431659 : Blo 2163435 16431659 := bstep (se 1 (by rfl) ⟨12323744, by rfl⟩ : syracuseStep 16431659 = 24647489) B24647489
theorem B10954439 : Blo 2163435 10954439 := bstep (se 1 (by rfl) ⟨8215829, by rfl⟩ : syracuseStep 10954439 = 16431659) B16431659
theorem B7302959 : Blo 2163435 7302959 := bstep (se 1 (by rfl) ⟨5477219, by rfl⟩ : syracuseStep 7302959 = 10954439) B10954439
theorem B4868639 : Blo 2163435 4868639 := bstep (se 1 (by rfl) ⟨3651479, by rfl⟩ : syracuseStep 4868639 = 7302959) B7302959
theorem B3245759 : Blo 2163435 3245759 := bstep (se 1 (by rfl) ⟨2434319, by rfl⟩ : syracuseStep 3245759 = 4868639) B4868639
theorem B2163839 : Blo 2163435 2163839 := bstep (se 1 (by rfl) ⟨1622879, by rfl⟩ : syracuseStep 2163839 = 3245759) B3245759
theorem B3245765 : Blo 2163435 3245765 := bbase (se 4 (by rfl) ⟨304290, by rfl⟩ : syracuseStep 3245765 = 608581) (by norm_num)
theorem B2163843 : Blo 2163435 2163843 := bstep (se 1 (by rfl) ⟨1622882, by rfl⟩ : syracuseStep 2163843 = 3245765) B3245765
theorem B3651493 : Blo 2163435 3651493 := bbase (se 4 (by rfl) ⟨342327, by rfl⟩ : syracuseStep 3651493 = 684655) (by norm_num)
theorem B4868657 : Blo 2163435 4868657 := bstep (se 2 (by rfl) ⟨1825746, by rfl⟩ : syracuseStep 4868657 = 3651493) B3651493
theorem B3245771 : Blo 2163435 3245771 := bstep (se 1 (by rfl) ⟨2434328, by rfl⟩ : syracuseStep 3245771 = 4868657) B4868657
theorem B2163847 : Blo 2163435 2163847 := bstep (se 1 (by rfl) ⟨1622885, by rfl⟩ : syracuseStep 2163847 = 3245771) B3245771
theorem B2434333 : Blo 2163435 2434333 := bbase (se 3 (by rfl) ⟨456437, by rfl⟩ : syracuseStep 2434333 = 912875) (by norm_num)
theorem B3245777 : Blo 2163435 3245777 := bstep (se 2 (by rfl) ⟨1217166, by rfl⟩ : syracuseStep 3245777 = 2434333) B2434333
theorem B2163851 : Blo 2163435 2163851 := bstep (se 1 (by rfl) ⟨1622888, by rfl⟩ : syracuseStep 2163851 = 3245777) B3245777
theorem B7303013 : Blo 2163435 7303013 := bbase (se 4 (by rfl) ⟨684657, by rfl⟩ : syracuseStep 7303013 = 1369315) (by norm_num)
theorem B4868675 : Blo 2163435 4868675 := bstep (se 1 (by rfl) ⟨3651506, by rfl⟩ : syracuseStep 4868675 = 7303013) B7303013
theorem B3245783 : Blo 2163435 3245783 := bstep (se 1 (by rfl) ⟨2434337, by rfl⟩ : syracuseStep 3245783 = 4868675) B4868675
theorem B2163855 : Blo 2163435 2163855 := bstep (se 1 (by rfl) ⟨1622891, by rfl⟩ : syracuseStep 2163855 = 3245783) B3245783
theorem B3245789 : Blo 2163435 3245789 := bbase (se 3 (by rfl) ⟨608585, by rfl⟩ : syracuseStep 3245789 = 1217171) (by norm_num)
theorem B2163859 : Blo 2163435 2163859 := bstep (se 1 (by rfl) ⟨1622894, by rfl⟩ : syracuseStep 2163859 = 3245789) B3245789
theorem B4868693 : Blo 2163435 4868693 := bbase (se 8 (by rfl) ⟨28527, by rfl⟩ : syracuseStep 4868693 = 57055) (by norm_num)
theorem B3245795 : Blo 2163435 3245795 := bstep (se 1 (by rfl) ⟨2434346, by rfl⟩ : syracuseStep 3245795 = 4868693) B4868693
theorem B2163863 : Blo 2163435 2163863 := bstep (se 1 (by rfl) ⟨1622897, by rfl⟩ : syracuseStep 2163863 = 3245795) B3245795
theorem B5199149 : Blo 2163435 5199149 := bbase (se 3 (by rfl) ⟨974840, by rfl⟩ : syracuseStep 5199149 = 1949681) (by norm_num)
theorem B3466099 : Blo 2163435 3466099 := bstep (se 1 (by rfl) ⟨2599574, by rfl⟩ : syracuseStep 3466099 = 5199149) B5199149
theorem B4621465 : Blo 2163435 4621465 := bstep (se 2 (by rfl) ⟨1733049, by rfl⟩ : syracuseStep 4621465 = 3466099) B3466099
theorem B6161953 : Blo 2163435 6161953 := bstep (se 2 (by rfl) ⟨2310732, by rfl⟩ : syracuseStep 6161953 = 4621465) B4621465
theorem B8215937 : Blo 2163435 8215937 := bstep (se 2 (by rfl) ⟨3080976, by rfl⟩ : syracuseStep 8215937 = 6161953) B6161953
theorem B5477291 : Blo 2163435 5477291 := bstep (se 1 (by rfl) ⟨4107968, by rfl⟩ : syracuseStep 5477291 = 8215937) B8215937
theorem B3651527 : Blo 2163435 3651527 := bstep (se 1 (by rfl) ⟨2738645, by rfl⟩ : syracuseStep 3651527 = 5477291) B5477291
theorem B2434351 : Blo 2163435 2434351 := bstep (se 1 (by rfl) ⟨1825763, by rfl⟩ : syracuseStep 2434351 = 3651527) B3651527
theorem B3245801 : Blo 2163435 3245801 := bstep (se 2 (by rfl) ⟨1217175, by rfl⟩ : syracuseStep 3245801 = 2434351) B2434351
theorem B2163867 : Blo 2163435 2163867 := bstep (se 1 (by rfl) ⟨1622900, by rfl⟩ : syracuseStep 2163867 = 3245801) B3245801
theorem B5199157 : Blo 2163435 5199157 := bbase (se 5 (by rfl) ⟨243710, by rfl⟩ : syracuseStep 5199157 = 487421) (by norm_num)
theorem B27728837 : Blo 2163435 27728837 := bstep (se 4 (by rfl) ⟨2599578, by rfl⟩ : syracuseStep 27728837 = 5199157) B5199157
theorem B18485891 : Blo 2163435 18485891 := bstep (se 1 (by rfl) ⟨13864418, by rfl⟩ : syracuseStep 18485891 = 27728837) B27728837
theorem B12323927 : Blo 2163435 12323927 := bstep (se 1 (by rfl) ⟨9242945, by rfl⟩ : syracuseStep 12323927 = 18485891) B18485891
theorem B8215951 : Blo 2163435 8215951 := bstep (se 1 (by rfl) ⟨6161963, by rfl⟩ : syracuseStep 8215951 = 12323927) B12323927
theorem B10954601 : Blo 2163435 10954601 := bstep (se 2 (by rfl) ⟨4107975, by rfl⟩ : syracuseStep 10954601 = 8215951) B8215951
theorem B7303067 : Blo 2163435 7303067 := bstep (se 1 (by rfl) ⟨5477300, by rfl⟩ : syracuseStep 7303067 = 10954601) B10954601
theorem B4868711 : Blo 2163435 4868711 := bstep (se 1 (by rfl) ⟨3651533, by rfl⟩ : syracuseStep 4868711 = 7303067) B7303067
theorem B3245807 : Blo 2163435 3245807 := bstep (se 1 (by rfl) ⟨2434355, by rfl⟩ : syracuseStep 3245807 = 4868711) B4868711
theorem B2163871 : Blo 2163435 2163871 := bstep (se 1 (by rfl) ⟨1622903, by rfl⟩ : syracuseStep 2163871 = 3245807) B3245807
theorem B3245813 : Blo 2163435 3245813 := bbase (se 5 (by rfl) ⟨152147, by rfl⟩ : syracuseStep 3245813 = 304295) (by norm_num)
theorem B2163875 : Blo 2163435 2163875 := bstep (se 1 (by rfl) ⟨1622906, by rfl⟩ : syracuseStep 2163875 = 3245813) B3245813
theorem B9242981 : Blo 2163435 9242981 := bbase (se 4 (by rfl) ⟨866529, by rfl⟩ : syracuseStep 9242981 = 1733059) (by norm_num)
theorem B6161987 : Blo 2163435 6161987 := bstep (se 1 (by rfl) ⟨4621490, by rfl⟩ : syracuseStep 6161987 = 9242981) B9242981
theorem B4107991 : Blo 2163435 4107991 := bstep (se 1 (by rfl) ⟨3080993, by rfl⟩ : syracuseStep 4107991 = 6161987) B6161987
theorem B5477321 : Blo 2163435 5477321 := bstep (se 2 (by rfl) ⟨2053995, by rfl⟩ : syracuseStep 5477321 = 4107991) B4107991
theorem B3651547 : Blo 2163435 3651547 := bstep (se 1 (by rfl) ⟨2738660, by rfl⟩ : syracuseStep 3651547 = 5477321) B5477321
theorem B4868729 : Blo 2163435 4868729 := bstep (se 2 (by rfl) ⟨1825773, by rfl⟩ : syracuseStep 4868729 = 3651547) B3651547
theorem B3245819 : Blo 2163435 3245819 := bstep (se 1 (by rfl) ⟨2434364, by rfl⟩ : syracuseStep 3245819 = 4868729) B4868729
theorem B2163879 : Blo 2163435 2163879 := bstep (se 1 (by rfl) ⟨1622909, by rfl⟩ : syracuseStep 2163879 = 3245819) B3245819
theorem B2434369 : Blo 2163435 2434369 := bbase (se 2 (by rfl) ⟨912888, by rfl⟩ : syracuseStep 2434369 = 1825777) (by norm_num)
theorem B3245825 : Blo 2163435 3245825 := bstep (se 2 (by rfl) ⟨1217184, by rfl⟩ : syracuseStep 3245825 = 2434369) B2434369
theorem B2163883 : Blo 2163435 2163883 := bstep (se 1 (by rfl) ⟨1622912, by rfl⟩ : syracuseStep 2163883 = 3245825) B3245825
theorem B5477341 : Blo 2163435 5477341 := bbase (se 3 (by rfl) ⟨1027001, by rfl⟩ : syracuseStep 5477341 = 2054003) (by norm_num)
theorem B7303121 : Blo 2163435 7303121 := bstep (se 2 (by rfl) ⟨2738670, by rfl⟩ : syracuseStep 7303121 = 5477341) B5477341
theorem B4868747 : Blo 2163435 4868747 := bstep (se 1 (by rfl) ⟨3651560, by rfl⟩ : syracuseStep 4868747 = 7303121) B7303121
theorem B3245831 : Blo 2163435 3245831 := bstep (se 1 (by rfl) ⟨2434373, by rfl⟩ : syracuseStep 3245831 = 4868747) B4868747
theorem B2163887 : Blo 2163435 2163887 := bstep (se 1 (by rfl) ⟨1622915, by rfl⟩ : syracuseStep 2163887 = 3245831) B3245831
theorem B3245837 : Blo 2163435 3245837 := bbase (se 3 (by rfl) ⟨608594, by rfl⟩ : syracuseStep 3245837 = 1217189) (by norm_num)
theorem B2163891 : Blo 2163435 2163891 := bstep (se 1 (by rfl) ⟨1622918, by rfl⟩ : syracuseStep 2163891 = 3245837) B3245837
theorem B4868765 : Blo 2163435 4868765 := bbase (se 3 (by rfl) ⟨912893, by rfl⟩ : syracuseStep 4868765 = 1825787) (by norm_num)
theorem B3245843 : Blo 2163435 3245843 := bstep (se 1 (by rfl) ⟨2434382, by rfl⟩ : syracuseStep 3245843 = 4868765) B4868765
theorem B2163895 : Blo 2163435 2163895 := bstep (se 1 (by rfl) ⟨1622921, by rfl⟩ : syracuseStep 2163895 = 3245843) B3245843
theorem B3651581 : Blo 2163435 3651581 := bbase (se 3 (by rfl) ⟨684671, by rfl⟩ : syracuseStep 3651581 = 1369343) (by norm_num)
theorem B2434387 : Blo 2163435 2434387 := bstep (se 1 (by rfl) ⟨1825790, by rfl⟩ : syracuseStep 2434387 = 3651581) B3651581
theorem B3245849 : Blo 2163435 3245849 := bstep (se 2 (by rfl) ⟨1217193, by rfl⟩ : syracuseStep 3245849 = 2434387) B2434387
theorem B2163899 : Blo 2163435 2163899 := bstep (se 1 (by rfl) ⟨1622924, by rfl⟩ : syracuseStep 2163899 = 3245849) B3245849
theorem B4621541 : Blo 2163435 4621541 := bbase (se 4 (by rfl) ⟨433269, by rfl⟩ : syracuseStep 4621541 = 866539) (by norm_num)
theorem B12324109 : Blo 2163435 12324109 := bstep (se 3 (by rfl) ⟨2310770, by rfl⟩ : syracuseStep 12324109 = 4621541) B4621541
theorem B16432145 : Blo 2163435 16432145 := bstep (se 2 (by rfl) ⟨6162054, by rfl⟩ : syracuseStep 16432145 = 12324109) B12324109
theorem B10954763 : Blo 2163435 10954763 := bstep (se 1 (by rfl) ⟨8216072, by rfl⟩ : syracuseStep 10954763 = 16432145) B16432145
theorem B7303175 : Blo 2163435 7303175 := bstep (se 1 (by rfl) ⟨5477381, by rfl⟩ : syracuseStep 7303175 = 10954763) B10954763
theorem B4868783 : Blo 2163435 4868783 := bstep (se 1 (by rfl) ⟨3651587, by rfl⟩ : syracuseStep 4868783 = 7303175) B7303175
theorem B3245855 : Blo 2163435 3245855 := bstep (se 1 (by rfl) ⟨2434391, by rfl⟩ : syracuseStep 3245855 = 4868783) B4868783
theorem B2163903 : Blo 2163435 2163903 := bstep (se 1 (by rfl) ⟨1622927, by rfl⟩ : syracuseStep 2163903 = 3245855) B3245855
theorem B3245861 : Blo 2163435 3245861 := bbase (se 4 (by rfl) ⟨304299, by rfl⟩ : syracuseStep 3245861 = 608599) (by norm_num)
theorem B2163907 : Blo 2163435 2163907 := bstep (se 1 (by rfl) ⟨1622930, by rfl⟩ : syracuseStep 2163907 = 3245861) B3245861
theorem B2738701 : Blo 2163435 2738701 := bbase (se 3 (by rfl) ⟨513506, by rfl⟩ : syracuseStep 2738701 = 1027013) (by norm_num)
theorem B3651601 : Blo 2163435 3651601 := bstep (se 2 (by rfl) ⟨1369350, by rfl⟩ : syracuseStep 3651601 = 2738701) B2738701
theorem B4868801 : Blo 2163435 4868801 := bstep (se 2 (by rfl) ⟨1825800, by rfl⟩ : syracuseStep 4868801 = 3651601) B3651601
theorem B3245867 : Blo 2163435 3245867 := bstep (se 1 (by rfl) ⟨2434400, by rfl⟩ : syracuseStep 3245867 = 4868801) B4868801
theorem B2163911 : Blo 2163435 2163911 := bstep (se 1 (by rfl) ⟨1622933, by rfl⟩ : syracuseStep 2163911 = 3245867) B3245867
theorem B2434405 : Blo 2163435 2434405 := bbase (se 4 (by rfl) ⟨228225, by rfl⟩ : syracuseStep 2434405 = 456451) (by norm_num)
theorem B3245873 : Blo 2163435 3245873 := bstep (se 2 (by rfl) ⟨1217202, by rfl⟩ : syracuseStep 3245873 = 2434405) B2434405
theorem B2163915 : Blo 2163435 2163915 := bstep (se 1 (by rfl) ⟨1622936, by rfl⟩ : syracuseStep 2163915 = 3245873) B3245873
theorem B6162101 : Blo 2163435 6162101 := bbase (se 5 (by rfl) ⟨288848, by rfl⟩ : syracuseStep 6162101 = 577697) (by norm_num)
theorem B4108067 : Blo 2163435 4108067 := bstep (se 1 (by rfl) ⟨3081050, by rfl⟩ : syracuseStep 4108067 = 6162101) B6162101
theorem B2738711 : Blo 2163435 2738711 := bstep (se 1 (by rfl) ⟨2054033, by rfl⟩ : syracuseStep 2738711 = 4108067) B4108067
theorem B7303229 : Blo 2163435 7303229 := bstep (se 3 (by rfl) ⟨1369355, by rfl⟩ : syracuseStep 7303229 = 2738711) B2738711
theorem B4868819 : Blo 2163435 4868819 := bstep (se 1 (by rfl) ⟨3651614, by rfl⟩ : syracuseStep 4868819 = 7303229) B7303229
theorem B3245879 : Blo 2163435 3245879 := bstep (se 1 (by rfl) ⟨2434409, by rfl⟩ : syracuseStep 3245879 = 4868819) B4868819
theorem B2163919 : Blo 2163435 2163919 := bstep (se 1 (by rfl) ⟨1622939, by rfl⟩ : syracuseStep 2163919 = 3245879) B3245879
theorem B3245885 : Blo 2163435 3245885 := bbase (se 3 (by rfl) ⟨608603, by rfl⟩ : syracuseStep 3245885 = 1217207) (by norm_num)
theorem B2163923 : Blo 2163435 2163923 := bstep (se 1 (by rfl) ⟨1622942, by rfl⟩ : syracuseStep 2163923 = 3245885) B3245885
theorem B4868837 : Blo 2163435 4868837 := bbase (se 4 (by rfl) ⟨456453, by rfl⟩ : syracuseStep 4868837 = 912907) (by norm_num)
theorem B3245891 : Blo 2163435 3245891 := bstep (se 1 (by rfl) ⟨2434418, by rfl⟩ : syracuseStep 3245891 = 4868837) B4868837
theorem B2163927 : Blo 2163435 2163927 := bstep (se 1 (by rfl) ⟨1622945, by rfl⟩ : syracuseStep 2163927 = 3245891) B3245891
theorem B5477453 : Blo 2163435 5477453 := bbase (se 3 (by rfl) ⟨1027022, by rfl⟩ : syracuseStep 5477453 = 2054045) (by norm_num)
theorem B3651635 : Blo 2163435 3651635 := bstep (se 1 (by rfl) ⟨2738726, by rfl⟩ : syracuseStep 3651635 = 5477453) B5477453
theorem B2434423 : Blo 2163435 2434423 := bstep (se 1 (by rfl) ⟨1825817, by rfl⟩ : syracuseStep 2434423 = 3651635) B3651635
theorem B3245897 : Blo 2163435 3245897 := bstep (se 2 (by rfl) ⟨1217211, by rfl⟩ : syracuseStep 3245897 = 2434423) B2434423
theorem B2163931 : Blo 2163435 2163931 := bstep (se 1 (by rfl) ⟨1622948, by rfl⟩ : syracuseStep 2163931 = 3245897) B3245897
theorem B2310805 : Blo 2163435 2310805 := bbase (se 6 (by rfl) ⟨54159, by rfl⟩ : syracuseStep 2310805 = 108319) (by norm_num)
theorem B3081073 : Blo 2163435 3081073 := bstep (se 2 (by rfl) ⟨1155402, by rfl⟩ : syracuseStep 3081073 = 2310805) B2310805
theorem B4108097 : Blo 2163435 4108097 := bstep (se 2 (by rfl) ⟨1540536, by rfl⟩ : syracuseStep 4108097 = 3081073) B3081073
theorem B10954925 : Blo 2163435 10954925 := bstep (se 3 (by rfl) ⟨2054048, by rfl⟩ : syracuseStep 10954925 = 4108097) B4108097
theorem B7303283 : Blo 2163435 7303283 := bstep (se 1 (by rfl) ⟨5477462, by rfl⟩ : syracuseStep 7303283 = 10954925) B10954925
theorem B4868855 : Blo 2163435 4868855 := bstep (se 1 (by rfl) ⟨3651641, by rfl⟩ : syracuseStep 4868855 = 7303283) B7303283
theorem B3245903 : Blo 2163435 3245903 := bstep (se 1 (by rfl) ⟨2434427, by rfl⟩ : syracuseStep 3245903 = 4868855) B4868855
theorem B2163935 : Blo 2163435 2163935 := bstep (se 1 (by rfl) ⟨1622951, by rfl⟩ : syracuseStep 2163935 = 3245903) B3245903
theorem B3245909 : Blo 2163435 3245909 := bbase (se 9 (by rfl) ⟨9509, by rfl⟩ : syracuseStep 3245909 = 19019) (by norm_num)
theorem B2163939 : Blo 2163435 2163939 := bstep (se 1 (by rfl) ⟨1622954, by rfl⟩ : syracuseStep 2163939 = 3245909) B3245909
theorem B7798997 : Blo 2163435 7798997 := bbase (se 7 (by rfl) ⟨91394, by rfl⟩ : syracuseStep 7798997 = 182789) (by norm_num)
theorem B5199331 : Blo 2163435 5199331 := bstep (se 1 (by rfl) ⟨3899498, by rfl⟩ : syracuseStep 5199331 = 7798997) B7798997
theorem B6932441 : Blo 2163435 6932441 := bstep (se 2 (by rfl) ⟨2599665, by rfl⟩ : syracuseStep 6932441 = 5199331) B5199331
theorem B4621627 : Blo 2163435 4621627 := bstep (se 1 (by rfl) ⟨3466220, by rfl⟩ : syracuseStep 4621627 = 6932441) B6932441
theorem B6162169 : Blo 2163435 6162169 := bstep (se 2 (by rfl) ⟨2310813, by rfl⟩ : syracuseStep 6162169 = 4621627) B4621627
theorem B8216225 : Blo 2163435 8216225 := bstep (se 2 (by rfl) ⟨3081084, by rfl⟩ : syracuseStep 8216225 = 6162169) B6162169
theorem B5477483 : Blo 2163435 5477483 := bstep (se 1 (by rfl) ⟨4108112, by rfl⟩ : syracuseStep 5477483 = 8216225) B8216225
theorem B3651655 : Blo 2163435 3651655 := bstep (se 1 (by rfl) ⟨2738741, by rfl⟩ : syracuseStep 3651655 = 5477483) B5477483
theorem B4868873 : Blo 2163435 4868873 := bstep (se 2 (by rfl) ⟨1825827, by rfl⟩ : syracuseStep 4868873 = 3651655) B3651655
theorem B3245915 : Blo 2163435 3245915 := bstep (se 1 (by rfl) ⟨2434436, by rfl⟩ : syracuseStep 3245915 = 4868873) B4868873
theorem B2163943 : Blo 2163435 2163943 := bstep (se 1 (by rfl) ⟨1622957, by rfl⟩ : syracuseStep 2163943 = 3245915) B3245915
theorem B2434441 : Blo 2163435 2434441 := bbase (se 2 (by rfl) ⟨912915, by rfl⟩ : syracuseStep 2434441 = 1825831) (by norm_num)
theorem B3245921 : Blo 2163435 3245921 := bstep (se 2 (by rfl) ⟨1217220, by rfl⟩ : syracuseStep 3245921 = 2434441) B2434441
theorem B2163947 : Blo 2163435 2163947 := bstep (se 1 (by rfl) ⟨1622960, by rfl⟩ : syracuseStep 2163947 = 3245921) B3245921
theorem B17787221 : Blo 2163435 17787221 := bbase (se 10 (by rfl) ⟨26055, by rfl⟩ : syracuseStep 17787221 = 52111) (by norm_num)
theorem B11858147 : Blo 2163435 11858147 := bstep (se 1 (by rfl) ⟨8893610, by rfl⟩ : syracuseStep 11858147 = 17787221) B17787221
theorem B7905431 : Blo 2163435 7905431 := bstep (se 1 (by rfl) ⟨5929073, by rfl⟩ : syracuseStep 7905431 = 11858147) B11858147
theorem B5270287 : Blo 2163435 5270287 := bstep (se 1 (by rfl) ⟨3952715, by rfl⟩ : syracuseStep 5270287 = 7905431) B7905431
theorem B7027049 : Blo 2163435 7027049 := bstep (se 2 (by rfl) ⟨2635143, by rfl⟩ : syracuseStep 7027049 = 5270287) B5270287
theorem B4684699 : Blo 2163435 4684699 := bstep (se 1 (by rfl) ⟨3513524, by rfl⟩ : syracuseStep 4684699 = 7027049) B7027049
theorem B6246265 : Blo 2163435 6246265 := bstep (se 2 (by rfl) ⟨2342349, by rfl⟩ : syracuseStep 6246265 = 4684699) B4684699
theorem B8328353 : Blo 2163435 8328353 := bstep (se 2 (by rfl) ⟨3123132, by rfl⟩ : syracuseStep 8328353 = 6246265) B6246265
theorem B22208941 : Blo 2163435 22208941 := bstep (se 3 (by rfl) ⟨4164176, by rfl⟩ : syracuseStep 22208941 = 8328353) B8328353
theorem B29611921 : Blo 2163435 29611921 := bstep (se 2 (by rfl) ⟨11104470, by rfl⟩ : syracuseStep 29611921 = 22208941) B22208941
theorem B39482561 : Blo 2163435 39482561 := bstep (se 2 (by rfl) ⟨14805960, by rfl⟩ : syracuseStep 39482561 = 29611921) B29611921
theorem B26321707 : Blo 2163435 26321707 := bstep (se 1 (by rfl) ⟨19741280, by rfl⟩ : syracuseStep 26321707 = 39482561) B39482561
theorem B35095609 : Blo 2163435 35095609 := bstep (se 2 (by rfl) ⟨13160853, by rfl⟩ : syracuseStep 35095609 = 26321707) B26321707
theorem B46794145 : Blo 2163435 46794145 := bstep (se 2 (by rfl) ⟨17547804, by rfl⟩ : syracuseStep 46794145 = 35095609) B35095609
theorem B62392193 : Blo 2163435 62392193 := bstep (se 2 (by rfl) ⟨23397072, by rfl⟩ : syracuseStep 62392193 = 46794145) B46794145
theorem B41594795 : Blo 2163435 41594795 := bstep (se 1 (by rfl) ⟨31196096, by rfl⟩ : syracuseStep 41594795 = 62392193) B62392193
theorem B27729863 : Blo 2163435 27729863 := bstep (se 1 (by rfl) ⟨20797397, by rfl⟩ : syracuseStep 27729863 = 41594795) B41594795
theorem B18486575 : Blo 2163435 18486575 := bstep (se 1 (by rfl) ⟨13864931, by rfl⟩ : syracuseStep 18486575 = 27729863) B27729863
theorem B12324383 : Blo 2163435 12324383 := bstep (se 1 (by rfl) ⟨9243287, by rfl⟩ : syracuseStep 12324383 = 18486575) B18486575
theorem B8216255 : Blo 2163435 8216255 := bstep (se 1 (by rfl) ⟨6162191, by rfl⟩ : syracuseStep 8216255 = 12324383) B12324383
theorem B5477503 : Blo 2163435 5477503 := bstep (se 1 (by rfl) ⟨4108127, by rfl⟩ : syracuseStep 5477503 = 8216255) B8216255
theorem B7303337 : Blo 2163435 7303337 := bstep (se 2 (by rfl) ⟨2738751, by rfl⟩ : syracuseStep 7303337 = 5477503) B5477503
theorem B4868891 : Blo 2163435 4868891 := bstep (se 1 (by rfl) ⟨3651668, by rfl⟩ : syracuseStep 4868891 = 7303337) B7303337
theorem B3245927 : Blo 2163435 3245927 := bstep (se 1 (by rfl) ⟨2434445, by rfl⟩ : syracuseStep 3245927 = 4868891) B4868891
theorem B2163951 : Blo 2163435 2163951 := bstep (se 1 (by rfl) ⟨1622963, by rfl⟩ : syracuseStep 2163951 = 3245927) B3245927
theorem B3245933 : Blo 2163435 3245933 := bbase (se 3 (by rfl) ⟨608612, by rfl⟩ : syracuseStep 3245933 = 1217225) (by norm_num)
theorem B2163955 : Blo 2163435 2163955 := bstep (se 1 (by rfl) ⟨1622966, by rfl⟩ : syracuseStep 2163955 = 3245933) B3245933
theorem B4868909 : Blo 2163435 4868909 := bbase (se 3 (by rfl) ⟨912920, by rfl⟩ : syracuseStep 4868909 = 1825841) (by norm_num)
theorem B3245939 : Blo 2163435 3245939 := bstep (se 1 (by rfl) ⟨2434454, by rfl⟩ : syracuseStep 3245939 = 4868909) B4868909
theorem B2163959 : Blo 2163435 2163959 := bstep (se 1 (by rfl) ⟨1622969, by rfl⟩ : syracuseStep 2163959 = 3245939) B3245939
theorem B3466253 : Blo 2163435 3466253 := bbase (se 3 (by rfl) ⟨649922, by rfl⟩ : syracuseStep 3466253 = 1299845) (by norm_num)
theorem B9243341 : Blo 2163435 9243341 := bstep (se 3 (by rfl) ⟨1733126, by rfl⟩ : syracuseStep 9243341 = 3466253) B3466253
theorem B6162227 : Blo 2163435 6162227 := bstep (se 1 (by rfl) ⟨4621670, by rfl⟩ : syracuseStep 6162227 = 9243341) B9243341
theorem B4108151 : Blo 2163435 4108151 := bstep (se 1 (by rfl) ⟨3081113, by rfl⟩ : syracuseStep 4108151 = 6162227) B6162227
theorem B2738767 : Blo 2163435 2738767 := bstep (se 1 (by rfl) ⟨2054075, by rfl⟩ : syracuseStep 2738767 = 4108151) B4108151
theorem B3651689 : Blo 2163435 3651689 := bstep (se 2 (by rfl) ⟨1369383, by rfl⟩ : syracuseStep 3651689 = 2738767) B2738767
theorem B2434459 : Blo 2163435 2434459 := bstep (se 1 (by rfl) ⟨1825844, by rfl⟩ : syracuseStep 2434459 = 3651689) B3651689
theorem B3245945 : Blo 2163435 3245945 := bstep (se 2 (by rfl) ⟨1217229, by rfl⟩ : syracuseStep 3245945 = 2434459) B2434459
theorem B2163963 : Blo 2163435 2163963 := bstep (se 1 (by rfl) ⟨1622972, by rfl⟩ : syracuseStep 2163963 = 3245945) B3245945
theorem B3473509 : Blo 2163435 3473509 := bbase (se 4 (by rfl) ⟨325641, by rfl⟩ : syracuseStep 3473509 = 651283) (by norm_num)
theorem B4631345 : Blo 2163435 4631345 := bstep (se 2 (by rfl) ⟨1736754, by rfl⟩ : syracuseStep 4631345 = 3473509) B3473509
theorem B3087563 : Blo 2163435 3087563 := bstep (se 1 (by rfl) ⟨2315672, by rfl⟩ : syracuseStep 3087563 = 4631345) B4631345
theorem B8233501 : Blo 2163435 8233501 := bstep (se 3 (by rfl) ⟨1543781, by rfl⟩ : syracuseStep 8233501 = 3087563) B3087563
theorem B10978001 : Blo 2163435 10978001 := bstep (se 2 (by rfl) ⟨4116750, by rfl⟩ : syracuseStep 10978001 = 8233501) B8233501
theorem B7318667 : Blo 2163435 7318667 := bstep (se 1 (by rfl) ⟨5489000, by rfl⟩ : syracuseStep 7318667 = 10978001) B10978001
theorem B4879111 : Blo 2163435 4879111 := bstep (se 1 (by rfl) ⟨3659333, by rfl⟩ : syracuseStep 4879111 = 7318667) B7318667
theorem B6505481 : Blo 2163435 6505481 := bstep (se 2 (by rfl) ⟨2439555, by rfl⟩ : syracuseStep 6505481 = 4879111) B4879111
theorem B4336987 : Blo 2163435 4336987 := bstep (se 1 (by rfl) ⟨3252740, by rfl⟩ : syracuseStep 4336987 = 6505481) B6505481
theorem B5782649 : Blo 2163435 5782649 := bstep (se 2 (by rfl) ⟨2168493, by rfl⟩ : syracuseStep 5782649 = 4336987) B4336987
theorem B15420397 : Blo 2163435 15420397 := bstep (se 3 (by rfl) ⟨2891324, by rfl⟩ : syracuseStep 15420397 = 5782649) B5782649
theorem B20560529 : Blo 2163435 20560529 := bstep (se 2 (by rfl) ⟨7710198, by rfl⟩ : syracuseStep 20560529 = 15420397) B15420397
theorem B13707019 : Blo 2163435 13707019 := bstep (se 1 (by rfl) ⟨10280264, by rfl⟩ : syracuseStep 13707019 = 20560529) B20560529
theorem B18276025 : Blo 2163435 18276025 := bstep (se 2 (by rfl) ⟨6853509, by rfl⟩ : syracuseStep 18276025 = 13707019) B13707019
theorem B24368033 : Blo 2163435 24368033 := bstep (se 2 (by rfl) ⟨9138012, by rfl⟩ : syracuseStep 24368033 = 18276025) B18276025
theorem B16245355 : Blo 2163435 16245355 := bstep (se 1 (by rfl) ⟨12184016, by rfl⟩ : syracuseStep 16245355 = 24368033) B24368033
theorem B21660473 : Blo 2163435 21660473 := bstep (se 2 (by rfl) ⟨8122677, by rfl⟩ : syracuseStep 21660473 = 16245355) B16245355
theorem B14440315 : Blo 2163435 14440315 := bstep (se 1 (by rfl) ⟨10830236, by rfl⟩ : syracuseStep 14440315 = 21660473) B21660473
theorem B19253753 : Blo 2163435 19253753 := bstep (se 2 (by rfl) ⟨7220157, by rfl⟩ : syracuseStep 19253753 = 14440315) B14440315
theorem B12835835 : Blo 2163435 12835835 := bstep (se 1 (by rfl) ⟨9626876, by rfl⟩ : syracuseStep 12835835 = 19253753) B19253753
theorem B8557223 : Blo 2163435 8557223 := bstep (se 1 (by rfl) ⟨6417917, by rfl⟩ : syracuseStep 8557223 = 12835835) B12835835
theorem B22819261 : Blo 2163435 22819261 := bstep (se 3 (by rfl) ⟨4278611, by rfl⟩ : syracuseStep 22819261 = 8557223) B8557223
theorem B30425681 : Blo 2163435 30425681 := bstep (se 2 (by rfl) ⟨11409630, by rfl⟩ : syracuseStep 30425681 = 22819261) B22819261
theorem B20283787 : Blo 2163435 20283787 := bstep (se 1 (by rfl) ⟨15212840, by rfl⟩ : syracuseStep 20283787 = 30425681) B30425681
theorem B108180197 : Blo 2163435 108180197 := bstep (se 4 (by rfl) ⟨10141893, by rfl⟩ : syracuseStep 108180197 = 20283787) B20283787
theorem B72120131 : Blo 2163435 72120131 := bstep (se 1 (by rfl) ⟨54090098, by rfl⟩ : syracuseStep 72120131 = 108180197) B108180197
theorem B48080087 : Blo 2163435 48080087 := bstep (se 1 (by rfl) ⟨36060065, by rfl⟩ : syracuseStep 48080087 = 72120131) B72120131
theorem B32053391 : Blo 2163435 32053391 := bstep (se 1 (by rfl) ⟨24040043, by rfl⟩ : syracuseStep 32053391 = 48080087) B48080087
theorem B21368927 : Blo 2163435 21368927 := bstep (se 1 (by rfl) ⟨16026695, by rfl⟩ : syracuseStep 21368927 = 32053391) B32053391
theorem B14245951 : Blo 2163435 14245951 := bstep (se 1 (by rfl) ⟨10684463, by rfl⟩ : syracuseStep 14245951 = 21368927) B21368927
theorem B18994601 : Blo 2163435 18994601 := bstep (se 2 (by rfl) ⟨7122975, by rfl⟩ : syracuseStep 18994601 = 14245951) B14245951
theorem B12663067 : Blo 2163435 12663067 := bstep (se 1 (by rfl) ⟨9497300, by rfl⟩ : syracuseStep 12663067 = 18994601) B18994601
theorem B16884089 : Blo 2163435 16884089 := bstep (se 2 (by rfl) ⟨6331533, by rfl⟩ : syracuseStep 16884089 = 12663067) B12663067
theorem B11256059 : Blo 2163435 11256059 := bstep (se 1 (by rfl) ⟨8442044, by rfl⟩ : syracuseStep 11256059 = 16884089) B16884089
theorem B7504039 : Blo 2163435 7504039 := bstep (se 1 (by rfl) ⟨5628029, by rfl⟩ : syracuseStep 7504039 = 11256059) B11256059
theorem B10005385 : Blo 2163435 10005385 := bstep (se 2 (by rfl) ⟨3752019, by rfl⟩ : syracuseStep 10005385 = 7504039) B7504039
theorem B13340513 : Blo 2163435 13340513 := bstep (se 2 (by rfl) ⟨5002692, by rfl⟩ : syracuseStep 13340513 = 10005385) B10005385
theorem B8893675 : Blo 2163435 8893675 := bstep (se 1 (by rfl) ⟨6670256, by rfl⟩ : syracuseStep 8893675 = 13340513) B13340513
theorem B11858233 : Blo 2163435 11858233 := bstep (se 2 (by rfl) ⟨4446837, by rfl⟩ : syracuseStep 11858233 = 8893675) B8893675
theorem B15810977 : Blo 2163435 15810977 := bstep (se 2 (by rfl) ⟨5929116, by rfl⟩ : syracuseStep 15810977 = 11858233) B11858233
theorem B42162605 : Blo 2163435 42162605 := bstep (se 3 (by rfl) ⟨7905488, by rfl⟩ : syracuseStep 42162605 = 15810977) B15810977
theorem B28108403 : Blo 2163435 28108403 := bstep (se 1 (by rfl) ⟨21081302, by rfl⟩ : syracuseStep 28108403 = 42162605) B42162605
theorem B18738935 : Blo 2163435 18738935 := bstep (se 1 (by rfl) ⟨14054201, by rfl⟩ : syracuseStep 18738935 = 28108403) B28108403
theorem B12492623 : Blo 2163435 12492623 := bstep (se 1 (by rfl) ⟨9369467, by rfl⟩ : syracuseStep 12492623 = 18738935) B18738935
theorem B8328415 : Blo 2163435 8328415 := bstep (se 1 (by rfl) ⟨6246311, by rfl⟩ : syracuseStep 8328415 = 12492623) B12492623
theorem B11104553 : Blo 2163435 11104553 := bstep (se 2 (by rfl) ⟨4164207, by rfl⟩ : syracuseStep 11104553 = 8328415) B8328415
theorem B29612141 : Blo 2163435 29612141 := bstep (se 3 (by rfl) ⟨5552276, by rfl⟩ : syracuseStep 29612141 = 11104553) B11104553
theorem B19741427 : Blo 2163435 19741427 := bstep (se 1 (by rfl) ⟨14806070, by rfl⟩ : syracuseStep 19741427 = 29612141) B29612141
theorem B13160951 : Blo 2163435 13160951 := bstep (se 1 (by rfl) ⟨9870713, by rfl⟩ : syracuseStep 13160951 = 19741427) B19741427
theorem B8773967 : Blo 2163435 8773967 := bstep (se 1 (by rfl) ⟨6580475, by rfl⟩ : syracuseStep 8773967 = 13160951) B13160951
theorem B23397245 : Blo 2163435 23397245 := bstep (se 3 (by rfl) ⟨4386983, by rfl⟩ : syracuseStep 23397245 = 8773967) B8773967
theorem B15598163 : Blo 2163435 15598163 := bstep (se 1 (by rfl) ⟨11698622, by rfl⟩ : syracuseStep 15598163 = 23397245) B23397245
theorem B10398775 : Blo 2163435 10398775 := bstep (se 1 (by rfl) ⟨7799081, by rfl⟩ : syracuseStep 10398775 = 15598163) B15598163
theorem B13865033 : Blo 2163435 13865033 := bstep (se 2 (by rfl) ⟨5199387, by rfl⟩ : syracuseStep 13865033 = 10398775) B10398775
theorem B36973421 : Blo 2163435 36973421 := bstep (se 3 (by rfl) ⟨6932516, by rfl⟩ : syracuseStep 36973421 = 13865033) B13865033
theorem B24648947 : Blo 2163435 24648947 := bstep (se 1 (by rfl) ⟨18486710, by rfl⟩ : syracuseStep 24648947 = 36973421) B36973421
theorem B16432631 : Blo 2163435 16432631 := bstep (se 1 (by rfl) ⟨12324473, by rfl⟩ : syracuseStep 16432631 = 24648947) B24648947
theorem B10955087 : Blo 2163435 10955087 := bstep (se 1 (by rfl) ⟨8216315, by rfl⟩ : syracuseStep 10955087 = 16432631) B16432631
theorem B7303391 : Blo 2163435 7303391 := bstep (se 1 (by rfl) ⟨5477543, by rfl⟩ : syracuseStep 7303391 = 10955087) B10955087
theorem B4868927 : Blo 2163435 4868927 := bstep (se 1 (by rfl) ⟨3651695, by rfl⟩ : syracuseStep 4868927 = 7303391) B7303391
theorem B3245951 : Blo 2163435 3245951 := bstep (se 1 (by rfl) ⟨2434463, by rfl⟩ : syracuseStep 3245951 = 4868927) B4868927
theorem B2163967 : Blo 2163435 2163967 := bstep (se 1 (by rfl) ⟨1622975, by rfl⟩ : syracuseStep 2163967 = 3245951) B3245951
theorem B3245957 : Blo 2163435 3245957 := bbase (se 4 (by rfl) ⟨304308, by rfl⟩ : syracuseStep 3245957 = 608617) (by norm_num)
theorem B2163971 : Blo 2163435 2163971 := bstep (se 1 (by rfl) ⟨1622978, by rfl⟩ : syracuseStep 2163971 = 3245957) B3245957
theorem B3651709 : Blo 2163435 3651709 := bbase (se 3 (by rfl) ⟨684695, by rfl⟩ : syracuseStep 3651709 = 1369391) (by norm_num)
theorem B4868945 : Blo 2163435 4868945 := bstep (se 2 (by rfl) ⟨1825854, by rfl⟩ : syracuseStep 4868945 = 3651709) B3651709
theorem B3245963 : Blo 2163435 3245963 := bstep (se 1 (by rfl) ⟨2434472, by rfl⟩ : syracuseStep 3245963 = 4868945) B4868945
theorem B2163975 : Blo 2163435 2163975 := bstep (se 1 (by rfl) ⟨1622981, by rfl⟩ : syracuseStep 2163975 = 3245963) B3245963
theorem B2434477 : Blo 2163435 2434477 := bbase (se 3 (by rfl) ⟨456464, by rfl⟩ : syracuseStep 2434477 = 912929) (by norm_num)
theorem B3245969 : Blo 2163435 3245969 := bstep (se 2 (by rfl) ⟨1217238, by rfl⟩ : syracuseStep 3245969 = 2434477) B2434477
theorem B2163979 : Blo 2163435 2163979 := bstep (se 1 (by rfl) ⟨1622984, by rfl⟩ : syracuseStep 2163979 = 3245969) B3245969
theorem B7303445 : Blo 2163435 7303445 := bbase (se 6 (by rfl) ⟨171174, by rfl⟩ : syracuseStep 7303445 = 342349) (by norm_num)
theorem B4868963 : Blo 2163435 4868963 := bstep (se 1 (by rfl) ⟨3651722, by rfl⟩ : syracuseStep 4868963 = 7303445) B7303445
theorem B3245975 : Blo 2163435 3245975 := bstep (se 1 (by rfl) ⟨2434481, by rfl⟩ : syracuseStep 3245975 = 4868963) B4868963
theorem B2163983 : Blo 2163435 2163983 := bstep (se 1 (by rfl) ⟨1622987, by rfl⟩ : syracuseStep 2163983 = 3245975) B3245975
theorem B3245981 : Blo 2163435 3245981 := bbase (se 3 (by rfl) ⟨608621, by rfl⟩ : syracuseStep 3245981 = 1217243) (by norm_num)
theorem B2163987 : Blo 2163435 2163987 := bstep (se 1 (by rfl) ⟨1622990, by rfl⟩ : syracuseStep 2163987 = 3245981) B3245981
theorem B4868981 : Blo 2163435 4868981 := bbase (se 5 (by rfl) ⟨228233, by rfl⟩ : syracuseStep 4868981 = 456467) (by norm_num)
theorem B3245987 : Blo 2163435 3245987 := bstep (se 1 (by rfl) ⟨2434490, by rfl⟩ : syracuseStep 3245987 = 4868981) B4868981
theorem B2163991 : Blo 2163435 2163991 := bstep (se 1 (by rfl) ⟨1622993, by rfl⟩ : syracuseStep 2163991 = 3245987) B3245987
theorem B9369589 : Blo 2163435 9369589 := bbase (se 5 (by rfl) ⟨439199, by rfl⟩ : syracuseStep 9369589 = 878399) (by norm_num)
theorem B12492785 : Blo 2163435 12492785 := bstep (se 2 (by rfl) ⟨4684794, by rfl⟩ : syracuseStep 12492785 = 9369589) B9369589
theorem B33314093 : Blo 2163435 33314093 := bstep (se 3 (by rfl) ⟨6246392, by rfl⟩ : syracuseStep 33314093 = 12492785) B12492785
theorem B22209395 : Blo 2163435 22209395 := bstep (se 1 (by rfl) ⟨16657046, by rfl⟩ : syracuseStep 22209395 = 33314093) B33314093
theorem B236900213 : Blo 2163435 236900213 := bstep (se 5 (by rfl) ⟨11104697, by rfl⟩ : syracuseStep 236900213 = 22209395) B22209395
theorem B157933475 : Blo 2163435 157933475 := bstep (se 1 (by rfl) ⟨118450106, by rfl⟩ : syracuseStep 157933475 = 236900213) B236900213
theorem B105288983 : Blo 2163435 105288983 := bstep (se 1 (by rfl) ⟨78966737, by rfl⟩ : syracuseStep 105288983 = 157933475) B157933475
theorem B70192655 : Blo 2163435 70192655 := bstep (se 1 (by rfl) ⟨52644491, by rfl⟩ : syracuseStep 70192655 = 105288983) B105288983
theorem B46795103 : Blo 2163435 46795103 := bstep (se 1 (by rfl) ⟨35096327, by rfl⟩ : syracuseStep 46795103 = 70192655) B70192655
theorem B31196735 : Blo 2163435 31196735 := bstep (se 1 (by rfl) ⟨23397551, by rfl⟩ : syracuseStep 31196735 = 46795103) B46795103
theorem B20797823 : Blo 2163435 20797823 := bstep (se 1 (by rfl) ⟨15598367, by rfl⟩ : syracuseStep 20797823 = 31196735) B31196735
theorem B13865215 : Blo 2163435 13865215 := bstep (se 1 (by rfl) ⟨10398911, by rfl⟩ : syracuseStep 13865215 = 20797823) B20797823
theorem B18486953 : Blo 2163435 18486953 := bstep (se 2 (by rfl) ⟨6932607, by rfl⟩ : syracuseStep 18486953 = 13865215) B13865215
theorem B12324635 : Blo 2163435 12324635 := bstep (se 1 (by rfl) ⟨9243476, by rfl⟩ : syracuseStep 12324635 = 18486953) B18486953
theorem B8216423 : Blo 2163435 8216423 := bstep (se 1 (by rfl) ⟨6162317, by rfl⟩ : syracuseStep 8216423 = 12324635) B12324635
theorem B5477615 : Blo 2163435 5477615 := bstep (se 1 (by rfl) ⟨4108211, by rfl⟩ : syracuseStep 5477615 = 8216423) B8216423
theorem B3651743 : Blo 2163435 3651743 := bstep (se 1 (by rfl) ⟨2738807, by rfl⟩ : syracuseStep 3651743 = 5477615) B5477615
theorem B2434495 : Blo 2163435 2434495 := bstep (se 1 (by rfl) ⟨1825871, by rfl⟩ : syracuseStep 2434495 = 3651743) B3651743
theorem B3245993 : Blo 2163435 3245993 := bstep (se 2 (by rfl) ⟨1217247, by rfl⟩ : syracuseStep 3245993 = 2434495) B2434495
theorem B2163995 : Blo 2163435 2163995 := bstep (se 1 (by rfl) ⟨1622996, by rfl⟩ : syracuseStep 2163995 = 3245993) B3245993
theorem B8216437 : Blo 2163435 8216437 := bbase (se 5 (by rfl) ⟨385145, by rfl⟩ : syracuseStep 8216437 = 770291) (by norm_num)
theorem B10955249 : Blo 2163435 10955249 := bstep (se 2 (by rfl) ⟨4108218, by rfl⟩ : syracuseStep 10955249 = 8216437) B8216437
theorem B7303499 : Blo 2163435 7303499 := bstep (se 1 (by rfl) ⟨5477624, by rfl⟩ : syracuseStep 7303499 = 10955249) B10955249
theorem B4868999 : Blo 2163435 4868999 := bstep (se 1 (by rfl) ⟨3651749, by rfl⟩ : syracuseStep 4868999 = 7303499) B7303499
theorem B3245999 : Blo 2163435 3245999 := bstep (se 1 (by rfl) ⟨2434499, by rfl⟩ : syracuseStep 3245999 = 4868999) B4868999
theorem B2163999 : Blo 2163435 2163999 := bstep (se 1 (by rfl) ⟨1622999, by rfl⟩ : syracuseStep 2163999 = 3245999) B3245999
theorem B3246005 : Blo 2163435 3246005 := bbase (se 5 (by rfl) ⟨152156, by rfl⟩ : syracuseStep 3246005 = 304313) (by norm_num)
theorem B2164003 : Blo 2163435 2164003 := bstep (se 1 (by rfl) ⟨1623002, by rfl⟩ : syracuseStep 2164003 = 3246005) B3246005
theorem B5477645 : Blo 2163435 5477645 := bbase (se 3 (by rfl) ⟨1027058, by rfl⟩ : syracuseStep 5477645 = 2054117) (by norm_num)
theorem B3651763 : Blo 2163435 3651763 := bstep (se 1 (by rfl) ⟨2738822, by rfl⟩ : syracuseStep 3651763 = 5477645) B5477645
theorem B4869017 : Blo 2163435 4869017 := bstep (se 2 (by rfl) ⟨1825881, by rfl⟩ : syracuseStep 4869017 = 3651763) B3651763
theorem B3246011 : Blo 2163435 3246011 := bstep (se 1 (by rfl) ⟨2434508, by rfl⟩ : syracuseStep 3246011 = 4869017) B4869017
theorem B2164007 : Blo 2163435 2164007 := bstep (se 1 (by rfl) ⟨1623005, by rfl⟩ : syracuseStep 2164007 = 3246011) B3246011
theorem B2434513 : Blo 2163435 2434513 := bbase (se 2 (by rfl) ⟨912942, by rfl⟩ : syracuseStep 2434513 = 1825885) (by norm_num)
theorem B3246017 : Blo 2163435 3246017 := bstep (se 2 (by rfl) ⟨1217256, by rfl⟩ : syracuseStep 3246017 = 2434513) B2434513
theorem B2164011 : Blo 2163435 2164011 := bstep (se 1 (by rfl) ⟨1623008, by rfl⟩ : syracuseStep 2164011 = 3246017) B3246017
theorem B4621781 : Blo 2163435 4621781 := bbase (se 7 (by rfl) ⟨54161, by rfl⟩ : syracuseStep 4621781 = 108323) (by norm_num)
theorem B3081187 : Blo 2163435 3081187 := bstep (se 1 (by rfl) ⟨2310890, by rfl⟩ : syracuseStep 3081187 = 4621781) B4621781
theorem B4108249 : Blo 2163435 4108249 := bstep (se 2 (by rfl) ⟨1540593, by rfl⟩ : syracuseStep 4108249 = 3081187) B3081187
theorem B5477665 : Blo 2163435 5477665 := bstep (se 2 (by rfl) ⟨2054124, by rfl⟩ : syracuseStep 5477665 = 4108249) B4108249
theorem B7303553 : Blo 2163435 7303553 := bstep (se 2 (by rfl) ⟨2738832, by rfl⟩ : syracuseStep 7303553 = 5477665) B5477665
theorem B4869035 : Blo 2163435 4869035 := bstep (se 1 (by rfl) ⟨3651776, by rfl⟩ : syracuseStep 4869035 = 7303553) B7303553
theorem B3246023 : Blo 2163435 3246023 := bstep (se 1 (by rfl) ⟨2434517, by rfl⟩ : syracuseStep 3246023 = 4869035) B4869035
theorem B2164015 : Blo 2163435 2164015 := bstep (se 1 (by rfl) ⟨1623011, by rfl⟩ : syracuseStep 2164015 = 3246023) B3246023
theorem B3246029 : Blo 2163435 3246029 := bbase (se 3 (by rfl) ⟨608630, by rfl⟩ : syracuseStep 3246029 = 1217261) (by norm_num)
theorem B2164019 : Blo 2163435 2164019 := bstep (se 1 (by rfl) ⟨1623014, by rfl⟩ : syracuseStep 2164019 = 3246029) B3246029
theorem B4869053 : Blo 2163435 4869053 := bbase (se 3 (by rfl) ⟨912947, by rfl⟩ : syracuseStep 4869053 = 1825895) (by norm_num)
theorem B3246035 : Blo 2163435 3246035 := bstep (se 1 (by rfl) ⟨2434526, by rfl⟩ : syracuseStep 3246035 = 4869053) B4869053
theorem B2164023 : Blo 2163435 2164023 := bstep (se 1 (by rfl) ⟨1623017, by rfl⟩ : syracuseStep 2164023 = 3246035) B3246035
theorem B3651797 : Blo 2163435 3651797 := bbase (se 7 (by rfl) ⟨42794, by rfl⟩ : syracuseStep 3651797 = 85589) (by norm_num)
theorem B2434531 : Blo 2163435 2434531 := bstep (se 1 (by rfl) ⟨1825898, by rfl⟩ : syracuseStep 2434531 = 3651797) B3651797
theorem B3246041 : Blo 2163435 3246041 := bstep (se 2 (by rfl) ⟨1217265, by rfl⟩ : syracuseStep 3246041 = 2434531) B2434531
theorem B2164027 : Blo 2163435 2164027 := bstep (se 1 (by rfl) ⟨1623020, by rfl⟩ : syracuseStep 2164027 = 3246041) B3246041
theorem B3701629 : Blo 2163435 3701629 := bbase (se 3 (by rfl) ⟨694055, by rfl⟩ : syracuseStep 3701629 = 1388111) (by norm_num)
theorem B4935505 : Blo 2163435 4935505 := bstep (se 2 (by rfl) ⟨1850814, by rfl⟩ : syracuseStep 4935505 = 3701629) B3701629
theorem B6580673 : Blo 2163435 6580673 := bstep (se 2 (by rfl) ⟨2467752, by rfl⟩ : syracuseStep 6580673 = 4935505) B4935505
theorem B4387115 : Blo 2163435 4387115 := bstep (se 1 (by rfl) ⟨3290336, by rfl⟩ : syracuseStep 4387115 = 6580673) B6580673
theorem B2924743 : Blo 2163435 2924743 := bstep (se 1 (by rfl) ⟨2193557, by rfl⟩ : syracuseStep 2924743 = 4387115) B4387115
theorem B3899657 : Blo 2163435 3899657 := bstep (se 2 (by rfl) ⟨1462371, by rfl⟩ : syracuseStep 3899657 = 2924743) B2924743
theorem B2599771 : Blo 2163435 2599771 := bstep (se 1 (by rfl) ⟨1949828, by rfl⟩ : syracuseStep 2599771 = 3899657) B3899657
theorem B3466361 : Blo 2163435 3466361 := bstep (se 2 (by rfl) ⟨1299885, by rfl⟩ : syracuseStep 3466361 = 2599771) B2599771
theorem B9243629 : Blo 2163435 9243629 := bstep (se 3 (by rfl) ⟨1733180, by rfl⟩ : syracuseStep 9243629 = 3466361) B3466361
theorem B6162419 : Blo 2163435 6162419 := bstep (se 1 (by rfl) ⟨4621814, by rfl⟩ : syracuseStep 6162419 = 9243629) B9243629
theorem B16433117 : Blo 2163435 16433117 := bstep (se 3 (by rfl) ⟨3081209, by rfl⟩ : syracuseStep 16433117 = 6162419) B6162419
theorem B10955411 : Blo 2163435 10955411 := bstep (se 1 (by rfl) ⟨8216558, by rfl⟩ : syracuseStep 10955411 = 16433117) B16433117
theorem B7303607 : Blo 2163435 7303607 := bstep (se 1 (by rfl) ⟨5477705, by rfl⟩ : syracuseStep 7303607 = 10955411) B10955411
theorem B4869071 : Blo 2163435 4869071 := bstep (se 1 (by rfl) ⟨3651803, by rfl⟩ : syracuseStep 4869071 = 7303607) B7303607
theorem B3246047 : Blo 2163435 3246047 := bstep (se 1 (by rfl) ⟨2434535, by rfl⟩ : syracuseStep 3246047 = 4869071) B4869071
theorem B2164031 : Blo 2163435 2164031 := bstep (se 1 (by rfl) ⟨1623023, by rfl⟩ : syracuseStep 2164031 = 3246047) B3246047
theorem B3246053 : Blo 2163435 3246053 := bbase (se 4 (by rfl) ⟨304317, by rfl⟩ : syracuseStep 3246053 = 608635) (by norm_num)
theorem B2164035 : Blo 2163435 2164035 := bstep (se 1 (by rfl) ⟨1623026, by rfl⟩ : syracuseStep 2164035 = 3246053) B3246053
theorem B2599781 : Blo 2163435 2599781 := bbase (se 4 (by rfl) ⟨243729, by rfl⟩ : syracuseStep 2599781 = 487459) (by norm_num)
theorem B6932749 : Blo 2163435 6932749 := bstep (se 3 (by rfl) ⟨1299890, by rfl⟩ : syracuseStep 6932749 = 2599781) B2599781
theorem B9243665 : Blo 2163435 9243665 := bstep (se 2 (by rfl) ⟨3466374, by rfl⟩ : syracuseStep 9243665 = 6932749) B6932749
theorem B6162443 : Blo 2163435 6162443 := bstep (se 1 (by rfl) ⟨4621832, by rfl⟩ : syracuseStep 6162443 = 9243665) B9243665
theorem B4108295 : Blo 2163435 4108295 := bstep (se 1 (by rfl) ⟨3081221, by rfl⟩ : syracuseStep 4108295 = 6162443) B6162443
theorem B2738863 : Blo 2163435 2738863 := bstep (se 1 (by rfl) ⟨2054147, by rfl⟩ : syracuseStep 2738863 = 4108295) B4108295
theorem B3651817 : Blo 2163435 3651817 := bstep (se 2 (by rfl) ⟨1369431, by rfl⟩ : syracuseStep 3651817 = 2738863) B2738863
theorem B4869089 : Blo 2163435 4869089 := bstep (se 2 (by rfl) ⟨1825908, by rfl⟩ : syracuseStep 4869089 = 3651817) B3651817
theorem B3246059 : Blo 2163435 3246059 := bstep (se 1 (by rfl) ⟨2434544, by rfl⟩ : syracuseStep 3246059 = 4869089) B4869089
theorem B2164039 : Blo 2163435 2164039 := bstep (se 1 (by rfl) ⟨1623029, by rfl⟩ : syracuseStep 2164039 = 3246059) B3246059
theorem B2434549 : Blo 2163435 2434549 := bbase (se 5 (by rfl) ⟨114119, by rfl⟩ : syracuseStep 2434549 = 228239) (by norm_num)
theorem B3246065 : Blo 2163435 3246065 := bstep (se 2 (by rfl) ⟨1217274, by rfl⟩ : syracuseStep 3246065 = 2434549) B2434549
theorem B2164043 : Blo 2163435 2164043 := bstep (se 1 (by rfl) ⟨1623032, by rfl⟩ : syracuseStep 2164043 = 3246065) B3246065
theorem B2738873 : Blo 2163435 2738873 := bbase (se 2 (by rfl) ⟨1027077, by rfl⟩ : syracuseStep 2738873 = 2054155) (by norm_num)
theorem B7303661 : Blo 2163435 7303661 := bstep (se 3 (by rfl) ⟨1369436, by rfl⟩ : syracuseStep 7303661 = 2738873) B2738873
theorem B4869107 : Blo 2163435 4869107 := bstep (se 1 (by rfl) ⟨3651830, by rfl⟩ : syracuseStep 4869107 = 7303661) B7303661
theorem B3246071 : Blo 2163435 3246071 := bstep (se 1 (by rfl) ⟨2434553, by rfl⟩ : syracuseStep 3246071 = 4869107) B4869107
theorem B2164047 : Blo 2163435 2164047 := bstep (se 1 (by rfl) ⟨1623035, by rfl⟩ : syracuseStep 2164047 = 3246071) B3246071
theorem B3246077 : Blo 2163435 3246077 := bbase (se 3 (by rfl) ⟨608639, by rfl⟩ : syracuseStep 3246077 = 1217279) (by norm_num)
theorem B2164051 : Blo 2163435 2164051 := bstep (se 1 (by rfl) ⟨1623038, by rfl⟩ : syracuseStep 2164051 = 3246077) B3246077
theorem B4869125 : Blo 2163435 4869125 := bbase (se 4 (by rfl) ⟨456480, by rfl⟩ : syracuseStep 4869125 = 912961) (by norm_num)
theorem B3246083 : Blo 2163435 3246083 := bstep (se 1 (by rfl) ⟨2434562, by rfl⟩ : syracuseStep 3246083 = 4869125) B4869125
theorem B2164055 : Blo 2163435 2164055 := bstep (se 1 (by rfl) ⟨1623041, by rfl⟩ : syracuseStep 2164055 = 3246083) B3246083
theorem B4108333 : Blo 2163435 4108333 := bbase (se 3 (by rfl) ⟨770312, by rfl⟩ : syracuseStep 4108333 = 1540625) (by norm_num)
theorem B5477777 : Blo 2163435 5477777 := bstep (se 2 (by rfl) ⟨2054166, by rfl⟩ : syracuseStep 5477777 = 4108333) B4108333
theorem B3651851 : Blo 2163435 3651851 := bstep (se 1 (by rfl) ⟨2738888, by rfl⟩ : syracuseStep 3651851 = 5477777) B5477777
theorem B2434567 : Blo 2163435 2434567 := bstep (se 1 (by rfl) ⟨1825925, by rfl⟩ : syracuseStep 2434567 = 3651851) B3651851
theorem B3246089 : Blo 2163435 3246089 := bstep (se 2 (by rfl) ⟨1217283, by rfl⟩ : syracuseStep 3246089 = 2434567) B2434567
theorem B2164059 : Blo 2163435 2164059 := bstep (se 1 (by rfl) ⟨1623044, by rfl⟩ : syracuseStep 2164059 = 3246089) B3246089
theorem B10955573 : Blo 2163435 10955573 := bbase (se 5 (by rfl) ⟨513542, by rfl⟩ : syracuseStep 10955573 = 1027085) (by norm_num)
theorem B7303715 : Blo 2163435 7303715 := bstep (se 1 (by rfl) ⟨5477786, by rfl⟩ : syracuseStep 7303715 = 10955573) B10955573
theorem B4869143 : Blo 2163435 4869143 := bstep (se 1 (by rfl) ⟨3651857, by rfl⟩ : syracuseStep 4869143 = 7303715) B7303715
theorem B3246095 : Blo 2163435 3246095 := bstep (se 1 (by rfl) ⟨2434571, by rfl⟩ : syracuseStep 3246095 = 4869143) B4869143
theorem B2164063 : Blo 2163435 2164063 := bstep (se 1 (by rfl) ⟨1623047, by rfl⟩ : syracuseStep 2164063 = 3246095) B3246095
theorem B3246101 : Blo 2163435 3246101 := bbase (se 6 (by rfl) ⟨76080, by rfl⟩ : syracuseStep 3246101 = 152161) (by norm_num)
theorem B2164067 : Blo 2163435 2164067 := bstep (se 1 (by rfl) ⟨1623050, by rfl⟩ : syracuseStep 2164067 = 3246101) B3246101
theorem B2924797 : Blo 2163435 2924797 := bbase (se 3 (by rfl) ⟨548399, by rfl⟩ : syracuseStep 2924797 = 1096799) (by norm_num)
theorem B3899729 : Blo 2163435 3899729 := bstep (se 2 (by rfl) ⟨1462398, by rfl⟩ : syracuseStep 3899729 = 2924797) B2924797
theorem B2599819 : Blo 2163435 2599819 := bstep (se 1 (by rfl) ⟨1949864, by rfl⟩ : syracuseStep 2599819 = 3899729) B3899729
theorem B13865701 : Blo 2163435 13865701 := bstep (se 4 (by rfl) ⟨1299909, by rfl⟩ : syracuseStep 13865701 = 2599819) B2599819
theorem B18487601 : Blo 2163435 18487601 := bstep (se 2 (by rfl) ⟨6932850, by rfl⟩ : syracuseStep 18487601 = 13865701) B13865701
theorem B12325067 : Blo 2163435 12325067 := bstep (se 1 (by rfl) ⟨9243800, by rfl⟩ : syracuseStep 12325067 = 18487601) B18487601
theorem B8216711 : Blo 2163435 8216711 := bstep (se 1 (by rfl) ⟨6162533, by rfl⟩ : syracuseStep 8216711 = 12325067) B12325067
theorem B5477807 : Blo 2163435 5477807 := bstep (se 1 (by rfl) ⟨4108355, by rfl⟩ : syracuseStep 5477807 = 8216711) B8216711
theorem B3651871 : Blo 2163435 3651871 := bstep (se 1 (by rfl) ⟨2738903, by rfl⟩ : syracuseStep 3651871 = 5477807) B5477807
theorem B4869161 : Blo 2163435 4869161 := bstep (se 2 (by rfl) ⟨1825935, by rfl⟩ : syracuseStep 4869161 = 3651871) B3651871
theorem B3246107 : Blo 2163435 3246107 := bstep (se 1 (by rfl) ⟨2434580, by rfl⟩ : syracuseStep 3246107 = 4869161) B4869161
theorem B2164071 : Blo 2163435 2164071 := bstep (se 1 (by rfl) ⟨1623053, by rfl⟩ : syracuseStep 2164071 = 3246107) B3246107
theorem B2434585 : Blo 2163435 2434585 := bbase (se 2 (by rfl) ⟨912969, by rfl⟩ : syracuseStep 2434585 = 1825939) (by norm_num)
theorem B3246113 : Blo 2163435 3246113 := bstep (se 2 (by rfl) ⟨1217292, by rfl⟩ : syracuseStep 3246113 = 2434585) B2434585
theorem B2164075 : Blo 2163435 2164075 := bstep (se 1 (by rfl) ⟨1623056, by rfl⟩ : syracuseStep 2164075 = 3246113) B3246113
theorem B8216741 : Blo 2163435 8216741 := bbase (se 4 (by rfl) ⟨770319, by rfl⟩ : syracuseStep 8216741 = 1540639) (by norm_num)
theorem B5477827 : Blo 2163435 5477827 := bstep (se 1 (by rfl) ⟨4108370, by rfl⟩ : syracuseStep 5477827 = 8216741) B8216741
theorem B7303769 : Blo 2163435 7303769 := bstep (se 2 (by rfl) ⟨2738913, by rfl⟩ : syracuseStep 7303769 = 5477827) B5477827
theorem B4869179 : Blo 2163435 4869179 := bstep (se 1 (by rfl) ⟨3651884, by rfl⟩ : syracuseStep 4869179 = 7303769) B7303769
theorem B3246119 : Blo 2163435 3246119 := bstep (se 1 (by rfl) ⟨2434589, by rfl⟩ : syracuseStep 3246119 = 4869179) B4869179
theorem B2164079 : Blo 2163435 2164079 := bstep (se 1 (by rfl) ⟨1623059, by rfl⟩ : syracuseStep 2164079 = 3246119) B3246119
theorem B3246125 : Blo 2163435 3246125 := bbase (se 3 (by rfl) ⟨608648, by rfl⟩ : syracuseStep 3246125 = 1217297) (by norm_num)
theorem B2164083 : Blo 2163435 2164083 := bstep (se 1 (by rfl) ⟨1623062, by rfl⟩ : syracuseStep 2164083 = 3246125) B3246125
theorem B4869197 : Blo 2163435 4869197 := bbase (se 3 (by rfl) ⟨912974, by rfl⟩ : syracuseStep 4869197 = 1825949) (by norm_num)
theorem B3246131 : Blo 2163435 3246131 := bstep (se 1 (by rfl) ⟨2434598, by rfl⟩ : syracuseStep 3246131 = 4869197) B4869197
theorem B2164087 : Blo 2163435 2164087 := bstep (se 1 (by rfl) ⟨1623065, by rfl⟩ : syracuseStep 2164087 = 3246131) B3246131
theorem B2738929 : Blo 2163435 2738929 := bbase (se 2 (by rfl) ⟨1027098, by rfl⟩ : syracuseStep 2738929 = 2054197) (by norm_num)
theorem B3651905 : Blo 2163435 3651905 := bstep (se 2 (by rfl) ⟨1369464, by rfl⟩ : syracuseStep 3651905 = 2738929) B2738929
theorem B2434603 : Blo 2163435 2434603 := bstep (se 1 (by rfl) ⟨1825952, by rfl⟩ : syracuseStep 2434603 = 3651905) B3651905
theorem B3246137 : Blo 2163435 3246137 := bstep (se 2 (by rfl) ⟨1217301, by rfl⟩ : syracuseStep 3246137 = 2434603) B2434603
theorem B2164091 : Blo 2163435 2164091 := bstep (se 1 (by rfl) ⟨1623068, by rfl⟩ : syracuseStep 2164091 = 3246137) B3246137
theorem B37480085 : Blo 2163435 37480085 := bbase (se 6 (by rfl) ⟨878439, by rfl⟩ : syracuseStep 37480085 = 1756879) (by norm_num)
theorem B24986723 : Blo 2163435 24986723 := bstep (se 1 (by rfl) ⟨18740042, by rfl⟩ : syracuseStep 24986723 = 37480085) B37480085
theorem B66631261 : Blo 2163435 66631261 := bstep (se 3 (by rfl) ⟨12493361, by rfl⟩ : syracuseStep 66631261 = 24986723) B24986723
theorem B88841681 : Blo 2163435 88841681 := bstep (se 2 (by rfl) ⟨33315630, by rfl⟩ : syracuseStep 88841681 = 66631261) B66631261
theorem B59227787 : Blo 2163435 59227787 := bstep (se 1 (by rfl) ⟨44420840, by rfl⟩ : syracuseStep 59227787 = 88841681) B88841681
theorem B39485191 : Blo 2163435 39485191 := bstep (se 1 (by rfl) ⟨29613893, by rfl⟩ : syracuseStep 39485191 = 59227787) B59227787
theorem B52646921 : Blo 2163435 52646921 := bstep (se 2 (by rfl) ⟨19742595, by rfl⟩ : syracuseStep 52646921 = 39485191) B39485191
theorem B35097947 : Blo 2163435 35097947 := bstep (se 1 (by rfl) ⟨26323460, by rfl⟩ : syracuseStep 35097947 = 52646921) B52646921
theorem B23398631 : Blo 2163435 23398631 := bstep (se 1 (by rfl) ⟨17548973, by rfl⟩ : syracuseStep 23398631 = 35097947) B35097947
theorem B15599087 : Blo 2163435 15599087 := bstep (se 1 (by rfl) ⟨11699315, by rfl⟩ : syracuseStep 15599087 = 23398631) B23398631
theorem B10399391 : Blo 2163435 10399391 := bstep (se 1 (by rfl) ⟨7799543, by rfl⟩ : syracuseStep 10399391 = 15599087) B15599087
theorem B6932927 : Blo 2163435 6932927 := bstep (se 1 (by rfl) ⟨5199695, by rfl⟩ : syracuseStep 6932927 = 10399391) B10399391
theorem B4621951 : Blo 2163435 4621951 := bstep (se 1 (by rfl) ⟨3466463, by rfl⟩ : syracuseStep 4621951 = 6932927) B6932927
theorem B24650405 : Blo 2163435 24650405 := bstep (se 4 (by rfl) ⟨2310975, by rfl⟩ : syracuseStep 24650405 = 4621951) B4621951
theorem B16433603 : Blo 2163435 16433603 := bstep (se 1 (by rfl) ⟨12325202, by rfl⟩ : syracuseStep 16433603 = 24650405) B24650405
theorem B10955735 : Blo 2163435 10955735 := bstep (se 1 (by rfl) ⟨8216801, by rfl⟩ : syracuseStep 10955735 = 16433603) B16433603
theorem B7303823 : Blo 2163435 7303823 := bstep (se 1 (by rfl) ⟨5477867, by rfl⟩ : syracuseStep 7303823 = 10955735) B10955735
theorem B4869215 : Blo 2163435 4869215 := bstep (se 1 (by rfl) ⟨3651911, by rfl⟩ : syracuseStep 4869215 = 7303823) B7303823
theorem B3246143 : Blo 2163435 3246143 := bstep (se 1 (by rfl) ⟨2434607, by rfl⟩ : syracuseStep 3246143 = 4869215) B4869215
theorem B2164095 : Blo 2163435 2164095 := bstep (se 1 (by rfl) ⟨1623071, by rfl⟩ : syracuseStep 2164095 = 3246143) B3246143
theorem B3246149 : Blo 2163435 3246149 := bbase (se 4 (by rfl) ⟨304326, by rfl⟩ : syracuseStep 3246149 = 608653) (by norm_num)
theorem B2164099 : Blo 2163435 2164099 := bstep (se 1 (by rfl) ⟨1623074, by rfl⟩ : syracuseStep 2164099 = 3246149) B3246149
theorem B3651925 : Blo 2163435 3651925 := bbase (se 10 (by rfl) ⟨5349, by rfl⟩ : syracuseStep 3651925 = 10699) (by norm_num)
theorem B4869233 : Blo 2163435 4869233 := bstep (se 2 (by rfl) ⟨1825962, by rfl⟩ : syracuseStep 4869233 = 3651925) B3651925
theorem B3246155 : Blo 2163435 3246155 := bstep (se 1 (by rfl) ⟨2434616, by rfl⟩ : syracuseStep 3246155 = 4869233) B4869233
theorem B2164103 : Blo 2163435 2164103 := bstep (se 1 (by rfl) ⟨1623077, by rfl⟩ : syracuseStep 2164103 = 3246155) B3246155
theorem B2434621 : Blo 2163435 2434621 := bbase (se 3 (by rfl) ⟨456491, by rfl⟩ : syracuseStep 2434621 = 912983) (by norm_num)
theorem B3246161 : Blo 2163435 3246161 := bstep (se 2 (by rfl) ⟨1217310, by rfl⟩ : syracuseStep 3246161 = 2434621) B2434621
theorem B2164107 : Blo 2163435 2164107 := bstep (se 1 (by rfl) ⟨1623080, by rfl⟩ : syracuseStep 2164107 = 3246161) B3246161
theorem B7303877 : Blo 2163435 7303877 := bbase (se 4 (by rfl) ⟨684738, by rfl⟩ : syracuseStep 7303877 = 1369477) (by norm_num)
theorem B4869251 : Blo 2163435 4869251 := bstep (se 1 (by rfl) ⟨3651938, by rfl⟩ : syracuseStep 4869251 = 7303877) B7303877
theorem B3246167 : Blo 2163435 3246167 := bstep (se 1 (by rfl) ⟨2434625, by rfl⟩ : syracuseStep 3246167 = 4869251) B4869251
theorem B2164111 : Blo 2163435 2164111 := bstep (se 1 (by rfl) ⟨1623083, by rfl⟩ : syracuseStep 2164111 = 3246167) B3246167
theorem B3246173 : Blo 2163435 3246173 := bbase (se 3 (by rfl) ⟨608657, by rfl⟩ : syracuseStep 3246173 = 1217315) (by norm_num)
theorem B2164115 : Blo 2163435 2164115 := bstep (se 1 (by rfl) ⟨1623086, by rfl⟩ : syracuseStep 2164115 = 3246173) B3246173
theorem B4869269 : Blo 2163435 4869269 := bbase (se 6 (by rfl) ⟨114123, by rfl⟩ : syracuseStep 4869269 = 228247) (by norm_num)
theorem B3246179 : Blo 2163435 3246179 := bstep (se 1 (by rfl) ⟨2434634, by rfl⟩ : syracuseStep 3246179 = 4869269) B4869269
theorem B2164119 : Blo 2163435 2164119 := bstep (se 1 (by rfl) ⟨1623089, by rfl⟩ : syracuseStep 2164119 = 3246179) B3246179
theorem B3081341 : Blo 2163435 3081341 := bbase (se 3 (by rfl) ⟨577751, by rfl⟩ : syracuseStep 3081341 = 1155503) (by norm_num)
theorem B8216909 : Blo 2163435 8216909 := bstep (se 3 (by rfl) ⟨1540670, by rfl⟩ : syracuseStep 8216909 = 3081341) B3081341
theorem B5477939 : Blo 2163435 5477939 := bstep (se 1 (by rfl) ⟨4108454, by rfl⟩ : syracuseStep 5477939 = 8216909) B8216909
theorem B3651959 : Blo 2163435 3651959 := bstep (se 1 (by rfl) ⟨2738969, by rfl⟩ : syracuseStep 3651959 = 5477939) B5477939
theorem B2434639 : Blo 2163435 2434639 := bstep (se 1 (by rfl) ⟨1825979, by rfl⟩ : syracuseStep 2434639 = 3651959) B3651959
theorem B3246185 : Blo 2163435 3246185 := bstep (se 2 (by rfl) ⟨1217319, by rfl⟩ : syracuseStep 3246185 = 2434639) B2434639
theorem B2164123 : Blo 2163435 2164123 := bstep (se 1 (by rfl) ⟨1623092, by rfl⟩ : syracuseStep 2164123 = 3246185) B3246185
theorem B15599317 : Blo 2163435 15599317 := bbase (se 7 (by rfl) ⟨182804, by rfl⟩ : syracuseStep 15599317 = 365609) (by norm_num)
theorem B20799089 : Blo 2163435 20799089 := bstep (se 2 (by rfl) ⟨7799658, by rfl⟩ : syracuseStep 20799089 = 15599317) B15599317
theorem B13866059 : Blo 2163435 13866059 := bstep (se 1 (by rfl) ⟨10399544, by rfl⟩ : syracuseStep 13866059 = 20799089) B20799089
theorem B9244039 : Blo 2163435 9244039 := bstep (se 1 (by rfl) ⟨6933029, by rfl⟩ : syracuseStep 9244039 = 13866059) B13866059
theorem B12325385 : Blo 2163435 12325385 := bstep (se 2 (by rfl) ⟨4622019, by rfl⟩ : syracuseStep 12325385 = 9244039) B9244039
theorem B8216923 : Blo 2163435 8216923 := bstep (se 1 (by rfl) ⟨6162692, by rfl⟩ : syracuseStep 8216923 = 12325385) B12325385
theorem B10955897 : Blo 2163435 10955897 := bstep (se 2 (by rfl) ⟨4108461, by rfl⟩ : syracuseStep 10955897 = 8216923) B8216923
theorem B7303931 : Blo 2163435 7303931 := bstep (se 1 (by rfl) ⟨5477948, by rfl⟩ : syracuseStep 7303931 = 10955897) B10955897
theorem B4869287 : Blo 2163435 4869287 := bstep (se 1 (by rfl) ⟨3651965, by rfl⟩ : syracuseStep 4869287 = 7303931) B7303931
theorem B3246191 : Blo 2163435 3246191 := bstep (se 1 (by rfl) ⟨2434643, by rfl⟩ : syracuseStep 3246191 = 4869287) B4869287
theorem B2164127 : Blo 2163435 2164127 := bstep (se 1 (by rfl) ⟨1623095, by rfl⟩ : syracuseStep 2164127 = 3246191) B3246191
theorem B3246197 : Blo 2163435 3246197 := bbase (se 5 (by rfl) ⟨152165, by rfl⟩ : syracuseStep 3246197 = 304331) (by norm_num)
theorem B2164131 : Blo 2163435 2164131 := bstep (se 1 (by rfl) ⟨1623098, by rfl⟩ : syracuseStep 2164131 = 3246197) B3246197
theorem B4108477 : Blo 2163435 4108477 := bbase (se 3 (by rfl) ⟨770339, by rfl⟩ : syracuseStep 4108477 = 1540679) (by norm_num)
theorem B5477969 : Blo 2163435 5477969 := bstep (se 2 (by rfl) ⟨2054238, by rfl⟩ : syracuseStep 5477969 = 4108477) B4108477
theorem B3651979 : Blo 2163435 3651979 := bstep (se 1 (by rfl) ⟨2738984, by rfl⟩ : syracuseStep 3651979 = 5477969) B5477969
theorem B4869305 : Blo 2163435 4869305 := bstep (se 2 (by rfl) ⟨1825989, by rfl⟩ : syracuseStep 4869305 = 3651979) B3651979
theorem B3246203 : Blo 2163435 3246203 := bstep (se 1 (by rfl) ⟨2434652, by rfl⟩ : syracuseStep 3246203 = 4869305) B4869305
theorem B2164135 : Blo 2163435 2164135 := bstep (se 1 (by rfl) ⟨1623101, by rfl⟩ : syracuseStep 2164135 = 3246203) B3246203
theorem B2434657 : Blo 2163435 2434657 := bbase (se 2 (by rfl) ⟨912996, by rfl⟩ : syracuseStep 2434657 = 1825993) (by norm_num)
theorem B3246209 : Blo 2163435 3246209 := bstep (se 2 (by rfl) ⟨1217328, by rfl⟩ : syracuseStep 3246209 = 2434657) B2434657
theorem B2164139 : Blo 2163435 2164139 := bstep (se 1 (by rfl) ⟨1623104, by rfl⟩ : syracuseStep 2164139 = 3246209) B3246209
theorem B5477989 : Blo 2163435 5477989 := bbase (se 4 (by rfl) ⟨513561, by rfl⟩ : syracuseStep 5477989 = 1027123) (by norm_num)
theorem B7303985 : Blo 2163435 7303985 := bstep (se 2 (by rfl) ⟨2738994, by rfl⟩ : syracuseStep 7303985 = 5477989) B5477989
theorem B4869323 : Blo 2163435 4869323 := bstep (se 1 (by rfl) ⟨3651992, by rfl⟩ : syracuseStep 4869323 = 7303985) B7303985
theorem B3246215 : Blo 2163435 3246215 := bstep (se 1 (by rfl) ⟨2434661, by rfl⟩ : syracuseStep 3246215 = 4869323) B4869323
theorem B2164143 : Blo 2163435 2164143 := bstep (se 1 (by rfl) ⟨1623107, by rfl⟩ : syracuseStep 2164143 = 3246215) B3246215
theorem B3246221 : Blo 2163435 3246221 := bbase (se 3 (by rfl) ⟨608666, by rfl⟩ : syracuseStep 3246221 = 1217333) (by norm_num)
theorem B2164147 : Blo 2163435 2164147 := bstep (se 1 (by rfl) ⟨1623110, by rfl⟩ : syracuseStep 2164147 = 3246221) B3246221
theorem B4869341 : Blo 2163435 4869341 := bbase (se 3 (by rfl) ⟨913001, by rfl⟩ : syracuseStep 4869341 = 1826003) (by norm_num)
theorem B3246227 : Blo 2163435 3246227 := bstep (se 1 (by rfl) ⟨2434670, by rfl⟩ : syracuseStep 3246227 = 4869341) B4869341
theorem B2164151 : Blo 2163435 2164151 := bstep (se 1 (by rfl) ⟨1623113, by rfl⟩ : syracuseStep 2164151 = 3246227) B3246227
theorem B3652013 : Blo 2163435 3652013 := bbase (se 3 (by rfl) ⟨684752, by rfl⟩ : syracuseStep 3652013 = 1369505) (by norm_num)
theorem B2434675 : Blo 2163435 2434675 := bstep (se 1 (by rfl) ⟨1826006, by rfl⟩ : syracuseStep 2434675 = 3652013) B3652013
theorem B3246233 : Blo 2163435 3246233 := bstep (se 2 (by rfl) ⟨1217337, by rfl⟩ : syracuseStep 3246233 = 2434675) B2434675
theorem B2164155 : Blo 2163435 2164155 := bstep (se 1 (by rfl) ⟨1623116, by rfl⟩ : syracuseStep 2164155 = 3246233) B3246233
theorem B4685149 : Blo 2163435 4685149 := bbase (se 3 (by rfl) ⟨878465, by rfl⟩ : syracuseStep 4685149 = 1756931) (by norm_num)
theorem B6246865 : Blo 2163435 6246865 := bstep (se 2 (by rfl) ⟨2342574, by rfl⟩ : syracuseStep 6246865 = 4685149) B4685149
theorem B8329153 : Blo 2163435 8329153 := bstep (se 2 (by rfl) ⟨3123432, by rfl⟩ : syracuseStep 8329153 = 6246865) B6246865
theorem B11105537 : Blo 2163435 11105537 := bstep (se 2 (by rfl) ⟨4164576, by rfl⟩ : syracuseStep 11105537 = 8329153) B8329153
theorem B118459061 : Blo 2163435 118459061 := bstep (se 5 (by rfl) ⟨5552768, by rfl⟩ : syracuseStep 118459061 = 11105537) B11105537
theorem B78972707 : Blo 2163435 78972707 := bstep (se 1 (by rfl) ⟨59229530, by rfl⟩ : syracuseStep 78972707 = 118459061) B118459061
theorem B52648471 : Blo 2163435 52648471 := bstep (se 1 (by rfl) ⟨39486353, by rfl⟩ : syracuseStep 52648471 = 78972707) B78972707
theorem B70197961 : Blo 2163435 70197961 := bstep (se 2 (by rfl) ⟨26324235, by rfl⟩ : syracuseStep 70197961 = 52648471) B52648471
theorem B93597281 : Blo 2163435 93597281 := bstep (se 2 (by rfl) ⟨35098980, by rfl⟩ : syracuseStep 93597281 = 70197961) B70197961
theorem B62398187 : Blo 2163435 62398187 := bstep (se 1 (by rfl) ⟨46798640, by rfl⟩ : syracuseStep 62398187 = 93597281) B93597281
theorem B41598791 : Blo 2163435 41598791 := bstep (se 1 (by rfl) ⟨31199093, by rfl⟩ : syracuseStep 41598791 = 62398187) B62398187
theorem B27732527 : Blo 2163435 27732527 := bstep (se 1 (by rfl) ⟨20799395, by rfl⟩ : syracuseStep 27732527 = 41598791) B41598791
theorem B18488351 : Blo 2163435 18488351 := bstep (se 1 (by rfl) ⟨13866263, by rfl⟩ : syracuseStep 18488351 = 27732527) B27732527
theorem B12325567 : Blo 2163435 12325567 := bstep (se 1 (by rfl) ⟨9244175, by rfl⟩ : syracuseStep 12325567 = 18488351) B18488351
theorem B16434089 : Blo 2163435 16434089 := bstep (se 2 (by rfl) ⟨6162783, by rfl⟩ : syracuseStep 16434089 = 12325567) B12325567
theorem B10956059 : Blo 2163435 10956059 := bstep (se 1 (by rfl) ⟨8217044, by rfl⟩ : syracuseStep 10956059 = 16434089) B16434089
theorem B7304039 : Blo 2163435 7304039 := bstep (se 1 (by rfl) ⟨5478029, by rfl⟩ : syracuseStep 7304039 = 10956059) B10956059
theorem B4869359 : Blo 2163435 4869359 := bstep (se 1 (by rfl) ⟨3652019, by rfl⟩ : syracuseStep 4869359 = 7304039) B7304039
theorem B3246239 : Blo 2163435 3246239 := bstep (se 1 (by rfl) ⟨2434679, by rfl⟩ : syracuseStep 3246239 = 4869359) B4869359
theorem B2164159 : Blo 2163435 2164159 := bstep (se 1 (by rfl) ⟨1623119, by rfl⟩ : syracuseStep 2164159 = 3246239) B3246239
theorem B3246245 : Blo 2163435 3246245 := bbase (se 4 (by rfl) ⟨304335, by rfl⟩ : syracuseStep 3246245 = 608671) (by norm_num)
theorem B2164163 : Blo 2163435 2164163 := bstep (se 1 (by rfl) ⟨1623122, by rfl⟩ : syracuseStep 2164163 = 3246245) B3246245
theorem B2739025 : Blo 2163435 2739025 := bbase (se 2 (by rfl) ⟨1027134, by rfl⟩ : syracuseStep 2739025 = 2054269) (by norm_num)
theorem B3652033 : Blo 2163435 3652033 := bstep (se 2 (by rfl) ⟨1369512, by rfl⟩ : syracuseStep 3652033 = 2739025) B2739025
theorem B4869377 : Blo 2163435 4869377 := bstep (se 2 (by rfl) ⟨1826016, by rfl⟩ : syracuseStep 4869377 = 3652033) B3652033
theorem B3246251 : Blo 2163435 3246251 := bstep (se 1 (by rfl) ⟨2434688, by rfl⟩ : syracuseStep 3246251 = 4869377) B4869377
theorem B2164167 : Blo 2163435 2164167 := bstep (se 1 (by rfl) ⟨1623125, by rfl⟩ : syracuseStep 2164167 = 3246251) B3246251
theorem B2434693 : Blo 2163435 2434693 := bbase (se 4 (by rfl) ⟨228252, by rfl⟩ : syracuseStep 2434693 = 456505) (by norm_num)
theorem B3246257 : Blo 2163435 3246257 := bstep (se 2 (by rfl) ⟨1217346, by rfl⟩ : syracuseStep 3246257 = 2434693) B2434693
theorem B2164171 : Blo 2163435 2164171 := bstep (se 1 (by rfl) ⟨1623128, by rfl⟩ : syracuseStep 2164171 = 3246257) B3246257
theorem B3899917 : Blo 2163435 3899917 := bbase (se 3 (by rfl) ⟨731234, by rfl⟩ : syracuseStep 3899917 = 1462469) (by norm_num)
theorem B5199889 : Blo 2163435 5199889 := bstep (se 2 (by rfl) ⟨1949958, by rfl⟩ : syracuseStep 5199889 = 3899917) B3899917
theorem B6933185 : Blo 2163435 6933185 := bstep (se 2 (by rfl) ⟨2599944, by rfl⟩ : syracuseStep 6933185 = 5199889) B5199889
theorem B4622123 : Blo 2163435 4622123 := bstep (se 1 (by rfl) ⟨3466592, by rfl⟩ : syracuseStep 4622123 = 6933185) B6933185
theorem B3081415 : Blo 2163435 3081415 := bstep (se 1 (by rfl) ⟨2311061, by rfl⟩ : syracuseStep 3081415 = 4622123) B4622123
theorem B4108553 : Blo 2163435 4108553 := bstep (se 2 (by rfl) ⟨1540707, by rfl⟩ : syracuseStep 4108553 = 3081415) B3081415
theorem B2739035 : Blo 2163435 2739035 := bstep (se 1 (by rfl) ⟨2054276, by rfl⟩ : syracuseStep 2739035 = 4108553) B4108553
theorem B7304093 : Blo 2163435 7304093 := bstep (se 3 (by rfl) ⟨1369517, by rfl⟩ : syracuseStep 7304093 = 2739035) B2739035
theorem B4869395 : Blo 2163435 4869395 := bstep (se 1 (by rfl) ⟨3652046, by rfl⟩ : syracuseStep 4869395 = 7304093) B7304093
theorem B3246263 : Blo 2163435 3246263 := bstep (se 1 (by rfl) ⟨2434697, by rfl⟩ : syracuseStep 3246263 = 4869395) B4869395
theorem B2164175 : Blo 2163435 2164175 := bstep (se 1 (by rfl) ⟨1623131, by rfl⟩ : syracuseStep 2164175 = 3246263) B3246263
theorem B3246269 : Blo 2163435 3246269 := bbase (se 3 (by rfl) ⟨608675, by rfl⟩ : syracuseStep 3246269 = 1217351) (by norm_num)
theorem B2164179 : Blo 2163435 2164179 := bstep (se 1 (by rfl) ⟨1623134, by rfl⟩ : syracuseStep 2164179 = 3246269) B3246269
theorem B4869413 : Blo 2163435 4869413 := bbase (se 4 (by rfl) ⟨456507, by rfl⟩ : syracuseStep 4869413 = 913015) (by norm_num)
theorem B3246275 : Blo 2163435 3246275 := bstep (se 1 (by rfl) ⟨2434706, by rfl⟩ : syracuseStep 3246275 = 4869413) B4869413
theorem B2164183 : Blo 2163435 2164183 := bstep (se 1 (by rfl) ⟨1623137, by rfl⟩ : syracuseStep 2164183 = 3246275) B3246275
theorem B5478101 : Blo 2163435 5478101 := bbase (se 7 (by rfl) ⟨64196, by rfl⟩ : syracuseStep 5478101 = 128393) (by norm_num)
theorem B3652067 : Blo 2163435 3652067 := bstep (se 1 (by rfl) ⟨2739050, by rfl⟩ : syracuseStep 3652067 = 5478101) B5478101
theorem B2434711 : Blo 2163435 2434711 := bstep (se 1 (by rfl) ⟨1826033, by rfl⟩ : syracuseStep 2434711 = 3652067) B3652067
theorem B3246281 : Blo 2163435 3246281 := bstep (se 2 (by rfl) ⟨1217355, by rfl⟩ : syracuseStep 3246281 = 2434711) B2434711
theorem B2164187 : Blo 2163435 2164187 := bstep (se 1 (by rfl) ⟨1623140, by rfl⟩ : syracuseStep 2164187 = 3246281) B3246281
theorem B5929733 : Blo 2163435 5929733 := bbase (se 4 (by rfl) ⟨555912, by rfl⟩ : syracuseStep 5929733 = 1111825) (by norm_num)
theorem B15812621 : Blo 2163435 15812621 := bstep (se 3 (by rfl) ⟨2964866, by rfl⟩ : syracuseStep 15812621 = 5929733) B5929733
theorem B10541747 : Blo 2163435 10541747 := bstep (se 1 (by rfl) ⟨7906310, by rfl⟩ : syracuseStep 10541747 = 15812621) B15812621
theorem B7027831 : Blo 2163435 7027831 := bstep (se 1 (by rfl) ⟨5270873, by rfl⟩ : syracuseStep 7027831 = 10541747) B10541747
theorem B9370441 : Blo 2163435 9370441 := bstep (se 2 (by rfl) ⟨3513915, by rfl⟩ : syracuseStep 9370441 = 7027831) B7027831
theorem B12493921 : Blo 2163435 12493921 := bstep (se 2 (by rfl) ⟨4685220, by rfl⟩ : syracuseStep 12493921 = 9370441) B9370441
theorem B16658561 : Blo 2163435 16658561 := bstep (se 2 (by rfl) ⟨6246960, by rfl⟩ : syracuseStep 16658561 = 12493921) B12493921
theorem B11105707 : Blo 2163435 11105707 := bstep (se 1 (by rfl) ⟨8329280, by rfl⟩ : syracuseStep 11105707 = 16658561) B16658561
theorem B14807609 : Blo 2163435 14807609 := bstep (se 2 (by rfl) ⟨5552853, by rfl⟩ : syracuseStep 14807609 = 11105707) B11105707
theorem B9871739 : Blo 2163435 9871739 := bstep (se 1 (by rfl) ⟨7403804, by rfl⟩ : syracuseStep 9871739 = 14807609) B14807609
theorem B6581159 : Blo 2163435 6581159 := bstep (se 1 (by rfl) ⟨4935869, by rfl⟩ : syracuseStep 6581159 = 9871739) B9871739
theorem B4387439 : Blo 2163435 4387439 := bstep (se 1 (by rfl) ⟨3290579, by rfl⟩ : syracuseStep 4387439 = 6581159) B6581159
theorem B2924959 : Blo 2163435 2924959 := bstep (se 1 (by rfl) ⟨2193719, by rfl⟩ : syracuseStep 2924959 = 4387439) B4387439
theorem B3899945 : Blo 2163435 3899945 := bstep (se 2 (by rfl) ⟨1462479, by rfl⟩ : syracuseStep 3899945 = 2924959) B2924959
theorem B10399853 : Blo 2163435 10399853 := bstep (se 3 (by rfl) ⟨1949972, by rfl⟩ : syracuseStep 10399853 = 3899945) B3899945
theorem B6933235 : Blo 2163435 6933235 := bstep (se 1 (by rfl) ⟨5199926, by rfl⟩ : syracuseStep 6933235 = 10399853) B10399853
theorem B9244313 : Blo 2163435 9244313 := bstep (se 2 (by rfl) ⟨3466617, by rfl⟩ : syracuseStep 9244313 = 6933235) B6933235
theorem B6162875 : Blo 2163435 6162875 := bstep (se 1 (by rfl) ⟨4622156, by rfl⟩ : syracuseStep 6162875 = 9244313) B9244313
theorem B4108583 : Blo 2163435 4108583 := bstep (se 1 (by rfl) ⟨3081437, by rfl⟩ : syracuseStep 4108583 = 6162875) B6162875
theorem B10956221 : Blo 2163435 10956221 := bstep (se 3 (by rfl) ⟨2054291, by rfl⟩ : syracuseStep 10956221 = 4108583) B4108583
theorem B7304147 : Blo 2163435 7304147 := bstep (se 1 (by rfl) ⟨5478110, by rfl⟩ : syracuseStep 7304147 = 10956221) B10956221
theorem B4869431 : Blo 2163435 4869431 := bstep (se 1 (by rfl) ⟨3652073, by rfl⟩ : syracuseStep 4869431 = 7304147) B7304147
theorem B3246287 : Blo 2163435 3246287 := bstep (se 1 (by rfl) ⟨2434715, by rfl⟩ : syracuseStep 3246287 = 4869431) B4869431
theorem B2164191 : Blo 2163435 2164191 := bstep (se 1 (by rfl) ⟨1623143, by rfl⟩ : syracuseStep 2164191 = 3246287) B3246287
theorem B3246293 : Blo 2163435 3246293 := bbase (se 7 (by rfl) ⟨38042, by rfl⟩ : syracuseStep 3246293 = 76085) (by norm_num)
theorem B2164195 : Blo 2163435 2164195 := bstep (se 1 (by rfl) ⟨1623146, by rfl⟩ : syracuseStep 2164195 = 3246293) B3246293
theorem B5849941 : Blo 2163435 5849941 := bbase (se 9 (by rfl) ⟨17138, by rfl⟩ : syracuseStep 5849941 = 34277) (by norm_num)
theorem B7799921 : Blo 2163435 7799921 := bstep (se 2 (by rfl) ⟨2924970, by rfl⟩ : syracuseStep 7799921 = 5849941) B5849941
theorem B5199947 : Blo 2163435 5199947 := bstep (se 1 (by rfl) ⟨3899960, by rfl⟩ : syracuseStep 5199947 = 7799921) B7799921
theorem B3466631 : Blo 2163435 3466631 := bstep (se 1 (by rfl) ⟨2599973, by rfl⟩ : syracuseStep 3466631 = 5199947) B5199947
theorem B2311087 : Blo 2163435 2311087 := bstep (se 1 (by rfl) ⟨1733315, by rfl⟩ : syracuseStep 2311087 = 3466631) B3466631
theorem B3081449 : Blo 2163435 3081449 := bstep (se 2 (by rfl) ⟨1155543, by rfl⟩ : syracuseStep 3081449 = 2311087) B2311087
theorem B8217197 : Blo 2163435 8217197 := bstep (se 3 (by rfl) ⟨1540724, by rfl⟩ : syracuseStep 8217197 = 3081449) B3081449
theorem B5478131 : Blo 2163435 5478131 := bstep (se 1 (by rfl) ⟨4108598, by rfl⟩ : syracuseStep 5478131 = 8217197) B8217197
theorem B3652087 : Blo 2163435 3652087 := bstep (se 1 (by rfl) ⟨2739065, by rfl⟩ : syracuseStep 3652087 = 5478131) B5478131
theorem B4869449 : Blo 2163435 4869449 := bstep (se 2 (by rfl) ⟨1826043, by rfl⟩ : syracuseStep 4869449 = 3652087) B3652087
theorem B3246299 : Blo 2163435 3246299 := bstep (se 1 (by rfl) ⟨2434724, by rfl⟩ : syracuseStep 3246299 = 4869449) B4869449
theorem B2164199 : Blo 2163435 2164199 := bstep (se 1 (by rfl) ⟨1623149, by rfl⟩ : syracuseStep 2164199 = 3246299) B3246299
theorem B2434729 : Blo 2163435 2434729 := bbase (se 2 (by rfl) ⟨913023, by rfl⟩ : syracuseStep 2434729 = 1826047) (by norm_num)
theorem B3246305 : Blo 2163435 3246305 := bstep (se 2 (by rfl) ⟨1217364, by rfl⟩ : syracuseStep 3246305 = 2434729) B2434729
theorem B2164203 : Blo 2163435 2164203 := bstep (se 1 (by rfl) ⟨1623152, by rfl⟩ : syracuseStep 2164203 = 3246305) B3246305
theorem B5199965 : Blo 2163435 5199965 := bbase (se 3 (by rfl) ⟨974993, by rfl⟩ : syracuseStep 5199965 = 1949987) (by norm_num)
theorem B3466643 : Blo 2163435 3466643 := bstep (se 1 (by rfl) ⟨2599982, by rfl⟩ : syracuseStep 3466643 = 5199965) B5199965
theorem B9244381 : Blo 2163435 9244381 := bstep (se 3 (by rfl) ⟨1733321, by rfl⟩ : syracuseStep 9244381 = 3466643) B3466643
theorem B12325841 : Blo 2163435 12325841 := bstep (se 2 (by rfl) ⟨4622190, by rfl⟩ : syracuseStep 12325841 = 9244381) B9244381
theorem B8217227 : Blo 2163435 8217227 := bstep (se 1 (by rfl) ⟨6162920, by rfl⟩ : syracuseStep 8217227 = 12325841) B12325841
theorem B5478151 : Blo 2163435 5478151 := bstep (se 1 (by rfl) ⟨4108613, by rfl⟩ : syracuseStep 5478151 = 8217227) B8217227
theorem B7304201 : Blo 2163435 7304201 := bstep (se 2 (by rfl) ⟨2739075, by rfl⟩ : syracuseStep 7304201 = 5478151) B5478151
theorem B4869467 : Blo 2163435 4869467 := bstep (se 1 (by rfl) ⟨3652100, by rfl⟩ : syracuseStep 4869467 = 7304201) B7304201
theorem B3246311 : Blo 2163435 3246311 := bstep (se 1 (by rfl) ⟨2434733, by rfl⟩ : syracuseStep 3246311 = 4869467) B4869467
theorem B2164207 : Blo 2163435 2164207 := bstep (se 1 (by rfl) ⟨1623155, by rfl⟩ : syracuseStep 2164207 = 3246311) B3246311
theorem B3246317 : Blo 2163435 3246317 := bbase (se 3 (by rfl) ⟨608684, by rfl⟩ : syracuseStep 3246317 = 1217369) (by norm_num)
theorem B2164211 : Blo 2163435 2164211 := bstep (se 1 (by rfl) ⟨1623158, by rfl⟩ : syracuseStep 2164211 = 3246317) B3246317
theorem B4869485 : Blo 2163435 4869485 := bbase (se 3 (by rfl) ⟨913028, by rfl⟩ : syracuseStep 4869485 = 1826057) (by norm_num)
theorem B3246323 : Blo 2163435 3246323 := bstep (se 1 (by rfl) ⟨2434742, by rfl⟩ : syracuseStep 3246323 = 4869485) B4869485
theorem B2164215 : Blo 2163435 2164215 := bstep (se 1 (by rfl) ⟨1623161, by rfl⟩ : syracuseStep 2164215 = 3246323) B3246323
theorem B4108637 : Blo 2163435 4108637 := bbase (se 3 (by rfl) ⟨770369, by rfl⟩ : syracuseStep 4108637 = 1540739) (by norm_num)
theorem B2739091 : Blo 2163435 2739091 := bstep (se 1 (by rfl) ⟨2054318, by rfl⟩ : syracuseStep 2739091 = 4108637) B4108637
theorem B3652121 : Blo 2163435 3652121 := bstep (se 2 (by rfl) ⟨1369545, by rfl⟩ : syracuseStep 3652121 = 2739091) B2739091
theorem B2434747 : Blo 2163435 2434747 := bstep (se 1 (by rfl) ⟨1826060, by rfl⟩ : syracuseStep 2434747 = 3652121) B3652121
theorem B3246329 : Blo 2163435 3246329 := bstep (se 2 (by rfl) ⟨1217373, by rfl⟩ : syracuseStep 3246329 = 2434747) B2434747
theorem B2164219 : Blo 2163435 2164219 := bstep (se 1 (by rfl) ⟨1623164, by rfl⟩ : syracuseStep 2164219 = 3246329) B3246329
theorem B10400005 : Blo 2163435 10400005 := bbase (se 4 (by rfl) ⟨975000, by rfl⟩ : syracuseStep 10400005 = 1950001) (by norm_num)
theorem B55466693 : Blo 2163435 55466693 := bstep (se 4 (by rfl) ⟨5200002, by rfl⟩ : syracuseStep 55466693 = 10400005) B10400005
theorem B36977795 : Blo 2163435 36977795 := bstep (se 1 (by rfl) ⟨27733346, by rfl⟩ : syracuseStep 36977795 = 55466693) B55466693
theorem B24651863 : Blo 2163435 24651863 := bstep (se 1 (by rfl) ⟨18488897, by rfl⟩ : syracuseStep 24651863 = 36977795) B36977795
theorem B16434575 : Blo 2163435 16434575 := bstep (se 1 (by rfl) ⟨12325931, by rfl⟩ : syracuseStep 16434575 = 24651863) B24651863
theorem B10956383 : Blo 2163435 10956383 := bstep (se 1 (by rfl) ⟨8217287, by rfl⟩ : syracuseStep 10956383 = 16434575) B16434575
theorem B7304255 : Blo 2163435 7304255 := bstep (se 1 (by rfl) ⟨5478191, by rfl⟩ : syracuseStep 7304255 = 10956383) B10956383
theorem B4869503 : Blo 2163435 4869503 := bstep (se 1 (by rfl) ⟨3652127, by rfl⟩ : syracuseStep 4869503 = 7304255) B7304255
theorem B3246335 : Blo 2163435 3246335 := bstep (se 1 (by rfl) ⟨2434751, by rfl⟩ : syracuseStep 3246335 = 4869503) B4869503
theorem B2164223 : Blo 2163435 2164223 := bstep (se 1 (by rfl) ⟨1623167, by rfl⟩ : syracuseStep 2164223 = 3246335) B3246335
theorem B3246341 : Blo 2163435 3246341 := bbase (se 4 (by rfl) ⟨304344, by rfl⟩ : syracuseStep 3246341 = 608689) (by norm_num)
theorem B2164227 : Blo 2163435 2164227 := bstep (se 1 (by rfl) ⟨1623170, by rfl⟩ : syracuseStep 2164227 = 3246341) B3246341
theorem B3652141 : Blo 2163435 3652141 := bbase (se 3 (by rfl) ⟨684776, by rfl⟩ : syracuseStep 3652141 = 1369553) (by norm_num)
theorem B4869521 : Blo 2163435 4869521 := bstep (se 2 (by rfl) ⟨1826070, by rfl⟩ : syracuseStep 4869521 = 3652141) B3652141
theorem B3246347 : Blo 2163435 3246347 := bstep (se 1 (by rfl) ⟨2434760, by rfl⟩ : syracuseStep 3246347 = 4869521) B4869521
theorem B2164231 : Blo 2163435 2164231 := bstep (se 1 (by rfl) ⟨1623173, by rfl⟩ : syracuseStep 2164231 = 3246347) B3246347
theorem B2434765 : Blo 2163435 2434765 := bbase (se 3 (by rfl) ⟨456518, by rfl⟩ : syracuseStep 2434765 = 913037) (by norm_num)
theorem B3246353 : Blo 2163435 3246353 := bstep (se 2 (by rfl) ⟨1217382, by rfl⟩ : syracuseStep 3246353 = 2434765) B2434765
theorem B2164235 : Blo 2163435 2164235 := bstep (se 1 (by rfl) ⟨1623176, by rfl⟩ : syracuseStep 2164235 = 3246353) B3246353
theorem B7304309 : Blo 2163435 7304309 := bbase (se 5 (by rfl) ⟨342389, by rfl⟩ : syracuseStep 7304309 = 684779) (by norm_num)
theorem B4869539 : Blo 2163435 4869539 := bstep (se 1 (by rfl) ⟨3652154, by rfl⟩ : syracuseStep 4869539 = 7304309) B7304309
theorem B3246359 : Blo 2163435 3246359 := bstep (se 1 (by rfl) ⟨2434769, by rfl⟩ : syracuseStep 3246359 = 4869539) B4869539
theorem B2164239 : Blo 2163435 2164239 := bstep (se 1 (by rfl) ⟨1623179, by rfl⟩ : syracuseStep 2164239 = 3246359) B3246359
theorem B3246365 : Blo 2163435 3246365 := bbase (se 3 (by rfl) ⟨608693, by rfl⟩ : syracuseStep 3246365 = 1217387) (by norm_num)
theorem B2164243 : Blo 2163435 2164243 := bstep (se 1 (by rfl) ⟨1623182, by rfl⟩ : syracuseStep 2164243 = 3246365) B3246365
theorem B4869557 : Blo 2163435 4869557 := bbase (se 5 (by rfl) ⟨228260, by rfl⟩ : syracuseStep 4869557 = 456521) (by norm_num)
theorem B3246371 : Blo 2163435 3246371 := bstep (se 1 (by rfl) ⟨2434778, by rfl⟩ : syracuseStep 3246371 = 4869557) B4869557
theorem B2164247 : Blo 2163435 2164247 := bstep (se 1 (by rfl) ⟨1623185, by rfl⟩ : syracuseStep 2164247 = 3246371) B3246371
theorem B4622285 : Blo 2163435 4622285 := bbase (se 3 (by rfl) ⟨866678, by rfl⟩ : syracuseStep 4622285 = 1733357) (by norm_num)
theorem B12326093 : Blo 2163435 12326093 := bstep (se 3 (by rfl) ⟨2311142, by rfl⟩ : syracuseStep 12326093 = 4622285) B4622285
theorem B8217395 : Blo 2163435 8217395 := bstep (se 1 (by rfl) ⟨6163046, by rfl⟩ : syracuseStep 8217395 = 12326093) B12326093
theorem B5478263 : Blo 2163435 5478263 := bstep (se 1 (by rfl) ⟨4108697, by rfl⟩ : syracuseStep 5478263 = 8217395) B8217395
theorem B3652175 : Blo 2163435 3652175 := bstep (se 1 (by rfl) ⟨2739131, by rfl⟩ : syracuseStep 3652175 = 5478263) B5478263
theorem B2434783 : Blo 2163435 2434783 := bstep (se 1 (by rfl) ⟨1826087, by rfl⟩ : syracuseStep 2434783 = 3652175) B3652175
theorem B3246377 : Blo 2163435 3246377 := bstep (se 2 (by rfl) ⟨1217391, by rfl⟩ : syracuseStep 3246377 = 2434783) B2434783
theorem B2164251 : Blo 2163435 2164251 := bstep (se 1 (by rfl) ⟨1623188, by rfl⟩ : syracuseStep 2164251 = 3246377) B3246377
theorem B4622293 : Blo 2163435 4622293 := bbase (se 7 (by rfl) ⟨54167, by rfl⟩ : syracuseStep 4622293 = 108335) (by norm_num)
theorem B6163057 : Blo 2163435 6163057 := bstep (se 2 (by rfl) ⟨2311146, by rfl⟩ : syracuseStep 6163057 = 4622293) B4622293
theorem B8217409 : Blo 2163435 8217409 := bstep (se 2 (by rfl) ⟨3081528, by rfl⟩ : syracuseStep 8217409 = 6163057) B6163057
theorem B10956545 : Blo 2163435 10956545 := bstep (se 2 (by rfl) ⟨4108704, by rfl⟩ : syracuseStep 10956545 = 8217409) B8217409
theorem B7304363 : Blo 2163435 7304363 := bstep (se 1 (by rfl) ⟨5478272, by rfl⟩ : syracuseStep 7304363 = 10956545) B10956545
theorem B4869575 : Blo 2163435 4869575 := bstep (se 1 (by rfl) ⟨3652181, by rfl⟩ : syracuseStep 4869575 = 7304363) B7304363
theorem B3246383 : Blo 2163435 3246383 := bstep (se 1 (by rfl) ⟨2434787, by rfl⟩ : syracuseStep 3246383 = 4869575) B4869575
theorem B2164255 : Blo 2163435 2164255 := bstep (se 1 (by rfl) ⟨1623191, by rfl⟩ : syracuseStep 2164255 = 3246383) B3246383
theorem B3246389 : Blo 2163435 3246389 := bbase (se 5 (by rfl) ⟨152174, by rfl⟩ : syracuseStep 3246389 = 304349) (by norm_num)
theorem B2164259 : Blo 2163435 2164259 := bstep (se 1 (by rfl) ⟨1623194, by rfl⟩ : syracuseStep 2164259 = 3246389) B3246389
theorem B5478293 : Blo 2163435 5478293 := bbase (se 6 (by rfl) ⟨128397, by rfl⟩ : syracuseStep 5478293 = 256795) (by norm_num)
theorem B3652195 : Blo 2163435 3652195 := bstep (se 1 (by rfl) ⟨2739146, by rfl⟩ : syracuseStep 3652195 = 5478293) B5478293
theorem B4869593 : Blo 2163435 4869593 := bstep (se 2 (by rfl) ⟨1826097, by rfl⟩ : syracuseStep 4869593 = 3652195) B3652195
theorem B3246395 : Blo 2163435 3246395 := bstep (se 1 (by rfl) ⟨2434796, by rfl⟩ : syracuseStep 3246395 = 4869593) B4869593
theorem B2164263 : Blo 2163435 2164263 := bstep (se 1 (by rfl) ⟨1623197, by rfl⟩ : syracuseStep 2164263 = 3246395) B3246395
theorem B2434801 : Blo 2163435 2434801 := bbase (se 2 (by rfl) ⟨913050, by rfl⟩ : syracuseStep 2434801 = 1826101) (by norm_num)
theorem B3246401 : Blo 2163435 3246401 := bstep (se 2 (by rfl) ⟨1217400, by rfl⟩ : syracuseStep 3246401 = 2434801) B2434801
theorem B2164267 : Blo 2163435 2164267 := bstep (se 1 (by rfl) ⟨1623200, by rfl⟩ : syracuseStep 2164267 = 3246401) B3246401
theorem B9872101 : Blo 2163435 9872101 := bbase (se 4 (by rfl) ⟨925509, by rfl⟩ : syracuseStep 9872101 = 1851019) (by norm_num)
theorem B52651205 : Blo 2163435 52651205 := bstep (se 4 (by rfl) ⟨4936050, by rfl⟩ : syracuseStep 52651205 = 9872101) B9872101
theorem B35100803 : Blo 2163435 35100803 := bstep (se 1 (by rfl) ⟨26325602, by rfl⟩ : syracuseStep 35100803 = 52651205) B52651205
theorem B23400535 : Blo 2163435 23400535 := bstep (se 1 (by rfl) ⟨17550401, by rfl⟩ : syracuseStep 23400535 = 35100803) B35100803
theorem B31200713 : Blo 2163435 31200713 := bstep (se 2 (by rfl) ⟨11700267, by rfl⟩ : syracuseStep 31200713 = 23400535) B23400535
theorem B20800475 : Blo 2163435 20800475 := bstep (se 1 (by rfl) ⟨15600356, by rfl⟩ : syracuseStep 20800475 = 31200713) B31200713
theorem B13866983 : Blo 2163435 13866983 := bstep (se 1 (by rfl) ⟨10400237, by rfl⟩ : syracuseStep 13866983 = 20800475) B20800475
theorem B9244655 : Blo 2163435 9244655 := bstep (se 1 (by rfl) ⟨6933491, by rfl⟩ : syracuseStep 9244655 = 13866983) B13866983
theorem B6163103 : Blo 2163435 6163103 := bstep (se 1 (by rfl) ⟨4622327, by rfl⟩ : syracuseStep 6163103 = 9244655) B9244655
theorem B4108735 : Blo 2163435 4108735 := bstep (se 1 (by rfl) ⟨3081551, by rfl⟩ : syracuseStep 4108735 = 6163103) B6163103
theorem B5478313 : Blo 2163435 5478313 := bstep (se 2 (by rfl) ⟨2054367, by rfl⟩ : syracuseStep 5478313 = 4108735) B4108735
theorem B7304417 : Blo 2163435 7304417 := bstep (se 2 (by rfl) ⟨2739156, by rfl⟩ : syracuseStep 7304417 = 5478313) B5478313
theorem B4869611 : Blo 2163435 4869611 := bstep (se 1 (by rfl) ⟨3652208, by rfl⟩ : syracuseStep 4869611 = 7304417) B7304417
theorem B3246407 : Blo 2163435 3246407 := bstep (se 1 (by rfl) ⟨2434805, by rfl⟩ : syracuseStep 3246407 = 4869611) B4869611
theorem B2164271 : Blo 2163435 2164271 := bstep (se 1 (by rfl) ⟨1623203, by rfl⟩ : syracuseStep 2164271 = 3246407) B3246407
theorem B3246413 : Blo 2163435 3246413 := bbase (se 3 (by rfl) ⟨608702, by rfl⟩ : syracuseStep 3246413 = 1217405) (by norm_num)
theorem B2164275 : Blo 2163435 2164275 := bstep (se 1 (by rfl) ⟨1623206, by rfl⟩ : syracuseStep 2164275 = 3246413) B3246413
theorem B4869629 : Blo 2163435 4869629 := bbase (se 3 (by rfl) ⟨913055, by rfl⟩ : syracuseStep 4869629 = 1826111) (by norm_num)
theorem B3246419 : Blo 2163435 3246419 := bstep (se 1 (by rfl) ⟨2434814, by rfl⟩ : syracuseStep 3246419 = 4869629) B4869629
theorem B2164279 : Blo 2163435 2164279 := bstep (se 1 (by rfl) ⟨1623209, by rfl⟩ : syracuseStep 2164279 = 3246419) B3246419
theorem B3652229 : Blo 2163435 3652229 := bbase (se 4 (by rfl) ⟨342396, by rfl⟩ : syracuseStep 3652229 = 684793) (by norm_num)
theorem B2434819 : Blo 2163435 2434819 := bstep (se 1 (by rfl) ⟨1826114, by rfl⟩ : syracuseStep 2434819 = 3652229) B3652229
theorem B3246425 : Blo 2163435 3246425 := bstep (se 2 (by rfl) ⟨1217409, by rfl⟩ : syracuseStep 3246425 = 2434819) B2434819
theorem B2164283 : Blo 2163435 2164283 := bstep (se 1 (by rfl) ⟨1623212, by rfl⟩ : syracuseStep 2164283 = 3246425) B3246425
theorem B16435061 : Blo 2163435 16435061 := bbase (se 5 (by rfl) ⟨770393, by rfl⟩ : syracuseStep 16435061 = 1540787) (by norm_num)
theorem B10956707 : Blo 2163435 10956707 := bstep (se 1 (by rfl) ⟨8217530, by rfl⟩ : syracuseStep 10956707 = 16435061) B16435061
theorem B7304471 : Blo 2163435 7304471 := bstep (se 1 (by rfl) ⟨5478353, by rfl⟩ : syracuseStep 7304471 = 10956707) B10956707
theorem B4869647 : Blo 2163435 4869647 := bstep (se 1 (by rfl) ⟨3652235, by rfl⟩ : syracuseStep 4869647 = 7304471) B7304471
theorem B3246431 : Blo 2163435 3246431 := bstep (se 1 (by rfl) ⟨2434823, by rfl⟩ : syracuseStep 3246431 = 4869647) B4869647
theorem B2164287 : Blo 2163435 2164287 := bstep (se 1 (by rfl) ⟨1623215, by rfl⟩ : syracuseStep 2164287 = 3246431) B3246431
theorem B3246437 : Blo 2163435 3246437 := bbase (se 4 (by rfl) ⟨304353, by rfl⟩ : syracuseStep 3246437 = 608707) (by norm_num)
theorem B2164291 : Blo 2163435 2164291 := bstep (se 1 (by rfl) ⟨1623218, by rfl⟩ : syracuseStep 2164291 = 3246437) B3246437
theorem B4108781 : Blo 2163435 4108781 := bbase (se 3 (by rfl) ⟨770396, by rfl⟩ : syracuseStep 4108781 = 1540793) (by norm_num)
theorem B2739187 : Blo 2163435 2739187 := bstep (se 1 (by rfl) ⟨2054390, by rfl⟩ : syracuseStep 2739187 = 4108781) B4108781
theorem B3652249 : Blo 2163435 3652249 := bstep (se 2 (by rfl) ⟨1369593, by rfl⟩ : syracuseStep 3652249 = 2739187) B2739187
theorem B4869665 : Blo 2163435 4869665 := bstep (se 2 (by rfl) ⟨1826124, by rfl⟩ : syracuseStep 4869665 = 3652249) B3652249
theorem B3246443 : Blo 2163435 3246443 := bstep (se 1 (by rfl) ⟨2434832, by rfl⟩ : syracuseStep 3246443 = 4869665) B4869665
theorem B2164295 : Blo 2163435 2164295 := bstep (se 1 (by rfl) ⟨1623221, by rfl⟩ : syracuseStep 2164295 = 3246443) B3246443
theorem B2434837 : Blo 2163435 2434837 := bbase (se 6 (by rfl) ⟨57066, by rfl⟩ : syracuseStep 2434837 = 114133) (by norm_num)
theorem B3246449 : Blo 2163435 3246449 := bstep (se 2 (by rfl) ⟨1217418, by rfl⟩ : syracuseStep 3246449 = 2434837) B2434837
theorem B2164299 : Blo 2163435 2164299 := bstep (se 1 (by rfl) ⟨1623224, by rfl⟩ : syracuseStep 2164299 = 3246449) B3246449
theorem B2739197 : Blo 2163435 2739197 := bbase (se 3 (by rfl) ⟨513599, by rfl⟩ : syracuseStep 2739197 = 1027199) (by norm_num)
theorem B7304525 : Blo 2163435 7304525 := bstep (se 3 (by rfl) ⟨1369598, by rfl⟩ : syracuseStep 7304525 = 2739197) B2739197
theorem B4869683 : Blo 2163435 4869683 := bstep (se 1 (by rfl) ⟨3652262, by rfl⟩ : syracuseStep 4869683 = 7304525) B7304525
theorem B3246455 : Blo 2163435 3246455 := bstep (se 1 (by rfl) ⟨2434841, by rfl⟩ : syracuseStep 3246455 = 4869683) B4869683
theorem B2164303 : Blo 2163435 2164303 := bstep (se 1 (by rfl) ⟨1623227, by rfl⟩ : syracuseStep 2164303 = 3246455) B3246455
theorem B3246461 : Blo 2163435 3246461 := bbase (se 3 (by rfl) ⟨608711, by rfl⟩ : syracuseStep 3246461 = 1217423) (by norm_num)
theorem B2164307 : Blo 2163435 2164307 := bstep (se 1 (by rfl) ⟨1623230, by rfl⟩ : syracuseStep 2164307 = 3246461) B3246461
theorem B4869701 : Blo 2163435 4869701 := bbase (se 4 (by rfl) ⟨456534, by rfl⟩ : syracuseStep 4869701 = 913069) (by norm_num)
theorem B3246467 : Blo 2163435 3246467 := bstep (se 1 (by rfl) ⟨2434850, by rfl⟩ : syracuseStep 3246467 = 4869701) B4869701
theorem B2164311 : Blo 2163435 2164311 := bstep (se 1 (by rfl) ⟨1623233, by rfl⟩ : syracuseStep 2164311 = 3246467) B3246467
theorem B2600113 : Blo 2163435 2600113 := bbase (se 2 (by rfl) ⟨975042, by rfl⟩ : syracuseStep 2600113 = 1950085) (by norm_num)
theorem B3466817 : Blo 2163435 3466817 := bstep (se 2 (by rfl) ⟨1300056, by rfl⟩ : syracuseStep 3466817 = 2600113) B2600113
theorem B2311211 : Blo 2163435 2311211 := bstep (se 1 (by rfl) ⟨1733408, by rfl⟩ : syracuseStep 2311211 = 3466817) B3466817
theorem B6163229 : Blo 2163435 6163229 := bstep (se 3 (by rfl) ⟨1155605, by rfl⟩ : syracuseStep 6163229 = 2311211) B2311211
theorem B4108819 : Blo 2163435 4108819 := bstep (se 1 (by rfl) ⟨3081614, by rfl⟩ : syracuseStep 4108819 = 6163229) B6163229
theorem B5478425 : Blo 2163435 5478425 := bstep (se 2 (by rfl) ⟨2054409, by rfl⟩ : syracuseStep 5478425 = 4108819) B4108819
theorem B3652283 : Blo 2163435 3652283 := bstep (se 1 (by rfl) ⟨2739212, by rfl⟩ : syracuseStep 3652283 = 5478425) B5478425
theorem B2434855 : Blo 2163435 2434855 := bstep (se 1 (by rfl) ⟨1826141, by rfl⟩ : syracuseStep 2434855 = 3652283) B3652283
theorem B3246473 : Blo 2163435 3246473 := bstep (se 2 (by rfl) ⟨1217427, by rfl⟩ : syracuseStep 3246473 = 2434855) B2434855
theorem B2164315 : Blo 2163435 2164315 := bstep (se 1 (by rfl) ⟨1623236, by rfl⟩ : syracuseStep 2164315 = 3246473) B3246473
theorem B10956869 : Blo 2163435 10956869 := bbase (se 4 (by rfl) ⟨1027206, by rfl⟩ : syracuseStep 10956869 = 2054413) (by norm_num)
theorem B7304579 : Blo 2163435 7304579 := bstep (se 1 (by rfl) ⟨5478434, by rfl⟩ : syracuseStep 7304579 = 10956869) B10956869
theorem B4869719 : Blo 2163435 4869719 := bstep (se 1 (by rfl) ⟨3652289, by rfl⟩ : syracuseStep 4869719 = 7304579) B7304579
theorem B3246479 : Blo 2163435 3246479 := bstep (se 1 (by rfl) ⟨2434859, by rfl⟩ : syracuseStep 3246479 = 4869719) B4869719
theorem B2164319 : Blo 2163435 2164319 := bstep (se 1 (by rfl) ⟨1623239, by rfl⟩ : syracuseStep 2164319 = 3246479) B3246479
theorem B3246485 : Blo 2163435 3246485 := bbase (se 6 (by rfl) ⟨76089, by rfl⟩ : syracuseStep 3246485 = 152179) (by norm_num)
theorem B2164323 : Blo 2163435 2164323 := bstep (se 1 (by rfl) ⟨1623242, by rfl⟩ : syracuseStep 2164323 = 3246485) B3246485
theorem B4164901 : Blo 2163435 4164901 := bbase (se 4 (by rfl) ⟨390459, by rfl⟩ : syracuseStep 4164901 = 780919) (by norm_num)
theorem B22212805 : Blo 2163435 22212805 := bstep (se 4 (by rfl) ⟨2082450, by rfl⟩ : syracuseStep 22212805 = 4164901) B4164901
theorem B29617073 : Blo 2163435 29617073 := bstep (se 2 (by rfl) ⟨11106402, by rfl⟩ : syracuseStep 29617073 = 22212805) B22212805
theorem B19744715 : Blo 2163435 19744715 := bstep (se 1 (by rfl) ⟨14808536, by rfl⟩ : syracuseStep 19744715 = 29617073) B29617073
theorem B13163143 : Blo 2163435 13163143 := bstep (se 1 (by rfl) ⟨9872357, by rfl⟩ : syracuseStep 13163143 = 19744715) B19744715
theorem B17550857 : Blo 2163435 17550857 := bstep (se 2 (by rfl) ⟨6581571, by rfl⟩ : syracuseStep 17550857 = 13163143) B13163143
theorem B11700571 : Blo 2163435 11700571 := bstep (se 1 (by rfl) ⟨8775428, by rfl⟩ : syracuseStep 11700571 = 17550857) B17550857
theorem B15600761 : Blo 2163435 15600761 := bstep (se 2 (by rfl) ⟨5850285, by rfl⟩ : syracuseStep 15600761 = 11700571) B11700571
theorem B10400507 : Blo 2163435 10400507 := bstep (se 1 (by rfl) ⟨7800380, by rfl⟩ : syracuseStep 10400507 = 15600761) B15600761
theorem B6933671 : Blo 2163435 6933671 := bstep (se 1 (by rfl) ⟨5200253, by rfl⟩ : syracuseStep 6933671 = 10400507) B10400507
theorem B4622447 : Blo 2163435 4622447 := bstep (se 1 (by rfl) ⟨3466835, by rfl⟩ : syracuseStep 4622447 = 6933671) B6933671
theorem B12326525 : Blo 2163435 12326525 := bstep (se 3 (by rfl) ⟨2311223, by rfl⟩ : syracuseStep 12326525 = 4622447) B4622447
theorem B8217683 : Blo 2163435 8217683 := bstep (se 1 (by rfl) ⟨6163262, by rfl⟩ : syracuseStep 8217683 = 12326525) B12326525
theorem B5478455 : Blo 2163435 5478455 := bstep (se 1 (by rfl) ⟨4108841, by rfl⟩ : syracuseStep 5478455 = 8217683) B8217683
theorem B3652303 : Blo 2163435 3652303 := bstep (se 1 (by rfl) ⟨2739227, by rfl⟩ : syracuseStep 3652303 = 5478455) B5478455
theorem B4869737 : Blo 2163435 4869737 := bstep (se 2 (by rfl) ⟨1826151, by rfl⟩ : syracuseStep 4869737 = 3652303) B3652303
theorem B3246491 : Blo 2163435 3246491 := bstep (se 1 (by rfl) ⟨2434868, by rfl⟩ : syracuseStep 3246491 = 4869737) B4869737
theorem B2164327 : Blo 2163435 2164327 := bstep (se 1 (by rfl) ⟨1623245, by rfl⟩ : syracuseStep 2164327 = 3246491) B3246491
theorem B2434873 : Blo 2163435 2434873 := bbase (se 2 (by rfl) ⟨913077, by rfl⟩ : syracuseStep 2434873 = 1826155) (by norm_num)
theorem B3246497 : Blo 2163435 3246497 := bstep (se 2 (by rfl) ⟨1217436, by rfl⟩ : syracuseStep 3246497 = 2434873) B2434873
theorem B2164331 : Blo 2163435 2164331 := bstep (se 1 (by rfl) ⟨1623248, by rfl⟩ : syracuseStep 2164331 = 3246497) B3246497
theorem B6163285 : Blo 2163435 6163285 := bbase (se 9 (by rfl) ⟨18056, by rfl⟩ : syracuseStep 6163285 = 36113) (by norm_num)
theorem B8217713 : Blo 2163435 8217713 := bstep (se 2 (by rfl) ⟨3081642, by rfl⟩ : syracuseStep 8217713 = 6163285) B6163285
theorem B5478475 : Blo 2163435 5478475 := bstep (se 1 (by rfl) ⟨4108856, by rfl⟩ : syracuseStep 5478475 = 8217713) B8217713
theorem B7304633 : Blo 2163435 7304633 := bstep (se 2 (by rfl) ⟨2739237, by rfl⟩ : syracuseStep 7304633 = 5478475) B5478475
theorem B4869755 : Blo 2163435 4869755 := bstep (se 1 (by rfl) ⟨3652316, by rfl⟩ : syracuseStep 4869755 = 7304633) B7304633
theorem B3246503 : Blo 2163435 3246503 := bstep (se 1 (by rfl) ⟨2434877, by rfl⟩ : syracuseStep 3246503 = 4869755) B4869755
theorem B2164335 : Blo 2163435 2164335 := bstep (se 1 (by rfl) ⟨1623251, by rfl⟩ : syracuseStep 2164335 = 3246503) B3246503
theorem B3246509 : Blo 2163435 3246509 := bbase (se 3 (by rfl) ⟨608720, by rfl⟩ : syracuseStep 3246509 = 1217441) (by norm_num)
theorem B2164339 : Blo 2163435 2164339 := bstep (se 1 (by rfl) ⟨1623254, by rfl⟩ : syracuseStep 2164339 = 3246509) B3246509
theorem B4869773 : Blo 2163435 4869773 := bbase (se 3 (by rfl) ⟨913082, by rfl⟩ : syracuseStep 4869773 = 1826165) (by norm_num)
theorem B3246515 : Blo 2163435 3246515 := bstep (se 1 (by rfl) ⟨2434886, by rfl⟩ : syracuseStep 3246515 = 4869773) B4869773
theorem B2164343 : Blo 2163435 2164343 := bstep (se 1 (by rfl) ⟨1623257, by rfl⟩ : syracuseStep 2164343 = 3246515) B3246515
theorem B2739253 : Blo 2163435 2739253 := bbase (se 5 (by rfl) ⟨128402, by rfl⟩ : syracuseStep 2739253 = 256805) (by norm_num)
theorem B3652337 : Blo 2163435 3652337 := bstep (se 2 (by rfl) ⟨1369626, by rfl⟩ : syracuseStep 3652337 = 2739253) B2739253
theorem B2434891 : Blo 2163435 2434891 := bstep (se 1 (by rfl) ⟨1826168, by rfl⟩ : syracuseStep 2434891 = 3652337) B3652337
theorem B3246521 : Blo 2163435 3246521 := bstep (se 2 (by rfl) ⟨1217445, by rfl⟩ : syracuseStep 3246521 = 2434891) B2434891
theorem B2164347 : Blo 2163435 2164347 := bstep (se 1 (by rfl) ⟨1623260, by rfl⟩ : syracuseStep 2164347 = 3246521) B3246521
theorem B2193881 : Blo 2163435 2193881 := bbase (se 2 (by rfl) ⟨822705, by rfl⟩ : syracuseStep 2193881 = 1645411) (by norm_num)
theorem B5850349 : Blo 2163435 5850349 := bstep (se 3 (by rfl) ⟨1096940, by rfl⟩ : syracuseStep 5850349 = 2193881) B2193881
theorem B31201861 : Blo 2163435 31201861 := bstep (se 4 (by rfl) ⟨2925174, by rfl⟩ : syracuseStep 31201861 = 5850349) B5850349
theorem B41602481 : Blo 2163435 41602481 := bstep (se 2 (by rfl) ⟨15600930, by rfl⟩ : syracuseStep 41602481 = 31201861) B31201861
theorem B27734987 : Blo 2163435 27734987 := bstep (se 1 (by rfl) ⟨20801240, by rfl⟩ : syracuseStep 27734987 = 41602481) B41602481
theorem B18489991 : Blo 2163435 18489991 := bstep (se 1 (by rfl) ⟨13867493, by rfl⟩ : syracuseStep 18489991 = 27734987) B27734987
theorem B24653321 : Blo 2163435 24653321 := bstep (se 2 (by rfl) ⟨9244995, by rfl⟩ : syracuseStep 24653321 = 18489991) B18489991
theorem B16435547 : Blo 2163435 16435547 := bstep (se 1 (by rfl) ⟨12326660, by rfl⟩ : syracuseStep 16435547 = 24653321) B24653321
theorem B10957031 : Blo 2163435 10957031 := bstep (se 1 (by rfl) ⟨8217773, by rfl⟩ : syracuseStep 10957031 = 16435547) B16435547
theorem B7304687 : Blo 2163435 7304687 := bstep (se 1 (by rfl) ⟨5478515, by rfl⟩ : syracuseStep 7304687 = 10957031) B10957031
theorem B4869791 : Blo 2163435 4869791 := bstep (se 1 (by rfl) ⟨3652343, by rfl⟩ : syracuseStep 4869791 = 7304687) B7304687
theorem B3246527 : Blo 2163435 3246527 := bstep (se 1 (by rfl) ⟨2434895, by rfl⟩ : syracuseStep 3246527 = 4869791) B4869791
theorem B2164351 : Blo 2163435 2164351 := bstep (se 1 (by rfl) ⟨1623263, by rfl⟩ : syracuseStep 2164351 = 3246527) B3246527
theorem B3246533 : Blo 2163435 3246533 := bbase (se 4 (by rfl) ⟨304362, by rfl⟩ : syracuseStep 3246533 = 608725) (by norm_num)
theorem B2164355 : Blo 2163435 2164355 := bstep (se 1 (by rfl) ⟨1623266, by rfl⟩ : syracuseStep 2164355 = 3246533) B3246533
theorem B3652357 : Blo 2163435 3652357 := bbase (se 4 (by rfl) ⟨342408, by rfl⟩ : syracuseStep 3652357 = 684817) (by norm_num)
theorem B4869809 : Blo 2163435 4869809 := bstep (se 2 (by rfl) ⟨1826178, by rfl⟩ : syracuseStep 4869809 = 3652357) B3652357
theorem B3246539 : Blo 2163435 3246539 := bstep (se 1 (by rfl) ⟨2434904, by rfl⟩ : syracuseStep 3246539 = 4869809) B4869809
theorem B2164359 : Blo 2163435 2164359 := bstep (se 1 (by rfl) ⟨1623269, by rfl⟩ : syracuseStep 2164359 = 3246539) B3246539
theorem B2434909 : Blo 2163435 2434909 := bbase (se 3 (by rfl) ⟨456545, by rfl⟩ : syracuseStep 2434909 = 913091) (by norm_num)
theorem B3246545 : Blo 2163435 3246545 := bstep (se 2 (by rfl) ⟨1217454, by rfl⟩ : syracuseStep 3246545 = 2434909) B2434909
theorem B2164363 : Blo 2163435 2164363 := bstep (se 1 (by rfl) ⟨1623272, by rfl⟩ : syracuseStep 2164363 = 3246545) B3246545
theorem B7304741 : Blo 2163435 7304741 := bbase (se 4 (by rfl) ⟨684819, by rfl⟩ : syracuseStep 7304741 = 1369639) (by norm_num)
theorem B4869827 : Blo 2163435 4869827 := bstep (se 1 (by rfl) ⟨3652370, by rfl⟩ : syracuseStep 4869827 = 7304741) B7304741
theorem B3246551 : Blo 2163435 3246551 := bstep (se 1 (by rfl) ⟨2434913, by rfl⟩ : syracuseStep 3246551 = 4869827) B4869827
theorem B2164367 : Blo 2163435 2164367 := bstep (se 1 (by rfl) ⟨1623275, by rfl⟩ : syracuseStep 2164367 = 3246551) B3246551
theorem B3246557 : Blo 2163435 3246557 := bbase (se 3 (by rfl) ⟨608729, by rfl⟩ : syracuseStep 3246557 = 1217459) (by norm_num)
theorem B2164371 : Blo 2163435 2164371 := bstep (se 1 (by rfl) ⟨1623278, by rfl⟩ : syracuseStep 2164371 = 3246557) B3246557
theorem B4869845 : Blo 2163435 4869845 := bbase (se 7 (by rfl) ⟨57068, by rfl⟩ : syracuseStep 4869845 = 114137) (by norm_num)
theorem B3246563 : Blo 2163435 3246563 := bstep (se 1 (by rfl) ⟨2434922, by rfl⟩ : syracuseStep 3246563 = 4869845) B4869845
theorem B2164375 : Blo 2163435 2164375 := bstep (se 1 (by rfl) ⟨1623281, by rfl⟩ : syracuseStep 2164375 = 3246563) B3246563
theorem B9872597 : Blo 2163435 9872597 := bbase (se 7 (by rfl) ⟨115694, by rfl⟩ : syracuseStep 9872597 = 231389) (by norm_num)
theorem B6581731 : Blo 2163435 6581731 := bstep (se 1 (by rfl) ⟨4936298, by rfl⟩ : syracuseStep 6581731 = 9872597) B9872597
theorem B8775641 : Blo 2163435 8775641 := bstep (se 2 (by rfl) ⟨3290865, by rfl⟩ : syracuseStep 8775641 = 6581731) B6581731
theorem B5850427 : Blo 2163435 5850427 := bstep (se 1 (by rfl) ⟨4387820, by rfl⟩ : syracuseStep 5850427 = 8775641) B8775641
theorem B7800569 : Blo 2163435 7800569 := bstep (se 2 (by rfl) ⟨2925213, by rfl⟩ : syracuseStep 7800569 = 5850427) B5850427
theorem B5200379 : Blo 2163435 5200379 := bstep (se 1 (by rfl) ⟨3900284, by rfl⟩ : syracuseStep 5200379 = 7800569) B7800569
theorem B3466919 : Blo 2163435 3466919 := bstep (se 1 (by rfl) ⟨2600189, by rfl⟩ : syracuseStep 3466919 = 5200379) B5200379
theorem B9245117 : Blo 2163435 9245117 := bstep (se 3 (by rfl) ⟨1733459, by rfl⟩ : syracuseStep 9245117 = 3466919) B3466919
theorem B6163411 : Blo 2163435 6163411 := bstep (se 1 (by rfl) ⟨4622558, by rfl⟩ : syracuseStep 6163411 = 9245117) B9245117
theorem B8217881 : Blo 2163435 8217881 := bstep (se 2 (by rfl) ⟨3081705, by rfl⟩ : syracuseStep 8217881 = 6163411) B6163411
theorem B5478587 : Blo 2163435 5478587 := bstep (se 1 (by rfl) ⟨4108940, by rfl⟩ : syracuseStep 5478587 = 8217881) B8217881
theorem B3652391 : Blo 2163435 3652391 := bstep (se 1 (by rfl) ⟨2739293, by rfl⟩ : syracuseStep 3652391 = 5478587) B5478587
theorem B2434927 : Blo 2163435 2434927 := bstep (se 1 (by rfl) ⟨1826195, by rfl⟩ : syracuseStep 2434927 = 3652391) B3652391
theorem B3246569 : Blo 2163435 3246569 := bstep (se 2 (by rfl) ⟨1217463, by rfl⟩ : syracuseStep 3246569 = 2434927) B2434927
theorem B2164379 : Blo 2163435 2164379 := bstep (se 1 (by rfl) ⟨1623284, by rfl⟩ : syracuseStep 2164379 = 3246569) B3246569
theorem B7800581 : Blo 2163435 7800581 := bbase (se 4 (by rfl) ⟨731304, by rfl⟩ : syracuseStep 7800581 = 1462609) (by norm_num)
theorem B20801549 : Blo 2163435 20801549 := bstep (se 3 (by rfl) ⟨3900290, by rfl⟩ : syracuseStep 20801549 = 7800581) B7800581
theorem B13867699 : Blo 2163435 13867699 := bstep (se 1 (by rfl) ⟨10400774, by rfl⟩ : syracuseStep 13867699 = 20801549) B20801549
theorem B18490265 : Blo 2163435 18490265 := bstep (se 2 (by rfl) ⟨6933849, by rfl⟩ : syracuseStep 18490265 = 13867699) B13867699
theorem B12326843 : Blo 2163435 12326843 := bstep (se 1 (by rfl) ⟨9245132, by rfl⟩ : syracuseStep 12326843 = 18490265) B18490265
theorem B8217895 : Blo 2163435 8217895 := bstep (se 1 (by rfl) ⟨6163421, by rfl⟩ : syracuseStep 8217895 = 12326843) B12326843
theorem B10957193 : Blo 2163435 10957193 := bstep (se 2 (by rfl) ⟨4108947, by rfl⟩ : syracuseStep 10957193 = 8217895) B8217895
theorem B7304795 : Blo 2163435 7304795 := bstep (se 1 (by rfl) ⟨5478596, by rfl⟩ : syracuseStep 7304795 = 10957193) B10957193
theorem B4869863 : Blo 2163435 4869863 := bstep (se 1 (by rfl) ⟨3652397, by rfl⟩ : syracuseStep 4869863 = 7304795) B7304795
theorem B3246575 : Blo 2163435 3246575 := bstep (se 1 (by rfl) ⟨2434931, by rfl⟩ : syracuseStep 3246575 = 4869863) B4869863
theorem B2164383 : Blo 2163435 2164383 := bstep (se 1 (by rfl) ⟨1623287, by rfl⟩ : syracuseStep 2164383 = 3246575) B3246575
theorem B3246581 : Blo 2163435 3246581 := bbase (se 5 (by rfl) ⟨152183, by rfl⟩ : syracuseStep 3246581 = 304367) (by norm_num)
theorem B2164387 : Blo 2163435 2164387 := bstep (se 1 (by rfl) ⟨1623290, by rfl⟩ : syracuseStep 2164387 = 3246581) B3246581
theorem B6163445 : Blo 2163435 6163445 := bbase (se 5 (by rfl) ⟨288911, by rfl⟩ : syracuseStep 6163445 = 577823) (by norm_num)
theorem B4108963 : Blo 2163435 4108963 := bstep (se 1 (by rfl) ⟨3081722, by rfl⟩ : syracuseStep 4108963 = 6163445) B6163445
theorem B5478617 : Blo 2163435 5478617 := bstep (se 2 (by rfl) ⟨2054481, by rfl⟩ : syracuseStep 5478617 = 4108963) B4108963
theorem B3652411 : Blo 2163435 3652411 := bstep (se 1 (by rfl) ⟨2739308, by rfl⟩ : syracuseStep 3652411 = 5478617) B5478617
theorem B4869881 : Blo 2163435 4869881 := bstep (se 2 (by rfl) ⟨1826205, by rfl⟩ : syracuseStep 4869881 = 3652411) B3652411
theorem B3246587 : Blo 2163435 3246587 := bstep (se 1 (by rfl) ⟨2434940, by rfl⟩ : syracuseStep 3246587 = 4869881) B4869881
theorem B2164391 : Blo 2163435 2164391 := bstep (se 1 (by rfl) ⟨1623293, by rfl⟩ : syracuseStep 2164391 = 3246587) B3246587
theorem B2434945 : Blo 2163435 2434945 := bbase (se 2 (by rfl) ⟨913104, by rfl⟩ : syracuseStep 2434945 = 1826209) (by norm_num)
theorem B3246593 : Blo 2163435 3246593 := bstep (se 2 (by rfl) ⟨1217472, by rfl⟩ : syracuseStep 3246593 = 2434945) B2434945
theorem B2164395 : Blo 2163435 2164395 := bstep (se 1 (by rfl) ⟨1623296, by rfl⟩ : syracuseStep 2164395 = 3246593) B3246593
theorem B5478637 : Blo 2163435 5478637 := bbase (se 3 (by rfl) ⟨1027244, by rfl⟩ : syracuseStep 5478637 = 2054489) (by norm_num)
theorem B7304849 : Blo 2163435 7304849 := bstep (se 2 (by rfl) ⟨2739318, by rfl⟩ : syracuseStep 7304849 = 5478637) B5478637
theorem B4869899 : Blo 2163435 4869899 := bstep (se 1 (by rfl) ⟨3652424, by rfl⟩ : syracuseStep 4869899 = 7304849) B7304849
theorem B3246599 : Blo 2163435 3246599 := bstep (se 1 (by rfl) ⟨2434949, by rfl⟩ : syracuseStep 3246599 = 4869899) B4869899
theorem B2164399 : Blo 2163435 2164399 := bstep (se 1 (by rfl) ⟨1623299, by rfl⟩ : syracuseStep 2164399 = 3246599) B3246599
theorem B3246605 : Blo 2163435 3246605 := bbase (se 3 (by rfl) ⟨608738, by rfl⟩ : syracuseStep 3246605 = 1217477) (by norm_num)
theorem B2164403 : Blo 2163435 2164403 := bstep (se 1 (by rfl) ⟨1623302, by rfl⟩ : syracuseStep 2164403 = 3246605) B3246605
theorem B4869917 : Blo 2163435 4869917 := bbase (se 3 (by rfl) ⟨913109, by rfl⟩ : syracuseStep 4869917 = 1826219) (by norm_num)
theorem B3246611 : Blo 2163435 3246611 := bstep (se 1 (by rfl) ⟨2434958, by rfl⟩ : syracuseStep 3246611 = 4869917) B4869917
theorem B2164407 : Blo 2163435 2164407 := bstep (se 1 (by rfl) ⟨1623305, by rfl⟩ : syracuseStep 2164407 = 3246611) B3246611
theorem B3652445 : Blo 2163435 3652445 := bbase (se 3 (by rfl) ⟨684833, by rfl⟩ : syracuseStep 3652445 = 1369667) (by norm_num)
theorem B2434963 : Blo 2163435 2434963 := bstep (se 1 (by rfl) ⟨1826222, by rfl⟩ : syracuseStep 2434963 = 3652445) B3652445
theorem B3246617 : Blo 2163435 3246617 := bstep (se 2 (by rfl) ⟨1217481, by rfl⟩ : syracuseStep 3246617 = 2434963) B2434963
theorem B2164411 : Blo 2163435 2164411 := bstep (se 1 (by rfl) ⟨1623308, by rfl⟩ : syracuseStep 2164411 = 3246617) B3246617
theorem B9245269 : Blo 2163435 9245269 := bbase (se 8 (by rfl) ⟨54171, by rfl⟩ : syracuseStep 9245269 = 108343) (by norm_num)
theorem B12327025 : Blo 2163435 12327025 := bstep (se 2 (by rfl) ⟨4622634, by rfl⟩ : syracuseStep 12327025 = 9245269) B9245269
theorem B16436033 : Blo 2163435 16436033 := bstep (se 2 (by rfl) ⟨6163512, by rfl⟩ : syracuseStep 16436033 = 12327025) B12327025
theorem B10957355 : Blo 2163435 10957355 := bstep (se 1 (by rfl) ⟨8218016, by rfl⟩ : syracuseStep 10957355 = 16436033) B16436033
theorem B7304903 : Blo 2163435 7304903 := bstep (se 1 (by rfl) ⟨5478677, by rfl⟩ : syracuseStep 7304903 = 10957355) B10957355
theorem B4869935 : Blo 2163435 4869935 := bstep (se 1 (by rfl) ⟨3652451, by rfl⟩ : syracuseStep 4869935 = 7304903) B7304903
theorem B3246623 : Blo 2163435 3246623 := bstep (se 1 (by rfl) ⟨2434967, by rfl⟩ : syracuseStep 3246623 = 4869935) B4869935
theorem B2164415 : Blo 2163435 2164415 := bstep (se 1 (by rfl) ⟨1623311, by rfl⟩ : syracuseStep 2164415 = 3246623) B3246623
theorem B3246629 : Blo 2163435 3246629 := bbase (se 4 (by rfl) ⟨304371, by rfl⟩ : syracuseStep 3246629 = 608743) (by norm_num)
theorem B2164419 : Blo 2163435 2164419 := bstep (se 1 (by rfl) ⟨1623314, by rfl⟩ : syracuseStep 2164419 = 3246629) B3246629
theorem B2739349 : Blo 2163435 2739349 := bbase (se 6 (by rfl) ⟨64203, by rfl⟩ : syracuseStep 2739349 = 128407) (by norm_num)
theorem B3652465 : Blo 2163435 3652465 := bstep (se 2 (by rfl) ⟨1369674, by rfl⟩ : syracuseStep 3652465 = 2739349) B2739349
theorem B4869953 : Blo 2163435 4869953 := bstep (se 2 (by rfl) ⟨1826232, by rfl⟩ : syracuseStep 4869953 = 3652465) B3652465
theorem B3246635 : Blo 2163435 3246635 := bstep (se 1 (by rfl) ⟨2434976, by rfl⟩ : syracuseStep 3246635 = 4869953) B4869953
theorem B2164423 : Blo 2163435 2164423 := bstep (se 1 (by rfl) ⟨1623317, by rfl⟩ : syracuseStep 2164423 = 3246635) B3246635
theorem B2434981 : Blo 2163435 2434981 := bbase (se 4 (by rfl) ⟨228279, by rfl⟩ : syracuseStep 2434981 = 456559) (by norm_num)
theorem B3246641 : Blo 2163435 3246641 := bstep (se 2 (by rfl) ⟨1217490, by rfl⟩ : syracuseStep 3246641 = 2434981) B2434981
theorem B2164427 : Blo 2163435 2164427 := bstep (se 1 (by rfl) ⟨1623320, by rfl⟩ : syracuseStep 2164427 = 3246641) B3246641
theorem B4759597 : Blo 2163435 4759597 := bbase (se 3 (by rfl) ⟨892424, by rfl⟩ : syracuseStep 4759597 = 1784849) (by norm_num)
theorem B6346129 : Blo 2163435 6346129 := bstep (se 2 (by rfl) ⟨2379798, by rfl⟩ : syracuseStep 6346129 = 4759597) B4759597
theorem B8461505 : Blo 2163435 8461505 := bstep (se 2 (by rfl) ⟨3173064, by rfl⟩ : syracuseStep 8461505 = 6346129) B6346129
theorem B22564013 : Blo 2163435 22564013 := bstep (se 3 (by rfl) ⟨4230752, by rfl⟩ : syracuseStep 22564013 = 8461505) B8461505
theorem B60170701 : Blo 2163435 60170701 := bstep (se 3 (by rfl) ⟨11282006, by rfl⟩ : syracuseStep 60170701 = 22564013) B22564013
theorem B80227601 : Blo 2163435 80227601 := bstep (se 2 (by rfl) ⟨30085350, by rfl⟩ : syracuseStep 80227601 = 60170701) B60170701
theorem B53485067 : Blo 2163435 53485067 := bstep (se 1 (by rfl) ⟨40113800, by rfl⟩ : syracuseStep 53485067 = 80227601) B80227601
theorem B142626845 : Blo 2163435 142626845 := bstep (se 3 (by rfl) ⟨26742533, by rfl⟩ : syracuseStep 142626845 = 53485067) B53485067
theorem B380338253 : Blo 2163435 380338253 := bstep (se 3 (by rfl) ⟨71313422, by rfl⟩ : syracuseStep 380338253 = 142626845) B142626845
theorem B253558835 : Blo 2163435 253558835 := bstep (se 1 (by rfl) ⟨190169126, by rfl⟩ : syracuseStep 253558835 = 380338253) B380338253
theorem B169039223 : Blo 2163435 169039223 := bstep (se 1 (by rfl) ⟨126779417, by rfl⟩ : syracuseStep 169039223 = 253558835) B253558835
theorem B112692815 : Blo 2163435 112692815 := bstep (se 1 (by rfl) ⟨84519611, by rfl⟩ : syracuseStep 112692815 = 169039223) B169039223
theorem B75128543 : Blo 2163435 75128543 := bstep (se 1 (by rfl) ⟨56346407, by rfl⟩ : syracuseStep 75128543 = 112692815) B112692815
theorem B50085695 : Blo 2163435 50085695 := bstep (se 1 (by rfl) ⟨37564271, by rfl⟩ : syracuseStep 50085695 = 75128543) B75128543
theorem B33390463 : Blo 2163435 33390463 := bstep (se 1 (by rfl) ⟨25042847, by rfl⟩ : syracuseStep 33390463 = 50085695) B50085695
theorem B44520617 : Blo 2163435 44520617 := bstep (se 2 (by rfl) ⟨16695231, by rfl⟩ : syracuseStep 44520617 = 33390463) B33390463
theorem B29680411 : Blo 2163435 29680411 := bstep (se 1 (by rfl) ⟨22260308, by rfl⟩ : syracuseStep 29680411 = 44520617) B44520617
theorem B39573881 : Blo 2163435 39573881 := bstep (se 2 (by rfl) ⟨14840205, by rfl⟩ : syracuseStep 39573881 = 29680411) B29680411
theorem B26382587 : Blo 2163435 26382587 := bstep (se 1 (by rfl) ⟨19786940, by rfl⟩ : syracuseStep 26382587 = 39573881) B39573881
theorem B281414261 : Blo 2163435 281414261 := bstep (se 5 (by rfl) ⟨13191293, by rfl⟩ : syracuseStep 281414261 = 26382587) B26382587
theorem B187609507 : Blo 2163435 187609507 := bstep (se 1 (by rfl) ⟨140707130, by rfl⟩ : syracuseStep 187609507 = 281414261) B281414261
theorem B1000584037 : Blo 2163435 1000584037 := bstep (se 4 (by rfl) ⟨93804753, by rfl⟩ : syracuseStep 1000584037 = 187609507) B187609507
theorem B1334112049 : Blo 2163435 1334112049 := bstep (se 2 (by rfl) ⟨500292018, by rfl⟩ : syracuseStep 1334112049 = 1000584037) B1000584037
theorem B1778816065 : Blo 2163435 1778816065 := bstep (se 2 (by rfl) ⟨667056024, by rfl⟩ : syracuseStep 1778816065 = 1334112049) B1334112049
theorem B2371754753 : Blo 2163435 2371754753 := bstep (se 2 (by rfl) ⟨889408032, by rfl⟩ : syracuseStep 2371754753 = 1778816065) B1778816065
theorem B1581169835 : Blo 2163435 1581169835 := bstep (se 1 (by rfl) ⟨1185877376, by rfl⟩ : syracuseStep 1581169835 = 2371754753) B2371754753
theorem B4216452893 : Blo 2163435 4216452893 := bstep (se 3 (by rfl) ⟨790584917, by rfl⟩ : syracuseStep 4216452893 = 1581169835) B1581169835
theorem B2810968595 : Blo 2163435 2810968595 := bstep (se 1 (by rfl) ⟨2108226446, by rfl⟩ : syracuseStep 2810968595 = 4216452893) B4216452893
theorem B1873979063 : Blo 2163435 1873979063 := bstep (se 1 (by rfl) ⟨1405484297, by rfl⟩ : syracuseStep 1873979063 = 2810968595) B2810968595
theorem B1249319375 : Blo 2163435 1249319375 := bstep (se 1 (by rfl) ⟨936989531, by rfl⟩ : syracuseStep 1249319375 = 1873979063) B1873979063
theorem B832879583 : Blo 2163435 832879583 := bstep (se 1 (by rfl) ⟨624659687, by rfl⟩ : syracuseStep 832879583 = 1249319375) B1249319375
theorem B555253055 : Blo 2163435 555253055 := bstep (se 1 (by rfl) ⟨416439791, by rfl⟩ : syracuseStep 555253055 = 832879583) B832879583
theorem B370168703 : Blo 2163435 370168703 := bstep (se 1 (by rfl) ⟨277626527, by rfl⟩ : syracuseStep 370168703 = 555253055) B555253055
theorem B246779135 : Blo 2163435 246779135 := bstep (se 1 (by rfl) ⟨185084351, by rfl⟩ : syracuseStep 246779135 = 370168703) B370168703
theorem B164519423 : Blo 2163435 164519423 := bstep (se 1 (by rfl) ⟨123389567, by rfl⟩ : syracuseStep 164519423 = 246779135) B246779135
theorem B109679615 : Blo 2163435 109679615 := bstep (se 1 (by rfl) ⟨82259711, by rfl⟩ : syracuseStep 109679615 = 164519423) B164519423
theorem B73119743 : Blo 2163435 73119743 := bstep (se 1 (by rfl) ⟨54839807, by rfl⟩ : syracuseStep 73119743 = 109679615) B109679615
theorem B48746495 : Blo 2163435 48746495 := bstep (se 1 (by rfl) ⟨36559871, by rfl⟩ : syracuseStep 48746495 = 73119743) B73119743
theorem B129990653 : Blo 2163435 129990653 := bstep (se 3 (by rfl) ⟨24373247, by rfl⟩ : syracuseStep 129990653 = 48746495) B48746495
theorem B86660435 : Blo 2163435 86660435 := bstep (se 1 (by rfl) ⟨64995326, by rfl⟩ : syracuseStep 86660435 = 129990653) B129990653
theorem B57773623 : Blo 2163435 57773623 := bstep (se 1 (by rfl) ⟨43330217, by rfl⟩ : syracuseStep 57773623 = 86660435) B86660435
theorem B77031497 : Blo 2163435 77031497 := bstep (se 2 (by rfl) ⟨28886811, by rfl⟩ : syracuseStep 77031497 = 57773623) B57773623
theorem B51354331 : Blo 2163435 51354331 := bstep (se 1 (by rfl) ⟨38515748, by rfl⟩ : syracuseStep 51354331 = 77031497) B77031497
theorem B273889765 : Blo 2163435 273889765 := bstep (se 4 (by rfl) ⟨25677165, by rfl⟩ : syracuseStep 273889765 = 51354331) B51354331
theorem B365186353 : Blo 2163435 365186353 := bstep (se 2 (by rfl) ⟨136944882, by rfl⟩ : syracuseStep 365186353 = 273889765) B273889765
theorem B486915137 : Blo 2163435 486915137 := bstep (se 2 (by rfl) ⟨182593176, by rfl⟩ : syracuseStep 486915137 = 365186353) B365186353
theorem B324610091 : Blo 2163435 324610091 := bstep (se 1 (by rfl) ⟨243457568, by rfl⟩ : syracuseStep 324610091 = 486915137) B486915137
theorem B216406727 : Blo 2163435 216406727 := bstep (se 1 (by rfl) ⟨162305045, by rfl⟩ : syracuseStep 216406727 = 324610091) B324610091
theorem B144271151 : Blo 2163435 144271151 := bstep (se 1 (by rfl) ⟨108203363, by rfl⟩ : syracuseStep 144271151 = 216406727) B216406727
theorem B96180767 : Blo 2163435 96180767 := bstep (se 1 (by rfl) ⟨72135575, by rfl⟩ : syracuseStep 96180767 = 144271151) B144271151
theorem B64120511 : Blo 2163435 64120511 := bstep (se 1 (by rfl) ⟨48090383, by rfl⟩ : syracuseStep 64120511 = 96180767) B96180767
theorem B42747007 : Blo 2163435 42747007 := bstep (se 1 (by rfl) ⟨32060255, by rfl⟩ : syracuseStep 42747007 = 64120511) B64120511
theorem B56996009 : Blo 2163435 56996009 := bstep (se 2 (by rfl) ⟨21373503, by rfl⟩ : syracuseStep 56996009 = 42747007) B42747007
theorem B607957429 : Blo 2163435 607957429 := bstep (se 5 (by rfl) ⟨28498004, by rfl⟩ : syracuseStep 607957429 = 56996009) B56996009
theorem B810609905 : Blo 2163435 810609905 := bstep (se 2 (by rfl) ⟨303978714, by rfl⟩ : syracuseStep 810609905 = 607957429) B607957429
theorem B540406603 : Blo 2163435 540406603 := bstep (se 1 (by rfl) ⟨405304952, by rfl⟩ : syracuseStep 540406603 = 810609905) B810609905
theorem B720542137 : Blo 2163435 720542137 := bstep (se 2 (by rfl) ⟨270203301, by rfl⟩ : syracuseStep 720542137 = 540406603) B540406603
theorem B960722849 : Blo 2163435 960722849 := bstep (se 2 (by rfl) ⟨360271068, by rfl⟩ : syracuseStep 960722849 = 720542137) B720542137
theorem B640481899 : Blo 2163435 640481899 := bstep (se 1 (by rfl) ⟨480361424, by rfl⟩ : syracuseStep 640481899 = 960722849) B960722849
theorem B853975865 : Blo 2163435 853975865 := bstep (se 2 (by rfl) ⟨320240949, by rfl⟩ : syracuseStep 853975865 = 640481899) B640481899
theorem B569317243 : Blo 2163435 569317243 := bstep (se 1 (by rfl) ⟨426987932, by rfl⟩ : syracuseStep 569317243 = 853975865) B853975865
theorem B759089657 : Blo 2163435 759089657 := bstep (se 2 (by rfl) ⟨284658621, by rfl⟩ : syracuseStep 759089657 = 569317243) B569317243
theorem B506059771 : Blo 2163435 506059771 := bstep (se 1 (by rfl) ⟨379544828, by rfl⟩ : syracuseStep 506059771 = 759089657) B759089657
theorem B674746361 : Blo 2163435 674746361 := bstep (se 2 (by rfl) ⟨253029885, by rfl⟩ : syracuseStep 674746361 = 506059771) B506059771
theorem B449830907 : Blo 2163435 449830907 := bstep (se 1 (by rfl) ⟨337373180, by rfl⟩ : syracuseStep 449830907 = 674746361) B674746361
theorem B299887271 : Blo 2163435 299887271 := bstep (se 1 (by rfl) ⟨224915453, by rfl⟩ : syracuseStep 299887271 = 449830907) B449830907
theorem B199924847 : Blo 2163435 199924847 := bstep (se 1 (by rfl) ⟨149943635, by rfl⟩ : syracuseStep 199924847 = 299887271) B299887271
theorem B133283231 : Blo 2163435 133283231 := bstep (se 1 (by rfl) ⟨99962423, by rfl⟩ : syracuseStep 133283231 = 199924847) B199924847
theorem B88855487 : Blo 2163435 88855487 := bstep (se 1 (by rfl) ⟨66641615, by rfl⟩ : syracuseStep 88855487 = 133283231) B133283231
theorem B59236991 : Blo 2163435 59236991 := bstep (se 1 (by rfl) ⟨44427743, by rfl⟩ : syracuseStep 59236991 = 88855487) B88855487
theorem B39491327 : Blo 2163435 39491327 := bstep (se 1 (by rfl) ⟨29618495, by rfl⟩ : syracuseStep 39491327 = 59236991) B59236991
theorem B26327551 : Blo 2163435 26327551 := bstep (se 1 (by rfl) ⟨19745663, by rfl⟩ : syracuseStep 26327551 = 39491327) B39491327
theorem B35103401 : Blo 2163435 35103401 := bstep (se 2 (by rfl) ⟨13163775, by rfl⟩ : syracuseStep 35103401 = 26327551) B26327551
theorem B23402267 : Blo 2163435 23402267 := bstep (se 1 (by rfl) ⟨17551700, by rfl⟩ : syracuseStep 23402267 = 35103401) B35103401
theorem B15601511 : Blo 2163435 15601511 := bstep (se 1 (by rfl) ⟨11701133, by rfl⟩ : syracuseStep 15601511 = 23402267) B23402267
theorem B10401007 : Blo 2163435 10401007 := bstep (se 1 (by rfl) ⟨7800755, by rfl⟩ : syracuseStep 10401007 = 15601511) B15601511
theorem B13868009 : Blo 2163435 13868009 := bstep (se 2 (by rfl) ⟨5200503, by rfl⟩ : syracuseStep 13868009 = 10401007) B10401007
theorem B9245339 : Blo 2163435 9245339 := bstep (se 1 (by rfl) ⟨6934004, by rfl⟩ : syracuseStep 9245339 = 13868009) B13868009
theorem B6163559 : Blo 2163435 6163559 := bstep (se 1 (by rfl) ⟨4622669, by rfl⟩ : syracuseStep 6163559 = 9245339) B9245339
theorem B4109039 : Blo 2163435 4109039 := bstep (se 1 (by rfl) ⟨3081779, by rfl⟩ : syracuseStep 4109039 = 6163559) B6163559
theorem B2739359 : Blo 2163435 2739359 := bstep (se 1 (by rfl) ⟨2054519, by rfl⟩ : syracuseStep 2739359 = 4109039) B4109039
theorem B7304957 : Blo 2163435 7304957 := bstep (se 3 (by rfl) ⟨1369679, by rfl⟩ : syracuseStep 7304957 = 2739359) B2739359
theorem B4869971 : Blo 2163435 4869971 := bstep (se 1 (by rfl) ⟨3652478, by rfl⟩ : syracuseStep 4869971 = 7304957) B7304957
theorem B3246647 : Blo 2163435 3246647 := bstep (se 1 (by rfl) ⟨2434985, by rfl⟩ : syracuseStep 3246647 = 4869971) B4869971
theorem B2164431 : Blo 2163435 2164431 := bstep (se 1 (by rfl) ⟨1623323, by rfl⟩ : syracuseStep 2164431 = 3246647) B3246647
theorem B3246653 : Blo 2163435 3246653 := bbase (se 3 (by rfl) ⟨608747, by rfl⟩ : syracuseStep 3246653 = 1217495) (by norm_num)
theorem B2164435 : Blo 2163435 2164435 := bstep (se 1 (by rfl) ⟨1623326, by rfl⟩ : syracuseStep 2164435 = 3246653) B3246653
theorem B4869989 : Blo 2163435 4869989 := bbase (se 4 (by rfl) ⟨456561, by rfl⟩ : syracuseStep 4869989 = 913123) (by norm_num)
theorem B3246659 : Blo 2163435 3246659 := bstep (se 1 (by rfl) ⟨2434994, by rfl⟩ : syracuseStep 3246659 = 4869989) B4869989
theorem B2164439 : Blo 2163435 2164439 := bstep (se 1 (by rfl) ⟨1623329, by rfl⟩ : syracuseStep 2164439 = 3246659) B3246659
theorem B5478749 : Blo 2163435 5478749 := bbase (se 3 (by rfl) ⟨1027265, by rfl⟩ : syracuseStep 5478749 = 2054531) (by norm_num)
theorem B3652499 : Blo 2163435 3652499 := bstep (se 1 (by rfl) ⟨2739374, by rfl⟩ : syracuseStep 3652499 = 5478749) B5478749
theorem B2434999 : Blo 2163435 2434999 := bstep (se 1 (by rfl) ⟨1826249, by rfl⟩ : syracuseStep 2434999 = 3652499) B3652499
theorem B3246665 : Blo 2163435 3246665 := bstep (se 2 (by rfl) ⟨1217499, by rfl⟩ : syracuseStep 3246665 = 2434999) B2434999
theorem B2164443 : Blo 2163435 2164443 := bstep (se 1 (by rfl) ⟨1623332, by rfl⟩ : syracuseStep 2164443 = 3246665) B3246665
theorem B4109069 : Blo 2163435 4109069 := bbase (se 3 (by rfl) ⟨770450, by rfl⟩ : syracuseStep 4109069 = 1540901) (by norm_num)
theorem B10957517 : Blo 2163435 10957517 := bstep (se 3 (by rfl) ⟨2054534, by rfl⟩ : syracuseStep 10957517 = 4109069) B4109069
theorem B7305011 : Blo 2163435 7305011 := bstep (se 1 (by rfl) ⟨5478758, by rfl⟩ : syracuseStep 7305011 = 10957517) B10957517
theorem B4870007 : Blo 2163435 4870007 := bstep (se 1 (by rfl) ⟨3652505, by rfl⟩ : syracuseStep 4870007 = 7305011) B7305011
theorem B3246671 : Blo 2163435 3246671 := bstep (se 1 (by rfl) ⟨2435003, by rfl⟩ : syracuseStep 3246671 = 4870007) B4870007
theorem B2164447 : Blo 2163435 2164447 := bstep (se 1 (by rfl) ⟨1623335, by rfl⟩ : syracuseStep 2164447 = 3246671) B3246671
theorem B3246677 : Blo 2163435 3246677 := bbase (se 8 (by rfl) ⟨19023, by rfl⟩ : syracuseStep 3246677 = 38047) (by norm_num)
theorem B2164451 : Blo 2163435 2164451 := bstep (se 1 (by rfl) ⟨1623338, by rfl⟩ : syracuseStep 2164451 = 3246677) B3246677
theorem B3900421 : Blo 2163435 3900421 := bbase (se 4 (by rfl) ⟨365664, by rfl⟩ : syracuseStep 3900421 = 731329) (by norm_num)
theorem B5200561 : Blo 2163435 5200561 := bstep (se 2 (by rfl) ⟨1950210, by rfl⟩ : syracuseStep 5200561 = 3900421) B3900421
theorem B6934081 : Blo 2163435 6934081 := bstep (se 2 (by rfl) ⟨2600280, by rfl⟩ : syracuseStep 6934081 = 5200561) B5200561
theorem B9245441 : Blo 2163435 9245441 := bstep (se 2 (by rfl) ⟨3467040, by rfl⟩ : syracuseStep 9245441 = 6934081) B6934081
theorem B6163627 : Blo 2163435 6163627 := bstep (se 1 (by rfl) ⟨4622720, by rfl⟩ : syracuseStep 6163627 = 9245441) B9245441
theorem B8218169 : Blo 2163435 8218169 := bstep (se 2 (by rfl) ⟨3081813, by rfl⟩ : syracuseStep 8218169 = 6163627) B6163627
theorem B5478779 : Blo 2163435 5478779 := bstep (se 1 (by rfl) ⟨4109084, by rfl⟩ : syracuseStep 5478779 = 8218169) B8218169
theorem B3652519 : Blo 2163435 3652519 := bstep (se 1 (by rfl) ⟨2739389, by rfl⟩ : syracuseStep 3652519 = 5478779) B5478779
theorem B4870025 : Blo 2163435 4870025 := bstep (se 2 (by rfl) ⟨1826259, by rfl⟩ : syracuseStep 4870025 = 3652519) B3652519
theorem B3246683 : Blo 2163435 3246683 := bstep (se 1 (by rfl) ⟨2435012, by rfl⟩ : syracuseStep 3246683 = 4870025) B4870025
theorem B2164455 : Blo 2163435 2164455 := bstep (se 1 (by rfl) ⟨1623341, by rfl⟩ : syracuseStep 2164455 = 3246683) B3246683
theorem B2435017 : Blo 2163435 2435017 := bbase (se 2 (by rfl) ⟨913131, by rfl⟩ : syracuseStep 2435017 = 1826263) (by norm_num)
theorem B3246689 : Blo 2163435 3246689 := bstep (se 2 (by rfl) ⟨1217508, by rfl⟩ : syracuseStep 3246689 = 2435017) B2435017
theorem B2164459 : Blo 2163435 2164459 := bstep (se 1 (by rfl) ⟨1623344, by rfl⟩ : syracuseStep 2164459 = 3246689) B3246689
theorem B3467053 : Blo 2163435 3467053 := bbase (se 3 (by rfl) ⟨650072, by rfl⟩ : syracuseStep 3467053 = 1300145) (by norm_num)
theorem B18490949 : Blo 2163435 18490949 := bstep (se 4 (by rfl) ⟨1733526, by rfl⟩ : syracuseStep 18490949 = 3467053) B3467053
theorem B12327299 : Blo 2163435 12327299 := bstep (se 1 (by rfl) ⟨9245474, by rfl⟩ : syracuseStep 12327299 = 18490949) B18490949
theorem B8218199 : Blo 2163435 8218199 := bstep (se 1 (by rfl) ⟨6163649, by rfl⟩ : syracuseStep 8218199 = 12327299) B12327299
theorem B5478799 : Blo 2163435 5478799 := bstep (se 1 (by rfl) ⟨4109099, by rfl⟩ : syracuseStep 5478799 = 8218199) B8218199
theorem B7305065 : Blo 2163435 7305065 := bstep (se 2 (by rfl) ⟨2739399, by rfl⟩ : syracuseStep 7305065 = 5478799) B5478799
theorem B4870043 : Blo 2163435 4870043 := bstep (se 1 (by rfl) ⟨3652532, by rfl⟩ : syracuseStep 4870043 = 7305065) B7305065
theorem B3246695 : Blo 2163435 3246695 := bstep (se 1 (by rfl) ⟨2435021, by rfl⟩ : syracuseStep 3246695 = 4870043) B4870043
theorem B2164463 : Blo 2163435 2164463 := bstep (se 1 (by rfl) ⟨1623347, by rfl⟩ : syracuseStep 2164463 = 3246695) B3246695
theorem B3246701 : Blo 2163435 3246701 := bbase (se 3 (by rfl) ⟨608756, by rfl⟩ : syracuseStep 3246701 = 1217513) (by norm_num)
theorem B2164467 : Blo 2163435 2164467 := bstep (se 1 (by rfl) ⟨1623350, by rfl⟩ : syracuseStep 2164467 = 3246701) B3246701
theorem B4870061 : Blo 2163435 4870061 := bbase (se 3 (by rfl) ⟨913136, by rfl⟩ : syracuseStep 4870061 = 1826273) (by norm_num)
theorem B3246707 : Blo 2163435 3246707 := bstep (se 1 (by rfl) ⟨2435030, by rfl⟩ : syracuseStep 3246707 = 4870061) B4870061
theorem B2164471 : Blo 2163435 2164471 := bstep (se 1 (by rfl) ⟨1623353, by rfl⟩ : syracuseStep 2164471 = 3246707) B3246707
theorem B6163685 : Blo 2163435 6163685 := bbase (se 4 (by rfl) ⟨577845, by rfl⟩ : syracuseStep 6163685 = 1155691) (by norm_num)
theorem B4109123 : Blo 2163435 4109123 := bstep (se 1 (by rfl) ⟨3081842, by rfl⟩ : syracuseStep 4109123 = 6163685) B6163685
theorem B2739415 : Blo 2163435 2739415 := bstep (se 1 (by rfl) ⟨2054561, by rfl⟩ : syracuseStep 2739415 = 4109123) B4109123
theorem B3652553 : Blo 2163435 3652553 := bstep (se 2 (by rfl) ⟨1369707, by rfl⟩ : syracuseStep 3652553 = 2739415) B2739415
theorem B2435035 : Blo 2163435 2435035 := bstep (se 1 (by rfl) ⟨1826276, by rfl⟩ : syracuseStep 2435035 = 3652553) B3652553
theorem B3246713 : Blo 2163435 3246713 := bstep (se 2 (by rfl) ⟨1217517, by rfl⟩ : syracuseStep 3246713 = 2435035) B2435035
theorem B2164475 : Blo 2163435 2164475 := bstep (se 1 (by rfl) ⟨1623356, by rfl⟩ : syracuseStep 2164475 = 3246713) B3246713
theorem B2965261 : Blo 2163435 2965261 := bbase (se 3 (by rfl) ⟨555986, by rfl⟩ : syracuseStep 2965261 = 1111973) (by norm_num)
theorem B3953681 : Blo 2163435 3953681 := bstep (se 2 (by rfl) ⟨1482630, by rfl⟩ : syracuseStep 3953681 = 2965261) B2965261
theorem B2635787 : Blo 2163435 2635787 := bstep (se 1 (by rfl) ⟨1976840, by rfl⟩ : syracuseStep 2635787 = 3953681) B3953681
theorem B7028765 : Blo 2163435 7028765 := bstep (se 3 (by rfl) ⟨1317893, by rfl⟩ : syracuseStep 7028765 = 2635787) B2635787
theorem B4685843 : Blo 2163435 4685843 := bstep (se 1 (by rfl) ⟨3514382, by rfl⟩ : syracuseStep 4685843 = 7028765) B7028765
theorem B3123895 : Blo 2163435 3123895 := bstep (se 1 (by rfl) ⟨2342921, by rfl⟩ : syracuseStep 3123895 = 4685843) B4685843
theorem B4165193 : Blo 2163435 4165193 := bstep (se 2 (by rfl) ⟨1561947, by rfl⟩ : syracuseStep 4165193 = 3123895) B3123895
theorem B11107181 : Blo 2163435 11107181 := bstep (se 3 (by rfl) ⟨2082596, by rfl⟩ : syracuseStep 11107181 = 4165193) B4165193
theorem B7404787 : Blo 2163435 7404787 := bstep (se 1 (by rfl) ⟨5553590, by rfl⟩ : syracuseStep 7404787 = 11107181) B11107181
theorem B9873049 : Blo 2163435 9873049 := bstep (se 2 (by rfl) ⟨3702393, by rfl⟩ : syracuseStep 9873049 = 7404787) B7404787
theorem B13164065 : Blo 2163435 13164065 := bstep (se 2 (by rfl) ⟨4936524, by rfl⟩ : syracuseStep 13164065 = 9873049) B9873049
theorem B8776043 : Blo 2163435 8776043 := bstep (se 1 (by rfl) ⟨6582032, by rfl⟩ : syracuseStep 8776043 = 13164065) B13164065
theorem B5850695 : Blo 2163435 5850695 := bstep (se 1 (by rfl) ⟨4388021, by rfl⟩ : syracuseStep 5850695 = 8776043) B8776043
theorem B15601853 : Blo 2163435 15601853 := bstep (se 3 (by rfl) ⟨2925347, by rfl⟩ : syracuseStep 15601853 = 5850695) B5850695
theorem B41604941 : Blo 2163435 41604941 := bstep (se 3 (by rfl) ⟨7800926, by rfl⟩ : syracuseStep 41604941 = 15601853) B15601853
theorem B27736627 : Blo 2163435 27736627 := bstep (se 1 (by rfl) ⟨20802470, by rfl⟩ : syracuseStep 27736627 = 41604941) B41604941
theorem B36982169 : Blo 2163435 36982169 := bstep (se 2 (by rfl) ⟨13868313, by rfl⟩ : syracuseStep 36982169 = 27736627) B27736627
theorem B24654779 : Blo 2163435 24654779 := bstep (se 1 (by rfl) ⟨18491084, by rfl⟩ : syracuseStep 24654779 = 36982169) B36982169
theorem B16436519 : Blo 2163435 16436519 := bstep (se 1 (by rfl) ⟨12327389, by rfl⟩ : syracuseStep 16436519 = 24654779) B24654779
theorem B10957679 : Blo 2163435 10957679 := bstep (se 1 (by rfl) ⟨8218259, by rfl⟩ : syracuseStep 10957679 = 16436519) B16436519
theorem B7305119 : Blo 2163435 7305119 := bstep (se 1 (by rfl) ⟨5478839, by rfl⟩ : syracuseStep 7305119 = 10957679) B10957679
theorem B4870079 : Blo 2163435 4870079 := bstep (se 1 (by rfl) ⟨3652559, by rfl⟩ : syracuseStep 4870079 = 7305119) B7305119
theorem B3246719 : Blo 2163435 3246719 := bstep (se 1 (by rfl) ⟨2435039, by rfl⟩ : syracuseStep 3246719 = 4870079) B4870079
theorem B2164479 : Blo 2163435 2164479 := bstep (se 1 (by rfl) ⟨1623359, by rfl⟩ : syracuseStep 2164479 = 3246719) B3246719
theorem B3246725 : Blo 2163435 3246725 := bbase (se 4 (by rfl) ⟨304380, by rfl⟩ : syracuseStep 3246725 = 608761) (by norm_num)
theorem B2164483 : Blo 2163435 2164483 := bstep (se 1 (by rfl) ⟨1623362, by rfl⟩ : syracuseStep 2164483 = 3246725) B3246725
theorem B3652573 : Blo 2163435 3652573 := bbase (se 3 (by rfl) ⟨684857, by rfl⟩ : syracuseStep 3652573 = 1369715) (by norm_num)
theorem B4870097 : Blo 2163435 4870097 := bstep (se 2 (by rfl) ⟨1826286, by rfl⟩ : syracuseStep 4870097 = 3652573) B3652573
theorem B3246731 : Blo 2163435 3246731 := bstep (se 1 (by rfl) ⟨2435048, by rfl⟩ : syracuseStep 3246731 = 4870097) B4870097
theorem B2164487 : Blo 2163435 2164487 := bstep (se 1 (by rfl) ⟨1623365, by rfl⟩ : syracuseStep 2164487 = 3246731) B3246731
theorem B2435053 : Blo 2163435 2435053 := bbase (se 3 (by rfl) ⟨456572, by rfl⟩ : syracuseStep 2435053 = 913145) (by norm_num)
theorem B3246737 : Blo 2163435 3246737 := bstep (se 2 (by rfl) ⟨1217526, by rfl⟩ : syracuseStep 3246737 = 2435053) B2435053
theorem B2164491 : Blo 2163435 2164491 := bstep (se 1 (by rfl) ⟨1623368, by rfl⟩ : syracuseStep 2164491 = 3246737) B3246737
theorem B7305173 : Blo 2163435 7305173 := bbase (se 7 (by rfl) ⟨85607, by rfl⟩ : syracuseStep 7305173 = 171215) (by norm_num)
theorem B4870115 : Blo 2163435 4870115 := bstep (se 1 (by rfl) ⟨3652586, by rfl⟩ : syracuseStep 4870115 = 7305173) B7305173
theorem B3246743 : Blo 2163435 3246743 := bstep (se 1 (by rfl) ⟨2435057, by rfl⟩ : syracuseStep 3246743 = 4870115) B4870115
theorem B2164495 : Blo 2163435 2164495 := bstep (se 1 (by rfl) ⟨1623371, by rfl⟩ : syracuseStep 2164495 = 3246743) B3246743
theorem B3246749 : Blo 2163435 3246749 := bbase (se 3 (by rfl) ⟨608765, by rfl⟩ : syracuseStep 3246749 = 1217531) (by norm_num)
theorem B2164499 : Blo 2163435 2164499 := bstep (se 1 (by rfl) ⟨1623374, by rfl⟩ : syracuseStep 2164499 = 3246749) B3246749
theorem B4870133 : Blo 2163435 4870133 := bbase (se 5 (by rfl) ⟨228287, by rfl⟩ : syracuseStep 4870133 = 456575) (by norm_num)
theorem B3246755 : Blo 2163435 3246755 := bstep (se 1 (by rfl) ⟨2435066, by rfl⟩ : syracuseStep 3246755 = 4870133) B4870133
theorem B2164503 : Blo 2163435 2164503 := bstep (se 1 (by rfl) ⟨1623377, by rfl⟩ : syracuseStep 2164503 = 3246755) B3246755
theorem B5343565 : Blo 2163435 5343565 := bbase (se 3 (by rfl) ⟨1001918, by rfl⟩ : syracuseStep 5343565 = 2003837) (by norm_num)
theorem B7124753 : Blo 2163435 7124753 := bstep (se 2 (by rfl) ⟨2671782, by rfl⟩ : syracuseStep 7124753 = 5343565) B5343565
theorem B18999341 : Blo 2163435 18999341 := bstep (se 3 (by rfl) ⟨3562376, by rfl⟩ : syracuseStep 18999341 = 7124753) B7124753
theorem B12666227 : Blo 2163435 12666227 := bstep (se 1 (by rfl) ⟨9499670, by rfl⟩ : syracuseStep 12666227 = 18999341) B18999341
theorem B33776605 : Blo 2163435 33776605 := bstep (se 3 (by rfl) ⟨6333113, by rfl⟩ : syracuseStep 33776605 = 12666227) B12666227
theorem B180141893 : Blo 2163435 180141893 := bstep (se 4 (by rfl) ⟨16888302, by rfl⟩ : syracuseStep 180141893 = 33776605) B33776605
theorem B120094595 : Blo 2163435 120094595 := bstep (se 1 (by rfl) ⟨90070946, by rfl⟩ : syracuseStep 120094595 = 180141893) B180141893
theorem B80063063 : Blo 2163435 80063063 := bstep (se 1 (by rfl) ⟨60047297, by rfl⟩ : syracuseStep 80063063 = 120094595) B120094595
theorem B53375375 : Blo 2163435 53375375 := bstep (se 1 (by rfl) ⟨40031531, by rfl⟩ : syracuseStep 53375375 = 80063063) B80063063
theorem B35583583 : Blo 2163435 35583583 := bstep (se 1 (by rfl) ⟨26687687, by rfl⟩ : syracuseStep 35583583 = 53375375) B53375375
theorem B47444777 : Blo 2163435 47444777 := bstep (se 2 (by rfl) ⟨17791791, by rfl⟩ : syracuseStep 47444777 = 35583583) B35583583
theorem B31629851 : Blo 2163435 31629851 := bstep (se 1 (by rfl) ⟨23722388, by rfl⟩ : syracuseStep 31629851 = 47444777) B47444777
theorem B21086567 : Blo 2163435 21086567 := bstep (se 1 (by rfl) ⟨15814925, by rfl⟩ : syracuseStep 21086567 = 31629851) B31629851
theorem B14057711 : Blo 2163435 14057711 := bstep (se 1 (by rfl) ⟨10543283, by rfl⟩ : syracuseStep 14057711 = 21086567) B21086567
theorem B9371807 : Blo 2163435 9371807 := bstep (se 1 (by rfl) ⟨7028855, by rfl⟩ : syracuseStep 9371807 = 14057711) B14057711
theorem B6247871 : Blo 2163435 6247871 := bstep (se 1 (by rfl) ⟨4685903, by rfl⟩ : syracuseStep 6247871 = 9371807) B9371807
theorem B4165247 : Blo 2163435 4165247 := bstep (se 1 (by rfl) ⟨3123935, by rfl⟩ : syracuseStep 4165247 = 6247871) B6247871
theorem B11107325 : Blo 2163435 11107325 := bstep (se 3 (by rfl) ⟨2082623, by rfl⟩ : syracuseStep 11107325 = 4165247) B4165247
theorem B7404883 : Blo 2163435 7404883 := bstep (se 1 (by rfl) ⟨5553662, by rfl⟩ : syracuseStep 7404883 = 11107325) B11107325
theorem B157970837 : Blo 2163435 157970837 := bstep (se 6 (by rfl) ⟨3702441, by rfl⟩ : syracuseStep 157970837 = 7404883) B7404883
theorem B105313891 : Blo 2163435 105313891 := bstep (se 1 (by rfl) ⟨78985418, by rfl⟩ : syracuseStep 105313891 = 157970837) B157970837
theorem B140418521 : Blo 2163435 140418521 := bstep (se 2 (by rfl) ⟨52656945, by rfl⟩ : syracuseStep 140418521 = 105313891) B105313891
theorem B93612347 : Blo 2163435 93612347 := bstep (se 1 (by rfl) ⟨70209260, by rfl⟩ : syracuseStep 93612347 = 140418521) B140418521
theorem B62408231 : Blo 2163435 62408231 := bstep (se 1 (by rfl) ⟨46806173, by rfl⟩ : syracuseStep 62408231 = 93612347) B93612347
theorem B41605487 : Blo 2163435 41605487 := bstep (se 1 (by rfl) ⟨31204115, by rfl⟩ : syracuseStep 41605487 = 62408231) B62408231
theorem B27736991 : Blo 2163435 27736991 := bstep (se 1 (by rfl) ⟨20802743, by rfl⟩ : syracuseStep 27736991 = 41605487) B41605487
theorem B18491327 : Blo 2163435 18491327 := bstep (se 1 (by rfl) ⟨13868495, by rfl⟩ : syracuseStep 18491327 = 27736991) B27736991
theorem B12327551 : Blo 2163435 12327551 := bstep (se 1 (by rfl) ⟨9245663, by rfl⟩ : syracuseStep 12327551 = 18491327) B18491327
theorem B8218367 : Blo 2163435 8218367 := bstep (se 1 (by rfl) ⟨6163775, by rfl⟩ : syracuseStep 8218367 = 12327551) B12327551
theorem B5478911 : Blo 2163435 5478911 := bstep (se 1 (by rfl) ⟨4109183, by rfl⟩ : syracuseStep 5478911 = 8218367) B8218367
theorem B3652607 : Blo 2163435 3652607 := bstep (se 1 (by rfl) ⟨2739455, by rfl⟩ : syracuseStep 3652607 = 5478911) B5478911
theorem B2435071 : Blo 2163435 2435071 := bstep (se 1 (by rfl) ⟨1826303, by rfl⟩ : syracuseStep 2435071 = 3652607) B3652607
theorem B3246761 : Blo 2163435 3246761 := bstep (se 2 (by rfl) ⟨1217535, by rfl⟩ : syracuseStep 3246761 = 2435071) B2435071
theorem B2164507 : Blo 2163435 2164507 := bstep (se 1 (by rfl) ⟨1623380, by rfl⟩ : syracuseStep 2164507 = 3246761) B3246761
theorem B3081893 : Blo 2163435 3081893 := bbase (se 4 (by rfl) ⟨288927, by rfl⟩ : syracuseStep 3081893 = 577855) (by norm_num)
theorem B8218381 : Blo 2163435 8218381 := bstep (se 3 (by rfl) ⟨1540946, by rfl⟩ : syracuseStep 8218381 = 3081893) B3081893
theorem B10957841 : Blo 2163435 10957841 := bstep (se 2 (by rfl) ⟨4109190, by rfl⟩ : syracuseStep 10957841 = 8218381) B8218381
theorem B7305227 : Blo 2163435 7305227 := bstep (se 1 (by rfl) ⟨5478920, by rfl⟩ : syracuseStep 7305227 = 10957841) B10957841
theorem B4870151 : Blo 2163435 4870151 := bstep (se 1 (by rfl) ⟨3652613, by rfl⟩ : syracuseStep 4870151 = 7305227) B7305227
theorem B3246767 : Blo 2163435 3246767 := bstep (se 1 (by rfl) ⟨2435075, by rfl⟩ : syracuseStep 3246767 = 4870151) B4870151
theorem B2164511 : Blo 2163435 2164511 := bstep (se 1 (by rfl) ⟨1623383, by rfl⟩ : syracuseStep 2164511 = 3246767) B3246767
theorem B3246773 : Blo 2163435 3246773 := bbase (se 5 (by rfl) ⟨152192, by rfl⟩ : syracuseStep 3246773 = 304385) (by norm_num)
theorem B2164515 : Blo 2163435 2164515 := bstep (se 1 (by rfl) ⟨1623386, by rfl⟩ : syracuseStep 2164515 = 3246773) B3246773
theorem B5478941 : Blo 2163435 5478941 := bbase (se 3 (by rfl) ⟨1027301, by rfl⟩ : syracuseStep 5478941 = 2054603) (by norm_num)
theorem B3652627 : Blo 2163435 3652627 := bstep (se 1 (by rfl) ⟨2739470, by rfl⟩ : syracuseStep 3652627 = 5478941) B5478941
theorem B4870169 : Blo 2163435 4870169 := bstep (se 2 (by rfl) ⟨1826313, by rfl⟩ : syracuseStep 4870169 = 3652627) B3652627
theorem B3246779 : Blo 2163435 3246779 := bstep (se 1 (by rfl) ⟨2435084, by rfl⟩ : syracuseStep 3246779 = 4870169) B4870169
theorem B2164519 : Blo 2163435 2164519 := bstep (se 1 (by rfl) ⟨1623389, by rfl⟩ : syracuseStep 2164519 = 3246779) B3246779
theorem B2435089 : Blo 2163435 2435089 := bbase (se 2 (by rfl) ⟨913158, by rfl⟩ : syracuseStep 2435089 = 1826317) (by norm_num)
theorem B3246785 : Blo 2163435 3246785 := bstep (se 2 (by rfl) ⟨1217544, by rfl⟩ : syracuseStep 3246785 = 2435089) B2435089
theorem B2164523 : Blo 2163435 2164523 := bstep (se 1 (by rfl) ⟨1623392, by rfl⟩ : syracuseStep 2164523 = 3246785) B3246785
theorem B4109221 : Blo 2163435 4109221 := bbase (se 4 (by rfl) ⟨385239, by rfl⟩ : syracuseStep 4109221 = 770479) (by norm_num)
theorem B5478961 : Blo 2163435 5478961 := bstep (se 2 (by rfl) ⟨2054610, by rfl⟩ : syracuseStep 5478961 = 4109221) B4109221
theorem B7305281 : Blo 2163435 7305281 := bstep (se 2 (by rfl) ⟨2739480, by rfl⟩ : syracuseStep 7305281 = 5478961) B5478961
theorem B4870187 : Blo 2163435 4870187 := bstep (se 1 (by rfl) ⟨3652640, by rfl⟩ : syracuseStep 4870187 = 7305281) B7305281
theorem B3246791 : Blo 2163435 3246791 := bstep (se 1 (by rfl) ⟨2435093, by rfl⟩ : syracuseStep 3246791 = 4870187) B4870187
theorem B2164527 : Blo 2163435 2164527 := bstep (se 1 (by rfl) ⟨1623395, by rfl⟩ : syracuseStep 2164527 = 3246791) B3246791
theorem B3246797 : Blo 2163435 3246797 := bbase (se 3 (by rfl) ⟨608774, by rfl⟩ : syracuseStep 3246797 = 1217549) (by norm_num)
theorem B2164531 : Blo 2163435 2164531 := bstep (se 1 (by rfl) ⟨1623398, by rfl⟩ : syracuseStep 2164531 = 3246797) B3246797
theorem B4870205 : Blo 2163435 4870205 := bbase (se 3 (by rfl) ⟨913163, by rfl⟩ : syracuseStep 4870205 = 1826327) (by norm_num)
theorem B3246803 : Blo 2163435 3246803 := bstep (se 1 (by rfl) ⟨2435102, by rfl⟩ : syracuseStep 3246803 = 4870205) B4870205
theorem B2164535 : Blo 2163435 2164535 := bstep (se 1 (by rfl) ⟨1623401, by rfl⟩ : syracuseStep 2164535 = 3246803) B3246803
theorem B3652661 : Blo 2163435 3652661 := bbase (se 5 (by rfl) ⟨171218, by rfl⟩ : syracuseStep 3652661 = 342437) (by norm_num)
theorem B2435107 : Blo 2163435 2435107 := bstep (se 1 (by rfl) ⟨1826330, by rfl⟩ : syracuseStep 2435107 = 3652661) B3652661
theorem B3246809 : Blo 2163435 3246809 := bstep (se 2 (by rfl) ⟨1217553, by rfl⟩ : syracuseStep 3246809 = 2435107) B2435107
theorem B2164539 : Blo 2163435 2164539 := bstep (se 1 (by rfl) ⟨1623404, by rfl⟩ : syracuseStep 2164539 = 3246809) B3246809
theorem B6163877 : Blo 2163435 6163877 := bbase (se 4 (by rfl) ⟨577863, by rfl⟩ : syracuseStep 6163877 = 1155727) (by norm_num)
theorem B16437005 : Blo 2163435 16437005 := bstep (se 3 (by rfl) ⟨3081938, by rfl⟩ : syracuseStep 16437005 = 6163877) B6163877
theorem B10958003 : Blo 2163435 10958003 := bstep (se 1 (by rfl) ⟨8218502, by rfl⟩ : syracuseStep 10958003 = 16437005) B16437005
theorem B7305335 : Blo 2163435 7305335 := bstep (se 1 (by rfl) ⟨5479001, by rfl⟩ : syracuseStep 7305335 = 10958003) B10958003
theorem B4870223 : Blo 2163435 4870223 := bstep (se 1 (by rfl) ⟨3652667, by rfl⟩ : syracuseStep 4870223 = 7305335) B7305335
theorem B3246815 : Blo 2163435 3246815 := bstep (se 1 (by rfl) ⟨2435111, by rfl⟩ : syracuseStep 3246815 = 4870223) B4870223
theorem B2164543 : Blo 2163435 2164543 := bstep (se 1 (by rfl) ⟨1623407, by rfl⟩ : syracuseStep 2164543 = 3246815) B3246815
theorem B3246821 : Blo 2163435 3246821 := bbase (se 4 (by rfl) ⟨304389, by rfl⟩ : syracuseStep 3246821 = 608779) (by norm_num)
theorem B2164547 : Blo 2163435 2164547 := bstep (se 1 (by rfl) ⟨1623410, by rfl⟩ : syracuseStep 2164547 = 3246821) B3246821
theorem B2194085 : Blo 2163435 2194085 := bbase (se 4 (by rfl) ⟨205695, by rfl⟩ : syracuseStep 2194085 = 411391) (by norm_num)
theorem B5850893 : Blo 2163435 5850893 := bstep (se 3 (by rfl) ⟨1097042, by rfl⟩ : syracuseStep 5850893 = 2194085) B2194085
theorem B3900595 : Blo 2163435 3900595 := bstep (se 1 (by rfl) ⟨2925446, by rfl⟩ : syracuseStep 3900595 = 5850893) B5850893
theorem B5200793 : Blo 2163435 5200793 := bstep (se 2 (by rfl) ⟨1950297, by rfl⟩ : syracuseStep 5200793 = 3900595) B3900595
theorem B3467195 : Blo 2163435 3467195 := bstep (se 1 (by rfl) ⟨2600396, by rfl⟩ : syracuseStep 3467195 = 5200793) B5200793
theorem B2311463 : Blo 2163435 2311463 := bstep (se 1 (by rfl) ⟨1733597, by rfl⟩ : syracuseStep 2311463 = 3467195) B3467195
theorem B6163901 : Blo 2163435 6163901 := bstep (se 3 (by rfl) ⟨1155731, by rfl⟩ : syracuseStep 6163901 = 2311463) B2311463
theorem B4109267 : Blo 2163435 4109267 := bstep (se 1 (by rfl) ⟨3081950, by rfl⟩ : syracuseStep 4109267 = 6163901) B6163901
theorem B2739511 : Blo 2163435 2739511 := bstep (se 1 (by rfl) ⟨2054633, by rfl⟩ : syracuseStep 2739511 = 4109267) B4109267
theorem B3652681 : Blo 2163435 3652681 := bstep (se 2 (by rfl) ⟨1369755, by rfl⟩ : syracuseStep 3652681 = 2739511) B2739511
theorem B4870241 : Blo 2163435 4870241 := bstep (se 2 (by rfl) ⟨1826340, by rfl⟩ : syracuseStep 4870241 = 3652681) B3652681
theorem B3246827 : Blo 2163435 3246827 := bstep (se 1 (by rfl) ⟨2435120, by rfl⟩ : syracuseStep 3246827 = 4870241) B4870241
theorem B2164551 : Blo 2163435 2164551 := bstep (se 1 (by rfl) ⟨1623413, by rfl⟩ : syracuseStep 2164551 = 3246827) B3246827
theorem B2435125 : Blo 2163435 2435125 := bbase (se 5 (by rfl) ⟨114146, by rfl⟩ : syracuseStep 2435125 = 228293) (by norm_num)
theorem B3246833 : Blo 2163435 3246833 := bstep (se 2 (by rfl) ⟨1217562, by rfl⟩ : syracuseStep 3246833 = 2435125) B2435125
theorem B2164555 : Blo 2163435 2164555 := bstep (se 1 (by rfl) ⟨1623416, by rfl⟩ : syracuseStep 2164555 = 3246833) B3246833
theorem B2739521 : Blo 2163435 2739521 := bbase (se 2 (by rfl) ⟨1027320, by rfl⟩ : syracuseStep 2739521 = 2054641) (by norm_num)
theorem B7305389 : Blo 2163435 7305389 := bstep (se 3 (by rfl) ⟨1369760, by rfl⟩ : syracuseStep 7305389 = 2739521) B2739521
theorem B4870259 : Blo 2163435 4870259 := bstep (se 1 (by rfl) ⟨3652694, by rfl⟩ : syracuseStep 4870259 = 7305389) B7305389
theorem B3246839 : Blo 2163435 3246839 := bstep (se 1 (by rfl) ⟨2435129, by rfl⟩ : syracuseStep 3246839 = 4870259) B4870259
theorem B2164559 : Blo 2163435 2164559 := bstep (se 1 (by rfl) ⟨1623419, by rfl⟩ : syracuseStep 2164559 = 3246839) B3246839
theorem B3246845 : Blo 2163435 3246845 := bbase (se 3 (by rfl) ⟨608783, by rfl⟩ : syracuseStep 3246845 = 1217567) (by norm_num)
theorem B2164563 : Blo 2163435 2164563 := bstep (se 1 (by rfl) ⟨1623422, by rfl⟩ : syracuseStep 2164563 = 3246845) B3246845
theorem B4870277 : Blo 2163435 4870277 := bbase (se 4 (by rfl) ⟨456588, by rfl⟩ : syracuseStep 4870277 = 913177) (by norm_num)
theorem B3246851 : Blo 2163435 3246851 := bstep (se 1 (by rfl) ⟨2435138, by rfl⟩ : syracuseStep 3246851 = 4870277) B4870277
theorem B2164567 : Blo 2163435 2164567 := bstep (se 1 (by rfl) ⟨1623425, by rfl⟩ : syracuseStep 2164567 = 3246851) B3246851
theorem B8776421 : Blo 2163435 8776421 := bbase (se 4 (by rfl) ⟨822789, by rfl⟩ : syracuseStep 8776421 = 1645579) (by norm_num)
theorem B5850947 : Blo 2163435 5850947 := bstep (se 1 (by rfl) ⟨4388210, by rfl⟩ : syracuseStep 5850947 = 8776421) B8776421
theorem B3900631 : Blo 2163435 3900631 := bstep (se 1 (by rfl) ⟨2925473, by rfl⟩ : syracuseStep 3900631 = 5850947) B5850947
theorem B5200841 : Blo 2163435 5200841 := bstep (se 2 (by rfl) ⟨1950315, by rfl⟩ : syracuseStep 5200841 = 3900631) B3900631
theorem B3467227 : Blo 2163435 3467227 := bstep (se 1 (by rfl) ⟨2600420, by rfl⟩ : syracuseStep 3467227 = 5200841) B5200841
theorem B4622969 : Blo 2163435 4622969 := bstep (se 2 (by rfl) ⟨1733613, by rfl⟩ : syracuseStep 4622969 = 3467227) B3467227
theorem B3081979 : Blo 2163435 3081979 := bstep (se 1 (by rfl) ⟨2311484, by rfl⟩ : syracuseStep 3081979 = 4622969) B4622969
theorem B4109305 : Blo 2163435 4109305 := bstep (se 2 (by rfl) ⟨1540989, by rfl⟩ : syracuseStep 4109305 = 3081979) B3081979
theorem B5479073 : Blo 2163435 5479073 := bstep (se 2 (by rfl) ⟨2054652, by rfl⟩ : syracuseStep 5479073 = 4109305) B4109305
theorem B3652715 : Blo 2163435 3652715 := bstep (se 1 (by rfl) ⟨2739536, by rfl⟩ : syracuseStep 3652715 = 5479073) B5479073
theorem B2435143 : Blo 2163435 2435143 := bstep (se 1 (by rfl) ⟨1826357, by rfl⟩ : syracuseStep 2435143 = 3652715) B3652715
theorem B3246857 : Blo 2163435 3246857 := bstep (se 2 (by rfl) ⟨1217571, by rfl⟩ : syracuseStep 3246857 = 2435143) B2435143
theorem B2164571 : Blo 2163435 2164571 := bstep (se 1 (by rfl) ⟨1623428, by rfl⟩ : syracuseStep 2164571 = 3246857) B3246857
theorem B10958165 : Blo 2163435 10958165 := bbase (se 13 (by rfl) ⟨2006, by rfl⟩ : syracuseStep 10958165 = 4013) (by norm_num)
theorem B7305443 : Blo 2163435 7305443 := bstep (se 1 (by rfl) ⟨5479082, by rfl⟩ : syracuseStep 7305443 = 10958165) B10958165
theorem B4870295 : Blo 2163435 4870295 := bstep (se 1 (by rfl) ⟨3652721, by rfl⟩ : syracuseStep 4870295 = 7305443) B7305443
theorem B3246863 : Blo 2163435 3246863 := bstep (se 1 (by rfl) ⟨2435147, by rfl⟩ : syracuseStep 3246863 = 4870295) B4870295
theorem B2164575 : Blo 2163435 2164575 := bstep (se 1 (by rfl) ⟨1623431, by rfl⟩ : syracuseStep 2164575 = 3246863) B3246863
theorem B3246869 : Blo 2163435 3246869 := bbase (se 6 (by rfl) ⟨76098, by rfl⟩ : syracuseStep 3246869 = 152197) (by norm_num)
theorem B2164579 : Blo 2163435 2164579 := bstep (se 1 (by rfl) ⟨1623434, by rfl⟩ : syracuseStep 2164579 = 3246869) B3246869
theorem B2468381 : Blo 2163435 2468381 := bbase (se 3 (by rfl) ⟨462821, by rfl⟩ : syracuseStep 2468381 = 925643) (by norm_num)
theorem B6582349 : Blo 2163435 6582349 := bstep (se 3 (by rfl) ⟨1234190, by rfl⟩ : syracuseStep 6582349 = 2468381) B2468381
theorem B35105861 : Blo 2163435 35105861 := bstep (se 4 (by rfl) ⟨3291174, by rfl⟩ : syracuseStep 35105861 = 6582349) B6582349
theorem B23403907 : Blo 2163435 23403907 := bstep (se 1 (by rfl) ⟨17552930, by rfl⟩ : syracuseStep 23403907 = 35105861) B35105861
theorem B31205209 : Blo 2163435 31205209 := bstep (se 2 (by rfl) ⟨11701953, by rfl⟩ : syracuseStep 31205209 = 23403907) B23403907
theorem B41606945 : Blo 2163435 41606945 := bstep (se 2 (by rfl) ⟨15602604, by rfl⟩ : syracuseStep 41606945 = 31205209) B31205209
theorem B27737963 : Blo 2163435 27737963 := bstep (se 1 (by rfl) ⟨20803472, by rfl⟩ : syracuseStep 27737963 = 41606945) B41606945
theorem B18491975 : Blo 2163435 18491975 := bstep (se 1 (by rfl) ⟨13868981, by rfl⟩ : syracuseStep 18491975 = 27737963) B27737963
theorem B12327983 : Blo 2163435 12327983 := bstep (se 1 (by rfl) ⟨9245987, by rfl⟩ : syracuseStep 12327983 = 18491975) B18491975
theorem B8218655 : Blo 2163435 8218655 := bstep (se 1 (by rfl) ⟨6163991, by rfl⟩ : syracuseStep 8218655 = 12327983) B12327983
theorem B5479103 : Blo 2163435 5479103 := bstep (se 1 (by rfl) ⟨4109327, by rfl⟩ : syracuseStep 5479103 = 8218655) B8218655
theorem B3652735 : Blo 2163435 3652735 := bstep (se 1 (by rfl) ⟨2739551, by rfl⟩ : syracuseStep 3652735 = 5479103) B5479103
theorem B4870313 : Blo 2163435 4870313 := bstep (se 2 (by rfl) ⟨1826367, by rfl⟩ : syracuseStep 4870313 = 3652735) B3652735
theorem B3246875 : Blo 2163435 3246875 := bstep (se 1 (by rfl) ⟨2435156, by rfl⟩ : syracuseStep 3246875 = 4870313) B4870313
theorem B2164583 : Blo 2163435 2164583 := bstep (se 1 (by rfl) ⟨1623437, by rfl⟩ : syracuseStep 2164583 = 3246875) B3246875
theorem B2435161 : Blo 2163435 2435161 := bbase (se 2 (by rfl) ⟨913185, by rfl⟩ : syracuseStep 2435161 = 1826371) (by norm_num)
theorem B3246881 : Blo 2163435 3246881 := bstep (se 2 (by rfl) ⟨1217580, by rfl⟩ : syracuseStep 3246881 = 2435161) B2435161
theorem B2164587 : Blo 2163435 2164587 := bstep (se 1 (by rfl) ⟨1623440, by rfl⟩ : syracuseStep 2164587 = 3246881) B3246881
theorem B6934517 : Blo 2163435 6934517 := bbase (se 5 (by rfl) ⟨325055, by rfl⟩ : syracuseStep 6934517 = 650111) (by norm_num)
theorem B4623011 : Blo 2163435 4623011 := bstep (se 1 (by rfl) ⟨3467258, by rfl⟩ : syracuseStep 4623011 = 6934517) B6934517
theorem B3082007 : Blo 2163435 3082007 := bstep (se 1 (by rfl) ⟨2311505, by rfl⟩ : syracuseStep 3082007 = 4623011) B4623011
theorem B8218685 : Blo 2163435 8218685 := bstep (se 3 (by rfl) ⟨1541003, by rfl⟩ : syracuseStep 8218685 = 3082007) B3082007
theorem B5479123 : Blo 2163435 5479123 := bstep (se 1 (by rfl) ⟨4109342, by rfl⟩ : syracuseStep 5479123 = 8218685) B8218685
theorem B7305497 : Blo 2163435 7305497 := bstep (se 2 (by rfl) ⟨2739561, by rfl⟩ : syracuseStep 7305497 = 5479123) B5479123
theorem B4870331 : Blo 2163435 4870331 := bstep (se 1 (by rfl) ⟨3652748, by rfl⟩ : syracuseStep 4870331 = 7305497) B7305497
theorem B3246887 : Blo 2163435 3246887 := bstep (se 1 (by rfl) ⟨2435165, by rfl⟩ : syracuseStep 3246887 = 4870331) B4870331
theorem B2164591 : Blo 2163435 2164591 := bstep (se 1 (by rfl) ⟨1623443, by rfl⟩ : syracuseStep 2164591 = 3246887) B3246887
theorem B3246893 : Blo 2163435 3246893 := bbase (se 3 (by rfl) ⟨608792, by rfl⟩ : syracuseStep 3246893 = 1217585) (by norm_num)
theorem B2164595 : Blo 2163435 2164595 := bstep (se 1 (by rfl) ⟨1623446, by rfl⟩ : syracuseStep 2164595 = 3246893) B3246893
theorem B4870349 : Blo 2163435 4870349 := bbase (se 3 (by rfl) ⟨913190, by rfl⟩ : syracuseStep 4870349 = 1826381) (by norm_num)
theorem B3246899 : Blo 2163435 3246899 := bstep (se 1 (by rfl) ⟨2435174, by rfl⟩ : syracuseStep 3246899 = 4870349) B4870349
theorem B2164599 : Blo 2163435 2164599 := bstep (se 1 (by rfl) ⟨1623449, by rfl⟩ : syracuseStep 2164599 = 3246899) B3246899
theorem B2739577 : Blo 2163435 2739577 := bbase (se 2 (by rfl) ⟨1027341, by rfl⟩ : syracuseStep 2739577 = 2054683) (by norm_num)
theorem B3652769 : Blo 2163435 3652769 := bstep (se 2 (by rfl) ⟨1369788, by rfl⟩ : syracuseStep 3652769 = 2739577) B2739577
theorem B2435179 : Blo 2163435 2435179 := bstep (se 1 (by rfl) ⟨1826384, by rfl⟩ : syracuseStep 2435179 = 3652769) B3652769
theorem B3246905 : Blo 2163435 3246905 := bstep (se 2 (by rfl) ⟨1217589, by rfl⟩ : syracuseStep 3246905 = 2435179) B2435179
theorem B2164603 : Blo 2163435 2164603 := bstep (se 1 (by rfl) ⟨1623452, by rfl⟩ : syracuseStep 2164603 = 3246905) B3246905
theorem B3702613 : Blo 2163435 3702613 := bbase (se 9 (by rfl) ⟨10847, by rfl⟩ : syracuseStep 3702613 = 21695) (by norm_num)
theorem B4936817 : Blo 2163435 4936817 := bstep (se 2 (by rfl) ⟨1851306, by rfl⟩ : syracuseStep 4936817 = 3702613) B3702613
theorem B3291211 : Blo 2163435 3291211 := bstep (se 1 (by rfl) ⟨2468408, by rfl⟩ : syracuseStep 3291211 = 4936817) B4936817
theorem B17553125 : Blo 2163435 17553125 := bstep (se 4 (by rfl) ⟨1645605, by rfl⟩ : syracuseStep 17553125 = 3291211) B3291211
theorem B11702083 : Blo 2163435 11702083 := bstep (se 1 (by rfl) ⟨8776562, by rfl⟩ : syracuseStep 11702083 = 17553125) B17553125
theorem B15602777 : Blo 2163435 15602777 := bstep (se 2 (by rfl) ⟨5851041, by rfl⟩ : syracuseStep 15602777 = 11702083) B11702083
theorem B10401851 : Blo 2163435 10401851 := bstep (se 1 (by rfl) ⟨7801388, by rfl⟩ : syracuseStep 10401851 = 15602777) B15602777
theorem B6934567 : Blo 2163435 6934567 := bstep (se 1 (by rfl) ⟨5200925, by rfl⟩ : syracuseStep 6934567 = 10401851) B10401851
theorem B9246089 : Blo 2163435 9246089 := bstep (se 2 (by rfl) ⟨3467283, by rfl⟩ : syracuseStep 9246089 = 6934567) B6934567
theorem B24656237 : Blo 2163435 24656237 := bstep (se 3 (by rfl) ⟨4623044, by rfl⟩ : syracuseStep 24656237 = 9246089) B9246089
theorem B16437491 : Blo 2163435 16437491 := bstep (se 1 (by rfl) ⟨12328118, by rfl⟩ : syracuseStep 16437491 = 24656237) B24656237
theorem B10958327 : Blo 2163435 10958327 := bstep (se 1 (by rfl) ⟨8218745, by rfl⟩ : syracuseStep 10958327 = 16437491) B16437491
theorem B7305551 : Blo 2163435 7305551 := bstep (se 1 (by rfl) ⟨5479163, by rfl⟩ : syracuseStep 7305551 = 10958327) B10958327
theorem B4870367 : Blo 2163435 4870367 := bstep (se 1 (by rfl) ⟨3652775, by rfl⟩ : syracuseStep 4870367 = 7305551) B7305551
theorem B3246911 : Blo 2163435 3246911 := bstep (se 1 (by rfl) ⟨2435183, by rfl⟩ : syracuseStep 3246911 = 4870367) B4870367
theorem B2164607 : Blo 2163435 2164607 := bstep (se 1 (by rfl) ⟨1623455, by rfl⟩ : syracuseStep 2164607 = 3246911) B3246911
theorem B3246917 : Blo 2163435 3246917 := bbase (se 4 (by rfl) ⟨304398, by rfl⟩ : syracuseStep 3246917 = 608797) (by norm_num)
theorem B2164611 : Blo 2163435 2164611 := bstep (se 1 (by rfl) ⟨1623458, by rfl⟩ : syracuseStep 2164611 = 3246917) B3246917
theorem B3652789 : Blo 2163435 3652789 := bbase (se 5 (by rfl) ⟨171224, by rfl⟩ : syracuseStep 3652789 = 342449) (by norm_num)
theorem B4870385 : Blo 2163435 4870385 := bstep (se 2 (by rfl) ⟨1826394, by rfl⟩ : syracuseStep 4870385 = 3652789) B3652789
theorem B3246923 : Blo 2163435 3246923 := bstep (se 1 (by rfl) ⟨2435192, by rfl⟩ : syracuseStep 3246923 = 4870385) B4870385
theorem B2164615 : Blo 2163435 2164615 := bstep (se 1 (by rfl) ⟨1623461, by rfl⟩ : syracuseStep 2164615 = 3246923) B3246923
theorem B2435197 : Blo 2163435 2435197 := bbase (se 3 (by rfl) ⟨456599, by rfl⟩ : syracuseStep 2435197 = 913199) (by norm_num)
theorem B3246929 : Blo 2163435 3246929 := bstep (se 2 (by rfl) ⟨1217598, by rfl⟩ : syracuseStep 3246929 = 2435197) B2435197
theorem B2164619 : Blo 2163435 2164619 := bstep (se 1 (by rfl) ⟨1623464, by rfl⟩ : syracuseStep 2164619 = 3246929) B3246929
theorem B7305605 : Blo 2163435 7305605 := bbase (se 4 (by rfl) ⟨684900, by rfl⟩ : syracuseStep 7305605 = 1369801) (by norm_num)
theorem B4870403 : Blo 2163435 4870403 := bstep (se 1 (by rfl) ⟨3652802, by rfl⟩ : syracuseStep 4870403 = 7305605) B7305605
theorem B3246935 : Blo 2163435 3246935 := bstep (se 1 (by rfl) ⟨2435201, by rfl⟩ : syracuseStep 3246935 = 4870403) B4870403
theorem B2164623 : Blo 2163435 2164623 := bstep (se 1 (by rfl) ⟨1623467, by rfl⟩ : syracuseStep 2164623 = 3246935) B3246935
theorem B3246941 : Blo 2163435 3246941 := bbase (se 3 (by rfl) ⟨608801, by rfl⟩ : syracuseStep 3246941 = 1217603) (by norm_num)
theorem B2164627 : Blo 2163435 2164627 := bstep (se 1 (by rfl) ⟨1623470, by rfl⟩ : syracuseStep 2164627 = 3246941) B3246941
theorem B4870421 : Blo 2163435 4870421 := bbase (se 6 (by rfl) ⟨114150, by rfl⟩ : syracuseStep 4870421 = 228301) (by norm_num)
theorem B3246947 : Blo 2163435 3246947 := bstep (se 1 (by rfl) ⟨2435210, by rfl⟩ : syracuseStep 3246947 = 4870421) B4870421
theorem B2164631 : Blo 2163435 2164631 := bstep (se 1 (by rfl) ⟨1623473, by rfl⟩ : syracuseStep 2164631 = 3246947) B3246947
theorem B8218853 : Blo 2163435 8218853 := bbase (se 4 (by rfl) ⟨770517, by rfl⟩ : syracuseStep 8218853 = 1541035) (by norm_num)
theorem B5479235 : Blo 2163435 5479235 := bstep (se 1 (by rfl) ⟨4109426, by rfl⟩ : syracuseStep 5479235 = 8218853) B8218853
theorem B3652823 : Blo 2163435 3652823 := bstep (se 1 (by rfl) ⟨2739617, by rfl⟩ : syracuseStep 3652823 = 5479235) B5479235
theorem B2435215 : Blo 2163435 2435215 := bstep (se 1 (by rfl) ⟨1826411, by rfl⟩ : syracuseStep 2435215 = 3652823) B3652823
theorem B3246953 : Blo 2163435 3246953 := bstep (se 2 (by rfl) ⟨1217607, by rfl⟩ : syracuseStep 3246953 = 2435215) B2435215
theorem B2164635 : Blo 2163435 2164635 := bstep (se 1 (by rfl) ⟨1623476, by rfl⟩ : syracuseStep 2164635 = 3246953) B3246953
theorem B17792885 : Blo 2163435 17792885 := bbase (se 5 (by rfl) ⟨834041, by rfl⟩ : syracuseStep 17792885 = 1668083) (by norm_num)
theorem B11861923 : Blo 2163435 11861923 := bstep (se 1 (by rfl) ⟨8896442, by rfl⟩ : syracuseStep 11861923 = 17792885) B17792885
theorem B15815897 : Blo 2163435 15815897 := bstep (se 2 (by rfl) ⟨5930961, by rfl⟩ : syracuseStep 15815897 = 11861923) B11861923
theorem B10543931 : Blo 2163435 10543931 := bstep (se 1 (by rfl) ⟨7907948, by rfl⟩ : syracuseStep 10543931 = 15815897) B15815897
theorem B7029287 : Blo 2163435 7029287 := bstep (se 1 (by rfl) ⟨5271965, by rfl⟩ : syracuseStep 7029287 = 10543931) B10543931
theorem B4686191 : Blo 2163435 4686191 := bstep (se 1 (by rfl) ⟨3514643, by rfl⟩ : syracuseStep 4686191 = 7029287) B7029287
theorem B3124127 : Blo 2163435 3124127 := bstep (se 1 (by rfl) ⟨2343095, by rfl⟩ : syracuseStep 3124127 = 4686191) B4686191
theorem B8331005 : Blo 2163435 8331005 := bstep (se 3 (by rfl) ⟨1562063, by rfl⟩ : syracuseStep 8331005 = 3124127) B3124127
theorem B5554003 : Blo 2163435 5554003 := bstep (se 1 (by rfl) ⟨4165502, by rfl⟩ : syracuseStep 5554003 = 8331005) B8331005
theorem B7405337 : Blo 2163435 7405337 := bstep (se 2 (by rfl) ⟨2777001, by rfl⟩ : syracuseStep 7405337 = 5554003) B5554003
theorem B4936891 : Blo 2163435 4936891 := bstep (se 1 (by rfl) ⟨3702668, by rfl⟩ : syracuseStep 4936891 = 7405337) B7405337
theorem B6582521 : Blo 2163435 6582521 := bstep (se 2 (by rfl) ⟨2468445, by rfl⟩ : syracuseStep 6582521 = 4936891) B4936891
theorem B4388347 : Blo 2163435 4388347 := bstep (se 1 (by rfl) ⟨3291260, by rfl⟩ : syracuseStep 4388347 = 6582521) B6582521
theorem B5851129 : Blo 2163435 5851129 := bstep (se 2 (by rfl) ⟨2194173, by rfl⟩ : syracuseStep 5851129 = 4388347) B4388347
theorem B7801505 : Blo 2163435 7801505 := bstep (se 2 (by rfl) ⟨2925564, by rfl⟩ : syracuseStep 7801505 = 5851129) B5851129
theorem B5201003 : Blo 2163435 5201003 := bstep (se 1 (by rfl) ⟨3900752, by rfl⟩ : syracuseStep 5201003 = 7801505) B7801505
theorem B3467335 : Blo 2163435 3467335 := bstep (se 1 (by rfl) ⟨2600501, by rfl⟩ : syracuseStep 3467335 = 5201003) B5201003
theorem B4623113 : Blo 2163435 4623113 := bstep (se 2 (by rfl) ⟨1733667, by rfl⟩ : syracuseStep 4623113 = 3467335) B3467335
theorem B12328301 : Blo 2163435 12328301 := bstep (se 3 (by rfl) ⟨2311556, by rfl⟩ : syracuseStep 12328301 = 4623113) B4623113
theorem B8218867 : Blo 2163435 8218867 := bstep (se 1 (by rfl) ⟨6164150, by rfl⟩ : syracuseStep 8218867 = 12328301) B12328301
theorem B10958489 : Blo 2163435 10958489 := bstep (se 2 (by rfl) ⟨4109433, by rfl⟩ : syracuseStep 10958489 = 8218867) B8218867
theorem B7305659 : Blo 2163435 7305659 := bstep (se 1 (by rfl) ⟨5479244, by rfl⟩ : syracuseStep 7305659 = 10958489) B10958489
theorem B4870439 : Blo 2163435 4870439 := bstep (se 1 (by rfl) ⟨3652829, by rfl⟩ : syracuseStep 4870439 = 7305659) B7305659
theorem B3246959 : Blo 2163435 3246959 := bstep (se 1 (by rfl) ⟨2435219, by rfl⟩ : syracuseStep 3246959 = 4870439) B4870439
theorem B2164639 : Blo 2163435 2164639 := bstep (se 1 (by rfl) ⟨1623479, by rfl⟩ : syracuseStep 2164639 = 3246959) B3246959
theorem B3246965 : Blo 2163435 3246965 := bbase (se 5 (by rfl) ⟨152201, by rfl⟩ : syracuseStep 3246965 = 304403) (by norm_num)
theorem B2164643 : Blo 2163435 2164643 := bstep (se 1 (by rfl) ⟨1623482, by rfl⟩ : syracuseStep 2164643 = 3246965) B3246965
theorem B4222349 : Blo 2163435 4222349 := bbase (se 3 (by rfl) ⟨791690, by rfl⟩ : syracuseStep 4222349 = 1583381) (by norm_num)
theorem B180153557 : Blo 2163435 180153557 := bstep (se 7 (by rfl) ⟨2111174, by rfl⟩ : syracuseStep 180153557 = 4222349) B4222349
theorem B120102371 : Blo 2163435 120102371 := bstep (se 1 (by rfl) ⟨90076778, by rfl⟩ : syracuseStep 120102371 = 180153557) B180153557
theorem B80068247 : Blo 2163435 80068247 := bstep (se 1 (by rfl) ⟨60051185, by rfl⟩ : syracuseStep 80068247 = 120102371) B120102371
theorem B53378831 : Blo 2163435 53378831 := bstep (se 1 (by rfl) ⟨40034123, by rfl⟩ : syracuseStep 53378831 = 80068247) B80068247
theorem B35585887 : Blo 2163435 35585887 := bstep (se 1 (by rfl) ⟨26689415, by rfl⟩ : syracuseStep 35585887 = 53378831) B53378831
theorem B47447849 : Blo 2163435 47447849 := bstep (se 2 (by rfl) ⟨17792943, by rfl⟩ : syracuseStep 47447849 = 35585887) B35585887
theorem B31631899 : Blo 2163435 31631899 := bstep (se 1 (by rfl) ⟨23723924, by rfl⟩ : syracuseStep 31631899 = 47447849) B47447849
theorem B42175865 : Blo 2163435 42175865 := bstep (se 2 (by rfl) ⟨15815949, by rfl⟩ : syracuseStep 42175865 = 31631899) B31631899
theorem B28117243 : Blo 2163435 28117243 := bstep (se 1 (by rfl) ⟨21087932, by rfl⟩ : syracuseStep 28117243 = 42175865) B42175865
theorem B37489657 : Blo 2163435 37489657 := bstep (se 2 (by rfl) ⟨14058621, by rfl⟩ : syracuseStep 37489657 = 28117243) B28117243
theorem B49986209 : Blo 2163435 49986209 := bstep (se 2 (by rfl) ⟨18744828, by rfl⟩ : syracuseStep 49986209 = 37489657) B37489657
theorem B33324139 : Blo 2163435 33324139 := bstep (se 1 (by rfl) ⟨24993104, by rfl⟩ : syracuseStep 33324139 = 49986209) B49986209
theorem B44432185 : Blo 2163435 44432185 := bstep (se 2 (by rfl) ⟨16662069, by rfl⟩ : syracuseStep 44432185 = 33324139) B33324139
theorem B59242913 : Blo 2163435 59242913 := bstep (se 2 (by rfl) ⟨22216092, by rfl⟩ : syracuseStep 59242913 = 44432185) B44432185
theorem B39495275 : Blo 2163435 39495275 := bstep (se 1 (by rfl) ⟨29621456, by rfl⟩ : syracuseStep 39495275 = 59242913) B59242913
theorem B26330183 : Blo 2163435 26330183 := bstep (se 1 (by rfl) ⟨19747637, by rfl⟩ : syracuseStep 26330183 = 39495275) B39495275
theorem B17553455 : Blo 2163435 17553455 := bstep (se 1 (by rfl) ⟨13165091, by rfl⟩ : syracuseStep 17553455 = 26330183) B26330183
theorem B11702303 : Blo 2163435 11702303 := bstep (se 1 (by rfl) ⟨8776727, by rfl⟩ : syracuseStep 11702303 = 17553455) B17553455
theorem B7801535 : Blo 2163435 7801535 := bstep (se 1 (by rfl) ⟨5851151, by rfl⟩ : syracuseStep 7801535 = 11702303) B11702303
theorem B5201023 : Blo 2163435 5201023 := bstep (se 1 (by rfl) ⟨3900767, by rfl⟩ : syracuseStep 5201023 = 7801535) B7801535
theorem B6934697 : Blo 2163435 6934697 := bstep (se 2 (by rfl) ⟨2600511, by rfl⟩ : syracuseStep 6934697 = 5201023) B5201023
theorem B4623131 : Blo 2163435 4623131 := bstep (se 1 (by rfl) ⟨3467348, by rfl⟩ : syracuseStep 4623131 = 6934697) B6934697
theorem B3082087 : Blo 2163435 3082087 := bstep (se 1 (by rfl) ⟨2311565, by rfl⟩ : syracuseStep 3082087 = 4623131) B4623131
theorem B4109449 : Blo 2163435 4109449 := bstep (se 2 (by rfl) ⟨1541043, by rfl⟩ : syracuseStep 4109449 = 3082087) B3082087
theorem B5479265 : Blo 2163435 5479265 := bstep (se 2 (by rfl) ⟨2054724, by rfl⟩ : syracuseStep 5479265 = 4109449) B4109449
theorem B3652843 : Blo 2163435 3652843 := bstep (se 1 (by rfl) ⟨2739632, by rfl⟩ : syracuseStep 3652843 = 5479265) B5479265
theorem B4870457 : Blo 2163435 4870457 := bstep (se 2 (by rfl) ⟨1826421, by rfl⟩ : syracuseStep 4870457 = 3652843) B3652843
theorem B3246971 : Blo 2163435 3246971 := bstep (se 1 (by rfl) ⟨2435228, by rfl⟩ : syracuseStep 3246971 = 4870457) B4870457
theorem B2164647 : Blo 2163435 2164647 := bstep (se 1 (by rfl) ⟨1623485, by rfl⟩ : syracuseStep 2164647 = 3246971) B3246971
theorem B2435233 : Blo 2163435 2435233 := bbase (se 2 (by rfl) ⟨913212, by rfl⟩ : syracuseStep 2435233 = 1826425) (by norm_num)
theorem B3246977 : Blo 2163435 3246977 := bstep (se 2 (by rfl) ⟨1217616, by rfl⟩ : syracuseStep 3246977 = 2435233) B2435233
theorem B2164651 : Blo 2163435 2164651 := bstep (se 1 (by rfl) ⟨1623488, by rfl⟩ : syracuseStep 2164651 = 3246977) B3246977
theorem B5479285 : Blo 2163435 5479285 := bbase (se 5 (by rfl) ⟨256841, by rfl⟩ : syracuseStep 5479285 = 513683) (by norm_num)
theorem B7305713 : Blo 2163435 7305713 := bstep (se 2 (by rfl) ⟨2739642, by rfl⟩ : syracuseStep 7305713 = 5479285) B5479285
theorem B4870475 : Blo 2163435 4870475 := bstep (se 1 (by rfl) ⟨3652856, by rfl⟩ : syracuseStep 4870475 = 7305713) B7305713
theorem B3246983 : Blo 2163435 3246983 := bstep (se 1 (by rfl) ⟨2435237, by rfl⟩ : syracuseStep 3246983 = 4870475) B4870475
theorem B2164655 : Blo 2163435 2164655 := bstep (se 1 (by rfl) ⟨1623491, by rfl⟩ : syracuseStep 2164655 = 3246983) B3246983
theorem B3246989 : Blo 2163435 3246989 := bbase (se 3 (by rfl) ⟨608810, by rfl⟩ : syracuseStep 3246989 = 1217621) (by norm_num)
theorem B2164659 : Blo 2163435 2164659 := bstep (se 1 (by rfl) ⟨1623494, by rfl⟩ : syracuseStep 2164659 = 3246989) B3246989
theorem B4870493 : Blo 2163435 4870493 := bbase (se 3 (by rfl) ⟨913217, by rfl⟩ : syracuseStep 4870493 = 1826435) (by norm_num)
theorem B3246995 : Blo 2163435 3246995 := bstep (se 1 (by rfl) ⟨2435246, by rfl⟩ : syracuseStep 3246995 = 4870493) B4870493
theorem B2164663 : Blo 2163435 2164663 := bstep (se 1 (by rfl) ⟨1623497, by rfl⟩ : syracuseStep 2164663 = 3246995) B3246995
theorem B3652877 : Blo 2163435 3652877 := bbase (se 3 (by rfl) ⟨684914, by rfl⟩ : syracuseStep 3652877 = 1369829) (by norm_num)
theorem B2435251 : Blo 2163435 2435251 := bstep (se 1 (by rfl) ⟨1826438, by rfl⟩ : syracuseStep 2435251 = 3652877) B3652877
theorem B3247001 : Blo 2163435 3247001 := bstep (se 2 (by rfl) ⟨1217625, by rfl⟩ : syracuseStep 3247001 = 2435251) B2435251
theorem B2164667 : Blo 2163435 2164667 := bstep (se 1 (by rfl) ⟨1623500, by rfl⟩ : syracuseStep 2164667 = 3247001) B3247001
theorem B18492725 : Blo 2163435 18492725 := bbase (se 5 (by rfl) ⟨866846, by rfl⟩ : syracuseStep 18492725 = 1733693) (by norm_num)
theorem B12328483 : Blo 2163435 12328483 := bstep (se 1 (by rfl) ⟨9246362, by rfl⟩ : syracuseStep 12328483 = 18492725) B18492725
theorem B16437977 : Blo 2163435 16437977 := bstep (se 2 (by rfl) ⟨6164241, by rfl⟩ : syracuseStep 16437977 = 12328483) B12328483
theorem B10958651 : Blo 2163435 10958651 := bstep (se 1 (by rfl) ⟨8218988, by rfl⟩ : syracuseStep 10958651 = 16437977) B16437977
theorem B7305767 : Blo 2163435 7305767 := bstep (se 1 (by rfl) ⟨5479325, by rfl⟩ : syracuseStep 7305767 = 10958651) B10958651
theorem B4870511 : Blo 2163435 4870511 := bstep (se 1 (by rfl) ⟨3652883, by rfl⟩ : syracuseStep 4870511 = 7305767) B7305767
theorem B3247007 : Blo 2163435 3247007 := bstep (se 1 (by rfl) ⟨2435255, by rfl⟩ : syracuseStep 3247007 = 4870511) B4870511
theorem B2164671 : Blo 2163435 2164671 := bstep (se 1 (by rfl) ⟨1623503, by rfl⟩ : syracuseStep 2164671 = 3247007) B3247007
theorem B3247013 : Blo 2163435 3247013 := bbase (se 4 (by rfl) ⟨304407, by rfl⟩ : syracuseStep 3247013 = 608815) (by norm_num)
theorem B2164675 : Blo 2163435 2164675 := bstep (se 1 (by rfl) ⟨1623506, by rfl⟩ : syracuseStep 2164675 = 3247013) B3247013
theorem B2739673 : Blo 2163435 2739673 := bbase (se 2 (by rfl) ⟨1027377, by rfl⟩ : syracuseStep 2739673 = 2054755) (by norm_num)
theorem B3652897 : Blo 2163435 3652897 := bstep (se 2 (by rfl) ⟨1369836, by rfl⟩ : syracuseStep 3652897 = 2739673) B2739673
theorem B4870529 : Blo 2163435 4870529 := bstep (se 2 (by rfl) ⟨1826448, by rfl⟩ : syracuseStep 4870529 = 3652897) B3652897
theorem B3247019 : Blo 2163435 3247019 := bstep (se 1 (by rfl) ⟨2435264, by rfl⟩ : syracuseStep 3247019 = 4870529) B4870529
theorem B2164679 : Blo 2163435 2164679 := bstep (se 1 (by rfl) ⟨1623509, by rfl⟩ : syracuseStep 2164679 = 3247019) B3247019
theorem B2435269 : Blo 2163435 2435269 := bbase (se 4 (by rfl) ⟨228306, by rfl⟩ : syracuseStep 2435269 = 456613) (by norm_num)
theorem B3247025 : Blo 2163435 3247025 := bstep (se 2 (by rfl) ⟨1217634, by rfl⟩ : syracuseStep 3247025 = 2435269) B2435269
theorem B2164683 : Blo 2163435 2164683 := bstep (se 1 (by rfl) ⟨1623512, by rfl⟩ : syracuseStep 2164683 = 3247025) B3247025
theorem B4109525 : Blo 2163435 4109525 := bbase (se 7 (by rfl) ⟨48158, by rfl⟩ : syracuseStep 4109525 = 96317) (by norm_num)
theorem B2739683 : Blo 2163435 2739683 := bstep (se 1 (by rfl) ⟨2054762, by rfl⟩ : syracuseStep 2739683 = 4109525) B4109525
theorem B7305821 : Blo 2163435 7305821 := bstep (se 3 (by rfl) ⟨1369841, by rfl⟩ : syracuseStep 7305821 = 2739683) B2739683
theorem B4870547 : Blo 2163435 4870547 := bstep (se 1 (by rfl) ⟨3652910, by rfl⟩ : syracuseStep 4870547 = 7305821) B7305821
theorem B3247031 : Blo 2163435 3247031 := bstep (se 1 (by rfl) ⟨2435273, by rfl⟩ : syracuseStep 3247031 = 4870547) B4870547
theorem B2164687 : Blo 2163435 2164687 := bstep (se 1 (by rfl) ⟨1623515, by rfl⟩ : syracuseStep 2164687 = 3247031) B3247031
theorem B3247037 : Blo 2163435 3247037 := bbase (se 3 (by rfl) ⟨608819, by rfl⟩ : syracuseStep 3247037 = 1217639) (by norm_num)
theorem B2164691 : Blo 2163435 2164691 := bstep (se 1 (by rfl) ⟨1623518, by rfl⟩ : syracuseStep 2164691 = 3247037) B3247037
theorem B4870565 : Blo 2163435 4870565 := bbase (se 4 (by rfl) ⟨456615, by rfl⟩ : syracuseStep 4870565 = 913231) (by norm_num)
theorem B3247043 : Blo 2163435 3247043 := bstep (se 1 (by rfl) ⟨2435282, by rfl⟩ : syracuseStep 3247043 = 4870565) B4870565
theorem B2164695 : Blo 2163435 2164695 := bstep (se 1 (by rfl) ⟨1623521, by rfl⟩ : syracuseStep 2164695 = 3247043) B3247043
theorem B5479397 : Blo 2163435 5479397 := bbase (se 4 (by rfl) ⟨513693, by rfl⟩ : syracuseStep 5479397 = 1027387) (by norm_num)
theorem B3652931 : Blo 2163435 3652931 := bstep (se 1 (by rfl) ⟨2739698, by rfl⟩ : syracuseStep 3652931 = 5479397) B5479397
theorem B2435287 : Blo 2163435 2435287 := bstep (se 1 (by rfl) ⟨1826465, by rfl⟩ : syracuseStep 2435287 = 3652931) B3652931
theorem B3247049 : Blo 2163435 3247049 := bstep (se 2 (by rfl) ⟨1217643, by rfl⟩ : syracuseStep 3247049 = 2435287) B2435287
theorem B2164699 : Blo 2163435 2164699 := bstep (se 1 (by rfl) ⟨1623524, by rfl⟩ : syracuseStep 2164699 = 3247049) B3247049
theorem B2311625 : Blo 2163435 2311625 := bbase (se 2 (by rfl) ⟨866859, by rfl⟩ : syracuseStep 2311625 = 1733719) (by norm_num)
theorem B6164333 : Blo 2163435 6164333 := bstep (se 3 (by rfl) ⟨1155812, by rfl⟩ : syracuseStep 6164333 = 2311625) B2311625
theorem B4109555 : Blo 2163435 4109555 := bstep (se 1 (by rfl) ⟨3082166, by rfl⟩ : syracuseStep 4109555 = 6164333) B6164333
theorem B10958813 : Blo 2163435 10958813 := bstep (se 3 (by rfl) ⟨2054777, by rfl⟩ : syracuseStep 10958813 = 4109555) B4109555
theorem B7305875 : Blo 2163435 7305875 := bstep (se 1 (by rfl) ⟨5479406, by rfl⟩ : syracuseStep 7305875 = 10958813) B10958813
theorem B4870583 : Blo 2163435 4870583 := bstep (se 1 (by rfl) ⟨3652937, by rfl⟩ : syracuseStep 4870583 = 7305875) B7305875
theorem B3247055 : Blo 2163435 3247055 := bstep (se 1 (by rfl) ⟨2435291, by rfl⟩ : syracuseStep 3247055 = 4870583) B4870583
theorem B2164703 : Blo 2163435 2164703 := bstep (se 1 (by rfl) ⟨1623527, by rfl⟩ : syracuseStep 2164703 = 3247055) B3247055
theorem B3247061 : Blo 2163435 3247061 := bbase (se 7 (by rfl) ⟨38051, by rfl⟩ : syracuseStep 3247061 = 76103) (by norm_num)
theorem B2164707 : Blo 2163435 2164707 := bstep (se 1 (by rfl) ⟨1623530, by rfl⟩ : syracuseStep 2164707 = 3247061) B3247061
theorem B8219141 : Blo 2163435 8219141 := bbase (se 4 (by rfl) ⟨770544, by rfl⟩ : syracuseStep 8219141 = 1541089) (by norm_num)
theorem B5479427 : Blo 2163435 5479427 := bstep (se 1 (by rfl) ⟨4109570, by rfl⟩ : syracuseStep 5479427 = 8219141) B8219141
theorem B3652951 : Blo 2163435 3652951 := bstep (se 1 (by rfl) ⟨2739713, by rfl⟩ : syracuseStep 3652951 = 5479427) B5479427
theorem B4870601 : Blo 2163435 4870601 := bstep (se 2 (by rfl) ⟨1826475, by rfl⟩ : syracuseStep 4870601 = 3652951) B3652951
theorem B3247067 : Blo 2163435 3247067 := bstep (se 1 (by rfl) ⟨2435300, by rfl⟩ : syracuseStep 3247067 = 4870601) B4870601
theorem B2164711 : Blo 2163435 2164711 := bstep (se 1 (by rfl) ⟨1623533, by rfl⟩ : syracuseStep 2164711 = 3247067) B3247067
theorem B2435305 : Blo 2163435 2435305 := bbase (se 2 (by rfl) ⟨913239, by rfl⟩ : syracuseStep 2435305 = 1826479) (by norm_num)
theorem B3247073 : Blo 2163435 3247073 := bstep (se 2 (by rfl) ⟨1217652, by rfl⟩ : syracuseStep 3247073 = 2435305) B2435305
theorem B2164715 : Blo 2163435 2164715 := bstep (se 1 (by rfl) ⟨1623536, by rfl⟩ : syracuseStep 2164715 = 3247073) B3247073
theorem B12328757 : Blo 2163435 12328757 := bbase (se 5 (by rfl) ⟨577910, by rfl⟩ : syracuseStep 12328757 = 1155821) (by norm_num)
theorem B8219171 : Blo 2163435 8219171 := bstep (se 1 (by rfl) ⟨6164378, by rfl⟩ : syracuseStep 8219171 = 12328757) B12328757
theorem B5479447 : Blo 2163435 5479447 := bstep (se 1 (by rfl) ⟨4109585, by rfl⟩ : syracuseStep 5479447 = 8219171) B8219171
theorem B7305929 : Blo 2163435 7305929 := bstep (se 2 (by rfl) ⟨2739723, by rfl⟩ : syracuseStep 7305929 = 5479447) B5479447
theorem B4870619 : Blo 2163435 4870619 := bstep (se 1 (by rfl) ⟨3652964, by rfl⟩ : syracuseStep 4870619 = 7305929) B7305929
theorem B3247079 : Blo 2163435 3247079 := bstep (se 1 (by rfl) ⟨2435309, by rfl⟩ : syracuseStep 3247079 = 4870619) B4870619
theorem B2164719 : Blo 2163435 2164719 := bstep (se 1 (by rfl) ⟨1623539, by rfl⟩ : syracuseStep 2164719 = 3247079) B3247079
theorem B3247085 : Blo 2163435 3247085 := bbase (se 3 (by rfl) ⟨608828, by rfl⟩ : syracuseStep 3247085 = 1217657) (by norm_num)
theorem B2164723 : Blo 2163435 2164723 := bstep (se 1 (by rfl) ⟨1623542, by rfl⟩ : syracuseStep 2164723 = 3247085) B3247085
theorem B4870637 : Blo 2163435 4870637 := bbase (se 3 (by rfl) ⟨913244, by rfl⟩ : syracuseStep 4870637 = 1826489) (by norm_num)
theorem B3247091 : Blo 2163435 3247091 := bstep (se 1 (by rfl) ⟨2435318, by rfl⟩ : syracuseStep 3247091 = 4870637) B4870637
theorem B2164727 : Blo 2163435 2164727 := bstep (se 1 (by rfl) ⟨1623545, by rfl⟩ : syracuseStep 2164727 = 3247091) B3247091
theorem B3124261 : Blo 2163435 3124261 := bbase (se 4 (by rfl) ⟨292899, by rfl⟩ : syracuseStep 3124261 = 585799) (by norm_num)
theorem B4165681 : Blo 2163435 4165681 := bstep (se 2 (by rfl) ⟨1562130, by rfl⟩ : syracuseStep 4165681 = 3124261) B3124261
theorem B5554241 : Blo 2163435 5554241 := bstep (se 2 (by rfl) ⟨2082840, by rfl⟩ : syracuseStep 5554241 = 4165681) B4165681
theorem B3702827 : Blo 2163435 3702827 := bstep (se 1 (by rfl) ⟨2777120, by rfl⟩ : syracuseStep 3702827 = 5554241) B5554241
theorem B2468551 : Blo 2163435 2468551 := bstep (se 1 (by rfl) ⟨1851413, by rfl⟩ : syracuseStep 2468551 = 3702827) B3702827
theorem B3291401 : Blo 2163435 3291401 := bstep (se 2 (by rfl) ⟨1234275, by rfl⟩ : syracuseStep 3291401 = 2468551) B2468551
theorem B8777069 : Blo 2163435 8777069 := bstep (se 3 (by rfl) ⟨1645700, by rfl⟩ : syracuseStep 8777069 = 3291401) B3291401
theorem B5851379 : Blo 2163435 5851379 := bstep (se 1 (by rfl) ⟨4388534, by rfl⟩ : syracuseStep 5851379 = 8777069) B8777069
theorem B15603677 : Blo 2163435 15603677 := bstep (se 3 (by rfl) ⟨2925689, by rfl⟩ : syracuseStep 15603677 = 5851379) B5851379
theorem B10402451 : Blo 2163435 10402451 := bstep (se 1 (by rfl) ⟨7801838, by rfl⟩ : syracuseStep 10402451 = 15603677) B15603677
theorem B6934967 : Blo 2163435 6934967 := bstep (se 1 (by rfl) ⟨5201225, by rfl⟩ : syracuseStep 6934967 = 10402451) B10402451
theorem B4623311 : Blo 2163435 4623311 := bstep (se 1 (by rfl) ⟨3467483, by rfl⟩ : syracuseStep 4623311 = 6934967) B6934967
theorem B3082207 : Blo 2163435 3082207 := bstep (se 1 (by rfl) ⟨2311655, by rfl⟩ : syracuseStep 3082207 = 4623311) B4623311
theorem B4109609 : Blo 2163435 4109609 := bstep (se 2 (by rfl) ⟨1541103, by rfl⟩ : syracuseStep 4109609 = 3082207) B3082207
theorem B2739739 : Blo 2163435 2739739 := bstep (se 1 (by rfl) ⟨2054804, by rfl⟩ : syracuseStep 2739739 = 4109609) B4109609
theorem B3652985 : Blo 2163435 3652985 := bstep (se 2 (by rfl) ⟨1369869, by rfl⟩ : syracuseStep 3652985 = 2739739) B2739739
theorem B2435323 : Blo 2163435 2435323 := bstep (se 1 (by rfl) ⟨1826492, by rfl⟩ : syracuseStep 2435323 = 3652985) B3652985
theorem B3247097 : Blo 2163435 3247097 := bstep (se 2 (by rfl) ⟨1217661, by rfl⟩ : syracuseStep 3247097 = 2435323) B2435323
theorem B2164731 : Blo 2163435 2164731 := bstep (se 1 (by rfl) ⟨1623548, by rfl⟩ : syracuseStep 2164731 = 3247097) B3247097
theorem B7908293 : Blo 2163435 7908293 := bbase (se 4 (by rfl) ⟨741402, by rfl⟩ : syracuseStep 7908293 = 1482805) (by norm_num)
theorem B21088781 : Blo 2163435 21088781 := bstep (se 3 (by rfl) ⟨3954146, by rfl⟩ : syracuseStep 21088781 = 7908293) B7908293
theorem B14059187 : Blo 2163435 14059187 := bstep (se 1 (by rfl) ⟨10544390, by rfl⟩ : syracuseStep 14059187 = 21088781) B21088781
theorem B9372791 : Blo 2163435 9372791 := bstep (se 1 (by rfl) ⟨7029593, by rfl⟩ : syracuseStep 9372791 = 14059187) B14059187
theorem B24994109 : Blo 2163435 24994109 := bstep (se 3 (by rfl) ⟨4686395, by rfl⟩ : syracuseStep 24994109 = 9372791) B9372791
theorem B66650957 : Blo 2163435 66650957 := bstep (se 3 (by rfl) ⟨12497054, by rfl⟩ : syracuseStep 66650957 = 24994109) B24994109
theorem B44433971 : Blo 2163435 44433971 := bstep (se 1 (by rfl) ⟨33325478, by rfl⟩ : syracuseStep 44433971 = 66650957) B66650957
theorem B29622647 : Blo 2163435 29622647 := bstep (se 1 (by rfl) ⟨22216985, by rfl⟩ : syracuseStep 29622647 = 44433971) B44433971
theorem B19748431 : Blo 2163435 19748431 := bstep (se 1 (by rfl) ⟨14811323, by rfl⟩ : syracuseStep 19748431 = 29622647) B29622647
theorem B26331241 : Blo 2163435 26331241 := bstep (se 2 (by rfl) ⟨9874215, by rfl⟩ : syracuseStep 26331241 = 19748431) B19748431
theorem B35108321 : Blo 2163435 35108321 := bstep (se 2 (by rfl) ⟨13165620, by rfl⟩ : syracuseStep 35108321 = 26331241) B26331241
theorem B93622189 : Blo 2163435 93622189 := bstep (se 3 (by rfl) ⟨17554160, by rfl⟩ : syracuseStep 93622189 = 35108321) B35108321
theorem B124829585 : Blo 2163435 124829585 := bstep (se 2 (by rfl) ⟨46811094, by rfl⟩ : syracuseStep 124829585 = 93622189) B93622189
theorem B83219723 : Blo 2163435 83219723 := bstep (se 1 (by rfl) ⟨62414792, by rfl⟩ : syracuseStep 83219723 = 124829585) B124829585
theorem B55479815 : Blo 2163435 55479815 := bstep (se 1 (by rfl) ⟨41609861, by rfl⟩ : syracuseStep 55479815 = 83219723) B83219723
theorem B36986543 : Blo 2163435 36986543 := bstep (se 1 (by rfl) ⟨27739907, by rfl⟩ : syracuseStep 36986543 = 55479815) B55479815
theorem B24657695 : Blo 2163435 24657695 := bstep (se 1 (by rfl) ⟨18493271, by rfl⟩ : syracuseStep 24657695 = 36986543) B36986543
theorem B16438463 : Blo 2163435 16438463 := bstep (se 1 (by rfl) ⟨12328847, by rfl⟩ : syracuseStep 16438463 = 24657695) B24657695
theorem B10958975 : Blo 2163435 10958975 := bstep (se 1 (by rfl) ⟨8219231, by rfl⟩ : syracuseStep 10958975 = 16438463) B16438463
theorem B7305983 : Blo 2163435 7305983 := bstep (se 1 (by rfl) ⟨5479487, by rfl⟩ : syracuseStep 7305983 = 10958975) B10958975
theorem B4870655 : Blo 2163435 4870655 := bstep (se 1 (by rfl) ⟨3652991, by rfl⟩ : syracuseStep 4870655 = 7305983) B7305983
theorem B3247103 : Blo 2163435 3247103 := bstep (se 1 (by rfl) ⟨2435327, by rfl⟩ : syracuseStep 3247103 = 4870655) B4870655
theorem B2164735 : Blo 2163435 2164735 := bstep (se 1 (by rfl) ⟨1623551, by rfl⟩ : syracuseStep 2164735 = 3247103) B3247103
theorem B3247109 : Blo 2163435 3247109 := bbase (se 4 (by rfl) ⟨304416, by rfl⟩ : syracuseStep 3247109 = 608833) (by norm_num)
theorem B2164739 : Blo 2163435 2164739 := bstep (se 1 (by rfl) ⟨1623554, by rfl⟩ : syracuseStep 2164739 = 3247109) B3247109
theorem B3653005 : Blo 2163435 3653005 := bbase (se 3 (by rfl) ⟨684938, by rfl⟩ : syracuseStep 3653005 = 1369877) (by norm_num)
theorem B4870673 : Blo 2163435 4870673 := bstep (se 2 (by rfl) ⟨1826502, by rfl⟩ : syracuseStep 4870673 = 3653005) B3653005
theorem B3247115 : Blo 2163435 3247115 := bstep (se 1 (by rfl) ⟨2435336, by rfl⟩ : syracuseStep 3247115 = 4870673) B4870673
theorem B2164743 : Blo 2163435 2164743 := bstep (se 1 (by rfl) ⟨1623557, by rfl⟩ : syracuseStep 2164743 = 3247115) B3247115
theorem B2435341 : Blo 2163435 2435341 := bbase (se 3 (by rfl) ⟨456626, by rfl⟩ : syracuseStep 2435341 = 913253) (by norm_num)
theorem B3247121 : Blo 2163435 3247121 := bstep (se 2 (by rfl) ⟨1217670, by rfl⟩ : syracuseStep 3247121 = 2435341) B2435341
theorem B2164747 : Blo 2163435 2164747 := bstep (se 1 (by rfl) ⟨1623560, by rfl⟩ : syracuseStep 2164747 = 3247121) B3247121
theorem B7306037 : Blo 2163435 7306037 := bbase (se 5 (by rfl) ⟨342470, by rfl⟩ : syracuseStep 7306037 = 684941) (by norm_num)
theorem B4870691 : Blo 2163435 4870691 := bstep (se 1 (by rfl) ⟨3653018, by rfl⟩ : syracuseStep 4870691 = 7306037) B7306037
theorem B3247127 : Blo 2163435 3247127 := bstep (se 1 (by rfl) ⟨2435345, by rfl⟩ : syracuseStep 3247127 = 4870691) B4870691
theorem B2164751 : Blo 2163435 2164751 := bstep (se 1 (by rfl) ⟨1623563, by rfl⟩ : syracuseStep 2164751 = 3247127) B3247127
theorem B3247133 : Blo 2163435 3247133 := bbase (se 3 (by rfl) ⟨608837, by rfl⟩ : syracuseStep 3247133 = 1217675) (by norm_num)
theorem B2164755 : Blo 2163435 2164755 := bstep (se 1 (by rfl) ⟨1623566, by rfl⟩ : syracuseStep 2164755 = 3247133) B3247133
theorem B4870709 : Blo 2163435 4870709 := bbase (se 5 (by rfl) ⟨228314, by rfl⟩ : syracuseStep 4870709 = 456629) (by norm_num)
theorem B3247139 : Blo 2163435 3247139 := bstep (se 1 (by rfl) ⟨2435354, by rfl⟩ : syracuseStep 3247139 = 4870709) B4870709
theorem B2164759 : Blo 2163435 2164759 := bstep (se 1 (by rfl) ⟨1623569, by rfl⟩ : syracuseStep 2164759 = 3247139) B3247139
theorem B9246757 : Blo 2163435 9246757 := bbase (se 4 (by rfl) ⟨866883, by rfl⟩ : syracuseStep 9246757 = 1733767) (by norm_num)
theorem B12329009 : Blo 2163435 12329009 := bstep (se 2 (by rfl) ⟨4623378, by rfl⟩ : syracuseStep 12329009 = 9246757) B9246757
theorem B8219339 : Blo 2163435 8219339 := bstep (se 1 (by rfl) ⟨6164504, by rfl⟩ : syracuseStep 8219339 = 12329009) B12329009
theorem B5479559 : Blo 2163435 5479559 := bstep (se 1 (by rfl) ⟨4109669, by rfl⟩ : syracuseStep 5479559 = 8219339) B8219339
theorem B3653039 : Blo 2163435 3653039 := bstep (se 1 (by rfl) ⟨2739779, by rfl⟩ : syracuseStep 3653039 = 5479559) B5479559
theorem B2435359 : Blo 2163435 2435359 := bstep (se 1 (by rfl) ⟨1826519, by rfl⟩ : syracuseStep 2435359 = 3653039) B3653039
theorem B3247145 : Blo 2163435 3247145 := bstep (se 2 (by rfl) ⟨1217679, by rfl⟩ : syracuseStep 3247145 = 2435359) B2435359
theorem B2164763 : Blo 2163435 2164763 := bstep (se 1 (by rfl) ⟨1623572, by rfl⟩ : syracuseStep 2164763 = 3247145) B3247145
theorem B9246773 : Blo 2163435 9246773 := bbase (se 5 (by rfl) ⟨433442, by rfl⟩ : syracuseStep 9246773 = 866885) (by norm_num)
theorem B6164515 : Blo 2163435 6164515 := bstep (se 1 (by rfl) ⟨4623386, by rfl⟩ : syracuseStep 6164515 = 9246773) B9246773
theorem B8219353 : Blo 2163435 8219353 := bstep (se 2 (by rfl) ⟨3082257, by rfl⟩ : syracuseStep 8219353 = 6164515) B6164515
theorem B10959137 : Blo 2163435 10959137 := bstep (se 2 (by rfl) ⟨4109676, by rfl⟩ : syracuseStep 10959137 = 8219353) B8219353
theorem B7306091 : Blo 2163435 7306091 := bstep (se 1 (by rfl) ⟨5479568, by rfl⟩ : syracuseStep 7306091 = 10959137) B10959137
theorem B4870727 : Blo 2163435 4870727 := bstep (se 1 (by rfl) ⟨3653045, by rfl⟩ : syracuseStep 4870727 = 7306091) B7306091
theorem B3247151 : Blo 2163435 3247151 := bstep (se 1 (by rfl) ⟨2435363, by rfl⟩ : syracuseStep 3247151 = 4870727) B4870727
theorem B2164767 : Blo 2163435 2164767 := bstep (se 1 (by rfl) ⟨1623575, by rfl⟩ : syracuseStep 2164767 = 3247151) B3247151
theorem B3247157 : Blo 2163435 3247157 := bbase (se 5 (by rfl) ⟨152210, by rfl⟩ : syracuseStep 3247157 = 304421) (by norm_num)
theorem B2164771 : Blo 2163435 2164771 := bstep (se 1 (by rfl) ⟨1623578, by rfl⟩ : syracuseStep 2164771 = 3247157) B3247157
theorem B5479589 : Blo 2163435 5479589 := bbase (se 4 (by rfl) ⟨513711, by rfl⟩ : syracuseStep 5479589 = 1027423) (by norm_num)
theorem B3653059 : Blo 2163435 3653059 := bstep (se 1 (by rfl) ⟨2739794, by rfl⟩ : syracuseStep 3653059 = 5479589) B5479589
theorem B4870745 : Blo 2163435 4870745 := bstep (se 2 (by rfl) ⟨1826529, by rfl⟩ : syracuseStep 4870745 = 3653059) B3653059
theorem B3247163 : Blo 2163435 3247163 := bstep (se 1 (by rfl) ⟨2435372, by rfl⟩ : syracuseStep 3247163 = 4870745) B4870745
theorem B2164775 : Blo 2163435 2164775 := bstep (se 1 (by rfl) ⟨1623581, by rfl⟩ : syracuseStep 2164775 = 3247163) B3247163
theorem B2435377 : Blo 2163435 2435377 := bbase (se 2 (by rfl) ⟨913266, by rfl⟩ : syracuseStep 2435377 = 1826533) (by norm_num)
theorem B3247169 : Blo 2163435 3247169 := bstep (se 2 (by rfl) ⟨1217688, by rfl⟩ : syracuseStep 3247169 = 2435377) B2435377
theorem B2164779 : Blo 2163435 2164779 := bstep (se 1 (by rfl) ⟨1623584, by rfl⟩ : syracuseStep 2164779 = 3247169) B3247169
theorem B4623421 : Blo 2163435 4623421 := bbase (se 3 (by rfl) ⟨866891, by rfl⟩ : syracuseStep 4623421 = 1733783) (by norm_num)
theorem B6164561 : Blo 2163435 6164561 := bstep (se 2 (by rfl) ⟨2311710, by rfl⟩ : syracuseStep 6164561 = 4623421) B4623421
theorem B4109707 : Blo 2163435 4109707 := bstep (se 1 (by rfl) ⟨3082280, by rfl⟩ : syracuseStep 4109707 = 6164561) B6164561
theorem B5479609 : Blo 2163435 5479609 := bstep (se 2 (by rfl) ⟨2054853, by rfl⟩ : syracuseStep 5479609 = 4109707) B4109707
theorem B7306145 : Blo 2163435 7306145 := bstep (se 2 (by rfl) ⟨2739804, by rfl⟩ : syracuseStep 7306145 = 5479609) B5479609
theorem B4870763 : Blo 2163435 4870763 := bstep (se 1 (by rfl) ⟨3653072, by rfl⟩ : syracuseStep 4870763 = 7306145) B7306145
theorem B3247175 : Blo 2163435 3247175 := bstep (se 1 (by rfl) ⟨2435381, by rfl⟩ : syracuseStep 3247175 = 4870763) B4870763
theorem B2164783 : Blo 2163435 2164783 := bstep (se 1 (by rfl) ⟨1623587, by rfl⟩ : syracuseStep 2164783 = 3247175) B3247175
theorem B3247181 : Blo 2163435 3247181 := bbase (se 3 (by rfl) ⟨608846, by rfl⟩ : syracuseStep 3247181 = 1217693) (by norm_num)
theorem B2164787 : Blo 2163435 2164787 := bstep (se 1 (by rfl) ⟨1623590, by rfl⟩ : syracuseStep 2164787 = 3247181) B3247181
theorem B4870781 : Blo 2163435 4870781 := bbase (se 3 (by rfl) ⟨913271, by rfl⟩ : syracuseStep 4870781 = 1826543) (by norm_num)
theorem B3247187 : Blo 2163435 3247187 := bstep (se 1 (by rfl) ⟨2435390, by rfl⟩ : syracuseStep 3247187 = 4870781) B4870781
theorem B2164791 : Blo 2163435 2164791 := bstep (se 1 (by rfl) ⟨1623593, by rfl⟩ : syracuseStep 2164791 = 3247187) B3247187
theorem B3653093 : Blo 2163435 3653093 := bbase (se 4 (by rfl) ⟨342477, by rfl⟩ : syracuseStep 3653093 = 684955) (by norm_num)
theorem B2435395 : Blo 2163435 2435395 := bstep (se 1 (by rfl) ⟨1826546, by rfl⟩ : syracuseStep 2435395 = 3653093) B3653093
theorem B3247193 : Blo 2163435 3247193 := bstep (se 2 (by rfl) ⟨1217697, by rfl⟩ : syracuseStep 3247193 = 2435395) B2435395
theorem B2164795 : Blo 2163435 2164795 := bstep (se 1 (by rfl) ⟨1623596, by rfl⟩ : syracuseStep 2164795 = 3247193) B3247193
theorem B12497429 : Blo 2163435 12497429 := bbase (se 6 (by rfl) ⟨292908, by rfl⟩ : syracuseStep 12497429 = 585817) (by norm_num)
theorem B33326477 : Blo 2163435 33326477 := bstep (se 3 (by rfl) ⟨6248714, by rfl⟩ : syracuseStep 33326477 = 12497429) B12497429
theorem B22217651 : Blo 2163435 22217651 := bstep (se 1 (by rfl) ⟨16663238, by rfl⟩ : syracuseStep 22217651 = 33326477) B33326477
theorem B14811767 : Blo 2163435 14811767 := bstep (se 1 (by rfl) ⟨11108825, by rfl⟩ : syracuseStep 14811767 = 22217651) B22217651
theorem B9874511 : Blo 2163435 9874511 := bstep (se 1 (by rfl) ⟨7405883, by rfl⟩ : syracuseStep 9874511 = 14811767) B14811767
theorem B6583007 : Blo 2163435 6583007 := bstep (se 1 (by rfl) ⟨4937255, by rfl⟩ : syracuseStep 6583007 = 9874511) B9874511
theorem B4388671 : Blo 2163435 4388671 := bstep (se 1 (by rfl) ⟨3291503, by rfl⟩ : syracuseStep 4388671 = 6583007) B6583007
theorem B23406245 : Blo 2163435 23406245 := bstep (se 4 (by rfl) ⟨2194335, by rfl⟩ : syracuseStep 23406245 = 4388671) B4388671
theorem B15604163 : Blo 2163435 15604163 := bstep (se 1 (by rfl) ⟨11703122, by rfl⟩ : syracuseStep 15604163 = 23406245) B23406245
theorem B10402775 : Blo 2163435 10402775 := bstep (se 1 (by rfl) ⟨7802081, by rfl⟩ : syracuseStep 10402775 = 15604163) B15604163
theorem B6935183 : Blo 2163435 6935183 := bstep (se 1 (by rfl) ⟨5201387, by rfl⟩ : syracuseStep 6935183 = 10402775) B10402775
theorem B4623455 : Blo 2163435 4623455 := bstep (se 1 (by rfl) ⟨3467591, by rfl⟩ : syracuseStep 4623455 = 6935183) B6935183
theorem B3082303 : Blo 2163435 3082303 := bstep (se 1 (by rfl) ⟨2311727, by rfl⟩ : syracuseStep 3082303 = 4623455) B4623455
theorem B16438949 : Blo 2163435 16438949 := bstep (se 4 (by rfl) ⟨1541151, by rfl⟩ : syracuseStep 16438949 = 3082303) B3082303
theorem B10959299 : Blo 2163435 10959299 := bstep (se 1 (by rfl) ⟨8219474, by rfl⟩ : syracuseStep 10959299 = 16438949) B16438949
theorem B7306199 : Blo 2163435 7306199 := bstep (se 1 (by rfl) ⟨5479649, by rfl⟩ : syracuseStep 7306199 = 10959299) B10959299
theorem B4870799 : Blo 2163435 4870799 := bstep (se 1 (by rfl) ⟨3653099, by rfl⟩ : syracuseStep 4870799 = 7306199) B7306199
theorem B3247199 : Blo 2163435 3247199 := bstep (se 1 (by rfl) ⟨2435399, by rfl⟩ : syracuseStep 3247199 = 4870799) B4870799
theorem B2164799 : Blo 2163435 2164799 := bstep (se 1 (by rfl) ⟨1623599, by rfl⟩ : syracuseStep 2164799 = 3247199) B3247199
theorem B3247205 : Blo 2163435 3247205 := bbase (se 4 (by rfl) ⟨304425, by rfl⟩ : syracuseStep 3247205 = 608851) (by norm_num)
theorem B2164803 : Blo 2163435 2164803 := bstep (se 1 (by rfl) ⟨1623602, by rfl⟩ : syracuseStep 2164803 = 3247205) B3247205
theorem B3467605 : Blo 2163435 3467605 := bbase (se 10 (by rfl) ⟨5079, by rfl⟩ : syracuseStep 3467605 = 10159) (by norm_num)
theorem B4623473 : Blo 2163435 4623473 := bstep (se 2 (by rfl) ⟨1733802, by rfl⟩ : syracuseStep 4623473 = 3467605) B3467605
theorem B3082315 : Blo 2163435 3082315 := bstep (se 1 (by rfl) ⟨2311736, by rfl⟩ : syracuseStep 3082315 = 4623473) B4623473
theorem B4109753 : Blo 2163435 4109753 := bstep (se 2 (by rfl) ⟨1541157, by rfl⟩ : syracuseStep 4109753 = 3082315) B3082315
theorem B2739835 : Blo 2163435 2739835 := bstep (se 1 (by rfl) ⟨2054876, by rfl⟩ : syracuseStep 2739835 = 4109753) B4109753
theorem B3653113 : Blo 2163435 3653113 := bstep (se 2 (by rfl) ⟨1369917, by rfl⟩ : syracuseStep 3653113 = 2739835) B2739835
theorem B4870817 : Blo 2163435 4870817 := bstep (se 2 (by rfl) ⟨1826556, by rfl⟩ : syracuseStep 4870817 = 3653113) B3653113
theorem B3247211 : Blo 2163435 3247211 := bstep (se 1 (by rfl) ⟨2435408, by rfl⟩ : syracuseStep 3247211 = 4870817) B4870817
theorem B2164807 : Blo 2163435 2164807 := bstep (se 1 (by rfl) ⟨1623605, by rfl⟩ : syracuseStep 2164807 = 3247211) B3247211
theorem B2435413 : Blo 2163435 2435413 := bbase (se 10 (by rfl) ⟨3567, by rfl⟩ : syracuseStep 2435413 = 7135) (by norm_num)
theorem B3247217 : Blo 2163435 3247217 := bstep (se 2 (by rfl) ⟨1217706, by rfl⟩ : syracuseStep 3247217 = 2435413) B2435413
theorem B2164811 : Blo 2163435 2164811 := bstep (se 1 (by rfl) ⟨1623608, by rfl⟩ : syracuseStep 2164811 = 3247217) B3247217
theorem B2739845 : Blo 2163435 2739845 := bbase (se 4 (by rfl) ⟨256860, by rfl⟩ : syracuseStep 2739845 = 513721) (by norm_num)
theorem B7306253 : Blo 2163435 7306253 := bstep (se 3 (by rfl) ⟨1369922, by rfl⟩ : syracuseStep 7306253 = 2739845) B2739845
theorem B4870835 : Blo 2163435 4870835 := bstep (se 1 (by rfl) ⟨3653126, by rfl⟩ : syracuseStep 4870835 = 7306253) B7306253
theorem B3247223 : Blo 2163435 3247223 := bstep (se 1 (by rfl) ⟨2435417, by rfl⟩ : syracuseStep 3247223 = 4870835) B4870835
theorem B2164815 : Blo 2163435 2164815 := bstep (se 1 (by rfl) ⟨1623611, by rfl⟩ : syracuseStep 2164815 = 3247223) B3247223
theorem B3247229 : Blo 2163435 3247229 := bbase (se 3 (by rfl) ⟨608855, by rfl⟩ : syracuseStep 3247229 = 1217711) (by norm_num)
theorem B2164819 : Blo 2163435 2164819 := bstep (se 1 (by rfl) ⟨1623614, by rfl⟩ : syracuseStep 2164819 = 3247229) B3247229
theorem B4870853 : Blo 2163435 4870853 := bbase (se 4 (by rfl) ⟨456642, by rfl⟩ : syracuseStep 4870853 = 913285) (by norm_num)
theorem B3247235 : Blo 2163435 3247235 := bstep (se 1 (by rfl) ⟨2435426, by rfl⟩ : syracuseStep 3247235 = 4870853) B4870853
theorem B2164823 : Blo 2163435 2164823 := bstep (se 1 (by rfl) ⟨1623617, by rfl⟩ : syracuseStep 2164823 = 3247235) B3247235
theorem B5630269 : Blo 2163435 5630269 := bbase (se 3 (by rfl) ⟨1055675, by rfl⟩ : syracuseStep 5630269 = 2111351) (by norm_num)
theorem B7507025 : Blo 2163435 7507025 := bstep (se 2 (by rfl) ⟨2815134, by rfl⟩ : syracuseStep 7507025 = 5630269) B5630269
theorem B5004683 : Blo 2163435 5004683 := bstep (se 1 (by rfl) ⟨3753512, by rfl⟩ : syracuseStep 5004683 = 7507025) B7507025
theorem B3336455 : Blo 2163435 3336455 := bstep (se 1 (by rfl) ⟨2502341, by rfl⟩ : syracuseStep 3336455 = 5004683) B5004683
theorem B2224303 : Blo 2163435 2224303 := bstep (se 1 (by rfl) ⟨1668227, by rfl⟩ : syracuseStep 2224303 = 3336455) B3336455
theorem B11862949 : Blo 2163435 11862949 := bstep (se 4 (by rfl) ⟨1112151, by rfl⟩ : syracuseStep 11862949 = 2224303) B2224303
theorem B15817265 : Blo 2163435 15817265 := bstep (se 2 (by rfl) ⟨5931474, by rfl⟩ : syracuseStep 15817265 = 11862949) B11862949
theorem B10544843 : Blo 2163435 10544843 := bstep (se 1 (by rfl) ⟨7908632, by rfl⟩ : syracuseStep 10544843 = 15817265) B15817265
theorem B28119581 : Blo 2163435 28119581 := bstep (se 3 (by rfl) ⟨5272421, by rfl⟩ : syracuseStep 28119581 = 10544843) B10544843
theorem B18746387 : Blo 2163435 18746387 := bstep (se 1 (by rfl) ⟨14059790, by rfl⟩ : syracuseStep 18746387 = 28119581) B28119581
theorem B12497591 : Blo 2163435 12497591 := bstep (se 1 (by rfl) ⟨9373193, by rfl⟩ : syracuseStep 12497591 = 18746387) B18746387
theorem B33326909 : Blo 2163435 33326909 := bstep (se 3 (by rfl) ⟨6248795, by rfl⟩ : syracuseStep 33326909 = 12497591) B12497591
theorem B22217939 : Blo 2163435 22217939 := bstep (se 1 (by rfl) ⟨16663454, by rfl⟩ : syracuseStep 22217939 = 33326909) B33326909
theorem B14811959 : Blo 2163435 14811959 := bstep (se 1 (by rfl) ⟨11108969, by rfl⟩ : syracuseStep 14811959 = 22217939) B22217939
theorem B9874639 : Blo 2163435 9874639 := bstep (se 1 (by rfl) ⟨7405979, by rfl⟩ : syracuseStep 9874639 = 14811959) B14811959
theorem B13166185 : Blo 2163435 13166185 := bstep (se 2 (by rfl) ⟨4937319, by rfl⟩ : syracuseStep 13166185 = 9874639) B9874639
theorem B17554913 : Blo 2163435 17554913 := bstep (se 2 (by rfl) ⟨6583092, by rfl⟩ : syracuseStep 17554913 = 13166185) B13166185
theorem B11703275 : Blo 2163435 11703275 := bstep (se 1 (by rfl) ⟨8777456, by rfl⟩ : syracuseStep 11703275 = 17554913) B17554913
theorem B7802183 : Blo 2163435 7802183 := bstep (se 1 (by rfl) ⟨5851637, by rfl⟩ : syracuseStep 7802183 = 11703275) B11703275
theorem B20805821 : Blo 2163435 20805821 := bstep (se 3 (by rfl) ⟨3901091, by rfl⟩ : syracuseStep 20805821 = 7802183) B7802183
theorem B13870547 : Blo 2163435 13870547 := bstep (se 1 (by rfl) ⟨10402910, by rfl⟩ : syracuseStep 13870547 = 20805821) B20805821
theorem B9247031 : Blo 2163435 9247031 := bstep (se 1 (by rfl) ⟨6935273, by rfl⟩ : syracuseStep 9247031 = 13870547) B13870547
theorem B6164687 : Blo 2163435 6164687 := bstep (se 1 (by rfl) ⟨4623515, by rfl⟩ : syracuseStep 6164687 = 9247031) B9247031
theorem B4109791 : Blo 2163435 4109791 := bstep (se 1 (by rfl) ⟨3082343, by rfl⟩ : syracuseStep 4109791 = 6164687) B6164687
theorem B5479721 : Blo 2163435 5479721 := bstep (se 2 (by rfl) ⟨2054895, by rfl⟩ : syracuseStep 5479721 = 4109791) B4109791
theorem B3653147 : Blo 2163435 3653147 := bstep (se 1 (by rfl) ⟨2739860, by rfl⟩ : syracuseStep 3653147 = 5479721) B5479721
theorem B2435431 : Blo 2163435 2435431 := bstep (se 1 (by rfl) ⟨1826573, by rfl⟩ : syracuseStep 2435431 = 3653147) B3653147
theorem B3247241 : Blo 2163435 3247241 := bstep (se 2 (by rfl) ⟨1217715, by rfl⟩ : syracuseStep 3247241 = 2435431) B2435431
theorem B2164827 : Blo 2163435 2164827 := bstep (se 1 (by rfl) ⟨1623620, by rfl⟩ : syracuseStep 2164827 = 3247241) B3247241
theorem B10959461 : Blo 2163435 10959461 := bbase (se 4 (by rfl) ⟨1027449, by rfl⟩ : syracuseStep 10959461 = 2054899) (by norm_num)
theorem B7306307 : Blo 2163435 7306307 := bstep (se 1 (by rfl) ⟨5479730, by rfl⟩ : syracuseStep 7306307 = 10959461) B10959461
theorem B4870871 : Blo 2163435 4870871 := bstep (se 1 (by rfl) ⟨3653153, by rfl⟩ : syracuseStep 4870871 = 7306307) B7306307
theorem B3247247 : Blo 2163435 3247247 := bstep (se 1 (by rfl) ⟨2435435, by rfl⟩ : syracuseStep 3247247 = 4870871) B4870871
theorem B2164831 : Blo 2163435 2164831 := bstep (se 1 (by rfl) ⟨1623623, by rfl⟩ : syracuseStep 2164831 = 3247247) B3247247
theorem B3247253 : Blo 2163435 3247253 := bbase (se 6 (by rfl) ⟨76107, by rfl⟩ : syracuseStep 3247253 = 152215) (by norm_num)
theorem B2164835 : Blo 2163435 2164835 := bstep (se 1 (by rfl) ⟨1623626, by rfl⟩ : syracuseStep 2164835 = 3247253) B3247253
theorem B23406677 : Blo 2163435 23406677 := bbase (se 8 (by rfl) ⟨137148, by rfl⟩ : syracuseStep 23406677 = 274297) (by norm_num)
theorem B15604451 : Blo 2163435 15604451 := bstep (se 1 (by rfl) ⟨11703338, by rfl⟩ : syracuseStep 15604451 = 23406677) B23406677
theorem B10402967 : Blo 2163435 10402967 := bstep (se 1 (by rfl) ⟨7802225, by rfl⟩ : syracuseStep 10402967 = 15604451) B15604451
theorem B6935311 : Blo 2163435 6935311 := bstep (se 1 (by rfl) ⟨5201483, by rfl⟩ : syracuseStep 6935311 = 10402967) B10402967
theorem B9247081 : Blo 2163435 9247081 := bstep (se 2 (by rfl) ⟨3467655, by rfl⟩ : syracuseStep 9247081 = 6935311) B6935311
theorem B12329441 : Blo 2163435 12329441 := bstep (se 2 (by rfl) ⟨4623540, by rfl⟩ : syracuseStep 12329441 = 9247081) B9247081
theorem B8219627 : Blo 2163435 8219627 := bstep (se 1 (by rfl) ⟨6164720, by rfl⟩ : syracuseStep 8219627 = 12329441) B12329441
theorem B5479751 : Blo 2163435 5479751 := bstep (se 1 (by rfl) ⟨4109813, by rfl⟩ : syracuseStep 5479751 = 8219627) B8219627
theorem B3653167 : Blo 2163435 3653167 := bstep (se 1 (by rfl) ⟨2739875, by rfl⟩ : syracuseStep 3653167 = 5479751) B5479751
theorem B4870889 : Blo 2163435 4870889 := bstep (se 2 (by rfl) ⟨1826583, by rfl⟩ : syracuseStep 4870889 = 3653167) B3653167
theorem B3247259 : Blo 2163435 3247259 := bstep (se 1 (by rfl) ⟨2435444, by rfl⟩ : syracuseStep 3247259 = 4870889) B4870889
theorem B2164839 : Blo 2163435 2164839 := bstep (se 1 (by rfl) ⟨1623629, by rfl⟩ : syracuseStep 2164839 = 3247259) B3247259
theorem B2435449 : Blo 2163435 2435449 := bbase (se 2 (by rfl) ⟨913293, by rfl⟩ : syracuseStep 2435449 = 1826587) (by norm_num)
theorem B3247265 : Blo 2163435 3247265 := bstep (se 2 (by rfl) ⟨1217724, by rfl⟩ : syracuseStep 3247265 = 2435449) B2435449
theorem B2164843 : Blo 2163435 2164843 := bstep (se 1 (by rfl) ⟨1623632, by rfl⟩ : syracuseStep 2164843 = 3247265) B3247265
theorem B4937365 : Blo 2163435 4937365 := bbase (se 6 (by rfl) ⟨115719, by rfl⟩ : syracuseStep 4937365 = 231439) (by norm_num)
theorem B6583153 : Blo 2163435 6583153 := bstep (se 2 (by rfl) ⟨2468682, by rfl⟩ : syracuseStep 6583153 = 4937365) B4937365
theorem B8777537 : Blo 2163435 8777537 := bstep (se 2 (by rfl) ⟨3291576, by rfl⟩ : syracuseStep 8777537 = 6583153) B6583153
theorem B5851691 : Blo 2163435 5851691 := bstep (se 1 (by rfl) ⟨4388768, by rfl⟩ : syracuseStep 5851691 = 8777537) B8777537
theorem B3901127 : Blo 2163435 3901127 := bstep (se 1 (by rfl) ⟨2925845, by rfl⟩ : syracuseStep 3901127 = 5851691) B5851691
theorem B10403005 : Blo 2163435 10403005 := bstep (se 3 (by rfl) ⟨1950563, by rfl⟩ : syracuseStep 10403005 = 3901127) B3901127
theorem B13870673 : Blo 2163435 13870673 := bstep (se 2 (by rfl) ⟨5201502, by rfl⟩ : syracuseStep 13870673 = 10403005) B10403005
theorem B9247115 : Blo 2163435 9247115 := bstep (se 1 (by rfl) ⟨6935336, by rfl⟩ : syracuseStep 9247115 = 13870673) B13870673
theorem B6164743 : Blo 2163435 6164743 := bstep (se 1 (by rfl) ⟨4623557, by rfl⟩ : syracuseStep 6164743 = 9247115) B9247115
theorem B8219657 : Blo 2163435 8219657 := bstep (se 2 (by rfl) ⟨3082371, by rfl⟩ : syracuseStep 8219657 = 6164743) B6164743
theorem B5479771 : Blo 2163435 5479771 := bstep (se 1 (by rfl) ⟨4109828, by rfl⟩ : syracuseStep 5479771 = 8219657) B8219657
theorem B7306361 : Blo 2163435 7306361 := bstep (se 2 (by rfl) ⟨2739885, by rfl⟩ : syracuseStep 7306361 = 5479771) B5479771
theorem B4870907 : Blo 2163435 4870907 := bstep (se 1 (by rfl) ⟨3653180, by rfl⟩ : syracuseStep 4870907 = 7306361) B7306361
theorem B3247271 : Blo 2163435 3247271 := bstep (se 1 (by rfl) ⟨2435453, by rfl⟩ : syracuseStep 3247271 = 4870907) B4870907
theorem B2164847 : Blo 2163435 2164847 := bstep (se 1 (by rfl) ⟨1623635, by rfl⟩ : syracuseStep 2164847 = 3247271) B3247271
theorem B3247277 : Blo 2163435 3247277 := bbase (se 3 (by rfl) ⟨608864, by rfl⟩ : syracuseStep 3247277 = 1217729) (by norm_num)
theorem B2164851 : Blo 2163435 2164851 := bstep (se 1 (by rfl) ⟨1623638, by rfl⟩ : syracuseStep 2164851 = 3247277) B3247277
theorem B4870925 : Blo 2163435 4870925 := bbase (se 3 (by rfl) ⟨913298, by rfl⟩ : syracuseStep 4870925 = 1826597) (by norm_num)
theorem B3247283 : Blo 2163435 3247283 := bstep (se 1 (by rfl) ⟨2435462, by rfl⟩ : syracuseStep 3247283 = 4870925) B4870925
theorem B2164855 : Blo 2163435 2164855 := bstep (se 1 (by rfl) ⟨1623641, by rfl⟩ : syracuseStep 2164855 = 3247283) B3247283
theorem B2739901 : Blo 2163435 2739901 := bbase (se 3 (by rfl) ⟨513731, by rfl⟩ : syracuseStep 2739901 = 1027463) (by norm_num)
theorem B3653201 : Blo 2163435 3653201 := bstep (se 2 (by rfl) ⟨1369950, by rfl⟩ : syracuseStep 3653201 = 2739901) B2739901
theorem B2435467 : Blo 2163435 2435467 := bstep (se 1 (by rfl) ⟨1826600, by rfl⟩ : syracuseStep 2435467 = 3653201) B3653201
theorem B3247289 : Blo 2163435 3247289 := bstep (se 2 (by rfl) ⟨1217733, by rfl⟩ : syracuseStep 3247289 = 2435467) B2435467
theorem B2164859 : Blo 2163435 2164859 := bstep (se 1 (by rfl) ⟨1623644, by rfl⟩ : syracuseStep 2164859 = 3247289) B3247289
theorem B7406101 : Blo 2163435 7406101 := bbase (se 6 (by rfl) ⟨173580, by rfl⟩ : syracuseStep 7406101 = 347161) (by norm_num)
theorem B9874801 : Blo 2163435 9874801 := bstep (se 2 (by rfl) ⟨3703050, by rfl⟩ : syracuseStep 9874801 = 7406101) B7406101
theorem B13166401 : Blo 2163435 13166401 := bstep (se 2 (by rfl) ⟨4937400, by rfl⟩ : syracuseStep 13166401 = 9874801) B9874801
theorem B17555201 : Blo 2163435 17555201 := bstep (se 2 (by rfl) ⟨6583200, by rfl⟩ : syracuseStep 17555201 = 13166401) B13166401
theorem B11703467 : Blo 2163435 11703467 := bstep (se 1 (by rfl) ⟨8777600, by rfl⟩ : syracuseStep 11703467 = 17555201) B17555201
theorem B7802311 : Blo 2163435 7802311 := bstep (se 1 (by rfl) ⟨5851733, by rfl⟩ : syracuseStep 7802311 = 11703467) B11703467
theorem B10403081 : Blo 2163435 10403081 := bstep (se 2 (by rfl) ⟨3901155, by rfl⟩ : syracuseStep 10403081 = 7802311) B7802311
theorem B6935387 : Blo 2163435 6935387 := bstep (se 1 (by rfl) ⟨5201540, by rfl⟩ : syracuseStep 6935387 = 10403081) B10403081
theorem B18494365 : Blo 2163435 18494365 := bstep (se 3 (by rfl) ⟨3467693, by rfl⟩ : syracuseStep 18494365 = 6935387) B6935387
theorem B24659153 : Blo 2163435 24659153 := bstep (se 2 (by rfl) ⟨9247182, by rfl⟩ : syracuseStep 24659153 = 18494365) B18494365
theorem B16439435 : Blo 2163435 16439435 := bstep (se 1 (by rfl) ⟨12329576, by rfl⟩ : syracuseStep 16439435 = 24659153) B24659153
theorem B10959623 : Blo 2163435 10959623 := bstep (se 1 (by rfl) ⟨8219717, by rfl⟩ : syracuseStep 10959623 = 16439435) B16439435
theorem B7306415 : Blo 2163435 7306415 := bstep (se 1 (by rfl) ⟨5479811, by rfl⟩ : syracuseStep 7306415 = 10959623) B10959623
theorem B4870943 : Blo 2163435 4870943 := bstep (se 1 (by rfl) ⟨3653207, by rfl⟩ : syracuseStep 4870943 = 7306415) B7306415
theorem B3247295 : Blo 2163435 3247295 := bstep (se 1 (by rfl) ⟨2435471, by rfl⟩ : syracuseStep 3247295 = 4870943) B4870943
theorem B2164863 : Blo 2163435 2164863 := bstep (se 1 (by rfl) ⟨1623647, by rfl⟩ : syracuseStep 2164863 = 3247295) B3247295
theorem B3247301 : Blo 2163435 3247301 := bbase (se 4 (by rfl) ⟨304434, by rfl⟩ : syracuseStep 3247301 = 608869) (by norm_num)
theorem B2164867 : Blo 2163435 2164867 := bstep (se 1 (by rfl) ⟨1623650, by rfl⟩ : syracuseStep 2164867 = 3247301) B3247301
theorem B3653221 : Blo 2163435 3653221 := bbase (se 4 (by rfl) ⟨342489, by rfl⟩ : syracuseStep 3653221 = 684979) (by norm_num)
theorem B4870961 : Blo 2163435 4870961 := bstep (se 2 (by rfl) ⟨1826610, by rfl⟩ : syracuseStep 4870961 = 3653221) B3653221
theorem B3247307 : Blo 2163435 3247307 := bstep (se 1 (by rfl) ⟨2435480, by rfl⟩ : syracuseStep 3247307 = 4870961) B4870961
theorem B2164871 : Blo 2163435 2164871 := bstep (se 1 (by rfl) ⟨1623653, by rfl⟩ : syracuseStep 2164871 = 3247307) B3247307
theorem B2435485 : Blo 2163435 2435485 := bbase (se 3 (by rfl) ⟨456653, by rfl⟩ : syracuseStep 2435485 = 913307) (by norm_num)
theorem B3247313 : Blo 2163435 3247313 := bstep (se 2 (by rfl) ⟨1217742, by rfl⟩ : syracuseStep 3247313 = 2435485) B2435485
theorem B2164875 : Blo 2163435 2164875 := bstep (se 1 (by rfl) ⟨1623656, by rfl⟩ : syracuseStep 2164875 = 3247313) B3247313
theorem B7306469 : Blo 2163435 7306469 := bbase (se 4 (by rfl) ⟨684981, by rfl⟩ : syracuseStep 7306469 = 1369963) (by norm_num)
theorem B4870979 : Blo 2163435 4870979 := bstep (se 1 (by rfl) ⟨3653234, by rfl⟩ : syracuseStep 4870979 = 7306469) B7306469
theorem B3247319 : Blo 2163435 3247319 := bstep (se 1 (by rfl) ⟨2435489, by rfl⟩ : syracuseStep 3247319 = 4870979) B4870979
theorem B2164879 : Blo 2163435 2164879 := bstep (se 1 (by rfl) ⟨1623659, by rfl⟩ : syracuseStep 2164879 = 3247319) B3247319
theorem B3247325 : Blo 2163435 3247325 := bbase (se 3 (by rfl) ⟨608873, by rfl⟩ : syracuseStep 3247325 = 1217747) (by norm_num)
theorem B2164883 : Blo 2163435 2164883 := bstep (se 1 (by rfl) ⟨1623662, by rfl⟩ : syracuseStep 2164883 = 3247325) B3247325
theorem B4870997 : Blo 2163435 4870997 := bbase (se 9 (by rfl) ⟨14270, by rfl⟩ : syracuseStep 4870997 = 28541) (by norm_num)
theorem B3247331 : Blo 2163435 3247331 := bstep (se 1 (by rfl) ⟨2435498, by rfl⟩ : syracuseStep 3247331 = 4870997) B4870997
theorem B2164887 : Blo 2163435 2164887 := bstep (se 1 (by rfl) ⟨1623665, by rfl⟩ : syracuseStep 2164887 = 3247331) B3247331
theorem B6164869 : Blo 2163435 6164869 := bbase (se 4 (by rfl) ⟨577956, by rfl⟩ : syracuseStep 6164869 = 1155913) (by norm_num)
theorem B8219825 : Blo 2163435 8219825 := bstep (se 2 (by rfl) ⟨3082434, by rfl⟩ : syracuseStep 8219825 = 6164869) B6164869
theorem B5479883 : Blo 2163435 5479883 := bstep (se 1 (by rfl) ⟨4109912, by rfl⟩ : syracuseStep 5479883 = 8219825) B8219825
theorem B3653255 : Blo 2163435 3653255 := bstep (se 1 (by rfl) ⟨2739941, by rfl⟩ : syracuseStep 3653255 = 5479883) B5479883
theorem B2435503 : Blo 2163435 2435503 := bstep (se 1 (by rfl) ⟨1826627, by rfl⟩ : syracuseStep 2435503 = 3653255) B3653255
theorem B3247337 : Blo 2163435 3247337 := bstep (se 2 (by rfl) ⟨1217751, by rfl⟩ : syracuseStep 3247337 = 2435503) B2435503
theorem B2164891 : Blo 2163435 2164891 := bstep (se 1 (by rfl) ⟨1623668, by rfl⟩ : syracuseStep 2164891 = 3247337) B3247337
theorem B2777329 : Blo 2163435 2777329 := bbase (se 2 (by rfl) ⟨1041498, by rfl⟩ : syracuseStep 2777329 = 2082997) (by norm_num)
theorem B3703105 : Blo 2163435 3703105 := bstep (se 2 (by rfl) ⟨1388664, by rfl⟩ : syracuseStep 3703105 = 2777329) B2777329
theorem B4937473 : Blo 2163435 4937473 := bstep (se 2 (by rfl) ⟨1851552, by rfl⟩ : syracuseStep 4937473 = 3703105) B3703105
theorem B26333189 : Blo 2163435 26333189 := bstep (se 4 (by rfl) ⟨2468736, by rfl⟩ : syracuseStep 26333189 = 4937473) B4937473
theorem B17555459 : Blo 2163435 17555459 := bstep (se 1 (by rfl) ⟨13166594, by rfl⟩ : syracuseStep 17555459 = 26333189) B26333189
theorem B46814557 : Blo 2163435 46814557 := bstep (se 3 (by rfl) ⟨8777729, by rfl⟩ : syracuseStep 46814557 = 17555459) B17555459
theorem B62419409 : Blo 2163435 62419409 := bstep (se 2 (by rfl) ⟨23407278, by rfl⟩ : syracuseStep 62419409 = 46814557) B46814557
theorem B41612939 : Blo 2163435 41612939 := bstep (se 1 (by rfl) ⟨31209704, by rfl⟩ : syracuseStep 41612939 = 62419409) B62419409
theorem B27741959 : Blo 2163435 27741959 := bstep (se 1 (by rfl) ⟨20806469, by rfl⟩ : syracuseStep 27741959 = 41612939) B41612939
theorem B18494639 : Blo 2163435 18494639 := bstep (se 1 (by rfl) ⟨13870979, by rfl⟩ : syracuseStep 18494639 = 27741959) B27741959
theorem B12329759 : Blo 2163435 12329759 := bstep (se 1 (by rfl) ⟨9247319, by rfl⟩ : syracuseStep 12329759 = 18494639) B18494639
theorem B8219839 : Blo 2163435 8219839 := bstep (se 1 (by rfl) ⟨6164879, by rfl⟩ : syracuseStep 8219839 = 12329759) B12329759
theorem B10959785 : Blo 2163435 10959785 := bstep (se 2 (by rfl) ⟨4109919, by rfl⟩ : syracuseStep 10959785 = 8219839) B8219839
theorem B7306523 : Blo 2163435 7306523 := bstep (se 1 (by rfl) ⟨5479892, by rfl⟩ : syracuseStep 7306523 = 10959785) B10959785
theorem B4871015 : Blo 2163435 4871015 := bstep (se 1 (by rfl) ⟨3653261, by rfl⟩ : syracuseStep 4871015 = 7306523) B7306523
theorem B3247343 : Blo 2163435 3247343 := bstep (se 1 (by rfl) ⟨2435507, by rfl⟩ : syracuseStep 3247343 = 4871015) B4871015
theorem B2164895 : Blo 2163435 2164895 := bstep (se 1 (by rfl) ⟨1623671, by rfl⟩ : syracuseStep 2164895 = 3247343) B3247343
theorem B3247349 : Blo 2163435 3247349 := bbase (se 5 (by rfl) ⟨152219, by rfl⟩ : syracuseStep 3247349 = 304439) (by norm_num)
theorem B2164899 : Blo 2163435 2164899 := bstep (se 1 (by rfl) ⟨1623674, by rfl⟩ : syracuseStep 2164899 = 3247349) B3247349
theorem B2194441 : Blo 2163435 2194441 := bbase (se 2 (by rfl) ⟨822915, by rfl⟩ : syracuseStep 2194441 = 1645831) (by norm_num)
theorem B11703685 : Blo 2163435 11703685 := bstep (se 4 (by rfl) ⟨1097220, by rfl⟩ : syracuseStep 11703685 = 2194441) B2194441
theorem B15604913 : Blo 2163435 15604913 := bstep (se 2 (by rfl) ⟨5851842, by rfl⟩ : syracuseStep 15604913 = 11703685) B11703685
theorem B10403275 : Blo 2163435 10403275 := bstep (se 1 (by rfl) ⟨7802456, by rfl⟩ : syracuseStep 10403275 = 15604913) B15604913
theorem B13871033 : Blo 2163435 13871033 := bstep (se 2 (by rfl) ⟨5201637, by rfl⟩ : syracuseStep 13871033 = 10403275) B10403275
theorem B9247355 : Blo 2163435 9247355 := bstep (se 1 (by rfl) ⟨6935516, by rfl⟩ : syracuseStep 9247355 = 13871033) B13871033
theorem B6164903 : Blo 2163435 6164903 := bstep (se 1 (by rfl) ⟨4623677, by rfl⟩ : syracuseStep 6164903 = 9247355) B9247355
theorem B4109935 : Blo 2163435 4109935 := bstep (se 1 (by rfl) ⟨3082451, by rfl⟩ : syracuseStep 4109935 = 6164903) B6164903
theorem B5479913 : Blo 2163435 5479913 := bstep (se 2 (by rfl) ⟨2054967, by rfl⟩ : syracuseStep 5479913 = 4109935) B4109935
theorem B3653275 : Blo 2163435 3653275 := bstep (se 1 (by rfl) ⟨2739956, by rfl⟩ : syracuseStep 3653275 = 5479913) B5479913
theorem B4871033 : Blo 2163435 4871033 := bstep (se 2 (by rfl) ⟨1826637, by rfl⟩ : syracuseStep 4871033 = 3653275) B3653275
theorem B3247355 : Blo 2163435 3247355 := bstep (se 1 (by rfl) ⟨2435516, by rfl⟩ : syracuseStep 3247355 = 4871033) B4871033
theorem B2164903 : Blo 2163435 2164903 := bstep (se 1 (by rfl) ⟨1623677, by rfl⟩ : syracuseStep 2164903 = 3247355) B3247355
theorem B2435521 : Blo 2163435 2435521 := bbase (se 2 (by rfl) ⟨913320, by rfl⟩ : syracuseStep 2435521 = 1826641) (by norm_num)
theorem B3247361 : Blo 2163435 3247361 := bstep (se 2 (by rfl) ⟨1217760, by rfl⟩ : syracuseStep 3247361 = 2435521) B2435521
theorem B2164907 : Blo 2163435 2164907 := bstep (se 1 (by rfl) ⟨1623680, by rfl⟩ : syracuseStep 2164907 = 3247361) B3247361
theorem B5479933 : Blo 2163435 5479933 := bbase (se 3 (by rfl) ⟨1027487, by rfl⟩ : syracuseStep 5479933 = 2054975) (by norm_num)
theorem B7306577 : Blo 2163435 7306577 := bstep (se 2 (by rfl) ⟨2739966, by rfl⟩ : syracuseStep 7306577 = 5479933) B5479933
theorem B4871051 : Blo 2163435 4871051 := bstep (se 1 (by rfl) ⟨3653288, by rfl⟩ : syracuseStep 4871051 = 7306577) B7306577
theorem B3247367 : Blo 2163435 3247367 := bstep (se 1 (by rfl) ⟨2435525, by rfl⟩ : syracuseStep 3247367 = 4871051) B4871051
theorem B2164911 : Blo 2163435 2164911 := bstep (se 1 (by rfl) ⟨1623683, by rfl⟩ : syracuseStep 2164911 = 3247367) B3247367
theorem B3247373 : Blo 2163435 3247373 := bbase (se 3 (by rfl) ⟨608882, by rfl⟩ : syracuseStep 3247373 = 1217765) (by norm_num)
theorem B2164915 : Blo 2163435 2164915 := bstep (se 1 (by rfl) ⟨1623686, by rfl⟩ : syracuseStep 2164915 = 3247373) B3247373
theorem B4871069 : Blo 2163435 4871069 := bbase (se 3 (by rfl) ⟨913325, by rfl⟩ : syracuseStep 4871069 = 1826651) (by norm_num)
theorem B3247379 : Blo 2163435 3247379 := bstep (se 1 (by rfl) ⟨2435534, by rfl⟩ : syracuseStep 3247379 = 4871069) B4871069
theorem B2164919 : Blo 2163435 2164919 := bstep (se 1 (by rfl) ⟨1623689, by rfl⟩ : syracuseStep 2164919 = 3247379) B3247379
theorem B3653309 : Blo 2163435 3653309 := bbase (se 3 (by rfl) ⟨684995, by rfl⟩ : syracuseStep 3653309 = 1369991) (by norm_num)
theorem B2435539 : Blo 2163435 2435539 := bstep (se 1 (by rfl) ⟨1826654, by rfl⟩ : syracuseStep 2435539 = 3653309) B3653309
theorem B3247385 : Blo 2163435 3247385 := bstep (se 2 (by rfl) ⟨1217769, by rfl⟩ : syracuseStep 3247385 = 2435539) B2435539
theorem B2164923 : Blo 2163435 2164923 := bstep (se 1 (by rfl) ⟨1623692, by rfl⟩ : syracuseStep 2164923 = 3247385) B3247385
theorem B12329941 : Blo 2163435 12329941 := bbase (se 7 (by rfl) ⟨144491, by rfl⟩ : syracuseStep 12329941 = 288983) (by norm_num)
theorem B16439921 : Blo 2163435 16439921 := bstep (se 2 (by rfl) ⟨6164970, by rfl⟩ : syracuseStep 16439921 = 12329941) B12329941
theorem B10959947 : Blo 2163435 10959947 := bstep (se 1 (by rfl) ⟨8219960, by rfl⟩ : syracuseStep 10959947 = 16439921) B16439921
theorem B7306631 : Blo 2163435 7306631 := bstep (se 1 (by rfl) ⟨5479973, by rfl⟩ : syracuseStep 7306631 = 10959947) B10959947
theorem B4871087 : Blo 2163435 4871087 := bstep (se 1 (by rfl) ⟨3653315, by rfl⟩ : syracuseStep 4871087 = 7306631) B7306631
theorem B3247391 : Blo 2163435 3247391 := bstep (se 1 (by rfl) ⟨2435543, by rfl⟩ : syracuseStep 3247391 = 4871087) B4871087
theorem B2164927 : Blo 2163435 2164927 := bstep (se 1 (by rfl) ⟨1623695, by rfl⟩ : syracuseStep 2164927 = 3247391) B3247391
theorem B3247397 : Blo 2163435 3247397 := bbase (se 4 (by rfl) ⟨304443, by rfl⟩ : syracuseStep 3247397 = 608887) (by norm_num)
theorem B2164931 : Blo 2163435 2164931 := bstep (se 1 (by rfl) ⟨1623698, by rfl⟩ : syracuseStep 2164931 = 3247397) B3247397
theorem B2739997 : Blo 2163435 2739997 := bbase (se 3 (by rfl) ⟨513749, by rfl⟩ : syracuseStep 2739997 = 1027499) (by norm_num)
theorem B3653329 : Blo 2163435 3653329 := bstep (se 2 (by rfl) ⟨1369998, by rfl⟩ : syracuseStep 3653329 = 2739997) B2739997
theorem B4871105 : Blo 2163435 4871105 := bstep (se 2 (by rfl) ⟨1826664, by rfl⟩ : syracuseStep 4871105 = 3653329) B3653329
theorem B3247403 : Blo 2163435 3247403 := bstep (se 1 (by rfl) ⟨2435552, by rfl⟩ : syracuseStep 3247403 = 4871105) B4871105
theorem B2164935 : Blo 2163435 2164935 := bstep (se 1 (by rfl) ⟨1623701, by rfl⟩ : syracuseStep 2164935 = 3247403) B3247403
theorem B2435557 : Blo 2163435 2435557 := bbase (se 4 (by rfl) ⟨228333, by rfl⟩ : syracuseStep 2435557 = 456667) (by norm_num)
theorem B3247409 : Blo 2163435 3247409 := bstep (se 2 (by rfl) ⟨1217778, by rfl⟩ : syracuseStep 3247409 = 2435557) B2435557
theorem B2164939 : Blo 2163435 2164939 := bstep (se 1 (by rfl) ⟨1623704, by rfl⟩ : syracuseStep 2164939 = 3247409) B3247409
theorem B3901301 : Blo 2163435 3901301 := bbase (se 5 (by rfl) ⟨182873, by rfl⟩ : syracuseStep 3901301 = 365747) (by norm_num)
theorem B2600867 : Blo 2163435 2600867 := bstep (se 1 (by rfl) ⟨1950650, by rfl⟩ : syracuseStep 2600867 = 3901301) B3901301
theorem B6935645 : Blo 2163435 6935645 := bstep (se 3 (by rfl) ⟨1300433, by rfl⟩ : syracuseStep 6935645 = 2600867) B2600867
theorem B4623763 : Blo 2163435 4623763 := bstep (se 1 (by rfl) ⟨3467822, by rfl⟩ : syracuseStep 4623763 = 6935645) B6935645
theorem B6165017 : Blo 2163435 6165017 := bstep (se 2 (by rfl) ⟨2311881, by rfl⟩ : syracuseStep 6165017 = 4623763) B4623763
theorem B4110011 : Blo 2163435 4110011 := bstep (se 1 (by rfl) ⟨3082508, by rfl⟩ : syracuseStep 4110011 = 6165017) B6165017
theorem B2740007 : Blo 2163435 2740007 := bstep (se 1 (by rfl) ⟨2055005, by rfl⟩ : syracuseStep 2740007 = 4110011) B4110011
theorem B7306685 : Blo 2163435 7306685 := bstep (se 3 (by rfl) ⟨1370003, by rfl⟩ : syracuseStep 7306685 = 2740007) B2740007
theorem B4871123 : Blo 2163435 4871123 := bstep (se 1 (by rfl) ⟨3653342, by rfl⟩ : syracuseStep 4871123 = 7306685) B7306685
theorem B3247415 : Blo 2163435 3247415 := bstep (se 1 (by rfl) ⟨2435561, by rfl⟩ : syracuseStep 3247415 = 4871123) B4871123
theorem B2164943 : Blo 2163435 2164943 := bstep (se 1 (by rfl) ⟨1623707, by rfl⟩ : syracuseStep 2164943 = 3247415) B3247415
theorem B3247421 : Blo 2163435 3247421 := bbase (se 3 (by rfl) ⟨608891, by rfl⟩ : syracuseStep 3247421 = 1217783) (by norm_num)
theorem B2164947 : Blo 2163435 2164947 := bstep (se 1 (by rfl) ⟨1623710, by rfl⟩ : syracuseStep 2164947 = 3247421) B3247421
theorem B4871141 : Blo 2163435 4871141 := bbase (se 4 (by rfl) ⟨456669, by rfl⟩ : syracuseStep 4871141 = 913339) (by norm_num)
theorem B3247427 : Blo 2163435 3247427 := bstep (se 1 (by rfl) ⟨2435570, by rfl⟩ : syracuseStep 3247427 = 4871141) B4871141
theorem B2164951 : Blo 2163435 2164951 := bstep (se 1 (by rfl) ⟨1623713, by rfl⟩ : syracuseStep 2164951 = 3247427) B3247427
theorem B5480045 : Blo 2163435 5480045 := bbase (se 3 (by rfl) ⟨1027508, by rfl⟩ : syracuseStep 5480045 = 2055017) (by norm_num)
theorem B3653363 : Blo 2163435 3653363 := bstep (se 1 (by rfl) ⟨2740022, by rfl⟩ : syracuseStep 3653363 = 5480045) B5480045
theorem B2435575 : Blo 2163435 2435575 := bstep (se 1 (by rfl) ⟨1826681, by rfl⟩ : syracuseStep 2435575 = 3653363) B3653363
theorem B3247433 : Blo 2163435 3247433 := bstep (se 2 (by rfl) ⟨1217787, by rfl⟩ : syracuseStep 3247433 = 2435575) B2435575
theorem B2164955 : Blo 2163435 2164955 := bstep (se 1 (by rfl) ⟨1623716, by rfl⟩ : syracuseStep 2164955 = 3247433) B3247433
theorem B4623797 : Blo 2163435 4623797 := bbase (se 5 (by rfl) ⟨216740, by rfl⟩ : syracuseStep 4623797 = 433481) (by norm_num)
theorem B3082531 : Blo 2163435 3082531 := bstep (se 1 (by rfl) ⟨2311898, by rfl⟩ : syracuseStep 3082531 = 4623797) B4623797
theorem B4110041 : Blo 2163435 4110041 := bstep (se 2 (by rfl) ⟨1541265, by rfl⟩ : syracuseStep 4110041 = 3082531) B3082531
theorem B10960109 : Blo 2163435 10960109 := bstep (se 3 (by rfl) ⟨2055020, by rfl⟩ : syracuseStep 10960109 = 4110041) B4110041
theorem B7306739 : Blo 2163435 7306739 := bstep (se 1 (by rfl) ⟨5480054, by rfl⟩ : syracuseStep 7306739 = 10960109) B10960109
theorem B4871159 : Blo 2163435 4871159 := bstep (se 1 (by rfl) ⟨3653369, by rfl⟩ : syracuseStep 4871159 = 7306739) B7306739
theorem B3247439 : Blo 2163435 3247439 := bstep (se 1 (by rfl) ⟨2435579, by rfl⟩ : syracuseStep 3247439 = 4871159) B4871159
theorem B2164959 : Blo 2163435 2164959 := bstep (se 1 (by rfl) ⟨1623719, by rfl⟩ : syracuseStep 2164959 = 3247439) B3247439
theorem B3247445 : Blo 2163435 3247445 := bbase (se 11 (by rfl) ⟨2378, by rfl⟩ : syracuseStep 3247445 = 4757) (by norm_num)
theorem B2164963 : Blo 2163435 2164963 := bstep (se 1 (by rfl) ⟨1623722, by rfl⟩ : syracuseStep 2164963 = 3247445) B3247445
theorem B3467861 : Blo 2163435 3467861 := bbase (se 8 (by rfl) ⟨20319, by rfl⟩ : syracuseStep 3467861 = 40639) (by norm_num)
theorem B2311907 : Blo 2163435 2311907 := bstep (se 1 (by rfl) ⟨1733930, by rfl⟩ : syracuseStep 2311907 = 3467861) B3467861
theorem B6165085 : Blo 2163435 6165085 := bstep (se 3 (by rfl) ⟨1155953, by rfl⟩ : syracuseStep 6165085 = 2311907) B2311907
theorem B8220113 : Blo 2163435 8220113 := bstep (se 2 (by rfl) ⟨3082542, by rfl⟩ : syracuseStep 8220113 = 6165085) B6165085
theorem B5480075 : Blo 2163435 5480075 := bstep (se 1 (by rfl) ⟨4110056, by rfl⟩ : syracuseStep 5480075 = 8220113) B8220113
theorem B3653383 : Blo 2163435 3653383 := bstep (se 1 (by rfl) ⟨2740037, by rfl⟩ : syracuseStep 3653383 = 5480075) B5480075
theorem B4871177 : Blo 2163435 4871177 := bstep (se 2 (by rfl) ⟨1826691, by rfl⟩ : syracuseStep 4871177 = 3653383) B3653383
theorem B3247451 : Blo 2163435 3247451 := bstep (se 1 (by rfl) ⟨2435588, by rfl⟩ : syracuseStep 3247451 = 4871177) B4871177
theorem B2164967 : Blo 2163435 2164967 := bstep (se 1 (by rfl) ⟨1623725, by rfl⟩ : syracuseStep 2164967 = 3247451) B3247451
theorem B2435593 : Blo 2163435 2435593 := bbase (se 2 (by rfl) ⟨913347, by rfl⟩ : syracuseStep 2435593 = 1826695) (by norm_num)
theorem B3247457 : Blo 2163435 3247457 := bstep (se 2 (by rfl) ⟨1217796, by rfl⟩ : syracuseStep 3247457 = 2435593) B2435593
theorem B2164971 : Blo 2163435 2164971 := bstep (se 1 (by rfl) ⟨1623728, by rfl⟩ : syracuseStep 2164971 = 3247457) B3247457
theorem B4448909 : Blo 2163435 4448909 := bbase (se 3 (by rfl) ⟨834170, by rfl⟩ : syracuseStep 4448909 = 1668341) (by norm_num)
theorem B2965939 : Blo 2163435 2965939 := bstep (se 1 (by rfl) ⟨2224454, by rfl⟩ : syracuseStep 2965939 = 4448909) B4448909
theorem B15818341 : Blo 2163435 15818341 := bstep (se 4 (by rfl) ⟨1482969, by rfl⟩ : syracuseStep 15818341 = 2965939) B2965939
theorem B21091121 : Blo 2163435 21091121 := bstep (se 2 (by rfl) ⟨7909170, by rfl⟩ : syracuseStep 21091121 = 15818341) B15818341
theorem B14060747 : Blo 2163435 14060747 := bstep (se 1 (by rfl) ⟨10545560, by rfl⟩ : syracuseStep 14060747 = 21091121) B21091121
theorem B37495325 : Blo 2163435 37495325 := bstep (se 3 (by rfl) ⟨7030373, by rfl⟩ : syracuseStep 37495325 = 14060747) B14060747
theorem B24996883 : Blo 2163435 24996883 := bstep (se 1 (by rfl) ⟨18747662, by rfl⟩ : syracuseStep 24996883 = 37495325) B37495325
theorem B33329177 : Blo 2163435 33329177 := bstep (se 2 (by rfl) ⟨12498441, by rfl⟩ : syracuseStep 33329177 = 24996883) B24996883
theorem B22219451 : Blo 2163435 22219451 := bstep (se 1 (by rfl) ⟨16664588, by rfl⟩ : syracuseStep 22219451 = 33329177) B33329177
theorem B14812967 : Blo 2163435 14812967 := bstep (se 1 (by rfl) ⟨11109725, by rfl⟩ : syracuseStep 14812967 = 22219451) B22219451
theorem B39501245 : Blo 2163435 39501245 := bstep (se 3 (by rfl) ⟨7406483, by rfl⟩ : syracuseStep 39501245 = 14812967) B14812967
theorem B26334163 : Blo 2163435 26334163 := bstep (se 1 (by rfl) ⟨19750622, by rfl⟩ : syracuseStep 26334163 = 39501245) B39501245
theorem B35112217 : Blo 2163435 35112217 := bstep (se 2 (by rfl) ⟨13167081, by rfl⟩ : syracuseStep 35112217 = 26334163) B26334163
theorem B46816289 : Blo 2163435 46816289 := bstep (se 2 (by rfl) ⟨17556108, by rfl⟩ : syracuseStep 46816289 = 35112217) B35112217
theorem B31210859 : Blo 2163435 31210859 := bstep (se 1 (by rfl) ⟨23408144, by rfl⟩ : syracuseStep 31210859 = 46816289) B46816289
theorem B20807239 : Blo 2163435 20807239 := bstep (se 1 (by rfl) ⟨15605429, by rfl⟩ : syracuseStep 20807239 = 31210859) B31210859
theorem B27742985 : Blo 2163435 27742985 := bstep (se 2 (by rfl) ⟨10403619, by rfl⟩ : syracuseStep 27742985 = 20807239) B20807239
theorem B18495323 : Blo 2163435 18495323 := bstep (se 1 (by rfl) ⟨13871492, by rfl⟩ : syracuseStep 18495323 = 27742985) B27742985
theorem B12330215 : Blo 2163435 12330215 := bstep (se 1 (by rfl) ⟨9247661, by rfl⟩ : syracuseStep 12330215 = 18495323) B18495323
theorem B8220143 : Blo 2163435 8220143 := bstep (se 1 (by rfl) ⟨6165107, by rfl⟩ : syracuseStep 8220143 = 12330215) B12330215
theorem B5480095 : Blo 2163435 5480095 := bstep (se 1 (by rfl) ⟨4110071, by rfl⟩ : syracuseStep 5480095 = 8220143) B8220143
theorem B7306793 : Blo 2163435 7306793 := bstep (se 2 (by rfl) ⟨2740047, by rfl⟩ : syracuseStep 7306793 = 5480095) B5480095
theorem B4871195 : Blo 2163435 4871195 := bstep (se 1 (by rfl) ⟨3653396, by rfl⟩ : syracuseStep 4871195 = 7306793) B7306793
theorem B3247463 : Blo 2163435 3247463 := bstep (se 1 (by rfl) ⟨2435597, by rfl⟩ : syracuseStep 3247463 = 4871195) B4871195
theorem B2164975 : Blo 2163435 2164975 := bstep (se 1 (by rfl) ⟨1623731, by rfl⟩ : syracuseStep 2164975 = 3247463) B3247463
theorem B3247469 : Blo 2163435 3247469 := bbase (se 3 (by rfl) ⟨608900, by rfl⟩ : syracuseStep 3247469 = 1217801) (by norm_num)
theorem B2164979 : Blo 2163435 2164979 := bstep (se 1 (by rfl) ⟨1623734, by rfl⟩ : syracuseStep 2164979 = 3247469) B3247469
theorem B4871213 : Blo 2163435 4871213 := bbase (se 3 (by rfl) ⟨913352, by rfl⟩ : syracuseStep 4871213 = 1826705) (by norm_num)
theorem B3247475 : Blo 2163435 3247475 := bstep (se 1 (by rfl) ⟨2435606, by rfl⟩ : syracuseStep 3247475 = 4871213) B4871213
theorem B2164983 : Blo 2163435 2164983 := bstep (se 1 (by rfl) ⟨1623737, by rfl⟩ : syracuseStep 2164983 = 3247475) B3247475
theorem B13871573 : Blo 2163435 13871573 := bbase (se 7 (by rfl) ⟨162557, by rfl⟩ : syracuseStep 13871573 = 325115) (by norm_num)
theorem B9247715 : Blo 2163435 9247715 := bstep (se 1 (by rfl) ⟨6935786, by rfl⟩ : syracuseStep 9247715 = 13871573) B13871573
theorem B6165143 : Blo 2163435 6165143 := bstep (se 1 (by rfl) ⟨4623857, by rfl⟩ : syracuseStep 6165143 = 9247715) B9247715
theorem B4110095 : Blo 2163435 4110095 := bstep (se 1 (by rfl) ⟨3082571, by rfl⟩ : syracuseStep 4110095 = 6165143) B6165143
theorem B2740063 : Blo 2163435 2740063 := bstep (se 1 (by rfl) ⟨2055047, by rfl⟩ : syracuseStep 2740063 = 4110095) B4110095
theorem B3653417 : Blo 2163435 3653417 := bstep (se 2 (by rfl) ⟨1370031, by rfl⟩ : syracuseStep 3653417 = 2740063) B2740063
theorem B2435611 : Blo 2163435 2435611 := bstep (se 1 (by rfl) ⟨1826708, by rfl⟩ : syracuseStep 2435611 = 3653417) B3653417
theorem B3247481 : Blo 2163435 3247481 := bstep (se 2 (by rfl) ⟨1217805, by rfl⟩ : syracuseStep 3247481 = 2435611) B2435611
theorem B2164987 : Blo 2163435 2164987 := bstep (se 1 (by rfl) ⟨1623740, by rfl⟩ : syracuseStep 2164987 = 3247481) B3247481
theorem B6935797 : Blo 2163435 6935797 := bbase (se 5 (by rfl) ⟨325115, by rfl⟩ : syracuseStep 6935797 = 650231) (by norm_num)
theorem B36990917 : Blo 2163435 36990917 := bstep (se 4 (by rfl) ⟨3467898, by rfl⟩ : syracuseStep 36990917 = 6935797) B6935797
theorem B24660611 : Blo 2163435 24660611 := bstep (se 1 (by rfl) ⟨18495458, by rfl⟩ : syracuseStep 24660611 = 36990917) B36990917
theorem B16440407 : Blo 2163435 16440407 := bstep (se 1 (by rfl) ⟨12330305, by rfl⟩ : syracuseStep 16440407 = 24660611) B24660611
theorem B10960271 : Blo 2163435 10960271 := bstep (se 1 (by rfl) ⟨8220203, by rfl⟩ : syracuseStep 10960271 = 16440407) B16440407
theorem B7306847 : Blo 2163435 7306847 := bstep (se 1 (by rfl) ⟨5480135, by rfl⟩ : syracuseStep 7306847 = 10960271) B10960271
theorem B4871231 : Blo 2163435 4871231 := bstep (se 1 (by rfl) ⟨3653423, by rfl⟩ : syracuseStep 4871231 = 7306847) B7306847
theorem B3247487 : Blo 2163435 3247487 := bstep (se 1 (by rfl) ⟨2435615, by rfl⟩ : syracuseStep 3247487 = 4871231) B4871231
theorem B2164991 : Blo 2163435 2164991 := bstep (se 1 (by rfl) ⟨1623743, by rfl⟩ : syracuseStep 2164991 = 3247487) B3247487
theorem B3247493 : Blo 2163435 3247493 := bbase (se 4 (by rfl) ⟨304452, by rfl⟩ : syracuseStep 3247493 = 608905) (by norm_num)
theorem B2164995 : Blo 2163435 2164995 := bstep (se 1 (by rfl) ⟨1623746, by rfl⟩ : syracuseStep 2164995 = 3247493) B3247493
theorem B3653437 : Blo 2163435 3653437 := bbase (se 3 (by rfl) ⟨685019, by rfl⟩ : syracuseStep 3653437 = 1370039) (by norm_num)
theorem B4871249 : Blo 2163435 4871249 := bstep (se 2 (by rfl) ⟨1826718, by rfl⟩ : syracuseStep 4871249 = 3653437) B3653437
theorem B3247499 : Blo 2163435 3247499 := bstep (se 1 (by rfl) ⟨2435624, by rfl⟩ : syracuseStep 3247499 = 4871249) B4871249
theorem B2164999 : Blo 2163435 2164999 := bstep (se 1 (by rfl) ⟨1623749, by rfl⟩ : syracuseStep 2164999 = 3247499) B3247499
theorem B2435629 : Blo 2163435 2435629 := bbase (se 3 (by rfl) ⟨456680, by rfl⟩ : syracuseStep 2435629 = 913361) (by norm_num)
theorem B3247505 : Blo 2163435 3247505 := bstep (se 2 (by rfl) ⟨1217814, by rfl⟩ : syracuseStep 3247505 = 2435629) B2435629
theorem B2165003 : Blo 2163435 2165003 := bstep (se 1 (by rfl) ⟨1623752, by rfl⟩ : syracuseStep 2165003 = 3247505) B3247505
theorem B7306901 : Blo 2163435 7306901 := bbase (se 6 (by rfl) ⟨171255, by rfl⟩ : syracuseStep 7306901 = 342511) (by norm_num)
theorem B4871267 : Blo 2163435 4871267 := bstep (se 1 (by rfl) ⟨3653450, by rfl⟩ : syracuseStep 4871267 = 7306901) B7306901
theorem B3247511 : Blo 2163435 3247511 := bstep (se 1 (by rfl) ⟨2435633, by rfl⟩ : syracuseStep 3247511 = 4871267) B4871267
theorem B2165007 : Blo 2163435 2165007 := bstep (se 1 (by rfl) ⟨1623755, by rfl⟩ : syracuseStep 2165007 = 3247511) B3247511
theorem B3247517 : Blo 2163435 3247517 := bbase (se 3 (by rfl) ⟨608909, by rfl⟩ : syracuseStep 3247517 = 1217819) (by norm_num)
theorem B2165011 : Blo 2163435 2165011 := bstep (se 1 (by rfl) ⟨1623758, by rfl⟩ : syracuseStep 2165011 = 3247517) B3247517
theorem B4871285 : Blo 2163435 4871285 := bbase (se 5 (by rfl) ⟨228341, by rfl⟩ : syracuseStep 4871285 = 456683) (by norm_num)
theorem B3247523 : Blo 2163435 3247523 := bstep (se 1 (by rfl) ⟨2435642, by rfl⟩ : syracuseStep 3247523 = 4871285) B4871285
theorem B2165015 : Blo 2163435 2165015 := bstep (se 1 (by rfl) ⟨1623761, by rfl⟩ : syracuseStep 2165015 = 3247523) B3247523
theorem B18495701 : Blo 2163435 18495701 := bbase (se 7 (by rfl) ⟨216746, by rfl⟩ : syracuseStep 18495701 = 433493) (by norm_num)
theorem B12330467 : Blo 2163435 12330467 := bstep (se 1 (by rfl) ⟨9247850, by rfl⟩ : syracuseStep 12330467 = 18495701) B18495701
theorem B8220311 : Blo 2163435 8220311 := bstep (se 1 (by rfl) ⟨6165233, by rfl⟩ : syracuseStep 8220311 = 12330467) B12330467
theorem B5480207 : Blo 2163435 5480207 := bstep (se 1 (by rfl) ⟨4110155, by rfl⟩ : syracuseStep 5480207 = 8220311) B8220311
theorem B3653471 : Blo 2163435 3653471 := bstep (se 1 (by rfl) ⟨2740103, by rfl⟩ : syracuseStep 3653471 = 5480207) B5480207
theorem B2435647 : Blo 2163435 2435647 := bstep (se 1 (by rfl) ⟨1826735, by rfl⟩ : syracuseStep 2435647 = 3653471) B3653471
theorem B3247529 : Blo 2163435 3247529 := bstep (se 2 (by rfl) ⟨1217823, by rfl⟩ : syracuseStep 3247529 = 2435647) B2435647
theorem B2165019 : Blo 2163435 2165019 := bstep (se 1 (by rfl) ⟨1623764, by rfl⟩ : syracuseStep 2165019 = 3247529) B3247529
theorem B8220325 : Blo 2163435 8220325 := bbase (se 4 (by rfl) ⟨770655, by rfl⟩ : syracuseStep 8220325 = 1541311) (by norm_num)
theorem B10960433 : Blo 2163435 10960433 := bstep (se 2 (by rfl) ⟨4110162, by rfl⟩ : syracuseStep 10960433 = 8220325) B8220325
theorem B7306955 : Blo 2163435 7306955 := bstep (se 1 (by rfl) ⟨5480216, by rfl⟩ : syracuseStep 7306955 = 10960433) B10960433
theorem B4871303 : Blo 2163435 4871303 := bstep (se 1 (by rfl) ⟨3653477, by rfl⟩ : syracuseStep 4871303 = 7306955) B7306955
theorem B3247535 : Blo 2163435 3247535 := bstep (se 1 (by rfl) ⟨2435651, by rfl⟩ : syracuseStep 3247535 = 4871303) B4871303
theorem B2165023 : Blo 2163435 2165023 := bstep (se 1 (by rfl) ⟨1623767, by rfl⟩ : syracuseStep 2165023 = 3247535) B3247535
theorem B3247541 : Blo 2163435 3247541 := bbase (se 5 (by rfl) ⟨152228, by rfl⟩ : syracuseStep 3247541 = 304457) (by norm_num)
theorem B2165027 : Blo 2163435 2165027 := bstep (se 1 (by rfl) ⟨1623770, by rfl⟩ : syracuseStep 2165027 = 3247541) B3247541
theorem B5480237 : Blo 2163435 5480237 := bbase (se 3 (by rfl) ⟨1027544, by rfl⟩ : syracuseStep 5480237 = 2055089) (by norm_num)
theorem B3653491 : Blo 2163435 3653491 := bstep (se 1 (by rfl) ⟨2740118, by rfl⟩ : syracuseStep 3653491 = 5480237) B5480237
theorem B4871321 : Blo 2163435 4871321 := bstep (se 2 (by rfl) ⟨1826745, by rfl⟩ : syracuseStep 4871321 = 3653491) B3653491
theorem B3247547 : Blo 2163435 3247547 := bstep (se 1 (by rfl) ⟨2435660, by rfl⟩ : syracuseStep 3247547 = 4871321) B4871321
theorem B2165031 : Blo 2163435 2165031 := bstep (se 1 (by rfl) ⟨1623773, by rfl⟩ : syracuseStep 2165031 = 3247547) B3247547
theorem B2435665 : Blo 2163435 2435665 := bbase (se 2 (by rfl) ⟨913374, by rfl⟩ : syracuseStep 2435665 = 1826749) (by norm_num)
theorem B3247553 : Blo 2163435 3247553 := bstep (se 2 (by rfl) ⟨1217832, by rfl⟩ : syracuseStep 3247553 = 2435665) B2435665
theorem B2165035 : Blo 2163435 2165035 := bstep (se 1 (by rfl) ⟨1623776, by rfl⟩ : syracuseStep 2165035 = 3247553) B3247553
theorem B3082645 : Blo 2163435 3082645 := bbase (se 6 (by rfl) ⟨72249, by rfl⟩ : syracuseStep 3082645 = 144499) (by norm_num)
theorem B4110193 : Blo 2163435 4110193 := bstep (se 2 (by rfl) ⟨1541322, by rfl⟩ : syracuseStep 4110193 = 3082645) B3082645
theorem B5480257 : Blo 2163435 5480257 := bstep (se 2 (by rfl) ⟨2055096, by rfl⟩ : syracuseStep 5480257 = 4110193) B4110193
theorem B7307009 : Blo 2163435 7307009 := bstep (se 2 (by rfl) ⟨2740128, by rfl⟩ : syracuseStep 7307009 = 5480257) B5480257
theorem B4871339 : Blo 2163435 4871339 := bstep (se 1 (by rfl) ⟨3653504, by rfl⟩ : syracuseStep 4871339 = 7307009) B7307009
theorem B3247559 : Blo 2163435 3247559 := bstep (se 1 (by rfl) ⟨2435669, by rfl⟩ : syracuseStep 3247559 = 4871339) B4871339
theorem B2165039 : Blo 2163435 2165039 := bstep (se 1 (by rfl) ⟨1623779, by rfl⟩ : syracuseStep 2165039 = 3247559) B3247559
theorem B3247565 : Blo 2163435 3247565 := bbase (se 3 (by rfl) ⟨608918, by rfl⟩ : syracuseStep 3247565 = 1217837) (by norm_num)
theorem B2165043 : Blo 2163435 2165043 := bstep (se 1 (by rfl) ⟨1623782, by rfl⟩ : syracuseStep 2165043 = 3247565) B3247565
theorem B4871357 : Blo 2163435 4871357 := bbase (se 3 (by rfl) ⟨913379, by rfl⟩ : syracuseStep 4871357 = 1826759) (by norm_num)
theorem B3247571 : Blo 2163435 3247571 := bstep (se 1 (by rfl) ⟨2435678, by rfl⟩ : syracuseStep 3247571 = 4871357) B4871357
theorem B2165047 : Blo 2163435 2165047 := bstep (se 1 (by rfl) ⟨1623785, by rfl⟩ : syracuseStep 2165047 = 3247571) B3247571
theorem B3653525 : Blo 2163435 3653525 := bbase (se 6 (by rfl) ⟨85629, by rfl⟩ : syracuseStep 3653525 = 171259) (by norm_num)
theorem B2435683 : Blo 2163435 2435683 := bstep (se 1 (by rfl) ⟨1826762, by rfl⟩ : syracuseStep 2435683 = 3653525) B3653525
theorem B3247577 : Blo 2163435 3247577 := bstep (se 2 (by rfl) ⟨1217841, by rfl⟩ : syracuseStep 3247577 = 2435683) B2435683
theorem B2165051 : Blo 2163435 2165051 := bstep (se 1 (by rfl) ⟨1623788, by rfl⟩ : syracuseStep 2165051 = 3247577) B3247577
theorem B2601001 : Blo 2163435 2601001 := bbase (se 2 (by rfl) ⟨975375, by rfl⟩ : syracuseStep 2601001 = 1950751) (by norm_num)
theorem B13872005 : Blo 2163435 13872005 := bstep (se 4 (by rfl) ⟨1300500, by rfl⟩ : syracuseStep 13872005 = 2601001) B2601001
theorem B9248003 : Blo 2163435 9248003 := bstep (se 1 (by rfl) ⟨6936002, by rfl⟩ : syracuseStep 9248003 = 13872005) B13872005
theorem B6165335 : Blo 2163435 6165335 := bstep (se 1 (by rfl) ⟨4624001, by rfl⟩ : syracuseStep 6165335 = 9248003) B9248003
theorem B16440893 : Blo 2163435 16440893 := bstep (se 3 (by rfl) ⟨3082667, by rfl⟩ : syracuseStep 16440893 = 6165335) B6165335
theorem B10960595 : Blo 2163435 10960595 := bstep (se 1 (by rfl) ⟨8220446, by rfl⟩ : syracuseStep 10960595 = 16440893) B16440893
theorem B7307063 : Blo 2163435 7307063 := bstep (se 1 (by rfl) ⟨5480297, by rfl⟩ : syracuseStep 7307063 = 10960595) B10960595
theorem B4871375 : Blo 2163435 4871375 := bstep (se 1 (by rfl) ⟨3653531, by rfl⟩ : syracuseStep 4871375 = 7307063) B7307063
theorem B3247583 : Blo 2163435 3247583 := bstep (se 1 (by rfl) ⟨2435687, by rfl⟩ : syracuseStep 3247583 = 4871375) B4871375
theorem B2165055 : Blo 2163435 2165055 := bstep (se 1 (by rfl) ⟨1623791, by rfl⟩ : syracuseStep 2165055 = 3247583) B3247583
theorem B3247589 : Blo 2163435 3247589 := bbase (se 4 (by rfl) ⟨304461, by rfl⟩ : syracuseStep 3247589 = 608923) (by norm_num)
theorem B2165059 : Blo 2163435 2165059 := bstep (se 1 (by rfl) ⟨1623794, by rfl⟩ : syracuseStep 2165059 = 3247589) B3247589
theorem B2468929 : Blo 2163435 2468929 := bbase (se 2 (by rfl) ⟨925848, by rfl⟩ : syracuseStep 2468929 = 1851697) (by norm_num)
theorem B3291905 : Blo 2163435 3291905 := bstep (se 2 (by rfl) ⟨1234464, by rfl⟩ : syracuseStep 3291905 = 2468929) B2468929
theorem B8778413 : Blo 2163435 8778413 := bstep (se 3 (by rfl) ⟨1645952, by rfl⟩ : syracuseStep 8778413 = 3291905) B3291905
theorem B23409101 : Blo 2163435 23409101 := bstep (se 3 (by rfl) ⟨4389206, by rfl⟩ : syracuseStep 23409101 = 8778413) B8778413
theorem B15606067 : Blo 2163435 15606067 := bstep (se 1 (by rfl) ⟨11704550, by rfl⟩ : syracuseStep 15606067 = 23409101) B23409101
theorem B20808089 : Blo 2163435 20808089 := bstep (se 2 (by rfl) ⟨7803033, by rfl⟩ : syracuseStep 20808089 = 15606067) B15606067
theorem B13872059 : Blo 2163435 13872059 := bstep (se 1 (by rfl) ⟨10404044, by rfl⟩ : syracuseStep 13872059 = 20808089) B20808089
theorem B9248039 : Blo 2163435 9248039 := bstep (se 1 (by rfl) ⟨6936029, by rfl⟩ : syracuseStep 9248039 = 13872059) B13872059
theorem B6165359 : Blo 2163435 6165359 := bstep (se 1 (by rfl) ⟨4624019, by rfl⟩ : syracuseStep 6165359 = 9248039) B9248039
theorem B4110239 : Blo 2163435 4110239 := bstep (se 1 (by rfl) ⟨3082679, by rfl⟩ : syracuseStep 4110239 = 6165359) B6165359
theorem B2740159 : Blo 2163435 2740159 := bstep (se 1 (by rfl) ⟨2055119, by rfl⟩ : syracuseStep 2740159 = 4110239) B4110239
theorem B3653545 : Blo 2163435 3653545 := bstep (se 2 (by rfl) ⟨1370079, by rfl⟩ : syracuseStep 3653545 = 2740159) B2740159
theorem B4871393 : Blo 2163435 4871393 := bstep (se 2 (by rfl) ⟨1826772, by rfl⟩ : syracuseStep 4871393 = 3653545) B3653545
theorem B3247595 : Blo 2163435 3247595 := bstep (se 1 (by rfl) ⟨2435696, by rfl⟩ : syracuseStep 3247595 = 4871393) B4871393
theorem B2165063 : Blo 2163435 2165063 := bstep (se 1 (by rfl) ⟨1623797, by rfl⟩ : syracuseStep 2165063 = 3247595) B3247595
theorem B2435701 : Blo 2163435 2435701 := bbase (se 5 (by rfl) ⟨114173, by rfl⟩ : syracuseStep 2435701 = 228347) (by norm_num)
theorem B3247601 : Blo 2163435 3247601 := bstep (se 2 (by rfl) ⟨1217850, by rfl⟩ : syracuseStep 3247601 = 2435701) B2435701
theorem B2165067 : Blo 2163435 2165067 := bstep (se 1 (by rfl) ⟨1623800, by rfl⟩ : syracuseStep 2165067 = 3247601) B3247601
theorem B2740169 : Blo 2163435 2740169 := bbase (se 2 (by rfl) ⟨1027563, by rfl⟩ : syracuseStep 2740169 = 2055127) (by norm_num)
theorem B7307117 : Blo 2163435 7307117 := bstep (se 3 (by rfl) ⟨1370084, by rfl⟩ : syracuseStep 7307117 = 2740169) B2740169
theorem B4871411 : Blo 2163435 4871411 := bstep (se 1 (by rfl) ⟨3653558, by rfl⟩ : syracuseStep 4871411 = 7307117) B7307117
theorem B3247607 : Blo 2163435 3247607 := bstep (se 1 (by rfl) ⟨2435705, by rfl⟩ : syracuseStep 3247607 = 4871411) B4871411
theorem B2165071 : Blo 2163435 2165071 := bstep (se 1 (by rfl) ⟨1623803, by rfl⟩ : syracuseStep 2165071 = 3247607) B3247607
theorem B3247613 : Blo 2163435 3247613 := bbase (se 3 (by rfl) ⟨608927, by rfl⟩ : syracuseStep 3247613 = 1217855) (by norm_num)
theorem B2165075 : Blo 2163435 2165075 := bstep (se 1 (by rfl) ⟨1623806, by rfl⟩ : syracuseStep 2165075 = 3247613) B3247613
theorem B4871429 : Blo 2163435 4871429 := bbase (se 4 (by rfl) ⟨456696, by rfl⟩ : syracuseStep 4871429 = 913393) (by norm_num)
theorem B3247619 : Blo 2163435 3247619 := bstep (se 1 (by rfl) ⟨2435714, by rfl⟩ : syracuseStep 3247619 = 4871429) B4871429
theorem B2165079 : Blo 2163435 2165079 := bstep (se 1 (by rfl) ⟨1623809, by rfl⟩ : syracuseStep 2165079 = 3247619) B3247619
theorem B4110277 : Blo 2163435 4110277 := bbase (se 4 (by rfl) ⟨385338, by rfl⟩ : syracuseStep 4110277 = 770677) (by norm_num)
theorem B5480369 : Blo 2163435 5480369 := bstep (se 2 (by rfl) ⟨2055138, by rfl⟩ : syracuseStep 5480369 = 4110277) B4110277
theorem B3653579 : Blo 2163435 3653579 := bstep (se 1 (by rfl) ⟨2740184, by rfl⟩ : syracuseStep 3653579 = 5480369) B5480369
theorem B2435719 : Blo 2163435 2435719 := bstep (se 1 (by rfl) ⟨1826789, by rfl⟩ : syracuseStep 2435719 = 3653579) B3653579
theorem B3247625 : Blo 2163435 3247625 := bstep (se 2 (by rfl) ⟨1217859, by rfl⟩ : syracuseStep 3247625 = 2435719) B2435719
theorem B2165083 : Blo 2163435 2165083 := bstep (se 1 (by rfl) ⟨1623812, by rfl⟩ : syracuseStep 2165083 = 3247625) B3247625
theorem B10960757 : Blo 2163435 10960757 := bbase (se 5 (by rfl) ⟨513785, by rfl⟩ : syracuseStep 10960757 = 1027571) (by norm_num)
theorem B7307171 : Blo 2163435 7307171 := bstep (se 1 (by rfl) ⟨5480378, by rfl⟩ : syracuseStep 7307171 = 10960757) B10960757
theorem B4871447 : Blo 2163435 4871447 := bstep (se 1 (by rfl) ⟨3653585, by rfl⟩ : syracuseStep 4871447 = 7307171) B7307171
theorem B3247631 : Blo 2163435 3247631 := bstep (se 1 (by rfl) ⟨2435723, by rfl⟩ : syracuseStep 3247631 = 4871447) B4871447
theorem B2165087 : Blo 2163435 2165087 := bstep (se 1 (by rfl) ⟨1623815, by rfl⟩ : syracuseStep 2165087 = 3247631) B3247631
theorem B3247637 : Blo 2163435 3247637 := bbase (se 6 (by rfl) ⟨76116, by rfl⟩ : syracuseStep 3247637 = 152233) (by norm_num)
theorem B2165091 : Blo 2163435 2165091 := bstep (se 1 (by rfl) ⟨1623818, by rfl⟩ : syracuseStep 2165091 = 3247637) B3247637
theorem B10404197 : Blo 2163435 10404197 := bbase (se 4 (by rfl) ⟨975393, by rfl⟩ : syracuseStep 10404197 = 1950787) (by norm_num)
theorem B6936131 : Blo 2163435 6936131 := bstep (se 1 (by rfl) ⟨5202098, by rfl⟩ : syracuseStep 6936131 = 10404197) B10404197
theorem B18496349 : Blo 2163435 18496349 := bstep (se 3 (by rfl) ⟨3468065, by rfl⟩ : syracuseStep 18496349 = 6936131) B6936131
theorem B12330899 : Blo 2163435 12330899 := bstep (se 1 (by rfl) ⟨9248174, by rfl⟩ : syracuseStep 12330899 = 18496349) B18496349
theorem B8220599 : Blo 2163435 8220599 := bstep (se 1 (by rfl) ⟨6165449, by rfl⟩ : syracuseStep 8220599 = 12330899) B12330899
theorem B5480399 : Blo 2163435 5480399 := bstep (se 1 (by rfl) ⟨4110299, by rfl⟩ : syracuseStep 5480399 = 8220599) B8220599
theorem B3653599 : Blo 2163435 3653599 := bstep (se 1 (by rfl) ⟨2740199, by rfl⟩ : syracuseStep 3653599 = 5480399) B5480399
theorem B4871465 : Blo 2163435 4871465 := bstep (se 2 (by rfl) ⟨1826799, by rfl⟩ : syracuseStep 4871465 = 3653599) B3653599
theorem B3247643 : Blo 2163435 3247643 := bstep (se 1 (by rfl) ⟨2435732, by rfl⟩ : syracuseStep 3247643 = 4871465) B4871465
theorem B2165095 : Blo 2163435 2165095 := bstep (se 1 (by rfl) ⟨1623821, by rfl⟩ : syracuseStep 2165095 = 3247643) B3247643
theorem B2435737 : Blo 2163435 2435737 := bbase (se 2 (by rfl) ⟨913401, by rfl⟩ : syracuseStep 2435737 = 1826803) (by norm_num)
theorem B3247649 : Blo 2163435 3247649 := bstep (se 2 (by rfl) ⟨1217868, by rfl⟩ : syracuseStep 3247649 = 2435737) B2435737
theorem B2165099 : Blo 2163435 2165099 := bstep (se 1 (by rfl) ⟨1623824, by rfl⟩ : syracuseStep 2165099 = 3247649) B3247649
theorem B8220629 : Blo 2163435 8220629 := bbase (se 7 (by rfl) ⟨96335, by rfl⟩ : syracuseStep 8220629 = 192671) (by norm_num)
theorem B5480419 : Blo 2163435 5480419 := bstep (se 1 (by rfl) ⟨4110314, by rfl⟩ : syracuseStep 5480419 = 8220629) B8220629
theorem B7307225 : Blo 2163435 7307225 := bstep (se 2 (by rfl) ⟨2740209, by rfl⟩ : syracuseStep 7307225 = 5480419) B5480419
theorem B4871483 : Blo 2163435 4871483 := bstep (se 1 (by rfl) ⟨3653612, by rfl⟩ : syracuseStep 4871483 = 7307225) B7307225
theorem B3247655 : Blo 2163435 3247655 := bstep (se 1 (by rfl) ⟨2435741, by rfl⟩ : syracuseStep 3247655 = 4871483) B4871483
theorem B2165103 : Blo 2163435 2165103 := bstep (se 1 (by rfl) ⟨1623827, by rfl⟩ : syracuseStep 2165103 = 3247655) B3247655
theorem B3247661 : Blo 2163435 3247661 := bbase (se 3 (by rfl) ⟨608936, by rfl⟩ : syracuseStep 3247661 = 1217873) (by norm_num)
theorem B2165107 : Blo 2163435 2165107 := bstep (se 1 (by rfl) ⟨1623830, by rfl⟩ : syracuseStep 2165107 = 3247661) B3247661
theorem B4871501 : Blo 2163435 4871501 := bbase (se 3 (by rfl) ⟨913406, by rfl⟩ : syracuseStep 4871501 = 1826813) (by norm_num)
theorem B3247667 : Blo 2163435 3247667 := bstep (se 1 (by rfl) ⟨2435750, by rfl⟩ : syracuseStep 3247667 = 4871501) B4871501
theorem B2165111 : Blo 2163435 2165111 := bstep (se 1 (by rfl) ⟨1623833, by rfl⟩ : syracuseStep 2165111 = 3247667) B3247667
theorem B2740225 : Blo 2163435 2740225 := bbase (se 2 (by rfl) ⟨1027584, by rfl⟩ : syracuseStep 2740225 = 2055169) (by norm_num)
theorem B3653633 : Blo 2163435 3653633 := bstep (se 2 (by rfl) ⟨1370112, by rfl⟩ : syracuseStep 3653633 = 2740225) B2740225
theorem B2435755 : Blo 2163435 2435755 := bstep (se 1 (by rfl) ⟨1826816, by rfl⟩ : syracuseStep 2435755 = 3653633) B3653633
theorem B3247673 : Blo 2163435 3247673 := bstep (se 2 (by rfl) ⟨1217877, by rfl⟩ : syracuseStep 3247673 = 2435755) B2435755
theorem B2165115 : Blo 2163435 2165115 := bstep (se 1 (by rfl) ⟨1623836, by rfl⟩ : syracuseStep 2165115 = 3247673) B3247673
theorem B2312069 : Blo 2163435 2312069 := bbase (se 4 (by rfl) ⟨216756, by rfl⟩ : syracuseStep 2312069 = 433513) (by norm_num)
theorem B24662069 : Blo 2163435 24662069 := bstep (se 5 (by rfl) ⟨1156034, by rfl⟩ : syracuseStep 24662069 = 2312069) B2312069
theorem B16441379 : Blo 2163435 16441379 := bstep (se 1 (by rfl) ⟨12331034, by rfl⟩ : syracuseStep 16441379 = 24662069) B24662069
theorem B10960919 : Blo 2163435 10960919 := bstep (se 1 (by rfl) ⟨8220689, by rfl⟩ : syracuseStep 10960919 = 16441379) B16441379
theorem B7307279 : Blo 2163435 7307279 := bstep (se 1 (by rfl) ⟨5480459, by rfl⟩ : syracuseStep 7307279 = 10960919) B10960919
theorem B4871519 : Blo 2163435 4871519 := bstep (se 1 (by rfl) ⟨3653639, by rfl⟩ : syracuseStep 4871519 = 7307279) B7307279
theorem B3247679 : Blo 2163435 3247679 := bstep (se 1 (by rfl) ⟨2435759, by rfl⟩ : syracuseStep 3247679 = 4871519) B4871519
theorem B2165119 : Blo 2163435 2165119 := bstep (se 1 (by rfl) ⟨1623839, by rfl⟩ : syracuseStep 2165119 = 3247679) B3247679
theorem B3247685 : Blo 2163435 3247685 := bbase (se 4 (by rfl) ⟨304470, by rfl⟩ : syracuseStep 3247685 = 608941) (by norm_num)
theorem B2165123 : Blo 2163435 2165123 := bstep (se 1 (by rfl) ⟨1623842, by rfl⟩ : syracuseStep 2165123 = 3247685) B3247685
theorem B3653653 : Blo 2163435 3653653 := bbase (se 6 (by rfl) ⟨85632, by rfl⟩ : syracuseStep 3653653 = 171265) (by norm_num)
theorem B4871537 : Blo 2163435 4871537 := bstep (se 2 (by rfl) ⟨1826826, by rfl⟩ : syracuseStep 4871537 = 3653653) B3653653
theorem B3247691 : Blo 2163435 3247691 := bstep (se 1 (by rfl) ⟨2435768, by rfl⟩ : syracuseStep 3247691 = 4871537) B4871537
theorem B2165127 : Blo 2163435 2165127 := bstep (se 1 (by rfl) ⟨1623845, by rfl⟩ : syracuseStep 2165127 = 3247691) B3247691
theorem B2435773 : Blo 2163435 2435773 := bbase (se 3 (by rfl) ⟨456707, by rfl⟩ : syracuseStep 2435773 = 913415) (by norm_num)
theorem B3247697 : Blo 2163435 3247697 := bstep (se 2 (by rfl) ⟨1217886, by rfl⟩ : syracuseStep 3247697 = 2435773) B2435773
theorem B2165131 : Blo 2163435 2165131 := bstep (se 1 (by rfl) ⟨1623848, by rfl⟩ : syracuseStep 2165131 = 3247697) B3247697
theorem B7307333 : Blo 2163435 7307333 := bbase (se 4 (by rfl) ⟨685062, by rfl⟩ : syracuseStep 7307333 = 1370125) (by norm_num)
theorem B4871555 : Blo 2163435 4871555 := bstep (se 1 (by rfl) ⟨3653666, by rfl⟩ : syracuseStep 4871555 = 7307333) B7307333
theorem B3247703 : Blo 2163435 3247703 := bstep (se 1 (by rfl) ⟨2435777, by rfl⟩ : syracuseStep 3247703 = 4871555) B4871555
theorem B2165135 : Blo 2163435 2165135 := bstep (se 1 (by rfl) ⟨1623851, by rfl⟩ : syracuseStep 2165135 = 3247703) B3247703
theorem B3247709 : Blo 2163435 3247709 := bbase (se 3 (by rfl) ⟨608945, by rfl⟩ : syracuseStep 3247709 = 1217891) (by norm_num)
theorem B2165139 : Blo 2163435 2165139 := bstep (se 1 (by rfl) ⟨1623854, by rfl⟩ : syracuseStep 2165139 = 3247709) B3247709
theorem B4871573 : Blo 2163435 4871573 := bbase (se 6 (by rfl) ⟨114177, by rfl⟩ : syracuseStep 4871573 = 228355) (by norm_num)
theorem B3247715 : Blo 2163435 3247715 := bstep (se 1 (by rfl) ⟨2435786, by rfl⟩ : syracuseStep 3247715 = 4871573) B4871573
theorem B2165143 : Blo 2163435 2165143 := bstep (se 1 (by rfl) ⟨1623857, by rfl⟩ : syracuseStep 2165143 = 3247715) B3247715
theorem B2469025 : Blo 2163435 2469025 := bbase (se 2 (by rfl) ⟨925884, by rfl⟩ : syracuseStep 2469025 = 1851769) (by norm_num)
theorem B13168133 : Blo 2163435 13168133 := bstep (se 4 (by rfl) ⟨1234512, by rfl⟩ : syracuseStep 13168133 = 2469025) B2469025
theorem B8778755 : Blo 2163435 8778755 := bstep (se 1 (by rfl) ⟨6584066, by rfl⟩ : syracuseStep 8778755 = 13168133) B13168133
theorem B5852503 : Blo 2163435 5852503 := bstep (se 1 (by rfl) ⟨4389377, by rfl⟩ : syracuseStep 5852503 = 8778755) B8778755
theorem B7803337 : Blo 2163435 7803337 := bstep (se 2 (by rfl) ⟨2926251, by rfl⟩ : syracuseStep 7803337 = 5852503) B5852503
theorem B10404449 : Blo 2163435 10404449 := bstep (se 2 (by rfl) ⟨3901668, by rfl⟩ : syracuseStep 10404449 = 7803337) B7803337
theorem B6936299 : Blo 2163435 6936299 := bstep (se 1 (by rfl) ⟨5202224, by rfl⟩ : syracuseStep 6936299 = 10404449) B10404449
theorem B4624199 : Blo 2163435 4624199 := bstep (se 1 (by rfl) ⟨3468149, by rfl⟩ : syracuseStep 4624199 = 6936299) B6936299
theorem B3082799 : Blo 2163435 3082799 := bstep (se 1 (by rfl) ⟨2312099, by rfl⟩ : syracuseStep 3082799 = 4624199) B4624199
theorem B8220797 : Blo 2163435 8220797 := bstep (se 3 (by rfl) ⟨1541399, by rfl⟩ : syracuseStep 8220797 = 3082799) B3082799
theorem B5480531 : Blo 2163435 5480531 := bstep (se 1 (by rfl) ⟨4110398, by rfl⟩ : syracuseStep 5480531 = 8220797) B8220797
theorem B3653687 : Blo 2163435 3653687 := bstep (se 1 (by rfl) ⟨2740265, by rfl⟩ : syracuseStep 3653687 = 5480531) B5480531
theorem B2435791 : Blo 2163435 2435791 := bstep (se 1 (by rfl) ⟨1826843, by rfl⟩ : syracuseStep 2435791 = 3653687) B3653687
theorem B3247721 : Blo 2163435 3247721 := bstep (se 2 (by rfl) ⟨1217895, by rfl⟩ : syracuseStep 3247721 = 2435791) B2435791
theorem B2165147 : Blo 2163435 2165147 := bstep (se 1 (by rfl) ⟨1623860, by rfl⟩ : syracuseStep 2165147 = 3247721) B3247721
theorem B5555317 : Blo 2163435 5555317 := bbase (se 5 (by rfl) ⟨260405, by rfl⟩ : syracuseStep 5555317 = 520811) (by norm_num)
theorem B7407089 : Blo 2163435 7407089 := bstep (se 2 (by rfl) ⟨2777658, by rfl⟩ : syracuseStep 7407089 = 5555317) B5555317
theorem B4938059 : Blo 2163435 4938059 := bstep (se 1 (by rfl) ⟨3703544, by rfl⟩ : syracuseStep 4938059 = 7407089) B7407089
theorem B3292039 : Blo 2163435 3292039 := bstep (se 1 (by rfl) ⟨2469029, by rfl⟩ : syracuseStep 3292039 = 4938059) B4938059
theorem B4389385 : Blo 2163435 4389385 := bstep (se 2 (by rfl) ⟨1646019, by rfl⟩ : syracuseStep 4389385 = 3292039) B3292039
theorem B5852513 : Blo 2163435 5852513 := bstep (se 2 (by rfl) ⟨2194692, by rfl⟩ : syracuseStep 5852513 = 4389385) B4389385
theorem B3901675 : Blo 2163435 3901675 := bstep (se 1 (by rfl) ⟨2926256, by rfl⟩ : syracuseStep 3901675 = 5852513) B5852513
theorem B5202233 : Blo 2163435 5202233 := bstep (se 2 (by rfl) ⟨1950837, by rfl⟩ : syracuseStep 5202233 = 3901675) B3901675
theorem B3468155 : Blo 2163435 3468155 := bstep (se 1 (by rfl) ⟨2601116, by rfl⟩ : syracuseStep 3468155 = 5202233) B5202233
theorem B9248413 : Blo 2163435 9248413 := bstep (se 3 (by rfl) ⟨1734077, by rfl⟩ : syracuseStep 9248413 = 3468155) B3468155
theorem B12331217 : Blo 2163435 12331217 := bstep (se 2 (by rfl) ⟨4624206, by rfl⟩ : syracuseStep 12331217 = 9248413) B9248413
theorem B8220811 : Blo 2163435 8220811 := bstep (se 1 (by rfl) ⟨6165608, by rfl⟩ : syracuseStep 8220811 = 12331217) B12331217
theorem B10961081 : Blo 2163435 10961081 := bstep (se 2 (by rfl) ⟨4110405, by rfl⟩ : syracuseStep 10961081 = 8220811) B8220811
theorem B7307387 : Blo 2163435 7307387 := bstep (se 1 (by rfl) ⟨5480540, by rfl⟩ : syracuseStep 7307387 = 10961081) B10961081
theorem B4871591 : Blo 2163435 4871591 := bstep (se 1 (by rfl) ⟨3653693, by rfl⟩ : syracuseStep 4871591 = 7307387) B7307387
theorem B3247727 : Blo 2163435 3247727 := bstep (se 1 (by rfl) ⟨2435795, by rfl⟩ : syracuseStep 3247727 = 4871591) B4871591
theorem B2165151 : Blo 2163435 2165151 := bstep (se 1 (by rfl) ⟨1623863, by rfl⟩ : syracuseStep 2165151 = 3247727) B3247727
theorem B3247733 : Blo 2163435 3247733 := bbase (se 5 (by rfl) ⟨152237, by rfl⟩ : syracuseStep 3247733 = 304475) (by norm_num)
theorem B2165155 : Blo 2163435 2165155 := bstep (se 1 (by rfl) ⟨1623866, by rfl⟩ : syracuseStep 2165155 = 3247733) B3247733
theorem B4110421 : Blo 2163435 4110421 := bbase (se 8 (by rfl) ⟨24084, by rfl⟩ : syracuseStep 4110421 = 48169) (by norm_num)
theorem B5480561 : Blo 2163435 5480561 := bstep (se 2 (by rfl) ⟨2055210, by rfl⟩ : syracuseStep 5480561 = 4110421) B4110421
theorem B3653707 : Blo 2163435 3653707 := bstep (se 1 (by rfl) ⟨2740280, by rfl⟩ : syracuseStep 3653707 = 5480561) B5480561
theorem B4871609 : Blo 2163435 4871609 := bstep (se 2 (by rfl) ⟨1826853, by rfl⟩ : syracuseStep 4871609 = 3653707) B3653707
theorem B3247739 : Blo 2163435 3247739 := bstep (se 1 (by rfl) ⟨2435804, by rfl⟩ : syracuseStep 3247739 = 4871609) B4871609
theorem B2165159 : Blo 2163435 2165159 := bstep (se 1 (by rfl) ⟨1623869, by rfl⟩ : syracuseStep 2165159 = 3247739) B3247739
theorem B2435809 : Blo 2163435 2435809 := bbase (se 2 (by rfl) ⟨913428, by rfl⟩ : syracuseStep 2435809 = 1826857) (by norm_num)
theorem B3247745 : Blo 2163435 3247745 := bstep (se 2 (by rfl) ⟨1217904, by rfl⟩ : syracuseStep 3247745 = 2435809) B2435809
theorem B2165163 : Blo 2163435 2165163 := bstep (se 1 (by rfl) ⟨1623872, by rfl⟩ : syracuseStep 2165163 = 3247745) B3247745
theorem B5480581 : Blo 2163435 5480581 := bbase (se 4 (by rfl) ⟨513804, by rfl⟩ : syracuseStep 5480581 = 1027609) (by norm_num)
theorem B7307441 : Blo 2163435 7307441 := bstep (se 2 (by rfl) ⟨2740290, by rfl⟩ : syracuseStep 7307441 = 5480581) B5480581
theorem B4871627 : Blo 2163435 4871627 := bstep (se 1 (by rfl) ⟨3653720, by rfl⟩ : syracuseStep 4871627 = 7307441) B7307441
theorem B3247751 : Blo 2163435 3247751 := bstep (se 1 (by rfl) ⟨2435813, by rfl⟩ : syracuseStep 3247751 = 4871627) B4871627
theorem B2165167 : Blo 2163435 2165167 := bstep (se 1 (by rfl) ⟨1623875, by rfl⟩ : syracuseStep 2165167 = 3247751) B3247751
theorem B3247757 : Blo 2163435 3247757 := bbase (se 3 (by rfl) ⟨608954, by rfl⟩ : syracuseStep 3247757 = 1217909) (by norm_num)
theorem B2165171 : Blo 2163435 2165171 := bstep (se 1 (by rfl) ⟨1623878, by rfl⟩ : syracuseStep 2165171 = 3247757) B3247757
theorem B4871645 : Blo 2163435 4871645 := bbase (se 3 (by rfl) ⟨913433, by rfl⟩ : syracuseStep 4871645 = 1826867) (by norm_num)
theorem B3247763 : Blo 2163435 3247763 := bstep (se 1 (by rfl) ⟨2435822, by rfl⟩ : syracuseStep 3247763 = 4871645) B4871645
theorem B2165175 : Blo 2163435 2165175 := bstep (se 1 (by rfl) ⟨1623881, by rfl⟩ : syracuseStep 2165175 = 3247763) B3247763
theorem B3653741 : Blo 2163435 3653741 := bbase (se 3 (by rfl) ⟨685076, by rfl⟩ : syracuseStep 3653741 = 1370153) (by norm_num)
theorem B2435827 : Blo 2163435 2435827 := bstep (se 1 (by rfl) ⟨1826870, by rfl⟩ : syracuseStep 2435827 = 3653741) B3653741
theorem B3247769 : Blo 2163435 3247769 := bstep (se 2 (by rfl) ⟨1217913, by rfl⟩ : syracuseStep 3247769 = 2435827) B2435827
theorem B2165179 : Blo 2163435 2165179 := bstep (se 1 (by rfl) ⟨1623884, by rfl⟩ : syracuseStep 2165179 = 3247769) B3247769
theorem B20809237 : Blo 2163435 20809237 := bbase (se 6 (by rfl) ⟨487716, by rfl⟩ : syracuseStep 20809237 = 975433) (by norm_num)
theorem B27745649 : Blo 2163435 27745649 := bstep (se 2 (by rfl) ⟨10404618, by rfl⟩ : syracuseStep 27745649 = 20809237) B20809237
theorem B18497099 : Blo 2163435 18497099 := bstep (se 1 (by rfl) ⟨13872824, by rfl⟩ : syracuseStep 18497099 = 27745649) B27745649
theorem B12331399 : Blo 2163435 12331399 := bstep (se 1 (by rfl) ⟨9248549, by rfl⟩ : syracuseStep 12331399 = 18497099) B18497099
theorem B16441865 : Blo 2163435 16441865 := bstep (se 2 (by rfl) ⟨6165699, by rfl⟩ : syracuseStep 16441865 = 12331399) B12331399
theorem B10961243 : Blo 2163435 10961243 := bstep (se 1 (by rfl) ⟨8220932, by rfl⟩ : syracuseStep 10961243 = 16441865) B16441865
theorem B7307495 : Blo 2163435 7307495 := bstep (se 1 (by rfl) ⟨5480621, by rfl⟩ : syracuseStep 7307495 = 10961243) B10961243
theorem B4871663 : Blo 2163435 4871663 := bstep (se 1 (by rfl) ⟨3653747, by rfl⟩ : syracuseStep 4871663 = 7307495) B7307495
theorem B3247775 : Blo 2163435 3247775 := bstep (se 1 (by rfl) ⟨2435831, by rfl⟩ : syracuseStep 3247775 = 4871663) B4871663
theorem B2165183 : Blo 2163435 2165183 := bstep (se 1 (by rfl) ⟨1623887, by rfl⟩ : syracuseStep 2165183 = 3247775) B3247775
theorem B3247781 : Blo 2163435 3247781 := bbase (se 4 (by rfl) ⟨304479, by rfl⟩ : syracuseStep 3247781 = 608959) (by norm_num)
theorem B2165187 : Blo 2163435 2165187 := bstep (se 1 (by rfl) ⟨1623890, by rfl⟩ : syracuseStep 2165187 = 3247781) B3247781
theorem B2740321 : Blo 2163435 2740321 := bbase (se 2 (by rfl) ⟨1027620, by rfl⟩ : syracuseStep 2740321 = 2055241) (by norm_num)
theorem B3653761 : Blo 2163435 3653761 := bstep (se 2 (by rfl) ⟨1370160, by rfl⟩ : syracuseStep 3653761 = 2740321) B2740321
theorem B4871681 : Blo 2163435 4871681 := bstep (se 2 (by rfl) ⟨1826880, by rfl⟩ : syracuseStep 4871681 = 3653761) B3653761
theorem B3247787 : Blo 2163435 3247787 := bstep (se 1 (by rfl) ⟨2435840, by rfl⟩ : syracuseStep 3247787 = 4871681) B4871681
theorem B2165191 : Blo 2163435 2165191 := bstep (se 1 (by rfl) ⟨1623893, by rfl⟩ : syracuseStep 2165191 = 3247787) B3247787
theorem B2435845 : Blo 2163435 2435845 := bbase (se 4 (by rfl) ⟨228360, by rfl⟩ : syracuseStep 2435845 = 456721) (by norm_num)
theorem B3247793 : Blo 2163435 3247793 := bstep (se 2 (by rfl) ⟨1217922, by rfl⟩ : syracuseStep 3247793 = 2435845) B2435845
theorem B2165195 : Blo 2163435 2165195 := bstep (se 1 (by rfl) ⟨1623896, by rfl⟩ : syracuseStep 2165195 = 3247793) B3247793
theorem B5852645 : Blo 2163435 5852645 := bbase (se 4 (by rfl) ⟨548685, by rfl⟩ : syracuseStep 5852645 = 1097371) (by norm_num)
theorem B3901763 : Blo 2163435 3901763 := bstep (se 1 (by rfl) ⟨2926322, by rfl⟩ : syracuseStep 3901763 = 5852645) B5852645
theorem B2601175 : Blo 2163435 2601175 := bstep (se 1 (by rfl) ⟨1950881, by rfl⟩ : syracuseStep 2601175 = 3901763) B3901763
theorem B3468233 : Blo 2163435 3468233 := bstep (se 2 (by rfl) ⟨1300587, by rfl⟩ : syracuseStep 3468233 = 2601175) B2601175
theorem B2312155 : Blo 2163435 2312155 := bstep (se 1 (by rfl) ⟨1734116, by rfl⟩ : syracuseStep 2312155 = 3468233) B3468233
theorem B3082873 : Blo 2163435 3082873 := bstep (se 2 (by rfl) ⟨1156077, by rfl⟩ : syracuseStep 3082873 = 2312155) B2312155
theorem B4110497 : Blo 2163435 4110497 := bstep (se 2 (by rfl) ⟨1541436, by rfl⟩ : syracuseStep 4110497 = 3082873) B3082873
theorem B2740331 : Blo 2163435 2740331 := bstep (se 1 (by rfl) ⟨2055248, by rfl⟩ : syracuseStep 2740331 = 4110497) B4110497
theorem B7307549 : Blo 2163435 7307549 := bstep (se 3 (by rfl) ⟨1370165, by rfl⟩ : syracuseStep 7307549 = 2740331) B2740331
theorem B4871699 : Blo 2163435 4871699 := bstep (se 1 (by rfl) ⟨3653774, by rfl⟩ : syracuseStep 4871699 = 7307549) B7307549
theorem B3247799 : Blo 2163435 3247799 := bstep (se 1 (by rfl) ⟨2435849, by rfl⟩ : syracuseStep 3247799 = 4871699) B4871699
theorem B2165199 : Blo 2163435 2165199 := bstep (se 1 (by rfl) ⟨1623899, by rfl⟩ : syracuseStep 2165199 = 3247799) B3247799
theorem B3247805 : Blo 2163435 3247805 := bbase (se 3 (by rfl) ⟨608963, by rfl⟩ : syracuseStep 3247805 = 1217927) (by norm_num)
theorem B2165203 : Blo 2163435 2165203 := bstep (se 1 (by rfl) ⟨1623902, by rfl⟩ : syracuseStep 2165203 = 3247805) B3247805
theorem B4871717 : Blo 2163435 4871717 := bbase (se 4 (by rfl) ⟨456723, by rfl⟩ : syracuseStep 4871717 = 913447) (by norm_num)
theorem B3247811 : Blo 2163435 3247811 := bstep (se 1 (by rfl) ⟨2435858, by rfl⟩ : syracuseStep 3247811 = 4871717) B4871717
theorem B2165207 : Blo 2163435 2165207 := bstep (se 1 (by rfl) ⟨1623905, by rfl⟩ : syracuseStep 2165207 = 3247811) B3247811
theorem B5480693 : Blo 2163435 5480693 := bbase (se 5 (by rfl) ⟨256907, by rfl⟩ : syracuseStep 5480693 = 513815) (by norm_num)
theorem B3653795 : Blo 2163435 3653795 := bstep (se 1 (by rfl) ⟨2740346, by rfl⟩ : syracuseStep 3653795 = 5480693) B5480693
theorem B2435863 : Blo 2163435 2435863 := bstep (se 1 (by rfl) ⟨1826897, by rfl⟩ : syracuseStep 2435863 = 3653795) B3653795
theorem B3247817 : Blo 2163435 3247817 := bstep (se 2 (by rfl) ⟨1217931, by rfl⟩ : syracuseStep 3247817 = 2435863) B2435863
theorem B2165211 : Blo 2163435 2165211 := bstep (se 1 (by rfl) ⟨1623908, by rfl⟩ : syracuseStep 2165211 = 3247817) B3247817
theorem B2194757 : Blo 2163435 2194757 := bbase (se 4 (by rfl) ⟨205758, by rfl⟩ : syracuseStep 2194757 = 411517) (by norm_num)
theorem B23410741 : Blo 2163435 23410741 := bstep (se 5 (by rfl) ⟨1097378, by rfl⟩ : syracuseStep 23410741 = 2194757) B2194757
theorem B31214321 : Blo 2163435 31214321 := bstep (se 2 (by rfl) ⟨11705370, by rfl⟩ : syracuseStep 31214321 = 23410741) B23410741
theorem B20809547 : Blo 2163435 20809547 := bstep (se 1 (by rfl) ⟨15607160, by rfl⟩ : syracuseStep 20809547 = 31214321) B31214321
theorem B13873031 : Blo 2163435 13873031 := bstep (se 1 (by rfl) ⟨10404773, by rfl⟩ : syracuseStep 13873031 = 20809547) B20809547
theorem B9248687 : Blo 2163435 9248687 := bstep (se 1 (by rfl) ⟨6936515, by rfl⟩ : syracuseStep 9248687 = 13873031) B13873031
theorem B6165791 : Blo 2163435 6165791 := bstep (se 1 (by rfl) ⟨4624343, by rfl⟩ : syracuseStep 6165791 = 9248687) B9248687
theorem B4110527 : Blo 2163435 4110527 := bstep (se 1 (by rfl) ⟨3082895, by rfl⟩ : syracuseStep 4110527 = 6165791) B6165791
theorem B10961405 : Blo 2163435 10961405 := bstep (se 3 (by rfl) ⟨2055263, by rfl⟩ : syracuseStep 10961405 = 4110527) B4110527
theorem B7307603 : Blo 2163435 7307603 := bstep (se 1 (by rfl) ⟨5480702, by rfl⟩ : syracuseStep 7307603 = 10961405) B10961405
theorem B4871735 : Blo 2163435 4871735 := bstep (se 1 (by rfl) ⟨3653801, by rfl⟩ : syracuseStep 4871735 = 7307603) B7307603
theorem B3247823 : Blo 2163435 3247823 := bstep (se 1 (by rfl) ⟨2435867, by rfl⟩ : syracuseStep 3247823 = 4871735) B4871735
theorem B2165215 : Blo 2163435 2165215 := bstep (se 1 (by rfl) ⟨1623911, by rfl⟩ : syracuseStep 2165215 = 3247823) B3247823
theorem B3247829 : Blo 2163435 3247829 := bbase (se 7 (by rfl) ⟨38060, by rfl⟩ : syracuseStep 3247829 = 76121) (by norm_num)
theorem B2165219 : Blo 2163435 2165219 := bstep (se 1 (by rfl) ⟨1623914, by rfl⟩ : syracuseStep 2165219 = 3247829) B3247829
theorem B8446949 : Blo 2163435 8446949 := bbase (se 4 (by rfl) ⟨791901, by rfl⟩ : syracuseStep 8446949 = 1583803) (by norm_num)
theorem B5631299 : Blo 2163435 5631299 := bstep (se 1 (by rfl) ⟨4223474, by rfl⟩ : syracuseStep 5631299 = 8446949) B8446949
theorem B3754199 : Blo 2163435 3754199 := bstep (se 1 (by rfl) ⟨2815649, by rfl⟩ : syracuseStep 3754199 = 5631299) B5631299
theorem B2502799 : Blo 2163435 2502799 := bstep (se 1 (by rfl) ⟨1877099, by rfl⟩ : syracuseStep 2502799 = 3754199) B3754199
theorem B13348261 : Blo 2163435 13348261 := bstep (se 4 (by rfl) ⟨1251399, by rfl⟩ : syracuseStep 13348261 = 2502799) B2502799
theorem B17797681 : Blo 2163435 17797681 := bstep (se 2 (by rfl) ⟨6674130, by rfl⟩ : syracuseStep 17797681 = 13348261) B13348261
theorem B23730241 : Blo 2163435 23730241 := bstep (se 2 (by rfl) ⟨8898840, by rfl⟩ : syracuseStep 23730241 = 17797681) B17797681
theorem B31640321 : Blo 2163435 31640321 := bstep (se 2 (by rfl) ⟨11865120, by rfl⟩ : syracuseStep 31640321 = 23730241) B23730241
theorem B21093547 : Blo 2163435 21093547 := bstep (se 1 (by rfl) ⟨15820160, by rfl⟩ : syracuseStep 21093547 = 31640321) B31640321
theorem B28124729 : Blo 2163435 28124729 := bstep (se 2 (by rfl) ⟨10546773, by rfl⟩ : syracuseStep 28124729 = 21093547) B21093547
theorem B18749819 : Blo 2163435 18749819 := bstep (se 1 (by rfl) ⟨14062364, by rfl⟩ : syracuseStep 18749819 = 28124729) B28124729
theorem B12499879 : Blo 2163435 12499879 := bstep (se 1 (by rfl) ⟨9374909, by rfl⟩ : syracuseStep 12499879 = 18749819) B18749819
theorem B16666505 : Blo 2163435 16666505 := bstep (se 2 (by rfl) ⟨6249939, by rfl⟩ : syracuseStep 16666505 = 12499879) B12499879
theorem B11111003 : Blo 2163435 11111003 := bstep (se 1 (by rfl) ⟨8333252, by rfl⟩ : syracuseStep 11111003 = 16666505) B16666505
theorem B7407335 : Blo 2163435 7407335 := bstep (se 1 (by rfl) ⟨5555501, by rfl⟩ : syracuseStep 7407335 = 11111003) B11111003
theorem B19752893 : Blo 2163435 19752893 := bstep (se 3 (by rfl) ⟨3703667, by rfl⟩ : syracuseStep 19752893 = 7407335) B7407335
theorem B13168595 : Blo 2163435 13168595 := bstep (se 1 (by rfl) ⟨9876446, by rfl⟩ : syracuseStep 13168595 = 19752893) B19752893
theorem B8779063 : Blo 2163435 8779063 := bstep (se 1 (by rfl) ⟨6584297, by rfl⟩ : syracuseStep 8779063 = 13168595) B13168595
theorem B11705417 : Blo 2163435 11705417 := bstep (se 2 (by rfl) ⟨4389531, by rfl⟩ : syracuseStep 11705417 = 8779063) B8779063
theorem B7803611 : Blo 2163435 7803611 := bstep (se 1 (by rfl) ⟨5852708, by rfl⟩ : syracuseStep 7803611 = 11705417) B11705417
theorem B5202407 : Blo 2163435 5202407 := bstep (se 1 (by rfl) ⟨3901805, by rfl⟩ : syracuseStep 5202407 = 7803611) B7803611
theorem B3468271 : Blo 2163435 3468271 := bstep (se 1 (by rfl) ⟨2601203, by rfl⟩ : syracuseStep 3468271 = 5202407) B5202407
theorem B4624361 : Blo 2163435 4624361 := bstep (se 2 (by rfl) ⟨1734135, by rfl⟩ : syracuseStep 4624361 = 3468271) B3468271
theorem B3082907 : Blo 2163435 3082907 := bstep (se 1 (by rfl) ⟨2312180, by rfl⟩ : syracuseStep 3082907 = 4624361) B4624361
theorem B8221085 : Blo 2163435 8221085 := bstep (se 3 (by rfl) ⟨1541453, by rfl⟩ : syracuseStep 8221085 = 3082907) B3082907
theorem B5480723 : Blo 2163435 5480723 := bstep (se 1 (by rfl) ⟨4110542, by rfl⟩ : syracuseStep 5480723 = 8221085) B8221085
theorem B3653815 : Blo 2163435 3653815 := bstep (se 1 (by rfl) ⟨2740361, by rfl⟩ : syracuseStep 3653815 = 5480723) B5480723
theorem B4871753 : Blo 2163435 4871753 := bstep (se 2 (by rfl) ⟨1826907, by rfl⟩ : syracuseStep 4871753 = 3653815) B3653815
theorem B3247835 : Blo 2163435 3247835 := bstep (se 1 (by rfl) ⟨2435876, by rfl⟩ : syracuseStep 3247835 = 4871753) B4871753
theorem B2165223 : Blo 2163435 2165223 := bstep (se 1 (by rfl) ⟨1623917, by rfl⟩ : syracuseStep 2165223 = 3247835) B3247835
theorem B2435881 : Blo 2163435 2435881 := bbase (se 2 (by rfl) ⟨913455, by rfl⟩ : syracuseStep 2435881 = 1826911) (by norm_num)
theorem B3247841 : Blo 2163435 3247841 := bstep (se 2 (by rfl) ⟨1217940, by rfl⟩ : syracuseStep 3247841 = 2435881) B2435881
theorem B2165227 : Blo 2163435 2165227 := bstep (se 1 (by rfl) ⟨1623920, by rfl⟩ : syracuseStep 2165227 = 3247841) B3247841
theorem B2777761 : Blo 2163435 2777761 := bbase (se 2 (by rfl) ⟨1041660, by rfl⟩ : syracuseStep 2777761 = 2083321) (by norm_num)
theorem B3703681 : Blo 2163435 3703681 := bstep (se 2 (by rfl) ⟨1388880, by rfl⟩ : syracuseStep 3703681 = 2777761) B2777761
theorem B4938241 : Blo 2163435 4938241 := bstep (se 2 (by rfl) ⟨1851840, by rfl⟩ : syracuseStep 4938241 = 3703681) B3703681
theorem B6584321 : Blo 2163435 6584321 := bstep (se 2 (by rfl) ⟨2469120, by rfl⟩ : syracuseStep 6584321 = 4938241) B4938241
theorem B4389547 : Blo 2163435 4389547 := bstep (se 1 (by rfl) ⟨3292160, by rfl⟩ : syracuseStep 4389547 = 6584321) B6584321
theorem B5852729 : Blo 2163435 5852729 := bstep (se 2 (by rfl) ⟨2194773, by rfl⟩ : syracuseStep 5852729 = 4389547) B4389547
theorem B3901819 : Blo 2163435 3901819 := bstep (se 1 (by rfl) ⟨2926364, by rfl⟩ : syracuseStep 3901819 = 5852729) B5852729
theorem B5202425 : Blo 2163435 5202425 := bstep (se 2 (by rfl) ⟨1950909, by rfl⟩ : syracuseStep 5202425 = 3901819) B3901819
theorem B13873133 : Blo 2163435 13873133 := bstep (se 3 (by rfl) ⟨2601212, by rfl⟩ : syracuseStep 13873133 = 5202425) B5202425
theorem B9248755 : Blo 2163435 9248755 := bstep (se 1 (by rfl) ⟨6936566, by rfl⟩ : syracuseStep 9248755 = 13873133) B13873133
theorem B12331673 : Blo 2163435 12331673 := bstep (se 2 (by rfl) ⟨4624377, by rfl⟩ : syracuseStep 12331673 = 9248755) B9248755
theorem B8221115 : Blo 2163435 8221115 := bstep (se 1 (by rfl) ⟨6165836, by rfl⟩ : syracuseStep 8221115 = 12331673) B12331673
theorem B5480743 : Blo 2163435 5480743 := bstep (se 1 (by rfl) ⟨4110557, by rfl⟩ : syracuseStep 5480743 = 8221115) B8221115
theorem B7307657 : Blo 2163435 7307657 := bstep (se 2 (by rfl) ⟨2740371, by rfl⟩ : syracuseStep 7307657 = 5480743) B5480743
theorem B4871771 : Blo 2163435 4871771 := bstep (se 1 (by rfl) ⟨3653828, by rfl⟩ : syracuseStep 4871771 = 7307657) B7307657
theorem B3247847 : Blo 2163435 3247847 := bstep (se 1 (by rfl) ⟨2435885, by rfl⟩ : syracuseStep 3247847 = 4871771) B4871771
theorem B2165231 : Blo 2163435 2165231 := bstep (se 1 (by rfl) ⟨1623923, by rfl⟩ : syracuseStep 2165231 = 3247847) B3247847
theorem B3247853 : Blo 2163435 3247853 := bbase (se 3 (by rfl) ⟨608972, by rfl⟩ : syracuseStep 3247853 = 1217945) (by norm_num)
theorem B2165235 : Blo 2163435 2165235 := bstep (se 1 (by rfl) ⟨1623926, by rfl⟩ : syracuseStep 2165235 = 3247853) B3247853
theorem B4871789 : Blo 2163435 4871789 := bbase (se 3 (by rfl) ⟨913460, by rfl⟩ : syracuseStep 4871789 = 1826921) (by norm_num)
theorem B3247859 : Blo 2163435 3247859 := bstep (se 1 (by rfl) ⟨2435894, by rfl⟩ : syracuseStep 3247859 = 4871789) B4871789
theorem B2165239 : Blo 2163435 2165239 := bstep (se 1 (by rfl) ⟨1623929, by rfl⟩ : syracuseStep 2165239 = 3247859) B3247859
theorem B4110581 : Blo 2163435 4110581 := bbase (se 5 (by rfl) ⟨192683, by rfl⟩ : syracuseStep 4110581 = 385367) (by norm_num)
theorem B2740387 : Blo 2163435 2740387 := bstep (se 1 (by rfl) ⟨2055290, by rfl⟩ : syracuseStep 2740387 = 4110581) B4110581
theorem B3653849 : Blo 2163435 3653849 := bstep (se 2 (by rfl) ⟨1370193, by rfl⟩ : syracuseStep 3653849 = 2740387) B2740387
theorem B2435899 : Blo 2163435 2435899 := bstep (se 1 (by rfl) ⟨1826924, by rfl⟩ : syracuseStep 2435899 = 3653849) B3653849
theorem B3247865 : Blo 2163435 3247865 := bstep (se 2 (by rfl) ⟨1217949, by rfl⟩ : syracuseStep 3247865 = 2435899) B2435899
theorem B2165243 : Blo 2163435 2165243 := bstep (se 1 (by rfl) ⟨1623932, by rfl⟩ : syracuseStep 2165243 = 3247865) B3247865
theorem B10546885 : Blo 2163435 10546885 := bbase (se 4 (by rfl) ⟨988770, by rfl⟩ : syracuseStep 10546885 = 1977541) (by norm_num)
theorem B14062513 : Blo 2163435 14062513 := bstep (se 2 (by rfl) ⟨5273442, by rfl⟩ : syracuseStep 14062513 = 10546885) B10546885
theorem B18750017 : Blo 2163435 18750017 := bstep (se 2 (by rfl) ⟨7031256, by rfl⟩ : syracuseStep 18750017 = 14062513) B14062513
theorem B12500011 : Blo 2163435 12500011 := bstep (se 1 (by rfl) ⟨9375008, by rfl⟩ : syracuseStep 12500011 = 18750017) B18750017
theorem B16666681 : Blo 2163435 16666681 := bstep (se 2 (by rfl) ⟨6250005, by rfl⟩ : syracuseStep 16666681 = 12500011) B12500011
theorem B22222241 : Blo 2163435 22222241 := bstep (se 2 (by rfl) ⟨8333340, by rfl⟩ : syracuseStep 22222241 = 16666681) B16666681
theorem B14814827 : Blo 2163435 14814827 := bstep (se 1 (by rfl) ⟨11111120, by rfl⟩ : syracuseStep 14814827 = 22222241) B22222241
theorem B9876551 : Blo 2163435 9876551 := bstep (se 1 (by rfl) ⟨7407413, by rfl⟩ : syracuseStep 9876551 = 14814827) B14814827
theorem B26337469 : Blo 2163435 26337469 := bstep (se 3 (by rfl) ⟨4938275, by rfl⟩ : syracuseStep 26337469 = 9876551) B9876551
theorem B35116625 : Blo 2163435 35116625 := bstep (se 2 (by rfl) ⟨13168734, by rfl⟩ : syracuseStep 35116625 = 26337469) B26337469
theorem B93644333 : Blo 2163435 93644333 := bstep (se 3 (by rfl) ⟨17558312, by rfl⟩ : syracuseStep 93644333 = 35116625) B35116625
theorem B62429555 : Blo 2163435 62429555 := bstep (se 1 (by rfl) ⟨46822166, by rfl⟩ : syracuseStep 62429555 = 93644333) B93644333
theorem B41619703 : Blo 2163435 41619703 := bstep (se 1 (by rfl) ⟨31214777, by rfl⟩ : syracuseStep 41619703 = 62429555) B62429555
theorem B55492937 : Blo 2163435 55492937 := bstep (se 2 (by rfl) ⟨20809851, by rfl⟩ : syracuseStep 55492937 = 41619703) B41619703
theorem B36995291 : Blo 2163435 36995291 := bstep (se 1 (by rfl) ⟨27746468, by rfl⟩ : syracuseStep 36995291 = 55492937) B55492937
theorem B24663527 : Blo 2163435 24663527 := bstep (se 1 (by rfl) ⟨18497645, by rfl⟩ : syracuseStep 24663527 = 36995291) B36995291
theorem B16442351 : Blo 2163435 16442351 := bstep (se 1 (by rfl) ⟨12331763, by rfl⟩ : syracuseStep 16442351 = 24663527) B24663527
theorem B10961567 : Blo 2163435 10961567 := bstep (se 1 (by rfl) ⟨8221175, by rfl⟩ : syracuseStep 10961567 = 16442351) B16442351
theorem B7307711 : Blo 2163435 7307711 := bstep (se 1 (by rfl) ⟨5480783, by rfl⟩ : syracuseStep 7307711 = 10961567) B10961567
theorem B4871807 : Blo 2163435 4871807 := bstep (se 1 (by rfl) ⟨3653855, by rfl⟩ : syracuseStep 4871807 = 7307711) B7307711
theorem B3247871 : Blo 2163435 3247871 := bstep (se 1 (by rfl) ⟨2435903, by rfl⟩ : syracuseStep 3247871 = 4871807) B4871807
theorem B2165247 : Blo 2163435 2165247 := bstep (se 1 (by rfl) ⟨1623935, by rfl⟩ : syracuseStep 2165247 = 3247871) B3247871
theorem B3247877 : Blo 2163435 3247877 := bbase (se 4 (by rfl) ⟨304488, by rfl⟩ : syracuseStep 3247877 = 608977) (by norm_num)
theorem B2165251 : Blo 2163435 2165251 := bstep (se 1 (by rfl) ⟨1623938, by rfl⟩ : syracuseStep 2165251 = 3247877) B3247877
theorem B3653869 : Blo 2163435 3653869 := bbase (se 3 (by rfl) ⟨685100, by rfl⟩ : syracuseStep 3653869 = 1370201) (by norm_num)
theorem B4871825 : Blo 2163435 4871825 := bstep (se 2 (by rfl) ⟨1826934, by rfl⟩ : syracuseStep 4871825 = 3653869) B3653869
theorem B3247883 : Blo 2163435 3247883 := bstep (se 1 (by rfl) ⟨2435912, by rfl⟩ : syracuseStep 3247883 = 4871825) B4871825
theorem B2165255 : Blo 2163435 2165255 := bstep (se 1 (by rfl) ⟨1623941, by rfl⟩ : syracuseStep 2165255 = 3247883) B3247883
theorem B2435917 : Blo 2163435 2435917 := bbase (se 3 (by rfl) ⟨456734, by rfl⟩ : syracuseStep 2435917 = 913469) (by norm_num)
theorem B3247889 : Blo 2163435 3247889 := bstep (se 2 (by rfl) ⟨1217958, by rfl⟩ : syracuseStep 3247889 = 2435917) B2435917
theorem B2165259 : Blo 2163435 2165259 := bstep (se 1 (by rfl) ⟨1623944, by rfl⟩ : syracuseStep 2165259 = 3247889) B3247889
theorem B7307765 : Blo 2163435 7307765 := bbase (se 5 (by rfl) ⟨342551, by rfl⟩ : syracuseStep 7307765 = 685103) (by norm_num)
theorem B4871843 : Blo 2163435 4871843 := bstep (se 1 (by rfl) ⟨3653882, by rfl⟩ : syracuseStep 4871843 = 7307765) B7307765
theorem B3247895 : Blo 2163435 3247895 := bstep (se 1 (by rfl) ⟨2435921, by rfl⟩ : syracuseStep 3247895 = 4871843) B4871843
theorem B2165263 : Blo 2163435 2165263 := bstep (se 1 (by rfl) ⟨1623947, by rfl⟩ : syracuseStep 2165263 = 3247895) B3247895
theorem B3247901 : Blo 2163435 3247901 := bbase (se 3 (by rfl) ⟨608981, by rfl⟩ : syracuseStep 3247901 = 1217963) (by norm_num)
theorem B2165267 : Blo 2163435 2165267 := bstep (se 1 (by rfl) ⟨1623950, by rfl⟩ : syracuseStep 2165267 = 3247901) B3247901
theorem B4871861 : Blo 2163435 4871861 := bbase (se 5 (by rfl) ⟨228368, by rfl⟩ : syracuseStep 4871861 = 456737) (by norm_num)
theorem B3247907 : Blo 2163435 3247907 := bstep (se 1 (by rfl) ⟨2435930, by rfl⟩ : syracuseStep 3247907 = 4871861) B4871861
theorem B2165271 : Blo 2163435 2165271 := bstep (se 1 (by rfl) ⟨1623953, by rfl⟩ : syracuseStep 2165271 = 3247907) B3247907
theorem B12331925 : Blo 2163435 12331925 := bbase (se 6 (by rfl) ⟨289029, by rfl⟩ : syracuseStep 12331925 = 578059) (by norm_num)
theorem B8221283 : Blo 2163435 8221283 := bstep (se 1 (by rfl) ⟨6165962, by rfl⟩ : syracuseStep 8221283 = 12331925) B12331925
theorem B5480855 : Blo 2163435 5480855 := bstep (se 1 (by rfl) ⟨4110641, by rfl⟩ : syracuseStep 5480855 = 8221283) B8221283
theorem B3653903 : Blo 2163435 3653903 := bstep (se 1 (by rfl) ⟨2740427, by rfl⟩ : syracuseStep 3653903 = 5480855) B5480855
theorem B2435935 : Blo 2163435 2435935 := bstep (se 1 (by rfl) ⟨1826951, by rfl⟩ : syracuseStep 2435935 = 3653903) B3653903
theorem B3247913 : Blo 2163435 3247913 := bstep (se 2 (by rfl) ⟨1217967, by rfl⟩ : syracuseStep 3247913 = 2435935) B2435935
theorem B2165275 : Blo 2163435 2165275 := bstep (se 1 (by rfl) ⟨1623956, by rfl⟩ : syracuseStep 2165275 = 3247913) B3247913
theorem B6165973 : Blo 2163435 6165973 := bbase (se 7 (by rfl) ⟨72257, by rfl⟩ : syracuseStep 6165973 = 144515) (by norm_num)
theorem B8221297 : Blo 2163435 8221297 := bstep (se 2 (by rfl) ⟨3082986, by rfl⟩ : syracuseStep 8221297 = 6165973) B6165973
theorem B10961729 : Blo 2163435 10961729 := bstep (se 2 (by rfl) ⟨4110648, by rfl⟩ : syracuseStep 10961729 = 8221297) B8221297
theorem B7307819 : Blo 2163435 7307819 := bstep (se 1 (by rfl) ⟨5480864, by rfl⟩ : syracuseStep 7307819 = 10961729) B10961729
theorem B4871879 : Blo 2163435 4871879 := bstep (se 1 (by rfl) ⟨3653909, by rfl⟩ : syracuseStep 4871879 = 7307819) B7307819
theorem B3247919 : Blo 2163435 3247919 := bstep (se 1 (by rfl) ⟨2435939, by rfl⟩ : syracuseStep 3247919 = 4871879) B4871879
theorem B2165279 : Blo 2163435 2165279 := bstep (se 1 (by rfl) ⟨1623959, by rfl⟩ : syracuseStep 2165279 = 3247919) B3247919
theorem B3247925 : Blo 2163435 3247925 := bbase (se 5 (by rfl) ⟨152246, by rfl⟩ : syracuseStep 3247925 = 304493) (by norm_num)
theorem B2165283 : Blo 2163435 2165283 := bstep (se 1 (by rfl) ⟨1623962, by rfl⟩ : syracuseStep 2165283 = 3247925) B3247925
theorem B5480885 : Blo 2163435 5480885 := bbase (se 5 (by rfl) ⟨256916, by rfl⟩ : syracuseStep 5480885 = 513833) (by norm_num)
theorem B3653923 : Blo 2163435 3653923 := bstep (se 1 (by rfl) ⟨2740442, by rfl⟩ : syracuseStep 3653923 = 5480885) B5480885
theorem B4871897 : Blo 2163435 4871897 := bstep (se 2 (by rfl) ⟨1826961, by rfl⟩ : syracuseStep 4871897 = 3653923) B3653923
theorem B3247931 : Blo 2163435 3247931 := bstep (se 1 (by rfl) ⟨2435948, by rfl⟩ : syracuseStep 3247931 = 4871897) B4871897
theorem B2165287 : Blo 2163435 2165287 := bstep (se 1 (by rfl) ⟨1623965, by rfl⟩ : syracuseStep 2165287 = 3247931) B3247931
theorem B2435953 : Blo 2163435 2435953 := bbase (se 2 (by rfl) ⟨913482, by rfl⟩ : syracuseStep 2435953 = 1826965) (by norm_num)
theorem B3247937 : Blo 2163435 3247937 := bstep (se 2 (by rfl) ⟨1217976, by rfl⟩ : syracuseStep 3247937 = 2435953) B2435953
theorem B2165291 : Blo 2163435 2165291 := bstep (se 1 (by rfl) ⟨1623968, by rfl⟩ : syracuseStep 2165291 = 3247937) B3247937
theorem B9249029 : Blo 2163435 9249029 := bbase (se 4 (by rfl) ⟨867096, by rfl⟩ : syracuseStep 9249029 = 1734193) (by norm_num)
theorem B6166019 : Blo 2163435 6166019 := bstep (se 1 (by rfl) ⟨4624514, by rfl⟩ : syracuseStep 6166019 = 9249029) B9249029
theorem B4110679 : Blo 2163435 4110679 := bstep (se 1 (by rfl) ⟨3083009, by rfl⟩ : syracuseStep 4110679 = 6166019) B6166019
theorem B5480905 : Blo 2163435 5480905 := bstep (se 2 (by rfl) ⟨2055339, by rfl⟩ : syracuseStep 5480905 = 4110679) B4110679
theorem B7307873 : Blo 2163435 7307873 := bstep (se 2 (by rfl) ⟨2740452, by rfl⟩ : syracuseStep 7307873 = 5480905) B5480905
theorem B4871915 : Blo 2163435 4871915 := bstep (se 1 (by rfl) ⟨3653936, by rfl⟩ : syracuseStep 4871915 = 7307873) B7307873
theorem B3247943 : Blo 2163435 3247943 := bstep (se 1 (by rfl) ⟨2435957, by rfl⟩ : syracuseStep 3247943 = 4871915) B4871915
theorem B2165295 : Blo 2163435 2165295 := bstep (se 1 (by rfl) ⟨1623971, by rfl⟩ : syracuseStep 2165295 = 3247943) B3247943
theorem B3247949 : Blo 2163435 3247949 := bbase (se 3 (by rfl) ⟨608990, by rfl⟩ : syracuseStep 3247949 = 1217981) (by norm_num)
theorem B2165299 : Blo 2163435 2165299 := bstep (se 1 (by rfl) ⟨1623974, by rfl⟩ : syracuseStep 2165299 = 3247949) B3247949
theorem B4871933 : Blo 2163435 4871933 := bbase (se 3 (by rfl) ⟨913487, by rfl⟩ : syracuseStep 4871933 = 1826975) (by norm_num)
theorem B3247955 : Blo 2163435 3247955 := bstep (se 1 (by rfl) ⟨2435966, by rfl⟩ : syracuseStep 3247955 = 4871933) B4871933
theorem B2165303 : Blo 2163435 2165303 := bstep (se 1 (by rfl) ⟨1623977, by rfl⟩ : syracuseStep 2165303 = 3247955) B3247955
theorem B3653957 : Blo 2163435 3653957 := bbase (se 4 (by rfl) ⟨342558, by rfl⟩ : syracuseStep 3653957 = 685117) (by norm_num)
theorem B2435971 : Blo 2163435 2435971 := bstep (se 1 (by rfl) ⟨1826978, by rfl⟩ : syracuseStep 2435971 = 3653957) B3653957
theorem B3247961 : Blo 2163435 3247961 := bstep (se 2 (by rfl) ⟨1217985, by rfl⟩ : syracuseStep 3247961 = 2435971) B2435971
theorem B2165307 : Blo 2163435 2165307 := bstep (se 1 (by rfl) ⟨1623980, by rfl⟩ : syracuseStep 2165307 = 3247961) B3247961
theorem B16442837 : Blo 2163435 16442837 := bbase (se 7 (by rfl) ⟨192689, by rfl⟩ : syracuseStep 16442837 = 385379) (by norm_num)
theorem B10961891 : Blo 2163435 10961891 := bstep (se 1 (by rfl) ⟨8221418, by rfl⟩ : syracuseStep 10961891 = 16442837) B16442837
theorem B7307927 : Blo 2163435 7307927 := bstep (se 1 (by rfl) ⟨5480945, by rfl⟩ : syracuseStep 7307927 = 10961891) B10961891
theorem B4871951 : Blo 2163435 4871951 := bstep (se 1 (by rfl) ⟨3653963, by rfl⟩ : syracuseStep 4871951 = 7307927) B7307927
theorem B3247967 : Blo 2163435 3247967 := bstep (se 1 (by rfl) ⟨2435975, by rfl⟩ : syracuseStep 3247967 = 4871951) B4871951
theorem B2165311 : Blo 2163435 2165311 := bstep (se 1 (by rfl) ⟨1623983, by rfl⟩ : syracuseStep 2165311 = 3247967) B3247967
theorem B3247973 : Blo 2163435 3247973 := bbase (se 4 (by rfl) ⟨304497, by rfl⟩ : syracuseStep 3247973 = 608995) (by norm_num)
theorem B2165315 : Blo 2163435 2165315 := bstep (se 1 (by rfl) ⟨1623986, by rfl⟩ : syracuseStep 2165315 = 3247973) B3247973
theorem B4110725 : Blo 2163435 4110725 := bbase (se 4 (by rfl) ⟨385380, by rfl⟩ : syracuseStep 4110725 = 770761) (by norm_num)
theorem B2740483 : Blo 2163435 2740483 := bstep (se 1 (by rfl) ⟨2055362, by rfl⟩ : syracuseStep 2740483 = 4110725) B4110725
theorem B3653977 : Blo 2163435 3653977 := bstep (se 2 (by rfl) ⟨1370241, by rfl⟩ : syracuseStep 3653977 = 2740483) B2740483
theorem B4871969 : Blo 2163435 4871969 := bstep (se 2 (by rfl) ⟨1826988, by rfl⟩ : syracuseStep 4871969 = 3653977) B3653977
theorem B3247979 : Blo 2163435 3247979 := bstep (se 1 (by rfl) ⟨2435984, by rfl⟩ : syracuseStep 3247979 = 4871969) B4871969
theorem B2165319 : Blo 2163435 2165319 := bstep (se 1 (by rfl) ⟨1623989, by rfl⟩ : syracuseStep 2165319 = 3247979) B3247979
theorem B2435989 : Blo 2163435 2435989 := bbase (se 6 (by rfl) ⟨57093, by rfl⟩ : syracuseStep 2435989 = 114187) (by norm_num)
theorem B3247985 : Blo 2163435 3247985 := bstep (se 2 (by rfl) ⟨1217994, by rfl⟩ : syracuseStep 3247985 = 2435989) B2435989
theorem B2165323 : Blo 2163435 2165323 := bstep (se 1 (by rfl) ⟨1623992, by rfl⟩ : syracuseStep 2165323 = 3247985) B3247985
theorem B2740493 : Blo 2163435 2740493 := bbase (se 3 (by rfl) ⟨513842, by rfl⟩ : syracuseStep 2740493 = 1027685) (by norm_num)
theorem B7307981 : Blo 2163435 7307981 := bstep (se 3 (by rfl) ⟨1370246, by rfl⟩ : syracuseStep 7307981 = 2740493) B2740493
theorem B4871987 : Blo 2163435 4871987 := bstep (se 1 (by rfl) ⟨3653990, by rfl⟩ : syracuseStep 4871987 = 7307981) B7307981
theorem B3247991 : Blo 2163435 3247991 := bstep (se 1 (by rfl) ⟨2435993, by rfl⟩ : syracuseStep 3247991 = 4871987) B4871987
theorem B2165327 : Blo 2163435 2165327 := bstep (se 1 (by rfl) ⟨1623995, by rfl⟩ : syracuseStep 2165327 = 3247991) B3247991
theorem B3247997 : Blo 2163435 3247997 := bbase (se 3 (by rfl) ⟨608999, by rfl⟩ : syracuseStep 3247997 = 1217999) (by norm_num)
theorem B2165331 : Blo 2163435 2165331 := bstep (se 1 (by rfl) ⟨1623998, by rfl⟩ : syracuseStep 2165331 = 3247997) B3247997
theorem B4872005 : Blo 2163435 4872005 := bbase (se 4 (by rfl) ⟨456750, by rfl⟩ : syracuseStep 4872005 = 913501) (by norm_num)
theorem B3248003 : Blo 2163435 3248003 := bstep (se 1 (by rfl) ⟨2436002, by rfl⟩ : syracuseStep 3248003 = 4872005) B4872005
theorem B2165335 : Blo 2163435 2165335 := bstep (se 1 (by rfl) ⟨1624001, by rfl⟩ : syracuseStep 2165335 = 3248003) B3248003
theorem B29630933 : Blo 2163435 29630933 := bbase (se 7 (by rfl) ⟨347237, by rfl⟩ : syracuseStep 29630933 = 694475) (by norm_num)
theorem B19753955 : Blo 2163435 19753955 := bstep (se 1 (by rfl) ⟨14815466, by rfl⟩ : syracuseStep 19753955 = 29630933) B29630933
theorem B13169303 : Blo 2163435 13169303 := bstep (se 1 (by rfl) ⟨9876977, by rfl⟩ : syracuseStep 13169303 = 19753955) B19753955
theorem B8779535 : Blo 2163435 8779535 := bstep (se 1 (by rfl) ⟨6584651, by rfl⟩ : syracuseStep 8779535 = 13169303) B13169303
theorem B5853023 : Blo 2163435 5853023 := bstep (se 1 (by rfl) ⟨4389767, by rfl⟩ : syracuseStep 5853023 = 8779535) B8779535
theorem B3902015 : Blo 2163435 3902015 := bstep (se 1 (by rfl) ⟨2926511, by rfl⟩ : syracuseStep 3902015 = 5853023) B5853023
theorem B2601343 : Blo 2163435 2601343 := bstep (se 1 (by rfl) ⟨1951007, by rfl⟩ : syracuseStep 2601343 = 3902015) B3902015
theorem B3468457 : Blo 2163435 3468457 := bstep (se 2 (by rfl) ⟨1300671, by rfl⟩ : syracuseStep 3468457 = 2601343) B2601343
theorem B4624609 : Blo 2163435 4624609 := bstep (se 2 (by rfl) ⟨1734228, by rfl⟩ : syracuseStep 4624609 = 3468457) B3468457
theorem B6166145 : Blo 2163435 6166145 := bstep (se 2 (by rfl) ⟨2312304, by rfl⟩ : syracuseStep 6166145 = 4624609) B4624609
theorem B4110763 : Blo 2163435 4110763 := bstep (se 1 (by rfl) ⟨3083072, by rfl⟩ : syracuseStep 4110763 = 6166145) B6166145
theorem B5481017 : Blo 2163435 5481017 := bstep (se 2 (by rfl) ⟨2055381, by rfl⟩ : syracuseStep 5481017 = 4110763) B4110763
theorem B3654011 : Blo 2163435 3654011 := bstep (se 1 (by rfl) ⟨2740508, by rfl⟩ : syracuseStep 3654011 = 5481017) B5481017
theorem B2436007 : Blo 2163435 2436007 := bstep (se 1 (by rfl) ⟨1827005, by rfl⟩ : syracuseStep 2436007 = 3654011) B3654011
theorem B3248009 : Blo 2163435 3248009 := bstep (se 2 (by rfl) ⟨1218003, by rfl⟩ : syracuseStep 3248009 = 2436007) B2436007
theorem B2165339 : Blo 2163435 2165339 := bstep (se 1 (by rfl) ⟨1624004, by rfl⟩ : syracuseStep 2165339 = 3248009) B3248009
theorem B10962053 : Blo 2163435 10962053 := bbase (se 4 (by rfl) ⟨1027692, by rfl⟩ : syracuseStep 10962053 = 2055385) (by norm_num)
theorem B7308035 : Blo 2163435 7308035 := bstep (se 1 (by rfl) ⟨5481026, by rfl⟩ : syracuseStep 7308035 = 10962053) B10962053
theorem B4872023 : Blo 2163435 4872023 := bstep (se 1 (by rfl) ⟨3654017, by rfl⟩ : syracuseStep 4872023 = 7308035) B7308035
theorem B3248015 : Blo 2163435 3248015 := bstep (se 1 (by rfl) ⟨2436011, by rfl⟩ : syracuseStep 3248015 = 4872023) B4872023
theorem B2165343 : Blo 2163435 2165343 := bstep (se 1 (by rfl) ⟨1624007, by rfl⟩ : syracuseStep 2165343 = 3248015) B3248015
theorem B3248021 : Blo 2163435 3248021 := bbase (se 6 (by rfl) ⟨76125, by rfl⟩ : syracuseStep 3248021 = 152251) (by norm_num)
theorem B2165347 : Blo 2163435 2165347 := bstep (se 1 (by rfl) ⟨1624010, by rfl⟩ : syracuseStep 2165347 = 3248021) B3248021
theorem B2312317 : Blo 2163435 2312317 := bbase (se 3 (by rfl) ⟨433559, by rfl⟩ : syracuseStep 2312317 = 867119) (by norm_num)
theorem B12332357 : Blo 2163435 12332357 := bstep (se 4 (by rfl) ⟨1156158, by rfl⟩ : syracuseStep 12332357 = 2312317) B2312317
theorem B8221571 : Blo 2163435 8221571 := bstep (se 1 (by rfl) ⟨6166178, by rfl⟩ : syracuseStep 8221571 = 12332357) B12332357
theorem B5481047 : Blo 2163435 5481047 := bstep (se 1 (by rfl) ⟨4110785, by rfl⟩ : syracuseStep 5481047 = 8221571) B8221571
theorem B3654031 : Blo 2163435 3654031 := bstep (se 1 (by rfl) ⟨2740523, by rfl⟩ : syracuseStep 3654031 = 5481047) B5481047
theorem B4872041 : Blo 2163435 4872041 := bstep (se 2 (by rfl) ⟨1827015, by rfl⟩ : syracuseStep 4872041 = 3654031) B3654031
theorem B3248027 : Blo 2163435 3248027 := bstep (se 1 (by rfl) ⟨2436020, by rfl⟩ : syracuseStep 3248027 = 4872041) B4872041
theorem B2165351 : Blo 2163435 2165351 := bstep (se 1 (by rfl) ⟨1624013, by rfl⟩ : syracuseStep 2165351 = 3248027) B3248027
theorem B2436025 : Blo 2163435 2436025 := bbase (se 2 (by rfl) ⟨913509, by rfl⟩ : syracuseStep 2436025 = 1827019) (by norm_num)
theorem B3248033 : Blo 2163435 3248033 := bstep (se 2 (by rfl) ⟨1218012, by rfl⟩ : syracuseStep 3248033 = 2436025) B2436025
theorem B2165355 : Blo 2163435 2165355 := bstep (se 1 (by rfl) ⟨1624016, by rfl⟩ : syracuseStep 2165355 = 3248033) B3248033
theorem B5202733 : Blo 2163435 5202733 := bbase (se 3 (by rfl) ⟨975512, by rfl⟩ : syracuseStep 5202733 = 1951025) (by norm_num)
theorem B6936977 : Blo 2163435 6936977 := bstep (se 2 (by rfl) ⟨2601366, by rfl⟩ : syracuseStep 6936977 = 5202733) B5202733
theorem B4624651 : Blo 2163435 4624651 := bstep (se 1 (by rfl) ⟨3468488, by rfl⟩ : syracuseStep 4624651 = 6936977) B6936977
theorem B6166201 : Blo 2163435 6166201 := bstep (se 2 (by rfl) ⟨2312325, by rfl⟩ : syracuseStep 6166201 = 4624651) B4624651
theorem B8221601 : Blo 2163435 8221601 := bstep (se 2 (by rfl) ⟨3083100, by rfl⟩ : syracuseStep 8221601 = 6166201) B6166201
theorem B5481067 : Blo 2163435 5481067 := bstep (se 1 (by rfl) ⟨4110800, by rfl⟩ : syracuseStep 5481067 = 8221601) B8221601
theorem B7308089 : Blo 2163435 7308089 := bstep (se 2 (by rfl) ⟨2740533, by rfl⟩ : syracuseStep 7308089 = 5481067) B5481067
theorem B4872059 : Blo 2163435 4872059 := bstep (se 1 (by rfl) ⟨3654044, by rfl⟩ : syracuseStep 4872059 = 7308089) B7308089
theorem B3248039 : Blo 2163435 3248039 := bstep (se 1 (by rfl) ⟨2436029, by rfl⟩ : syracuseStep 3248039 = 4872059) B4872059
theorem B2165359 : Blo 2163435 2165359 := bstep (se 1 (by rfl) ⟨1624019, by rfl⟩ : syracuseStep 2165359 = 3248039) B3248039
theorem B3248045 : Blo 2163435 3248045 := bbase (se 3 (by rfl) ⟨609008, by rfl⟩ : syracuseStep 3248045 = 1218017) (by norm_num)
theorem B2165363 : Blo 2163435 2165363 := bstep (se 1 (by rfl) ⟨1624022, by rfl⟩ : syracuseStep 2165363 = 3248045) B3248045
theorem B4872077 : Blo 2163435 4872077 := bbase (se 3 (by rfl) ⟨913514, by rfl⟩ : syracuseStep 4872077 = 1827029) (by norm_num)
theorem B3248051 : Blo 2163435 3248051 := bstep (se 1 (by rfl) ⟨2436038, by rfl⟩ : syracuseStep 3248051 = 4872077) B4872077
theorem B2165367 : Blo 2163435 2165367 := bstep (se 1 (by rfl) ⟨1624025, by rfl⟩ : syracuseStep 2165367 = 3248051) B3248051
theorem B2740549 : Blo 2163435 2740549 := bbase (se 4 (by rfl) ⟨256926, by rfl⟩ : syracuseStep 2740549 = 513853) (by norm_num)
theorem B3654065 : Blo 2163435 3654065 := bstep (se 2 (by rfl) ⟨1370274, by rfl⟩ : syracuseStep 3654065 = 2740549) B2740549
theorem B2436043 : Blo 2163435 2436043 := bstep (se 1 (by rfl) ⟨1827032, by rfl⟩ : syracuseStep 2436043 = 3654065) B3654065
theorem B3248057 : Blo 2163435 3248057 := bstep (se 2 (by rfl) ⟨1218021, by rfl⟩ : syracuseStep 3248057 = 2436043) B2436043
theorem B2165371 : Blo 2163435 2165371 := bstep (se 1 (by rfl) ⟨1624028, by rfl⟩ : syracuseStep 2165371 = 3248057) B3248057
theorem B10405541 : Blo 2163435 10405541 := bbase (se 4 (by rfl) ⟨975519, by rfl⟩ : syracuseStep 10405541 = 1951039) (by norm_num)
theorem B27748109 : Blo 2163435 27748109 := bstep (se 3 (by rfl) ⟨5202770, by rfl⟩ : syracuseStep 27748109 = 10405541) B10405541
theorem B18498739 : Blo 2163435 18498739 := bstep (se 1 (by rfl) ⟨13874054, by rfl⟩ : syracuseStep 18498739 = 27748109) B27748109
theorem B24664985 : Blo 2163435 24664985 := bstep (se 2 (by rfl) ⟨9249369, by rfl⟩ : syracuseStep 24664985 = 18498739) B18498739
theorem B16443323 : Blo 2163435 16443323 := bstep (se 1 (by rfl) ⟨12332492, by rfl⟩ : syracuseStep 16443323 = 24664985) B24664985
theorem B10962215 : Blo 2163435 10962215 := bstep (se 1 (by rfl) ⟨8221661, by rfl⟩ : syracuseStep 10962215 = 16443323) B16443323
theorem B7308143 : Blo 2163435 7308143 := bstep (se 1 (by rfl) ⟨5481107, by rfl⟩ : syracuseStep 7308143 = 10962215) B10962215
theorem B4872095 : Blo 2163435 4872095 := bstep (se 1 (by rfl) ⟨3654071, by rfl⟩ : syracuseStep 4872095 = 7308143) B7308143
theorem B3248063 : Blo 2163435 3248063 := bstep (se 1 (by rfl) ⟨2436047, by rfl⟩ : syracuseStep 3248063 = 4872095) B4872095
theorem B2165375 : Blo 2163435 2165375 := bstep (se 1 (by rfl) ⟨1624031, by rfl⟩ : syracuseStep 2165375 = 3248063) B3248063
theorem B3248069 : Blo 2163435 3248069 := bbase (se 4 (by rfl) ⟨304506, by rfl⟩ : syracuseStep 3248069 = 609013) (by norm_num)
theorem B2165379 : Blo 2163435 2165379 := bstep (se 1 (by rfl) ⟨1624034, by rfl⟩ : syracuseStep 2165379 = 3248069) B3248069
theorem B3654085 : Blo 2163435 3654085 := bbase (se 4 (by rfl) ⟨342570, by rfl⟩ : syracuseStep 3654085 = 685141) (by norm_num)
theorem B4872113 : Blo 2163435 4872113 := bstep (se 2 (by rfl) ⟨1827042, by rfl⟩ : syracuseStep 4872113 = 3654085) B3654085
theorem B3248075 : Blo 2163435 3248075 := bstep (se 1 (by rfl) ⟨2436056, by rfl⟩ : syracuseStep 3248075 = 4872113) B4872113
theorem B2165383 : Blo 2163435 2165383 := bstep (se 1 (by rfl) ⟨1624037, by rfl⟩ : syracuseStep 2165383 = 3248075) B3248075
theorem B2436061 : Blo 2163435 2436061 := bbase (se 3 (by rfl) ⟨456761, by rfl⟩ : syracuseStep 2436061 = 913523) (by norm_num)
theorem B3248081 : Blo 2163435 3248081 := bstep (se 2 (by rfl) ⟨1218030, by rfl⟩ : syracuseStep 3248081 = 2436061) B2436061
theorem B2165387 : Blo 2163435 2165387 := bstep (se 1 (by rfl) ⟨1624040, by rfl⟩ : syracuseStep 2165387 = 3248081) B3248081
theorem B7308197 : Blo 2163435 7308197 := bbase (se 4 (by rfl) ⟨685143, by rfl⟩ : syracuseStep 7308197 = 1370287) (by norm_num)
theorem B4872131 : Blo 2163435 4872131 := bstep (se 1 (by rfl) ⟨3654098, by rfl⟩ : syracuseStep 4872131 = 7308197) B7308197
theorem B3248087 : Blo 2163435 3248087 := bstep (se 1 (by rfl) ⟨2436065, by rfl⟩ : syracuseStep 3248087 = 4872131) B4872131
theorem B2165391 : Blo 2163435 2165391 := bstep (se 1 (by rfl) ⟨1624043, by rfl⟩ : syracuseStep 2165391 = 3248087) B3248087
theorem B3248093 : Blo 2163435 3248093 := bbase (se 3 (by rfl) ⟨609017, by rfl⟩ : syracuseStep 3248093 = 1218035) (by norm_num)
theorem B2165395 : Blo 2163435 2165395 := bstep (se 1 (by rfl) ⟨1624046, by rfl⟩ : syracuseStep 2165395 = 3248093) B3248093
theorem B4872149 : Blo 2163435 4872149 := bbase (se 7 (by rfl) ⟨57095, by rfl⟩ : syracuseStep 4872149 = 114191) (by norm_num)
theorem B3248099 : Blo 2163435 3248099 := bstep (se 1 (by rfl) ⟨2436074, by rfl⟩ : syracuseStep 3248099 = 4872149) B4872149
theorem B2165399 : Blo 2163435 2165399 := bstep (se 1 (by rfl) ⟨1624049, by rfl⟩ : syracuseStep 2165399 = 3248099) B3248099
theorem B11706389 : Blo 2163435 11706389 := bbase (se 6 (by rfl) ⟨274368, by rfl⟩ : syracuseStep 11706389 = 548737) (by norm_num)
theorem B7804259 : Blo 2163435 7804259 := bstep (se 1 (by rfl) ⟨5853194, by rfl⟩ : syracuseStep 7804259 = 11706389) B11706389
theorem B5202839 : Blo 2163435 5202839 := bstep (se 1 (by rfl) ⟨3902129, by rfl⟩ : syracuseStep 5202839 = 7804259) B7804259
theorem B13874237 : Blo 2163435 13874237 := bstep (se 3 (by rfl) ⟨2601419, by rfl⟩ : syracuseStep 13874237 = 5202839) B5202839
theorem B9249491 : Blo 2163435 9249491 := bstep (se 1 (by rfl) ⟨6937118, by rfl⟩ : syracuseStep 9249491 = 13874237) B13874237
theorem B6166327 : Blo 2163435 6166327 := bstep (se 1 (by rfl) ⟨4624745, by rfl⟩ : syracuseStep 6166327 = 9249491) B9249491
theorem B8221769 : Blo 2163435 8221769 := bstep (se 2 (by rfl) ⟨3083163, by rfl⟩ : syracuseStep 8221769 = 6166327) B6166327
theorem B5481179 : Blo 2163435 5481179 := bstep (se 1 (by rfl) ⟨4110884, by rfl⟩ : syracuseStep 5481179 = 8221769) B8221769
theorem B3654119 : Blo 2163435 3654119 := bstep (se 1 (by rfl) ⟨2740589, by rfl⟩ : syracuseStep 3654119 = 5481179) B5481179
theorem B2436079 : Blo 2163435 2436079 := bstep (se 1 (by rfl) ⟨1827059, by rfl⟩ : syracuseStep 2436079 = 3654119) B3654119
theorem B3248105 : Blo 2163435 3248105 := bstep (se 2 (by rfl) ⟨1218039, by rfl⟩ : syracuseStep 3248105 = 2436079) B2436079
theorem B2165403 : Blo 2163435 2165403 := bstep (se 1 (by rfl) ⟨1624052, by rfl⟩ : syracuseStep 2165403 = 3248105) B3248105
theorem B3468565 : Blo 2163435 3468565 := bbase (se 6 (by rfl) ⟨81294, by rfl⟩ : syracuseStep 3468565 = 162589) (by norm_num)
theorem B18499013 : Blo 2163435 18499013 := bstep (se 4 (by rfl) ⟨1734282, by rfl⟩ : syracuseStep 18499013 = 3468565) B3468565
theorem B12332675 : Blo 2163435 12332675 := bstep (se 1 (by rfl) ⟨9249506, by rfl⟩ : syracuseStep 12332675 = 18499013) B18499013
theorem B8221783 : Blo 2163435 8221783 := bstep (se 1 (by rfl) ⟨6166337, by rfl⟩ : syracuseStep 8221783 = 12332675) B12332675
theorem B10962377 : Blo 2163435 10962377 := bstep (se 2 (by rfl) ⟨4110891, by rfl⟩ : syracuseStep 10962377 = 8221783) B8221783
theorem B7308251 : Blo 2163435 7308251 := bstep (se 1 (by rfl) ⟨5481188, by rfl⟩ : syracuseStep 7308251 = 10962377) B10962377
theorem B4872167 : Blo 2163435 4872167 := bstep (se 1 (by rfl) ⟨3654125, by rfl⟩ : syracuseStep 4872167 = 7308251) B7308251
theorem B3248111 : Blo 2163435 3248111 := bstep (se 1 (by rfl) ⟨2436083, by rfl⟩ : syracuseStep 3248111 = 4872167) B4872167
theorem B2165407 : Blo 2163435 2165407 := bstep (se 1 (by rfl) ⟨1624055, by rfl⟩ : syracuseStep 2165407 = 3248111) B3248111
theorem B3248117 : Blo 2163435 3248117 := bbase (se 5 (by rfl) ⟨152255, by rfl⟩ : syracuseStep 3248117 = 304511) (by norm_num)
theorem B2165411 : Blo 2163435 2165411 := bstep (se 1 (by rfl) ⟨1624058, by rfl⟩ : syracuseStep 2165411 = 3248117) B3248117
theorem B6937157 : Blo 2163435 6937157 := bbase (se 4 (by rfl) ⟨650358, by rfl⟩ : syracuseStep 6937157 = 1300717) (by norm_num)
theorem B4624771 : Blo 2163435 4624771 := bstep (se 1 (by rfl) ⟨3468578, by rfl⟩ : syracuseStep 4624771 = 6937157) B6937157
theorem B6166361 : Blo 2163435 6166361 := bstep (se 2 (by rfl) ⟨2312385, by rfl⟩ : syracuseStep 6166361 = 4624771) B4624771
theorem B4110907 : Blo 2163435 4110907 := bstep (se 1 (by rfl) ⟨3083180, by rfl⟩ : syracuseStep 4110907 = 6166361) B6166361
theorem B5481209 : Blo 2163435 5481209 := bstep (se 2 (by rfl) ⟨2055453, by rfl⟩ : syracuseStep 5481209 = 4110907) B4110907
theorem B3654139 : Blo 2163435 3654139 := bstep (se 1 (by rfl) ⟨2740604, by rfl⟩ : syracuseStep 3654139 = 5481209) B5481209
theorem B4872185 : Blo 2163435 4872185 := bstep (se 2 (by rfl) ⟨1827069, by rfl⟩ : syracuseStep 4872185 = 3654139) B3654139
theorem B3248123 : Blo 2163435 3248123 := bstep (se 1 (by rfl) ⟨2436092, by rfl⟩ : syracuseStep 3248123 = 4872185) B4872185
theorem B2165415 : Blo 2163435 2165415 := bstep (se 1 (by rfl) ⟨1624061, by rfl⟩ : syracuseStep 2165415 = 3248123) B3248123
theorem B2436097 : Blo 2163435 2436097 := bbase (se 2 (by rfl) ⟨913536, by rfl⟩ : syracuseStep 2436097 = 1827073) (by norm_num)
theorem B3248129 : Blo 2163435 3248129 := bstep (se 2 (by rfl) ⟨1218048, by rfl⟩ : syracuseStep 3248129 = 2436097) B2436097
theorem B2165419 : Blo 2163435 2165419 := bstep (se 1 (by rfl) ⟨1624064, by rfl⟩ : syracuseStep 2165419 = 3248129) B3248129
theorem B5481229 : Blo 2163435 5481229 := bbase (se 3 (by rfl) ⟨1027730, by rfl⟩ : syracuseStep 5481229 = 2055461) (by norm_num)
theorem B7308305 : Blo 2163435 7308305 := bstep (se 2 (by rfl) ⟨2740614, by rfl⟩ : syracuseStep 7308305 = 5481229) B5481229
theorem B4872203 : Blo 2163435 4872203 := bstep (se 1 (by rfl) ⟨3654152, by rfl⟩ : syracuseStep 4872203 = 7308305) B7308305
theorem B3248135 : Blo 2163435 3248135 := bstep (se 1 (by rfl) ⟨2436101, by rfl⟩ : syracuseStep 3248135 = 4872203) B4872203
theorem B2165423 : Blo 2163435 2165423 := bstep (se 1 (by rfl) ⟨1624067, by rfl⟩ : syracuseStep 2165423 = 3248135) B3248135
theorem B3248141 : Blo 2163435 3248141 := bbase (se 3 (by rfl) ⟨609026, by rfl⟩ : syracuseStep 3248141 = 1218053) (by norm_num)
theorem B2165427 : Blo 2163435 2165427 := bstep (se 1 (by rfl) ⟨1624070, by rfl⟩ : syracuseStep 2165427 = 3248141) B3248141
theorem B4872221 : Blo 2163435 4872221 := bbase (se 3 (by rfl) ⟨913541, by rfl⟩ : syracuseStep 4872221 = 1827083) (by norm_num)
theorem B3248147 : Blo 2163435 3248147 := bstep (se 1 (by rfl) ⟨2436110, by rfl⟩ : syracuseStep 3248147 = 4872221) B4872221
theorem B2165431 : Blo 2163435 2165431 := bstep (se 1 (by rfl) ⟨1624073, by rfl⟩ : syracuseStep 2165431 = 3248147) B3248147
theorem B3654173 : Blo 2163435 3654173 := bbase (se 3 (by rfl) ⟨685157, by rfl⟩ : syracuseStep 3654173 = 1370315) (by norm_num)
theorem B2436115 : Blo 2163435 2436115 := bstep (se 1 (by rfl) ⟨1827086, by rfl⟩ : syracuseStep 2436115 = 3654173) B3654173
theorem B3248153 : Blo 2163435 3248153 := bstep (se 2 (by rfl) ⟨1218057, by rfl⟩ : syracuseStep 3248153 = 2436115) B2436115
theorem B2165435 : Blo 2163435 2165435 := bstep (se 1 (by rfl) ⟨1624076, by rfl⟩ : syracuseStep 2165435 = 3248153) B3248153
theorem C0 (j : ℕ) (h1 : 540858 ≤ j) (h2 : j ≤ 541358) : Blo 2163435 (4 * j + 3) := by
  interval_cases j
  · exact B2163435
  · exact B2163439
  · exact B2163443
  · exact B2163447
  · exact B2163451
  · exact B2163455
  · exact B2163459
  · exact B2163463
  · exact B2163467
  · exact B2163471
  · exact B2163475
  · exact B2163479
  · exact B2163483
  · exact B2163487
  · exact B2163491
  · exact B2163495
  · exact B2163499
  · exact B2163503
  · exact B2163507
  · exact B2163511
  · exact B2163515
  · exact B2163519
  · exact B2163523
  · exact B2163527
  · exact B2163531
  · exact B2163535
  · exact B2163539
  · exact B2163543
  · exact B2163547
  · exact B2163551
  · exact B2163555
  · exact B2163559
  · exact B2163563
  · exact B2163567
  · exact B2163571
  · exact B2163575
  · exact B2163579
  · exact B2163583
  · exact B2163587
  · exact B2163591
  · exact B2163595
  · exact B2163599
  · exact B2163603
  · exact B2163607
  · exact B2163611
  · exact B2163615
  · exact B2163619
  · exact B2163623
  · exact B2163627
  · exact B2163631
  · exact B2163635
  · exact B2163639
  · exact B2163643
  · exact B2163647
  · exact B2163651
  · exact B2163655
  · exact B2163659
  · exact B2163663
  · exact B2163667
  · exact B2163671
  · exact B2163675
  · exact B2163679
  · exact B2163683
  · exact B2163687
  · exact B2163691
  · exact B2163695
  · exact B2163699
  · exact B2163703
  · exact B2163707
  · exact B2163711
  · exact B2163715
  · exact B2163719
  · exact B2163723
  · exact B2163727
  · exact B2163731
  · exact B2163735
  · exact B2163739
  · exact B2163743
  · exact B2163747
  · exact B2163751
  · exact B2163755
  · exact B2163759
  · exact B2163763
  · exact B2163767
  · exact B2163771
  · exact B2163775
  · exact B2163779
  · exact B2163783
  · exact B2163787
  · exact B2163791
  · exact B2163795
  · exact B2163799
  · exact B2163803
  · exact B2163807
  · exact B2163811
  · exact B2163815
  · exact B2163819
  · exact B2163823
  · exact B2163827
  · exact B2163831
  · exact B2163835
  · exact B2163839
  · exact B2163843
  · exact B2163847
  · exact B2163851
  · exact B2163855
  · exact B2163859
  · exact B2163863
  · exact B2163867
  · exact B2163871
  · exact B2163875
  · exact B2163879
  · exact B2163883
  · exact B2163887
  · exact B2163891
  · exact B2163895
  · exact B2163899
  · exact B2163903
  · exact B2163907
  · exact B2163911
  · exact B2163915
  · exact B2163919
  · exact B2163923
  · exact B2163927
  · exact B2163931
  · exact B2163935
  · exact B2163939
  · exact B2163943
  · exact B2163947
  · exact B2163951
  · exact B2163955
  · exact B2163959
  · exact B2163963
  · exact B2163967
  · exact B2163971
  · exact B2163975
  · exact B2163979
  · exact B2163983
  · exact B2163987
  · exact B2163991
  · exact B2163995
  · exact B2163999
  · exact B2164003
  · exact B2164007
  · exact B2164011
  · exact B2164015
  · exact B2164019
  · exact B2164023
  · exact B2164027
  · exact B2164031
  · exact B2164035
  · exact B2164039
  · exact B2164043
  · exact B2164047
  · exact B2164051
  · exact B2164055
  · exact B2164059
  · exact B2164063
  · exact B2164067
  · exact B2164071
  · exact B2164075
  · exact B2164079
  · exact B2164083
  · exact B2164087
  · exact B2164091
  · exact B2164095
  · exact B2164099
  · exact B2164103
  · exact B2164107
  · exact B2164111
  · exact B2164115
  · exact B2164119
  · exact B2164123
  · exact B2164127
  · exact B2164131
  · exact B2164135
  · exact B2164139
  · exact B2164143
  · exact B2164147
  · exact B2164151
  · exact B2164155
  · exact B2164159
  · exact B2164163
  · exact B2164167
  · exact B2164171
  · exact B2164175
  · exact B2164179
  · exact B2164183
  · exact B2164187
  · exact B2164191
  · exact B2164195
  · exact B2164199
  · exact B2164203
  · exact B2164207
  · exact B2164211
  · exact B2164215
  · exact B2164219
  · exact B2164223
  · exact B2164227
  · exact B2164231
  · exact B2164235
  · exact B2164239
  · exact B2164243
  · exact B2164247
  · exact B2164251
  · exact B2164255
  · exact B2164259
  · exact B2164263
  · exact B2164267
  · exact B2164271
  · exact B2164275
  · exact B2164279
  · exact B2164283
  · exact B2164287
  · exact B2164291
  · exact B2164295
  · exact B2164299
  · exact B2164303
  · exact B2164307
  · exact B2164311
  · exact B2164315
  · exact B2164319
  · exact B2164323
  · exact B2164327
  · exact B2164331
  · exact B2164335
  · exact B2164339
  · exact B2164343
  · exact B2164347
  · exact B2164351
  · exact B2164355
  · exact B2164359
  · exact B2164363
  · exact B2164367
  · exact B2164371
  · exact B2164375
  · exact B2164379
  · exact B2164383
  · exact B2164387
  · exact B2164391
  · exact B2164395
  · exact B2164399
  · exact B2164403
  · exact B2164407
  · exact B2164411
  · exact B2164415
  · exact B2164419
  · exact B2164423
  · exact B2164427
  · exact B2164431
  · exact B2164435
  · exact B2164439
  · exact B2164443
  · exact B2164447
  · exact B2164451
  · exact B2164455
  · exact B2164459
  · exact B2164463
  · exact B2164467
  · exact B2164471
  · exact B2164475
  · exact B2164479
  · exact B2164483
  · exact B2164487
  · exact B2164491
  · exact B2164495
  · exact B2164499
  · exact B2164503
  · exact B2164507
  · exact B2164511
  · exact B2164515
  · exact B2164519
  · exact B2164523
  · exact B2164527
  · exact B2164531
  · exact B2164535
  · exact B2164539
  · exact B2164543
  · exact B2164547
  · exact B2164551
  · exact B2164555
  · exact B2164559
  · exact B2164563
  · exact B2164567
  · exact B2164571
  · exact B2164575
  · exact B2164579
  · exact B2164583
  · exact B2164587
  · exact B2164591
  · exact B2164595
  · exact B2164599
  · exact B2164603
  · exact B2164607
  · exact B2164611
  · exact B2164615
  · exact B2164619
  · exact B2164623
  · exact B2164627
  · exact B2164631
  · exact B2164635
  · exact B2164639
  · exact B2164643
  · exact B2164647
  · exact B2164651
  · exact B2164655
  · exact B2164659
  · exact B2164663
  · exact B2164667
  · exact B2164671
  · exact B2164675
  · exact B2164679
  · exact B2164683
  · exact B2164687
  · exact B2164691
  · exact B2164695
  · exact B2164699
  · exact B2164703
  · exact B2164707
  · exact B2164711
  · exact B2164715
  · exact B2164719
  · exact B2164723
  · exact B2164727
  · exact B2164731
  · exact B2164735
  · exact B2164739
  · exact B2164743
  · exact B2164747
  · exact B2164751
  · exact B2164755
  · exact B2164759
  · exact B2164763
  · exact B2164767
  · exact B2164771
  · exact B2164775
  · exact B2164779
  · exact B2164783
  · exact B2164787
  · exact B2164791
  · exact B2164795
  · exact B2164799
  · exact B2164803
  · exact B2164807
  · exact B2164811
  · exact B2164815
  · exact B2164819
  · exact B2164823
  · exact B2164827
  · exact B2164831
  · exact B2164835
  · exact B2164839
  · exact B2164843
  · exact B2164847
  · exact B2164851
  · exact B2164855
  · exact B2164859
  · exact B2164863
  · exact B2164867
  · exact B2164871
  · exact B2164875
  · exact B2164879
  · exact B2164883
  · exact B2164887
  · exact B2164891
  · exact B2164895
  · exact B2164899
  · exact B2164903
  · exact B2164907
  · exact B2164911
  · exact B2164915
  · exact B2164919
  · exact B2164923
  · exact B2164927
  · exact B2164931
  · exact B2164935
  · exact B2164939
  · exact B2164943
  · exact B2164947
  · exact B2164951
  · exact B2164955
  · exact B2164959
  · exact B2164963
  · exact B2164967
  · exact B2164971
  · exact B2164975
  · exact B2164979
  · exact B2164983
  · exact B2164987
  · exact B2164991
  · exact B2164995
  · exact B2164999
  · exact B2165003
  · exact B2165007
  · exact B2165011
  · exact B2165015
  · exact B2165019
  · exact B2165023
  · exact B2165027
  · exact B2165031
  · exact B2165035
  · exact B2165039
  · exact B2165043
  · exact B2165047
  · exact B2165051
  · exact B2165055
  · exact B2165059
  · exact B2165063
  · exact B2165067
  · exact B2165071
  · exact B2165075
  · exact B2165079
  · exact B2165083
  · exact B2165087
  · exact B2165091
  · exact B2165095
  · exact B2165099
  · exact B2165103
  · exact B2165107
  · exact B2165111
  · exact B2165115
  · exact B2165119
  · exact B2165123
  · exact B2165127
  · exact B2165131
  · exact B2165135
  · exact B2165139
  · exact B2165143
  · exact B2165147
  · exact B2165151
  · exact B2165155
  · exact B2165159
  · exact B2165163
  · exact B2165167
  · exact B2165171
  · exact B2165175
  · exact B2165179
  · exact B2165183
  · exact B2165187
  · exact B2165191
  · exact B2165195
  · exact B2165199
  · exact B2165203
  · exact B2165207
  · exact B2165211
  · exact B2165215
  · exact B2165219
  · exact B2165223
  · exact B2165227
  · exact B2165231
  · exact B2165235
  · exact B2165239
  · exact B2165243
  · exact B2165247
  · exact B2165251
  · exact B2165255
  · exact B2165259
  · exact B2165263
  · exact B2165267
  · exact B2165271
  · exact B2165275
  · exact B2165279
  · exact B2165283
  · exact B2165287
  · exact B2165291
  · exact B2165295
  · exact B2165299
  · exact B2165303
  · exact B2165307
  · exact B2165311
  · exact B2165315
  · exact B2165319
  · exact B2165323
  · exact B2165327
  · exact B2165331
  · exact B2165335
  · exact B2165339
  · exact B2165343
  · exact B2165347
  · exact B2165351
  · exact B2165355
  · exact B2165359
  · exact B2165363
  · exact B2165367
  · exact B2165371
  · exact B2165375
  · exact B2165379
  · exact B2165383
  · exact B2165387
  · exact B2165391
  · exact B2165395
  · exact B2165399
  · exact B2165403
  · exact B2165407
  · exact B2165411
  · exact B2165415
  · exact B2165419
  · exact B2165423
  · exact B2165427
  · exact B2165431
  · exact B2165435
theorem solution (m : ℕ) (hlo : 2163435 ≤ m) (hhi : m ≤ 2165435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 540858 ≤ j := by omega
    have hj2 : j ≤ 541358 := by omega
    have hb : Blo 2163435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
