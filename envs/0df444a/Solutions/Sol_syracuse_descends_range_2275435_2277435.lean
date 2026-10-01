-- Prove2me | solution 1 for syracuse_descends_range_2275435_2277435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:49:31.66139+00:00
-- url     : https://prove2.me/submissions/71790ed6-0c13-467a-9d21-f958c7f9ec36

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

theorem B2559865 : Blo 2275435 2559865 := bbase (se 2 (by rfl) ⟨959949, by rfl⟩ : syracuseStep 2559865 = 1919899) (by norm_num)
theorem B3413153 : Blo 2275435 3413153 := bstep (se 2 (by rfl) ⟨1279932, by rfl⟩ : syracuseStep 3413153 = 2559865) B2559865
theorem B2275435 : Blo 2275435 2275435 := bstep (se 1 (by rfl) ⟨1706576, by rfl⟩ : syracuseStep 2275435 = 3413153) B3413153
theorem B2306485 : Blo 2275435 2306485 := bbase (se 5 (by rfl) ⟨108116, by rfl⟩ : syracuseStep 2306485 = 216233) (by norm_num)
theorem B12301253 : Blo 2275435 12301253 := bstep (se 4 (by rfl) ⟨1153242, by rfl⟩ : syracuseStep 12301253 = 2306485) B2306485
theorem B8200835 : Blo 2275435 8200835 := bstep (se 1 (by rfl) ⟨6150626, by rfl⟩ : syracuseStep 8200835 = 12301253) B12301253
theorem B5467223 : Blo 2275435 5467223 := bstep (se 1 (by rfl) ⟨4100417, by rfl⟩ : syracuseStep 5467223 = 8200835) B8200835
theorem B14579261 : Blo 2275435 14579261 := bstep (se 3 (by rfl) ⟨2733611, by rfl⟩ : syracuseStep 14579261 = 5467223) B5467223
theorem B9719507 : Blo 2275435 9719507 := bstep (se 1 (by rfl) ⟨7289630, by rfl⟩ : syracuseStep 9719507 = 14579261) B14579261
theorem B6479671 : Blo 2275435 6479671 := bstep (se 1 (by rfl) ⟨4859753, by rfl⟩ : syracuseStep 6479671 = 9719507) B9719507
theorem B8639561 : Blo 2275435 8639561 := bstep (se 2 (by rfl) ⟨3239835, by rfl⟩ : syracuseStep 8639561 = 6479671) B6479671
theorem B5759707 : Blo 2275435 5759707 := bstep (se 1 (by rfl) ⟨4319780, by rfl⟩ : syracuseStep 5759707 = 8639561) B8639561
theorem B7679609 : Blo 2275435 7679609 := bstep (se 2 (by rfl) ⟨2879853, by rfl⟩ : syracuseStep 7679609 = 5759707) B5759707
theorem B5119739 : Blo 2275435 5119739 := bstep (se 1 (by rfl) ⟨3839804, by rfl⟩ : syracuseStep 5119739 = 7679609) B7679609
theorem B3413159 : Blo 2275435 3413159 := bstep (se 1 (by rfl) ⟨2559869, by rfl⟩ : syracuseStep 3413159 = 5119739) B5119739
theorem B2275439 : Blo 2275435 2275439 := bstep (se 1 (by rfl) ⟨1706579, by rfl⟩ : syracuseStep 2275439 = 3413159) B3413159
theorem B3413165 : Blo 2275435 3413165 := bbase (se 3 (by rfl) ⟨639968, by rfl⟩ : syracuseStep 3413165 = 1279937) (by norm_num)
theorem B2275443 : Blo 2275435 2275443 := bstep (se 1 (by rfl) ⟨1706582, by rfl⟩ : syracuseStep 2275443 = 3413165) B3413165
theorem B5119757 : Blo 2275435 5119757 := bbase (se 3 (by rfl) ⟨959954, by rfl⟩ : syracuseStep 5119757 = 1919909) (by norm_num)
theorem B3413171 : Blo 2275435 3413171 := bstep (se 1 (by rfl) ⟨2559878, by rfl⟩ : syracuseStep 3413171 = 5119757) B5119757
theorem B2275447 : Blo 2275435 2275447 := bstep (se 1 (by rfl) ⟨1706585, by rfl⟩ : syracuseStep 2275447 = 3413171) B3413171
theorem B2879869 : Blo 2275435 2879869 := bbase (se 3 (by rfl) ⟨539975, by rfl⟩ : syracuseStep 2879869 = 1079951) (by norm_num)
theorem B3839825 : Blo 2275435 3839825 := bstep (se 2 (by rfl) ⟨1439934, by rfl⟩ : syracuseStep 3839825 = 2879869) B2879869
theorem B2559883 : Blo 2275435 2559883 := bstep (se 1 (by rfl) ⟨1919912, by rfl⟩ : syracuseStep 2559883 = 3839825) B3839825
theorem B3413177 : Blo 2275435 3413177 := bstep (se 2 (by rfl) ⟨1279941, by rfl⟩ : syracuseStep 3413177 = 2559883) B2559883
theorem B2275451 : Blo 2275435 2275451 := bstep (se 1 (by rfl) ⟨1706588, by rfl⟩ : syracuseStep 2275451 = 3413177) B3413177
theorem B5467261 : Blo 2275435 5467261 := bbase (se 3 (by rfl) ⟨1025111, by rfl⟩ : syracuseStep 5467261 = 2050223) (by norm_num)
theorem B7289681 : Blo 2275435 7289681 := bstep (se 2 (by rfl) ⟨2733630, by rfl⟩ : syracuseStep 7289681 = 5467261) B5467261
theorem B19439149 : Blo 2275435 19439149 := bstep (se 3 (by rfl) ⟨3644840, by rfl⟩ : syracuseStep 19439149 = 7289681) B7289681
theorem B25918865 : Blo 2275435 25918865 := bstep (se 2 (by rfl) ⟨9719574, by rfl⟩ : syracuseStep 25918865 = 19439149) B19439149
theorem B17279243 : Blo 2275435 17279243 := bstep (se 1 (by rfl) ⟨12959432, by rfl⟩ : syracuseStep 17279243 = 25918865) B25918865
theorem B11519495 : Blo 2275435 11519495 := bstep (se 1 (by rfl) ⟨8639621, by rfl⟩ : syracuseStep 11519495 = 17279243) B17279243
theorem B7679663 : Blo 2275435 7679663 := bstep (se 1 (by rfl) ⟨5759747, by rfl⟩ : syracuseStep 7679663 = 11519495) B11519495
theorem B5119775 : Blo 2275435 5119775 := bstep (se 1 (by rfl) ⟨3839831, by rfl⟩ : syracuseStep 5119775 = 7679663) B7679663
theorem B3413183 : Blo 2275435 3413183 := bstep (se 1 (by rfl) ⟨2559887, by rfl⟩ : syracuseStep 3413183 = 5119775) B5119775
theorem B2275455 : Blo 2275435 2275455 := bstep (se 1 (by rfl) ⟨1706591, by rfl⟩ : syracuseStep 2275455 = 3413183) B3413183
theorem B3413189 : Blo 2275435 3413189 := bbase (se 4 (by rfl) ⟨319986, by rfl⟩ : syracuseStep 3413189 = 639973) (by norm_num)
theorem B2275459 : Blo 2275435 2275459 := bstep (se 1 (by rfl) ⟨1706594, by rfl⟩ : syracuseStep 2275459 = 3413189) B3413189
theorem B3839845 : Blo 2275435 3839845 := bbase (se 4 (by rfl) ⟨359985, by rfl⟩ : syracuseStep 3839845 = 719971) (by norm_num)
theorem B5119793 : Blo 2275435 5119793 := bstep (se 2 (by rfl) ⟨1919922, by rfl⟩ : syracuseStep 5119793 = 3839845) B3839845
theorem B3413195 : Blo 2275435 3413195 := bstep (se 1 (by rfl) ⟨2559896, by rfl⟩ : syracuseStep 3413195 = 5119793) B5119793
theorem B2275463 : Blo 2275435 2275463 := bstep (se 1 (by rfl) ⟨1706597, by rfl⟩ : syracuseStep 2275463 = 3413195) B3413195
theorem B2559901 : Blo 2275435 2559901 := bbase (se 3 (by rfl) ⟨479981, by rfl⟩ : syracuseStep 2559901 = 959963) (by norm_num)
theorem B3413201 : Blo 2275435 3413201 := bstep (se 2 (by rfl) ⟨1279950, by rfl⟩ : syracuseStep 3413201 = 2559901) B2559901
theorem B2275467 : Blo 2275435 2275467 := bstep (se 1 (by rfl) ⟨1706600, by rfl⟩ : syracuseStep 2275467 = 3413201) B3413201
theorem B7679717 : Blo 2275435 7679717 := bbase (se 4 (by rfl) ⟨719973, by rfl⟩ : syracuseStep 7679717 = 1439947) (by norm_num)
theorem B5119811 : Blo 2275435 5119811 := bstep (se 1 (by rfl) ⟨3839858, by rfl⟩ : syracuseStep 5119811 = 7679717) B7679717
theorem B3413207 : Blo 2275435 3413207 := bstep (se 1 (by rfl) ⟨2559905, by rfl⟩ : syracuseStep 3413207 = 5119811) B5119811
theorem B2275471 : Blo 2275435 2275471 := bstep (se 1 (by rfl) ⟨1706603, by rfl⟩ : syracuseStep 2275471 = 3413207) B3413207
theorem B3413213 : Blo 2275435 3413213 := bbase (se 3 (by rfl) ⟨639977, by rfl⟩ : syracuseStep 3413213 = 1279955) (by norm_num)
theorem B2275475 : Blo 2275435 2275475 := bstep (se 1 (by rfl) ⟨1706606, by rfl⟩ : syracuseStep 2275475 = 3413213) B3413213
theorem B5119829 : Blo 2275435 5119829 := bbase (se 9 (by rfl) ⟨14999, by rfl⟩ : syracuseStep 5119829 = 29999) (by norm_num)
theorem B3413219 : Blo 2275435 3413219 := bstep (se 1 (by rfl) ⟨2559914, by rfl⟩ : syracuseStep 3413219 = 5119829) B5119829
theorem B2275479 : Blo 2275435 2275479 := bstep (se 1 (by rfl) ⟨1706609, by rfl⟩ : syracuseStep 2275479 = 3413219) B3413219
theorem B6479797 : Blo 2275435 6479797 := bbase (se 5 (by rfl) ⟨303740, by rfl⟩ : syracuseStep 6479797 = 607481) (by norm_num)
theorem B8639729 : Blo 2275435 8639729 := bstep (se 2 (by rfl) ⟨3239898, by rfl⟩ : syracuseStep 8639729 = 6479797) B6479797
theorem B5759819 : Blo 2275435 5759819 := bstep (se 1 (by rfl) ⟨4319864, by rfl⟩ : syracuseStep 5759819 = 8639729) B8639729
theorem B3839879 : Blo 2275435 3839879 := bstep (se 1 (by rfl) ⟨2879909, by rfl⟩ : syracuseStep 3839879 = 5759819) B5759819
theorem B2559919 : Blo 2275435 2559919 := bstep (se 1 (by rfl) ⟨1919939, by rfl⟩ : syracuseStep 2559919 = 3839879) B3839879
theorem B3413225 : Blo 2275435 3413225 := bstep (se 2 (by rfl) ⟨1279959, by rfl⟩ : syracuseStep 3413225 = 2559919) B2559919
theorem B2275483 : Blo 2275435 2275483 := bstep (se 1 (by rfl) ⟨1706612, by rfl⟩ : syracuseStep 2275483 = 3413225) B3413225
theorem B3694621 : Blo 2275435 3694621 := bbase (se 3 (by rfl) ⟨692741, by rfl⟩ : syracuseStep 3694621 = 1385483) (by norm_num)
theorem B4926161 : Blo 2275435 4926161 := bstep (se 2 (by rfl) ⟨1847310, by rfl⟩ : syracuseStep 4926161 = 3694621) B3694621
theorem B3284107 : Blo 2275435 3284107 := bstep (se 1 (by rfl) ⟨2463080, by rfl⟩ : syracuseStep 3284107 = 4926161) B4926161
theorem B70060949 : Blo 2275435 70060949 := bstep (se 6 (by rfl) ⟨1642053, by rfl⟩ : syracuseStep 70060949 = 3284107) B3284107
theorem B46707299 : Blo 2275435 46707299 := bstep (se 1 (by rfl) ⟨35030474, by rfl⟩ : syracuseStep 46707299 = 70060949) B70060949
theorem B31138199 : Blo 2275435 31138199 := bstep (se 1 (by rfl) ⟨23353649, by rfl⟩ : syracuseStep 31138199 = 46707299) B46707299
theorem B20758799 : Blo 2275435 20758799 := bstep (se 1 (by rfl) ⟨15569099, by rfl⟩ : syracuseStep 20758799 = 31138199) B31138199
theorem B55356797 : Blo 2275435 55356797 := bstep (se 3 (by rfl) ⟨10379399, by rfl⟩ : syracuseStep 55356797 = 20758799) B20758799
theorem B147618125 : Blo 2275435 147618125 := bstep (se 3 (by rfl) ⟨27678398, by rfl⟩ : syracuseStep 147618125 = 55356797) B55356797
theorem B98412083 : Blo 2275435 98412083 := bstep (se 1 (by rfl) ⟨73809062, by rfl⟩ : syracuseStep 98412083 = 147618125) B147618125
theorem B65608055 : Blo 2275435 65608055 := bstep (se 1 (by rfl) ⟨49206041, by rfl⟩ : syracuseStep 65608055 = 98412083) B98412083
theorem B43738703 : Blo 2275435 43738703 := bstep (se 1 (by rfl) ⟨32804027, by rfl⟩ : syracuseStep 43738703 = 65608055) B65608055
theorem B29159135 : Blo 2275435 29159135 := bstep (se 1 (by rfl) ⟨21869351, by rfl⟩ : syracuseStep 29159135 = 43738703) B43738703
theorem B19439423 : Blo 2275435 19439423 := bstep (se 1 (by rfl) ⟨14579567, by rfl⟩ : syracuseStep 19439423 = 29159135) B29159135
theorem B12959615 : Blo 2275435 12959615 := bstep (se 1 (by rfl) ⟨9719711, by rfl⟩ : syracuseStep 12959615 = 19439423) B19439423
theorem B8639743 : Blo 2275435 8639743 := bstep (se 1 (by rfl) ⟨6479807, by rfl⟩ : syracuseStep 8639743 = 12959615) B12959615
theorem B11519657 : Blo 2275435 11519657 := bstep (se 2 (by rfl) ⟨4319871, by rfl⟩ : syracuseStep 11519657 = 8639743) B8639743
theorem B7679771 : Blo 2275435 7679771 := bstep (se 1 (by rfl) ⟨5759828, by rfl⟩ : syracuseStep 7679771 = 11519657) B11519657
theorem B5119847 : Blo 2275435 5119847 := bstep (se 1 (by rfl) ⟨3839885, by rfl⟩ : syracuseStep 5119847 = 7679771) B7679771
theorem B3413231 : Blo 2275435 3413231 := bstep (se 1 (by rfl) ⟨2559923, by rfl⟩ : syracuseStep 3413231 = 5119847) B5119847
theorem B2275487 : Blo 2275435 2275487 := bstep (se 1 (by rfl) ⟨1706615, by rfl⟩ : syracuseStep 2275487 = 3413231) B3413231
theorem B3413237 : Blo 2275435 3413237 := bbase (se 5 (by rfl) ⟨159995, by rfl⟩ : syracuseStep 3413237 = 319991) (by norm_num)
theorem B2275491 : Blo 2275435 2275491 := bstep (se 1 (by rfl) ⟨1706618, by rfl⟩ : syracuseStep 2275491 = 3413237) B3413237
theorem B7784581 : Blo 2275435 7784581 := bbase (se 4 (by rfl) ⟨729804, by rfl⟩ : syracuseStep 7784581 = 1459609) (by norm_num)
theorem B10379441 : Blo 2275435 10379441 := bstep (se 2 (by rfl) ⟨3892290, by rfl⟩ : syracuseStep 10379441 = 7784581) B7784581
theorem B6919627 : Blo 2275435 6919627 := bstep (se 1 (by rfl) ⟨5189720, by rfl⟩ : syracuseStep 6919627 = 10379441) B10379441
theorem B9226169 : Blo 2275435 9226169 := bstep (se 2 (by rfl) ⟨3459813, by rfl⟩ : syracuseStep 9226169 = 6919627) B6919627
theorem B6150779 : Blo 2275435 6150779 := bstep (se 1 (by rfl) ⟨4613084, by rfl⟩ : syracuseStep 6150779 = 9226169) B9226169
theorem B4100519 : Blo 2275435 4100519 := bstep (se 1 (by rfl) ⟨3075389, by rfl⟩ : syracuseStep 4100519 = 6150779) B6150779
theorem B2733679 : Blo 2275435 2733679 := bstep (se 1 (by rfl) ⟨2050259, by rfl⟩ : syracuseStep 2733679 = 4100519) B4100519
theorem B14579621 : Blo 2275435 14579621 := bstep (se 4 (by rfl) ⟨1366839, by rfl⟩ : syracuseStep 14579621 = 2733679) B2733679
theorem B9719747 : Blo 2275435 9719747 := bstep (se 1 (by rfl) ⟨7289810, by rfl⟩ : syracuseStep 9719747 = 14579621) B14579621
theorem B6479831 : Blo 2275435 6479831 := bstep (se 1 (by rfl) ⟨4859873, by rfl⟩ : syracuseStep 6479831 = 9719747) B9719747
theorem B4319887 : Blo 2275435 4319887 := bstep (se 1 (by rfl) ⟨3239915, by rfl⟩ : syracuseStep 4319887 = 6479831) B6479831
theorem B5759849 : Blo 2275435 5759849 := bstep (se 2 (by rfl) ⟨2159943, by rfl⟩ : syracuseStep 5759849 = 4319887) B4319887
theorem B3839899 : Blo 2275435 3839899 := bstep (se 1 (by rfl) ⟨2879924, by rfl⟩ : syracuseStep 3839899 = 5759849) B5759849
theorem B5119865 : Blo 2275435 5119865 := bstep (se 2 (by rfl) ⟨1919949, by rfl⟩ : syracuseStep 5119865 = 3839899) B3839899
theorem B3413243 : Blo 2275435 3413243 := bstep (se 1 (by rfl) ⟨2559932, by rfl⟩ : syracuseStep 3413243 = 5119865) B5119865
theorem B2275495 : Blo 2275435 2275495 := bstep (se 1 (by rfl) ⟨1706621, by rfl⟩ : syracuseStep 2275495 = 3413243) B3413243
theorem B2559937 : Blo 2275435 2559937 := bbase (se 2 (by rfl) ⟨959976, by rfl⟩ : syracuseStep 2559937 = 1919953) (by norm_num)
theorem B3413249 : Blo 2275435 3413249 := bstep (se 2 (by rfl) ⟨1279968, by rfl⟩ : syracuseStep 3413249 = 2559937) B2559937
theorem B2275499 : Blo 2275435 2275499 := bstep (se 1 (by rfl) ⟨1706624, by rfl⟩ : syracuseStep 2275499 = 3413249) B3413249
theorem B5759869 : Blo 2275435 5759869 := bbase (se 3 (by rfl) ⟨1079975, by rfl⟩ : syracuseStep 5759869 = 2159951) (by norm_num)
theorem B7679825 : Blo 2275435 7679825 := bstep (se 2 (by rfl) ⟨2879934, by rfl⟩ : syracuseStep 7679825 = 5759869) B5759869
theorem B5119883 : Blo 2275435 5119883 := bstep (se 1 (by rfl) ⟨3839912, by rfl⟩ : syracuseStep 5119883 = 7679825) B7679825
theorem B3413255 : Blo 2275435 3413255 := bstep (se 1 (by rfl) ⟨2559941, by rfl⟩ : syracuseStep 3413255 = 5119883) B5119883
theorem B2275503 : Blo 2275435 2275503 := bstep (se 1 (by rfl) ⟨1706627, by rfl⟩ : syracuseStep 2275503 = 3413255) B3413255
theorem B3413261 : Blo 2275435 3413261 := bbase (se 3 (by rfl) ⟨639986, by rfl⟩ : syracuseStep 3413261 = 1279973) (by norm_num)
theorem B2275507 : Blo 2275435 2275507 := bstep (se 1 (by rfl) ⟨1706630, by rfl⟩ : syracuseStep 2275507 = 3413261) B3413261
theorem B5119901 : Blo 2275435 5119901 := bbase (se 3 (by rfl) ⟨959981, by rfl⟩ : syracuseStep 5119901 = 1919963) (by norm_num)
theorem B3413267 : Blo 2275435 3413267 := bstep (se 1 (by rfl) ⟨2559950, by rfl⟩ : syracuseStep 3413267 = 5119901) B5119901
theorem B2275511 : Blo 2275435 2275511 := bstep (se 1 (by rfl) ⟨1706633, by rfl⟩ : syracuseStep 2275511 = 3413267) B3413267
theorem B3839933 : Blo 2275435 3839933 := bbase (se 3 (by rfl) ⟨719987, by rfl⟩ : syracuseStep 3839933 = 1439975) (by norm_num)
theorem B2559955 : Blo 2275435 2559955 := bstep (se 1 (by rfl) ⟨1919966, by rfl⟩ : syracuseStep 2559955 = 3839933) B3839933
theorem B3413273 : Blo 2275435 3413273 := bstep (se 2 (by rfl) ⟨1279977, by rfl⟩ : syracuseStep 3413273 = 2559955) B2559955
theorem B2275515 : Blo 2275435 2275515 := bstep (se 1 (by rfl) ⟨1706636, by rfl⟩ : syracuseStep 2275515 = 3413273) B3413273
theorem B12959797 : Blo 2275435 12959797 := bbase (se 5 (by rfl) ⟨607490, by rfl⟩ : syracuseStep 12959797 = 1214981) (by norm_num)
theorem B17279729 : Blo 2275435 17279729 := bstep (se 2 (by rfl) ⟨6479898, by rfl⟩ : syracuseStep 17279729 = 12959797) B12959797
theorem B11519819 : Blo 2275435 11519819 := bstep (se 1 (by rfl) ⟨8639864, by rfl⟩ : syracuseStep 11519819 = 17279729) B17279729
theorem B7679879 : Blo 2275435 7679879 := bstep (se 1 (by rfl) ⟨5759909, by rfl⟩ : syracuseStep 7679879 = 11519819) B11519819
theorem B5119919 : Blo 2275435 5119919 := bstep (se 1 (by rfl) ⟨3839939, by rfl⟩ : syracuseStep 5119919 = 7679879) B7679879
theorem B3413279 : Blo 2275435 3413279 := bstep (se 1 (by rfl) ⟨2559959, by rfl⟩ : syracuseStep 3413279 = 5119919) B5119919
theorem B2275519 : Blo 2275435 2275519 := bstep (se 1 (by rfl) ⟨1706639, by rfl⟩ : syracuseStep 2275519 = 3413279) B3413279
theorem B3413285 : Blo 2275435 3413285 := bbase (se 4 (by rfl) ⟨319995, by rfl⟩ : syracuseStep 3413285 = 639991) (by norm_num)
theorem B2275523 : Blo 2275435 2275523 := bstep (se 1 (by rfl) ⟨1706642, by rfl⟩ : syracuseStep 2275523 = 3413285) B3413285
theorem B2879965 : Blo 2275435 2879965 := bbase (se 3 (by rfl) ⟨539993, by rfl⟩ : syracuseStep 2879965 = 1079987) (by norm_num)
theorem B3839953 : Blo 2275435 3839953 := bstep (se 2 (by rfl) ⟨1439982, by rfl⟩ : syracuseStep 3839953 = 2879965) B2879965
theorem B5119937 : Blo 2275435 5119937 := bstep (se 2 (by rfl) ⟨1919976, by rfl⟩ : syracuseStep 5119937 = 3839953) B3839953
theorem B3413291 : Blo 2275435 3413291 := bstep (se 1 (by rfl) ⟨2559968, by rfl⟩ : syracuseStep 3413291 = 5119937) B5119937
theorem B2275527 : Blo 2275435 2275527 := bstep (se 1 (by rfl) ⟨1706645, by rfl⟩ : syracuseStep 2275527 = 3413291) B3413291
theorem B2559973 : Blo 2275435 2559973 := bbase (se 4 (by rfl) ⟨239997, by rfl⟩ : syracuseStep 2559973 = 479995) (by norm_num)
theorem B3413297 : Blo 2275435 3413297 := bstep (se 2 (by rfl) ⟨1279986, by rfl⟩ : syracuseStep 3413297 = 2559973) B2559973
theorem B2275531 : Blo 2275435 2275531 := bstep (se 1 (by rfl) ⟨1706648, by rfl⟩ : syracuseStep 2275531 = 3413297) B3413297
theorem B17315989 : Blo 2275435 17315989 := bbase (se 6 (by rfl) ⟨405843, by rfl⟩ : syracuseStep 17315989 = 811687) (by norm_num)
theorem B369407765 : Blo 2275435 369407765 := bstep (se 6 (by rfl) ⟨8657994, by rfl⟩ : syracuseStep 369407765 = 17315989) B17315989
theorem B246271843 : Blo 2275435 246271843 := bstep (se 1 (by rfl) ⟨184703882, by rfl⟩ : syracuseStep 246271843 = 369407765) B369407765
theorem B328362457 : Blo 2275435 328362457 := bstep (se 2 (by rfl) ⟨123135921, by rfl⟩ : syracuseStep 328362457 = 246271843) B246271843
theorem B437816609 : Blo 2275435 437816609 := bstep (se 2 (by rfl) ⟨164181228, by rfl⟩ : syracuseStep 437816609 = 328362457) B328362457
theorem B291877739 : Blo 2275435 291877739 := bstep (se 1 (by rfl) ⟨218908304, by rfl⟩ : syracuseStep 291877739 = 437816609) B437816609
theorem B194585159 : Blo 2275435 194585159 := bstep (se 1 (by rfl) ⟨145938869, by rfl⟩ : syracuseStep 194585159 = 291877739) B291877739
theorem B129723439 : Blo 2275435 129723439 := bstep (se 1 (by rfl) ⟨97292579, by rfl⟩ : syracuseStep 129723439 = 194585159) B194585159
theorem B172964585 : Blo 2275435 172964585 := bstep (se 2 (by rfl) ⟨64861719, by rfl⟩ : syracuseStep 172964585 = 129723439) B129723439
theorem B461238893 : Blo 2275435 461238893 := bstep (se 3 (by rfl) ⟨86482292, by rfl⟩ : syracuseStep 461238893 = 172964585) B172964585
theorem B307492595 : Blo 2275435 307492595 := bstep (se 1 (by rfl) ⟨230619446, by rfl⟩ : syracuseStep 307492595 = 461238893) B461238893
theorem B204995063 : Blo 2275435 204995063 := bstep (se 1 (by rfl) ⟨153746297, by rfl⟩ : syracuseStep 204995063 = 307492595) B307492595
theorem B136663375 : Blo 2275435 136663375 := bstep (se 1 (by rfl) ⟨102497531, by rfl⟩ : syracuseStep 136663375 = 204995063) B204995063
theorem B182217833 : Blo 2275435 182217833 := bstep (se 2 (by rfl) ⟨68331687, by rfl⟩ : syracuseStep 182217833 = 136663375) B136663375
theorem B121478555 : Blo 2275435 121478555 := bstep (se 1 (by rfl) ⟨91108916, by rfl⟩ : syracuseStep 121478555 = 182217833) B182217833
theorem B80985703 : Blo 2275435 80985703 := bstep (se 1 (by rfl) ⟨60739277, by rfl⟩ : syracuseStep 80985703 = 121478555) B121478555
theorem B107980937 : Blo 2275435 107980937 := bstep (se 2 (by rfl) ⟨40492851, by rfl⟩ : syracuseStep 107980937 = 80985703) B80985703
theorem B71987291 : Blo 2275435 71987291 := bstep (se 1 (by rfl) ⟨53990468, by rfl⟩ : syracuseStep 71987291 = 107980937) B107980937
theorem B47991527 : Blo 2275435 47991527 := bstep (se 1 (by rfl) ⟨35993645, by rfl⟩ : syracuseStep 47991527 = 71987291) B71987291
theorem B31994351 : Blo 2275435 31994351 := bstep (se 1 (by rfl) ⟨23995763, by rfl⟩ : syracuseStep 31994351 = 47991527) B47991527
theorem B21329567 : Blo 2275435 21329567 := bstep (se 1 (by rfl) ⟨15997175, by rfl⟩ : syracuseStep 21329567 = 31994351) B31994351
theorem B14219711 : Blo 2275435 14219711 := bstep (se 1 (by rfl) ⟨10664783, by rfl⟩ : syracuseStep 14219711 = 21329567) B21329567
theorem B9479807 : Blo 2275435 9479807 := bstep (se 1 (by rfl) ⟨7109855, by rfl⟩ : syracuseStep 9479807 = 14219711) B14219711
theorem B6319871 : Blo 2275435 6319871 := bstep (se 1 (by rfl) ⟨4739903, by rfl⟩ : syracuseStep 6319871 = 9479807) B9479807
theorem B4213247 : Blo 2275435 4213247 := bstep (se 1 (by rfl) ⟨3159935, by rfl⟩ : syracuseStep 4213247 = 6319871) B6319871
theorem B44941301 : Blo 2275435 44941301 := bstep (se 5 (by rfl) ⟨2106623, by rfl⟩ : syracuseStep 44941301 = 4213247) B4213247
theorem B29960867 : Blo 2275435 29960867 := bstep (se 1 (by rfl) ⟨22470650, by rfl⟩ : syracuseStep 29960867 = 44941301) B44941301
theorem B79895645 : Blo 2275435 79895645 := bstep (se 3 (by rfl) ⟨14980433, by rfl⟩ : syracuseStep 79895645 = 29960867) B29960867
theorem B53263763 : Blo 2275435 53263763 := bstep (se 1 (by rfl) ⟨39947822, by rfl⟩ : syracuseStep 53263763 = 79895645) B79895645
theorem B35509175 : Blo 2275435 35509175 := bstep (se 1 (by rfl) ⟨26631881, by rfl⟩ : syracuseStep 35509175 = 53263763) B53263763
theorem B23672783 : Blo 2275435 23672783 := bstep (se 1 (by rfl) ⟨17754587, by rfl⟩ : syracuseStep 23672783 = 35509175) B35509175
theorem B63127421 : Blo 2275435 63127421 := bstep (se 3 (by rfl) ⟨11836391, by rfl⟩ : syracuseStep 63127421 = 23672783) B23672783
theorem B42084947 : Blo 2275435 42084947 := bstep (se 1 (by rfl) ⟨31563710, by rfl⟩ : syracuseStep 42084947 = 63127421) B63127421
theorem B28056631 : Blo 2275435 28056631 := bstep (se 1 (by rfl) ⟨21042473, by rfl⟩ : syracuseStep 28056631 = 42084947) B42084947
theorem B37408841 : Blo 2275435 37408841 := bstep (se 2 (by rfl) ⟨14028315, by rfl⟩ : syracuseStep 37408841 = 28056631) B28056631
theorem B24939227 : Blo 2275435 24939227 := bstep (se 1 (by rfl) ⟨18704420, by rfl⟩ : syracuseStep 24939227 = 37408841) B37408841
theorem B16626151 : Blo 2275435 16626151 := bstep (se 1 (by rfl) ⟨12469613, by rfl⟩ : syracuseStep 16626151 = 24939227) B24939227
theorem B88672805 : Blo 2275435 88672805 := bstep (se 4 (by rfl) ⟨8313075, by rfl⟩ : syracuseStep 88672805 = 16626151) B16626151
theorem B59115203 : Blo 2275435 59115203 := bstep (se 1 (by rfl) ⟨44336402, by rfl⟩ : syracuseStep 59115203 = 88672805) B88672805
theorem B39410135 : Blo 2275435 39410135 := bstep (se 1 (by rfl) ⟨29557601, by rfl⟩ : syracuseStep 39410135 = 59115203) B59115203
theorem B26273423 : Blo 2275435 26273423 := bstep (se 1 (by rfl) ⟨19705067, by rfl⟩ : syracuseStep 26273423 = 39410135) B39410135
theorem B17515615 : Blo 2275435 17515615 := bstep (se 1 (by rfl) ⟨13136711, by rfl⟩ : syracuseStep 17515615 = 26273423) B26273423
theorem B23354153 : Blo 2275435 23354153 := bstep (se 2 (by rfl) ⟨8757807, by rfl⟩ : syracuseStep 23354153 = 17515615) B17515615
theorem B15569435 : Blo 2275435 15569435 := bstep (se 1 (by rfl) ⟨11677076, by rfl⟩ : syracuseStep 15569435 = 23354153) B23354153
theorem B10379623 : Blo 2275435 10379623 := bstep (se 1 (by rfl) ⟨7784717, by rfl⟩ : syracuseStep 10379623 = 15569435) B15569435
theorem B13839497 : Blo 2275435 13839497 := bstep (se 2 (by rfl) ⟨5189811, by rfl⟩ : syracuseStep 13839497 = 10379623) B10379623
theorem B9226331 : Blo 2275435 9226331 := bstep (se 1 (by rfl) ⟨6919748, by rfl⟩ : syracuseStep 9226331 = 13839497) B13839497
theorem B6150887 : Blo 2275435 6150887 := bstep (se 1 (by rfl) ⟨4613165, by rfl⟩ : syracuseStep 6150887 = 9226331) B9226331
theorem B4100591 : Blo 2275435 4100591 := bstep (se 1 (by rfl) ⟨3075443, by rfl⟩ : syracuseStep 4100591 = 6150887) B6150887
theorem B10934909 : Blo 2275435 10934909 := bstep (se 3 (by rfl) ⟨2050295, by rfl⟩ : syracuseStep 10934909 = 4100591) B4100591
theorem B7289939 : Blo 2275435 7289939 := bstep (se 1 (by rfl) ⟨5467454, by rfl⟩ : syracuseStep 7289939 = 10934909) B10934909
theorem B4859959 : Blo 2275435 4859959 := bstep (se 1 (by rfl) ⟨3644969, by rfl⟩ : syracuseStep 4859959 = 7289939) B7289939
theorem B6479945 : Blo 2275435 6479945 := bstep (se 2 (by rfl) ⟨2429979, by rfl⟩ : syracuseStep 6479945 = 4859959) B4859959
theorem B4319963 : Blo 2275435 4319963 := bstep (se 1 (by rfl) ⟨3239972, by rfl⟩ : syracuseStep 4319963 = 6479945) B6479945
theorem B2879975 : Blo 2275435 2879975 := bstep (se 1 (by rfl) ⟨2159981, by rfl⟩ : syracuseStep 2879975 = 4319963) B4319963
theorem B7679933 : Blo 2275435 7679933 := bstep (se 3 (by rfl) ⟨1439987, by rfl⟩ : syracuseStep 7679933 = 2879975) B2879975
theorem B5119955 : Blo 2275435 5119955 := bstep (se 1 (by rfl) ⟨3839966, by rfl⟩ : syracuseStep 5119955 = 7679933) B7679933
theorem B3413303 : Blo 2275435 3413303 := bstep (se 1 (by rfl) ⟨2559977, by rfl⟩ : syracuseStep 3413303 = 5119955) B5119955
theorem B2275535 : Blo 2275435 2275535 := bstep (se 1 (by rfl) ⟨1706651, by rfl⟩ : syracuseStep 2275535 = 3413303) B3413303
theorem B3413309 : Blo 2275435 3413309 := bbase (se 3 (by rfl) ⟨639995, by rfl⟩ : syracuseStep 3413309 = 1279991) (by norm_num)
theorem B2275539 : Blo 2275435 2275539 := bstep (se 1 (by rfl) ⟨1706654, by rfl⟩ : syracuseStep 2275539 = 3413309) B3413309
theorem B5119973 : Blo 2275435 5119973 := bbase (se 4 (by rfl) ⟨479997, by rfl⟩ : syracuseStep 5119973 = 959995) (by norm_num)
theorem B3413315 : Blo 2275435 3413315 := bstep (se 1 (by rfl) ⟨2559986, by rfl⟩ : syracuseStep 3413315 = 5119973) B5119973
theorem B2275543 : Blo 2275435 2275543 := bstep (se 1 (by rfl) ⟨1706657, by rfl⟩ : syracuseStep 2275543 = 3413315) B3413315
theorem B5759981 : Blo 2275435 5759981 := bbase (se 3 (by rfl) ⟨1079996, by rfl⟩ : syracuseStep 5759981 = 2159993) (by norm_num)
theorem B3839987 : Blo 2275435 3839987 := bstep (se 1 (by rfl) ⟨2879990, by rfl⟩ : syracuseStep 3839987 = 5759981) B5759981
theorem B2559991 : Blo 2275435 2559991 := bstep (se 1 (by rfl) ⟨1919993, by rfl⟩ : syracuseStep 2559991 = 3839987) B3839987
theorem B3413321 : Blo 2275435 3413321 := bstep (se 2 (by rfl) ⟨1279995, by rfl⟩ : syracuseStep 3413321 = 2559991) B2559991
theorem B2275547 : Blo 2275435 2275547 := bstep (se 1 (by rfl) ⟨1706660, by rfl⟩ : syracuseStep 2275547 = 3413321) B3413321
theorem B5467493 : Blo 2275435 5467493 := bbase (se 4 (by rfl) ⟨512577, by rfl⟩ : syracuseStep 5467493 = 1025155) (by norm_num)
theorem B3644995 : Blo 2275435 3644995 := bstep (se 1 (by rfl) ⟨2733746, by rfl⟩ : syracuseStep 3644995 = 5467493) B5467493
theorem B4859993 : Blo 2275435 4859993 := bstep (se 2 (by rfl) ⟨1822497, by rfl⟩ : syracuseStep 4859993 = 3644995) B3644995
theorem B3239995 : Blo 2275435 3239995 := bstep (se 1 (by rfl) ⟨2429996, by rfl⟩ : syracuseStep 3239995 = 4859993) B4859993
theorem B4319993 : Blo 2275435 4319993 := bstep (se 2 (by rfl) ⟨1619997, by rfl⟩ : syracuseStep 4319993 = 3239995) B3239995
theorem B11519981 : Blo 2275435 11519981 := bstep (se 3 (by rfl) ⟨2159996, by rfl⟩ : syracuseStep 11519981 = 4319993) B4319993
theorem B7679987 : Blo 2275435 7679987 := bstep (se 1 (by rfl) ⟨5759990, by rfl⟩ : syracuseStep 7679987 = 11519981) B11519981
theorem B5119991 : Blo 2275435 5119991 := bstep (se 1 (by rfl) ⟨3839993, by rfl⟩ : syracuseStep 5119991 = 7679987) B7679987
theorem B3413327 : Blo 2275435 3413327 := bstep (se 1 (by rfl) ⟨2559995, by rfl⟩ : syracuseStep 3413327 = 5119991) B5119991
theorem B2275551 : Blo 2275435 2275551 := bstep (se 1 (by rfl) ⟨1706663, by rfl⟩ : syracuseStep 2275551 = 3413327) B3413327
theorem B3413333 : Blo 2275435 3413333 := bbase (se 14 (by rfl) ⟨312, by rfl⟩ : syracuseStep 3413333 = 625) (by norm_num)
theorem B2275555 : Blo 2275435 2275555 := bstep (se 1 (by rfl) ⟨1706666, by rfl⟩ : syracuseStep 2275555 = 3413333) B3413333
theorem B2430005 : Blo 2275435 2430005 := bbase (se 5 (by rfl) ⟨113906, by rfl⟩ : syracuseStep 2430005 = 227813) (by norm_num)
theorem B6480013 : Blo 2275435 6480013 := bstep (se 3 (by rfl) ⟨1215002, by rfl⟩ : syracuseStep 6480013 = 2430005) B2430005
theorem B8640017 : Blo 2275435 8640017 := bstep (se 2 (by rfl) ⟨3240006, by rfl⟩ : syracuseStep 8640017 = 6480013) B6480013
theorem B5760011 : Blo 2275435 5760011 := bstep (se 1 (by rfl) ⟨4320008, by rfl⟩ : syracuseStep 5760011 = 8640017) B8640017
theorem B3840007 : Blo 2275435 3840007 := bstep (se 1 (by rfl) ⟨2880005, by rfl⟩ : syracuseStep 3840007 = 5760011) B5760011
theorem B5120009 : Blo 2275435 5120009 := bstep (se 2 (by rfl) ⟨1920003, by rfl⟩ : syracuseStep 5120009 = 3840007) B3840007
theorem B3413339 : Blo 2275435 3413339 := bstep (se 1 (by rfl) ⟨2560004, by rfl⟩ : syracuseStep 3413339 = 5120009) B5120009
theorem B2275559 : Blo 2275435 2275559 := bstep (se 1 (by rfl) ⟨1706669, by rfl⟩ : syracuseStep 2275559 = 3413339) B3413339
theorem B2560009 : Blo 2275435 2560009 := bbase (se 2 (by rfl) ⟨960003, by rfl⟩ : syracuseStep 2560009 = 1920007) (by norm_num)
theorem B3413345 : Blo 2275435 3413345 := bstep (se 2 (by rfl) ⟨1280004, by rfl⟩ : syracuseStep 3413345 = 2560009) B2560009
theorem B2275563 : Blo 2275435 2275563 := bstep (se 1 (by rfl) ⟨1706672, by rfl⟩ : syracuseStep 2275563 = 3413345) B3413345
theorem B15782069 : Blo 2275435 15782069 := bbase (se 5 (by rfl) ⟨739784, by rfl⟩ : syracuseStep 15782069 = 1479569) (by norm_num)
theorem B42085517 : Blo 2275435 42085517 := bstep (se 3 (by rfl) ⟨7891034, by rfl⟩ : syracuseStep 42085517 = 15782069) B15782069
theorem B448912181 : Blo 2275435 448912181 := bstep (se 5 (by rfl) ⟨21042758, by rfl⟩ : syracuseStep 448912181 = 42085517) B42085517
theorem B299274787 : Blo 2275435 299274787 := bstep (se 1 (by rfl) ⟨224456090, by rfl⟩ : syracuseStep 299274787 = 448912181) B448912181
theorem B399033049 : Blo 2275435 399033049 := bstep (se 2 (by rfl) ⟨149637393, by rfl⟩ : syracuseStep 399033049 = 299274787) B299274787
theorem B532044065 : Blo 2275435 532044065 := bstep (se 2 (by rfl) ⟨199516524, by rfl⟩ : syracuseStep 532044065 = 399033049) B399033049
theorem B354696043 : Blo 2275435 354696043 := bstep (se 1 (by rfl) ⟨266022032, by rfl⟩ : syracuseStep 354696043 = 532044065) B532044065
theorem B472928057 : Blo 2275435 472928057 := bstep (se 2 (by rfl) ⟨177348021, by rfl⟩ : syracuseStep 472928057 = 354696043) B354696043
theorem B315285371 : Blo 2275435 315285371 := bstep (se 1 (by rfl) ⟨236464028, by rfl⟩ : syracuseStep 315285371 = 472928057) B472928057
theorem B210190247 : Blo 2275435 210190247 := bstep (se 1 (by rfl) ⟨157642685, by rfl⟩ : syracuseStep 210190247 = 315285371) B315285371
theorem B140126831 : Blo 2275435 140126831 := bstep (se 1 (by rfl) ⟨105095123, by rfl⟩ : syracuseStep 140126831 = 210190247) B210190247
theorem B93417887 : Blo 2275435 93417887 := bstep (se 1 (by rfl) ⟨70063415, by rfl⟩ : syracuseStep 93417887 = 140126831) B140126831
theorem B62278591 : Blo 2275435 62278591 := bstep (se 1 (by rfl) ⟨46708943, by rfl⟩ : syracuseStep 62278591 = 93417887) B93417887
theorem B83038121 : Blo 2275435 83038121 := bstep (se 2 (by rfl) ⟨31139295, by rfl⟩ : syracuseStep 83038121 = 62278591) B62278591
theorem B55358747 : Blo 2275435 55358747 := bstep (se 1 (by rfl) ⟨41519060, by rfl⟩ : syracuseStep 55358747 = 83038121) B83038121
theorem B36905831 : Blo 2275435 36905831 := bstep (se 1 (by rfl) ⟨27679373, by rfl⟩ : syracuseStep 36905831 = 55358747) B55358747
theorem B24603887 : Blo 2275435 24603887 := bstep (se 1 (by rfl) ⟨18452915, by rfl⟩ : syracuseStep 24603887 = 36905831) B36905831
theorem B16402591 : Blo 2275435 16402591 := bstep (se 1 (by rfl) ⟨12301943, by rfl⟩ : syracuseStep 16402591 = 24603887) B24603887
theorem B21870121 : Blo 2275435 21870121 := bstep (se 2 (by rfl) ⟨8201295, by rfl⟩ : syracuseStep 21870121 = 16402591) B16402591
theorem B29160161 : Blo 2275435 29160161 := bstep (se 2 (by rfl) ⟨10935060, by rfl⟩ : syracuseStep 29160161 = 21870121) B21870121
theorem B19440107 : Blo 2275435 19440107 := bstep (se 1 (by rfl) ⟨14580080, by rfl⟩ : syracuseStep 19440107 = 29160161) B29160161
theorem B12960071 : Blo 2275435 12960071 := bstep (se 1 (by rfl) ⟨9720053, by rfl⟩ : syracuseStep 12960071 = 19440107) B19440107
theorem B8640047 : Blo 2275435 8640047 := bstep (se 1 (by rfl) ⟨6480035, by rfl⟩ : syracuseStep 8640047 = 12960071) B12960071
theorem B5760031 : Blo 2275435 5760031 := bstep (se 1 (by rfl) ⟨4320023, by rfl⟩ : syracuseStep 5760031 = 8640047) B8640047
theorem B7680041 : Blo 2275435 7680041 := bstep (se 2 (by rfl) ⟨2880015, by rfl⟩ : syracuseStep 7680041 = 5760031) B5760031
theorem B5120027 : Blo 2275435 5120027 := bstep (se 1 (by rfl) ⟨3840020, by rfl⟩ : syracuseStep 5120027 = 7680041) B7680041
theorem B3413351 : Blo 2275435 3413351 := bstep (se 1 (by rfl) ⟨2560013, by rfl⟩ : syracuseStep 3413351 = 5120027) B5120027
theorem B2275567 : Blo 2275435 2275567 := bstep (se 1 (by rfl) ⟨1706675, by rfl⟩ : syracuseStep 2275567 = 3413351) B3413351
theorem B3413357 : Blo 2275435 3413357 := bbase (se 3 (by rfl) ⟨640004, by rfl⟩ : syracuseStep 3413357 = 1280009) (by norm_num)
theorem B2275571 : Blo 2275435 2275571 := bstep (se 1 (by rfl) ⟨1706678, by rfl⟩ : syracuseStep 2275571 = 3413357) B3413357
theorem B5120045 : Blo 2275435 5120045 := bbase (se 3 (by rfl) ⟨960008, by rfl⟩ : syracuseStep 5120045 = 1920017) (by norm_num)
theorem B3413363 : Blo 2275435 3413363 := bstep (se 1 (by rfl) ⟨2560022, by rfl⟩ : syracuseStep 3413363 = 5120045) B5120045
theorem B2275575 : Blo 2275435 2275575 := bstep (se 1 (by rfl) ⟨1706681, by rfl⟩ : syracuseStep 2275575 = 3413363) B3413363
theorem B7784869 : Blo 2275435 7784869 := bbase (se 4 (by rfl) ⟨729831, by rfl⟩ : syracuseStep 7784869 = 1459663) (by norm_num)
theorem B10379825 : Blo 2275435 10379825 := bstep (se 2 (by rfl) ⟨3892434, by rfl⟩ : syracuseStep 10379825 = 7784869) B7784869
theorem B6919883 : Blo 2275435 6919883 := bstep (se 1 (by rfl) ⟨5189912, by rfl⟩ : syracuseStep 6919883 = 10379825) B10379825
theorem B4613255 : Blo 2275435 4613255 := bstep (se 1 (by rfl) ⟨3459941, by rfl⟩ : syracuseStep 4613255 = 6919883) B6919883
theorem B3075503 : Blo 2275435 3075503 := bstep (se 1 (by rfl) ⟨2306627, by rfl⟩ : syracuseStep 3075503 = 4613255) B4613255
theorem B8201341 : Blo 2275435 8201341 := bstep (se 3 (by rfl) ⟨1537751, by rfl⟩ : syracuseStep 8201341 = 3075503) B3075503
theorem B10935121 : Blo 2275435 10935121 := bstep (se 2 (by rfl) ⟨4100670, by rfl⟩ : syracuseStep 10935121 = 8201341) B8201341
theorem B14580161 : Blo 2275435 14580161 := bstep (se 2 (by rfl) ⟨5467560, by rfl⟩ : syracuseStep 14580161 = 10935121) B10935121
theorem B9720107 : Blo 2275435 9720107 := bstep (se 1 (by rfl) ⟨7290080, by rfl⟩ : syracuseStep 9720107 = 14580161) B14580161
theorem B6480071 : Blo 2275435 6480071 := bstep (se 1 (by rfl) ⟨4860053, by rfl⟩ : syracuseStep 6480071 = 9720107) B9720107
theorem B4320047 : Blo 2275435 4320047 := bstep (se 1 (by rfl) ⟨3240035, by rfl⟩ : syracuseStep 4320047 = 6480071) B6480071
theorem B2880031 : Blo 2275435 2880031 := bstep (se 1 (by rfl) ⟨2160023, by rfl⟩ : syracuseStep 2880031 = 4320047) B4320047
theorem B3840041 : Blo 2275435 3840041 := bstep (se 2 (by rfl) ⟨1440015, by rfl⟩ : syracuseStep 3840041 = 2880031) B2880031
theorem B2560027 : Blo 2275435 2560027 := bstep (se 1 (by rfl) ⟨1920020, by rfl⟩ : syracuseStep 2560027 = 3840041) B3840041
theorem B3413369 : Blo 2275435 3413369 := bstep (se 2 (by rfl) ⟨1280013, by rfl⟩ : syracuseStep 3413369 = 2560027) B2560027
theorem B2275579 : Blo 2275435 2275579 := bstep (se 1 (by rfl) ⟨1706684, by rfl⟩ : syracuseStep 2275579 = 3413369) B3413369
theorem B3117469 : Blo 2275435 3117469 := bbase (se 3 (by rfl) ⟨584525, by rfl⟩ : syracuseStep 3117469 = 1169051) (by norm_num)
theorem B4156625 : Blo 2275435 4156625 := bstep (se 2 (by rfl) ⟨1558734, by rfl⟩ : syracuseStep 4156625 = 3117469) B3117469
theorem B2771083 : Blo 2275435 2771083 := bstep (se 1 (by rfl) ⟨2078312, by rfl⟩ : syracuseStep 2771083 = 4156625) B4156625
theorem B3694777 : Blo 2275435 3694777 := bstep (se 2 (by rfl) ⟨1385541, by rfl⟩ : syracuseStep 3694777 = 2771083) B2771083
theorem B78821909 : Blo 2275435 78821909 := bstep (se 6 (by rfl) ⟨1847388, by rfl⟩ : syracuseStep 78821909 = 3694777) B3694777
theorem B52547939 : Blo 2275435 52547939 := bstep (se 1 (by rfl) ⟨39410954, by rfl⟩ : syracuseStep 52547939 = 78821909) B78821909
theorem B35031959 : Blo 2275435 35031959 := bstep (se 1 (by rfl) ⟨26273969, by rfl⟩ : syracuseStep 35031959 = 52547939) B52547939
theorem B23354639 : Blo 2275435 23354639 := bstep (se 1 (by rfl) ⟨17515979, by rfl⟩ : syracuseStep 23354639 = 35031959) B35031959
theorem B15569759 : Blo 2275435 15569759 := bstep (se 1 (by rfl) ⟨11677319, by rfl⟩ : syracuseStep 15569759 = 23354639) B23354639
theorem B10379839 : Blo 2275435 10379839 := bstep (se 1 (by rfl) ⟨7784879, by rfl⟩ : syracuseStep 10379839 = 15569759) B15569759
theorem B13839785 : Blo 2275435 13839785 := bstep (se 2 (by rfl) ⟨5189919, by rfl⟩ : syracuseStep 13839785 = 10379839) B10379839
theorem B9226523 : Blo 2275435 9226523 := bstep (se 1 (by rfl) ⟨6919892, by rfl⟩ : syracuseStep 9226523 = 13839785) B13839785
theorem B6151015 : Blo 2275435 6151015 := bstep (se 1 (by rfl) ⟨4613261, by rfl⟩ : syracuseStep 6151015 = 9226523) B9226523
theorem B8201353 : Blo 2275435 8201353 := bstep (se 2 (by rfl) ⟨3075507, by rfl⟩ : syracuseStep 8201353 = 6151015) B6151015
theorem B10935137 : Blo 2275435 10935137 := bstep (se 2 (by rfl) ⟨4100676, by rfl⟩ : syracuseStep 10935137 = 8201353) B8201353
theorem B7290091 : Blo 2275435 7290091 := bstep (se 1 (by rfl) ⟨5467568, by rfl⟩ : syracuseStep 7290091 = 10935137) B10935137
theorem B38880485 : Blo 2275435 38880485 := bstep (se 4 (by rfl) ⟨3645045, by rfl⟩ : syracuseStep 38880485 = 7290091) B7290091
theorem B25920323 : Blo 2275435 25920323 := bstep (se 1 (by rfl) ⟨19440242, by rfl⟩ : syracuseStep 25920323 = 38880485) B38880485
theorem B17280215 : Blo 2275435 17280215 := bstep (se 1 (by rfl) ⟨12960161, by rfl⟩ : syracuseStep 17280215 = 25920323) B25920323
theorem B11520143 : Blo 2275435 11520143 := bstep (se 1 (by rfl) ⟨8640107, by rfl⟩ : syracuseStep 11520143 = 17280215) B17280215
theorem B7680095 : Blo 2275435 7680095 := bstep (se 1 (by rfl) ⟨5760071, by rfl⟩ : syracuseStep 7680095 = 11520143) B11520143
theorem B5120063 : Blo 2275435 5120063 := bstep (se 1 (by rfl) ⟨3840047, by rfl⟩ : syracuseStep 5120063 = 7680095) B7680095
theorem B3413375 : Blo 2275435 3413375 := bstep (se 1 (by rfl) ⟨2560031, by rfl⟩ : syracuseStep 3413375 = 5120063) B5120063
theorem B2275583 : Blo 2275435 2275583 := bstep (se 1 (by rfl) ⟨1706687, by rfl⟩ : syracuseStep 2275583 = 3413375) B3413375
theorem B3413381 : Blo 2275435 3413381 := bbase (se 4 (by rfl) ⟨320004, by rfl⟩ : syracuseStep 3413381 = 640009) (by norm_num)
theorem B2275587 : Blo 2275435 2275587 := bstep (se 1 (by rfl) ⟨1706690, by rfl⟩ : syracuseStep 2275587 = 3413381) B3413381
theorem B3840061 : Blo 2275435 3840061 := bbase (se 3 (by rfl) ⟨720011, by rfl⟩ : syracuseStep 3840061 = 1440023) (by norm_num)
theorem B5120081 : Blo 2275435 5120081 := bstep (se 2 (by rfl) ⟨1920030, by rfl⟩ : syracuseStep 5120081 = 3840061) B3840061
theorem B3413387 : Blo 2275435 3413387 := bstep (se 1 (by rfl) ⟨2560040, by rfl⟩ : syracuseStep 3413387 = 5120081) B5120081
theorem B2275591 : Blo 2275435 2275591 := bstep (se 1 (by rfl) ⟨1706693, by rfl⟩ : syracuseStep 2275591 = 3413387) B3413387
theorem B2560045 : Blo 2275435 2560045 := bbase (se 3 (by rfl) ⟨480008, by rfl⟩ : syracuseStep 2560045 = 960017) (by norm_num)
theorem B3413393 : Blo 2275435 3413393 := bstep (se 2 (by rfl) ⟨1280022, by rfl⟩ : syracuseStep 3413393 = 2560045) B2560045
theorem B2275595 : Blo 2275435 2275595 := bstep (se 1 (by rfl) ⟨1706696, by rfl⟩ : syracuseStep 2275595 = 3413393) B3413393
theorem B7680149 : Blo 2275435 7680149 := bbase (se 6 (by rfl) ⟨180003, by rfl⟩ : syracuseStep 7680149 = 360007) (by norm_num)
theorem B5120099 : Blo 2275435 5120099 := bstep (se 1 (by rfl) ⟨3840074, by rfl⟩ : syracuseStep 5120099 = 7680149) B7680149
theorem B3413399 : Blo 2275435 3413399 := bstep (se 1 (by rfl) ⟨2560049, by rfl⟩ : syracuseStep 3413399 = 5120099) B5120099
theorem B2275599 : Blo 2275435 2275599 := bstep (se 1 (by rfl) ⟨1706699, by rfl⟩ : syracuseStep 2275599 = 3413399) B3413399
theorem B3413405 : Blo 2275435 3413405 := bbase (se 3 (by rfl) ⟨640013, by rfl⟩ : syracuseStep 3413405 = 1280027) (by norm_num)
theorem B2275603 : Blo 2275435 2275603 := bstep (se 1 (by rfl) ⟨1706702, by rfl⟩ : syracuseStep 2275603 = 3413405) B3413405
theorem B5120117 : Blo 2275435 5120117 := bbase (se 5 (by rfl) ⟨240005, by rfl⟩ : syracuseStep 5120117 = 480011) (by norm_num)
theorem B3413411 : Blo 2275435 3413411 := bstep (se 1 (by rfl) ⟨2560058, by rfl⟩ : syracuseStep 3413411 = 5120117) B5120117
theorem B2275607 : Blo 2275435 2275607 := bstep (se 1 (by rfl) ⟨1706705, by rfl⟩ : syracuseStep 2275607 = 3413411) B3413411
theorem B5467637 : Blo 2275435 5467637 := bbase (se 5 (by rfl) ⟨256295, by rfl⟩ : syracuseStep 5467637 = 512591) (by norm_num)
theorem B3645091 : Blo 2275435 3645091 := bstep (se 1 (by rfl) ⟨2733818, by rfl⟩ : syracuseStep 3645091 = 5467637) B5467637
theorem B19440485 : Blo 2275435 19440485 := bstep (se 4 (by rfl) ⟨1822545, by rfl⟩ : syracuseStep 19440485 = 3645091) B3645091
theorem B12960323 : Blo 2275435 12960323 := bstep (se 1 (by rfl) ⟨9720242, by rfl⟩ : syracuseStep 12960323 = 19440485) B19440485
theorem B8640215 : Blo 2275435 8640215 := bstep (se 1 (by rfl) ⟨6480161, by rfl⟩ : syracuseStep 8640215 = 12960323) B12960323
theorem B5760143 : Blo 2275435 5760143 := bstep (se 1 (by rfl) ⟨4320107, by rfl⟩ : syracuseStep 5760143 = 8640215) B8640215
theorem B3840095 : Blo 2275435 3840095 := bstep (se 1 (by rfl) ⟨2880071, by rfl⟩ : syracuseStep 3840095 = 5760143) B5760143
theorem B2560063 : Blo 2275435 2560063 := bstep (se 1 (by rfl) ⟨1920047, by rfl⟩ : syracuseStep 2560063 = 3840095) B3840095
theorem B3413417 : Blo 2275435 3413417 := bstep (se 2 (by rfl) ⟨1280031, by rfl⟩ : syracuseStep 3413417 = 2560063) B2560063
theorem B2275611 : Blo 2275435 2275611 := bstep (se 1 (by rfl) ⟨1706708, by rfl⟩ : syracuseStep 2275611 = 3413417) B3413417
theorem B8640229 : Blo 2275435 8640229 := bbase (se 4 (by rfl) ⟨810021, by rfl⟩ : syracuseStep 8640229 = 1620043) (by norm_num)
theorem B11520305 : Blo 2275435 11520305 := bstep (se 2 (by rfl) ⟨4320114, by rfl⟩ : syracuseStep 11520305 = 8640229) B8640229
theorem B7680203 : Blo 2275435 7680203 := bstep (se 1 (by rfl) ⟨5760152, by rfl⟩ : syracuseStep 7680203 = 11520305) B11520305
theorem B5120135 : Blo 2275435 5120135 := bstep (se 1 (by rfl) ⟨3840101, by rfl⟩ : syracuseStep 5120135 = 7680203) B7680203
theorem B3413423 : Blo 2275435 3413423 := bstep (se 1 (by rfl) ⟨2560067, by rfl⟩ : syracuseStep 3413423 = 5120135) B5120135
theorem B2275615 : Blo 2275435 2275615 := bstep (se 1 (by rfl) ⟨1706711, by rfl⟩ : syracuseStep 2275615 = 3413423) B3413423
theorem B3413429 : Blo 2275435 3413429 := bbase (se 5 (by rfl) ⟨160004, by rfl⟩ : syracuseStep 3413429 = 320009) (by norm_num)
theorem B2275619 : Blo 2275435 2275619 := bstep (se 1 (by rfl) ⟨1706714, by rfl⟩ : syracuseStep 2275619 = 3413429) B3413429
theorem B5760173 : Blo 2275435 5760173 := bbase (se 3 (by rfl) ⟨1080032, by rfl⟩ : syracuseStep 5760173 = 2160065) (by norm_num)
theorem B3840115 : Blo 2275435 3840115 := bstep (se 1 (by rfl) ⟨2880086, by rfl⟩ : syracuseStep 3840115 = 5760173) B5760173
theorem B5120153 : Blo 2275435 5120153 := bstep (se 2 (by rfl) ⟨1920057, by rfl⟩ : syracuseStep 5120153 = 3840115) B3840115
theorem B3413435 : Blo 2275435 3413435 := bstep (se 1 (by rfl) ⟨2560076, by rfl⟩ : syracuseStep 3413435 = 5120153) B5120153
theorem B2275623 : Blo 2275435 2275623 := bstep (se 1 (by rfl) ⟨1706717, by rfl⟩ : syracuseStep 2275623 = 3413435) B3413435
theorem B2560081 : Blo 2275435 2560081 := bbase (se 2 (by rfl) ⟨960030, by rfl⟩ : syracuseStep 2560081 = 1920061) (by norm_num)
theorem B3413441 : Blo 2275435 3413441 := bstep (se 2 (by rfl) ⟨1280040, by rfl⟩ : syracuseStep 3413441 = 2560081) B2560081
theorem B2275627 : Blo 2275435 2275627 := bstep (se 1 (by rfl) ⟨1706720, by rfl⟩ : syracuseStep 2275627 = 3413441) B3413441
theorem B3240109 : Blo 2275435 3240109 := bbase (se 3 (by rfl) ⟨607520, by rfl⟩ : syracuseStep 3240109 = 1215041) (by norm_num)
theorem B4320145 : Blo 2275435 4320145 := bstep (se 2 (by rfl) ⟨1620054, by rfl⟩ : syracuseStep 4320145 = 3240109) B3240109
theorem B5760193 : Blo 2275435 5760193 := bstep (se 2 (by rfl) ⟨2160072, by rfl⟩ : syracuseStep 5760193 = 4320145) B4320145
theorem B7680257 : Blo 2275435 7680257 := bstep (se 2 (by rfl) ⟨2880096, by rfl⟩ : syracuseStep 7680257 = 5760193) B5760193
theorem B5120171 : Blo 2275435 5120171 := bstep (se 1 (by rfl) ⟨3840128, by rfl⟩ : syracuseStep 5120171 = 7680257) B7680257
theorem B3413447 : Blo 2275435 3413447 := bstep (se 1 (by rfl) ⟨2560085, by rfl⟩ : syracuseStep 3413447 = 5120171) B5120171
theorem B2275631 : Blo 2275435 2275631 := bstep (se 1 (by rfl) ⟨1706723, by rfl⟩ : syracuseStep 2275631 = 3413447) B3413447
theorem B3413453 : Blo 2275435 3413453 := bbase (se 3 (by rfl) ⟨640022, by rfl⟩ : syracuseStep 3413453 = 1280045) (by norm_num)
theorem B2275635 : Blo 2275435 2275635 := bstep (se 1 (by rfl) ⟨1706726, by rfl⟩ : syracuseStep 2275635 = 3413453) B3413453
theorem B5120189 : Blo 2275435 5120189 := bbase (se 3 (by rfl) ⟨960035, by rfl⟩ : syracuseStep 5120189 = 1920071) (by norm_num)
theorem B3413459 : Blo 2275435 3413459 := bstep (se 1 (by rfl) ⟨2560094, by rfl⟩ : syracuseStep 3413459 = 5120189) B5120189
theorem B2275639 : Blo 2275435 2275639 := bstep (se 1 (by rfl) ⟨1706729, by rfl⟩ : syracuseStep 2275639 = 3413459) B3413459
theorem B3840149 : Blo 2275435 3840149 := bbase (se 6 (by rfl) ⟨90003, by rfl⟩ : syracuseStep 3840149 = 180007) (by norm_num)
theorem B2560099 : Blo 2275435 2560099 := bstep (se 1 (by rfl) ⟨1920074, by rfl⟩ : syracuseStep 2560099 = 3840149) B3840149
theorem B3413465 : Blo 2275435 3413465 := bstep (se 2 (by rfl) ⟨1280049, by rfl⟩ : syracuseStep 3413465 = 2560099) B2560099
theorem B2275643 : Blo 2275435 2275643 := bstep (se 1 (by rfl) ⟨1706732, by rfl⟩ : syracuseStep 2275643 = 3413465) B3413465
theorem B10935445 : Blo 2275435 10935445 := bbase (se 6 (by rfl) ⟨256299, by rfl⟩ : syracuseStep 10935445 = 512599) (by norm_num)
theorem B14580593 : Blo 2275435 14580593 := bstep (se 2 (by rfl) ⟨5467722, by rfl⟩ : syracuseStep 14580593 = 10935445) B10935445
theorem B9720395 : Blo 2275435 9720395 := bstep (se 1 (by rfl) ⟨7290296, by rfl⟩ : syracuseStep 9720395 = 14580593) B14580593
theorem B6480263 : Blo 2275435 6480263 := bstep (se 1 (by rfl) ⟨4860197, by rfl⟩ : syracuseStep 6480263 = 9720395) B9720395
theorem B17280701 : Blo 2275435 17280701 := bstep (se 3 (by rfl) ⟨3240131, by rfl⟩ : syracuseStep 17280701 = 6480263) B6480263
theorem B11520467 : Blo 2275435 11520467 := bstep (se 1 (by rfl) ⟨8640350, by rfl⟩ : syracuseStep 11520467 = 17280701) B17280701
theorem B7680311 : Blo 2275435 7680311 := bstep (se 1 (by rfl) ⟨5760233, by rfl⟩ : syracuseStep 7680311 = 11520467) B11520467
theorem B5120207 : Blo 2275435 5120207 := bstep (se 1 (by rfl) ⟨3840155, by rfl⟩ : syracuseStep 5120207 = 7680311) B7680311
theorem B3413471 : Blo 2275435 3413471 := bstep (se 1 (by rfl) ⟨2560103, by rfl⟩ : syracuseStep 3413471 = 5120207) B5120207
theorem B2275647 : Blo 2275435 2275647 := bstep (se 1 (by rfl) ⟨1706735, by rfl⟩ : syracuseStep 2275647 = 3413471) B3413471
theorem B3413477 : Blo 2275435 3413477 := bbase (se 4 (by rfl) ⟨320013, by rfl⟩ : syracuseStep 3413477 = 640027) (by norm_num)
theorem B2275651 : Blo 2275435 2275651 := bstep (se 1 (by rfl) ⟨1706738, by rfl⟩ : syracuseStep 2275651 = 3413477) B3413477
theorem B5838845 : Blo 2275435 5838845 := bbase (se 3 (by rfl) ⟨1094783, by rfl⟩ : syracuseStep 5838845 = 2189567) (by norm_num)
theorem B15570253 : Blo 2275435 15570253 := bstep (se 3 (by rfl) ⟨2919422, by rfl⟩ : syracuseStep 15570253 = 5838845) B5838845
theorem B20760337 : Blo 2275435 20760337 := bstep (se 2 (by rfl) ⟨7785126, by rfl⟩ : syracuseStep 20760337 = 15570253) B15570253
theorem B27680449 : Blo 2275435 27680449 := bstep (se 2 (by rfl) ⟨10380168, by rfl⟩ : syracuseStep 27680449 = 20760337) B20760337
theorem B36907265 : Blo 2275435 36907265 := bstep (se 2 (by rfl) ⟨13840224, by rfl⟩ : syracuseStep 36907265 = 27680449) B27680449
theorem B24604843 : Blo 2275435 24604843 := bstep (se 1 (by rfl) ⟨18453632, by rfl⟩ : syracuseStep 24604843 = 36907265) B36907265
theorem B32806457 : Blo 2275435 32806457 := bstep (se 2 (by rfl) ⟨12302421, by rfl⟩ : syracuseStep 32806457 = 24604843) B24604843
theorem B21870971 : Blo 2275435 21870971 := bstep (se 1 (by rfl) ⟨16403228, by rfl⟩ : syracuseStep 21870971 = 32806457) B32806457
theorem B14580647 : Blo 2275435 14580647 := bstep (se 1 (by rfl) ⟨10935485, by rfl⟩ : syracuseStep 14580647 = 21870971) B21870971
theorem B9720431 : Blo 2275435 9720431 := bstep (se 1 (by rfl) ⟨7290323, by rfl⟩ : syracuseStep 9720431 = 14580647) B14580647
theorem B6480287 : Blo 2275435 6480287 := bstep (se 1 (by rfl) ⟨4860215, by rfl⟩ : syracuseStep 6480287 = 9720431) B9720431
theorem B4320191 : Blo 2275435 4320191 := bstep (se 1 (by rfl) ⟨3240143, by rfl⟩ : syracuseStep 4320191 = 6480287) B6480287
theorem B2880127 : Blo 2275435 2880127 := bstep (se 1 (by rfl) ⟨2160095, by rfl⟩ : syracuseStep 2880127 = 4320191) B4320191
theorem B3840169 : Blo 2275435 3840169 := bstep (se 2 (by rfl) ⟨1440063, by rfl⟩ : syracuseStep 3840169 = 2880127) B2880127
theorem B5120225 : Blo 2275435 5120225 := bstep (se 2 (by rfl) ⟨1920084, by rfl⟩ : syracuseStep 5120225 = 3840169) B3840169
theorem B3413483 : Blo 2275435 3413483 := bstep (se 1 (by rfl) ⟨2560112, by rfl⟩ : syracuseStep 3413483 = 5120225) B5120225
theorem B2275655 : Blo 2275435 2275655 := bstep (se 1 (by rfl) ⟨1706741, by rfl⟩ : syracuseStep 2275655 = 3413483) B3413483
theorem B2560117 : Blo 2275435 2560117 := bbase (se 5 (by rfl) ⟨120005, by rfl⟩ : syracuseStep 2560117 = 240011) (by norm_num)
theorem B3413489 : Blo 2275435 3413489 := bstep (se 2 (by rfl) ⟨1280058, by rfl⟩ : syracuseStep 3413489 = 2560117) B2560117
theorem B2275659 : Blo 2275435 2275659 := bstep (se 1 (by rfl) ⟨1706744, by rfl⟩ : syracuseStep 2275659 = 3413489) B3413489
theorem B2880137 : Blo 2275435 2880137 := bbase (se 2 (by rfl) ⟨1080051, by rfl⟩ : syracuseStep 2880137 = 2160103) (by norm_num)
theorem B7680365 : Blo 2275435 7680365 := bstep (se 3 (by rfl) ⟨1440068, by rfl⟩ : syracuseStep 7680365 = 2880137) B2880137
theorem B5120243 : Blo 2275435 5120243 := bstep (se 1 (by rfl) ⟨3840182, by rfl⟩ : syracuseStep 5120243 = 7680365) B7680365
theorem B3413495 : Blo 2275435 3413495 := bstep (se 1 (by rfl) ⟨2560121, by rfl⟩ : syracuseStep 3413495 = 5120243) B5120243
theorem B2275663 : Blo 2275435 2275663 := bstep (se 1 (by rfl) ⟨1706747, by rfl⟩ : syracuseStep 2275663 = 3413495) B3413495
theorem B3413501 : Blo 2275435 3413501 := bbase (se 3 (by rfl) ⟨640031, by rfl⟩ : syracuseStep 3413501 = 1280063) (by norm_num)
theorem B2275667 : Blo 2275435 2275667 := bstep (se 1 (by rfl) ⟨1706750, by rfl⟩ : syracuseStep 2275667 = 3413501) B3413501
theorem B5120261 : Blo 2275435 5120261 := bbase (se 4 (by rfl) ⟨480024, by rfl⟩ : syracuseStep 5120261 = 960049) (by norm_num)
theorem B3413507 : Blo 2275435 3413507 := bstep (se 1 (by rfl) ⟨2560130, by rfl⟩ : syracuseStep 3413507 = 5120261) B5120261
theorem B2275671 : Blo 2275435 2275671 := bstep (se 1 (by rfl) ⟨1706753, by rfl⟩ : syracuseStep 2275671 = 3413507) B3413507
theorem B4320229 : Blo 2275435 4320229 := bbase (se 4 (by rfl) ⟨405021, by rfl⟩ : syracuseStep 4320229 = 810043) (by norm_num)
theorem B5760305 : Blo 2275435 5760305 := bstep (se 2 (by rfl) ⟨2160114, by rfl⟩ : syracuseStep 5760305 = 4320229) B4320229
theorem B3840203 : Blo 2275435 3840203 := bstep (se 1 (by rfl) ⟨2880152, by rfl⟩ : syracuseStep 3840203 = 5760305) B5760305
theorem B2560135 : Blo 2275435 2560135 := bstep (se 1 (by rfl) ⟨1920101, by rfl⟩ : syracuseStep 2560135 = 3840203) B3840203
theorem B3413513 : Blo 2275435 3413513 := bstep (se 2 (by rfl) ⟨1280067, by rfl⟩ : syracuseStep 3413513 = 2560135) B2560135
theorem B2275675 : Blo 2275435 2275675 := bstep (se 1 (by rfl) ⟨1706756, by rfl⟩ : syracuseStep 2275675 = 3413513) B3413513
theorem B11520629 : Blo 2275435 11520629 := bbase (se 5 (by rfl) ⟨540029, by rfl⟩ : syracuseStep 11520629 = 1080059) (by norm_num)
theorem B7680419 : Blo 2275435 7680419 := bstep (se 1 (by rfl) ⟨5760314, by rfl⟩ : syracuseStep 7680419 = 11520629) B11520629
theorem B5120279 : Blo 2275435 5120279 := bstep (se 1 (by rfl) ⟨3840209, by rfl⟩ : syracuseStep 5120279 = 7680419) B7680419
theorem B3413519 : Blo 2275435 3413519 := bstep (se 1 (by rfl) ⟨2560139, by rfl⟩ : syracuseStep 3413519 = 5120279) B5120279
theorem B2275679 : Blo 2275435 2275679 := bstep (se 1 (by rfl) ⟨1706759, by rfl⟩ : syracuseStep 2275679 = 3413519) B3413519
theorem B3413525 : Blo 2275435 3413525 := bbase (se 6 (by rfl) ⟨80004, by rfl⟩ : syracuseStep 3413525 = 160009) (by norm_num)
theorem B2275683 : Blo 2275435 2275683 := bstep (se 1 (by rfl) ⟨1706762, by rfl⟩ : syracuseStep 2275683 = 3413525) B3413525
theorem B4379197 : Blo 2275435 4379197 := bbase (se 3 (by rfl) ⟨821099, by rfl⟩ : syracuseStep 4379197 = 1642199) (by norm_num)
theorem B5838929 : Blo 2275435 5838929 := bstep (se 2 (by rfl) ⟨2189598, by rfl⟩ : syracuseStep 5838929 = 4379197) B4379197
theorem B3892619 : Blo 2275435 3892619 := bstep (se 1 (by rfl) ⟨2919464, by rfl⟩ : syracuseStep 3892619 = 5838929) B5838929
theorem B2595079 : Blo 2275435 2595079 := bstep (se 1 (by rfl) ⟨1946309, by rfl⟩ : syracuseStep 2595079 = 3892619) B3892619
theorem B3460105 : Blo 2275435 3460105 := bstep (se 2 (by rfl) ⟨1297539, by rfl⟩ : syracuseStep 3460105 = 2595079) B2595079
theorem B4613473 : Blo 2275435 4613473 := bstep (se 2 (by rfl) ⟨1730052, by rfl⟩ : syracuseStep 4613473 = 3460105) B3460105
theorem B6151297 : Blo 2275435 6151297 := bstep (se 2 (by rfl) ⟨2306736, by rfl⟩ : syracuseStep 6151297 = 4613473) B4613473
theorem B8201729 : Blo 2275435 8201729 := bstep (se 2 (by rfl) ⟨3075648, by rfl⟩ : syracuseStep 8201729 = 6151297) B6151297
theorem B5467819 : Blo 2275435 5467819 := bstep (se 1 (by rfl) ⟨4100864, by rfl⟩ : syracuseStep 5467819 = 8201729) B8201729
theorem B7290425 : Blo 2275435 7290425 := bstep (se 2 (by rfl) ⟨2733909, by rfl⟩ : syracuseStep 7290425 = 5467819) B5467819
theorem B19441133 : Blo 2275435 19441133 := bstep (se 3 (by rfl) ⟨3645212, by rfl⟩ : syracuseStep 19441133 = 7290425) B7290425
theorem B12960755 : Blo 2275435 12960755 := bstep (se 1 (by rfl) ⟨9720566, by rfl⟩ : syracuseStep 12960755 = 19441133) B19441133
theorem B8640503 : Blo 2275435 8640503 := bstep (se 1 (by rfl) ⟨6480377, by rfl⟩ : syracuseStep 8640503 = 12960755) B12960755
theorem B5760335 : Blo 2275435 5760335 := bstep (se 1 (by rfl) ⟨4320251, by rfl⟩ : syracuseStep 5760335 = 8640503) B8640503
theorem B3840223 : Blo 2275435 3840223 := bstep (se 1 (by rfl) ⟨2880167, by rfl⟩ : syracuseStep 3840223 = 5760335) B5760335
theorem B5120297 : Blo 2275435 5120297 := bstep (se 2 (by rfl) ⟨1920111, by rfl⟩ : syracuseStep 5120297 = 3840223) B3840223
theorem B3413531 : Blo 2275435 3413531 := bstep (se 1 (by rfl) ⟨2560148, by rfl⟩ : syracuseStep 3413531 = 5120297) B5120297
theorem B2275687 : Blo 2275435 2275687 := bstep (se 1 (by rfl) ⟨1706765, by rfl⟩ : syracuseStep 2275687 = 3413531) B3413531
theorem B2560153 : Blo 2275435 2560153 := bbase (se 2 (by rfl) ⟨960057, by rfl⟩ : syracuseStep 2560153 = 1920115) (by norm_num)
theorem B3413537 : Blo 2275435 3413537 := bstep (se 2 (by rfl) ⟨1280076, by rfl⟩ : syracuseStep 3413537 = 2560153) B2560153
theorem B2275691 : Blo 2275435 2275691 := bstep (se 1 (by rfl) ⟨1706768, by rfl⟩ : syracuseStep 2275691 = 3413537) B3413537
theorem B8640533 : Blo 2275435 8640533 := bbase (se 6 (by rfl) ⟨202512, by rfl⟩ : syracuseStep 8640533 = 405025) (by norm_num)
theorem B5760355 : Blo 2275435 5760355 := bstep (se 1 (by rfl) ⟨4320266, by rfl⟩ : syracuseStep 5760355 = 8640533) B8640533
theorem B7680473 : Blo 2275435 7680473 := bstep (se 2 (by rfl) ⟨2880177, by rfl⟩ : syracuseStep 7680473 = 5760355) B5760355
theorem B5120315 : Blo 2275435 5120315 := bstep (se 1 (by rfl) ⟨3840236, by rfl⟩ : syracuseStep 5120315 = 7680473) B7680473
theorem B3413543 : Blo 2275435 3413543 := bstep (se 1 (by rfl) ⟨2560157, by rfl⟩ : syracuseStep 3413543 = 5120315) B5120315
theorem B2275695 : Blo 2275435 2275695 := bstep (se 1 (by rfl) ⟨1706771, by rfl⟩ : syracuseStep 2275695 = 3413543) B3413543
theorem B3413549 : Blo 2275435 3413549 := bbase (se 3 (by rfl) ⟨640040, by rfl⟩ : syracuseStep 3413549 = 1280081) (by norm_num)
theorem B2275699 : Blo 2275435 2275699 := bstep (se 1 (by rfl) ⟨1706774, by rfl⟩ : syracuseStep 2275699 = 3413549) B3413549
theorem B5120333 : Blo 2275435 5120333 := bbase (se 3 (by rfl) ⟨960062, by rfl⟩ : syracuseStep 5120333 = 1920125) (by norm_num)
theorem B3413555 : Blo 2275435 3413555 := bstep (se 1 (by rfl) ⟨2560166, by rfl⟩ : syracuseStep 3413555 = 5120333) B5120333
theorem B2275703 : Blo 2275435 2275703 := bstep (se 1 (by rfl) ⟨1706777, by rfl⟩ : syracuseStep 2275703 = 3413555) B3413555
theorem B2880193 : Blo 2275435 2880193 := bbase (se 2 (by rfl) ⟨1080072, by rfl⟩ : syracuseStep 2880193 = 2160145) (by norm_num)
theorem B3840257 : Blo 2275435 3840257 := bstep (se 2 (by rfl) ⟨1440096, by rfl⟩ : syracuseStep 3840257 = 2880193) B2880193
theorem B2560171 : Blo 2275435 2560171 := bstep (se 1 (by rfl) ⟨1920128, by rfl⟩ : syracuseStep 2560171 = 3840257) B3840257
theorem B3413561 : Blo 2275435 3413561 := bstep (se 2 (by rfl) ⟨1280085, by rfl⟩ : syracuseStep 3413561 = 2560171) B2560171
theorem B2275707 : Blo 2275435 2275707 := bstep (se 1 (by rfl) ⟨1706780, by rfl⟩ : syracuseStep 2275707 = 3413561) B3413561
theorem B5467877 : Blo 2275435 5467877 := bbase (se 4 (by rfl) ⟨512613, by rfl⟩ : syracuseStep 5467877 = 1025227) (by norm_num)
theorem B3645251 : Blo 2275435 3645251 := bstep (se 1 (by rfl) ⟨2733938, by rfl⟩ : syracuseStep 3645251 = 5467877) B5467877
theorem B2430167 : Blo 2275435 2430167 := bstep (se 1 (by rfl) ⟨1822625, by rfl⟩ : syracuseStep 2430167 = 3645251) B3645251
theorem B25921781 : Blo 2275435 25921781 := bstep (se 5 (by rfl) ⟨1215083, by rfl⟩ : syracuseStep 25921781 = 2430167) B2430167
theorem B17281187 : Blo 2275435 17281187 := bstep (se 1 (by rfl) ⟨12960890, by rfl⟩ : syracuseStep 17281187 = 25921781) B25921781
theorem B11520791 : Blo 2275435 11520791 := bstep (se 1 (by rfl) ⟨8640593, by rfl⟩ : syracuseStep 11520791 = 17281187) B17281187
theorem B7680527 : Blo 2275435 7680527 := bstep (se 1 (by rfl) ⟨5760395, by rfl⟩ : syracuseStep 7680527 = 11520791) B11520791
theorem B5120351 : Blo 2275435 5120351 := bstep (se 1 (by rfl) ⟨3840263, by rfl⟩ : syracuseStep 5120351 = 7680527) B7680527
theorem B3413567 : Blo 2275435 3413567 := bstep (se 1 (by rfl) ⟨2560175, by rfl⟩ : syracuseStep 3413567 = 5120351) B5120351
theorem B2275711 : Blo 2275435 2275711 := bstep (se 1 (by rfl) ⟨1706783, by rfl⟩ : syracuseStep 2275711 = 3413567) B3413567
theorem B3413573 : Blo 2275435 3413573 := bbase (se 4 (by rfl) ⟨320022, by rfl⟩ : syracuseStep 3413573 = 640045) (by norm_num)
theorem B2275715 : Blo 2275435 2275715 := bstep (se 1 (by rfl) ⟨1706786, by rfl⟩ : syracuseStep 2275715 = 3413573) B3413573
theorem B3840277 : Blo 2275435 3840277 := bbase (se 6 (by rfl) ⟨90006, by rfl⟩ : syracuseStep 3840277 = 180013) (by norm_num)
theorem B5120369 : Blo 2275435 5120369 := bstep (se 2 (by rfl) ⟨1920138, by rfl⟩ : syracuseStep 5120369 = 3840277) B3840277
theorem B3413579 : Blo 2275435 3413579 := bstep (se 1 (by rfl) ⟨2560184, by rfl⟩ : syracuseStep 3413579 = 5120369) B5120369
theorem B2275719 : Blo 2275435 2275719 := bstep (se 1 (by rfl) ⟨1706789, by rfl⟩ : syracuseStep 2275719 = 3413579) B3413579
theorem B2560189 : Blo 2275435 2560189 := bbase (se 3 (by rfl) ⟨480035, by rfl⟩ : syracuseStep 2560189 = 960071) (by norm_num)
theorem B3413585 : Blo 2275435 3413585 := bstep (se 2 (by rfl) ⟨1280094, by rfl⟩ : syracuseStep 3413585 = 2560189) B2560189
theorem B2275723 : Blo 2275435 2275723 := bstep (se 1 (by rfl) ⟨1706792, by rfl⟩ : syracuseStep 2275723 = 3413585) B3413585
theorem B7680581 : Blo 2275435 7680581 := bbase (se 4 (by rfl) ⟨720054, by rfl⟩ : syracuseStep 7680581 = 1440109) (by norm_num)
theorem B5120387 : Blo 2275435 5120387 := bstep (se 1 (by rfl) ⟨3840290, by rfl⟩ : syracuseStep 5120387 = 7680581) B7680581
theorem B3413591 : Blo 2275435 3413591 := bstep (se 1 (by rfl) ⟨2560193, by rfl⟩ : syracuseStep 3413591 = 5120387) B5120387
theorem B2275727 : Blo 2275435 2275727 := bstep (se 1 (by rfl) ⟨1706795, by rfl⟩ : syracuseStep 2275727 = 3413591) B3413591
theorem B3413597 : Blo 2275435 3413597 := bbase (se 3 (by rfl) ⟨640049, by rfl⟩ : syracuseStep 3413597 = 1280099) (by norm_num)
theorem B2275731 : Blo 2275435 2275731 := bstep (se 1 (by rfl) ⟨1706798, by rfl⟩ : syracuseStep 2275731 = 3413597) B3413597
theorem B5120405 : Blo 2275435 5120405 := bbase (se 6 (by rfl) ⟨120009, by rfl⟩ : syracuseStep 5120405 = 240019) (by norm_num)
theorem B3413603 : Blo 2275435 3413603 := bstep (se 1 (by rfl) ⟨2560202, by rfl⟩ : syracuseStep 3413603 = 5120405) B5120405
theorem B2275735 : Blo 2275435 2275735 := bstep (se 1 (by rfl) ⟨1706801, by rfl⟩ : syracuseStep 2275735 = 3413603) B3413603
theorem B20761109 : Blo 2275435 20761109 := bbase (se 6 (by rfl) ⟨486588, by rfl⟩ : syracuseStep 20761109 = 973177) (by norm_num)
theorem B13840739 : Blo 2275435 13840739 := bstep (se 1 (by rfl) ⟨10380554, by rfl⟩ : syracuseStep 13840739 = 20761109) B20761109
theorem B9227159 : Blo 2275435 9227159 := bstep (se 1 (by rfl) ⟨6920369, by rfl⟩ : syracuseStep 9227159 = 13840739) B13840739
theorem B6151439 : Blo 2275435 6151439 := bstep (se 1 (by rfl) ⟨4613579, by rfl⟩ : syracuseStep 6151439 = 9227159) B9227159
theorem B4100959 : Blo 2275435 4100959 := bstep (se 1 (by rfl) ⟨3075719, by rfl⟩ : syracuseStep 4100959 = 6151439) B6151439
theorem B5467945 : Blo 2275435 5467945 := bstep (se 2 (by rfl) ⟨2050479, by rfl⟩ : syracuseStep 5467945 = 4100959) B4100959
theorem B7290593 : Blo 2275435 7290593 := bstep (se 2 (by rfl) ⟨2733972, by rfl⟩ : syracuseStep 7290593 = 5467945) B5467945
theorem B4860395 : Blo 2275435 4860395 := bstep (se 1 (by rfl) ⟨3645296, by rfl⟩ : syracuseStep 4860395 = 7290593) B7290593
theorem B3240263 : Blo 2275435 3240263 := bstep (se 1 (by rfl) ⟨2430197, by rfl⟩ : syracuseStep 3240263 = 4860395) B4860395
theorem B8640701 : Blo 2275435 8640701 := bstep (se 3 (by rfl) ⟨1620131, by rfl⟩ : syracuseStep 8640701 = 3240263) B3240263
theorem B5760467 : Blo 2275435 5760467 := bstep (se 1 (by rfl) ⟨4320350, by rfl⟩ : syracuseStep 5760467 = 8640701) B8640701
theorem B3840311 : Blo 2275435 3840311 := bstep (se 1 (by rfl) ⟨2880233, by rfl⟩ : syracuseStep 3840311 = 5760467) B5760467
theorem B2560207 : Blo 2275435 2560207 := bstep (se 1 (by rfl) ⟨1920155, by rfl⟩ : syracuseStep 2560207 = 3840311) B3840311
theorem B3413609 : Blo 2275435 3413609 := bstep (se 2 (by rfl) ⟨1280103, by rfl⟩ : syracuseStep 3413609 = 2560207) B2560207
theorem B2275739 : Blo 2275435 2275739 := bstep (se 1 (by rfl) ⟨1706804, by rfl⟩ : syracuseStep 2275739 = 3413609) B3413609
theorem B9720805 : Blo 2275435 9720805 := bbase (se 4 (by rfl) ⟨911325, by rfl⟩ : syracuseStep 9720805 = 1822651) (by norm_num)
theorem B12961073 : Blo 2275435 12961073 := bstep (se 2 (by rfl) ⟨4860402, by rfl⟩ : syracuseStep 12961073 = 9720805) B9720805
theorem B8640715 : Blo 2275435 8640715 := bstep (se 1 (by rfl) ⟨6480536, by rfl⟩ : syracuseStep 8640715 = 12961073) B12961073
theorem B11520953 : Blo 2275435 11520953 := bstep (se 2 (by rfl) ⟨4320357, by rfl⟩ : syracuseStep 11520953 = 8640715) B8640715
theorem B7680635 : Blo 2275435 7680635 := bstep (se 1 (by rfl) ⟨5760476, by rfl⟩ : syracuseStep 7680635 = 11520953) B11520953
theorem B5120423 : Blo 2275435 5120423 := bstep (se 1 (by rfl) ⟨3840317, by rfl⟩ : syracuseStep 5120423 = 7680635) B7680635
theorem B3413615 : Blo 2275435 3413615 := bstep (se 1 (by rfl) ⟨2560211, by rfl⟩ : syracuseStep 3413615 = 5120423) B5120423
theorem B2275743 : Blo 2275435 2275743 := bstep (se 1 (by rfl) ⟨1706807, by rfl⟩ : syracuseStep 2275743 = 3413615) B3413615
theorem B3413621 : Blo 2275435 3413621 := bbase (se 5 (by rfl) ⟨160013, by rfl⟩ : syracuseStep 3413621 = 320027) (by norm_num)
theorem B2275747 : Blo 2275435 2275747 := bstep (se 1 (by rfl) ⟨1706810, by rfl⟩ : syracuseStep 2275747 = 3413621) B3413621
theorem B4320373 : Blo 2275435 4320373 := bbase (se 5 (by rfl) ⟨202517, by rfl⟩ : syracuseStep 4320373 = 405035) (by norm_num)
theorem B5760497 : Blo 2275435 5760497 := bstep (se 2 (by rfl) ⟨2160186, by rfl⟩ : syracuseStep 5760497 = 4320373) B4320373
theorem B3840331 : Blo 2275435 3840331 := bstep (se 1 (by rfl) ⟨2880248, by rfl⟩ : syracuseStep 3840331 = 5760497) B5760497
theorem B5120441 : Blo 2275435 5120441 := bstep (se 2 (by rfl) ⟨1920165, by rfl⟩ : syracuseStep 5120441 = 3840331) B3840331
theorem B3413627 : Blo 2275435 3413627 := bstep (se 1 (by rfl) ⟨2560220, by rfl⟩ : syracuseStep 3413627 = 5120441) B5120441
theorem B2275751 : Blo 2275435 2275751 := bstep (se 1 (by rfl) ⟨1706813, by rfl⟩ : syracuseStep 2275751 = 3413627) B3413627
theorem B2560225 : Blo 2275435 2560225 := bbase (se 2 (by rfl) ⟨960084, by rfl⟩ : syracuseStep 2560225 = 1920169) (by norm_num)
theorem B3413633 : Blo 2275435 3413633 := bstep (se 2 (by rfl) ⟨1280112, by rfl⟩ : syracuseStep 3413633 = 2560225) B2560225
theorem B2275755 : Blo 2275435 2275755 := bstep (se 1 (by rfl) ⟨1706816, by rfl⟩ : syracuseStep 2275755 = 3413633) B3413633
theorem B5760517 : Blo 2275435 5760517 := bbase (se 4 (by rfl) ⟨540048, by rfl⟩ : syracuseStep 5760517 = 1080097) (by norm_num)
theorem B7680689 : Blo 2275435 7680689 := bstep (se 2 (by rfl) ⟨2880258, by rfl⟩ : syracuseStep 7680689 = 5760517) B5760517
theorem B5120459 : Blo 2275435 5120459 := bstep (se 1 (by rfl) ⟨3840344, by rfl⟩ : syracuseStep 5120459 = 7680689) B7680689
theorem B3413639 : Blo 2275435 3413639 := bstep (se 1 (by rfl) ⟨2560229, by rfl⟩ : syracuseStep 3413639 = 5120459) B5120459
theorem B2275759 : Blo 2275435 2275759 := bstep (se 1 (by rfl) ⟨1706819, by rfl⟩ : syracuseStep 2275759 = 3413639) B3413639
theorem B3413645 : Blo 2275435 3413645 := bbase (se 3 (by rfl) ⟨640058, by rfl⟩ : syracuseStep 3413645 = 1280117) (by norm_num)
theorem B2275763 : Blo 2275435 2275763 := bstep (se 1 (by rfl) ⟨1706822, by rfl⟩ : syracuseStep 2275763 = 3413645) B3413645
theorem B5120477 : Blo 2275435 5120477 := bbase (se 3 (by rfl) ⟨960089, by rfl⟩ : syracuseStep 5120477 = 1920179) (by norm_num)
theorem B3413651 : Blo 2275435 3413651 := bstep (se 1 (by rfl) ⟨2560238, by rfl⟩ : syracuseStep 3413651 = 5120477) B5120477
theorem B2275767 : Blo 2275435 2275767 := bstep (se 1 (by rfl) ⟨1706825, by rfl⟩ : syracuseStep 2275767 = 3413651) B3413651
theorem B3840365 : Blo 2275435 3840365 := bbase (se 3 (by rfl) ⟨720068, by rfl⟩ : syracuseStep 3840365 = 1440137) (by norm_num)
theorem B2560243 : Blo 2275435 2560243 := bstep (se 1 (by rfl) ⟨1920182, by rfl⟩ : syracuseStep 2560243 = 3840365) B3840365
theorem B3413657 : Blo 2275435 3413657 := bstep (se 2 (by rfl) ⟨1280121, by rfl⟩ : syracuseStep 3413657 = 2560243) B2560243
theorem B2275771 : Blo 2275435 2275771 := bstep (se 1 (by rfl) ⟨1706828, by rfl⟩ : syracuseStep 2275771 = 3413657) B3413657
theorem B4676597 : Blo 2275435 4676597 := bbase (se 5 (by rfl) ⟨219215, by rfl⟩ : syracuseStep 4676597 = 438431) (by norm_num)
theorem B3117731 : Blo 2275435 3117731 := bstep (se 1 (by rfl) ⟨2338298, by rfl⟩ : syracuseStep 3117731 = 4676597) B4676597
theorem B8313949 : Blo 2275435 8313949 := bstep (se 3 (by rfl) ⟨1558865, by rfl⟩ : syracuseStep 8313949 = 3117731) B3117731
theorem B11085265 : Blo 2275435 11085265 := bstep (se 2 (by rfl) ⟨4156974, by rfl⟩ : syracuseStep 11085265 = 8313949) B8313949
theorem B59121413 : Blo 2275435 59121413 := bstep (se 4 (by rfl) ⟨5542632, by rfl⟩ : syracuseStep 59121413 = 11085265) B11085265
theorem B39414275 : Blo 2275435 39414275 := bstep (se 1 (by rfl) ⟨29560706, by rfl⟩ : syracuseStep 39414275 = 59121413) B59121413
theorem B26276183 : Blo 2275435 26276183 := bstep (se 1 (by rfl) ⟨19707137, by rfl⟩ : syracuseStep 26276183 = 39414275) B39414275
theorem B17517455 : Blo 2275435 17517455 := bstep (se 1 (by rfl) ⟨13138091, by rfl⟩ : syracuseStep 17517455 = 26276183) B26276183
theorem B11678303 : Blo 2275435 11678303 := bstep (se 1 (by rfl) ⟨8758727, by rfl⟩ : syracuseStep 11678303 = 17517455) B17517455
theorem B31142141 : Blo 2275435 31142141 := bstep (se 3 (by rfl) ⟨5839151, by rfl⟩ : syracuseStep 31142141 = 11678303) B11678303
theorem B20761427 : Blo 2275435 20761427 := bstep (se 1 (by rfl) ⟨15571070, by rfl⟩ : syracuseStep 20761427 = 31142141) B31142141
theorem B13840951 : Blo 2275435 13840951 := bstep (se 1 (by rfl) ⟨10380713, by rfl⟩ : syracuseStep 13840951 = 20761427) B20761427
theorem B18454601 : Blo 2275435 18454601 := bstep (se 2 (by rfl) ⟨6920475, by rfl⟩ : syracuseStep 18454601 = 13840951) B13840951
theorem B49212269 : Blo 2275435 49212269 := bstep (se 3 (by rfl) ⟨9227300, by rfl⟩ : syracuseStep 49212269 = 18454601) B18454601
theorem B32808179 : Blo 2275435 32808179 := bstep (se 1 (by rfl) ⟨24606134, by rfl⟩ : syracuseStep 32808179 = 49212269) B49212269
theorem B21872119 : Blo 2275435 21872119 := bstep (se 1 (by rfl) ⟨16404089, by rfl⟩ : syracuseStep 21872119 = 32808179) B32808179
theorem B29162825 : Blo 2275435 29162825 := bstep (se 2 (by rfl) ⟨10936059, by rfl⟩ : syracuseStep 29162825 = 21872119) B21872119
theorem B19441883 : Blo 2275435 19441883 := bstep (se 1 (by rfl) ⟨14581412, by rfl⟩ : syracuseStep 19441883 = 29162825) B29162825
theorem B12961255 : Blo 2275435 12961255 := bstep (se 1 (by rfl) ⟨9720941, by rfl⟩ : syracuseStep 12961255 = 19441883) B19441883
theorem B17281673 : Blo 2275435 17281673 := bstep (se 2 (by rfl) ⟨6480627, by rfl⟩ : syracuseStep 17281673 = 12961255) B12961255
theorem B11521115 : Blo 2275435 11521115 := bstep (se 1 (by rfl) ⟨8640836, by rfl⟩ : syracuseStep 11521115 = 17281673) B17281673
theorem B7680743 : Blo 2275435 7680743 := bstep (se 1 (by rfl) ⟨5760557, by rfl⟩ : syracuseStep 7680743 = 11521115) B11521115
theorem B5120495 : Blo 2275435 5120495 := bstep (se 1 (by rfl) ⟨3840371, by rfl⟩ : syracuseStep 5120495 = 7680743) B7680743
theorem B3413663 : Blo 2275435 3413663 := bstep (se 1 (by rfl) ⟨2560247, by rfl⟩ : syracuseStep 3413663 = 5120495) B5120495
theorem B2275775 : Blo 2275435 2275775 := bstep (se 1 (by rfl) ⟨1706831, by rfl⟩ : syracuseStep 2275775 = 3413663) B3413663
theorem B3413669 : Blo 2275435 3413669 := bbase (se 4 (by rfl) ⟨320031, by rfl⟩ : syracuseStep 3413669 = 640063) (by norm_num)
theorem B2275779 : Blo 2275435 2275779 := bstep (se 1 (by rfl) ⟨1706834, by rfl⟩ : syracuseStep 2275779 = 3413669) B3413669
theorem B2880289 : Blo 2275435 2880289 := bbase (se 2 (by rfl) ⟨1080108, by rfl⟩ : syracuseStep 2880289 = 2160217) (by norm_num)
theorem B3840385 : Blo 2275435 3840385 := bstep (se 2 (by rfl) ⟨1440144, by rfl⟩ : syracuseStep 3840385 = 2880289) B2880289
theorem B5120513 : Blo 2275435 5120513 := bstep (se 2 (by rfl) ⟨1920192, by rfl⟩ : syracuseStep 5120513 = 3840385) B3840385
theorem B3413675 : Blo 2275435 3413675 := bstep (se 1 (by rfl) ⟨2560256, by rfl⟩ : syracuseStep 3413675 = 5120513) B5120513
theorem B2275783 : Blo 2275435 2275783 := bstep (se 1 (by rfl) ⟨1706837, by rfl⟩ : syracuseStep 2275783 = 3413675) B3413675
theorem B2560261 : Blo 2275435 2560261 := bbase (se 4 (by rfl) ⟨240024, by rfl⟩ : syracuseStep 2560261 = 480049) (by norm_num)
theorem B3413681 : Blo 2275435 3413681 := bstep (se 2 (by rfl) ⟨1280130, by rfl⟩ : syracuseStep 3413681 = 2560261) B2560261
theorem B2275787 : Blo 2275435 2275787 := bstep (se 1 (by rfl) ⟨1706840, by rfl⟩ : syracuseStep 2275787 = 3413681) B3413681
theorem B2430253 : Blo 2275435 2430253 := bbase (se 3 (by rfl) ⟨455672, by rfl⟩ : syracuseStep 2430253 = 911345) (by norm_num)
theorem B3240337 : Blo 2275435 3240337 := bstep (se 2 (by rfl) ⟨1215126, by rfl⟩ : syracuseStep 3240337 = 2430253) B2430253
theorem B4320449 : Blo 2275435 4320449 := bstep (se 2 (by rfl) ⟨1620168, by rfl⟩ : syracuseStep 4320449 = 3240337) B3240337
theorem B2880299 : Blo 2275435 2880299 := bstep (se 1 (by rfl) ⟨2160224, by rfl⟩ : syracuseStep 2880299 = 4320449) B4320449
theorem B7680797 : Blo 2275435 7680797 := bstep (se 3 (by rfl) ⟨1440149, by rfl⟩ : syracuseStep 7680797 = 2880299) B2880299
theorem B5120531 : Blo 2275435 5120531 := bstep (se 1 (by rfl) ⟨3840398, by rfl⟩ : syracuseStep 5120531 = 7680797) B7680797
theorem B3413687 : Blo 2275435 3413687 := bstep (se 1 (by rfl) ⟨2560265, by rfl⟩ : syracuseStep 3413687 = 5120531) B5120531
theorem B2275791 : Blo 2275435 2275791 := bstep (se 1 (by rfl) ⟨1706843, by rfl⟩ : syracuseStep 2275791 = 3413687) B3413687
theorem B3413693 : Blo 2275435 3413693 := bbase (se 3 (by rfl) ⟨640067, by rfl⟩ : syracuseStep 3413693 = 1280135) (by norm_num)
theorem B2275795 : Blo 2275435 2275795 := bstep (se 1 (by rfl) ⟨1706846, by rfl⟩ : syracuseStep 2275795 = 3413693) B3413693
theorem B5120549 : Blo 2275435 5120549 := bbase (se 4 (by rfl) ⟨480051, by rfl⟩ : syracuseStep 5120549 = 960103) (by norm_num)
theorem B3413699 : Blo 2275435 3413699 := bstep (se 1 (by rfl) ⟨2560274, by rfl⟩ : syracuseStep 3413699 = 5120549) B5120549
theorem B2275799 : Blo 2275435 2275799 := bstep (se 1 (by rfl) ⟨1706849, by rfl⟩ : syracuseStep 2275799 = 3413699) B3413699
theorem B5760629 : Blo 2275435 5760629 := bbase (se 5 (by rfl) ⟨270029, by rfl⟩ : syracuseStep 5760629 = 540059) (by norm_num)
theorem B3840419 : Blo 2275435 3840419 := bstep (se 1 (by rfl) ⟨2880314, by rfl⟩ : syracuseStep 3840419 = 5760629) B5760629
theorem B2560279 : Blo 2275435 2560279 := bstep (se 1 (by rfl) ⟨1920209, by rfl⟩ : syracuseStep 2560279 = 3840419) B3840419
theorem B3413705 : Blo 2275435 3413705 := bstep (se 2 (by rfl) ⟨1280139, by rfl⟩ : syracuseStep 3413705 = 2560279) B2560279
theorem B2275803 : Blo 2275435 2275803 := bstep (se 1 (by rfl) ⟨1706852, by rfl⟩ : syracuseStep 2275803 = 3413705) B3413705
theorem B6151621 : Blo 2275435 6151621 := bbase (se 4 (by rfl) ⟨576714, by rfl⟩ : syracuseStep 6151621 = 1153429) (by norm_num)
theorem B8202161 : Blo 2275435 8202161 := bstep (se 2 (by rfl) ⟨3075810, by rfl⟩ : syracuseStep 8202161 = 6151621) B6151621
theorem B21872429 : Blo 2275435 21872429 := bstep (se 3 (by rfl) ⟨4101080, by rfl⟩ : syracuseStep 21872429 = 8202161) B8202161
theorem B14581619 : Blo 2275435 14581619 := bstep (se 1 (by rfl) ⟨10936214, by rfl⟩ : syracuseStep 14581619 = 21872429) B21872429
theorem B9721079 : Blo 2275435 9721079 := bstep (se 1 (by rfl) ⟨7290809, by rfl⟩ : syracuseStep 9721079 = 14581619) B14581619
theorem B6480719 : Blo 2275435 6480719 := bstep (se 1 (by rfl) ⟨4860539, by rfl⟩ : syracuseStep 6480719 = 9721079) B9721079
theorem B4320479 : Blo 2275435 4320479 := bstep (se 1 (by rfl) ⟨3240359, by rfl⟩ : syracuseStep 4320479 = 6480719) B6480719
theorem B11521277 : Blo 2275435 11521277 := bstep (se 3 (by rfl) ⟨2160239, by rfl⟩ : syracuseStep 11521277 = 4320479) B4320479
theorem B7680851 : Blo 2275435 7680851 := bstep (se 1 (by rfl) ⟨5760638, by rfl⟩ : syracuseStep 7680851 = 11521277) B11521277
theorem B5120567 : Blo 2275435 5120567 := bstep (se 1 (by rfl) ⟨3840425, by rfl⟩ : syracuseStep 5120567 = 7680851) B7680851
theorem B3413711 : Blo 2275435 3413711 := bstep (se 1 (by rfl) ⟨2560283, by rfl⟩ : syracuseStep 3413711 = 5120567) B5120567
theorem B2275807 : Blo 2275435 2275807 := bstep (se 1 (by rfl) ⟨1706855, by rfl⟩ : syracuseStep 2275807 = 3413711) B3413711
theorem B3413717 : Blo 2275435 3413717 := bbase (se 7 (by rfl) ⟨40004, by rfl⟩ : syracuseStep 3413717 = 80009) (by norm_num)
theorem B2275811 : Blo 2275435 2275811 := bstep (se 1 (by rfl) ⟨1706858, by rfl⟩ : syracuseStep 2275811 = 3413717) B3413717
theorem B4860557 : Blo 2275435 4860557 := bbase (se 3 (by rfl) ⟨911354, by rfl⟩ : syracuseStep 4860557 = 1822709) (by norm_num)
theorem B3240371 : Blo 2275435 3240371 := bstep (se 1 (by rfl) ⟨2430278, by rfl⟩ : syracuseStep 3240371 = 4860557) B4860557
theorem B8640989 : Blo 2275435 8640989 := bstep (se 3 (by rfl) ⟨1620185, by rfl⟩ : syracuseStep 8640989 = 3240371) B3240371
theorem B5760659 : Blo 2275435 5760659 := bstep (se 1 (by rfl) ⟨4320494, by rfl⟩ : syracuseStep 5760659 = 8640989) B8640989
theorem B3840439 : Blo 2275435 3840439 := bstep (se 1 (by rfl) ⟨2880329, by rfl⟩ : syracuseStep 3840439 = 5760659) B5760659
theorem B5120585 : Blo 2275435 5120585 := bstep (se 2 (by rfl) ⟨1920219, by rfl⟩ : syracuseStep 5120585 = 3840439) B3840439
theorem B3413723 : Blo 2275435 3413723 := bstep (se 1 (by rfl) ⟨2560292, by rfl⟩ : syracuseStep 3413723 = 5120585) B5120585
theorem B2275815 : Blo 2275435 2275815 := bstep (se 1 (by rfl) ⟨1706861, by rfl⟩ : syracuseStep 2275815 = 3413723) B3413723
theorem B2560297 : Blo 2275435 2560297 := bbase (se 2 (by rfl) ⟨960111, by rfl⟩ : syracuseStep 2560297 = 1920223) (by norm_num)
theorem B3413729 : Blo 2275435 3413729 := bstep (se 2 (by rfl) ⟨1280148, by rfl⟩ : syracuseStep 3413729 = 2560297) B2560297
theorem B2275819 : Blo 2275435 2275819 := bstep (se 1 (by rfl) ⟨1706864, by rfl⟩ : syracuseStep 2275819 = 3413729) B3413729
theorem B16404437 : Blo 2275435 16404437 := bbase (se 7 (by rfl) ⟨192239, by rfl⟩ : syracuseStep 16404437 = 384479) (by norm_num)
theorem B10936291 : Blo 2275435 10936291 := bstep (se 1 (by rfl) ⟨8202218, by rfl⟩ : syracuseStep 10936291 = 16404437) B16404437
theorem B14581721 : Blo 2275435 14581721 := bstep (se 2 (by rfl) ⟨5468145, by rfl⟩ : syracuseStep 14581721 = 10936291) B10936291
theorem B9721147 : Blo 2275435 9721147 := bstep (se 1 (by rfl) ⟨7290860, by rfl⟩ : syracuseStep 9721147 = 14581721) B14581721
theorem B12961529 : Blo 2275435 12961529 := bstep (se 2 (by rfl) ⟨4860573, by rfl⟩ : syracuseStep 12961529 = 9721147) B9721147
theorem B8641019 : Blo 2275435 8641019 := bstep (se 1 (by rfl) ⟨6480764, by rfl⟩ : syracuseStep 8641019 = 12961529) B12961529
theorem B5760679 : Blo 2275435 5760679 := bstep (se 1 (by rfl) ⟨4320509, by rfl⟩ : syracuseStep 5760679 = 8641019) B8641019
theorem B7680905 : Blo 2275435 7680905 := bstep (se 2 (by rfl) ⟨2880339, by rfl⟩ : syracuseStep 7680905 = 5760679) B5760679
theorem B5120603 : Blo 2275435 5120603 := bstep (se 1 (by rfl) ⟨3840452, by rfl⟩ : syracuseStep 5120603 = 7680905) B7680905
theorem B3413735 : Blo 2275435 3413735 := bstep (se 1 (by rfl) ⟨2560301, by rfl⟩ : syracuseStep 3413735 = 5120603) B5120603
theorem B2275823 : Blo 2275435 2275823 := bstep (se 1 (by rfl) ⟨1706867, by rfl⟩ : syracuseStep 2275823 = 3413735) B3413735
theorem B3413741 : Blo 2275435 3413741 := bbase (se 3 (by rfl) ⟨640076, by rfl⟩ : syracuseStep 3413741 = 1280153) (by norm_num)
theorem B2275827 : Blo 2275435 2275827 := bstep (se 1 (by rfl) ⟨1706870, by rfl⟩ : syracuseStep 2275827 = 3413741) B3413741
theorem B5120621 : Blo 2275435 5120621 := bbase (se 3 (by rfl) ⟨960116, by rfl⟩ : syracuseStep 5120621 = 1920233) (by norm_num)
theorem B3413747 : Blo 2275435 3413747 := bstep (se 1 (by rfl) ⟨2560310, by rfl⟩ : syracuseStep 3413747 = 5120621) B5120621
theorem B2275831 : Blo 2275435 2275831 := bstep (se 1 (by rfl) ⟨1706873, by rfl⟩ : syracuseStep 2275831 = 3413747) B3413747
theorem B4320533 : Blo 2275435 4320533 := bbase (se 6 (by rfl) ⟨101262, by rfl⟩ : syracuseStep 4320533 = 202525) (by norm_num)
theorem B2880355 : Blo 2275435 2880355 := bstep (se 1 (by rfl) ⟨2160266, by rfl⟩ : syracuseStep 2880355 = 4320533) B4320533
theorem B3840473 : Blo 2275435 3840473 := bstep (se 2 (by rfl) ⟨1440177, by rfl⟩ : syracuseStep 3840473 = 2880355) B2880355
theorem B2560315 : Blo 2275435 2560315 := bstep (se 1 (by rfl) ⟨1920236, by rfl⟩ : syracuseStep 2560315 = 3840473) B3840473
theorem B3413753 : Blo 2275435 3413753 := bstep (se 2 (by rfl) ⟨1280157, by rfl⟩ : syracuseStep 3413753 = 2560315) B2560315
theorem B2275835 : Blo 2275435 2275835 := bstep (se 1 (by rfl) ⟨1706876, by rfl⟩ : syracuseStep 2275835 = 3413753) B3413753
theorem B5542789 : Blo 2275435 5542789 := bbase (se 4 (by rfl) ⟨519636, by rfl⟩ : syracuseStep 5542789 = 1039273) (by norm_num)
theorem B7390385 : Blo 2275435 7390385 := bstep (se 2 (by rfl) ⟨2771394, by rfl⟩ : syracuseStep 7390385 = 5542789) B5542789
theorem B4926923 : Blo 2275435 4926923 := bstep (se 1 (by rfl) ⟨3695192, by rfl⟩ : syracuseStep 4926923 = 7390385) B7390385
theorem B3284615 : Blo 2275435 3284615 := bstep (se 1 (by rfl) ⟨2463461, by rfl⟩ : syracuseStep 3284615 = 4926923) B4926923
theorem B8758973 : Blo 2275435 8758973 := bstep (se 3 (by rfl) ⟨1642307, by rfl⟩ : syracuseStep 8758973 = 3284615) B3284615
theorem B23357261 : Blo 2275435 23357261 := bstep (se 3 (by rfl) ⟨4379486, by rfl⟩ : syracuseStep 23357261 = 8758973) B8758973
theorem B62286029 : Blo 2275435 62286029 := bstep (se 3 (by rfl) ⟨11678630, by rfl⟩ : syracuseStep 62286029 = 23357261) B23357261
theorem B41524019 : Blo 2275435 41524019 := bstep (se 1 (by rfl) ⟨31143014, by rfl⟩ : syracuseStep 41524019 = 62286029) B62286029
theorem B27682679 : Blo 2275435 27682679 := bstep (se 1 (by rfl) ⟨20762009, by rfl⟩ : syracuseStep 27682679 = 41524019) B41524019
theorem B73820477 : Blo 2275435 73820477 := bstep (se 3 (by rfl) ⟨13841339, by rfl⟩ : syracuseStep 73820477 = 27682679) B27682679
theorem B49213651 : Blo 2275435 49213651 := bstep (se 1 (by rfl) ⟨36910238, by rfl⟩ : syracuseStep 49213651 = 73820477) B73820477
theorem B65618201 : Blo 2275435 65618201 := bstep (se 2 (by rfl) ⟨24606825, by rfl⟩ : syracuseStep 65618201 = 49213651) B49213651
theorem B43745467 : Blo 2275435 43745467 := bstep (se 1 (by rfl) ⟨32809100, by rfl⟩ : syracuseStep 43745467 = 65618201) B65618201
theorem B58327289 : Blo 2275435 58327289 := bstep (se 2 (by rfl) ⟨21872733, by rfl⟩ : syracuseStep 58327289 = 43745467) B43745467
theorem B38884859 : Blo 2275435 38884859 := bstep (se 1 (by rfl) ⟨29163644, by rfl⟩ : syracuseStep 38884859 = 58327289) B58327289
theorem B25923239 : Blo 2275435 25923239 := bstep (se 1 (by rfl) ⟨19442429, by rfl⟩ : syracuseStep 25923239 = 38884859) B38884859
theorem B17282159 : Blo 2275435 17282159 := bstep (se 1 (by rfl) ⟨12961619, by rfl⟩ : syracuseStep 17282159 = 25923239) B25923239
theorem B11521439 : Blo 2275435 11521439 := bstep (se 1 (by rfl) ⟨8641079, by rfl⟩ : syracuseStep 11521439 = 17282159) B17282159
theorem B7680959 : Blo 2275435 7680959 := bstep (se 1 (by rfl) ⟨5760719, by rfl⟩ : syracuseStep 7680959 = 11521439) B11521439
theorem B5120639 : Blo 2275435 5120639 := bstep (se 1 (by rfl) ⟨3840479, by rfl⟩ : syracuseStep 5120639 = 7680959) B7680959
theorem B3413759 : Blo 2275435 3413759 := bstep (se 1 (by rfl) ⟨2560319, by rfl⟩ : syracuseStep 3413759 = 5120639) B5120639
theorem B2275839 : Blo 2275435 2275839 := bstep (se 1 (by rfl) ⟨1706879, by rfl⟩ : syracuseStep 2275839 = 3413759) B3413759
theorem B3413765 : Blo 2275435 3413765 := bbase (se 4 (by rfl) ⟨320040, by rfl⟩ : syracuseStep 3413765 = 640081) (by norm_num)
theorem B2275843 : Blo 2275435 2275843 := bstep (se 1 (by rfl) ⟨1706882, by rfl⟩ : syracuseStep 2275843 = 3413765) B3413765
theorem B3840493 : Blo 2275435 3840493 := bbase (se 3 (by rfl) ⟨720092, by rfl⟩ : syracuseStep 3840493 = 1440185) (by norm_num)
theorem B5120657 : Blo 2275435 5120657 := bstep (se 2 (by rfl) ⟨1920246, by rfl⟩ : syracuseStep 5120657 = 3840493) B3840493
theorem B3413771 : Blo 2275435 3413771 := bstep (se 1 (by rfl) ⟨2560328, by rfl⟩ : syracuseStep 3413771 = 5120657) B5120657
theorem B2275847 : Blo 2275435 2275847 := bstep (se 1 (by rfl) ⟨1706885, by rfl⟩ : syracuseStep 2275847 = 3413771) B3413771
theorem B2560333 : Blo 2275435 2560333 := bbase (se 3 (by rfl) ⟨480062, by rfl⟩ : syracuseStep 2560333 = 960125) (by norm_num)
theorem B3413777 : Blo 2275435 3413777 := bstep (se 2 (by rfl) ⟨1280166, by rfl⟩ : syracuseStep 3413777 = 2560333) B2560333
theorem B2275851 : Blo 2275435 2275851 := bstep (se 1 (by rfl) ⟨1706888, by rfl⟩ : syracuseStep 2275851 = 3413777) B3413777
theorem B7681013 : Blo 2275435 7681013 := bbase (se 5 (by rfl) ⟨360047, by rfl⟩ : syracuseStep 7681013 = 720095) (by norm_num)
theorem B5120675 : Blo 2275435 5120675 := bstep (se 1 (by rfl) ⟨3840506, by rfl⟩ : syracuseStep 5120675 = 7681013) B7681013
theorem B3413783 : Blo 2275435 3413783 := bstep (se 1 (by rfl) ⟨2560337, by rfl⟩ : syracuseStep 3413783 = 5120675) B5120675
theorem B2275855 : Blo 2275435 2275855 := bstep (se 1 (by rfl) ⟨1706891, by rfl⟩ : syracuseStep 2275855 = 3413783) B3413783
theorem B3413789 : Blo 2275435 3413789 := bbase (se 3 (by rfl) ⟨640085, by rfl⟩ : syracuseStep 3413789 = 1280171) (by norm_num)
theorem B2275859 : Blo 2275435 2275859 := bstep (se 1 (by rfl) ⟨1706894, by rfl⟩ : syracuseStep 2275859 = 3413789) B3413789
theorem B5120693 : Blo 2275435 5120693 := bbase (se 5 (by rfl) ⟨240032, by rfl⟩ : syracuseStep 5120693 = 480065) (by norm_num)
theorem B3413795 : Blo 2275435 3413795 := bstep (se 1 (by rfl) ⟨2560346, by rfl⟩ : syracuseStep 3413795 = 5120693) B5120693
theorem B2275863 : Blo 2275435 2275863 := bstep (se 1 (by rfl) ⟨1706897, by rfl⟩ : syracuseStep 2275863 = 3413795) B3413795
theorem B12961781 : Blo 2275435 12961781 := bbase (se 5 (by rfl) ⟨607583, by rfl⟩ : syracuseStep 12961781 = 1215167) (by norm_num)
theorem B8641187 : Blo 2275435 8641187 := bstep (se 1 (by rfl) ⟨6480890, by rfl⟩ : syracuseStep 8641187 = 12961781) B12961781
theorem B5760791 : Blo 2275435 5760791 := bstep (se 1 (by rfl) ⟨4320593, by rfl⟩ : syracuseStep 5760791 = 8641187) B8641187
theorem B3840527 : Blo 2275435 3840527 := bstep (se 1 (by rfl) ⟨2880395, by rfl⟩ : syracuseStep 3840527 = 5760791) B5760791
theorem B2560351 : Blo 2275435 2560351 := bstep (se 1 (by rfl) ⟨1920263, by rfl⟩ : syracuseStep 2560351 = 3840527) B3840527
theorem B3413801 : Blo 2275435 3413801 := bstep (se 2 (by rfl) ⟨1280175, by rfl⟩ : syracuseStep 3413801 = 2560351) B2560351
theorem B2275867 : Blo 2275435 2275867 := bstep (se 1 (by rfl) ⟨1706900, by rfl⟩ : syracuseStep 2275867 = 3413801) B3413801
theorem B6480901 : Blo 2275435 6480901 := bbase (se 4 (by rfl) ⟨607584, by rfl⟩ : syracuseStep 6480901 = 1215169) (by norm_num)
theorem B8641201 : Blo 2275435 8641201 := bstep (se 2 (by rfl) ⟨3240450, by rfl⟩ : syracuseStep 8641201 = 6480901) B6480901
theorem B11521601 : Blo 2275435 11521601 := bstep (se 2 (by rfl) ⟨4320600, by rfl⟩ : syracuseStep 11521601 = 8641201) B8641201
theorem B7681067 : Blo 2275435 7681067 := bstep (se 1 (by rfl) ⟨5760800, by rfl⟩ : syracuseStep 7681067 = 11521601) B11521601
theorem B5120711 : Blo 2275435 5120711 := bstep (se 1 (by rfl) ⟨3840533, by rfl⟩ : syracuseStep 5120711 = 7681067) B7681067
theorem B3413807 : Blo 2275435 3413807 := bstep (se 1 (by rfl) ⟨2560355, by rfl⟩ : syracuseStep 3413807 = 5120711) B5120711
theorem B2275871 : Blo 2275435 2275871 := bstep (se 1 (by rfl) ⟨1706903, by rfl⟩ : syracuseStep 2275871 = 3413807) B3413807
theorem B3413813 : Blo 2275435 3413813 := bbase (se 5 (by rfl) ⟨160022, by rfl⟩ : syracuseStep 3413813 = 320045) (by norm_num)
theorem B2275875 : Blo 2275435 2275875 := bstep (se 1 (by rfl) ⟨1706906, by rfl⟩ : syracuseStep 2275875 = 3413813) B3413813
theorem B5760821 : Blo 2275435 5760821 := bbase (se 5 (by rfl) ⟨270038, by rfl⟩ : syracuseStep 5760821 = 540077) (by norm_num)
theorem B3840547 : Blo 2275435 3840547 := bstep (se 1 (by rfl) ⟨2880410, by rfl⟩ : syracuseStep 3840547 = 5760821) B5760821
theorem B5120729 : Blo 2275435 5120729 := bstep (se 2 (by rfl) ⟨1920273, by rfl⟩ : syracuseStep 5120729 = 3840547) B3840547
theorem B3413819 : Blo 2275435 3413819 := bstep (se 1 (by rfl) ⟨2560364, by rfl⟩ : syracuseStep 3413819 = 5120729) B5120729
theorem B2275879 : Blo 2275435 2275879 := bstep (se 1 (by rfl) ⟨1706909, by rfl⟩ : syracuseStep 2275879 = 3413819) B3413819
theorem B2560369 : Blo 2275435 2560369 := bbase (se 2 (by rfl) ⟨960138, by rfl⟩ : syracuseStep 2560369 = 1920277) (by norm_num)
theorem B3413825 : Blo 2275435 3413825 := bstep (se 2 (by rfl) ⟨1280184, by rfl⟩ : syracuseStep 3413825 = 2560369) B2560369
theorem B2275883 : Blo 2275435 2275883 := bstep (se 1 (by rfl) ⟨1706912, by rfl⟩ : syracuseStep 2275883 = 3413825) B3413825
theorem B3645533 : Blo 2275435 3645533 := bbase (se 3 (by rfl) ⟨683537, by rfl⟩ : syracuseStep 3645533 = 1367075) (by norm_num)
theorem B9721421 : Blo 2275435 9721421 := bstep (se 3 (by rfl) ⟨1822766, by rfl⟩ : syracuseStep 9721421 = 3645533) B3645533
theorem B6480947 : Blo 2275435 6480947 := bstep (se 1 (by rfl) ⟨4860710, by rfl⟩ : syracuseStep 6480947 = 9721421) B9721421
theorem B4320631 : Blo 2275435 4320631 := bstep (se 1 (by rfl) ⟨3240473, by rfl⟩ : syracuseStep 4320631 = 6480947) B6480947
theorem B5760841 : Blo 2275435 5760841 := bstep (se 2 (by rfl) ⟨2160315, by rfl⟩ : syracuseStep 5760841 = 4320631) B4320631
theorem B7681121 : Blo 2275435 7681121 := bstep (se 2 (by rfl) ⟨2880420, by rfl⟩ : syracuseStep 7681121 = 5760841) B5760841
theorem B5120747 : Blo 2275435 5120747 := bstep (se 1 (by rfl) ⟨3840560, by rfl⟩ : syracuseStep 5120747 = 7681121) B7681121
theorem B3413831 : Blo 2275435 3413831 := bstep (se 1 (by rfl) ⟨2560373, by rfl⟩ : syracuseStep 3413831 = 5120747) B5120747
theorem B2275887 : Blo 2275435 2275887 := bstep (se 1 (by rfl) ⟨1706915, by rfl⟩ : syracuseStep 2275887 = 3413831) B3413831
theorem B3413837 : Blo 2275435 3413837 := bbase (se 3 (by rfl) ⟨640094, by rfl⟩ : syracuseStep 3413837 = 1280189) (by norm_num)
theorem B2275891 : Blo 2275435 2275891 := bstep (se 1 (by rfl) ⟨1706918, by rfl⟩ : syracuseStep 2275891 = 3413837) B3413837
theorem B5120765 : Blo 2275435 5120765 := bbase (se 3 (by rfl) ⟨960143, by rfl⟩ : syracuseStep 5120765 = 1920287) (by norm_num)
theorem B3413843 : Blo 2275435 3413843 := bstep (se 1 (by rfl) ⟨2560382, by rfl⟩ : syracuseStep 3413843 = 5120765) B5120765
theorem B2275895 : Blo 2275435 2275895 := bstep (se 1 (by rfl) ⟨1706921, by rfl⟩ : syracuseStep 2275895 = 3413843) B3413843
theorem B3840581 : Blo 2275435 3840581 := bbase (se 4 (by rfl) ⟨360054, by rfl⟩ : syracuseStep 3840581 = 720109) (by norm_num)
theorem B2560387 : Blo 2275435 2560387 := bstep (se 1 (by rfl) ⟨1920290, by rfl⟩ : syracuseStep 2560387 = 3840581) B3840581
theorem B3413849 : Blo 2275435 3413849 := bstep (se 2 (by rfl) ⟨1280193, by rfl⟩ : syracuseStep 3413849 = 2560387) B2560387
theorem B2275899 : Blo 2275435 2275899 := bstep (se 1 (by rfl) ⟨1706924, by rfl⟩ : syracuseStep 2275899 = 3413849) B3413849
theorem B17282645 : Blo 2275435 17282645 := bbase (se 8 (by rfl) ⟨101265, by rfl⟩ : syracuseStep 17282645 = 202531) (by norm_num)
theorem B11521763 : Blo 2275435 11521763 := bstep (se 1 (by rfl) ⟨8641322, by rfl⟩ : syracuseStep 11521763 = 17282645) B17282645
theorem B7681175 : Blo 2275435 7681175 := bstep (se 1 (by rfl) ⟨5760881, by rfl⟩ : syracuseStep 7681175 = 11521763) B11521763
theorem B5120783 : Blo 2275435 5120783 := bstep (se 1 (by rfl) ⟨3840587, by rfl⟩ : syracuseStep 5120783 = 7681175) B7681175
theorem B3413855 : Blo 2275435 3413855 := bstep (se 1 (by rfl) ⟨2560391, by rfl⟩ : syracuseStep 3413855 = 5120783) B5120783
theorem B2275903 : Blo 2275435 2275903 := bstep (se 1 (by rfl) ⟨1706927, by rfl⟩ : syracuseStep 2275903 = 3413855) B3413855
theorem B3413861 : Blo 2275435 3413861 := bbase (se 4 (by rfl) ⟨320049, by rfl⟩ : syracuseStep 3413861 = 640099) (by norm_num)
theorem B2275907 : Blo 2275435 2275907 := bstep (se 1 (by rfl) ⟨1706930, by rfl⟩ : syracuseStep 2275907 = 3413861) B3413861
theorem B4320677 : Blo 2275435 4320677 := bbase (se 4 (by rfl) ⟨405063, by rfl⟩ : syracuseStep 4320677 = 810127) (by norm_num)
theorem B2880451 : Blo 2275435 2880451 := bstep (se 1 (by rfl) ⟨2160338, by rfl⟩ : syracuseStep 2880451 = 4320677) B4320677
theorem B3840601 : Blo 2275435 3840601 := bstep (se 2 (by rfl) ⟨1440225, by rfl⟩ : syracuseStep 3840601 = 2880451) B2880451
theorem B5120801 : Blo 2275435 5120801 := bstep (se 2 (by rfl) ⟨1920300, by rfl⟩ : syracuseStep 5120801 = 3840601) B3840601
theorem B3413867 : Blo 2275435 3413867 := bstep (se 1 (by rfl) ⟨2560400, by rfl⟩ : syracuseStep 3413867 = 5120801) B5120801
theorem B2275911 : Blo 2275435 2275911 := bstep (se 1 (by rfl) ⟨1706933, by rfl⟩ : syracuseStep 2275911 = 3413867) B3413867
theorem B2560405 : Blo 2275435 2560405 := bbase (se 6 (by rfl) ⟨60009, by rfl⟩ : syracuseStep 2560405 = 120019) (by norm_num)
theorem B3413873 : Blo 2275435 3413873 := bstep (se 2 (by rfl) ⟨1280202, by rfl⟩ : syracuseStep 3413873 = 2560405) B2560405
theorem B2275915 : Blo 2275435 2275915 := bstep (se 1 (by rfl) ⟨1706936, by rfl⟩ : syracuseStep 2275915 = 3413873) B3413873
theorem B2880461 : Blo 2275435 2880461 := bbase (se 3 (by rfl) ⟨540086, by rfl⟩ : syracuseStep 2880461 = 1080173) (by norm_num)
theorem B7681229 : Blo 2275435 7681229 := bstep (se 3 (by rfl) ⟨1440230, by rfl⟩ : syracuseStep 7681229 = 2880461) B2880461
theorem B5120819 : Blo 2275435 5120819 := bstep (se 1 (by rfl) ⟨3840614, by rfl⟩ : syracuseStep 5120819 = 7681229) B7681229
theorem B3413879 : Blo 2275435 3413879 := bstep (se 1 (by rfl) ⟨2560409, by rfl⟩ : syracuseStep 3413879 = 5120819) B5120819
theorem B2275919 : Blo 2275435 2275919 := bstep (se 1 (by rfl) ⟨1706939, by rfl⟩ : syracuseStep 2275919 = 3413879) B3413879
theorem B3413885 : Blo 2275435 3413885 := bbase (se 3 (by rfl) ⟨640103, by rfl⟩ : syracuseStep 3413885 = 1280207) (by norm_num)
theorem B2275923 : Blo 2275435 2275923 := bstep (se 1 (by rfl) ⟨1706942, by rfl⟩ : syracuseStep 2275923 = 3413885) B3413885
theorem B5120837 : Blo 2275435 5120837 := bbase (se 4 (by rfl) ⟨480078, by rfl⟩ : syracuseStep 5120837 = 960157) (by norm_num)
theorem B3413891 : Blo 2275435 3413891 := bstep (se 1 (by rfl) ⟨2560418, by rfl⟩ : syracuseStep 3413891 = 5120837) B5120837
theorem B2275927 : Blo 2275435 2275927 := bstep (se 1 (by rfl) ⟨1706945, by rfl⟩ : syracuseStep 2275927 = 3413891) B3413891
theorem B4860805 : Blo 2275435 4860805 := bbase (se 4 (by rfl) ⟨455700, by rfl⟩ : syracuseStep 4860805 = 911401) (by norm_num)
theorem B6481073 : Blo 2275435 6481073 := bstep (se 2 (by rfl) ⟨2430402, by rfl⟩ : syracuseStep 6481073 = 4860805) B4860805
theorem B4320715 : Blo 2275435 4320715 := bstep (se 1 (by rfl) ⟨3240536, by rfl⟩ : syracuseStep 4320715 = 6481073) B6481073
theorem B5760953 : Blo 2275435 5760953 := bstep (se 2 (by rfl) ⟨2160357, by rfl⟩ : syracuseStep 5760953 = 4320715) B4320715
theorem B3840635 : Blo 2275435 3840635 := bstep (se 1 (by rfl) ⟨2880476, by rfl⟩ : syracuseStep 3840635 = 5760953) B5760953
theorem B2560423 : Blo 2275435 2560423 := bstep (se 1 (by rfl) ⟨1920317, by rfl⟩ : syracuseStep 2560423 = 3840635) B3840635
theorem B3413897 : Blo 2275435 3413897 := bstep (se 2 (by rfl) ⟨1280211, by rfl⟩ : syracuseStep 3413897 = 2560423) B2560423
theorem B2275931 : Blo 2275435 2275931 := bstep (se 1 (by rfl) ⟨1706948, by rfl⟩ : syracuseStep 2275931 = 3413897) B3413897
theorem B11521925 : Blo 2275435 11521925 := bbase (se 4 (by rfl) ⟨1080180, by rfl⟩ : syracuseStep 11521925 = 2160361) (by norm_num)
theorem B7681283 : Blo 2275435 7681283 := bstep (se 1 (by rfl) ⟨5760962, by rfl⟩ : syracuseStep 7681283 = 11521925) B11521925
theorem B5120855 : Blo 2275435 5120855 := bstep (se 1 (by rfl) ⟨3840641, by rfl⟩ : syracuseStep 5120855 = 7681283) B7681283
theorem B3413903 : Blo 2275435 3413903 := bstep (se 1 (by rfl) ⟨2560427, by rfl⟩ : syracuseStep 3413903 = 5120855) B5120855
theorem B2275935 : Blo 2275435 2275935 := bstep (se 1 (by rfl) ⟨1706951, by rfl⟩ : syracuseStep 2275935 = 3413903) B3413903
theorem B3413909 : Blo 2275435 3413909 := bbase (se 6 (by rfl) ⟨80013, by rfl⟩ : syracuseStep 3413909 = 160027) (by norm_num)
theorem B2275939 : Blo 2275435 2275939 := bstep (se 1 (by rfl) ⟨1706954, by rfl⟩ : syracuseStep 2275939 = 3413909) B3413909
theorem B11679173 : Blo 2275435 11679173 := bbase (se 4 (by rfl) ⟨1094922, by rfl⟩ : syracuseStep 11679173 = 2189845) (by norm_num)
theorem B7786115 : Blo 2275435 7786115 := bstep (se 1 (by rfl) ⟨5839586, by rfl⟩ : syracuseStep 7786115 = 11679173) B11679173
theorem B5190743 : Blo 2275435 5190743 := bstep (se 1 (by rfl) ⟨3893057, by rfl⟩ : syracuseStep 5190743 = 7786115) B7786115
theorem B3460495 : Blo 2275435 3460495 := bstep (se 1 (by rfl) ⟨2595371, by rfl⟩ : syracuseStep 3460495 = 5190743) B5190743
theorem B4613993 : Blo 2275435 4613993 := bstep (se 2 (by rfl) ⟨1730247, by rfl⟩ : syracuseStep 4613993 = 3460495) B3460495
theorem B3075995 : Blo 2275435 3075995 := bstep (se 1 (by rfl) ⟨2306996, by rfl⟩ : syracuseStep 3075995 = 4613993) B4613993
theorem B8202653 : Blo 2275435 8202653 := bstep (se 3 (by rfl) ⟨1537997, by rfl⟩ : syracuseStep 8202653 = 3075995) B3075995
theorem B5468435 : Blo 2275435 5468435 := bstep (se 1 (by rfl) ⟨4101326, by rfl⟩ : syracuseStep 5468435 = 8202653) B8202653
theorem B3645623 : Blo 2275435 3645623 := bstep (se 1 (by rfl) ⟨2734217, by rfl⟩ : syracuseStep 3645623 = 5468435) B5468435
theorem B2430415 : Blo 2275435 2430415 := bstep (se 1 (by rfl) ⟨1822811, by rfl⟩ : syracuseStep 2430415 = 3645623) B3645623
theorem B12962213 : Blo 2275435 12962213 := bstep (se 4 (by rfl) ⟨1215207, by rfl⟩ : syracuseStep 12962213 = 2430415) B2430415
theorem B8641475 : Blo 2275435 8641475 := bstep (se 1 (by rfl) ⟨6481106, by rfl⟩ : syracuseStep 8641475 = 12962213) B12962213
theorem B5760983 : Blo 2275435 5760983 := bstep (se 1 (by rfl) ⟨4320737, by rfl⟩ : syracuseStep 5760983 = 8641475) B8641475
theorem B3840655 : Blo 2275435 3840655 := bstep (se 1 (by rfl) ⟨2880491, by rfl⟩ : syracuseStep 3840655 = 5760983) B5760983
theorem B5120873 : Blo 2275435 5120873 := bstep (se 2 (by rfl) ⟨1920327, by rfl⟩ : syracuseStep 5120873 = 3840655) B3840655
theorem B3413915 : Blo 2275435 3413915 := bstep (se 1 (by rfl) ⟨2560436, by rfl⟩ : syracuseStep 3413915 = 5120873) B5120873
theorem B2275943 : Blo 2275435 2275943 := bstep (se 1 (by rfl) ⟨1706957, by rfl⟩ : syracuseStep 2275943 = 3413915) B3413915
theorem B2560441 : Blo 2275435 2560441 := bbase (se 2 (by rfl) ⟨960165, by rfl⟩ : syracuseStep 2560441 = 1920331) (by norm_num)
theorem B3413921 : Blo 2275435 3413921 := bstep (se 2 (by rfl) ⟨1280220, by rfl⟩ : syracuseStep 3413921 = 2560441) B2560441
theorem B2275947 : Blo 2275435 2275947 := bstep (se 1 (by rfl) ⟨1706960, by rfl⟩ : syracuseStep 2275947 = 3413921) B3413921
theorem B12304021 : Blo 2275435 12304021 := bbase (se 6 (by rfl) ⟨288375, by rfl⟩ : syracuseStep 12304021 = 576751) (by norm_num)
theorem B16405361 : Blo 2275435 16405361 := bstep (se 2 (by rfl) ⟨6152010, by rfl⟩ : syracuseStep 16405361 = 12304021) B12304021
theorem B10936907 : Blo 2275435 10936907 := bstep (se 1 (by rfl) ⟨8202680, by rfl⟩ : syracuseStep 10936907 = 16405361) B16405361
theorem B7291271 : Blo 2275435 7291271 := bstep (se 1 (by rfl) ⟨5468453, by rfl⟩ : syracuseStep 7291271 = 10936907) B10936907
theorem B4860847 : Blo 2275435 4860847 := bstep (se 1 (by rfl) ⟨3645635, by rfl⟩ : syracuseStep 4860847 = 7291271) B7291271
theorem B6481129 : Blo 2275435 6481129 := bstep (se 2 (by rfl) ⟨2430423, by rfl⟩ : syracuseStep 6481129 = 4860847) B4860847
theorem B8641505 : Blo 2275435 8641505 := bstep (se 2 (by rfl) ⟨3240564, by rfl⟩ : syracuseStep 8641505 = 6481129) B6481129
theorem B5761003 : Blo 2275435 5761003 := bstep (se 1 (by rfl) ⟨4320752, by rfl⟩ : syracuseStep 5761003 = 8641505) B8641505
theorem B7681337 : Blo 2275435 7681337 := bstep (se 2 (by rfl) ⟨2880501, by rfl⟩ : syracuseStep 7681337 = 5761003) B5761003
theorem B5120891 : Blo 2275435 5120891 := bstep (se 1 (by rfl) ⟨3840668, by rfl⟩ : syracuseStep 5120891 = 7681337) B7681337
theorem B3413927 : Blo 2275435 3413927 := bstep (se 1 (by rfl) ⟨2560445, by rfl⟩ : syracuseStep 3413927 = 5120891) B5120891
theorem B2275951 : Blo 2275435 2275951 := bstep (se 1 (by rfl) ⟨1706963, by rfl⟩ : syracuseStep 2275951 = 3413927) B3413927
theorem B3413933 : Blo 2275435 3413933 := bbase (se 3 (by rfl) ⟨640112, by rfl⟩ : syracuseStep 3413933 = 1280225) (by norm_num)
theorem B2275955 : Blo 2275435 2275955 := bstep (se 1 (by rfl) ⟨1706966, by rfl⟩ : syracuseStep 2275955 = 3413933) B3413933
theorem B5120909 : Blo 2275435 5120909 := bbase (se 3 (by rfl) ⟨960170, by rfl⟩ : syracuseStep 5120909 = 1920341) (by norm_num)
theorem B3413939 : Blo 2275435 3413939 := bstep (se 1 (by rfl) ⟨2560454, by rfl⟩ : syracuseStep 3413939 = 5120909) B5120909
theorem B2275959 : Blo 2275435 2275959 := bstep (se 1 (by rfl) ⟨1706969, by rfl⟩ : syracuseStep 2275959 = 3413939) B3413939
theorem B2880517 : Blo 2275435 2880517 := bbase (se 4 (by rfl) ⟨270048, by rfl⟩ : syracuseStep 2880517 = 540097) (by norm_num)
theorem B3840689 : Blo 2275435 3840689 := bstep (se 2 (by rfl) ⟨1440258, by rfl⟩ : syracuseStep 3840689 = 2880517) B2880517
theorem B2560459 : Blo 2275435 2560459 := bstep (se 1 (by rfl) ⟨1920344, by rfl⟩ : syracuseStep 2560459 = 3840689) B3840689
theorem B3413945 : Blo 2275435 3413945 := bstep (se 2 (by rfl) ⟨1280229, by rfl⟩ : syracuseStep 3413945 = 2560459) B2560459
theorem B2275963 : Blo 2275435 2275963 := bstep (se 1 (by rfl) ⟨1706972, by rfl⟩ : syracuseStep 2275963 = 3413945) B3413945
theorem B6152053 : Blo 2275435 6152053 := bbase (se 5 (by rfl) ⟨288377, by rfl⟩ : syracuseStep 6152053 = 576755) (by norm_num)
theorem B8202737 : Blo 2275435 8202737 := bstep (se 2 (by rfl) ⟨3076026, by rfl⟩ : syracuseStep 8202737 = 6152053) B6152053
theorem B5468491 : Blo 2275435 5468491 := bstep (se 1 (by rfl) ⟨4101368, by rfl⟩ : syracuseStep 5468491 = 8202737) B8202737
theorem B29165285 : Blo 2275435 29165285 := bstep (se 4 (by rfl) ⟨2734245, by rfl⟩ : syracuseStep 29165285 = 5468491) B5468491
theorem B19443523 : Blo 2275435 19443523 := bstep (se 1 (by rfl) ⟨14582642, by rfl⟩ : syracuseStep 19443523 = 29165285) B29165285
theorem B25924697 : Blo 2275435 25924697 := bstep (se 2 (by rfl) ⟨9721761, by rfl⟩ : syracuseStep 25924697 = 19443523) B19443523
theorem B17283131 : Blo 2275435 17283131 := bstep (se 1 (by rfl) ⟨12962348, by rfl⟩ : syracuseStep 17283131 = 25924697) B25924697
theorem B11522087 : Blo 2275435 11522087 := bstep (se 1 (by rfl) ⟨8641565, by rfl⟩ : syracuseStep 11522087 = 17283131) B17283131
theorem B7681391 : Blo 2275435 7681391 := bstep (se 1 (by rfl) ⟨5761043, by rfl⟩ : syracuseStep 7681391 = 11522087) B11522087
theorem B5120927 : Blo 2275435 5120927 := bstep (se 1 (by rfl) ⟨3840695, by rfl⟩ : syracuseStep 5120927 = 7681391) B7681391
theorem B3413951 : Blo 2275435 3413951 := bstep (se 1 (by rfl) ⟨2560463, by rfl⟩ : syracuseStep 3413951 = 5120927) B5120927
theorem B2275967 : Blo 2275435 2275967 := bstep (se 1 (by rfl) ⟨1706975, by rfl⟩ : syracuseStep 2275967 = 3413951) B3413951
theorem B3413957 : Blo 2275435 3413957 := bbase (se 4 (by rfl) ⟨320058, by rfl⟩ : syracuseStep 3413957 = 640117) (by norm_num)
theorem B2275971 : Blo 2275435 2275971 := bstep (se 1 (by rfl) ⟨1706978, by rfl⟩ : syracuseStep 2275971 = 3413957) B3413957
theorem B3840709 : Blo 2275435 3840709 := bbase (se 4 (by rfl) ⟨360066, by rfl⟩ : syracuseStep 3840709 = 720133) (by norm_num)
theorem B5120945 : Blo 2275435 5120945 := bstep (se 2 (by rfl) ⟨1920354, by rfl⟩ : syracuseStep 5120945 = 3840709) B3840709
theorem B3413963 : Blo 2275435 3413963 := bstep (se 1 (by rfl) ⟨2560472, by rfl⟩ : syracuseStep 3413963 = 5120945) B5120945
theorem B2275975 : Blo 2275435 2275975 := bstep (se 1 (by rfl) ⟨1706981, by rfl⟩ : syracuseStep 2275975 = 3413963) B3413963
theorem B2560477 : Blo 2275435 2560477 := bbase (se 3 (by rfl) ⟨480089, by rfl⟩ : syracuseStep 2560477 = 960179) (by norm_num)
theorem B3413969 : Blo 2275435 3413969 := bstep (se 2 (by rfl) ⟨1280238, by rfl⟩ : syracuseStep 3413969 = 2560477) B2560477
theorem B2275979 : Blo 2275435 2275979 := bstep (se 1 (by rfl) ⟨1706984, by rfl⟩ : syracuseStep 2275979 = 3413969) B3413969
theorem B7681445 : Blo 2275435 7681445 := bbase (se 4 (by rfl) ⟨720135, by rfl⟩ : syracuseStep 7681445 = 1440271) (by norm_num)
theorem B5120963 : Blo 2275435 5120963 := bstep (se 1 (by rfl) ⟨3840722, by rfl⟩ : syracuseStep 5120963 = 7681445) B7681445
theorem B3413975 : Blo 2275435 3413975 := bstep (se 1 (by rfl) ⟨2560481, by rfl⟩ : syracuseStep 3413975 = 5120963) B5120963
theorem B2275983 : Blo 2275435 2275983 := bstep (se 1 (by rfl) ⟨1706987, by rfl⟩ : syracuseStep 2275983 = 3413975) B3413975
theorem B3413981 : Blo 2275435 3413981 := bbase (se 3 (by rfl) ⟨640121, by rfl⟩ : syracuseStep 3413981 = 1280243) (by norm_num)
theorem B2275987 : Blo 2275435 2275987 := bstep (se 1 (by rfl) ⟨1706990, by rfl⟩ : syracuseStep 2275987 = 3413981) B3413981
theorem B5120981 : Blo 2275435 5120981 := bbase (se 7 (by rfl) ⟨60011, by rfl⟩ : syracuseStep 5120981 = 120023) (by norm_num)
theorem B3413987 : Blo 2275435 3413987 := bstep (se 1 (by rfl) ⟨2560490, by rfl⟩ : syracuseStep 3413987 = 5120981) B5120981
theorem B2275991 : Blo 2275435 2275991 := bstep (se 1 (by rfl) ⟨1706993, by rfl⟩ : syracuseStep 2275991 = 3413987) B3413987
theorem B23358869 : Blo 2275435 23358869 := bbase (se 6 (by rfl) ⟨547473, by rfl⟩ : syracuseStep 23358869 = 1094947) (by norm_num)
theorem B15572579 : Blo 2275435 15572579 := bstep (se 1 (by rfl) ⟨11679434, by rfl⟩ : syracuseStep 15572579 = 23358869) B23358869
theorem B41526877 : Blo 2275435 41526877 := bstep (se 3 (by rfl) ⟨7786289, by rfl⟩ : syracuseStep 41526877 = 15572579) B15572579
theorem B55369169 : Blo 2275435 55369169 := bstep (se 2 (by rfl) ⟨20763438, by rfl⟩ : syracuseStep 55369169 = 41526877) B41526877
theorem B36912779 : Blo 2275435 36912779 := bstep (se 1 (by rfl) ⟨27684584, by rfl⟩ : syracuseStep 36912779 = 55369169) B55369169
theorem B24608519 : Blo 2275435 24608519 := bstep (se 1 (by rfl) ⟨18456389, by rfl⟩ : syracuseStep 24608519 = 36912779) B36912779
theorem B16405679 : Blo 2275435 16405679 := bstep (se 1 (by rfl) ⟨12304259, by rfl⟩ : syracuseStep 16405679 = 24608519) B24608519
theorem B10937119 : Blo 2275435 10937119 := bstep (se 1 (by rfl) ⟨8202839, by rfl⟩ : syracuseStep 10937119 = 16405679) B16405679
theorem B14582825 : Blo 2275435 14582825 := bstep (se 2 (by rfl) ⟨5468559, by rfl⟩ : syracuseStep 14582825 = 10937119) B10937119
theorem B9721883 : Blo 2275435 9721883 := bstep (se 1 (by rfl) ⟨7291412, by rfl⟩ : syracuseStep 9721883 = 14582825) B14582825
theorem B6481255 : Blo 2275435 6481255 := bstep (se 1 (by rfl) ⟨4860941, by rfl⟩ : syracuseStep 6481255 = 9721883) B9721883
theorem B8641673 : Blo 2275435 8641673 := bstep (se 2 (by rfl) ⟨3240627, by rfl⟩ : syracuseStep 8641673 = 6481255) B6481255
theorem B5761115 : Blo 2275435 5761115 := bstep (se 1 (by rfl) ⟨4320836, by rfl⟩ : syracuseStep 5761115 = 8641673) B8641673
theorem B3840743 : Blo 2275435 3840743 := bstep (se 1 (by rfl) ⟨2880557, by rfl⟩ : syracuseStep 3840743 = 5761115) B5761115
theorem B2560495 : Blo 2275435 2560495 := bstep (se 1 (by rfl) ⟨1920371, by rfl⟩ : syracuseStep 2560495 = 3840743) B3840743
theorem B3413993 : Blo 2275435 3413993 := bstep (se 2 (by rfl) ⟨1280247, by rfl⟩ : syracuseStep 3413993 = 2560495) B2560495
theorem B2275995 : Blo 2275435 2275995 := bstep (se 1 (by rfl) ⟨1706996, by rfl⟩ : syracuseStep 2275995 = 3413993) B3413993
theorem B19443797 : Blo 2275435 19443797 := bbase (se 8 (by rfl) ⟨113928, by rfl⟩ : syracuseStep 19443797 = 227857) (by norm_num)
theorem B12962531 : Blo 2275435 12962531 := bstep (se 1 (by rfl) ⟨9721898, by rfl⟩ : syracuseStep 12962531 = 19443797) B19443797
theorem B8641687 : Blo 2275435 8641687 := bstep (se 1 (by rfl) ⟨6481265, by rfl⟩ : syracuseStep 8641687 = 12962531) B12962531
theorem B11522249 : Blo 2275435 11522249 := bstep (se 2 (by rfl) ⟨4320843, by rfl⟩ : syracuseStep 11522249 = 8641687) B8641687
theorem B7681499 : Blo 2275435 7681499 := bstep (se 1 (by rfl) ⟨5761124, by rfl⟩ : syracuseStep 7681499 = 11522249) B11522249
theorem B5120999 : Blo 2275435 5120999 := bstep (se 1 (by rfl) ⟨3840749, by rfl⟩ : syracuseStep 5120999 = 7681499) B7681499
theorem B3413999 : Blo 2275435 3413999 := bstep (se 1 (by rfl) ⟨2560499, by rfl⟩ : syracuseStep 3413999 = 5120999) B5120999
theorem B2275999 : Blo 2275435 2275999 := bstep (se 1 (by rfl) ⟨1706999, by rfl⟩ : syracuseStep 2275999 = 3413999) B3413999
theorem B3414005 : Blo 2275435 3414005 := bbase (se 5 (by rfl) ⟨160031, by rfl⟩ : syracuseStep 3414005 = 320063) (by norm_num)
theorem B2276003 : Blo 2275435 2276003 := bstep (se 1 (by rfl) ⟨1707002, by rfl⟩ : syracuseStep 2276003 = 3414005) B3414005
theorem B2307061 : Blo 2275435 2307061 := bbase (se 5 (by rfl) ⟨108143, by rfl⟩ : syracuseStep 2307061 = 216287) (by norm_num)
theorem B12304325 : Blo 2275435 12304325 := bstep (se 4 (by rfl) ⟨1153530, by rfl⟩ : syracuseStep 12304325 = 2307061) B2307061
theorem B8202883 : Blo 2275435 8202883 := bstep (se 1 (by rfl) ⟨6152162, by rfl⟩ : syracuseStep 8202883 = 12304325) B12304325
theorem B10937177 : Blo 2275435 10937177 := bstep (se 2 (by rfl) ⟨4101441, by rfl⟩ : syracuseStep 10937177 = 8202883) B8202883
theorem B7291451 : Blo 2275435 7291451 := bstep (se 1 (by rfl) ⟨5468588, by rfl⟩ : syracuseStep 7291451 = 10937177) B10937177
theorem B4860967 : Blo 2275435 4860967 := bstep (se 1 (by rfl) ⟨3645725, by rfl⟩ : syracuseStep 4860967 = 7291451) B7291451
theorem B6481289 : Blo 2275435 6481289 := bstep (se 2 (by rfl) ⟨2430483, by rfl⟩ : syracuseStep 6481289 = 4860967) B4860967
theorem B4320859 : Blo 2275435 4320859 := bstep (se 1 (by rfl) ⟨3240644, by rfl⟩ : syracuseStep 4320859 = 6481289) B6481289
theorem B5761145 : Blo 2275435 5761145 := bstep (se 2 (by rfl) ⟨2160429, by rfl⟩ : syracuseStep 5761145 = 4320859) B4320859
theorem B3840763 : Blo 2275435 3840763 := bstep (se 1 (by rfl) ⟨2880572, by rfl⟩ : syracuseStep 3840763 = 5761145) B5761145
theorem B5121017 : Blo 2275435 5121017 := bstep (se 2 (by rfl) ⟨1920381, by rfl⟩ : syracuseStep 5121017 = 3840763) B3840763
theorem B3414011 : Blo 2275435 3414011 := bstep (se 1 (by rfl) ⟨2560508, by rfl⟩ : syracuseStep 3414011 = 5121017) B5121017
theorem B2276007 : Blo 2275435 2276007 := bstep (se 1 (by rfl) ⟨1707005, by rfl⟩ : syracuseStep 2276007 = 3414011) B3414011
theorem B2560513 : Blo 2275435 2560513 := bbase (se 2 (by rfl) ⟨960192, by rfl⟩ : syracuseStep 2560513 = 1920385) (by norm_num)
theorem B3414017 : Blo 2275435 3414017 := bstep (se 2 (by rfl) ⟨1280256, by rfl⟩ : syracuseStep 3414017 = 2560513) B2560513
theorem B2276011 : Blo 2275435 2276011 := bstep (se 1 (by rfl) ⟨1707008, by rfl⟩ : syracuseStep 2276011 = 3414017) B3414017
theorem B5761165 : Blo 2275435 5761165 := bbase (se 3 (by rfl) ⟨1080218, by rfl⟩ : syracuseStep 5761165 = 2160437) (by norm_num)
theorem B7681553 : Blo 2275435 7681553 := bstep (se 2 (by rfl) ⟨2880582, by rfl⟩ : syracuseStep 7681553 = 5761165) B5761165
theorem B5121035 : Blo 2275435 5121035 := bstep (se 1 (by rfl) ⟨3840776, by rfl⟩ : syracuseStep 5121035 = 7681553) B7681553
theorem B3414023 : Blo 2275435 3414023 := bstep (se 1 (by rfl) ⟨2560517, by rfl⟩ : syracuseStep 3414023 = 5121035) B5121035
theorem B2276015 : Blo 2275435 2276015 := bstep (se 1 (by rfl) ⟨1707011, by rfl⟩ : syracuseStep 2276015 = 3414023) B3414023
theorem B3414029 : Blo 2275435 3414029 := bbase (se 3 (by rfl) ⟨640130, by rfl⟩ : syracuseStep 3414029 = 1280261) (by norm_num)
theorem B2276019 : Blo 2275435 2276019 := bstep (se 1 (by rfl) ⟨1707014, by rfl⟩ : syracuseStep 2276019 = 3414029) B3414029
theorem B5121053 : Blo 2275435 5121053 := bbase (se 3 (by rfl) ⟨960197, by rfl⟩ : syracuseStep 5121053 = 1920395) (by norm_num)
theorem B3414035 : Blo 2275435 3414035 := bstep (se 1 (by rfl) ⟨2560526, by rfl⟩ : syracuseStep 3414035 = 5121053) B5121053
theorem B2276023 : Blo 2275435 2276023 := bstep (se 1 (by rfl) ⟨1707017, by rfl⟩ : syracuseStep 2276023 = 3414035) B3414035
theorem B3840797 : Blo 2275435 3840797 := bbase (se 3 (by rfl) ⟨720149, by rfl⟩ : syracuseStep 3840797 = 1440299) (by norm_num)
theorem B2560531 : Blo 2275435 2560531 := bstep (se 1 (by rfl) ⟨1920398, by rfl⟩ : syracuseStep 2560531 = 3840797) B3840797
theorem B3414041 : Blo 2275435 3414041 := bstep (se 2 (by rfl) ⟨1280265, by rfl⟩ : syracuseStep 3414041 = 2560531) B2560531
theorem B2276027 : Blo 2275435 2276027 := bstep (se 1 (by rfl) ⟨1707020, by rfl⟩ : syracuseStep 2276027 = 3414041) B3414041
theorem B5468645 : Blo 2275435 5468645 := bbase (se 4 (by rfl) ⟨512685, by rfl⟩ : syracuseStep 5468645 = 1025371) (by norm_num)
theorem B14583053 : Blo 2275435 14583053 := bstep (se 3 (by rfl) ⟨2734322, by rfl⟩ : syracuseStep 14583053 = 5468645) B5468645
theorem B9722035 : Blo 2275435 9722035 := bstep (se 1 (by rfl) ⟨7291526, by rfl⟩ : syracuseStep 9722035 = 14583053) B14583053
theorem B12962713 : Blo 2275435 12962713 := bstep (se 2 (by rfl) ⟨4861017, by rfl⟩ : syracuseStep 12962713 = 9722035) B9722035
theorem B17283617 : Blo 2275435 17283617 := bstep (se 2 (by rfl) ⟨6481356, by rfl⟩ : syracuseStep 17283617 = 12962713) B12962713
theorem B11522411 : Blo 2275435 11522411 := bstep (se 1 (by rfl) ⟨8641808, by rfl⟩ : syracuseStep 11522411 = 17283617) B17283617
theorem B7681607 : Blo 2275435 7681607 := bstep (se 1 (by rfl) ⟨5761205, by rfl⟩ : syracuseStep 7681607 = 11522411) B11522411
theorem B5121071 : Blo 2275435 5121071 := bstep (se 1 (by rfl) ⟨3840803, by rfl⟩ : syracuseStep 5121071 = 7681607) B7681607
theorem B3414047 : Blo 2275435 3414047 := bstep (se 1 (by rfl) ⟨2560535, by rfl⟩ : syracuseStep 3414047 = 5121071) B5121071
theorem B2276031 : Blo 2275435 2276031 := bstep (se 1 (by rfl) ⟨1707023, by rfl⟩ : syracuseStep 2276031 = 3414047) B3414047
theorem B3414053 : Blo 2275435 3414053 := bbase (se 4 (by rfl) ⟨320067, by rfl⟩ : syracuseStep 3414053 = 640135) (by norm_num)
theorem B2276035 : Blo 2275435 2276035 := bstep (se 1 (by rfl) ⟨1707026, by rfl⟩ : syracuseStep 2276035 = 3414053) B3414053
theorem B2880613 : Blo 2275435 2880613 := bbase (se 4 (by rfl) ⟨270057, by rfl⟩ : syracuseStep 2880613 = 540115) (by norm_num)
theorem B3840817 : Blo 2275435 3840817 := bstep (se 2 (by rfl) ⟨1440306, by rfl⟩ : syracuseStep 3840817 = 2880613) B2880613
theorem B5121089 : Blo 2275435 5121089 := bstep (se 2 (by rfl) ⟨1920408, by rfl⟩ : syracuseStep 5121089 = 3840817) B3840817
theorem B3414059 : Blo 2275435 3414059 := bstep (se 1 (by rfl) ⟨2560544, by rfl⟩ : syracuseStep 3414059 = 5121089) B5121089
theorem B2276039 : Blo 2275435 2276039 := bstep (se 1 (by rfl) ⟨1707029, by rfl⟩ : syracuseStep 2276039 = 3414059) B3414059
theorem B2560549 : Blo 2275435 2560549 := bbase (se 4 (by rfl) ⟨240051, by rfl⟩ : syracuseStep 2560549 = 480103) (by norm_num)
theorem B3414065 : Blo 2275435 3414065 := bstep (se 2 (by rfl) ⟨1280274, by rfl⟩ : syracuseStep 3414065 = 2560549) B2560549
theorem B2276043 : Blo 2275435 2276043 := bstep (se 1 (by rfl) ⟨1707032, by rfl⟩ : syracuseStep 2276043 = 3414065) B3414065
theorem B7786469 : Blo 2275435 7786469 := bbase (se 4 (by rfl) ⟨729981, by rfl⟩ : syracuseStep 7786469 = 1459963) (by norm_num)
theorem B5190979 : Blo 2275435 5190979 := bstep (se 1 (by rfl) ⟨3893234, by rfl⟩ : syracuseStep 5190979 = 7786469) B7786469
theorem B6921305 : Blo 2275435 6921305 := bstep (se 2 (by rfl) ⟨2595489, by rfl⟩ : syracuseStep 6921305 = 5190979) B5190979
theorem B4614203 : Blo 2275435 4614203 := bstep (se 1 (by rfl) ⟨3460652, by rfl⟩ : syracuseStep 4614203 = 6921305) B6921305
theorem B12304541 : Blo 2275435 12304541 := bstep (se 3 (by rfl) ⟨2307101, by rfl⟩ : syracuseStep 12304541 = 4614203) B4614203
theorem B8203027 : Blo 2275435 8203027 := bstep (se 1 (by rfl) ⟨6152270, by rfl⟩ : syracuseStep 8203027 = 12304541) B12304541
theorem B10937369 : Blo 2275435 10937369 := bstep (se 2 (by rfl) ⟨4101513, by rfl⟩ : syracuseStep 10937369 = 8203027) B8203027
theorem B7291579 : Blo 2275435 7291579 := bstep (se 1 (by rfl) ⟨5468684, by rfl⟩ : syracuseStep 7291579 = 10937369) B10937369
theorem B9722105 : Blo 2275435 9722105 := bstep (se 2 (by rfl) ⟨3645789, by rfl⟩ : syracuseStep 9722105 = 7291579) B7291579
theorem B6481403 : Blo 2275435 6481403 := bstep (se 1 (by rfl) ⟨4861052, by rfl⟩ : syracuseStep 6481403 = 9722105) B9722105
theorem B4320935 : Blo 2275435 4320935 := bstep (se 1 (by rfl) ⟨3240701, by rfl⟩ : syracuseStep 4320935 = 6481403) B6481403
theorem B2880623 : Blo 2275435 2880623 := bstep (se 1 (by rfl) ⟨2160467, by rfl⟩ : syracuseStep 2880623 = 4320935) B4320935
theorem B7681661 : Blo 2275435 7681661 := bstep (se 3 (by rfl) ⟨1440311, by rfl⟩ : syracuseStep 7681661 = 2880623) B2880623
theorem B5121107 : Blo 2275435 5121107 := bstep (se 1 (by rfl) ⟨3840830, by rfl⟩ : syracuseStep 5121107 = 7681661) B7681661
theorem B3414071 : Blo 2275435 3414071 := bstep (se 1 (by rfl) ⟨2560553, by rfl⟩ : syracuseStep 3414071 = 5121107) B5121107
theorem B2276047 : Blo 2275435 2276047 := bstep (se 1 (by rfl) ⟨1707035, by rfl⟩ : syracuseStep 2276047 = 3414071) B3414071
theorem B3414077 : Blo 2275435 3414077 := bbase (se 3 (by rfl) ⟨640139, by rfl⟩ : syracuseStep 3414077 = 1280279) (by norm_num)
theorem B2276051 : Blo 2275435 2276051 := bstep (se 1 (by rfl) ⟨1707038, by rfl⟩ : syracuseStep 2276051 = 3414077) B3414077
theorem B5121125 : Blo 2275435 5121125 := bbase (se 4 (by rfl) ⟨480105, by rfl⟩ : syracuseStep 5121125 = 960211) (by norm_num)
theorem B3414083 : Blo 2275435 3414083 := bstep (se 1 (by rfl) ⟨2560562, by rfl⟩ : syracuseStep 3414083 = 5121125) B5121125
theorem B2276055 : Blo 2275435 2276055 := bstep (se 1 (by rfl) ⟨1707041, by rfl⟩ : syracuseStep 2276055 = 3414083) B3414083
theorem B5761277 : Blo 2275435 5761277 := bbase (se 3 (by rfl) ⟨1080239, by rfl⟩ : syracuseStep 5761277 = 2160479) (by norm_num)
theorem B3840851 : Blo 2275435 3840851 := bstep (se 1 (by rfl) ⟨2880638, by rfl⟩ : syracuseStep 3840851 = 5761277) B5761277
theorem B2560567 : Blo 2275435 2560567 := bstep (se 1 (by rfl) ⟨1920425, by rfl⟩ : syracuseStep 2560567 = 3840851) B3840851
theorem B3414089 : Blo 2275435 3414089 := bstep (se 2 (by rfl) ⟨1280283, by rfl⟩ : syracuseStep 3414089 = 2560567) B2560567
theorem B2276059 : Blo 2275435 2276059 := bstep (se 1 (by rfl) ⟨1707044, by rfl⟩ : syracuseStep 2276059 = 3414089) B3414089
theorem B4320965 : Blo 2275435 4320965 := bbase (se 4 (by rfl) ⟨405090, by rfl⟩ : syracuseStep 4320965 = 810181) (by norm_num)
theorem B11522573 : Blo 2275435 11522573 := bstep (se 3 (by rfl) ⟨2160482, by rfl⟩ : syracuseStep 11522573 = 4320965) B4320965
theorem B7681715 : Blo 2275435 7681715 := bstep (se 1 (by rfl) ⟨5761286, by rfl⟩ : syracuseStep 7681715 = 11522573) B11522573
theorem B5121143 : Blo 2275435 5121143 := bstep (se 1 (by rfl) ⟨3840857, by rfl⟩ : syracuseStep 5121143 = 7681715) B7681715
theorem B3414095 : Blo 2275435 3414095 := bstep (se 1 (by rfl) ⟨2560571, by rfl⟩ : syracuseStep 3414095 = 5121143) B5121143
theorem B2276063 : Blo 2275435 2276063 := bstep (se 1 (by rfl) ⟨1707047, by rfl⟩ : syracuseStep 2276063 = 3414095) B3414095
theorem B3414101 : Blo 2275435 3414101 := bbase (se 8 (by rfl) ⟨20004, by rfl⟩ : syracuseStep 3414101 = 40009) (by norm_num)
theorem B2276067 : Blo 2275435 2276067 := bstep (se 1 (by rfl) ⟨1707050, by rfl⟩ : syracuseStep 2276067 = 3414101) B3414101
theorem B16630069 : Blo 2275435 16630069 := bbase (se 5 (by rfl) ⟨779534, by rfl⟩ : syracuseStep 16630069 = 1559069) (by norm_num)
theorem B22173425 : Blo 2275435 22173425 := bstep (se 2 (by rfl) ⟨8315034, by rfl⟩ : syracuseStep 22173425 = 16630069) B16630069
theorem B14782283 : Blo 2275435 14782283 := bstep (se 1 (by rfl) ⟨11086712, by rfl⟩ : syracuseStep 14782283 = 22173425) B22173425
theorem B9854855 : Blo 2275435 9854855 := bstep (se 1 (by rfl) ⟨7391141, by rfl⟩ : syracuseStep 9854855 = 14782283) B14782283
theorem B6569903 : Blo 2275435 6569903 := bstep (se 1 (by rfl) ⟨4927427, by rfl⟩ : syracuseStep 6569903 = 9854855) B9854855
theorem B4379935 : Blo 2275435 4379935 := bstep (se 1 (by rfl) ⟨3284951, by rfl⟩ : syracuseStep 4379935 = 6569903) B6569903
theorem B5839913 : Blo 2275435 5839913 := bstep (se 2 (by rfl) ⟨2189967, by rfl⟩ : syracuseStep 5839913 = 4379935) B4379935
theorem B3893275 : Blo 2275435 3893275 := bstep (se 1 (by rfl) ⟨2919956, by rfl⟩ : syracuseStep 3893275 = 5839913) B5839913
theorem B5191033 : Blo 2275435 5191033 := bstep (se 2 (by rfl) ⟨1946637, by rfl⟩ : syracuseStep 5191033 = 3893275) B3893275
theorem B6921377 : Blo 2275435 6921377 := bstep (se 2 (by rfl) ⟨2595516, by rfl⟩ : syracuseStep 6921377 = 5191033) B5191033
theorem B4614251 : Blo 2275435 4614251 := bstep (se 1 (by rfl) ⟨3460688, by rfl⟩ : syracuseStep 4614251 = 6921377) B6921377
theorem B49218677 : Blo 2275435 49218677 := bstep (se 5 (by rfl) ⟨2307125, by rfl⟩ : syracuseStep 49218677 = 4614251) B4614251
theorem B32812451 : Blo 2275435 32812451 := bstep (se 1 (by rfl) ⟨24609338, by rfl⟩ : syracuseStep 32812451 = 49218677) B49218677
theorem B21874967 : Blo 2275435 21874967 := bstep (se 1 (by rfl) ⟨16406225, by rfl⟩ : syracuseStep 21874967 = 32812451) B32812451
theorem B14583311 : Blo 2275435 14583311 := bstep (se 1 (by rfl) ⟨10937483, by rfl⟩ : syracuseStep 14583311 = 21874967) B21874967
theorem B9722207 : Blo 2275435 9722207 := bstep (se 1 (by rfl) ⟨7291655, by rfl⟩ : syracuseStep 9722207 = 14583311) B14583311
theorem B6481471 : Blo 2275435 6481471 := bstep (se 1 (by rfl) ⟨4861103, by rfl⟩ : syracuseStep 6481471 = 9722207) B9722207
theorem B8641961 : Blo 2275435 8641961 := bstep (se 2 (by rfl) ⟨3240735, by rfl⟩ : syracuseStep 8641961 = 6481471) B6481471
theorem B5761307 : Blo 2275435 5761307 := bstep (se 1 (by rfl) ⟨4320980, by rfl⟩ : syracuseStep 5761307 = 8641961) B8641961
theorem B3840871 : Blo 2275435 3840871 := bstep (se 1 (by rfl) ⟨2880653, by rfl⟩ : syracuseStep 3840871 = 5761307) B5761307
theorem B5121161 : Blo 2275435 5121161 := bstep (se 2 (by rfl) ⟨1920435, by rfl⟩ : syracuseStep 5121161 = 3840871) B3840871
theorem B3414107 : Blo 2275435 3414107 := bstep (se 1 (by rfl) ⟨2560580, by rfl⟩ : syracuseStep 3414107 = 5121161) B5121161
theorem B2276071 : Blo 2275435 2276071 := bstep (se 1 (by rfl) ⟨1707053, by rfl⟩ : syracuseStep 2276071 = 3414107) B3414107
theorem B2560585 : Blo 2275435 2560585 := bbase (se 2 (by rfl) ⟨960219, by rfl⟩ : syracuseStep 2560585 = 1920439) (by norm_num)
theorem B3414113 : Blo 2275435 3414113 := bstep (se 2 (by rfl) ⟨1280292, by rfl⟩ : syracuseStep 3414113 = 2560585) B2560585
theorem B2276075 : Blo 2275435 2276075 := bstep (se 1 (by rfl) ⟨1707056, by rfl⟩ : syracuseStep 2276075 = 3414113) B3414113
theorem B8203141 : Blo 2275435 8203141 := bbase (se 4 (by rfl) ⟨769044, by rfl⟩ : syracuseStep 8203141 = 1538089) (by norm_num)
theorem B10937521 : Blo 2275435 10937521 := bstep (se 2 (by rfl) ⟨4101570, by rfl⟩ : syracuseStep 10937521 = 8203141) B8203141
theorem B14583361 : Blo 2275435 14583361 := bstep (se 2 (by rfl) ⟨5468760, by rfl⟩ : syracuseStep 14583361 = 10937521) B10937521
theorem B19444481 : Blo 2275435 19444481 := bstep (se 2 (by rfl) ⟨7291680, by rfl⟩ : syracuseStep 19444481 = 14583361) B14583361
theorem B12962987 : Blo 2275435 12962987 := bstep (se 1 (by rfl) ⟨9722240, by rfl⟩ : syracuseStep 12962987 = 19444481) B19444481
theorem B8641991 : Blo 2275435 8641991 := bstep (se 1 (by rfl) ⟨6481493, by rfl⟩ : syracuseStep 8641991 = 12962987) B12962987
theorem B5761327 : Blo 2275435 5761327 := bstep (se 1 (by rfl) ⟨4320995, by rfl⟩ : syracuseStep 5761327 = 8641991) B8641991
theorem B7681769 : Blo 2275435 7681769 := bstep (se 2 (by rfl) ⟨2880663, by rfl⟩ : syracuseStep 7681769 = 5761327) B5761327
theorem B5121179 : Blo 2275435 5121179 := bstep (se 1 (by rfl) ⟨3840884, by rfl⟩ : syracuseStep 5121179 = 7681769) B7681769
theorem B3414119 : Blo 2275435 3414119 := bstep (se 1 (by rfl) ⟨2560589, by rfl⟩ : syracuseStep 3414119 = 5121179) B5121179
theorem B2276079 : Blo 2275435 2276079 := bstep (se 1 (by rfl) ⟨1707059, by rfl⟩ : syracuseStep 2276079 = 3414119) B3414119
theorem B3414125 : Blo 2275435 3414125 := bbase (se 3 (by rfl) ⟨640148, by rfl⟩ : syracuseStep 3414125 = 1280297) (by norm_num)
theorem B2276083 : Blo 2275435 2276083 := bstep (se 1 (by rfl) ⟨1707062, by rfl⟩ : syracuseStep 2276083 = 3414125) B3414125
theorem B5121197 : Blo 2275435 5121197 := bbase (se 3 (by rfl) ⟨960224, by rfl⟩ : syracuseStep 5121197 = 1920449) (by norm_num)
theorem B3414131 : Blo 2275435 3414131 := bstep (se 1 (by rfl) ⟨2560598, by rfl⟩ : syracuseStep 3414131 = 5121197) B5121197
theorem B2276087 : Blo 2275435 2276087 := bstep (se 1 (by rfl) ⟨1707065, by rfl⟩ : syracuseStep 2276087 = 3414131) B3414131
theorem B4614293 : Blo 2275435 4614293 := bbase (se 6 (by rfl) ⟨108147, by rfl⟩ : syracuseStep 4614293 = 216295) (by norm_num)
theorem B12304781 : Blo 2275435 12304781 := bstep (se 3 (by rfl) ⟨2307146, by rfl⟩ : syracuseStep 12304781 = 4614293) B4614293
theorem B8203187 : Blo 2275435 8203187 := bstep (se 1 (by rfl) ⟨6152390, by rfl⟩ : syracuseStep 8203187 = 12304781) B12304781
theorem B5468791 : Blo 2275435 5468791 := bstep (se 1 (by rfl) ⟨4101593, by rfl⟩ : syracuseStep 5468791 = 8203187) B8203187
theorem B7291721 : Blo 2275435 7291721 := bstep (se 2 (by rfl) ⟨2734395, by rfl⟩ : syracuseStep 7291721 = 5468791) B5468791
theorem B4861147 : Blo 2275435 4861147 := bstep (se 1 (by rfl) ⟨3645860, by rfl⟩ : syracuseStep 4861147 = 7291721) B7291721
theorem B6481529 : Blo 2275435 6481529 := bstep (se 2 (by rfl) ⟨2430573, by rfl⟩ : syracuseStep 6481529 = 4861147) B4861147
theorem B4321019 : Blo 2275435 4321019 := bstep (se 1 (by rfl) ⟨3240764, by rfl⟩ : syracuseStep 4321019 = 6481529) B6481529
theorem B2880679 : Blo 2275435 2880679 := bstep (se 1 (by rfl) ⟨2160509, by rfl⟩ : syracuseStep 2880679 = 4321019) B4321019
theorem B3840905 : Blo 2275435 3840905 := bstep (se 2 (by rfl) ⟨1440339, by rfl⟩ : syracuseStep 3840905 = 2880679) B2880679
theorem B2560603 : Blo 2275435 2560603 := bstep (se 1 (by rfl) ⟨1920452, by rfl⟩ : syracuseStep 2560603 = 3840905) B3840905
theorem B3414137 : Blo 2275435 3414137 := bstep (se 2 (by rfl) ⟨1280301, by rfl⟩ : syracuseStep 3414137 = 2560603) B2560603
theorem B2276091 : Blo 2275435 2276091 := bstep (se 1 (by rfl) ⟨1707068, by rfl⟩ : syracuseStep 2276091 = 3414137) B3414137
theorem B3555805 : Blo 2275435 3555805 := bbase (se 3 (by rfl) ⟨666713, by rfl⟩ : syracuseStep 3555805 = 1333427) (by norm_num)
theorem B4741073 : Blo 2275435 4741073 := bstep (se 2 (by rfl) ⟨1777902, by rfl⟩ : syracuseStep 4741073 = 3555805) B3555805
theorem B3160715 : Blo 2275435 3160715 := bstep (se 1 (by rfl) ⟨2370536, by rfl⟩ : syracuseStep 3160715 = 4741073) B4741073
theorem B8428573 : Blo 2275435 8428573 := bstep (se 3 (by rfl) ⟨1580357, by rfl⟩ : syracuseStep 8428573 = 3160715) B3160715
theorem B11238097 : Blo 2275435 11238097 := bstep (se 2 (by rfl) ⟨4214286, by rfl⟩ : syracuseStep 11238097 = 8428573) B8428573
theorem B14984129 : Blo 2275435 14984129 := bstep (se 2 (by rfl) ⟨5619048, by rfl⟩ : syracuseStep 14984129 = 11238097) B11238097
theorem B9989419 : Blo 2275435 9989419 := bstep (se 1 (by rfl) ⟨7492064, by rfl⟩ : syracuseStep 9989419 = 14984129) B14984129
theorem B13319225 : Blo 2275435 13319225 := bstep (se 2 (by rfl) ⟨4994709, by rfl⟩ : syracuseStep 13319225 = 9989419) B9989419
theorem B8879483 : Blo 2275435 8879483 := bstep (se 1 (by rfl) ⟨6659612, by rfl⟩ : syracuseStep 8879483 = 13319225) B13319225
theorem B5919655 : Blo 2275435 5919655 := bstep (se 1 (by rfl) ⟨4439741, by rfl⟩ : syracuseStep 5919655 = 8879483) B8879483
theorem B7892873 : Blo 2275435 7892873 := bstep (se 2 (by rfl) ⟨2959827, by rfl⟩ : syracuseStep 7892873 = 5919655) B5919655
theorem B5261915 : Blo 2275435 5261915 := bstep (se 1 (by rfl) ⟨3946436, by rfl⟩ : syracuseStep 5261915 = 7892873) B7892873
theorem B3507943 : Blo 2275435 3507943 := bstep (se 1 (by rfl) ⟨2630957, by rfl⟩ : syracuseStep 3507943 = 5261915) B5261915
theorem B4677257 : Blo 2275435 4677257 := bstep (se 2 (by rfl) ⟨1753971, by rfl⟩ : syracuseStep 4677257 = 3507943) B3507943
theorem B3118171 : Blo 2275435 3118171 := bstep (se 1 (by rfl) ⟨2338628, by rfl⟩ : syracuseStep 3118171 = 4677257) B4677257
theorem B4157561 : Blo 2275435 4157561 := bstep (se 2 (by rfl) ⟨1559085, by rfl⟩ : syracuseStep 4157561 = 3118171) B3118171
theorem B2771707 : Blo 2275435 2771707 := bstep (se 1 (by rfl) ⟨2078780, by rfl⟩ : syracuseStep 2771707 = 4157561) B4157561
theorem B3695609 : Blo 2275435 3695609 := bstep (se 2 (by rfl) ⟨1385853, by rfl⟩ : syracuseStep 3695609 = 2771707) B2771707
theorem B2463739 : Blo 2275435 2463739 := bstep (se 1 (by rfl) ⟨1847804, by rfl⟩ : syracuseStep 2463739 = 3695609) B3695609
theorem B13139941 : Blo 2275435 13139941 := bstep (se 4 (by rfl) ⟨1231869, by rfl⟩ : syracuseStep 13139941 = 2463739) B2463739
theorem B17519921 : Blo 2275435 17519921 := bstep (se 2 (by rfl) ⟨6569970, by rfl⟩ : syracuseStep 17519921 = 13139941) B13139941
theorem B11679947 : Blo 2275435 11679947 := bstep (se 1 (by rfl) ⟨8759960, by rfl⟩ : syracuseStep 11679947 = 17519921) B17519921
theorem B7786631 : Blo 2275435 7786631 := bstep (se 1 (by rfl) ⟨5839973, by rfl⟩ : syracuseStep 7786631 = 11679947) B11679947
theorem B20764349 : Blo 2275435 20764349 := bstep (se 3 (by rfl) ⟨3893315, by rfl⟩ : syracuseStep 20764349 = 7786631) B7786631
theorem B13842899 : Blo 2275435 13842899 := bstep (se 1 (by rfl) ⟨10382174, by rfl⟩ : syracuseStep 13842899 = 20764349) B20764349
theorem B9228599 : Blo 2275435 9228599 := bstep (se 1 (by rfl) ⟨6921449, by rfl⟩ : syracuseStep 9228599 = 13842899) B13842899
theorem B6152399 : Blo 2275435 6152399 := bstep (se 1 (by rfl) ⟨4614299, by rfl⟩ : syracuseStep 6152399 = 9228599) B9228599
theorem B4101599 : Blo 2275435 4101599 := bstep (se 1 (by rfl) ⟨3076199, by rfl⟩ : syracuseStep 4101599 = 6152399) B6152399
theorem B10937597 : Blo 2275435 10937597 := bstep (se 3 (by rfl) ⟨2050799, by rfl⟩ : syracuseStep 10937597 = 4101599) B4101599
theorem B29166925 : Blo 2275435 29166925 := bstep (se 3 (by rfl) ⟨5468798, by rfl⟩ : syracuseStep 29166925 = 10937597) B10937597
theorem B38889233 : Blo 2275435 38889233 := bstep (se 2 (by rfl) ⟨14583462, by rfl⟩ : syracuseStep 38889233 = 29166925) B29166925
theorem B25926155 : Blo 2275435 25926155 := bstep (se 1 (by rfl) ⟨19444616, by rfl⟩ : syracuseStep 25926155 = 38889233) B38889233
theorem B17284103 : Blo 2275435 17284103 := bstep (se 1 (by rfl) ⟨12963077, by rfl⟩ : syracuseStep 17284103 = 25926155) B25926155
theorem B11522735 : Blo 2275435 11522735 := bstep (se 1 (by rfl) ⟨8642051, by rfl⟩ : syracuseStep 11522735 = 17284103) B17284103
theorem B7681823 : Blo 2275435 7681823 := bstep (se 1 (by rfl) ⟨5761367, by rfl⟩ : syracuseStep 7681823 = 11522735) B11522735
theorem B5121215 : Blo 2275435 5121215 := bstep (se 1 (by rfl) ⟨3840911, by rfl⟩ : syracuseStep 5121215 = 7681823) B7681823
theorem B3414143 : Blo 2275435 3414143 := bstep (se 1 (by rfl) ⟨2560607, by rfl⟩ : syracuseStep 3414143 = 5121215) B5121215
theorem B2276095 : Blo 2275435 2276095 := bstep (se 1 (by rfl) ⟨1707071, by rfl⟩ : syracuseStep 2276095 = 3414143) B3414143
theorem B3414149 : Blo 2275435 3414149 := bbase (se 4 (by rfl) ⟨320076, by rfl⟩ : syracuseStep 3414149 = 640153) (by norm_num)
theorem B2276099 : Blo 2275435 2276099 := bstep (se 1 (by rfl) ⟨1707074, by rfl⟩ : syracuseStep 2276099 = 3414149) B3414149
theorem B3840925 : Blo 2275435 3840925 := bbase (se 3 (by rfl) ⟨720173, by rfl⟩ : syracuseStep 3840925 = 1440347) (by norm_num)
theorem B5121233 : Blo 2275435 5121233 := bstep (se 2 (by rfl) ⟨1920462, by rfl⟩ : syracuseStep 5121233 = 3840925) B3840925
theorem B3414155 : Blo 2275435 3414155 := bstep (se 1 (by rfl) ⟨2560616, by rfl⟩ : syracuseStep 3414155 = 5121233) B5121233
theorem B2276103 : Blo 2275435 2276103 := bstep (se 1 (by rfl) ⟨1707077, by rfl⟩ : syracuseStep 2276103 = 3414155) B3414155
theorem B2560621 : Blo 2275435 2560621 := bbase (se 3 (by rfl) ⟨480116, by rfl⟩ : syracuseStep 2560621 = 960233) (by norm_num)
theorem B3414161 : Blo 2275435 3414161 := bstep (se 2 (by rfl) ⟨1280310, by rfl⟩ : syracuseStep 3414161 = 2560621) B2560621
theorem B2276107 : Blo 2275435 2276107 := bstep (se 1 (by rfl) ⟨1707080, by rfl⟩ : syracuseStep 2276107 = 3414161) B3414161
theorem B7681877 : Blo 2275435 7681877 := bbase (se 9 (by rfl) ⟨22505, by rfl⟩ : syracuseStep 7681877 = 45011) (by norm_num)
theorem B5121251 : Blo 2275435 5121251 := bstep (se 1 (by rfl) ⟨3840938, by rfl⟩ : syracuseStep 5121251 = 7681877) B7681877
theorem B3414167 : Blo 2275435 3414167 := bstep (se 1 (by rfl) ⟨2560625, by rfl⟩ : syracuseStep 3414167 = 5121251) B5121251
theorem B2276111 : Blo 2275435 2276111 := bstep (se 1 (by rfl) ⟨1707083, by rfl⟩ : syracuseStep 2276111 = 3414167) B3414167
theorem B3414173 : Blo 2275435 3414173 := bbase (se 3 (by rfl) ⟨640157, by rfl⟩ : syracuseStep 3414173 = 1280315) (by norm_num)
theorem B2276115 : Blo 2275435 2276115 := bstep (se 1 (by rfl) ⟨1707086, by rfl⟩ : syracuseStep 2276115 = 3414173) B3414173
theorem B5121269 : Blo 2275435 5121269 := bbase (se 5 (by rfl) ⟨240059, by rfl⟩ : syracuseStep 5121269 = 480119) (by norm_num)
theorem B3414179 : Blo 2275435 3414179 := bstep (se 1 (by rfl) ⟨2560634, by rfl⟩ : syracuseStep 3414179 = 5121269) B5121269
theorem B2276119 : Blo 2275435 2276119 := bstep (se 1 (by rfl) ⟨1707089, by rfl⟩ : syracuseStep 2276119 = 3414179) B3414179
theorem B2630989 : Blo 2275435 2630989 := bbase (se 3 (by rfl) ⟨493310, by rfl⟩ : syracuseStep 2630989 = 986621) (by norm_num)
theorem B3507985 : Blo 2275435 3507985 := bstep (se 2 (by rfl) ⟨1315494, by rfl⟩ : syracuseStep 3507985 = 2630989) B2630989
theorem B4677313 : Blo 2275435 4677313 := bstep (se 2 (by rfl) ⟨1753992, by rfl⟩ : syracuseStep 4677313 = 3507985) B3507985
theorem B6236417 : Blo 2275435 6236417 := bstep (se 2 (by rfl) ⟨2338656, by rfl⟩ : syracuseStep 6236417 = 4677313) B4677313
theorem B4157611 : Blo 2275435 4157611 := bstep (se 1 (by rfl) ⟨3118208, by rfl⟩ : syracuseStep 4157611 = 6236417) B6236417
theorem B22173925 : Blo 2275435 22173925 := bstep (se 4 (by rfl) ⟨2078805, by rfl⟩ : syracuseStep 22173925 = 4157611) B4157611
theorem B29565233 : Blo 2275435 29565233 := bstep (se 2 (by rfl) ⟨11086962, by rfl⟩ : syracuseStep 29565233 = 22173925) B22173925
theorem B19710155 : Blo 2275435 19710155 := bstep (se 1 (by rfl) ⟨14782616, by rfl⟩ : syracuseStep 19710155 = 29565233) B29565233
theorem B52560413 : Blo 2275435 52560413 := bstep (se 3 (by rfl) ⟨9855077, by rfl⟩ : syracuseStep 52560413 = 19710155) B19710155
theorem B35040275 : Blo 2275435 35040275 := bstep (se 1 (by rfl) ⟨26280206, by rfl⟩ : syracuseStep 35040275 = 52560413) B52560413
theorem B23360183 : Blo 2275435 23360183 := bstep (se 1 (by rfl) ⟨17520137, by rfl⟩ : syracuseStep 23360183 = 35040275) B35040275
theorem B15573455 : Blo 2275435 15573455 := bstep (se 1 (by rfl) ⟨11680091, by rfl⟩ : syracuseStep 15573455 = 23360183) B23360183
theorem B10382303 : Blo 2275435 10382303 := bstep (se 1 (by rfl) ⟨7786727, by rfl⟩ : syracuseStep 10382303 = 15573455) B15573455
theorem B6921535 : Blo 2275435 6921535 := bstep (se 1 (by rfl) ⟨5191151, by rfl⟩ : syracuseStep 6921535 = 10382303) B10382303
theorem B9228713 : Blo 2275435 9228713 := bstep (se 2 (by rfl) ⟨3460767, by rfl⟩ : syracuseStep 9228713 = 6921535) B6921535
theorem B24609901 : Blo 2275435 24609901 := bstep (se 3 (by rfl) ⟨4614356, by rfl⟩ : syracuseStep 24609901 = 9228713) B9228713
theorem B32813201 : Blo 2275435 32813201 := bstep (se 2 (by rfl) ⟨12304950, by rfl⟩ : syracuseStep 32813201 = 24609901) B24609901
theorem B21875467 : Blo 2275435 21875467 := bstep (se 1 (by rfl) ⟨16406600, by rfl⟩ : syracuseStep 21875467 = 32813201) B32813201
theorem B29167289 : Blo 2275435 29167289 := bstep (se 2 (by rfl) ⟨10937733, by rfl⟩ : syracuseStep 29167289 = 21875467) B21875467
theorem B19444859 : Blo 2275435 19444859 := bstep (se 1 (by rfl) ⟨14583644, by rfl⟩ : syracuseStep 19444859 = 29167289) B29167289
theorem B12963239 : Blo 2275435 12963239 := bstep (se 1 (by rfl) ⟨9722429, by rfl⟩ : syracuseStep 12963239 = 19444859) B19444859
theorem B8642159 : Blo 2275435 8642159 := bstep (se 1 (by rfl) ⟨6481619, by rfl⟩ : syracuseStep 8642159 = 12963239) B12963239
theorem B5761439 : Blo 2275435 5761439 := bstep (se 1 (by rfl) ⟨4321079, by rfl⟩ : syracuseStep 5761439 = 8642159) B8642159
theorem B3840959 : Blo 2275435 3840959 := bstep (se 1 (by rfl) ⟨2880719, by rfl⟩ : syracuseStep 3840959 = 5761439) B5761439
theorem B2560639 : Blo 2275435 2560639 := bstep (se 1 (by rfl) ⟨1920479, by rfl⟩ : syracuseStep 2560639 = 3840959) B3840959
theorem B3414185 : Blo 2275435 3414185 := bstep (se 2 (by rfl) ⟨1280319, by rfl⟩ : syracuseStep 3414185 = 2560639) B2560639
theorem B2276123 : Blo 2275435 2276123 := bstep (se 1 (by rfl) ⟨1707092, by rfl⟩ : syracuseStep 2276123 = 3414185) B3414185
theorem B4614365 : Blo 2275435 4614365 := bbase (se 3 (by rfl) ⟨865193, by rfl⟩ : syracuseStep 4614365 = 1730387) (by norm_num)
theorem B12304973 : Blo 2275435 12304973 := bstep (se 3 (by rfl) ⟨2307182, by rfl⟩ : syracuseStep 12304973 = 4614365) B4614365
theorem B8203315 : Blo 2275435 8203315 := bstep (se 1 (by rfl) ⟨6152486, by rfl⟩ : syracuseStep 8203315 = 12304973) B12304973
theorem B10937753 : Blo 2275435 10937753 := bstep (se 2 (by rfl) ⟨4101657, by rfl⟩ : syracuseStep 10937753 = 8203315) B8203315
theorem B7291835 : Blo 2275435 7291835 := bstep (se 1 (by rfl) ⟨5468876, by rfl⟩ : syracuseStep 7291835 = 10937753) B10937753
theorem B4861223 : Blo 2275435 4861223 := bstep (se 1 (by rfl) ⟨3645917, by rfl⟩ : syracuseStep 4861223 = 7291835) B7291835
theorem B3240815 : Blo 2275435 3240815 := bstep (se 1 (by rfl) ⟨2430611, by rfl⟩ : syracuseStep 3240815 = 4861223) B4861223
theorem B8642173 : Blo 2275435 8642173 := bstep (se 3 (by rfl) ⟨1620407, by rfl⟩ : syracuseStep 8642173 = 3240815) B3240815
theorem B11522897 : Blo 2275435 11522897 := bstep (se 2 (by rfl) ⟨4321086, by rfl⟩ : syracuseStep 11522897 = 8642173) B8642173
theorem B7681931 : Blo 2275435 7681931 := bstep (se 1 (by rfl) ⟨5761448, by rfl⟩ : syracuseStep 7681931 = 11522897) B11522897
theorem B5121287 : Blo 2275435 5121287 := bstep (se 1 (by rfl) ⟨3840965, by rfl⟩ : syracuseStep 5121287 = 7681931) B7681931
theorem B3414191 : Blo 2275435 3414191 := bstep (se 1 (by rfl) ⟨2560643, by rfl⟩ : syracuseStep 3414191 = 5121287) B5121287
theorem B2276127 : Blo 2275435 2276127 := bstep (se 1 (by rfl) ⟨1707095, by rfl⟩ : syracuseStep 2276127 = 3414191) B3414191
theorem B3414197 : Blo 2275435 3414197 := bbase (se 5 (by rfl) ⟨160040, by rfl⟩ : syracuseStep 3414197 = 320081) (by norm_num)
theorem B2276131 : Blo 2275435 2276131 := bstep (se 1 (by rfl) ⟨1707098, by rfl⟩ : syracuseStep 2276131 = 3414197) B3414197
theorem B5761469 : Blo 2275435 5761469 := bbase (se 3 (by rfl) ⟨1080275, by rfl⟩ : syracuseStep 5761469 = 2160551) (by norm_num)
theorem B3840979 : Blo 2275435 3840979 := bstep (se 1 (by rfl) ⟨2880734, by rfl⟩ : syracuseStep 3840979 = 5761469) B5761469
theorem B5121305 : Blo 2275435 5121305 := bstep (se 2 (by rfl) ⟨1920489, by rfl⟩ : syracuseStep 5121305 = 3840979) B3840979
theorem B3414203 : Blo 2275435 3414203 := bstep (se 1 (by rfl) ⟨2560652, by rfl⟩ : syracuseStep 3414203 = 5121305) B5121305
theorem B2276135 : Blo 2275435 2276135 := bstep (se 1 (by rfl) ⟨1707101, by rfl⟩ : syracuseStep 2276135 = 3414203) B3414203
theorem B2560657 : Blo 2275435 2560657 := bbase (se 2 (by rfl) ⟨960246, by rfl⟩ : syracuseStep 2560657 = 1920493) (by norm_num)
theorem B3414209 : Blo 2275435 3414209 := bstep (se 2 (by rfl) ⟨1280328, by rfl⟩ : syracuseStep 3414209 = 2560657) B2560657
theorem B2276139 : Blo 2275435 2276139 := bstep (se 1 (by rfl) ⟨1707104, by rfl⟩ : syracuseStep 2276139 = 3414209) B3414209
theorem B4321117 : Blo 2275435 4321117 := bbase (se 3 (by rfl) ⟨810209, by rfl⟩ : syracuseStep 4321117 = 1620419) (by norm_num)
theorem B5761489 : Blo 2275435 5761489 := bstep (se 2 (by rfl) ⟨2160558, by rfl⟩ : syracuseStep 5761489 = 4321117) B4321117
theorem B7681985 : Blo 2275435 7681985 := bstep (se 2 (by rfl) ⟨2880744, by rfl⟩ : syracuseStep 7681985 = 5761489) B5761489
theorem B5121323 : Blo 2275435 5121323 := bstep (se 1 (by rfl) ⟨3840992, by rfl⟩ : syracuseStep 5121323 = 7681985) B7681985
theorem B3414215 : Blo 2275435 3414215 := bstep (se 1 (by rfl) ⟨2560661, by rfl⟩ : syracuseStep 3414215 = 5121323) B5121323
theorem B2276143 : Blo 2275435 2276143 := bstep (se 1 (by rfl) ⟨1707107, by rfl⟩ : syracuseStep 2276143 = 3414215) B3414215
theorem B3414221 : Blo 2275435 3414221 := bbase (se 3 (by rfl) ⟨640166, by rfl⟩ : syracuseStep 3414221 = 1280333) (by norm_num)
theorem B2276147 : Blo 2275435 2276147 := bstep (se 1 (by rfl) ⟨1707110, by rfl⟩ : syracuseStep 2276147 = 3414221) B3414221
theorem B5121341 : Blo 2275435 5121341 := bbase (se 3 (by rfl) ⟨960251, by rfl⟩ : syracuseStep 5121341 = 1920503) (by norm_num)
theorem B3414227 : Blo 2275435 3414227 := bstep (se 1 (by rfl) ⟨2560670, by rfl⟩ : syracuseStep 3414227 = 5121341) B5121341
theorem B2276151 : Blo 2275435 2276151 := bstep (se 1 (by rfl) ⟨1707113, by rfl⟩ : syracuseStep 2276151 = 3414227) B3414227
theorem B3841013 : Blo 2275435 3841013 := bbase (se 5 (by rfl) ⟨180047, by rfl⟩ : syracuseStep 3841013 = 360095) (by norm_num)
theorem B2560675 : Blo 2275435 2560675 := bstep (se 1 (by rfl) ⟨1920506, by rfl⟩ : syracuseStep 2560675 = 3841013) B3841013
theorem B3414233 : Blo 2275435 3414233 := bstep (se 2 (by rfl) ⟨1280337, by rfl⟩ : syracuseStep 3414233 = 2560675) B2560675
theorem B2276155 : Blo 2275435 2276155 := bstep (se 1 (by rfl) ⟨1707116, by rfl⟩ : syracuseStep 2276155 = 3414233) B3414233
theorem B7786853 : Blo 2275435 7786853 := bbase (se 4 (by rfl) ⟨730017, by rfl⟩ : syracuseStep 7786853 = 1460035) (by norm_num)
theorem B5191235 : Blo 2275435 5191235 := bstep (se 1 (by rfl) ⟨3893426, by rfl⟩ : syracuseStep 5191235 = 7786853) B7786853
theorem B3460823 : Blo 2275435 3460823 := bstep (se 1 (by rfl) ⟨2595617, by rfl⟩ : syracuseStep 3460823 = 5191235) B5191235
theorem B2307215 : Blo 2275435 2307215 := bstep (se 1 (by rfl) ⟨1730411, by rfl⟩ : syracuseStep 2307215 = 3460823) B3460823
theorem B6152573 : Blo 2275435 6152573 := bstep (se 3 (by rfl) ⟨1153607, by rfl⟩ : syracuseStep 6152573 = 2307215) B2307215
theorem B4101715 : Blo 2275435 4101715 := bstep (se 1 (by rfl) ⟨3076286, by rfl⟩ : syracuseStep 4101715 = 6152573) B6152573
theorem B5468953 : Blo 2275435 5468953 := bstep (se 2 (by rfl) ⟨2050857, by rfl⟩ : syracuseStep 5468953 = 4101715) B4101715
theorem B7291937 : Blo 2275435 7291937 := bstep (se 2 (by rfl) ⟨2734476, by rfl⟩ : syracuseStep 7291937 = 5468953) B5468953
theorem B4861291 : Blo 2275435 4861291 := bstep (se 1 (by rfl) ⟨3645968, by rfl⟩ : syracuseStep 4861291 = 7291937) B7291937
theorem B6481721 : Blo 2275435 6481721 := bstep (se 2 (by rfl) ⟨2430645, by rfl⟩ : syracuseStep 6481721 = 4861291) B4861291
theorem B17284589 : Blo 2275435 17284589 := bstep (se 3 (by rfl) ⟨3240860, by rfl⟩ : syracuseStep 17284589 = 6481721) B6481721
theorem B11523059 : Blo 2275435 11523059 := bstep (se 1 (by rfl) ⟨8642294, by rfl⟩ : syracuseStep 11523059 = 17284589) B17284589
theorem B7682039 : Blo 2275435 7682039 := bstep (se 1 (by rfl) ⟨5761529, by rfl⟩ : syracuseStep 7682039 = 11523059) B11523059
theorem B5121359 : Blo 2275435 5121359 := bstep (se 1 (by rfl) ⟨3841019, by rfl⟩ : syracuseStep 5121359 = 7682039) B7682039
theorem B3414239 : Blo 2275435 3414239 := bstep (se 1 (by rfl) ⟨2560679, by rfl⟩ : syracuseStep 3414239 = 5121359) B5121359
theorem B2276159 : Blo 2275435 2276159 := bstep (se 1 (by rfl) ⟨1707119, by rfl⟩ : syracuseStep 2276159 = 3414239) B3414239
theorem B3414245 : Blo 2275435 3414245 := bbase (se 4 (by rfl) ⟨320085, by rfl⟩ : syracuseStep 3414245 = 640171) (by norm_num)
theorem B2276163 : Blo 2275435 2276163 := bstep (se 1 (by rfl) ⟨1707122, by rfl⟩ : syracuseStep 2276163 = 3414245) B3414245
theorem B4861309 : Blo 2275435 4861309 := bbase (se 3 (by rfl) ⟨911495, by rfl⟩ : syracuseStep 4861309 = 1822991) (by norm_num)
theorem B6481745 : Blo 2275435 6481745 := bstep (se 2 (by rfl) ⟨2430654, by rfl⟩ : syracuseStep 6481745 = 4861309) B4861309
theorem B4321163 : Blo 2275435 4321163 := bstep (se 1 (by rfl) ⟨3240872, by rfl⟩ : syracuseStep 4321163 = 6481745) B6481745
theorem B2880775 : Blo 2275435 2880775 := bstep (se 1 (by rfl) ⟨2160581, by rfl⟩ : syracuseStep 2880775 = 4321163) B4321163
theorem B3841033 : Blo 2275435 3841033 := bstep (se 2 (by rfl) ⟨1440387, by rfl⟩ : syracuseStep 3841033 = 2880775) B2880775
theorem B5121377 : Blo 2275435 5121377 := bstep (se 2 (by rfl) ⟨1920516, by rfl⟩ : syracuseStep 5121377 = 3841033) B3841033
theorem B3414251 : Blo 2275435 3414251 := bstep (se 1 (by rfl) ⟨2560688, by rfl⟩ : syracuseStep 3414251 = 5121377) B5121377
theorem B2276167 : Blo 2275435 2276167 := bstep (se 1 (by rfl) ⟨1707125, by rfl⟩ : syracuseStep 2276167 = 3414251) B3414251
theorem B2560693 : Blo 2275435 2560693 := bbase (se 5 (by rfl) ⟨120032, by rfl⟩ : syracuseStep 2560693 = 240065) (by norm_num)
theorem B3414257 : Blo 2275435 3414257 := bstep (se 2 (by rfl) ⟨1280346, by rfl⟩ : syracuseStep 3414257 = 2560693) B2560693
theorem B2276171 : Blo 2275435 2276171 := bstep (se 1 (by rfl) ⟨1707128, by rfl⟩ : syracuseStep 2276171 = 3414257) B3414257
theorem B2880785 : Blo 2275435 2880785 := bbase (se 2 (by rfl) ⟨1080294, by rfl⟩ : syracuseStep 2880785 = 2160589) (by norm_num)
theorem B7682093 : Blo 2275435 7682093 := bstep (se 3 (by rfl) ⟨1440392, by rfl⟩ : syracuseStep 7682093 = 2880785) B2880785
theorem B5121395 : Blo 2275435 5121395 := bstep (se 1 (by rfl) ⟨3841046, by rfl⟩ : syracuseStep 5121395 = 7682093) B7682093
theorem B3414263 : Blo 2275435 3414263 := bstep (se 1 (by rfl) ⟨2560697, by rfl⟩ : syracuseStep 3414263 = 5121395) B5121395
theorem B2276175 : Blo 2275435 2276175 := bstep (se 1 (by rfl) ⟨1707131, by rfl⟩ : syracuseStep 2276175 = 3414263) B3414263
theorem B3414269 : Blo 2275435 3414269 := bbase (se 3 (by rfl) ⟨640175, by rfl⟩ : syracuseStep 3414269 = 1280351) (by norm_num)
theorem B2276179 : Blo 2275435 2276179 := bstep (se 1 (by rfl) ⟨1707134, by rfl⟩ : syracuseStep 2276179 = 3414269) B3414269
theorem B5121413 : Blo 2275435 5121413 := bbase (se 4 (by rfl) ⟨480132, by rfl⟩ : syracuseStep 5121413 = 960265) (by norm_num)
theorem B3414275 : Blo 2275435 3414275 := bstep (se 1 (by rfl) ⟨2560706, by rfl⟩ : syracuseStep 3414275 = 5121413) B5121413
theorem B2276183 : Blo 2275435 2276183 := bstep (se 1 (by rfl) ⟨1707137, by rfl⟩ : syracuseStep 2276183 = 3414275) B3414275
theorem B3240901 : Blo 2275435 3240901 := bbase (se 4 (by rfl) ⟨303834, by rfl⟩ : syracuseStep 3240901 = 607669) (by norm_num)
theorem B4321201 : Blo 2275435 4321201 := bstep (se 2 (by rfl) ⟨1620450, by rfl⟩ : syracuseStep 4321201 = 3240901) B3240901
theorem B5761601 : Blo 2275435 5761601 := bstep (se 2 (by rfl) ⟨2160600, by rfl⟩ : syracuseStep 5761601 = 4321201) B4321201
theorem B3841067 : Blo 2275435 3841067 := bstep (se 1 (by rfl) ⟨2880800, by rfl⟩ : syracuseStep 3841067 = 5761601) B5761601
theorem B2560711 : Blo 2275435 2560711 := bstep (se 1 (by rfl) ⟨1920533, by rfl⟩ : syracuseStep 2560711 = 3841067) B3841067
theorem B3414281 : Blo 2275435 3414281 := bstep (se 2 (by rfl) ⟨1280355, by rfl⟩ : syracuseStep 3414281 = 2560711) B2560711
theorem B2276187 : Blo 2275435 2276187 := bstep (se 1 (by rfl) ⟨1707140, by rfl⟩ : syracuseStep 2276187 = 3414281) B3414281
theorem B11523221 : Blo 2275435 11523221 := bbase (se 6 (by rfl) ⟨270075, by rfl⟩ : syracuseStep 11523221 = 540151) (by norm_num)
theorem B7682147 : Blo 2275435 7682147 := bstep (se 1 (by rfl) ⟨5761610, by rfl⟩ : syracuseStep 7682147 = 11523221) B11523221
theorem B5121431 : Blo 2275435 5121431 := bstep (se 1 (by rfl) ⟨3841073, by rfl⟩ : syracuseStep 5121431 = 7682147) B7682147
theorem B3414287 : Blo 2275435 3414287 := bstep (se 1 (by rfl) ⟨2560715, by rfl⟩ : syracuseStep 3414287 = 5121431) B5121431
theorem B2276191 : Blo 2275435 2276191 := bstep (se 1 (by rfl) ⟨1707143, by rfl⟩ : syracuseStep 2276191 = 3414287) B3414287
theorem B3414293 : Blo 2275435 3414293 := bbase (se 6 (by rfl) ⟨80022, by rfl⟩ : syracuseStep 3414293 = 160045) (by norm_num)
theorem B2276195 : Blo 2275435 2276195 := bstep (se 1 (by rfl) ⟨1707146, by rfl⟩ : syracuseStep 2276195 = 3414293) B3414293
theorem B17520725 : Blo 2275435 17520725 := bbase (se 8 (by rfl) ⟨102660, by rfl⟩ : syracuseStep 17520725 = 205321) (by norm_num)
theorem B11680483 : Blo 2275435 11680483 := bstep (se 1 (by rfl) ⟨8760362, by rfl⟩ : syracuseStep 11680483 = 17520725) B17520725
theorem B15573977 : Blo 2275435 15573977 := bstep (se 2 (by rfl) ⟨5840241, by rfl⟩ : syracuseStep 15573977 = 11680483) B11680483
theorem B10382651 : Blo 2275435 10382651 := bstep (se 1 (by rfl) ⟨7786988, by rfl⟩ : syracuseStep 10382651 = 15573977) B15573977
theorem B6921767 : Blo 2275435 6921767 := bstep (se 1 (by rfl) ⟨5191325, by rfl⟩ : syracuseStep 6921767 = 10382651) B10382651
theorem B4614511 : Blo 2275435 4614511 := bstep (se 1 (by rfl) ⟨3460883, by rfl⟩ : syracuseStep 4614511 = 6921767) B6921767
theorem B6152681 : Blo 2275435 6152681 := bstep (se 2 (by rfl) ⟨2307255, by rfl⟩ : syracuseStep 6152681 = 4614511) B4614511
theorem B4101787 : Blo 2275435 4101787 := bstep (se 1 (by rfl) ⟨3076340, by rfl⟩ : syracuseStep 4101787 = 6152681) B6152681
theorem B5469049 : Blo 2275435 5469049 := bstep (se 2 (by rfl) ⟨2050893, by rfl⟩ : syracuseStep 5469049 = 4101787) B4101787
theorem B29168261 : Blo 2275435 29168261 := bstep (se 4 (by rfl) ⟨2734524, by rfl⟩ : syracuseStep 29168261 = 5469049) B5469049
theorem B19445507 : Blo 2275435 19445507 := bstep (se 1 (by rfl) ⟨14584130, by rfl⟩ : syracuseStep 19445507 = 29168261) B29168261
theorem B12963671 : Blo 2275435 12963671 := bstep (se 1 (by rfl) ⟨9722753, by rfl⟩ : syracuseStep 12963671 = 19445507) B19445507
theorem B8642447 : Blo 2275435 8642447 := bstep (se 1 (by rfl) ⟨6481835, by rfl⟩ : syracuseStep 8642447 = 12963671) B12963671
theorem B5761631 : Blo 2275435 5761631 := bstep (se 1 (by rfl) ⟨4321223, by rfl⟩ : syracuseStep 5761631 = 8642447) B8642447
theorem B3841087 : Blo 2275435 3841087 := bstep (se 1 (by rfl) ⟨2880815, by rfl⟩ : syracuseStep 3841087 = 5761631) B5761631
theorem B5121449 : Blo 2275435 5121449 := bstep (se 2 (by rfl) ⟨1920543, by rfl⟩ : syracuseStep 5121449 = 3841087) B3841087
theorem B3414299 : Blo 2275435 3414299 := bstep (se 1 (by rfl) ⟨2560724, by rfl⟩ : syracuseStep 3414299 = 5121449) B5121449
theorem B2276199 : Blo 2275435 2276199 := bstep (se 1 (by rfl) ⟨1707149, by rfl⟩ : syracuseStep 2276199 = 3414299) B3414299
theorem B2560729 : Blo 2275435 2560729 := bbase (se 2 (by rfl) ⟨960273, by rfl⟩ : syracuseStep 2560729 = 1920547) (by norm_num)
theorem B3414305 : Blo 2275435 3414305 := bstep (se 2 (by rfl) ⟨1280364, by rfl⟩ : syracuseStep 3414305 = 2560729) B2560729
theorem B2276203 : Blo 2275435 2276203 := bstep (se 1 (by rfl) ⟨1707152, by rfl⟩ : syracuseStep 2276203 = 3414305) B3414305
theorem B2430697 : Blo 2275435 2430697 := bbase (se 2 (by rfl) ⟨911511, by rfl⟩ : syracuseStep 2430697 = 1823023) (by norm_num)
theorem B3240929 : Blo 2275435 3240929 := bstep (se 2 (by rfl) ⟨1215348, by rfl⟩ : syracuseStep 3240929 = 2430697) B2430697
theorem B8642477 : Blo 2275435 8642477 := bstep (se 3 (by rfl) ⟨1620464, by rfl⟩ : syracuseStep 8642477 = 3240929) B3240929
theorem B5761651 : Blo 2275435 5761651 := bstep (se 1 (by rfl) ⟨4321238, by rfl⟩ : syracuseStep 5761651 = 8642477) B8642477
theorem B7682201 : Blo 2275435 7682201 := bstep (se 2 (by rfl) ⟨2880825, by rfl⟩ : syracuseStep 7682201 = 5761651) B5761651
theorem B5121467 : Blo 2275435 5121467 := bstep (se 1 (by rfl) ⟨3841100, by rfl⟩ : syracuseStep 5121467 = 7682201) B7682201
theorem B3414311 : Blo 2275435 3414311 := bstep (se 1 (by rfl) ⟨2560733, by rfl⟩ : syracuseStep 3414311 = 5121467) B5121467
theorem B2276207 : Blo 2275435 2276207 := bstep (se 1 (by rfl) ⟨1707155, by rfl⟩ : syracuseStep 2276207 = 3414311) B3414311
theorem B3414317 : Blo 2275435 3414317 := bbase (se 3 (by rfl) ⟨640184, by rfl⟩ : syracuseStep 3414317 = 1280369) (by norm_num)
theorem B2276211 : Blo 2275435 2276211 := bstep (se 1 (by rfl) ⟨1707158, by rfl⟩ : syracuseStep 2276211 = 3414317) B3414317
theorem B5121485 : Blo 2275435 5121485 := bbase (se 3 (by rfl) ⟨960278, by rfl⟩ : syracuseStep 5121485 = 1920557) (by norm_num)
theorem B3414323 : Blo 2275435 3414323 := bstep (se 1 (by rfl) ⟨2560742, by rfl⟩ : syracuseStep 3414323 = 5121485) B5121485
theorem B2276215 : Blo 2275435 2276215 := bstep (se 1 (by rfl) ⟨1707161, by rfl⟩ : syracuseStep 2276215 = 3414323) B3414323
theorem B2880841 : Blo 2275435 2880841 := bbase (se 2 (by rfl) ⟨1080315, by rfl⟩ : syracuseStep 2880841 = 2160631) (by norm_num)
theorem B3841121 : Blo 2275435 3841121 := bstep (se 2 (by rfl) ⟨1440420, by rfl⟩ : syracuseStep 3841121 = 2880841) B2880841
theorem B2560747 : Blo 2275435 2560747 := bstep (se 1 (by rfl) ⟨1920560, by rfl⟩ : syracuseStep 2560747 = 3841121) B3841121
theorem B3414329 : Blo 2275435 3414329 := bstep (se 2 (by rfl) ⟨1280373, by rfl⟩ : syracuseStep 3414329 = 2560747) B2560747
theorem B2276219 : Blo 2275435 2276219 := bstep (se 1 (by rfl) ⟨1707164, by rfl⟩ : syracuseStep 2276219 = 3414329) B3414329
theorem B6570341 : Blo 2275435 6570341 := bbase (se 4 (by rfl) ⟨615969, by rfl⟩ : syracuseStep 6570341 = 1231939) (by norm_num)
theorem B4380227 : Blo 2275435 4380227 := bstep (se 1 (by rfl) ⟨3285170, by rfl⟩ : syracuseStep 4380227 = 6570341) B6570341
theorem B2920151 : Blo 2275435 2920151 := bstep (se 1 (by rfl) ⟨2190113, by rfl⟩ : syracuseStep 2920151 = 4380227) B4380227
theorem B7787069 : Blo 2275435 7787069 := bstep (se 3 (by rfl) ⟨1460075, by rfl⟩ : syracuseStep 7787069 = 2920151) B2920151
theorem B5191379 : Blo 2275435 5191379 := bstep (se 1 (by rfl) ⟨3893534, by rfl⟩ : syracuseStep 5191379 = 7787069) B7787069
theorem B3460919 : Blo 2275435 3460919 := bstep (se 1 (by rfl) ⟨2595689, by rfl⟩ : syracuseStep 3460919 = 5191379) B5191379
theorem B36916469 : Blo 2275435 36916469 := bstep (se 5 (by rfl) ⟨1730459, by rfl⟩ : syracuseStep 36916469 = 3460919) B3460919
theorem B24610979 : Blo 2275435 24610979 := bstep (se 1 (by rfl) ⟨18458234, by rfl⟩ : syracuseStep 24610979 = 36916469) B36916469
theorem B16407319 : Blo 2275435 16407319 := bstep (se 1 (by rfl) ⟨12305489, by rfl⟩ : syracuseStep 16407319 = 24610979) B24610979
theorem B21876425 : Blo 2275435 21876425 := bstep (se 2 (by rfl) ⟨8203659, by rfl⟩ : syracuseStep 21876425 = 16407319) B16407319
theorem B14584283 : Blo 2275435 14584283 := bstep (se 1 (by rfl) ⟨10938212, by rfl⟩ : syracuseStep 14584283 = 21876425) B21876425
theorem B9722855 : Blo 2275435 9722855 := bstep (se 1 (by rfl) ⟨7292141, by rfl⟩ : syracuseStep 9722855 = 14584283) B14584283
theorem B25927613 : Blo 2275435 25927613 := bstep (se 3 (by rfl) ⟨4861427, by rfl⟩ : syracuseStep 25927613 = 9722855) B9722855
theorem B17285075 : Blo 2275435 17285075 := bstep (se 1 (by rfl) ⟨12963806, by rfl⟩ : syracuseStep 17285075 = 25927613) B25927613
theorem B11523383 : Blo 2275435 11523383 := bstep (se 1 (by rfl) ⟨8642537, by rfl⟩ : syracuseStep 11523383 = 17285075) B17285075
theorem B7682255 : Blo 2275435 7682255 := bstep (se 1 (by rfl) ⟨5761691, by rfl⟩ : syracuseStep 7682255 = 11523383) B11523383
theorem B5121503 : Blo 2275435 5121503 := bstep (se 1 (by rfl) ⟨3841127, by rfl⟩ : syracuseStep 5121503 = 7682255) B7682255
theorem B3414335 : Blo 2275435 3414335 := bstep (se 1 (by rfl) ⟨2560751, by rfl⟩ : syracuseStep 3414335 = 5121503) B5121503
theorem B2276223 : Blo 2275435 2276223 := bstep (se 1 (by rfl) ⟨1707167, by rfl⟩ : syracuseStep 2276223 = 3414335) B3414335
theorem B3414341 : Blo 2275435 3414341 := bbase (se 4 (by rfl) ⟨320094, by rfl⟩ : syracuseStep 3414341 = 640189) (by norm_num)
theorem B2276227 : Blo 2275435 2276227 := bstep (se 1 (by rfl) ⟨1707170, by rfl⟩ : syracuseStep 2276227 = 3414341) B3414341
theorem B3841141 : Blo 2275435 3841141 := bbase (se 5 (by rfl) ⟨180053, by rfl⟩ : syracuseStep 3841141 = 360107) (by norm_num)
theorem B5121521 : Blo 2275435 5121521 := bstep (se 2 (by rfl) ⟨1920570, by rfl⟩ : syracuseStep 5121521 = 3841141) B3841141
theorem B3414347 : Blo 2275435 3414347 := bstep (se 1 (by rfl) ⟨2560760, by rfl⟩ : syracuseStep 3414347 = 5121521) B5121521
theorem B2276231 : Blo 2275435 2276231 := bstep (se 1 (by rfl) ⟨1707173, by rfl⟩ : syracuseStep 2276231 = 3414347) B3414347
theorem B2560765 : Blo 2275435 2560765 := bbase (se 3 (by rfl) ⟨480143, by rfl⟩ : syracuseStep 2560765 = 960287) (by norm_num)
theorem B3414353 : Blo 2275435 3414353 := bstep (se 2 (by rfl) ⟨1280382, by rfl⟩ : syracuseStep 3414353 = 2560765) B2560765
theorem B2276235 : Blo 2275435 2276235 := bstep (se 1 (by rfl) ⟨1707176, by rfl⟩ : syracuseStep 2276235 = 3414353) B3414353
theorem B7682309 : Blo 2275435 7682309 := bbase (se 4 (by rfl) ⟨720216, by rfl⟩ : syracuseStep 7682309 = 1440433) (by norm_num)
theorem B5121539 : Blo 2275435 5121539 := bstep (se 1 (by rfl) ⟨3841154, by rfl⟩ : syracuseStep 5121539 = 7682309) B7682309
theorem B3414359 : Blo 2275435 3414359 := bstep (se 1 (by rfl) ⟨2560769, by rfl⟩ : syracuseStep 3414359 = 5121539) B5121539
theorem B2276239 : Blo 2275435 2276239 := bstep (se 1 (by rfl) ⟨1707179, by rfl⟩ : syracuseStep 2276239 = 3414359) B3414359
theorem B3414365 : Blo 2275435 3414365 := bbase (se 3 (by rfl) ⟨640193, by rfl⟩ : syracuseStep 3414365 = 1280387) (by norm_num)
theorem B2276243 : Blo 2275435 2276243 := bstep (se 1 (by rfl) ⟨1707182, by rfl⟩ : syracuseStep 2276243 = 3414365) B3414365
theorem B5121557 : Blo 2275435 5121557 := bbase (se 6 (by rfl) ⟨120036, by rfl⟩ : syracuseStep 5121557 = 240073) (by norm_num)
theorem B3414371 : Blo 2275435 3414371 := bstep (se 1 (by rfl) ⟨2560778, by rfl⟩ : syracuseStep 3414371 = 5121557) B5121557
theorem B2276247 : Blo 2275435 2276247 := bstep (se 1 (by rfl) ⟨1707185, by rfl⟩ : syracuseStep 2276247 = 3414371) B3414371
theorem B8642645 : Blo 2275435 8642645 := bbase (se 8 (by rfl) ⟨50640, by rfl⟩ : syracuseStep 8642645 = 101281) (by norm_num)
theorem B5761763 : Blo 2275435 5761763 := bstep (se 1 (by rfl) ⟨4321322, by rfl⟩ : syracuseStep 5761763 = 8642645) B8642645
theorem B3841175 : Blo 2275435 3841175 := bstep (se 1 (by rfl) ⟨2880881, by rfl⟩ : syracuseStep 3841175 = 5761763) B5761763
theorem B2560783 : Blo 2275435 2560783 := bstep (se 1 (by rfl) ⟨1920587, by rfl⟩ : syracuseStep 2560783 = 3841175) B3841175
theorem B3414377 : Blo 2275435 3414377 := bstep (se 2 (by rfl) ⟨1280391, by rfl⟩ : syracuseStep 3414377 = 2560783) B2560783
theorem B2276251 : Blo 2275435 2276251 := bstep (se 1 (by rfl) ⟨1707188, by rfl⟩ : syracuseStep 2276251 = 3414377) B3414377
theorem B12963989 : Blo 2275435 12963989 := bbase (se 6 (by rfl) ⟨303843, by rfl⟩ : syracuseStep 12963989 = 607687) (by norm_num)
theorem B8642659 : Blo 2275435 8642659 := bstep (se 1 (by rfl) ⟨6481994, by rfl⟩ : syracuseStep 8642659 = 12963989) B12963989
theorem B11523545 : Blo 2275435 11523545 := bstep (se 2 (by rfl) ⟨4321329, by rfl⟩ : syracuseStep 11523545 = 8642659) B8642659
theorem B7682363 : Blo 2275435 7682363 := bstep (se 1 (by rfl) ⟨5761772, by rfl⟩ : syracuseStep 7682363 = 11523545) B11523545
theorem B5121575 : Blo 2275435 5121575 := bstep (se 1 (by rfl) ⟨3841181, by rfl⟩ : syracuseStep 5121575 = 7682363) B7682363
theorem B3414383 : Blo 2275435 3414383 := bstep (se 1 (by rfl) ⟨2560787, by rfl⟩ : syracuseStep 3414383 = 5121575) B5121575
theorem B2276255 : Blo 2275435 2276255 := bstep (se 1 (by rfl) ⟨1707191, by rfl⟩ : syracuseStep 2276255 = 3414383) B3414383
theorem B3414389 : Blo 2275435 3414389 := bbase (se 5 (by rfl) ⟨160049, by rfl⟩ : syracuseStep 3414389 = 320099) (by norm_num)
theorem B2276259 : Blo 2275435 2276259 := bstep (se 1 (by rfl) ⟨1707194, by rfl⟩ : syracuseStep 2276259 = 3414389) B3414389
theorem B2430757 : Blo 2275435 2430757 := bbase (se 4 (by rfl) ⟨227883, by rfl⟩ : syracuseStep 2430757 = 455767) (by norm_num)
theorem B3241009 : Blo 2275435 3241009 := bstep (se 2 (by rfl) ⟨1215378, by rfl⟩ : syracuseStep 3241009 = 2430757) B2430757
theorem B4321345 : Blo 2275435 4321345 := bstep (se 2 (by rfl) ⟨1620504, by rfl⟩ : syracuseStep 4321345 = 3241009) B3241009
theorem B5761793 : Blo 2275435 5761793 := bstep (se 2 (by rfl) ⟨2160672, by rfl⟩ : syracuseStep 5761793 = 4321345) B4321345
theorem B3841195 : Blo 2275435 3841195 := bstep (se 1 (by rfl) ⟨2880896, by rfl⟩ : syracuseStep 3841195 = 5761793) B5761793
theorem B5121593 : Blo 2275435 5121593 := bstep (se 2 (by rfl) ⟨1920597, by rfl⟩ : syracuseStep 5121593 = 3841195) B3841195
theorem B3414395 : Blo 2275435 3414395 := bstep (se 1 (by rfl) ⟨2560796, by rfl⟩ : syracuseStep 3414395 = 5121593) B5121593
theorem B2276263 : Blo 2275435 2276263 := bstep (se 1 (by rfl) ⟨1707197, by rfl⟩ : syracuseStep 2276263 = 3414395) B3414395
theorem B2560801 : Blo 2275435 2560801 := bbase (se 2 (by rfl) ⟨960300, by rfl⟩ : syracuseStep 2560801 = 1920601) (by norm_num)
theorem B3414401 : Blo 2275435 3414401 := bstep (se 2 (by rfl) ⟨1280400, by rfl⟩ : syracuseStep 3414401 = 2560801) B2560801
theorem B2276267 : Blo 2275435 2276267 := bstep (se 1 (by rfl) ⟨1707200, by rfl⟩ : syracuseStep 2276267 = 3414401) B3414401
theorem B5761813 : Blo 2275435 5761813 := bbase (se 6 (by rfl) ⟨135042, by rfl⟩ : syracuseStep 5761813 = 270085) (by norm_num)
theorem B7682417 : Blo 2275435 7682417 := bstep (se 2 (by rfl) ⟨2880906, by rfl⟩ : syracuseStep 7682417 = 5761813) B5761813
theorem B5121611 : Blo 2275435 5121611 := bstep (se 1 (by rfl) ⟨3841208, by rfl⟩ : syracuseStep 5121611 = 7682417) B7682417
theorem B3414407 : Blo 2275435 3414407 := bstep (se 1 (by rfl) ⟨2560805, by rfl⟩ : syracuseStep 3414407 = 5121611) B5121611
theorem B2276271 : Blo 2275435 2276271 := bstep (se 1 (by rfl) ⟨1707203, by rfl⟩ : syracuseStep 2276271 = 3414407) B3414407
theorem B3414413 : Blo 2275435 3414413 := bbase (se 3 (by rfl) ⟨640202, by rfl⟩ : syracuseStep 3414413 = 1280405) (by norm_num)
theorem B2276275 : Blo 2275435 2276275 := bstep (se 1 (by rfl) ⟨1707206, by rfl⟩ : syracuseStep 2276275 = 3414413) B3414413
theorem B5121629 : Blo 2275435 5121629 := bbase (se 3 (by rfl) ⟨960305, by rfl⟩ : syracuseStep 5121629 = 1920611) (by norm_num)
theorem B3414419 : Blo 2275435 3414419 := bstep (se 1 (by rfl) ⟨2560814, by rfl⟩ : syracuseStep 3414419 = 5121629) B5121629
theorem B2276279 : Blo 2275435 2276279 := bstep (se 1 (by rfl) ⟨1707209, by rfl⟩ : syracuseStep 2276279 = 3414419) B3414419
theorem B3841229 : Blo 2275435 3841229 := bbase (se 3 (by rfl) ⟨720230, by rfl⟩ : syracuseStep 3841229 = 1440461) (by norm_num)
theorem B2560819 : Blo 2275435 2560819 := bstep (se 1 (by rfl) ⟨1920614, by rfl⟩ : syracuseStep 2560819 = 3841229) B3841229
theorem B3414425 : Blo 2275435 3414425 := bstep (se 2 (by rfl) ⟨1280409, by rfl⟩ : syracuseStep 3414425 = 2560819) B2560819
theorem B2276283 : Blo 2275435 2276283 := bstep (se 1 (by rfl) ⟨1707212, by rfl⟩ : syracuseStep 2276283 = 3414425) B3414425
theorem B14584693 : Blo 2275435 14584693 := bbase (se 5 (by rfl) ⟨683657, by rfl⟩ : syracuseStep 14584693 = 1367315) (by norm_num)
theorem B19446257 : Blo 2275435 19446257 := bstep (se 2 (by rfl) ⟨7292346, by rfl⟩ : syracuseStep 19446257 = 14584693) B14584693
theorem B12964171 : Blo 2275435 12964171 := bstep (se 1 (by rfl) ⟨9723128, by rfl⟩ : syracuseStep 12964171 = 19446257) B19446257
theorem B17285561 : Blo 2275435 17285561 := bstep (se 2 (by rfl) ⟨6482085, by rfl⟩ : syracuseStep 17285561 = 12964171) B12964171
theorem B11523707 : Blo 2275435 11523707 := bstep (se 1 (by rfl) ⟨8642780, by rfl⟩ : syracuseStep 11523707 = 17285561) B17285561
theorem B7682471 : Blo 2275435 7682471 := bstep (se 1 (by rfl) ⟨5761853, by rfl⟩ : syracuseStep 7682471 = 11523707) B11523707
theorem B5121647 : Blo 2275435 5121647 := bstep (se 1 (by rfl) ⟨3841235, by rfl⟩ : syracuseStep 5121647 = 7682471) B7682471
theorem B3414431 : Blo 2275435 3414431 := bstep (se 1 (by rfl) ⟨2560823, by rfl⟩ : syracuseStep 3414431 = 5121647) B5121647
theorem B2276287 : Blo 2275435 2276287 := bstep (se 1 (by rfl) ⟨1707215, by rfl⟩ : syracuseStep 2276287 = 3414431) B3414431
theorem B3414437 : Blo 2275435 3414437 := bbase (se 4 (by rfl) ⟨320103, by rfl⟩ : syracuseStep 3414437 = 640207) (by norm_num)
theorem B2276291 : Blo 2275435 2276291 := bstep (se 1 (by rfl) ⟨1707218, by rfl⟩ : syracuseStep 2276291 = 3414437) B3414437
theorem B2880937 : Blo 2275435 2880937 := bbase (se 2 (by rfl) ⟨1080351, by rfl⟩ : syracuseStep 2880937 = 2160703) (by norm_num)
theorem B3841249 : Blo 2275435 3841249 := bstep (se 2 (by rfl) ⟨1440468, by rfl⟩ : syracuseStep 3841249 = 2880937) B2880937
theorem B5121665 : Blo 2275435 5121665 := bstep (se 2 (by rfl) ⟨1920624, by rfl⟩ : syracuseStep 5121665 = 3841249) B3841249
theorem B3414443 : Blo 2275435 3414443 := bstep (se 1 (by rfl) ⟨2560832, by rfl⟩ : syracuseStep 3414443 = 5121665) B5121665
theorem B2276295 : Blo 2275435 2276295 := bstep (se 1 (by rfl) ⟨1707221, by rfl⟩ : syracuseStep 2276295 = 3414443) B3414443
theorem B2560837 : Blo 2275435 2560837 := bbase (se 4 (by rfl) ⟨240078, by rfl⟩ : syracuseStep 2560837 = 480157) (by norm_num)
theorem B3414449 : Blo 2275435 3414449 := bstep (se 2 (by rfl) ⟨1280418, by rfl⟩ : syracuseStep 3414449 = 2560837) B2560837
theorem B2276299 : Blo 2275435 2276299 := bstep (se 1 (by rfl) ⟨1707224, by rfl⟩ : syracuseStep 2276299 = 3414449) B3414449
theorem B4321421 : Blo 2275435 4321421 := bbase (se 3 (by rfl) ⟨810266, by rfl⟩ : syracuseStep 4321421 = 1620533) (by norm_num)
theorem B2880947 : Blo 2275435 2880947 := bstep (se 1 (by rfl) ⟨2160710, by rfl⟩ : syracuseStep 2880947 = 4321421) B4321421
theorem B7682525 : Blo 2275435 7682525 := bstep (se 3 (by rfl) ⟨1440473, by rfl⟩ : syracuseStep 7682525 = 2880947) B2880947
theorem B5121683 : Blo 2275435 5121683 := bstep (se 1 (by rfl) ⟨3841262, by rfl⟩ : syracuseStep 5121683 = 7682525) B7682525
theorem B3414455 : Blo 2275435 3414455 := bstep (se 1 (by rfl) ⟨2560841, by rfl⟩ : syracuseStep 3414455 = 5121683) B5121683
theorem B2276303 : Blo 2275435 2276303 := bstep (se 1 (by rfl) ⟨1707227, by rfl⟩ : syracuseStep 2276303 = 3414455) B3414455
theorem B3414461 : Blo 2275435 3414461 := bbase (se 3 (by rfl) ⟨640211, by rfl⟩ : syracuseStep 3414461 = 1280423) (by norm_num)
theorem B2276307 : Blo 2275435 2276307 := bstep (se 1 (by rfl) ⟨1707230, by rfl⟩ : syracuseStep 2276307 = 3414461) B3414461
theorem B5121701 : Blo 2275435 5121701 := bbase (se 4 (by rfl) ⟨480159, by rfl⟩ : syracuseStep 5121701 = 960319) (by norm_num)
theorem B3414467 : Blo 2275435 3414467 := bstep (se 1 (by rfl) ⟨2560850, by rfl⟩ : syracuseStep 3414467 = 5121701) B5121701
theorem B2276311 : Blo 2275435 2276311 := bstep (se 1 (by rfl) ⟨1707233, by rfl⟩ : syracuseStep 2276311 = 3414467) B3414467
theorem B5761925 : Blo 2275435 5761925 := bbase (se 4 (by rfl) ⟨540180, by rfl⟩ : syracuseStep 5761925 = 1080361) (by norm_num)
theorem B3841283 : Blo 2275435 3841283 := bstep (se 1 (by rfl) ⟨2880962, by rfl⟩ : syracuseStep 3841283 = 5761925) B5761925
theorem B2560855 : Blo 2275435 2560855 := bstep (se 1 (by rfl) ⟨1920641, by rfl⟩ : syracuseStep 2560855 = 3841283) B3841283
theorem B3414473 : Blo 2275435 3414473 := bstep (se 2 (by rfl) ⟨1280427, by rfl⟩ : syracuseStep 3414473 = 2560855) B2560855
theorem B2276315 : Blo 2275435 2276315 := bstep (se 1 (by rfl) ⟨1707236, by rfl⟩ : syracuseStep 2276315 = 3414473) B3414473
theorem B2734669 : Blo 2275435 2734669 := bbase (se 3 (by rfl) ⟨512750, by rfl⟩ : syracuseStep 2734669 = 1025501) (by norm_num)
theorem B3646225 : Blo 2275435 3646225 := bstep (se 2 (by rfl) ⟨1367334, by rfl⟩ : syracuseStep 3646225 = 2734669) B2734669
theorem B4861633 : Blo 2275435 4861633 := bstep (se 2 (by rfl) ⟨1823112, by rfl⟩ : syracuseStep 4861633 = 3646225) B3646225
theorem B6482177 : Blo 2275435 6482177 := bstep (se 2 (by rfl) ⟨2430816, by rfl⟩ : syracuseStep 6482177 = 4861633) B4861633
theorem B4321451 : Blo 2275435 4321451 := bstep (se 1 (by rfl) ⟨3241088, by rfl⟩ : syracuseStep 4321451 = 6482177) B6482177
theorem B11523869 : Blo 2275435 11523869 := bstep (se 3 (by rfl) ⟨2160725, by rfl⟩ : syracuseStep 11523869 = 4321451) B4321451
theorem B7682579 : Blo 2275435 7682579 := bstep (se 1 (by rfl) ⟨5761934, by rfl⟩ : syracuseStep 7682579 = 11523869) B11523869
theorem B5121719 : Blo 2275435 5121719 := bstep (se 1 (by rfl) ⟨3841289, by rfl⟩ : syracuseStep 5121719 = 7682579) B7682579
theorem B3414479 : Blo 2275435 3414479 := bstep (se 1 (by rfl) ⟨2560859, by rfl⟩ : syracuseStep 3414479 = 5121719) B5121719
theorem B2276319 : Blo 2275435 2276319 := bstep (se 1 (by rfl) ⟨1707239, by rfl⟩ : syracuseStep 2276319 = 3414479) B3414479
theorem B3414485 : Blo 2275435 3414485 := bbase (se 7 (by rfl) ⟨40013, by rfl⟩ : syracuseStep 3414485 = 80027) (by norm_num)
theorem B2276323 : Blo 2275435 2276323 := bstep (se 1 (by rfl) ⟨1707242, by rfl⟩ : syracuseStep 2276323 = 3414485) B3414485
theorem B8642933 : Blo 2275435 8642933 := bbase (se 5 (by rfl) ⟨405137, by rfl⟩ : syracuseStep 8642933 = 810275) (by norm_num)
theorem B5761955 : Blo 2275435 5761955 := bstep (se 1 (by rfl) ⟨4321466, by rfl⟩ : syracuseStep 5761955 = 8642933) B8642933
theorem B3841303 : Blo 2275435 3841303 := bstep (se 1 (by rfl) ⟨2880977, by rfl⟩ : syracuseStep 3841303 = 5761955) B5761955
theorem B5121737 : Blo 2275435 5121737 := bstep (se 2 (by rfl) ⟨1920651, by rfl⟩ : syracuseStep 5121737 = 3841303) B3841303
theorem B3414491 : Blo 2275435 3414491 := bstep (se 1 (by rfl) ⟨2560868, by rfl⟩ : syracuseStep 3414491 = 5121737) B5121737
theorem B2276327 : Blo 2275435 2276327 := bstep (se 1 (by rfl) ⟨1707245, by rfl⟩ : syracuseStep 2276327 = 3414491) B3414491
theorem B2560873 : Blo 2275435 2560873 := bbase (se 2 (by rfl) ⟨960327, by rfl⟩ : syracuseStep 2560873 = 1920655) (by norm_num)
theorem B3414497 : Blo 2275435 3414497 := bstep (se 2 (by rfl) ⟨1280436, by rfl⟩ : syracuseStep 3414497 = 2560873) B2560873
theorem B2276331 : Blo 2275435 2276331 := bstep (se 1 (by rfl) ⟨1707248, by rfl⟩ : syracuseStep 2276331 = 3414497) B3414497
theorem B7292501 : Blo 2275435 7292501 := bbase (se 8 (by rfl) ⟨42729, by rfl⟩ : syracuseStep 7292501 = 85459) (by norm_num)
theorem B4861667 : Blo 2275435 4861667 := bstep (se 1 (by rfl) ⟨3646250, by rfl⟩ : syracuseStep 4861667 = 7292501) B7292501
theorem B12964445 : Blo 2275435 12964445 := bstep (se 3 (by rfl) ⟨2430833, by rfl⟩ : syracuseStep 12964445 = 4861667) B4861667
theorem B8642963 : Blo 2275435 8642963 := bstep (se 1 (by rfl) ⟨6482222, by rfl⟩ : syracuseStep 8642963 = 12964445) B12964445
theorem B5761975 : Blo 2275435 5761975 := bstep (se 1 (by rfl) ⟨4321481, by rfl⟩ : syracuseStep 5761975 = 8642963) B8642963
theorem B7682633 : Blo 2275435 7682633 := bstep (se 2 (by rfl) ⟨2880987, by rfl⟩ : syracuseStep 7682633 = 5761975) B5761975
theorem B5121755 : Blo 2275435 5121755 := bstep (se 1 (by rfl) ⟨3841316, by rfl⟩ : syracuseStep 5121755 = 7682633) B7682633
theorem B3414503 : Blo 2275435 3414503 := bstep (se 1 (by rfl) ⟨2560877, by rfl⟩ : syracuseStep 3414503 = 5121755) B5121755
theorem B2276335 : Blo 2275435 2276335 := bstep (se 1 (by rfl) ⟨1707251, by rfl⟩ : syracuseStep 2276335 = 3414503) B3414503
theorem B3414509 : Blo 2275435 3414509 := bbase (se 3 (by rfl) ⟨640220, by rfl⟩ : syracuseStep 3414509 = 1280441) (by norm_num)
theorem B2276339 : Blo 2275435 2276339 := bstep (se 1 (by rfl) ⟨1707254, by rfl⟩ : syracuseStep 2276339 = 3414509) B3414509
theorem B5121773 : Blo 2275435 5121773 := bbase (se 3 (by rfl) ⟨960332, by rfl⟩ : syracuseStep 5121773 = 1920665) (by norm_num)
theorem B3414515 : Blo 2275435 3414515 := bstep (se 1 (by rfl) ⟨2560886, by rfl⟩ : syracuseStep 3414515 = 5121773) B5121773
theorem B2276343 : Blo 2275435 2276343 := bstep (se 1 (by rfl) ⟨1707257, by rfl⟩ : syracuseStep 2276343 = 3414515) B3414515
theorem B2667149 : Blo 2275435 2667149 := bbase (se 3 (by rfl) ⟨500090, by rfl⟩ : syracuseStep 2667149 = 1000181) (by norm_num)
theorem B28449589 : Blo 2275435 28449589 := bstep (se 5 (by rfl) ⟨1333574, by rfl⟩ : syracuseStep 28449589 = 2667149) B2667149
theorem B37932785 : Blo 2275435 37932785 := bstep (se 2 (by rfl) ⟨14224794, by rfl⟩ : syracuseStep 37932785 = 28449589) B28449589
theorem B25288523 : Blo 2275435 25288523 := bstep (se 1 (by rfl) ⟨18966392, by rfl⟩ : syracuseStep 25288523 = 37932785) B37932785
theorem B16859015 : Blo 2275435 16859015 := bstep (se 1 (by rfl) ⟨12644261, by rfl⟩ : syracuseStep 16859015 = 25288523) B25288523
theorem B11239343 : Blo 2275435 11239343 := bstep (se 1 (by rfl) ⟨8429507, by rfl⟩ : syracuseStep 11239343 = 16859015) B16859015
theorem B7492895 : Blo 2275435 7492895 := bstep (se 1 (by rfl) ⟨5619671, by rfl⟩ : syracuseStep 7492895 = 11239343) B11239343
theorem B4995263 : Blo 2275435 4995263 := bstep (se 1 (by rfl) ⟨3746447, by rfl⟩ : syracuseStep 4995263 = 7492895) B7492895
theorem B3330175 : Blo 2275435 3330175 := bstep (se 1 (by rfl) ⟨2497631, by rfl⟩ : syracuseStep 3330175 = 4995263) B4995263
theorem B4440233 : Blo 2275435 4440233 := bstep (se 2 (by rfl) ⟨1665087, by rfl⟩ : syracuseStep 4440233 = 3330175) B3330175
theorem B2960155 : Blo 2275435 2960155 := bstep (se 1 (by rfl) ⟨2220116, by rfl⟩ : syracuseStep 2960155 = 4440233) B4440233
theorem B15787493 : Blo 2275435 15787493 := bstep (se 4 (by rfl) ⟨1480077, by rfl⟩ : syracuseStep 15787493 = 2960155) B2960155
theorem B10524995 : Blo 2275435 10524995 := bstep (se 1 (by rfl) ⟨7893746, by rfl⟩ : syracuseStep 10524995 = 15787493) B15787493
theorem B7016663 : Blo 2275435 7016663 := bstep (se 1 (by rfl) ⟨5262497, by rfl⟩ : syracuseStep 7016663 = 10524995) B10524995
theorem B18711101 : Blo 2275435 18711101 := bstep (se 3 (by rfl) ⟨3508331, by rfl⟩ : syracuseStep 18711101 = 7016663) B7016663
theorem B49896269 : Blo 2275435 49896269 := bstep (se 3 (by rfl) ⟨9355550, by rfl⟩ : syracuseStep 49896269 = 18711101) B18711101
theorem B33264179 : Blo 2275435 33264179 := bstep (se 1 (by rfl) ⟨24948134, by rfl⟩ : syracuseStep 33264179 = 49896269) B49896269
theorem B22176119 : Blo 2275435 22176119 := bstep (se 1 (by rfl) ⟨16632089, by rfl⟩ : syracuseStep 22176119 = 33264179) B33264179
theorem B14784079 : Blo 2275435 14784079 := bstep (se 1 (by rfl) ⟨11088059, by rfl⟩ : syracuseStep 14784079 = 22176119) B22176119
theorem B19712105 : Blo 2275435 19712105 := bstep (se 2 (by rfl) ⟨7392039, by rfl⟩ : syracuseStep 19712105 = 14784079) B14784079
theorem B13141403 : Blo 2275435 13141403 := bstep (se 1 (by rfl) ⟨9856052, by rfl⟩ : syracuseStep 13141403 = 19712105) B19712105
theorem B8760935 : Blo 2275435 8760935 := bstep (se 1 (by rfl) ⟨6570701, by rfl⟩ : syracuseStep 8760935 = 13141403) B13141403
theorem B5840623 : Blo 2275435 5840623 := bstep (se 1 (by rfl) ⟨4380467, by rfl⟩ : syracuseStep 5840623 = 8760935) B8760935
theorem B7787497 : Blo 2275435 7787497 := bstep (se 2 (by rfl) ⟨2920311, by rfl⟩ : syracuseStep 7787497 = 5840623) B5840623
theorem B10383329 : Blo 2275435 10383329 := bstep (se 2 (by rfl) ⟨3893748, by rfl⟩ : syracuseStep 10383329 = 7787497) B7787497
theorem B27688877 : Blo 2275435 27688877 := bstep (se 3 (by rfl) ⟨5191664, by rfl⟩ : syracuseStep 27688877 = 10383329) B10383329
theorem B18459251 : Blo 2275435 18459251 := bstep (se 1 (by rfl) ⟨13844438, by rfl⟩ : syracuseStep 18459251 = 27688877) B27688877
theorem B12306167 : Blo 2275435 12306167 := bstep (se 1 (by rfl) ⟨9229625, by rfl⟩ : syracuseStep 12306167 = 18459251) B18459251
theorem B8204111 : Blo 2275435 8204111 := bstep (se 1 (by rfl) ⟨6153083, by rfl⟩ : syracuseStep 8204111 = 12306167) B12306167
theorem B5469407 : Blo 2275435 5469407 := bstep (se 1 (by rfl) ⟨4102055, by rfl⟩ : syracuseStep 5469407 = 8204111) B8204111
theorem B3646271 : Blo 2275435 3646271 := bstep (se 1 (by rfl) ⟨2734703, by rfl⟩ : syracuseStep 3646271 = 5469407) B5469407
theorem B2430847 : Blo 2275435 2430847 := bstep (se 1 (by rfl) ⟨1823135, by rfl⟩ : syracuseStep 2430847 = 3646271) B3646271
theorem B3241129 : Blo 2275435 3241129 := bstep (se 2 (by rfl) ⟨1215423, by rfl⟩ : syracuseStep 3241129 = 2430847) B2430847
theorem B4321505 : Blo 2275435 4321505 := bstep (se 2 (by rfl) ⟨1620564, by rfl⟩ : syracuseStep 4321505 = 3241129) B3241129
theorem B2881003 : Blo 2275435 2881003 := bstep (se 1 (by rfl) ⟨2160752, by rfl⟩ : syracuseStep 2881003 = 4321505) B4321505
theorem B3841337 : Blo 2275435 3841337 := bstep (se 2 (by rfl) ⟨1440501, by rfl⟩ : syracuseStep 3841337 = 2881003) B2881003
theorem B2560891 : Blo 2275435 2560891 := bstep (se 1 (by rfl) ⟨1920668, by rfl⟩ : syracuseStep 2560891 = 3841337) B3841337
theorem B3414521 : Blo 2275435 3414521 := bstep (se 2 (by rfl) ⟨1280445, by rfl⟩ : syracuseStep 3414521 = 2560891) B2560891
theorem B2276347 : Blo 2275435 2276347 := bstep (se 1 (by rfl) ⟨1707260, by rfl⟩ : syracuseStep 2276347 = 3414521) B3414521
theorem B5840629 : Blo 2275435 5840629 := bbase (se 5 (by rfl) ⟨273779, by rfl⟩ : syracuseStep 5840629 = 547559) (by norm_num)
theorem B31150021 : Blo 2275435 31150021 := bstep (se 4 (by rfl) ⟨2920314, by rfl⟩ : syracuseStep 31150021 = 5840629) B5840629
theorem B41533361 : Blo 2275435 41533361 := bstep (se 2 (by rfl) ⟨15575010, by rfl⟩ : syracuseStep 41533361 = 31150021) B31150021
theorem B27688907 : Blo 2275435 27688907 := bstep (se 1 (by rfl) ⟨20766680, by rfl⟩ : syracuseStep 27688907 = 41533361) B41533361
theorem B18459271 : Blo 2275435 18459271 := bstep (se 1 (by rfl) ⟨13844453, by rfl⟩ : syracuseStep 18459271 = 27688907) B27688907
theorem B98449445 : Blo 2275435 98449445 := bstep (se 4 (by rfl) ⟨9229635, by rfl⟩ : syracuseStep 98449445 = 18459271) B18459271
theorem B65632963 : Blo 2275435 65632963 := bstep (se 1 (by rfl) ⟨49224722, by rfl⟩ : syracuseStep 65632963 = 98449445) B98449445
theorem B87510617 : Blo 2275435 87510617 := bstep (se 2 (by rfl) ⟨32816481, by rfl⟩ : syracuseStep 87510617 = 65632963) B65632963
theorem B58340411 : Blo 2275435 58340411 := bstep (se 1 (by rfl) ⟨43755308, by rfl⟩ : syracuseStep 58340411 = 87510617) B87510617
theorem B38893607 : Blo 2275435 38893607 := bstep (se 1 (by rfl) ⟨29170205, by rfl⟩ : syracuseStep 38893607 = 58340411) B58340411
theorem B25929071 : Blo 2275435 25929071 := bstep (se 1 (by rfl) ⟨19446803, by rfl⟩ : syracuseStep 25929071 = 38893607) B38893607
theorem B17286047 : Blo 2275435 17286047 := bstep (se 1 (by rfl) ⟨12964535, by rfl⟩ : syracuseStep 17286047 = 25929071) B25929071
theorem B11524031 : Blo 2275435 11524031 := bstep (se 1 (by rfl) ⟨8643023, by rfl⟩ : syracuseStep 11524031 = 17286047) B17286047
theorem B7682687 : Blo 2275435 7682687 := bstep (se 1 (by rfl) ⟨5762015, by rfl⟩ : syracuseStep 7682687 = 11524031) B11524031
theorem B5121791 : Blo 2275435 5121791 := bstep (se 1 (by rfl) ⟨3841343, by rfl⟩ : syracuseStep 5121791 = 7682687) B7682687
theorem B3414527 : Blo 2275435 3414527 := bstep (se 1 (by rfl) ⟨2560895, by rfl⟩ : syracuseStep 3414527 = 5121791) B5121791
theorem B2276351 : Blo 2275435 2276351 := bstep (se 1 (by rfl) ⟨1707263, by rfl⟩ : syracuseStep 2276351 = 3414527) B3414527
theorem B3414533 : Blo 2275435 3414533 := bbase (se 4 (by rfl) ⟨320112, by rfl⟩ : syracuseStep 3414533 = 640225) (by norm_num)
theorem B2276355 : Blo 2275435 2276355 := bstep (se 1 (by rfl) ⟨1707266, by rfl⟩ : syracuseStep 2276355 = 3414533) B3414533
theorem B3841357 : Blo 2275435 3841357 := bbase (se 3 (by rfl) ⟨720254, by rfl⟩ : syracuseStep 3841357 = 1440509) (by norm_num)
theorem B5121809 : Blo 2275435 5121809 := bstep (se 2 (by rfl) ⟨1920678, by rfl⟩ : syracuseStep 5121809 = 3841357) B3841357
theorem B3414539 : Blo 2275435 3414539 := bstep (se 1 (by rfl) ⟨2560904, by rfl⟩ : syracuseStep 3414539 = 5121809) B5121809
theorem B2276359 : Blo 2275435 2276359 := bstep (se 1 (by rfl) ⟨1707269, by rfl⟩ : syracuseStep 2276359 = 3414539) B3414539
theorem B2560909 : Blo 2275435 2560909 := bbase (se 3 (by rfl) ⟨480170, by rfl⟩ : syracuseStep 2560909 = 960341) (by norm_num)
theorem B3414545 : Blo 2275435 3414545 := bstep (se 2 (by rfl) ⟨1280454, by rfl⟩ : syracuseStep 3414545 = 2560909) B2560909
theorem B2276363 : Blo 2275435 2276363 := bstep (se 1 (by rfl) ⟨1707272, by rfl⟩ : syracuseStep 2276363 = 3414545) B3414545
theorem B7682741 : Blo 2275435 7682741 := bbase (se 5 (by rfl) ⟨360128, by rfl⟩ : syracuseStep 7682741 = 720257) (by norm_num)
theorem B5121827 : Blo 2275435 5121827 := bstep (se 1 (by rfl) ⟨3841370, by rfl⟩ : syracuseStep 5121827 = 7682741) B7682741
theorem B3414551 : Blo 2275435 3414551 := bstep (se 1 (by rfl) ⟨2560913, by rfl⟩ : syracuseStep 3414551 = 5121827) B5121827
theorem B2276367 : Blo 2275435 2276367 := bstep (se 1 (by rfl) ⟨1707275, by rfl⟩ : syracuseStep 2276367 = 3414551) B3414551
theorem B3414557 : Blo 2275435 3414557 := bbase (se 3 (by rfl) ⟨640229, by rfl⟩ : syracuseStep 3414557 = 1280459) (by norm_num)
theorem B2276371 : Blo 2275435 2276371 := bstep (se 1 (by rfl) ⟨1707278, by rfl⟩ : syracuseStep 2276371 = 3414557) B3414557
theorem B5121845 : Blo 2275435 5121845 := bbase (se 5 (by rfl) ⟨240086, by rfl⟩ : syracuseStep 5121845 = 480173) (by norm_num)
theorem B3414563 : Blo 2275435 3414563 := bstep (se 1 (by rfl) ⟨2560922, by rfl⟩ : syracuseStep 3414563 = 5121845) B5121845
theorem B2276375 : Blo 2275435 2276375 := bstep (se 1 (by rfl) ⟨1707281, by rfl⟩ : syracuseStep 2276375 = 3414563) B3414563
theorem B2734741 : Blo 2275435 2734741 := bbase (se 6 (by rfl) ⟨64095, by rfl⟩ : syracuseStep 2734741 = 128191) (by norm_num)
theorem B14585285 : Blo 2275435 14585285 := bstep (se 4 (by rfl) ⟨1367370, by rfl⟩ : syracuseStep 14585285 = 2734741) B2734741
theorem B9723523 : Blo 2275435 9723523 := bstep (se 1 (by rfl) ⟨7292642, by rfl⟩ : syracuseStep 9723523 = 14585285) B14585285
theorem B12964697 : Blo 2275435 12964697 := bstep (se 2 (by rfl) ⟨4861761, by rfl⟩ : syracuseStep 12964697 = 9723523) B9723523
theorem B8643131 : Blo 2275435 8643131 := bstep (se 1 (by rfl) ⟨6482348, by rfl⟩ : syracuseStep 8643131 = 12964697) B12964697
theorem B5762087 : Blo 2275435 5762087 := bstep (se 1 (by rfl) ⟨4321565, by rfl⟩ : syracuseStep 5762087 = 8643131) B8643131
theorem B3841391 : Blo 2275435 3841391 := bstep (se 1 (by rfl) ⟨2881043, by rfl⟩ : syracuseStep 3841391 = 5762087) B5762087
theorem B2560927 : Blo 2275435 2560927 := bstep (se 1 (by rfl) ⟨1920695, by rfl⟩ : syracuseStep 2560927 = 3841391) B3841391
theorem B3414569 : Blo 2275435 3414569 := bstep (se 2 (by rfl) ⟨1280463, by rfl⟩ : syracuseStep 3414569 = 2560927) B2560927
theorem B2276379 : Blo 2275435 2276379 := bstep (se 1 (by rfl) ⟨1707284, by rfl⟩ : syracuseStep 2276379 = 3414569) B3414569
theorem B3076589 : Blo 2275435 3076589 := bbase (se 3 (by rfl) ⟨576860, by rfl⟩ : syracuseStep 3076589 = 1153721) (by norm_num)
theorem B8204237 : Blo 2275435 8204237 := bstep (se 3 (by rfl) ⟨1538294, by rfl⟩ : syracuseStep 8204237 = 3076589) B3076589
theorem B5469491 : Blo 2275435 5469491 := bstep (se 1 (by rfl) ⟨4102118, by rfl⟩ : syracuseStep 5469491 = 8204237) B8204237
theorem B14585309 : Blo 2275435 14585309 := bstep (se 3 (by rfl) ⟨2734745, by rfl⟩ : syracuseStep 14585309 = 5469491) B5469491
theorem B9723539 : Blo 2275435 9723539 := bstep (se 1 (by rfl) ⟨7292654, by rfl⟩ : syracuseStep 9723539 = 14585309) B14585309
theorem B6482359 : Blo 2275435 6482359 := bstep (se 1 (by rfl) ⟨4861769, by rfl⟩ : syracuseStep 6482359 = 9723539) B9723539
theorem B8643145 : Blo 2275435 8643145 := bstep (se 2 (by rfl) ⟨3241179, by rfl⟩ : syracuseStep 8643145 = 6482359) B6482359
theorem B11524193 : Blo 2275435 11524193 := bstep (se 2 (by rfl) ⟨4321572, by rfl⟩ : syracuseStep 11524193 = 8643145) B8643145
theorem B7682795 : Blo 2275435 7682795 := bstep (se 1 (by rfl) ⟨5762096, by rfl⟩ : syracuseStep 7682795 = 11524193) B11524193
theorem B5121863 : Blo 2275435 5121863 := bstep (se 1 (by rfl) ⟨3841397, by rfl⟩ : syracuseStep 5121863 = 7682795) B7682795
theorem B3414575 : Blo 2275435 3414575 := bstep (se 1 (by rfl) ⟨2560931, by rfl⟩ : syracuseStep 3414575 = 5121863) B5121863
theorem B2276383 : Blo 2275435 2276383 := bstep (se 1 (by rfl) ⟨1707287, by rfl⟩ : syracuseStep 2276383 = 3414575) B3414575
theorem B3414581 : Blo 2275435 3414581 := bbase (se 5 (by rfl) ⟨160058, by rfl⟩ : syracuseStep 3414581 = 320117) (by norm_num)
theorem B2276387 : Blo 2275435 2276387 := bstep (se 1 (by rfl) ⟨1707290, by rfl⟩ : syracuseStep 2276387 = 3414581) B3414581
theorem B5762117 : Blo 2275435 5762117 := bbase (se 4 (by rfl) ⟨540198, by rfl⟩ : syracuseStep 5762117 = 1080397) (by norm_num)
theorem B3841411 : Blo 2275435 3841411 := bstep (se 1 (by rfl) ⟨2881058, by rfl⟩ : syracuseStep 3841411 = 5762117) B5762117
theorem B5121881 : Blo 2275435 5121881 := bstep (se 2 (by rfl) ⟨1920705, by rfl⟩ : syracuseStep 5121881 = 3841411) B3841411
theorem B3414587 : Blo 2275435 3414587 := bstep (se 1 (by rfl) ⟨2560940, by rfl⟩ : syracuseStep 3414587 = 5121881) B5121881
theorem B2276391 : Blo 2275435 2276391 := bstep (se 1 (by rfl) ⟨1707293, by rfl⟩ : syracuseStep 2276391 = 3414587) B3414587
theorem B2560945 : Blo 2275435 2560945 := bbase (se 2 (by rfl) ⟨960354, by rfl⟩ : syracuseStep 2560945 = 1920709) (by norm_num)
theorem B3414593 : Blo 2275435 3414593 := bstep (se 2 (by rfl) ⟨1280472, by rfl⟩ : syracuseStep 3414593 = 2560945) B2560945
theorem B2276395 : Blo 2275435 2276395 := bstep (se 1 (by rfl) ⟨1707296, by rfl⟩ : syracuseStep 2276395 = 3414593) B3414593
theorem B6482405 : Blo 2275435 6482405 := bbase (se 4 (by rfl) ⟨607725, by rfl⟩ : syracuseStep 6482405 = 1215451) (by norm_num)
theorem B4321603 : Blo 2275435 4321603 := bstep (se 1 (by rfl) ⟨3241202, by rfl⟩ : syracuseStep 4321603 = 6482405) B6482405
theorem B5762137 : Blo 2275435 5762137 := bstep (se 2 (by rfl) ⟨2160801, by rfl⟩ : syracuseStep 5762137 = 4321603) B4321603
theorem B7682849 : Blo 2275435 7682849 := bstep (se 2 (by rfl) ⟨2881068, by rfl⟩ : syracuseStep 7682849 = 5762137) B5762137
theorem B5121899 : Blo 2275435 5121899 := bstep (se 1 (by rfl) ⟨3841424, by rfl⟩ : syracuseStep 5121899 = 7682849) B7682849
theorem B3414599 : Blo 2275435 3414599 := bstep (se 1 (by rfl) ⟨2560949, by rfl⟩ : syracuseStep 3414599 = 5121899) B5121899
theorem B2276399 : Blo 2275435 2276399 := bstep (se 1 (by rfl) ⟨1707299, by rfl⟩ : syracuseStep 2276399 = 3414599) B3414599
theorem B3414605 : Blo 2275435 3414605 := bbase (se 3 (by rfl) ⟨640238, by rfl⟩ : syracuseStep 3414605 = 1280477) (by norm_num)
theorem B2276403 : Blo 2275435 2276403 := bstep (se 1 (by rfl) ⟨1707302, by rfl⟩ : syracuseStep 2276403 = 3414605) B3414605
theorem B5121917 : Blo 2275435 5121917 := bbase (se 3 (by rfl) ⟨960359, by rfl⟩ : syracuseStep 5121917 = 1920719) (by norm_num)
theorem B3414611 : Blo 2275435 3414611 := bstep (se 1 (by rfl) ⟨2560958, by rfl⟩ : syracuseStep 3414611 = 5121917) B5121917
theorem B2276407 : Blo 2275435 2276407 := bstep (se 1 (by rfl) ⟨1707305, by rfl⟩ : syracuseStep 2276407 = 3414611) B3414611
theorem B3841445 : Blo 2275435 3841445 := bbase (se 4 (by rfl) ⟨360135, by rfl⟩ : syracuseStep 3841445 = 720271) (by norm_num)
theorem B2560963 : Blo 2275435 2560963 := bstep (se 1 (by rfl) ⟨1920722, by rfl⟩ : syracuseStep 2560963 = 3841445) B3841445
theorem B3414617 : Blo 2275435 3414617 := bstep (se 2 (by rfl) ⟨1280481, by rfl⟩ : syracuseStep 3414617 = 2560963) B2560963
theorem B2276411 : Blo 2275435 2276411 := bstep (se 1 (by rfl) ⟨1707308, by rfl⟩ : syracuseStep 2276411 = 3414617) B3414617
theorem B3461213 : Blo 2275435 3461213 := bbase (se 3 (by rfl) ⟨648977, by rfl⟩ : syracuseStep 3461213 = 1297955) (by norm_num)
theorem B2307475 : Blo 2275435 2307475 := bstep (se 1 (by rfl) ⟨1730606, by rfl⟩ : syracuseStep 2307475 = 3461213) B3461213
theorem B3076633 : Blo 2275435 3076633 := bstep (se 2 (by rfl) ⟨1153737, by rfl⟩ : syracuseStep 3076633 = 2307475) B2307475
theorem B4102177 : Blo 2275435 4102177 := bstep (se 2 (by rfl) ⟨1538316, by rfl⟩ : syracuseStep 4102177 = 3076633) B3076633
theorem B5469569 : Blo 2275435 5469569 := bstep (se 2 (by rfl) ⟨2051088, by rfl⟩ : syracuseStep 5469569 = 4102177) B4102177
theorem B3646379 : Blo 2275435 3646379 := bstep (se 1 (by rfl) ⟨2734784, by rfl⟩ : syracuseStep 3646379 = 5469569) B5469569
theorem B2430919 : Blo 2275435 2430919 := bstep (se 1 (by rfl) ⟨1823189, by rfl⟩ : syracuseStep 2430919 = 3646379) B3646379
theorem B3241225 : Blo 2275435 3241225 := bstep (se 2 (by rfl) ⟨1215459, by rfl⟩ : syracuseStep 3241225 = 2430919) B2430919
theorem B17286533 : Blo 2275435 17286533 := bstep (se 4 (by rfl) ⟨1620612, by rfl⟩ : syracuseStep 17286533 = 3241225) B3241225
theorem B11524355 : Blo 2275435 11524355 := bstep (se 1 (by rfl) ⟨8643266, by rfl⟩ : syracuseStep 11524355 = 17286533) B17286533
theorem B7682903 : Blo 2275435 7682903 := bstep (se 1 (by rfl) ⟨5762177, by rfl⟩ : syracuseStep 7682903 = 11524355) B11524355
theorem B5121935 : Blo 2275435 5121935 := bstep (se 1 (by rfl) ⟨3841451, by rfl⟩ : syracuseStep 5121935 = 7682903) B7682903
theorem B3414623 : Blo 2275435 3414623 := bstep (se 1 (by rfl) ⟨2560967, by rfl⟩ : syracuseStep 3414623 = 5121935) B5121935
theorem B2276415 : Blo 2275435 2276415 := bstep (se 1 (by rfl) ⟨1707311, by rfl⟩ : syracuseStep 2276415 = 3414623) B3414623
theorem B3414629 : Blo 2275435 3414629 := bbase (se 4 (by rfl) ⟨320121, by rfl⟩ : syracuseStep 3414629 = 640243) (by norm_num)
theorem B2276419 : Blo 2275435 2276419 := bstep (se 1 (by rfl) ⟨1707314, by rfl⟩ : syracuseStep 2276419 = 3414629) B3414629
theorem B3241237 : Blo 2275435 3241237 := bbase (se 6 (by rfl) ⟨75966, by rfl⟩ : syracuseStep 3241237 = 151933) (by norm_num)
theorem B4321649 : Blo 2275435 4321649 := bstep (se 2 (by rfl) ⟨1620618, by rfl⟩ : syracuseStep 4321649 = 3241237) B3241237
theorem B2881099 : Blo 2275435 2881099 := bstep (se 1 (by rfl) ⟨2160824, by rfl⟩ : syracuseStep 2881099 = 4321649) B4321649
theorem B3841465 : Blo 2275435 3841465 := bstep (se 2 (by rfl) ⟨1440549, by rfl⟩ : syracuseStep 3841465 = 2881099) B2881099
theorem B5121953 : Blo 2275435 5121953 := bstep (se 2 (by rfl) ⟨1920732, by rfl⟩ : syracuseStep 5121953 = 3841465) B3841465
theorem B3414635 : Blo 2275435 3414635 := bstep (se 1 (by rfl) ⟨2560976, by rfl⟩ : syracuseStep 3414635 = 5121953) B5121953
theorem B2276423 : Blo 2275435 2276423 := bstep (se 1 (by rfl) ⟨1707317, by rfl⟩ : syracuseStep 2276423 = 3414635) B3414635
theorem B2560981 : Blo 2275435 2560981 := bbase (se 7 (by rfl) ⟨30011, by rfl⟩ : syracuseStep 2560981 = 60023) (by norm_num)
theorem B3414641 : Blo 2275435 3414641 := bstep (se 2 (by rfl) ⟨1280490, by rfl⟩ : syracuseStep 3414641 = 2560981) B2560981
theorem B2276427 : Blo 2275435 2276427 := bstep (se 1 (by rfl) ⟨1707320, by rfl⟩ : syracuseStep 2276427 = 3414641) B3414641
theorem B2881109 : Blo 2275435 2881109 := bbase (se 8 (by rfl) ⟨16881, by rfl⟩ : syracuseStep 2881109 = 33763) (by norm_num)
theorem B7682957 : Blo 2275435 7682957 := bstep (se 3 (by rfl) ⟨1440554, by rfl⟩ : syracuseStep 7682957 = 2881109) B2881109
theorem B5121971 : Blo 2275435 5121971 := bstep (se 1 (by rfl) ⟨3841478, by rfl⟩ : syracuseStep 5121971 = 7682957) B7682957
theorem B3414647 : Blo 2275435 3414647 := bstep (se 1 (by rfl) ⟨2560985, by rfl⟩ : syracuseStep 3414647 = 5121971) B5121971
theorem B2276431 : Blo 2275435 2276431 := bstep (se 1 (by rfl) ⟨1707323, by rfl⟩ : syracuseStep 2276431 = 3414647) B3414647
theorem B3414653 : Blo 2275435 3414653 := bbase (se 3 (by rfl) ⟨640247, by rfl⟩ : syracuseStep 3414653 = 1280495) (by norm_num)
theorem B2276435 : Blo 2275435 2276435 := bstep (se 1 (by rfl) ⟨1707326, by rfl⟩ : syracuseStep 2276435 = 3414653) B3414653
theorem B5121989 : Blo 2275435 5121989 := bbase (se 4 (by rfl) ⟨480186, by rfl⟩ : syracuseStep 5121989 = 960373) (by norm_num)
theorem B3414659 : Blo 2275435 3414659 := bstep (se 1 (by rfl) ⟨2560994, by rfl⟩ : syracuseStep 3414659 = 5121989) B5121989
theorem B2276439 : Blo 2275435 2276439 := bstep (se 1 (by rfl) ⟨1707329, by rfl⟩ : syracuseStep 2276439 = 3414659) B3414659
theorem B9723797 : Blo 2275435 9723797 := bbase (se 6 (by rfl) ⟨227901, by rfl⟩ : syracuseStep 9723797 = 455803) (by norm_num)
theorem B6482531 : Blo 2275435 6482531 := bstep (se 1 (by rfl) ⟨4861898, by rfl⟩ : syracuseStep 6482531 = 9723797) B9723797
theorem B4321687 : Blo 2275435 4321687 := bstep (se 1 (by rfl) ⟨3241265, by rfl⟩ : syracuseStep 4321687 = 6482531) B6482531
theorem B5762249 : Blo 2275435 5762249 := bstep (se 2 (by rfl) ⟨2160843, by rfl⟩ : syracuseStep 5762249 = 4321687) B4321687
theorem B3841499 : Blo 2275435 3841499 := bstep (se 1 (by rfl) ⟨2881124, by rfl⟩ : syracuseStep 3841499 = 5762249) B5762249
theorem B2560999 : Blo 2275435 2560999 := bstep (se 1 (by rfl) ⟨1920749, by rfl⟩ : syracuseStep 2560999 = 3841499) B3841499
theorem B3414665 : Blo 2275435 3414665 := bstep (se 2 (by rfl) ⟨1280499, by rfl⟩ : syracuseStep 3414665 = 2560999) B2560999
theorem B2276443 : Blo 2275435 2276443 := bstep (se 1 (by rfl) ⟨1707332, by rfl⟩ : syracuseStep 2276443 = 3414665) B3414665
theorem B11524517 : Blo 2275435 11524517 := bbase (se 4 (by rfl) ⟨1080423, by rfl⟩ : syracuseStep 11524517 = 2160847) (by norm_num)
theorem B7683011 : Blo 2275435 7683011 := bstep (se 1 (by rfl) ⟨5762258, by rfl⟩ : syracuseStep 7683011 = 11524517) B11524517
theorem B5122007 : Blo 2275435 5122007 := bstep (se 1 (by rfl) ⟨3841505, by rfl⟩ : syracuseStep 5122007 = 7683011) B7683011
theorem B3414671 : Blo 2275435 3414671 := bstep (se 1 (by rfl) ⟨2561003, by rfl⟩ : syracuseStep 3414671 = 5122007) B5122007
theorem B2276447 : Blo 2275435 2276447 := bstep (se 1 (by rfl) ⟨1707335, by rfl⟩ : syracuseStep 2276447 = 3414671) B3414671
theorem B3414677 : Blo 2275435 3414677 := bbase (se 6 (by rfl) ⟨80031, by rfl⟩ : syracuseStep 3414677 = 160063) (by norm_num)
theorem B2276451 : Blo 2275435 2276451 := bstep (se 1 (by rfl) ⟨1707338, by rfl⟩ : syracuseStep 2276451 = 3414677) B3414677
theorem B2464129 : Blo 2275435 2464129 := bbase (se 2 (by rfl) ⟨924048, by rfl⟩ : syracuseStep 2464129 = 1848097) (by norm_num)
theorem B3285505 : Blo 2275435 3285505 := bstep (se 2 (by rfl) ⟨1232064, by rfl⟩ : syracuseStep 3285505 = 2464129) B2464129
theorem B17522693 : Blo 2275435 17522693 := bstep (se 4 (by rfl) ⟨1642752, by rfl⟩ : syracuseStep 17522693 = 3285505) B3285505
theorem B11681795 : Blo 2275435 11681795 := bstep (se 1 (by rfl) ⟨8761346, by rfl⟩ : syracuseStep 11681795 = 17522693) B17522693
theorem B7787863 : Blo 2275435 7787863 := bstep (se 1 (by rfl) ⟨5840897, by rfl⟩ : syracuseStep 7787863 = 11681795) B11681795
theorem B10383817 : Blo 2275435 10383817 := bstep (se 2 (by rfl) ⟨3893931, by rfl⟩ : syracuseStep 10383817 = 7787863) B7787863
theorem B13845089 : Blo 2275435 13845089 := bstep (se 2 (by rfl) ⟨5191908, by rfl⟩ : syracuseStep 13845089 = 10383817) B10383817
theorem B9230059 : Blo 2275435 9230059 := bstep (se 1 (by rfl) ⟨6922544, by rfl⟩ : syracuseStep 9230059 = 13845089) B13845089
theorem B12306745 : Blo 2275435 12306745 := bstep (se 2 (by rfl) ⟨4615029, by rfl⟩ : syracuseStep 12306745 = 9230059) B9230059
theorem B16408993 : Blo 2275435 16408993 := bstep (se 2 (by rfl) ⟨6153372, by rfl⟩ : syracuseStep 16408993 = 12306745) B12306745
theorem B21878657 : Blo 2275435 21878657 := bstep (se 2 (by rfl) ⟨8204496, by rfl⟩ : syracuseStep 21878657 = 16408993) B16408993
theorem B14585771 : Blo 2275435 14585771 := bstep (se 1 (by rfl) ⟨10939328, by rfl⟩ : syracuseStep 14585771 = 21878657) B21878657
theorem B9723847 : Blo 2275435 9723847 := bstep (se 1 (by rfl) ⟨7292885, by rfl⟩ : syracuseStep 9723847 = 14585771) B14585771
theorem B12965129 : Blo 2275435 12965129 := bstep (se 2 (by rfl) ⟨4861923, by rfl⟩ : syracuseStep 12965129 = 9723847) B9723847
theorem B8643419 : Blo 2275435 8643419 := bstep (se 1 (by rfl) ⟨6482564, by rfl⟩ : syracuseStep 8643419 = 12965129) B12965129
theorem B5762279 : Blo 2275435 5762279 := bstep (se 1 (by rfl) ⟨4321709, by rfl⟩ : syracuseStep 5762279 = 8643419) B8643419
theorem B3841519 : Blo 2275435 3841519 := bstep (se 1 (by rfl) ⟨2881139, by rfl⟩ : syracuseStep 3841519 = 5762279) B5762279
theorem B5122025 : Blo 2275435 5122025 := bstep (se 2 (by rfl) ⟨1920759, by rfl⟩ : syracuseStep 5122025 = 3841519) B3841519
theorem B3414683 : Blo 2275435 3414683 := bstep (se 1 (by rfl) ⟨2561012, by rfl⟩ : syracuseStep 3414683 = 5122025) B5122025
theorem B2276455 : Blo 2275435 2276455 := bstep (se 1 (by rfl) ⟨1707341, by rfl⟩ : syracuseStep 2276455 = 3414683) B3414683
theorem B2561017 : Blo 2275435 2561017 := bbase (se 2 (by rfl) ⟨960381, by rfl⟩ : syracuseStep 2561017 = 1920763) (by norm_num)
theorem B3414689 : Blo 2275435 3414689 := bstep (se 2 (by rfl) ⟨1280508, by rfl⟩ : syracuseStep 3414689 = 2561017) B2561017
theorem B2276459 : Blo 2275435 2276459 := bstep (se 1 (by rfl) ⟨1707344, by rfl⟩ : syracuseStep 2276459 = 3414689) B3414689
theorem B3285517 : Blo 2275435 3285517 := bbase (se 3 (by rfl) ⟨616034, by rfl⟩ : syracuseStep 3285517 = 1232069) (by norm_num)
theorem B4380689 : Blo 2275435 4380689 := bstep (se 2 (by rfl) ⟨1642758, by rfl⟩ : syracuseStep 4380689 = 3285517) B3285517
theorem B2920459 : Blo 2275435 2920459 := bstep (se 1 (by rfl) ⟨2190344, by rfl⟩ : syracuseStep 2920459 = 4380689) B4380689
theorem B3893945 : Blo 2275435 3893945 := bstep (se 2 (by rfl) ⟨1460229, by rfl⟩ : syracuseStep 3893945 = 2920459) B2920459
theorem B41535413 : Blo 2275435 41535413 := bstep (se 5 (by rfl) ⟨1946972, by rfl⟩ : syracuseStep 41535413 = 3893945) B3893945
theorem B27690275 : Blo 2275435 27690275 := bstep (se 1 (by rfl) ⟨20767706, by rfl⟩ : syracuseStep 27690275 = 41535413) B41535413
theorem B18460183 : Blo 2275435 18460183 := bstep (se 1 (by rfl) ⟨13845137, by rfl⟩ : syracuseStep 18460183 = 27690275) B27690275
theorem B24613577 : Blo 2275435 24613577 := bstep (se 2 (by rfl) ⟨9230091, by rfl⟩ : syracuseStep 24613577 = 18460183) B18460183
theorem B16409051 : Blo 2275435 16409051 := bstep (se 1 (by rfl) ⟨12306788, by rfl⟩ : syracuseStep 16409051 = 24613577) B24613577
theorem B10939367 : Blo 2275435 10939367 := bstep (se 1 (by rfl) ⟨8204525, by rfl⟩ : syracuseStep 10939367 = 16409051) B16409051
theorem B7292911 : Blo 2275435 7292911 := bstep (se 1 (by rfl) ⟨5469683, by rfl⟩ : syracuseStep 7292911 = 10939367) B10939367
theorem B9723881 : Blo 2275435 9723881 := bstep (se 2 (by rfl) ⟨3646455, by rfl⟩ : syracuseStep 9723881 = 7292911) B7292911
theorem B6482587 : Blo 2275435 6482587 := bstep (se 1 (by rfl) ⟨4861940, by rfl⟩ : syracuseStep 6482587 = 9723881) B9723881
theorem B8643449 : Blo 2275435 8643449 := bstep (se 2 (by rfl) ⟨3241293, by rfl⟩ : syracuseStep 8643449 = 6482587) B6482587
theorem B5762299 : Blo 2275435 5762299 := bstep (se 1 (by rfl) ⟨4321724, by rfl⟩ : syracuseStep 5762299 = 8643449) B8643449
theorem B7683065 : Blo 2275435 7683065 := bstep (se 2 (by rfl) ⟨2881149, by rfl⟩ : syracuseStep 7683065 = 5762299) B5762299
theorem B5122043 : Blo 2275435 5122043 := bstep (se 1 (by rfl) ⟨3841532, by rfl⟩ : syracuseStep 5122043 = 7683065) B7683065
theorem B3414695 : Blo 2275435 3414695 := bstep (se 1 (by rfl) ⟨2561021, by rfl⟩ : syracuseStep 3414695 = 5122043) B5122043
theorem B2276463 : Blo 2275435 2276463 := bstep (se 1 (by rfl) ⟨1707347, by rfl⟩ : syracuseStep 2276463 = 3414695) B3414695
theorem B3414701 : Blo 2275435 3414701 := bbase (se 3 (by rfl) ⟨640256, by rfl⟩ : syracuseStep 3414701 = 1280513) (by norm_num)
theorem B2276467 : Blo 2275435 2276467 := bstep (se 1 (by rfl) ⟨1707350, by rfl⟩ : syracuseStep 2276467 = 3414701) B3414701
theorem B5122061 : Blo 2275435 5122061 := bbase (se 3 (by rfl) ⟨960386, by rfl⟩ : syracuseStep 5122061 = 1920773) (by norm_num)
theorem B3414707 : Blo 2275435 3414707 := bstep (se 1 (by rfl) ⟨2561030, by rfl⟩ : syracuseStep 3414707 = 5122061) B5122061
theorem B2276471 : Blo 2275435 2276471 := bstep (se 1 (by rfl) ⟨1707353, by rfl⟩ : syracuseStep 2276471 = 3414707) B3414707
theorem B2881165 : Blo 2275435 2881165 := bbase (se 3 (by rfl) ⟨540218, by rfl⟩ : syracuseStep 2881165 = 1080437) (by norm_num)
theorem B3841553 : Blo 2275435 3841553 := bstep (se 2 (by rfl) ⟨1440582, by rfl⟩ : syracuseStep 3841553 = 2881165) B2881165
theorem B2561035 : Blo 2275435 2561035 := bstep (se 1 (by rfl) ⟨1920776, by rfl⟩ : syracuseStep 2561035 = 3841553) B3841553
theorem B3414713 : Blo 2275435 3414713 := bstep (se 2 (by rfl) ⟨1280517, by rfl⟩ : syracuseStep 3414713 = 2561035) B2561035
theorem B2276475 : Blo 2275435 2276475 := bstep (se 1 (by rfl) ⟨1707356, by rfl⟩ : syracuseStep 2276475 = 3414713) B3414713
theorem B3461309 : Blo 2275435 3461309 := bbase (se 3 (by rfl) ⟨648995, by rfl⟩ : syracuseStep 3461309 = 1297991) (by norm_num)
theorem B2307539 : Blo 2275435 2307539 := bstep (se 1 (by rfl) ⟨1730654, by rfl⟩ : syracuseStep 2307539 = 3461309) B3461309
theorem B6153437 : Blo 2275435 6153437 := bstep (se 3 (by rfl) ⟨1153769, by rfl⟩ : syracuseStep 6153437 = 2307539) B2307539
theorem B4102291 : Blo 2275435 4102291 := bstep (se 1 (by rfl) ⟨3076718, by rfl⟩ : syracuseStep 4102291 = 6153437) B6153437
theorem B21878885 : Blo 2275435 21878885 := bstep (se 4 (by rfl) ⟨2051145, by rfl⟩ : syracuseStep 21878885 = 4102291) B4102291
theorem B14585923 : Blo 2275435 14585923 := bstep (se 1 (by rfl) ⟨10939442, by rfl⟩ : syracuseStep 14585923 = 21878885) B21878885
theorem B19447897 : Blo 2275435 19447897 := bstep (se 2 (by rfl) ⟨7292961, by rfl⟩ : syracuseStep 19447897 = 14585923) B14585923
theorem B25930529 : Blo 2275435 25930529 := bstep (se 2 (by rfl) ⟨9723948, by rfl⟩ : syracuseStep 25930529 = 19447897) B19447897
theorem B17287019 : Blo 2275435 17287019 := bstep (se 1 (by rfl) ⟨12965264, by rfl⟩ : syracuseStep 17287019 = 25930529) B25930529
theorem B11524679 : Blo 2275435 11524679 := bstep (se 1 (by rfl) ⟨8643509, by rfl⟩ : syracuseStep 11524679 = 17287019) B17287019
theorem B7683119 : Blo 2275435 7683119 := bstep (se 1 (by rfl) ⟨5762339, by rfl⟩ : syracuseStep 7683119 = 11524679) B11524679
theorem B5122079 : Blo 2275435 5122079 := bstep (se 1 (by rfl) ⟨3841559, by rfl⟩ : syracuseStep 5122079 = 7683119) B7683119
theorem B3414719 : Blo 2275435 3414719 := bstep (se 1 (by rfl) ⟨2561039, by rfl⟩ : syracuseStep 3414719 = 5122079) B5122079
theorem B2276479 : Blo 2275435 2276479 := bstep (se 1 (by rfl) ⟨1707359, by rfl⟩ : syracuseStep 2276479 = 3414719) B3414719
theorem B3414725 : Blo 2275435 3414725 := bbase (se 4 (by rfl) ⟨320130, by rfl⟩ : syracuseStep 3414725 = 640261) (by norm_num)
theorem B2276483 : Blo 2275435 2276483 := bstep (se 1 (by rfl) ⟨1707362, by rfl⟩ : syracuseStep 2276483 = 3414725) B3414725
theorem B3841573 : Blo 2275435 3841573 := bbase (se 4 (by rfl) ⟨360147, by rfl⟩ : syracuseStep 3841573 = 720295) (by norm_num)
theorem B5122097 : Blo 2275435 5122097 := bstep (se 2 (by rfl) ⟨1920786, by rfl⟩ : syracuseStep 5122097 = 3841573) B3841573
theorem B3414731 : Blo 2275435 3414731 := bstep (se 1 (by rfl) ⟨2561048, by rfl⟩ : syracuseStep 3414731 = 5122097) B5122097
theorem B2276487 : Blo 2275435 2276487 := bstep (se 1 (by rfl) ⟨1707365, by rfl⟩ : syracuseStep 2276487 = 3414731) B3414731
theorem B2561053 : Blo 2275435 2561053 := bbase (se 3 (by rfl) ⟨480197, by rfl⟩ : syracuseStep 2561053 = 960395) (by norm_num)
theorem B3414737 : Blo 2275435 3414737 := bstep (se 2 (by rfl) ⟨1280526, by rfl⟩ : syracuseStep 3414737 = 2561053) B2561053
theorem B2276491 : Blo 2275435 2276491 := bstep (se 1 (by rfl) ⟨1707368, by rfl⟩ : syracuseStep 2276491 = 3414737) B3414737
theorem B7683173 : Blo 2275435 7683173 := bbase (se 4 (by rfl) ⟨720297, by rfl⟩ : syracuseStep 7683173 = 1440595) (by norm_num)
theorem B5122115 : Blo 2275435 5122115 := bstep (se 1 (by rfl) ⟨3841586, by rfl⟩ : syracuseStep 5122115 = 7683173) B7683173
theorem B3414743 : Blo 2275435 3414743 := bstep (se 1 (by rfl) ⟨2561057, by rfl⟩ : syracuseStep 3414743 = 5122115) B5122115
theorem B2276495 : Blo 2275435 2276495 := bstep (se 1 (by rfl) ⟨1707371, by rfl⟩ : syracuseStep 2276495 = 3414743) B3414743
theorem B3414749 : Blo 2275435 3414749 := bbase (se 3 (by rfl) ⟨640265, by rfl⟩ : syracuseStep 3414749 = 1280531) (by norm_num)
theorem B2276499 : Blo 2275435 2276499 := bstep (se 1 (by rfl) ⟨1707374, by rfl⟩ : syracuseStep 2276499 = 3414749) B3414749
theorem B5122133 : Blo 2275435 5122133 := bbase (se 8 (by rfl) ⟨30012, by rfl⟩ : syracuseStep 5122133 = 60025) (by norm_num)
theorem B3414755 : Blo 2275435 3414755 := bstep (se 1 (by rfl) ⟨2561066, by rfl⟩ : syracuseStep 3414755 = 5122133) B5122133
theorem B2276503 : Blo 2275435 2276503 := bstep (se 1 (by rfl) ⟨1707377, by rfl⟩ : syracuseStep 2276503 = 3414755) B3414755
theorem B5192029 : Blo 2275435 5192029 := bbase (se 3 (by rfl) ⟨973505, by rfl⟩ : syracuseStep 5192029 = 1947011) (by norm_num)
theorem B6922705 : Blo 2275435 6922705 := bstep (se 2 (by rfl) ⟨2596014, by rfl⟩ : syracuseStep 6922705 = 5192029) B5192029
theorem B9230273 : Blo 2275435 9230273 := bstep (se 2 (by rfl) ⟨3461352, by rfl⟩ : syracuseStep 9230273 = 6922705) B6922705
theorem B6153515 : Blo 2275435 6153515 := bstep (se 1 (by rfl) ⟨4615136, by rfl⟩ : syracuseStep 6153515 = 9230273) B9230273
theorem B4102343 : Blo 2275435 4102343 := bstep (se 1 (by rfl) ⟨3076757, by rfl⟩ : syracuseStep 4102343 = 6153515) B6153515
theorem B2734895 : Blo 2275435 2734895 := bstep (se 1 (by rfl) ⟨2051171, by rfl⟩ : syracuseStep 2734895 = 4102343) B4102343
theorem B7293053 : Blo 2275435 7293053 := bstep (se 3 (by rfl) ⟨1367447, by rfl⟩ : syracuseStep 7293053 = 2734895) B2734895
theorem B4862035 : Blo 2275435 4862035 := bstep (se 1 (by rfl) ⟨3646526, by rfl⟩ : syracuseStep 4862035 = 7293053) B7293053
theorem B6482713 : Blo 2275435 6482713 := bstep (se 2 (by rfl) ⟨2431017, by rfl⟩ : syracuseStep 6482713 = 4862035) B4862035
theorem B8643617 : Blo 2275435 8643617 := bstep (se 2 (by rfl) ⟨3241356, by rfl⟩ : syracuseStep 8643617 = 6482713) B6482713
theorem B5762411 : Blo 2275435 5762411 := bstep (se 1 (by rfl) ⟨4321808, by rfl⟩ : syracuseStep 5762411 = 8643617) B8643617
theorem B3841607 : Blo 2275435 3841607 := bstep (se 1 (by rfl) ⟨2881205, by rfl⟩ : syracuseStep 3841607 = 5762411) B5762411
theorem B2561071 : Blo 2275435 2561071 := bstep (se 1 (by rfl) ⟨1920803, by rfl⟩ : syracuseStep 2561071 = 3841607) B3841607
theorem B3414761 : Blo 2275435 3414761 := bstep (se 2 (by rfl) ⟨1280535, by rfl⟩ : syracuseStep 3414761 = 2561071) B2561071
theorem B2276507 : Blo 2275435 2276507 := bstep (se 1 (by rfl) ⟨1707380, by rfl⟩ : syracuseStep 2276507 = 3414761) B3414761
theorem B3461357 : Blo 2275435 3461357 := bbase (se 3 (by rfl) ⟨649004, by rfl⟩ : syracuseStep 3461357 = 1298009) (by norm_num)
theorem B9230285 : Blo 2275435 9230285 := bstep (se 3 (by rfl) ⟨1730678, by rfl⟩ : syracuseStep 9230285 = 3461357) B3461357
theorem B24614093 : Blo 2275435 24614093 := bstep (se 3 (by rfl) ⟨4615142, by rfl⟩ : syracuseStep 24614093 = 9230285) B9230285
theorem B16409395 : Blo 2275435 16409395 := bstep (se 1 (by rfl) ⟨12307046, by rfl⟩ : syracuseStep 16409395 = 24614093) B24614093
theorem B21879193 : Blo 2275435 21879193 := bstep (se 2 (by rfl) ⟨8204697, by rfl⟩ : syracuseStep 21879193 = 16409395) B16409395
theorem B29172257 : Blo 2275435 29172257 := bstep (se 2 (by rfl) ⟨10939596, by rfl⟩ : syracuseStep 29172257 = 21879193) B21879193
theorem B19448171 : Blo 2275435 19448171 := bstep (se 1 (by rfl) ⟨14586128, by rfl⟩ : syracuseStep 19448171 = 29172257) B29172257
theorem B12965447 : Blo 2275435 12965447 := bstep (se 1 (by rfl) ⟨9724085, by rfl⟩ : syracuseStep 12965447 = 19448171) B19448171
theorem B8643631 : Blo 2275435 8643631 := bstep (se 1 (by rfl) ⟨6482723, by rfl⟩ : syracuseStep 8643631 = 12965447) B12965447
theorem B11524841 : Blo 2275435 11524841 := bstep (se 2 (by rfl) ⟨4321815, by rfl⟩ : syracuseStep 11524841 = 8643631) B8643631
theorem B7683227 : Blo 2275435 7683227 := bstep (se 1 (by rfl) ⟨5762420, by rfl⟩ : syracuseStep 7683227 = 11524841) B11524841
theorem B5122151 : Blo 2275435 5122151 := bstep (se 1 (by rfl) ⟨3841613, by rfl⟩ : syracuseStep 5122151 = 7683227) B7683227
theorem B3414767 : Blo 2275435 3414767 := bstep (se 1 (by rfl) ⟨2561075, by rfl⟩ : syracuseStep 3414767 = 5122151) B5122151
theorem B2276511 : Blo 2275435 2276511 := bstep (se 1 (by rfl) ⟨1707383, by rfl⟩ : syracuseStep 2276511 = 3414767) B3414767
theorem B3414773 : Blo 2275435 3414773 := bbase (se 5 (by rfl) ⟨160067, by rfl⟩ : syracuseStep 3414773 = 320135) (by norm_num)
theorem B2276515 : Blo 2275435 2276515 := bstep (se 1 (by rfl) ⟨1707386, by rfl⟩ : syracuseStep 2276515 = 3414773) B3414773
theorem B10939637 : Blo 2275435 10939637 := bbase (se 5 (by rfl) ⟨512795, by rfl⟩ : syracuseStep 10939637 = 1025591) (by norm_num)
theorem B7293091 : Blo 2275435 7293091 := bstep (se 1 (by rfl) ⟨5469818, by rfl⟩ : syracuseStep 7293091 = 10939637) B10939637
theorem B9724121 : Blo 2275435 9724121 := bstep (se 2 (by rfl) ⟨3646545, by rfl⟩ : syracuseStep 9724121 = 7293091) B7293091
theorem B6482747 : Blo 2275435 6482747 := bstep (se 1 (by rfl) ⟨4862060, by rfl⟩ : syracuseStep 6482747 = 9724121) B9724121
theorem B4321831 : Blo 2275435 4321831 := bstep (se 1 (by rfl) ⟨3241373, by rfl⟩ : syracuseStep 4321831 = 6482747) B6482747
theorem B5762441 : Blo 2275435 5762441 := bstep (se 2 (by rfl) ⟨2160915, by rfl⟩ : syracuseStep 5762441 = 4321831) B4321831
theorem B3841627 : Blo 2275435 3841627 := bstep (se 1 (by rfl) ⟨2881220, by rfl⟩ : syracuseStep 3841627 = 5762441) B5762441
theorem B5122169 : Blo 2275435 5122169 := bstep (se 2 (by rfl) ⟨1920813, by rfl⟩ : syracuseStep 5122169 = 3841627) B3841627
theorem B3414779 : Blo 2275435 3414779 := bstep (se 1 (by rfl) ⟨2561084, by rfl⟩ : syracuseStep 3414779 = 5122169) B5122169
theorem B2276519 : Blo 2275435 2276519 := bstep (se 1 (by rfl) ⟨1707389, by rfl⟩ : syracuseStep 2276519 = 3414779) B3414779
theorem B2561089 : Blo 2275435 2561089 := bbase (se 2 (by rfl) ⟨960408, by rfl⟩ : syracuseStep 2561089 = 1920817) (by norm_num)
theorem B3414785 : Blo 2275435 3414785 := bstep (se 2 (by rfl) ⟨1280544, by rfl⟩ : syracuseStep 3414785 = 2561089) B2561089
theorem B2276523 : Blo 2275435 2276523 := bstep (se 1 (by rfl) ⟨1707392, by rfl⟩ : syracuseStep 2276523 = 3414785) B3414785
theorem B5762461 : Blo 2275435 5762461 := bbase (se 3 (by rfl) ⟨1080461, by rfl⟩ : syracuseStep 5762461 = 2160923) (by norm_num)
theorem B7683281 : Blo 2275435 7683281 := bstep (se 2 (by rfl) ⟨2881230, by rfl⟩ : syracuseStep 7683281 = 5762461) B5762461
theorem B5122187 : Blo 2275435 5122187 := bstep (se 1 (by rfl) ⟨3841640, by rfl⟩ : syracuseStep 5122187 = 7683281) B7683281
theorem B3414791 : Blo 2275435 3414791 := bstep (se 1 (by rfl) ⟨2561093, by rfl⟩ : syracuseStep 3414791 = 5122187) B5122187
theorem B2276527 : Blo 2275435 2276527 := bstep (se 1 (by rfl) ⟨1707395, by rfl⟩ : syracuseStep 2276527 = 3414791) B3414791
theorem B3414797 : Blo 2275435 3414797 := bbase (se 3 (by rfl) ⟨640274, by rfl⟩ : syracuseStep 3414797 = 1280549) (by norm_num)
theorem B2276531 : Blo 2275435 2276531 := bstep (se 1 (by rfl) ⟨1707398, by rfl⟩ : syracuseStep 2276531 = 3414797) B3414797
theorem B5122205 : Blo 2275435 5122205 := bbase (se 3 (by rfl) ⟨960413, by rfl⟩ : syracuseStep 5122205 = 1920827) (by norm_num)
theorem B3414803 : Blo 2275435 3414803 := bstep (se 1 (by rfl) ⟨2561102, by rfl⟩ : syracuseStep 3414803 = 5122205) B5122205
theorem B2276535 : Blo 2275435 2276535 := bstep (se 1 (by rfl) ⟨1707401, by rfl⟩ : syracuseStep 2276535 = 3414803) B3414803
theorem B3841661 : Blo 2275435 3841661 := bbase (se 3 (by rfl) ⟨720311, by rfl⟩ : syracuseStep 3841661 = 1440623) (by norm_num)
theorem B2561107 : Blo 2275435 2561107 := bstep (se 1 (by rfl) ⟨1920830, by rfl⟩ : syracuseStep 2561107 = 3841661) B3841661
theorem B3414809 : Blo 2275435 3414809 := bstep (se 2 (by rfl) ⟨1280553, by rfl⟩ : syracuseStep 3414809 = 2561107) B2561107
theorem B2276539 : Blo 2275435 2276539 := bstep (se 1 (by rfl) ⟨1707404, by rfl⟩ : syracuseStep 2276539 = 3414809) B3414809
theorem B3797885 : Blo 2275435 3797885 := bbase (se 3 (by rfl) ⟨712103, by rfl⟩ : syracuseStep 3797885 = 1424207) (by norm_num)
theorem B10127693 : Blo 2275435 10127693 := bstep (se 3 (by rfl) ⟨1898942, by rfl⟩ : syracuseStep 10127693 = 3797885) B3797885
theorem B27007181 : Blo 2275435 27007181 := bstep (se 3 (by rfl) ⟨5063846, by rfl⟩ : syracuseStep 27007181 = 10127693) B10127693
theorem B18004787 : Blo 2275435 18004787 := bstep (se 1 (by rfl) ⟨13503590, by rfl⟩ : syracuseStep 18004787 = 27007181) B27007181
theorem B12003191 : Blo 2275435 12003191 := bstep (se 1 (by rfl) ⟨9002393, by rfl⟩ : syracuseStep 12003191 = 18004787) B18004787
theorem B8002127 : Blo 2275435 8002127 := bstep (se 1 (by rfl) ⟨6001595, by rfl⟩ : syracuseStep 8002127 = 12003191) B12003191
theorem B5334751 : Blo 2275435 5334751 := bstep (se 1 (by rfl) ⟨4001063, by rfl⟩ : syracuseStep 5334751 = 8002127) B8002127
theorem B28452005 : Blo 2275435 28452005 := bstep (se 4 (by rfl) ⟨2667375, by rfl⟩ : syracuseStep 28452005 = 5334751) B5334751
theorem B18968003 : Blo 2275435 18968003 := bstep (se 1 (by rfl) ⟨14226002, by rfl⟩ : syracuseStep 18968003 = 28452005) B28452005
theorem B12645335 : Blo 2275435 12645335 := bstep (se 1 (by rfl) ⟨9484001, by rfl⟩ : syracuseStep 12645335 = 18968003) B18968003
theorem B33720893 : Blo 2275435 33720893 := bstep (se 3 (by rfl) ⟨6322667, by rfl⟩ : syracuseStep 33720893 = 12645335) B12645335
theorem B22480595 : Blo 2275435 22480595 := bstep (se 1 (by rfl) ⟨16860446, by rfl⟩ : syracuseStep 22480595 = 33720893) B33720893
theorem B14987063 : Blo 2275435 14987063 := bstep (se 1 (by rfl) ⟨11240297, by rfl⟩ : syracuseStep 14987063 = 22480595) B22480595
theorem B39965501 : Blo 2275435 39965501 := bstep (se 3 (by rfl) ⟨7493531, by rfl⟩ : syracuseStep 39965501 = 14987063) B14987063
theorem B26643667 : Blo 2275435 26643667 := bstep (se 1 (by rfl) ⟨19982750, by rfl⟩ : syracuseStep 26643667 = 39965501) B39965501
theorem B35524889 : Blo 2275435 35524889 := bstep (se 2 (by rfl) ⟨13321833, by rfl⟩ : syracuseStep 35524889 = 26643667) B26643667
theorem B23683259 : Blo 2275435 23683259 := bstep (se 1 (by rfl) ⟨17762444, by rfl⟩ : syracuseStep 23683259 = 35524889) B35524889
theorem B63155357 : Blo 2275435 63155357 := bstep (se 3 (by rfl) ⟨11841629, by rfl⟩ : syracuseStep 63155357 = 23683259) B23683259
theorem B42103571 : Blo 2275435 42103571 := bstep (se 1 (by rfl) ⟨31577678, by rfl⟩ : syracuseStep 42103571 = 63155357) B63155357
theorem B112276189 : Blo 2275435 112276189 := bstep (se 3 (by rfl) ⟨21051785, by rfl⟩ : syracuseStep 112276189 = 42103571) B42103571
theorem B598806341 : Blo 2275435 598806341 := bstep (se 4 (by rfl) ⟨56138094, by rfl⟩ : syracuseStep 598806341 = 112276189) B112276189
theorem B399204227 : Blo 2275435 399204227 := bstep (se 1 (by rfl) ⟨299403170, by rfl⟩ : syracuseStep 399204227 = 598806341) B598806341
theorem B266136151 : Blo 2275435 266136151 := bstep (se 1 (by rfl) ⟨199602113, by rfl⟩ : syracuseStep 266136151 = 399204227) B399204227
theorem B354848201 : Blo 2275435 354848201 := bstep (se 2 (by rfl) ⟨133068075, by rfl⟩ : syracuseStep 354848201 = 266136151) B266136151
theorem B236565467 : Blo 2275435 236565467 := bstep (se 1 (by rfl) ⟨177424100, by rfl⟩ : syracuseStep 236565467 = 354848201) B354848201
theorem B157710311 : Blo 2275435 157710311 := bstep (se 1 (by rfl) ⟨118282733, by rfl⟩ : syracuseStep 157710311 = 236565467) B236565467
theorem B105140207 : Blo 2275435 105140207 := bstep (se 1 (by rfl) ⟨78855155, by rfl⟩ : syracuseStep 105140207 = 157710311) B157710311
theorem B70093471 : Blo 2275435 70093471 := bstep (se 1 (by rfl) ⟨52570103, by rfl⟩ : syracuseStep 70093471 = 105140207) B105140207
theorem B93457961 : Blo 2275435 93457961 := bstep (se 2 (by rfl) ⟨35046735, by rfl⟩ : syracuseStep 93457961 = 70093471) B70093471
theorem B62305307 : Blo 2275435 62305307 := bstep (se 1 (by rfl) ⟨46728980, by rfl⟩ : syracuseStep 62305307 = 93457961) B93457961
theorem B41536871 : Blo 2275435 41536871 := bstep (se 1 (by rfl) ⟨31152653, by rfl⟩ : syracuseStep 41536871 = 62305307) B62305307
theorem B27691247 : Blo 2275435 27691247 := bstep (se 1 (by rfl) ⟨20768435, by rfl⟩ : syracuseStep 27691247 = 41536871) B41536871
theorem B18460831 : Blo 2275435 18460831 := bstep (se 1 (by rfl) ⟨13845623, by rfl⟩ : syracuseStep 18460831 = 27691247) B27691247
theorem B24614441 : Blo 2275435 24614441 := bstep (se 2 (by rfl) ⟨9230415, by rfl⟩ : syracuseStep 24614441 = 18460831) B18460831
theorem B16409627 : Blo 2275435 16409627 := bstep (se 1 (by rfl) ⟨12307220, by rfl⟩ : syracuseStep 16409627 = 24614441) B24614441
theorem B10939751 : Blo 2275435 10939751 := bstep (se 1 (by rfl) ⟨8204813, by rfl⟩ : syracuseStep 10939751 = 16409627) B16409627
theorem B7293167 : Blo 2275435 7293167 := bstep (se 1 (by rfl) ⟨5469875, by rfl⟩ : syracuseStep 7293167 = 10939751) B10939751
theorem B4862111 : Blo 2275435 4862111 := bstep (se 1 (by rfl) ⟨3646583, by rfl⟩ : syracuseStep 4862111 = 7293167) B7293167
theorem B12965629 : Blo 2275435 12965629 := bstep (se 3 (by rfl) ⟨2431055, by rfl⟩ : syracuseStep 12965629 = 4862111) B4862111
theorem B17287505 : Blo 2275435 17287505 := bstep (se 2 (by rfl) ⟨6482814, by rfl⟩ : syracuseStep 17287505 = 12965629) B12965629
theorem B11525003 : Blo 2275435 11525003 := bstep (se 1 (by rfl) ⟨8643752, by rfl⟩ : syracuseStep 11525003 = 17287505) B17287505
theorem B7683335 : Blo 2275435 7683335 := bstep (se 1 (by rfl) ⟨5762501, by rfl⟩ : syracuseStep 7683335 = 11525003) B11525003
theorem B5122223 : Blo 2275435 5122223 := bstep (se 1 (by rfl) ⟨3841667, by rfl⟩ : syracuseStep 5122223 = 7683335) B7683335
theorem B3414815 : Blo 2275435 3414815 := bstep (se 1 (by rfl) ⟨2561111, by rfl⟩ : syracuseStep 3414815 = 5122223) B5122223
theorem B2276543 : Blo 2275435 2276543 := bstep (se 1 (by rfl) ⟨1707407, by rfl⟩ : syracuseStep 2276543 = 3414815) B3414815
theorem B3414821 : Blo 2275435 3414821 := bbase (se 4 (by rfl) ⟨320139, by rfl⟩ : syracuseStep 3414821 = 640279) (by norm_num)
theorem B2276547 : Blo 2275435 2276547 := bstep (se 1 (by rfl) ⟨1707410, by rfl⟩ : syracuseStep 2276547 = 3414821) B3414821
theorem B2881261 : Blo 2275435 2881261 := bbase (se 3 (by rfl) ⟨540236, by rfl⟩ : syracuseStep 2881261 = 1080473) (by norm_num)
theorem B3841681 : Blo 2275435 3841681 := bstep (se 2 (by rfl) ⟨1440630, by rfl⟩ : syracuseStep 3841681 = 2881261) B2881261
theorem B5122241 : Blo 2275435 5122241 := bstep (se 2 (by rfl) ⟨1920840, by rfl⟩ : syracuseStep 5122241 = 3841681) B3841681
theorem B3414827 : Blo 2275435 3414827 := bstep (se 1 (by rfl) ⟨2561120, by rfl⟩ : syracuseStep 3414827 = 5122241) B5122241
theorem B2276551 : Blo 2275435 2276551 := bstep (se 1 (by rfl) ⟨1707413, by rfl⟩ : syracuseStep 2276551 = 3414827) B3414827
theorem B2561125 : Blo 2275435 2561125 := bbase (se 4 (by rfl) ⟨240105, by rfl⟩ : syracuseStep 2561125 = 480211) (by norm_num)
theorem B3414833 : Blo 2275435 3414833 := bstep (se 2 (by rfl) ⟨1280562, by rfl⟩ : syracuseStep 3414833 = 2561125) B2561125
theorem B2276555 : Blo 2275435 2276555 := bstep (se 1 (by rfl) ⟨1707416, by rfl⟩ : syracuseStep 2276555 = 3414833) B3414833
theorem B2431073 : Blo 2275435 2431073 := bbase (se 2 (by rfl) ⟨911652, by rfl⟩ : syracuseStep 2431073 = 1823305) (by norm_num)
theorem B6482861 : Blo 2275435 6482861 := bstep (se 3 (by rfl) ⟨1215536, by rfl⟩ : syracuseStep 6482861 = 2431073) B2431073
theorem B4321907 : Blo 2275435 4321907 := bstep (se 1 (by rfl) ⟨3241430, by rfl⟩ : syracuseStep 4321907 = 6482861) B6482861
theorem B2881271 : Blo 2275435 2881271 := bstep (se 1 (by rfl) ⟨2160953, by rfl⟩ : syracuseStep 2881271 = 4321907) B4321907
theorem B7683389 : Blo 2275435 7683389 := bstep (se 3 (by rfl) ⟨1440635, by rfl⟩ : syracuseStep 7683389 = 2881271) B2881271
theorem B5122259 : Blo 2275435 5122259 := bstep (se 1 (by rfl) ⟨3841694, by rfl⟩ : syracuseStep 5122259 = 7683389) B7683389
theorem B3414839 : Blo 2275435 3414839 := bstep (se 1 (by rfl) ⟨2561129, by rfl⟩ : syracuseStep 3414839 = 5122259) B5122259
theorem B2276559 : Blo 2275435 2276559 := bstep (se 1 (by rfl) ⟨1707419, by rfl⟩ : syracuseStep 2276559 = 3414839) B3414839
theorem B3414845 : Blo 2275435 3414845 := bbase (se 3 (by rfl) ⟨640283, by rfl⟩ : syracuseStep 3414845 = 1280567) (by norm_num)
theorem B2276563 : Blo 2275435 2276563 := bstep (se 1 (by rfl) ⟨1707422, by rfl⟩ : syracuseStep 2276563 = 3414845) B3414845
theorem B5122277 : Blo 2275435 5122277 := bbase (se 4 (by rfl) ⟨480213, by rfl⟩ : syracuseStep 5122277 = 960427) (by norm_num)
theorem B3414851 : Blo 2275435 3414851 := bstep (se 1 (by rfl) ⟨2561138, by rfl⟩ : syracuseStep 3414851 = 5122277) B5122277
theorem B2276567 : Blo 2275435 2276567 := bstep (se 1 (by rfl) ⟨1707425, by rfl⟩ : syracuseStep 2276567 = 3414851) B3414851
theorem B5762573 : Blo 2275435 5762573 := bbase (se 3 (by rfl) ⟨1080482, by rfl⟩ : syracuseStep 5762573 = 2160965) (by norm_num)
theorem B3841715 : Blo 2275435 3841715 := bstep (se 1 (by rfl) ⟨2881286, by rfl⟩ : syracuseStep 3841715 = 5762573) B5762573
theorem B2561143 : Blo 2275435 2561143 := bstep (se 1 (by rfl) ⟨1920857, by rfl⟩ : syracuseStep 2561143 = 3841715) B3841715
theorem B3414857 : Blo 2275435 3414857 := bstep (se 2 (by rfl) ⟨1280571, by rfl⟩ : syracuseStep 3414857 = 2561143) B2561143
theorem B2276571 : Blo 2275435 2276571 := bstep (se 1 (by rfl) ⟨1707428, by rfl⟩ : syracuseStep 2276571 = 3414857) B3414857
theorem B3241453 : Blo 2275435 3241453 := bbase (se 3 (by rfl) ⟨607772, by rfl⟩ : syracuseStep 3241453 = 1215545) (by norm_num)
theorem B4321937 : Blo 2275435 4321937 := bstep (se 2 (by rfl) ⟨1620726, by rfl⟩ : syracuseStep 4321937 = 3241453) B3241453
theorem B11525165 : Blo 2275435 11525165 := bstep (se 3 (by rfl) ⟨2160968, by rfl⟩ : syracuseStep 11525165 = 4321937) B4321937
theorem B7683443 : Blo 2275435 7683443 := bstep (se 1 (by rfl) ⟨5762582, by rfl⟩ : syracuseStep 7683443 = 11525165) B11525165
theorem B5122295 : Blo 2275435 5122295 := bstep (se 1 (by rfl) ⟨3841721, by rfl⟩ : syracuseStep 5122295 = 7683443) B7683443
theorem B3414863 : Blo 2275435 3414863 := bstep (se 1 (by rfl) ⟨2561147, by rfl⟩ : syracuseStep 3414863 = 5122295) B5122295
theorem B2276575 : Blo 2275435 2276575 := bstep (se 1 (by rfl) ⟨1707431, by rfl⟩ : syracuseStep 2276575 = 3414863) B3414863
theorem B3414869 : Blo 2275435 3414869 := bbase (se 9 (by rfl) ⟨10004, by rfl⟩ : syracuseStep 3414869 = 20009) (by norm_num)
theorem B2276579 : Blo 2275435 2276579 := bstep (se 1 (by rfl) ⟨1707434, by rfl⟩ : syracuseStep 2276579 = 3414869) B3414869
theorem B4862197 : Blo 2275435 4862197 := bbase (se 5 (by rfl) ⟨227915, by rfl⟩ : syracuseStep 4862197 = 455831) (by norm_num)
theorem B6482929 : Blo 2275435 6482929 := bstep (se 2 (by rfl) ⟨2431098, by rfl⟩ : syracuseStep 6482929 = 4862197) B4862197
theorem B8643905 : Blo 2275435 8643905 := bstep (se 2 (by rfl) ⟨3241464, by rfl⟩ : syracuseStep 8643905 = 6482929) B6482929
theorem B5762603 : Blo 2275435 5762603 := bstep (se 1 (by rfl) ⟨4321952, by rfl⟩ : syracuseStep 5762603 = 8643905) B8643905
theorem B3841735 : Blo 2275435 3841735 := bstep (se 1 (by rfl) ⟨2881301, by rfl⟩ : syracuseStep 3841735 = 5762603) B5762603
theorem B5122313 : Blo 2275435 5122313 := bstep (se 2 (by rfl) ⟨1920867, by rfl⟩ : syracuseStep 5122313 = 3841735) B3841735
theorem B3414875 : Blo 2275435 3414875 := bstep (se 1 (by rfl) ⟨2561156, by rfl⟩ : syracuseStep 3414875 = 5122313) B5122313
theorem B2276583 : Blo 2275435 2276583 := bstep (se 1 (by rfl) ⟨1707437, by rfl⟩ : syracuseStep 2276583 = 3414875) B3414875
theorem B2561161 : Blo 2275435 2561161 := bbase (se 2 (by rfl) ⟨960435, by rfl⟩ : syracuseStep 2561161 = 1920871) (by norm_num)
theorem B3414881 : Blo 2275435 3414881 := bstep (se 2 (by rfl) ⟨1280580, by rfl⟩ : syracuseStep 3414881 = 2561161) B2561161
theorem B2276587 : Blo 2275435 2276587 := bstep (se 1 (by rfl) ⟨1707440, by rfl⟩ : syracuseStep 2276587 = 3414881) B3414881
theorem B4102493 : Blo 2275435 4102493 := bbase (se 3 (by rfl) ⟨769217, by rfl⟩ : syracuseStep 4102493 = 1538435) (by norm_num)
theorem B43759925 : Blo 2275435 43759925 := bstep (se 5 (by rfl) ⟨2051246, by rfl⟩ : syracuseStep 43759925 = 4102493) B4102493
theorem B29173283 : Blo 2275435 29173283 := bstep (se 1 (by rfl) ⟨21879962, by rfl⟩ : syracuseStep 29173283 = 43759925) B43759925
theorem B19448855 : Blo 2275435 19448855 := bstep (se 1 (by rfl) ⟨14586641, by rfl⟩ : syracuseStep 19448855 = 29173283) B29173283
theorem B12965903 : Blo 2275435 12965903 := bstep (se 1 (by rfl) ⟨9724427, by rfl⟩ : syracuseStep 12965903 = 19448855) B19448855
theorem B8643935 : Blo 2275435 8643935 := bstep (se 1 (by rfl) ⟨6482951, by rfl⟩ : syracuseStep 8643935 = 12965903) B12965903
theorem B5762623 : Blo 2275435 5762623 := bstep (se 1 (by rfl) ⟨4321967, by rfl⟩ : syracuseStep 5762623 = 8643935) B8643935
theorem B7683497 : Blo 2275435 7683497 := bstep (se 2 (by rfl) ⟨2881311, by rfl⟩ : syracuseStep 7683497 = 5762623) B5762623
theorem B5122331 : Blo 2275435 5122331 := bstep (se 1 (by rfl) ⟨3841748, by rfl⟩ : syracuseStep 5122331 = 7683497) B7683497
theorem B3414887 : Blo 2275435 3414887 := bstep (se 1 (by rfl) ⟨2561165, by rfl⟩ : syracuseStep 3414887 = 5122331) B5122331
theorem B2276591 : Blo 2275435 2276591 := bstep (se 1 (by rfl) ⟨1707443, by rfl⟩ : syracuseStep 2276591 = 3414887) B3414887
theorem B3414893 : Blo 2275435 3414893 := bbase (se 3 (by rfl) ⟨640292, by rfl⟩ : syracuseStep 3414893 = 1280585) (by norm_num)
theorem B2276595 : Blo 2275435 2276595 := bstep (se 1 (by rfl) ⟨1707446, by rfl⟩ : syracuseStep 2276595 = 3414893) B3414893
theorem B5122349 : Blo 2275435 5122349 := bbase (se 3 (by rfl) ⟨960440, by rfl⟩ : syracuseStep 5122349 = 1920881) (by norm_num)
theorem B3414899 : Blo 2275435 3414899 := bstep (se 1 (by rfl) ⟨2561174, by rfl⟩ : syracuseStep 3414899 = 5122349) B5122349
theorem B2276599 : Blo 2275435 2276599 := bstep (se 1 (by rfl) ⟨1707449, by rfl⟩ : syracuseStep 2276599 = 3414899) B3414899
theorem B5470021 : Blo 2275435 5470021 := bbase (se 4 (by rfl) ⟨512814, by rfl⟩ : syracuseStep 5470021 = 1025629) (by norm_num)
theorem B7293361 : Blo 2275435 7293361 := bstep (se 2 (by rfl) ⟨2735010, by rfl⟩ : syracuseStep 7293361 = 5470021) B5470021
theorem B9724481 : Blo 2275435 9724481 := bstep (se 2 (by rfl) ⟨3646680, by rfl⟩ : syracuseStep 9724481 = 7293361) B7293361
theorem B6482987 : Blo 2275435 6482987 := bstep (se 1 (by rfl) ⟨4862240, by rfl⟩ : syracuseStep 6482987 = 9724481) B9724481
theorem B4321991 : Blo 2275435 4321991 := bstep (se 1 (by rfl) ⟨3241493, by rfl⟩ : syracuseStep 4321991 = 6482987) B6482987
theorem B2881327 : Blo 2275435 2881327 := bstep (se 1 (by rfl) ⟨2160995, by rfl⟩ : syracuseStep 2881327 = 4321991) B4321991
theorem B3841769 : Blo 2275435 3841769 := bstep (se 2 (by rfl) ⟨1440663, by rfl⟩ : syracuseStep 3841769 = 2881327) B2881327
theorem B2561179 : Blo 2275435 2561179 := bstep (se 1 (by rfl) ⟨1920884, by rfl⟩ : syracuseStep 2561179 = 3841769) B3841769
theorem B3414905 : Blo 2275435 3414905 := bstep (se 2 (by rfl) ⟨1280589, by rfl⟩ : syracuseStep 3414905 = 2561179) B2561179
theorem B2276603 : Blo 2275435 2276603 := bstep (se 1 (by rfl) ⟨1707452, by rfl⟩ : syracuseStep 2276603 = 3414905) B3414905
theorem B39428693 : Blo 2275435 39428693 := bbase (se 8 (by rfl) ⟨231027, by rfl⟩ : syracuseStep 39428693 = 462055) (by norm_num)
theorem B26285795 : Blo 2275435 26285795 := bstep (se 1 (by rfl) ⟨19714346, by rfl⟩ : syracuseStep 26285795 = 39428693) B39428693
theorem B17523863 : Blo 2275435 17523863 := bstep (se 1 (by rfl) ⟨13142897, by rfl⟩ : syracuseStep 17523863 = 26285795) B26285795
theorem B11682575 : Blo 2275435 11682575 := bstep (se 1 (by rfl) ⟨8761931, by rfl⟩ : syracuseStep 11682575 = 17523863) B17523863
theorem B7788383 : Blo 2275435 7788383 := bstep (se 1 (by rfl) ⟨5841287, by rfl⟩ : syracuseStep 7788383 = 11682575) B11682575
theorem B5192255 : Blo 2275435 5192255 := bstep (se 1 (by rfl) ⟨3894191, by rfl⟩ : syracuseStep 5192255 = 7788383) B7788383
theorem B3461503 : Blo 2275435 3461503 := bstep (se 1 (by rfl) ⟨2596127, by rfl⟩ : syracuseStep 3461503 = 5192255) B5192255
theorem B4615337 : Blo 2275435 4615337 := bstep (se 2 (by rfl) ⟨1730751, by rfl⟩ : syracuseStep 4615337 = 3461503) B3461503
theorem B12307565 : Blo 2275435 12307565 := bstep (se 3 (by rfl) ⟨2307668, by rfl⟩ : syracuseStep 12307565 = 4615337) B4615337
theorem B32820173 : Blo 2275435 32820173 := bstep (se 3 (by rfl) ⟨6153782, by rfl⟩ : syracuseStep 32820173 = 12307565) B12307565
theorem B21880115 : Blo 2275435 21880115 := bstep (se 1 (by rfl) ⟨16410086, by rfl⟩ : syracuseStep 21880115 = 32820173) B32820173
theorem B14586743 : Blo 2275435 14586743 := bstep (se 1 (by rfl) ⟨10940057, by rfl⟩ : syracuseStep 14586743 = 21880115) B21880115
theorem B38897981 : Blo 2275435 38897981 := bstep (se 3 (by rfl) ⟨7293371, by rfl⟩ : syracuseStep 38897981 = 14586743) B14586743
theorem B25931987 : Blo 2275435 25931987 := bstep (se 1 (by rfl) ⟨19448990, by rfl⟩ : syracuseStep 25931987 = 38897981) B38897981
theorem B17287991 : Blo 2275435 17287991 := bstep (se 1 (by rfl) ⟨12965993, by rfl⟩ : syracuseStep 17287991 = 25931987) B25931987
theorem B11525327 : Blo 2275435 11525327 := bstep (se 1 (by rfl) ⟨8643995, by rfl⟩ : syracuseStep 11525327 = 17287991) B17287991
theorem B7683551 : Blo 2275435 7683551 := bstep (se 1 (by rfl) ⟨5762663, by rfl⟩ : syracuseStep 7683551 = 11525327) B11525327
theorem B5122367 : Blo 2275435 5122367 := bstep (se 1 (by rfl) ⟨3841775, by rfl⟩ : syracuseStep 5122367 = 7683551) B7683551
theorem B3414911 : Blo 2275435 3414911 := bstep (se 1 (by rfl) ⟨2561183, by rfl⟩ : syracuseStep 3414911 = 5122367) B5122367
theorem B2276607 : Blo 2275435 2276607 := bstep (se 1 (by rfl) ⟨1707455, by rfl⟩ : syracuseStep 2276607 = 3414911) B3414911
theorem B3414917 : Blo 2275435 3414917 := bbase (se 4 (by rfl) ⟨320148, by rfl⟩ : syracuseStep 3414917 = 640297) (by norm_num)
theorem B2276611 : Blo 2275435 2276611 := bstep (se 1 (by rfl) ⟨1707458, by rfl⟩ : syracuseStep 2276611 = 3414917) B3414917
theorem B3841789 : Blo 2275435 3841789 := bbase (se 3 (by rfl) ⟨720335, by rfl⟩ : syracuseStep 3841789 = 1440671) (by norm_num)
theorem B5122385 : Blo 2275435 5122385 := bstep (se 2 (by rfl) ⟨1920894, by rfl⟩ : syracuseStep 5122385 = 3841789) B3841789
theorem B3414923 : Blo 2275435 3414923 := bstep (se 1 (by rfl) ⟨2561192, by rfl⟩ : syracuseStep 3414923 = 5122385) B5122385
theorem B2276615 : Blo 2275435 2276615 := bstep (se 1 (by rfl) ⟨1707461, by rfl⟩ : syracuseStep 2276615 = 3414923) B3414923
theorem B2561197 : Blo 2275435 2561197 := bbase (se 3 (by rfl) ⟨480224, by rfl⟩ : syracuseStep 2561197 = 960449) (by norm_num)
theorem B3414929 : Blo 2275435 3414929 := bstep (se 2 (by rfl) ⟨1280598, by rfl⟩ : syracuseStep 3414929 = 2561197) B2561197
theorem B2276619 : Blo 2275435 2276619 := bstep (se 1 (by rfl) ⟨1707464, by rfl⟩ : syracuseStep 2276619 = 3414929) B3414929
theorem B7683605 : Blo 2275435 7683605 := bbase (se 6 (by rfl) ⟨180084, by rfl⟩ : syracuseStep 7683605 = 360169) (by norm_num)
theorem B5122403 : Blo 2275435 5122403 := bstep (se 1 (by rfl) ⟨3841802, by rfl⟩ : syracuseStep 5122403 = 7683605) B7683605
theorem B3414935 : Blo 2275435 3414935 := bstep (se 1 (by rfl) ⟨2561201, by rfl⟩ : syracuseStep 3414935 = 5122403) B5122403
theorem B2276623 : Blo 2275435 2276623 := bstep (se 1 (by rfl) ⟨1707467, by rfl⟩ : syracuseStep 2276623 = 3414935) B3414935
theorem B3414941 : Blo 2275435 3414941 := bbase (se 3 (by rfl) ⟨640301, by rfl⟩ : syracuseStep 3414941 = 1280603) (by norm_num)
theorem B2276627 : Blo 2275435 2276627 := bstep (se 1 (by rfl) ⟨1707470, by rfl⟩ : syracuseStep 2276627 = 3414941) B3414941
theorem B5122421 : Blo 2275435 5122421 := bbase (se 5 (by rfl) ⟨240113, by rfl⟩ : syracuseStep 5122421 = 480227) (by norm_num)
theorem B3414947 : Blo 2275435 3414947 := bstep (se 1 (by rfl) ⟨2561210, by rfl⟩ : syracuseStep 3414947 = 5122421) B5122421
theorem B2276631 : Blo 2275435 2276631 := bstep (se 1 (by rfl) ⟨1707473, by rfl⟩ : syracuseStep 2276631 = 3414947) B3414947
theorem B4102573 : Blo 2275435 4102573 := bbase (se 3 (by rfl) ⟨769232, by rfl⟩ : syracuseStep 4102573 = 1538465) (by norm_num)
theorem B5470097 : Blo 2275435 5470097 := bstep (se 2 (by rfl) ⟨2051286, by rfl⟩ : syracuseStep 5470097 = 4102573) B4102573
theorem B14586925 : Blo 2275435 14586925 := bstep (se 3 (by rfl) ⟨2735048, by rfl⟩ : syracuseStep 14586925 = 5470097) B5470097
theorem B19449233 : Blo 2275435 19449233 := bstep (se 2 (by rfl) ⟨7293462, by rfl⟩ : syracuseStep 19449233 = 14586925) B14586925
theorem B12966155 : Blo 2275435 12966155 := bstep (se 1 (by rfl) ⟨9724616, by rfl⟩ : syracuseStep 12966155 = 19449233) B19449233
theorem B8644103 : Blo 2275435 8644103 := bstep (se 1 (by rfl) ⟨6483077, by rfl⟩ : syracuseStep 8644103 = 12966155) B12966155
theorem B5762735 : Blo 2275435 5762735 := bstep (se 1 (by rfl) ⟨4322051, by rfl⟩ : syracuseStep 5762735 = 8644103) B8644103
theorem B3841823 : Blo 2275435 3841823 := bstep (se 1 (by rfl) ⟨2881367, by rfl⟩ : syracuseStep 3841823 = 5762735) B5762735
theorem B2561215 : Blo 2275435 2561215 := bstep (se 1 (by rfl) ⟨1920911, by rfl⟩ : syracuseStep 2561215 = 3841823) B3841823
theorem B3414953 : Blo 2275435 3414953 := bstep (se 2 (by rfl) ⟨1280607, by rfl⟩ : syracuseStep 3414953 = 2561215) B2561215
theorem B2276635 : Blo 2275435 2276635 := bstep (se 1 (by rfl) ⟨1707476, by rfl⟩ : syracuseStep 2276635 = 3414953) B3414953
theorem B8644117 : Blo 2275435 8644117 := bbase (se 6 (by rfl) ⟨202596, by rfl⟩ : syracuseStep 8644117 = 405193) (by norm_num)
theorem B11525489 : Blo 2275435 11525489 := bstep (se 2 (by rfl) ⟨4322058, by rfl⟩ : syracuseStep 11525489 = 8644117) B8644117
theorem B7683659 : Blo 2275435 7683659 := bstep (se 1 (by rfl) ⟨5762744, by rfl⟩ : syracuseStep 7683659 = 11525489) B11525489
theorem B5122439 : Blo 2275435 5122439 := bstep (se 1 (by rfl) ⟨3841829, by rfl⟩ : syracuseStep 5122439 = 7683659) B7683659
theorem B3414959 : Blo 2275435 3414959 := bstep (se 1 (by rfl) ⟨2561219, by rfl⟩ : syracuseStep 3414959 = 5122439) B5122439
theorem B2276639 : Blo 2275435 2276639 := bstep (se 1 (by rfl) ⟨1707479, by rfl⟩ : syracuseStep 2276639 = 3414959) B3414959
theorem B3414965 : Blo 2275435 3414965 := bbase (se 5 (by rfl) ⟨160076, by rfl⟩ : syracuseStep 3414965 = 320153) (by norm_num)
theorem B2276643 : Blo 2275435 2276643 := bstep (se 1 (by rfl) ⟨1707482, by rfl⟩ : syracuseStep 2276643 = 3414965) B3414965
theorem B5762765 : Blo 2275435 5762765 := bbase (se 3 (by rfl) ⟨1080518, by rfl⟩ : syracuseStep 5762765 = 2161037) (by norm_num)
theorem B3841843 : Blo 2275435 3841843 := bstep (se 1 (by rfl) ⟨2881382, by rfl⟩ : syracuseStep 3841843 = 5762765) B5762765
theorem B5122457 : Blo 2275435 5122457 := bstep (se 2 (by rfl) ⟨1920921, by rfl⟩ : syracuseStep 5122457 = 3841843) B3841843
theorem B3414971 : Blo 2275435 3414971 := bstep (se 1 (by rfl) ⟨2561228, by rfl⟩ : syracuseStep 3414971 = 5122457) B5122457
theorem B2276647 : Blo 2275435 2276647 := bstep (se 1 (by rfl) ⟨1707485, by rfl⟩ : syracuseStep 2276647 = 3414971) B3414971
theorem B2561233 : Blo 2275435 2561233 := bbase (se 2 (by rfl) ⟨960462, by rfl⟩ : syracuseStep 2561233 = 1920925) (by norm_num)
theorem B3414977 : Blo 2275435 3414977 := bstep (se 2 (by rfl) ⟨1280616, by rfl⟩ : syracuseStep 3414977 = 2561233) B2561233
theorem B2276651 : Blo 2275435 2276651 := bstep (se 1 (by rfl) ⟨1707488, by rfl⟩ : syracuseStep 2276651 = 3414977) B3414977
theorem B3076957 : Blo 2275435 3076957 := bbase (se 3 (by rfl) ⟨576929, by rfl⟩ : syracuseStep 3076957 = 1153859) (by norm_num)
theorem B16410437 : Blo 2275435 16410437 := bstep (se 4 (by rfl) ⟨1538478, by rfl⟩ : syracuseStep 16410437 = 3076957) B3076957
theorem B10940291 : Blo 2275435 10940291 := bstep (se 1 (by rfl) ⟨8205218, by rfl⟩ : syracuseStep 10940291 = 16410437) B16410437
theorem B7293527 : Blo 2275435 7293527 := bstep (se 1 (by rfl) ⟨5470145, by rfl⟩ : syracuseStep 7293527 = 10940291) B10940291
theorem B4862351 : Blo 2275435 4862351 := bstep (se 1 (by rfl) ⟨3646763, by rfl⟩ : syracuseStep 4862351 = 7293527) B7293527
theorem B3241567 : Blo 2275435 3241567 := bstep (se 1 (by rfl) ⟨2431175, by rfl⟩ : syracuseStep 3241567 = 4862351) B4862351
theorem B4322089 : Blo 2275435 4322089 := bstep (se 2 (by rfl) ⟨1620783, by rfl⟩ : syracuseStep 4322089 = 3241567) B3241567
theorem B5762785 : Blo 2275435 5762785 := bstep (se 2 (by rfl) ⟨2161044, by rfl⟩ : syracuseStep 5762785 = 4322089) B4322089
theorem B7683713 : Blo 2275435 7683713 := bstep (se 2 (by rfl) ⟨2881392, by rfl⟩ : syracuseStep 7683713 = 5762785) B5762785
theorem B5122475 : Blo 2275435 5122475 := bstep (se 1 (by rfl) ⟨3841856, by rfl⟩ : syracuseStep 5122475 = 7683713) B7683713
theorem B3414983 : Blo 2275435 3414983 := bstep (se 1 (by rfl) ⟨2561237, by rfl⟩ : syracuseStep 3414983 = 5122475) B5122475
theorem B2276655 : Blo 2275435 2276655 := bstep (se 1 (by rfl) ⟨1707491, by rfl⟩ : syracuseStep 2276655 = 3414983) B3414983
theorem B3414989 : Blo 2275435 3414989 := bbase (se 3 (by rfl) ⟨640310, by rfl⟩ : syracuseStep 3414989 = 1280621) (by norm_num)
theorem B2276659 : Blo 2275435 2276659 := bstep (se 1 (by rfl) ⟨1707494, by rfl⟩ : syracuseStep 2276659 = 3414989) B3414989
theorem B5122493 : Blo 2275435 5122493 := bbase (se 3 (by rfl) ⟨960467, by rfl⟩ : syracuseStep 5122493 = 1920935) (by norm_num)
theorem B3414995 : Blo 2275435 3414995 := bstep (se 1 (by rfl) ⟨2561246, by rfl⟩ : syracuseStep 3414995 = 5122493) B5122493
theorem B2276663 : Blo 2275435 2276663 := bstep (se 1 (by rfl) ⟨1707497, by rfl⟩ : syracuseStep 2276663 = 3414995) B3414995
theorem B3841877 : Blo 2275435 3841877 := bbase (se 9 (by rfl) ⟨11255, by rfl⟩ : syracuseStep 3841877 = 22511) (by norm_num)
theorem B2561251 : Blo 2275435 2561251 := bstep (se 1 (by rfl) ⟨1920938, by rfl⟩ : syracuseStep 2561251 = 3841877) B3841877
theorem B3415001 : Blo 2275435 3415001 := bstep (se 2 (by rfl) ⟨1280625, by rfl⟩ : syracuseStep 3415001 = 2561251) B2561251
theorem B2276667 : Blo 2275435 2276667 := bstep (se 1 (by rfl) ⟨1707500, by rfl⟩ : syracuseStep 2276667 = 3415001) B3415001
theorem B3894301 : Blo 2275435 3894301 := bbase (se 3 (by rfl) ⟨730181, by rfl⟩ : syracuseStep 3894301 = 1460363) (by norm_num)
theorem B20769605 : Blo 2275435 20769605 := bstep (se 4 (by rfl) ⟨1947150, by rfl⟩ : syracuseStep 20769605 = 3894301) B3894301
theorem B13846403 : Blo 2275435 13846403 := bstep (se 1 (by rfl) ⟨10384802, by rfl⟩ : syracuseStep 13846403 = 20769605) B20769605
theorem B9230935 : Blo 2275435 9230935 := bstep (se 1 (by rfl) ⟨6923201, by rfl⟩ : syracuseStep 9230935 = 13846403) B13846403
theorem B12307913 : Blo 2275435 12307913 := bstep (se 2 (by rfl) ⟨4615467, by rfl⟩ : syracuseStep 12307913 = 9230935) B9230935
theorem B8205275 : Blo 2275435 8205275 := bstep (se 1 (by rfl) ⟨6153956, by rfl⟩ : syracuseStep 8205275 = 12307913) B12307913
theorem B5470183 : Blo 2275435 5470183 := bstep (se 1 (by rfl) ⟨4102637, by rfl⟩ : syracuseStep 5470183 = 8205275) B8205275
theorem B7293577 : Blo 2275435 7293577 := bstep (se 2 (by rfl) ⟨2735091, by rfl⟩ : syracuseStep 7293577 = 5470183) B5470183
theorem B9724769 : Blo 2275435 9724769 := bstep (se 2 (by rfl) ⟨3646788, by rfl⟩ : syracuseStep 9724769 = 7293577) B7293577
theorem B6483179 : Blo 2275435 6483179 := bstep (se 1 (by rfl) ⟨4862384, by rfl⟩ : syracuseStep 6483179 = 9724769) B9724769
theorem B17288477 : Blo 2275435 17288477 := bstep (se 3 (by rfl) ⟨3241589, by rfl⟩ : syracuseStep 17288477 = 6483179) B6483179
theorem B11525651 : Blo 2275435 11525651 := bstep (se 1 (by rfl) ⟨8644238, by rfl⟩ : syracuseStep 11525651 = 17288477) B17288477
theorem B7683767 : Blo 2275435 7683767 := bstep (se 1 (by rfl) ⟨5762825, by rfl⟩ : syracuseStep 7683767 = 11525651) B11525651
theorem B5122511 : Blo 2275435 5122511 := bstep (se 1 (by rfl) ⟨3841883, by rfl⟩ : syracuseStep 5122511 = 7683767) B7683767
theorem B3415007 : Blo 2275435 3415007 := bstep (se 1 (by rfl) ⟨2561255, by rfl⟩ : syracuseStep 3415007 = 5122511) B5122511
theorem B2276671 : Blo 2275435 2276671 := bstep (se 1 (by rfl) ⟨1707503, by rfl⟩ : syracuseStep 2276671 = 3415007) B3415007
theorem B3415013 : Blo 2275435 3415013 := bbase (se 4 (by rfl) ⟨320157, by rfl⟩ : syracuseStep 3415013 = 640315) (by norm_num)
theorem B2276675 : Blo 2275435 2276675 := bstep (se 1 (by rfl) ⟨1707506, by rfl⟩ : syracuseStep 2276675 = 3415013) B3415013
theorem B9724805 : Blo 2275435 9724805 := bbase (se 4 (by rfl) ⟨911700, by rfl⟩ : syracuseStep 9724805 = 1823401) (by norm_num)
theorem B6483203 : Blo 2275435 6483203 := bstep (se 1 (by rfl) ⟨4862402, by rfl⟩ : syracuseStep 6483203 = 9724805) B9724805
theorem B4322135 : Blo 2275435 4322135 := bstep (se 1 (by rfl) ⟨3241601, by rfl⟩ : syracuseStep 4322135 = 6483203) B6483203
theorem B2881423 : Blo 2275435 2881423 := bstep (se 1 (by rfl) ⟨2161067, by rfl⟩ : syracuseStep 2881423 = 4322135) B4322135
theorem B3841897 : Blo 2275435 3841897 := bstep (se 2 (by rfl) ⟨1440711, by rfl⟩ : syracuseStep 3841897 = 2881423) B2881423
theorem B5122529 : Blo 2275435 5122529 := bstep (se 2 (by rfl) ⟨1920948, by rfl⟩ : syracuseStep 5122529 = 3841897) B3841897
theorem B3415019 : Blo 2275435 3415019 := bstep (se 1 (by rfl) ⟨2561264, by rfl⟩ : syracuseStep 3415019 = 5122529) B5122529
theorem B2276679 : Blo 2275435 2276679 := bstep (se 1 (by rfl) ⟨1707509, by rfl⟩ : syracuseStep 2276679 = 3415019) B3415019
theorem B2561269 : Blo 2275435 2561269 := bbase (se 5 (by rfl) ⟨120059, by rfl⟩ : syracuseStep 2561269 = 240119) (by norm_num)
theorem B3415025 : Blo 2275435 3415025 := bstep (se 2 (by rfl) ⟨1280634, by rfl⟩ : syracuseStep 3415025 = 2561269) B2561269
theorem B2276683 : Blo 2275435 2276683 := bstep (se 1 (by rfl) ⟨1707512, by rfl⟩ : syracuseStep 2276683 = 3415025) B3415025
theorem B2881433 : Blo 2275435 2881433 := bbase (se 2 (by rfl) ⟨1080537, by rfl⟩ : syracuseStep 2881433 = 2161075) (by norm_num)
theorem B7683821 : Blo 2275435 7683821 := bstep (se 3 (by rfl) ⟨1440716, by rfl⟩ : syracuseStep 7683821 = 2881433) B2881433
theorem B5122547 : Blo 2275435 5122547 := bstep (se 1 (by rfl) ⟨3841910, by rfl⟩ : syracuseStep 5122547 = 7683821) B7683821
theorem B3415031 : Blo 2275435 3415031 := bstep (se 1 (by rfl) ⟨2561273, by rfl⟩ : syracuseStep 3415031 = 5122547) B5122547
theorem B2276687 : Blo 2275435 2276687 := bstep (se 1 (by rfl) ⟨1707515, by rfl⟩ : syracuseStep 2276687 = 3415031) B3415031
theorem B3415037 : Blo 2275435 3415037 := bbase (se 3 (by rfl) ⟨640319, by rfl⟩ : syracuseStep 3415037 = 1280639) (by norm_num)
theorem B2276691 : Blo 2275435 2276691 := bstep (se 1 (by rfl) ⟨1707518, by rfl⟩ : syracuseStep 2276691 = 3415037) B3415037
theorem B5122565 : Blo 2275435 5122565 := bbase (se 4 (by rfl) ⟨480240, by rfl⟩ : syracuseStep 5122565 = 960481) (by norm_num)
theorem B3415043 : Blo 2275435 3415043 := bstep (se 1 (by rfl) ⟨2561282, by rfl⟩ : syracuseStep 3415043 = 5122565) B5122565
theorem B2276695 : Blo 2275435 2276695 := bstep (se 1 (by rfl) ⟨1707521, by rfl⟩ : syracuseStep 2276695 = 3415043) B3415043
theorem B4322173 : Blo 2275435 4322173 := bbase (se 3 (by rfl) ⟨810407, by rfl⟩ : syracuseStep 4322173 = 1620815) (by norm_num)
theorem B5762897 : Blo 2275435 5762897 := bstep (se 2 (by rfl) ⟨2161086, by rfl⟩ : syracuseStep 5762897 = 4322173) B4322173
theorem B3841931 : Blo 2275435 3841931 := bstep (se 1 (by rfl) ⟨2881448, by rfl⟩ : syracuseStep 3841931 = 5762897) B5762897
theorem B2561287 : Blo 2275435 2561287 := bstep (se 1 (by rfl) ⟨1920965, by rfl⟩ : syracuseStep 2561287 = 3841931) B3841931
theorem B3415049 : Blo 2275435 3415049 := bstep (se 2 (by rfl) ⟨1280643, by rfl⟩ : syracuseStep 3415049 = 2561287) B2561287
theorem B2276699 : Blo 2275435 2276699 := bstep (se 1 (by rfl) ⟨1707524, by rfl⟩ : syracuseStep 2276699 = 3415049) B3415049
theorem B11525813 : Blo 2275435 11525813 := bbase (se 5 (by rfl) ⟨540272, by rfl⟩ : syracuseStep 11525813 = 1080545) (by norm_num)
theorem B7683875 : Blo 2275435 7683875 := bstep (se 1 (by rfl) ⟨5762906, by rfl⟩ : syracuseStep 7683875 = 11525813) B11525813
theorem B5122583 : Blo 2275435 5122583 := bstep (se 1 (by rfl) ⟨3841937, by rfl⟩ : syracuseStep 5122583 = 7683875) B7683875
theorem B3415055 : Blo 2275435 3415055 := bstep (se 1 (by rfl) ⟨2561291, by rfl⟩ : syracuseStep 3415055 = 5122583) B5122583
theorem B2276703 : Blo 2275435 2276703 := bstep (se 1 (by rfl) ⟨1707527, by rfl⟩ : syracuseStep 2276703 = 3415055) B3415055
theorem B3415061 : Blo 2275435 3415061 := bbase (se 6 (by rfl) ⟨80040, by rfl⟩ : syracuseStep 3415061 = 160081) (by norm_num)
theorem B2276707 : Blo 2275435 2276707 := bstep (se 1 (by rfl) ⟨1707530, by rfl⟩ : syracuseStep 2276707 = 3415061) B3415061
theorem B11683109 : Blo 2275435 11683109 := bbase (se 4 (by rfl) ⟨1095291, by rfl⟩ : syracuseStep 11683109 = 2190583) (by norm_num)
theorem B7788739 : Blo 2275435 7788739 := bstep (se 1 (by rfl) ⟨5841554, by rfl⟩ : syracuseStep 7788739 = 11683109) B11683109
theorem B10384985 : Blo 2275435 10384985 := bstep (se 2 (by rfl) ⟨3894369, by rfl⟩ : syracuseStep 10384985 = 7788739) B7788739
theorem B6923323 : Blo 2275435 6923323 := bstep (se 1 (by rfl) ⟨5192492, by rfl⟩ : syracuseStep 6923323 = 10384985) B10384985
theorem B9231097 : Blo 2275435 9231097 := bstep (se 2 (by rfl) ⟨3461661, by rfl⟩ : syracuseStep 9231097 = 6923323) B6923323
theorem B12308129 : Blo 2275435 12308129 := bstep (se 2 (by rfl) ⟨4615548, by rfl⟩ : syracuseStep 12308129 = 9231097) B9231097
theorem B8205419 : Blo 2275435 8205419 := bstep (se 1 (by rfl) ⟨6154064, by rfl⟩ : syracuseStep 8205419 = 12308129) B12308129
theorem B21881117 : Blo 2275435 21881117 := bstep (se 3 (by rfl) ⟨4102709, by rfl⟩ : syracuseStep 21881117 = 8205419) B8205419
theorem B14587411 : Blo 2275435 14587411 := bstep (se 1 (by rfl) ⟨10940558, by rfl⟩ : syracuseStep 14587411 = 21881117) B21881117
theorem B19449881 : Blo 2275435 19449881 := bstep (se 2 (by rfl) ⟨7293705, by rfl⟩ : syracuseStep 19449881 = 14587411) B14587411
theorem B12966587 : Blo 2275435 12966587 := bstep (se 1 (by rfl) ⟨9724940, by rfl⟩ : syracuseStep 12966587 = 19449881) B19449881
theorem B8644391 : Blo 2275435 8644391 := bstep (se 1 (by rfl) ⟨6483293, by rfl⟩ : syracuseStep 8644391 = 12966587) B12966587
theorem B5762927 : Blo 2275435 5762927 := bstep (se 1 (by rfl) ⟨4322195, by rfl⟩ : syracuseStep 5762927 = 8644391) B8644391
theorem B3841951 : Blo 2275435 3841951 := bstep (se 1 (by rfl) ⟨2881463, by rfl⟩ : syracuseStep 3841951 = 5762927) B5762927
theorem B5122601 : Blo 2275435 5122601 := bstep (se 2 (by rfl) ⟨1920975, by rfl⟩ : syracuseStep 5122601 = 3841951) B3841951
theorem B3415067 : Blo 2275435 3415067 := bstep (se 1 (by rfl) ⟨2561300, by rfl⟩ : syracuseStep 3415067 = 5122601) B5122601
theorem B2276711 : Blo 2275435 2276711 := bstep (se 1 (by rfl) ⟨1707533, by rfl⟩ : syracuseStep 2276711 = 3415067) B3415067
theorem B2561305 : Blo 2275435 2561305 := bbase (se 2 (by rfl) ⟨960489, by rfl⟩ : syracuseStep 2561305 = 1920979) (by norm_num)
theorem B3415073 : Blo 2275435 3415073 := bstep (se 2 (by rfl) ⟨1280652, by rfl⟩ : syracuseStep 3415073 = 2561305) B2561305
theorem B2276715 : Blo 2275435 2276715 := bstep (se 1 (by rfl) ⟨1707536, by rfl⟩ : syracuseStep 2276715 = 3415073) B3415073
theorem B8644421 : Blo 2275435 8644421 := bbase (se 4 (by rfl) ⟨810414, by rfl⟩ : syracuseStep 8644421 = 1620829) (by norm_num)
theorem B5762947 : Blo 2275435 5762947 := bstep (se 1 (by rfl) ⟨4322210, by rfl⟩ : syracuseStep 5762947 = 8644421) B8644421
theorem B7683929 : Blo 2275435 7683929 := bstep (se 2 (by rfl) ⟨2881473, by rfl⟩ : syracuseStep 7683929 = 5762947) B5762947
theorem B5122619 : Blo 2275435 5122619 := bstep (se 1 (by rfl) ⟨3841964, by rfl⟩ : syracuseStep 5122619 = 7683929) B7683929
theorem B3415079 : Blo 2275435 3415079 := bstep (se 1 (by rfl) ⟨2561309, by rfl⟩ : syracuseStep 3415079 = 5122619) B5122619
theorem B2276719 : Blo 2275435 2276719 := bstep (se 1 (by rfl) ⟨1707539, by rfl⟩ : syracuseStep 2276719 = 3415079) B3415079
theorem B3415085 : Blo 2275435 3415085 := bbase (se 3 (by rfl) ⟨640328, by rfl⟩ : syracuseStep 3415085 = 1280657) (by norm_num)
theorem B2276723 : Blo 2275435 2276723 := bstep (se 1 (by rfl) ⟨1707542, by rfl⟩ : syracuseStep 2276723 = 3415085) B3415085
theorem B5122637 : Blo 2275435 5122637 := bbase (se 3 (by rfl) ⟨960494, by rfl⟩ : syracuseStep 5122637 = 1920989) (by norm_num)
theorem B3415091 : Blo 2275435 3415091 := bstep (se 1 (by rfl) ⟨2561318, by rfl⟩ : syracuseStep 3415091 = 5122637) B5122637
theorem B2276727 : Blo 2275435 2276727 := bstep (se 1 (by rfl) ⟨1707545, by rfl⟩ : syracuseStep 2276727 = 3415091) B3415091
theorem B2881489 : Blo 2275435 2881489 := bbase (se 2 (by rfl) ⟨1080558, by rfl⟩ : syracuseStep 2881489 = 2161117) (by norm_num)
theorem B3841985 : Blo 2275435 3841985 := bstep (se 2 (by rfl) ⟨1440744, by rfl⟩ : syracuseStep 3841985 = 2881489) B2881489
theorem B2561323 : Blo 2275435 2561323 := bstep (se 1 (by rfl) ⟨1920992, by rfl⟩ : syracuseStep 2561323 = 3841985) B3841985
theorem B3415097 : Blo 2275435 3415097 := bstep (se 2 (by rfl) ⟨1280661, by rfl⟩ : syracuseStep 3415097 = 2561323) B2561323
theorem B2276731 : Blo 2275435 2276731 := bstep (se 1 (by rfl) ⟨1707548, by rfl⟩ : syracuseStep 2276731 = 3415097) B3415097
theorem B5192549 : Blo 2275435 5192549 := bbase (se 4 (by rfl) ⟨486801, by rfl⟩ : syracuseStep 5192549 = 973603) (by norm_num)
theorem B3461699 : Blo 2275435 3461699 := bstep (se 1 (by rfl) ⟨2596274, by rfl⟩ : syracuseStep 3461699 = 5192549) B5192549
theorem B2307799 : Blo 2275435 2307799 := bstep (se 1 (by rfl) ⟨1730849, by rfl⟩ : syracuseStep 2307799 = 3461699) B3461699
theorem B3077065 : Blo 2275435 3077065 := bstep (se 2 (by rfl) ⟨1153899, by rfl⟩ : syracuseStep 3077065 = 2307799) B2307799
theorem B4102753 : Blo 2275435 4102753 := bstep (se 2 (by rfl) ⟨1538532, by rfl⟩ : syracuseStep 4102753 = 3077065) B3077065
theorem B5470337 : Blo 2275435 5470337 := bstep (se 2 (by rfl) ⟨2051376, by rfl⟩ : syracuseStep 5470337 = 4102753) B4102753
theorem B3646891 : Blo 2275435 3646891 := bstep (se 1 (by rfl) ⟨2735168, by rfl⟩ : syracuseStep 3646891 = 5470337) B5470337
theorem B4862521 : Blo 2275435 4862521 := bstep (se 2 (by rfl) ⟨1823445, by rfl⟩ : syracuseStep 4862521 = 3646891) B3646891
theorem B25933445 : Blo 2275435 25933445 := bstep (se 4 (by rfl) ⟨2431260, by rfl⟩ : syracuseStep 25933445 = 4862521) B4862521
theorem B17288963 : Blo 2275435 17288963 := bstep (se 1 (by rfl) ⟨12966722, by rfl⟩ : syracuseStep 17288963 = 25933445) B25933445
theorem B11525975 : Blo 2275435 11525975 := bstep (se 1 (by rfl) ⟨8644481, by rfl⟩ : syracuseStep 11525975 = 17288963) B17288963
theorem B7683983 : Blo 2275435 7683983 := bstep (se 1 (by rfl) ⟨5762987, by rfl⟩ : syracuseStep 7683983 = 11525975) B11525975
theorem B5122655 : Blo 2275435 5122655 := bstep (se 1 (by rfl) ⟨3841991, by rfl⟩ : syracuseStep 5122655 = 7683983) B7683983
theorem B3415103 : Blo 2275435 3415103 := bstep (se 1 (by rfl) ⟨2561327, by rfl⟩ : syracuseStep 3415103 = 5122655) B5122655
theorem B2276735 : Blo 2275435 2276735 := bstep (se 1 (by rfl) ⟨1707551, by rfl⟩ : syracuseStep 2276735 = 3415103) B3415103
theorem B3415109 : Blo 2275435 3415109 := bbase (se 4 (by rfl) ⟨320166, by rfl⟩ : syracuseStep 3415109 = 640333) (by norm_num)
theorem B2276739 : Blo 2275435 2276739 := bstep (se 1 (by rfl) ⟨1707554, by rfl⟩ : syracuseStep 2276739 = 3415109) B3415109
theorem B3842005 : Blo 2275435 3842005 := bbase (se 7 (by rfl) ⟨45023, by rfl⟩ : syracuseStep 3842005 = 90047) (by norm_num)
theorem B5122673 : Blo 2275435 5122673 := bstep (se 2 (by rfl) ⟨1921002, by rfl⟩ : syracuseStep 5122673 = 3842005) B3842005
theorem B3415115 : Blo 2275435 3415115 := bstep (se 1 (by rfl) ⟨2561336, by rfl⟩ : syracuseStep 3415115 = 5122673) B5122673
theorem B2276743 : Blo 2275435 2276743 := bstep (se 1 (by rfl) ⟨1707557, by rfl⟩ : syracuseStep 2276743 = 3415115) B3415115
theorem B2561341 : Blo 2275435 2561341 := bbase (se 3 (by rfl) ⟨480251, by rfl⟩ : syracuseStep 2561341 = 960503) (by norm_num)
theorem B3415121 : Blo 2275435 3415121 := bstep (se 2 (by rfl) ⟨1280670, by rfl⟩ : syracuseStep 3415121 = 2561341) B2561341
theorem B2276747 : Blo 2275435 2276747 := bstep (se 1 (by rfl) ⟨1707560, by rfl⟩ : syracuseStep 2276747 = 3415121) B3415121
theorem B7684037 : Blo 2275435 7684037 := bbase (se 4 (by rfl) ⟨720378, by rfl⟩ : syracuseStep 7684037 = 1440757) (by norm_num)
theorem B5122691 : Blo 2275435 5122691 := bstep (se 1 (by rfl) ⟨3842018, by rfl⟩ : syracuseStep 5122691 = 7684037) B7684037
theorem B3415127 : Blo 2275435 3415127 := bstep (se 1 (by rfl) ⟨2561345, by rfl⟩ : syracuseStep 3415127 = 5122691) B5122691
theorem B2276751 : Blo 2275435 2276751 := bstep (se 1 (by rfl) ⟨1707563, by rfl⟩ : syracuseStep 2276751 = 3415127) B3415127
theorem B3415133 : Blo 2275435 3415133 := bbase (se 3 (by rfl) ⟨640337, by rfl⟩ : syracuseStep 3415133 = 1280675) (by norm_num)
theorem B2276755 : Blo 2275435 2276755 := bstep (se 1 (by rfl) ⟨1707566, by rfl⟩ : syracuseStep 2276755 = 3415133) B3415133
theorem B5122709 : Blo 2275435 5122709 := bbase (se 6 (by rfl) ⟨120063, by rfl⟩ : syracuseStep 5122709 = 240127) (by norm_num)
theorem B3415139 : Blo 2275435 3415139 := bstep (se 1 (by rfl) ⟨2561354, by rfl⟩ : syracuseStep 3415139 = 5122709) B5122709
theorem B2276759 : Blo 2275435 2276759 := bstep (se 1 (by rfl) ⟨1707569, by rfl⟩ : syracuseStep 2276759 = 3415139) B3415139
theorem B4102805 : Blo 2275435 4102805 := bbase (se 6 (by rfl) ⟨96159, by rfl⟩ : syracuseStep 4102805 = 192319) (by norm_num)
theorem B2735203 : Blo 2275435 2735203 := bstep (se 1 (by rfl) ⟨2051402, by rfl⟩ : syracuseStep 2735203 = 4102805) B4102805
theorem B3646937 : Blo 2275435 3646937 := bstep (se 2 (by rfl) ⟨1367601, by rfl⟩ : syracuseStep 3646937 = 2735203) B2735203
theorem B2431291 : Blo 2275435 2431291 := bstep (se 1 (by rfl) ⟨1823468, by rfl⟩ : syracuseStep 2431291 = 3646937) B3646937
theorem B3241721 : Blo 2275435 3241721 := bstep (se 2 (by rfl) ⟨1215645, by rfl⟩ : syracuseStep 3241721 = 2431291) B2431291
theorem B8644589 : Blo 2275435 8644589 := bstep (se 3 (by rfl) ⟨1620860, by rfl⟩ : syracuseStep 8644589 = 3241721) B3241721
theorem B5763059 : Blo 2275435 5763059 := bstep (se 1 (by rfl) ⟨4322294, by rfl⟩ : syracuseStep 5763059 = 8644589) B8644589
theorem B3842039 : Blo 2275435 3842039 := bstep (se 1 (by rfl) ⟨2881529, by rfl⟩ : syracuseStep 3842039 = 5763059) B5763059
theorem B2561359 : Blo 2275435 2561359 := bstep (se 1 (by rfl) ⟨1921019, by rfl⟩ : syracuseStep 2561359 = 3842039) B3842039
theorem B3415145 : Blo 2275435 3415145 := bstep (se 2 (by rfl) ⟨1280679, by rfl⟩ : syracuseStep 3415145 = 2561359) B2561359
theorem B2276763 : Blo 2275435 2276763 := bstep (se 1 (by rfl) ⟨1707572, by rfl⟩ : syracuseStep 2276763 = 3415145) B3415145
theorem B4928933 : Blo 2275435 4928933 := bbase (se 4 (by rfl) ⟨462087, by rfl⟩ : syracuseStep 4928933 = 924175) (by norm_num)
theorem B3285955 : Blo 2275435 3285955 := bstep (se 1 (by rfl) ⟨2464466, by rfl⟩ : syracuseStep 3285955 = 4928933) B4928933
theorem B4381273 : Blo 2275435 4381273 := bstep (se 2 (by rfl) ⟨1642977, by rfl⟩ : syracuseStep 4381273 = 3285955) B3285955
theorem B23366789 : Blo 2275435 23366789 := bstep (se 4 (by rfl) ⟨2190636, by rfl⟩ : syracuseStep 23366789 = 4381273) B4381273
theorem B15577859 : Blo 2275435 15577859 := bstep (se 1 (by rfl) ⟨11683394, by rfl⟩ : syracuseStep 15577859 = 23366789) B23366789
theorem B41540957 : Blo 2275435 41540957 := bstep (se 3 (by rfl) ⟨7788929, by rfl⟩ : syracuseStep 41540957 = 15577859) B15577859
theorem B27693971 : Blo 2275435 27693971 := bstep (se 1 (by rfl) ⟨20770478, by rfl⟩ : syracuseStep 27693971 = 41540957) B41540957
theorem B18462647 : Blo 2275435 18462647 := bstep (se 1 (by rfl) ⟨13846985, by rfl⟩ : syracuseStep 18462647 = 27693971) B27693971
theorem B12308431 : Blo 2275435 12308431 := bstep (se 1 (by rfl) ⟨9231323, by rfl⟩ : syracuseStep 12308431 = 18462647) B18462647
theorem B16411241 : Blo 2275435 16411241 := bstep (se 2 (by rfl) ⟨6154215, by rfl⟩ : syracuseStep 16411241 = 12308431) B12308431
theorem B10940827 : Blo 2275435 10940827 := bstep (se 1 (by rfl) ⟨8205620, by rfl⟩ : syracuseStep 10940827 = 16411241) B16411241
theorem B14587769 : Blo 2275435 14587769 := bstep (se 2 (by rfl) ⟨5470413, by rfl⟩ : syracuseStep 14587769 = 10940827) B10940827
theorem B9725179 : Blo 2275435 9725179 := bstep (se 1 (by rfl) ⟨7293884, by rfl⟩ : syracuseStep 9725179 = 14587769) B14587769
theorem B12966905 : Blo 2275435 12966905 := bstep (se 2 (by rfl) ⟨4862589, by rfl⟩ : syracuseStep 12966905 = 9725179) B9725179
theorem B8644603 : Blo 2275435 8644603 := bstep (se 1 (by rfl) ⟨6483452, by rfl⟩ : syracuseStep 8644603 = 12966905) B12966905
theorem B11526137 : Blo 2275435 11526137 := bstep (se 2 (by rfl) ⟨4322301, by rfl⟩ : syracuseStep 11526137 = 8644603) B8644603
theorem B7684091 : Blo 2275435 7684091 := bstep (se 1 (by rfl) ⟨5763068, by rfl⟩ : syracuseStep 7684091 = 11526137) B11526137
theorem B5122727 : Blo 2275435 5122727 := bstep (se 1 (by rfl) ⟨3842045, by rfl⟩ : syracuseStep 5122727 = 7684091) B7684091
theorem B3415151 : Blo 2275435 3415151 := bstep (se 1 (by rfl) ⟨2561363, by rfl⟩ : syracuseStep 3415151 = 5122727) B5122727
theorem B2276767 : Blo 2275435 2276767 := bstep (se 1 (by rfl) ⟨1707575, by rfl⟩ : syracuseStep 2276767 = 3415151) B3415151
theorem B3415157 : Blo 2275435 3415157 := bbase (se 5 (by rfl) ⟨160085, by rfl⟩ : syracuseStep 3415157 = 320171) (by norm_num)
theorem B2276771 : Blo 2275435 2276771 := bstep (se 1 (by rfl) ⟨1707578, by rfl⟩ : syracuseStep 2276771 = 3415157) B3415157
theorem B4322317 : Blo 2275435 4322317 := bbase (se 3 (by rfl) ⟨810434, by rfl⟩ : syracuseStep 4322317 = 1620869) (by norm_num)
theorem B5763089 : Blo 2275435 5763089 := bstep (se 2 (by rfl) ⟨2161158, by rfl⟩ : syracuseStep 5763089 = 4322317) B4322317
theorem B3842059 : Blo 2275435 3842059 := bstep (se 1 (by rfl) ⟨2881544, by rfl⟩ : syracuseStep 3842059 = 5763089) B5763089
theorem B5122745 : Blo 2275435 5122745 := bstep (se 2 (by rfl) ⟨1921029, by rfl⟩ : syracuseStep 5122745 = 3842059) B3842059
theorem B3415163 : Blo 2275435 3415163 := bstep (se 1 (by rfl) ⟨2561372, by rfl⟩ : syracuseStep 3415163 = 5122745) B5122745
theorem B2276775 : Blo 2275435 2276775 := bstep (se 1 (by rfl) ⟨1707581, by rfl⟩ : syracuseStep 2276775 = 3415163) B3415163
theorem B2561377 : Blo 2275435 2561377 := bbase (se 2 (by rfl) ⟨960516, by rfl⟩ : syracuseStep 2561377 = 1921033) (by norm_num)
theorem B3415169 : Blo 2275435 3415169 := bstep (se 2 (by rfl) ⟨1280688, by rfl⟩ : syracuseStep 3415169 = 2561377) B2561377
theorem B2276779 : Blo 2275435 2276779 := bstep (se 1 (by rfl) ⟨1707584, by rfl⟩ : syracuseStep 2276779 = 3415169) B3415169
theorem B5763109 : Blo 2275435 5763109 := bbase (se 4 (by rfl) ⟨540291, by rfl⟩ : syracuseStep 5763109 = 1080583) (by norm_num)
theorem B7684145 : Blo 2275435 7684145 := bstep (se 2 (by rfl) ⟨2881554, by rfl⟩ : syracuseStep 7684145 = 5763109) B5763109
theorem B5122763 : Blo 2275435 5122763 := bstep (se 1 (by rfl) ⟨3842072, by rfl⟩ : syracuseStep 5122763 = 7684145) B7684145
theorem B3415175 : Blo 2275435 3415175 := bstep (se 1 (by rfl) ⟨2561381, by rfl⟩ : syracuseStep 3415175 = 5122763) B5122763
theorem B2276783 : Blo 2275435 2276783 := bstep (se 1 (by rfl) ⟨1707587, by rfl⟩ : syracuseStep 2276783 = 3415175) B3415175
theorem B3415181 : Blo 2275435 3415181 := bbase (se 3 (by rfl) ⟨640346, by rfl⟩ : syracuseStep 3415181 = 1280693) (by norm_num)
theorem B2276787 : Blo 2275435 2276787 := bstep (se 1 (by rfl) ⟨1707590, by rfl⟩ : syracuseStep 2276787 = 3415181) B3415181
theorem B5122781 : Blo 2275435 5122781 := bbase (se 3 (by rfl) ⟨960521, by rfl⟩ : syracuseStep 5122781 = 1921043) (by norm_num)
theorem B3415187 : Blo 2275435 3415187 := bstep (se 1 (by rfl) ⟨2561390, by rfl⟩ : syracuseStep 3415187 = 5122781) B5122781
theorem B2276791 : Blo 2275435 2276791 := bstep (se 1 (by rfl) ⟨1707593, by rfl⟩ : syracuseStep 2276791 = 3415187) B3415187
theorem B3842093 : Blo 2275435 3842093 := bbase (se 3 (by rfl) ⟨720392, by rfl⟩ : syracuseStep 3842093 = 1440785) (by norm_num)
theorem B2561395 : Blo 2275435 2561395 := bstep (se 1 (by rfl) ⟨1921046, by rfl⟩ : syracuseStep 2561395 = 3842093) B3842093
theorem B3415193 : Blo 2275435 3415193 := bstep (se 2 (by rfl) ⟨1280697, by rfl⟩ : syracuseStep 3415193 = 2561395) B2561395
theorem B2276795 : Blo 2275435 2276795 := bstep (se 1 (by rfl) ⟨1707596, by rfl⟩ : syracuseStep 2276795 = 3415193) B3415193
theorem B2464501 : Blo 2275435 2464501 := bbase (se 5 (by rfl) ⟨115523, by rfl⟩ : syracuseStep 2464501 = 231047) (by norm_num)
theorem B3286001 : Blo 2275435 3286001 := bstep (se 2 (by rfl) ⟨1232250, by rfl⟩ : syracuseStep 3286001 = 2464501) B2464501
theorem B8762669 : Blo 2275435 8762669 := bstep (se 3 (by rfl) ⟨1643000, by rfl⟩ : syracuseStep 8762669 = 3286001) B3286001
theorem B5841779 : Blo 2275435 5841779 := bstep (se 1 (by rfl) ⟨4381334, by rfl⟩ : syracuseStep 5841779 = 8762669) B8762669
theorem B15578077 : Blo 2275435 15578077 := bstep (se 3 (by rfl) ⟨2920889, by rfl⟩ : syracuseStep 15578077 = 5841779) B5841779
theorem B20770769 : Blo 2275435 20770769 := bstep (se 2 (by rfl) ⟨7789038, by rfl⟩ : syracuseStep 20770769 = 15578077) B15578077
theorem B13847179 : Blo 2275435 13847179 := bstep (se 1 (by rfl) ⟨10385384, by rfl⟩ : syracuseStep 13847179 = 20770769) B20770769
theorem B18462905 : Blo 2275435 18462905 := bstep (se 2 (by rfl) ⟨6923589, by rfl⟩ : syracuseStep 18462905 = 13847179) B13847179
theorem B12308603 : Blo 2275435 12308603 := bstep (se 1 (by rfl) ⟨9231452, by rfl⟩ : syracuseStep 12308603 = 18462905) B18462905
theorem B32822941 : Blo 2275435 32822941 := bstep (se 3 (by rfl) ⟨6154301, by rfl⟩ : syracuseStep 32822941 = 12308603) B12308603
theorem B43763921 : Blo 2275435 43763921 := bstep (se 2 (by rfl) ⟨16411470, by rfl⟩ : syracuseStep 43763921 = 32822941) B32822941
theorem B29175947 : Blo 2275435 29175947 := bstep (se 1 (by rfl) ⟨21881960, by rfl⟩ : syracuseStep 29175947 = 43763921) B43763921
theorem B19450631 : Blo 2275435 19450631 := bstep (se 1 (by rfl) ⟨14587973, by rfl⟩ : syracuseStep 19450631 = 29175947) B29175947
theorem B12967087 : Blo 2275435 12967087 := bstep (se 1 (by rfl) ⟨9725315, by rfl⟩ : syracuseStep 12967087 = 19450631) B19450631
theorem B17289449 : Blo 2275435 17289449 := bstep (se 2 (by rfl) ⟨6483543, by rfl⟩ : syracuseStep 17289449 = 12967087) B12967087
theorem B11526299 : Blo 2275435 11526299 := bstep (se 1 (by rfl) ⟨8644724, by rfl⟩ : syracuseStep 11526299 = 17289449) B17289449
theorem B7684199 : Blo 2275435 7684199 := bstep (se 1 (by rfl) ⟨5763149, by rfl⟩ : syracuseStep 7684199 = 11526299) B11526299
theorem B5122799 : Blo 2275435 5122799 := bstep (se 1 (by rfl) ⟨3842099, by rfl⟩ : syracuseStep 5122799 = 7684199) B7684199
theorem B3415199 : Blo 2275435 3415199 := bstep (se 1 (by rfl) ⟨2561399, by rfl⟩ : syracuseStep 3415199 = 5122799) B5122799
theorem B2276799 : Blo 2275435 2276799 := bstep (se 1 (by rfl) ⟨1707599, by rfl⟩ : syracuseStep 2276799 = 3415199) B3415199
theorem B3415205 : Blo 2275435 3415205 := bbase (se 4 (by rfl) ⟨320175, by rfl⟩ : syracuseStep 3415205 = 640351) (by norm_num)
theorem B2276803 : Blo 2275435 2276803 := bstep (se 1 (by rfl) ⟨1707602, by rfl⟩ : syracuseStep 2276803 = 3415205) B3415205
theorem B2881585 : Blo 2275435 2881585 := bbase (se 2 (by rfl) ⟨1080594, by rfl⟩ : syracuseStep 2881585 = 2161189) (by norm_num)
theorem B3842113 : Blo 2275435 3842113 := bstep (se 2 (by rfl) ⟨1440792, by rfl⟩ : syracuseStep 3842113 = 2881585) B2881585
theorem B5122817 : Blo 2275435 5122817 := bstep (se 2 (by rfl) ⟨1921056, by rfl⟩ : syracuseStep 5122817 = 3842113) B3842113
theorem B3415211 : Blo 2275435 3415211 := bstep (se 1 (by rfl) ⟨2561408, by rfl⟩ : syracuseStep 3415211 = 5122817) B5122817
theorem B2276807 : Blo 2275435 2276807 := bstep (se 1 (by rfl) ⟨1707605, by rfl⟩ : syracuseStep 2276807 = 3415211) B3415211
theorem B2561413 : Blo 2275435 2561413 := bbase (se 4 (by rfl) ⟨240132, by rfl⟩ : syracuseStep 2561413 = 480265) (by norm_num)
theorem B3415217 : Blo 2275435 3415217 := bstep (se 2 (by rfl) ⟨1280706, by rfl⟩ : syracuseStep 3415217 = 2561413) B2561413
theorem B2276811 : Blo 2275435 2276811 := bstep (se 1 (by rfl) ⟨1707608, by rfl⟩ : syracuseStep 2276811 = 3415217) B3415217
theorem B4862693 : Blo 2275435 4862693 := bbase (se 4 (by rfl) ⟨455877, by rfl⟩ : syracuseStep 4862693 = 911755) (by norm_num)
theorem B3241795 : Blo 2275435 3241795 := bstep (se 1 (by rfl) ⟨2431346, by rfl⟩ : syracuseStep 3241795 = 4862693) B4862693
theorem B4322393 : Blo 2275435 4322393 := bstep (se 2 (by rfl) ⟨1620897, by rfl⟩ : syracuseStep 4322393 = 3241795) B3241795
theorem B2881595 : Blo 2275435 2881595 := bstep (se 1 (by rfl) ⟨2161196, by rfl⟩ : syracuseStep 2881595 = 4322393) B4322393
theorem B7684253 : Blo 2275435 7684253 := bstep (se 3 (by rfl) ⟨1440797, by rfl⟩ : syracuseStep 7684253 = 2881595) B2881595
theorem B5122835 : Blo 2275435 5122835 := bstep (se 1 (by rfl) ⟨3842126, by rfl⟩ : syracuseStep 5122835 = 7684253) B7684253
theorem B3415223 : Blo 2275435 3415223 := bstep (se 1 (by rfl) ⟨2561417, by rfl⟩ : syracuseStep 3415223 = 5122835) B5122835
theorem B2276815 : Blo 2275435 2276815 := bstep (se 1 (by rfl) ⟨1707611, by rfl⟩ : syracuseStep 2276815 = 3415223) B3415223
theorem B3415229 : Blo 2275435 3415229 := bbase (se 3 (by rfl) ⟨640355, by rfl⟩ : syracuseStep 3415229 = 1280711) (by norm_num)
theorem B2276819 : Blo 2275435 2276819 := bstep (se 1 (by rfl) ⟨1707614, by rfl⟩ : syracuseStep 2276819 = 3415229) B3415229
theorem B5122853 : Blo 2275435 5122853 := bbase (se 4 (by rfl) ⟨480267, by rfl⟩ : syracuseStep 5122853 = 960535) (by norm_num)
theorem B3415235 : Blo 2275435 3415235 := bstep (se 1 (by rfl) ⟨2561426, by rfl⟩ : syracuseStep 3415235 = 5122853) B5122853
theorem B2276823 : Blo 2275435 2276823 := bstep (se 1 (by rfl) ⟨1707617, by rfl⟩ : syracuseStep 2276823 = 3415235) B3415235
theorem B5763221 : Blo 2275435 5763221 := bbase (se 6 (by rfl) ⟨135075, by rfl⟩ : syracuseStep 5763221 = 270151) (by norm_num)
theorem B3842147 : Blo 2275435 3842147 := bstep (se 1 (by rfl) ⟨2881610, by rfl⟩ : syracuseStep 3842147 = 5763221) B5763221
theorem B2561431 : Blo 2275435 2561431 := bstep (se 1 (by rfl) ⟨1921073, by rfl⟩ : syracuseStep 2561431 = 3842147) B3842147
theorem B3415241 : Blo 2275435 3415241 := bstep (se 2 (by rfl) ⟨1280715, by rfl⟩ : syracuseStep 3415241 = 2561431) B2561431
theorem B2276827 : Blo 2275435 2276827 := bstep (se 1 (by rfl) ⟨1707620, by rfl⟩ : syracuseStep 2276827 = 3415241) B3415241
theorem B3647045 : Blo 2275435 3647045 := bbase (se 4 (by rfl) ⟨341910, by rfl⟩ : syracuseStep 3647045 = 683821) (by norm_num)
theorem B9725453 : Blo 2275435 9725453 := bstep (se 3 (by rfl) ⟨1823522, by rfl⟩ : syracuseStep 9725453 = 3647045) B3647045
theorem B6483635 : Blo 2275435 6483635 := bstep (se 1 (by rfl) ⟨4862726, by rfl⟩ : syracuseStep 6483635 = 9725453) B9725453
theorem B4322423 : Blo 2275435 4322423 := bstep (se 1 (by rfl) ⟨3241817, by rfl⟩ : syracuseStep 4322423 = 6483635) B6483635
theorem B11526461 : Blo 2275435 11526461 := bstep (se 3 (by rfl) ⟨2161211, by rfl⟩ : syracuseStep 11526461 = 4322423) B4322423
theorem B7684307 : Blo 2275435 7684307 := bstep (se 1 (by rfl) ⟨5763230, by rfl⟩ : syracuseStep 7684307 = 11526461) B11526461
theorem B5122871 : Blo 2275435 5122871 := bstep (se 1 (by rfl) ⟨3842153, by rfl⟩ : syracuseStep 5122871 = 7684307) B7684307
theorem B3415247 : Blo 2275435 3415247 := bstep (se 1 (by rfl) ⟨2561435, by rfl⟩ : syracuseStep 3415247 = 5122871) B5122871
theorem B2276831 : Blo 2275435 2276831 := bstep (se 1 (by rfl) ⟨1707623, by rfl⟩ : syracuseStep 2276831 = 3415247) B3415247
theorem B3415253 : Blo 2275435 3415253 := bbase (se 7 (by rfl) ⟨40022, by rfl⟩ : syracuseStep 3415253 = 80045) (by norm_num)
theorem B2276835 : Blo 2275435 2276835 := bstep (se 1 (by rfl) ⟨1707626, by rfl⟩ : syracuseStep 2276835 = 3415253) B3415253
theorem B3241829 : Blo 2275435 3241829 := bbase (se 4 (by rfl) ⟨303921, by rfl⟩ : syracuseStep 3241829 = 607843) (by norm_num)
theorem B8644877 : Blo 2275435 8644877 := bstep (se 3 (by rfl) ⟨1620914, by rfl⟩ : syracuseStep 8644877 = 3241829) B3241829
theorem B5763251 : Blo 2275435 5763251 := bstep (se 1 (by rfl) ⟨4322438, by rfl⟩ : syracuseStep 5763251 = 8644877) B8644877
theorem B3842167 : Blo 2275435 3842167 := bstep (se 1 (by rfl) ⟨2881625, by rfl⟩ : syracuseStep 3842167 = 5763251) B5763251
theorem B5122889 : Blo 2275435 5122889 := bstep (se 2 (by rfl) ⟨1921083, by rfl⟩ : syracuseStep 5122889 = 3842167) B3842167
theorem B3415259 : Blo 2275435 3415259 := bstep (se 1 (by rfl) ⟨2561444, by rfl⟩ : syracuseStep 3415259 = 5122889) B5122889
theorem B2276839 : Blo 2275435 2276839 := bstep (se 1 (by rfl) ⟨1707629, by rfl⟩ : syracuseStep 2276839 = 3415259) B3415259
theorem B2561449 : Blo 2275435 2561449 := bbase (se 2 (by rfl) ⟨960543, by rfl⟩ : syracuseStep 2561449 = 1921087) (by norm_num)
theorem B3415265 : Blo 2275435 3415265 := bstep (se 2 (by rfl) ⟨1280724, by rfl⟩ : syracuseStep 3415265 = 2561449) B2561449
theorem B2276843 : Blo 2275435 2276843 := bstep (se 1 (by rfl) ⟨1707632, by rfl⟩ : syracuseStep 2276843 = 3415265) B3415265
theorem B3461869 : Blo 2275435 3461869 := bbase (se 3 (by rfl) ⟨649100, by rfl⟩ : syracuseStep 3461869 = 1298201) (by norm_num)
theorem B4615825 : Blo 2275435 4615825 := bstep (se 2 (by rfl) ⟨1730934, by rfl⟩ : syracuseStep 4615825 = 3461869) B3461869
theorem B6154433 : Blo 2275435 6154433 := bstep (se 2 (by rfl) ⟨2307912, by rfl⟩ : syracuseStep 6154433 = 4615825) B4615825
theorem B4102955 : Blo 2275435 4102955 := bstep (se 1 (by rfl) ⟨3077216, by rfl⟩ : syracuseStep 4102955 = 6154433) B6154433
theorem B2735303 : Blo 2275435 2735303 := bstep (se 1 (by rfl) ⟨2051477, by rfl⟩ : syracuseStep 2735303 = 4102955) B4102955
theorem B7294141 : Blo 2275435 7294141 := bstep (se 3 (by rfl) ⟨1367651, by rfl⟩ : syracuseStep 7294141 = 2735303) B2735303
theorem B9725521 : Blo 2275435 9725521 := bstep (se 2 (by rfl) ⟨3647070, by rfl⟩ : syracuseStep 9725521 = 7294141) B7294141
theorem B12967361 : Blo 2275435 12967361 := bstep (se 2 (by rfl) ⟨4862760, by rfl⟩ : syracuseStep 12967361 = 9725521) B9725521
theorem B8644907 : Blo 2275435 8644907 := bstep (se 1 (by rfl) ⟨6483680, by rfl⟩ : syracuseStep 8644907 = 12967361) B12967361
theorem B5763271 : Blo 2275435 5763271 := bstep (se 1 (by rfl) ⟨4322453, by rfl⟩ : syracuseStep 5763271 = 8644907) B8644907
theorem B7684361 : Blo 2275435 7684361 := bstep (se 2 (by rfl) ⟨2881635, by rfl⟩ : syracuseStep 7684361 = 5763271) B5763271
theorem B5122907 : Blo 2275435 5122907 := bstep (se 1 (by rfl) ⟨3842180, by rfl⟩ : syracuseStep 5122907 = 7684361) B7684361
theorem B3415271 : Blo 2275435 3415271 := bstep (se 1 (by rfl) ⟨2561453, by rfl⟩ : syracuseStep 3415271 = 5122907) B5122907
theorem B2276847 : Blo 2275435 2276847 := bstep (se 1 (by rfl) ⟨1707635, by rfl⟩ : syracuseStep 2276847 = 3415271) B3415271
theorem B3415277 : Blo 2275435 3415277 := bbase (se 3 (by rfl) ⟨640364, by rfl⟩ : syracuseStep 3415277 = 1280729) (by norm_num)
theorem B2276851 : Blo 2275435 2276851 := bstep (se 1 (by rfl) ⟨1707638, by rfl⟩ : syracuseStep 2276851 = 3415277) B3415277
theorem B5122925 : Blo 2275435 5122925 := bbase (se 3 (by rfl) ⟨960548, by rfl⟩ : syracuseStep 5122925 = 1921097) (by norm_num)
theorem B3415283 : Blo 2275435 3415283 := bstep (se 1 (by rfl) ⟨2561462, by rfl⟩ : syracuseStep 3415283 = 5122925) B5122925
theorem B2276855 : Blo 2275435 2276855 := bstep (se 1 (by rfl) ⟨1707641, by rfl⟩ : syracuseStep 2276855 = 3415283) B3415283
theorem B4322477 : Blo 2275435 4322477 := bbase (se 3 (by rfl) ⟨810464, by rfl⟩ : syracuseStep 4322477 = 1620929) (by norm_num)
theorem B2881651 : Blo 2275435 2881651 := bstep (se 1 (by rfl) ⟨2161238, by rfl⟩ : syracuseStep 2881651 = 4322477) B4322477
theorem B3842201 : Blo 2275435 3842201 := bstep (se 2 (by rfl) ⟨1440825, by rfl⟩ : syracuseStep 3842201 = 2881651) B2881651
theorem B2561467 : Blo 2275435 2561467 := bstep (se 1 (by rfl) ⟨1921100, by rfl⟩ : syracuseStep 2561467 = 3842201) B3842201
theorem B3415289 : Blo 2275435 3415289 := bstep (se 2 (by rfl) ⟨1280733, by rfl⟩ : syracuseStep 3415289 = 2561467) B2561467
theorem B2276859 : Blo 2275435 2276859 := bstep (se 1 (by rfl) ⟨1707644, by rfl⟩ : syracuseStep 2276859 = 3415289) B3415289
theorem B3119221 : Blo 2275435 3119221 := bbase (se 5 (by rfl) ⟨146213, by rfl⟩ : syracuseStep 3119221 = 292427) (by norm_num)
theorem B16635845 : Blo 2275435 16635845 := bstep (se 4 (by rfl) ⟨1559610, by rfl⟩ : syracuseStep 16635845 = 3119221) B3119221
theorem B44362253 : Blo 2275435 44362253 := bstep (se 3 (by rfl) ⟨8317922, by rfl⟩ : syracuseStep 44362253 = 16635845) B16635845
theorem B118299341 : Blo 2275435 118299341 := bstep (se 3 (by rfl) ⟨22181126, by rfl⟩ : syracuseStep 118299341 = 44362253) B44362253
theorem B78866227 : Blo 2275435 78866227 := bstep (se 1 (by rfl) ⟨59149670, by rfl⟩ : syracuseStep 78866227 = 118299341) B118299341
theorem B105154969 : Blo 2275435 105154969 := bstep (se 2 (by rfl) ⟨39433113, by rfl⟩ : syracuseStep 105154969 = 78866227) B78866227
theorem B140206625 : Blo 2275435 140206625 := bstep (se 2 (by rfl) ⟨52577484, by rfl⟩ : syracuseStep 140206625 = 105154969) B105154969
theorem B93471083 : Blo 2275435 93471083 := bstep (se 1 (by rfl) ⟨70103312, by rfl⟩ : syracuseStep 93471083 = 140206625) B140206625
theorem B62314055 : Blo 2275435 62314055 := bstep (se 1 (by rfl) ⟨46735541, by rfl⟩ : syracuseStep 62314055 = 93471083) B93471083
theorem B41542703 : Blo 2275435 41542703 := bstep (se 1 (by rfl) ⟨31157027, by rfl⟩ : syracuseStep 41542703 = 62314055) B62314055
theorem B27695135 : Blo 2275435 27695135 := bstep (se 1 (by rfl) ⟨20771351, by rfl⟩ : syracuseStep 27695135 = 41542703) B41542703
theorem B73853693 : Blo 2275435 73853693 := bstep (se 3 (by rfl) ⟨13847567, by rfl⟩ : syracuseStep 73853693 = 27695135) B27695135
theorem B49235795 : Blo 2275435 49235795 := bstep (se 1 (by rfl) ⟨36926846, by rfl⟩ : syracuseStep 49235795 = 73853693) B73853693
theorem B32823863 : Blo 2275435 32823863 := bstep (se 1 (by rfl) ⟨24617897, by rfl⟩ : syracuseStep 32823863 = 49235795) B49235795
theorem B21882575 : Blo 2275435 21882575 := bstep (se 1 (by rfl) ⟨16411931, by rfl⟩ : syracuseStep 21882575 = 32823863) B32823863
theorem B58353533 : Blo 2275435 58353533 := bstep (se 3 (by rfl) ⟨10941287, by rfl⟩ : syracuseStep 58353533 = 21882575) B21882575
theorem B38902355 : Blo 2275435 38902355 := bstep (se 1 (by rfl) ⟨29176766, by rfl⟩ : syracuseStep 38902355 = 58353533) B58353533
theorem B25934903 : Blo 2275435 25934903 := bstep (se 1 (by rfl) ⟨19451177, by rfl⟩ : syracuseStep 25934903 = 38902355) B38902355
theorem B17289935 : Blo 2275435 17289935 := bstep (se 1 (by rfl) ⟨12967451, by rfl⟩ : syracuseStep 17289935 = 25934903) B25934903
theorem B11526623 : Blo 2275435 11526623 := bstep (se 1 (by rfl) ⟨8644967, by rfl⟩ : syracuseStep 11526623 = 17289935) B17289935
theorem B7684415 : Blo 2275435 7684415 := bstep (se 1 (by rfl) ⟨5763311, by rfl⟩ : syracuseStep 7684415 = 11526623) B11526623
theorem B5122943 : Blo 2275435 5122943 := bstep (se 1 (by rfl) ⟨3842207, by rfl⟩ : syracuseStep 5122943 = 7684415) B7684415
theorem B3415295 : Blo 2275435 3415295 := bstep (se 1 (by rfl) ⟨2561471, by rfl⟩ : syracuseStep 3415295 = 5122943) B5122943
theorem B2276863 : Blo 2275435 2276863 := bstep (se 1 (by rfl) ⟨1707647, by rfl⟩ : syracuseStep 2276863 = 3415295) B3415295
theorem B3415301 : Blo 2275435 3415301 := bbase (se 4 (by rfl) ⟨320184, by rfl⟩ : syracuseStep 3415301 = 640369) (by norm_num)
theorem B2276867 : Blo 2275435 2276867 := bstep (se 1 (by rfl) ⟨1707650, by rfl⟩ : syracuseStep 2276867 = 3415301) B3415301
theorem B3842221 : Blo 2275435 3842221 := bbase (se 3 (by rfl) ⟨720416, by rfl⟩ : syracuseStep 3842221 = 1440833) (by norm_num)
theorem B5122961 : Blo 2275435 5122961 := bstep (se 2 (by rfl) ⟨1921110, by rfl⟩ : syracuseStep 5122961 = 3842221) B3842221
theorem B3415307 : Blo 2275435 3415307 := bstep (se 1 (by rfl) ⟨2561480, by rfl⟩ : syracuseStep 3415307 = 5122961) B5122961
theorem B2276871 : Blo 2275435 2276871 := bstep (se 1 (by rfl) ⟨1707653, by rfl⟩ : syracuseStep 2276871 = 3415307) B3415307
theorem B2561485 : Blo 2275435 2561485 := bbase (se 3 (by rfl) ⟨480278, by rfl⟩ : syracuseStep 2561485 = 960557) (by norm_num)
theorem B3415313 : Blo 2275435 3415313 := bstep (se 2 (by rfl) ⟨1280742, by rfl⟩ : syracuseStep 3415313 = 2561485) B2561485
theorem B2276875 : Blo 2275435 2276875 := bstep (se 1 (by rfl) ⟨1707656, by rfl⟩ : syracuseStep 2276875 = 3415313) B3415313
theorem B7684469 : Blo 2275435 7684469 := bbase (se 5 (by rfl) ⟨360209, by rfl⟩ : syracuseStep 7684469 = 720419) (by norm_num)
theorem B5122979 : Blo 2275435 5122979 := bstep (se 1 (by rfl) ⟨3842234, by rfl⟩ : syracuseStep 5122979 = 7684469) B7684469
theorem B3415319 : Blo 2275435 3415319 := bstep (se 1 (by rfl) ⟨2561489, by rfl⟩ : syracuseStep 3415319 = 5122979) B5122979
theorem B2276879 : Blo 2275435 2276879 := bstep (se 1 (by rfl) ⟨1707659, by rfl⟩ : syracuseStep 2276879 = 3415319) B3415319
theorem B3415325 : Blo 2275435 3415325 := bbase (se 3 (by rfl) ⟨640373, by rfl⟩ : syracuseStep 3415325 = 1280747) (by norm_num)
theorem B2276883 : Blo 2275435 2276883 := bstep (se 1 (by rfl) ⟨1707662, by rfl⟩ : syracuseStep 2276883 = 3415325) B3415325
theorem B5122997 : Blo 2275435 5122997 := bbase (se 5 (by rfl) ⟨240140, by rfl⟩ : syracuseStep 5122997 = 480281) (by norm_num)
theorem B3415331 : Blo 2275435 3415331 := bstep (se 1 (by rfl) ⟨2561498, by rfl⟩ : syracuseStep 3415331 = 5122997) B5122997
theorem B2276887 : Blo 2275435 2276887 := bstep (se 1 (by rfl) ⟨1707665, by rfl⟩ : syracuseStep 2276887 = 3415331) B3415331
theorem B8206069 : Blo 2275435 8206069 := bbase (se 5 (by rfl) ⟨384659, by rfl⟩ : syracuseStep 8206069 = 769319) (by norm_num)
theorem B10941425 : Blo 2275435 10941425 := bstep (se 2 (by rfl) ⟨4103034, by rfl⟩ : syracuseStep 10941425 = 8206069) B8206069
theorem B7294283 : Blo 2275435 7294283 := bstep (se 1 (by rfl) ⟨5470712, by rfl⟩ : syracuseStep 7294283 = 10941425) B10941425
theorem B4862855 : Blo 2275435 4862855 := bstep (se 1 (by rfl) ⟨3647141, by rfl⟩ : syracuseStep 4862855 = 7294283) B7294283
theorem B12967613 : Blo 2275435 12967613 := bstep (se 3 (by rfl) ⟨2431427, by rfl⟩ : syracuseStep 12967613 = 4862855) B4862855
theorem B8645075 : Blo 2275435 8645075 := bstep (se 1 (by rfl) ⟨6483806, by rfl⟩ : syracuseStep 8645075 = 12967613) B12967613
theorem B5763383 : Blo 2275435 5763383 := bstep (se 1 (by rfl) ⟨4322537, by rfl⟩ : syracuseStep 5763383 = 8645075) B8645075
theorem B3842255 : Blo 2275435 3842255 := bstep (se 1 (by rfl) ⟨2881691, by rfl⟩ : syracuseStep 3842255 = 5763383) B5763383
theorem B2561503 : Blo 2275435 2561503 := bstep (se 1 (by rfl) ⟨1921127, by rfl⟩ : syracuseStep 2561503 = 3842255) B3842255
theorem B3415337 : Blo 2275435 3415337 := bstep (se 2 (by rfl) ⟨1280751, by rfl⟩ : syracuseStep 3415337 = 2561503) B2561503
theorem B2276891 : Blo 2275435 2276891 := bstep (se 1 (by rfl) ⟨1707668, by rfl⟩ : syracuseStep 2276891 = 3415337) B3415337
theorem B2307961 : Blo 2275435 2307961 := bbase (se 2 (by rfl) ⟨865485, by rfl⟩ : syracuseStep 2307961 = 1730971) (by norm_num)
theorem B3077281 : Blo 2275435 3077281 := bstep (se 2 (by rfl) ⟨1153980, by rfl⟩ : syracuseStep 3077281 = 2307961) B2307961
theorem B16412165 : Blo 2275435 16412165 := bstep (se 4 (by rfl) ⟨1538640, by rfl⟩ : syracuseStep 16412165 = 3077281) B3077281
theorem B10941443 : Blo 2275435 10941443 := bstep (se 1 (by rfl) ⟨8206082, by rfl⟩ : syracuseStep 10941443 = 16412165) B16412165
theorem B7294295 : Blo 2275435 7294295 := bstep (se 1 (by rfl) ⟨5470721, by rfl⟩ : syracuseStep 7294295 = 10941443) B10941443
theorem B4862863 : Blo 2275435 4862863 := bstep (se 1 (by rfl) ⟨3647147, by rfl⟩ : syracuseStep 4862863 = 7294295) B7294295
theorem B6483817 : Blo 2275435 6483817 := bstep (se 2 (by rfl) ⟨2431431, by rfl⟩ : syracuseStep 6483817 = 4862863) B4862863
theorem B8645089 : Blo 2275435 8645089 := bstep (se 2 (by rfl) ⟨3241908, by rfl⟩ : syracuseStep 8645089 = 6483817) B6483817
theorem B11526785 : Blo 2275435 11526785 := bstep (se 2 (by rfl) ⟨4322544, by rfl⟩ : syracuseStep 11526785 = 8645089) B8645089
theorem B7684523 : Blo 2275435 7684523 := bstep (se 1 (by rfl) ⟨5763392, by rfl⟩ : syracuseStep 7684523 = 11526785) B11526785
theorem B5123015 : Blo 2275435 5123015 := bstep (se 1 (by rfl) ⟨3842261, by rfl⟩ : syracuseStep 5123015 = 7684523) B7684523
theorem B3415343 : Blo 2275435 3415343 := bstep (se 1 (by rfl) ⟨2561507, by rfl⟩ : syracuseStep 3415343 = 5123015) B5123015
theorem B2276895 : Blo 2275435 2276895 := bstep (se 1 (by rfl) ⟨1707671, by rfl⟩ : syracuseStep 2276895 = 3415343) B3415343
theorem B3415349 : Blo 2275435 3415349 := bbase (se 5 (by rfl) ⟨160094, by rfl⟩ : syracuseStep 3415349 = 320189) (by norm_num)
theorem B2276899 : Blo 2275435 2276899 := bstep (se 1 (by rfl) ⟨1707674, by rfl⟩ : syracuseStep 2276899 = 3415349) B3415349
theorem B5763413 : Blo 2275435 5763413 := bbase (se 10 (by rfl) ⟨8442, by rfl⟩ : syracuseStep 5763413 = 16885) (by norm_num)
theorem B3842275 : Blo 2275435 3842275 := bstep (se 1 (by rfl) ⟨2881706, by rfl⟩ : syracuseStep 3842275 = 5763413) B5763413
theorem B5123033 : Blo 2275435 5123033 := bstep (se 2 (by rfl) ⟨1921137, by rfl⟩ : syracuseStep 5123033 = 3842275) B3842275
theorem B3415355 : Blo 2275435 3415355 := bstep (se 1 (by rfl) ⟨2561516, by rfl⟩ : syracuseStep 3415355 = 5123033) B5123033
theorem B2276903 : Blo 2275435 2276903 := bstep (se 1 (by rfl) ⟨1707677, by rfl⟩ : syracuseStep 2276903 = 3415355) B3415355
theorem B2561521 : Blo 2275435 2561521 := bbase (se 2 (by rfl) ⟨960570, by rfl⟩ : syracuseStep 2561521 = 1921141) (by norm_num)
theorem B3415361 : Blo 2275435 3415361 := bstep (se 2 (by rfl) ⟨1280760, by rfl⟩ : syracuseStep 3415361 = 2561521) B2561521
theorem B2276907 : Blo 2275435 2276907 := bstep (se 1 (by rfl) ⟨1707680, by rfl⟩ : syracuseStep 2276907 = 3415361) B3415361
theorem B14588693 : Blo 2275435 14588693 := bbase (se 6 (by rfl) ⟨341922, by rfl⟩ : syracuseStep 14588693 = 683845) (by norm_num)
theorem B9725795 : Blo 2275435 9725795 := bstep (se 1 (by rfl) ⟨7294346, by rfl⟩ : syracuseStep 9725795 = 14588693) B14588693
theorem B6483863 : Blo 2275435 6483863 := bstep (se 1 (by rfl) ⟨4862897, by rfl⟩ : syracuseStep 6483863 = 9725795) B9725795
theorem B4322575 : Blo 2275435 4322575 := bstep (se 1 (by rfl) ⟨3241931, by rfl⟩ : syracuseStep 4322575 = 6483863) B6483863
theorem B5763433 : Blo 2275435 5763433 := bstep (se 2 (by rfl) ⟨2161287, by rfl⟩ : syracuseStep 5763433 = 4322575) B4322575
theorem B7684577 : Blo 2275435 7684577 := bstep (se 2 (by rfl) ⟨2881716, by rfl⟩ : syracuseStep 7684577 = 5763433) B5763433
theorem B5123051 : Blo 2275435 5123051 := bstep (se 1 (by rfl) ⟨3842288, by rfl⟩ : syracuseStep 5123051 = 7684577) B7684577
theorem B3415367 : Blo 2275435 3415367 := bstep (se 1 (by rfl) ⟨2561525, by rfl⟩ : syracuseStep 3415367 = 5123051) B5123051
theorem B2276911 : Blo 2275435 2276911 := bstep (se 1 (by rfl) ⟨1707683, by rfl⟩ : syracuseStep 2276911 = 3415367) B3415367
theorem B3415373 : Blo 2275435 3415373 := bbase (se 3 (by rfl) ⟨640382, by rfl⟩ : syracuseStep 3415373 = 1280765) (by norm_num)
theorem B2276915 : Blo 2275435 2276915 := bstep (se 1 (by rfl) ⟨1707686, by rfl⟩ : syracuseStep 2276915 = 3415373) B3415373
theorem B5123069 : Blo 2275435 5123069 := bbase (se 3 (by rfl) ⟨960575, by rfl⟩ : syracuseStep 5123069 = 1921151) (by norm_num)
theorem B3415379 : Blo 2275435 3415379 := bstep (se 1 (by rfl) ⟨2561534, by rfl⟩ : syracuseStep 3415379 = 5123069) B5123069
theorem B2276919 : Blo 2275435 2276919 := bstep (se 1 (by rfl) ⟨1707689, by rfl⟩ : syracuseStep 2276919 = 3415379) B3415379
theorem B3842309 : Blo 2275435 3842309 := bbase (se 4 (by rfl) ⟨360216, by rfl⟩ : syracuseStep 3842309 = 720433) (by norm_num)
theorem B2561539 : Blo 2275435 2561539 := bstep (se 1 (by rfl) ⟨1921154, by rfl⟩ : syracuseStep 2561539 = 3842309) B3842309
theorem B3415385 : Blo 2275435 3415385 := bstep (se 2 (by rfl) ⟨1280769, by rfl⟩ : syracuseStep 3415385 = 2561539) B2561539
theorem B2276923 : Blo 2275435 2276923 := bstep (se 1 (by rfl) ⟨1707692, by rfl⟩ : syracuseStep 2276923 = 3415385) B3415385
theorem B17290421 : Blo 2275435 17290421 := bbase (se 5 (by rfl) ⟨810488, by rfl⟩ : syracuseStep 17290421 = 1620977) (by norm_num)
theorem B11526947 : Blo 2275435 11526947 := bstep (se 1 (by rfl) ⟨8645210, by rfl⟩ : syracuseStep 11526947 = 17290421) B17290421
theorem B7684631 : Blo 2275435 7684631 := bstep (se 1 (by rfl) ⟨5763473, by rfl⟩ : syracuseStep 7684631 = 11526947) B11526947
theorem B5123087 : Blo 2275435 5123087 := bstep (se 1 (by rfl) ⟨3842315, by rfl⟩ : syracuseStep 5123087 = 7684631) B7684631
theorem B3415391 : Blo 2275435 3415391 := bstep (se 1 (by rfl) ⟨2561543, by rfl⟩ : syracuseStep 3415391 = 5123087) B5123087
theorem B2276927 : Blo 2275435 2276927 := bstep (se 1 (by rfl) ⟨1707695, by rfl⟩ : syracuseStep 2276927 = 3415391) B3415391
theorem B3415397 : Blo 2275435 3415397 := bbase (se 4 (by rfl) ⟨320193, by rfl⟩ : syracuseStep 3415397 = 640387) (by norm_num)
theorem B2276931 : Blo 2275435 2276931 := bstep (se 1 (by rfl) ⟨1707698, by rfl⟩ : syracuseStep 2276931 = 3415397) B3415397
theorem B4322621 : Blo 2275435 4322621 := bbase (se 3 (by rfl) ⟨810491, by rfl⟩ : syracuseStep 4322621 = 1620983) (by norm_num)
theorem B2881747 : Blo 2275435 2881747 := bstep (se 1 (by rfl) ⟨2161310, by rfl⟩ : syracuseStep 2881747 = 4322621) B4322621
theorem B3842329 : Blo 2275435 3842329 := bstep (se 2 (by rfl) ⟨1440873, by rfl⟩ : syracuseStep 3842329 = 2881747) B2881747
theorem B5123105 : Blo 2275435 5123105 := bstep (se 2 (by rfl) ⟨1921164, by rfl⟩ : syracuseStep 5123105 = 3842329) B3842329
theorem B3415403 : Blo 2275435 3415403 := bstep (se 1 (by rfl) ⟨2561552, by rfl⟩ : syracuseStep 3415403 = 5123105) B5123105
theorem B2276935 : Blo 2275435 2276935 := bstep (se 1 (by rfl) ⟨1707701, by rfl⟩ : syracuseStep 2276935 = 3415403) B3415403
theorem B2561557 : Blo 2275435 2561557 := bbase (se 6 (by rfl) ⟨60036, by rfl⟩ : syracuseStep 2561557 = 120073) (by norm_num)
theorem B3415409 : Blo 2275435 3415409 := bstep (se 2 (by rfl) ⟨1280778, by rfl⟩ : syracuseStep 3415409 = 2561557) B2561557
theorem B2276939 : Blo 2275435 2276939 := bstep (se 1 (by rfl) ⟨1707704, by rfl⟩ : syracuseStep 2276939 = 3415409) B3415409
theorem B2881757 : Blo 2275435 2881757 := bbase (se 3 (by rfl) ⟨540329, by rfl⟩ : syracuseStep 2881757 = 1080659) (by norm_num)
theorem B7684685 : Blo 2275435 7684685 := bstep (se 3 (by rfl) ⟨1440878, by rfl⟩ : syracuseStep 7684685 = 2881757) B2881757
theorem B5123123 : Blo 2275435 5123123 := bstep (se 1 (by rfl) ⟨3842342, by rfl⟩ : syracuseStep 5123123 = 7684685) B7684685
theorem B3415415 : Blo 2275435 3415415 := bstep (se 1 (by rfl) ⟨2561561, by rfl⟩ : syracuseStep 3415415 = 5123123) B5123123
theorem B2276943 : Blo 2275435 2276943 := bstep (se 1 (by rfl) ⟨1707707, by rfl⟩ : syracuseStep 2276943 = 3415415) B3415415
theorem B3415421 : Blo 2275435 3415421 := bbase (se 3 (by rfl) ⟨640391, by rfl⟩ : syracuseStep 3415421 = 1280783) (by norm_num)
theorem B2276947 : Blo 2275435 2276947 := bstep (se 1 (by rfl) ⟨1707710, by rfl⟩ : syracuseStep 2276947 = 3415421) B3415421
theorem B5123141 : Blo 2275435 5123141 := bbase (se 4 (by rfl) ⟨480294, by rfl⟩ : syracuseStep 5123141 = 960589) (by norm_num)
theorem B3415427 : Blo 2275435 3415427 := bstep (se 1 (by rfl) ⟨2561570, by rfl⟩ : syracuseStep 3415427 = 5123141) B5123141
theorem B2276951 : Blo 2275435 2276951 := bstep (se 1 (by rfl) ⟨1707713, by rfl⟩ : syracuseStep 2276951 = 3415427) B3415427
theorem B6483989 : Blo 2275435 6483989 := bbase (se 6 (by rfl) ⟨151968, by rfl⟩ : syracuseStep 6483989 = 303937) (by norm_num)
theorem B4322659 : Blo 2275435 4322659 := bstep (se 1 (by rfl) ⟨3241994, by rfl⟩ : syracuseStep 4322659 = 6483989) B6483989
theorem B5763545 : Blo 2275435 5763545 := bstep (se 2 (by rfl) ⟨2161329, by rfl⟩ : syracuseStep 5763545 = 4322659) B4322659
theorem B3842363 : Blo 2275435 3842363 := bstep (se 1 (by rfl) ⟨2881772, by rfl⟩ : syracuseStep 3842363 = 5763545) B5763545
theorem B2561575 : Blo 2275435 2561575 := bstep (se 1 (by rfl) ⟨1921181, by rfl⟩ : syracuseStep 2561575 = 3842363) B3842363
theorem B3415433 : Blo 2275435 3415433 := bstep (se 2 (by rfl) ⟨1280787, by rfl⟩ : syracuseStep 3415433 = 2561575) B2561575
theorem B2276955 : Blo 2275435 2276955 := bstep (se 1 (by rfl) ⟨1707716, by rfl⟩ : syracuseStep 2276955 = 3415433) B3415433
theorem B11527109 : Blo 2275435 11527109 := bbase (se 4 (by rfl) ⟨1080666, by rfl⟩ : syracuseStep 11527109 = 2161333) (by norm_num)
theorem B7684739 : Blo 2275435 7684739 := bstep (se 1 (by rfl) ⟨5763554, by rfl⟩ : syracuseStep 7684739 = 11527109) B11527109
theorem B5123159 : Blo 2275435 5123159 := bstep (se 1 (by rfl) ⟨3842369, by rfl⟩ : syracuseStep 5123159 = 7684739) B7684739
theorem B3415439 : Blo 2275435 3415439 := bstep (se 1 (by rfl) ⟨2561579, by rfl⟩ : syracuseStep 3415439 = 5123159) B5123159
theorem B2276959 : Blo 2275435 2276959 := bstep (se 1 (by rfl) ⟨1707719, by rfl⟩ : syracuseStep 2276959 = 3415439) B3415439
theorem B3415445 : Blo 2275435 3415445 := bbase (se 6 (by rfl) ⟨80049, by rfl⟩ : syracuseStep 3415445 = 160099) (by norm_num)
theorem B2276963 : Blo 2275435 2276963 := bstep (se 1 (by rfl) ⟨1707722, by rfl⟩ : syracuseStep 2276963 = 3415445) B3415445
theorem B5193077 : Blo 2275435 5193077 := bbase (se 5 (by rfl) ⟨243425, by rfl⟩ : syracuseStep 5193077 = 486851) (by norm_num)
theorem B13848205 : Blo 2275435 13848205 := bstep (se 3 (by rfl) ⟨2596538, by rfl⟩ : syracuseStep 13848205 = 5193077) B5193077
theorem B18464273 : Blo 2275435 18464273 := bstep (se 2 (by rfl) ⟨6924102, by rfl⟩ : syracuseStep 18464273 = 13848205) B13848205
theorem B12309515 : Blo 2275435 12309515 := bstep (se 1 (by rfl) ⟨9232136, by rfl⟩ : syracuseStep 12309515 = 18464273) B18464273
theorem B8206343 : Blo 2275435 8206343 := bstep (se 1 (by rfl) ⟨6154757, by rfl⟩ : syracuseStep 8206343 = 12309515) B12309515
theorem B5470895 : Blo 2275435 5470895 := bstep (se 1 (by rfl) ⟨4103171, by rfl⟩ : syracuseStep 5470895 = 8206343) B8206343
theorem B3647263 : Blo 2275435 3647263 := bstep (se 1 (by rfl) ⟨2735447, by rfl⟩ : syracuseStep 3647263 = 5470895) B5470895
theorem B4863017 : Blo 2275435 4863017 := bstep (se 2 (by rfl) ⟨1823631, by rfl⟩ : syracuseStep 4863017 = 3647263) B3647263
theorem B12968045 : Blo 2275435 12968045 := bstep (se 3 (by rfl) ⟨2431508, by rfl⟩ : syracuseStep 12968045 = 4863017) B4863017
theorem B8645363 : Blo 2275435 8645363 := bstep (se 1 (by rfl) ⟨6484022, by rfl⟩ : syracuseStep 8645363 = 12968045) B12968045
theorem B5763575 : Blo 2275435 5763575 := bstep (se 1 (by rfl) ⟨4322681, by rfl⟩ : syracuseStep 5763575 = 8645363) B8645363
theorem B3842383 : Blo 2275435 3842383 := bstep (se 1 (by rfl) ⟨2881787, by rfl⟩ : syracuseStep 3842383 = 5763575) B5763575
theorem B5123177 : Blo 2275435 5123177 := bstep (se 2 (by rfl) ⟨1921191, by rfl⟩ : syracuseStep 5123177 = 3842383) B3842383
theorem B3415451 : Blo 2275435 3415451 := bstep (se 1 (by rfl) ⟨2561588, by rfl⟩ : syracuseStep 3415451 = 5123177) B5123177
theorem B2276967 : Blo 2275435 2276967 := bstep (se 1 (by rfl) ⟨1707725, by rfl⟩ : syracuseStep 2276967 = 3415451) B3415451
theorem B2561593 : Blo 2275435 2561593 := bbase (se 2 (by rfl) ⟨960597, by rfl⟩ : syracuseStep 2561593 = 1921195) (by norm_num)
theorem B3415457 : Blo 2275435 3415457 := bstep (se 2 (by rfl) ⟨1280796, by rfl⟩ : syracuseStep 3415457 = 2561593) B2561593
theorem B2276971 : Blo 2275435 2276971 := bstep (se 1 (by rfl) ⟨1707728, by rfl⟩ : syracuseStep 2276971 = 3415457) B3415457
theorem B2431517 : Blo 2275435 2431517 := bbase (se 3 (by rfl) ⟨455909, by rfl⟩ : syracuseStep 2431517 = 911819) (by norm_num)
theorem B6484045 : Blo 2275435 6484045 := bstep (se 3 (by rfl) ⟨1215758, by rfl⟩ : syracuseStep 6484045 = 2431517) B2431517
theorem B8645393 : Blo 2275435 8645393 := bstep (se 2 (by rfl) ⟨3242022, by rfl⟩ : syracuseStep 8645393 = 6484045) B6484045
theorem B5763595 : Blo 2275435 5763595 := bstep (se 1 (by rfl) ⟨4322696, by rfl⟩ : syracuseStep 5763595 = 8645393) B8645393
theorem B7684793 : Blo 2275435 7684793 := bstep (se 2 (by rfl) ⟨2881797, by rfl⟩ : syracuseStep 7684793 = 5763595) B5763595
theorem B5123195 : Blo 2275435 5123195 := bstep (se 1 (by rfl) ⟨3842396, by rfl⟩ : syracuseStep 5123195 = 7684793) B7684793
theorem B3415463 : Blo 2275435 3415463 := bstep (se 1 (by rfl) ⟨2561597, by rfl⟩ : syracuseStep 3415463 = 5123195) B5123195
theorem B2276975 : Blo 2275435 2276975 := bstep (se 1 (by rfl) ⟨1707731, by rfl⟩ : syracuseStep 2276975 = 3415463) B3415463
theorem B3415469 : Blo 2275435 3415469 := bbase (se 3 (by rfl) ⟨640400, by rfl⟩ : syracuseStep 3415469 = 1280801) (by norm_num)
theorem B2276979 : Blo 2275435 2276979 := bstep (se 1 (by rfl) ⟨1707734, by rfl⟩ : syracuseStep 2276979 = 3415469) B3415469
theorem B5123213 : Blo 2275435 5123213 := bbase (se 3 (by rfl) ⟨960602, by rfl⟩ : syracuseStep 5123213 = 1921205) (by norm_num)
theorem B3415475 : Blo 2275435 3415475 := bstep (se 1 (by rfl) ⟨2561606, by rfl⟩ : syracuseStep 3415475 = 5123213) B5123213
theorem B2276983 : Blo 2275435 2276983 := bstep (se 1 (by rfl) ⟨1707737, by rfl⟩ : syracuseStep 2276983 = 3415475) B3415475
theorem B2881813 : Blo 2275435 2881813 := bbase (se 6 (by rfl) ⟨67542, by rfl⟩ : syracuseStep 2881813 = 135085) (by norm_num)
theorem B3842417 : Blo 2275435 3842417 := bstep (se 2 (by rfl) ⟨1440906, by rfl⟩ : syracuseStep 3842417 = 2881813) B2881813
theorem B2561611 : Blo 2275435 2561611 := bstep (se 1 (by rfl) ⟨1921208, by rfl⟩ : syracuseStep 2561611 = 3842417) B3842417
theorem B3415481 : Blo 2275435 3415481 := bstep (se 2 (by rfl) ⟨1280805, by rfl⟩ : syracuseStep 3415481 = 2561611) B2561611
theorem B2276987 : Blo 2275435 2276987 := bstep (se 1 (by rfl) ⟨1707740, by rfl⟩ : syracuseStep 2276987 = 3415481) B3415481
theorem B2596565 : Blo 2275435 2596565 := bbase (se 7 (by rfl) ⟨30428, by rfl⟩ : syracuseStep 2596565 = 60857) (by norm_num)
theorem B6924173 : Blo 2275435 6924173 := bstep (se 3 (by rfl) ⟨1298282, by rfl⟩ : syracuseStep 6924173 = 2596565) B2596565
theorem B73857845 : Blo 2275435 73857845 := bstep (se 5 (by rfl) ⟨3462086, by rfl⟩ : syracuseStep 73857845 = 6924173) B6924173
theorem B49238563 : Blo 2275435 49238563 := bstep (se 1 (by rfl) ⟨36928922, by rfl⟩ : syracuseStep 49238563 = 73857845) B73857845
theorem B65651417 : Blo 2275435 65651417 := bstep (se 2 (by rfl) ⟨24619281, by rfl⟩ : syracuseStep 65651417 = 49238563) B49238563
theorem B43767611 : Blo 2275435 43767611 := bstep (se 1 (by rfl) ⟨32825708, by rfl⟩ : syracuseStep 43767611 = 65651417) B65651417
theorem B29178407 : Blo 2275435 29178407 := bstep (se 1 (by rfl) ⟨21883805, by rfl⟩ : syracuseStep 29178407 = 43767611) B43767611
theorem B19452271 : Blo 2275435 19452271 := bstep (se 1 (by rfl) ⟨14589203, by rfl⟩ : syracuseStep 19452271 = 29178407) B29178407
theorem B25936361 : Blo 2275435 25936361 := bstep (se 2 (by rfl) ⟨9726135, by rfl⟩ : syracuseStep 25936361 = 19452271) B19452271
theorem B17290907 : Blo 2275435 17290907 := bstep (se 1 (by rfl) ⟨12968180, by rfl⟩ : syracuseStep 17290907 = 25936361) B25936361
theorem B11527271 : Blo 2275435 11527271 := bstep (se 1 (by rfl) ⟨8645453, by rfl⟩ : syracuseStep 11527271 = 17290907) B17290907
theorem B7684847 : Blo 2275435 7684847 := bstep (se 1 (by rfl) ⟨5763635, by rfl⟩ : syracuseStep 7684847 = 11527271) B11527271
theorem B5123231 : Blo 2275435 5123231 := bstep (se 1 (by rfl) ⟨3842423, by rfl⟩ : syracuseStep 5123231 = 7684847) B7684847
theorem B3415487 : Blo 2275435 3415487 := bstep (se 1 (by rfl) ⟨2561615, by rfl⟩ : syracuseStep 3415487 = 5123231) B5123231
theorem B2276991 : Blo 2275435 2276991 := bstep (se 1 (by rfl) ⟨1707743, by rfl⟩ : syracuseStep 2276991 = 3415487) B3415487
theorem B3415493 : Blo 2275435 3415493 := bbase (se 4 (by rfl) ⟨320202, by rfl⟩ : syracuseStep 3415493 = 640405) (by norm_num)
theorem B2276995 : Blo 2275435 2276995 := bstep (se 1 (by rfl) ⟨1707746, by rfl⟩ : syracuseStep 2276995 = 3415493) B3415493
theorem B3842437 : Blo 2275435 3842437 := bbase (se 4 (by rfl) ⟨360228, by rfl⟩ : syracuseStep 3842437 = 720457) (by norm_num)
theorem B5123249 : Blo 2275435 5123249 := bstep (se 2 (by rfl) ⟨1921218, by rfl⟩ : syracuseStep 5123249 = 3842437) B3842437
theorem B3415499 : Blo 2275435 3415499 := bstep (se 1 (by rfl) ⟨2561624, by rfl⟩ : syracuseStep 3415499 = 5123249) B5123249
theorem B2276999 : Blo 2275435 2276999 := bstep (se 1 (by rfl) ⟨1707749, by rfl⟩ : syracuseStep 2276999 = 3415499) B3415499
theorem B2561629 : Blo 2275435 2561629 := bbase (se 3 (by rfl) ⟨480305, by rfl⟩ : syracuseStep 2561629 = 960611) (by norm_num)
theorem B3415505 : Blo 2275435 3415505 := bstep (se 2 (by rfl) ⟨1280814, by rfl⟩ : syracuseStep 3415505 = 2561629) B2561629
theorem B2277003 : Blo 2275435 2277003 := bstep (se 1 (by rfl) ⟨1707752, by rfl⟩ : syracuseStep 2277003 = 3415505) B3415505
theorem B7684901 : Blo 2275435 7684901 := bbase (se 4 (by rfl) ⟨720459, by rfl⟩ : syracuseStep 7684901 = 1440919) (by norm_num)
theorem B5123267 : Blo 2275435 5123267 := bstep (se 1 (by rfl) ⟨3842450, by rfl⟩ : syracuseStep 5123267 = 7684901) B7684901
theorem B3415511 : Blo 2275435 3415511 := bstep (se 1 (by rfl) ⟨2561633, by rfl⟩ : syracuseStep 3415511 = 5123267) B5123267
theorem B2277007 : Blo 2275435 2277007 := bstep (se 1 (by rfl) ⟨1707755, by rfl⟩ : syracuseStep 2277007 = 3415511) B3415511
theorem B3415517 : Blo 2275435 3415517 := bbase (se 3 (by rfl) ⟨640409, by rfl⟩ : syracuseStep 3415517 = 1280819) (by norm_num)
theorem B2277011 : Blo 2275435 2277011 := bstep (se 1 (by rfl) ⟨1707758, by rfl⟩ : syracuseStep 2277011 = 3415517) B3415517
theorem B5123285 : Blo 2275435 5123285 := bbase (se 7 (by rfl) ⟨60038, by rfl⟩ : syracuseStep 5123285 = 120077) (by norm_num)
theorem B3415523 : Blo 2275435 3415523 := bstep (se 1 (by rfl) ⟨2561642, by rfl⟩ : syracuseStep 3415523 = 5123285) B5123285
theorem B2277015 : Blo 2275435 2277015 := bstep (se 1 (by rfl) ⟨1707761, by rfl⟩ : syracuseStep 2277015 = 3415523) B3415523
theorem B7294693 : Blo 2275435 7294693 := bbase (se 4 (by rfl) ⟨683877, by rfl⟩ : syracuseStep 7294693 = 1367755) (by norm_num)
theorem B9726257 : Blo 2275435 9726257 := bstep (se 2 (by rfl) ⟨3647346, by rfl⟩ : syracuseStep 9726257 = 7294693) B7294693
theorem B6484171 : Blo 2275435 6484171 := bstep (se 1 (by rfl) ⟨4863128, by rfl⟩ : syracuseStep 6484171 = 9726257) B9726257
theorem B8645561 : Blo 2275435 8645561 := bstep (se 2 (by rfl) ⟨3242085, by rfl⟩ : syracuseStep 8645561 = 6484171) B6484171
theorem B5763707 : Blo 2275435 5763707 := bstep (se 1 (by rfl) ⟨4322780, by rfl⟩ : syracuseStep 5763707 = 8645561) B8645561
theorem B3842471 : Blo 2275435 3842471 := bstep (se 1 (by rfl) ⟨2881853, by rfl⟩ : syracuseStep 3842471 = 5763707) B5763707
theorem B2561647 : Blo 2275435 2561647 := bstep (se 1 (by rfl) ⟨1921235, by rfl⟩ : syracuseStep 2561647 = 3842471) B3842471
theorem B3415529 : Blo 2275435 3415529 := bstep (se 2 (by rfl) ⟨1280823, by rfl⟩ : syracuseStep 3415529 = 2561647) B2561647
theorem B2277019 : Blo 2275435 2277019 := bstep (se 1 (by rfl) ⟨1707764, by rfl⟩ : syracuseStep 2277019 = 3415529) B3415529
theorem B9358325 : Blo 2275435 9358325 := bbase (se 5 (by rfl) ⟨438671, by rfl⟩ : syracuseStep 9358325 = 877343) (by norm_num)
theorem B6238883 : Blo 2275435 6238883 := bstep (se 1 (by rfl) ⟨4679162, by rfl⟩ : syracuseStep 6238883 = 9358325) B9358325
theorem B4159255 : Blo 2275435 4159255 := bstep (se 1 (by rfl) ⟨3119441, by rfl⟩ : syracuseStep 4159255 = 6238883) B6238883
theorem B5545673 : Blo 2275435 5545673 := bstep (se 2 (by rfl) ⟨2079627, by rfl⟩ : syracuseStep 5545673 = 4159255) B4159255
theorem B3697115 : Blo 2275435 3697115 := bstep (se 1 (by rfl) ⟨2772836, by rfl⟩ : syracuseStep 3697115 = 5545673) B5545673
theorem B39435893 : Blo 2275435 39435893 := bstep (se 5 (by rfl) ⟨1848557, by rfl⟩ : syracuseStep 39435893 = 3697115) B3697115
theorem B26290595 : Blo 2275435 26290595 := bstep (se 1 (by rfl) ⟨19717946, by rfl⟩ : syracuseStep 26290595 = 39435893) B39435893
theorem B17527063 : Blo 2275435 17527063 := bstep (se 1 (by rfl) ⟨13145297, by rfl⟩ : syracuseStep 17527063 = 26290595) B26290595
theorem B23369417 : Blo 2275435 23369417 := bstep (se 2 (by rfl) ⟨8763531, by rfl⟩ : syracuseStep 23369417 = 17527063) B17527063
theorem B15579611 : Blo 2275435 15579611 := bstep (se 1 (by rfl) ⟨11684708, by rfl⟩ : syracuseStep 15579611 = 23369417) B23369417
theorem B10386407 : Blo 2275435 10386407 := bstep (se 1 (by rfl) ⟨7789805, by rfl⟩ : syracuseStep 10386407 = 15579611) B15579611
theorem B27697085 : Blo 2275435 27697085 := bstep (se 3 (by rfl) ⟨5193203, by rfl⟩ : syracuseStep 27697085 = 10386407) B10386407
theorem B18464723 : Blo 2275435 18464723 := bstep (se 1 (by rfl) ⟨13848542, by rfl⟩ : syracuseStep 18464723 = 27697085) B27697085
theorem B12309815 : Blo 2275435 12309815 := bstep (se 1 (by rfl) ⟨9232361, by rfl⟩ : syracuseStep 12309815 = 18464723) B18464723
theorem B8206543 : Blo 2275435 8206543 := bstep (se 1 (by rfl) ⟨6154907, by rfl⟩ : syracuseStep 8206543 = 12309815) B12309815
theorem B10942057 : Blo 2275435 10942057 := bstep (se 2 (by rfl) ⟨4103271, by rfl⟩ : syracuseStep 10942057 = 8206543) B8206543
theorem B14589409 : Blo 2275435 14589409 := bstep (se 2 (by rfl) ⟨5471028, by rfl⟩ : syracuseStep 14589409 = 10942057) B10942057
theorem B19452545 : Blo 2275435 19452545 := bstep (se 2 (by rfl) ⟨7294704, by rfl⟩ : syracuseStep 19452545 = 14589409) B14589409
theorem B12968363 : Blo 2275435 12968363 := bstep (se 1 (by rfl) ⟨9726272, by rfl⟩ : syracuseStep 12968363 = 19452545) B19452545
theorem B8645575 : Blo 2275435 8645575 := bstep (se 1 (by rfl) ⟨6484181, by rfl⟩ : syracuseStep 8645575 = 12968363) B12968363
theorem B11527433 : Blo 2275435 11527433 := bstep (se 2 (by rfl) ⟨4322787, by rfl⟩ : syracuseStep 11527433 = 8645575) B8645575
theorem B7684955 : Blo 2275435 7684955 := bstep (se 1 (by rfl) ⟨5763716, by rfl⟩ : syracuseStep 7684955 = 11527433) B11527433
theorem B5123303 : Blo 2275435 5123303 := bstep (se 1 (by rfl) ⟨3842477, by rfl⟩ : syracuseStep 5123303 = 7684955) B7684955
theorem B3415535 : Blo 2275435 3415535 := bstep (se 1 (by rfl) ⟨2561651, by rfl⟩ : syracuseStep 3415535 = 5123303) B5123303
theorem B2277023 : Blo 2275435 2277023 := bstep (se 1 (by rfl) ⟨1707767, by rfl⟩ : syracuseStep 2277023 = 3415535) B3415535
theorem B3415541 : Blo 2275435 3415541 := bbase (se 5 (by rfl) ⟨160103, by rfl⟩ : syracuseStep 3415541 = 320207) (by norm_num)
theorem B2277027 : Blo 2275435 2277027 := bstep (se 1 (by rfl) ⟨1707770, by rfl⟩ : syracuseStep 2277027 = 3415541) B3415541
theorem B2431577 : Blo 2275435 2431577 := bbase (se 2 (by rfl) ⟨911841, by rfl⟩ : syracuseStep 2431577 = 1823683) (by norm_num)
theorem B6484205 : Blo 2275435 6484205 := bstep (se 3 (by rfl) ⟨1215788, by rfl⟩ : syracuseStep 6484205 = 2431577) B2431577
theorem B4322803 : Blo 2275435 4322803 := bstep (se 1 (by rfl) ⟨3242102, by rfl⟩ : syracuseStep 4322803 = 6484205) B6484205
theorem B5763737 : Blo 2275435 5763737 := bstep (se 2 (by rfl) ⟨2161401, by rfl⟩ : syracuseStep 5763737 = 4322803) B4322803
theorem B3842491 : Blo 2275435 3842491 := bstep (se 1 (by rfl) ⟨2881868, by rfl⟩ : syracuseStep 3842491 = 5763737) B5763737
theorem B5123321 : Blo 2275435 5123321 := bstep (se 2 (by rfl) ⟨1921245, by rfl⟩ : syracuseStep 5123321 = 3842491) B3842491
theorem B3415547 : Blo 2275435 3415547 := bstep (se 1 (by rfl) ⟨2561660, by rfl⟩ : syracuseStep 3415547 = 5123321) B5123321
theorem B2277031 : Blo 2275435 2277031 := bstep (se 1 (by rfl) ⟨1707773, by rfl⟩ : syracuseStep 2277031 = 3415547) B3415547
theorem B2561665 : Blo 2275435 2561665 := bbase (se 2 (by rfl) ⟨960624, by rfl⟩ : syracuseStep 2561665 = 1921249) (by norm_num)
theorem B3415553 : Blo 2275435 3415553 := bstep (se 2 (by rfl) ⟨1280832, by rfl⟩ : syracuseStep 3415553 = 2561665) B2561665
theorem B2277035 : Blo 2275435 2277035 := bstep (se 1 (by rfl) ⟨1707776, by rfl⟩ : syracuseStep 2277035 = 3415553) B3415553
theorem B5763757 : Blo 2275435 5763757 := bbase (se 3 (by rfl) ⟨1080704, by rfl⟩ : syracuseStep 5763757 = 2161409) (by norm_num)
theorem B7685009 : Blo 2275435 7685009 := bstep (se 2 (by rfl) ⟨2881878, by rfl⟩ : syracuseStep 7685009 = 5763757) B5763757
theorem B5123339 : Blo 2275435 5123339 := bstep (se 1 (by rfl) ⟨3842504, by rfl⟩ : syracuseStep 5123339 = 7685009) B7685009
theorem B3415559 : Blo 2275435 3415559 := bstep (se 1 (by rfl) ⟨2561669, by rfl⟩ : syracuseStep 3415559 = 5123339) B5123339
theorem B2277039 : Blo 2275435 2277039 := bstep (se 1 (by rfl) ⟨1707779, by rfl⟩ : syracuseStep 2277039 = 3415559) B3415559
theorem B3415565 : Blo 2275435 3415565 := bbase (se 3 (by rfl) ⟨640418, by rfl⟩ : syracuseStep 3415565 = 1280837) (by norm_num)
theorem B2277043 : Blo 2275435 2277043 := bstep (se 1 (by rfl) ⟨1707782, by rfl⟩ : syracuseStep 2277043 = 3415565) B3415565
theorem B5123357 : Blo 2275435 5123357 := bbase (se 3 (by rfl) ⟨960629, by rfl⟩ : syracuseStep 5123357 = 1921259) (by norm_num)
theorem B3415571 : Blo 2275435 3415571 := bstep (se 1 (by rfl) ⟨2561678, by rfl⟩ : syracuseStep 3415571 = 5123357) B5123357
theorem B2277047 : Blo 2275435 2277047 := bstep (se 1 (by rfl) ⟨1707785, by rfl⟩ : syracuseStep 2277047 = 3415571) B3415571
theorem B3842525 : Blo 2275435 3842525 := bbase (se 3 (by rfl) ⟨720473, by rfl⟩ : syracuseStep 3842525 = 1440947) (by norm_num)
theorem B2561683 : Blo 2275435 2561683 := bstep (se 1 (by rfl) ⟨1921262, by rfl⟩ : syracuseStep 2561683 = 3842525) B3842525
theorem B3415577 : Blo 2275435 3415577 := bstep (se 2 (by rfl) ⟨1280841, by rfl⟩ : syracuseStep 3415577 = 2561683) B2561683
theorem B2277051 : Blo 2275435 2277051 := bstep (se 1 (by rfl) ⟨1707788, by rfl⟩ : syracuseStep 2277051 = 3415577) B3415577
theorem B2772877 : Blo 2275435 2772877 := bbase (se 3 (by rfl) ⟨519914, by rfl⟩ : syracuseStep 2772877 = 1039829) (by norm_num)
theorem B3697169 : Blo 2275435 3697169 := bstep (se 2 (by rfl) ⟨1386438, by rfl⟩ : syracuseStep 3697169 = 2772877) B2772877
theorem B9859117 : Blo 2275435 9859117 := bstep (se 3 (by rfl) ⟨1848584, by rfl⟩ : syracuseStep 9859117 = 3697169) B3697169
theorem B13145489 : Blo 2275435 13145489 := bstep (se 2 (by rfl) ⟨4929558, by rfl⟩ : syracuseStep 13145489 = 9859117) B9859117
theorem B8763659 : Blo 2275435 8763659 := bstep (se 1 (by rfl) ⟨6572744, by rfl⟩ : syracuseStep 8763659 = 13145489) B13145489
theorem B5842439 : Blo 2275435 5842439 := bstep (se 1 (by rfl) ⟨4381829, by rfl⟩ : syracuseStep 5842439 = 8763659) B8763659
theorem B3894959 : Blo 2275435 3894959 := bstep (se 1 (by rfl) ⟨2921219, by rfl⟩ : syracuseStep 3894959 = 5842439) B5842439
theorem B2596639 : Blo 2275435 2596639 := bstep (se 1 (by rfl) ⟨1947479, by rfl⟩ : syracuseStep 2596639 = 3894959) B3894959
theorem B3462185 : Blo 2275435 3462185 := bstep (se 2 (by rfl) ⟨1298319, by rfl⟩ : syracuseStep 3462185 = 2596639) B2596639
theorem B2308123 : Blo 2275435 2308123 := bstep (se 1 (by rfl) ⟨1731092, by rfl⟩ : syracuseStep 2308123 = 3462185) B3462185
theorem B3077497 : Blo 2275435 3077497 := bstep (se 2 (by rfl) ⟨1154061, by rfl⟩ : syracuseStep 3077497 = 2308123) B2308123
theorem B16413317 : Blo 2275435 16413317 := bstep (se 4 (by rfl) ⟨1538748, by rfl⟩ : syracuseStep 16413317 = 3077497) B3077497
theorem B10942211 : Blo 2275435 10942211 := bstep (se 1 (by rfl) ⟨8206658, by rfl⟩ : syracuseStep 10942211 = 16413317) B16413317
theorem B7294807 : Blo 2275435 7294807 := bstep (se 1 (by rfl) ⟨5471105, by rfl⟩ : syracuseStep 7294807 = 10942211) B10942211
theorem B9726409 : Blo 2275435 9726409 := bstep (se 2 (by rfl) ⟨3647403, by rfl⟩ : syracuseStep 9726409 = 7294807) B7294807
theorem B12968545 : Blo 2275435 12968545 := bstep (se 2 (by rfl) ⟨4863204, by rfl⟩ : syracuseStep 12968545 = 9726409) B9726409
theorem B17291393 : Blo 2275435 17291393 := bstep (se 2 (by rfl) ⟨6484272, by rfl⟩ : syracuseStep 17291393 = 12968545) B12968545
theorem B11527595 : Blo 2275435 11527595 := bstep (se 1 (by rfl) ⟨8645696, by rfl⟩ : syracuseStep 11527595 = 17291393) B17291393
theorem B7685063 : Blo 2275435 7685063 := bstep (se 1 (by rfl) ⟨5763797, by rfl⟩ : syracuseStep 7685063 = 11527595) B11527595
theorem B5123375 : Blo 2275435 5123375 := bstep (se 1 (by rfl) ⟨3842531, by rfl⟩ : syracuseStep 5123375 = 7685063) B7685063
theorem B3415583 : Blo 2275435 3415583 := bstep (se 1 (by rfl) ⟨2561687, by rfl⟩ : syracuseStep 3415583 = 5123375) B5123375
theorem B2277055 : Blo 2275435 2277055 := bstep (se 1 (by rfl) ⟨1707791, by rfl⟩ : syracuseStep 2277055 = 3415583) B3415583
theorem B3415589 : Blo 2275435 3415589 := bbase (se 4 (by rfl) ⟨320211, by rfl⟩ : syracuseStep 3415589 = 640423) (by norm_num)
theorem B2277059 : Blo 2275435 2277059 := bstep (se 1 (by rfl) ⟨1707794, by rfl⟩ : syracuseStep 2277059 = 3415589) B3415589
theorem B2881909 : Blo 2275435 2881909 := bbase (se 5 (by rfl) ⟨135089, by rfl⟩ : syracuseStep 2881909 = 270179) (by norm_num)
theorem B3842545 : Blo 2275435 3842545 := bstep (se 2 (by rfl) ⟨1440954, by rfl⟩ : syracuseStep 3842545 = 2881909) B2881909
theorem B5123393 : Blo 2275435 5123393 := bstep (se 2 (by rfl) ⟨1921272, by rfl⟩ : syracuseStep 5123393 = 3842545) B3842545
theorem B3415595 : Blo 2275435 3415595 := bstep (se 1 (by rfl) ⟨2561696, by rfl⟩ : syracuseStep 3415595 = 5123393) B5123393
theorem B2277063 : Blo 2275435 2277063 := bstep (se 1 (by rfl) ⟨1707797, by rfl⟩ : syracuseStep 2277063 = 3415595) B3415595
theorem B2561701 : Blo 2275435 2561701 := bbase (se 4 (by rfl) ⟨240159, by rfl⟩ : syracuseStep 2561701 = 480319) (by norm_num)
theorem B3415601 : Blo 2275435 3415601 := bstep (se 2 (by rfl) ⟨1280850, by rfl⟩ : syracuseStep 3415601 = 2561701) B2561701
theorem B2277067 : Blo 2275435 2277067 := bstep (se 1 (by rfl) ⟨1707800, by rfl⟩ : syracuseStep 2277067 = 3415601) B3415601
theorem B10386629 : Blo 2275435 10386629 := bbase (se 4 (by rfl) ⟨973746, by rfl⟩ : syracuseStep 10386629 = 1947493) (by norm_num)
theorem B6924419 : Blo 2275435 6924419 := bstep (se 1 (by rfl) ⟨5193314, by rfl⟩ : syracuseStep 6924419 = 10386629) B10386629
theorem B4616279 : Blo 2275435 4616279 := bstep (se 1 (by rfl) ⟨3462209, by rfl⟩ : syracuseStep 4616279 = 6924419) B6924419
theorem B3077519 : Blo 2275435 3077519 := bstep (se 1 (by rfl) ⟨2308139, by rfl⟩ : syracuseStep 3077519 = 4616279) B4616279
theorem B32826869 : Blo 2275435 32826869 := bstep (se 5 (by rfl) ⟨1538759, by rfl⟩ : syracuseStep 32826869 = 3077519) B3077519
theorem B21884579 : Blo 2275435 21884579 := bstep (se 1 (by rfl) ⟨16413434, by rfl⟩ : syracuseStep 21884579 = 32826869) B32826869
theorem B14589719 : Blo 2275435 14589719 := bstep (se 1 (by rfl) ⟨10942289, by rfl⟩ : syracuseStep 14589719 = 21884579) B21884579
theorem B9726479 : Blo 2275435 9726479 := bstep (se 1 (by rfl) ⟨7294859, by rfl⟩ : syracuseStep 9726479 = 14589719) B14589719
theorem B6484319 : Blo 2275435 6484319 := bstep (se 1 (by rfl) ⟨4863239, by rfl⟩ : syracuseStep 6484319 = 9726479) B9726479
theorem B4322879 : Blo 2275435 4322879 := bstep (se 1 (by rfl) ⟨3242159, by rfl⟩ : syracuseStep 4322879 = 6484319) B6484319
theorem B2881919 : Blo 2275435 2881919 := bstep (se 1 (by rfl) ⟨2161439, by rfl⟩ : syracuseStep 2881919 = 4322879) B4322879
theorem B7685117 : Blo 2275435 7685117 := bstep (se 3 (by rfl) ⟨1440959, by rfl⟩ : syracuseStep 7685117 = 2881919) B2881919
theorem B5123411 : Blo 2275435 5123411 := bstep (se 1 (by rfl) ⟨3842558, by rfl⟩ : syracuseStep 5123411 = 7685117) B7685117
theorem B3415607 : Blo 2275435 3415607 := bstep (se 1 (by rfl) ⟨2561705, by rfl⟩ : syracuseStep 3415607 = 5123411) B5123411
theorem B2277071 : Blo 2275435 2277071 := bstep (se 1 (by rfl) ⟨1707803, by rfl⟩ : syracuseStep 2277071 = 3415607) B3415607
theorem B3415613 : Blo 2275435 3415613 := bbase (se 3 (by rfl) ⟨640427, by rfl⟩ : syracuseStep 3415613 = 1280855) (by norm_num)
theorem B2277075 : Blo 2275435 2277075 := bstep (se 1 (by rfl) ⟨1707806, by rfl⟩ : syracuseStep 2277075 = 3415613) B3415613
theorem B5123429 : Blo 2275435 5123429 := bbase (se 4 (by rfl) ⟨480321, by rfl⟩ : syracuseStep 5123429 = 960643) (by norm_num)
theorem B3415619 : Blo 2275435 3415619 := bstep (se 1 (by rfl) ⟨2561714, by rfl⟩ : syracuseStep 3415619 = 5123429) B5123429
theorem B2277079 : Blo 2275435 2277079 := bstep (se 1 (by rfl) ⟨1707809, by rfl⟩ : syracuseStep 2277079 = 3415619) B3415619
theorem B5763869 : Blo 2275435 5763869 := bbase (se 3 (by rfl) ⟨1080725, by rfl⟩ : syracuseStep 5763869 = 2161451) (by norm_num)
theorem B3842579 : Blo 2275435 3842579 := bstep (se 1 (by rfl) ⟨2881934, by rfl⟩ : syracuseStep 3842579 = 5763869) B5763869
theorem B2561719 : Blo 2275435 2561719 := bstep (se 1 (by rfl) ⟨1921289, by rfl⟩ : syracuseStep 2561719 = 3842579) B3842579
theorem B3415625 : Blo 2275435 3415625 := bstep (se 2 (by rfl) ⟨1280859, by rfl⟩ : syracuseStep 3415625 = 2561719) B2561719
theorem B2277083 : Blo 2275435 2277083 := bstep (se 1 (by rfl) ⟨1707812, by rfl⟩ : syracuseStep 2277083 = 3415625) B3415625
theorem B4322909 : Blo 2275435 4322909 := bbase (se 3 (by rfl) ⟨810545, by rfl⟩ : syracuseStep 4322909 = 1621091) (by norm_num)
theorem B11527757 : Blo 2275435 11527757 := bstep (se 3 (by rfl) ⟨2161454, by rfl⟩ : syracuseStep 11527757 = 4322909) B4322909
theorem B7685171 : Blo 2275435 7685171 := bstep (se 1 (by rfl) ⟨5763878, by rfl⟩ : syracuseStep 7685171 = 11527757) B11527757
theorem B5123447 : Blo 2275435 5123447 := bstep (se 1 (by rfl) ⟨3842585, by rfl⟩ : syracuseStep 5123447 = 7685171) B7685171
theorem B3415631 : Blo 2275435 3415631 := bstep (se 1 (by rfl) ⟨2561723, by rfl⟩ : syracuseStep 3415631 = 5123447) B5123447
theorem B2277087 : Blo 2275435 2277087 := bstep (se 1 (by rfl) ⟨1707815, by rfl⟩ : syracuseStep 2277087 = 3415631) B3415631
theorem B3415637 : Blo 2275435 3415637 := bbase (se 8 (by rfl) ⟨20013, by rfl⟩ : syracuseStep 3415637 = 40027) (by norm_num)
theorem B2277091 : Blo 2275435 2277091 := bstep (se 1 (by rfl) ⟨1707818, by rfl⟩ : syracuseStep 2277091 = 3415637) B3415637
theorem B9726581 : Blo 2275435 9726581 := bbase (se 5 (by rfl) ⟨455933, by rfl⟩ : syracuseStep 9726581 = 911867) (by norm_num)
theorem B6484387 : Blo 2275435 6484387 := bstep (se 1 (by rfl) ⟨4863290, by rfl⟩ : syracuseStep 6484387 = 9726581) B9726581
theorem B8645849 : Blo 2275435 8645849 := bstep (se 2 (by rfl) ⟨3242193, by rfl⟩ : syracuseStep 8645849 = 6484387) B6484387
theorem B5763899 : Blo 2275435 5763899 := bstep (se 1 (by rfl) ⟨4322924, by rfl⟩ : syracuseStep 5763899 = 8645849) B8645849
theorem B3842599 : Blo 2275435 3842599 := bstep (se 1 (by rfl) ⟨2881949, by rfl⟩ : syracuseStep 3842599 = 5763899) B5763899
theorem B5123465 : Blo 2275435 5123465 := bstep (se 2 (by rfl) ⟨1921299, by rfl⟩ : syracuseStep 5123465 = 3842599) B3842599
theorem B3415643 : Blo 2275435 3415643 := bstep (se 1 (by rfl) ⟨2561732, by rfl⟩ : syracuseStep 3415643 = 5123465) B5123465
theorem B2277095 : Blo 2275435 2277095 := bstep (se 1 (by rfl) ⟨1707821, by rfl⟩ : syracuseStep 2277095 = 3415643) B3415643
theorem B2561737 : Blo 2275435 2561737 := bbase (se 2 (by rfl) ⟨960651, by rfl⟩ : syracuseStep 2561737 = 1921303) (by norm_num)
theorem B3415649 : Blo 2275435 3415649 := bstep (se 2 (by rfl) ⟨1280868, by rfl⟩ : syracuseStep 3415649 = 2561737) B2561737
theorem B2277099 : Blo 2275435 2277099 := bstep (se 1 (by rfl) ⟨1707824, by rfl⟩ : syracuseStep 2277099 = 3415649) B3415649
theorem B5471221 : Blo 2275435 5471221 := bbase (se 5 (by rfl) ⟨256463, by rfl⟩ : syracuseStep 5471221 = 512927) (by norm_num)
theorem B7294961 : Blo 2275435 7294961 := bstep (se 2 (by rfl) ⟨2735610, by rfl⟩ : syracuseStep 7294961 = 5471221) B5471221
theorem B19453229 : Blo 2275435 19453229 := bstep (se 3 (by rfl) ⟨3647480, by rfl⟩ : syracuseStep 19453229 = 7294961) B7294961
theorem B12968819 : Blo 2275435 12968819 := bstep (se 1 (by rfl) ⟨9726614, by rfl⟩ : syracuseStep 12968819 = 19453229) B19453229
theorem B8645879 : Blo 2275435 8645879 := bstep (se 1 (by rfl) ⟨6484409, by rfl⟩ : syracuseStep 8645879 = 12968819) B12968819
theorem B5763919 : Blo 2275435 5763919 := bstep (se 1 (by rfl) ⟨4322939, by rfl⟩ : syracuseStep 5763919 = 8645879) B8645879
theorem B7685225 : Blo 2275435 7685225 := bstep (se 2 (by rfl) ⟨2881959, by rfl⟩ : syracuseStep 7685225 = 5763919) B5763919
theorem B5123483 : Blo 2275435 5123483 := bstep (se 1 (by rfl) ⟨3842612, by rfl⟩ : syracuseStep 5123483 = 7685225) B7685225
theorem B3415655 : Blo 2275435 3415655 := bstep (se 1 (by rfl) ⟨2561741, by rfl⟩ : syracuseStep 3415655 = 5123483) B5123483
theorem B2277103 : Blo 2275435 2277103 := bstep (se 1 (by rfl) ⟨1707827, by rfl⟩ : syracuseStep 2277103 = 3415655) B3415655
theorem B3415661 : Blo 2275435 3415661 := bbase (se 3 (by rfl) ⟨640436, by rfl⟩ : syracuseStep 3415661 = 1280873) (by norm_num)
theorem B2277107 : Blo 2275435 2277107 := bstep (se 1 (by rfl) ⟨1707830, by rfl⟩ : syracuseStep 2277107 = 3415661) B3415661
theorem B5123501 : Blo 2275435 5123501 := bbase (se 3 (by rfl) ⟨960656, by rfl⟩ : syracuseStep 5123501 = 1921313) (by norm_num)
theorem B3415667 : Blo 2275435 3415667 := bstep (se 1 (by rfl) ⟨2561750, by rfl⟩ : syracuseStep 3415667 = 5123501) B5123501
theorem B2277111 : Blo 2275435 2277111 := bstep (se 1 (by rfl) ⟨1707833, by rfl⟩ : syracuseStep 2277111 = 3415667) B3415667
theorem B3647501 : Blo 2275435 3647501 := bbase (se 3 (by rfl) ⟨683906, by rfl⟩ : syracuseStep 3647501 = 1367813) (by norm_num)
theorem B2431667 : Blo 2275435 2431667 := bstep (se 1 (by rfl) ⟨1823750, by rfl⟩ : syracuseStep 2431667 = 3647501) B3647501
theorem B6484445 : Blo 2275435 6484445 := bstep (se 3 (by rfl) ⟨1215833, by rfl⟩ : syracuseStep 6484445 = 2431667) B2431667
theorem B4322963 : Blo 2275435 4322963 := bstep (se 1 (by rfl) ⟨3242222, by rfl⟩ : syracuseStep 4322963 = 6484445) B6484445
theorem B2881975 : Blo 2275435 2881975 := bstep (se 1 (by rfl) ⟨2161481, by rfl⟩ : syracuseStep 2881975 = 4322963) B4322963
theorem B3842633 : Blo 2275435 3842633 := bstep (se 2 (by rfl) ⟨1440987, by rfl⟩ : syracuseStep 3842633 = 2881975) B2881975
theorem B2561755 : Blo 2275435 2561755 := bstep (se 1 (by rfl) ⟨1921316, by rfl⟩ : syracuseStep 2561755 = 3842633) B3842633
theorem B3415673 : Blo 2275435 3415673 := bstep (se 2 (by rfl) ⟨1280877, by rfl⟩ : syracuseStep 3415673 = 2561755) B2561755
theorem B2277115 : Blo 2275435 2277115 := bstep (se 1 (by rfl) ⟨1707836, by rfl⟩ : syracuseStep 2277115 = 3415673) B3415673
theorem B16637717 : Blo 2275435 16637717 := bbase (se 6 (by rfl) ⟨389946, by rfl⟩ : syracuseStep 16637717 = 779893) (by norm_num)
theorem B11091811 : Blo 2275435 11091811 := bstep (se 1 (by rfl) ⟨8318858, by rfl⟩ : syracuseStep 11091811 = 16637717) B16637717
theorem B14789081 : Blo 2275435 14789081 := bstep (se 2 (by rfl) ⟨5545905, by rfl⟩ : syracuseStep 14789081 = 11091811) B11091811
theorem B39437549 : Blo 2275435 39437549 := bstep (se 3 (by rfl) ⟨7394540, by rfl⟩ : syracuseStep 39437549 = 14789081) B14789081
theorem B26291699 : Blo 2275435 26291699 := bstep (se 1 (by rfl) ⟨19718774, by rfl⟩ : syracuseStep 26291699 = 39437549) B39437549
theorem B17527799 : Blo 2275435 17527799 := bstep (se 1 (by rfl) ⟨13145849, by rfl⟩ : syracuseStep 17527799 = 26291699) B26291699
theorem B46740797 : Blo 2275435 46740797 := bstep (se 3 (by rfl) ⟨8763899, by rfl⟩ : syracuseStep 46740797 = 17527799) B17527799
theorem B31160531 : Blo 2275435 31160531 := bstep (se 1 (by rfl) ⟨23370398, by rfl⟩ : syracuseStep 31160531 = 46740797) B46740797
theorem B20773687 : Blo 2275435 20773687 := bstep (se 1 (by rfl) ⟨15580265, by rfl⟩ : syracuseStep 20773687 = 31160531) B31160531
theorem B27698249 : Blo 2275435 27698249 := bstep (se 2 (by rfl) ⟨10386843, by rfl⟩ : syracuseStep 27698249 = 20773687) B20773687
theorem B18465499 : Blo 2275435 18465499 := bstep (se 1 (by rfl) ⟨13849124, by rfl⟩ : syracuseStep 18465499 = 27698249) B27698249
theorem B98482661 : Blo 2275435 98482661 := bstep (se 4 (by rfl) ⟨9232749, by rfl⟩ : syracuseStep 98482661 = 18465499) B18465499
theorem B65655107 : Blo 2275435 65655107 := bstep (se 1 (by rfl) ⟨49241330, by rfl⟩ : syracuseStep 65655107 = 98482661) B98482661
theorem B43770071 : Blo 2275435 43770071 := bstep (se 1 (by rfl) ⟨32827553, by rfl⟩ : syracuseStep 43770071 = 65655107) B65655107
theorem B29180047 : Blo 2275435 29180047 := bstep (se 1 (by rfl) ⟨21885035, by rfl⟩ : syracuseStep 29180047 = 43770071) B43770071
theorem B38906729 : Blo 2275435 38906729 := bstep (se 2 (by rfl) ⟨14590023, by rfl⟩ : syracuseStep 38906729 = 29180047) B29180047
theorem B25937819 : Blo 2275435 25937819 := bstep (se 1 (by rfl) ⟨19453364, by rfl⟩ : syracuseStep 25937819 = 38906729) B38906729
theorem B17291879 : Blo 2275435 17291879 := bstep (se 1 (by rfl) ⟨12968909, by rfl⟩ : syracuseStep 17291879 = 25937819) B25937819
theorem B11527919 : Blo 2275435 11527919 := bstep (se 1 (by rfl) ⟨8645939, by rfl⟩ : syracuseStep 11527919 = 17291879) B17291879
theorem B7685279 : Blo 2275435 7685279 := bstep (se 1 (by rfl) ⟨5763959, by rfl⟩ : syracuseStep 7685279 = 11527919) B11527919
theorem B5123519 : Blo 2275435 5123519 := bstep (se 1 (by rfl) ⟨3842639, by rfl⟩ : syracuseStep 5123519 = 7685279) B7685279
theorem B3415679 : Blo 2275435 3415679 := bstep (se 1 (by rfl) ⟨2561759, by rfl⟩ : syracuseStep 3415679 = 5123519) B5123519
theorem B2277119 : Blo 2275435 2277119 := bstep (se 1 (by rfl) ⟨1707839, by rfl⟩ : syracuseStep 2277119 = 3415679) B3415679
theorem B3415685 : Blo 2275435 3415685 := bbase (se 4 (by rfl) ⟨320220, by rfl⟩ : syracuseStep 3415685 = 640441) (by norm_num)
theorem B2277123 : Blo 2275435 2277123 := bstep (se 1 (by rfl) ⟨1707842, by rfl⟩ : syracuseStep 2277123 = 3415685) B3415685
theorem B3842653 : Blo 2275435 3842653 := bbase (se 3 (by rfl) ⟨720497, by rfl⟩ : syracuseStep 3842653 = 1440995) (by norm_num)
theorem B5123537 : Blo 2275435 5123537 := bstep (se 2 (by rfl) ⟨1921326, by rfl⟩ : syracuseStep 5123537 = 3842653) B3842653
theorem B3415691 : Blo 2275435 3415691 := bstep (se 1 (by rfl) ⟨2561768, by rfl⟩ : syracuseStep 3415691 = 5123537) B5123537
theorem B2277127 : Blo 2275435 2277127 := bstep (se 1 (by rfl) ⟨1707845, by rfl⟩ : syracuseStep 2277127 = 3415691) B3415691
theorem B2561773 : Blo 2275435 2561773 := bbase (se 3 (by rfl) ⟨480332, by rfl⟩ : syracuseStep 2561773 = 960665) (by norm_num)
theorem B3415697 : Blo 2275435 3415697 := bstep (se 2 (by rfl) ⟨1280886, by rfl⟩ : syracuseStep 3415697 = 2561773) B2561773
theorem B2277131 : Blo 2275435 2277131 := bstep (se 1 (by rfl) ⟨1707848, by rfl⟩ : syracuseStep 2277131 = 3415697) B3415697
theorem B7685333 : Blo 2275435 7685333 := bbase (se 7 (by rfl) ⟨90062, by rfl⟩ : syracuseStep 7685333 = 180125) (by norm_num)
theorem B5123555 : Blo 2275435 5123555 := bstep (se 1 (by rfl) ⟨3842666, by rfl⟩ : syracuseStep 5123555 = 7685333) B7685333
theorem B3415703 : Blo 2275435 3415703 := bstep (se 1 (by rfl) ⟨2561777, by rfl⟩ : syracuseStep 3415703 = 5123555) B5123555
theorem B2277135 : Blo 2275435 2277135 := bstep (se 1 (by rfl) ⟨1707851, by rfl⟩ : syracuseStep 2277135 = 3415703) B3415703
theorem B3415709 : Blo 2275435 3415709 := bbase (se 3 (by rfl) ⟨640445, by rfl⟩ : syracuseStep 3415709 = 1280891) (by norm_num)
theorem B2277139 : Blo 2275435 2277139 := bstep (se 1 (by rfl) ⟨1707854, by rfl⟩ : syracuseStep 2277139 = 3415709) B3415709
theorem B5123573 : Blo 2275435 5123573 := bbase (se 5 (by rfl) ⟨240167, by rfl⟩ : syracuseStep 5123573 = 480335) (by norm_num)
theorem B3415715 : Blo 2275435 3415715 := bstep (se 1 (by rfl) ⟨2561786, by rfl⟩ : syracuseStep 3415715 = 5123573) B5123573
theorem B2277143 : Blo 2275435 2277143 := bstep (se 1 (by rfl) ⟨1707857, by rfl⟩ : syracuseStep 2277143 = 3415715) B3415715
theorem B4382005 : Blo 2275435 4382005 := bbase (se 5 (by rfl) ⟨205406, by rfl⟩ : syracuseStep 4382005 = 410813) (by norm_num)
theorem B5842673 : Blo 2275435 5842673 := bstep (se 2 (by rfl) ⟨2191002, by rfl⟩ : syracuseStep 5842673 = 4382005) B4382005
theorem B3895115 : Blo 2275435 3895115 := bstep (se 1 (by rfl) ⟨2921336, by rfl⟩ : syracuseStep 3895115 = 5842673) B5842673
theorem B10386973 : Blo 2275435 10386973 := bstep (se 3 (by rfl) ⟨1947557, by rfl⟩ : syracuseStep 10386973 = 3895115) B3895115
theorem B55397189 : Blo 2275435 55397189 := bstep (se 4 (by rfl) ⟨5193486, by rfl⟩ : syracuseStep 55397189 = 10386973) B10386973
theorem B36931459 : Blo 2275435 36931459 := bstep (se 1 (by rfl) ⟨27698594, by rfl⟩ : syracuseStep 36931459 = 55397189) B55397189
theorem B49241945 : Blo 2275435 49241945 := bstep (se 2 (by rfl) ⟨18465729, by rfl⟩ : syracuseStep 49241945 = 36931459) B36931459
theorem B32827963 : Blo 2275435 32827963 := bstep (se 1 (by rfl) ⟨24620972, by rfl⟩ : syracuseStep 32827963 = 49241945) B49241945
theorem B43770617 : Blo 2275435 43770617 := bstep (se 2 (by rfl) ⟨16413981, by rfl⟩ : syracuseStep 43770617 = 32827963) B32827963
theorem B29180411 : Blo 2275435 29180411 := bstep (se 1 (by rfl) ⟨21885308, by rfl⟩ : syracuseStep 29180411 = 43770617) B43770617
theorem B19453607 : Blo 2275435 19453607 := bstep (se 1 (by rfl) ⟨14590205, by rfl⟩ : syracuseStep 19453607 = 29180411) B29180411
theorem B12969071 : Blo 2275435 12969071 := bstep (se 1 (by rfl) ⟨9726803, by rfl⟩ : syracuseStep 12969071 = 19453607) B19453607
theorem B8646047 : Blo 2275435 8646047 := bstep (se 1 (by rfl) ⟨6484535, by rfl⟩ : syracuseStep 8646047 = 12969071) B12969071
theorem B5764031 : Blo 2275435 5764031 := bstep (se 1 (by rfl) ⟨4323023, by rfl⟩ : syracuseStep 5764031 = 8646047) B8646047
theorem B3842687 : Blo 2275435 3842687 := bstep (se 1 (by rfl) ⟨2882015, by rfl⟩ : syracuseStep 3842687 = 5764031) B5764031
theorem B2561791 : Blo 2275435 2561791 := bstep (se 1 (by rfl) ⟨1921343, by rfl⟩ : syracuseStep 2561791 = 3842687) B3842687
theorem B3415721 : Blo 2275435 3415721 := bstep (se 2 (by rfl) ⟨1280895, by rfl⟩ : syracuseStep 3415721 = 2561791) B2561791
theorem B2277147 : Blo 2275435 2277147 := bstep (se 1 (by rfl) ⟨1707860, by rfl⟩ : syracuseStep 2277147 = 3415721) B3415721
theorem B2431705 : Blo 2275435 2431705 := bbase (se 2 (by rfl) ⟨911889, by rfl⟩ : syracuseStep 2431705 = 1823779) (by norm_num)
theorem B3242273 : Blo 2275435 3242273 := bstep (se 2 (by rfl) ⟨1215852, by rfl⟩ : syracuseStep 3242273 = 2431705) B2431705
theorem B8646061 : Blo 2275435 8646061 := bstep (se 3 (by rfl) ⟨1621136, by rfl⟩ : syracuseStep 8646061 = 3242273) B3242273
theorem B11528081 : Blo 2275435 11528081 := bstep (se 2 (by rfl) ⟨4323030, by rfl⟩ : syracuseStep 11528081 = 8646061) B8646061
theorem B7685387 : Blo 2275435 7685387 := bstep (se 1 (by rfl) ⟨5764040, by rfl⟩ : syracuseStep 7685387 = 11528081) B11528081
theorem B5123591 : Blo 2275435 5123591 := bstep (se 1 (by rfl) ⟨3842693, by rfl⟩ : syracuseStep 5123591 = 7685387) B7685387
theorem B3415727 : Blo 2275435 3415727 := bstep (se 1 (by rfl) ⟨2561795, by rfl⟩ : syracuseStep 3415727 = 5123591) B5123591
theorem B2277151 : Blo 2275435 2277151 := bstep (se 1 (by rfl) ⟨1707863, by rfl⟩ : syracuseStep 2277151 = 3415727) B3415727
theorem B3415733 : Blo 2275435 3415733 := bbase (se 5 (by rfl) ⟨160112, by rfl⟩ : syracuseStep 3415733 = 320225) (by norm_num)
theorem B2277155 : Blo 2275435 2277155 := bstep (se 1 (by rfl) ⟨1707866, by rfl⟩ : syracuseStep 2277155 = 3415733) B3415733
theorem B5764061 : Blo 2275435 5764061 := bbase (se 3 (by rfl) ⟨1080761, by rfl⟩ : syracuseStep 5764061 = 2161523) (by norm_num)
theorem B3842707 : Blo 2275435 3842707 := bstep (se 1 (by rfl) ⟨2882030, by rfl⟩ : syracuseStep 3842707 = 5764061) B5764061
theorem B5123609 : Blo 2275435 5123609 := bstep (se 2 (by rfl) ⟨1921353, by rfl⟩ : syracuseStep 5123609 = 3842707) B3842707
theorem B3415739 : Blo 2275435 3415739 := bstep (se 1 (by rfl) ⟨2561804, by rfl⟩ : syracuseStep 3415739 = 5123609) B5123609
theorem B2277159 : Blo 2275435 2277159 := bstep (se 1 (by rfl) ⟨1707869, by rfl⟩ : syracuseStep 2277159 = 3415739) B3415739
theorem B2561809 : Blo 2275435 2561809 := bbase (se 2 (by rfl) ⟨960678, by rfl⟩ : syracuseStep 2561809 = 1921357) (by norm_num)
theorem B3415745 : Blo 2275435 3415745 := bstep (se 2 (by rfl) ⟨1280904, by rfl⟩ : syracuseStep 3415745 = 2561809) B2561809
theorem B2277163 : Blo 2275435 2277163 := bstep (se 1 (by rfl) ⟨1707872, by rfl⟩ : syracuseStep 2277163 = 3415745) B3415745
theorem B4323061 : Blo 2275435 4323061 := bbase (se 5 (by rfl) ⟨202643, by rfl⟩ : syracuseStep 4323061 = 405287) (by norm_num)
theorem B5764081 : Blo 2275435 5764081 := bstep (se 2 (by rfl) ⟨2161530, by rfl⟩ : syracuseStep 5764081 = 4323061) B4323061
theorem B7685441 : Blo 2275435 7685441 := bstep (se 2 (by rfl) ⟨2882040, by rfl⟩ : syracuseStep 7685441 = 5764081) B5764081
theorem B5123627 : Blo 2275435 5123627 := bstep (se 1 (by rfl) ⟨3842720, by rfl⟩ : syracuseStep 5123627 = 7685441) B7685441
theorem B3415751 : Blo 2275435 3415751 := bstep (se 1 (by rfl) ⟨2561813, by rfl⟩ : syracuseStep 3415751 = 5123627) B5123627
theorem B2277167 : Blo 2275435 2277167 := bstep (se 1 (by rfl) ⟨1707875, by rfl⟩ : syracuseStep 2277167 = 3415751) B3415751
theorem B3415757 : Blo 2275435 3415757 := bbase (se 3 (by rfl) ⟨640454, by rfl⟩ : syracuseStep 3415757 = 1280909) (by norm_num)
theorem B2277171 : Blo 2275435 2277171 := bstep (se 1 (by rfl) ⟨1707878, by rfl⟩ : syracuseStep 2277171 = 3415757) B3415757
theorem B5123645 : Blo 2275435 5123645 := bbase (se 3 (by rfl) ⟨960683, by rfl⟩ : syracuseStep 5123645 = 1921367) (by norm_num)
theorem B3415763 : Blo 2275435 3415763 := bstep (se 1 (by rfl) ⟨2561822, by rfl⟩ : syracuseStep 3415763 = 5123645) B5123645
theorem B2277175 : Blo 2275435 2277175 := bstep (se 1 (by rfl) ⟨1707881, by rfl⟩ : syracuseStep 2277175 = 3415763) B3415763
theorem B3842741 : Blo 2275435 3842741 := bbase (se 5 (by rfl) ⟨180128, by rfl⟩ : syracuseStep 3842741 = 360257) (by norm_num)
theorem B2561827 : Blo 2275435 2561827 := bstep (se 1 (by rfl) ⟨1921370, by rfl⟩ : syracuseStep 2561827 = 3842741) B3842741
theorem B3415769 : Blo 2275435 3415769 := bstep (se 2 (by rfl) ⟨1280913, by rfl⟩ : syracuseStep 3415769 = 2561827) B2561827
theorem B2277179 : Blo 2275435 2277179 := bstep (se 1 (by rfl) ⟨1707884, by rfl⟩ : syracuseStep 2277179 = 3415769) B3415769
theorem B7790357 : Blo 2275435 7790357 := bbase (se 6 (by rfl) ⟨182586, by rfl⟩ : syracuseStep 7790357 = 365173) (by norm_num)
theorem B5193571 : Blo 2275435 5193571 := bstep (se 1 (by rfl) ⟨3895178, by rfl⟩ : syracuseStep 5193571 = 7790357) B7790357
theorem B6924761 : Blo 2275435 6924761 := bstep (se 2 (by rfl) ⟨2596785, by rfl⟩ : syracuseStep 6924761 = 5193571) B5193571
theorem B4616507 : Blo 2275435 4616507 := bstep (se 1 (by rfl) ⟨3462380, by rfl⟩ : syracuseStep 4616507 = 6924761) B6924761
theorem B3077671 : Blo 2275435 3077671 := bstep (se 1 (by rfl) ⟨2308253, by rfl⟩ : syracuseStep 3077671 = 4616507) B4616507
theorem B4103561 : Blo 2275435 4103561 := bstep (se 2 (by rfl) ⟨1538835, by rfl⟩ : syracuseStep 4103561 = 3077671) B3077671
theorem B2735707 : Blo 2275435 2735707 := bstep (se 1 (by rfl) ⟨2051780, by rfl⟩ : syracuseStep 2735707 = 4103561) B4103561
theorem B3647609 : Blo 2275435 3647609 := bstep (se 2 (by rfl) ⟨1367853, by rfl⟩ : syracuseStep 3647609 = 2735707) B2735707
theorem B2431739 : Blo 2275435 2431739 := bstep (se 1 (by rfl) ⟨1823804, by rfl⟩ : syracuseStep 2431739 = 3647609) B3647609
theorem B6484637 : Blo 2275435 6484637 := bstep (se 3 (by rfl) ⟨1215869, by rfl⟩ : syracuseStep 6484637 = 2431739) B2431739
theorem B17292365 : Blo 2275435 17292365 := bstep (se 3 (by rfl) ⟨3242318, by rfl⟩ : syracuseStep 17292365 = 6484637) B6484637
theorem B11528243 : Blo 2275435 11528243 := bstep (se 1 (by rfl) ⟨8646182, by rfl⟩ : syracuseStep 11528243 = 17292365) B17292365
theorem B7685495 : Blo 2275435 7685495 := bstep (se 1 (by rfl) ⟨5764121, by rfl⟩ : syracuseStep 7685495 = 11528243) B11528243
theorem B5123663 : Blo 2275435 5123663 := bstep (se 1 (by rfl) ⟨3842747, by rfl⟩ : syracuseStep 5123663 = 7685495) B7685495
theorem B3415775 : Blo 2275435 3415775 := bstep (se 1 (by rfl) ⟨2561831, by rfl⟩ : syracuseStep 3415775 = 5123663) B5123663
theorem B2277183 : Blo 2275435 2277183 := bstep (se 1 (by rfl) ⟨1707887, by rfl⟩ : syracuseStep 2277183 = 3415775) B3415775
theorem B3415781 : Blo 2275435 3415781 := bbase (se 4 (by rfl) ⟨320229, by rfl⟩ : syracuseStep 3415781 = 640459) (by norm_num)
theorem B2277187 : Blo 2275435 2277187 := bstep (se 1 (by rfl) ⟨1707890, by rfl⟩ : syracuseStep 2277187 = 3415781) B3415781
theorem B6484661 : Blo 2275435 6484661 := bbase (se 5 (by rfl) ⟨303968, by rfl⟩ : syracuseStep 6484661 = 607937) (by norm_num)
theorem B4323107 : Blo 2275435 4323107 := bstep (se 1 (by rfl) ⟨3242330, by rfl⟩ : syracuseStep 4323107 = 6484661) B6484661
theorem B2882071 : Blo 2275435 2882071 := bstep (se 1 (by rfl) ⟨2161553, by rfl⟩ : syracuseStep 2882071 = 4323107) B4323107
theorem B3842761 : Blo 2275435 3842761 := bstep (se 2 (by rfl) ⟨1441035, by rfl⟩ : syracuseStep 3842761 = 2882071) B2882071
theorem B5123681 : Blo 2275435 5123681 := bstep (se 2 (by rfl) ⟨1921380, by rfl⟩ : syracuseStep 5123681 = 3842761) B3842761
theorem B3415787 : Blo 2275435 3415787 := bstep (se 1 (by rfl) ⟨2561840, by rfl⟩ : syracuseStep 3415787 = 5123681) B5123681
theorem B2277191 : Blo 2275435 2277191 := bstep (se 1 (by rfl) ⟨1707893, by rfl⟩ : syracuseStep 2277191 = 3415787) B3415787
theorem B2561845 : Blo 2275435 2561845 := bbase (se 5 (by rfl) ⟨120086, by rfl⟩ : syracuseStep 2561845 = 240173) (by norm_num)
theorem B3415793 : Blo 2275435 3415793 := bstep (se 2 (by rfl) ⟨1280922, by rfl⟩ : syracuseStep 3415793 = 2561845) B2561845
theorem B2277195 : Blo 2275435 2277195 := bstep (se 1 (by rfl) ⟨1707896, by rfl⟩ : syracuseStep 2277195 = 3415793) B3415793
theorem B2882081 : Blo 2275435 2882081 := bbase (se 2 (by rfl) ⟨1080780, by rfl⟩ : syracuseStep 2882081 = 2161561) (by norm_num)
theorem B7685549 : Blo 2275435 7685549 := bstep (se 3 (by rfl) ⟨1441040, by rfl⟩ : syracuseStep 7685549 = 2882081) B2882081
theorem B5123699 : Blo 2275435 5123699 := bstep (se 1 (by rfl) ⟨3842774, by rfl⟩ : syracuseStep 5123699 = 7685549) B7685549
theorem B3415799 : Blo 2275435 3415799 := bstep (se 1 (by rfl) ⟨2561849, by rfl⟩ : syracuseStep 3415799 = 5123699) B5123699
theorem B2277199 : Blo 2275435 2277199 := bstep (se 1 (by rfl) ⟨1707899, by rfl⟩ : syracuseStep 2277199 = 3415799) B3415799
theorem B3415805 : Blo 2275435 3415805 := bbase (se 3 (by rfl) ⟨640463, by rfl⟩ : syracuseStep 3415805 = 1280927) (by norm_num)
theorem B2277203 : Blo 2275435 2277203 := bstep (se 1 (by rfl) ⟨1707902, by rfl⟩ : syracuseStep 2277203 = 3415805) B3415805
theorem B5123717 : Blo 2275435 5123717 := bbase (se 4 (by rfl) ⟨480348, by rfl⟩ : syracuseStep 5123717 = 960697) (by norm_num)
theorem B3415811 : Blo 2275435 3415811 := bstep (se 1 (by rfl) ⟨2561858, by rfl⟩ : syracuseStep 3415811 = 5123717) B5123717
theorem B2277207 : Blo 2275435 2277207 := bstep (se 1 (by rfl) ⟨1707905, by rfl⟩ : syracuseStep 2277207 = 3415811) B3415811
theorem B2735741 : Blo 2275435 2735741 := bbase (se 3 (by rfl) ⟨512951, by rfl⟩ : syracuseStep 2735741 = 1025903) (by norm_num)
theorem B7295309 : Blo 2275435 7295309 := bstep (se 3 (by rfl) ⟨1367870, by rfl⟩ : syracuseStep 7295309 = 2735741) B2735741
theorem B4863539 : Blo 2275435 4863539 := bstep (se 1 (by rfl) ⟨3647654, by rfl⟩ : syracuseStep 4863539 = 7295309) B7295309
theorem B3242359 : Blo 2275435 3242359 := bstep (se 1 (by rfl) ⟨2431769, by rfl⟩ : syracuseStep 3242359 = 4863539) B4863539
theorem B4323145 : Blo 2275435 4323145 := bstep (se 2 (by rfl) ⟨1621179, by rfl⟩ : syracuseStep 4323145 = 3242359) B3242359
theorem B5764193 : Blo 2275435 5764193 := bstep (se 2 (by rfl) ⟨2161572, by rfl⟩ : syracuseStep 5764193 = 4323145) B4323145
theorem B3842795 : Blo 2275435 3842795 := bstep (se 1 (by rfl) ⟨2882096, by rfl⟩ : syracuseStep 3842795 = 5764193) B5764193
theorem B2561863 : Blo 2275435 2561863 := bstep (se 1 (by rfl) ⟨1921397, by rfl⟩ : syracuseStep 2561863 = 3842795) B3842795
theorem B3415817 : Blo 2275435 3415817 := bstep (se 2 (by rfl) ⟨1280931, by rfl⟩ : syracuseStep 3415817 = 2561863) B2561863
theorem B2277211 : Blo 2275435 2277211 := bstep (se 1 (by rfl) ⟨1707908, by rfl⟩ : syracuseStep 2277211 = 3415817) B3415817
theorem B11528405 : Blo 2275435 11528405 := bbase (se 7 (by rfl) ⟨135098, by rfl⟩ : syracuseStep 11528405 = 270197) (by norm_num)
theorem B7685603 : Blo 2275435 7685603 := bstep (se 1 (by rfl) ⟨5764202, by rfl⟩ : syracuseStep 7685603 = 11528405) B11528405
theorem B5123735 : Blo 2275435 5123735 := bstep (se 1 (by rfl) ⟨3842801, by rfl⟩ : syracuseStep 5123735 = 7685603) B7685603
theorem B3415823 : Blo 2275435 3415823 := bstep (se 1 (by rfl) ⟨2561867, by rfl⟩ : syracuseStep 3415823 = 5123735) B5123735
theorem B2277215 : Blo 2275435 2277215 := bstep (se 1 (by rfl) ⟨1707911, by rfl⟩ : syracuseStep 2277215 = 3415823) B3415823
theorem B3415829 : Blo 2275435 3415829 := bbase (se 6 (by rfl) ⟨80058, by rfl⟩ : syracuseStep 3415829 = 160117) (by norm_num)
theorem B2277219 : Blo 2275435 2277219 := bstep (se 1 (by rfl) ⟨1707914, by rfl⟩ : syracuseStep 2277219 = 3415829) B3415829
theorem B3286613 : Blo 2275435 3286613 := bbase (se 8 (by rfl) ⟨19257, by rfl⟩ : syracuseStep 3286613 = 38515) (by norm_num)
theorem B8764301 : Blo 2275435 8764301 := bstep (se 3 (by rfl) ⟨1643306, by rfl⟩ : syracuseStep 8764301 = 3286613) B3286613
theorem B23371469 : Blo 2275435 23371469 := bstep (se 3 (by rfl) ⟨4382150, by rfl⟩ : syracuseStep 23371469 = 8764301) B8764301
theorem B15580979 : Blo 2275435 15580979 := bstep (se 1 (by rfl) ⟨11685734, by rfl⟩ : syracuseStep 15580979 = 23371469) B23371469
theorem B10387319 : Blo 2275435 10387319 := bstep (se 1 (by rfl) ⟨7790489, by rfl⟩ : syracuseStep 10387319 = 15580979) B15580979
theorem B27699517 : Blo 2275435 27699517 := bstep (se 3 (by rfl) ⟨5193659, by rfl⟩ : syracuseStep 27699517 = 10387319) B10387319
theorem B36932689 : Blo 2275435 36932689 := bstep (se 2 (by rfl) ⟨13849758, by rfl⟩ : syracuseStep 36932689 = 27699517) B27699517
theorem B49243585 : Blo 2275435 49243585 := bstep (se 2 (by rfl) ⟨18466344, by rfl⟩ : syracuseStep 49243585 = 36932689) B36932689
theorem B65658113 : Blo 2275435 65658113 := bstep (se 2 (by rfl) ⟨24621792, by rfl⟩ : syracuseStep 65658113 = 49243585) B49243585
theorem B43772075 : Blo 2275435 43772075 := bstep (se 1 (by rfl) ⟨32829056, by rfl⟩ : syracuseStep 43772075 = 65658113) B65658113
theorem B29181383 : Blo 2275435 29181383 := bstep (se 1 (by rfl) ⟨21886037, by rfl⟩ : syracuseStep 29181383 = 43772075) B43772075
theorem B19454255 : Blo 2275435 19454255 := bstep (se 1 (by rfl) ⟨14590691, by rfl⟩ : syracuseStep 19454255 = 29181383) B29181383
theorem B12969503 : Blo 2275435 12969503 := bstep (se 1 (by rfl) ⟨9727127, by rfl⟩ : syracuseStep 12969503 = 19454255) B19454255
theorem B8646335 : Blo 2275435 8646335 := bstep (se 1 (by rfl) ⟨6484751, by rfl⟩ : syracuseStep 8646335 = 12969503) B12969503
theorem B5764223 : Blo 2275435 5764223 := bstep (se 1 (by rfl) ⟨4323167, by rfl⟩ : syracuseStep 5764223 = 8646335) B8646335
theorem B3842815 : Blo 2275435 3842815 := bstep (se 1 (by rfl) ⟨2882111, by rfl⟩ : syracuseStep 3842815 = 5764223) B5764223
theorem B5123753 : Blo 2275435 5123753 := bstep (se 2 (by rfl) ⟨1921407, by rfl⟩ : syracuseStep 5123753 = 3842815) B3842815
theorem B3415835 : Blo 2275435 3415835 := bstep (se 1 (by rfl) ⟨2561876, by rfl⟩ : syracuseStep 3415835 = 5123753) B5123753
theorem B2277223 : Blo 2275435 2277223 := bstep (se 1 (by rfl) ⟨1707917, by rfl⟩ : syracuseStep 2277223 = 3415835) B3415835
theorem B2561881 : Blo 2275435 2561881 := bbase (se 2 (by rfl) ⟨960705, by rfl⟩ : syracuseStep 2561881 = 1921411) (by norm_num)
theorem B3415841 : Blo 2275435 3415841 := bstep (se 2 (by rfl) ⟨1280940, by rfl⟩ : syracuseStep 3415841 = 2561881) B2561881
theorem B2277227 : Blo 2275435 2277227 := bstep (se 1 (by rfl) ⟨1707920, by rfl⟩ : syracuseStep 2277227 = 3415841) B3415841
theorem B4863581 : Blo 2275435 4863581 := bbase (se 3 (by rfl) ⟨911921, by rfl⟩ : syracuseStep 4863581 = 1823843) (by norm_num)
theorem B3242387 : Blo 2275435 3242387 := bstep (se 1 (by rfl) ⟨2431790, by rfl⟩ : syracuseStep 3242387 = 4863581) B4863581
theorem B8646365 : Blo 2275435 8646365 := bstep (se 3 (by rfl) ⟨1621193, by rfl⟩ : syracuseStep 8646365 = 3242387) B3242387
theorem B5764243 : Blo 2275435 5764243 := bstep (se 1 (by rfl) ⟨4323182, by rfl⟩ : syracuseStep 5764243 = 8646365) B8646365
theorem B7685657 : Blo 2275435 7685657 := bstep (se 2 (by rfl) ⟨2882121, by rfl⟩ : syracuseStep 7685657 = 5764243) B5764243
theorem B5123771 : Blo 2275435 5123771 := bstep (se 1 (by rfl) ⟨3842828, by rfl⟩ : syracuseStep 5123771 = 7685657) B7685657
theorem B3415847 : Blo 2275435 3415847 := bstep (se 1 (by rfl) ⟨2561885, by rfl⟩ : syracuseStep 3415847 = 5123771) B5123771
theorem B2277231 : Blo 2275435 2277231 := bstep (se 1 (by rfl) ⟨1707923, by rfl⟩ : syracuseStep 2277231 = 3415847) B3415847
theorem B3415853 : Blo 2275435 3415853 := bbase (se 3 (by rfl) ⟨640472, by rfl⟩ : syracuseStep 3415853 = 1280945) (by norm_num)
theorem B2277235 : Blo 2275435 2277235 := bstep (se 1 (by rfl) ⟨1707926, by rfl⟩ : syracuseStep 2277235 = 3415853) B3415853
theorem B5123789 : Blo 2275435 5123789 := bbase (se 3 (by rfl) ⟨960710, by rfl⟩ : syracuseStep 5123789 = 1921421) (by norm_num)
theorem B3415859 : Blo 2275435 3415859 := bstep (se 1 (by rfl) ⟨2561894, by rfl⟩ : syracuseStep 3415859 = 5123789) B5123789
theorem B2277239 : Blo 2275435 2277239 := bstep (se 1 (by rfl) ⟨1707929, by rfl⟩ : syracuseStep 2277239 = 3415859) B3415859
theorem B2882137 : Blo 2275435 2882137 := bbase (se 2 (by rfl) ⟨1080801, by rfl⟩ : syracuseStep 2882137 = 2161603) (by norm_num)
theorem B3842849 : Blo 2275435 3842849 := bstep (se 2 (by rfl) ⟨1441068, by rfl⟩ : syracuseStep 3842849 = 2882137) B2882137
theorem B2561899 : Blo 2275435 2561899 := bstep (se 1 (by rfl) ⟨1921424, by rfl⟩ : syracuseStep 2561899 = 3842849) B3842849
theorem B3415865 : Blo 2275435 3415865 := bstep (se 2 (by rfl) ⟨1280949, by rfl⟩ : syracuseStep 3415865 = 2561899) B2561899
theorem B2277243 : Blo 2275435 2277243 := bstep (se 1 (by rfl) ⟨1707932, by rfl⟩ : syracuseStep 2277243 = 3415865) B3415865
theorem B2921465 : Blo 2275435 2921465 := bbase (se 2 (by rfl) ⟨1095549, by rfl⟩ : syracuseStep 2921465 = 2191099) (by norm_num)
theorem B7790573 : Blo 2275435 7790573 := bstep (se 3 (by rfl) ⟨1460732, by rfl⟩ : syracuseStep 7790573 = 2921465) B2921465
theorem B5193715 : Blo 2275435 5193715 := bstep (se 1 (by rfl) ⟨3895286, by rfl⟩ : syracuseStep 5193715 = 7790573) B7790573
theorem B6924953 : Blo 2275435 6924953 := bstep (se 2 (by rfl) ⟨2596857, by rfl⟩ : syracuseStep 6924953 = 5193715) B5193715
theorem B18466541 : Blo 2275435 18466541 := bstep (se 3 (by rfl) ⟨3462476, by rfl⟩ : syracuseStep 18466541 = 6924953) B6924953
theorem B12311027 : Blo 2275435 12311027 := bstep (se 1 (by rfl) ⟨9233270, by rfl⟩ : syracuseStep 12311027 = 18466541) B18466541
theorem B8207351 : Blo 2275435 8207351 := bstep (se 1 (by rfl) ⟨6155513, by rfl⟩ : syracuseStep 8207351 = 12311027) B12311027
theorem B5471567 : Blo 2275435 5471567 := bstep (se 1 (by rfl) ⟨4103675, by rfl⟩ : syracuseStep 5471567 = 8207351) B8207351
theorem B3647711 : Blo 2275435 3647711 := bstep (se 1 (by rfl) ⟨2735783, by rfl⟩ : syracuseStep 3647711 = 5471567) B5471567
theorem B9727229 : Blo 2275435 9727229 := bstep (se 3 (by rfl) ⟨1823855, by rfl⟩ : syracuseStep 9727229 = 3647711) B3647711
theorem B25939277 : Blo 2275435 25939277 := bstep (se 3 (by rfl) ⟨4863614, by rfl⟩ : syracuseStep 25939277 = 9727229) B9727229
theorem B17292851 : Blo 2275435 17292851 := bstep (se 1 (by rfl) ⟨12969638, by rfl⟩ : syracuseStep 17292851 = 25939277) B25939277
theorem B11528567 : Blo 2275435 11528567 := bstep (se 1 (by rfl) ⟨8646425, by rfl⟩ : syracuseStep 11528567 = 17292851) B17292851
theorem B7685711 : Blo 2275435 7685711 := bstep (se 1 (by rfl) ⟨5764283, by rfl⟩ : syracuseStep 7685711 = 11528567) B11528567
theorem B5123807 : Blo 2275435 5123807 := bstep (se 1 (by rfl) ⟨3842855, by rfl⟩ : syracuseStep 5123807 = 7685711) B7685711
theorem B3415871 : Blo 2275435 3415871 := bstep (se 1 (by rfl) ⟨2561903, by rfl⟩ : syracuseStep 3415871 = 5123807) B5123807
theorem B2277247 : Blo 2275435 2277247 := bstep (se 1 (by rfl) ⟨1707935, by rfl⟩ : syracuseStep 2277247 = 3415871) B3415871
theorem B3415877 : Blo 2275435 3415877 := bbase (se 4 (by rfl) ⟨320238, by rfl⟩ : syracuseStep 3415877 = 640477) (by norm_num)
theorem B2277251 : Blo 2275435 2277251 := bstep (se 1 (by rfl) ⟨1707938, by rfl⟩ : syracuseStep 2277251 = 3415877) B3415877
theorem B3842869 : Blo 2275435 3842869 := bbase (se 5 (by rfl) ⟨180134, by rfl⟩ : syracuseStep 3842869 = 360269) (by norm_num)
theorem B5123825 : Blo 2275435 5123825 := bstep (se 2 (by rfl) ⟨1921434, by rfl⟩ : syracuseStep 5123825 = 3842869) B3842869
theorem B3415883 : Blo 2275435 3415883 := bstep (se 1 (by rfl) ⟨2561912, by rfl⟩ : syracuseStep 3415883 = 5123825) B5123825
theorem B2277255 : Blo 2275435 2277255 := bstep (se 1 (by rfl) ⟨1707941, by rfl⟩ : syracuseStep 2277255 = 3415883) B3415883
theorem B2561917 : Blo 2275435 2561917 := bbase (se 3 (by rfl) ⟨480359, by rfl⟩ : syracuseStep 2561917 = 960719) (by norm_num)
theorem B3415889 : Blo 2275435 3415889 := bstep (se 2 (by rfl) ⟨1280958, by rfl⟩ : syracuseStep 3415889 = 2561917) B2561917
theorem B2277259 : Blo 2275435 2277259 := bstep (se 1 (by rfl) ⟨1707944, by rfl⟩ : syracuseStep 2277259 = 3415889) B3415889
theorem B7685765 : Blo 2275435 7685765 := bbase (se 4 (by rfl) ⟨720540, by rfl⟩ : syracuseStep 7685765 = 1441081) (by norm_num)
theorem B5123843 : Blo 2275435 5123843 := bstep (se 1 (by rfl) ⟨3842882, by rfl⟩ : syracuseStep 5123843 = 7685765) B7685765
theorem B3415895 : Blo 2275435 3415895 := bstep (se 1 (by rfl) ⟨2561921, by rfl⟩ : syracuseStep 3415895 = 5123843) B5123843
theorem B2277263 : Blo 2275435 2277263 := bstep (se 1 (by rfl) ⟨1707947, by rfl⟩ : syracuseStep 2277263 = 3415895) B3415895
theorem B3415901 : Blo 2275435 3415901 := bbase (se 3 (by rfl) ⟨640481, by rfl⟩ : syracuseStep 3415901 = 1280963) (by norm_num)
theorem B2277267 : Blo 2275435 2277267 := bstep (se 1 (by rfl) ⟨1707950, by rfl⟩ : syracuseStep 2277267 = 3415901) B3415901
theorem B5123861 : Blo 2275435 5123861 := bbase (se 6 (by rfl) ⟨120090, by rfl⟩ : syracuseStep 5123861 = 240181) (by norm_num)
theorem B3415907 : Blo 2275435 3415907 := bstep (se 1 (by rfl) ⟨2561930, by rfl⟩ : syracuseStep 3415907 = 5123861) B5123861
theorem B2277271 : Blo 2275435 2277271 := bstep (se 1 (by rfl) ⟨1707953, by rfl⟩ : syracuseStep 2277271 = 3415907) B3415907
theorem B8646533 : Blo 2275435 8646533 := bbase (se 4 (by rfl) ⟨810612, by rfl⟩ : syracuseStep 8646533 = 1621225) (by norm_num)
theorem B5764355 : Blo 2275435 5764355 := bstep (se 1 (by rfl) ⟨4323266, by rfl⟩ : syracuseStep 5764355 = 8646533) B8646533
theorem B3842903 : Blo 2275435 3842903 := bstep (se 1 (by rfl) ⟨2882177, by rfl⟩ : syracuseStep 3842903 = 5764355) B5764355
theorem B2561935 : Blo 2275435 2561935 := bstep (se 1 (by rfl) ⟨1921451, by rfl⟩ : syracuseStep 2561935 = 3842903) B3842903
theorem B3415913 : Blo 2275435 3415913 := bstep (se 2 (by rfl) ⟨1280967, by rfl⟩ : syracuseStep 3415913 = 2561935) B2561935
theorem B2277275 : Blo 2275435 2277275 := bstep (se 1 (by rfl) ⟨1707956, by rfl⟩ : syracuseStep 2277275 = 3415913) B3415913
theorem B7295525 : Blo 2275435 7295525 := bbase (se 4 (by rfl) ⟨683955, by rfl⟩ : syracuseStep 7295525 = 1367911) (by norm_num)
theorem B4863683 : Blo 2275435 4863683 := bstep (se 1 (by rfl) ⟨3647762, by rfl⟩ : syracuseStep 4863683 = 7295525) B7295525
theorem B12969821 : Blo 2275435 12969821 := bstep (se 3 (by rfl) ⟨2431841, by rfl⟩ : syracuseStep 12969821 = 4863683) B4863683
theorem B8646547 : Blo 2275435 8646547 := bstep (se 1 (by rfl) ⟨6484910, by rfl⟩ : syracuseStep 8646547 = 12969821) B12969821
theorem B11528729 : Blo 2275435 11528729 := bstep (se 2 (by rfl) ⟨4323273, by rfl⟩ : syracuseStep 11528729 = 8646547) B8646547
theorem B7685819 : Blo 2275435 7685819 := bstep (se 1 (by rfl) ⟨5764364, by rfl⟩ : syracuseStep 7685819 = 11528729) B11528729
theorem B5123879 : Blo 2275435 5123879 := bstep (se 1 (by rfl) ⟨3842909, by rfl⟩ : syracuseStep 5123879 = 7685819) B7685819
theorem B3415919 : Blo 2275435 3415919 := bstep (se 1 (by rfl) ⟨2561939, by rfl⟩ : syracuseStep 3415919 = 5123879) B5123879
theorem B2277279 : Blo 2275435 2277279 := bstep (se 1 (by rfl) ⟨1707959, by rfl⟩ : syracuseStep 2277279 = 3415919) B3415919
theorem B3415925 : Blo 2275435 3415925 := bbase (se 5 (by rfl) ⟨160121, by rfl⟩ : syracuseStep 3415925 = 320243) (by norm_num)
theorem B2277283 : Blo 2275435 2277283 := bstep (se 1 (by rfl) ⟨1707962, by rfl⟩ : syracuseStep 2277283 = 3415925) B3415925
theorem B4863701 : Blo 2275435 4863701 := bbase (se 7 (by rfl) ⟨56996, by rfl⟩ : syracuseStep 4863701 = 113993) (by norm_num)
theorem B3242467 : Blo 2275435 3242467 := bstep (se 1 (by rfl) ⟨2431850, by rfl⟩ : syracuseStep 3242467 = 4863701) B4863701
theorem B4323289 : Blo 2275435 4323289 := bstep (se 2 (by rfl) ⟨1621233, by rfl⟩ : syracuseStep 4323289 = 3242467) B3242467
theorem B5764385 : Blo 2275435 5764385 := bstep (se 2 (by rfl) ⟨2161644, by rfl⟩ : syracuseStep 5764385 = 4323289) B4323289
theorem B3842923 : Blo 2275435 3842923 := bstep (se 1 (by rfl) ⟨2882192, by rfl⟩ : syracuseStep 3842923 = 5764385) B5764385
theorem B5123897 : Blo 2275435 5123897 := bstep (se 2 (by rfl) ⟨1921461, by rfl⟩ : syracuseStep 5123897 = 3842923) B3842923
theorem B3415931 : Blo 2275435 3415931 := bstep (se 1 (by rfl) ⟨2561948, by rfl⟩ : syracuseStep 3415931 = 5123897) B5123897
theorem B2277287 : Blo 2275435 2277287 := bstep (se 1 (by rfl) ⟨1707965, by rfl⟩ : syracuseStep 2277287 = 3415931) B3415931
theorem B2561953 : Blo 2275435 2561953 := bbase (se 2 (by rfl) ⟨960732, by rfl⟩ : syracuseStep 2561953 = 1921465) (by norm_num)
theorem B3415937 : Blo 2275435 3415937 := bstep (se 2 (by rfl) ⟨1280976, by rfl⟩ : syracuseStep 3415937 = 2561953) B2561953
theorem B2277291 : Blo 2275435 2277291 := bstep (se 1 (by rfl) ⟨1707968, by rfl⟩ : syracuseStep 2277291 = 3415937) B3415937
theorem B5764405 : Blo 2275435 5764405 := bbase (se 5 (by rfl) ⟨270206, by rfl⟩ : syracuseStep 5764405 = 540413) (by norm_num)
theorem B7685873 : Blo 2275435 7685873 := bstep (se 2 (by rfl) ⟨2882202, by rfl⟩ : syracuseStep 7685873 = 5764405) B5764405
theorem B5123915 : Blo 2275435 5123915 := bstep (se 1 (by rfl) ⟨3842936, by rfl⟩ : syracuseStep 5123915 = 7685873) B7685873
theorem B3415943 : Blo 2275435 3415943 := bstep (se 1 (by rfl) ⟨2561957, by rfl⟩ : syracuseStep 3415943 = 5123915) B5123915
theorem B2277295 : Blo 2275435 2277295 := bstep (se 1 (by rfl) ⟨1707971, by rfl⟩ : syracuseStep 2277295 = 3415943) B3415943
theorem B3415949 : Blo 2275435 3415949 := bbase (se 3 (by rfl) ⟨640490, by rfl⟩ : syracuseStep 3415949 = 1280981) (by norm_num)
theorem B2277299 : Blo 2275435 2277299 := bstep (se 1 (by rfl) ⟨1707974, by rfl⟩ : syracuseStep 2277299 = 3415949) B3415949
theorem B5123933 : Blo 2275435 5123933 := bbase (se 3 (by rfl) ⟨960737, by rfl⟩ : syracuseStep 5123933 = 1921475) (by norm_num)
theorem B3415955 : Blo 2275435 3415955 := bstep (se 1 (by rfl) ⟨2561966, by rfl⟩ : syracuseStep 3415955 = 5123933) B5123933
theorem B2277303 : Blo 2275435 2277303 := bstep (se 1 (by rfl) ⟨1707977, by rfl⟩ : syracuseStep 2277303 = 3415955) B3415955
theorem B3842957 : Blo 2275435 3842957 := bbase (se 3 (by rfl) ⟨720554, by rfl⟩ : syracuseStep 3842957 = 1441109) (by norm_num)
theorem B2561971 : Blo 2275435 2561971 := bstep (se 1 (by rfl) ⟨1921478, by rfl⟩ : syracuseStep 2561971 = 3842957) B3842957
theorem B3415961 : Blo 2275435 3415961 := bstep (se 2 (by rfl) ⟨1280985, by rfl⟩ : syracuseStep 3415961 = 2561971) B2561971
theorem B2277307 : Blo 2275435 2277307 := bstep (se 1 (by rfl) ⟨1707980, by rfl⟩ : syracuseStep 2277307 = 3415961) B3415961
theorem B4616765 : Blo 2275435 4616765 := bbase (se 3 (by rfl) ⟨865643, by rfl⟩ : syracuseStep 4616765 = 1731287) (by norm_num)
theorem B3077843 : Blo 2275435 3077843 := bstep (se 1 (by rfl) ⟨2308382, by rfl⟩ : syracuseStep 3077843 = 4616765) B4616765
theorem B8207581 : Blo 2275435 8207581 := bstep (se 3 (by rfl) ⟨1538921, by rfl⟩ : syracuseStep 8207581 = 3077843) B3077843
theorem B10943441 : Blo 2275435 10943441 := bstep (se 2 (by rfl) ⟨4103790, by rfl⟩ : syracuseStep 10943441 = 8207581) B8207581
theorem B7295627 : Blo 2275435 7295627 := bstep (se 1 (by rfl) ⟨5471720, by rfl⟩ : syracuseStep 7295627 = 10943441) B10943441
theorem B19455005 : Blo 2275435 19455005 := bstep (se 3 (by rfl) ⟨3647813, by rfl⟩ : syracuseStep 19455005 = 7295627) B7295627
theorem B12970003 : Blo 2275435 12970003 := bstep (se 1 (by rfl) ⟨9727502, by rfl⟩ : syracuseStep 12970003 = 19455005) B19455005
theorem B17293337 : Blo 2275435 17293337 := bstep (se 2 (by rfl) ⟨6485001, by rfl⟩ : syracuseStep 17293337 = 12970003) B12970003
theorem B11528891 : Blo 2275435 11528891 := bstep (se 1 (by rfl) ⟨8646668, by rfl⟩ : syracuseStep 11528891 = 17293337) B17293337
theorem B7685927 : Blo 2275435 7685927 := bstep (se 1 (by rfl) ⟨5764445, by rfl⟩ : syracuseStep 7685927 = 11528891) B11528891
theorem B5123951 : Blo 2275435 5123951 := bstep (se 1 (by rfl) ⟨3842963, by rfl⟩ : syracuseStep 5123951 = 7685927) B7685927
theorem B3415967 : Blo 2275435 3415967 := bstep (se 1 (by rfl) ⟨2561975, by rfl⟩ : syracuseStep 3415967 = 5123951) B5123951
theorem B2277311 : Blo 2275435 2277311 := bstep (se 1 (by rfl) ⟨1707983, by rfl⟩ : syracuseStep 2277311 = 3415967) B3415967
theorem B3415973 : Blo 2275435 3415973 := bbase (se 4 (by rfl) ⟨320247, by rfl⟩ : syracuseStep 3415973 = 640495) (by norm_num)
theorem B2277315 : Blo 2275435 2277315 := bstep (se 1 (by rfl) ⟨1707986, by rfl⟩ : syracuseStep 2277315 = 3415973) B3415973
theorem B2882233 : Blo 2275435 2882233 := bbase (se 2 (by rfl) ⟨1080837, by rfl⟩ : syracuseStep 2882233 = 2161675) (by norm_num)
theorem B3842977 : Blo 2275435 3842977 := bstep (se 2 (by rfl) ⟨1441116, by rfl⟩ : syracuseStep 3842977 = 2882233) B2882233
theorem B5123969 : Blo 2275435 5123969 := bstep (se 2 (by rfl) ⟨1921488, by rfl⟩ : syracuseStep 5123969 = 3842977) B3842977
theorem B3415979 : Blo 2275435 3415979 := bstep (se 1 (by rfl) ⟨2561984, by rfl⟩ : syracuseStep 3415979 = 5123969) B5123969
theorem B2277319 : Blo 2275435 2277319 := bstep (se 1 (by rfl) ⟨1707989, by rfl⟩ : syracuseStep 2277319 = 3415979) B3415979
theorem B2561989 : Blo 2275435 2561989 := bbase (se 4 (by rfl) ⟨240186, by rfl⟩ : syracuseStep 2561989 = 480373) (by norm_num)
theorem B3415985 : Blo 2275435 3415985 := bstep (se 2 (by rfl) ⟨1280994, by rfl⟩ : syracuseStep 3415985 = 2561989) B2561989
theorem B2277323 : Blo 2275435 2277323 := bstep (se 1 (by rfl) ⟨1707992, by rfl⟩ : syracuseStep 2277323 = 3415985) B3415985
theorem B4323365 : Blo 2275435 4323365 := bbase (se 4 (by rfl) ⟨405315, by rfl⟩ : syracuseStep 4323365 = 810631) (by norm_num)
theorem B2882243 : Blo 2275435 2882243 := bstep (se 1 (by rfl) ⟨2161682, by rfl⟩ : syracuseStep 2882243 = 4323365) B4323365
theorem B7685981 : Blo 2275435 7685981 := bstep (se 3 (by rfl) ⟨1441121, by rfl⟩ : syracuseStep 7685981 = 2882243) B2882243
theorem B5123987 : Blo 2275435 5123987 := bstep (se 1 (by rfl) ⟨3842990, by rfl⟩ : syracuseStep 5123987 = 7685981) B7685981
theorem B3415991 : Blo 2275435 3415991 := bstep (se 1 (by rfl) ⟨2561993, by rfl⟩ : syracuseStep 3415991 = 5123987) B5123987
theorem B2277327 : Blo 2275435 2277327 := bstep (se 1 (by rfl) ⟨1707995, by rfl⟩ : syracuseStep 2277327 = 3415991) B3415991
theorem B3415997 : Blo 2275435 3415997 := bbase (se 3 (by rfl) ⟨640499, by rfl⟩ : syracuseStep 3415997 = 1280999) (by norm_num)
theorem B2277331 : Blo 2275435 2277331 := bstep (se 1 (by rfl) ⟨1707998, by rfl⟩ : syracuseStep 2277331 = 3415997) B3415997
theorem B5124005 : Blo 2275435 5124005 := bbase (se 4 (by rfl) ⟨480375, by rfl⟩ : syracuseStep 5124005 = 960751) (by norm_num)
theorem B3416003 : Blo 2275435 3416003 := bstep (se 1 (by rfl) ⟨2562002, by rfl⟩ : syracuseStep 3416003 = 5124005) B5124005
theorem B2277335 : Blo 2275435 2277335 := bstep (se 1 (by rfl) ⟨1708001, by rfl⟩ : syracuseStep 2277335 = 3416003) B3416003
theorem B5764517 : Blo 2275435 5764517 := bbase (se 4 (by rfl) ⟨540423, by rfl⟩ : syracuseStep 5764517 = 1080847) (by norm_num)
theorem B3843011 : Blo 2275435 3843011 := bstep (se 1 (by rfl) ⟨2882258, by rfl⟩ : syracuseStep 3843011 = 5764517) B5764517
theorem B2562007 : Blo 2275435 2562007 := bstep (se 1 (by rfl) ⟨1921505, by rfl⟩ : syracuseStep 2562007 = 3843011) B3843011
theorem B3416009 : Blo 2275435 3416009 := bstep (se 2 (by rfl) ⟨1281003, by rfl⟩ : syracuseStep 3416009 = 2562007) B2562007
theorem B2277339 : Blo 2275435 2277339 := bstep (se 1 (by rfl) ⟨1708004, by rfl⟩ : syracuseStep 2277339 = 3416009) B3416009
theorem B6485093 : Blo 2275435 6485093 := bbase (se 4 (by rfl) ⟨607977, by rfl⟩ : syracuseStep 6485093 = 1215955) (by norm_num)
theorem B4323395 : Blo 2275435 4323395 := bstep (se 1 (by rfl) ⟨3242546, by rfl⟩ : syracuseStep 4323395 = 6485093) B6485093
theorem B11529053 : Blo 2275435 11529053 := bstep (se 3 (by rfl) ⟨2161697, by rfl⟩ : syracuseStep 11529053 = 4323395) B4323395
theorem B7686035 : Blo 2275435 7686035 := bstep (se 1 (by rfl) ⟨5764526, by rfl⟩ : syracuseStep 7686035 = 11529053) B11529053
theorem B5124023 : Blo 2275435 5124023 := bstep (se 1 (by rfl) ⟨3843017, by rfl⟩ : syracuseStep 5124023 = 7686035) B7686035
theorem B3416015 : Blo 2275435 3416015 := bstep (se 1 (by rfl) ⟨2562011, by rfl⟩ : syracuseStep 3416015 = 5124023) B5124023
theorem B2277343 : Blo 2275435 2277343 := bstep (se 1 (by rfl) ⟨1708007, by rfl⟩ : syracuseStep 2277343 = 3416015) B3416015
theorem B3416021 : Blo 2275435 3416021 := bbase (se 7 (by rfl) ⟨40031, by rfl⟩ : syracuseStep 3416021 = 80063) (by norm_num)
theorem B2277347 : Blo 2275435 2277347 := bstep (se 1 (by rfl) ⟨1708010, by rfl⟩ : syracuseStep 2277347 = 3416021) B3416021
theorem B8646821 : Blo 2275435 8646821 := bbase (se 4 (by rfl) ⟨810639, by rfl⟩ : syracuseStep 8646821 = 1621279) (by norm_num)
theorem B5764547 : Blo 2275435 5764547 := bstep (se 1 (by rfl) ⟨4323410, by rfl⟩ : syracuseStep 5764547 = 8646821) B8646821
theorem B3843031 : Blo 2275435 3843031 := bstep (se 1 (by rfl) ⟨2882273, by rfl⟩ : syracuseStep 3843031 = 5764547) B5764547
theorem B5124041 : Blo 2275435 5124041 := bstep (se 2 (by rfl) ⟨1921515, by rfl⟩ : syracuseStep 5124041 = 3843031) B3843031
theorem B3416027 : Blo 2275435 3416027 := bstep (se 1 (by rfl) ⟨2562020, by rfl⟩ : syracuseStep 3416027 = 5124041) B5124041
theorem B2277351 : Blo 2275435 2277351 := bstep (se 1 (by rfl) ⟨1708013, by rfl⟩ : syracuseStep 2277351 = 3416027) B3416027
theorem B2562025 : Blo 2275435 2562025 := bbase (se 2 (by rfl) ⟨960759, by rfl⟩ : syracuseStep 2562025 = 1921519) (by norm_num)
theorem B3416033 : Blo 2275435 3416033 := bstep (se 2 (by rfl) ⟨1281012, by rfl⟩ : syracuseStep 3416033 = 2562025) B2562025
theorem B2277355 : Blo 2275435 2277355 := bstep (se 1 (by rfl) ⟨1708016, by rfl⟩ : syracuseStep 2277355 = 3416033) B3416033
theorem B5471837 : Blo 2275435 5471837 := bbase (se 3 (by rfl) ⟨1025969, by rfl⟩ : syracuseStep 5471837 = 2051939) (by norm_num)
theorem B3647891 : Blo 2275435 3647891 := bstep (se 1 (by rfl) ⟨2735918, by rfl⟩ : syracuseStep 3647891 = 5471837) B5471837
theorem B2431927 : Blo 2275435 2431927 := bstep (se 1 (by rfl) ⟨1823945, by rfl⟩ : syracuseStep 2431927 = 3647891) B3647891
theorem B12970277 : Blo 2275435 12970277 := bstep (se 4 (by rfl) ⟨1215963, by rfl⟩ : syracuseStep 12970277 = 2431927) B2431927
theorem B8646851 : Blo 2275435 8646851 := bstep (se 1 (by rfl) ⟨6485138, by rfl⟩ : syracuseStep 8646851 = 12970277) B12970277
theorem B5764567 : Blo 2275435 5764567 := bstep (se 1 (by rfl) ⟨4323425, by rfl⟩ : syracuseStep 5764567 = 8646851) B8646851
theorem B7686089 : Blo 2275435 7686089 := bstep (se 2 (by rfl) ⟨2882283, by rfl⟩ : syracuseStep 7686089 = 5764567) B5764567
theorem B5124059 : Blo 2275435 5124059 := bstep (se 1 (by rfl) ⟨3843044, by rfl⟩ : syracuseStep 5124059 = 7686089) B7686089
theorem B3416039 : Blo 2275435 3416039 := bstep (se 1 (by rfl) ⟨2562029, by rfl⟩ : syracuseStep 3416039 = 5124059) B5124059
theorem B2277359 : Blo 2275435 2277359 := bstep (se 1 (by rfl) ⟨1708019, by rfl⟩ : syracuseStep 2277359 = 3416039) B3416039
theorem B3416045 : Blo 2275435 3416045 := bbase (se 3 (by rfl) ⟨640508, by rfl⟩ : syracuseStep 3416045 = 1281017) (by norm_num)
theorem B2277363 : Blo 2275435 2277363 := bstep (se 1 (by rfl) ⟨1708022, by rfl⟩ : syracuseStep 2277363 = 3416045) B3416045
theorem B5124077 : Blo 2275435 5124077 := bbase (se 3 (by rfl) ⟨960764, by rfl⟩ : syracuseStep 5124077 = 1921529) (by norm_num)
theorem B3416051 : Blo 2275435 3416051 := bstep (se 1 (by rfl) ⟨2562038, by rfl⟩ : syracuseStep 3416051 = 5124077) B5124077
theorem B2277367 : Blo 2275435 2277367 := bstep (se 1 (by rfl) ⟨1708025, by rfl⟩ : syracuseStep 2277367 = 3416051) B3416051
theorem B6925333 : Blo 2275435 6925333 := bbase (se 6 (by rfl) ⟨162312, by rfl⟩ : syracuseStep 6925333 = 324625) (by norm_num)
theorem B9233777 : Blo 2275435 9233777 := bstep (se 2 (by rfl) ⟨3462666, by rfl⟩ : syracuseStep 9233777 = 6925333) B6925333
theorem B6155851 : Blo 2275435 6155851 := bstep (se 1 (by rfl) ⟨4616888, by rfl⟩ : syracuseStep 6155851 = 9233777) B9233777
theorem B8207801 : Blo 2275435 8207801 := bstep (se 2 (by rfl) ⟨3077925, by rfl⟩ : syracuseStep 8207801 = 6155851) B6155851
theorem B5471867 : Blo 2275435 5471867 := bstep (se 1 (by rfl) ⟨4103900, by rfl⟩ : syracuseStep 5471867 = 8207801) B8207801
theorem B3647911 : Blo 2275435 3647911 := bstep (se 1 (by rfl) ⟨2735933, by rfl⟩ : syracuseStep 3647911 = 5471867) B5471867
theorem B4863881 : Blo 2275435 4863881 := bstep (se 2 (by rfl) ⟨1823955, by rfl⟩ : syracuseStep 4863881 = 3647911) B3647911
theorem B3242587 : Blo 2275435 3242587 := bstep (se 1 (by rfl) ⟨2431940, by rfl⟩ : syracuseStep 3242587 = 4863881) B4863881
theorem B4323449 : Blo 2275435 4323449 := bstep (se 2 (by rfl) ⟨1621293, by rfl⟩ : syracuseStep 4323449 = 3242587) B3242587
theorem B2882299 : Blo 2275435 2882299 := bstep (se 1 (by rfl) ⟨2161724, by rfl⟩ : syracuseStep 2882299 = 4323449) B4323449
theorem B3843065 : Blo 2275435 3843065 := bstep (se 2 (by rfl) ⟨1441149, by rfl⟩ : syracuseStep 3843065 = 2882299) B2882299
theorem B2562043 : Blo 2275435 2562043 := bstep (se 1 (by rfl) ⟨1921532, by rfl⟩ : syracuseStep 2562043 = 3843065) B3843065
theorem B3416057 : Blo 2275435 3416057 := bstep (se 2 (by rfl) ⟨1281021, by rfl⟩ : syracuseStep 3416057 = 2562043) B2562043
theorem B2277371 : Blo 2275435 2277371 := bstep (se 1 (by rfl) ⟨1708028, by rfl⟩ : syracuseStep 2277371 = 3416057) B3416057
theorem B21059477 : Blo 2275435 21059477 := bbase (se 6 (by rfl) ⟨493581, by rfl⟩ : syracuseStep 21059477 = 987163) (by norm_num)
theorem B14039651 : Blo 2275435 14039651 := bstep (se 1 (by rfl) ⟨10529738, by rfl⟩ : syracuseStep 14039651 = 21059477) B21059477
theorem B9359767 : Blo 2275435 9359767 := bstep (se 1 (by rfl) ⟨7019825, by rfl⟩ : syracuseStep 9359767 = 14039651) B14039651
theorem B12479689 : Blo 2275435 12479689 := bstep (se 2 (by rfl) ⟨4679883, by rfl⟩ : syracuseStep 12479689 = 9359767) B9359767
theorem B66558341 : Blo 2275435 66558341 := bstep (se 4 (by rfl) ⟨6239844, by rfl⟩ : syracuseStep 66558341 = 12479689) B12479689
theorem B44372227 : Blo 2275435 44372227 := bstep (se 1 (by rfl) ⟨33279170, by rfl⟩ : syracuseStep 44372227 = 66558341) B66558341
theorem B59162969 : Blo 2275435 59162969 := bstep (se 2 (by rfl) ⟨22186113, by rfl⟩ : syracuseStep 59162969 = 44372227) B44372227
theorem B39441979 : Blo 2275435 39441979 := bstep (se 1 (by rfl) ⟨29581484, by rfl⟩ : syracuseStep 39441979 = 59162969) B59162969
theorem B52589305 : Blo 2275435 52589305 := bstep (se 2 (by rfl) ⟨19720989, by rfl⟩ : syracuseStep 52589305 = 39441979) B39441979
theorem B70119073 : Blo 2275435 70119073 := bstep (se 2 (by rfl) ⟨26294652, by rfl⟩ : syracuseStep 70119073 = 52589305) B52589305
theorem B373968389 : Blo 2275435 373968389 := bstep (se 4 (by rfl) ⟨35059536, by rfl⟩ : syracuseStep 373968389 = 70119073) B70119073
theorem B249312259 : Blo 2275435 249312259 := bstep (se 1 (by rfl) ⟨186984194, by rfl⟩ : syracuseStep 249312259 = 373968389) B373968389
theorem B332416345 : Blo 2275435 332416345 := bstep (se 2 (by rfl) ⟨124656129, by rfl⟩ : syracuseStep 332416345 = 249312259) B249312259
theorem B443221793 : Blo 2275435 443221793 := bstep (se 2 (by rfl) ⟨166208172, by rfl⟩ : syracuseStep 443221793 = 332416345) B332416345
theorem B295481195 : Blo 2275435 295481195 := bstep (se 1 (by rfl) ⟨221610896, by rfl⟩ : syracuseStep 295481195 = 443221793) B443221793
theorem B196987463 : Blo 2275435 196987463 := bstep (se 1 (by rfl) ⟨147740597, by rfl⟩ : syracuseStep 196987463 = 295481195) B295481195
theorem B131324975 : Blo 2275435 131324975 := bstep (se 1 (by rfl) ⟨98493731, by rfl⟩ : syracuseStep 131324975 = 196987463) B196987463
theorem B87549983 : Blo 2275435 87549983 := bstep (se 1 (by rfl) ⟨65662487, by rfl⟩ : syracuseStep 87549983 = 131324975) B131324975
theorem B58366655 : Blo 2275435 58366655 := bstep (se 1 (by rfl) ⟨43774991, by rfl⟩ : syracuseStep 58366655 = 87549983) B87549983
theorem B38911103 : Blo 2275435 38911103 := bstep (se 1 (by rfl) ⟨29183327, by rfl⟩ : syracuseStep 38911103 = 58366655) B58366655
theorem B25940735 : Blo 2275435 25940735 := bstep (se 1 (by rfl) ⟨19455551, by rfl⟩ : syracuseStep 25940735 = 38911103) B38911103
theorem B17293823 : Blo 2275435 17293823 := bstep (se 1 (by rfl) ⟨12970367, by rfl⟩ : syracuseStep 17293823 = 25940735) B25940735
theorem B11529215 : Blo 2275435 11529215 := bstep (se 1 (by rfl) ⟨8646911, by rfl⟩ : syracuseStep 11529215 = 17293823) B17293823
theorem B7686143 : Blo 2275435 7686143 := bstep (se 1 (by rfl) ⟨5764607, by rfl⟩ : syracuseStep 7686143 = 11529215) B11529215
theorem B5124095 : Blo 2275435 5124095 := bstep (se 1 (by rfl) ⟨3843071, by rfl⟩ : syracuseStep 5124095 = 7686143) B7686143
theorem B3416063 : Blo 2275435 3416063 := bstep (se 1 (by rfl) ⟨2562047, by rfl⟩ : syracuseStep 3416063 = 5124095) B5124095
theorem B2277375 : Blo 2275435 2277375 := bstep (se 1 (by rfl) ⟨1708031, by rfl⟩ : syracuseStep 2277375 = 3416063) B3416063
theorem B3416069 : Blo 2275435 3416069 := bbase (se 4 (by rfl) ⟨320256, by rfl⟩ : syracuseStep 3416069 = 640513) (by norm_num)
theorem B2277379 : Blo 2275435 2277379 := bstep (se 1 (by rfl) ⟨1708034, by rfl⟩ : syracuseStep 2277379 = 3416069) B3416069
theorem B3843085 : Blo 2275435 3843085 := bbase (se 3 (by rfl) ⟨720578, by rfl⟩ : syracuseStep 3843085 = 1441157) (by norm_num)
theorem B5124113 : Blo 2275435 5124113 := bstep (se 2 (by rfl) ⟨1921542, by rfl⟩ : syracuseStep 5124113 = 3843085) B3843085
theorem B3416075 : Blo 2275435 3416075 := bstep (se 1 (by rfl) ⟨2562056, by rfl⟩ : syracuseStep 3416075 = 5124113) B5124113
theorem B2277383 : Blo 2275435 2277383 := bstep (se 1 (by rfl) ⟨1708037, by rfl⟩ : syracuseStep 2277383 = 3416075) B3416075
theorem B2562061 : Blo 2275435 2562061 := bbase (se 3 (by rfl) ⟨480386, by rfl⟩ : syracuseStep 2562061 = 960773) (by norm_num)
theorem B3416081 : Blo 2275435 3416081 := bstep (se 2 (by rfl) ⟨1281030, by rfl⟩ : syracuseStep 3416081 = 2562061) B2562061
theorem B2277387 : Blo 2275435 2277387 := bstep (se 1 (by rfl) ⟨1708040, by rfl⟩ : syracuseStep 2277387 = 3416081) B3416081
theorem B7686197 : Blo 2275435 7686197 := bbase (se 5 (by rfl) ⟨360290, by rfl⟩ : syracuseStep 7686197 = 720581) (by norm_num)
theorem B5124131 : Blo 2275435 5124131 := bstep (se 1 (by rfl) ⟨3843098, by rfl⟩ : syracuseStep 5124131 = 7686197) B7686197
theorem B3416087 : Blo 2275435 3416087 := bstep (se 1 (by rfl) ⟨2562065, by rfl⟩ : syracuseStep 3416087 = 5124131) B5124131
theorem B2277391 : Blo 2275435 2277391 := bstep (se 1 (by rfl) ⟨1708043, by rfl⟩ : syracuseStep 2277391 = 3416087) B3416087
theorem B3416093 : Blo 2275435 3416093 := bbase (se 3 (by rfl) ⟨640517, by rfl⟩ : syracuseStep 3416093 = 1281035) (by norm_num)
theorem B2277395 : Blo 2275435 2277395 := bstep (se 1 (by rfl) ⟨1708046, by rfl⟩ : syracuseStep 2277395 = 3416093) B3416093
theorem B5124149 : Blo 2275435 5124149 := bbase (se 5 (by rfl) ⟨240194, by rfl⟩ : syracuseStep 5124149 = 480389) (by norm_num)
theorem B3416099 : Blo 2275435 3416099 := bstep (se 1 (by rfl) ⟨2562074, by rfl⟩ : syracuseStep 3416099 = 5124149) B5124149
theorem B2277399 : Blo 2275435 2277399 := bstep (se 1 (by rfl) ⟨1708049, by rfl⟩ : syracuseStep 2277399 = 3416099) B3416099
theorem B4103957 : Blo 2275435 4103957 := bbase (se 6 (by rfl) ⟨96186, by rfl⟩ : syracuseStep 4103957 = 192373) (by norm_num)
theorem B10943885 : Blo 2275435 10943885 := bstep (se 3 (by rfl) ⟨2051978, by rfl⟩ : syracuseStep 10943885 = 4103957) B4103957
theorem B7295923 : Blo 2275435 7295923 := bstep (se 1 (by rfl) ⟨5471942, by rfl⟩ : syracuseStep 7295923 = 10943885) B10943885
theorem B9727897 : Blo 2275435 9727897 := bstep (se 2 (by rfl) ⟨3647961, by rfl⟩ : syracuseStep 9727897 = 7295923) B7295923
theorem B12970529 : Blo 2275435 12970529 := bstep (se 2 (by rfl) ⟨4863948, by rfl⟩ : syracuseStep 12970529 = 9727897) B9727897
theorem B8647019 : Blo 2275435 8647019 := bstep (se 1 (by rfl) ⟨6485264, by rfl⟩ : syracuseStep 8647019 = 12970529) B12970529
theorem B5764679 : Blo 2275435 5764679 := bstep (se 1 (by rfl) ⟨4323509, by rfl⟩ : syracuseStep 5764679 = 8647019) B8647019
theorem B3843119 : Blo 2275435 3843119 := bstep (se 1 (by rfl) ⟨2882339, by rfl⟩ : syracuseStep 3843119 = 5764679) B5764679
theorem B2562079 : Blo 2275435 2562079 := bstep (se 1 (by rfl) ⟨1921559, by rfl⟩ : syracuseStep 2562079 = 3843119) B3843119
theorem B3416105 : Blo 2275435 3416105 := bstep (se 2 (by rfl) ⟨1281039, by rfl⟩ : syracuseStep 3416105 = 2562079) B2562079
theorem B2277403 : Blo 2275435 2277403 := bstep (se 1 (by rfl) ⟨1708052, by rfl⟩ : syracuseStep 2277403 = 3416105) B3416105
theorem B7115701 : Blo 2275435 7115701 := bbase (se 5 (by rfl) ⟨333548, by rfl⟩ : syracuseStep 7115701 = 667097) (by norm_num)
theorem B9487601 : Blo 2275435 9487601 := bstep (se 2 (by rfl) ⟨3557850, by rfl⟩ : syracuseStep 9487601 = 7115701) B7115701
theorem B6325067 : Blo 2275435 6325067 := bstep (se 1 (by rfl) ⟨4743800, by rfl⟩ : syracuseStep 6325067 = 9487601) B9487601
theorem B16866845 : Blo 2275435 16866845 := bstep (se 3 (by rfl) ⟨3162533, by rfl⟩ : syracuseStep 16866845 = 6325067) B6325067
theorem B11244563 : Blo 2275435 11244563 := bstep (se 1 (by rfl) ⟨8433422, by rfl⟩ : syracuseStep 11244563 = 16866845) B16866845
theorem B479768021 : Blo 2275435 479768021 := bstep (se 7 (by rfl) ⟨5622281, by rfl⟩ : syracuseStep 479768021 = 11244563) B11244563
theorem B319845347 : Blo 2275435 319845347 := bstep (se 1 (by rfl) ⟨239884010, by rfl⟩ : syracuseStep 319845347 = 479768021) B479768021
theorem B213230231 : Blo 2275435 213230231 := bstep (se 1 (by rfl) ⟨159922673, by rfl⟩ : syracuseStep 213230231 = 319845347) B319845347
theorem B142153487 : Blo 2275435 142153487 := bstep (se 1 (by rfl) ⟨106615115, by rfl⟩ : syracuseStep 142153487 = 213230231) B213230231
theorem B94768991 : Blo 2275435 94768991 := bstep (se 1 (by rfl) ⟨71076743, by rfl⟩ : syracuseStep 94768991 = 142153487) B142153487
theorem B63179327 : Blo 2275435 63179327 := bstep (se 1 (by rfl) ⟨47384495, by rfl⟩ : syracuseStep 63179327 = 94768991) B94768991
theorem B42119551 : Blo 2275435 42119551 := bstep (se 1 (by rfl) ⟨31589663, by rfl⟩ : syracuseStep 42119551 = 63179327) B63179327
theorem B56159401 : Blo 2275435 56159401 := bstep (se 2 (by rfl) ⟨21059775, by rfl⟩ : syracuseStep 56159401 = 42119551) B42119551
theorem B74879201 : Blo 2275435 74879201 := bstep (se 2 (by rfl) ⟨28079700, by rfl⟩ : syracuseStep 74879201 = 56159401) B56159401
theorem B199677869 : Blo 2275435 199677869 := bstep (se 3 (by rfl) ⟨37439600, by rfl⟩ : syracuseStep 199677869 = 74879201) B74879201
theorem B133118579 : Blo 2275435 133118579 := bstep (se 1 (by rfl) ⟨99838934, by rfl⟩ : syracuseStep 133118579 = 199677869) B199677869
theorem B88745719 : Blo 2275435 88745719 := bstep (se 1 (by rfl) ⟨66559289, by rfl⟩ : syracuseStep 88745719 = 133118579) B133118579
theorem B118327625 : Blo 2275435 118327625 := bstep (se 2 (by rfl) ⟨44372859, by rfl⟩ : syracuseStep 118327625 = 88745719) B88745719
theorem B78885083 : Blo 2275435 78885083 := bstep (se 1 (by rfl) ⟨59163812, by rfl⟩ : syracuseStep 78885083 = 118327625) B118327625
theorem B52590055 : Blo 2275435 52590055 := bstep (se 1 (by rfl) ⟨39442541, by rfl⟩ : syracuseStep 52590055 = 78885083) B78885083
theorem B70120073 : Blo 2275435 70120073 := bstep (se 2 (by rfl) ⟨26295027, by rfl⟩ : syracuseStep 70120073 = 52590055) B52590055
theorem B46746715 : Blo 2275435 46746715 := bstep (se 1 (by rfl) ⟨35060036, by rfl⟩ : syracuseStep 46746715 = 70120073) B70120073
theorem B62328953 : Blo 2275435 62328953 := bstep (se 2 (by rfl) ⟨23373357, by rfl⟩ : syracuseStep 62328953 = 46746715) B46746715
theorem B41552635 : Blo 2275435 41552635 := bstep (se 1 (by rfl) ⟨31164476, by rfl⟩ : syracuseStep 41552635 = 62328953) B62328953
theorem B55403513 : Blo 2275435 55403513 := bstep (se 2 (by rfl) ⟨20776317, by rfl⟩ : syracuseStep 55403513 = 41552635) B41552635
theorem B36935675 : Blo 2275435 36935675 := bstep (se 1 (by rfl) ⟨27701756, by rfl⟩ : syracuseStep 36935675 = 55403513) B55403513
theorem B24623783 : Blo 2275435 24623783 := bstep (se 1 (by rfl) ⟨18467837, by rfl⟩ : syracuseStep 24623783 = 36935675) B36935675
theorem B16415855 : Blo 2275435 16415855 := bstep (se 1 (by rfl) ⟨12311891, by rfl⟩ : syracuseStep 16415855 = 24623783) B24623783
theorem B10943903 : Blo 2275435 10943903 := bstep (se 1 (by rfl) ⟨8207927, by rfl⟩ : syracuseStep 10943903 = 16415855) B16415855
theorem B7295935 : Blo 2275435 7295935 := bstep (se 1 (by rfl) ⟨5471951, by rfl⟩ : syracuseStep 7295935 = 10943903) B10943903
theorem B9727913 : Blo 2275435 9727913 := bstep (se 2 (by rfl) ⟨3647967, by rfl⟩ : syracuseStep 9727913 = 7295935) B7295935
theorem B6485275 : Blo 2275435 6485275 := bstep (se 1 (by rfl) ⟨4863956, by rfl⟩ : syracuseStep 6485275 = 9727913) B9727913
theorem B8647033 : Blo 2275435 8647033 := bstep (se 2 (by rfl) ⟨3242637, by rfl⟩ : syracuseStep 8647033 = 6485275) B6485275
theorem B11529377 : Blo 2275435 11529377 := bstep (se 2 (by rfl) ⟨4323516, by rfl⟩ : syracuseStep 11529377 = 8647033) B8647033
theorem B7686251 : Blo 2275435 7686251 := bstep (se 1 (by rfl) ⟨5764688, by rfl⟩ : syracuseStep 7686251 = 11529377) B11529377
theorem B5124167 : Blo 2275435 5124167 := bstep (se 1 (by rfl) ⟨3843125, by rfl⟩ : syracuseStep 5124167 = 7686251) B7686251
theorem B3416111 : Blo 2275435 3416111 := bstep (se 1 (by rfl) ⟨2562083, by rfl⟩ : syracuseStep 3416111 = 5124167) B5124167
theorem B2277407 : Blo 2275435 2277407 := bstep (se 1 (by rfl) ⟨1708055, by rfl⟩ : syracuseStep 2277407 = 3416111) B3416111
theorem B3416117 : Blo 2275435 3416117 := bbase (se 5 (by rfl) ⟨160130, by rfl⟩ : syracuseStep 3416117 = 320261) (by norm_num)
theorem B2277411 : Blo 2275435 2277411 := bstep (se 1 (by rfl) ⟨1708058, by rfl⟩ : syracuseStep 2277411 = 3416117) B3416117
theorem B5764709 : Blo 2275435 5764709 := bbase (se 4 (by rfl) ⟨540441, by rfl⟩ : syracuseStep 5764709 = 1080883) (by norm_num)
theorem B3843139 : Blo 2275435 3843139 := bstep (se 1 (by rfl) ⟨2882354, by rfl⟩ : syracuseStep 3843139 = 5764709) B5764709
theorem B5124185 : Blo 2275435 5124185 := bstep (se 2 (by rfl) ⟨1921569, by rfl⟩ : syracuseStep 5124185 = 3843139) B3843139
theorem B3416123 : Blo 2275435 3416123 := bstep (se 1 (by rfl) ⟨2562092, by rfl⟩ : syracuseStep 3416123 = 5124185) B5124185
theorem B2277415 : Blo 2275435 2277415 := bstep (se 1 (by rfl) ⟨1708061, by rfl⟩ : syracuseStep 2277415 = 3416123) B3416123
theorem B2562097 : Blo 2275435 2562097 := bbase (se 2 (by rfl) ⟨960786, by rfl⟩ : syracuseStep 2562097 = 1921573) (by norm_num)
theorem B3416129 : Blo 2275435 3416129 := bstep (se 2 (by rfl) ⟨1281048, by rfl⟩ : syracuseStep 3416129 = 2562097) B2562097
theorem B2277419 : Blo 2275435 2277419 := bstep (se 1 (by rfl) ⟨1708064, by rfl⟩ : syracuseStep 2277419 = 3416129) B3416129
theorem B3895589 : Blo 2275435 3895589 := bbase (se 4 (by rfl) ⟨365211, by rfl⟩ : syracuseStep 3895589 = 730423) (by norm_num)
theorem B2597059 : Blo 2275435 2597059 := bstep (se 1 (by rfl) ⟨1947794, by rfl⟩ : syracuseStep 2597059 = 3895589) B3895589
theorem B3462745 : Blo 2275435 3462745 := bstep (se 2 (by rfl) ⟨1298529, by rfl⟩ : syracuseStep 3462745 = 2597059) B2597059
theorem B4616993 : Blo 2275435 4616993 := bstep (se 2 (by rfl) ⟨1731372, by rfl⟩ : syracuseStep 4616993 = 3462745) B3462745
theorem B3077995 : Blo 2275435 3077995 := bstep (se 1 (by rfl) ⟨2308496, by rfl⟩ : syracuseStep 3077995 = 4616993) B4616993
theorem B4103993 : Blo 2275435 4103993 := bstep (se 2 (by rfl) ⟨1538997, by rfl⟩ : syracuseStep 4103993 = 3077995) B3077995
theorem B10943981 : Blo 2275435 10943981 := bstep (se 3 (by rfl) ⟨2051996, by rfl⟩ : syracuseStep 10943981 = 4103993) B4103993
theorem B7295987 : Blo 2275435 7295987 := bstep (se 1 (by rfl) ⟨5471990, by rfl⟩ : syracuseStep 7295987 = 10943981) B10943981
theorem B4863991 : Blo 2275435 4863991 := bstep (se 1 (by rfl) ⟨3647993, by rfl⟩ : syracuseStep 4863991 = 7295987) B7295987
theorem B6485321 : Blo 2275435 6485321 := bstep (se 2 (by rfl) ⟨2431995, by rfl⟩ : syracuseStep 6485321 = 4863991) B4863991
theorem B4323547 : Blo 2275435 4323547 := bstep (se 1 (by rfl) ⟨3242660, by rfl⟩ : syracuseStep 4323547 = 6485321) B6485321
theorem B5764729 : Blo 2275435 5764729 := bstep (se 2 (by rfl) ⟨2161773, by rfl⟩ : syracuseStep 5764729 = 4323547) B4323547
theorem B7686305 : Blo 2275435 7686305 := bstep (se 2 (by rfl) ⟨2882364, by rfl⟩ : syracuseStep 7686305 = 5764729) B5764729
theorem B5124203 : Blo 2275435 5124203 := bstep (se 1 (by rfl) ⟨3843152, by rfl⟩ : syracuseStep 5124203 = 7686305) B7686305
theorem B3416135 : Blo 2275435 3416135 := bstep (se 1 (by rfl) ⟨2562101, by rfl⟩ : syracuseStep 3416135 = 5124203) B5124203
theorem B2277423 : Blo 2275435 2277423 := bstep (se 1 (by rfl) ⟨1708067, by rfl⟩ : syracuseStep 2277423 = 3416135) B3416135
theorem B3416141 : Blo 2275435 3416141 := bbase (se 3 (by rfl) ⟨640526, by rfl⟩ : syracuseStep 3416141 = 1281053) (by norm_num)
theorem B2277427 : Blo 2275435 2277427 := bstep (se 1 (by rfl) ⟨1708070, by rfl⟩ : syracuseStep 2277427 = 3416141) B3416141
theorem B5124221 : Blo 2275435 5124221 := bbase (se 3 (by rfl) ⟨960791, by rfl⟩ : syracuseStep 5124221 = 1921583) (by norm_num)
theorem B3416147 : Blo 2275435 3416147 := bstep (se 1 (by rfl) ⟨2562110, by rfl⟩ : syracuseStep 3416147 = 5124221) B5124221
theorem B2277431 : Blo 2275435 2277431 := bstep (se 1 (by rfl) ⟨1708073, by rfl⟩ : syracuseStep 2277431 = 3416147) B3416147
theorem B3843173 : Blo 2275435 3843173 := bbase (se 4 (by rfl) ⟨360297, by rfl⟩ : syracuseStep 3843173 = 720595) (by norm_num)
theorem B2562115 : Blo 2275435 2562115 := bstep (se 1 (by rfl) ⟨1921586, by rfl⟩ : syracuseStep 2562115 = 3843173) B3843173
theorem B3416153 : Blo 2275435 3416153 := bstep (se 2 (by rfl) ⟨1281057, by rfl⟩ : syracuseStep 3416153 = 2562115) B2562115
theorem B2277435 : Blo 2275435 2277435 := bstep (se 1 (by rfl) ⟨1708076, by rfl⟩ : syracuseStep 2277435 = 3416153) B3416153
theorem C0 (j : ℕ) (h1 : 568858 ≤ j) (h2 : j ≤ 569358) : Blo 2275435 (4 * j + 3) := by
  interval_cases j
  · exact B2275435
  · exact B2275439
  · exact B2275443
  · exact B2275447
  · exact B2275451
  · exact B2275455
  · exact B2275459
  · exact B2275463
  · exact B2275467
  · exact B2275471
  · exact B2275475
  · exact B2275479
  · exact B2275483
  · exact B2275487
  · exact B2275491
  · exact B2275495
  · exact B2275499
  · exact B2275503
  · exact B2275507
  · exact B2275511
  · exact B2275515
  · exact B2275519
  · exact B2275523
  · exact B2275527
  · exact B2275531
  · exact B2275535
  · exact B2275539
  · exact B2275543
  · exact B2275547
  · exact B2275551
  · exact B2275555
  · exact B2275559
  · exact B2275563
  · exact B2275567
  · exact B2275571
  · exact B2275575
  · exact B2275579
  · exact B2275583
  · exact B2275587
  · exact B2275591
  · exact B2275595
  · exact B2275599
  · exact B2275603
  · exact B2275607
  · exact B2275611
  · exact B2275615
  · exact B2275619
  · exact B2275623
  · exact B2275627
  · exact B2275631
  · exact B2275635
  · exact B2275639
  · exact B2275643
  · exact B2275647
  · exact B2275651
  · exact B2275655
  · exact B2275659
  · exact B2275663
  · exact B2275667
  · exact B2275671
  · exact B2275675
  · exact B2275679
  · exact B2275683
  · exact B2275687
  · exact B2275691
  · exact B2275695
  · exact B2275699
  · exact B2275703
  · exact B2275707
  · exact B2275711
  · exact B2275715
  · exact B2275719
  · exact B2275723
  · exact B2275727
  · exact B2275731
  · exact B2275735
  · exact B2275739
  · exact B2275743
  · exact B2275747
  · exact B2275751
  · exact B2275755
  · exact B2275759
  · exact B2275763
  · exact B2275767
  · exact B2275771
  · exact B2275775
  · exact B2275779
  · exact B2275783
  · exact B2275787
  · exact B2275791
  · exact B2275795
  · exact B2275799
  · exact B2275803
  · exact B2275807
  · exact B2275811
  · exact B2275815
  · exact B2275819
  · exact B2275823
  · exact B2275827
  · exact B2275831
  · exact B2275835
  · exact B2275839
  · exact B2275843
  · exact B2275847
  · exact B2275851
  · exact B2275855
  · exact B2275859
  · exact B2275863
  · exact B2275867
  · exact B2275871
  · exact B2275875
  · exact B2275879
  · exact B2275883
  · exact B2275887
  · exact B2275891
  · exact B2275895
  · exact B2275899
  · exact B2275903
  · exact B2275907
  · exact B2275911
  · exact B2275915
  · exact B2275919
  · exact B2275923
  · exact B2275927
  · exact B2275931
  · exact B2275935
  · exact B2275939
  · exact B2275943
  · exact B2275947
  · exact B2275951
  · exact B2275955
  · exact B2275959
  · exact B2275963
  · exact B2275967
  · exact B2275971
  · exact B2275975
  · exact B2275979
  · exact B2275983
  · exact B2275987
  · exact B2275991
  · exact B2275995
  · exact B2275999
  · exact B2276003
  · exact B2276007
  · exact B2276011
  · exact B2276015
  · exact B2276019
  · exact B2276023
  · exact B2276027
  · exact B2276031
  · exact B2276035
  · exact B2276039
  · exact B2276043
  · exact B2276047
  · exact B2276051
  · exact B2276055
  · exact B2276059
  · exact B2276063
  · exact B2276067
  · exact B2276071
  · exact B2276075
  · exact B2276079
  · exact B2276083
  · exact B2276087
  · exact B2276091
  · exact B2276095
  · exact B2276099
  · exact B2276103
  · exact B2276107
  · exact B2276111
  · exact B2276115
  · exact B2276119
  · exact B2276123
  · exact B2276127
  · exact B2276131
  · exact B2276135
  · exact B2276139
  · exact B2276143
  · exact B2276147
  · exact B2276151
  · exact B2276155
  · exact B2276159
  · exact B2276163
  · exact B2276167
  · exact B2276171
  · exact B2276175
  · exact B2276179
  · exact B2276183
  · exact B2276187
  · exact B2276191
  · exact B2276195
  · exact B2276199
  · exact B2276203
  · exact B2276207
  · exact B2276211
  · exact B2276215
  · exact B2276219
  · exact B2276223
  · exact B2276227
  · exact B2276231
  · exact B2276235
  · exact B2276239
  · exact B2276243
  · exact B2276247
  · exact B2276251
  · exact B2276255
  · exact B2276259
  · exact B2276263
  · exact B2276267
  · exact B2276271
  · exact B2276275
  · exact B2276279
  · exact B2276283
  · exact B2276287
  · exact B2276291
  · exact B2276295
  · exact B2276299
  · exact B2276303
  · exact B2276307
  · exact B2276311
  · exact B2276315
  · exact B2276319
  · exact B2276323
  · exact B2276327
  · exact B2276331
  · exact B2276335
  · exact B2276339
  · exact B2276343
  · exact B2276347
  · exact B2276351
  · exact B2276355
  · exact B2276359
  · exact B2276363
  · exact B2276367
  · exact B2276371
  · exact B2276375
  · exact B2276379
  · exact B2276383
  · exact B2276387
  · exact B2276391
  · exact B2276395
  · exact B2276399
  · exact B2276403
  · exact B2276407
  · exact B2276411
  · exact B2276415
  · exact B2276419
  · exact B2276423
  · exact B2276427
  · exact B2276431
  · exact B2276435
  · exact B2276439
  · exact B2276443
  · exact B2276447
  · exact B2276451
  · exact B2276455
  · exact B2276459
  · exact B2276463
  · exact B2276467
  · exact B2276471
  · exact B2276475
  · exact B2276479
  · exact B2276483
  · exact B2276487
  · exact B2276491
  · exact B2276495
  · exact B2276499
  · exact B2276503
  · exact B2276507
  · exact B2276511
  · exact B2276515
  · exact B2276519
  · exact B2276523
  · exact B2276527
  · exact B2276531
  · exact B2276535
  · exact B2276539
  · exact B2276543
  · exact B2276547
  · exact B2276551
  · exact B2276555
  · exact B2276559
  · exact B2276563
  · exact B2276567
  · exact B2276571
  · exact B2276575
  · exact B2276579
  · exact B2276583
  · exact B2276587
  · exact B2276591
  · exact B2276595
  · exact B2276599
  · exact B2276603
  · exact B2276607
  · exact B2276611
  · exact B2276615
  · exact B2276619
  · exact B2276623
  · exact B2276627
  · exact B2276631
  · exact B2276635
  · exact B2276639
  · exact B2276643
  · exact B2276647
  · exact B2276651
  · exact B2276655
  · exact B2276659
  · exact B2276663
  · exact B2276667
  · exact B2276671
  · exact B2276675
  · exact B2276679
  · exact B2276683
  · exact B2276687
  · exact B2276691
  · exact B2276695
  · exact B2276699
  · exact B2276703
  · exact B2276707
  · exact B2276711
  · exact B2276715
  · exact B2276719
  · exact B2276723
  · exact B2276727
  · exact B2276731
  · exact B2276735
  · exact B2276739
  · exact B2276743
  · exact B2276747
  · exact B2276751
  · exact B2276755
  · exact B2276759
  · exact B2276763
  · exact B2276767
  · exact B2276771
  · exact B2276775
  · exact B2276779
  · exact B2276783
  · exact B2276787
  · exact B2276791
  · exact B2276795
  · exact B2276799
  · exact B2276803
  · exact B2276807
  · exact B2276811
  · exact B2276815
  · exact B2276819
  · exact B2276823
  · exact B2276827
  · exact B2276831
  · exact B2276835
  · exact B2276839
  · exact B2276843
  · exact B2276847
  · exact B2276851
  · exact B2276855
  · exact B2276859
  · exact B2276863
  · exact B2276867
  · exact B2276871
  · exact B2276875
  · exact B2276879
  · exact B2276883
  · exact B2276887
  · exact B2276891
  · exact B2276895
  · exact B2276899
  · exact B2276903
  · exact B2276907
  · exact B2276911
  · exact B2276915
  · exact B2276919
  · exact B2276923
  · exact B2276927
  · exact B2276931
  · exact B2276935
  · exact B2276939
  · exact B2276943
  · exact B2276947
  · exact B2276951
  · exact B2276955
  · exact B2276959
  · exact B2276963
  · exact B2276967
  · exact B2276971
  · exact B2276975
  · exact B2276979
  · exact B2276983
  · exact B2276987
  · exact B2276991
  · exact B2276995
  · exact B2276999
  · exact B2277003
  · exact B2277007
  · exact B2277011
  · exact B2277015
  · exact B2277019
  · exact B2277023
  · exact B2277027
  · exact B2277031
  · exact B2277035
  · exact B2277039
  · exact B2277043
  · exact B2277047
  · exact B2277051
  · exact B2277055
  · exact B2277059
  · exact B2277063
  · exact B2277067
  · exact B2277071
  · exact B2277075
  · exact B2277079
  · exact B2277083
  · exact B2277087
  · exact B2277091
  · exact B2277095
  · exact B2277099
  · exact B2277103
  · exact B2277107
  · exact B2277111
  · exact B2277115
  · exact B2277119
  · exact B2277123
  · exact B2277127
  · exact B2277131
  · exact B2277135
  · exact B2277139
  · exact B2277143
  · exact B2277147
  · exact B2277151
  · exact B2277155
  · exact B2277159
  · exact B2277163
  · exact B2277167
  · exact B2277171
  · exact B2277175
  · exact B2277179
  · exact B2277183
  · exact B2277187
  · exact B2277191
  · exact B2277195
  · exact B2277199
  · exact B2277203
  · exact B2277207
  · exact B2277211
  · exact B2277215
  · exact B2277219
  · exact B2277223
  · exact B2277227
  · exact B2277231
  · exact B2277235
  · exact B2277239
  · exact B2277243
  · exact B2277247
  · exact B2277251
  · exact B2277255
  · exact B2277259
  · exact B2277263
  · exact B2277267
  · exact B2277271
  · exact B2277275
  · exact B2277279
  · exact B2277283
  · exact B2277287
  · exact B2277291
  · exact B2277295
  · exact B2277299
  · exact B2277303
  · exact B2277307
  · exact B2277311
  · exact B2277315
  · exact B2277319
  · exact B2277323
  · exact B2277327
  · exact B2277331
  · exact B2277335
  · exact B2277339
  · exact B2277343
  · exact B2277347
  · exact B2277351
  · exact B2277355
  · exact B2277359
  · exact B2277363
  · exact B2277367
  · exact B2277371
  · exact B2277375
  · exact B2277379
  · exact B2277383
  · exact B2277387
  · exact B2277391
  · exact B2277395
  · exact B2277399
  · exact B2277403
  · exact B2277407
  · exact B2277411
  · exact B2277415
  · exact B2277419
  · exact B2277423
  · exact B2277427
  · exact B2277431
  · exact B2277435
theorem solution (m : ℕ) (hlo : 2275435 ≤ m) (hhi : m ≤ 2277435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 568858 ≤ j := by omega
    have hj2 : j ≤ 569358 := by omega
    have hb : Blo 2275435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
