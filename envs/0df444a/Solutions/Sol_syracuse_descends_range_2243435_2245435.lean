-- Prove2me | solution 1 for syracuse_descends_range_2243435_2245435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:19:01.620368+00:00
-- url     : https://prove2.me/submissions/8e782442-1409-42ac-a90c-e20180f18c6e

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

theorem B2523865 : Blo 2243435 2523865 := bbase (se 2 (by rfl) ⟨946449, by rfl⟩ : syracuseStep 2523865 = 1892899) (by norm_num)
theorem B3365153 : Blo 2243435 3365153 := bstep (se 2 (by rfl) ⟨1261932, by rfl⟩ : syracuseStep 3365153 = 2523865) B2523865
theorem B2243435 : Blo 2243435 2243435 := bstep (se 1 (by rfl) ⟨1682576, by rfl⟩ : syracuseStep 2243435 = 3365153) B3365153
theorem B2395705 : Blo 2243435 2395705 := bbase (se 2 (by rfl) ⟨898389, by rfl⟩ : syracuseStep 2395705 = 1796779) (by norm_num)
theorem B3194273 : Blo 2243435 3194273 := bstep (se 2 (by rfl) ⟨1197852, by rfl⟩ : syracuseStep 3194273 = 2395705) B2395705
theorem B8518061 : Blo 2243435 8518061 := bstep (se 3 (by rfl) ⟨1597136, by rfl⟩ : syracuseStep 8518061 = 3194273) B3194273
theorem B5678707 : Blo 2243435 5678707 := bstep (se 1 (by rfl) ⟨4259030, by rfl⟩ : syracuseStep 5678707 = 8518061) B8518061
theorem B7571609 : Blo 2243435 7571609 := bstep (se 2 (by rfl) ⟨2839353, by rfl⟩ : syracuseStep 7571609 = 5678707) B5678707
theorem B5047739 : Blo 2243435 5047739 := bstep (se 1 (by rfl) ⟨3785804, by rfl⟩ : syracuseStep 5047739 = 7571609) B7571609
theorem B3365159 : Blo 2243435 3365159 := bstep (se 1 (by rfl) ⟨2523869, by rfl⟩ : syracuseStep 3365159 = 5047739) B5047739
theorem B2243439 : Blo 2243435 2243439 := bstep (se 1 (by rfl) ⟨1682579, by rfl⟩ : syracuseStep 2243439 = 3365159) B3365159
theorem B3365165 : Blo 2243435 3365165 := bbase (se 3 (by rfl) ⟨630968, by rfl⟩ : syracuseStep 3365165 = 1261937) (by norm_num)
theorem B2243443 : Blo 2243435 2243443 := bstep (se 1 (by rfl) ⟨1682582, by rfl⟩ : syracuseStep 2243443 = 3365165) B3365165
theorem B5047757 : Blo 2243435 5047757 := bbase (se 3 (by rfl) ⟨946454, by rfl⟩ : syracuseStep 5047757 = 1892909) (by norm_num)
theorem B3365171 : Blo 2243435 3365171 := bstep (se 1 (by rfl) ⟨2523878, by rfl⟩ : syracuseStep 3365171 = 5047757) B5047757
theorem B2243447 : Blo 2243435 2243447 := bstep (se 1 (by rfl) ⟨1682585, by rfl⟩ : syracuseStep 2243447 = 3365171) B3365171
theorem B2839369 : Blo 2243435 2839369 := bbase (se 2 (by rfl) ⟨1064763, by rfl⟩ : syracuseStep 2839369 = 2129527) (by norm_num)
theorem B3785825 : Blo 2243435 3785825 := bstep (se 2 (by rfl) ⟨1419684, by rfl⟩ : syracuseStep 3785825 = 2839369) B2839369
theorem B2523883 : Blo 2243435 2523883 := bstep (se 1 (by rfl) ⟨1892912, by rfl⟩ : syracuseStep 2523883 = 3785825) B3785825
theorem B3365177 : Blo 2243435 3365177 := bstep (se 2 (by rfl) ⟨1261941, by rfl⟩ : syracuseStep 3365177 = 2523883) B2523883
theorem B2243451 : Blo 2243435 2243451 := bstep (se 1 (by rfl) ⟨1682588, by rfl⟩ : syracuseStep 2243451 = 3365177) B3365177
theorem B5116645 : Blo 2243435 5116645 := bbase (se 4 (by rfl) ⟨479685, by rfl⟩ : syracuseStep 5116645 = 959371) (by norm_num)
theorem B6822193 : Blo 2243435 6822193 := bstep (se 2 (by rfl) ⟨2558322, by rfl⟩ : syracuseStep 6822193 = 5116645) B5116645
theorem B9096257 : Blo 2243435 9096257 := bstep (se 2 (by rfl) ⟨3411096, by rfl⟩ : syracuseStep 9096257 = 6822193) B6822193
theorem B24256685 : Blo 2243435 24256685 := bstep (se 3 (by rfl) ⟨4548128, by rfl⟩ : syracuseStep 24256685 = 9096257) B9096257
theorem B16171123 : Blo 2243435 16171123 := bstep (se 1 (by rfl) ⟨12128342, by rfl⟩ : syracuseStep 16171123 = 24256685) B24256685
theorem B21561497 : Blo 2243435 21561497 := bstep (se 2 (by rfl) ⟨8085561, by rfl⟩ : syracuseStep 21561497 = 16171123) B16171123
theorem B14374331 : Blo 2243435 14374331 := bstep (se 1 (by rfl) ⟨10780748, by rfl⟩ : syracuseStep 14374331 = 21561497) B21561497
theorem B9582887 : Blo 2243435 9582887 := bstep (se 1 (by rfl) ⟨7187165, by rfl⟩ : syracuseStep 9582887 = 14374331) B14374331
theorem B25554365 : Blo 2243435 25554365 := bstep (se 3 (by rfl) ⟨4791443, by rfl⟩ : syracuseStep 25554365 = 9582887) B9582887
theorem B17036243 : Blo 2243435 17036243 := bstep (se 1 (by rfl) ⟨12777182, by rfl⟩ : syracuseStep 17036243 = 25554365) B25554365
theorem B11357495 : Blo 2243435 11357495 := bstep (se 1 (by rfl) ⟨8518121, by rfl⟩ : syracuseStep 11357495 = 17036243) B17036243
theorem B7571663 : Blo 2243435 7571663 := bstep (se 1 (by rfl) ⟨5678747, by rfl⟩ : syracuseStep 7571663 = 11357495) B11357495
theorem B5047775 : Blo 2243435 5047775 := bstep (se 1 (by rfl) ⟨3785831, by rfl⟩ : syracuseStep 5047775 = 7571663) B7571663
theorem B3365183 : Blo 2243435 3365183 := bstep (se 1 (by rfl) ⟨2523887, by rfl⟩ : syracuseStep 3365183 = 5047775) B5047775
theorem B2243455 : Blo 2243435 2243455 := bstep (se 1 (by rfl) ⟨1682591, by rfl⟩ : syracuseStep 2243455 = 3365183) B3365183
theorem B3365189 : Blo 2243435 3365189 := bbase (se 4 (by rfl) ⟨315486, by rfl⟩ : syracuseStep 3365189 = 630973) (by norm_num)
theorem B2243459 : Blo 2243435 2243459 := bstep (se 1 (by rfl) ⟨1682594, by rfl⟩ : syracuseStep 2243459 = 3365189) B3365189
theorem B3785845 : Blo 2243435 3785845 := bbase (se 5 (by rfl) ⟨177461, by rfl⟩ : syracuseStep 3785845 = 354923) (by norm_num)
theorem B5047793 : Blo 2243435 5047793 := bstep (se 2 (by rfl) ⟨1892922, by rfl⟩ : syracuseStep 5047793 = 3785845) B3785845
theorem B3365195 : Blo 2243435 3365195 := bstep (se 1 (by rfl) ⟨2523896, by rfl⟩ : syracuseStep 3365195 = 5047793) B5047793
theorem B2243463 : Blo 2243435 2243463 := bstep (se 1 (by rfl) ⟨1682597, by rfl⟩ : syracuseStep 2243463 = 3365195) B3365195
theorem B2523901 : Blo 2243435 2523901 := bbase (se 3 (by rfl) ⟨473231, by rfl⟩ : syracuseStep 2523901 = 946463) (by norm_num)
theorem B3365201 : Blo 2243435 3365201 := bstep (se 2 (by rfl) ⟨1261950, by rfl⟩ : syracuseStep 3365201 = 2523901) B2523901
theorem B2243467 : Blo 2243435 2243467 := bstep (se 1 (by rfl) ⟨1682600, by rfl⟩ : syracuseStep 2243467 = 3365201) B3365201
theorem B7571717 : Blo 2243435 7571717 := bbase (se 4 (by rfl) ⟨709848, by rfl⟩ : syracuseStep 7571717 = 1419697) (by norm_num)
theorem B5047811 : Blo 2243435 5047811 := bstep (se 1 (by rfl) ⟨3785858, by rfl⟩ : syracuseStep 5047811 = 7571717) B7571717
theorem B3365207 : Blo 2243435 3365207 := bstep (se 1 (by rfl) ⟨2523905, by rfl⟩ : syracuseStep 3365207 = 5047811) B5047811
theorem B2243471 : Blo 2243435 2243471 := bstep (se 1 (by rfl) ⟨1682603, by rfl⟩ : syracuseStep 2243471 = 3365207) B3365207
theorem B3365213 : Blo 2243435 3365213 := bbase (se 3 (by rfl) ⟨630977, by rfl⟩ : syracuseStep 3365213 = 1261955) (by norm_num)
theorem B2243475 : Blo 2243435 2243475 := bstep (se 1 (by rfl) ⟨1682606, by rfl⟩ : syracuseStep 2243475 = 3365213) B3365213
theorem B5047829 : Blo 2243435 5047829 := bbase (se 6 (by rfl) ⟨118308, by rfl⟩ : syracuseStep 5047829 = 236617) (by norm_num)
theorem B3365219 : Blo 2243435 3365219 := bstep (se 1 (by rfl) ⟨2523914, by rfl⟩ : syracuseStep 3365219 = 5047829) B5047829
theorem B2243479 : Blo 2243435 2243479 := bstep (se 1 (by rfl) ⟨1682609, by rfl⟩ : syracuseStep 2243479 = 3365219) B3365219
theorem B8518229 : Blo 2243435 8518229 := bbase (se 8 (by rfl) ⟨49911, by rfl⟩ : syracuseStep 8518229 = 99823) (by norm_num)
theorem B5678819 : Blo 2243435 5678819 := bstep (se 1 (by rfl) ⟨4259114, by rfl⟩ : syracuseStep 5678819 = 8518229) B8518229
theorem B3785879 : Blo 2243435 3785879 := bstep (se 1 (by rfl) ⟨2839409, by rfl⟩ : syracuseStep 3785879 = 5678819) B5678819
theorem B2523919 : Blo 2243435 2523919 := bstep (se 1 (by rfl) ⟨1892939, by rfl⟩ : syracuseStep 2523919 = 3785879) B3785879
theorem B3365225 : Blo 2243435 3365225 := bstep (se 2 (by rfl) ⟨1261959, by rfl⟩ : syracuseStep 3365225 = 2523919) B2523919
theorem B2243483 : Blo 2243435 2243483 := bstep (se 1 (by rfl) ⟨1682612, by rfl⟩ : syracuseStep 2243483 = 3365225) B3365225
theorem B12777365 : Blo 2243435 12777365 := bbase (se 6 (by rfl) ⟨299469, by rfl⟩ : syracuseStep 12777365 = 598939) (by norm_num)
theorem B8518243 : Blo 2243435 8518243 := bstep (se 1 (by rfl) ⟨6388682, by rfl⟩ : syracuseStep 8518243 = 12777365) B12777365
theorem B11357657 : Blo 2243435 11357657 := bstep (se 2 (by rfl) ⟨4259121, by rfl⟩ : syracuseStep 11357657 = 8518243) B8518243
theorem B7571771 : Blo 2243435 7571771 := bstep (se 1 (by rfl) ⟨5678828, by rfl⟩ : syracuseStep 7571771 = 11357657) B11357657
theorem B5047847 : Blo 2243435 5047847 := bstep (se 1 (by rfl) ⟨3785885, by rfl⟩ : syracuseStep 5047847 = 7571771) B7571771
theorem B3365231 : Blo 2243435 3365231 := bstep (se 1 (by rfl) ⟨2523923, by rfl⟩ : syracuseStep 3365231 = 5047847) B5047847
theorem B2243487 : Blo 2243435 2243487 := bstep (se 1 (by rfl) ⟨1682615, by rfl⟩ : syracuseStep 2243487 = 3365231) B3365231
theorem B3365237 : Blo 2243435 3365237 := bbase (se 5 (by rfl) ⟨157745, by rfl⟩ : syracuseStep 3365237 = 315491) (by norm_num)
theorem B2243491 : Blo 2243435 2243491 := bstep (se 1 (by rfl) ⟨1682618, by rfl⟩ : syracuseStep 2243491 = 3365237) B3365237
theorem B2395765 : Blo 2243435 2395765 := bbase (se 5 (by rfl) ⟨112301, by rfl⟩ : syracuseStep 2395765 = 224603) (by norm_num)
theorem B3194353 : Blo 2243435 3194353 := bstep (se 2 (by rfl) ⟨1197882, by rfl⟩ : syracuseStep 3194353 = 2395765) B2395765
theorem B4259137 : Blo 2243435 4259137 := bstep (se 2 (by rfl) ⟨1597176, by rfl⟩ : syracuseStep 4259137 = 3194353) B3194353
theorem B5678849 : Blo 2243435 5678849 := bstep (se 2 (by rfl) ⟨2129568, by rfl⟩ : syracuseStep 5678849 = 4259137) B4259137
theorem B3785899 : Blo 2243435 3785899 := bstep (se 1 (by rfl) ⟨2839424, by rfl⟩ : syracuseStep 3785899 = 5678849) B5678849
theorem B5047865 : Blo 2243435 5047865 := bstep (se 2 (by rfl) ⟨1892949, by rfl⟩ : syracuseStep 5047865 = 3785899) B3785899
theorem B3365243 : Blo 2243435 3365243 := bstep (se 1 (by rfl) ⟨2523932, by rfl⟩ : syracuseStep 3365243 = 5047865) B5047865
theorem B2243495 : Blo 2243435 2243495 := bstep (se 1 (by rfl) ⟨1682621, by rfl⟩ : syracuseStep 2243495 = 3365243) B3365243
theorem B2523937 : Blo 2243435 2523937 := bbase (se 2 (by rfl) ⟨946476, by rfl⟩ : syracuseStep 2523937 = 1892953) (by norm_num)
theorem B3365249 : Blo 2243435 3365249 := bstep (se 2 (by rfl) ⟨1261968, by rfl⟩ : syracuseStep 3365249 = 2523937) B2523937
theorem B2243499 : Blo 2243435 2243499 := bstep (se 1 (by rfl) ⟨1682624, by rfl⟩ : syracuseStep 2243499 = 3365249) B3365249
theorem B5678869 : Blo 2243435 5678869 := bbase (se 6 (by rfl) ⟨133098, by rfl⟩ : syracuseStep 5678869 = 266197) (by norm_num)
theorem B7571825 : Blo 2243435 7571825 := bstep (se 2 (by rfl) ⟨2839434, by rfl⟩ : syracuseStep 7571825 = 5678869) B5678869
theorem B5047883 : Blo 2243435 5047883 := bstep (se 1 (by rfl) ⟨3785912, by rfl⟩ : syracuseStep 5047883 = 7571825) B7571825
theorem B3365255 : Blo 2243435 3365255 := bstep (se 1 (by rfl) ⟨2523941, by rfl⟩ : syracuseStep 3365255 = 5047883) B5047883
theorem B2243503 : Blo 2243435 2243503 := bstep (se 1 (by rfl) ⟨1682627, by rfl⟩ : syracuseStep 2243503 = 3365255) B3365255
theorem B3365261 : Blo 2243435 3365261 := bbase (se 3 (by rfl) ⟨630986, by rfl⟩ : syracuseStep 3365261 = 1261973) (by norm_num)
theorem B2243507 : Blo 2243435 2243507 := bstep (se 1 (by rfl) ⟨1682630, by rfl⟩ : syracuseStep 2243507 = 3365261) B3365261
theorem B5047901 : Blo 2243435 5047901 := bbase (se 3 (by rfl) ⟨946481, by rfl⟩ : syracuseStep 5047901 = 1892963) (by norm_num)
theorem B3365267 : Blo 2243435 3365267 := bstep (se 1 (by rfl) ⟨2523950, by rfl⟩ : syracuseStep 3365267 = 5047901) B5047901
theorem B2243511 : Blo 2243435 2243511 := bstep (se 1 (by rfl) ⟨1682633, by rfl⟩ : syracuseStep 2243511 = 3365267) B3365267
theorem B3785933 : Blo 2243435 3785933 := bbase (se 3 (by rfl) ⟨709862, by rfl⟩ : syracuseStep 3785933 = 1419725) (by norm_num)
theorem B2523955 : Blo 2243435 2523955 := bstep (se 1 (by rfl) ⟨1892966, by rfl⟩ : syracuseStep 2523955 = 3785933) B3785933
theorem B3365273 : Blo 2243435 3365273 := bstep (se 2 (by rfl) ⟨1261977, by rfl⟩ : syracuseStep 3365273 = 2523955) B2523955
theorem B2243515 : Blo 2243435 2243515 := bstep (se 1 (by rfl) ⟨1682636, by rfl⟩ : syracuseStep 2243515 = 3365273) B3365273
theorem B14374741 : Blo 2243435 14374741 := bbase (se 9 (by rfl) ⟨42113, by rfl⟩ : syracuseStep 14374741 = 84227) (by norm_num)
theorem B19166321 : Blo 2243435 19166321 := bstep (se 2 (by rfl) ⟨7187370, by rfl⟩ : syracuseStep 19166321 = 14374741) B14374741
theorem B12777547 : Blo 2243435 12777547 := bstep (se 1 (by rfl) ⟨9583160, by rfl⟩ : syracuseStep 12777547 = 19166321) B19166321
theorem B17036729 : Blo 2243435 17036729 := bstep (se 2 (by rfl) ⟨6388773, by rfl⟩ : syracuseStep 17036729 = 12777547) B12777547
theorem B11357819 : Blo 2243435 11357819 := bstep (se 1 (by rfl) ⟨8518364, by rfl⟩ : syracuseStep 11357819 = 17036729) B17036729
theorem B7571879 : Blo 2243435 7571879 := bstep (se 1 (by rfl) ⟨5678909, by rfl⟩ : syracuseStep 7571879 = 11357819) B11357819
theorem B5047919 : Blo 2243435 5047919 := bstep (se 1 (by rfl) ⟨3785939, by rfl⟩ : syracuseStep 5047919 = 7571879) B7571879
theorem B3365279 : Blo 2243435 3365279 := bstep (se 1 (by rfl) ⟨2523959, by rfl⟩ : syracuseStep 3365279 = 5047919) B5047919
theorem B2243519 : Blo 2243435 2243519 := bstep (se 1 (by rfl) ⟨1682639, by rfl⟩ : syracuseStep 2243519 = 3365279) B3365279
theorem B3365285 : Blo 2243435 3365285 := bbase (se 4 (by rfl) ⟨315495, by rfl⟩ : syracuseStep 3365285 = 630991) (by norm_num)
theorem B2243523 : Blo 2243435 2243523 := bstep (se 1 (by rfl) ⟨1682642, by rfl⟩ : syracuseStep 2243523 = 3365285) B3365285
theorem B2839465 : Blo 2243435 2839465 := bbase (se 2 (by rfl) ⟨1064799, by rfl⟩ : syracuseStep 2839465 = 2129599) (by norm_num)
theorem B3785953 : Blo 2243435 3785953 := bstep (se 2 (by rfl) ⟨1419732, by rfl⟩ : syracuseStep 3785953 = 2839465) B2839465
theorem B5047937 : Blo 2243435 5047937 := bstep (se 2 (by rfl) ⟨1892976, by rfl⟩ : syracuseStep 5047937 = 3785953) B3785953
theorem B3365291 : Blo 2243435 3365291 := bstep (se 1 (by rfl) ⟨2523968, by rfl⟩ : syracuseStep 3365291 = 5047937) B5047937
theorem B2243527 : Blo 2243435 2243527 := bstep (se 1 (by rfl) ⟨1682645, by rfl⟩ : syracuseStep 2243527 = 3365291) B3365291
theorem B2523973 : Blo 2243435 2523973 := bbase (se 4 (by rfl) ⟨236622, by rfl⟩ : syracuseStep 2523973 = 473245) (by norm_num)
theorem B3365297 : Blo 2243435 3365297 := bstep (se 2 (by rfl) ⟨1261986, by rfl⟩ : syracuseStep 3365297 = 2523973) B2523973
theorem B2243531 : Blo 2243435 2243531 := bstep (se 1 (by rfl) ⟨1682648, by rfl⟩ : syracuseStep 2243531 = 3365297) B3365297
theorem B4259213 : Blo 2243435 4259213 := bbase (se 3 (by rfl) ⟨798602, by rfl⟩ : syracuseStep 4259213 = 1597205) (by norm_num)
theorem B2839475 : Blo 2243435 2839475 := bstep (se 1 (by rfl) ⟨2129606, by rfl⟩ : syracuseStep 2839475 = 4259213) B4259213
theorem B7571933 : Blo 2243435 7571933 := bstep (se 3 (by rfl) ⟨1419737, by rfl⟩ : syracuseStep 7571933 = 2839475) B2839475
theorem B5047955 : Blo 2243435 5047955 := bstep (se 1 (by rfl) ⟨3785966, by rfl⟩ : syracuseStep 5047955 = 7571933) B7571933
theorem B3365303 : Blo 2243435 3365303 := bstep (se 1 (by rfl) ⟨2523977, by rfl⟩ : syracuseStep 3365303 = 5047955) B5047955
theorem B2243535 : Blo 2243435 2243535 := bstep (se 1 (by rfl) ⟨1682651, by rfl⟩ : syracuseStep 2243535 = 3365303) B3365303
theorem B3365309 : Blo 2243435 3365309 := bbase (se 3 (by rfl) ⟨630995, by rfl⟩ : syracuseStep 3365309 = 1261991) (by norm_num)
theorem B2243539 : Blo 2243435 2243539 := bstep (se 1 (by rfl) ⟨1682654, by rfl⟩ : syracuseStep 2243539 = 3365309) B3365309
theorem B5047973 : Blo 2243435 5047973 := bbase (se 4 (by rfl) ⟨473247, by rfl⟩ : syracuseStep 5047973 = 946495) (by norm_num)
theorem B3365315 : Blo 2243435 3365315 := bstep (se 1 (by rfl) ⟨2523986, by rfl⟩ : syracuseStep 3365315 = 5047973) B5047973
theorem B2243543 : Blo 2243435 2243543 := bstep (se 1 (by rfl) ⟨1682657, by rfl⟩ : syracuseStep 2243543 = 3365315) B3365315
theorem B5678981 : Blo 2243435 5678981 := bbase (se 4 (by rfl) ⟨532404, by rfl⟩ : syracuseStep 5678981 = 1064809) (by norm_num)
theorem B3785987 : Blo 2243435 3785987 := bstep (se 1 (by rfl) ⟨2839490, by rfl⟩ : syracuseStep 3785987 = 5678981) B5678981
theorem B2523991 : Blo 2243435 2523991 := bstep (se 1 (by rfl) ⟨1892993, by rfl⟩ : syracuseStep 2523991 = 3785987) B3785987
theorem B3365321 : Blo 2243435 3365321 := bstep (se 2 (by rfl) ⟨1261995, by rfl⟩ : syracuseStep 3365321 = 2523991) B2523991
theorem B2243547 : Blo 2243435 2243547 := bstep (se 1 (by rfl) ⟨1682660, by rfl⟩ : syracuseStep 2243547 = 3365321) B3365321
theorem B4548325 : Blo 2243435 4548325 := bbase (se 4 (by rfl) ⟨426405, by rfl⟩ : syracuseStep 4548325 = 852811) (by norm_num)
theorem B6064433 : Blo 2243435 6064433 := bstep (se 2 (by rfl) ⟨2274162, by rfl⟩ : syracuseStep 6064433 = 4548325) B4548325
theorem B4042955 : Blo 2243435 4042955 := bstep (se 1 (by rfl) ⟨3032216, by rfl⟩ : syracuseStep 4042955 = 6064433) B6064433
theorem B2695303 : Blo 2243435 2695303 := bstep (se 1 (by rfl) ⟨2021477, by rfl⟩ : syracuseStep 2695303 = 4042955) B4042955
theorem B3593737 : Blo 2243435 3593737 := bstep (se 2 (by rfl) ⟨1347651, by rfl⟩ : syracuseStep 3593737 = 2695303) B2695303
theorem B4791649 : Blo 2243435 4791649 := bstep (se 2 (by rfl) ⟨1796868, by rfl⟩ : syracuseStep 4791649 = 3593737) B3593737
theorem B6388865 : Blo 2243435 6388865 := bstep (se 2 (by rfl) ⟨2395824, by rfl⟩ : syracuseStep 6388865 = 4791649) B4791649
theorem B4259243 : Blo 2243435 4259243 := bstep (se 1 (by rfl) ⟨3194432, by rfl⟩ : syracuseStep 4259243 = 6388865) B6388865
theorem B11357981 : Blo 2243435 11357981 := bstep (se 3 (by rfl) ⟨2129621, by rfl⟩ : syracuseStep 11357981 = 4259243) B4259243
theorem B7571987 : Blo 2243435 7571987 := bstep (se 1 (by rfl) ⟨5678990, by rfl⟩ : syracuseStep 7571987 = 11357981) B11357981
theorem B5047991 : Blo 2243435 5047991 := bstep (se 1 (by rfl) ⟨3785993, by rfl⟩ : syracuseStep 5047991 = 7571987) B7571987
theorem B3365327 : Blo 2243435 3365327 := bstep (se 1 (by rfl) ⟨2523995, by rfl⟩ : syracuseStep 3365327 = 5047991) B5047991
theorem B2243551 : Blo 2243435 2243551 := bstep (se 1 (by rfl) ⟨1682663, by rfl⟩ : syracuseStep 2243551 = 3365327) B3365327
theorem B3365333 : Blo 2243435 3365333 := bbase (se 7 (by rfl) ⟨39437, by rfl⟩ : syracuseStep 3365333 = 78875) (by norm_num)
theorem B2243555 : Blo 2243435 2243555 := bstep (se 1 (by rfl) ⟨1682666, by rfl⟩ : syracuseStep 2243555 = 3365333) B3365333
theorem B8518517 : Blo 2243435 8518517 := bbase (se 5 (by rfl) ⟨399305, by rfl⟩ : syracuseStep 8518517 = 798611) (by norm_num)
theorem B5679011 : Blo 2243435 5679011 := bstep (se 1 (by rfl) ⟨4259258, by rfl⟩ : syracuseStep 5679011 = 8518517) B8518517
theorem B3786007 : Blo 2243435 3786007 := bstep (se 1 (by rfl) ⟨2839505, by rfl⟩ : syracuseStep 3786007 = 5679011) B5679011
theorem B5048009 : Blo 2243435 5048009 := bstep (se 2 (by rfl) ⟨1893003, by rfl⟩ : syracuseStep 5048009 = 3786007) B3786007
theorem B3365339 : Blo 2243435 3365339 := bstep (se 1 (by rfl) ⟨2524004, by rfl⟩ : syracuseStep 3365339 = 5048009) B5048009
theorem B2243559 : Blo 2243435 2243559 := bstep (se 1 (by rfl) ⟨1682669, by rfl⟩ : syracuseStep 2243559 = 3365339) B3365339
theorem B2524009 : Blo 2243435 2524009 := bbase (se 2 (by rfl) ⟨946503, by rfl⟩ : syracuseStep 2524009 = 1893007) (by norm_num)
theorem B3365345 : Blo 2243435 3365345 := bstep (se 2 (by rfl) ⟨1262004, by rfl⟩ : syracuseStep 3365345 = 2524009) B2524009
theorem B2243563 : Blo 2243435 2243563 := bstep (se 1 (by rfl) ⟨1682672, by rfl⟩ : syracuseStep 2243563 = 3365345) B3365345
theorem B7187525 : Blo 2243435 7187525 := bbase (se 4 (by rfl) ⟨673830, by rfl⟩ : syracuseStep 7187525 = 1347661) (by norm_num)
theorem B4791683 : Blo 2243435 4791683 := bstep (se 1 (by rfl) ⟨3593762, by rfl⟩ : syracuseStep 4791683 = 7187525) B7187525
theorem B12777821 : Blo 2243435 12777821 := bstep (se 3 (by rfl) ⟨2395841, by rfl⟩ : syracuseStep 12777821 = 4791683) B4791683
theorem B8518547 : Blo 2243435 8518547 := bstep (se 1 (by rfl) ⟨6388910, by rfl⟩ : syracuseStep 8518547 = 12777821) B12777821
theorem B5679031 : Blo 2243435 5679031 := bstep (se 1 (by rfl) ⟨4259273, by rfl⟩ : syracuseStep 5679031 = 8518547) B8518547
theorem B7572041 : Blo 2243435 7572041 := bstep (se 2 (by rfl) ⟨2839515, by rfl⟩ : syracuseStep 7572041 = 5679031) B5679031
theorem B5048027 : Blo 2243435 5048027 := bstep (se 1 (by rfl) ⟨3786020, by rfl⟩ : syracuseStep 5048027 = 7572041) B7572041
theorem B3365351 : Blo 2243435 3365351 := bstep (se 1 (by rfl) ⟨2524013, by rfl⟩ : syracuseStep 3365351 = 5048027) B5048027
theorem B2243567 : Blo 2243435 2243567 := bstep (se 1 (by rfl) ⟨1682675, by rfl⟩ : syracuseStep 2243567 = 3365351) B3365351
theorem B3365357 : Blo 2243435 3365357 := bbase (se 3 (by rfl) ⟨631004, by rfl⟩ : syracuseStep 3365357 = 1262009) (by norm_num)
theorem B2243571 : Blo 2243435 2243571 := bstep (se 1 (by rfl) ⟨1682678, by rfl⟩ : syracuseStep 2243571 = 3365357) B3365357
theorem B5048045 : Blo 2243435 5048045 := bbase (se 3 (by rfl) ⟨946508, by rfl⟩ : syracuseStep 5048045 = 1893017) (by norm_num)
theorem B3365363 : Blo 2243435 3365363 := bstep (se 1 (by rfl) ⟨2524022, by rfl⟩ : syracuseStep 3365363 = 5048045) B5048045
theorem B2243575 : Blo 2243435 2243575 := bstep (se 1 (by rfl) ⟨1682681, by rfl⟩ : syracuseStep 2243575 = 3365363) B3365363
theorem B6476117 : Blo 2243435 6476117 := bbase (se 10 (by rfl) ⟨9486, by rfl⟩ : syracuseStep 6476117 = 18973) (by norm_num)
theorem B17269645 : Blo 2243435 17269645 := bstep (se 3 (by rfl) ⟨3238058, by rfl⟩ : syracuseStep 17269645 = 6476117) B6476117
theorem B23026193 : Blo 2243435 23026193 := bstep (se 2 (by rfl) ⟨8634822, by rfl⟩ : syracuseStep 23026193 = 17269645) B17269645
theorem B15350795 : Blo 2243435 15350795 := bstep (se 1 (by rfl) ⟨11513096, by rfl⟩ : syracuseStep 15350795 = 23026193) B23026193
theorem B10233863 : Blo 2243435 10233863 := bstep (se 1 (by rfl) ⟨7675397, by rfl⟩ : syracuseStep 10233863 = 15350795) B15350795
theorem B6822575 : Blo 2243435 6822575 := bstep (se 1 (by rfl) ⟨5116931, by rfl⟩ : syracuseStep 6822575 = 10233863) B10233863
theorem B4548383 : Blo 2243435 4548383 := bstep (se 1 (by rfl) ⟨3411287, by rfl⟩ : syracuseStep 4548383 = 6822575) B6822575
theorem B3032255 : Blo 2243435 3032255 := bstep (se 1 (by rfl) ⟨2274191, by rfl⟩ : syracuseStep 3032255 = 4548383) B4548383
theorem B8086013 : Blo 2243435 8086013 := bstep (se 3 (by rfl) ⟨1516127, by rfl⟩ : syracuseStep 8086013 = 3032255) B3032255
theorem B5390675 : Blo 2243435 5390675 := bstep (se 1 (by rfl) ⟨4043006, by rfl⟩ : syracuseStep 5390675 = 8086013) B8086013
theorem B3593783 : Blo 2243435 3593783 := bstep (se 1 (by rfl) ⟨2695337, by rfl⟩ : syracuseStep 3593783 = 5390675) B5390675
theorem B2395855 : Blo 2243435 2395855 := bstep (se 1 (by rfl) ⟨1796891, by rfl⟩ : syracuseStep 2395855 = 3593783) B3593783
theorem B3194473 : Blo 2243435 3194473 := bstep (se 2 (by rfl) ⟨1197927, by rfl⟩ : syracuseStep 3194473 = 2395855) B2395855
theorem B4259297 : Blo 2243435 4259297 := bstep (se 2 (by rfl) ⟨1597236, by rfl⟩ : syracuseStep 4259297 = 3194473) B3194473
theorem B2839531 : Blo 2243435 2839531 := bstep (se 1 (by rfl) ⟨2129648, by rfl⟩ : syracuseStep 2839531 = 4259297) B4259297
theorem B3786041 : Blo 2243435 3786041 := bstep (se 2 (by rfl) ⟨1419765, by rfl⟩ : syracuseStep 3786041 = 2839531) B2839531
theorem B2524027 : Blo 2243435 2524027 := bstep (se 1 (by rfl) ⟨1893020, by rfl⟩ : syracuseStep 2524027 = 3786041) B3786041
theorem B3365369 : Blo 2243435 3365369 := bstep (se 2 (by rfl) ⟨1262013, by rfl⟩ : syracuseStep 3365369 = 2524027) B2524027
theorem B2243579 : Blo 2243435 2243579 := bstep (se 1 (by rfl) ⟨1682684, by rfl⟩ : syracuseStep 2243579 = 3365369) B3365369
theorem B12294517 : Blo 2243435 12294517 := bbase (se 5 (by rfl) ⟨576305, by rfl⟩ : syracuseStep 12294517 = 1152611) (by norm_num)
theorem B16392689 : Blo 2243435 16392689 := bstep (se 2 (by rfl) ⟨6147258, by rfl⟩ : syracuseStep 16392689 = 12294517) B12294517
theorem B10928459 : Blo 2243435 10928459 := bstep (se 1 (by rfl) ⟨8196344, by rfl⟩ : syracuseStep 10928459 = 16392689) B16392689
theorem B7285639 : Blo 2243435 7285639 := bstep (se 1 (by rfl) ⟨5464229, by rfl⟩ : syracuseStep 7285639 = 10928459) B10928459
theorem B9714185 : Blo 2243435 9714185 := bstep (se 2 (by rfl) ⟨3642819, by rfl⟩ : syracuseStep 9714185 = 7285639) B7285639
theorem B6476123 : Blo 2243435 6476123 := bstep (se 1 (by rfl) ⟨4857092, by rfl⟩ : syracuseStep 6476123 = 9714185) B9714185
theorem B17269661 : Blo 2243435 17269661 := bstep (se 3 (by rfl) ⟨3238061, by rfl⟩ : syracuseStep 17269661 = 6476123) B6476123
theorem B11513107 : Blo 2243435 11513107 := bstep (se 1 (by rfl) ⟨8634830, by rfl⟩ : syracuseStep 11513107 = 17269661) B17269661
theorem B15350809 : Blo 2243435 15350809 := bstep (se 2 (by rfl) ⟨5756553, by rfl⟩ : syracuseStep 15350809 = 11513107) B11513107
theorem B20467745 : Blo 2243435 20467745 := bstep (se 2 (by rfl) ⟨7675404, by rfl⟩ : syracuseStep 20467745 = 15350809) B15350809
theorem B13645163 : Blo 2243435 13645163 := bstep (se 1 (by rfl) ⟨10233872, by rfl⟩ : syracuseStep 13645163 = 20467745) B20467745
theorem B36387101 : Blo 2243435 36387101 := bstep (se 3 (by rfl) ⟨6822581, by rfl⟩ : syracuseStep 36387101 = 13645163) B13645163
theorem B97032269 : Blo 2243435 97032269 := bstep (se 3 (by rfl) ⟨18193550, by rfl⟩ : syracuseStep 97032269 = 36387101) B36387101
theorem B64688179 : Blo 2243435 64688179 := bstep (se 1 (by rfl) ⟨48516134, by rfl⟩ : syracuseStep 64688179 = 97032269) B97032269
theorem B86250905 : Blo 2243435 86250905 := bstep (se 2 (by rfl) ⟨32344089, by rfl⟩ : syracuseStep 86250905 = 64688179) B64688179
theorem B57500603 : Blo 2243435 57500603 := bstep (se 1 (by rfl) ⟨43125452, by rfl⟩ : syracuseStep 57500603 = 86250905) B86250905
theorem B38333735 : Blo 2243435 38333735 := bstep (se 1 (by rfl) ⟨28750301, by rfl⟩ : syracuseStep 38333735 = 57500603) B57500603
theorem B25555823 : Blo 2243435 25555823 := bstep (se 1 (by rfl) ⟨19166867, by rfl⟩ : syracuseStep 25555823 = 38333735) B38333735
theorem B17037215 : Blo 2243435 17037215 := bstep (se 1 (by rfl) ⟨12777911, by rfl⟩ : syracuseStep 17037215 = 25555823) B25555823
theorem B11358143 : Blo 2243435 11358143 := bstep (se 1 (by rfl) ⟨8518607, by rfl⟩ : syracuseStep 11358143 = 17037215) B17037215
theorem B7572095 : Blo 2243435 7572095 := bstep (se 1 (by rfl) ⟨5679071, by rfl⟩ : syracuseStep 7572095 = 11358143) B11358143
theorem B5048063 : Blo 2243435 5048063 := bstep (se 1 (by rfl) ⟨3786047, by rfl⟩ : syracuseStep 5048063 = 7572095) B7572095
theorem B3365375 : Blo 2243435 3365375 := bstep (se 1 (by rfl) ⟨2524031, by rfl⟩ : syracuseStep 3365375 = 5048063) B5048063
theorem B2243583 : Blo 2243435 2243583 := bstep (se 1 (by rfl) ⟨1682687, by rfl⟩ : syracuseStep 2243583 = 3365375) B3365375
theorem B3365381 : Blo 2243435 3365381 := bbase (se 4 (by rfl) ⟨315504, by rfl⟩ : syracuseStep 3365381 = 631009) (by norm_num)
theorem B2243587 : Blo 2243435 2243587 := bstep (se 1 (by rfl) ⟨1682690, by rfl⟩ : syracuseStep 2243587 = 3365381) B3365381
theorem B3786061 : Blo 2243435 3786061 := bbase (se 3 (by rfl) ⟨709886, by rfl⟩ : syracuseStep 3786061 = 1419773) (by norm_num)
theorem B5048081 : Blo 2243435 5048081 := bstep (se 2 (by rfl) ⟨1893030, by rfl⟩ : syracuseStep 5048081 = 3786061) B3786061
theorem B3365387 : Blo 2243435 3365387 := bstep (se 1 (by rfl) ⟨2524040, by rfl⟩ : syracuseStep 3365387 = 5048081) B5048081
theorem B2243591 : Blo 2243435 2243591 := bstep (se 1 (by rfl) ⟨1682693, by rfl⟩ : syracuseStep 2243591 = 3365387) B3365387
theorem B2524045 : Blo 2243435 2524045 := bbase (se 3 (by rfl) ⟨473258, by rfl⟩ : syracuseStep 2524045 = 946517) (by norm_num)
theorem B3365393 : Blo 2243435 3365393 := bstep (se 2 (by rfl) ⟨1262022, by rfl⟩ : syracuseStep 3365393 = 2524045) B2524045
theorem B2243595 : Blo 2243435 2243595 := bstep (se 1 (by rfl) ⟨1682696, by rfl⟩ : syracuseStep 2243595 = 3365393) B3365393
theorem B7572149 : Blo 2243435 7572149 := bbase (se 5 (by rfl) ⟨354944, by rfl⟩ : syracuseStep 7572149 = 709889) (by norm_num)
theorem B5048099 : Blo 2243435 5048099 := bstep (se 1 (by rfl) ⟨3786074, by rfl⟩ : syracuseStep 5048099 = 7572149) B7572149
theorem B3365399 : Blo 2243435 3365399 := bstep (se 1 (by rfl) ⟨2524049, by rfl⟩ : syracuseStep 3365399 = 5048099) B5048099
theorem B2243599 : Blo 2243435 2243599 := bstep (se 1 (by rfl) ⟨1682699, by rfl⟩ : syracuseStep 2243599 = 3365399) B3365399
theorem B3365405 : Blo 2243435 3365405 := bbase (se 3 (by rfl) ⟨631013, by rfl⟩ : syracuseStep 3365405 = 1262027) (by norm_num)
theorem B2243603 : Blo 2243435 2243603 := bstep (se 1 (by rfl) ⟨1682702, by rfl⟩ : syracuseStep 2243603 = 3365405) B3365405
theorem B5048117 : Blo 2243435 5048117 := bbase (se 5 (by rfl) ⟨236630, by rfl⟩ : syracuseStep 5048117 = 473261) (by norm_num)
theorem B3365411 : Blo 2243435 3365411 := bstep (se 1 (by rfl) ⟨2524058, by rfl⟩ : syracuseStep 3365411 = 5048117) B5048117
theorem B2243607 : Blo 2243435 2243607 := bstep (se 1 (by rfl) ⟨1682705, by rfl⟩ : syracuseStep 2243607 = 3365411) B3365411
theorem B5756629 : Blo 2243435 5756629 := bbase (se 7 (by rfl) ⟨67460, by rfl⟩ : syracuseStep 5756629 = 134921) (by norm_num)
theorem B7675505 : Blo 2243435 7675505 := bstep (se 2 (by rfl) ⟨2878314, by rfl⟩ : syracuseStep 7675505 = 5756629) B5756629
theorem B5117003 : Blo 2243435 5117003 := bstep (se 1 (by rfl) ⟨3837752, by rfl⟩ : syracuseStep 5117003 = 7675505) B7675505
theorem B3411335 : Blo 2243435 3411335 := bstep (se 1 (by rfl) ⟨2558501, by rfl⟩ : syracuseStep 3411335 = 5117003) B5117003
theorem B9096893 : Blo 2243435 9096893 := bstep (se 3 (by rfl) ⟨1705667, by rfl⟩ : syracuseStep 9096893 = 3411335) B3411335
theorem B6064595 : Blo 2243435 6064595 := bstep (se 1 (by rfl) ⟨4548446, by rfl⟩ : syracuseStep 6064595 = 9096893) B9096893
theorem B4043063 : Blo 2243435 4043063 := bstep (se 1 (by rfl) ⟨3032297, by rfl⟩ : syracuseStep 4043063 = 6064595) B6064595
theorem B2695375 : Blo 2243435 2695375 := bstep (se 1 (by rfl) ⟨2021531, by rfl⟩ : syracuseStep 2695375 = 4043063) B4043063
theorem B14375333 : Blo 2243435 14375333 := bstep (se 4 (by rfl) ⟨1347687, by rfl⟩ : syracuseStep 14375333 = 2695375) B2695375
theorem B9583555 : Blo 2243435 9583555 := bstep (se 1 (by rfl) ⟨7187666, by rfl⟩ : syracuseStep 9583555 = 14375333) B14375333
theorem B12778073 : Blo 2243435 12778073 := bstep (se 2 (by rfl) ⟨4791777, by rfl⟩ : syracuseStep 12778073 = 9583555) B9583555
theorem B8518715 : Blo 2243435 8518715 := bstep (se 1 (by rfl) ⟨6389036, by rfl⟩ : syracuseStep 8518715 = 12778073) B12778073
theorem B5679143 : Blo 2243435 5679143 := bstep (se 1 (by rfl) ⟨4259357, by rfl⟩ : syracuseStep 5679143 = 8518715) B8518715
theorem B3786095 : Blo 2243435 3786095 := bstep (se 1 (by rfl) ⟨2839571, by rfl⟩ : syracuseStep 3786095 = 5679143) B5679143
theorem B2524063 : Blo 2243435 2524063 := bstep (se 1 (by rfl) ⟨1893047, by rfl⟩ : syracuseStep 2524063 = 3786095) B3786095
theorem B3365417 : Blo 2243435 3365417 := bstep (se 2 (by rfl) ⟨1262031, by rfl⟩ : syracuseStep 3365417 = 2524063) B2524063
theorem B2243611 : Blo 2243435 2243611 := bstep (se 1 (by rfl) ⟨1682708, by rfl⟩ : syracuseStep 2243611 = 3365417) B3365417
theorem B10234021 : Blo 2243435 10234021 := bbase (se 4 (by rfl) ⟨959439, by rfl⟩ : syracuseStep 10234021 = 1918879) (by norm_num)
theorem B13645361 : Blo 2243435 13645361 := bstep (se 2 (by rfl) ⟨5117010, by rfl⟩ : syracuseStep 13645361 = 10234021) B10234021
theorem B9096907 : Blo 2243435 9096907 := bstep (se 1 (by rfl) ⟨6822680, by rfl⟩ : syracuseStep 9096907 = 13645361) B13645361
theorem B12129209 : Blo 2243435 12129209 := bstep (se 2 (by rfl) ⟨4548453, by rfl⟩ : syracuseStep 12129209 = 9096907) B9096907
theorem B8086139 : Blo 2243435 8086139 := bstep (se 1 (by rfl) ⟨6064604, by rfl⟩ : syracuseStep 8086139 = 12129209) B12129209
theorem B5390759 : Blo 2243435 5390759 := bstep (se 1 (by rfl) ⟨4043069, by rfl⟩ : syracuseStep 5390759 = 8086139) B8086139
theorem B14375357 : Blo 2243435 14375357 := bstep (se 3 (by rfl) ⟨2695379, by rfl⟩ : syracuseStep 14375357 = 5390759) B5390759
theorem B9583571 : Blo 2243435 9583571 := bstep (se 1 (by rfl) ⟨7187678, by rfl⟩ : syracuseStep 9583571 = 14375357) B14375357
theorem B6389047 : Blo 2243435 6389047 := bstep (se 1 (by rfl) ⟨4791785, by rfl⟩ : syracuseStep 6389047 = 9583571) B9583571
theorem B8518729 : Blo 2243435 8518729 := bstep (se 2 (by rfl) ⟨3194523, by rfl⟩ : syracuseStep 8518729 = 6389047) B6389047
theorem B11358305 : Blo 2243435 11358305 := bstep (se 2 (by rfl) ⟨4259364, by rfl⟩ : syracuseStep 11358305 = 8518729) B8518729
theorem B7572203 : Blo 2243435 7572203 := bstep (se 1 (by rfl) ⟨5679152, by rfl⟩ : syracuseStep 7572203 = 11358305) B11358305
theorem B5048135 : Blo 2243435 5048135 := bstep (se 1 (by rfl) ⟨3786101, by rfl⟩ : syracuseStep 5048135 = 7572203) B7572203
theorem B3365423 : Blo 2243435 3365423 := bstep (se 1 (by rfl) ⟨2524067, by rfl⟩ : syracuseStep 3365423 = 5048135) B5048135
theorem B2243615 : Blo 2243435 2243615 := bstep (se 1 (by rfl) ⟨1682711, by rfl⟩ : syracuseStep 2243615 = 3365423) B3365423
theorem B3365429 : Blo 2243435 3365429 := bbase (se 5 (by rfl) ⟨157754, by rfl⟩ : syracuseStep 3365429 = 315509) (by norm_num)
theorem B2243619 : Blo 2243435 2243619 := bstep (se 1 (by rfl) ⟨1682714, by rfl⟩ : syracuseStep 2243619 = 3365429) B3365429
theorem B5679173 : Blo 2243435 5679173 := bbase (se 4 (by rfl) ⟨532422, by rfl⟩ : syracuseStep 5679173 = 1064845) (by norm_num)
theorem B3786115 : Blo 2243435 3786115 := bstep (se 1 (by rfl) ⟨2839586, by rfl⟩ : syracuseStep 3786115 = 5679173) B5679173
theorem B5048153 : Blo 2243435 5048153 := bstep (se 2 (by rfl) ⟨1893057, by rfl⟩ : syracuseStep 5048153 = 3786115) B3786115
theorem B3365435 : Blo 2243435 3365435 := bstep (se 1 (by rfl) ⟨2524076, by rfl⟩ : syracuseStep 3365435 = 5048153) B5048153
theorem B2243623 : Blo 2243435 2243623 := bstep (se 1 (by rfl) ⟨1682717, by rfl⟩ : syracuseStep 2243623 = 3365435) B3365435
theorem B2524081 : Blo 2243435 2524081 := bbase (se 2 (by rfl) ⟨946530, by rfl⟩ : syracuseStep 2524081 = 1893061) (by norm_num)
theorem B3365441 : Blo 2243435 3365441 := bstep (se 2 (by rfl) ⟨1262040, by rfl⟩ : syracuseStep 3365441 = 2524081) B2524081
theorem B2243627 : Blo 2243435 2243627 := bstep (se 1 (by rfl) ⟨1682720, by rfl⟩ : syracuseStep 2243627 = 3365441) B3365441
theorem B6389093 : Blo 2243435 6389093 := bbase (se 4 (by rfl) ⟨598977, by rfl⟩ : syracuseStep 6389093 = 1197955) (by norm_num)
theorem B4259395 : Blo 2243435 4259395 := bstep (se 1 (by rfl) ⟨3194546, by rfl⟩ : syracuseStep 4259395 = 6389093) B6389093
theorem B5679193 : Blo 2243435 5679193 := bstep (se 2 (by rfl) ⟨2129697, by rfl⟩ : syracuseStep 5679193 = 4259395) B4259395
theorem B7572257 : Blo 2243435 7572257 := bstep (se 2 (by rfl) ⟨2839596, by rfl⟩ : syracuseStep 7572257 = 5679193) B5679193
theorem B5048171 : Blo 2243435 5048171 := bstep (se 1 (by rfl) ⟨3786128, by rfl⟩ : syracuseStep 5048171 = 7572257) B7572257
theorem B3365447 : Blo 2243435 3365447 := bstep (se 1 (by rfl) ⟨2524085, by rfl⟩ : syracuseStep 3365447 = 5048171) B5048171
theorem B2243631 : Blo 2243435 2243631 := bstep (se 1 (by rfl) ⟨1682723, by rfl⟩ : syracuseStep 2243631 = 3365447) B3365447
theorem B3365453 : Blo 2243435 3365453 := bbase (se 3 (by rfl) ⟨631022, by rfl⟩ : syracuseStep 3365453 = 1262045) (by norm_num)
theorem B2243635 : Blo 2243435 2243635 := bstep (se 1 (by rfl) ⟨1682726, by rfl⟩ : syracuseStep 2243635 = 3365453) B3365453
theorem B5048189 : Blo 2243435 5048189 := bbase (se 3 (by rfl) ⟨946535, by rfl⟩ : syracuseStep 5048189 = 1893071) (by norm_num)
theorem B3365459 : Blo 2243435 3365459 := bstep (se 1 (by rfl) ⟨2524094, by rfl⟩ : syracuseStep 3365459 = 5048189) B5048189
theorem B2243639 : Blo 2243435 2243639 := bstep (se 1 (by rfl) ⟨1682729, by rfl⟩ : syracuseStep 2243639 = 3365459) B3365459
theorem B3786149 : Blo 2243435 3786149 := bbase (se 4 (by rfl) ⟨354951, by rfl⟩ : syracuseStep 3786149 = 709903) (by norm_num)
theorem B2524099 : Blo 2243435 2524099 := bstep (se 1 (by rfl) ⟨1893074, by rfl⟩ : syracuseStep 2524099 = 3786149) B3786149
theorem B3365465 : Blo 2243435 3365465 := bstep (se 2 (by rfl) ⟨1262049, by rfl⟩ : syracuseStep 3365465 = 2524099) B2524099
theorem B2243643 : Blo 2243435 2243643 := bstep (se 1 (by rfl) ⟨1682732, by rfl⟩ : syracuseStep 2243643 = 3365465) B3365465
theorem B5390837 : Blo 2243435 5390837 := bbase (se 5 (by rfl) ⟨252695, by rfl⟩ : syracuseStep 5390837 = 505391) (by norm_num)
theorem B3593891 : Blo 2243435 3593891 := bstep (se 1 (by rfl) ⟨2695418, by rfl⟩ : syracuseStep 3593891 = 5390837) B5390837
theorem B2395927 : Blo 2243435 2395927 := bstep (se 1 (by rfl) ⟨1796945, by rfl⟩ : syracuseStep 2395927 = 3593891) B3593891
theorem B3194569 : Blo 2243435 3194569 := bstep (se 2 (by rfl) ⟨1197963, by rfl⟩ : syracuseStep 3194569 = 2395927) B2395927
theorem B17037701 : Blo 2243435 17037701 := bstep (se 4 (by rfl) ⟨1597284, by rfl⟩ : syracuseStep 17037701 = 3194569) B3194569
theorem B11358467 : Blo 2243435 11358467 := bstep (se 1 (by rfl) ⟨8518850, by rfl⟩ : syracuseStep 11358467 = 17037701) B17037701
theorem B7572311 : Blo 2243435 7572311 := bstep (se 1 (by rfl) ⟨5679233, by rfl⟩ : syracuseStep 7572311 = 11358467) B11358467
theorem B5048207 : Blo 2243435 5048207 := bstep (se 1 (by rfl) ⟨3786155, by rfl⟩ : syracuseStep 5048207 = 7572311) B7572311
theorem B3365471 : Blo 2243435 3365471 := bstep (se 1 (by rfl) ⟨2524103, by rfl⟩ : syracuseStep 3365471 = 5048207) B5048207
theorem B2243647 : Blo 2243435 2243647 := bstep (se 1 (by rfl) ⟨1682735, by rfl⟩ : syracuseStep 2243647 = 3365471) B3365471
theorem B3365477 : Blo 2243435 3365477 := bbase (se 4 (by rfl) ⟨315513, by rfl⟩ : syracuseStep 3365477 = 631027) (by norm_num)
theorem B2243651 : Blo 2243435 2243651 := bstep (se 1 (by rfl) ⟨1682738, by rfl⟩ : syracuseStep 2243651 = 3365477) B3365477
theorem B3194581 : Blo 2243435 3194581 := bbase (se 7 (by rfl) ⟨37436, by rfl⟩ : syracuseStep 3194581 = 74873) (by norm_num)
theorem B4259441 : Blo 2243435 4259441 := bstep (se 2 (by rfl) ⟨1597290, by rfl⟩ : syracuseStep 4259441 = 3194581) B3194581
theorem B2839627 : Blo 2243435 2839627 := bstep (se 1 (by rfl) ⟨2129720, by rfl⟩ : syracuseStep 2839627 = 4259441) B4259441
theorem B3786169 : Blo 2243435 3786169 := bstep (se 2 (by rfl) ⟨1419813, by rfl⟩ : syracuseStep 3786169 = 2839627) B2839627
theorem B5048225 : Blo 2243435 5048225 := bstep (se 2 (by rfl) ⟨1893084, by rfl⟩ : syracuseStep 5048225 = 3786169) B3786169
theorem B3365483 : Blo 2243435 3365483 := bstep (se 1 (by rfl) ⟨2524112, by rfl⟩ : syracuseStep 3365483 = 5048225) B5048225
theorem B2243655 : Blo 2243435 2243655 := bstep (se 1 (by rfl) ⟨1682741, by rfl⟩ : syracuseStep 2243655 = 3365483) B3365483
theorem B2524117 : Blo 2243435 2524117 := bbase (se 7 (by rfl) ⟨29579, by rfl⟩ : syracuseStep 2524117 = 59159) (by norm_num)
theorem B3365489 : Blo 2243435 3365489 := bstep (se 2 (by rfl) ⟨1262058, by rfl⟩ : syracuseStep 3365489 = 2524117) B2524117
theorem B2243659 : Blo 2243435 2243659 := bstep (se 1 (by rfl) ⟨1682744, by rfl⟩ : syracuseStep 2243659 = 3365489) B3365489
theorem B2839637 : Blo 2243435 2839637 := bbase (se 8 (by rfl) ⟨16638, by rfl⟩ : syracuseStep 2839637 = 33277) (by norm_num)
theorem B7572365 : Blo 2243435 7572365 := bstep (se 3 (by rfl) ⟨1419818, by rfl⟩ : syracuseStep 7572365 = 2839637) B2839637
theorem B5048243 : Blo 2243435 5048243 := bstep (se 1 (by rfl) ⟨3786182, by rfl⟩ : syracuseStep 5048243 = 7572365) B7572365
theorem B3365495 : Blo 2243435 3365495 := bstep (se 1 (by rfl) ⟨2524121, by rfl⟩ : syracuseStep 3365495 = 5048243) B5048243
theorem B2243663 : Blo 2243435 2243663 := bstep (se 1 (by rfl) ⟨1682747, by rfl⟩ : syracuseStep 2243663 = 3365495) B3365495
theorem B3365501 : Blo 2243435 3365501 := bbase (se 3 (by rfl) ⟨631031, by rfl⟩ : syracuseStep 3365501 = 1262063) (by norm_num)
theorem B2243667 : Blo 2243435 2243667 := bstep (se 1 (by rfl) ⟨1682750, by rfl⟩ : syracuseStep 2243667 = 3365501) B3365501
theorem B5048261 : Blo 2243435 5048261 := bbase (se 4 (by rfl) ⟨473274, by rfl⟩ : syracuseStep 5048261 = 946549) (by norm_num)
theorem B3365507 : Blo 2243435 3365507 := bstep (se 1 (by rfl) ⟨2524130, by rfl⟩ : syracuseStep 3365507 = 5048261) B5048261
theorem B2243671 : Blo 2243435 2243671 := bstep (se 1 (by rfl) ⟨1682753, by rfl⟩ : syracuseStep 2243671 = 3365507) B3365507
theorem B9583829 : Blo 2243435 9583829 := bbase (se 7 (by rfl) ⟨112310, by rfl⟩ : syracuseStep 9583829 = 224621) (by norm_num)
theorem B6389219 : Blo 2243435 6389219 := bstep (se 1 (by rfl) ⟨4791914, by rfl⟩ : syracuseStep 6389219 = 9583829) B9583829
theorem B4259479 : Blo 2243435 4259479 := bstep (se 1 (by rfl) ⟨3194609, by rfl⟩ : syracuseStep 4259479 = 6389219) B6389219
theorem B5679305 : Blo 2243435 5679305 := bstep (se 2 (by rfl) ⟨2129739, by rfl⟩ : syracuseStep 5679305 = 4259479) B4259479
theorem B3786203 : Blo 2243435 3786203 := bstep (se 1 (by rfl) ⟨2839652, by rfl⟩ : syracuseStep 3786203 = 5679305) B5679305
theorem B2524135 : Blo 2243435 2524135 := bstep (se 1 (by rfl) ⟨1893101, by rfl⟩ : syracuseStep 2524135 = 3786203) B3786203
theorem B3365513 : Blo 2243435 3365513 := bstep (se 2 (by rfl) ⟨1262067, by rfl⟩ : syracuseStep 3365513 = 2524135) B2524135
theorem B2243675 : Blo 2243435 2243675 := bstep (se 1 (by rfl) ⟨1682756, by rfl⟩ : syracuseStep 2243675 = 3365513) B3365513
theorem B11358629 : Blo 2243435 11358629 := bbase (se 4 (by rfl) ⟨1064871, by rfl⟩ : syracuseStep 11358629 = 2129743) (by norm_num)
theorem B7572419 : Blo 2243435 7572419 := bstep (se 1 (by rfl) ⟨5679314, by rfl⟩ : syracuseStep 7572419 = 11358629) B11358629
theorem B5048279 : Blo 2243435 5048279 := bstep (se 1 (by rfl) ⟨3786209, by rfl⟩ : syracuseStep 5048279 = 7572419) B7572419
theorem B3365519 : Blo 2243435 3365519 := bstep (se 1 (by rfl) ⟨2524139, by rfl⟩ : syracuseStep 3365519 = 5048279) B5048279
theorem B2243679 : Blo 2243435 2243679 := bstep (se 1 (by rfl) ⟨1682759, by rfl⟩ : syracuseStep 2243679 = 3365519) B3365519
theorem B3365525 : Blo 2243435 3365525 := bbase (se 6 (by rfl) ⟨78879, by rfl⟩ : syracuseStep 3365525 = 157759) (by norm_num)
theorem B2243683 : Blo 2243435 2243683 := bstep (se 1 (by rfl) ⟨1682762, by rfl⟩ : syracuseStep 2243683 = 3365525) B3365525
theorem B3642989 : Blo 2243435 3642989 := bbase (se 3 (by rfl) ⟨683060, by rfl⟩ : syracuseStep 3642989 = 1366121) (by norm_num)
theorem B9714637 : Blo 2243435 9714637 := bstep (se 3 (by rfl) ⟨1821494, by rfl⟩ : syracuseStep 9714637 = 3642989) B3642989
theorem B51811397 : Blo 2243435 51811397 := bstep (se 4 (by rfl) ⟨4857318, by rfl⟩ : syracuseStep 51811397 = 9714637) B9714637
theorem B34540931 : Blo 2243435 34540931 := bstep (se 1 (by rfl) ⟨25905698, by rfl⟩ : syracuseStep 34540931 = 51811397) B51811397
theorem B23027287 : Blo 2243435 23027287 := bstep (se 1 (by rfl) ⟨17270465, by rfl⟩ : syracuseStep 23027287 = 34540931) B34540931
theorem B30703049 : Blo 2243435 30703049 := bstep (se 2 (by rfl) ⟨11513643, by rfl⟩ : syracuseStep 30703049 = 23027287) B23027287
theorem B20468699 : Blo 2243435 20468699 := bstep (se 1 (by rfl) ⟨15351524, by rfl⟩ : syracuseStep 20468699 = 30703049) B30703049
theorem B13645799 : Blo 2243435 13645799 := bstep (se 1 (by rfl) ⟨10234349, by rfl⟩ : syracuseStep 13645799 = 20468699) B20468699
theorem B9097199 : Blo 2243435 9097199 := bstep (se 1 (by rfl) ⟨6822899, by rfl⟩ : syracuseStep 9097199 = 13645799) B13645799
theorem B6064799 : Blo 2243435 6064799 := bstep (se 1 (by rfl) ⟨4548599, by rfl⟩ : syracuseStep 6064799 = 9097199) B9097199
theorem B16172797 : Blo 2243435 16172797 := bstep (se 3 (by rfl) ⟨3032399, by rfl⟩ : syracuseStep 16172797 = 6064799) B6064799
theorem B21563729 : Blo 2243435 21563729 := bstep (se 2 (by rfl) ⟨8086398, by rfl⟩ : syracuseStep 21563729 = 16172797) B16172797
theorem B14375819 : Blo 2243435 14375819 := bstep (se 1 (by rfl) ⟨10781864, by rfl⟩ : syracuseStep 14375819 = 21563729) B21563729
theorem B9583879 : Blo 2243435 9583879 := bstep (se 1 (by rfl) ⟨7187909, by rfl⟩ : syracuseStep 9583879 = 14375819) B14375819
theorem B12778505 : Blo 2243435 12778505 := bstep (se 2 (by rfl) ⟨4791939, by rfl⟩ : syracuseStep 12778505 = 9583879) B9583879
theorem B8519003 : Blo 2243435 8519003 := bstep (se 1 (by rfl) ⟨6389252, by rfl⟩ : syracuseStep 8519003 = 12778505) B12778505
theorem B5679335 : Blo 2243435 5679335 := bstep (se 1 (by rfl) ⟨4259501, by rfl⟩ : syracuseStep 5679335 = 8519003) B8519003
theorem B3786223 : Blo 2243435 3786223 := bstep (se 1 (by rfl) ⟨2839667, by rfl⟩ : syracuseStep 3786223 = 5679335) B5679335
theorem B5048297 : Blo 2243435 5048297 := bstep (se 2 (by rfl) ⟨1893111, by rfl⟩ : syracuseStep 5048297 = 3786223) B3786223
theorem B3365531 : Blo 2243435 3365531 := bstep (se 1 (by rfl) ⟨2524148, by rfl⟩ : syracuseStep 3365531 = 5048297) B5048297
theorem B2243687 : Blo 2243435 2243687 := bstep (se 1 (by rfl) ⟨1682765, by rfl⟩ : syracuseStep 2243687 = 3365531) B3365531
theorem B2524153 : Blo 2243435 2524153 := bbase (se 2 (by rfl) ⟨946557, by rfl⟩ : syracuseStep 2524153 = 1893115) (by norm_num)
theorem B3365537 : Blo 2243435 3365537 := bstep (se 2 (by rfl) ⟨1262076, by rfl⟩ : syracuseStep 3365537 = 2524153) B2524153
theorem B2243691 : Blo 2243435 2243691 := bstep (se 1 (by rfl) ⟨1682768, by rfl⟩ : syracuseStep 2243691 = 3365537) B3365537
theorem B2878421 : Blo 2243435 2878421 := bbase (se 7 (by rfl) ⟨33731, by rfl⟩ : syracuseStep 2878421 = 67463) (by norm_num)
theorem B30703157 : Blo 2243435 30703157 := bstep (se 5 (by rfl) ⟨1439210, by rfl⟩ : syracuseStep 30703157 = 2878421) B2878421
theorem B20468771 : Blo 2243435 20468771 := bstep (se 1 (by rfl) ⟨15351578, by rfl⟩ : syracuseStep 20468771 = 30703157) B30703157
theorem B13645847 : Blo 2243435 13645847 := bstep (se 1 (by rfl) ⟨10234385, by rfl⟩ : syracuseStep 13645847 = 20468771) B20468771
theorem B36388925 : Blo 2243435 36388925 := bstep (se 3 (by rfl) ⟨6822923, by rfl⟩ : syracuseStep 36388925 = 13645847) B13645847
theorem B24259283 : Blo 2243435 24259283 := bstep (se 1 (by rfl) ⟨18194462, by rfl⟩ : syracuseStep 24259283 = 36388925) B36388925
theorem B16172855 : Blo 2243435 16172855 := bstep (se 1 (by rfl) ⟨12129641, by rfl⟩ : syracuseStep 16172855 = 24259283) B24259283
theorem B10781903 : Blo 2243435 10781903 := bstep (se 1 (by rfl) ⟨8086427, by rfl⟩ : syracuseStep 10781903 = 16172855) B16172855
theorem B7187935 : Blo 2243435 7187935 := bstep (se 1 (by rfl) ⟨5390951, by rfl⟩ : syracuseStep 7187935 = 10781903) B10781903
theorem B9583913 : Blo 2243435 9583913 := bstep (se 2 (by rfl) ⟨3593967, by rfl⟩ : syracuseStep 9583913 = 7187935) B7187935
theorem B6389275 : Blo 2243435 6389275 := bstep (se 1 (by rfl) ⟨4791956, by rfl⟩ : syracuseStep 6389275 = 9583913) B9583913
theorem B8519033 : Blo 2243435 8519033 := bstep (se 2 (by rfl) ⟨3194637, by rfl⟩ : syracuseStep 8519033 = 6389275) B6389275
theorem B5679355 : Blo 2243435 5679355 := bstep (se 1 (by rfl) ⟨4259516, by rfl⟩ : syracuseStep 5679355 = 8519033) B8519033
theorem B7572473 : Blo 2243435 7572473 := bstep (se 2 (by rfl) ⟨2839677, by rfl⟩ : syracuseStep 7572473 = 5679355) B5679355
theorem B5048315 : Blo 2243435 5048315 := bstep (se 1 (by rfl) ⟨3786236, by rfl⟩ : syracuseStep 5048315 = 7572473) B7572473
theorem B3365543 : Blo 2243435 3365543 := bstep (se 1 (by rfl) ⟨2524157, by rfl⟩ : syracuseStep 3365543 = 5048315) B5048315
theorem B2243695 : Blo 2243435 2243695 := bstep (se 1 (by rfl) ⟨1682771, by rfl⟩ : syracuseStep 2243695 = 3365543) B3365543
theorem B3365549 : Blo 2243435 3365549 := bbase (se 3 (by rfl) ⟨631040, by rfl⟩ : syracuseStep 3365549 = 1262081) (by norm_num)
theorem B2243699 : Blo 2243435 2243699 := bstep (se 1 (by rfl) ⟨1682774, by rfl⟩ : syracuseStep 2243699 = 3365549) B3365549
theorem B5048333 : Blo 2243435 5048333 := bbase (se 3 (by rfl) ⟨946562, by rfl⟩ : syracuseStep 5048333 = 1893125) (by norm_num)
theorem B3365555 : Blo 2243435 3365555 := bstep (se 1 (by rfl) ⟨2524166, by rfl⟩ : syracuseStep 3365555 = 5048333) B5048333
theorem B2243703 : Blo 2243435 2243703 := bstep (se 1 (by rfl) ⟨1682777, by rfl⟩ : syracuseStep 2243703 = 3365555) B3365555
theorem B2839693 : Blo 2243435 2839693 := bbase (se 3 (by rfl) ⟨532442, by rfl⟩ : syracuseStep 2839693 = 1064885) (by norm_num)
theorem B3786257 : Blo 2243435 3786257 := bstep (se 2 (by rfl) ⟨1419846, by rfl⟩ : syracuseStep 3786257 = 2839693) B2839693
theorem B2524171 : Blo 2243435 2524171 := bstep (se 1 (by rfl) ⟨1893128, by rfl⟩ : syracuseStep 2524171 = 3786257) B3786257
theorem B3365561 : Blo 2243435 3365561 := bstep (se 2 (by rfl) ⟨1262085, by rfl⟩ : syracuseStep 3365561 = 2524171) B2524171
theorem B2243707 : Blo 2243435 2243707 := bstep (se 1 (by rfl) ⟨1682780, by rfl⟩ : syracuseStep 2243707 = 3365561) B3365561
theorem B21563957 : Blo 2243435 21563957 := bbase (se 5 (by rfl) ⟨1010810, by rfl⟩ : syracuseStep 21563957 = 2021621) (by norm_num)
theorem B14375971 : Blo 2243435 14375971 := bstep (se 1 (by rfl) ⟨10781978, by rfl⟩ : syracuseStep 14375971 = 21563957) B21563957
theorem B19167961 : Blo 2243435 19167961 := bstep (se 2 (by rfl) ⟨7187985, by rfl⟩ : syracuseStep 19167961 = 14375971) B14375971
theorem B25557281 : Blo 2243435 25557281 := bstep (se 2 (by rfl) ⟨9583980, by rfl⟩ : syracuseStep 25557281 = 19167961) B19167961
theorem B17038187 : Blo 2243435 17038187 := bstep (se 1 (by rfl) ⟨12778640, by rfl⟩ : syracuseStep 17038187 = 25557281) B25557281
theorem B11358791 : Blo 2243435 11358791 := bstep (se 1 (by rfl) ⟨8519093, by rfl⟩ : syracuseStep 11358791 = 17038187) B17038187
theorem B7572527 : Blo 2243435 7572527 := bstep (se 1 (by rfl) ⟨5679395, by rfl⟩ : syracuseStep 7572527 = 11358791) B11358791
theorem B5048351 : Blo 2243435 5048351 := bstep (se 1 (by rfl) ⟨3786263, by rfl⟩ : syracuseStep 5048351 = 7572527) B7572527
theorem B3365567 : Blo 2243435 3365567 := bstep (se 1 (by rfl) ⟨2524175, by rfl⟩ : syracuseStep 3365567 = 5048351) B5048351
theorem B2243711 : Blo 2243435 2243711 := bstep (se 1 (by rfl) ⟨1682783, by rfl⟩ : syracuseStep 2243711 = 3365567) B3365567
theorem B3365573 : Blo 2243435 3365573 := bbase (se 4 (by rfl) ⟨315522, by rfl⟩ : syracuseStep 3365573 = 631045) (by norm_num)
theorem B2243715 : Blo 2243435 2243715 := bstep (se 1 (by rfl) ⟨1682786, by rfl⟩ : syracuseStep 2243715 = 3365573) B3365573
theorem B3786277 : Blo 2243435 3786277 := bbase (se 4 (by rfl) ⟨354963, by rfl⟩ : syracuseStep 3786277 = 709927) (by norm_num)
theorem B5048369 : Blo 2243435 5048369 := bstep (se 2 (by rfl) ⟨1893138, by rfl⟩ : syracuseStep 5048369 = 3786277) B3786277
theorem B3365579 : Blo 2243435 3365579 := bstep (se 1 (by rfl) ⟨2524184, by rfl⟩ : syracuseStep 3365579 = 5048369) B5048369
theorem B2243719 : Blo 2243435 2243719 := bstep (se 1 (by rfl) ⟨1682789, by rfl⟩ : syracuseStep 2243719 = 3365579) B3365579
theorem B2524189 : Blo 2243435 2524189 := bbase (se 3 (by rfl) ⟨473285, by rfl⟩ : syracuseStep 2524189 = 946571) (by norm_num)
theorem B3365585 : Blo 2243435 3365585 := bstep (se 2 (by rfl) ⟨1262094, by rfl⟩ : syracuseStep 3365585 = 2524189) B2524189
theorem B2243723 : Blo 2243435 2243723 := bstep (se 1 (by rfl) ⟨1682792, by rfl⟩ : syracuseStep 2243723 = 3365585) B3365585
theorem B7572581 : Blo 2243435 7572581 := bbase (se 4 (by rfl) ⟨709929, by rfl⟩ : syracuseStep 7572581 = 1419859) (by norm_num)
theorem B5048387 : Blo 2243435 5048387 := bstep (se 1 (by rfl) ⟨3786290, by rfl⟩ : syracuseStep 5048387 = 7572581) B7572581
theorem B3365591 : Blo 2243435 3365591 := bstep (se 1 (by rfl) ⟨2524193, by rfl⟩ : syracuseStep 3365591 = 5048387) B5048387
theorem B2243727 : Blo 2243435 2243727 := bstep (se 1 (by rfl) ⟨1682795, by rfl⟩ : syracuseStep 2243727 = 3365591) B3365591
theorem B3365597 : Blo 2243435 3365597 := bbase (se 3 (by rfl) ⟨631049, by rfl⟩ : syracuseStep 3365597 = 1262099) (by norm_num)
theorem B2243731 : Blo 2243435 2243731 := bstep (se 1 (by rfl) ⟨1682798, by rfl⟩ : syracuseStep 2243731 = 3365597) B3365597
theorem B5048405 : Blo 2243435 5048405 := bbase (se 8 (by rfl) ⟨29580, by rfl⟩ : syracuseStep 5048405 = 59161) (by norm_num)
theorem B3365603 : Blo 2243435 3365603 := bstep (se 1 (by rfl) ⟨2524202, by rfl⟩ : syracuseStep 3365603 = 5048405) B5048405
theorem B2243735 : Blo 2243435 2243735 := bstep (se 1 (by rfl) ⟨1682801, by rfl⟩ : syracuseStep 2243735 = 3365603) B3365603
theorem B2695529 : Blo 2243435 2695529 := bbase (se 2 (by rfl) ⟨1010823, by rfl⟩ : syracuseStep 2695529 = 2021647) (by norm_num)
theorem B7188077 : Blo 2243435 7188077 := bstep (se 3 (by rfl) ⟨1347764, by rfl⟩ : syracuseStep 7188077 = 2695529) B2695529
theorem B4792051 : Blo 2243435 4792051 := bstep (se 1 (by rfl) ⟨3594038, by rfl⟩ : syracuseStep 4792051 = 7188077) B7188077
theorem B6389401 : Blo 2243435 6389401 := bstep (se 2 (by rfl) ⟨2396025, by rfl⟩ : syracuseStep 6389401 = 4792051) B4792051
theorem B8519201 : Blo 2243435 8519201 := bstep (se 2 (by rfl) ⟨3194700, by rfl⟩ : syracuseStep 8519201 = 6389401) B6389401
theorem B5679467 : Blo 2243435 5679467 := bstep (se 1 (by rfl) ⟨4259600, by rfl⟩ : syracuseStep 5679467 = 8519201) B8519201
theorem B3786311 : Blo 2243435 3786311 := bstep (se 1 (by rfl) ⟨2839733, by rfl⟩ : syracuseStep 3786311 = 5679467) B5679467
theorem B2524207 : Blo 2243435 2524207 := bstep (se 1 (by rfl) ⟨1893155, by rfl⟩ : syracuseStep 2524207 = 3786311) B3786311
theorem B3365609 : Blo 2243435 3365609 := bstep (se 2 (by rfl) ⟨1262103, by rfl⟩ : syracuseStep 3365609 = 2524207) B2524207
theorem B2243739 : Blo 2243435 2243739 := bstep (se 1 (by rfl) ⟨1682804, by rfl⟩ : syracuseStep 2243739 = 3365609) B3365609
theorem B4610773 : Blo 2243435 4610773 := bbase (se 7 (by rfl) ⟨54032, by rfl⟩ : syracuseStep 4610773 = 108065) (by norm_num)
theorem B24590789 : Blo 2243435 24590789 := bstep (se 4 (by rfl) ⟨2305386, by rfl⟩ : syracuseStep 24590789 = 4610773) B4610773
theorem B16393859 : Blo 2243435 16393859 := bstep (se 1 (by rfl) ⟨12295394, by rfl⟩ : syracuseStep 16393859 = 24590789) B24590789
theorem B10929239 : Blo 2243435 10929239 := bstep (se 1 (by rfl) ⟨8196929, by rfl⟩ : syracuseStep 10929239 = 16393859) B16393859
theorem B7286159 : Blo 2243435 7286159 := bstep (se 1 (by rfl) ⟨5464619, by rfl⟩ : syracuseStep 7286159 = 10929239) B10929239
theorem B19429757 : Blo 2243435 19429757 := bstep (se 3 (by rfl) ⟨3643079, by rfl⟩ : syracuseStep 19429757 = 7286159) B7286159
theorem B12953171 : Blo 2243435 12953171 := bstep (se 1 (by rfl) ⟨9714878, by rfl⟩ : syracuseStep 12953171 = 19429757) B19429757
theorem B8635447 : Blo 2243435 8635447 := bstep (se 1 (by rfl) ⟨6476585, by rfl⟩ : syracuseStep 8635447 = 12953171) B12953171
theorem B11513929 : Blo 2243435 11513929 := bstep (se 2 (by rfl) ⟨4317723, by rfl⟩ : syracuseStep 11513929 = 8635447) B8635447
theorem B15351905 : Blo 2243435 15351905 := bstep (se 2 (by rfl) ⟨5756964, by rfl⟩ : syracuseStep 15351905 = 11513929) B11513929
theorem B10234603 : Blo 2243435 10234603 := bstep (se 1 (by rfl) ⟨7675952, by rfl⟩ : syracuseStep 10234603 = 15351905) B15351905
theorem B54584549 : Blo 2243435 54584549 := bstep (se 4 (by rfl) ⟨5117301, by rfl⟩ : syracuseStep 54584549 = 10234603) B10234603
theorem B36389699 : Blo 2243435 36389699 := bstep (se 1 (by rfl) ⟨27292274, by rfl⟩ : syracuseStep 36389699 = 54584549) B54584549
theorem B24259799 : Blo 2243435 24259799 := bstep (se 1 (by rfl) ⟨18194849, by rfl⟩ : syracuseStep 24259799 = 36389699) B36389699
theorem B16173199 : Blo 2243435 16173199 := bstep (se 1 (by rfl) ⟨12129899, by rfl⟩ : syracuseStep 16173199 = 24259799) B24259799
theorem B21564265 : Blo 2243435 21564265 := bstep (se 2 (by rfl) ⟨8086599, by rfl⟩ : syracuseStep 21564265 = 16173199) B16173199
theorem B28752353 : Blo 2243435 28752353 := bstep (se 2 (by rfl) ⟨10782132, by rfl⟩ : syracuseStep 28752353 = 21564265) B21564265
theorem B19168235 : Blo 2243435 19168235 := bstep (se 1 (by rfl) ⟨14376176, by rfl⟩ : syracuseStep 19168235 = 28752353) B28752353
theorem B12778823 : Blo 2243435 12778823 := bstep (se 1 (by rfl) ⟨9584117, by rfl⟩ : syracuseStep 12778823 = 19168235) B19168235
theorem B8519215 : Blo 2243435 8519215 := bstep (se 1 (by rfl) ⟨6389411, by rfl⟩ : syracuseStep 8519215 = 12778823) B12778823
theorem B11358953 : Blo 2243435 11358953 := bstep (se 2 (by rfl) ⟨4259607, by rfl⟩ : syracuseStep 11358953 = 8519215) B8519215
theorem B7572635 : Blo 2243435 7572635 := bstep (se 1 (by rfl) ⟨5679476, by rfl⟩ : syracuseStep 7572635 = 11358953) B11358953
theorem B5048423 : Blo 2243435 5048423 := bstep (se 1 (by rfl) ⟨3786317, by rfl⟩ : syracuseStep 5048423 = 7572635) B7572635
theorem B3365615 : Blo 2243435 3365615 := bstep (se 1 (by rfl) ⟨2524211, by rfl⟩ : syracuseStep 3365615 = 5048423) B5048423
theorem B2243743 : Blo 2243435 2243743 := bstep (se 1 (by rfl) ⟨1682807, by rfl⟩ : syracuseStep 2243743 = 3365615) B3365615
theorem B3365621 : Blo 2243435 3365621 := bbase (se 5 (by rfl) ⟨157763, by rfl⟩ : syracuseStep 3365621 = 315527) (by norm_num)
theorem B2243747 : Blo 2243435 2243747 := bstep (se 1 (by rfl) ⟨1682810, by rfl⟩ : syracuseStep 2243747 = 3365621) B3365621
theorem B2274365 : Blo 2243435 2274365 := bbase (se 3 (by rfl) ⟨426443, by rfl⟩ : syracuseStep 2274365 = 852887) (by norm_num)
theorem B6064973 : Blo 2243435 6064973 := bstep (se 3 (by rfl) ⟨1137182, by rfl⟩ : syracuseStep 6064973 = 2274365) B2274365
theorem B4043315 : Blo 2243435 4043315 := bstep (se 1 (by rfl) ⟨3032486, by rfl⟩ : syracuseStep 4043315 = 6064973) B6064973
theorem B10782173 : Blo 2243435 10782173 := bstep (se 3 (by rfl) ⟨2021657, by rfl⟩ : syracuseStep 10782173 = 4043315) B4043315
theorem B7188115 : Blo 2243435 7188115 := bstep (se 1 (by rfl) ⟨5391086, by rfl⟩ : syracuseStep 7188115 = 10782173) B10782173
theorem B9584153 : Blo 2243435 9584153 := bstep (se 2 (by rfl) ⟨3594057, by rfl⟩ : syracuseStep 9584153 = 7188115) B7188115
theorem B6389435 : Blo 2243435 6389435 := bstep (se 1 (by rfl) ⟨4792076, by rfl⟩ : syracuseStep 6389435 = 9584153) B9584153
theorem B4259623 : Blo 2243435 4259623 := bstep (se 1 (by rfl) ⟨3194717, by rfl⟩ : syracuseStep 4259623 = 6389435) B6389435
theorem B5679497 : Blo 2243435 5679497 := bstep (se 2 (by rfl) ⟨2129811, by rfl⟩ : syracuseStep 5679497 = 4259623) B4259623
theorem B3786331 : Blo 2243435 3786331 := bstep (se 1 (by rfl) ⟨2839748, by rfl⟩ : syracuseStep 3786331 = 5679497) B5679497
theorem B5048441 : Blo 2243435 5048441 := bstep (se 2 (by rfl) ⟨1893165, by rfl⟩ : syracuseStep 5048441 = 3786331) B3786331
theorem B3365627 : Blo 2243435 3365627 := bstep (se 1 (by rfl) ⟨2524220, by rfl⟩ : syracuseStep 3365627 = 5048441) B5048441
theorem B2243751 : Blo 2243435 2243751 := bstep (se 1 (by rfl) ⟨1682813, by rfl⟩ : syracuseStep 2243751 = 3365627) B3365627
theorem B2524225 : Blo 2243435 2524225 := bbase (se 2 (by rfl) ⟨946584, by rfl⟩ : syracuseStep 2524225 = 1893169) (by norm_num)
theorem B3365633 : Blo 2243435 3365633 := bstep (se 2 (by rfl) ⟨1262112, by rfl⟩ : syracuseStep 3365633 = 2524225) B2524225
theorem B2243755 : Blo 2243435 2243755 := bstep (se 1 (by rfl) ⟨1682816, by rfl⟩ : syracuseStep 2243755 = 3365633) B3365633
theorem B5679517 : Blo 2243435 5679517 := bbase (se 3 (by rfl) ⟨1064909, by rfl⟩ : syracuseStep 5679517 = 2129819) (by norm_num)
theorem B7572689 : Blo 2243435 7572689 := bstep (se 2 (by rfl) ⟨2839758, by rfl⟩ : syracuseStep 7572689 = 5679517) B5679517
theorem B5048459 : Blo 2243435 5048459 := bstep (se 1 (by rfl) ⟨3786344, by rfl⟩ : syracuseStep 5048459 = 7572689) B7572689
theorem B3365639 : Blo 2243435 3365639 := bstep (se 1 (by rfl) ⟨2524229, by rfl⟩ : syracuseStep 3365639 = 5048459) B5048459
theorem B2243759 : Blo 2243435 2243759 := bstep (se 1 (by rfl) ⟨1682819, by rfl⟩ : syracuseStep 2243759 = 3365639) B3365639
theorem B3365645 : Blo 2243435 3365645 := bbase (se 3 (by rfl) ⟨631058, by rfl⟩ : syracuseStep 3365645 = 1262117) (by norm_num)
theorem B2243763 : Blo 2243435 2243763 := bstep (se 1 (by rfl) ⟨1682822, by rfl⟩ : syracuseStep 2243763 = 3365645) B3365645
theorem B5048477 : Blo 2243435 5048477 := bbase (se 3 (by rfl) ⟨946589, by rfl⟩ : syracuseStep 5048477 = 1893179) (by norm_num)
theorem B3365651 : Blo 2243435 3365651 := bstep (se 1 (by rfl) ⟨2524238, by rfl⟩ : syracuseStep 3365651 = 5048477) B5048477
theorem B2243767 : Blo 2243435 2243767 := bstep (se 1 (by rfl) ⟨1682825, by rfl⟩ : syracuseStep 2243767 = 3365651) B3365651
theorem B3786365 : Blo 2243435 3786365 := bbase (se 3 (by rfl) ⟨709943, by rfl⟩ : syracuseStep 3786365 = 1419887) (by norm_num)
theorem B2524243 : Blo 2243435 2524243 := bstep (se 1 (by rfl) ⟨1893182, by rfl⟩ : syracuseStep 2524243 = 3786365) B3786365
theorem B3365657 : Blo 2243435 3365657 := bstep (se 2 (by rfl) ⟨1262121, by rfl⟩ : syracuseStep 3365657 = 2524243) B2524243
theorem B2243771 : Blo 2243435 2243771 := bstep (se 1 (by rfl) ⟨1682828, by rfl⟩ : syracuseStep 2243771 = 3365657) B3365657
theorem B5915213 : Blo 2243435 5915213 := bbase (se 3 (by rfl) ⟨1109102, by rfl⟩ : syracuseStep 5915213 = 2218205) (by norm_num)
theorem B3943475 : Blo 2243435 3943475 := bstep (se 1 (by rfl) ⟨2957606, by rfl⟩ : syracuseStep 3943475 = 5915213) B5915213
theorem B2628983 : Blo 2243435 2628983 := bstep (se 1 (by rfl) ⟨1971737, by rfl⟩ : syracuseStep 2628983 = 3943475) B3943475
theorem B7010621 : Blo 2243435 7010621 := bstep (se 3 (by rfl) ⟨1314491, by rfl⟩ : syracuseStep 7010621 = 2628983) B2628983
theorem B4673747 : Blo 2243435 4673747 := bstep (se 1 (by rfl) ⟨3505310, by rfl⟩ : syracuseStep 4673747 = 7010621) B7010621
theorem B3115831 : Blo 2243435 3115831 := bstep (se 1 (by rfl) ⟨2336873, by rfl⟩ : syracuseStep 3115831 = 4673747) B4673747
theorem B4154441 : Blo 2243435 4154441 := bstep (se 2 (by rfl) ⟨1557915, by rfl⟩ : syracuseStep 4154441 = 3115831) B3115831
theorem B44314037 : Blo 2243435 44314037 := bstep (se 5 (by rfl) ⟨2077220, by rfl⟩ : syracuseStep 44314037 = 4154441) B4154441
theorem B29542691 : Blo 2243435 29542691 := bstep (se 1 (by rfl) ⟨22157018, by rfl⟩ : syracuseStep 29542691 = 44314037) B44314037
theorem B78780509 : Blo 2243435 78780509 := bstep (se 3 (by rfl) ⟨14771345, by rfl⟩ : syracuseStep 78780509 = 29542691) B29542691
theorem B52520339 : Blo 2243435 52520339 := bstep (se 1 (by rfl) ⟨39390254, by rfl⟩ : syracuseStep 52520339 = 78780509) B78780509
theorem B35013559 : Blo 2243435 35013559 := bstep (se 1 (by rfl) ⟨26260169, by rfl⟩ : syracuseStep 35013559 = 52520339) B52520339
theorem B46684745 : Blo 2243435 46684745 := bstep (se 2 (by rfl) ⟨17506779, by rfl⟩ : syracuseStep 46684745 = 35013559) B35013559
theorem B31123163 : Blo 2243435 31123163 := bstep (se 1 (by rfl) ⟨23342372, by rfl⟩ : syracuseStep 31123163 = 46684745) B46684745
theorem B82995101 : Blo 2243435 82995101 := bstep (se 3 (by rfl) ⟨15561581, by rfl⟩ : syracuseStep 82995101 = 31123163) B31123163
theorem B55330067 : Blo 2243435 55330067 := bstep (se 1 (by rfl) ⟨41497550, by rfl⟩ : syracuseStep 55330067 = 82995101) B82995101
theorem B147546845 : Blo 2243435 147546845 := bstep (se 3 (by rfl) ⟨27665033, by rfl⟩ : syracuseStep 147546845 = 55330067) B55330067
theorem B98364563 : Blo 2243435 98364563 := bstep (se 1 (by rfl) ⟨73773422, by rfl⟩ : syracuseStep 98364563 = 147546845) B147546845
theorem B65576375 : Blo 2243435 65576375 := bstep (se 1 (by rfl) ⟨49182281, by rfl⟩ : syracuseStep 65576375 = 98364563) B98364563
theorem B43717583 : Blo 2243435 43717583 := bstep (se 1 (by rfl) ⟨32788187, by rfl⟩ : syracuseStep 43717583 = 65576375) B65576375
theorem B29145055 : Blo 2243435 29145055 := bstep (se 1 (by rfl) ⟨21858791, by rfl⟩ : syracuseStep 29145055 = 43717583) B43717583
theorem B38860073 : Blo 2243435 38860073 := bstep (se 2 (by rfl) ⟨14572527, by rfl⟩ : syracuseStep 38860073 = 29145055) B29145055
theorem B25906715 : Blo 2243435 25906715 := bstep (se 1 (by rfl) ⟨19430036, by rfl⟩ : syracuseStep 25906715 = 38860073) B38860073
theorem B17271143 : Blo 2243435 17271143 := bstep (se 1 (by rfl) ⟨12953357, by rfl⟩ : syracuseStep 17271143 = 25906715) B25906715
theorem B11514095 : Blo 2243435 11514095 := bstep (se 1 (by rfl) ⟨8635571, by rfl⟩ : syracuseStep 11514095 = 17271143) B17271143
theorem B7676063 : Blo 2243435 7676063 := bstep (se 1 (by rfl) ⟨5757047, by rfl⟩ : syracuseStep 7676063 = 11514095) B11514095
theorem B5117375 : Blo 2243435 5117375 := bstep (se 1 (by rfl) ⟨3838031, by rfl⟩ : syracuseStep 5117375 = 7676063) B7676063
theorem B13646333 : Blo 2243435 13646333 := bstep (se 3 (by rfl) ⟨2558687, by rfl⟩ : syracuseStep 13646333 = 5117375) B5117375
theorem B36390221 : Blo 2243435 36390221 := bstep (se 3 (by rfl) ⟨6823166, by rfl⟩ : syracuseStep 36390221 = 13646333) B13646333
theorem B24260147 : Blo 2243435 24260147 := bstep (se 1 (by rfl) ⟨18195110, by rfl⟩ : syracuseStep 24260147 = 36390221) B36390221
theorem B16173431 : Blo 2243435 16173431 := bstep (se 1 (by rfl) ⟨12130073, by rfl⟩ : syracuseStep 16173431 = 24260147) B24260147
theorem B10782287 : Blo 2243435 10782287 := bstep (se 1 (by rfl) ⟨8086715, by rfl⟩ : syracuseStep 10782287 = 16173431) B16173431
theorem B7188191 : Blo 2243435 7188191 := bstep (se 1 (by rfl) ⟨5391143, by rfl⟩ : syracuseStep 7188191 = 10782287) B10782287
theorem B4792127 : Blo 2243435 4792127 := bstep (se 1 (by rfl) ⟨3594095, by rfl⟩ : syracuseStep 4792127 = 7188191) B7188191
theorem B12779005 : Blo 2243435 12779005 := bstep (se 3 (by rfl) ⟨2396063, by rfl⟩ : syracuseStep 12779005 = 4792127) B4792127
theorem B17038673 : Blo 2243435 17038673 := bstep (se 2 (by rfl) ⟨6389502, by rfl⟩ : syracuseStep 17038673 = 12779005) B12779005
theorem B11359115 : Blo 2243435 11359115 := bstep (se 1 (by rfl) ⟨8519336, by rfl⟩ : syracuseStep 11359115 = 17038673) B17038673
theorem B7572743 : Blo 2243435 7572743 := bstep (se 1 (by rfl) ⟨5679557, by rfl⟩ : syracuseStep 7572743 = 11359115) B11359115
theorem B5048495 : Blo 2243435 5048495 := bstep (se 1 (by rfl) ⟨3786371, by rfl⟩ : syracuseStep 5048495 = 7572743) B7572743
theorem B3365663 : Blo 2243435 3365663 := bstep (se 1 (by rfl) ⟨2524247, by rfl⟩ : syracuseStep 3365663 = 5048495) B5048495
theorem B2243775 : Blo 2243435 2243775 := bstep (se 1 (by rfl) ⟨1682831, by rfl⟩ : syracuseStep 2243775 = 3365663) B3365663
theorem B3365669 : Blo 2243435 3365669 := bbase (se 4 (by rfl) ⟨315531, by rfl⟩ : syracuseStep 3365669 = 631063) (by norm_num)
theorem B2243779 : Blo 2243435 2243779 := bstep (se 1 (by rfl) ⟨1682834, by rfl⟩ : syracuseStep 2243779 = 3365669) B3365669
theorem B2839789 : Blo 2243435 2839789 := bbase (se 3 (by rfl) ⟨532460, by rfl⟩ : syracuseStep 2839789 = 1064921) (by norm_num)
theorem B3786385 : Blo 2243435 3786385 := bstep (se 2 (by rfl) ⟨1419894, by rfl⟩ : syracuseStep 3786385 = 2839789) B2839789
theorem B5048513 : Blo 2243435 5048513 := bstep (se 2 (by rfl) ⟨1893192, by rfl⟩ : syracuseStep 5048513 = 3786385) B3786385
theorem B3365675 : Blo 2243435 3365675 := bstep (se 1 (by rfl) ⟨2524256, by rfl⟩ : syracuseStep 3365675 = 5048513) B5048513
theorem B2243783 : Blo 2243435 2243783 := bstep (se 1 (by rfl) ⟨1682837, by rfl⟩ : syracuseStep 2243783 = 3365675) B3365675
theorem B2524261 : Blo 2243435 2524261 := bbase (se 4 (by rfl) ⟨236649, by rfl⟩ : syracuseStep 2524261 = 473299) (by norm_num)
theorem B3365681 : Blo 2243435 3365681 := bstep (se 2 (by rfl) ⟨1262130, by rfl⟩ : syracuseStep 3365681 = 2524261) B2524261
theorem B2243787 : Blo 2243435 2243787 := bstep (se 1 (by rfl) ⟨1682840, by rfl⟩ : syracuseStep 2243787 = 3365681) B3365681
theorem B2396081 : Blo 2243435 2396081 := bbase (se 2 (by rfl) ⟨898530, by rfl⟩ : syracuseStep 2396081 = 1797061) (by norm_num)
theorem B6389549 : Blo 2243435 6389549 := bstep (se 3 (by rfl) ⟨1198040, by rfl⟩ : syracuseStep 6389549 = 2396081) B2396081
theorem B4259699 : Blo 2243435 4259699 := bstep (se 1 (by rfl) ⟨3194774, by rfl⟩ : syracuseStep 4259699 = 6389549) B6389549
theorem B2839799 : Blo 2243435 2839799 := bstep (se 1 (by rfl) ⟨2129849, by rfl⟩ : syracuseStep 2839799 = 4259699) B4259699
theorem B7572797 : Blo 2243435 7572797 := bstep (se 3 (by rfl) ⟨1419899, by rfl⟩ : syracuseStep 7572797 = 2839799) B2839799
theorem B5048531 : Blo 2243435 5048531 := bstep (se 1 (by rfl) ⟨3786398, by rfl⟩ : syracuseStep 5048531 = 7572797) B7572797
theorem B3365687 : Blo 2243435 3365687 := bstep (se 1 (by rfl) ⟨2524265, by rfl⟩ : syracuseStep 3365687 = 5048531) B5048531
theorem B2243791 : Blo 2243435 2243791 := bstep (se 1 (by rfl) ⟨1682843, by rfl⟩ : syracuseStep 2243791 = 3365687) B3365687
theorem B3365693 : Blo 2243435 3365693 := bbase (se 3 (by rfl) ⟨631067, by rfl⟩ : syracuseStep 3365693 = 1262135) (by norm_num)
theorem B2243795 : Blo 2243435 2243795 := bstep (se 1 (by rfl) ⟨1682846, by rfl⟩ : syracuseStep 2243795 = 3365693) B3365693
theorem B5048549 : Blo 2243435 5048549 := bbase (se 4 (by rfl) ⟨473301, by rfl⟩ : syracuseStep 5048549 = 946603) (by norm_num)
theorem B3365699 : Blo 2243435 3365699 := bstep (se 1 (by rfl) ⟨2524274, by rfl⟩ : syracuseStep 3365699 = 5048549) B5048549
theorem B2243799 : Blo 2243435 2243799 := bstep (se 1 (by rfl) ⟨1682849, by rfl⟩ : syracuseStep 2243799 = 3365699) B3365699
theorem B5679629 : Blo 2243435 5679629 := bbase (se 3 (by rfl) ⟨1064930, by rfl⟩ : syracuseStep 5679629 = 2129861) (by norm_num)
theorem B3786419 : Blo 2243435 3786419 := bstep (se 1 (by rfl) ⟨2839814, by rfl⟩ : syracuseStep 3786419 = 5679629) B5679629
theorem B2524279 : Blo 2243435 2524279 := bstep (se 1 (by rfl) ⟨1893209, by rfl⟩ : syracuseStep 2524279 = 3786419) B3786419
theorem B3365705 : Blo 2243435 3365705 := bstep (se 2 (by rfl) ⟨1262139, by rfl⟩ : syracuseStep 3365705 = 2524279) B2524279
theorem B2243803 : Blo 2243435 2243803 := bstep (se 1 (by rfl) ⟨1682852, by rfl⟩ : syracuseStep 2243803 = 3365705) B3365705
theorem B3194797 : Blo 2243435 3194797 := bbase (se 3 (by rfl) ⟨599024, by rfl⟩ : syracuseStep 3194797 = 1198049) (by norm_num)
theorem B4259729 : Blo 2243435 4259729 := bstep (se 2 (by rfl) ⟨1597398, by rfl⟩ : syracuseStep 4259729 = 3194797) B3194797
theorem B11359277 : Blo 2243435 11359277 := bstep (se 3 (by rfl) ⟨2129864, by rfl⟩ : syracuseStep 11359277 = 4259729) B4259729
theorem B7572851 : Blo 2243435 7572851 := bstep (se 1 (by rfl) ⟨5679638, by rfl⟩ : syracuseStep 7572851 = 11359277) B11359277
theorem B5048567 : Blo 2243435 5048567 := bstep (se 1 (by rfl) ⟨3786425, by rfl⟩ : syracuseStep 5048567 = 7572851) B7572851
theorem B3365711 : Blo 2243435 3365711 := bstep (se 1 (by rfl) ⟨2524283, by rfl⟩ : syracuseStep 3365711 = 5048567) B5048567
theorem B2243807 : Blo 2243435 2243807 := bstep (se 1 (by rfl) ⟨1682855, by rfl⟩ : syracuseStep 2243807 = 3365711) B3365711
theorem B3365717 : Blo 2243435 3365717 := bbase (se 9 (by rfl) ⟨9860, by rfl⟩ : syracuseStep 3365717 = 19721) (by norm_num)
theorem B2243811 : Blo 2243435 2243811 := bstep (se 1 (by rfl) ⟨1682858, by rfl⟩ : syracuseStep 2243811 = 3365717) B3365717
theorem B4792213 : Blo 2243435 4792213 := bbase (se 6 (by rfl) ⟨112317, by rfl⟩ : syracuseStep 4792213 = 224635) (by norm_num)
theorem B6389617 : Blo 2243435 6389617 := bstep (se 2 (by rfl) ⟨2396106, by rfl⟩ : syracuseStep 6389617 = 4792213) B4792213
theorem B8519489 : Blo 2243435 8519489 := bstep (se 2 (by rfl) ⟨3194808, by rfl⟩ : syracuseStep 8519489 = 6389617) B6389617
theorem B5679659 : Blo 2243435 5679659 := bstep (se 1 (by rfl) ⟨4259744, by rfl⟩ : syracuseStep 5679659 = 8519489) B8519489
theorem B3786439 : Blo 2243435 3786439 := bstep (se 1 (by rfl) ⟨2839829, by rfl⟩ : syracuseStep 3786439 = 5679659) B5679659
theorem B5048585 : Blo 2243435 5048585 := bstep (se 2 (by rfl) ⟨1893219, by rfl⟩ : syracuseStep 5048585 = 3786439) B3786439
theorem B3365723 : Blo 2243435 3365723 := bstep (se 1 (by rfl) ⟨2524292, by rfl⟩ : syracuseStep 3365723 = 5048585) B5048585
theorem B2243815 : Blo 2243435 2243815 := bstep (se 1 (by rfl) ⟨1682861, by rfl⟩ : syracuseStep 2243815 = 3365723) B3365723
theorem B2524297 : Blo 2243435 2524297 := bbase (se 2 (by rfl) ⟨946611, by rfl⟩ : syracuseStep 2524297 = 1893223) (by norm_num)
theorem B3365729 : Blo 2243435 3365729 := bstep (se 2 (by rfl) ⟨1262148, by rfl⟩ : syracuseStep 3365729 = 2524297) B2524297
theorem B2243819 : Blo 2243435 2243819 := bstep (se 1 (by rfl) ⟨1682864, by rfl⟩ : syracuseStep 2243819 = 3365729) B3365729
theorem B43130069 : Blo 2243435 43130069 := bbase (se 7 (by rfl) ⟨505430, by rfl⟩ : syracuseStep 43130069 = 1010861) (by norm_num)
theorem B28753379 : Blo 2243435 28753379 := bstep (se 1 (by rfl) ⟨21565034, by rfl⟩ : syracuseStep 28753379 = 43130069) B43130069
theorem B19168919 : Blo 2243435 19168919 := bstep (se 1 (by rfl) ⟨14376689, by rfl⟩ : syracuseStep 19168919 = 28753379) B28753379
theorem B12779279 : Blo 2243435 12779279 := bstep (se 1 (by rfl) ⟨9584459, by rfl⟩ : syracuseStep 12779279 = 19168919) B19168919
theorem B8519519 : Blo 2243435 8519519 := bstep (se 1 (by rfl) ⟨6389639, by rfl⟩ : syracuseStep 8519519 = 12779279) B12779279
theorem B5679679 : Blo 2243435 5679679 := bstep (se 1 (by rfl) ⟨4259759, by rfl⟩ : syracuseStep 5679679 = 8519519) B8519519
theorem B7572905 : Blo 2243435 7572905 := bstep (se 2 (by rfl) ⟨2839839, by rfl⟩ : syracuseStep 7572905 = 5679679) B5679679
theorem B5048603 : Blo 2243435 5048603 := bstep (se 1 (by rfl) ⟨3786452, by rfl⟩ : syracuseStep 5048603 = 7572905) B7572905
theorem B3365735 : Blo 2243435 3365735 := bstep (se 1 (by rfl) ⟨2524301, by rfl⟩ : syracuseStep 3365735 = 5048603) B5048603
theorem B2243823 : Blo 2243435 2243823 := bstep (se 1 (by rfl) ⟨1682867, by rfl⟩ : syracuseStep 2243823 = 3365735) B3365735
theorem B3365741 : Blo 2243435 3365741 := bbase (se 3 (by rfl) ⟨631076, by rfl⟩ : syracuseStep 3365741 = 1262153) (by norm_num)
theorem B2243827 : Blo 2243435 2243827 := bstep (se 1 (by rfl) ⟨1682870, by rfl⟩ : syracuseStep 2243827 = 3365741) B3365741
theorem B5048621 : Blo 2243435 5048621 := bbase (se 3 (by rfl) ⟨946616, by rfl⟩ : syracuseStep 5048621 = 1893233) (by norm_num)
theorem B3365747 : Blo 2243435 3365747 := bstep (se 1 (by rfl) ⟨2524310, by rfl⟩ : syracuseStep 3365747 = 5048621) B5048621
theorem B2243831 : Blo 2243435 2243831 := bstep (se 1 (by rfl) ⟨1682873, by rfl⟩ : syracuseStep 2243831 = 3365747) B3365747
theorem B4548901 : Blo 2243435 4548901 := bbase (se 4 (by rfl) ⟨426459, by rfl⟩ : syracuseStep 4548901 = 852919) (by norm_num)
theorem B6065201 : Blo 2243435 6065201 := bstep (se 2 (by rfl) ⟨2274450, by rfl⟩ : syracuseStep 6065201 = 4548901) B4548901
theorem B4043467 : Blo 2243435 4043467 := bstep (se 1 (by rfl) ⟨3032600, by rfl⟩ : syracuseStep 4043467 = 6065201) B6065201
theorem B5391289 : Blo 2243435 5391289 := bstep (se 2 (by rfl) ⟨2021733, by rfl⟩ : syracuseStep 5391289 = 4043467) B4043467
theorem B7188385 : Blo 2243435 7188385 := bstep (se 2 (by rfl) ⟨2695644, by rfl⟩ : syracuseStep 7188385 = 5391289) B5391289
theorem B9584513 : Blo 2243435 9584513 := bstep (se 2 (by rfl) ⟨3594192, by rfl⟩ : syracuseStep 9584513 = 7188385) B7188385
theorem B6389675 : Blo 2243435 6389675 := bstep (se 1 (by rfl) ⟨4792256, by rfl⟩ : syracuseStep 6389675 = 9584513) B9584513
theorem B4259783 : Blo 2243435 4259783 := bstep (se 1 (by rfl) ⟨3194837, by rfl⟩ : syracuseStep 4259783 = 6389675) B6389675
theorem B2839855 : Blo 2243435 2839855 := bstep (se 1 (by rfl) ⟨2129891, by rfl⟩ : syracuseStep 2839855 = 4259783) B4259783
theorem B3786473 : Blo 2243435 3786473 := bstep (se 2 (by rfl) ⟨1419927, by rfl⟩ : syracuseStep 3786473 = 2839855) B2839855
theorem B2524315 : Blo 2243435 2524315 := bstep (se 1 (by rfl) ⟨1893236, by rfl⟩ : syracuseStep 2524315 = 3786473) B3786473
theorem B3365753 : Blo 2243435 3365753 := bstep (se 2 (by rfl) ⟨1262157, by rfl⟩ : syracuseStep 3365753 = 2524315) B2524315
theorem B2243835 : Blo 2243435 2243835 := bstep (se 1 (by rfl) ⟨1682876, by rfl⟩ : syracuseStep 2243835 = 3365753) B3365753
theorem B3838141 : Blo 2243435 3838141 := bbase (se 3 (by rfl) ⟨719651, by rfl⟩ : syracuseStep 3838141 = 1439303) (by norm_num)
theorem B5117521 : Blo 2243435 5117521 := bstep (se 2 (by rfl) ⟨1919070, by rfl⟩ : syracuseStep 5117521 = 3838141) B3838141
theorem B6823361 : Blo 2243435 6823361 := bstep (se 2 (by rfl) ⟨2558760, by rfl⟩ : syracuseStep 6823361 = 5117521) B5117521
theorem B4548907 : Blo 2243435 4548907 := bstep (se 1 (by rfl) ⟨3411680, by rfl⟩ : syracuseStep 4548907 = 6823361) B6823361
theorem B6065209 : Blo 2243435 6065209 := bstep (se 2 (by rfl) ⟨2274453, by rfl⟩ : syracuseStep 6065209 = 4548907) B4548907
theorem B32347781 : Blo 2243435 32347781 := bstep (se 4 (by rfl) ⟨3032604, by rfl⟩ : syracuseStep 32347781 = 6065209) B6065209
theorem B21565187 : Blo 2243435 21565187 := bstep (se 1 (by rfl) ⟨16173890, by rfl⟩ : syracuseStep 21565187 = 32347781) B32347781
theorem B14376791 : Blo 2243435 14376791 := bstep (se 1 (by rfl) ⟨10782593, by rfl⟩ : syracuseStep 14376791 = 21565187) B21565187
theorem B38338109 : Blo 2243435 38338109 := bstep (se 3 (by rfl) ⟨7188395, by rfl⟩ : syracuseStep 38338109 = 14376791) B14376791
theorem B25558739 : Blo 2243435 25558739 := bstep (se 1 (by rfl) ⟨19169054, by rfl⟩ : syracuseStep 25558739 = 38338109) B38338109
theorem B17039159 : Blo 2243435 17039159 := bstep (se 1 (by rfl) ⟨12779369, by rfl⟩ : syracuseStep 17039159 = 25558739) B25558739
theorem B11359439 : Blo 2243435 11359439 := bstep (se 1 (by rfl) ⟨8519579, by rfl⟩ : syracuseStep 11359439 = 17039159) B17039159
theorem B7572959 : Blo 2243435 7572959 := bstep (se 1 (by rfl) ⟨5679719, by rfl⟩ : syracuseStep 7572959 = 11359439) B11359439
theorem B5048639 : Blo 2243435 5048639 := bstep (se 1 (by rfl) ⟨3786479, by rfl⟩ : syracuseStep 5048639 = 7572959) B7572959
theorem B3365759 : Blo 2243435 3365759 := bstep (se 1 (by rfl) ⟨2524319, by rfl⟩ : syracuseStep 3365759 = 5048639) B5048639
theorem B2243839 : Blo 2243435 2243839 := bstep (se 1 (by rfl) ⟨1682879, by rfl⟩ : syracuseStep 2243839 = 3365759) B3365759
theorem B3365765 : Blo 2243435 3365765 := bbase (se 4 (by rfl) ⟨315540, by rfl⟩ : syracuseStep 3365765 = 631081) (by norm_num)
theorem B2243843 : Blo 2243435 2243843 := bstep (se 1 (by rfl) ⟨1682882, by rfl⟩ : syracuseStep 2243843 = 3365765) B3365765
theorem B3786493 : Blo 2243435 3786493 := bbase (se 3 (by rfl) ⟨709967, by rfl⟩ : syracuseStep 3786493 = 1419935) (by norm_num)
theorem B5048657 : Blo 2243435 5048657 := bstep (se 2 (by rfl) ⟨1893246, by rfl⟩ : syracuseStep 5048657 = 3786493) B3786493
theorem B3365771 : Blo 2243435 3365771 := bstep (se 1 (by rfl) ⟨2524328, by rfl⟩ : syracuseStep 3365771 = 5048657) B5048657
theorem B2243847 : Blo 2243435 2243847 := bstep (se 1 (by rfl) ⟨1682885, by rfl⟩ : syracuseStep 2243847 = 3365771) B3365771
theorem B2524333 : Blo 2243435 2524333 := bbase (se 3 (by rfl) ⟨473312, by rfl⟩ : syracuseStep 2524333 = 946625) (by norm_num)
theorem B3365777 : Blo 2243435 3365777 := bstep (se 2 (by rfl) ⟨1262166, by rfl⟩ : syracuseStep 3365777 = 2524333) B2524333
theorem B2243851 : Blo 2243435 2243851 := bstep (se 1 (by rfl) ⟨1682888, by rfl⟩ : syracuseStep 2243851 = 3365777) B3365777
theorem B7573013 : Blo 2243435 7573013 := bbase (se 6 (by rfl) ⟨177492, by rfl⟩ : syracuseStep 7573013 = 354985) (by norm_num)
theorem B5048675 : Blo 2243435 5048675 := bstep (se 1 (by rfl) ⟨3786506, by rfl⟩ : syracuseStep 5048675 = 7573013) B7573013
theorem B3365783 : Blo 2243435 3365783 := bstep (se 1 (by rfl) ⟨2524337, by rfl⟩ : syracuseStep 3365783 = 5048675) B5048675
theorem B2243855 : Blo 2243435 2243855 := bstep (se 1 (by rfl) ⟨1682891, by rfl⟩ : syracuseStep 2243855 = 3365783) B3365783
theorem B3365789 : Blo 2243435 3365789 := bbase (se 3 (by rfl) ⟨631085, by rfl⟩ : syracuseStep 3365789 = 1262171) (by norm_num)
theorem B2243859 : Blo 2243435 2243859 := bstep (se 1 (by rfl) ⟨1682894, by rfl⟩ : syracuseStep 2243859 = 3365789) B3365789
theorem B5048693 : Blo 2243435 5048693 := bbase (se 5 (by rfl) ⟨236657, by rfl⟩ : syracuseStep 5048693 = 473315) (by norm_num)
theorem B3365795 : Blo 2243435 3365795 := bstep (se 1 (by rfl) ⟨2524346, by rfl⟩ : syracuseStep 3365795 = 5048693) B5048693
theorem B2243863 : Blo 2243435 2243863 := bstep (se 1 (by rfl) ⟨1682897, by rfl⟩ : syracuseStep 2243863 = 3365795) B3365795
theorem B5391365 : Blo 2243435 5391365 := bbase (se 4 (by rfl) ⟨505440, by rfl⟩ : syracuseStep 5391365 = 1010881) (by norm_num)
theorem B14376973 : Blo 2243435 14376973 := bstep (se 3 (by rfl) ⟨2695682, by rfl⟩ : syracuseStep 14376973 = 5391365) B5391365
theorem B19169297 : Blo 2243435 19169297 := bstep (se 2 (by rfl) ⟨7188486, by rfl⟩ : syracuseStep 19169297 = 14376973) B14376973
theorem B12779531 : Blo 2243435 12779531 := bstep (se 1 (by rfl) ⟨9584648, by rfl⟩ : syracuseStep 12779531 = 19169297) B19169297
theorem B8519687 : Blo 2243435 8519687 := bstep (se 1 (by rfl) ⟨6389765, by rfl⟩ : syracuseStep 8519687 = 12779531) B12779531
theorem B5679791 : Blo 2243435 5679791 := bstep (se 1 (by rfl) ⟨4259843, by rfl⟩ : syracuseStep 5679791 = 8519687) B8519687
theorem B3786527 : Blo 2243435 3786527 := bstep (se 1 (by rfl) ⟨2839895, by rfl⟩ : syracuseStep 3786527 = 5679791) B5679791
theorem B2524351 : Blo 2243435 2524351 := bstep (se 1 (by rfl) ⟨1893263, by rfl⟩ : syracuseStep 2524351 = 3786527) B3786527
theorem B3365801 : Blo 2243435 3365801 := bstep (se 2 (by rfl) ⟨1262175, by rfl⟩ : syracuseStep 3365801 = 2524351) B2524351
theorem B2243867 : Blo 2243435 2243867 := bstep (se 1 (by rfl) ⟨1682900, by rfl⟩ : syracuseStep 2243867 = 3365801) B3365801
theorem B8519701 : Blo 2243435 8519701 := bbase (se 6 (by rfl) ⟨199680, by rfl⟩ : syracuseStep 8519701 = 399361) (by norm_num)
theorem B11359601 : Blo 2243435 11359601 := bstep (se 2 (by rfl) ⟨4259850, by rfl⟩ : syracuseStep 11359601 = 8519701) B8519701
theorem B7573067 : Blo 2243435 7573067 := bstep (se 1 (by rfl) ⟨5679800, by rfl⟩ : syracuseStep 7573067 = 11359601) B11359601
theorem B5048711 : Blo 2243435 5048711 := bstep (se 1 (by rfl) ⟨3786533, by rfl⟩ : syracuseStep 5048711 = 7573067) B7573067
theorem B3365807 : Blo 2243435 3365807 := bstep (se 1 (by rfl) ⟨2524355, by rfl⟩ : syracuseStep 3365807 = 5048711) B5048711
theorem B2243871 : Blo 2243435 2243871 := bstep (se 1 (by rfl) ⟨1682903, by rfl⟩ : syracuseStep 2243871 = 3365807) B3365807
theorem B3365813 : Blo 2243435 3365813 := bbase (se 5 (by rfl) ⟨157772, by rfl⟩ : syracuseStep 3365813 = 315545) (by norm_num)
theorem B2243875 : Blo 2243435 2243875 := bstep (se 1 (by rfl) ⟨1682906, by rfl⟩ : syracuseStep 2243875 = 3365813) B3365813
theorem B5679821 : Blo 2243435 5679821 := bbase (se 3 (by rfl) ⟨1064966, by rfl⟩ : syracuseStep 5679821 = 2129933) (by norm_num)
theorem B3786547 : Blo 2243435 3786547 := bstep (se 1 (by rfl) ⟨2839910, by rfl⟩ : syracuseStep 3786547 = 5679821) B5679821
theorem B5048729 : Blo 2243435 5048729 := bstep (se 2 (by rfl) ⟨1893273, by rfl⟩ : syracuseStep 5048729 = 3786547) B3786547
theorem B3365819 : Blo 2243435 3365819 := bstep (se 1 (by rfl) ⟨2524364, by rfl⟩ : syracuseStep 3365819 = 5048729) B5048729
theorem B2243879 : Blo 2243435 2243879 := bstep (se 1 (by rfl) ⟨1682909, by rfl⟩ : syracuseStep 2243879 = 3365819) B3365819
theorem B2524369 : Blo 2243435 2524369 := bbase (se 2 (by rfl) ⟨946638, by rfl⟩ : syracuseStep 2524369 = 1893277) (by norm_num)
theorem B3365825 : Blo 2243435 3365825 := bstep (se 2 (by rfl) ⟨1262184, by rfl⟩ : syracuseStep 3365825 = 2524369) B2524369
theorem B2243883 : Blo 2243435 2243883 := bstep (se 1 (by rfl) ⟨1682912, by rfl⟩ : syracuseStep 2243883 = 3365825) B3365825
theorem B23662037 : Blo 2243435 23662037 := bbase (se 7 (by rfl) ⟨277289, by rfl⟩ : syracuseStep 23662037 = 554579) (by norm_num)
theorem B15774691 : Blo 2243435 15774691 := bstep (se 1 (by rfl) ⟨11831018, by rfl⟩ : syracuseStep 15774691 = 23662037) B23662037
theorem B21032921 : Blo 2243435 21032921 := bstep (se 2 (by rfl) ⟨7887345, by rfl⟩ : syracuseStep 21032921 = 15774691) B15774691
theorem B14021947 : Blo 2243435 14021947 := bstep (se 1 (by rfl) ⟨10516460, by rfl⟩ : syracuseStep 14021947 = 21032921) B21032921
theorem B18695929 : Blo 2243435 18695929 := bstep (se 2 (by rfl) ⟨7010973, by rfl⟩ : syracuseStep 18695929 = 14021947) B14021947
theorem B24927905 : Blo 2243435 24927905 := bstep (se 2 (by rfl) ⟨9347964, by rfl⟩ : syracuseStep 24927905 = 18695929) B18695929
theorem B16618603 : Blo 2243435 16618603 := bstep (se 1 (by rfl) ⟨12463952, by rfl⟩ : syracuseStep 16618603 = 24927905) B24927905
theorem B22158137 : Blo 2243435 22158137 := bstep (se 2 (by rfl) ⟨8309301, by rfl⟩ : syracuseStep 22158137 = 16618603) B16618603
theorem B59088365 : Blo 2243435 59088365 := bstep (se 3 (by rfl) ⟨11079068, by rfl⟩ : syracuseStep 59088365 = 22158137) B22158137
theorem B39392243 : Blo 2243435 39392243 := bstep (se 1 (by rfl) ⟨29544182, by rfl⟩ : syracuseStep 39392243 = 59088365) B59088365
theorem B26261495 : Blo 2243435 26261495 := bstep (se 1 (by rfl) ⟨19696121, by rfl⟩ : syracuseStep 26261495 = 39392243) B39392243
theorem B17507663 : Blo 2243435 17507663 := bstep (se 1 (by rfl) ⟨13130747, by rfl⟩ : syracuseStep 17507663 = 26261495) B26261495
theorem B11671775 : Blo 2243435 11671775 := bstep (se 1 (by rfl) ⟨8753831, by rfl⟩ : syracuseStep 11671775 = 17507663) B17507663
theorem B7781183 : Blo 2243435 7781183 := bstep (se 1 (by rfl) ⟨5835887, by rfl⟩ : syracuseStep 7781183 = 11671775) B11671775
theorem B5187455 : Blo 2243435 5187455 := bstep (se 1 (by rfl) ⟨3890591, by rfl⟩ : syracuseStep 5187455 = 7781183) B7781183
theorem B3458303 : Blo 2243435 3458303 := bstep (se 1 (by rfl) ⟨2593727, by rfl⟩ : syracuseStep 3458303 = 5187455) B5187455
theorem B2305535 : Blo 2243435 2305535 := bstep (se 1 (by rfl) ⟨1729151, by rfl⟩ : syracuseStep 2305535 = 3458303) B3458303
theorem B6148093 : Blo 2243435 6148093 := bstep (se 3 (by rfl) ⟨1152767, by rfl⟩ : syracuseStep 6148093 = 2305535) B2305535
theorem B8197457 : Blo 2243435 8197457 := bstep (se 2 (by rfl) ⟨3074046, by rfl⟩ : syracuseStep 8197457 = 6148093) B6148093
theorem B21859885 : Blo 2243435 21859885 := bstep (se 3 (by rfl) ⟨4098728, by rfl⟩ : syracuseStep 21859885 = 8197457) B8197457
theorem B116586053 : Blo 2243435 116586053 := bstep (se 4 (by rfl) ⟨10929942, by rfl⟩ : syracuseStep 116586053 = 21859885) B21859885
theorem B77724035 : Blo 2243435 77724035 := bstep (se 1 (by rfl) ⟨58293026, by rfl⟩ : syracuseStep 77724035 = 116586053) B116586053
theorem B51816023 : Blo 2243435 51816023 := bstep (se 1 (by rfl) ⟨38862017, by rfl⟩ : syracuseStep 51816023 = 77724035) B77724035
theorem B34544015 : Blo 2243435 34544015 := bstep (se 1 (by rfl) ⟨25908011, by rfl⟩ : syracuseStep 34544015 = 51816023) B51816023
theorem B23029343 : Blo 2243435 23029343 := bstep (se 1 (by rfl) ⟨17272007, by rfl⟩ : syracuseStep 23029343 = 34544015) B34544015
theorem B15352895 : Blo 2243435 15352895 := bstep (se 1 (by rfl) ⟨11514671, by rfl⟩ : syracuseStep 15352895 = 23029343) B23029343
theorem B10235263 : Blo 2243435 10235263 := bstep (se 1 (by rfl) ⟨7676447, by rfl⟩ : syracuseStep 10235263 = 15352895) B15352895
theorem B13647017 : Blo 2243435 13647017 := bstep (se 2 (by rfl) ⟨5117631, by rfl⟩ : syracuseStep 13647017 = 10235263) B10235263
theorem B9098011 : Blo 2243435 9098011 := bstep (se 1 (by rfl) ⟨6823508, by rfl⟩ : syracuseStep 9098011 = 13647017) B13647017
theorem B12130681 : Blo 2243435 12130681 := bstep (se 2 (by rfl) ⟨4549005, by rfl⟩ : syracuseStep 12130681 = 9098011) B9098011
theorem B16174241 : Blo 2243435 16174241 := bstep (se 2 (by rfl) ⟨6065340, by rfl⟩ : syracuseStep 16174241 = 12130681) B12130681
theorem B10782827 : Blo 2243435 10782827 := bstep (se 1 (by rfl) ⟨8087120, by rfl⟩ : syracuseStep 10782827 = 16174241) B16174241
theorem B7188551 : Blo 2243435 7188551 := bstep (se 1 (by rfl) ⟨5391413, by rfl⟩ : syracuseStep 7188551 = 10782827) B10782827
theorem B4792367 : Blo 2243435 4792367 := bstep (se 1 (by rfl) ⟨3594275, by rfl⟩ : syracuseStep 4792367 = 7188551) B7188551
theorem B3194911 : Blo 2243435 3194911 := bstep (se 1 (by rfl) ⟨2396183, by rfl⟩ : syracuseStep 3194911 = 4792367) B4792367
theorem B4259881 : Blo 2243435 4259881 := bstep (se 2 (by rfl) ⟨1597455, by rfl⟩ : syracuseStep 4259881 = 3194911) B3194911
theorem B5679841 : Blo 2243435 5679841 := bstep (se 2 (by rfl) ⟨2129940, by rfl⟩ : syracuseStep 5679841 = 4259881) B4259881
theorem B7573121 : Blo 2243435 7573121 := bstep (se 2 (by rfl) ⟨2839920, by rfl⟩ : syracuseStep 7573121 = 5679841) B5679841
theorem B5048747 : Blo 2243435 5048747 := bstep (se 1 (by rfl) ⟨3786560, by rfl⟩ : syracuseStep 5048747 = 7573121) B7573121
theorem B3365831 : Blo 2243435 3365831 := bstep (se 1 (by rfl) ⟨2524373, by rfl⟩ : syracuseStep 3365831 = 5048747) B5048747
theorem B2243887 : Blo 2243435 2243887 := bstep (se 1 (by rfl) ⟨1682915, by rfl⟩ : syracuseStep 2243887 = 3365831) B3365831
theorem B3365837 : Blo 2243435 3365837 := bbase (se 3 (by rfl) ⟨631094, by rfl⟩ : syracuseStep 3365837 = 1262189) (by norm_num)
theorem B2243891 : Blo 2243435 2243891 := bstep (se 1 (by rfl) ⟨1682918, by rfl⟩ : syracuseStep 2243891 = 3365837) B3365837
theorem B5048765 : Blo 2243435 5048765 := bbase (se 3 (by rfl) ⟨946643, by rfl⟩ : syracuseStep 5048765 = 1893287) (by norm_num)
theorem B3365843 : Blo 2243435 3365843 := bstep (se 1 (by rfl) ⟨2524382, by rfl⟩ : syracuseStep 3365843 = 5048765) B5048765
theorem B2243895 : Blo 2243435 2243895 := bstep (se 1 (by rfl) ⟨1682921, by rfl⟩ : syracuseStep 2243895 = 3365843) B3365843
theorem B3786581 : Blo 2243435 3786581 := bbase (se 9 (by rfl) ⟨11093, by rfl⟩ : syracuseStep 3786581 = 22187) (by norm_num)
theorem B2524387 : Blo 2243435 2524387 := bstep (se 1 (by rfl) ⟨1893290, by rfl⟩ : syracuseStep 2524387 = 3786581) B3786581
theorem B3365849 : Blo 2243435 3365849 := bstep (se 2 (by rfl) ⟨1262193, by rfl⟩ : syracuseStep 3365849 = 2524387) B2524387
theorem B2243899 : Blo 2243435 2243899 := bstep (se 1 (by rfl) ⟨1682924, by rfl⟩ : syracuseStep 2243899 = 3365849) B3365849
theorem B9715573 : Blo 2243435 9715573 := bbase (se 5 (by rfl) ⟨455417, by rfl⟩ : syracuseStep 9715573 = 910835) (by norm_num)
theorem B12954097 : Blo 2243435 12954097 := bstep (se 2 (by rfl) ⟨4857786, by rfl⟩ : syracuseStep 12954097 = 9715573) B9715573
theorem B17272129 : Blo 2243435 17272129 := bstep (se 2 (by rfl) ⟨6477048, by rfl⟩ : syracuseStep 17272129 = 12954097) B12954097
theorem B23029505 : Blo 2243435 23029505 := bstep (se 2 (by rfl) ⟨8636064, by rfl⟩ : syracuseStep 23029505 = 17272129) B17272129
theorem B15353003 : Blo 2243435 15353003 := bstep (se 1 (by rfl) ⟨11514752, by rfl⟩ : syracuseStep 15353003 = 23029505) B23029505
theorem B10235335 : Blo 2243435 10235335 := bstep (se 1 (by rfl) ⟨7676501, by rfl⟩ : syracuseStep 10235335 = 15353003) B15353003
theorem B13647113 : Blo 2243435 13647113 := bstep (se 2 (by rfl) ⟨5117667, by rfl⟩ : syracuseStep 13647113 = 10235335) B10235335
theorem B9098075 : Blo 2243435 9098075 := bstep (se 1 (by rfl) ⟨6823556, by rfl⟩ : syracuseStep 9098075 = 13647113) B13647113
theorem B6065383 : Blo 2243435 6065383 := bstep (se 1 (by rfl) ⟨4549037, by rfl⟩ : syracuseStep 6065383 = 9098075) B9098075
theorem B8087177 : Blo 2243435 8087177 := bstep (se 2 (by rfl) ⟨3032691, by rfl⟩ : syracuseStep 8087177 = 6065383) B6065383
theorem B5391451 : Blo 2243435 5391451 := bstep (se 1 (by rfl) ⟨4043588, by rfl⟩ : syracuseStep 5391451 = 8087177) B8087177
theorem B7188601 : Blo 2243435 7188601 := bstep (se 2 (by rfl) ⟨2695725, by rfl⟩ : syracuseStep 7188601 = 5391451) B5391451
theorem B9584801 : Blo 2243435 9584801 := bstep (se 2 (by rfl) ⟨3594300, by rfl⟩ : syracuseStep 9584801 = 7188601) B7188601
theorem B6389867 : Blo 2243435 6389867 := bstep (se 1 (by rfl) ⟨4792400, by rfl⟩ : syracuseStep 6389867 = 9584801) B9584801
theorem B17039645 : Blo 2243435 17039645 := bstep (se 3 (by rfl) ⟨3194933, by rfl⟩ : syracuseStep 17039645 = 6389867) B6389867
theorem B11359763 : Blo 2243435 11359763 := bstep (se 1 (by rfl) ⟨8519822, by rfl⟩ : syracuseStep 11359763 = 17039645) B17039645
theorem B7573175 : Blo 2243435 7573175 := bstep (se 1 (by rfl) ⟨5679881, by rfl⟩ : syracuseStep 7573175 = 11359763) B11359763
theorem B5048783 : Blo 2243435 5048783 := bstep (se 1 (by rfl) ⟨3786587, by rfl⟩ : syracuseStep 5048783 = 7573175) B7573175
theorem B3365855 : Blo 2243435 3365855 := bstep (se 1 (by rfl) ⟨2524391, by rfl⟩ : syracuseStep 3365855 = 5048783) B5048783
theorem B2243903 : Blo 2243435 2243903 := bstep (se 1 (by rfl) ⟨1682927, by rfl⟩ : syracuseStep 2243903 = 3365855) B3365855
theorem B3365861 : Blo 2243435 3365861 := bbase (se 4 (by rfl) ⟨315549, by rfl⟩ : syracuseStep 3365861 = 631099) (by norm_num)
theorem B2243907 : Blo 2243435 2243907 := bstep (se 1 (by rfl) ⟨1682930, by rfl⟩ : syracuseStep 2243907 = 3365861) B3365861
theorem B9584837 : Blo 2243435 9584837 := bbase (se 4 (by rfl) ⟨898578, by rfl⟩ : syracuseStep 9584837 = 1797157) (by norm_num)
theorem B6389891 : Blo 2243435 6389891 := bstep (se 1 (by rfl) ⟨4792418, by rfl⟩ : syracuseStep 6389891 = 9584837) B9584837
theorem B4259927 : Blo 2243435 4259927 := bstep (se 1 (by rfl) ⟨3194945, by rfl⟩ : syracuseStep 4259927 = 6389891) B6389891
theorem B2839951 : Blo 2243435 2839951 := bstep (se 1 (by rfl) ⟨2129963, by rfl⟩ : syracuseStep 2839951 = 4259927) B4259927
theorem B3786601 : Blo 2243435 3786601 := bstep (se 2 (by rfl) ⟨1419975, by rfl⟩ : syracuseStep 3786601 = 2839951) B2839951
theorem B5048801 : Blo 2243435 5048801 := bstep (se 2 (by rfl) ⟨1893300, by rfl⟩ : syracuseStep 5048801 = 3786601) B3786601
theorem B3365867 : Blo 2243435 3365867 := bstep (se 1 (by rfl) ⟨2524400, by rfl⟩ : syracuseStep 3365867 = 5048801) B5048801
theorem B2243911 : Blo 2243435 2243911 := bstep (se 1 (by rfl) ⟨1682933, by rfl⟩ : syracuseStep 2243911 = 3365867) B3365867
theorem B2524405 : Blo 2243435 2524405 := bbase (se 5 (by rfl) ⟨118331, by rfl⟩ : syracuseStep 2524405 = 236663) (by norm_num)
theorem B3365873 : Blo 2243435 3365873 := bstep (se 2 (by rfl) ⟨1262202, by rfl⟩ : syracuseStep 3365873 = 2524405) B2524405
theorem B2243915 : Blo 2243435 2243915 := bstep (se 1 (by rfl) ⟨1682936, by rfl⟩ : syracuseStep 2243915 = 3365873) B3365873
theorem B2839961 : Blo 2243435 2839961 := bbase (se 2 (by rfl) ⟨1064985, by rfl⟩ : syracuseStep 2839961 = 2129971) (by norm_num)
theorem B7573229 : Blo 2243435 7573229 := bstep (se 3 (by rfl) ⟨1419980, by rfl⟩ : syracuseStep 7573229 = 2839961) B2839961
theorem B5048819 : Blo 2243435 5048819 := bstep (se 1 (by rfl) ⟨3786614, by rfl⟩ : syracuseStep 5048819 = 7573229) B7573229
theorem B3365879 : Blo 2243435 3365879 := bstep (se 1 (by rfl) ⟨2524409, by rfl⟩ : syracuseStep 3365879 = 5048819) B5048819
theorem B2243919 : Blo 2243435 2243919 := bstep (se 1 (by rfl) ⟨1682939, by rfl⟩ : syracuseStep 2243919 = 3365879) B3365879
theorem B3365885 : Blo 2243435 3365885 := bbase (se 3 (by rfl) ⟨631103, by rfl⟩ : syracuseStep 3365885 = 1262207) (by norm_num)
theorem B2243923 : Blo 2243435 2243923 := bstep (se 1 (by rfl) ⟨1682942, by rfl⟩ : syracuseStep 2243923 = 3365885) B3365885
theorem B5048837 : Blo 2243435 5048837 := bbase (se 4 (by rfl) ⟨473328, by rfl⟩ : syracuseStep 5048837 = 946657) (by norm_num)
theorem B3365891 : Blo 2243435 3365891 := bstep (se 1 (by rfl) ⟨2524418, by rfl⟩ : syracuseStep 3365891 = 5048837) B5048837
theorem B2243927 : Blo 2243435 2243927 := bstep (se 1 (by rfl) ⟨1682945, by rfl⟩ : syracuseStep 2243927 = 3365891) B3365891
theorem B4259965 : Blo 2243435 4259965 := bbase (se 3 (by rfl) ⟨798743, by rfl⟩ : syracuseStep 4259965 = 1597487) (by norm_num)
theorem B5679953 : Blo 2243435 5679953 := bstep (se 2 (by rfl) ⟨2129982, by rfl⟩ : syracuseStep 5679953 = 4259965) B4259965
theorem B3786635 : Blo 2243435 3786635 := bstep (se 1 (by rfl) ⟨2839976, by rfl⟩ : syracuseStep 3786635 = 5679953) B5679953
theorem B2524423 : Blo 2243435 2524423 := bstep (se 1 (by rfl) ⟨1893317, by rfl⟩ : syracuseStep 2524423 = 3786635) B3786635
theorem B3365897 : Blo 2243435 3365897 := bstep (se 2 (by rfl) ⟨1262211, by rfl⟩ : syracuseStep 3365897 = 2524423) B2524423
theorem B2243931 : Blo 2243435 2243931 := bstep (se 1 (by rfl) ⟨1682948, by rfl⟩ : syracuseStep 2243931 = 3365897) B3365897
theorem B11359925 : Blo 2243435 11359925 := bbase (se 5 (by rfl) ⟨532496, by rfl⟩ : syracuseStep 11359925 = 1064993) (by norm_num)
theorem B7573283 : Blo 2243435 7573283 := bstep (se 1 (by rfl) ⟨5679962, by rfl⟩ : syracuseStep 7573283 = 11359925) B11359925
theorem B5048855 : Blo 2243435 5048855 := bstep (se 1 (by rfl) ⟨3786641, by rfl⟩ : syracuseStep 5048855 = 7573283) B7573283
theorem B3365903 : Blo 2243435 3365903 := bstep (se 1 (by rfl) ⟨2524427, by rfl⟩ : syracuseStep 3365903 = 5048855) B5048855
theorem B2243935 : Blo 2243435 2243935 := bstep (se 1 (by rfl) ⟨1682951, by rfl⟩ : syracuseStep 2243935 = 3365903) B3365903
theorem B3365909 : Blo 2243435 3365909 := bbase (se 6 (by rfl) ⟨78888, by rfl⟩ : syracuseStep 3365909 = 157777) (by norm_num)
theorem B2243939 : Blo 2243435 2243939 := bstep (se 1 (by rfl) ⟨1682954, by rfl⟩ : syracuseStep 2243939 = 3365909) B3365909
theorem B14573621 : Blo 2243435 14573621 := bbase (se 5 (by rfl) ⟨683138, by rfl⟩ : syracuseStep 14573621 = 1366277) (by norm_num)
theorem B38862989 : Blo 2243435 38862989 := bstep (se 3 (by rfl) ⟨7286810, by rfl⟩ : syracuseStep 38862989 = 14573621) B14573621
theorem B25908659 : Blo 2243435 25908659 := bstep (se 1 (by rfl) ⟨19431494, by rfl⟩ : syracuseStep 25908659 = 38862989) B38862989
theorem B17272439 : Blo 2243435 17272439 := bstep (se 1 (by rfl) ⟨12954329, by rfl⟩ : syracuseStep 17272439 = 25908659) B25908659
theorem B11514959 : Blo 2243435 11514959 := bstep (se 1 (by rfl) ⟨8636219, by rfl⟩ : syracuseStep 11514959 = 17272439) B17272439
theorem B7676639 : Blo 2243435 7676639 := bstep (se 1 (by rfl) ⟨5757479, by rfl⟩ : syracuseStep 7676639 = 11514959) B11514959
theorem B5117759 : Blo 2243435 5117759 := bstep (se 1 (by rfl) ⟨3838319, by rfl⟩ : syracuseStep 5117759 = 7676639) B7676639
theorem B3411839 : Blo 2243435 3411839 := bstep (se 1 (by rfl) ⟨2558879, by rfl⟩ : syracuseStep 3411839 = 5117759) B5117759
theorem B9098237 : Blo 2243435 9098237 := bstep (se 3 (by rfl) ⟨1705919, by rfl⟩ : syracuseStep 9098237 = 3411839) B3411839
theorem B6065491 : Blo 2243435 6065491 := bstep (se 1 (by rfl) ⟨4549118, by rfl⟩ : syracuseStep 6065491 = 9098237) B9098237
theorem B8087321 : Blo 2243435 8087321 := bstep (se 2 (by rfl) ⟨3032745, by rfl⟩ : syracuseStep 8087321 = 6065491) B6065491
theorem B21566189 : Blo 2243435 21566189 := bstep (se 3 (by rfl) ⟨4043660, by rfl⟩ : syracuseStep 21566189 = 8087321) B8087321
theorem B14377459 : Blo 2243435 14377459 := bstep (se 1 (by rfl) ⟨10783094, by rfl⟩ : syracuseStep 14377459 = 21566189) B21566189
theorem B19169945 : Blo 2243435 19169945 := bstep (se 2 (by rfl) ⟨7188729, by rfl⟩ : syracuseStep 19169945 = 14377459) B14377459
theorem B12779963 : Blo 2243435 12779963 := bstep (se 1 (by rfl) ⟨9584972, by rfl⟩ : syracuseStep 12779963 = 19169945) B19169945
theorem B8519975 : Blo 2243435 8519975 := bstep (se 1 (by rfl) ⟨6389981, by rfl⟩ : syracuseStep 8519975 = 12779963) B12779963
theorem B5679983 : Blo 2243435 5679983 := bstep (se 1 (by rfl) ⟨4259987, by rfl⟩ : syracuseStep 5679983 = 8519975) B8519975
theorem B3786655 : Blo 2243435 3786655 := bstep (se 1 (by rfl) ⟨2839991, by rfl⟩ : syracuseStep 3786655 = 5679983) B5679983
theorem B5048873 : Blo 2243435 5048873 := bstep (se 2 (by rfl) ⟨1893327, by rfl⟩ : syracuseStep 5048873 = 3786655) B3786655
theorem B3365915 : Blo 2243435 3365915 := bstep (se 1 (by rfl) ⟨2524436, by rfl⟩ : syracuseStep 3365915 = 5048873) B5048873
theorem B2243943 : Blo 2243435 2243943 := bstep (se 1 (by rfl) ⟨1682957, by rfl⟩ : syracuseStep 2243943 = 3365915) B3365915
theorem B2524441 : Blo 2243435 2524441 := bbase (se 2 (by rfl) ⟨946665, by rfl⟩ : syracuseStep 2524441 = 1893331) (by norm_num)
theorem B3365921 : Blo 2243435 3365921 := bstep (se 2 (by rfl) ⟨1262220, by rfl⟩ : syracuseStep 3365921 = 2524441) B2524441
theorem B2243947 : Blo 2243435 2243947 := bstep (se 1 (by rfl) ⟨1682960, by rfl⟩ : syracuseStep 2243947 = 3365921) B3365921
theorem B8520005 : Blo 2243435 8520005 := bbase (se 4 (by rfl) ⟨798750, by rfl⟩ : syracuseStep 8520005 = 1597501) (by norm_num)
theorem B5680003 : Blo 2243435 5680003 := bstep (se 1 (by rfl) ⟨4260002, by rfl⟩ : syracuseStep 5680003 = 8520005) B8520005
theorem B7573337 : Blo 2243435 7573337 := bstep (se 2 (by rfl) ⟨2840001, by rfl⟩ : syracuseStep 7573337 = 5680003) B5680003
theorem B5048891 : Blo 2243435 5048891 := bstep (se 1 (by rfl) ⟨3786668, by rfl⟩ : syracuseStep 5048891 = 7573337) B7573337
theorem B3365927 : Blo 2243435 3365927 := bstep (se 1 (by rfl) ⟨2524445, by rfl⟩ : syracuseStep 3365927 = 5048891) B5048891
theorem B2243951 : Blo 2243435 2243951 := bstep (se 1 (by rfl) ⟨1682963, by rfl⟩ : syracuseStep 2243951 = 3365927) B3365927
theorem B3365933 : Blo 2243435 3365933 := bbase (se 3 (by rfl) ⟨631112, by rfl⟩ : syracuseStep 3365933 = 1262225) (by norm_num)
theorem B2243955 : Blo 2243435 2243955 := bstep (se 1 (by rfl) ⟨1682966, by rfl⟩ : syracuseStep 2243955 = 3365933) B3365933
theorem B5048909 : Blo 2243435 5048909 := bbase (se 3 (by rfl) ⟨946670, by rfl⟩ : syracuseStep 5048909 = 1893341) (by norm_num)
theorem B3365939 : Blo 2243435 3365939 := bstep (se 1 (by rfl) ⟨2524454, by rfl⟩ : syracuseStep 3365939 = 5048909) B5048909
theorem B2243959 : Blo 2243435 2243959 := bstep (se 1 (by rfl) ⟨1682969, by rfl⟩ : syracuseStep 2243959 = 3365939) B3365939
theorem B2840017 : Blo 2243435 2840017 := bbase (se 2 (by rfl) ⟨1065006, by rfl⟩ : syracuseStep 2840017 = 2130013) (by norm_num)
theorem B3786689 : Blo 2243435 3786689 := bstep (se 2 (by rfl) ⟨1420008, by rfl⟩ : syracuseStep 3786689 = 2840017) B2840017
theorem B2524459 : Blo 2243435 2524459 := bstep (se 1 (by rfl) ⟨1893344, by rfl⟩ : syracuseStep 2524459 = 3786689) B3786689
theorem B3365945 : Blo 2243435 3365945 := bstep (se 2 (by rfl) ⟨1262229, by rfl⟩ : syracuseStep 3365945 = 2524459) B2524459
theorem B2243963 : Blo 2243435 2243963 := bstep (se 1 (by rfl) ⟨1682972, by rfl⟩ : syracuseStep 2243963 = 3365945) B3365945
theorem B5391605 : Blo 2243435 5391605 := bbase (se 5 (by rfl) ⟨252731, by rfl⟩ : syracuseStep 5391605 = 505463) (by norm_num)
theorem B3594403 : Blo 2243435 3594403 := bstep (se 1 (by rfl) ⟨2695802, by rfl⟩ : syracuseStep 3594403 = 5391605) B5391605
theorem B4792537 : Blo 2243435 4792537 := bstep (se 2 (by rfl) ⟨1797201, by rfl⟩ : syracuseStep 4792537 = 3594403) B3594403
theorem B25560197 : Blo 2243435 25560197 := bstep (se 4 (by rfl) ⟨2396268, by rfl⟩ : syracuseStep 25560197 = 4792537) B4792537
theorem B17040131 : Blo 2243435 17040131 := bstep (se 1 (by rfl) ⟨12780098, by rfl⟩ : syracuseStep 17040131 = 25560197) B25560197
theorem B11360087 : Blo 2243435 11360087 := bstep (se 1 (by rfl) ⟨8520065, by rfl⟩ : syracuseStep 11360087 = 17040131) B17040131
theorem B7573391 : Blo 2243435 7573391 := bstep (se 1 (by rfl) ⟨5680043, by rfl⟩ : syracuseStep 7573391 = 11360087) B11360087
theorem B5048927 : Blo 2243435 5048927 := bstep (se 1 (by rfl) ⟨3786695, by rfl⟩ : syracuseStep 5048927 = 7573391) B7573391
theorem B3365951 : Blo 2243435 3365951 := bstep (se 1 (by rfl) ⟨2524463, by rfl⟩ : syracuseStep 3365951 = 5048927) B5048927
theorem B2243967 : Blo 2243435 2243967 := bstep (se 1 (by rfl) ⟨1682975, by rfl⟩ : syracuseStep 2243967 = 3365951) B3365951
theorem B3365957 : Blo 2243435 3365957 := bbase (se 4 (by rfl) ⟨315558, by rfl⟩ : syracuseStep 3365957 = 631117) (by norm_num)
theorem B2243971 : Blo 2243435 2243971 := bstep (se 1 (by rfl) ⟨1682978, by rfl⟩ : syracuseStep 2243971 = 3365957) B3365957
theorem B3786709 : Blo 2243435 3786709 := bbase (se 7 (by rfl) ⟨44375, by rfl⟩ : syracuseStep 3786709 = 88751) (by norm_num)
theorem B5048945 : Blo 2243435 5048945 := bstep (se 2 (by rfl) ⟨1893354, by rfl⟩ : syracuseStep 5048945 = 3786709) B3786709
theorem B3365963 : Blo 2243435 3365963 := bstep (se 1 (by rfl) ⟨2524472, by rfl⟩ : syracuseStep 3365963 = 5048945) B5048945
theorem B2243975 : Blo 2243435 2243975 := bstep (se 1 (by rfl) ⟨1682981, by rfl⟩ : syracuseStep 2243975 = 3365963) B3365963
theorem B2524477 : Blo 2243435 2524477 := bbase (se 3 (by rfl) ⟨473339, by rfl⟩ : syracuseStep 2524477 = 946679) (by norm_num)
theorem B3365969 : Blo 2243435 3365969 := bstep (se 2 (by rfl) ⟨1262238, by rfl⟩ : syracuseStep 3365969 = 2524477) B2524477
theorem B2243979 : Blo 2243435 2243979 := bstep (se 1 (by rfl) ⟨1682984, by rfl⟩ : syracuseStep 2243979 = 3365969) B3365969
theorem B7573445 : Blo 2243435 7573445 := bbase (se 4 (by rfl) ⟨710010, by rfl⟩ : syracuseStep 7573445 = 1420021) (by norm_num)
theorem B5048963 : Blo 2243435 5048963 := bstep (se 1 (by rfl) ⟨3786722, by rfl⟩ : syracuseStep 5048963 = 7573445) B7573445
theorem B3365975 : Blo 2243435 3365975 := bstep (se 1 (by rfl) ⟨2524481, by rfl⟩ : syracuseStep 3365975 = 5048963) B5048963
theorem B2243983 : Blo 2243435 2243983 := bstep (se 1 (by rfl) ⟨1682987, by rfl⟩ : syracuseStep 2243983 = 3365975) B3365975
theorem B3365981 : Blo 2243435 3365981 := bbase (se 3 (by rfl) ⟨631121, by rfl⟩ : syracuseStep 3365981 = 1262243) (by norm_num)
theorem B2243987 : Blo 2243435 2243987 := bstep (se 1 (by rfl) ⟨1682990, by rfl⟩ : syracuseStep 2243987 = 3365981) B3365981
theorem B5048981 : Blo 2243435 5048981 := bbase (se 6 (by rfl) ⟨118335, by rfl⟩ : syracuseStep 5048981 = 236671) (by norm_num)
theorem B3365987 : Blo 2243435 3365987 := bstep (se 1 (by rfl) ⟨2524490, by rfl⟩ : syracuseStep 3365987 = 5048981) B5048981
theorem B2243991 : Blo 2243435 2243991 := bstep (se 1 (by rfl) ⟨1682993, by rfl⟩ : syracuseStep 2243991 = 3365987) B3365987
theorem B2695837 : Blo 2243435 2695837 := bbase (se 3 (by rfl) ⟨505469, by rfl⟩ : syracuseStep 2695837 = 1010939) (by norm_num)
theorem B3594449 : Blo 2243435 3594449 := bstep (se 2 (by rfl) ⟨1347918, by rfl⟩ : syracuseStep 3594449 = 2695837) B2695837
theorem B2396299 : Blo 2243435 2396299 := bstep (se 1 (by rfl) ⟨1797224, by rfl⟩ : syracuseStep 2396299 = 3594449) B3594449
theorem B3195065 : Blo 2243435 3195065 := bstep (se 2 (by rfl) ⟨1198149, by rfl⟩ : syracuseStep 3195065 = 2396299) B2396299
theorem B8520173 : Blo 2243435 8520173 := bstep (se 3 (by rfl) ⟨1597532, by rfl⟩ : syracuseStep 8520173 = 3195065) B3195065
theorem B5680115 : Blo 2243435 5680115 := bstep (se 1 (by rfl) ⟨4260086, by rfl⟩ : syracuseStep 5680115 = 8520173) B8520173
theorem B3786743 : Blo 2243435 3786743 := bstep (se 1 (by rfl) ⟨2840057, by rfl⟩ : syracuseStep 3786743 = 5680115) B5680115
theorem B2524495 : Blo 2243435 2524495 := bstep (se 1 (by rfl) ⟨1893371, by rfl⟩ : syracuseStep 2524495 = 3786743) B3786743
theorem B3365993 : Blo 2243435 3365993 := bstep (se 2 (by rfl) ⟨1262247, by rfl⟩ : syracuseStep 3365993 = 2524495) B2524495
theorem B2243995 : Blo 2243435 2243995 := bstep (se 1 (by rfl) ⟨1682996, by rfl⟩ : syracuseStep 2243995 = 3365993) B3365993
theorem B3032821 : Blo 2243435 3032821 := bbase (se 5 (by rfl) ⟨142163, by rfl⟩ : syracuseStep 3032821 = 284327) (by norm_num)
theorem B16175045 : Blo 2243435 16175045 := bstep (se 4 (by rfl) ⟨1516410, by rfl⟩ : syracuseStep 16175045 = 3032821) B3032821
theorem B10783363 : Blo 2243435 10783363 := bstep (se 1 (by rfl) ⟨8087522, by rfl⟩ : syracuseStep 10783363 = 16175045) B16175045
theorem B14377817 : Blo 2243435 14377817 := bstep (se 2 (by rfl) ⟨5391681, by rfl⟩ : syracuseStep 14377817 = 10783363) B10783363
theorem B9585211 : Blo 2243435 9585211 := bstep (se 1 (by rfl) ⟨7188908, by rfl⟩ : syracuseStep 9585211 = 14377817) B14377817
theorem B12780281 : Blo 2243435 12780281 := bstep (se 2 (by rfl) ⟨4792605, by rfl⟩ : syracuseStep 12780281 = 9585211) B9585211
theorem B8520187 : Blo 2243435 8520187 := bstep (se 1 (by rfl) ⟨6390140, by rfl⟩ : syracuseStep 8520187 = 12780281) B12780281
theorem B11360249 : Blo 2243435 11360249 := bstep (se 2 (by rfl) ⟨4260093, by rfl⟩ : syracuseStep 11360249 = 8520187) B8520187
theorem B7573499 : Blo 2243435 7573499 := bstep (se 1 (by rfl) ⟨5680124, by rfl⟩ : syracuseStep 7573499 = 11360249) B11360249
theorem B5048999 : Blo 2243435 5048999 := bstep (se 1 (by rfl) ⟨3786749, by rfl⟩ : syracuseStep 5048999 = 7573499) B7573499
theorem B3365999 : Blo 2243435 3365999 := bstep (se 1 (by rfl) ⟨2524499, by rfl⟩ : syracuseStep 3365999 = 5048999) B5048999
theorem B2243999 : Blo 2243435 2243999 := bstep (se 1 (by rfl) ⟨1682999, by rfl⟩ : syracuseStep 2243999 = 3365999) B3365999
theorem B3366005 : Blo 2243435 3366005 := bbase (se 5 (by rfl) ⟨157781, by rfl⟩ : syracuseStep 3366005 = 315563) (by norm_num)
theorem B2244003 : Blo 2243435 2244003 := bstep (se 1 (by rfl) ⟨1683002, by rfl⟩ : syracuseStep 2244003 = 3366005) B3366005
theorem B4260109 : Blo 2243435 4260109 := bbase (se 3 (by rfl) ⟨798770, by rfl⟩ : syracuseStep 4260109 = 1597541) (by norm_num)
theorem B5680145 : Blo 2243435 5680145 := bstep (se 2 (by rfl) ⟨2130054, by rfl⟩ : syracuseStep 5680145 = 4260109) B4260109
theorem B3786763 : Blo 2243435 3786763 := bstep (se 1 (by rfl) ⟨2840072, by rfl⟩ : syracuseStep 3786763 = 5680145) B5680145
theorem B5049017 : Blo 2243435 5049017 := bstep (se 2 (by rfl) ⟨1893381, by rfl⟩ : syracuseStep 5049017 = 3786763) B3786763
theorem B3366011 : Blo 2243435 3366011 := bstep (se 1 (by rfl) ⟨2524508, by rfl⟩ : syracuseStep 3366011 = 5049017) B5049017
theorem B2244007 : Blo 2243435 2244007 := bstep (se 1 (by rfl) ⟨1683005, by rfl⟩ : syracuseStep 2244007 = 3366011) B3366011
theorem B2524513 : Blo 2243435 2524513 := bbase (se 2 (by rfl) ⟨946692, by rfl⟩ : syracuseStep 2524513 = 1893385) (by norm_num)
theorem B3366017 : Blo 2243435 3366017 := bstep (se 2 (by rfl) ⟨1262256, by rfl⟩ : syracuseStep 3366017 = 2524513) B2524513
theorem B2244011 : Blo 2243435 2244011 := bstep (se 1 (by rfl) ⟨1683008, by rfl⟩ : syracuseStep 2244011 = 3366017) B3366017
theorem B5680165 : Blo 2243435 5680165 := bbase (se 4 (by rfl) ⟨532515, by rfl⟩ : syracuseStep 5680165 = 1065031) (by norm_num)
theorem B7573553 : Blo 2243435 7573553 := bstep (se 2 (by rfl) ⟨2840082, by rfl⟩ : syracuseStep 7573553 = 5680165) B5680165
theorem B5049035 : Blo 2243435 5049035 := bstep (se 1 (by rfl) ⟨3786776, by rfl⟩ : syracuseStep 5049035 = 7573553) B7573553
theorem B3366023 : Blo 2243435 3366023 := bstep (se 1 (by rfl) ⟨2524517, by rfl⟩ : syracuseStep 3366023 = 5049035) B5049035
theorem B2244015 : Blo 2243435 2244015 := bstep (se 1 (by rfl) ⟨1683011, by rfl⟩ : syracuseStep 2244015 = 3366023) B3366023
theorem B3366029 : Blo 2243435 3366029 := bbase (se 3 (by rfl) ⟨631130, by rfl⟩ : syracuseStep 3366029 = 1262261) (by norm_num)
theorem B2244019 : Blo 2243435 2244019 := bstep (se 1 (by rfl) ⟨1683014, by rfl⟩ : syracuseStep 2244019 = 3366029) B3366029
theorem B5049053 : Blo 2243435 5049053 := bbase (se 3 (by rfl) ⟨946697, by rfl⟩ : syracuseStep 5049053 = 1893395) (by norm_num)
theorem B3366035 : Blo 2243435 3366035 := bstep (se 1 (by rfl) ⟨2524526, by rfl⟩ : syracuseStep 3366035 = 5049053) B5049053
theorem B2244023 : Blo 2243435 2244023 := bstep (se 1 (by rfl) ⟨1683017, by rfl⟩ : syracuseStep 2244023 = 3366035) B3366035
theorem B3786797 : Blo 2243435 3786797 := bbase (se 3 (by rfl) ⟨710024, by rfl⟩ : syracuseStep 3786797 = 1420049) (by norm_num)
theorem B2524531 : Blo 2243435 2524531 := bstep (se 1 (by rfl) ⟨1893398, by rfl⟩ : syracuseStep 2524531 = 3786797) B3786797
theorem B3366041 : Blo 2243435 3366041 := bstep (se 2 (by rfl) ⟨1262265, by rfl⟩ : syracuseStep 3366041 = 2524531) B2524531
theorem B2244027 : Blo 2243435 2244027 := bstep (se 1 (by rfl) ⟨1683020, by rfl⟩ : syracuseStep 2244027 = 3366041) B3366041
theorem B32350549 : Blo 2243435 32350549 := bbase (se 10 (by rfl) ⟨47388, by rfl⟩ : syracuseStep 32350549 = 94777) (by norm_num)
theorem B43134065 : Blo 2243435 43134065 := bstep (se 2 (by rfl) ⟨16175274, by rfl⟩ : syracuseStep 43134065 = 32350549) B32350549
theorem B28756043 : Blo 2243435 28756043 := bstep (se 1 (by rfl) ⟨21567032, by rfl⟩ : syracuseStep 28756043 = 43134065) B43134065
theorem B19170695 : Blo 2243435 19170695 := bstep (se 1 (by rfl) ⟨14378021, by rfl⟩ : syracuseStep 19170695 = 28756043) B28756043
theorem B12780463 : Blo 2243435 12780463 := bstep (se 1 (by rfl) ⟨9585347, by rfl⟩ : syracuseStep 12780463 = 19170695) B19170695
theorem B17040617 : Blo 2243435 17040617 := bstep (se 2 (by rfl) ⟨6390231, by rfl⟩ : syracuseStep 17040617 = 12780463) B12780463
theorem B11360411 : Blo 2243435 11360411 := bstep (se 1 (by rfl) ⟨8520308, by rfl⟩ : syracuseStep 11360411 = 17040617) B17040617
theorem B7573607 : Blo 2243435 7573607 := bstep (se 1 (by rfl) ⟨5680205, by rfl⟩ : syracuseStep 7573607 = 11360411) B11360411
theorem B5049071 : Blo 2243435 5049071 := bstep (se 1 (by rfl) ⟨3786803, by rfl⟩ : syracuseStep 5049071 = 7573607) B7573607
theorem B3366047 : Blo 2243435 3366047 := bstep (se 1 (by rfl) ⟨2524535, by rfl⟩ : syracuseStep 3366047 = 5049071) B5049071
theorem B2244031 : Blo 2243435 2244031 := bstep (se 1 (by rfl) ⟨1683023, by rfl⟩ : syracuseStep 2244031 = 3366047) B3366047
theorem B3366053 : Blo 2243435 3366053 := bbase (se 4 (by rfl) ⟨315567, by rfl⟩ : syracuseStep 3366053 = 631135) (by norm_num)
theorem B2244035 : Blo 2243435 2244035 := bstep (se 1 (by rfl) ⟨1683026, by rfl⟩ : syracuseStep 2244035 = 3366053) B3366053
theorem B2840113 : Blo 2243435 2840113 := bbase (se 2 (by rfl) ⟨1065042, by rfl⟩ : syracuseStep 2840113 = 2130085) (by norm_num)
theorem B3786817 : Blo 2243435 3786817 := bstep (se 2 (by rfl) ⟨1420056, by rfl⟩ : syracuseStep 3786817 = 2840113) B2840113
theorem B5049089 : Blo 2243435 5049089 := bstep (se 2 (by rfl) ⟨1893408, by rfl⟩ : syracuseStep 5049089 = 3786817) B3786817
theorem B3366059 : Blo 2243435 3366059 := bstep (se 1 (by rfl) ⟨2524544, by rfl⟩ : syracuseStep 3366059 = 5049089) B5049089
theorem B2244039 : Blo 2243435 2244039 := bstep (se 1 (by rfl) ⟨1683029, by rfl⟩ : syracuseStep 2244039 = 3366059) B3366059
theorem B2524549 : Blo 2243435 2524549 := bbase (se 4 (by rfl) ⟨236676, by rfl⟩ : syracuseStep 2524549 = 473353) (by norm_num)
theorem B3366065 : Blo 2243435 3366065 := bstep (se 2 (by rfl) ⟨1262274, by rfl⟩ : syracuseStep 3366065 = 2524549) B2524549
theorem B2244043 : Blo 2243435 2244043 := bstep (se 1 (by rfl) ⟨1683032, by rfl⟩ : syracuseStep 2244043 = 3366065) B3366065
theorem B4792709 : Blo 2243435 4792709 := bbase (se 4 (by rfl) ⟨449316, by rfl⟩ : syracuseStep 4792709 = 898633) (by norm_num)
theorem B3195139 : Blo 2243435 3195139 := bstep (se 1 (by rfl) ⟨2396354, by rfl⟩ : syracuseStep 3195139 = 4792709) B4792709
theorem B4260185 : Blo 2243435 4260185 := bstep (se 2 (by rfl) ⟨1597569, by rfl⟩ : syracuseStep 4260185 = 3195139) B3195139
theorem B2840123 : Blo 2243435 2840123 := bstep (se 1 (by rfl) ⟨2130092, by rfl⟩ : syracuseStep 2840123 = 4260185) B4260185
theorem B7573661 : Blo 2243435 7573661 := bstep (se 3 (by rfl) ⟨1420061, by rfl⟩ : syracuseStep 7573661 = 2840123) B2840123
theorem B5049107 : Blo 2243435 5049107 := bstep (se 1 (by rfl) ⟨3786830, by rfl⟩ : syracuseStep 5049107 = 7573661) B7573661
theorem B3366071 : Blo 2243435 3366071 := bstep (se 1 (by rfl) ⟨2524553, by rfl⟩ : syracuseStep 3366071 = 5049107) B5049107
theorem B2244047 : Blo 2243435 2244047 := bstep (se 1 (by rfl) ⟨1683035, by rfl⟩ : syracuseStep 2244047 = 3366071) B3366071
theorem B3366077 : Blo 2243435 3366077 := bbase (se 3 (by rfl) ⟨631139, by rfl⟩ : syracuseStep 3366077 = 1262279) (by norm_num)
theorem B2244051 : Blo 2243435 2244051 := bstep (se 1 (by rfl) ⟨1683038, by rfl⟩ : syracuseStep 2244051 = 3366077) B3366077
theorem B5049125 : Blo 2243435 5049125 := bbase (se 4 (by rfl) ⟨473355, by rfl⟩ : syracuseStep 5049125 = 946711) (by norm_num)
theorem B3366083 : Blo 2243435 3366083 := bstep (se 1 (by rfl) ⟨2524562, by rfl⟩ : syracuseStep 3366083 = 5049125) B5049125
theorem B2244055 : Blo 2243435 2244055 := bstep (se 1 (by rfl) ⟨1683041, by rfl⟩ : syracuseStep 2244055 = 3366083) B3366083
theorem B5680277 : Blo 2243435 5680277 := bbase (se 6 (by rfl) ⟨133131, by rfl⟩ : syracuseStep 5680277 = 266263) (by norm_num)
theorem B3786851 : Blo 2243435 3786851 := bstep (se 1 (by rfl) ⟨2840138, by rfl⟩ : syracuseStep 3786851 = 5680277) B5680277
theorem B2524567 : Blo 2243435 2524567 := bstep (se 1 (by rfl) ⟨1893425, by rfl⟩ : syracuseStep 2524567 = 3786851) B3786851
theorem B3366089 : Blo 2243435 3366089 := bstep (se 2 (by rfl) ⟨1262283, by rfl⟩ : syracuseStep 3366089 = 2524567) B2524567
theorem B2244059 : Blo 2243435 2244059 := bstep (se 1 (by rfl) ⟨1683044, by rfl⟩ : syracuseStep 2244059 = 3366089) B3366089
theorem B3594557 : Blo 2243435 3594557 := bbase (se 3 (by rfl) ⟨673979, by rfl⟩ : syracuseStep 3594557 = 1347959) (by norm_num)
theorem B9585485 : Blo 2243435 9585485 := bstep (se 3 (by rfl) ⟨1797278, by rfl⟩ : syracuseStep 9585485 = 3594557) B3594557
theorem B6390323 : Blo 2243435 6390323 := bstep (se 1 (by rfl) ⟨4792742, by rfl⟩ : syracuseStep 6390323 = 9585485) B9585485
theorem B4260215 : Blo 2243435 4260215 := bstep (se 1 (by rfl) ⟨3195161, by rfl⟩ : syracuseStep 4260215 = 6390323) B6390323
theorem B11360573 : Blo 2243435 11360573 := bstep (se 3 (by rfl) ⟨2130107, by rfl⟩ : syracuseStep 11360573 = 4260215) B4260215
theorem B7573715 : Blo 2243435 7573715 := bstep (se 1 (by rfl) ⟨5680286, by rfl⟩ : syracuseStep 7573715 = 11360573) B11360573
theorem B5049143 : Blo 2243435 5049143 := bstep (se 1 (by rfl) ⟨3786857, by rfl⟩ : syracuseStep 5049143 = 7573715) B7573715
theorem B3366095 : Blo 2243435 3366095 := bstep (se 1 (by rfl) ⟨2524571, by rfl⟩ : syracuseStep 3366095 = 5049143) B5049143
theorem B2244063 : Blo 2243435 2244063 := bstep (se 1 (by rfl) ⟨1683047, by rfl⟩ : syracuseStep 2244063 = 3366095) B3366095
theorem B3366101 : Blo 2243435 3366101 := bbase (se 7 (by rfl) ⟨39446, by rfl⟩ : syracuseStep 3366101 = 78893) (by norm_num)
theorem B2244067 : Blo 2243435 2244067 := bstep (se 1 (by rfl) ⟨1683050, by rfl⟩ : syracuseStep 2244067 = 3366101) B3366101
theorem B3195173 : Blo 2243435 3195173 := bbase (se 4 (by rfl) ⟨299547, by rfl⟩ : syracuseStep 3195173 = 599095) (by norm_num)
theorem B8520461 : Blo 2243435 8520461 := bstep (se 3 (by rfl) ⟨1597586, by rfl⟩ : syracuseStep 8520461 = 3195173) B3195173
theorem B5680307 : Blo 2243435 5680307 := bstep (se 1 (by rfl) ⟨4260230, by rfl⟩ : syracuseStep 5680307 = 8520461) B8520461
theorem B3786871 : Blo 2243435 3786871 := bstep (se 1 (by rfl) ⟨2840153, by rfl⟩ : syracuseStep 3786871 = 5680307) B5680307
theorem B5049161 : Blo 2243435 5049161 := bstep (se 2 (by rfl) ⟨1893435, by rfl⟩ : syracuseStep 5049161 = 3786871) B3786871
theorem B3366107 : Blo 2243435 3366107 := bstep (se 1 (by rfl) ⟨2524580, by rfl⟩ : syracuseStep 3366107 = 5049161) B5049161
theorem B2244071 : Blo 2243435 2244071 := bstep (se 1 (by rfl) ⟨1683053, by rfl⟩ : syracuseStep 2244071 = 3366107) B3366107
theorem B2524585 : Blo 2243435 2524585 := bbase (se 2 (by rfl) ⟨946719, by rfl⟩ : syracuseStep 2524585 = 1893439) (by norm_num)
theorem B3366113 : Blo 2243435 3366113 := bstep (se 2 (by rfl) ⟨1262292, by rfl⟩ : syracuseStep 3366113 = 2524585) B2524585
theorem B2244075 : Blo 2243435 2244075 := bstep (se 1 (by rfl) ⟨1683056, by rfl⟩ : syracuseStep 2244075 = 3366113) B3366113
theorem B2695937 : Blo 2243435 2695937 := bbase (se 2 (by rfl) ⟨1010976, by rfl⟩ : syracuseStep 2695937 = 2021953) (by norm_num)
theorem B7189165 : Blo 2243435 7189165 := bstep (se 3 (by rfl) ⟨1347968, by rfl⟩ : syracuseStep 7189165 = 2695937) B2695937
theorem B9585553 : Blo 2243435 9585553 := bstep (se 2 (by rfl) ⟨3594582, by rfl⟩ : syracuseStep 9585553 = 7189165) B7189165
theorem B12780737 : Blo 2243435 12780737 := bstep (se 2 (by rfl) ⟨4792776, by rfl⟩ : syracuseStep 12780737 = 9585553) B9585553
theorem B8520491 : Blo 2243435 8520491 := bstep (se 1 (by rfl) ⟨6390368, by rfl⟩ : syracuseStep 8520491 = 12780737) B12780737
theorem B5680327 : Blo 2243435 5680327 := bstep (se 1 (by rfl) ⟨4260245, by rfl⟩ : syracuseStep 5680327 = 8520491) B8520491
theorem B7573769 : Blo 2243435 7573769 := bstep (se 2 (by rfl) ⟨2840163, by rfl⟩ : syracuseStep 7573769 = 5680327) B5680327
theorem B5049179 : Blo 2243435 5049179 := bstep (se 1 (by rfl) ⟨3786884, by rfl⟩ : syracuseStep 5049179 = 7573769) B7573769
theorem B3366119 : Blo 2243435 3366119 := bstep (se 1 (by rfl) ⟨2524589, by rfl⟩ : syracuseStep 3366119 = 5049179) B5049179
theorem B2244079 : Blo 2243435 2244079 := bstep (se 1 (by rfl) ⟨1683059, by rfl⟩ : syracuseStep 2244079 = 3366119) B3366119
theorem B3366125 : Blo 2243435 3366125 := bbase (se 3 (by rfl) ⟨631148, by rfl⟩ : syracuseStep 3366125 = 1262297) (by norm_num)
theorem B2244083 : Blo 2243435 2244083 := bstep (se 1 (by rfl) ⟨1683062, by rfl⟩ : syracuseStep 2244083 = 3366125) B3366125
theorem B5049197 : Blo 2243435 5049197 := bbase (se 3 (by rfl) ⟨946724, by rfl⟩ : syracuseStep 5049197 = 1893449) (by norm_num)
theorem B3366131 : Blo 2243435 3366131 := bstep (se 1 (by rfl) ⟨2524598, by rfl⟩ : syracuseStep 3366131 = 5049197) B5049197
theorem B2244087 : Blo 2243435 2244087 := bstep (se 1 (by rfl) ⟨1683065, by rfl⟩ : syracuseStep 2244087 = 3366131) B3366131
theorem B4260269 : Blo 2243435 4260269 := bbase (se 3 (by rfl) ⟨798800, by rfl⟩ : syracuseStep 4260269 = 1597601) (by norm_num)
theorem B2840179 : Blo 2243435 2840179 := bstep (se 1 (by rfl) ⟨2130134, by rfl⟩ : syracuseStep 2840179 = 4260269) B4260269
theorem B3786905 : Blo 2243435 3786905 := bstep (se 2 (by rfl) ⟨1420089, by rfl⟩ : syracuseStep 3786905 = 2840179) B2840179
theorem B2524603 : Blo 2243435 2524603 := bstep (se 1 (by rfl) ⟨1893452, by rfl⟩ : syracuseStep 2524603 = 3786905) B3786905
theorem B3366137 : Blo 2243435 3366137 := bstep (se 2 (by rfl) ⟨1262301, by rfl⟩ : syracuseStep 3366137 = 2524603) B2524603
theorem B2244091 : Blo 2243435 2244091 := bstep (se 1 (by rfl) ⟨1683068, by rfl⟩ : syracuseStep 2244091 = 3366137) B3366137
theorem B8198213 : Blo 2243435 8198213 := bbase (se 4 (by rfl) ⟨768582, by rfl⟩ : syracuseStep 8198213 = 1537165) (by norm_num)
theorem B87447605 : Blo 2243435 87447605 := bstep (se 5 (by rfl) ⟨4099106, by rfl⟩ : syracuseStep 87447605 = 8198213) B8198213
theorem B932774453 : Blo 2243435 932774453 := bstep (se 5 (by rfl) ⟨43723802, by rfl⟩ : syracuseStep 932774453 = 87447605) B87447605
theorem B621849635 : Blo 2243435 621849635 := bstep (se 1 (by rfl) ⟨466387226, by rfl⟩ : syracuseStep 621849635 = 932774453) B932774453
theorem B414566423 : Blo 2243435 414566423 := bstep (se 1 (by rfl) ⟨310924817, by rfl⟩ : syracuseStep 414566423 = 621849635) B621849635
theorem B276377615 : Blo 2243435 276377615 := bstep (se 1 (by rfl) ⟨207283211, by rfl⟩ : syracuseStep 276377615 = 414566423) B414566423
theorem B184251743 : Blo 2243435 184251743 := bstep (se 1 (by rfl) ⟨138188807, by rfl⟩ : syracuseStep 184251743 = 276377615) B276377615
theorem B122834495 : Blo 2243435 122834495 := bstep (se 1 (by rfl) ⟨92125871, by rfl⟩ : syracuseStep 122834495 = 184251743) B184251743
theorem B81889663 : Blo 2243435 81889663 := bstep (se 1 (by rfl) ⟨61417247, by rfl⟩ : syracuseStep 81889663 = 122834495) B122834495
theorem B109186217 : Blo 2243435 109186217 := bstep (se 2 (by rfl) ⟨40944831, by rfl⟩ : syracuseStep 109186217 = 81889663) B81889663
theorem B72790811 : Blo 2243435 72790811 := bstep (se 1 (by rfl) ⟨54593108, by rfl⟩ : syracuseStep 72790811 = 109186217) B109186217
theorem B48527207 : Blo 2243435 48527207 := bstep (se 1 (by rfl) ⟨36395405, by rfl⟩ : syracuseStep 48527207 = 72790811) B72790811
theorem B32351471 : Blo 2243435 32351471 := bstep (se 1 (by rfl) ⟨24263603, by rfl⟩ : syracuseStep 32351471 = 48527207) B48527207
theorem B21567647 : Blo 2243435 21567647 := bstep (se 1 (by rfl) ⟨16175735, by rfl⟩ : syracuseStep 21567647 = 32351471) B32351471
theorem B57513725 : Blo 2243435 57513725 := bstep (se 3 (by rfl) ⟨10783823, by rfl⟩ : syracuseStep 57513725 = 21567647) B21567647
theorem B38342483 : Blo 2243435 38342483 := bstep (se 1 (by rfl) ⟨28756862, by rfl⟩ : syracuseStep 38342483 = 57513725) B57513725
theorem B25561655 : Blo 2243435 25561655 := bstep (se 1 (by rfl) ⟨19171241, by rfl⟩ : syracuseStep 25561655 = 38342483) B38342483
theorem B17041103 : Blo 2243435 17041103 := bstep (se 1 (by rfl) ⟨12780827, by rfl⟩ : syracuseStep 17041103 = 25561655) B25561655
theorem B11360735 : Blo 2243435 11360735 := bstep (se 1 (by rfl) ⟨8520551, by rfl⟩ : syracuseStep 11360735 = 17041103) B17041103
theorem B7573823 : Blo 2243435 7573823 := bstep (se 1 (by rfl) ⟨5680367, by rfl⟩ : syracuseStep 7573823 = 11360735) B11360735
theorem B5049215 : Blo 2243435 5049215 := bstep (se 1 (by rfl) ⟨3786911, by rfl⟩ : syracuseStep 5049215 = 7573823) B7573823
theorem B3366143 : Blo 2243435 3366143 := bstep (se 1 (by rfl) ⟨2524607, by rfl⟩ : syracuseStep 3366143 = 5049215) B5049215
theorem B2244095 : Blo 2243435 2244095 := bstep (se 1 (by rfl) ⟨1683071, by rfl⟩ : syracuseStep 2244095 = 3366143) B3366143
theorem B3366149 : Blo 2243435 3366149 := bbase (se 4 (by rfl) ⟨315576, by rfl⟩ : syracuseStep 3366149 = 631153) (by norm_num)
theorem B2244099 : Blo 2243435 2244099 := bstep (se 1 (by rfl) ⟨1683074, by rfl⟩ : syracuseStep 2244099 = 3366149) B3366149
theorem B3786925 : Blo 2243435 3786925 := bbase (se 3 (by rfl) ⟨710048, by rfl⟩ : syracuseStep 3786925 = 1420097) (by norm_num)
theorem B5049233 : Blo 2243435 5049233 := bstep (se 2 (by rfl) ⟨1893462, by rfl⟩ : syracuseStep 5049233 = 3786925) B3786925
theorem B3366155 : Blo 2243435 3366155 := bstep (se 1 (by rfl) ⟨2524616, by rfl⟩ : syracuseStep 3366155 = 5049233) B5049233
theorem B2244103 : Blo 2243435 2244103 := bstep (se 1 (by rfl) ⟨1683077, by rfl⟩ : syracuseStep 2244103 = 3366155) B3366155
theorem B2524621 : Blo 2243435 2524621 := bbase (se 3 (by rfl) ⟨473366, by rfl⟩ : syracuseStep 2524621 = 946733) (by norm_num)
theorem B3366161 : Blo 2243435 3366161 := bstep (se 2 (by rfl) ⟨1262310, by rfl⟩ : syracuseStep 3366161 = 2524621) B2524621
theorem B2244107 : Blo 2243435 2244107 := bstep (se 1 (by rfl) ⟨1683080, by rfl⟩ : syracuseStep 2244107 = 3366161) B3366161
theorem B7573877 : Blo 2243435 7573877 := bbase (se 5 (by rfl) ⟨355025, by rfl⟩ : syracuseStep 7573877 = 710051) (by norm_num)
theorem B5049251 : Blo 2243435 5049251 := bstep (se 1 (by rfl) ⟨3786938, by rfl⟩ : syracuseStep 5049251 = 7573877) B7573877
theorem B3366167 : Blo 2243435 3366167 := bstep (se 1 (by rfl) ⟨2524625, by rfl⟩ : syracuseStep 3366167 = 5049251) B5049251
theorem B2244111 : Blo 2243435 2244111 := bstep (se 1 (by rfl) ⟨1683083, by rfl⟩ : syracuseStep 2244111 = 3366167) B3366167
theorem B3366173 : Blo 2243435 3366173 := bbase (se 3 (by rfl) ⟨631157, by rfl⟩ : syracuseStep 3366173 = 1262315) (by norm_num)
theorem B2244115 : Blo 2243435 2244115 := bstep (se 1 (by rfl) ⟨1683086, by rfl⟩ : syracuseStep 2244115 = 3366173) B3366173
theorem B5049269 : Blo 2243435 5049269 := bbase (se 5 (by rfl) ⟨236684, by rfl⟩ : syracuseStep 5049269 = 473369) (by norm_num)
theorem B3366179 : Blo 2243435 3366179 := bstep (se 1 (by rfl) ⟨2524634, by rfl⟩ : syracuseStep 3366179 = 5049269) B5049269
theorem B2244119 : Blo 2243435 2244119 := bstep (se 1 (by rfl) ⟨1683089, by rfl⟩ : syracuseStep 2244119 = 3366179) B3366179
theorem B12131957 : Blo 2243435 12131957 := bbase (se 5 (by rfl) ⟨568685, by rfl⟩ : syracuseStep 12131957 = 1137371) (by norm_num)
theorem B8087971 : Blo 2243435 8087971 := bstep (se 1 (by rfl) ⟨6065978, by rfl⟩ : syracuseStep 8087971 = 12131957) B12131957
theorem B10783961 : Blo 2243435 10783961 := bstep (se 2 (by rfl) ⟨4043985, by rfl⟩ : syracuseStep 10783961 = 8087971) B8087971
theorem B7189307 : Blo 2243435 7189307 := bstep (se 1 (by rfl) ⟨5391980, by rfl⟩ : syracuseStep 7189307 = 10783961) B10783961
theorem B4792871 : Blo 2243435 4792871 := bstep (se 1 (by rfl) ⟨3594653, by rfl⟩ : syracuseStep 4792871 = 7189307) B7189307
theorem B12780989 : Blo 2243435 12780989 := bstep (se 3 (by rfl) ⟨2396435, by rfl⟩ : syracuseStep 12780989 = 4792871) B4792871
theorem B8520659 : Blo 2243435 8520659 := bstep (se 1 (by rfl) ⟨6390494, by rfl⟩ : syracuseStep 8520659 = 12780989) B12780989
theorem B5680439 : Blo 2243435 5680439 := bstep (se 1 (by rfl) ⟨4260329, by rfl⟩ : syracuseStep 5680439 = 8520659) B8520659
theorem B3786959 : Blo 2243435 3786959 := bstep (se 1 (by rfl) ⟨2840219, by rfl⟩ : syracuseStep 3786959 = 5680439) B5680439
theorem B2524639 : Blo 2243435 2524639 := bstep (se 1 (by rfl) ⟨1893479, by rfl⟩ : syracuseStep 2524639 = 3786959) B3786959
theorem B3366185 : Blo 2243435 3366185 := bstep (se 2 (by rfl) ⟨1262319, by rfl⟩ : syracuseStep 3366185 = 2524639) B2524639
theorem B2244123 : Blo 2243435 2244123 := bstep (se 1 (by rfl) ⟨1683092, by rfl⟩ : syracuseStep 2244123 = 3366185) B3366185
theorem B22462837 : Blo 2243435 22462837 := bbase (se 5 (by rfl) ⟨1052945, by rfl⟩ : syracuseStep 22462837 = 2105891) (by norm_num)
theorem B119801797 : Blo 2243435 119801797 := bstep (se 4 (by rfl) ⟨11231418, by rfl⟩ : syracuseStep 119801797 = 22462837) B22462837
theorem B638942917 : Blo 2243435 638942917 := bstep (se 4 (by rfl) ⟨59900898, by rfl⟩ : syracuseStep 638942917 = 119801797) B119801797
theorem B851923889 : Blo 2243435 851923889 := bstep (se 2 (by rfl) ⟨319471458, by rfl⟩ : syracuseStep 851923889 = 638942917) B638942917
theorem B567949259 : Blo 2243435 567949259 := bstep (se 1 (by rfl) ⟨425961944, by rfl⟩ : syracuseStep 567949259 = 851923889) B851923889
theorem B378632839 : Blo 2243435 378632839 := bstep (se 1 (by rfl) ⟨283974629, by rfl⟩ : syracuseStep 378632839 = 567949259) B567949259
theorem B504843785 : Blo 2243435 504843785 := bstep (se 2 (by rfl) ⟨189316419, by rfl⟩ : syracuseStep 504843785 = 378632839) B378632839
theorem B336562523 : Blo 2243435 336562523 := bstep (se 1 (by rfl) ⟨252421892, by rfl⟩ : syracuseStep 336562523 = 504843785) B504843785
theorem B224375015 : Blo 2243435 224375015 := bstep (se 1 (by rfl) ⟨168281261, by rfl⟩ : syracuseStep 224375015 = 336562523) B336562523
theorem B149583343 : Blo 2243435 149583343 := bstep (se 1 (by rfl) ⟨112187507, by rfl⟩ : syracuseStep 149583343 = 224375015) B224375015
theorem B199444457 : Blo 2243435 199444457 := bstep (se 2 (by rfl) ⟨74791671, by rfl⟩ : syracuseStep 199444457 = 149583343) B149583343
theorem B132962971 : Blo 2243435 132962971 := bstep (se 1 (by rfl) ⟨99722228, by rfl⟩ : syracuseStep 132962971 = 199444457) B199444457
theorem B177283961 : Blo 2243435 177283961 := bstep (se 2 (by rfl) ⟨66481485, by rfl⟩ : syracuseStep 177283961 = 132962971) B132962971
theorem B118189307 : Blo 2243435 118189307 := bstep (se 1 (by rfl) ⟨88641980, by rfl⟩ : syracuseStep 118189307 = 177283961) B177283961
theorem B78792871 : Blo 2243435 78792871 := bstep (se 1 (by rfl) ⟨59094653, by rfl⟩ : syracuseStep 78792871 = 118189307) B118189307
theorem B105057161 : Blo 2243435 105057161 := bstep (se 2 (by rfl) ⟨39396435, by rfl⟩ : syracuseStep 105057161 = 78792871) B78792871
theorem B70038107 : Blo 2243435 70038107 := bstep (se 1 (by rfl) ⟨52528580, by rfl⟩ : syracuseStep 70038107 = 105057161) B105057161
theorem B46692071 : Blo 2243435 46692071 := bstep (se 1 (by rfl) ⟨35019053, by rfl⟩ : syracuseStep 46692071 = 70038107) B70038107
theorem B31128047 : Blo 2243435 31128047 := bstep (se 1 (by rfl) ⟨23346035, by rfl⟩ : syracuseStep 31128047 = 46692071) B46692071
theorem B20752031 : Blo 2243435 20752031 := bstep (se 1 (by rfl) ⟨15564023, by rfl⟩ : syracuseStep 20752031 = 31128047) B31128047
theorem B13834687 : Blo 2243435 13834687 := bstep (se 1 (by rfl) ⟨10376015, by rfl⟩ : syracuseStep 13834687 = 20752031) B20752031
theorem B18446249 : Blo 2243435 18446249 := bstep (se 2 (by rfl) ⟨6917343, by rfl⟩ : syracuseStep 18446249 = 13834687) B13834687
theorem B49189997 : Blo 2243435 49189997 := bstep (se 3 (by rfl) ⟨9223124, by rfl⟩ : syracuseStep 49189997 = 18446249) B18446249
theorem B32793331 : Blo 2243435 32793331 := bstep (se 1 (by rfl) ⟨24594998, by rfl⟩ : syracuseStep 32793331 = 49189997) B49189997
theorem B43724441 : Blo 2243435 43724441 := bstep (se 2 (by rfl) ⟨16396665, by rfl⟩ : syracuseStep 43724441 = 32793331) B32793331
theorem B29149627 : Blo 2243435 29149627 := bstep (se 1 (by rfl) ⟨21862220, by rfl⟩ : syracuseStep 29149627 = 43724441) B43724441
theorem B38866169 : Blo 2243435 38866169 := bstep (se 2 (by rfl) ⟨14574813, by rfl⟩ : syracuseStep 38866169 = 29149627) B29149627
theorem B25910779 : Blo 2243435 25910779 := bstep (se 1 (by rfl) ⟨19433084, by rfl⟩ : syracuseStep 25910779 = 38866169) B38866169
theorem B34547705 : Blo 2243435 34547705 := bstep (se 2 (by rfl) ⟨12955389, by rfl⟩ : syracuseStep 34547705 = 25910779) B25910779
theorem B23031803 : Blo 2243435 23031803 := bstep (se 1 (by rfl) ⟨17273852, by rfl⟩ : syracuseStep 23031803 = 34547705) B34547705
theorem B15354535 : Blo 2243435 15354535 := bstep (se 1 (by rfl) ⟨11515901, by rfl⟩ : syracuseStep 15354535 = 23031803) B23031803
theorem B20472713 : Blo 2243435 20472713 := bstep (se 2 (by rfl) ⟨7677267, by rfl⟩ : syracuseStep 20472713 = 15354535) B15354535
theorem B13648475 : Blo 2243435 13648475 := bstep (se 1 (by rfl) ⟨10236356, by rfl⟩ : syracuseStep 13648475 = 20472713) B20472713
theorem B9098983 : Blo 2243435 9098983 := bstep (se 1 (by rfl) ⟨6824237, by rfl⟩ : syracuseStep 9098983 = 13648475) B13648475
theorem B12131977 : Blo 2243435 12131977 := bstep (se 2 (by rfl) ⟨4549491, by rfl⟩ : syracuseStep 12131977 = 9098983) B9098983
theorem B16175969 : Blo 2243435 16175969 := bstep (se 2 (by rfl) ⟨6065988, by rfl⟩ : syracuseStep 16175969 = 12131977) B12131977
theorem B10783979 : Blo 2243435 10783979 := bstep (se 1 (by rfl) ⟨8087984, by rfl⟩ : syracuseStep 10783979 = 16175969) B16175969
theorem B7189319 : Blo 2243435 7189319 := bstep (se 1 (by rfl) ⟨5391989, by rfl⟩ : syracuseStep 7189319 = 10783979) B10783979
theorem B4792879 : Blo 2243435 4792879 := bstep (se 1 (by rfl) ⟨3594659, by rfl⟩ : syracuseStep 4792879 = 7189319) B7189319
theorem B6390505 : Blo 2243435 6390505 := bstep (se 2 (by rfl) ⟨2396439, by rfl⟩ : syracuseStep 6390505 = 4792879) B4792879
theorem B8520673 : Blo 2243435 8520673 := bstep (se 2 (by rfl) ⟨3195252, by rfl⟩ : syracuseStep 8520673 = 6390505) B6390505
theorem B11360897 : Blo 2243435 11360897 := bstep (se 2 (by rfl) ⟨4260336, by rfl⟩ : syracuseStep 11360897 = 8520673) B8520673
theorem B7573931 : Blo 2243435 7573931 := bstep (se 1 (by rfl) ⟨5680448, by rfl⟩ : syracuseStep 7573931 = 11360897) B11360897
theorem B5049287 : Blo 2243435 5049287 := bstep (se 1 (by rfl) ⟨3786965, by rfl⟩ : syracuseStep 5049287 = 7573931) B7573931
theorem B3366191 : Blo 2243435 3366191 := bstep (se 1 (by rfl) ⟨2524643, by rfl⟩ : syracuseStep 3366191 = 5049287) B5049287
theorem B2244127 : Blo 2243435 2244127 := bstep (se 1 (by rfl) ⟨1683095, by rfl⟩ : syracuseStep 2244127 = 3366191) B3366191
theorem B3366197 : Blo 2243435 3366197 := bbase (se 5 (by rfl) ⟨157790, by rfl⟩ : syracuseStep 3366197 = 315581) (by norm_num)
theorem B2244131 : Blo 2243435 2244131 := bstep (se 1 (by rfl) ⟨1683098, by rfl⟩ : syracuseStep 2244131 = 3366197) B3366197
theorem B5680469 : Blo 2243435 5680469 := bbase (se 11 (by rfl) ⟨4160, by rfl⟩ : syracuseStep 5680469 = 8321) (by norm_num)
theorem B3786979 : Blo 2243435 3786979 := bstep (se 1 (by rfl) ⟨2840234, by rfl⟩ : syracuseStep 3786979 = 5680469) B5680469
theorem B5049305 : Blo 2243435 5049305 := bstep (se 2 (by rfl) ⟨1893489, by rfl⟩ : syracuseStep 5049305 = 3786979) B3786979
theorem B3366203 : Blo 2243435 3366203 := bstep (se 1 (by rfl) ⟨2524652, by rfl⟩ : syracuseStep 3366203 = 5049305) B5049305
theorem B2244135 : Blo 2243435 2244135 := bstep (se 1 (by rfl) ⟨1683101, by rfl⟩ : syracuseStep 2244135 = 3366203) B3366203
theorem B2524657 : Blo 2243435 2524657 := bbase (se 2 (by rfl) ⟨946746, by rfl⟩ : syracuseStep 2524657 = 1893493) (by norm_num)
theorem B3366209 : Blo 2243435 3366209 := bstep (se 2 (by rfl) ⟨1262328, by rfl⟩ : syracuseStep 3366209 = 2524657) B2524657
theorem B2244139 : Blo 2243435 2244139 := bstep (se 1 (by rfl) ⟨1683104, by rfl⟩ : syracuseStep 2244139 = 3366209) B3366209
theorem B14378741 : Blo 2243435 14378741 := bbase (se 5 (by rfl) ⟨674003, by rfl⟩ : syracuseStep 14378741 = 1348007) (by norm_num)
theorem B9585827 : Blo 2243435 9585827 := bstep (se 1 (by rfl) ⟨7189370, by rfl⟩ : syracuseStep 9585827 = 14378741) B14378741
theorem B6390551 : Blo 2243435 6390551 := bstep (se 1 (by rfl) ⟨4792913, by rfl⟩ : syracuseStep 6390551 = 9585827) B9585827
theorem B4260367 : Blo 2243435 4260367 := bstep (se 1 (by rfl) ⟨3195275, by rfl⟩ : syracuseStep 4260367 = 6390551) B6390551
theorem B5680489 : Blo 2243435 5680489 := bstep (se 2 (by rfl) ⟨2130183, by rfl⟩ : syracuseStep 5680489 = 4260367) B4260367
theorem B7573985 : Blo 2243435 7573985 := bstep (se 2 (by rfl) ⟨2840244, by rfl⟩ : syracuseStep 7573985 = 5680489) B5680489
theorem B5049323 : Blo 2243435 5049323 := bstep (se 1 (by rfl) ⟨3786992, by rfl⟩ : syracuseStep 5049323 = 7573985) B7573985
theorem B3366215 : Blo 2243435 3366215 := bstep (se 1 (by rfl) ⟨2524661, by rfl⟩ : syracuseStep 3366215 = 5049323) B5049323
theorem B2244143 : Blo 2243435 2244143 := bstep (se 1 (by rfl) ⟨1683107, by rfl⟩ : syracuseStep 2244143 = 3366215) B3366215
theorem B3366221 : Blo 2243435 3366221 := bbase (se 3 (by rfl) ⟨631166, by rfl⟩ : syracuseStep 3366221 = 1262333) (by norm_num)
theorem B2244147 : Blo 2243435 2244147 := bstep (se 1 (by rfl) ⟨1683110, by rfl⟩ : syracuseStep 2244147 = 3366221) B3366221
theorem B5049341 : Blo 2243435 5049341 := bbase (se 3 (by rfl) ⟨946751, by rfl⟩ : syracuseStep 5049341 = 1893503) (by norm_num)
theorem B3366227 : Blo 2243435 3366227 := bstep (se 1 (by rfl) ⟨2524670, by rfl⟩ : syracuseStep 3366227 = 5049341) B5049341
theorem B2244151 : Blo 2243435 2244151 := bstep (se 1 (by rfl) ⟨1683113, by rfl⟩ : syracuseStep 2244151 = 3366227) B3366227
theorem B3787013 : Blo 2243435 3787013 := bbase (se 4 (by rfl) ⟨355032, by rfl⟩ : syracuseStep 3787013 = 710065) (by norm_num)
theorem B2524675 : Blo 2243435 2524675 := bstep (se 1 (by rfl) ⟨1893506, by rfl⟩ : syracuseStep 2524675 = 3787013) B3787013
theorem B3366233 : Blo 2243435 3366233 := bstep (se 2 (by rfl) ⟨1262337, by rfl⟩ : syracuseStep 3366233 = 2524675) B2524675
theorem B2244155 : Blo 2243435 2244155 := bstep (se 1 (by rfl) ⟨1683116, by rfl⟩ : syracuseStep 2244155 = 3366233) B3366233
theorem B17041589 : Blo 2243435 17041589 := bbase (se 5 (by rfl) ⟨798824, by rfl⟩ : syracuseStep 17041589 = 1597649) (by norm_num)
theorem B11361059 : Blo 2243435 11361059 := bstep (se 1 (by rfl) ⟨8520794, by rfl⟩ : syracuseStep 11361059 = 17041589) B17041589
theorem B7574039 : Blo 2243435 7574039 := bstep (se 1 (by rfl) ⟨5680529, by rfl⟩ : syracuseStep 7574039 = 11361059) B11361059
theorem B5049359 : Blo 2243435 5049359 := bstep (se 1 (by rfl) ⟨3787019, by rfl⟩ : syracuseStep 5049359 = 7574039) B7574039
theorem B3366239 : Blo 2243435 3366239 := bstep (se 1 (by rfl) ⟨2524679, by rfl⟩ : syracuseStep 3366239 = 5049359) B5049359
theorem B2244159 : Blo 2243435 2244159 := bstep (se 1 (by rfl) ⟨1683119, by rfl⟩ : syracuseStep 2244159 = 3366239) B3366239
theorem B3366245 : Blo 2243435 3366245 := bbase (se 4 (by rfl) ⟨315585, by rfl⟩ : syracuseStep 3366245 = 631171) (by norm_num)
theorem B2244163 : Blo 2243435 2244163 := bstep (se 1 (by rfl) ⟨1683122, by rfl⟩ : syracuseStep 2244163 = 3366245) B3366245
theorem B4260413 : Blo 2243435 4260413 := bbase (se 3 (by rfl) ⟨798827, by rfl⟩ : syracuseStep 4260413 = 1597655) (by norm_num)
theorem B2840275 : Blo 2243435 2840275 := bstep (se 1 (by rfl) ⟨2130206, by rfl⟩ : syracuseStep 2840275 = 4260413) B4260413
theorem B3787033 : Blo 2243435 3787033 := bstep (se 2 (by rfl) ⟨1420137, by rfl⟩ : syracuseStep 3787033 = 2840275) B2840275
theorem B5049377 : Blo 2243435 5049377 := bstep (se 2 (by rfl) ⟨1893516, by rfl⟩ : syracuseStep 5049377 = 3787033) B3787033
theorem B3366251 : Blo 2243435 3366251 := bstep (se 1 (by rfl) ⟨2524688, by rfl⟩ : syracuseStep 3366251 = 5049377) B5049377
theorem B2244167 : Blo 2243435 2244167 := bstep (se 1 (by rfl) ⟨1683125, by rfl⟩ : syracuseStep 2244167 = 3366251) B3366251
theorem B2524693 : Blo 2243435 2524693 := bbase (se 6 (by rfl) ⟨59172, by rfl⟩ : syracuseStep 2524693 = 118345) (by norm_num)
theorem B3366257 : Blo 2243435 3366257 := bstep (se 2 (by rfl) ⟨1262346, by rfl⟩ : syracuseStep 3366257 = 2524693) B2524693
theorem B2244171 : Blo 2243435 2244171 := bstep (se 1 (by rfl) ⟨1683128, by rfl⟩ : syracuseStep 2244171 = 3366257) B3366257
theorem B2840285 : Blo 2243435 2840285 := bbase (se 3 (by rfl) ⟨532553, by rfl⟩ : syracuseStep 2840285 = 1065107) (by norm_num)
theorem B7574093 : Blo 2243435 7574093 := bstep (se 3 (by rfl) ⟨1420142, by rfl⟩ : syracuseStep 7574093 = 2840285) B2840285
theorem B5049395 : Blo 2243435 5049395 := bstep (se 1 (by rfl) ⟨3787046, by rfl⟩ : syracuseStep 5049395 = 7574093) B7574093
theorem B3366263 : Blo 2243435 3366263 := bstep (se 1 (by rfl) ⟨2524697, by rfl⟩ : syracuseStep 3366263 = 5049395) B5049395
theorem B2244175 : Blo 2243435 2244175 := bstep (se 1 (by rfl) ⟨1683131, by rfl⟩ : syracuseStep 2244175 = 3366263) B3366263
theorem B3366269 : Blo 2243435 3366269 := bbase (se 3 (by rfl) ⟨631175, by rfl⟩ : syracuseStep 3366269 = 1262351) (by norm_num)
theorem B2244179 : Blo 2243435 2244179 := bstep (se 1 (by rfl) ⟨1683134, by rfl⟩ : syracuseStep 2244179 = 3366269) B3366269
theorem B5049413 : Blo 2243435 5049413 := bbase (se 4 (by rfl) ⟨473382, by rfl⟩ : syracuseStep 5049413 = 946765) (by norm_num)
theorem B3366275 : Blo 2243435 3366275 := bstep (se 1 (by rfl) ⟨2524706, by rfl⟩ : syracuseStep 3366275 = 5049413) B5049413
theorem B2244183 : Blo 2243435 2244183 := bstep (se 1 (by rfl) ⟨1683137, by rfl⟩ : syracuseStep 2244183 = 3366275) B3366275
theorem B6390677 : Blo 2243435 6390677 := bbase (se 6 (by rfl) ⟨149781, by rfl⟩ : syracuseStep 6390677 = 299563) (by norm_num)
theorem B4260451 : Blo 2243435 4260451 := bstep (se 1 (by rfl) ⟨3195338, by rfl⟩ : syracuseStep 4260451 = 6390677) B6390677
theorem B5680601 : Blo 2243435 5680601 := bstep (se 2 (by rfl) ⟨2130225, by rfl⟩ : syracuseStep 5680601 = 4260451) B4260451
theorem B3787067 : Blo 2243435 3787067 := bstep (se 1 (by rfl) ⟨2840300, by rfl⟩ : syracuseStep 3787067 = 5680601) B5680601
theorem B2524711 : Blo 2243435 2524711 := bstep (se 1 (by rfl) ⟨1893533, by rfl⟩ : syracuseStep 2524711 = 3787067) B3787067
theorem B3366281 : Blo 2243435 3366281 := bstep (se 2 (by rfl) ⟨1262355, by rfl⟩ : syracuseStep 3366281 = 2524711) B2524711
theorem B2244187 : Blo 2243435 2244187 := bstep (se 1 (by rfl) ⟨1683140, by rfl⟩ : syracuseStep 2244187 = 3366281) B3366281
theorem B11361221 : Blo 2243435 11361221 := bbase (se 4 (by rfl) ⟨1065114, by rfl⟩ : syracuseStep 11361221 = 2130229) (by norm_num)
theorem B7574147 : Blo 2243435 7574147 := bstep (se 1 (by rfl) ⟨5680610, by rfl⟩ : syracuseStep 7574147 = 11361221) B11361221
theorem B5049431 : Blo 2243435 5049431 := bstep (se 1 (by rfl) ⟨3787073, by rfl⟩ : syracuseStep 5049431 = 7574147) B7574147
theorem B3366287 : Blo 2243435 3366287 := bstep (se 1 (by rfl) ⟨2524715, by rfl⟩ : syracuseStep 3366287 = 5049431) B5049431
theorem B2244191 : Blo 2243435 2244191 := bstep (se 1 (by rfl) ⟨1683143, by rfl⟩ : syracuseStep 2244191 = 3366287) B3366287
theorem B3366293 : Blo 2243435 3366293 := bbase (se 6 (by rfl) ⟨78897, by rfl⟩ : syracuseStep 3366293 = 157795) (by norm_num)
theorem B2244195 : Blo 2243435 2244195 := bstep (se 1 (by rfl) ⟨1683146, by rfl⟩ : syracuseStep 2244195 = 3366293) B3366293
theorem B8088245 : Blo 2243435 8088245 := bbase (se 5 (by rfl) ⟨379136, by rfl⟩ : syracuseStep 8088245 = 758273) (by norm_num)
theorem B5392163 : Blo 2243435 5392163 := bstep (se 1 (by rfl) ⟨4044122, by rfl⟩ : syracuseStep 5392163 = 8088245) B8088245
theorem B3594775 : Blo 2243435 3594775 := bstep (se 1 (by rfl) ⟨2696081, by rfl⟩ : syracuseStep 3594775 = 5392163) B5392163
theorem B4793033 : Blo 2243435 4793033 := bstep (se 2 (by rfl) ⟨1797387, by rfl⟩ : syracuseStep 4793033 = 3594775) B3594775
theorem B12781421 : Blo 2243435 12781421 := bstep (se 3 (by rfl) ⟨2396516, by rfl⟩ : syracuseStep 12781421 = 4793033) B4793033
theorem B8520947 : Blo 2243435 8520947 := bstep (se 1 (by rfl) ⟨6390710, by rfl⟩ : syracuseStep 8520947 = 12781421) B12781421
theorem B5680631 : Blo 2243435 5680631 := bstep (se 1 (by rfl) ⟨4260473, by rfl⟩ : syracuseStep 5680631 = 8520947) B8520947
theorem B3787087 : Blo 2243435 3787087 := bstep (se 1 (by rfl) ⟨2840315, by rfl⟩ : syracuseStep 3787087 = 5680631) B5680631
theorem B5049449 : Blo 2243435 5049449 := bstep (se 2 (by rfl) ⟨1893543, by rfl⟩ : syracuseStep 5049449 = 3787087) B3787087
theorem B3366299 : Blo 2243435 3366299 := bstep (se 1 (by rfl) ⟨2524724, by rfl⟩ : syracuseStep 3366299 = 5049449) B5049449
theorem B2244199 : Blo 2243435 2244199 := bstep (se 1 (by rfl) ⟨1683149, by rfl⟩ : syracuseStep 2244199 = 3366299) B3366299
theorem B2524729 : Blo 2243435 2524729 := bbase (se 2 (by rfl) ⟨946773, by rfl⟩ : syracuseStep 2524729 = 1893547) (by norm_num)
theorem B3366305 : Blo 2243435 3366305 := bstep (se 2 (by rfl) ⟨1262364, by rfl⟩ : syracuseStep 3366305 = 2524729) B2524729
theorem B2244203 : Blo 2243435 2244203 := bstep (se 1 (by rfl) ⟨1683152, by rfl⟩ : syracuseStep 2244203 = 3366305) B3366305
theorem B2396525 : Blo 2243435 2396525 := bbase (se 3 (by rfl) ⟨449348, by rfl⟩ : syracuseStep 2396525 = 898697) (by norm_num)
theorem B6390733 : Blo 2243435 6390733 := bstep (se 3 (by rfl) ⟨1198262, by rfl⟩ : syracuseStep 6390733 = 2396525) B2396525
theorem B8520977 : Blo 2243435 8520977 := bstep (se 2 (by rfl) ⟨3195366, by rfl⟩ : syracuseStep 8520977 = 6390733) B6390733
theorem B5680651 : Blo 2243435 5680651 := bstep (se 1 (by rfl) ⟨4260488, by rfl⟩ : syracuseStep 5680651 = 8520977) B8520977
theorem B7574201 : Blo 2243435 7574201 := bstep (se 2 (by rfl) ⟨2840325, by rfl⟩ : syracuseStep 7574201 = 5680651) B5680651
theorem B5049467 : Blo 2243435 5049467 := bstep (se 1 (by rfl) ⟨3787100, by rfl⟩ : syracuseStep 5049467 = 7574201) B7574201
theorem B3366311 : Blo 2243435 3366311 := bstep (se 1 (by rfl) ⟨2524733, by rfl⟩ : syracuseStep 3366311 = 5049467) B5049467
theorem B2244207 : Blo 2243435 2244207 := bstep (se 1 (by rfl) ⟨1683155, by rfl⟩ : syracuseStep 2244207 = 3366311) B3366311
theorem B3366317 : Blo 2243435 3366317 := bbase (se 3 (by rfl) ⟨631184, by rfl⟩ : syracuseStep 3366317 = 1262369) (by norm_num)
theorem B2244211 : Blo 2243435 2244211 := bstep (se 1 (by rfl) ⟨1683158, by rfl⟩ : syracuseStep 2244211 = 3366317) B3366317
theorem B5049485 : Blo 2243435 5049485 := bbase (se 3 (by rfl) ⟨946778, by rfl⟩ : syracuseStep 5049485 = 1893557) (by norm_num)
theorem B3366323 : Blo 2243435 3366323 := bstep (se 1 (by rfl) ⟨2524742, by rfl⟩ : syracuseStep 3366323 = 5049485) B5049485
theorem B2244215 : Blo 2243435 2244215 := bstep (se 1 (by rfl) ⟨1683161, by rfl⟩ : syracuseStep 2244215 = 3366323) B3366323
theorem B2840341 : Blo 2243435 2840341 := bbase (se 6 (by rfl) ⟨66570, by rfl⟩ : syracuseStep 2840341 = 133141) (by norm_num)
theorem B3787121 : Blo 2243435 3787121 := bstep (se 2 (by rfl) ⟨1420170, by rfl⟩ : syracuseStep 3787121 = 2840341) B2840341
theorem B2524747 : Blo 2243435 2524747 := bstep (se 1 (by rfl) ⟨1893560, by rfl⟩ : syracuseStep 2524747 = 3787121) B3787121
theorem B3366329 : Blo 2243435 3366329 := bstep (se 2 (by rfl) ⟨1262373, by rfl⟩ : syracuseStep 3366329 = 2524747) B2524747
theorem B2244219 : Blo 2243435 2244219 := bstep (se 1 (by rfl) ⟨1683164, by rfl⟩ : syracuseStep 2244219 = 3366329) B3366329
theorem B5188229 : Blo 2243435 5188229 := bbase (se 4 (by rfl) ⟨486396, by rfl⟩ : syracuseStep 5188229 = 972793) (by norm_num)
theorem B3458819 : Blo 2243435 3458819 := bstep (se 1 (by rfl) ⟨2594114, by rfl⟩ : syracuseStep 3458819 = 5188229) B5188229
theorem B2305879 : Blo 2243435 2305879 := bstep (se 1 (by rfl) ⟨1729409, by rfl⟩ : syracuseStep 2305879 = 3458819) B3458819
theorem B49192085 : Blo 2243435 49192085 := bstep (se 6 (by rfl) ⟨1152939, by rfl⟩ : syracuseStep 49192085 = 2305879) B2305879
theorem B32794723 : Blo 2243435 32794723 := bstep (se 1 (by rfl) ⟨24596042, by rfl⟩ : syracuseStep 32794723 = 49192085) B49192085
theorem B174905189 : Blo 2243435 174905189 := bstep (se 4 (by rfl) ⟨16397361, by rfl⟩ : syracuseStep 174905189 = 32794723) B32794723
theorem B116603459 : Blo 2243435 116603459 := bstep (se 1 (by rfl) ⟨87452594, by rfl⟩ : syracuseStep 116603459 = 174905189) B174905189
theorem B77735639 : Blo 2243435 77735639 := bstep (se 1 (by rfl) ⟨58301729, by rfl⟩ : syracuseStep 77735639 = 116603459) B116603459
theorem B207295037 : Blo 2243435 207295037 := bstep (se 3 (by rfl) ⟨38867819, by rfl⟩ : syracuseStep 207295037 = 77735639) B77735639
theorem B138196691 : Blo 2243435 138196691 := bstep (se 1 (by rfl) ⟨103647518, by rfl⟩ : syracuseStep 138196691 = 207295037) B207295037
theorem B92131127 : Blo 2243435 92131127 := bstep (se 1 (by rfl) ⟨69098345, by rfl⟩ : syracuseStep 92131127 = 138196691) B138196691
theorem B61420751 : Blo 2243435 61420751 := bstep (se 1 (by rfl) ⟨46065563, by rfl⟩ : syracuseStep 61420751 = 92131127) B92131127
theorem B40947167 : Blo 2243435 40947167 := bstep (se 1 (by rfl) ⟨30710375, by rfl⟩ : syracuseStep 40947167 = 61420751) B61420751
theorem B109192445 : Blo 2243435 109192445 := bstep (se 3 (by rfl) ⟨20473583, by rfl⟩ : syracuseStep 109192445 = 40947167) B40947167
theorem B72794963 : Blo 2243435 72794963 := bstep (se 1 (by rfl) ⟨54596222, by rfl⟩ : syracuseStep 72794963 = 109192445) B109192445
theorem B48529975 : Blo 2243435 48529975 := bstep (se 1 (by rfl) ⟨36397481, by rfl⟩ : syracuseStep 48529975 = 72794963) B72794963
theorem B64706633 : Blo 2243435 64706633 := bstep (se 2 (by rfl) ⟨24264987, by rfl⟩ : syracuseStep 64706633 = 48529975) B48529975
theorem B43137755 : Blo 2243435 43137755 := bstep (se 1 (by rfl) ⟨32353316, by rfl⟩ : syracuseStep 43137755 = 64706633) B64706633
theorem B28758503 : Blo 2243435 28758503 := bstep (se 1 (by rfl) ⟨21568877, by rfl⟩ : syracuseStep 28758503 = 43137755) B43137755
theorem B19172335 : Blo 2243435 19172335 := bstep (se 1 (by rfl) ⟨14379251, by rfl⟩ : syracuseStep 19172335 = 28758503) B28758503
theorem B25563113 : Blo 2243435 25563113 := bstep (se 2 (by rfl) ⟨9586167, by rfl⟩ : syracuseStep 25563113 = 19172335) B19172335
theorem B17042075 : Blo 2243435 17042075 := bstep (se 1 (by rfl) ⟨12781556, by rfl⟩ : syracuseStep 17042075 = 25563113) B25563113
theorem B11361383 : Blo 2243435 11361383 := bstep (se 1 (by rfl) ⟨8521037, by rfl⟩ : syracuseStep 11361383 = 17042075) B17042075
theorem B7574255 : Blo 2243435 7574255 := bstep (se 1 (by rfl) ⟨5680691, by rfl⟩ : syracuseStep 7574255 = 11361383) B11361383
theorem B5049503 : Blo 2243435 5049503 := bstep (se 1 (by rfl) ⟨3787127, by rfl⟩ : syracuseStep 5049503 = 7574255) B7574255
theorem B3366335 : Blo 2243435 3366335 := bstep (se 1 (by rfl) ⟨2524751, by rfl⟩ : syracuseStep 3366335 = 5049503) B5049503
theorem B2244223 : Blo 2243435 2244223 := bstep (se 1 (by rfl) ⟨1683167, by rfl⟩ : syracuseStep 2244223 = 3366335) B3366335
theorem B3366341 : Blo 2243435 3366341 := bbase (se 4 (by rfl) ⟨315594, by rfl⟩ : syracuseStep 3366341 = 631189) (by norm_num)
theorem B2244227 : Blo 2243435 2244227 := bstep (se 1 (by rfl) ⟨1683170, by rfl⟩ : syracuseStep 2244227 = 3366341) B3366341
theorem B3787141 : Blo 2243435 3787141 := bbase (se 4 (by rfl) ⟨355044, by rfl⟩ : syracuseStep 3787141 = 710089) (by norm_num)
theorem B5049521 : Blo 2243435 5049521 := bstep (se 2 (by rfl) ⟨1893570, by rfl⟩ : syracuseStep 5049521 = 3787141) B3787141
theorem B3366347 : Blo 2243435 3366347 := bstep (se 1 (by rfl) ⟨2524760, by rfl⟩ : syracuseStep 3366347 = 5049521) B5049521
theorem B2244231 : Blo 2243435 2244231 := bstep (se 1 (by rfl) ⟨1683173, by rfl⟩ : syracuseStep 2244231 = 3366347) B3366347
theorem B2524765 : Blo 2243435 2524765 := bbase (se 3 (by rfl) ⟨473393, by rfl⟩ : syracuseStep 2524765 = 946787) (by norm_num)
theorem B3366353 : Blo 2243435 3366353 := bstep (se 2 (by rfl) ⟨1262382, by rfl⟩ : syracuseStep 3366353 = 2524765) B2524765
theorem B2244235 : Blo 2243435 2244235 := bstep (se 1 (by rfl) ⟨1683176, by rfl⟩ : syracuseStep 2244235 = 3366353) B3366353
theorem B7574309 : Blo 2243435 7574309 := bbase (se 4 (by rfl) ⟨710091, by rfl⟩ : syracuseStep 7574309 = 1420183) (by norm_num)
theorem B5049539 : Blo 2243435 5049539 := bstep (se 1 (by rfl) ⟨3787154, by rfl⟩ : syracuseStep 5049539 = 7574309) B7574309
theorem B3366359 : Blo 2243435 3366359 := bstep (se 1 (by rfl) ⟨2524769, by rfl⟩ : syracuseStep 3366359 = 5049539) B5049539
theorem B2244239 : Blo 2243435 2244239 := bstep (se 1 (by rfl) ⟨1683179, by rfl⟩ : syracuseStep 2244239 = 3366359) B3366359
theorem B3366365 : Blo 2243435 3366365 := bbase (se 3 (by rfl) ⟨631193, by rfl⟩ : syracuseStep 3366365 = 1262387) (by norm_num)
theorem B2244243 : Blo 2243435 2244243 := bstep (se 1 (by rfl) ⟨1683182, by rfl⟩ : syracuseStep 2244243 = 3366365) B3366365
theorem B5049557 : Blo 2243435 5049557 := bbase (se 7 (by rfl) ⟨59174, by rfl⟩ : syracuseStep 5049557 = 118349) (by norm_num)
theorem B3366371 : Blo 2243435 3366371 := bstep (se 1 (by rfl) ⟨2524778, by rfl⟩ : syracuseStep 3366371 = 5049557) B5049557
theorem B2244247 : Blo 2243435 2244247 := bstep (se 1 (by rfl) ⟨1683185, by rfl⟩ : syracuseStep 2244247 = 3366371) B3366371
theorem B7189717 : Blo 2243435 7189717 := bbase (se 7 (by rfl) ⟨84254, by rfl⟩ : syracuseStep 7189717 = 168509) (by norm_num)
theorem B9586289 : Blo 2243435 9586289 := bstep (se 2 (by rfl) ⟨3594858, by rfl⟩ : syracuseStep 9586289 = 7189717) B7189717
theorem B6390859 : Blo 2243435 6390859 := bstep (se 1 (by rfl) ⟨4793144, by rfl⟩ : syracuseStep 6390859 = 9586289) B9586289
theorem B8521145 : Blo 2243435 8521145 := bstep (se 2 (by rfl) ⟨3195429, by rfl⟩ : syracuseStep 8521145 = 6390859) B6390859
theorem B5680763 : Blo 2243435 5680763 := bstep (se 1 (by rfl) ⟨4260572, by rfl⟩ : syracuseStep 5680763 = 8521145) B8521145
theorem B3787175 : Blo 2243435 3787175 := bstep (se 1 (by rfl) ⟨2840381, by rfl⟩ : syracuseStep 3787175 = 5680763) B5680763
theorem B2524783 : Blo 2243435 2524783 := bstep (se 1 (by rfl) ⟨1893587, by rfl⟩ : syracuseStep 2524783 = 3787175) B3787175
theorem B3366377 : Blo 2243435 3366377 := bstep (se 2 (by rfl) ⟨1262391, by rfl⟩ : syracuseStep 3366377 = 2524783) B2524783
theorem B2244251 : Blo 2243435 2244251 := bstep (se 1 (by rfl) ⟨1683188, by rfl⟩ : syracuseStep 2244251 = 3366377) B3366377
theorem B3838853 : Blo 2243435 3838853 := bbase (se 4 (by rfl) ⟨359892, by rfl⟩ : syracuseStep 3838853 = 719785) (by norm_num)
theorem B10236941 : Blo 2243435 10236941 := bstep (se 3 (by rfl) ⟨1919426, by rfl⟩ : syracuseStep 10236941 = 3838853) B3838853
theorem B6824627 : Blo 2243435 6824627 := bstep (se 1 (by rfl) ⟨5118470, by rfl⟩ : syracuseStep 6824627 = 10236941) B10236941
theorem B4549751 : Blo 2243435 4549751 := bstep (se 1 (by rfl) ⟨3412313, by rfl⟩ : syracuseStep 4549751 = 6824627) B6824627
theorem B3033167 : Blo 2243435 3033167 := bstep (se 1 (by rfl) ⟨2274875, by rfl⟩ : syracuseStep 3033167 = 4549751) B4549751
theorem B8088445 : Blo 2243435 8088445 := bstep (se 3 (by rfl) ⟨1516583, by rfl⟩ : syracuseStep 8088445 = 3033167) B3033167
theorem B10784593 : Blo 2243435 10784593 := bstep (se 2 (by rfl) ⟨4044222, by rfl⟩ : syracuseStep 10784593 = 8088445) B8088445
theorem B14379457 : Blo 2243435 14379457 := bstep (se 2 (by rfl) ⟨5392296, by rfl⟩ : syracuseStep 14379457 = 10784593) B10784593
theorem B19172609 : Blo 2243435 19172609 := bstep (se 2 (by rfl) ⟨7189728, by rfl⟩ : syracuseStep 19172609 = 14379457) B14379457
theorem B12781739 : Blo 2243435 12781739 := bstep (se 1 (by rfl) ⟨9586304, by rfl⟩ : syracuseStep 12781739 = 19172609) B19172609
theorem B8521159 : Blo 2243435 8521159 := bstep (se 1 (by rfl) ⟨6390869, by rfl⟩ : syracuseStep 8521159 = 12781739) B12781739
theorem B11361545 : Blo 2243435 11361545 := bstep (se 2 (by rfl) ⟨4260579, by rfl⟩ : syracuseStep 11361545 = 8521159) B8521159
theorem B7574363 : Blo 2243435 7574363 := bstep (se 1 (by rfl) ⟨5680772, by rfl⟩ : syracuseStep 7574363 = 11361545) B11361545
theorem B5049575 : Blo 2243435 5049575 := bstep (se 1 (by rfl) ⟨3787181, by rfl⟩ : syracuseStep 5049575 = 7574363) B7574363
theorem B3366383 : Blo 2243435 3366383 := bstep (se 1 (by rfl) ⟨2524787, by rfl⟩ : syracuseStep 3366383 = 5049575) B5049575
theorem B2244255 : Blo 2243435 2244255 := bstep (se 1 (by rfl) ⟨1683191, by rfl⟩ : syracuseStep 2244255 = 3366383) B3366383
theorem B3366389 : Blo 2243435 3366389 := bbase (se 5 (by rfl) ⟨157799, by rfl⟩ : syracuseStep 3366389 = 315599) (by norm_num)
theorem B2244259 : Blo 2243435 2244259 := bstep (se 1 (by rfl) ⟨1683194, by rfl⟩ : syracuseStep 2244259 = 3366389) B3366389
theorem B2396585 : Blo 2243435 2396585 := bbase (se 2 (by rfl) ⟨898719, by rfl⟩ : syracuseStep 2396585 = 1797439) (by norm_num)
theorem B6390893 : Blo 2243435 6390893 := bstep (se 3 (by rfl) ⟨1198292, by rfl⟩ : syracuseStep 6390893 = 2396585) B2396585
theorem B4260595 : Blo 2243435 4260595 := bstep (se 1 (by rfl) ⟨3195446, by rfl⟩ : syracuseStep 4260595 = 6390893) B6390893
theorem B5680793 : Blo 2243435 5680793 := bstep (se 2 (by rfl) ⟨2130297, by rfl⟩ : syracuseStep 5680793 = 4260595) B4260595
theorem B3787195 : Blo 2243435 3787195 := bstep (se 1 (by rfl) ⟨2840396, by rfl⟩ : syracuseStep 3787195 = 5680793) B5680793
theorem B5049593 : Blo 2243435 5049593 := bstep (se 2 (by rfl) ⟨1893597, by rfl⟩ : syracuseStep 5049593 = 3787195) B3787195
theorem B3366395 : Blo 2243435 3366395 := bstep (se 1 (by rfl) ⟨2524796, by rfl⟩ : syracuseStep 3366395 = 5049593) B5049593
theorem B2244263 : Blo 2243435 2244263 := bstep (se 1 (by rfl) ⟨1683197, by rfl⟩ : syracuseStep 2244263 = 3366395) B3366395
theorem B2524801 : Blo 2243435 2524801 := bbase (se 2 (by rfl) ⟨946800, by rfl⟩ : syracuseStep 2524801 = 1893601) (by norm_num)
theorem B3366401 : Blo 2243435 3366401 := bstep (se 2 (by rfl) ⟨1262400, by rfl⟩ : syracuseStep 3366401 = 2524801) B2524801
theorem B2244267 : Blo 2243435 2244267 := bstep (se 1 (by rfl) ⟨1683200, by rfl⟩ : syracuseStep 2244267 = 3366401) B3366401
theorem B5680813 : Blo 2243435 5680813 := bbase (se 3 (by rfl) ⟨1065152, by rfl⟩ : syracuseStep 5680813 = 2130305) (by norm_num)
theorem B7574417 : Blo 2243435 7574417 := bstep (se 2 (by rfl) ⟨2840406, by rfl⟩ : syracuseStep 7574417 = 5680813) B5680813
theorem B5049611 : Blo 2243435 5049611 := bstep (se 1 (by rfl) ⟨3787208, by rfl⟩ : syracuseStep 5049611 = 7574417) B7574417
theorem B3366407 : Blo 2243435 3366407 := bstep (se 1 (by rfl) ⟨2524805, by rfl⟩ : syracuseStep 3366407 = 5049611) B5049611
theorem B2244271 : Blo 2243435 2244271 := bstep (se 1 (by rfl) ⟨1683203, by rfl⟩ : syracuseStep 2244271 = 3366407) B3366407
theorem B3366413 : Blo 2243435 3366413 := bbase (se 3 (by rfl) ⟨631202, by rfl⟩ : syracuseStep 3366413 = 1262405) (by norm_num)
theorem B2244275 : Blo 2243435 2244275 := bstep (se 1 (by rfl) ⟨1683206, by rfl⟩ : syracuseStep 2244275 = 3366413) B3366413
theorem B5049629 : Blo 2243435 5049629 := bbase (se 3 (by rfl) ⟨946805, by rfl⟩ : syracuseStep 5049629 = 1893611) (by norm_num)
theorem B3366419 : Blo 2243435 3366419 := bstep (se 1 (by rfl) ⟨2524814, by rfl⟩ : syracuseStep 3366419 = 5049629) B5049629
theorem B2244279 : Blo 2243435 2244279 := bstep (se 1 (by rfl) ⟨1683209, by rfl⟩ : syracuseStep 2244279 = 3366419) B3366419
theorem B3787229 : Blo 2243435 3787229 := bbase (se 3 (by rfl) ⟨710105, by rfl⟩ : syracuseStep 3787229 = 1420211) (by norm_num)
theorem B2524819 : Blo 2243435 2524819 := bstep (se 1 (by rfl) ⟨1893614, by rfl⟩ : syracuseStep 2524819 = 3787229) B3787229
theorem B3366425 : Blo 2243435 3366425 := bstep (se 2 (by rfl) ⟨1262409, by rfl⟩ : syracuseStep 3366425 = 2524819) B2524819
theorem B2244283 : Blo 2243435 2244283 := bstep (se 1 (by rfl) ⟨1683212, by rfl⟩ : syracuseStep 2244283 = 3366425) B3366425
theorem B34550165 : Blo 2243435 34550165 := bbase (se 6 (by rfl) ⟨809769, by rfl⟩ : syracuseStep 34550165 = 1619539) (by norm_num)
theorem B23033443 : Blo 2243435 23033443 := bstep (se 1 (by rfl) ⟨17275082, by rfl⟩ : syracuseStep 23033443 = 34550165) B34550165
theorem B30711257 : Blo 2243435 30711257 := bstep (se 2 (by rfl) ⟨11516721, by rfl⟩ : syracuseStep 30711257 = 23033443) B23033443
theorem B20474171 : Blo 2243435 20474171 := bstep (se 1 (by rfl) ⟨15355628, by rfl⟩ : syracuseStep 20474171 = 30711257) B30711257
theorem B13649447 : Blo 2243435 13649447 := bstep (se 1 (by rfl) ⟨10237085, by rfl⟩ : syracuseStep 13649447 = 20474171) B20474171
theorem B9099631 : Blo 2243435 9099631 := bstep (se 1 (by rfl) ⟨6824723, by rfl⟩ : syracuseStep 9099631 = 13649447) B13649447
theorem B12132841 : Blo 2243435 12132841 := bstep (se 2 (by rfl) ⟨4549815, by rfl⟩ : syracuseStep 12132841 = 9099631) B9099631
theorem B16177121 : Blo 2243435 16177121 := bstep (se 2 (by rfl) ⟨6066420, by rfl⟩ : syracuseStep 16177121 = 12132841) B12132841
theorem B10784747 : Blo 2243435 10784747 := bstep (se 1 (by rfl) ⟨8088560, by rfl⟩ : syracuseStep 10784747 = 16177121) B16177121
theorem B7189831 : Blo 2243435 7189831 := bstep (se 1 (by rfl) ⟨5392373, by rfl⟩ : syracuseStep 7189831 = 10784747) B10784747
theorem B9586441 : Blo 2243435 9586441 := bstep (se 2 (by rfl) ⟨3594915, by rfl⟩ : syracuseStep 9586441 = 7189831) B7189831
theorem B12781921 : Blo 2243435 12781921 := bstep (se 2 (by rfl) ⟨4793220, by rfl⟩ : syracuseStep 12781921 = 9586441) B9586441
theorem B17042561 : Blo 2243435 17042561 := bstep (se 2 (by rfl) ⟨6390960, by rfl⟩ : syracuseStep 17042561 = 12781921) B12781921
theorem B11361707 : Blo 2243435 11361707 := bstep (se 1 (by rfl) ⟨8521280, by rfl⟩ : syracuseStep 11361707 = 17042561) B17042561
theorem B7574471 : Blo 2243435 7574471 := bstep (se 1 (by rfl) ⟨5680853, by rfl⟩ : syracuseStep 7574471 = 11361707) B11361707
theorem B5049647 : Blo 2243435 5049647 := bstep (se 1 (by rfl) ⟨3787235, by rfl⟩ : syracuseStep 5049647 = 7574471) B7574471
theorem B3366431 : Blo 2243435 3366431 := bstep (se 1 (by rfl) ⟨2524823, by rfl⟩ : syracuseStep 3366431 = 5049647) B5049647
theorem B2244287 : Blo 2243435 2244287 := bstep (se 1 (by rfl) ⟨1683215, by rfl⟩ : syracuseStep 2244287 = 3366431) B3366431
theorem B3366437 : Blo 2243435 3366437 := bbase (se 4 (by rfl) ⟨315603, by rfl⟩ : syracuseStep 3366437 = 631207) (by norm_num)
theorem B2244291 : Blo 2243435 2244291 := bstep (se 1 (by rfl) ⟨1683218, by rfl⟩ : syracuseStep 2244291 = 3366437) B3366437
theorem B2840437 : Blo 2243435 2840437 := bbase (se 5 (by rfl) ⟨133145, by rfl⟩ : syracuseStep 2840437 = 266291) (by norm_num)
theorem B3787249 : Blo 2243435 3787249 := bstep (se 2 (by rfl) ⟨1420218, by rfl⟩ : syracuseStep 3787249 = 2840437) B2840437
theorem B5049665 : Blo 2243435 5049665 := bstep (se 2 (by rfl) ⟨1893624, by rfl⟩ : syracuseStep 5049665 = 3787249) B3787249
theorem B3366443 : Blo 2243435 3366443 := bstep (se 1 (by rfl) ⟨2524832, by rfl⟩ : syracuseStep 3366443 = 5049665) B5049665
theorem B2244295 : Blo 2243435 2244295 := bstep (se 1 (by rfl) ⟨1683221, by rfl⟩ : syracuseStep 2244295 = 3366443) B3366443
theorem B2524837 : Blo 2243435 2524837 := bbase (se 4 (by rfl) ⟨236703, by rfl⟩ : syracuseStep 2524837 = 473407) (by norm_num)
theorem B3366449 : Blo 2243435 3366449 := bstep (se 2 (by rfl) ⟨1262418, by rfl⟩ : syracuseStep 3366449 = 2524837) B2524837
theorem B2244299 : Blo 2243435 2244299 := bstep (se 1 (by rfl) ⟨1683224, by rfl⟩ : syracuseStep 2244299 = 3366449) B3366449
theorem B6824773 : Blo 2243435 6824773 := bbase (se 4 (by rfl) ⟨639822, by rfl⟩ : syracuseStep 6824773 = 1279645) (by norm_num)
theorem B9099697 : Blo 2243435 9099697 := bstep (se 2 (by rfl) ⟨3412386, by rfl⟩ : syracuseStep 9099697 = 6824773) B6824773
theorem B12132929 : Blo 2243435 12132929 := bstep (se 2 (by rfl) ⟨4549848, by rfl⟩ : syracuseStep 12132929 = 9099697) B9099697
theorem B32354477 : Blo 2243435 32354477 := bstep (se 3 (by rfl) ⟨6066464, by rfl⟩ : syracuseStep 32354477 = 12132929) B12132929
theorem B21569651 : Blo 2243435 21569651 := bstep (se 1 (by rfl) ⟨16177238, by rfl⟩ : syracuseStep 21569651 = 32354477) B32354477
theorem B14379767 : Blo 2243435 14379767 := bstep (se 1 (by rfl) ⟨10784825, by rfl⟩ : syracuseStep 14379767 = 21569651) B21569651
theorem B9586511 : Blo 2243435 9586511 := bstep (se 1 (by rfl) ⟨7189883, by rfl⟩ : syracuseStep 9586511 = 14379767) B14379767
theorem B6391007 : Blo 2243435 6391007 := bstep (se 1 (by rfl) ⟨4793255, by rfl⟩ : syracuseStep 6391007 = 9586511) B9586511
theorem B4260671 : Blo 2243435 4260671 := bstep (se 1 (by rfl) ⟨3195503, by rfl⟩ : syracuseStep 4260671 = 6391007) B6391007
theorem B2840447 : Blo 2243435 2840447 := bstep (se 1 (by rfl) ⟨2130335, by rfl⟩ : syracuseStep 2840447 = 4260671) B4260671
theorem B7574525 : Blo 2243435 7574525 := bstep (se 3 (by rfl) ⟨1420223, by rfl⟩ : syracuseStep 7574525 = 2840447) B2840447
theorem B5049683 : Blo 2243435 5049683 := bstep (se 1 (by rfl) ⟨3787262, by rfl⟩ : syracuseStep 5049683 = 7574525) B7574525
theorem B3366455 : Blo 2243435 3366455 := bstep (se 1 (by rfl) ⟨2524841, by rfl⟩ : syracuseStep 3366455 = 5049683) B5049683
theorem B2244303 : Blo 2243435 2244303 := bstep (se 1 (by rfl) ⟨1683227, by rfl⟩ : syracuseStep 2244303 = 3366455) B3366455
theorem B3366461 : Blo 2243435 3366461 := bbase (se 3 (by rfl) ⟨631211, by rfl⟩ : syracuseStep 3366461 = 1262423) (by norm_num)
theorem B2244307 : Blo 2243435 2244307 := bstep (se 1 (by rfl) ⟨1683230, by rfl⟩ : syracuseStep 2244307 = 3366461) B3366461
theorem B5049701 : Blo 2243435 5049701 := bbase (se 4 (by rfl) ⟨473409, by rfl⟩ : syracuseStep 5049701 = 946819) (by norm_num)
theorem B3366467 : Blo 2243435 3366467 := bstep (se 1 (by rfl) ⟨2524850, by rfl⟩ : syracuseStep 3366467 = 5049701) B5049701
theorem B2244311 : Blo 2243435 2244311 := bstep (se 1 (by rfl) ⟨1683233, by rfl⟩ : syracuseStep 2244311 = 3366467) B3366467
theorem B5680925 : Blo 2243435 5680925 := bbase (se 3 (by rfl) ⟨1065173, by rfl⟩ : syracuseStep 5680925 = 2130347) (by norm_num)
theorem B3787283 : Blo 2243435 3787283 := bstep (se 1 (by rfl) ⟨2840462, by rfl⟩ : syracuseStep 3787283 = 5680925) B5680925
theorem B2524855 : Blo 2243435 2524855 := bstep (se 1 (by rfl) ⟨1893641, by rfl⟩ : syracuseStep 2524855 = 3787283) B3787283
theorem B3366473 : Blo 2243435 3366473 := bstep (se 2 (by rfl) ⟨1262427, by rfl⟩ : syracuseStep 3366473 = 2524855) B2524855
theorem B2244315 : Blo 2243435 2244315 := bstep (se 1 (by rfl) ⟨1683236, by rfl⟩ : syracuseStep 2244315 = 3366473) B3366473
theorem B4260701 : Blo 2243435 4260701 := bbase (se 3 (by rfl) ⟨798881, by rfl⟩ : syracuseStep 4260701 = 1597763) (by norm_num)
theorem B11361869 : Blo 2243435 11361869 := bstep (se 3 (by rfl) ⟨2130350, by rfl⟩ : syracuseStep 11361869 = 4260701) B4260701
theorem B7574579 : Blo 2243435 7574579 := bstep (se 1 (by rfl) ⟨5680934, by rfl⟩ : syracuseStep 7574579 = 11361869) B11361869
theorem B5049719 : Blo 2243435 5049719 := bstep (se 1 (by rfl) ⟨3787289, by rfl⟩ : syracuseStep 5049719 = 7574579) B7574579
theorem B3366479 : Blo 2243435 3366479 := bstep (se 1 (by rfl) ⟨2524859, by rfl⟩ : syracuseStep 3366479 = 5049719) B5049719
theorem B2244319 : Blo 2243435 2244319 := bstep (se 1 (by rfl) ⟨1683239, by rfl⟩ : syracuseStep 2244319 = 3366479) B3366479
theorem B3366485 : Blo 2243435 3366485 := bbase (se 8 (by rfl) ⟨19725, by rfl⟩ : syracuseStep 3366485 = 39451) (by norm_num)
theorem B2244323 : Blo 2243435 2244323 := bstep (se 1 (by rfl) ⟨1683242, by rfl⟩ : syracuseStep 2244323 = 3366485) B3366485
theorem B9586613 : Blo 2243435 9586613 := bbase (se 5 (by rfl) ⟨449372, by rfl⟩ : syracuseStep 9586613 = 898745) (by norm_num)
theorem B6391075 : Blo 2243435 6391075 := bstep (se 1 (by rfl) ⟨4793306, by rfl⟩ : syracuseStep 6391075 = 9586613) B9586613
theorem B8521433 : Blo 2243435 8521433 := bstep (se 2 (by rfl) ⟨3195537, by rfl⟩ : syracuseStep 8521433 = 6391075) B6391075
theorem B5680955 : Blo 2243435 5680955 := bstep (se 1 (by rfl) ⟨4260716, by rfl⟩ : syracuseStep 5680955 = 8521433) B8521433
theorem B3787303 : Blo 2243435 3787303 := bstep (se 1 (by rfl) ⟨2840477, by rfl⟩ : syracuseStep 3787303 = 5680955) B5680955
theorem B5049737 : Blo 2243435 5049737 := bstep (se 2 (by rfl) ⟨1893651, by rfl⟩ : syracuseStep 5049737 = 3787303) B3787303
theorem B3366491 : Blo 2243435 3366491 := bstep (se 1 (by rfl) ⟨2524868, by rfl⟩ : syracuseStep 3366491 = 5049737) B5049737
theorem B2244327 : Blo 2243435 2244327 := bstep (se 1 (by rfl) ⟨1683245, by rfl⟩ : syracuseStep 2244327 = 3366491) B3366491
theorem B2524873 : Blo 2243435 2524873 := bbase (se 2 (by rfl) ⟨946827, by rfl⟩ : syracuseStep 2524873 = 1893655) (by norm_num)
theorem B3366497 : Blo 2243435 3366497 := bstep (se 2 (by rfl) ⟨1262436, by rfl⟩ : syracuseStep 3366497 = 2524873) B2524873
theorem B2244331 : Blo 2243435 2244331 := bstep (se 1 (by rfl) ⟨1683248, by rfl⟩ : syracuseStep 2244331 = 3366497) B3366497
theorem B5118653 : Blo 2243435 5118653 := bbase (se 3 (by rfl) ⟨959747, by rfl⟩ : syracuseStep 5118653 = 1919495) (by norm_num)
theorem B13649741 : Blo 2243435 13649741 := bstep (se 3 (by rfl) ⟨2559326, by rfl⟩ : syracuseStep 13649741 = 5118653) B5118653
theorem B9099827 : Blo 2243435 9099827 := bstep (se 1 (by rfl) ⟨6824870, by rfl⟩ : syracuseStep 9099827 = 13649741) B13649741
theorem B6066551 : Blo 2243435 6066551 := bstep (se 1 (by rfl) ⟨4549913, by rfl⟩ : syracuseStep 6066551 = 9099827) B9099827
theorem B4044367 : Blo 2243435 4044367 := bstep (se 1 (by rfl) ⟨3033275, by rfl⟩ : syracuseStep 4044367 = 6066551) B6066551
theorem B5392489 : Blo 2243435 5392489 := bstep (se 2 (by rfl) ⟨2022183, by rfl⟩ : syracuseStep 5392489 = 4044367) B4044367
theorem B7189985 : Blo 2243435 7189985 := bstep (se 2 (by rfl) ⟨2696244, by rfl⟩ : syracuseStep 7189985 = 5392489) B5392489
theorem B19173293 : Blo 2243435 19173293 := bstep (se 3 (by rfl) ⟨3594992, by rfl⟩ : syracuseStep 19173293 = 7189985) B7189985
theorem B12782195 : Blo 2243435 12782195 := bstep (se 1 (by rfl) ⟨9586646, by rfl⟩ : syracuseStep 12782195 = 19173293) B19173293
theorem B8521463 : Blo 2243435 8521463 := bstep (se 1 (by rfl) ⟨6391097, by rfl⟩ : syracuseStep 8521463 = 12782195) B12782195
theorem B5680975 : Blo 2243435 5680975 := bstep (se 1 (by rfl) ⟨4260731, by rfl⟩ : syracuseStep 5680975 = 8521463) B8521463
theorem B7574633 : Blo 2243435 7574633 := bstep (se 2 (by rfl) ⟨2840487, by rfl⟩ : syracuseStep 7574633 = 5680975) B5680975
theorem B5049755 : Blo 2243435 5049755 := bstep (se 1 (by rfl) ⟨3787316, by rfl⟩ : syracuseStep 5049755 = 7574633) B7574633
theorem B3366503 : Blo 2243435 3366503 := bstep (se 1 (by rfl) ⟨2524877, by rfl⟩ : syracuseStep 3366503 = 5049755) B5049755
theorem B2244335 : Blo 2243435 2244335 := bstep (se 1 (by rfl) ⟨1683251, by rfl⟩ : syracuseStep 2244335 = 3366503) B3366503
theorem B3366509 : Blo 2243435 3366509 := bbase (se 3 (by rfl) ⟨631220, by rfl⟩ : syracuseStep 3366509 = 1262441) (by norm_num)
theorem B2244339 : Blo 2243435 2244339 := bstep (se 1 (by rfl) ⟨1683254, by rfl⟩ : syracuseStep 2244339 = 3366509) B3366509
theorem B5049773 : Blo 2243435 5049773 := bbase (se 3 (by rfl) ⟨946832, by rfl⟩ : syracuseStep 5049773 = 1893665) (by norm_num)
theorem B3366515 : Blo 2243435 3366515 := bstep (se 1 (by rfl) ⟨2524886, by rfl⟩ : syracuseStep 3366515 = 5049773) B5049773
theorem B2244343 : Blo 2243435 2244343 := bstep (se 1 (by rfl) ⟨1683257, by rfl⟩ : syracuseStep 2244343 = 3366515) B3366515
theorem B3595013 : Blo 2243435 3595013 := bbase (se 4 (by rfl) ⟨337032, by rfl⟩ : syracuseStep 3595013 = 674065) (by norm_num)
theorem B2396675 : Blo 2243435 2396675 := bstep (se 1 (by rfl) ⟨1797506, by rfl⟩ : syracuseStep 2396675 = 3595013) B3595013
theorem B6391133 : Blo 2243435 6391133 := bstep (se 3 (by rfl) ⟨1198337, by rfl⟩ : syracuseStep 6391133 = 2396675) B2396675
theorem B4260755 : Blo 2243435 4260755 := bstep (se 1 (by rfl) ⟨3195566, by rfl⟩ : syracuseStep 4260755 = 6391133) B6391133
theorem B2840503 : Blo 2243435 2840503 := bstep (se 1 (by rfl) ⟨2130377, by rfl⟩ : syracuseStep 2840503 = 4260755) B4260755
theorem B3787337 : Blo 2243435 3787337 := bstep (se 2 (by rfl) ⟨1420251, by rfl⟩ : syracuseStep 3787337 = 2840503) B2840503
theorem B2524891 : Blo 2243435 2524891 := bstep (se 1 (by rfl) ⟨1893668, by rfl⟩ : syracuseStep 2524891 = 3787337) B3787337
theorem B3366521 : Blo 2243435 3366521 := bstep (se 2 (by rfl) ⟨1262445, by rfl⟩ : syracuseStep 3366521 = 2524891) B2524891
theorem B2244347 : Blo 2243435 2244347 := bstep (se 1 (by rfl) ⟨1683260, by rfl⟩ : syracuseStep 2244347 = 3366521) B3366521
theorem B6824917 : Blo 2243435 6824917 := bbase (se 7 (by rfl) ⟨79979, by rfl⟩ : syracuseStep 6824917 = 159959) (by norm_num)
theorem B36399557 : Blo 2243435 36399557 := bstep (se 4 (by rfl) ⟨3412458, by rfl⟩ : syracuseStep 36399557 = 6824917) B6824917
theorem B97065485 : Blo 2243435 97065485 := bstep (se 3 (by rfl) ⟨18199778, by rfl⟩ : syracuseStep 97065485 = 36399557) B36399557
theorem B64710323 : Blo 2243435 64710323 := bstep (se 1 (by rfl) ⟨48532742, by rfl⟩ : syracuseStep 64710323 = 97065485) B97065485
theorem B43140215 : Blo 2243435 43140215 := bstep (se 1 (by rfl) ⟨32355161, by rfl⟩ : syracuseStep 43140215 = 64710323) B64710323
theorem B28760143 : Blo 2243435 28760143 := bstep (se 1 (by rfl) ⟨21570107, by rfl⟩ : syracuseStep 28760143 = 43140215) B43140215
theorem B38346857 : Blo 2243435 38346857 := bstep (se 2 (by rfl) ⟨14380071, by rfl⟩ : syracuseStep 38346857 = 28760143) B28760143
theorem B25564571 : Blo 2243435 25564571 := bstep (se 1 (by rfl) ⟨19173428, by rfl⟩ : syracuseStep 25564571 = 38346857) B38346857
theorem B17043047 : Blo 2243435 17043047 := bstep (se 1 (by rfl) ⟨12782285, by rfl⟩ : syracuseStep 17043047 = 25564571) B25564571
theorem B11362031 : Blo 2243435 11362031 := bstep (se 1 (by rfl) ⟨8521523, by rfl⟩ : syracuseStep 11362031 = 17043047) B17043047
theorem B7574687 : Blo 2243435 7574687 := bstep (se 1 (by rfl) ⟨5681015, by rfl⟩ : syracuseStep 7574687 = 11362031) B11362031
theorem B5049791 : Blo 2243435 5049791 := bstep (se 1 (by rfl) ⟨3787343, by rfl⟩ : syracuseStep 5049791 = 7574687) B7574687
theorem B3366527 : Blo 2243435 3366527 := bstep (se 1 (by rfl) ⟨2524895, by rfl⟩ : syracuseStep 3366527 = 5049791) B5049791
theorem B2244351 : Blo 2243435 2244351 := bstep (se 1 (by rfl) ⟨1683263, by rfl⟩ : syracuseStep 2244351 = 3366527) B3366527
theorem B3366533 : Blo 2243435 3366533 := bbase (se 4 (by rfl) ⟨315612, by rfl⟩ : syracuseStep 3366533 = 631225) (by norm_num)
theorem B2244355 : Blo 2243435 2244355 := bstep (se 1 (by rfl) ⟨1683266, by rfl⟩ : syracuseStep 2244355 = 3366533) B3366533
theorem B3787357 : Blo 2243435 3787357 := bbase (se 3 (by rfl) ⟨710129, by rfl⟩ : syracuseStep 3787357 = 1420259) (by norm_num)
theorem B5049809 : Blo 2243435 5049809 := bstep (se 2 (by rfl) ⟨1893678, by rfl⟩ : syracuseStep 5049809 = 3787357) B3787357
theorem B3366539 : Blo 2243435 3366539 := bstep (se 1 (by rfl) ⟨2524904, by rfl⟩ : syracuseStep 3366539 = 5049809) B5049809
theorem B2244359 : Blo 2243435 2244359 := bstep (se 1 (by rfl) ⟨1683269, by rfl⟩ : syracuseStep 2244359 = 3366539) B3366539
theorem B2524909 : Blo 2243435 2524909 := bbase (se 3 (by rfl) ⟨473420, by rfl⟩ : syracuseStep 2524909 = 946841) (by norm_num)
theorem B3366545 : Blo 2243435 3366545 := bstep (se 2 (by rfl) ⟨1262454, by rfl⟩ : syracuseStep 3366545 = 2524909) B2524909
theorem B2244363 : Blo 2243435 2244363 := bstep (se 1 (by rfl) ⟨1683272, by rfl⟩ : syracuseStep 2244363 = 3366545) B3366545
theorem B7574741 : Blo 2243435 7574741 := bbase (se 7 (by rfl) ⟨88766, by rfl⟩ : syracuseStep 7574741 = 177533) (by norm_num)
theorem B5049827 : Blo 2243435 5049827 := bstep (se 1 (by rfl) ⟨3787370, by rfl⟩ : syracuseStep 5049827 = 7574741) B7574741
theorem B3366551 : Blo 2243435 3366551 := bstep (se 1 (by rfl) ⟨2524913, by rfl⟩ : syracuseStep 3366551 = 5049827) B5049827
theorem B2244367 : Blo 2243435 2244367 := bstep (se 1 (by rfl) ⟨1683275, by rfl⟩ : syracuseStep 2244367 = 3366551) B3366551
theorem B3366557 : Blo 2243435 3366557 := bbase (se 3 (by rfl) ⟨631229, by rfl⟩ : syracuseStep 3366557 = 1262459) (by norm_num)
theorem B2244371 : Blo 2243435 2244371 := bstep (se 1 (by rfl) ⟨1683278, by rfl⟩ : syracuseStep 2244371 = 3366557) B3366557
theorem B5049845 : Blo 2243435 5049845 := bbase (se 5 (by rfl) ⟨236711, by rfl⟩ : syracuseStep 5049845 = 473423) (by norm_num)
theorem B3366563 : Blo 2243435 3366563 := bstep (se 1 (by rfl) ⟨2524922, by rfl⟩ : syracuseStep 3366563 = 5049845) B5049845
theorem B2244375 : Blo 2243435 2244375 := bstep (se 1 (by rfl) ⟨1683281, by rfl⟩ : syracuseStep 2244375 = 3366563) B3366563
theorem B5758597 : Blo 2243435 5758597 := bbase (se 4 (by rfl) ⟨539868, by rfl⟩ : syracuseStep 5758597 = 1079737) (by norm_num)
theorem B30712517 : Blo 2243435 30712517 := bstep (se 4 (by rfl) ⟨2879298, by rfl⟩ : syracuseStep 30712517 = 5758597) B5758597
theorem B20475011 : Blo 2243435 20475011 := bstep (se 1 (by rfl) ⟨15356258, by rfl⟩ : syracuseStep 20475011 = 30712517) B30712517
theorem B13650007 : Blo 2243435 13650007 := bstep (se 1 (by rfl) ⟨10237505, by rfl⟩ : syracuseStep 13650007 = 20475011) B20475011
theorem B18200009 : Blo 2243435 18200009 := bstep (se 2 (by rfl) ⟨6825003, by rfl⟩ : syracuseStep 18200009 = 13650007) B13650007
theorem B48533357 : Blo 2243435 48533357 := bstep (se 3 (by rfl) ⟨9100004, by rfl⟩ : syracuseStep 48533357 = 18200009) B18200009
theorem B32355571 : Blo 2243435 32355571 := bstep (se 1 (by rfl) ⟨24266678, by rfl⟩ : syracuseStep 32355571 = 48533357) B48533357
theorem B43140761 : Blo 2243435 43140761 := bstep (se 2 (by rfl) ⟨16177785, by rfl⟩ : syracuseStep 43140761 = 32355571) B32355571
theorem B28760507 : Blo 2243435 28760507 := bstep (se 1 (by rfl) ⟨21570380, by rfl⟩ : syracuseStep 28760507 = 43140761) B43140761
theorem B19173671 : Blo 2243435 19173671 := bstep (se 1 (by rfl) ⟨14380253, by rfl⟩ : syracuseStep 19173671 = 28760507) B28760507
theorem B12782447 : Blo 2243435 12782447 := bstep (se 1 (by rfl) ⟨9586835, by rfl⟩ : syracuseStep 12782447 = 19173671) B19173671
theorem B8521631 : Blo 2243435 8521631 := bstep (se 1 (by rfl) ⟨6391223, by rfl⟩ : syracuseStep 8521631 = 12782447) B12782447
theorem B5681087 : Blo 2243435 5681087 := bstep (se 1 (by rfl) ⟨4260815, by rfl⟩ : syracuseStep 5681087 = 8521631) B8521631
theorem B3787391 : Blo 2243435 3787391 := bstep (se 1 (by rfl) ⟨2840543, by rfl⟩ : syracuseStep 3787391 = 5681087) B5681087
theorem B2524927 : Blo 2243435 2524927 := bstep (se 1 (by rfl) ⟨1893695, by rfl⟩ : syracuseStep 2524927 = 3787391) B3787391
theorem B3366569 : Blo 2243435 3366569 := bstep (se 2 (by rfl) ⟨1262463, by rfl⟩ : syracuseStep 3366569 = 2524927) B2524927
theorem B2244379 : Blo 2243435 2244379 := bstep (se 1 (by rfl) ⟨1683284, by rfl⟩ : syracuseStep 2244379 = 3366569) B3366569
theorem B2396713 : Blo 2243435 2396713 := bbase (se 2 (by rfl) ⟨898767, by rfl⟩ : syracuseStep 2396713 = 1797535) (by norm_num)
theorem B3195617 : Blo 2243435 3195617 := bstep (se 2 (by rfl) ⟨1198356, by rfl⟩ : syracuseStep 3195617 = 2396713) B2396713
theorem B8521645 : Blo 2243435 8521645 := bstep (se 3 (by rfl) ⟨1597808, by rfl⟩ : syracuseStep 8521645 = 3195617) B3195617
theorem B11362193 : Blo 2243435 11362193 := bstep (se 2 (by rfl) ⟨4260822, by rfl⟩ : syracuseStep 11362193 = 8521645) B8521645
theorem B7574795 : Blo 2243435 7574795 := bstep (se 1 (by rfl) ⟨5681096, by rfl⟩ : syracuseStep 7574795 = 11362193) B11362193
theorem B5049863 : Blo 2243435 5049863 := bstep (se 1 (by rfl) ⟨3787397, by rfl⟩ : syracuseStep 5049863 = 7574795) B7574795
theorem B3366575 : Blo 2243435 3366575 := bstep (se 1 (by rfl) ⟨2524931, by rfl⟩ : syracuseStep 3366575 = 5049863) B5049863
theorem B2244383 : Blo 2243435 2244383 := bstep (se 1 (by rfl) ⟨1683287, by rfl⟩ : syracuseStep 2244383 = 3366575) B3366575
theorem B3366581 : Blo 2243435 3366581 := bbase (se 5 (by rfl) ⟨157808, by rfl⟩ : syracuseStep 3366581 = 315617) (by norm_num)
theorem B2244387 : Blo 2243435 2244387 := bstep (se 1 (by rfl) ⟨1683290, by rfl⟩ : syracuseStep 2244387 = 3366581) B3366581
theorem B5681117 : Blo 2243435 5681117 := bbase (se 3 (by rfl) ⟨1065209, by rfl⟩ : syracuseStep 5681117 = 2130419) (by norm_num)
theorem B3787411 : Blo 2243435 3787411 := bstep (se 1 (by rfl) ⟨2840558, by rfl⟩ : syracuseStep 3787411 = 5681117) B5681117
theorem B5049881 : Blo 2243435 5049881 := bstep (se 2 (by rfl) ⟨1893705, by rfl⟩ : syracuseStep 5049881 = 3787411) B3787411
theorem B3366587 : Blo 2243435 3366587 := bstep (se 1 (by rfl) ⟨2524940, by rfl⟩ : syracuseStep 3366587 = 5049881) B5049881
theorem B2244391 : Blo 2243435 2244391 := bstep (se 1 (by rfl) ⟨1683293, by rfl⟩ : syracuseStep 2244391 = 3366587) B3366587
theorem B2524945 : Blo 2243435 2524945 := bbase (se 2 (by rfl) ⟨946854, by rfl⟩ : syracuseStep 2524945 = 1893709) (by norm_num)
theorem B3366593 : Blo 2243435 3366593 := bstep (se 2 (by rfl) ⟨1262472, by rfl⟩ : syracuseStep 3366593 = 2524945) B2524945
theorem B2244395 : Blo 2243435 2244395 := bstep (se 1 (by rfl) ⟨1683296, by rfl⟩ : syracuseStep 2244395 = 3366593) B3366593
theorem B4260853 : Blo 2243435 4260853 := bbase (se 5 (by rfl) ⟨199727, by rfl⟩ : syracuseStep 4260853 = 399455) (by norm_num)
theorem B5681137 : Blo 2243435 5681137 := bstep (se 2 (by rfl) ⟨2130426, by rfl⟩ : syracuseStep 5681137 = 4260853) B4260853
theorem B7574849 : Blo 2243435 7574849 := bstep (se 2 (by rfl) ⟨2840568, by rfl⟩ : syracuseStep 7574849 = 5681137) B5681137
theorem B5049899 : Blo 2243435 5049899 := bstep (se 1 (by rfl) ⟨3787424, by rfl⟩ : syracuseStep 5049899 = 7574849) B7574849
theorem B3366599 : Blo 2243435 3366599 := bstep (se 1 (by rfl) ⟨2524949, by rfl⟩ : syracuseStep 3366599 = 5049899) B5049899
theorem B2244399 : Blo 2243435 2244399 := bstep (se 1 (by rfl) ⟨1683299, by rfl⟩ : syracuseStep 2244399 = 3366599) B3366599
theorem B3366605 : Blo 2243435 3366605 := bbase (se 3 (by rfl) ⟨631238, by rfl⟩ : syracuseStep 3366605 = 1262477) (by norm_num)
theorem B2244403 : Blo 2243435 2244403 := bstep (se 1 (by rfl) ⟨1683302, by rfl⟩ : syracuseStep 2244403 = 3366605) B3366605
theorem B5049917 : Blo 2243435 5049917 := bbase (se 3 (by rfl) ⟨946859, by rfl⟩ : syracuseStep 5049917 = 1893719) (by norm_num)
theorem B3366611 : Blo 2243435 3366611 := bstep (se 1 (by rfl) ⟨2524958, by rfl⟩ : syracuseStep 3366611 = 5049917) B5049917
theorem B2244407 : Blo 2243435 2244407 := bstep (se 1 (by rfl) ⟨1683305, by rfl⟩ : syracuseStep 2244407 = 3366611) B3366611
theorem B3787445 : Blo 2243435 3787445 := bbase (se 5 (by rfl) ⟨177536, by rfl⟩ : syracuseStep 3787445 = 355073) (by norm_num)
theorem B2524963 : Blo 2243435 2524963 := bstep (se 1 (by rfl) ⟨1893722, by rfl⟩ : syracuseStep 2524963 = 3787445) B3787445
theorem B3366617 : Blo 2243435 3366617 := bstep (se 2 (by rfl) ⟨1262481, by rfl⟩ : syracuseStep 3366617 = 2524963) B2524963
theorem B2244411 : Blo 2243435 2244411 := bstep (se 1 (by rfl) ⟨1683308, by rfl⟩ : syracuseStep 2244411 = 3366617) B3366617
theorem B2696341 : Blo 2243435 2696341 := bbase (se 6 (by rfl) ⟨63195, by rfl⟩ : syracuseStep 2696341 = 126391) (by norm_num)
theorem B3595121 : Blo 2243435 3595121 := bstep (se 2 (by rfl) ⟨1348170, by rfl⟩ : syracuseStep 3595121 = 2696341) B2696341
theorem B2396747 : Blo 2243435 2396747 := bstep (se 1 (by rfl) ⟨1797560, by rfl⟩ : syracuseStep 2396747 = 3595121) B3595121
theorem B6391325 : Blo 2243435 6391325 := bstep (se 3 (by rfl) ⟨1198373, by rfl⟩ : syracuseStep 6391325 = 2396747) B2396747
theorem B17043533 : Blo 2243435 17043533 := bstep (se 3 (by rfl) ⟨3195662, by rfl⟩ : syracuseStep 17043533 = 6391325) B6391325
theorem B11362355 : Blo 2243435 11362355 := bstep (se 1 (by rfl) ⟨8521766, by rfl⟩ : syracuseStep 11362355 = 17043533) B17043533
theorem B7574903 : Blo 2243435 7574903 := bstep (se 1 (by rfl) ⟨5681177, by rfl⟩ : syracuseStep 7574903 = 11362355) B11362355
theorem B5049935 : Blo 2243435 5049935 := bstep (se 1 (by rfl) ⟨3787451, by rfl⟩ : syracuseStep 5049935 = 7574903) B7574903
theorem B3366623 : Blo 2243435 3366623 := bstep (se 1 (by rfl) ⟨2524967, by rfl⟩ : syracuseStep 3366623 = 5049935) B5049935
theorem B2244415 : Blo 2243435 2244415 := bstep (se 1 (by rfl) ⟨1683311, by rfl⟩ : syracuseStep 2244415 = 3366623) B3366623
theorem B3366629 : Blo 2243435 3366629 := bbase (se 4 (by rfl) ⟨315621, by rfl⟩ : syracuseStep 3366629 = 631243) (by norm_num)
theorem B2244419 : Blo 2243435 2244419 := bstep (se 1 (by rfl) ⟨1683314, by rfl⟩ : syracuseStep 2244419 = 3366629) B3366629
theorem B6391349 : Blo 2243435 6391349 := bbase (se 5 (by rfl) ⟨299594, by rfl⟩ : syracuseStep 6391349 = 599189) (by norm_num)
theorem B4260899 : Blo 2243435 4260899 := bstep (se 1 (by rfl) ⟨3195674, by rfl⟩ : syracuseStep 4260899 = 6391349) B6391349
theorem B2840599 : Blo 2243435 2840599 := bstep (se 1 (by rfl) ⟨2130449, by rfl⟩ : syracuseStep 2840599 = 4260899) B4260899
theorem B3787465 : Blo 2243435 3787465 := bstep (se 2 (by rfl) ⟨1420299, by rfl⟩ : syracuseStep 3787465 = 2840599) B2840599
theorem B5049953 : Blo 2243435 5049953 := bstep (se 2 (by rfl) ⟨1893732, by rfl⟩ : syracuseStep 5049953 = 3787465) B3787465
theorem B3366635 : Blo 2243435 3366635 := bstep (se 1 (by rfl) ⟨2524976, by rfl⟩ : syracuseStep 3366635 = 5049953) B5049953
theorem B2244423 : Blo 2243435 2244423 := bstep (se 1 (by rfl) ⟨1683317, by rfl⟩ : syracuseStep 2244423 = 3366635) B3366635
theorem B2524981 : Blo 2243435 2524981 := bbase (se 5 (by rfl) ⟨118358, by rfl⟩ : syracuseStep 2524981 = 236717) (by norm_num)
theorem B3366641 : Blo 2243435 3366641 := bstep (se 2 (by rfl) ⟨1262490, by rfl⟩ : syracuseStep 3366641 = 2524981) B2524981
theorem B2244427 : Blo 2243435 2244427 := bstep (se 1 (by rfl) ⟨1683320, by rfl⟩ : syracuseStep 2244427 = 3366641) B3366641
theorem B2840609 : Blo 2243435 2840609 := bbase (se 2 (by rfl) ⟨1065228, by rfl⟩ : syracuseStep 2840609 = 2130457) (by norm_num)
theorem B7574957 : Blo 2243435 7574957 := bstep (se 3 (by rfl) ⟨1420304, by rfl⟩ : syracuseStep 7574957 = 2840609) B2840609
theorem B5049971 : Blo 2243435 5049971 := bstep (se 1 (by rfl) ⟨3787478, by rfl⟩ : syracuseStep 5049971 = 7574957) B7574957
theorem B3366647 : Blo 2243435 3366647 := bstep (se 1 (by rfl) ⟨2524985, by rfl⟩ : syracuseStep 3366647 = 5049971) B5049971
theorem B2244431 : Blo 2243435 2244431 := bstep (se 1 (by rfl) ⟨1683323, by rfl⟩ : syracuseStep 2244431 = 3366647) B3366647
theorem B3366653 : Blo 2243435 3366653 := bbase (se 3 (by rfl) ⟨631247, by rfl⟩ : syracuseStep 3366653 = 1262495) (by norm_num)
theorem B2244435 : Blo 2243435 2244435 := bstep (se 1 (by rfl) ⟨1683326, by rfl⟩ : syracuseStep 2244435 = 3366653) B3366653
theorem B5049989 : Blo 2243435 5049989 := bbase (se 4 (by rfl) ⟨473436, by rfl⟩ : syracuseStep 5049989 = 946873) (by norm_num)
theorem B3366659 : Blo 2243435 3366659 := bstep (se 1 (by rfl) ⟨2524994, by rfl⟩ : syracuseStep 3366659 = 5049989) B5049989
theorem B2244439 : Blo 2243435 2244439 := bstep (se 1 (by rfl) ⟨1683329, by rfl⟩ : syracuseStep 2244439 = 3366659) B3366659
theorem B6478613 : Blo 2243435 6478613 := bbase (se 6 (by rfl) ⟨151842, by rfl⟩ : syracuseStep 6478613 = 303685) (by norm_num)
theorem B4319075 : Blo 2243435 4319075 := bstep (se 1 (by rfl) ⟨3239306, by rfl⟩ : syracuseStep 4319075 = 6478613) B6478613
theorem B2879383 : Blo 2243435 2879383 := bstep (se 1 (by rfl) ⟨2159537, by rfl⟩ : syracuseStep 2879383 = 4319075) B4319075
theorem B3839177 : Blo 2243435 3839177 := bstep (se 2 (by rfl) ⟨1439691, by rfl⟩ : syracuseStep 3839177 = 2879383) B2879383
theorem B2559451 : Blo 2243435 2559451 := bstep (se 1 (by rfl) ⟨1919588, by rfl⟩ : syracuseStep 2559451 = 3839177) B3839177
theorem B3412601 : Blo 2243435 3412601 := bstep (se 2 (by rfl) ⟨1279725, by rfl⟩ : syracuseStep 3412601 = 2559451) B2559451
theorem B2275067 : Blo 2243435 2275067 := bstep (se 1 (by rfl) ⟨1706300, by rfl⟩ : syracuseStep 2275067 = 3412601) B3412601
theorem B6066845 : Blo 2243435 6066845 := bstep (se 3 (by rfl) ⟨1137533, by rfl⟩ : syracuseStep 6066845 = 2275067) B2275067
theorem B4044563 : Blo 2243435 4044563 := bstep (se 1 (by rfl) ⟨3033422, by rfl⟩ : syracuseStep 4044563 = 6066845) B6066845
theorem B2696375 : Blo 2243435 2696375 := bstep (se 1 (by rfl) ⟨2022281, by rfl⟩ : syracuseStep 2696375 = 4044563) B4044563
theorem B7190333 : Blo 2243435 7190333 := bstep (se 3 (by rfl) ⟨1348187, by rfl⟩ : syracuseStep 7190333 = 2696375) B2696375
theorem B4793555 : Blo 2243435 4793555 := bstep (se 1 (by rfl) ⟨3595166, by rfl⟩ : syracuseStep 4793555 = 7190333) B7190333
theorem B3195703 : Blo 2243435 3195703 := bstep (se 1 (by rfl) ⟨2396777, by rfl⟩ : syracuseStep 3195703 = 4793555) B4793555
theorem B4260937 : Blo 2243435 4260937 := bstep (se 2 (by rfl) ⟨1597851, by rfl⟩ : syracuseStep 4260937 = 3195703) B3195703
theorem B5681249 : Blo 2243435 5681249 := bstep (se 2 (by rfl) ⟨2130468, by rfl⟩ : syracuseStep 5681249 = 4260937) B4260937
theorem B3787499 : Blo 2243435 3787499 := bstep (se 1 (by rfl) ⟨2840624, by rfl⟩ : syracuseStep 3787499 = 5681249) B5681249
theorem B2524999 : Blo 2243435 2524999 := bstep (se 1 (by rfl) ⟨1893749, by rfl⟩ : syracuseStep 2524999 = 3787499) B3787499
theorem B3366665 : Blo 2243435 3366665 := bstep (se 2 (by rfl) ⟨1262499, by rfl⟩ : syracuseStep 3366665 = 2524999) B2524999
theorem B2244443 : Blo 2243435 2244443 := bstep (se 1 (by rfl) ⟨1683332, by rfl⟩ : syracuseStep 2244443 = 3366665) B3366665
theorem B11362517 : Blo 2243435 11362517 := bbase (se 7 (by rfl) ⟨133154, by rfl⟩ : syracuseStep 11362517 = 266309) (by norm_num)
theorem B7575011 : Blo 2243435 7575011 := bstep (se 1 (by rfl) ⟨5681258, by rfl⟩ : syracuseStep 7575011 = 11362517) B11362517
theorem B5050007 : Blo 2243435 5050007 := bstep (se 1 (by rfl) ⟨3787505, by rfl⟩ : syracuseStep 5050007 = 7575011) B7575011
theorem B3366671 : Blo 2243435 3366671 := bstep (se 1 (by rfl) ⟨2525003, by rfl⟩ : syracuseStep 3366671 = 5050007) B5050007
theorem B2244447 : Blo 2243435 2244447 := bstep (se 1 (by rfl) ⟨1683335, by rfl⟩ : syracuseStep 2244447 = 3366671) B3366671
theorem B3366677 : Blo 2243435 3366677 := bbase (se 6 (by rfl) ⟨78906, by rfl⟩ : syracuseStep 3366677 = 157813) (by norm_num)
theorem B2244451 : Blo 2243435 2244451 := bstep (se 1 (by rfl) ⟨1683338, by rfl⟩ : syracuseStep 2244451 = 3366677) B3366677
theorem B48534997 : Blo 2243435 48534997 := bbase (se 7 (by rfl) ⟨568769, by rfl⟩ : syracuseStep 48534997 = 1137539) (by norm_num)
theorem B64713329 : Blo 2243435 64713329 := bstep (se 2 (by rfl) ⟨24267498, by rfl⟩ : syracuseStep 64713329 = 48534997) B48534997
theorem B43142219 : Blo 2243435 43142219 := bstep (se 1 (by rfl) ⟨32356664, by rfl⟩ : syracuseStep 43142219 = 64713329) B64713329
theorem B28761479 : Blo 2243435 28761479 := bstep (se 1 (by rfl) ⟨21571109, by rfl⟩ : syracuseStep 28761479 = 43142219) B43142219
theorem B19174319 : Blo 2243435 19174319 := bstep (se 1 (by rfl) ⟨14380739, by rfl⟩ : syracuseStep 19174319 = 28761479) B28761479
theorem B12782879 : Blo 2243435 12782879 := bstep (se 1 (by rfl) ⟨9587159, by rfl⟩ : syracuseStep 12782879 = 19174319) B19174319
theorem B8521919 : Blo 2243435 8521919 := bstep (se 1 (by rfl) ⟨6391439, by rfl⟩ : syracuseStep 8521919 = 12782879) B12782879
theorem B5681279 : Blo 2243435 5681279 := bstep (se 1 (by rfl) ⟨4260959, by rfl⟩ : syracuseStep 5681279 = 8521919) B8521919
theorem B3787519 : Blo 2243435 3787519 := bstep (se 1 (by rfl) ⟨2840639, by rfl⟩ : syracuseStep 3787519 = 5681279) B5681279
theorem B5050025 : Blo 2243435 5050025 := bstep (se 2 (by rfl) ⟨1893759, by rfl⟩ : syracuseStep 5050025 = 3787519) B3787519
theorem B3366683 : Blo 2243435 3366683 := bstep (se 1 (by rfl) ⟨2525012, by rfl⟩ : syracuseStep 3366683 = 5050025) B5050025
theorem B2244455 : Blo 2243435 2244455 := bstep (se 1 (by rfl) ⟨1683341, by rfl⟩ : syracuseStep 2244455 = 3366683) B3366683
theorem B2525017 : Blo 2243435 2525017 := bbase (se 2 (by rfl) ⟨946881, by rfl⟩ : syracuseStep 2525017 = 1893763) (by norm_num)
theorem B3366689 : Blo 2243435 3366689 := bstep (se 2 (by rfl) ⟨1262508, by rfl⟩ : syracuseStep 3366689 = 2525017) B2525017
theorem B2244459 : Blo 2243435 2244459 := bstep (se 1 (by rfl) ⟨1683344, by rfl⟩ : syracuseStep 2244459 = 3366689) B3366689
theorem B4793597 : Blo 2243435 4793597 := bbase (se 3 (by rfl) ⟨898799, by rfl⟩ : syracuseStep 4793597 = 1797599) (by norm_num)
theorem B3195731 : Blo 2243435 3195731 := bstep (se 1 (by rfl) ⟨2396798, by rfl⟩ : syracuseStep 3195731 = 4793597) B4793597
theorem B8521949 : Blo 2243435 8521949 := bstep (se 3 (by rfl) ⟨1597865, by rfl⟩ : syracuseStep 8521949 = 3195731) B3195731
theorem B5681299 : Blo 2243435 5681299 := bstep (se 1 (by rfl) ⟨4260974, by rfl⟩ : syracuseStep 5681299 = 8521949) B8521949
theorem B7575065 : Blo 2243435 7575065 := bstep (se 2 (by rfl) ⟨2840649, by rfl⟩ : syracuseStep 7575065 = 5681299) B5681299
theorem B5050043 : Blo 2243435 5050043 := bstep (se 1 (by rfl) ⟨3787532, by rfl⟩ : syracuseStep 5050043 = 7575065) B7575065
theorem B3366695 : Blo 2243435 3366695 := bstep (se 1 (by rfl) ⟨2525021, by rfl⟩ : syracuseStep 3366695 = 5050043) B5050043
theorem B2244463 : Blo 2243435 2244463 := bstep (se 1 (by rfl) ⟨1683347, by rfl⟩ : syracuseStep 2244463 = 3366695) B3366695
theorem B3366701 : Blo 2243435 3366701 := bbase (se 3 (by rfl) ⟨631256, by rfl⟩ : syracuseStep 3366701 = 1262513) (by norm_num)
theorem B2244467 : Blo 2243435 2244467 := bstep (se 1 (by rfl) ⟨1683350, by rfl⟩ : syracuseStep 2244467 = 3366701) B3366701
theorem B5050061 : Blo 2243435 5050061 := bbase (se 3 (by rfl) ⟨946886, by rfl⟩ : syracuseStep 5050061 = 1893773) (by norm_num)
theorem B3366707 : Blo 2243435 3366707 := bstep (se 1 (by rfl) ⟨2525030, by rfl⟩ : syracuseStep 3366707 = 5050061) B5050061
theorem B2244471 : Blo 2243435 2244471 := bstep (se 1 (by rfl) ⟨1683353, by rfl⟩ : syracuseStep 2244471 = 3366707) B3366707
theorem B2840665 : Blo 2243435 2840665 := bbase (se 2 (by rfl) ⟨1065249, by rfl⟩ : syracuseStep 2840665 = 2130499) (by norm_num)
theorem B3787553 : Blo 2243435 3787553 := bstep (se 2 (by rfl) ⟨1420332, by rfl⟩ : syracuseStep 3787553 = 2840665) B2840665
theorem B2525035 : Blo 2243435 2525035 := bstep (se 1 (by rfl) ⟨1893776, by rfl⟩ : syracuseStep 2525035 = 3787553) B3787553
theorem B3366713 : Blo 2243435 3366713 := bstep (se 2 (by rfl) ⟨1262517, by rfl⟩ : syracuseStep 3366713 = 2525035) B2525035
theorem B2244475 : Blo 2243435 2244475 := bstep (se 1 (by rfl) ⟨1683356, by rfl⟩ : syracuseStep 2244475 = 3366713) B3366713
theorem B8089253 : Blo 2243435 8089253 := bbase (se 4 (by rfl) ⟨758367, by rfl⟩ : syracuseStep 8089253 = 1516735) (by norm_num)
theorem B5392835 : Blo 2243435 5392835 := bstep (se 1 (by rfl) ⟨4044626, by rfl⟩ : syracuseStep 5392835 = 8089253) B8089253
theorem B3595223 : Blo 2243435 3595223 := bstep (se 1 (by rfl) ⟨2696417, by rfl⟩ : syracuseStep 3595223 = 5392835) B5392835
theorem B9587261 : Blo 2243435 9587261 := bstep (se 3 (by rfl) ⟨1797611, by rfl⟩ : syracuseStep 9587261 = 3595223) B3595223
theorem B25566029 : Blo 2243435 25566029 := bstep (se 3 (by rfl) ⟨4793630, by rfl⟩ : syracuseStep 25566029 = 9587261) B9587261
theorem B17044019 : Blo 2243435 17044019 := bstep (se 1 (by rfl) ⟨12783014, by rfl⟩ : syracuseStep 17044019 = 25566029) B25566029
theorem B11362679 : Blo 2243435 11362679 := bstep (se 1 (by rfl) ⟨8522009, by rfl⟩ : syracuseStep 11362679 = 17044019) B17044019
theorem B7575119 : Blo 2243435 7575119 := bstep (se 1 (by rfl) ⟨5681339, by rfl⟩ : syracuseStep 7575119 = 11362679) B11362679
theorem B5050079 : Blo 2243435 5050079 := bstep (se 1 (by rfl) ⟨3787559, by rfl⟩ : syracuseStep 5050079 = 7575119) B7575119
theorem B3366719 : Blo 2243435 3366719 := bstep (se 1 (by rfl) ⟨2525039, by rfl⟩ : syracuseStep 3366719 = 5050079) B5050079
theorem B2244479 : Blo 2243435 2244479 := bstep (se 1 (by rfl) ⟨1683359, by rfl⟩ : syracuseStep 2244479 = 3366719) B3366719
theorem B3366725 : Blo 2243435 3366725 := bbase (se 4 (by rfl) ⟨315630, by rfl⟩ : syracuseStep 3366725 = 631261) (by norm_num)
theorem B2244483 : Blo 2243435 2244483 := bstep (se 1 (by rfl) ⟨1683362, by rfl⟩ : syracuseStep 2244483 = 3366725) B3366725
theorem B3787573 : Blo 2243435 3787573 := bbase (se 5 (by rfl) ⟨177542, by rfl⟩ : syracuseStep 3787573 = 355085) (by norm_num)
theorem B5050097 : Blo 2243435 5050097 := bstep (se 2 (by rfl) ⟨1893786, by rfl⟩ : syracuseStep 5050097 = 3787573) B3787573
theorem B3366731 : Blo 2243435 3366731 := bstep (se 1 (by rfl) ⟨2525048, by rfl⟩ : syracuseStep 3366731 = 5050097) B5050097
theorem B2244487 : Blo 2243435 2244487 := bstep (se 1 (by rfl) ⟨1683365, by rfl⟩ : syracuseStep 2244487 = 3366731) B3366731
theorem B2525053 : Blo 2243435 2525053 := bbase (se 3 (by rfl) ⟨473447, by rfl⟩ : syracuseStep 2525053 = 946895) (by norm_num)
theorem B3366737 : Blo 2243435 3366737 := bstep (se 2 (by rfl) ⟨1262526, by rfl⟩ : syracuseStep 3366737 = 2525053) B2525053
theorem B2244491 : Blo 2243435 2244491 := bstep (se 1 (by rfl) ⟨1683368, by rfl⟩ : syracuseStep 2244491 = 3366737) B3366737
theorem B7575173 : Blo 2243435 7575173 := bbase (se 4 (by rfl) ⟨710172, by rfl⟩ : syracuseStep 7575173 = 1420345) (by norm_num)
theorem B5050115 : Blo 2243435 5050115 := bstep (se 1 (by rfl) ⟨3787586, by rfl⟩ : syracuseStep 5050115 = 7575173) B7575173
theorem B3366743 : Blo 2243435 3366743 := bstep (se 1 (by rfl) ⟨2525057, by rfl⟩ : syracuseStep 3366743 = 5050115) B5050115
theorem B2244495 : Blo 2243435 2244495 := bstep (se 1 (by rfl) ⟨1683371, by rfl⟩ : syracuseStep 2244495 = 3366743) B3366743
theorem B3366749 : Blo 2243435 3366749 := bbase (se 3 (by rfl) ⟨631265, by rfl⟩ : syracuseStep 3366749 = 1262531) (by norm_num)
theorem B2244499 : Blo 2243435 2244499 := bstep (se 1 (by rfl) ⟨1683374, by rfl⟩ : syracuseStep 2244499 = 3366749) B3366749
theorem B5050133 : Blo 2243435 5050133 := bbase (se 6 (by rfl) ⟨118362, by rfl⟩ : syracuseStep 5050133 = 236725) (by norm_num)
theorem B3366755 : Blo 2243435 3366755 := bstep (se 1 (by rfl) ⟨2525066, by rfl⟩ : syracuseStep 3366755 = 5050133) B5050133
theorem B2244503 : Blo 2243435 2244503 := bstep (se 1 (by rfl) ⟨1683377, by rfl⟩ : syracuseStep 2244503 = 3366755) B3366755
theorem B8522117 : Blo 2243435 8522117 := bbase (se 4 (by rfl) ⟨798948, by rfl⟩ : syracuseStep 8522117 = 1597897) (by norm_num)
theorem B5681411 : Blo 2243435 5681411 := bstep (se 1 (by rfl) ⟨4261058, by rfl⟩ : syracuseStep 5681411 = 8522117) B8522117
theorem B3787607 : Blo 2243435 3787607 := bstep (se 1 (by rfl) ⟨2840705, by rfl⟩ : syracuseStep 3787607 = 5681411) B5681411
theorem B2525071 : Blo 2243435 2525071 := bstep (se 1 (by rfl) ⟨1893803, by rfl⟩ : syracuseStep 2525071 = 3787607) B3787607
theorem B3366761 : Blo 2243435 3366761 := bstep (se 2 (by rfl) ⟨1262535, by rfl⟩ : syracuseStep 3366761 = 2525071) B2525071
theorem B2244507 : Blo 2243435 2244507 := bstep (se 1 (by rfl) ⟨1683380, by rfl⟩ : syracuseStep 2244507 = 3366761) B3366761
theorem B7190549 : Blo 2243435 7190549 := bbase (se 6 (by rfl) ⟨168528, by rfl⟩ : syracuseStep 7190549 = 337057) (by norm_num)
theorem B4793699 : Blo 2243435 4793699 := bstep (se 1 (by rfl) ⟨3595274, by rfl⟩ : syracuseStep 4793699 = 7190549) B7190549
theorem B12783197 : Blo 2243435 12783197 := bstep (se 3 (by rfl) ⟨2396849, by rfl⟩ : syracuseStep 12783197 = 4793699) B4793699
theorem B8522131 : Blo 2243435 8522131 := bstep (se 1 (by rfl) ⟨6391598, by rfl⟩ : syracuseStep 8522131 = 12783197) B12783197
theorem B11362841 : Blo 2243435 11362841 := bstep (se 2 (by rfl) ⟨4261065, by rfl⟩ : syracuseStep 11362841 = 8522131) B8522131
theorem B7575227 : Blo 2243435 7575227 := bstep (se 1 (by rfl) ⟨5681420, by rfl⟩ : syracuseStep 7575227 = 11362841) B11362841
theorem B5050151 : Blo 2243435 5050151 := bstep (se 1 (by rfl) ⟨3787613, by rfl⟩ : syracuseStep 5050151 = 7575227) B7575227
theorem B3366767 : Blo 2243435 3366767 := bstep (se 1 (by rfl) ⟨2525075, by rfl⟩ : syracuseStep 3366767 = 5050151) B5050151
theorem B2244511 : Blo 2243435 2244511 := bstep (se 1 (by rfl) ⟨1683383, by rfl⟩ : syracuseStep 2244511 = 3366767) B3366767
theorem B3366773 : Blo 2243435 3366773 := bbase (se 5 (by rfl) ⟨157817, by rfl⟩ : syracuseStep 3366773 = 315635) (by norm_num)
theorem B2244515 : Blo 2243435 2244515 := bstep (se 1 (by rfl) ⟨1683386, by rfl⟩ : syracuseStep 2244515 = 3366773) B3366773
theorem B4793717 : Blo 2243435 4793717 := bbase (se 5 (by rfl) ⟨224705, by rfl⟩ : syracuseStep 4793717 = 449411) (by norm_num)
theorem B3195811 : Blo 2243435 3195811 := bstep (se 1 (by rfl) ⟨2396858, by rfl⟩ : syracuseStep 3195811 = 4793717) B4793717
theorem B4261081 : Blo 2243435 4261081 := bstep (se 2 (by rfl) ⟨1597905, by rfl⟩ : syracuseStep 4261081 = 3195811) B3195811
theorem B5681441 : Blo 2243435 5681441 := bstep (se 2 (by rfl) ⟨2130540, by rfl⟩ : syracuseStep 5681441 = 4261081) B4261081
theorem B3787627 : Blo 2243435 3787627 := bstep (se 1 (by rfl) ⟨2840720, by rfl⟩ : syracuseStep 3787627 = 5681441) B5681441
theorem B5050169 : Blo 2243435 5050169 := bstep (se 2 (by rfl) ⟨1893813, by rfl⟩ : syracuseStep 5050169 = 3787627) B3787627
theorem B3366779 : Blo 2243435 3366779 := bstep (se 1 (by rfl) ⟨2525084, by rfl⟩ : syracuseStep 3366779 = 5050169) B5050169
theorem B2244519 : Blo 2243435 2244519 := bstep (se 1 (by rfl) ⟨1683389, by rfl⟩ : syracuseStep 2244519 = 3366779) B3366779
theorem B2525089 : Blo 2243435 2525089 := bbase (se 2 (by rfl) ⟨946908, by rfl⟩ : syracuseStep 2525089 = 1893817) (by norm_num)
theorem B3366785 : Blo 2243435 3366785 := bstep (se 2 (by rfl) ⟨1262544, by rfl⟩ : syracuseStep 3366785 = 2525089) B2525089
theorem B2244523 : Blo 2243435 2244523 := bstep (se 1 (by rfl) ⟨1683392, by rfl⟩ : syracuseStep 2244523 = 3366785) B3366785
theorem B5681461 : Blo 2243435 5681461 := bbase (se 5 (by rfl) ⟨266318, by rfl⟩ : syracuseStep 5681461 = 532637) (by norm_num)
theorem B7575281 : Blo 2243435 7575281 := bstep (se 2 (by rfl) ⟨2840730, by rfl⟩ : syracuseStep 7575281 = 5681461) B5681461
theorem B5050187 : Blo 2243435 5050187 := bstep (se 1 (by rfl) ⟨3787640, by rfl⟩ : syracuseStep 5050187 = 7575281) B7575281
theorem B3366791 : Blo 2243435 3366791 := bstep (se 1 (by rfl) ⟨2525093, by rfl⟩ : syracuseStep 3366791 = 5050187) B5050187
theorem B2244527 : Blo 2243435 2244527 := bstep (se 1 (by rfl) ⟨1683395, by rfl⟩ : syracuseStep 2244527 = 3366791) B3366791
theorem B3366797 : Blo 2243435 3366797 := bbase (se 3 (by rfl) ⟨631274, by rfl⟩ : syracuseStep 3366797 = 1262549) (by norm_num)
theorem B2244531 : Blo 2243435 2244531 := bstep (se 1 (by rfl) ⟨1683398, by rfl⟩ : syracuseStep 2244531 = 3366797) B3366797
theorem B5050205 : Blo 2243435 5050205 := bbase (se 3 (by rfl) ⟨946913, by rfl⟩ : syracuseStep 5050205 = 1893827) (by norm_num)
theorem B3366803 : Blo 2243435 3366803 := bstep (se 1 (by rfl) ⟨2525102, by rfl⟩ : syracuseStep 3366803 = 5050205) B5050205
theorem B2244535 : Blo 2243435 2244535 := bstep (se 1 (by rfl) ⟨1683401, by rfl⟩ : syracuseStep 2244535 = 3366803) B3366803
theorem B3787661 : Blo 2243435 3787661 := bbase (se 3 (by rfl) ⟨710186, by rfl⟩ : syracuseStep 3787661 = 1420373) (by norm_num)
theorem B2525107 : Blo 2243435 2525107 := bstep (se 1 (by rfl) ⟨1893830, by rfl⟩ : syracuseStep 2525107 = 3787661) B3787661
theorem B3366809 : Blo 2243435 3366809 := bstep (se 2 (by rfl) ⟨1262553, by rfl⟩ : syracuseStep 3366809 = 2525107) B2525107
theorem B2244539 : Blo 2243435 2244539 := bstep (se 1 (by rfl) ⟨1683404, by rfl⟩ : syracuseStep 2244539 = 3366809) B3366809
theorem B11518037 : Blo 2243435 11518037 := bbase (se 8 (by rfl) ⟨67488, by rfl⟩ : syracuseStep 11518037 = 134977) (by norm_num)
theorem B7678691 : Blo 2243435 7678691 := bstep (se 1 (by rfl) ⟨5759018, by rfl⟩ : syracuseStep 7678691 = 11518037) B11518037
theorem B5119127 : Blo 2243435 5119127 := bstep (se 1 (by rfl) ⟨3839345, by rfl⟩ : syracuseStep 5119127 = 7678691) B7678691
theorem B3412751 : Blo 2243435 3412751 := bstep (se 1 (by rfl) ⟨2559563, by rfl⟩ : syracuseStep 3412751 = 5119127) B5119127
theorem B9100669 : Blo 2243435 9100669 := bstep (se 3 (by rfl) ⟨1706375, by rfl⟩ : syracuseStep 9100669 = 3412751) B3412751
theorem B12134225 : Blo 2243435 12134225 := bstep (se 2 (by rfl) ⟨4550334, by rfl⟩ : syracuseStep 12134225 = 9100669) B9100669
theorem B8089483 : Blo 2243435 8089483 := bstep (se 1 (by rfl) ⟨6067112, by rfl⟩ : syracuseStep 8089483 = 12134225) B12134225
theorem B10785977 : Blo 2243435 10785977 := bstep (se 2 (by rfl) ⟨4044741, by rfl⟩ : syracuseStep 10785977 = 8089483) B8089483
theorem B7190651 : Blo 2243435 7190651 := bstep (se 1 (by rfl) ⟨5392988, by rfl⟩ : syracuseStep 7190651 = 10785977) B10785977
theorem B19175069 : Blo 2243435 19175069 := bstep (se 3 (by rfl) ⟨3595325, by rfl⟩ : syracuseStep 19175069 = 7190651) B7190651
theorem B12783379 : Blo 2243435 12783379 := bstep (se 1 (by rfl) ⟨9587534, by rfl⟩ : syracuseStep 12783379 = 19175069) B19175069
theorem B17044505 : Blo 2243435 17044505 := bstep (se 2 (by rfl) ⟨6391689, by rfl⟩ : syracuseStep 17044505 = 12783379) B12783379
theorem B11363003 : Blo 2243435 11363003 := bstep (se 1 (by rfl) ⟨8522252, by rfl⟩ : syracuseStep 11363003 = 17044505) B17044505
theorem B7575335 : Blo 2243435 7575335 := bstep (se 1 (by rfl) ⟨5681501, by rfl⟩ : syracuseStep 7575335 = 11363003) B11363003
theorem B5050223 : Blo 2243435 5050223 := bstep (se 1 (by rfl) ⟨3787667, by rfl⟩ : syracuseStep 5050223 = 7575335) B7575335
theorem B3366815 : Blo 2243435 3366815 := bstep (se 1 (by rfl) ⟨2525111, by rfl⟩ : syracuseStep 3366815 = 5050223) B5050223
theorem B2244543 : Blo 2243435 2244543 := bstep (se 1 (by rfl) ⟨1683407, by rfl⟩ : syracuseStep 2244543 = 3366815) B3366815
theorem B3366821 : Blo 2243435 3366821 := bbase (se 4 (by rfl) ⟨315639, by rfl⟩ : syracuseStep 3366821 = 631279) (by norm_num)
theorem B2244547 : Blo 2243435 2244547 := bstep (se 1 (by rfl) ⟨1683410, by rfl⟩ : syracuseStep 2244547 = 3366821) B3366821
theorem B2840761 : Blo 2243435 2840761 := bbase (se 2 (by rfl) ⟨1065285, by rfl⟩ : syracuseStep 2840761 = 2130571) (by norm_num)
theorem B3787681 : Blo 2243435 3787681 := bstep (se 2 (by rfl) ⟨1420380, by rfl⟩ : syracuseStep 3787681 = 2840761) B2840761
theorem B5050241 : Blo 2243435 5050241 := bstep (se 2 (by rfl) ⟨1893840, by rfl⟩ : syracuseStep 5050241 = 3787681) B3787681
theorem B3366827 : Blo 2243435 3366827 := bstep (se 1 (by rfl) ⟨2525120, by rfl⟩ : syracuseStep 3366827 = 5050241) B5050241
theorem B2244551 : Blo 2243435 2244551 := bstep (se 1 (by rfl) ⟨1683413, by rfl⟩ : syracuseStep 2244551 = 3366827) B3366827
theorem B2525125 : Blo 2243435 2525125 := bbase (se 4 (by rfl) ⟨236730, by rfl⟩ : syracuseStep 2525125 = 473461) (by norm_num)
theorem B3366833 : Blo 2243435 3366833 := bstep (se 2 (by rfl) ⟨1262562, by rfl⟩ : syracuseStep 3366833 = 2525125) B2525125
theorem B2244555 : Blo 2243435 2244555 := bstep (se 1 (by rfl) ⟨1683416, by rfl⟩ : syracuseStep 2244555 = 3366833) B3366833
theorem B4261157 : Blo 2243435 4261157 := bbase (se 4 (by rfl) ⟨399483, by rfl⟩ : syracuseStep 4261157 = 798967) (by norm_num)
theorem B2840771 : Blo 2243435 2840771 := bstep (se 1 (by rfl) ⟨2130578, by rfl⟩ : syracuseStep 2840771 = 4261157) B4261157
theorem B7575389 : Blo 2243435 7575389 := bstep (se 3 (by rfl) ⟨1420385, by rfl⟩ : syracuseStep 7575389 = 2840771) B2840771
theorem B5050259 : Blo 2243435 5050259 := bstep (se 1 (by rfl) ⟨3787694, by rfl⟩ : syracuseStep 5050259 = 7575389) B7575389
theorem B3366839 : Blo 2243435 3366839 := bstep (se 1 (by rfl) ⟨2525129, by rfl⟩ : syracuseStep 3366839 = 5050259) B5050259
theorem B2244559 : Blo 2243435 2244559 := bstep (se 1 (by rfl) ⟨1683419, by rfl⟩ : syracuseStep 2244559 = 3366839) B3366839
theorem B3366845 : Blo 2243435 3366845 := bbase (se 3 (by rfl) ⟨631283, by rfl⟩ : syracuseStep 3366845 = 1262567) (by norm_num)
theorem B2244563 : Blo 2243435 2244563 := bstep (se 1 (by rfl) ⟨1683422, by rfl⟩ : syracuseStep 2244563 = 3366845) B3366845
theorem B5050277 : Blo 2243435 5050277 := bbase (se 4 (by rfl) ⟨473463, by rfl⟩ : syracuseStep 5050277 = 946927) (by norm_num)
theorem B3366851 : Blo 2243435 3366851 := bstep (se 1 (by rfl) ⟨2525138, by rfl⟩ : syracuseStep 3366851 = 5050277) B5050277
theorem B2244567 : Blo 2243435 2244567 := bstep (se 1 (by rfl) ⟨1683425, by rfl⟩ : syracuseStep 2244567 = 3366851) B3366851
theorem B5681573 : Blo 2243435 5681573 := bbase (se 4 (by rfl) ⟨532647, by rfl⟩ : syracuseStep 5681573 = 1065295) (by norm_num)
theorem B3787715 : Blo 2243435 3787715 := bstep (se 1 (by rfl) ⟨2840786, by rfl⟩ : syracuseStep 3787715 = 5681573) B5681573
theorem B2525143 : Blo 2243435 2525143 := bstep (se 1 (by rfl) ⟨1893857, by rfl⟩ : syracuseStep 2525143 = 3787715) B3787715
theorem B3366857 : Blo 2243435 3366857 := bstep (se 2 (by rfl) ⟨1262571, by rfl⟩ : syracuseStep 3366857 = 2525143) B2525143
theorem B2244571 : Blo 2243435 2244571 := bstep (se 1 (by rfl) ⟨1683428, by rfl⟩ : syracuseStep 2244571 = 3366857) B3366857
theorem B6391781 : Blo 2243435 6391781 := bbase (se 4 (by rfl) ⟨599229, by rfl⟩ : syracuseStep 6391781 = 1198459) (by norm_num)
theorem B4261187 : Blo 2243435 4261187 := bstep (se 1 (by rfl) ⟨3195890, by rfl⟩ : syracuseStep 4261187 = 6391781) B6391781
theorem B11363165 : Blo 2243435 11363165 := bstep (se 3 (by rfl) ⟨2130593, by rfl⟩ : syracuseStep 11363165 = 4261187) B4261187
theorem B7575443 : Blo 2243435 7575443 := bstep (se 1 (by rfl) ⟨5681582, by rfl⟩ : syracuseStep 7575443 = 11363165) B11363165
theorem B5050295 : Blo 2243435 5050295 := bstep (se 1 (by rfl) ⟨3787721, by rfl⟩ : syracuseStep 5050295 = 7575443) B7575443
theorem B3366863 : Blo 2243435 3366863 := bstep (se 1 (by rfl) ⟨2525147, by rfl⟩ : syracuseStep 3366863 = 5050295) B5050295
theorem B2244575 : Blo 2243435 2244575 := bstep (se 1 (by rfl) ⟨1683431, by rfl⟩ : syracuseStep 2244575 = 3366863) B3366863
theorem B3366869 : Blo 2243435 3366869 := bbase (se 7 (by rfl) ⟨39455, by rfl⟩ : syracuseStep 3366869 = 78911) (by norm_num)
theorem B2244579 : Blo 2243435 2244579 := bstep (se 1 (by rfl) ⟨1683434, by rfl⟩ : syracuseStep 2244579 = 3366869) B3366869
theorem B8522405 : Blo 2243435 8522405 := bbase (se 4 (by rfl) ⟨798975, by rfl⟩ : syracuseStep 8522405 = 1597951) (by norm_num)
theorem B5681603 : Blo 2243435 5681603 := bstep (se 1 (by rfl) ⟨4261202, by rfl⟩ : syracuseStep 5681603 = 8522405) B8522405
theorem B3787735 : Blo 2243435 3787735 := bstep (se 1 (by rfl) ⟨2840801, by rfl⟩ : syracuseStep 3787735 = 5681603) B5681603
theorem B5050313 : Blo 2243435 5050313 := bstep (se 2 (by rfl) ⟨1893867, by rfl⟩ : syracuseStep 5050313 = 3787735) B3787735
theorem B3366875 : Blo 2243435 3366875 := bstep (se 1 (by rfl) ⟨2525156, by rfl⟩ : syracuseStep 3366875 = 5050313) B5050313
theorem B2244583 : Blo 2243435 2244583 := bstep (se 1 (by rfl) ⟨1683437, by rfl⟩ : syracuseStep 2244583 = 3366875) B3366875
theorem B2525161 : Blo 2243435 2525161 := bbase (se 2 (by rfl) ⟨946935, by rfl⟩ : syracuseStep 2525161 = 1893871) (by norm_num)
theorem B3366881 : Blo 2243435 3366881 := bstep (se 2 (by rfl) ⟨1262580, by rfl⟩ : syracuseStep 3366881 = 2525161) B2525161
theorem B2244587 : Blo 2243435 2244587 := bstep (se 1 (by rfl) ⟨1683440, by rfl⟩ : syracuseStep 2244587 = 3366881) B3366881
theorem B4044829 : Blo 2243435 4044829 := bbase (se 3 (by rfl) ⟨758405, by rfl⟩ : syracuseStep 4044829 = 1516811) (by norm_num)
theorem B5393105 : Blo 2243435 5393105 := bstep (se 2 (by rfl) ⟨2022414, by rfl⟩ : syracuseStep 5393105 = 4044829) B4044829
theorem B3595403 : Blo 2243435 3595403 := bstep (se 1 (by rfl) ⟨2696552, by rfl⟩ : syracuseStep 3595403 = 5393105) B5393105
theorem B2396935 : Blo 2243435 2396935 := bstep (se 1 (by rfl) ⟨1797701, by rfl⟩ : syracuseStep 2396935 = 3595403) B3595403
theorem B12783653 : Blo 2243435 12783653 := bstep (se 4 (by rfl) ⟨1198467, by rfl⟩ : syracuseStep 12783653 = 2396935) B2396935
theorem B8522435 : Blo 2243435 8522435 := bstep (se 1 (by rfl) ⟨6391826, by rfl⟩ : syracuseStep 8522435 = 12783653) B12783653
theorem B5681623 : Blo 2243435 5681623 := bstep (se 1 (by rfl) ⟨4261217, by rfl⟩ : syracuseStep 5681623 = 8522435) B8522435
theorem B7575497 : Blo 2243435 7575497 := bstep (se 2 (by rfl) ⟨2840811, by rfl⟩ : syracuseStep 7575497 = 5681623) B5681623
theorem B5050331 : Blo 2243435 5050331 := bstep (se 1 (by rfl) ⟨3787748, by rfl⟩ : syracuseStep 5050331 = 7575497) B7575497
theorem B3366887 : Blo 2243435 3366887 := bstep (se 1 (by rfl) ⟨2525165, by rfl⟩ : syracuseStep 3366887 = 5050331) B5050331
theorem B2244591 : Blo 2243435 2244591 := bstep (se 1 (by rfl) ⟨1683443, by rfl⟩ : syracuseStep 2244591 = 3366887) B3366887
theorem B3366893 : Blo 2243435 3366893 := bbase (se 3 (by rfl) ⟨631292, by rfl⟩ : syracuseStep 3366893 = 1262585) (by norm_num)
theorem B2244595 : Blo 2243435 2244595 := bstep (se 1 (by rfl) ⟨1683446, by rfl⟩ : syracuseStep 2244595 = 3366893) B3366893
theorem B5050349 : Blo 2243435 5050349 := bbase (se 3 (by rfl) ⟨946940, by rfl⟩ : syracuseStep 5050349 = 1893881) (by norm_num)
theorem B3366899 : Blo 2243435 3366899 := bstep (se 1 (by rfl) ⟨2525174, by rfl⟩ : syracuseStep 3366899 = 5050349) B5050349
theorem B2244599 : Blo 2243435 2244599 := bstep (se 1 (by rfl) ⟨1683449, by rfl⟩ : syracuseStep 2244599 = 3366899) B3366899
theorem B7388405 : Blo 2243435 7388405 := bbase (se 5 (by rfl) ⟨346331, by rfl⟩ : syracuseStep 7388405 = 692663) (by norm_num)
theorem B4925603 : Blo 2243435 4925603 := bstep (se 1 (by rfl) ⟨3694202, by rfl⟩ : syracuseStep 4925603 = 7388405) B7388405
theorem B3283735 : Blo 2243435 3283735 := bstep (se 1 (by rfl) ⟨2462801, by rfl⟩ : syracuseStep 3283735 = 4925603) B4925603
theorem B4378313 : Blo 2243435 4378313 := bstep (se 2 (by rfl) ⟨1641867, by rfl⟩ : syracuseStep 4378313 = 3283735) B3283735
theorem B11675501 : Blo 2243435 11675501 := bstep (se 3 (by rfl) ⟨2189156, by rfl⟩ : syracuseStep 11675501 = 4378313) B4378313
theorem B7783667 : Blo 2243435 7783667 := bstep (se 1 (by rfl) ⟨5837750, by rfl⟩ : syracuseStep 7783667 = 11675501) B11675501
theorem B5189111 : Blo 2243435 5189111 := bstep (se 1 (by rfl) ⟨3891833, by rfl⟩ : syracuseStep 5189111 = 7783667) B7783667
theorem B3459407 : Blo 2243435 3459407 := bstep (se 1 (by rfl) ⟨2594555, by rfl⟩ : syracuseStep 3459407 = 5189111) B5189111
theorem B9225085 : Blo 2243435 9225085 := bstep (se 3 (by rfl) ⟨1729703, by rfl⟩ : syracuseStep 9225085 = 3459407) B3459407
theorem B12300113 : Blo 2243435 12300113 := bstep (se 2 (by rfl) ⟨4612542, by rfl⟩ : syracuseStep 12300113 = 9225085) B9225085
theorem B32800301 : Blo 2243435 32800301 := bstep (se 3 (by rfl) ⟨6150056, by rfl⟩ : syracuseStep 32800301 = 12300113) B12300113
theorem B21866867 : Blo 2243435 21866867 := bstep (se 1 (by rfl) ⟨16400150, by rfl⟩ : syracuseStep 21866867 = 32800301) B32800301
theorem B14577911 : Blo 2243435 14577911 := bstep (se 1 (by rfl) ⟨10933433, by rfl⟩ : syracuseStep 14577911 = 21866867) B21866867
theorem B9718607 : Blo 2243435 9718607 := bstep (se 1 (by rfl) ⟨7288955, by rfl⟩ : syracuseStep 9718607 = 14577911) B14577911
theorem B6479071 : Blo 2243435 6479071 := bstep (se 1 (by rfl) ⟨4859303, by rfl⟩ : syracuseStep 6479071 = 9718607) B9718607
theorem B34555045 : Blo 2243435 34555045 := bstep (se 4 (by rfl) ⟨3239535, by rfl⟩ : syracuseStep 34555045 = 6479071) B6479071
theorem B46073393 : Blo 2243435 46073393 := bstep (se 2 (by rfl) ⟨17277522, by rfl⟩ : syracuseStep 46073393 = 34555045) B34555045
theorem B30715595 : Blo 2243435 30715595 := bstep (se 1 (by rfl) ⟨23036696, by rfl⟩ : syracuseStep 30715595 = 46073393) B46073393
theorem B20477063 : Blo 2243435 20477063 := bstep (se 1 (by rfl) ⟨15357797, by rfl⟩ : syracuseStep 20477063 = 30715595) B30715595
theorem B13651375 : Blo 2243435 13651375 := bstep (se 1 (by rfl) ⟨10238531, by rfl⟩ : syracuseStep 13651375 = 20477063) B20477063
theorem B18201833 : Blo 2243435 18201833 := bstep (se 2 (by rfl) ⟨6825687, by rfl⟩ : syracuseStep 18201833 = 13651375) B13651375
theorem B12134555 : Blo 2243435 12134555 := bstep (se 1 (by rfl) ⟨9100916, by rfl⟩ : syracuseStep 12134555 = 18201833) B18201833
theorem B8089703 : Blo 2243435 8089703 := bstep (se 1 (by rfl) ⟨6067277, by rfl⟩ : syracuseStep 8089703 = 12134555) B12134555
theorem B5393135 : Blo 2243435 5393135 := bstep (se 1 (by rfl) ⟨4044851, by rfl⟩ : syracuseStep 5393135 = 8089703) B8089703
theorem B3595423 : Blo 2243435 3595423 := bstep (se 1 (by rfl) ⟨2696567, by rfl⟩ : syracuseStep 3595423 = 5393135) B5393135
theorem B4793897 : Blo 2243435 4793897 := bstep (se 2 (by rfl) ⟨1797711, by rfl⟩ : syracuseStep 4793897 = 3595423) B3595423
theorem B3195931 : Blo 2243435 3195931 := bstep (se 1 (by rfl) ⟨2396948, by rfl⟩ : syracuseStep 3195931 = 4793897) B4793897
theorem B4261241 : Blo 2243435 4261241 := bstep (se 2 (by rfl) ⟨1597965, by rfl⟩ : syracuseStep 4261241 = 3195931) B3195931
theorem B2840827 : Blo 2243435 2840827 := bstep (se 1 (by rfl) ⟨2130620, by rfl⟩ : syracuseStep 2840827 = 4261241) B4261241
theorem B3787769 : Blo 2243435 3787769 := bstep (se 2 (by rfl) ⟨1420413, by rfl⟩ : syracuseStep 3787769 = 2840827) B2840827
theorem B2525179 : Blo 2243435 2525179 := bstep (se 1 (by rfl) ⟨1893884, by rfl⟩ : syracuseStep 2525179 = 3787769) B3787769
theorem B3366905 : Blo 2243435 3366905 := bstep (se 2 (by rfl) ⟨1262589, by rfl⟩ : syracuseStep 3366905 = 2525179) B2525179
theorem B2244603 : Blo 2243435 2244603 := bstep (se 1 (by rfl) ⟨1683452, by rfl⟩ : syracuseStep 2244603 = 3366905) B3366905
theorem B4859309 : Blo 2243435 4859309 := bbase (se 3 (by rfl) ⟨911120, by rfl⟩ : syracuseStep 4859309 = 1822241) (by norm_num)
theorem B12958157 : Blo 2243435 12958157 := bstep (se 3 (by rfl) ⟨2429654, by rfl⟩ : syracuseStep 12958157 = 4859309) B4859309
theorem B34555085 : Blo 2243435 34555085 := bstep (se 3 (by rfl) ⟨6479078, by rfl⟩ : syracuseStep 34555085 = 12958157) B12958157
theorem B23036723 : Blo 2243435 23036723 := bstep (se 1 (by rfl) ⟨17277542, by rfl⟩ : syracuseStep 23036723 = 34555085) B34555085
theorem B15357815 : Blo 2243435 15357815 := bstep (se 1 (by rfl) ⟨11518361, by rfl⟩ : syracuseStep 15357815 = 23036723) B23036723
theorem B10238543 : Blo 2243435 10238543 := bstep (se 1 (by rfl) ⟨7678907, by rfl⟩ : syracuseStep 10238543 = 15357815) B15357815
theorem B436844501 : Blo 2243435 436844501 := bstep (se 7 (by rfl) ⟨5119271, by rfl⟩ : syracuseStep 436844501 = 10238543) B10238543
theorem B291229667 : Blo 2243435 291229667 := bstep (se 1 (by rfl) ⟨218422250, by rfl⟩ : syracuseStep 291229667 = 436844501) B436844501
theorem B194153111 : Blo 2243435 194153111 := bstep (se 1 (by rfl) ⟨145614833, by rfl⟩ : syracuseStep 194153111 = 291229667) B291229667
theorem B129435407 : Blo 2243435 129435407 := bstep (se 1 (by rfl) ⟨97076555, by rfl⟩ : syracuseStep 129435407 = 194153111) B194153111
theorem B86290271 : Blo 2243435 86290271 := bstep (se 1 (by rfl) ⟨64717703, by rfl⟩ : syracuseStep 86290271 = 129435407) B129435407
theorem B57526847 : Blo 2243435 57526847 := bstep (se 1 (by rfl) ⟨43145135, by rfl⟩ : syracuseStep 57526847 = 86290271) B86290271
theorem B38351231 : Blo 2243435 38351231 := bstep (se 1 (by rfl) ⟨28763423, by rfl⟩ : syracuseStep 38351231 = 57526847) B57526847
theorem B25567487 : Blo 2243435 25567487 := bstep (se 1 (by rfl) ⟨19175615, by rfl⟩ : syracuseStep 25567487 = 38351231) B38351231
theorem B17044991 : Blo 2243435 17044991 := bstep (se 1 (by rfl) ⟨12783743, by rfl⟩ : syracuseStep 17044991 = 25567487) B25567487
theorem B11363327 : Blo 2243435 11363327 := bstep (se 1 (by rfl) ⟨8522495, by rfl⟩ : syracuseStep 11363327 = 17044991) B17044991
theorem B7575551 : Blo 2243435 7575551 := bstep (se 1 (by rfl) ⟨5681663, by rfl⟩ : syracuseStep 7575551 = 11363327) B11363327
theorem B5050367 : Blo 2243435 5050367 := bstep (se 1 (by rfl) ⟨3787775, by rfl⟩ : syracuseStep 5050367 = 7575551) B7575551
theorem B3366911 : Blo 2243435 3366911 := bstep (se 1 (by rfl) ⟨2525183, by rfl⟩ : syracuseStep 3366911 = 5050367) B5050367
theorem B2244607 : Blo 2243435 2244607 := bstep (se 1 (by rfl) ⟨1683455, by rfl⟩ : syracuseStep 2244607 = 3366911) B3366911
theorem B3366917 : Blo 2243435 3366917 := bbase (se 4 (by rfl) ⟨315648, by rfl⟩ : syracuseStep 3366917 = 631297) (by norm_num)
theorem B2244611 : Blo 2243435 2244611 := bstep (se 1 (by rfl) ⟨1683458, by rfl⟩ : syracuseStep 2244611 = 3366917) B3366917
theorem B3787789 : Blo 2243435 3787789 := bbase (se 3 (by rfl) ⟨710210, by rfl⟩ : syracuseStep 3787789 = 1420421) (by norm_num)
theorem B5050385 : Blo 2243435 5050385 := bstep (se 2 (by rfl) ⟨1893894, by rfl⟩ : syracuseStep 5050385 = 3787789) B3787789
theorem B3366923 : Blo 2243435 3366923 := bstep (se 1 (by rfl) ⟨2525192, by rfl⟩ : syracuseStep 3366923 = 5050385) B5050385
theorem B2244615 : Blo 2243435 2244615 := bstep (se 1 (by rfl) ⟨1683461, by rfl⟩ : syracuseStep 2244615 = 3366923) B3366923
theorem B2525197 : Blo 2243435 2525197 := bbase (se 3 (by rfl) ⟨473474, by rfl⟩ : syracuseStep 2525197 = 946949) (by norm_num)
theorem B3366929 : Blo 2243435 3366929 := bstep (se 2 (by rfl) ⟨1262598, by rfl⟩ : syracuseStep 3366929 = 2525197) B2525197
theorem B2244619 : Blo 2243435 2244619 := bstep (se 1 (by rfl) ⟨1683464, by rfl⟩ : syracuseStep 2244619 = 3366929) B3366929
theorem B7575605 : Blo 2243435 7575605 := bbase (se 5 (by rfl) ⟨355106, by rfl⟩ : syracuseStep 7575605 = 710213) (by norm_num)
theorem B5050403 : Blo 2243435 5050403 := bstep (se 1 (by rfl) ⟨3787802, by rfl⟩ : syracuseStep 5050403 = 7575605) B7575605
theorem B3366935 : Blo 2243435 3366935 := bstep (se 1 (by rfl) ⟨2525201, by rfl⟩ : syracuseStep 3366935 = 5050403) B5050403
theorem B2244623 : Blo 2243435 2244623 := bstep (se 1 (by rfl) ⟨1683467, by rfl⟩ : syracuseStep 2244623 = 3366935) B3366935
theorem B3366941 : Blo 2243435 3366941 := bbase (se 3 (by rfl) ⟨631301, by rfl⟩ : syracuseStep 3366941 = 1262603) (by norm_num)
theorem B2244627 : Blo 2243435 2244627 := bstep (se 1 (by rfl) ⟨1683470, by rfl⟩ : syracuseStep 2244627 = 3366941) B3366941
theorem B5050421 : Blo 2243435 5050421 := bbase (se 5 (by rfl) ⟨236738, by rfl⟩ : syracuseStep 5050421 = 473477) (by norm_num)
theorem B3366947 : Blo 2243435 3366947 := bstep (se 1 (by rfl) ⟨2525210, by rfl⟩ : syracuseStep 3366947 = 5050421) B5050421
theorem B2244631 : Blo 2243435 2244631 := bstep (se 1 (by rfl) ⟨1683473, by rfl⟩ : syracuseStep 2244631 = 3366947) B3366947
theorem B10786421 : Blo 2243435 10786421 := bbase (se 5 (by rfl) ⟨505613, by rfl⟩ : syracuseStep 10786421 = 1011227) (by norm_num)
theorem B7190947 : Blo 2243435 7190947 := bstep (se 1 (by rfl) ⟨5393210, by rfl⟩ : syracuseStep 7190947 = 10786421) B10786421
theorem B9587929 : Blo 2243435 9587929 := bstep (se 2 (by rfl) ⟨3595473, by rfl⟩ : syracuseStep 9587929 = 7190947) B7190947
theorem B12783905 : Blo 2243435 12783905 := bstep (se 2 (by rfl) ⟨4793964, by rfl⟩ : syracuseStep 12783905 = 9587929) B9587929
theorem B8522603 : Blo 2243435 8522603 := bstep (se 1 (by rfl) ⟨6391952, by rfl⟩ : syracuseStep 8522603 = 12783905) B12783905
theorem B5681735 : Blo 2243435 5681735 := bstep (se 1 (by rfl) ⟨4261301, by rfl⟩ : syracuseStep 5681735 = 8522603) B8522603
theorem B3787823 : Blo 2243435 3787823 := bstep (se 1 (by rfl) ⟨2840867, by rfl⟩ : syracuseStep 3787823 = 5681735) B5681735
theorem B2525215 : Blo 2243435 2525215 := bstep (se 1 (by rfl) ⟨1893911, by rfl⟩ : syracuseStep 2525215 = 3787823) B3787823
theorem B3366953 : Blo 2243435 3366953 := bstep (se 2 (by rfl) ⟨1262607, by rfl⟩ : syracuseStep 3366953 = 2525215) B2525215
theorem B2244635 : Blo 2243435 2244635 := bstep (se 1 (by rfl) ⟨1683476, by rfl⟩ : syracuseStep 2244635 = 3366953) B3366953
theorem B2559673 : Blo 2243435 2559673 := bbase (se 2 (by rfl) ⟨959877, by rfl⟩ : syracuseStep 2559673 = 1919755) (by norm_num)
theorem B3412897 : Blo 2243435 3412897 := bstep (se 2 (by rfl) ⟨1279836, by rfl⟩ : syracuseStep 3412897 = 2559673) B2559673
theorem B18202117 : Blo 2243435 18202117 := bstep (se 4 (by rfl) ⟨1706448, by rfl⟩ : syracuseStep 18202117 = 3412897) B3412897
theorem B24269489 : Blo 2243435 24269489 := bstep (se 2 (by rfl) ⟨9101058, by rfl⟩ : syracuseStep 24269489 = 18202117) B18202117
theorem B16179659 : Blo 2243435 16179659 := bstep (se 1 (by rfl) ⟨12134744, by rfl⟩ : syracuseStep 16179659 = 24269489) B24269489
theorem B10786439 : Blo 2243435 10786439 := bstep (se 1 (by rfl) ⟨8089829, by rfl⟩ : syracuseStep 10786439 = 16179659) B16179659
theorem B7190959 : Blo 2243435 7190959 := bstep (se 1 (by rfl) ⟨5393219, by rfl⟩ : syracuseStep 7190959 = 10786439) B10786439
theorem B9587945 : Blo 2243435 9587945 := bstep (se 2 (by rfl) ⟨3595479, by rfl⟩ : syracuseStep 9587945 = 7190959) B7190959
theorem B6391963 : Blo 2243435 6391963 := bstep (se 1 (by rfl) ⟨4793972, by rfl⟩ : syracuseStep 6391963 = 9587945) B9587945
theorem B8522617 : Blo 2243435 8522617 := bstep (se 2 (by rfl) ⟨3195981, by rfl⟩ : syracuseStep 8522617 = 6391963) B6391963
theorem B11363489 : Blo 2243435 11363489 := bstep (se 2 (by rfl) ⟨4261308, by rfl⟩ : syracuseStep 11363489 = 8522617) B8522617
theorem B7575659 : Blo 2243435 7575659 := bstep (se 1 (by rfl) ⟨5681744, by rfl⟩ : syracuseStep 7575659 = 11363489) B11363489
theorem B5050439 : Blo 2243435 5050439 := bstep (se 1 (by rfl) ⟨3787829, by rfl⟩ : syracuseStep 5050439 = 7575659) B7575659
theorem B3366959 : Blo 2243435 3366959 := bstep (se 1 (by rfl) ⟨2525219, by rfl⟩ : syracuseStep 3366959 = 5050439) B5050439
theorem B2244639 : Blo 2243435 2244639 := bstep (se 1 (by rfl) ⟨1683479, by rfl⟩ : syracuseStep 2244639 = 3366959) B3366959
theorem B3366965 : Blo 2243435 3366965 := bbase (se 5 (by rfl) ⟨157826, by rfl⟩ : syracuseStep 3366965 = 315653) (by norm_num)
theorem B2244643 : Blo 2243435 2244643 := bstep (se 1 (by rfl) ⟨1683482, by rfl⟩ : syracuseStep 2244643 = 3366965) B3366965
theorem B5681765 : Blo 2243435 5681765 := bbase (se 4 (by rfl) ⟨532665, by rfl⟩ : syracuseStep 5681765 = 1065331) (by norm_num)
theorem B3787843 : Blo 2243435 3787843 := bstep (se 1 (by rfl) ⟨2840882, by rfl⟩ : syracuseStep 3787843 = 5681765) B5681765
theorem B5050457 : Blo 2243435 5050457 := bstep (se 2 (by rfl) ⟨1893921, by rfl⟩ : syracuseStep 5050457 = 3787843) B3787843
theorem B3366971 : Blo 2243435 3366971 := bstep (se 1 (by rfl) ⟨2525228, by rfl⟩ : syracuseStep 3366971 = 5050457) B5050457
theorem B2244647 : Blo 2243435 2244647 := bstep (se 1 (by rfl) ⟨1683485, by rfl⟩ : syracuseStep 2244647 = 3366971) B3366971
theorem B2525233 : Blo 2243435 2525233 := bbase (se 2 (by rfl) ⟨946962, by rfl⟩ : syracuseStep 2525233 = 1893925) (by norm_num)
theorem B3366977 : Blo 2243435 3366977 := bstep (se 2 (by rfl) ⟨1262616, by rfl⟩ : syracuseStep 3366977 = 2525233) B2525233
theorem B2244651 : Blo 2243435 2244651 := bstep (se 1 (by rfl) ⟨1683488, by rfl⟩ : syracuseStep 2244651 = 3366977) B3366977
theorem B10786517 : Blo 2243435 10786517 := bbase (se 7 (by rfl) ⟨126404, by rfl⟩ : syracuseStep 10786517 = 252809) (by norm_num)
theorem B7191011 : Blo 2243435 7191011 := bstep (se 1 (by rfl) ⟨5393258, by rfl⟩ : syracuseStep 7191011 = 10786517) B10786517
theorem B4794007 : Blo 2243435 4794007 := bstep (se 1 (by rfl) ⟨3595505, by rfl⟩ : syracuseStep 4794007 = 7191011) B7191011
theorem B6392009 : Blo 2243435 6392009 := bstep (se 2 (by rfl) ⟨2397003, by rfl⟩ : syracuseStep 6392009 = 4794007) B4794007
theorem B4261339 : Blo 2243435 4261339 := bstep (se 1 (by rfl) ⟨3196004, by rfl⟩ : syracuseStep 4261339 = 6392009) B6392009
theorem B5681785 : Blo 2243435 5681785 := bstep (se 2 (by rfl) ⟨2130669, by rfl⟩ : syracuseStep 5681785 = 4261339) B4261339
theorem B7575713 : Blo 2243435 7575713 := bstep (se 2 (by rfl) ⟨2840892, by rfl⟩ : syracuseStep 7575713 = 5681785) B5681785
theorem B5050475 : Blo 2243435 5050475 := bstep (se 1 (by rfl) ⟨3787856, by rfl⟩ : syracuseStep 5050475 = 7575713) B7575713
theorem B3366983 : Blo 2243435 3366983 := bstep (se 1 (by rfl) ⟨2525237, by rfl⟩ : syracuseStep 3366983 = 5050475) B5050475
theorem B2244655 : Blo 2243435 2244655 := bstep (se 1 (by rfl) ⟨1683491, by rfl⟩ : syracuseStep 2244655 = 3366983) B3366983
theorem B3366989 : Blo 2243435 3366989 := bbase (se 3 (by rfl) ⟨631310, by rfl⟩ : syracuseStep 3366989 = 1262621) (by norm_num)
theorem B2244659 : Blo 2243435 2244659 := bstep (se 1 (by rfl) ⟨1683494, by rfl⟩ : syracuseStep 2244659 = 3366989) B3366989
theorem B5050493 : Blo 2243435 5050493 := bbase (se 3 (by rfl) ⟨946967, by rfl⟩ : syracuseStep 5050493 = 1893935) (by norm_num)
theorem B3366995 : Blo 2243435 3366995 := bstep (se 1 (by rfl) ⟨2525246, by rfl⟩ : syracuseStep 3366995 = 5050493) B5050493
theorem B2244663 : Blo 2243435 2244663 := bstep (se 1 (by rfl) ⟨1683497, by rfl⟩ : syracuseStep 2244663 = 3366995) B3366995
theorem B3787877 : Blo 2243435 3787877 := bbase (se 4 (by rfl) ⟨355113, by rfl⟩ : syracuseStep 3787877 = 710227) (by norm_num)
theorem B2525251 : Blo 2243435 2525251 := bstep (se 1 (by rfl) ⟨1893938, by rfl⟩ : syracuseStep 2525251 = 3787877) B3787877
theorem B3367001 : Blo 2243435 3367001 := bstep (se 2 (by rfl) ⟨1262625, by rfl⟩ : syracuseStep 3367001 = 2525251) B2525251
theorem B2244667 : Blo 2243435 2244667 := bstep (se 1 (by rfl) ⟨1683500, by rfl⟩ : syracuseStep 2244667 = 3367001) B3367001
theorem B4044973 : Blo 2243435 4044973 := bbase (se 3 (by rfl) ⟨758432, by rfl⟩ : syracuseStep 4044973 = 1516865) (by norm_num)
theorem B5393297 : Blo 2243435 5393297 := bstep (se 2 (by rfl) ⟨2022486, by rfl⟩ : syracuseStep 5393297 = 4044973) B4044973
theorem B3595531 : Blo 2243435 3595531 := bstep (se 1 (by rfl) ⟨2696648, by rfl⟩ : syracuseStep 3595531 = 5393297) B5393297
theorem B4794041 : Blo 2243435 4794041 := bstep (se 2 (by rfl) ⟨1797765, by rfl⟩ : syracuseStep 4794041 = 3595531) B3595531
theorem B3196027 : Blo 2243435 3196027 := bstep (se 1 (by rfl) ⟨2397020, by rfl⟩ : syracuseStep 3196027 = 4794041) B4794041
theorem B17045477 : Blo 2243435 17045477 := bstep (se 4 (by rfl) ⟨1598013, by rfl⟩ : syracuseStep 17045477 = 3196027) B3196027
theorem B11363651 : Blo 2243435 11363651 := bstep (se 1 (by rfl) ⟨8522738, by rfl⟩ : syracuseStep 11363651 = 17045477) B17045477
theorem B7575767 : Blo 2243435 7575767 := bstep (se 1 (by rfl) ⟨5681825, by rfl⟩ : syracuseStep 7575767 = 11363651) B11363651
theorem B5050511 : Blo 2243435 5050511 := bstep (se 1 (by rfl) ⟨3787883, by rfl⟩ : syracuseStep 5050511 = 7575767) B7575767
theorem B3367007 : Blo 2243435 3367007 := bstep (se 1 (by rfl) ⟨2525255, by rfl⟩ : syracuseStep 3367007 = 5050511) B5050511
theorem B2244671 : Blo 2243435 2244671 := bstep (se 1 (by rfl) ⟨1683503, by rfl⟩ : syracuseStep 2244671 = 3367007) B3367007
theorem B3367013 : Blo 2243435 3367013 := bbase (se 4 (by rfl) ⟨315657, by rfl⟩ : syracuseStep 3367013 = 631315) (by norm_num)
theorem B2244675 : Blo 2243435 2244675 := bstep (se 1 (by rfl) ⟨1683506, by rfl⟩ : syracuseStep 2244675 = 3367013) B3367013
theorem B5393317 : Blo 2243435 5393317 := bbase (se 4 (by rfl) ⟨505623, by rfl⟩ : syracuseStep 5393317 = 1011247) (by norm_num)
theorem B7191089 : Blo 2243435 7191089 := bstep (se 2 (by rfl) ⟨2696658, by rfl⟩ : syracuseStep 7191089 = 5393317) B5393317
theorem B4794059 : Blo 2243435 4794059 := bstep (se 1 (by rfl) ⟨3595544, by rfl⟩ : syracuseStep 4794059 = 7191089) B7191089
theorem B3196039 : Blo 2243435 3196039 := bstep (se 1 (by rfl) ⟨2397029, by rfl⟩ : syracuseStep 3196039 = 4794059) B4794059
theorem B4261385 : Blo 2243435 4261385 := bstep (se 2 (by rfl) ⟨1598019, by rfl⟩ : syracuseStep 4261385 = 3196039) B3196039
theorem B2840923 : Blo 2243435 2840923 := bstep (se 1 (by rfl) ⟨2130692, by rfl⟩ : syracuseStep 2840923 = 4261385) B4261385
theorem B3787897 : Blo 2243435 3787897 := bstep (se 2 (by rfl) ⟨1420461, by rfl⟩ : syracuseStep 3787897 = 2840923) B2840923
theorem B5050529 : Blo 2243435 5050529 := bstep (se 2 (by rfl) ⟨1893948, by rfl⟩ : syracuseStep 5050529 = 3787897) B3787897
theorem B3367019 : Blo 2243435 3367019 := bstep (se 1 (by rfl) ⟨2525264, by rfl⟩ : syracuseStep 3367019 = 5050529) B5050529
theorem B2244679 : Blo 2243435 2244679 := bstep (se 1 (by rfl) ⟨1683509, by rfl⟩ : syracuseStep 2244679 = 3367019) B3367019
theorem B2525269 : Blo 2243435 2525269 := bbase (se 8 (by rfl) ⟨14796, by rfl⟩ : syracuseStep 2525269 = 29593) (by norm_num)
theorem B3367025 : Blo 2243435 3367025 := bstep (se 2 (by rfl) ⟨1262634, by rfl⟩ : syracuseStep 3367025 = 2525269) B2525269
theorem B2244683 : Blo 2243435 2244683 := bstep (se 1 (by rfl) ⟨1683512, by rfl⟩ : syracuseStep 2244683 = 3367025) B3367025
theorem B2840933 : Blo 2243435 2840933 := bbase (se 4 (by rfl) ⟨266337, by rfl⟩ : syracuseStep 2840933 = 532675) (by norm_num)
theorem B7575821 : Blo 2243435 7575821 := bstep (se 3 (by rfl) ⟨1420466, by rfl⟩ : syracuseStep 7575821 = 2840933) B2840933
theorem B5050547 : Blo 2243435 5050547 := bstep (se 1 (by rfl) ⟨3787910, by rfl⟩ : syracuseStep 5050547 = 7575821) B7575821
theorem B3367031 : Blo 2243435 3367031 := bstep (se 1 (by rfl) ⟨2525273, by rfl⟩ : syracuseStep 3367031 = 5050547) B5050547
theorem B2244687 : Blo 2243435 2244687 := bstep (se 1 (by rfl) ⟨1683515, by rfl⟩ : syracuseStep 2244687 = 3367031) B3367031
theorem B3367037 : Blo 2243435 3367037 := bbase (se 3 (by rfl) ⟨631319, by rfl⟩ : syracuseStep 3367037 = 1262639) (by norm_num)
theorem B2244691 : Blo 2243435 2244691 := bstep (se 1 (by rfl) ⟨1683518, by rfl⟩ : syracuseStep 2244691 = 3367037) B3367037
theorem B5050565 : Blo 2243435 5050565 := bbase (se 4 (by rfl) ⟨473490, by rfl⟩ : syracuseStep 5050565 = 946981) (by norm_num)
theorem B3367043 : Blo 2243435 3367043 := bstep (se 1 (by rfl) ⟨2525282, by rfl⟩ : syracuseStep 3367043 = 5050565) B5050565
theorem B2244695 : Blo 2243435 2244695 := bstep (se 1 (by rfl) ⟨1683521, by rfl⟩ : syracuseStep 2244695 = 3367043) B3367043
theorem B23351989 : Blo 2243435 23351989 := bbase (se 5 (by rfl) ⟨1094624, by rfl⟩ : syracuseStep 23351989 = 2189249) (by norm_num)
theorem B31135985 : Blo 2243435 31135985 := bstep (se 2 (by rfl) ⟨11675994, by rfl⟩ : syracuseStep 31135985 = 23351989) B23351989
theorem B20757323 : Blo 2243435 20757323 := bstep (se 1 (by rfl) ⟨15567992, by rfl⟩ : syracuseStep 20757323 = 31135985) B31135985
theorem B13838215 : Blo 2243435 13838215 := bstep (se 1 (by rfl) ⟨10378661, by rfl⟩ : syracuseStep 13838215 = 20757323) B20757323
theorem B18450953 : Blo 2243435 18450953 := bstep (se 2 (by rfl) ⟨6919107, by rfl⟩ : syracuseStep 18450953 = 13838215) B13838215
theorem B12300635 : Blo 2243435 12300635 := bstep (se 1 (by rfl) ⟨9225476, by rfl⟩ : syracuseStep 12300635 = 18450953) B18450953
theorem B8200423 : Blo 2243435 8200423 := bstep (se 1 (by rfl) ⟨6150317, by rfl⟩ : syracuseStep 8200423 = 12300635) B12300635
theorem B43735589 : Blo 2243435 43735589 := bstep (se 4 (by rfl) ⟨4100211, by rfl⟩ : syracuseStep 43735589 = 8200423) B8200423
theorem B29157059 : Blo 2243435 29157059 := bstep (se 1 (by rfl) ⟨21867794, by rfl⟩ : syracuseStep 29157059 = 43735589) B43735589
theorem B19438039 : Blo 2243435 19438039 := bstep (se 1 (by rfl) ⟨14578529, by rfl⟩ : syracuseStep 19438039 = 29157059) B29157059
theorem B103669541 : Blo 2243435 103669541 := bstep (se 4 (by rfl) ⟨9719019, by rfl⟩ : syracuseStep 103669541 = 19438039) B19438039
theorem B69113027 : Blo 2243435 69113027 := bstep (se 1 (by rfl) ⟨51834770, by rfl⟩ : syracuseStep 69113027 = 103669541) B103669541
theorem B46075351 : Blo 2243435 46075351 := bstep (se 1 (by rfl) ⟨34556513, by rfl⟩ : syracuseStep 46075351 = 69113027) B69113027
theorem B61433801 : Blo 2243435 61433801 := bstep (se 2 (by rfl) ⟨23037675, by rfl⟩ : syracuseStep 61433801 = 46075351) B46075351
theorem B40955867 : Blo 2243435 40955867 := bstep (se 1 (by rfl) ⟨30716900, by rfl⟩ : syracuseStep 40955867 = 61433801) B61433801
theorem B27303911 : Blo 2243435 27303911 := bstep (se 1 (by rfl) ⟨20477933, by rfl⟩ : syracuseStep 27303911 = 40955867) B40955867
theorem B18202607 : Blo 2243435 18202607 := bstep (se 1 (by rfl) ⟨13651955, by rfl⟩ : syracuseStep 18202607 = 27303911) B27303911
theorem B12135071 : Blo 2243435 12135071 := bstep (se 1 (by rfl) ⟨9101303, by rfl⟩ : syracuseStep 12135071 = 18202607) B18202607
theorem B8090047 : Blo 2243435 8090047 := bstep (se 1 (by rfl) ⟨6067535, by rfl⟩ : syracuseStep 8090047 = 12135071) B12135071
theorem B10786729 : Blo 2243435 10786729 := bstep (se 2 (by rfl) ⟨4045023, by rfl⟩ : syracuseStep 10786729 = 8090047) B8090047
theorem B14382305 : Blo 2243435 14382305 := bstep (se 2 (by rfl) ⟨5393364, by rfl⟩ : syracuseStep 14382305 = 10786729) B10786729
theorem B9588203 : Blo 2243435 9588203 := bstep (se 1 (by rfl) ⟨7191152, by rfl⟩ : syracuseStep 9588203 = 14382305) B14382305
theorem B6392135 : Blo 2243435 6392135 := bstep (se 1 (by rfl) ⟨4794101, by rfl⟩ : syracuseStep 6392135 = 9588203) B9588203
theorem B4261423 : Blo 2243435 4261423 := bstep (se 1 (by rfl) ⟨3196067, by rfl⟩ : syracuseStep 4261423 = 6392135) B6392135
theorem B5681897 : Blo 2243435 5681897 := bstep (se 2 (by rfl) ⟨2130711, by rfl⟩ : syracuseStep 5681897 = 4261423) B4261423
theorem B3787931 : Blo 2243435 3787931 := bstep (se 1 (by rfl) ⟨2840948, by rfl⟩ : syracuseStep 3787931 = 5681897) B5681897
theorem B2525287 : Blo 2243435 2525287 := bstep (se 1 (by rfl) ⟨1893965, by rfl⟩ : syracuseStep 2525287 = 3787931) B3787931
theorem B3367049 : Blo 2243435 3367049 := bstep (se 2 (by rfl) ⟨1262643, by rfl⟩ : syracuseStep 3367049 = 2525287) B2525287
theorem B2244699 : Blo 2243435 2244699 := bstep (se 1 (by rfl) ⟨1683524, by rfl⟩ : syracuseStep 2244699 = 3367049) B3367049
theorem B11363813 : Blo 2243435 11363813 := bbase (se 4 (by rfl) ⟨1065357, by rfl⟩ : syracuseStep 11363813 = 2130715) (by norm_num)
theorem B7575875 : Blo 2243435 7575875 := bstep (se 1 (by rfl) ⟨5681906, by rfl⟩ : syracuseStep 7575875 = 11363813) B11363813
theorem B5050583 : Blo 2243435 5050583 := bstep (se 1 (by rfl) ⟨3787937, by rfl⟩ : syracuseStep 5050583 = 7575875) B7575875
theorem B3367055 : Blo 2243435 3367055 := bstep (se 1 (by rfl) ⟨2525291, by rfl⟩ : syracuseStep 3367055 = 5050583) B5050583
theorem B2244703 : Blo 2243435 2244703 := bstep (se 1 (by rfl) ⟨1683527, by rfl⟩ : syracuseStep 2244703 = 3367055) B3367055
theorem B3367061 : Blo 2243435 3367061 := bbase (se 6 (by rfl) ⟨78915, by rfl⟩ : syracuseStep 3367061 = 157831) (by norm_num)
theorem B2244707 : Blo 2243435 2244707 := bstep (se 1 (by rfl) ⟨1683530, by rfl⟩ : syracuseStep 2244707 = 3367061) B3367061
theorem B4045045 : Blo 2243435 4045045 := bbase (se 5 (by rfl) ⟨189611, by rfl⟩ : syracuseStep 4045045 = 379223) (by norm_num)
theorem B5393393 : Blo 2243435 5393393 := bstep (se 2 (by rfl) ⟨2022522, by rfl⟩ : syracuseStep 5393393 = 4045045) B4045045
theorem B3595595 : Blo 2243435 3595595 := bstep (se 1 (by rfl) ⟨2696696, by rfl⟩ : syracuseStep 3595595 = 5393393) B5393393
theorem B9588253 : Blo 2243435 9588253 := bstep (se 3 (by rfl) ⟨1797797, by rfl⟩ : syracuseStep 9588253 = 3595595) B3595595
theorem B12784337 : Blo 2243435 12784337 := bstep (se 2 (by rfl) ⟨4794126, by rfl⟩ : syracuseStep 12784337 = 9588253) B9588253
theorem B8522891 : Blo 2243435 8522891 := bstep (se 1 (by rfl) ⟨6392168, by rfl⟩ : syracuseStep 8522891 = 12784337) B12784337
theorem B5681927 : Blo 2243435 5681927 := bstep (se 1 (by rfl) ⟨4261445, by rfl⟩ : syracuseStep 5681927 = 8522891) B8522891
theorem B3787951 : Blo 2243435 3787951 := bstep (se 1 (by rfl) ⟨2840963, by rfl⟩ : syracuseStep 3787951 = 5681927) B5681927
theorem B5050601 : Blo 2243435 5050601 := bstep (se 2 (by rfl) ⟨1893975, by rfl⟩ : syracuseStep 5050601 = 3787951) B3787951
theorem B3367067 : Blo 2243435 3367067 := bstep (se 1 (by rfl) ⟨2525300, by rfl⟩ : syracuseStep 3367067 = 5050601) B5050601
theorem B2244711 : Blo 2243435 2244711 := bstep (se 1 (by rfl) ⟨1683533, by rfl⟩ : syracuseStep 2244711 = 3367067) B3367067
theorem B2525305 : Blo 2243435 2525305 := bbase (se 2 (by rfl) ⟨946989, by rfl⟩ : syracuseStep 2525305 = 1893979) (by norm_num)
theorem B3367073 : Blo 2243435 3367073 := bstep (se 2 (by rfl) ⟨1262652, by rfl⟩ : syracuseStep 3367073 = 2525305) B2525305
theorem B2244715 : Blo 2243435 2244715 := bstep (se 1 (by rfl) ⟨1683536, by rfl⟩ : syracuseStep 2244715 = 3367073) B3367073
theorem B6826037 : Blo 2243435 6826037 := bbase (se 5 (by rfl) ⟨319970, by rfl⟩ : syracuseStep 6826037 = 639941) (by norm_num)
theorem B72811061 : Blo 2243435 72811061 := bstep (se 5 (by rfl) ⟨3413018, by rfl⟩ : syracuseStep 72811061 = 6826037) B6826037
theorem B48540707 : Blo 2243435 48540707 := bstep (se 1 (by rfl) ⟨36405530, by rfl⟩ : syracuseStep 48540707 = 72811061) B72811061
theorem B32360471 : Blo 2243435 32360471 := bstep (se 1 (by rfl) ⟨24270353, by rfl⟩ : syracuseStep 32360471 = 48540707) B48540707
theorem B21573647 : Blo 2243435 21573647 := bstep (se 1 (by rfl) ⟨16180235, by rfl⟩ : syracuseStep 21573647 = 32360471) B32360471
theorem B14382431 : Blo 2243435 14382431 := bstep (se 1 (by rfl) ⟨10786823, by rfl⟩ : syracuseStep 14382431 = 21573647) B21573647
theorem B9588287 : Blo 2243435 9588287 := bstep (se 1 (by rfl) ⟨7191215, by rfl⟩ : syracuseStep 9588287 = 14382431) B14382431
theorem B6392191 : Blo 2243435 6392191 := bstep (se 1 (by rfl) ⟨4794143, by rfl⟩ : syracuseStep 6392191 = 9588287) B9588287
theorem B8522921 : Blo 2243435 8522921 := bstep (se 2 (by rfl) ⟨3196095, by rfl⟩ : syracuseStep 8522921 = 6392191) B6392191
theorem B5681947 : Blo 2243435 5681947 := bstep (se 1 (by rfl) ⟨4261460, by rfl⟩ : syracuseStep 5681947 = 8522921) B8522921
theorem B7575929 : Blo 2243435 7575929 := bstep (se 2 (by rfl) ⟨2840973, by rfl⟩ : syracuseStep 7575929 = 5681947) B5681947
theorem B5050619 : Blo 2243435 5050619 := bstep (se 1 (by rfl) ⟨3787964, by rfl⟩ : syracuseStep 5050619 = 7575929) B7575929
theorem B3367079 : Blo 2243435 3367079 := bstep (se 1 (by rfl) ⟨2525309, by rfl⟩ : syracuseStep 3367079 = 5050619) B5050619
theorem B2244719 : Blo 2243435 2244719 := bstep (se 1 (by rfl) ⟨1683539, by rfl⟩ : syracuseStep 2244719 = 3367079) B3367079
theorem B3367085 : Blo 2243435 3367085 := bbase (se 3 (by rfl) ⟨631328, by rfl⟩ : syracuseStep 3367085 = 1262657) (by norm_num)
theorem B2244723 : Blo 2243435 2244723 := bstep (se 1 (by rfl) ⟨1683542, by rfl⟩ : syracuseStep 2244723 = 3367085) B3367085
theorem B5050637 : Blo 2243435 5050637 := bbase (se 3 (by rfl) ⟨946994, by rfl⟩ : syracuseStep 5050637 = 1893989) (by norm_num)
theorem B3367091 : Blo 2243435 3367091 := bstep (se 1 (by rfl) ⟨2525318, by rfl⟩ : syracuseStep 3367091 = 5050637) B5050637
theorem B2244727 : Blo 2243435 2244727 := bstep (se 1 (by rfl) ⟨1683545, by rfl⟩ : syracuseStep 2244727 = 3367091) B3367091
theorem B2840989 : Blo 2243435 2840989 := bbase (se 3 (by rfl) ⟨532685, by rfl⟩ : syracuseStep 2840989 = 1065371) (by norm_num)
theorem B3787985 : Blo 2243435 3787985 := bstep (se 2 (by rfl) ⟨1420494, by rfl⟩ : syracuseStep 3787985 = 2840989) B2840989
theorem B2525323 : Blo 2243435 2525323 := bstep (se 1 (by rfl) ⟨1893992, by rfl⟩ : syracuseStep 2525323 = 3787985) B3787985
theorem B3367097 : Blo 2243435 3367097 := bstep (se 2 (by rfl) ⟨1262661, by rfl⟩ : syracuseStep 3367097 = 2525323) B2525323
theorem B2244731 : Blo 2243435 2244731 := bstep (se 1 (by rfl) ⟨1683548, by rfl⟩ : syracuseStep 2244731 = 3367097) B3367097
theorem B2696725 : Blo 2243435 2696725 := bbase (se 6 (by rfl) ⟨63204, by rfl⟩ : syracuseStep 2696725 = 126409) (by norm_num)
theorem B3595633 : Blo 2243435 3595633 := bstep (se 2 (by rfl) ⟨1348362, by rfl⟩ : syracuseStep 3595633 = 2696725) B2696725
theorem B19176709 : Blo 2243435 19176709 := bstep (se 4 (by rfl) ⟨1797816, by rfl⟩ : syracuseStep 19176709 = 3595633) B3595633
theorem B25568945 : Blo 2243435 25568945 := bstep (se 2 (by rfl) ⟨9588354, by rfl⟩ : syracuseStep 25568945 = 19176709) B19176709
theorem B17045963 : Blo 2243435 17045963 := bstep (se 1 (by rfl) ⟨12784472, by rfl⟩ : syracuseStep 17045963 = 25568945) B25568945
theorem B11363975 : Blo 2243435 11363975 := bstep (se 1 (by rfl) ⟨8522981, by rfl⟩ : syracuseStep 11363975 = 17045963) B17045963
theorem B7575983 : Blo 2243435 7575983 := bstep (se 1 (by rfl) ⟨5681987, by rfl⟩ : syracuseStep 7575983 = 11363975) B11363975
theorem B5050655 : Blo 2243435 5050655 := bstep (se 1 (by rfl) ⟨3787991, by rfl⟩ : syracuseStep 5050655 = 7575983) B7575983
theorem B3367103 : Blo 2243435 3367103 := bstep (se 1 (by rfl) ⟨2525327, by rfl⟩ : syracuseStep 3367103 = 5050655) B5050655
theorem B2244735 : Blo 2243435 2244735 := bstep (se 1 (by rfl) ⟨1683551, by rfl⟩ : syracuseStep 2244735 = 3367103) B3367103
theorem B3367109 : Blo 2243435 3367109 := bbase (se 4 (by rfl) ⟨315666, by rfl⟩ : syracuseStep 3367109 = 631333) (by norm_num)
theorem B2244739 : Blo 2243435 2244739 := bstep (se 1 (by rfl) ⟨1683554, by rfl⟩ : syracuseStep 2244739 = 3367109) B3367109
theorem B3788005 : Blo 2243435 3788005 := bbase (se 4 (by rfl) ⟨355125, by rfl⟩ : syracuseStep 3788005 = 710251) (by norm_num)
theorem B5050673 : Blo 2243435 5050673 := bstep (se 2 (by rfl) ⟨1894002, by rfl⟩ : syracuseStep 5050673 = 3788005) B3788005
theorem B3367115 : Blo 2243435 3367115 := bstep (se 1 (by rfl) ⟨2525336, by rfl⟩ : syracuseStep 3367115 = 5050673) B5050673
theorem B2244743 : Blo 2243435 2244743 := bstep (se 1 (by rfl) ⟨1683557, by rfl⟩ : syracuseStep 2244743 = 3367115) B3367115
theorem B2525341 : Blo 2243435 2525341 := bbase (se 3 (by rfl) ⟨473501, by rfl⟩ : syracuseStep 2525341 = 947003) (by norm_num)
theorem B3367121 : Blo 2243435 3367121 := bstep (se 2 (by rfl) ⟨1262670, by rfl⟩ : syracuseStep 3367121 = 2525341) B2525341
theorem B2244747 : Blo 2243435 2244747 := bstep (se 1 (by rfl) ⟨1683560, by rfl⟩ : syracuseStep 2244747 = 3367121) B3367121
theorem B7576037 : Blo 2243435 7576037 := bbase (se 4 (by rfl) ⟨710253, by rfl⟩ : syracuseStep 7576037 = 1420507) (by norm_num)
theorem B5050691 : Blo 2243435 5050691 := bstep (se 1 (by rfl) ⟨3788018, by rfl⟩ : syracuseStep 5050691 = 7576037) B7576037
theorem B3367127 : Blo 2243435 3367127 := bstep (se 1 (by rfl) ⟨2525345, by rfl⟩ : syracuseStep 3367127 = 5050691) B5050691
theorem B2244751 : Blo 2243435 2244751 := bstep (se 1 (by rfl) ⟨1683563, by rfl⟩ : syracuseStep 2244751 = 3367127) B3367127
theorem B3367133 : Blo 2243435 3367133 := bbase (se 3 (by rfl) ⟨631337, by rfl⟩ : syracuseStep 3367133 = 1262675) (by norm_num)
theorem B2244755 : Blo 2243435 2244755 := bstep (se 1 (by rfl) ⟨1683566, by rfl⟩ : syracuseStep 2244755 = 3367133) B3367133
theorem B5050709 : Blo 2243435 5050709 := bbase (se 10 (by rfl) ⟨7398, by rfl⟩ : syracuseStep 5050709 = 14797) (by norm_num)
theorem B3367139 : Blo 2243435 3367139 := bstep (se 1 (by rfl) ⟨2525354, by rfl⟩ : syracuseStep 3367139 = 5050709) B5050709
theorem B2244759 : Blo 2243435 2244759 := bstep (se 1 (by rfl) ⟨1683569, by rfl⟩ : syracuseStep 2244759 = 3367139) B3367139
theorem B2733553 : Blo 2243435 2733553 := bbase (se 2 (by rfl) ⟨1025082, by rfl⟩ : syracuseStep 2733553 = 2050165) (by norm_num)
theorem B14578949 : Blo 2243435 14578949 := bstep (se 4 (by rfl) ⟨1366776, by rfl⟩ : syracuseStep 14578949 = 2733553) B2733553
theorem B9719299 : Blo 2243435 9719299 := bstep (se 1 (by rfl) ⟨7289474, by rfl⟩ : syracuseStep 9719299 = 14578949) B14578949
theorem B12959065 : Blo 2243435 12959065 := bstep (se 2 (by rfl) ⟨4859649, by rfl⟩ : syracuseStep 12959065 = 9719299) B9719299
theorem B17278753 : Blo 2243435 17278753 := bstep (se 2 (by rfl) ⟨6479532, by rfl⟩ : syracuseStep 17278753 = 12959065) B12959065
theorem B23038337 : Blo 2243435 23038337 := bstep (se 2 (by rfl) ⟨8639376, by rfl⟩ : syracuseStep 23038337 = 17278753) B17278753
theorem B15358891 : Blo 2243435 15358891 := bstep (se 1 (by rfl) ⟨11519168, by rfl⟩ : syracuseStep 15358891 = 23038337) B23038337
theorem B20478521 : Blo 2243435 20478521 := bstep (se 2 (by rfl) ⟨7679445, by rfl⟩ : syracuseStep 20478521 = 15358891) B15358891
theorem B13652347 : Blo 2243435 13652347 := bstep (se 1 (by rfl) ⟨10239260, by rfl⟩ : syracuseStep 13652347 = 20478521) B20478521
theorem B18203129 : Blo 2243435 18203129 := bstep (se 2 (by rfl) ⟨6826173, by rfl⟩ : syracuseStep 18203129 = 13652347) B13652347
theorem B12135419 : Blo 2243435 12135419 := bstep (se 1 (by rfl) ⟨9101564, by rfl⟩ : syracuseStep 12135419 = 18203129) B18203129
theorem B8090279 : Blo 2243435 8090279 := bstep (se 1 (by rfl) ⟨6067709, by rfl⟩ : syracuseStep 8090279 = 12135419) B12135419
theorem B5393519 : Blo 2243435 5393519 := bstep (se 1 (by rfl) ⟨4045139, by rfl⟩ : syracuseStep 5393519 = 8090279) B8090279
theorem B3595679 : Blo 2243435 3595679 := bstep (se 1 (by rfl) ⟨2696759, by rfl⟩ : syracuseStep 3595679 = 5393519) B5393519
theorem B2397119 : Blo 2243435 2397119 := bstep (se 1 (by rfl) ⟨1797839, by rfl⟩ : syracuseStep 2397119 = 3595679) B3595679
theorem B6392317 : Blo 2243435 6392317 := bstep (se 3 (by rfl) ⟨1198559, by rfl⟩ : syracuseStep 6392317 = 2397119) B2397119
theorem B8523089 : Blo 2243435 8523089 := bstep (se 2 (by rfl) ⟨3196158, by rfl⟩ : syracuseStep 8523089 = 6392317) B6392317
theorem B5682059 : Blo 2243435 5682059 := bstep (se 1 (by rfl) ⟨4261544, by rfl⟩ : syracuseStep 5682059 = 8523089) B8523089
theorem B3788039 : Blo 2243435 3788039 := bstep (se 1 (by rfl) ⟨2841029, by rfl⟩ : syracuseStep 3788039 = 5682059) B5682059
theorem B2525359 : Blo 2243435 2525359 := bstep (se 1 (by rfl) ⟨1894019, by rfl⟩ : syracuseStep 2525359 = 3788039) B3788039
theorem B3367145 : Blo 2243435 3367145 := bstep (se 2 (by rfl) ⟨1262679, by rfl⟩ : syracuseStep 3367145 = 2525359) B2525359
theorem B2244763 : Blo 2243435 2244763 := bstep (se 1 (by rfl) ⟨1683572, by rfl⟩ : syracuseStep 2244763 = 3367145) B3367145
theorem B4550789 : Blo 2243435 4550789 := bbase (se 4 (by rfl) ⟨426636, by rfl⟩ : syracuseStep 4550789 = 853273) (by norm_num)
theorem B3033859 : Blo 2243435 3033859 := bstep (se 1 (by rfl) ⟨2275394, by rfl⟩ : syracuseStep 3033859 = 4550789) B4550789
theorem B4045145 : Blo 2243435 4045145 := bstep (se 2 (by rfl) ⟨1516929, by rfl⟩ : syracuseStep 4045145 = 3033859) B3033859
theorem B43148213 : Blo 2243435 43148213 := bstep (se 5 (by rfl) ⟨2022572, by rfl⟩ : syracuseStep 43148213 = 4045145) B4045145
theorem B28765475 : Blo 2243435 28765475 := bstep (se 1 (by rfl) ⟨21574106, by rfl⟩ : syracuseStep 28765475 = 43148213) B43148213
theorem B19176983 : Blo 2243435 19176983 := bstep (se 1 (by rfl) ⟨14382737, by rfl⟩ : syracuseStep 19176983 = 28765475) B28765475
theorem B12784655 : Blo 2243435 12784655 := bstep (se 1 (by rfl) ⟨9588491, by rfl⟩ : syracuseStep 12784655 = 19176983) B19176983
theorem B8523103 : Blo 2243435 8523103 := bstep (se 1 (by rfl) ⟨6392327, by rfl⟩ : syracuseStep 8523103 = 12784655) B12784655
theorem B11364137 : Blo 2243435 11364137 := bstep (se 2 (by rfl) ⟨4261551, by rfl⟩ : syracuseStep 11364137 = 8523103) B8523103
theorem B7576091 : Blo 2243435 7576091 := bstep (se 1 (by rfl) ⟨5682068, by rfl⟩ : syracuseStep 7576091 = 11364137) B11364137
theorem B5050727 : Blo 2243435 5050727 := bstep (se 1 (by rfl) ⟨3788045, by rfl⟩ : syracuseStep 5050727 = 7576091) B7576091
theorem B3367151 : Blo 2243435 3367151 := bstep (se 1 (by rfl) ⟨2525363, by rfl⟩ : syracuseStep 3367151 = 5050727) B5050727
theorem B2244767 : Blo 2243435 2244767 := bstep (se 1 (by rfl) ⟨1683575, by rfl⟩ : syracuseStep 2244767 = 3367151) B3367151
theorem B3367157 : Blo 2243435 3367157 := bbase (se 5 (by rfl) ⟨157835, by rfl⟩ : syracuseStep 3367157 = 315671) (by norm_num)
theorem B2244771 : Blo 2243435 2244771 := bstep (se 1 (by rfl) ⟨1683578, by rfl⟩ : syracuseStep 2244771 = 3367157) B3367157
theorem B18203221 : Blo 2243435 18203221 := bbase (se 8 (by rfl) ⟨106659, by rfl⟩ : syracuseStep 18203221 = 213319) (by norm_num)
theorem B24270961 : Blo 2243435 24270961 := bstep (se 2 (by rfl) ⟨9101610, by rfl⟩ : syracuseStep 24270961 = 18203221) B18203221
theorem B32361281 : Blo 2243435 32361281 := bstep (se 2 (by rfl) ⟨12135480, by rfl⟩ : syracuseStep 32361281 = 24270961) B24270961
theorem B21574187 : Blo 2243435 21574187 := bstep (se 1 (by rfl) ⟨16180640, by rfl⟩ : syracuseStep 21574187 = 32361281) B32361281
theorem B14382791 : Blo 2243435 14382791 := bstep (se 1 (by rfl) ⟨10787093, by rfl⟩ : syracuseStep 14382791 = 21574187) B21574187
theorem B9588527 : Blo 2243435 9588527 := bstep (se 1 (by rfl) ⟨7191395, by rfl⟩ : syracuseStep 9588527 = 14382791) B14382791
theorem B6392351 : Blo 2243435 6392351 := bstep (se 1 (by rfl) ⟨4794263, by rfl⟩ : syracuseStep 6392351 = 9588527) B9588527
theorem B4261567 : Blo 2243435 4261567 := bstep (se 1 (by rfl) ⟨3196175, by rfl⟩ : syracuseStep 4261567 = 6392351) B6392351
theorem B5682089 : Blo 2243435 5682089 := bstep (se 2 (by rfl) ⟨2130783, by rfl⟩ : syracuseStep 5682089 = 4261567) B4261567
theorem B3788059 : Blo 2243435 3788059 := bstep (se 1 (by rfl) ⟨2841044, by rfl⟩ : syracuseStep 3788059 = 5682089) B5682089
theorem B5050745 : Blo 2243435 5050745 := bstep (se 2 (by rfl) ⟨1894029, by rfl⟩ : syracuseStep 5050745 = 3788059) B3788059
theorem B3367163 : Blo 2243435 3367163 := bstep (se 1 (by rfl) ⟨2525372, by rfl⟩ : syracuseStep 3367163 = 5050745) B5050745
theorem B2244775 : Blo 2243435 2244775 := bstep (se 1 (by rfl) ⟨1683581, by rfl⟩ : syracuseStep 2244775 = 3367163) B3367163
theorem B2525377 : Blo 2243435 2525377 := bbase (se 2 (by rfl) ⟨947016, by rfl⟩ : syracuseStep 2525377 = 1894033) (by norm_num)
theorem B3367169 : Blo 2243435 3367169 := bstep (se 2 (by rfl) ⟨1262688, by rfl⟩ : syracuseStep 3367169 = 2525377) B2525377
theorem B2244779 : Blo 2243435 2244779 := bstep (se 1 (by rfl) ⟨1683584, by rfl⟩ : syracuseStep 2244779 = 3367169) B3367169
theorem B5682109 : Blo 2243435 5682109 := bbase (se 3 (by rfl) ⟨1065395, by rfl⟩ : syracuseStep 5682109 = 2130791) (by norm_num)
theorem B7576145 : Blo 2243435 7576145 := bstep (se 2 (by rfl) ⟨2841054, by rfl⟩ : syracuseStep 7576145 = 5682109) B5682109
theorem B5050763 : Blo 2243435 5050763 := bstep (se 1 (by rfl) ⟨3788072, by rfl⟩ : syracuseStep 5050763 = 7576145) B7576145
theorem B3367175 : Blo 2243435 3367175 := bstep (se 1 (by rfl) ⟨2525381, by rfl⟩ : syracuseStep 3367175 = 5050763) B5050763
theorem B2244783 : Blo 2243435 2244783 := bstep (se 1 (by rfl) ⟨1683587, by rfl⟩ : syracuseStep 2244783 = 3367175) B3367175
theorem B3367181 : Blo 2243435 3367181 := bbase (se 3 (by rfl) ⟨631346, by rfl⟩ : syracuseStep 3367181 = 1262693) (by norm_num)
theorem B2244787 : Blo 2243435 2244787 := bstep (se 1 (by rfl) ⟨1683590, by rfl⟩ : syracuseStep 2244787 = 3367181) B3367181
theorem B5050781 : Blo 2243435 5050781 := bbase (se 3 (by rfl) ⟨947021, by rfl⟩ : syracuseStep 5050781 = 1894043) (by norm_num)
theorem B3367187 : Blo 2243435 3367187 := bstep (se 1 (by rfl) ⟨2525390, by rfl⟩ : syracuseStep 3367187 = 5050781) B5050781
theorem B2244791 : Blo 2243435 2244791 := bstep (se 1 (by rfl) ⟨1683593, by rfl⟩ : syracuseStep 2244791 = 3367187) B3367187
theorem B3788093 : Blo 2243435 3788093 := bbase (se 3 (by rfl) ⟨710267, by rfl⟩ : syracuseStep 3788093 = 1420535) (by norm_num)
theorem B2525395 : Blo 2243435 2525395 := bstep (se 1 (by rfl) ⟨1894046, by rfl⟩ : syracuseStep 2525395 = 3788093) B3788093
theorem B3367193 : Blo 2243435 3367193 := bstep (se 2 (by rfl) ⟨1262697, by rfl⟩ : syracuseStep 3367193 = 2525395) B2525395
theorem B2244795 : Blo 2243435 2244795 := bstep (se 1 (by rfl) ⟨1683596, by rfl⟩ : syracuseStep 2244795 = 3367193) B3367193
theorem B2397157 : Blo 2243435 2397157 := bbase (se 4 (by rfl) ⟨224733, by rfl⟩ : syracuseStep 2397157 = 449467) (by norm_num)
theorem B12784837 : Blo 2243435 12784837 := bstep (se 4 (by rfl) ⟨1198578, by rfl⟩ : syracuseStep 12784837 = 2397157) B2397157
theorem B17046449 : Blo 2243435 17046449 := bstep (se 2 (by rfl) ⟨6392418, by rfl⟩ : syracuseStep 17046449 = 12784837) B12784837
theorem B11364299 : Blo 2243435 11364299 := bstep (se 1 (by rfl) ⟨8523224, by rfl⟩ : syracuseStep 11364299 = 17046449) B17046449
theorem B7576199 : Blo 2243435 7576199 := bstep (se 1 (by rfl) ⟨5682149, by rfl⟩ : syracuseStep 7576199 = 11364299) B11364299
theorem B5050799 : Blo 2243435 5050799 := bstep (se 1 (by rfl) ⟨3788099, by rfl⟩ : syracuseStep 5050799 = 7576199) B7576199
theorem B3367199 : Blo 2243435 3367199 := bstep (se 1 (by rfl) ⟨2525399, by rfl⟩ : syracuseStep 3367199 = 5050799) B5050799
theorem B2244799 : Blo 2243435 2244799 := bstep (se 1 (by rfl) ⟨1683599, by rfl⟩ : syracuseStep 2244799 = 3367199) B3367199
theorem B3367205 : Blo 2243435 3367205 := bbase (se 4 (by rfl) ⟨315675, by rfl⟩ : syracuseStep 3367205 = 631351) (by norm_num)
theorem B2244803 : Blo 2243435 2244803 := bstep (se 1 (by rfl) ⟨1683602, by rfl⟩ : syracuseStep 2244803 = 3367205) B3367205
theorem B2841085 : Blo 2243435 2841085 := bbase (se 3 (by rfl) ⟨532703, by rfl⟩ : syracuseStep 2841085 = 1065407) (by norm_num)
theorem B3788113 : Blo 2243435 3788113 := bstep (se 2 (by rfl) ⟨1420542, by rfl⟩ : syracuseStep 3788113 = 2841085) B2841085
theorem B5050817 : Blo 2243435 5050817 := bstep (se 2 (by rfl) ⟨1894056, by rfl⟩ : syracuseStep 5050817 = 3788113) B3788113
theorem B3367211 : Blo 2243435 3367211 := bstep (se 1 (by rfl) ⟨2525408, by rfl⟩ : syracuseStep 3367211 = 5050817) B5050817
theorem B2244807 : Blo 2243435 2244807 := bstep (se 1 (by rfl) ⟨1683605, by rfl⟩ : syracuseStep 2244807 = 3367211) B3367211
theorem B2525413 : Blo 2243435 2525413 := bbase (se 4 (by rfl) ⟨236757, by rfl⟩ : syracuseStep 2525413 = 473515) (by norm_num)
theorem B3367217 : Blo 2243435 3367217 := bstep (se 2 (by rfl) ⟨1262706, by rfl⟩ : syracuseStep 3367217 = 2525413) B2525413
theorem B2244811 : Blo 2243435 2244811 := bstep (se 1 (by rfl) ⟨1683608, by rfl⟩ : syracuseStep 2244811 = 3367217) B3367217
theorem B4794349 : Blo 2243435 4794349 := bbase (se 3 (by rfl) ⟨898940, by rfl⟩ : syracuseStep 4794349 = 1797881) (by norm_num)
theorem B6392465 : Blo 2243435 6392465 := bstep (se 2 (by rfl) ⟨2397174, by rfl⟩ : syracuseStep 6392465 = 4794349) B4794349
theorem B4261643 : Blo 2243435 4261643 := bstep (se 1 (by rfl) ⟨3196232, by rfl⟩ : syracuseStep 4261643 = 6392465) B6392465
theorem B2841095 : Blo 2243435 2841095 := bstep (se 1 (by rfl) ⟨2130821, by rfl⟩ : syracuseStep 2841095 = 4261643) B4261643
theorem B7576253 : Blo 2243435 7576253 := bstep (se 3 (by rfl) ⟨1420547, by rfl⟩ : syracuseStep 7576253 = 2841095) B2841095
theorem B5050835 : Blo 2243435 5050835 := bstep (se 1 (by rfl) ⟨3788126, by rfl⟩ : syracuseStep 5050835 = 7576253) B7576253
theorem B3367223 : Blo 2243435 3367223 := bstep (se 1 (by rfl) ⟨2525417, by rfl⟩ : syracuseStep 3367223 = 5050835) B5050835
theorem B2244815 : Blo 2243435 2244815 := bstep (se 1 (by rfl) ⟨1683611, by rfl⟩ : syracuseStep 2244815 = 3367223) B3367223
theorem B3367229 : Blo 2243435 3367229 := bbase (se 3 (by rfl) ⟨631355, by rfl⟩ : syracuseStep 3367229 = 1262711) (by norm_num)
theorem B2244819 : Blo 2243435 2244819 := bstep (se 1 (by rfl) ⟨1683614, by rfl⟩ : syracuseStep 2244819 = 3367229) B3367229
theorem B5050853 : Blo 2243435 5050853 := bbase (se 4 (by rfl) ⟨473517, by rfl⟩ : syracuseStep 5050853 = 947035) (by norm_num)
theorem B3367235 : Blo 2243435 3367235 := bstep (se 1 (by rfl) ⟨2525426, by rfl⟩ : syracuseStep 3367235 = 5050853) B5050853
theorem B2244823 : Blo 2243435 2244823 := bstep (se 1 (by rfl) ⟨1683617, by rfl⟩ : syracuseStep 2244823 = 3367235) B3367235
theorem B5682221 : Blo 2243435 5682221 := bbase (se 3 (by rfl) ⟨1065416, by rfl⟩ : syracuseStep 5682221 = 2130833) (by norm_num)
theorem B3788147 : Blo 2243435 3788147 := bstep (se 1 (by rfl) ⟨2841110, by rfl⟩ : syracuseStep 3788147 = 5682221) B5682221
theorem B2525431 : Blo 2243435 2525431 := bstep (se 1 (by rfl) ⟨1894073, by rfl⟩ : syracuseStep 2525431 = 3788147) B3788147
theorem B3367241 : Blo 2243435 3367241 := bstep (se 2 (by rfl) ⟨1262715, by rfl⟩ : syracuseStep 3367241 = 2525431) B2525431
theorem B2244827 : Blo 2243435 2244827 := bstep (se 1 (by rfl) ⟨1683620, by rfl⟩ : syracuseStep 2244827 = 3367241) B3367241
theorem B16181045 : Blo 2243435 16181045 := bbase (se 5 (by rfl) ⟨758486, by rfl⟩ : syracuseStep 16181045 = 1516973) (by norm_num)
theorem B10787363 : Blo 2243435 10787363 := bstep (se 1 (by rfl) ⟨8090522, by rfl⟩ : syracuseStep 10787363 = 16181045) B16181045
theorem B7191575 : Blo 2243435 7191575 := bstep (se 1 (by rfl) ⟨5393681, by rfl⟩ : syracuseStep 7191575 = 10787363) B10787363
theorem B4794383 : Blo 2243435 4794383 := bstep (se 1 (by rfl) ⟨3595787, by rfl⟩ : syracuseStep 4794383 = 7191575) B7191575
theorem B3196255 : Blo 2243435 3196255 := bstep (se 1 (by rfl) ⟨2397191, by rfl⟩ : syracuseStep 3196255 = 4794383) B4794383
theorem B4261673 : Blo 2243435 4261673 := bstep (se 2 (by rfl) ⟨1598127, by rfl⟩ : syracuseStep 4261673 = 3196255) B3196255
theorem B11364461 : Blo 2243435 11364461 := bstep (se 3 (by rfl) ⟨2130836, by rfl⟩ : syracuseStep 11364461 = 4261673) B4261673
theorem B7576307 : Blo 2243435 7576307 := bstep (se 1 (by rfl) ⟨5682230, by rfl⟩ : syracuseStep 7576307 = 11364461) B11364461
theorem B5050871 : Blo 2243435 5050871 := bstep (se 1 (by rfl) ⟨3788153, by rfl⟩ : syracuseStep 5050871 = 7576307) B7576307
theorem B3367247 : Blo 2243435 3367247 := bstep (se 1 (by rfl) ⟨2525435, by rfl⟩ : syracuseStep 3367247 = 5050871) B5050871
theorem B2244831 : Blo 2243435 2244831 := bstep (se 1 (by rfl) ⟨1683623, by rfl⟩ : syracuseStep 2244831 = 3367247) B3367247
theorem B3367253 : Blo 2243435 3367253 := bbase (se 10 (by rfl) ⟨4932, by rfl⟩ : syracuseStep 3367253 = 9865) (by norm_num)
theorem B2244835 : Blo 2243435 2244835 := bstep (se 1 (by rfl) ⟨1683626, by rfl⟩ : syracuseStep 2244835 = 3367253) B3367253
theorem B6392533 : Blo 2243435 6392533 := bbase (se 7 (by rfl) ⟨74912, by rfl⟩ : syracuseStep 6392533 = 149825) (by norm_num)
theorem B8523377 : Blo 2243435 8523377 := bstep (se 2 (by rfl) ⟨3196266, by rfl⟩ : syracuseStep 8523377 = 6392533) B6392533
theorem B5682251 : Blo 2243435 5682251 := bstep (se 1 (by rfl) ⟨4261688, by rfl⟩ : syracuseStep 5682251 = 8523377) B8523377
theorem B3788167 : Blo 2243435 3788167 := bstep (se 1 (by rfl) ⟨2841125, by rfl⟩ : syracuseStep 3788167 = 5682251) B5682251
theorem B5050889 : Blo 2243435 5050889 := bstep (se 2 (by rfl) ⟨1894083, by rfl⟩ : syracuseStep 5050889 = 3788167) B3788167
theorem B3367259 : Blo 2243435 3367259 := bstep (se 1 (by rfl) ⟨2525444, by rfl⟩ : syracuseStep 3367259 = 5050889) B5050889
theorem B2244839 : Blo 2243435 2244839 := bstep (se 1 (by rfl) ⟨1683629, by rfl⟩ : syracuseStep 2244839 = 3367259) B3367259
theorem B2525449 : Blo 2243435 2525449 := bbase (se 2 (by rfl) ⟨947043, by rfl⟩ : syracuseStep 2525449 = 1894087) (by norm_num)
theorem B3367265 : Blo 2243435 3367265 := bstep (se 2 (by rfl) ⟨1262724, by rfl⟩ : syracuseStep 3367265 = 2525449) B2525449
theorem B2244843 : Blo 2243435 2244843 := bstep (se 1 (by rfl) ⟨1683632, by rfl⟩ : syracuseStep 2244843 = 3367265) B3367265
theorem B6150725 : Blo 2243435 6150725 := bbase (se 4 (by rfl) ⟨576630, by rfl⟩ : syracuseStep 6150725 = 1153261) (by norm_num)
theorem B4100483 : Blo 2243435 4100483 := bstep (se 1 (by rfl) ⟨3075362, by rfl⟩ : syracuseStep 4100483 = 6150725) B6150725
theorem B10934621 : Blo 2243435 10934621 := bstep (se 3 (by rfl) ⟨2050241, by rfl⟩ : syracuseStep 10934621 = 4100483) B4100483
theorem B7289747 : Blo 2243435 7289747 := bstep (se 1 (by rfl) ⟨5467310, by rfl⟩ : syracuseStep 7289747 = 10934621) B10934621
theorem B4859831 : Blo 2243435 4859831 := bstep (se 1 (by rfl) ⟨3644873, by rfl⟩ : syracuseStep 4859831 = 7289747) B7289747
theorem B3239887 : Blo 2243435 3239887 := bstep (se 1 (by rfl) ⟨2429915, by rfl⟩ : syracuseStep 3239887 = 4859831) B4859831
theorem B4319849 : Blo 2243435 4319849 := bstep (se 2 (by rfl) ⟨1619943, by rfl⟩ : syracuseStep 4319849 = 3239887) B3239887
theorem B11519597 : Blo 2243435 11519597 := bstep (se 3 (by rfl) ⟨2159924, by rfl⟩ : syracuseStep 11519597 = 4319849) B4319849
theorem B7679731 : Blo 2243435 7679731 := bstep (se 1 (by rfl) ⟨5759798, by rfl⟩ : syracuseStep 7679731 = 11519597) B11519597
theorem B10239641 : Blo 2243435 10239641 := bstep (se 2 (by rfl) ⟨3839865, by rfl⟩ : syracuseStep 10239641 = 7679731) B7679731
theorem B6826427 : Blo 2243435 6826427 := bstep (se 1 (by rfl) ⟨5119820, by rfl⟩ : syracuseStep 6826427 = 10239641) B10239641
theorem B4550951 : Blo 2243435 4550951 := bstep (se 1 (by rfl) ⟨3413213, by rfl⟩ : syracuseStep 4550951 = 6826427) B6826427
theorem B12135869 : Blo 2243435 12135869 := bstep (se 3 (by rfl) ⟨2275475, by rfl⟩ : syracuseStep 12135869 = 4550951) B4550951
theorem B8090579 : Blo 2243435 8090579 := bstep (se 1 (by rfl) ⟨6067934, by rfl⟩ : syracuseStep 8090579 = 12135869) B12135869
theorem B5393719 : Blo 2243435 5393719 := bstep (se 1 (by rfl) ⟨4045289, by rfl⟩ : syracuseStep 5393719 = 8090579) B8090579
theorem B28766501 : Blo 2243435 28766501 := bstep (se 4 (by rfl) ⟨2696859, by rfl⟩ : syracuseStep 28766501 = 5393719) B5393719
theorem B19177667 : Blo 2243435 19177667 := bstep (se 1 (by rfl) ⟨14383250, by rfl⟩ : syracuseStep 19177667 = 28766501) B28766501
theorem B12785111 : Blo 2243435 12785111 := bstep (se 1 (by rfl) ⟨9588833, by rfl⟩ : syracuseStep 12785111 = 19177667) B19177667
theorem B8523407 : Blo 2243435 8523407 := bstep (se 1 (by rfl) ⟨6392555, by rfl⟩ : syracuseStep 8523407 = 12785111) B12785111
theorem B5682271 : Blo 2243435 5682271 := bstep (se 1 (by rfl) ⟨4261703, by rfl⟩ : syracuseStep 5682271 = 8523407) B8523407
theorem B7576361 : Blo 2243435 7576361 := bstep (se 2 (by rfl) ⟨2841135, by rfl⟩ : syracuseStep 7576361 = 5682271) B5682271
theorem B5050907 : Blo 2243435 5050907 := bstep (se 1 (by rfl) ⟨3788180, by rfl⟩ : syracuseStep 5050907 = 7576361) B7576361
theorem B3367271 : Blo 2243435 3367271 := bstep (se 1 (by rfl) ⟨2525453, by rfl⟩ : syracuseStep 3367271 = 5050907) B5050907
theorem B2244847 : Blo 2243435 2244847 := bstep (se 1 (by rfl) ⟨1683635, by rfl⟩ : syracuseStep 2244847 = 3367271) B3367271
theorem B3367277 : Blo 2243435 3367277 := bbase (se 3 (by rfl) ⟨631364, by rfl⟩ : syracuseStep 3367277 = 1262729) (by norm_num)
theorem B2244851 : Blo 2243435 2244851 := bstep (se 1 (by rfl) ⟨1683638, by rfl⟩ : syracuseStep 2244851 = 3367277) B3367277
theorem B5050925 : Blo 2243435 5050925 := bbase (se 3 (by rfl) ⟨947048, by rfl⟩ : syracuseStep 5050925 = 1894097) (by norm_num)
theorem B3367283 : Blo 2243435 3367283 := bstep (se 1 (by rfl) ⟨2525462, by rfl⟩ : syracuseStep 3367283 = 5050925) B5050925
theorem B2244855 : Blo 2243435 2244855 := bstep (se 1 (by rfl) ⟨1683641, by rfl⟩ : syracuseStep 2244855 = 3367283) B3367283
theorem B21574997 : Blo 2243435 21574997 := bbase (se 13 (by rfl) ⟨3950, by rfl⟩ : syracuseStep 21574997 = 7901) (by norm_num)
theorem B14383331 : Blo 2243435 14383331 := bstep (se 1 (by rfl) ⟨10787498, by rfl⟩ : syracuseStep 14383331 = 21574997) B21574997
theorem B9588887 : Blo 2243435 9588887 := bstep (se 1 (by rfl) ⟨7191665, by rfl⟩ : syracuseStep 9588887 = 14383331) B14383331
theorem B6392591 : Blo 2243435 6392591 := bstep (se 1 (by rfl) ⟨4794443, by rfl⟩ : syracuseStep 6392591 = 9588887) B9588887
theorem B4261727 : Blo 2243435 4261727 := bstep (se 1 (by rfl) ⟨3196295, by rfl⟩ : syracuseStep 4261727 = 6392591) B6392591
theorem B2841151 : Blo 2243435 2841151 := bstep (se 1 (by rfl) ⟨2130863, by rfl⟩ : syracuseStep 2841151 = 4261727) B4261727
theorem B3788201 : Blo 2243435 3788201 := bstep (se 2 (by rfl) ⟨1420575, by rfl⟩ : syracuseStep 3788201 = 2841151) B2841151
theorem B2525467 : Blo 2243435 2525467 := bstep (se 1 (by rfl) ⟨1894100, by rfl⟩ : syracuseStep 2525467 = 3788201) B3788201
theorem B3367289 : Blo 2243435 3367289 := bstep (se 2 (by rfl) ⟨1262733, by rfl⟩ : syracuseStep 3367289 = 2525467) B2525467
theorem B2244859 : Blo 2243435 2244859 := bstep (se 1 (by rfl) ⟨1683644, by rfl⟩ : syracuseStep 2244859 = 3367289) B3367289
theorem B38355605 : Blo 2243435 38355605 := bbase (se 6 (by rfl) ⟨898959, by rfl⟩ : syracuseStep 38355605 = 1797919) (by norm_num)
theorem B25570403 : Blo 2243435 25570403 := bstep (se 1 (by rfl) ⟨19177802, by rfl⟩ : syracuseStep 25570403 = 38355605) B38355605
theorem B17046935 : Blo 2243435 17046935 := bstep (se 1 (by rfl) ⟨12785201, by rfl⟩ : syracuseStep 17046935 = 25570403) B25570403
theorem B11364623 : Blo 2243435 11364623 := bstep (se 1 (by rfl) ⟨8523467, by rfl⟩ : syracuseStep 11364623 = 17046935) B17046935
theorem B7576415 : Blo 2243435 7576415 := bstep (se 1 (by rfl) ⟨5682311, by rfl⟩ : syracuseStep 7576415 = 11364623) B11364623
theorem B5050943 : Blo 2243435 5050943 := bstep (se 1 (by rfl) ⟨3788207, by rfl⟩ : syracuseStep 5050943 = 7576415) B7576415
theorem B3367295 : Blo 2243435 3367295 := bstep (se 1 (by rfl) ⟨2525471, by rfl⟩ : syracuseStep 3367295 = 5050943) B5050943
theorem B2244863 : Blo 2243435 2244863 := bstep (se 1 (by rfl) ⟨1683647, by rfl⟩ : syracuseStep 2244863 = 3367295) B3367295
theorem B3367301 : Blo 2243435 3367301 := bbase (se 4 (by rfl) ⟨315684, by rfl⟩ : syracuseStep 3367301 = 631369) (by norm_num)
theorem B2244867 : Blo 2243435 2244867 := bstep (se 1 (by rfl) ⟨1683650, by rfl⟩ : syracuseStep 2244867 = 3367301) B3367301
theorem B3788221 : Blo 2243435 3788221 := bbase (se 3 (by rfl) ⟨710291, by rfl⟩ : syracuseStep 3788221 = 1420583) (by norm_num)
theorem B5050961 : Blo 2243435 5050961 := bstep (se 2 (by rfl) ⟨1894110, by rfl⟩ : syracuseStep 5050961 = 3788221) B3788221
theorem B3367307 : Blo 2243435 3367307 := bstep (se 1 (by rfl) ⟨2525480, by rfl⟩ : syracuseStep 3367307 = 5050961) B5050961
theorem B2244871 : Blo 2243435 2244871 := bstep (se 1 (by rfl) ⟨1683653, by rfl⟩ : syracuseStep 2244871 = 3367307) B3367307
theorem B2525485 : Blo 2243435 2525485 := bbase (se 3 (by rfl) ⟨473528, by rfl⟩ : syracuseStep 2525485 = 947057) (by norm_num)
theorem B3367313 : Blo 2243435 3367313 := bstep (se 2 (by rfl) ⟨1262742, by rfl⟩ : syracuseStep 3367313 = 2525485) B2525485
theorem B2244875 : Blo 2243435 2244875 := bstep (se 1 (by rfl) ⟨1683656, by rfl⟩ : syracuseStep 2244875 = 3367313) B3367313
theorem B7576469 : Blo 2243435 7576469 := bbase (se 6 (by rfl) ⟨177573, by rfl⟩ : syracuseStep 7576469 = 355147) (by norm_num)
theorem B5050979 : Blo 2243435 5050979 := bstep (se 1 (by rfl) ⟨3788234, by rfl⟩ : syracuseStep 5050979 = 7576469) B7576469
theorem B3367319 : Blo 2243435 3367319 := bstep (se 1 (by rfl) ⟨2525489, by rfl⟩ : syracuseStep 3367319 = 5050979) B5050979
theorem B2244879 : Blo 2243435 2244879 := bstep (se 1 (by rfl) ⟨1683659, by rfl⟩ : syracuseStep 2244879 = 3367319) B3367319
theorem B3367325 : Blo 2243435 3367325 := bbase (se 3 (by rfl) ⟨631373, by rfl⟩ : syracuseStep 3367325 = 1262747) (by norm_num)
theorem B2244883 : Blo 2243435 2244883 := bstep (se 1 (by rfl) ⟨1683662, by rfl⟩ : syracuseStep 2244883 = 3367325) B3367325
theorem B5050997 : Blo 2243435 5050997 := bbase (se 5 (by rfl) ⟨236765, by rfl⟩ : syracuseStep 5050997 = 473531) (by norm_num)
theorem B3367331 : Blo 2243435 3367331 := bstep (se 1 (by rfl) ⟨2525498, by rfl⟩ : syracuseStep 3367331 = 5050997) B5050997
theorem B2244887 : Blo 2243435 2244887 := bstep (se 1 (by rfl) ⟨1683665, by rfl⟩ : syracuseStep 2244887 = 3367331) B3367331
theorem B2559961 : Blo 2243435 2559961 := bbase (se 2 (by rfl) ⟨959985, by rfl⟩ : syracuseStep 2559961 = 1919971) (by norm_num)
theorem B3413281 : Blo 2243435 3413281 := bstep (se 2 (by rfl) ⟨1279980, by rfl⟩ : syracuseStep 3413281 = 2559961) B2559961
theorem B4551041 : Blo 2243435 4551041 := bstep (se 2 (by rfl) ⟨1706640, by rfl⟩ : syracuseStep 4551041 = 3413281) B3413281
theorem B3034027 : Blo 2243435 3034027 := bstep (se 1 (by rfl) ⟨2275520, by rfl⟩ : syracuseStep 3034027 = 4551041) B4551041
theorem B16181477 : Blo 2243435 16181477 := bstep (se 4 (by rfl) ⟨1517013, by rfl⟩ : syracuseStep 16181477 = 3034027) B3034027
theorem B10787651 : Blo 2243435 10787651 := bstep (se 1 (by rfl) ⟨8090738, by rfl⟩ : syracuseStep 10787651 = 16181477) B16181477
theorem B7191767 : Blo 2243435 7191767 := bstep (se 1 (by rfl) ⟨5393825, by rfl⟩ : syracuseStep 7191767 = 10787651) B10787651
theorem B19178045 : Blo 2243435 19178045 := bstep (se 3 (by rfl) ⟨3595883, by rfl⟩ : syracuseStep 19178045 = 7191767) B7191767
theorem B12785363 : Blo 2243435 12785363 := bstep (se 1 (by rfl) ⟨9589022, by rfl⟩ : syracuseStep 12785363 = 19178045) B19178045
theorem B8523575 : Blo 2243435 8523575 := bstep (se 1 (by rfl) ⟨6392681, by rfl⟩ : syracuseStep 8523575 = 12785363) B12785363
theorem B5682383 : Blo 2243435 5682383 := bstep (se 1 (by rfl) ⟨4261787, by rfl⟩ : syracuseStep 5682383 = 8523575) B8523575
theorem B3788255 : Blo 2243435 3788255 := bstep (se 1 (by rfl) ⟨2841191, by rfl⟩ : syracuseStep 3788255 = 5682383) B5682383
theorem B2525503 : Blo 2243435 2525503 := bstep (se 1 (by rfl) ⟨1894127, by rfl⟩ : syracuseStep 2525503 = 3788255) B3788255
theorem B3367337 : Blo 2243435 3367337 := bstep (se 2 (by rfl) ⟨1262751, by rfl⟩ : syracuseStep 3367337 = 2525503) B2525503
theorem B2244891 : Blo 2243435 2244891 := bstep (se 1 (by rfl) ⟨1683668, by rfl⟩ : syracuseStep 2244891 = 3367337) B3367337
theorem B8523589 : Blo 2243435 8523589 := bbase (se 4 (by rfl) ⟨799086, by rfl⟩ : syracuseStep 8523589 = 1598173) (by norm_num)
theorem B11364785 : Blo 2243435 11364785 := bstep (se 2 (by rfl) ⟨4261794, by rfl⟩ : syracuseStep 11364785 = 8523589) B8523589
theorem B7576523 : Blo 2243435 7576523 := bstep (se 1 (by rfl) ⟨5682392, by rfl⟩ : syracuseStep 7576523 = 11364785) B11364785
theorem B5051015 : Blo 2243435 5051015 := bstep (se 1 (by rfl) ⟨3788261, by rfl⟩ : syracuseStep 5051015 = 7576523) B7576523
theorem B3367343 : Blo 2243435 3367343 := bstep (se 1 (by rfl) ⟨2525507, by rfl⟩ : syracuseStep 3367343 = 5051015) B5051015
theorem B2244895 : Blo 2243435 2244895 := bstep (se 1 (by rfl) ⟨1683671, by rfl⟩ : syracuseStep 2244895 = 3367343) B3367343
theorem B3367349 : Blo 2243435 3367349 := bbase (se 5 (by rfl) ⟨157844, by rfl⟩ : syracuseStep 3367349 = 315689) (by norm_num)
theorem B2244899 : Blo 2243435 2244899 := bstep (se 1 (by rfl) ⟨1683674, by rfl⟩ : syracuseStep 2244899 = 3367349) B3367349
theorem B5682413 : Blo 2243435 5682413 := bbase (se 3 (by rfl) ⟨1065452, by rfl⟩ : syracuseStep 5682413 = 2130905) (by norm_num)
theorem B3788275 : Blo 2243435 3788275 := bstep (se 1 (by rfl) ⟨2841206, by rfl⟩ : syracuseStep 3788275 = 5682413) B5682413
theorem B5051033 : Blo 2243435 5051033 := bstep (se 2 (by rfl) ⟨1894137, by rfl⟩ : syracuseStep 5051033 = 3788275) B3788275
theorem B3367355 : Blo 2243435 3367355 := bstep (se 1 (by rfl) ⟨2525516, by rfl⟩ : syracuseStep 3367355 = 5051033) B5051033
theorem B2244903 : Blo 2243435 2244903 := bstep (se 1 (by rfl) ⟨1683677, by rfl⟩ : syracuseStep 2244903 = 3367355) B3367355
theorem B2525521 : Blo 2243435 2525521 := bbase (se 2 (by rfl) ⟨947070, by rfl⟩ : syracuseStep 2525521 = 1894141) (by norm_num)
theorem B3367361 : Blo 2243435 3367361 := bstep (se 2 (by rfl) ⟨1262760, by rfl⟩ : syracuseStep 3367361 = 2525521) B2525521
theorem B2244907 : Blo 2243435 2244907 := bstep (se 1 (by rfl) ⟨1683680, by rfl⟩ : syracuseStep 2244907 = 3367361) B3367361
theorem B2397277 : Blo 2243435 2397277 := bbase (se 3 (by rfl) ⟨449489, by rfl⟩ : syracuseStep 2397277 = 898979) (by norm_num)
theorem B3196369 : Blo 2243435 3196369 := bstep (se 2 (by rfl) ⟨1198638, by rfl⟩ : syracuseStep 3196369 = 2397277) B2397277
theorem B4261825 : Blo 2243435 4261825 := bstep (se 2 (by rfl) ⟨1598184, by rfl⟩ : syracuseStep 4261825 = 3196369) B3196369
theorem B5682433 : Blo 2243435 5682433 := bstep (se 2 (by rfl) ⟨2130912, by rfl⟩ : syracuseStep 5682433 = 4261825) B4261825
theorem B7576577 : Blo 2243435 7576577 := bstep (se 2 (by rfl) ⟨2841216, by rfl⟩ : syracuseStep 7576577 = 5682433) B5682433
theorem B5051051 : Blo 2243435 5051051 := bstep (se 1 (by rfl) ⟨3788288, by rfl⟩ : syracuseStep 5051051 = 7576577) B7576577
theorem B3367367 : Blo 2243435 3367367 := bstep (se 1 (by rfl) ⟨2525525, by rfl⟩ : syracuseStep 3367367 = 5051051) B5051051
theorem B2244911 : Blo 2243435 2244911 := bstep (se 1 (by rfl) ⟨1683683, by rfl⟩ : syracuseStep 2244911 = 3367367) B3367367
theorem B3367373 : Blo 2243435 3367373 := bbase (se 3 (by rfl) ⟨631382, by rfl⟩ : syracuseStep 3367373 = 1262765) (by norm_num)
theorem B2244915 : Blo 2243435 2244915 := bstep (se 1 (by rfl) ⟨1683686, by rfl⟩ : syracuseStep 2244915 = 3367373) B3367373
theorem B5051069 : Blo 2243435 5051069 := bbase (se 3 (by rfl) ⟨947075, by rfl⟩ : syracuseStep 5051069 = 1894151) (by norm_num)
theorem B3367379 : Blo 2243435 3367379 := bstep (se 1 (by rfl) ⟨2525534, by rfl⟩ : syracuseStep 3367379 = 5051069) B5051069
theorem B2244919 : Blo 2243435 2244919 := bstep (se 1 (by rfl) ⟨1683689, by rfl⟩ : syracuseStep 2244919 = 3367379) B3367379
theorem B3788309 : Blo 2243435 3788309 := bbase (se 6 (by rfl) ⟨88788, by rfl⟩ : syracuseStep 3788309 = 177577) (by norm_num)
theorem B2525539 : Blo 2243435 2525539 := bstep (se 1 (by rfl) ⟨1894154, by rfl⟩ : syracuseStep 2525539 = 3788309) B3788309
theorem B3367385 : Blo 2243435 3367385 := bstep (se 2 (by rfl) ⟨1262769, by rfl⟩ : syracuseStep 3367385 = 2525539) B2525539
theorem B2244923 : Blo 2243435 2244923 := bstep (se 1 (by rfl) ⟨1683692, by rfl⟩ : syracuseStep 2244923 = 3367385) B3367385
theorem B7680005 : Blo 2243435 7680005 := bbase (se 4 (by rfl) ⟨720000, by rfl⟩ : syracuseStep 7680005 = 1440001) (by norm_num)
theorem B5120003 : Blo 2243435 5120003 := bstep (se 1 (by rfl) ⟨3840002, by rfl⟩ : syracuseStep 5120003 = 7680005) B7680005
theorem B3413335 : Blo 2243435 3413335 := bstep (se 1 (by rfl) ⟨2560001, by rfl⟩ : syracuseStep 3413335 = 5120003) B5120003
theorem B4551113 : Blo 2243435 4551113 := bstep (se 2 (by rfl) ⟨1706667, by rfl⟩ : syracuseStep 4551113 = 3413335) B3413335
theorem B12136301 : Blo 2243435 12136301 := bstep (se 3 (by rfl) ⟨2275556, by rfl⟩ : syracuseStep 12136301 = 4551113) B4551113
theorem B8090867 : Blo 2243435 8090867 := bstep (se 1 (by rfl) ⟨6068150, by rfl⟩ : syracuseStep 8090867 = 12136301) B12136301
theorem B21575645 : Blo 2243435 21575645 := bstep (se 3 (by rfl) ⟨4045433, by rfl⟩ : syracuseStep 21575645 = 8090867) B8090867
theorem B14383763 : Blo 2243435 14383763 := bstep (se 1 (by rfl) ⟨10787822, by rfl⟩ : syracuseStep 14383763 = 21575645) B21575645
theorem B9589175 : Blo 2243435 9589175 := bstep (se 1 (by rfl) ⟨7191881, by rfl⟩ : syracuseStep 9589175 = 14383763) B14383763
theorem B6392783 : Blo 2243435 6392783 := bstep (se 1 (by rfl) ⟨4794587, by rfl⟩ : syracuseStep 6392783 = 9589175) B9589175
theorem B17047421 : Blo 2243435 17047421 := bstep (se 3 (by rfl) ⟨3196391, by rfl⟩ : syracuseStep 17047421 = 6392783) B6392783
theorem B11364947 : Blo 2243435 11364947 := bstep (se 1 (by rfl) ⟨8523710, by rfl⟩ : syracuseStep 11364947 = 17047421) B17047421
theorem B7576631 : Blo 2243435 7576631 := bstep (se 1 (by rfl) ⟨5682473, by rfl⟩ : syracuseStep 7576631 = 11364947) B11364947
theorem B5051087 : Blo 2243435 5051087 := bstep (se 1 (by rfl) ⟨3788315, by rfl⟩ : syracuseStep 5051087 = 7576631) B7576631
theorem B3367391 : Blo 2243435 3367391 := bstep (se 1 (by rfl) ⟨2525543, by rfl⟩ : syracuseStep 3367391 = 5051087) B5051087
theorem B2244927 : Blo 2243435 2244927 := bstep (se 1 (by rfl) ⟨1683695, by rfl⟩ : syracuseStep 2244927 = 3367391) B3367391
theorem B3367397 : Blo 2243435 3367397 := bbase (se 4 (by rfl) ⟨315693, by rfl⟩ : syracuseStep 3367397 = 631387) (by norm_num)
theorem B2244931 : Blo 2243435 2244931 := bstep (se 1 (by rfl) ⟨1683698, by rfl⟩ : syracuseStep 2244931 = 3367397) B3367397
theorem B2275565 : Blo 2243435 2275565 := bbase (se 3 (by rfl) ⟨426668, by rfl⟩ : syracuseStep 2275565 = 853337) (by norm_num)
theorem B24272693 : Blo 2243435 24272693 := bstep (se 5 (by rfl) ⟨1137782, by rfl⟩ : syracuseStep 24272693 = 2275565) B2275565
theorem B16181795 : Blo 2243435 16181795 := bstep (se 1 (by rfl) ⟨12136346, by rfl⟩ : syracuseStep 16181795 = 24272693) B24272693
theorem B10787863 : Blo 2243435 10787863 := bstep (se 1 (by rfl) ⟨8090897, by rfl⟩ : syracuseStep 10787863 = 16181795) B16181795
theorem B14383817 : Blo 2243435 14383817 := bstep (se 2 (by rfl) ⟨5393931, by rfl⟩ : syracuseStep 14383817 = 10787863) B10787863
theorem B9589211 : Blo 2243435 9589211 := bstep (se 1 (by rfl) ⟨7191908, by rfl⟩ : syracuseStep 9589211 = 14383817) B14383817
theorem B6392807 : Blo 2243435 6392807 := bstep (se 1 (by rfl) ⟨4794605, by rfl⟩ : syracuseStep 6392807 = 9589211) B9589211
theorem B4261871 : Blo 2243435 4261871 := bstep (se 1 (by rfl) ⟨3196403, by rfl⟩ : syracuseStep 4261871 = 6392807) B6392807
theorem B2841247 : Blo 2243435 2841247 := bstep (se 1 (by rfl) ⟨2130935, by rfl⟩ : syracuseStep 2841247 = 4261871) B4261871
theorem B3788329 : Blo 2243435 3788329 := bstep (se 2 (by rfl) ⟨1420623, by rfl⟩ : syracuseStep 3788329 = 2841247) B2841247
theorem B5051105 : Blo 2243435 5051105 := bstep (se 2 (by rfl) ⟨1894164, by rfl⟩ : syracuseStep 5051105 = 3788329) B3788329
theorem B3367403 : Blo 2243435 3367403 := bstep (se 1 (by rfl) ⟨2525552, by rfl⟩ : syracuseStep 3367403 = 5051105) B5051105
theorem B2244935 : Blo 2243435 2244935 := bstep (se 1 (by rfl) ⟨1683701, by rfl⟩ : syracuseStep 2244935 = 3367403) B3367403
theorem B2525557 : Blo 2243435 2525557 := bbase (se 5 (by rfl) ⟨118385, by rfl⟩ : syracuseStep 2525557 = 236771) (by norm_num)
theorem B3367409 : Blo 2243435 3367409 := bstep (se 2 (by rfl) ⟨1262778, by rfl⟩ : syracuseStep 3367409 = 2525557) B2525557
theorem B2244939 : Blo 2243435 2244939 := bstep (se 1 (by rfl) ⟨1683704, by rfl⟩ : syracuseStep 2244939 = 3367409) B3367409
theorem B2841257 : Blo 2243435 2841257 := bbase (se 2 (by rfl) ⟨1065471, by rfl⟩ : syracuseStep 2841257 = 2130943) (by norm_num)
theorem B7576685 : Blo 2243435 7576685 := bstep (se 3 (by rfl) ⟨1420628, by rfl⟩ : syracuseStep 7576685 = 2841257) B2841257
theorem B5051123 : Blo 2243435 5051123 := bstep (se 1 (by rfl) ⟨3788342, by rfl⟩ : syracuseStep 5051123 = 7576685) B7576685
theorem B3367415 : Blo 2243435 3367415 := bstep (se 1 (by rfl) ⟨2525561, by rfl⟩ : syracuseStep 3367415 = 5051123) B5051123
theorem B2244943 : Blo 2243435 2244943 := bstep (se 1 (by rfl) ⟨1683707, by rfl⟩ : syracuseStep 2244943 = 3367415) B3367415
theorem B3367421 : Blo 2243435 3367421 := bbase (se 3 (by rfl) ⟨631391, by rfl⟩ : syracuseStep 3367421 = 1262783) (by norm_num)
theorem B2244947 : Blo 2243435 2244947 := bstep (se 1 (by rfl) ⟨1683710, by rfl⟩ : syracuseStep 2244947 = 3367421) B3367421
theorem B5051141 : Blo 2243435 5051141 := bbase (se 4 (by rfl) ⟨473544, by rfl⟩ : syracuseStep 5051141 = 947089) (by norm_num)
theorem B3367427 : Blo 2243435 3367427 := bstep (se 1 (by rfl) ⟨2525570, by rfl⟩ : syracuseStep 3367427 = 5051141) B5051141
theorem B2244951 : Blo 2243435 2244951 := bstep (se 1 (by rfl) ⟨1683713, by rfl⟩ : syracuseStep 2244951 = 3367427) B3367427
theorem B4261909 : Blo 2243435 4261909 := bbase (se 6 (by rfl) ⟨99888, by rfl⟩ : syracuseStep 4261909 = 199777) (by norm_num)
theorem B5682545 : Blo 2243435 5682545 := bstep (se 2 (by rfl) ⟨2130954, by rfl⟩ : syracuseStep 5682545 = 4261909) B4261909
theorem B3788363 : Blo 2243435 3788363 := bstep (se 1 (by rfl) ⟨2841272, by rfl⟩ : syracuseStep 3788363 = 5682545) B5682545
theorem B2525575 : Blo 2243435 2525575 := bstep (se 1 (by rfl) ⟨1894181, by rfl⟩ : syracuseStep 2525575 = 3788363) B3788363
theorem B3367433 : Blo 2243435 3367433 := bstep (se 2 (by rfl) ⟨1262787, by rfl⟩ : syracuseStep 3367433 = 2525575) B2525575
theorem B2244955 : Blo 2243435 2244955 := bstep (se 1 (by rfl) ⟨1683716, by rfl⟩ : syracuseStep 2244955 = 3367433) B3367433
theorem B11365109 : Blo 2243435 11365109 := bbase (se 5 (by rfl) ⟨532739, by rfl⟩ : syracuseStep 11365109 = 1065479) (by norm_num)
theorem B7576739 : Blo 2243435 7576739 := bstep (se 1 (by rfl) ⟨5682554, by rfl⟩ : syracuseStep 7576739 = 11365109) B11365109
theorem B5051159 : Blo 2243435 5051159 := bstep (se 1 (by rfl) ⟨3788369, by rfl⟩ : syracuseStep 5051159 = 7576739) B7576739
theorem B3367439 : Blo 2243435 3367439 := bstep (se 1 (by rfl) ⟨2525579, by rfl⟩ : syracuseStep 3367439 = 5051159) B5051159
theorem B2244959 : Blo 2243435 2244959 := bstep (se 1 (by rfl) ⟨1683719, by rfl⟩ : syracuseStep 2244959 = 3367439) B3367439
theorem B3367445 : Blo 2243435 3367445 := bbase (se 6 (by rfl) ⟨78924, by rfl⟩ : syracuseStep 3367445 = 157849) (by norm_num)
theorem B2244963 : Blo 2243435 2244963 := bstep (se 1 (by rfl) ⟨1683722, by rfl⟩ : syracuseStep 2244963 = 3367445) B3367445
theorem B3596005 : Blo 2243435 3596005 := bbase (se 4 (by rfl) ⟨337125, by rfl⟩ : syracuseStep 3596005 = 674251) (by norm_num)
theorem B19178693 : Blo 2243435 19178693 := bstep (se 4 (by rfl) ⟨1798002, by rfl⟩ : syracuseStep 19178693 = 3596005) B3596005
theorem B12785795 : Blo 2243435 12785795 := bstep (se 1 (by rfl) ⟨9589346, by rfl⟩ : syracuseStep 12785795 = 19178693) B19178693
theorem B8523863 : Blo 2243435 8523863 := bstep (se 1 (by rfl) ⟨6392897, by rfl⟩ : syracuseStep 8523863 = 12785795) B12785795
theorem B5682575 : Blo 2243435 5682575 := bstep (se 1 (by rfl) ⟨4261931, by rfl⟩ : syracuseStep 5682575 = 8523863) B8523863
theorem B3788383 : Blo 2243435 3788383 := bstep (se 1 (by rfl) ⟨2841287, by rfl⟩ : syracuseStep 3788383 = 5682575) B5682575
theorem B5051177 : Blo 2243435 5051177 := bstep (se 2 (by rfl) ⟨1894191, by rfl⟩ : syracuseStep 5051177 = 3788383) B3788383
theorem B3367451 : Blo 2243435 3367451 := bstep (se 1 (by rfl) ⟨2525588, by rfl⟩ : syracuseStep 3367451 = 5051177) B5051177
theorem B2244967 : Blo 2243435 2244967 := bstep (se 1 (by rfl) ⟨1683725, by rfl⟩ : syracuseStep 2244967 = 3367451) B3367451
theorem B2525593 : Blo 2243435 2525593 := bbase (se 2 (by rfl) ⟨947097, by rfl⟩ : syracuseStep 2525593 = 1894195) (by norm_num)
theorem B3367457 : Blo 2243435 3367457 := bstep (se 2 (by rfl) ⟨1262796, by rfl⟩ : syracuseStep 3367457 = 2525593) B2525593
theorem B2244971 : Blo 2243435 2244971 := bstep (se 1 (by rfl) ⟨1683728, by rfl⟩ : syracuseStep 2244971 = 3367457) B3367457
theorem B8523893 : Blo 2243435 8523893 := bbase (se 5 (by rfl) ⟨399557, by rfl⟩ : syracuseStep 8523893 = 799115) (by norm_num)
theorem B5682595 : Blo 2243435 5682595 := bstep (se 1 (by rfl) ⟨4261946, by rfl⟩ : syracuseStep 5682595 = 8523893) B8523893
theorem B7576793 : Blo 2243435 7576793 := bstep (se 2 (by rfl) ⟨2841297, by rfl⟩ : syracuseStep 7576793 = 5682595) B5682595
theorem B5051195 : Blo 2243435 5051195 := bstep (se 1 (by rfl) ⟨3788396, by rfl⟩ : syracuseStep 5051195 = 7576793) B7576793
theorem B3367463 : Blo 2243435 3367463 := bstep (se 1 (by rfl) ⟨2525597, by rfl⟩ : syracuseStep 3367463 = 5051195) B5051195
theorem B2244975 : Blo 2243435 2244975 := bstep (se 1 (by rfl) ⟨1683731, by rfl⟩ : syracuseStep 2244975 = 3367463) B3367463
theorem B3367469 : Blo 2243435 3367469 := bbase (se 3 (by rfl) ⟨631400, by rfl⟩ : syracuseStep 3367469 = 1262801) (by norm_num)
theorem B2244979 : Blo 2243435 2244979 := bstep (se 1 (by rfl) ⟨1683734, by rfl⟩ : syracuseStep 2244979 = 3367469) B3367469
theorem B5051213 : Blo 2243435 5051213 := bbase (se 3 (by rfl) ⟨947102, by rfl⟩ : syracuseStep 5051213 = 1894205) (by norm_num)
theorem B3367475 : Blo 2243435 3367475 := bstep (se 1 (by rfl) ⟨2525606, by rfl⟩ : syracuseStep 3367475 = 5051213) B5051213
theorem B2244983 : Blo 2243435 2244983 := bstep (se 1 (by rfl) ⟨1683737, by rfl⟩ : syracuseStep 2244983 = 3367475) B3367475
theorem B2841313 : Blo 2243435 2841313 := bbase (se 2 (by rfl) ⟨1065492, by rfl⟩ : syracuseStep 2841313 = 2130985) (by norm_num)
theorem B3788417 : Blo 2243435 3788417 := bstep (se 2 (by rfl) ⟨1420656, by rfl⟩ : syracuseStep 3788417 = 2841313) B2841313
theorem B2525611 : Blo 2243435 2525611 := bstep (se 1 (by rfl) ⟨1894208, by rfl⟩ : syracuseStep 2525611 = 3788417) B3788417
theorem B3367481 : Blo 2243435 3367481 := bstep (se 2 (by rfl) ⟨1262805, by rfl⟩ : syracuseStep 3367481 = 2525611) B2525611
theorem B2244987 : Blo 2243435 2244987 := bstep (se 1 (by rfl) ⟨1683740, by rfl⟩ : syracuseStep 2244987 = 3367481) B3367481
theorem B25571861 : Blo 2243435 25571861 := bbase (se 6 (by rfl) ⟨599340, by rfl⟩ : syracuseStep 25571861 = 1198681) (by norm_num)
theorem B17047907 : Blo 2243435 17047907 := bstep (se 1 (by rfl) ⟨12785930, by rfl⟩ : syracuseStep 17047907 = 25571861) B25571861
theorem B11365271 : Blo 2243435 11365271 := bstep (se 1 (by rfl) ⟨8523953, by rfl⟩ : syracuseStep 11365271 = 17047907) B17047907
theorem B7576847 : Blo 2243435 7576847 := bstep (se 1 (by rfl) ⟨5682635, by rfl⟩ : syracuseStep 7576847 = 11365271) B11365271
theorem B5051231 : Blo 2243435 5051231 := bstep (se 1 (by rfl) ⟨3788423, by rfl⟩ : syracuseStep 5051231 = 7576847) B7576847
theorem B3367487 : Blo 2243435 3367487 := bstep (se 1 (by rfl) ⟨2525615, by rfl⟩ : syracuseStep 3367487 = 5051231) B5051231
theorem B2244991 : Blo 2243435 2244991 := bstep (se 1 (by rfl) ⟨1683743, by rfl⟩ : syracuseStep 2244991 = 3367487) B3367487
theorem B3367493 : Blo 2243435 3367493 := bbase (se 4 (by rfl) ⟨315702, by rfl⟩ : syracuseStep 3367493 = 631405) (by norm_num)
theorem B2244995 : Blo 2243435 2244995 := bstep (se 1 (by rfl) ⟨1683746, by rfl⟩ : syracuseStep 2244995 = 3367493) B3367493
theorem B3788437 : Blo 2243435 3788437 := bbase (se 6 (by rfl) ⟨88791, by rfl⟩ : syracuseStep 3788437 = 177583) (by norm_num)
theorem B5051249 : Blo 2243435 5051249 := bstep (se 2 (by rfl) ⟨1894218, by rfl⟩ : syracuseStep 5051249 = 3788437) B3788437
theorem B3367499 : Blo 2243435 3367499 := bstep (se 1 (by rfl) ⟨2525624, by rfl⟩ : syracuseStep 3367499 = 5051249) B5051249
theorem B2244999 : Blo 2243435 2244999 := bstep (se 1 (by rfl) ⟨1683749, by rfl⟩ : syracuseStep 2244999 = 3367499) B3367499
theorem B2525629 : Blo 2243435 2525629 := bbase (se 3 (by rfl) ⟨473555, by rfl⟩ : syracuseStep 2525629 = 947111) (by norm_num)
theorem B3367505 : Blo 2243435 3367505 := bstep (se 2 (by rfl) ⟨1262814, by rfl⟩ : syracuseStep 3367505 = 2525629) B2525629
theorem B2245003 : Blo 2243435 2245003 := bstep (se 1 (by rfl) ⟨1683752, by rfl⟩ : syracuseStep 2245003 = 3367505) B3367505
theorem B7576901 : Blo 2243435 7576901 := bbase (se 4 (by rfl) ⟨710334, by rfl⟩ : syracuseStep 7576901 = 1420669) (by norm_num)
theorem B5051267 : Blo 2243435 5051267 := bstep (se 1 (by rfl) ⟨3788450, by rfl⟩ : syracuseStep 5051267 = 7576901) B7576901
theorem B3367511 : Blo 2243435 3367511 := bstep (se 1 (by rfl) ⟨2525633, by rfl⟩ : syracuseStep 3367511 = 5051267) B5051267
theorem B2245007 : Blo 2243435 2245007 := bstep (se 1 (by rfl) ⟨1683755, by rfl⟩ : syracuseStep 2245007 = 3367511) B3367511
theorem B3367517 : Blo 2243435 3367517 := bbase (se 3 (by rfl) ⟨631409, by rfl⟩ : syracuseStep 3367517 = 1262819) (by norm_num)
theorem B2245011 : Blo 2243435 2245011 := bstep (se 1 (by rfl) ⟨1683758, by rfl⟩ : syracuseStep 2245011 = 3367517) B3367517
theorem B5051285 : Blo 2243435 5051285 := bbase (se 6 (by rfl) ⟨118389, by rfl⟩ : syracuseStep 5051285 = 236779) (by norm_num)
theorem B3367523 : Blo 2243435 3367523 := bstep (se 1 (by rfl) ⟨2525642, by rfl⟩ : syracuseStep 3367523 = 5051285) B5051285
theorem B2245015 : Blo 2243435 2245015 := bstep (se 1 (by rfl) ⟨1683761, by rfl⟩ : syracuseStep 2245015 = 3367523) B3367523
theorem B3413477 : Blo 2243435 3413477 := bbase (se 4 (by rfl) ⟨320013, by rfl⟩ : syracuseStep 3413477 = 640027) (by norm_num)
theorem B2275651 : Blo 2243435 2275651 := bstep (se 1 (by rfl) ⟨1706738, by rfl⟩ : syracuseStep 2275651 = 3413477) B3413477
theorem B3034201 : Blo 2243435 3034201 := bstep (se 2 (by rfl) ⟨1137825, by rfl⟩ : syracuseStep 3034201 = 2275651) B2275651
theorem B4045601 : Blo 2243435 4045601 := bstep (se 2 (by rfl) ⟨1517100, by rfl⟩ : syracuseStep 4045601 = 3034201) B3034201
theorem B2697067 : Blo 2243435 2697067 := bstep (se 1 (by rfl) ⟨2022800, by rfl⟩ : syracuseStep 2697067 = 4045601) B4045601
theorem B3596089 : Blo 2243435 3596089 := bstep (se 2 (by rfl) ⟨1348533, by rfl⟩ : syracuseStep 3596089 = 2697067) B2697067
theorem B4794785 : Blo 2243435 4794785 := bstep (se 2 (by rfl) ⟨1798044, by rfl⟩ : syracuseStep 4794785 = 3596089) B3596089
theorem B3196523 : Blo 2243435 3196523 := bstep (se 1 (by rfl) ⟨2397392, by rfl⟩ : syracuseStep 3196523 = 4794785) B4794785
theorem B8524061 : Blo 2243435 8524061 := bstep (se 3 (by rfl) ⟨1598261, by rfl⟩ : syracuseStep 8524061 = 3196523) B3196523
theorem B5682707 : Blo 2243435 5682707 := bstep (se 1 (by rfl) ⟨4262030, by rfl⟩ : syracuseStep 5682707 = 8524061) B8524061
theorem B3788471 : Blo 2243435 3788471 := bstep (se 1 (by rfl) ⟨2841353, by rfl⟩ : syracuseStep 3788471 = 5682707) B5682707
theorem B2525647 : Blo 2243435 2525647 := bstep (se 1 (by rfl) ⟨1894235, by rfl⟩ : syracuseStep 2525647 = 3788471) B3788471
theorem B3367529 : Blo 2243435 3367529 := bstep (se 2 (by rfl) ⟨1262823, by rfl⟩ : syracuseStep 3367529 = 2525647) B2525647
theorem B2245019 : Blo 2243435 2245019 := bstep (se 1 (by rfl) ⟨1683764, by rfl⟩ : syracuseStep 2245019 = 3367529) B3367529
theorem B2919421 : Blo 2243435 2919421 := bbase (se 3 (by rfl) ⟨547391, by rfl⟩ : syracuseStep 2919421 = 1094783) (by norm_num)
theorem B15570245 : Blo 2243435 15570245 := bstep (se 4 (by rfl) ⟨1459710, by rfl⟩ : syracuseStep 15570245 = 2919421) B2919421
theorem B10380163 : Blo 2243435 10380163 := bstep (se 1 (by rfl) ⟨7785122, by rfl⟩ : syracuseStep 10380163 = 15570245) B15570245
theorem B13840217 : Blo 2243435 13840217 := bstep (se 2 (by rfl) ⟨5190081, by rfl⟩ : syracuseStep 13840217 = 10380163) B10380163
theorem B9226811 : Blo 2243435 9226811 := bstep (se 1 (by rfl) ⟨6920108, by rfl⟩ : syracuseStep 9226811 = 13840217) B13840217
theorem B24604829 : Blo 2243435 24604829 := bstep (se 3 (by rfl) ⟨4613405, by rfl⟩ : syracuseStep 24604829 = 9226811) B9226811
theorem B16403219 : Blo 2243435 16403219 := bstep (se 1 (by rfl) ⟨12302414, by rfl⟩ : syracuseStep 16403219 = 24604829) B24604829
theorem B10935479 : Blo 2243435 10935479 := bstep (se 1 (by rfl) ⟨8201609, by rfl⟩ : syracuseStep 10935479 = 16403219) B16403219
theorem B7290319 : Blo 2243435 7290319 := bstep (se 1 (by rfl) ⟨5467739, by rfl⟩ : syracuseStep 7290319 = 10935479) B10935479
theorem B9720425 : Blo 2243435 9720425 := bstep (se 2 (by rfl) ⟨3645159, by rfl⟩ : syracuseStep 9720425 = 7290319) B7290319
theorem B6480283 : Blo 2243435 6480283 := bstep (se 1 (by rfl) ⟨4860212, by rfl⟩ : syracuseStep 6480283 = 9720425) B9720425
theorem B8640377 : Blo 2243435 8640377 := bstep (se 2 (by rfl) ⟨3240141, by rfl⟩ : syracuseStep 8640377 = 6480283) B6480283
theorem B5760251 : Blo 2243435 5760251 := bstep (se 1 (by rfl) ⟨4320188, by rfl⟩ : syracuseStep 5760251 = 8640377) B8640377
theorem B3840167 : Blo 2243435 3840167 := bstep (se 1 (by rfl) ⟨2880125, by rfl⟩ : syracuseStep 3840167 = 5760251) B5760251
theorem B10240445 : Blo 2243435 10240445 := bstep (se 3 (by rfl) ⟨1920083, by rfl⟩ : syracuseStep 10240445 = 3840167) B3840167
theorem B6826963 : Blo 2243435 6826963 := bstep (se 1 (by rfl) ⟨5120222, by rfl⟩ : syracuseStep 6826963 = 10240445) B10240445
theorem B9102617 : Blo 2243435 9102617 := bstep (se 2 (by rfl) ⟨3413481, by rfl⟩ : syracuseStep 9102617 = 6826963) B6826963
theorem B6068411 : Blo 2243435 6068411 := bstep (se 1 (by rfl) ⟨4551308, by rfl⟩ : syracuseStep 6068411 = 9102617) B9102617
theorem B4045607 : Blo 2243435 4045607 := bstep (se 1 (by rfl) ⟨3034205, by rfl⟩ : syracuseStep 4045607 = 6068411) B6068411
theorem B2697071 : Blo 2243435 2697071 := bstep (se 1 (by rfl) ⟨2022803, by rfl⟩ : syracuseStep 2697071 = 4045607) B4045607
theorem B7192189 : Blo 2243435 7192189 := bstep (se 3 (by rfl) ⟨1348535, by rfl⟩ : syracuseStep 7192189 = 2697071) B2697071
theorem B9589585 : Blo 2243435 9589585 := bstep (se 2 (by rfl) ⟨3596094, by rfl⟩ : syracuseStep 9589585 = 7192189) B7192189
theorem B12786113 : Blo 2243435 12786113 := bstep (se 2 (by rfl) ⟨4794792, by rfl⟩ : syracuseStep 12786113 = 9589585) B9589585
theorem B8524075 : Blo 2243435 8524075 := bstep (se 1 (by rfl) ⟨6393056, by rfl⟩ : syracuseStep 8524075 = 12786113) B12786113
theorem B11365433 : Blo 2243435 11365433 := bstep (se 2 (by rfl) ⟨4262037, by rfl⟩ : syracuseStep 11365433 = 8524075) B8524075
theorem B7576955 : Blo 2243435 7576955 := bstep (se 1 (by rfl) ⟨5682716, by rfl⟩ : syracuseStep 7576955 = 11365433) B11365433
theorem B5051303 : Blo 2243435 5051303 := bstep (se 1 (by rfl) ⟨3788477, by rfl⟩ : syracuseStep 5051303 = 7576955) B7576955
theorem B3367535 : Blo 2243435 3367535 := bstep (se 1 (by rfl) ⟨2525651, by rfl⟩ : syracuseStep 3367535 = 5051303) B5051303
theorem B2245023 : Blo 2243435 2245023 := bstep (se 1 (by rfl) ⟨1683767, by rfl⟩ : syracuseStep 2245023 = 3367535) B3367535
theorem B3367541 : Blo 2243435 3367541 := bbase (se 5 (by rfl) ⟨157853, by rfl⟩ : syracuseStep 3367541 = 315707) (by norm_num)
theorem B2245027 : Blo 2243435 2245027 := bstep (se 1 (by rfl) ⟨1683770, by rfl⟩ : syracuseStep 2245027 = 3367541) B3367541
theorem B4262053 : Blo 2243435 4262053 := bbase (se 4 (by rfl) ⟨399567, by rfl⟩ : syracuseStep 4262053 = 799135) (by norm_num)
theorem B5682737 : Blo 2243435 5682737 := bstep (se 2 (by rfl) ⟨2131026, by rfl⟩ : syracuseStep 5682737 = 4262053) B4262053
theorem B3788491 : Blo 2243435 3788491 := bstep (se 1 (by rfl) ⟨2841368, by rfl⟩ : syracuseStep 3788491 = 5682737) B5682737
theorem B5051321 : Blo 2243435 5051321 := bstep (se 2 (by rfl) ⟨1894245, by rfl⟩ : syracuseStep 5051321 = 3788491) B3788491
theorem B3367547 : Blo 2243435 3367547 := bstep (se 1 (by rfl) ⟨2525660, by rfl⟩ : syracuseStep 3367547 = 5051321) B5051321
theorem B2245031 : Blo 2243435 2245031 := bstep (se 1 (by rfl) ⟨1683773, by rfl⟩ : syracuseStep 2245031 = 3367547) B3367547
theorem B2525665 : Blo 2243435 2525665 := bbase (se 2 (by rfl) ⟨947124, by rfl⟩ : syracuseStep 2525665 = 1894249) (by norm_num)
theorem B3367553 : Blo 2243435 3367553 := bstep (se 2 (by rfl) ⟨1262832, by rfl⟩ : syracuseStep 3367553 = 2525665) B2525665
theorem B2245035 : Blo 2243435 2245035 := bstep (se 1 (by rfl) ⟨1683776, by rfl⟩ : syracuseStep 2245035 = 3367553) B3367553
theorem B5682757 : Blo 2243435 5682757 := bbase (se 4 (by rfl) ⟨532758, by rfl⟩ : syracuseStep 5682757 = 1065517) (by norm_num)
theorem B7577009 : Blo 2243435 7577009 := bstep (se 2 (by rfl) ⟨2841378, by rfl⟩ : syracuseStep 7577009 = 5682757) B5682757
theorem B5051339 : Blo 2243435 5051339 := bstep (se 1 (by rfl) ⟨3788504, by rfl⟩ : syracuseStep 5051339 = 7577009) B7577009
theorem B3367559 : Blo 2243435 3367559 := bstep (se 1 (by rfl) ⟨2525669, by rfl⟩ : syracuseStep 3367559 = 5051339) B5051339
theorem B2245039 : Blo 2243435 2245039 := bstep (se 1 (by rfl) ⟨1683779, by rfl⟩ : syracuseStep 2245039 = 3367559) B3367559
theorem B3367565 : Blo 2243435 3367565 := bbase (se 3 (by rfl) ⟨631418, by rfl⟩ : syracuseStep 3367565 = 1262837) (by norm_num)
theorem B2245043 : Blo 2243435 2245043 := bstep (se 1 (by rfl) ⟨1683782, by rfl⟩ : syracuseStep 2245043 = 3367565) B3367565
theorem B5051357 : Blo 2243435 5051357 := bbase (se 3 (by rfl) ⟨947129, by rfl⟩ : syracuseStep 5051357 = 1894259) (by norm_num)
theorem B3367571 : Blo 2243435 3367571 := bstep (se 1 (by rfl) ⟨2525678, by rfl⟩ : syracuseStep 3367571 = 5051357) B5051357
theorem B2245047 : Blo 2243435 2245047 := bstep (se 1 (by rfl) ⟨1683785, by rfl⟩ : syracuseStep 2245047 = 3367571) B3367571
theorem B3788525 : Blo 2243435 3788525 := bbase (se 3 (by rfl) ⟨710348, by rfl⟩ : syracuseStep 3788525 = 1420697) (by norm_num)
theorem B2525683 : Blo 2243435 2525683 := bstep (se 1 (by rfl) ⟨1894262, by rfl⟩ : syracuseStep 2525683 = 3788525) B3788525
theorem B3367577 : Blo 2243435 3367577 := bstep (se 2 (by rfl) ⟨1262841, by rfl⟩ : syracuseStep 3367577 = 2525683) B2525683
theorem B2245051 : Blo 2243435 2245051 := bstep (se 1 (by rfl) ⟨1683788, by rfl⟩ : syracuseStep 2245051 = 3367577) B3367577
theorem B10788437 : Blo 2243435 10788437 := bbase (se 8 (by rfl) ⟨63213, by rfl⟩ : syracuseStep 10788437 = 126427) (by norm_num)
theorem B28769165 : Blo 2243435 28769165 := bstep (se 3 (by rfl) ⟨5394218, by rfl⟩ : syracuseStep 28769165 = 10788437) B10788437
theorem B19179443 : Blo 2243435 19179443 := bstep (se 1 (by rfl) ⟨14384582, by rfl⟩ : syracuseStep 19179443 = 28769165) B28769165
theorem B12786295 : Blo 2243435 12786295 := bstep (se 1 (by rfl) ⟨9589721, by rfl⟩ : syracuseStep 12786295 = 19179443) B19179443
theorem B17048393 : Blo 2243435 17048393 := bstep (se 2 (by rfl) ⟨6393147, by rfl⟩ : syracuseStep 17048393 = 12786295) B12786295
theorem B11365595 : Blo 2243435 11365595 := bstep (se 1 (by rfl) ⟨8524196, by rfl⟩ : syracuseStep 11365595 = 17048393) B17048393
theorem B7577063 : Blo 2243435 7577063 := bstep (se 1 (by rfl) ⟨5682797, by rfl⟩ : syracuseStep 7577063 = 11365595) B11365595
theorem B5051375 : Blo 2243435 5051375 := bstep (se 1 (by rfl) ⟨3788531, by rfl⟩ : syracuseStep 5051375 = 7577063) B7577063
theorem B3367583 : Blo 2243435 3367583 := bstep (se 1 (by rfl) ⟨2525687, by rfl⟩ : syracuseStep 3367583 = 5051375) B5051375
theorem B2245055 : Blo 2243435 2245055 := bstep (se 1 (by rfl) ⟨1683791, by rfl⟩ : syracuseStep 2245055 = 3367583) B3367583
theorem B3367589 : Blo 2243435 3367589 := bbase (se 4 (by rfl) ⟨315711, by rfl⟩ : syracuseStep 3367589 = 631423) (by norm_num)
theorem B2245059 : Blo 2243435 2245059 := bstep (se 1 (by rfl) ⟨1683794, by rfl⟩ : syracuseStep 2245059 = 3367589) B3367589
theorem B2841409 : Blo 2243435 2841409 := bbase (se 2 (by rfl) ⟨1065528, by rfl⟩ : syracuseStep 2841409 = 2131057) (by norm_num)
theorem B3788545 : Blo 2243435 3788545 := bstep (se 2 (by rfl) ⟨1420704, by rfl⟩ : syracuseStep 3788545 = 2841409) B2841409
theorem B5051393 : Blo 2243435 5051393 := bstep (se 2 (by rfl) ⟨1894272, by rfl⟩ : syracuseStep 5051393 = 3788545) B3788545
theorem B3367595 : Blo 2243435 3367595 := bstep (se 1 (by rfl) ⟨2525696, by rfl⟩ : syracuseStep 3367595 = 5051393) B5051393
theorem B2245063 : Blo 2243435 2245063 := bstep (se 1 (by rfl) ⟨1683797, by rfl⟩ : syracuseStep 2245063 = 3367595) B3367595
theorem B2525701 : Blo 2243435 2525701 := bbase (se 4 (by rfl) ⟨236784, by rfl⟩ : syracuseStep 2525701 = 473569) (by norm_num)
theorem B3367601 : Blo 2243435 3367601 := bstep (se 2 (by rfl) ⟨1262850, by rfl⟩ : syracuseStep 3367601 = 2525701) B2525701
theorem B2245067 : Blo 2243435 2245067 := bstep (se 1 (by rfl) ⟨1683800, by rfl⟩ : syracuseStep 2245067 = 3367601) B3367601
theorem B3196597 : Blo 2243435 3196597 := bbase (se 5 (by rfl) ⟨149840, by rfl⟩ : syracuseStep 3196597 = 299681) (by norm_num)
theorem B4262129 : Blo 2243435 4262129 := bstep (se 2 (by rfl) ⟨1598298, by rfl⟩ : syracuseStep 4262129 = 3196597) B3196597
theorem B2841419 : Blo 2243435 2841419 := bstep (se 1 (by rfl) ⟨2131064, by rfl⟩ : syracuseStep 2841419 = 4262129) B4262129
theorem B7577117 : Blo 2243435 7577117 := bstep (se 3 (by rfl) ⟨1420709, by rfl⟩ : syracuseStep 7577117 = 2841419) B2841419
theorem B5051411 : Blo 2243435 5051411 := bstep (se 1 (by rfl) ⟨3788558, by rfl⟩ : syracuseStep 5051411 = 7577117) B7577117
theorem B3367607 : Blo 2243435 3367607 := bstep (se 1 (by rfl) ⟨2525705, by rfl⟩ : syracuseStep 3367607 = 5051411) B5051411
theorem B2245071 : Blo 2243435 2245071 := bstep (se 1 (by rfl) ⟨1683803, by rfl⟩ : syracuseStep 2245071 = 3367607) B3367607
theorem B3367613 : Blo 2243435 3367613 := bbase (se 3 (by rfl) ⟨631427, by rfl⟩ : syracuseStep 3367613 = 1262855) (by norm_num)
theorem B2245075 : Blo 2243435 2245075 := bstep (se 1 (by rfl) ⟨1683806, by rfl⟩ : syracuseStep 2245075 = 3367613) B3367613
theorem B5051429 : Blo 2243435 5051429 := bbase (se 4 (by rfl) ⟨473571, by rfl⟩ : syracuseStep 5051429 = 947143) (by norm_num)
theorem B3367619 : Blo 2243435 3367619 := bstep (se 1 (by rfl) ⟨2525714, by rfl⟩ : syracuseStep 3367619 = 5051429) B5051429
theorem B2245079 : Blo 2243435 2245079 := bstep (se 1 (by rfl) ⟨1683809, by rfl⟩ : syracuseStep 2245079 = 3367619) B3367619
theorem B5682869 : Blo 2243435 5682869 := bbase (se 5 (by rfl) ⟨266384, by rfl⟩ : syracuseStep 5682869 = 532769) (by norm_num)
theorem B3788579 : Blo 2243435 3788579 := bstep (se 1 (by rfl) ⟨2841434, by rfl⟩ : syracuseStep 3788579 = 5682869) B5682869
theorem B2525719 : Blo 2243435 2525719 := bstep (se 1 (by rfl) ⟨1894289, by rfl⟩ : syracuseStep 2525719 = 3788579) B3788579
theorem B3367625 : Blo 2243435 3367625 := bstep (se 2 (by rfl) ⟨1262859, by rfl⟩ : syracuseStep 3367625 = 2525719) B2525719
theorem B2245083 : Blo 2243435 2245083 := bstep (se 1 (by rfl) ⟨1683812, by rfl⟩ : syracuseStep 2245083 = 3367625) B3367625
theorem B14384789 : Blo 2243435 14384789 := bbase (se 6 (by rfl) ⟨337143, by rfl⟩ : syracuseStep 14384789 = 674287) (by norm_num)
theorem B9589859 : Blo 2243435 9589859 := bstep (se 1 (by rfl) ⟨7192394, by rfl⟩ : syracuseStep 9589859 = 14384789) B14384789
theorem B6393239 : Blo 2243435 6393239 := bstep (se 1 (by rfl) ⟨4794929, by rfl⟩ : syracuseStep 6393239 = 9589859) B9589859
theorem B4262159 : Blo 2243435 4262159 := bstep (se 1 (by rfl) ⟨3196619, by rfl⟩ : syracuseStep 4262159 = 6393239) B6393239
theorem B11365757 : Blo 2243435 11365757 := bstep (se 3 (by rfl) ⟨2131079, by rfl⟩ : syracuseStep 11365757 = 4262159) B4262159
theorem B7577171 : Blo 2243435 7577171 := bstep (se 1 (by rfl) ⟨5682878, by rfl⟩ : syracuseStep 7577171 = 11365757) B11365757
theorem B5051447 : Blo 2243435 5051447 := bstep (se 1 (by rfl) ⟨3788585, by rfl⟩ : syracuseStep 5051447 = 7577171) B7577171
theorem B3367631 : Blo 2243435 3367631 := bstep (se 1 (by rfl) ⟨2525723, by rfl⟩ : syracuseStep 3367631 = 5051447) B5051447
theorem B2245087 : Blo 2243435 2245087 := bstep (se 1 (by rfl) ⟨1683815, by rfl⟩ : syracuseStep 2245087 = 3367631) B3367631
theorem B3367637 : Blo 2243435 3367637 := bbase (se 7 (by rfl) ⟨39464, by rfl⟩ : syracuseStep 3367637 = 78929) (by norm_num)
theorem B2245091 : Blo 2243435 2245091 := bstep (se 1 (by rfl) ⟨1683818, by rfl⟩ : syracuseStep 2245091 = 3367637) B3367637
theorem B7192421 : Blo 2243435 7192421 := bbase (se 4 (by rfl) ⟨674289, by rfl⟩ : syracuseStep 7192421 = 1348579) (by norm_num)
theorem B4794947 : Blo 2243435 4794947 := bstep (se 1 (by rfl) ⟨3596210, by rfl⟩ : syracuseStep 4794947 = 7192421) B7192421
theorem B3196631 : Blo 2243435 3196631 := bstep (se 1 (by rfl) ⟨2397473, by rfl⟩ : syracuseStep 3196631 = 4794947) B4794947
theorem B8524349 : Blo 2243435 8524349 := bstep (se 3 (by rfl) ⟨1598315, by rfl⟩ : syracuseStep 8524349 = 3196631) B3196631
theorem B5682899 : Blo 2243435 5682899 := bstep (se 1 (by rfl) ⟨4262174, by rfl⟩ : syracuseStep 5682899 = 8524349) B8524349
theorem B3788599 : Blo 2243435 3788599 := bstep (se 1 (by rfl) ⟨2841449, by rfl⟩ : syracuseStep 3788599 = 5682899) B5682899
theorem B5051465 : Blo 2243435 5051465 := bstep (se 2 (by rfl) ⟨1894299, by rfl⟩ : syracuseStep 5051465 = 3788599) B3788599
theorem B3367643 : Blo 2243435 3367643 := bstep (se 1 (by rfl) ⟨2525732, by rfl⟩ : syracuseStep 3367643 = 5051465) B5051465
theorem B2245095 : Blo 2243435 2245095 := bstep (se 1 (by rfl) ⟨1683821, by rfl⟩ : syracuseStep 2245095 = 3367643) B3367643
theorem B2525737 : Blo 2243435 2525737 := bbase (se 2 (by rfl) ⟨947151, by rfl⟩ : syracuseStep 2525737 = 1894303) (by norm_num)
theorem B3367649 : Blo 2243435 3367649 := bstep (se 2 (by rfl) ⟨1262868, by rfl⟩ : syracuseStep 3367649 = 2525737) B2525737
theorem B2245099 : Blo 2243435 2245099 := bstep (se 1 (by rfl) ⟨1683824, by rfl⟩ : syracuseStep 2245099 = 3367649) B3367649
theorem B8219045 : Blo 2243435 8219045 := bbase (se 4 (by rfl) ⟨770535, by rfl⟩ : syracuseStep 8219045 = 1541071) (by norm_num)
theorem B5479363 : Blo 2243435 5479363 := bstep (se 1 (by rfl) ⟨4109522, by rfl⟩ : syracuseStep 5479363 = 8219045) B8219045
theorem B7305817 : Blo 2243435 7305817 := bstep (se 2 (by rfl) ⟨2739681, by rfl⟩ : syracuseStep 7305817 = 5479363) B5479363
theorem B9741089 : Blo 2243435 9741089 := bstep (se 2 (by rfl) ⟨3652908, by rfl⟩ : syracuseStep 9741089 = 7305817) B7305817
theorem B6494059 : Blo 2243435 6494059 := bstep (se 1 (by rfl) ⟨4870544, by rfl⟩ : syracuseStep 6494059 = 9741089) B9741089
theorem B34634981 : Blo 2243435 34634981 := bstep (se 4 (by rfl) ⟨3247029, by rfl⟩ : syracuseStep 34634981 = 6494059) B6494059
theorem B23089987 : Blo 2243435 23089987 := bstep (se 1 (by rfl) ⟨17317490, by rfl⟩ : syracuseStep 23089987 = 34634981) B34634981
theorem B30786649 : Blo 2243435 30786649 := bstep (se 2 (by rfl) ⟨11544993, by rfl⟩ : syracuseStep 30786649 = 23089987) B23089987
theorem B164195461 : Blo 2243435 164195461 := bstep (se 4 (by rfl) ⟨15393324, by rfl⟩ : syracuseStep 164195461 = 30786649) B30786649
theorem B218927281 : Blo 2243435 218927281 := bstep (se 2 (by rfl) ⟨82097730, by rfl⟩ : syracuseStep 218927281 = 164195461) B164195461
theorem B291903041 : Blo 2243435 291903041 := bstep (se 2 (by rfl) ⟨109463640, by rfl⟩ : syracuseStep 291903041 = 218927281) B218927281
theorem B194602027 : Blo 2243435 194602027 := bstep (se 1 (by rfl) ⟨145951520, by rfl⟩ : syracuseStep 194602027 = 291903041) B291903041
theorem B259469369 : Blo 2243435 259469369 := bstep (se 2 (by rfl) ⟨97301013, by rfl⟩ : syracuseStep 259469369 = 194602027) B194602027
theorem B172979579 : Blo 2243435 172979579 := bstep (se 1 (by rfl) ⟨129734684, by rfl⟩ : syracuseStep 172979579 = 259469369) B259469369
theorem B115319719 : Blo 2243435 115319719 := bstep (se 1 (by rfl) ⟨86489789, by rfl⟩ : syracuseStep 115319719 = 172979579) B172979579
theorem B153759625 : Blo 2243435 153759625 := bstep (se 2 (by rfl) ⟨57659859, by rfl⟩ : syracuseStep 153759625 = 115319719) B115319719
theorem B820051333 : Blo 2243435 820051333 := bstep (se 4 (by rfl) ⟨76879812, by rfl⟩ : syracuseStep 820051333 = 153759625) B153759625
theorem B17494428437 : Blo 2243435 17494428437 := bstep (se 6 (by rfl) ⟨410025666, by rfl⟩ : syracuseStep 17494428437 = 820051333) B820051333
theorem B11662952291 : Blo 2243435 11662952291 := bstep (se 1 (by rfl) ⟨8747214218, by rfl⟩ : syracuseStep 11662952291 = 17494428437) B17494428437
theorem B7775301527 : Blo 2243435 7775301527 := bstep (se 1 (by rfl) ⟨5831476145, by rfl⟩ : syracuseStep 7775301527 = 11662952291) B11662952291
theorem B5183534351 : Blo 2243435 5183534351 := bstep (se 1 (by rfl) ⟨3887650763, by rfl⟩ : syracuseStep 5183534351 = 7775301527) B7775301527
theorem B3455689567 : Blo 2243435 3455689567 := bstep (se 1 (by rfl) ⟨2591767175, by rfl⟩ : syracuseStep 3455689567 = 5183534351) B5183534351
theorem B4607586089 : Blo 2243435 4607586089 := bstep (se 2 (by rfl) ⟨1727844783, by rfl⟩ : syracuseStep 4607586089 = 3455689567) B3455689567
theorem B3071724059 : Blo 2243435 3071724059 := bstep (se 1 (by rfl) ⟨2303793044, by rfl⟩ : syracuseStep 3071724059 = 4607586089) B4607586089
theorem B2047816039 : Blo 2243435 2047816039 := bstep (se 1 (by rfl) ⟨1535862029, by rfl⟩ : syracuseStep 2047816039 = 3071724059) B3071724059
theorem B2730421385 : Blo 2243435 2730421385 := bstep (se 2 (by rfl) ⟨1023908019, by rfl⟩ : syracuseStep 2730421385 = 2047816039) B2047816039
theorem B1820280923 : Blo 2243435 1820280923 := bstep (se 1 (by rfl) ⟨1365210692, by rfl⟩ : syracuseStep 1820280923 = 2730421385) B2730421385
theorem B1213520615 : Blo 2243435 1213520615 := bstep (se 1 (by rfl) ⟨910140461, by rfl⟩ : syracuseStep 1213520615 = 1820280923) B1820280923
theorem B809013743 : Blo 2243435 809013743 := bstep (se 1 (by rfl) ⟨606760307, by rfl⟩ : syracuseStep 809013743 = 1213520615) B1213520615
theorem B539342495 : Blo 2243435 539342495 := bstep (se 1 (by rfl) ⟨404506871, by rfl⟩ : syracuseStep 539342495 = 809013743) B809013743
theorem B359561663 : Blo 2243435 359561663 := bstep (se 1 (by rfl) ⟨269671247, by rfl⟩ : syracuseStep 359561663 = 539342495) B539342495
theorem B239707775 : Blo 2243435 239707775 := bstep (se 1 (by rfl) ⟨179780831, by rfl⟩ : syracuseStep 239707775 = 359561663) B359561663
theorem B639220733 : Blo 2243435 639220733 := bstep (se 3 (by rfl) ⟨119853887, by rfl⟩ : syracuseStep 639220733 = 239707775) B239707775
theorem B426147155 : Blo 2243435 426147155 := bstep (se 1 (by rfl) ⟨319610366, by rfl⟩ : syracuseStep 426147155 = 639220733) B639220733
theorem B284098103 : Blo 2243435 284098103 := bstep (se 1 (by rfl) ⟨213073577, by rfl⟩ : syracuseStep 284098103 = 426147155) B426147155
theorem B189398735 : Blo 2243435 189398735 := bstep (se 1 (by rfl) ⟨142049051, by rfl⟩ : syracuseStep 189398735 = 284098103) B284098103
theorem B126265823 : Blo 2243435 126265823 := bstep (se 1 (by rfl) ⟨94699367, by rfl⟩ : syracuseStep 126265823 = 189398735) B189398735
theorem B84177215 : Blo 2243435 84177215 := bstep (se 1 (by rfl) ⟨63132911, by rfl⟩ : syracuseStep 84177215 = 126265823) B126265823
theorem B56118143 : Blo 2243435 56118143 := bstep (se 1 (by rfl) ⟨42088607, by rfl⟩ : syracuseStep 56118143 = 84177215) B84177215
theorem B149648381 : Blo 2243435 149648381 := bstep (se 3 (by rfl) ⟨28059071, by rfl⟩ : syracuseStep 149648381 = 56118143) B56118143
theorem B99765587 : Blo 2243435 99765587 := bstep (se 1 (by rfl) ⟨74824190, by rfl⟩ : syracuseStep 99765587 = 149648381) B149648381
theorem B66510391 : Blo 2243435 66510391 := bstep (se 1 (by rfl) ⟨49882793, by rfl⟩ : syracuseStep 66510391 = 99765587) B99765587
theorem B88680521 : Blo 2243435 88680521 := bstep (se 2 (by rfl) ⟨33255195, by rfl⟩ : syracuseStep 88680521 = 66510391) B66510391
theorem B236481389 : Blo 2243435 236481389 := bstep (se 3 (by rfl) ⟨44340260, by rfl⟩ : syracuseStep 236481389 = 88680521) B88680521
theorem B157654259 : Blo 2243435 157654259 := bstep (se 1 (by rfl) ⟨118240694, by rfl⟩ : syracuseStep 157654259 = 236481389) B236481389
theorem B105102839 : Blo 2243435 105102839 := bstep (se 1 (by rfl) ⟨78827129, by rfl⟩ : syracuseStep 105102839 = 157654259) B157654259
theorem B70068559 : Blo 2243435 70068559 := bstep (se 1 (by rfl) ⟨52551419, by rfl⟩ : syracuseStep 70068559 = 105102839) B105102839
theorem B93424745 : Blo 2243435 93424745 := bstep (se 2 (by rfl) ⟨35034279, by rfl⟩ : syracuseStep 93424745 = 70068559) B70068559
theorem B62283163 : Blo 2243435 62283163 := bstep (se 1 (by rfl) ⟨46712372, by rfl⟩ : syracuseStep 62283163 = 93424745) B93424745
theorem B83044217 : Blo 2243435 83044217 := bstep (se 2 (by rfl) ⟨31141581, by rfl⟩ : syracuseStep 83044217 = 62283163) B62283163
theorem B55362811 : Blo 2243435 55362811 := bstep (se 1 (by rfl) ⟨41522108, by rfl⟩ : syracuseStep 55362811 = 83044217) B83044217
theorem B73817081 : Blo 2243435 73817081 := bstep (se 2 (by rfl) ⟨27681405, by rfl⟩ : syracuseStep 73817081 = 55362811) B55362811
theorem B49211387 : Blo 2243435 49211387 := bstep (se 1 (by rfl) ⟨36908540, by rfl⟩ : syracuseStep 49211387 = 73817081) B73817081
theorem B32807591 : Blo 2243435 32807591 := bstep (se 1 (by rfl) ⟨24605693, by rfl⟩ : syracuseStep 32807591 = 49211387) B49211387
theorem B21871727 : Blo 2243435 21871727 := bstep (se 1 (by rfl) ⟨16403795, by rfl⟩ : syracuseStep 21871727 = 32807591) B32807591
theorem B14581151 : Blo 2243435 14581151 := bstep (se 1 (by rfl) ⟨10935863, by rfl⟩ : syracuseStep 14581151 = 21871727) B21871727
theorem B9720767 : Blo 2243435 9720767 := bstep (se 1 (by rfl) ⟨7290575, by rfl⟩ : syracuseStep 9720767 = 14581151) B14581151
theorem B25922045 : Blo 2243435 25922045 := bstep (se 3 (by rfl) ⟨4860383, by rfl⟩ : syracuseStep 25922045 = 9720767) B9720767
theorem B17281363 : Blo 2243435 17281363 := bstep (se 1 (by rfl) ⟨12961022, by rfl⟩ : syracuseStep 17281363 = 25922045) B25922045
theorem B23041817 : Blo 2243435 23041817 := bstep (se 2 (by rfl) ⟨8640681, by rfl⟩ : syracuseStep 23041817 = 17281363) B17281363
theorem B15361211 : Blo 2243435 15361211 := bstep (se 1 (by rfl) ⟨11520908, by rfl⟩ : syracuseStep 15361211 = 23041817) B23041817
theorem B40963229 : Blo 2243435 40963229 := bstep (se 3 (by rfl) ⟨7680605, by rfl⟩ : syracuseStep 40963229 = 15361211) B15361211
theorem B27308819 : Blo 2243435 27308819 := bstep (se 1 (by rfl) ⟨20481614, by rfl⟩ : syracuseStep 27308819 = 40963229) B40963229
theorem B18205879 : Blo 2243435 18205879 := bstep (se 1 (by rfl) ⟨13654409, by rfl⟩ : syracuseStep 18205879 = 27308819) B27308819
theorem B24274505 : Blo 2243435 24274505 := bstep (se 2 (by rfl) ⟨9102939, by rfl⟩ : syracuseStep 24274505 = 18205879) B18205879
theorem B16183003 : Blo 2243435 16183003 := bstep (se 1 (by rfl) ⟨12137252, by rfl⟩ : syracuseStep 16183003 = 24274505) B24274505
theorem B21577337 : Blo 2243435 21577337 := bstep (se 2 (by rfl) ⟨8091501, by rfl⟩ : syracuseStep 21577337 = 16183003) B16183003
theorem B14384891 : Blo 2243435 14384891 := bstep (se 1 (by rfl) ⟨10788668, by rfl⟩ : syracuseStep 14384891 = 21577337) B21577337
theorem B9589927 : Blo 2243435 9589927 := bstep (se 1 (by rfl) ⟨7192445, by rfl⟩ : syracuseStep 9589927 = 14384891) B14384891
theorem B12786569 : Blo 2243435 12786569 := bstep (se 2 (by rfl) ⟨4794963, by rfl⟩ : syracuseStep 12786569 = 9589927) B9589927
theorem B8524379 : Blo 2243435 8524379 := bstep (se 1 (by rfl) ⟨6393284, by rfl⟩ : syracuseStep 8524379 = 12786569) B12786569
theorem B5682919 : Blo 2243435 5682919 := bstep (se 1 (by rfl) ⟨4262189, by rfl⟩ : syracuseStep 5682919 = 8524379) B8524379
theorem B7577225 : Blo 2243435 7577225 := bstep (se 2 (by rfl) ⟨2841459, by rfl⟩ : syracuseStep 7577225 = 5682919) B5682919
theorem B5051483 : Blo 2243435 5051483 := bstep (se 1 (by rfl) ⟨3788612, by rfl⟩ : syracuseStep 5051483 = 7577225) B7577225
theorem B3367655 : Blo 2243435 3367655 := bstep (se 1 (by rfl) ⟨2525741, by rfl⟩ : syracuseStep 3367655 = 5051483) B5051483
theorem B2245103 : Blo 2243435 2245103 := bstep (se 1 (by rfl) ⟨1683827, by rfl⟩ : syracuseStep 2245103 = 3367655) B3367655
theorem B3367661 : Blo 2243435 3367661 := bbase (se 3 (by rfl) ⟨631436, by rfl⟩ : syracuseStep 3367661 = 1262873) (by norm_num)
theorem B2245107 : Blo 2243435 2245107 := bstep (se 1 (by rfl) ⟨1683830, by rfl⟩ : syracuseStep 2245107 = 3367661) B3367661
theorem B5051501 : Blo 2243435 5051501 := bbase (se 3 (by rfl) ⟨947156, by rfl⟩ : syracuseStep 5051501 = 1894313) (by norm_num)
theorem B3367667 : Blo 2243435 3367667 := bstep (se 1 (by rfl) ⟨2525750, by rfl⟩ : syracuseStep 3367667 = 5051501) B5051501
theorem B2245111 : Blo 2243435 2245111 := bstep (se 1 (by rfl) ⟨1683833, by rfl⟩ : syracuseStep 2245111 = 3367667) B3367667
theorem B4262213 : Blo 2243435 4262213 := bbase (se 4 (by rfl) ⟨399582, by rfl⟩ : syracuseStep 4262213 = 799165) (by norm_num)
theorem B2841475 : Blo 2243435 2841475 := bstep (se 1 (by rfl) ⟨2131106, by rfl⟩ : syracuseStep 2841475 = 4262213) B4262213
theorem B3788633 : Blo 2243435 3788633 := bstep (se 2 (by rfl) ⟨1420737, by rfl⟩ : syracuseStep 3788633 = 2841475) B2841475
theorem B2525755 : Blo 2243435 2525755 := bstep (se 1 (by rfl) ⟨1894316, by rfl⟩ : syracuseStep 2525755 = 3788633) B3788633
theorem B3367673 : Blo 2243435 3367673 := bstep (se 2 (by rfl) ⟨1262877, by rfl⟩ : syracuseStep 3367673 = 2525755) B2525755
theorem B2245115 : Blo 2243435 2245115 := bstep (se 1 (by rfl) ⟨1683836, by rfl⟩ : syracuseStep 2245115 = 3367673) B3367673
theorem B2733985 : Blo 2243435 2733985 := bbase (se 2 (by rfl) ⟨1025244, by rfl⟩ : syracuseStep 2733985 = 2050489) (by norm_num)
theorem B14581253 : Blo 2243435 14581253 := bstep (se 4 (by rfl) ⟨1366992, by rfl⟩ : syracuseStep 14581253 = 2733985) B2733985
theorem B38883341 : Blo 2243435 38883341 := bstep (se 3 (by rfl) ⟨7290626, by rfl⟩ : syracuseStep 38883341 = 14581253) B14581253
theorem B25922227 : Blo 2243435 25922227 := bstep (se 1 (by rfl) ⟨19441670, by rfl⟩ : syracuseStep 25922227 = 38883341) B38883341
theorem B34562969 : Blo 2243435 34562969 := bstep (se 2 (by rfl) ⟨12961113, by rfl⟩ : syracuseStep 34562969 = 25922227) B25922227
theorem B23041979 : Blo 2243435 23041979 := bstep (se 1 (by rfl) ⟨17281484, by rfl⟩ : syracuseStep 23041979 = 34562969) B34562969
theorem B15361319 : Blo 2243435 15361319 := bstep (se 1 (by rfl) ⟨11520989, by rfl⟩ : syracuseStep 15361319 = 23041979) B23041979
theorem B10240879 : Blo 2243435 10240879 := bstep (se 1 (by rfl) ⟨7680659, by rfl⟩ : syracuseStep 10240879 = 15361319) B15361319
theorem B13654505 : Blo 2243435 13654505 := bstep (se 2 (by rfl) ⟨5120439, by rfl⟩ : syracuseStep 13654505 = 10240879) B10240879
theorem B36412013 : Blo 2243435 36412013 := bstep (se 3 (by rfl) ⟨6827252, by rfl⟩ : syracuseStep 36412013 = 13654505) B13654505
theorem B24274675 : Blo 2243435 24274675 := bstep (se 1 (by rfl) ⟨18206006, by rfl⟩ : syracuseStep 24274675 = 36412013) B36412013
theorem B32366233 : Blo 2243435 32366233 := bstep (se 2 (by rfl) ⟨12137337, by rfl⟩ : syracuseStep 32366233 = 24274675) B24274675
theorem B43154977 : Blo 2243435 43154977 := bstep (se 2 (by rfl) ⟨16183116, by rfl⟩ : syracuseStep 43154977 = 32366233) B32366233
theorem B57539969 : Blo 2243435 57539969 := bstep (se 2 (by rfl) ⟨21577488, by rfl⟩ : syracuseStep 57539969 = 43154977) B43154977
theorem B38359979 : Blo 2243435 38359979 := bstep (se 1 (by rfl) ⟨28769984, by rfl⟩ : syracuseStep 38359979 = 57539969) B57539969
theorem B25573319 : Blo 2243435 25573319 := bstep (se 1 (by rfl) ⟨19179989, by rfl⟩ : syracuseStep 25573319 = 38359979) B38359979
theorem B17048879 : Blo 2243435 17048879 := bstep (se 1 (by rfl) ⟨12786659, by rfl⟩ : syracuseStep 17048879 = 25573319) B25573319
theorem B11365919 : Blo 2243435 11365919 := bstep (se 1 (by rfl) ⟨8524439, by rfl⟩ : syracuseStep 11365919 = 17048879) B17048879
theorem B7577279 : Blo 2243435 7577279 := bstep (se 1 (by rfl) ⟨5682959, by rfl⟩ : syracuseStep 7577279 = 11365919) B11365919
theorem B5051519 : Blo 2243435 5051519 := bstep (se 1 (by rfl) ⟨3788639, by rfl⟩ : syracuseStep 5051519 = 7577279) B7577279
theorem B3367679 : Blo 2243435 3367679 := bstep (se 1 (by rfl) ⟨2525759, by rfl⟩ : syracuseStep 3367679 = 5051519) B5051519
theorem B2245119 : Blo 2243435 2245119 := bstep (se 1 (by rfl) ⟨1683839, by rfl⟩ : syracuseStep 2245119 = 3367679) B3367679
theorem B3367685 : Blo 2243435 3367685 := bbase (se 4 (by rfl) ⟨315720, by rfl⟩ : syracuseStep 3367685 = 631441) (by norm_num)
theorem B2245123 : Blo 2243435 2245123 := bstep (se 1 (by rfl) ⟨1683842, by rfl⟩ : syracuseStep 2245123 = 3367685) B3367685
theorem B3788653 : Blo 2243435 3788653 := bbase (se 3 (by rfl) ⟨710372, by rfl⟩ : syracuseStep 3788653 = 1420745) (by norm_num)
theorem B5051537 : Blo 2243435 5051537 := bstep (se 2 (by rfl) ⟨1894326, by rfl⟩ : syracuseStep 5051537 = 3788653) B3788653
theorem B3367691 : Blo 2243435 3367691 := bstep (se 1 (by rfl) ⟨2525768, by rfl⟩ : syracuseStep 3367691 = 5051537) B5051537
theorem B2245127 : Blo 2243435 2245127 := bstep (se 1 (by rfl) ⟨1683845, by rfl⟩ : syracuseStep 2245127 = 3367691) B3367691
theorem B2525773 : Blo 2243435 2525773 := bbase (se 3 (by rfl) ⟨473582, by rfl⟩ : syracuseStep 2525773 = 947165) (by norm_num)
theorem B3367697 : Blo 2243435 3367697 := bstep (se 2 (by rfl) ⟨1262886, by rfl⟩ : syracuseStep 3367697 = 2525773) B2525773
theorem B2245131 : Blo 2243435 2245131 := bstep (se 1 (by rfl) ⟨1683848, by rfl⟩ : syracuseStep 2245131 = 3367697) B3367697
theorem B7577333 : Blo 2243435 7577333 := bbase (se 5 (by rfl) ⟨355187, by rfl⟩ : syracuseStep 7577333 = 710375) (by norm_num)
theorem B5051555 : Blo 2243435 5051555 := bstep (se 1 (by rfl) ⟨3788666, by rfl⟩ : syracuseStep 5051555 = 7577333) B7577333
theorem B3367703 : Blo 2243435 3367703 := bstep (se 1 (by rfl) ⟨2525777, by rfl⟩ : syracuseStep 3367703 = 5051555) B5051555
theorem B2245135 : Blo 2243435 2245135 := bstep (se 1 (by rfl) ⟨1683851, by rfl⟩ : syracuseStep 2245135 = 3367703) B3367703
theorem B3367709 : Blo 2243435 3367709 := bbase (se 3 (by rfl) ⟨631445, by rfl⟩ : syracuseStep 3367709 = 1262891) (by norm_num)
theorem B2245139 : Blo 2243435 2245139 := bstep (se 1 (by rfl) ⟨1683854, by rfl⟩ : syracuseStep 2245139 = 3367709) B3367709
theorem B5051573 : Blo 2243435 5051573 := bbase (se 5 (by rfl) ⟨236792, by rfl⟩ : syracuseStep 5051573 = 473585) (by norm_num)
theorem B3367715 : Blo 2243435 3367715 := bstep (se 1 (by rfl) ⟨2525786, by rfl⟩ : syracuseStep 3367715 = 5051573) B5051573
theorem B2245143 : Blo 2243435 2245143 := bstep (se 1 (by rfl) ⟨1683857, by rfl⟩ : syracuseStep 2245143 = 3367715) B3367715
theorem B2397529 : Blo 2243435 2397529 := bbase (se 2 (by rfl) ⟨899073, by rfl⟩ : syracuseStep 2397529 = 1798147) (by norm_num)
theorem B12786821 : Blo 2243435 12786821 := bstep (se 4 (by rfl) ⟨1198764, by rfl⟩ : syracuseStep 12786821 = 2397529) B2397529
theorem B8524547 : Blo 2243435 8524547 := bstep (se 1 (by rfl) ⟨6393410, by rfl⟩ : syracuseStep 8524547 = 12786821) B12786821
theorem B5683031 : Blo 2243435 5683031 := bstep (se 1 (by rfl) ⟨4262273, by rfl⟩ : syracuseStep 5683031 = 8524547) B8524547
theorem B3788687 : Blo 2243435 3788687 := bstep (se 1 (by rfl) ⟨2841515, by rfl⟩ : syracuseStep 3788687 = 5683031) B5683031
theorem B2525791 : Blo 2243435 2525791 := bstep (se 1 (by rfl) ⟨1894343, by rfl⟩ : syracuseStep 2525791 = 3788687) B3788687
theorem B3367721 : Blo 2243435 3367721 := bstep (se 2 (by rfl) ⟨1262895, by rfl⟩ : syracuseStep 3367721 = 2525791) B2525791
theorem B2245147 : Blo 2243435 2245147 := bstep (se 1 (by rfl) ⟨1683860, by rfl⟩ : syracuseStep 2245147 = 3367721) B3367721
theorem B2397533 : Blo 2243435 2397533 := bbase (se 3 (by rfl) ⟨449537, by rfl⟩ : syracuseStep 2397533 = 899075) (by norm_num)
theorem B6393421 : Blo 2243435 6393421 := bstep (se 3 (by rfl) ⟨1198766, by rfl⟩ : syracuseStep 6393421 = 2397533) B2397533
theorem B8524561 : Blo 2243435 8524561 := bstep (se 2 (by rfl) ⟨3196710, by rfl⟩ : syracuseStep 8524561 = 6393421) B6393421
theorem B11366081 : Blo 2243435 11366081 := bstep (se 2 (by rfl) ⟨4262280, by rfl⟩ : syracuseStep 11366081 = 8524561) B8524561
theorem B7577387 : Blo 2243435 7577387 := bstep (se 1 (by rfl) ⟨5683040, by rfl⟩ : syracuseStep 7577387 = 11366081) B11366081
theorem B5051591 : Blo 2243435 5051591 := bstep (se 1 (by rfl) ⟨3788693, by rfl⟩ : syracuseStep 5051591 = 7577387) B7577387
theorem B3367727 : Blo 2243435 3367727 := bstep (se 1 (by rfl) ⟨2525795, by rfl⟩ : syracuseStep 3367727 = 5051591) B5051591
theorem B2245151 : Blo 2243435 2245151 := bstep (se 1 (by rfl) ⟨1683863, by rfl⟩ : syracuseStep 2245151 = 3367727) B3367727
theorem B3367733 : Blo 2243435 3367733 := bbase (se 5 (by rfl) ⟨157862, by rfl⟩ : syracuseStep 3367733 = 315725) (by norm_num)
theorem B2245155 : Blo 2243435 2245155 := bstep (se 1 (by rfl) ⟨1683866, by rfl⟩ : syracuseStep 2245155 = 3367733) B3367733
theorem B5683061 : Blo 2243435 5683061 := bbase (se 5 (by rfl) ⟨266393, by rfl⟩ : syracuseStep 5683061 = 532787) (by norm_num)
theorem B3788707 : Blo 2243435 3788707 := bstep (se 1 (by rfl) ⟨2841530, by rfl⟩ : syracuseStep 3788707 = 5683061) B5683061
theorem B5051609 : Blo 2243435 5051609 := bstep (se 2 (by rfl) ⟨1894353, by rfl⟩ : syracuseStep 5051609 = 3788707) B3788707
theorem B3367739 : Blo 2243435 3367739 := bstep (se 1 (by rfl) ⟨2525804, by rfl⟩ : syracuseStep 3367739 = 5051609) B5051609
theorem B2245159 : Blo 2243435 2245159 := bstep (se 1 (by rfl) ⟨1683869, by rfl⟩ : syracuseStep 2245159 = 3367739) B3367739
theorem B2525809 : Blo 2243435 2525809 := bbase (se 2 (by rfl) ⟨947178, by rfl⟩ : syracuseStep 2525809 = 1894357) (by norm_num)
theorem B3367745 : Blo 2243435 3367745 := bstep (se 2 (by rfl) ⟨1262904, by rfl⟩ : syracuseStep 3367745 = 2525809) B2525809
theorem B2245163 : Blo 2243435 2245163 := bstep (se 1 (by rfl) ⟨1683872, by rfl⟩ : syracuseStep 2245163 = 3367745) B3367745
theorem B8091733 : Blo 2243435 8091733 := bbase (se 8 (by rfl) ⟨47412, by rfl⟩ : syracuseStep 8091733 = 94825) (by norm_num)
theorem B10788977 : Blo 2243435 10788977 := bstep (se 2 (by rfl) ⟨4045866, by rfl⟩ : syracuseStep 10788977 = 8091733) B8091733
theorem B7192651 : Blo 2243435 7192651 := bstep (se 1 (by rfl) ⟨5394488, by rfl⟩ : syracuseStep 7192651 = 10788977) B10788977
theorem B9590201 : Blo 2243435 9590201 := bstep (se 2 (by rfl) ⟨3596325, by rfl⟩ : syracuseStep 9590201 = 7192651) B7192651
theorem B6393467 : Blo 2243435 6393467 := bstep (se 1 (by rfl) ⟨4795100, by rfl⟩ : syracuseStep 6393467 = 9590201) B9590201
theorem B4262311 : Blo 2243435 4262311 := bstep (se 1 (by rfl) ⟨3196733, by rfl⟩ : syracuseStep 4262311 = 6393467) B6393467
theorem B5683081 : Blo 2243435 5683081 := bstep (se 2 (by rfl) ⟨2131155, by rfl⟩ : syracuseStep 5683081 = 4262311) B4262311
theorem B7577441 : Blo 2243435 7577441 := bstep (se 2 (by rfl) ⟨2841540, by rfl⟩ : syracuseStep 7577441 = 5683081) B5683081
theorem B5051627 : Blo 2243435 5051627 := bstep (se 1 (by rfl) ⟨3788720, by rfl⟩ : syracuseStep 5051627 = 7577441) B7577441
theorem B3367751 : Blo 2243435 3367751 := bstep (se 1 (by rfl) ⟨2525813, by rfl⟩ : syracuseStep 3367751 = 5051627) B5051627
theorem B2245167 : Blo 2243435 2245167 := bstep (se 1 (by rfl) ⟨1683875, by rfl⟩ : syracuseStep 2245167 = 3367751) B3367751
theorem B3367757 : Blo 2243435 3367757 := bbase (se 3 (by rfl) ⟨631454, by rfl⟩ : syracuseStep 3367757 = 1262909) (by norm_num)
theorem B2245171 : Blo 2243435 2245171 := bstep (se 1 (by rfl) ⟨1683878, by rfl⟩ : syracuseStep 2245171 = 3367757) B3367757
theorem B5051645 : Blo 2243435 5051645 := bbase (se 3 (by rfl) ⟨947183, by rfl⟩ : syracuseStep 5051645 = 1894367) (by norm_num)
theorem B3367763 : Blo 2243435 3367763 := bstep (se 1 (by rfl) ⟨2525822, by rfl⟩ : syracuseStep 3367763 = 5051645) B5051645
theorem B2245175 : Blo 2243435 2245175 := bstep (se 1 (by rfl) ⟨1683881, by rfl⟩ : syracuseStep 2245175 = 3367763) B3367763
theorem B3788741 : Blo 2243435 3788741 := bbase (se 4 (by rfl) ⟨355194, by rfl⟩ : syracuseStep 3788741 = 710389) (by norm_num)
theorem B2525827 : Blo 2243435 2525827 := bstep (se 1 (by rfl) ⟨1894370, by rfl⟩ : syracuseStep 2525827 = 3788741) B3788741
theorem B3367769 : Blo 2243435 3367769 := bstep (se 2 (by rfl) ⟨1262913, by rfl⟩ : syracuseStep 3367769 = 2525827) B2525827
theorem B2245179 : Blo 2243435 2245179 := bstep (se 1 (by rfl) ⟨1683884, by rfl⟩ : syracuseStep 2245179 = 3367769) B3367769
theorem B17049365 : Blo 2243435 17049365 := bbase (se 6 (by rfl) ⟨399594, by rfl⟩ : syracuseStep 17049365 = 799189) (by norm_num)
theorem B11366243 : Blo 2243435 11366243 := bstep (se 1 (by rfl) ⟨8524682, by rfl⟩ : syracuseStep 11366243 = 17049365) B17049365
theorem B7577495 : Blo 2243435 7577495 := bstep (se 1 (by rfl) ⟨5683121, by rfl⟩ : syracuseStep 7577495 = 11366243) B11366243
theorem B5051663 : Blo 2243435 5051663 := bstep (se 1 (by rfl) ⟨3788747, by rfl⟩ : syracuseStep 5051663 = 7577495) B7577495
theorem B3367775 : Blo 2243435 3367775 := bstep (se 1 (by rfl) ⟨2525831, by rfl⟩ : syracuseStep 3367775 = 5051663) B5051663
theorem B2245183 : Blo 2243435 2245183 := bstep (se 1 (by rfl) ⟨1683887, by rfl⟩ : syracuseStep 2245183 = 3367775) B3367775
theorem B3367781 : Blo 2243435 3367781 := bbase (se 4 (by rfl) ⟨315729, by rfl⟩ : syracuseStep 3367781 = 631459) (by norm_num)
theorem B2245187 : Blo 2243435 2245187 := bstep (se 1 (by rfl) ⟨1683890, by rfl⟩ : syracuseStep 2245187 = 3367781) B3367781
theorem B4262357 : Blo 2243435 4262357 := bbase (se 7 (by rfl) ⟨49949, by rfl⟩ : syracuseStep 4262357 = 99899) (by norm_num)
theorem B2841571 : Blo 2243435 2841571 := bstep (se 1 (by rfl) ⟨2131178, by rfl⟩ : syracuseStep 2841571 = 4262357) B4262357
theorem B3788761 : Blo 2243435 3788761 := bstep (se 2 (by rfl) ⟨1420785, by rfl⟩ : syracuseStep 3788761 = 2841571) B2841571
theorem B5051681 : Blo 2243435 5051681 := bstep (se 2 (by rfl) ⟨1894380, by rfl⟩ : syracuseStep 5051681 = 3788761) B3788761
theorem B3367787 : Blo 2243435 3367787 := bstep (se 1 (by rfl) ⟨2525840, by rfl⟩ : syracuseStep 3367787 = 5051681) B5051681
theorem B2245191 : Blo 2243435 2245191 := bstep (se 1 (by rfl) ⟨1683893, by rfl⟩ : syracuseStep 2245191 = 3367787) B3367787
theorem B2525845 : Blo 2243435 2525845 := bbase (se 6 (by rfl) ⟨59199, by rfl⟩ : syracuseStep 2525845 = 118399) (by norm_num)
theorem B3367793 : Blo 2243435 3367793 := bstep (se 2 (by rfl) ⟨1262922, by rfl⟩ : syracuseStep 3367793 = 2525845) B2525845
theorem B2245195 : Blo 2243435 2245195 := bstep (se 1 (by rfl) ⟨1683896, by rfl⟩ : syracuseStep 2245195 = 3367793) B3367793
theorem B2841581 : Blo 2243435 2841581 := bbase (se 3 (by rfl) ⟨532796, by rfl⟩ : syracuseStep 2841581 = 1065593) (by norm_num)
theorem B7577549 : Blo 2243435 7577549 := bstep (se 3 (by rfl) ⟨1420790, by rfl⟩ : syracuseStep 7577549 = 2841581) B2841581
theorem B5051699 : Blo 2243435 5051699 := bstep (se 1 (by rfl) ⟨3788774, by rfl⟩ : syracuseStep 5051699 = 7577549) B7577549
theorem B3367799 : Blo 2243435 3367799 := bstep (se 1 (by rfl) ⟨2525849, by rfl⟩ : syracuseStep 3367799 = 5051699) B5051699
theorem B2245199 : Blo 2243435 2245199 := bstep (se 1 (by rfl) ⟨1683899, by rfl⟩ : syracuseStep 2245199 = 3367799) B3367799
theorem B3367805 : Blo 2243435 3367805 := bbase (se 3 (by rfl) ⟨631463, by rfl⟩ : syracuseStep 3367805 = 1262927) (by norm_num)
theorem B2245203 : Blo 2243435 2245203 := bstep (se 1 (by rfl) ⟨1683902, by rfl⟩ : syracuseStep 2245203 = 3367805) B3367805
theorem B5051717 : Blo 2243435 5051717 := bbase (se 4 (by rfl) ⟨473598, by rfl⟩ : syracuseStep 5051717 = 947197) (by norm_num)
theorem B3367811 : Blo 2243435 3367811 := bstep (se 1 (by rfl) ⟨2525858, by rfl⟩ : syracuseStep 3367811 = 5051717) B5051717
theorem B2245207 : Blo 2243435 2245207 := bstep (se 1 (by rfl) ⟨1683905, by rfl⟩ : syracuseStep 2245207 = 3367811) B3367811
theorem B8091893 : Blo 2243435 8091893 := bbase (se 5 (by rfl) ⟨379307, by rfl⟩ : syracuseStep 8091893 = 758615) (by norm_num)
theorem B5394595 : Blo 2243435 5394595 := bstep (se 1 (by rfl) ⟨4045946, by rfl⟩ : syracuseStep 5394595 = 8091893) B8091893
theorem B7192793 : Blo 2243435 7192793 := bstep (se 2 (by rfl) ⟨2697297, by rfl⟩ : syracuseStep 7192793 = 5394595) B5394595
theorem B4795195 : Blo 2243435 4795195 := bstep (se 1 (by rfl) ⟨3596396, by rfl⟩ : syracuseStep 4795195 = 7192793) B7192793
theorem B6393593 : Blo 2243435 6393593 := bstep (se 2 (by rfl) ⟨2397597, by rfl⟩ : syracuseStep 6393593 = 4795195) B4795195
theorem B4262395 : Blo 2243435 4262395 := bstep (se 1 (by rfl) ⟨3196796, by rfl⟩ : syracuseStep 4262395 = 6393593) B6393593
theorem B5683193 : Blo 2243435 5683193 := bstep (se 2 (by rfl) ⟨2131197, by rfl⟩ : syracuseStep 5683193 = 4262395) B4262395
theorem B3788795 : Blo 2243435 3788795 := bstep (se 1 (by rfl) ⟨2841596, by rfl⟩ : syracuseStep 3788795 = 5683193) B5683193
theorem B2525863 : Blo 2243435 2525863 := bstep (se 1 (by rfl) ⟨1894397, by rfl⟩ : syracuseStep 2525863 = 3788795) B3788795
theorem B3367817 : Blo 2243435 3367817 := bstep (se 2 (by rfl) ⟨1262931, by rfl⟩ : syracuseStep 3367817 = 2525863) B2525863
theorem B2245211 : Blo 2243435 2245211 := bstep (se 1 (by rfl) ⟨1683908, by rfl⟩ : syracuseStep 2245211 = 3367817) B3367817
theorem B11366405 : Blo 2243435 11366405 := bbase (se 4 (by rfl) ⟨1065600, by rfl⟩ : syracuseStep 11366405 = 2131201) (by norm_num)
theorem B7577603 : Blo 2243435 7577603 := bstep (se 1 (by rfl) ⟨5683202, by rfl⟩ : syracuseStep 7577603 = 11366405) B11366405
theorem B5051735 : Blo 2243435 5051735 := bstep (se 1 (by rfl) ⟨3788801, by rfl⟩ : syracuseStep 5051735 = 7577603) B7577603
theorem B3367823 : Blo 2243435 3367823 := bstep (se 1 (by rfl) ⟨2525867, by rfl⟩ : syracuseStep 3367823 = 5051735) B5051735
theorem B2245215 : Blo 2243435 2245215 := bstep (se 1 (by rfl) ⟨1683911, by rfl⟩ : syracuseStep 2245215 = 3367823) B3367823
theorem B3367829 : Blo 2243435 3367829 := bbase (se 6 (by rfl) ⟨78933, by rfl⟩ : syracuseStep 3367829 = 157867) (by norm_num)
theorem B2245219 : Blo 2243435 2245219 := bstep (se 1 (by rfl) ⟨1683914, by rfl⟩ : syracuseStep 2245219 = 3367829) B3367829
theorem B12787253 : Blo 2243435 12787253 := bbase (se 5 (by rfl) ⟨599402, by rfl⟩ : syracuseStep 12787253 = 1198805) (by norm_num)
theorem B8524835 : Blo 2243435 8524835 := bstep (se 1 (by rfl) ⟨6393626, by rfl⟩ : syracuseStep 8524835 = 12787253) B12787253
theorem B5683223 : Blo 2243435 5683223 := bstep (se 1 (by rfl) ⟨4262417, by rfl⟩ : syracuseStep 5683223 = 8524835) B8524835
theorem B3788815 : Blo 2243435 3788815 := bstep (se 1 (by rfl) ⟨2841611, by rfl⟩ : syracuseStep 3788815 = 5683223) B5683223
theorem B5051753 : Blo 2243435 5051753 := bstep (se 2 (by rfl) ⟨1894407, by rfl⟩ : syracuseStep 5051753 = 3788815) B3788815
theorem B3367835 : Blo 2243435 3367835 := bstep (se 1 (by rfl) ⟨2525876, by rfl⟩ : syracuseStep 3367835 = 5051753) B5051753
theorem B2245223 : Blo 2243435 2245223 := bstep (se 1 (by rfl) ⟨1683917, by rfl⟩ : syracuseStep 2245223 = 3367835) B3367835
theorem B2525881 : Blo 2243435 2525881 := bbase (se 2 (by rfl) ⟨947205, by rfl⟩ : syracuseStep 2525881 = 1894411) (by norm_num)
theorem B3367841 : Blo 2243435 3367841 := bstep (se 2 (by rfl) ⟨1262940, by rfl⟩ : syracuseStep 3367841 = 2525881) B2525881
theorem B2245227 : Blo 2243435 2245227 := bstep (se 1 (by rfl) ⟨1683920, by rfl⟩ : syracuseStep 2245227 = 3367841) B3367841
theorem B4795237 : Blo 2243435 4795237 := bbase (se 4 (by rfl) ⟨449553, by rfl⟩ : syracuseStep 4795237 = 899107) (by norm_num)
theorem B6393649 : Blo 2243435 6393649 := bstep (se 2 (by rfl) ⟨2397618, by rfl⟩ : syracuseStep 6393649 = 4795237) B4795237
theorem B8524865 : Blo 2243435 8524865 := bstep (se 2 (by rfl) ⟨3196824, by rfl⟩ : syracuseStep 8524865 = 6393649) B6393649
theorem B5683243 : Blo 2243435 5683243 := bstep (se 1 (by rfl) ⟨4262432, by rfl⟩ : syracuseStep 5683243 = 8524865) B8524865
theorem B7577657 : Blo 2243435 7577657 := bstep (se 2 (by rfl) ⟨2841621, by rfl⟩ : syracuseStep 7577657 = 5683243) B5683243
theorem B5051771 : Blo 2243435 5051771 := bstep (se 1 (by rfl) ⟨3788828, by rfl⟩ : syracuseStep 5051771 = 7577657) B7577657
theorem B3367847 : Blo 2243435 3367847 := bstep (se 1 (by rfl) ⟨2525885, by rfl⟩ : syracuseStep 3367847 = 5051771) B5051771
theorem B2245231 : Blo 2243435 2245231 := bstep (se 1 (by rfl) ⟨1683923, by rfl⟩ : syracuseStep 2245231 = 3367847) B3367847
theorem B3367853 : Blo 2243435 3367853 := bbase (se 3 (by rfl) ⟨631472, by rfl⟩ : syracuseStep 3367853 = 1262945) (by norm_num)
theorem B2245235 : Blo 2243435 2245235 := bstep (se 1 (by rfl) ⟨1683926, by rfl⟩ : syracuseStep 2245235 = 3367853) B3367853
theorem B5051789 : Blo 2243435 5051789 := bbase (se 3 (by rfl) ⟨947210, by rfl⟩ : syracuseStep 5051789 = 1894421) (by norm_num)
theorem B3367859 : Blo 2243435 3367859 := bstep (se 1 (by rfl) ⟨2525894, by rfl⟩ : syracuseStep 3367859 = 5051789) B5051789
theorem B2245239 : Blo 2243435 2245239 := bstep (se 1 (by rfl) ⟨1683929, by rfl⟩ : syracuseStep 2245239 = 3367859) B3367859
theorem B2841637 : Blo 2243435 2841637 := bbase (se 4 (by rfl) ⟨266403, by rfl⟩ : syracuseStep 2841637 = 532807) (by norm_num)
theorem B3788849 : Blo 2243435 3788849 := bstep (se 2 (by rfl) ⟨1420818, by rfl⟩ : syracuseStep 3788849 = 2841637) B2841637
theorem B2525899 : Blo 2243435 2525899 := bstep (se 1 (by rfl) ⟨1894424, by rfl⟩ : syracuseStep 2525899 = 3788849) B3788849
theorem B3367865 : Blo 2243435 3367865 := bstep (se 2 (by rfl) ⟨1262949, by rfl⟩ : syracuseStep 3367865 = 2525899) B2525899
theorem B2245243 : Blo 2243435 2245243 := bstep (se 1 (by rfl) ⟨1683932, by rfl⟩ : syracuseStep 2245243 = 3367865) B3367865
theorem B12814133 : Blo 2243435 12814133 := bbase (se 5 (by rfl) ⟨600662, by rfl⟩ : syracuseStep 12814133 = 1201325) (by norm_num)
theorem B34171021 : Blo 2243435 34171021 := bstep (se 3 (by rfl) ⟨6407066, by rfl⟩ : syracuseStep 34171021 = 12814133) B12814133
theorem B45561361 : Blo 2243435 45561361 := bstep (se 2 (by rfl) ⟨17085510, by rfl⟩ : syracuseStep 45561361 = 34171021) B34171021
theorem B60748481 : Blo 2243435 60748481 := bstep (se 2 (by rfl) ⟨22780680, by rfl⟩ : syracuseStep 60748481 = 45561361) B45561361
theorem B40498987 : Blo 2243435 40498987 := bstep (se 1 (by rfl) ⟨30374240, by rfl⟩ : syracuseStep 40498987 = 60748481) B60748481
theorem B53998649 : Blo 2243435 53998649 := bstep (se 2 (by rfl) ⟨20249493, by rfl⟩ : syracuseStep 53998649 = 40498987) B40498987
theorem B35999099 : Blo 2243435 35999099 := bstep (se 1 (by rfl) ⟨26999324, by rfl⟩ : syracuseStep 35999099 = 53998649) B53998649
theorem B23999399 : Blo 2243435 23999399 := bstep (se 1 (by rfl) ⟨17999549, by rfl⟩ : syracuseStep 23999399 = 35999099) B35999099
theorem B15999599 : Blo 2243435 15999599 := bstep (se 1 (by rfl) ⟨11999699, by rfl⟩ : syracuseStep 15999599 = 23999399) B23999399
theorem B10666399 : Blo 2243435 10666399 := bstep (se 1 (by rfl) ⟨7999799, by rfl⟩ : syracuseStep 10666399 = 15999599) B15999599
theorem B14221865 : Blo 2243435 14221865 := bstep (se 2 (by rfl) ⟨5333199, by rfl⟩ : syracuseStep 14221865 = 10666399) B10666399
theorem B37924973 : Blo 2243435 37924973 := bstep (se 3 (by rfl) ⟨7110932, by rfl⟩ : syracuseStep 37924973 = 14221865) B14221865
theorem B25283315 : Blo 2243435 25283315 := bstep (se 1 (by rfl) ⟨18962486, by rfl⟩ : syracuseStep 25283315 = 37924973) B37924973
theorem B16855543 : Blo 2243435 16855543 := bstep (se 1 (by rfl) ⟨12641657, by rfl⟩ : syracuseStep 16855543 = 25283315) B25283315
theorem B22474057 : Blo 2243435 22474057 := bstep (se 2 (by rfl) ⟨8427771, by rfl⟩ : syracuseStep 22474057 = 16855543) B16855543
theorem B29965409 : Blo 2243435 29965409 := bstep (se 2 (by rfl) ⟨11237028, by rfl⟩ : syracuseStep 29965409 = 22474057) B22474057
theorem B19976939 : Blo 2243435 19976939 := bstep (se 1 (by rfl) ⟨14982704, by rfl⟩ : syracuseStep 19976939 = 29965409) B29965409
theorem B13317959 : Blo 2243435 13317959 := bstep (se 1 (by rfl) ⟨9988469, by rfl⟩ : syracuseStep 13317959 = 19976939) B19976939
theorem B35514557 : Blo 2243435 35514557 := bstep (se 3 (by rfl) ⟨6658979, by rfl⟩ : syracuseStep 35514557 = 13317959) B13317959
theorem B23676371 : Blo 2243435 23676371 := bstep (se 1 (by rfl) ⟨17757278, by rfl⟩ : syracuseStep 23676371 = 35514557) B35514557
theorem B15784247 : Blo 2243435 15784247 := bstep (se 1 (by rfl) ⟨11838185, by rfl⟩ : syracuseStep 15784247 = 23676371) B23676371
theorem B10522831 : Blo 2243435 10522831 := bstep (se 1 (by rfl) ⟨7892123, by rfl⟩ : syracuseStep 10522831 = 15784247) B15784247
theorem B14030441 : Blo 2243435 14030441 := bstep (se 2 (by rfl) ⟨5261415, by rfl⟩ : syracuseStep 14030441 = 10522831) B10522831
theorem B9353627 : Blo 2243435 9353627 := bstep (se 1 (by rfl) ⟨7015220, by rfl⟩ : syracuseStep 9353627 = 14030441) B14030441
theorem B6235751 : Blo 2243435 6235751 := bstep (se 1 (by rfl) ⟨4676813, by rfl⟩ : syracuseStep 6235751 = 9353627) B9353627
theorem B4157167 : Blo 2243435 4157167 := bstep (se 1 (by rfl) ⟨3117875, by rfl⟩ : syracuseStep 4157167 = 6235751) B6235751
theorem B5542889 : Blo 2243435 5542889 := bstep (se 2 (by rfl) ⟨2078583, by rfl⟩ : syracuseStep 5542889 = 4157167) B4157167
theorem B14781037 : Blo 2243435 14781037 := bstep (se 3 (by rfl) ⟨2771444, by rfl⟩ : syracuseStep 14781037 = 5542889) B5542889
theorem B19708049 : Blo 2243435 19708049 := bstep (se 2 (by rfl) ⟨7390518, by rfl⟩ : syracuseStep 19708049 = 14781037) B14781037
theorem B13138699 : Blo 2243435 13138699 := bstep (se 1 (by rfl) ⟨9854024, by rfl⟩ : syracuseStep 13138699 = 19708049) B19708049
theorem B17518265 : Blo 2243435 17518265 := bstep (se 2 (by rfl) ⟨6569349, by rfl⟩ : syracuseStep 17518265 = 13138699) B13138699
theorem B11678843 : Blo 2243435 11678843 := bstep (se 1 (by rfl) ⟨8759132, by rfl⟩ : syracuseStep 11678843 = 17518265) B17518265
theorem B7785895 : Blo 2243435 7785895 := bstep (se 1 (by rfl) ⟨5839421, by rfl⟩ : syracuseStep 7785895 = 11678843) B11678843
theorem B10381193 : Blo 2243435 10381193 := bstep (se 2 (by rfl) ⟨3892947, by rfl⟩ : syracuseStep 10381193 = 7785895) B7785895
theorem B6920795 : Blo 2243435 6920795 := bstep (se 1 (by rfl) ⟨5190596, by rfl⟩ : syracuseStep 6920795 = 10381193) B10381193
theorem B4613863 : Blo 2243435 4613863 := bstep (se 1 (by rfl) ⟨3460397, by rfl⟩ : syracuseStep 4613863 = 6920795) B6920795
theorem B6151817 : Blo 2243435 6151817 := bstep (se 2 (by rfl) ⟨2306931, by rfl⟩ : syracuseStep 6151817 = 4613863) B4613863
theorem B4101211 : Blo 2243435 4101211 := bstep (se 1 (by rfl) ⟨3075908, by rfl⟩ : syracuseStep 4101211 = 6151817) B6151817
theorem B21873125 : Blo 2243435 21873125 := bstep (se 4 (by rfl) ⟨2050605, by rfl⟩ : syracuseStep 21873125 = 4101211) B4101211
theorem B58328333 : Blo 2243435 58328333 := bstep (se 3 (by rfl) ⟨10936562, by rfl⟩ : syracuseStep 58328333 = 21873125) B21873125
theorem B38885555 : Blo 2243435 38885555 := bstep (se 1 (by rfl) ⟨29164166, by rfl⟩ : syracuseStep 38885555 = 58328333) B58328333
theorem B103694813 : Blo 2243435 103694813 := bstep (se 3 (by rfl) ⟨19442777, by rfl⟩ : syracuseStep 103694813 = 38885555) B38885555
theorem B69129875 : Blo 2243435 69129875 := bstep (se 1 (by rfl) ⟨51847406, by rfl⟩ : syracuseStep 69129875 = 103694813) B103694813
theorem B46086583 : Blo 2243435 46086583 := bstep (se 1 (by rfl) ⟨34564937, by rfl⟩ : syracuseStep 46086583 = 69129875) B69129875
theorem B61448777 : Blo 2243435 61448777 := bstep (se 2 (by rfl) ⟨23043291, by rfl⟩ : syracuseStep 61448777 = 46086583) B46086583
theorem B40965851 : Blo 2243435 40965851 := bstep (se 1 (by rfl) ⟨30724388, by rfl⟩ : syracuseStep 40965851 = 61448777) B61448777
theorem B109242269 : Blo 2243435 109242269 := bstep (se 3 (by rfl) ⟨20482925, by rfl⟩ : syracuseStep 109242269 = 40965851) B40965851
theorem B72828179 : Blo 2243435 72828179 := bstep (se 1 (by rfl) ⟨54621134, by rfl⟩ : syracuseStep 72828179 = 109242269) B109242269
theorem B48552119 : Blo 2243435 48552119 := bstep (se 1 (by rfl) ⟨36414089, by rfl⟩ : syracuseStep 48552119 = 72828179) B72828179
theorem B32368079 : Blo 2243435 32368079 := bstep (se 1 (by rfl) ⟨24276059, by rfl⟩ : syracuseStep 32368079 = 48552119) B48552119
theorem B21578719 : Blo 2243435 21578719 := bstep (se 1 (by rfl) ⟨16184039, by rfl⟩ : syracuseStep 21578719 = 32368079) B32368079
theorem B28771625 : Blo 2243435 28771625 := bstep (se 2 (by rfl) ⟨10789359, by rfl⟩ : syracuseStep 28771625 = 21578719) B21578719
theorem B19181083 : Blo 2243435 19181083 := bstep (se 1 (by rfl) ⟨14385812, by rfl⟩ : syracuseStep 19181083 = 28771625) B28771625
theorem B25574777 : Blo 2243435 25574777 := bstep (se 2 (by rfl) ⟨9590541, by rfl⟩ : syracuseStep 25574777 = 19181083) B19181083
theorem B17049851 : Blo 2243435 17049851 := bstep (se 1 (by rfl) ⟨12787388, by rfl⟩ : syracuseStep 17049851 = 25574777) B25574777
theorem B11366567 : Blo 2243435 11366567 := bstep (se 1 (by rfl) ⟨8524925, by rfl⟩ : syracuseStep 11366567 = 17049851) B17049851
theorem B7577711 : Blo 2243435 7577711 := bstep (se 1 (by rfl) ⟨5683283, by rfl⟩ : syracuseStep 7577711 = 11366567) B11366567
theorem B5051807 : Blo 2243435 5051807 := bstep (se 1 (by rfl) ⟨3788855, by rfl⟩ : syracuseStep 5051807 = 7577711) B7577711
theorem B3367871 : Blo 2243435 3367871 := bstep (se 1 (by rfl) ⟨2525903, by rfl⟩ : syracuseStep 3367871 = 5051807) B5051807
theorem B2245247 : Blo 2243435 2245247 := bstep (se 1 (by rfl) ⟨1683935, by rfl⟩ : syracuseStep 2245247 = 3367871) B3367871
theorem B3367877 : Blo 2243435 3367877 := bbase (se 4 (by rfl) ⟨315738, by rfl⟩ : syracuseStep 3367877 = 631477) (by norm_num)
theorem B2245251 : Blo 2243435 2245251 := bstep (se 1 (by rfl) ⟨1683938, by rfl⟩ : syracuseStep 2245251 = 3367877) B3367877
theorem B3788869 : Blo 2243435 3788869 := bbase (se 4 (by rfl) ⟨355206, by rfl⟩ : syracuseStep 3788869 = 710413) (by norm_num)
theorem B5051825 : Blo 2243435 5051825 := bstep (se 2 (by rfl) ⟨1894434, by rfl⟩ : syracuseStep 5051825 = 3788869) B3788869
theorem B3367883 : Blo 2243435 3367883 := bstep (se 1 (by rfl) ⟨2525912, by rfl⟩ : syracuseStep 3367883 = 5051825) B5051825
theorem B2245255 : Blo 2243435 2245255 := bstep (se 1 (by rfl) ⟨1683941, by rfl⟩ : syracuseStep 2245255 = 3367883) B3367883
theorem B2525917 : Blo 2243435 2525917 := bbase (se 3 (by rfl) ⟨473609, by rfl⟩ : syracuseStep 2525917 = 947219) (by norm_num)
theorem B3367889 : Blo 2243435 3367889 := bstep (se 2 (by rfl) ⟨1262958, by rfl⟩ : syracuseStep 3367889 = 2525917) B2525917
theorem B2245259 : Blo 2243435 2245259 := bstep (se 1 (by rfl) ⟨1683944, by rfl⟩ : syracuseStep 2245259 = 3367889) B3367889
theorem B7577765 : Blo 2243435 7577765 := bbase (se 4 (by rfl) ⟨710415, by rfl⟩ : syracuseStep 7577765 = 1420831) (by norm_num)
theorem B5051843 : Blo 2243435 5051843 := bstep (se 1 (by rfl) ⟨3788882, by rfl⟩ : syracuseStep 5051843 = 7577765) B7577765
theorem B3367895 : Blo 2243435 3367895 := bstep (se 1 (by rfl) ⟨2525921, by rfl⟩ : syracuseStep 3367895 = 5051843) B5051843
theorem B2245263 : Blo 2243435 2245263 := bstep (se 1 (by rfl) ⟨1683947, by rfl⟩ : syracuseStep 2245263 = 3367895) B3367895
theorem B3367901 : Blo 2243435 3367901 := bbase (se 3 (by rfl) ⟨631481, by rfl⟩ : syracuseStep 3367901 = 1262963) (by norm_num)
theorem B2245267 : Blo 2243435 2245267 := bstep (se 1 (by rfl) ⟨1683950, by rfl⟩ : syracuseStep 2245267 = 3367901) B3367901
theorem B5051861 : Blo 2243435 5051861 := bbase (se 7 (by rfl) ⟨59201, by rfl⟩ : syracuseStep 5051861 = 118403) (by norm_num)
theorem B3367907 : Blo 2243435 3367907 := bstep (se 1 (by rfl) ⟨2525930, by rfl⟩ : syracuseStep 3367907 = 5051861) B5051861
theorem B2245271 : Blo 2243435 2245271 := bstep (se 1 (by rfl) ⟨1683953, by rfl⟩ : syracuseStep 2245271 = 3367907) B3367907
theorem B16184245 : Blo 2243435 16184245 := bbase (se 5 (by rfl) ⟨758636, by rfl⟩ : syracuseStep 16184245 = 1517273) (by norm_num)
theorem B21578993 : Blo 2243435 21578993 := bstep (se 2 (by rfl) ⟨8092122, by rfl⟩ : syracuseStep 21578993 = 16184245) B16184245
theorem B14385995 : Blo 2243435 14385995 := bstep (se 1 (by rfl) ⟨10789496, by rfl⟩ : syracuseStep 14385995 = 21578993) B21578993
theorem B9590663 : Blo 2243435 9590663 := bstep (se 1 (by rfl) ⟨7192997, by rfl⟩ : syracuseStep 9590663 = 14385995) B14385995
theorem B6393775 : Blo 2243435 6393775 := bstep (se 1 (by rfl) ⟨4795331, by rfl⟩ : syracuseStep 6393775 = 9590663) B9590663
theorem B8525033 : Blo 2243435 8525033 := bstep (se 2 (by rfl) ⟨3196887, by rfl⟩ : syracuseStep 8525033 = 6393775) B6393775
theorem B5683355 : Blo 2243435 5683355 := bstep (se 1 (by rfl) ⟨4262516, by rfl⟩ : syracuseStep 5683355 = 8525033) B8525033
theorem B3788903 : Blo 2243435 3788903 := bstep (se 1 (by rfl) ⟨2841677, by rfl⟩ : syracuseStep 3788903 = 5683355) B5683355
theorem B2525935 : Blo 2243435 2525935 := bstep (se 1 (by rfl) ⟨1894451, by rfl⟩ : syracuseStep 2525935 = 3788903) B3788903
theorem B3367913 : Blo 2243435 3367913 := bstep (se 2 (by rfl) ⟨1262967, by rfl⟩ : syracuseStep 3367913 = 2525935) B2525935
theorem B2245275 : Blo 2243435 2245275 := bstep (se 1 (by rfl) ⟨1683956, by rfl⟩ : syracuseStep 2245275 = 3367913) B3367913
theorem B5394757 : Blo 2243435 5394757 := bbase (se 4 (by rfl) ⟨505758, by rfl⟩ : syracuseStep 5394757 = 1011517) (by norm_num)
theorem B7193009 : Blo 2243435 7193009 := bstep (se 2 (by rfl) ⟨2697378, by rfl⟩ : syracuseStep 7193009 = 5394757) B5394757
theorem B19181357 : Blo 2243435 19181357 := bstep (se 3 (by rfl) ⟨3596504, by rfl⟩ : syracuseStep 19181357 = 7193009) B7193009
theorem B12787571 : Blo 2243435 12787571 := bstep (se 1 (by rfl) ⟨9590678, by rfl⟩ : syracuseStep 12787571 = 19181357) B19181357
theorem B8525047 : Blo 2243435 8525047 := bstep (se 1 (by rfl) ⟨6393785, by rfl⟩ : syracuseStep 8525047 = 12787571) B12787571
theorem B11366729 : Blo 2243435 11366729 := bstep (se 2 (by rfl) ⟨4262523, by rfl⟩ : syracuseStep 11366729 = 8525047) B8525047
theorem B7577819 : Blo 2243435 7577819 := bstep (se 1 (by rfl) ⟨5683364, by rfl⟩ : syracuseStep 7577819 = 11366729) B11366729
theorem B5051879 : Blo 2243435 5051879 := bstep (se 1 (by rfl) ⟨3788909, by rfl⟩ : syracuseStep 5051879 = 7577819) B7577819
theorem B3367919 : Blo 2243435 3367919 := bstep (se 1 (by rfl) ⟨2525939, by rfl⟩ : syracuseStep 3367919 = 5051879) B5051879
theorem B2245279 : Blo 2243435 2245279 := bstep (se 1 (by rfl) ⟨1683959, by rfl⟩ : syracuseStep 2245279 = 3367919) B3367919
theorem B3367925 : Blo 2243435 3367925 := bbase (se 5 (by rfl) ⟨157871, by rfl⟩ : syracuseStep 3367925 = 315743) (by norm_num)
theorem B2245283 : Blo 2243435 2245283 := bstep (se 1 (by rfl) ⟨1683962, by rfl⟩ : syracuseStep 2245283 = 3367925) B3367925
theorem B4795357 : Blo 2243435 4795357 := bbase (se 3 (by rfl) ⟨899129, by rfl⟩ : syracuseStep 4795357 = 1798259) (by norm_num)
theorem B6393809 : Blo 2243435 6393809 := bstep (se 2 (by rfl) ⟨2397678, by rfl⟩ : syracuseStep 6393809 = 4795357) B4795357
theorem B4262539 : Blo 2243435 4262539 := bstep (se 1 (by rfl) ⟨3196904, by rfl⟩ : syracuseStep 4262539 = 6393809) B6393809
theorem B5683385 : Blo 2243435 5683385 := bstep (se 2 (by rfl) ⟨2131269, by rfl⟩ : syracuseStep 5683385 = 4262539) B4262539
theorem B3788923 : Blo 2243435 3788923 := bstep (se 1 (by rfl) ⟨2841692, by rfl⟩ : syracuseStep 3788923 = 5683385) B5683385
theorem B5051897 : Blo 2243435 5051897 := bstep (se 2 (by rfl) ⟨1894461, by rfl⟩ : syracuseStep 5051897 = 3788923) B3788923
theorem B3367931 : Blo 2243435 3367931 := bstep (se 1 (by rfl) ⟨2525948, by rfl⟩ : syracuseStep 3367931 = 5051897) B5051897
theorem B2245287 : Blo 2243435 2245287 := bstep (se 1 (by rfl) ⟨1683965, by rfl⟩ : syracuseStep 2245287 = 3367931) B3367931
theorem B2525953 : Blo 2243435 2525953 := bbase (se 2 (by rfl) ⟨947232, by rfl⟩ : syracuseStep 2525953 = 1894465) (by norm_num)
theorem B3367937 : Blo 2243435 3367937 := bstep (se 2 (by rfl) ⟨1262976, by rfl⟩ : syracuseStep 3367937 = 2525953) B2525953
theorem B2245291 : Blo 2243435 2245291 := bstep (se 1 (by rfl) ⟨1683968, by rfl⟩ : syracuseStep 2245291 = 3367937) B3367937
theorem B5683405 : Blo 2243435 5683405 := bbase (se 3 (by rfl) ⟨1065638, by rfl⟩ : syracuseStep 5683405 = 2131277) (by norm_num)
theorem B7577873 : Blo 2243435 7577873 := bstep (se 2 (by rfl) ⟨2841702, by rfl⟩ : syracuseStep 7577873 = 5683405) B5683405
theorem B5051915 : Blo 2243435 5051915 := bstep (se 1 (by rfl) ⟨3788936, by rfl⟩ : syracuseStep 5051915 = 7577873) B7577873
theorem B3367943 : Blo 2243435 3367943 := bstep (se 1 (by rfl) ⟨2525957, by rfl⟩ : syracuseStep 3367943 = 5051915) B5051915
theorem B2245295 : Blo 2243435 2245295 := bstep (se 1 (by rfl) ⟨1683971, by rfl⟩ : syracuseStep 2245295 = 3367943) B3367943
theorem B3367949 : Blo 2243435 3367949 := bbase (se 3 (by rfl) ⟨631490, by rfl⟩ : syracuseStep 3367949 = 1262981) (by norm_num)
theorem B2245299 : Blo 2243435 2245299 := bstep (se 1 (by rfl) ⟨1683974, by rfl⟩ : syracuseStep 2245299 = 3367949) B3367949
theorem B5051933 : Blo 2243435 5051933 := bbase (se 3 (by rfl) ⟨947237, by rfl⟩ : syracuseStep 5051933 = 1894475) (by norm_num)
theorem B3367955 : Blo 2243435 3367955 := bstep (se 1 (by rfl) ⟨2525966, by rfl⟩ : syracuseStep 3367955 = 5051933) B5051933
theorem B2245303 : Blo 2243435 2245303 := bstep (se 1 (by rfl) ⟨1683977, by rfl⟩ : syracuseStep 2245303 = 3367955) B3367955
theorem B3788957 : Blo 2243435 3788957 := bbase (se 3 (by rfl) ⟨710429, by rfl⟩ : syracuseStep 3788957 = 1420859) (by norm_num)
theorem B2525971 : Blo 2243435 2525971 := bstep (se 1 (by rfl) ⟨1894478, by rfl⟩ : syracuseStep 2525971 = 3788957) B3788957
theorem B3367961 : Blo 2243435 3367961 := bstep (se 2 (by rfl) ⟨1262985, by rfl⟩ : syracuseStep 3367961 = 2525971) B2525971
theorem B2245307 : Blo 2243435 2245307 := bstep (se 1 (by rfl) ⟨1683980, by rfl⟩ : syracuseStep 2245307 = 3367961) B3367961
theorem B3075997 : Blo 2243435 3075997 := bbase (se 3 (by rfl) ⟨576749, by rfl⟩ : syracuseStep 3075997 = 1153499) (by norm_num)
theorem B4101329 : Blo 2243435 4101329 := bstep (se 2 (by rfl) ⟨1537998, by rfl⟩ : syracuseStep 4101329 = 3075997) B3075997
theorem B2734219 : Blo 2243435 2734219 := bstep (se 1 (by rfl) ⟨2050664, by rfl⟩ : syracuseStep 2734219 = 4101329) B4101329
theorem B14582501 : Blo 2243435 14582501 := bstep (se 4 (by rfl) ⟨1367109, by rfl⟩ : syracuseStep 14582501 = 2734219) B2734219
theorem B9721667 : Blo 2243435 9721667 := bstep (se 1 (by rfl) ⟨7291250, by rfl⟩ : syracuseStep 9721667 = 14582501) B14582501
theorem B25924445 : Blo 2243435 25924445 := bstep (se 3 (by rfl) ⟨4860833, by rfl⟩ : syracuseStep 25924445 = 9721667) B9721667
theorem B17282963 : Blo 2243435 17282963 := bstep (se 1 (by rfl) ⟨12962222, by rfl⟩ : syracuseStep 17282963 = 25924445) B25924445
theorem B11521975 : Blo 2243435 11521975 := bstep (se 1 (by rfl) ⟨8641481, by rfl⟩ : syracuseStep 11521975 = 17282963) B17282963
theorem B15362633 : Blo 2243435 15362633 := bstep (se 2 (by rfl) ⟨5760987, by rfl⟩ : syracuseStep 15362633 = 11521975) B11521975
theorem B40967021 : Blo 2243435 40967021 := bstep (se 3 (by rfl) ⟨7681316, by rfl⟩ : syracuseStep 40967021 = 15362633) B15362633
theorem B27311347 : Blo 2243435 27311347 := bstep (se 1 (by rfl) ⟨20483510, by rfl⟩ : syracuseStep 27311347 = 40967021) B40967021
theorem B36415129 : Blo 2243435 36415129 := bstep (se 2 (by rfl) ⟨13655673, by rfl⟩ : syracuseStep 36415129 = 27311347) B27311347
theorem B48553505 : Blo 2243435 48553505 := bstep (se 2 (by rfl) ⟨18207564, by rfl⟩ : syracuseStep 48553505 = 36415129) B36415129
theorem B32369003 : Blo 2243435 32369003 := bstep (se 1 (by rfl) ⟨24276752, by rfl⟩ : syracuseStep 32369003 = 48553505) B48553505
theorem B21579335 : Blo 2243435 21579335 := bstep (se 1 (by rfl) ⟨16184501, by rfl⟩ : syracuseStep 21579335 = 32369003) B32369003
theorem B14386223 : Blo 2243435 14386223 := bstep (se 1 (by rfl) ⟨10789667, by rfl⟩ : syracuseStep 14386223 = 21579335) B21579335
theorem B9590815 : Blo 2243435 9590815 := bstep (se 1 (by rfl) ⟨7193111, by rfl⟩ : syracuseStep 9590815 = 14386223) B14386223
theorem B12787753 : Blo 2243435 12787753 := bstep (se 2 (by rfl) ⟨4795407, by rfl⟩ : syracuseStep 12787753 = 9590815) B9590815
theorem B17050337 : Blo 2243435 17050337 := bstep (se 2 (by rfl) ⟨6393876, by rfl⟩ : syracuseStep 17050337 = 12787753) B12787753
theorem B11366891 : Blo 2243435 11366891 := bstep (se 1 (by rfl) ⟨8525168, by rfl⟩ : syracuseStep 11366891 = 17050337) B17050337
theorem B7577927 : Blo 2243435 7577927 := bstep (se 1 (by rfl) ⟨5683445, by rfl⟩ : syracuseStep 7577927 = 11366891) B11366891
theorem B5051951 : Blo 2243435 5051951 := bstep (se 1 (by rfl) ⟨3788963, by rfl⟩ : syracuseStep 5051951 = 7577927) B7577927
theorem B3367967 : Blo 2243435 3367967 := bstep (se 1 (by rfl) ⟨2525975, by rfl⟩ : syracuseStep 3367967 = 5051951) B5051951
theorem B2245311 : Blo 2243435 2245311 := bstep (se 1 (by rfl) ⟨1683983, by rfl⟩ : syracuseStep 2245311 = 3367967) B3367967
theorem B3367973 : Blo 2243435 3367973 := bbase (se 4 (by rfl) ⟨315747, by rfl⟩ : syracuseStep 3367973 = 631495) (by norm_num)
theorem B2245315 : Blo 2243435 2245315 := bstep (se 1 (by rfl) ⟨1683986, by rfl⟩ : syracuseStep 2245315 = 3367973) B3367973
theorem B2841733 : Blo 2243435 2841733 := bbase (se 4 (by rfl) ⟨266412, by rfl⟩ : syracuseStep 2841733 = 532825) (by norm_num)
theorem B3788977 : Blo 2243435 3788977 := bstep (se 2 (by rfl) ⟨1420866, by rfl⟩ : syracuseStep 3788977 = 2841733) B2841733
theorem B5051969 : Blo 2243435 5051969 := bstep (se 2 (by rfl) ⟨1894488, by rfl⟩ : syracuseStep 5051969 = 3788977) B3788977
theorem B3367979 : Blo 2243435 3367979 := bstep (se 1 (by rfl) ⟨2525984, by rfl⟩ : syracuseStep 3367979 = 5051969) B5051969
theorem B2245319 : Blo 2243435 2245319 := bstep (se 1 (by rfl) ⟨1683989, by rfl⟩ : syracuseStep 2245319 = 3367979) B3367979
theorem B2525989 : Blo 2243435 2525989 := bbase (se 4 (by rfl) ⟨236811, by rfl⟩ : syracuseStep 2525989 = 473623) (by norm_num)
theorem B3367985 : Blo 2243435 3367985 := bstep (se 2 (by rfl) ⟨1262994, by rfl⟩ : syracuseStep 3367985 = 2525989) B2525989
theorem B2245323 : Blo 2243435 2245323 := bstep (se 1 (by rfl) ⟨1683992, by rfl⟩ : syracuseStep 2245323 = 3367985) B3367985
theorem B9590885 : Blo 2243435 9590885 := bbase (se 4 (by rfl) ⟨899145, by rfl⟩ : syracuseStep 9590885 = 1798291) (by norm_num)
theorem B6393923 : Blo 2243435 6393923 := bstep (se 1 (by rfl) ⟨4795442, by rfl⟩ : syracuseStep 6393923 = 9590885) B9590885
theorem B4262615 : Blo 2243435 4262615 := bstep (se 1 (by rfl) ⟨3196961, by rfl⟩ : syracuseStep 4262615 = 6393923) B6393923
theorem B2841743 : Blo 2243435 2841743 := bstep (se 1 (by rfl) ⟨2131307, by rfl⟩ : syracuseStep 2841743 = 4262615) B4262615
theorem B7577981 : Blo 2243435 7577981 := bstep (se 3 (by rfl) ⟨1420871, by rfl⟩ : syracuseStep 7577981 = 2841743) B2841743
theorem B5051987 : Blo 2243435 5051987 := bstep (se 1 (by rfl) ⟨3788990, by rfl⟩ : syracuseStep 5051987 = 7577981) B7577981
theorem B3367991 : Blo 2243435 3367991 := bstep (se 1 (by rfl) ⟨2525993, by rfl⟩ : syracuseStep 3367991 = 5051987) B5051987
theorem B2245327 : Blo 2243435 2245327 := bstep (se 1 (by rfl) ⟨1683995, by rfl⟩ : syracuseStep 2245327 = 3367991) B3367991
theorem B3367997 : Blo 2243435 3367997 := bbase (se 3 (by rfl) ⟨631499, by rfl⟩ : syracuseStep 3367997 = 1262999) (by norm_num)
theorem B2245331 : Blo 2243435 2245331 := bstep (se 1 (by rfl) ⟨1683998, by rfl⟩ : syracuseStep 2245331 = 3367997) B3367997
theorem B5052005 : Blo 2243435 5052005 := bbase (se 4 (by rfl) ⟨473625, by rfl⟩ : syracuseStep 5052005 = 947251) (by norm_num)
theorem B3368003 : Blo 2243435 3368003 := bstep (se 1 (by rfl) ⟨2526002, by rfl⟩ : syracuseStep 3368003 = 5052005) B5052005
theorem B2245335 : Blo 2243435 2245335 := bstep (se 1 (by rfl) ⟨1684001, by rfl⟩ : syracuseStep 2245335 = 3368003) B3368003
theorem B5683517 : Blo 2243435 5683517 := bbase (se 3 (by rfl) ⟨1065659, by rfl⟩ : syracuseStep 5683517 = 2131319) (by norm_num)
theorem B3789011 : Blo 2243435 3789011 := bstep (se 1 (by rfl) ⟨2841758, by rfl⟩ : syracuseStep 3789011 = 5683517) B5683517
theorem B2526007 : Blo 2243435 2526007 := bstep (se 1 (by rfl) ⟨1894505, by rfl⟩ : syracuseStep 2526007 = 3789011) B3789011
theorem B3368009 : Blo 2243435 3368009 := bstep (se 2 (by rfl) ⟨1263003, by rfl⟩ : syracuseStep 3368009 = 2526007) B2526007
theorem B2245339 : Blo 2243435 2245339 := bstep (se 1 (by rfl) ⟨1684004, by rfl⟩ : syracuseStep 2245339 = 3368009) B3368009
theorem B4262645 : Blo 2243435 4262645 := bbase (se 5 (by rfl) ⟨199811, by rfl⟩ : syracuseStep 4262645 = 399623) (by norm_num)
theorem B11367053 : Blo 2243435 11367053 := bstep (se 3 (by rfl) ⟨2131322, by rfl⟩ : syracuseStep 11367053 = 4262645) B4262645
theorem B7578035 : Blo 2243435 7578035 := bstep (se 1 (by rfl) ⟨5683526, by rfl⟩ : syracuseStep 7578035 = 11367053) B11367053
theorem B5052023 : Blo 2243435 5052023 := bstep (se 1 (by rfl) ⟨3789017, by rfl⟩ : syracuseStep 5052023 = 7578035) B7578035
theorem B3368015 : Blo 2243435 3368015 := bstep (se 1 (by rfl) ⟨2526011, by rfl⟩ : syracuseStep 3368015 = 5052023) B5052023
theorem B2245343 : Blo 2243435 2245343 := bstep (se 1 (by rfl) ⟨1684007, by rfl⟩ : syracuseStep 2245343 = 3368015) B3368015
theorem B3368021 : Blo 2243435 3368021 := bbase (se 8 (by rfl) ⟨19734, by rfl⟩ : syracuseStep 3368021 = 39469) (by norm_num)
theorem B2245347 : Blo 2243435 2245347 := bstep (se 1 (by rfl) ⟨1684010, by rfl⟩ : syracuseStep 2245347 = 3368021) B3368021
theorem B10789861 : Blo 2243435 10789861 := bbase (se 4 (by rfl) ⟨1011549, by rfl⟩ : syracuseStep 10789861 = 2023099) (by norm_num)
theorem B14386481 : Blo 2243435 14386481 := bstep (se 2 (by rfl) ⟨5394930, by rfl⟩ : syracuseStep 14386481 = 10789861) B10789861
theorem B9590987 : Blo 2243435 9590987 := bstep (se 1 (by rfl) ⟨7193240, by rfl⟩ : syracuseStep 9590987 = 14386481) B14386481
theorem B6393991 : Blo 2243435 6393991 := bstep (se 1 (by rfl) ⟨4795493, by rfl⟩ : syracuseStep 6393991 = 9590987) B9590987
theorem B8525321 : Blo 2243435 8525321 := bstep (se 2 (by rfl) ⟨3196995, by rfl⟩ : syracuseStep 8525321 = 6393991) B6393991
theorem B5683547 : Blo 2243435 5683547 := bstep (se 1 (by rfl) ⟨4262660, by rfl⟩ : syracuseStep 5683547 = 8525321) B8525321
theorem B3789031 : Blo 2243435 3789031 := bstep (se 1 (by rfl) ⟨2841773, by rfl⟩ : syracuseStep 3789031 = 5683547) B5683547
theorem B5052041 : Blo 2243435 5052041 := bstep (se 2 (by rfl) ⟨1894515, by rfl⟩ : syracuseStep 5052041 = 3789031) B3789031
theorem B3368027 : Blo 2243435 3368027 := bstep (se 1 (by rfl) ⟨2526020, by rfl⟩ : syracuseStep 3368027 = 5052041) B5052041
theorem B2245351 : Blo 2243435 2245351 := bstep (se 1 (by rfl) ⟨1684013, by rfl⟩ : syracuseStep 2245351 = 3368027) B3368027
theorem B2526025 : Blo 2243435 2526025 := bbase (se 2 (by rfl) ⟨947259, by rfl⟩ : syracuseStep 2526025 = 1894519) (by norm_num)
theorem B3368033 : Blo 2243435 3368033 := bstep (se 2 (by rfl) ⟨1263012, by rfl⟩ : syracuseStep 3368033 = 2526025) B2526025
theorem B2245355 : Blo 2243435 2245355 := bstep (se 1 (by rfl) ⟨1684016, by rfl⟩ : syracuseStep 2245355 = 3368033) B3368033
theorem B21579797 : Blo 2243435 21579797 := bbase (se 6 (by rfl) ⟨505776, by rfl⟩ : syracuseStep 21579797 = 1011553) (by norm_num)
theorem B14386531 : Blo 2243435 14386531 := bstep (se 1 (by rfl) ⟨10789898, by rfl⟩ : syracuseStep 14386531 = 21579797) B21579797
theorem B19182041 : Blo 2243435 19182041 := bstep (se 2 (by rfl) ⟨7193265, by rfl⟩ : syracuseStep 19182041 = 14386531) B14386531
theorem B12788027 : Blo 2243435 12788027 := bstep (se 1 (by rfl) ⟨9591020, by rfl⟩ : syracuseStep 12788027 = 19182041) B19182041
theorem B8525351 : Blo 2243435 8525351 := bstep (se 1 (by rfl) ⟨6394013, by rfl⟩ : syracuseStep 8525351 = 12788027) B12788027
theorem B5683567 : Blo 2243435 5683567 := bstep (se 1 (by rfl) ⟨4262675, by rfl⟩ : syracuseStep 5683567 = 8525351) B8525351
theorem B7578089 : Blo 2243435 7578089 := bstep (se 2 (by rfl) ⟨2841783, by rfl⟩ : syracuseStep 7578089 = 5683567) B5683567
theorem B5052059 : Blo 2243435 5052059 := bstep (se 1 (by rfl) ⟨3789044, by rfl⟩ : syracuseStep 5052059 = 7578089) B7578089
theorem B3368039 : Blo 2243435 3368039 := bstep (se 1 (by rfl) ⟨2526029, by rfl⟩ : syracuseStep 3368039 = 5052059) B5052059
theorem B2245359 : Blo 2243435 2245359 := bstep (se 1 (by rfl) ⟨1684019, by rfl⟩ : syracuseStep 2245359 = 3368039) B3368039
theorem B3368045 : Blo 2243435 3368045 := bbase (se 3 (by rfl) ⟨631508, by rfl⟩ : syracuseStep 3368045 = 1263017) (by norm_num)
theorem B2245363 : Blo 2243435 2245363 := bstep (se 1 (by rfl) ⟨1684022, by rfl⟩ : syracuseStep 2245363 = 3368045) B3368045
theorem B5052077 : Blo 2243435 5052077 := bbase (se 3 (by rfl) ⟨947264, by rfl⟩ : syracuseStep 5052077 = 1894529) (by norm_num)
theorem B3368051 : Blo 2243435 3368051 := bstep (se 1 (by rfl) ⟨2526038, by rfl⟩ : syracuseStep 3368051 = 5052077) B5052077
theorem B2245367 : Blo 2243435 2245367 := bstep (se 1 (by rfl) ⟨1684025, by rfl⟩ : syracuseStep 2245367 = 3368051) B3368051
theorem B3596653 : Blo 2243435 3596653 := bbase (se 3 (by rfl) ⟨674372, by rfl⟩ : syracuseStep 3596653 = 1348745) (by norm_num)
theorem B4795537 : Blo 2243435 4795537 := bstep (se 2 (by rfl) ⟨1798326, by rfl⟩ : syracuseStep 4795537 = 3596653) B3596653
theorem B6394049 : Blo 2243435 6394049 := bstep (se 2 (by rfl) ⟨2397768, by rfl⟩ : syracuseStep 6394049 = 4795537) B4795537
theorem B4262699 : Blo 2243435 4262699 := bstep (se 1 (by rfl) ⟨3197024, by rfl⟩ : syracuseStep 4262699 = 6394049) B6394049
theorem B2841799 : Blo 2243435 2841799 := bstep (se 1 (by rfl) ⟨2131349, by rfl⟩ : syracuseStep 2841799 = 4262699) B4262699
theorem B3789065 : Blo 2243435 3789065 := bstep (se 2 (by rfl) ⟨1420899, by rfl⟩ : syracuseStep 3789065 = 2841799) B2841799
theorem B2526043 : Blo 2243435 2526043 := bstep (se 1 (by rfl) ⟨1894532, by rfl⟩ : syracuseStep 2526043 = 3789065) B3789065
theorem B3368057 : Blo 2243435 3368057 := bstep (se 2 (by rfl) ⟨1263021, by rfl⟩ : syracuseStep 3368057 = 2526043) B2526043
theorem B2245371 : Blo 2243435 2245371 := bstep (se 1 (by rfl) ⟨1684028, by rfl⟩ : syracuseStep 2245371 = 3368057) B3368057
theorem B4552021 : Blo 2243435 4552021 := bbase (se 13 (by rfl) ⟨833, by rfl⟩ : syracuseStep 4552021 = 1667) (by norm_num)
theorem B6069361 : Blo 2243435 6069361 := bstep (se 2 (by rfl) ⟨2276010, by rfl⟩ : syracuseStep 6069361 = 4552021) B4552021
theorem B8092481 : Blo 2243435 8092481 := bstep (se 2 (by rfl) ⟨3034680, by rfl⟩ : syracuseStep 8092481 = 6069361) B6069361
theorem B21579949 : Blo 2243435 21579949 := bstep (se 3 (by rfl) ⟨4046240, by rfl⟩ : syracuseStep 21579949 = 8092481) B8092481
theorem B28773265 : Blo 2243435 28773265 := bstep (se 2 (by rfl) ⟨10789974, by rfl⟩ : syracuseStep 28773265 = 21579949) B21579949
theorem B38364353 : Blo 2243435 38364353 := bstep (se 2 (by rfl) ⟨14386632, by rfl⟩ : syracuseStep 38364353 = 28773265) B28773265
theorem B25576235 : Blo 2243435 25576235 := bstep (se 1 (by rfl) ⟨19182176, by rfl⟩ : syracuseStep 25576235 = 38364353) B38364353
theorem B17050823 : Blo 2243435 17050823 := bstep (se 1 (by rfl) ⟨12788117, by rfl⟩ : syracuseStep 17050823 = 25576235) B25576235
theorem B11367215 : Blo 2243435 11367215 := bstep (se 1 (by rfl) ⟨8525411, by rfl⟩ : syracuseStep 11367215 = 17050823) B17050823
theorem B7578143 : Blo 2243435 7578143 := bstep (se 1 (by rfl) ⟨5683607, by rfl⟩ : syracuseStep 7578143 = 11367215) B11367215
theorem B5052095 : Blo 2243435 5052095 := bstep (se 1 (by rfl) ⟨3789071, by rfl⟩ : syracuseStep 5052095 = 7578143) B7578143
theorem B3368063 : Blo 2243435 3368063 := bstep (se 1 (by rfl) ⟨2526047, by rfl⟩ : syracuseStep 3368063 = 5052095) B5052095
theorem B2245375 : Blo 2243435 2245375 := bstep (se 1 (by rfl) ⟨1684031, by rfl⟩ : syracuseStep 2245375 = 3368063) B3368063
theorem B3368069 : Blo 2243435 3368069 := bbase (se 4 (by rfl) ⟨315756, by rfl⟩ : syracuseStep 3368069 = 631513) (by norm_num)
theorem B2245379 : Blo 2243435 2245379 := bstep (se 1 (by rfl) ⟨1684034, by rfl⟩ : syracuseStep 2245379 = 3368069) B3368069
theorem B3789085 : Blo 2243435 3789085 := bbase (se 3 (by rfl) ⟨710453, by rfl⟩ : syracuseStep 3789085 = 1420907) (by norm_num)
theorem B5052113 : Blo 2243435 5052113 := bstep (se 2 (by rfl) ⟨1894542, by rfl⟩ : syracuseStep 5052113 = 3789085) B3789085
theorem B3368075 : Blo 2243435 3368075 := bstep (se 1 (by rfl) ⟨2526056, by rfl⟩ : syracuseStep 3368075 = 5052113) B5052113
theorem B2245383 : Blo 2243435 2245383 := bstep (se 1 (by rfl) ⟨1684037, by rfl⟩ : syracuseStep 2245383 = 3368075) B3368075
theorem B2526061 : Blo 2243435 2526061 := bbase (se 3 (by rfl) ⟨473636, by rfl⟩ : syracuseStep 2526061 = 947273) (by norm_num)
theorem B3368081 : Blo 2243435 3368081 := bstep (se 2 (by rfl) ⟨1263030, by rfl⟩ : syracuseStep 3368081 = 2526061) B2526061
theorem B2245387 : Blo 2243435 2245387 := bstep (se 1 (by rfl) ⟨1684040, by rfl⟩ : syracuseStep 2245387 = 3368081) B3368081
theorem B7578197 : Blo 2243435 7578197 := bbase (se 8 (by rfl) ⟨44403, by rfl⟩ : syracuseStep 7578197 = 88807) (by norm_num)
theorem B5052131 : Blo 2243435 5052131 := bstep (se 1 (by rfl) ⟨3789098, by rfl⟩ : syracuseStep 5052131 = 7578197) B7578197
theorem B3368087 : Blo 2243435 3368087 := bstep (se 1 (by rfl) ⟨2526065, by rfl⟩ : syracuseStep 3368087 = 5052131) B5052131
theorem B2245391 : Blo 2243435 2245391 := bstep (se 1 (by rfl) ⟨1684043, by rfl⟩ : syracuseStep 2245391 = 3368087) B3368087
theorem B3368093 : Blo 2243435 3368093 := bbase (se 3 (by rfl) ⟨631517, by rfl⟩ : syracuseStep 3368093 = 1263035) (by norm_num)
theorem B2245395 : Blo 2243435 2245395 := bstep (se 1 (by rfl) ⟨1684046, by rfl⟩ : syracuseStep 2245395 = 3368093) B3368093
theorem B5052149 : Blo 2243435 5052149 := bbase (se 5 (by rfl) ⟨236819, by rfl⟩ : syracuseStep 5052149 = 473639) (by norm_num)
theorem B3368099 : Blo 2243435 3368099 := bstep (se 1 (by rfl) ⟨2526074, by rfl⟩ : syracuseStep 3368099 = 5052149) B5052149
theorem B2245399 : Blo 2243435 2245399 := bstep (se 1 (by rfl) ⟨1684049, by rfl⟩ : syracuseStep 2245399 = 3368099) B3368099
theorem B2430517 : Blo 2243435 2430517 := bbase (se 5 (by rfl) ⟨113930, by rfl⟩ : syracuseStep 2430517 = 227861) (by norm_num)
theorem B3240689 : Blo 2243435 3240689 := bstep (se 2 (by rfl) ⟨1215258, by rfl⟩ : syracuseStep 3240689 = 2430517) B2430517
theorem B8641837 : Blo 2243435 8641837 := bstep (se 3 (by rfl) ⟨1620344, by rfl⟩ : syracuseStep 8641837 = 3240689) B3240689
theorem B11522449 : Blo 2243435 11522449 := bstep (se 2 (by rfl) ⟨4320918, by rfl⟩ : syracuseStep 11522449 = 8641837) B8641837
theorem B15363265 : Blo 2243435 15363265 := bstep (se 2 (by rfl) ⟨5761224, by rfl⟩ : syracuseStep 15363265 = 11522449) B11522449
theorem B20484353 : Blo 2243435 20484353 := bstep (se 2 (by rfl) ⟨7681632, by rfl⟩ : syracuseStep 20484353 = 15363265) B15363265
theorem B54624941 : Blo 2243435 54624941 := bstep (se 3 (by rfl) ⟨10242176, by rfl⟩ : syracuseStep 54624941 = 20484353) B20484353
theorem B36416627 : Blo 2243435 36416627 := bstep (se 1 (by rfl) ⟨27312470, by rfl⟩ : syracuseStep 36416627 = 54624941) B54624941
theorem B24277751 : Blo 2243435 24277751 := bstep (se 1 (by rfl) ⟨18208313, by rfl⟩ : syracuseStep 24277751 = 36416627) B36416627
theorem B16185167 : Blo 2243435 16185167 := bstep (se 1 (by rfl) ⟨12138875, by rfl⟩ : syracuseStep 16185167 = 24277751) B24277751
theorem B10790111 : Blo 2243435 10790111 := bstep (se 1 (by rfl) ⟨8092583, by rfl⟩ : syracuseStep 10790111 = 16185167) B16185167
theorem B28773629 : Blo 2243435 28773629 := bstep (se 3 (by rfl) ⟨5395055, by rfl⟩ : syracuseStep 28773629 = 10790111) B10790111
theorem B19182419 : Blo 2243435 19182419 := bstep (se 1 (by rfl) ⟨14386814, by rfl⟩ : syracuseStep 19182419 = 28773629) B28773629
theorem B12788279 : Blo 2243435 12788279 := bstep (se 1 (by rfl) ⟨9591209, by rfl⟩ : syracuseStep 12788279 = 19182419) B19182419
theorem B8525519 : Blo 2243435 8525519 := bstep (se 1 (by rfl) ⟨6394139, by rfl⟩ : syracuseStep 8525519 = 12788279) B12788279
theorem B5683679 : Blo 2243435 5683679 := bstep (se 1 (by rfl) ⟨4262759, by rfl⟩ : syracuseStep 5683679 = 8525519) B8525519
theorem B3789119 : Blo 2243435 3789119 := bstep (se 1 (by rfl) ⟨2841839, by rfl⟩ : syracuseStep 3789119 = 5683679) B5683679
theorem B2526079 : Blo 2243435 2526079 := bstep (se 1 (by rfl) ⟨1894559, by rfl⟩ : syracuseStep 2526079 = 3789119) B3789119
theorem B3368105 : Blo 2243435 3368105 := bstep (se 2 (by rfl) ⟨1263039, by rfl⟩ : syracuseStep 3368105 = 2526079) B2526079
theorem B2245403 : Blo 2243435 2245403 := bstep (se 1 (by rfl) ⟨1684052, by rfl⟩ : syracuseStep 2245403 = 3368105) B3368105
theorem B4795613 : Blo 2243435 4795613 := bbase (se 3 (by rfl) ⟨899177, by rfl⟩ : syracuseStep 4795613 = 1798355) (by norm_num)
theorem B3197075 : Blo 2243435 3197075 := bstep (se 1 (by rfl) ⟨2397806, by rfl⟩ : syracuseStep 3197075 = 4795613) B4795613
theorem B8525533 : Blo 2243435 8525533 := bstep (se 3 (by rfl) ⟨1598537, by rfl⟩ : syracuseStep 8525533 = 3197075) B3197075
theorem B11367377 : Blo 2243435 11367377 := bstep (se 2 (by rfl) ⟨4262766, by rfl⟩ : syracuseStep 11367377 = 8525533) B8525533
theorem B7578251 : Blo 2243435 7578251 := bstep (se 1 (by rfl) ⟨5683688, by rfl⟩ : syracuseStep 7578251 = 11367377) B11367377
theorem B5052167 : Blo 2243435 5052167 := bstep (se 1 (by rfl) ⟨3789125, by rfl⟩ : syracuseStep 5052167 = 7578251) B7578251
theorem B3368111 : Blo 2243435 3368111 := bstep (se 1 (by rfl) ⟨2526083, by rfl⟩ : syracuseStep 3368111 = 5052167) B5052167
theorem B2245407 : Blo 2243435 2245407 := bstep (se 1 (by rfl) ⟨1684055, by rfl⟩ : syracuseStep 2245407 = 3368111) B3368111
theorem B3368117 : Blo 2243435 3368117 := bbase (se 5 (by rfl) ⟨157880, by rfl⟩ : syracuseStep 3368117 = 315761) (by norm_num)
theorem B2245411 : Blo 2243435 2245411 := bstep (se 1 (by rfl) ⟨1684058, by rfl⟩ : syracuseStep 2245411 = 3368117) B3368117
theorem B5683709 : Blo 2243435 5683709 := bbase (se 3 (by rfl) ⟨1065695, by rfl⟩ : syracuseStep 5683709 = 2131391) (by norm_num)
theorem B3789139 : Blo 2243435 3789139 := bstep (se 1 (by rfl) ⟨2841854, by rfl⟩ : syracuseStep 3789139 = 5683709) B5683709
theorem B5052185 : Blo 2243435 5052185 := bstep (se 2 (by rfl) ⟨1894569, by rfl⟩ : syracuseStep 5052185 = 3789139) B3789139
theorem B3368123 : Blo 2243435 3368123 := bstep (se 1 (by rfl) ⟨2526092, by rfl⟩ : syracuseStep 3368123 = 5052185) B5052185
theorem B2245415 : Blo 2243435 2245415 := bstep (se 1 (by rfl) ⟨1684061, by rfl⟩ : syracuseStep 2245415 = 3368123) B3368123
theorem B2526097 : Blo 2243435 2526097 := bbase (se 2 (by rfl) ⟨947286, by rfl⟩ : syracuseStep 2526097 = 1894573) (by norm_num)
theorem B3368129 : Blo 2243435 3368129 := bstep (se 2 (by rfl) ⟨1263048, by rfl⟩ : syracuseStep 3368129 = 2526097) B2526097
theorem B2245419 : Blo 2243435 2245419 := bstep (se 1 (by rfl) ⟨1684064, by rfl⟩ : syracuseStep 2245419 = 3368129) B3368129
theorem B4262797 : Blo 2243435 4262797 := bbase (se 3 (by rfl) ⟨799274, by rfl⟩ : syracuseStep 4262797 = 1598549) (by norm_num)
theorem B5683729 : Blo 2243435 5683729 := bstep (se 2 (by rfl) ⟨2131398, by rfl⟩ : syracuseStep 5683729 = 4262797) B4262797
theorem B7578305 : Blo 2243435 7578305 := bstep (se 2 (by rfl) ⟨2841864, by rfl⟩ : syracuseStep 7578305 = 5683729) B5683729
theorem B5052203 : Blo 2243435 5052203 := bstep (se 1 (by rfl) ⟨3789152, by rfl⟩ : syracuseStep 5052203 = 7578305) B7578305
theorem B3368135 : Blo 2243435 3368135 := bstep (se 1 (by rfl) ⟨2526101, by rfl⟩ : syracuseStep 3368135 = 5052203) B5052203
theorem B2245423 : Blo 2243435 2245423 := bstep (se 1 (by rfl) ⟨1684067, by rfl⟩ : syracuseStep 2245423 = 3368135) B3368135
theorem B3368141 : Blo 2243435 3368141 := bbase (se 3 (by rfl) ⟨631526, by rfl⟩ : syracuseStep 3368141 = 1263053) (by norm_num)
theorem B2245427 : Blo 2243435 2245427 := bstep (se 1 (by rfl) ⟨1684070, by rfl⟩ : syracuseStep 2245427 = 3368141) B3368141
theorem B5052221 : Blo 2243435 5052221 := bbase (se 3 (by rfl) ⟨947291, by rfl⟩ : syracuseStep 5052221 = 1894583) (by norm_num)
theorem B3368147 : Blo 2243435 3368147 := bstep (se 1 (by rfl) ⟨2526110, by rfl⟩ : syracuseStep 3368147 = 5052221) B5052221
theorem B2245431 : Blo 2243435 2245431 := bstep (se 1 (by rfl) ⟨1684073, by rfl⟩ : syracuseStep 2245431 = 3368147) B3368147
theorem B3789173 : Blo 2243435 3789173 := bbase (se 5 (by rfl) ⟨177617, by rfl⟩ : syracuseStep 3789173 = 355235) (by norm_num)
theorem B2526115 : Blo 2243435 2526115 := bstep (se 1 (by rfl) ⟨1894586, by rfl⟩ : syracuseStep 2526115 = 3789173) B3789173
theorem B3368153 : Blo 2243435 3368153 := bstep (se 2 (by rfl) ⟨1263057, by rfl⟩ : syracuseStep 3368153 = 2526115) B2526115
theorem B2245435 : Blo 2243435 2245435 := bstep (se 1 (by rfl) ⟨1684076, by rfl⟩ : syracuseStep 2245435 = 3368153) B3368153
theorem C0 (j : ℕ) (h1 : 560858 ≤ j) (h2 : j ≤ 561358) : Blo 2243435 (4 * j + 3) := by
  interval_cases j
  · exact B2243435
  · exact B2243439
  · exact B2243443
  · exact B2243447
  · exact B2243451
  · exact B2243455
  · exact B2243459
  · exact B2243463
  · exact B2243467
  · exact B2243471
  · exact B2243475
  · exact B2243479
  · exact B2243483
  · exact B2243487
  · exact B2243491
  · exact B2243495
  · exact B2243499
  · exact B2243503
  · exact B2243507
  · exact B2243511
  · exact B2243515
  · exact B2243519
  · exact B2243523
  · exact B2243527
  · exact B2243531
  · exact B2243535
  · exact B2243539
  · exact B2243543
  · exact B2243547
  · exact B2243551
  · exact B2243555
  · exact B2243559
  · exact B2243563
  · exact B2243567
  · exact B2243571
  · exact B2243575
  · exact B2243579
  · exact B2243583
  · exact B2243587
  · exact B2243591
  · exact B2243595
  · exact B2243599
  · exact B2243603
  · exact B2243607
  · exact B2243611
  · exact B2243615
  · exact B2243619
  · exact B2243623
  · exact B2243627
  · exact B2243631
  · exact B2243635
  · exact B2243639
  · exact B2243643
  · exact B2243647
  · exact B2243651
  · exact B2243655
  · exact B2243659
  · exact B2243663
  · exact B2243667
  · exact B2243671
  · exact B2243675
  · exact B2243679
  · exact B2243683
  · exact B2243687
  · exact B2243691
  · exact B2243695
  · exact B2243699
  · exact B2243703
  · exact B2243707
  · exact B2243711
  · exact B2243715
  · exact B2243719
  · exact B2243723
  · exact B2243727
  · exact B2243731
  · exact B2243735
  · exact B2243739
  · exact B2243743
  · exact B2243747
  · exact B2243751
  · exact B2243755
  · exact B2243759
  · exact B2243763
  · exact B2243767
  · exact B2243771
  · exact B2243775
  · exact B2243779
  · exact B2243783
  · exact B2243787
  · exact B2243791
  · exact B2243795
  · exact B2243799
  · exact B2243803
  · exact B2243807
  · exact B2243811
  · exact B2243815
  · exact B2243819
  · exact B2243823
  · exact B2243827
  · exact B2243831
  · exact B2243835
  · exact B2243839
  · exact B2243843
  · exact B2243847
  · exact B2243851
  · exact B2243855
  · exact B2243859
  · exact B2243863
  · exact B2243867
  · exact B2243871
  · exact B2243875
  · exact B2243879
  · exact B2243883
  · exact B2243887
  · exact B2243891
  · exact B2243895
  · exact B2243899
  · exact B2243903
  · exact B2243907
  · exact B2243911
  · exact B2243915
  · exact B2243919
  · exact B2243923
  · exact B2243927
  · exact B2243931
  · exact B2243935
  · exact B2243939
  · exact B2243943
  · exact B2243947
  · exact B2243951
  · exact B2243955
  · exact B2243959
  · exact B2243963
  · exact B2243967
  · exact B2243971
  · exact B2243975
  · exact B2243979
  · exact B2243983
  · exact B2243987
  · exact B2243991
  · exact B2243995
  · exact B2243999
  · exact B2244003
  · exact B2244007
  · exact B2244011
  · exact B2244015
  · exact B2244019
  · exact B2244023
  · exact B2244027
  · exact B2244031
  · exact B2244035
  · exact B2244039
  · exact B2244043
  · exact B2244047
  · exact B2244051
  · exact B2244055
  · exact B2244059
  · exact B2244063
  · exact B2244067
  · exact B2244071
  · exact B2244075
  · exact B2244079
  · exact B2244083
  · exact B2244087
  · exact B2244091
  · exact B2244095
  · exact B2244099
  · exact B2244103
  · exact B2244107
  · exact B2244111
  · exact B2244115
  · exact B2244119
  · exact B2244123
  · exact B2244127
  · exact B2244131
  · exact B2244135
  · exact B2244139
  · exact B2244143
  · exact B2244147
  · exact B2244151
  · exact B2244155
  · exact B2244159
  · exact B2244163
  · exact B2244167
  · exact B2244171
  · exact B2244175
  · exact B2244179
  · exact B2244183
  · exact B2244187
  · exact B2244191
  · exact B2244195
  · exact B2244199
  · exact B2244203
  · exact B2244207
  · exact B2244211
  · exact B2244215
  · exact B2244219
  · exact B2244223
  · exact B2244227
  · exact B2244231
  · exact B2244235
  · exact B2244239
  · exact B2244243
  · exact B2244247
  · exact B2244251
  · exact B2244255
  · exact B2244259
  · exact B2244263
  · exact B2244267
  · exact B2244271
  · exact B2244275
  · exact B2244279
  · exact B2244283
  · exact B2244287
  · exact B2244291
  · exact B2244295
  · exact B2244299
  · exact B2244303
  · exact B2244307
  · exact B2244311
  · exact B2244315
  · exact B2244319
  · exact B2244323
  · exact B2244327
  · exact B2244331
  · exact B2244335
  · exact B2244339
  · exact B2244343
  · exact B2244347
  · exact B2244351
  · exact B2244355
  · exact B2244359
  · exact B2244363
  · exact B2244367
  · exact B2244371
  · exact B2244375
  · exact B2244379
  · exact B2244383
  · exact B2244387
  · exact B2244391
  · exact B2244395
  · exact B2244399
  · exact B2244403
  · exact B2244407
  · exact B2244411
  · exact B2244415
  · exact B2244419
  · exact B2244423
  · exact B2244427
  · exact B2244431
  · exact B2244435
  · exact B2244439
  · exact B2244443
  · exact B2244447
  · exact B2244451
  · exact B2244455
  · exact B2244459
  · exact B2244463
  · exact B2244467
  · exact B2244471
  · exact B2244475
  · exact B2244479
  · exact B2244483
  · exact B2244487
  · exact B2244491
  · exact B2244495
  · exact B2244499
  · exact B2244503
  · exact B2244507
  · exact B2244511
  · exact B2244515
  · exact B2244519
  · exact B2244523
  · exact B2244527
  · exact B2244531
  · exact B2244535
  · exact B2244539
  · exact B2244543
  · exact B2244547
  · exact B2244551
  · exact B2244555
  · exact B2244559
  · exact B2244563
  · exact B2244567
  · exact B2244571
  · exact B2244575
  · exact B2244579
  · exact B2244583
  · exact B2244587
  · exact B2244591
  · exact B2244595
  · exact B2244599
  · exact B2244603
  · exact B2244607
  · exact B2244611
  · exact B2244615
  · exact B2244619
  · exact B2244623
  · exact B2244627
  · exact B2244631
  · exact B2244635
  · exact B2244639
  · exact B2244643
  · exact B2244647
  · exact B2244651
  · exact B2244655
  · exact B2244659
  · exact B2244663
  · exact B2244667
  · exact B2244671
  · exact B2244675
  · exact B2244679
  · exact B2244683
  · exact B2244687
  · exact B2244691
  · exact B2244695
  · exact B2244699
  · exact B2244703
  · exact B2244707
  · exact B2244711
  · exact B2244715
  · exact B2244719
  · exact B2244723
  · exact B2244727
  · exact B2244731
  · exact B2244735
  · exact B2244739
  · exact B2244743
  · exact B2244747
  · exact B2244751
  · exact B2244755
  · exact B2244759
  · exact B2244763
  · exact B2244767
  · exact B2244771
  · exact B2244775
  · exact B2244779
  · exact B2244783
  · exact B2244787
  · exact B2244791
  · exact B2244795
  · exact B2244799
  · exact B2244803
  · exact B2244807
  · exact B2244811
  · exact B2244815
  · exact B2244819
  · exact B2244823
  · exact B2244827
  · exact B2244831
  · exact B2244835
  · exact B2244839
  · exact B2244843
  · exact B2244847
  · exact B2244851
  · exact B2244855
  · exact B2244859
  · exact B2244863
  · exact B2244867
  · exact B2244871
  · exact B2244875
  · exact B2244879
  · exact B2244883
  · exact B2244887
  · exact B2244891
  · exact B2244895
  · exact B2244899
  · exact B2244903
  · exact B2244907
  · exact B2244911
  · exact B2244915
  · exact B2244919
  · exact B2244923
  · exact B2244927
  · exact B2244931
  · exact B2244935
  · exact B2244939
  · exact B2244943
  · exact B2244947
  · exact B2244951
  · exact B2244955
  · exact B2244959
  · exact B2244963
  · exact B2244967
  · exact B2244971
  · exact B2244975
  · exact B2244979
  · exact B2244983
  · exact B2244987
  · exact B2244991
  · exact B2244995
  · exact B2244999
  · exact B2245003
  · exact B2245007
  · exact B2245011
  · exact B2245015
  · exact B2245019
  · exact B2245023
  · exact B2245027
  · exact B2245031
  · exact B2245035
  · exact B2245039
  · exact B2245043
  · exact B2245047
  · exact B2245051
  · exact B2245055
  · exact B2245059
  · exact B2245063
  · exact B2245067
  · exact B2245071
  · exact B2245075
  · exact B2245079
  · exact B2245083
  · exact B2245087
  · exact B2245091
  · exact B2245095
  · exact B2245099
  · exact B2245103
  · exact B2245107
  · exact B2245111
  · exact B2245115
  · exact B2245119
  · exact B2245123
  · exact B2245127
  · exact B2245131
  · exact B2245135
  · exact B2245139
  · exact B2245143
  · exact B2245147
  · exact B2245151
  · exact B2245155
  · exact B2245159
  · exact B2245163
  · exact B2245167
  · exact B2245171
  · exact B2245175
  · exact B2245179
  · exact B2245183
  · exact B2245187
  · exact B2245191
  · exact B2245195
  · exact B2245199
  · exact B2245203
  · exact B2245207
  · exact B2245211
  · exact B2245215
  · exact B2245219
  · exact B2245223
  · exact B2245227
  · exact B2245231
  · exact B2245235
  · exact B2245239
  · exact B2245243
  · exact B2245247
  · exact B2245251
  · exact B2245255
  · exact B2245259
  · exact B2245263
  · exact B2245267
  · exact B2245271
  · exact B2245275
  · exact B2245279
  · exact B2245283
  · exact B2245287
  · exact B2245291
  · exact B2245295
  · exact B2245299
  · exact B2245303
  · exact B2245307
  · exact B2245311
  · exact B2245315
  · exact B2245319
  · exact B2245323
  · exact B2245327
  · exact B2245331
  · exact B2245335
  · exact B2245339
  · exact B2245343
  · exact B2245347
  · exact B2245351
  · exact B2245355
  · exact B2245359
  · exact B2245363
  · exact B2245367
  · exact B2245371
  · exact B2245375
  · exact B2245379
  · exact B2245383
  · exact B2245387
  · exact B2245391
  · exact B2245395
  · exact B2245399
  · exact B2245403
  · exact B2245407
  · exact B2245411
  · exact B2245415
  · exact B2245419
  · exact B2245423
  · exact B2245427
  · exact B2245431
  · exact B2245435
theorem solution (m : ℕ) (hlo : 2243435 ≤ m) (hhi : m ≤ 2245435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 560858 ≤ j := by omega
    have hj2 : j ≤ 561358 := by omega
    have hb : Blo 2243435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
