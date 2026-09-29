-- Prove2me | solution 1 for syracuse_descends_range_1780091_1782091
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:44:21.311381+00:00
-- url     : https://prove2.me/submissions/da68d5de-78e2-4b0a-80b6-5ea040af536c

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


theorem B2670605 : Blo 1780091 2670605 := bbase (se 3 (by rfl) ⟨500738, by rfl⟩ : syracuseStep 2670605 = 1001477) (by norm_num)
theorem B4005917 : Blo 1780091 4005917 := bbase (se 3 (by rfl) ⟨751109, by rfl⟩ : syracuseStep 4005917 = 1502219) (by norm_num)
theorem B2670629 : Blo 1780091 2670629 := bbase (se 4 (by rfl) ⟨250371, by rfl⟩ : syracuseStep 2670629 = 500743) (by norm_num)
theorem B3006517 : Blo 1780091 3006517 := bbase (se 5 (by rfl) ⟨140930, by rfl⟩ : syracuseStep 3006517 = 281861) (by norm_num)
theorem B2670653 : Blo 1780091 2670653 := bbase (se 3 (by rfl) ⟨500747, by rfl⟩ : syracuseStep 2670653 = 1001495) (by norm_num)
theorem B2670677 : Blo 1780091 2670677 := bbase (se 8 (by rfl) ⟨15648, by rfl⟩ : syracuseStep 2670677 = 31297) (by norm_num)
theorem B3612757 : Blo 1780091 3612757 := bbase (se 8 (by rfl) ⟨21168, by rfl⟩ : syracuseStep 3612757 = 42337) (by norm_num)
theorem B4005989 : Blo 1780091 4005989 := bbase (se 4 (by rfl) ⟨375561, by rfl⟩ : syracuseStep 4005989 = 751123) (by norm_num)
theorem B2670701 : Blo 1780091 2670701 := bbase (se 3 (by rfl) ⟨500756, by rfl⟩ : syracuseStep 2670701 = 1001513) (by norm_num)
theorem B2252929 : Blo 1780091 2252929 := bbase (se 2 (by rfl) ⟨844848, by rfl⟩ : syracuseStep 2252929 = 1689697) (by norm_num)
theorem B2670725 : Blo 1780091 2670725 := bbase (se 4 (by rfl) ⟨250380, by rfl⟩ : syracuseStep 2670725 = 500761) (by norm_num)
theorem B6013061 : Blo 1780091 6013061 := bbase (se 4 (by rfl) ⟨563724, by rfl⟩ : syracuseStep 6013061 = 1127449) (by norm_num)
theorem B3006605 : Blo 1780091 3006605 := bbase (se 3 (by rfl) ⟨563738, by rfl⟩ : syracuseStep 3006605 = 1127477) (by norm_num)
theorem B2670749 : Blo 1780091 2670749 := bbase (se 3 (by rfl) ⟨500765, by rfl⟩ : syracuseStep 2670749 = 1001531) (by norm_num)
theorem B4006061 : Blo 1780091 4006061 := bbase (se 3 (by rfl) ⟨751136, by rfl⟩ : syracuseStep 4006061 = 1502273) (by norm_num)
theorem B2670773 : Blo 1780091 2670773 := bbase (se 5 (by rfl) ⟨125192, by rfl⟩ : syracuseStep 2670773 = 250385) (by norm_num)
theorem B2670797 : Blo 1780091 2670797 := bbase (se 3 (by rfl) ⟨500774, by rfl⟩ : syracuseStep 2670797 = 1001549) (by norm_num)
theorem B5071061 : Blo 1780091 5071061 := bbase (se 7 (by rfl) ⟨59426, by rfl⟩ : syracuseStep 5071061 = 118853) (by norm_num)
theorem B2253025 : Blo 1780091 2253025 := bbase (se 2 (by rfl) ⟨844884, by rfl⟩ : syracuseStep 2253025 = 1689769) (by norm_num)
theorem B2670821 : Blo 1780091 2670821 := bbase (se 4 (by rfl) ⟨250389, by rfl⟩ : syracuseStep 2670821 = 500779) (by norm_num)
theorem B4006133 : Blo 1780091 4006133 := bbase (se 5 (by rfl) ⟨187787, by rfl⟩ : syracuseStep 4006133 = 375575) (by norm_num)
theorem B2670845 : Blo 1780091 2670845 := bbase (se 3 (by rfl) ⟨500783, by rfl⟩ : syracuseStep 2670845 = 1001567) (by norm_num)
theorem B3006733 : Blo 1780091 3006733 := bbase (se 3 (by rfl) ⟨563762, by rfl⟩ : syracuseStep 3006733 = 1127525) (by norm_num)
theorem B2670869 : Blo 1780091 2670869 := bbase (se 6 (by rfl) ⟨62598, by rfl⟩ : syracuseStep 2670869 = 125197) (by norm_num)
theorem B2670893 : Blo 1780091 2670893 := bbase (se 3 (by rfl) ⟨500792, by rfl⟩ : syracuseStep 2670893 = 1001585) (by norm_num)
theorem B2007349 : Blo 1780091 2007349 := bbase (se 5 (by rfl) ⟨94094, by rfl⟩ : syracuseStep 2007349 = 188189) (by norm_num)
theorem B4006205 : Blo 1780091 4006205 := bbase (se 3 (by rfl) ⟨751163, by rfl⟩ : syracuseStep 4006205 = 1502327) (by norm_num)
theorem B2670917 : Blo 1780091 2670917 := bbase (se 4 (by rfl) ⟨250398, by rfl⟩ : syracuseStep 2670917 = 500797) (by norm_num)
theorem B2670941 : Blo 1780091 2670941 := bbase (se 3 (by rfl) ⟨500801, by rfl⟩ : syracuseStep 2670941 = 1001603) (by norm_num)
theorem B3006821 : Blo 1780091 3006821 := bbase (se 4 (by rfl) ⟨281889, by rfl⟩ : syracuseStep 3006821 = 563779) (by norm_num)
theorem B1900913 : Blo 1780091 1900913 := bbase (se 2 (by rfl) ⟨712842, by rfl⟩ : syracuseStep 1900913 = 1425685) (by norm_num)
theorem B2670965 : Blo 1780091 2670965 := bbase (se 5 (by rfl) ⟨125201, by rfl⟩ : syracuseStep 2670965 = 250403) (by norm_num)
theorem B4505989 : Blo 1780091 4505989 := bbase (se 4 (by rfl) ⟨422436, by rfl⟩ : syracuseStep 4505989 = 844873) (by norm_num)
theorem B4006277 : Blo 1780091 4006277 := bbase (se 4 (by rfl) ⟨375588, by rfl⟩ : syracuseStep 4006277 = 751177) (by norm_num)
theorem B2253197 : Blo 1780091 2253197 := bbase (se 3 (by rfl) ⟨422474, by rfl⟩ : syracuseStep 2253197 = 844949) (by norm_num)
theorem B2670989 : Blo 1780091 2670989 := bbase (se 3 (by rfl) ⟨500810, by rfl⟩ : syracuseStep 2670989 = 1001621) (by norm_num)
theorem B2671013 : Blo 1780091 2671013 := bbase (se 4 (by rfl) ⟨250407, by rfl⟩ : syracuseStep 2671013 = 500815) (by norm_num)
theorem B2671037 : Blo 1780091 2671037 := bbase (se 3 (by rfl) ⟨500819, by rfl⟩ : syracuseStep 2671037 = 1001639) (by norm_num)
theorem B2253253 : Blo 1780091 2253253 := bbase (se 4 (by rfl) ⟨211242, by rfl⟩ : syracuseStep 2253253 = 422485) (by norm_num)
theorem B4006349 : Blo 1780091 4006349 := bbase (se 3 (by rfl) ⟨751190, by rfl⟩ : syracuseStep 4006349 = 1502381) (by norm_num)
theorem B2671061 : Blo 1780091 2671061 := bbase (se 7 (by rfl) ⟨31301, by rfl⟩ : syracuseStep 2671061 = 62603) (by norm_num)
theorem B3006949 : Blo 1780091 3006949 := bbase (se 4 (by rfl) ⟨281901, by rfl⟩ : syracuseStep 3006949 = 563803) (by norm_num)
theorem B2671085 : Blo 1780091 2671085 := bbase (se 3 (by rfl) ⟨500828, by rfl⟩ : syracuseStep 2671085 = 1001657) (by norm_num)
theorem B4506101 : Blo 1780091 4506101 := bbase (se 5 (by rfl) ⟨211223, by rfl⟩ : syracuseStep 4506101 = 422447) (by norm_num)
theorem B2671109 : Blo 1780091 2671109 := bbase (se 4 (by rfl) ⟨250416, by rfl⟩ : syracuseStep 2671109 = 500833) (by norm_num)
theorem B4006421 : Blo 1780091 4006421 := bbase (se 6 (by rfl) ⟨93900, by rfl⟩ : syracuseStep 4006421 = 187801) (by norm_num)
theorem B2138653 : Blo 1780091 2138653 := bbase (se 3 (by rfl) ⟨400997, by rfl⟩ : syracuseStep 2138653 = 801995) (by norm_num)
theorem B2671133 : Blo 1780091 2671133 := bbase (se 3 (by rfl) ⟨500837, by rfl⟩ : syracuseStep 2671133 = 1001675) (by norm_num)
theorem B2253349 : Blo 1780091 2253349 := bbase (se 4 (by rfl) ⟨211251, by rfl⟩ : syracuseStep 2253349 = 422503) (by norm_num)
theorem B2671157 : Blo 1780091 2671157 := bbase (se 5 (by rfl) ⟨125210, by rfl⟩ : syracuseStep 2671157 = 250421) (by norm_num)
theorem B6013493 : Blo 1780091 6013493 := bbase (se 5 (by rfl) ⟨281882, by rfl⟩ : syracuseStep 6013493 = 563765) (by norm_num)
theorem B3007037 : Blo 1780091 3007037 := bbase (se 3 (by rfl) ⟨563819, by rfl⟩ : syracuseStep 3007037 = 1127639) (by norm_num)
theorem B2032193 : Blo 1780091 2032193 := bbase (se 2 (by rfl) ⟨762072, by rfl⟩ : syracuseStep 2032193 = 1524145) (by norm_num)
theorem B2671181 : Blo 1780091 2671181 := bbase (se 3 (by rfl) ⟨500846, by rfl⟩ : syracuseStep 2671181 = 1001693) (by norm_num)
theorem B2851421 : Blo 1780091 2851421 := bbase (se 3 (by rfl) ⟨534641, by rfl⟩ : syracuseStep 2851421 = 1069283) (by norm_num)
theorem B4006493 : Blo 1780091 4006493 := bbase (se 3 (by rfl) ⟨751217, by rfl⟩ : syracuseStep 4006493 = 1502435) (by norm_num)
theorem B2671205 : Blo 1780091 2671205 := bbase (se 4 (by rfl) ⟨250425, by rfl⟩ : syracuseStep 2671205 = 500851) (by norm_num)
theorem B1901161 : Blo 1780091 1901161 := bbase (se 2 (by rfl) ⟨712935, by rfl⟩ : syracuseStep 1901161 = 1425871) (by norm_num)
theorem B2671229 : Blo 1780091 2671229 := bbase (se 3 (by rfl) ⟨500855, by rfl⟩ : syracuseStep 2671229 = 1001711) (by norm_num)
theorem B2671253 : Blo 1780091 2671253 := bbase (se 6 (by rfl) ⟨62607, by rfl⟩ : syracuseStep 2671253 = 125215) (by norm_num)
theorem B4006565 : Blo 1780091 4006565 := bbase (se 4 (by rfl) ⟨375615, by rfl⟩ : syracuseStep 4006565 = 751231) (by norm_num)
theorem B2671277 : Blo 1780091 2671277 := bbase (se 3 (by rfl) ⟨500864, by rfl⟩ : syracuseStep 2671277 = 1001729) (by norm_num)
theorem B4506293 : Blo 1780091 4506293 := bbase (se 5 (by rfl) ⟨211232, by rfl⟩ : syracuseStep 4506293 = 422465) (by norm_num)
theorem B3007165 : Blo 1780091 3007165 := bbase (se 3 (by rfl) ⟨563843, by rfl⟩ : syracuseStep 3007165 = 1127687) (by norm_num)
theorem B2671301 : Blo 1780091 2671301 := bbase (se 4 (by rfl) ⟨250434, by rfl⟩ : syracuseStep 2671301 = 500869) (by norm_num)
theorem B2253521 : Blo 1780091 2253521 := bbase (se 2 (by rfl) ⟨845070, by rfl⟩ : syracuseStep 2253521 = 1690141) (by norm_num)
theorem B21660373 : Blo 1780091 21660373 := bbase (se 7 (by rfl) ⟨253832, by rfl⟩ : syracuseStep 21660373 = 507665) (by norm_num)
theorem B2671325 : Blo 1780091 2671325 := bbase (se 3 (by rfl) ⟨500873, by rfl⟩ : syracuseStep 2671325 = 1001747) (by norm_num)
theorem B4006637 : Blo 1780091 4006637 := bbase (se 3 (by rfl) ⟨751244, by rfl⟩ : syracuseStep 4006637 = 1502489) (by norm_num)
theorem B2138869 : Blo 1780091 2138869 := bbase (se 5 (by rfl) ⟨100259, by rfl⟩ : syracuseStep 2138869 = 200519) (by norm_num)
theorem B2671349 : Blo 1780091 2671349 := bbase (se 5 (by rfl) ⟨125219, by rfl⟩ : syracuseStep 2671349 = 250439) (by norm_num)
theorem B2253577 : Blo 1780091 2253577 := bbase (se 2 (by rfl) ⟨845091, by rfl⟩ : syracuseStep 2253577 = 1690183) (by norm_num)
theorem B2671373 : Blo 1780091 2671373 := bbase (se 3 (by rfl) ⟨500882, by rfl⟩ : syracuseStep 2671373 = 1001765) (by norm_num)
theorem B11412245 : Blo 1780091 11412245 := bbase (se 6 (by rfl) ⟨267474, by rfl⟩ : syracuseStep 11412245 = 534949) (by norm_num)
theorem B3007253 : Blo 1780091 3007253 := bbase (se 6 (by rfl) ⟨70482, by rfl⟩ : syracuseStep 3007253 = 140965) (by norm_num)
theorem B2671397 : Blo 1780091 2671397 := bbase (se 4 (by rfl) ⟨250443, by rfl⟩ : syracuseStep 2671397 = 500887) (by norm_num)
theorem B4006709 : Blo 1780091 4006709 := bbase (se 5 (by rfl) ⟨187814, by rfl⟩ : syracuseStep 4006709 = 375629) (by norm_num)
theorem B2671421 : Blo 1780091 2671421 := bbase (se 3 (by rfl) ⟨500891, by rfl⟩ : syracuseStep 2671421 = 1001783) (by norm_num)
theorem B7611205 : Blo 1780091 7611205 := bbase (se 4 (by rfl) ⟨713550, by rfl⟩ : syracuseStep 7611205 = 1427101) (by norm_num)
theorem B2671445 : Blo 1780091 2671445 := bbase (se 9 (by rfl) ⟨7826, by rfl⟩ : syracuseStep 2671445 = 15653) (by norm_num)
theorem B2253673 : Blo 1780091 2253673 := bbase (se 2 (by rfl) ⟨845127, by rfl⟩ : syracuseStep 2253673 = 1690255) (by norm_num)
theorem B2671469 : Blo 1780091 2671469 := bbase (se 3 (by rfl) ⟨500900, by rfl⟩ : syracuseStep 2671469 = 1001801) (by norm_num)
theorem B4006781 : Blo 1780091 4006781 := bbase (se 3 (by rfl) ⟨751271, by rfl⟩ : syracuseStep 4006781 = 1502543) (by norm_num)
theorem B2671493 : Blo 1780091 2671493 := bbase (se 4 (by rfl) ⟨250452, by rfl⟩ : syracuseStep 2671493 = 500905) (by norm_num)
theorem B2671517 : Blo 1780091 2671517 := bbase (se 3 (by rfl) ⟨500909, by rfl⟩ : syracuseStep 2671517 = 1001819) (by norm_num)
theorem B2671541 : Blo 1780091 2671541 := bbase (se 5 (by rfl) ⟨125228, by rfl⟩ : syracuseStep 2671541 = 250457) (by norm_num)
theorem B4006853 : Blo 1780091 4006853 := bbase (se 4 (by rfl) ⟨375642, by rfl⟩ : syracuseStep 4006853 = 751285) (by norm_num)
theorem B2671565 : Blo 1780091 2671565 := bbase (se 3 (by rfl) ⟨500918, by rfl⟩ : syracuseStep 2671565 = 1001837) (by norm_num)
theorem B2671589 : Blo 1780091 2671589 := bbase (se 4 (by rfl) ⟨250461, by rfl⟩ : syracuseStep 2671589 = 500923) (by norm_num)
theorem B6013925 : Blo 1780091 6013925 := bbase (se 4 (by rfl) ⟨563805, by rfl⟩ : syracuseStep 6013925 = 1127611) (by norm_num)
theorem B2671613 : Blo 1780091 2671613 := bbase (se 3 (by rfl) ⟨500927, by rfl⟩ : syracuseStep 2671613 = 1001855) (by norm_num)
theorem B4506637 : Blo 1780091 4506637 := bbase (se 3 (by rfl) ⟨844994, by rfl⟩ : syracuseStep 4506637 = 1689989) (by norm_num)
theorem B4006925 : Blo 1780091 4006925 := bbase (se 3 (by rfl) ⟨751298, by rfl⟩ : syracuseStep 4006925 = 1502597) (by norm_num)
theorem B2253845 : Blo 1780091 2253845 := bbase (se 6 (by rfl) ⟨52824, by rfl⟩ : syracuseStep 2253845 = 105649) (by norm_num)
theorem B2671637 : Blo 1780091 2671637 := bbase (se 6 (by rfl) ⟨62616, by rfl⟩ : syracuseStep 2671637 = 125233) (by norm_num)
theorem B1901593 : Blo 1780091 1901593 := bbase (se 2 (by rfl) ⟨713097, by rfl⟩ : syracuseStep 1901593 = 1426195) (by norm_num)
theorem B2671661 : Blo 1780091 2671661 := bbase (se 3 (by rfl) ⟨500936, by rfl⟩ : syracuseStep 2671661 = 1001873) (by norm_num)
theorem B6947893 : Blo 1780091 6947893 := bbase (se 5 (by rfl) ⟨325682, by rfl⟩ : syracuseStep 6947893 = 651365) (by norm_num)
theorem B2671685 : Blo 1780091 2671685 := bbase (se 4 (by rfl) ⟨250470, by rfl⟩ : syracuseStep 2671685 = 500941) (by norm_num)
theorem B2253901 : Blo 1780091 2253901 := bbase (se 3 (by rfl) ⟨422606, by rfl⟩ : syracuseStep 2253901 = 845213) (by norm_num)
theorem B4006997 : Blo 1780091 4006997 := bbase (se 8 (by rfl) ⟨23478, by rfl⟩ : syracuseStep 4006997 = 46957) (by norm_num)
theorem B26395733 : Blo 1780091 26395733 := bbase (se 8 (by rfl) ⟨154662, by rfl⟩ : syracuseStep 26395733 = 309325) (by norm_num)
theorem B2671709 : Blo 1780091 2671709 := bbase (se 3 (by rfl) ⟨500945, by rfl⟩ : syracuseStep 2671709 = 1001891) (by norm_num)
theorem B1901665 : Blo 1780091 1901665 := bbase (se 2 (by rfl) ⟨713124, by rfl⟩ : syracuseStep 1901665 = 1426249) (by norm_num)
theorem B2671733 : Blo 1780091 2671733 := bbase (se 5 (by rfl) ⟨125237, by rfl⟩ : syracuseStep 2671733 = 250475) (by norm_num)
theorem B4506749 : Blo 1780091 4506749 := bbase (se 3 (by rfl) ⟨845015, by rfl⟩ : syracuseStep 4506749 = 1690031) (by norm_num)
theorem B2671757 : Blo 1780091 2671757 := bbase (se 3 (by rfl) ⟨500954, by rfl⟩ : syracuseStep 2671757 = 1001909) (by norm_num)
theorem B4007069 : Blo 1780091 4007069 := bbase (se 3 (by rfl) ⟨751325, by rfl⟩ : syracuseStep 4007069 = 1502651) (by norm_num)
theorem B2671781 : Blo 1780091 2671781 := bbase (se 4 (by rfl) ⟨250479, by rfl⟩ : syracuseStep 2671781 = 500959) (by norm_num)
theorem B2253997 : Blo 1780091 2253997 := bbase (se 3 (by rfl) ⟨422624, by rfl⟩ : syracuseStep 2253997 = 845249) (by norm_num)
theorem B2671805 : Blo 1780091 2671805 := bbase (se 3 (by rfl) ⟨500963, by rfl⟩ : syracuseStep 2671805 = 1001927) (by norm_num)
theorem B2671829 : Blo 1780091 2671829 := bbase (se 7 (by rfl) ⟨31310, by rfl⟩ : syracuseStep 2671829 = 62621) (by norm_num)
theorem B4007141 : Blo 1780091 4007141 := bbase (se 4 (by rfl) ⟨375669, by rfl⟩ : syracuseStep 4007141 = 751339) (by norm_num)
theorem B9020645 : Blo 1780091 9020645 := bbase (se 4 (by rfl) ⟨845685, by rfl⟩ : syracuseStep 9020645 = 1691371) (by norm_num)
theorem B2671853 : Blo 1780091 2671853 := bbase (se 3 (by rfl) ⟨500972, by rfl⟩ : syracuseStep 2671853 = 1001945) (by norm_num)
theorem B2852101 : Blo 1780091 2852101 := bbase (se 4 (by rfl) ⟨267384, by rfl⟩ : syracuseStep 2852101 = 534769) (by norm_num)
theorem B2671877 : Blo 1780091 2671877 := bbase (se 4 (by rfl) ⟨250488, by rfl⟩ : syracuseStep 2671877 = 500977) (by norm_num)
theorem B2671901 : Blo 1780091 2671901 := bbase (se 3 (by rfl) ⟨500981, by rfl⟩ : syracuseStep 2671901 = 1001963) (by norm_num)
theorem B4007213 : Blo 1780091 4007213 := bbase (se 3 (by rfl) ⟨751352, by rfl⟩ : syracuseStep 4007213 = 1502705) (by norm_num)
theorem B2671925 : Blo 1780091 2671925 := bbase (se 5 (by rfl) ⟨125246, by rfl⟩ : syracuseStep 2671925 = 250493) (by norm_num)
theorem B4506941 : Blo 1780091 4506941 := bbase (se 3 (by rfl) ⟨845051, by rfl⟩ : syracuseStep 4506941 = 1690103) (by norm_num)
theorem B2852165 : Blo 1780091 2852165 := bbase (se 4 (by rfl) ⟨267390, by rfl⟩ : syracuseStep 2852165 = 534781) (by norm_num)
theorem B2671949 : Blo 1780091 2671949 := bbase (se 3 (by rfl) ⟨500990, by rfl⟩ : syracuseStep 2671949 = 1001981) (by norm_num)
theorem B38495573 : Blo 1780091 38495573 := bbase (se 12 (by rfl) ⟨14097, by rfl⟩ : syracuseStep 38495573 = 28195) (by norm_num)
theorem B2254169 : Blo 1780091 2254169 := bbase (se 2 (by rfl) ⟨845313, by rfl⟩ : syracuseStep 2254169 = 1690627) (by norm_num)
theorem B2671973 : Blo 1780091 2671973 := bbase (se 4 (by rfl) ⟨250497, by rfl⟩ : syracuseStep 2671973 = 500995) (by norm_num)
theorem B4007285 : Blo 1780091 4007285 := bbase (se 5 (by rfl) ⟨187841, by rfl⟩ : syracuseStep 4007285 = 375683) (by norm_num)
theorem B2671997 : Blo 1780091 2671997 := bbase (se 3 (by rfl) ⟨500999, by rfl⟩ : syracuseStep 2671997 = 1001999) (by norm_num)
theorem B2254225 : Blo 1780091 2254225 := bbase (se 2 (by rfl) ⟨845334, by rfl⟩ : syracuseStep 2254225 = 1690669) (by norm_num)
theorem B2672021 : Blo 1780091 2672021 := bbase (se 6 (by rfl) ⟨62625, by rfl⟩ : syracuseStep 2672021 = 125251) (by norm_num)
theorem B6014357 : Blo 1780091 6014357 := bbase (se 6 (by rfl) ⟨140961, by rfl⟩ : syracuseStep 6014357 = 281923) (by norm_num)
theorem B2672045 : Blo 1780091 2672045 := bbase (se 3 (by rfl) ⟨501008, by rfl⟩ : syracuseStep 2672045 = 1002017) (by norm_num)
theorem B4007357 : Blo 1780091 4007357 := bbase (se 3 (by rfl) ⟨751379, by rfl⟩ : syracuseStep 4007357 = 1502759) (by norm_num)
theorem B2672069 : Blo 1780091 2672069 := bbase (se 4 (by rfl) ⟨250506, by rfl⟩ : syracuseStep 2672069 = 501013) (by norm_num)
theorem B1902037 : Blo 1780091 1902037 := bbase (se 7 (by rfl) ⟨22289, by rfl⟩ : syracuseStep 1902037 = 44579) (by norm_num)
theorem B2672093 : Blo 1780091 2672093 := bbase (se 3 (by rfl) ⟨501017, by rfl⟩ : syracuseStep 2672093 = 1002035) (by norm_num)
theorem B2254321 : Blo 1780091 2254321 := bbase (se 2 (by rfl) ⟨845370, by rfl⟩ : syracuseStep 2254321 = 1690741) (by norm_num)
theorem B2672117 : Blo 1780091 2672117 := bbase (se 5 (by rfl) ⟨125255, by rfl⟩ : syracuseStep 2672117 = 250511) (by norm_num)
theorem B4007429 : Blo 1780091 4007429 := bbase (se 4 (by rfl) ⟨375696, by rfl⟩ : syracuseStep 4007429 = 751393) (by norm_num)
theorem B2672141 : Blo 1780091 2672141 := bbase (se 3 (by rfl) ⟨501026, by rfl⟩ : syracuseStep 2672141 = 1002053) (by norm_num)
theorem B2672165 : Blo 1780091 2672165 := bbase (se 4 (by rfl) ⟨250515, by rfl⟩ : syracuseStep 2672165 = 501031) (by norm_num)
theorem B2672189 : Blo 1780091 2672189 := bbase (se 3 (by rfl) ⟨501035, by rfl⟩ : syracuseStep 2672189 = 1002071) (by norm_num)
theorem B4007501 : Blo 1780091 4007501 := bbase (se 3 (by rfl) ⟨751406, by rfl⟩ : syracuseStep 4007501 = 1502813) (by norm_num)
theorem B2672213 : Blo 1780091 2672213 := bbase (se 8 (by rfl) ⟨15657, by rfl⟩ : syracuseStep 2672213 = 31315) (by norm_num)
theorem B2672237 : Blo 1780091 2672237 := bbase (se 3 (by rfl) ⟨501044, by rfl⟩ : syracuseStep 2672237 = 1002089) (by norm_num)
theorem B9012869 : Blo 1780091 9012869 := bbase (se 4 (by rfl) ⟨844956, by rfl⟩ : syracuseStep 9012869 = 1689913) (by norm_num)
theorem B2672261 : Blo 1780091 2672261 := bbase (se 4 (by rfl) ⟨250524, by rfl⟩ : syracuseStep 2672261 = 501049) (by norm_num)
theorem B4507285 : Blo 1780091 4507285 := bbase (se 6 (by rfl) ⟨105639, by rfl⟩ : syracuseStep 4507285 = 211279) (by norm_num)
theorem B4007573 : Blo 1780091 4007573 := bbase (se 6 (by rfl) ⟨93927, by rfl⟩ : syracuseStep 4007573 = 187855) (by norm_num)
theorem B2254493 : Blo 1780091 2254493 := bbase (se 3 (by rfl) ⟨422717, by rfl⟩ : syracuseStep 2254493 = 845435) (by norm_num)
theorem B2672285 : Blo 1780091 2672285 := bbase (se 3 (by rfl) ⟨501053, by rfl⟩ : syracuseStep 2672285 = 1002107) (by norm_num)
theorem B2672309 : Blo 1780091 2672309 := bbase (se 5 (by rfl) ⟨125264, by rfl⟩ : syracuseStep 2672309 = 250529) (by norm_num)
theorem B2672333 : Blo 1780091 2672333 := bbase (se 3 (by rfl) ⟨501062, by rfl⟩ : syracuseStep 2672333 = 1002125) (by norm_num)
theorem B2254549 : Blo 1780091 2254549 := bbase (se 7 (by rfl) ⟨26420, by rfl⟩ : syracuseStep 2254549 = 52841) (by norm_num)
theorem B4007645 : Blo 1780091 4007645 := bbase (se 3 (by rfl) ⟨751433, by rfl⟩ : syracuseStep 4007645 = 1502867) (by norm_num)
theorem B2672357 : Blo 1780091 2672357 := bbase (se 4 (by rfl) ⟨250533, by rfl⟩ : syracuseStep 2672357 = 501067) (by norm_num)
theorem B2672381 : Blo 1780091 2672381 := bbase (se 3 (by rfl) ⟨501071, by rfl⟩ : syracuseStep 2672381 = 1002143) (by norm_num)
theorem B4507397 : Blo 1780091 4507397 := bbase (se 4 (by rfl) ⟨422568, by rfl⟩ : syracuseStep 4507397 = 845137) (by norm_num)
theorem B5072645 : Blo 1780091 5072645 := bbase (se 4 (by rfl) ⟨475560, by rfl⟩ : syracuseStep 5072645 = 951121) (by norm_num)
theorem B2672405 : Blo 1780091 2672405 := bbase (se 6 (by rfl) ⟨62634, by rfl⟩ : syracuseStep 2672405 = 125269) (by norm_num)
theorem B4007717 : Blo 1780091 4007717 := bbase (se 4 (by rfl) ⟨375723, by rfl⟩ : syracuseStep 4007717 = 751447) (by norm_num)
theorem B2672429 : Blo 1780091 2672429 := bbase (se 3 (by rfl) ⟨501080, by rfl⟩ : syracuseStep 2672429 = 1002161) (by norm_num)
theorem B10282805 : Blo 1780091 10282805 := bbase (se 5 (by rfl) ⟨482006, by rfl⟩ : syracuseStep 10282805 = 964013) (by norm_num)
theorem B13526837 : Blo 1780091 13526837 := bbase (se 5 (by rfl) ⟨634070, by rfl⟩ : syracuseStep 13526837 = 1268141) (by norm_num)
theorem B2254645 : Blo 1780091 2254645 := bbase (se 5 (by rfl) ⟨105686, by rfl⟩ : syracuseStep 2254645 = 211373) (by norm_num)
theorem B2672453 : Blo 1780091 2672453 := bbase (se 4 (by rfl) ⟨250542, by rfl⟩ : syracuseStep 2672453 = 501085) (by norm_num)
theorem B1902413 : Blo 1780091 1902413 := bbase (se 3 (by rfl) ⟨356702, by rfl⟩ : syracuseStep 1902413 = 713405) (by norm_num)
theorem B5703509 : Blo 1780091 5703509 := bbase (se 9 (by rfl) ⟨16709, by rfl⟩ : syracuseStep 5703509 = 33419) (by norm_num)
theorem B15222613 : Blo 1780091 15222613 := bbase (se 9 (by rfl) ⟨44597, by rfl⟩ : syracuseStep 15222613 = 89195) (by norm_num)
theorem B2672477 : Blo 1780091 2672477 := bbase (se 3 (by rfl) ⟨501089, by rfl⟩ : syracuseStep 2672477 = 1002179) (by norm_num)
theorem B4007789 : Blo 1780091 4007789 := bbase (se 3 (by rfl) ⟨751460, by rfl⟩ : syracuseStep 4007789 = 1502921) (by norm_num)
theorem B2672501 : Blo 1780091 2672501 := bbase (se 5 (by rfl) ⟨125273, by rfl⟩ : syracuseStep 2672501 = 250547) (by norm_num)
theorem B2672525 : Blo 1780091 2672525 := bbase (se 3 (by rfl) ⟨501098, by rfl⟩ : syracuseStep 2672525 = 1002197) (by norm_num)
theorem B1902485 : Blo 1780091 1902485 := bbase (se 6 (by rfl) ⟨44589, by rfl⟩ : syracuseStep 1902485 = 89179) (by norm_num)
theorem B2672549 : Blo 1780091 2672549 := bbase (se 4 (by rfl) ⟨250551, by rfl⟩ : syracuseStep 2672549 = 501103) (by norm_num)
theorem B4007861 : Blo 1780091 4007861 := bbase (se 5 (by rfl) ⟨187868, by rfl⟩ : syracuseStep 4007861 = 375737) (by norm_num)
theorem B2672573 : Blo 1780091 2672573 := bbase (se 3 (by rfl) ⟨501107, by rfl⟩ : syracuseStep 2672573 = 1002215) (by norm_num)
theorem B4507589 : Blo 1780091 4507589 := bbase (se 4 (by rfl) ⟨422586, by rfl⟩ : syracuseStep 4507589 = 845173) (by norm_num)
theorem B2672597 : Blo 1780091 2672597 := bbase (se 7 (by rfl) ⟨31319, by rfl⟩ : syracuseStep 2672597 = 62639) (by norm_num)
theorem B2254817 : Blo 1780091 2254817 := bbase (se 2 (by rfl) ⟨845556, by rfl⟩ : syracuseStep 2254817 = 1691113) (by norm_num)
theorem B2672621 : Blo 1780091 2672621 := bbase (se 3 (by rfl) ⟨501116, by rfl⟩ : syracuseStep 2672621 = 1002233) (by norm_num)
theorem B3803125 : Blo 1780091 3803125 := bbase (se 5 (by rfl) ⟨178271, by rfl⟩ : syracuseStep 3803125 = 356543) (by norm_num)
theorem B4007933 : Blo 1780091 4007933 := bbase (se 3 (by rfl) ⟨751487, by rfl⟩ : syracuseStep 4007933 = 1502975) (by norm_num)
theorem B2672645 : Blo 1780091 2672645 := bbase (se 4 (by rfl) ⟨250560, by rfl⟩ : syracuseStep 2672645 = 501121) (by norm_num)
theorem B2254873 : Blo 1780091 2254873 := bbase (se 2 (by rfl) ⟨845577, by rfl⟩ : syracuseStep 2254873 = 1691155) (by norm_num)
theorem B2672669 : Blo 1780091 2672669 := bbase (se 3 (by rfl) ⟨501125, by rfl⟩ : syracuseStep 2672669 = 1002251) (by norm_num)
theorem B2672693 : Blo 1780091 2672693 := bbase (se 5 (by rfl) ⟨125282, by rfl⟩ : syracuseStep 2672693 = 250565) (by norm_num)
theorem B4008005 : Blo 1780091 4008005 := bbase (se 4 (by rfl) ⟨375750, by rfl⟩ : syracuseStep 4008005 = 751501) (by norm_num)
theorem B2672717 : Blo 1780091 2672717 := bbase (se 3 (by rfl) ⟨501134, by rfl⟩ : syracuseStep 2672717 = 1002269) (by norm_num)
theorem B1902673 : Blo 1780091 1902673 := bbase (se 2 (by rfl) ⟨713502, by rfl⟩ : syracuseStep 1902673 = 1427005) (by norm_num)
theorem B2672741 : Blo 1780091 2672741 := bbase (se 4 (by rfl) ⟨250569, by rfl⟩ : syracuseStep 2672741 = 501139) (by norm_num)
theorem B2254969 : Blo 1780091 2254969 := bbase (se 2 (by rfl) ⟨845613, by rfl⟩ : syracuseStep 2254969 = 1691227) (by norm_num)
theorem B2672765 : Blo 1780091 2672765 := bbase (se 3 (by rfl) ⟨501143, by rfl⟩ : syracuseStep 2672765 = 1002287) (by norm_num)
theorem B4008077 : Blo 1780091 4008077 := bbase (se 3 (by rfl) ⟨751514, by rfl⟩ : syracuseStep 4008077 = 1503029) (by norm_num)
theorem B2672789 : Blo 1780091 2672789 := bbase (se 6 (by rfl) ⟨62643, by rfl⟩ : syracuseStep 2672789 = 125287) (by norm_num)
theorem B2672813 : Blo 1780091 2672813 := bbase (se 3 (by rfl) ⟨501152, by rfl⟩ : syracuseStep 2672813 = 1002305) (by norm_num)
theorem B1804465 : Blo 1780091 1804465 := bbase (se 2 (by rfl) ⟨676674, by rfl⟩ : syracuseStep 1804465 = 1353349) (by norm_num)
theorem B7604405 : Blo 1780091 7604405 := bbase (se 5 (by rfl) ⟨356456, by rfl⟩ : syracuseStep 7604405 = 712913) (by norm_num)
theorem B2672837 : Blo 1780091 2672837 := bbase (se 4 (by rfl) ⟨250578, by rfl⟩ : syracuseStep 2672837 = 501157) (by norm_num)
theorem B13519061 : Blo 1780091 13519061 := bbase (se 7 (by rfl) ⟨158426, by rfl⟩ : syracuseStep 13519061 = 316853) (by norm_num)
theorem B4008149 : Blo 1780091 4008149 := bbase (se 7 (by rfl) ⟨46970, by rfl⟩ : syracuseStep 4008149 = 93941) (by norm_num)
theorem B2672861 : Blo 1780091 2672861 := bbase (se 3 (by rfl) ⟨501161, by rfl⟩ : syracuseStep 2672861 = 1002323) (by norm_num)
theorem B2672885 : Blo 1780091 2672885 := bbase (se 5 (by rfl) ⟨125291, by rfl⟩ : syracuseStep 2672885 = 250583) (by norm_num)
theorem B1902857 : Blo 1780091 1902857 := bbase (se 2 (by rfl) ⟨713571, by rfl⟩ : syracuseStep 1902857 = 1427143) (by norm_num)
theorem B2672909 : Blo 1780091 2672909 := bbase (se 3 (by rfl) ⟨501170, by rfl⟩ : syracuseStep 2672909 = 1002341) (by norm_num)
theorem B4507933 : Blo 1780091 4507933 := bbase (se 3 (by rfl) ⟨845237, by rfl⟩ : syracuseStep 4507933 = 1690475) (by norm_num)
theorem B4008221 : Blo 1780091 4008221 := bbase (se 3 (by rfl) ⟨751541, by rfl⟩ : syracuseStep 4008221 = 1503083) (by norm_num)
theorem B2255141 : Blo 1780091 2255141 := bbase (se 4 (by rfl) ⟨211419, by rfl⟩ : syracuseStep 2255141 = 422839) (by norm_num)
theorem B2672933 : Blo 1780091 2672933 := bbase (se 4 (by rfl) ⟨250587, by rfl⟩ : syracuseStep 2672933 = 501175) (by norm_num)
theorem B2672957 : Blo 1780091 2672957 := bbase (se 3 (by rfl) ⟨501179, by rfl⟩ : syracuseStep 2672957 = 1002359) (by norm_num)
theorem B7317845 : Blo 1780091 7317845 := bbase (se 10 (by rfl) ⟨10719, by rfl⟩ : syracuseStep 7317845 = 21439) (by norm_num)
theorem B2672981 : Blo 1780091 2672981 := bbase (se 10 (by rfl) ⟨3915, by rfl⟩ : syracuseStep 2672981 = 7831) (by norm_num)
theorem B2255197 : Blo 1780091 2255197 := bbase (se 3 (by rfl) ⟨422849, by rfl⟩ : syracuseStep 2255197 = 845699) (by norm_num)
theorem B4008293 : Blo 1780091 4008293 := bbase (se 4 (by rfl) ⟨375777, by rfl⟩ : syracuseStep 4008293 = 751555) (by norm_num)
theorem B2673005 : Blo 1780091 2673005 := bbase (se 3 (by rfl) ⟨501188, by rfl⟩ : syracuseStep 2673005 = 1002377) (by norm_num)
theorem B2673029 : Blo 1780091 2673029 := bbase (se 4 (by rfl) ⟨250596, by rfl⟩ : syracuseStep 2673029 = 501193) (by norm_num)
theorem B4508045 : Blo 1780091 4508045 := bbase (se 3 (by rfl) ⟨845258, by rfl⟩ : syracuseStep 4508045 = 1690517) (by norm_num)
theorem B6760853 : Blo 1780091 6760853 := bbase (se 6 (by rfl) ⟨158457, by rfl⟩ : syracuseStep 6760853 = 316915) (by norm_num)
theorem B2140565 : Blo 1780091 2140565 := bbase (se 6 (by rfl) ⟨50169, by rfl⟩ : syracuseStep 2140565 = 100339) (by norm_num)
theorem B2673053 : Blo 1780091 2673053 := bbase (se 3 (by rfl) ⟨501197, by rfl⟩ : syracuseStep 2673053 = 1002395) (by norm_num)
theorem B5073317 : Blo 1780091 5073317 := bbase (se 4 (by rfl) ⟨475623, by rfl⟩ : syracuseStep 5073317 = 951247) (by norm_num)
theorem B4008365 : Blo 1780091 4008365 := bbase (se 3 (by rfl) ⟨751568, by rfl⟩ : syracuseStep 4008365 = 1503137) (by norm_num)
theorem B2673077 : Blo 1780091 2673077 := bbase (se 5 (by rfl) ⟨125300, by rfl⟩ : syracuseStep 2673077 = 250601) (by norm_num)
theorem B2255293 : Blo 1780091 2255293 := bbase (se 3 (by rfl) ⟨422867, by rfl⟩ : syracuseStep 2255293 = 845735) (by norm_num)
theorem B2673101 : Blo 1780091 2673101 := bbase (se 3 (by rfl) ⟨501206, by rfl⟩ : syracuseStep 2673101 = 1002413) (by norm_num)
theorem B21121493 : Blo 1780091 21121493 := bbase (se 7 (by rfl) ⟨247517, by rfl⟩ : syracuseStep 21121493 = 495035) (by norm_num)
theorem B2673125 : Blo 1780091 2673125 := bbase (se 4 (by rfl) ⟨250605, by rfl⟩ : syracuseStep 2673125 = 501211) (by norm_num)
theorem B4008437 : Blo 1780091 4008437 := bbase (se 5 (by rfl) ⟨187895, by rfl⟩ : syracuseStep 4008437 = 375791) (by norm_num)
theorem B4008509 : Blo 1780091 4008509 := bbase (se 3 (by rfl) ⟨751595, by rfl⟩ : syracuseStep 4008509 = 1503191) (by norm_num)
theorem B4508237 : Blo 1780091 4508237 := bbase (se 3 (by rfl) ⟨845294, by rfl⟩ : syracuseStep 4508237 = 1690589) (by norm_num)
theorem B2140777 : Blo 1780091 2140777 := bbase (se 2 (by rfl) ⟨802791, by rfl⟩ : syracuseStep 2140777 = 1605583) (by norm_num)
theorem B2853485 : Blo 1780091 2853485 := bbase (se 3 (by rfl) ⟨535028, by rfl⟩ : syracuseStep 2853485 = 1070057) (by norm_num)
theorem B4008581 : Blo 1780091 4008581 := bbase (se 4 (by rfl) ⟨375804, by rfl⟩ : syracuseStep 4008581 = 751609) (by norm_num)
theorem B6761141 : Blo 1780091 6761141 := bbase (se 5 (by rfl) ⟨316928, by rfl⟩ : syracuseStep 6761141 = 633857) (by norm_num)
theorem B4008653 : Blo 1780091 4008653 := bbase (se 3 (by rfl) ⟨751622, by rfl⟩ : syracuseStep 4008653 = 1503245) (by norm_num)
theorem B4278997 : Blo 1780091 4278997 := bbase (se 7 (by rfl) ⟨50144, by rfl⟩ : syracuseStep 4278997 = 100289) (by norm_num)
theorem B2140921 : Blo 1780091 2140921 := bbase (se 2 (by rfl) ⟨802845, by rfl⟩ : syracuseStep 2140921 = 1605691) (by norm_num)
theorem B4008725 : Blo 1780091 4008725 := bbase (se 6 (by rfl) ⟨93954, by rfl⟩ : syracuseStep 4008725 = 187909) (by norm_num)
theorem B2853677 : Blo 1780091 2853677 := bbase (se 3 (by rfl) ⟨535064, by rfl⟩ : syracuseStep 2853677 = 1070129) (by norm_num)
theorem B5073749 : Blo 1780091 5073749 := bbase (se 9 (by rfl) ⟨14864, by rfl⟩ : syracuseStep 5073749 = 29729) (by norm_num)
theorem B4008797 : Blo 1780091 4008797 := bbase (se 3 (by rfl) ⟨751649, by rfl⟩ : syracuseStep 4008797 = 1503299) (by norm_num)
theorem B3804013 : Blo 1780091 3804013 := bbase (se 3 (by rfl) ⟨713252, by rfl⟩ : syracuseStep 3804013 = 1426505) (by norm_num)
theorem B11406197 : Blo 1780091 11406197 := bbase (se 5 (by rfl) ⟨534665, by rfl⟩ : syracuseStep 11406197 = 1069331) (by norm_num)
theorem B9014165 : Blo 1780091 9014165 := bbase (se 6 (by rfl) ⟨211269, by rfl⟩ : syracuseStep 9014165 = 422539) (by norm_num)
theorem B4508581 : Blo 1780091 4508581 := bbase (se 4 (by rfl) ⟨422679, by rfl⟩ : syracuseStep 4508581 = 845359) (by norm_num)
theorem B4008869 : Blo 1780091 4008869 := bbase (se 4 (by rfl) ⟨375831, by rfl⟩ : syracuseStep 4008869 = 751663) (by norm_num)
theorem B2853805 : Blo 1780091 2853805 := bbase (se 3 (by rfl) ⟨535088, by rfl⟩ : syracuseStep 2853805 = 1070177) (by norm_num)
theorem B4008941 : Blo 1780091 4008941 := bbase (se 3 (by rfl) ⟨751676, by rfl⟩ : syracuseStep 4008941 = 1503353) (by norm_num)
theorem B12184597 : Blo 1780091 12184597 := bbase (se 6 (by rfl) ⟨285576, by rfl⟩ : syracuseStep 12184597 = 571153) (by norm_num)
theorem B4508693 : Blo 1780091 4508693 := bbase (se 6 (by rfl) ⟨105672, by rfl⟩ : syracuseStep 4508693 = 211345) (by norm_num)
theorem B1805365 : Blo 1780091 1805365 := bbase (se 5 (by rfl) ⟨84626, by rfl⟩ : syracuseStep 1805365 = 169253) (by norm_num)
theorem B4009013 : Blo 1780091 4009013 := bbase (se 5 (by rfl) ⟨187922, by rfl⟩ : syracuseStep 4009013 = 375845) (by norm_num)
theorem B6007877 : Blo 1780091 6007877 := bbase (se 4 (by rfl) ⟨563238, by rfl⟩ : syracuseStep 6007877 = 1126477) (by norm_num)
theorem B4009085 : Blo 1780091 4009085 := bbase (se 3 (by rfl) ⟨751703, by rfl⟩ : syracuseStep 4009085 = 1503407) (by norm_num)
theorem B4009157 : Blo 1780091 4009157 := bbase (se 4 (by rfl) ⟨375858, by rfl⟩ : syracuseStep 4009157 = 751717) (by norm_num)
theorem B4508885 : Blo 1780091 4508885 := bbase (se 7 (by rfl) ⟨52838, by rfl⟩ : syracuseStep 4508885 = 105677) (by norm_num)
theorem B4009229 : Blo 1780091 4009229 := bbase (se 3 (by rfl) ⟨751730, by rfl⟩ : syracuseStep 4009229 = 1503461) (by norm_num)
theorem B4009301 : Blo 1780091 4009301 := bbase (se 11 (by rfl) ⟨2936, by rfl⟩ : syracuseStep 4009301 = 5873) (by norm_num)
theorem B3804509 : Blo 1780091 3804509 := bbase (se 3 (by rfl) ⟨713345, by rfl⟩ : syracuseStep 3804509 = 1426691) (by norm_num)
theorem B10833301 : Blo 1780091 10833301 := bbase (se 6 (by rfl) ⟨253905, by rfl⟩ : syracuseStep 10833301 = 507811) (by norm_num)
theorem B4279709 : Blo 1780091 4279709 := bbase (se 3 (by rfl) ⟨802445, by rfl⟩ : syracuseStep 4279709 = 1604891) (by norm_num)
theorem B4009373 : Blo 1780091 4009373 := bbase (se 3 (by rfl) ⟨751757, by rfl⟩ : syracuseStep 4009373 = 1503515) (by norm_num)
theorem B4009445 : Blo 1780091 4009445 := bbase (se 4 (by rfl) ⟨375885, by rfl⟩ : syracuseStep 4009445 = 751771) (by norm_num)
theorem B6008309 : Blo 1780091 6008309 := bbase (se 5 (by rfl) ⟨281639, by rfl⟩ : syracuseStep 6008309 = 563279) (by norm_num)
theorem B1928729 : Blo 1780091 1928729 := bbase (se 2 (by rfl) ⟨723273, by rfl⟩ : syracuseStep 1928729 = 1446547) (by norm_num)
theorem B4509229 : Blo 1780091 4509229 := bbase (se 3 (by rfl) ⟨845480, by rfl⟩ : syracuseStep 4509229 = 1690961) (by norm_num)
theorem B4009517 : Blo 1780091 4009517 := bbase (se 3 (by rfl) ⟨751784, by rfl⟩ : syracuseStep 4009517 = 1503569) (by norm_num)
theorem B2854445 : Blo 1780091 2854445 := bbase (se 3 (by rfl) ⟨535208, by rfl⟩ : syracuseStep 2854445 = 1070417) (by norm_num)
theorem B2707013 : Blo 1780091 2707013 := bbase (se 4 (by rfl) ⟨253782, by rfl⟩ : syracuseStep 2707013 = 507565) (by norm_num)
theorem B5074501 : Blo 1780091 5074501 := bbase (se 4 (by rfl) ⟨475734, by rfl⟩ : syracuseStep 5074501 = 951469) (by norm_num)
theorem B4009589 : Blo 1780091 4009589 := bbase (se 5 (by rfl) ⟨187949, by rfl⟩ : syracuseStep 4009589 = 375899) (by norm_num)
theorem B4509341 : Blo 1780091 4509341 := bbase (se 3 (by rfl) ⟨845501, by rfl⟩ : syracuseStep 4509341 = 1691003) (by norm_num)
theorem B1805981 : Blo 1780091 1805981 := bbase (se 3 (by rfl) ⟨338621, by rfl⟩ : syracuseStep 1805981 = 677243) (by norm_num)
theorem B2002621 : Blo 1780091 2002621 := bbase (se 3 (by rfl) ⟨375491, by rfl⟩ : syracuseStep 2002621 = 750983) (by norm_num)
theorem B4009661 : Blo 1780091 4009661 := bbase (se 3 (by rfl) ⟨751811, by rfl⟩ : syracuseStep 4009661 = 1503623) (by norm_num)
theorem B2002657 : Blo 1780091 2002657 := bbase (se 2 (by rfl) ⟨750996, by rfl⟩ : syracuseStep 2002657 = 1501993) (by norm_num)
theorem B2002693 : Blo 1780091 2002693 := bbase (se 4 (by rfl) ⟨187752, by rfl⟩ : syracuseStep 2002693 = 375505) (by norm_num)
theorem B14634773 : Blo 1780091 14634773 := bbase (se 6 (by rfl) ⟨343002, by rfl⟩ : syracuseStep 14634773 = 686005) (by norm_num)
theorem B4280093 : Blo 1780091 4280093 := bbase (se 3 (by rfl) ⟨802517, by rfl⟩ : syracuseStep 4280093 = 1605035) (by norm_num)
theorem B2002729 : Blo 1780091 2002729 := bbase (se 2 (by rfl) ⟨751023, by rfl⟩ : syracuseStep 2002729 = 1502047) (by norm_num)
theorem B2535229 : Blo 1780091 2535229 := bbase (se 3 (by rfl) ⟨475355, by rfl⟩ : syracuseStep 2535229 = 950711) (by norm_num)
theorem B2002765 : Blo 1780091 2002765 := bbase (se 3 (by rfl) ⟨375518, by rfl⟩ : syracuseStep 2002765 = 751037) (by norm_num)
theorem B6762325 : Blo 1780091 6762325 := bbase (se 9 (by rfl) ⟨19811, by rfl⟩ : syracuseStep 6762325 = 39623) (by norm_num)
theorem B4509533 : Blo 1780091 4509533 := bbase (se 3 (by rfl) ⟨845537, by rfl⟩ : syracuseStep 4509533 = 1691075) (by norm_num)
theorem B2002801 : Blo 1780091 2002801 := bbase (se 2 (by rfl) ⟨751050, by rfl⟩ : syracuseStep 2002801 = 1502101) (by norm_num)
theorem B2002837 : Blo 1780091 2002837 := bbase (se 6 (by rfl) ⟨46941, by rfl⟩ : syracuseStep 2002837 = 93883) (by norm_num)
theorem B6008741 : Blo 1780091 6008741 := bbase (se 4 (by rfl) ⟨563319, by rfl⟩ : syracuseStep 6008741 = 1126639) (by norm_num)
theorem B4812725 : Blo 1780091 4812725 := bbase (se 5 (by rfl) ⟨225596, by rfl⟩ : syracuseStep 4812725 = 451193) (by norm_num)
theorem B2002873 : Blo 1780091 2002873 := bbase (se 2 (by rfl) ⟨751077, by rfl⟩ : syracuseStep 2002873 = 1502155) (by norm_num)
theorem B2002909 : Blo 1780091 2002909 := bbase (se 3 (by rfl) ⟨375545, by rfl⟩ : syracuseStep 2002909 = 751091) (by norm_num)
theorem B2002945 : Blo 1780091 2002945 := bbase (se 2 (by rfl) ⟨751104, by rfl⟩ : syracuseStep 2002945 = 1502209) (by norm_num)
theorem B6418453 : Blo 1780091 6418453 := bbase (se 6 (by rfl) ⟨150432, by rfl⟩ : syracuseStep 6418453 = 300865) (by norm_num)
theorem B2002981 : Blo 1780091 2002981 := bbase (se 4 (by rfl) ⟨187779, by rfl⟩ : syracuseStep 2002981 = 375559) (by norm_num)
theorem B5705765 : Blo 1780091 5705765 := bbase (se 4 (by rfl) ⟨534915, by rfl⟩ : syracuseStep 5705765 = 1069831) (by norm_num)
theorem B1855529 : Blo 1780091 1855529 := bbase (se 2 (by rfl) ⟨695823, by rfl⟩ : syracuseStep 1855529 = 1391647) (by norm_num)
theorem B4280381 : Blo 1780091 4280381 := bbase (se 3 (by rfl) ⟨802571, by rfl⟩ : syracuseStep 4280381 = 1605143) (by norm_num)
theorem B2003017 : Blo 1780091 2003017 := bbase (se 2 (by rfl) ⟨751131, by rfl⟩ : syracuseStep 2003017 = 1502263) (by norm_num)
theorem B2003053 : Blo 1780091 2003053 := bbase (se 3 (by rfl) ⟨375572, by rfl⟩ : syracuseStep 2003053 = 751145) (by norm_num)
theorem B6762629 : Blo 1780091 6762629 := bbase (se 4 (by rfl) ⟨633996, by rfl⟩ : syracuseStep 6762629 = 1267993) (by norm_num)
theorem B3854477 : Blo 1780091 3854477 := bbase (se 3 (by rfl) ⟨722714, by rfl⟩ : syracuseStep 3854477 = 1445429) (by norm_num)
theorem B2535565 : Blo 1780091 2535565 := bbase (se 3 (by rfl) ⟨475418, by rfl⟩ : syracuseStep 2535565 = 950837) (by norm_num)
theorem B2003089 : Blo 1780091 2003089 := bbase (se 2 (by rfl) ⟨751158, by rfl⟩ : syracuseStep 2003089 = 1502317) (by norm_num)
theorem B9015461 : Blo 1780091 9015461 := bbase (se 4 (by rfl) ⟨845199, by rfl⟩ : syracuseStep 9015461 = 1690399) (by norm_num)
theorem B2003125 : Blo 1780091 2003125 := bbase (se 5 (by rfl) ⟨93896, by rfl⟩ : syracuseStep 2003125 = 187793) (by norm_num)
theorem B4509877 : Blo 1780091 4509877 := bbase (se 5 (by rfl) ⟨211400, by rfl⟩ : syracuseStep 4509877 = 422801) (by norm_num)
theorem B3805373 : Blo 1780091 3805373 := bbase (se 3 (by rfl) ⟨713507, by rfl⟩ : syracuseStep 3805373 = 1427015) (by norm_num)
theorem B2003161 : Blo 1780091 2003161 := bbase (se 2 (by rfl) ⟨751185, by rfl⟩ : syracuseStep 2003161 = 1502371) (by norm_num)
theorem B2003197 : Blo 1780091 2003197 := bbase (se 3 (by rfl) ⟨375599, by rfl⟩ : syracuseStep 2003197 = 751199) (by norm_num)
theorem B3379477 : Blo 1780091 3379477 := bbase (se 6 (by rfl) ⟨79206, by rfl⟩ : syracuseStep 3379477 = 158413) (by norm_num)
theorem B8679701 : Blo 1780091 8679701 := bbase (se 6 (by rfl) ⟨203430, by rfl⟩ : syracuseStep 8679701 = 406861) (by norm_num)
theorem B2003233 : Blo 1780091 2003233 := bbase (se 2 (by rfl) ⟨751212, by rfl⟩ : syracuseStep 2003233 = 1502425) (by norm_num)
theorem B4509989 : Blo 1780091 4509989 := bbase (se 4 (by rfl) ⟨422811, by rfl⟩ : syracuseStep 4509989 = 845623) (by norm_num)
theorem B12185909 : Blo 1780091 12185909 := bbase (se 5 (by rfl) ⟨571214, by rfl⟩ : syracuseStep 12185909 = 1142429) (by norm_num)
theorem B2003269 : Blo 1780091 2003269 := bbase (se 4 (by rfl) ⟨187806, by rfl⟩ : syracuseStep 2003269 = 375613) (by norm_num)
theorem B4116805 : Blo 1780091 4116805 := bbase (se 4 (by rfl) ⟨385950, by rfl⟩ : syracuseStep 4116805 = 771901) (by norm_num)
theorem B3805517 : Blo 1780091 3805517 := bbase (se 3 (by rfl) ⟨713534, by rfl⟩ : syracuseStep 3805517 = 1427069) (by norm_num)
theorem B6009173 : Blo 1780091 6009173 := bbase (se 10 (by rfl) ⟨8802, by rfl⟩ : syracuseStep 6009173 = 17605) (by norm_num)
theorem B2535781 : Blo 1780091 2535781 := bbase (se 4 (by rfl) ⟨237729, by rfl⟩ : syracuseStep 2535781 = 475459) (by norm_num)
theorem B2003305 : Blo 1780091 2003305 := bbase (se 2 (by rfl) ⟨751239, by rfl⟩ : syracuseStep 2003305 = 1502479) (by norm_num)
theorem B2003341 : Blo 1780091 2003341 := bbase (se 3 (by rfl) ⟨375626, by rfl⟩ : syracuseStep 2003341 = 751253) (by norm_num)
theorem B3658133 : Blo 1780091 3658133 := bbase (se 6 (by rfl) ⟨85737, by rfl⟩ : syracuseStep 3658133 = 171475) (by norm_num)
theorem B2003377 : Blo 1780091 2003377 := bbase (se 2 (by rfl) ⟨751266, by rfl⟩ : syracuseStep 2003377 = 1502533) (by norm_num)
theorem B3379637 : Blo 1780091 3379637 := bbase (se 5 (by rfl) ⟨158420, by rfl⟩ : syracuseStep 3379637 = 316841) (by norm_num)
theorem B2003413 : Blo 1780091 2003413 := bbase (se 7 (by rfl) ⟨23477, by rfl⟩ : syracuseStep 2003413 = 46955) (by norm_num)
theorem B4510181 : Blo 1780091 4510181 := bbase (se 4 (by rfl) ⟨422829, by rfl⟩ : syracuseStep 4510181 = 845659) (by norm_num)
theorem B2003449 : Blo 1780091 2003449 := bbase (se 2 (by rfl) ⟨751293, by rfl⟩ : syracuseStep 2003449 = 1502587) (by norm_num)
theorem B15430165 : Blo 1780091 15430165 := bbase (se 6 (by rfl) ⟨361644, by rfl⟩ : syracuseStep 15430165 = 723289) (by norm_num)
theorem B2003485 : Blo 1780091 2003485 := bbase (se 3 (by rfl) ⟨375653, by rfl⟩ : syracuseStep 2003485 = 751307) (by norm_num)
theorem B8557109 : Blo 1780091 8557109 := bbase (se 5 (by rfl) ⟨401114, by rfl⟩ : syracuseStep 8557109 = 802229) (by norm_num)
theorem B2003521 : Blo 1780091 2003521 := bbase (se 2 (by rfl) ⟨751320, by rfl⟩ : syracuseStep 2003521 = 1502641) (by norm_num)
theorem B3379781 : Blo 1780091 3379781 := bbase (se 4 (by rfl) ⟨316854, by rfl⟩ : syracuseStep 3379781 = 633709) (by norm_num)
theorem B2003557 : Blo 1780091 2003557 := bbase (se 4 (by rfl) ⟨187833, by rfl⟩ : syracuseStep 2003557 = 375667) (by norm_num)
theorem B2003593 : Blo 1780091 2003593 := bbase (se 2 (by rfl) ⟨751347, by rfl⟩ : syracuseStep 2003593 = 1502695) (by norm_num)
theorem B2003629 : Blo 1780091 2003629 := bbase (se 3 (by rfl) ⟨375680, by rfl⟩ : syracuseStep 2003629 = 751361) (by norm_num)
theorem B2003665 : Blo 1780091 2003665 := bbase (se 2 (by rfl) ⟨751374, by rfl⟩ : syracuseStep 2003665 = 1502749) (by norm_num)
theorem B2536157 : Blo 1780091 2536157 := bbase (se 3 (by rfl) ⟨475529, by rfl⟩ : syracuseStep 2536157 = 951059) (by norm_num)
theorem B2003701 : Blo 1780091 2003701 := bbase (se 5 (by rfl) ⟨93923, by rfl⟩ : syracuseStep 2003701 = 187847) (by norm_num)
theorem B6009605 : Blo 1780091 6009605 := bbase (se 4 (by rfl) ⟨563400, by rfl⟩ : syracuseStep 6009605 = 1126801) (by norm_num)
theorem B2003737 : Blo 1780091 2003737 := bbase (se 2 (by rfl) ⟨751401, by rfl⟩ : syracuseStep 2003737 = 1502803) (by norm_num)
theorem B5706533 : Blo 1780091 5706533 := bbase (se 4 (by rfl) ⟨534987, by rfl⟩ : syracuseStep 5706533 = 1069975) (by norm_num)
theorem B2003773 : Blo 1780091 2003773 := bbase (se 3 (by rfl) ⟨375707, by rfl⟩ : syracuseStep 2003773 = 751415) (by norm_num)
theorem B4510525 : Blo 1780091 4510525 := bbase (se 3 (by rfl) ⟨845723, by rfl⟩ : syracuseStep 4510525 = 1691447) (by norm_num)
theorem B2003809 : Blo 1780091 2003809 := bbase (se 2 (by rfl) ⟨751428, by rfl⟩ : syracuseStep 2003809 = 1502857) (by norm_num)
theorem B3380069 : Blo 1780091 3380069 := bbase (se 4 (by rfl) ⟨316881, by rfl⟩ : syracuseStep 3380069 = 633763) (by norm_num)
theorem B2003845 : Blo 1780091 2003845 := bbase (se 4 (by rfl) ⟨187860, by rfl⟩ : syracuseStep 2003845 = 375721) (by norm_num)
theorem B2003881 : Blo 1780091 2003881 := bbase (se 2 (by rfl) ⟨751455, by rfl⟩ : syracuseStep 2003881 = 1502911) (by norm_num)
theorem B4510637 : Blo 1780091 4510637 := bbase (se 3 (by rfl) ⟨845744, by rfl⟩ : syracuseStep 4510637 = 1691489) (by norm_num)
theorem B2003917 : Blo 1780091 2003917 := bbase (se 3 (by rfl) ⟨375734, by rfl⟩ : syracuseStep 2003917 = 751469) (by norm_num)
theorem B6853589 : Blo 1780091 6853589 := bbase (se 7 (by rfl) ⟨80315, by rfl⟩ : syracuseStep 6853589 = 160631) (by norm_num)
theorem B2003953 : Blo 1780091 2003953 := bbase (se 2 (by rfl) ⟨751482, by rfl⟩ : syracuseStep 2003953 = 1502965) (by norm_num)
theorem B3208189 : Blo 1780091 3208189 := bbase (se 3 (by rfl) ⟨601535, by rfl⟩ : syracuseStep 3208189 = 1203071) (by norm_num)
theorem B3380221 : Blo 1780091 3380221 := bbase (se 3 (by rfl) ⟨633791, by rfl⟩ : syracuseStep 3380221 = 1267583) (by norm_num)
theorem B2003989 : Blo 1780091 2003989 := bbase (se 6 (by rfl) ⟨46968, by rfl⟩ : syracuseStep 2003989 = 93937) (by norm_num)
theorem B2004025 : Blo 1780091 2004025 := bbase (se 2 (by rfl) ⟨751509, by rfl⟩ : syracuseStep 2004025 = 1503019) (by norm_num)
theorem B2004061 : Blo 1780091 2004061 := bbase (se 3 (by rfl) ⟨375761, by rfl⟩ : syracuseStep 2004061 = 751523) (by norm_num)
theorem B4510829 : Blo 1780091 4510829 := bbase (se 3 (by rfl) ⟨845780, by rfl⟩ : syracuseStep 4510829 = 1691561) (by norm_num)
theorem B12833909 : Blo 1780091 12833909 := bbase (se 5 (by rfl) ⟨601589, by rfl⟩ : syracuseStep 12833909 = 1203179) (by norm_num)
theorem B15045749 : Blo 1780091 15045749 := bbase (se 5 (by rfl) ⟨705269, by rfl⟩ : syracuseStep 15045749 = 1410539) (by norm_num)
theorem B2004097 : Blo 1780091 2004097 := bbase (se 2 (by rfl) ⟨751536, by rfl⟩ : syracuseStep 2004097 = 1503073) (by norm_num)
theorem B2004133 : Blo 1780091 2004133 := bbase (se 4 (by rfl) ⟨187887, by rfl⟩ : syracuseStep 2004133 = 375775) (by norm_num)
theorem B6010037 : Blo 1780091 6010037 := bbase (se 5 (by rfl) ⟨281720, by rfl⟩ : syracuseStep 6010037 = 563441) (by norm_num)
theorem B2004169 : Blo 1780091 2004169 := bbase (se 2 (by rfl) ⟨751563, by rfl⟩ : syracuseStep 2004169 = 1503127) (by norm_num)
theorem B2004205 : Blo 1780091 2004205 := bbase (se 3 (by rfl) ⟨375788, by rfl⟩ : syracuseStep 2004205 = 751577) (by norm_num)
theorem B2004241 : Blo 1780091 2004241 := bbase (se 2 (by rfl) ⟨751590, by rfl⟩ : syracuseStep 2004241 = 1503181) (by norm_num)
theorem B3855637 : Blo 1780091 3855637 := bbase (se 6 (by rfl) ⟨90366, by rfl⟩ : syracuseStep 3855637 = 180733) (by norm_num)
theorem B5707045 : Blo 1780091 5707045 := bbase (se 4 (by rfl) ⟨535035, by rfl⟩ : syracuseStep 5707045 = 1070071) (by norm_num)
theorem B3380525 : Blo 1780091 3380525 := bbase (se 3 (by rfl) ⟨633848, by rfl⟩ : syracuseStep 3380525 = 1267697) (by norm_num)
theorem B5862709 : Blo 1780091 5862709 := bbase (se 5 (by rfl) ⟨274814, by rfl⟩ : syracuseStep 5862709 = 549629) (by norm_num)
theorem B2004277 : Blo 1780091 2004277 := bbase (se 5 (by rfl) ⟨93950, by rfl⟩ : syracuseStep 2004277 = 187901) (by norm_num)
theorem B2004313 : Blo 1780091 2004313 := bbase (se 2 (by rfl) ⟨751617, by rfl⟩ : syracuseStep 2004313 = 1503235) (by norm_num)
theorem B4568413 : Blo 1780091 4568413 := bbase (se 3 (by rfl) ⟨856577, by rfl⟩ : syracuseStep 4568413 = 1713155) (by norm_num)
theorem B2004349 : Blo 1780091 2004349 := bbase (se 3 (by rfl) ⟨375815, by rfl⟩ : syracuseStep 2004349 = 751631) (by norm_num)
theorem B2004385 : Blo 1780091 2004385 := bbase (se 2 (by rfl) ⟨751644, by rfl⟩ : syracuseStep 2004385 = 1503289) (by norm_num)
theorem B9016757 : Blo 1780091 9016757 := bbase (se 5 (by rfl) ⟨422660, by rfl⟩ : syracuseStep 9016757 = 845321) (by norm_num)
theorem B2004421 : Blo 1780091 2004421 := bbase (se 4 (by rfl) ⟨187914, by rfl⟩ : syracuseStep 2004421 = 375829) (by norm_num)
theorem B10139093 : Blo 1780091 10139093 := bbase (se 7 (by rfl) ⟨118817, by rfl⟩ : syracuseStep 10139093 = 237635) (by norm_num)
theorem B2004457 : Blo 1780091 2004457 := bbase (se 2 (by rfl) ⟨751671, by rfl⟩ : syracuseStep 2004457 = 1503343) (by norm_num)
theorem B2004493 : Blo 1780091 2004493 := bbase (se 3 (by rfl) ⟨375842, by rfl⟩ : syracuseStep 2004493 = 751685) (by norm_num)
theorem B3003925 : Blo 1780091 3003925 := bbase (se 6 (by rfl) ⟨70404, by rfl⟩ : syracuseStep 3003925 = 140809) (by norm_num)
theorem B2004529 : Blo 1780091 2004529 := bbase (se 2 (by rfl) ⟨751698, by rfl⟩ : syracuseStep 2004529 = 1503397) (by norm_num)
theorem B2004565 : Blo 1780091 2004565 := bbase (se 8 (by rfl) ⟨11745, by rfl⟩ : syracuseStep 2004565 = 23491) (by norm_num)
theorem B6010469 : Blo 1780091 6010469 := bbase (se 4 (by rfl) ⟨563481, by rfl⟩ : syracuseStep 6010469 = 1126963) (by norm_num)
theorem B3004013 : Blo 1780091 3004013 := bbase (se 3 (by rfl) ⟨563252, by rfl⟩ : syracuseStep 3004013 = 1126505) (by norm_num)
theorem B2004601 : Blo 1780091 2004601 := bbase (se 2 (by rfl) ⟨751725, by rfl⟩ : syracuseStep 2004601 = 1503451) (by norm_num)
theorem B3208829 : Blo 1780091 3208829 := bbase (se 3 (by rfl) ⟨601655, by rfl⟩ : syracuseStep 3208829 = 1203311) (by norm_num)
theorem B2004637 : Blo 1780091 2004637 := bbase (se 3 (by rfl) ⟨375869, by rfl⟩ : syracuseStep 2004637 = 751739) (by norm_num)
theorem B2004673 : Blo 1780091 2004673 := bbase (se 2 (by rfl) ⟨751752, by rfl⟩ : syracuseStep 2004673 = 1503505) (by norm_num)
theorem B2004709 : Blo 1780091 2004709 := bbase (se 4 (by rfl) ⟨187941, by rfl⟩ : syracuseStep 2004709 = 375883) (by norm_num)
theorem B3004141 : Blo 1780091 3004141 := bbase (se 3 (by rfl) ⟨563276, by rfl⟩ : syracuseStep 3004141 = 1126553) (by norm_num)
theorem B2709245 : Blo 1780091 2709245 := bbase (se 3 (by rfl) ⟨507983, by rfl⟩ : syracuseStep 2709245 = 1015967) (by norm_num)
theorem B2004745 : Blo 1780091 2004745 := bbase (se 2 (by rfl) ⟨751779, by rfl⟩ : syracuseStep 2004745 = 1503559) (by norm_num)
theorem B12515093 : Blo 1780091 12515093 := bbase (se 6 (by rfl) ⟨293322, by rfl⟩ : syracuseStep 12515093 = 586645) (by norm_num)
theorem B7714597 : Blo 1780091 7714597 := bbase (se 4 (by rfl) ⟨723243, by rfl⟩ : syracuseStep 7714597 = 1446487) (by norm_num)
theorem B2004781 : Blo 1780091 2004781 := bbase (se 3 (by rfl) ⟨375896, by rfl⟩ : syracuseStep 2004781 = 751793) (by norm_num)
theorem B3004229 : Blo 1780091 3004229 := bbase (se 4 (by rfl) ⟨281646, by rfl⟩ : syracuseStep 3004229 = 563293) (by norm_num)
theorem B2004817 : Blo 1780091 2004817 := bbase (se 2 (by rfl) ⟨751806, by rfl⟩ : syracuseStep 2004817 = 1503613) (by norm_num)
theorem B3610453 : Blo 1780091 3610453 := bbase (se 9 (by rfl) ⟨10577, by rfl⟩ : syracuseStep 3610453 = 21155) (by norm_num)
theorem B4061029 : Blo 1780091 4061029 := bbase (se 4 (by rfl) ⟨380721, by rfl⟩ : syracuseStep 4061029 = 761443) (by norm_num)
theorem B2004853 : Blo 1780091 2004853 := bbase (se 5 (by rfl) ⟨93977, by rfl⟩ : syracuseStep 2004853 = 187955) (by norm_num)
theorem B2709397 : Blo 1780091 2709397 := bbase (se 6 (by rfl) ⟨63501, by rfl⟩ : syracuseStep 2709397 = 127003) (by norm_num)
theorem B3004357 : Blo 1780091 3004357 := bbase (se 4 (by rfl) ⟨281658, by rfl⟩ : syracuseStep 3004357 = 563317) (by norm_num)
theorem B2406341 : Blo 1780091 2406341 := bbase (se 4 (by rfl) ⟨225594, by rfl⟩ : syracuseStep 2406341 = 451189) (by norm_num)
theorem B2709469 : Blo 1780091 2709469 := bbase (se 3 (by rfl) ⟨508025, by rfl⟩ : syracuseStep 2709469 = 1016051) (by norm_num)
theorem B6420485 : Blo 1780091 6420485 := bbase (se 4 (by rfl) ⟨601920, by rfl⟩ : syracuseStep 6420485 = 1203841) (by norm_num)
theorem B6010901 : Blo 1780091 6010901 := bbase (se 6 (by rfl) ⟨140880, by rfl⟩ : syracuseStep 6010901 = 281761) (by norm_num)
theorem B3004445 : Blo 1780091 3004445 := bbase (se 3 (by rfl) ⟨563333, by rfl⟩ : syracuseStep 3004445 = 1126667) (by norm_num)
theorem B3381277 : Blo 1780091 3381277 := bbase (se 3 (by rfl) ⟨633989, by rfl⟩ : syracuseStep 3381277 = 1267979) (by norm_num)
theorem B7608437 : Blo 1780091 7608437 := bbase (se 5 (by rfl) ⟨356645, by rfl⟩ : syracuseStep 7608437 = 713291) (by norm_num)
theorem B3004573 : Blo 1780091 3004573 := bbase (se 3 (by rfl) ⟨563357, by rfl⟩ : syracuseStep 3004573 = 1126715) (by norm_num)
theorem B4569253 : Blo 1780091 4569253 := bbase (se 4 (by rfl) ⟨428367, by rfl⟩ : syracuseStep 4569253 = 856735) (by norm_num)
theorem B3381421 : Blo 1780091 3381421 := bbase (se 3 (by rfl) ⟨634016, by rfl⟩ : syracuseStep 3381421 = 1268033) (by norm_num)
theorem B2283709 : Blo 1780091 2283709 := bbase (se 3 (by rfl) ⟨428195, by rfl⟩ : syracuseStep 2283709 = 856391) (by norm_num)
theorem B6764741 : Blo 1780091 6764741 := bbase (se 4 (by rfl) ⟨634194, by rfl⟩ : syracuseStep 6764741 = 1268389) (by norm_num)
theorem B2316493 : Blo 1780091 2316493 := bbase (se 3 (by rfl) ⟨434342, by rfl⟩ : syracuseStep 2316493 = 868685) (by norm_num)
theorem B66771157 : Blo 1780091 66771157 := bbase (se 7 (by rfl) ⟨782474, by rfl⟩ : syracuseStep 66771157 = 1564949) (by norm_num)
theorem B17832149 : Blo 1780091 17832149 := bbase (se 7 (by rfl) ⟨208970, by rfl⟩ : syracuseStep 17832149 = 417941) (by norm_num)
theorem B3004661 : Blo 1780091 3004661 := bbase (se 5 (by rfl) ⟨140843, by rfl⟩ : syracuseStep 3004661 = 281687) (by norm_num)
theorem B3381581 : Blo 1780091 3381581 := bbase (se 3 (by rfl) ⟨634046, by rfl⟩ : syracuseStep 3381581 = 1268093) (by norm_num)
theorem B3004789 : Blo 1780091 3004789 := bbase (se 5 (by rfl) ⟨140849, by rfl⟩ : syracuseStep 3004789 = 281699) (by norm_num)
theorem B3611069 : Blo 1780091 3611069 := bbase (se 3 (by rfl) ⟨677075, by rfl⟩ : syracuseStep 3611069 = 1354151) (by norm_num)
theorem B6011333 : Blo 1780091 6011333 := bbase (se 4 (by rfl) ⟨563562, by rfl⟩ : syracuseStep 6011333 = 1127125) (by norm_num)
theorem B3004877 : Blo 1780091 3004877 := bbase (se 3 (by rfl) ⟨563414, by rfl⟩ : syracuseStep 3004877 = 1126829) (by norm_num)
theorem B3381725 : Blo 1780091 3381725 := bbase (se 3 (by rfl) ⟨634073, by rfl⟩ : syracuseStep 3381725 = 1268147) (by norm_num)
theorem B6765029 : Blo 1780091 6765029 := bbase (se 4 (by rfl) ⟨634221, by rfl⟩ : syracuseStep 6765029 = 1268443) (by norm_num)
theorem B3005005 : Blo 1780091 3005005 := bbase (se 3 (by rfl) ⟨563438, by rfl⟩ : syracuseStep 3005005 = 1126877) (by norm_num)
theorem B3005093 : Blo 1780091 3005093 := bbase (se 4 (by rfl) ⟨281727, by rfl⟩ : syracuseStep 3005093 = 563455) (by norm_num)
theorem B8125109 : Blo 1780091 8125109 := bbase (se 5 (by rfl) ⟨380864, by rfl⟩ : syracuseStep 8125109 = 761729) (by norm_num)
theorem B2030269 : Blo 1780091 2030269 := bbase (se 3 (by rfl) ⟨380675, by rfl⟩ : syracuseStep 2030269 = 761351) (by norm_num)
theorem B9018053 : Blo 1780091 9018053 := bbase (se 4 (by rfl) ⟨845442, by rfl⟩ : syracuseStep 9018053 = 1690885) (by norm_num)
theorem B2407141 : Blo 1780091 2407141 := bbase (se 4 (by rfl) ⟨225669, by rfl⟩ : syracuseStep 2407141 = 451339) (by norm_num)
theorem B5069557 : Blo 1780091 5069557 := bbase (se 5 (by rfl) ⟨237635, by rfl⟩ : syracuseStep 5069557 = 475271) (by norm_num)
theorem B3382013 : Blo 1780091 3382013 := bbase (se 3 (by rfl) ⟨634127, by rfl⟩ : syracuseStep 3382013 = 1268255) (by norm_num)
theorem B3005221 : Blo 1780091 3005221 := bbase (se 4 (by rfl) ⟨281739, by rfl⟩ : syracuseStep 3005221 = 563479) (by norm_num)
theorem B7322453 : Blo 1780091 7322453 := bbase (se 9 (by rfl) ⟨21452, by rfl⟩ : syracuseStep 7322453 = 42905) (by norm_num)
theorem B6421349 : Blo 1780091 6421349 := bbase (se 4 (by rfl) ⟨602001, by rfl⟩ : syracuseStep 6421349 = 1204003) (by norm_num)
theorem B6011765 : Blo 1780091 6011765 := bbase (se 5 (by rfl) ⟨281801, by rfl⟩ : syracuseStep 6011765 = 563603) (by norm_num)
theorem B3005309 : Blo 1780091 3005309 := bbase (se 3 (by rfl) ⟨563495, by rfl⟩ : syracuseStep 3005309 = 1126991) (by norm_num)
theorem B3382165 : Blo 1780091 3382165 := bbase (se 6 (by rfl) ⟨79269, by rfl⟩ : syracuseStep 3382165 = 158539) (by norm_num)
theorem B3210149 : Blo 1780091 3210149 := bbase (se 4 (by rfl) ⟨300951, by rfl⟩ : syracuseStep 3210149 = 601903) (by norm_num)
theorem B3046349 : Blo 1780091 3046349 := bbase (se 3 (by rfl) ⟨571190, by rfl⟩ : syracuseStep 3046349 = 1142381) (by norm_num)
theorem B5708789 : Blo 1780091 5708789 := bbase (se 5 (by rfl) ⟨267599, by rfl⟩ : syracuseStep 5708789 = 535199) (by norm_num)
theorem B3005437 : Blo 1780091 3005437 := bbase (se 3 (by rfl) ⟨563519, by rfl⟩ : syracuseStep 3005437 = 1127039) (by norm_num)
theorem B3611677 : Blo 1780091 3611677 := bbase (se 3 (by rfl) ⟨677189, by rfl⟩ : syracuseStep 3611677 = 1354379) (by norm_num)
theorem B3005525 : Blo 1780091 3005525 := bbase (se 8 (by rfl) ⟨17610, by rfl⟩ : syracuseStep 3005525 = 35221) (by norm_num)
theorem B17112181 : Blo 1780091 17112181 := bbase (se 5 (by rfl) ⟨802133, by rfl⟩ : syracuseStep 17112181 = 1604267) (by norm_num)
theorem B9624757 : Blo 1780091 9624757 := bbase (se 5 (by rfl) ⟨451160, by rfl⟩ : syracuseStep 9624757 = 902321) (by norm_num)
theorem B5708981 : Blo 1780091 5708981 := bbase (se 5 (by rfl) ⟨267608, by rfl⟩ : syracuseStep 5708981 = 535217) (by norm_num)
theorem B2030789 : Blo 1780091 2030789 := bbase (se 4 (by rfl) ⟨190386, by rfl⟩ : syracuseStep 2030789 = 380773) (by norm_num)
theorem B3382469 : Blo 1780091 3382469 := bbase (se 4 (by rfl) ⟨317106, by rfl⟩ : syracuseStep 3382469 = 634213) (by norm_num)
theorem B3005653 : Blo 1780091 3005653 := bbase (se 7 (by rfl) ⟨35222, by rfl⟩ : syracuseStep 3005653 = 70445) (by norm_num)
theorem B8559877 : Blo 1780091 8559877 := bbase (se 4 (by rfl) ⟨802488, by rfl⟩ : syracuseStep 8559877 = 1604977) (by norm_num)
theorem B2284817 : Blo 1780091 2284817 := bbase (se 2 (by rfl) ⟨856806, by rfl⟩ : syracuseStep 2284817 = 1713613) (by norm_num)
theorem B3661085 : Blo 1780091 3661085 := bbase (se 3 (by rfl) ⟨686453, by rfl⟩ : syracuseStep 3661085 = 1372907) (by norm_num)
theorem B6012197 : Blo 1780091 6012197 := bbase (se 4 (by rfl) ⟨563643, by rfl⟩ : syracuseStep 6012197 = 1127287) (by norm_num)
theorem B3005741 : Blo 1780091 3005741 := bbase (se 3 (by rfl) ⟨563576, by rfl⟩ : syracuseStep 3005741 = 1127153) (by norm_num)
theorem B4005269 : Blo 1780091 4005269 := bbase (se 6 (by rfl) ⟨93873, by rfl⟩ : syracuseStep 4005269 = 187747) (by norm_num)
theorem B3005869 : Blo 1780091 3005869 := bbase (se 3 (by rfl) ⟨563600, by rfl⟩ : syracuseStep 3005869 = 1127201) (by norm_num)
theorem B3087829 : Blo 1780091 3087829 := bbase (se 7 (by rfl) ⟨36185, by rfl⟩ : syracuseStep 3087829 = 72371) (by norm_num)
theorem B4005341 : Blo 1780091 4005341 := bbase (se 3 (by rfl) ⟨751001, by rfl⟩ : syracuseStep 4005341 = 1502003) (by norm_num)
theorem B3005957 : Blo 1780091 3005957 := bbase (se 4 (by rfl) ⟨281808, by rfl⟩ : syracuseStep 3005957 = 563617) (by norm_num)
theorem B4005413 : Blo 1780091 4005413 := bbase (se 4 (by rfl) ⟨375507, by rfl⟩ : syracuseStep 4005413 = 751015) (by norm_num)
theorem B3612197 : Blo 1780091 3612197 := bbase (se 4 (by rfl) ⟨338643, by rfl⟩ : syracuseStep 3612197 = 677287) (by norm_num)
theorem B2670149 : Blo 1780091 2670149 := bbase (se 4 (by rfl) ⟨250326, by rfl⟩ : syracuseStep 2670149 = 500653) (by norm_num)
theorem B2670173 : Blo 1780091 2670173 := bbase (se 3 (by rfl) ⟨500657, by rfl⟩ : syracuseStep 2670173 = 1001315) (by norm_num)
theorem B4005485 : Blo 1780091 4005485 := bbase (se 3 (by rfl) ⟨751028, by rfl⟩ : syracuseStep 4005485 = 1502057) (by norm_num)
theorem B2670197 : Blo 1780091 2670197 := bbase (se 5 (by rfl) ⟨125165, by rfl⟩ : syracuseStep 2670197 = 250331) (by norm_num)
theorem B10141301 : Blo 1780091 10141301 := bbase (se 5 (by rfl) ⟨475373, by rfl⟩ : syracuseStep 10141301 = 950747) (by norm_num)
theorem B3210877 : Blo 1780091 3210877 := bbase (se 3 (by rfl) ⟨602039, by rfl⟩ : syracuseStep 3210877 = 1204079) (by norm_num)
theorem B3006085 : Blo 1780091 3006085 := bbase (se 4 (by rfl) ⟨281820, by rfl⟩ : syracuseStep 3006085 = 563641) (by norm_num)
theorem B6766213 : Blo 1780091 6766213 := bbase (se 4 (by rfl) ⟨634332, by rfl⟩ : syracuseStep 6766213 = 1268665) (by norm_num)
theorem B2670221 : Blo 1780091 2670221 := bbase (se 3 (by rfl) ⟨500666, by rfl⟩ : syracuseStep 2670221 = 1001333) (by norm_num)
theorem B2670245 : Blo 1780091 2670245 := bbase (se 4 (by rfl) ⟨250335, by rfl⟩ : syracuseStep 2670245 = 500671) (by norm_num)
theorem B4005557 : Blo 1780091 4005557 := bbase (se 5 (by rfl) ⟨187760, by rfl⟩ : syracuseStep 4005557 = 375521) (by norm_num)
theorem B2670269 : Blo 1780091 2670269 := bbase (se 3 (by rfl) ⟨500675, by rfl⟩ : syracuseStep 2670269 = 1001351) (by norm_num)
theorem B2670293 : Blo 1780091 2670293 := bbase (se 7 (by rfl) ⟨31292, by rfl⟩ : syracuseStep 2670293 = 62585) (by norm_num)
theorem B6012629 : Blo 1780091 6012629 := bbase (se 7 (by rfl) ⟨70460, by rfl⟩ : syracuseStep 6012629 = 140921) (by norm_num)
theorem B3006173 : Blo 1780091 3006173 := bbase (se 3 (by rfl) ⟨563657, by rfl⟩ : syracuseStep 3006173 = 1127315) (by norm_num)
theorem B3047141 : Blo 1780091 3047141 := bbase (se 4 (by rfl) ⟨285669, by rfl⟩ : syracuseStep 3047141 = 571339) (by norm_num)
theorem B2670317 : Blo 1780091 2670317 := bbase (se 3 (by rfl) ⟨500684, by rfl⟩ : syracuseStep 2670317 = 1001369) (by norm_num)
theorem B4005629 : Blo 1780091 4005629 := bbase (se 3 (by rfl) ⟨751055, by rfl⟩ : syracuseStep 4005629 = 1502111) (by norm_num)
theorem B2670341 : Blo 1780091 2670341 := bbase (se 4 (by rfl) ⟨250344, by rfl⟩ : syracuseStep 2670341 = 500689) (by norm_num)
theorem B2670365 : Blo 1780091 2670365 := bbase (se 3 (by rfl) ⟨500693, by rfl⟩ : syracuseStep 2670365 = 1001387) (by norm_num)
theorem B2670389 : Blo 1780091 2670389 := bbase (se 5 (by rfl) ⟨125174, by rfl⟩ : syracuseStep 2670389 = 250349) (by norm_num)
theorem B4005701 : Blo 1780091 4005701 := bbase (se 4 (by rfl) ⟨375534, by rfl⟩ : syracuseStep 4005701 = 751069) (by norm_num)
theorem B2670413 : Blo 1780091 2670413 := bbase (se 3 (by rfl) ⟨500702, by rfl⟩ : syracuseStep 2670413 = 1001405) (by norm_num)
theorem B6946645 : Blo 1780091 6946645 := bbase (se 9 (by rfl) ⟨20351, by rfl⟩ : syracuseStep 6946645 = 40703) (by norm_num)
theorem B3211093 : Blo 1780091 3211093 := bbase (se 9 (by rfl) ⟨9407, by rfl⟩ : syracuseStep 3211093 = 18815) (by norm_num)
theorem B3006301 : Blo 1780091 3006301 := bbase (se 3 (by rfl) ⟨563681, by rfl⟩ : syracuseStep 3006301 = 1127363) (by norm_num)
theorem B2670437 : Blo 1780091 2670437 := bbase (se 4 (by rfl) ⟨250353, by rfl⟩ : syracuseStep 2670437 = 500707) (by norm_num)
theorem B7610213 : Blo 1780091 7610213 := bbase (se 4 (by rfl) ⟨713457, by rfl⟩ : syracuseStep 7610213 = 1426915) (by norm_num)
theorem B2670461 : Blo 1780091 2670461 := bbase (se 3 (by rfl) ⟨500711, by rfl⟩ : syracuseStep 2670461 = 1001423) (by norm_num)
theorem B4005773 : Blo 1780091 4005773 := bbase (se 3 (by rfl) ⟨751082, by rfl⟩ : syracuseStep 4005773 = 1502165) (by norm_num)
theorem B2670485 : Blo 1780091 2670485 := bbase (se 6 (by rfl) ⟨62589, by rfl⟩ : syracuseStep 2670485 = 125179) (by norm_num)
theorem B2670509 : Blo 1780091 2670509 := bbase (se 3 (by rfl) ⟨500720, by rfl⟩ : syracuseStep 2670509 = 1001441) (by norm_num)
theorem B2891701 : Blo 1780091 2891701 := bbase (se 5 (by rfl) ⟨135548, by rfl⟩ : syracuseStep 2891701 = 271097) (by norm_num)
theorem B3006389 : Blo 1780091 3006389 := bbase (se 5 (by rfl) ⟨140924, by rfl⟩ : syracuseStep 3006389 = 281849) (by norm_num)
theorem B2670533 : Blo 1780091 2670533 := bbase (se 4 (by rfl) ⟨250362, by rfl⟩ : syracuseStep 2670533 = 500725) (by norm_num)
theorem B4005845 : Blo 1780091 4005845 := bbase (se 7 (by rfl) ⟨46943, by rfl⟩ : syracuseStep 4005845 = 93887) (by norm_num)
theorem B9019349 : Blo 1780091 9019349 := bbase (se 7 (by rfl) ⟨105695, by rfl⟩ : syracuseStep 9019349 = 211391) (by norm_num)
theorem B2670557 : Blo 1780091 2670557 := bbase (se 3 (by rfl) ⟨500729, by rfl⟩ : syracuseStep 2670557 = 1001459) (by norm_num)
theorem B2670581 : Blo 1780091 2670581 := bbase (se 5 (by rfl) ⟨125183, by rfl⟩ : syracuseStep 2670581 = 250367) (by norm_num)
theorem B2670593 : Blo 1780091 2670593 := bstep (se 2 (by rfl) ⟨1001472, by rfl⟩ : syracuseStep 2670593 = 2002945) B2002945
theorem B17121293 : Blo 1780091 17121293 := bstep (se 3 (by rfl) ⟨3210242, by rfl⟩ : syracuseStep 17121293 = 6420485) B6420485
theorem B2670611 : Blo 1780091 2670611 := bstep (se 1 (by rfl) ⟨2002958, by rfl⟩ : syracuseStep 2670611 = 4005917) B4005917
theorem B3006497 : Blo 1780091 3006497 := bstep (se 2 (by rfl) ⟨1127436, by rfl⟩ : syracuseStep 3006497 = 2254873) B2254873
theorem B2670641 : Blo 1780091 2670641 := bstep (se 2 (by rfl) ⟨1001490, by rfl⟩ : syracuseStep 2670641 = 2002981) B2002981
theorem B2670659 : Blo 1780091 2670659 := bstep (se 1 (by rfl) ⟨2002994, by rfl⟩ : syracuseStep 2670659 = 4005989) B4005989
theorem B2670689 : Blo 1780091 2670689 := bstep (se 2 (by rfl) ⟨1001508, by rfl⟩ : syracuseStep 2670689 = 2003017) B2003017
theorem B4817009 : Blo 1780091 4817009 := bstep (se 2 (by rfl) ⟨1806378, by rfl⟩ : syracuseStep 4817009 = 3612757) B3612757
theorem B2670707 : Blo 1780091 2670707 := bstep (se 1 (by rfl) ⟨2003030, by rfl⟩ : syracuseStep 2670707 = 4006061) B4006061
theorem B2670737 : Blo 1780091 2670737 := bstep (se 2 (by rfl) ⟨1001526, by rfl⟩ : syracuseStep 2670737 = 2003053) B2003053
theorem B3006625 : Blo 1780091 3006625 := bstep (se 2 (by rfl) ⟨1127484, by rfl⟩ : syracuseStep 3006625 = 2254969) B2254969
theorem B2670755 : Blo 1780091 2670755 := bstep (se 1 (by rfl) ⟨2003066, by rfl⟩ : syracuseStep 2670755 = 4006133) B4006133
theorem B24371381 : Blo 1780091 24371381 := bstep (se 5 (by rfl) ⟨1142408, by rfl⟩ : syracuseStep 24371381 = 2284817) B2284817
theorem B2670785 : Blo 1780091 2670785 := bstep (se 2 (by rfl) ⟨1001544, by rfl⟩ : syracuseStep 2670785 = 2003089) B2003089
theorem B3006659 : Blo 1780091 3006659 := bstep (se 1 (by rfl) ⟨2254994, by rfl⟩ : syracuseStep 3006659 = 4509989) B4509989
theorem B4006097 : Blo 1780091 4006097 := bstep (se 2 (by rfl) ⟨1502286, by rfl⟩ : syracuseStep 4006097 = 3004573) B3004573
theorem B2670803 : Blo 1780091 2670803 := bstep (se 1 (by rfl) ⟨2003102, by rfl⟩ : syracuseStep 2670803 = 4006205) B4006205
theorem B4006115 : Blo 1780091 4006115 := bstep (se 1 (by rfl) ⟨3004586, by rfl⟩ : syracuseStep 4006115 = 6009173) B6009173
theorem B2670833 : Blo 1780091 2670833 := bstep (se 2 (by rfl) ⟨1001562, by rfl⟩ : syracuseStep 2670833 = 2003125) B2003125
theorem B6013169 : Blo 1780091 6013169 := bstep (se 2 (by rfl) ⟨2254938, by rfl⟩ : syracuseStep 6013169 = 4509877) B4509877
theorem B2670851 : Blo 1780091 2670851 := bstep (se 1 (by rfl) ⟨2003138, by rfl⟩ : syracuseStep 2670851 = 4006277) B4006277
theorem B2670881 : Blo 1780091 2670881 := bstep (se 2 (by rfl) ⟨1001580, by rfl⟩ : syracuseStep 2670881 = 2003161) B2003161
theorem B2253091 : Blo 1780091 2253091 := bstep (se 1 (by rfl) ⟨1689818, by rfl⟩ : syracuseStep 2253091 = 3379637) B3379637
theorem B2670899 : Blo 1780091 2670899 := bstep (se 1 (by rfl) ⟨2003174, by rfl⟩ : syracuseStep 2670899 = 4006349) B4006349
theorem B3006787 : Blo 1780091 3006787 := bstep (se 1 (by rfl) ⟨2255090, by rfl⟩ : syracuseStep 3006787 = 4510181) B4510181
theorem B2670929 : Blo 1780091 2670929 := bstep (se 2 (by rfl) ⟨1001598, by rfl⟩ : syracuseStep 2670929 = 2003197) B2003197
theorem B2670947 : Blo 1780091 2670947 := bstep (se 1 (by rfl) ⟨2003210, by rfl⟩ : syracuseStep 2670947 = 4006421) B4006421
theorem B4505969 : Blo 1780091 4505969 := bstep (se 2 (by rfl) ⟨1689738, by rfl⟩ : syracuseStep 4505969 = 3379477) B3379477
theorem B2670977 : Blo 1780091 2670977 := bstep (se 2 (by rfl) ⟨1001616, by rfl⟩ : syracuseStep 2670977 = 2003233) B2003233
theorem B2253187 : Blo 1780091 2253187 := bstep (se 1 (by rfl) ⟨1689890, by rfl⟩ : syracuseStep 2253187 = 3379781) B3379781
theorem B2670995 : Blo 1780091 2670995 := bstep (se 1 (by rfl) ⟨2003246, by rfl⟩ : syracuseStep 2670995 = 4006493) B4006493
theorem B2671025 : Blo 1780091 2671025 := bstep (se 2 (by rfl) ⟨1001634, by rfl⟩ : syracuseStep 2671025 = 2003269) B2003269
theorem B19792309 : Blo 1780091 19792309 := bstep (se 5 (by rfl) ⟨927764, by rfl⟩ : syracuseStep 19792309 = 1855529) B1855529
theorem B2671043 : Blo 1780091 2671043 := bstep (se 1 (by rfl) ⟨2003282, by rfl⟩ : syracuseStep 2671043 = 4006565) B4006565
theorem B3006929 : Blo 1780091 3006929 := bstep (se 2 (by rfl) ⟨1127598, by rfl⟩ : syracuseStep 3006929 = 2255197) B2255197
theorem B2671073 : Blo 1780091 2671073 := bstep (se 2 (by rfl) ⟨1001652, by rfl⟩ : syracuseStep 2671073 = 2003305) B2003305
theorem B4006385 : Blo 1780091 4006385 := bstep (se 2 (by rfl) ⟨1502394, by rfl⟩ : syracuseStep 4006385 = 3004789) B3004789
theorem B2671091 : Blo 1780091 2671091 := bstep (se 1 (by rfl) ⟨2003318, by rfl⟩ : syracuseStep 2671091 = 4006637) B4006637
theorem B4006403 : Blo 1780091 4006403 := bstep (se 1 (by rfl) ⟨3004802, by rfl⟩ : syracuseStep 4006403 = 6009605) B6009605
theorem B5415437 : Blo 1780091 5415437 := bstep (se 3 (by rfl) ⟨1015394, by rfl⟩ : syracuseStep 5415437 = 2030789) B2030789
theorem B2671121 : Blo 1780091 2671121 := bstep (se 2 (by rfl) ⟨1001670, by rfl⟩ : syracuseStep 2671121 = 2003341) B2003341
theorem B2671139 : Blo 1780091 2671139 := bstep (se 1 (by rfl) ⟨2003354, by rfl⟩ : syracuseStep 2671139 = 4006709) B4006709
theorem B2671169 : Blo 1780091 2671169 := bstep (se 2 (by rfl) ⟨1001688, by rfl⟩ : syracuseStep 2671169 = 2003377) B2003377
theorem B3007057 : Blo 1780091 3007057 := bstep (se 2 (by rfl) ⟨1127646, by rfl⟩ : syracuseStep 3007057 = 2255293) B2255293
theorem B2671187 : Blo 1780091 2671187 := bstep (se 1 (by rfl) ⟨2003390, by rfl⟩ : syracuseStep 2671187 = 4006781) B4006781
theorem B2671217 : Blo 1780091 2671217 := bstep (se 2 (by rfl) ⟨1001706, by rfl⟩ : syracuseStep 2671217 = 2003413) B2003413
theorem B3007091 : Blo 1780091 3007091 := bstep (se 1 (by rfl) ⟨2255318, by rfl⟩ : syracuseStep 3007091 = 4510637) B4510637
theorem B2671235 : Blo 1780091 2671235 := bstep (se 1 (by rfl) ⟨2003426, by rfl⟩ : syracuseStep 2671235 = 4006853) B4006853
theorem B2671265 : Blo 1780091 2671265 := bstep (se 2 (by rfl) ⟨1001724, by rfl⟩ : syracuseStep 2671265 = 2003449) B2003449
theorem B2671283 : Blo 1780091 2671283 := bstep (se 1 (by rfl) ⟨2003462, by rfl⟩ : syracuseStep 2671283 = 4006925) B4006925
theorem B2851537 : Blo 1780091 2851537 := bstep (se 2 (by rfl) ⟨1069326, by rfl⟩ : syracuseStep 2851537 = 2138653) B2138653
theorem B2671313 : Blo 1780091 2671313 := bstep (se 2 (by rfl) ⟨1001742, by rfl⟩ : syracuseStep 2671313 = 2003485) B2003485
theorem B2671331 : Blo 1780091 2671331 := bstep (se 1 (by rfl) ⟨2003498, by rfl⟩ : syracuseStep 2671331 = 4006997) B4006997
theorem B17597155 : Blo 1780091 17597155 := bstep (se 1 (by rfl) ⟨13197866, by rfl⟩ : syracuseStep 17597155 = 26395733) B26395733
theorem B3007219 : Blo 1780091 3007219 := bstep (se 1 (by rfl) ⟨2255414, by rfl⟩ : syracuseStep 3007219 = 4510829) B4510829
theorem B2671361 : Blo 1780091 2671361 := bstep (se 2 (by rfl) ⟨1001760, by rfl⟩ : syracuseStep 2671361 = 2003521) B2003521
theorem B6013709 : Blo 1780091 6013709 := bstep (se 3 (by rfl) ⟨1127570, by rfl⟩ : syracuseStep 6013709 = 2255141) B2255141
theorem B4006673 : Blo 1780091 4006673 := bstep (se 2 (by rfl) ⟨1502502, by rfl⟩ : syracuseStep 4006673 = 3005005) B3005005
theorem B2671379 : Blo 1780091 2671379 := bstep (se 1 (by rfl) ⟨2003534, by rfl⟩ : syracuseStep 2671379 = 4007069) B4007069
theorem B4006691 : Blo 1780091 4006691 := bstep (se 1 (by rfl) ⟨3005018, by rfl⟩ : syracuseStep 4006691 = 6010037) B6010037
theorem B2671409 : Blo 1780091 2671409 := bstep (se 2 (by rfl) ⟨1001778, by rfl⟩ : syracuseStep 2671409 = 2003557) B2003557
theorem B2671427 : Blo 1780091 2671427 := bstep (se 1 (by rfl) ⟨2003570, by rfl⟩ : syracuseStep 2671427 = 4007141) B4007141
theorem B6013763 : Blo 1780091 6013763 := bstep (se 1 (by rfl) ⟨4510322, by rfl⟩ : syracuseStep 6013763 = 9020645) B9020645
theorem B2671457 : Blo 1780091 2671457 := bstep (se 2 (by rfl) ⟨1001796, by rfl⟩ : syracuseStep 2671457 = 2003593) B2003593
theorem B2253683 : Blo 1780091 2253683 := bstep (se 1 (by rfl) ⟨1690262, by rfl⟩ : syracuseStep 2253683 = 3380525) B3380525
theorem B2671475 : Blo 1780091 2671475 := bstep (se 1 (by rfl) ⟨2003606, by rfl⟩ : syracuseStep 2671475 = 4007213) B4007213
theorem B1901443 : Blo 1780091 1901443 := bstep (se 1 (by rfl) ⟨1426082, by rfl⟩ : syracuseStep 1901443 = 2852165) B2852165
theorem B2671505 : Blo 1780091 2671505 := bstep (se 2 (by rfl) ⟨1001814, by rfl⟩ : syracuseStep 2671505 = 2003629) B2003629
theorem B2671523 : Blo 1780091 2671523 := bstep (se 1 (by rfl) ⟨2003642, by rfl⟩ : syracuseStep 2671523 = 4007285) B4007285
theorem B2671553 : Blo 1780091 2671553 := bstep (se 2 (by rfl) ⟨1001832, by rfl⟩ : syracuseStep 2671553 = 2003665) B2003665
theorem B2671571 : Blo 1780091 2671571 := bstep (se 1 (by rfl) ⟨2003678, by rfl⟩ : syracuseStep 2671571 = 4007357) B4007357
theorem B6759395 : Blo 1780091 6759395 := bstep (se 1 (by rfl) ⟨5069546, by rfl⟩ : syracuseStep 6759395 = 10139093) B10139093
theorem B6759409 : Blo 1780091 6759409 := bstep (se 2 (by rfl) ⟨2534778, by rfl⟩ : syracuseStep 6759409 = 5069557) B5069557
theorem B2671601 : Blo 1780091 2671601 := bstep (se 2 (by rfl) ⟨1001850, by rfl⟩ : syracuseStep 2671601 = 2003701) B2003701
theorem B2671619 : Blo 1780091 2671619 := bstep (se 1 (by rfl) ⟨2003714, by rfl⟩ : syracuseStep 2671619 = 4007429) B4007429
theorem B2671649 : Blo 1780091 2671649 := bstep (se 2 (by rfl) ⟨1001868, by rfl⟩ : syracuseStep 2671649 = 2003737) B2003737
theorem B4006961 : Blo 1780091 4006961 := bstep (se 2 (by rfl) ⟨1502610, by rfl⟩ : syracuseStep 4006961 = 3005221) B3005221
theorem B2671667 : Blo 1780091 2671667 := bstep (se 1 (by rfl) ⟨2003750, by rfl⟩ : syracuseStep 2671667 = 4007501) B4007501
theorem B4006979 : Blo 1780091 4006979 := bstep (se 1 (by rfl) ⟨3005234, by rfl⟩ : syracuseStep 4006979 = 6010469) B6010469
theorem B12354629 : Blo 1780091 12354629 := bstep (se 4 (by rfl) ⟨1158246, by rfl⟩ : syracuseStep 12354629 = 2316493) B2316493
theorem B2671697 : Blo 1780091 2671697 := bstep (se 2 (by rfl) ⟨1001886, by rfl⟩ : syracuseStep 2671697 = 2003773) B2003773
theorem B6014033 : Blo 1780091 6014033 := bstep (se 2 (by rfl) ⟨2255262, by rfl⟩ : syracuseStep 6014033 = 4510525) B4510525
theorem B2671715 : Blo 1780091 2671715 := bstep (se 1 (by rfl) ⟨2003786, by rfl⟩ : syracuseStep 2671715 = 4007573) B4007573
theorem B2671745 : Blo 1780091 2671745 := bstep (se 2 (by rfl) ⟨1001904, by rfl⟩ : syracuseStep 2671745 = 2003809) B2003809
theorem B2671763 : Blo 1780091 2671763 := bstep (se 1 (by rfl) ⟨2003822, by rfl⟩ : syracuseStep 2671763 = 4007645) B4007645
theorem B2671793 : Blo 1780091 2671793 := bstep (se 2 (by rfl) ⟨1001922, by rfl⟩ : syracuseStep 2671793 = 2003845) B2003845
theorem B20276405 : Blo 1780091 20276405 := bstep (se 5 (by rfl) ⟨950456, by rfl⟩ : syracuseStep 20276405 = 1900913) B1900913
theorem B2671811 : Blo 1780091 2671811 := bstep (se 1 (by rfl) ⟨2003858, by rfl⟩ : syracuseStep 2671811 = 4007717) B4007717
theorem B12838085 : Blo 1780091 12838085 := bstep (se 4 (by rfl) ⟨1203570, by rfl⟩ : syracuseStep 12838085 = 2407141) B2407141
theorem B2671841 : Blo 1780091 2671841 := bstep (se 2 (by rfl) ⟨1001940, by rfl⟩ : syracuseStep 2671841 = 2003881) B2003881
theorem B3802339 : Blo 1780091 3802339 := bstep (se 1 (by rfl) ⟨2851754, by rfl⟩ : syracuseStep 3802339 = 5703509) B5703509
theorem B2671859 : Blo 1780091 2671859 := bstep (se 1 (by rfl) ⟨2003894, by rfl⟩ : syracuseStep 2671859 = 4007789) B4007789
theorem B2671889 : Blo 1780091 2671889 := bstep (se 2 (by rfl) ⟨1001958, by rfl⟩ : syracuseStep 2671889 = 2003917) B2003917
theorem B2671907 : Blo 1780091 2671907 := bstep (se 1 (by rfl) ⟨2003930, by rfl⟩ : syracuseStep 2671907 = 4007861) B4007861
theorem B2671937 : Blo 1780091 2671937 := bstep (se 2 (by rfl) ⟨1001976, by rfl⟩ : syracuseStep 2671937 = 2003953) B2003953
theorem B4277585 : Blo 1780091 4277585 := bstep (se 2 (by rfl) ⟨1604094, by rfl⟩ : syracuseStep 4277585 = 3208189) B3208189
theorem B4506961 : Blo 1780091 4506961 := bstep (se 2 (by rfl) ⟨1690110, by rfl⟩ : syracuseStep 4506961 = 3380221) B3380221
theorem B4007249 : Blo 1780091 4007249 := bstep (se 2 (by rfl) ⟨1502718, by rfl⟩ : syracuseStep 4007249 = 3005437) B3005437
theorem B2671955 : Blo 1780091 2671955 := bstep (se 1 (by rfl) ⟨2003966, by rfl⟩ : syracuseStep 2671955 = 4007933) B4007933
theorem B4007267 : Blo 1780091 4007267 := bstep (se 1 (by rfl) ⟨3005450, by rfl⟩ : syracuseStep 4007267 = 6010901) B6010901
theorem B16246129 : Blo 1780091 16246129 := bstep (se 2 (by rfl) ⟨6092298, by rfl⟩ : syracuseStep 16246129 = 12184597) B12184597
theorem B2671985 : Blo 1780091 2671985 := bstep (se 2 (by rfl) ⟨1001994, by rfl⟩ : syracuseStep 2671985 = 2003989) B2003989
theorem B2672003 : Blo 1780091 2672003 := bstep (se 1 (by rfl) ⟨2004002, by rfl⟩ : syracuseStep 2672003 = 4008005) B4008005
theorem B2672033 : Blo 1780091 2672033 := bstep (se 2 (by rfl) ⟨1002012, by rfl⟩ : syracuseStep 2672033 = 2004025) B2004025
theorem B5072291 : Blo 1780091 5072291 := bstep (se 1 (by rfl) ⟨3804218, by rfl⟩ : syracuseStep 5072291 = 7608437) B7608437
theorem B2672051 : Blo 1780091 2672051 := bstep (se 1 (by rfl) ⟨2004038, by rfl⟩ : syracuseStep 2672051 = 4008077) B4008077
theorem B2672081 : Blo 1780091 2672081 := bstep (se 2 (by rfl) ⟨1002030, by rfl⟩ : syracuseStep 2672081 = 2004061) B2004061
theorem B9012707 : Blo 1780091 9012707 := bstep (se 1 (by rfl) ⟨6759530, by rfl⟩ : syracuseStep 9012707 = 13519061) B13519061
theorem B2672099 : Blo 1780091 2672099 := bstep (se 1 (by rfl) ⟨2004074, by rfl⟩ : syracuseStep 2672099 = 4008149) B4008149
theorem B11888099 : Blo 1780091 11888099 := bstep (se 1 (by rfl) ⟨8916074, by rfl⟩ : syracuseStep 11888099 = 17832149) B17832149
theorem B22816241 : Blo 1780091 22816241 := bstep (se 2 (by rfl) ⟨8556090, by rfl⟩ : syracuseStep 22816241 = 17112181) B17112181
theorem B2672129 : Blo 1780091 2672129 := bstep (se 2 (by rfl) ⟨1002048, by rfl⟩ : syracuseStep 2672129 = 2004097) B2004097
theorem B2672147 : Blo 1780091 2672147 := bstep (se 1 (by rfl) ⟨2004110, by rfl⟩ : syracuseStep 2672147 = 4008221) B4008221
theorem B2672177 : Blo 1780091 2672177 := bstep (se 2 (by rfl) ⟨1002066, by rfl⟩ : syracuseStep 2672177 = 2004133) B2004133
theorem B2254387 : Blo 1780091 2254387 := bstep (se 1 (by rfl) ⟨1690790, by rfl⟩ : syracuseStep 2254387 = 3381581) B3381581
theorem B2672195 : Blo 1780091 2672195 := bstep (se 1 (by rfl) ⟨2004146, by rfl⟩ : syracuseStep 2672195 = 4008293) B4008293
theorem B7603789 : Blo 1780091 7603789 := bstep (se 3 (by rfl) ⟨1425710, by rfl⟩ : syracuseStep 7603789 = 2851421) B2851421
theorem B2672225 : Blo 1780091 2672225 := bstep (se 2 (by rfl) ⟨1002084, by rfl⟩ : syracuseStep 2672225 = 2004169) B2004169
theorem B4507235 : Blo 1780091 4507235 := bstep (se 1 (by rfl) ⟨3380426, by rfl⟩ : syracuseStep 4507235 = 6760853) B6760853
theorem B4007537 : Blo 1780091 4007537 := bstep (se 2 (by rfl) ⟨1502826, by rfl⟩ : syracuseStep 4007537 = 3005653) B3005653
theorem B2672243 : Blo 1780091 2672243 := bstep (se 1 (by rfl) ⟨2004182, by rfl⟩ : syracuseStep 2672243 = 4008365) B4008365
theorem B4007555 : Blo 1780091 4007555 := bstep (se 1 (by rfl) ⟨3005666, by rfl⟩ : syracuseStep 4007555 = 6011333) B6011333
theorem B2672273 : Blo 1780091 2672273 := bstep (se 2 (by rfl) ⟨1002102, by rfl⟩ : syracuseStep 2672273 = 2004205) B2004205
theorem B2254483 : Blo 1780091 2254483 := bstep (se 1 (by rfl) ⟨1690862, by rfl⟩ : syracuseStep 2254483 = 3381725) B3381725
theorem B2672291 : Blo 1780091 2672291 := bstep (se 1 (by rfl) ⟨2004218, by rfl⟩ : syracuseStep 2672291 = 4008437) B4008437
theorem B3802801 : Blo 1780091 3802801 := bstep (se 2 (by rfl) ⟨1426050, by rfl⟩ : syracuseStep 3802801 = 2852101) B2852101
theorem B11413169 : Blo 1780091 11413169 := bstep (se 2 (by rfl) ⟨4279938, by rfl⟩ : syracuseStep 11413169 = 8559877) B8559877
theorem B2672321 : Blo 1780091 2672321 := bstep (se 2 (by rfl) ⟨1002120, by rfl⟩ : syracuseStep 2672321 = 2004241) B2004241
theorem B21956293 : Blo 1780091 21956293 := bstep (se 4 (by rfl) ⟨2058402, by rfl⟩ : syracuseStep 21956293 = 4116805) B4116805
theorem B2672339 : Blo 1780091 2672339 := bstep (se 1 (by rfl) ⟨2004254, by rfl⟩ : syracuseStep 2672339 = 4008509) B4008509
theorem B2672369 : Blo 1780091 2672369 := bstep (se 2 (by rfl) ⟨1002138, by rfl⟩ : syracuseStep 2672369 = 2004277) B2004277
theorem B1902323 : Blo 1780091 1902323 := bstep (se 1 (by rfl) ⟨1426742, by rfl⟩ : syracuseStep 1902323 = 2853485) B2853485
theorem B2672387 : Blo 1780091 2672387 := bstep (se 1 (by rfl) ⟨2004290, by rfl⟩ : syracuseStep 2672387 = 4008581) B4008581
theorem B2672417 : Blo 1780091 2672417 := bstep (se 2 (by rfl) ⟨1002156, by rfl⟩ : syracuseStep 2672417 = 2004313) B2004313
theorem B4507427 : Blo 1780091 4507427 := bstep (se 1 (by rfl) ⟨3380570, by rfl⟩ : syracuseStep 4507427 = 6761141) B6761141
theorem B5416739 : Blo 1780091 5416739 := bstep (se 1 (by rfl) ⟨4062554, by rfl⟩ : syracuseStep 5416739 = 8125109) B8125109
theorem B2672435 : Blo 1780091 2672435 := bstep (se 1 (by rfl) ⟨2004326, by rfl⟩ : syracuseStep 2672435 = 4008653) B4008653
theorem B2672465 : Blo 1780091 2672465 := bstep (se 2 (by rfl) ⟨1002174, by rfl⟩ : syracuseStep 2672465 = 2004349) B2004349
theorem B2672483 : Blo 1780091 2672483 := bstep (se 1 (by rfl) ⟨2004362, by rfl⟩ : syracuseStep 2672483 = 4008725) B4008725
theorem B14444401 : Blo 1780091 14444401 := bstep (se 2 (by rfl) ⟨5416650, by rfl⟩ : syracuseStep 14444401 = 10833301) B10833301
theorem B1902451 : Blo 1780091 1902451 := bstep (se 1 (by rfl) ⟨1426838, by rfl⟩ : syracuseStep 1902451 = 2853677) B2853677
theorem B2672513 : Blo 1780091 2672513 := bstep (se 2 (by rfl) ⟨1002192, by rfl⟩ : syracuseStep 2672513 = 2004385) B2004385
theorem B4007825 : Blo 1780091 4007825 := bstep (se 2 (by rfl) ⟨1502934, by rfl⟩ : syracuseStep 4007825 = 3005869) B3005869
theorem B2672531 : Blo 1780091 2672531 := bstep (se 1 (by rfl) ⟨2004398, by rfl⟩ : syracuseStep 2672531 = 4008797) B4008797
theorem B7604131 : Blo 1780091 7604131 := bstep (se 1 (by rfl) ⟨5703098, by rfl⟩ : syracuseStep 7604131 = 11406197) B11406197
theorem B4007843 : Blo 1780091 4007843 := bstep (se 1 (by rfl) ⟨3005882, by rfl⟩ : syracuseStep 4007843 = 6011765) B6011765
theorem B2672561 : Blo 1780091 2672561 := bstep (se 2 (by rfl) ⟨1002210, by rfl⟩ : syracuseStep 2672561 = 2004421) B2004421
theorem B2672579 : Blo 1780091 2672579 := bstep (se 1 (by rfl) ⟨2004434, by rfl⟩ : syracuseStep 2672579 = 4008869) B4008869
theorem B2672609 : Blo 1780091 2672609 := bstep (se 2 (by rfl) ⟨1002228, by rfl⟩ : syracuseStep 2672609 = 2004457) B2004457
theorem B2672627 : Blo 1780091 2672627 := bstep (se 1 (by rfl) ⟨2004470, by rfl⟩ : syracuseStep 2672627 = 4008941) B4008941
theorem B2672657 : Blo 1780091 2672657 := bstep (se 2 (by rfl) ⟨1002246, by rfl⟩ : syracuseStep 2672657 = 2004493) B2004493
theorem B2672675 : Blo 1780091 2672675 := bstep (se 1 (by rfl) ⟨2004506, by rfl⟩ : syracuseStep 2672675 = 4009013) B4009013
theorem B2672705 : Blo 1780091 2672705 := bstep (se 2 (by rfl) ⟨1002264, by rfl⟩ : syracuseStep 2672705 = 2004529) B2004529
theorem B2672723 : Blo 1780091 2672723 := bstep (se 1 (by rfl) ⟨2004542, by rfl⟩ : syracuseStep 2672723 = 4009085) B4009085
theorem B2672753 : Blo 1780091 2672753 := bstep (se 2 (by rfl) ⟨1002282, by rfl⟩ : syracuseStep 2672753 = 2004565) B2004565
theorem B2254979 : Blo 1780091 2254979 := bstep (se 1 (by rfl) ⟨1691234, by rfl⟩ : syracuseStep 2254979 = 3382469) B3382469
theorem B2672771 : Blo 1780091 2672771 := bstep (se 1 (by rfl) ⟨2004578, by rfl⟩ : syracuseStep 2672771 = 4009157) B4009157
theorem B2672801 : Blo 1780091 2672801 := bstep (se 2 (by rfl) ⟨1002300, by rfl⟩ : syracuseStep 2672801 = 2004601) B2004601
theorem B4008113 : Blo 1780091 4008113 := bstep (se 2 (by rfl) ⟨1503042, by rfl⟩ : syracuseStep 4008113 = 3006085) B3006085
theorem B2672819 : Blo 1780091 2672819 := bstep (se 1 (by rfl) ⟨2004614, by rfl⟩ : syracuseStep 2672819 = 4009229) B4009229
theorem B9021617 : Blo 1780091 9021617 := bstep (se 2 (by rfl) ⟨3383106, by rfl⟩ : syracuseStep 9021617 = 6766213) B6766213
theorem B4008131 : Blo 1780091 4008131 := bstep (se 1 (by rfl) ⟨3006098, by rfl⟩ : syracuseStep 4008131 = 6012197) B6012197
theorem B5073101 : Blo 1780091 5073101 := bstep (se 3 (by rfl) ⟨951206, by rfl⟩ : syracuseStep 5073101 = 1902413) B1902413
theorem B2672849 : Blo 1780091 2672849 := bstep (se 2 (by rfl) ⟨1002318, by rfl⟩ : syracuseStep 2672849 = 2004637) B2004637
theorem B2672867 : Blo 1780091 2672867 := bstep (se 1 (by rfl) ⟨2004650, by rfl⟩ : syracuseStep 2672867 = 4009301) B4009301
theorem B2672897 : Blo 1780091 2672897 := bstep (se 2 (by rfl) ⟨1002336, by rfl⟩ : syracuseStep 2672897 = 2004673) B2004673
theorem B9013517 : Blo 1780091 9013517 := bstep (se 3 (by rfl) ⟨1690034, by rfl⟩ : syracuseStep 9013517 = 3380069) B3380069
theorem B20293901 : Blo 1780091 20293901 := bstep (se 3 (by rfl) ⟨3805106, by rfl⟩ : syracuseStep 20293901 = 7610213) B7610213
theorem B2853139 : Blo 1780091 2853139 := bstep (se 1 (by rfl) ⟨2139854, by rfl⟩ : syracuseStep 2853139 = 4279709) B4279709
theorem B2672915 : Blo 1780091 2672915 := bstep (se 1 (by rfl) ⟨2004686, by rfl⟩ : syracuseStep 2672915 = 4009373) B4009373
theorem B2672945 : Blo 1780091 2672945 := bstep (se 2 (by rfl) ⟨1002354, by rfl⟩ : syracuseStep 2672945 = 2004709) B2004709
theorem B2672963 : Blo 1780091 2672963 := bstep (se 1 (by rfl) ⟨2004722, by rfl⟩ : syracuseStep 2672963 = 4009445) B4009445
theorem B2672993 : Blo 1780091 2672993 := bstep (se 2 (by rfl) ⟨1002372, by rfl⟩ : syracuseStep 2672993 = 2004745) B2004745
theorem B2673011 : Blo 1780091 2673011 := bstep (se 1 (by rfl) ⟨2004758, by rfl⟩ : syracuseStep 2673011 = 4009517) B4009517
theorem B1780099 : Blo 1780091 1780099 := bstep (se 1 (by rfl) ⟨1335074, by rfl⟩ : syracuseStep 1780099 = 2670149) B2670149
theorem B1804675 : Blo 1780091 1804675 := bstep (se 1 (by rfl) ⟨1353506, by rfl⟩ : syracuseStep 1804675 = 2707013) B2707013
theorem B5073293 : Blo 1780091 5073293 := bstep (se 3 (by rfl) ⟨951242, by rfl⟩ : syracuseStep 5073293 = 1902485) B1902485
theorem B2673041 : Blo 1780091 2673041 := bstep (se 2 (by rfl) ⟨1002390, by rfl⟩ : syracuseStep 2673041 = 2004781) B2004781
theorem B1780115 : Blo 1780091 1780115 := bstep (se 1 (by rfl) ⟨1335086, by rfl⟩ : syracuseStep 1780115 = 2670173) B2670173
theorem B1780131 : Blo 1780091 1780131 := bstep (se 1 (by rfl) ⟨1335098, by rfl⟩ : syracuseStep 1780131 = 2670197) B2670197
theorem B6760867 : Blo 1780091 6760867 := bstep (se 1 (by rfl) ⟨5070650, by rfl⟩ : syracuseStep 6760867 = 10141301) B10141301
theorem B2673059 : Blo 1780091 2673059 := bstep (se 1 (by rfl) ⟨2004794, by rfl⟩ : syracuseStep 2673059 = 4009589) B4009589
theorem B1780147 : Blo 1780091 1780147 := bstep (se 1 (by rfl) ⟨1335110, by rfl⟩ : syracuseStep 1780147 = 2670221) B2670221
theorem B1780163 : Blo 1780091 1780163 := bstep (se 1 (by rfl) ⟨1335122, by rfl⟩ : syracuseStep 1780163 = 2670245) B2670245
theorem B2673089 : Blo 1780091 2673089 := bstep (se 2 (by rfl) ⟨1002408, by rfl⟩ : syracuseStep 2673089 = 2004817) B2004817
theorem B4008401 : Blo 1780091 4008401 := bstep (se 2 (by rfl) ⟨1503150, by rfl⟩ : syracuseStep 4008401 = 3006301) B3006301
theorem B1780179 : Blo 1780091 1780179 := bstep (se 1 (by rfl) ⟨1335134, by rfl⟩ : syracuseStep 1780179 = 2670269) B2670269
theorem B2673107 : Blo 1780091 2673107 := bstep (se 1 (by rfl) ⟨2004830, by rfl⟩ : syracuseStep 2673107 = 4009661) B4009661
theorem B1780195 : Blo 1780091 1780195 := bstep (se 1 (by rfl) ⟨1335146, by rfl⟩ : syracuseStep 1780195 = 2670293) B2670293
theorem B4008419 : Blo 1780091 4008419 := bstep (se 1 (by rfl) ⟨3006314, by rfl⟩ : syracuseStep 4008419 = 6012629) B6012629
theorem B2673137 : Blo 1780091 2673137 := bstep (se 2 (by rfl) ⟨1002426, by rfl⟩ : syracuseStep 2673137 = 2004853) B2004853
theorem B1780211 : Blo 1780091 1780211 := bstep (se 1 (by rfl) ⟨1335158, by rfl⟩ : syracuseStep 1780211 = 2670317) B2670317
theorem B1780227 : Blo 1780091 1780227 := bstep (se 1 (by rfl) ⟨1335170, by rfl⟩ : syracuseStep 1780227 = 2670341) B2670341
theorem B6416909 : Blo 1780091 6416909 := bstep (se 3 (by rfl) ⟨1203170, by rfl⟩ : syracuseStep 6416909 = 2406341) B2406341
theorem B1780243 : Blo 1780091 1780243 := bstep (se 1 (by rfl) ⟨1335182, by rfl⟩ : syracuseStep 1780243 = 2670365) B2670365
theorem B2853395 : Blo 1780091 2853395 := bstep (se 1 (by rfl) ⟨2140046, by rfl⟩ : syracuseStep 2853395 = 4280093) B4280093
theorem B1780259 : Blo 1780091 1780259 := bstep (se 1 (by rfl) ⟨1335194, by rfl⟩ : syracuseStep 1780259 = 2670389) B2670389
theorem B1780275 : Blo 1780091 1780275 := bstep (se 1 (by rfl) ⟨1335206, by rfl⟩ : syracuseStep 1780275 = 2670413) B2670413
theorem B1780291 : Blo 1780091 1780291 := bstep (se 1 (by rfl) ⟨1335218, by rfl⟩ : syracuseStep 1780291 = 2670437) B2670437
theorem B1780307 : Blo 1780091 1780307 := bstep (se 1 (by rfl) ⟨1335230, by rfl⟩ : syracuseStep 1780307 = 2670461) B2670461
theorem B1780323 : Blo 1780091 1780323 := bstep (se 1 (by rfl) ⟨1335242, by rfl⟩ : syracuseStep 1780323 = 2670485) B2670485
theorem B1780339 : Blo 1780091 1780339 := bstep (se 1 (by rfl) ⟨1335254, by rfl⟩ : syracuseStep 1780339 = 2670509) B2670509
theorem B1780355 : Blo 1780091 1780355 := bstep (se 1 (by rfl) ⟨1335266, by rfl⟩ : syracuseStep 1780355 = 2670533) B2670533
theorem B1780371 : Blo 1780091 1780371 := bstep (se 1 (by rfl) ⟨1335278, by rfl⟩ : syracuseStep 1780371 = 2670557) B2670557
theorem B1780387 : Blo 1780091 1780387 := bstep (se 1 (by rfl) ⟨1335290, by rfl⟩ : syracuseStep 1780387 = 2670581) B2670581
theorem B1780403 : Blo 1780091 1780403 := bstep (se 1 (by rfl) ⟨1335302, by rfl⟩ : syracuseStep 1780403 = 2670605) B2670605
theorem B1780419 : Blo 1780091 1780419 := bstep (se 1 (by rfl) ⟨1335314, by rfl⟩ : syracuseStep 1780419 = 2670629) B2670629
theorem B3803843 : Blo 1780091 3803843 := bstep (se 1 (by rfl) ⟨2852882, by rfl⟩ : syracuseStep 3803843 = 5705765) B5705765
theorem B4508369 : Blo 1780091 4508369 := bstep (se 2 (by rfl) ⟨1690638, by rfl⟩ : syracuseStep 4508369 = 3381277) B3381277
theorem B1780435 : Blo 1780091 1780435 := bstep (se 1 (by rfl) ⟨1335326, by rfl⟩ : syracuseStep 1780435 = 2670653) B2670653
theorem B2853587 : Blo 1780091 2853587 := bstep (se 1 (by rfl) ⟨2140190, by rfl⟩ : syracuseStep 2853587 = 4280381) B4280381
theorem B1780451 : Blo 1780091 1780451 := bstep (se 1 (by rfl) ⟨1335338, by rfl⟩ : syracuseStep 1780451 = 2670677) B2670677
theorem B4008689 : Blo 1780091 4008689 := bstep (se 2 (by rfl) ⟨1503258, by rfl⟩ : syracuseStep 4008689 = 3006517) B3006517
theorem B1780467 : Blo 1780091 1780467 := bstep (se 1 (by rfl) ⟨1335350, by rfl⟩ : syracuseStep 1780467 = 2670701) B2670701
theorem B1780483 : Blo 1780091 1780483 := bstep (se 1 (by rfl) ⟨1335362, by rfl⟩ : syracuseStep 1780483 = 2670725) B2670725
theorem B4508419 : Blo 1780091 4508419 := bstep (se 1 (by rfl) ⟨3381314, by rfl⟩ : syracuseStep 4508419 = 6762629) B6762629
theorem B4008707 : Blo 1780091 4008707 := bstep (se 1 (by rfl) ⟨3006530, by rfl⟩ : syracuseStep 4008707 = 6013061) B6013061
theorem B1780499 : Blo 1780091 1780499 := bstep (se 1 (by rfl) ⟨1335374, by rfl⟩ : syracuseStep 1780499 = 2670749) B2670749
theorem B1780515 : Blo 1780091 1780515 := bstep (se 1 (by rfl) ⟨1335386, by rfl⟩ : syracuseStep 1780515 = 2670773) B2670773
theorem B1780531 : Blo 1780091 1780531 := bstep (se 1 (by rfl) ⟨1335398, by rfl⟩ : syracuseStep 1780531 = 2670797) B2670797
theorem B1780547 : Blo 1780091 1780547 := bstep (se 1 (by rfl) ⟨1335410, by rfl⟩ : syracuseStep 1780547 = 2670821) B2670821
theorem B1780563 : Blo 1780091 1780563 := bstep (se 1 (by rfl) ⟨1335422, by rfl⟩ : syracuseStep 1780563 = 2670845) B2670845
theorem B1780579 : Blo 1780091 1780579 := bstep (se 1 (by rfl) ⟨1335434, by rfl⟩ : syracuseStep 1780579 = 2670869) B2670869
theorem B5786467 : Blo 1780091 5786467 := bstep (se 1 (by rfl) ⟨4339850, by rfl⟩ : syracuseStep 5786467 = 8679701) B8679701
theorem B1780595 : Blo 1780091 1780595 := bstep (se 1 (by rfl) ⟨1335446, by rfl⟩ : syracuseStep 1780595 = 2670893) B2670893
theorem B1780611 : Blo 1780091 1780611 := bstep (se 1 (by rfl) ⟨1335458, by rfl⟩ : syracuseStep 1780611 = 2670917) B2670917
theorem B4508561 : Blo 1780091 4508561 := bstep (se 2 (by rfl) ⟨1690710, by rfl⟩ : syracuseStep 4508561 = 3381421) B3381421
theorem B1780627 : Blo 1780091 1780627 := bstep (se 1 (by rfl) ⟨1335470, by rfl⟩ : syracuseStep 1780627 = 2670941) B2670941
theorem B1780643 : Blo 1780091 1780643 := bstep (se 1 (by rfl) ⟨1335482, by rfl⟩ : syracuseStep 1780643 = 2670965) B2670965
theorem B1780659 : Blo 1780091 1780659 := bstep (se 1 (by rfl) ⟨1335494, by rfl⟩ : syracuseStep 1780659 = 2670989) B2670989
theorem B1780675 : Blo 1780091 1780675 := bstep (se 1 (by rfl) ⟨1335506, by rfl⟩ : syracuseStep 1780675 = 2671013) B2671013
theorem B1780691 : Blo 1780091 1780691 := bstep (se 1 (by rfl) ⟨1335518, by rfl⟩ : syracuseStep 1780691 = 2671037) B2671037
theorem B1780707 : Blo 1780091 1780707 := bstep (se 1 (by rfl) ⟨1335530, by rfl⟩ : syracuseStep 1780707 = 2671061) B2671061
theorem B1780723 : Blo 1780091 1780723 := bstep (se 1 (by rfl) ⟨1335542, by rfl⟩ : syracuseStep 1780723 = 2671085) B2671085
theorem B1780739 : Blo 1780091 1780739 := bstep (se 1 (by rfl) ⟨1335554, by rfl⟩ : syracuseStep 1780739 = 2671109) B2671109
theorem B4008977 : Blo 1780091 4008977 := bstep (se 2 (by rfl) ⟨1503366, by rfl⟩ : syracuseStep 4008977 = 3006733) B3006733
theorem B1780755 : Blo 1780091 1780755 := bstep (se 1 (by rfl) ⟨1335566, by rfl⟩ : syracuseStep 1780755 = 2671133) B2671133
theorem B5704739 : Blo 1780091 5704739 := bstep (se 1 (by rfl) ⟨4278554, by rfl⟩ : syracuseStep 5704739 = 8557109) B8557109
theorem B1780771 : Blo 1780091 1780771 := bstep (se 1 (by rfl) ⟨1335578, by rfl⟩ : syracuseStep 1780771 = 2671157) B2671157
theorem B4008995 : Blo 1780091 4008995 := bstep (se 1 (by rfl) ⟨3006746, by rfl⟩ : syracuseStep 4008995 = 6013493) B6013493
theorem B1780787 : Blo 1780091 1780787 := bstep (se 1 (by rfl) ⟨1335590, by rfl⟩ : syracuseStep 1780787 = 2671181) B2671181
theorem B1780803 : Blo 1780091 1780803 := bstep (se 1 (by rfl) ⟨1335602, by rfl⟩ : syracuseStep 1780803 = 2671205) B2671205
theorem B1780819 : Blo 1780091 1780819 := bstep (se 1 (by rfl) ⟨1335614, by rfl⟩ : syracuseStep 1780819 = 2671229) B2671229
theorem B1780835 : Blo 1780091 1780835 := bstep (se 1 (by rfl) ⟨1335626, by rfl⟩ : syracuseStep 1780835 = 2671253) B2671253
theorem B1780851 : Blo 1780091 1780851 := bstep (se 1 (by rfl) ⟨1335638, by rfl⟩ : syracuseStep 1780851 = 2671277) B2671277
theorem B1780867 : Blo 1780091 1780867 := bstep (se 1 (by rfl) ⟨1335650, by rfl⟩ : syracuseStep 1780867 = 2671301) B2671301
theorem B15223949 : Blo 1780091 15223949 := bstep (se 3 (by rfl) ⟨2854490, by rfl⟩ : syracuseStep 15223949 = 5708981) B5708981
theorem B1780883 : Blo 1780091 1780883 := bstep (se 1 (by rfl) ⟨1335662, by rfl⟩ : syracuseStep 1780883 = 2671325) B2671325
theorem B1780899 : Blo 1780091 1780899 := bstep (se 1 (by rfl) ⟨1335674, by rfl⟩ : syracuseStep 1780899 = 2671349) B2671349
theorem B6007985 : Blo 1780091 6007985 := bstep (se 2 (by rfl) ⟨2252994, by rfl⟩ : syracuseStep 6007985 = 4505989) B4505989
theorem B1780915 : Blo 1780091 1780915 := bstep (se 1 (by rfl) ⟨1335686, by rfl⟩ : syracuseStep 1780915 = 2671373) B2671373
theorem B1780931 : Blo 1780091 1780931 := bstep (se 1 (by rfl) ⟨1335698, by rfl⟩ : syracuseStep 1780931 = 2671397) B2671397
theorem B3804355 : Blo 1780091 3804355 := bstep (se 1 (by rfl) ⟨2853266, by rfl⟩ : syracuseStep 3804355 = 5706533) B5706533
theorem B1780947 : Blo 1780091 1780947 := bstep (se 1 (by rfl) ⟨1335710, by rfl⟩ : syracuseStep 1780947 = 2671421) B2671421
theorem B1780963 : Blo 1780091 1780963 := bstep (se 1 (by rfl) ⟨1335722, by rfl⟩ : syracuseStep 1780963 = 2671445) B2671445
theorem B1780979 : Blo 1780091 1780979 := bstep (se 1 (by rfl) ⟨1335734, by rfl⟩ : syracuseStep 1780979 = 2671469) B2671469
theorem B1780995 : Blo 1780091 1780995 := bstep (se 1 (by rfl) ⟨1335746, by rfl⟩ : syracuseStep 1780995 = 2671493) B2671493
theorem B1781011 : Blo 1780091 1781011 := bstep (se 1 (by rfl) ⟨1335758, by rfl⟩ : syracuseStep 1781011 = 2671517) B2671517
theorem B1781027 : Blo 1780091 1781027 := bstep (se 1 (by rfl) ⟨1335770, by rfl⟩ : syracuseStep 1781027 = 2671541) B2671541
theorem B4009265 : Blo 1780091 4009265 := bstep (se 2 (by rfl) ⟨1503474, by rfl⟩ : syracuseStep 4009265 = 3006949) B3006949
theorem B1781043 : Blo 1780091 1781043 := bstep (se 1 (by rfl) ⟨1335782, by rfl⟩ : syracuseStep 1781043 = 2671565) B2671565
theorem B1781059 : Blo 1780091 1781059 := bstep (se 1 (by rfl) ⟨1335794, by rfl⟩ : syracuseStep 1781059 = 2671589) B2671589
theorem B4009283 : Blo 1780091 4009283 := bstep (se 1 (by rfl) ⟨3006962, by rfl⟩ : syracuseStep 4009283 = 6013925) B6013925
theorem B1781075 : Blo 1780091 1781075 := bstep (se 1 (by rfl) ⟨1335806, by rfl⟩ : syracuseStep 1781075 = 2671613) B2671613
theorem B1781091 : Blo 1780091 1781091 := bstep (se 1 (by rfl) ⟨1335818, by rfl⟩ : syracuseStep 1781091 = 2671637) B2671637
theorem B5074285 : Blo 1780091 5074285 := bstep (se 3 (by rfl) ⟨951428, by rfl⟩ : syracuseStep 5074285 = 1902857) B1902857
theorem B1781107 : Blo 1780091 1781107 := bstep (se 1 (by rfl) ⟨1335830, by rfl⟩ : syracuseStep 1781107 = 2671661) B2671661
theorem B1781123 : Blo 1780091 1781123 := bstep (se 1 (by rfl) ⟨1335842, by rfl⟩ : syracuseStep 1781123 = 2671685) B2671685
theorem B1781139 : Blo 1780091 1781139 := bstep (se 1 (by rfl) ⟨1335854, by rfl⟩ : syracuseStep 1781139 = 2671709) B2671709
theorem B8555939 : Blo 1780091 8555939 := bstep (se 1 (by rfl) ⟨6416954, by rfl⟩ : syracuseStep 8555939 = 12833909) B12833909
theorem B1781155 : Blo 1780091 1781155 := bstep (se 1 (by rfl) ⟨1335866, by rfl⟩ : syracuseStep 1781155 = 2671733) B2671733
theorem B10030499 : Blo 1780091 10030499 := bstep (se 1 (by rfl) ⟨7522874, by rfl⟩ : syracuseStep 10030499 = 15045749) B15045749
theorem B1781171 : Blo 1780091 1781171 := bstep (se 1 (by rfl) ⟨1335878, by rfl⟩ : syracuseStep 1781171 = 2671757) B2671757
theorem B1781187 : Blo 1780091 1781187 := bstep (se 1 (by rfl) ⟨1335890, by rfl⟩ : syracuseStep 1781187 = 2671781) B2671781
theorem B1781203 : Blo 1780091 1781203 := bstep (se 1 (by rfl) ⟨1335902, by rfl⟩ : syracuseStep 1781203 = 2671805) B2671805
theorem B2854369 : Blo 1780091 2854369 := bstep (se 2 (by rfl) ⟨1070388, by rfl⟩ : syracuseStep 2854369 = 2140777) B2140777
theorem B1781219 : Blo 1780091 1781219 := bstep (se 1 (by rfl) ⟨1335914, by rfl⟩ : syracuseStep 1781219 = 2671829) B2671829
theorem B1781235 : Blo 1780091 1781235 := bstep (se 1 (by rfl) ⟨1335926, by rfl⟩ : syracuseStep 1781235 = 2671853) B2671853
theorem B1781251 : Blo 1780091 1781251 := bstep (se 1 (by rfl) ⟨1335938, by rfl⟩ : syracuseStep 1781251 = 2671877) B2671877
theorem B1781267 : Blo 1780091 1781267 := bstep (se 1 (by rfl) ⟨1335950, by rfl⟩ : syracuseStep 1781267 = 2671901) B2671901
theorem B1781283 : Blo 1780091 1781283 := bstep (se 1 (by rfl) ⟨1335962, by rfl⟩ : syracuseStep 1781283 = 2671925) B2671925
theorem B1781299 : Blo 1780091 1781299 := bstep (se 1 (by rfl) ⟨1335974, by rfl⟩ : syracuseStep 1781299 = 2671949) B2671949
theorem B1781315 : Blo 1780091 1781315 := bstep (se 1 (by rfl) ⟨1335986, by rfl⟩ : syracuseStep 1781315 = 2671973) B2671973
theorem B10145357 : Blo 1780091 10145357 := bstep (se 3 (by rfl) ⟨1902254, by rfl⟩ : syracuseStep 10145357 = 3804509) B3804509
theorem B2707025 : Blo 1780091 2707025 := bstep (se 2 (by rfl) ⟨1015134, by rfl⟩ : syracuseStep 2707025 = 2030269) B2030269
theorem B4009553 : Blo 1780091 4009553 := bstep (se 2 (by rfl) ⟨1503582, by rfl⟩ : syracuseStep 4009553 = 3007165) B3007165
theorem B1781331 : Blo 1780091 1781331 := bstep (se 1 (by rfl) ⟨1335998, by rfl⟩ : syracuseStep 1781331 = 2671997) B2671997
theorem B1781347 : Blo 1780091 1781347 := bstep (se 1 (by rfl) ⟨1336010, by rfl⟩ : syracuseStep 1781347 = 2672021) B2672021
theorem B4009571 : Blo 1780091 4009571 := bstep (se 1 (by rfl) ⟨3007178, by rfl⟩ : syracuseStep 4009571 = 6014357) B6014357
theorem B28880497 : Blo 1780091 28880497 := bstep (se 2 (by rfl) ⟨10830186, by rfl⟩ : syracuseStep 28880497 = 21660373) B21660373
theorem B5705329 : Blo 1780091 5705329 := bstep (se 2 (by rfl) ⟨2139498, by rfl⟩ : syracuseStep 5705329 = 4278997) B4278997
theorem B1781363 : Blo 1780091 1781363 := bstep (se 1 (by rfl) ⟨1336022, by rfl⟩ : syracuseStep 1781363 = 2672045) B2672045
theorem B1781379 : Blo 1780091 1781379 := bstep (se 1 (by rfl) ⟨1336034, by rfl⟩ : syracuseStep 1781379 = 2672069) B2672069
theorem B1781395 : Blo 1780091 1781395 := bstep (se 1 (by rfl) ⟨1336046, by rfl⟩ : syracuseStep 1781395 = 2672093) B2672093
theorem B1781411 : Blo 1780091 1781411 := bstep (se 1 (by rfl) ⟨1336058, by rfl⟩ : syracuseStep 1781411 = 2672117) B2672117
theorem B1781427 : Blo 1780091 1781427 := bstep (se 1 (by rfl) ⟨1336070, by rfl⟩ : syracuseStep 1781427 = 2672141) B2672141
theorem B1781443 : Blo 1780091 1781443 := bstep (se 1 (by rfl) ⟨1336082, by rfl⟩ : syracuseStep 1781443 = 2672165) B2672165
theorem B6008525 : Blo 1780091 6008525 := bstep (se 3 (by rfl) ⟨1126598, by rfl⟩ : syracuseStep 6008525 = 2253197) B2253197
theorem B1781459 : Blo 1780091 1781459 := bstep (se 1 (by rfl) ⟨1336094, by rfl⟩ : syracuseStep 1781459 = 2672189) B2672189
theorem B1781475 : Blo 1780091 1781475 := bstep (se 1 (by rfl) ⟨1336106, by rfl⟩ : syracuseStep 1781475 = 2672213) B2672213
theorem B2002675 : Blo 1780091 2002675 := bstep (se 1 (by rfl) ⟨1502006, by rfl⟩ : syracuseStep 2002675 = 3004013) B3004013
theorem B1781491 : Blo 1780091 1781491 := bstep (se 1 (by rfl) ⟨1336118, by rfl⟩ : syracuseStep 1781491 = 2672237) B2672237
theorem B6008579 : Blo 1780091 6008579 := bstep (se 1 (by rfl) ⟨4506434, by rfl⟩ : syracuseStep 6008579 = 9012869) B9012869
theorem B1781507 : Blo 1780091 1781507 := bstep (se 1 (by rfl) ⟨1336130, by rfl⟩ : syracuseStep 1781507 = 2672261) B2672261
theorem B1781523 : Blo 1780091 1781523 := bstep (se 1 (by rfl) ⟨1336142, by rfl⟩ : syracuseStep 1781523 = 2672285) B2672285
theorem B1781539 : Blo 1780091 1781539 := bstep (se 1 (by rfl) ⟨1336154, by rfl⟩ : syracuseStep 1781539 = 2672309) B2672309
theorem B1781555 : Blo 1780091 1781555 := bstep (se 1 (by rfl) ⟨1336166, by rfl⟩ : syracuseStep 1781555 = 2672333) B2672333
theorem B1781571 : Blo 1780091 1781571 := bstep (se 1 (by rfl) ⟨1336178, by rfl⟩ : syracuseStep 1781571 = 2672357) B2672357
theorem B1781587 : Blo 1780091 1781587 := bstep (se 1 (by rfl) ⟨1336190, by rfl⟩ : syracuseStep 1781587 = 2672381) B2672381
theorem B8343395 : Blo 1780091 8343395 := bstep (se 1 (by rfl) ⟨6257546, by rfl⟩ : syracuseStep 8343395 = 12515093) B12515093
theorem B1781603 : Blo 1780091 1781603 := bstep (se 1 (by rfl) ⟨1336202, by rfl⟩ : syracuseStep 1781603 = 2672405) B2672405
theorem B4509553 : Blo 1780091 4509553 := bstep (se 2 (by rfl) ⟨1691082, by rfl⟩ : syracuseStep 4509553 = 3382165) B3382165
theorem B1781619 : Blo 1780091 1781619 := bstep (se 1 (by rfl) ⟨1336214, by rfl⟩ : syracuseStep 1781619 = 2672429) B2672429
theorem B2002819 : Blo 1780091 2002819 := bstep (se 1 (by rfl) ⟨1502114, by rfl⟩ : syracuseStep 2002819 = 3004229) B3004229
theorem B1781635 : Blo 1780091 1781635 := bstep (se 1 (by rfl) ⟨1336226, by rfl⟩ : syracuseStep 1781635 = 2672453) B2672453
theorem B56323981 : Blo 1780091 56323981 := bstep (se 3 (by rfl) ⟨10560746, by rfl⟩ : syracuseStep 56323981 = 21121493) B21121493
theorem B3805073 : Blo 1780091 3805073 := bstep (se 2 (by rfl) ⟨1426902, by rfl⟩ : syracuseStep 3805073 = 2853805) B2853805
theorem B1781651 : Blo 1780091 1781651 := bstep (se 1 (by rfl) ⟨1336238, by rfl⟩ : syracuseStep 1781651 = 2672477) B2672477
theorem B1781667 : Blo 1780091 1781667 := bstep (se 1 (by rfl) ⟨1336250, by rfl⟩ : syracuseStep 1781667 = 2672501) B2672501
theorem B1781683 : Blo 1780091 1781683 := bstep (se 1 (by rfl) ⟨1336262, by rfl⟩ : syracuseStep 1781683 = 2672525) B2672525
theorem B1781699 : Blo 1780091 1781699 := bstep (se 1 (by rfl) ⟨1336274, by rfl⟩ : syracuseStep 1781699 = 2672549) B2672549
theorem B11407301 : Blo 1780091 11407301 := bstep (se 4 (by rfl) ⟨1069434, by rfl⟩ : syracuseStep 11407301 = 2138869) B2138869
theorem B1781715 : Blo 1780091 1781715 := bstep (se 1 (by rfl) ⟨1336286, by rfl⟩ : syracuseStep 1781715 = 2672573) B2672573
theorem B1781731 : Blo 1780091 1781731 := bstep (se 1 (by rfl) ⟨1336298, by rfl⟩ : syracuseStep 1781731 = 2672597) B2672597
theorem B1781747 : Blo 1780091 1781747 := bstep (se 1 (by rfl) ⟨1336310, by rfl⟩ : syracuseStep 1781747 = 2672621) B2672621
theorem B1781763 : Blo 1780091 1781763 := bstep (se 1 (by rfl) ⟨1336322, by rfl⟩ : syracuseStep 1781763 = 2672645) B2672645
theorem B6008849 : Blo 1780091 6008849 := bstep (se 2 (by rfl) ⟨2253318, by rfl⟩ : syracuseStep 6008849 = 4506637) B4506637
theorem B2002963 : Blo 1780091 2002963 := bstep (se 1 (by rfl) ⟨1502222, by rfl⟩ : syracuseStep 2002963 = 3004445) B3004445
theorem B1781779 : Blo 1780091 1781779 := bstep (se 1 (by rfl) ⟨1336334, by rfl⟩ : syracuseStep 1781779 = 2672669) B2672669
theorem B2535457 : Blo 1780091 2535457 := bstep (se 2 (by rfl) ⟨950796, by rfl⟩ : syracuseStep 2535457 = 1901593) B1901593
theorem B1781795 : Blo 1780091 1781795 := bstep (se 1 (by rfl) ⟨1336346, by rfl⟩ : syracuseStep 1781795 = 2672693) B2672693
theorem B1781811 : Blo 1780091 1781811 := bstep (se 1 (by rfl) ⟨1336358, by rfl⟩ : syracuseStep 1781811 = 2672717) B2672717
theorem B1781827 : Blo 1780091 1781827 := bstep (se 1 (by rfl) ⟨1336370, by rfl⟩ : syracuseStep 1781827 = 2672741) B2672741
theorem B1781843 : Blo 1780091 1781843 := bstep (se 1 (by rfl) ⟨1336382, by rfl⟩ : syracuseStep 1781843 = 2672765) B2672765
theorem B1781859 : Blo 1780091 1781859 := bstep (se 1 (by rfl) ⟨1336394, by rfl⟩ : syracuseStep 1781859 = 2672789) B2672789
theorem B1781875 : Blo 1780091 1781875 := bstep (se 1 (by rfl) ⟨1336406, by rfl⟩ : syracuseStep 1781875 = 2672813) B2672813
theorem B2535553 : Blo 1780091 2535553 := bstep (se 2 (by rfl) ⟨950832, by rfl⟩ : syracuseStep 2535553 = 1901665) B1901665
theorem B4509827 : Blo 1780091 4509827 := bstep (se 1 (by rfl) ⟨3382370, by rfl⟩ : syracuseStep 4509827 = 6764741) B6764741
theorem B1781891 : Blo 1780091 1781891 := bstep (se 1 (by rfl) ⟨1336418, by rfl⟩ : syracuseStep 1781891 = 2672837) B2672837
theorem B1781907 : Blo 1780091 1781907 := bstep (se 1 (by rfl) ⟨1336430, by rfl⟩ : syracuseStep 1781907 = 2672861) B2672861
theorem B2003107 : Blo 1780091 2003107 := bstep (se 1 (by rfl) ⟨1502330, by rfl⟩ : syracuseStep 2003107 = 3004661) B3004661
theorem B1781923 : Blo 1780091 1781923 := bstep (se 1 (by rfl) ⟨1336442, by rfl⟩ : syracuseStep 1781923 = 2672885) B2672885
theorem B5419181 : Blo 1780091 5419181 := bstep (se 3 (by rfl) ⟨1016096, by rfl⟩ : syracuseStep 5419181 = 2032193) B2032193
theorem B1781939 : Blo 1780091 1781939 := bstep (se 1 (by rfl) ⟨1336454, by rfl⟩ : syracuseStep 1781939 = 2672909) B2672909
theorem B1781955 : Blo 1780091 1781955 := bstep (se 1 (by rfl) ⟨1336466, by rfl⟩ : syracuseStep 1781955 = 2672933) B2672933
theorem B1781971 : Blo 1780091 1781971 := bstep (se 1 (by rfl) ⟨1336478, by rfl⟩ : syracuseStep 1781971 = 2672957) B2672957
theorem B4878563 : Blo 1780091 4878563 := bstep (se 1 (by rfl) ⟨3658922, by rfl⟩ : syracuseStep 4878563 = 7317845) B7317845
theorem B1781987 : Blo 1780091 1781987 := bstep (se 1 (by rfl) ⟨1336490, by rfl⟩ : syracuseStep 1781987 = 2672981) B2672981
theorem B12833009 : Blo 1780091 12833009 := bstep (se 2 (by rfl) ⟨4812378, by rfl⟩ : syracuseStep 12833009 = 9624757) B9624757
theorem B1782003 : Blo 1780091 1782003 := bstep (se 1 (by rfl) ⟨1336502, by rfl⟩ : syracuseStep 1782003 = 2673005) B2673005
theorem B1782019 : Blo 1780091 1782019 := bstep (se 1 (by rfl) ⟨1336514, by rfl⟩ : syracuseStep 1782019 = 2673029) B2673029
theorem B1782035 : Blo 1780091 1782035 := bstep (se 1 (by rfl) ⟨1336526, by rfl⟩ : syracuseStep 1782035 = 2673053) B2673053
theorem B1782051 : Blo 1780091 1782051 := bstep (se 1 (by rfl) ⟨1336538, by rfl⟩ : syracuseStep 1782051 = 2673077) B2673077
theorem B2003251 : Blo 1780091 2003251 := bstep (se 1 (by rfl) ⟨1502438, by rfl⟩ : syracuseStep 2003251 = 3004877) B3004877
theorem B1782067 : Blo 1780091 1782067 := bstep (se 1 (by rfl) ⟨1336550, by rfl⟩ : syracuseStep 1782067 = 2673101) B2673101
theorem B4510019 : Blo 1780091 4510019 := bstep (se 1 (by rfl) ⟨3382514, by rfl⟩ : syracuseStep 4510019 = 6765029) B6765029
theorem B1782083 : Blo 1780091 1782083 := bstep (se 1 (by rfl) ⟨1336562, by rfl⟩ : syracuseStep 1782083 = 2673125) B2673125
theorem B8556877 : Blo 1780091 8556877 := bstep (se 3 (by rfl) ⟨1604414, by rfl⟩ : syracuseStep 8556877 = 3208829) B3208829
theorem B5140849 : Blo 1780091 5140849 := bstep (se 2 (by rfl) ⟨1927818, by rfl⟩ : syracuseStep 5140849 = 3855637) B3855637
theorem B2003395 : Blo 1780091 2003395 := bstep (se 1 (by rfl) ⟨1502546, by rfl⟩ : syracuseStep 2003395 = 3005093) B3005093
theorem B17125829 : Blo 1780091 17125829 := bstep (se 4 (by rfl) ⟨1605546, by rfl⟩ : syracuseStep 17125829 = 3211093) B3211093
theorem B6091217 : Blo 1780091 6091217 := bstep (se 2 (by rfl) ⟨2284206, by rfl⟩ : syracuseStep 6091217 = 4568413) B4568413
theorem B6009389 : Blo 1780091 6009389 := bstep (se 3 (by rfl) ⟨1126760, by rfl⟩ : syracuseStep 6009389 = 2253521) B2253521
theorem B4280899 : Blo 1780091 4280899 := bstep (se 1 (by rfl) ⟨3210674, by rfl⟩ : syracuseStep 4280899 = 6421349) B6421349
theorem B20288069 : Blo 1780091 20288069 := bstep (se 4 (by rfl) ⟨1902006, by rfl⟩ : syracuseStep 20288069 = 3804013) B3804013
theorem B6763085 : Blo 1780091 6763085 := bstep (se 3 (by rfl) ⟨1268078, by rfl⟩ : syracuseStep 6763085 = 2536157) B2536157
theorem B2003539 : Blo 1780091 2003539 := bstep (se 1 (by rfl) ⟨1502654, by rfl⟩ : syracuseStep 2003539 = 3005309) B3005309
theorem B6009443 : Blo 1780091 6009443 := bstep (se 1 (by rfl) ⟨4507082, by rfl⟩ : syracuseStep 6009443 = 9014165) B9014165
theorem B4117105 : Blo 1780091 4117105 := bstep (se 2 (by rfl) ⟨1543914, by rfl⟩ : syracuseStep 4117105 = 3087829) B3087829
theorem B2536049 : Blo 1780091 2536049 := bstep (se 2 (by rfl) ⟨951018, by rfl⟩ : syracuseStep 2536049 = 1902037) B1902037
theorem B3805859 : Blo 1780091 3805859 := bstep (se 1 (by rfl) ⟨2854394, by rfl⟩ : syracuseStep 3805859 = 5708789) B5708789
theorem B2003683 : Blo 1780091 2003683 := bstep (se 1 (by rfl) ⟨1502762, by rfl⟩ : syracuseStep 2003683 = 3005525) B3005525
theorem B4281169 : Blo 1780091 4281169 := bstep (se 2 (by rfl) ⟨1605438, by rfl⟩ : syracuseStep 4281169 = 3210877) B3210877
theorem B6009713 : Blo 1780091 6009713 := bstep (se 2 (by rfl) ⟨2253642, by rfl⟩ : syracuseStep 6009713 = 4507285) B4507285
theorem B2003827 : Blo 1780091 2003827 := bstep (se 1 (by rfl) ⟨1502870, by rfl⟩ : syracuseStep 2003827 = 3005741) B3005741
theorem B15422405 : Blo 1780091 15422405 := bstep (se 4 (by rfl) ⟨1445850, by rfl⟩ : syracuseStep 15422405 = 2891701) B2891701
theorem B2003971 : Blo 1780091 2003971 := bstep (se 1 (by rfl) ⟨1502978, by rfl⟩ : syracuseStep 2003971 = 3005957) B3005957
theorem B10286129 : Blo 1780091 10286129 := bstep (se 2 (by rfl) ⟨3857298, by rfl⟩ : syracuseStep 10286129 = 7714597) B7714597
theorem B3380305 : Blo 1780091 3380305 := bstep (se 2 (by rfl) ⟨1267614, by rfl⟩ : syracuseStep 3380305 = 2535229) B2535229
theorem B9262193 : Blo 1780091 9262193 := bstep (se 2 (by rfl) ⟨3473322, by rfl⟩ : syracuseStep 9262193 = 6946645) B6946645
theorem B4813937 : Blo 1780091 4813937 := bstep (se 2 (by rfl) ⟨1805226, by rfl⟩ : syracuseStep 4813937 = 3610453) B3610453
theorem B9016433 : Blo 1780091 9016433 := bstep (se 2 (by rfl) ⟨3381162, by rfl⟩ : syracuseStep 9016433 = 6762325) B6762325
theorem B20296817 : Blo 1780091 20296817 := bstep (se 2 (by rfl) ⟨7611306, by rfl⟩ : syracuseStep 20296817 = 15222613) B15222613
theorem B2004115 : Blo 1780091 2004115 := bstep (se 1 (by rfl) ⟨1503086, by rfl⟩ : syracuseStep 2004115 = 3006173) B3006173
theorem B8123597 : Blo 1780091 8123597 := bstep (se 3 (by rfl) ⟨1523174, by rfl⟩ : syracuseStep 8123597 = 3046349) B3046349
theorem B3208483 : Blo 1780091 3208483 := bstep (se 1 (by rfl) ⟨2406362, by rfl⟩ : syracuseStep 3208483 = 4812725) B4812725
theorem B2004259 : Blo 1780091 2004259 := bstep (se 1 (by rfl) ⟨1503194, by rfl⟩ : syracuseStep 2004259 = 3006389) B3006389
theorem B8557937 : Blo 1780091 8557937 := bstep (se 2 (by rfl) ⟨3209226, by rfl⟩ : syracuseStep 8557937 = 6418453) B6418453
theorem B6010253 : Blo 1780091 6010253 := bstep (se 3 (by rfl) ⟨1126922, by rfl⟩ : syracuseStep 6010253 = 2253845) B2253845
theorem B2569651 : Blo 1780091 2569651 := bstep (se 1 (by rfl) ⟨1927238, by rfl⟩ : syracuseStep 2569651 = 3854477) B3854477
theorem B2004403 : Blo 1780091 2004403 := bstep (se 1 (by rfl) ⟨1503302, by rfl⟩ : syracuseStep 2004403 = 3006605) B3006605
theorem B6010307 : Blo 1780091 6010307 := bstep (se 1 (by rfl) ⟨4507730, by rfl⟩ : syracuseStep 6010307 = 9015461) B9015461
theorem B82294213 : Blo 1780091 82294213 := bstep (se 4 (by rfl) ⟨7715082, by rfl⟩ : syracuseStep 82294213 = 15430165) B15430165
theorem B2536915 : Blo 1780091 2536915 := bstep (se 1 (by rfl) ⟨1902686, by rfl⟩ : syracuseStep 2536915 = 3805373) B3805373
theorem B3380707 : Blo 1780091 3380707 := bstep (se 1 (by rfl) ⟨2535530, by rfl⟩ : syracuseStep 3380707 = 5071061) B5071061
theorem B3003905 : Blo 1780091 3003905 := bstep (se 2 (by rfl) ⟨1126464, by rfl⟩ : syracuseStep 3003905 = 2252929) B2252929
theorem B3380753 : Blo 1780091 3380753 := bstep (se 2 (by rfl) ⟨1267782, by rfl⟩ : syracuseStep 3380753 = 2535565) B2535565
theorem B8123939 : Blo 1780091 8123939 := bstep (se 1 (by rfl) ⟨6092954, by rfl⟩ : syracuseStep 8123939 = 12185909) B12185909
theorem B2537011 : Blo 1780091 2537011 := bstep (se 1 (by rfl) ⟨1902758, by rfl⟩ : syracuseStep 2537011 = 3805517) B3805517
theorem B2405953 : Blo 1780091 2405953 := bstep (se 2 (by rfl) ⟨902232, by rfl⟩ : syracuseStep 2405953 = 1804465) B1804465
theorem B2004547 : Blo 1780091 2004547 := bstep (se 1 (by rfl) ⟨1503410, by rfl⟩ : syracuseStep 2004547 = 3006821) B3006821
theorem B3044945 : Blo 1780091 3044945 := bstep (se 2 (by rfl) ⟨1141854, by rfl⟩ : syracuseStep 3044945 = 2283709) B2283709
theorem B2438755 : Blo 1780091 2438755 := bstep (se 1 (by rfl) ⟨1829066, by rfl⟩ : syracuseStep 2438755 = 3658133) B3658133
theorem B89028209 : Blo 1780091 89028209 := bstep (se 2 (by rfl) ⟨33385578, by rfl⟩ : syracuseStep 89028209 = 66771157) B66771157
theorem B3004033 : Blo 1780091 3004033 := bstep (se 2 (by rfl) ⟨1126512, by rfl⟩ : syracuseStep 3004033 = 2253025) B2253025
theorem B3004067 : Blo 1780091 3004067 := bstep (se 1 (by rfl) ⟨2253050, by rfl⟩ : syracuseStep 3004067 = 4506101) B4506101
theorem B6010577 : Blo 1780091 6010577 := bstep (se 2 (by rfl) ⟨2253966, by rfl⟩ : syracuseStep 6010577 = 4507933) B4507933
theorem B2004691 : Blo 1780091 2004691 := bstep (se 1 (by rfl) ⟨1503518, by rfl⟩ : syracuseStep 2004691 = 3007037) B3007037
theorem B10147589 : Blo 1780091 10147589 := bstep (se 4 (by rfl) ⟨951336, by rfl⟩ : syracuseStep 10147589 = 1902673) B1902673
theorem B3004195 : Blo 1780091 3004195 := bstep (se 1 (by rfl) ⟨2253146, by rfl⟩ : syracuseStep 3004195 = 4506293) B4506293
theorem B3381041 : Blo 1780091 3381041 := bstep (se 2 (by rfl) ⟨1267890, by rfl⟩ : syracuseStep 3381041 = 2535781) B2535781
theorem B30447413 : Blo 1780091 30447413 := bstep (se 5 (by rfl) ⟨1427222, by rfl⟩ : syracuseStep 30447413 = 2854445) B2854445
theorem B7608163 : Blo 1780091 7608163 := bstep (se 1 (by rfl) ⟨5706122, by rfl⟩ : syracuseStep 7608163 = 11412245) B11412245
theorem B2004835 : Blo 1780091 2004835 := bstep (se 1 (by rfl) ⟨1503626, by rfl⟩ : syracuseStep 2004835 = 3007253) B3007253
theorem B10139525 : Blo 1780091 10139525 := bstep (se 4 (by rfl) ⟨950580, by rfl⟩ : syracuseStep 10139525 = 1901161) B1901161
theorem B3004337 : Blo 1780091 3004337 := bstep (se 2 (by rfl) ⟨1126626, by rfl⟩ : syracuseStep 3004337 = 2253253) B2253253
theorem B4569059 : Blo 1780091 4569059 := bstep (se 1 (by rfl) ⟨3426794, by rfl⟩ : syracuseStep 4569059 = 6853589) B6853589
theorem B3004465 : Blo 1780091 3004465 := bstep (se 2 (by rfl) ⟨1126674, by rfl⟩ : syracuseStep 3004465 = 2253349) B2253349
theorem B9762893 : Blo 1780091 9762893 := bstep (se 3 (by rfl) ⟨1830542, by rfl⟩ : syracuseStep 9762893 = 3661085) B3661085
theorem B3004499 : Blo 1780091 3004499 := bstep (se 1 (by rfl) ⟨2253374, by rfl⟩ : syracuseStep 3004499 = 4506749) B4506749
theorem B24369349 : Blo 1780091 24369349 := bstep (se 4 (by rfl) ⟨2284626, by rfl⟩ : syracuseStep 24369349 = 4569253) B4569253
theorem B3004627 : Blo 1780091 3004627 := bstep (se 1 (by rfl) ⟨2253470, by rfl⟩ : syracuseStep 3004627 = 4506941) B4506941
theorem B25663715 : Blo 1780091 25663715 := bstep (se 1 (by rfl) ⟨19247786, by rfl⟩ : syracuseStep 25663715 = 38495573) B38495573
theorem B6011117 : Blo 1780091 6011117 := bstep (se 3 (by rfl) ⟨1127084, by rfl⟩ : syracuseStep 6011117 = 2254169) B2254169
theorem B6011171 : Blo 1780091 6011171 := bstep (se 1 (by rfl) ⟨4508378, by rfl⟩ : syracuseStep 6011171 = 9016757) B9016757
theorem B3004769 : Blo 1780091 3004769 := bstep (se 2 (by rfl) ⟨1126788, by rfl⟩ : syracuseStep 3004769 = 2253577) B2253577
theorem B5708173 : Blo 1780091 5708173 := bstep (se 3 (by rfl) ⟨1070282, by rfl⟩ : syracuseStep 5708173 = 2140565) B2140565
theorem B10148273 : Blo 1780091 10148273 := bstep (se 2 (by rfl) ⟨3805602, by rfl⟩ : syracuseStep 10148273 = 7611205) B7611205
theorem B3004897 : Blo 1780091 3004897 := bstep (se 2 (by rfl) ⟨1126836, by rfl⟩ : syracuseStep 3004897 = 2253673) B2253673
theorem B3004931 : Blo 1780091 3004931 := bstep (se 1 (by rfl) ⟨2253698, by rfl⟩ : syracuseStep 3004931 = 4507397) B4507397
theorem B3381763 : Blo 1780091 3381763 := bstep (se 1 (by rfl) ⟨2536322, by rfl⟩ : syracuseStep 3381763 = 5072645) B5072645
theorem B6855203 : Blo 1780091 6855203 := bstep (se 1 (by rfl) ⟨5141402, by rfl⟩ : syracuseStep 6855203 = 10282805) B10282805
theorem B9017891 : Blo 1780091 9017891 := bstep (se 1 (by rfl) ⟨6763418, by rfl⟩ : syracuseStep 9017891 = 13526837) B13526837
theorem B6011441 : Blo 1780091 6011441 := bstep (se 2 (by rfl) ⟨2254290, by rfl⟩ : syracuseStep 6011441 = 4508581) B4508581
theorem B3005059 : Blo 1780091 3005059 := bstep (se 1 (by rfl) ⟨2253794, by rfl⟩ : syracuseStep 3005059 = 4507589) B4507589
theorem B11418245 : Blo 1780091 11418245 := bstep (se 4 (by rfl) ⟨1070460, by rfl⟩ : syracuseStep 11418245 = 2140921) B2140921
theorem B4815569 : Blo 1780091 4815569 := bstep (se 2 (by rfl) ⟨1805838, by rfl⟩ : syracuseStep 4815569 = 3611677) B3611677
theorem B5143277 : Blo 1780091 5143277 := bstep (se 3 (by rfl) ⟨964364, by rfl⟩ : syracuseStep 5143277 = 1928729) B1928729
theorem B9263857 : Blo 1780091 9263857 := bstep (se 2 (by rfl) ⟨3473946, by rfl⟩ : syracuseStep 9263857 = 6947893) B6947893
theorem B2407153 : Blo 1780091 2407153 := bstep (se 2 (by rfl) ⟨902682, by rfl⟩ : syracuseStep 2407153 = 1805365) B1805365
theorem B3005201 : Blo 1780091 3005201 := bstep (se 2 (by rfl) ⟨1126950, by rfl⟩ : syracuseStep 3005201 = 2253901) B2253901
theorem B5069603 : Blo 1780091 5069603 := bstep (se 1 (by rfl) ⟨3802202, by rfl⟩ : syracuseStep 5069603 = 7604405) B7604405
theorem B3005329 : Blo 1780091 3005329 := bstep (se 2 (by rfl) ⟨1126998, by rfl⟩ : syracuseStep 3005329 = 2253997) B2253997
theorem B3005363 : Blo 1780091 3005363 := bstep (se 1 (by rfl) ⟨2254022, by rfl⟩ : syracuseStep 3005363 = 4508045) B4508045
theorem B3382211 : Blo 1780091 3382211 := bstep (se 1 (by rfl) ⟨2536658, by rfl⟩ : syracuseStep 3382211 = 5073317) B5073317
theorem B10705861 : Blo 1780091 10705861 := bstep (se 4 (by rfl) ⟨1003674, by rfl⟩ : syracuseStep 10705861 = 2007349) B2007349
theorem B31267781 : Blo 1780091 31267781 := bstep (se 4 (by rfl) ⟨2931354, by rfl⟩ : syracuseStep 31267781 = 5862709) B5862709
theorem B2407379 : Blo 1780091 2407379 := bstep (se 1 (by rfl) ⟨1805534, by rfl⟩ : syracuseStep 2407379 = 3611069) B3611069
theorem B7609393 : Blo 1780091 7609393 := bstep (se 2 (by rfl) ⟨2853522, by rfl⟩ : syracuseStep 7609393 = 5707045) B5707045
theorem B3005491 : Blo 1780091 3005491 := bstep (se 1 (by rfl) ⟨2254118, by rfl⟩ : syracuseStep 3005491 = 4508237) B4508237
theorem B6011981 : Blo 1780091 6011981 := bstep (se 3 (by rfl) ⟨1127246, by rfl⟩ : syracuseStep 6011981 = 2254493) B2254493
theorem B4815949 : Blo 1780091 4815949 := bstep (se 3 (by rfl) ⟨902990, by rfl⟩ : syracuseStep 4815949 = 1805981) B1805981
theorem B6012035 : Blo 1780091 6012035 := bstep (se 1 (by rfl) ⟨4509026, by rfl⟩ : syracuseStep 6012035 = 9018053) B9018053
theorem B3005633 : Blo 1780091 3005633 := bstep (se 2 (by rfl) ⟨1127112, by rfl⟩ : syracuseStep 3005633 = 2254225) B2254225
theorem B4881635 : Blo 1780091 4881635 := bstep (se 1 (by rfl) ⟨3661226, by rfl⟩ : syracuseStep 4881635 = 7322453) B7322453
theorem B3382499 : Blo 1780091 3382499 := bstep (se 1 (by rfl) ⟨2536874, by rfl⟩ : syracuseStep 3382499 = 5073749) B5073749
theorem B3005761 : Blo 1780091 3005761 := bstep (se 2 (by rfl) ⟨1127160, by rfl⟩ : syracuseStep 3005761 = 2254321) B2254321
theorem B9018701 : Blo 1780091 9018701 := bstep (se 3 (by rfl) ⟨1691006, by rfl⟩ : syracuseStep 9018701 = 3382013) B3382013
theorem B7224653 : Blo 1780091 7224653 := bstep (se 3 (by rfl) ⟨1354622, by rfl⟩ : syracuseStep 7224653 = 2709245) B2709245
theorem B3005795 : Blo 1780091 3005795 := bstep (se 1 (by rfl) ⟨2254346, by rfl⟩ : syracuseStep 3005795 = 4508693) B4508693
theorem B4005233 : Blo 1780091 4005233 := bstep (se 2 (by rfl) ⟨1501962, by rfl⟩ : syracuseStep 4005233 = 3003925) B3003925
theorem B4005251 : Blo 1780091 4005251 := bstep (se 1 (by rfl) ⟨3003938, by rfl⟩ : syracuseStep 4005251 = 6007877) B6007877
theorem B6012305 : Blo 1780091 6012305 := bstep (se 2 (by rfl) ⟨2254614, by rfl⟩ : syracuseStep 6012305 = 4509229) B4509229
theorem B6766001 : Blo 1780091 6766001 := bstep (se 2 (by rfl) ⟨2537250, by rfl⟩ : syracuseStep 6766001 = 5074501) B5074501
theorem B3005923 : Blo 1780091 3005923 := bstep (se 1 (by rfl) ⟨2254442, by rfl⟩ : syracuseStep 3005923 = 4508885) B4508885
theorem B2670161 : Blo 1780091 2670161 := bstep (se 2 (by rfl) ⟨1001310, by rfl⟩ : syracuseStep 2670161 = 2002621) B2002621
theorem B2670179 : Blo 1780091 2670179 := bstep (se 1 (by rfl) ⟨2002634, by rfl⟩ : syracuseStep 2670179 = 4005269) B4005269
theorem B3006065 : Blo 1780091 3006065 := bstep (se 2 (by rfl) ⟨1127274, by rfl⟩ : syracuseStep 3006065 = 2254549) B2254549
theorem B2670209 : Blo 1780091 2670209 := bstep (se 2 (by rfl) ⟨1001328, by rfl⟩ : syracuseStep 2670209 = 2002657) B2002657
theorem B4005521 : Blo 1780091 4005521 := bstep (se 2 (by rfl) ⟨1502070, by rfl⟩ : syracuseStep 4005521 = 3004141) B3004141
theorem B2670227 : Blo 1780091 2670227 := bstep (se 1 (by rfl) ⟨2002670, by rfl⟩ : syracuseStep 2670227 = 4005341) B4005341
theorem B4005539 : Blo 1780091 4005539 := bstep (se 1 (by rfl) ⟨3004154, by rfl⟩ : syracuseStep 4005539 = 6008309) B6008309
theorem B2670257 : Blo 1780091 2670257 := bstep (se 2 (by rfl) ⟨1001346, by rfl⟩ : syracuseStep 2670257 = 2002693) B2002693
theorem B2670275 : Blo 1780091 2670275 := bstep (se 1 (by rfl) ⟨2002706, by rfl⟩ : syracuseStep 2670275 = 4005413) B4005413
theorem B2408131 : Blo 1780091 2408131 := bstep (se 1 (by rfl) ⟨1806098, by rfl⟩ : syracuseStep 2408131 = 3612197) B3612197
theorem B2670305 : Blo 1780091 2670305 := bstep (se 2 (by rfl) ⟨1001364, by rfl⟩ : syracuseStep 2670305 = 2002729) B2002729
theorem B3006193 : Blo 1780091 3006193 := bstep (se 2 (by rfl) ⟨1127322, by rfl⟩ : syracuseStep 3006193 = 2254645) B2254645
theorem B2670323 : Blo 1780091 2670323 := bstep (se 1 (by rfl) ⟨2002742, by rfl⟩ : syracuseStep 2670323 = 4005485) B4005485
theorem B8560397 : Blo 1780091 8560397 := bstep (se 3 (by rfl) ⟨1605074, by rfl⟩ : syracuseStep 8560397 = 3210149) B3210149
theorem B2670353 : Blo 1780091 2670353 := bstep (se 2 (by rfl) ⟨1001382, by rfl⟩ : syracuseStep 2670353 = 2002765) B2002765
theorem B3006227 : Blo 1780091 3006227 := bstep (se 1 (by rfl) ⟨2254670, by rfl⟩ : syracuseStep 3006227 = 4509341) B4509341
theorem B2670371 : Blo 1780091 2670371 := bstep (se 1 (by rfl) ⟨2002778, by rfl⟩ : syracuseStep 2670371 = 4005557) B4005557
theorem B5414705 : Blo 1780091 5414705 := bstep (se 2 (by rfl) ⟨2030514, by rfl⟩ : syracuseStep 5414705 = 4061029) B4061029
theorem B2670401 : Blo 1780091 2670401 := bstep (se 2 (by rfl) ⟨1001400, by rfl⟩ : syracuseStep 2670401 = 2002801) B2002801
theorem B2031427 : Blo 1780091 2031427 := bstep (se 1 (by rfl) ⟨1523570, by rfl⟩ : syracuseStep 2031427 = 3047141) B3047141
theorem B14450501 : Blo 1780091 14450501 := bstep (se 4 (by rfl) ⟨1354734, by rfl⟩ : syracuseStep 14450501 = 2709469) B2709469
theorem B2670419 : Blo 1780091 2670419 := bstep (se 1 (by rfl) ⟨2002814, by rfl⟩ : syracuseStep 2670419 = 4005629) B4005629
theorem B9756515 : Blo 1780091 9756515 := bstep (se 1 (by rfl) ⟨7317386, by rfl⟩ : syracuseStep 9756515 = 14634773) B14634773
theorem B2670449 : Blo 1780091 2670449 := bstep (se 2 (by rfl) ⟨1001418, by rfl⟩ : syracuseStep 2670449 = 2002837) B2002837
theorem B3612529 : Blo 1780091 3612529 := bstep (se 2 (by rfl) ⟨1354698, by rfl⟩ : syracuseStep 3612529 = 2709397) B2709397
theorem B2670467 : Blo 1780091 2670467 := bstep (se 1 (by rfl) ⟨2002850, by rfl⟩ : syracuseStep 2670467 = 4005701) B4005701
theorem B3006355 : Blo 1780091 3006355 := bstep (se 1 (by rfl) ⟨2254766, by rfl⟩ : syracuseStep 3006355 = 4509533) B4509533
theorem B2670497 : Blo 1780091 2670497 := bstep (se 2 (by rfl) ⟨1001436, by rfl⟩ : syracuseStep 2670497 = 2002873) B2002873
theorem B6012845 : Blo 1780091 6012845 := bstep (se 3 (by rfl) ⟨1127408, by rfl⟩ : syracuseStep 6012845 = 2254817) B2254817
theorem B4005809 : Blo 1780091 4005809 := bstep (se 2 (by rfl) ⟨1502178, by rfl⟩ : syracuseStep 4005809 = 3004357) B3004357
theorem B2670515 : Blo 1780091 2670515 := bstep (se 1 (by rfl) ⟨2002886, by rfl⟩ : syracuseStep 2670515 = 4005773) B4005773
theorem B4005827 : Blo 1780091 4005827 := bstep (se 1 (by rfl) ⟨3004370, by rfl⟩ : syracuseStep 4005827 = 6008741) B6008741
theorem B2670545 : Blo 1780091 2670545 := bstep (se 2 (by rfl) ⟨1001454, by rfl⟩ : syracuseStep 2670545 = 2002909) B2002909
theorem B2670563 : Blo 1780091 2670563 := bstep (se 1 (by rfl) ⟨2002922, by rfl⟩ : syracuseStep 2670563 = 4005845) B4005845
theorem B6012899 : Blo 1780091 6012899 := bstep (se 1 (by rfl) ⟨4509674, by rfl⟩ : syracuseStep 6012899 = 9019349) B9019349
theorem B5070833 : Blo 1780091 5070833 := bstep (se 2 (by rfl) ⟨1901562, by rfl⟩ : syracuseStep 5070833 = 3803125) B3803125
theorem B4005899 : Blo 1780091 4005899 := bstep (se 1 (by rfl) ⟨3004424, by rfl⟩ : syracuseStep 4005899 = 6008849) B6008849
theorem B2670617 : Blo 1780091 2670617 := bstep (se 2 (by rfl) ⟨1001481, by rfl⟩ : syracuseStep 2670617 = 2002963) B2002963
theorem B4005953 : Blo 1780091 4005953 := bstep (se 2 (by rfl) ⟨1502232, by rfl⟩ : syracuseStep 4005953 = 3004465) B3004465
theorem B3211339 : Blo 1780091 3211339 := bstep (se 1 (by rfl) ⟨2408504, by rfl⟩ : syracuseStep 3211339 = 4817009) B4817009
theorem B3006551 : Blo 1780091 3006551 := bstep (se 1 (by rfl) ⟨2254913, by rfl⟩ : syracuseStep 3006551 = 4509827) B4509827
theorem B2670731 : Blo 1780091 2670731 := bstep (se 1 (by rfl) ⟨2003048, by rfl⟩ : syracuseStep 2670731 = 4006097) B4006097
theorem B2670743 : Blo 1780091 2670743 := bstep (se 1 (by rfl) ⟨2003057, by rfl⟩ : syracuseStep 2670743 = 4006115) B4006115
theorem B3006679 : Blo 1780091 3006679 := bstep (se 1 (by rfl) ⟨2255009, by rfl⟩ : syracuseStep 3006679 = 4510019) B4510019
theorem B2670809 : Blo 1780091 2670809 := bstep (se 2 (by rfl) ⟨1001553, by rfl⟩ : syracuseStep 2670809 = 2003107) B2003107
theorem B4006169 : Blo 1780091 4006169 := bstep (se 2 (by rfl) ⟨1502313, by rfl⟩ : syracuseStep 4006169 = 3004627) B3004627
theorem B24699181 : Blo 1780091 24699181 := bstep (se 3 (by rfl) ⟨4631096, by rfl⟩ : syracuseStep 24699181 = 9262193) B9262193
theorem B2670923 : Blo 1780091 2670923 := bstep (se 1 (by rfl) ⟨2003192, by rfl⟩ : syracuseStep 2670923 = 4006385) B4006385
theorem B2670935 : Blo 1780091 2670935 := bstep (se 1 (by rfl) ⟨2003201, by rfl⟩ : syracuseStep 2670935 = 4006403) B4006403
theorem B6013277 : Blo 1780091 6013277 := bstep (se 3 (by rfl) ⟨1127489, by rfl⟩ : syracuseStep 6013277 = 2254979) B2254979
theorem B4006259 : Blo 1780091 4006259 := bstep (se 1 (by rfl) ⟨3004694, by rfl⟩ : syracuseStep 4006259 = 6009389) B6009389
theorem B13525379 : Blo 1780091 13525379 := bstep (se 1 (by rfl) ⟨10144034, by rfl⟩ : syracuseStep 13525379 = 20288069) B20288069
theorem B4006295 : Blo 1780091 4006295 := bstep (se 1 (by rfl) ⟨3004721, by rfl⟩ : syracuseStep 4006295 = 6009443) B6009443
theorem B2671001 : Blo 1780091 2671001 := bstep (se 2 (by rfl) ⟨1001625, by rfl⟩ : syracuseStep 2671001 = 2003251) B2003251
theorem B14451149 : Blo 1780091 14451149 := bstep (se 3 (by rfl) ⟨2709590, by rfl⟩ : syracuseStep 14451149 = 5419181) B5419181
theorem B2671115 : Blo 1780091 2671115 := bstep (se 1 (by rfl) ⟨2003336, by rfl⟩ : syracuseStep 2671115 = 4006673) B4006673
theorem B7610897 : Blo 1780091 7610897 := bstep (se 2 (by rfl) ⟨2854086, by rfl⟩ : syracuseStep 7610897 = 5708173) B5708173
theorem B2671127 : Blo 1780091 2671127 := bstep (se 1 (by rfl) ⟨2003345, by rfl⟩ : syracuseStep 2671127 = 4006691) B4006691
theorem B4006475 : Blo 1780091 4006475 := bstep (se 1 (by rfl) ⟨3004856, by rfl⟩ : syracuseStep 4006475 = 6009713) B6009713
theorem B2671193 : Blo 1780091 2671193 := bstep (se 2 (by rfl) ⟨1001697, by rfl⟩ : syracuseStep 2671193 = 2003395) B2003395
theorem B13009501 : Blo 1780091 13009501 := bstep (se 3 (by rfl) ⟨2439281, by rfl⟩ : syracuseStep 13009501 = 4878563) B4878563
theorem B9019997 : Blo 1780091 9019997 := bstep (se 3 (by rfl) ⟨1691249, by rfl⟩ : syracuseStep 9019997 = 3382499) B3382499
theorem B4006529 : Blo 1780091 4006529 := bstep (se 2 (by rfl) ⟨1502448, by rfl⟩ : syracuseStep 4006529 = 3004897) B3004897
theorem B4506263 : Blo 1780091 4506263 := bstep (se 1 (by rfl) ⟨3379697, by rfl⟩ : syracuseStep 4506263 = 6759395) B6759395
theorem B2671307 : Blo 1780091 2671307 := bstep (se 1 (by rfl) ⟨2003480, by rfl⟩ : syracuseStep 2671307 = 4006961) B4006961
theorem B6857419 : Blo 1780091 6857419 := bstep (se 1 (by rfl) ⟨5143064, by rfl⟩ : syracuseStep 6857419 = 10286129) B10286129
theorem B2671319 : Blo 1780091 2671319 := bstep (se 1 (by rfl) ⟨2003489, by rfl⟩ : syracuseStep 2671319 = 4006979) B4006979
theorem B2671385 : Blo 1780091 2671385 := bstep (se 2 (by rfl) ⟨1001769, by rfl⟩ : syracuseStep 2671385 = 2003539) B2003539
theorem B13517603 : Blo 1780091 13517603 := bstep (se 1 (by rfl) ⟨10138202, by rfl⟩ : syracuseStep 13517603 = 20276405) B20276405
theorem B5415731 : Blo 1780091 5415731 := bstep (se 1 (by rfl) ⟨4061798, by rfl⟩ : syracuseStep 5415731 = 8123597) B8123597
theorem B104137525 : Blo 1780091 104137525 := bstep (se 5 (by rfl) ⟨4881446, by rfl⟩ : syracuseStep 104137525 = 9762893) B9762893
theorem B5489473 : Blo 1780091 5489473 := bstep (se 2 (by rfl) ⟨2058552, by rfl⟩ : syracuseStep 5489473 = 4117105) B4117105
theorem B4006745 : Blo 1780091 4006745 := bstep (se 2 (by rfl) ⟨1502529, by rfl⟩ : syracuseStep 4006745 = 3005059) B3005059
theorem B2851723 : Blo 1780091 2851723 := bstep (se 1 (by rfl) ⟨2138792, by rfl⟩ : syracuseStep 2851723 = 4277585) B4277585
theorem B2671499 : Blo 1780091 2671499 := bstep (se 1 (by rfl) ⟨2003624, by rfl⟩ : syracuseStep 2671499 = 4007249) B4007249
theorem B2671511 : Blo 1780091 2671511 := bstep (se 1 (by rfl) ⟨2003633, by rfl⟩ : syracuseStep 2671511 = 4007267) B4007267
theorem B4006835 : Blo 1780091 4006835 := bstep (se 1 (by rfl) ⟨3005126, by rfl⟩ : syracuseStep 4006835 = 6010253) B6010253
theorem B3802049 : Blo 1780091 3802049 := bstep (se 2 (by rfl) ⟨1425768, by rfl⟩ : syracuseStep 3802049 = 2851537) B2851537
theorem B4006871 : Blo 1780091 4006871 := bstep (se 1 (by rfl) ⟨3005153, by rfl⟩ : syracuseStep 4006871 = 6010307) B6010307
theorem B2671577 : Blo 1780091 2671577 := bstep (se 2 (by rfl) ⟨1001841, by rfl⟩ : syracuseStep 2671577 = 2003683) B2003683
theorem B23462873 : Blo 1780091 23462873 := bstep (se 2 (by rfl) ⟨8798577, by rfl⟩ : syracuseStep 23462873 = 17597155) B17597155
theorem B2253835 : Blo 1780091 2253835 := bstep (se 1 (by rfl) ⟨1690376, by rfl⟩ : syracuseStep 2253835 = 3380753) B3380753
theorem B5415959 : Blo 1780091 5415959 := bstep (se 1 (by rfl) ⟨4061969, by rfl⟩ : syracuseStep 5415959 = 8123939) B8123939
theorem B59352139 : Blo 1780091 59352139 := bstep (se 1 (by rfl) ⟨44514104, by rfl⟩ : syracuseStep 59352139 = 89028209) B89028209
theorem B2671691 : Blo 1780091 2671691 := bstep (se 1 (by rfl) ⟨2003768, by rfl⟩ : syracuseStep 2671691 = 4007537) B4007537
theorem B2671703 : Blo 1780091 2671703 := bstep (se 1 (by rfl) ⟨2003777, by rfl⟩ : syracuseStep 2671703 = 4007555) B4007555
theorem B4007051 : Blo 1780091 4007051 := bstep (se 1 (by rfl) ⟨3005288, by rfl⟩ : syracuseStep 4007051 = 6010577) B6010577
theorem B2671769 : Blo 1780091 2671769 := bstep (se 2 (by rfl) ⟨1001913, by rfl⟩ : syracuseStep 2671769 = 2003827) B2003827
theorem B4007105 : Blo 1780091 4007105 := bstep (se 2 (by rfl) ⟨1502664, by rfl⟩ : syracuseStep 4007105 = 3005329) B3005329
theorem B6759683 : Blo 1780091 6759683 := bstep (se 1 (by rfl) ⟨5069762, by rfl⟩ : syracuseStep 6759683 = 10139525) B10139525
theorem B2671883 : Blo 1780091 2671883 := bstep (se 1 (by rfl) ⟨2003912, by rfl⟩ : syracuseStep 2671883 = 4007825) B4007825
theorem B2671895 : Blo 1780091 2671895 := bstep (se 1 (by rfl) ⟨2003921, by rfl⟩ : syracuseStep 2671895 = 4007843) B4007843
theorem B9012545 : Blo 1780091 9012545 := bstep (se 2 (by rfl) ⟨3379704, by rfl⟩ : syracuseStep 9012545 = 6759409) B6759409
theorem B2671961 : Blo 1780091 2671961 := bstep (se 2 (by rfl) ⟨1001985, by rfl⟩ : syracuseStep 2671961 = 2003971) B2003971
theorem B4007321 : Blo 1780091 4007321 := bstep (se 2 (by rfl) ⟨1502745, by rfl⟩ : syracuseStep 4007321 = 3005491) B3005491
theorem B4507073 : Blo 1780091 4507073 := bstep (se 2 (by rfl) ⟨1690152, by rfl⟩ : syracuseStep 4507073 = 3380305) B3380305
theorem B2672075 : Blo 1780091 2672075 := bstep (se 1 (by rfl) ⟨2004056, by rfl⟩ : syracuseStep 2672075 = 4008113) B4008113
theorem B6014411 : Blo 1780091 6014411 := bstep (se 1 (by rfl) ⟨4510808, by rfl⟩ : syracuseStep 6014411 = 9021617) B9021617
theorem B2672087 : Blo 1780091 2672087 := bstep (se 1 (by rfl) ⟨2004065, by rfl⟩ : syracuseStep 2672087 = 4008131) B4008131
theorem B4007411 : Blo 1780091 4007411 := bstep (se 1 (by rfl) ⟨3005558, by rfl⟩ : syracuseStep 4007411 = 6011117) B6011117
theorem B4007447 : Blo 1780091 4007447 := bstep (se 1 (by rfl) ⟨3005585, by rfl⟩ : syracuseStep 4007447 = 6011171) B6011171
theorem B2672153 : Blo 1780091 2672153 := bstep (se 2 (by rfl) ⟨1002057, by rfl⟩ : syracuseStep 2672153 = 2004115) B2004115
theorem B8119853 : Blo 1780091 8119853 := bstep (se 3 (by rfl) ⟨1522472, by rfl⟩ : syracuseStep 8119853 = 3044945) B3044945
theorem B7218733 : Blo 1780091 7218733 := bstep (se 3 (by rfl) ⟨1353512, by rfl⟩ : syracuseStep 7218733 = 2707025) B2707025
theorem B5072473 : Blo 1780091 5072473 := bstep (se 2 (by rfl) ⟨1902177, by rfl⟩ : syracuseStep 5072473 = 3804355) B3804355
theorem B2672267 : Blo 1780091 2672267 := bstep (se 1 (by rfl) ⟨2004200, by rfl⟩ : syracuseStep 2672267 = 4008401) B4008401
theorem B2672279 : Blo 1780091 2672279 := bstep (se 1 (by rfl) ⟨2004209, by rfl⟩ : syracuseStep 2672279 = 4008419) B4008419
theorem B4277939 : Blo 1780091 4277939 := bstep (se 1 (by rfl) ⟨3208454, by rfl⟩ : syracuseStep 4277939 = 6416909) B6416909
theorem B1902263 : Blo 1780091 1902263 := bstep (se 1 (by rfl) ⟨1426697, by rfl⟩ : syracuseStep 1902263 = 2853395) B2853395
theorem B4007627 : Blo 1780091 4007627 := bstep (se 1 (by rfl) ⟨3005720, by rfl⟩ : syracuseStep 4007627 = 6011441) B6011441
theorem B4277977 : Blo 1780091 4277977 := bstep (se 2 (by rfl) ⟨1604241, by rfl⟩ : syracuseStep 4277977 = 3208483) B3208483
theorem B2672345 : Blo 1780091 2672345 := bstep (se 2 (by rfl) ⟨1002129, by rfl⟩ : syracuseStep 2672345 = 2004259) B2004259
theorem B4007681 : Blo 1780091 4007681 := bstep (se 2 (by rfl) ⟨1502880, by rfl⟩ : syracuseStep 4007681 = 3005761) B3005761
theorem B7612163 : Blo 1780091 7612163 := bstep (se 1 (by rfl) ⟨5709122, by rfl⟩ : syracuseStep 7612163 = 11418245) B11418245
theorem B21661505 : Blo 1780091 21661505 := bstep (se 2 (by rfl) ⟨8123064, by rfl⟩ : syracuseStep 21661505 = 16246129) B16246129
theorem B2672459 : Blo 1780091 2672459 := bstep (se 1 (by rfl) ⟨2004344, by rfl⟩ : syracuseStep 2672459 = 4008689) B4008689
theorem B2672471 : Blo 1780091 2672471 := bstep (se 1 (by rfl) ⟨2004353, by rfl⟩ : syracuseStep 2672471 = 4008707) B4008707
theorem B30861157 : Blo 1780091 30861157 := bstep (se 4 (by rfl) ⟨2893233, by rfl⟩ : syracuseStep 30861157 = 5786467) B5786467
theorem B2672537 : Blo 1780091 2672537 := bstep (se 2 (by rfl) ⟨1002201, by rfl⟩ : syracuseStep 2672537 = 2004403) B2004403
theorem B109725617 : Blo 1780091 109725617 := bstep (se 2 (by rfl) ⟨41147106, by rfl⟩ : syracuseStep 109725617 = 82294213) B82294213
theorem B13715405 : Blo 1780091 13715405 := bstep (se 3 (by rfl) ⟨2571638, by rfl⟩ : syracuseStep 13715405 = 5143277) B5143277
theorem B2254807 : Blo 1780091 2254807 := bstep (se 1 (by rfl) ⟨1691105, by rfl⟩ : syracuseStep 2254807 = 3382211) B3382211
theorem B4507609 : Blo 1780091 4507609 := bstep (se 2 (by rfl) ⟨1690353, by rfl⟩ : syracuseStep 4507609 = 3380707) B3380707
theorem B4007897 : Blo 1780091 4007897 := bstep (se 2 (by rfl) ⟨1502961, by rfl⟩ : syracuseStep 4007897 = 3005923) B3005923
theorem B5072861 : Blo 1780091 5072861 := bstep (se 3 (by rfl) ⟨951161, by rfl⟩ : syracuseStep 5072861 = 1902323) B1902323
theorem B2672651 : Blo 1780091 2672651 := bstep (se 1 (by rfl) ⟨2004488, by rfl⟩ : syracuseStep 2672651 = 4008977) B4008977
theorem B3803159 : Blo 1780091 3803159 := bstep (se 1 (by rfl) ⟨2852369, by rfl⟩ : syracuseStep 3803159 = 5704739) B5704739
theorem B2672663 : Blo 1780091 2672663 := bstep (se 1 (by rfl) ⟨2004497, by rfl⟩ : syracuseStep 2672663 = 4008995) B4008995
theorem B4007987 : Blo 1780091 4007987 := bstep (se 1 (by rfl) ⟨3005990, by rfl⟩ : syracuseStep 4007987 = 6011981) B6011981
theorem B300394565 : Blo 1780091 300394565 := bstep (se 4 (by rfl) ⟨28161990, by rfl⟩ : syracuseStep 300394565 = 56323981) B56323981
theorem B4008023 : Blo 1780091 4008023 := bstep (se 1 (by rfl) ⟨3006017, by rfl⟩ : syracuseStep 4008023 = 6012035) B6012035
theorem B2672729 : Blo 1780091 2672729 := bstep (se 2 (by rfl) ⟨1002273, by rfl⟩ : syracuseStep 2672729 = 2004547) B2004547
theorem B3254423 : Blo 1780091 3254423 := bstep (se 1 (by rfl) ⟨2440817, by rfl⟩ : syracuseStep 3254423 = 4881635) B4881635
theorem B2672843 : Blo 1780091 2672843 := bstep (se 1 (by rfl) ⟨2004632, by rfl⟩ : syracuseStep 2672843 = 4009265) B4009265
theorem B2672855 : Blo 1780091 2672855 := bstep (se 1 (by rfl) ⟨2004641, by rfl⟩ : syracuseStep 2672855 = 4009283) B4009283
theorem B4008203 : Blo 1780091 4008203 := bstep (se 1 (by rfl) ⟨3006152, by rfl⟩ : syracuseStep 4008203 = 6012305) B6012305
theorem B5703959 : Blo 1780091 5703959 := bstep (se 1 (by rfl) ⟨4277969, by rfl⟩ : syracuseStep 5703959 = 8555939) B8555939
theorem B6686999 : Blo 1780091 6686999 := bstep (se 1 (by rfl) ⟨5015249, by rfl⟩ : syracuseStep 6686999 = 10030499) B10030499
theorem B2672921 : Blo 1780091 2672921 := bstep (se 2 (by rfl) ⟨1002345, by rfl⟩ : syracuseStep 2672921 = 2004691) B2004691
theorem B4008257 : Blo 1780091 4008257 := bstep (se 2 (by rfl) ⟨1503096, by rfl⟩ : syracuseStep 4008257 = 3006193) B3006193
theorem B1780107 : Blo 1780091 1780107 := bstep (se 1 (by rfl) ⟨1335080, by rfl⟩ : syracuseStep 1780107 = 2670161) B2670161
theorem B2673035 : Blo 1780091 2673035 := bstep (se 1 (by rfl) ⟨2004776, by rfl⟩ : syracuseStep 2673035 = 4009553) B4009553
theorem B1780119 : Blo 1780091 1780119 := bstep (se 1 (by rfl) ⟨1335089, by rfl⟩ : syracuseStep 1780119 = 2670179) B2670179
theorem B2673047 : Blo 1780091 2673047 := bstep (se 1 (by rfl) ⟨2004785, by rfl⟩ : syracuseStep 2673047 = 4009571) B4009571
theorem B1780139 : Blo 1780091 1780139 := bstep (se 1 (by rfl) ⟨1335104, by rfl⟩ : syracuseStep 1780139 = 2670209) B2670209
theorem B1780151 : Blo 1780091 1780151 := bstep (se 1 (by rfl) ⟨1335113, by rfl⟩ : syracuseStep 1780151 = 2670227) B2670227
theorem B1780171 : Blo 1780091 1780171 := bstep (se 1 (by rfl) ⟨1335128, by rfl⟩ : syracuseStep 1780171 = 2670257) B2670257
theorem B1780183 : Blo 1780091 1780183 := bstep (se 1 (by rfl) ⟨1335137, by rfl⟩ : syracuseStep 1780183 = 2670275) B2670275
theorem B10144217 : Blo 1780091 10144217 := bstep (se 2 (by rfl) ⟨3804081, by rfl⟩ : syracuseStep 10144217 = 7608163) B7608163
theorem B2673113 : Blo 1780091 2673113 := bstep (se 2 (by rfl) ⟨1002417, by rfl⟩ : syracuseStep 2673113 = 2004835) B2004835
theorem B1780203 : Blo 1780091 1780203 := bstep (se 1 (by rfl) ⟨1335152, by rfl⟩ : syracuseStep 1780203 = 2670305) B2670305
theorem B1780215 : Blo 1780091 1780215 := bstep (se 1 (by rfl) ⟨1335161, by rfl⟩ : syracuseStep 1780215 = 2670323) B2670323
theorem B1780235 : Blo 1780091 1780235 := bstep (se 1 (by rfl) ⟨1335176, by rfl⟩ : syracuseStep 1780235 = 2670353) B2670353
theorem B41126413 : Blo 1780091 41126413 := bstep (se 3 (by rfl) ⟨7711202, by rfl⟩ : syracuseStep 41126413 = 15422405) B15422405
theorem B1780247 : Blo 1780091 1780247 := bstep (se 1 (by rfl) ⟨1335185, by rfl⟩ : syracuseStep 1780247 = 2670371) B2670371
theorem B4008473 : Blo 1780091 4008473 := bstep (se 2 (by rfl) ⟨1503177, by rfl⟩ : syracuseStep 4008473 = 3006355) B3006355
theorem B1780267 : Blo 1780091 1780267 := bstep (se 1 (by rfl) ⟨1335200, by rfl⟩ : syracuseStep 1780267 = 2670401) B2670401
theorem B1780279 : Blo 1780091 1780279 := bstep (se 1 (by rfl) ⟨1335209, by rfl⟩ : syracuseStep 1780279 = 2670419) B2670419
theorem B1780299 : Blo 1780091 1780299 := bstep (se 1 (by rfl) ⟨1335224, by rfl⟩ : syracuseStep 1780299 = 2670449) B2670449
theorem B1780311 : Blo 1780091 1780311 := bstep (se 1 (by rfl) ⟨1335233, by rfl⟩ : syracuseStep 1780311 = 2670467) B2670467
theorem B12184157 : Blo 1780091 12184157 := bstep (se 3 (by rfl) ⟨2284529, by rfl⟩ : syracuseStep 12184157 = 4569059) B4569059
theorem B1780331 : Blo 1780091 1780331 := bstep (se 1 (by rfl) ⟨1335248, by rfl⟩ : syracuseStep 1780331 = 2670497) B2670497
theorem B4008563 : Blo 1780091 4008563 := bstep (se 1 (by rfl) ⟨3006422, by rfl⟩ : syracuseStep 4008563 = 6012845) B6012845
theorem B1780343 : Blo 1780091 1780343 := bstep (se 1 (by rfl) ⟨1335257, by rfl⟩ : syracuseStep 1780343 = 2670515) B2670515
theorem B7604867 : Blo 1780091 7604867 := bstep (se 1 (by rfl) ⟨5703650, by rfl⟩ : syracuseStep 7604867 = 11407301) B11407301
theorem B1780363 : Blo 1780091 1780363 := bstep (se 1 (by rfl) ⟨1335272, by rfl⟩ : syracuseStep 1780363 = 2670545) B2670545
theorem B1780375 : Blo 1780091 1780375 := bstep (se 1 (by rfl) ⟨1335281, by rfl⟩ : syracuseStep 1780375 = 2670563) B2670563
theorem B4008599 : Blo 1780091 4008599 := bstep (se 1 (by rfl) ⟨3006449, by rfl⟩ : syracuseStep 4008599 = 6012899) B6012899
theorem B1780395 : Blo 1780091 1780395 := bstep (se 1 (by rfl) ⟨1335296, by rfl⟩ : syracuseStep 1780395 = 2670593) B2670593
theorem B11414195 : Blo 1780091 11414195 := bstep (se 1 (by rfl) ⟨8560646, by rfl⟩ : syracuseStep 11414195 = 17121293) B17121293
theorem B1780407 : Blo 1780091 1780407 := bstep (se 1 (by rfl) ⟨1335305, by rfl⟩ : syracuseStep 1780407 = 2670611) B2670611
theorem B1780427 : Blo 1780091 1780427 := bstep (se 1 (by rfl) ⟨1335320, by rfl⟩ : syracuseStep 1780427 = 2670641) B2670641
theorem B1780439 : Blo 1780091 1780439 := bstep (se 1 (by rfl) ⟨1335329, by rfl⟩ : syracuseStep 1780439 = 2670659) B2670659
theorem B1780459 : Blo 1780091 1780459 := bstep (se 1 (by rfl) ⟨1335344, by rfl⟩ : syracuseStep 1780459 = 2670689) B2670689
theorem B1780471 : Blo 1780091 1780471 := bstep (se 1 (by rfl) ⟨1335353, by rfl⟩ : syracuseStep 1780471 = 2670707) B2670707
theorem B1780491 : Blo 1780091 1780491 := bstep (se 1 (by rfl) ⟨1335368, by rfl⟩ : syracuseStep 1780491 = 2670737) B2670737
theorem B1780503 : Blo 1780091 1780503 := bstep (se 1 (by rfl) ⟨1335377, by rfl⟩ : syracuseStep 1780503 = 2670755) B2670755
theorem B1780523 : Blo 1780091 1780523 := bstep (se 1 (by rfl) ⟨1335392, by rfl⟩ : syracuseStep 1780523 = 2670785) B2670785
theorem B1780535 : Blo 1780091 1780535 := bstep (se 1 (by rfl) ⟨1335401, by rfl⟩ : syracuseStep 1780535 = 2670803) B2670803
theorem B8555339 : Blo 1780091 8555339 := bstep (se 1 (by rfl) ⟨6416504, by rfl⟩ : syracuseStep 8555339 = 12833009) B12833009
theorem B1780555 : Blo 1780091 1780555 := bstep (se 1 (by rfl) ⟨1335416, by rfl⟩ : syracuseStep 1780555 = 2670833) B2670833
theorem B4008779 : Blo 1780091 4008779 := bstep (se 1 (by rfl) ⟨3006584, by rfl⟩ : syracuseStep 4008779 = 6013169) B6013169
theorem B1780567 : Blo 1780091 1780567 := bstep (se 1 (by rfl) ⟨1335425, by rfl⟩ : syracuseStep 1780567 = 2670851) B2670851
theorem B1780587 : Blo 1780091 1780587 := bstep (se 1 (by rfl) ⟨1335440, by rfl⟩ : syracuseStep 1780587 = 2670881) B2670881
theorem B1780599 : Blo 1780091 1780599 := bstep (se 1 (by rfl) ⟨1335449, by rfl⟩ : syracuseStep 1780599 = 2670899) B2670899
theorem B4008833 : Blo 1780091 4008833 := bstep (se 2 (by rfl) ⟨1503312, by rfl⟩ : syracuseStep 4008833 = 3006625) B3006625
theorem B1780619 : Blo 1780091 1780619 := bstep (se 1 (by rfl) ⟨1335464, by rfl⟩ : syracuseStep 1780619 = 2670929) B2670929
theorem B1780631 : Blo 1780091 1780631 := bstep (se 1 (by rfl) ⟨1335473, by rfl⟩ : syracuseStep 1780631 = 2670947) B2670947
theorem B1780651 : Blo 1780091 1780651 := bstep (se 1 (by rfl) ⟨1335488, by rfl⟩ : syracuseStep 1780651 = 2670977) B2670977
theorem B32492465 : Blo 1780091 32492465 := bstep (se 2 (by rfl) ⟨12184674, by rfl⟩ : syracuseStep 32492465 = 24369349) B24369349
theorem B1780663 : Blo 1780091 1780663 := bstep (se 1 (by rfl) ⟨1335497, by rfl⟩ : syracuseStep 1780663 = 2670995) B2670995
theorem B1780683 : Blo 1780091 1780683 := bstep (se 1 (by rfl) ⟨1335512, by rfl⟩ : syracuseStep 1780683 = 2671025) B2671025
theorem B1780695 : Blo 1780091 1780695 := bstep (se 1 (by rfl) ⟨1335521, by rfl⟩ : syracuseStep 1780695 = 2671043) B2671043
theorem B1780715 : Blo 1780091 1780715 := bstep (se 1 (by rfl) ⟨1335536, by rfl⟩ : syracuseStep 1780715 = 2671073) B2671073
theorem B1780727 : Blo 1780091 1780727 := bstep (se 1 (by rfl) ⟨1335545, by rfl⟩ : syracuseStep 1780727 = 2671091) B2671091
theorem B1780747 : Blo 1780091 1780747 := bstep (se 1 (by rfl) ⟨1335560, by rfl⟩ : syracuseStep 1780747 = 2671121) B2671121
theorem B1780759 : Blo 1780091 1780759 := bstep (se 1 (by rfl) ⟨1335569, by rfl⟩ : syracuseStep 1780759 = 2671139) B2671139
theorem B3804185 : Blo 1780091 3804185 := bstep (se 2 (by rfl) ⟨1426569, by rfl⟩ : syracuseStep 3804185 = 2853139) B2853139
theorem B1780779 : Blo 1780091 1780779 := bstep (se 1 (by rfl) ⟨1335584, by rfl⟩ : syracuseStep 1780779 = 2671169) B2671169
theorem B4508723 : Blo 1780091 4508723 := bstep (se 1 (by rfl) ⟨3381542, by rfl⟩ : syracuseStep 4508723 = 6763085) B6763085
theorem B1780791 : Blo 1780091 1780791 := bstep (se 1 (by rfl) ⟨1335593, by rfl⟩ : syracuseStep 1780791 = 2671187) B2671187
theorem B1780811 : Blo 1780091 1780811 := bstep (se 1 (by rfl) ⟨1335608, by rfl⟩ : syracuseStep 1780811 = 2671217) B2671217
theorem B1780823 : Blo 1780091 1780823 := bstep (se 1 (by rfl) ⟨1335617, by rfl⟩ : syracuseStep 1780823 = 2671235) B2671235
theorem B4009049 : Blo 1780091 4009049 := bstep (se 2 (by rfl) ⟨1503393, by rfl⟩ : syracuseStep 4009049 = 3006787) B3006787
theorem B1780843 : Blo 1780091 1780843 := bstep (se 1 (by rfl) ⟨1335632, by rfl⟩ : syracuseStep 1780843 = 2671265) B2671265
theorem B1780855 : Blo 1780091 1780855 := bstep (se 1 (by rfl) ⟨1335641, by rfl⟩ : syracuseStep 1780855 = 2671283) B2671283
theorem B1780875 : Blo 1780091 1780875 := bstep (se 1 (by rfl) ⟨1335656, by rfl⟩ : syracuseStep 1780875 = 2671313) B2671313
theorem B64990349 : Blo 1780091 64990349 := bstep (se 3 (by rfl) ⟨12185690, by rfl⟩ : syracuseStep 64990349 = 24371381) B24371381
theorem B1780887 : Blo 1780091 1780887 := bstep (se 1 (by rfl) ⟨1335665, by rfl⟩ : syracuseStep 1780887 = 2671331) B2671331
theorem B1780907 : Blo 1780091 1780907 := bstep (se 1 (by rfl) ⟨1335680, by rfl⟩ : syracuseStep 1780907 = 2671361) B2671361
theorem B4009139 : Blo 1780091 4009139 := bstep (se 1 (by rfl) ⟨3006854, by rfl⟩ : syracuseStep 4009139 = 6013709) B6013709
theorem B1780919 : Blo 1780091 1780919 := bstep (se 1 (by rfl) ⟨1335689, by rfl⟩ : syracuseStep 1780919 = 2671379) B2671379
theorem B1780939 : Blo 1780091 1780939 := bstep (se 1 (by rfl) ⟨1335704, by rfl⟩ : syracuseStep 1780939 = 2671409) B2671409
theorem B1780951 : Blo 1780091 1780951 := bstep (se 1 (by rfl) ⟨1335713, by rfl⟩ : syracuseStep 1780951 = 2671427) B2671427
theorem B9014489 : Blo 1780091 9014489 := bstep (se 2 (by rfl) ⟨3380433, by rfl⟩ : syracuseStep 9014489 = 6760867) B6760867
theorem B4009175 : Blo 1780091 4009175 := bstep (se 1 (by rfl) ⟨3006881, by rfl⟩ : syracuseStep 4009175 = 6013763) B6013763
theorem B1780971 : Blo 1780091 1780971 := bstep (se 1 (by rfl) ⟨1335728, by rfl⟩ : syracuseStep 1780971 = 2671457) B2671457
theorem B26389745 : Blo 1780091 26389745 := bstep (se 2 (by rfl) ⟨9896154, by rfl⟩ : syracuseStep 26389745 = 19792309) B19792309
theorem B1780983 : Blo 1780091 1780983 := bstep (se 1 (by rfl) ⟨1335737, by rfl⟩ : syracuseStep 1780983 = 2671475) B2671475
theorem B1781003 : Blo 1780091 1781003 := bstep (se 1 (by rfl) ⟨1335752, by rfl⟩ : syracuseStep 1781003 = 2671505) B2671505
theorem B1781015 : Blo 1780091 1781015 := bstep (se 1 (by rfl) ⟨1335761, by rfl⟩ : syracuseStep 1781015 = 2671523) B2671523
theorem B1781035 : Blo 1780091 1781035 := bstep (se 1 (by rfl) ⟨1335776, by rfl⟩ : syracuseStep 1781035 = 2671553) B2671553
theorem B1781047 : Blo 1780091 1781047 := bstep (se 1 (by rfl) ⟨1335785, by rfl⟩ : syracuseStep 1781047 = 2671571) B2671571
theorem B1781067 : Blo 1780091 1781067 := bstep (se 1 (by rfl) ⟨1335800, by rfl⟩ : syracuseStep 1781067 = 2671601) B2671601
theorem B1781079 : Blo 1780091 1781079 := bstep (se 1 (by rfl) ⟨1335809, by rfl⟩ : syracuseStep 1781079 = 2671619) B2671619
theorem B4509017 : Blo 1780091 4509017 := bstep (se 2 (by rfl) ⟨1690881, by rfl⟩ : syracuseStep 4509017 = 3381763) B3381763
theorem B1781099 : Blo 1780091 1781099 := bstep (se 1 (by rfl) ⟨1335824, by rfl⟩ : syracuseStep 1781099 = 2671649) B2671649
theorem B1781111 : Blo 1780091 1781111 := bstep (se 1 (by rfl) ⟨1335833, by rfl⟩ : syracuseStep 1781111 = 2671667) B2671667
theorem B1781131 : Blo 1780091 1781131 := bstep (se 1 (by rfl) ⟨1335848, by rfl⟩ : syracuseStep 1781131 = 2671697) B2671697
theorem B4009355 : Blo 1780091 4009355 := bstep (se 1 (by rfl) ⟨3007016, by rfl⟩ : syracuseStep 4009355 = 6014033) B6014033
theorem B1781143 : Blo 1780091 1781143 := bstep (se 1 (by rfl) ⟨1335857, by rfl⟩ : syracuseStep 1781143 = 2671715) B2671715
theorem B1781163 : Blo 1780091 1781163 := bstep (se 1 (by rfl) ⟨1335872, by rfl⟩ : syracuseStep 1781163 = 2671745) B2671745
theorem B1781175 : Blo 1780091 1781175 := bstep (se 1 (by rfl) ⟨1335881, by rfl⟩ : syracuseStep 1781175 = 2671763) B2671763
theorem B4009409 : Blo 1780091 4009409 := bstep (se 2 (by rfl) ⟨1503528, by rfl⟩ : syracuseStep 4009409 = 3007057) B3007057
theorem B1781195 : Blo 1780091 1781195 := bstep (se 1 (by rfl) ⟨1335896, by rfl⟩ : syracuseStep 1781195 = 2671793) B2671793
theorem B1781207 : Blo 1780091 1781207 := bstep (se 1 (by rfl) ⟨1335905, by rfl⟩ : syracuseStep 1781207 = 2671811) B2671811
theorem B1781227 : Blo 1780091 1781227 := bstep (se 1 (by rfl) ⟨1335920, by rfl⟩ : syracuseStep 1781227 = 2671841) B2671841
theorem B1781239 : Blo 1780091 1781239 := bstep (se 1 (by rfl) ⟨1335929, by rfl⟩ : syracuseStep 1781239 = 2671859) B2671859
theorem B1781259 : Blo 1780091 1781259 := bstep (se 1 (by rfl) ⟨1335944, by rfl⟩ : syracuseStep 1781259 = 2671889) B2671889
theorem B1781271 : Blo 1780091 1781271 := bstep (se 1 (by rfl) ⟨1335953, by rfl⟩ : syracuseStep 1781271 = 2671907) B2671907
theorem B1781291 : Blo 1780091 1781291 := bstep (se 1 (by rfl) ⟨1335968, by rfl⟩ : syracuseStep 1781291 = 2671937) B2671937
theorem B1781303 : Blo 1780091 1781303 := bstep (se 1 (by rfl) ⟨1335977, by rfl⟩ : syracuseStep 1781303 = 2671955) B2671955
theorem B5705291 : Blo 1780091 5705291 := bstep (se 1 (by rfl) ⟨4278968, by rfl⟩ : syracuseStep 5705291 = 8557937) B8557937
theorem B1781323 : Blo 1780091 1781323 := bstep (se 1 (by rfl) ⟨1335992, by rfl⟩ : syracuseStep 1781323 = 2671985) B2671985
theorem B1781335 : Blo 1780091 1781335 := bstep (se 1 (by rfl) ⟨1336001, by rfl⟩ : syracuseStep 1781335 = 2672003) B2672003
theorem B1781355 : Blo 1780091 1781355 := bstep (se 1 (by rfl) ⟨1336016, by rfl⟩ : syracuseStep 1781355 = 2672033) B2672033
theorem B1781367 : Blo 1780091 1781367 := bstep (se 1 (by rfl) ⟨1336025, by rfl⟩ : syracuseStep 1781367 = 2672051) B2672051
theorem B1781387 : Blo 1780091 1781387 := bstep (se 1 (by rfl) ⟨1336040, by rfl⟩ : syracuseStep 1781387 = 2672081) B2672081
theorem B6008471 : Blo 1780091 6008471 := bstep (se 1 (by rfl) ⟨4506353, by rfl⟩ : syracuseStep 6008471 = 9012707) B9012707
theorem B1781399 : Blo 1780091 1781399 := bstep (se 1 (by rfl) ⟨1336049, by rfl⟩ : syracuseStep 1781399 = 2672099) B2672099
theorem B7925399 : Blo 1780091 7925399 := bstep (se 1 (by rfl) ⟨5944049, by rfl⟩ : syracuseStep 7925399 = 11888099) B11888099
theorem B4009625 : Blo 1780091 4009625 := bstep (se 2 (by rfl) ⟨1503609, by rfl⟩ : syracuseStep 4009625 = 3007219) B3007219
theorem B2002603 : Blo 1780091 2002603 := bstep (se 1 (by rfl) ⟨1501952, by rfl⟩ : syracuseStep 2002603 = 3003905) B3003905
theorem B1781419 : Blo 1780091 1781419 := bstep (se 1 (by rfl) ⟨1336064, by rfl⟩ : syracuseStep 1781419 = 2672129) B2672129
theorem B1781431 : Blo 1780091 1781431 := bstep (se 1 (by rfl) ⟨1336073, by rfl⟩ : syracuseStep 1781431 = 2672147) B2672147
theorem B1781451 : Blo 1780091 1781451 := bstep (se 1 (by rfl) ⟨1336088, by rfl⟩ : syracuseStep 1781451 = 2672177) B2672177
theorem B13528781 : Blo 1780091 13528781 := bstep (se 3 (by rfl) ⟨2536646, by rfl⟩ : syracuseStep 13528781 = 5073293) B5073293
theorem B1781463 : Blo 1780091 1781463 := bstep (se 1 (by rfl) ⟨1336097, by rfl⟩ : syracuseStep 1781463 = 2672195) B2672195
theorem B1781483 : Blo 1780091 1781483 := bstep (se 1 (by rfl) ⟨1336112, by rfl⟩ : syracuseStep 1781483 = 2672225) B2672225
theorem B1781495 : Blo 1780091 1781495 := bstep (se 1 (by rfl) ⟨1336121, by rfl⟩ : syracuseStep 1781495 = 2672243) B2672243
theorem B1781515 : Blo 1780091 1781515 := bstep (se 1 (by rfl) ⟨1336136, by rfl⟩ : syracuseStep 1781515 = 2672273) B2672273
theorem B2002711 : Blo 1780091 2002711 := bstep (se 1 (by rfl) ⟨1502033, by rfl⟩ : syracuseStep 2002711 = 3004067) B3004067
theorem B1781527 : Blo 1780091 1781527 := bstep (se 1 (by rfl) ⟨1336145, by rfl⟩ : syracuseStep 1781527 = 2672291) B2672291
theorem B1781547 : Blo 1780091 1781547 := bstep (se 1 (by rfl) ⟨1336160, by rfl⟩ : syracuseStep 1781547 = 2672321) B2672321
theorem B1781559 : Blo 1780091 1781559 := bstep (se 1 (by rfl) ⟨1336169, by rfl⟩ : syracuseStep 1781559 = 2672339) B2672339
theorem B1781579 : Blo 1780091 1781579 := bstep (se 1 (by rfl) ⟨1336184, by rfl⟩ : syracuseStep 1781579 = 2672369) B2672369
theorem B1781591 : Blo 1780091 1781591 := bstep (se 1 (by rfl) ⟨1336193, by rfl⟩ : syracuseStep 1781591 = 2672387) B2672387
theorem B2535257 : Blo 1780091 2535257 := bstep (se 2 (by rfl) ⟨950721, by rfl⟩ : syracuseStep 2535257 = 1901443) B1901443
theorem B1781611 : Blo 1780091 1781611 := bstep (se 1 (by rfl) ⟨1336208, by rfl⟩ : syracuseStep 1781611 = 2672417) B2672417
theorem B1781623 : Blo 1780091 1781623 := bstep (se 1 (by rfl) ⟨1336217, by rfl⟩ : syracuseStep 1781623 = 2672435) B2672435
theorem B1781643 : Blo 1780091 1781643 := bstep (se 1 (by rfl) ⟨1336232, by rfl⟩ : syracuseStep 1781643 = 2672465) B2672465
theorem B1781655 : Blo 1780091 1781655 := bstep (se 1 (by rfl) ⟨1336241, by rfl⟩ : syracuseStep 1781655 = 2672483) B2672483
theorem B1781675 : Blo 1780091 1781675 := bstep (se 1 (by rfl) ⟨1336256, by rfl⟩ : syracuseStep 1781675 = 2672513) B2672513
theorem B14274481 : Blo 1780091 14274481 := bstep (se 2 (by rfl) ⟨5352930, by rfl⟩ : syracuseStep 14274481 = 10705861) B10705861
theorem B1781687 : Blo 1780091 1781687 := bstep (se 1 (by rfl) ⟨1336265, by rfl⟩ : syracuseStep 1781687 = 2672531) B2672531
theorem B2002891 : Blo 1780091 2002891 := bstep (se 1 (by rfl) ⟨1502168, by rfl⟩ : syracuseStep 2002891 = 3004337) B3004337
theorem B1781707 : Blo 1780091 1781707 := bstep (se 1 (by rfl) ⟨1336280, by rfl⟩ : syracuseStep 1781707 = 2672561) B2672561
theorem B1781719 : Blo 1780091 1781719 := bstep (se 1 (by rfl) ⟨1336289, by rfl⟩ : syracuseStep 1781719 = 2672579) B2672579
theorem B1781739 : Blo 1780091 1781739 := bstep (se 1 (by rfl) ⟨1336304, by rfl⟩ : syracuseStep 1781739 = 2672609) B2672609
theorem B1781751 : Blo 1780091 1781751 := bstep (se 1 (by rfl) ⟨1336313, by rfl⟩ : syracuseStep 1781751 = 2672627) B2672627
theorem B1781771 : Blo 1780091 1781771 := bstep (se 1 (by rfl) ⟨1336328, by rfl⟩ : syracuseStep 1781771 = 2672657) B2672657
theorem B1781783 : Blo 1780091 1781783 := bstep (se 1 (by rfl) ⟨1336337, by rfl⟩ : syracuseStep 1781783 = 2672675) B2672675
theorem B1781803 : Blo 1780091 1781803 := bstep (se 1 (by rfl) ⟨1336352, by rfl⟩ : syracuseStep 1781803 = 2672705) B2672705
theorem B2002999 : Blo 1780091 2002999 := bstep (se 1 (by rfl) ⟨1502249, by rfl⟩ : syracuseStep 2002999 = 3004499) B3004499
theorem B1781815 : Blo 1780091 1781815 := bstep (se 1 (by rfl) ⟨1336361, by rfl⟩ : syracuseStep 1781815 = 2672723) B2672723
theorem B10145857 : Blo 1780091 10145857 := bstep (se 2 (by rfl) ⟨3804696, by rfl⟩ : syracuseStep 10145857 = 7609393) B7609393
theorem B1781835 : Blo 1780091 1781835 := bstep (se 1 (by rfl) ⟨1336376, by rfl⟩ : syracuseStep 1781835 = 2672753) B2672753
theorem B1781847 : Blo 1780091 1781847 := bstep (se 1 (by rfl) ⟨1336385, by rfl⟩ : syracuseStep 1781847 = 2672771) B2672771
theorem B18280541 : Blo 1780091 18280541 := bstep (se 3 (by rfl) ⟨3427601, by rfl⟩ : syracuseStep 18280541 = 6855203) B6855203
theorem B1781867 : Blo 1780091 1781867 := bstep (se 1 (by rfl) ⟨1336400, by rfl⟩ : syracuseStep 1781867 = 2672801) B2672801
theorem B1781879 : Blo 1780091 1781879 := bstep (se 1 (by rfl) ⟨1336409, by rfl⟩ : syracuseStep 1781879 = 2672819) B2672819
theorem B1781899 : Blo 1780091 1781899 := bstep (se 1 (by rfl) ⟨1336424, by rfl⟩ : syracuseStep 1781899 = 2672849) B2672849
theorem B17109143 : Blo 1780091 17109143 := bstep (se 1 (by rfl) ⟨12831857, by rfl⟩ : syracuseStep 17109143 = 25663715) B25663715
theorem B1781911 : Blo 1780091 1781911 := bstep (se 1 (by rfl) ⟨1336433, by rfl⟩ : syracuseStep 1781911 = 2672867) B2672867
theorem B1781931 : Blo 1780091 1781931 := bstep (se 1 (by rfl) ⟨1336448, by rfl⟩ : syracuseStep 1781931 = 2672897) B2672897
theorem B6009011 : Blo 1780091 6009011 := bstep (se 1 (by rfl) ⟨4506758, by rfl⟩ : syracuseStep 6009011 = 9013517) B9013517
theorem B13529267 : Blo 1780091 13529267 := bstep (se 1 (by rfl) ⟨10146950, by rfl⟩ : syracuseStep 13529267 = 20293901) B20293901
theorem B1781943 : Blo 1780091 1781943 := bstep (se 1 (by rfl) ⟨1336457, by rfl⟩ : syracuseStep 1781943 = 2672915) B2672915
theorem B1781963 : Blo 1780091 1781963 := bstep (se 1 (by rfl) ⟨1336472, by rfl⟩ : syracuseStep 1781963 = 2672945) B2672945
theorem B1781975 : Blo 1780091 1781975 := bstep (se 1 (by rfl) ⟨1336481, by rfl⟩ : syracuseStep 1781975 = 2672963) B2672963
theorem B2003179 : Blo 1780091 2003179 := bstep (se 1 (by rfl) ⟨1502384, by rfl⟩ : syracuseStep 2003179 = 3004769) B3004769
theorem B1781995 : Blo 1780091 1781995 := bstep (se 1 (by rfl) ⟨1336496, by rfl⟩ : syracuseStep 1781995 = 2672993) B2672993
theorem B1782007 : Blo 1780091 1782007 := bstep (se 1 (by rfl) ⟨1336505, by rfl⟩ : syracuseStep 1782007 = 2673011) B2673011
theorem B1782027 : Blo 1780091 1782027 := bstep (se 1 (by rfl) ⟨1336520, by rfl⟩ : syracuseStep 1782027 = 2673041) B2673041
theorem B1782039 : Blo 1780091 1782039 := bstep (se 1 (by rfl) ⟨1336529, by rfl⟩ : syracuseStep 1782039 = 2673059) B2673059
theorem B1782059 : Blo 1780091 1782059 := bstep (se 1 (by rfl) ⟨1336544, by rfl⟩ : syracuseStep 1782059 = 2673089) B2673089
theorem B6762797 : Blo 1780091 6762797 := bstep (se 3 (by rfl) ⟨1268024, by rfl⟩ : syracuseStep 6762797 = 2536049) B2536049
theorem B1782071 : Blo 1780091 1782071 := bstep (se 1 (by rfl) ⟨1336553, by rfl⟩ : syracuseStep 1782071 = 2673107) B2673107
theorem B1782091 : Blo 1780091 1782091 := bstep (se 1 (by rfl) ⟨1336568, by rfl⟩ : syracuseStep 1782091 = 2673137) B2673137
theorem B2003287 : Blo 1780091 2003287 := bstep (se 1 (by rfl) ⟨1502465, by rfl⟩ : syracuseStep 2003287 = 3004931) B3004931
theorem B6009281 : Blo 1780091 6009281 := bstep (se 2 (by rfl) ⟨2253480, by rfl⟩ : syracuseStep 6009281 = 4506961) B4506961
theorem B2535895 : Blo 1780091 2535895 := bstep (se 1 (by rfl) ⟨1901921, by rfl⟩ : syracuseStep 2535895 = 3803843) B3803843
theorem B2003467 : Blo 1780091 2003467 := bstep (se 1 (by rfl) ⟨1502600, by rfl⟩ : syracuseStep 2003467 = 3005201) B3005201
theorem B3379735 : Blo 1780091 3379735 := bstep (se 1 (by rfl) ⟨2534801, by rfl⟩ : syracuseStep 3379735 = 5069603) B5069603
theorem B12841517 : Blo 1780091 12841517 := bstep (se 3 (by rfl) ⟨2407784, by rfl⟩ : syracuseStep 12841517 = 4815569) B4815569
theorem B2003575 : Blo 1780091 2003575 := bstep (se 1 (by rfl) ⟨1502681, by rfl⟩ : syracuseStep 2003575 = 3005363) B3005363
theorem B3805825 : Blo 1780091 3805825 := bstep (se 2 (by rfl) ⟨1427184, by rfl⟩ : syracuseStep 3805825 = 2854369) B2854369
theorem B20845187 : Blo 1780091 20845187 := bstep (se 1 (by rfl) ⟨15633890, by rfl⟩ : syracuseStep 20845187 = 31267781) B31267781
theorem B3207937 : Blo 1780091 3207937 := bstep (se 2 (by rfl) ⟨1202976, by rfl⟩ : syracuseStep 3207937 = 2405953) B2405953
theorem B10138385 : Blo 1780091 10138385 := bstep (se 2 (by rfl) ⟨3801894, by rfl⟩ : syracuseStep 10138385 = 7603789) B7603789
theorem B2003755 : Blo 1780091 2003755 := bstep (se 1 (by rfl) ⟨1502816, by rfl⟩ : syracuseStep 2003755 = 3005633) B3005633
theorem B9016109 : Blo 1780091 9016109 := bstep (se 3 (by rfl) ⟨1690520, by rfl⟩ : syracuseStep 9016109 = 3381041) B3381041
theorem B38507329 : Blo 1780091 38507329 := bstep (se 2 (by rfl) ⟨14440248, by rfl⟩ : syracuseStep 38507329 = 28880497) B28880497
theorem B7607105 : Blo 1780091 7607105 := bstep (se 2 (by rfl) ⟨2852664, by rfl⟩ : syracuseStep 7607105 = 5705329) B5705329
theorem B2003863 : Blo 1780091 2003863 := bstep (se 1 (by rfl) ⟨1502897, by rfl⟩ : syracuseStep 2003863 = 3005795) B3005795
theorem B29275057 : Blo 1780091 29275057 := bstep (se 2 (by rfl) ⟨10978146, by rfl⟩ : syracuseStep 29275057 = 21956293) B21956293
theorem B4510667 : Blo 1780091 4510667 := bstep (se 1 (by rfl) ⟨3383000, by rfl⟩ : syracuseStep 4510667 = 6766001) B6766001
theorem B6009821 : Blo 1780091 6009821 := bstep (se 3 (by rfl) ⟨1126841, by rfl⟩ : syracuseStep 6009821 = 2253683) B2253683
theorem B6763571 : Blo 1780091 6763571 := bstep (se 1 (by rfl) ⟨5072678, by rfl⟩ : syracuseStep 6763571 = 10145357) B10145357
theorem B2004043 : Blo 1780091 2004043 := bstep (se 1 (by rfl) ⟨1503032, by rfl⟩ : syracuseStep 2004043 = 3006065) B3006065
theorem B2708569 : Blo 1780091 2708569 := bstep (se 2 (by rfl) ⟨1015713, by rfl⟩ : syracuseStep 2708569 = 2031427) B2031427
theorem B2536601 : Blo 1780091 2536601 := bstep (se 2 (by rfl) ⟨951225, by rfl⟩ : syracuseStep 2536601 = 1902451) B1902451
theorem B5706931 : Blo 1780091 5706931 := bstep (se 1 (by rfl) ⟨4280198, by rfl⟩ : syracuseStep 5706931 = 8560397) B8560397
theorem B2004151 : Blo 1780091 2004151 := bstep (se 1 (by rfl) ⟨1503113, by rfl⟩ : syracuseStep 2004151 = 3006227) B3006227
theorem B3609803 : Blo 1780091 3609803 := bstep (se 1 (by rfl) ⟨2707352, by rfl⟩ : syracuseStep 3609803 = 5414705) B5414705
theorem B10138841 : Blo 1780091 10138841 := bstep (se 2 (by rfl) ⟨3802065, by rfl⟩ : syracuseStep 10138841 = 7604131) B7604131
theorem B6419677 : Blo 1780091 6419677 := bstep (se 3 (by rfl) ⟨1203689, by rfl⟩ : syracuseStep 6419677 = 2407379) B2407379
theorem B2536715 : Blo 1780091 2536715 := bstep (se 1 (by rfl) ⟨1902536, by rfl⟩ : syracuseStep 2536715 = 3805073) B3805073
theorem B3380555 : Blo 1780091 3380555 := bstep (se 1 (by rfl) ⟨2535416, by rfl⟩ : syracuseStep 3380555 = 5070833) B5070833
theorem B2004331 : Blo 1780091 2004331 := bstep (se 1 (by rfl) ⟨1503248, by rfl⟩ : syracuseStep 2004331 = 3006497) B3006497
theorem B3380609 : Blo 1780091 3380609 := bstep (se 2 (by rfl) ⟨1267728, by rfl⟩ : syracuseStep 3380609 = 2535457) B2535457
theorem B2004439 : Blo 1780091 2004439 := bstep (se 1 (by rfl) ⟨1503329, by rfl⟩ : syracuseStep 2004439 = 3006659) B3006659
theorem B3003979 : Blo 1780091 3003979 := bstep (se 1 (by rfl) ⟨2252984, by rfl⟩ : syracuseStep 3003979 = 4505969) B4505969
theorem B13530725 : Blo 1780091 13530725 := bstep (se 4 (by rfl) ⟨1268505, by rfl⟩ : syracuseStep 13530725 = 2537011) B2537011
theorem B11417219 : Blo 1780091 11417219 := bstep (se 1 (by rfl) ⟨8562914, by rfl⟩ : syracuseStep 11417219 = 17125829) B17125829
theorem B4060811 : Blo 1780091 4060811 := bstep (se 1 (by rfl) ⟨3045608, by rfl⟩ : syracuseStep 4060811 = 6091217) B6091217
theorem B2004619 : Blo 1780091 2004619 := bstep (se 1 (by rfl) ⟨1503464, by rfl⟩ : syracuseStep 2004619 = 3006929) B3006929
theorem B3610291 : Blo 1780091 3610291 := bstep (se 1 (by rfl) ⟨2707718, by rfl⟩ : syracuseStep 3610291 = 5415437) B5415437
theorem B3004121 : Blo 1780091 3004121 := bstep (se 2 (by rfl) ⟨1126545, by rfl⟩ : syracuseStep 3004121 = 2253091) B2253091
theorem B2004727 : Blo 1780091 2004727 := bstep (se 1 (by rfl) ⟨1503545, by rfl⟩ : syracuseStep 2004727 = 3007091) B3007091
theorem B11409169 : Blo 1780091 11409169 := bstep (se 2 (by rfl) ⟨4278438, by rfl⟩ : syracuseStep 11409169 = 8556877) B8556877
theorem B2537239 : Blo 1780091 2537239 := bstep (se 1 (by rfl) ⟨1902929, by rfl⟩ : syracuseStep 2537239 = 3805859) B3805859
theorem B6854465 : Blo 1780091 6854465 := bstep (se 2 (by rfl) ⟨2570424, by rfl⟩ : syracuseStep 6854465 = 5140849) B5140849
theorem B3004249 : Blo 1780091 3004249 := bstep (se 2 (by rfl) ⟨1126593, by rfl⟩ : syracuseStep 3004249 = 2253187) B2253187
theorem B2406233 : Blo 1780091 2406233 := bstep (se 2 (by rfl) ⟨902337, by rfl⟩ : syracuseStep 2406233 = 1804675) B1804675
theorem B13006693 : Blo 1780091 13006693 := bstep (se 4 (by rfl) ⟨1219377, by rfl⟩ : syracuseStep 13006693 = 2438755) B2438755
theorem B13522949 : Blo 1780091 13522949 := bstep (se 4 (by rfl) ⟨1267776, by rfl⟩ : syracuseStep 13522949 = 2535553) B2535553
theorem B131782709 : Blo 1780091 131782709 := bstep (se 5 (by rfl) ⟨6177314, by rfl⟩ : syracuseStep 131782709 = 12354629) B12354629
theorem B3209291 : Blo 1780091 3209291 := bstep (se 1 (by rfl) ⟨2406968, by rfl⟩ : syracuseStep 3209291 = 4813937) B4813937
theorem B6010955 : Blo 1780091 6010955 := bstep (se 1 (by rfl) ⟨4508216, by rfl⟩ : syracuseStep 6010955 = 9016433) B9016433
theorem B13531211 : Blo 1780091 13531211 := bstep (se 1 (by rfl) ⟨10148408, by rfl⟩ : syracuseStep 13531211 = 20296817) B20296817
theorem B5707865 : Blo 1780091 5707865 := bstep (se 2 (by rfl) ⟨2140449, by rfl⟩ : syracuseStep 5707865 = 4280899) B4280899
theorem B8558723 : Blo 1780091 8558723 := bstep (se 1 (by rfl) ⟨6419042, by rfl⟩ : syracuseStep 8558723 = 12838085) B12838085
theorem B3381527 : Blo 1780091 3381527 := bstep (se 1 (by rfl) ⟨2536145, by rfl⟩ : syracuseStep 3381527 = 5072291) B5072291
theorem B12351809 : Blo 1780091 12351809 := bstep (se 2 (by rfl) ⟨4631928, by rfl⟩ : syracuseStep 12351809 = 9263857) B9263857
theorem B3209537 : Blo 1780091 3209537 := bstep (se 2 (by rfl) ⟨1203576, by rfl⟩ : syracuseStep 3209537 = 2407153) B2407153
theorem B15210827 : Blo 1780091 15210827 := bstep (se 1 (by rfl) ⟨11408120, by rfl⟩ : syracuseStep 15210827 = 22816241) B22816241
theorem B6011225 : Blo 1780091 6011225 := bstep (se 2 (by rfl) ⟨2254209, by rfl⟩ : syracuseStep 6011225 = 4508419) B4508419
theorem B3004823 : Blo 1780091 3004823 := bstep (se 1 (by rfl) ⟨2253617, by rfl⟩ : syracuseStep 3004823 = 4507235) B4507235
theorem B5708225 : Blo 1780091 5708225 := bstep (se 2 (by rfl) ⟨2140584, by rfl⟩ : syracuseStep 5708225 = 4281169) B4281169
theorem B7608779 : Blo 1780091 7608779 := bstep (se 1 (by rfl) ⟨5706584, by rfl⟩ : syracuseStep 7608779 = 11413169) B11413169
theorem B6765059 : Blo 1780091 6765059 := bstep (se 1 (by rfl) ⟨5073794, by rfl⟩ : syracuseStep 6765059 = 10147589) B10147589
theorem B3004951 : Blo 1780091 3004951 := bstep (se 1 (by rfl) ⟨2253713, by rfl⟩ : syracuseStep 3004951 = 4507427) B4507427
theorem B3611159 : Blo 1780091 3611159 := bstep (se 1 (by rfl) ⟨2708369, by rfl⟩ : syracuseStep 3611159 = 5416739) B5416739
theorem B20298275 : Blo 1780091 20298275 := bstep (se 1 (by rfl) ⟨15223706, by rfl⟩ : syracuseStep 20298275 = 30447413) B30447413
theorem B6421265 : Blo 1780091 6421265 := bstep (se 2 (by rfl) ⟨2407974, by rfl⟩ : syracuseStep 6421265 = 4815949) B4815949
theorem B3382067 : Blo 1780091 3382067 := bstep (se 1 (by rfl) ⟨2536550, by rfl⟩ : syracuseStep 3382067 = 5073101) B5073101
theorem B6765515 : Blo 1780091 6765515 := bstep (se 1 (by rfl) ⟨5074136, by rfl⟩ : syracuseStep 6765515 = 10148273) B10148273
theorem B5069785 : Blo 1780091 5069785 := bstep (se 2 (by rfl) ⟨1901169, by rfl⟩ : syracuseStep 5069785 = 3802339) B3802339
theorem B6011927 : Blo 1780091 6011927 := bstep (se 1 (by rfl) ⟨4508945, by rfl⟩ : syracuseStep 6011927 = 9017891) B9017891
theorem B3005579 : Blo 1780091 3005579 := bstep (se 1 (by rfl) ⟨2254184, by rfl⟩ : syracuseStep 3005579 = 4508369) B4508369
theorem B6765713 : Blo 1780091 6765713 := bstep (se 2 (by rfl) ⟨2537142, by rfl⟩ : syracuseStep 6765713 = 5074285) B5074285
theorem B7609565 : Blo 1780091 7609565 := bstep (se 3 (by rfl) ⟨1426793, by rfl⟩ : syracuseStep 7609565 = 2853587) B2853587
theorem B3005707 : Blo 1780091 3005707 := bstep (se 1 (by rfl) ⟨2254280, by rfl⟩ : syracuseStep 3005707 = 4508561) B4508561
theorem B3382553 : Blo 1780091 3382553 := bstep (se 2 (by rfl) ⟨1268457, by rfl⟩ : syracuseStep 3382553 = 2536915) B2536915
theorem B3005849 : Blo 1780091 3005849 := bstep (se 2 (by rfl) ⟨1127193, by rfl⟩ : syracuseStep 3005849 = 2254387) B2254387
theorem B10149299 : Blo 1780091 10149299 := bstep (se 1 (by rfl) ⟨7611974, by rfl⟩ : syracuseStep 10149299 = 15223949) B15223949
theorem B4005323 : Blo 1780091 4005323 := bstep (se 1 (by rfl) ⟨3003992, by rfl⟩ : syracuseStep 4005323 = 6007985) B6007985
theorem B4005377 : Blo 1780091 4005377 := bstep (se 2 (by rfl) ⟨1502016, by rfl⟩ : syracuseStep 4005377 = 3004033) B3004033
theorem B3005977 : Blo 1780091 3005977 := bstep (se 2 (by rfl) ⟨1127241, by rfl⟩ : syracuseStep 3005977 = 2254483) B2254483
theorem B6012467 : Blo 1780091 6012467 := bstep (se 1 (by rfl) ⟨4509350, by rfl⟩ : syracuseStep 6012467 = 9018701) B9018701
theorem B4816435 : Blo 1780091 4816435 := bstep (se 1 (by rfl) ⟨3612326, by rfl⟩ : syracuseStep 4816435 = 7224653) B7224653
theorem B5070401 : Blo 1780091 5070401 := bstep (se 2 (by rfl) ⟨1901400, by rfl⟩ : syracuseStep 5070401 = 3802801) B3802801
theorem B2670155 : Blo 1780091 2670155 := bstep (se 1 (by rfl) ⟨2002616, by rfl⟩ : syracuseStep 2670155 = 4005233) B4005233
theorem B2670167 : Blo 1780091 2670167 := bstep (se 1 (by rfl) ⟨2002625, by rfl⟩ : syracuseStep 2670167 = 4005251) B4005251
theorem B3210841 : Blo 1780091 3210841 := bstep (se 2 (by rfl) ⟨1204065, by rfl⟩ : syracuseStep 3210841 = 2408131) B2408131
theorem B13704805 : Blo 1780091 13704805 := bstep (se 4 (by rfl) ⟨1284825, by rfl⟩ : syracuseStep 13704805 = 2569651) B2569651
theorem B2670233 : Blo 1780091 2670233 := bstep (se 2 (by rfl) ⟨1001337, by rfl⟩ : syracuseStep 2670233 = 2002675) B2002675
theorem B4005593 : Blo 1780091 4005593 := bstep (se 2 (by rfl) ⟨1502097, by rfl⟩ : syracuseStep 4005593 = 3004195) B3004195
theorem B2670347 : Blo 1780091 2670347 := bstep (se 1 (by rfl) ⟨2002760, by rfl⟩ : syracuseStep 2670347 = 4005521) B4005521
theorem B2670359 : Blo 1780091 2670359 := bstep (se 1 (by rfl) ⟨2002769, by rfl⟩ : syracuseStep 2670359 = 4005539) B4005539
theorem B4005683 : Blo 1780091 4005683 := bstep (se 1 (by rfl) ⟨3004262, by rfl⟩ : syracuseStep 4005683 = 6008525) B6008525
theorem B19259201 : Blo 1780091 19259201 := bstep (se 2 (by rfl) ⟨7222200, by rfl⟩ : syracuseStep 19259201 = 14444401) B14444401
theorem B6012737 : Blo 1780091 6012737 := bstep (se 2 (by rfl) ⟨2254776, by rfl⟩ : syracuseStep 6012737 = 4509553) B4509553
theorem B4816705 : Blo 1780091 4816705 := bstep (se 2 (by rfl) ⟨1806264, by rfl⟩ : syracuseStep 4816705 = 3612529) B3612529
theorem B4005719 : Blo 1780091 4005719 := bstep (se 1 (by rfl) ⟨3004289, by rfl⟩ : syracuseStep 4005719 = 6008579) B6008579
theorem B2670425 : Blo 1780091 2670425 := bstep (se 2 (by rfl) ⟨1001409, by rfl⟩ : syracuseStep 2670425 = 2002819) B2002819
theorem B9633667 : Blo 1780091 9633667 := bstep (se 1 (by rfl) ⟨7225250, by rfl⟩ : syracuseStep 9633667 = 14450501) B14450501
theorem B5562263 : Blo 1780091 5562263 := bstep (se 1 (by rfl) ⟨4171697, by rfl⟩ : syracuseStep 5562263 = 8343395) B8343395
theorem B6504343 : Blo 1780091 6504343 := bstep (se 1 (by rfl) ⟨4878257, by rfl⟩ : syracuseStep 6504343 = 9756515) B9756515
theorem B2670539 : Blo 1780091 2670539 := bstep (se 1 (by rfl) ⟨2002904, by rfl⟩ : syracuseStep 2670539 = 4005809) B4005809
theorem B2670551 : Blo 1780091 2670551 := bstep (se 1 (by rfl) ⟨2002913, by rfl⟩ : syracuseStep 2670551 = 4005827) B4005827
theorem B2670599 : Blo 1780091 2670599 := bstep (se 1 (by rfl) ⟨2002949, by rfl⟩ : syracuseStep 2670599 = 4005899) B4005899
theorem B2670635 : Blo 1780091 2670635 := bstep (se 1 (by rfl) ⟨2002976, by rfl⟩ : syracuseStep 2670635 = 4005953) B4005953
theorem B10141757 : Blo 1780091 10141757 := bstep (se 3 (by rfl) ⟨1901579, by rfl⟩ : syracuseStep 10141757 = 3803159) B3803159
theorem B2670665 : Blo 1780091 2670665 := bstep (se 2 (by rfl) ⟨1001499, by rfl⟩ : syracuseStep 2670665 = 2002999) B2002999
theorem B4006007 : Blo 1780091 4006007 := bstep (se 1 (by rfl) ⟨3004505, by rfl⟩ : syracuseStep 4006007 = 6009011) B6009011
theorem B9019511 : Blo 1780091 9019511 := bstep (se 1 (by rfl) ⟨6764633, by rfl⟩ : syracuseStep 9019511 = 13529267) B13529267
theorem B2670779 : Blo 1780091 2670779 := bstep (se 1 (by rfl) ⟨2003084, by rfl⟩ : syracuseStep 2670779 = 4006169) B4006169
theorem B15220973 : Blo 1780091 15220973 := bstep (se 3 (by rfl) ⟨2853932, by rfl⟩ : syracuseStep 15220973 = 5707865) B5707865
theorem B2670839 : Blo 1780091 2670839 := bstep (se 1 (by rfl) ⟨2003129, by rfl⟩ : syracuseStep 2670839 = 4006259) B4006259
theorem B2670863 : Blo 1780091 2670863 := bstep (se 1 (by rfl) ⟨2003147, by rfl⟩ : syracuseStep 2670863 = 4006295) B4006295
theorem B4006187 : Blo 1780091 4006187 := bstep (se 1 (by rfl) ⟨3004640, by rfl⟩ : syracuseStep 4006187 = 6009281) B6009281
theorem B2670905 : Blo 1780091 2670905 := bstep (se 2 (by rfl) ⟨1001589, by rfl⟩ : syracuseStep 2670905 = 2003179) B2003179
theorem B2670983 : Blo 1780091 2670983 := bstep (se 1 (by rfl) ⟨2003237, by rfl⟩ : syracuseStep 2670983 = 4006475) B4006475
theorem B32932241 : Blo 1780091 32932241 := bstep (se 2 (by rfl) ⟨12349590, by rfl⟩ : syracuseStep 32932241 = 24699181) B24699181
theorem B6013331 : Blo 1780091 6013331 := bstep (se 1 (by rfl) ⟨4509998, by rfl⟩ : syracuseStep 6013331 = 9019997) B9019997
theorem B2671019 : Blo 1780091 2671019 := bstep (se 1 (by rfl) ⟨2003264, by rfl⟩ : syracuseStep 2671019 = 4006529) B4006529
theorem B2671049 : Blo 1780091 2671049 := bstep (se 2 (by rfl) ⟨1001643, by rfl⟩ : syracuseStep 2671049 = 2003287) B2003287
theorem B6758923 : Blo 1780091 6758923 := bstep (se 1 (by rfl) ⟨5069192, by rfl⟩ : syracuseStep 6758923 = 10138385) B10138385
theorem B9011735 : Blo 1780091 9011735 := bstep (se 1 (by rfl) ⟨6758801, by rfl⟩ : syracuseStep 9011735 = 13517603) B13517603
theorem B9626141 : Blo 1780091 9626141 := bstep (se 3 (by rfl) ⟨1804901, by rfl⟩ : syracuseStep 9626141 = 3609803) B3609803
theorem B5071403 : Blo 1780091 5071403 := bstep (se 1 (by rfl) ⟨3803552, by rfl⟩ : syracuseStep 5071403 = 7607105) B7607105
theorem B2671163 : Blo 1780091 2671163 := bstep (se 1 (by rfl) ⟨2003372, by rfl⟩ : syracuseStep 2671163 = 4006745) B4006745
theorem B2671223 : Blo 1780091 2671223 := bstep (se 1 (by rfl) ⟨2003417, by rfl⟩ : syracuseStep 2671223 = 4006835) B4006835
theorem B3007111 : Blo 1780091 3007111 := bstep (se 1 (by rfl) ⟨2255333, by rfl⟩ : syracuseStep 3007111 = 4510667) B4510667
theorem B2671247 : Blo 1780091 2671247 := bstep (se 1 (by rfl) ⟨2003435, by rfl⟩ : syracuseStep 2671247 = 4006871) B4006871
theorem B4006547 : Blo 1780091 4006547 := bstep (se 1 (by rfl) ⟨3004910, by rfl⟩ : syracuseStep 4006547 = 6009821) B6009821
theorem B2671289 : Blo 1780091 2671289 := bstep (se 2 (by rfl) ⟨1001733, by rfl⟩ : syracuseStep 2671289 = 2003467) B2003467
theorem B4506313 : Blo 1780091 4506313 := bstep (se 2 (by rfl) ⟨1689867, by rfl⟩ : syracuseStep 4506313 = 3379735) B3379735
theorem B4006601 : Blo 1780091 4006601 := bstep (se 2 (by rfl) ⟨1502475, by rfl⟩ : syracuseStep 4006601 = 3004951) B3004951
theorem B2671367 : Blo 1780091 2671367 := bstep (se 1 (by rfl) ⟨2003525, by rfl⟩ : syracuseStep 2671367 = 4007051) B4007051
theorem B2671403 : Blo 1780091 2671403 := bstep (se 1 (by rfl) ⟨2003552, by rfl⟩ : syracuseStep 2671403 = 4007105) B4007105
theorem B6759227 : Blo 1780091 6759227 := bstep (se 1 (by rfl) ⟨5069420, by rfl⟩ : syracuseStep 6759227 = 10138841) B10138841
theorem B2671433 : Blo 1780091 2671433 := bstep (se 2 (by rfl) ⟨1001787, by rfl⟩ : syracuseStep 2671433 = 2003575) B2003575
theorem B4506455 : Blo 1780091 4506455 := bstep (se 1 (by rfl) ⟨3379841, by rfl⟩ : syracuseStep 4506455 = 6759683) B6759683
theorem B2253739 : Blo 1780091 2253739 := bstep (se 1 (by rfl) ⟨1690304, by rfl⟩ : syracuseStep 2253739 = 3380609) B3380609
theorem B9143225 : Blo 1780091 9143225 := bstep (se 2 (by rfl) ⟨3428709, by rfl⟩ : syracuseStep 9143225 = 6857419) B6857419
theorem B2671547 : Blo 1780091 2671547 := bstep (se 1 (by rfl) ⟨2003660, by rfl⟩ : syracuseStep 2671547 = 4007321) B4007321
theorem B2671607 : Blo 1780091 2671607 := bstep (se 1 (by rfl) ⟨2003705, by rfl⟩ : syracuseStep 2671607 = 4007411) B4007411
theorem B4277249 : Blo 1780091 4277249 := bstep (se 2 (by rfl) ⟨1603968, by rfl⟩ : syracuseStep 4277249 = 3207937) B3207937
theorem B2671631 : Blo 1780091 2671631 := bstep (se 1 (by rfl) ⟨2003723, by rfl⟩ : syracuseStep 2671631 = 4007447) B4007447
theorem B2671673 : Blo 1780091 2671673 := bstep (se 2 (by rfl) ⟨1001877, by rfl⟩ : syracuseStep 2671673 = 2003755) B2003755
theorem B9020483 : Blo 1780091 9020483 := bstep (se 1 (by rfl) ⟨6765362, by rfl⟩ : syracuseStep 9020483 = 13530725) B13530725
theorem B7611479 : Blo 1780091 7611479 := bstep (se 1 (by rfl) ⟨5708609, by rfl⟩ : syracuseStep 7611479 = 11417219) B11417219
theorem B22815877 : Blo 1780091 22815877 := bstep (se 4 (by rfl) ⟨2138988, by rfl⟩ : syracuseStep 22815877 = 4277977) B4277977
theorem B2671751 : Blo 1780091 2671751 := bstep (se 1 (by rfl) ⟨2003813, by rfl⟩ : syracuseStep 2671751 = 4007627) B4007627
theorem B2671787 : Blo 1780091 2671787 := bstep (se 1 (by rfl) ⟨2003840, by rfl⟩ : syracuseStep 2671787 = 4007681) B4007681
theorem B3802297 : Blo 1780091 3802297 := bstep (se 2 (by rfl) ⟨1425861, by rfl⟩ : syracuseStep 3802297 = 2851723) B2851723
theorem B2671817 : Blo 1780091 2671817 := bstep (se 2 (by rfl) ⟨1001931, by rfl⟩ : syracuseStep 2671817 = 2003863) B2003863
theorem B38536397 : Blo 1780091 38536397 := bstep (se 3 (by rfl) ⟨7225574, by rfl⟩ : syracuseStep 38536397 = 14451149) B14451149
theorem B6759713 : Blo 1780091 6759713 := bstep (se 2 (by rfl) ⟨2534892, by rfl⟩ : syracuseStep 6759713 = 5069785) B5069785
theorem B9143603 : Blo 1780091 9143603 := bstep (se 1 (by rfl) ⟨6857702, by rfl⟩ : syracuseStep 9143603 = 13715405) B13715405
theorem B2671931 : Blo 1780091 2671931 := bstep (se 1 (by rfl) ⟨2003948, by rfl⟩ : syracuseStep 2671931 = 4007897) B4007897
theorem B2671991 : Blo 1780091 2671991 := bstep (se 1 (by rfl) ⟨2003993, by rfl⟩ : syracuseStep 2671991 = 4007987) B4007987
theorem B200263043 : Blo 1780091 200263043 := bstep (se 1 (by rfl) ⟨150197282, by rfl⟩ : syracuseStep 200263043 = 300394565) B300394565
theorem B2139527 : Blo 1780091 2139527 := bstep (se 1 (by rfl) ⟨1604645, by rfl⟩ : syracuseStep 2139527 = 3209291) B3209291
theorem B4007303 : Blo 1780091 4007303 := bstep (se 1 (by rfl) ⟨3005477, by rfl⟩ : syracuseStep 4007303 = 6010955) B6010955
theorem B9020807 : Blo 1780091 9020807 := bstep (se 1 (by rfl) ⟨6765605, by rfl⟩ : syracuseStep 9020807 = 13531211) B13531211
theorem B2672015 : Blo 1780091 2672015 := bstep (se 1 (by rfl) ⟨2004011, by rfl⟩ : syracuseStep 2672015 = 4008023) B4008023
theorem B79136185 : Blo 1780091 79136185 := bstep (se 2 (by rfl) ⟨29676069, by rfl⟩ : syracuseStep 79136185 = 59352139) B59352139
theorem B2672057 : Blo 1780091 2672057 := bstep (se 2 (by rfl) ⟨1002021, by rfl⟩ : syracuseStep 2672057 = 2004043) B2004043
theorem B34244045 : Blo 1780091 34244045 := bstep (se 3 (by rfl) ⟨6420758, by rfl⟩ : syracuseStep 34244045 = 12841517) B12841517
theorem B2672135 : Blo 1780091 2672135 := bstep (se 1 (by rfl) ⟨2004101, by rfl⟩ : syracuseStep 2672135 = 4008203) B4008203
theorem B3802639 : Blo 1780091 3802639 := bstep (se 1 (by rfl) ⟨2851979, by rfl⟩ : syracuseStep 3802639 = 5703959) B5703959
theorem B4457999 : Blo 1780091 4457999 := bstep (se 1 (by rfl) ⟨3343499, by rfl⟩ : syracuseStep 4457999 = 6686999) B6686999
theorem B2139691 : Blo 1780091 2139691 := bstep (se 1 (by rfl) ⟨1604768, by rfl⟩ : syracuseStep 2139691 = 3209537) B3209537
theorem B2672171 : Blo 1780091 2672171 := bstep (se 1 (by rfl) ⟨2004128, by rfl⟩ : syracuseStep 2672171 = 4008257) B4008257
theorem B4007483 : Blo 1780091 4007483 := bstep (se 1 (by rfl) ⟨3005612, by rfl⟩ : syracuseStep 4007483 = 6011225) B6011225
theorem B2672201 : Blo 1780091 2672201 := bstep (se 2 (by rfl) ⟨1002075, by rfl⟩ : syracuseStep 2672201 = 2004151) B2004151
theorem B5072519 : Blo 1780091 5072519 := bstep (se 1 (by rfl) ⟨3804389, by rfl⟩ : syracuseStep 5072519 = 7608779) B7608779
theorem B4007609 : Blo 1780091 4007609 := bstep (se 2 (by rfl) ⟨1502853, by rfl⟩ : syracuseStep 4007609 = 3005707) B3005707
theorem B2672315 : Blo 1780091 2672315 := bstep (se 1 (by rfl) ⟨2004236, by rfl⟩ : syracuseStep 2672315 = 4008473) B4008473
theorem B2672375 : Blo 1780091 2672375 := bstep (se 1 (by rfl) ⟨2004281, by rfl⟩ : syracuseStep 2672375 = 4008563) B4008563
theorem B2672399 : Blo 1780091 2672399 := bstep (se 1 (by rfl) ⟨2004299, by rfl⟩ : syracuseStep 2672399 = 4008599) B4008599
theorem B2672441 : Blo 1780091 2672441 := bstep (se 2 (by rfl) ⟨1002165, by rfl⟩ : syracuseStep 2672441 = 2004331) B2004331
theorem B5072701 : Blo 1780091 5072701 := bstep (se 3 (by rfl) ⟨951131, by rfl⟩ : syracuseStep 5072701 = 1902263) B1902263
theorem B2254711 : Blo 1780091 2254711 := bstep (se 1 (by rfl) ⟨1691033, by rfl⟩ : syracuseStep 2254711 = 3382067) B3382067
theorem B2672519 : Blo 1780091 2672519 := bstep (se 1 (by rfl) ⟨2004389, by rfl⟩ : syracuseStep 2672519 = 4008779) B4008779
theorem B2672555 : Blo 1780091 2672555 := bstep (se 1 (by rfl) ⟨2004416, by rfl⟩ : syracuseStep 2672555 = 4008833) B4008833
theorem B2672585 : Blo 1780091 2672585 := bstep (se 2 (by rfl) ⟨1002219, by rfl⟩ : syracuseStep 2672585 = 2004439) B2004439
theorem B21661643 : Blo 1780091 21661643 := bstep (se 1 (by rfl) ⟨16246232, by rfl⟩ : syracuseStep 21661643 = 32492465) B32492465
theorem B4007951 : Blo 1780091 4007951 := bstep (se 1 (by rfl) ⟨3005963, by rfl⟩ : syracuseStep 4007951 = 6011927) B6011927
theorem B4007969 : Blo 1780091 4007969 := bstep (se 2 (by rfl) ⟨1502988, by rfl⟩ : syracuseStep 4007969 = 3005977) B3005977
theorem B2672699 : Blo 1780091 2672699 := bstep (se 1 (by rfl) ⟨2004524, by rfl⟩ : syracuseStep 2672699 = 4009049) B4009049
theorem B2672759 : Blo 1780091 2672759 := bstep (se 1 (by rfl) ⟨2004569, by rfl⟩ : syracuseStep 2672759 = 4009139) B4009139
theorem B2672783 : Blo 1780091 2672783 := bstep (se 1 (by rfl) ⟨2004587, by rfl⟩ : syracuseStep 2672783 = 4009175) B4009175
theorem B5073043 : Blo 1780091 5073043 := bstep (se 1 (by rfl) ⟨3804782, by rfl⟩ : syracuseStep 5073043 = 7609565) B7609565
theorem B2672825 : Blo 1780091 2672825 := bstep (se 2 (by rfl) ⟨1002309, by rfl⟩ : syracuseStep 2672825 = 2004619) B2004619
theorem B2255035 : Blo 1780091 2255035 := bstep (se 1 (by rfl) ⟨1691276, by rfl⟩ : syracuseStep 2255035 = 3382553) B3382553
theorem B6416621 : Blo 1780091 6416621 := bstep (se 3 (by rfl) ⟨1203116, by rfl⟩ : syracuseStep 6416621 = 2406233) B2406233
theorem B6760685 : Blo 1780091 6760685 := bstep (se 3 (by rfl) ⟨1267628, by rfl⟩ : syracuseStep 6760685 = 2535257) B2535257
theorem B2672903 : Blo 1780091 2672903 := bstep (se 1 (by rfl) ⟨2004677, by rfl⟩ : syracuseStep 2672903 = 4009355) B4009355
theorem B2672939 : Blo 1780091 2672939 := bstep (se 1 (by rfl) ⟨2004704, by rfl⟩ : syracuseStep 2672939 = 4009409) B4009409
theorem B2672969 : Blo 1780091 2672969 := bstep (se 2 (by rfl) ⟨1002363, by rfl⟩ : syracuseStep 2672969 = 2004727) B2004727
theorem B4008311 : Blo 1780091 4008311 := bstep (se 1 (by rfl) ⟨3006233, by rfl⟩ : syracuseStep 4008311 = 6012467) B6012467
theorem B1780103 : Blo 1780091 1780103 := bstep (se 1 (by rfl) ⟨1335077, by rfl⟩ : syracuseStep 1780103 = 2670155) B2670155
theorem B3803527 : Blo 1780091 3803527 := bstep (se 1 (by rfl) ⟨2852645, by rfl⟩ : syracuseStep 3803527 = 5705291) B5705291
theorem B1780111 : Blo 1780091 1780111 := bstep (se 1 (by rfl) ⟨1335083, by rfl⟩ : syracuseStep 1780111 = 2670167) B2670167
theorem B1780155 : Blo 1780091 1780155 := bstep (se 1 (by rfl) ⟨1335116, by rfl⟩ : syracuseStep 1780155 = 2670233) B2670233
theorem B2673083 : Blo 1780091 2673083 := bstep (se 1 (by rfl) ⟨2004812, by rfl⟩ : syracuseStep 2673083 = 4009625) B4009625
theorem B1780231 : Blo 1780091 1780231 := bstep (se 1 (by rfl) ⟨1335173, by rfl⟩ : syracuseStep 1780231 = 2670347) B2670347
theorem B1780239 : Blo 1780091 1780239 := bstep (se 1 (by rfl) ⟨1335179, by rfl⟩ : syracuseStep 1780239 = 2670359) B2670359
theorem B12839467 : Blo 1780091 12839467 := bstep (se 1 (by rfl) ⟨9629600, by rfl⟩ : syracuseStep 12839467 = 19259201) B19259201
theorem B4008491 : Blo 1780091 4008491 := bstep (se 1 (by rfl) ⟨3006368, by rfl⟩ : syracuseStep 4008491 = 6012737) B6012737
theorem B1780283 : Blo 1780091 1780283 := bstep (se 1 (by rfl) ⟨1335212, by rfl⟩ : syracuseStep 1780283 = 2670425) B2670425
theorem B19032641 : Blo 1780091 19032641 := bstep (se 2 (by rfl) ⟨7137240, by rfl⟩ : syracuseStep 19032641 = 14274481) B14274481
theorem B1780359 : Blo 1780091 1780359 := bstep (se 1 (by rfl) ⟨1335269, by rfl⟩ : syracuseStep 1780359 = 2670539) B2670539
theorem B1780367 : Blo 1780091 1780367 := bstep (se 1 (by rfl) ⟨1335275, by rfl⟩ : syracuseStep 1780367 = 2670551) B2670551
theorem B1780411 : Blo 1780091 1780411 := bstep (se 1 (by rfl) ⟨1335308, by rfl⟩ : syracuseStep 1780411 = 2670617) B2670617
theorem B13527809 : Blo 1780091 13527809 := bstep (se 2 (by rfl) ⟨5072928, by rfl⟩ : syracuseStep 13527809 = 10145857) B10145857
theorem B1780487 : Blo 1780091 1780487 := bstep (se 1 (by rfl) ⟨1335365, by rfl⟩ : syracuseStep 1780487 = 2670731) B2670731
theorem B11406095 : Blo 1780091 11406095 := bstep (se 1 (by rfl) ⟨8554571, by rfl⟩ : syracuseStep 11406095 = 17109143) B17109143
theorem B1780495 : Blo 1780091 1780495 := bstep (se 1 (by rfl) ⟨1335371, by rfl⟩ : syracuseStep 1780495 = 2670743) B2670743
theorem B1780539 : Blo 1780091 1780539 := bstep (se 1 (by rfl) ⟨1335404, by rfl⟩ : syracuseStep 1780539 = 2670809) B2670809
theorem B4508531 : Blo 1780091 4508531 := bstep (se 1 (by rfl) ⟨3381398, by rfl⟩ : syracuseStep 4508531 = 6762797) B6762797
theorem B1780615 : Blo 1780091 1780615 := bstep (se 1 (by rfl) ⟨1335461, by rfl⟩ : syracuseStep 1780615 = 2670923) B2670923
theorem B1780623 : Blo 1780091 1780623 := bstep (se 1 (by rfl) ⟨1335467, by rfl⟩ : syracuseStep 1780623 = 2670935) B2670935
theorem B4008851 : Blo 1780091 4008851 := bstep (se 1 (by rfl) ⟨3006638, by rfl⟩ : syracuseStep 4008851 = 6013277) B6013277
theorem B1780667 : Blo 1780091 1780667 := bstep (se 1 (by rfl) ⟨1335500, by rfl⟩ : syracuseStep 1780667 = 2671001) B2671001
theorem B4008905 : Blo 1780091 4008905 := bstep (se 2 (by rfl) ⟨1503339, by rfl⟩ : syracuseStep 4008905 = 3006679) B3006679
theorem B1780743 : Blo 1780091 1780743 := bstep (se 1 (by rfl) ⟨1335557, by rfl⟩ : syracuseStep 1780743 = 2671115) B2671115
theorem B5073931 : Blo 1780091 5073931 := bstep (se 1 (by rfl) ⟨3805448, by rfl⟩ : syracuseStep 5073931 = 7610897) B7610897
theorem B1780751 : Blo 1780091 1780751 := bstep (se 1 (by rfl) ⟨1335563, by rfl⟩ : syracuseStep 1780751 = 2671127) B2671127
theorem B1780795 : Blo 1780091 1780795 := bstep (se 1 (by rfl) ⟨1335596, by rfl⟩ : syracuseStep 1780795 = 2671193) B2671193
theorem B8678461 : Blo 1780091 8678461 := bstep (se 3 (by rfl) ⟨1627211, by rfl⟩ : syracuseStep 8678461 = 3254423) B3254423
theorem B13896791 : Blo 1780091 13896791 := bstep (se 1 (by rfl) ⟨10422593, by rfl⟩ : syracuseStep 13896791 = 20845187) B20845187
theorem B14445701 : Blo 1780091 14445701 := bstep (se 4 (by rfl) ⟨1354284, by rfl⟩ : syracuseStep 14445701 = 2708569) B2708569
theorem B1780871 : Blo 1780091 1780871 := bstep (se 1 (by rfl) ⟨1335653, by rfl⟩ : syracuseStep 1780871 = 2671307) B2671307
theorem B1780879 : Blo 1780091 1780879 := bstep (se 1 (by rfl) ⟨1335659, by rfl⟩ : syracuseStep 1780879 = 2671319) B2671319
theorem B1780923 : Blo 1780091 1780923 := bstep (se 1 (by rfl) ⟨1335692, by rfl⟩ : syracuseStep 1780923 = 2671385) B2671385
theorem B1780999 : Blo 1780091 1780999 := bstep (se 1 (by rfl) ⟨1335749, by rfl⟩ : syracuseStep 1780999 = 2671499) B2671499
theorem B1781007 : Blo 1780091 1781007 := bstep (se 1 (by rfl) ⟨1335755, by rfl⟩ : syracuseStep 1781007 = 2671511) B2671511
theorem B2534699 : Blo 1780091 2534699 := bstep (se 1 (by rfl) ⟨1901024, by rfl⟩ : syracuseStep 2534699 = 3802049) B3802049
theorem B1781051 : Blo 1780091 1781051 := bstep (se 1 (by rfl) ⟨1335788, by rfl⟩ : syracuseStep 1781051 = 2671577) B2671577
theorem B4509047 : Blo 1780091 4509047 := bstep (se 1 (by rfl) ⟨3381785, by rfl⟩ : syracuseStep 4509047 = 6763571) B6763571
theorem B1781127 : Blo 1780091 1781127 := bstep (se 1 (by rfl) ⟨1335845, by rfl⟩ : syracuseStep 1781127 = 2671691) B2671691
theorem B1781135 : Blo 1780091 1781135 := bstep (se 1 (by rfl) ⟨1335851, by rfl⟩ : syracuseStep 1781135 = 2671703) B2671703
theorem B1781179 : Blo 1780091 1781179 := bstep (se 1 (by rfl) ⟨1335884, by rfl⟩ : syracuseStep 1781179 = 2671769) B2671769
theorem B17346001 : Blo 1780091 17346001 := bstep (se 2 (by rfl) ⟨6504750, by rfl⟩ : syracuseStep 17346001 = 13009501) B13009501
theorem B5074433 : Blo 1780091 5074433 := bstep (se 2 (by rfl) ⟨1902912, by rfl⟩ : syracuseStep 5074433 = 3805825) B3805825
theorem B1781255 : Blo 1780091 1781255 := bstep (se 1 (by rfl) ⟨1335941, by rfl⟩ : syracuseStep 1781255 = 2671883) B2671883
theorem B1781263 : Blo 1780091 1781263 := bstep (se 1 (by rfl) ⟨1335947, by rfl⟩ : syracuseStep 1781263 = 2671895) B2671895
theorem B9014813 : Blo 1780091 9014813 := bstep (se 3 (by rfl) ⟨1690277, by rfl⟩ : syracuseStep 9014813 = 3380555) B3380555
theorem B6008363 : Blo 1780091 6008363 := bstep (se 1 (by rfl) ⟨4506272, by rfl⟩ : syracuseStep 6008363 = 9012545) B9012545
theorem B1781307 : Blo 1780091 1781307 := bstep (se 1 (by rfl) ⟨1335980, by rfl⟩ : syracuseStep 1781307 = 2671961) B2671961
theorem B1781383 : Blo 1780091 1781383 := bstep (se 1 (by rfl) ⟨1336037, by rfl⟩ : syracuseStep 1781383 = 2672075) B2672075
theorem B4009607 : Blo 1780091 4009607 := bstep (se 1 (by rfl) ⟨3007205, by rfl⟩ : syracuseStep 4009607 = 6014411) B6014411
theorem B1781391 : Blo 1780091 1781391 := bstep (se 1 (by rfl) ⟨1336043, by rfl⟩ : syracuseStep 1781391 = 2672087) B2672087
theorem B1781435 : Blo 1780091 1781435 := bstep (se 1 (by rfl) ⟨1336076, by rfl⟩ : syracuseStep 1781435 = 2672153) B2672153
theorem B1001082581 : Blo 1780091 1001082581 := bstep (se 7 (by rfl) ⟨11731436, by rfl⟩ : syracuseStep 1001082581 = 23462873) B23462873
theorem B138850033 : Blo 1780091 138850033 := bstep (se 2 (by rfl) ⟨52068762, by rfl⟩ : syracuseStep 138850033 = 104137525) B104137525
theorem B51343105 : Blo 1780091 51343105 := bstep (se 2 (by rfl) ⟨19253664, by rfl⟩ : syracuseStep 51343105 = 38507329) B38507329
theorem B7319297 : Blo 1780091 7319297 := bstep (se 2 (by rfl) ⟨2744736, by rfl⟩ : syracuseStep 7319297 = 5489473) B5489473
theorem B1781511 : Blo 1780091 1781511 := bstep (se 1 (by rfl) ⟨1336133, by rfl⟩ : syracuseStep 1781511 = 2672267) B2672267
theorem B1781519 : Blo 1780091 1781519 := bstep (se 1 (by rfl) ⟨1336139, by rfl⟩ : syracuseStep 1781519 = 2672279) B2672279
theorem B2002747 : Blo 1780091 2002747 := bstep (se 1 (by rfl) ⟨1502060, by rfl⟩ : syracuseStep 2002747 = 3004121) B3004121
theorem B1781563 : Blo 1780091 1781563 := bstep (se 1 (by rfl) ⟨1336172, by rfl⟩ : syracuseStep 1781563 = 2672345) B2672345
theorem B5074775 : Blo 1780091 5074775 := bstep (se 1 (by rfl) ⟨3806081, by rfl⟩ : syracuseStep 5074775 = 7612163) B7612163
theorem B1781639 : Blo 1780091 1781639 := bstep (se 1 (by rfl) ⟨1336229, by rfl⟩ : syracuseStep 1781639 = 2672459) B2672459
theorem B1781647 : Blo 1780091 1781647 := bstep (se 1 (by rfl) ⟨1336235, by rfl⟩ : syracuseStep 1781647 = 2672471) B2672471
theorem B1781691 : Blo 1780091 1781691 := bstep (se 1 (by rfl) ⟨1336268, by rfl⟩ : syracuseStep 1781691 = 2672537) B2672537
theorem B73150411 : Blo 1780091 73150411 := bstep (se 1 (by rfl) ⟨54862808, by rfl⟩ : syracuseStep 73150411 = 109725617) B109725617
theorem B9015299 : Blo 1780091 9015299 := bstep (se 1 (by rfl) ⟨6761474, by rfl⟩ : syracuseStep 9015299 = 13522949) B13522949
theorem B1781767 : Blo 1780091 1781767 := bstep (se 1 (by rfl) ⟨1336325, by rfl⟩ : syracuseStep 1781767 = 2672651) B2672651
theorem B1781775 : Blo 1780091 1781775 := bstep (se 1 (by rfl) ⟨1336331, by rfl⟩ : syracuseStep 1781775 = 2672663) B2672663
theorem B87855139 : Blo 1780091 87855139 := bstep (se 1 (by rfl) ⟨65891354, by rfl⟩ : syracuseStep 87855139 = 131782709) B131782709
theorem B1781819 : Blo 1780091 1781819 := bstep (se 1 (by rfl) ⟨1336364, by rfl⟩ : syracuseStep 1781819 = 2672729) B2672729
theorem B5705815 : Blo 1780091 5705815 := bstep (se 1 (by rfl) ⟨4279361, by rfl⟩ : syracuseStep 5705815 = 8558723) B8558723
theorem B1781895 : Blo 1780091 1781895 := bstep (se 1 (by rfl) ⟨1336421, by rfl⟩ : syracuseStep 1781895 = 2672843) B2672843
theorem B1781903 : Blo 1780091 1781903 := bstep (se 1 (by rfl) ⟨1336427, by rfl⟩ : syracuseStep 1781903 = 2672855) B2672855
theorem B1781947 : Blo 1780091 1781947 := bstep (se 1 (by rfl) ⟨1336460, by rfl⟩ : syracuseStep 1781947 = 2672921) B2672921
theorem B84537589 : Blo 1780091 84537589 := bstep (se 5 (by rfl) ⟨3962699, by rfl⟩ : syracuseStep 84537589 = 7925399) B7925399
theorem B1782023 : Blo 1780091 1782023 := bstep (se 1 (by rfl) ⟨1336517, by rfl⟩ : syracuseStep 1782023 = 2673035) B2673035
theorem B2003215 : Blo 1780091 2003215 := bstep (se 1 (by rfl) ⟨1502411, by rfl⟩ : syracuseStep 2003215 = 3004823) B3004823
theorem B1782031 : Blo 1780091 1782031 := bstep (se 1 (by rfl) ⟨1336523, by rfl⟩ : syracuseStep 1782031 = 2673047) B2673047
theorem B3805483 : Blo 1780091 3805483 := bstep (se 1 (by rfl) ⟨2854112, by rfl⟩ : syracuseStep 3805483 = 5708225) B5708225
theorem B6762811 : Blo 1780091 6762811 := bstep (se 1 (by rfl) ⟨5072108, by rfl⟩ : syracuseStep 6762811 = 10144217) B10144217
theorem B1782075 : Blo 1780091 1782075 := bstep (se 1 (by rfl) ⟨1336556, by rfl⟩ : syracuseStep 1782075 = 2673113) B2673113
theorem B4510039 : Blo 1780091 4510039 := bstep (se 1 (by rfl) ⟨3382529, by rfl⟩ : syracuseStep 4510039 = 6765059) B6765059
theorem B8122771 : Blo 1780091 8122771 := bstep (se 1 (by rfl) ⟨6092078, by rfl⟩ : syracuseStep 8122771 = 12184157) B12184157
theorem B11407837 : Blo 1780091 11407837 := bstep (se 3 (by rfl) ⟨2138969, by rfl⟩ : syracuseStep 11407837 = 4277939) B4277939
theorem B4280843 : Blo 1780091 4280843 := bstep (se 1 (by rfl) ⟨3210632, by rfl⟩ : syracuseStep 4280843 = 6421265) B6421265
theorem B4510343 : Blo 1780091 4510343 := bstep (se 1 (by rfl) ⟨3382757, by rfl⟩ : syracuseStep 4510343 = 6765515) B6765515
theorem B2536123 : Blo 1780091 2536123 := bstep (se 1 (by rfl) ⟨1902092, by rfl⟩ : syracuseStep 2536123 = 3804185) B3804185
theorem B2003719 : Blo 1780091 2003719 := bstep (se 1 (by rfl) ⟨1502789, by rfl⟩ : syracuseStep 2003719 = 3005579) B3005579
theorem B4510475 : Blo 1780091 4510475 := bstep (se 1 (by rfl) ⟨3382856, by rfl⟩ : syracuseStep 4510475 = 6765713) B6765713
theorem B6763297 : Blo 1780091 6763297 := bstep (se 2 (by rfl) ⟨2536236, by rfl⟩ : syracuseStep 6763297 = 5072473) B5072473
theorem B4281121 : Blo 1780091 4281121 := bstep (se 2 (by rfl) ⟨1605420, by rfl⟩ : syracuseStep 4281121 = 3210841) B3210841
theorem B34689829 : Blo 1780091 34689829 := bstep (se 4 (by rfl) ⟨3252171, by rfl⟩ : syracuseStep 34689829 = 6504343) B6504343
theorem B18273073 : Blo 1780091 18273073 := bstep (se 2 (by rfl) ⟨6852402, by rfl⟩ : syracuseStep 18273073 = 13704805) B13704805
theorem B6009659 : Blo 1780091 6009659 := bstep (se 1 (by rfl) ⟨4507244, by rfl⟩ : syracuseStep 6009659 = 9014489) B9014489
theorem B17593163 : Blo 1780091 17593163 := bstep (se 1 (by rfl) ⟨13194872, by rfl⟩ : syracuseStep 17593163 = 26389745) B26389745
theorem B4813721 : Blo 1780091 4813721 := bstep (se 2 (by rfl) ⟨1805145, by rfl⟩ : syracuseStep 4813721 = 3610291) B3610291
theorem B2003899 : Blo 1780091 2003899 := bstep (se 1 (by rfl) ⟨1502924, by rfl⟩ : syracuseStep 2003899 = 3005849) B3005849
theorem B3380267 : Blo 1780091 3380267 := bstep (se 1 (by rfl) ⟨2535200, by rfl⟩ : syracuseStep 3380267 = 5070401) B5070401
theorem B3708175 : Blo 1780091 3708175 := bstep (se 1 (by rfl) ⟨2781131, by rfl⟩ : syracuseStep 3708175 = 5562263) B5562263
theorem B6010145 : Blo 1780091 6010145 := bstep (se 2 (by rfl) ⟨2253804, by rfl⟩ : syracuseStep 6010145 = 4507609) B4507609
theorem B2004367 : Blo 1780091 2004367 := bstep (se 1 (by rfl) ⟨1503275, by rfl⟩ : syracuseStep 2004367 = 3006551) B3006551
theorem B12187027 : Blo 1780091 12187027 := bstep (se 1 (by rfl) ⟨9140270, by rfl⟩ : syracuseStep 12187027 = 18280541) B18280541
theorem B4281785 : Blo 1780091 4281785 := bstep (se 2 (by rfl) ⟨1605669, by rfl⟩ : syracuseStep 4281785 = 3211339) B3211339
theorem B9016919 : Blo 1780091 9016919 := bstep (se 1 (by rfl) ⟨6762689, by rfl⟩ : syracuseStep 9016919 = 13525379) B13525379
theorem B6764269 : Blo 1780091 6764269 := bstep (se 3 (by rfl) ⟨1268300, by rfl⟩ : syracuseStep 6764269 = 2536601) B2536601
theorem B3004175 : Blo 1780091 3004175 := bstep (se 1 (by rfl) ⟨2253131, by rfl⟩ : syracuseStep 3004175 = 4506263) B4506263
theorem B6010739 : Blo 1780091 6010739 := bstep (se 1 (by rfl) ⟨4508054, by rfl⟩ : syracuseStep 6010739 = 9016109) B9016109
theorem B3610487 : Blo 1780091 3610487 := bstep (se 1 (by rfl) ⟨2707865, by rfl⟩ : syracuseStep 3610487 = 5415731) B5415731
theorem B3381193 : Blo 1780091 3381193 := bstep (se 2 (by rfl) ⟨1267947, by rfl⟩ : syracuseStep 3381193 = 2535895) B2535895
theorem B3610639 : Blo 1780091 3610639 := bstep (se 1 (by rfl) ⟨2707979, by rfl⟩ : syracuseStep 3610639 = 5415959) B5415959
theorem B54835217 : Blo 1780091 54835217 := bstep (se 2 (by rfl) ⟨20563206, by rfl⟩ : syracuseStep 54835217 = 41126413) B41126413
theorem B6764573 : Blo 1780091 6764573 := bstep (se 3 (by rfl) ⟨1268357, by rfl⟩ : syracuseStep 6764573 = 2536715) B2536715
theorem B9017405 : Blo 1780091 9017405 := bstep (se 3 (by rfl) ⟨1690763, by rfl⟩ : syracuseStep 9017405 = 3381527) B3381527
theorem B32938157 : Blo 1780091 32938157 := bstep (se 3 (by rfl) ⟨6175904, by rfl⟩ : syracuseStep 32938157 = 12351809) B12351809
theorem B3004715 : Blo 1780091 3004715 := bstep (se 1 (by rfl) ⟨2253536, by rfl⟩ : syracuseStep 3004715 = 4507073) B4507073
theorem B5413235 : Blo 1780091 5413235 := bstep (se 1 (by rfl) ⟨4059926, by rfl⟩ : syracuseStep 5413235 = 8119853) B8119853
theorem B14441003 : Blo 1780091 14441003 := bstep (se 1 (by rfl) ⟨10830752, by rfl⟩ : syracuseStep 14441003 = 21661505) B21661505
theorem B4569643 : Blo 1780091 4569643 := bstep (se 1 (by rfl) ⟨3427232, by rfl⟩ : syracuseStep 4569643 = 6854465) B6854465
theorem B39033409 : Blo 1780091 39033409 := bstep (se 2 (by rfl) ⟨14637528, by rfl⟩ : syracuseStep 39033409 = 29275057) B29275057
theorem B3381907 : Blo 1780091 3381907 := bstep (se 1 (by rfl) ⟨2536430, by rfl⟩ : syracuseStep 3381907 = 5072861) B5072861
theorem B3005113 : Blo 1780091 3005113 := bstep (se 2 (by rfl) ⟨1126917, by rfl⟩ : syracuseStep 3005113 = 2253835) B2253835
theorem B10140551 : Blo 1780091 10140551 := bstep (se 1 (by rfl) ⟨7605413, by rfl⟩ : syracuseStep 10140551 = 15210827) B15210827
theorem B7609241 : Blo 1780091 7609241 := bstep (se 2 (by rfl) ⟨2853465, by rfl⟩ : syracuseStep 7609241 = 5706931) B5706931
theorem B8559569 : Blo 1780091 8559569 := bstep (se 2 (by rfl) ⟨3209838, by rfl⟩ : syracuseStep 8559569 = 6419677) B6419677
theorem B2407439 : Blo 1780091 2407439 := bstep (se 1 (by rfl) ⟨1805579, by rfl⟩ : syracuseStep 2407439 = 3611159) B3611159
theorem B13532183 : Blo 1780091 13532183 := bstep (se 1 (by rfl) ⟨10149137, by rfl⟩ : syracuseStep 13532183 = 20298275) B20298275
theorem B10828829 : Blo 1780091 10828829 := bstep (se 3 (by rfl) ⟨2030405, by rfl⟩ : syracuseStep 10828829 = 4060811) B4060811
theorem B5069911 : Blo 1780091 5069911 := bstep (se 1 (by rfl) ⟨3802433, by rfl⟩ : syracuseStep 5069911 = 7604867) B7604867
theorem B7609463 : Blo 1780091 7609463 := bstep (se 1 (by rfl) ⟨5707097, by rfl⟩ : syracuseStep 7609463 = 11414195) B11414195
theorem B3005815 : Blo 1780091 3005815 := bstep (se 1 (by rfl) ⟨2254361, by rfl⟩ : syracuseStep 3005815 = 4508723) B4508723
theorem B9624977 : Blo 1780091 9624977 := bstep (se 2 (by rfl) ⟨3609366, by rfl⟩ : syracuseStep 9624977 = 7218733) B7218733
theorem B6421913 : Blo 1780091 6421913 := bstep (se 2 (by rfl) ⟨2408217, by rfl⟩ : syracuseStep 6421913 = 4816435) B4816435
theorem B43326899 : Blo 1780091 43326899 := bstep (se 1 (by rfl) ⟨32495174, by rfl⟩ : syracuseStep 43326899 = 64990349) B64990349
theorem B4005305 : Blo 1780091 4005305 := bstep (se 2 (by rfl) ⟨1501989, by rfl⟩ : syracuseStep 4005305 = 3003979) B3003979
theorem B22814237 : Blo 1780091 22814237 := bstep (se 3 (by rfl) ⟨4277669, by rfl⟩ : syracuseStep 22814237 = 8555339) B8555339
theorem B2670137 : Blo 1780091 2670137 := bstep (se 2 (by rfl) ⟨1001301, by rfl⟩ : syracuseStep 2670137 = 2002603) B2002603
theorem B3006011 : Blo 1780091 3006011 := bstep (se 1 (by rfl) ⟨2254508, by rfl⟩ : syracuseStep 3006011 = 4509017) B4509017
theorem B6766199 : Blo 1780091 6766199 := bstep (se 1 (by rfl) ⟨5074649, by rfl⟩ : syracuseStep 6766199 = 10149299) B10149299
theorem B2670215 : Blo 1780091 2670215 := bstep (se 1 (by rfl) ⟨2002661, by rfl⟩ : syracuseStep 2670215 = 4005323) B4005323
theorem B2670251 : Blo 1780091 2670251 := bstep (se 1 (by rfl) ⟨2002688, by rfl⟩ : syracuseStep 2670251 = 4005377) B4005377
theorem B15212225 : Blo 1780091 15212225 := bstep (se 2 (by rfl) ⟨5704584, by rfl⟩ : syracuseStep 15212225 = 11409169) B11409169
theorem B2670281 : Blo 1780091 2670281 := bstep (se 2 (by rfl) ⟨1001355, by rfl⟩ : syracuseStep 2670281 = 2002711) B2002711
theorem B3382985 : Blo 1780091 3382985 := bstep (se 2 (by rfl) ⟨1268619, by rfl⟩ : syracuseStep 3382985 = 2537239) B2537239
theorem B6422273 : Blo 1780091 6422273 := bstep (se 2 (by rfl) ⟨2408352, by rfl⟩ : syracuseStep 6422273 = 4816705) B4816705
theorem B4005647 : Blo 1780091 4005647 := bstep (se 1 (by rfl) ⟨3004235, by rfl⟩ : syracuseStep 4005647 = 6008471) B6008471
theorem B4005665 : Blo 1780091 4005665 := bstep (se 2 (by rfl) ⟨1502124, by rfl⟩ : syracuseStep 4005665 = 3004249) B3004249
theorem B17342257 : Blo 1780091 17342257 := bstep (se 2 (by rfl) ⟨6503346, by rfl⟩ : syracuseStep 17342257 = 13006693) B13006693
theorem B9019187 : Blo 1780091 9019187 := bstep (se 1 (by rfl) ⟨6764390, by rfl⟩ : syracuseStep 9019187 = 13528781) B13528781
theorem B41148209 : Blo 1780091 41148209 := bstep (se 2 (by rfl) ⟨15430578, by rfl⟩ : syracuseStep 41148209 = 30861157) B30861157
theorem B2670395 : Blo 1780091 2670395 := bstep (se 1 (by rfl) ⟨2002796, by rfl⟩ : syracuseStep 2670395 = 4005593) B4005593
theorem B12844889 : Blo 1780091 12844889 := bstep (se 2 (by rfl) ⟨4816833, by rfl⟩ : syracuseStep 12844889 = 9633667) B9633667
theorem B2670455 : Blo 1780091 2670455 := bstep (se 1 (by rfl) ⟨2002841, by rfl⟩ : syracuseStep 2670455 = 4005683) B4005683
theorem B2670479 : Blo 1780091 2670479 := bstep (se 1 (by rfl) ⟨2002859, by rfl⟩ : syracuseStep 2670479 = 4005719) B4005719
theorem B2670521 : Blo 1780091 2670521 := bstep (se 2 (by rfl) ⟨1001445, by rfl⟩ : syracuseStep 2670521 = 2002891) B2002891
theorem B3006409 : Blo 1780091 3006409 := bstep (se 2 (by rfl) ⟨1127403, by rfl⟩ : syracuseStep 3006409 = 2254807) B2254807
theorem B2670671 : Blo 1780091 2670671 := bstep (se 1 (by rfl) ⟨2003003, by rfl⟩ : syracuseStep 2670671 = 4006007) B4006007
theorem B6013007 : Blo 1780091 6013007 := bstep (se 1 (by rfl) ⟨4509755, by rfl⟩ : syracuseStep 6013007 = 9019511) B9019511
theorem B2670791 : Blo 1780091 2670791 := bstep (se 1 (by rfl) ⟨2003093, by rfl⟩ : syracuseStep 2670791 = 4006187) B4006187
theorem B3006713 : Blo 1780091 3006713 := bstep (se 2 (by rfl) ⟨1127517, by rfl⟩ : syracuseStep 3006713 = 2255035) B2255035
theorem B21954827 : Blo 1780091 21954827 := bstep (se 1 (by rfl) ⟨16466120, by rfl⟩ : syracuseStep 21954827 = 32932241) B32932241
theorem B2670953 : Blo 1780091 2670953 := bstep (se 2 (by rfl) ⟨1001607, by rfl⟩ : syracuseStep 2670953 = 2003215) B2003215
theorem B3006895 : Blo 1780091 3006895 := bstep (se 1 (by rfl) ⟨2255171, by rfl⟩ : syracuseStep 3006895 = 4510343) B4510343
theorem B2671031 : Blo 1780091 2671031 := bstep (se 1 (by rfl) ⟨2003273, by rfl⟩ : syracuseStep 2671031 = 4006547) B4006547
theorem B6013385 : Blo 1780091 6013385 := bstep (se 2 (by rfl) ⟨2255019, by rfl⟩ : syracuseStep 6013385 = 4510039) B4510039
theorem B2671067 : Blo 1780091 2671067 := bstep (se 1 (by rfl) ⟨2003300, by rfl⟩ : syracuseStep 2671067 = 4006601) B4006601
theorem B3006983 : Blo 1780091 3006983 := bstep (se 1 (by rfl) ⟨2255237, by rfl⟩ : syracuseStep 3006983 = 4510475) B4510475
theorem B5071369 : Blo 1780091 5071369 := bstep (se 2 (by rfl) ⟨1901763, by rfl⟩ : syracuseStep 5071369 = 3803527) B3803527
theorem B10830361 : Blo 1780091 10830361 := bstep (se 2 (by rfl) ⟨4061385, by rfl⟩ : syracuseStep 10830361 = 8122771) B8122771
theorem B4506151 : Blo 1780091 4506151 := bstep (se 1 (by rfl) ⟨3379613, by rfl⟩ : syracuseStep 4506151 = 6759227) B6759227
theorem B4006439 : Blo 1780091 4006439 := bstep (se 1 (by rfl) ⟨3004829, by rfl⟩ : syracuseStep 4006439 = 6009659) B6009659
theorem B6095483 : Blo 1780091 6095483 := bstep (se 1 (by rfl) ⟨4571612, by rfl⟩ : syracuseStep 6095483 = 9143225) B9143225
theorem B2851499 : Blo 1780091 2851499 := bstep (se 1 (by rfl) ⟨2138624, by rfl⟩ : syracuseStep 2851499 = 4277249) B4277249
theorem B9011897 : Blo 1780091 9011897 := bstep (se 2 (by rfl) ⟨3379461, by rfl⟩ : syracuseStep 9011897 = 6758923) B6758923
theorem B2253511 : Blo 1780091 2253511 := bstep (se 1 (by rfl) ⟨1690133, by rfl⟩ : syracuseStep 2253511 = 3380267) B3380267
theorem B6013655 : Blo 1780091 6013655 := bstep (se 1 (by rfl) ⟨4510241, by rfl⟩ : syracuseStep 6013655 = 9020483) B9020483
theorem B52044545 : Blo 1780091 52044545 := bstep (se 2 (by rfl) ⟨19516704, by rfl⟩ : syracuseStep 52044545 = 39033409) B39033409
theorem B6759197 : Blo 1780091 6759197 := bstep (se 3 (by rfl) ⟨1267349, by rfl⟩ : syracuseStep 6759197 = 2534699) B2534699
theorem B25690931 : Blo 1780091 25690931 := bstep (se 1 (by rfl) ⟨19268198, by rfl⟩ : syracuseStep 25690931 = 38536397) B38536397
theorem B4506475 : Blo 1780091 4506475 := bstep (se 1 (by rfl) ⟨3379856, by rfl⟩ : syracuseStep 4506475 = 6759713) B6759713
theorem B4006763 : Blo 1780091 4006763 := bstep (se 1 (by rfl) ⟨3005072, by rfl⟩ : syracuseStep 4006763 = 6010145) B6010145
theorem B6095735 : Blo 1780091 6095735 := bstep (se 1 (by rfl) ⟨4571801, by rfl⟩ : syracuseStep 6095735 = 9143603) B9143603
theorem B4006817 : Blo 1780091 4006817 := bstep (se 2 (by rfl) ⟨1502556, by rfl⟩ : syracuseStep 4006817 = 3005113) B3005113
theorem B2671535 : Blo 1780091 2671535 := bstep (se 1 (by rfl) ⟨2003651, by rfl⟩ : syracuseStep 2671535 = 4007303) B4007303
theorem B6013871 : Blo 1780091 6013871 := bstep (se 1 (by rfl) ⟨4510403, by rfl⟩ : syracuseStep 6013871 = 9020807) B9020807
theorem B14435293 : Blo 1780091 14435293 := bstep (se 3 (by rfl) ⟨2706617, by rfl⟩ : syracuseStep 14435293 = 5413235) B5413235
theorem B2671625 : Blo 1780091 2671625 := bstep (se 2 (by rfl) ⟨1001859, by rfl⟩ : syracuseStep 2671625 = 2003719) B2003719
theorem B2671655 : Blo 1780091 2671655 := bstep (se 1 (by rfl) ⟨2003741, by rfl⟩ : syracuseStep 2671655 = 4007483) B4007483
theorem B46253105 : Blo 1780091 46253105 := bstep (se 2 (by rfl) ⟨17344914, by rfl⟩ : syracuseStep 46253105 = 34689829) B34689829
theorem B24364097 : Blo 1780091 24364097 := bstep (se 2 (by rfl) ⟨9136536, by rfl⟩ : syracuseStep 24364097 = 18273073) B18273073
theorem B2671739 : Blo 1780091 2671739 := bstep (se 1 (by rfl) ⟨2003804, by rfl⟩ : syracuseStep 2671739 = 4007609) B4007609
theorem B4007159 : Blo 1780091 4007159 := bstep (se 1 (by rfl) ⟨3005369, by rfl⟩ : syracuseStep 4007159 = 6010739) B6010739
theorem B2671865 : Blo 1780091 2671865 := bstep (se 2 (by rfl) ⟨1001949, by rfl⟩ : syracuseStep 2671865 = 2003899) B2003899
theorem B2671967 : Blo 1780091 2671967 := bstep (se 1 (by rfl) ⟨2003975, by rfl⟩ : syracuseStep 2671967 = 4007951) B4007951
theorem B2671979 : Blo 1780091 2671979 := bstep (se 1 (by rfl) ⟨2003984, by rfl⟩ : syracuseStep 2671979 = 4007969) B4007969
theorem B6759881 : Blo 1780091 6759881 := bstep (se 2 (by rfl) ⟨2534955, by rfl⟩ : syracuseStep 6759881 = 5069911) B5069911
theorem B4277747 : Blo 1780091 4277747 := bstep (se 1 (by rfl) ⟨3208310, by rfl⟩ : syracuseStep 4277747 = 6416621) B6416621
theorem B4507123 : Blo 1780091 4507123 := bstep (se 1 (by rfl) ⟨3380342, by rfl⟩ : syracuseStep 4507123 = 6760685) B6760685
theorem B2672207 : Blo 1780091 2672207 := bstep (se 1 (by rfl) ⟨2004155, by rfl⟩ : syracuseStep 2672207 = 4008311) B4008311
theorem B9627335 : Blo 1780091 9627335 := bstep (se 1 (by rfl) ⟨7220501, by rfl⟩ : syracuseStep 9627335 = 14441003) B14441003
theorem B2672327 : Blo 1780091 2672327 := bstep (se 1 (by rfl) ⟨2004245, by rfl⟩ : syracuseStep 2672327 = 4008491) B4008491
theorem B4007753 : Blo 1780091 4007753 := bstep (se 2 (by rfl) ⟨1502907, by rfl⟩ : syracuseStep 4007753 = 3005815) B3005815
theorem B7604063 : Blo 1780091 7604063 := bstep (se 1 (by rfl) ⟨5703047, by rfl⟩ : syracuseStep 7604063 = 11406095) B11406095
theorem B2672489 : Blo 1780091 2672489 := bstep (se 2 (by rfl) ⟨1002183, by rfl⟩ : syracuseStep 2672489 = 2004367) B2004367
theorem B9021293 : Blo 1780091 9021293 := bstep (se 3 (by rfl) ⟨1691492, by rfl⟩ : syracuseStep 9021293 = 3382985) B3382985
theorem B105514913 : Blo 1780091 105514913 := bstep (se 2 (by rfl) ⟨39568092, by rfl⟩ : syracuseStep 105514913 = 79136185) B79136185
theorem B6760367 : Blo 1780091 6760367 := bstep (se 1 (by rfl) ⟨5070275, by rfl⟩ : syracuseStep 6760367 = 10140551) B10140551
theorem B2672567 : Blo 1780091 2672567 := bstep (se 1 (by rfl) ⟨2004425, by rfl⟩ : syracuseStep 2672567 = 4008851) B4008851
theorem B5072827 : Blo 1780091 5072827 := bstep (se 1 (by rfl) ⟨3804620, by rfl⟩ : syracuseStep 5072827 = 7609241) B7609241
theorem B23128001 : Blo 1780091 23128001 := bstep (se 2 (by rfl) ⟨8673000, by rfl⟩ : syracuseStep 23128001 = 17346001) B17346001
theorem B2672603 : Blo 1780091 2672603 := bstep (se 1 (by rfl) ⟨2004452, by rfl⟩ : syracuseStep 2672603 = 4008905) B4008905
theorem B9021455 : Blo 1780091 9021455 := bstep (se 1 (by rfl) ⟨6766091, by rfl⟩ : syracuseStep 9021455 = 13532183) B13532183
theorem B7219219 : Blo 1780091 7219219 := bstep (se 1 (by rfl) ⟨5414414, by rfl⟩ : syracuseStep 7219219 = 10828829) B10828829
theorem B2852921 : Blo 1780091 2852921 := bstep (se 2 (by rfl) ⟨1069845, by rfl⟩ : syracuseStep 2852921 = 2139691) B2139691
theorem B5072975 : Blo 1780091 5072975 := bstep (se 1 (by rfl) ⟨3804731, by rfl⟩ : syracuseStep 5072975 = 7609463) B7609463
theorem B6416651 : Blo 1780091 6416651 := bstep (se 1 (by rfl) ⟨4812488, by rfl⟩ : syracuseStep 6416651 = 9624977) B9624977
theorem B185133377 : Blo 1780091 185133377 := bstep (se 2 (by rfl) ⟨69425016, by rfl⟩ : syracuseStep 185133377 = 138850033) B138850033
theorem B1780091 : Blo 1780091 1780091 := bstep (se 1 (by rfl) ⟨1335068, by rfl⟩ : syracuseStep 1780091 = 2670137) B2670137
theorem B1780143 : Blo 1780091 1780143 := bstep (se 1 (by rfl) ⟨1335107, by rfl⟩ : syracuseStep 1780143 = 2670215) B2670215
theorem B2673071 : Blo 1780091 2673071 := bstep (se 1 (by rfl) ⟨2004803, by rfl⟩ : syracuseStep 2673071 = 4009607) B4009607
theorem B1780167 : Blo 1780091 1780167 := bstep (se 1 (by rfl) ⟨1335125, by rfl⟩ : syracuseStep 1780167 = 2670251) B2670251
theorem B1780187 : Blo 1780091 1780187 := bstep (se 1 (by rfl) ⟨1335140, by rfl⟩ : syracuseStep 1780187 = 2670281) B2670281
theorem B667388387 : Blo 1780091 667388387 := bstep (se 1 (by rfl) ⟨500541290, by rfl⟩ : syracuseStep 667388387 = 1001082581) B1001082581
theorem B1780263 : Blo 1780091 1780263 := bstep (se 1 (by rfl) ⟨1335197, by rfl⟩ : syracuseStep 1780263 = 2670395) B2670395
theorem B8563259 : Blo 1780091 8563259 := bstep (se 1 (by rfl) ⟨6422444, by rfl⟩ : syracuseStep 8563259 = 12844889) B12844889
theorem B1780303 : Blo 1780091 1780303 := bstep (se 1 (by rfl) ⟨1335227, by rfl⟩ : syracuseStep 1780303 = 2670455) B2670455
theorem B1780319 : Blo 1780091 1780319 := bstep (se 1 (by rfl) ⟨1335239, by rfl⟩ : syracuseStep 1780319 = 2670479) B2670479
theorem B4508257 : Blo 1780091 4508257 := bstep (se 2 (by rfl) ⟨1690596, by rfl⟩ : syracuseStep 4508257 = 3381193) B3381193
theorem B4008545 : Blo 1780091 4008545 := bstep (se 2 (by rfl) ⟨1503204, by rfl⟩ : syracuseStep 4008545 = 3006409) B3006409
theorem B1780347 : Blo 1780091 1780347 := bstep (se 1 (by rfl) ⟨1335260, by rfl⟩ : syracuseStep 1780347 = 2670521) B2670521
theorem B1780399 : Blo 1780091 1780399 := bstep (se 1 (by rfl) ⟨1335299, by rfl⟩ : syracuseStep 1780399 = 2670599) B2670599
theorem B1780423 : Blo 1780091 1780423 := bstep (se 1 (by rfl) ⟨1335317, by rfl⟩ : syracuseStep 1780423 = 2670635) B2670635
theorem B6761171 : Blo 1780091 6761171 := bstep (se 1 (by rfl) ⟨5070878, by rfl⟩ : syracuseStep 6761171 = 10141757) B10141757
theorem B117140185 : Blo 1780091 117140185 := bstep (se 2 (by rfl) ⟨43927569, by rfl⟩ : syracuseStep 117140185 = 87855139) B87855139
theorem B1780443 : Blo 1780091 1780443 := bstep (se 1 (by rfl) ⟨1335332, by rfl⟩ : syracuseStep 1780443 = 2670665) B2670665
theorem B1780519 : Blo 1780091 1780519 := bstep (se 1 (by rfl) ⟨1335389, by rfl⟩ : syracuseStep 1780519 = 2670779) B2670779
theorem B1780559 : Blo 1780091 1780559 := bstep (se 1 (by rfl) ⟨1335419, by rfl⟩ : syracuseStep 1780559 = 2670839) B2670839
theorem B1780575 : Blo 1780091 1780575 := bstep (se 1 (by rfl) ⟨1335431, by rfl⟩ : syracuseStep 1780575 = 2670863) B2670863
theorem B1780603 : Blo 1780091 1780603 := bstep (se 1 (by rfl) ⟨1335452, by rfl⟩ : syracuseStep 1780603 = 2670905) B2670905
theorem B1780655 : Blo 1780091 1780655 := bstep (se 1 (by rfl) ⟨1335491, by rfl⟩ : syracuseStep 1780655 = 2670983) B2670983
theorem B4008887 : Blo 1780091 4008887 := bstep (se 1 (by rfl) ⟨3006665, by rfl⟩ : syracuseStep 4008887 = 6013331) B6013331
theorem B1780679 : Blo 1780091 1780679 := bstep (se 1 (by rfl) ⟨1335509, by rfl⟩ : syracuseStep 1780679 = 2671019) B2671019
theorem B1780699 : Blo 1780091 1780699 := bstep (se 1 (by rfl) ⟨1335524, by rfl⟩ : syracuseStep 1780699 = 2671049) B2671049
theorem B112716785 : Blo 1780091 112716785 := bstep (se 2 (by rfl) ⟨42268794, by rfl⟩ : syracuseStep 112716785 = 84537589) B84537589
theorem B2853895 : Blo 1780091 2853895 := bstep (se 1 (by rfl) ⟨2140421, by rfl⟩ : syracuseStep 2853895 = 4280843) B4280843
theorem B6007823 : Blo 1780091 6007823 := bstep (se 1 (by rfl) ⟨4505867, by rfl⟩ : syracuseStep 6007823 = 9011735) B9011735
theorem B1780775 : Blo 1780091 1780775 := bstep (se 1 (by rfl) ⟨1335581, by rfl⟩ : syracuseStep 1780775 = 2671163) B2671163
theorem B5073977 : Blo 1780091 5073977 := bstep (se 2 (by rfl) ⟨1902741, by rfl⟩ : syracuseStep 5073977 = 3805483) B3805483
theorem B1780815 : Blo 1780091 1780815 := bstep (se 1 (by rfl) ⟨1335611, by rfl⟩ : syracuseStep 1780815 = 2671223) B2671223
theorem B1780831 : Blo 1780091 1780831 := bstep (se 1 (by rfl) ⟨1335623, by rfl⟩ : syracuseStep 1780831 = 2671247) B2671247
theorem B1780859 : Blo 1780091 1780859 := bstep (se 1 (by rfl) ⟨1335644, by rfl⟩ : syracuseStep 1780859 = 2671289) B2671289
theorem B1780911 : Blo 1780091 1780911 := bstep (se 1 (by rfl) ⟨1335683, by rfl⟩ : syracuseStep 1780911 = 2671367) B2671367
theorem B1780935 : Blo 1780091 1780935 := bstep (se 1 (by rfl) ⟨1335701, by rfl⟩ : syracuseStep 1780935 = 2671403) B2671403
theorem B1780955 : Blo 1780091 1780955 := bstep (se 1 (by rfl) ⟨1335716, by rfl⟩ : syracuseStep 1780955 = 2671433) B2671433
theorem B1781031 : Blo 1780091 1781031 := bstep (se 1 (by rfl) ⟨1335773, by rfl⟩ : syracuseStep 1781031 = 2671547) B2671547
theorem B1781071 : Blo 1780091 1781071 := bstep (se 1 (by rfl) ⟨1335803, by rfl⟩ : syracuseStep 1781071 = 2671607) B2671607
theorem B1781087 : Blo 1780091 1781087 := bstep (se 1 (by rfl) ⟨1335815, by rfl⟩ : syracuseStep 1781087 = 2671631) B2671631
theorem B1781115 : Blo 1780091 1781115 := bstep (se 1 (by rfl) ⟨1335836, by rfl⟩ : syracuseStep 1781115 = 2671673) B2671673
theorem B5074319 : Blo 1780091 5074319 := bstep (se 1 (by rfl) ⟨3805739, by rfl⟩ : syracuseStep 5074319 = 7611479) B7611479
theorem B1781167 : Blo 1780091 1781167 := bstep (se 1 (by rfl) ⟨1335875, by rfl⟩ : syracuseStep 1781167 = 2671751) B2671751
theorem B1781191 : Blo 1780091 1781191 := bstep (se 1 (by rfl) ⟨1335893, by rfl⟩ : syracuseStep 1781191 = 2671787) B2671787
theorem B1781211 : Blo 1780091 1781211 := bstep (se 1 (by rfl) ⟨1335908, by rfl⟩ : syracuseStep 1781211 = 2671817) B2671817
theorem B4009481 : Blo 1780091 4009481 := bstep (se 2 (by rfl) ⟨1503555, by rfl⟩ : syracuseStep 4009481 = 3007111) B3007111
theorem B4509209 : Blo 1780091 4509209 := bstep (se 2 (by rfl) ⟨1690953, by rfl⟩ : syracuseStep 4509209 = 3381907) B3381907
theorem B1781287 : Blo 1780091 1781287 := bstep (se 1 (by rfl) ⟨1335965, by rfl⟩ : syracuseStep 1781287 = 2671931) B2671931
theorem B1781327 : Blo 1780091 1781327 := bstep (se 1 (by rfl) ⟨1335995, by rfl⟩ : syracuseStep 1781327 = 2671991) B2671991
theorem B1781343 : Blo 1780091 1781343 := bstep (se 1 (by rfl) ⟨1336007, by rfl⟩ : syracuseStep 1781343 = 2672015) B2672015
theorem B6008417 : Blo 1780091 6008417 := bstep (se 2 (by rfl) ⟨2253156, by rfl⟩ : syracuseStep 6008417 = 4506313) B4506313
theorem B1781371 : Blo 1780091 1781371 := bstep (se 1 (by rfl) ⟨1336028, by rfl⟩ : syracuseStep 1781371 = 2672057) B2672057
theorem B2854523 : Blo 1780091 2854523 := bstep (se 1 (by rfl) ⟨2140892, by rfl⟩ : syracuseStep 2854523 = 4281785) B4281785
theorem B1781423 : Blo 1780091 1781423 := bstep (se 1 (by rfl) ⟨1336067, by rfl⟩ : syracuseStep 1781423 = 2672135) B2672135
theorem B5705405 : Blo 1780091 5705405 := bstep (se 3 (by rfl) ⟨1069763, by rfl⟩ : syracuseStep 5705405 = 2139527) B2139527
theorem B1781447 : Blo 1780091 1781447 := bstep (se 1 (by rfl) ⟨1336085, by rfl⟩ : syracuseStep 1781447 = 2672171) B2672171
theorem B1781467 : Blo 1780091 1781467 := bstep (se 1 (by rfl) ⟨1336100, by rfl⟩ : syracuseStep 1781467 = 2672201) B2672201
theorem B1781543 : Blo 1780091 1781543 := bstep (se 1 (by rfl) ⟨1336157, by rfl⟩ : syracuseStep 1781543 = 2672315) B2672315
theorem B1781583 : Blo 1780091 1781583 := bstep (se 1 (by rfl) ⟨1336187, by rfl⟩ : syracuseStep 1781583 = 2672375) B2672375
theorem B2002783 : Blo 1780091 2002783 := bstep (se 1 (by rfl) ⟨1502087, by rfl⟩ : syracuseStep 2002783 = 3004175) B3004175
theorem B1781599 : Blo 1780091 1781599 := bstep (se 1 (by rfl) ⟨1336199, by rfl⟩ : syracuseStep 1781599 = 2672399) B2672399
theorem B1781627 : Blo 1780091 1781627 := bstep (se 1 (by rfl) ⟨1336220, by rfl⟩ : syracuseStep 1781627 = 2672441) B2672441
theorem B1781679 : Blo 1780091 1781679 := bstep (se 1 (by rfl) ⟨1336259, by rfl⟩ : syracuseStep 1781679 = 2672519) B2672519
theorem B1781703 : Blo 1780091 1781703 := bstep (se 1 (by rfl) ⟨1336277, by rfl⟩ : syracuseStep 1781703 = 2672555) B2672555
theorem B1781723 : Blo 1780091 1781723 := bstep (se 1 (by rfl) ⟨1336292, by rfl⟩ : syracuseStep 1781723 = 2672585) B2672585
theorem B36556811 : Blo 1780091 36556811 := bstep (se 1 (by rfl) ⟨27417608, by rfl⟩ : syracuseStep 36556811 = 54835217) B54835217
theorem B4509715 : Blo 1780091 4509715 := bstep (se 1 (by rfl) ⟨3382286, by rfl⟩ : syracuseStep 4509715 = 6764573) B6764573
theorem B1781799 : Blo 1780091 1781799 := bstep (se 1 (by rfl) ⟨1336349, by rfl⟩ : syracuseStep 1781799 = 2672699) B2672699
theorem B25669709 : Blo 1780091 25669709 := bstep (se 3 (by rfl) ⟨4813070, by rfl⟩ : syracuseStep 25669709 = 9626141) B9626141
theorem B1781839 : Blo 1780091 1781839 := bstep (se 1 (by rfl) ⟨1336379, by rfl⟩ : syracuseStep 1781839 = 2672759) B2672759
theorem B11571281 : Blo 1780091 11571281 := bstep (se 2 (by rfl) ⟨4339230, by rfl⟩ : syracuseStep 11571281 = 8678461) B8678461
theorem B1781855 : Blo 1780091 1781855 := bstep (se 1 (by rfl) ⟨1336391, by rfl⟩ : syracuseStep 1781855 = 2672783) B2672783
theorem B21958771 : Blo 1780091 21958771 := bstep (se 1 (by rfl) ⟨16469078, by rfl⟩ : syracuseStep 21958771 = 32938157) B32938157
theorem B1781883 : Blo 1780091 1781883 := bstep (se 1 (by rfl) ⟨1336412, by rfl⟩ : syracuseStep 1781883 = 2672825) B2672825
theorem B1781935 : Blo 1780091 1781935 := bstep (se 1 (by rfl) ⟨1336451, by rfl⟩ : syracuseStep 1781935 = 2672903) B2672903
theorem B30421169 : Blo 1780091 30421169 := bstep (se 2 (by rfl) ⟨11407938, by rfl⟩ : syracuseStep 30421169 = 22815877) B22815877
theorem B2003143 : Blo 1780091 2003143 := bstep (se 1 (by rfl) ⟨1502357, by rfl⟩ : syracuseStep 2003143 = 3004715) B3004715
theorem B1781959 : Blo 1780091 1781959 := bstep (se 1 (by rfl) ⟨1336469, by rfl⟩ : syracuseStep 1781959 = 2672939) B2672939
theorem B1781979 : Blo 1780091 1781979 := bstep (se 1 (by rfl) ⟨1336484, by rfl⟩ : syracuseStep 1781979 = 2672969) B2672969
theorem B1782055 : Blo 1780091 1782055 := bstep (se 1 (by rfl) ⟨1336541, by rfl⟩ : syracuseStep 1782055 = 2673083) B2673083
theorem B4944233 : Blo 1780091 4944233 := bstep (se 2 (by rfl) ⟨1854087, by rfl⟩ : syracuseStep 4944233 = 3708175) B3708175
theorem B16249369 : Blo 1780091 16249369 := bstep (se 2 (by rfl) ⟨6093513, by rfl⟩ : syracuseStep 16249369 = 12187027) B12187027
theorem B5706379 : Blo 1780091 5706379 := bstep (se 1 (by rfl) ⟨4279784, by rfl⟩ : syracuseStep 5706379 = 8559569) B8559569
theorem B9630467 : Blo 1780091 9630467 := bstep (se 1 (by rfl) ⟨7222850, by rfl⟩ : syracuseStep 9630467 = 14445701) B14445701
theorem B109728557 : Blo 1780091 109728557 := bstep (se 3 (by rfl) ⟨20574104, by rfl⟩ : syracuseStep 109728557 = 41148209) B41148209
theorem B4281275 : Blo 1780091 4281275 := bstep (se 1 (by rfl) ⟨3210956, by rfl⟩ : syracuseStep 4281275 = 6421913) B6421913
theorem B68457473 : Blo 1780091 68457473 := bstep (se 2 (by rfl) ⟨25671552, by rfl⟩ : syracuseStep 68457473 = 51343105) B51343105
theorem B15209491 : Blo 1780091 15209491 := bstep (se 1 (by rfl) ⟨11407118, by rfl⟩ : syracuseStep 15209491 = 22814237) B22814237
theorem B6009875 : Blo 1780091 6009875 := bstep (se 1 (by rfl) ⟨4507406, by rfl⟩ : syracuseStep 6009875 = 9014813) B9014813
theorem B2004007 : Blo 1780091 2004007 := bstep (se 1 (by rfl) ⟨1503005, by rfl⟩ : syracuseStep 2004007 = 3006011) B3006011
theorem B23123009 : Blo 1780091 23123009 := bstep (se 2 (by rfl) ⟨8671128, by rfl⟩ : syracuseStep 23123009 = 17342257) B17342257
theorem B4510799 : Blo 1780091 4510799 := bstep (se 1 (by rfl) ⟨3383099, by rfl⟩ : syracuseStep 4510799 = 6766199) B6766199
theorem B6763601 : Blo 1780091 6763601 := bstep (se 2 (by rfl) ⟨2536350, by rfl⟩ : syracuseStep 6763601 = 5072701) B5072701
theorem B4879531 : Blo 1780091 4879531 := bstep (se 1 (by rfl) ⟨3659648, by rfl⟩ : syracuseStep 4879531 = 7319297) B7319297
theorem B4281515 : Blo 1780091 4281515 := bstep (se 1 (by rfl) ⟨3211136, by rfl⟩ : syracuseStep 4281515 = 6422273) B6422273
theorem B6010199 : Blo 1780091 6010199 := bstep (se 1 (by rfl) ⟨4507649, by rfl⟩ : syracuseStep 6010199 = 9015299) B9015299
theorem B6419837 : Blo 1780091 6419837 := bstep (se 3 (by rfl) ⟨1203719, by rfl⟩ : syracuseStep 6419837 = 2407439) B2407439
theorem B19256741 : Blo 1780091 19256741 := bstep (se 4 (by rfl) ⟨1805319, by rfl⟩ : syracuseStep 19256741 = 3610639) B3610639
theorem B7607753 : Blo 1780091 7607753 := bstep (se 2 (by rfl) ⟨2852907, by rfl⟩ : syracuseStep 7607753 = 5705815) B5705815
theorem B10147315 : Blo 1780091 10147315 := bstep (se 1 (by rfl) ⟨7610486, by rfl⟩ : syracuseStep 10147315 = 15220973) B15220973
theorem B6764057 : Blo 1780091 6764057 := bstep (se 2 (by rfl) ⟨2536521, by rfl⟩ : syracuseStep 6764057 = 5073043) B5073043
theorem B3380935 : Blo 1780091 3380935 := bstep (se 1 (by rfl) ⟨2535701, by rfl⟩ : syracuseStep 3380935 = 5071403) B5071403
theorem B9017081 : Blo 1780091 9017081 := bstep (se 2 (by rfl) ⟨3381405, by rfl⟩ : syracuseStep 9017081 = 6762811) B6762811
theorem B11728775 : Blo 1780091 11728775 := bstep (se 1 (by rfl) ⟨8796581, by rfl⟩ : syracuseStep 11728775 = 17593163) B17593163
theorem B3004303 : Blo 1780091 3004303 := bstep (se 1 (by rfl) ⟨2253227, by rfl⟩ : syracuseStep 3004303 = 4506455) B4506455
theorem B3209147 : Blo 1780091 3209147 := bstep (se 1 (by rfl) ⟨2406860, by rfl⟩ : syracuseStep 3209147 = 4813721) B4813721
theorem B15210449 : Blo 1780091 15210449 := bstep (se 2 (by rfl) ⟨5703918, by rfl⟩ : syracuseStep 15210449 = 11407837) B11407837
theorem B6092857 : Blo 1780091 6092857 := bstep (se 2 (by rfl) ⟨2284821, by rfl⟩ : syracuseStep 6092857 = 4569643) B4569643
theorem B17119289 : Blo 1780091 17119289 := bstep (se 2 (by rfl) ⟨6419733, by rfl⟩ : syracuseStep 17119289 = 12839467) B12839467
theorem B3381497 : Blo 1780091 3381497 := bstep (se 2 (by rfl) ⟨1268061, by rfl⟩ : syracuseStep 3381497 = 2536123) B2536123
theorem B22829363 : Blo 1780091 22829363 := bstep (se 1 (by rfl) ⟨17122022, by rfl⟩ : syracuseStep 22829363 = 34244045) B34244045
theorem B534034781 : Blo 1780091 534034781 := bstep (se 3 (by rfl) ⟨100131521, by rfl⟩ : syracuseStep 534034781 = 200263043) B200263043
theorem B2971999 : Blo 1780091 2971999 := bstep (se 1 (by rfl) ⟨2228999, by rfl⟩ : syracuseStep 2971999 = 4457999) B4457999
theorem B9017729 : Blo 1780091 9017729 := bstep (se 2 (by rfl) ⟨3381648, by rfl⟩ : syracuseStep 9017729 = 6763297) B6763297
theorem B5708161 : Blo 1780091 5708161 := bstep (se 2 (by rfl) ⟨2140560, by rfl⟩ : syracuseStep 5708161 = 4281121) B4281121
theorem B6011279 : Blo 1780091 6011279 := bstep (se 1 (by rfl) ⟨4508459, by rfl⟩ : syracuseStep 6011279 = 9016919) B9016919
theorem B3381679 : Blo 1780091 3381679 := bstep (se 1 (by rfl) ⟨2536259, by rfl⟩ : syracuseStep 3381679 = 5072519) B5072519
theorem B3004985 : Blo 1780091 3004985 := bstep (se 2 (by rfl) ⟨1126869, by rfl⟩ : syracuseStep 3004985 = 2253739) B2253739
theorem B2406991 : Blo 1780091 2406991 := bstep (se 1 (by rfl) ⟨1805243, by rfl⟩ : syracuseStep 2406991 = 3610487) B3610487
theorem B14441095 : Blo 1780091 14441095 := bstep (se 1 (by rfl) ⟨10830821, by rfl⟩ : syracuseStep 14441095 = 21661643) B21661643
theorem B6765241 : Blo 1780091 6765241 := bstep (se 2 (by rfl) ⟨2536965, by rfl⟩ : syracuseStep 6765241 = 5073931) B5073931
theorem B6011603 : Blo 1780091 6011603 := bstep (se 1 (by rfl) ⟨4508702, by rfl⟩ : syracuseStep 6011603 = 9017405) B9017405
theorem B5069729 : Blo 1780091 5069729 := bstep (se 2 (by rfl) ⟨1901148, by rfl⟩ : syracuseStep 5069729 = 3802297) B3802297
theorem B12688427 : Blo 1780091 12688427 := bstep (se 1 (by rfl) ⟨9516320, by rfl⟩ : syracuseStep 12688427 = 19032641) B19032641
theorem B9018539 : Blo 1780091 9018539 := bstep (se 1 (by rfl) ⟨6763904, by rfl⟩ : syracuseStep 9018539 = 13527809) B13527809
theorem B3005687 : Blo 1780091 3005687 := bstep (se 1 (by rfl) ⟨2254265, by rfl⟩ : syracuseStep 3005687 = 4508531) B4508531
theorem B5070185 : Blo 1780091 5070185 := bstep (se 2 (by rfl) ⟨1901319, by rfl⟩ : syracuseStep 5070185 = 3802639) B3802639
theorem B9264527 : Blo 1780091 9264527 := bstep (se 1 (by rfl) ⟨6948395, by rfl⟩ : syracuseStep 9264527 = 13896791) B13896791
theorem B3006031 : Blo 1780091 3006031 := bstep (se 1 (by rfl) ⟨2254523, by rfl⟩ : syracuseStep 3006031 = 4509047) B4509047
theorem B28884599 : Blo 1780091 28884599 := bstep (se 1 (by rfl) ⟨21663449, by rfl⟩ : syracuseStep 28884599 = 43326899) B43326899
theorem B2670203 : Blo 1780091 2670203 := bstep (se 1 (by rfl) ⟨2002652, by rfl⟩ : syracuseStep 2670203 = 4005305) B4005305
theorem B9019025 : Blo 1780091 9019025 := bstep (se 2 (by rfl) ⟨3382134, by rfl⟩ : syracuseStep 9019025 = 6764269) B6764269
theorem B3382955 : Blo 1780091 3382955 := bstep (se 1 (by rfl) ⟨2537216, by rfl⟩ : syracuseStep 3382955 = 5074433) B5074433
theorem B4005575 : Blo 1780091 4005575 := bstep (se 1 (by rfl) ⟨3004181, by rfl⟩ : syracuseStep 4005575 = 6008363) B6008363
theorem B2670329 : Blo 1780091 2670329 := bstep (se 2 (by rfl) ⟨1001373, by rfl⟩ : syracuseStep 2670329 = 2002747) B2002747
theorem B10141483 : Blo 1780091 10141483 := bstep (se 1 (by rfl) ⟨7606112, by rfl⟩ : syracuseStep 10141483 = 15212225) B15212225
theorem B3006281 : Blo 1780091 3006281 := bstep (se 2 (by rfl) ⟨1127355, by rfl⟩ : syracuseStep 3006281 = 2254711) B2254711
theorem B2670431 : Blo 1780091 2670431 := bstep (se 1 (by rfl) ⟨2002823, by rfl⟩ : syracuseStep 2670431 = 4005647) B4005647
theorem B2670443 : Blo 1780091 2670443 := bstep (se 1 (by rfl) ⟨2002832, by rfl⟩ : syracuseStep 2670443 = 4005665) B4005665
theorem B6012791 : Blo 1780091 6012791 := bstep (se 1 (by rfl) ⟨4509593, by rfl⟩ : syracuseStep 6012791 = 9019187) B9019187
theorem B3383183 : Blo 1780091 3383183 := bstep (se 1 (by rfl) ⟨2537387, by rfl⟩ : syracuseStep 3383183 = 5074775) B5074775
theorem B97533881 : Blo 1780091 97533881 := bstep (se 2 (by rfl) ⟨36575205, by rfl⟩ : syracuseStep 97533881 = 73150411) B73150411
theorem B24371207 : Blo 1780091 24371207 := bstep (se 1 (by rfl) ⟨18278405, by rfl⟩ : syracuseStep 24371207 = 36556811) B36556811
theorem B9625625 : Blo 1780091 9625625 := bstep (se 2 (by rfl) ⟨3609609, by rfl⟩ : syracuseStep 9625625 = 7219219) B7219219
theorem B6012953 : Blo 1780091 6012953 := bstep (se 2 (by rfl) ⟨2254857, by rfl⟩ : syracuseStep 6012953 = 4509715) B4509715
theorem B17113139 : Blo 1780091 17113139 := bstep (se 1 (by rfl) ⟨12834854, by rfl⟩ : syracuseStep 17113139 = 25669709) B25669709
theorem B29278361 : Blo 1780091 29278361 := bstep (se 2 (by rfl) ⟨10979385, by rfl⟩ : syracuseStep 29278361 = 21958771) B21958771
theorem B61661357 : Blo 1780091 61661357 := bstep (se 3 (by rfl) ⟨11561504, by rfl⟩ : syracuseStep 61661357 = 23123009) B23123009
theorem B2670857 : Blo 1780091 2670857 := bstep (se 2 (by rfl) ⟨1001571, by rfl⟩ : syracuseStep 2670857 = 2003143) B2003143
theorem B2670959 : Blo 1780091 2670959 := bstep (se 1 (by rfl) ⟨2003219, by rfl⟩ : syracuseStep 2670959 = 4006439) B4006439
theorem B1900999 : Blo 1780091 1900999 := bstep (se 1 (by rfl) ⟨1425749, by rfl⟩ : syracuseStep 1900999 = 2851499) B2851499
theorem B7610881 : Blo 1780091 7610881 := bstep (se 2 (by rfl) ⟨2854080, by rfl⟩ : syracuseStep 7610881 = 5708161) B5708161
theorem B4506131 : Blo 1780091 4506131 := bstep (se 1 (by rfl) ⟨3379598, by rfl⟩ : syracuseStep 4506131 = 6759197) B6759197
theorem B2671175 : Blo 1780091 2671175 := bstep (se 1 (by rfl) ⟨2003381, by rfl⟩ : syracuseStep 2671175 = 4006763) B4006763
theorem B4063823 : Blo 1780091 4063823 := bstep (se 1 (by rfl) ⟨3047867, by rfl⟩ : syracuseStep 4063823 = 6095735) B6095735
theorem B2671211 : Blo 1780091 2671211 := bstep (se 1 (by rfl) ⟨2003408, by rfl⟩ : syracuseStep 2671211 = 4006817) B4006817
theorem B45638315 : Blo 1780091 45638315 := bstep (se 1 (by rfl) ⟨34228736, by rfl⟩ : syracuseStep 45638315 = 68457473) B68457473
theorem B4006583 : Blo 1780091 4006583 := bstep (se 1 (by rfl) ⟨3004937, by rfl⟩ : syracuseStep 4006583 = 6009875) B6009875
theorem B30835403 : Blo 1780091 30835403 := bstep (se 1 (by rfl) ⟨23126552, by rfl⟩ : syracuseStep 30835403 = 46253105) B46253105
theorem B3007199 : Blo 1780091 3007199 := bstep (se 1 (by rfl) ⟨2255399, by rfl⟩ : syracuseStep 3007199 = 4510799) B4510799
theorem B2671439 : Blo 1780091 2671439 := bstep (se 1 (by rfl) ⟨2003579, by rfl⟩ : syracuseStep 2671439 = 4007159) B4007159
theorem B4006799 : Blo 1780091 4006799 := bstep (se 1 (by rfl) ⟨3005099, by rfl⟩ : syracuseStep 4006799 = 6010199) B6010199
theorem B9020321 : Blo 1780091 9020321 := bstep (se 2 (by rfl) ⟨3382620, by rfl⟩ : syracuseStep 9020321 = 6765241) B6765241
theorem B12837827 : Blo 1780091 12837827 := bstep (se 1 (by rfl) ⟨9628370, by rfl⟩ : syracuseStep 12837827 = 19256741) B19256741
theorem B4506587 : Blo 1780091 4506587 := bstep (se 1 (by rfl) ⟨3379940, by rfl⟩ : syracuseStep 4506587 = 6759881) B6759881
theorem B5071835 : Blo 1780091 5071835 := bstep (se 1 (by rfl) ⟨3803876, by rfl⟩ : syracuseStep 5071835 = 7607753) B7607753
theorem B2851831 : Blo 1780091 2851831 := bstep (se 1 (by rfl) ⟨2138873, by rfl⟩ : syracuseStep 2851831 = 4277747) B4277747
theorem B2671835 : Blo 1780091 2671835 := bstep (se 1 (by rfl) ⟨2003876, by rfl⟩ : syracuseStep 2671835 = 4007753) B4007753
theorem B6014195 : Blo 1780091 6014195 := bstep (se 1 (by rfl) ⟨4510646, by rfl⟩ : syracuseStep 6014195 = 9021293) B9021293
theorem B4506911 : Blo 1780091 4506911 := bstep (se 1 (by rfl) ⟨3380183, by rfl⟩ : syracuseStep 4506911 = 6760367) B6760367
theorem B2139431 : Blo 1780091 2139431 := bstep (se 1 (by rfl) ⟨1604573, by rfl⟩ : syracuseStep 2139431 = 3209147) B3209147
theorem B15418667 : Blo 1780091 15418667 := bstep (se 1 (by rfl) ⟨11564000, by rfl⟩ : syracuseStep 15418667 = 23128001) B23128001
theorem B6014303 : Blo 1780091 6014303 := bstep (se 1 (by rfl) ⟨4510727, by rfl⟩ : syracuseStep 6014303 = 9021455) B9021455
theorem B2672009 : Blo 1780091 2672009 := bstep (se 2 (by rfl) ⟨1002003, by rfl⟩ : syracuseStep 2672009 = 2004007) B2004007
theorem B2254331 : Blo 1780091 2254331 := bstep (se 1 (by rfl) ⟨1690748, by rfl⟩ : syracuseStep 2254331 = 3381497) B3381497
theorem B4277767 : Blo 1780091 4277767 := bstep (se 1 (by rfl) ⟨3208325, by rfl⟩ : syracuseStep 4277767 = 6416651) B6416651
theorem B123422251 : Blo 1780091 123422251 := bstep (se 1 (by rfl) ⟨92566688, by rfl⟩ : syracuseStep 123422251 = 185133377) B185133377
theorem B6506041 : Blo 1780091 6506041 := bstep (se 2 (by rfl) ⟨2439765, by rfl⟩ : syracuseStep 6506041 = 4879531) B4879531
theorem B4007519 : Blo 1780091 4007519 := bstep (se 1 (by rfl) ⟨3005639, by rfl⟩ : syracuseStep 4007519 = 6011279) B6011279
theorem B444925591 : Blo 1780091 444925591 := bstep (se 1 (by rfl) ⟨333694193, by rfl⟩ : syracuseStep 444925591 = 667388387) B667388387
theorem B2672363 : Blo 1780091 2672363 := bstep (se 1 (by rfl) ⟨2004272, by rfl⟩ : syracuseStep 2672363 = 4008545) B4008545
theorem B4507447 : Blo 1780091 4507447 := bstep (se 1 (by rfl) ⟨3380585, by rfl⟩ : syracuseStep 4507447 = 6761171) B6761171
theorem B4007735 : Blo 1780091 4007735 := bstep (se 1 (by rfl) ⟨3005801, by rfl⟩ : syracuseStep 4007735 = 6011603) B6011603
theorem B2672591 : Blo 1780091 2672591 := bstep (se 1 (by rfl) ⟨2004443, by rfl⟩ : syracuseStep 2672591 = 4008887) B4008887
theorem B4008041 : Blo 1780091 4008041 := bstep (se 2 (by rfl) ⟨1503015, by rfl⟩ : syracuseStep 4008041 = 3006031) B3006031
theorem B4507913 : Blo 1780091 4507913 := bstep (se 2 (by rfl) ⟨1690467, by rfl⟩ : syracuseStep 4507913 = 3380935) B3380935
theorem B2672987 : Blo 1780091 2672987 := bstep (se 1 (by rfl) ⟨2004740, by rfl⟩ : syracuseStep 2672987 = 4009481) B4009481
theorem B1780135 : Blo 1780091 1780135 := bstep (se 1 (by rfl) ⟨1335101, by rfl⟩ : syracuseStep 1780135 = 2670203) B2670203
theorem B1903015 : Blo 1780091 1903015 := bstep (se 1 (by rfl) ⟨1427261, by rfl⟩ : syracuseStep 1903015 = 2854523) B2854523
theorem B281373101 : Blo 1780091 281373101 := bstep (se 3 (by rfl) ⟨52757456, by rfl⟩ : syracuseStep 281373101 = 105514913) B105514913
theorem B2255303 : Blo 1780091 2255303 := bstep (se 1 (by rfl) ⟨1691477, by rfl⟩ : syracuseStep 2255303 = 3382955) B3382955
theorem B3803603 : Blo 1780091 3803603 := bstep (se 1 (by rfl) ⟨2852702, by rfl⟩ : syracuseStep 3803603 = 5705405) B5705405
theorem B1780219 : Blo 1780091 1780219 := bstep (se 1 (by rfl) ⟨1335164, by rfl⟩ : syracuseStep 1780219 = 2670329) B2670329
theorem B1780287 : Blo 1780091 1780287 := bstep (se 1 (by rfl) ⟨1335215, by rfl⟩ : syracuseStep 1780287 = 2670431) B2670431
theorem B1780295 : Blo 1780091 1780295 := bstep (se 1 (by rfl) ⟨1335221, by rfl⟩ : syracuseStep 1780295 = 2670443) B2670443
theorem B4008527 : Blo 1780091 4008527 := bstep (se 1 (by rfl) ⟨3006395, by rfl⟩ : syracuseStep 4008527 = 6012791) B6012791
theorem B2255455 : Blo 1780091 2255455 := bstep (se 1 (by rfl) ⟨1691591, by rfl⟩ : syracuseStep 2255455 = 3383183) B3383183
theorem B65022587 : Blo 1780091 65022587 := bstep (se 1 (by rfl) ⟨48766940, by rfl⟩ : syracuseStep 65022587 = 97533881) B97533881
theorem B1780447 : Blo 1780091 1780447 := bstep (se 1 (by rfl) ⟨1335335, by rfl⟩ : syracuseStep 1780447 = 2670671) B2670671
theorem B4008671 : Blo 1780091 4008671 := bstep (se 1 (by rfl) ⟨3006503, by rfl⟩ : syracuseStep 4008671 = 6013007) B6013007
theorem B1780527 : Blo 1780091 1780527 := bstep (se 1 (by rfl) ⟨1335395, by rfl⟩ : syracuseStep 1780527 = 2670791) B2670791
theorem B1780635 : Blo 1780091 1780635 := bstep (se 1 (by rfl) ⟨1335476, by rfl⟩ : syracuseStep 1780635 = 2670953) B2670953
theorem B1780687 : Blo 1780091 1780687 := bstep (se 1 (by rfl) ⟨1335515, by rfl⟩ : syracuseStep 1780687 = 2671031) B2671031
theorem B4008923 : Blo 1780091 4008923 := bstep (se 1 (by rfl) ⟨3006692, by rfl⟩ : syracuseStep 4008923 = 6013385) B6013385
theorem B1780711 : Blo 1780091 1780711 := bstep (se 1 (by rfl) ⟨1335533, by rfl⟩ : syracuseStep 1780711 = 2671067) B2671067
theorem B6007931 : Blo 1780091 6007931 := bstep (se 1 (by rfl) ⟨4505948, by rfl⟩ : syracuseStep 6007931 = 9011897) B9011897
theorem B4009103 : Blo 1780091 4009103 := bstep (se 1 (by rfl) ⟨3006827, by rfl⟩ : syracuseStep 4009103 = 6013655) B6013655
theorem B34696363 : Blo 1780091 34696363 := bstep (se 1 (by rfl) ⟨26022272, by rfl⟩ : syracuseStep 34696363 = 52044545) B52044545
theorem B4508905 : Blo 1780091 4508905 := bstep (se 2 (by rfl) ⟨1690839, by rfl⟩ : syracuseStep 4508905 = 3381679) B3381679
theorem B4009193 : Blo 1780091 4009193 := bstep (se 2 (by rfl) ⟨1503447, by rfl⟩ : syracuseStep 4009193 = 3006895) B3006895
theorem B1781023 : Blo 1780091 1781023 := bstep (se 1 (by rfl) ⟨1335767, by rfl⟩ : syracuseStep 1781023 = 2671535) B2671535
theorem B4009247 : Blo 1780091 4009247 := bstep (se 1 (by rfl) ⟨3006935, by rfl⟩ : syracuseStep 4009247 = 6013871) B6013871
theorem B1781083 : Blo 1780091 1781083 := bstep (se 1 (by rfl) ⟨1335812, by rfl⟩ : syracuseStep 1781083 = 2671625) B2671625
theorem B6761825 : Blo 1780091 6761825 := bstep (se 2 (by rfl) ⟨2535684, by rfl⟩ : syracuseStep 6761825 = 5071369) B5071369
theorem B1781103 : Blo 1780091 1781103 := bstep (se 1 (by rfl) ⟨1335827, by rfl⟩ : syracuseStep 1781103 = 2671655) B2671655
theorem B6008201 : Blo 1780091 6008201 := bstep (se 2 (by rfl) ⟨2253075, by rfl⟩ : syracuseStep 6008201 = 4506151) B4506151
theorem B4509067 : Blo 1780091 4509067 := bstep (se 1 (by rfl) ⟨3381800, by rfl⟩ : syracuseStep 4509067 = 6763601) B6763601
theorem B1781159 : Blo 1780091 1781159 := bstep (se 1 (by rfl) ⟨1335869, by rfl⟩ : syracuseStep 1781159 = 2671739) B2671739
theorem B2854343 : Blo 1780091 2854343 := bstep (se 1 (by rfl) ⟨2140757, by rfl⟩ : syracuseStep 2854343 = 4281515) B4281515
theorem B1781243 : Blo 1780091 1781243 := bstep (se 1 (by rfl) ⟨1335932, by rfl⟩ : syracuseStep 1781243 = 2671865) B2671865
theorem B19254793 : Blo 1780091 19254793 := bstep (se 2 (by rfl) ⟨7220547, by rfl⟩ : syracuseStep 19254793 = 14441095) B14441095
theorem B1781311 : Blo 1780091 1781311 := bstep (se 1 (by rfl) ⟨1335983, by rfl⟩ : syracuseStep 1781311 = 2671967) B2671967
theorem B1781319 : Blo 1780091 1781319 := bstep (se 1 (by rfl) ⟨1335989, by rfl⟩ : syracuseStep 1781319 = 2671979) B2671979
theorem B4279891 : Blo 1780091 4279891 := bstep (se 1 (by rfl) ⟨3209918, by rfl⟩ : syracuseStep 4279891 = 6419837) B6419837
theorem B13184621 : Blo 1780091 13184621 := bstep (se 3 (by rfl) ⟨2472116, by rfl⟩ : syracuseStep 13184621 = 4944233) B4944233
theorem B4509371 : Blo 1780091 4509371 := bstep (se 1 (by rfl) ⟨3382028, by rfl⟩ : syracuseStep 4509371 = 6764057) B6764057
theorem B1781471 : Blo 1780091 1781471 := bstep (se 1 (by rfl) ⟨1336103, by rfl⟩ : syracuseStep 1781471 = 2672207) B2672207
theorem B6418223 : Blo 1780091 6418223 := bstep (se 1 (by rfl) ⟨4813667, by rfl⟩ : syracuseStep 6418223 = 9627335) B9627335
theorem B1781551 : Blo 1780091 1781551 := bstep (se 1 (by rfl) ⟨1336163, by rfl⟩ : syracuseStep 1781551 = 2672327) B2672327
theorem B6008633 : Blo 1780091 6008633 := bstep (se 2 (by rfl) ⟨2253237, by rfl⟩ : syracuseStep 6008633 = 4506475) B4506475
theorem B1781659 : Blo 1780091 1781659 := bstep (se 1 (by rfl) ⟨1336244, by rfl⟩ : syracuseStep 1781659 = 2672489) B2672489
theorem B7819183 : Blo 1780091 7819183 := bstep (se 1 (by rfl) ⟨5864387, by rfl⟩ : syracuseStep 7819183 = 11728775) B11728775
theorem B1781711 : Blo 1780091 1781711 := bstep (se 1 (by rfl) ⟨1336283, by rfl⟩ : syracuseStep 1781711 = 2672567) B2672567
theorem B19247057 : Blo 1780091 19247057 := bstep (se 2 (by rfl) ⟨7217646, by rfl⟩ : syracuseStep 19247057 = 14435293) B14435293
theorem B1781735 : Blo 1780091 1781735 := bstep (se 1 (by rfl) ⟨1336301, by rfl⟩ : syracuseStep 1781735 = 2672603) B2672603
theorem B3805193 : Blo 1780091 3805193 := bstep (se 2 (by rfl) ⟨1426947, by rfl⟩ : syracuseStep 3805193 = 2853895) B2853895
theorem B20279321 : Blo 1780091 20279321 := bstep (se 2 (by rfl) ⟨7604745, by rfl⟩ : syracuseStep 20279321 = 15209491) B15209491
theorem B22835357 : Blo 1780091 22835357 := bstep (se 3 (by rfl) ⟨4281629, by rfl⟩ : syracuseStep 22835357 = 8563259) B8563259
theorem B1782047 : Blo 1780091 1782047 := bstep (se 1 (by rfl) ⟨1336535, by rfl⟩ : syracuseStep 1782047 = 2673071) B2673071
theorem B2003323 : Blo 1780091 2003323 := bstep (se 1 (by rfl) ⟨1502492, by rfl⟩ : syracuseStep 2003323 = 3004985) B3004985
theorem B3379819 : Blo 1780091 3379819 := bstep (se 1 (by rfl) ⟨2534864, by rfl⟩ : syracuseStep 3379819 = 5069729) B5069729
theorem B6009497 : Blo 1780091 6009497 := bstep (se 2 (by rfl) ⟨2253561, by rfl⟩ : syracuseStep 6009497 = 4507123) B4507123
theorem B13529753 : Blo 1780091 13529753 := bstep (se 2 (by rfl) ⟨5073657, by rfl⟩ : syracuseStep 13529753 = 10147315) B10147315
theorem B8458951 : Blo 1780091 8458951 := bstep (se 1 (by rfl) ⟨6344213, by rfl⟩ : syracuseStep 8458951 = 12688427) B12688427
theorem B2003791 : Blo 1780091 2003791 := bstep (se 1 (by rfl) ⟨1502843, by rfl⟩ : syracuseStep 2003791 = 3005687) B3005687
theorem B3380123 : Blo 1780091 3380123 := bstep (se 1 (by rfl) ⟨2535092, by rfl⟩ : syracuseStep 3380123 = 5070185) B5070185
theorem B13521977 : Blo 1780091 13521977 := bstep (se 2 (by rfl) ⟨5070741, by rfl⟩ : syracuseStep 13521977 = 10141483) B10141483
theorem B19256399 : Blo 1780091 19256399 := bstep (se 1 (by rfl) ⟨14442299, by rfl⟩ : syracuseStep 19256399 = 28884599) B28884599
theorem B11416733 : Blo 1780091 11416733 := bstep (se 3 (by rfl) ⟨2140637, by rfl⟩ : syracuseStep 11416733 = 4281275) B4281275
theorem B2004187 : Blo 1780091 2004187 := bstep (se 1 (by rfl) ⟨1503140, by rfl⟩ : syracuseStep 2004187 = 3006281) B3006281
theorem B6763769 : Blo 1780091 6763769 := bstep (se 2 (by rfl) ⟨2536413, by rfl⟩ : syracuseStep 6763769 = 5072827) B5072827
theorem B7714187 : Blo 1780091 7714187 := bstep (se 1 (by rfl) ⟨5785640, by rfl⟩ : syracuseStep 7714187 = 11571281) B11571281
theorem B8123809 : Blo 1780091 8123809 := bstep (se 2 (by rfl) ⟨3046428, by rfl⟩ : syracuseStep 8123809 = 6092857) B6092857
theorem B20280779 : Blo 1780091 20280779 := bstep (se 1 (by rfl) ⟨15210584, by rfl⟩ : syracuseStep 20280779 = 30421169) B30421169
theorem B7607789 : Blo 1780091 7607789 := bstep (se 3 (by rfl) ⟨1426460, by rfl⟩ : syracuseStep 7607789 = 2852921) B2852921
theorem B45651437 : Blo 1780091 45651437 := bstep (se 3 (by rfl) ⟨8559644, by rfl⟩ : syracuseStep 45651437 = 17119289) B17119289
theorem B2004475 : Blo 1780091 2004475 := bstep (se 1 (by rfl) ⟨1503356, by rfl⟩ : syracuseStep 2004475 = 3006713) B3006713
theorem B14636551 : Blo 1780091 14636551 := bstep (se 1 (by rfl) ⟨10977413, by rfl⟩ : syracuseStep 14636551 = 21954827) B21954827
theorem B2004655 : Blo 1780091 2004655 := bstep (se 1 (by rfl) ⟨1503491, by rfl⟩ : syracuseStep 2004655 = 3006983) B3006983
theorem B3962665 : Blo 1780091 3962665 := bstep (se 2 (by rfl) ⟨1485999, by rfl⟩ : syracuseStep 3962665 = 2971999) B2971999
theorem B6420311 : Blo 1780091 6420311 := bstep (se 1 (by rfl) ⟨4815233, by rfl⟩ : syracuseStep 6420311 = 9630467) B9630467
theorem B73152371 : Blo 1780091 73152371 := bstep (se 1 (by rfl) ⟨54864278, by rfl⟩ : syracuseStep 73152371 = 109728557) B109728557
theorem B17127287 : Blo 1780091 17127287 := bstep (se 1 (by rfl) ⟨12845465, by rfl⟩ : syracuseStep 17127287 = 25690931) B25690931
theorem B14440481 : Blo 1780091 14440481 := bstep (se 2 (by rfl) ⟨5415180, by rfl⟩ : syracuseStep 14440481 = 10830361) B10830361
theorem B21665825 : Blo 1780091 21665825 := bstep (se 2 (by rfl) ⟨8124684, by rfl⟩ : syracuseStep 21665825 = 16249369) B16249369
theorem B16242731 : Blo 1780091 16242731 := bstep (se 1 (by rfl) ⟨12182048, by rfl⟩ : syracuseStep 16242731 = 24364097) B24364097
theorem B3209321 : Blo 1780091 3209321 := bstep (se 2 (by rfl) ⟨1203495, by rfl⟩ : syracuseStep 3209321 = 2406991) B2406991
theorem B6011009 : Blo 1780091 6011009 := bstep (se 2 (by rfl) ⟨2254128, by rfl⟩ : syracuseStep 6011009 = 4508257) B4508257
theorem B7608505 : Blo 1780091 7608505 := bstep (se 2 (by rfl) ⟨2853189, by rfl⟩ : syracuseStep 7608505 = 5706379) B5706379
theorem B3004681 : Blo 1780091 3004681 := bstep (se 2 (by rfl) ⟨1126755, by rfl⟩ : syracuseStep 3004681 = 2253511) B2253511
theorem B156186913 : Blo 1780091 156186913 := bstep (se 2 (by rfl) ⟨58570092, by rfl⟩ : syracuseStep 156186913 = 117140185) B117140185
theorem B6011387 : Blo 1780091 6011387 := bstep (se 1 (by rfl) ⟨4508540, by rfl⟩ : syracuseStep 6011387 = 9017081) B9017081
theorem B5069375 : Blo 1780091 5069375 := bstep (se 1 (by rfl) ⟨3802031, by rfl⟩ : syracuseStep 5069375 = 7604063) B7604063
theorem B65018485 : Blo 1780091 65018485 := bstep (se 5 (by rfl) ⟨3047741, by rfl⟩ : syracuseStep 65018485 = 6095483) B6095483
theorem B10140299 : Blo 1780091 10140299 := bstep (se 1 (by rfl) ⟨7605224, by rfl⟩ : syracuseStep 10140299 = 15210449) B15210449
theorem B3381983 : Blo 1780091 3381983 := bstep (se 1 (by rfl) ⟨2536487, by rfl⟩ : syracuseStep 3381983 = 5072975) B5072975
theorem B15219575 : Blo 1780091 15219575 := bstep (se 1 (by rfl) ⟨11414681, by rfl⟩ : syracuseStep 15219575 = 22829363) B22829363
theorem B356023187 : Blo 1780091 356023187 := bstep (se 1 (by rfl) ⟨267017390, by rfl⟩ : syracuseStep 356023187 = 534034781) B534034781
theorem B6011819 : Blo 1780091 6011819 := bstep (se 1 (by rfl) ⟨4508864, by rfl⟩ : syracuseStep 6011819 = 9017729) B9017729
theorem B75144523 : Blo 1780091 75144523 := bstep (se 1 (by rfl) ⟨56358392, by rfl⟩ : syracuseStep 75144523 = 112716785) B112716785
theorem B4005215 : Blo 1780091 4005215 := bstep (se 1 (by rfl) ⟨3003911, by rfl⟩ : syracuseStep 4005215 = 6007823) B6007823
theorem B3382651 : Blo 1780091 3382651 := bstep (se 1 (by rfl) ⟨2536988, by rfl⟩ : syracuseStep 3382651 = 5073977) B5073977
theorem B6012359 : Blo 1780091 6012359 := bstep (se 1 (by rfl) ⟨4509269, by rfl⟩ : syracuseStep 6012359 = 9018539) B9018539
theorem B6176351 : Blo 1780091 6176351 := bstep (se 1 (by rfl) ⟨4632263, by rfl⟩ : syracuseStep 6176351 = 9264527) B9264527
theorem B3382879 : Blo 1780091 3382879 := bstep (se 1 (by rfl) ⟨2537159, by rfl⟩ : syracuseStep 3382879 = 5074319) B5074319
theorem B3006139 : Blo 1780091 3006139 := bstep (se 1 (by rfl) ⟨2254604, by rfl⟩ : syracuseStep 3006139 = 4509209) B4509209
theorem B4005611 : Blo 1780091 4005611 := bstep (se 1 (by rfl) ⟨3004208, by rfl⟩ : syracuseStep 4005611 = 6008417) B6008417
theorem B6012683 : Blo 1780091 6012683 := bstep (se 1 (by rfl) ⟨4509512, by rfl⟩ : syracuseStep 6012683 = 9019025) B9019025
theorem B2670377 : Blo 1780091 2670377 := bstep (se 2 (by rfl) ⟨1001391, by rfl⟩ : syracuseStep 2670377 = 2002783) B2002783
theorem B2670383 : Blo 1780091 2670383 := bstep (se 1 (by rfl) ⟨2002787, by rfl⟩ : syracuseStep 2670383 = 4005575) B4005575
theorem B4005737 : Blo 1780091 4005737 := bstep (se 2 (by rfl) ⟨1502151, by rfl⟩ : syracuseStep 4005737 = 3004303) B3004303
theorem B41107571 : Blo 1780091 41107571 := bstep (se 1 (by rfl) ⟨30830678, by rfl⟩ : syracuseStep 41107571 = 61661357) B61661357
theorem B4006241 : Blo 1780091 4006241 := bstep (se 2 (by rfl) ⟨1502340, by rfl⟩ : syracuseStep 4006241 = 3004681) B3004681
theorem B208249217 : Blo 1780091 208249217 := bstep (se 2 (by rfl) ⟨78093456, by rfl⟩ : syracuseStep 208249217 = 156186913) B156186913
theorem B4006331 : Blo 1780091 4006331 := bstep (se 1 (by rfl) ⟨3004748, by rfl⟩ : syracuseStep 4006331 = 6009497) B6009497
theorem B9019835 : Blo 1780091 9019835 := bstep (se 1 (by rfl) ⟨6764876, by rfl⟩ : syracuseStep 9019835 = 13529753) B13529753
theorem B30425543 : Blo 1780091 30425543 := bstep (se 1 (by rfl) ⟨22819157, by rfl⟩ : syracuseStep 30425543 = 45638315) B45638315
theorem B2671055 : Blo 1780091 2671055 := bstep (se 1 (by rfl) ⟨2003291, by rfl⟩ : syracuseStep 2671055 = 4006583) B4006583
theorem B2671097 : Blo 1780091 2671097 := bstep (se 2 (by rfl) ⟨1001661, by rfl⟩ : syracuseStep 2671097 = 2003323) B2003323
theorem B2671199 : Blo 1780091 2671199 := bstep (se 1 (by rfl) ⟨2003399, by rfl⟩ : syracuseStep 2671199 = 4006799) B4006799
theorem B2253415 : Blo 1780091 2253415 := bstep (se 1 (by rfl) ⟨1690061, by rfl⟩ : syracuseStep 2253415 = 3380123) B3380123
theorem B6013547 : Blo 1780091 6013547 := bstep (se 1 (by rfl) ⟨4510160, by rfl⟩ : syracuseStep 6013547 = 9020321) B9020321
theorem B12837599 : Blo 1780091 12837599 := bstep (se 1 (by rfl) ⟨9628199, by rfl⟩ : syracuseStep 12837599 = 19256399) B19256399
theorem B7611155 : Blo 1780091 7611155 := bstep (se 1 (by rfl) ⟨5708366, by rfl⟩ : syracuseStep 7611155 = 11416733) B11416733
theorem B2372936485 : Blo 1780091 2372936485 := bstep (se 4 (by rfl) ⟨222462795, by rfl⟩ : syracuseStep 2372936485 = 444925591) B444925591
theorem B3007273 : Blo 1780091 3007273 := bstep (se 2 (by rfl) ⟨1127727, by rfl⟩ : syracuseStep 3007273 = 2255455) B2255455
theorem B4506425 : Blo 1780091 4506425 := bstep (se 2 (by rfl) ⟨1689909, by rfl⟩ : syracuseStep 4506425 = 3379819) B3379819
theorem B5071859 : Blo 1780091 5071859 := bstep (se 1 (by rfl) ⟨3803894, by rfl⟩ : syracuseStep 5071859 = 7607789) B7607789
theorem B30434291 : Blo 1780091 30434291 := bstep (se 1 (by rfl) ⟨22825718, by rfl⟩ : syracuseStep 30434291 = 45651437) B45651437
theorem B2671679 : Blo 1780091 2671679 := bstep (se 1 (by rfl) ⟨2003759, by rfl⟩ : syracuseStep 2671679 = 4007519) B4007519
theorem B2671721 : Blo 1780091 2671721 := bstep (se 2 (by rfl) ⟨1001895, by rfl⟩ : syracuseStep 2671721 = 2003791) B2003791
theorem B6014141 : Blo 1780091 6014141 := bstep (se 3 (by rfl) ⟨1127651, by rfl⟩ : syracuseStep 6014141 = 2255303) B2255303
theorem B2671823 : Blo 1780091 2671823 := bstep (se 1 (by rfl) ⟨2003867, by rfl⟩ : syracuseStep 2671823 = 4007735) B4007735
theorem B10142941 : Blo 1780091 10142941 := bstep (se 3 (by rfl) ⟨1901801, by rfl⟩ : syracuseStep 10142941 = 3803603) B3803603
theorem B48768247 : Blo 1780091 48768247 := bstep (se 1 (by rfl) ⟨36576185, by rfl⟩ : syracuseStep 48768247 = 73152371) B73152371
theorem B9626987 : Blo 1780091 9626987 := bstep (se 1 (by rfl) ⟨7220240, by rfl⟩ : syracuseStep 9626987 = 14440481) B14440481
theorem B14443883 : Blo 1780091 14443883 := bstep (se 1 (by rfl) ⟨10832912, by rfl⟩ : syracuseStep 14443883 = 21665825) B21665825
theorem B2139547 : Blo 1780091 2139547 := bstep (se 1 (by rfl) ⟨1604660, by rfl⟩ : syracuseStep 2139547 = 3209321) B3209321
theorem B2672027 : Blo 1780091 2672027 := bstep (se 1 (by rfl) ⟨2004020, by rfl⟩ : syracuseStep 2672027 = 4008041) B4008041
theorem B4007339 : Blo 1780091 4007339 := bstep (se 1 (by rfl) ⟨3005504, by rfl⟩ : syracuseStep 4007339 = 6011009) B6011009
theorem B46261817 : Blo 1780091 46261817 := bstep (se 2 (by rfl) ⟨17348181, by rfl⟩ : syracuseStep 46261817 = 34696363) B34696363
theorem B187582067 : Blo 1780091 187582067 := bstep (se 1 (by rfl) ⟨140686550, by rfl⟩ : syracuseStep 187582067 = 281373101) B281373101
theorem B2672249 : Blo 1780091 2672249 := bstep (se 2 (by rfl) ⟨1002093, by rfl⟩ : syracuseStep 2672249 = 2004187) B2004187
theorem B4007591 : Blo 1780091 4007591 := bstep (se 1 (by rfl) ⟨3005693, by rfl⟩ : syracuseStep 4007591 = 6011387) B6011387
theorem B2672351 : Blo 1780091 2672351 := bstep (se 1 (by rfl) ⟨2004263, by rfl⟩ : syracuseStep 2672351 = 4008527) B4008527
theorem B6760199 : Blo 1780091 6760199 := bstep (se 1 (by rfl) ⟨5070149, by rfl⟩ : syracuseStep 6760199 = 10140299) B10140299
theorem B2254655 : Blo 1780091 2254655 := bstep (se 1 (by rfl) ⟨1690991, by rfl⟩ : syracuseStep 2254655 = 3381983) B3381983
theorem B2672447 : Blo 1780091 2672447 := bstep (se 1 (by rfl) ⟨2004335, by rfl⟩ : syracuseStep 2672447 = 4008671) B4008671
theorem B10831745 : Blo 1780091 10831745 := bstep (se 2 (by rfl) ⟨4061904, by rfl⟩ : syracuseStep 10831745 = 8123809) B8123809
theorem B237348791 : Blo 1780091 237348791 := bstep (se 1 (by rfl) ⟨178011593, by rfl⟩ : syracuseStep 237348791 = 356023187) B356023187
theorem B4007879 : Blo 1780091 4007879 := bstep (se 1 (by rfl) ⟨3005909, by rfl⟩ : syracuseStep 4007879 = 6011819) B6011819
theorem B2672615 : Blo 1780091 2672615 := bstep (se 1 (by rfl) ⟨2004461, by rfl⟩ : syracuseStep 2672615 = 4008923) B4008923
theorem B2672633 : Blo 1780091 2672633 := bstep (se 2 (by rfl) ⟨1002237, by rfl⟩ : syracuseStep 2672633 = 2004475) B2004475
theorem B5703689 : Blo 1780091 5703689 := bstep (se 2 (by rfl) ⟨2138883, by rfl⟩ : syracuseStep 5703689 = 4277767) B4277767
theorem B19515401 : Blo 1780091 19515401 := bstep (se 2 (by rfl) ⟨7318275, by rfl⟩ : syracuseStep 19515401 = 14636551) B14636551
theorem B164563001 : Blo 1780091 164563001 := bstep (se 2 (by rfl) ⟨61711125, by rfl⟩ : syracuseStep 164563001 = 123422251) B123422251
theorem B2672735 : Blo 1780091 2672735 := bstep (se 1 (by rfl) ⟨2004551, by rfl⟩ : syracuseStep 2672735 = 4009103) B4009103
theorem B2672795 : Blo 1780091 2672795 := bstep (se 1 (by rfl) ⟨2004596, by rfl⟩ : syracuseStep 2672795 = 4009193) B4009193
theorem B2672831 : Blo 1780091 2672831 := bstep (se 1 (by rfl) ⟨2004623, by rfl⟩ : syracuseStep 2672831 = 4009247) B4009247
theorem B2672873 : Blo 1780091 2672873 := bstep (se 2 (by rfl) ⟨1002327, by rfl⟩ : syracuseStep 2672873 = 2004655) B2004655
theorem B4507883 : Blo 1780091 4507883 := bstep (se 1 (by rfl) ⟨3380912, by rfl⟩ : syracuseStep 4507883 = 6761825) B6761825
theorem B4008185 : Blo 1780091 4008185 := bstep (se 2 (by rfl) ⟨1503069, by rfl⟩ : syracuseStep 4008185 = 3006139) B3006139
theorem B4008239 : Blo 1780091 4008239 := bstep (se 1 (by rfl) ⟨3006179, by rfl⟩ : syracuseStep 4008239 = 6012359) B6012359
theorem B1902895 : Blo 1780091 1902895 := bstep (se 1 (by rfl) ⟨1427171, by rfl⟩ : syracuseStep 1902895 = 2854343) B2854343
theorem B4008455 : Blo 1780091 4008455 := bstep (se 1 (by rfl) ⟨3006341, by rfl⟩ : syracuseStep 4008455 = 6012683) B6012683
theorem B1780251 : Blo 1780091 1780251 := bstep (se 1 (by rfl) ⟨1335188, by rfl⟩ : syracuseStep 1780251 = 2670377) B2670377
theorem B1780255 : Blo 1780091 1780255 := bstep (se 1 (by rfl) ⟨1335191, by rfl⟩ : syracuseStep 1780255 = 2670383) B2670383
theorem B4278815 : Blo 1780091 4278815 := bstep (se 1 (by rfl) ⟨3209111, by rfl⟩ : syracuseStep 4278815 = 6418223) B6418223
theorem B12831371 : Blo 1780091 12831371 := bstep (se 1 (by rfl) ⟨9623528, by rfl⟩ : syracuseStep 12831371 = 19247057) B19247057
theorem B16247471 : Blo 1780091 16247471 := bstep (se 1 (by rfl) ⟨12185603, by rfl⟩ : syracuseStep 16247471 = 24371207) B24371207
theorem B13519547 : Blo 1780091 13519547 := bstep (se 1 (by rfl) ⟨10139660, by rfl⟩ : syracuseStep 13519547 = 20279321) B20279321
theorem B6417083 : Blo 1780091 6417083 := bstep (se 1 (by rfl) ⟨4812812, by rfl⟩ : syracuseStep 6417083 = 9625625) B9625625
theorem B4008635 : Blo 1780091 4008635 := bstep (se 1 (by rfl) ⟨3006476, by rfl⟩ : syracuseStep 4008635 = 6012953) B6012953
theorem B15223571 : Blo 1780091 15223571 := bstep (se 1 (by rfl) ⟨11417678, by rfl⟩ : syracuseStep 15223571 = 22835357) B22835357
theorem B1780571 : Blo 1780091 1780571 := bstep (se 1 (by rfl) ⟨1335428, by rfl⟩ : syracuseStep 1780571 = 2670857) B2670857
theorem B1780639 : Blo 1780091 1780639 := bstep (se 1 (by rfl) ⟨1335479, by rfl⟩ : syracuseStep 1780639 = 2670959) B2670959
theorem B10144673 : Blo 1780091 10144673 := bstep (se 2 (by rfl) ⟨3804252, by rfl⟩ : syracuseStep 10144673 = 7608505) B7608505
theorem B1780783 : Blo 1780091 1780783 := bstep (se 1 (by rfl) ⟨1335587, by rfl⟩ : syracuseStep 1780783 = 2671175) B2671175
theorem B1780807 : Blo 1780091 1780807 := bstep (se 1 (by rfl) ⟨1335605, by rfl⟩ : syracuseStep 1780807 = 2671211) B2671211
theorem B20556935 : Blo 1780091 20556935 := bstep (se 1 (by rfl) ⟨15417701, by rfl⟩ : syracuseStep 20556935 = 30835403) B30835403
theorem B1780959 : Blo 1780091 1780959 := bstep (se 1 (by rfl) ⟨1335719, by rfl⟩ : syracuseStep 1780959 = 2671439) B2671439
theorem B2534665 : Blo 1780091 2534665 := bstep (se 2 (by rfl) ⟨950499, by rfl⟩ : syracuseStep 2534665 = 1900999) B1900999
theorem B9014651 : Blo 1780091 9014651 := bstep (se 1 (by rfl) ⟨6760988, by rfl⟩ : syracuseStep 9014651 = 13521977) B13521977
theorem B5705149 : Blo 1780091 5705149 := bstep (se 3 (by rfl) ⟨1069715, by rfl⟩ : syracuseStep 5705149 = 2139431) B2139431
theorem B1781223 : Blo 1780091 1781223 := bstep (se 1 (by rfl) ⟨1335917, by rfl⟩ : syracuseStep 1781223 = 2671835) B2671835
theorem B86691313 : Blo 1780091 86691313 := bstep (se 2 (by rfl) ⟨32509242, by rfl⟩ : syracuseStep 86691313 = 65018485) B65018485
theorem B4009463 : Blo 1780091 4009463 := bstep (se 1 (by rfl) ⟨3007097, by rfl⟩ : syracuseStep 4009463 = 6014195) B6014195
theorem B4509179 : Blo 1780091 4509179 := bstep (se 1 (by rfl) ⟨3381884, by rfl⟩ : syracuseStep 4509179 = 6763769) B6763769
theorem B4009535 : Blo 1780091 4009535 := bstep (se 1 (by rfl) ⟨3007151, by rfl⟩ : syracuseStep 4009535 = 6014303) B6014303
theorem B1781339 : Blo 1780091 1781339 := bstep (se 1 (by rfl) ⟨1336004, by rfl⟩ : syracuseStep 1781339 = 2672009) B2672009
theorem B13520519 : Blo 1780091 13520519 := bstep (se 1 (by rfl) ⟨10140389, by rfl⟩ : syracuseStep 13520519 = 20280779) B20280779
theorem B1781575 : Blo 1780091 1781575 := bstep (se 1 (by rfl) ⟨1336181, by rfl⟩ : syracuseStep 1781575 = 2672363) B2672363
theorem B4280207 : Blo 1780091 4280207 := bstep (se 1 (by rfl) ⟨3210155, by rfl⟩ : syracuseStep 4280207 = 6420311) B6420311
theorem B1781727 : Blo 1780091 1781727 := bstep (se 1 (by rfl) ⟨1336295, by rfl⟩ : syracuseStep 1781727 = 2672591) B2672591
theorem B1781991 : Blo 1780091 1781991 := bstep (se 1 (by rfl) ⟨1336493, by rfl⟩ : syracuseStep 1781991 = 2672987) B2672987
theorem B3379583 : Blo 1780091 3379583 := bstep (se 1 (by rfl) ⟨2534687, by rfl⟩ : syracuseStep 3379583 = 5069375) B5069375
theorem B43348391 : Blo 1780091 43348391 := bstep (se 1 (by rfl) ⟨32511293, by rfl⟩ : syracuseStep 43348391 = 65022587) B65022587
theorem B100192697 : Blo 1780091 100192697 := bstep (se 2 (by rfl) ⟨37572261, by rfl⟩ : syracuseStep 100192697 = 75144523) B75144523
theorem B4510201 : Blo 1780091 4510201 := bstep (se 2 (by rfl) ⟨1691325, by rfl⟩ : syracuseStep 4510201 = 3382651) B3382651
theorem B10146383 : Blo 1780091 10146383 := bstep (se 1 (by rfl) ⟨7609787, by rfl⟩ : syracuseStep 10146383 = 15219575) B15219575
theorem B5706521 : Blo 1780091 5706521 := bstep (se 2 (by rfl) ⟨2139945, by rfl⟩ : syracuseStep 5706521 = 4279891) B4279891
theorem B4510505 : Blo 1780091 4510505 := bstep (se 2 (by rfl) ⟨1691439, by rfl⟩ : syracuseStep 4510505 = 3382879) B3382879
theorem B4117567 : Blo 1780091 4117567 := bstep (se 1 (by rfl) ⟨3088175, by rfl⟩ : syracuseStep 4117567 = 6176351) B6176351
theorem B6009929 : Blo 1780091 6009929 := bstep (se 2 (by rfl) ⟨2253723, by rfl⟩ : syracuseStep 6009929 = 4507447) B4507447
theorem B10425577 : Blo 1780091 10425577 := bstep (se 2 (by rfl) ⟨3909591, by rfl⟩ : syracuseStep 10425577 = 7819183) B7819183
theorem B15209765 : Blo 1780091 15209765 := bstep (se 4 (by rfl) ⟨1425915, by rfl⟩ : syracuseStep 15209765 = 2851831) B2851831
theorem B2536795 : Blo 1780091 2536795 := bstep (se 1 (by rfl) ⟨1902596, by rfl⟩ : syracuseStep 2536795 = 3805193) B3805193
theorem B11408759 : Blo 1780091 11408759 := bstep (se 1 (by rfl) ⟨8556569, by rfl⟩ : syracuseStep 11408759 = 17113139) B17113139
theorem B19518907 : Blo 1780091 19518907 := bstep (se 1 (by rfl) ⟨14639180, by rfl⟩ : syracuseStep 19518907 = 29278361) B29278361
theorem B3004087 : Blo 1780091 3004087 := bstep (se 1 (by rfl) ⟨2253065, by rfl⟩ : syracuseStep 3004087 = 4506131) B4506131
theorem B2709215 : Blo 1780091 2709215 := bstep (se 1 (by rfl) ⟨2031911, by rfl⟩ : syracuseStep 2709215 = 4063823) B4063823
theorem B2004799 : Blo 1780091 2004799 := bstep (se 1 (by rfl) ⟨1503599, by rfl⟩ : syracuseStep 2004799 = 3007199) B3007199
theorem B2537353 : Blo 1780091 2537353 := bstep (se 2 (by rfl) ⟨951507, by rfl⟩ : syracuseStep 2537353 = 1903015) B1903015
theorem B8558551 : Blo 1780091 8558551 := bstep (se 1 (by rfl) ⟨6418913, by rfl⟩ : syracuseStep 8558551 = 12837827) B12837827
theorem B3004391 : Blo 1780091 3004391 := bstep (se 1 (by rfl) ⟨2253293, by rfl⟩ : syracuseStep 3004391 = 4506587) B4506587
theorem B10147841 : Blo 1780091 10147841 := bstep (se 2 (by rfl) ⟨3805440, by rfl⟩ : syracuseStep 10147841 = 7610881) B7610881
theorem B3004607 : Blo 1780091 3004607 := bstep (se 1 (by rfl) ⟨2253455, by rfl⟩ : syracuseStep 3004607 = 4506911) B4506911
theorem B10279111 : Blo 1780091 10279111 := bstep (se 1 (by rfl) ⟨7709333, by rfl⟩ : syracuseStep 10279111 = 15418667) B15418667
theorem B5142791 : Blo 1780091 5142791 := bstep (se 1 (by rfl) ⟨3857093, by rfl⟩ : syracuseStep 5142791 = 7714187) B7714187
theorem B11278601 : Blo 1780091 11278601 := bstep (se 2 (by rfl) ⟨4229475, by rfl⟩ : syracuseStep 11278601 = 8458951) B8458951
theorem B11418191 : Blo 1780091 11418191 := bstep (se 1 (by rfl) ⟨8563643, by rfl⟩ : syracuseStep 11418191 = 17127287) B17127287
theorem B6011549 : Blo 1780091 6011549 := bstep (se 3 (by rfl) ⟨1127165, by rfl⟩ : syracuseStep 6011549 = 2254331) B2254331
theorem B10828487 : Blo 1780091 10828487 := bstep (se 1 (by rfl) ⟨8121365, by rfl⟩ : syracuseStep 10828487 = 16242731) B16242731
theorem B3005275 : Blo 1780091 3005275 := bstep (se 1 (by rfl) ⟨2253956, by rfl⟩ : syracuseStep 3005275 = 4507913) B4507913
theorem B6011873 : Blo 1780091 6011873 := bstep (se 2 (by rfl) ⟨2254452, by rfl⟩ : syracuseStep 6011873 = 4508905) B4508905
theorem B6012089 : Blo 1780091 6012089 := bstep (se 2 (by rfl) ⟨2254533, by rfl⟩ : syracuseStep 6012089 = 4509067) B4509067
theorem B25673057 : Blo 1780091 25673057 := bstep (se 2 (by rfl) ⟨9627396, by rfl⟩ : syracuseStep 25673057 = 19254793) B19254793
theorem B8674721 : Blo 1780091 8674721 := bstep (se 2 (by rfl) ⟨3253020, by rfl⟩ : syracuseStep 8674721 = 6506041) B6506041
theorem B4005287 : Blo 1780091 4005287 := bstep (se 1 (by rfl) ⟨3003965, by rfl⟩ : syracuseStep 4005287 = 6007931) B6007931
theorem B2670143 : Blo 1780091 2670143 := bstep (se 1 (by rfl) ⟨2002607, by rfl⟩ : syracuseStep 2670143 = 4005215) B4005215
theorem B4005467 : Blo 1780091 4005467 := bstep (se 1 (by rfl) ⟨3004100, by rfl⟩ : syracuseStep 4005467 = 6008201) B6008201
theorem B5283553 : Blo 1780091 5283553 := bstep (se 2 (by rfl) ⟨1981332, by rfl⟩ : syracuseStep 5283553 = 3962665) B3962665
theorem B8789747 : Blo 1780091 8789747 := bstep (se 1 (by rfl) ⟨6592310, by rfl⟩ : syracuseStep 8789747 = 13184621) B13184621
theorem B3006247 : Blo 1780091 3006247 := bstep (se 1 (by rfl) ⟨2254685, by rfl⟩ : syracuseStep 3006247 = 4509371) B4509371
theorem B2670407 : Blo 1780091 2670407 := bstep (se 1 (by rfl) ⟨2002805, by rfl⟩ : syracuseStep 2670407 = 4005611) B4005611
theorem B4005755 : Blo 1780091 4005755 := bstep (se 1 (by rfl) ⟨3004316, by rfl⟩ : syracuseStep 4005755 = 6008633) B6008633
theorem B2670491 : Blo 1780091 2670491 := bstep (se 1 (by rfl) ⟨2002868, by rfl⟩ : syracuseStep 2670491 = 4005737) B4005737
theorem B13524893 : Blo 1780091 13524893 := bstep (se 3 (by rfl) ⟨2535917, by rfl⟩ : syracuseStep 13524893 = 5071835) B5071835
theorem B2670827 : Blo 1780091 2670827 := bstep (se 1 (by rfl) ⟨2003120, by rfl⟩ : syracuseStep 2670827 = 4006241) B4006241
theorem B13705481 : Blo 1780091 13705481 := bstep (se 2 (by rfl) ⟨5139555, by rfl⟩ : syracuseStep 13705481 = 10279111) B10279111
theorem B2670887 : Blo 1780091 2670887 := bstep (se 1 (by rfl) ⟨2003165, by rfl⟩ : syracuseStep 2670887 = 4006331) B4006331
theorem B6013223 : Blo 1780091 6013223 := bstep (se 1 (by rfl) ⟨4509917, by rfl⟩ : syracuseStep 6013223 = 9019835) B9019835
theorem B20283695 : Blo 1780091 20283695 := bstep (se 1 (by rfl) ⟨15212771, by rfl⟩ : syracuseStep 20283695 = 30425543) B30425543
theorem B3007003 : Blo 1780091 3007003 := bstep (se 1 (by rfl) ⟨2255252, by rfl⟩ : syracuseStep 3007003 = 4510505) B4510505
theorem B6013601 : Blo 1780091 6013601 := bstep (se 2 (by rfl) ⟨2255100, by rfl⟩ : syracuseStep 6013601 = 4510201) B4510201
theorem B13714109 : Blo 1780091 13714109 := bstep (se 3 (by rfl) ⟨2571395, by rfl⟩ : syracuseStep 13714109 = 5142791) B5142791
theorem B4006619 : Blo 1780091 4006619 := bstep (se 1 (by rfl) ⟨3004964, by rfl⟩ : syracuseStep 4006619 = 6009929) B6009929
theorem B2671559 : Blo 1780091 2671559 := bstep (se 1 (by rfl) ⟨2003669, by rfl⟩ : syracuseStep 2671559 = 4007339) B4007339
theorem B9012221 : Blo 1780091 9012221 := bstep (se 3 (by rfl) ⟨1689791, by rfl⟩ : syracuseStep 9012221 = 3379583) B3379583
theorem B3163915313 : Blo 1780091 3163915313 := bstep (se 2 (by rfl) ⟨1186468242, by rfl⟩ : syracuseStep 3163915313 = 2372936485) B2372936485
theorem B2671727 : Blo 1780091 2671727 := bstep (se 1 (by rfl) ⟨2003795, by rfl⟩ : syracuseStep 2671727 = 4007591) B4007591
theorem B4007033 : Blo 1780091 4007033 := bstep (se 2 (by rfl) ⟨1502637, by rfl⟩ : syracuseStep 4007033 = 3005275) B3005275
theorem B4506799 : Blo 1780091 4506799 := bstep (se 1 (by rfl) ⟨3380099, by rfl⟩ : syracuseStep 4506799 = 6760199) B6760199
theorem B2671919 : Blo 1780091 2671919 := bstep (se 1 (by rfl) ⟨2003939, by rfl⟩ : syracuseStep 2671919 = 4007879) B4007879
theorem B3802459 : Blo 1780091 3802459 := bstep (se 1 (by rfl) ⟨2851844, by rfl⟩ : syracuseStep 3802459 = 5703689) B5703689
theorem B13010267 : Blo 1780091 13010267 := bstep (se 1 (by rfl) ⟨9757700, by rfl⟩ : syracuseStep 13010267 = 19515401) B19515401
theorem B109708667 : Blo 1780091 109708667 := bstep (se 1 (by rfl) ⟨82281500, by rfl⟩ : syracuseStep 109708667 = 164563001) B164563001
theorem B5490089 : Blo 1780091 5490089 := bstep (se 2 (by rfl) ⟨2058783, by rfl⟩ : syracuseStep 5490089 = 4117567) B4117567
theorem B2672123 : Blo 1780091 2672123 := bstep (se 1 (by rfl) ⟨2004092, by rfl⟩ : syracuseStep 2672123 = 4008185) B4008185
theorem B2672159 : Blo 1780091 2672159 := bstep (se 1 (by rfl) ⟨2004119, by rfl⟩ : syracuseStep 2672159 = 4008239) B4008239
theorem B2672303 : Blo 1780091 2672303 := bstep (se 1 (by rfl) ⟨2004227, by rfl⟩ : syracuseStep 2672303 = 4008455) B4008455
theorem B2852543 : Blo 1780091 2852543 := bstep (se 1 (by rfl) ⟨2139407, by rfl⟩ : syracuseStep 2852543 = 4278815) B4278815
theorem B7612127 : Blo 1780091 7612127 := bstep (se 1 (by rfl) ⟨5709095, by rfl⟩ : syracuseStep 7612127 = 11418191) B11418191
theorem B8554247 : Blo 1780091 8554247 := bstep (se 1 (by rfl) ⟨6415685, by rfl⟩ : syracuseStep 8554247 = 12831371) B12831371
theorem B4007699 : Blo 1780091 4007699 := bstep (se 1 (by rfl) ⟨3005774, by rfl⟩ : syracuseStep 4007699 = 6011549) B6011549
theorem B9013031 : Blo 1780091 9013031 := bstep (se 1 (by rfl) ⟨6759773, by rfl⟩ : syracuseStep 9013031 = 13519547) B13519547
theorem B4278055 : Blo 1780091 4278055 := bstep (se 1 (by rfl) ⟨3208541, by rfl⟩ : syracuseStep 4278055 = 6417083) B6417083
theorem B2672423 : Blo 1780091 2672423 := bstep (se 1 (by rfl) ⟨2004317, by rfl⟩ : syracuseStep 2672423 = 4008635) B4008635
theorem B7218991 : Blo 1780091 7218991 := bstep (se 1 (by rfl) ⟨5414243, by rfl⟩ : syracuseStep 7218991 = 10828487) B10828487
theorem B2852729 : Blo 1780091 2852729 := bstep (se 2 (by rfl) ⟨1069773, by rfl⟩ : syracuseStep 2852729 = 2139547) B2139547
theorem B4007915 : Blo 1780091 4007915 := bstep (se 1 (by rfl) ⟨3005936, by rfl⟩ : syracuseStep 4007915 = 6011873) B6011873
theorem B4008059 : Blo 1780091 4008059 := bstep (se 1 (by rfl) ⟨3006044, by rfl⟩ : syracuseStep 4008059 = 6012089) B6012089
theorem B17115371 : Blo 1780091 17115371 := bstep (se 1 (by rfl) ⟨12836528, by rfl⟩ : syracuseStep 17115371 = 25673057) B25673057
theorem B2672975 : Blo 1780091 2672975 := bstep (se 1 (by rfl) ⟨2004731, by rfl⟩ : syracuseStep 2672975 = 4009463) B4009463
theorem B11413885 : Blo 1780091 11413885 := bstep (se 3 (by rfl) ⟨2140103, by rfl⟩ : syracuseStep 11413885 = 4280207) B4280207
theorem B1780095 : Blo 1780091 1780095 := bstep (se 1 (by rfl) ⟨1335071, by rfl⟩ : syracuseStep 1780095 = 2670143) B2670143
theorem B2673023 : Blo 1780091 2673023 := bstep (se 1 (by rfl) ⟨2004767, by rfl⟩ : syracuseStep 2673023 = 4009535) B4009535
theorem B4008329 : Blo 1780091 4008329 := bstep (se 2 (by rfl) ⟨1503123, by rfl⟩ : syracuseStep 4008329 = 3006247) B3006247
theorem B2673065 : Blo 1780091 2673065 := bstep (se 2 (by rfl) ⟨1002399, by rfl⟩ : syracuseStep 2673065 = 2004799) B2004799
theorem B9013679 : Blo 1780091 9013679 := bstep (se 1 (by rfl) ⟨6760259, by rfl⟩ : syracuseStep 9013679 = 13520519) B13520519
theorem B1780271 : Blo 1780091 1780271 := bstep (se 1 (by rfl) ⟨1335203, by rfl⟩ : syracuseStep 1780271 = 2670407) B2670407
theorem B1780327 : Blo 1780091 1780327 := bstep (se 1 (by rfl) ⟨1335245, by rfl⟩ : syracuseStep 1780327 = 2670491) B2670491
theorem B27405047 : Blo 1780091 27405047 := bstep (se 1 (by rfl) ⟨20553785, by rfl⟩ : syracuseStep 27405047 = 41107571) B41107571
theorem B138832811 : Blo 1780091 138832811 := bstep (se 1 (by rfl) ⟨104124608, by rfl⟩ : syracuseStep 138832811 = 208249217) B208249217
theorem B1780703 : Blo 1780091 1780703 := bstep (se 1 (by rfl) ⟨1335527, by rfl⟩ : syracuseStep 1780703 = 2671055) B2671055
theorem B1780731 : Blo 1780091 1780731 := bstep (se 1 (by rfl) ⟨1335548, by rfl⟩ : syracuseStep 1780731 = 2671097) B2671097
theorem B1780799 : Blo 1780091 1780799 := bstep (se 1 (by rfl) ⟨1335599, by rfl⟩ : syracuseStep 1780799 = 2671199) B2671199
theorem B4009031 : Blo 1780091 4009031 := bstep (se 1 (by rfl) ⟨3006773, by rfl⟩ : syracuseStep 4009031 = 6013547) B6013547
theorem B5074103 : Blo 1780091 5074103 := bstep (se 1 (by rfl) ⟨3805577, by rfl⟩ : syracuseStep 5074103 = 7611155) B7611155
theorem B3804347 : Blo 1780091 3804347 := bstep (se 1 (by rfl) ⟨2853260, by rfl⟩ : syracuseStep 3804347 = 5706521) B5706521
theorem B1781119 : Blo 1780091 1781119 := bstep (se 1 (by rfl) ⟨1335839, by rfl⟩ : syracuseStep 1781119 = 2671679) B2671679
theorem B1781147 : Blo 1780091 1781147 := bstep (se 1 (by rfl) ⟨1335860, by rfl⟩ : syracuseStep 1781147 = 2671721) B2671721
theorem B4009427 : Blo 1780091 4009427 := bstep (se 1 (by rfl) ⟨3007070, by rfl⟩ : syracuseStep 4009427 = 6014141) B6014141
theorem B1781215 : Blo 1780091 1781215 := bstep (se 1 (by rfl) ⟨1335911, by rfl⟩ : syracuseStep 1781215 = 2671823) B2671823
theorem B6417991 : Blo 1780091 6417991 := bstep (se 1 (by rfl) ⟨4813493, by rfl⟩ : syracuseStep 6417991 = 9626987) B9626987
theorem B9629255 : Blo 1780091 9629255 := bstep (se 1 (by rfl) ⟨7221941, by rfl⟩ : syracuseStep 9629255 = 14443883) B14443883
theorem B7605839 : Blo 1780091 7605839 := bstep (se 1 (by rfl) ⟨5704379, by rfl⟩ : syracuseStep 7605839 = 11408759) B11408759
theorem B1781351 : Blo 1780091 1781351 := bstep (se 1 (by rfl) ⟨1336013, by rfl⟩ : syracuseStep 1781351 = 2672027) B2672027
theorem B4009697 : Blo 1780091 4009697 := bstep (se 2 (by rfl) ⟨1503636, by rfl⟩ : syracuseStep 4009697 = 3007273) B3007273
theorem B125054711 : Blo 1780091 125054711 := bstep (se 1 (by rfl) ⟨93791033, by rfl⟩ : syracuseStep 125054711 = 187582067) B187582067
theorem B1781499 : Blo 1780091 1781499 := bstep (se 1 (by rfl) ⟨1336124, by rfl⟩ : syracuseStep 1781499 = 2672249) B2672249
theorem B1781567 : Blo 1780091 1781567 := bstep (se 1 (by rfl) ⟨1336175, by rfl⟩ : syracuseStep 1781567 = 2672351) B2672351
theorem B1806143 : Blo 1780091 1806143 := bstep (se 1 (by rfl) ⟨1354607, by rfl⟩ : syracuseStep 1806143 = 2709215) B2709215
theorem B1781631 : Blo 1780091 1781631 := bstep (se 1 (by rfl) ⟨1336223, by rfl⟩ : syracuseStep 1781631 = 2672447) B2672447
theorem B7221163 : Blo 1780091 7221163 := bstep (se 1 (by rfl) ⟨5415872, by rfl⟩ : syracuseStep 7221163 = 10831745) B10831745
theorem B158232527 : Blo 1780091 158232527 := bstep (se 1 (by rfl) ⟨118674395, by rfl⟩ : syracuseStep 158232527 = 237348791) B237348791
theorem B2002927 : Blo 1780091 2002927 := bstep (se 1 (by rfl) ⟨1502195, by rfl⟩ : syracuseStep 2002927 = 3004391) B3004391
theorem B1781743 : Blo 1780091 1781743 := bstep (se 1 (by rfl) ⟨1336307, by rfl⟩ : syracuseStep 1781743 = 2672615) B2672615
theorem B1781755 : Blo 1780091 1781755 := bstep (se 1 (by rfl) ⟨1336316, by rfl⟩ : syracuseStep 1781755 = 2672633) B2672633
theorem B1781823 : Blo 1780091 1781823 := bstep (se 1 (by rfl) ⟨1336367, by rfl⟩ : syracuseStep 1781823 = 2672735) B2672735
theorem B1781863 : Blo 1780091 1781863 := bstep (se 1 (by rfl) ⟨1336397, by rfl⟩ : syracuseStep 1781863 = 2672795) B2672795
theorem B2003071 : Blo 1780091 2003071 := bstep (se 1 (by rfl) ⟨1502303, by rfl⟩ : syracuseStep 2003071 = 3004607) B3004607
theorem B1781887 : Blo 1780091 1781887 := bstep (se 1 (by rfl) ⟨1336415, by rfl⟩ : syracuseStep 1781887 = 2672831) B2672831
theorem B1781915 : Blo 1780091 1781915 := bstep (se 1 (by rfl) ⟨1336436, by rfl⟩ : syracuseStep 1781915 = 2672873) B2672873
theorem B65024329 : Blo 1780091 65024329 := bstep (se 2 (by rfl) ⟨24384123, by rfl⟩ : syracuseStep 65024329 = 48768247) B48768247
theorem B3379553 : Blo 1780091 3379553 := bstep (se 2 (by rfl) ⟨1267332, by rfl⟩ : syracuseStep 3379553 = 2534665) B2534665
theorem B7606865 : Blo 1780091 7606865 := bstep (se 2 (by rfl) ⟨2852574, by rfl⟩ : syracuseStep 7606865 = 5705149) B5705149
theorem B6763115 : Blo 1780091 6763115 := bstep (se 1 (by rfl) ⟨5072336, by rfl⟩ : syracuseStep 6763115 = 10144673) B10144673
theorem B6009767 : Blo 1780091 6009767 := bstep (se 1 (by rfl) ⟨4507325, by rfl⟩ : syracuseStep 6009767 = 9014651) B9014651
theorem B9016595 : Blo 1780091 9016595 := bstep (se 1 (by rfl) ⟨6762446, by rfl⟩ : syracuseStep 9016595 = 13524893) B13524893
theorem B28898927 : Blo 1780091 28898927 := bstep (se 1 (by rfl) ⟨21674195, by rfl⟩ : syracuseStep 28898927 = 43348391) B43348391
theorem B66795131 : Blo 1780091 66795131 := bstep (se 1 (by rfl) ⟨50096348, by rfl⟩ : syracuseStep 66795131 = 100192697) B100192697
theorem B6764255 : Blo 1780091 6764255 := bstep (se 1 (by rfl) ⟨5073191, by rfl⟩ : syracuseStep 6764255 = 10146383) B10146383
theorem B8558399 : Blo 1780091 8558399 := bstep (se 1 (by rfl) ⟨6418799, by rfl⟩ : syracuseStep 8558399 = 12837599) B12837599
theorem B3004283 : Blo 1780091 3004283 := bstep (se 1 (by rfl) ⟨2253212, by rfl⟩ : syracuseStep 3004283 = 4506425) B4506425
theorem B3381239 : Blo 1780091 3381239 := bstep (se 1 (by rfl) ⟨2535929, by rfl⟩ : syracuseStep 3381239 = 5071859) B5071859
theorem B20289527 : Blo 1780091 20289527 := bstep (se 1 (by rfl) ⟨15217145, by rfl⟩ : syracuseStep 20289527 = 30434291) B30434291
theorem B3004553 : Blo 1780091 3004553 := bstep (se 2 (by rfl) ⟨1126707, by rfl⟩ : syracuseStep 3004553 = 2253415) B2253415
theorem B10139843 : Blo 1780091 10139843 := bstep (se 1 (by rfl) ⟨7604882, by rfl⟩ : syracuseStep 10139843 = 15209765) B15209765
theorem B30841211 : Blo 1780091 30841211 := bstep (se 1 (by rfl) ⟨23130908, by rfl⟩ : syracuseStep 30841211 = 46261817) B46261817
theorem B6765227 : Blo 1780091 6765227 := bstep (se 1 (by rfl) ⟨5073920, by rfl⟩ : syracuseStep 6765227 = 10147841) B10147841
theorem B3005255 : Blo 1780091 3005255 := bstep (se 1 (by rfl) ⟨2253941, by rfl⟩ : syracuseStep 3005255 = 4507883) B4507883
theorem B7519067 : Blo 1780091 7519067 := bstep (se 1 (by rfl) ⟨5639300, by rfl⟩ : syracuseStep 7519067 = 11278601) B11278601
theorem B10148773 : Blo 1780091 10148773 := bstep (se 4 (by rfl) ⟨951447, by rfl⟩ : syracuseStep 10148773 = 1902895) B1902895
theorem B13523921 : Blo 1780091 13523921 := bstep (se 2 (by rfl) ⟨5071470, by rfl⟩ : syracuseStep 13523921 = 10142941) B10142941
theorem B13900769 : Blo 1780091 13900769 := bstep (se 2 (by rfl) ⟨5212788, by rfl⟩ : syracuseStep 13900769 = 10425577) B10425577
theorem B3382393 : Blo 1780091 3382393 := bstep (se 2 (by rfl) ⟨1268397, by rfl⟩ : syracuseStep 3382393 = 2536795) B2536795
theorem B43326589 : Blo 1780091 43326589 := bstep (se 3 (by rfl) ⟨8123735, by rfl⟩ : syracuseStep 43326589 = 16247471) B16247471
theorem B10149047 : Blo 1780091 10149047 := bstep (se 1 (by rfl) ⟨7611785, by rfl⟩ : syracuseStep 10149047 = 15223571) B15223571
theorem B26025209 : Blo 1780091 26025209 := bstep (se 2 (by rfl) ⟨9759453, by rfl⟩ : syracuseStep 26025209 = 19518907) B19518907
theorem B115588417 : Blo 1780091 115588417 := bstep (se 2 (by rfl) ⟨43345656, by rfl⟩ : syracuseStep 115588417 = 86691313) B86691313
theorem B13704623 : Blo 1780091 13704623 := bstep (se 1 (by rfl) ⟨10278467, by rfl⟩ : syracuseStep 13704623 = 20556935) B20556935
theorem B6012413 : Blo 1780091 6012413 := bstep (se 3 (by rfl) ⟨1127327, by rfl⟩ : syracuseStep 6012413 = 2254655) B2254655
theorem B4005449 : Blo 1780091 4005449 := bstep (se 2 (by rfl) ⟨1502043, by rfl⟩ : syracuseStep 4005449 = 3004087) B3004087
theorem B5783147 : Blo 1780091 5783147 := bstep (se 1 (by rfl) ⟨4337360, by rfl⟩ : syracuseStep 5783147 = 8674721) B8674721
theorem B2670191 : Blo 1780091 2670191 := bstep (se 1 (by rfl) ⟨2002643, by rfl⟩ : syracuseStep 2670191 = 4005287) B4005287
theorem B7044737 : Blo 1780091 7044737 := bstep (se 2 (by rfl) ⟨2641776, by rfl⟩ : syracuseStep 7044737 = 5283553) B5283553
theorem B3006119 : Blo 1780091 3006119 := bstep (se 1 (by rfl) ⟨2254589, by rfl⟩ : syracuseStep 3006119 = 4509179) B4509179
theorem B2670311 : Blo 1780091 2670311 := bstep (se 1 (by rfl) ⟨2002733, by rfl⟩ : syracuseStep 2670311 = 4005467) B4005467
theorem B3383137 : Blo 1780091 3383137 := bstep (se 2 (by rfl) ⟨1268676, by rfl⟩ : syracuseStep 3383137 = 2537353) B2537353
theorem B93757301 : Blo 1780091 93757301 := bstep (se 5 (by rfl) ⟨4394873, by rfl⟩ : syracuseStep 93757301 = 8789747) B8789747
theorem B2670503 : Blo 1780091 2670503 := bstep (se 1 (by rfl) ⟨2002877, by rfl⟩ : syracuseStep 2670503 = 4005755) B4005755
theorem B11411401 : Blo 1780091 11411401 := bstep (se 2 (by rfl) ⟨4279275, by rfl⟩ : syracuseStep 11411401 = 8558551) B8558551
theorem B2670761 : Blo 1780091 2670761 := bstep (se 2 (by rfl) ⟨1001535, by rfl⟩ : syracuseStep 2670761 = 2003071) B2003071
theorem B2253035 : Blo 1780091 2253035 := bstep (se 1 (by rfl) ⟨1689776, by rfl⟩ : syracuseStep 2253035 = 3379553) B3379553
theorem B5071243 : Blo 1780091 5071243 := bstep (se 1 (by rfl) ⟨3803432, by rfl⟩ : syracuseStep 5071243 = 7606865) B7606865
theorem B9142739 : Blo 1780091 9142739 := bstep (se 1 (by rfl) ⟨6857054, by rfl⟩ : syracuseStep 9142739 = 13714109) B13714109
theorem B2671079 : Blo 1780091 2671079 := bstep (se 1 (by rfl) ⟨2003309, by rfl⟩ : syracuseStep 2671079 = 4006619) B4006619
theorem B4006511 : Blo 1780091 4006511 := bstep (se 1 (by rfl) ⟨3004883, by rfl⟩ : syracuseStep 4006511 = 6009767) B6009767
theorem B2109276875 : Blo 1780091 2109276875 := bstep (se 1 (by rfl) ⟨1581957656, by rfl⟩ : syracuseStep 2109276875 = 3163915313) B3163915313
theorem B2671355 : Blo 1780091 2671355 := bstep (se 1 (by rfl) ⟨2003516, by rfl⟩ : syracuseStep 2671355 = 4007033) B4007033
theorem B34694045 : Blo 1780091 34694045 := bstep (se 3 (by rfl) ⟨6505133, by rfl⟩ : syracuseStep 34694045 = 13010267) B13010267
theorem B73139111 : Blo 1780091 73139111 := bstep (se 1 (by rfl) ⟨54854333, by rfl⟩ : syracuseStep 73139111 = 109708667) B109708667
theorem B5702831 : Blo 1780091 5702831 := bstep (se 1 (by rfl) ⟨4277123, by rfl⟩ : syracuseStep 5702831 = 8554247) B8554247
theorem B2671799 : Blo 1780091 2671799 := bstep (se 1 (by rfl) ⟨2003849, by rfl⟩ : syracuseStep 2671799 = 4007699) B4007699
theorem B1901819 : Blo 1780091 1901819 := bstep (se 1 (by rfl) ⟨1426364, by rfl⟩ : syracuseStep 1901819 = 2852729) B2852729
theorem B2671943 : Blo 1780091 2671943 := bstep (se 1 (by rfl) ⟨2003957, by rfl⟩ : syracuseStep 2671943 = 4007915) B4007915
theorem B2254159 : Blo 1780091 2254159 := bstep (se 1 (by rfl) ⟨1690619, by rfl⟩ : syracuseStep 2254159 = 3381239) B3381239
theorem B13526351 : Blo 1780091 13526351 := bstep (se 1 (by rfl) ⟨10144763, by rfl⟩ : syracuseStep 13526351 = 20289527) B20289527
theorem B2672039 : Blo 1780091 2672039 := bstep (se 1 (by rfl) ⟨2004029, by rfl⟩ : syracuseStep 2672039 = 4008059) B4008059
theorem B6759895 : Blo 1780091 6759895 := bstep (se 1 (by rfl) ⟨5069921, by rfl⟩ : syracuseStep 6759895 = 10139843) B10139843
theorem B2672219 : Blo 1780091 2672219 := bstep (se 1 (by rfl) ⟨2004164, by rfl⟩ : syracuseStep 2672219 = 4008329) B4008329
theorem B178120349 : Blo 1780091 178120349 := bstep (se 3 (by rfl) ⟨33397565, by rfl⟩ : syracuseStep 178120349 = 66795131) B66795131
theorem B154117889 : Blo 1780091 154117889 := bstep (se 2 (by rfl) ⟨57794208, by rfl⟩ : syracuseStep 154117889 = 115588417) B115588417
theorem B18270031 : Blo 1780091 18270031 := bstep (se 1 (by rfl) ⟨13702523, by rfl⟩ : syracuseStep 18270031 = 27405047) B27405047
theorem B92555207 : Blo 1780091 92555207 := bstep (se 1 (by rfl) ⟨69416405, by rfl⟩ : syracuseStep 92555207 = 138832811) B138832811
theorem B9267179 : Blo 1780091 9267179 := bstep (se 1 (by rfl) ⟨6950384, by rfl⟩ : syracuseStep 9267179 = 13900769) B13900769
theorem B2672687 : Blo 1780091 2672687 := bstep (se 1 (by rfl) ⟨2004515, by rfl⟩ : syracuseStep 2672687 = 4009031) B4009031
theorem B9136415 : Blo 1780091 9136415 := bstep (se 1 (by rfl) ⟨6852311, by rfl⟩ : syracuseStep 9136415 = 13704623) B13704623
theorem B2672951 : Blo 1780091 2672951 := bstep (se 1 (by rfl) ⟨2004713, by rfl⟩ : syracuseStep 2672951 = 4009427) B4009427
theorem B4008275 : Blo 1780091 4008275 := bstep (se 1 (by rfl) ⟨3006206, by rfl⟩ : syracuseStep 4008275 = 6012413) B6012413
theorem B5704073 : Blo 1780091 5704073 := bstep (se 2 (by rfl) ⟨2139027, by rfl⟩ : syracuseStep 5704073 = 4278055) B4278055
theorem B1780127 : Blo 1780091 1780127 := bstep (se 1 (by rfl) ⟨1335095, by rfl⟩ : syracuseStep 1780127 = 2670191) B2670191
theorem B2673131 : Blo 1780091 2673131 := bstep (se 1 (by rfl) ⟨2004848, by rfl⟩ : syracuseStep 2673131 = 4009697) B4009697
theorem B1780207 : Blo 1780091 1780207 := bstep (se 1 (by rfl) ⟨1335155, by rfl⟩ : syracuseStep 1780207 = 2670311) B2670311
theorem B9628217 : Blo 1780091 9628217 := bstep (se 2 (by rfl) ⟨3610581, by rfl⟩ : syracuseStep 9628217 = 7221163) B7221163
theorem B15215201 : Blo 1780091 15215201 := bstep (se 2 (by rfl) ⟨5705700, by rfl⟩ : syracuseStep 15215201 = 11411401) B11411401
theorem B1780335 : Blo 1780091 1780335 := bstep (se 1 (by rfl) ⟨1335251, by rfl⟩ : syracuseStep 1780335 = 2670503) B2670503
theorem B1780551 : Blo 1780091 1780551 := bstep (se 1 (by rfl) ⟨1335413, by rfl⟩ : syracuseStep 1780551 = 2670827) B2670827
theorem B1780591 : Blo 1780091 1780591 := bstep (se 1 (by rfl) ⟨1335443, by rfl⟩ : syracuseStep 1780591 = 2670887) B2670887
theorem B4008815 : Blo 1780091 4008815 := bstep (se 1 (by rfl) ⟨3006611, by rfl⟩ : syracuseStep 4008815 = 6013223) B6013223
theorem B4508743 : Blo 1780091 4508743 := bstep (se 1 (by rfl) ⟨3381557, by rfl⟩ : syracuseStep 4508743 = 6763115) B6763115
theorem B86699105 : Blo 1780091 86699105 := bstep (se 2 (by rfl) ⟨32512164, by rfl⟩ : syracuseStep 86699105 = 65024329) B65024329
theorem B4009067 : Blo 1780091 4009067 := bstep (se 1 (by rfl) ⟨3006800, by rfl⟩ : syracuseStep 4009067 = 6013601) B6013601
theorem B10144925 : Blo 1780091 10144925 := bstep (se 3 (by rfl) ⟨1902173, by rfl⟩ : syracuseStep 10144925 = 3804347) B3804347
theorem B1781039 : Blo 1780091 1781039 := bstep (se 1 (by rfl) ⟨1335779, by rfl⟩ : syracuseStep 1781039 = 2671559) B2671559
theorem B6008147 : Blo 1780091 6008147 := bstep (se 1 (by rfl) ⟨4506110, by rfl⟩ : syracuseStep 6008147 = 9012221) B9012221
theorem B36547949 : Blo 1780091 36547949 := bstep (se 3 (by rfl) ⟨6852740, by rfl⟩ : syracuseStep 36547949 = 13705481) B13705481
theorem B4009337 : Blo 1780091 4009337 := bstep (se 2 (by rfl) ⟨1503501, by rfl⟩ : syracuseStep 4009337 = 3007003) B3007003
theorem B1781151 : Blo 1780091 1781151 := bstep (se 1 (by rfl) ⟨1335863, by rfl⟩ : syracuseStep 1781151 = 2671727) B2671727
theorem B1781279 : Blo 1780091 1781279 := bstep (se 1 (by rfl) ⟨1335959, by rfl⟩ : syracuseStep 1781279 = 2671919) B2671919
theorem B1781415 : Blo 1780091 1781415 := bstep (se 1 (by rfl) ⟨1336061, by rfl⟩ : syracuseStep 1781415 = 2672123) B2672123
theorem B1781439 : Blo 1780091 1781439 := bstep (se 1 (by rfl) ⟨1336079, by rfl⟩ : syracuseStep 1781439 = 2672159) B2672159
theorem B1781535 : Blo 1780091 1781535 := bstep (se 1 (by rfl) ⟨1336151, by rfl⟩ : syracuseStep 1781535 = 2672303) B2672303
theorem B4509503 : Blo 1780091 4509503 := bstep (se 1 (by rfl) ⟨3382127, by rfl⟩ : syracuseStep 4509503 = 6764255) B6764255
theorem B5074751 : Blo 1780091 5074751 := bstep (se 1 (by rfl) ⟨3806063, by rfl⟩ : syracuseStep 5074751 = 7612127) B7612127
theorem B6008687 : Blo 1780091 6008687 := bstep (se 1 (by rfl) ⟨4506515, by rfl⟩ : syracuseStep 6008687 = 9013031) B9013031
theorem B1781615 : Blo 1780091 1781615 := bstep (se 1 (by rfl) ⟨1336211, by rfl⟩ : syracuseStep 1781615 = 2672423) B2672423
theorem B5705599 : Blo 1780091 5705599 := bstep (se 1 (by rfl) ⟨4279199, by rfl⟩ : syracuseStep 5705599 = 8558399) B8558399
theorem B2002855 : Blo 1780091 2002855 := bstep (se 1 (by rfl) ⟨1502141, by rfl⟩ : syracuseStep 2002855 = 3004283) B3004283
theorem B2003035 : Blo 1780091 2003035 := bstep (se 1 (by rfl) ⟨1502276, by rfl⟩ : syracuseStep 2003035 = 3004553) B3004553
theorem B4509857 : Blo 1780091 4509857 := bstep (se 2 (by rfl) ⟨1691196, by rfl⟩ : syracuseStep 4509857 = 3382393) B3382393
theorem B1781983 : Blo 1780091 1781983 := bstep (se 1 (by rfl) ⟨1336487, by rfl⟩ : syracuseStep 1781983 = 2672975) B2672975
theorem B6009065 : Blo 1780091 6009065 := bstep (se 2 (by rfl) ⟨2253399, by rfl⟩ : syracuseStep 6009065 = 4506799) B4506799
theorem B1782015 : Blo 1780091 1782015 := bstep (se 1 (by rfl) ⟨1336511, by rfl⟩ : syracuseStep 1782015 = 2673023) B2673023
theorem B1782043 : Blo 1780091 1782043 := bstep (se 1 (by rfl) ⟨1336532, by rfl⟩ : syracuseStep 1782043 = 2673065) B2673065
theorem B6009119 : Blo 1780091 6009119 := bstep (se 1 (by rfl) ⟨4506839, by rfl⟩ : syracuseStep 6009119 = 9013679) B9013679
theorem B4510151 : Blo 1780091 4510151 := bstep (se 1 (by rfl) ⟨3382613, by rfl⟩ : syracuseStep 4510151 = 6765227) B6765227
theorem B7606781 : Blo 1780091 7606781 := bstep (se 3 (by rfl) ⟨1426271, by rfl⟩ : syracuseStep 7606781 = 2852543) B2852543
theorem B2003503 : Blo 1780091 2003503 := bstep (se 1 (by rfl) ⟨1502627, by rfl⟩ : syracuseStep 2003503 = 3005255) B3005255
theorem B9015947 : Blo 1780091 9015947 := bstep (se 1 (by rfl) ⟨6761960, by rfl⟩ : syracuseStep 9015947 = 13523921) B13523921
theorem B8557321 : Blo 1780091 8557321 := bstep (se 2 (by rfl) ⟨3208995, by rfl⟩ : syracuseStep 8557321 = 6417991) B6417991
theorem B6419503 : Blo 1780091 6419503 := bstep (se 1 (by rfl) ⟨4814627, by rfl⟩ : syracuseStep 6419503 = 9629255) B9629255
theorem B3855431 : Blo 1780091 3855431 := bstep (se 1 (by rfl) ⟨2891573, by rfl⟩ : syracuseStep 3855431 = 5783147) B5783147
theorem B2004079 : Blo 1780091 2004079 := bstep (se 1 (by rfl) ⟨1503059, by rfl⟩ : syracuseStep 2004079 = 3006119) B3006119
theorem B4510849 : Blo 1780091 4510849 := bstep (se 2 (by rfl) ⟨1691568, by rfl⟩ : syracuseStep 4510849 = 3383137) B3383137
theorem B13522463 : Blo 1780091 13522463 := bstep (se 1 (by rfl) ⟨10141847, by rfl⟩ : syracuseStep 13522463 = 20283695) B20283695
theorem B15218513 : Blo 1780091 15218513 := bstep (se 2 (by rfl) ⟨5706942, by rfl⟩ : syracuseStep 15218513 = 11413885) B11413885
theorem B19265525 : Blo 1780091 19265525 := bstep (se 5 (by rfl) ⟨903071, by rfl⟩ : syracuseStep 19265525 = 1806143) B1806143
theorem B6011063 : Blo 1780091 6011063 := bstep (se 1 (by rfl) ⟨4508297, by rfl⟩ : syracuseStep 6011063 = 9016595) B9016595
theorem B3660059 : Blo 1780091 3660059 := bstep (se 1 (by rfl) ⟨2745044, by rfl⟩ : syracuseStep 3660059 = 5490089) B5490089
theorem B19265951 : Blo 1780091 19265951 := bstep (se 1 (by rfl) ⟨14449463, by rfl⟩ : syracuseStep 19265951 = 28898927) B28898927
theorem B13531697 : Blo 1780091 13531697 := bstep (se 2 (by rfl) ⟨5074386, by rfl⟩ : syracuseStep 13531697 = 10148773) B10148773
theorem B75143861 : Blo 1780091 75143861 := bstep (se 5 (by rfl) ⟨3522368, by rfl⟩ : syracuseStep 75143861 = 7044737) B7044737
theorem B11410247 : Blo 1780091 11410247 := bstep (se 1 (by rfl) ⟨8557685, by rfl⟩ : syracuseStep 11410247 = 17115371) B17115371
theorem B57768785 : Blo 1780091 57768785 := bstep (se 2 (by rfl) ⟨21663294, by rfl⟩ : syracuseStep 57768785 = 43326589) B43326589
theorem B20282237 : Blo 1780091 20282237 := bstep (se 3 (by rfl) ⟨3802919, by rfl⟩ : syracuseStep 20282237 = 7605839) B7605839
theorem B20560807 : Blo 1780091 20560807 := bstep (se 1 (by rfl) ⟨15420605, by rfl⟩ : syracuseStep 20560807 = 30841211) B30841211
theorem B5069945 : Blo 1780091 5069945 := bstep (se 2 (by rfl) ⟨1901229, by rfl⟩ : syracuseStep 5069945 = 3802459) B3802459
theorem B5012711 : Blo 1780091 5012711 := bstep (se 1 (by rfl) ⟨3759533, by rfl⟩ : syracuseStep 5012711 = 7519067) B7519067
theorem B3382735 : Blo 1780091 3382735 := bstep (se 1 (by rfl) ⟨2537051, by rfl⟩ : syracuseStep 3382735 = 5074103) B5074103
theorem B6766031 : Blo 1780091 6766031 := bstep (se 1 (by rfl) ⟨5074523, by rfl⟩ : syracuseStep 6766031 = 10149047) B10149047
theorem B17350139 : Blo 1780091 17350139 := bstep (se 1 (by rfl) ⟨13012604, by rfl⟩ : syracuseStep 17350139 = 26025209) B26025209
theorem B2670299 : Blo 1780091 2670299 := bstep (se 1 (by rfl) ⟨2002724, by rfl⟩ : syracuseStep 2670299 = 4005449) B4005449
theorem B9625321 : Blo 1780091 9625321 := bstep (se 2 (by rfl) ⟨3609495, by rfl⟩ : syracuseStep 9625321 = 7218991) B7218991
theorem B83369807 : Blo 1780091 83369807 := bstep (se 1 (by rfl) ⟨62527355, by rfl⟩ : syracuseStep 83369807 = 125054711) B125054711
theorem B62504867 : Blo 1780091 62504867 := bstep (se 1 (by rfl) ⟨46878650, by rfl⟩ : syracuseStep 62504867 = 93757301) B93757301
theorem B105488351 : Blo 1780091 105488351 := bstep (se 1 (by rfl) ⟨79116263, by rfl⟩ : syracuseStep 105488351 = 158232527) B158232527
theorem B2670569 : Blo 1780091 2670569 := bstep (se 2 (by rfl) ⟨1001463, by rfl⟩ : syracuseStep 2670569 = 2002927) B2002927
theorem B3006571 : Blo 1780091 3006571 := bstep (se 1 (by rfl) ⟨2254928, by rfl⟩ : syracuseStep 3006571 = 4509857) B4509857
theorem B2670713 : Blo 1780091 2670713 := bstep (se 2 (by rfl) ⟨1001517, by rfl⟩ : syracuseStep 2670713 = 2003035) B2003035
theorem B4006043 : Blo 1780091 4006043 := bstep (se 1 (by rfl) ⟨3004532, by rfl⟩ : syracuseStep 4006043 = 6009065) B6009065
theorem B4006079 : Blo 1780091 4006079 := bstep (se 1 (by rfl) ⟨3004559, by rfl⟩ : syracuseStep 4006079 = 6009119) B6009119
theorem B3006767 : Blo 1780091 3006767 := bstep (se 1 (by rfl) ⟨2255075, by rfl⟩ : syracuseStep 3006767 = 4510151) B4510151
theorem B6095159 : Blo 1780091 6095159 := bstep (se 1 (by rfl) ⟨4571369, by rfl⟩ : syracuseStep 6095159 = 9142739) B9142739
theorem B5071187 : Blo 1780091 5071187 := bstep (se 1 (by rfl) ⟨3803390, by rfl⟩ : syracuseStep 5071187 = 7606781) B7606781
theorem B2671007 : Blo 1780091 2671007 := bstep (se 1 (by rfl) ⟨2003255, by rfl⟩ : syracuseStep 2671007 = 4006511) B4006511
theorem B48759407 : Blo 1780091 48759407 := bstep (se 1 (by rfl) ⟨36569555, by rfl⟩ : syracuseStep 48759407 = 73139111) B73139111
theorem B5071517 : Blo 1780091 5071517 := bstep (se 3 (by rfl) ⟨950909, by rfl⟩ : syracuseStep 5071517 = 1901819) B1901819
theorem B2671337 : Blo 1780091 2671337 := bstep (se 2 (by rfl) ⟨1001751, by rfl⟩ : syracuseStep 2671337 = 2003503) B2003503
theorem B24363773 : Blo 1780091 24363773 := bstep (se 3 (by rfl) ⟨4568207, by rfl⟩ : syracuseStep 24363773 = 9136415) B9136415
theorem B3801887 : Blo 1780091 3801887 := bstep (se 1 (by rfl) ⟨2851415, by rfl⟩ : syracuseStep 3801887 = 5702831) B5702831
theorem B102745259 : Blo 1780091 102745259 := bstep (se 1 (by rfl) ⟨77058944, by rfl⟩ : syracuseStep 102745259 = 154117889) B154117889
theorem B61703471 : Blo 1780091 61703471 := bstep (se 1 (by rfl) ⟨46277603, by rfl⟩ : syracuseStep 61703471 = 92555207) B92555207
theorem B4007375 : Blo 1780091 4007375 := bstep (se 1 (by rfl) ⟨3005531, by rfl⟩ : syracuseStep 4007375 = 6011063) B6011063
theorem B2672105 : Blo 1780091 2672105 := bstep (se 2 (by rfl) ⟨1002039, by rfl⟩ : syracuseStep 2672105 = 2004079) B2004079
theorem B6014465 : Blo 1780091 6014465 := bstep (se 2 (by rfl) ⟨2255424, by rfl⟩ : syracuseStep 6014465 = 4510849) B4510849
theorem B2672183 : Blo 1780091 2672183 := bstep (se 1 (by rfl) ⟨2004137, by rfl⟩ : syracuseStep 2672183 = 4008275) B4008275
theorem B3802715 : Blo 1780091 3802715 := bstep (se 1 (by rfl) ⟨2852036, by rfl⟩ : syracuseStep 3802715 = 5704073) B5704073
theorem B9021131 : Blo 1780091 9021131 := bstep (se 1 (by rfl) ⟨6765848, by rfl⟩ : syracuseStep 9021131 = 13531697) B13531697
theorem B10143467 : Blo 1780091 10143467 := bstep (se 1 (by rfl) ⟨7607600, by rfl⟩ : syracuseStep 10143467 = 15215201) B15215201
theorem B50095907 : Blo 1780091 50095907 := bstep (se 1 (by rfl) ⟨37571930, by rfl⟩ : syracuseStep 50095907 = 75143861) B75143861
theorem B38512523 : Blo 1780091 38512523 := bstep (se 1 (by rfl) ⟨28884392, by rfl⟩ : syracuseStep 38512523 = 57768785) B57768785
theorem B2672543 : Blo 1780091 2672543 := bstep (se 1 (by rfl) ⟨2004407, by rfl⟩ : syracuseStep 2672543 = 4008815) B4008815
theorem B9013193 : Blo 1780091 9013193 := bstep (se 2 (by rfl) ⟨3379947, by rfl⟩ : syracuseStep 9013193 = 6759895) B6759895
theorem B2672711 : Blo 1780091 2672711 := bstep (se 1 (by rfl) ⟨2004533, by rfl⟩ : syracuseStep 2672711 = 4009067) B4009067
theorem B24365299 : Blo 1780091 24365299 := bstep (se 1 (by rfl) ⟨18273974, by rfl⟩ : syracuseStep 24365299 = 36547949) B36547949
theorem B2672891 : Blo 1780091 2672891 := bstep (se 1 (by rfl) ⟨2004668, by rfl⟩ : syracuseStep 2672891 = 4009337) B4009337
theorem B1780199 : Blo 1780091 1780199 := bstep (se 1 (by rfl) ⟨1335149, by rfl⟩ : syracuseStep 1780199 = 2670299) B2670299
theorem B1780379 : Blo 1780091 1780379 := bstep (se 1 (by rfl) ⟨1335284, by rfl⟩ : syracuseStep 1780379 = 2670569) B2670569
theorem B1780507 : Blo 1780091 1780507 := bstep (se 1 (by rfl) ⟨1335380, by rfl⟩ : syracuseStep 1780507 = 2670761) B2670761
theorem B34237349 : Blo 1780091 34237349 := bstep (se 4 (by rfl) ⟨3209751, by rfl⟩ : syracuseStep 34237349 = 6419503) B6419503
theorem B1780719 : Blo 1780091 1780719 := bstep (se 1 (by rfl) ⟨1335539, by rfl⟩ : syracuseStep 1780719 = 2671079) B2671079
theorem B1406184583 : Blo 1780091 1406184583 := bstep (se 1 (by rfl) ⟨1054638437, by rfl⟩ : syracuseStep 1406184583 = 2109276875) B2109276875
theorem B1780903 : Blo 1780091 1780903 := bstep (se 1 (by rfl) ⟨1335677, by rfl⟩ : syracuseStep 1780903 = 2671355) B2671355
theorem B6761657 : Blo 1780091 6761657 := bstep (se 2 (by rfl) ⟨2535621, by rfl⟩ : syracuseStep 6761657 = 5071243) B5071243
theorem B23129363 : Blo 1780091 23129363 := bstep (se 1 (by rfl) ⟨17347022, by rfl⟩ : syracuseStep 23129363 = 34694045) B34694045
theorem B6008093 : Blo 1780091 6008093 := bstep (se 3 (by rfl) ⟨1126517, by rfl⟩ : syracuseStep 6008093 = 2253035) B2253035
theorem B1781199 : Blo 1780091 1781199 := bstep (se 1 (by rfl) ⟨1335899, by rfl⟩ : syracuseStep 1781199 = 2671799) B2671799
theorem B1781295 : Blo 1780091 1781295 := bstep (se 1 (by rfl) ⟨1335971, by rfl⟩ : syracuseStep 1781295 = 2671943) B2671943
theorem B1781359 : Blo 1780091 1781359 := bstep (se 1 (by rfl) ⟨1336019, by rfl⟩ : syracuseStep 1781359 = 2672039) B2672039
theorem B9014975 : Blo 1780091 9014975 := bstep (se 1 (by rfl) ⟨6761231, by rfl⟩ : syracuseStep 9014975 = 13522463) B13522463
theorem B1781479 : Blo 1780091 1781479 := bstep (se 1 (by rfl) ⟨1336109, by rfl⟩ : syracuseStep 1781479 = 2672219) B2672219
theorem B118746899 : Blo 1780091 118746899 := bstep (se 1 (by rfl) ⟨89060174, by rfl⟩ : syracuseStep 118746899 = 178120349) B178120349
theorem B10145675 : Blo 1780091 10145675 := bstep (se 1 (by rfl) ⟨7609256, by rfl⟩ : syracuseStep 10145675 = 15218513) B15218513
theorem B1781791 : Blo 1780091 1781791 := bstep (se 1 (by rfl) ⟨1336343, by rfl⟩ : syracuseStep 1781791 = 2672687) B2672687
theorem B1781967 : Blo 1780091 1781967 := bstep (se 1 (by rfl) ⟨1336475, by rfl⟩ : syracuseStep 1781967 = 2672951) B2672951
theorem B1782087 : Blo 1780091 1782087 := bstep (se 1 (by rfl) ⟨1336565, by rfl⟩ : syracuseStep 1782087 = 2673131) B2673131
theorem B6418811 : Blo 1780091 6418811 := bstep (se 1 (by rfl) ⟨4814108, by rfl⟩ : syracuseStep 6418811 = 9628217) B9628217
theorem B7606831 : Blo 1780091 7606831 := bstep (se 1 (by rfl) ⟨5705123, by rfl⟩ : syracuseStep 7606831 = 11410247) B11410247
theorem B13521491 : Blo 1780091 13521491 := bstep (se 1 (by rfl) ⟨10141118, by rfl⟩ : syracuseStep 13521491 = 20282237) B20282237
theorem B4510313 : Blo 1780091 4510313 := bstep (se 2 (by rfl) ⟨1691367, by rfl⟩ : syracuseStep 4510313 = 3382735) B3382735
theorem B57799403 : Blo 1780091 57799403 := bstep (se 1 (by rfl) ⟨43349552, by rfl⟩ : syracuseStep 57799403 = 86699105) B86699105
theorem B3379963 : Blo 1780091 3379963 := bstep (se 1 (by rfl) ⟨2534972, by rfl⟩ : syracuseStep 3379963 = 5069945) B5069945
theorem B6763283 : Blo 1780091 6763283 := bstep (se 1 (by rfl) ⟨5072462, by rfl⟩ : syracuseStep 6763283 = 10144925) B10144925
theorem B4510687 : Blo 1780091 4510687 := bstep (se 1 (by rfl) ⟨3383015, by rfl⟩ : syracuseStep 4510687 = 6766031) B6766031
theorem B12833761 : Blo 1780091 12833761 := bstep (se 2 (by rfl) ⟨4812660, by rfl⟩ : syracuseStep 12833761 = 9625321) B9625321
theorem B24360041 : Blo 1780091 24360041 := bstep (se 2 (by rfl) ⟨9135015, by rfl⟩ : syracuseStep 24360041 = 18270031) B18270031
theorem B98849909 : Blo 1780091 98849909 := bstep (se 5 (by rfl) ⟨4633589, by rfl⟩ : syracuseStep 98849909 = 9267179) B9267179
theorem B7607465 : Blo 1780091 7607465 := bstep (se 2 (by rfl) ⟨2852799, by rfl⟩ : syracuseStep 7607465 = 5705599) B5705599
theorem B55579871 : Blo 1780091 55579871 := bstep (se 1 (by rfl) ⟨41684903, by rfl⟩ : syracuseStep 55579871 = 83369807) B83369807
theorem B41669911 : Blo 1780091 41669911 := bstep (se 1 (by rfl) ⟨31252433, by rfl⟩ : syracuseStep 41669911 = 62504867) B62504867
theorem B70325567 : Blo 1780091 70325567 := bstep (se 1 (by rfl) ⟨52744175, by rfl⟩ : syracuseStep 70325567 = 105488351) B105488351
theorem B6010631 : Blo 1780091 6010631 := bstep (se 1 (by rfl) ⟨4507973, by rfl⟩ : syracuseStep 6010631 = 9015947) B9015947
theorem B2570287 : Blo 1780091 2570287 := bstep (se 1 (by rfl) ⟨1927715, by rfl⟩ : syracuseStep 2570287 = 3855431) B3855431
theorem B9017567 : Blo 1780091 9017567 := bstep (se 1 (by rfl) ⟨6763175, by rfl⟩ : syracuseStep 9017567 = 13526351) B13526351
theorem B11409761 : Blo 1780091 11409761 := bstep (se 2 (by rfl) ⟨4278660, by rfl⟩ : syracuseStep 11409761 = 8557321) B8557321
theorem B12843683 : Blo 1780091 12843683 := bstep (se 1 (by rfl) ⟨9632762, by rfl⟩ : syracuseStep 12843683 = 19265525) B19265525
theorem B6011657 : Blo 1780091 6011657 := bstep (se 2 (by rfl) ⟨2254371, by rfl⟩ : syracuseStep 6011657 = 4508743) B4508743
theorem B2440039 : Blo 1780091 2440039 := bstep (se 1 (by rfl) ⟨1830029, by rfl⟩ : syracuseStep 2440039 = 3660059) B3660059
theorem B12843967 : Blo 1780091 12843967 := bstep (se 1 (by rfl) ⟨9632975, by rfl⟩ : syracuseStep 12843967 = 19265951) B19265951
theorem B3005545 : Blo 1780091 3005545 := bstep (se 2 (by rfl) ⟨1127079, by rfl⟩ : syracuseStep 3005545 = 2254159) B2254159
theorem B3341807 : Blo 1780091 3341807 := bstep (se 1 (by rfl) ⟨2506355, by rfl⟩ : syracuseStep 3341807 = 5012711) B5012711
theorem B13532669 : Blo 1780091 13532669 := bstep (se 3 (by rfl) ⟨2537375, by rfl⟩ : syracuseStep 13532669 = 5074751) B5074751
theorem B109657637 : Blo 1780091 109657637 := bstep (se 4 (by rfl) ⟨10280403, by rfl⟩ : syracuseStep 109657637 = 20560807) B20560807
theorem B4005431 : Blo 1780091 4005431 := bstep (se 1 (by rfl) ⟨3004073, by rfl⟩ : syracuseStep 4005431 = 6008147) B6008147
theorem B11566759 : Blo 1780091 11566759 := bstep (se 1 (by rfl) ⟨8675069, by rfl⟩ : syracuseStep 11566759 = 17350139) B17350139
theorem B3006335 : Blo 1780091 3006335 := bstep (se 1 (by rfl) ⟨2254751, by rfl⟩ : syracuseStep 3006335 = 4509503) B4509503
theorem B2670473 : Blo 1780091 2670473 := bstep (se 2 (by rfl) ⟨1001427, by rfl⟩ : syracuseStep 2670473 = 2002855) B2002855
theorem B4005791 : Blo 1780091 4005791 := bstep (se 1 (by rfl) ⟨3004343, by rfl⟩ : syracuseStep 4005791 = 6008687) B6008687
theorem B2670695 : Blo 1780091 2670695 := bstep (se 1 (by rfl) ⟨2003021, by rfl⟩ : syracuseStep 2670695 = 4006043) B4006043
theorem B2670719 : Blo 1780091 2670719 := bstep (se 1 (by rfl) ⟨2003039, by rfl⟩ : syracuseStep 2670719 = 4006079) B4006079
theorem B4063439 : Blo 1780091 4063439 := bstep (se 1 (by rfl) ⟨3047579, by rfl⟩ : syracuseStep 4063439 = 6095159) B6095159
theorem B3006875 : Blo 1780091 3006875 := bstep (se 1 (by rfl) ⟨2255156, by rfl⟩ : syracuseStep 3006875 = 4510313) B4510313
theorem B32506271 : Blo 1780091 32506271 := bstep (se 1 (by rfl) ⟨24379703, by rfl⟩ : syracuseStep 32506271 = 48759407) B48759407
theorem B10142441 : Blo 1780091 10142441 := bstep (se 2 (by rfl) ⟨3803415, by rfl⟩ : syracuseStep 10142441 = 7606831) B7606831
theorem B5071643 : Blo 1780091 5071643 := bstep (se 1 (by rfl) ⟨3803732, by rfl⟩ : syracuseStep 5071643 = 7607465) B7607465
theorem B37053247 : Blo 1780091 37053247 := bstep (se 1 (by rfl) ⟨27789935, by rfl⟩ : syracuseStep 37053247 = 55579871) B55579871
theorem B46883711 : Blo 1780091 46883711 := bstep (se 1 (by rfl) ⟨35162783, by rfl⟩ : syracuseStep 46883711 = 70325567) B70325567
theorem B2671583 : Blo 1780091 2671583 := bstep (se 1 (by rfl) ⟨2003687, by rfl⟩ : syracuseStep 2671583 = 4007375) B4007375
theorem B4506617 : Blo 1780091 4506617 := bstep (se 2 (by rfl) ⟨1689981, by rfl⟩ : syracuseStep 4506617 = 3379963) B3379963
theorem B6014087 : Blo 1780091 6014087 := bstep (se 1 (by rfl) ⟨4510565, by rfl⟩ : syracuseStep 6014087 = 9021131) B9021131
theorem B3253385 : Blo 1780091 3253385 := bstep (se 2 (by rfl) ⟨1220019, by rfl⟩ : syracuseStep 3253385 = 2440039) B2440039
theorem B4007087 : Blo 1780091 4007087 := bstep (se 1 (by rfl) ⟨3005315, by rfl⟩ : syracuseStep 4007087 = 6010631) B6010631
theorem B25675015 : Blo 1780091 25675015 := bstep (se 1 (by rfl) ⟨19256261, by rfl⟩ : syracuseStep 25675015 = 38512523) B38512523
theorem B6014249 : Blo 1780091 6014249 := bstep (se 2 (by rfl) ⟨2255343, by rfl⟩ : syracuseStep 6014249 = 4510687) B4510687
theorem B4007393 : Blo 1780091 4007393 := bstep (se 2 (by rfl) ⟨1502772, by rfl⟩ : syracuseStep 4007393 = 3005545) B3005545
theorem B1874912777 : Blo 1780091 1874912777 := bstep (se 2 (by rfl) ⟨703092291, by rfl⟩ : syracuseStep 1874912777 = 1406184583) B1406184583
theorem B55559881 : Blo 1780091 55559881 := bstep (se 2 (by rfl) ⟨20834955, by rfl⟩ : syracuseStep 55559881 = 41669911) B41669911
theorem B8562455 : Blo 1780091 8562455 := bstep (se 1 (by rfl) ⟨6421841, by rfl⟩ : syracuseStep 8562455 = 12843683) B12843683
theorem B4007771 : Blo 1780091 4007771 := bstep (se 1 (by rfl) ⟨3005828, by rfl⟩ : syracuseStep 4007771 = 6011657) B6011657
theorem B22824899 : Blo 1780091 22824899 := bstep (se 1 (by rfl) ⟨17118674, by rfl⟩ : syracuseStep 22824899 = 34237349) B34237349
theorem B4507771 : Blo 1780091 4507771 := bstep (se 1 (by rfl) ⟨3380828, by rfl⟩ : syracuseStep 4507771 = 6761657) B6761657
theorem B15419575 : Blo 1780091 15419575 := bstep (se 1 (by rfl) ⟨11564681, by rfl⟩ : syracuseStep 15419575 = 23129363) B23129363
theorem B9021779 : Blo 1780091 9021779 := bstep (se 1 (by rfl) ⟨6766334, by rfl⟩ : syracuseStep 9021779 = 13532669) B13532669
theorem B1780315 : Blo 1780091 1780315 := bstep (se 1 (by rfl) ⟨1335236, by rfl⟩ : syracuseStep 1780315 = 2670473) B2670473
theorem B3427049 : Blo 1780091 3427049 := bstep (se 2 (by rfl) ⟨1285143, by rfl⟩ : syracuseStep 3427049 = 2570287) B2570287
theorem B1780475 : Blo 1780091 1780475 := bstep (se 1 (by rfl) ⟨1335356, by rfl⟩ : syracuseStep 1780475 = 2670713) B2670713
theorem B4008761 : Blo 1780091 4008761 := bstep (se 2 (by rfl) ⟨1503285, by rfl⟩ : syracuseStep 4008761 = 3006571) B3006571
theorem B1780671 : Blo 1780091 1780671 := bstep (se 1 (by rfl) ⟨1335503, by rfl⟩ : syracuseStep 1780671 = 2671007) B2671007
theorem B9014327 : Blo 1780091 9014327 := bstep (se 1 (by rfl) ⟨6760745, by rfl⟩ : syracuseStep 9014327 = 13521491) B13521491
theorem B1780891 : Blo 1780091 1780891 := bstep (se 1 (by rfl) ⟨1335668, by rfl⟩ : syracuseStep 1780891 = 2671337) B2671337
theorem B4508855 : Blo 1780091 4508855 := bstep (se 1 (by rfl) ⟨3381641, by rfl⟩ : syracuseStep 4508855 = 6763283) B6763283
theorem B2534591 : Blo 1780091 2534591 := bstep (se 1 (by rfl) ⟨1900943, by rfl⟩ : syracuseStep 2534591 = 3801887) B3801887
theorem B16240027 : Blo 1780091 16240027 := bstep (se 1 (by rfl) ⟨12180020, by rfl⟩ : syracuseStep 16240027 = 24360041) B24360041
theorem B68496839 : Blo 1780091 68496839 := bstep (se 1 (by rfl) ⟨51372629, by rfl⟩ : syracuseStep 68496839 = 102745259) B102745259
theorem B41135647 : Blo 1780091 41135647 := bstep (se 1 (by rfl) ⟨30851735, by rfl⟩ : syracuseStep 41135647 = 61703471) B61703471
theorem B1781403 : Blo 1780091 1781403 := bstep (se 1 (by rfl) ⟨1336052, by rfl⟩ : syracuseStep 1781403 = 2672105) B2672105
theorem B17116829 : Blo 1780091 17116829 := bstep (se 3 (by rfl) ⟨3209405, by rfl⟩ : syracuseStep 17116829 = 6418811) B6418811
theorem B4009643 : Blo 1780091 4009643 := bstep (se 1 (by rfl) ⟨3007232, by rfl⟩ : syracuseStep 4009643 = 6014465) B6014465
theorem B1781455 : Blo 1780091 1781455 := bstep (se 1 (by rfl) ⟨1336091, by rfl⟩ : syracuseStep 1781455 = 2672183) B2672183
theorem B2535143 : Blo 1780091 2535143 := bstep (se 1 (by rfl) ⟨1901357, by rfl⟩ : syracuseStep 2535143 = 3802715) B3802715
theorem B6762311 : Blo 1780091 6762311 := bstep (se 1 (by rfl) ⟨5071733, by rfl⟩ : syracuseStep 6762311 = 10143467) B10143467
theorem B17125289 : Blo 1780091 17125289 := bstep (se 2 (by rfl) ⟨6421983, by rfl⟩ : syracuseStep 17125289 = 12843967) B12843967
theorem B1781695 : Blo 1780091 1781695 := bstep (se 1 (by rfl) ⟨1336271, by rfl⟩ : syracuseStep 1781695 = 2672543) B2672543
theorem B6008795 : Blo 1780091 6008795 := bstep (se 1 (by rfl) ⟨4506596, by rfl⟩ : syracuseStep 6008795 = 9013193) B9013193
theorem B1781807 : Blo 1780091 1781807 := bstep (se 1 (by rfl) ⟨1336355, by rfl⟩ : syracuseStep 1781807 = 2672711) B2672711
theorem B1781927 : Blo 1780091 1781927 := bstep (se 1 (by rfl) ⟨1336445, by rfl⟩ : syracuseStep 1781927 = 2672891) B2672891
theorem B7606507 : Blo 1780091 7606507 := bstep (se 1 (by rfl) ⟨5704880, by rfl⟩ : syracuseStep 7606507 = 11409761) B11409761
theorem B15422345 : Blo 1780091 15422345 := bstep (se 2 (by rfl) ⟨5783379, by rfl⟩ : syracuseStep 15422345 = 11566759) B11566759
theorem B6009983 : Blo 1780091 6009983 := bstep (se 1 (by rfl) ⟨4507487, by rfl⟩ : syracuseStep 6009983 = 9014975) B9014975
theorem B79164599 : Blo 1780091 79164599 := bstep (se 1 (by rfl) ⟨59373449, by rfl⟩ : syracuseStep 79164599 = 118746899) B118746899
theorem B2004223 : Blo 1780091 2004223 := bstep (se 1 (by rfl) ⟨1503167, by rfl⟩ : syracuseStep 2004223 = 3006335) B3006335
theorem B6763783 : Blo 1780091 6763783 := bstep (se 1 (by rfl) ⟨5072837, by rfl⟩ : syracuseStep 6763783 = 10145675) B10145675
theorem B2004511 : Blo 1780091 2004511 := bstep (se 1 (by rfl) ⟨1503383, by rfl⟩ : syracuseStep 2004511 = 3006767) B3006767
theorem B3380791 : Blo 1780091 3380791 := bstep (se 1 (by rfl) ⟨2535593, by rfl⟩ : syracuseStep 3380791 = 5071187) B5071187
theorem B263599757 : Blo 1780091 263599757 := bstep (se 3 (by rfl) ⟨49424954, by rfl⟩ : syracuseStep 263599757 = 98849909) B98849909
theorem B32487065 : Blo 1780091 32487065 := bstep (se 2 (by rfl) ⟨12182649, by rfl⟩ : syracuseStep 32487065 = 24365299) B24365299
theorem B3381011 : Blo 1780091 3381011 := bstep (se 1 (by rfl) ⟨2535758, by rfl⟩ : syracuseStep 3381011 = 5071517) B5071517
theorem B38532935 : Blo 1780091 38532935 := bstep (se 1 (by rfl) ⟨28899701, by rfl⟩ : syracuseStep 38532935 = 57799403) B57799403
theorem B16242515 : Blo 1780091 16242515 := bstep (se 1 (by rfl) ⟨12181886, by rfl⟩ : syracuseStep 16242515 = 24363773) B24363773
theorem B33397271 : Blo 1780091 33397271 := bstep (se 1 (by rfl) ⟨25047953, by rfl⟩ : syracuseStep 33397271 = 50095907) B50095907
theorem B17111681 : Blo 1780091 17111681 := bstep (se 2 (by rfl) ⟨6416880, by rfl⟩ : syracuseStep 17111681 = 12833761) B12833761
theorem B6011711 : Blo 1780091 6011711 := bstep (se 1 (by rfl) ⟨4508783, by rfl⟩ : syracuseStep 6011711 = 9017567) B9017567
theorem B4005395 : Blo 1780091 4005395 := bstep (se 1 (by rfl) ⟨3004046, by rfl⟩ : syracuseStep 4005395 = 6008093) B6008093
theorem B2227871 : Blo 1780091 2227871 := bstep (se 1 (by rfl) ⟨1670903, by rfl⟩ : syracuseStep 2227871 = 3341807) B3341807
theorem B73105091 : Blo 1780091 73105091 := bstep (se 1 (by rfl) ⟨54828818, by rfl⟩ : syracuseStep 73105091 = 109657637) B109657637
theorem B2670287 : Blo 1780091 2670287 := bstep (se 1 (by rfl) ⟨2002715, by rfl⟩ : syracuseStep 2670287 = 4005431) B4005431
theorem B2670527 : Blo 1780091 2670527 := bstep (se 1 (by rfl) ⟨2002895, by rfl⟩ : syracuseStep 2670527 = 4005791) B4005791
theorem B10142009 : Blo 1780091 10142009 := bstep (se 2 (by rfl) ⟨3803253, by rfl⟩ : syracuseStep 10142009 = 7606507) B7606507
theorem B8675693 : Blo 1780091 8675693 := bstep (se 3 (by rfl) ⟨1626692, by rfl⟩ : syracuseStep 8675693 = 3253385) B3253385
theorem B6758909 : Blo 1780091 6758909 := bstep (se 3 (by rfl) ⟨1267295, by rfl⟩ : syracuseStep 6758909 = 2534591) B2534591
theorem B10281563 : Blo 1780091 10281563 := bstep (se 1 (by rfl) ⟨7711172, by rfl⟩ : syracuseStep 10281563 = 15422345) B15422345
theorem B4006655 : Blo 1780091 4006655 := bstep (se 1 (by rfl) ⟨3004991, by rfl⟩ : syracuseStep 4006655 = 6009983) B6009983
theorem B2671391 : Blo 1780091 2671391 := bstep (se 1 (by rfl) ⟨2003543, by rfl⟩ : syracuseStep 2671391 = 4007087) B4007087
theorem B2671595 : Blo 1780091 2671595 := bstep (se 1 (by rfl) ⟨2003696, by rfl⟩ : syracuseStep 2671595 = 4007393) B4007393
theorem B2254007 : Blo 1780091 2254007 := bstep (se 1 (by rfl) ⟨1690505, by rfl⟩ : syracuseStep 2254007 = 3381011) B3381011
theorem B2671847 : Blo 1780091 2671847 := bstep (se 1 (by rfl) ⟨2003885, by rfl⟩ : syracuseStep 2671847 = 4007771) B4007771
theorem B6014519 : Blo 1780091 6014519 := bstep (se 1 (by rfl) ⟨4510889, by rfl⟩ : syracuseStep 6014519 = 9021779) B9021779
theorem B2672297 : Blo 1780091 2672297 := bstep (se 2 (by rfl) ⟨1002111, by rfl⟩ : syracuseStep 2672297 = 2004223) B2004223
theorem B5940989 : Blo 1780091 5940989 := bstep (se 3 (by rfl) ⟨1113935, by rfl⟩ : syracuseStep 5940989 = 2227871) B2227871
theorem B21653369 : Blo 1780091 21653369 := bstep (se 2 (by rfl) ⟨8120013, by rfl⟩ : syracuseStep 21653369 = 16240027) B16240027
theorem B2672507 : Blo 1780091 2672507 := bstep (se 1 (by rfl) ⟨2004380, by rfl⟩ : syracuseStep 2672507 = 4008761) B4008761
theorem B4007807 : Blo 1780091 4007807 := bstep (se 1 (by rfl) ⟨3005855, by rfl⟩ : syracuseStep 4007807 = 6011711) B6011711
theorem B6760381 : Blo 1780091 6760381 := bstep (se 3 (by rfl) ⟨1267571, by rfl⟩ : syracuseStep 6760381 = 2535143) B2535143
theorem B54847529 : Blo 1780091 54847529 := bstep (se 2 (by rfl) ⟨20567823, by rfl⟩ : syracuseStep 54847529 = 41135647) B41135647
theorem B2672681 : Blo 1780091 2672681 := bstep (se 2 (by rfl) ⟨1002255, by rfl⟩ : syracuseStep 2672681 = 2004511) B2004511
theorem B4507721 : Blo 1780091 4507721 := bstep (se 2 (by rfl) ⟨1690395, by rfl⟩ : syracuseStep 4507721 = 3380791) B3380791
theorem B45664559 : Blo 1780091 45664559 := bstep (se 1 (by rfl) ⟨34248419, by rfl⟩ : syracuseStep 45664559 = 68496839) B68496839
theorem B2673095 : Blo 1780091 2673095 := bstep (se 1 (by rfl) ⟨2004821, by rfl⟩ : syracuseStep 2673095 = 4009643) B4009643
theorem B48736727 : Blo 1780091 48736727 := bstep (se 1 (by rfl) ⟨36552545, by rfl⟩ : syracuseStep 48736727 = 73105091) B73105091
theorem B1780191 : Blo 1780091 1780191 := bstep (se 1 (by rfl) ⟨1335143, by rfl⟩ : syracuseStep 1780191 = 2670287) B2670287
theorem B4508207 : Blo 1780091 4508207 := bstep (se 1 (by rfl) ⟨3381155, by rfl⟩ : syracuseStep 4508207 = 6762311) B6762311
theorem B1780351 : Blo 1780091 1780351 := bstep (se 1 (by rfl) ⟨1335263, by rfl⟩ : syracuseStep 1780351 = 2670527) B2670527
theorem B1780463 : Blo 1780091 1780463 := bstep (se 1 (by rfl) ⟨1335347, by rfl⟩ : syracuseStep 1780463 = 2670695) B2670695
theorem B1780479 : Blo 1780091 1780479 := bstep (se 1 (by rfl) ⟨1335359, by rfl⟩ : syracuseStep 1780479 = 2670719) B2670719
theorem B21670847 : Blo 1780091 21670847 := bstep (se 1 (by rfl) ⟨16253135, by rfl⟩ : syracuseStep 21670847 = 32506271) B32506271
theorem B6761627 : Blo 1780091 6761627 := bstep (se 1 (by rfl) ⟨5071220, by rfl⟩ : syracuseStep 6761627 = 10142441) B10142441
theorem B31255807 : Blo 1780091 31255807 := bstep (se 1 (by rfl) ⟨23441855, by rfl⟩ : syracuseStep 31255807 = 46883711) B46883711
theorem B1781055 : Blo 1780091 1781055 := bstep (se 1 (by rfl) ⟨1335791, by rfl⟩ : syracuseStep 1781055 = 2671583) B2671583
theorem B4009391 : Blo 1780091 4009391 := bstep (se 1 (by rfl) ⟨3007043, by rfl⟩ : syracuseStep 4009391 = 6014087) B6014087
theorem B4009499 : Blo 1780091 4009499 := bstep (se 1 (by rfl) ⟨3007124, by rfl⟩ : syracuseStep 4009499 = 6014249) B6014249
theorem B15216599 : Blo 1780091 15216599 := bstep (se 1 (by rfl) ⟨11412449, by rfl⟩ : syracuseStep 15216599 = 22824899) B22824899
theorem B11407787 : Blo 1780091 11407787 := bstep (se 1 (by rfl) ⟨8555840, by rfl⟩ : syracuseStep 11407787 = 17111681) B17111681
theorem B6009551 : Blo 1780091 6009551 := bstep (se 1 (by rfl) ⟨4507163, by rfl⟩ : syracuseStep 6009551 = 9014327) B9014327
theorem B11416859 : Blo 1780091 11416859 := bstep (se 1 (by rfl) ⟨8562644, by rfl⟩ : syracuseStep 11416859 = 17125289) B17125289
theorem B2708959 : Blo 1780091 2708959 := bstep (se 1 (by rfl) ⟨2031719, by rfl⟩ : syracuseStep 2708959 = 4063439) B4063439
theorem B6010361 : Blo 1780091 6010361 := bstep (se 2 (by rfl) ⟨2253885, by rfl⟩ : syracuseStep 6010361 = 4507771) B4507771
theorem B20559433 : Blo 1780091 20559433 := bstep (se 2 (by rfl) ⟨7709787, by rfl⟩ : syracuseStep 20559433 = 15419575) B15419575
theorem B2004583 : Blo 1780091 2004583 := bstep (se 1 (by rfl) ⟨1503437, by rfl⟩ : syracuseStep 2004583 = 3006875) B3006875
theorem B211105597 : Blo 1780091 211105597 := bstep (se 3 (by rfl) ⟨39582299, by rfl⟩ : syracuseStep 211105597 = 79164599) B79164599
theorem B3381095 : Blo 1780091 3381095 := bstep (se 1 (by rfl) ⟨2535821, by rfl⟩ : syracuseStep 3381095 = 5071643) B5071643
theorem B3004411 : Blo 1780091 3004411 := bstep (se 1 (by rfl) ⟨2253308, by rfl⟩ : syracuseStep 3004411 = 4506617) B4506617
theorem B1249941851 : Blo 1780091 1249941851 := bstep (se 1 (by rfl) ⟨937456388, by rfl⟩ : syracuseStep 1249941851 = 1874912777) B1874912777
theorem B49404329 : Blo 1780091 49404329 := bstep (se 2 (by rfl) ⟨18526623, by rfl⟩ : syracuseStep 49404329 = 37053247) B37053247
theorem B175733171 : Blo 1780091 175733171 := bstep (se 1 (by rfl) ⟨131799878, by rfl⟩ : syracuseStep 175733171 = 263599757) B263599757
theorem B21658043 : Blo 1780091 21658043 := bstep (se 1 (by rfl) ⟨16243532, by rfl⟩ : syracuseStep 21658043 = 32487065) B32487065
theorem B5708303 : Blo 1780091 5708303 := bstep (se 1 (by rfl) ⟨4281227, by rfl⟩ : syracuseStep 5708303 = 8562455) B8562455
theorem B25688623 : Blo 1780091 25688623 := bstep (se 1 (by rfl) ⟨19266467, by rfl⟩ : syracuseStep 25688623 = 38532935) B38532935
theorem B10828343 : Blo 1780091 10828343 := bstep (se 1 (by rfl) ⟨8121257, by rfl⟩ : syracuseStep 10828343 = 16242515) B16242515
theorem B34233353 : Blo 1780091 34233353 := bstep (se 2 (by rfl) ⟨12837507, by rfl⟩ : syracuseStep 34233353 = 25675015) B25675015
theorem B9018377 : Blo 1780091 9018377 := bstep (se 2 (by rfl) ⟨3381891, by rfl⟩ : syracuseStep 9018377 = 6763783) B6763783
theorem B22264847 : Blo 1780091 22264847 := bstep (se 1 (by rfl) ⟨16698635, by rfl⟩ : syracuseStep 22264847 = 33397271) B33397271
theorem B2284699 : Blo 1780091 2284699 := bstep (se 1 (by rfl) ⟨1713524, by rfl⟩ : syracuseStep 2284699 = 3427049) B3427049
theorem B3005903 : Blo 1780091 3005903 := bstep (se 1 (by rfl) ⟨2254427, by rfl⟩ : syracuseStep 3005903 = 4508855) B4508855
theorem B74079841 : Blo 1780091 74079841 := bstep (se 2 (by rfl) ⟨27779940, by rfl⟩ : syracuseStep 74079841 = 55559881) B55559881
theorem B2670263 : Blo 1780091 2670263 := bstep (se 1 (by rfl) ⟨2002697, by rfl⟩ : syracuseStep 2670263 = 4005395) B4005395
theorem B11411219 : Blo 1780091 11411219 := bstep (se 1 (by rfl) ⟨8558414, by rfl⟩ : syracuseStep 11411219 = 17116829) B17116829
theorem B4005863 : Blo 1780091 4005863 := bstep (se 1 (by rfl) ⟨3004397, by rfl⟩ : syracuseStep 4005863 = 6008795) B6008795
theorem B5783795 : Blo 1780091 5783795 := bstep (se 1 (by rfl) ⟨4337846, by rfl⟩ : syracuseStep 5783795 = 8675693) B8675693
theorem B4505939 : Blo 1780091 4505939 := bstep (se 1 (by rfl) ⟨3379454, by rfl⟩ : syracuseStep 4505939 = 6758909) B6758909
theorem B4006367 : Blo 1780091 4006367 := bstep (se 1 (by rfl) ⟨3004775, by rfl⟩ : syracuseStep 4006367 = 6009551) B6009551
theorem B2671103 : Blo 1780091 2671103 := bstep (se 1 (by rfl) ⟨2003327, by rfl⟩ : syracuseStep 2671103 = 4006655) B4006655
theorem B34251497 : Blo 1780091 34251497 := bstep (se 2 (by rfl) ⟨12844311, by rfl⟩ : syracuseStep 34251497 = 25688623) B25688623
theorem B7611239 : Blo 1780091 7611239 := bstep (se 1 (by rfl) ⟨5708429, by rfl⟩ : syracuseStep 7611239 = 11416859) B11416859
theorem B4006907 : Blo 1780091 4006907 := bstep (se 1 (by rfl) ⟨3005180, by rfl⟩ : syracuseStep 4006907 = 6010361) B6010361
theorem B2254063 : Blo 1780091 2254063 := bstep (se 1 (by rfl) ⟨1690547, by rfl⟩ : syracuseStep 2254063 = 3381095) B3381095
theorem B14435579 : Blo 1780091 14435579 := bstep (se 1 (by rfl) ⟨10826684, by rfl⟩ : syracuseStep 14435579 = 21653369) B21653369
theorem B2671871 : Blo 1780091 2671871 := bstep (se 1 (by rfl) ⟨2003903, by rfl⟩ : syracuseStep 2671871 = 4007807) B4007807
theorem B30443039 : Blo 1780091 30443039 := bstep (se 1 (by rfl) ⟨22832279, by rfl⟩ : syracuseStep 30443039 = 45664559) B45664559
theorem B117155447 : Blo 1780091 117155447 := bstep (se 1 (by rfl) ⟨87866585, by rfl⟩ : syracuseStep 117155447 = 175733171) B175733171
theorem B32491151 : Blo 1780091 32491151 := bstep (se 1 (by rfl) ⟨24368363, by rfl⟩ : syracuseStep 32491151 = 48736727) B48736727
theorem B41674409 : Blo 1780091 41674409 := bstep (se 2 (by rfl) ⟨15627903, by rfl⟩ : syracuseStep 41674409 = 31255807) B31255807
theorem B7218895 : Blo 1780091 7218895 := bstep (se 1 (by rfl) ⟨5414171, by rfl⟩ : syracuseStep 7218895 = 10828343) B10828343
theorem B27412577 : Blo 1780091 27412577 := bstep (se 2 (by rfl) ⟨10279716, by rfl⟩ : syracuseStep 27412577 = 20559433) B20559433
theorem B4507751 : Blo 1780091 4507751 := bstep (se 1 (by rfl) ⟨3380813, by rfl⟩ : syracuseStep 4507751 = 6761627) B6761627
theorem B98773121 : Blo 1780091 98773121 := bstep (se 2 (by rfl) ⟨37039920, by rfl⟩ : syracuseStep 98773121 = 74079841) B74079841
theorem B2672777 : Blo 1780091 2672777 := bstep (se 2 (by rfl) ⟨1002291, by rfl⟩ : syracuseStep 2672777 = 2004583) B2004583
theorem B2672927 : Blo 1780091 2672927 := bstep (se 1 (by rfl) ⟨2004695, by rfl⟩ : syracuseStep 2672927 = 4009391) B4009391
theorem B2672999 : Blo 1780091 2672999 := bstep (se 1 (by rfl) ⟨2004749, by rfl⟩ : syracuseStep 2672999 = 4009499) B4009499
theorem B1780175 : Blo 1780091 1780175 := bstep (se 1 (by rfl) ⟨1335131, by rfl⟩ : syracuseStep 1780175 = 2670263) B2670263
theorem B9013841 : Blo 1780091 9013841 := bstep (se 2 (by rfl) ⟨3380190, by rfl⟩ : syracuseStep 9013841 = 6760381) B6760381
theorem B10144399 : Blo 1780091 10144399 := bstep (se 1 (by rfl) ⟨7608299, by rfl⟩ : syracuseStep 10144399 = 15216599) B15216599
theorem B6761339 : Blo 1780091 6761339 := bstep (se 1 (by rfl) ⟨5071004, by rfl⟩ : syracuseStep 6761339 = 10142009) B10142009
theorem B7605191 : Blo 1780091 7605191 := bstep (se 1 (by rfl) ⟨5703893, by rfl⟩ : syracuseStep 7605191 = 11407787) B11407787
theorem B1780927 : Blo 1780091 1780927 := bstep (se 1 (by rfl) ⟨1335695, by rfl⟩ : syracuseStep 1780927 = 2671391) B2671391
theorem B1781063 : Blo 1780091 1781063 := bstep (se 1 (by rfl) ⟨1335797, by rfl⟩ : syracuseStep 1781063 = 2671595) B2671595
theorem B1781231 : Blo 1780091 1781231 := bstep (se 1 (by rfl) ⟨1335923, by rfl⟩ : syracuseStep 1781231 = 2671847) B2671847
theorem B4009679 : Blo 1780091 4009679 := bstep (se 1 (by rfl) ⟨3007259, by rfl⟩ : syracuseStep 4009679 = 6014519) B6014519
theorem B1781531 : Blo 1780091 1781531 := bstep (se 1 (by rfl) ⟨1336148, by rfl⟩ : syracuseStep 1781531 = 2672297) B2672297
theorem B3960659 : Blo 1780091 3960659 := bstep (se 1 (by rfl) ⟨2970494, by rfl⟩ : syracuseStep 3960659 = 5940989) B5940989
theorem B1781671 : Blo 1780091 1781671 := bstep (se 1 (by rfl) ⟨1336253, by rfl⟩ : syracuseStep 1781671 = 2672507) B2672507
theorem B36565019 : Blo 1780091 36565019 := bstep (se 1 (by rfl) ⟨27423764, by rfl⟩ : syracuseStep 36565019 = 54847529) B54847529
theorem B1781787 : Blo 1780091 1781787 := bstep (se 1 (by rfl) ⟨1336340, by rfl⟩ : syracuseStep 1781787 = 2672681) B2672681
theorem B833294567 : Blo 1780091 833294567 := bstep (se 1 (by rfl) ⟨624970925, by rfl⟩ : syracuseStep 833294567 = 1249941851) B1249941851
theorem B32936219 : Blo 1780091 32936219 := bstep (se 1 (by rfl) ⟨24702164, by rfl⟩ : syracuseStep 32936219 = 49404329) B49404329
theorem B14438695 : Blo 1780091 14438695 := bstep (se 1 (by rfl) ⟨10829021, by rfl⟩ : syracuseStep 14438695 = 21658043) B21658043
theorem B1782063 : Blo 1780091 1782063 := bstep (se 1 (by rfl) ⟨1336547, by rfl⟩ : syracuseStep 1782063 = 2673095) B2673095
theorem B3805535 : Blo 1780091 3805535 := bstep (se 1 (by rfl) ⟨2854151, by rfl⟩ : syracuseStep 3805535 = 5708303) B5708303
theorem B14447231 : Blo 1780091 14447231 := bstep (se 1 (by rfl) ⟨10835423, by rfl⟩ : syracuseStep 14447231 = 21670847) B21670847
theorem B30429917 : Blo 1780091 30429917 := bstep (se 3 (by rfl) ⟨5705609, by rfl⟩ : syracuseStep 30429917 = 11411219) B11411219
theorem B2003935 : Blo 1780091 2003935 := bstep (se 1 (by rfl) ⟨1502951, by rfl⟩ : syracuseStep 2003935 = 3005903) B3005903
theorem B281474129 : Blo 1780091 281474129 := bstep (se 2 (by rfl) ⟨105552798, by rfl⟩ : syracuseStep 281474129 = 211105597) B211105597
theorem B6854375 : Blo 1780091 6854375 := bstep (se 1 (by rfl) ⟨5140781, by rfl⟩ : syracuseStep 6854375 = 10281563) B10281563
theorem B6010685 : Blo 1780091 6010685 := bstep (se 3 (by rfl) ⟨1127003, by rfl⟩ : syracuseStep 6010685 = 2254007) B2254007
theorem B3005147 : Blo 1780091 3005147 := bstep (se 1 (by rfl) ⟨2253860, by rfl⟩ : syracuseStep 3005147 = 4507721) B4507721
theorem B3046265 : Blo 1780091 3046265 := bstep (se 2 (by rfl) ⟨1142349, by rfl⟩ : syracuseStep 3046265 = 2284699) B2284699
theorem B3005471 : Blo 1780091 3005471 := bstep (se 1 (by rfl) ⟨2254103, by rfl⟩ : syracuseStep 3005471 = 4508207) B4508207
theorem B3611945 : Blo 1780091 3611945 := bstep (se 2 (by rfl) ⟨1354479, by rfl⟩ : syracuseStep 3611945 = 2708959) B2708959
theorem B22822235 : Blo 1780091 22822235 := bstep (se 1 (by rfl) ⟨17116676, by rfl⟩ : syracuseStep 22822235 = 34233353) B34233353
theorem B6012251 : Blo 1780091 6012251 := bstep (se 1 (by rfl) ⟨4509188, by rfl⟩ : syracuseStep 6012251 = 9018377) B9018377
theorem B14843231 : Blo 1780091 14843231 := bstep (se 1 (by rfl) ⟨11132423, by rfl⟩ : syracuseStep 14843231 = 22264847) B22264847
theorem B2670575 : Blo 1780091 2670575 := bstep (se 1 (by rfl) ⟨2002931, by rfl⟩ : syracuseStep 2670575 = 4005863) B4005863
theorem B4005881 : Blo 1780091 4005881 := bstep (se 2 (by rfl) ⟨1502205, by rfl⟩ : syracuseStep 4005881 = 3004411) B3004411
theorem B2670911 : Blo 1780091 2670911 := bstep (se 1 (by rfl) ⟨2003183, by rfl⟩ : syracuseStep 2670911 = 4006367) B4006367
theorem B19251593 : Blo 1780091 19251593 := bstep (se 2 (by rfl) ⟨7219347, by rfl⟩ : syracuseStep 19251593 = 14438695) B14438695
theorem B2671271 : Blo 1780091 2671271 := bstep (se 1 (by rfl) ⟨2003453, by rfl⟩ : syracuseStep 2671271 = 4006907) B4006907
theorem B13525865 : Blo 1780091 13525865 := bstep (se 2 (by rfl) ⟨5072199, by rfl⟩ : syracuseStep 13525865 = 10144399) B10144399
theorem B158327797 : Blo 1780091 158327797 := bstep (se 5 (by rfl) ⟨7421615, by rfl⟩ : syracuseStep 158327797 = 14843231) B14843231
theorem B78103631 : Blo 1780091 78103631 := bstep (se 1 (by rfl) ⟨58577723, by rfl⟩ : syracuseStep 78103631 = 117155447) B117155447
theorem B21660767 : Blo 1780091 21660767 := bstep (se 1 (by rfl) ⟨16245575, by rfl⟩ : syracuseStep 21660767 = 32491151) B32491151
theorem B4007123 : Blo 1780091 4007123 := bstep (se 1 (by rfl) ⟨3005342, by rfl⟩ : syracuseStep 4007123 = 6010685) B6010685
theorem B2671913 : Blo 1780091 2671913 := bstep (se 2 (by rfl) ⟨1001967, by rfl⟩ : syracuseStep 2671913 = 2003935) B2003935
theorem B4507559 : Blo 1780091 4507559 := bstep (se 1 (by rfl) ⟨3380669, by rfl⟩ : syracuseStep 4507559 = 6761339) B6761339
theorem B15214823 : Blo 1780091 15214823 := bstep (se 1 (by rfl) ⟨11411117, by rfl⟩ : syracuseStep 15214823 = 22822235) B22822235
theorem B4008167 : Blo 1780091 4008167 := bstep (se 1 (by rfl) ⟨3006125, by rfl⟩ : syracuseStep 4008167 = 6012251) B6012251
theorem B2673119 : Blo 1780091 2673119 := bstep (se 1 (by rfl) ⟨2004839, by rfl⟩ : syracuseStep 2673119 = 4009679) B4009679
theorem B2640439 : Blo 1780091 2640439 := bstep (se 1 (by rfl) ⟨1980329, by rfl⟩ : syracuseStep 2640439 = 3960659) B3960659
theorem B1780383 : Blo 1780091 1780383 := bstep (se 1 (by rfl) ⟨1335287, by rfl⟩ : syracuseStep 1780383 = 2670575) B2670575
theorem B21957479 : Blo 1780091 21957479 := bstep (se 1 (by rfl) ⟨16468109, by rfl⟩ : syracuseStep 21957479 = 32936219) B32936219
theorem B1780735 : Blo 1780091 1780735 := bstep (se 1 (by rfl) ⟨1335551, by rfl⟩ : syracuseStep 1780735 = 2671103) B2671103
theorem B20286611 : Blo 1780091 20286611 := bstep (se 1 (by rfl) ⟨15214958, by rfl⟩ : syracuseStep 20286611 = 30429917) B30429917
theorem B22834331 : Blo 1780091 22834331 := bstep (se 1 (by rfl) ⟨17125748, by rfl⟩ : syracuseStep 22834331 = 34251497) B34251497
theorem B5074159 : Blo 1780091 5074159 := bstep (se 1 (by rfl) ⟨3805619, by rfl⟩ : syracuseStep 5074159 = 7611239) B7611239
theorem B187649419 : Blo 1780091 187649419 := bstep (se 1 (by rfl) ⟨140737064, by rfl⟩ : syracuseStep 187649419 = 281474129) B281474129
theorem B1781247 : Blo 1780091 1781247 := bstep (se 1 (by rfl) ⟨1335935, by rfl⟩ : syracuseStep 1781247 = 2671871) B2671871
theorem B20295359 : Blo 1780091 20295359 := bstep (se 1 (by rfl) ⟨15221519, by rfl⟩ : syracuseStep 20295359 = 30443039) B30443039
theorem B27782939 : Blo 1780091 27782939 := bstep (se 1 (by rfl) ⟨20837204, by rfl⟩ : syracuseStep 27782939 = 41674409) B41674409
theorem B1781851 : Blo 1780091 1781851 := bstep (se 1 (by rfl) ⟨1336388, by rfl⟩ : syracuseStep 1781851 = 2672777) B2672777
theorem B1781951 : Blo 1780091 1781951 := bstep (se 1 (by rfl) ⟨1336463, by rfl⟩ : syracuseStep 1781951 = 2672927) B2672927
theorem B1781999 : Blo 1780091 1781999 := bstep (se 1 (by rfl) ⟨1336499, by rfl⟩ : syracuseStep 1781999 = 2672999) B2672999
theorem B6009227 : Blo 1780091 6009227 := bstep (se 1 (by rfl) ⟨4506920, by rfl⟩ : syracuseStep 6009227 = 9013841) B9013841
theorem B2003431 : Blo 1780091 2003431 := bstep (se 1 (by rfl) ⟨1502573, by rfl⟩ : syracuseStep 2003431 = 3005147) B3005147
theorem B2003647 : Blo 1780091 2003647 := bstep (se 1 (by rfl) ⟨1502735, by rfl⟩ : syracuseStep 2003647 = 3005471) B3005471
theorem B24376679 : Blo 1780091 24376679 := bstep (se 1 (by rfl) ⟨18282509, by rfl⟩ : syracuseStep 24376679 = 36565019) B36565019
theorem B555529711 : Blo 1780091 555529711 := bstep (se 1 (by rfl) ⟨416647283, by rfl⟩ : syracuseStep 555529711 = 833294567) B833294567
theorem B3855863 : Blo 1780091 3855863 := bstep (se 1 (by rfl) ⟨2891897, by rfl⟩ : syracuseStep 3855863 = 5783795) B5783795
theorem B3003959 : Blo 1780091 3003959 := bstep (se 1 (by rfl) ⟨2252969, by rfl⟩ : syracuseStep 3003959 = 4505939) B4505939
theorem B2537023 : Blo 1780091 2537023 := bstep (se 1 (by rfl) ⟨1902767, by rfl⟩ : syracuseStep 2537023 = 3805535) B3805535
theorem B263394989 : Blo 1780091 263394989 := bstep (se 3 (by rfl) ⟨49386560, by rfl⟩ : syracuseStep 263394989 = 98773121) B98773121
theorem B9631487 : Blo 1780091 9631487 := bstep (se 1 (by rfl) ⟨7223615, by rfl⟩ : syracuseStep 9631487 = 14447231) B14447231
theorem B9623719 : Blo 1780091 9623719 := bstep (se 1 (by rfl) ⟨7217789, by rfl⟩ : syracuseStep 9623719 = 14435579) B14435579
theorem B4569583 : Blo 1780091 4569583 := bstep (se 1 (by rfl) ⟨3427187, by rfl⟩ : syracuseStep 4569583 = 6854375) B6854375
theorem B18275051 : Blo 1780091 18275051 := bstep (se 1 (by rfl) ⟨13706288, by rfl⟩ : syracuseStep 18275051 = 27412577) B27412577
theorem B3005167 : Blo 1780091 3005167 := bstep (se 1 (by rfl) ⟨2253875, by rfl⟩ : syracuseStep 3005167 = 4507751) B4507751
theorem B3005417 : Blo 1780091 3005417 := bstep (se 2 (by rfl) ⟨1127031, by rfl⟩ : syracuseStep 3005417 = 2254063) B2254063
theorem B2030843 : Blo 1780091 2030843 := bstep (se 1 (by rfl) ⟨1523132, by rfl⟩ : syracuseStep 2030843 = 3046265) B3046265
theorem B5070127 : Blo 1780091 5070127 := bstep (se 1 (by rfl) ⟨3802595, by rfl⟩ : syracuseStep 5070127 = 7605191) B7605191
theorem B2407963 : Blo 1780091 2407963 := bstep (se 1 (by rfl) ⟨1805972, by rfl⟩ : syracuseStep 2407963 = 3611945) B3611945
theorem B9625193 : Blo 1780091 9625193 := bstep (se 2 (by rfl) ⟨3609447, by rfl⟩ : syracuseStep 9625193 = 7218895) B7218895
theorem B2670587 : Blo 1780091 2670587 := bstep (se 1 (by rfl) ⟨2002940, by rfl⟩ : syracuseStep 2670587 = 4005881) B4005881
theorem B4006151 : Blo 1780091 4006151 := bstep (se 1 (by rfl) ⟨3004613, by rfl⟩ : syracuseStep 4006151 = 6009227) B6009227
theorem B14082341 : Blo 1780091 14082341 := bstep (se 4 (by rfl) ⟨1320219, by rfl⟩ : syracuseStep 14082341 = 2640439) B2640439
theorem B2671241 : Blo 1780091 2671241 := bstep (se 2 (by rfl) ⟨1001715, by rfl⟩ : syracuseStep 2671241 = 2003431) B2003431
theorem B5415581 : Blo 1780091 5415581 := bstep (se 3 (by rfl) ⟨1015421, by rfl⟩ : syracuseStep 5415581 = 2030843) B2030843
theorem B52069087 : Blo 1780091 52069087 := bstep (se 1 (by rfl) ⟨39051815, by rfl⟩ : syracuseStep 52069087 = 78103631) B78103631
theorem B2671415 : Blo 1780091 2671415 := bstep (se 1 (by rfl) ⟨2003561, by rfl⟩ : syracuseStep 2671415 = 4007123) B4007123
theorem B2671529 : Blo 1780091 2671529 := bstep (se 2 (by rfl) ⟨1001823, by rfl⟩ : syracuseStep 2671529 = 2003647) B2003647
theorem B4006889 : Blo 1780091 4006889 := bstep (se 2 (by rfl) ⟨1502583, by rfl⟩ : syracuseStep 4006889 = 3005167) B3005167
theorem B175596659 : Blo 1780091 175596659 := bstep (se 1 (by rfl) ⟨131697494, by rfl⟩ : syracuseStep 175596659 = 263394989) B263394989
theorem B10282301 : Blo 1780091 10282301 := bstep (se 3 (by rfl) ⟨1927931, by rfl⟩ : syracuseStep 10282301 = 3855863) B3855863
theorem B10143215 : Blo 1780091 10143215 := bstep (se 1 (by rfl) ⟨7607411, by rfl⟩ : syracuseStep 10143215 = 15214823) B15214823
theorem B2672111 : Blo 1780091 2672111 := bstep (se 1 (by rfl) ⟨2004083, by rfl⟩ : syracuseStep 2672111 = 4008167) B4008167
theorem B6760169 : Blo 1780091 6760169 := bstep (se 2 (by rfl) ⟨2535063, by rfl⟩ : syracuseStep 6760169 = 5070127) B5070127
theorem B12183367 : Blo 1780091 12183367 := bstep (se 1 (by rfl) ⟨9137525, by rfl⟩ : syracuseStep 12183367 = 18275051) B18275051
theorem B740706281 : Blo 1780091 740706281 := bstep (se 2 (by rfl) ⟨277764855, by rfl⟩ : syracuseStep 740706281 = 555529711) B555529711
theorem B15222887 : Blo 1780091 15222887 := bstep (se 1 (by rfl) ⟨11417165, by rfl⟩ : syracuseStep 15222887 = 22834331) B22834331
theorem B6416795 : Blo 1780091 6416795 := bstep (se 1 (by rfl) ⟨4812596, by rfl⟩ : syracuseStep 6416795 = 9625193) B9625193
theorem B1780391 : Blo 1780091 1780391 := bstep (se 1 (by rfl) ⟨1335293, by rfl⟩ : syracuseStep 1780391 = 2670587) B2670587
theorem B1780607 : Blo 1780091 1780607 := bstep (se 1 (by rfl) ⟨1335455, by rfl⟩ : syracuseStep 1780607 = 2670911) B2670911
theorem B12831625 : Blo 1780091 12831625 := bstep (se 2 (by rfl) ⟨4811859, by rfl⟩ : syracuseStep 12831625 = 9623719) B9623719
theorem B1780847 : Blo 1780091 1780847 := bstep (se 1 (by rfl) ⟨1335635, by rfl⟩ : syracuseStep 1780847 = 2671271) B2671271
theorem B1781275 : Blo 1780091 1781275 := bstep (se 1 (by rfl) ⟨1335956, by rfl⟩ : syracuseStep 1781275 = 2671913) B2671913
theorem B2002639 : Blo 1780091 2002639 := bstep (se 1 (by rfl) ⟨1501979, by rfl⟩ : syracuseStep 2002639 = 3003959) B3003959
theorem B211103729 : Blo 1780091 211103729 := bstep (se 2 (by rfl) ⟨79163898, by rfl⟩ : syracuseStep 211103729 = 158327797) B158327797
theorem B1782079 : Blo 1780091 1782079 := bstep (se 1 (by rfl) ⟨1336559, by rfl⟩ : syracuseStep 1782079 = 2673119) B2673119
theorem B2003611 : Blo 1780091 2003611 := bstep (se 1 (by rfl) ⟨1502708, by rfl⟩ : syracuseStep 2003611 = 3005417) B3005417
theorem B13530239 : Blo 1780091 13530239 := bstep (se 1 (by rfl) ⟨10147679, by rfl⟩ : syracuseStep 13530239 = 20295359) B20295359
theorem B12834395 : Blo 1780091 12834395 := bstep (se 1 (by rfl) ⟨9625796, by rfl⟩ : syracuseStep 12834395 = 19251593) B19251593
theorem B9017243 : Blo 1780091 9017243 := bstep (se 1 (by rfl) ⟨6762932, by rfl⟩ : syracuseStep 9017243 = 13525865) B13525865
theorem B6092777 : Blo 1780091 6092777 := bstep (se 2 (by rfl) ⟨2284791, by rfl⟩ : syracuseStep 6092777 = 4569583) B4569583
theorem B14440511 : Blo 1780091 14440511 := bstep (se 1 (by rfl) ⟨10830383, by rfl⟩ : syracuseStep 14440511 = 21660767) B21660767
theorem B16251119 : Blo 1780091 16251119 := bstep (se 1 (by rfl) ⟨12188339, by rfl⟩ : syracuseStep 16251119 = 24376679) B24376679
theorem B6420991 : Blo 1780091 6420991 := bstep (se 1 (by rfl) ⟨4815743, by rfl⟩ : syracuseStep 6420991 = 9631487) B9631487
theorem B3005039 : Blo 1780091 3005039 := bstep (se 1 (by rfl) ⟨2253779, by rfl⟩ : syracuseStep 3005039 = 4507559) B4507559
theorem B6765545 : Blo 1780091 6765545 := bstep (se 2 (by rfl) ⟨2537079, by rfl⟩ : syracuseStep 6765545 = 5074159) B5074159
theorem B250199225 : Blo 1780091 250199225 := bstep (se 2 (by rfl) ⟨93824709, by rfl⟩ : syracuseStep 250199225 = 187649419) B187649419
theorem B14638319 : Blo 1780091 14638319 := bstep (se 1 (by rfl) ⟨10978739, by rfl⟩ : syracuseStep 14638319 = 21957479) B21957479
theorem B3210617 : Blo 1780091 3210617 := bstep (se 2 (by rfl) ⟨1203981, by rfl⟩ : syracuseStep 3210617 = 2407963) B2407963
theorem B3382697 : Blo 1780091 3382697 := bstep (se 2 (by rfl) ⟨1268511, by rfl⟩ : syracuseStep 3382697 = 2537023) B2537023
theorem B13524407 : Blo 1780091 13524407 := bstep (se 1 (by rfl) ⟨10143305, by rfl⟩ : syracuseStep 13524407 = 20286611) B20286611
theorem B18521959 : Blo 1780091 18521959 := bstep (se 1 (by rfl) ⟨13891469, by rfl⟩ : syracuseStep 18521959 = 27782939) B27782939
theorem B2670767 : Blo 1780091 2670767 := bstep (se 1 (by rfl) ⟨2003075, by rfl⟩ : syracuseStep 2670767 = 4006151) B4006151
theorem B2671259 : Blo 1780091 2671259 := bstep (se 1 (by rfl) ⟨2003444, by rfl⟩ : syracuseStep 2671259 = 4006889) B4006889
theorem B8561321 : Blo 1780091 8561321 := bstep (se 2 (by rfl) ⟨3210495, by rfl⟩ : syracuseStep 8561321 = 6420991) B6420991
theorem B117064439 : Blo 1780091 117064439 := bstep (se 1 (by rfl) ⟨87798329, by rfl⟩ : syracuseStep 117064439 = 175596659) B175596659
theorem B9020159 : Blo 1780091 9020159 := bstep (se 1 (by rfl) ⟨6765119, by rfl⟩ : syracuseStep 9020159 = 13530239) B13530239
theorem B37552909 : Blo 1780091 37552909 := bstep (se 3 (by rfl) ⟨7041170, by rfl⟩ : syracuseStep 37552909 = 14082341) B14082341
theorem B2671481 : Blo 1780091 2671481 := bstep (se 2 (by rfl) ⟨1001805, by rfl⟩ : syracuseStep 2671481 = 2003611) B2003611
theorem B8561645 : Blo 1780091 8561645 := bstep (se 3 (by rfl) ⟨1605308, by rfl⟩ : syracuseStep 8561645 = 3210617) B3210617
theorem B4506779 : Blo 1780091 4506779 := bstep (se 1 (by rfl) ⟨3380084, by rfl⟩ : syracuseStep 4506779 = 6760169) B6760169
theorem B277701797 : Blo 1780091 277701797 := bstep (se 4 (by rfl) ⟨26034543, by rfl⟩ : syracuseStep 277701797 = 52069087) B52069087
theorem B9627007 : Blo 1780091 9627007 := bstep (se 1 (by rfl) ⟨7220255, by rfl⟩ : syracuseStep 9627007 = 14440511) B14440511
theorem B4277863 : Blo 1780091 4277863 := bstep (se 1 (by rfl) ⟨3208397, by rfl⟩ : syracuseStep 4277863 = 6416795) B6416795
theorem B166799483 : Blo 1780091 166799483 := bstep (se 1 (by rfl) ⟨125099612, by rfl⟩ : syracuseStep 166799483 = 250199225) B250199225
theorem B9758879 : Blo 1780091 9758879 := bstep (se 1 (by rfl) ⟨7319159, by rfl⟩ : syracuseStep 9758879 = 14638319) B14638319
theorem B2255131 : Blo 1780091 2255131 := bstep (se 1 (by rfl) ⟨1691348, by rfl⟩ : syracuseStep 2255131 = 3382697) B3382697
theorem B16247405 : Blo 1780091 16247405 := bstep (se 3 (by rfl) ⟨3046388, by rfl⟩ : syracuseStep 16247405 = 6092777) B6092777
theorem B1780827 : Blo 1780091 1780827 := bstep (se 1 (by rfl) ⟨1335620, by rfl⟩ : syracuseStep 1780827 = 2671241) B2671241
theorem B1780943 : Blo 1780091 1780943 := bstep (se 1 (by rfl) ⟨1335707, by rfl⟩ : syracuseStep 1780943 = 2671415) B2671415
theorem B1781019 : Blo 1780091 1781019 := bstep (se 1 (by rfl) ⟨1335764, by rfl⟩ : syracuseStep 1781019 = 2671529) B2671529
theorem B6762143 : Blo 1780091 6762143 := bstep (se 1 (by rfl) ⟨5071607, by rfl⟩ : syracuseStep 6762143 = 10143215) B10143215
theorem B1781407 : Blo 1780091 1781407 := bstep (se 1 (by rfl) ⟨1336055, by rfl⟩ : syracuseStep 1781407 = 2672111) B2672111
theorem B8556263 : Blo 1780091 8556263 := bstep (se 1 (by rfl) ⟨6417197, by rfl⟩ : syracuseStep 8556263 = 12834395) B12834395
theorem B17108833 : Blo 1780091 17108833 := bstep (se 2 (by rfl) ⟨6415812, by rfl⟩ : syracuseStep 17108833 = 12831625) B12831625
theorem B10834079 : Blo 1780091 10834079 := bstep (se 1 (by rfl) ⟨8125559, by rfl⟩ : syracuseStep 10834079 = 16251119) B16251119
theorem B2003359 : Blo 1780091 2003359 := bstep (se 1 (by rfl) ⟨1502519, by rfl⟩ : syracuseStep 2003359 = 3005039) B3005039
theorem B4510363 : Blo 1780091 4510363 := bstep (se 1 (by rfl) ⟨3382772, by rfl⟩ : syracuseStep 4510363 = 6765545) B6765545
theorem B9016271 : Blo 1780091 9016271 := bstep (se 1 (by rfl) ⟨6762203, by rfl⟩ : syracuseStep 9016271 = 13524407) B13524407
theorem B24695945 : Blo 1780091 24695945 := bstep (se 2 (by rfl) ⟨9260979, by rfl⟩ : syracuseStep 24695945 = 18521959) B18521959
theorem B140735819 : Blo 1780091 140735819 := bstep (se 1 (by rfl) ⟨105551864, by rfl⟩ : syracuseStep 140735819 = 211103729) B211103729
theorem B3610387 : Blo 1780091 3610387 := bstep (se 1 (by rfl) ⟨2707790, by rfl⟩ : syracuseStep 3610387 = 5415581) B5415581
theorem B6854867 : Blo 1780091 6854867 := bstep (se 1 (by rfl) ⟨5141150, by rfl⟩ : syracuseStep 6854867 = 10282301) B10282301
theorem B6011495 : Blo 1780091 6011495 := bstep (se 1 (by rfl) ⟨4508621, by rfl⟩ : syracuseStep 6011495 = 9017243) B9017243
theorem B493804187 : Blo 1780091 493804187 := bstep (se 1 (by rfl) ⟨370353140, by rfl⟩ : syracuseStep 493804187 = 740706281) B740706281
theorem B10148591 : Blo 1780091 10148591 := bstep (se 1 (by rfl) ⟨7611443, by rfl⟩ : syracuseStep 10148591 = 15222887) B15222887
theorem B2670185 : Blo 1780091 2670185 := bstep (se 2 (by rfl) ⟨1001319, by rfl⟩ : syracuseStep 2670185 = 2002639) B2002639
theorem B16244489 : Blo 1780091 16244489 := bstep (se 2 (by rfl) ⟨6091683, by rfl⟩ : syracuseStep 16244489 = 12183367) B12183367
theorem B3006841 : Blo 1780091 3006841 := bstep (se 2 (by rfl) ⟨1127565, by rfl⟩ : syracuseStep 3006841 = 2255131) B2255131
theorem B6013439 : Blo 1780091 6013439 := bstep (se 1 (by rfl) ⟨4510079, by rfl⟩ : syracuseStep 6013439 = 9020159) B9020159
theorem B2671145 : Blo 1780091 2671145 := bstep (se 2 (by rfl) ⟨1001679, by rfl⟩ : syracuseStep 2671145 = 2003359) B2003359
theorem B6013817 : Blo 1780091 6013817 := bstep (se 2 (by rfl) ⟨2255181, by rfl⟩ : syracuseStep 6013817 = 4510363) B4510363
theorem B93823879 : Blo 1780091 93823879 := bstep (se 1 (by rfl) ⟨70367909, by rfl⟩ : syracuseStep 93823879 = 140735819) B140735819
theorem B50070545 : Blo 1780091 50070545 := bstep (se 2 (by rfl) ⟨18776454, by rfl⟩ : syracuseStep 50070545 = 37552909) B37552909
theorem B111199655 : Blo 1780091 111199655 := bstep (se 1 (by rfl) ⟨83399741, by rfl⟩ : syracuseStep 111199655 = 166799483) B166799483
theorem B6505919 : Blo 1780091 6505919 := bstep (se 1 (by rfl) ⟨4879439, by rfl⟩ : syracuseStep 6505919 = 9758879) B9758879
theorem B4007663 : Blo 1780091 4007663 := bstep (se 1 (by rfl) ⟨3005747, by rfl⟩ : syracuseStep 4007663 = 6011495) B6011495
theorem B10831603 : Blo 1780091 10831603 := bstep (se 1 (by rfl) ⟨8123702, by rfl⟩ : syracuseStep 10831603 = 16247405) B16247405
theorem B5703817 : Blo 1780091 5703817 := bstep (se 2 (by rfl) ⟨2138931, by rfl⟩ : syracuseStep 5703817 = 4277863) B4277863
theorem B1780123 : Blo 1780091 1780123 := bstep (se 1 (by rfl) ⟨1335092, by rfl⟩ : syracuseStep 1780123 = 2670185) B2670185
theorem B4508095 : Blo 1780091 4508095 := bstep (se 1 (by rfl) ⟨3381071, by rfl⟩ : syracuseStep 4508095 = 6762143) B6762143
theorem B5704175 : Blo 1780091 5704175 := bstep (se 1 (by rfl) ⟨4278131, by rfl⟩ : syracuseStep 5704175 = 8556263) B8556263
theorem B1780511 : Blo 1780091 1780511 := bstep (se 1 (by rfl) ⟨1335383, by rfl⟩ : syracuseStep 1780511 = 2670767) B2670767
theorem B1780839 : Blo 1780091 1780839 := bstep (se 1 (by rfl) ⟨1335629, by rfl⟩ : syracuseStep 1780839 = 2671259) B2671259
theorem B1780987 : Blo 1780091 1780987 := bstep (se 1 (by rfl) ⟨1335740, by rfl⟩ : syracuseStep 1780987 = 2671481) B2671481
theorem B4813849 : Blo 1780091 4813849 := bstep (se 2 (by rfl) ⟨1805193, by rfl⟩ : syracuseStep 4813849 = 3610387) B3610387
theorem B22811777 : Blo 1780091 22811777 := bstep (se 2 (by rfl) ⟨8554416, by rfl⟩ : syracuseStep 22811777 = 17108833) B17108833
theorem B740538125 : Blo 1780091 740538125 := bstep (se 3 (by rfl) ⟨138850898, by rfl⟩ : syracuseStep 740538125 = 277701797) B277701797
theorem B5707547 : Blo 1780091 5707547 := bstep (se 1 (by rfl) ⟨4280660, by rfl⟩ : syracuseStep 5707547 = 8561321) B8561321
theorem B78042959 : Blo 1780091 78042959 := bstep (se 1 (by rfl) ⟨58532219, by rfl⟩ : syracuseStep 78042959 = 117064439) B117064439
theorem B6010847 : Blo 1780091 6010847 := bstep (se 1 (by rfl) ⟨4508135, by rfl⟩ : syracuseStep 6010847 = 9016271) B9016271
theorem B5707763 : Blo 1780091 5707763 := bstep (se 1 (by rfl) ⟨4280822, by rfl⟩ : syracuseStep 5707763 = 8561645) B8561645
theorem B16463963 : Blo 1780091 16463963 := bstep (se 1 (by rfl) ⟨12347972, by rfl⟩ : syracuseStep 16463963 = 24695945) B24695945
theorem B3004519 : Blo 1780091 3004519 := bstep (se 1 (by rfl) ⟨2253389, by rfl⟩ : syracuseStep 3004519 = 4506779) B4506779
theorem B4569911 : Blo 1780091 4569911 := bstep (se 1 (by rfl) ⟨3427433, by rfl⟩ : syracuseStep 4569911 = 6854867) B6854867
theorem B115563509 : Blo 1780091 115563509 := bstep (se 5 (by rfl) ⟨5417039, by rfl⟩ : syracuseStep 115563509 = 10834079) B10834079
theorem B329202791 : Blo 1780091 329202791 := bstep (se 1 (by rfl) ⟨246902093, by rfl⟩ : syracuseStep 329202791 = 493804187) B493804187
theorem B6765727 : Blo 1780091 6765727 := bstep (se 1 (by rfl) ⟨5074295, by rfl⟩ : syracuseStep 6765727 = 10148591) B10148591
theorem B12836009 : Blo 1780091 12836009 := bstep (se 2 (by rfl) ⟨4813503, by rfl⟩ : syracuseStep 12836009 = 9627007) B9627007
theorem B10829659 : Blo 1780091 10829659 := bstep (se 1 (by rfl) ⟨8122244, by rfl⟩ : syracuseStep 10829659 = 16244489) B16244489
theorem B25673861 : Blo 1780091 25673861 := bstep (se 4 (by rfl) ⟨2406924, by rfl⟩ : syracuseStep 25673861 = 4813849) B4813849
theorem B4006025 : Blo 1780091 4006025 := bstep (se 2 (by rfl) ⟨1502259, by rfl⟩ : syracuseStep 4006025 = 3004519) B3004519
theorem B2671775 : Blo 1780091 2671775 := bstep (se 1 (by rfl) ⟨2003831, by rfl⟩ : syracuseStep 2671775 = 4007663) B4007663
theorem B493692083 : Blo 1780091 493692083 := bstep (se 1 (by rfl) ⟨370269062, by rfl⟩ : syracuseStep 493692083 = 740538125) B740538125
theorem B52028639 : Blo 1780091 52028639 := bstep (se 1 (by rfl) ⟨39021479, by rfl⟩ : syracuseStep 52028639 = 78042959) B78042959
theorem B4007231 : Blo 1780091 4007231 := bstep (se 1 (by rfl) ⟨3005423, by rfl⟩ : syracuseStep 4007231 = 6010847) B6010847
theorem B9020969 : Blo 1780091 9020969 := bstep (se 2 (by rfl) ⟨3382863, by rfl⟩ : syracuseStep 9020969 = 6765727) B6765727
theorem B3802783 : Blo 1780091 3802783 := bstep (se 1 (by rfl) ⟨2852087, by rfl⟩ : syracuseStep 3802783 = 5704175) B5704175
theorem B7605089 : Blo 1780091 7605089 := bstep (se 2 (by rfl) ⟨2851908, by rfl⟩ : syracuseStep 7605089 = 5703817) B5703817
theorem B4008959 : Blo 1780091 4008959 := bstep (se 1 (by rfl) ⟨3006719, by rfl⟩ : syracuseStep 4008959 = 6013439) B6013439
theorem B1780763 : Blo 1780091 1780763 := bstep (se 1 (by rfl) ⟨1335572, by rfl⟩ : syracuseStep 1780763 = 2671145) B2671145
theorem B4009121 : Blo 1780091 4009121 := bstep (se 2 (by rfl) ⟨1503420, by rfl⟩ : syracuseStep 4009121 = 3006841) B3006841
theorem B4009211 : Blo 1780091 4009211 := bstep (se 1 (by rfl) ⟨3006908, by rfl⟩ : syracuseStep 4009211 = 6013817) B6013817
theorem B15207851 : Blo 1780091 15207851 := bstep (se 1 (by rfl) ⟨11405888, by rfl⟩ : syracuseStep 15207851 = 22811777) B22811777
theorem B4337279 : Blo 1780091 4337279 := bstep (se 1 (by rfl) ⟨3252959, by rfl⟩ : syracuseStep 4337279 = 6505919) B6505919
theorem B3805031 : Blo 1780091 3805031 := bstep (se 1 (by rfl) ⟨2853773, by rfl⟩ : syracuseStep 3805031 = 5707547) B5707547
theorem B3805175 : Blo 1780091 3805175 := bstep (se 1 (by rfl) ⟨2853881, by rfl⟩ : syracuseStep 3805175 = 5707763) B5707763
theorem B77042339 : Blo 1780091 77042339 := bstep (se 1 (by rfl) ⟨57781754, by rfl⟩ : syracuseStep 77042339 = 115563509) B115563509
theorem B219468527 : Blo 1780091 219468527 := bstep (se 1 (by rfl) ⟨164601395, by rfl⟩ : syracuseStep 219468527 = 329202791) B329202791
theorem B8557339 : Blo 1780091 8557339 := bstep (se 1 (by rfl) ⟨6418004, by rfl⟩ : syracuseStep 8557339 = 12836009) B12836009
theorem B14439545 : Blo 1780091 14439545 := bstep (se 2 (by rfl) ⟨5414829, by rfl⟩ : syracuseStep 14439545 = 10829659) B10829659
theorem B6010793 : Blo 1780091 6010793 := bstep (se 2 (by rfl) ⟨2254047, by rfl⟩ : syracuseStep 6010793 = 4508095) B4508095
theorem B33380363 : Blo 1780091 33380363 := bstep (se 1 (by rfl) ⟨25035272, by rfl⟩ : syracuseStep 33380363 = 50070545) B50070545
theorem B296532413 : Blo 1780091 296532413 := bstep (se 3 (by rfl) ⟨55599827, by rfl⟩ : syracuseStep 296532413 = 111199655) B111199655
theorem B125098505 : Blo 1780091 125098505 := bstep (se 2 (by rfl) ⟨46911939, by rfl⟩ : syracuseStep 125098505 = 93823879) B93823879
theorem B10975975 : Blo 1780091 10975975 := bstep (se 1 (by rfl) ⟨8231981, by rfl⟩ : syracuseStep 10975975 = 16463963) B16463963
theorem B3046607 : Blo 1780091 3046607 := bstep (se 1 (by rfl) ⟨2284955, by rfl⟩ : syracuseStep 3046607 = 4569911) B4569911
theorem B14442137 : Blo 1780091 14442137 := bstep (se 2 (by rfl) ⟨5415801, by rfl⟩ : syracuseStep 14442137 = 10831603) B10831603
theorem B2670683 : Blo 1780091 2670683 := bstep (se 1 (by rfl) ⟨2003012, by rfl⟩ : syracuseStep 2670683 = 4006025) B4006025
theorem B9626363 : Blo 1780091 9626363 := bstep (se 1 (by rfl) ⟨7219772, by rfl⟩ : syracuseStep 9626363 = 14439545) B14439545
theorem B34685759 : Blo 1780091 34685759 := bstep (se 1 (by rfl) ⟨26014319, by rfl⟩ : syracuseStep 34685759 = 52028639) B52028639
theorem B2671487 : Blo 1780091 2671487 := bstep (se 1 (by rfl) ⟨2003615, by rfl⟩ : syracuseStep 2671487 = 4007231) B4007231
theorem B6013979 : Blo 1780091 6013979 := bstep (se 1 (by rfl) ⟨4510484, by rfl⟩ : syracuseStep 6013979 = 9020969) B9020969
theorem B4007195 : Blo 1780091 4007195 := bstep (se 1 (by rfl) ⟨3005396, by rfl⟩ : syracuseStep 4007195 = 6010793) B6010793
theorem B2672639 : Blo 1780091 2672639 := bstep (se 1 (by rfl) ⟨2004479, by rfl⟩ : syracuseStep 2672639 = 4008959) B4008959
theorem B2672747 : Blo 1780091 2672747 := bstep (se 1 (by rfl) ⟨2004560, by rfl⟩ : syracuseStep 2672747 = 4009121) B4009121
theorem B2672807 : Blo 1780091 2672807 := bstep (se 1 (by rfl) ⟨2004605, by rfl⟩ : syracuseStep 2672807 = 4009211) B4009211
theorem B9628091 : Blo 1780091 9628091 := bstep (se 1 (by rfl) ⟨7221068, by rfl⟩ : syracuseStep 9628091 = 14442137) B14442137
theorem B17115907 : Blo 1780091 17115907 := bstep (se 1 (by rfl) ⟨12836930, by rfl⟩ : syracuseStep 17115907 = 25673861) B25673861
theorem B146312351 : Blo 1780091 146312351 := bstep (se 1 (by rfl) ⟨109734263, by rfl⟩ : syracuseStep 146312351 = 219468527) B219468527
theorem B1781183 : Blo 1780091 1781183 := bstep (se 1 (by rfl) ⟨1335887, by rfl⟩ : syracuseStep 1781183 = 2671775) B2671775
theorem B22253575 : Blo 1780091 22253575 := bstep (se 1 (by rfl) ⟨16690181, by rfl⟩ : syracuseStep 22253575 = 33380363) B33380363
theorem B83399003 : Blo 1780091 83399003 := bstep (se 1 (by rfl) ⟨62549252, by rfl⟩ : syracuseStep 83399003 = 125098505) B125098505
theorem B10138567 : Blo 1780091 10138567 := bstep (se 1 (by rfl) ⟨7603925, by rfl⟩ : syracuseStep 10138567 = 15207851) B15207851
theorem B2536687 : Blo 1780091 2536687 := bstep (se 1 (by rfl) ⟨1902515, by rfl⟩ : syracuseStep 2536687 = 3805031) B3805031
theorem B10147133 : Blo 1780091 10147133 := bstep (se 3 (by rfl) ⟨1902587, by rfl⟩ : syracuseStep 10147133 = 3805175) B3805175
theorem B51361559 : Blo 1780091 51361559 := bstep (se 1 (by rfl) ⟨38521169, by rfl⟩ : syracuseStep 51361559 = 77042339) B77042339
theorem B329128055 : Blo 1780091 329128055 := bstep (se 1 (by rfl) ⟨246846041, by rfl⟩ : syracuseStep 329128055 = 493692083) B493692083
theorem B11409785 : Blo 1780091 11409785 := bstep (se 2 (by rfl) ⟨4278669, by rfl⟩ : syracuseStep 11409785 = 8557339) B8557339
theorem B58538533 : Blo 1780091 58538533 := bstep (se 4 (by rfl) ⟨5487987, by rfl⟩ : syracuseStep 58538533 = 10975975) B10975975
theorem B197688275 : Blo 1780091 197688275 := bstep (se 1 (by rfl) ⟨148266206, by rfl⟩ : syracuseStep 197688275 = 296532413) B296532413
theorem B5070059 : Blo 1780091 5070059 := bstep (se 1 (by rfl) ⟨3802544, by rfl⟩ : syracuseStep 5070059 = 7605089) B7605089
theorem B2031071 : Blo 1780091 2031071 := bstep (se 1 (by rfl) ⟨1523303, by rfl⟩ : syracuseStep 2031071 = 3046607) B3046607
theorem B5070377 : Blo 1780091 5070377 := bstep (se 2 (by rfl) ⟨1901391, by rfl⟩ : syracuseStep 5070377 = 3802783) B3802783
theorem B2891519 : Blo 1780091 2891519 := bstep (se 1 (by rfl) ⟨2168639, by rfl⟩ : syracuseStep 2891519 = 4337279) B4337279
theorem B29671433 : Blo 1780091 29671433 := bstep (se 2 (by rfl) ⟨11126787, by rfl⟩ : syracuseStep 29671433 = 22253575) B22253575
theorem B55599335 : Blo 1780091 55599335 := bstep (se 1 (by rfl) ⟨41699501, by rfl⟩ : syracuseStep 55599335 = 83399003) B83399003
theorem B2671463 : Blo 1780091 2671463 := bstep (se 1 (by rfl) ⟨2003597, by rfl⟩ : syracuseStep 2671463 = 4007195) B4007195
theorem B5416189 : Blo 1780091 5416189 := bstep (se 3 (by rfl) ⟨1015535, by rfl⟩ : syracuseStep 5416189 = 2031071) B2031071
theorem B13518089 : Blo 1780091 13518089 := bstep (se 2 (by rfl) ⟨5069283, by rfl⟩ : syracuseStep 13518089 = 10138567) B10138567
theorem B1780455 : Blo 1780091 1780455 := bstep (se 1 (by rfl) ⟨1335341, by rfl⟩ : syracuseStep 1780455 = 2670683) B2670683
theorem B6417575 : Blo 1780091 6417575 := bstep (se 1 (by rfl) ⟨4813181, by rfl⟩ : syracuseStep 6417575 = 9626363) B9626363
theorem B1780991 : Blo 1780091 1780991 := bstep (se 1 (by rfl) ⟨1335743, by rfl⟩ : syracuseStep 1780991 = 2671487) B2671487
theorem B4009319 : Blo 1780091 4009319 := bstep (se 1 (by rfl) ⟨3006989, by rfl⟩ : syracuseStep 4009319 = 6013979) B6013979
theorem B1781759 : Blo 1780091 1781759 := bstep (se 1 (by rfl) ⟨1336319, by rfl⟩ : syracuseStep 1781759 = 2672639) B2672639
theorem B1781831 : Blo 1780091 1781831 := bstep (se 1 (by rfl) ⟨1336373, by rfl⟩ : syracuseStep 1781831 = 2672747) B2672747
theorem B219418703 : Blo 1780091 219418703 := bstep (se 1 (by rfl) ⟨164564027, by rfl⟩ : syracuseStep 219418703 = 329128055) B329128055
theorem B13521005 : Blo 1780091 13521005 := bstep (se 3 (by rfl) ⟨2535188, by rfl⟩ : syracuseStep 13521005 = 5070377) B5070377
theorem B1781871 : Blo 1780091 1781871 := bstep (se 1 (by rfl) ⟨1336403, by rfl⟩ : syracuseStep 1781871 = 2672807) B2672807
theorem B7606523 : Blo 1780091 7606523 := bstep (se 1 (by rfl) ⟨5704892, by rfl⟩ : syracuseStep 7606523 = 11409785) B11409785
theorem B6418727 : Blo 1780091 6418727 := bstep (se 1 (by rfl) ⟨4814045, by rfl⟩ : syracuseStep 6418727 = 9628091) B9628091
theorem B3380039 : Blo 1780091 3380039 := bstep (se 1 (by rfl) ⟨2535029, by rfl⟩ : syracuseStep 3380039 = 5070059) B5070059
theorem B23123839 : Blo 1780091 23123839 := bstep (se 1 (by rfl) ⟨17342879, by rfl⟩ : syracuseStep 23123839 = 34685759) B34685759
theorem B78051377 : Blo 1780091 78051377 := bstep (se 2 (by rfl) ⟨29269266, by rfl⟩ : syracuseStep 78051377 = 58538533) B58538533
theorem B6764755 : Blo 1780091 6764755 := bstep (se 1 (by rfl) ⟨5073566, by rfl⟩ : syracuseStep 6764755 = 10147133) B10147133
theorem B22821209 : Blo 1780091 22821209 := bstep (se 2 (by rfl) ⟨8557953, by rfl⟩ : syracuseStep 22821209 = 17115907) B17115907
theorem B34241039 : Blo 1780091 34241039 := bstep (se 1 (by rfl) ⟨25680779, by rfl⟩ : syracuseStep 34241039 = 51361559) B51361559
theorem B3382249 : Blo 1780091 3382249 := bstep (se 2 (by rfl) ⟨1268343, by rfl⟩ : syracuseStep 3382249 = 2536687) B2536687
theorem B131792183 : Blo 1780091 131792183 := bstep (se 1 (by rfl) ⟨98844137, by rfl⟩ : syracuseStep 131792183 = 197688275) B197688275
theorem B97541567 : Blo 1780091 97541567 := bstep (se 1 (by rfl) ⟨73156175, by rfl⟩ : syracuseStep 97541567 = 146312351) B146312351
theorem B30842869 : Blo 1780091 30842869 := bstep (se 5 (by rfl) ⟨1445759, by rfl⟩ : syracuseStep 30842869 = 2891519) B2891519
theorem B5071015 : Blo 1780091 5071015 := bstep (se 1 (by rfl) ⟨3803261, by rfl⟩ : syracuseStep 5071015 = 7606523) B7606523
theorem B9019673 : Blo 1780091 9019673 := bstep (se 2 (by rfl) ⟨3382377, by rfl⟩ : syracuseStep 9019673 = 6764755) B6764755
theorem B2253359 : Blo 1780091 2253359 := bstep (se 1 (by rfl) ⟨1690019, by rfl⟩ : syracuseStep 2253359 = 3380039) B3380039
theorem B9012059 : Blo 1780091 9012059 := bstep (se 1 (by rfl) ⟨6759044, by rfl⟩ : syracuseStep 9012059 = 13518089) B13518089
theorem B28886341 : Blo 1780091 28886341 := bstep (se 4 (by rfl) ⟨2708094, by rfl⟩ : syracuseStep 28886341 = 5416189) B5416189
theorem B15214139 : Blo 1780091 15214139 := bstep (se 1 (by rfl) ⟨11410604, by rfl⟩ : syracuseStep 15214139 = 22821209) B22821209
theorem B4278383 : Blo 1780091 4278383 := bstep (se 1 (by rfl) ⟨3208787, by rfl⟩ : syracuseStep 4278383 = 6417575) B6417575
theorem B87861455 : Blo 1780091 87861455 := bstep (se 1 (by rfl) ⟨65896091, by rfl⟩ : syracuseStep 87861455 = 131792183) B131792183
theorem B2672879 : Blo 1780091 2672879 := bstep (se 1 (by rfl) ⟨2004659, by rfl⟩ : syracuseStep 2672879 = 4009319) B4009319
theorem B146279135 : Blo 1780091 146279135 := bstep (se 1 (by rfl) ⟨109709351, by rfl⟩ : syracuseStep 146279135 = 219418703) B219418703
theorem B9014003 : Blo 1780091 9014003 := bstep (se 1 (by rfl) ⟨6760502, by rfl⟩ : syracuseStep 9014003 = 13521005) B13521005
theorem B4279151 : Blo 1780091 4279151 := bstep (se 1 (by rfl) ⟨3209363, by rfl⟩ : syracuseStep 4279151 = 6418727) B6418727
theorem B1780975 : Blo 1780091 1780975 := bstep (se 1 (by rfl) ⟨1335731, by rfl⟩ : syracuseStep 1780975 = 2671463) B2671463
theorem B4509665 : Blo 1780091 4509665 := bstep (se 2 (by rfl) ⟨1691124, by rfl⟩ : syracuseStep 4509665 = 3382249) B3382249
theorem B22827359 : Blo 1780091 22827359 := bstep (se 1 (by rfl) ⟨17120519, by rfl⟩ : syracuseStep 22827359 = 34241039) B34241039
theorem B30831785 : Blo 1780091 30831785 := bstep (se 2 (by rfl) ⟨11561919, by rfl⟩ : syracuseStep 30831785 = 23123839) B23123839
theorem B19780955 : Blo 1780091 19780955 := bstep (se 1 (by rfl) ⟨14835716, by rfl⟩ : syracuseStep 19780955 = 29671433) B29671433
theorem B37066223 : Blo 1780091 37066223 := bstep (se 1 (by rfl) ⟨27799667, by rfl⟩ : syracuseStep 37066223 = 55599335) B55599335
theorem B52034251 : Blo 1780091 52034251 := bstep (se 1 (by rfl) ⟨39025688, by rfl⟩ : syracuseStep 52034251 = 78051377) B78051377
theorem B65027711 : Blo 1780091 65027711 := bstep (se 1 (by rfl) ⟨48770783, by rfl⟩ : syracuseStep 65027711 = 97541567) B97541567
theorem B41123825 : Blo 1780091 41123825 := bstep (se 2 (by rfl) ⟨15421434, by rfl⟩ : syracuseStep 41123825 = 30842869) B30842869
theorem B6013115 : Blo 1780091 6013115 := bstep (se 1 (by rfl) ⟨4509836, by rfl⟩ : syracuseStep 6013115 = 9019673) B9019673
theorem B20554523 : Blo 1780091 20554523 := bstep (se 1 (by rfl) ⟨15415892, by rfl⟩ : syracuseStep 20554523 = 30831785) B30831785
theorem B69379001 : Blo 1780091 69379001 := bstep (se 2 (by rfl) ⟨26017125, by rfl⟩ : syracuseStep 69379001 = 52034251) B52034251
theorem B10142759 : Blo 1780091 10142759 := bstep (se 1 (by rfl) ⟨7607069, by rfl⟩ : syracuseStep 10142759 = 15214139) B15214139
theorem B2852255 : Blo 1780091 2852255 := bstep (se 1 (by rfl) ⟨2139191, by rfl⟩ : syracuseStep 2852255 = 4278383) B4278383
theorem B58574303 : Blo 1780091 58574303 := bstep (se 1 (by rfl) ⟨43930727, by rfl⟩ : syracuseStep 58574303 = 87861455) B87861455
theorem B2852767 : Blo 1780091 2852767 := bstep (se 1 (by rfl) ⟨2139575, by rfl⟩ : syracuseStep 2852767 = 4279151) B4279151
theorem B6761353 : Blo 1780091 6761353 := bstep (se 2 (by rfl) ⟨2535507, by rfl⟩ : syracuseStep 6761353 = 5071015) B5071015
theorem B6008039 : Blo 1780091 6008039 := bstep (se 1 (by rfl) ⟨4506029, by rfl⟩ : syracuseStep 6008039 = 9012059) B9012059
theorem B24710815 : Blo 1780091 24710815 := bstep (se 1 (by rfl) ⟨18533111, by rfl⟩ : syracuseStep 24710815 = 37066223) B37066223
theorem B6008957 : Blo 1780091 6008957 := bstep (se 3 (by rfl) ⟨1126679, by rfl⟩ : syracuseStep 6008957 = 2253359) B2253359
theorem B1781919 : Blo 1780091 1781919 := bstep (se 1 (by rfl) ⟨1336439, by rfl⟩ : syracuseStep 1781919 = 2672879) B2672879
theorem B38515121 : Blo 1780091 38515121 := bstep (se 2 (by rfl) ⟨14443170, by rfl⟩ : syracuseStep 38515121 = 28886341) B28886341
theorem B6009335 : Blo 1780091 6009335 := bstep (se 1 (by rfl) ⟨4507001, by rfl⟩ : syracuseStep 6009335 = 9014003) B9014003
theorem B27415883 : Blo 1780091 27415883 := bstep (se 1 (by rfl) ⟨20561912, by rfl⟩ : syracuseStep 27415883 = 41123825) B41123825
theorem B15218239 : Blo 1780091 15218239 := bstep (se 1 (by rfl) ⟨11413679, by rfl⟩ : syracuseStep 15218239 = 22827359) B22827359
theorem B13187303 : Blo 1780091 13187303 := bstep (se 1 (by rfl) ⟨9890477, by rfl⟩ : syracuseStep 13187303 = 19780955) B19780955
theorem B390077693 : Blo 1780091 390077693 := bstep (se 3 (by rfl) ⟨73139567, by rfl⟩ : syracuseStep 390077693 = 146279135) B146279135
theorem B43351807 : Blo 1780091 43351807 := bstep (se 1 (by rfl) ⟨32513855, by rfl⟩ : syracuseStep 43351807 = 65027711) B65027711
theorem B3006443 : Blo 1780091 3006443 := bstep (se 1 (by rfl) ⟨2254832, by rfl⟩ : syracuseStep 3006443 = 4509665) B4509665
theorem B4005971 : Blo 1780091 4005971 := bstep (se 1 (by rfl) ⟨3004478, by rfl⟩ : syracuseStep 4005971 = 6008957) B6008957
theorem B4006223 : Blo 1780091 4006223 := bstep (se 1 (by rfl) ⟨3004667, by rfl⟩ : syracuseStep 4006223 = 6009335) B6009335
theorem B46252667 : Blo 1780091 46252667 := bstep (se 1 (by rfl) ⟨34689500, by rfl⟩ : syracuseStep 46252667 = 69379001) B69379001
theorem B18277255 : Blo 1780091 18277255 := bstep (se 1 (by rfl) ⟨13707941, by rfl⟩ : syracuseStep 18277255 = 27415883) B27415883
theorem B1901503 : Blo 1780091 1901503 := bstep (se 1 (by rfl) ⟨1426127, by rfl⟩ : syracuseStep 1901503 = 2852255) B2852255
theorem B8791535 : Blo 1780091 8791535 := bstep (se 1 (by rfl) ⟨6593651, by rfl⟩ : syracuseStep 8791535 = 13187303) B13187303
theorem B3803689 : Blo 1780091 3803689 := bstep (se 2 (by rfl) ⟨1426383, by rfl⟩ : syracuseStep 3803689 = 2852767) B2852767
theorem B4008743 : Blo 1780091 4008743 := bstep (se 1 (by rfl) ⟨3006557, by rfl⟩ : syracuseStep 4008743 = 6013115) B6013115
theorem B25676747 : Blo 1780091 25676747 := bstep (se 1 (by rfl) ⟨19257560, by rfl⟩ : syracuseStep 25676747 = 38515121) B38515121
theorem B6761839 : Blo 1780091 6761839 := bstep (se 1 (by rfl) ⟨5071379, by rfl⟩ : syracuseStep 6761839 = 10142759) B10142759
theorem B9015137 : Blo 1780091 9015137 := bstep (se 2 (by rfl) ⟨3380676, by rfl⟩ : syracuseStep 9015137 = 6761353) B6761353
theorem B260051795 : Blo 1780091 260051795 := bstep (se 1 (by rfl) ⟨195038846, by rfl⟩ : syracuseStep 260051795 = 390077693) B390077693
theorem B2004295 : Blo 1780091 2004295 := bstep (se 1 (by rfl) ⟨1503221, by rfl⟩ : syracuseStep 2004295 = 3006443) B3006443
theorem B13703015 : Blo 1780091 13703015 := bstep (se 1 (by rfl) ⟨10277261, by rfl⟩ : syracuseStep 13703015 = 20554523) B20554523
theorem B131791013 : Blo 1780091 131791013 := bstep (se 4 (by rfl) ⟨12355407, by rfl⟩ : syracuseStep 131791013 = 24710815) B24710815
theorem B39049535 : Blo 1780091 39049535 := bstep (se 1 (by rfl) ⟨29287151, by rfl⟩ : syracuseStep 39049535 = 58574303) B58574303
theorem B20290985 : Blo 1780091 20290985 := bstep (se 2 (by rfl) ⟨7609119, by rfl⟩ : syracuseStep 20290985 = 15218239) B15218239
theorem B4005359 : Blo 1780091 4005359 := bstep (se 1 (by rfl) ⟨3004019, by rfl⟩ : syracuseStep 4005359 = 6008039) B6008039
theorem B57802409 : Blo 1780091 57802409 := bstep (se 2 (by rfl) ⟨21675903, by rfl⟩ : syracuseStep 57802409 = 43351807) B43351807
theorem B2670647 : Blo 1780091 2670647 := bstep (se 1 (by rfl) ⟨2002985, by rfl⟩ : syracuseStep 2670647 = 4005971) B4005971
theorem B2670815 : Blo 1780091 2670815 := bstep (se 1 (by rfl) ⟨2003111, by rfl⟩ : syracuseStep 2670815 = 4006223) B4006223
theorem B173367863 : Blo 1780091 173367863 := bstep (se 1 (by rfl) ⟨130025897, by rfl⟩ : syracuseStep 173367863 = 260051795) B260051795
theorem B5071585 : Blo 1780091 5071585 := bstep (se 2 (by rfl) ⟨1901844, by rfl⟩ : syracuseStep 5071585 = 3803689) B3803689
theorem B9135343 : Blo 1780091 9135343 := bstep (se 1 (by rfl) ⟨6851507, by rfl⟩ : syracuseStep 9135343 = 13703015) B13703015
theorem B87860675 : Blo 1780091 87860675 := bstep (se 1 (by rfl) ⟨65895506, by rfl⟩ : syracuseStep 87860675 = 131791013) B131791013
theorem B123340445 : Blo 1780091 123340445 := bstep (se 3 (by rfl) ⟨23126333, by rfl⟩ : syracuseStep 123340445 = 46252667) B46252667
theorem B2672393 : Blo 1780091 2672393 := bstep (se 2 (by rfl) ⟨1002147, by rfl⟩ : syracuseStep 2672393 = 2004295) B2004295
theorem B2672495 : Blo 1780091 2672495 := bstep (se 1 (by rfl) ⟨2004371, by rfl⟩ : syracuseStep 2672495 = 4008743) B4008743
theorem B13527323 : Blo 1780091 13527323 := bstep (se 1 (by rfl) ⟨10145492, by rfl⟩ : syracuseStep 13527323 = 20290985) B20290985
theorem B2535337 : Blo 1780091 2535337 := bstep (se 2 (by rfl) ⟨950751, by rfl⟩ : syracuseStep 2535337 = 1901503) B1901503
theorem B9015785 : Blo 1780091 9015785 := bstep (se 2 (by rfl) ⟨3380919, by rfl⟩ : syracuseStep 9015785 = 6761839) B6761839
theorem B17117831 : Blo 1780091 17117831 := bstep (se 1 (by rfl) ⟨12838373, by rfl⟩ : syracuseStep 17117831 = 25676747) B25676747
theorem B6010091 : Blo 1780091 6010091 := bstep (se 1 (by rfl) ⟨4507568, by rfl⟩ : syracuseStep 6010091 = 9015137) B9015137
theorem B24369673 : Blo 1780091 24369673 := bstep (se 2 (by rfl) ⟨9138627, by rfl⟩ : syracuseStep 24369673 = 18277255) B18277255
theorem B23444093 : Blo 1780091 23444093 := bstep (se 3 (by rfl) ⟨4395767, by rfl⟩ : syracuseStep 23444093 = 8791535) B8791535
theorem B26033023 : Blo 1780091 26033023 := bstep (se 1 (by rfl) ⟨19524767, by rfl⟩ : syracuseStep 26033023 = 39049535) B39049535
theorem B2670239 : Blo 1780091 2670239 := bstep (se 1 (by rfl) ⟨2002679, by rfl⟩ : syracuseStep 2670239 = 4005359) B4005359
theorem B38534939 : Blo 1780091 38534939 := bstep (se 1 (by rfl) ⟨28901204, by rfl⟩ : syracuseStep 38534939 = 57802409) B57802409
theorem B11411887 : Blo 1780091 11411887 := bstep (se 1 (by rfl) ⟨8558915, by rfl⟩ : syracuseStep 11411887 = 17117831) B17117831
theorem B4006727 : Blo 1780091 4006727 := bstep (se 1 (by rfl) ⟨3005045, by rfl⟩ : syracuseStep 4006727 = 6010091) B6010091
theorem B58573783 : Blo 1780091 58573783 := bstep (se 1 (by rfl) ⟨43930337, by rfl⟩ : syracuseStep 58573783 = 87860675) B87860675
theorem B34710697 : Blo 1780091 34710697 := bstep (se 2 (by rfl) ⟨13016511, by rfl⟩ : syracuseStep 34710697 = 26033023) B26033023
theorem B1780159 : Blo 1780091 1780159 := bstep (se 1 (by rfl) ⟨1335119, by rfl⟩ : syracuseStep 1780159 = 2670239) B2670239
theorem B1780431 : Blo 1780091 1780431 := bstep (se 1 (by rfl) ⟨1335323, by rfl⟩ : syracuseStep 1780431 = 2670647) B2670647
theorem B1780543 : Blo 1780091 1780543 := bstep (se 1 (by rfl) ⟨1335407, by rfl⟩ : syracuseStep 1780543 = 2670815) B2670815
theorem B32492897 : Blo 1780091 32492897 := bstep (se 2 (by rfl) ⟨12184836, by rfl⟩ : syracuseStep 32492897 = 24369673) B24369673
theorem B6762113 : Blo 1780091 6762113 := bstep (se 2 (by rfl) ⟨2535792, by rfl⟩ : syracuseStep 6762113 = 5071585) B5071585
theorem B82226963 : Blo 1780091 82226963 := bstep (se 1 (by rfl) ⟨61670222, by rfl⟩ : syracuseStep 82226963 = 123340445) B123340445
theorem B1781595 : Blo 1780091 1781595 := bstep (se 1 (by rfl) ⟨1336196, by rfl⟩ : syracuseStep 1781595 = 2672393) B2672393
theorem B1781663 : Blo 1780091 1781663 := bstep (se 1 (by rfl) ⟨1336247, by rfl⟩ : syracuseStep 1781663 = 2672495) B2672495
theorem B3380449 : Blo 1780091 3380449 := bstep (se 2 (by rfl) ⟨1267668, by rfl⟩ : syracuseStep 3380449 = 2535337) B2535337
theorem B6010523 : Blo 1780091 6010523 := bstep (se 1 (by rfl) ⟨4507892, by rfl⟩ : syracuseStep 6010523 = 9015785) B9015785
theorem B115578575 : Blo 1780091 115578575 := bstep (se 1 (by rfl) ⟨86683931, by rfl⟩ : syracuseStep 115578575 = 173367863) B173367863
theorem B9018215 : Blo 1780091 9018215 := bstep (se 1 (by rfl) ⟨6763661, by rfl⟩ : syracuseStep 9018215 = 13527323) B13527323
theorem B12180457 : Blo 1780091 12180457 := bstep (se 2 (by rfl) ⟨4567671, by rfl⟩ : syracuseStep 12180457 = 9135343) B9135343
theorem B15629395 : Blo 1780091 15629395 := bstep (se 1 (by rfl) ⟨11722046, by rfl⟩ : syracuseStep 15629395 = 23444093) B23444093
theorem B25689959 : Blo 1780091 25689959 := bstep (se 1 (by rfl) ⟨19267469, by rfl⟩ : syracuseStep 25689959 = 38534939) B38534939
theorem B2671151 : Blo 1780091 2671151 := bstep (se 1 (by rfl) ⟨2003363, by rfl⟩ : syracuseStep 2671151 = 4006727) B4006727
theorem B4007015 : Blo 1780091 4007015 := bstep (se 1 (by rfl) ⟨3005261, by rfl⟩ : syracuseStep 4007015 = 6010523) B6010523
theorem B4507265 : Blo 1780091 4507265 := bstep (se 2 (by rfl) ⟨1690224, by rfl⟩ : syracuseStep 4507265 = 3380449) B3380449
theorem B21661931 : Blo 1780091 21661931 := bstep (se 1 (by rfl) ⟨16246448, by rfl⟩ : syracuseStep 21661931 = 32492897) B32492897
theorem B4508075 : Blo 1780091 4508075 := bstep (se 1 (by rfl) ⟨3381056, by rfl⟩ : syracuseStep 4508075 = 6762113) B6762113
theorem B15215849 : Blo 1780091 15215849 := bstep (se 2 (by rfl) ⟨5705943, by rfl⟩ : syracuseStep 15215849 = 11411887) B11411887
theorem B16240609 : Blo 1780091 16240609 := bstep (se 2 (by rfl) ⟨6090228, by rfl⟩ : syracuseStep 16240609 = 12180457) B12180457
theorem B46280929 : Blo 1780091 46280929 := bstep (se 2 (by rfl) ⟨17355348, by rfl⟩ : syracuseStep 46280929 = 34710697) B34710697
theorem B54817975 : Blo 1780091 54817975 := bstep (se 1 (by rfl) ⟨41113481, by rfl⟩ : syracuseStep 54817975 = 82226963) B82226963
theorem B17126639 : Blo 1780091 17126639 := bstep (se 1 (by rfl) ⟨12844979, by rfl⟩ : syracuseStep 17126639 = 25689959) B25689959
theorem B77052383 : Blo 1780091 77052383 := bstep (se 1 (by rfl) ⟨57789287, by rfl⟩ : syracuseStep 77052383 = 115578575) B115578575
theorem B20839193 : Blo 1780091 20839193 := bstep (se 2 (by rfl) ⟨7814697, by rfl⟩ : syracuseStep 20839193 = 15629395) B15629395
theorem B6012143 : Blo 1780091 6012143 := bstep (se 1 (by rfl) ⟨4509107, by rfl⟩ : syracuseStep 6012143 = 9018215) B9018215
theorem B312393509 : Blo 1780091 312393509 := bstep (se 4 (by rfl) ⟨29286891, by rfl⟩ : syracuseStep 312393509 = 58573783) B58573783
theorem B2671343 : Blo 1780091 2671343 := bstep (se 1 (by rfl) ⟨2003507, by rfl⟩ : syracuseStep 2671343 = 4007015) B4007015
theorem B73090633 : Blo 1780091 73090633 := bstep (se 2 (by rfl) ⟨27408987, by rfl⟩ : syracuseStep 73090633 = 54817975) B54817975
theorem B10143899 : Blo 1780091 10143899 := bstep (se 1 (by rfl) ⟨7607924, by rfl⟩ : syracuseStep 10143899 = 15215849) B15215849
theorem B4008095 : Blo 1780091 4008095 := bstep (se 1 (by rfl) ⟨3006071, by rfl⟩ : syracuseStep 4008095 = 6012143) B6012143
theorem B21654145 : Blo 1780091 21654145 := bstep (se 2 (by rfl) ⟨8120304, by rfl⟩ : syracuseStep 21654145 = 16240609) B16240609
theorem B1780767 : Blo 1780091 1780767 := bstep (se 1 (by rfl) ⟨1335575, by rfl⟩ : syracuseStep 1780767 = 2671151) B2671151
theorem B57765149 : Blo 1780091 57765149 := bstep (se 3 (by rfl) ⟨10830965, by rfl⟩ : syracuseStep 57765149 = 21661931) B21661931
theorem B51368255 : Blo 1780091 51368255 := bstep (se 1 (by rfl) ⟨38526191, by rfl⟩ : syracuseStep 51368255 = 77052383) B77052383
theorem B208262339 : Blo 1780091 208262339 := bstep (se 1 (by rfl) ⟨156196754, by rfl⟩ : syracuseStep 208262339 = 312393509) B312393509
theorem B61707905 : Blo 1780091 61707905 := bstep (se 2 (by rfl) ⟨23140464, by rfl⟩ : syracuseStep 61707905 = 46280929) B46280929
theorem B11417759 : Blo 1780091 11417759 := bstep (se 1 (by rfl) ⟨8563319, by rfl⟩ : syracuseStep 11417759 = 17126639) B17126639
theorem B3004843 : Blo 1780091 3004843 := bstep (se 1 (by rfl) ⟨2253632, by rfl⟩ : syracuseStep 3004843 = 4507265) B4507265
theorem B3005383 : Blo 1780091 3005383 := bstep (se 1 (by rfl) ⟨2254037, by rfl⟩ : syracuseStep 3005383 = 4508075) B4508075
theorem B13892795 : Blo 1780091 13892795 := bstep (se 1 (by rfl) ⟨10419596, by rfl⟩ : syracuseStep 13892795 = 20839193) B20839193
theorem B4006457 : Blo 1780091 4006457 := bstep (se 2 (by rfl) ⟨1502421, by rfl⟩ : syracuseStep 4006457 = 3004843) B3004843
theorem B4007177 : Blo 1780091 4007177 := bstep (se 2 (by rfl) ⟨1502691, by rfl⟩ : syracuseStep 4007177 = 3005383) B3005383
theorem B2672063 : Blo 1780091 2672063 := bstep (se 1 (by rfl) ⟨2004047, by rfl⟩ : syracuseStep 2672063 = 4008095) B4008095
theorem B7611839 : Blo 1780091 7611839 := bstep (se 1 (by rfl) ⟨5708879, by rfl⟩ : syracuseStep 7611839 = 11417759) B11417759
theorem B97454177 : Blo 1780091 97454177 := bstep (se 2 (by rfl) ⟨36545316, by rfl⟩ : syracuseStep 97454177 = 73090633) B73090633
theorem B34245503 : Blo 1780091 34245503 := bstep (se 1 (by rfl) ⟨25684127, by rfl⟩ : syracuseStep 34245503 = 51368255) B51368255
theorem B1780895 : Blo 1780091 1780895 := bstep (se 1 (by rfl) ⟨1335671, by rfl⟩ : syracuseStep 1780895 = 2671343) B2671343
theorem B138841559 : Blo 1780091 138841559 := bstep (se 1 (by rfl) ⟨104131169, by rfl⟩ : syracuseStep 138841559 = 208262339) B208262339
theorem B6762599 : Blo 1780091 6762599 := bstep (se 1 (by rfl) ⟨5071949, by rfl⟩ : syracuseStep 6762599 = 10143899) B10143899
theorem B9261863 : Blo 1780091 9261863 := bstep (se 1 (by rfl) ⟨6946397, by rfl⟩ : syracuseStep 9261863 = 13892795) B13892795
theorem B115488773 : Blo 1780091 115488773 := bstep (se 4 (by rfl) ⟨10827072, by rfl⟩ : syracuseStep 115488773 = 21654145) B21654145
theorem B41138603 : Blo 1780091 41138603 := bstep (se 1 (by rfl) ⟨30853952, by rfl⟩ : syracuseStep 41138603 = 61707905) B61707905
theorem B38510099 : Blo 1780091 38510099 := bstep (se 1 (by rfl) ⟨28882574, by rfl⟩ : syracuseStep 38510099 = 57765149) B57765149
theorem B2670971 : Blo 1780091 2670971 := bstep (se 1 (by rfl) ⟨2003228, by rfl⟩ : syracuseStep 2670971 = 4006457) B4006457
theorem B2671451 : Blo 1780091 2671451 := bstep (se 1 (by rfl) ⟨2003588, by rfl⟩ : syracuseStep 2671451 = 4007177) B4007177
theorem B4508399 : Blo 1780091 4508399 := bstep (se 1 (by rfl) ⟨3381299, by rfl⟩ : syracuseStep 4508399 = 6762599) B6762599
theorem B1781375 : Blo 1780091 1781375 := bstep (se 1 (by rfl) ⟨1336031, by rfl⟩ : syracuseStep 1781375 = 2672063) B2672063
theorem B5074559 : Blo 1780091 5074559 := bstep (se 1 (by rfl) ⟨3805919, by rfl⟩ : syracuseStep 5074559 = 7611839) B7611839
theorem B76992515 : Blo 1780091 76992515 := bstep (se 1 (by rfl) ⟨57744386, by rfl⟩ : syracuseStep 76992515 = 115488773) B115488773
theorem B6174575 : Blo 1780091 6174575 := bstep (se 1 (by rfl) ⟨4630931, by rfl⟩ : syracuseStep 6174575 = 9261863) B9261863
theorem B64969451 : Blo 1780091 64969451 := bstep (se 1 (by rfl) ⟨48727088, by rfl⟩ : syracuseStep 64969451 = 97454177) B97454177
theorem B27425735 : Blo 1780091 27425735 := bstep (se 1 (by rfl) ⟨20569301, by rfl⟩ : syracuseStep 27425735 = 41138603) B41138603
theorem B22830335 : Blo 1780091 22830335 := bstep (se 1 (by rfl) ⟨17122751, by rfl⟩ : syracuseStep 22830335 = 34245503) B34245503
theorem B92561039 : Blo 1780091 92561039 := bstep (se 1 (by rfl) ⟨69420779, by rfl⟩ : syracuseStep 92561039 = 138841559) B138841559
theorem B25673399 : Blo 1780091 25673399 := bstep (se 1 (by rfl) ⟨19255049, by rfl⟩ : syracuseStep 25673399 = 38510099) B38510099
theorem B43312967 : Blo 1780091 43312967 := bstep (se 1 (by rfl) ⟨32484725, by rfl⟩ : syracuseStep 43312967 = 64969451) B64969451
theorem B17115599 : Blo 1780091 17115599 := bstep (se 1 (by rfl) ⟨12836699, by rfl⟩ : syracuseStep 17115599 = 25673399) B25673399
theorem B1780647 : Blo 1780091 1780647 := bstep (se 1 (by rfl) ⟨1335485, by rfl⟩ : syracuseStep 1780647 = 2670971) B2670971
theorem B1780967 : Blo 1780091 1780967 := bstep (se 1 (by rfl) ⟨1335725, by rfl⟩ : syracuseStep 1780967 = 2671451) B2671451
theorem B4116383 : Blo 1780091 4116383 := bstep (se 1 (by rfl) ⟨3087287, by rfl⟩ : syracuseStep 4116383 = 6174575) B6174575
theorem B61707359 : Blo 1780091 61707359 := bstep (se 1 (by rfl) ⟨46280519, by rfl⟩ : syracuseStep 61707359 = 92561039) B92561039
theorem B51328343 : Blo 1780091 51328343 := bstep (se 1 (by rfl) ⟨38496257, by rfl⟩ : syracuseStep 51328343 = 76992515) B76992515
theorem B3005599 : Blo 1780091 3005599 := bstep (se 1 (by rfl) ⟨2254199, by rfl⟩ : syracuseStep 3005599 = 4508399) B4508399
theorem B18283823 : Blo 1780091 18283823 := bstep (se 1 (by rfl) ⟨13712867, by rfl⟩ : syracuseStep 18283823 = 27425735) B27425735
theorem B15220223 : Blo 1780091 15220223 := bstep (se 1 (by rfl) ⟨11415167, by rfl⟩ : syracuseStep 15220223 = 22830335) B22830335
theorem B3383039 : Blo 1780091 3383039 := bstep (se 1 (by rfl) ⟨2537279, by rfl⟩ : syracuseStep 3383039 = 5074559) B5074559
theorem B164552957 : Blo 1780091 164552957 := bstep (se 3 (by rfl) ⟨30853679, by rfl⟩ : syracuseStep 164552957 = 61707359) B61707359
theorem B34218895 : Blo 1780091 34218895 := bstep (se 1 (by rfl) ⟨25664171, by rfl⟩ : syracuseStep 34218895 = 51328343) B51328343
theorem B4007465 : Blo 1780091 4007465 := bstep (se 2 (by rfl) ⟨1502799, by rfl⟩ : syracuseStep 4007465 = 3005599) B3005599
theorem B2255359 : Blo 1780091 2255359 := bstep (se 1 (by rfl) ⟨1691519, by rfl⟩ : syracuseStep 2255359 = 3383039) B3383039
theorem B10146815 : Blo 1780091 10146815 := bstep (se 1 (by rfl) ⟨7610111, by rfl⟩ : syracuseStep 10146815 = 15220223) B15220223
theorem B28875311 : Blo 1780091 28875311 := bstep (se 1 (by rfl) ⟨21656483, by rfl⟩ : syracuseStep 28875311 = 43312967) B43312967
theorem B11410399 : Blo 1780091 11410399 := bstep (se 1 (by rfl) ⟨8557799, by rfl⟩ : syracuseStep 11410399 = 17115599) B17115599
theorem B12189215 : Blo 1780091 12189215 := bstep (se 1 (by rfl) ⟨9141911, by rfl⟩ : syracuseStep 12189215 = 18283823) B18283823
theorem B2744255 : Blo 1780091 2744255 := bstep (se 1 (by rfl) ⟨2058191, by rfl⟩ : syracuseStep 2744255 = 4116383) B4116383
theorem B3007145 : Blo 1780091 3007145 := bstep (se 2 (by rfl) ⟨1127679, by rfl⟩ : syracuseStep 3007145 = 2255359) B2255359
theorem B2671643 : Blo 1780091 2671643 := bstep (se 1 (by rfl) ⟨2003732, by rfl⟩ : syracuseStep 2671643 = 4007465) B4007465
theorem B15213865 : Blo 1780091 15213865 := bstep (se 2 (by rfl) ⟨5705199, by rfl⟩ : syracuseStep 15213865 = 11410399) B11410399
theorem B1829503 : Blo 1780091 1829503 := bstep (se 1 (by rfl) ⟨1372127, by rfl⟩ : syracuseStep 1829503 = 2744255) B2744255
theorem B109701971 : Blo 1780091 109701971 := bstep (se 1 (by rfl) ⟨82276478, by rfl⟩ : syracuseStep 109701971 = 164552957) B164552957
theorem B45625193 : Blo 1780091 45625193 := bstep (se 2 (by rfl) ⟨17109447, by rfl⟩ : syracuseStep 45625193 = 34218895) B34218895
theorem B6764543 : Blo 1780091 6764543 := bstep (se 1 (by rfl) ⟨5073407, by rfl⟩ : syracuseStep 6764543 = 10146815) B10146815
theorem B32504573 : Blo 1780091 32504573 := bstep (se 3 (by rfl) ⟨6094607, by rfl⟩ : syracuseStep 32504573 = 12189215) B12189215
theorem B19250207 : Blo 1780091 19250207 := bstep (se 1 (by rfl) ⟨14437655, by rfl⟩ : syracuseStep 19250207 = 28875311) B28875311
theorem B20285153 : Blo 1780091 20285153 := bstep (se 2 (by rfl) ⟨7606932, by rfl⟩ : syracuseStep 20285153 = 15213865) B15213865
theorem B21669715 : Blo 1780091 21669715 := bstep (se 1 (by rfl) ⟨16252286, by rfl⟩ : syracuseStep 21669715 = 32504573) B32504573
theorem B1781095 : Blo 1780091 1781095 := bstep (se 1 (by rfl) ⟨1335821, by rfl⟩ : syracuseStep 1781095 = 2671643) B2671643
theorem B4509695 : Blo 1780091 4509695 := bstep (se 1 (by rfl) ⟨3382271, by rfl⟩ : syracuseStep 4509695 = 6764543) B6764543
theorem B73134647 : Blo 1780091 73134647 := bstep (se 1 (by rfl) ⟨54850985, by rfl⟩ : syracuseStep 73134647 = 109701971) B109701971
theorem B12833471 : Blo 1780091 12833471 := bstep (se 1 (by rfl) ⟨9625103, by rfl⟩ : syracuseStep 12833471 = 19250207) B19250207
theorem B2004763 : Blo 1780091 2004763 := bstep (se 1 (by rfl) ⟨1503572, by rfl⟩ : syracuseStep 2004763 = 3007145) B3007145
theorem B2439337 : Blo 1780091 2439337 := bstep (se 2 (by rfl) ⟨914751, by rfl⟩ : syracuseStep 2439337 = 1829503) B1829503
theorem B30416795 : Blo 1780091 30416795 := bstep (se 1 (by rfl) ⟨22812596, by rfl⟩ : syracuseStep 30416795 = 45625193) B45625193
theorem B3252449 : Blo 1780091 3252449 := bstep (se 2 (by rfl) ⟨1219668, by rfl⟩ : syracuseStep 3252449 = 2439337) B2439337
theorem B2673017 : Blo 1780091 2673017 := bstep (se 2 (by rfl) ⟨1002381, by rfl⟩ : syracuseStep 2673017 = 2004763) B2004763
theorem B20277863 : Blo 1780091 20277863 := bstep (se 1 (by rfl) ⟨15208397, by rfl⟩ : syracuseStep 20277863 = 30416795) B30416795
theorem B8555647 : Blo 1780091 8555647 := bstep (se 1 (by rfl) ⟨6416735, by rfl⟩ : syracuseStep 8555647 = 12833471) B12833471
theorem B48756431 : Blo 1780091 48756431 := bstep (se 1 (by rfl) ⟨36567323, by rfl⟩ : syracuseStep 48756431 = 73134647) B73134647
theorem B13523435 : Blo 1780091 13523435 := bstep (se 1 (by rfl) ⟨10142576, by rfl⟩ : syracuseStep 13523435 = 20285153) B20285153
theorem B28892953 : Blo 1780091 28892953 := bstep (se 2 (by rfl) ⟨10834857, by rfl⟩ : syracuseStep 28892953 = 21669715) B21669715
theorem B3006463 : Blo 1780091 3006463 := bstep (se 1 (by rfl) ⟨2254847, by rfl⟩ : syracuseStep 3006463 = 4509695) B4509695
theorem B13518575 : Blo 1780091 13518575 := bstep (se 1 (by rfl) ⟨10138931, by rfl⟩ : syracuseStep 13518575 = 20277863) B20277863
theorem B4008617 : Blo 1780091 4008617 := bstep (se 2 (by rfl) ⟨1503231, by rfl⟩ : syracuseStep 4008617 = 3006463) B3006463
theorem B11407529 : Blo 1780091 11407529 := bstep (se 2 (by rfl) ⟨4277823, by rfl⟩ : syracuseStep 11407529 = 8555647) B8555647
theorem B1782011 : Blo 1780091 1782011 := bstep (se 1 (by rfl) ⟨1336508, by rfl⟩ : syracuseStep 1782011 = 2673017) B2673017
theorem B9015623 : Blo 1780091 9015623 := bstep (se 1 (by rfl) ⟨6761717, by rfl⟩ : syracuseStep 9015623 = 13523435) B13523435
theorem B38523937 : Blo 1780091 38523937 := bstep (se 2 (by rfl) ⟨14446476, by rfl⟩ : syracuseStep 38523937 = 28892953) B28892953
theorem B2168299 : Blo 1780091 2168299 := bstep (se 1 (by rfl) ⟨1626224, by rfl⟩ : syracuseStep 2168299 = 3252449) B3252449
theorem B32504287 : Blo 1780091 32504287 := bstep (se 1 (by rfl) ⟨24378215, by rfl⟩ : syracuseStep 32504287 = 48756431) B48756431
theorem B9012383 : Blo 1780091 9012383 := bstep (se 1 (by rfl) ⟨6759287, by rfl⟩ : syracuseStep 9012383 = 13518575) B13518575
theorem B51365249 : Blo 1780091 51365249 := bstep (se 2 (by rfl) ⟨19261968, by rfl⟩ : syracuseStep 51365249 = 38523937) B38523937
theorem B2672411 : Blo 1780091 2672411 := bstep (se 1 (by rfl) ⟨2004308, by rfl⟩ : syracuseStep 2672411 = 4008617) B4008617
theorem B7605019 : Blo 1780091 7605019 := bstep (se 1 (by rfl) ⟨5703764, by rfl⟩ : syracuseStep 7605019 = 11407529) B11407529
theorem B43339049 : Blo 1780091 43339049 := bstep (se 2 (by rfl) ⟨16252143, by rfl⟩ : syracuseStep 43339049 = 32504287) B32504287
theorem B11564261 : Blo 1780091 11564261 := bstep (se 4 (by rfl) ⟨1084149, by rfl⟩ : syracuseStep 11564261 = 2168299) B2168299
theorem B6010415 : Blo 1780091 6010415 := bstep (se 1 (by rfl) ⟨4507811, by rfl⟩ : syracuseStep 6010415 = 9015623) B9015623
theorem B7709507 : Blo 1780091 7709507 := bstep (se 1 (by rfl) ⟨5782130, by rfl⟩ : syracuseStep 7709507 = 11564261) B11564261
theorem B34243499 : Blo 1780091 34243499 := bstep (se 1 (by rfl) ⟨25682624, by rfl⟩ : syracuseStep 34243499 = 51365249) B51365249
theorem B4006943 : Blo 1780091 4006943 := bstep (se 1 (by rfl) ⟨3005207, by rfl⟩ : syracuseStep 4006943 = 6010415) B6010415
theorem B6008255 : Blo 1780091 6008255 := bstep (se 1 (by rfl) ⟨4506191, by rfl⟩ : syracuseStep 6008255 = 9012383) B9012383
theorem B1781607 : Blo 1780091 1781607 := bstep (se 1 (by rfl) ⟨1336205, by rfl⟩ : syracuseStep 1781607 = 2672411) B2672411
theorem B10140025 : Blo 1780091 10140025 := bstep (se 2 (by rfl) ⟨3802509, by rfl⟩ : syracuseStep 10140025 = 7605019) B7605019
theorem B28892699 : Blo 1780091 28892699 := bstep (se 1 (by rfl) ⟨21669524, by rfl⟩ : syracuseStep 28892699 = 43339049) B43339049
theorem B2671295 : Blo 1780091 2671295 := bstep (se 1 (by rfl) ⟨2003471, by rfl⟩ : syracuseStep 2671295 = 4006943) B4006943
theorem B19261799 : Blo 1780091 19261799 := bstep (se 1 (by rfl) ⟨14446349, by rfl⟩ : syracuseStep 19261799 = 28892699) B28892699
theorem B13520033 : Blo 1780091 13520033 := bstep (se 2 (by rfl) ⟨5070012, by rfl⟩ : syracuseStep 13520033 = 10140025) B10140025
theorem B5139671 : Blo 1780091 5139671 := bstep (se 1 (by rfl) ⟨3854753, by rfl⟩ : syracuseStep 5139671 = 7709507) B7709507
theorem B22828999 : Blo 1780091 22828999 := bstep (se 1 (by rfl) ⟨17121749, by rfl⟩ : syracuseStep 22828999 = 34243499) B34243499
theorem B4005503 : Blo 1780091 4005503 := bstep (se 1 (by rfl) ⟨3004127, by rfl⟩ : syracuseStep 4005503 = 6008255) B6008255
theorem B13705789 : Blo 1780091 13705789 := bstep (se 3 (by rfl) ⟨2569835, by rfl⟩ : syracuseStep 13705789 = 5139671) B5139671
theorem B9013355 : Blo 1780091 9013355 := bstep (se 1 (by rfl) ⟨6760016, by rfl⟩ : syracuseStep 9013355 = 13520033) B13520033
theorem B1780863 : Blo 1780091 1780863 := bstep (se 1 (by rfl) ⟨1335647, by rfl⟩ : syracuseStep 1780863 = 2671295) B2671295
theorem B12841199 : Blo 1780091 12841199 := bstep (se 1 (by rfl) ⟨9630899, by rfl⟩ : syracuseStep 12841199 = 19261799) B19261799
theorem B30438665 : Blo 1780091 30438665 := bstep (se 2 (by rfl) ⟨11414499, by rfl⟩ : syracuseStep 30438665 = 22828999) B22828999
theorem B2670335 : Blo 1780091 2670335 := bstep (se 1 (by rfl) ⟨2002751, by rfl⟩ : syracuseStep 2670335 = 4005503) B4005503
theorem B8560799 : Blo 1780091 8560799 := bstep (se 1 (by rfl) ⟨6420599, by rfl⟩ : syracuseStep 8560799 = 12841199) B12841199
theorem B20292443 : Blo 1780091 20292443 := bstep (se 1 (by rfl) ⟨15219332, by rfl⟩ : syracuseStep 20292443 = 30438665) B30438665
theorem B1780223 : Blo 1780091 1780223 := bstep (se 1 (by rfl) ⟨1335167, by rfl⟩ : syracuseStep 1780223 = 2670335) B2670335
theorem B6008903 : Blo 1780091 6008903 := bstep (se 1 (by rfl) ⟨4506677, by rfl⟩ : syracuseStep 6008903 = 9013355) B9013355
theorem B18274385 : Blo 1780091 18274385 := bstep (se 2 (by rfl) ⟨6852894, by rfl⟩ : syracuseStep 18274385 = 13705789) B13705789
theorem B4005935 : Blo 1780091 4005935 := bstep (se 1 (by rfl) ⟨3004451, by rfl⟩ : syracuseStep 4005935 = 6008903) B6008903
theorem B12182923 : Blo 1780091 12182923 := bstep (se 1 (by rfl) ⟨9137192, by rfl⟩ : syracuseStep 12182923 = 18274385) B18274385
theorem B13528295 : Blo 1780091 13528295 := bstep (se 1 (by rfl) ⟨10146221, by rfl⟩ : syracuseStep 13528295 = 20292443) B20292443
theorem B5707199 : Blo 1780091 5707199 := bstep (se 1 (by rfl) ⟨4280399, by rfl⟩ : syracuseStep 5707199 = 8560799) B8560799
theorem B2670623 : Blo 1780091 2670623 := bstep (se 1 (by rfl) ⟨2002967, by rfl⟩ : syracuseStep 2670623 = 4005935) B4005935
theorem B15219197 : Blo 1780091 15219197 := bstep (se 3 (by rfl) ⟨2853599, by rfl⟩ : syracuseStep 15219197 = 5707199) B5707199
theorem B16243897 : Blo 1780091 16243897 := bstep (se 2 (by rfl) ⟨6091461, by rfl⟩ : syracuseStep 16243897 = 12182923) B12182923
theorem B9018863 : Blo 1780091 9018863 := bstep (se 1 (by rfl) ⟨6764147, by rfl⟩ : syracuseStep 9018863 = 13528295) B13528295
theorem B1780415 : Blo 1780091 1780415 := bstep (se 1 (by rfl) ⟨1335311, by rfl⟩ : syracuseStep 1780415 = 2670623) B2670623
theorem B10146131 : Blo 1780091 10146131 := bstep (se 1 (by rfl) ⟨7609598, by rfl⟩ : syracuseStep 10146131 = 15219197) B15219197
theorem B21658529 : Blo 1780091 21658529 := bstep (se 2 (by rfl) ⟨8121948, by rfl⟩ : syracuseStep 21658529 = 16243897) B16243897
theorem B6012575 : Blo 1780091 6012575 := bstep (se 1 (by rfl) ⟨4509431, by rfl⟩ : syracuseStep 6012575 = 9018863) B9018863
theorem B4008383 : Blo 1780091 4008383 := bstep (se 1 (by rfl) ⟨3006287, by rfl⟩ : syracuseStep 4008383 = 6012575) B6012575
theorem B14439019 : Blo 1780091 14439019 := bstep (se 1 (by rfl) ⟨10829264, by rfl⟩ : syracuseStep 14439019 = 21658529) B21658529
theorem B6764087 : Blo 1780091 6764087 := bstep (se 1 (by rfl) ⟨5073065, by rfl⟩ : syracuseStep 6764087 = 10146131) B10146131
theorem B19252025 : Blo 1780091 19252025 := bstep (se 2 (by rfl) ⟨7219509, by rfl⟩ : syracuseStep 19252025 = 14439019) B14439019
theorem B2672255 : Blo 1780091 2672255 := bstep (se 1 (by rfl) ⟨2004191, by rfl⟩ : syracuseStep 2672255 = 4008383) B4008383
theorem B4509391 : Blo 1780091 4509391 := bstep (se 1 (by rfl) ⟨3382043, by rfl⟩ : syracuseStep 4509391 = 6764087) B6764087
theorem B1781503 : Blo 1780091 1781503 := bstep (se 1 (by rfl) ⟨1336127, by rfl⟩ : syracuseStep 1781503 = 2672255) B2672255
theorem B12834683 : Blo 1780091 12834683 := bstep (se 1 (by rfl) ⟨9626012, by rfl⟩ : syracuseStep 12834683 = 19252025) B19252025
theorem B6012521 : Blo 1780091 6012521 := bstep (se 2 (by rfl) ⟨2254695, by rfl⟩ : syracuseStep 6012521 = 4509391) B4509391
theorem B4008347 : Blo 1780091 4008347 := bstep (se 1 (by rfl) ⟨3006260, by rfl⟩ : syracuseStep 4008347 = 6012521) B6012521
theorem B8556455 : Blo 1780091 8556455 := bstep (se 1 (by rfl) ⟨6417341, by rfl⟩ : syracuseStep 8556455 = 12834683) B12834683
theorem B2672231 : Blo 1780091 2672231 := bstep (se 1 (by rfl) ⟨2004173, by rfl⟩ : syracuseStep 2672231 = 4008347) B4008347
theorem B22817213 : Blo 1780091 22817213 := bstep (se 3 (by rfl) ⟨4278227, by rfl⟩ : syracuseStep 22817213 = 8556455) B8556455
theorem B1781487 : Blo 1780091 1781487 := bstep (se 1 (by rfl) ⟨1336115, by rfl⟩ : syracuseStep 1781487 = 2672231) B2672231
theorem B15211475 : Blo 1780091 15211475 := bstep (se 1 (by rfl) ⟨11408606, by rfl⟩ : syracuseStep 15211475 = 22817213) B22817213
theorem B10140983 : Blo 1780091 10140983 := bstep (se 1 (by rfl) ⟨7605737, by rfl⟩ : syracuseStep 10140983 = 15211475) B15211475
theorem B6760655 : Blo 1780091 6760655 := bstep (se 1 (by rfl) ⟨5070491, by rfl⟩ : syracuseStep 6760655 = 10140983) B10140983
theorem B4507103 : Blo 1780091 4507103 := bstep (se 1 (by rfl) ⟨3380327, by rfl⟩ : syracuseStep 4507103 = 6760655) B6760655
theorem B3004735 : Blo 1780091 3004735 := bstep (se 1 (by rfl) ⟨2253551, by rfl⟩ : syracuseStep 3004735 = 4507103) B4507103
theorem B4006313 : Blo 1780091 4006313 := bstep (se 2 (by rfl) ⟨1502367, by rfl⟩ : syracuseStep 4006313 = 3004735) B3004735
theorem B2670875 : Blo 1780091 2670875 := bstep (se 1 (by rfl) ⟨2003156, by rfl⟩ : syracuseStep 2670875 = 4006313) B4006313
theorem B1780583 : Blo 1780091 1780583 := bstep (se 1 (by rfl) ⟨1335437, by rfl⟩ : syracuseStep 1780583 = 2670875) B2670875

theorem C0 (j : ℕ) (h1 : 445022 ≤ j) (h2 : j ≤ 445522) : Blo 1780091 (4 * j + 3) := by
  interval_cases j
  · exact B1780091
  · exact B1780095
  · exact B1780099
  · exact B1780103
  · exact B1780107
  · exact B1780111
  · exact B1780115
  · exact B1780119
  · exact B1780123
  · exact B1780127
  · exact B1780131
  · exact B1780135
  · exact B1780139
  · exact B1780143
  · exact B1780147
  · exact B1780151
  · exact B1780155
  · exact B1780159
  · exact B1780163
  · exact B1780167
  · exact B1780171
  · exact B1780175
  · exact B1780179
  · exact B1780183
  · exact B1780187
  · exact B1780191
  · exact B1780195
  · exact B1780199
  · exact B1780203
  · exact B1780207
  · exact B1780211
  · exact B1780215
  · exact B1780219
  · exact B1780223
  · exact B1780227
  · exact B1780231
  · exact B1780235
  · exact B1780239
  · exact B1780243
  · exact B1780247
  · exact B1780251
  · exact B1780255
  · exact B1780259
  · exact B1780263
  · exact B1780267
  · exact B1780271
  · exact B1780275
  · exact B1780279
  · exact B1780283
  · exact B1780287
  · exact B1780291
  · exact B1780295
  · exact B1780299
  · exact B1780303
  · exact B1780307
  · exact B1780311
  · exact B1780315
  · exact B1780319
  · exact B1780323
  · exact B1780327
  · exact B1780331
  · exact B1780335
  · exact B1780339
  · exact B1780343
  · exact B1780347
  · exact B1780351
  · exact B1780355
  · exact B1780359
  · exact B1780363
  · exact B1780367
  · exact B1780371
  · exact B1780375
  · exact B1780379
  · exact B1780383
  · exact B1780387
  · exact B1780391
  · exact B1780395
  · exact B1780399
  · exact B1780403
  · exact B1780407
  · exact B1780411
  · exact B1780415
  · exact B1780419
  · exact B1780423
  · exact B1780427
  · exact B1780431
  · exact B1780435
  · exact B1780439
  · exact B1780443
  · exact B1780447
  · exact B1780451
  · exact B1780455
  · exact B1780459
  · exact B1780463
  · exact B1780467
  · exact B1780471
  · exact B1780475
  · exact B1780479
  · exact B1780483
  · exact B1780487
  · exact B1780491
  · exact B1780495
  · exact B1780499
  · exact B1780503
  · exact B1780507
  · exact B1780511
  · exact B1780515
  · exact B1780519
  · exact B1780523
  · exact B1780527
  · exact B1780531
  · exact B1780535
  · exact B1780539
  · exact B1780543
  · exact B1780547
  · exact B1780551
  · exact B1780555
  · exact B1780559
  · exact B1780563
  · exact B1780567
  · exact B1780571
  · exact B1780575
  · exact B1780579
  · exact B1780583
  · exact B1780587
  · exact B1780591
  · exact B1780595
  · exact B1780599
  · exact B1780603
  · exact B1780607
  · exact B1780611
  · exact B1780615
  · exact B1780619
  · exact B1780623
  · exact B1780627
  · exact B1780631
  · exact B1780635
  · exact B1780639
  · exact B1780643
  · exact B1780647
  · exact B1780651
  · exact B1780655
  · exact B1780659
  · exact B1780663
  · exact B1780667
  · exact B1780671
  · exact B1780675
  · exact B1780679
  · exact B1780683
  · exact B1780687
  · exact B1780691
  · exact B1780695
  · exact B1780699
  · exact B1780703
  · exact B1780707
  · exact B1780711
  · exact B1780715
  · exact B1780719
  · exact B1780723
  · exact B1780727
  · exact B1780731
  · exact B1780735
  · exact B1780739
  · exact B1780743
  · exact B1780747
  · exact B1780751
  · exact B1780755
  · exact B1780759
  · exact B1780763
  · exact B1780767
  · exact B1780771
  · exact B1780775
  · exact B1780779
  · exact B1780783
  · exact B1780787
  · exact B1780791
  · exact B1780795
  · exact B1780799
  · exact B1780803
  · exact B1780807
  · exact B1780811
  · exact B1780815
  · exact B1780819
  · exact B1780823
  · exact B1780827
  · exact B1780831
  · exact B1780835
  · exact B1780839
  · exact B1780843
  · exact B1780847
  · exact B1780851
  · exact B1780855
  · exact B1780859
  · exact B1780863
  · exact B1780867
  · exact B1780871
  · exact B1780875
  · exact B1780879
  · exact B1780883
  · exact B1780887
  · exact B1780891
  · exact B1780895
  · exact B1780899
  · exact B1780903
  · exact B1780907
  · exact B1780911
  · exact B1780915
  · exact B1780919
  · exact B1780923
  · exact B1780927
  · exact B1780931
  · exact B1780935
  · exact B1780939
  · exact B1780943
  · exact B1780947
  · exact B1780951
  · exact B1780955
  · exact B1780959
  · exact B1780963
  · exact B1780967
  · exact B1780971
  · exact B1780975
  · exact B1780979
  · exact B1780983
  · exact B1780987
  · exact B1780991
  · exact B1780995
  · exact B1780999
  · exact B1781003
  · exact B1781007
  · exact B1781011
  · exact B1781015
  · exact B1781019
  · exact B1781023
  · exact B1781027
  · exact B1781031
  · exact B1781035
  · exact B1781039
  · exact B1781043
  · exact B1781047
  · exact B1781051
  · exact B1781055
  · exact B1781059
  · exact B1781063
  · exact B1781067
  · exact B1781071
  · exact B1781075
  · exact B1781079
  · exact B1781083
  · exact B1781087
  · exact B1781091
  · exact B1781095
  · exact B1781099
  · exact B1781103
  · exact B1781107
  · exact B1781111
  · exact B1781115
  · exact B1781119
  · exact B1781123
  · exact B1781127
  · exact B1781131
  · exact B1781135
  · exact B1781139
  · exact B1781143
  · exact B1781147
  · exact B1781151
  · exact B1781155
  · exact B1781159
  · exact B1781163
  · exact B1781167
  · exact B1781171
  · exact B1781175
  · exact B1781179
  · exact B1781183
  · exact B1781187
  · exact B1781191
  · exact B1781195
  · exact B1781199
  · exact B1781203
  · exact B1781207
  · exact B1781211
  · exact B1781215
  · exact B1781219
  · exact B1781223
  · exact B1781227
  · exact B1781231
  · exact B1781235
  · exact B1781239
  · exact B1781243
  · exact B1781247
  · exact B1781251
  · exact B1781255
  · exact B1781259
  · exact B1781263
  · exact B1781267
  · exact B1781271
  · exact B1781275
  · exact B1781279
  · exact B1781283
  · exact B1781287
  · exact B1781291
  · exact B1781295
  · exact B1781299
  · exact B1781303
  · exact B1781307
  · exact B1781311
  · exact B1781315
  · exact B1781319
  · exact B1781323
  · exact B1781327
  · exact B1781331
  · exact B1781335
  · exact B1781339
  · exact B1781343
  · exact B1781347
  · exact B1781351
  · exact B1781355
  · exact B1781359
  · exact B1781363
  · exact B1781367
  · exact B1781371
  · exact B1781375
  · exact B1781379
  · exact B1781383
  · exact B1781387
  · exact B1781391
  · exact B1781395
  · exact B1781399
  · exact B1781403
  · exact B1781407
  · exact B1781411
  · exact B1781415
  · exact B1781419
  · exact B1781423
  · exact B1781427
  · exact B1781431
  · exact B1781435
  · exact B1781439
  · exact B1781443
  · exact B1781447
  · exact B1781451
  · exact B1781455
  · exact B1781459
  · exact B1781463
  · exact B1781467
  · exact B1781471
  · exact B1781475
  · exact B1781479
  · exact B1781483
  · exact B1781487
  · exact B1781491
  · exact B1781495
  · exact B1781499
  · exact B1781503
  · exact B1781507
  · exact B1781511
  · exact B1781515
  · exact B1781519
  · exact B1781523
  · exact B1781527
  · exact B1781531
  · exact B1781535
  · exact B1781539
  · exact B1781543
  · exact B1781547
  · exact B1781551
  · exact B1781555
  · exact B1781559
  · exact B1781563
  · exact B1781567
  · exact B1781571
  · exact B1781575
  · exact B1781579
  · exact B1781583
  · exact B1781587
  · exact B1781591
  · exact B1781595
  · exact B1781599
  · exact B1781603
  · exact B1781607
  · exact B1781611
  · exact B1781615
  · exact B1781619
  · exact B1781623
  · exact B1781627
  · exact B1781631
  · exact B1781635
  · exact B1781639
  · exact B1781643
  · exact B1781647
  · exact B1781651
  · exact B1781655
  · exact B1781659
  · exact B1781663
  · exact B1781667
  · exact B1781671
  · exact B1781675
  · exact B1781679
  · exact B1781683
  · exact B1781687
  · exact B1781691
  · exact B1781695
  · exact B1781699
  · exact B1781703
  · exact B1781707
  · exact B1781711
  · exact B1781715
  · exact B1781719
  · exact B1781723
  · exact B1781727
  · exact B1781731
  · exact B1781735
  · exact B1781739
  · exact B1781743
  · exact B1781747
  · exact B1781751
  · exact B1781755
  · exact B1781759
  · exact B1781763
  · exact B1781767
  · exact B1781771
  · exact B1781775
  · exact B1781779
  · exact B1781783
  · exact B1781787
  · exact B1781791
  · exact B1781795
  · exact B1781799
  · exact B1781803
  · exact B1781807
  · exact B1781811
  · exact B1781815
  · exact B1781819
  · exact B1781823
  · exact B1781827
  · exact B1781831
  · exact B1781835
  · exact B1781839
  · exact B1781843
  · exact B1781847
  · exact B1781851
  · exact B1781855
  · exact B1781859
  · exact B1781863
  · exact B1781867
  · exact B1781871
  · exact B1781875
  · exact B1781879
  · exact B1781883
  · exact B1781887
  · exact B1781891
  · exact B1781895
  · exact B1781899
  · exact B1781903
  · exact B1781907
  · exact B1781911
  · exact B1781915
  · exact B1781919
  · exact B1781923
  · exact B1781927
  · exact B1781931
  · exact B1781935
  · exact B1781939
  · exact B1781943
  · exact B1781947
  · exact B1781951
  · exact B1781955
  · exact B1781959
  · exact B1781963
  · exact B1781967
  · exact B1781971
  · exact B1781975
  · exact B1781979
  · exact B1781983
  · exact B1781987
  · exact B1781991
  · exact B1781995
  · exact B1781999
  · exact B1782003
  · exact B1782007
  · exact B1782011
  · exact B1782015
  · exact B1782019
  · exact B1782023
  · exact B1782027
  · exact B1782031
  · exact B1782035
  · exact B1782039
  · exact B1782043
  · exact B1782047
  · exact B1782051
  · exact B1782055
  · exact B1782059
  · exact B1782063
  · exact B1782067
  · exact B1782071
  · exact B1782075
  · exact B1782079
  · exact B1782083
  · exact B1782087
  · exact B1782091

theorem solution (m : ℕ) (hlo : 1780091 ≤ m) (hhi : m ≤ 1782091) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 445022 ≤ j := by omega
    have hj2 : j ≤ 445522 := by omega
    have hb : Blo 1780091 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
