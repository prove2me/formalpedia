-- Prove2me | solution 1 for syracuse_descends_range_1909435_1911435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:46:59.23977+00:00
-- url     : https://prove2.me/submissions/019be976-a4b9-49cc-b2a0-ed45457d6689

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

theorem B3222173 : Blo 1909435 3222173 := bbase (se 3 (by rfl) ⟨604157, by rfl⟩ : syracuseStep 3222173 = 1208315) (by norm_num)
theorem B2148115 : Blo 1909435 2148115 := bstep (se 1 (by rfl) ⟨1611086, by rfl⟩ : syracuseStep 2148115 = 3222173) B3222173
theorem B2864153 : Blo 1909435 2864153 := bstep (se 2 (by rfl) ⟨1074057, by rfl⟩ : syracuseStep 2864153 = 2148115) B2148115
theorem B1909435 : Blo 1909435 1909435 := bstep (se 1 (by rfl) ⟨1432076, by rfl⟩ : syracuseStep 1909435 = 2864153) B2864153
theorem B3923797 : Blo 1909435 3923797 := bbase (se 9 (by rfl) ⟨11495, by rfl⟩ : syracuseStep 3923797 = 22991) (by norm_num)
theorem B5231729 : Blo 1909435 5231729 := bstep (se 2 (by rfl) ⟨1961898, by rfl⟩ : syracuseStep 5231729 = 3923797) B3923797
theorem B13951277 : Blo 1909435 13951277 := bstep (se 3 (by rfl) ⟨2615864, by rfl⟩ : syracuseStep 13951277 = 5231729) B5231729
theorem B9300851 : Blo 1909435 9300851 := bstep (se 1 (by rfl) ⟨6975638, by rfl⟩ : syracuseStep 9300851 = 13951277) B13951277
theorem B6200567 : Blo 1909435 6200567 := bstep (se 1 (by rfl) ⟨4650425, by rfl⟩ : syracuseStep 6200567 = 9300851) B9300851
theorem B4133711 : Blo 1909435 4133711 := bstep (se 1 (by rfl) ⟨3100283, by rfl⟩ : syracuseStep 4133711 = 6200567) B6200567
theorem B11023229 : Blo 1909435 11023229 := bstep (se 3 (by rfl) ⟨2066855, by rfl⟩ : syracuseStep 11023229 = 4133711) B4133711
theorem B7348819 : Blo 1909435 7348819 := bstep (se 1 (by rfl) ⟨5511614, by rfl⟩ : syracuseStep 7348819 = 11023229) B11023229
theorem B9798425 : Blo 1909435 9798425 := bstep (se 2 (by rfl) ⟨3674409, by rfl⟩ : syracuseStep 9798425 = 7348819) B7348819
theorem B6532283 : Blo 1909435 6532283 := bstep (se 1 (by rfl) ⟨4899212, by rfl⟩ : syracuseStep 6532283 = 9798425) B9798425
theorem B17419421 : Blo 1909435 17419421 := bstep (se 3 (by rfl) ⟨3266141, by rfl⟩ : syracuseStep 17419421 = 6532283) B6532283
theorem B46451789 : Blo 1909435 46451789 := bstep (se 3 (by rfl) ⟨8709710, by rfl⟩ : syracuseStep 46451789 = 17419421) B17419421
theorem B30967859 : Blo 1909435 30967859 := bstep (se 1 (by rfl) ⟨23225894, by rfl⟩ : syracuseStep 30967859 = 46451789) B46451789
theorem B20645239 : Blo 1909435 20645239 := bstep (se 1 (by rfl) ⟨15483929, by rfl⟩ : syracuseStep 20645239 = 30967859) B30967859
theorem B27526985 : Blo 1909435 27526985 := bstep (se 2 (by rfl) ⟨10322619, by rfl⟩ : syracuseStep 27526985 = 20645239) B20645239
theorem B18351323 : Blo 1909435 18351323 := bstep (se 1 (by rfl) ⟨13763492, by rfl⟩ : syracuseStep 18351323 = 27526985) B27526985
theorem B12234215 : Blo 1909435 12234215 := bstep (se 1 (by rfl) ⟨9175661, by rfl⟩ : syracuseStep 12234215 = 18351323) B18351323
theorem B8156143 : Blo 1909435 8156143 := bstep (se 1 (by rfl) ⟨6117107, by rfl⟩ : syracuseStep 8156143 = 12234215) B12234215
theorem B10874857 : Blo 1909435 10874857 := bstep (se 2 (by rfl) ⟨4078071, by rfl⟩ : syracuseStep 10874857 = 8156143) B8156143
theorem B14499809 : Blo 1909435 14499809 := bstep (se 2 (by rfl) ⟨5437428, by rfl⟩ : syracuseStep 14499809 = 10874857) B10874857
theorem B9666539 : Blo 1909435 9666539 := bstep (se 1 (by rfl) ⟨7249904, by rfl⟩ : syracuseStep 9666539 = 14499809) B14499809
theorem B6444359 : Blo 1909435 6444359 := bstep (se 1 (by rfl) ⟨4833269, by rfl⟩ : syracuseStep 6444359 = 9666539) B9666539
theorem B4296239 : Blo 1909435 4296239 := bstep (se 1 (by rfl) ⟨3222179, by rfl⟩ : syracuseStep 4296239 = 6444359) B6444359
theorem B2864159 : Blo 1909435 2864159 := bstep (se 1 (by rfl) ⟨2148119, by rfl⟩ : syracuseStep 2864159 = 4296239) B4296239
theorem B1909439 : Blo 1909435 1909439 := bstep (se 1 (by rfl) ⟨1432079, by rfl⟩ : syracuseStep 1909439 = 2864159) B2864159
theorem B2864165 : Blo 1909435 2864165 := bbase (se 4 (by rfl) ⟨268515, by rfl⟩ : syracuseStep 2864165 = 537031) (by norm_num)
theorem B1909443 : Blo 1909435 1909443 := bstep (se 1 (by rfl) ⟨1432082, by rfl⟩ : syracuseStep 1909443 = 2864165) B2864165
theorem B2416645 : Blo 1909435 2416645 := bbase (se 4 (by rfl) ⟨226560, by rfl⟩ : syracuseStep 2416645 = 453121) (by norm_num)
theorem B3222193 : Blo 1909435 3222193 := bstep (se 2 (by rfl) ⟨1208322, by rfl⟩ : syracuseStep 3222193 = 2416645) B2416645
theorem B4296257 : Blo 1909435 4296257 := bstep (se 2 (by rfl) ⟨1611096, by rfl⟩ : syracuseStep 4296257 = 3222193) B3222193
theorem B2864171 : Blo 1909435 2864171 := bstep (se 1 (by rfl) ⟨2148128, by rfl⟩ : syracuseStep 2864171 = 4296257) B4296257
theorem B1909447 : Blo 1909435 1909447 := bstep (se 1 (by rfl) ⟨1432085, by rfl⟩ : syracuseStep 1909447 = 2864171) B2864171
theorem B2148133 : Blo 1909435 2148133 := bbase (se 4 (by rfl) ⟨201387, by rfl⟩ : syracuseStep 2148133 = 402775) (by norm_num)
theorem B2864177 : Blo 1909435 2864177 := bstep (se 2 (by rfl) ⟨1074066, by rfl⟩ : syracuseStep 2864177 = 2148133) B2148133
theorem B1909451 : Blo 1909435 1909451 := bstep (se 1 (by rfl) ⟨1432088, by rfl⟩ : syracuseStep 1909451 = 2864177) B2864177
theorem B8156213 : Blo 1909435 8156213 := bbase (se 5 (by rfl) ⟨382322, by rfl⟩ : syracuseStep 8156213 = 764645) (by norm_num)
theorem B5437475 : Blo 1909435 5437475 := bstep (se 1 (by rfl) ⟨4078106, by rfl⟩ : syracuseStep 5437475 = 8156213) B8156213
theorem B3624983 : Blo 1909435 3624983 := bstep (se 1 (by rfl) ⟨2718737, by rfl⟩ : syracuseStep 3624983 = 5437475) B5437475
theorem B2416655 : Blo 1909435 2416655 := bstep (se 1 (by rfl) ⟨1812491, by rfl⟩ : syracuseStep 2416655 = 3624983) B3624983
theorem B6444413 : Blo 1909435 6444413 := bstep (se 3 (by rfl) ⟨1208327, by rfl⟩ : syracuseStep 6444413 = 2416655) B2416655
theorem B4296275 : Blo 1909435 4296275 := bstep (se 1 (by rfl) ⟨3222206, by rfl⟩ : syracuseStep 4296275 = 6444413) B6444413
theorem B2864183 : Blo 1909435 2864183 := bstep (se 1 (by rfl) ⟨2148137, by rfl⟩ : syracuseStep 2864183 = 4296275) B4296275
theorem B1909455 : Blo 1909435 1909455 := bstep (se 1 (by rfl) ⟨1432091, by rfl⟩ : syracuseStep 1909455 = 2864183) B2864183
theorem B2864189 : Blo 1909435 2864189 := bbase (se 3 (by rfl) ⟨537035, by rfl⟩ : syracuseStep 2864189 = 1074071) (by norm_num)
theorem B1909459 : Blo 1909435 1909459 := bstep (se 1 (by rfl) ⟨1432094, by rfl⟩ : syracuseStep 1909459 = 2864189) B2864189
theorem B4296293 : Blo 1909435 4296293 := bbase (se 4 (by rfl) ⟨402777, by rfl⟩ : syracuseStep 4296293 = 805555) (by norm_num)
theorem B2864195 : Blo 1909435 2864195 := bstep (se 1 (by rfl) ⟨2148146, by rfl⟩ : syracuseStep 2864195 = 4296293) B4296293
theorem B1909463 : Blo 1909435 1909463 := bstep (se 1 (by rfl) ⟨1432097, by rfl⟩ : syracuseStep 1909463 = 2864195) B2864195
theorem B4833341 : Blo 1909435 4833341 := bbase (se 3 (by rfl) ⟨906251, by rfl⟩ : syracuseStep 4833341 = 1812503) (by norm_num)
theorem B3222227 : Blo 1909435 3222227 := bstep (se 1 (by rfl) ⟨2416670, by rfl⟩ : syracuseStep 3222227 = 4833341) B4833341
theorem B2148151 : Blo 1909435 2148151 := bstep (se 1 (by rfl) ⟨1611113, by rfl⟩ : syracuseStep 2148151 = 3222227) B3222227
theorem B2864201 : Blo 1909435 2864201 := bstep (se 2 (by rfl) ⟨1074075, by rfl⟩ : syracuseStep 2864201 = 2148151) B2148151
theorem B1909467 : Blo 1909435 1909467 := bstep (se 1 (by rfl) ⟨1432100, by rfl⟩ : syracuseStep 1909467 = 2864201) B2864201
theorem B3625013 : Blo 1909435 3625013 := bbase (se 5 (by rfl) ⟨169922, by rfl⟩ : syracuseStep 3625013 = 339845) (by norm_num)
theorem B9666701 : Blo 1909435 9666701 := bstep (se 3 (by rfl) ⟨1812506, by rfl⟩ : syracuseStep 9666701 = 3625013) B3625013
theorem B6444467 : Blo 1909435 6444467 := bstep (se 1 (by rfl) ⟨4833350, by rfl⟩ : syracuseStep 6444467 = 9666701) B9666701
theorem B4296311 : Blo 1909435 4296311 := bstep (se 1 (by rfl) ⟨3222233, by rfl⟩ : syracuseStep 4296311 = 6444467) B6444467
theorem B2864207 : Blo 1909435 2864207 := bstep (se 1 (by rfl) ⟨2148155, by rfl⟩ : syracuseStep 2864207 = 4296311) B4296311
theorem B1909471 : Blo 1909435 1909471 := bstep (se 1 (by rfl) ⟨1432103, by rfl⟩ : syracuseStep 1909471 = 2864207) B2864207
theorem B2864213 : Blo 1909435 2864213 := bbase (se 8 (by rfl) ⟨16782, by rfl⟩ : syracuseStep 2864213 = 33565) (by norm_num)
theorem B1909475 : Blo 1909435 1909475 := bstep (se 1 (by rfl) ⟨1432106, by rfl⟩ : syracuseStep 1909475 = 2864213) B2864213
theorem B6532421 : Blo 1909435 6532421 := bbase (se 4 (by rfl) ⟨612414, by rfl⟩ : syracuseStep 6532421 = 1224829) (by norm_num)
theorem B17419789 : Blo 1909435 17419789 := bstep (se 3 (by rfl) ⟨3266210, by rfl⟩ : syracuseStep 17419789 = 6532421) B6532421
theorem B23226385 : Blo 1909435 23226385 := bstep (se 2 (by rfl) ⟨8709894, by rfl⟩ : syracuseStep 23226385 = 17419789) B17419789
theorem B30968513 : Blo 1909435 30968513 := bstep (se 2 (by rfl) ⟨11613192, by rfl⟩ : syracuseStep 30968513 = 23226385) B23226385
theorem B20645675 : Blo 1909435 20645675 := bstep (se 1 (by rfl) ⟨15484256, by rfl⟩ : syracuseStep 20645675 = 30968513) B30968513
theorem B13763783 : Blo 1909435 13763783 := bstep (se 1 (by rfl) ⟨10322837, by rfl⟩ : syracuseStep 13763783 = 20645675) B20645675
theorem B9175855 : Blo 1909435 9175855 := bstep (se 1 (by rfl) ⟨6881891, by rfl⟩ : syracuseStep 9175855 = 13763783) B13763783
theorem B12234473 : Blo 1909435 12234473 := bstep (se 2 (by rfl) ⟨4587927, by rfl⟩ : syracuseStep 12234473 = 9175855) B9175855
theorem B8156315 : Blo 1909435 8156315 := bstep (se 1 (by rfl) ⟨6117236, by rfl⟩ : syracuseStep 8156315 = 12234473) B12234473
theorem B5437543 : Blo 1909435 5437543 := bstep (se 1 (by rfl) ⟨4078157, by rfl⟩ : syracuseStep 5437543 = 8156315) B8156315
theorem B7250057 : Blo 1909435 7250057 := bstep (se 2 (by rfl) ⟨2718771, by rfl⟩ : syracuseStep 7250057 = 5437543) B5437543
theorem B4833371 : Blo 1909435 4833371 := bstep (se 1 (by rfl) ⟨3625028, by rfl⟩ : syracuseStep 4833371 = 7250057) B7250057
theorem B3222247 : Blo 1909435 3222247 := bstep (se 1 (by rfl) ⟨2416685, by rfl⟩ : syracuseStep 3222247 = 4833371) B4833371
theorem B4296329 : Blo 1909435 4296329 := bstep (se 2 (by rfl) ⟨1611123, by rfl⟩ : syracuseStep 4296329 = 3222247) B3222247
theorem B2864219 : Blo 1909435 2864219 := bstep (se 1 (by rfl) ⟨2148164, by rfl⟩ : syracuseStep 2864219 = 4296329) B4296329
theorem B1909479 : Blo 1909435 1909479 := bstep (se 1 (by rfl) ⟨1432109, by rfl⟩ : syracuseStep 1909479 = 2864219) B2864219
theorem B2148169 : Blo 1909435 2148169 := bbase (se 2 (by rfl) ⟨805563, by rfl⟩ : syracuseStep 2148169 = 1611127) (by norm_num)
theorem B2864225 : Blo 1909435 2864225 := bstep (se 2 (by rfl) ⟨1074084, by rfl⟩ : syracuseStep 2864225 = 2148169) B2148169
theorem B1909483 : Blo 1909435 1909483 := bstep (se 1 (by rfl) ⟨1432112, by rfl⟩ : syracuseStep 1909483 = 2864225) B2864225
theorem B158917717 : Blo 1909435 158917717 := bbase (se 8 (by rfl) ⟨931158, by rfl⟩ : syracuseStep 158917717 = 1862317) (by norm_num)
theorem B847561157 : Blo 1909435 847561157 := bstep (se 4 (by rfl) ⟨79458858, by rfl⟩ : syracuseStep 847561157 = 158917717) B158917717
theorem B565040771 : Blo 1909435 565040771 := bstep (se 1 (by rfl) ⟨423780578, by rfl⟩ : syracuseStep 565040771 = 847561157) B847561157
theorem B376693847 : Blo 1909435 376693847 := bstep (se 1 (by rfl) ⟨282520385, by rfl⟩ : syracuseStep 376693847 = 565040771) B565040771
theorem B251129231 : Blo 1909435 251129231 := bstep (se 1 (by rfl) ⟨188346923, by rfl⟩ : syracuseStep 251129231 = 376693847) B376693847
theorem B167419487 : Blo 1909435 167419487 := bstep (se 1 (by rfl) ⟨125564615, by rfl⟩ : syracuseStep 167419487 = 251129231) B251129231
theorem B111612991 : Blo 1909435 111612991 := bstep (se 1 (by rfl) ⟨83709743, by rfl⟩ : syracuseStep 111612991 = 167419487) B167419487
theorem B148817321 : Blo 1909435 148817321 := bstep (se 2 (by rfl) ⟨55806495, by rfl⟩ : syracuseStep 148817321 = 111612991) B111612991
theorem B99211547 : Blo 1909435 99211547 := bstep (se 1 (by rfl) ⟨74408660, by rfl⟩ : syracuseStep 99211547 = 148817321) B148817321
theorem B66141031 : Blo 1909435 66141031 := bstep (se 1 (by rfl) ⟨49605773, by rfl⟩ : syracuseStep 66141031 = 99211547) B99211547
theorem B88188041 : Blo 1909435 88188041 := bstep (se 2 (by rfl) ⟨33070515, by rfl⟩ : syracuseStep 88188041 = 66141031) B66141031
theorem B235168109 : Blo 1909435 235168109 := bstep (se 3 (by rfl) ⟨44094020, by rfl⟩ : syracuseStep 235168109 = 88188041) B88188041
theorem B156778739 : Blo 1909435 156778739 := bstep (se 1 (by rfl) ⟨117584054, by rfl⟩ : syracuseStep 156778739 = 235168109) B235168109
theorem B104519159 : Blo 1909435 104519159 := bstep (se 1 (by rfl) ⟨78389369, by rfl⟩ : syracuseStep 104519159 = 156778739) B156778739
theorem B69679439 : Blo 1909435 69679439 := bstep (se 1 (by rfl) ⟨52259579, by rfl⟩ : syracuseStep 69679439 = 104519159) B104519159
theorem B46452959 : Blo 1909435 46452959 := bstep (se 1 (by rfl) ⟨34839719, by rfl⟩ : syracuseStep 46452959 = 69679439) B69679439
theorem B30968639 : Blo 1909435 30968639 := bstep (se 1 (by rfl) ⟨23226479, by rfl⟩ : syracuseStep 30968639 = 46452959) B46452959
theorem B20645759 : Blo 1909435 20645759 := bstep (se 1 (by rfl) ⟨15484319, by rfl⟩ : syracuseStep 20645759 = 30968639) B30968639
theorem B13763839 : Blo 1909435 13763839 := bstep (se 1 (by rfl) ⟨10322879, by rfl⟩ : syracuseStep 13763839 = 20645759) B20645759
theorem B18351785 : Blo 1909435 18351785 := bstep (se 2 (by rfl) ⟨6881919, by rfl⟩ : syracuseStep 18351785 = 13763839) B13763839
theorem B12234523 : Blo 1909435 12234523 := bstep (se 1 (by rfl) ⟨9175892, by rfl⟩ : syracuseStep 12234523 = 18351785) B18351785
theorem B16312697 : Blo 1909435 16312697 := bstep (se 2 (by rfl) ⟨6117261, by rfl⟩ : syracuseStep 16312697 = 12234523) B12234523
theorem B10875131 : Blo 1909435 10875131 := bstep (se 1 (by rfl) ⟨8156348, by rfl⟩ : syracuseStep 10875131 = 16312697) B16312697
theorem B7250087 : Blo 1909435 7250087 := bstep (se 1 (by rfl) ⟨5437565, by rfl⟩ : syracuseStep 7250087 = 10875131) B10875131
theorem B4833391 : Blo 1909435 4833391 := bstep (se 1 (by rfl) ⟨3625043, by rfl⟩ : syracuseStep 4833391 = 7250087) B7250087
theorem B6444521 : Blo 1909435 6444521 := bstep (se 2 (by rfl) ⟨2416695, by rfl⟩ : syracuseStep 6444521 = 4833391) B4833391
theorem B4296347 : Blo 1909435 4296347 := bstep (se 1 (by rfl) ⟨3222260, by rfl⟩ : syracuseStep 4296347 = 6444521) B6444521
theorem B2864231 : Blo 1909435 2864231 := bstep (se 1 (by rfl) ⟨2148173, by rfl⟩ : syracuseStep 2864231 = 4296347) B4296347
theorem B1909487 : Blo 1909435 1909487 := bstep (se 1 (by rfl) ⟨1432115, by rfl⟩ : syracuseStep 1909487 = 2864231) B2864231
theorem B2864237 : Blo 1909435 2864237 := bbase (se 3 (by rfl) ⟨537044, by rfl⟩ : syracuseStep 2864237 = 1074089) (by norm_num)
theorem B1909491 : Blo 1909435 1909491 := bstep (se 1 (by rfl) ⟨1432118, by rfl⟩ : syracuseStep 1909491 = 2864237) B2864237
theorem B4296365 : Blo 1909435 4296365 := bbase (se 3 (by rfl) ⟨805568, by rfl⟩ : syracuseStep 4296365 = 1611137) (by norm_num)
theorem B2864243 : Blo 1909435 2864243 := bstep (se 1 (by rfl) ⟨2148182, by rfl⟩ : syracuseStep 2864243 = 4296365) B4296365
theorem B1909495 : Blo 1909435 1909495 := bstep (se 1 (by rfl) ⟨1432121, by rfl⟩ : syracuseStep 1909495 = 2864243) B2864243
theorem B7742213 : Blo 1909435 7742213 := bbase (se 4 (by rfl) ⟨725832, by rfl⟩ : syracuseStep 7742213 = 1451665) (by norm_num)
theorem B5161475 : Blo 1909435 5161475 := bstep (se 1 (by rfl) ⟨3871106, by rfl⟩ : syracuseStep 5161475 = 7742213) B7742213
theorem B3440983 : Blo 1909435 3440983 := bstep (se 1 (by rfl) ⟨2580737, by rfl⟩ : syracuseStep 3440983 = 5161475) B5161475
theorem B4587977 : Blo 1909435 4587977 := bstep (se 2 (by rfl) ⟨1720491, by rfl⟩ : syracuseStep 4587977 = 3440983) B3440983
theorem B3058651 : Blo 1909435 3058651 := bstep (se 1 (by rfl) ⟨2293988, by rfl⟩ : syracuseStep 3058651 = 4587977) B4587977
theorem B4078201 : Blo 1909435 4078201 := bstep (se 2 (by rfl) ⟨1529325, by rfl⟩ : syracuseStep 4078201 = 3058651) B3058651
theorem B5437601 : Blo 1909435 5437601 := bstep (se 2 (by rfl) ⟨2039100, by rfl⟩ : syracuseStep 5437601 = 4078201) B4078201
theorem B3625067 : Blo 1909435 3625067 := bstep (se 1 (by rfl) ⟨2718800, by rfl⟩ : syracuseStep 3625067 = 5437601) B5437601
theorem B2416711 : Blo 1909435 2416711 := bstep (se 1 (by rfl) ⟨1812533, by rfl⟩ : syracuseStep 2416711 = 3625067) B3625067
theorem B3222281 : Blo 1909435 3222281 := bstep (se 2 (by rfl) ⟨1208355, by rfl⟩ : syracuseStep 3222281 = 2416711) B2416711
theorem B2148187 : Blo 1909435 2148187 := bstep (se 1 (by rfl) ⟨1611140, by rfl⟩ : syracuseStep 2148187 = 3222281) B3222281
theorem B2864249 : Blo 1909435 2864249 := bstep (se 2 (by rfl) ⟨1074093, by rfl⟩ : syracuseStep 2864249 = 2148187) B2148187
theorem B1909499 : Blo 1909435 1909499 := bstep (se 1 (by rfl) ⟨1432124, by rfl⟩ : syracuseStep 1909499 = 2864249) B2864249
theorem B10322965 : Blo 1909435 10322965 := bbase (se 6 (by rfl) ⟨241944, by rfl⟩ : syracuseStep 10322965 = 483889) (by norm_num)
theorem B13763953 : Blo 1909435 13763953 := bstep (se 2 (by rfl) ⟨5161482, by rfl⟩ : syracuseStep 13763953 = 10322965) B10322965
theorem B18351937 : Blo 1909435 18351937 := bstep (se 2 (by rfl) ⟨6881976, by rfl⟩ : syracuseStep 18351937 = 13763953) B13763953
theorem B24469249 : Blo 1909435 24469249 := bstep (se 2 (by rfl) ⟨9175968, by rfl⟩ : syracuseStep 24469249 = 18351937) B18351937
theorem B32625665 : Blo 1909435 32625665 := bstep (se 2 (by rfl) ⟨12234624, by rfl⟩ : syracuseStep 32625665 = 24469249) B24469249
theorem B21750443 : Blo 1909435 21750443 := bstep (se 1 (by rfl) ⟨16312832, by rfl⟩ : syracuseStep 21750443 = 32625665) B32625665
theorem B14500295 : Blo 1909435 14500295 := bstep (se 1 (by rfl) ⟨10875221, by rfl⟩ : syracuseStep 14500295 = 21750443) B21750443
theorem B9666863 : Blo 1909435 9666863 := bstep (se 1 (by rfl) ⟨7250147, by rfl⟩ : syracuseStep 9666863 = 14500295) B14500295
theorem B6444575 : Blo 1909435 6444575 := bstep (se 1 (by rfl) ⟨4833431, by rfl⟩ : syracuseStep 6444575 = 9666863) B9666863
theorem B4296383 : Blo 1909435 4296383 := bstep (se 1 (by rfl) ⟨3222287, by rfl⟩ : syracuseStep 4296383 = 6444575) B6444575
theorem B2864255 : Blo 1909435 2864255 := bstep (se 1 (by rfl) ⟨2148191, by rfl⟩ : syracuseStep 2864255 = 4296383) B4296383
theorem B1909503 : Blo 1909435 1909503 := bstep (se 1 (by rfl) ⟨1432127, by rfl⟩ : syracuseStep 1909503 = 2864255) B2864255
theorem B2864261 : Blo 1909435 2864261 := bbase (se 4 (by rfl) ⟨268524, by rfl⟩ : syracuseStep 2864261 = 537049) (by norm_num)
theorem B1909507 : Blo 1909435 1909507 := bstep (se 1 (by rfl) ⟨1432130, by rfl⟩ : syracuseStep 1909507 = 2864261) B2864261
theorem B3222301 : Blo 1909435 3222301 := bbase (se 3 (by rfl) ⟨604181, by rfl⟩ : syracuseStep 3222301 = 1208363) (by norm_num)
theorem B4296401 : Blo 1909435 4296401 := bstep (se 2 (by rfl) ⟨1611150, by rfl⟩ : syracuseStep 4296401 = 3222301) B3222301
theorem B2864267 : Blo 1909435 2864267 := bstep (se 1 (by rfl) ⟨2148200, by rfl⟩ : syracuseStep 2864267 = 4296401) B4296401
theorem B1909511 : Blo 1909435 1909511 := bstep (se 1 (by rfl) ⟨1432133, by rfl⟩ : syracuseStep 1909511 = 2864267) B2864267
theorem B2148205 : Blo 1909435 2148205 := bbase (se 3 (by rfl) ⟨402788, by rfl⟩ : syracuseStep 2148205 = 805577) (by norm_num)
theorem B2864273 : Blo 1909435 2864273 := bstep (se 2 (by rfl) ⟨1074102, by rfl⟩ : syracuseStep 2864273 = 2148205) B2148205
theorem B1909515 : Blo 1909435 1909515 := bstep (se 1 (by rfl) ⟨1432136, by rfl⟩ : syracuseStep 1909515 = 2864273) B2864273
theorem B6444629 : Blo 1909435 6444629 := bbase (se 8 (by rfl) ⟨37761, by rfl⟩ : syracuseStep 6444629 = 75523) (by norm_num)
theorem B4296419 : Blo 1909435 4296419 := bstep (se 1 (by rfl) ⟨3222314, by rfl⟩ : syracuseStep 4296419 = 6444629) B6444629
theorem B2864279 : Blo 1909435 2864279 := bstep (se 1 (by rfl) ⟨2148209, by rfl⟩ : syracuseStep 2864279 = 4296419) B4296419
theorem B1909519 : Blo 1909435 1909519 := bstep (se 1 (by rfl) ⟨1432139, by rfl⟩ : syracuseStep 1909519 = 2864279) B2864279
theorem B2864285 : Blo 1909435 2864285 := bbase (se 3 (by rfl) ⟨537053, by rfl⟩ : syracuseStep 2864285 = 1074107) (by norm_num)
theorem B1909523 : Blo 1909435 1909523 := bstep (se 1 (by rfl) ⟨1432142, by rfl⟩ : syracuseStep 1909523 = 2864285) B2864285
theorem B4296437 : Blo 1909435 4296437 := bbase (se 5 (by rfl) ⟨201395, by rfl⟩ : syracuseStep 4296437 = 402791) (by norm_num)
theorem B2864291 : Blo 1909435 2864291 := bstep (se 1 (by rfl) ⟨2148218, by rfl⟩ : syracuseStep 2864291 = 4296437) B4296437
theorem B1909527 : Blo 1909435 1909527 := bstep (se 1 (by rfl) ⟨1432145, by rfl⟩ : syracuseStep 1909527 = 2864291) B2864291
theorem B9301301 : Blo 1909435 9301301 := bbase (se 5 (by rfl) ⟨435998, by rfl⟩ : syracuseStep 9301301 = 871997) (by norm_num)
theorem B6200867 : Blo 1909435 6200867 := bstep (se 1 (by rfl) ⟨4650650, by rfl⟩ : syracuseStep 6200867 = 9301301) B9301301
theorem B4133911 : Blo 1909435 4133911 := bstep (se 1 (by rfl) ⟨3100433, by rfl⟩ : syracuseStep 4133911 = 6200867) B6200867
theorem B5511881 : Blo 1909435 5511881 := bstep (se 2 (by rfl) ⟨2066955, by rfl⟩ : syracuseStep 5511881 = 4133911) B4133911
theorem B14698349 : Blo 1909435 14698349 := bstep (se 3 (by rfl) ⟨2755940, by rfl⟩ : syracuseStep 14698349 = 5511881) B5511881
theorem B9798899 : Blo 1909435 9798899 := bstep (se 1 (by rfl) ⟨7349174, by rfl⟩ : syracuseStep 9798899 = 14698349) B14698349
theorem B26130397 : Blo 1909435 26130397 := bstep (se 3 (by rfl) ⟨4899449, by rfl⟩ : syracuseStep 26130397 = 9798899) B9798899
theorem B34840529 : Blo 1909435 34840529 := bstep (se 2 (by rfl) ⟨13065198, by rfl⟩ : syracuseStep 34840529 = 26130397) B26130397
theorem B23227019 : Blo 1909435 23227019 := bstep (se 1 (by rfl) ⟨17420264, by rfl⟩ : syracuseStep 23227019 = 34840529) B34840529
theorem B15484679 : Blo 1909435 15484679 := bstep (se 1 (by rfl) ⟨11613509, by rfl⟩ : syracuseStep 15484679 = 23227019) B23227019
theorem B10323119 : Blo 1909435 10323119 := bstep (se 1 (by rfl) ⟨7742339, by rfl⟩ : syracuseStep 10323119 = 15484679) B15484679
theorem B6882079 : Blo 1909435 6882079 := bstep (se 1 (by rfl) ⟨5161559, by rfl⟩ : syracuseStep 6882079 = 10323119) B10323119
theorem B9176105 : Blo 1909435 9176105 := bstep (se 2 (by rfl) ⟨3441039, by rfl⟩ : syracuseStep 9176105 = 6882079) B6882079
theorem B24469613 : Blo 1909435 24469613 := bstep (se 3 (by rfl) ⟨4588052, by rfl⟩ : syracuseStep 24469613 = 9176105) B9176105
theorem B16313075 : Blo 1909435 16313075 := bstep (se 1 (by rfl) ⟨12234806, by rfl⟩ : syracuseStep 16313075 = 24469613) B24469613
theorem B10875383 : Blo 1909435 10875383 := bstep (se 1 (by rfl) ⟨8156537, by rfl⟩ : syracuseStep 10875383 = 16313075) B16313075
theorem B7250255 : Blo 1909435 7250255 := bstep (se 1 (by rfl) ⟨5437691, by rfl⟩ : syracuseStep 7250255 = 10875383) B10875383
theorem B4833503 : Blo 1909435 4833503 := bstep (se 1 (by rfl) ⟨3625127, by rfl⟩ : syracuseStep 4833503 = 7250255) B7250255
theorem B3222335 : Blo 1909435 3222335 := bstep (se 1 (by rfl) ⟨2416751, by rfl⟩ : syracuseStep 3222335 = 4833503) B4833503
theorem B2148223 : Blo 1909435 2148223 := bstep (se 1 (by rfl) ⟨1611167, by rfl⟩ : syracuseStep 2148223 = 3222335) B3222335
theorem B2864297 : Blo 1909435 2864297 := bstep (se 2 (by rfl) ⟨1074111, by rfl⟩ : syracuseStep 2864297 = 2148223) B2148223
theorem B1909531 : Blo 1909435 1909531 := bstep (se 1 (by rfl) ⟨1432148, by rfl⟩ : syracuseStep 1909531 = 2864297) B2864297
theorem B4078277 : Blo 1909435 4078277 := bbase (se 4 (by rfl) ⟨382338, by rfl⟩ : syracuseStep 4078277 = 764677) (by norm_num)
theorem B2718851 : Blo 1909435 2718851 := bstep (se 1 (by rfl) ⟨2039138, by rfl⟩ : syracuseStep 2718851 = 4078277) B4078277
theorem B7250269 : Blo 1909435 7250269 := bstep (se 3 (by rfl) ⟨1359425, by rfl⟩ : syracuseStep 7250269 = 2718851) B2718851
theorem B9667025 : Blo 1909435 9667025 := bstep (se 2 (by rfl) ⟨3625134, by rfl⟩ : syracuseStep 9667025 = 7250269) B7250269
theorem B6444683 : Blo 1909435 6444683 := bstep (se 1 (by rfl) ⟨4833512, by rfl⟩ : syracuseStep 6444683 = 9667025) B9667025
theorem B4296455 : Blo 1909435 4296455 := bstep (se 1 (by rfl) ⟨3222341, by rfl⟩ : syracuseStep 4296455 = 6444683) B6444683
theorem B2864303 : Blo 1909435 2864303 := bstep (se 1 (by rfl) ⟨2148227, by rfl⟩ : syracuseStep 2864303 = 4296455) B4296455
theorem B1909535 : Blo 1909435 1909535 := bstep (se 1 (by rfl) ⟨1432151, by rfl⟩ : syracuseStep 1909535 = 2864303) B2864303
theorem B2864309 : Blo 1909435 2864309 := bbase (se 5 (by rfl) ⟨134264, by rfl⟩ : syracuseStep 2864309 = 268529) (by norm_num)
theorem B1909539 : Blo 1909435 1909539 := bstep (se 1 (by rfl) ⟨1432154, by rfl⟩ : syracuseStep 1909539 = 2864309) B2864309
theorem B4833533 : Blo 1909435 4833533 := bbase (se 3 (by rfl) ⟨906287, by rfl⟩ : syracuseStep 4833533 = 1812575) (by norm_num)
theorem B3222355 : Blo 1909435 3222355 := bstep (se 1 (by rfl) ⟨2416766, by rfl⟩ : syracuseStep 3222355 = 4833533) B4833533
theorem B4296473 : Blo 1909435 4296473 := bstep (se 2 (by rfl) ⟨1611177, by rfl⟩ : syracuseStep 4296473 = 3222355) B3222355
theorem B2864315 : Blo 1909435 2864315 := bstep (se 1 (by rfl) ⟨2148236, by rfl⟩ : syracuseStep 2864315 = 4296473) B4296473
theorem B1909543 : Blo 1909435 1909543 := bstep (se 1 (by rfl) ⟨1432157, by rfl⟩ : syracuseStep 1909543 = 2864315) B2864315
theorem B2148241 : Blo 1909435 2148241 := bbase (se 2 (by rfl) ⟨805590, by rfl⟩ : syracuseStep 2148241 = 1611181) (by norm_num)
theorem B2864321 : Blo 1909435 2864321 := bstep (se 2 (by rfl) ⟨1074120, by rfl⟩ : syracuseStep 2864321 = 2148241) B2148241
theorem B1909547 : Blo 1909435 1909547 := bstep (se 1 (by rfl) ⟨1432160, by rfl⟩ : syracuseStep 1909547 = 2864321) B2864321
theorem B3625165 : Blo 1909435 3625165 := bbase (se 3 (by rfl) ⟨679718, by rfl⟩ : syracuseStep 3625165 = 1359437) (by norm_num)
theorem B4833553 : Blo 1909435 4833553 := bstep (se 2 (by rfl) ⟨1812582, by rfl⟩ : syracuseStep 4833553 = 3625165) B3625165
theorem B6444737 : Blo 1909435 6444737 := bstep (se 2 (by rfl) ⟨2416776, by rfl⟩ : syracuseStep 6444737 = 4833553) B4833553
theorem B4296491 : Blo 1909435 4296491 := bstep (se 1 (by rfl) ⟨3222368, by rfl⟩ : syracuseStep 4296491 = 6444737) B6444737
theorem B2864327 : Blo 1909435 2864327 := bstep (se 1 (by rfl) ⟨2148245, by rfl⟩ : syracuseStep 2864327 = 4296491) B4296491
theorem B1909551 : Blo 1909435 1909551 := bstep (se 1 (by rfl) ⟨1432163, by rfl⟩ : syracuseStep 1909551 = 2864327) B2864327
theorem B2864333 : Blo 1909435 2864333 := bbase (se 3 (by rfl) ⟨537062, by rfl⟩ : syracuseStep 2864333 = 1074125) (by norm_num)
theorem B1909555 : Blo 1909435 1909555 := bstep (se 1 (by rfl) ⟨1432166, by rfl⟩ : syracuseStep 1909555 = 2864333) B2864333
theorem B4296509 : Blo 1909435 4296509 := bbase (se 3 (by rfl) ⟨805595, by rfl⟩ : syracuseStep 4296509 = 1611191) (by norm_num)
theorem B2864339 : Blo 1909435 2864339 := bstep (se 1 (by rfl) ⟨2148254, by rfl⟩ : syracuseStep 2864339 = 4296509) B4296509
theorem B1909559 : Blo 1909435 1909559 := bstep (se 1 (by rfl) ⟨1432169, by rfl⟩ : syracuseStep 1909559 = 2864339) B2864339
theorem B3222389 : Blo 1909435 3222389 := bbase (se 5 (by rfl) ⟨151049, by rfl⟩ : syracuseStep 3222389 = 302099) (by norm_num)
theorem B2148259 : Blo 1909435 2148259 := bstep (se 1 (by rfl) ⟨1611194, by rfl⟩ : syracuseStep 2148259 = 3222389) B3222389
theorem B2864345 : Blo 1909435 2864345 := bstep (se 2 (by rfl) ⟨1074129, by rfl⟩ : syracuseStep 2864345 = 2148259) B2148259
theorem B1909563 : Blo 1909435 1909563 := bstep (se 1 (by rfl) ⟨1432172, by rfl⟩ : syracuseStep 1909563 = 2864345) B2864345
theorem B4355149 : Blo 1909435 4355149 := bbase (se 3 (by rfl) ⟨816590, by rfl⟩ : syracuseStep 4355149 = 1633181) (by norm_num)
theorem B5806865 : Blo 1909435 5806865 := bstep (se 2 (by rfl) ⟨2177574, by rfl⟩ : syracuseStep 5806865 = 4355149) B4355149
theorem B3871243 : Blo 1909435 3871243 := bstep (se 1 (by rfl) ⟨2903432, by rfl⟩ : syracuseStep 3871243 = 5806865) B5806865
theorem B5161657 : Blo 1909435 5161657 := bstep (se 2 (by rfl) ⟨1935621, by rfl⟩ : syracuseStep 5161657 = 3871243) B3871243
theorem B6882209 : Blo 1909435 6882209 := bstep (se 2 (by rfl) ⟨2580828, by rfl⟩ : syracuseStep 6882209 = 5161657) B5161657
theorem B4588139 : Blo 1909435 4588139 := bstep (se 1 (by rfl) ⟨3441104, by rfl⟩ : syracuseStep 4588139 = 6882209) B6882209
theorem B3058759 : Blo 1909435 3058759 := bstep (se 1 (by rfl) ⟨2294069, by rfl⟩ : syracuseStep 3058759 = 4588139) B4588139
theorem B4078345 : Blo 1909435 4078345 := bstep (se 2 (by rfl) ⟨1529379, by rfl⟩ : syracuseStep 4078345 = 3058759) B3058759
theorem B5437793 : Blo 1909435 5437793 := bstep (se 2 (by rfl) ⟨2039172, by rfl⟩ : syracuseStep 5437793 = 4078345) B4078345
theorem B14500781 : Blo 1909435 14500781 := bstep (se 3 (by rfl) ⟨2718896, by rfl⟩ : syracuseStep 14500781 = 5437793) B5437793
theorem B9667187 : Blo 1909435 9667187 := bstep (se 1 (by rfl) ⟨7250390, by rfl⟩ : syracuseStep 9667187 = 14500781) B14500781
theorem B6444791 : Blo 1909435 6444791 := bstep (se 1 (by rfl) ⟨4833593, by rfl⟩ : syracuseStep 6444791 = 9667187) B9667187
theorem B4296527 : Blo 1909435 4296527 := bstep (se 1 (by rfl) ⟨3222395, by rfl⟩ : syracuseStep 4296527 = 6444791) B6444791
theorem B2864351 : Blo 1909435 2864351 := bstep (se 1 (by rfl) ⟨2148263, by rfl⟩ : syracuseStep 2864351 = 4296527) B4296527
theorem B1909567 : Blo 1909435 1909567 := bstep (se 1 (by rfl) ⟨1432175, by rfl⟩ : syracuseStep 1909567 = 2864351) B2864351
theorem B2864357 : Blo 1909435 2864357 := bbase (se 4 (by rfl) ⟨268533, by rfl⟩ : syracuseStep 2864357 = 537067) (by norm_num)
theorem B1909571 : Blo 1909435 1909571 := bstep (se 1 (by rfl) ⟨1432178, by rfl⟩ : syracuseStep 1909571 = 2864357) B2864357
theorem B8829173 : Blo 1909435 8829173 := bbase (se 5 (by rfl) ⟨413867, by rfl⟩ : syracuseStep 8829173 = 827735) (by norm_num)
theorem B23544461 : Blo 1909435 23544461 := bstep (se 3 (by rfl) ⟨4414586, by rfl⟩ : syracuseStep 23544461 = 8829173) B8829173
theorem B15696307 : Blo 1909435 15696307 := bstep (se 1 (by rfl) ⟨11772230, by rfl⟩ : syracuseStep 15696307 = 23544461) B23544461
theorem B83713637 : Blo 1909435 83713637 := bstep (se 4 (by rfl) ⟨7848153, by rfl⟩ : syracuseStep 83713637 = 15696307) B15696307
theorem B55809091 : Blo 1909435 55809091 := bstep (se 1 (by rfl) ⟨41856818, by rfl⟩ : syracuseStep 55809091 = 83713637) B83713637
theorem B74412121 : Blo 1909435 74412121 := bstep (se 2 (by rfl) ⟨27904545, by rfl⟩ : syracuseStep 74412121 = 55809091) B55809091
theorem B99216161 : Blo 1909435 99216161 := bstep (se 2 (by rfl) ⟨37206060, by rfl⟩ : syracuseStep 99216161 = 74412121) B74412121
theorem B66144107 : Blo 1909435 66144107 := bstep (se 1 (by rfl) ⟨49608080, by rfl⟩ : syracuseStep 66144107 = 99216161) B99216161
theorem B44096071 : Blo 1909435 44096071 := bstep (se 1 (by rfl) ⟨33072053, by rfl⟩ : syracuseStep 44096071 = 66144107) B66144107
theorem B58794761 : Blo 1909435 58794761 := bstep (se 2 (by rfl) ⟨22048035, by rfl⟩ : syracuseStep 58794761 = 44096071) B44096071
theorem B39196507 : Blo 1909435 39196507 := bstep (se 1 (by rfl) ⟨29397380, by rfl⟩ : syracuseStep 39196507 = 58794761) B58794761
theorem B52262009 : Blo 1909435 52262009 := bstep (se 2 (by rfl) ⟨19598253, by rfl⟩ : syracuseStep 52262009 = 39196507) B39196507
theorem B34841339 : Blo 1909435 34841339 := bstep (se 1 (by rfl) ⟨26131004, by rfl⟩ : syracuseStep 34841339 = 52262009) B52262009
theorem B23227559 : Blo 1909435 23227559 := bstep (se 1 (by rfl) ⟨17420669, by rfl⟩ : syracuseStep 23227559 = 34841339) B34841339
theorem B15485039 : Blo 1909435 15485039 := bstep (se 1 (by rfl) ⟨11613779, by rfl⟩ : syracuseStep 15485039 = 23227559) B23227559
theorem B10323359 : Blo 1909435 10323359 := bstep (se 1 (by rfl) ⟨7742519, by rfl⟩ : syracuseStep 10323359 = 15485039) B15485039
theorem B6882239 : Blo 1909435 6882239 := bstep (se 1 (by rfl) ⟨5161679, by rfl⟩ : syracuseStep 6882239 = 10323359) B10323359
theorem B4588159 : Blo 1909435 4588159 := bstep (se 1 (by rfl) ⟨3441119, by rfl⟩ : syracuseStep 4588159 = 6882239) B6882239
theorem B6117545 : Blo 1909435 6117545 := bstep (se 2 (by rfl) ⟨2294079, by rfl⟩ : syracuseStep 6117545 = 4588159) B4588159
theorem B4078363 : Blo 1909435 4078363 := bstep (se 1 (by rfl) ⟨3058772, by rfl⟩ : syracuseStep 4078363 = 6117545) B6117545
theorem B5437817 : Blo 1909435 5437817 := bstep (se 2 (by rfl) ⟨2039181, by rfl⟩ : syracuseStep 5437817 = 4078363) B4078363
theorem B3625211 : Blo 1909435 3625211 := bstep (se 1 (by rfl) ⟨2718908, by rfl⟩ : syracuseStep 3625211 = 5437817) B5437817
theorem B2416807 : Blo 1909435 2416807 := bstep (se 1 (by rfl) ⟨1812605, by rfl⟩ : syracuseStep 2416807 = 3625211) B3625211
theorem B3222409 : Blo 1909435 3222409 := bstep (se 2 (by rfl) ⟨1208403, by rfl⟩ : syracuseStep 3222409 = 2416807) B2416807
theorem B4296545 : Blo 1909435 4296545 := bstep (se 2 (by rfl) ⟨1611204, by rfl⟩ : syracuseStep 4296545 = 3222409) B3222409
theorem B2864363 : Blo 1909435 2864363 := bstep (se 1 (by rfl) ⟨2148272, by rfl⟩ : syracuseStep 2864363 = 4296545) B4296545
theorem B1909575 : Blo 1909435 1909575 := bstep (se 1 (by rfl) ⟨1432181, by rfl⟩ : syracuseStep 1909575 = 2864363) B2864363
theorem B2148277 : Blo 1909435 2148277 := bbase (se 5 (by rfl) ⟨100700, by rfl⟩ : syracuseStep 2148277 = 201401) (by norm_num)
theorem B2864369 : Blo 1909435 2864369 := bstep (se 2 (by rfl) ⟨1074138, by rfl⟩ : syracuseStep 2864369 = 2148277) B2148277
theorem B1909579 : Blo 1909435 1909579 := bstep (se 1 (by rfl) ⟨1432184, by rfl⟩ : syracuseStep 1909579 = 2864369) B2864369
theorem B2416817 : Blo 1909435 2416817 := bbase (se 2 (by rfl) ⟨906306, by rfl⟩ : syracuseStep 2416817 = 1812613) (by norm_num)
theorem B6444845 : Blo 1909435 6444845 := bstep (se 3 (by rfl) ⟨1208408, by rfl⟩ : syracuseStep 6444845 = 2416817) B2416817
theorem B4296563 : Blo 1909435 4296563 := bstep (se 1 (by rfl) ⟨3222422, by rfl⟩ : syracuseStep 4296563 = 6444845) B6444845
theorem B2864375 : Blo 1909435 2864375 := bstep (se 1 (by rfl) ⟨2148281, by rfl⟩ : syracuseStep 2864375 = 4296563) B4296563
theorem B1909583 : Blo 1909435 1909583 := bstep (se 1 (by rfl) ⟨1432187, by rfl⟩ : syracuseStep 1909583 = 2864375) B2864375
theorem B2864381 : Blo 1909435 2864381 := bbase (se 3 (by rfl) ⟨537071, by rfl⟩ : syracuseStep 2864381 = 1074143) (by norm_num)
theorem B1909587 : Blo 1909435 1909587 := bstep (se 1 (by rfl) ⟨1432190, by rfl⟩ : syracuseStep 1909587 = 2864381) B2864381
theorem B4296581 : Blo 1909435 4296581 := bbase (se 4 (by rfl) ⟨402804, by rfl⟩ : syracuseStep 4296581 = 805609) (by norm_num)
theorem B2864387 : Blo 1909435 2864387 := bstep (se 1 (by rfl) ⟨2148290, by rfl⟩ : syracuseStep 2864387 = 4296581) B4296581
theorem B1909591 : Blo 1909435 1909591 := bstep (se 1 (by rfl) ⟨1432193, by rfl⟩ : syracuseStep 1909591 = 2864387) B2864387
theorem B3058805 : Blo 1909435 3058805 := bbase (se 5 (by rfl) ⟨143381, by rfl⟩ : syracuseStep 3058805 = 286763) (by norm_num)
theorem B2039203 : Blo 1909435 2039203 := bstep (se 1 (by rfl) ⟨1529402, by rfl⟩ : syracuseStep 2039203 = 3058805) B3058805
theorem B2718937 : Blo 1909435 2718937 := bstep (se 2 (by rfl) ⟨1019601, by rfl⟩ : syracuseStep 2718937 = 2039203) B2039203
theorem B3625249 : Blo 1909435 3625249 := bstep (se 2 (by rfl) ⟨1359468, by rfl⟩ : syracuseStep 3625249 = 2718937) B2718937
theorem B4833665 : Blo 1909435 4833665 := bstep (se 2 (by rfl) ⟨1812624, by rfl⟩ : syracuseStep 4833665 = 3625249) B3625249
theorem B3222443 : Blo 1909435 3222443 := bstep (se 1 (by rfl) ⟨2416832, by rfl⟩ : syracuseStep 3222443 = 4833665) B4833665
theorem B2148295 : Blo 1909435 2148295 := bstep (se 1 (by rfl) ⟨1611221, by rfl⟩ : syracuseStep 2148295 = 3222443) B3222443
theorem B2864393 : Blo 1909435 2864393 := bstep (se 2 (by rfl) ⟨1074147, by rfl⟩ : syracuseStep 2864393 = 2148295) B2148295
theorem B1909595 : Blo 1909435 1909595 := bstep (se 1 (by rfl) ⟨1432196, by rfl⟩ : syracuseStep 1909595 = 2864393) B2864393
theorem B9667349 : Blo 1909435 9667349 := bbase (se 6 (by rfl) ⟨226578, by rfl⟩ : syracuseStep 9667349 = 453157) (by norm_num)
theorem B6444899 : Blo 1909435 6444899 := bstep (se 1 (by rfl) ⟨4833674, by rfl⟩ : syracuseStep 6444899 = 9667349) B9667349
theorem B4296599 : Blo 1909435 4296599 := bstep (se 1 (by rfl) ⟨3222449, by rfl⟩ : syracuseStep 4296599 = 6444899) B6444899
theorem B2864399 : Blo 1909435 2864399 := bstep (se 1 (by rfl) ⟨2148299, by rfl⟩ : syracuseStep 2864399 = 4296599) B4296599
theorem B1909599 : Blo 1909435 1909599 := bstep (se 1 (by rfl) ⟨1432199, by rfl⟩ : syracuseStep 1909599 = 2864399) B2864399
theorem B2864405 : Blo 1909435 2864405 := bbase (se 6 (by rfl) ⟨67134, by rfl⟩ : syracuseStep 2864405 = 134269) (by norm_num)
theorem B1909603 : Blo 1909435 1909603 := bstep (se 1 (by rfl) ⟨1432202, by rfl⟩ : syracuseStep 1909603 = 2864405) B2864405
theorem B2651789 : Blo 1909435 2651789 := bbase (se 3 (by rfl) ⟨497210, by rfl⟩ : syracuseStep 2651789 = 994421) (by norm_num)
theorem B7071437 : Blo 1909435 7071437 := bstep (se 3 (by rfl) ⟨1325894, by rfl⟩ : syracuseStep 7071437 = 2651789) B2651789
theorem B4714291 : Blo 1909435 4714291 := bstep (se 1 (by rfl) ⟨3535718, by rfl⟩ : syracuseStep 4714291 = 7071437) B7071437
theorem B6285721 : Blo 1909435 6285721 := bstep (se 2 (by rfl) ⟨2357145, by rfl⟩ : syracuseStep 6285721 = 4714291) B4714291
theorem B8380961 : Blo 1909435 8380961 := bstep (se 2 (by rfl) ⟨3142860, by rfl⟩ : syracuseStep 8380961 = 6285721) B6285721
theorem B5587307 : Blo 1909435 5587307 := bstep (se 1 (by rfl) ⟨4190480, by rfl⟩ : syracuseStep 5587307 = 8380961) B8380961
theorem B3724871 : Blo 1909435 3724871 := bstep (se 1 (by rfl) ⟨2793653, by rfl⟩ : syracuseStep 3724871 = 5587307) B5587307
theorem B9932989 : Blo 1909435 9932989 := bstep (se 3 (by rfl) ⟨1862435, by rfl⟩ : syracuseStep 9932989 = 3724871) B3724871
theorem B13243985 : Blo 1909435 13243985 := bstep (se 2 (by rfl) ⟨4966494, by rfl⟩ : syracuseStep 13243985 = 9932989) B9932989
theorem B8829323 : Blo 1909435 8829323 := bstep (se 1 (by rfl) ⟨6621992, by rfl⟩ : syracuseStep 8829323 = 13243985) B13243985
theorem B5886215 : Blo 1909435 5886215 := bstep (se 1 (by rfl) ⟨4414661, by rfl⟩ : syracuseStep 5886215 = 8829323) B8829323
theorem B3924143 : Blo 1909435 3924143 := bstep (se 1 (by rfl) ⟨2943107, by rfl⟩ : syracuseStep 3924143 = 5886215) B5886215
theorem B2616095 : Blo 1909435 2616095 := bstep (se 1 (by rfl) ⟨1962071, by rfl⟩ : syracuseStep 2616095 = 3924143) B3924143
theorem B6976253 : Blo 1909435 6976253 := bstep (se 3 (by rfl) ⟨1308047, by rfl⟩ : syracuseStep 6976253 = 2616095) B2616095
theorem B18603341 : Blo 1909435 18603341 := bstep (se 3 (by rfl) ⟨3488126, by rfl⟩ : syracuseStep 18603341 = 6976253) B6976253
theorem B12402227 : Blo 1909435 12402227 := bstep (se 1 (by rfl) ⟨9301670, by rfl⟩ : syracuseStep 12402227 = 18603341) B18603341
theorem B8268151 : Blo 1909435 8268151 := bstep (se 1 (by rfl) ⟨6201113, by rfl⟩ : syracuseStep 8268151 = 12402227) B12402227
theorem B11024201 : Blo 1909435 11024201 := bstep (se 2 (by rfl) ⟨4134075, by rfl⟩ : syracuseStep 11024201 = 8268151) B8268151
theorem B7349467 : Blo 1909435 7349467 := bstep (se 1 (by rfl) ⟨5512100, by rfl⟩ : syracuseStep 7349467 = 11024201) B11024201
theorem B9799289 : Blo 1909435 9799289 := bstep (se 2 (by rfl) ⟨3674733, by rfl⟩ : syracuseStep 9799289 = 7349467) B7349467
theorem B6532859 : Blo 1909435 6532859 := bstep (se 1 (by rfl) ⟨4899644, by rfl⟩ : syracuseStep 6532859 = 9799289) B9799289
theorem B4355239 : Blo 1909435 4355239 := bstep (se 1 (by rfl) ⟨3266429, by rfl⟩ : syracuseStep 4355239 = 6532859) B6532859
theorem B5806985 : Blo 1909435 5806985 := bstep (se 2 (by rfl) ⟨2177619, by rfl⟩ : syracuseStep 5806985 = 4355239) B4355239
theorem B15485293 : Blo 1909435 15485293 := bstep (se 3 (by rfl) ⟨2903492, by rfl⟩ : syracuseStep 15485293 = 5806985) B5806985
theorem B20647057 : Blo 1909435 20647057 := bstep (se 2 (by rfl) ⟨7742646, by rfl⟩ : syracuseStep 20647057 = 15485293) B15485293
theorem B27529409 : Blo 1909435 27529409 := bstep (se 2 (by rfl) ⟨10323528, by rfl⟩ : syracuseStep 27529409 = 20647057) B20647057
theorem B18352939 : Blo 1909435 18352939 := bstep (se 1 (by rfl) ⟨13764704, by rfl⟩ : syracuseStep 18352939 = 27529409) B27529409
theorem B24470585 : Blo 1909435 24470585 := bstep (se 2 (by rfl) ⟨9176469, by rfl⟩ : syracuseStep 24470585 = 18352939) B18352939
theorem B16313723 : Blo 1909435 16313723 := bstep (se 1 (by rfl) ⟨12235292, by rfl⟩ : syracuseStep 16313723 = 24470585) B24470585
theorem B10875815 : Blo 1909435 10875815 := bstep (se 1 (by rfl) ⟨8156861, by rfl⟩ : syracuseStep 10875815 = 16313723) B16313723
theorem B7250543 : Blo 1909435 7250543 := bstep (se 1 (by rfl) ⟨5437907, by rfl⟩ : syracuseStep 7250543 = 10875815) B10875815
theorem B4833695 : Blo 1909435 4833695 := bstep (se 1 (by rfl) ⟨3625271, by rfl⟩ : syracuseStep 4833695 = 7250543) B7250543
theorem B3222463 : Blo 1909435 3222463 := bstep (se 1 (by rfl) ⟨2416847, by rfl⟩ : syracuseStep 3222463 = 4833695) B4833695
theorem B4296617 : Blo 1909435 4296617 := bstep (se 2 (by rfl) ⟨1611231, by rfl⟩ : syracuseStep 4296617 = 3222463) B3222463
theorem B2864411 : Blo 1909435 2864411 := bstep (se 1 (by rfl) ⟨2148308, by rfl⟩ : syracuseStep 2864411 = 4296617) B4296617
theorem B1909607 : Blo 1909435 1909607 := bstep (se 1 (by rfl) ⟨1432205, by rfl⟩ : syracuseStep 1909607 = 2864411) B2864411
theorem B2148313 : Blo 1909435 2148313 := bbase (se 2 (by rfl) ⟨805617, by rfl⟩ : syracuseStep 2148313 = 1611235) (by norm_num)
theorem B2864417 : Blo 1909435 2864417 := bstep (se 2 (by rfl) ⟨1074156, by rfl⟩ : syracuseStep 2864417 = 2148313) B2148313
theorem B1909611 : Blo 1909435 1909611 := bstep (se 1 (by rfl) ⟨1432208, by rfl⟩ : syracuseStep 1909611 = 2864417) B2864417
theorem B2718965 : Blo 1909435 2718965 := bbase (se 5 (by rfl) ⟨127451, by rfl⟩ : syracuseStep 2718965 = 254903) (by norm_num)
theorem B7250573 : Blo 1909435 7250573 := bstep (se 3 (by rfl) ⟨1359482, by rfl⟩ : syracuseStep 7250573 = 2718965) B2718965
theorem B4833715 : Blo 1909435 4833715 := bstep (se 1 (by rfl) ⟨3625286, by rfl⟩ : syracuseStep 4833715 = 7250573) B7250573
theorem B6444953 : Blo 1909435 6444953 := bstep (se 2 (by rfl) ⟨2416857, by rfl⟩ : syracuseStep 6444953 = 4833715) B4833715
theorem B4296635 : Blo 1909435 4296635 := bstep (se 1 (by rfl) ⟨3222476, by rfl⟩ : syracuseStep 4296635 = 6444953) B6444953
theorem B2864423 : Blo 1909435 2864423 := bstep (se 1 (by rfl) ⟨2148317, by rfl⟩ : syracuseStep 2864423 = 4296635) B4296635
theorem B1909615 : Blo 1909435 1909615 := bstep (se 1 (by rfl) ⟨1432211, by rfl⟩ : syracuseStep 1909615 = 2864423) B2864423
theorem B2864429 : Blo 1909435 2864429 := bbase (se 3 (by rfl) ⟨537080, by rfl⟩ : syracuseStep 2864429 = 1074161) (by norm_num)
theorem B1909619 : Blo 1909435 1909619 := bstep (se 1 (by rfl) ⟨1432214, by rfl⟩ : syracuseStep 1909619 = 2864429) B2864429
theorem B4296653 : Blo 1909435 4296653 := bbase (se 3 (by rfl) ⟨805622, by rfl⟩ : syracuseStep 4296653 = 1611245) (by norm_num)
theorem B2864435 : Blo 1909435 2864435 := bstep (se 1 (by rfl) ⟨2148326, by rfl⟩ : syracuseStep 2864435 = 4296653) B4296653
theorem B1909623 : Blo 1909435 1909623 := bstep (se 1 (by rfl) ⟨1432217, by rfl⟩ : syracuseStep 1909623 = 2864435) B2864435
theorem B2416873 : Blo 1909435 2416873 := bbase (se 2 (by rfl) ⟨906327, by rfl⟩ : syracuseStep 2416873 = 1812655) (by norm_num)
theorem B3222497 : Blo 1909435 3222497 := bstep (se 2 (by rfl) ⟨1208436, by rfl⟩ : syracuseStep 3222497 = 2416873) B2416873
theorem B2148331 : Blo 1909435 2148331 := bstep (se 1 (by rfl) ⟨1611248, by rfl⟩ : syracuseStep 2148331 = 3222497) B3222497
theorem B2864441 : Blo 1909435 2864441 := bstep (se 2 (by rfl) ⟨1074165, by rfl⟩ : syracuseStep 2864441 = 2148331) B2148331
theorem B1909627 : Blo 1909435 1909627 := bstep (se 1 (by rfl) ⟨1432220, by rfl⟩ : syracuseStep 1909627 = 2864441) B2864441
theorem B12235445 : Blo 1909435 12235445 := bbase (se 5 (by rfl) ⟨573536, by rfl⟩ : syracuseStep 12235445 = 1147073) (by norm_num)
theorem B8156963 : Blo 1909435 8156963 := bstep (se 1 (by rfl) ⟨6117722, by rfl⟩ : syracuseStep 8156963 = 12235445) B12235445
theorem B21751901 : Blo 1909435 21751901 := bstep (se 3 (by rfl) ⟨4078481, by rfl⟩ : syracuseStep 21751901 = 8156963) B8156963
theorem B14501267 : Blo 1909435 14501267 := bstep (se 1 (by rfl) ⟨10875950, by rfl⟩ : syracuseStep 14501267 = 21751901) B21751901
theorem B9667511 : Blo 1909435 9667511 := bstep (se 1 (by rfl) ⟨7250633, by rfl⟩ : syracuseStep 9667511 = 14501267) B14501267
theorem B6445007 : Blo 1909435 6445007 := bstep (se 1 (by rfl) ⟨4833755, by rfl⟩ : syracuseStep 6445007 = 9667511) B9667511
theorem B4296671 : Blo 1909435 4296671 := bstep (se 1 (by rfl) ⟨3222503, by rfl⟩ : syracuseStep 4296671 = 6445007) B6445007
theorem B2864447 : Blo 1909435 2864447 := bstep (se 1 (by rfl) ⟨2148335, by rfl⟩ : syracuseStep 2864447 = 4296671) B4296671
theorem B1909631 : Blo 1909435 1909631 := bstep (se 1 (by rfl) ⟨1432223, by rfl⟩ : syracuseStep 1909631 = 2864447) B2864447
theorem B2864453 : Blo 1909435 2864453 := bbase (se 4 (by rfl) ⟨268542, by rfl⟩ : syracuseStep 2864453 = 537085) (by norm_num)
theorem B1909635 : Blo 1909435 1909635 := bstep (se 1 (by rfl) ⟨1432226, by rfl⟩ : syracuseStep 1909635 = 2864453) B2864453
theorem B3222517 : Blo 1909435 3222517 := bbase (se 5 (by rfl) ⟨151055, by rfl⟩ : syracuseStep 3222517 = 302111) (by norm_num)
theorem B4296689 : Blo 1909435 4296689 := bstep (se 2 (by rfl) ⟨1611258, by rfl⟩ : syracuseStep 4296689 = 3222517) B3222517
theorem B2864459 : Blo 1909435 2864459 := bstep (se 1 (by rfl) ⟨2148344, by rfl⟩ : syracuseStep 2864459 = 4296689) B4296689
theorem B1909639 : Blo 1909435 1909639 := bstep (se 1 (by rfl) ⟨1432229, by rfl⟩ : syracuseStep 1909639 = 2864459) B2864459
theorem B2148349 : Blo 1909435 2148349 := bbase (se 3 (by rfl) ⟨402815, by rfl⟩ : syracuseStep 2148349 = 805631) (by norm_num)
theorem B2864465 : Blo 1909435 2864465 := bstep (se 2 (by rfl) ⟨1074174, by rfl⟩ : syracuseStep 2864465 = 2148349) B2148349
theorem B1909643 : Blo 1909435 1909643 := bstep (se 1 (by rfl) ⟨1432232, by rfl⟩ : syracuseStep 1909643 = 2864465) B2864465
theorem B6445061 : Blo 1909435 6445061 := bbase (se 4 (by rfl) ⟨604224, by rfl⟩ : syracuseStep 6445061 = 1208449) (by norm_num)
theorem B4296707 : Blo 1909435 4296707 := bstep (se 1 (by rfl) ⟨3222530, by rfl⟩ : syracuseStep 4296707 = 6445061) B6445061
theorem B2864471 : Blo 1909435 2864471 := bstep (se 1 (by rfl) ⟨2148353, by rfl⟩ : syracuseStep 2864471 = 4296707) B4296707
theorem B1909647 : Blo 1909435 1909647 := bstep (se 1 (by rfl) ⟨1432235, by rfl⟩ : syracuseStep 1909647 = 2864471) B2864471
theorem B2864477 : Blo 1909435 2864477 := bbase (se 3 (by rfl) ⟨537089, by rfl⟩ : syracuseStep 2864477 = 1074179) (by norm_num)
theorem B1909651 : Blo 1909435 1909651 := bstep (se 1 (by rfl) ⟨1432238, by rfl⟩ : syracuseStep 1909651 = 2864477) B2864477
theorem B4296725 : Blo 1909435 4296725 := bbase (se 6 (by rfl) ⟨100704, by rfl⟩ : syracuseStep 4296725 = 201409) (by norm_num)
theorem B2864483 : Blo 1909435 2864483 := bstep (se 1 (by rfl) ⟨2148362, by rfl⟩ : syracuseStep 2864483 = 4296725) B4296725
theorem B1909655 : Blo 1909435 1909655 := bstep (se 1 (by rfl) ⟨1432241, by rfl⟩ : syracuseStep 1909655 = 2864483) B2864483
theorem B7250741 : Blo 1909435 7250741 := bbase (se 5 (by rfl) ⟨339878, by rfl⟩ : syracuseStep 7250741 = 679757) (by norm_num)
theorem B4833827 : Blo 1909435 4833827 := bstep (se 1 (by rfl) ⟨3625370, by rfl⟩ : syracuseStep 4833827 = 7250741) B7250741
theorem B3222551 : Blo 1909435 3222551 := bstep (se 1 (by rfl) ⟨2416913, by rfl⟩ : syracuseStep 3222551 = 4833827) B4833827
theorem B2148367 : Blo 1909435 2148367 := bstep (se 1 (by rfl) ⟨1611275, by rfl⟩ : syracuseStep 2148367 = 3222551) B3222551
theorem B2864489 : Blo 1909435 2864489 := bstep (se 2 (by rfl) ⟨1074183, by rfl⟩ : syracuseStep 2864489 = 2148367) B2148367
theorem B1909659 : Blo 1909435 1909659 := bstep (se 1 (by rfl) ⟨1432244, by rfl⟩ : syracuseStep 1909659 = 2864489) B2864489
theorem B2294185 : Blo 1909435 2294185 := bbase (se 2 (by rfl) ⟨860319, by rfl⟩ : syracuseStep 2294185 = 1720639) (by norm_num)
theorem B3058913 : Blo 1909435 3058913 := bstep (se 2 (by rfl) ⟨1147092, by rfl⟩ : syracuseStep 3058913 = 2294185) B2294185
theorem B2039275 : Blo 1909435 2039275 := bstep (se 1 (by rfl) ⟨1529456, by rfl⟩ : syracuseStep 2039275 = 3058913) B3058913
theorem B10876133 : Blo 1909435 10876133 := bstep (se 4 (by rfl) ⟨1019637, by rfl⟩ : syracuseStep 10876133 = 2039275) B2039275
theorem B7250755 : Blo 1909435 7250755 := bstep (se 1 (by rfl) ⟨5438066, by rfl⟩ : syracuseStep 7250755 = 10876133) B10876133
theorem B9667673 : Blo 1909435 9667673 := bstep (se 2 (by rfl) ⟨3625377, by rfl⟩ : syracuseStep 9667673 = 7250755) B7250755
theorem B6445115 : Blo 1909435 6445115 := bstep (se 1 (by rfl) ⟨4833836, by rfl⟩ : syracuseStep 6445115 = 9667673) B9667673
theorem B4296743 : Blo 1909435 4296743 := bstep (se 1 (by rfl) ⟨3222557, by rfl⟩ : syracuseStep 4296743 = 6445115) B6445115
theorem B2864495 : Blo 1909435 2864495 := bstep (se 1 (by rfl) ⟨2148371, by rfl⟩ : syracuseStep 2864495 = 4296743) B4296743
theorem B1909663 : Blo 1909435 1909663 := bstep (se 1 (by rfl) ⟨1432247, by rfl⟩ : syracuseStep 1909663 = 2864495) B2864495
theorem B2864501 : Blo 1909435 2864501 := bbase (se 5 (by rfl) ⟨134273, by rfl⟩ : syracuseStep 2864501 = 268547) (by norm_num)
theorem B1909667 : Blo 1909435 1909667 := bstep (se 1 (by rfl) ⟨1432250, by rfl⟩ : syracuseStep 1909667 = 2864501) B2864501
theorem B2719045 : Blo 1909435 2719045 := bbase (se 4 (by rfl) ⟨254910, by rfl⟩ : syracuseStep 2719045 = 509821) (by norm_num)
theorem B3625393 : Blo 1909435 3625393 := bstep (se 2 (by rfl) ⟨1359522, by rfl⟩ : syracuseStep 3625393 = 2719045) B2719045
theorem B4833857 : Blo 1909435 4833857 := bstep (se 2 (by rfl) ⟨1812696, by rfl⟩ : syracuseStep 4833857 = 3625393) B3625393
theorem B3222571 : Blo 1909435 3222571 := bstep (se 1 (by rfl) ⟨2416928, by rfl⟩ : syracuseStep 3222571 = 4833857) B4833857
theorem B4296761 : Blo 1909435 4296761 := bstep (se 2 (by rfl) ⟨1611285, by rfl⟩ : syracuseStep 4296761 = 3222571) B3222571
theorem B2864507 : Blo 1909435 2864507 := bstep (se 1 (by rfl) ⟨2148380, by rfl⟩ : syracuseStep 2864507 = 4296761) B4296761
theorem B1909671 : Blo 1909435 1909671 := bstep (se 1 (by rfl) ⟨1432253, by rfl⟩ : syracuseStep 1909671 = 2864507) B2864507
theorem B2148385 : Blo 1909435 2148385 := bbase (se 2 (by rfl) ⟨805644, by rfl⟩ : syracuseStep 2148385 = 1611289) (by norm_num)
theorem B2864513 : Blo 1909435 2864513 := bstep (se 2 (by rfl) ⟨1074192, by rfl⟩ : syracuseStep 2864513 = 2148385) B2148385
theorem B1909675 : Blo 1909435 1909675 := bstep (se 1 (by rfl) ⟨1432256, by rfl⟩ : syracuseStep 1909675 = 2864513) B2864513
theorem B4833877 : Blo 1909435 4833877 := bbase (se 8 (by rfl) ⟨28323, by rfl⟩ : syracuseStep 4833877 = 56647) (by norm_num)
theorem B6445169 : Blo 1909435 6445169 := bstep (se 2 (by rfl) ⟨2416938, by rfl⟩ : syracuseStep 6445169 = 4833877) B4833877
theorem B4296779 : Blo 1909435 4296779 := bstep (se 1 (by rfl) ⟨3222584, by rfl⟩ : syracuseStep 4296779 = 6445169) B6445169
theorem B2864519 : Blo 1909435 2864519 := bstep (se 1 (by rfl) ⟨2148389, by rfl⟩ : syracuseStep 2864519 = 4296779) B4296779
theorem B1909679 : Blo 1909435 1909679 := bstep (se 1 (by rfl) ⟨1432259, by rfl⟩ : syracuseStep 1909679 = 2864519) B2864519
theorem B2864525 : Blo 1909435 2864525 := bbase (se 3 (by rfl) ⟨537098, by rfl⟩ : syracuseStep 2864525 = 1074197) (by norm_num)
theorem B1909683 : Blo 1909435 1909683 := bstep (se 1 (by rfl) ⟨1432262, by rfl⟩ : syracuseStep 1909683 = 2864525) B2864525
theorem B4296797 : Blo 1909435 4296797 := bbase (se 3 (by rfl) ⟨805649, by rfl⟩ : syracuseStep 4296797 = 1611299) (by norm_num)
theorem B2864531 : Blo 1909435 2864531 := bstep (se 1 (by rfl) ⟨2148398, by rfl⟩ : syracuseStep 2864531 = 4296797) B4296797
theorem B1909687 : Blo 1909435 1909687 := bstep (se 1 (by rfl) ⟨1432265, by rfl⟩ : syracuseStep 1909687 = 2864531) B2864531
theorem B3222605 : Blo 1909435 3222605 := bbase (se 3 (by rfl) ⟨604238, by rfl⟩ : syracuseStep 3222605 = 1208477) (by norm_num)
theorem B2148403 : Blo 1909435 2148403 := bstep (se 1 (by rfl) ⟨1611302, by rfl⟩ : syracuseStep 2148403 = 3222605) B3222605
theorem B2864537 : Blo 1909435 2864537 := bstep (se 2 (by rfl) ⟨1074201, by rfl⟩ : syracuseStep 2864537 = 2148403) B2148403
theorem B1909691 : Blo 1909435 1909691 := bstep (se 1 (by rfl) ⟨1432268, by rfl⟩ : syracuseStep 1909691 = 2864537) B2864537
theorem B15486005 : Blo 1909435 15486005 := bbase (se 5 (by rfl) ⟨725906, by rfl⟩ : syracuseStep 15486005 = 1451813) (by norm_num)
theorem B41296013 : Blo 1909435 41296013 := bstep (se 3 (by rfl) ⟨7743002, by rfl⟩ : syracuseStep 41296013 = 15486005) B15486005
theorem B27530675 : Blo 1909435 27530675 := bstep (se 1 (by rfl) ⟨20648006, by rfl⟩ : syracuseStep 27530675 = 41296013) B41296013
theorem B18353783 : Blo 1909435 18353783 := bstep (se 1 (by rfl) ⟨13765337, by rfl⟩ : syracuseStep 18353783 = 27530675) B27530675
theorem B12235855 : Blo 1909435 12235855 := bstep (se 1 (by rfl) ⟨9176891, by rfl⟩ : syracuseStep 12235855 = 18353783) B18353783
theorem B16314473 : Blo 1909435 16314473 := bstep (se 2 (by rfl) ⟨6117927, by rfl⟩ : syracuseStep 16314473 = 12235855) B12235855
theorem B10876315 : Blo 1909435 10876315 := bstep (se 1 (by rfl) ⟨8157236, by rfl⟩ : syracuseStep 10876315 = 16314473) B16314473
theorem B14501753 : Blo 1909435 14501753 := bstep (se 2 (by rfl) ⟨5438157, by rfl⟩ : syracuseStep 14501753 = 10876315) B10876315
theorem B9667835 : Blo 1909435 9667835 := bstep (se 1 (by rfl) ⟨7250876, by rfl⟩ : syracuseStep 9667835 = 14501753) B14501753
theorem B6445223 : Blo 1909435 6445223 := bstep (se 1 (by rfl) ⟨4833917, by rfl⟩ : syracuseStep 6445223 = 9667835) B9667835
theorem B4296815 : Blo 1909435 4296815 := bstep (se 1 (by rfl) ⟨3222611, by rfl⟩ : syracuseStep 4296815 = 6445223) B6445223
theorem B2864543 : Blo 1909435 2864543 := bstep (se 1 (by rfl) ⟨2148407, by rfl⟩ : syracuseStep 2864543 = 4296815) B4296815
theorem B1909695 : Blo 1909435 1909695 := bstep (se 1 (by rfl) ⟨1432271, by rfl⟩ : syracuseStep 1909695 = 2864543) B2864543
theorem B2864549 : Blo 1909435 2864549 := bbase (se 4 (by rfl) ⟨268551, by rfl⟩ : syracuseStep 2864549 = 537103) (by norm_num)
theorem B1909699 : Blo 1909435 1909699 := bstep (se 1 (by rfl) ⟨1432274, by rfl⟩ : syracuseStep 1909699 = 2864549) B2864549
theorem B2416969 : Blo 1909435 2416969 := bbase (se 2 (by rfl) ⟨906363, by rfl⟩ : syracuseStep 2416969 = 1812727) (by norm_num)
theorem B3222625 : Blo 1909435 3222625 := bstep (se 2 (by rfl) ⟨1208484, by rfl⟩ : syracuseStep 3222625 = 2416969) B2416969
theorem B4296833 : Blo 1909435 4296833 := bstep (se 2 (by rfl) ⟨1611312, by rfl⟩ : syracuseStep 4296833 = 3222625) B3222625
theorem B2864555 : Blo 1909435 2864555 := bstep (se 1 (by rfl) ⟨2148416, by rfl⟩ : syracuseStep 2864555 = 4296833) B4296833
theorem B1909703 : Blo 1909435 1909703 := bstep (se 1 (by rfl) ⟨1432277, by rfl⟩ : syracuseStep 1909703 = 2864555) B2864555
theorem B2148421 : Blo 1909435 2148421 := bbase (se 4 (by rfl) ⟨201414, by rfl⟩ : syracuseStep 2148421 = 402829) (by norm_num)
theorem B2864561 : Blo 1909435 2864561 := bstep (se 2 (by rfl) ⟨1074210, by rfl⟩ : syracuseStep 2864561 = 2148421) B2148421
theorem B1909707 : Blo 1909435 1909707 := bstep (se 1 (by rfl) ⟨1432280, by rfl⟩ : syracuseStep 1909707 = 2864561) B2864561
theorem B3625469 : Blo 1909435 3625469 := bbase (se 3 (by rfl) ⟨679775, by rfl⟩ : syracuseStep 3625469 = 1359551) (by norm_num)
theorem B2416979 : Blo 1909435 2416979 := bstep (se 1 (by rfl) ⟨1812734, by rfl⟩ : syracuseStep 2416979 = 3625469) B3625469
theorem B6445277 : Blo 1909435 6445277 := bstep (se 3 (by rfl) ⟨1208489, by rfl⟩ : syracuseStep 6445277 = 2416979) B2416979
theorem B4296851 : Blo 1909435 4296851 := bstep (se 1 (by rfl) ⟨3222638, by rfl⟩ : syracuseStep 4296851 = 6445277) B6445277
theorem B2864567 : Blo 1909435 2864567 := bstep (se 1 (by rfl) ⟨2148425, by rfl⟩ : syracuseStep 2864567 = 4296851) B4296851
theorem B1909711 : Blo 1909435 1909711 := bstep (se 1 (by rfl) ⟨1432283, by rfl⟩ : syracuseStep 1909711 = 2864567) B2864567
theorem B2864573 : Blo 1909435 2864573 := bbase (se 3 (by rfl) ⟨537107, by rfl⟩ : syracuseStep 2864573 = 1074215) (by norm_num)
theorem B1909715 : Blo 1909435 1909715 := bstep (se 1 (by rfl) ⟨1432286, by rfl⟩ : syracuseStep 1909715 = 2864573) B2864573
theorem B4296869 : Blo 1909435 4296869 := bbase (se 4 (by rfl) ⟨402831, by rfl⟩ : syracuseStep 4296869 = 805663) (by norm_num)
theorem B2864579 : Blo 1909435 2864579 := bstep (se 1 (by rfl) ⟨2148434, by rfl⟩ : syracuseStep 2864579 = 4296869) B4296869
theorem B1909719 : Blo 1909435 1909719 := bstep (se 1 (by rfl) ⟨1432289, by rfl⟩ : syracuseStep 1909719 = 2864579) B2864579
theorem B4833989 : Blo 1909435 4833989 := bbase (se 4 (by rfl) ⟨453186, by rfl⟩ : syracuseStep 4833989 = 906373) (by norm_num)
theorem B3222659 : Blo 1909435 3222659 := bstep (se 1 (by rfl) ⟨2416994, by rfl⟩ : syracuseStep 3222659 = 4833989) B4833989
theorem B2148439 : Blo 1909435 2148439 := bstep (se 1 (by rfl) ⟨1611329, by rfl⟩ : syracuseStep 2148439 = 3222659) B3222659
theorem B2864585 : Blo 1909435 2864585 := bstep (se 2 (by rfl) ⟨1074219, by rfl⟩ : syracuseStep 2864585 = 2148439) B2148439
theorem B1909723 : Blo 1909435 1909723 := bstep (se 1 (by rfl) ⟨1432292, by rfl⟩ : syracuseStep 1909723 = 2864585) B2864585
theorem B3674965 : Blo 1909435 3674965 := bbase (se 9 (by rfl) ⟨10766, by rfl⟩ : syracuseStep 3674965 = 21533) (by norm_num)
theorem B4899953 : Blo 1909435 4899953 := bstep (se 2 (by rfl) ⟨1837482, by rfl⟩ : syracuseStep 4899953 = 3674965) B3674965
theorem B13066541 : Blo 1909435 13066541 := bstep (se 3 (by rfl) ⟨2449976, by rfl⟩ : syracuseStep 13066541 = 4899953) B4899953
theorem B8711027 : Blo 1909435 8711027 := bstep (se 1 (by rfl) ⟨6533270, by rfl⟩ : syracuseStep 8711027 = 13066541) B13066541
theorem B5807351 : Blo 1909435 5807351 := bstep (se 1 (by rfl) ⟨4355513, by rfl⟩ : syracuseStep 5807351 = 8711027) B8711027
theorem B3871567 : Blo 1909435 3871567 := bstep (se 1 (by rfl) ⟨2903675, by rfl⟩ : syracuseStep 3871567 = 5807351) B5807351
theorem B20648357 : Blo 1909435 20648357 := bstep (se 4 (by rfl) ⟨1935783, by rfl⟩ : syracuseStep 20648357 = 3871567) B3871567
theorem B13765571 : Blo 1909435 13765571 := bstep (se 1 (by rfl) ⟨10324178, by rfl⟩ : syracuseStep 13765571 = 20648357) B20648357
theorem B9177047 : Blo 1909435 9177047 := bstep (se 1 (by rfl) ⟨6882785, by rfl⟩ : syracuseStep 9177047 = 13765571) B13765571
theorem B6118031 : Blo 1909435 6118031 := bstep (se 1 (by rfl) ⟨4588523, by rfl⟩ : syracuseStep 6118031 = 9177047) B9177047
theorem B4078687 : Blo 1909435 4078687 := bstep (se 1 (by rfl) ⟨3059015, by rfl⟩ : syracuseStep 4078687 = 6118031) B6118031
theorem B5438249 : Blo 1909435 5438249 := bstep (se 2 (by rfl) ⟨2039343, by rfl⟩ : syracuseStep 5438249 = 4078687) B4078687
theorem B3625499 : Blo 1909435 3625499 := bstep (se 1 (by rfl) ⟨2719124, by rfl⟩ : syracuseStep 3625499 = 5438249) B5438249
theorem B9667997 : Blo 1909435 9667997 := bstep (se 3 (by rfl) ⟨1812749, by rfl⟩ : syracuseStep 9667997 = 3625499) B3625499
theorem B6445331 : Blo 1909435 6445331 := bstep (se 1 (by rfl) ⟨4833998, by rfl⟩ : syracuseStep 6445331 = 9667997) B9667997
theorem B4296887 : Blo 1909435 4296887 := bstep (se 1 (by rfl) ⟨3222665, by rfl⟩ : syracuseStep 4296887 = 6445331) B6445331
theorem B2864591 : Blo 1909435 2864591 := bstep (se 1 (by rfl) ⟨2148443, by rfl⟩ : syracuseStep 2864591 = 4296887) B4296887
theorem B1909727 : Blo 1909435 1909727 := bstep (se 1 (by rfl) ⟨1432295, by rfl⟩ : syracuseStep 1909727 = 2864591) B2864591
theorem B2864597 : Blo 1909435 2864597 := bbase (se 7 (by rfl) ⟨33569, by rfl⟩ : syracuseStep 2864597 = 67139) (by norm_num)
theorem B1909731 : Blo 1909435 1909731 := bstep (se 1 (by rfl) ⟨1432298, by rfl⟩ : syracuseStep 1909731 = 2864597) B2864597
theorem B7251029 : Blo 1909435 7251029 := bbase (se 8 (by rfl) ⟨42486, by rfl⟩ : syracuseStep 7251029 = 84973) (by norm_num)
theorem B4834019 : Blo 1909435 4834019 := bstep (se 1 (by rfl) ⟨3625514, by rfl⟩ : syracuseStep 4834019 = 7251029) B7251029
theorem B3222679 : Blo 1909435 3222679 := bstep (se 1 (by rfl) ⟨2417009, by rfl⟩ : syracuseStep 3222679 = 4834019) B4834019
theorem B4296905 : Blo 1909435 4296905 := bstep (se 2 (by rfl) ⟨1611339, by rfl⟩ : syracuseStep 4296905 = 3222679) B3222679
theorem B2864603 : Blo 1909435 2864603 := bstep (se 1 (by rfl) ⟨2148452, by rfl⟩ : syracuseStep 2864603 = 4296905) B4296905
theorem B1909735 : Blo 1909435 1909735 := bstep (se 1 (by rfl) ⟨1432301, by rfl⟩ : syracuseStep 1909735 = 2864603) B2864603
theorem B2148457 : Blo 1909435 2148457 := bbase (se 2 (by rfl) ⟨805671, by rfl⟩ : syracuseStep 2148457 = 1611343) (by norm_num)
theorem B2864609 : Blo 1909435 2864609 := bstep (se 2 (by rfl) ⟨1074228, by rfl⟩ : syracuseStep 2864609 = 2148457) B2148457
theorem B1909739 : Blo 1909435 1909739 := bstep (se 1 (by rfl) ⟨1432304, by rfl⟩ : syracuseStep 1909739 = 2864609) B2864609
theorem B2294281 : Blo 1909435 2294281 := bbase (se 2 (by rfl) ⟨860355, by rfl⟩ : syracuseStep 2294281 = 1720711) (by norm_num)
theorem B3059041 : Blo 1909435 3059041 := bstep (se 2 (by rfl) ⟨1147140, by rfl⟩ : syracuseStep 3059041 = 2294281) B2294281
theorem B4078721 : Blo 1909435 4078721 := bstep (se 2 (by rfl) ⟨1529520, by rfl⟩ : syracuseStep 4078721 = 3059041) B3059041
theorem B10876589 : Blo 1909435 10876589 := bstep (se 3 (by rfl) ⟨2039360, by rfl⟩ : syracuseStep 10876589 = 4078721) B4078721
theorem B7251059 : Blo 1909435 7251059 := bstep (se 1 (by rfl) ⟨5438294, by rfl⟩ : syracuseStep 7251059 = 10876589) B10876589
theorem B4834039 : Blo 1909435 4834039 := bstep (se 1 (by rfl) ⟨3625529, by rfl⟩ : syracuseStep 4834039 = 7251059) B7251059
theorem B6445385 : Blo 1909435 6445385 := bstep (se 2 (by rfl) ⟨2417019, by rfl⟩ : syracuseStep 6445385 = 4834039) B4834039
theorem B4296923 : Blo 1909435 4296923 := bstep (se 1 (by rfl) ⟨3222692, by rfl⟩ : syracuseStep 4296923 = 6445385) B6445385
theorem B2864615 : Blo 1909435 2864615 := bstep (se 1 (by rfl) ⟨2148461, by rfl⟩ : syracuseStep 2864615 = 4296923) B4296923
theorem B1909743 : Blo 1909435 1909743 := bstep (se 1 (by rfl) ⟨1432307, by rfl⟩ : syracuseStep 1909743 = 2864615) B2864615
theorem B2864621 : Blo 1909435 2864621 := bbase (se 3 (by rfl) ⟨537116, by rfl⟩ : syracuseStep 2864621 = 1074233) (by norm_num)
theorem B1909747 : Blo 1909435 1909747 := bstep (se 1 (by rfl) ⟨1432310, by rfl⟩ : syracuseStep 1909747 = 2864621) B2864621
theorem B4296941 : Blo 1909435 4296941 := bbase (se 3 (by rfl) ⟨805676, by rfl⟩ : syracuseStep 4296941 = 1611353) (by norm_num)
theorem B2864627 : Blo 1909435 2864627 := bstep (se 1 (by rfl) ⟨2148470, by rfl⟩ : syracuseStep 2864627 = 4296941) B4296941
theorem B1909751 : Blo 1909435 1909751 := bstep (se 1 (by rfl) ⟨1432313, by rfl⟩ : syracuseStep 1909751 = 2864627) B2864627
theorem B2719165 : Blo 1909435 2719165 := bbase (se 3 (by rfl) ⟨509843, by rfl⟩ : syracuseStep 2719165 = 1019687) (by norm_num)
theorem B3625553 : Blo 1909435 3625553 := bstep (se 2 (by rfl) ⟨1359582, by rfl⟩ : syracuseStep 3625553 = 2719165) B2719165
theorem B2417035 : Blo 1909435 2417035 := bstep (se 1 (by rfl) ⟨1812776, by rfl⟩ : syracuseStep 2417035 = 3625553) B3625553
theorem B3222713 : Blo 1909435 3222713 := bstep (se 2 (by rfl) ⟨1208517, by rfl⟩ : syracuseStep 3222713 = 2417035) B2417035
theorem B2148475 : Blo 1909435 2148475 := bstep (se 1 (by rfl) ⟨1611356, by rfl⟩ : syracuseStep 2148475 = 3222713) B3222713
theorem B2864633 : Blo 1909435 2864633 := bstep (se 2 (by rfl) ⟨1074237, by rfl⟩ : syracuseStep 2864633 = 2148475) B2148475
theorem B1909755 : Blo 1909435 1909755 := bstep (se 1 (by rfl) ⟨1432316, by rfl⟩ : syracuseStep 1909755 = 2864633) B2864633
theorem B2450017 : Blo 1909435 2450017 := bbase (se 2 (by rfl) ⟨918756, by rfl⟩ : syracuseStep 2450017 = 1837513) (by norm_num)
theorem B13066757 : Blo 1909435 13066757 := bstep (se 4 (by rfl) ⟨1225008, by rfl⟩ : syracuseStep 13066757 = 2450017) B2450017
theorem B8711171 : Blo 1909435 8711171 := bstep (se 1 (by rfl) ⟨6533378, by rfl⟩ : syracuseStep 8711171 = 13066757) B13066757
theorem B5807447 : Blo 1909435 5807447 := bstep (se 1 (by rfl) ⟨4355585, by rfl⟩ : syracuseStep 5807447 = 8711171) B8711171
theorem B3871631 : Blo 1909435 3871631 := bstep (se 1 (by rfl) ⟨2903723, by rfl⟩ : syracuseStep 3871631 = 5807447) B5807447
theorem B10324349 : Blo 1909435 10324349 := bstep (se 3 (by rfl) ⟨1935815, by rfl⟩ : syracuseStep 10324349 = 3871631) B3871631
theorem B6882899 : Blo 1909435 6882899 := bstep (se 1 (by rfl) ⟨5162174, by rfl⟩ : syracuseStep 6882899 = 10324349) B10324349
theorem B73417589 : Blo 1909435 73417589 := bstep (se 5 (by rfl) ⟨3441449, by rfl⟩ : syracuseStep 73417589 = 6882899) B6882899
theorem B48945059 : Blo 1909435 48945059 := bstep (se 1 (by rfl) ⟨36708794, by rfl⟩ : syracuseStep 48945059 = 73417589) B73417589
theorem B32630039 : Blo 1909435 32630039 := bstep (se 1 (by rfl) ⟨24472529, by rfl⟩ : syracuseStep 32630039 = 48945059) B48945059
theorem B21753359 : Blo 1909435 21753359 := bstep (se 1 (by rfl) ⟨16315019, by rfl⟩ : syracuseStep 21753359 = 32630039) B32630039
theorem B14502239 : Blo 1909435 14502239 := bstep (se 1 (by rfl) ⟨10876679, by rfl⟩ : syracuseStep 14502239 = 21753359) B21753359
theorem B9668159 : Blo 1909435 9668159 := bstep (se 1 (by rfl) ⟨7251119, by rfl⟩ : syracuseStep 9668159 = 14502239) B14502239
theorem B6445439 : Blo 1909435 6445439 := bstep (se 1 (by rfl) ⟨4834079, by rfl⟩ : syracuseStep 6445439 = 9668159) B9668159
theorem B4296959 : Blo 1909435 4296959 := bstep (se 1 (by rfl) ⟨3222719, by rfl⟩ : syracuseStep 4296959 = 6445439) B6445439
theorem B2864639 : Blo 1909435 2864639 := bstep (se 1 (by rfl) ⟨2148479, by rfl⟩ : syracuseStep 2864639 = 4296959) B4296959
theorem B1909759 : Blo 1909435 1909759 := bstep (se 1 (by rfl) ⟨1432319, by rfl⟩ : syracuseStep 1909759 = 2864639) B2864639
theorem B2864645 : Blo 1909435 2864645 := bbase (se 4 (by rfl) ⟨268560, by rfl⟩ : syracuseStep 2864645 = 537121) (by norm_num)
theorem B1909763 : Blo 1909435 1909763 := bstep (se 1 (by rfl) ⟨1432322, by rfl⟩ : syracuseStep 1909763 = 2864645) B2864645
theorem B3222733 : Blo 1909435 3222733 := bbase (se 3 (by rfl) ⟨604262, by rfl⟩ : syracuseStep 3222733 = 1208525) (by norm_num)
theorem B4296977 : Blo 1909435 4296977 := bstep (se 2 (by rfl) ⟨1611366, by rfl⟩ : syracuseStep 4296977 = 3222733) B3222733
theorem B2864651 : Blo 1909435 2864651 := bstep (se 1 (by rfl) ⟨2148488, by rfl⟩ : syracuseStep 2864651 = 4296977) B4296977
theorem B1909767 : Blo 1909435 1909767 := bstep (se 1 (by rfl) ⟨1432325, by rfl⟩ : syracuseStep 1909767 = 2864651) B2864651
theorem B2148493 : Blo 1909435 2148493 := bbase (se 3 (by rfl) ⟨402842, by rfl⟩ : syracuseStep 2148493 = 805685) (by norm_num)
theorem B2864657 : Blo 1909435 2864657 := bstep (se 2 (by rfl) ⟨1074246, by rfl⟩ : syracuseStep 2864657 = 2148493) B2148493
theorem B1909771 : Blo 1909435 1909771 := bstep (se 1 (by rfl) ⟨1432328, by rfl⟩ : syracuseStep 1909771 = 2864657) B2864657
theorem B6445493 : Blo 1909435 6445493 := bbase (se 5 (by rfl) ⟨302132, by rfl⟩ : syracuseStep 6445493 = 604265) (by norm_num)
theorem B4296995 : Blo 1909435 4296995 := bstep (se 1 (by rfl) ⟨3222746, by rfl⟩ : syracuseStep 4296995 = 6445493) B6445493
theorem B2864663 : Blo 1909435 2864663 := bstep (se 1 (by rfl) ⟨2148497, by rfl⟩ : syracuseStep 2864663 = 4296995) B4296995
theorem B1909775 : Blo 1909435 1909775 := bstep (se 1 (by rfl) ⟨1432331, by rfl⟩ : syracuseStep 1909775 = 2864663) B2864663
theorem B2864669 : Blo 1909435 2864669 := bbase (se 3 (by rfl) ⟨537125, by rfl⟩ : syracuseStep 2864669 = 1074251) (by norm_num)
theorem B1909779 : Blo 1909435 1909779 := bstep (se 1 (by rfl) ⟨1432334, by rfl⟩ : syracuseStep 1909779 = 2864669) B2864669
theorem B4297013 : Blo 1909435 4297013 := bbase (se 5 (by rfl) ⟨201422, by rfl⟩ : syracuseStep 4297013 = 402845) (by norm_num)
theorem B2864675 : Blo 1909435 2864675 := bstep (se 1 (by rfl) ⟨2148506, by rfl⟩ : syracuseStep 2864675 = 4297013) B4297013
theorem B1909783 : Blo 1909435 1909783 := bstep (se 1 (by rfl) ⟨1432337, by rfl⟩ : syracuseStep 1909783 = 2864675) B2864675
theorem B2983541 : Blo 1909435 2983541 := bbase (se 5 (by rfl) ⟨139853, by rfl⟩ : syracuseStep 2983541 = 279707) (by norm_num)
theorem B7956109 : Blo 1909435 7956109 := bstep (se 3 (by rfl) ⟨1491770, by rfl⟩ : syracuseStep 7956109 = 2983541) B2983541
theorem B42432581 : Blo 1909435 42432581 := bstep (se 4 (by rfl) ⟨3978054, by rfl⟩ : syracuseStep 42432581 = 7956109) B7956109
theorem B28288387 : Blo 1909435 28288387 := bstep (se 1 (by rfl) ⟨21216290, by rfl⟩ : syracuseStep 28288387 = 42432581) B42432581
theorem B37717849 : Blo 1909435 37717849 := bstep (se 2 (by rfl) ⟨14144193, by rfl⟩ : syracuseStep 37717849 = 28288387) B28288387
theorem B50290465 : Blo 1909435 50290465 := bstep (se 2 (by rfl) ⟨18858924, by rfl⟩ : syracuseStep 50290465 = 37717849) B37717849
theorem B67053953 : Blo 1909435 67053953 := bstep (se 2 (by rfl) ⟨25145232, by rfl⟩ : syracuseStep 67053953 = 50290465) B50290465
theorem B178810541 : Blo 1909435 178810541 := bstep (se 3 (by rfl) ⟨33526976, by rfl⟩ : syracuseStep 178810541 = 67053953) B67053953
theorem B119207027 : Blo 1909435 119207027 := bstep (se 1 (by rfl) ⟨89405270, by rfl⟩ : syracuseStep 119207027 = 178810541) B178810541
theorem B317885405 : Blo 1909435 317885405 := bstep (se 3 (by rfl) ⟨59603513, by rfl⟩ : syracuseStep 317885405 = 119207027) B119207027
theorem B847694413 : Blo 1909435 847694413 := bstep (se 3 (by rfl) ⟨158942702, by rfl⟩ : syracuseStep 847694413 = 317885405) B317885405
theorem B1130259217 : Blo 1909435 1130259217 := bstep (se 2 (by rfl) ⟨423847206, by rfl⟩ : syracuseStep 1130259217 = 847694413) B847694413
theorem B1507012289 : Blo 1909435 1507012289 := bstep (se 2 (by rfl) ⟨565129608, by rfl⟩ : syracuseStep 1507012289 = 1130259217) B1130259217
theorem B1004674859 : Blo 1909435 1004674859 := bstep (se 1 (by rfl) ⟨753506144, by rfl⟩ : syracuseStep 1004674859 = 1507012289) B1507012289
theorem B669783239 : Blo 1909435 669783239 := bstep (se 1 (by rfl) ⟨502337429, by rfl⟩ : syracuseStep 669783239 = 1004674859) B1004674859
theorem B446522159 : Blo 1909435 446522159 := bstep (se 1 (by rfl) ⟨334891619, by rfl⟩ : syracuseStep 446522159 = 669783239) B669783239
theorem B297681439 : Blo 1909435 297681439 := bstep (se 1 (by rfl) ⟨223261079, by rfl⟩ : syracuseStep 297681439 = 446522159) B446522159
theorem B396908585 : Blo 1909435 396908585 := bstep (se 2 (by rfl) ⟨148840719, by rfl⟩ : syracuseStep 396908585 = 297681439) B297681439
theorem B264605723 : Blo 1909435 264605723 := bstep (se 1 (by rfl) ⟨198454292, by rfl⟩ : syracuseStep 264605723 = 396908585) B396908585
theorem B176403815 : Blo 1909435 176403815 := bstep (se 1 (by rfl) ⟨132302861, by rfl⟩ : syracuseStep 176403815 = 264605723) B264605723
theorem B117602543 : Blo 1909435 117602543 := bstep (se 1 (by rfl) ⟨88201907, by rfl⟩ : syracuseStep 117602543 = 176403815) B176403815
theorem B78401695 : Blo 1909435 78401695 := bstep (se 1 (by rfl) ⟨58801271, by rfl⟩ : syracuseStep 78401695 = 117602543) B117602543
theorem B104535593 : Blo 1909435 104535593 := bstep (se 2 (by rfl) ⟨39200847, by rfl⟩ : syracuseStep 104535593 = 78401695) B78401695
theorem B69690395 : Blo 1909435 69690395 := bstep (se 1 (by rfl) ⟨52267796, by rfl⟩ : syracuseStep 69690395 = 104535593) B104535593
theorem B46460263 : Blo 1909435 46460263 := bstep (se 1 (by rfl) ⟨34845197, by rfl⟩ : syracuseStep 46460263 = 69690395) B69690395
theorem B61947017 : Blo 1909435 61947017 := bstep (se 2 (by rfl) ⟨23230131, by rfl⟩ : syracuseStep 61947017 = 46460263) B46460263
theorem B41298011 : Blo 1909435 41298011 := bstep (se 1 (by rfl) ⟨30973508, by rfl⟩ : syracuseStep 41298011 = 61947017) B61947017
theorem B27532007 : Blo 1909435 27532007 := bstep (se 1 (by rfl) ⟨20649005, by rfl⟩ : syracuseStep 27532007 = 41298011) B41298011
theorem B18354671 : Blo 1909435 18354671 := bstep (se 1 (by rfl) ⟨13766003, by rfl⟩ : syracuseStep 18354671 = 27532007) B27532007
theorem B12236447 : Blo 1909435 12236447 := bstep (se 1 (by rfl) ⟨9177335, by rfl⟩ : syracuseStep 12236447 = 18354671) B18354671
theorem B8157631 : Blo 1909435 8157631 := bstep (se 1 (by rfl) ⟨6118223, by rfl⟩ : syracuseStep 8157631 = 12236447) B12236447
theorem B10876841 : Blo 1909435 10876841 := bstep (se 2 (by rfl) ⟨4078815, by rfl⟩ : syracuseStep 10876841 = 8157631) B8157631
theorem B7251227 : Blo 1909435 7251227 := bstep (se 1 (by rfl) ⟨5438420, by rfl⟩ : syracuseStep 7251227 = 10876841) B10876841
theorem B4834151 : Blo 1909435 4834151 := bstep (se 1 (by rfl) ⟨3625613, by rfl⟩ : syracuseStep 4834151 = 7251227) B7251227
theorem B3222767 : Blo 1909435 3222767 := bstep (se 1 (by rfl) ⟨2417075, by rfl⟩ : syracuseStep 3222767 = 4834151) B4834151
theorem B2148511 : Blo 1909435 2148511 := bstep (se 1 (by rfl) ⟨1611383, by rfl⟩ : syracuseStep 2148511 = 3222767) B3222767
theorem B2864681 : Blo 1909435 2864681 := bstep (se 2 (by rfl) ⟨1074255, by rfl⟩ : syracuseStep 2864681 = 2148511) B2148511
theorem B1909787 : Blo 1909435 1909787 := bstep (se 1 (by rfl) ⟨1432340, by rfl⟩ : syracuseStep 1909787 = 2864681) B2864681
theorem B8711317 : Blo 1909435 8711317 := bbase (se 6 (by rfl) ⟨204171, by rfl⟩ : syracuseStep 8711317 = 408343) (by norm_num)
theorem B11615089 : Blo 1909435 11615089 := bstep (se 2 (by rfl) ⟨4355658, by rfl⟩ : syracuseStep 11615089 = 8711317) B8711317
theorem B15486785 : Blo 1909435 15486785 := bstep (se 2 (by rfl) ⟨5807544, by rfl⟩ : syracuseStep 15486785 = 11615089) B11615089
theorem B10324523 : Blo 1909435 10324523 := bstep (se 1 (by rfl) ⟨7743392, by rfl⟩ : syracuseStep 10324523 = 15486785) B15486785
theorem B27532061 : Blo 1909435 27532061 := bstep (se 3 (by rfl) ⟨5162261, by rfl⟩ : syracuseStep 27532061 = 10324523) B10324523
theorem B18354707 : Blo 1909435 18354707 := bstep (se 1 (by rfl) ⟨13766030, by rfl⟩ : syracuseStep 18354707 = 27532061) B27532061
theorem B12236471 : Blo 1909435 12236471 := bstep (se 1 (by rfl) ⟨9177353, by rfl⟩ : syracuseStep 12236471 = 18354707) B18354707
theorem B8157647 : Blo 1909435 8157647 := bstep (se 1 (by rfl) ⟨6118235, by rfl⟩ : syracuseStep 8157647 = 12236471) B12236471
theorem B5438431 : Blo 1909435 5438431 := bstep (se 1 (by rfl) ⟨4078823, by rfl⟩ : syracuseStep 5438431 = 8157647) B8157647
theorem B7251241 : Blo 1909435 7251241 := bstep (se 2 (by rfl) ⟨2719215, by rfl⟩ : syracuseStep 7251241 = 5438431) B5438431
theorem B9668321 : Blo 1909435 9668321 := bstep (se 2 (by rfl) ⟨3625620, by rfl⟩ : syracuseStep 9668321 = 7251241) B7251241
theorem B6445547 : Blo 1909435 6445547 := bstep (se 1 (by rfl) ⟨4834160, by rfl⟩ : syracuseStep 6445547 = 9668321) B9668321
theorem B4297031 : Blo 1909435 4297031 := bstep (se 1 (by rfl) ⟨3222773, by rfl⟩ : syracuseStep 4297031 = 6445547) B6445547
theorem B2864687 : Blo 1909435 2864687 := bstep (se 1 (by rfl) ⟨2148515, by rfl⟩ : syracuseStep 2864687 = 4297031) B4297031
theorem B1909791 : Blo 1909435 1909791 := bstep (se 1 (by rfl) ⟨1432343, by rfl⟩ : syracuseStep 1909791 = 2864687) B2864687
theorem B2864693 : Blo 1909435 2864693 := bbase (se 5 (by rfl) ⟨134282, by rfl⟩ : syracuseStep 2864693 = 268565) (by norm_num)
theorem B1909795 : Blo 1909435 1909795 := bstep (se 1 (by rfl) ⟨1432346, by rfl⟩ : syracuseStep 1909795 = 2864693) B2864693
theorem B4834181 : Blo 1909435 4834181 := bbase (se 4 (by rfl) ⟨453204, by rfl⟩ : syracuseStep 4834181 = 906409) (by norm_num)
theorem B3222787 : Blo 1909435 3222787 := bstep (se 1 (by rfl) ⟨2417090, by rfl⟩ : syracuseStep 3222787 = 4834181) B4834181
theorem B4297049 : Blo 1909435 4297049 := bstep (se 2 (by rfl) ⟨1611393, by rfl⟩ : syracuseStep 4297049 = 3222787) B3222787
theorem B2864699 : Blo 1909435 2864699 := bstep (se 1 (by rfl) ⟨2148524, by rfl⟩ : syracuseStep 2864699 = 4297049) B4297049
theorem B1909799 : Blo 1909435 1909799 := bstep (se 1 (by rfl) ⟨1432349, by rfl⟩ : syracuseStep 1909799 = 2864699) B2864699
theorem B2148529 : Blo 1909435 2148529 := bbase (se 2 (by rfl) ⟨805698, by rfl⟩ : syracuseStep 2148529 = 1611397) (by norm_num)
theorem B2864705 : Blo 1909435 2864705 := bstep (se 2 (by rfl) ⟨1074264, by rfl⟩ : syracuseStep 2864705 = 2148529) B2148529
theorem B1909803 : Blo 1909435 1909803 := bstep (se 1 (by rfl) ⟨1432352, by rfl⟩ : syracuseStep 1909803 = 2864705) B2864705
theorem B2039429 : Blo 1909435 2039429 := bbase (se 4 (by rfl) ⟨191196, by rfl⟩ : syracuseStep 2039429 = 382393) (by norm_num)
theorem B5438477 : Blo 1909435 5438477 := bstep (se 3 (by rfl) ⟨1019714, by rfl⟩ : syracuseStep 5438477 = 2039429) B2039429
theorem B3625651 : Blo 1909435 3625651 := bstep (se 1 (by rfl) ⟨2719238, by rfl⟩ : syracuseStep 3625651 = 5438477) B5438477
theorem B4834201 : Blo 1909435 4834201 := bstep (se 2 (by rfl) ⟨1812825, by rfl⟩ : syracuseStep 4834201 = 3625651) B3625651
theorem B6445601 : Blo 1909435 6445601 := bstep (se 2 (by rfl) ⟨2417100, by rfl⟩ : syracuseStep 6445601 = 4834201) B4834201
theorem B4297067 : Blo 1909435 4297067 := bstep (se 1 (by rfl) ⟨3222800, by rfl⟩ : syracuseStep 4297067 = 6445601) B6445601
theorem B2864711 : Blo 1909435 2864711 := bstep (se 1 (by rfl) ⟨2148533, by rfl⟩ : syracuseStep 2864711 = 4297067) B4297067
theorem B1909807 : Blo 1909435 1909807 := bstep (se 1 (by rfl) ⟨1432355, by rfl⟩ : syracuseStep 1909807 = 2864711) B2864711
theorem B2864717 : Blo 1909435 2864717 := bbase (se 3 (by rfl) ⟨537134, by rfl⟩ : syracuseStep 2864717 = 1074269) (by norm_num)
theorem B1909811 : Blo 1909435 1909811 := bstep (se 1 (by rfl) ⟨1432358, by rfl⟩ : syracuseStep 1909811 = 2864717) B2864717
theorem B4297085 : Blo 1909435 4297085 := bbase (se 3 (by rfl) ⟨805703, by rfl⟩ : syracuseStep 4297085 = 1611407) (by norm_num)
theorem B2864723 : Blo 1909435 2864723 := bstep (se 1 (by rfl) ⟨2148542, by rfl⟩ : syracuseStep 2864723 = 4297085) B4297085
theorem B1909815 : Blo 1909435 1909815 := bstep (se 1 (by rfl) ⟨1432361, by rfl⟩ : syracuseStep 1909815 = 2864723) B2864723
theorem B3222821 : Blo 1909435 3222821 := bbase (se 4 (by rfl) ⟨302139, by rfl⟩ : syracuseStep 3222821 = 604279) (by norm_num)
theorem B2148547 : Blo 1909435 2148547 := bstep (se 1 (by rfl) ⟨1611410, by rfl⟩ : syracuseStep 2148547 = 3222821) B3222821
theorem B2864729 : Blo 1909435 2864729 := bstep (se 2 (by rfl) ⟨1074273, by rfl⟩ : syracuseStep 2864729 = 2148547) B2148547
theorem B1909819 : Blo 1909435 1909819 := bstep (se 1 (by rfl) ⟨1432364, by rfl⟩ : syracuseStep 1909819 = 2864729) B2864729
theorem B2719261 : Blo 1909435 2719261 := bbase (se 3 (by rfl) ⟨509861, by rfl⟩ : syracuseStep 2719261 = 1019723) (by norm_num)
theorem B14502725 : Blo 1909435 14502725 := bstep (se 4 (by rfl) ⟨1359630, by rfl⟩ : syracuseStep 14502725 = 2719261) B2719261
theorem B9668483 : Blo 1909435 9668483 := bstep (se 1 (by rfl) ⟨7251362, by rfl⟩ : syracuseStep 9668483 = 14502725) B14502725
theorem B6445655 : Blo 1909435 6445655 := bstep (se 1 (by rfl) ⟨4834241, by rfl⟩ : syracuseStep 6445655 = 9668483) B9668483
theorem B4297103 : Blo 1909435 4297103 := bstep (se 1 (by rfl) ⟨3222827, by rfl⟩ : syracuseStep 4297103 = 6445655) B6445655
theorem B2864735 : Blo 1909435 2864735 := bstep (se 1 (by rfl) ⟨2148551, by rfl⟩ : syracuseStep 2864735 = 4297103) B4297103
theorem B1909823 : Blo 1909435 1909823 := bstep (se 1 (by rfl) ⟨1432367, by rfl⟩ : syracuseStep 1909823 = 2864735) B2864735
theorem B2864741 : Blo 1909435 2864741 := bbase (se 4 (by rfl) ⟨268569, by rfl⟩ : syracuseStep 2864741 = 537139) (by norm_num)
theorem B1909827 : Blo 1909435 1909827 := bstep (se 1 (by rfl) ⟨1432370, by rfl⟩ : syracuseStep 1909827 = 2864741) B2864741
theorem B47095253 : Blo 1909435 47095253 := bbase (se 7 (by rfl) ⟨551897, by rfl⟩ : syracuseStep 47095253 = 1103795) (by norm_num)
theorem B31396835 : Blo 1909435 31396835 := bstep (se 1 (by rfl) ⟨23547626, by rfl⟩ : syracuseStep 31396835 = 47095253) B47095253
theorem B20931223 : Blo 1909435 20931223 := bstep (se 1 (by rfl) ⟨15698417, by rfl⟩ : syracuseStep 20931223 = 31396835) B31396835
theorem B27908297 : Blo 1909435 27908297 := bstep (se 2 (by rfl) ⟨10465611, by rfl⟩ : syracuseStep 27908297 = 20931223) B20931223
theorem B18605531 : Blo 1909435 18605531 := bstep (se 1 (by rfl) ⟨13954148, by rfl⟩ : syracuseStep 18605531 = 27908297) B27908297
theorem B12403687 : Blo 1909435 12403687 := bstep (se 1 (by rfl) ⟨9302765, by rfl⟩ : syracuseStep 12403687 = 18605531) B18605531
theorem B16538249 : Blo 1909435 16538249 := bstep (se 2 (by rfl) ⟨6201843, by rfl⟩ : syracuseStep 16538249 = 12403687) B12403687
theorem B11025499 : Blo 1909435 11025499 := bstep (se 1 (by rfl) ⟨8269124, by rfl⟩ : syracuseStep 11025499 = 16538249) B16538249
theorem B14700665 : Blo 1909435 14700665 := bstep (se 2 (by rfl) ⟨5512749, by rfl⟩ : syracuseStep 14700665 = 11025499) B11025499
theorem B9800443 : Blo 1909435 9800443 := bstep (se 1 (by rfl) ⟨7350332, by rfl⟩ : syracuseStep 9800443 = 14700665) B14700665
theorem B13067257 : Blo 1909435 13067257 := bstep (se 2 (by rfl) ⟨4900221, by rfl⟩ : syracuseStep 13067257 = 9800443) B9800443
theorem B17423009 : Blo 1909435 17423009 := bstep (se 2 (by rfl) ⟨6533628, by rfl⟩ : syracuseStep 17423009 = 13067257) B13067257
theorem B11615339 : Blo 1909435 11615339 := bstep (se 1 (by rfl) ⟨8711504, by rfl⟩ : syracuseStep 11615339 = 17423009) B17423009
theorem B7743559 : Blo 1909435 7743559 := bstep (se 1 (by rfl) ⟨5807669, by rfl⟩ : syracuseStep 7743559 = 11615339) B11615339
theorem B10324745 : Blo 1909435 10324745 := bstep (se 2 (by rfl) ⟨3871779, by rfl⟩ : syracuseStep 10324745 = 7743559) B7743559
theorem B6883163 : Blo 1909435 6883163 := bstep (se 1 (by rfl) ⟨5162372, by rfl⟩ : syracuseStep 6883163 = 10324745) B10324745
theorem B4588775 : Blo 1909435 4588775 := bstep (se 1 (by rfl) ⟨3441581, by rfl⟩ : syracuseStep 4588775 = 6883163) B6883163
theorem B3059183 : Blo 1909435 3059183 := bstep (se 1 (by rfl) ⟨2294387, by rfl⟩ : syracuseStep 3059183 = 4588775) B4588775
theorem B2039455 : Blo 1909435 2039455 := bstep (se 1 (by rfl) ⟨1529591, by rfl⟩ : syracuseStep 2039455 = 3059183) B3059183
theorem B2719273 : Blo 1909435 2719273 := bstep (se 2 (by rfl) ⟨1019727, by rfl⟩ : syracuseStep 2719273 = 2039455) B2039455
theorem B3625697 : Blo 1909435 3625697 := bstep (se 2 (by rfl) ⟨1359636, by rfl⟩ : syracuseStep 3625697 = 2719273) B2719273
theorem B2417131 : Blo 1909435 2417131 := bstep (se 1 (by rfl) ⟨1812848, by rfl⟩ : syracuseStep 2417131 = 3625697) B3625697
theorem B3222841 : Blo 1909435 3222841 := bstep (se 2 (by rfl) ⟨1208565, by rfl⟩ : syracuseStep 3222841 = 2417131) B2417131
theorem B4297121 : Blo 1909435 4297121 := bstep (se 2 (by rfl) ⟨1611420, by rfl⟩ : syracuseStep 4297121 = 3222841) B3222841
theorem B2864747 : Blo 1909435 2864747 := bstep (se 1 (by rfl) ⟨2148560, by rfl⟩ : syracuseStep 2864747 = 4297121) B4297121
theorem B1909831 : Blo 1909435 1909831 := bstep (se 1 (by rfl) ⟨1432373, by rfl⟩ : syracuseStep 1909831 = 2864747) B2864747
theorem B2148565 : Blo 1909435 2148565 := bbase (se 7 (by rfl) ⟨25178, by rfl⟩ : syracuseStep 2148565 = 50357) (by norm_num)
theorem B2864753 : Blo 1909435 2864753 := bstep (se 2 (by rfl) ⟨1074282, by rfl⟩ : syracuseStep 2864753 = 2148565) B2148565
theorem B1909835 : Blo 1909435 1909835 := bstep (se 1 (by rfl) ⟨1432376, by rfl⟩ : syracuseStep 1909835 = 2864753) B2864753
theorem B2417141 : Blo 1909435 2417141 := bbase (se 5 (by rfl) ⟨113303, by rfl⟩ : syracuseStep 2417141 = 226607) (by norm_num)
theorem B6445709 : Blo 1909435 6445709 := bstep (se 3 (by rfl) ⟨1208570, by rfl⟩ : syracuseStep 6445709 = 2417141) B2417141
theorem B4297139 : Blo 1909435 4297139 := bstep (se 1 (by rfl) ⟨3222854, by rfl⟩ : syracuseStep 4297139 = 6445709) B6445709
theorem B2864759 : Blo 1909435 2864759 := bstep (se 1 (by rfl) ⟨2148569, by rfl⟩ : syracuseStep 2864759 = 4297139) B4297139
theorem B1909839 : Blo 1909435 1909839 := bstep (se 1 (by rfl) ⟨1432379, by rfl⟩ : syracuseStep 1909839 = 2864759) B2864759
theorem B2864765 : Blo 1909435 2864765 := bbase (se 3 (by rfl) ⟨537143, by rfl⟩ : syracuseStep 2864765 = 1074287) (by norm_num)
theorem B1909843 : Blo 1909435 1909843 := bstep (se 1 (by rfl) ⟨1432382, by rfl⟩ : syracuseStep 1909843 = 2864765) B2864765
theorem B4297157 : Blo 1909435 4297157 := bbase (se 4 (by rfl) ⟨402858, by rfl⟩ : syracuseStep 4297157 = 805717) (by norm_num)
theorem B2864771 : Blo 1909435 2864771 := bstep (se 1 (by rfl) ⟨2148578, by rfl⟩ : syracuseStep 2864771 = 4297157) B4297157
theorem B1909847 : Blo 1909435 1909847 := bstep (se 1 (by rfl) ⟨1432385, by rfl⟩ : syracuseStep 1909847 = 2864771) B2864771
theorem B2581213 : Blo 1909435 2581213 := bbase (se 3 (by rfl) ⟨483977, by rfl⟩ : syracuseStep 2581213 = 967955) (by norm_num)
theorem B3441617 : Blo 1909435 3441617 := bstep (se 2 (by rfl) ⟨1290606, by rfl⟩ : syracuseStep 3441617 = 2581213) B2581213
theorem B2294411 : Blo 1909435 2294411 := bstep (se 1 (by rfl) ⟨1720808, by rfl⟩ : syracuseStep 2294411 = 3441617) B3441617
theorem B6118429 : Blo 1909435 6118429 := bstep (se 3 (by rfl) ⟨1147205, by rfl⟩ : syracuseStep 6118429 = 2294411) B2294411
theorem B8157905 : Blo 1909435 8157905 := bstep (se 2 (by rfl) ⟨3059214, by rfl⟩ : syracuseStep 8157905 = 6118429) B6118429
theorem B5438603 : Blo 1909435 5438603 := bstep (se 1 (by rfl) ⟨4078952, by rfl⟩ : syracuseStep 5438603 = 8157905) B8157905
theorem B3625735 : Blo 1909435 3625735 := bstep (se 1 (by rfl) ⟨2719301, by rfl⟩ : syracuseStep 3625735 = 5438603) B5438603
theorem B4834313 : Blo 1909435 4834313 := bstep (se 2 (by rfl) ⟨1812867, by rfl⟩ : syracuseStep 4834313 = 3625735) B3625735
theorem B3222875 : Blo 1909435 3222875 := bstep (se 1 (by rfl) ⟨2417156, by rfl⟩ : syracuseStep 3222875 = 4834313) B4834313
theorem B2148583 : Blo 1909435 2148583 := bstep (se 1 (by rfl) ⟨1611437, by rfl⟩ : syracuseStep 2148583 = 3222875) B3222875
theorem B2864777 : Blo 1909435 2864777 := bstep (se 2 (by rfl) ⟨1074291, by rfl⟩ : syracuseStep 2864777 = 2148583) B2148583
theorem B1909851 : Blo 1909435 1909851 := bstep (se 1 (by rfl) ⟨1432388, by rfl⟩ : syracuseStep 1909851 = 2864777) B2864777
theorem B9668645 : Blo 1909435 9668645 := bbase (se 4 (by rfl) ⟨906435, by rfl⟩ : syracuseStep 9668645 = 1812871) (by norm_num)
theorem B6445763 : Blo 1909435 6445763 := bstep (se 1 (by rfl) ⟨4834322, by rfl⟩ : syracuseStep 6445763 = 9668645) B9668645
theorem B4297175 : Blo 1909435 4297175 := bstep (se 1 (by rfl) ⟨3222881, by rfl⟩ : syracuseStep 4297175 = 6445763) B6445763
theorem B2864783 : Blo 1909435 2864783 := bstep (se 1 (by rfl) ⟨2148587, by rfl⟩ : syracuseStep 2864783 = 4297175) B4297175
theorem B1909855 : Blo 1909435 1909855 := bstep (se 1 (by rfl) ⟨1432391, by rfl⟩ : syracuseStep 1909855 = 2864783) B2864783
theorem B2864789 : Blo 1909435 2864789 := bbase (se 6 (by rfl) ⟨67143, by rfl⟩ : syracuseStep 2864789 = 134287) (by norm_num)
theorem B1909859 : Blo 1909435 1909859 := bstep (se 1 (by rfl) ⟨1432394, by rfl⟩ : syracuseStep 1909859 = 2864789) B2864789
theorem B2294425 : Blo 1909435 2294425 := bbase (se 2 (by rfl) ⟨860409, by rfl⟩ : syracuseStep 2294425 = 1720819) (by norm_num)
theorem B12236933 : Blo 1909435 12236933 := bstep (se 4 (by rfl) ⟨1147212, by rfl⟩ : syracuseStep 12236933 = 2294425) B2294425
theorem B8157955 : Blo 1909435 8157955 := bstep (se 1 (by rfl) ⟨6118466, by rfl⟩ : syracuseStep 8157955 = 12236933) B12236933
theorem B10877273 : Blo 1909435 10877273 := bstep (se 2 (by rfl) ⟨4078977, by rfl⟩ : syracuseStep 10877273 = 8157955) B8157955
theorem B7251515 : Blo 1909435 7251515 := bstep (se 1 (by rfl) ⟨5438636, by rfl⟩ : syracuseStep 7251515 = 10877273) B10877273
theorem B4834343 : Blo 1909435 4834343 := bstep (se 1 (by rfl) ⟨3625757, by rfl⟩ : syracuseStep 4834343 = 7251515) B7251515
theorem B3222895 : Blo 1909435 3222895 := bstep (se 1 (by rfl) ⟨2417171, by rfl⟩ : syracuseStep 3222895 = 4834343) B4834343
theorem B4297193 : Blo 1909435 4297193 := bstep (se 2 (by rfl) ⟨1611447, by rfl⟩ : syracuseStep 4297193 = 3222895) B3222895
theorem B2864795 : Blo 1909435 2864795 := bstep (se 1 (by rfl) ⟨2148596, by rfl⟩ : syracuseStep 2864795 = 4297193) B4297193
theorem B1909863 : Blo 1909435 1909863 := bstep (se 1 (by rfl) ⟨1432397, by rfl⟩ : syracuseStep 1909863 = 2864795) B2864795
theorem B2148601 : Blo 1909435 2148601 := bbase (se 2 (by rfl) ⟨805725, by rfl⟩ : syracuseStep 2148601 = 1611451) (by norm_num)
theorem B2864801 : Blo 1909435 2864801 := bstep (se 2 (by rfl) ⟨1074300, by rfl⟩ : syracuseStep 2864801 = 2148601) B2148601
theorem B1909867 : Blo 1909435 1909867 := bstep (se 1 (by rfl) ⟨1432400, by rfl⟩ : syracuseStep 1909867 = 2864801) B2864801
theorem B8157989 : Blo 1909435 8157989 := bbase (se 4 (by rfl) ⟨764811, by rfl⟩ : syracuseStep 8157989 = 1529623) (by norm_num)
theorem B5438659 : Blo 1909435 5438659 := bstep (se 1 (by rfl) ⟨4078994, by rfl⟩ : syracuseStep 5438659 = 8157989) B8157989
theorem B7251545 : Blo 1909435 7251545 := bstep (se 2 (by rfl) ⟨2719329, by rfl⟩ : syracuseStep 7251545 = 5438659) B5438659
theorem B4834363 : Blo 1909435 4834363 := bstep (se 1 (by rfl) ⟨3625772, by rfl⟩ : syracuseStep 4834363 = 7251545) B7251545
theorem B6445817 : Blo 1909435 6445817 := bstep (se 2 (by rfl) ⟨2417181, by rfl⟩ : syracuseStep 6445817 = 4834363) B4834363
theorem B4297211 : Blo 1909435 4297211 := bstep (se 1 (by rfl) ⟨3222908, by rfl⟩ : syracuseStep 4297211 = 6445817) B6445817
theorem B2864807 : Blo 1909435 2864807 := bstep (se 1 (by rfl) ⟨2148605, by rfl⟩ : syracuseStep 2864807 = 4297211) B4297211
theorem B1909871 : Blo 1909435 1909871 := bstep (se 1 (by rfl) ⟨1432403, by rfl⟩ : syracuseStep 1909871 = 2864807) B2864807
theorem B2864813 : Blo 1909435 2864813 := bbase (se 3 (by rfl) ⟨537152, by rfl⟩ : syracuseStep 2864813 = 1074305) (by norm_num)
theorem B1909875 : Blo 1909435 1909875 := bstep (se 1 (by rfl) ⟨1432406, by rfl⟩ : syracuseStep 1909875 = 2864813) B2864813
theorem B4297229 : Blo 1909435 4297229 := bbase (se 3 (by rfl) ⟨805730, by rfl⟩ : syracuseStep 4297229 = 1611461) (by norm_num)
theorem B2864819 : Blo 1909435 2864819 := bstep (se 1 (by rfl) ⟨2148614, by rfl⟩ : syracuseStep 2864819 = 4297229) B4297229
theorem B1909879 : Blo 1909435 1909879 := bstep (se 1 (by rfl) ⟨1432409, by rfl⟩ : syracuseStep 1909879 = 2864819) B2864819
theorem B2417197 : Blo 1909435 2417197 := bbase (se 3 (by rfl) ⟨453224, by rfl⟩ : syracuseStep 2417197 = 906449) (by norm_num)
theorem B3222929 : Blo 1909435 3222929 := bstep (se 2 (by rfl) ⟨1208598, by rfl⟩ : syracuseStep 3222929 = 2417197) B2417197
theorem B2148619 : Blo 1909435 2148619 := bstep (se 1 (by rfl) ⟨1611464, by rfl⟩ : syracuseStep 2148619 = 3222929) B3222929
theorem B2864825 : Blo 1909435 2864825 := bstep (se 2 (by rfl) ⟨1074309, by rfl⟩ : syracuseStep 2864825 = 2148619) B2148619
theorem B1909883 : Blo 1909435 1909883 := bstep (se 1 (by rfl) ⟨1432412, by rfl⟩ : syracuseStep 1909883 = 2864825) B2864825
theorem B3266909 : Blo 1909435 3266909 := bbase (se 3 (by rfl) ⟨612545, by rfl⟩ : syracuseStep 3266909 = 1225091) (by norm_num)
theorem B2177939 : Blo 1909435 2177939 := bstep (se 1 (by rfl) ⟨1633454, by rfl⟩ : syracuseStep 2177939 = 3266909) B3266909
theorem B5807837 : Blo 1909435 5807837 := bstep (se 3 (by rfl) ⟨1088969, by rfl⟩ : syracuseStep 5807837 = 2177939) B2177939
theorem B3871891 : Blo 1909435 3871891 := bstep (se 1 (by rfl) ⟨2903918, by rfl⟩ : syracuseStep 3871891 = 5807837) B5807837
theorem B5162521 : Blo 1909435 5162521 := bstep (se 2 (by rfl) ⟨1935945, by rfl⟩ : syracuseStep 5162521 = 3871891) B3871891
theorem B6883361 : Blo 1909435 6883361 := bstep (se 2 (by rfl) ⟨2581260, by rfl⟩ : syracuseStep 6883361 = 5162521) B5162521
theorem B4588907 : Blo 1909435 4588907 := bstep (se 1 (by rfl) ⟨3441680, by rfl⟩ : syracuseStep 4588907 = 6883361) B6883361
theorem B12237085 : Blo 1909435 12237085 := bstep (se 3 (by rfl) ⟨2294453, by rfl⟩ : syracuseStep 12237085 = 4588907) B4588907
theorem B16316113 : Blo 1909435 16316113 := bstep (se 2 (by rfl) ⟨6118542, by rfl⟩ : syracuseStep 16316113 = 12237085) B12237085
theorem B21754817 : Blo 1909435 21754817 := bstep (se 2 (by rfl) ⟨8158056, by rfl⟩ : syracuseStep 21754817 = 16316113) B16316113
theorem B14503211 : Blo 1909435 14503211 := bstep (se 1 (by rfl) ⟨10877408, by rfl⟩ : syracuseStep 14503211 = 21754817) B21754817
theorem B9668807 : Blo 1909435 9668807 := bstep (se 1 (by rfl) ⟨7251605, by rfl⟩ : syracuseStep 9668807 = 14503211) B14503211
theorem B6445871 : Blo 1909435 6445871 := bstep (se 1 (by rfl) ⟨4834403, by rfl⟩ : syracuseStep 6445871 = 9668807) B9668807
theorem B4297247 : Blo 1909435 4297247 := bstep (se 1 (by rfl) ⟨3222935, by rfl⟩ : syracuseStep 4297247 = 6445871) B6445871
theorem B2864831 : Blo 1909435 2864831 := bstep (se 1 (by rfl) ⟨2148623, by rfl⟩ : syracuseStep 2864831 = 4297247) B4297247
theorem B1909887 : Blo 1909435 1909887 := bstep (se 1 (by rfl) ⟨1432415, by rfl⟩ : syracuseStep 1909887 = 2864831) B2864831
theorem B2864837 : Blo 1909435 2864837 := bbase (se 4 (by rfl) ⟨268578, by rfl⟩ : syracuseStep 2864837 = 537157) (by norm_num)
theorem B1909891 : Blo 1909435 1909891 := bstep (se 1 (by rfl) ⟨1432418, by rfl⟩ : syracuseStep 1909891 = 2864837) B2864837
theorem B3222949 : Blo 1909435 3222949 := bbase (se 4 (by rfl) ⟨302151, by rfl⟩ : syracuseStep 3222949 = 604303) (by norm_num)
theorem B4297265 : Blo 1909435 4297265 := bstep (se 2 (by rfl) ⟨1611474, by rfl⟩ : syracuseStep 4297265 = 3222949) B3222949
theorem B2864843 : Blo 1909435 2864843 := bstep (se 1 (by rfl) ⟨2148632, by rfl⟩ : syracuseStep 2864843 = 4297265) B4297265
theorem B1909895 : Blo 1909435 1909895 := bstep (se 1 (by rfl) ⟨1432421, by rfl⟩ : syracuseStep 1909895 = 2864843) B2864843
theorem B2148637 : Blo 1909435 2148637 := bbase (se 3 (by rfl) ⟨402869, by rfl⟩ : syracuseStep 2148637 = 805739) (by norm_num)
theorem B2864849 : Blo 1909435 2864849 := bstep (se 2 (by rfl) ⟨1074318, by rfl⟩ : syracuseStep 2864849 = 2148637) B2148637
theorem B1909899 : Blo 1909435 1909899 := bstep (se 1 (by rfl) ⟨1432424, by rfl⟩ : syracuseStep 1909899 = 2864849) B2864849
theorem B6445925 : Blo 1909435 6445925 := bbase (se 4 (by rfl) ⟨604305, by rfl⟩ : syracuseStep 6445925 = 1208611) (by norm_num)
theorem B4297283 : Blo 1909435 4297283 := bstep (se 1 (by rfl) ⟨3222962, by rfl⟩ : syracuseStep 4297283 = 6445925) B6445925
theorem B2864855 : Blo 1909435 2864855 := bstep (se 1 (by rfl) ⟨2148641, by rfl⟩ : syracuseStep 2864855 = 4297283) B4297283
theorem B1909903 : Blo 1909435 1909903 := bstep (se 1 (by rfl) ⟨1432427, by rfl⟩ : syracuseStep 1909903 = 2864855) B2864855
theorem B2864861 : Blo 1909435 2864861 := bbase (se 3 (by rfl) ⟨537161, by rfl⟩ : syracuseStep 2864861 = 1074323) (by norm_num)
theorem B1909907 : Blo 1909435 1909907 := bstep (se 1 (by rfl) ⟨1432430, by rfl⟩ : syracuseStep 1909907 = 2864861) B2864861
theorem B4297301 : Blo 1909435 4297301 := bbase (se 8 (by rfl) ⟨25179, by rfl⟩ : syracuseStep 4297301 = 50359) (by norm_num)
theorem B2864867 : Blo 1909435 2864867 := bstep (se 1 (by rfl) ⟨2148650, by rfl⟩ : syracuseStep 2864867 = 4297301) B4297301
theorem B1909911 : Blo 1909435 1909911 := bstep (se 1 (by rfl) ⟨1432433, by rfl⟩ : syracuseStep 1909911 = 2864867) B2864867
theorem B3059317 : Blo 1909435 3059317 := bbase (se 5 (by rfl) ⟨143405, by rfl⟩ : syracuseStep 3059317 = 286811) (by norm_num)
theorem B4079089 : Blo 1909435 4079089 := bstep (se 2 (by rfl) ⟨1529658, by rfl⟩ : syracuseStep 4079089 = 3059317) B3059317
theorem B5438785 : Blo 1909435 5438785 := bstep (se 2 (by rfl) ⟨2039544, by rfl⟩ : syracuseStep 5438785 = 4079089) B4079089
theorem B7251713 : Blo 1909435 7251713 := bstep (se 2 (by rfl) ⟨2719392, by rfl⟩ : syracuseStep 7251713 = 5438785) B5438785
theorem B4834475 : Blo 1909435 4834475 := bstep (se 1 (by rfl) ⟨3625856, by rfl⟩ : syracuseStep 4834475 = 7251713) B7251713
theorem B3222983 : Blo 1909435 3222983 := bstep (se 1 (by rfl) ⟨2417237, by rfl⟩ : syracuseStep 3222983 = 4834475) B4834475
theorem B2148655 : Blo 1909435 2148655 := bstep (se 1 (by rfl) ⟨1611491, by rfl⟩ : syracuseStep 2148655 = 3222983) B3222983
theorem B2864873 : Blo 1909435 2864873 := bstep (se 2 (by rfl) ⟨1074327, by rfl⟩ : syracuseStep 2864873 = 2148655) B2148655
theorem B1909915 : Blo 1909435 1909915 := bstep (se 1 (by rfl) ⟨1432436, by rfl⟩ : syracuseStep 1909915 = 2864873) B2864873
theorem B24474581 : Blo 1909435 24474581 := bbase (se 7 (by rfl) ⟨286811, by rfl⟩ : syracuseStep 24474581 = 573623) (by norm_num)
theorem B16316387 : Blo 1909435 16316387 := bstep (se 1 (by rfl) ⟨12237290, by rfl⟩ : syracuseStep 16316387 = 24474581) B24474581
theorem B10877591 : Blo 1909435 10877591 := bstep (se 1 (by rfl) ⟨8158193, by rfl⟩ : syracuseStep 10877591 = 16316387) B16316387
theorem B7251727 : Blo 1909435 7251727 := bstep (se 1 (by rfl) ⟨5438795, by rfl⟩ : syracuseStep 7251727 = 10877591) B10877591
theorem B9668969 : Blo 1909435 9668969 := bstep (se 2 (by rfl) ⟨3625863, by rfl⟩ : syracuseStep 9668969 = 7251727) B7251727
theorem B6445979 : Blo 1909435 6445979 := bstep (se 1 (by rfl) ⟨4834484, by rfl⟩ : syracuseStep 6445979 = 9668969) B9668969
theorem B4297319 : Blo 1909435 4297319 := bstep (se 1 (by rfl) ⟨3222989, by rfl⟩ : syracuseStep 4297319 = 6445979) B6445979
theorem B2864879 : Blo 1909435 2864879 := bstep (se 1 (by rfl) ⟨2148659, by rfl⟩ : syracuseStep 2864879 = 4297319) B4297319
theorem B1909919 : Blo 1909435 1909919 := bstep (se 1 (by rfl) ⟨1432439, by rfl⟩ : syracuseStep 1909919 = 2864879) B2864879
theorem B2864885 : Blo 1909435 2864885 := bbase (se 5 (by rfl) ⟨134291, by rfl⟩ : syracuseStep 2864885 = 268583) (by norm_num)
theorem B1909923 : Blo 1909435 1909923 := bstep (se 1 (by rfl) ⟨1432442, by rfl⟩ : syracuseStep 1909923 = 2864885) B2864885
theorem B8158229 : Blo 1909435 8158229 := bbase (se 6 (by rfl) ⟨191208, by rfl⟩ : syracuseStep 8158229 = 382417) (by norm_num)
theorem B5438819 : Blo 1909435 5438819 := bstep (se 1 (by rfl) ⟨4079114, by rfl⟩ : syracuseStep 5438819 = 8158229) B8158229
theorem B3625879 : Blo 1909435 3625879 := bstep (se 1 (by rfl) ⟨2719409, by rfl⟩ : syracuseStep 3625879 = 5438819) B5438819
theorem B4834505 : Blo 1909435 4834505 := bstep (se 2 (by rfl) ⟨1812939, by rfl⟩ : syracuseStep 4834505 = 3625879) B3625879
theorem B3223003 : Blo 1909435 3223003 := bstep (se 1 (by rfl) ⟨2417252, by rfl⟩ : syracuseStep 3223003 = 4834505) B4834505
theorem B4297337 : Blo 1909435 4297337 := bstep (se 2 (by rfl) ⟨1611501, by rfl⟩ : syracuseStep 4297337 = 3223003) B3223003
theorem B2864891 : Blo 1909435 2864891 := bstep (se 1 (by rfl) ⟨2148668, by rfl⟩ : syracuseStep 2864891 = 4297337) B4297337
theorem B1909927 : Blo 1909435 1909927 := bstep (se 1 (by rfl) ⟨1432445, by rfl⟩ : syracuseStep 1909927 = 2864891) B2864891
theorem B2148673 : Blo 1909435 2148673 := bbase (se 2 (by rfl) ⟨805752, by rfl⟩ : syracuseStep 2148673 = 1611505) (by norm_num)
theorem B2864897 : Blo 1909435 2864897 := bstep (se 2 (by rfl) ⟨1074336, by rfl⟩ : syracuseStep 2864897 = 2148673) B2148673
theorem B1909931 : Blo 1909435 1909931 := bstep (se 1 (by rfl) ⟨1432448, by rfl⟩ : syracuseStep 1909931 = 2864897) B2864897
theorem B4834525 : Blo 1909435 4834525 := bbase (se 3 (by rfl) ⟨906473, by rfl⟩ : syracuseStep 4834525 = 1812947) (by norm_num)
theorem B6446033 : Blo 1909435 6446033 := bstep (se 2 (by rfl) ⟨2417262, by rfl⟩ : syracuseStep 6446033 = 4834525) B4834525
theorem B4297355 : Blo 1909435 4297355 := bstep (se 1 (by rfl) ⟨3223016, by rfl⟩ : syracuseStep 4297355 = 6446033) B6446033
theorem B2864903 : Blo 1909435 2864903 := bstep (se 1 (by rfl) ⟨2148677, by rfl⟩ : syracuseStep 2864903 = 4297355) B4297355
theorem B1909935 : Blo 1909435 1909935 := bstep (se 1 (by rfl) ⟨1432451, by rfl⟩ : syracuseStep 1909935 = 2864903) B2864903
theorem B2864909 : Blo 1909435 2864909 := bbase (se 3 (by rfl) ⟨537170, by rfl⟩ : syracuseStep 2864909 = 1074341) (by norm_num)
theorem B1909939 : Blo 1909435 1909939 := bstep (se 1 (by rfl) ⟨1432454, by rfl⟩ : syracuseStep 1909939 = 2864909) B2864909
theorem B4297373 : Blo 1909435 4297373 := bbase (se 3 (by rfl) ⟨805757, by rfl⟩ : syracuseStep 4297373 = 1611515) (by norm_num)
theorem B2864915 : Blo 1909435 2864915 := bstep (se 1 (by rfl) ⟨2148686, by rfl⟩ : syracuseStep 2864915 = 4297373) B4297373
theorem B1909943 : Blo 1909435 1909943 := bstep (se 1 (by rfl) ⟨1432457, by rfl⟩ : syracuseStep 1909943 = 2864915) B2864915
theorem B3223037 : Blo 1909435 3223037 := bbase (se 3 (by rfl) ⟨604319, by rfl⟩ : syracuseStep 3223037 = 1208639) (by norm_num)
theorem B2148691 : Blo 1909435 2148691 := bstep (se 1 (by rfl) ⟨1611518, by rfl⟩ : syracuseStep 2148691 = 3223037) B3223037
theorem B2864921 : Blo 1909435 2864921 := bstep (se 2 (by rfl) ⟨1074345, by rfl⟩ : syracuseStep 2864921 = 2148691) B2148691
theorem B1909947 : Blo 1909435 1909947 := bstep (se 1 (by rfl) ⟨1432460, by rfl⟩ : syracuseStep 1909947 = 2864921) B2864921
theorem B4079165 : Blo 1909435 4079165 := bbase (se 3 (by rfl) ⟨764843, by rfl⟩ : syracuseStep 4079165 = 1529687) (by norm_num)
theorem B10877773 : Blo 1909435 10877773 := bstep (se 3 (by rfl) ⟨2039582, by rfl⟩ : syracuseStep 10877773 = 4079165) B4079165
theorem B14503697 : Blo 1909435 14503697 := bstep (se 2 (by rfl) ⟨5438886, by rfl⟩ : syracuseStep 14503697 = 10877773) B10877773
theorem B9669131 : Blo 1909435 9669131 := bstep (se 1 (by rfl) ⟨7251848, by rfl⟩ : syracuseStep 9669131 = 14503697) B14503697
theorem B6446087 : Blo 1909435 6446087 := bstep (se 1 (by rfl) ⟨4834565, by rfl⟩ : syracuseStep 6446087 = 9669131) B9669131
theorem B4297391 : Blo 1909435 4297391 := bstep (se 1 (by rfl) ⟨3223043, by rfl⟩ : syracuseStep 4297391 = 6446087) B6446087
theorem B2864927 : Blo 1909435 2864927 := bstep (se 1 (by rfl) ⟨2148695, by rfl⟩ : syracuseStep 2864927 = 4297391) B4297391
theorem B1909951 : Blo 1909435 1909951 := bstep (se 1 (by rfl) ⟨1432463, by rfl⟩ : syracuseStep 1909951 = 2864927) B2864927
theorem B2864933 : Blo 1909435 2864933 := bbase (se 4 (by rfl) ⟨268587, by rfl⟩ : syracuseStep 2864933 = 537175) (by norm_num)
theorem B1909955 : Blo 1909435 1909955 := bstep (se 1 (by rfl) ⟨1432466, by rfl⟩ : syracuseStep 1909955 = 2864933) B2864933
theorem B2417293 : Blo 1909435 2417293 := bbase (se 3 (by rfl) ⟨453242, by rfl⟩ : syracuseStep 2417293 = 906485) (by norm_num)
theorem B3223057 : Blo 1909435 3223057 := bstep (se 2 (by rfl) ⟨1208646, by rfl⟩ : syracuseStep 3223057 = 2417293) B2417293
theorem B4297409 : Blo 1909435 4297409 := bstep (se 2 (by rfl) ⟨1611528, by rfl⟩ : syracuseStep 4297409 = 3223057) B3223057
theorem B2864939 : Blo 1909435 2864939 := bstep (se 1 (by rfl) ⟨2148704, by rfl⟩ : syracuseStep 2864939 = 4297409) B4297409
theorem B1909959 : Blo 1909435 1909959 := bstep (se 1 (by rfl) ⟨1432469, by rfl⟩ : syracuseStep 1909959 = 2864939) B2864939
theorem B2148709 : Blo 1909435 2148709 := bbase (se 4 (by rfl) ⟨201441, by rfl⟩ : syracuseStep 2148709 = 402883) (by norm_num)
theorem B2864945 : Blo 1909435 2864945 := bstep (se 2 (by rfl) ⟨1074354, by rfl⟩ : syracuseStep 2864945 = 2148709) B2148709
theorem B1909963 : Blo 1909435 1909963 := bstep (se 1 (by rfl) ⟨1432472, by rfl⟩ : syracuseStep 1909963 = 2864945) B2864945
theorem B5438933 : Blo 1909435 5438933 := bbase (se 7 (by rfl) ⟨63737, by rfl⟩ : syracuseStep 5438933 = 127475) (by norm_num)
theorem B3625955 : Blo 1909435 3625955 := bstep (se 1 (by rfl) ⟨2719466, by rfl⟩ : syracuseStep 3625955 = 5438933) B5438933
theorem B2417303 : Blo 1909435 2417303 := bstep (se 1 (by rfl) ⟨1812977, by rfl⟩ : syracuseStep 2417303 = 3625955) B3625955
theorem B6446141 : Blo 1909435 6446141 := bstep (se 3 (by rfl) ⟨1208651, by rfl⟩ : syracuseStep 6446141 = 2417303) B2417303
theorem B4297427 : Blo 1909435 4297427 := bstep (se 1 (by rfl) ⟨3223070, by rfl⟩ : syracuseStep 4297427 = 6446141) B6446141
theorem B2864951 : Blo 1909435 2864951 := bstep (se 1 (by rfl) ⟨2148713, by rfl⟩ : syracuseStep 2864951 = 4297427) B4297427
theorem B1909967 : Blo 1909435 1909967 := bstep (se 1 (by rfl) ⟨1432475, by rfl⟩ : syracuseStep 1909967 = 2864951) B2864951
theorem B2864957 : Blo 1909435 2864957 := bbase (se 3 (by rfl) ⟨537179, by rfl⟩ : syracuseStep 2864957 = 1074359) (by norm_num)
theorem B1909971 : Blo 1909435 1909971 := bstep (se 1 (by rfl) ⟨1432478, by rfl⟩ : syracuseStep 1909971 = 2864957) B2864957
theorem B4297445 : Blo 1909435 4297445 := bbase (se 4 (by rfl) ⟨402885, by rfl⟩ : syracuseStep 4297445 = 805771) (by norm_num)
theorem B2864963 : Blo 1909435 2864963 := bstep (se 1 (by rfl) ⟨2148722, by rfl⟩ : syracuseStep 2864963 = 4297445) B4297445
theorem B1909975 : Blo 1909435 1909975 := bstep (se 1 (by rfl) ⟨1432481, by rfl⟩ : syracuseStep 1909975 = 2864963) B2864963
theorem B4834637 : Blo 1909435 4834637 := bbase (se 3 (by rfl) ⟨906494, by rfl⟩ : syracuseStep 4834637 = 1812989) (by norm_num)
theorem B3223091 : Blo 1909435 3223091 := bstep (se 1 (by rfl) ⟨2417318, by rfl⟩ : syracuseStep 3223091 = 4834637) B4834637
theorem B2148727 : Blo 1909435 2148727 := bstep (se 1 (by rfl) ⟨1611545, by rfl⟩ : syracuseStep 2148727 = 3223091) B3223091
theorem B2864969 : Blo 1909435 2864969 := bstep (se 2 (by rfl) ⟨1074363, by rfl⟩ : syracuseStep 2864969 = 2148727) B2148727
theorem B1909979 : Blo 1909435 1909979 := bstep (se 1 (by rfl) ⟨1432484, by rfl⟩ : syracuseStep 1909979 = 2864969) B2864969
theorem B2039617 : Blo 1909435 2039617 := bbase (se 2 (by rfl) ⟨764856, by rfl⟩ : syracuseStep 2039617 = 1529713) (by norm_num)
theorem B2719489 : Blo 1909435 2719489 := bstep (se 2 (by rfl) ⟨1019808, by rfl⟩ : syracuseStep 2719489 = 2039617) B2039617
theorem B3625985 : Blo 1909435 3625985 := bstep (se 2 (by rfl) ⟨1359744, by rfl⟩ : syracuseStep 3625985 = 2719489) B2719489
theorem B9669293 : Blo 1909435 9669293 := bstep (se 3 (by rfl) ⟨1812992, by rfl⟩ : syracuseStep 9669293 = 3625985) B3625985
theorem B6446195 : Blo 1909435 6446195 := bstep (se 1 (by rfl) ⟨4834646, by rfl⟩ : syracuseStep 6446195 = 9669293) B9669293
theorem B4297463 : Blo 1909435 4297463 := bstep (se 1 (by rfl) ⟨3223097, by rfl⟩ : syracuseStep 4297463 = 6446195) B6446195
theorem B2864975 : Blo 1909435 2864975 := bstep (se 1 (by rfl) ⟨2148731, by rfl⟩ : syracuseStep 2864975 = 4297463) B4297463
theorem B1909983 : Blo 1909435 1909983 := bstep (se 1 (by rfl) ⟨1432487, by rfl⟩ : syracuseStep 1909983 = 2864975) B2864975
theorem B2864981 : Blo 1909435 2864981 := bbase (se 9 (by rfl) ⟨8393, by rfl⟩ : syracuseStep 2864981 = 16787) (by norm_num)
theorem B1909987 : Blo 1909435 1909987 := bstep (se 1 (by rfl) ⟨1432490, by rfl⟩ : syracuseStep 1909987 = 2864981) B2864981
theorem B3441869 : Blo 1909435 3441869 := bbase (se 3 (by rfl) ⟨645350, by rfl⟩ : syracuseStep 3441869 = 1290701) (by norm_num)
theorem B2294579 : Blo 1909435 2294579 := bstep (se 1 (by rfl) ⟨1720934, by rfl⟩ : syracuseStep 2294579 = 3441869) B3441869
theorem B6118877 : Blo 1909435 6118877 := bstep (se 3 (by rfl) ⟨1147289, by rfl⟩ : syracuseStep 6118877 = 2294579) B2294579
theorem B4079251 : Blo 1909435 4079251 := bstep (se 1 (by rfl) ⟨3059438, by rfl⟩ : syracuseStep 4079251 = 6118877) B6118877
theorem B5439001 : Blo 1909435 5439001 := bstep (se 2 (by rfl) ⟨2039625, by rfl⟩ : syracuseStep 5439001 = 4079251) B4079251
theorem B7252001 : Blo 1909435 7252001 := bstep (se 2 (by rfl) ⟨2719500, by rfl⟩ : syracuseStep 7252001 = 5439001) B5439001
theorem B4834667 : Blo 1909435 4834667 := bstep (se 1 (by rfl) ⟨3626000, by rfl⟩ : syracuseStep 4834667 = 7252001) B7252001
theorem B3223111 : Blo 1909435 3223111 := bstep (se 1 (by rfl) ⟨2417333, by rfl⟩ : syracuseStep 3223111 = 4834667) B4834667
theorem B4297481 : Blo 1909435 4297481 := bstep (se 2 (by rfl) ⟨1611555, by rfl⟩ : syracuseStep 4297481 = 3223111) B3223111
theorem B2864987 : Blo 1909435 2864987 := bstep (se 1 (by rfl) ⟨2148740, by rfl⟩ : syracuseStep 2864987 = 4297481) B4297481
theorem B1909991 : Blo 1909435 1909991 := bstep (se 1 (by rfl) ⟨1432493, by rfl⟩ : syracuseStep 1909991 = 2864987) B2864987
theorem B2148745 : Blo 1909435 2148745 := bbase (se 2 (by rfl) ⟨805779, by rfl⟩ : syracuseStep 2148745 = 1611559) (by norm_num)
theorem B2864993 : Blo 1909435 2864993 := bstep (se 2 (by rfl) ⟨1074372, by rfl⟩ : syracuseStep 2864993 = 2148745) B2148745
theorem B1909995 : Blo 1909435 1909995 := bstep (se 1 (by rfl) ⟨1432496, by rfl⟩ : syracuseStep 1909995 = 2864993) B2864993
theorem B18607157 : Blo 1909435 18607157 := bbase (se 5 (by rfl) ⟨872210, by rfl⟩ : syracuseStep 18607157 = 1744421) (by norm_num)
theorem B12404771 : Blo 1909435 12404771 := bstep (se 1 (by rfl) ⟨9303578, by rfl⟩ : syracuseStep 12404771 = 18607157) B18607157
theorem B8269847 : Blo 1909435 8269847 := bstep (se 1 (by rfl) ⟨6202385, by rfl⟩ : syracuseStep 8269847 = 12404771) B12404771
theorem B5513231 : Blo 1909435 5513231 := bstep (se 1 (by rfl) ⟨4134923, by rfl⟩ : syracuseStep 5513231 = 8269847) B8269847
theorem B14701949 : Blo 1909435 14701949 := bstep (se 3 (by rfl) ⟨2756615, by rfl⟩ : syracuseStep 14701949 = 5513231) B5513231
theorem B9801299 : Blo 1909435 9801299 := bstep (se 1 (by rfl) ⟨7350974, by rfl⟩ : syracuseStep 9801299 = 14701949) B14701949
theorem B6534199 : Blo 1909435 6534199 := bstep (se 1 (by rfl) ⟨4900649, by rfl⟩ : syracuseStep 6534199 = 9801299) B9801299
theorem B34849061 : Blo 1909435 34849061 := bstep (se 4 (by rfl) ⟨3267099, by rfl⟩ : syracuseStep 34849061 = 6534199) B6534199
theorem B23232707 : Blo 1909435 23232707 := bstep (se 1 (by rfl) ⟨17424530, by rfl⟩ : syracuseStep 23232707 = 34849061) B34849061
theorem B15488471 : Blo 1909435 15488471 := bstep (se 1 (by rfl) ⟨11616353, by rfl⟩ : syracuseStep 15488471 = 23232707) B23232707
theorem B10325647 : Blo 1909435 10325647 := bstep (se 1 (by rfl) ⟨7744235, by rfl⟩ : syracuseStep 10325647 = 15488471) B15488471
theorem B55070117 : Blo 1909435 55070117 := bstep (se 4 (by rfl) ⟨5162823, by rfl⟩ : syracuseStep 55070117 = 10325647) B10325647
theorem B36713411 : Blo 1909435 36713411 := bstep (se 1 (by rfl) ⟨27535058, by rfl⟩ : syracuseStep 36713411 = 55070117) B55070117
theorem B24475607 : Blo 1909435 24475607 := bstep (se 1 (by rfl) ⟨18356705, by rfl⟩ : syracuseStep 24475607 = 36713411) B36713411
theorem B16317071 : Blo 1909435 16317071 := bstep (se 1 (by rfl) ⟨12237803, by rfl⟩ : syracuseStep 16317071 = 24475607) B24475607
theorem B10878047 : Blo 1909435 10878047 := bstep (se 1 (by rfl) ⟨8158535, by rfl⟩ : syracuseStep 10878047 = 16317071) B16317071
theorem B7252031 : Blo 1909435 7252031 := bstep (se 1 (by rfl) ⟨5439023, by rfl⟩ : syracuseStep 7252031 = 10878047) B10878047
theorem B4834687 : Blo 1909435 4834687 := bstep (se 1 (by rfl) ⟨3626015, by rfl⟩ : syracuseStep 4834687 = 7252031) B7252031
theorem B6446249 : Blo 1909435 6446249 := bstep (se 2 (by rfl) ⟨2417343, by rfl⟩ : syracuseStep 6446249 = 4834687) B4834687
theorem B4297499 : Blo 1909435 4297499 := bstep (se 1 (by rfl) ⟨3223124, by rfl⟩ : syracuseStep 4297499 = 6446249) B6446249
theorem B2864999 : Blo 1909435 2864999 := bstep (se 1 (by rfl) ⟨2148749, by rfl⟩ : syracuseStep 2864999 = 4297499) B4297499
theorem B1909999 : Blo 1909435 1909999 := bstep (se 1 (by rfl) ⟨1432499, by rfl⟩ : syracuseStep 1909999 = 2864999) B2864999
theorem B2865005 : Blo 1909435 2865005 := bbase (se 3 (by rfl) ⟨537188, by rfl⟩ : syracuseStep 2865005 = 1074377) (by norm_num)
theorem B1910003 : Blo 1909435 1910003 := bstep (se 1 (by rfl) ⟨1432502, by rfl⟩ : syracuseStep 1910003 = 2865005) B2865005
theorem B4297517 : Blo 1909435 4297517 := bbase (se 3 (by rfl) ⟨805784, by rfl⟩ : syracuseStep 4297517 = 1611569) (by norm_num)
theorem B2865011 : Blo 1909435 2865011 := bstep (se 1 (by rfl) ⟨2148758, by rfl⟩ : syracuseStep 2865011 = 4297517) B4297517
theorem B1910007 : Blo 1909435 1910007 := bstep (se 1 (by rfl) ⟨1432505, by rfl⟩ : syracuseStep 1910007 = 2865011) B2865011
theorem B10325717 : Blo 1909435 10325717 := bbase (se 7 (by rfl) ⟨121004, by rfl⟩ : syracuseStep 10325717 = 242009) (by norm_num)
theorem B6883811 : Blo 1909435 6883811 := bstep (se 1 (by rfl) ⟨5162858, by rfl⟩ : syracuseStep 6883811 = 10325717) B10325717
theorem B4589207 : Blo 1909435 4589207 := bstep (se 1 (by rfl) ⟨3441905, by rfl⟩ : syracuseStep 4589207 = 6883811) B6883811
theorem B3059471 : Blo 1909435 3059471 := bstep (se 1 (by rfl) ⟨2294603, by rfl⟩ : syracuseStep 3059471 = 4589207) B4589207
theorem B8158589 : Blo 1909435 8158589 := bstep (se 3 (by rfl) ⟨1529735, by rfl⟩ : syracuseStep 8158589 = 3059471) B3059471
theorem B5439059 : Blo 1909435 5439059 := bstep (se 1 (by rfl) ⟨4079294, by rfl⟩ : syracuseStep 5439059 = 8158589) B8158589
theorem B3626039 : Blo 1909435 3626039 := bstep (se 1 (by rfl) ⟨2719529, by rfl⟩ : syracuseStep 3626039 = 5439059) B5439059
theorem B2417359 : Blo 1909435 2417359 := bstep (se 1 (by rfl) ⟨1813019, by rfl⟩ : syracuseStep 2417359 = 3626039) B3626039
theorem B3223145 : Blo 1909435 3223145 := bstep (se 2 (by rfl) ⟨1208679, by rfl⟩ : syracuseStep 3223145 = 2417359) B2417359
theorem B2148763 : Blo 1909435 2148763 := bstep (se 1 (by rfl) ⟨1611572, by rfl⟩ : syracuseStep 2148763 = 3223145) B3223145
theorem B2865017 : Blo 1909435 2865017 := bstep (se 2 (by rfl) ⟨1074381, by rfl⟩ : syracuseStep 2865017 = 2148763) B2148763
theorem B1910011 : Blo 1909435 1910011 := bstep (se 1 (by rfl) ⟨1432508, by rfl⟩ : syracuseStep 1910011 = 2865017) B2865017
theorem B2178085 : Blo 1909435 2178085 := bbase (se 4 (by rfl) ⟨204195, by rfl⟩ : syracuseStep 2178085 = 408391) (by norm_num)
theorem B2904113 : Blo 1909435 2904113 := bstep (se 2 (by rfl) ⟨1089042, by rfl⟩ : syracuseStep 2904113 = 2178085) B2178085
theorem B7744301 : Blo 1909435 7744301 := bstep (se 3 (by rfl) ⟨1452056, by rfl⟩ : syracuseStep 7744301 = 2904113) B2904113
theorem B5162867 : Blo 1909435 5162867 := bstep (se 1 (by rfl) ⟨3872150, by rfl⟩ : syracuseStep 5162867 = 7744301) B7744301
theorem B3441911 : Blo 1909435 3441911 := bstep (se 1 (by rfl) ⟨2581433, by rfl⟩ : syracuseStep 3441911 = 5162867) B5162867
theorem B9178429 : Blo 1909435 9178429 := bstep (se 3 (by rfl) ⟨1720955, by rfl⟩ : syracuseStep 9178429 = 3441911) B3441911
theorem B12237905 : Blo 1909435 12237905 := bstep (se 2 (by rfl) ⟨4589214, by rfl⟩ : syracuseStep 12237905 = 9178429) B9178429
theorem B32634413 : Blo 1909435 32634413 := bstep (se 3 (by rfl) ⟨6118952, by rfl⟩ : syracuseStep 32634413 = 12237905) B12237905
theorem B21756275 : Blo 1909435 21756275 := bstep (se 1 (by rfl) ⟨16317206, by rfl⟩ : syracuseStep 21756275 = 32634413) B32634413
theorem B14504183 : Blo 1909435 14504183 := bstep (se 1 (by rfl) ⟨10878137, by rfl⟩ : syracuseStep 14504183 = 21756275) B21756275
theorem B9669455 : Blo 1909435 9669455 := bstep (se 1 (by rfl) ⟨7252091, by rfl⟩ : syracuseStep 9669455 = 14504183) B14504183
theorem B6446303 : Blo 1909435 6446303 := bstep (se 1 (by rfl) ⟨4834727, by rfl⟩ : syracuseStep 6446303 = 9669455) B9669455
theorem B4297535 : Blo 1909435 4297535 := bstep (se 1 (by rfl) ⟨3223151, by rfl⟩ : syracuseStep 4297535 = 6446303) B6446303
theorem B2865023 : Blo 1909435 2865023 := bstep (se 1 (by rfl) ⟨2148767, by rfl⟩ : syracuseStep 2865023 = 4297535) B4297535
theorem B1910015 : Blo 1909435 1910015 := bstep (se 1 (by rfl) ⟨1432511, by rfl⟩ : syracuseStep 1910015 = 2865023) B2865023
theorem B2865029 : Blo 1909435 2865029 := bbase (se 4 (by rfl) ⟨268596, by rfl⟩ : syracuseStep 2865029 = 537193) (by norm_num)
theorem B1910019 : Blo 1909435 1910019 := bstep (se 1 (by rfl) ⟨1432514, by rfl⟩ : syracuseStep 1910019 = 2865029) B2865029
theorem B3223165 : Blo 1909435 3223165 := bbase (se 3 (by rfl) ⟨604343, by rfl⟩ : syracuseStep 3223165 = 1208687) (by norm_num)
theorem B4297553 : Blo 1909435 4297553 := bstep (se 2 (by rfl) ⟨1611582, by rfl⟩ : syracuseStep 4297553 = 3223165) B3223165
theorem B2865035 : Blo 1909435 2865035 := bstep (se 1 (by rfl) ⟨2148776, by rfl⟩ : syracuseStep 2865035 = 4297553) B4297553
theorem B1910023 : Blo 1909435 1910023 := bstep (se 1 (by rfl) ⟨1432517, by rfl⟩ : syracuseStep 1910023 = 2865035) B2865035
theorem B2148781 : Blo 1909435 2148781 := bbase (se 3 (by rfl) ⟨402896, by rfl⟩ : syracuseStep 2148781 = 805793) (by norm_num)
theorem B2865041 : Blo 1909435 2865041 := bstep (se 2 (by rfl) ⟨1074390, by rfl⟩ : syracuseStep 2865041 = 2148781) B2148781
theorem B1910027 : Blo 1909435 1910027 := bstep (se 1 (by rfl) ⟨1432520, by rfl⟩ : syracuseStep 1910027 = 2865041) B2865041
theorem B6446357 : Blo 1909435 6446357 := bbase (se 6 (by rfl) ⟨151086, by rfl⟩ : syracuseStep 6446357 = 302173) (by norm_num)
theorem B4297571 : Blo 1909435 4297571 := bstep (se 1 (by rfl) ⟨3223178, by rfl⟩ : syracuseStep 4297571 = 6446357) B6446357
theorem B2865047 : Blo 1909435 2865047 := bstep (se 1 (by rfl) ⟨2148785, by rfl⟩ : syracuseStep 2865047 = 4297571) B4297571
theorem B1910031 : Blo 1909435 1910031 := bstep (se 1 (by rfl) ⟨1432523, by rfl⟩ : syracuseStep 1910031 = 2865047) B2865047
theorem B2865053 : Blo 1909435 2865053 := bbase (se 3 (by rfl) ⟨537197, by rfl⟩ : syracuseStep 2865053 = 1074395) (by norm_num)
theorem B1910035 : Blo 1909435 1910035 := bstep (se 1 (by rfl) ⟨1432526, by rfl⟩ : syracuseStep 1910035 = 2865053) B2865053
theorem B4297589 : Blo 1909435 4297589 := bbase (se 5 (by rfl) ⟨201449, by rfl⟩ : syracuseStep 4297589 = 402899) (by norm_num)
theorem B2865059 : Blo 1909435 2865059 := bstep (se 1 (by rfl) ⟨2148794, by rfl⟩ : syracuseStep 2865059 = 4297589) B4297589
theorem B1910039 : Blo 1909435 1910039 := bstep (se 1 (by rfl) ⟨1432529, by rfl⟩ : syracuseStep 1910039 = 2865059) B2865059
theorem B4191437 : Blo 1909435 4191437 := bbase (se 3 (by rfl) ⟨785894, by rfl⟩ : syracuseStep 4191437 = 1571789) (by norm_num)
theorem B11177165 : Blo 1909435 11177165 := bstep (se 3 (by rfl) ⟨2095718, by rfl⟩ : syracuseStep 11177165 = 4191437) B4191437
theorem B7451443 : Blo 1909435 7451443 := bstep (se 1 (by rfl) ⟨5588582, by rfl⟩ : syracuseStep 7451443 = 11177165) B11177165
theorem B9935257 : Blo 1909435 9935257 := bstep (se 2 (by rfl) ⟨3725721, by rfl⟩ : syracuseStep 9935257 = 7451443) B7451443
theorem B13247009 : Blo 1909435 13247009 := bstep (se 2 (by rfl) ⟨4967628, by rfl⟩ : syracuseStep 13247009 = 9935257) B9935257
theorem B8831339 : Blo 1909435 8831339 := bstep (se 1 (by rfl) ⟨6623504, by rfl⟩ : syracuseStep 8831339 = 13247009) B13247009
theorem B5887559 : Blo 1909435 5887559 := bstep (se 1 (by rfl) ⟨4415669, by rfl⟩ : syracuseStep 5887559 = 8831339) B8831339
theorem B3925039 : Blo 1909435 3925039 := bstep (se 1 (by rfl) ⟨2943779, by rfl⟩ : syracuseStep 3925039 = 5887559) B5887559
theorem B5233385 : Blo 1909435 5233385 := bstep (se 2 (by rfl) ⟨1962519, by rfl⟩ : syracuseStep 5233385 = 3925039) B3925039
theorem B3488923 : Blo 1909435 3488923 := bstep (se 1 (by rfl) ⟨2616692, by rfl⟩ : syracuseStep 3488923 = 5233385) B5233385
theorem B4651897 : Blo 1909435 4651897 := bstep (se 2 (by rfl) ⟨1744461, by rfl⟩ : syracuseStep 4651897 = 3488923) B3488923
theorem B6202529 : Blo 1909435 6202529 := bstep (se 2 (by rfl) ⟨2325948, by rfl⟩ : syracuseStep 6202529 = 4651897) B4651897
theorem B4135019 : Blo 1909435 4135019 := bstep (se 1 (by rfl) ⟨3101264, by rfl⟩ : syracuseStep 4135019 = 6202529) B6202529
theorem B44106869 : Blo 1909435 44106869 := bstep (se 5 (by rfl) ⟨2067509, by rfl⟩ : syracuseStep 44106869 = 4135019) B4135019
theorem B29404579 : Blo 1909435 29404579 := bstep (se 1 (by rfl) ⟨22053434, by rfl⟩ : syracuseStep 29404579 = 44106869) B44106869
theorem B39206105 : Blo 1909435 39206105 := bstep (se 2 (by rfl) ⟨14702289, by rfl⟩ : syracuseStep 39206105 = 29404579) B29404579
theorem B26137403 : Blo 1909435 26137403 := bstep (se 1 (by rfl) ⟨19603052, by rfl⟩ : syracuseStep 26137403 = 39206105) B39206105
theorem B17424935 : Blo 1909435 17424935 := bstep (se 1 (by rfl) ⟨13068701, by rfl⟩ : syracuseStep 17424935 = 26137403) B26137403
theorem B11616623 : Blo 1909435 11616623 := bstep (se 1 (by rfl) ⟨8712467, by rfl⟩ : syracuseStep 11616623 = 17424935) B17424935
theorem B7744415 : Blo 1909435 7744415 := bstep (se 1 (by rfl) ⟨5808311, by rfl⟩ : syracuseStep 7744415 = 11616623) B11616623
theorem B20651773 : Blo 1909435 20651773 := bstep (se 3 (by rfl) ⟨3872207, by rfl⟩ : syracuseStep 20651773 = 7744415) B7744415
theorem B27535697 : Blo 1909435 27535697 := bstep (se 2 (by rfl) ⟨10325886, by rfl⟩ : syracuseStep 27535697 = 20651773) B20651773
theorem B18357131 : Blo 1909435 18357131 := bstep (se 1 (by rfl) ⟨13767848, by rfl⟩ : syracuseStep 18357131 = 27535697) B27535697
theorem B12238087 : Blo 1909435 12238087 := bstep (se 1 (by rfl) ⟨9178565, by rfl⟩ : syracuseStep 12238087 = 18357131) B18357131
theorem B16317449 : Blo 1909435 16317449 := bstep (se 2 (by rfl) ⟨6119043, by rfl⟩ : syracuseStep 16317449 = 12238087) B12238087
theorem B10878299 : Blo 1909435 10878299 := bstep (se 1 (by rfl) ⟨8158724, by rfl⟩ : syracuseStep 10878299 = 16317449) B16317449
theorem B7252199 : Blo 1909435 7252199 := bstep (se 1 (by rfl) ⟨5439149, by rfl⟩ : syracuseStep 7252199 = 10878299) B10878299
theorem B4834799 : Blo 1909435 4834799 := bstep (se 1 (by rfl) ⟨3626099, by rfl⟩ : syracuseStep 4834799 = 7252199) B7252199
theorem B3223199 : Blo 1909435 3223199 := bstep (se 1 (by rfl) ⟨2417399, by rfl⟩ : syracuseStep 3223199 = 4834799) B4834799
theorem B2148799 : Blo 1909435 2148799 := bstep (se 1 (by rfl) ⟨1611599, by rfl⟩ : syracuseStep 2148799 = 3223199) B3223199
theorem B2865065 : Blo 1909435 2865065 := bstep (se 2 (by rfl) ⟨1074399, by rfl⟩ : syracuseStep 2865065 = 2148799) B2148799
theorem B1910043 : Blo 1909435 1910043 := bstep (se 1 (by rfl) ⟨1432532, by rfl⟩ : syracuseStep 1910043 = 2865065) B2865065
theorem B7252213 : Blo 1909435 7252213 := bbase (se 5 (by rfl) ⟨339947, by rfl⟩ : syracuseStep 7252213 = 679895) (by norm_num)
theorem B9669617 : Blo 1909435 9669617 := bstep (se 2 (by rfl) ⟨3626106, by rfl⟩ : syracuseStep 9669617 = 7252213) B7252213
theorem B6446411 : Blo 1909435 6446411 := bstep (se 1 (by rfl) ⟨4834808, by rfl⟩ : syracuseStep 6446411 = 9669617) B9669617
theorem B4297607 : Blo 1909435 4297607 := bstep (se 1 (by rfl) ⟨3223205, by rfl⟩ : syracuseStep 4297607 = 6446411) B6446411
theorem B2865071 : Blo 1909435 2865071 := bstep (se 1 (by rfl) ⟨2148803, by rfl⟩ : syracuseStep 2865071 = 4297607) B4297607
theorem B1910047 : Blo 1909435 1910047 := bstep (se 1 (by rfl) ⟨1432535, by rfl⟩ : syracuseStep 1910047 = 2865071) B2865071
theorem B2865077 : Blo 1909435 2865077 := bbase (se 5 (by rfl) ⟨134300, by rfl⟩ : syracuseStep 2865077 = 268601) (by norm_num)
theorem B1910051 : Blo 1909435 1910051 := bstep (se 1 (by rfl) ⟨1432538, by rfl⟩ : syracuseStep 1910051 = 2865077) B2865077
theorem B4834829 : Blo 1909435 4834829 := bbase (se 3 (by rfl) ⟨906530, by rfl⟩ : syracuseStep 4834829 = 1813061) (by norm_num)
theorem B3223219 : Blo 1909435 3223219 := bstep (se 1 (by rfl) ⟨2417414, by rfl⟩ : syracuseStep 3223219 = 4834829) B4834829
theorem B4297625 : Blo 1909435 4297625 := bstep (se 2 (by rfl) ⟨1611609, by rfl⟩ : syracuseStep 4297625 = 3223219) B3223219
theorem B2865083 : Blo 1909435 2865083 := bstep (se 1 (by rfl) ⟨2148812, by rfl⟩ : syracuseStep 2865083 = 4297625) B4297625
theorem B1910055 : Blo 1909435 1910055 := bstep (se 1 (by rfl) ⟨1432541, by rfl⟩ : syracuseStep 1910055 = 2865083) B2865083
theorem B2148817 : Blo 1909435 2148817 := bbase (se 2 (by rfl) ⟨805806, by rfl⟩ : syracuseStep 2148817 = 1611613) (by norm_num)
theorem B2865089 : Blo 1909435 2865089 := bstep (se 2 (by rfl) ⟨1074408, by rfl⟩ : syracuseStep 2865089 = 2148817) B2148817
theorem B1910059 : Blo 1909435 1910059 := bstep (se 1 (by rfl) ⟨1432544, by rfl⟩ : syracuseStep 1910059 = 2865089) B2865089
theorem B4079405 : Blo 1909435 4079405 := bbase (se 3 (by rfl) ⟨764888, by rfl⟩ : syracuseStep 4079405 = 1529777) (by norm_num)
theorem B2719603 : Blo 1909435 2719603 := bstep (se 1 (by rfl) ⟨2039702, by rfl⟩ : syracuseStep 2719603 = 4079405) B4079405
theorem B3626137 : Blo 1909435 3626137 := bstep (se 2 (by rfl) ⟨1359801, by rfl⟩ : syracuseStep 3626137 = 2719603) B2719603
theorem B4834849 : Blo 1909435 4834849 := bstep (se 2 (by rfl) ⟨1813068, by rfl⟩ : syracuseStep 4834849 = 3626137) B3626137
theorem B6446465 : Blo 1909435 6446465 := bstep (se 2 (by rfl) ⟨2417424, by rfl⟩ : syracuseStep 6446465 = 4834849) B4834849
theorem B4297643 : Blo 1909435 4297643 := bstep (se 1 (by rfl) ⟨3223232, by rfl⟩ : syracuseStep 4297643 = 6446465) B6446465
theorem B2865095 : Blo 1909435 2865095 := bstep (se 1 (by rfl) ⟨2148821, by rfl⟩ : syracuseStep 2865095 = 4297643) B4297643
theorem B1910063 : Blo 1909435 1910063 := bstep (se 1 (by rfl) ⟨1432547, by rfl⟩ : syracuseStep 1910063 = 2865095) B2865095
theorem B2865101 : Blo 1909435 2865101 := bbase (se 3 (by rfl) ⟨537206, by rfl⟩ : syracuseStep 2865101 = 1074413) (by norm_num)
theorem B1910067 : Blo 1909435 1910067 := bstep (se 1 (by rfl) ⟨1432550, by rfl⟩ : syracuseStep 1910067 = 2865101) B2865101
theorem B4297661 : Blo 1909435 4297661 := bbase (se 3 (by rfl) ⟨805811, by rfl⟩ : syracuseStep 4297661 = 1611623) (by norm_num)
theorem B2865107 : Blo 1909435 2865107 := bstep (se 1 (by rfl) ⟨2148830, by rfl⟩ : syracuseStep 2865107 = 4297661) B4297661
theorem B1910071 : Blo 1909435 1910071 := bstep (se 1 (by rfl) ⟨1432553, by rfl⟩ : syracuseStep 1910071 = 2865107) B2865107
theorem B3223253 : Blo 1909435 3223253 := bbase (se 7 (by rfl) ⟨37772, by rfl⟩ : syracuseStep 3223253 = 75545) (by norm_num)
theorem B2148835 : Blo 1909435 2148835 := bstep (se 1 (by rfl) ⟨1611626, by rfl⟩ : syracuseStep 2148835 = 3223253) B3223253
theorem B2865113 : Blo 1909435 2865113 := bstep (se 2 (by rfl) ⟨1074417, by rfl⟩ : syracuseStep 2865113 = 2148835) B2148835
theorem B1910075 : Blo 1909435 1910075 := bstep (se 1 (by rfl) ⟨1432556, by rfl⟩ : syracuseStep 1910075 = 2865113) B2865113
theorem B4356317 : Blo 1909435 4356317 := bbase (se 3 (by rfl) ⟨816809, by rfl⟩ : syracuseStep 4356317 = 1633619) (by norm_num)
theorem B2904211 : Blo 1909435 2904211 := bstep (se 1 (by rfl) ⟨2178158, by rfl⟩ : syracuseStep 2904211 = 4356317) B4356317
theorem B3872281 : Blo 1909435 3872281 := bstep (se 2 (by rfl) ⟨1452105, by rfl⟩ : syracuseStep 3872281 = 2904211) B2904211
theorem B5163041 : Blo 1909435 5163041 := bstep (se 2 (by rfl) ⟨1936140, by rfl⟩ : syracuseStep 5163041 = 3872281) B3872281
theorem B3442027 : Blo 1909435 3442027 := bstep (se 1 (by rfl) ⟨2581520, by rfl⟩ : syracuseStep 3442027 = 5163041) B5163041
theorem B4589369 : Blo 1909435 4589369 := bstep (se 2 (by rfl) ⟨1721013, by rfl⟩ : syracuseStep 4589369 = 3442027) B3442027
theorem B3059579 : Blo 1909435 3059579 := bstep (se 1 (by rfl) ⟨2294684, by rfl⟩ : syracuseStep 3059579 = 4589369) B4589369
theorem B8158877 : Blo 1909435 8158877 := bstep (se 3 (by rfl) ⟨1529789, by rfl⟩ : syracuseStep 8158877 = 3059579) B3059579
theorem B5439251 : Blo 1909435 5439251 := bstep (se 1 (by rfl) ⟨4079438, by rfl⟩ : syracuseStep 5439251 = 8158877) B8158877
theorem B14504669 : Blo 1909435 14504669 := bstep (se 3 (by rfl) ⟨2719625, by rfl⟩ : syracuseStep 14504669 = 5439251) B5439251
theorem B9669779 : Blo 1909435 9669779 := bstep (se 1 (by rfl) ⟨7252334, by rfl⟩ : syracuseStep 9669779 = 14504669) B14504669
theorem B6446519 : Blo 1909435 6446519 := bstep (se 1 (by rfl) ⟨4834889, by rfl⟩ : syracuseStep 6446519 = 9669779) B9669779
theorem B4297679 : Blo 1909435 4297679 := bstep (se 1 (by rfl) ⟨3223259, by rfl⟩ : syracuseStep 4297679 = 6446519) B6446519
theorem B2865119 : Blo 1909435 2865119 := bstep (se 1 (by rfl) ⟨2148839, by rfl⟩ : syracuseStep 2865119 = 4297679) B4297679
theorem B1910079 : Blo 1909435 1910079 := bstep (se 1 (by rfl) ⟨1432559, by rfl⟩ : syracuseStep 1910079 = 2865119) B2865119
theorem B2865125 : Blo 1909435 2865125 := bbase (se 4 (by rfl) ⟨268605, by rfl⟩ : syracuseStep 2865125 = 537211) (by norm_num)
theorem B1910083 : Blo 1909435 1910083 := bstep (se 1 (by rfl) ⟨1432562, by rfl⟩ : syracuseStep 1910083 = 2865125) B2865125
theorem B4589389 : Blo 1909435 4589389 := bbase (se 3 (by rfl) ⟨860510, by rfl⟩ : syracuseStep 4589389 = 1721021) (by norm_num)
theorem B6119185 : Blo 1909435 6119185 := bstep (se 2 (by rfl) ⟨2294694, by rfl⟩ : syracuseStep 6119185 = 4589389) B4589389
theorem B8158913 : Blo 1909435 8158913 := bstep (se 2 (by rfl) ⟨3059592, by rfl⟩ : syracuseStep 8158913 = 6119185) B6119185
theorem B5439275 : Blo 1909435 5439275 := bstep (se 1 (by rfl) ⟨4079456, by rfl⟩ : syracuseStep 5439275 = 8158913) B8158913
theorem B3626183 : Blo 1909435 3626183 := bstep (se 1 (by rfl) ⟨2719637, by rfl⟩ : syracuseStep 3626183 = 5439275) B5439275
theorem B2417455 : Blo 1909435 2417455 := bstep (se 1 (by rfl) ⟨1813091, by rfl⟩ : syracuseStep 2417455 = 3626183) B3626183
theorem B3223273 : Blo 1909435 3223273 := bstep (se 2 (by rfl) ⟨1208727, by rfl⟩ : syracuseStep 3223273 = 2417455) B2417455
theorem B4297697 : Blo 1909435 4297697 := bstep (se 2 (by rfl) ⟨1611636, by rfl⟩ : syracuseStep 4297697 = 3223273) B3223273
theorem B2865131 : Blo 1909435 2865131 := bstep (se 1 (by rfl) ⟨2148848, by rfl⟩ : syracuseStep 2865131 = 4297697) B4297697
theorem B1910087 : Blo 1909435 1910087 := bstep (se 1 (by rfl) ⟨1432565, by rfl⟩ : syracuseStep 1910087 = 2865131) B2865131
theorem B2148853 : Blo 1909435 2148853 := bbase (se 5 (by rfl) ⟨100727, by rfl⟩ : syracuseStep 2148853 = 201455) (by norm_num)
theorem B2865137 : Blo 1909435 2865137 := bstep (se 2 (by rfl) ⟨1074426, by rfl⟩ : syracuseStep 2865137 = 2148853) B2148853
theorem B1910091 : Blo 1909435 1910091 := bstep (se 1 (by rfl) ⟨1432568, by rfl⟩ : syracuseStep 1910091 = 2865137) B2865137
theorem B2417465 : Blo 1909435 2417465 := bbase (se 2 (by rfl) ⟨906549, by rfl⟩ : syracuseStep 2417465 = 1813099) (by norm_num)
theorem B6446573 : Blo 1909435 6446573 := bstep (se 3 (by rfl) ⟨1208732, by rfl⟩ : syracuseStep 6446573 = 2417465) B2417465
theorem B4297715 : Blo 1909435 4297715 := bstep (se 1 (by rfl) ⟨3223286, by rfl⟩ : syracuseStep 4297715 = 6446573) B6446573
theorem B2865143 : Blo 1909435 2865143 := bstep (se 1 (by rfl) ⟨2148857, by rfl⟩ : syracuseStep 2865143 = 4297715) B4297715
theorem B1910095 : Blo 1909435 1910095 := bstep (se 1 (by rfl) ⟨1432571, by rfl⟩ : syracuseStep 1910095 = 2865143) B2865143
theorem B2865149 : Blo 1909435 2865149 := bbase (se 3 (by rfl) ⟨537215, by rfl⟩ : syracuseStep 2865149 = 1074431) (by norm_num)
theorem B1910099 : Blo 1909435 1910099 := bstep (se 1 (by rfl) ⟨1432574, by rfl⟩ : syracuseStep 1910099 = 2865149) B2865149
theorem B4297733 : Blo 1909435 4297733 := bbase (se 4 (by rfl) ⟨402912, by rfl⟩ : syracuseStep 4297733 = 805825) (by norm_num)
theorem B2865155 : Blo 1909435 2865155 := bstep (se 1 (by rfl) ⟨2148866, by rfl⟩ : syracuseStep 2865155 = 4297733) B4297733
theorem B1910103 : Blo 1909435 1910103 := bstep (se 1 (by rfl) ⟨1432577, by rfl⟩ : syracuseStep 1910103 = 2865155) B2865155
theorem B3626221 : Blo 1909435 3626221 := bbase (se 3 (by rfl) ⟨679916, by rfl⟩ : syracuseStep 3626221 = 1359833) (by norm_num)
theorem B4834961 : Blo 1909435 4834961 := bstep (se 2 (by rfl) ⟨1813110, by rfl⟩ : syracuseStep 4834961 = 3626221) B3626221
theorem B3223307 : Blo 1909435 3223307 := bstep (se 1 (by rfl) ⟨2417480, by rfl⟩ : syracuseStep 3223307 = 4834961) B4834961
theorem B2148871 : Blo 1909435 2148871 := bstep (se 1 (by rfl) ⟨1611653, by rfl⟩ : syracuseStep 2148871 = 3223307) B3223307
theorem B2865161 : Blo 1909435 2865161 := bstep (se 2 (by rfl) ⟨1074435, by rfl⟩ : syracuseStep 2865161 = 2148871) B2148871
theorem B1910107 : Blo 1909435 1910107 := bstep (se 1 (by rfl) ⟨1432580, by rfl⟩ : syracuseStep 1910107 = 2865161) B2865161
theorem B9669941 : Blo 1909435 9669941 := bbase (se 5 (by rfl) ⟨453278, by rfl⟩ : syracuseStep 9669941 = 906557) (by norm_num)
theorem B6446627 : Blo 1909435 6446627 := bstep (se 1 (by rfl) ⟨4834970, by rfl⟩ : syracuseStep 6446627 = 9669941) B9669941
theorem B4297751 : Blo 1909435 4297751 := bstep (se 1 (by rfl) ⟨3223313, by rfl⟩ : syracuseStep 4297751 = 6446627) B6446627
theorem B2865167 : Blo 1909435 2865167 := bstep (se 1 (by rfl) ⟨2148875, by rfl⟩ : syracuseStep 2865167 = 4297751) B4297751
theorem B1910111 : Blo 1909435 1910111 := bstep (se 1 (by rfl) ⟨1432583, by rfl⟩ : syracuseStep 1910111 = 2865167) B2865167
theorem B2865173 : Blo 1909435 2865173 := bbase (se 6 (by rfl) ⟨67152, by rfl⟩ : syracuseStep 2865173 = 134305) (by norm_num)
theorem B1910115 : Blo 1909435 1910115 := bstep (se 1 (by rfl) ⟨1432586, by rfl⟩ : syracuseStep 1910115 = 2865173) B2865173
theorem B1936181 : Blo 1909435 1936181 := bbase (se 5 (by rfl) ⟨90758, by rfl⟩ : syracuseStep 1936181 = 181517) (by norm_num)
theorem B5163149 : Blo 1909435 5163149 := bstep (se 3 (by rfl) ⟨968090, by rfl⟩ : syracuseStep 5163149 = 1936181) B1936181
theorem B3442099 : Blo 1909435 3442099 := bstep (se 1 (by rfl) ⟨2581574, by rfl⟩ : syracuseStep 3442099 = 5163149) B5163149
theorem B4589465 : Blo 1909435 4589465 := bstep (se 2 (by rfl) ⟨1721049, by rfl⟩ : syracuseStep 4589465 = 3442099) B3442099
theorem B12238573 : Blo 1909435 12238573 := bstep (se 3 (by rfl) ⟨2294732, by rfl⟩ : syracuseStep 12238573 = 4589465) B4589465
theorem B16318097 : Blo 1909435 16318097 := bstep (se 2 (by rfl) ⟨6119286, by rfl⟩ : syracuseStep 16318097 = 12238573) B12238573
theorem B10878731 : Blo 1909435 10878731 := bstep (se 1 (by rfl) ⟨8159048, by rfl⟩ : syracuseStep 10878731 = 16318097) B16318097
theorem B7252487 : Blo 1909435 7252487 := bstep (se 1 (by rfl) ⟨5439365, by rfl⟩ : syracuseStep 7252487 = 10878731) B10878731
theorem B4834991 : Blo 1909435 4834991 := bstep (se 1 (by rfl) ⟨3626243, by rfl⟩ : syracuseStep 4834991 = 7252487) B7252487
theorem B3223327 : Blo 1909435 3223327 := bstep (se 1 (by rfl) ⟨2417495, by rfl⟩ : syracuseStep 3223327 = 4834991) B4834991
theorem B4297769 : Blo 1909435 4297769 := bstep (se 2 (by rfl) ⟨1611663, by rfl⟩ : syracuseStep 4297769 = 3223327) B3223327
theorem B2865179 : Blo 1909435 2865179 := bstep (se 1 (by rfl) ⟨2148884, by rfl⟩ : syracuseStep 2865179 = 4297769) B4297769
theorem B1910119 : Blo 1909435 1910119 := bstep (se 1 (by rfl) ⟨1432589, by rfl⟩ : syracuseStep 1910119 = 2865179) B2865179
theorem B2148889 : Blo 1909435 2148889 := bbase (se 2 (by rfl) ⟨805833, by rfl⟩ : syracuseStep 2148889 = 1611667) (by norm_num)
theorem B2865185 : Blo 1909435 2865185 := bstep (se 2 (by rfl) ⟨1074444, by rfl⟩ : syracuseStep 2865185 = 2148889) B2148889
theorem B1910123 : Blo 1909435 1910123 := bstep (se 1 (by rfl) ⟨1432592, by rfl⟩ : syracuseStep 1910123 = 2865185) B2865185
theorem B7252517 : Blo 1909435 7252517 := bbase (se 4 (by rfl) ⟨679923, by rfl⟩ : syracuseStep 7252517 = 1359847) (by norm_num)
theorem B4835011 : Blo 1909435 4835011 := bstep (se 1 (by rfl) ⟨3626258, by rfl⟩ : syracuseStep 4835011 = 7252517) B7252517
theorem B6446681 : Blo 1909435 6446681 := bstep (se 2 (by rfl) ⟨2417505, by rfl⟩ : syracuseStep 6446681 = 4835011) B4835011
theorem B4297787 : Blo 1909435 4297787 := bstep (se 1 (by rfl) ⟨3223340, by rfl⟩ : syracuseStep 4297787 = 6446681) B6446681
theorem B2865191 : Blo 1909435 2865191 := bstep (se 1 (by rfl) ⟨2148893, by rfl⟩ : syracuseStep 2865191 = 4297787) B4297787
theorem B1910127 : Blo 1909435 1910127 := bstep (se 1 (by rfl) ⟨1432595, by rfl⟩ : syracuseStep 1910127 = 2865191) B2865191
theorem B2865197 : Blo 1909435 2865197 := bbase (se 3 (by rfl) ⟨537224, by rfl⟩ : syracuseStep 2865197 = 1074449) (by norm_num)
theorem B1910131 : Blo 1909435 1910131 := bstep (se 1 (by rfl) ⟨1432598, by rfl⟩ : syracuseStep 1910131 = 2865197) B2865197
theorem B4297805 : Blo 1909435 4297805 := bbase (se 3 (by rfl) ⟨805838, by rfl⟩ : syracuseStep 4297805 = 1611677) (by norm_num)
theorem B2865203 : Blo 1909435 2865203 := bstep (se 1 (by rfl) ⟨2148902, by rfl⟩ : syracuseStep 2865203 = 4297805) B4297805
theorem B1910135 : Blo 1909435 1910135 := bstep (se 1 (by rfl) ⟨1432601, by rfl⟩ : syracuseStep 1910135 = 2865203) B2865203
theorem B2417521 : Blo 1909435 2417521 := bbase (se 2 (by rfl) ⟨906570, by rfl⟩ : syracuseStep 2417521 = 1813141) (by norm_num)
theorem B3223361 : Blo 1909435 3223361 := bstep (se 2 (by rfl) ⟨1208760, by rfl⟩ : syracuseStep 3223361 = 2417521) B2417521
theorem B2148907 : Blo 1909435 2148907 := bstep (se 1 (by rfl) ⟨1611680, by rfl⟩ : syracuseStep 2148907 = 3223361) B3223361
theorem B2865209 : Blo 1909435 2865209 := bstep (se 2 (by rfl) ⟨1074453, by rfl⟩ : syracuseStep 2865209 = 2148907) B2148907
theorem B1910139 : Blo 1909435 1910139 := bstep (se 1 (by rfl) ⟨1432604, by rfl⟩ : syracuseStep 1910139 = 2865209) B2865209
theorem B9179045 : Blo 1909435 9179045 := bbase (se 4 (by rfl) ⟨860535, by rfl⟩ : syracuseStep 9179045 = 1721071) (by norm_num)
theorem B6119363 : Blo 1909435 6119363 := bstep (se 1 (by rfl) ⟨4589522, by rfl⟩ : syracuseStep 6119363 = 9179045) B9179045
theorem B4079575 : Blo 1909435 4079575 := bstep (se 1 (by rfl) ⟨3059681, by rfl⟩ : syracuseStep 4079575 = 6119363) B6119363
theorem B21757733 : Blo 1909435 21757733 := bstep (se 4 (by rfl) ⟨2039787, by rfl⟩ : syracuseStep 21757733 = 4079575) B4079575
theorem B14505155 : Blo 1909435 14505155 := bstep (se 1 (by rfl) ⟨10878866, by rfl⟩ : syracuseStep 14505155 = 21757733) B21757733
theorem B9670103 : Blo 1909435 9670103 := bstep (se 1 (by rfl) ⟨7252577, by rfl⟩ : syracuseStep 9670103 = 14505155) B14505155
theorem B6446735 : Blo 1909435 6446735 := bstep (se 1 (by rfl) ⟨4835051, by rfl⟩ : syracuseStep 6446735 = 9670103) B9670103
theorem B4297823 : Blo 1909435 4297823 := bstep (se 1 (by rfl) ⟨3223367, by rfl⟩ : syracuseStep 4297823 = 6446735) B6446735
theorem B2865215 : Blo 1909435 2865215 := bstep (se 1 (by rfl) ⟨2148911, by rfl⟩ : syracuseStep 2865215 = 4297823) B4297823
theorem B1910143 : Blo 1909435 1910143 := bstep (se 1 (by rfl) ⟨1432607, by rfl⟩ : syracuseStep 1910143 = 2865215) B2865215
theorem B2865221 : Blo 1909435 2865221 := bbase (se 4 (by rfl) ⟨268614, by rfl⟩ : syracuseStep 2865221 = 537229) (by norm_num)
theorem B1910147 : Blo 1909435 1910147 := bstep (se 1 (by rfl) ⟨1432610, by rfl⟩ : syracuseStep 1910147 = 2865221) B2865221
theorem B3223381 : Blo 1909435 3223381 := bbase (se 9 (by rfl) ⟨9443, by rfl⟩ : syracuseStep 3223381 = 18887) (by norm_num)
theorem B4297841 : Blo 1909435 4297841 := bstep (se 2 (by rfl) ⟨1611690, by rfl⟩ : syracuseStep 4297841 = 3223381) B3223381
theorem B2865227 : Blo 1909435 2865227 := bstep (se 1 (by rfl) ⟨2148920, by rfl⟩ : syracuseStep 2865227 = 4297841) B4297841
theorem B1910151 : Blo 1909435 1910151 := bstep (se 1 (by rfl) ⟨1432613, by rfl⟩ : syracuseStep 1910151 = 2865227) B2865227
theorem B2148925 : Blo 1909435 2148925 := bbase (se 3 (by rfl) ⟨402923, by rfl⟩ : syracuseStep 2148925 = 805847) (by norm_num)
theorem B2865233 : Blo 1909435 2865233 := bstep (se 2 (by rfl) ⟨1074462, by rfl⟩ : syracuseStep 2865233 = 2148925) B2148925
theorem B1910155 : Blo 1909435 1910155 := bstep (se 1 (by rfl) ⟨1432616, by rfl⟩ : syracuseStep 1910155 = 2865233) B2865233
theorem B6446789 : Blo 1909435 6446789 := bbase (se 4 (by rfl) ⟨604386, by rfl⟩ : syracuseStep 6446789 = 1208773) (by norm_num)
theorem B4297859 : Blo 1909435 4297859 := bstep (se 1 (by rfl) ⟨3223394, by rfl⟩ : syracuseStep 4297859 = 6446789) B6446789
theorem B2865239 : Blo 1909435 2865239 := bstep (se 1 (by rfl) ⟨2148929, by rfl⟩ : syracuseStep 2865239 = 4297859) B4297859
theorem B1910159 : Blo 1909435 1910159 := bstep (se 1 (by rfl) ⟨1432619, by rfl⟩ : syracuseStep 1910159 = 2865239) B2865239
theorem B2865245 : Blo 1909435 2865245 := bbase (se 3 (by rfl) ⟨537233, by rfl⟩ : syracuseStep 2865245 = 1074467) (by norm_num)
theorem B1910163 : Blo 1909435 1910163 := bstep (se 1 (by rfl) ⟨1432622, by rfl⟩ : syracuseStep 1910163 = 2865245) B2865245
theorem B4297877 : Blo 1909435 4297877 := bbase (se 6 (by rfl) ⟨100731, by rfl⟩ : syracuseStep 4297877 = 201463) (by norm_num)
theorem B2865251 : Blo 1909435 2865251 := bstep (se 1 (by rfl) ⟨2148938, by rfl⟩ : syracuseStep 2865251 = 4297877) B4297877
theorem B1910167 : Blo 1909435 1910167 := bstep (se 1 (by rfl) ⟨1432625, by rfl⟩ : syracuseStep 1910167 = 2865251) B2865251
theorem B2719757 : Blo 1909435 2719757 := bbase (se 3 (by rfl) ⟨509954, by rfl⟩ : syracuseStep 2719757 = 1019909) (by norm_num)
theorem B7252685 : Blo 1909435 7252685 := bstep (se 3 (by rfl) ⟨1359878, by rfl⟩ : syracuseStep 7252685 = 2719757) B2719757
theorem B4835123 : Blo 1909435 4835123 := bstep (se 1 (by rfl) ⟨3626342, by rfl⟩ : syracuseStep 4835123 = 7252685) B7252685
theorem B3223415 : Blo 1909435 3223415 := bstep (se 1 (by rfl) ⟨2417561, by rfl⟩ : syracuseStep 3223415 = 4835123) B4835123
theorem B2148943 : Blo 1909435 2148943 := bstep (se 1 (by rfl) ⟨1611707, by rfl⟩ : syracuseStep 2148943 = 3223415) B3223415
theorem B2865257 : Blo 1909435 2865257 := bstep (se 2 (by rfl) ⟨1074471, by rfl⟩ : syracuseStep 2865257 = 2148943) B2148943
theorem B1910171 : Blo 1909435 1910171 := bstep (se 1 (by rfl) ⟨1432628, by rfl⟩ : syracuseStep 1910171 = 2865257) B2865257
theorem B19604405 : Blo 1909435 19604405 := bbase (se 5 (by rfl) ⟨918956, by rfl⟩ : syracuseStep 19604405 = 1837913) (by norm_num)
theorem B13069603 : Blo 1909435 13069603 := bstep (se 1 (by rfl) ⟨9802202, by rfl⟩ : syracuseStep 13069603 = 19604405) B19604405
theorem B17426137 : Blo 1909435 17426137 := bstep (se 2 (by rfl) ⟨6534801, by rfl⟩ : syracuseStep 17426137 = 13069603) B13069603
theorem B23234849 : Blo 1909435 23234849 := bstep (se 2 (by rfl) ⟨8713068, by rfl⟩ : syracuseStep 23234849 = 17426137) B17426137
theorem B15489899 : Blo 1909435 15489899 := bstep (se 1 (by rfl) ⟨11617424, by rfl⟩ : syracuseStep 15489899 = 23234849) B23234849
theorem B10326599 : Blo 1909435 10326599 := bstep (se 1 (by rfl) ⟨7744949, by rfl⟩ : syracuseStep 10326599 = 15489899) B15489899
theorem B6884399 : Blo 1909435 6884399 := bstep (se 1 (by rfl) ⟨5163299, by rfl⟩ : syracuseStep 6884399 = 10326599) B10326599
theorem B18358397 : Blo 1909435 18358397 := bstep (se 3 (by rfl) ⟨3442199, by rfl⟩ : syracuseStep 18358397 = 6884399) B6884399
theorem B12238931 : Blo 1909435 12238931 := bstep (se 1 (by rfl) ⟨9179198, by rfl⟩ : syracuseStep 12238931 = 18358397) B18358397
theorem B8159287 : Blo 1909435 8159287 := bstep (se 1 (by rfl) ⟨6119465, by rfl⟩ : syracuseStep 8159287 = 12238931) B12238931
theorem B10879049 : Blo 1909435 10879049 := bstep (se 2 (by rfl) ⟨4079643, by rfl⟩ : syracuseStep 10879049 = 8159287) B8159287
theorem B7252699 : Blo 1909435 7252699 := bstep (se 1 (by rfl) ⟨5439524, by rfl⟩ : syracuseStep 7252699 = 10879049) B10879049
theorem B9670265 : Blo 1909435 9670265 := bstep (se 2 (by rfl) ⟨3626349, by rfl⟩ : syracuseStep 9670265 = 7252699) B7252699
theorem B6446843 : Blo 1909435 6446843 := bstep (se 1 (by rfl) ⟨4835132, by rfl⟩ : syracuseStep 6446843 = 9670265) B9670265
theorem B4297895 : Blo 1909435 4297895 := bstep (se 1 (by rfl) ⟨3223421, by rfl⟩ : syracuseStep 4297895 = 6446843) B6446843
theorem B2865263 : Blo 1909435 2865263 := bstep (se 1 (by rfl) ⟨2148947, by rfl⟩ : syracuseStep 2865263 = 4297895) B4297895
theorem B1910175 : Blo 1909435 1910175 := bstep (se 1 (by rfl) ⟨1432631, by rfl⟩ : syracuseStep 1910175 = 2865263) B2865263
theorem B2865269 : Blo 1909435 2865269 := bbase (se 5 (by rfl) ⟨134309, by rfl⟩ : syracuseStep 2865269 = 268619) (by norm_num)
theorem B1910179 : Blo 1909435 1910179 := bstep (se 1 (by rfl) ⟨1432634, by rfl⟩ : syracuseStep 1910179 = 2865269) B2865269
theorem B3626365 : Blo 1909435 3626365 := bbase (se 3 (by rfl) ⟨679943, by rfl⟩ : syracuseStep 3626365 = 1359887) (by norm_num)
theorem B4835153 : Blo 1909435 4835153 := bstep (se 2 (by rfl) ⟨1813182, by rfl⟩ : syracuseStep 4835153 = 3626365) B3626365
theorem B3223435 : Blo 1909435 3223435 := bstep (se 1 (by rfl) ⟨2417576, by rfl⟩ : syracuseStep 3223435 = 4835153) B4835153
theorem B4297913 : Blo 1909435 4297913 := bstep (se 2 (by rfl) ⟨1611717, by rfl⟩ : syracuseStep 4297913 = 3223435) B3223435
theorem B2865275 : Blo 1909435 2865275 := bstep (se 1 (by rfl) ⟨2148956, by rfl⟩ : syracuseStep 2865275 = 4297913) B4297913
theorem B1910183 : Blo 1909435 1910183 := bstep (se 1 (by rfl) ⟨1432637, by rfl⟩ : syracuseStep 1910183 = 2865275) B2865275
theorem B2148961 : Blo 1909435 2148961 := bbase (se 2 (by rfl) ⟨805860, by rfl⟩ : syracuseStep 2148961 = 1611721) (by norm_num)
theorem B2865281 : Blo 1909435 2865281 := bstep (se 2 (by rfl) ⟨1074480, by rfl⟩ : syracuseStep 2865281 = 2148961) B2148961
theorem B1910187 : Blo 1909435 1910187 := bstep (se 1 (by rfl) ⟨1432640, by rfl⟩ : syracuseStep 1910187 = 2865281) B2865281
theorem B4835173 : Blo 1909435 4835173 := bbase (se 4 (by rfl) ⟨453297, by rfl⟩ : syracuseStep 4835173 = 906595) (by norm_num)
theorem B6446897 : Blo 1909435 6446897 := bstep (se 2 (by rfl) ⟨2417586, by rfl⟩ : syracuseStep 6446897 = 4835173) B4835173
theorem B4297931 : Blo 1909435 4297931 := bstep (se 1 (by rfl) ⟨3223448, by rfl⟩ : syracuseStep 4297931 = 6446897) B6446897
theorem B2865287 : Blo 1909435 2865287 := bstep (se 1 (by rfl) ⟨2148965, by rfl⟩ : syracuseStep 2865287 = 4297931) B4297931
theorem B1910191 : Blo 1909435 1910191 := bstep (se 1 (by rfl) ⟨1432643, by rfl⟩ : syracuseStep 1910191 = 2865287) B2865287
theorem B2865293 : Blo 1909435 2865293 := bbase (se 3 (by rfl) ⟨537242, by rfl⟩ : syracuseStep 2865293 = 1074485) (by norm_num)
theorem B1910195 : Blo 1909435 1910195 := bstep (se 1 (by rfl) ⟨1432646, by rfl⟩ : syracuseStep 1910195 = 2865293) B2865293
theorem B4297949 : Blo 1909435 4297949 := bbase (se 3 (by rfl) ⟨805865, by rfl⟩ : syracuseStep 4297949 = 1611731) (by norm_num)
theorem B2865299 : Blo 1909435 2865299 := bstep (se 1 (by rfl) ⟨2148974, by rfl⟩ : syracuseStep 2865299 = 4297949) B4297949
theorem B1910199 : Blo 1909435 1910199 := bstep (se 1 (by rfl) ⟨1432649, by rfl⟩ : syracuseStep 1910199 = 2865299) B2865299
theorem B3223469 : Blo 1909435 3223469 := bbase (se 3 (by rfl) ⟨604400, by rfl⟩ : syracuseStep 3223469 = 1208801) (by norm_num)
theorem B2148979 : Blo 1909435 2148979 := bstep (se 1 (by rfl) ⟨1611734, by rfl⟩ : syracuseStep 2148979 = 3223469) B3223469
theorem B2865305 : Blo 1909435 2865305 := bstep (se 2 (by rfl) ⟨1074489, by rfl⟩ : syracuseStep 2865305 = 2148979) B2148979
theorem B1910203 : Blo 1909435 1910203 := bstep (se 1 (by rfl) ⟨1432652, by rfl⟩ : syracuseStep 1910203 = 2865305) B2865305
theorem B2124493 : Blo 1909435 2124493 := bbase (se 3 (by rfl) ⟨398342, by rfl⟩ : syracuseStep 2124493 = 796685) (by norm_num)
theorem B45322517 : Blo 1909435 45322517 := bstep (se 6 (by rfl) ⟨1062246, by rfl⟩ : syracuseStep 45322517 = 2124493) B2124493
theorem B120860045 : Blo 1909435 120860045 := bstep (se 3 (by rfl) ⟨22661258, by rfl⟩ : syracuseStep 120860045 = 45322517) B45322517
theorem B80573363 : Blo 1909435 80573363 := bstep (se 1 (by rfl) ⟨60430022, by rfl⟩ : syracuseStep 80573363 = 120860045) B120860045
theorem B53715575 : Blo 1909435 53715575 := bstep (se 1 (by rfl) ⟨40286681, by rfl⟩ : syracuseStep 53715575 = 80573363) B80573363
theorem B35810383 : Blo 1909435 35810383 := bstep (se 1 (by rfl) ⟨26857787, by rfl⟩ : syracuseStep 35810383 = 53715575) B53715575
theorem B47747177 : Blo 1909435 47747177 := bstep (se 2 (by rfl) ⟨17905191, by rfl⟩ : syracuseStep 47747177 = 35810383) B35810383
theorem B31831451 : Blo 1909435 31831451 := bstep (se 1 (by rfl) ⟨23873588, by rfl⟩ : syracuseStep 31831451 = 47747177) B47747177
theorem B21220967 : Blo 1909435 21220967 := bstep (se 1 (by rfl) ⟨15915725, by rfl⟩ : syracuseStep 21220967 = 31831451) B31831451
theorem B14147311 : Blo 1909435 14147311 := bstep (se 1 (by rfl) ⟨10610483, by rfl⟩ : syracuseStep 14147311 = 21220967) B21220967
theorem B18863081 : Blo 1909435 18863081 := bstep (se 2 (by rfl) ⟨7073655, by rfl⟩ : syracuseStep 18863081 = 14147311) B14147311
theorem B12575387 : Blo 1909435 12575387 := bstep (se 1 (by rfl) ⟨9431540, by rfl⟩ : syracuseStep 12575387 = 18863081) B18863081
theorem B8383591 : Blo 1909435 8383591 := bstep (se 1 (by rfl) ⟨6287693, by rfl⟩ : syracuseStep 8383591 = 12575387) B12575387
theorem B11178121 : Blo 1909435 11178121 := bstep (se 2 (by rfl) ⟨4191795, by rfl⟩ : syracuseStep 11178121 = 8383591) B8383591
theorem B14904161 : Blo 1909435 14904161 := bstep (se 2 (by rfl) ⟨5589060, by rfl⟩ : syracuseStep 14904161 = 11178121) B11178121
theorem B9936107 : Blo 1909435 9936107 := bstep (se 1 (by rfl) ⟨7452080, by rfl⟩ : syracuseStep 9936107 = 14904161) B14904161
theorem B6624071 : Blo 1909435 6624071 := bstep (se 1 (by rfl) ⟨4968053, by rfl⟩ : syracuseStep 6624071 = 9936107) B9936107
theorem B4416047 : Blo 1909435 4416047 := bstep (se 1 (by rfl) ⟨3312035, by rfl⟩ : syracuseStep 4416047 = 6624071) B6624071
theorem B2944031 : Blo 1909435 2944031 := bstep (se 1 (by rfl) ⟨2208023, by rfl⟩ : syracuseStep 2944031 = 4416047) B4416047
theorem B31402997 : Blo 1909435 31402997 := bstep (se 5 (by rfl) ⟨1472015, by rfl⟩ : syracuseStep 31402997 = 2944031) B2944031
theorem B20935331 : Blo 1909435 20935331 := bstep (se 1 (by rfl) ⟨15701498, by rfl⟩ : syracuseStep 20935331 = 31402997) B31402997
theorem B13956887 : Blo 1909435 13956887 := bstep (se 1 (by rfl) ⟨10467665, by rfl⟩ : syracuseStep 13956887 = 20935331) B20935331
theorem B37218365 : Blo 1909435 37218365 := bstep (se 3 (by rfl) ⟨6978443, by rfl⟩ : syracuseStep 37218365 = 13956887) B13956887
theorem B24812243 : Blo 1909435 24812243 := bstep (se 1 (by rfl) ⟨18609182, by rfl⟩ : syracuseStep 24812243 = 37218365) B37218365
theorem B16541495 : Blo 1909435 16541495 := bstep (se 1 (by rfl) ⟨12406121, by rfl⟩ : syracuseStep 16541495 = 24812243) B24812243
theorem B11027663 : Blo 1909435 11027663 := bstep (se 1 (by rfl) ⟨8270747, by rfl⟩ : syracuseStep 11027663 = 16541495) B16541495
theorem B7351775 : Blo 1909435 7351775 := bstep (se 1 (by rfl) ⟨5513831, by rfl⟩ : syracuseStep 7351775 = 11027663) B11027663
theorem B4901183 : Blo 1909435 4901183 := bstep (se 1 (by rfl) ⟨3675887, by rfl⟩ : syracuseStep 4901183 = 7351775) B7351775
theorem B3267455 : Blo 1909435 3267455 := bstep (se 1 (by rfl) ⟨2450591, by rfl⟩ : syracuseStep 3267455 = 4901183) B4901183
theorem B8713213 : Blo 1909435 8713213 := bstep (se 3 (by rfl) ⟨1633727, by rfl⟩ : syracuseStep 8713213 = 3267455) B3267455
theorem B185881877 : Blo 1909435 185881877 := bstep (se 6 (by rfl) ⟨4356606, by rfl⟩ : syracuseStep 185881877 = 8713213) B8713213
theorem B123921251 : Blo 1909435 123921251 := bstep (se 1 (by rfl) ⟨92940938, by rfl⟩ : syracuseStep 123921251 = 185881877) B185881877
theorem B82614167 : Blo 1909435 82614167 := bstep (se 1 (by rfl) ⟨61960625, by rfl⟩ : syracuseStep 82614167 = 123921251) B123921251
theorem B55076111 : Blo 1909435 55076111 := bstep (se 1 (by rfl) ⟨41307083, by rfl⟩ : syracuseStep 55076111 = 82614167) B82614167
theorem B36717407 : Blo 1909435 36717407 := bstep (se 1 (by rfl) ⟨27538055, by rfl⟩ : syracuseStep 36717407 = 55076111) B55076111
theorem B24478271 : Blo 1909435 24478271 := bstep (se 1 (by rfl) ⟨18358703, by rfl⟩ : syracuseStep 24478271 = 36717407) B36717407
theorem B16318847 : Blo 1909435 16318847 := bstep (se 1 (by rfl) ⟨12239135, by rfl⟩ : syracuseStep 16318847 = 24478271) B24478271
theorem B10879231 : Blo 1909435 10879231 := bstep (se 1 (by rfl) ⟨8159423, by rfl⟩ : syracuseStep 10879231 = 16318847) B16318847
theorem B14505641 : Blo 1909435 14505641 := bstep (se 2 (by rfl) ⟨5439615, by rfl⟩ : syracuseStep 14505641 = 10879231) B10879231
theorem B9670427 : Blo 1909435 9670427 := bstep (se 1 (by rfl) ⟨7252820, by rfl⟩ : syracuseStep 9670427 = 14505641) B14505641
theorem B6446951 : Blo 1909435 6446951 := bstep (se 1 (by rfl) ⟨4835213, by rfl⟩ : syracuseStep 6446951 = 9670427) B9670427
theorem B4297967 : Blo 1909435 4297967 := bstep (se 1 (by rfl) ⟨3223475, by rfl⟩ : syracuseStep 4297967 = 6446951) B6446951
theorem B2865311 : Blo 1909435 2865311 := bstep (se 1 (by rfl) ⟨2148983, by rfl⟩ : syracuseStep 2865311 = 4297967) B4297967
theorem B1910207 : Blo 1909435 1910207 := bstep (se 1 (by rfl) ⟨1432655, by rfl⟩ : syracuseStep 1910207 = 2865311) B2865311
theorem B2865317 : Blo 1909435 2865317 := bbase (se 4 (by rfl) ⟨268623, by rfl⟩ : syracuseStep 2865317 = 537247) (by norm_num)
theorem B1910211 : Blo 1909435 1910211 := bstep (se 1 (by rfl) ⟨1432658, by rfl⟩ : syracuseStep 1910211 = 2865317) B2865317
theorem B2417617 : Blo 1909435 2417617 := bbase (se 2 (by rfl) ⟨906606, by rfl⟩ : syracuseStep 2417617 = 1813213) (by norm_num)
theorem B3223489 : Blo 1909435 3223489 := bstep (se 2 (by rfl) ⟨1208808, by rfl⟩ : syracuseStep 3223489 = 2417617) B2417617
theorem B4297985 : Blo 1909435 4297985 := bstep (se 2 (by rfl) ⟨1611744, by rfl⟩ : syracuseStep 4297985 = 3223489) B3223489
theorem B2865323 : Blo 1909435 2865323 := bstep (se 1 (by rfl) ⟨2148992, by rfl⟩ : syracuseStep 2865323 = 4297985) B4297985
theorem B1910215 : Blo 1909435 1910215 := bstep (se 1 (by rfl) ⟨1432661, by rfl⟩ : syracuseStep 1910215 = 2865323) B2865323
theorem B2148997 : Blo 1909435 2148997 := bbase (se 4 (by rfl) ⟨201468, by rfl⟩ : syracuseStep 2148997 = 402937) (by norm_num)
theorem B2865329 : Blo 1909435 2865329 := bstep (se 2 (by rfl) ⟨1074498, by rfl⟩ : syracuseStep 2865329 = 2148997) B2148997
theorem B1910219 : Blo 1909435 1910219 := bstep (se 1 (by rfl) ⟨1432664, by rfl⟩ : syracuseStep 1910219 = 2865329) B2865329
theorem B6119621 : Blo 1909435 6119621 := bbase (se 4 (by rfl) ⟨573714, by rfl⟩ : syracuseStep 6119621 = 1147429) (by norm_num)
theorem B4079747 : Blo 1909435 4079747 := bstep (se 1 (by rfl) ⟨3059810, by rfl⟩ : syracuseStep 4079747 = 6119621) B6119621
theorem B2719831 : Blo 1909435 2719831 := bstep (se 1 (by rfl) ⟨2039873, by rfl⟩ : syracuseStep 2719831 = 4079747) B4079747
theorem B3626441 : Blo 1909435 3626441 := bstep (se 2 (by rfl) ⟨1359915, by rfl⟩ : syracuseStep 3626441 = 2719831) B2719831
theorem B2417627 : Blo 1909435 2417627 := bstep (se 1 (by rfl) ⟨1813220, by rfl⟩ : syracuseStep 2417627 = 3626441) B3626441
theorem B6447005 : Blo 1909435 6447005 := bstep (se 3 (by rfl) ⟨1208813, by rfl⟩ : syracuseStep 6447005 = 2417627) B2417627
theorem B4298003 : Blo 1909435 4298003 := bstep (se 1 (by rfl) ⟨3223502, by rfl⟩ : syracuseStep 4298003 = 6447005) B6447005
theorem B2865335 : Blo 1909435 2865335 := bstep (se 1 (by rfl) ⟨2149001, by rfl⟩ : syracuseStep 2865335 = 4298003) B4298003
theorem B1910223 : Blo 1909435 1910223 := bstep (se 1 (by rfl) ⟨1432667, by rfl⟩ : syracuseStep 1910223 = 2865335) B2865335
theorem B2865341 : Blo 1909435 2865341 := bbase (se 3 (by rfl) ⟨537251, by rfl⟩ : syracuseStep 2865341 = 1074503) (by norm_num)
theorem B1910227 : Blo 1909435 1910227 := bstep (se 1 (by rfl) ⟨1432670, by rfl⟩ : syracuseStep 1910227 = 2865341) B2865341
theorem B4298021 : Blo 1909435 4298021 := bbase (se 4 (by rfl) ⟨402939, by rfl⟩ : syracuseStep 4298021 = 805879) (by norm_num)
theorem B2865347 : Blo 1909435 2865347 := bstep (se 1 (by rfl) ⟨2149010, by rfl⟩ : syracuseStep 2865347 = 4298021) B4298021
theorem B1910231 : Blo 1909435 1910231 := bstep (se 1 (by rfl) ⟨1432673, by rfl⟩ : syracuseStep 1910231 = 2865347) B2865347
theorem B4835285 : Blo 1909435 4835285 := bbase (se 7 (by rfl) ⟨56663, by rfl⟩ : syracuseStep 4835285 = 113327) (by norm_num)
theorem B3223523 : Blo 1909435 3223523 := bstep (se 1 (by rfl) ⟨2417642, by rfl⟩ : syracuseStep 3223523 = 4835285) B4835285
theorem B2149015 : Blo 1909435 2149015 := bstep (se 1 (by rfl) ⟨1611761, by rfl⟩ : syracuseStep 2149015 = 3223523) B3223523
theorem B2865353 : Blo 1909435 2865353 := bstep (se 2 (by rfl) ⟨1074507, by rfl⟩ : syracuseStep 2865353 = 2149015) B2149015
theorem B1910235 : Blo 1909435 1910235 := bstep (se 1 (by rfl) ⟨1432676, by rfl⟩ : syracuseStep 1910235 = 2865353) B2865353
theorem B3872605 : Blo 1909435 3872605 := bbase (se 3 (by rfl) ⟨726113, by rfl⟩ : syracuseStep 3872605 = 1452227) (by norm_num)
theorem B5163473 : Blo 1909435 5163473 := bstep (se 2 (by rfl) ⟨1936302, by rfl⟩ : syracuseStep 5163473 = 3872605) B3872605
theorem B13769261 : Blo 1909435 13769261 := bstep (se 3 (by rfl) ⟨2581736, by rfl⟩ : syracuseStep 13769261 = 5163473) B5163473
theorem B9179507 : Blo 1909435 9179507 := bstep (se 1 (by rfl) ⟨6884630, by rfl⟩ : syracuseStep 9179507 = 13769261) B13769261
theorem B6119671 : Blo 1909435 6119671 := bstep (se 1 (by rfl) ⟨4589753, by rfl⟩ : syracuseStep 6119671 = 9179507) B9179507
theorem B8159561 : Blo 1909435 8159561 := bstep (se 2 (by rfl) ⟨3059835, by rfl⟩ : syracuseStep 8159561 = 6119671) B6119671
theorem B5439707 : Blo 1909435 5439707 := bstep (se 1 (by rfl) ⟨4079780, by rfl⟩ : syracuseStep 5439707 = 8159561) B8159561
theorem B3626471 : Blo 1909435 3626471 := bstep (se 1 (by rfl) ⟨2719853, by rfl⟩ : syracuseStep 3626471 = 5439707) B5439707
theorem B9670589 : Blo 1909435 9670589 := bstep (se 3 (by rfl) ⟨1813235, by rfl⟩ : syracuseStep 9670589 = 3626471) B3626471
theorem B6447059 : Blo 1909435 6447059 := bstep (se 1 (by rfl) ⟨4835294, by rfl⟩ : syracuseStep 6447059 = 9670589) B9670589
theorem B4298039 : Blo 1909435 4298039 := bstep (se 1 (by rfl) ⟨3223529, by rfl⟩ : syracuseStep 4298039 = 6447059) B6447059
theorem B2865359 : Blo 1909435 2865359 := bstep (se 1 (by rfl) ⟨2149019, by rfl⟩ : syracuseStep 2865359 = 4298039) B4298039
theorem B1910239 : Blo 1909435 1910239 := bstep (se 1 (by rfl) ⟨1432679, by rfl⟩ : syracuseStep 1910239 = 2865359) B2865359
theorem B2865365 : Blo 1909435 2865365 := bbase (se 7 (by rfl) ⟨33578, by rfl⟩ : syracuseStep 2865365 = 67157) (by norm_num)
theorem B1910243 : Blo 1909435 1910243 := bstep (se 1 (by rfl) ⟨1432682, by rfl⟩ : syracuseStep 1910243 = 2865365) B2865365
theorem B10467893 : Blo 1909435 10467893 := bbase (se 5 (by rfl) ⟨490682, by rfl⟩ : syracuseStep 10467893 = 981365) (by norm_num)
theorem B27914381 : Blo 1909435 27914381 := bstep (se 3 (by rfl) ⟨5233946, by rfl⟩ : syracuseStep 27914381 = 10467893) B10467893
theorem B18609587 : Blo 1909435 18609587 := bstep (se 1 (by rfl) ⟨13957190, by rfl⟩ : syracuseStep 18609587 = 27914381) B27914381
theorem B12406391 : Blo 1909435 12406391 := bstep (se 1 (by rfl) ⟨9304793, by rfl⟩ : syracuseStep 12406391 = 18609587) B18609587
theorem B8270927 : Blo 1909435 8270927 := bstep (se 1 (by rfl) ⟨6203195, by rfl⟩ : syracuseStep 8270927 = 12406391) B12406391
theorem B5513951 : Blo 1909435 5513951 := bstep (se 1 (by rfl) ⟨4135463, by rfl⟩ : syracuseStep 5513951 = 8270927) B8270927
theorem B14703869 : Blo 1909435 14703869 := bstep (se 3 (by rfl) ⟨2756975, by rfl⟩ : syracuseStep 14703869 = 5513951) B5513951
theorem B9802579 : Blo 1909435 9802579 := bstep (se 1 (by rfl) ⟨7351934, by rfl⟩ : syracuseStep 9802579 = 14703869) B14703869
theorem B13070105 : Blo 1909435 13070105 := bstep (se 2 (by rfl) ⟨4901289, by rfl⟩ : syracuseStep 13070105 = 9802579) B9802579
theorem B8713403 : Blo 1909435 8713403 := bstep (se 1 (by rfl) ⟨6535052, by rfl⟩ : syracuseStep 8713403 = 13070105) B13070105
theorem B5808935 : Blo 1909435 5808935 := bstep (se 1 (by rfl) ⟨4356701, by rfl⟩ : syracuseStep 5808935 = 8713403) B8713403
theorem B3872623 : Blo 1909435 3872623 := bstep (se 1 (by rfl) ⟨2904467, by rfl⟩ : syracuseStep 3872623 = 5808935) B5808935
theorem B5163497 : Blo 1909435 5163497 := bstep (se 2 (by rfl) ⟨1936311, by rfl⟩ : syracuseStep 5163497 = 3872623) B3872623
theorem B3442331 : Blo 1909435 3442331 := bstep (se 1 (by rfl) ⟨2581748, by rfl⟩ : syracuseStep 3442331 = 5163497) B5163497
theorem B2294887 : Blo 1909435 2294887 := bstep (se 1 (by rfl) ⟨1721165, by rfl⟩ : syracuseStep 2294887 = 3442331) B3442331
theorem B3059849 : Blo 1909435 3059849 := bstep (se 2 (by rfl) ⟨1147443, by rfl⟩ : syracuseStep 3059849 = 2294887) B2294887
theorem B2039899 : Blo 1909435 2039899 := bstep (se 1 (by rfl) ⟨1529924, by rfl⟩ : syracuseStep 2039899 = 3059849) B3059849
theorem B2719865 : Blo 1909435 2719865 := bstep (se 2 (by rfl) ⟨1019949, by rfl⟩ : syracuseStep 2719865 = 2039899) B2039899
theorem B7252973 : Blo 1909435 7252973 := bstep (se 3 (by rfl) ⟨1359932, by rfl⟩ : syracuseStep 7252973 = 2719865) B2719865
theorem B4835315 : Blo 1909435 4835315 := bstep (se 1 (by rfl) ⟨3626486, by rfl⟩ : syracuseStep 4835315 = 7252973) B7252973
theorem B3223543 : Blo 1909435 3223543 := bstep (se 1 (by rfl) ⟨2417657, by rfl⟩ : syracuseStep 3223543 = 4835315) B4835315
theorem B4298057 : Blo 1909435 4298057 := bstep (se 2 (by rfl) ⟨1611771, by rfl⟩ : syracuseStep 4298057 = 3223543) B3223543
theorem B2865371 : Blo 1909435 2865371 := bstep (se 1 (by rfl) ⟨2149028, by rfl⟩ : syracuseStep 2865371 = 4298057) B4298057
theorem B1910247 : Blo 1909435 1910247 := bstep (se 1 (by rfl) ⟨1432685, by rfl⟩ : syracuseStep 1910247 = 2865371) B2865371
theorem B2149033 : Blo 1909435 2149033 := bbase (se 2 (by rfl) ⟨805887, by rfl⟩ : syracuseStep 2149033 = 1611775) (by norm_num)
theorem B2865377 : Blo 1909435 2865377 := bstep (se 2 (by rfl) ⟨1074516, by rfl⟩ : syracuseStep 2865377 = 2149033) B2149033
theorem B1910251 : Blo 1909435 1910251 := bstep (se 1 (by rfl) ⟨1432688, by rfl⟩ : syracuseStep 1910251 = 2865377) B2865377
theorem B3059861 : Blo 1909435 3059861 := bbase (se 6 (by rfl) ⟨71715, by rfl⟩ : syracuseStep 3059861 = 143431) (by norm_num)
theorem B8159629 : Blo 1909435 8159629 := bstep (se 3 (by rfl) ⟨1529930, by rfl⟩ : syracuseStep 8159629 = 3059861) B3059861
theorem B10879505 : Blo 1909435 10879505 := bstep (se 2 (by rfl) ⟨4079814, by rfl⟩ : syracuseStep 10879505 = 8159629) B8159629
theorem B7253003 : Blo 1909435 7253003 := bstep (se 1 (by rfl) ⟨5439752, by rfl⟩ : syracuseStep 7253003 = 10879505) B10879505
theorem B4835335 : Blo 1909435 4835335 := bstep (se 1 (by rfl) ⟨3626501, by rfl⟩ : syracuseStep 4835335 = 7253003) B7253003
theorem B6447113 : Blo 1909435 6447113 := bstep (se 2 (by rfl) ⟨2417667, by rfl⟩ : syracuseStep 6447113 = 4835335) B4835335
theorem B4298075 : Blo 1909435 4298075 := bstep (se 1 (by rfl) ⟨3223556, by rfl⟩ : syracuseStep 4298075 = 6447113) B6447113
theorem B2865383 : Blo 1909435 2865383 := bstep (se 1 (by rfl) ⟨2149037, by rfl⟩ : syracuseStep 2865383 = 4298075) B4298075
theorem B1910255 : Blo 1909435 1910255 := bstep (se 1 (by rfl) ⟨1432691, by rfl⟩ : syracuseStep 1910255 = 2865383) B2865383
theorem B2865389 : Blo 1909435 2865389 := bbase (se 3 (by rfl) ⟨537260, by rfl⟩ : syracuseStep 2865389 = 1074521) (by norm_num)
theorem B1910259 : Blo 1909435 1910259 := bstep (se 1 (by rfl) ⟨1432694, by rfl⟩ : syracuseStep 1910259 = 2865389) B2865389
theorem B4298093 : Blo 1909435 4298093 := bbase (se 3 (by rfl) ⟨805892, by rfl⟩ : syracuseStep 4298093 = 1611785) (by norm_num)
theorem B2865395 : Blo 1909435 2865395 := bstep (se 1 (by rfl) ⟨2149046, by rfl⟩ : syracuseStep 2865395 = 4298093) B4298093
theorem B1910263 : Blo 1909435 1910263 := bstep (se 1 (by rfl) ⟨1432697, by rfl⟩ : syracuseStep 1910263 = 2865395) B2865395
theorem B3626525 : Blo 1909435 3626525 := bbase (se 3 (by rfl) ⟨679973, by rfl⟩ : syracuseStep 3626525 = 1359947) (by norm_num)
theorem B2417683 : Blo 1909435 2417683 := bstep (se 1 (by rfl) ⟨1813262, by rfl⟩ : syracuseStep 2417683 = 3626525) B3626525
theorem B3223577 : Blo 1909435 3223577 := bstep (se 2 (by rfl) ⟨1208841, by rfl⟩ : syracuseStep 3223577 = 2417683) B2417683
theorem B2149051 : Blo 1909435 2149051 := bstep (se 1 (by rfl) ⟨1611788, by rfl⟩ : syracuseStep 2149051 = 3223577) B3223577
theorem B2865401 : Blo 1909435 2865401 := bstep (se 2 (by rfl) ⟨1074525, by rfl⟩ : syracuseStep 2865401 = 2149051) B2149051
theorem B1910267 : Blo 1909435 1910267 := bstep (se 1 (by rfl) ⟨1432700, by rfl⟩ : syracuseStep 1910267 = 2865401) B2865401
theorem B3872669 : Blo 1909435 3872669 := bbase (se 3 (by rfl) ⟨726125, by rfl⟩ : syracuseStep 3872669 = 1452251) (by norm_num)
theorem B10327117 : Blo 1909435 10327117 := bstep (se 3 (by rfl) ⟨1936334, by rfl⟩ : syracuseStep 10327117 = 3872669) B3872669
theorem B13769489 : Blo 1909435 13769489 := bstep (se 2 (by rfl) ⟨5163558, by rfl⟩ : syracuseStep 13769489 = 10327117) B10327117
theorem B9179659 : Blo 1909435 9179659 := bstep (se 1 (by rfl) ⟨6884744, by rfl⟩ : syracuseStep 9179659 = 13769489) B13769489
theorem B48958181 : Blo 1909435 48958181 := bstep (se 4 (by rfl) ⟨4589829, by rfl⟩ : syracuseStep 48958181 = 9179659) B9179659
theorem B32638787 : Blo 1909435 32638787 := bstep (se 1 (by rfl) ⟨24479090, by rfl⟩ : syracuseStep 32638787 = 48958181) B48958181
theorem B21759191 : Blo 1909435 21759191 := bstep (se 1 (by rfl) ⟨16319393, by rfl⟩ : syracuseStep 21759191 = 32638787) B32638787
theorem B14506127 : Blo 1909435 14506127 := bstep (se 1 (by rfl) ⟨10879595, by rfl⟩ : syracuseStep 14506127 = 21759191) B21759191
theorem B9670751 : Blo 1909435 9670751 := bstep (se 1 (by rfl) ⟨7253063, by rfl⟩ : syracuseStep 9670751 = 14506127) B14506127
theorem B6447167 : Blo 1909435 6447167 := bstep (se 1 (by rfl) ⟨4835375, by rfl⟩ : syracuseStep 6447167 = 9670751) B9670751
theorem B4298111 : Blo 1909435 4298111 := bstep (se 1 (by rfl) ⟨3223583, by rfl⟩ : syracuseStep 4298111 = 6447167) B6447167
theorem B2865407 : Blo 1909435 2865407 := bstep (se 1 (by rfl) ⟨2149055, by rfl⟩ : syracuseStep 2865407 = 4298111) B4298111
theorem B1910271 : Blo 1909435 1910271 := bstep (se 1 (by rfl) ⟨1432703, by rfl⟩ : syracuseStep 1910271 = 2865407) B2865407
theorem B2865413 : Blo 1909435 2865413 := bbase (se 4 (by rfl) ⟨268632, by rfl⟩ : syracuseStep 2865413 = 537265) (by norm_num)
theorem B1910275 : Blo 1909435 1910275 := bstep (se 1 (by rfl) ⟨1432706, by rfl⟩ : syracuseStep 1910275 = 2865413) B2865413
theorem B3223597 : Blo 1909435 3223597 := bbase (se 3 (by rfl) ⟨604424, by rfl⟩ : syracuseStep 3223597 = 1208849) (by norm_num)
theorem B4298129 : Blo 1909435 4298129 := bstep (se 2 (by rfl) ⟨1611798, by rfl⟩ : syracuseStep 4298129 = 3223597) B3223597
theorem B2865419 : Blo 1909435 2865419 := bstep (se 1 (by rfl) ⟨2149064, by rfl⟩ : syracuseStep 2865419 = 4298129) B4298129
theorem B1910279 : Blo 1909435 1910279 := bstep (se 1 (by rfl) ⟨1432709, by rfl⟩ : syracuseStep 1910279 = 2865419) B2865419
theorem B2149069 : Blo 1909435 2149069 := bbase (se 3 (by rfl) ⟨402950, by rfl⟩ : syracuseStep 2149069 = 805901) (by norm_num)
theorem B2865425 : Blo 1909435 2865425 := bstep (se 2 (by rfl) ⟨1074534, by rfl⟩ : syracuseStep 2865425 = 2149069) B2149069
theorem B1910283 : Blo 1909435 1910283 := bstep (se 1 (by rfl) ⟨1432712, by rfl⟩ : syracuseStep 1910283 = 2865425) B2865425
theorem B6447221 : Blo 1909435 6447221 := bbase (se 5 (by rfl) ⟨302213, by rfl⟩ : syracuseStep 6447221 = 604427) (by norm_num)
theorem B4298147 : Blo 1909435 4298147 := bstep (se 1 (by rfl) ⟨3223610, by rfl⟩ : syracuseStep 4298147 = 6447221) B6447221
theorem B2865431 : Blo 1909435 2865431 := bstep (se 1 (by rfl) ⟨2149073, by rfl⟩ : syracuseStep 2865431 = 4298147) B4298147
theorem B1910287 : Blo 1909435 1910287 := bstep (se 1 (by rfl) ⟨1432715, by rfl⟩ : syracuseStep 1910287 = 2865431) B2865431
theorem B2865437 : Blo 1909435 2865437 := bbase (se 3 (by rfl) ⟨537269, by rfl⟩ : syracuseStep 2865437 = 1074539) (by norm_num)
theorem B1910291 : Blo 1909435 1910291 := bstep (se 1 (by rfl) ⟨1432718, by rfl⟩ : syracuseStep 1910291 = 2865437) B2865437
theorem B4298165 : Blo 1909435 4298165 := bbase (se 5 (by rfl) ⟨201476, by rfl⟩ : syracuseStep 4298165 = 402953) (by norm_num)
theorem B2865443 : Blo 1909435 2865443 := bstep (se 1 (by rfl) ⟨2149082, by rfl⟩ : syracuseStep 2865443 = 4298165) B4298165
theorem B1910295 : Blo 1909435 1910295 := bstep (se 1 (by rfl) ⟨1432721, by rfl⟩ : syracuseStep 1910295 = 2865443) B2865443
theorem B4079909 : Blo 1909435 4079909 := bbase (se 4 (by rfl) ⟨382491, by rfl⟩ : syracuseStep 4079909 = 764983) (by norm_num)
theorem B10879757 : Blo 1909435 10879757 := bstep (se 3 (by rfl) ⟨2039954, by rfl⟩ : syracuseStep 10879757 = 4079909) B4079909
theorem B7253171 : Blo 1909435 7253171 := bstep (se 1 (by rfl) ⟨5439878, by rfl⟩ : syracuseStep 7253171 = 10879757) B10879757
theorem B4835447 : Blo 1909435 4835447 := bstep (se 1 (by rfl) ⟨3626585, by rfl⟩ : syracuseStep 4835447 = 7253171) B7253171
theorem B3223631 : Blo 1909435 3223631 := bstep (se 1 (by rfl) ⟨2417723, by rfl⟩ : syracuseStep 3223631 = 4835447) B4835447
theorem B2149087 : Blo 1909435 2149087 := bstep (se 1 (by rfl) ⟨1611815, by rfl⟩ : syracuseStep 2149087 = 3223631) B3223631
theorem B2865449 : Blo 1909435 2865449 := bstep (se 2 (by rfl) ⟨1074543, by rfl⟩ : syracuseStep 2865449 = 2149087) B2149087
theorem B1910299 : Blo 1909435 1910299 := bstep (se 1 (by rfl) ⟨1432724, by rfl⟩ : syracuseStep 1910299 = 2865449) B2865449
theorem B4079917 : Blo 1909435 4079917 := bbase (se 3 (by rfl) ⟨764984, by rfl⟩ : syracuseStep 4079917 = 1529969) (by norm_num)
theorem B5439889 : Blo 1909435 5439889 := bstep (se 2 (by rfl) ⟨2039958, by rfl⟩ : syracuseStep 5439889 = 4079917) B4079917
theorem B7253185 : Blo 1909435 7253185 := bstep (se 2 (by rfl) ⟨2719944, by rfl⟩ : syracuseStep 7253185 = 5439889) B5439889
theorem B9670913 : Blo 1909435 9670913 := bstep (se 2 (by rfl) ⟨3626592, by rfl⟩ : syracuseStep 9670913 = 7253185) B7253185
theorem B6447275 : Blo 1909435 6447275 := bstep (se 1 (by rfl) ⟨4835456, by rfl⟩ : syracuseStep 6447275 = 9670913) B9670913
theorem B4298183 : Blo 1909435 4298183 := bstep (se 1 (by rfl) ⟨3223637, by rfl⟩ : syracuseStep 4298183 = 6447275) B6447275
theorem B2865455 : Blo 1909435 2865455 := bstep (se 1 (by rfl) ⟨2149091, by rfl⟩ : syracuseStep 2865455 = 4298183) B4298183
theorem B1910303 : Blo 1909435 1910303 := bstep (se 1 (by rfl) ⟨1432727, by rfl⟩ : syracuseStep 1910303 = 2865455) B2865455
theorem B2865461 : Blo 1909435 2865461 := bbase (se 5 (by rfl) ⟨134318, by rfl⟩ : syracuseStep 2865461 = 268637) (by norm_num)
theorem B1910307 : Blo 1909435 1910307 := bstep (se 1 (by rfl) ⟨1432730, by rfl⟩ : syracuseStep 1910307 = 2865461) B2865461
theorem B4835477 : Blo 1909435 4835477 := bbase (se 6 (by rfl) ⟨113331, by rfl⟩ : syracuseStep 4835477 = 226663) (by norm_num)
theorem B3223651 : Blo 1909435 3223651 := bstep (se 1 (by rfl) ⟨2417738, by rfl⟩ : syracuseStep 3223651 = 4835477) B4835477
theorem B4298201 : Blo 1909435 4298201 := bstep (se 2 (by rfl) ⟨1611825, by rfl⟩ : syracuseStep 4298201 = 3223651) B3223651
theorem B2865467 : Blo 1909435 2865467 := bstep (se 1 (by rfl) ⟨2149100, by rfl⟩ : syracuseStep 2865467 = 4298201) B4298201
theorem B1910311 : Blo 1909435 1910311 := bstep (se 1 (by rfl) ⟨1432733, by rfl⟩ : syracuseStep 1910311 = 2865467) B2865467
theorem B2149105 : Blo 1909435 2149105 := bbase (se 2 (by rfl) ⟨805914, by rfl⟩ : syracuseStep 2149105 = 1611829) (by norm_num)
theorem B2865473 : Blo 1909435 2865473 := bstep (se 2 (by rfl) ⟨1074552, by rfl⟩ : syracuseStep 2865473 = 2149105) B2149105
theorem B1910315 : Blo 1909435 1910315 := bstep (se 1 (by rfl) ⟨1432736, by rfl⟩ : syracuseStep 1910315 = 2865473) B2865473
theorem B13248917 : Blo 1909435 13248917 := bbase (se 6 (by rfl) ⟨310521, by rfl⟩ : syracuseStep 13248917 = 621043) (by norm_num)
theorem B8832611 : Blo 1909435 8832611 := bstep (se 1 (by rfl) ⟨6624458, by rfl⟩ : syracuseStep 8832611 = 13248917) B13248917
theorem B23553629 : Blo 1909435 23553629 := bstep (se 3 (by rfl) ⟨4416305, by rfl⟩ : syracuseStep 23553629 = 8832611) B8832611
theorem B15702419 : Blo 1909435 15702419 := bstep (se 1 (by rfl) ⟨11776814, by rfl⟩ : syracuseStep 15702419 = 23553629) B23553629
theorem B10468279 : Blo 1909435 10468279 := bstep (se 1 (by rfl) ⟨7851209, by rfl⟩ : syracuseStep 10468279 = 15702419) B15702419
theorem B13957705 : Blo 1909435 13957705 := bstep (se 2 (by rfl) ⟨5234139, by rfl⟩ : syracuseStep 13957705 = 10468279) B10468279
theorem B18610273 : Blo 1909435 18610273 := bstep (se 2 (by rfl) ⟨6978852, by rfl⟩ : syracuseStep 18610273 = 13957705) B13957705
theorem B24813697 : Blo 1909435 24813697 := bstep (se 2 (by rfl) ⟨9305136, by rfl⟩ : syracuseStep 24813697 = 18610273) B18610273
theorem B33084929 : Blo 1909435 33084929 := bstep (se 2 (by rfl) ⟨12406848, by rfl⟩ : syracuseStep 33084929 = 24813697) B24813697
theorem B22056619 : Blo 1909435 22056619 := bstep (se 1 (by rfl) ⟨16542464, by rfl⟩ : syracuseStep 22056619 = 33084929) B33084929
theorem B29408825 : Blo 1909435 29408825 := bstep (se 2 (by rfl) ⟨11028309, by rfl⟩ : syracuseStep 29408825 = 22056619) B22056619
theorem B19605883 : Blo 1909435 19605883 := bstep (se 1 (by rfl) ⟨14704412, by rfl⟩ : syracuseStep 19605883 = 29408825) B29408825
theorem B26141177 : Blo 1909435 26141177 := bstep (se 2 (by rfl) ⟨9802941, by rfl⟩ : syracuseStep 26141177 = 19605883) B19605883
theorem B69709805 : Blo 1909435 69709805 := bstep (se 3 (by rfl) ⟨13070588, by rfl⟩ : syracuseStep 69709805 = 26141177) B26141177
theorem B46473203 : Blo 1909435 46473203 := bstep (se 1 (by rfl) ⟨34854902, by rfl⟩ : syracuseStep 46473203 = 69709805) B69709805
theorem B30982135 : Blo 1909435 30982135 := bstep (se 1 (by rfl) ⟨23236601, by rfl⟩ : syracuseStep 30982135 = 46473203) B46473203
theorem B41309513 : Blo 1909435 41309513 := bstep (se 2 (by rfl) ⟨15491067, by rfl⟩ : syracuseStep 41309513 = 30982135) B30982135
theorem B27539675 : Blo 1909435 27539675 := bstep (se 1 (by rfl) ⟨20654756, by rfl⟩ : syracuseStep 27539675 = 41309513) B41309513
theorem B18359783 : Blo 1909435 18359783 := bstep (se 1 (by rfl) ⟨13769837, by rfl⟩ : syracuseStep 18359783 = 27539675) B27539675
theorem B12239855 : Blo 1909435 12239855 := bstep (se 1 (by rfl) ⟨9179891, by rfl⟩ : syracuseStep 12239855 = 18359783) B18359783
theorem B8159903 : Blo 1909435 8159903 := bstep (se 1 (by rfl) ⟨6119927, by rfl⟩ : syracuseStep 8159903 = 12239855) B12239855
theorem B5439935 : Blo 1909435 5439935 := bstep (se 1 (by rfl) ⟨4079951, by rfl⟩ : syracuseStep 5439935 = 8159903) B8159903
theorem B3626623 : Blo 1909435 3626623 := bstep (se 1 (by rfl) ⟨2719967, by rfl⟩ : syracuseStep 3626623 = 5439935) B5439935
theorem B4835497 : Blo 1909435 4835497 := bstep (se 2 (by rfl) ⟨1813311, by rfl⟩ : syracuseStep 4835497 = 3626623) B3626623
theorem B6447329 : Blo 1909435 6447329 := bstep (se 2 (by rfl) ⟨2417748, by rfl⟩ : syracuseStep 6447329 = 4835497) B4835497
theorem B4298219 : Blo 1909435 4298219 := bstep (se 1 (by rfl) ⟨3223664, by rfl⟩ : syracuseStep 4298219 = 6447329) B6447329
theorem B2865479 : Blo 1909435 2865479 := bstep (se 1 (by rfl) ⟨2149109, by rfl⟩ : syracuseStep 2865479 = 4298219) B4298219
theorem B1910319 : Blo 1909435 1910319 := bstep (se 1 (by rfl) ⟨1432739, by rfl⟩ : syracuseStep 1910319 = 2865479) B2865479
theorem B2865485 : Blo 1909435 2865485 := bbase (se 3 (by rfl) ⟨537278, by rfl⟩ : syracuseStep 2865485 = 1074557) (by norm_num)
theorem B1910323 : Blo 1909435 1910323 := bstep (se 1 (by rfl) ⟨1432742, by rfl⟩ : syracuseStep 1910323 = 2865485) B2865485
theorem B4298237 : Blo 1909435 4298237 := bbase (se 3 (by rfl) ⟨805919, by rfl⟩ : syracuseStep 4298237 = 1611839) (by norm_num)
theorem B2865491 : Blo 1909435 2865491 := bstep (se 1 (by rfl) ⟨2149118, by rfl⟩ : syracuseStep 2865491 = 4298237) B4298237
theorem B1910327 : Blo 1909435 1910327 := bstep (se 1 (by rfl) ⟨1432745, by rfl⟩ : syracuseStep 1910327 = 2865491) B2865491
theorem B3223685 : Blo 1909435 3223685 := bbase (se 4 (by rfl) ⟨302220, by rfl⟩ : syracuseStep 3223685 = 604441) (by norm_num)
theorem B2149123 : Blo 1909435 2149123 := bstep (se 1 (by rfl) ⟨1611842, by rfl⟩ : syracuseStep 2149123 = 3223685) B3223685
theorem B2865497 : Blo 1909435 2865497 := bstep (se 2 (by rfl) ⟨1074561, by rfl⟩ : syracuseStep 2865497 = 2149123) B2149123
theorem B1910331 : Blo 1909435 1910331 := bstep (se 1 (by rfl) ⟨1432748, by rfl⟩ : syracuseStep 1910331 = 2865497) B2865497
theorem B14506613 : Blo 1909435 14506613 := bbase (se 5 (by rfl) ⟨679997, by rfl⟩ : syracuseStep 14506613 = 1359995) (by norm_num)
theorem B9671075 : Blo 1909435 9671075 := bstep (se 1 (by rfl) ⟨7253306, by rfl⟩ : syracuseStep 9671075 = 14506613) B14506613
theorem B6447383 : Blo 1909435 6447383 := bstep (se 1 (by rfl) ⟨4835537, by rfl⟩ : syracuseStep 6447383 = 9671075) B9671075
theorem B4298255 : Blo 1909435 4298255 := bstep (se 1 (by rfl) ⟨3223691, by rfl⟩ : syracuseStep 4298255 = 6447383) B6447383
theorem B2865503 : Blo 1909435 2865503 := bstep (se 1 (by rfl) ⟨2149127, by rfl⟩ : syracuseStep 2865503 = 4298255) B4298255
theorem B1910335 : Blo 1909435 1910335 := bstep (se 1 (by rfl) ⟨1432751, by rfl⟩ : syracuseStep 1910335 = 2865503) B2865503
theorem B2865509 : Blo 1909435 2865509 := bbase (se 4 (by rfl) ⟨268641, by rfl⟩ : syracuseStep 2865509 = 537283) (by norm_num)
theorem B1910339 : Blo 1909435 1910339 := bstep (se 1 (by rfl) ⟨1432754, by rfl⟩ : syracuseStep 1910339 = 2865509) B2865509
theorem B3626669 : Blo 1909435 3626669 := bbase (se 3 (by rfl) ⟨680000, by rfl⟩ : syracuseStep 3626669 = 1360001) (by norm_num)
theorem B2417779 : Blo 1909435 2417779 := bstep (se 1 (by rfl) ⟨1813334, by rfl⟩ : syracuseStep 2417779 = 3626669) B3626669
theorem B3223705 : Blo 1909435 3223705 := bstep (se 2 (by rfl) ⟨1208889, by rfl⟩ : syracuseStep 3223705 = 2417779) B2417779
theorem B4298273 : Blo 1909435 4298273 := bstep (se 2 (by rfl) ⟨1611852, by rfl⟩ : syracuseStep 4298273 = 3223705) B3223705
theorem B2865515 : Blo 1909435 2865515 := bstep (se 1 (by rfl) ⟨2149136, by rfl⟩ : syracuseStep 2865515 = 4298273) B4298273
theorem B1910343 : Blo 1909435 1910343 := bstep (se 1 (by rfl) ⟨1432757, by rfl⟩ : syracuseStep 1910343 = 2865515) B2865515
theorem B2149141 : Blo 1909435 2149141 := bbase (se 6 (by rfl) ⟨50370, by rfl⟩ : syracuseStep 2149141 = 100741) (by norm_num)
theorem B2865521 : Blo 1909435 2865521 := bstep (se 2 (by rfl) ⟨1074570, by rfl⟩ : syracuseStep 2865521 = 2149141) B2149141
theorem B1910347 : Blo 1909435 1910347 := bstep (se 1 (by rfl) ⟨1432760, by rfl⟩ : syracuseStep 1910347 = 2865521) B2865521
theorem B2417789 : Blo 1909435 2417789 := bbase (se 3 (by rfl) ⟨453335, by rfl⟩ : syracuseStep 2417789 = 906671) (by norm_num)
theorem B6447437 : Blo 1909435 6447437 := bstep (se 3 (by rfl) ⟨1208894, by rfl⟩ : syracuseStep 6447437 = 2417789) B2417789
theorem B4298291 : Blo 1909435 4298291 := bstep (se 1 (by rfl) ⟨3223718, by rfl⟩ : syracuseStep 4298291 = 6447437) B6447437
theorem B2865527 : Blo 1909435 2865527 := bstep (se 1 (by rfl) ⟨2149145, by rfl⟩ : syracuseStep 2865527 = 4298291) B4298291
theorem B1910351 : Blo 1909435 1910351 := bstep (se 1 (by rfl) ⟨1432763, by rfl⟩ : syracuseStep 1910351 = 2865527) B2865527
theorem B2865533 : Blo 1909435 2865533 := bbase (se 3 (by rfl) ⟨537287, by rfl⟩ : syracuseStep 2865533 = 1074575) (by norm_num)
theorem B1910355 : Blo 1909435 1910355 := bstep (se 1 (by rfl) ⟨1432766, by rfl⟩ : syracuseStep 1910355 = 2865533) B2865533
theorem B4298309 : Blo 1909435 4298309 := bbase (se 4 (by rfl) ⟨402966, by rfl⟩ : syracuseStep 4298309 = 805933) (by norm_num)
theorem B2865539 : Blo 1909435 2865539 := bstep (se 1 (by rfl) ⟨2149154, by rfl⟩ : syracuseStep 2865539 = 4298309) B4298309
theorem B1910359 : Blo 1909435 1910359 := bstep (se 1 (by rfl) ⟨1432769, by rfl⟩ : syracuseStep 1910359 = 2865539) B2865539
theorem B4590053 : Blo 1909435 4590053 := bbase (se 4 (by rfl) ⟨430317, by rfl⟩ : syracuseStep 4590053 = 860635) (by norm_num)
theorem B3060035 : Blo 1909435 3060035 := bstep (se 1 (by rfl) ⟨2295026, by rfl⟩ : syracuseStep 3060035 = 4590053) B4590053
theorem B2040023 : Blo 1909435 2040023 := bstep (se 1 (by rfl) ⟨1530017, by rfl⟩ : syracuseStep 2040023 = 3060035) B3060035
theorem B5440061 : Blo 1909435 5440061 := bstep (se 3 (by rfl) ⟨1020011, by rfl⟩ : syracuseStep 5440061 = 2040023) B2040023
theorem B3626707 : Blo 1909435 3626707 := bstep (se 1 (by rfl) ⟨2720030, by rfl⟩ : syracuseStep 3626707 = 5440061) B5440061
theorem B4835609 : Blo 1909435 4835609 := bstep (se 2 (by rfl) ⟨1813353, by rfl⟩ : syracuseStep 4835609 = 3626707) B3626707
theorem B3223739 : Blo 1909435 3223739 := bstep (se 1 (by rfl) ⟨2417804, by rfl⟩ : syracuseStep 3223739 = 4835609) B4835609
theorem B2149159 : Blo 1909435 2149159 := bstep (se 1 (by rfl) ⟨1611869, by rfl⟩ : syracuseStep 2149159 = 3223739) B3223739
theorem B2865545 : Blo 1909435 2865545 := bstep (se 2 (by rfl) ⟨1074579, by rfl⟩ : syracuseStep 2865545 = 2149159) B2149159
theorem B1910363 : Blo 1909435 1910363 := bstep (se 1 (by rfl) ⟨1432772, by rfl⟩ : syracuseStep 1910363 = 2865545) B2865545
theorem B9671237 : Blo 1909435 9671237 := bbase (se 4 (by rfl) ⟨906678, by rfl⟩ : syracuseStep 9671237 = 1813357) (by norm_num)
theorem B6447491 : Blo 1909435 6447491 := bstep (se 1 (by rfl) ⟨4835618, by rfl⟩ : syracuseStep 6447491 = 9671237) B9671237
theorem B4298327 : Blo 1909435 4298327 := bstep (se 1 (by rfl) ⟨3223745, by rfl⟩ : syracuseStep 4298327 = 6447491) B6447491
theorem B2865551 : Blo 1909435 2865551 := bstep (se 1 (by rfl) ⟨2149163, by rfl⟩ : syracuseStep 2865551 = 4298327) B4298327
theorem B1910367 : Blo 1909435 1910367 := bstep (se 1 (by rfl) ⟨1432775, by rfl⟩ : syracuseStep 1910367 = 2865551) B2865551
theorem B2865557 : Blo 1909435 2865557 := bbase (se 6 (by rfl) ⟨67161, by rfl⟩ : syracuseStep 2865557 = 134323) (by norm_num)
theorem B1910371 : Blo 1909435 1910371 := bstep (se 1 (by rfl) ⟨1432778, by rfl⟩ : syracuseStep 1910371 = 2865557) B2865557
theorem B2904661 : Blo 1909435 2904661 := bbase (se 8 (by rfl) ⟨17019, by rfl⟩ : syracuseStep 2904661 = 34039) (by norm_num)
theorem B3872881 : Blo 1909435 3872881 := bstep (se 2 (by rfl) ⟨1452330, by rfl⟩ : syracuseStep 3872881 = 2904661) B2904661
theorem B5163841 : Blo 1909435 5163841 := bstep (se 2 (by rfl) ⟨1936440, by rfl⟩ : syracuseStep 5163841 = 3872881) B3872881
theorem B6885121 : Blo 1909435 6885121 := bstep (se 2 (by rfl) ⟨2581920, by rfl⟩ : syracuseStep 6885121 = 5163841) B5163841
theorem B9180161 : Blo 1909435 9180161 := bstep (se 2 (by rfl) ⟨3442560, by rfl⟩ : syracuseStep 9180161 = 6885121) B6885121
theorem B6120107 : Blo 1909435 6120107 := bstep (se 1 (by rfl) ⟨4590080, by rfl⟩ : syracuseStep 6120107 = 9180161) B9180161
theorem B4080071 : Blo 1909435 4080071 := bstep (se 1 (by rfl) ⟨3060053, by rfl⟩ : syracuseStep 4080071 = 6120107) B6120107
theorem B10880189 : Blo 1909435 10880189 := bstep (se 3 (by rfl) ⟨2040035, by rfl⟩ : syracuseStep 10880189 = 4080071) B4080071
theorem B7253459 : Blo 1909435 7253459 := bstep (se 1 (by rfl) ⟨5440094, by rfl⟩ : syracuseStep 7253459 = 10880189) B10880189
theorem B4835639 : Blo 1909435 4835639 := bstep (se 1 (by rfl) ⟨3626729, by rfl⟩ : syracuseStep 4835639 = 7253459) B7253459
theorem B3223759 : Blo 1909435 3223759 := bstep (se 1 (by rfl) ⟨2417819, by rfl⟩ : syracuseStep 3223759 = 4835639) B4835639
theorem B4298345 : Blo 1909435 4298345 := bstep (se 2 (by rfl) ⟨1611879, by rfl⟩ : syracuseStep 4298345 = 3223759) B3223759
theorem B2865563 : Blo 1909435 2865563 := bstep (se 1 (by rfl) ⟨2149172, by rfl⟩ : syracuseStep 2865563 = 4298345) B4298345
theorem B1910375 : Blo 1909435 1910375 := bstep (se 1 (by rfl) ⟨1432781, by rfl⟩ : syracuseStep 1910375 = 2865563) B2865563
theorem B2149177 : Blo 1909435 2149177 := bbase (se 2 (by rfl) ⟨805941, by rfl⟩ : syracuseStep 2149177 = 1611883) (by norm_num)
theorem B2865569 : Blo 1909435 2865569 := bstep (se 2 (by rfl) ⟨1074588, by rfl⟩ : syracuseStep 2865569 = 2149177) B2149177
theorem B1910379 : Blo 1909435 1910379 := bstep (se 1 (by rfl) ⟨1432784, by rfl⟩ : syracuseStep 1910379 = 2865569) B2865569
theorem B5440117 : Blo 1909435 5440117 := bbase (se 5 (by rfl) ⟨255005, by rfl⟩ : syracuseStep 5440117 = 510011) (by norm_num)
theorem B7253489 : Blo 1909435 7253489 := bstep (se 2 (by rfl) ⟨2720058, by rfl⟩ : syracuseStep 7253489 = 5440117) B5440117
theorem B4835659 : Blo 1909435 4835659 := bstep (se 1 (by rfl) ⟨3626744, by rfl⟩ : syracuseStep 4835659 = 7253489) B7253489
theorem B6447545 : Blo 1909435 6447545 := bstep (se 2 (by rfl) ⟨2417829, by rfl⟩ : syracuseStep 6447545 = 4835659) B4835659
theorem B4298363 : Blo 1909435 4298363 := bstep (se 1 (by rfl) ⟨3223772, by rfl⟩ : syracuseStep 4298363 = 6447545) B6447545
theorem B2865575 : Blo 1909435 2865575 := bstep (se 1 (by rfl) ⟨2149181, by rfl⟩ : syracuseStep 2865575 = 4298363) B4298363
theorem B1910383 : Blo 1909435 1910383 := bstep (se 1 (by rfl) ⟨1432787, by rfl⟩ : syracuseStep 1910383 = 2865575) B2865575
theorem B2865581 : Blo 1909435 2865581 := bbase (se 3 (by rfl) ⟨537296, by rfl⟩ : syracuseStep 2865581 = 1074593) (by norm_num)
theorem B1910387 : Blo 1909435 1910387 := bstep (se 1 (by rfl) ⟨1432790, by rfl⟩ : syracuseStep 1910387 = 2865581) B2865581
theorem B4298381 : Blo 1909435 4298381 := bbase (se 3 (by rfl) ⟨805946, by rfl⟩ : syracuseStep 4298381 = 1611893) (by norm_num)
theorem B2865587 : Blo 1909435 2865587 := bstep (se 1 (by rfl) ⟨2149190, by rfl⟩ : syracuseStep 2865587 = 4298381) B4298381
theorem B1910391 : Blo 1909435 1910391 := bstep (se 1 (by rfl) ⟨1432793, by rfl⟩ : syracuseStep 1910391 = 2865587) B2865587
theorem B2417845 : Blo 1909435 2417845 := bbase (se 5 (by rfl) ⟨113336, by rfl⟩ : syracuseStep 2417845 = 226673) (by norm_num)
theorem B3223793 : Blo 1909435 3223793 := bstep (se 2 (by rfl) ⟨1208922, by rfl⟩ : syracuseStep 3223793 = 2417845) B2417845
theorem B2149195 : Blo 1909435 2149195 := bstep (se 1 (by rfl) ⟨1611896, by rfl⟩ : syracuseStep 2149195 = 3223793) B3223793
theorem B2865593 : Blo 1909435 2865593 := bstep (se 2 (by rfl) ⟨1074597, by rfl⟩ : syracuseStep 2865593 = 2149195) B2149195
theorem B1910395 : Blo 1909435 1910395 := bstep (se 1 (by rfl) ⟨1432796, by rfl⟩ : syracuseStep 1910395 = 2865593) B2865593
theorem B4135789 : Blo 1909435 4135789 := bbase (se 3 (by rfl) ⟨775460, by rfl⟩ : syracuseStep 4135789 = 1550921) (by norm_num)
theorem B22057541 : Blo 1909435 22057541 := bstep (se 4 (by rfl) ⟨2067894, by rfl⟩ : syracuseStep 22057541 = 4135789) B4135789
theorem B14705027 : Blo 1909435 14705027 := bstep (se 1 (by rfl) ⟨11028770, by rfl⟩ : syracuseStep 14705027 = 22057541) B22057541
theorem B9803351 : Blo 1909435 9803351 := bstep (se 1 (by rfl) ⟨7352513, by rfl⟩ : syracuseStep 9803351 = 14705027) B14705027
theorem B6535567 : Blo 1909435 6535567 := bstep (se 1 (by rfl) ⟨4901675, by rfl⟩ : syracuseStep 6535567 = 9803351) B9803351
theorem B8714089 : Blo 1909435 8714089 := bstep (se 2 (by rfl) ⟨3267783, by rfl⟩ : syracuseStep 8714089 = 6535567) B6535567
theorem B11618785 : Blo 1909435 11618785 := bstep (se 2 (by rfl) ⟨4357044, by rfl⟩ : syracuseStep 11618785 = 8714089) B8714089
theorem B61966853 : Blo 1909435 61966853 := bstep (se 4 (by rfl) ⟨5809392, by rfl⟩ : syracuseStep 61966853 = 11618785) B11618785
theorem B41311235 : Blo 1909435 41311235 := bstep (se 1 (by rfl) ⟨30983426, by rfl⟩ : syracuseStep 41311235 = 61966853) B61966853
theorem B27540823 : Blo 1909435 27540823 := bstep (se 1 (by rfl) ⟨20655617, by rfl⟩ : syracuseStep 27540823 = 41311235) B41311235
theorem B36721097 : Blo 1909435 36721097 := bstep (se 2 (by rfl) ⟨13770411, by rfl⟩ : syracuseStep 36721097 = 27540823) B27540823
theorem B24480731 : Blo 1909435 24480731 := bstep (se 1 (by rfl) ⟨18360548, by rfl⟩ : syracuseStep 24480731 = 36721097) B36721097
theorem B16320487 : Blo 1909435 16320487 := bstep (se 1 (by rfl) ⟨12240365, by rfl⟩ : syracuseStep 16320487 = 24480731) B24480731
theorem B21760649 : Blo 1909435 21760649 := bstep (se 2 (by rfl) ⟨8160243, by rfl⟩ : syracuseStep 21760649 = 16320487) B16320487
theorem B14507099 : Blo 1909435 14507099 := bstep (se 1 (by rfl) ⟨10880324, by rfl⟩ : syracuseStep 14507099 = 21760649) B21760649
theorem B9671399 : Blo 1909435 9671399 := bstep (se 1 (by rfl) ⟨7253549, by rfl⟩ : syracuseStep 9671399 = 14507099) B14507099
theorem B6447599 : Blo 1909435 6447599 := bstep (se 1 (by rfl) ⟨4835699, by rfl⟩ : syracuseStep 6447599 = 9671399) B9671399
theorem B4298399 : Blo 1909435 4298399 := bstep (se 1 (by rfl) ⟨3223799, by rfl⟩ : syracuseStep 4298399 = 6447599) B6447599
theorem B2865599 : Blo 1909435 2865599 := bstep (se 1 (by rfl) ⟨2149199, by rfl⟩ : syracuseStep 2865599 = 4298399) B4298399
theorem B1910399 : Blo 1909435 1910399 := bstep (se 1 (by rfl) ⟨1432799, by rfl⟩ : syracuseStep 1910399 = 2865599) B2865599
theorem B2865605 : Blo 1909435 2865605 := bbase (se 4 (by rfl) ⟨268650, by rfl⟩ : syracuseStep 2865605 = 537301) (by norm_num)
theorem B1910403 : Blo 1909435 1910403 := bstep (se 1 (by rfl) ⟨1432802, by rfl⟩ : syracuseStep 1910403 = 2865605) B2865605
theorem B3223813 : Blo 1909435 3223813 := bbase (se 4 (by rfl) ⟨302232, by rfl⟩ : syracuseStep 3223813 = 604465) (by norm_num)
theorem B4298417 : Blo 1909435 4298417 := bstep (se 2 (by rfl) ⟨1611906, by rfl⟩ : syracuseStep 4298417 = 3223813) B3223813
theorem B2865611 : Blo 1909435 2865611 := bstep (se 1 (by rfl) ⟨2149208, by rfl⟩ : syracuseStep 2865611 = 4298417) B4298417
theorem B1910407 : Blo 1909435 1910407 := bstep (se 1 (by rfl) ⟨1432805, by rfl⟩ : syracuseStep 1910407 = 2865611) B2865611
theorem B2149213 : Blo 1909435 2149213 := bbase (se 3 (by rfl) ⟨402977, by rfl⟩ : syracuseStep 2149213 = 805955) (by norm_num)
theorem B2865617 : Blo 1909435 2865617 := bstep (se 2 (by rfl) ⟨1074606, by rfl⟩ : syracuseStep 2865617 = 2149213) B2149213
theorem B1910411 : Blo 1909435 1910411 := bstep (se 1 (by rfl) ⟨1432808, by rfl⟩ : syracuseStep 1910411 = 2865617) B2865617
theorem B6447653 : Blo 1909435 6447653 := bbase (se 4 (by rfl) ⟨604467, by rfl⟩ : syracuseStep 6447653 = 1208935) (by norm_num)
theorem B4298435 : Blo 1909435 4298435 := bstep (se 1 (by rfl) ⟨3223826, by rfl⟩ : syracuseStep 4298435 = 6447653) B6447653
theorem B2865623 : Blo 1909435 2865623 := bstep (se 1 (by rfl) ⟨2149217, by rfl⟩ : syracuseStep 2865623 = 4298435) B4298435
theorem B1910415 : Blo 1909435 1910415 := bstep (se 1 (by rfl) ⟨1432811, by rfl⟩ : syracuseStep 1910415 = 2865623) B2865623
theorem B2865629 : Blo 1909435 2865629 := bbase (se 3 (by rfl) ⟨537305, by rfl⟩ : syracuseStep 2865629 = 1074611) (by norm_num)
theorem B1910419 : Blo 1909435 1910419 := bstep (se 1 (by rfl) ⟨1432814, by rfl⟩ : syracuseStep 1910419 = 2865629) B2865629
theorem B4298453 : Blo 1909435 4298453 := bbase (se 7 (by rfl) ⟨50372, by rfl⟩ : syracuseStep 4298453 = 100745) (by norm_num)
theorem B2865635 : Blo 1909435 2865635 := bstep (se 1 (by rfl) ⟨2149226, by rfl⟩ : syracuseStep 2865635 = 4298453) B4298453
theorem B1910423 : Blo 1909435 1910423 := bstep (se 1 (by rfl) ⟨1432817, by rfl⟩ : syracuseStep 1910423 = 2865635) B2865635
theorem B4135853 : Blo 1909435 4135853 := bbase (se 3 (by rfl) ⟨775472, by rfl⟩ : syracuseStep 4135853 = 1550945) (by norm_num)
theorem B2757235 : Blo 1909435 2757235 := bstep (se 1 (by rfl) ⟨2067926, by rfl⟩ : syracuseStep 2757235 = 4135853) B4135853
theorem B3676313 : Blo 1909435 3676313 := bstep (se 2 (by rfl) ⟨1378617, by rfl⟩ : syracuseStep 3676313 = 2757235) B2757235
theorem B9803501 : Blo 1909435 9803501 := bstep (se 3 (by rfl) ⟨1838156, by rfl⟩ : syracuseStep 9803501 = 3676313) B3676313
theorem B6535667 : Blo 1909435 6535667 := bstep (se 1 (by rfl) ⟨4901750, by rfl⟩ : syracuseStep 6535667 = 9803501) B9803501
theorem B17428445 : Blo 1909435 17428445 := bstep (se 3 (by rfl) ⟨3267833, by rfl⟩ : syracuseStep 17428445 = 6535667) B6535667
theorem B11618963 : Blo 1909435 11618963 := bstep (se 1 (by rfl) ⟨8714222, by rfl⟩ : syracuseStep 11618963 = 17428445) B17428445
theorem B7745975 : Blo 1909435 7745975 := bstep (se 1 (by rfl) ⟨5809481, by rfl⟩ : syracuseStep 7745975 = 11618963) B11618963
theorem B5163983 : Blo 1909435 5163983 := bstep (se 1 (by rfl) ⟨3872987, by rfl⟩ : syracuseStep 5163983 = 7745975) B7745975
theorem B3442655 : Blo 1909435 3442655 := bstep (se 1 (by rfl) ⟨2581991, by rfl⟩ : syracuseStep 3442655 = 5163983) B5163983
theorem B2295103 : Blo 1909435 2295103 := bstep (se 1 (by rfl) ⟨1721327, by rfl⟩ : syracuseStep 2295103 = 3442655) B3442655
theorem B3060137 : Blo 1909435 3060137 := bstep (se 2 (by rfl) ⟨1147551, by rfl⟩ : syracuseStep 3060137 = 2295103) B2295103
theorem B8160365 : Blo 1909435 8160365 := bstep (se 3 (by rfl) ⟨1530068, by rfl⟩ : syracuseStep 8160365 = 3060137) B3060137
theorem B5440243 : Blo 1909435 5440243 := bstep (se 1 (by rfl) ⟨4080182, by rfl⟩ : syracuseStep 5440243 = 8160365) B8160365
theorem B7253657 : Blo 1909435 7253657 := bstep (se 2 (by rfl) ⟨2720121, by rfl⟩ : syracuseStep 7253657 = 5440243) B5440243
theorem B4835771 : Blo 1909435 4835771 := bstep (se 1 (by rfl) ⟨3626828, by rfl⟩ : syracuseStep 4835771 = 7253657) B7253657
theorem B3223847 : Blo 1909435 3223847 := bstep (se 1 (by rfl) ⟨2417885, by rfl⟩ : syracuseStep 3223847 = 4835771) B4835771
theorem B2149231 : Blo 1909435 2149231 := bstep (se 1 (by rfl) ⟨1611923, by rfl⟩ : syracuseStep 2149231 = 3223847) B3223847
theorem B2865641 : Blo 1909435 2865641 := bstep (se 2 (by rfl) ⟨1074615, by rfl⟩ : syracuseStep 2865641 = 2149231) B2149231
theorem B1910427 : Blo 1909435 1910427 := bstep (se 1 (by rfl) ⟨1432820, by rfl⟩ : syracuseStep 1910427 = 2865641) B2865641
theorem B2518213 : Blo 1909435 2518213 := bbase (se 4 (by rfl) ⟨236082, by rfl⟩ : syracuseStep 2518213 = 472165) (by norm_num)
theorem B3357617 : Blo 1909435 3357617 := bstep (se 2 (by rfl) ⟨1259106, by rfl⟩ : syracuseStep 3357617 = 2518213) B2518213
theorem B8953645 : Blo 1909435 8953645 := bstep (se 3 (by rfl) ⟨1678808, by rfl⟩ : syracuseStep 8953645 = 3357617) B3357617
theorem B11938193 : Blo 1909435 11938193 := bstep (se 2 (by rfl) ⟨4476822, by rfl⟩ : syracuseStep 11938193 = 8953645) B8953645
theorem B7958795 : Blo 1909435 7958795 := bstep (se 1 (by rfl) ⟨5969096, by rfl⟩ : syracuseStep 7958795 = 11938193) B11938193
theorem B21223453 : Blo 1909435 21223453 := bstep (se 3 (by rfl) ⟨3979397, by rfl⟩ : syracuseStep 21223453 = 7958795) B7958795
theorem B28297937 : Blo 1909435 28297937 := bstep (se 2 (by rfl) ⟨10611726, by rfl⟩ : syracuseStep 28297937 = 21223453) B21223453
theorem B75461165 : Blo 1909435 75461165 := bstep (se 3 (by rfl) ⟨14148968, by rfl⟩ : syracuseStep 75461165 = 28297937) B28297937
theorem B50307443 : Blo 1909435 50307443 := bstep (se 1 (by rfl) ⟨37730582, by rfl⟩ : syracuseStep 50307443 = 75461165) B75461165
theorem B33538295 : Blo 1909435 33538295 := bstep (se 1 (by rfl) ⟨25153721, by rfl⟩ : syracuseStep 33538295 = 50307443) B50307443
theorem B22358863 : Blo 1909435 22358863 := bstep (se 1 (by rfl) ⟨16769147, by rfl⟩ : syracuseStep 22358863 = 33538295) B33538295
theorem B29811817 : Blo 1909435 29811817 := bstep (se 2 (by rfl) ⟨11179431, by rfl⟩ : syracuseStep 29811817 = 22358863) B22358863
theorem B158996357 : Blo 1909435 158996357 := bstep (se 4 (by rfl) ⟨14905908, by rfl⟩ : syracuseStep 158996357 = 29811817) B29811817
theorem B105997571 : Blo 1909435 105997571 := bstep (se 1 (by rfl) ⟨79498178, by rfl⟩ : syracuseStep 105997571 = 158996357) B158996357
theorem B70665047 : Blo 1909435 70665047 := bstep (se 1 (by rfl) ⟨52998785, by rfl⟩ : syracuseStep 70665047 = 105997571) B105997571
theorem B47110031 : Blo 1909435 47110031 := bstep (se 1 (by rfl) ⟨35332523, by rfl⟩ : syracuseStep 47110031 = 70665047) B70665047
theorem B31406687 : Blo 1909435 31406687 := bstep (se 1 (by rfl) ⟨23555015, by rfl⟩ : syracuseStep 31406687 = 47110031) B47110031
theorem B20937791 : Blo 1909435 20937791 := bstep (se 1 (by rfl) ⟨15703343, by rfl⟩ : syracuseStep 20937791 = 31406687) B31406687
theorem B55834109 : Blo 1909435 55834109 := bstep (se 3 (by rfl) ⟨10468895, by rfl⟩ : syracuseStep 55834109 = 20937791) B20937791
theorem B37222739 : Blo 1909435 37222739 := bstep (se 1 (by rfl) ⟨27917054, by rfl⟩ : syracuseStep 37222739 = 55834109) B55834109
theorem B24815159 : Blo 1909435 24815159 := bstep (se 1 (by rfl) ⟨18611369, by rfl⟩ : syracuseStep 24815159 = 37222739) B37222739
theorem B16543439 : Blo 1909435 16543439 := bstep (se 1 (by rfl) ⟨12407579, by rfl⟩ : syracuseStep 16543439 = 24815159) B24815159
theorem B11028959 : Blo 1909435 11028959 := bstep (se 1 (by rfl) ⟨8271719, by rfl⟩ : syracuseStep 11028959 = 16543439) B16543439
theorem B7352639 : Blo 1909435 7352639 := bstep (se 1 (by rfl) ⟨5514479, by rfl⟩ : syracuseStep 7352639 = 11028959) B11028959
theorem B4901759 : Blo 1909435 4901759 := bstep (se 1 (by rfl) ⟨3676319, by rfl⟩ : syracuseStep 4901759 = 7352639) B7352639
theorem B3267839 : Blo 1909435 3267839 := bstep (se 1 (by rfl) ⟨2450879, by rfl⟩ : syracuseStep 3267839 = 4901759) B4901759
theorem B2178559 : Blo 1909435 2178559 := bstep (se 1 (by rfl) ⟨1633919, by rfl⟩ : syracuseStep 2178559 = 3267839) B3267839
theorem B11618981 : Blo 1909435 11618981 := bstep (se 4 (by rfl) ⟨1089279, by rfl⟩ : syracuseStep 11618981 = 2178559) B2178559
theorem B7745987 : Blo 1909435 7745987 := bstep (se 1 (by rfl) ⟨5809490, by rfl⟩ : syracuseStep 7745987 = 11618981) B11618981
theorem B20655965 : Blo 1909435 20655965 := bstep (se 3 (by rfl) ⟨3872993, by rfl⟩ : syracuseStep 20655965 = 7745987) B7745987
theorem B13770643 : Blo 1909435 13770643 := bstep (se 1 (by rfl) ⟨10327982, by rfl⟩ : syracuseStep 13770643 = 20655965) B20655965
theorem B18360857 : Blo 1909435 18360857 := bstep (se 2 (by rfl) ⟨6885321, by rfl⟩ : syracuseStep 18360857 = 13770643) B13770643
theorem B12240571 : Blo 1909435 12240571 := bstep (se 1 (by rfl) ⟨9180428, by rfl⟩ : syracuseStep 12240571 = 18360857) B18360857
theorem B16320761 : Blo 1909435 16320761 := bstep (se 2 (by rfl) ⟨6120285, by rfl⟩ : syracuseStep 16320761 = 12240571) B12240571
theorem B10880507 : Blo 1909435 10880507 := bstep (se 1 (by rfl) ⟨8160380, by rfl⟩ : syracuseStep 10880507 = 16320761) B16320761
theorem B7253671 : Blo 1909435 7253671 := bstep (se 1 (by rfl) ⟨5440253, by rfl⟩ : syracuseStep 7253671 = 10880507) B10880507
theorem B9671561 : Blo 1909435 9671561 := bstep (se 2 (by rfl) ⟨3626835, by rfl⟩ : syracuseStep 9671561 = 7253671) B7253671
theorem B6447707 : Blo 1909435 6447707 := bstep (se 1 (by rfl) ⟨4835780, by rfl⟩ : syracuseStep 6447707 = 9671561) B9671561
theorem B4298471 : Blo 1909435 4298471 := bstep (se 1 (by rfl) ⟨3223853, by rfl⟩ : syracuseStep 4298471 = 6447707) B6447707
theorem B2865647 : Blo 1909435 2865647 := bstep (se 1 (by rfl) ⟨2149235, by rfl⟩ : syracuseStep 2865647 = 4298471) B4298471
theorem B1910431 : Blo 1909435 1910431 := bstep (se 1 (by rfl) ⟨1432823, by rfl⟩ : syracuseStep 1910431 = 2865647) B2865647
theorem B2865653 : Blo 1909435 2865653 := bbase (se 5 (by rfl) ⟨134327, by rfl⟩ : syracuseStep 2865653 = 268655) (by norm_num)
theorem B1910435 : Blo 1909435 1910435 := bstep (se 1 (by rfl) ⟨1432826, by rfl⟩ : syracuseStep 1910435 = 2865653) B2865653
theorem B5440277 : Blo 1909435 5440277 := bbase (se 6 (by rfl) ⟨127506, by rfl⟩ : syracuseStep 5440277 = 255013) (by norm_num)
theorem B3626851 : Blo 1909435 3626851 := bstep (se 1 (by rfl) ⟨2720138, by rfl⟩ : syracuseStep 3626851 = 5440277) B5440277
theorem B4835801 : Blo 1909435 4835801 := bstep (se 2 (by rfl) ⟨1813425, by rfl⟩ : syracuseStep 4835801 = 3626851) B3626851
theorem B3223867 : Blo 1909435 3223867 := bstep (se 1 (by rfl) ⟨2417900, by rfl⟩ : syracuseStep 3223867 = 4835801) B4835801
theorem B4298489 : Blo 1909435 4298489 := bstep (se 2 (by rfl) ⟨1611933, by rfl⟩ : syracuseStep 4298489 = 3223867) B3223867
theorem B2865659 : Blo 1909435 2865659 := bstep (se 1 (by rfl) ⟨2149244, by rfl⟩ : syracuseStep 2865659 = 4298489) B4298489
theorem B1910439 : Blo 1909435 1910439 := bstep (se 1 (by rfl) ⟨1432829, by rfl⟩ : syracuseStep 1910439 = 2865659) B2865659
theorem B2149249 : Blo 1909435 2149249 := bbase (se 2 (by rfl) ⟨805968, by rfl⟩ : syracuseStep 2149249 = 1611937) (by norm_num)
theorem B2865665 : Blo 1909435 2865665 := bstep (se 2 (by rfl) ⟨1074624, by rfl⟩ : syracuseStep 2865665 = 2149249) B2149249
theorem B1910443 : Blo 1909435 1910443 := bstep (se 1 (by rfl) ⟨1432832, by rfl⟩ : syracuseStep 1910443 = 2865665) B2865665
theorem B4835821 : Blo 1909435 4835821 := bbase (se 3 (by rfl) ⟨906716, by rfl⟩ : syracuseStep 4835821 = 1813433) (by norm_num)
theorem B6447761 : Blo 1909435 6447761 := bstep (se 2 (by rfl) ⟨2417910, by rfl⟩ : syracuseStep 6447761 = 4835821) B4835821
theorem B4298507 : Blo 1909435 4298507 := bstep (se 1 (by rfl) ⟨3223880, by rfl⟩ : syracuseStep 4298507 = 6447761) B6447761
theorem B2865671 : Blo 1909435 2865671 := bstep (se 1 (by rfl) ⟨2149253, by rfl⟩ : syracuseStep 2865671 = 4298507) B4298507
theorem B1910447 : Blo 1909435 1910447 := bstep (se 1 (by rfl) ⟨1432835, by rfl⟩ : syracuseStep 1910447 = 2865671) B2865671
theorem B2865677 : Blo 1909435 2865677 := bbase (se 3 (by rfl) ⟨537314, by rfl⟩ : syracuseStep 2865677 = 1074629) (by norm_num)
theorem B1910451 : Blo 1909435 1910451 := bstep (se 1 (by rfl) ⟨1432838, by rfl⟩ : syracuseStep 1910451 = 2865677) B2865677
theorem B4298525 : Blo 1909435 4298525 := bbase (se 3 (by rfl) ⟨805973, by rfl⟩ : syracuseStep 4298525 = 1611947) (by norm_num)
theorem B2865683 : Blo 1909435 2865683 := bstep (se 1 (by rfl) ⟨2149262, by rfl⟩ : syracuseStep 2865683 = 4298525) B4298525
theorem B1910455 : Blo 1909435 1910455 := bstep (se 1 (by rfl) ⟨1432841, by rfl⟩ : syracuseStep 1910455 = 2865683) B2865683
theorem B3223901 : Blo 1909435 3223901 := bbase (se 3 (by rfl) ⟨604481, by rfl⟩ : syracuseStep 3223901 = 1208963) (by norm_num)
theorem B2149267 : Blo 1909435 2149267 := bstep (se 1 (by rfl) ⟨1611950, by rfl⟩ : syracuseStep 2149267 = 3223901) B3223901
theorem B2865689 : Blo 1909435 2865689 := bstep (se 2 (by rfl) ⟨1074633, by rfl⟩ : syracuseStep 2865689 = 2149267) B2149267
theorem B1910459 : Blo 1909435 1910459 := bstep (se 1 (by rfl) ⟨1432844, by rfl⟩ : syracuseStep 1910459 = 2865689) B2865689
theorem B8160517 : Blo 1909435 8160517 := bbase (se 4 (by rfl) ⟨765048, by rfl⟩ : syracuseStep 8160517 = 1530097) (by norm_num)
theorem B10880689 : Blo 1909435 10880689 := bstep (se 2 (by rfl) ⟨4080258, by rfl⟩ : syracuseStep 10880689 = 8160517) B8160517
theorem B14507585 : Blo 1909435 14507585 := bstep (se 2 (by rfl) ⟨5440344, by rfl⟩ : syracuseStep 14507585 = 10880689) B10880689
theorem B9671723 : Blo 1909435 9671723 := bstep (se 1 (by rfl) ⟨7253792, by rfl⟩ : syracuseStep 9671723 = 14507585) B14507585
theorem B6447815 : Blo 1909435 6447815 := bstep (se 1 (by rfl) ⟨4835861, by rfl⟩ : syracuseStep 6447815 = 9671723) B9671723
theorem B4298543 : Blo 1909435 4298543 := bstep (se 1 (by rfl) ⟨3223907, by rfl⟩ : syracuseStep 4298543 = 6447815) B6447815
theorem B2865695 : Blo 1909435 2865695 := bstep (se 1 (by rfl) ⟨2149271, by rfl⟩ : syracuseStep 2865695 = 4298543) B4298543
theorem B1910463 : Blo 1909435 1910463 := bstep (se 1 (by rfl) ⟨1432847, by rfl⟩ : syracuseStep 1910463 = 2865695) B2865695
theorem B2865701 : Blo 1909435 2865701 := bbase (se 4 (by rfl) ⟨268659, by rfl⟩ : syracuseStep 2865701 = 537319) (by norm_num)
theorem B1910467 : Blo 1909435 1910467 := bstep (se 1 (by rfl) ⟨1432850, by rfl⟩ : syracuseStep 1910467 = 2865701) B2865701
theorem B2417941 : Blo 1909435 2417941 := bbase (se 6 (by rfl) ⟨56670, by rfl⟩ : syracuseStep 2417941 = 113341) (by norm_num)
theorem B3223921 : Blo 1909435 3223921 := bstep (se 2 (by rfl) ⟨1208970, by rfl⟩ : syracuseStep 3223921 = 2417941) B2417941
theorem B4298561 : Blo 1909435 4298561 := bstep (se 2 (by rfl) ⟨1611960, by rfl⟩ : syracuseStep 4298561 = 3223921) B3223921
theorem B2865707 : Blo 1909435 2865707 := bstep (se 1 (by rfl) ⟨2149280, by rfl⟩ : syracuseStep 2865707 = 4298561) B4298561
theorem B1910471 : Blo 1909435 1910471 := bstep (se 1 (by rfl) ⟨1432853, by rfl⟩ : syracuseStep 1910471 = 2865707) B2865707
theorem B2149285 : Blo 1909435 2149285 := bbase (se 4 (by rfl) ⟨201495, by rfl⟩ : syracuseStep 2149285 = 402991) (by norm_num)
theorem B2865713 : Blo 1909435 2865713 := bstep (se 2 (by rfl) ⟨1074642, by rfl⟩ : syracuseStep 2865713 = 2149285) B2149285
theorem B1910475 : Blo 1909435 1910475 := bstep (se 1 (by rfl) ⟨1432856, by rfl⟩ : syracuseStep 1910475 = 2865713) B2865713
theorem B9180661 : Blo 1909435 9180661 := bbase (se 5 (by rfl) ⟨430343, by rfl⟩ : syracuseStep 9180661 = 860687) (by norm_num)
theorem B12240881 : Blo 1909435 12240881 := bstep (se 2 (by rfl) ⟨4590330, by rfl⟩ : syracuseStep 12240881 = 9180661) B9180661
theorem B8160587 : Blo 1909435 8160587 := bstep (se 1 (by rfl) ⟨6120440, by rfl⟩ : syracuseStep 8160587 = 12240881) B12240881
theorem B5440391 : Blo 1909435 5440391 := bstep (se 1 (by rfl) ⟨4080293, by rfl⟩ : syracuseStep 5440391 = 8160587) B8160587
theorem B3626927 : Blo 1909435 3626927 := bstep (se 1 (by rfl) ⟨2720195, by rfl⟩ : syracuseStep 3626927 = 5440391) B5440391
theorem B2417951 : Blo 1909435 2417951 := bstep (se 1 (by rfl) ⟨1813463, by rfl⟩ : syracuseStep 2417951 = 3626927) B3626927
theorem B6447869 : Blo 1909435 6447869 := bstep (se 3 (by rfl) ⟨1208975, by rfl⟩ : syracuseStep 6447869 = 2417951) B2417951
theorem B4298579 : Blo 1909435 4298579 := bstep (se 1 (by rfl) ⟨3223934, by rfl⟩ : syracuseStep 4298579 = 6447869) B6447869
theorem B2865719 : Blo 1909435 2865719 := bstep (se 1 (by rfl) ⟨2149289, by rfl⟩ : syracuseStep 2865719 = 4298579) B4298579
theorem B1910479 : Blo 1909435 1910479 := bstep (se 1 (by rfl) ⟨1432859, by rfl⟩ : syracuseStep 1910479 = 2865719) B2865719
theorem B2865725 : Blo 1909435 2865725 := bbase (se 3 (by rfl) ⟨537323, by rfl⟩ : syracuseStep 2865725 = 1074647) (by norm_num)
theorem B1910483 : Blo 1909435 1910483 := bstep (se 1 (by rfl) ⟨1432862, by rfl⟩ : syracuseStep 1910483 = 2865725) B2865725
theorem B4298597 : Blo 1909435 4298597 := bbase (se 4 (by rfl) ⟨402993, by rfl⟩ : syracuseStep 4298597 = 805987) (by norm_num)
theorem B2865731 : Blo 1909435 2865731 := bstep (se 1 (by rfl) ⟨2149298, by rfl⟩ : syracuseStep 2865731 = 4298597) B4298597
theorem B1910487 : Blo 1909435 1910487 := bstep (se 1 (by rfl) ⟨1432865, by rfl⟩ : syracuseStep 1910487 = 2865731) B2865731
theorem B4835933 : Blo 1909435 4835933 := bbase (se 3 (by rfl) ⟨906737, by rfl⟩ : syracuseStep 4835933 = 1813475) (by norm_num)
theorem B3223955 : Blo 1909435 3223955 := bstep (se 1 (by rfl) ⟨2417966, by rfl⟩ : syracuseStep 3223955 = 4835933) B4835933
theorem B2149303 : Blo 1909435 2149303 := bstep (se 1 (by rfl) ⟨1611977, by rfl⟩ : syracuseStep 2149303 = 3223955) B3223955
theorem B2865737 : Blo 1909435 2865737 := bstep (se 2 (by rfl) ⟨1074651, by rfl⟩ : syracuseStep 2865737 = 2149303) B2149303
theorem B1910491 : Blo 1909435 1910491 := bstep (se 1 (by rfl) ⟨1432868, by rfl⟩ : syracuseStep 1910491 = 2865737) B2865737
theorem B3626957 : Blo 1909435 3626957 := bbase (se 3 (by rfl) ⟨680054, by rfl⟩ : syracuseStep 3626957 = 1360109) (by norm_num)
theorem B9671885 : Blo 1909435 9671885 := bstep (se 3 (by rfl) ⟨1813478, by rfl⟩ : syracuseStep 9671885 = 3626957) B3626957
theorem B6447923 : Blo 1909435 6447923 := bstep (se 1 (by rfl) ⟨4835942, by rfl⟩ : syracuseStep 6447923 = 9671885) B9671885
theorem B4298615 : Blo 1909435 4298615 := bstep (se 1 (by rfl) ⟨3223961, by rfl⟩ : syracuseStep 4298615 = 6447923) B6447923
theorem B2865743 : Blo 1909435 2865743 := bstep (se 1 (by rfl) ⟨2149307, by rfl⟩ : syracuseStep 2865743 = 4298615) B4298615
theorem B1910495 : Blo 1909435 1910495 := bstep (se 1 (by rfl) ⟨1432871, by rfl⟩ : syracuseStep 1910495 = 2865743) B2865743
theorem B2865749 : Blo 1909435 2865749 := bbase (se 8 (by rfl) ⟨16791, by rfl⟩ : syracuseStep 2865749 = 33583) (by norm_num)
theorem B1910499 : Blo 1909435 1910499 := bstep (se 1 (by rfl) ⟨1432874, by rfl⟩ : syracuseStep 1910499 = 2865749) B2865749
theorem B6120517 : Blo 1909435 6120517 := bbase (se 4 (by rfl) ⟨573798, by rfl⟩ : syracuseStep 6120517 = 1147597) (by norm_num)
theorem B8160689 : Blo 1909435 8160689 := bstep (se 2 (by rfl) ⟨3060258, by rfl⟩ : syracuseStep 8160689 = 6120517) B6120517
theorem B5440459 : Blo 1909435 5440459 := bstep (se 1 (by rfl) ⟨4080344, by rfl⟩ : syracuseStep 5440459 = 8160689) B8160689
theorem B7253945 : Blo 1909435 7253945 := bstep (se 2 (by rfl) ⟨2720229, by rfl⟩ : syracuseStep 7253945 = 5440459) B5440459
theorem B4835963 : Blo 1909435 4835963 := bstep (se 1 (by rfl) ⟨3626972, by rfl⟩ : syracuseStep 4835963 = 7253945) B7253945
theorem B3223975 : Blo 1909435 3223975 := bstep (se 1 (by rfl) ⟨2417981, by rfl⟩ : syracuseStep 3223975 = 4835963) B4835963
theorem B4298633 : Blo 1909435 4298633 := bstep (se 2 (by rfl) ⟨1611987, by rfl⟩ : syracuseStep 4298633 = 3223975) B3223975
theorem B2865755 : Blo 1909435 2865755 := bstep (se 1 (by rfl) ⟨2149316, by rfl⟩ : syracuseStep 2865755 = 4298633) B4298633
theorem B1910503 : Blo 1909435 1910503 := bstep (se 1 (by rfl) ⟨1432877, by rfl⟩ : syracuseStep 1910503 = 2865755) B2865755
theorem B2149321 : Blo 1909435 2149321 := bbase (se 2 (by rfl) ⟨805995, by rfl⟩ : syracuseStep 2149321 = 1611991) (by norm_num)
theorem B2865761 : Blo 1909435 2865761 := bstep (se 2 (by rfl) ⟨1074660, by rfl⟩ : syracuseStep 2865761 = 2149321) B2149321
theorem B1910507 : Blo 1909435 1910507 := bstep (se 1 (by rfl) ⟨1432880, by rfl⟩ : syracuseStep 1910507 = 2865761) B2865761
theorem B1963001 : Blo 1909435 1963001 := bbase (se 2 (by rfl) ⟨736125, by rfl⟩ : syracuseStep 1963001 = 1472251) (by norm_num)
theorem B5234669 : Blo 1909435 5234669 := bstep (se 3 (by rfl) ⟨981500, by rfl⟩ : syracuseStep 5234669 = 1963001) B1963001
theorem B3489779 : Blo 1909435 3489779 := bstep (se 1 (by rfl) ⟨2617334, by rfl⟩ : syracuseStep 3489779 = 5234669) B5234669
theorem B2326519 : Blo 1909435 2326519 := bstep (se 1 (by rfl) ⟨1744889, by rfl⟩ : syracuseStep 2326519 = 3489779) B3489779
theorem B3102025 : Blo 1909435 3102025 := bstep (se 2 (by rfl) ⟨1163259, by rfl⟩ : syracuseStep 3102025 = 2326519) B2326519
theorem B4136033 : Blo 1909435 4136033 := bstep (se 2 (by rfl) ⟨1551012, by rfl⟩ : syracuseStep 4136033 = 3102025) B3102025
theorem B11029421 : Blo 1909435 11029421 := bstep (se 3 (by rfl) ⟨2068016, by rfl⟩ : syracuseStep 11029421 = 4136033) B4136033
theorem B7352947 : Blo 1909435 7352947 := bstep (se 1 (by rfl) ⟨5514710, by rfl⟩ : syracuseStep 7352947 = 11029421) B11029421
theorem B9803929 : Blo 1909435 9803929 := bstep (se 2 (by rfl) ⟨3676473, by rfl⟩ : syracuseStep 9803929 = 7352947) B7352947
theorem B13071905 : Blo 1909435 13071905 := bstep (se 2 (by rfl) ⟨4901964, by rfl⟩ : syracuseStep 13071905 = 9803929) B9803929
theorem B8714603 : Blo 1909435 8714603 := bstep (se 1 (by rfl) ⟨6535952, by rfl⟩ : syracuseStep 8714603 = 13071905) B13071905
theorem B5809735 : Blo 1909435 5809735 := bstep (se 1 (by rfl) ⟨4357301, by rfl⟩ : syracuseStep 5809735 = 8714603) B8714603
theorem B7746313 : Blo 1909435 7746313 := bstep (se 2 (by rfl) ⟨2904867, by rfl⟩ : syracuseStep 7746313 = 5809735) B5809735
theorem B10328417 : Blo 1909435 10328417 := bstep (se 2 (by rfl) ⟨3873156, by rfl⟩ : syracuseStep 10328417 = 7746313) B7746313
theorem B6885611 : Blo 1909435 6885611 := bstep (se 1 (by rfl) ⟨5164208, by rfl⟩ : syracuseStep 6885611 = 10328417) B10328417
theorem B4590407 : Blo 1909435 4590407 := bstep (se 1 (by rfl) ⟨3442805, by rfl⟩ : syracuseStep 4590407 = 6885611) B6885611
theorem B3060271 : Blo 1909435 3060271 := bstep (se 1 (by rfl) ⟨2295203, by rfl⟩ : syracuseStep 3060271 = 4590407) B4590407
theorem B16321445 : Blo 1909435 16321445 := bstep (se 4 (by rfl) ⟨1530135, by rfl⟩ : syracuseStep 16321445 = 3060271) B3060271
theorem B10880963 : Blo 1909435 10880963 := bstep (se 1 (by rfl) ⟨8160722, by rfl⟩ : syracuseStep 10880963 = 16321445) B16321445
theorem B7253975 : Blo 1909435 7253975 := bstep (se 1 (by rfl) ⟨5440481, by rfl⟩ : syracuseStep 7253975 = 10880963) B10880963
theorem B4835983 : Blo 1909435 4835983 := bstep (se 1 (by rfl) ⟨3626987, by rfl⟩ : syracuseStep 4835983 = 7253975) B7253975
theorem B6447977 : Blo 1909435 6447977 := bstep (se 2 (by rfl) ⟨2417991, by rfl⟩ : syracuseStep 6447977 = 4835983) B4835983
theorem B4298651 : Blo 1909435 4298651 := bstep (se 1 (by rfl) ⟨3223988, by rfl⟩ : syracuseStep 4298651 = 6447977) B6447977
theorem B2865767 : Blo 1909435 2865767 := bstep (se 1 (by rfl) ⟨2149325, by rfl⟩ : syracuseStep 2865767 = 4298651) B4298651
theorem B1910511 : Blo 1909435 1910511 := bstep (se 1 (by rfl) ⟨1432883, by rfl⟩ : syracuseStep 1910511 = 2865767) B2865767
theorem B2865773 : Blo 1909435 2865773 := bbase (se 3 (by rfl) ⟨537332, by rfl⟩ : syracuseStep 2865773 = 1074665) (by norm_num)
theorem B1910515 : Blo 1909435 1910515 := bstep (se 1 (by rfl) ⟨1432886, by rfl⟩ : syracuseStep 1910515 = 2865773) B2865773
theorem B4298669 : Blo 1909435 4298669 := bbase (se 3 (by rfl) ⟨806000, by rfl⟩ : syracuseStep 4298669 = 1612001) (by norm_num)
theorem B2865779 : Blo 1909435 2865779 := bstep (se 1 (by rfl) ⟨2149334, by rfl⟩ : syracuseStep 2865779 = 4298669) B4298669
theorem B1910519 : Blo 1909435 1910519 := bstep (se 1 (by rfl) ⟨1432889, by rfl⟩ : syracuseStep 1910519 = 2865779) B2865779
theorem B5440517 : Blo 1909435 5440517 := bbase (se 4 (by rfl) ⟨510048, by rfl⟩ : syracuseStep 5440517 = 1020097) (by norm_num)
theorem B3627011 : Blo 1909435 3627011 := bstep (se 1 (by rfl) ⟨2720258, by rfl⟩ : syracuseStep 3627011 = 5440517) B5440517
theorem B2418007 : Blo 1909435 2418007 := bstep (se 1 (by rfl) ⟨1813505, by rfl⟩ : syracuseStep 2418007 = 3627011) B3627011
theorem B3224009 : Blo 1909435 3224009 := bstep (se 2 (by rfl) ⟨1209003, by rfl⟩ : syracuseStep 3224009 = 2418007) B2418007
theorem B2149339 : Blo 1909435 2149339 := bstep (se 1 (by rfl) ⟨1612004, by rfl⟩ : syracuseStep 2149339 = 3224009) B3224009
theorem B2865785 : Blo 1909435 2865785 := bstep (se 2 (by rfl) ⟨1074669, by rfl⟩ : syracuseStep 2865785 = 2149339) B2149339
theorem B1910523 : Blo 1909435 1910523 := bstep (se 1 (by rfl) ⟨1432892, by rfl⟩ : syracuseStep 1910523 = 2865785) B2865785
theorem B10328501 : Blo 1909435 10328501 := bbase (se 5 (by rfl) ⟨484148, by rfl⟩ : syracuseStep 10328501 = 968297) (by norm_num)
theorem B6885667 : Blo 1909435 6885667 := bstep (se 1 (by rfl) ⟨5164250, by rfl⟩ : syracuseStep 6885667 = 10328501) B10328501
theorem B36723557 : Blo 1909435 36723557 := bstep (se 4 (by rfl) ⟨3442833, by rfl⟩ : syracuseStep 36723557 = 6885667) B6885667
theorem B24482371 : Blo 1909435 24482371 := bstep (se 1 (by rfl) ⟨18361778, by rfl⟩ : syracuseStep 24482371 = 36723557) B36723557
theorem B32643161 : Blo 1909435 32643161 := bstep (se 2 (by rfl) ⟨12241185, by rfl⟩ : syracuseStep 32643161 = 24482371) B24482371
theorem B21762107 : Blo 1909435 21762107 := bstep (se 1 (by rfl) ⟨16321580, by rfl⟩ : syracuseStep 21762107 = 32643161) B32643161
theorem B14508071 : Blo 1909435 14508071 := bstep (se 1 (by rfl) ⟨10881053, by rfl⟩ : syracuseStep 14508071 = 21762107) B21762107
theorem B9672047 : Blo 1909435 9672047 := bstep (se 1 (by rfl) ⟨7254035, by rfl⟩ : syracuseStep 9672047 = 14508071) B14508071
theorem B6448031 : Blo 1909435 6448031 := bstep (se 1 (by rfl) ⟨4836023, by rfl⟩ : syracuseStep 6448031 = 9672047) B9672047
theorem B4298687 : Blo 1909435 4298687 := bstep (se 1 (by rfl) ⟨3224015, by rfl⟩ : syracuseStep 4298687 = 6448031) B6448031
theorem B2865791 : Blo 1909435 2865791 := bstep (se 1 (by rfl) ⟨2149343, by rfl⟩ : syracuseStep 2865791 = 4298687) B4298687
theorem B1910527 : Blo 1909435 1910527 := bstep (se 1 (by rfl) ⟨1432895, by rfl⟩ : syracuseStep 1910527 = 2865791) B2865791
theorem B2865797 : Blo 1909435 2865797 := bbase (se 4 (by rfl) ⟨268668, by rfl⟩ : syracuseStep 2865797 = 537337) (by norm_num)
theorem B1910531 : Blo 1909435 1910531 := bstep (se 1 (by rfl) ⟨1432898, by rfl⟩ : syracuseStep 1910531 = 2865797) B2865797
theorem B3224029 : Blo 1909435 3224029 := bbase (se 3 (by rfl) ⟨604505, by rfl⟩ : syracuseStep 3224029 = 1209011) (by norm_num)
theorem B4298705 : Blo 1909435 4298705 := bstep (se 2 (by rfl) ⟨1612014, by rfl⟩ : syracuseStep 4298705 = 3224029) B3224029
theorem B2865803 : Blo 1909435 2865803 := bstep (se 1 (by rfl) ⟨2149352, by rfl⟩ : syracuseStep 2865803 = 4298705) B4298705
theorem B1910535 : Blo 1909435 1910535 := bstep (se 1 (by rfl) ⟨1432901, by rfl⟩ : syracuseStep 1910535 = 2865803) B2865803
theorem B2149357 : Blo 1909435 2149357 := bbase (se 3 (by rfl) ⟨403004, by rfl⟩ : syracuseStep 2149357 = 806009) (by norm_num)
theorem B2865809 : Blo 1909435 2865809 := bstep (se 2 (by rfl) ⟨1074678, by rfl⟩ : syracuseStep 2865809 = 2149357) B2149357
theorem B1910539 : Blo 1909435 1910539 := bstep (se 1 (by rfl) ⟨1432904, by rfl⟩ : syracuseStep 1910539 = 2865809) B2865809
theorem B6448085 : Blo 1909435 6448085 := bbase (se 7 (by rfl) ⟨75563, by rfl⟩ : syracuseStep 6448085 = 151127) (by norm_num)
theorem B4298723 : Blo 1909435 4298723 := bstep (se 1 (by rfl) ⟨3224042, by rfl⟩ : syracuseStep 4298723 = 6448085) B6448085
theorem B2865815 : Blo 1909435 2865815 := bstep (se 1 (by rfl) ⟨2149361, by rfl⟩ : syracuseStep 2865815 = 4298723) B4298723
theorem B1910543 : Blo 1909435 1910543 := bstep (se 1 (by rfl) ⟨1432907, by rfl⟩ : syracuseStep 1910543 = 2865815) B2865815
theorem B2865821 : Blo 1909435 2865821 := bbase (se 3 (by rfl) ⟨537341, by rfl⟩ : syracuseStep 2865821 = 1074683) (by norm_num)
theorem B1910547 : Blo 1909435 1910547 := bstep (se 1 (by rfl) ⟨1432910, by rfl⟩ : syracuseStep 1910547 = 2865821) B2865821
theorem B4298741 : Blo 1909435 4298741 := bbase (se 5 (by rfl) ⟨201503, by rfl⟩ : syracuseStep 4298741 = 403007) (by norm_num)
theorem B2865827 : Blo 1909435 2865827 := bstep (se 1 (by rfl) ⟨2149370, by rfl⟩ : syracuseStep 2865827 = 4298741) B4298741
theorem B1910551 : Blo 1909435 1910551 := bstep (se 1 (by rfl) ⟨1432913, by rfl⟩ : syracuseStep 1910551 = 2865827) B2865827
theorem B61971925 : Blo 1909435 61971925 := bbase (se 7 (by rfl) ⟨726233, by rfl⟩ : syracuseStep 61971925 = 1452467) (by norm_num)
theorem B82629233 : Blo 1909435 82629233 := bstep (se 2 (by rfl) ⟨30985962, by rfl⟩ : syracuseStep 82629233 = 61971925) B61971925
theorem B55086155 : Blo 1909435 55086155 := bstep (se 1 (by rfl) ⟨41314616, by rfl⟩ : syracuseStep 55086155 = 82629233) B82629233
theorem B36724103 : Blo 1909435 36724103 := bstep (se 1 (by rfl) ⟨27543077, by rfl⟩ : syracuseStep 36724103 = 55086155) B55086155
theorem B24482735 : Blo 1909435 24482735 := bstep (se 1 (by rfl) ⟨18362051, by rfl⟩ : syracuseStep 24482735 = 36724103) B36724103
theorem B16321823 : Blo 1909435 16321823 := bstep (se 1 (by rfl) ⟨12241367, by rfl⟩ : syracuseStep 16321823 = 24482735) B24482735
theorem B10881215 : Blo 1909435 10881215 := bstep (se 1 (by rfl) ⟨8160911, by rfl⟩ : syracuseStep 10881215 = 16321823) B16321823
theorem B7254143 : Blo 1909435 7254143 := bstep (se 1 (by rfl) ⟨5440607, by rfl⟩ : syracuseStep 7254143 = 10881215) B10881215
theorem B4836095 : Blo 1909435 4836095 := bstep (se 1 (by rfl) ⟨3627071, by rfl⟩ : syracuseStep 4836095 = 7254143) B7254143
theorem B3224063 : Blo 1909435 3224063 := bstep (se 1 (by rfl) ⟨2418047, by rfl⟩ : syracuseStep 3224063 = 4836095) B4836095
theorem B2149375 : Blo 1909435 2149375 := bstep (se 1 (by rfl) ⟨1612031, by rfl⟩ : syracuseStep 2149375 = 3224063) B3224063
theorem B2865833 : Blo 1909435 2865833 := bstep (se 2 (by rfl) ⟨1074687, by rfl⟩ : syracuseStep 2865833 = 2149375) B2149375
theorem B1910555 : Blo 1909435 1910555 := bstep (se 1 (by rfl) ⟨1432916, by rfl⟩ : syracuseStep 1910555 = 2865833) B2865833
theorem B2720309 : Blo 1909435 2720309 := bbase (se 5 (by rfl) ⟨127514, by rfl⟩ : syracuseStep 2720309 = 255029) (by norm_num)
theorem B7254157 : Blo 1909435 7254157 := bstep (se 3 (by rfl) ⟨1360154, by rfl⟩ : syracuseStep 7254157 = 2720309) B2720309
theorem B9672209 : Blo 1909435 9672209 := bstep (se 2 (by rfl) ⟨3627078, by rfl⟩ : syracuseStep 9672209 = 7254157) B7254157
theorem B6448139 : Blo 1909435 6448139 := bstep (se 1 (by rfl) ⟨4836104, by rfl⟩ : syracuseStep 6448139 = 9672209) B9672209
theorem B4298759 : Blo 1909435 4298759 := bstep (se 1 (by rfl) ⟨3224069, by rfl⟩ : syracuseStep 4298759 = 6448139) B6448139
theorem B2865839 : Blo 1909435 2865839 := bstep (se 1 (by rfl) ⟨2149379, by rfl⟩ : syracuseStep 2865839 = 4298759) B4298759
theorem B1910559 : Blo 1909435 1910559 := bstep (se 1 (by rfl) ⟨1432919, by rfl⟩ : syracuseStep 1910559 = 2865839) B2865839
theorem B2865845 : Blo 1909435 2865845 := bbase (se 5 (by rfl) ⟨134336, by rfl⟩ : syracuseStep 2865845 = 268673) (by norm_num)
theorem B1910563 : Blo 1909435 1910563 := bstep (se 1 (by rfl) ⟨1432922, by rfl⟩ : syracuseStep 1910563 = 2865845) B2865845
theorem B4836125 : Blo 1909435 4836125 := bbase (se 3 (by rfl) ⟨906773, by rfl⟩ : syracuseStep 4836125 = 1813547) (by norm_num)
theorem B3224083 : Blo 1909435 3224083 := bstep (se 1 (by rfl) ⟨2418062, by rfl⟩ : syracuseStep 3224083 = 4836125) B4836125
theorem B4298777 : Blo 1909435 4298777 := bstep (se 2 (by rfl) ⟨1612041, by rfl⟩ : syracuseStep 4298777 = 3224083) B3224083
theorem B2865851 : Blo 1909435 2865851 := bstep (se 1 (by rfl) ⟨2149388, by rfl⟩ : syracuseStep 2865851 = 4298777) B4298777
theorem B1910567 : Blo 1909435 1910567 := bstep (se 1 (by rfl) ⟨1432925, by rfl⟩ : syracuseStep 1910567 = 2865851) B2865851
theorem B2149393 : Blo 1909435 2149393 := bbase (se 2 (by rfl) ⟨806022, by rfl⟩ : syracuseStep 2149393 = 1612045) (by norm_num)
theorem B2865857 : Blo 1909435 2865857 := bstep (se 2 (by rfl) ⟨1074696, by rfl⟩ : syracuseStep 2865857 = 2149393) B2149393
theorem B1910571 : Blo 1909435 1910571 := bstep (se 1 (by rfl) ⟨1432928, by rfl⟩ : syracuseStep 1910571 = 2865857) B2865857
theorem B3627109 : Blo 1909435 3627109 := bbase (se 4 (by rfl) ⟨340041, by rfl⟩ : syracuseStep 3627109 = 680083) (by norm_num)
theorem B4836145 : Blo 1909435 4836145 := bstep (se 2 (by rfl) ⟨1813554, by rfl⟩ : syracuseStep 4836145 = 3627109) B3627109
theorem B6448193 : Blo 1909435 6448193 := bstep (se 2 (by rfl) ⟨2418072, by rfl⟩ : syracuseStep 6448193 = 4836145) B4836145
theorem B4298795 : Blo 1909435 4298795 := bstep (se 1 (by rfl) ⟨3224096, by rfl⟩ : syracuseStep 4298795 = 6448193) B6448193
theorem B2865863 : Blo 1909435 2865863 := bstep (se 1 (by rfl) ⟨2149397, by rfl⟩ : syracuseStep 2865863 = 4298795) B4298795
theorem B1910575 : Blo 1909435 1910575 := bstep (se 1 (by rfl) ⟨1432931, by rfl⟩ : syracuseStep 1910575 = 2865863) B2865863
theorem B2865869 : Blo 1909435 2865869 := bbase (se 3 (by rfl) ⟨537350, by rfl⟩ : syracuseStep 2865869 = 1074701) (by norm_num)
theorem B1910579 : Blo 1909435 1910579 := bstep (se 1 (by rfl) ⟨1432934, by rfl⟩ : syracuseStep 1910579 = 2865869) B2865869
theorem B4298813 : Blo 1909435 4298813 := bbase (se 3 (by rfl) ⟨806027, by rfl⟩ : syracuseStep 4298813 = 1612055) (by norm_num)
theorem B2865875 : Blo 1909435 2865875 := bstep (se 1 (by rfl) ⟨2149406, by rfl⟩ : syracuseStep 2865875 = 4298813) B4298813
theorem B1910583 : Blo 1909435 1910583 := bstep (se 1 (by rfl) ⟨1432937, by rfl⟩ : syracuseStep 1910583 = 2865875) B2865875
theorem B3224117 : Blo 1909435 3224117 := bbase (se 5 (by rfl) ⟨151130, by rfl⟩ : syracuseStep 3224117 = 302261) (by norm_num)
theorem B2149411 : Blo 1909435 2149411 := bstep (se 1 (by rfl) ⟨1612058, by rfl⟩ : syracuseStep 2149411 = 3224117) B3224117
theorem B2865881 : Blo 1909435 2865881 := bstep (se 2 (by rfl) ⟨1074705, by rfl⟩ : syracuseStep 2865881 = 2149411) B2149411
theorem B1910587 : Blo 1909435 1910587 := bstep (se 1 (by rfl) ⟨1432940, by rfl⟩ : syracuseStep 1910587 = 2865881) B2865881
theorem B5440709 : Blo 1909435 5440709 := bbase (se 4 (by rfl) ⟨510066, by rfl⟩ : syracuseStep 5440709 = 1020133) (by norm_num)
theorem B14508557 : Blo 1909435 14508557 := bstep (se 3 (by rfl) ⟨2720354, by rfl⟩ : syracuseStep 14508557 = 5440709) B5440709
theorem B9672371 : Blo 1909435 9672371 := bstep (se 1 (by rfl) ⟨7254278, by rfl⟩ : syracuseStep 9672371 = 14508557) B14508557
theorem B6448247 : Blo 1909435 6448247 := bstep (se 1 (by rfl) ⟨4836185, by rfl⟩ : syracuseStep 6448247 = 9672371) B9672371
theorem B4298831 : Blo 1909435 4298831 := bstep (se 1 (by rfl) ⟨3224123, by rfl⟩ : syracuseStep 4298831 = 6448247) B6448247
theorem B2865887 : Blo 1909435 2865887 := bstep (se 1 (by rfl) ⟨2149415, by rfl⟩ : syracuseStep 2865887 = 4298831) B4298831
theorem B1910591 : Blo 1909435 1910591 := bstep (se 1 (by rfl) ⟨1432943, by rfl⟩ : syracuseStep 1910591 = 2865887) B2865887
theorem B2865893 : Blo 1909435 2865893 := bbase (se 4 (by rfl) ⟨268677, by rfl⟩ : syracuseStep 2865893 = 537355) (by norm_num)
theorem B1910595 : Blo 1909435 1910595 := bstep (se 1 (by rfl) ⟨1432946, by rfl⟩ : syracuseStep 1910595 = 2865893) B2865893
theorem B3060413 : Blo 1909435 3060413 := bbase (se 3 (by rfl) ⟨573827, by rfl⟩ : syracuseStep 3060413 = 1147655) (by norm_num)
theorem B2040275 : Blo 1909435 2040275 := bstep (se 1 (by rfl) ⟨1530206, by rfl⟩ : syracuseStep 2040275 = 3060413) B3060413
theorem B5440733 : Blo 1909435 5440733 := bstep (se 3 (by rfl) ⟨1020137, by rfl⟩ : syracuseStep 5440733 = 2040275) B2040275
theorem B3627155 : Blo 1909435 3627155 := bstep (se 1 (by rfl) ⟨2720366, by rfl⟩ : syracuseStep 3627155 = 5440733) B5440733
theorem B2418103 : Blo 1909435 2418103 := bstep (se 1 (by rfl) ⟨1813577, by rfl⟩ : syracuseStep 2418103 = 3627155) B3627155
theorem B3224137 : Blo 1909435 3224137 := bstep (se 2 (by rfl) ⟨1209051, by rfl⟩ : syracuseStep 3224137 = 2418103) B2418103
theorem B4298849 : Blo 1909435 4298849 := bstep (se 2 (by rfl) ⟨1612068, by rfl⟩ : syracuseStep 4298849 = 3224137) B3224137
theorem B2865899 : Blo 1909435 2865899 := bstep (se 1 (by rfl) ⟨2149424, by rfl⟩ : syracuseStep 2865899 = 4298849) B4298849
theorem B1910599 : Blo 1909435 1910599 := bstep (se 1 (by rfl) ⟨1432949, by rfl⟩ : syracuseStep 1910599 = 2865899) B2865899
theorem B2149429 : Blo 1909435 2149429 := bbase (se 5 (by rfl) ⟨100754, by rfl⟩ : syracuseStep 2149429 = 201509) (by norm_num)
theorem B2865905 : Blo 1909435 2865905 := bstep (se 2 (by rfl) ⟨1074714, by rfl⟩ : syracuseStep 2865905 = 2149429) B2149429
theorem B1910603 : Blo 1909435 1910603 := bstep (se 1 (by rfl) ⟨1432952, by rfl⟩ : syracuseStep 1910603 = 2865905) B2865905
theorem B2418113 : Blo 1909435 2418113 := bbase (se 2 (by rfl) ⟨906792, by rfl⟩ : syracuseStep 2418113 = 1813585) (by norm_num)
theorem B6448301 : Blo 1909435 6448301 := bstep (se 3 (by rfl) ⟨1209056, by rfl⟩ : syracuseStep 6448301 = 2418113) B2418113
theorem B4298867 : Blo 1909435 4298867 := bstep (se 1 (by rfl) ⟨3224150, by rfl⟩ : syracuseStep 4298867 = 6448301) B6448301
theorem B2865911 : Blo 1909435 2865911 := bstep (se 1 (by rfl) ⟨2149433, by rfl⟩ : syracuseStep 2865911 = 4298867) B4298867
theorem B1910607 : Blo 1909435 1910607 := bstep (se 1 (by rfl) ⟨1432955, by rfl⟩ : syracuseStep 1910607 = 2865911) B2865911
theorem B2865917 : Blo 1909435 2865917 := bbase (se 3 (by rfl) ⟨537359, by rfl⟩ : syracuseStep 2865917 = 1074719) (by norm_num)
theorem B1910611 : Blo 1909435 1910611 := bstep (se 1 (by rfl) ⟨1432958, by rfl⟩ : syracuseStep 1910611 = 2865917) B2865917
theorem B4298885 : Blo 1909435 4298885 := bbase (se 4 (by rfl) ⟨403020, by rfl⟩ : syracuseStep 4298885 = 806041) (by norm_num)
theorem B2865923 : Blo 1909435 2865923 := bstep (se 1 (by rfl) ⟨2149442, by rfl⟩ : syracuseStep 2865923 = 4298885) B4298885
theorem B1910615 : Blo 1909435 1910615 := bstep (se 1 (by rfl) ⟨1432961, by rfl⟩ : syracuseStep 1910615 = 2865923) B2865923
theorem B3060445 : Blo 1909435 3060445 := bbase (se 3 (by rfl) ⟨573833, by rfl⟩ : syracuseStep 3060445 = 1147667) (by norm_num)
theorem B4080593 : Blo 1909435 4080593 := bstep (se 2 (by rfl) ⟨1530222, by rfl⟩ : syracuseStep 4080593 = 3060445) B3060445
theorem B2720395 : Blo 1909435 2720395 := bstep (se 1 (by rfl) ⟨2040296, by rfl⟩ : syracuseStep 2720395 = 4080593) B4080593
theorem B3627193 : Blo 1909435 3627193 := bstep (se 2 (by rfl) ⟨1360197, by rfl⟩ : syracuseStep 3627193 = 2720395) B2720395
theorem B4836257 : Blo 1909435 4836257 := bstep (se 2 (by rfl) ⟨1813596, by rfl⟩ : syracuseStep 4836257 = 3627193) B3627193
theorem B3224171 : Blo 1909435 3224171 := bstep (se 1 (by rfl) ⟨2418128, by rfl⟩ : syracuseStep 3224171 = 4836257) B4836257
theorem B2149447 : Blo 1909435 2149447 := bstep (se 1 (by rfl) ⟨1612085, by rfl⟩ : syracuseStep 2149447 = 3224171) B3224171
theorem B2865929 : Blo 1909435 2865929 := bstep (se 2 (by rfl) ⟨1074723, by rfl⟩ : syracuseStep 2865929 = 2149447) B2149447
theorem B1910619 : Blo 1909435 1910619 := bstep (se 1 (by rfl) ⟨1432964, by rfl⟩ : syracuseStep 1910619 = 2865929) B2865929
theorem B9672533 : Blo 1909435 9672533 := bbase (se 9 (by rfl) ⟨28337, by rfl⟩ : syracuseStep 9672533 = 56675) (by norm_num)
theorem B6448355 : Blo 1909435 6448355 := bstep (se 1 (by rfl) ⟨4836266, by rfl⟩ : syracuseStep 6448355 = 9672533) B9672533
theorem B4298903 : Blo 1909435 4298903 := bstep (se 1 (by rfl) ⟨3224177, by rfl⟩ : syracuseStep 4298903 = 6448355) B6448355
theorem B2865935 : Blo 1909435 2865935 := bstep (se 1 (by rfl) ⟨2149451, by rfl⟩ : syracuseStep 2865935 = 4298903) B4298903
theorem B1910623 : Blo 1909435 1910623 := bstep (se 1 (by rfl) ⟨1432967, by rfl⟩ : syracuseStep 1910623 = 2865935) B2865935
theorem B2865941 : Blo 1909435 2865941 := bbase (se 6 (by rfl) ⟨67170, by rfl⟩ : syracuseStep 2865941 = 134341) (by norm_num)
theorem B1910627 : Blo 1909435 1910627 := bstep (se 1 (by rfl) ⟨1432970, by rfl⟩ : syracuseStep 1910627 = 2865941) B2865941
theorem B2944685 : Blo 1909435 2944685 := bbase (se 3 (by rfl) ⟨552128, by rfl⟩ : syracuseStep 2944685 = 1104257) (by norm_num)
theorem B1963123 : Blo 1909435 1963123 := bstep (se 1 (by rfl) ⟨1472342, by rfl⟩ : syracuseStep 1963123 = 2944685) B2944685
theorem B10469989 : Blo 1909435 10469989 := bstep (se 4 (by rfl) ⟨981561, by rfl⟩ : syracuseStep 10469989 = 1963123) B1963123
theorem B55839941 : Blo 1909435 55839941 := bstep (se 4 (by rfl) ⟨5234994, by rfl⟩ : syracuseStep 55839941 = 10469989) B10469989
theorem B37226627 : Blo 1909435 37226627 := bstep (se 1 (by rfl) ⟨27919970, by rfl⟩ : syracuseStep 37226627 = 55839941) B55839941
theorem B24817751 : Blo 1909435 24817751 := bstep (se 1 (by rfl) ⟨18613313, by rfl⟩ : syracuseStep 24817751 = 37226627) B37226627
theorem B16545167 : Blo 1909435 16545167 := bstep (se 1 (by rfl) ⟨12408875, by rfl⟩ : syracuseStep 16545167 = 24817751) B24817751
theorem B11030111 : Blo 1909435 11030111 := bstep (se 1 (by rfl) ⟨8272583, by rfl⟩ : syracuseStep 11030111 = 16545167) B16545167
theorem B7353407 : Blo 1909435 7353407 := bstep (se 1 (by rfl) ⟨5515055, by rfl⟩ : syracuseStep 7353407 = 11030111) B11030111
theorem B4902271 : Blo 1909435 4902271 := bstep (se 1 (by rfl) ⟨3676703, by rfl⟩ : syracuseStep 4902271 = 7353407) B7353407
theorem B26145445 : Blo 1909435 26145445 := bstep (se 4 (by rfl) ⟨2451135, by rfl⟩ : syracuseStep 26145445 = 4902271) B4902271
theorem B34860593 : Blo 1909435 34860593 := bstep (se 2 (by rfl) ⟨13072722, by rfl⟩ : syracuseStep 34860593 = 26145445) B26145445
theorem B23240395 : Blo 1909435 23240395 := bstep (se 1 (by rfl) ⟨17430296, by rfl⟩ : syracuseStep 23240395 = 34860593) B34860593
theorem B30987193 : Blo 1909435 30987193 := bstep (se 2 (by rfl) ⟨11620197, by rfl⟩ : syracuseStep 30987193 = 23240395) B23240395
theorem B41316257 : Blo 1909435 41316257 := bstep (se 2 (by rfl) ⟨15493596, by rfl⟩ : syracuseStep 41316257 = 30987193) B30987193
theorem B27544171 : Blo 1909435 27544171 := bstep (se 1 (by rfl) ⟨20658128, by rfl⟩ : syracuseStep 27544171 = 41316257) B41316257
theorem B36725561 : Blo 1909435 36725561 := bstep (se 2 (by rfl) ⟨13772085, by rfl⟩ : syracuseStep 36725561 = 27544171) B27544171
theorem B24483707 : Blo 1909435 24483707 := bstep (se 1 (by rfl) ⟨18362780, by rfl⟩ : syracuseStep 24483707 = 36725561) B36725561
theorem B16322471 : Blo 1909435 16322471 := bstep (se 1 (by rfl) ⟨12241853, by rfl⟩ : syracuseStep 16322471 = 24483707) B24483707
theorem B10881647 : Blo 1909435 10881647 := bstep (se 1 (by rfl) ⟨8161235, by rfl⟩ : syracuseStep 10881647 = 16322471) B16322471
theorem B7254431 : Blo 1909435 7254431 := bstep (se 1 (by rfl) ⟨5440823, by rfl⟩ : syracuseStep 7254431 = 10881647) B10881647
theorem B4836287 : Blo 1909435 4836287 := bstep (se 1 (by rfl) ⟨3627215, by rfl⟩ : syracuseStep 4836287 = 7254431) B7254431
theorem B3224191 : Blo 1909435 3224191 := bstep (se 1 (by rfl) ⟨2418143, by rfl⟩ : syracuseStep 3224191 = 4836287) B4836287
theorem B4298921 : Blo 1909435 4298921 := bstep (se 2 (by rfl) ⟨1612095, by rfl⟩ : syracuseStep 4298921 = 3224191) B3224191
theorem B2865947 : Blo 1909435 2865947 := bstep (se 1 (by rfl) ⟨2149460, by rfl⟩ : syracuseStep 2865947 = 4298921) B4298921
theorem B1910631 : Blo 1909435 1910631 := bstep (se 1 (by rfl) ⟨1432973, by rfl⟩ : syracuseStep 1910631 = 2865947) B2865947
theorem B2149465 : Blo 1909435 2149465 := bbase (se 2 (by rfl) ⟨806049, by rfl⟩ : syracuseStep 2149465 = 1612099) (by norm_num)
theorem B2865953 : Blo 1909435 2865953 := bstep (se 2 (by rfl) ⟨1074732, by rfl⟩ : syracuseStep 2865953 = 2149465) B2149465
theorem B1910635 : Blo 1909435 1910635 := bstep (se 1 (by rfl) ⟨1432976, by rfl⟩ : syracuseStep 1910635 = 2865953) B2865953
theorem B2178797 : Blo 1909435 2178797 := bbase (se 3 (by rfl) ⟨408524, by rfl⟩ : syracuseStep 2178797 = 817049) (by norm_num)
theorem B5810125 : Blo 1909435 5810125 := bstep (se 3 (by rfl) ⟨1089398, by rfl⟩ : syracuseStep 5810125 = 2178797) B2178797
theorem B7746833 : Blo 1909435 7746833 := bstep (se 2 (by rfl) ⟨2905062, by rfl⟩ : syracuseStep 7746833 = 5810125) B5810125
theorem B5164555 : Blo 1909435 5164555 := bstep (se 1 (by rfl) ⟨3873416, by rfl⟩ : syracuseStep 5164555 = 7746833) B7746833
theorem B6886073 : Blo 1909435 6886073 := bstep (se 2 (by rfl) ⟨2582277, by rfl⟩ : syracuseStep 6886073 = 5164555) B5164555
theorem B4590715 : Blo 1909435 4590715 := bstep (se 1 (by rfl) ⟨3443036, by rfl⟩ : syracuseStep 4590715 = 6886073) B6886073
theorem B6120953 : Blo 1909435 6120953 := bstep (se 2 (by rfl) ⟨2295357, by rfl⟩ : syracuseStep 6120953 = 4590715) B4590715
theorem B4080635 : Blo 1909435 4080635 := bstep (se 1 (by rfl) ⟨3060476, by rfl⟩ : syracuseStep 4080635 = 6120953) B6120953
theorem B2720423 : Blo 1909435 2720423 := bstep (se 1 (by rfl) ⟨2040317, by rfl⟩ : syracuseStep 2720423 = 4080635) B4080635
theorem B7254461 : Blo 1909435 7254461 := bstep (se 3 (by rfl) ⟨1360211, by rfl⟩ : syracuseStep 7254461 = 2720423) B2720423
theorem B4836307 : Blo 1909435 4836307 := bstep (se 1 (by rfl) ⟨3627230, by rfl⟩ : syracuseStep 4836307 = 7254461) B7254461
theorem B6448409 : Blo 1909435 6448409 := bstep (se 2 (by rfl) ⟨2418153, by rfl⟩ : syracuseStep 6448409 = 4836307) B4836307
theorem B4298939 : Blo 1909435 4298939 := bstep (se 1 (by rfl) ⟨3224204, by rfl⟩ : syracuseStep 4298939 = 6448409) B6448409
theorem B2865959 : Blo 1909435 2865959 := bstep (se 1 (by rfl) ⟨2149469, by rfl⟩ : syracuseStep 2865959 = 4298939) B4298939
theorem B1910639 : Blo 1909435 1910639 := bstep (se 1 (by rfl) ⟨1432979, by rfl⟩ : syracuseStep 1910639 = 2865959) B2865959
theorem B2865965 : Blo 1909435 2865965 := bbase (se 3 (by rfl) ⟨537368, by rfl⟩ : syracuseStep 2865965 = 1074737) (by norm_num)
theorem B1910643 : Blo 1909435 1910643 := bstep (se 1 (by rfl) ⟨1432982, by rfl⟩ : syracuseStep 1910643 = 2865965) B2865965
theorem B4298957 : Blo 1909435 4298957 := bbase (se 3 (by rfl) ⟨806054, by rfl⟩ : syracuseStep 4298957 = 1612109) (by norm_num)
theorem B2865971 : Blo 1909435 2865971 := bstep (se 1 (by rfl) ⟨2149478, by rfl⟩ : syracuseStep 2865971 = 4298957) B4298957
theorem B1910647 : Blo 1909435 1910647 := bstep (se 1 (by rfl) ⟨1432985, by rfl⟩ : syracuseStep 1910647 = 2865971) B2865971
theorem B2418169 : Blo 1909435 2418169 := bbase (se 2 (by rfl) ⟨906813, by rfl⟩ : syracuseStep 2418169 = 1813627) (by norm_num)
theorem B3224225 : Blo 1909435 3224225 := bstep (se 2 (by rfl) ⟨1209084, by rfl⟩ : syracuseStep 3224225 = 2418169) B2418169
theorem B2149483 : Blo 1909435 2149483 := bstep (se 1 (by rfl) ⟨1612112, by rfl⟩ : syracuseStep 2149483 = 3224225) B3224225
theorem B2865977 : Blo 1909435 2865977 := bstep (se 2 (by rfl) ⟨1074741, by rfl⟩ : syracuseStep 2865977 = 2149483) B2149483
theorem B1910651 : Blo 1909435 1910651 := bstep (se 1 (by rfl) ⟨1432988, by rfl⟩ : syracuseStep 1910651 = 2865977) B2865977
theorem B5164597 : Blo 1909435 5164597 := bbase (se 5 (by rfl) ⟨242090, by rfl⟩ : syracuseStep 5164597 = 484181) (by norm_num)
theorem B6886129 : Blo 1909435 6886129 := bstep (se 2 (by rfl) ⟨2582298, by rfl⟩ : syracuseStep 6886129 = 5164597) B5164597
theorem B9181505 : Blo 1909435 9181505 := bstep (se 2 (by rfl) ⟨3443064, by rfl⟩ : syracuseStep 9181505 = 6886129) B6886129
theorem B6121003 : Blo 1909435 6121003 := bstep (se 1 (by rfl) ⟨4590752, by rfl⟩ : syracuseStep 6121003 = 9181505) B9181505
theorem B8161337 : Blo 1909435 8161337 := bstep (se 2 (by rfl) ⟨3060501, by rfl⟩ : syracuseStep 8161337 = 6121003) B6121003
theorem B21763565 : Blo 1909435 21763565 := bstep (se 3 (by rfl) ⟨4080668, by rfl⟩ : syracuseStep 21763565 = 8161337) B8161337
theorem B14509043 : Blo 1909435 14509043 := bstep (se 1 (by rfl) ⟨10881782, by rfl⟩ : syracuseStep 14509043 = 21763565) B21763565
theorem B9672695 : Blo 1909435 9672695 := bstep (se 1 (by rfl) ⟨7254521, by rfl⟩ : syracuseStep 9672695 = 14509043) B14509043
theorem B6448463 : Blo 1909435 6448463 := bstep (se 1 (by rfl) ⟨4836347, by rfl⟩ : syracuseStep 6448463 = 9672695) B9672695
theorem B4298975 : Blo 1909435 4298975 := bstep (se 1 (by rfl) ⟨3224231, by rfl⟩ : syracuseStep 4298975 = 6448463) B6448463
theorem B2865983 : Blo 1909435 2865983 := bstep (se 1 (by rfl) ⟨2149487, by rfl⟩ : syracuseStep 2865983 = 4298975) B4298975
theorem B1910655 : Blo 1909435 1910655 := bstep (se 1 (by rfl) ⟨1432991, by rfl⟩ : syracuseStep 1910655 = 2865983) B2865983
theorem B2865989 : Blo 1909435 2865989 := bbase (se 4 (by rfl) ⟨268686, by rfl⟩ : syracuseStep 2865989 = 537373) (by norm_num)
theorem B1910659 : Blo 1909435 1910659 := bstep (se 1 (by rfl) ⟨1432994, by rfl⟩ : syracuseStep 1910659 = 2865989) B2865989
theorem B3224245 : Blo 1909435 3224245 := bbase (se 5 (by rfl) ⟨151136, by rfl⟩ : syracuseStep 3224245 = 302273) (by norm_num)
theorem B4298993 : Blo 1909435 4298993 := bstep (se 2 (by rfl) ⟨1612122, by rfl⟩ : syracuseStep 4298993 = 3224245) B3224245
theorem B2865995 : Blo 1909435 2865995 := bstep (se 1 (by rfl) ⟨2149496, by rfl⟩ : syracuseStep 2865995 = 4298993) B4298993
theorem B1910663 : Blo 1909435 1910663 := bstep (se 1 (by rfl) ⟨1432997, by rfl⟩ : syracuseStep 1910663 = 2865995) B2865995
theorem B2149501 : Blo 1909435 2149501 := bbase (se 3 (by rfl) ⟨403031, by rfl⟩ : syracuseStep 2149501 = 806063) (by norm_num)
theorem B2866001 : Blo 1909435 2866001 := bstep (se 2 (by rfl) ⟨1074750, by rfl⟩ : syracuseStep 2866001 = 2149501) B2149501
theorem B1910667 : Blo 1909435 1910667 := bstep (se 1 (by rfl) ⟨1433000, by rfl⟩ : syracuseStep 1910667 = 2866001) B2866001
theorem B6448517 : Blo 1909435 6448517 := bbase (se 4 (by rfl) ⟨604548, by rfl⟩ : syracuseStep 6448517 = 1209097) (by norm_num)
theorem B4299011 : Blo 1909435 4299011 := bstep (se 1 (by rfl) ⟨3224258, by rfl⟩ : syracuseStep 4299011 = 6448517) B6448517
theorem B2866007 : Blo 1909435 2866007 := bstep (se 1 (by rfl) ⟨2149505, by rfl⟩ : syracuseStep 2866007 = 4299011) B4299011
theorem B1910671 : Blo 1909435 1910671 := bstep (se 1 (by rfl) ⟨1433003, by rfl⟩ : syracuseStep 1910671 = 2866007) B2866007
theorem B2866013 : Blo 1909435 2866013 := bbase (se 3 (by rfl) ⟨537377, by rfl⟩ : syracuseStep 2866013 = 1074755) (by norm_num)
theorem B1910675 : Blo 1909435 1910675 := bstep (se 1 (by rfl) ⟨1433006, by rfl⟩ : syracuseStep 1910675 = 2866013) B2866013
theorem B4299029 : Blo 1909435 4299029 := bbase (se 6 (by rfl) ⟨100758, by rfl⟩ : syracuseStep 4299029 = 201517) (by norm_num)
theorem B2866019 : Blo 1909435 2866019 := bstep (se 1 (by rfl) ⟨2149514, by rfl⟩ : syracuseStep 2866019 = 4299029) B4299029
theorem B1910679 : Blo 1909435 1910679 := bstep (se 1 (by rfl) ⟨1433009, by rfl⟩ : syracuseStep 1910679 = 2866019) B2866019
theorem B7254629 : Blo 1909435 7254629 := bbase (se 4 (by rfl) ⟨680121, by rfl⟩ : syracuseStep 7254629 = 1360243) (by norm_num)
theorem B4836419 : Blo 1909435 4836419 := bstep (se 1 (by rfl) ⟨3627314, by rfl⟩ : syracuseStep 4836419 = 7254629) B7254629
theorem B3224279 : Blo 1909435 3224279 := bstep (se 1 (by rfl) ⟨2418209, by rfl⟩ : syracuseStep 3224279 = 4836419) B4836419
theorem B2149519 : Blo 1909435 2149519 := bstep (se 1 (by rfl) ⟨1612139, by rfl⟩ : syracuseStep 2149519 = 3224279) B3224279
theorem B2866025 : Blo 1909435 2866025 := bstep (se 2 (by rfl) ⟨1074759, by rfl⟩ : syracuseStep 2866025 = 2149519) B2149519
theorem B1910683 : Blo 1909435 1910683 := bstep (se 1 (by rfl) ⟨1433012, by rfl⟩ : syracuseStep 1910683 = 2866025) B2866025
theorem B1936757 : Blo 1909435 1936757 := bbase (se 5 (by rfl) ⟨90785, by rfl⟩ : syracuseStep 1936757 = 181571) (by norm_num)
theorem B5164685 : Blo 1909435 5164685 := bstep (se 3 (by rfl) ⟨968378, by rfl⟩ : syracuseStep 5164685 = 1936757) B1936757
theorem B3443123 : Blo 1909435 3443123 := bstep (se 1 (by rfl) ⟨2582342, by rfl⟩ : syracuseStep 3443123 = 5164685) B5164685
theorem B2295415 : Blo 1909435 2295415 := bstep (se 1 (by rfl) ⟨1721561, by rfl⟩ : syracuseStep 2295415 = 3443123) B3443123
theorem B3060553 : Blo 1909435 3060553 := bstep (se 2 (by rfl) ⟨1147707, by rfl⟩ : syracuseStep 3060553 = 2295415) B2295415
theorem B4080737 : Blo 1909435 4080737 := bstep (se 2 (by rfl) ⟨1530276, by rfl⟩ : syracuseStep 4080737 = 3060553) B3060553
theorem B10881965 : Blo 1909435 10881965 := bstep (se 3 (by rfl) ⟨2040368, by rfl⟩ : syracuseStep 10881965 = 4080737) B4080737
theorem B7254643 : Blo 1909435 7254643 := bstep (se 1 (by rfl) ⟨5440982, by rfl⟩ : syracuseStep 7254643 = 10881965) B10881965
theorem B9672857 : Blo 1909435 9672857 := bstep (se 2 (by rfl) ⟨3627321, by rfl⟩ : syracuseStep 9672857 = 7254643) B7254643
theorem B6448571 : Blo 1909435 6448571 := bstep (se 1 (by rfl) ⟨4836428, by rfl⟩ : syracuseStep 6448571 = 9672857) B9672857
theorem B4299047 : Blo 1909435 4299047 := bstep (se 1 (by rfl) ⟨3224285, by rfl⟩ : syracuseStep 4299047 = 6448571) B6448571
theorem B2866031 : Blo 1909435 2866031 := bstep (se 1 (by rfl) ⟨2149523, by rfl⟩ : syracuseStep 2866031 = 4299047) B4299047
theorem B1910687 : Blo 1909435 1910687 := bstep (se 1 (by rfl) ⟨1433015, by rfl⟩ : syracuseStep 1910687 = 2866031) B2866031
theorem B2866037 : Blo 1909435 2866037 := bbase (se 5 (by rfl) ⟨134345, by rfl⟩ : syracuseStep 2866037 = 268691) (by norm_num)
theorem B1910691 : Blo 1909435 1910691 := bstep (se 1 (by rfl) ⟨1433018, by rfl⟩ : syracuseStep 1910691 = 2866037) B2866037
theorem B2295425 : Blo 1909435 2295425 := bbase (se 2 (by rfl) ⟨860784, by rfl⟩ : syracuseStep 2295425 = 1721569) (by norm_num)
theorem B6121133 : Blo 1909435 6121133 := bstep (se 3 (by rfl) ⟨1147712, by rfl⟩ : syracuseStep 6121133 = 2295425) B2295425
theorem B4080755 : Blo 1909435 4080755 := bstep (se 1 (by rfl) ⟨3060566, by rfl⟩ : syracuseStep 4080755 = 6121133) B6121133
theorem B2720503 : Blo 1909435 2720503 := bstep (se 1 (by rfl) ⟨2040377, by rfl⟩ : syracuseStep 2720503 = 4080755) B4080755
theorem B3627337 : Blo 1909435 3627337 := bstep (se 2 (by rfl) ⟨1360251, by rfl⟩ : syracuseStep 3627337 = 2720503) B2720503
theorem B4836449 : Blo 1909435 4836449 := bstep (se 2 (by rfl) ⟨1813668, by rfl⟩ : syracuseStep 4836449 = 3627337) B3627337
theorem B3224299 : Blo 1909435 3224299 := bstep (se 1 (by rfl) ⟨2418224, by rfl⟩ : syracuseStep 3224299 = 4836449) B4836449
theorem B4299065 : Blo 1909435 4299065 := bstep (se 2 (by rfl) ⟨1612149, by rfl⟩ : syracuseStep 4299065 = 3224299) B3224299
theorem B2866043 : Blo 1909435 2866043 := bstep (se 1 (by rfl) ⟨2149532, by rfl⟩ : syracuseStep 2866043 = 4299065) B4299065
theorem B1910695 : Blo 1909435 1910695 := bstep (se 1 (by rfl) ⟨1433021, by rfl⟩ : syracuseStep 1910695 = 2866043) B2866043
theorem B2149537 : Blo 1909435 2149537 := bbase (se 2 (by rfl) ⟨806076, by rfl⟩ : syracuseStep 2149537 = 1612153) (by norm_num)
theorem B2866049 : Blo 1909435 2866049 := bstep (se 2 (by rfl) ⟨1074768, by rfl⟩ : syracuseStep 2866049 = 2149537) B2149537
theorem B1910699 : Blo 1909435 1910699 := bstep (se 1 (by rfl) ⟨1433024, by rfl⟩ : syracuseStep 1910699 = 2866049) B2866049
theorem B4836469 : Blo 1909435 4836469 := bbase (se 5 (by rfl) ⟨226709, by rfl⟩ : syracuseStep 4836469 = 453419) (by norm_num)
theorem B6448625 : Blo 1909435 6448625 := bstep (se 2 (by rfl) ⟨2418234, by rfl⟩ : syracuseStep 6448625 = 4836469) B4836469
theorem B4299083 : Blo 1909435 4299083 := bstep (se 1 (by rfl) ⟨3224312, by rfl⟩ : syracuseStep 4299083 = 6448625) B6448625
theorem B2866055 : Blo 1909435 2866055 := bstep (se 1 (by rfl) ⟨2149541, by rfl⟩ : syracuseStep 2866055 = 4299083) B4299083
theorem B1910703 : Blo 1909435 1910703 := bstep (se 1 (by rfl) ⟨1433027, by rfl⟩ : syracuseStep 1910703 = 2866055) B2866055
theorem B2866061 : Blo 1909435 2866061 := bbase (se 3 (by rfl) ⟨537386, by rfl⟩ : syracuseStep 2866061 = 1074773) (by norm_num)
theorem B1910707 : Blo 1909435 1910707 := bstep (se 1 (by rfl) ⟨1433030, by rfl⟩ : syracuseStep 1910707 = 2866061) B2866061
theorem B4299101 : Blo 1909435 4299101 := bbase (se 3 (by rfl) ⟨806081, by rfl⟩ : syracuseStep 4299101 = 1612163) (by norm_num)
theorem B2866067 : Blo 1909435 2866067 := bstep (se 1 (by rfl) ⟨2149550, by rfl⟩ : syracuseStep 2866067 = 4299101) B4299101
theorem B1910711 : Blo 1909435 1910711 := bstep (se 1 (by rfl) ⟨1433033, by rfl⟩ : syracuseStep 1910711 = 2866067) B2866067
theorem B3224333 : Blo 1909435 3224333 := bbase (se 3 (by rfl) ⟨604562, by rfl⟩ : syracuseStep 3224333 = 1209125) (by norm_num)
theorem B2149555 : Blo 1909435 2149555 := bstep (se 1 (by rfl) ⟨1612166, by rfl⟩ : syracuseStep 2149555 = 3224333) B3224333
theorem B2866073 : Blo 1909435 2866073 := bstep (se 2 (by rfl) ⟨1074777, by rfl⟩ : syracuseStep 2866073 = 2149555) B2149555
theorem B1910715 : Blo 1909435 1910715 := bstep (se 1 (by rfl) ⟨1433036, by rfl⟩ : syracuseStep 1910715 = 2866073) B2866073
theorem B16323221 : Blo 1909435 16323221 := bbase (se 6 (by rfl) ⟨382575, by rfl⟩ : syracuseStep 16323221 = 765151) (by norm_num)
theorem B10882147 : Blo 1909435 10882147 := bstep (se 1 (by rfl) ⟨8161610, by rfl⟩ : syracuseStep 10882147 = 16323221) B16323221
theorem B14509529 : Blo 1909435 14509529 := bstep (se 2 (by rfl) ⟨5441073, by rfl⟩ : syracuseStep 14509529 = 10882147) B10882147
theorem B9673019 : Blo 1909435 9673019 := bstep (se 1 (by rfl) ⟨7254764, by rfl⟩ : syracuseStep 9673019 = 14509529) B14509529
theorem B6448679 : Blo 1909435 6448679 := bstep (se 1 (by rfl) ⟨4836509, by rfl⟩ : syracuseStep 6448679 = 9673019) B9673019
theorem B4299119 : Blo 1909435 4299119 := bstep (se 1 (by rfl) ⟨3224339, by rfl⟩ : syracuseStep 4299119 = 6448679) B6448679
theorem B2866079 : Blo 1909435 2866079 := bstep (se 1 (by rfl) ⟨2149559, by rfl⟩ : syracuseStep 2866079 = 4299119) B4299119
theorem B1910719 : Blo 1909435 1910719 := bstep (se 1 (by rfl) ⟨1433039, by rfl⟩ : syracuseStep 1910719 = 2866079) B2866079
theorem B2866085 : Blo 1909435 2866085 := bbase (se 4 (by rfl) ⟨268695, by rfl⟩ : syracuseStep 2866085 = 537391) (by norm_num)
theorem B1910723 : Blo 1909435 1910723 := bstep (se 1 (by rfl) ⟨1433042, by rfl⟩ : syracuseStep 1910723 = 2866085) B2866085
theorem B2418265 : Blo 1909435 2418265 := bbase (se 2 (by rfl) ⟨906849, by rfl⟩ : syracuseStep 2418265 = 1813699) (by norm_num)
theorem B3224353 : Blo 1909435 3224353 := bstep (se 2 (by rfl) ⟨1209132, by rfl⟩ : syracuseStep 3224353 = 2418265) B2418265
theorem B4299137 : Blo 1909435 4299137 := bstep (se 2 (by rfl) ⟨1612176, by rfl⟩ : syracuseStep 4299137 = 3224353) B3224353
theorem B2866091 : Blo 1909435 2866091 := bstep (se 1 (by rfl) ⟨2149568, by rfl⟩ : syracuseStep 2866091 = 4299137) B4299137
theorem B1910727 : Blo 1909435 1910727 := bstep (se 1 (by rfl) ⟨1433045, by rfl⟩ : syracuseStep 1910727 = 2866091) B2866091
theorem B2149573 : Blo 1909435 2149573 := bbase (se 4 (by rfl) ⟨201522, by rfl⟩ : syracuseStep 2149573 = 403045) (by norm_num)
theorem B2866097 : Blo 1909435 2866097 := bstep (se 2 (by rfl) ⟨1074786, by rfl⟩ : syracuseStep 2866097 = 2149573) B2149573
theorem B1910731 : Blo 1909435 1910731 := bstep (se 1 (by rfl) ⟨1433048, by rfl⟩ : syracuseStep 1910731 = 2866097) B2866097
theorem B3627413 : Blo 1909435 3627413 := bbase (se 6 (by rfl) ⟨85017, by rfl⟩ : syracuseStep 3627413 = 170035) (by norm_num)
theorem B2418275 : Blo 1909435 2418275 := bstep (se 1 (by rfl) ⟨1813706, by rfl⟩ : syracuseStep 2418275 = 3627413) B3627413
theorem B6448733 : Blo 1909435 6448733 := bstep (se 3 (by rfl) ⟨1209137, by rfl⟩ : syracuseStep 6448733 = 2418275) B2418275
theorem B4299155 : Blo 1909435 4299155 := bstep (se 1 (by rfl) ⟨3224366, by rfl⟩ : syracuseStep 4299155 = 6448733) B6448733
theorem B2866103 : Blo 1909435 2866103 := bstep (se 1 (by rfl) ⟨2149577, by rfl⟩ : syracuseStep 2866103 = 4299155) B4299155
theorem B1910735 : Blo 1909435 1910735 := bstep (se 1 (by rfl) ⟨1433051, by rfl⟩ : syracuseStep 1910735 = 2866103) B2866103
theorem B2866109 : Blo 1909435 2866109 := bbase (se 3 (by rfl) ⟨537395, by rfl⟩ : syracuseStep 2866109 = 1074791) (by norm_num)
theorem B1910739 : Blo 1909435 1910739 := bstep (se 1 (by rfl) ⟨1433054, by rfl⟩ : syracuseStep 1910739 = 2866109) B2866109
theorem B4299173 : Blo 1909435 4299173 := bbase (se 4 (by rfl) ⟨403047, by rfl⟩ : syracuseStep 4299173 = 806095) (by norm_num)
theorem B2866115 : Blo 1909435 2866115 := bstep (se 1 (by rfl) ⟨2149586, by rfl⟩ : syracuseStep 2866115 = 4299173) B4299173
theorem B1910743 : Blo 1909435 1910743 := bstep (se 1 (by rfl) ⟨1433057, by rfl⟩ : syracuseStep 1910743 = 2866115) B2866115
theorem B4836581 : Blo 1909435 4836581 := bbase (se 4 (by rfl) ⟨453429, by rfl⟩ : syracuseStep 4836581 = 906859) (by norm_num)
theorem B3224387 : Blo 1909435 3224387 := bstep (se 1 (by rfl) ⟨2418290, by rfl⟩ : syracuseStep 3224387 = 4836581) B4836581
theorem B2149591 : Blo 1909435 2149591 := bstep (se 1 (by rfl) ⟨1612193, by rfl⟩ : syracuseStep 2149591 = 3224387) B3224387
theorem B2866121 : Blo 1909435 2866121 := bstep (se 2 (by rfl) ⟨1074795, by rfl⟩ : syracuseStep 2866121 = 2149591) B2149591
theorem B1910747 : Blo 1909435 1910747 := bstep (se 1 (by rfl) ⟨1433060, by rfl⟩ : syracuseStep 1910747 = 2866121) B2866121
theorem B2040437 : Blo 1909435 2040437 := bbase (se 5 (by rfl) ⟨95645, by rfl⟩ : syracuseStep 2040437 = 191291) (by norm_num)
theorem B5441165 : Blo 1909435 5441165 := bstep (se 3 (by rfl) ⟨1020218, by rfl⟩ : syracuseStep 5441165 = 2040437) B2040437
theorem B3627443 : Blo 1909435 3627443 := bstep (se 1 (by rfl) ⟨2720582, by rfl⟩ : syracuseStep 3627443 = 5441165) B5441165
theorem B9673181 : Blo 1909435 9673181 := bstep (se 3 (by rfl) ⟨1813721, by rfl⟩ : syracuseStep 9673181 = 3627443) B3627443
theorem B6448787 : Blo 1909435 6448787 := bstep (se 1 (by rfl) ⟨4836590, by rfl⟩ : syracuseStep 6448787 = 9673181) B9673181
theorem B4299191 : Blo 1909435 4299191 := bstep (se 1 (by rfl) ⟨3224393, by rfl⟩ : syracuseStep 4299191 = 6448787) B6448787
theorem B2866127 : Blo 1909435 2866127 := bstep (se 1 (by rfl) ⟨2149595, by rfl⟩ : syracuseStep 2866127 = 4299191) B4299191
theorem B1910751 : Blo 1909435 1910751 := bstep (se 1 (by rfl) ⟨1433063, by rfl⟩ : syracuseStep 1910751 = 2866127) B2866127
theorem B2866133 : Blo 1909435 2866133 := bbase (se 7 (by rfl) ⟨33587, by rfl⟩ : syracuseStep 2866133 = 67175) (by norm_num)
theorem B1910755 : Blo 1909435 1910755 := bstep (se 1 (by rfl) ⟨1433066, by rfl⟩ : syracuseStep 1910755 = 2866133) B2866133
theorem B7254917 : Blo 1909435 7254917 := bbase (se 4 (by rfl) ⟨680148, by rfl⟩ : syracuseStep 7254917 = 1360297) (by norm_num)
theorem B4836611 : Blo 1909435 4836611 := bstep (se 1 (by rfl) ⟨3627458, by rfl⟩ : syracuseStep 4836611 = 7254917) B7254917
theorem B3224407 : Blo 1909435 3224407 := bstep (se 1 (by rfl) ⟨2418305, by rfl⟩ : syracuseStep 3224407 = 4836611) B4836611
theorem B4299209 : Blo 1909435 4299209 := bstep (se 2 (by rfl) ⟨1612203, by rfl⟩ : syracuseStep 4299209 = 3224407) B3224407
theorem B2866139 : Blo 1909435 2866139 := bstep (se 1 (by rfl) ⟨2149604, by rfl⟩ : syracuseStep 2866139 = 4299209) B4299209
theorem B1910759 : Blo 1909435 1910759 := bstep (se 1 (by rfl) ⟨1433069, by rfl⟩ : syracuseStep 1910759 = 2866139) B2866139
theorem B2149609 : Blo 1909435 2149609 := bbase (se 2 (by rfl) ⟨806103, by rfl⟩ : syracuseStep 2149609 = 1612207) (by norm_num)
theorem B2866145 : Blo 1909435 2866145 := bstep (se 2 (by rfl) ⟨1074804, by rfl⟩ : syracuseStep 2866145 = 2149609) B2149609
theorem B1910763 : Blo 1909435 1910763 := bstep (se 1 (by rfl) ⟨1433072, by rfl⟩ : syracuseStep 1910763 = 2866145) B2866145
theorem B10882421 : Blo 1909435 10882421 := bbase (se 5 (by rfl) ⟨510113, by rfl⟩ : syracuseStep 10882421 = 1020227) (by norm_num)
theorem B7254947 : Blo 1909435 7254947 := bstep (se 1 (by rfl) ⟨5441210, by rfl⟩ : syracuseStep 7254947 = 10882421) B10882421
theorem B4836631 : Blo 1909435 4836631 := bstep (se 1 (by rfl) ⟨3627473, by rfl⟩ : syracuseStep 4836631 = 7254947) B7254947
theorem B6448841 : Blo 1909435 6448841 := bstep (se 2 (by rfl) ⟨2418315, by rfl⟩ : syracuseStep 6448841 = 4836631) B4836631
theorem B4299227 : Blo 1909435 4299227 := bstep (se 1 (by rfl) ⟨3224420, by rfl⟩ : syracuseStep 4299227 = 6448841) B6448841
theorem B2866151 : Blo 1909435 2866151 := bstep (se 1 (by rfl) ⟨2149613, by rfl⟩ : syracuseStep 2866151 = 4299227) B4299227
theorem B1910767 : Blo 1909435 1910767 := bstep (se 1 (by rfl) ⟨1433075, by rfl⟩ : syracuseStep 1910767 = 2866151) B2866151
theorem B2866157 : Blo 1909435 2866157 := bbase (se 3 (by rfl) ⟨537404, by rfl⟩ : syracuseStep 2866157 = 1074809) (by norm_num)
theorem B1910771 : Blo 1909435 1910771 := bstep (se 1 (by rfl) ⟨1433078, by rfl⟩ : syracuseStep 1910771 = 2866157) B2866157
theorem B4299245 : Blo 1909435 4299245 := bbase (se 3 (by rfl) ⟨806108, by rfl⟩ : syracuseStep 4299245 = 1612217) (by norm_num)
theorem B2866163 : Blo 1909435 2866163 := bstep (se 1 (by rfl) ⟨2149622, by rfl⟩ : syracuseStep 2866163 = 4299245) B4299245
theorem B1910775 : Blo 1909435 1910775 := bstep (se 1 (by rfl) ⟨1433081, by rfl⟩ : syracuseStep 1910775 = 2866163) B2866163
theorem B3873701 : Blo 1909435 3873701 := bbase (se 4 (by rfl) ⟨363159, by rfl⟩ : syracuseStep 3873701 = 726319) (by norm_num)
theorem B10329869 : Blo 1909435 10329869 := bstep (se 3 (by rfl) ⟨1936850, by rfl⟩ : syracuseStep 10329869 = 3873701) B3873701
theorem B6886579 : Blo 1909435 6886579 := bstep (se 1 (by rfl) ⟨5164934, by rfl⟩ : syracuseStep 6886579 = 10329869) B10329869
theorem B9182105 : Blo 1909435 9182105 := bstep (se 2 (by rfl) ⟨3443289, by rfl⟩ : syracuseStep 9182105 = 6886579) B6886579
theorem B6121403 : Blo 1909435 6121403 := bstep (se 1 (by rfl) ⟨4591052, by rfl⟩ : syracuseStep 6121403 = 9182105) B9182105
theorem B4080935 : Blo 1909435 4080935 := bstep (se 1 (by rfl) ⟨3060701, by rfl⟩ : syracuseStep 4080935 = 6121403) B6121403
theorem B2720623 : Blo 1909435 2720623 := bstep (se 1 (by rfl) ⟨2040467, by rfl⟩ : syracuseStep 2720623 = 4080935) B4080935
theorem B3627497 : Blo 1909435 3627497 := bstep (se 2 (by rfl) ⟨1360311, by rfl⟩ : syracuseStep 3627497 = 2720623) B2720623
theorem B2418331 : Blo 1909435 2418331 := bstep (se 1 (by rfl) ⟨1813748, by rfl⟩ : syracuseStep 2418331 = 3627497) B3627497
theorem B3224441 : Blo 1909435 3224441 := bstep (se 2 (by rfl) ⟨1209165, by rfl⟩ : syracuseStep 3224441 = 2418331) B2418331
theorem B2149627 : Blo 1909435 2149627 := bstep (se 1 (by rfl) ⟨1612220, by rfl⟩ : syracuseStep 2149627 = 3224441) B3224441
theorem B2866169 : Blo 1909435 2866169 := bstep (se 2 (by rfl) ⟨1074813, by rfl⟩ : syracuseStep 2866169 = 2149627) B2149627
theorem B1910779 : Blo 1909435 1910779 := bstep (se 1 (by rfl) ⟨1433084, by rfl⟩ : syracuseStep 1910779 = 2866169) B2866169
theorem B123958613 : Blo 1909435 123958613 := bbase (se 13 (by rfl) ⟨22697, by rfl⟩ : syracuseStep 123958613 = 45395) (by norm_num)
theorem B82639075 : Blo 1909435 82639075 := bstep (se 1 (by rfl) ⟨61979306, by rfl⟩ : syracuseStep 82639075 = 123958613) B123958613
theorem B110185433 : Blo 1909435 110185433 := bstep (se 2 (by rfl) ⟨41319537, by rfl⟩ : syracuseStep 110185433 = 82639075) B82639075
theorem B73456955 : Blo 1909435 73456955 := bstep (se 1 (by rfl) ⟨55092716, by rfl⟩ : syracuseStep 73456955 = 110185433) B110185433
theorem B48971303 : Blo 1909435 48971303 := bstep (se 1 (by rfl) ⟨36728477, by rfl⟩ : syracuseStep 48971303 = 73456955) B73456955
theorem B32647535 : Blo 1909435 32647535 := bstep (se 1 (by rfl) ⟨24485651, by rfl⟩ : syracuseStep 32647535 = 48971303) B48971303
theorem B21765023 : Blo 1909435 21765023 := bstep (se 1 (by rfl) ⟨16323767, by rfl⟩ : syracuseStep 21765023 = 32647535) B32647535
theorem B14510015 : Blo 1909435 14510015 := bstep (se 1 (by rfl) ⟨10882511, by rfl⟩ : syracuseStep 14510015 = 21765023) B21765023
theorem B9673343 : Blo 1909435 9673343 := bstep (se 1 (by rfl) ⟨7255007, by rfl⟩ : syracuseStep 9673343 = 14510015) B14510015
theorem B6448895 : Blo 1909435 6448895 := bstep (se 1 (by rfl) ⟨4836671, by rfl⟩ : syracuseStep 6448895 = 9673343) B9673343
theorem B4299263 : Blo 1909435 4299263 := bstep (se 1 (by rfl) ⟨3224447, by rfl⟩ : syracuseStep 4299263 = 6448895) B6448895
theorem B2866175 : Blo 1909435 2866175 := bstep (se 1 (by rfl) ⟨2149631, by rfl⟩ : syracuseStep 2866175 = 4299263) B4299263
theorem B1910783 : Blo 1909435 1910783 := bstep (se 1 (by rfl) ⟨1433087, by rfl⟩ : syracuseStep 1910783 = 2866175) B2866175
theorem B2866181 : Blo 1909435 2866181 := bbase (se 4 (by rfl) ⟨268704, by rfl⟩ : syracuseStep 2866181 = 537409) (by norm_num)
theorem B1910787 : Blo 1909435 1910787 := bstep (se 1 (by rfl) ⟨1433090, by rfl⟩ : syracuseStep 1910787 = 2866181) B2866181
theorem B3224461 : Blo 1909435 3224461 := bbase (se 3 (by rfl) ⟨604586, by rfl⟩ : syracuseStep 3224461 = 1209173) (by norm_num)
theorem B4299281 : Blo 1909435 4299281 := bstep (se 2 (by rfl) ⟨1612230, by rfl⟩ : syracuseStep 4299281 = 3224461) B3224461
theorem B2866187 : Blo 1909435 2866187 := bstep (se 1 (by rfl) ⟨2149640, by rfl⟩ : syracuseStep 2866187 = 4299281) B4299281
theorem B1910791 : Blo 1909435 1910791 := bstep (se 1 (by rfl) ⟨1433093, by rfl⟩ : syracuseStep 1910791 = 2866187) B2866187
theorem B2149645 : Blo 1909435 2149645 := bbase (se 3 (by rfl) ⟨403058, by rfl⟩ : syracuseStep 2149645 = 806117) (by norm_num)
theorem B2866193 : Blo 1909435 2866193 := bstep (se 2 (by rfl) ⟨1074822, by rfl⟩ : syracuseStep 2866193 = 2149645) B2149645
theorem B1910795 : Blo 1909435 1910795 := bstep (se 1 (by rfl) ⟨1433096, by rfl⟩ : syracuseStep 1910795 = 2866193) B2866193
theorem B6448949 : Blo 1909435 6448949 := bbase (se 5 (by rfl) ⟨302294, by rfl⟩ : syracuseStep 6448949 = 604589) (by norm_num)
theorem B4299299 : Blo 1909435 4299299 := bstep (se 1 (by rfl) ⟨3224474, by rfl⟩ : syracuseStep 4299299 = 6448949) B6448949
theorem B2866199 : Blo 1909435 2866199 := bstep (se 1 (by rfl) ⟨2149649, by rfl⟩ : syracuseStep 2866199 = 4299299) B4299299
theorem B1910799 : Blo 1909435 1910799 := bstep (se 1 (by rfl) ⟨1433099, by rfl⟩ : syracuseStep 1910799 = 2866199) B2866199
theorem B2866205 : Blo 1909435 2866205 := bbase (se 3 (by rfl) ⟨537413, by rfl⟩ : syracuseStep 2866205 = 1074827) (by norm_num)
theorem B1910803 : Blo 1909435 1910803 := bstep (se 1 (by rfl) ⟨1433102, by rfl⟩ : syracuseStep 1910803 = 2866205) B2866205
theorem B4299317 : Blo 1909435 4299317 := bbase (se 5 (by rfl) ⟨201530, by rfl⟩ : syracuseStep 4299317 = 403061) (by norm_num)
theorem B2866211 : Blo 1909435 2866211 := bstep (se 1 (by rfl) ⟨2149658, by rfl⟩ : syracuseStep 2866211 = 4299317) B4299317
theorem B1910807 : Blo 1909435 1910807 := bstep (se 1 (by rfl) ⟨1433105, by rfl⟩ : syracuseStep 1910807 = 2866211) B2866211
theorem B8162005 : Blo 1909435 8162005 := bbase (se 7 (by rfl) ⟨95648, by rfl⟩ : syracuseStep 8162005 = 191297) (by norm_num)
theorem B10882673 : Blo 1909435 10882673 := bstep (se 2 (by rfl) ⟨4081002, by rfl⟩ : syracuseStep 10882673 = 8162005) B8162005
theorem B7255115 : Blo 1909435 7255115 := bstep (se 1 (by rfl) ⟨5441336, by rfl⟩ : syracuseStep 7255115 = 10882673) B10882673
theorem B4836743 : Blo 1909435 4836743 := bstep (se 1 (by rfl) ⟨3627557, by rfl⟩ : syracuseStep 4836743 = 7255115) B7255115
theorem B3224495 : Blo 1909435 3224495 := bstep (se 1 (by rfl) ⟨2418371, by rfl⟩ : syracuseStep 3224495 = 4836743) B4836743
theorem B2149663 : Blo 1909435 2149663 := bstep (se 1 (by rfl) ⟨1612247, by rfl⟩ : syracuseStep 2149663 = 3224495) B3224495
theorem B2866217 : Blo 1909435 2866217 := bstep (se 2 (by rfl) ⟨1074831, by rfl⟩ : syracuseStep 2866217 = 2149663) B2149663
theorem B1910811 : Blo 1909435 1910811 := bstep (se 1 (by rfl) ⟨1433108, by rfl⟩ : syracuseStep 1910811 = 2866217) B2866217
theorem B8162021 : Blo 1909435 8162021 := bbase (se 4 (by rfl) ⟨765189, by rfl⟩ : syracuseStep 8162021 = 1530379) (by norm_num)
theorem B5441347 : Blo 1909435 5441347 := bstep (se 1 (by rfl) ⟨4081010, by rfl⟩ : syracuseStep 5441347 = 8162021) B8162021
theorem B7255129 : Blo 1909435 7255129 := bstep (se 2 (by rfl) ⟨2720673, by rfl⟩ : syracuseStep 7255129 = 5441347) B5441347
theorem B9673505 : Blo 1909435 9673505 := bstep (se 2 (by rfl) ⟨3627564, by rfl⟩ : syracuseStep 9673505 = 7255129) B7255129
theorem B6449003 : Blo 1909435 6449003 := bstep (se 1 (by rfl) ⟨4836752, by rfl⟩ : syracuseStep 6449003 = 9673505) B9673505
theorem B4299335 : Blo 1909435 4299335 := bstep (se 1 (by rfl) ⟨3224501, by rfl⟩ : syracuseStep 4299335 = 6449003) B6449003
theorem B2866223 : Blo 1909435 2866223 := bstep (se 1 (by rfl) ⟨2149667, by rfl⟩ : syracuseStep 2866223 = 4299335) B4299335
theorem B1910815 : Blo 1909435 1910815 := bstep (se 1 (by rfl) ⟨1433111, by rfl⟩ : syracuseStep 1910815 = 2866223) B2866223
theorem B2866229 : Blo 1909435 2866229 := bbase (se 5 (by rfl) ⟨134354, by rfl⟩ : syracuseStep 2866229 = 268709) (by norm_num)
theorem B1910819 : Blo 1909435 1910819 := bstep (se 1 (by rfl) ⟨1433114, by rfl⟩ : syracuseStep 1910819 = 2866229) B2866229
theorem B4836773 : Blo 1909435 4836773 := bbase (se 4 (by rfl) ⟨453447, by rfl⟩ : syracuseStep 4836773 = 906895) (by norm_num)
theorem B3224515 : Blo 1909435 3224515 := bstep (se 1 (by rfl) ⟨2418386, by rfl⟩ : syracuseStep 3224515 = 4836773) B4836773
theorem B4299353 : Blo 1909435 4299353 := bstep (se 2 (by rfl) ⟨1612257, by rfl⟩ : syracuseStep 4299353 = 3224515) B3224515
theorem B2866235 : Blo 1909435 2866235 := bstep (se 1 (by rfl) ⟨2149676, by rfl⟩ : syracuseStep 2866235 = 4299353) B4299353
theorem B1910823 : Blo 1909435 1910823 := bstep (se 1 (by rfl) ⟨1433117, by rfl⟩ : syracuseStep 1910823 = 2866235) B2866235
theorem B2149681 : Blo 1909435 2149681 := bbase (se 2 (by rfl) ⟨806130, by rfl⟩ : syracuseStep 2149681 = 1612261) (by norm_num)
theorem B2866241 : Blo 1909435 2866241 := bstep (se 2 (by rfl) ⟨1074840, by rfl⟩ : syracuseStep 2866241 = 2149681) B2149681
theorem B1910827 : Blo 1909435 1910827 := bstep (se 1 (by rfl) ⟨1433120, by rfl⟩ : syracuseStep 1910827 = 2866241) B2866241
theorem B4081045 : Blo 1909435 4081045 := bbase (se 6 (by rfl) ⟨95649, by rfl⟩ : syracuseStep 4081045 = 191299) (by norm_num)
theorem B5441393 : Blo 1909435 5441393 := bstep (se 2 (by rfl) ⟨2040522, by rfl⟩ : syracuseStep 5441393 = 4081045) B4081045
theorem B3627595 : Blo 1909435 3627595 := bstep (se 1 (by rfl) ⟨2720696, by rfl⟩ : syracuseStep 3627595 = 5441393) B5441393
theorem B4836793 : Blo 1909435 4836793 := bstep (se 2 (by rfl) ⟨1813797, by rfl⟩ : syracuseStep 4836793 = 3627595) B3627595
theorem B6449057 : Blo 1909435 6449057 := bstep (se 2 (by rfl) ⟨2418396, by rfl⟩ : syracuseStep 6449057 = 4836793) B4836793
theorem B4299371 : Blo 1909435 4299371 := bstep (se 1 (by rfl) ⟨3224528, by rfl⟩ : syracuseStep 4299371 = 6449057) B6449057
theorem B2866247 : Blo 1909435 2866247 := bstep (se 1 (by rfl) ⟨2149685, by rfl⟩ : syracuseStep 2866247 = 4299371) B4299371
theorem B1910831 : Blo 1909435 1910831 := bstep (se 1 (by rfl) ⟨1433123, by rfl⟩ : syracuseStep 1910831 = 2866247) B2866247
theorem B2866253 : Blo 1909435 2866253 := bbase (se 3 (by rfl) ⟨537422, by rfl⟩ : syracuseStep 2866253 = 1074845) (by norm_num)
theorem B1910835 : Blo 1909435 1910835 := bstep (se 1 (by rfl) ⟨1433126, by rfl⟩ : syracuseStep 1910835 = 2866253) B2866253
theorem B4299389 : Blo 1909435 4299389 := bbase (se 3 (by rfl) ⟨806135, by rfl⟩ : syracuseStep 4299389 = 1612271) (by norm_num)
theorem B2866259 : Blo 1909435 2866259 := bstep (se 1 (by rfl) ⟨2149694, by rfl⟩ : syracuseStep 2866259 = 4299389) B4299389
theorem B1910839 : Blo 1909435 1910839 := bstep (se 1 (by rfl) ⟨1433129, by rfl⟩ : syracuseStep 1910839 = 2866259) B2866259
theorem B3224549 : Blo 1909435 3224549 := bbase (se 4 (by rfl) ⟨302301, by rfl⟩ : syracuseStep 3224549 = 604603) (by norm_num)
theorem B2149699 : Blo 1909435 2149699 := bstep (se 1 (by rfl) ⟨1612274, by rfl⟩ : syracuseStep 2149699 = 3224549) B3224549
theorem B2866265 : Blo 1909435 2866265 := bstep (se 2 (by rfl) ⟨1074849, by rfl⟩ : syracuseStep 2866265 = 2149699) B2149699
theorem B1910843 : Blo 1909435 1910843 := bstep (se 1 (by rfl) ⟨1433132, by rfl⟩ : syracuseStep 1910843 = 2866265) B2866265
theorem B4358069 : Blo 1909435 4358069 := bbase (se 5 (by rfl) ⟨204284, by rfl⟩ : syracuseStep 4358069 = 408569) (by norm_num)
theorem B2905379 : Blo 1909435 2905379 := bstep (se 1 (by rfl) ⟨2179034, by rfl⟩ : syracuseStep 2905379 = 4358069) B4358069
theorem B1936919 : Blo 1909435 1936919 := bstep (se 1 (by rfl) ⟨1452689, by rfl⟩ : syracuseStep 1936919 = 2905379) B2905379
theorem B5165117 : Blo 1909435 5165117 := bstep (se 3 (by rfl) ⟨968459, by rfl⟩ : syracuseStep 5165117 = 1936919) B1936919
theorem B3443411 : Blo 1909435 3443411 := bstep (se 1 (by rfl) ⟨2582558, by rfl⟩ : syracuseStep 3443411 = 5165117) B5165117
theorem B9182429 : Blo 1909435 9182429 := bstep (se 3 (by rfl) ⟨1721705, by rfl⟩ : syracuseStep 9182429 = 3443411) B3443411
theorem B6121619 : Blo 1909435 6121619 := bstep (se 1 (by rfl) ⟨4591214, by rfl⟩ : syracuseStep 6121619 = 9182429) B9182429
theorem B4081079 : Blo 1909435 4081079 := bstep (se 1 (by rfl) ⟨3060809, by rfl⟩ : syracuseStep 4081079 = 6121619) B6121619
theorem B2720719 : Blo 1909435 2720719 := bstep (se 1 (by rfl) ⟨2040539, by rfl⟩ : syracuseStep 2720719 = 4081079) B4081079
theorem B14510501 : Blo 1909435 14510501 := bstep (se 4 (by rfl) ⟨1360359, by rfl⟩ : syracuseStep 14510501 = 2720719) B2720719
theorem B9673667 : Blo 1909435 9673667 := bstep (se 1 (by rfl) ⟨7255250, by rfl⟩ : syracuseStep 9673667 = 14510501) B14510501
theorem B6449111 : Blo 1909435 6449111 := bstep (se 1 (by rfl) ⟨4836833, by rfl⟩ : syracuseStep 6449111 = 9673667) B9673667
theorem B4299407 : Blo 1909435 4299407 := bstep (se 1 (by rfl) ⟨3224555, by rfl⟩ : syracuseStep 4299407 = 6449111) B6449111
theorem B2866271 : Blo 1909435 2866271 := bstep (se 1 (by rfl) ⟨2149703, by rfl⟩ : syracuseStep 2866271 = 4299407) B4299407
theorem B1910847 : Blo 1909435 1910847 := bstep (se 1 (by rfl) ⟨1433135, by rfl⟩ : syracuseStep 1910847 = 2866271) B2866271
theorem B2866277 : Blo 1909435 2866277 := bbase (se 4 (by rfl) ⟨268713, by rfl⟩ : syracuseStep 2866277 = 537427) (by norm_num)
theorem B1910851 : Blo 1909435 1910851 := bstep (se 1 (by rfl) ⟨1433138, by rfl⟩ : syracuseStep 1910851 = 2866277) B2866277
theorem B6886853 : Blo 1909435 6886853 := bbase (se 4 (by rfl) ⟨645642, by rfl⟩ : syracuseStep 6886853 = 1291285) (by norm_num)
theorem B4591235 : Blo 1909435 4591235 := bstep (se 1 (by rfl) ⟨3443426, by rfl⟩ : syracuseStep 4591235 = 6886853) B6886853
theorem B3060823 : Blo 1909435 3060823 := bstep (se 1 (by rfl) ⟨2295617, by rfl⟩ : syracuseStep 3060823 = 4591235) B4591235
theorem B4081097 : Blo 1909435 4081097 := bstep (se 2 (by rfl) ⟨1530411, by rfl⟩ : syracuseStep 4081097 = 3060823) B3060823
theorem B2720731 : Blo 1909435 2720731 := bstep (se 1 (by rfl) ⟨2040548, by rfl⟩ : syracuseStep 2720731 = 4081097) B4081097
theorem B3627641 : Blo 1909435 3627641 := bstep (se 2 (by rfl) ⟨1360365, by rfl⟩ : syracuseStep 3627641 = 2720731) B2720731
theorem B2418427 : Blo 1909435 2418427 := bstep (se 1 (by rfl) ⟨1813820, by rfl⟩ : syracuseStep 2418427 = 3627641) B3627641
theorem B3224569 : Blo 1909435 3224569 := bstep (se 2 (by rfl) ⟨1209213, by rfl⟩ : syracuseStep 3224569 = 2418427) B2418427
theorem B4299425 : Blo 1909435 4299425 := bstep (se 2 (by rfl) ⟨1612284, by rfl⟩ : syracuseStep 4299425 = 3224569) B3224569
theorem B2866283 : Blo 1909435 2866283 := bstep (se 1 (by rfl) ⟨2149712, by rfl⟩ : syracuseStep 2866283 = 4299425) B4299425
theorem B1910855 : Blo 1909435 1910855 := bstep (se 1 (by rfl) ⟨1433141, by rfl⟩ : syracuseStep 1910855 = 2866283) B2866283
theorem B2149717 : Blo 1909435 2149717 := bbase (se 11 (by rfl) ⟨1574, by rfl⟩ : syracuseStep 2149717 = 3149) (by norm_num)
theorem B2866289 : Blo 1909435 2866289 := bstep (se 2 (by rfl) ⟨1074858, by rfl⟩ : syracuseStep 2866289 = 2149717) B2149717
theorem B1910859 : Blo 1909435 1910859 := bstep (se 1 (by rfl) ⟨1433144, by rfl⟩ : syracuseStep 1910859 = 2866289) B2866289
theorem B2418437 : Blo 1909435 2418437 := bbase (se 4 (by rfl) ⟨226728, by rfl⟩ : syracuseStep 2418437 = 453457) (by norm_num)
theorem B6449165 : Blo 1909435 6449165 := bstep (se 3 (by rfl) ⟨1209218, by rfl⟩ : syracuseStep 6449165 = 2418437) B2418437
theorem B4299443 : Blo 1909435 4299443 := bstep (se 1 (by rfl) ⟨3224582, by rfl⟩ : syracuseStep 4299443 = 6449165) B6449165
theorem B2866295 : Blo 1909435 2866295 := bstep (se 1 (by rfl) ⟨2149721, by rfl⟩ : syracuseStep 2866295 = 4299443) B4299443
theorem B1910863 : Blo 1909435 1910863 := bstep (se 1 (by rfl) ⟨1433147, by rfl⟩ : syracuseStep 1910863 = 2866295) B2866295
theorem B2866301 : Blo 1909435 2866301 := bbase (se 3 (by rfl) ⟨537431, by rfl⟩ : syracuseStep 2866301 = 1074863) (by norm_num)
theorem B1910867 : Blo 1909435 1910867 := bstep (se 1 (by rfl) ⟨1433150, by rfl⟩ : syracuseStep 1910867 = 2866301) B2866301
theorem B4299461 : Blo 1909435 4299461 := bbase (se 4 (by rfl) ⟨403074, by rfl⟩ : syracuseStep 4299461 = 806149) (by norm_num)
theorem B2866307 : Blo 1909435 2866307 := bstep (se 1 (by rfl) ⟨2149730, by rfl⟩ : syracuseStep 2866307 = 4299461) B4299461
theorem B1910871 : Blo 1909435 1910871 := bstep (se 1 (by rfl) ⟨1433153, by rfl⟩ : syracuseStep 1910871 = 2866307) B2866307
theorem B2905421 : Blo 1909435 2905421 := bbase (se 3 (by rfl) ⟨544766, by rfl⟩ : syracuseStep 2905421 = 1089533) (by norm_num)
theorem B30991157 : Blo 1909435 30991157 := bstep (se 5 (by rfl) ⟨1452710, by rfl⟩ : syracuseStep 30991157 = 2905421) B2905421
theorem B20660771 : Blo 1909435 20660771 := bstep (se 1 (by rfl) ⟨15495578, by rfl⟩ : syracuseStep 20660771 = 30991157) B30991157
theorem B13773847 : Blo 1909435 13773847 := bstep (se 1 (by rfl) ⟨10330385, by rfl⟩ : syracuseStep 13773847 = 20660771) B20660771
theorem B18365129 : Blo 1909435 18365129 := bstep (se 2 (by rfl) ⟨6886923, by rfl⟩ : syracuseStep 18365129 = 13773847) B13773847
theorem B12243419 : Blo 1909435 12243419 := bstep (se 1 (by rfl) ⟨9182564, by rfl⟩ : syracuseStep 12243419 = 18365129) B18365129
theorem B8162279 : Blo 1909435 8162279 := bstep (se 1 (by rfl) ⟨6121709, by rfl⟩ : syracuseStep 8162279 = 12243419) B12243419
theorem B5441519 : Blo 1909435 5441519 := bstep (se 1 (by rfl) ⟨4081139, by rfl⟩ : syracuseStep 5441519 = 8162279) B8162279
theorem B3627679 : Blo 1909435 3627679 := bstep (se 1 (by rfl) ⟨2720759, by rfl⟩ : syracuseStep 3627679 = 5441519) B5441519
theorem B4836905 : Blo 1909435 4836905 := bstep (se 2 (by rfl) ⟨1813839, by rfl⟩ : syracuseStep 4836905 = 3627679) B3627679
theorem B3224603 : Blo 1909435 3224603 := bstep (se 1 (by rfl) ⟨2418452, by rfl⟩ : syracuseStep 3224603 = 4836905) B4836905
theorem B2149735 : Blo 1909435 2149735 := bstep (se 1 (by rfl) ⟨1612301, by rfl⟩ : syracuseStep 2149735 = 3224603) B3224603
theorem B2866313 : Blo 1909435 2866313 := bstep (se 2 (by rfl) ⟨1074867, by rfl⟩ : syracuseStep 2866313 = 2149735) B2149735
theorem B1910875 : Blo 1909435 1910875 := bstep (se 1 (by rfl) ⟨1433156, by rfl⟩ : syracuseStep 1910875 = 2866313) B2866313
theorem B9673829 : Blo 1909435 9673829 := bbase (se 4 (by rfl) ⟨906921, by rfl⟩ : syracuseStep 9673829 = 1813843) (by norm_num)
theorem B6449219 : Blo 1909435 6449219 := bstep (se 1 (by rfl) ⟨4836914, by rfl⟩ : syracuseStep 6449219 = 9673829) B9673829
theorem B4299479 : Blo 1909435 4299479 := bstep (se 1 (by rfl) ⟨3224609, by rfl⟩ : syracuseStep 4299479 = 6449219) B6449219
theorem B2866319 : Blo 1909435 2866319 := bstep (se 1 (by rfl) ⟨2149739, by rfl⟩ : syracuseStep 2866319 = 4299479) B4299479
theorem B1910879 : Blo 1909435 1910879 := bstep (se 1 (by rfl) ⟨1433159, by rfl⟩ : syracuseStep 1910879 = 2866319) B2866319
theorem B2866325 : Blo 1909435 2866325 := bbase (se 6 (by rfl) ⟨67179, by rfl⟩ : syracuseStep 2866325 = 134359) (by norm_num)
theorem B1910883 : Blo 1909435 1910883 := bstep (se 1 (by rfl) ⟨1433162, by rfl⟩ : syracuseStep 1910883 = 2866325) B2866325
theorem B8500997 : Blo 1909435 8500997 := bbase (se 4 (by rfl) ⟨796968, by rfl⟩ : syracuseStep 8500997 = 1593937) (by norm_num)
theorem B22669325 : Blo 1909435 22669325 := bstep (se 3 (by rfl) ⟨4250498, by rfl⟩ : syracuseStep 22669325 = 8500997) B8500997
theorem B15112883 : Blo 1909435 15112883 := bstep (se 1 (by rfl) ⟨11334662, by rfl⟩ : syracuseStep 15112883 = 22669325) B22669325
theorem B10075255 : Blo 1909435 10075255 := bstep (se 1 (by rfl) ⟨7556441, by rfl⟩ : syracuseStep 10075255 = 15112883) B15112883
theorem B53734693 : Blo 1909435 53734693 := bstep (se 4 (by rfl) ⟨5037627, by rfl⟩ : syracuseStep 53734693 = 10075255) B10075255
theorem B71646257 : Blo 1909435 71646257 := bstep (se 2 (by rfl) ⟨26867346, by rfl⟩ : syracuseStep 71646257 = 53734693) B53734693
theorem B47764171 : Blo 1909435 47764171 := bstep (se 1 (by rfl) ⟨35823128, by rfl⟩ : syracuseStep 47764171 = 71646257) B71646257
theorem B63685561 : Blo 1909435 63685561 := bstep (se 2 (by rfl) ⟨23882085, by rfl⟩ : syracuseStep 63685561 = 47764171) B47764171
theorem B84914081 : Blo 1909435 84914081 := bstep (se 2 (by rfl) ⟨31842780, by rfl⟩ : syracuseStep 84914081 = 63685561) B63685561
theorem B56609387 : Blo 1909435 56609387 := bstep (se 1 (by rfl) ⟨42457040, by rfl⟩ : syracuseStep 56609387 = 84914081) B84914081
theorem B37739591 : Blo 1909435 37739591 := bstep (se 1 (by rfl) ⟨28304693, by rfl⟩ : syracuseStep 37739591 = 56609387) B56609387
theorem B25159727 : Blo 1909435 25159727 := bstep (se 1 (by rfl) ⟨18869795, by rfl⟩ : syracuseStep 25159727 = 37739591) B37739591
theorem B16773151 : Blo 1909435 16773151 := bstep (se 1 (by rfl) ⟨12579863, by rfl⟩ : syracuseStep 16773151 = 25159727) B25159727
theorem B22364201 : Blo 1909435 22364201 := bstep (se 2 (by rfl) ⟨8386575, by rfl⟩ : syracuseStep 22364201 = 16773151) B16773151
theorem B59637869 : Blo 1909435 59637869 := bstep (se 3 (by rfl) ⟨11182100, by rfl⟩ : syracuseStep 59637869 = 22364201) B22364201
theorem B39758579 : Blo 1909435 39758579 := bstep (se 1 (by rfl) ⟨29818934, by rfl⟩ : syracuseStep 39758579 = 59637869) B59637869
theorem B26505719 : Blo 1909435 26505719 := bstep (se 1 (by rfl) ⟨19879289, by rfl⟩ : syracuseStep 26505719 = 39758579) B39758579
theorem B17670479 : Blo 1909435 17670479 := bstep (se 1 (by rfl) ⟨13252859, by rfl⟩ : syracuseStep 17670479 = 26505719) B26505719
theorem B47121277 : Blo 1909435 47121277 := bstep (se 3 (by rfl) ⟨8835239, by rfl⟩ : syracuseStep 47121277 = 17670479) B17670479
theorem B62828369 : Blo 1909435 62828369 := bstep (se 2 (by rfl) ⟨23560638, by rfl⟩ : syracuseStep 62828369 = 47121277) B47121277
theorem B41885579 : Blo 1909435 41885579 := bstep (se 1 (by rfl) ⟨31414184, by rfl⟩ : syracuseStep 41885579 = 62828369) B62828369
theorem B27923719 : Blo 1909435 27923719 := bstep (se 1 (by rfl) ⟨20942789, by rfl⟩ : syracuseStep 27923719 = 41885579) B41885579
theorem B37231625 : Blo 1909435 37231625 := bstep (se 2 (by rfl) ⟨13961859, by rfl⟩ : syracuseStep 37231625 = 27923719) B27923719
theorem B24821083 : Blo 1909435 24821083 := bstep (se 1 (by rfl) ⟨18615812, by rfl⟩ : syracuseStep 24821083 = 37231625) B37231625
theorem B33094777 : Blo 1909435 33094777 := bstep (se 2 (by rfl) ⟨12410541, by rfl⟩ : syracuseStep 33094777 = 24821083) B24821083
theorem B44126369 : Blo 1909435 44126369 := bstep (se 2 (by rfl) ⟨16547388, by rfl⟩ : syracuseStep 44126369 = 33094777) B33094777
theorem B29417579 : Blo 1909435 29417579 := bstep (se 1 (by rfl) ⟨22063184, by rfl⟩ : syracuseStep 29417579 = 44126369) B44126369
theorem B19611719 : Blo 1909435 19611719 := bstep (se 1 (by rfl) ⟨14708789, by rfl⟩ : syracuseStep 19611719 = 29417579) B29417579
theorem B13074479 : Blo 1909435 13074479 := bstep (se 1 (by rfl) ⟨9805859, by rfl⟩ : syracuseStep 13074479 = 19611719) B19611719
theorem B8716319 : Blo 1909435 8716319 := bstep (se 1 (by rfl) ⟨6537239, by rfl⟩ : syracuseStep 8716319 = 13074479) B13074479
theorem B5810879 : Blo 1909435 5810879 := bstep (se 1 (by rfl) ⟨4358159, by rfl⟩ : syracuseStep 5810879 = 8716319) B8716319
theorem B3873919 : Blo 1909435 3873919 := bstep (se 1 (by rfl) ⟨2905439, by rfl⟩ : syracuseStep 3873919 = 5810879) B5810879
theorem B5165225 : Blo 1909435 5165225 := bstep (se 2 (by rfl) ⟨1936959, by rfl⟩ : syracuseStep 5165225 = 3873919) B3873919
theorem B3443483 : Blo 1909435 3443483 := bstep (se 1 (by rfl) ⟨2582612, by rfl⟩ : syracuseStep 3443483 = 5165225) B5165225
theorem B9182621 : Blo 1909435 9182621 := bstep (se 3 (by rfl) ⟨1721741, by rfl⟩ : syracuseStep 9182621 = 3443483) B3443483
theorem B6121747 : Blo 1909435 6121747 := bstep (se 1 (by rfl) ⟨4591310, by rfl⟩ : syracuseStep 6121747 = 9182621) B9182621
theorem B8162329 : Blo 1909435 8162329 := bstep (se 2 (by rfl) ⟨3060873, by rfl⟩ : syracuseStep 8162329 = 6121747) B6121747
theorem B10883105 : Blo 1909435 10883105 := bstep (se 2 (by rfl) ⟨4081164, by rfl⟩ : syracuseStep 10883105 = 8162329) B8162329
theorem B7255403 : Blo 1909435 7255403 := bstep (se 1 (by rfl) ⟨5441552, by rfl⟩ : syracuseStep 7255403 = 10883105) B10883105
theorem B4836935 : Blo 1909435 4836935 := bstep (se 1 (by rfl) ⟨3627701, by rfl⟩ : syracuseStep 4836935 = 7255403) B7255403
theorem B3224623 : Blo 1909435 3224623 := bstep (se 1 (by rfl) ⟨2418467, by rfl⟩ : syracuseStep 3224623 = 4836935) B4836935
theorem B4299497 : Blo 1909435 4299497 := bstep (se 2 (by rfl) ⟨1612311, by rfl⟩ : syracuseStep 4299497 = 3224623) B3224623
theorem B2866331 : Blo 1909435 2866331 := bstep (se 1 (by rfl) ⟨2149748, by rfl⟩ : syracuseStep 2866331 = 4299497) B4299497
theorem B1910887 : Blo 1909435 1910887 := bstep (se 1 (by rfl) ⟨1433165, by rfl⟩ : syracuseStep 1910887 = 2866331) B2866331
theorem B2149753 : Blo 1909435 2149753 := bbase (se 2 (by rfl) ⟨806157, by rfl⟩ : syracuseStep 2149753 = 1612315) (by norm_num)
theorem B2866337 : Blo 1909435 2866337 := bstep (se 2 (by rfl) ⟨1074876, by rfl⟩ : syracuseStep 2866337 = 2149753) B2149753
theorem B1910891 : Blo 1909435 1910891 := bstep (se 1 (by rfl) ⟨1433168, by rfl⟩ : syracuseStep 1910891 = 2866337) B2866337
theorem B3677213 : Blo 1909435 3677213 := bbase (se 3 (by rfl) ⟨689477, by rfl⟩ : syracuseStep 3677213 = 1378955) (by norm_num)
theorem B2451475 : Blo 1909435 2451475 := bstep (se 1 (by rfl) ⟨1838606, by rfl⟩ : syracuseStep 2451475 = 3677213) B3677213
theorem B13074533 : Blo 1909435 13074533 := bstep (se 4 (by rfl) ⟨1225737, by rfl⟩ : syracuseStep 13074533 = 2451475) B2451475
theorem B8716355 : Blo 1909435 8716355 := bstep (se 1 (by rfl) ⟨6537266, by rfl⟩ : syracuseStep 8716355 = 13074533) B13074533
theorem B5810903 : Blo 1909435 5810903 := bstep (se 1 (by rfl) ⟨4358177, by rfl⟩ : syracuseStep 5810903 = 8716355) B8716355
theorem B3873935 : Blo 1909435 3873935 := bstep (se 1 (by rfl) ⟨2905451, by rfl⟩ : syracuseStep 3873935 = 5810903) B5810903
theorem B2582623 : Blo 1909435 2582623 := bstep (se 1 (by rfl) ⟨1936967, by rfl⟩ : syracuseStep 2582623 = 3873935) B3873935
theorem B13773989 : Blo 1909435 13773989 := bstep (se 4 (by rfl) ⟨1291311, by rfl⟩ : syracuseStep 13773989 = 2582623) B2582623
theorem B9182659 : Blo 1909435 9182659 := bstep (se 1 (by rfl) ⟨6886994, by rfl⟩ : syracuseStep 9182659 = 13773989) B13773989
theorem B12243545 : Blo 1909435 12243545 := bstep (se 2 (by rfl) ⟨4591329, by rfl⟩ : syracuseStep 12243545 = 9182659) B9182659
theorem B8162363 : Blo 1909435 8162363 := bstep (se 1 (by rfl) ⟨6121772, by rfl⟩ : syracuseStep 8162363 = 12243545) B12243545
theorem B5441575 : Blo 1909435 5441575 := bstep (se 1 (by rfl) ⟨4081181, by rfl⟩ : syracuseStep 5441575 = 8162363) B8162363
theorem B7255433 : Blo 1909435 7255433 := bstep (se 2 (by rfl) ⟨2720787, by rfl⟩ : syracuseStep 7255433 = 5441575) B5441575
theorem B4836955 : Blo 1909435 4836955 := bstep (se 1 (by rfl) ⟨3627716, by rfl⟩ : syracuseStep 4836955 = 7255433) B7255433
theorem B6449273 : Blo 1909435 6449273 := bstep (se 2 (by rfl) ⟨2418477, by rfl⟩ : syracuseStep 6449273 = 4836955) B4836955
theorem B4299515 : Blo 1909435 4299515 := bstep (se 1 (by rfl) ⟨3224636, by rfl⟩ : syracuseStep 4299515 = 6449273) B6449273
theorem B2866343 : Blo 1909435 2866343 := bstep (se 1 (by rfl) ⟨2149757, by rfl⟩ : syracuseStep 2866343 = 4299515) B4299515
theorem B1910895 : Blo 1909435 1910895 := bstep (se 1 (by rfl) ⟨1433171, by rfl⟩ : syracuseStep 1910895 = 2866343) B2866343
theorem B2866349 : Blo 1909435 2866349 := bbase (se 3 (by rfl) ⟨537440, by rfl⟩ : syracuseStep 2866349 = 1074881) (by norm_num)
theorem B1910899 : Blo 1909435 1910899 := bstep (se 1 (by rfl) ⟨1433174, by rfl⟩ : syracuseStep 1910899 = 2866349) B2866349
theorem B4299533 : Blo 1909435 4299533 := bbase (se 3 (by rfl) ⟨806162, by rfl⟩ : syracuseStep 4299533 = 1612325) (by norm_num)
theorem B2866355 : Blo 1909435 2866355 := bstep (se 1 (by rfl) ⟨2149766, by rfl⟩ : syracuseStep 2866355 = 4299533) B4299533
theorem B1910903 : Blo 1909435 1910903 := bstep (se 1 (by rfl) ⟨1433177, by rfl⟩ : syracuseStep 1910903 = 2866355) B2866355
theorem B2418493 : Blo 1909435 2418493 := bbase (se 3 (by rfl) ⟨453467, by rfl⟩ : syracuseStep 2418493 = 906935) (by norm_num)
theorem B3224657 : Blo 1909435 3224657 := bstep (se 2 (by rfl) ⟨1209246, by rfl⟩ : syracuseStep 3224657 = 2418493) B2418493
theorem B2149771 : Blo 1909435 2149771 := bstep (se 1 (by rfl) ⟨1612328, by rfl⟩ : syracuseStep 2149771 = 3224657) B3224657
theorem B2866361 : Blo 1909435 2866361 := bstep (se 2 (by rfl) ⟨1074885, by rfl⟩ : syracuseStep 2866361 = 2149771) B2149771
theorem B1910907 : Blo 1909435 1910907 := bstep (se 1 (by rfl) ⟨1433180, by rfl⟩ : syracuseStep 1910907 = 2866361) B2866361
theorem B4358213 : Blo 1909435 4358213 := bbase (se 4 (by rfl) ⟨408582, by rfl⟩ : syracuseStep 4358213 = 817165) (by norm_num)
theorem B2905475 : Blo 1909435 2905475 := bstep (se 1 (by rfl) ⟨2179106, by rfl⟩ : syracuseStep 2905475 = 4358213) B4358213
theorem B30991733 : Blo 1909435 30991733 := bstep (se 5 (by rfl) ⟨1452737, by rfl⟩ : syracuseStep 30991733 = 2905475) B2905475
theorem B20661155 : Blo 1909435 20661155 := bstep (se 1 (by rfl) ⟨15495866, by rfl⟩ : syracuseStep 20661155 = 30991733) B30991733
theorem B13774103 : Blo 1909435 13774103 := bstep (se 1 (by rfl) ⟨10330577, by rfl⟩ : syracuseStep 13774103 = 20661155) B20661155
theorem B9182735 : Blo 1909435 9182735 := bstep (se 1 (by rfl) ⟨6887051, by rfl⟩ : syracuseStep 9182735 = 13774103) B13774103
theorem B6121823 : Blo 1909435 6121823 := bstep (se 1 (by rfl) ⟨4591367, by rfl⟩ : syracuseStep 6121823 = 9182735) B9182735
theorem B16324861 : Blo 1909435 16324861 := bstep (se 3 (by rfl) ⟨3060911, by rfl⟩ : syracuseStep 16324861 = 6121823) B6121823
theorem B21766481 : Blo 1909435 21766481 := bstep (se 2 (by rfl) ⟨8162430, by rfl⟩ : syracuseStep 21766481 = 16324861) B16324861
theorem B14510987 : Blo 1909435 14510987 := bstep (se 1 (by rfl) ⟨10883240, by rfl⟩ : syracuseStep 14510987 = 21766481) B21766481
theorem B9673991 : Blo 1909435 9673991 := bstep (se 1 (by rfl) ⟨7255493, by rfl⟩ : syracuseStep 9673991 = 14510987) B14510987
theorem B6449327 : Blo 1909435 6449327 := bstep (se 1 (by rfl) ⟨4836995, by rfl⟩ : syracuseStep 6449327 = 9673991) B9673991
theorem B4299551 : Blo 1909435 4299551 := bstep (se 1 (by rfl) ⟨3224663, by rfl⟩ : syracuseStep 4299551 = 6449327) B6449327
theorem B2866367 : Blo 1909435 2866367 := bstep (se 1 (by rfl) ⟨2149775, by rfl⟩ : syracuseStep 2866367 = 4299551) B4299551
theorem B1910911 : Blo 1909435 1910911 := bstep (se 1 (by rfl) ⟨1433183, by rfl⟩ : syracuseStep 1910911 = 2866367) B2866367
theorem B2866373 : Blo 1909435 2866373 := bbase (se 4 (by rfl) ⟨268722, by rfl⟩ : syracuseStep 2866373 = 537445) (by norm_num)
theorem B1910915 : Blo 1909435 1910915 := bstep (se 1 (by rfl) ⟨1433186, by rfl⟩ : syracuseStep 1910915 = 2866373) B2866373
theorem B3224677 : Blo 1909435 3224677 := bbase (se 4 (by rfl) ⟨302313, by rfl⟩ : syracuseStep 3224677 = 604627) (by norm_num)
theorem B4299569 : Blo 1909435 4299569 := bstep (se 2 (by rfl) ⟨1612338, by rfl⟩ : syracuseStep 4299569 = 3224677) B3224677
theorem B2866379 : Blo 1909435 2866379 := bstep (se 1 (by rfl) ⟨2149784, by rfl⟩ : syracuseStep 2866379 = 4299569) B4299569
theorem B1910919 : Blo 1909435 1910919 := bstep (se 1 (by rfl) ⟨1433189, by rfl⟩ : syracuseStep 1910919 = 2866379) B2866379
theorem B2149789 : Blo 1909435 2149789 := bbase (se 3 (by rfl) ⟨403085, by rfl⟩ : syracuseStep 2149789 = 806171) (by norm_num)
theorem B2866385 : Blo 1909435 2866385 := bstep (se 2 (by rfl) ⟨1074894, by rfl⟩ : syracuseStep 2866385 = 2149789) B2149789
theorem B1910923 : Blo 1909435 1910923 := bstep (se 1 (by rfl) ⟨1433192, by rfl⟩ : syracuseStep 1910923 = 2866385) B2866385
theorem B6449381 : Blo 1909435 6449381 := bbase (se 4 (by rfl) ⟨604629, by rfl⟩ : syracuseStep 6449381 = 1209259) (by norm_num)
theorem B4299587 : Blo 1909435 4299587 := bstep (se 1 (by rfl) ⟨3224690, by rfl⟩ : syracuseStep 4299587 = 6449381) B6449381
theorem B2866391 : Blo 1909435 2866391 := bstep (se 1 (by rfl) ⟨2149793, by rfl⟩ : syracuseStep 2866391 = 4299587) B4299587
theorem B1910927 : Blo 1909435 1910927 := bstep (se 1 (by rfl) ⟨1433195, by rfl⟩ : syracuseStep 1910927 = 2866391) B2866391
theorem B2866397 : Blo 1909435 2866397 := bbase (se 3 (by rfl) ⟨537449, by rfl⟩ : syracuseStep 2866397 = 1074899) (by norm_num)
theorem B1910931 : Blo 1909435 1910931 := bstep (se 1 (by rfl) ⟨1433198, by rfl⟩ : syracuseStep 1910931 = 2866397) B2866397
theorem B4299605 : Blo 1909435 4299605 := bbase (se 9 (by rfl) ⟨12596, by rfl⟩ : syracuseStep 4299605 = 25193) (by norm_num)
theorem B2866403 : Blo 1909435 2866403 := bstep (se 1 (by rfl) ⟨2149802, by rfl⟩ : syracuseStep 2866403 = 4299605) B4299605
theorem B1910935 : Blo 1909435 1910935 := bstep (se 1 (by rfl) ⟨1433201, by rfl⟩ : syracuseStep 1910935 = 2866403) B2866403
theorem B5441701 : Blo 1909435 5441701 := bbase (se 4 (by rfl) ⟨510159, by rfl⟩ : syracuseStep 5441701 = 1020319) (by norm_num)
theorem B7255601 : Blo 1909435 7255601 := bstep (se 2 (by rfl) ⟨2720850, by rfl⟩ : syracuseStep 7255601 = 5441701) B5441701
theorem B4837067 : Blo 1909435 4837067 := bstep (se 1 (by rfl) ⟨3627800, by rfl⟩ : syracuseStep 4837067 = 7255601) B7255601
theorem B3224711 : Blo 1909435 3224711 := bstep (se 1 (by rfl) ⟨2418533, by rfl⟩ : syracuseStep 3224711 = 4837067) B4837067
theorem B2149807 : Blo 1909435 2149807 := bstep (se 1 (by rfl) ⟨1612355, by rfl⟩ : syracuseStep 2149807 = 3224711) B3224711
theorem B2866409 : Blo 1909435 2866409 := bstep (se 2 (by rfl) ⟨1074903, by rfl⟩ : syracuseStep 2866409 = 2149807) B2149807
theorem B1910939 : Blo 1909435 1910939 := bstep (se 1 (by rfl) ⟨1433204, by rfl⟩ : syracuseStep 1910939 = 2866409) B2866409
theorem B4478021 : Blo 1909435 4478021 := bbase (se 4 (by rfl) ⟨419814, by rfl⟩ : syracuseStep 4478021 = 839629) (by norm_num)
theorem B2985347 : Blo 1909435 2985347 := bstep (se 1 (by rfl) ⟨2239010, by rfl⟩ : syracuseStep 2985347 = 4478021) B4478021
theorem B7960925 : Blo 1909435 7960925 := bstep (se 3 (by rfl) ⟨1492673, by rfl⟩ : syracuseStep 7960925 = 2985347) B2985347
theorem B21229133 : Blo 1909435 21229133 := bstep (se 3 (by rfl) ⟨3980462, by rfl⟩ : syracuseStep 21229133 = 7960925) B7960925
theorem B226444085 : Blo 1909435 226444085 := bstep (se 5 (by rfl) ⟨10614566, by rfl⟩ : syracuseStep 226444085 = 21229133) B21229133
theorem B150962723 : Blo 1909435 150962723 := bstep (se 1 (by rfl) ⟨113222042, by rfl⟩ : syracuseStep 150962723 = 226444085) B226444085
theorem B100641815 : Blo 1909435 100641815 := bstep (se 1 (by rfl) ⟨75481361, by rfl⟩ : syracuseStep 100641815 = 150962723) B150962723
theorem B67094543 : Blo 1909435 67094543 := bstep (se 1 (by rfl) ⟨50320907, by rfl⟩ : syracuseStep 67094543 = 100641815) B100641815
theorem B44729695 : Blo 1909435 44729695 := bstep (se 1 (by rfl) ⟨33547271, by rfl⟩ : syracuseStep 44729695 = 67094543) B67094543
theorem B59639593 : Blo 1909435 59639593 := bstep (se 2 (by rfl) ⟨22364847, by rfl⟩ : syracuseStep 59639593 = 44729695) B44729695
theorem B79519457 : Blo 1909435 79519457 := bstep (se 2 (by rfl) ⟨29819796, by rfl⟩ : syracuseStep 79519457 = 59639593) B59639593
theorem B53012971 : Blo 1909435 53012971 := bstep (se 1 (by rfl) ⟨39759728, by rfl⟩ : syracuseStep 53012971 = 79519457) B79519457
theorem B70683961 : Blo 1909435 70683961 := bstep (se 2 (by rfl) ⟨26506485, by rfl⟩ : syracuseStep 70683961 = 53012971) B53012971
theorem B94245281 : Blo 1909435 94245281 := bstep (se 2 (by rfl) ⟨35341980, by rfl⟩ : syracuseStep 94245281 = 70683961) B70683961
theorem B62830187 : Blo 1909435 62830187 := bstep (se 1 (by rfl) ⟨47122640, by rfl⟩ : syracuseStep 62830187 = 94245281) B94245281
theorem B41886791 : Blo 1909435 41886791 := bstep (se 1 (by rfl) ⟨31415093, by rfl⟩ : syracuseStep 41886791 = 62830187) B62830187
theorem B27924527 : Blo 1909435 27924527 := bstep (se 1 (by rfl) ⟨20943395, by rfl⟩ : syracuseStep 27924527 = 41886791) B41886791
theorem B74465405 : Blo 1909435 74465405 := bstep (se 3 (by rfl) ⟨13962263, by rfl⟩ : syracuseStep 74465405 = 27924527) B27924527
theorem B49643603 : Blo 1909435 49643603 := bstep (se 1 (by rfl) ⟨37232702, by rfl⟩ : syracuseStep 49643603 = 74465405) B74465405
theorem B33095735 : Blo 1909435 33095735 := bstep (se 1 (by rfl) ⟨24821801, by rfl⟩ : syracuseStep 33095735 = 49643603) B49643603
theorem B22063823 : Blo 1909435 22063823 := bstep (se 1 (by rfl) ⟨16547867, by rfl⟩ : syracuseStep 22063823 = 33095735) B33095735
theorem B14709215 : Blo 1909435 14709215 := bstep (se 1 (by rfl) ⟨11031911, by rfl⟩ : syracuseStep 14709215 = 22063823) B22063823
theorem B39224573 : Blo 1909435 39224573 := bstep (se 3 (by rfl) ⟨7354607, by rfl⟩ : syracuseStep 39224573 = 14709215) B14709215
theorem B26149715 : Blo 1909435 26149715 := bstep (se 1 (by rfl) ⟨19612286, by rfl⟩ : syracuseStep 26149715 = 39224573) B39224573
theorem B17433143 : Blo 1909435 17433143 := bstep (se 1 (by rfl) ⟨13074857, by rfl⟩ : syracuseStep 17433143 = 26149715) B26149715
theorem B11622095 : Blo 1909435 11622095 := bstep (se 1 (by rfl) ⟨8716571, by rfl⟩ : syracuseStep 11622095 = 17433143) B17433143
theorem B7748063 : Blo 1909435 7748063 := bstep (se 1 (by rfl) ⟨5811047, by rfl⟩ : syracuseStep 7748063 = 11622095) B11622095
theorem B5165375 : Blo 1909435 5165375 := bstep (se 1 (by rfl) ⟨3874031, by rfl⟩ : syracuseStep 5165375 = 7748063) B7748063
theorem B55097333 : Blo 1909435 55097333 := bstep (se 5 (by rfl) ⟨2582687, by rfl⟩ : syracuseStep 55097333 = 5165375) B5165375
theorem B36731555 : Blo 1909435 36731555 := bstep (se 1 (by rfl) ⟨27548666, by rfl⟩ : syracuseStep 36731555 = 55097333) B55097333
theorem B24487703 : Blo 1909435 24487703 := bstep (se 1 (by rfl) ⟨18365777, by rfl⟩ : syracuseStep 24487703 = 36731555) B36731555
theorem B16325135 : Blo 1909435 16325135 := bstep (se 1 (by rfl) ⟨12243851, by rfl⟩ : syracuseStep 16325135 = 24487703) B24487703
theorem B10883423 : Blo 1909435 10883423 := bstep (se 1 (by rfl) ⟨8162567, by rfl⟩ : syracuseStep 10883423 = 16325135) B16325135
theorem B7255615 : Blo 1909435 7255615 := bstep (se 1 (by rfl) ⟨5441711, by rfl⟩ : syracuseStep 7255615 = 10883423) B10883423
theorem B9674153 : Blo 1909435 9674153 := bstep (se 2 (by rfl) ⟨3627807, by rfl⟩ : syracuseStep 9674153 = 7255615) B7255615
theorem B6449435 : Blo 1909435 6449435 := bstep (se 1 (by rfl) ⟨4837076, by rfl⟩ : syracuseStep 6449435 = 9674153) B9674153
theorem B4299623 : Blo 1909435 4299623 := bstep (se 1 (by rfl) ⟨3224717, by rfl⟩ : syracuseStep 4299623 = 6449435) B6449435
theorem B2866415 : Blo 1909435 2866415 := bstep (se 1 (by rfl) ⟨2149811, by rfl⟩ : syracuseStep 2866415 = 4299623) B4299623
theorem B1910943 : Blo 1909435 1910943 := bstep (se 1 (by rfl) ⟨1433207, by rfl⟩ : syracuseStep 1910943 = 2866415) B2866415
theorem B2866421 : Blo 1909435 2866421 := bbase (se 5 (by rfl) ⟨134363, by rfl⟩ : syracuseStep 2866421 = 268727) (by norm_num)
theorem B1910947 : Blo 1909435 1910947 := bstep (se 1 (by rfl) ⟨1433210, by rfl⟩ : syracuseStep 1910947 = 2866421) B2866421
theorem B2179153 : Blo 1909435 2179153 := bbase (se 2 (by rfl) ⟨817182, by rfl⟩ : syracuseStep 2179153 = 1634365) (by norm_num)
theorem B2905537 : Blo 1909435 2905537 := bstep (se 2 (by rfl) ⟨1089576, by rfl⟩ : syracuseStep 2905537 = 2179153) B2179153
theorem B3874049 : Blo 1909435 3874049 := bstep (se 2 (by rfl) ⟨1452768, by rfl⟩ : syracuseStep 3874049 = 2905537) B2905537
theorem B2582699 : Blo 1909435 2582699 := bstep (se 1 (by rfl) ⟨1937024, by rfl⟩ : syracuseStep 2582699 = 3874049) B3874049
theorem B6887197 : Blo 1909435 6887197 := bstep (se 3 (by rfl) ⟨1291349, by rfl⟩ : syracuseStep 6887197 = 2582699) B2582699
theorem B9182929 : Blo 1909435 9182929 := bstep (se 2 (by rfl) ⟨3443598, by rfl⟩ : syracuseStep 9182929 = 6887197) B6887197
theorem B12243905 : Blo 1909435 12243905 := bstep (se 2 (by rfl) ⟨4591464, by rfl⟩ : syracuseStep 12243905 = 9182929) B9182929
theorem B8162603 : Blo 1909435 8162603 := bstep (se 1 (by rfl) ⟨6121952, by rfl⟩ : syracuseStep 8162603 = 12243905) B12243905
theorem B5441735 : Blo 1909435 5441735 := bstep (se 1 (by rfl) ⟨4081301, by rfl⟩ : syracuseStep 5441735 = 8162603) B8162603
theorem B3627823 : Blo 1909435 3627823 := bstep (se 1 (by rfl) ⟨2720867, by rfl⟩ : syracuseStep 3627823 = 5441735) B5441735
theorem B4837097 : Blo 1909435 4837097 := bstep (se 2 (by rfl) ⟨1813911, by rfl⟩ : syracuseStep 4837097 = 3627823) B3627823
theorem B3224731 : Blo 1909435 3224731 := bstep (se 1 (by rfl) ⟨2418548, by rfl⟩ : syracuseStep 3224731 = 4837097) B4837097
theorem B4299641 : Blo 1909435 4299641 := bstep (se 2 (by rfl) ⟨1612365, by rfl⟩ : syracuseStep 4299641 = 3224731) B3224731
theorem B2866427 : Blo 1909435 2866427 := bstep (se 1 (by rfl) ⟨2149820, by rfl⟩ : syracuseStep 2866427 = 4299641) B4299641
theorem B1910951 : Blo 1909435 1910951 := bstep (se 1 (by rfl) ⟨1433213, by rfl⟩ : syracuseStep 1910951 = 2866427) B2866427
theorem B2149825 : Blo 1909435 2149825 := bbase (se 2 (by rfl) ⟨806184, by rfl⟩ : syracuseStep 2149825 = 1612369) (by norm_num)
theorem B2866433 : Blo 1909435 2866433 := bstep (se 2 (by rfl) ⟨1074912, by rfl⟩ : syracuseStep 2866433 = 2149825) B2149825
theorem B1910955 : Blo 1909435 1910955 := bstep (se 1 (by rfl) ⟨1433216, by rfl⟩ : syracuseStep 1910955 = 2866433) B2866433
theorem B4837117 : Blo 1909435 4837117 := bbase (se 3 (by rfl) ⟨906959, by rfl⟩ : syracuseStep 4837117 = 1813919) (by norm_num)
theorem B6449489 : Blo 1909435 6449489 := bstep (se 2 (by rfl) ⟨2418558, by rfl⟩ : syracuseStep 6449489 = 4837117) B4837117
theorem B4299659 : Blo 1909435 4299659 := bstep (se 1 (by rfl) ⟨3224744, by rfl⟩ : syracuseStep 4299659 = 6449489) B6449489
theorem B2866439 : Blo 1909435 2866439 := bstep (se 1 (by rfl) ⟨2149829, by rfl⟩ : syracuseStep 2866439 = 4299659) B4299659
theorem B1910959 : Blo 1909435 1910959 := bstep (se 1 (by rfl) ⟨1433219, by rfl⟩ : syracuseStep 1910959 = 2866439) B2866439
theorem B2866445 : Blo 1909435 2866445 := bbase (se 3 (by rfl) ⟨537458, by rfl⟩ : syracuseStep 2866445 = 1074917) (by norm_num)
theorem B1910963 : Blo 1909435 1910963 := bstep (se 1 (by rfl) ⟨1433222, by rfl⟩ : syracuseStep 1910963 = 2866445) B2866445
theorem B4299677 : Blo 1909435 4299677 := bbase (se 3 (by rfl) ⟨806189, by rfl⟩ : syracuseStep 4299677 = 1612379) (by norm_num)
theorem B2866451 : Blo 1909435 2866451 := bstep (se 1 (by rfl) ⟨2149838, by rfl⟩ : syracuseStep 2866451 = 4299677) B4299677
theorem B1910967 : Blo 1909435 1910967 := bstep (se 1 (by rfl) ⟨1433225, by rfl⟩ : syracuseStep 1910967 = 2866451) B2866451
theorem B3224765 : Blo 1909435 3224765 := bbase (se 3 (by rfl) ⟨604643, by rfl⟩ : syracuseStep 3224765 = 1209287) (by norm_num)
theorem B2149843 : Blo 1909435 2149843 := bstep (se 1 (by rfl) ⟨1612382, by rfl⟩ : syracuseStep 2149843 = 3224765) B3224765
theorem B2866457 : Blo 1909435 2866457 := bstep (se 2 (by rfl) ⟨1074921, by rfl⟩ : syracuseStep 2866457 = 2149843) B2149843
theorem B1910971 : Blo 1909435 1910971 := bstep (se 1 (by rfl) ⟨1433228, by rfl⟩ : syracuseStep 1910971 = 2866457) B2866457
theorem B10883605 : Blo 1909435 10883605 := bbase (se 6 (by rfl) ⟨255084, by rfl⟩ : syracuseStep 10883605 = 510169) (by norm_num)
theorem B14511473 : Blo 1909435 14511473 := bstep (se 2 (by rfl) ⟨5441802, by rfl⟩ : syracuseStep 14511473 = 10883605) B10883605
theorem B9674315 : Blo 1909435 9674315 := bstep (se 1 (by rfl) ⟨7255736, by rfl⟩ : syracuseStep 9674315 = 14511473) B14511473
theorem B6449543 : Blo 1909435 6449543 := bstep (se 1 (by rfl) ⟨4837157, by rfl⟩ : syracuseStep 6449543 = 9674315) B9674315
theorem B4299695 : Blo 1909435 4299695 := bstep (se 1 (by rfl) ⟨3224771, by rfl⟩ : syracuseStep 4299695 = 6449543) B6449543
theorem B2866463 : Blo 1909435 2866463 := bstep (se 1 (by rfl) ⟨2149847, by rfl⟩ : syracuseStep 2866463 = 4299695) B4299695
theorem B1910975 : Blo 1909435 1910975 := bstep (se 1 (by rfl) ⟨1433231, by rfl⟩ : syracuseStep 1910975 = 2866463) B2866463
theorem B2866469 : Blo 1909435 2866469 := bbase (se 4 (by rfl) ⟨268731, by rfl⟩ : syracuseStep 2866469 = 537463) (by norm_num)
theorem B1910979 : Blo 1909435 1910979 := bstep (se 1 (by rfl) ⟨1433234, by rfl⟩ : syracuseStep 1910979 = 2866469) B2866469
theorem B2418589 : Blo 1909435 2418589 := bbase (se 3 (by rfl) ⟨453485, by rfl⟩ : syracuseStep 2418589 = 906971) (by norm_num)
theorem B3224785 : Blo 1909435 3224785 := bstep (se 2 (by rfl) ⟨1209294, by rfl⟩ : syracuseStep 3224785 = 2418589) B2418589
theorem B4299713 : Blo 1909435 4299713 := bstep (se 2 (by rfl) ⟨1612392, by rfl⟩ : syracuseStep 4299713 = 3224785) B3224785
theorem B2866475 : Blo 1909435 2866475 := bstep (se 1 (by rfl) ⟨2149856, by rfl⟩ : syracuseStep 2866475 = 4299713) B4299713
theorem B1910983 : Blo 1909435 1910983 := bstep (se 1 (by rfl) ⟨1433237, by rfl⟩ : syracuseStep 1910983 = 2866475) B2866475
theorem B2149861 : Blo 1909435 2149861 := bbase (se 4 (by rfl) ⟨201549, by rfl⟩ : syracuseStep 2149861 = 403099) (by norm_num)
theorem B2866481 : Blo 1909435 2866481 := bstep (se 2 (by rfl) ⟨1074930, by rfl⟩ : syracuseStep 2866481 = 2149861) B2149861
theorem B1910987 : Blo 1909435 1910987 := bstep (se 1 (by rfl) ⟨1433240, by rfl⟩ : syracuseStep 1910987 = 2866481) B2866481
theorem B7748261 : Blo 1909435 7748261 := bbase (se 4 (by rfl) ⟨726399, by rfl⟩ : syracuseStep 7748261 = 1452799) (by norm_num)
theorem B5165507 : Blo 1909435 5165507 := bstep (se 1 (by rfl) ⟨3874130, by rfl⟩ : syracuseStep 5165507 = 7748261) B7748261
theorem B3443671 : Blo 1909435 3443671 := bstep (se 1 (by rfl) ⟨2582753, by rfl⟩ : syracuseStep 3443671 = 5165507) B5165507
theorem B4591561 : Blo 1909435 4591561 := bstep (se 2 (by rfl) ⟨1721835, by rfl⟩ : syracuseStep 4591561 = 3443671) B3443671
theorem B6122081 : Blo 1909435 6122081 := bstep (se 2 (by rfl) ⟨2295780, by rfl⟩ : syracuseStep 6122081 = 4591561) B4591561
theorem B4081387 : Blo 1909435 4081387 := bstep (se 1 (by rfl) ⟨3061040, by rfl⟩ : syracuseStep 4081387 = 6122081) B6122081
theorem B5441849 : Blo 1909435 5441849 := bstep (se 2 (by rfl) ⟨2040693, by rfl⟩ : syracuseStep 5441849 = 4081387) B4081387
theorem B3627899 : Blo 1909435 3627899 := bstep (se 1 (by rfl) ⟨2720924, by rfl⟩ : syracuseStep 3627899 = 5441849) B5441849
theorem B2418599 : Blo 1909435 2418599 := bstep (se 1 (by rfl) ⟨1813949, by rfl⟩ : syracuseStep 2418599 = 3627899) B3627899
theorem B6449597 : Blo 1909435 6449597 := bstep (se 3 (by rfl) ⟨1209299, by rfl⟩ : syracuseStep 6449597 = 2418599) B2418599
theorem B4299731 : Blo 1909435 4299731 := bstep (se 1 (by rfl) ⟨3224798, by rfl⟩ : syracuseStep 4299731 = 6449597) B6449597
theorem B2866487 : Blo 1909435 2866487 := bstep (se 1 (by rfl) ⟨2149865, by rfl⟩ : syracuseStep 2866487 = 4299731) B4299731
theorem B1910991 : Blo 1909435 1910991 := bstep (se 1 (by rfl) ⟨1433243, by rfl⟩ : syracuseStep 1910991 = 2866487) B2866487
theorem B2866493 : Blo 1909435 2866493 := bbase (se 3 (by rfl) ⟨537467, by rfl⟩ : syracuseStep 2866493 = 1074935) (by norm_num)
theorem B1910995 : Blo 1909435 1910995 := bstep (se 1 (by rfl) ⟨1433246, by rfl⟩ : syracuseStep 1910995 = 2866493) B2866493
theorem B4299749 : Blo 1909435 4299749 := bbase (se 4 (by rfl) ⟨403101, by rfl⟩ : syracuseStep 4299749 = 806203) (by norm_num)
theorem B2866499 : Blo 1909435 2866499 := bstep (se 1 (by rfl) ⟨2149874, by rfl⟩ : syracuseStep 2866499 = 4299749) B4299749
theorem B1910999 : Blo 1909435 1910999 := bstep (se 1 (by rfl) ⟨1433249, by rfl⟩ : syracuseStep 1910999 = 2866499) B2866499
theorem B4837229 : Blo 1909435 4837229 := bbase (se 3 (by rfl) ⟨906980, by rfl⟩ : syracuseStep 4837229 = 1813961) (by norm_num)
theorem B3224819 : Blo 1909435 3224819 := bstep (se 1 (by rfl) ⟨2418614, by rfl⟩ : syracuseStep 3224819 = 4837229) B4837229
theorem B2149879 : Blo 1909435 2149879 := bstep (se 1 (by rfl) ⟨1612409, by rfl⟩ : syracuseStep 2149879 = 3224819) B3224819
theorem B2866505 : Blo 1909435 2866505 := bstep (se 2 (by rfl) ⟨1074939, by rfl⟩ : syracuseStep 2866505 = 2149879) B2149879
theorem B1911003 : Blo 1909435 1911003 := bstep (se 1 (by rfl) ⟨1433252, by rfl⟩ : syracuseStep 1911003 = 2866505) B2866505
theorem B4081421 : Blo 1909435 4081421 := bbase (se 3 (by rfl) ⟨765266, by rfl⟩ : syracuseStep 4081421 = 1530533) (by norm_num)
theorem B2720947 : Blo 1909435 2720947 := bstep (se 1 (by rfl) ⟨2040710, by rfl⟩ : syracuseStep 2720947 = 4081421) B4081421
theorem B3627929 : Blo 1909435 3627929 := bstep (se 2 (by rfl) ⟨1360473, by rfl⟩ : syracuseStep 3627929 = 2720947) B2720947
theorem B9674477 : Blo 1909435 9674477 := bstep (se 3 (by rfl) ⟨1813964, by rfl⟩ : syracuseStep 9674477 = 3627929) B3627929
theorem B6449651 : Blo 1909435 6449651 := bstep (se 1 (by rfl) ⟨4837238, by rfl⟩ : syracuseStep 6449651 = 9674477) B9674477
theorem B4299767 : Blo 1909435 4299767 := bstep (se 1 (by rfl) ⟨3224825, by rfl⟩ : syracuseStep 4299767 = 6449651) B6449651
theorem B2866511 : Blo 1909435 2866511 := bstep (se 1 (by rfl) ⟨2149883, by rfl⟩ : syracuseStep 2866511 = 4299767) B4299767
theorem B1911007 : Blo 1909435 1911007 := bstep (se 1 (by rfl) ⟨1433255, by rfl⟩ : syracuseStep 1911007 = 2866511) B2866511
theorem B2866517 : Blo 1909435 2866517 := bbase (se 11 (by rfl) ⟨2099, by rfl⟩ : syracuseStep 2866517 = 4199) (by norm_num)
theorem B1911011 : Blo 1909435 1911011 := bstep (se 1 (by rfl) ⟨1433258, by rfl⟩ : syracuseStep 1911011 = 2866517) B2866517
theorem B6887429 : Blo 1909435 6887429 := bbase (se 4 (by rfl) ⟨645696, by rfl⟩ : syracuseStep 6887429 = 1291393) (by norm_num)
theorem B4591619 : Blo 1909435 4591619 := bstep (se 1 (by rfl) ⟨3443714, by rfl⟩ : syracuseStep 4591619 = 6887429) B6887429
theorem B3061079 : Blo 1909435 3061079 := bstep (se 1 (by rfl) ⟨2295809, by rfl⟩ : syracuseStep 3061079 = 4591619) B4591619
theorem B2040719 : Blo 1909435 2040719 := bstep (se 1 (by rfl) ⟨1530539, by rfl⟩ : syracuseStep 2040719 = 3061079) B3061079
theorem B5441917 : Blo 1909435 5441917 := bstep (se 3 (by rfl) ⟨1020359, by rfl⟩ : syracuseStep 5441917 = 2040719) B2040719
theorem B7255889 : Blo 1909435 7255889 := bstep (se 2 (by rfl) ⟨2720958, by rfl⟩ : syracuseStep 7255889 = 5441917) B5441917
theorem B4837259 : Blo 1909435 4837259 := bstep (se 1 (by rfl) ⟨3627944, by rfl⟩ : syracuseStep 4837259 = 7255889) B7255889
theorem B3224839 : Blo 1909435 3224839 := bstep (se 1 (by rfl) ⟨2418629, by rfl⟩ : syracuseStep 3224839 = 4837259) B4837259
theorem B4299785 : Blo 1909435 4299785 := bstep (se 2 (by rfl) ⟨1612419, by rfl⟩ : syracuseStep 4299785 = 3224839) B3224839
theorem B2866523 : Blo 1909435 2866523 := bstep (se 1 (by rfl) ⟨2149892, by rfl⟩ : syracuseStep 2866523 = 4299785) B4299785
theorem B1911015 : Blo 1909435 1911015 := bstep (se 1 (by rfl) ⟨1433261, by rfl⟩ : syracuseStep 1911015 = 2866523) B2866523
theorem B2149897 : Blo 1909435 2149897 := bbase (se 2 (by rfl) ⟨806211, by rfl⟩ : syracuseStep 2149897 = 1612423) (by norm_num)
theorem B2866529 : Blo 1909435 2866529 := bstep (se 2 (by rfl) ⟨1074948, by rfl⟩ : syracuseStep 2866529 = 2149897) B2149897
theorem B1911019 : Blo 1909435 1911019 := bstep (se 1 (by rfl) ⟨1433264, by rfl⟩ : syracuseStep 1911019 = 2866529) B2866529
theorem B11032373 : Blo 1909435 11032373 := bbase (se 5 (by rfl) ⟨517142, by rfl⟩ : syracuseStep 11032373 = 1034285) (by norm_num)
theorem B29419661 : Blo 1909435 29419661 := bstep (se 3 (by rfl) ⟨5516186, by rfl⟩ : syracuseStep 29419661 = 11032373) B11032373
theorem B19613107 : Blo 1909435 19613107 := bstep (se 1 (by rfl) ⟨14709830, by rfl⟩ : syracuseStep 19613107 = 29419661) B29419661
theorem B26150809 : Blo 1909435 26150809 := bstep (se 2 (by rfl) ⟨9806553, by rfl⟩ : syracuseStep 26150809 = 19613107) B19613107
theorem B34867745 : Blo 1909435 34867745 := bstep (se 2 (by rfl) ⟨13075404, by rfl⟩ : syracuseStep 34867745 = 26150809) B26150809
theorem B23245163 : Blo 1909435 23245163 := bstep (se 1 (by rfl) ⟨17433872, by rfl⟩ : syracuseStep 23245163 = 34867745) B34867745
theorem B15496775 : Blo 1909435 15496775 := bstep (se 1 (by rfl) ⟨11622581, by rfl⟩ : syracuseStep 15496775 = 23245163) B23245163
theorem B10331183 : Blo 1909435 10331183 := bstep (se 1 (by rfl) ⟨7748387, by rfl⟩ : syracuseStep 10331183 = 15496775) B15496775
theorem B27549821 : Blo 1909435 27549821 := bstep (se 3 (by rfl) ⟨5165591, by rfl⟩ : syracuseStep 27549821 = 10331183) B10331183
theorem B18366547 : Blo 1909435 18366547 := bstep (se 1 (by rfl) ⟨13774910, by rfl⟩ : syracuseStep 18366547 = 27549821) B27549821
theorem B24488729 : Blo 1909435 24488729 := bstep (se 2 (by rfl) ⟨9183273, by rfl⟩ : syracuseStep 24488729 = 18366547) B18366547
theorem B16325819 : Blo 1909435 16325819 := bstep (se 1 (by rfl) ⟨12244364, by rfl⟩ : syracuseStep 16325819 = 24488729) B24488729
theorem B10883879 : Blo 1909435 10883879 := bstep (se 1 (by rfl) ⟨8162909, by rfl⟩ : syracuseStep 10883879 = 16325819) B16325819
theorem B7255919 : Blo 1909435 7255919 := bstep (se 1 (by rfl) ⟨5441939, by rfl⟩ : syracuseStep 7255919 = 10883879) B10883879
theorem B4837279 : Blo 1909435 4837279 := bstep (se 1 (by rfl) ⟨3627959, by rfl⟩ : syracuseStep 4837279 = 7255919) B7255919
theorem B6449705 : Blo 1909435 6449705 := bstep (se 2 (by rfl) ⟨2418639, by rfl⟩ : syracuseStep 6449705 = 4837279) B4837279
theorem B4299803 : Blo 1909435 4299803 := bstep (se 1 (by rfl) ⟨3224852, by rfl⟩ : syracuseStep 4299803 = 6449705) B6449705
theorem B2866535 : Blo 1909435 2866535 := bstep (se 1 (by rfl) ⟨2149901, by rfl⟩ : syracuseStep 2866535 = 4299803) B4299803
theorem B1911023 : Blo 1909435 1911023 := bstep (se 1 (by rfl) ⟨1433267, by rfl⟩ : syracuseStep 1911023 = 2866535) B2866535
theorem B2866541 : Blo 1909435 2866541 := bbase (se 3 (by rfl) ⟨537476, by rfl⟩ : syracuseStep 2866541 = 1074953) (by norm_num)
theorem B1911027 : Blo 1909435 1911027 := bstep (se 1 (by rfl) ⟨1433270, by rfl⟩ : syracuseStep 1911027 = 2866541) B2866541
theorem B4299821 : Blo 1909435 4299821 := bbase (se 3 (by rfl) ⟨806216, by rfl⟩ : syracuseStep 4299821 = 1612433) (by norm_num)
theorem B2866547 : Blo 1909435 2866547 := bstep (se 1 (by rfl) ⟨2149910, by rfl⟩ : syracuseStep 2866547 = 4299821) B4299821
theorem B1911031 : Blo 1909435 1911031 := bstep (se 1 (by rfl) ⟨1433273, by rfl⟩ : syracuseStep 1911031 = 2866547) B2866547
theorem B2582813 : Blo 1909435 2582813 := bbase (se 3 (by rfl) ⟨484277, by rfl⟩ : syracuseStep 2582813 = 968555) (by norm_num)
theorem B6887501 : Blo 1909435 6887501 := bstep (se 3 (by rfl) ⟨1291406, by rfl⟩ : syracuseStep 6887501 = 2582813) B2582813
theorem B4591667 : Blo 1909435 4591667 := bstep (se 1 (by rfl) ⟨3443750, by rfl⟩ : syracuseStep 4591667 = 6887501) B6887501
theorem B12244445 : Blo 1909435 12244445 := bstep (se 3 (by rfl) ⟨2295833, by rfl⟩ : syracuseStep 12244445 = 4591667) B4591667
theorem B8162963 : Blo 1909435 8162963 := bstep (se 1 (by rfl) ⟨6122222, by rfl⟩ : syracuseStep 8162963 = 12244445) B12244445
theorem B5441975 : Blo 1909435 5441975 := bstep (se 1 (by rfl) ⟨4081481, by rfl⟩ : syracuseStep 5441975 = 8162963) B8162963
theorem B3627983 : Blo 1909435 3627983 := bstep (se 1 (by rfl) ⟨2720987, by rfl⟩ : syracuseStep 3627983 = 5441975) B5441975
theorem B2418655 : Blo 1909435 2418655 := bstep (se 1 (by rfl) ⟨1813991, by rfl⟩ : syracuseStep 2418655 = 3627983) B3627983
theorem B3224873 : Blo 1909435 3224873 := bstep (se 2 (by rfl) ⟨1209327, by rfl⟩ : syracuseStep 3224873 = 2418655) B2418655
theorem B2149915 : Blo 1909435 2149915 := bstep (se 1 (by rfl) ⟨1612436, by rfl⟩ : syracuseStep 2149915 = 3224873) B3224873
theorem B2866553 : Blo 1909435 2866553 := bstep (se 2 (by rfl) ⟨1074957, by rfl⟩ : syracuseStep 2866553 = 2149915) B2149915
theorem B1911035 : Blo 1909435 1911035 := bstep (se 1 (by rfl) ⟨1433276, by rfl⟩ : syracuseStep 1911035 = 2866553) B2866553
theorem B7748453 : Blo 1909435 7748453 := bbase (se 4 (by rfl) ⟨726417, by rfl⟩ : syracuseStep 7748453 = 1452835) (by norm_num)
theorem B5165635 : Blo 1909435 5165635 := bstep (se 1 (by rfl) ⟨3874226, by rfl⟩ : syracuseStep 5165635 = 7748453) B7748453
theorem B6887513 : Blo 1909435 6887513 := bstep (se 2 (by rfl) ⟨2582817, by rfl⟩ : syracuseStep 6887513 = 5165635) B5165635
theorem B4591675 : Blo 1909435 4591675 := bstep (se 1 (by rfl) ⟨3443756, by rfl⟩ : syracuseStep 4591675 = 6887513) B6887513
theorem B6122233 : Blo 1909435 6122233 := bstep (se 2 (by rfl) ⟨2295837, by rfl⟩ : syracuseStep 6122233 = 4591675) B4591675
theorem B32651909 : Blo 1909435 32651909 := bstep (se 4 (by rfl) ⟨3061116, by rfl⟩ : syracuseStep 32651909 = 6122233) B6122233
theorem B21767939 : Blo 1909435 21767939 := bstep (se 1 (by rfl) ⟨16325954, by rfl⟩ : syracuseStep 21767939 = 32651909) B32651909
theorem B14511959 : Blo 1909435 14511959 := bstep (se 1 (by rfl) ⟨10883969, by rfl⟩ : syracuseStep 14511959 = 21767939) B21767939
theorem B9674639 : Blo 1909435 9674639 := bstep (se 1 (by rfl) ⟨7255979, by rfl⟩ : syracuseStep 9674639 = 14511959) B14511959
theorem B6449759 : Blo 1909435 6449759 := bstep (se 1 (by rfl) ⟨4837319, by rfl⟩ : syracuseStep 6449759 = 9674639) B9674639
theorem B4299839 : Blo 1909435 4299839 := bstep (se 1 (by rfl) ⟨3224879, by rfl⟩ : syracuseStep 4299839 = 6449759) B6449759
theorem B2866559 : Blo 1909435 2866559 := bstep (se 1 (by rfl) ⟨2149919, by rfl⟩ : syracuseStep 2866559 = 4299839) B4299839
theorem B1911039 : Blo 1909435 1911039 := bstep (se 1 (by rfl) ⟨1433279, by rfl⟩ : syracuseStep 1911039 = 2866559) B2866559
theorem B2866565 : Blo 1909435 2866565 := bbase (se 4 (by rfl) ⟨268740, by rfl⟩ : syracuseStep 2866565 = 537481) (by norm_num)
theorem B1911043 : Blo 1909435 1911043 := bstep (se 1 (by rfl) ⟨1433282, by rfl⟩ : syracuseStep 1911043 = 2866565) B2866565
theorem B3224893 : Blo 1909435 3224893 := bbase (se 3 (by rfl) ⟨604667, by rfl⟩ : syracuseStep 3224893 = 1209335) (by norm_num)
theorem B4299857 : Blo 1909435 4299857 := bstep (se 2 (by rfl) ⟨1612446, by rfl⟩ : syracuseStep 4299857 = 3224893) B3224893
theorem B2866571 : Blo 1909435 2866571 := bstep (se 1 (by rfl) ⟨2149928, by rfl⟩ : syracuseStep 2866571 = 4299857) B4299857
theorem B1911047 : Blo 1909435 1911047 := bstep (se 1 (by rfl) ⟨1433285, by rfl⟩ : syracuseStep 1911047 = 2866571) B2866571
theorem B2149933 : Blo 1909435 2149933 := bbase (se 3 (by rfl) ⟨403112, by rfl⟩ : syracuseStep 2149933 = 806225) (by norm_num)
theorem B2866577 : Blo 1909435 2866577 := bstep (se 2 (by rfl) ⟨1074966, by rfl⟩ : syracuseStep 2866577 = 2149933) B2149933
theorem B1911051 : Blo 1909435 1911051 := bstep (se 1 (by rfl) ⟨1433288, by rfl⟩ : syracuseStep 1911051 = 2866577) B2866577
theorem B6449813 : Blo 1909435 6449813 := bbase (se 6 (by rfl) ⟨151167, by rfl⟩ : syracuseStep 6449813 = 302335) (by norm_num)
theorem B4299875 : Blo 1909435 4299875 := bstep (se 1 (by rfl) ⟨3224906, by rfl⟩ : syracuseStep 4299875 = 6449813) B6449813
theorem B2866583 : Blo 1909435 2866583 := bstep (se 1 (by rfl) ⟨2149937, by rfl⟩ : syracuseStep 2866583 = 4299875) B4299875
theorem B1911055 : Blo 1909435 1911055 := bstep (se 1 (by rfl) ⟨1433291, by rfl⟩ : syracuseStep 1911055 = 2866583) B2866583
theorem B2866589 : Blo 1909435 2866589 := bbase (se 3 (by rfl) ⟨537485, by rfl⟩ : syracuseStep 2866589 = 1074971) (by norm_num)
theorem B1911059 : Blo 1909435 1911059 := bstep (se 1 (by rfl) ⟨1433294, by rfl⟩ : syracuseStep 1911059 = 2866589) B2866589
theorem B4299893 : Blo 1909435 4299893 := bbase (se 5 (by rfl) ⟨201557, by rfl⟩ : syracuseStep 4299893 = 403115) (by norm_num)
theorem B2866595 : Blo 1909435 2866595 := bstep (se 1 (by rfl) ⟨2149946, by rfl⟩ : syracuseStep 2866595 = 4299893) B4299893
theorem B1911063 : Blo 1909435 1911063 := bstep (se 1 (by rfl) ⟨1433297, by rfl⟩ : syracuseStep 1911063 = 2866595) B2866595
theorem B16326197 : Blo 1909435 16326197 := bbase (se 5 (by rfl) ⟨765290, by rfl⟩ : syracuseStep 16326197 = 1530581) (by norm_num)
theorem B10884131 : Blo 1909435 10884131 := bstep (se 1 (by rfl) ⟨8163098, by rfl⟩ : syracuseStep 10884131 = 16326197) B16326197
theorem B7256087 : Blo 1909435 7256087 := bstep (se 1 (by rfl) ⟨5442065, by rfl⟩ : syracuseStep 7256087 = 10884131) B10884131
theorem B4837391 : Blo 1909435 4837391 := bstep (se 1 (by rfl) ⟨3628043, by rfl⟩ : syracuseStep 4837391 = 7256087) B7256087
theorem B3224927 : Blo 1909435 3224927 := bstep (se 1 (by rfl) ⟨2418695, by rfl⟩ : syracuseStep 3224927 = 4837391) B4837391
theorem B2149951 : Blo 1909435 2149951 := bstep (se 1 (by rfl) ⟨1612463, by rfl⟩ : syracuseStep 2149951 = 3224927) B3224927
theorem B2866601 : Blo 1909435 2866601 := bstep (se 2 (by rfl) ⟨1074975, by rfl⟩ : syracuseStep 2866601 = 2149951) B2149951
theorem B1911067 : Blo 1909435 1911067 := bstep (se 1 (by rfl) ⟨1433300, by rfl⟩ : syracuseStep 1911067 = 2866601) B2866601
theorem B7256101 : Blo 1909435 7256101 := bbase (se 4 (by rfl) ⟨680259, by rfl⟩ : syracuseStep 7256101 = 1360519) (by norm_num)
theorem B9674801 : Blo 1909435 9674801 := bstep (se 2 (by rfl) ⟨3628050, by rfl⟩ : syracuseStep 9674801 = 7256101) B7256101
theorem B6449867 : Blo 1909435 6449867 := bstep (se 1 (by rfl) ⟨4837400, by rfl⟩ : syracuseStep 6449867 = 9674801) B9674801
theorem B4299911 : Blo 1909435 4299911 := bstep (se 1 (by rfl) ⟨3224933, by rfl⟩ : syracuseStep 4299911 = 6449867) B6449867
theorem B2866607 : Blo 1909435 2866607 := bstep (se 1 (by rfl) ⟨2149955, by rfl⟩ : syracuseStep 2866607 = 4299911) B4299911
theorem B1911071 : Blo 1909435 1911071 := bstep (se 1 (by rfl) ⟨1433303, by rfl⟩ : syracuseStep 1911071 = 2866607) B2866607
theorem B2866613 : Blo 1909435 2866613 := bbase (se 5 (by rfl) ⟨134372, by rfl⟩ : syracuseStep 2866613 = 268745) (by norm_num)
theorem B1911075 : Blo 1909435 1911075 := bstep (se 1 (by rfl) ⟨1433306, by rfl⟩ : syracuseStep 1911075 = 2866613) B2866613
theorem B4837421 : Blo 1909435 4837421 := bbase (se 3 (by rfl) ⟨907016, by rfl⟩ : syracuseStep 4837421 = 1814033) (by norm_num)
theorem B3224947 : Blo 1909435 3224947 := bstep (se 1 (by rfl) ⟨2418710, by rfl⟩ : syracuseStep 3224947 = 4837421) B4837421
theorem B4299929 : Blo 1909435 4299929 := bstep (se 2 (by rfl) ⟨1612473, by rfl⟩ : syracuseStep 4299929 = 3224947) B3224947
theorem B2866619 : Blo 1909435 2866619 := bstep (se 1 (by rfl) ⟨2149964, by rfl⟩ : syracuseStep 2866619 = 4299929) B4299929
theorem B1911079 : Blo 1909435 1911079 := bstep (se 1 (by rfl) ⟨1433309, by rfl⟩ : syracuseStep 1911079 = 2866619) B2866619
theorem B2149969 : Blo 1909435 2149969 := bbase (se 2 (by rfl) ⟨806238, by rfl⟩ : syracuseStep 2149969 = 1612477) (by norm_num)
theorem B2866625 : Blo 1909435 2866625 := bstep (se 2 (by rfl) ⟨1074984, by rfl⟩ : syracuseStep 2866625 = 2149969) B2149969
theorem B1911083 : Blo 1909435 1911083 := bstep (se 1 (by rfl) ⟨1433312, by rfl⟩ : syracuseStep 1911083 = 2866625) B2866625
theorem B2721061 : Blo 1909435 2721061 := bbase (se 4 (by rfl) ⟨255099, by rfl⟩ : syracuseStep 2721061 = 510199) (by norm_num)
theorem B3628081 : Blo 1909435 3628081 := bstep (se 2 (by rfl) ⟨1360530, by rfl⟩ : syracuseStep 3628081 = 2721061) B2721061
theorem B4837441 : Blo 1909435 4837441 := bstep (se 2 (by rfl) ⟨1814040, by rfl⟩ : syracuseStep 4837441 = 3628081) B3628081
theorem B6449921 : Blo 1909435 6449921 := bstep (se 2 (by rfl) ⟨2418720, by rfl⟩ : syracuseStep 6449921 = 4837441) B4837441
theorem B4299947 : Blo 1909435 4299947 := bstep (se 1 (by rfl) ⟨3224960, by rfl⟩ : syracuseStep 4299947 = 6449921) B6449921
theorem B2866631 : Blo 1909435 2866631 := bstep (se 1 (by rfl) ⟨2149973, by rfl⟩ : syracuseStep 2866631 = 4299947) B4299947
theorem B1911087 : Blo 1909435 1911087 := bstep (se 1 (by rfl) ⟨1433315, by rfl⟩ : syracuseStep 1911087 = 2866631) B2866631
theorem B2866637 : Blo 1909435 2866637 := bbase (se 3 (by rfl) ⟨537494, by rfl⟩ : syracuseStep 2866637 = 1074989) (by norm_num)
theorem B1911091 : Blo 1909435 1911091 := bstep (se 1 (by rfl) ⟨1433318, by rfl⟩ : syracuseStep 1911091 = 2866637) B2866637
theorem B4299965 : Blo 1909435 4299965 := bbase (se 3 (by rfl) ⟨806243, by rfl⟩ : syracuseStep 4299965 = 1612487) (by norm_num)
theorem B2866643 : Blo 1909435 2866643 := bstep (se 1 (by rfl) ⟨2149982, by rfl⟩ : syracuseStep 2866643 = 4299965) B4299965
theorem B1911095 : Blo 1909435 1911095 := bstep (se 1 (by rfl) ⟨1433321, by rfl⟩ : syracuseStep 1911095 = 2866643) B2866643
theorem B3224981 : Blo 1909435 3224981 := bbase (se 6 (by rfl) ⟨75585, by rfl⟩ : syracuseStep 3224981 = 151171) (by norm_num)
theorem B2149987 : Blo 1909435 2149987 := bstep (se 1 (by rfl) ⟨1612490, by rfl⟩ : syracuseStep 2149987 = 3224981) B3224981
theorem B2866649 : Blo 1909435 2866649 := bstep (se 2 (by rfl) ⟨1074993, by rfl⟩ : syracuseStep 2866649 = 2149987) B2149987
theorem B1911099 : Blo 1909435 1911099 := bstep (se 1 (by rfl) ⟨1433324, by rfl⟩ : syracuseStep 1911099 = 2866649) B2866649
theorem B4591829 : Blo 1909435 4591829 := bbase (se 7 (by rfl) ⟨53810, by rfl⟩ : syracuseStep 4591829 = 107621) (by norm_num)
theorem B12244877 : Blo 1909435 12244877 := bstep (se 3 (by rfl) ⟨2295914, by rfl⟩ : syracuseStep 12244877 = 4591829) B4591829
theorem B8163251 : Blo 1909435 8163251 := bstep (se 1 (by rfl) ⟨6122438, by rfl⟩ : syracuseStep 8163251 = 12244877) B12244877
theorem B5442167 : Blo 1909435 5442167 := bstep (se 1 (by rfl) ⟨4081625, by rfl⟩ : syracuseStep 5442167 = 8163251) B8163251
theorem B14512445 : Blo 1909435 14512445 := bstep (se 3 (by rfl) ⟨2721083, by rfl⟩ : syracuseStep 14512445 = 5442167) B5442167
theorem B9674963 : Blo 1909435 9674963 := bstep (se 1 (by rfl) ⟨7256222, by rfl⟩ : syracuseStep 9674963 = 14512445) B14512445
theorem B6449975 : Blo 1909435 6449975 := bstep (se 1 (by rfl) ⟨4837481, by rfl⟩ : syracuseStep 6449975 = 9674963) B9674963
theorem B4299983 : Blo 1909435 4299983 := bstep (se 1 (by rfl) ⟨3224987, by rfl⟩ : syracuseStep 4299983 = 6449975) B6449975
theorem B2866655 : Blo 1909435 2866655 := bstep (se 1 (by rfl) ⟨2149991, by rfl⟩ : syracuseStep 2866655 = 4299983) B4299983
theorem B1911103 : Blo 1909435 1911103 := bstep (se 1 (by rfl) ⟨1433327, by rfl⟩ : syracuseStep 1911103 = 2866655) B2866655
theorem B2866661 : Blo 1909435 2866661 := bbase (se 4 (by rfl) ⟨268749, by rfl⟩ : syracuseStep 2866661 = 537499) (by norm_num)
theorem B1911107 : Blo 1909435 1911107 := bstep (se 1 (by rfl) ⟨1433330, by rfl⟩ : syracuseStep 1911107 = 2866661) B2866661
theorem B3677629 : Blo 1909435 3677629 := bbase (se 3 (by rfl) ⟨689555, by rfl⟩ : syracuseStep 3677629 = 1379111) (by norm_num)
theorem B4903505 : Blo 1909435 4903505 := bstep (se 2 (by rfl) ⟨1838814, by rfl⟩ : syracuseStep 4903505 = 3677629) B3677629
theorem B3269003 : Blo 1909435 3269003 := bstep (se 1 (by rfl) ⟨2451752, by rfl⟩ : syracuseStep 3269003 = 4903505) B4903505
theorem B8717341 : Blo 1909435 8717341 := bstep (se 3 (by rfl) ⟨1634501, by rfl⟩ : syracuseStep 8717341 = 3269003) B3269003
theorem B11623121 : Blo 1909435 11623121 := bstep (se 2 (by rfl) ⟨4358670, by rfl⟩ : syracuseStep 11623121 = 8717341) B8717341
theorem B7748747 : Blo 1909435 7748747 := bstep (se 1 (by rfl) ⟨5811560, by rfl⟩ : syracuseStep 7748747 = 11623121) B11623121
theorem B5165831 : Blo 1909435 5165831 := bstep (se 1 (by rfl) ⟨3874373, by rfl⟩ : syracuseStep 5165831 = 7748747) B7748747
theorem B3443887 : Blo 1909435 3443887 := bstep (se 1 (by rfl) ⟨2582915, by rfl⟩ : syracuseStep 3443887 = 5165831) B5165831
theorem B18367397 : Blo 1909435 18367397 := bstep (se 4 (by rfl) ⟨1721943, by rfl⟩ : syracuseStep 18367397 = 3443887) B3443887
theorem B12244931 : Blo 1909435 12244931 := bstep (se 1 (by rfl) ⟨9183698, by rfl⟩ : syracuseStep 12244931 = 18367397) B18367397
theorem B8163287 : Blo 1909435 8163287 := bstep (se 1 (by rfl) ⟨6122465, by rfl⟩ : syracuseStep 8163287 = 12244931) B12244931
theorem B5442191 : Blo 1909435 5442191 := bstep (se 1 (by rfl) ⟨4081643, by rfl⟩ : syracuseStep 5442191 = 8163287) B8163287
theorem B3628127 : Blo 1909435 3628127 := bstep (se 1 (by rfl) ⟨2721095, by rfl⟩ : syracuseStep 3628127 = 5442191) B5442191
theorem B2418751 : Blo 1909435 2418751 := bstep (se 1 (by rfl) ⟨1814063, by rfl⟩ : syracuseStep 2418751 = 3628127) B3628127
theorem B3225001 : Blo 1909435 3225001 := bstep (se 2 (by rfl) ⟨1209375, by rfl⟩ : syracuseStep 3225001 = 2418751) B2418751
theorem B4300001 : Blo 1909435 4300001 := bstep (se 2 (by rfl) ⟨1612500, by rfl⟩ : syracuseStep 4300001 = 3225001) B3225001
theorem B2866667 : Blo 1909435 2866667 := bstep (se 1 (by rfl) ⟨2150000, by rfl⟩ : syracuseStep 2866667 = 4300001) B4300001
theorem B1911111 : Blo 1909435 1911111 := bstep (se 1 (by rfl) ⟨1433333, by rfl⟩ : syracuseStep 1911111 = 2866667) B2866667
theorem B2150005 : Blo 1909435 2150005 := bbase (se 5 (by rfl) ⟨100781, by rfl⟩ : syracuseStep 2150005 = 201563) (by norm_num)
theorem B2866673 : Blo 1909435 2866673 := bstep (se 2 (by rfl) ⟨1075002, by rfl⟩ : syracuseStep 2866673 = 2150005) B2150005
theorem B1911115 : Blo 1909435 1911115 := bstep (se 1 (by rfl) ⟨1433336, by rfl⟩ : syracuseStep 1911115 = 2866673) B2866673
theorem B2418761 : Blo 1909435 2418761 := bbase (se 2 (by rfl) ⟨907035, by rfl⟩ : syracuseStep 2418761 = 1814071) (by norm_num)
theorem B6450029 : Blo 1909435 6450029 := bstep (se 3 (by rfl) ⟨1209380, by rfl⟩ : syracuseStep 6450029 = 2418761) B2418761
theorem B4300019 : Blo 1909435 4300019 := bstep (se 1 (by rfl) ⟨3225014, by rfl⟩ : syracuseStep 4300019 = 6450029) B6450029
theorem B2866679 : Blo 1909435 2866679 := bstep (se 1 (by rfl) ⟨2150009, by rfl⟩ : syracuseStep 2866679 = 4300019) B4300019
theorem B1911119 : Blo 1909435 1911119 := bstep (se 1 (by rfl) ⟨1433339, by rfl⟩ : syracuseStep 1911119 = 2866679) B2866679
theorem B2866685 : Blo 1909435 2866685 := bbase (se 3 (by rfl) ⟨537503, by rfl⟩ : syracuseStep 2866685 = 1075007) (by norm_num)
theorem B1911123 : Blo 1909435 1911123 := bstep (se 1 (by rfl) ⟨1433342, by rfl⟩ : syracuseStep 1911123 = 2866685) B2866685
theorem B4300037 : Blo 1909435 4300037 := bbase (se 4 (by rfl) ⟨403128, by rfl⟩ : syracuseStep 4300037 = 806257) (by norm_num)
theorem B2866691 : Blo 1909435 2866691 := bstep (se 1 (by rfl) ⟨2150018, by rfl⟩ : syracuseStep 2866691 = 4300037) B4300037
theorem B1911127 : Blo 1909435 1911127 := bstep (se 1 (by rfl) ⟨1433345, by rfl⟩ : syracuseStep 1911127 = 2866691) B2866691
theorem B3628165 : Blo 1909435 3628165 := bbase (se 4 (by rfl) ⟨340140, by rfl⟩ : syracuseStep 3628165 = 680281) (by norm_num)
theorem B4837553 : Blo 1909435 4837553 := bstep (se 2 (by rfl) ⟨1814082, by rfl⟩ : syracuseStep 4837553 = 3628165) B3628165
theorem B3225035 : Blo 1909435 3225035 := bstep (se 1 (by rfl) ⟨2418776, by rfl⟩ : syracuseStep 3225035 = 4837553) B4837553
theorem B2150023 : Blo 1909435 2150023 := bstep (se 1 (by rfl) ⟨1612517, by rfl⟩ : syracuseStep 2150023 = 3225035) B3225035
theorem B2866697 : Blo 1909435 2866697 := bstep (se 2 (by rfl) ⟨1075011, by rfl⟩ : syracuseStep 2866697 = 2150023) B2150023
theorem B1911131 : Blo 1909435 1911131 := bstep (se 1 (by rfl) ⟨1433348, by rfl⟩ : syracuseStep 1911131 = 2866697) B2866697
theorem B9675125 : Blo 1909435 9675125 := bbase (se 5 (by rfl) ⟨453521, by rfl⟩ : syracuseStep 9675125 = 907043) (by norm_num)
theorem B6450083 : Blo 1909435 6450083 := bstep (se 1 (by rfl) ⟨4837562, by rfl⟩ : syracuseStep 6450083 = 9675125) B9675125
theorem B4300055 : Blo 1909435 4300055 := bstep (se 1 (by rfl) ⟨3225041, by rfl⟩ : syracuseStep 4300055 = 6450083) B6450083
theorem B2866703 : Blo 1909435 2866703 := bstep (se 1 (by rfl) ⟨2150027, by rfl⟩ : syracuseStep 2866703 = 4300055) B4300055
theorem B1911135 : Blo 1909435 1911135 := bstep (se 1 (by rfl) ⟨1433351, by rfl⟩ : syracuseStep 1911135 = 2866703) B2866703
theorem B2866709 : Blo 1909435 2866709 := bbase (se 6 (by rfl) ⟨67188, by rfl⟩ : syracuseStep 2866709 = 134377) (by norm_num)
theorem B1911139 : Blo 1909435 1911139 := bstep (se 1 (by rfl) ⟨1433354, by rfl⟩ : syracuseStep 1911139 = 2866709) B2866709
theorem B2451793 : Blo 1909435 2451793 := bbase (se 2 (by rfl) ⟨919422, by rfl⟩ : syracuseStep 2451793 = 1838845) (by norm_num)
theorem B3269057 : Blo 1909435 3269057 := bstep (se 2 (by rfl) ⟨1225896, by rfl⟩ : syracuseStep 3269057 = 2451793) B2451793
theorem B8717485 : Blo 1909435 8717485 := bstep (se 3 (by rfl) ⟨1634528, by rfl⟩ : syracuseStep 8717485 = 3269057) B3269057
theorem B11623313 : Blo 1909435 11623313 := bstep (se 2 (by rfl) ⟨4358742, by rfl⟩ : syracuseStep 11623313 = 8717485) B8717485
theorem B7748875 : Blo 1909435 7748875 := bstep (se 1 (by rfl) ⟨5811656, by rfl⟩ : syracuseStep 7748875 = 11623313) B11623313
theorem B10331833 : Blo 1909435 10331833 := bstep (se 2 (by rfl) ⟨3874437, by rfl⟩ : syracuseStep 10331833 = 7748875) B7748875
theorem B13775777 : Blo 1909435 13775777 := bstep (se 2 (by rfl) ⟨5165916, by rfl⟩ : syracuseStep 13775777 = 10331833) B10331833
theorem B9183851 : Blo 1909435 9183851 := bstep (se 1 (by rfl) ⟨6887888, by rfl⟩ : syracuseStep 9183851 = 13775777) B13775777
theorem B6122567 : Blo 1909435 6122567 := bstep (se 1 (by rfl) ⟨4591925, by rfl⟩ : syracuseStep 6122567 = 9183851) B9183851
theorem B16326845 : Blo 1909435 16326845 := bstep (se 3 (by rfl) ⟨3061283, by rfl⟩ : syracuseStep 16326845 = 6122567) B6122567
theorem B10884563 : Blo 1909435 10884563 := bstep (se 1 (by rfl) ⟨8163422, by rfl⟩ : syracuseStep 10884563 = 16326845) B16326845
theorem B7256375 : Blo 1909435 7256375 := bstep (se 1 (by rfl) ⟨5442281, by rfl⟩ : syracuseStep 7256375 = 10884563) B10884563
theorem B4837583 : Blo 1909435 4837583 := bstep (se 1 (by rfl) ⟨3628187, by rfl⟩ : syracuseStep 4837583 = 7256375) B7256375
theorem B3225055 : Blo 1909435 3225055 := bstep (se 1 (by rfl) ⟨2418791, by rfl⟩ : syracuseStep 3225055 = 4837583) B4837583
theorem B4300073 : Blo 1909435 4300073 := bstep (se 2 (by rfl) ⟨1612527, by rfl⟩ : syracuseStep 4300073 = 3225055) B3225055
theorem B2866715 : Blo 1909435 2866715 := bstep (se 1 (by rfl) ⟨2150036, by rfl⟩ : syracuseStep 2866715 = 4300073) B4300073
theorem B1911143 : Blo 1909435 1911143 := bstep (se 1 (by rfl) ⟨1433357, by rfl⟩ : syracuseStep 1911143 = 2866715) B2866715
theorem B2150041 : Blo 1909435 2150041 := bbase (se 2 (by rfl) ⟨806265, by rfl⟩ : syracuseStep 2150041 = 1612531) (by norm_num)
theorem B2866721 : Blo 1909435 2866721 := bstep (se 2 (by rfl) ⟨1075020, by rfl⟩ : syracuseStep 2866721 = 2150041) B2150041
theorem B1911147 : Blo 1909435 1911147 := bstep (se 1 (by rfl) ⟨1433360, by rfl⟩ : syracuseStep 1911147 = 2866721) B2866721
theorem B7256405 : Blo 1909435 7256405 := bbase (se 10 (by rfl) ⟨10629, by rfl⟩ : syracuseStep 7256405 = 21259) (by norm_num)
theorem B4837603 : Blo 1909435 4837603 := bstep (se 1 (by rfl) ⟨3628202, by rfl⟩ : syracuseStep 4837603 = 7256405) B7256405
theorem B6450137 : Blo 1909435 6450137 := bstep (se 2 (by rfl) ⟨2418801, by rfl⟩ : syracuseStep 6450137 = 4837603) B4837603
theorem B4300091 : Blo 1909435 4300091 := bstep (se 1 (by rfl) ⟨3225068, by rfl⟩ : syracuseStep 4300091 = 6450137) B6450137
theorem B2866727 : Blo 1909435 2866727 := bstep (se 1 (by rfl) ⟨2150045, by rfl⟩ : syracuseStep 2866727 = 4300091) B4300091
theorem B1911151 : Blo 1909435 1911151 := bstep (se 1 (by rfl) ⟨1433363, by rfl⟩ : syracuseStep 1911151 = 2866727) B2866727
theorem B2866733 : Blo 1909435 2866733 := bbase (se 3 (by rfl) ⟨537512, by rfl⟩ : syracuseStep 2866733 = 1075025) (by norm_num)
theorem B1911155 : Blo 1909435 1911155 := bstep (se 1 (by rfl) ⟨1433366, by rfl⟩ : syracuseStep 1911155 = 2866733) B2866733
theorem B4300109 : Blo 1909435 4300109 := bbase (se 3 (by rfl) ⟨806270, by rfl⟩ : syracuseStep 4300109 = 1612541) (by norm_num)
theorem B2866739 : Blo 1909435 2866739 := bstep (se 1 (by rfl) ⟨2150054, by rfl⟩ : syracuseStep 2866739 = 4300109) B4300109
theorem B1911159 : Blo 1909435 1911159 := bstep (se 1 (by rfl) ⟨1433369, by rfl⟩ : syracuseStep 1911159 = 2866739) B2866739
theorem B2418817 : Blo 1909435 2418817 := bbase (se 2 (by rfl) ⟨907056, by rfl⟩ : syracuseStep 2418817 = 1814113) (by norm_num)
theorem B3225089 : Blo 1909435 3225089 := bstep (se 2 (by rfl) ⟨1209408, by rfl⟩ : syracuseStep 3225089 = 2418817) B2418817
theorem B2150059 : Blo 1909435 2150059 := bstep (se 1 (by rfl) ⟨1612544, by rfl⟩ : syracuseStep 2150059 = 3225089) B3225089
theorem B2866745 : Blo 1909435 2866745 := bstep (se 2 (by rfl) ⟨1075029, by rfl⟩ : syracuseStep 2866745 = 2150059) B2150059
theorem B1911163 : Blo 1909435 1911163 := bstep (se 1 (by rfl) ⟨1433372, by rfl⟩ : syracuseStep 1911163 = 2866745) B2866745
theorem B2040881 : Blo 1909435 2040881 := bbase (se 2 (by rfl) ⟨765330, by rfl⟩ : syracuseStep 2040881 = 1530661) (by norm_num)
theorem B21769397 : Blo 1909435 21769397 := bstep (se 5 (by rfl) ⟨1020440, by rfl⟩ : syracuseStep 21769397 = 2040881) B2040881
theorem B14512931 : Blo 1909435 14512931 := bstep (se 1 (by rfl) ⟨10884698, by rfl⟩ : syracuseStep 14512931 = 21769397) B21769397
theorem B9675287 : Blo 1909435 9675287 := bstep (se 1 (by rfl) ⟨7256465, by rfl⟩ : syracuseStep 9675287 = 14512931) B14512931
theorem B6450191 : Blo 1909435 6450191 := bstep (se 1 (by rfl) ⟨4837643, by rfl⟩ : syracuseStep 6450191 = 9675287) B9675287
theorem B4300127 : Blo 1909435 4300127 := bstep (se 1 (by rfl) ⟨3225095, by rfl⟩ : syracuseStep 4300127 = 6450191) B6450191
theorem B2866751 : Blo 1909435 2866751 := bstep (se 1 (by rfl) ⟨2150063, by rfl⟩ : syracuseStep 2866751 = 4300127) B4300127
theorem B1911167 : Blo 1909435 1911167 := bstep (se 1 (by rfl) ⟨1433375, by rfl⟩ : syracuseStep 1911167 = 2866751) B2866751
theorem B2866757 : Blo 1909435 2866757 := bbase (se 4 (by rfl) ⟨268758, by rfl⟩ : syracuseStep 2866757 = 537517) (by norm_num)
theorem B1911171 : Blo 1909435 1911171 := bstep (se 1 (by rfl) ⟨1433378, by rfl⟩ : syracuseStep 1911171 = 2866757) B2866757
theorem B3225109 : Blo 1909435 3225109 := bbase (se 6 (by rfl) ⟨75588, by rfl⟩ : syracuseStep 3225109 = 151177) (by norm_num)
theorem B4300145 : Blo 1909435 4300145 := bstep (se 2 (by rfl) ⟨1612554, by rfl⟩ : syracuseStep 4300145 = 3225109) B3225109
theorem B2866763 : Blo 1909435 2866763 := bstep (se 1 (by rfl) ⟨2150072, by rfl⟩ : syracuseStep 2866763 = 4300145) B4300145
theorem B1911175 : Blo 1909435 1911175 := bstep (se 1 (by rfl) ⟨1433381, by rfl⟩ : syracuseStep 1911175 = 2866763) B2866763
theorem B2150077 : Blo 1909435 2150077 := bbase (se 3 (by rfl) ⟨403139, by rfl⟩ : syracuseStep 2150077 = 806279) (by norm_num)
theorem B2866769 : Blo 1909435 2866769 := bstep (se 2 (by rfl) ⟨1075038, by rfl⟩ : syracuseStep 2866769 = 2150077) B2150077
theorem B1911179 : Blo 1909435 1911179 := bstep (se 1 (by rfl) ⟨1433384, by rfl⟩ : syracuseStep 1911179 = 2866769) B2866769
theorem B6450245 : Blo 1909435 6450245 := bbase (se 4 (by rfl) ⟨604710, by rfl⟩ : syracuseStep 6450245 = 1209421) (by norm_num)
theorem B4300163 : Blo 1909435 4300163 := bstep (se 1 (by rfl) ⟨3225122, by rfl⟩ : syracuseStep 4300163 = 6450245) B6450245
theorem B2866775 : Blo 1909435 2866775 := bstep (se 1 (by rfl) ⟨2150081, by rfl⟩ : syracuseStep 2866775 = 4300163) B4300163
theorem B1911183 : Blo 1909435 1911183 := bstep (se 1 (by rfl) ⟨1433387, by rfl⟩ : syracuseStep 1911183 = 2866775) B2866775
theorem B2866781 : Blo 1909435 2866781 := bbase (se 3 (by rfl) ⟨537521, by rfl⟩ : syracuseStep 2866781 = 1075043) (by norm_num)
theorem B1911187 : Blo 1909435 1911187 := bstep (se 1 (by rfl) ⟨1433390, by rfl⟩ : syracuseStep 1911187 = 2866781) B2866781
theorem B4300181 : Blo 1909435 4300181 := bbase (se 6 (by rfl) ⟨100785, by rfl⟩ : syracuseStep 4300181 = 201571) (by norm_num)
theorem B2866787 : Blo 1909435 2866787 := bstep (se 1 (by rfl) ⟨2150090, by rfl⟩ : syracuseStep 2866787 = 4300181) B4300181
theorem B1911191 : Blo 1909435 1911191 := bstep (se 1 (by rfl) ⟨1433393, by rfl⟩ : syracuseStep 1911191 = 2866787) B2866787
theorem B15923957 : Blo 1909435 15923957 := bbase (se 5 (by rfl) ⟨746435, by rfl⟩ : syracuseStep 15923957 = 1492871) (by norm_num)
theorem B42463885 : Blo 1909435 42463885 := bstep (se 3 (by rfl) ⟨7961978, by rfl⟩ : syracuseStep 42463885 = 15923957) B15923957
theorem B56618513 : Blo 1909435 56618513 := bstep (se 2 (by rfl) ⟨21231942, by rfl⟩ : syracuseStep 56618513 = 42463885) B42463885
theorem B37745675 : Blo 1909435 37745675 := bstep (se 1 (by rfl) ⟨28309256, by rfl⟩ : syracuseStep 37745675 = 56618513) B56618513
theorem B25163783 : Blo 1909435 25163783 := bstep (se 1 (by rfl) ⟨18872837, by rfl⟩ : syracuseStep 25163783 = 37745675) B37745675
theorem B16775855 : Blo 1909435 16775855 := bstep (se 1 (by rfl) ⟨12581891, by rfl⟩ : syracuseStep 16775855 = 25163783) B25163783
theorem B11183903 : Blo 1909435 11183903 := bstep (se 1 (by rfl) ⟨8387927, by rfl⟩ : syracuseStep 11183903 = 16775855) B16775855
theorem B7455935 : Blo 1909435 7455935 := bstep (se 1 (by rfl) ⟨5591951, by rfl⟩ : syracuseStep 7455935 = 11183903) B11183903
theorem B19882493 : Blo 1909435 19882493 := bstep (se 3 (by rfl) ⟨3727967, by rfl⟩ : syracuseStep 19882493 = 7455935) B7455935
theorem B13254995 : Blo 1909435 13254995 := bstep (se 1 (by rfl) ⟨9941246, by rfl⟩ : syracuseStep 13254995 = 19882493) B19882493
theorem B8836663 : Blo 1909435 8836663 := bstep (se 1 (by rfl) ⟨6627497, by rfl⟩ : syracuseStep 8836663 = 13254995) B13254995
theorem B11782217 : Blo 1909435 11782217 := bstep (se 2 (by rfl) ⟨4418331, by rfl⟩ : syracuseStep 11782217 = 8836663) B8836663
theorem B31419245 : Blo 1909435 31419245 := bstep (se 3 (by rfl) ⟨5891108, by rfl⟩ : syracuseStep 31419245 = 11782217) B11782217
theorem B20946163 : Blo 1909435 20946163 := bstep (se 1 (by rfl) ⟨15709622, by rfl⟩ : syracuseStep 20946163 = 31419245) B31419245
theorem B27928217 : Blo 1909435 27928217 := bstep (se 2 (by rfl) ⟨10473081, by rfl⟩ : syracuseStep 27928217 = 20946163) B20946163
theorem B18618811 : Blo 1909435 18618811 := bstep (se 1 (by rfl) ⟨13964108, by rfl⟩ : syracuseStep 18618811 = 27928217) B27928217
theorem B99300325 : Blo 1909435 99300325 := bstep (se 4 (by rfl) ⟨9309405, by rfl⟩ : syracuseStep 99300325 = 18618811) B18618811
theorem B132400433 : Blo 1909435 132400433 := bstep (se 2 (by rfl) ⟨49650162, by rfl⟩ : syracuseStep 132400433 = 99300325) B99300325
theorem B88266955 : Blo 1909435 88266955 := bstep (se 1 (by rfl) ⟨66200216, by rfl⟩ : syracuseStep 88266955 = 132400433) B132400433
theorem B117689273 : Blo 1909435 117689273 := bstep (se 2 (by rfl) ⟨44133477, by rfl⟩ : syracuseStep 117689273 = 88266955) B88266955
theorem B78459515 : Blo 1909435 78459515 := bstep (se 1 (by rfl) ⟨58844636, by rfl⟩ : syracuseStep 78459515 = 117689273) B117689273
theorem B52306343 : Blo 1909435 52306343 := bstep (se 1 (by rfl) ⟨39229757, by rfl⟩ : syracuseStep 52306343 = 78459515) B78459515
theorem B34870895 : Blo 1909435 34870895 := bstep (se 1 (by rfl) ⟨26153171, by rfl⟩ : syracuseStep 34870895 = 52306343) B52306343
theorem B23247263 : Blo 1909435 23247263 := bstep (se 1 (by rfl) ⟨17435447, by rfl⟩ : syracuseStep 23247263 = 34870895) B34870895
theorem B15498175 : Blo 1909435 15498175 := bstep (se 1 (by rfl) ⟨11623631, by rfl⟩ : syracuseStep 15498175 = 23247263) B23247263
theorem B20664233 : Blo 1909435 20664233 := bstep (se 2 (by rfl) ⟨7749087, by rfl⟩ : syracuseStep 20664233 = 15498175) B15498175
theorem B13776155 : Blo 1909435 13776155 := bstep (se 1 (by rfl) ⟨10332116, by rfl⟩ : syracuseStep 13776155 = 20664233) B20664233
theorem B9184103 : Blo 1909435 9184103 := bstep (se 1 (by rfl) ⟨6888077, by rfl⟩ : syracuseStep 9184103 = 13776155) B13776155
theorem B6122735 : Blo 1909435 6122735 := bstep (se 1 (by rfl) ⟨4592051, by rfl⟩ : syracuseStep 6122735 = 9184103) B9184103
theorem B4081823 : Blo 1909435 4081823 := bstep (se 1 (by rfl) ⟨3061367, by rfl⟩ : syracuseStep 4081823 = 6122735) B6122735
theorem B2721215 : Blo 1909435 2721215 := bstep (se 1 (by rfl) ⟨2040911, by rfl⟩ : syracuseStep 2721215 = 4081823) B4081823
theorem B7256573 : Blo 1909435 7256573 := bstep (se 3 (by rfl) ⟨1360607, by rfl⟩ : syracuseStep 7256573 = 2721215) B2721215
theorem B4837715 : Blo 1909435 4837715 := bstep (se 1 (by rfl) ⟨3628286, by rfl⟩ : syracuseStep 4837715 = 7256573) B7256573
theorem B3225143 : Blo 1909435 3225143 := bstep (se 1 (by rfl) ⟨2418857, by rfl⟩ : syracuseStep 3225143 = 4837715) B4837715
theorem B2150095 : Blo 1909435 2150095 := bstep (se 1 (by rfl) ⟨1612571, by rfl⟩ : syracuseStep 2150095 = 3225143) B3225143
theorem B2866793 : Blo 1909435 2866793 := bstep (se 2 (by rfl) ⟨1075047, by rfl⟩ : syracuseStep 2866793 = 2150095) B2150095
theorem B1911195 : Blo 1909435 1911195 := bstep (se 1 (by rfl) ⟨1433396, by rfl⟩ : syracuseStep 1911195 = 2866793) B2866793
theorem B3061373 : Blo 1909435 3061373 := bbase (se 3 (by rfl) ⟨574007, by rfl⟩ : syracuseStep 3061373 = 1148015) (by norm_num)
theorem B8163661 : Blo 1909435 8163661 := bstep (se 3 (by rfl) ⟨1530686, by rfl⟩ : syracuseStep 8163661 = 3061373) B3061373
theorem B10884881 : Blo 1909435 10884881 := bstep (se 2 (by rfl) ⟨4081830, by rfl⟩ : syracuseStep 10884881 = 8163661) B8163661
theorem B7256587 : Blo 1909435 7256587 := bstep (se 1 (by rfl) ⟨5442440, by rfl⟩ : syracuseStep 7256587 = 10884881) B10884881
theorem B9675449 : Blo 1909435 9675449 := bstep (se 2 (by rfl) ⟨3628293, by rfl⟩ : syracuseStep 9675449 = 7256587) B7256587
theorem B6450299 : Blo 1909435 6450299 := bstep (se 1 (by rfl) ⟨4837724, by rfl⟩ : syracuseStep 6450299 = 9675449) B9675449
theorem B4300199 : Blo 1909435 4300199 := bstep (se 1 (by rfl) ⟨3225149, by rfl⟩ : syracuseStep 4300199 = 6450299) B6450299
theorem B2866799 : Blo 1909435 2866799 := bstep (se 1 (by rfl) ⟨2150099, by rfl⟩ : syracuseStep 2866799 = 4300199) B4300199
theorem B1911199 : Blo 1909435 1911199 := bstep (se 1 (by rfl) ⟨1433399, by rfl⟩ : syracuseStep 1911199 = 2866799) B2866799
theorem B2866805 : Blo 1909435 2866805 := bbase (se 5 (by rfl) ⟨134381, by rfl⟩ : syracuseStep 2866805 = 268763) (by norm_num)
theorem B1911203 : Blo 1909435 1911203 := bstep (se 1 (by rfl) ⟨1433402, by rfl⟩ : syracuseStep 1911203 = 2866805) B2866805
theorem B3628309 : Blo 1909435 3628309 := bbase (se 6 (by rfl) ⟨85038, by rfl⟩ : syracuseStep 3628309 = 170077) (by norm_num)
theorem B4837745 : Blo 1909435 4837745 := bstep (se 2 (by rfl) ⟨1814154, by rfl⟩ : syracuseStep 4837745 = 3628309) B3628309
theorem B3225163 : Blo 1909435 3225163 := bstep (se 1 (by rfl) ⟨2418872, by rfl⟩ : syracuseStep 3225163 = 4837745) B4837745
theorem B4300217 : Blo 1909435 4300217 := bstep (se 2 (by rfl) ⟨1612581, by rfl⟩ : syracuseStep 4300217 = 3225163) B3225163
theorem B2866811 : Blo 1909435 2866811 := bstep (se 1 (by rfl) ⟨2150108, by rfl⟩ : syracuseStep 2866811 = 4300217) B4300217
theorem B1911207 : Blo 1909435 1911207 := bstep (se 1 (by rfl) ⟨1433405, by rfl⟩ : syracuseStep 1911207 = 2866811) B2866811
theorem B2150113 : Blo 1909435 2150113 := bbase (se 2 (by rfl) ⟨806292, by rfl⟩ : syracuseStep 2150113 = 1612585) (by norm_num)
theorem B2866817 : Blo 1909435 2866817 := bstep (se 2 (by rfl) ⟨1075056, by rfl⟩ : syracuseStep 2866817 = 2150113) B2150113
theorem B1911211 : Blo 1909435 1911211 := bstep (se 1 (by rfl) ⟨1433408, by rfl⟩ : syracuseStep 1911211 = 2866817) B2866817
theorem B4837765 : Blo 1909435 4837765 := bbase (se 4 (by rfl) ⟨453540, by rfl⟩ : syracuseStep 4837765 = 907081) (by norm_num)
theorem B6450353 : Blo 1909435 6450353 := bstep (se 2 (by rfl) ⟨2418882, by rfl⟩ : syracuseStep 6450353 = 4837765) B4837765
theorem B4300235 : Blo 1909435 4300235 := bstep (se 1 (by rfl) ⟨3225176, by rfl⟩ : syracuseStep 4300235 = 6450353) B6450353
theorem B2866823 : Blo 1909435 2866823 := bstep (se 1 (by rfl) ⟨2150117, by rfl⟩ : syracuseStep 2866823 = 4300235) B4300235
theorem B1911215 : Blo 1909435 1911215 := bstep (se 1 (by rfl) ⟨1433411, by rfl⟩ : syracuseStep 1911215 = 2866823) B2866823
theorem B2866829 : Blo 1909435 2866829 := bbase (se 3 (by rfl) ⟨537530, by rfl⟩ : syracuseStep 2866829 = 1075061) (by norm_num)
theorem B1911219 : Blo 1909435 1911219 := bstep (se 1 (by rfl) ⟨1433414, by rfl⟩ : syracuseStep 1911219 = 2866829) B2866829
theorem B4300253 : Blo 1909435 4300253 := bbase (se 3 (by rfl) ⟨806297, by rfl⟩ : syracuseStep 4300253 = 1612595) (by norm_num)
theorem B2866835 : Blo 1909435 2866835 := bstep (se 1 (by rfl) ⟨2150126, by rfl⟩ : syracuseStep 2866835 = 4300253) B4300253
theorem B1911223 : Blo 1909435 1911223 := bstep (se 1 (by rfl) ⟨1433417, by rfl⟩ : syracuseStep 1911223 = 2866835) B2866835
theorem B3225197 : Blo 1909435 3225197 := bbase (se 3 (by rfl) ⟨604724, by rfl⟩ : syracuseStep 3225197 = 1209449) (by norm_num)
theorem B2150131 : Blo 1909435 2150131 := bstep (se 1 (by rfl) ⟨1612598, by rfl⟩ : syracuseStep 2150131 = 3225197) B3225197
theorem B2866841 : Blo 1909435 2866841 := bstep (se 2 (by rfl) ⟨1075065, by rfl⟩ : syracuseStep 2866841 = 2150131) B2150131
theorem B1911227 : Blo 1909435 1911227 := bstep (se 1 (by rfl) ⟨1433420, by rfl⟩ : syracuseStep 1911227 = 2866841) B2866841
theorem B7355717 : Blo 1909435 7355717 := bbase (se 4 (by rfl) ⟨689598, by rfl⟩ : syracuseStep 7355717 = 1379197) (by norm_num)
theorem B4903811 : Blo 1909435 4903811 := bstep (se 1 (by rfl) ⟨3677858, by rfl⟩ : syracuseStep 4903811 = 7355717) B7355717
theorem B3269207 : Blo 1909435 3269207 := bstep (se 1 (by rfl) ⟨2451905, by rfl⟩ : syracuseStep 3269207 = 4903811) B4903811
theorem B8717885 : Blo 1909435 8717885 := bstep (se 3 (by rfl) ⟨1634603, by rfl⟩ : syracuseStep 8717885 = 3269207) B3269207
theorem B5811923 : Blo 1909435 5811923 := bstep (se 1 (by rfl) ⟨4358942, by rfl⟩ : syracuseStep 5811923 = 8717885) B8717885
theorem B15498461 : Blo 1909435 15498461 := bstep (se 3 (by rfl) ⟨2905961, by rfl⟩ : syracuseStep 15498461 = 5811923) B5811923
theorem B10332307 : Blo 1909435 10332307 := bstep (se 1 (by rfl) ⟨7749230, by rfl⟩ : syracuseStep 10332307 = 15498461) B15498461
theorem B13776409 : Blo 1909435 13776409 := bstep (se 2 (by rfl) ⟨5166153, by rfl⟩ : syracuseStep 13776409 = 10332307) B10332307
theorem B18368545 : Blo 1909435 18368545 := bstep (se 2 (by rfl) ⟨6888204, by rfl⟩ : syracuseStep 18368545 = 13776409) B13776409
theorem B24491393 : Blo 1909435 24491393 := bstep (se 2 (by rfl) ⟨9184272, by rfl⟩ : syracuseStep 24491393 = 18368545) B18368545
theorem B16327595 : Blo 1909435 16327595 := bstep (se 1 (by rfl) ⟨12245696, by rfl⟩ : syracuseStep 16327595 = 24491393) B24491393
theorem B10885063 : Blo 1909435 10885063 := bstep (se 1 (by rfl) ⟨8163797, by rfl⟩ : syracuseStep 10885063 = 16327595) B16327595
theorem B14513417 : Blo 1909435 14513417 := bstep (se 2 (by rfl) ⟨5442531, by rfl⟩ : syracuseStep 14513417 = 10885063) B10885063
theorem B9675611 : Blo 1909435 9675611 := bstep (se 1 (by rfl) ⟨7256708, by rfl⟩ : syracuseStep 9675611 = 14513417) B14513417
theorem B6450407 : Blo 1909435 6450407 := bstep (se 1 (by rfl) ⟨4837805, by rfl⟩ : syracuseStep 6450407 = 9675611) B9675611
theorem B4300271 : Blo 1909435 4300271 := bstep (se 1 (by rfl) ⟨3225203, by rfl⟩ : syracuseStep 4300271 = 6450407) B6450407
theorem B2866847 : Blo 1909435 2866847 := bstep (se 1 (by rfl) ⟨2150135, by rfl⟩ : syracuseStep 2866847 = 4300271) B4300271
theorem B1911231 : Blo 1909435 1911231 := bstep (se 1 (by rfl) ⟨1433423, by rfl⟩ : syracuseStep 1911231 = 2866847) B2866847
theorem B2866853 : Blo 1909435 2866853 := bbase (se 4 (by rfl) ⟨268767, by rfl⟩ : syracuseStep 2866853 = 537535) (by norm_num)
theorem B1911235 : Blo 1909435 1911235 := bstep (se 1 (by rfl) ⟨1433426, by rfl⟩ : syracuseStep 1911235 = 2866853) B2866853
theorem B2418913 : Blo 1909435 2418913 := bbase (se 2 (by rfl) ⟨907092, by rfl⟩ : syracuseStep 2418913 = 1814185) (by norm_num)
theorem B3225217 : Blo 1909435 3225217 := bstep (se 2 (by rfl) ⟨1209456, by rfl⟩ : syracuseStep 3225217 = 2418913) B2418913
theorem B4300289 : Blo 1909435 4300289 := bstep (se 2 (by rfl) ⟨1612608, by rfl⟩ : syracuseStep 4300289 = 3225217) B3225217
theorem B2866859 : Blo 1909435 2866859 := bstep (se 1 (by rfl) ⟨2150144, by rfl⟩ : syracuseStep 2866859 = 4300289) B4300289
theorem B1911239 : Blo 1909435 1911239 := bstep (se 1 (by rfl) ⟨1433429, by rfl⟩ : syracuseStep 1911239 = 2866859) B2866859
theorem B2150149 : Blo 1909435 2150149 := bbase (se 4 (by rfl) ⟨201576, by rfl⟩ : syracuseStep 2150149 = 403153) (by norm_num)
theorem B2866865 : Blo 1909435 2866865 := bstep (se 2 (by rfl) ⟨1075074, by rfl⟩ : syracuseStep 2866865 = 2150149) B2150149
theorem B1911243 : Blo 1909435 1911243 := bstep (se 1 (by rfl) ⟨1433432, by rfl⟩ : syracuseStep 1911243 = 2866865) B2866865
theorem B3444133 : Blo 1909435 3444133 := bbase (se 4 (by rfl) ⟨322887, by rfl⟩ : syracuseStep 3444133 = 645775) (by norm_num)
theorem B4592177 : Blo 1909435 4592177 := bstep (se 2 (by rfl) ⟨1722066, by rfl⟩ : syracuseStep 4592177 = 3444133) B3444133
theorem B3061451 : Blo 1909435 3061451 := bstep (se 1 (by rfl) ⟨2296088, by rfl⟩ : syracuseStep 3061451 = 4592177) B4592177
theorem B2040967 : Blo 1909435 2040967 := bstep (se 1 (by rfl) ⟨1530725, by rfl⟩ : syracuseStep 2040967 = 3061451) B3061451
theorem B2721289 : Blo 1909435 2721289 := bstep (se 2 (by rfl) ⟨1020483, by rfl⟩ : syracuseStep 2721289 = 2040967) B2040967
theorem B3628385 : Blo 1909435 3628385 := bstep (se 2 (by rfl) ⟨1360644, by rfl⟩ : syracuseStep 3628385 = 2721289) B2721289
theorem B2418923 : Blo 1909435 2418923 := bstep (se 1 (by rfl) ⟨1814192, by rfl⟩ : syracuseStep 2418923 = 3628385) B3628385
theorem B6450461 : Blo 1909435 6450461 := bstep (se 3 (by rfl) ⟨1209461, by rfl⟩ : syracuseStep 6450461 = 2418923) B2418923
theorem B4300307 : Blo 1909435 4300307 := bstep (se 1 (by rfl) ⟨3225230, by rfl⟩ : syracuseStep 4300307 = 6450461) B6450461
theorem B2866871 : Blo 1909435 2866871 := bstep (se 1 (by rfl) ⟨2150153, by rfl⟩ : syracuseStep 2866871 = 4300307) B4300307
theorem B1911247 : Blo 1909435 1911247 := bstep (se 1 (by rfl) ⟨1433435, by rfl⟩ : syracuseStep 1911247 = 2866871) B2866871
theorem B2866877 : Blo 1909435 2866877 := bbase (se 3 (by rfl) ⟨537539, by rfl⟩ : syracuseStep 2866877 = 1075079) (by norm_num)
theorem B1911251 : Blo 1909435 1911251 := bstep (se 1 (by rfl) ⟨1433438, by rfl⟩ : syracuseStep 1911251 = 2866877) B2866877
theorem B4300325 : Blo 1909435 4300325 := bbase (se 4 (by rfl) ⟨403155, by rfl⟩ : syracuseStep 4300325 = 806311) (by norm_num)
theorem B2866883 : Blo 1909435 2866883 := bstep (se 1 (by rfl) ⟨2150162, by rfl⟩ : syracuseStep 2866883 = 4300325) B4300325
theorem B1911255 : Blo 1909435 1911255 := bstep (se 1 (by rfl) ⟨1433441, by rfl⟩ : syracuseStep 1911255 = 2866883) B2866883
theorem B4837877 : Blo 1909435 4837877 := bbase (se 5 (by rfl) ⟨226775, by rfl⟩ : syracuseStep 4837877 = 453551) (by norm_num)
theorem B3225251 : Blo 1909435 3225251 := bstep (se 1 (by rfl) ⟨2418938, by rfl⟩ : syracuseStep 3225251 = 4837877) B4837877
theorem B2150167 : Blo 1909435 2150167 := bstep (se 1 (by rfl) ⟨1612625, by rfl⟩ : syracuseStep 2150167 = 3225251) B3225251
theorem B2866889 : Blo 1909435 2866889 := bstep (se 2 (by rfl) ⟨1075083, by rfl⟩ : syracuseStep 2866889 = 2150167) B2150167
theorem B1911259 : Blo 1909435 1911259 := bstep (se 1 (by rfl) ⟨1433444, by rfl⟩ : syracuseStep 1911259 = 2866889) B2866889
theorem B5812021 : Blo 1909435 5812021 := bbase (se 5 (by rfl) ⟨272438, by rfl⟩ : syracuseStep 5812021 = 544877) (by norm_num)
theorem B7749361 : Blo 1909435 7749361 := bstep (se 2 (by rfl) ⟨2906010, by rfl⟩ : syracuseStep 7749361 = 5812021) B5812021
theorem B41329925 : Blo 1909435 41329925 := bstep (se 4 (by rfl) ⟨3874680, by rfl⟩ : syracuseStep 41329925 = 7749361) B7749361
theorem B27553283 : Blo 1909435 27553283 := bstep (se 1 (by rfl) ⟨20664962, by rfl⟩ : syracuseStep 27553283 = 41329925) B41329925
theorem B18368855 : Blo 1909435 18368855 := bstep (se 1 (by rfl) ⟨13776641, by rfl⟩ : syracuseStep 18368855 = 27553283) B27553283
theorem B12245903 : Blo 1909435 12245903 := bstep (se 1 (by rfl) ⟨9184427, by rfl⟩ : syracuseStep 12245903 = 18368855) B18368855
theorem B8163935 : Blo 1909435 8163935 := bstep (se 1 (by rfl) ⟨6122951, by rfl⟩ : syracuseStep 8163935 = 12245903) B12245903
theorem B5442623 : Blo 1909435 5442623 := bstep (se 1 (by rfl) ⟨4081967, by rfl⟩ : syracuseStep 5442623 = 8163935) B8163935
theorem B3628415 : Blo 1909435 3628415 := bstep (se 1 (by rfl) ⟨2721311, by rfl⟩ : syracuseStep 3628415 = 5442623) B5442623
theorem B9675773 : Blo 1909435 9675773 := bstep (se 3 (by rfl) ⟨1814207, by rfl⟩ : syracuseStep 9675773 = 3628415) B3628415
theorem B6450515 : Blo 1909435 6450515 := bstep (se 1 (by rfl) ⟨4837886, by rfl⟩ : syracuseStep 6450515 = 9675773) B9675773
theorem B4300343 : Blo 1909435 4300343 := bstep (se 1 (by rfl) ⟨3225257, by rfl⟩ : syracuseStep 4300343 = 6450515) B6450515
theorem B2866895 : Blo 1909435 2866895 := bstep (se 1 (by rfl) ⟨2150171, by rfl⟩ : syracuseStep 2866895 = 4300343) B4300343
theorem B1911263 : Blo 1909435 1911263 := bstep (se 1 (by rfl) ⟨1433447, by rfl⟩ : syracuseStep 1911263 = 2866895) B2866895
theorem B2866901 : Blo 1909435 2866901 := bbase (se 7 (by rfl) ⟨33596, by rfl⟩ : syracuseStep 2866901 = 67193) (by norm_num)
theorem B1911267 : Blo 1909435 1911267 := bstep (se 1 (by rfl) ⟨1433450, by rfl⟩ : syracuseStep 1911267 = 2866901) B2866901
theorem B2296117 : Blo 1909435 2296117 := bbase (se 5 (by rfl) ⟨107630, by rfl⟩ : syracuseStep 2296117 = 215261) (by norm_num)
theorem B3061489 : Blo 1909435 3061489 := bstep (se 2 (by rfl) ⟨1148058, by rfl⟩ : syracuseStep 3061489 = 2296117) B2296117
theorem B4081985 : Blo 1909435 4081985 := bstep (se 2 (by rfl) ⟨1530744, by rfl⟩ : syracuseStep 4081985 = 3061489) B3061489
theorem B2721323 : Blo 1909435 2721323 := bstep (se 1 (by rfl) ⟨2040992, by rfl⟩ : syracuseStep 2721323 = 4081985) B4081985
theorem B7256861 : Blo 1909435 7256861 := bstep (se 3 (by rfl) ⟨1360661, by rfl⟩ : syracuseStep 7256861 = 2721323) B2721323
theorem B4837907 : Blo 1909435 4837907 := bstep (se 1 (by rfl) ⟨3628430, by rfl⟩ : syracuseStep 4837907 = 7256861) B7256861
theorem B3225271 : Blo 1909435 3225271 := bstep (se 1 (by rfl) ⟨2418953, by rfl⟩ : syracuseStep 3225271 = 4837907) B4837907
theorem B4300361 : Blo 1909435 4300361 := bstep (se 2 (by rfl) ⟨1612635, by rfl⟩ : syracuseStep 4300361 = 3225271) B3225271
theorem B2866907 : Blo 1909435 2866907 := bstep (se 1 (by rfl) ⟨2150180, by rfl⟩ : syracuseStep 2866907 = 4300361) B4300361
theorem B1911271 : Blo 1909435 1911271 := bstep (se 1 (by rfl) ⟨1433453, by rfl⟩ : syracuseStep 1911271 = 2866907) B2866907
theorem B2150185 : Blo 1909435 2150185 := bbase (se 2 (by rfl) ⟨806319, by rfl⟩ : syracuseStep 2150185 = 1612639) (by norm_num)
theorem B2866913 : Blo 1909435 2866913 := bstep (se 2 (by rfl) ⟨1075092, by rfl⟩ : syracuseStep 2866913 = 2150185) B2150185
theorem B1911275 : Blo 1909435 1911275 := bstep (se 1 (by rfl) ⟨1433456, by rfl⟩ : syracuseStep 1911275 = 2866913) B2866913
theorem B12246005 : Blo 1909435 12246005 := bbase (se 5 (by rfl) ⟨574031, by rfl⟩ : syracuseStep 12246005 = 1148063) (by norm_num)
theorem B8164003 : Blo 1909435 8164003 := bstep (se 1 (by rfl) ⟨6123002, by rfl⟩ : syracuseStep 8164003 = 12246005) B12246005
theorem B10885337 : Blo 1909435 10885337 := bstep (se 2 (by rfl) ⟨4082001, by rfl⟩ : syracuseStep 10885337 = 8164003) B8164003
theorem B7256891 : Blo 1909435 7256891 := bstep (se 1 (by rfl) ⟨5442668, by rfl⟩ : syracuseStep 7256891 = 10885337) B10885337
theorem B4837927 : Blo 1909435 4837927 := bstep (se 1 (by rfl) ⟨3628445, by rfl⟩ : syracuseStep 4837927 = 7256891) B7256891
theorem B6450569 : Blo 1909435 6450569 := bstep (se 2 (by rfl) ⟨2418963, by rfl⟩ : syracuseStep 6450569 = 4837927) B4837927
theorem B4300379 : Blo 1909435 4300379 := bstep (se 1 (by rfl) ⟨3225284, by rfl⟩ : syracuseStep 4300379 = 6450569) B6450569
theorem B2866919 : Blo 1909435 2866919 := bstep (se 1 (by rfl) ⟨2150189, by rfl⟩ : syracuseStep 2866919 = 4300379) B4300379
theorem B1911279 : Blo 1909435 1911279 := bstep (se 1 (by rfl) ⟨1433459, by rfl⟩ : syracuseStep 1911279 = 2866919) B2866919
theorem B2866925 : Blo 1909435 2866925 := bbase (se 3 (by rfl) ⟨537548, by rfl⟩ : syracuseStep 2866925 = 1075097) (by norm_num)
theorem B1911283 : Blo 1909435 1911283 := bstep (se 1 (by rfl) ⟨1433462, by rfl⟩ : syracuseStep 1911283 = 2866925) B2866925
theorem B4300397 : Blo 1909435 4300397 := bbase (se 3 (by rfl) ⟨806324, by rfl⟩ : syracuseStep 4300397 = 1612649) (by norm_num)
theorem B2866931 : Blo 1909435 2866931 := bstep (se 1 (by rfl) ⟨2150198, by rfl⟩ : syracuseStep 2866931 = 4300397) B4300397
theorem B1911287 : Blo 1909435 1911287 := bstep (se 1 (by rfl) ⟨1433465, by rfl⟩ : syracuseStep 1911287 = 2866931) B2866931
theorem B3628469 : Blo 1909435 3628469 := bbase (se 5 (by rfl) ⟨170084, by rfl⟩ : syracuseStep 3628469 = 340169) (by norm_num)
theorem B2418979 : Blo 1909435 2418979 := bstep (se 1 (by rfl) ⟨1814234, by rfl⟩ : syracuseStep 2418979 = 3628469) B3628469
theorem B3225305 : Blo 1909435 3225305 := bstep (se 2 (by rfl) ⟨1209489, by rfl⟩ : syracuseStep 3225305 = 2418979) B2418979
theorem B2150203 : Blo 1909435 2150203 := bstep (se 1 (by rfl) ⟨1612652, by rfl⟩ : syracuseStep 2150203 = 3225305) B3225305
theorem B2866937 : Blo 1909435 2866937 := bstep (se 2 (by rfl) ⟨1075101, by rfl⟩ : syracuseStep 2866937 = 2150203) B2150203
theorem B1911291 : Blo 1909435 1911291 := bstep (se 1 (by rfl) ⟨1433468, by rfl⟩ : syracuseStep 1911291 = 2866937) B2866937
theorem B5812117 : Blo 1909435 5812117 := bbase (se 6 (by rfl) ⟨136221, by rfl⟩ : syracuseStep 5812117 = 272443) (by norm_num)
theorem B123991829 : Blo 1909435 123991829 := bstep (se 6 (by rfl) ⟨2906058, by rfl⟩ : syracuseStep 123991829 = 5812117) B5812117
theorem B82661219 : Blo 1909435 82661219 := bstep (se 1 (by rfl) ⟨61995914, by rfl⟩ : syracuseStep 82661219 = 123991829) B123991829
theorem B55107479 : Blo 1909435 55107479 := bstep (se 1 (by rfl) ⟨41330609, by rfl⟩ : syracuseStep 55107479 = 82661219) B82661219
theorem B36738319 : Blo 1909435 36738319 := bstep (se 1 (by rfl) ⟨27553739, by rfl⟩ : syracuseStep 36738319 = 55107479) B55107479
theorem B48984425 : Blo 1909435 48984425 := bstep (se 2 (by rfl) ⟨18369159, by rfl⟩ : syracuseStep 48984425 = 36738319) B36738319
theorem B32656283 : Blo 1909435 32656283 := bstep (se 1 (by rfl) ⟨24492212, by rfl⟩ : syracuseStep 32656283 = 48984425) B48984425
theorem B21770855 : Blo 1909435 21770855 := bstep (se 1 (by rfl) ⟨16328141, by rfl⟩ : syracuseStep 21770855 = 32656283) B32656283
theorem B14513903 : Blo 1909435 14513903 := bstep (se 1 (by rfl) ⟨10885427, by rfl⟩ : syracuseStep 14513903 = 21770855) B21770855
theorem B9675935 : Blo 1909435 9675935 := bstep (se 1 (by rfl) ⟨7256951, by rfl⟩ : syracuseStep 9675935 = 14513903) B14513903
theorem B6450623 : Blo 1909435 6450623 := bstep (se 1 (by rfl) ⟨4837967, by rfl⟩ : syracuseStep 6450623 = 9675935) B9675935
theorem B4300415 : Blo 1909435 4300415 := bstep (se 1 (by rfl) ⟨3225311, by rfl⟩ : syracuseStep 4300415 = 6450623) B6450623
theorem B2866943 : Blo 1909435 2866943 := bstep (se 1 (by rfl) ⟨2150207, by rfl⟩ : syracuseStep 2866943 = 4300415) B4300415
theorem B1911295 : Blo 1909435 1911295 := bstep (se 1 (by rfl) ⟨1433471, by rfl⟩ : syracuseStep 1911295 = 2866943) B2866943
theorem B2866949 : Blo 1909435 2866949 := bbase (se 4 (by rfl) ⟨268776, by rfl⟩ : syracuseStep 2866949 = 537553) (by norm_num)
theorem B1911299 : Blo 1909435 1911299 := bstep (se 1 (by rfl) ⟨1433474, by rfl⟩ : syracuseStep 1911299 = 2866949) B2866949
theorem B3225325 : Blo 1909435 3225325 := bbase (se 3 (by rfl) ⟨604748, by rfl⟩ : syracuseStep 3225325 = 1209497) (by norm_num)
theorem B4300433 : Blo 1909435 4300433 := bstep (se 2 (by rfl) ⟨1612662, by rfl⟩ : syracuseStep 4300433 = 3225325) B3225325
theorem B2866955 : Blo 1909435 2866955 := bstep (se 1 (by rfl) ⟨2150216, by rfl⟩ : syracuseStep 2866955 = 4300433) B4300433
theorem B1911303 : Blo 1909435 1911303 := bstep (se 1 (by rfl) ⟨1433477, by rfl⟩ : syracuseStep 1911303 = 2866955) B2866955
theorem B2150221 : Blo 1909435 2150221 := bbase (se 3 (by rfl) ⟨403166, by rfl⟩ : syracuseStep 2150221 = 806333) (by norm_num)
theorem B2866961 : Blo 1909435 2866961 := bstep (se 2 (by rfl) ⟨1075110, by rfl⟩ : syracuseStep 2866961 = 2150221) B2150221
theorem B1911307 : Blo 1909435 1911307 := bstep (se 1 (by rfl) ⟨1433480, by rfl⟩ : syracuseStep 1911307 = 2866961) B2866961
theorem B6450677 : Blo 1909435 6450677 := bbase (se 5 (by rfl) ⟨302375, by rfl⟩ : syracuseStep 6450677 = 604751) (by norm_num)
theorem B4300451 : Blo 1909435 4300451 := bstep (se 1 (by rfl) ⟨3225338, by rfl⟩ : syracuseStep 4300451 = 6450677) B6450677
theorem B2866967 : Blo 1909435 2866967 := bstep (se 1 (by rfl) ⟨2150225, by rfl⟩ : syracuseStep 2866967 = 4300451) B4300451
theorem B1911311 : Blo 1909435 1911311 := bstep (se 1 (by rfl) ⟨1433483, by rfl⟩ : syracuseStep 1911311 = 2866967) B2866967
theorem B2866973 : Blo 1909435 2866973 := bbase (se 3 (by rfl) ⟨537557, by rfl⟩ : syracuseStep 2866973 = 1075115) (by norm_num)
theorem B1911315 : Blo 1909435 1911315 := bstep (se 1 (by rfl) ⟨1433486, by rfl⟩ : syracuseStep 1911315 = 2866973) B2866973
theorem B4300469 : Blo 1909435 4300469 := bbase (se 5 (by rfl) ⟨201584, by rfl⟩ : syracuseStep 4300469 = 403169) (by norm_num)
theorem B2866979 : Blo 1909435 2866979 := bstep (se 1 (by rfl) ⟨2150234, by rfl⟩ : syracuseStep 2866979 = 4300469) B4300469
theorem B1911319 : Blo 1909435 1911319 := bstep (se 1 (by rfl) ⟨1433489, by rfl⟩ : syracuseStep 1911319 = 2866979) B2866979
theorem B10885589 : Blo 1909435 10885589 := bbase (se 7 (by rfl) ⟨127565, by rfl⟩ : syracuseStep 10885589 = 255131) (by norm_num)
theorem B7257059 : Blo 1909435 7257059 := bstep (se 1 (by rfl) ⟨5442794, by rfl⟩ : syracuseStep 7257059 = 10885589) B10885589
theorem B4838039 : Blo 1909435 4838039 := bstep (se 1 (by rfl) ⟨3628529, by rfl⟩ : syracuseStep 4838039 = 7257059) B7257059
theorem B3225359 : Blo 1909435 3225359 := bstep (se 1 (by rfl) ⟨2419019, by rfl⟩ : syracuseStep 3225359 = 4838039) B4838039
theorem B2150239 : Blo 1909435 2150239 := bstep (se 1 (by rfl) ⟨1612679, by rfl⟩ : syracuseStep 2150239 = 3225359) B3225359
theorem B2866985 : Blo 1909435 2866985 := bstep (se 2 (by rfl) ⟨1075119, by rfl⟩ : syracuseStep 2866985 = 2150239) B2150239
theorem B1911323 : Blo 1909435 1911323 := bstep (se 1 (by rfl) ⟨1433492, by rfl⟩ : syracuseStep 1911323 = 2866985) B2866985
theorem B5442805 : Blo 1909435 5442805 := bbase (se 5 (by rfl) ⟨255131, by rfl⟩ : syracuseStep 5442805 = 510263) (by norm_num)
theorem B7257073 : Blo 1909435 7257073 := bstep (se 2 (by rfl) ⟨2721402, by rfl⟩ : syracuseStep 7257073 = 5442805) B5442805
theorem B9676097 : Blo 1909435 9676097 := bstep (se 2 (by rfl) ⟨3628536, by rfl⟩ : syracuseStep 9676097 = 7257073) B7257073
theorem B6450731 : Blo 1909435 6450731 := bstep (se 1 (by rfl) ⟨4838048, by rfl⟩ : syracuseStep 6450731 = 9676097) B9676097
theorem B4300487 : Blo 1909435 4300487 := bstep (se 1 (by rfl) ⟨3225365, by rfl⟩ : syracuseStep 4300487 = 6450731) B6450731
theorem B2866991 : Blo 1909435 2866991 := bstep (se 1 (by rfl) ⟨2150243, by rfl⟩ : syracuseStep 2866991 = 4300487) B4300487
theorem B1911327 : Blo 1909435 1911327 := bstep (se 1 (by rfl) ⟨1433495, by rfl⟩ : syracuseStep 1911327 = 2866991) B2866991
theorem B2866997 : Blo 1909435 2866997 := bbase (se 5 (by rfl) ⟨134390, by rfl⟩ : syracuseStep 2866997 = 268781) (by norm_num)
theorem B1911331 : Blo 1909435 1911331 := bstep (se 1 (by rfl) ⟨1433498, by rfl⟩ : syracuseStep 1911331 = 2866997) B2866997
theorem B4838069 : Blo 1909435 4838069 := bbase (se 5 (by rfl) ⟨226784, by rfl⟩ : syracuseStep 4838069 = 453569) (by norm_num)
theorem B3225379 : Blo 1909435 3225379 := bstep (se 1 (by rfl) ⟨2419034, by rfl⟩ : syracuseStep 3225379 = 4838069) B4838069
theorem B4300505 : Blo 1909435 4300505 := bstep (se 2 (by rfl) ⟨1612689, by rfl⟩ : syracuseStep 4300505 = 3225379) B3225379
theorem B2867003 : Blo 1909435 2867003 := bstep (se 1 (by rfl) ⟨2150252, by rfl⟩ : syracuseStep 2867003 = 4300505) B4300505
theorem B1911335 : Blo 1909435 1911335 := bstep (se 1 (by rfl) ⟨1433501, by rfl⟩ : syracuseStep 1911335 = 2867003) B2867003
theorem B2150257 : Blo 1909435 2150257 := bbase (se 2 (by rfl) ⟨806346, by rfl⟩ : syracuseStep 2150257 = 1612693) (by norm_num)
theorem B2867009 : Blo 1909435 2867009 := bstep (se 2 (by rfl) ⟨1075128, by rfl⟩ : syracuseStep 2867009 = 2150257) B2150257
theorem B1911339 : Blo 1909435 1911339 := bstep (se 1 (by rfl) ⟨1433504, by rfl⟩ : syracuseStep 1911339 = 2867009) B2867009
theorem B8164277 : Blo 1909435 8164277 := bbase (se 5 (by rfl) ⟨382700, by rfl⟩ : syracuseStep 8164277 = 765401) (by norm_num)
theorem B5442851 : Blo 1909435 5442851 := bstep (se 1 (by rfl) ⟨4082138, by rfl⟩ : syracuseStep 5442851 = 8164277) B8164277
theorem B3628567 : Blo 1909435 3628567 := bstep (se 1 (by rfl) ⟨2721425, by rfl⟩ : syracuseStep 3628567 = 5442851) B5442851
theorem B4838089 : Blo 1909435 4838089 := bstep (se 2 (by rfl) ⟨1814283, by rfl⟩ : syracuseStep 4838089 = 3628567) B3628567
theorem B6450785 : Blo 1909435 6450785 := bstep (se 2 (by rfl) ⟨2419044, by rfl⟩ : syracuseStep 6450785 = 4838089) B4838089
theorem B4300523 : Blo 1909435 4300523 := bstep (se 1 (by rfl) ⟨3225392, by rfl⟩ : syracuseStep 4300523 = 6450785) B6450785
theorem B2867015 : Blo 1909435 2867015 := bstep (se 1 (by rfl) ⟨2150261, by rfl⟩ : syracuseStep 2867015 = 4300523) B4300523
theorem B1911343 : Blo 1909435 1911343 := bstep (se 1 (by rfl) ⟨1433507, by rfl⟩ : syracuseStep 1911343 = 2867015) B2867015
theorem B2867021 : Blo 1909435 2867021 := bbase (se 3 (by rfl) ⟨537566, by rfl⟩ : syracuseStep 2867021 = 1075133) (by norm_num)
theorem B1911347 : Blo 1909435 1911347 := bstep (se 1 (by rfl) ⟨1433510, by rfl⟩ : syracuseStep 1911347 = 2867021) B2867021
theorem B4300541 : Blo 1909435 4300541 := bbase (se 3 (by rfl) ⟨806351, by rfl⟩ : syracuseStep 4300541 = 1612703) (by norm_num)
theorem B2867027 : Blo 1909435 2867027 := bstep (se 1 (by rfl) ⟨2150270, by rfl⟩ : syracuseStep 2867027 = 4300541) B4300541
theorem B1911351 : Blo 1909435 1911351 := bstep (se 1 (by rfl) ⟨1433513, by rfl⟩ : syracuseStep 1911351 = 2867027) B2867027
theorem B3225413 : Blo 1909435 3225413 := bbase (se 4 (by rfl) ⟨302382, by rfl⟩ : syracuseStep 3225413 = 604765) (by norm_num)
theorem B2150275 : Blo 1909435 2150275 := bstep (se 1 (by rfl) ⟨1612706, by rfl⟩ : syracuseStep 2150275 = 3225413) B3225413
theorem B2867033 : Blo 1909435 2867033 := bstep (se 2 (by rfl) ⟨1075137, by rfl⟩ : syracuseStep 2867033 = 2150275) B2150275
theorem B1911355 : Blo 1909435 1911355 := bstep (se 1 (by rfl) ⟨1433516, by rfl⟩ : syracuseStep 1911355 = 2867033) B2867033
theorem B14514389 : Blo 1909435 14514389 := bbase (se 7 (by rfl) ⟨170090, by rfl⟩ : syracuseStep 14514389 = 340181) (by norm_num)
theorem B9676259 : Blo 1909435 9676259 := bstep (se 1 (by rfl) ⟨7257194, by rfl⟩ : syracuseStep 9676259 = 14514389) B14514389
theorem B6450839 : Blo 1909435 6450839 := bstep (se 1 (by rfl) ⟨4838129, by rfl⟩ : syracuseStep 6450839 = 9676259) B9676259
theorem B4300559 : Blo 1909435 4300559 := bstep (se 1 (by rfl) ⟨3225419, by rfl⟩ : syracuseStep 4300559 = 6450839) B6450839
theorem B2867039 : Blo 1909435 2867039 := bstep (se 1 (by rfl) ⟨2150279, by rfl⟩ : syracuseStep 2867039 = 4300559) B4300559
theorem B1911359 : Blo 1909435 1911359 := bstep (se 1 (by rfl) ⟨1433519, by rfl⟩ : syracuseStep 1911359 = 2867039) B2867039
theorem B2867045 : Blo 1909435 2867045 := bbase (se 4 (by rfl) ⟨268785, by rfl⟩ : syracuseStep 2867045 = 537571) (by norm_num)
theorem B1911363 : Blo 1909435 1911363 := bstep (se 1 (by rfl) ⟨1433522, by rfl⟩ : syracuseStep 1911363 = 2867045) B2867045
theorem B3628613 : Blo 1909435 3628613 := bbase (se 4 (by rfl) ⟨340182, by rfl⟩ : syracuseStep 3628613 = 680365) (by norm_num)
theorem B2419075 : Blo 1909435 2419075 := bstep (se 1 (by rfl) ⟨1814306, by rfl⟩ : syracuseStep 2419075 = 3628613) B3628613
theorem B3225433 : Blo 1909435 3225433 := bstep (se 2 (by rfl) ⟨1209537, by rfl⟩ : syracuseStep 3225433 = 2419075) B2419075
theorem B4300577 : Blo 1909435 4300577 := bstep (se 2 (by rfl) ⟨1612716, by rfl⟩ : syracuseStep 4300577 = 3225433) B3225433
theorem B2867051 : Blo 1909435 2867051 := bstep (se 1 (by rfl) ⟨2150288, by rfl⟩ : syracuseStep 2867051 = 4300577) B4300577
theorem B1911367 : Blo 1909435 1911367 := bstep (se 1 (by rfl) ⟨1433525, by rfl⟩ : syracuseStep 1911367 = 2867051) B2867051
theorem B2150293 : Blo 1909435 2150293 := bbase (se 6 (by rfl) ⟨50397, by rfl⟩ : syracuseStep 2150293 = 100795) (by norm_num)
theorem B2867057 : Blo 1909435 2867057 := bstep (se 2 (by rfl) ⟨1075146, by rfl⟩ : syracuseStep 2867057 = 2150293) B2150293
theorem B1911371 : Blo 1909435 1911371 := bstep (se 1 (by rfl) ⟨1433528, by rfl⟩ : syracuseStep 1911371 = 2867057) B2867057
theorem B2419085 : Blo 1909435 2419085 := bbase (se 3 (by rfl) ⟨453578, by rfl⟩ : syracuseStep 2419085 = 907157) (by norm_num)
theorem B6450893 : Blo 1909435 6450893 := bstep (se 3 (by rfl) ⟨1209542, by rfl⟩ : syracuseStep 6450893 = 2419085) B2419085
theorem B4300595 : Blo 1909435 4300595 := bstep (se 1 (by rfl) ⟨3225446, by rfl⟩ : syracuseStep 4300595 = 6450893) B6450893
theorem B2867063 : Blo 1909435 2867063 := bstep (se 1 (by rfl) ⟨2150297, by rfl⟩ : syracuseStep 2867063 = 4300595) B4300595
theorem B1911375 : Blo 1909435 1911375 := bstep (se 1 (by rfl) ⟨1433531, by rfl⟩ : syracuseStep 1911375 = 2867063) B2867063
theorem B2867069 : Blo 1909435 2867069 := bbase (se 3 (by rfl) ⟨537575, by rfl⟩ : syracuseStep 2867069 = 1075151) (by norm_num)
theorem B1911379 : Blo 1909435 1911379 := bstep (se 1 (by rfl) ⟨1433534, by rfl⟩ : syracuseStep 1911379 = 2867069) B2867069
theorem B4300613 : Blo 1909435 4300613 := bbase (se 4 (by rfl) ⟨403182, by rfl⟩ : syracuseStep 4300613 = 806365) (by norm_num)
theorem B2867075 : Blo 1909435 2867075 := bstep (se 1 (by rfl) ⟨2150306, by rfl⟩ : syracuseStep 2867075 = 4300613) B4300613
theorem B1911383 : Blo 1909435 1911383 := bstep (se 1 (by rfl) ⟨1433537, by rfl⟩ : syracuseStep 1911383 = 2867075) B2867075
theorem B3269477 : Blo 1909435 3269477 := bbase (se 4 (by rfl) ⟨306513, by rfl⟩ : syracuseStep 3269477 = 613027) (by norm_num)
theorem B2179651 : Blo 1909435 2179651 := bstep (se 1 (by rfl) ⟨1634738, by rfl⟩ : syracuseStep 2179651 = 3269477) B3269477
theorem B2906201 : Blo 1909435 2906201 := bstep (se 2 (by rfl) ⟨1089825, by rfl⟩ : syracuseStep 2906201 = 2179651) B2179651
theorem B1937467 : Blo 1909435 1937467 := bstep (se 1 (by rfl) ⟨1453100, by rfl⟩ : syracuseStep 1937467 = 2906201) B2906201
theorem B2583289 : Blo 1909435 2583289 := bstep (se 2 (by rfl) ⟨968733, by rfl⟩ : syracuseStep 2583289 = 1937467) B1937467
theorem B3444385 : Blo 1909435 3444385 := bstep (se 2 (by rfl) ⟨1291644, by rfl⟩ : syracuseStep 3444385 = 2583289) B2583289
theorem B4592513 : Blo 1909435 4592513 := bstep (se 2 (by rfl) ⟨1722192, by rfl⟩ : syracuseStep 4592513 = 3444385) B3444385
theorem B3061675 : Blo 1909435 3061675 := bstep (se 1 (by rfl) ⟨2296256, by rfl⟩ : syracuseStep 3061675 = 4592513) B4592513
theorem B4082233 : Blo 1909435 4082233 := bstep (se 2 (by rfl) ⟨1530837, by rfl⟩ : syracuseStep 4082233 = 3061675) B3061675
theorem B5442977 : Blo 1909435 5442977 := bstep (se 2 (by rfl) ⟨2041116, by rfl⟩ : syracuseStep 5442977 = 4082233) B4082233
theorem B3628651 : Blo 1909435 3628651 := bstep (se 1 (by rfl) ⟨2721488, by rfl⟩ : syracuseStep 3628651 = 5442977) B5442977
theorem B4838201 : Blo 1909435 4838201 := bstep (se 2 (by rfl) ⟨1814325, by rfl⟩ : syracuseStep 4838201 = 3628651) B3628651
theorem B3225467 : Blo 1909435 3225467 := bstep (se 1 (by rfl) ⟨2419100, by rfl⟩ : syracuseStep 3225467 = 4838201) B4838201
theorem B2150311 : Blo 1909435 2150311 := bstep (se 1 (by rfl) ⟨1612733, by rfl⟩ : syracuseStep 2150311 = 3225467) B3225467
theorem B2867081 : Blo 1909435 2867081 := bstep (se 2 (by rfl) ⟨1075155, by rfl⟩ : syracuseStep 2867081 = 2150311) B2150311
theorem B1911387 : Blo 1909435 1911387 := bstep (se 1 (by rfl) ⟨1433540, by rfl⟩ : syracuseStep 1911387 = 2867081) B2867081
theorem B9676421 : Blo 1909435 9676421 := bbase (se 4 (by rfl) ⟨907164, by rfl⟩ : syracuseStep 9676421 = 1814329) (by norm_num)
theorem B6450947 : Blo 1909435 6450947 := bstep (se 1 (by rfl) ⟨4838210, by rfl⟩ : syracuseStep 6450947 = 9676421) B9676421
theorem B4300631 : Blo 1909435 4300631 := bstep (se 1 (by rfl) ⟨3225473, by rfl⟩ : syracuseStep 4300631 = 6450947) B6450947
theorem B2867087 : Blo 1909435 2867087 := bstep (se 1 (by rfl) ⟨2150315, by rfl⟩ : syracuseStep 2867087 = 4300631) B4300631
theorem B1911391 : Blo 1909435 1911391 := bstep (se 1 (by rfl) ⟨1433543, by rfl⟩ : syracuseStep 1911391 = 2867087) B2867087
theorem B2867093 : Blo 1909435 2867093 := bbase (se 6 (by rfl) ⟨67197, by rfl⟩ : syracuseStep 2867093 = 134395) (by norm_num)
theorem B1911395 : Blo 1909435 1911395 := bstep (se 1 (by rfl) ⟨1433546, by rfl⟩ : syracuseStep 1911395 = 2867093) B2867093
theorem B2041129 : Blo 1909435 2041129 := bbase (se 2 (by rfl) ⟨765423, by rfl⟩ : syracuseStep 2041129 = 1530847) (by norm_num)
theorem B10886021 : Blo 1909435 10886021 := bstep (se 4 (by rfl) ⟨1020564, by rfl⟩ : syracuseStep 10886021 = 2041129) B2041129
theorem B7257347 : Blo 1909435 7257347 := bstep (se 1 (by rfl) ⟨5443010, by rfl⟩ : syracuseStep 7257347 = 10886021) B10886021
theorem B4838231 : Blo 1909435 4838231 := bstep (se 1 (by rfl) ⟨3628673, by rfl⟩ : syracuseStep 4838231 = 7257347) B7257347
theorem B3225487 : Blo 1909435 3225487 := bstep (se 1 (by rfl) ⟨2419115, by rfl⟩ : syracuseStep 3225487 = 4838231) B4838231
theorem B4300649 : Blo 1909435 4300649 := bstep (se 2 (by rfl) ⟨1612743, by rfl⟩ : syracuseStep 4300649 = 3225487) B3225487
theorem B2867099 : Blo 1909435 2867099 := bstep (se 1 (by rfl) ⟨2150324, by rfl⟩ : syracuseStep 2867099 = 4300649) B4300649
theorem B1911399 : Blo 1909435 1911399 := bstep (se 1 (by rfl) ⟨1433549, by rfl⟩ : syracuseStep 1911399 = 2867099) B2867099
theorem B2150329 : Blo 1909435 2150329 := bbase (se 2 (by rfl) ⟨806373, by rfl⟩ : syracuseStep 2150329 = 1612747) (by norm_num)
theorem B2867105 : Blo 1909435 2867105 := bstep (se 2 (by rfl) ⟨1075164, by rfl⟩ : syracuseStep 2867105 = 2150329) B2150329
theorem B1911403 : Blo 1909435 1911403 := bstep (se 1 (by rfl) ⟨1433552, by rfl⟩ : syracuseStep 1911403 = 2867105) B2867105
theorem B6123413 : Blo 1909435 6123413 := bbase (se 6 (by rfl) ⟨143517, by rfl⟩ : syracuseStep 6123413 = 287035) (by norm_num)
theorem B4082275 : Blo 1909435 4082275 := bstep (se 1 (by rfl) ⟨3061706, by rfl⟩ : syracuseStep 4082275 = 6123413) B6123413
theorem B5443033 : Blo 1909435 5443033 := bstep (se 2 (by rfl) ⟨2041137, by rfl⟩ : syracuseStep 5443033 = 4082275) B4082275
theorem B7257377 : Blo 1909435 7257377 := bstep (se 2 (by rfl) ⟨2721516, by rfl⟩ : syracuseStep 7257377 = 5443033) B5443033
theorem B4838251 : Blo 1909435 4838251 := bstep (se 1 (by rfl) ⟨3628688, by rfl⟩ : syracuseStep 4838251 = 7257377) B7257377
theorem B6451001 : Blo 1909435 6451001 := bstep (se 2 (by rfl) ⟨2419125, by rfl⟩ : syracuseStep 6451001 = 4838251) B4838251
theorem B4300667 : Blo 1909435 4300667 := bstep (se 1 (by rfl) ⟨3225500, by rfl⟩ : syracuseStep 4300667 = 6451001) B6451001
theorem B2867111 : Blo 1909435 2867111 := bstep (se 1 (by rfl) ⟨2150333, by rfl⟩ : syracuseStep 2867111 = 4300667) B4300667
theorem B1911407 : Blo 1909435 1911407 := bstep (se 1 (by rfl) ⟨1433555, by rfl⟩ : syracuseStep 1911407 = 2867111) B2867111
theorem B2867117 : Blo 1909435 2867117 := bbase (se 3 (by rfl) ⟨537584, by rfl⟩ : syracuseStep 2867117 = 1075169) (by norm_num)
theorem B1911411 : Blo 1909435 1911411 := bstep (se 1 (by rfl) ⟨1433558, by rfl⟩ : syracuseStep 1911411 = 2867117) B2867117
theorem B4300685 : Blo 1909435 4300685 := bbase (se 3 (by rfl) ⟨806378, by rfl⟩ : syracuseStep 4300685 = 1612757) (by norm_num)
theorem B2867123 : Blo 1909435 2867123 := bstep (se 1 (by rfl) ⟨2150342, by rfl⟩ : syracuseStep 2867123 = 4300685) B4300685
theorem B1911415 : Blo 1909435 1911415 := bstep (se 1 (by rfl) ⟨1433561, by rfl⟩ : syracuseStep 1911415 = 2867123) B2867123
theorem B2419141 : Blo 1909435 2419141 := bbase (se 4 (by rfl) ⟨226794, by rfl⟩ : syracuseStep 2419141 = 453589) (by norm_num)
theorem B3225521 : Blo 1909435 3225521 := bstep (se 2 (by rfl) ⟨1209570, by rfl⟩ : syracuseStep 3225521 = 2419141) B2419141
theorem B2150347 : Blo 1909435 2150347 := bstep (se 1 (by rfl) ⟨1612760, by rfl⟩ : syracuseStep 2150347 = 3225521) B3225521
theorem B2867129 : Blo 1909435 2867129 := bstep (se 2 (by rfl) ⟨1075173, by rfl⟩ : syracuseStep 2867129 = 2150347) B2150347
theorem B1911419 : Blo 1909435 1911419 := bstep (se 1 (by rfl) ⟨1433564, by rfl⟩ : syracuseStep 1911419 = 2867129) B2867129
theorem B1963937 : Blo 1909435 1963937 := bbase (se 2 (by rfl) ⟨736476, by rfl⟩ : syracuseStep 1963937 = 1472953) (by norm_num)
theorem B5237165 : Blo 1909435 5237165 := bstep (se 3 (by rfl) ⟨981968, by rfl⟩ : syracuseStep 5237165 = 1963937) B1963937
theorem B3491443 : Blo 1909435 3491443 := bstep (se 1 (by rfl) ⟨2618582, by rfl⟩ : syracuseStep 3491443 = 5237165) B5237165
theorem B18621029 : Blo 1909435 18621029 := bstep (se 4 (by rfl) ⟨1745721, by rfl⟩ : syracuseStep 18621029 = 3491443) B3491443
theorem B49656077 : Blo 1909435 49656077 := bstep (se 3 (by rfl) ⟨9310514, by rfl⟩ : syracuseStep 49656077 = 18621029) B18621029
theorem B33104051 : Blo 1909435 33104051 := bstep (se 1 (by rfl) ⟨24828038, by rfl⟩ : syracuseStep 33104051 = 49656077) B49656077
theorem B22069367 : Blo 1909435 22069367 := bstep (se 1 (by rfl) ⟨16552025, by rfl⟩ : syracuseStep 22069367 = 33104051) B33104051
theorem B14712911 : Blo 1909435 14712911 := bstep (se 1 (by rfl) ⟨11034683, by rfl⟩ : syracuseStep 14712911 = 22069367) B22069367
theorem B9808607 : Blo 1909435 9808607 := bstep (se 1 (by rfl) ⟨7356455, by rfl⟩ : syracuseStep 9808607 = 14712911) B14712911
theorem B6539071 : Blo 1909435 6539071 := bstep (se 1 (by rfl) ⟨4904303, by rfl⟩ : syracuseStep 6539071 = 9808607) B9808607
theorem B8718761 : Blo 1909435 8718761 := bstep (se 2 (by rfl) ⟨3269535, by rfl⟩ : syracuseStep 8718761 = 6539071) B6539071
theorem B5812507 : Blo 1909435 5812507 := bstep (se 1 (by rfl) ⟨4359380, by rfl⟩ : syracuseStep 5812507 = 8718761) B8718761
theorem B7750009 : Blo 1909435 7750009 := bstep (se 2 (by rfl) ⟨2906253, by rfl⟩ : syracuseStep 7750009 = 5812507) B5812507
theorem B10333345 : Blo 1909435 10333345 := bstep (se 2 (by rfl) ⟨3875004, by rfl⟩ : syracuseStep 10333345 = 7750009) B7750009
theorem B13777793 : Blo 1909435 13777793 := bstep (se 2 (by rfl) ⟨5166672, by rfl⟩ : syracuseStep 13777793 = 10333345) B10333345
theorem B9185195 : Blo 1909435 9185195 := bstep (se 1 (by rfl) ⟨6888896, by rfl⟩ : syracuseStep 9185195 = 13777793) B13777793
theorem B24493853 : Blo 1909435 24493853 := bstep (se 3 (by rfl) ⟨4592597, by rfl⟩ : syracuseStep 24493853 = 9185195) B9185195
theorem B16329235 : Blo 1909435 16329235 := bstep (se 1 (by rfl) ⟨12246926, by rfl⟩ : syracuseStep 16329235 = 24493853) B24493853
theorem B21772313 : Blo 1909435 21772313 := bstep (se 2 (by rfl) ⟨8164617, by rfl⟩ : syracuseStep 21772313 = 16329235) B16329235
theorem B14514875 : Blo 1909435 14514875 := bstep (se 1 (by rfl) ⟨10886156, by rfl⟩ : syracuseStep 14514875 = 21772313) B21772313
theorem B9676583 : Blo 1909435 9676583 := bstep (se 1 (by rfl) ⟨7257437, by rfl⟩ : syracuseStep 9676583 = 14514875) B14514875
theorem B6451055 : Blo 1909435 6451055 := bstep (se 1 (by rfl) ⟨4838291, by rfl⟩ : syracuseStep 6451055 = 9676583) B9676583
theorem B4300703 : Blo 1909435 4300703 := bstep (se 1 (by rfl) ⟨3225527, by rfl⟩ : syracuseStep 4300703 = 6451055) B6451055
theorem B2867135 : Blo 1909435 2867135 := bstep (se 1 (by rfl) ⟨2150351, by rfl⟩ : syracuseStep 2867135 = 4300703) B4300703
theorem B1911423 : Blo 1909435 1911423 := bstep (se 1 (by rfl) ⟨1433567, by rfl⟩ : syracuseStep 1911423 = 2867135) B2867135
theorem B2867141 : Blo 1909435 2867141 := bbase (se 4 (by rfl) ⟨268794, by rfl⟩ : syracuseStep 2867141 = 537589) (by norm_num)
theorem B1911427 : Blo 1909435 1911427 := bstep (se 1 (by rfl) ⟨1433570, by rfl⟩ : syracuseStep 1911427 = 2867141) B2867141
theorem B3225541 : Blo 1909435 3225541 := bbase (se 4 (by rfl) ⟨302394, by rfl⟩ : syracuseStep 3225541 = 604789) (by norm_num)
theorem B4300721 : Blo 1909435 4300721 := bstep (se 2 (by rfl) ⟨1612770, by rfl⟩ : syracuseStep 4300721 = 3225541) B3225541
theorem B2867147 : Blo 1909435 2867147 := bstep (se 1 (by rfl) ⟨2150360, by rfl⟩ : syracuseStep 2867147 = 4300721) B4300721
theorem B1911431 : Blo 1909435 1911431 := bstep (se 1 (by rfl) ⟨1433573, by rfl⟩ : syracuseStep 1911431 = 2867147) B2867147
theorem B2150365 : Blo 1909435 2150365 := bbase (se 3 (by rfl) ⟨403193, by rfl⟩ : syracuseStep 2150365 = 806387) (by norm_num)
theorem B2867153 : Blo 1909435 2867153 := bstep (se 2 (by rfl) ⟨1075182, by rfl⟩ : syracuseStep 2867153 = 2150365) B2150365
theorem B1911435 : Blo 1909435 1911435 := bstep (se 1 (by rfl) ⟨1433576, by rfl⟩ : syracuseStep 1911435 = 2867153) B2867153
theorem C0 (j : ℕ) (h1 : 477358 ≤ j) (h2 : j ≤ 477858) : Blo 1909435 (4 * j + 3) := by
  interval_cases j
  · exact B1909435
  · exact B1909439
  · exact B1909443
  · exact B1909447
  · exact B1909451
  · exact B1909455
  · exact B1909459
  · exact B1909463
  · exact B1909467
  · exact B1909471
  · exact B1909475
  · exact B1909479
  · exact B1909483
  · exact B1909487
  · exact B1909491
  · exact B1909495
  · exact B1909499
  · exact B1909503
  · exact B1909507
  · exact B1909511
  · exact B1909515
  · exact B1909519
  · exact B1909523
  · exact B1909527
  · exact B1909531
  · exact B1909535
  · exact B1909539
  · exact B1909543
  · exact B1909547
  · exact B1909551
  · exact B1909555
  · exact B1909559
  · exact B1909563
  · exact B1909567
  · exact B1909571
  · exact B1909575
  · exact B1909579
  · exact B1909583
  · exact B1909587
  · exact B1909591
  · exact B1909595
  · exact B1909599
  · exact B1909603
  · exact B1909607
  · exact B1909611
  · exact B1909615
  · exact B1909619
  · exact B1909623
  · exact B1909627
  · exact B1909631
  · exact B1909635
  · exact B1909639
  · exact B1909643
  · exact B1909647
  · exact B1909651
  · exact B1909655
  · exact B1909659
  · exact B1909663
  · exact B1909667
  · exact B1909671
  · exact B1909675
  · exact B1909679
  · exact B1909683
  · exact B1909687
  · exact B1909691
  · exact B1909695
  · exact B1909699
  · exact B1909703
  · exact B1909707
  · exact B1909711
  · exact B1909715
  · exact B1909719
  · exact B1909723
  · exact B1909727
  · exact B1909731
  · exact B1909735
  · exact B1909739
  · exact B1909743
  · exact B1909747
  · exact B1909751
  · exact B1909755
  · exact B1909759
  · exact B1909763
  · exact B1909767
  · exact B1909771
  · exact B1909775
  · exact B1909779
  · exact B1909783
  · exact B1909787
  · exact B1909791
  · exact B1909795
  · exact B1909799
  · exact B1909803
  · exact B1909807
  · exact B1909811
  · exact B1909815
  · exact B1909819
  · exact B1909823
  · exact B1909827
  · exact B1909831
  · exact B1909835
  · exact B1909839
  · exact B1909843
  · exact B1909847
  · exact B1909851
  · exact B1909855
  · exact B1909859
  · exact B1909863
  · exact B1909867
  · exact B1909871
  · exact B1909875
  · exact B1909879
  · exact B1909883
  · exact B1909887
  · exact B1909891
  · exact B1909895
  · exact B1909899
  · exact B1909903
  · exact B1909907
  · exact B1909911
  · exact B1909915
  · exact B1909919
  · exact B1909923
  · exact B1909927
  · exact B1909931
  · exact B1909935
  · exact B1909939
  · exact B1909943
  · exact B1909947
  · exact B1909951
  · exact B1909955
  · exact B1909959
  · exact B1909963
  · exact B1909967
  · exact B1909971
  · exact B1909975
  · exact B1909979
  · exact B1909983
  · exact B1909987
  · exact B1909991
  · exact B1909995
  · exact B1909999
  · exact B1910003
  · exact B1910007
  · exact B1910011
  · exact B1910015
  · exact B1910019
  · exact B1910023
  · exact B1910027
  · exact B1910031
  · exact B1910035
  · exact B1910039
  · exact B1910043
  · exact B1910047
  · exact B1910051
  · exact B1910055
  · exact B1910059
  · exact B1910063
  · exact B1910067
  · exact B1910071
  · exact B1910075
  · exact B1910079
  · exact B1910083
  · exact B1910087
  · exact B1910091
  · exact B1910095
  · exact B1910099
  · exact B1910103
  · exact B1910107
  · exact B1910111
  · exact B1910115
  · exact B1910119
  · exact B1910123
  · exact B1910127
  · exact B1910131
  · exact B1910135
  · exact B1910139
  · exact B1910143
  · exact B1910147
  · exact B1910151
  · exact B1910155
  · exact B1910159
  · exact B1910163
  · exact B1910167
  · exact B1910171
  · exact B1910175
  · exact B1910179
  · exact B1910183
  · exact B1910187
  · exact B1910191
  · exact B1910195
  · exact B1910199
  · exact B1910203
  · exact B1910207
  · exact B1910211
  · exact B1910215
  · exact B1910219
  · exact B1910223
  · exact B1910227
  · exact B1910231
  · exact B1910235
  · exact B1910239
  · exact B1910243
  · exact B1910247
  · exact B1910251
  · exact B1910255
  · exact B1910259
  · exact B1910263
  · exact B1910267
  · exact B1910271
  · exact B1910275
  · exact B1910279
  · exact B1910283
  · exact B1910287
  · exact B1910291
  · exact B1910295
  · exact B1910299
  · exact B1910303
  · exact B1910307
  · exact B1910311
  · exact B1910315
  · exact B1910319
  · exact B1910323
  · exact B1910327
  · exact B1910331
  · exact B1910335
  · exact B1910339
  · exact B1910343
  · exact B1910347
  · exact B1910351
  · exact B1910355
  · exact B1910359
  · exact B1910363
  · exact B1910367
  · exact B1910371
  · exact B1910375
  · exact B1910379
  · exact B1910383
  · exact B1910387
  · exact B1910391
  · exact B1910395
  · exact B1910399
  · exact B1910403
  · exact B1910407
  · exact B1910411
  · exact B1910415
  · exact B1910419
  · exact B1910423
  · exact B1910427
  · exact B1910431
  · exact B1910435
  · exact B1910439
  · exact B1910443
  · exact B1910447
  · exact B1910451
  · exact B1910455
  · exact B1910459
  · exact B1910463
  · exact B1910467
  · exact B1910471
  · exact B1910475
  · exact B1910479
  · exact B1910483
  · exact B1910487
  · exact B1910491
  · exact B1910495
  · exact B1910499
  · exact B1910503
  · exact B1910507
  · exact B1910511
  · exact B1910515
  · exact B1910519
  · exact B1910523
  · exact B1910527
  · exact B1910531
  · exact B1910535
  · exact B1910539
  · exact B1910543
  · exact B1910547
  · exact B1910551
  · exact B1910555
  · exact B1910559
  · exact B1910563
  · exact B1910567
  · exact B1910571
  · exact B1910575
  · exact B1910579
  · exact B1910583
  · exact B1910587
  · exact B1910591
  · exact B1910595
  · exact B1910599
  · exact B1910603
  · exact B1910607
  · exact B1910611
  · exact B1910615
  · exact B1910619
  · exact B1910623
  · exact B1910627
  · exact B1910631
  · exact B1910635
  · exact B1910639
  · exact B1910643
  · exact B1910647
  · exact B1910651
  · exact B1910655
  · exact B1910659
  · exact B1910663
  · exact B1910667
  · exact B1910671
  · exact B1910675
  · exact B1910679
  · exact B1910683
  · exact B1910687
  · exact B1910691
  · exact B1910695
  · exact B1910699
  · exact B1910703
  · exact B1910707
  · exact B1910711
  · exact B1910715
  · exact B1910719
  · exact B1910723
  · exact B1910727
  · exact B1910731
  · exact B1910735
  · exact B1910739
  · exact B1910743
  · exact B1910747
  · exact B1910751
  · exact B1910755
  · exact B1910759
  · exact B1910763
  · exact B1910767
  · exact B1910771
  · exact B1910775
  · exact B1910779
  · exact B1910783
  · exact B1910787
  · exact B1910791
  · exact B1910795
  · exact B1910799
  · exact B1910803
  · exact B1910807
  · exact B1910811
  · exact B1910815
  · exact B1910819
  · exact B1910823
  · exact B1910827
  · exact B1910831
  · exact B1910835
  · exact B1910839
  · exact B1910843
  · exact B1910847
  · exact B1910851
  · exact B1910855
  · exact B1910859
  · exact B1910863
  · exact B1910867
  · exact B1910871
  · exact B1910875
  · exact B1910879
  · exact B1910883
  · exact B1910887
  · exact B1910891
  · exact B1910895
  · exact B1910899
  · exact B1910903
  · exact B1910907
  · exact B1910911
  · exact B1910915
  · exact B1910919
  · exact B1910923
  · exact B1910927
  · exact B1910931
  · exact B1910935
  · exact B1910939
  · exact B1910943
  · exact B1910947
  · exact B1910951
  · exact B1910955
  · exact B1910959
  · exact B1910963
  · exact B1910967
  · exact B1910971
  · exact B1910975
  · exact B1910979
  · exact B1910983
  · exact B1910987
  · exact B1910991
  · exact B1910995
  · exact B1910999
  · exact B1911003
  · exact B1911007
  · exact B1911011
  · exact B1911015
  · exact B1911019
  · exact B1911023
  · exact B1911027
  · exact B1911031
  · exact B1911035
  · exact B1911039
  · exact B1911043
  · exact B1911047
  · exact B1911051
  · exact B1911055
  · exact B1911059
  · exact B1911063
  · exact B1911067
  · exact B1911071
  · exact B1911075
  · exact B1911079
  · exact B1911083
  · exact B1911087
  · exact B1911091
  · exact B1911095
  · exact B1911099
  · exact B1911103
  · exact B1911107
  · exact B1911111
  · exact B1911115
  · exact B1911119
  · exact B1911123
  · exact B1911127
  · exact B1911131
  · exact B1911135
  · exact B1911139
  · exact B1911143
  · exact B1911147
  · exact B1911151
  · exact B1911155
  · exact B1911159
  · exact B1911163
  · exact B1911167
  · exact B1911171
  · exact B1911175
  · exact B1911179
  · exact B1911183
  · exact B1911187
  · exact B1911191
  · exact B1911195
  · exact B1911199
  · exact B1911203
  · exact B1911207
  · exact B1911211
  · exact B1911215
  · exact B1911219
  · exact B1911223
  · exact B1911227
  · exact B1911231
  · exact B1911235
  · exact B1911239
  · exact B1911243
  · exact B1911247
  · exact B1911251
  · exact B1911255
  · exact B1911259
  · exact B1911263
  · exact B1911267
  · exact B1911271
  · exact B1911275
  · exact B1911279
  · exact B1911283
  · exact B1911287
  · exact B1911291
  · exact B1911295
  · exact B1911299
  · exact B1911303
  · exact B1911307
  · exact B1911311
  · exact B1911315
  · exact B1911319
  · exact B1911323
  · exact B1911327
  · exact B1911331
  · exact B1911335
  · exact B1911339
  · exact B1911343
  · exact B1911347
  · exact B1911351
  · exact B1911355
  · exact B1911359
  · exact B1911363
  · exact B1911367
  · exact B1911371
  · exact B1911375
  · exact B1911379
  · exact B1911383
  · exact B1911387
  · exact B1911391
  · exact B1911395
  · exact B1911399
  · exact B1911403
  · exact B1911407
  · exact B1911411
  · exact B1911415
  · exact B1911419
  · exact B1911423
  · exact B1911427
  · exact B1911431
  · exact B1911435
theorem solution (m : ℕ) (hlo : 1909435 ≤ m) (hhi : m ≤ 1911435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 477358 ≤ j := by omega
    have hj2 : j ≤ 477858 := by omega
    have hb : Blo 1909435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
