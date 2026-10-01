-- Prove2me | solution 1 for syracuse_descends_range_1977435_1979435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:48:09.167983+00:00
-- url     : https://prove2.me/submissions/4da78211-7eed-4626-8fe4-0197f3f57b38

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

theorem B10426133 : Blo 1977435 10426133 := bbase (se 6 (by rfl) ⟨244362, by rfl⟩ : syracuseStep 10426133 = 488725) (by norm_num)
theorem B6950755 : Blo 1977435 6950755 := bstep (se 1 (by rfl) ⟨5213066, by rfl⟩ : syracuseStep 6950755 = 10426133) B10426133
theorem B37070693 : Blo 1977435 37070693 := bstep (se 4 (by rfl) ⟨3475377, by rfl⟩ : syracuseStep 37070693 = 6950755) B6950755
theorem B24713795 : Blo 1977435 24713795 := bstep (se 1 (by rfl) ⟨18535346, by rfl⟩ : syracuseStep 24713795 = 37070693) B37070693
theorem B65903453 : Blo 1977435 65903453 := bstep (se 3 (by rfl) ⟨12356897, by rfl⟩ : syracuseStep 65903453 = 24713795) B24713795
theorem B43935635 : Blo 1977435 43935635 := bstep (se 1 (by rfl) ⟨32951726, by rfl⟩ : syracuseStep 43935635 = 65903453) B65903453
theorem B29290423 : Blo 1977435 29290423 := bstep (se 1 (by rfl) ⟨21967817, by rfl⟩ : syracuseStep 29290423 = 43935635) B43935635
theorem B39053897 : Blo 1977435 39053897 := bstep (se 2 (by rfl) ⟨14645211, by rfl⟩ : syracuseStep 39053897 = 29290423) B29290423
theorem B26035931 : Blo 1977435 26035931 := bstep (se 1 (by rfl) ⟨19526948, by rfl⟩ : syracuseStep 26035931 = 39053897) B39053897
theorem B69429149 : Blo 1977435 69429149 := bstep (se 3 (by rfl) ⟨13017965, by rfl⟩ : syracuseStep 69429149 = 26035931) B26035931
theorem B46286099 : Blo 1977435 46286099 := bstep (se 1 (by rfl) ⟨34714574, by rfl⟩ : syracuseStep 46286099 = 69429149) B69429149
theorem B30857399 : Blo 1977435 30857399 := bstep (se 1 (by rfl) ⟨23143049, by rfl⟩ : syracuseStep 30857399 = 46286099) B46286099
theorem B20571599 : Blo 1977435 20571599 := bstep (se 1 (by rfl) ⟨15428699, by rfl⟩ : syracuseStep 20571599 = 30857399) B30857399
theorem B13714399 : Blo 1977435 13714399 := bstep (se 1 (by rfl) ⟨10285799, by rfl⟩ : syracuseStep 13714399 = 20571599) B20571599
theorem B73143461 : Blo 1977435 73143461 := bstep (se 4 (by rfl) ⟨6857199, by rfl⟩ : syracuseStep 73143461 = 13714399) B13714399
theorem B48762307 : Blo 1977435 48762307 := bstep (se 1 (by rfl) ⟨36571730, by rfl⟩ : syracuseStep 48762307 = 73143461) B73143461
theorem B260065637 : Blo 1977435 260065637 := bstep (se 4 (by rfl) ⟨24381153, by rfl⟩ : syracuseStep 260065637 = 48762307) B48762307
theorem B173377091 : Blo 1977435 173377091 := bstep (se 1 (by rfl) ⟨130032818, by rfl⟩ : syracuseStep 173377091 = 260065637) B260065637
theorem B115584727 : Blo 1977435 115584727 := bstep (se 1 (by rfl) ⟨86688545, by rfl⟩ : syracuseStep 115584727 = 173377091) B173377091
theorem B154112969 : Blo 1977435 154112969 := bstep (se 2 (by rfl) ⟨57792363, by rfl⟩ : syracuseStep 154112969 = 115584727) B115584727
theorem B102741979 : Blo 1977435 102741979 := bstep (se 1 (by rfl) ⟨77056484, by rfl⟩ : syracuseStep 102741979 = 154112969) B154112969
theorem B136989305 : Blo 1977435 136989305 := bstep (se 2 (by rfl) ⟨51370989, by rfl⟩ : syracuseStep 136989305 = 102741979) B102741979
theorem B91326203 : Blo 1977435 91326203 := bstep (se 1 (by rfl) ⟨68494652, by rfl⟩ : syracuseStep 91326203 = 136989305) B136989305
theorem B60884135 : Blo 1977435 60884135 := bstep (se 1 (by rfl) ⟨45663101, by rfl⟩ : syracuseStep 60884135 = 91326203) B91326203
theorem B40589423 : Blo 1977435 40589423 := bstep (se 1 (by rfl) ⟨30442067, by rfl⟩ : syracuseStep 40589423 = 60884135) B60884135
theorem B27059615 : Blo 1977435 27059615 := bstep (se 1 (by rfl) ⟨20294711, by rfl⟩ : syracuseStep 27059615 = 40589423) B40589423
theorem B18039743 : Blo 1977435 18039743 := bstep (se 1 (by rfl) ⟨13529807, by rfl⟩ : syracuseStep 18039743 = 27059615) B27059615
theorem B12026495 : Blo 1977435 12026495 := bstep (se 1 (by rfl) ⟨9019871, by rfl⟩ : syracuseStep 12026495 = 18039743) B18039743
theorem B8017663 : Blo 1977435 8017663 := bstep (se 1 (by rfl) ⟨6013247, by rfl⟩ : syracuseStep 8017663 = 12026495) B12026495
theorem B10690217 : Blo 1977435 10690217 := bstep (se 2 (by rfl) ⟨4008831, by rfl⟩ : syracuseStep 10690217 = 8017663) B8017663
theorem B7126811 : Blo 1977435 7126811 := bstep (se 1 (by rfl) ⟨5345108, by rfl⟩ : syracuseStep 7126811 = 10690217) B10690217
theorem B4751207 : Blo 1977435 4751207 := bstep (se 1 (by rfl) ⟨3563405, by rfl⟩ : syracuseStep 4751207 = 7126811) B7126811
theorem B3167471 : Blo 1977435 3167471 := bstep (se 1 (by rfl) ⟨2375603, by rfl⟩ : syracuseStep 3167471 = 4751207) B4751207
theorem B8446589 : Blo 1977435 8446589 := bstep (se 3 (by rfl) ⟨1583735, by rfl⟩ : syracuseStep 8446589 = 3167471) B3167471
theorem B5631059 : Blo 1977435 5631059 := bstep (se 1 (by rfl) ⟨4223294, by rfl⟩ : syracuseStep 5631059 = 8446589) B8446589
theorem B3754039 : Blo 1977435 3754039 := bstep (se 1 (by rfl) ⟨2815529, by rfl⟩ : syracuseStep 3754039 = 5631059) B5631059
theorem B5005385 : Blo 1977435 5005385 := bstep (se 2 (by rfl) ⟨1877019, by rfl⟩ : syracuseStep 5005385 = 3754039) B3754039
theorem B3336923 : Blo 1977435 3336923 := bstep (se 1 (by rfl) ⟨2502692, by rfl⟩ : syracuseStep 3336923 = 5005385) B5005385
theorem B2224615 : Blo 1977435 2224615 := bstep (se 1 (by rfl) ⟨1668461, by rfl⟩ : syracuseStep 2224615 = 3336923) B3336923
theorem B2966153 : Blo 1977435 2966153 := bstep (se 2 (by rfl) ⟨1112307, by rfl⟩ : syracuseStep 2966153 = 2224615) B2224615
theorem B1977435 : Blo 1977435 1977435 := bstep (se 1 (by rfl) ⟨1483076, by rfl⟩ : syracuseStep 1977435 = 2966153) B2966153
theorem B10010789 : Blo 1977435 10010789 := bbase (se 4 (by rfl) ⟨938511, by rfl⟩ : syracuseStep 10010789 = 1877023) (by norm_num)
theorem B6673859 : Blo 1977435 6673859 := bstep (se 1 (by rfl) ⟨5005394, by rfl⟩ : syracuseStep 6673859 = 10010789) B10010789
theorem B4449239 : Blo 1977435 4449239 := bstep (se 1 (by rfl) ⟨3336929, by rfl⟩ : syracuseStep 4449239 = 6673859) B6673859
theorem B2966159 : Blo 1977435 2966159 := bstep (se 1 (by rfl) ⟨2224619, by rfl⟩ : syracuseStep 2966159 = 4449239) B4449239
theorem B1977439 : Blo 1977435 1977439 := bstep (se 1 (by rfl) ⟨1483079, by rfl⟩ : syracuseStep 1977439 = 2966159) B2966159
theorem B2966165 : Blo 1977435 2966165 := bbase (se 6 (by rfl) ⟨69519, by rfl⟩ : syracuseStep 2966165 = 139039) (by norm_num)
theorem B1977443 : Blo 1977435 1977443 := bstep (se 1 (by rfl) ⟨1483082, by rfl⟩ : syracuseStep 1977443 = 2966165) B2966165
theorem B2254981 : Blo 1977435 2254981 := bbase (se 4 (by rfl) ⟨211404, by rfl⟩ : syracuseStep 2254981 = 422809) (by norm_num)
theorem B3006641 : Blo 1977435 3006641 := bstep (se 2 (by rfl) ⟨1127490, by rfl⟩ : syracuseStep 3006641 = 2254981) B2254981
theorem B8017709 : Blo 1977435 8017709 := bstep (se 3 (by rfl) ⟨1503320, by rfl⟩ : syracuseStep 8017709 = 3006641) B3006641
theorem B21380557 : Blo 1977435 21380557 := bstep (se 3 (by rfl) ⟨4008854, by rfl⟩ : syracuseStep 21380557 = 8017709) B8017709
theorem B28507409 : Blo 1977435 28507409 := bstep (se 2 (by rfl) ⟨10690278, by rfl⟩ : syracuseStep 28507409 = 21380557) B21380557
theorem B19004939 : Blo 1977435 19004939 := bstep (se 1 (by rfl) ⟨14253704, by rfl⟩ : syracuseStep 19004939 = 28507409) B28507409
theorem B12669959 : Blo 1977435 12669959 := bstep (se 1 (by rfl) ⟨9502469, by rfl⟩ : syracuseStep 12669959 = 19004939) B19004939
theorem B8446639 : Blo 1977435 8446639 := bstep (se 1 (by rfl) ⟨6334979, by rfl⟩ : syracuseStep 8446639 = 12669959) B12669959
theorem B11262185 : Blo 1977435 11262185 := bstep (se 2 (by rfl) ⟨4223319, by rfl⟩ : syracuseStep 11262185 = 8446639) B8446639
theorem B7508123 : Blo 1977435 7508123 := bstep (se 1 (by rfl) ⟨5631092, by rfl⟩ : syracuseStep 7508123 = 11262185) B11262185
theorem B5005415 : Blo 1977435 5005415 := bstep (se 1 (by rfl) ⟨3754061, by rfl⟩ : syracuseStep 5005415 = 7508123) B7508123
theorem B3336943 : Blo 1977435 3336943 := bstep (se 1 (by rfl) ⟨2502707, by rfl⟩ : syracuseStep 3336943 = 5005415) B5005415
theorem B4449257 : Blo 1977435 4449257 := bstep (se 2 (by rfl) ⟨1668471, by rfl⟩ : syracuseStep 4449257 = 3336943) B3336943
theorem B2966171 : Blo 1977435 2966171 := bstep (se 1 (by rfl) ⟨2224628, by rfl⟩ : syracuseStep 2966171 = 4449257) B4449257
theorem B1977447 : Blo 1977435 1977447 := bstep (se 1 (by rfl) ⟨1483085, by rfl⟩ : syracuseStep 1977447 = 2966171) B2966171
theorem B2224633 : Blo 1977435 2224633 := bbase (se 2 (by rfl) ⟨834237, by rfl⟩ : syracuseStep 2224633 = 1668475) (by norm_num)
theorem B2966177 : Blo 1977435 2966177 := bstep (se 2 (by rfl) ⟨1112316, by rfl⟩ : syracuseStep 2966177 = 2224633) B2224633
theorem B1977451 : Blo 1977435 1977451 := bstep (se 1 (by rfl) ⟨1483088, by rfl⟩ : syracuseStep 1977451 = 2966177) B2966177
theorem B2672581 : Blo 1977435 2672581 := bbase (se 4 (by rfl) ⟨250554, by rfl⟩ : syracuseStep 2672581 = 501109) (by norm_num)
theorem B3563441 : Blo 1977435 3563441 := bstep (se 2 (by rfl) ⟨1336290, by rfl⟩ : syracuseStep 3563441 = 2672581) B2672581
theorem B2375627 : Blo 1977435 2375627 := bstep (se 1 (by rfl) ⟨1781720, by rfl⟩ : syracuseStep 2375627 = 3563441) B3563441
theorem B6335005 : Blo 1977435 6335005 := bstep (se 3 (by rfl) ⟨1187813, by rfl⟩ : syracuseStep 6335005 = 2375627) B2375627
theorem B8446673 : Blo 1977435 8446673 := bstep (se 2 (by rfl) ⟨3167502, by rfl⟩ : syracuseStep 8446673 = 6335005) B6335005
theorem B5631115 : Blo 1977435 5631115 := bstep (se 1 (by rfl) ⟨4223336, by rfl⟩ : syracuseStep 5631115 = 8446673) B8446673
theorem B7508153 : Blo 1977435 7508153 := bstep (se 2 (by rfl) ⟨2815557, by rfl⟩ : syracuseStep 7508153 = 5631115) B5631115
theorem B5005435 : Blo 1977435 5005435 := bstep (se 1 (by rfl) ⟨3754076, by rfl⟩ : syracuseStep 5005435 = 7508153) B7508153
theorem B6673913 : Blo 1977435 6673913 := bstep (se 2 (by rfl) ⟨2502717, by rfl⟩ : syracuseStep 6673913 = 5005435) B5005435
theorem B4449275 : Blo 1977435 4449275 := bstep (se 1 (by rfl) ⟨3336956, by rfl⟩ : syracuseStep 4449275 = 6673913) B6673913
theorem B2966183 : Blo 1977435 2966183 := bstep (se 1 (by rfl) ⟨2224637, by rfl⟩ : syracuseStep 2966183 = 4449275) B4449275
theorem B1977455 : Blo 1977435 1977455 := bstep (se 1 (by rfl) ⟨1483091, by rfl⟩ : syracuseStep 1977455 = 2966183) B2966183
theorem B2966189 : Blo 1977435 2966189 := bbase (se 3 (by rfl) ⟨556160, by rfl⟩ : syracuseStep 2966189 = 1112321) (by norm_num)
theorem B1977459 : Blo 1977435 1977459 := bstep (se 1 (by rfl) ⟨1483094, by rfl⟩ : syracuseStep 1977459 = 2966189) B2966189
theorem B4449293 : Blo 1977435 4449293 := bbase (se 3 (by rfl) ⟨834242, by rfl⟩ : syracuseStep 4449293 = 1668485) (by norm_num)
theorem B2966195 : Blo 1977435 2966195 := bstep (se 1 (by rfl) ⟨2224646, by rfl⟩ : syracuseStep 2966195 = 4449293) B4449293
theorem B1977463 : Blo 1977435 1977463 := bstep (se 1 (by rfl) ⟨1483097, by rfl⟩ : syracuseStep 1977463 = 2966195) B2966195
theorem B2502733 : Blo 1977435 2502733 := bbase (se 3 (by rfl) ⟨469262, by rfl⟩ : syracuseStep 2502733 = 938525) (by norm_num)
theorem B3336977 : Blo 1977435 3336977 := bstep (se 2 (by rfl) ⟨1251366, by rfl⟩ : syracuseStep 3336977 = 2502733) B2502733
theorem B2224651 : Blo 1977435 2224651 := bstep (se 1 (by rfl) ⟨1668488, by rfl⟩ : syracuseStep 2224651 = 3336977) B3336977
theorem B2966201 : Blo 1977435 2966201 := bstep (se 2 (by rfl) ⟨1112325, by rfl⟩ : syracuseStep 2966201 = 2224651) B2224651
theorem B1977467 : Blo 1977435 1977467 := bstep (se 1 (by rfl) ⟨1483100, by rfl⟩ : syracuseStep 1977467 = 2966201) B2966201
theorem B5492053 : Blo 1977435 5492053 := bbase (se 11 (by rfl) ⟨4022, by rfl⟩ : syracuseStep 5492053 = 8045) (by norm_num)
theorem B7322737 : Blo 1977435 7322737 := bstep (se 2 (by rfl) ⟨2746026, by rfl⟩ : syracuseStep 7322737 = 5492053) B5492053
theorem B9763649 : Blo 1977435 9763649 := bstep (se 2 (by rfl) ⟨3661368, by rfl⟩ : syracuseStep 9763649 = 7322737) B7322737
theorem B6509099 : Blo 1977435 6509099 := bstep (se 1 (by rfl) ⟨4881824, by rfl⟩ : syracuseStep 6509099 = 9763649) B9763649
theorem B17357597 : Blo 1977435 17357597 := bstep (se 3 (by rfl) ⟨3254549, by rfl⟩ : syracuseStep 17357597 = 6509099) B6509099
theorem B11571731 : Blo 1977435 11571731 := bstep (se 1 (by rfl) ⟨8678798, by rfl⟩ : syracuseStep 11571731 = 17357597) B17357597
theorem B7714487 : Blo 1977435 7714487 := bstep (se 1 (by rfl) ⟨5785865, by rfl⟩ : syracuseStep 7714487 = 11571731) B11571731
theorem B20571965 : Blo 1977435 20571965 := bstep (se 3 (by rfl) ⟨3857243, by rfl⟩ : syracuseStep 20571965 = 7714487) B7714487
theorem B13714643 : Blo 1977435 13714643 := bstep (se 1 (by rfl) ⟨10285982, by rfl⟩ : syracuseStep 13714643 = 20571965) B20571965
theorem B36572381 : Blo 1977435 36572381 := bstep (se 3 (by rfl) ⟨6857321, by rfl⟩ : syracuseStep 36572381 = 13714643) B13714643
theorem B24381587 : Blo 1977435 24381587 := bstep (se 1 (by rfl) ⟨18286190, by rfl⟩ : syracuseStep 24381587 = 36572381) B36572381
theorem B16254391 : Blo 1977435 16254391 := bstep (se 1 (by rfl) ⟨12190793, by rfl⟩ : syracuseStep 16254391 = 24381587) B24381587
theorem B21672521 : Blo 1977435 21672521 := bstep (se 2 (by rfl) ⟨8127195, by rfl⟩ : syracuseStep 21672521 = 16254391) B16254391
theorem B14448347 : Blo 1977435 14448347 := bstep (se 1 (by rfl) ⟨10836260, by rfl⟩ : syracuseStep 14448347 = 21672521) B21672521
theorem B9632231 : Blo 1977435 9632231 := bstep (se 1 (by rfl) ⟨7224173, by rfl⟩ : syracuseStep 9632231 = 14448347) B14448347
theorem B6421487 : Blo 1977435 6421487 := bstep (se 1 (by rfl) ⟨4816115, by rfl⟩ : syracuseStep 6421487 = 9632231) B9632231
theorem B68495861 : Blo 1977435 68495861 := bstep (se 5 (by rfl) ⟨3210743, by rfl⟩ : syracuseStep 68495861 = 6421487) B6421487
theorem B45663907 : Blo 1977435 45663907 := bstep (se 1 (by rfl) ⟨34247930, by rfl⟩ : syracuseStep 45663907 = 68495861) B68495861
theorem B60885209 : Blo 1977435 60885209 := bstep (se 2 (by rfl) ⟨22831953, by rfl⟩ : syracuseStep 60885209 = 45663907) B45663907
theorem B162360557 : Blo 1977435 162360557 := bstep (se 3 (by rfl) ⟨30442604, by rfl⟩ : syracuseStep 162360557 = 60885209) B60885209
theorem B108240371 : Blo 1977435 108240371 := bstep (se 1 (by rfl) ⟨81180278, by rfl⟩ : syracuseStep 108240371 = 162360557) B162360557
theorem B72160247 : Blo 1977435 72160247 := bstep (se 1 (by rfl) ⟨54120185, by rfl⟩ : syracuseStep 72160247 = 108240371) B108240371
theorem B48106831 : Blo 1977435 48106831 := bstep (se 1 (by rfl) ⟨36080123, by rfl⟩ : syracuseStep 48106831 = 72160247) B72160247
theorem B64142441 : Blo 1977435 64142441 := bstep (se 2 (by rfl) ⟨24053415, by rfl⟩ : syracuseStep 64142441 = 48106831) B48106831
theorem B42761627 : Blo 1977435 42761627 := bstep (se 1 (by rfl) ⟨32071220, by rfl⟩ : syracuseStep 42761627 = 64142441) B64142441
theorem B28507751 : Blo 1977435 28507751 := bstep (se 1 (by rfl) ⟨21380813, by rfl⟩ : syracuseStep 28507751 = 42761627) B42761627
theorem B19005167 : Blo 1977435 19005167 := bstep (se 1 (by rfl) ⟨14253875, by rfl⟩ : syracuseStep 19005167 = 28507751) B28507751
theorem B12670111 : Blo 1977435 12670111 := bstep (se 1 (by rfl) ⟨9502583, by rfl⟩ : syracuseStep 12670111 = 19005167) B19005167
theorem B16893481 : Blo 1977435 16893481 := bstep (se 2 (by rfl) ⟨6335055, by rfl⟩ : syracuseStep 16893481 = 12670111) B12670111
theorem B22524641 : Blo 1977435 22524641 := bstep (se 2 (by rfl) ⟨8446740, by rfl⟩ : syracuseStep 22524641 = 16893481) B16893481
theorem B15016427 : Blo 1977435 15016427 := bstep (se 1 (by rfl) ⟨11262320, by rfl⟩ : syracuseStep 15016427 = 22524641) B22524641
theorem B10010951 : Blo 1977435 10010951 := bstep (se 1 (by rfl) ⟨7508213, by rfl⟩ : syracuseStep 10010951 = 15016427) B15016427
theorem B6673967 : Blo 1977435 6673967 := bstep (se 1 (by rfl) ⟨5005475, by rfl⟩ : syracuseStep 6673967 = 10010951) B10010951
theorem B4449311 : Blo 1977435 4449311 := bstep (se 1 (by rfl) ⟨3336983, by rfl⟩ : syracuseStep 4449311 = 6673967) B6673967
theorem B2966207 : Blo 1977435 2966207 := bstep (se 1 (by rfl) ⟨2224655, by rfl⟩ : syracuseStep 2966207 = 4449311) B4449311
theorem B1977471 : Blo 1977435 1977471 := bstep (se 1 (by rfl) ⟨1483103, by rfl⟩ : syracuseStep 1977471 = 2966207) B2966207
theorem B2966213 : Blo 1977435 2966213 := bbase (se 4 (by rfl) ⟨278082, by rfl⟩ : syracuseStep 2966213 = 556165) (by norm_num)
theorem B1977475 : Blo 1977435 1977475 := bstep (se 1 (by rfl) ⟨1483106, by rfl⟩ : syracuseStep 1977475 = 2966213) B2966213
theorem B3336997 : Blo 1977435 3336997 := bbase (se 4 (by rfl) ⟨312843, by rfl⟩ : syracuseStep 3336997 = 625687) (by norm_num)
theorem B4449329 : Blo 1977435 4449329 := bstep (se 2 (by rfl) ⟨1668498, by rfl⟩ : syracuseStep 4449329 = 3336997) B3336997
theorem B2966219 : Blo 1977435 2966219 := bstep (se 1 (by rfl) ⟨2224664, by rfl⟩ : syracuseStep 2966219 = 4449329) B4449329
theorem B1977479 : Blo 1977435 1977479 := bstep (se 1 (by rfl) ⟨1483109, by rfl⟩ : syracuseStep 1977479 = 2966219) B2966219
theorem B2224669 : Blo 1977435 2224669 := bbase (se 3 (by rfl) ⟨417125, by rfl⟩ : syracuseStep 2224669 = 834251) (by norm_num)
theorem B2966225 : Blo 1977435 2966225 := bstep (se 2 (by rfl) ⟨1112334, by rfl⟩ : syracuseStep 2966225 = 2224669) B2224669
theorem B1977483 : Blo 1977435 1977483 := bstep (se 1 (by rfl) ⟨1483112, by rfl⟩ : syracuseStep 1977483 = 2966225) B2966225
theorem B6674021 : Blo 1977435 6674021 := bbase (se 4 (by rfl) ⟨625689, by rfl⟩ : syracuseStep 6674021 = 1251379) (by norm_num)
theorem B4449347 : Blo 1977435 4449347 := bstep (se 1 (by rfl) ⟨3337010, by rfl⟩ : syracuseStep 4449347 = 6674021) B6674021
theorem B2966231 : Blo 1977435 2966231 := bstep (se 1 (by rfl) ⟨2224673, by rfl⟩ : syracuseStep 2966231 = 4449347) B4449347
theorem B1977487 : Blo 1977435 1977487 := bstep (se 1 (by rfl) ⟨1483115, by rfl⟩ : syracuseStep 1977487 = 2966231) B2966231
theorem B2966237 : Blo 1977435 2966237 := bbase (se 3 (by rfl) ⟨556169, by rfl⟩ : syracuseStep 2966237 = 1112339) (by norm_num)
theorem B1977491 : Blo 1977435 1977491 := bstep (se 1 (by rfl) ⟨1483118, by rfl⟩ : syracuseStep 1977491 = 2966237) B2966237
theorem B4449365 : Blo 1977435 4449365 := bbase (se 8 (by rfl) ⟨26070, by rfl⟩ : syracuseStep 4449365 = 52141) (by norm_num)
theorem B2966243 : Blo 1977435 2966243 := bstep (se 1 (by rfl) ⟨2224682, by rfl⟩ : syracuseStep 2966243 = 4449365) B4449365
theorem B1977495 : Blo 1977435 1977495 := bstep (se 1 (by rfl) ⟨1483121, by rfl⟩ : syracuseStep 1977495 = 2966243) B2966243
theorem B2255041 : Blo 1977435 2255041 := bbase (se 2 (by rfl) ⟨845640, by rfl⟩ : syracuseStep 2255041 = 1691281) (by norm_num)
theorem B3006721 : Blo 1977435 3006721 := bstep (se 2 (by rfl) ⟨1127520, by rfl⟩ : syracuseStep 3006721 = 2255041) B2255041
theorem B4008961 : Blo 1977435 4008961 := bstep (se 2 (by rfl) ⟨1503360, by rfl⟩ : syracuseStep 4008961 = 3006721) B3006721
theorem B5345281 : Blo 1977435 5345281 := bstep (se 2 (by rfl) ⟨2004480, by rfl⟩ : syracuseStep 5345281 = 4008961) B4008961
theorem B7127041 : Blo 1977435 7127041 := bstep (se 2 (by rfl) ⟨2672640, by rfl⟩ : syracuseStep 7127041 = 5345281) B5345281
theorem B9502721 : Blo 1977435 9502721 := bstep (se 2 (by rfl) ⟨3563520, by rfl⟩ : syracuseStep 9502721 = 7127041) B7127041
theorem B6335147 : Blo 1977435 6335147 := bstep (se 1 (by rfl) ⟨4751360, by rfl⟩ : syracuseStep 6335147 = 9502721) B9502721
theorem B4223431 : Blo 1977435 4223431 := bstep (se 1 (by rfl) ⟨3167573, by rfl⟩ : syracuseStep 4223431 = 6335147) B6335147
theorem B5631241 : Blo 1977435 5631241 := bstep (se 2 (by rfl) ⟨2111715, by rfl⟩ : syracuseStep 5631241 = 4223431) B4223431
theorem B7508321 : Blo 1977435 7508321 := bstep (se 2 (by rfl) ⟨2815620, by rfl⟩ : syracuseStep 7508321 = 5631241) B5631241
theorem B5005547 : Blo 1977435 5005547 := bstep (se 1 (by rfl) ⟨3754160, by rfl⟩ : syracuseStep 5005547 = 7508321) B7508321
theorem B3337031 : Blo 1977435 3337031 := bstep (se 1 (by rfl) ⟨2502773, by rfl⟩ : syracuseStep 3337031 = 5005547) B5005547
theorem B2224687 : Blo 1977435 2224687 := bstep (se 1 (by rfl) ⟨1668515, by rfl⟩ : syracuseStep 2224687 = 3337031) B3337031
theorem B2966249 : Blo 1977435 2966249 := bstep (se 2 (by rfl) ⟨1112343, by rfl⟩ : syracuseStep 2966249 = 2224687) B2224687
theorem B1977499 : Blo 1977435 1977499 := bstep (se 1 (by rfl) ⟨1483124, by rfl⟩ : syracuseStep 1977499 = 2966249) B2966249
theorem B2672645 : Blo 1977435 2672645 := bbase (se 4 (by rfl) ⟨250560, by rfl⟩ : syracuseStep 2672645 = 501121) (by norm_num)
theorem B28508213 : Blo 1977435 28508213 := bstep (se 5 (by rfl) ⟨1336322, by rfl⟩ : syracuseStep 28508213 = 2672645) B2672645
theorem B19005475 : Blo 1977435 19005475 := bstep (se 1 (by rfl) ⟨14254106, by rfl⟩ : syracuseStep 19005475 = 28508213) B28508213
theorem B25340633 : Blo 1977435 25340633 := bstep (se 2 (by rfl) ⟨9502737, by rfl⟩ : syracuseStep 25340633 = 19005475) B19005475
theorem B16893755 : Blo 1977435 16893755 := bstep (se 1 (by rfl) ⟨12670316, by rfl⟩ : syracuseStep 16893755 = 25340633) B25340633
theorem B11262503 : Blo 1977435 11262503 := bstep (se 1 (by rfl) ⟨8446877, by rfl⟩ : syracuseStep 11262503 = 16893755) B16893755
theorem B7508335 : Blo 1977435 7508335 := bstep (se 1 (by rfl) ⟨5631251, by rfl⟩ : syracuseStep 7508335 = 11262503) B11262503
theorem B10011113 : Blo 1977435 10011113 := bstep (se 2 (by rfl) ⟨3754167, by rfl⟩ : syracuseStep 10011113 = 7508335) B7508335
theorem B6674075 : Blo 1977435 6674075 := bstep (se 1 (by rfl) ⟨5005556, by rfl⟩ : syracuseStep 6674075 = 10011113) B10011113
theorem B4449383 : Blo 1977435 4449383 := bstep (se 1 (by rfl) ⟨3337037, by rfl⟩ : syracuseStep 4449383 = 6674075) B6674075
theorem B2966255 : Blo 1977435 2966255 := bstep (se 1 (by rfl) ⟨2224691, by rfl⟩ : syracuseStep 2966255 = 4449383) B4449383
theorem B1977503 : Blo 1977435 1977503 := bstep (se 1 (by rfl) ⟨1483127, by rfl⟩ : syracuseStep 1977503 = 2966255) B2966255
theorem B2966261 : Blo 1977435 2966261 := bbase (se 5 (by rfl) ⟨139043, by rfl⟩ : syracuseStep 2966261 = 278087) (by norm_num)
theorem B1977507 : Blo 1977435 1977507 := bstep (se 1 (by rfl) ⟨1483130, by rfl⟩ : syracuseStep 1977507 = 2966261) B2966261
theorem B4751389 : Blo 1977435 4751389 := bbase (se 3 (by rfl) ⟨890885, by rfl⟩ : syracuseStep 4751389 = 1781771) (by norm_num)
theorem B6335185 : Blo 1977435 6335185 := bstep (se 2 (by rfl) ⟨2375694, by rfl⟩ : syracuseStep 6335185 = 4751389) B4751389
theorem B8446913 : Blo 1977435 8446913 := bstep (se 2 (by rfl) ⟨3167592, by rfl⟩ : syracuseStep 8446913 = 6335185) B6335185
theorem B5631275 : Blo 1977435 5631275 := bstep (se 1 (by rfl) ⟨4223456, by rfl⟩ : syracuseStep 5631275 = 8446913) B8446913
theorem B3754183 : Blo 1977435 3754183 := bstep (se 1 (by rfl) ⟨2815637, by rfl⟩ : syracuseStep 3754183 = 5631275) B5631275
theorem B5005577 : Blo 1977435 5005577 := bstep (se 2 (by rfl) ⟨1877091, by rfl⟩ : syracuseStep 5005577 = 3754183) B3754183
theorem B3337051 : Blo 1977435 3337051 := bstep (se 1 (by rfl) ⟨2502788, by rfl⟩ : syracuseStep 3337051 = 5005577) B5005577
theorem B4449401 : Blo 1977435 4449401 := bstep (se 2 (by rfl) ⟨1668525, by rfl⟩ : syracuseStep 4449401 = 3337051) B3337051
theorem B2966267 : Blo 1977435 2966267 := bstep (se 1 (by rfl) ⟨2224700, by rfl⟩ : syracuseStep 2966267 = 4449401) B4449401
theorem B1977511 : Blo 1977435 1977511 := bstep (se 1 (by rfl) ⟨1483133, by rfl⟩ : syracuseStep 1977511 = 2966267) B2966267
theorem B2224705 : Blo 1977435 2224705 := bbase (se 2 (by rfl) ⟨834264, by rfl⟩ : syracuseStep 2224705 = 1668529) (by norm_num)
theorem B2966273 : Blo 1977435 2966273 := bstep (se 2 (by rfl) ⟨1112352, by rfl⟩ : syracuseStep 2966273 = 2224705) B2224705
theorem B1977515 : Blo 1977435 1977515 := bstep (se 1 (by rfl) ⟨1483136, by rfl⟩ : syracuseStep 1977515 = 2966273) B2966273
theorem B5005597 : Blo 1977435 5005597 := bbase (se 3 (by rfl) ⟨938549, by rfl⟩ : syracuseStep 5005597 = 1877099) (by norm_num)
theorem B6674129 : Blo 1977435 6674129 := bstep (se 2 (by rfl) ⟨2502798, by rfl⟩ : syracuseStep 6674129 = 5005597) B5005597
theorem B4449419 : Blo 1977435 4449419 := bstep (se 1 (by rfl) ⟨3337064, by rfl⟩ : syracuseStep 4449419 = 6674129) B6674129
theorem B2966279 : Blo 1977435 2966279 := bstep (se 1 (by rfl) ⟨2224709, by rfl⟩ : syracuseStep 2966279 = 4449419) B4449419
theorem B1977519 : Blo 1977435 1977519 := bstep (se 1 (by rfl) ⟨1483139, by rfl⟩ : syracuseStep 1977519 = 2966279) B2966279
theorem B2966285 : Blo 1977435 2966285 := bbase (se 3 (by rfl) ⟨556178, by rfl⟩ : syracuseStep 2966285 = 1112357) (by norm_num)
theorem B1977523 : Blo 1977435 1977523 := bstep (se 1 (by rfl) ⟨1483142, by rfl⟩ : syracuseStep 1977523 = 2966285) B2966285
theorem B4449437 : Blo 1977435 4449437 := bbase (se 3 (by rfl) ⟨834269, by rfl⟩ : syracuseStep 4449437 = 1668539) (by norm_num)
theorem B2966291 : Blo 1977435 2966291 := bstep (se 1 (by rfl) ⟨2224718, by rfl⟩ : syracuseStep 2966291 = 4449437) B4449437
theorem B1977527 : Blo 1977435 1977527 := bstep (se 1 (by rfl) ⟨1483145, by rfl⟩ : syracuseStep 1977527 = 2966291) B2966291
theorem B3337085 : Blo 1977435 3337085 := bbase (se 3 (by rfl) ⟨625703, by rfl⟩ : syracuseStep 3337085 = 1251407) (by norm_num)
theorem B2224723 : Blo 1977435 2224723 := bstep (se 1 (by rfl) ⟨1668542, by rfl⟩ : syracuseStep 2224723 = 3337085) B3337085
theorem B2966297 : Blo 1977435 2966297 := bstep (se 2 (by rfl) ⟨1112361, by rfl⟩ : syracuseStep 2966297 = 2224723) B2224723
theorem B1977531 : Blo 1977435 1977531 := bstep (se 1 (by rfl) ⟨1483148, by rfl⟩ : syracuseStep 1977531 = 2966297) B2966297
theorem B2004517 : Blo 1977435 2004517 := bbase (se 4 (by rfl) ⟨187923, by rfl⟩ : syracuseStep 2004517 = 375847) (by norm_num)
theorem B2672689 : Blo 1977435 2672689 := bstep (se 2 (by rfl) ⟨1002258, by rfl⟩ : syracuseStep 2672689 = 2004517) B2004517
theorem B3563585 : Blo 1977435 3563585 := bstep (se 2 (by rfl) ⟨1336344, by rfl⟩ : syracuseStep 3563585 = 2672689) B2672689
theorem B2375723 : Blo 1977435 2375723 := bstep (se 1 (by rfl) ⟨1781792, by rfl⟩ : syracuseStep 2375723 = 3563585) B3563585
theorem B6335261 : Blo 1977435 6335261 := bstep (se 3 (by rfl) ⟨1187861, by rfl⟩ : syracuseStep 6335261 = 2375723) B2375723
theorem B4223507 : Blo 1977435 4223507 := bstep (se 1 (by rfl) ⟨3167630, by rfl⟩ : syracuseStep 4223507 = 6335261) B6335261
theorem B11262685 : Blo 1977435 11262685 := bstep (se 3 (by rfl) ⟨2111753, by rfl⟩ : syracuseStep 11262685 = 4223507) B4223507
theorem B15016913 : Blo 1977435 15016913 := bstep (se 2 (by rfl) ⟨5631342, by rfl⟩ : syracuseStep 15016913 = 11262685) B11262685
theorem B10011275 : Blo 1977435 10011275 := bstep (se 1 (by rfl) ⟨7508456, by rfl⟩ : syracuseStep 10011275 = 15016913) B15016913
theorem B6674183 : Blo 1977435 6674183 := bstep (se 1 (by rfl) ⟨5005637, by rfl⟩ : syracuseStep 6674183 = 10011275) B10011275
theorem B4449455 : Blo 1977435 4449455 := bstep (se 1 (by rfl) ⟨3337091, by rfl⟩ : syracuseStep 4449455 = 6674183) B6674183
theorem B2966303 : Blo 1977435 2966303 := bstep (se 1 (by rfl) ⟨2224727, by rfl⟩ : syracuseStep 2966303 = 4449455) B4449455
theorem B1977535 : Blo 1977435 1977535 := bstep (se 1 (by rfl) ⟨1483151, by rfl⟩ : syracuseStep 1977535 = 2966303) B2966303
theorem B2966309 : Blo 1977435 2966309 := bbase (se 4 (by rfl) ⟨278091, by rfl⟩ : syracuseStep 2966309 = 556183) (by norm_num)
theorem B1977539 : Blo 1977435 1977539 := bstep (se 1 (by rfl) ⟨1483154, by rfl⟩ : syracuseStep 1977539 = 2966309) B2966309
theorem B2502829 : Blo 1977435 2502829 := bbase (se 3 (by rfl) ⟨469280, by rfl⟩ : syracuseStep 2502829 = 938561) (by norm_num)
theorem B3337105 : Blo 1977435 3337105 := bstep (se 2 (by rfl) ⟨1251414, by rfl⟩ : syracuseStep 3337105 = 2502829) B2502829
theorem B4449473 : Blo 1977435 4449473 := bstep (se 2 (by rfl) ⟨1668552, by rfl⟩ : syracuseStep 4449473 = 3337105) B3337105
theorem B2966315 : Blo 1977435 2966315 := bstep (se 1 (by rfl) ⟨2224736, by rfl⟩ : syracuseStep 2966315 = 4449473) B4449473
theorem B1977543 : Blo 1977435 1977543 := bstep (se 1 (by rfl) ⟨1483157, by rfl⟩ : syracuseStep 1977543 = 2966315) B2966315
theorem B2224741 : Blo 1977435 2224741 := bbase (se 4 (by rfl) ⟨208569, by rfl⟩ : syracuseStep 2224741 = 417139) (by norm_num)
theorem B2966321 : Blo 1977435 2966321 := bstep (se 2 (by rfl) ⟨1112370, by rfl⟩ : syracuseStep 2966321 = 2224741) B2224741
theorem B1977547 : Blo 1977435 1977547 := bstep (se 1 (by rfl) ⟨1483160, by rfl⟩ : syracuseStep 1977547 = 2966321) B2966321
theorem B3210877 : Blo 1977435 3210877 := bbase (se 3 (by rfl) ⟨602039, by rfl⟩ : syracuseStep 3210877 = 1204079) (by norm_num)
theorem B4281169 : Blo 1977435 4281169 := bstep (se 2 (by rfl) ⟨1605438, by rfl⟩ : syracuseStep 4281169 = 3210877) B3210877
theorem B5708225 : Blo 1977435 5708225 := bstep (se 2 (by rfl) ⟨2140584, by rfl⟩ : syracuseStep 5708225 = 4281169) B4281169
theorem B3805483 : Blo 1977435 3805483 := bstep (se 1 (by rfl) ⟨2854112, by rfl⟩ : syracuseStep 3805483 = 5708225) B5708225
theorem B5073977 : Blo 1977435 5073977 := bstep (se 2 (by rfl) ⟨1902741, by rfl⟩ : syracuseStep 5073977 = 3805483) B3805483
theorem B3382651 : Blo 1977435 3382651 := bstep (se 1 (by rfl) ⟨2536988, by rfl⟩ : syracuseStep 3382651 = 5073977) B5073977
theorem B18040805 : Blo 1977435 18040805 := bstep (se 4 (by rfl) ⟨1691325, by rfl⟩ : syracuseStep 18040805 = 3382651) B3382651
theorem B12027203 : Blo 1977435 12027203 := bstep (se 1 (by rfl) ⟨9020402, by rfl⟩ : syracuseStep 12027203 = 18040805) B18040805
theorem B8018135 : Blo 1977435 8018135 := bstep (se 1 (by rfl) ⟨6013601, by rfl⟩ : syracuseStep 8018135 = 12027203) B12027203
theorem B5345423 : Blo 1977435 5345423 := bstep (se 1 (by rfl) ⟨4009067, by rfl⟩ : syracuseStep 5345423 = 8018135) B8018135
theorem B3563615 : Blo 1977435 3563615 := bstep (se 1 (by rfl) ⟨2672711, by rfl⟩ : syracuseStep 3563615 = 5345423) B5345423
theorem B2375743 : Blo 1977435 2375743 := bstep (se 1 (by rfl) ⟨1781807, by rfl⟩ : syracuseStep 2375743 = 3563615) B3563615
theorem B3167657 : Blo 1977435 3167657 := bstep (se 2 (by rfl) ⟨1187871, by rfl⟩ : syracuseStep 3167657 = 2375743) B2375743
theorem B2111771 : Blo 1977435 2111771 := bstep (se 1 (by rfl) ⟨1583828, by rfl⟩ : syracuseStep 2111771 = 3167657) B3167657
theorem B5631389 : Blo 1977435 5631389 := bstep (se 3 (by rfl) ⟨1055885, by rfl⟩ : syracuseStep 5631389 = 2111771) B2111771
theorem B3754259 : Blo 1977435 3754259 := bstep (se 1 (by rfl) ⟨2815694, by rfl⟩ : syracuseStep 3754259 = 5631389) B5631389
theorem B2502839 : Blo 1977435 2502839 := bstep (se 1 (by rfl) ⟨1877129, by rfl⟩ : syracuseStep 2502839 = 3754259) B3754259
theorem B6674237 : Blo 1977435 6674237 := bstep (se 3 (by rfl) ⟨1251419, by rfl⟩ : syracuseStep 6674237 = 2502839) B2502839
theorem B4449491 : Blo 1977435 4449491 := bstep (se 1 (by rfl) ⟨3337118, by rfl⟩ : syracuseStep 4449491 = 6674237) B6674237
theorem B2966327 : Blo 1977435 2966327 := bstep (se 1 (by rfl) ⟨2224745, by rfl⟩ : syracuseStep 2966327 = 4449491) B4449491
theorem B1977551 : Blo 1977435 1977551 := bstep (se 1 (by rfl) ⟨1483163, by rfl⟩ : syracuseStep 1977551 = 2966327) B2966327
theorem B2966333 : Blo 1977435 2966333 := bbase (se 3 (by rfl) ⟨556187, by rfl⟩ : syracuseStep 2966333 = 1112375) (by norm_num)
theorem B1977555 : Blo 1977435 1977555 := bstep (se 1 (by rfl) ⟨1483166, by rfl⟩ : syracuseStep 1977555 = 2966333) B2966333
theorem B4449509 : Blo 1977435 4449509 := bbase (se 4 (by rfl) ⟨417141, by rfl⟩ : syracuseStep 4449509 = 834283) (by norm_num)
theorem B2966339 : Blo 1977435 2966339 := bstep (se 1 (by rfl) ⟨2224754, by rfl⟩ : syracuseStep 2966339 = 4449509) B4449509
theorem B1977559 : Blo 1977435 1977559 := bstep (se 1 (by rfl) ⟨1483169, by rfl⟩ : syracuseStep 1977559 = 2966339) B2966339
theorem B5005709 : Blo 1977435 5005709 := bbase (se 3 (by rfl) ⟨938570, by rfl⟩ : syracuseStep 5005709 = 1877141) (by norm_num)
theorem B3337139 : Blo 1977435 3337139 := bstep (se 1 (by rfl) ⟨2502854, by rfl⟩ : syracuseStep 3337139 = 5005709) B5005709
theorem B2224759 : Blo 1977435 2224759 := bstep (se 1 (by rfl) ⟨1668569, by rfl⟩ : syracuseStep 2224759 = 3337139) B3337139
theorem B2966345 : Blo 1977435 2966345 := bstep (se 2 (by rfl) ⟨1112379, by rfl⟩ : syracuseStep 2966345 = 2224759) B2224759
theorem B1977563 : Blo 1977435 1977563 := bstep (se 1 (by rfl) ⟨1483172, by rfl⟩ : syracuseStep 1977563 = 2966345) B2966345
theorem B2815717 : Blo 1977435 2815717 := bbase (se 4 (by rfl) ⟨263973, by rfl⟩ : syracuseStep 2815717 = 527947) (by norm_num)
theorem B3754289 : Blo 1977435 3754289 := bstep (se 2 (by rfl) ⟨1407858, by rfl⟩ : syracuseStep 3754289 = 2815717) B2815717
theorem B10011437 : Blo 1977435 10011437 := bstep (se 3 (by rfl) ⟨1877144, by rfl⟩ : syracuseStep 10011437 = 3754289) B3754289
theorem B6674291 : Blo 1977435 6674291 := bstep (se 1 (by rfl) ⟨5005718, by rfl⟩ : syracuseStep 6674291 = 10011437) B10011437
theorem B4449527 : Blo 1977435 4449527 := bstep (se 1 (by rfl) ⟨3337145, by rfl⟩ : syracuseStep 4449527 = 6674291) B6674291
theorem B2966351 : Blo 1977435 2966351 := bstep (se 1 (by rfl) ⟨2224763, by rfl⟩ : syracuseStep 2966351 = 4449527) B4449527
theorem B1977567 : Blo 1977435 1977567 := bstep (se 1 (by rfl) ⟨1483175, by rfl⟩ : syracuseStep 1977567 = 2966351) B2966351
theorem B2966357 : Blo 1977435 2966357 := bbase (se 9 (by rfl) ⟨8690, by rfl⟩ : syracuseStep 2966357 = 17381) (by norm_num)
theorem B1977571 : Blo 1977435 1977571 := bstep (se 1 (by rfl) ⟨1483178, by rfl⟩ : syracuseStep 1977571 = 2966357) B2966357
theorem B3047861 : Blo 1977435 3047861 := bbase (se 5 (by rfl) ⟨142868, by rfl⟩ : syracuseStep 3047861 = 285737) (by norm_num)
theorem B8127629 : Blo 1977435 8127629 := bstep (se 3 (by rfl) ⟨1523930, by rfl⟩ : syracuseStep 8127629 = 3047861) B3047861
theorem B5418419 : Blo 1977435 5418419 := bstep (se 1 (by rfl) ⟨4063814, by rfl⟩ : syracuseStep 5418419 = 8127629) B8127629
theorem B14449117 : Blo 1977435 14449117 := bstep (se 3 (by rfl) ⟨2709209, by rfl⟩ : syracuseStep 14449117 = 5418419) B5418419
theorem B19265489 : Blo 1977435 19265489 := bstep (se 2 (by rfl) ⟨7224558, by rfl⟩ : syracuseStep 19265489 = 14449117) B14449117
theorem B12843659 : Blo 1977435 12843659 := bstep (se 1 (by rfl) ⟨9632744, by rfl⟩ : syracuseStep 12843659 = 19265489) B19265489
theorem B8562439 : Blo 1977435 8562439 := bstep (se 1 (by rfl) ⟨6421829, by rfl⟩ : syracuseStep 8562439 = 12843659) B12843659
theorem B11416585 : Blo 1977435 11416585 := bstep (se 2 (by rfl) ⟨4281219, by rfl⟩ : syracuseStep 11416585 = 8562439) B8562439
theorem B15222113 : Blo 1977435 15222113 := bstep (se 2 (by rfl) ⟨5708292, by rfl⟩ : syracuseStep 15222113 = 11416585) B11416585
theorem B10148075 : Blo 1977435 10148075 := bstep (se 1 (by rfl) ⟨7611056, by rfl⟩ : syracuseStep 10148075 = 15222113) B15222113
theorem B6765383 : Blo 1977435 6765383 := bstep (se 1 (by rfl) ⟨5074037, by rfl⟩ : syracuseStep 6765383 = 10148075) B10148075
theorem B4510255 : Blo 1977435 4510255 := bstep (se 1 (by rfl) ⟨3382691, by rfl⟩ : syracuseStep 4510255 = 6765383) B6765383
theorem B6013673 : Blo 1977435 6013673 := bstep (se 2 (by rfl) ⟨2255127, by rfl⟩ : syracuseStep 6013673 = 4510255) B4510255
theorem B4009115 : Blo 1977435 4009115 := bstep (se 1 (by rfl) ⟨3006836, by rfl⟩ : syracuseStep 4009115 = 6013673) B6013673
theorem B10690973 : Blo 1977435 10690973 := bstep (se 3 (by rfl) ⟨2004557, by rfl⟩ : syracuseStep 10690973 = 4009115) B4009115
theorem B7127315 : Blo 1977435 7127315 := bstep (se 1 (by rfl) ⟨5345486, by rfl⟩ : syracuseStep 7127315 = 10690973) B10690973
theorem B4751543 : Blo 1977435 4751543 := bstep (se 1 (by rfl) ⟨3563657, by rfl⟩ : syracuseStep 4751543 = 7127315) B7127315
theorem B3167695 : Blo 1977435 3167695 := bstep (se 1 (by rfl) ⟨2375771, by rfl⟩ : syracuseStep 3167695 = 4751543) B4751543
theorem B4223593 : Blo 1977435 4223593 := bstep (se 2 (by rfl) ⟨1583847, by rfl⟩ : syracuseStep 4223593 = 3167695) B3167695
theorem B5631457 : Blo 1977435 5631457 := bstep (se 2 (by rfl) ⟨2111796, by rfl⟩ : syracuseStep 5631457 = 4223593) B4223593
theorem B7508609 : Blo 1977435 7508609 := bstep (se 2 (by rfl) ⟨2815728, by rfl⟩ : syracuseStep 7508609 = 5631457) B5631457
theorem B5005739 : Blo 1977435 5005739 := bstep (se 1 (by rfl) ⟨3754304, by rfl⟩ : syracuseStep 5005739 = 7508609) B7508609
theorem B3337159 : Blo 1977435 3337159 := bstep (se 1 (by rfl) ⟨2502869, by rfl⟩ : syracuseStep 3337159 = 5005739) B5005739
theorem B4449545 : Blo 1977435 4449545 := bstep (se 2 (by rfl) ⟨1668579, by rfl⟩ : syracuseStep 4449545 = 3337159) B3337159
theorem B2966363 : Blo 1977435 2966363 := bstep (se 1 (by rfl) ⟨2224772, by rfl⟩ : syracuseStep 2966363 = 4449545) B4449545
theorem B1977575 : Blo 1977435 1977575 := bstep (se 1 (by rfl) ⟨1483181, by rfl⟩ : syracuseStep 1977575 = 2966363) B2966363
theorem B2224777 : Blo 1977435 2224777 := bbase (se 2 (by rfl) ⟨834291, by rfl⟩ : syracuseStep 2224777 = 1668583) (by norm_num)
theorem B2966369 : Blo 1977435 2966369 := bstep (se 2 (by rfl) ⟨1112388, by rfl⟩ : syracuseStep 2966369 = 2224777) B2224777
theorem B1977579 : Blo 1977435 1977579 := bstep (se 1 (by rfl) ⟨1483184, by rfl⟩ : syracuseStep 1977579 = 2966369) B2966369
theorem B3299141 : Blo 1977435 3299141 := bbase (se 4 (by rfl) ⟨309294, by rfl⟩ : syracuseStep 3299141 = 618589) (by norm_num)
theorem B8797709 : Blo 1977435 8797709 := bstep (se 3 (by rfl) ⟨1649570, by rfl⟩ : syracuseStep 8797709 = 3299141) B3299141
theorem B5865139 : Blo 1977435 5865139 := bstep (se 1 (by rfl) ⟨4398854, by rfl⟩ : syracuseStep 5865139 = 8797709) B8797709
theorem B7820185 : Blo 1977435 7820185 := bstep (se 2 (by rfl) ⟨2932569, by rfl⟩ : syracuseStep 7820185 = 5865139) B5865139
theorem B10426913 : Blo 1977435 10426913 := bstep (se 2 (by rfl) ⟨3910092, by rfl⟩ : syracuseStep 10426913 = 7820185) B7820185
theorem B6951275 : Blo 1977435 6951275 := bstep (se 1 (by rfl) ⟨5213456, by rfl⟩ : syracuseStep 6951275 = 10426913) B10426913
theorem B4634183 : Blo 1977435 4634183 := bstep (se 1 (by rfl) ⟨3475637, by rfl⟩ : syracuseStep 4634183 = 6951275) B6951275
theorem B12357821 : Blo 1977435 12357821 := bstep (se 3 (by rfl) ⟨2317091, by rfl⟩ : syracuseStep 12357821 = 4634183) B4634183
theorem B8238547 : Blo 1977435 8238547 := bstep (se 1 (by rfl) ⟨6178910, by rfl⟩ : syracuseStep 8238547 = 12357821) B12357821
theorem B10984729 : Blo 1977435 10984729 := bstep (se 2 (by rfl) ⟨4119273, by rfl⟩ : syracuseStep 10984729 = 8238547) B8238547
theorem B14646305 : Blo 1977435 14646305 := bstep (se 2 (by rfl) ⟨5492364, by rfl⟩ : syracuseStep 14646305 = 10984729) B10984729
theorem B39056813 : Blo 1977435 39056813 := bstep (se 3 (by rfl) ⟨7323152, by rfl⟩ : syracuseStep 39056813 = 14646305) B14646305
theorem B26037875 : Blo 1977435 26037875 := bstep (se 1 (by rfl) ⟨19528406, by rfl⟩ : syracuseStep 26037875 = 39056813) B39056813
theorem B17358583 : Blo 1977435 17358583 := bstep (se 1 (by rfl) ⟨13018937, by rfl⟩ : syracuseStep 17358583 = 26037875) B26037875
theorem B23144777 : Blo 1977435 23144777 := bstep (se 2 (by rfl) ⟨8679291, by rfl⟩ : syracuseStep 23144777 = 17358583) B17358583
theorem B15429851 : Blo 1977435 15429851 := bstep (se 1 (by rfl) ⟨11572388, by rfl⟩ : syracuseStep 15429851 = 23144777) B23144777
theorem B10286567 : Blo 1977435 10286567 := bstep (se 1 (by rfl) ⟨7714925, by rfl⟩ : syracuseStep 10286567 = 15429851) B15429851
theorem B6857711 : Blo 1977435 6857711 := bstep (se 1 (by rfl) ⟨5143283, by rfl⟩ : syracuseStep 6857711 = 10286567) B10286567
theorem B4571807 : Blo 1977435 4571807 := bstep (se 1 (by rfl) ⟨3428855, by rfl⟩ : syracuseStep 4571807 = 6857711) B6857711
theorem B12191485 : Blo 1977435 12191485 := bstep (se 3 (by rfl) ⟨2285903, by rfl⟩ : syracuseStep 12191485 = 4571807) B4571807
theorem B16255313 : Blo 1977435 16255313 := bstep (se 2 (by rfl) ⟨6095742, by rfl⟩ : syracuseStep 16255313 = 12191485) B12191485
theorem B10836875 : Blo 1977435 10836875 := bstep (se 1 (by rfl) ⟨8127656, by rfl⟩ : syracuseStep 10836875 = 16255313) B16255313
theorem B7224583 : Blo 1977435 7224583 := bstep (se 1 (by rfl) ⟨5418437, by rfl⟩ : syracuseStep 7224583 = 10836875) B10836875
theorem B9632777 : Blo 1977435 9632777 := bstep (se 2 (by rfl) ⟨3612291, by rfl⟩ : syracuseStep 9632777 = 7224583) B7224583
theorem B25687405 : Blo 1977435 25687405 := bstep (se 3 (by rfl) ⟨4816388, by rfl⟩ : syracuseStep 25687405 = 9632777) B9632777
theorem B34249873 : Blo 1977435 34249873 := bstep (se 2 (by rfl) ⟨12843702, by rfl⟩ : syracuseStep 34249873 = 25687405) B25687405
theorem B45666497 : Blo 1977435 45666497 := bstep (se 2 (by rfl) ⟨17124936, by rfl⟩ : syracuseStep 45666497 = 34249873) B34249873
theorem B30444331 : Blo 1977435 30444331 := bstep (se 1 (by rfl) ⟨22833248, by rfl⟩ : syracuseStep 30444331 = 45666497) B45666497
theorem B40592441 : Blo 1977435 40592441 := bstep (se 2 (by rfl) ⟨15222165, by rfl⟩ : syracuseStep 40592441 = 30444331) B30444331
theorem B27061627 : Blo 1977435 27061627 := bstep (se 1 (by rfl) ⟨20296220, by rfl⟩ : syracuseStep 27061627 = 40592441) B40592441
theorem B36082169 : Blo 1977435 36082169 := bstep (se 2 (by rfl) ⟨13530813, by rfl⟩ : syracuseStep 36082169 = 27061627) B27061627
theorem B24054779 : Blo 1977435 24054779 := bstep (se 1 (by rfl) ⟨18041084, by rfl⟩ : syracuseStep 24054779 = 36082169) B36082169
theorem B64146077 : Blo 1977435 64146077 := bstep (se 3 (by rfl) ⟨12027389, by rfl⟩ : syracuseStep 64146077 = 24054779) B24054779
theorem B42764051 : Blo 1977435 42764051 := bstep (se 1 (by rfl) ⟨32073038, by rfl⟩ : syracuseStep 42764051 = 64146077) B64146077
theorem B28509367 : Blo 1977435 28509367 := bstep (se 1 (by rfl) ⟨21382025, by rfl⟩ : syracuseStep 28509367 = 42764051) B42764051
theorem B38012489 : Blo 1977435 38012489 := bstep (se 2 (by rfl) ⟨14254683, by rfl⟩ : syracuseStep 38012489 = 28509367) B28509367
theorem B25341659 : Blo 1977435 25341659 := bstep (se 1 (by rfl) ⟨19006244, by rfl⟩ : syracuseStep 25341659 = 38012489) B38012489
theorem B16894439 : Blo 1977435 16894439 := bstep (se 1 (by rfl) ⟨12670829, by rfl⟩ : syracuseStep 16894439 = 25341659) B25341659
theorem B11262959 : Blo 1977435 11262959 := bstep (se 1 (by rfl) ⟨8447219, by rfl⟩ : syracuseStep 11262959 = 16894439) B16894439
theorem B7508639 : Blo 1977435 7508639 := bstep (se 1 (by rfl) ⟨5631479, by rfl⟩ : syracuseStep 7508639 = 11262959) B11262959
theorem B5005759 : Blo 1977435 5005759 := bstep (se 1 (by rfl) ⟨3754319, by rfl⟩ : syracuseStep 5005759 = 7508639) B7508639
theorem B6674345 : Blo 1977435 6674345 := bstep (se 2 (by rfl) ⟨2502879, by rfl⟩ : syracuseStep 6674345 = 5005759) B5005759
theorem B4449563 : Blo 1977435 4449563 := bstep (se 1 (by rfl) ⟨3337172, by rfl⟩ : syracuseStep 4449563 = 6674345) B6674345
theorem B2966375 : Blo 1977435 2966375 := bstep (se 1 (by rfl) ⟨2224781, by rfl⟩ : syracuseStep 2966375 = 4449563) B4449563
theorem B1977583 : Blo 1977435 1977583 := bstep (se 1 (by rfl) ⟨1483187, by rfl⟩ : syracuseStep 1977583 = 2966375) B2966375
theorem B2966381 : Blo 1977435 2966381 := bbase (se 3 (by rfl) ⟨556196, by rfl⟩ : syracuseStep 2966381 = 1112393) (by norm_num)
theorem B1977587 : Blo 1977435 1977587 := bstep (se 1 (by rfl) ⟨1483190, by rfl⟩ : syracuseStep 1977587 = 2966381) B2966381
theorem B4449581 : Blo 1977435 4449581 := bbase (se 3 (by rfl) ⟨834296, by rfl⟩ : syracuseStep 4449581 = 1668593) (by norm_num)
theorem B2966387 : Blo 1977435 2966387 := bstep (se 1 (by rfl) ⟨2224790, by rfl⟩ : syracuseStep 2966387 = 4449581) B4449581
theorem B1977591 : Blo 1977435 1977591 := bstep (se 1 (by rfl) ⟨1483193, by rfl⟩ : syracuseStep 1977591 = 2966387) B2966387
theorem B13530901 : Blo 1977435 13530901 := bbase (se 6 (by rfl) ⟨317130, by rfl⟩ : syracuseStep 13530901 = 634261) (by norm_num)
theorem B18041201 : Blo 1977435 18041201 := bstep (se 2 (by rfl) ⟨6765450, by rfl⟩ : syracuseStep 18041201 = 13530901) B13530901
theorem B12027467 : Blo 1977435 12027467 := bstep (se 1 (by rfl) ⟨9020600, by rfl⟩ : syracuseStep 12027467 = 18041201) B18041201
theorem B32073245 : Blo 1977435 32073245 := bstep (se 3 (by rfl) ⟨6013733, by rfl⟩ : syracuseStep 32073245 = 12027467) B12027467
theorem B21382163 : Blo 1977435 21382163 := bstep (se 1 (by rfl) ⟨16036622, by rfl⟩ : syracuseStep 21382163 = 32073245) B32073245
theorem B14254775 : Blo 1977435 14254775 := bstep (se 1 (by rfl) ⟨10691081, by rfl⟩ : syracuseStep 14254775 = 21382163) B21382163
theorem B9503183 : Blo 1977435 9503183 := bstep (se 1 (by rfl) ⟨7127387, by rfl⟩ : syracuseStep 9503183 = 14254775) B14254775
theorem B6335455 : Blo 1977435 6335455 := bstep (se 1 (by rfl) ⟨4751591, by rfl⟩ : syracuseStep 6335455 = 9503183) B9503183
theorem B8447273 : Blo 1977435 8447273 := bstep (se 2 (by rfl) ⟨3167727, by rfl⟩ : syracuseStep 8447273 = 6335455) B6335455
theorem B5631515 : Blo 1977435 5631515 := bstep (se 1 (by rfl) ⟨4223636, by rfl⟩ : syracuseStep 5631515 = 8447273) B8447273
theorem B3754343 : Blo 1977435 3754343 := bstep (se 1 (by rfl) ⟨2815757, by rfl⟩ : syracuseStep 3754343 = 5631515) B5631515
theorem B2502895 : Blo 1977435 2502895 := bstep (se 1 (by rfl) ⟨1877171, by rfl⟩ : syracuseStep 2502895 = 3754343) B3754343
theorem B3337193 : Blo 1977435 3337193 := bstep (se 2 (by rfl) ⟨1251447, by rfl⟩ : syracuseStep 3337193 = 2502895) B2502895
theorem B2224795 : Blo 1977435 2224795 := bstep (se 1 (by rfl) ⟨1668596, by rfl⟩ : syracuseStep 2224795 = 3337193) B3337193
theorem B2966393 : Blo 1977435 2966393 := bstep (se 2 (by rfl) ⟨1112397, by rfl⟩ : syracuseStep 2966393 = 2224795) B2224795
theorem B1977595 : Blo 1977435 1977595 := bstep (se 1 (by rfl) ⟨1483196, by rfl⟩ : syracuseStep 1977595 = 2966393) B2966393
theorem B4281269 : Blo 1977435 4281269 := bbase (se 5 (by rfl) ⟨200684, by rfl⟩ : syracuseStep 4281269 = 401369) (by norm_num)
theorem B11416717 : Blo 1977435 11416717 := bstep (se 3 (by rfl) ⟨2140634, by rfl⟩ : syracuseStep 11416717 = 4281269) B4281269
theorem B60889157 : Blo 1977435 60889157 := bstep (se 4 (by rfl) ⟨5708358, by rfl⟩ : syracuseStep 60889157 = 11416717) B11416717
theorem B40592771 : Blo 1977435 40592771 := bstep (se 1 (by rfl) ⟨30444578, by rfl⟩ : syracuseStep 40592771 = 60889157) B60889157
theorem B27061847 : Blo 1977435 27061847 := bstep (se 1 (by rfl) ⟨20296385, by rfl⟩ : syracuseStep 27061847 = 40592771) B40592771
theorem B18041231 : Blo 1977435 18041231 := bstep (se 1 (by rfl) ⟨13530923, by rfl⟩ : syracuseStep 18041231 = 27061847) B27061847
theorem B12027487 : Blo 1977435 12027487 := bstep (se 1 (by rfl) ⟨9020615, by rfl⟩ : syracuseStep 12027487 = 18041231) B18041231
theorem B16036649 : Blo 1977435 16036649 := bstep (se 2 (by rfl) ⟨6013743, by rfl⟩ : syracuseStep 16036649 = 12027487) B12027487
theorem B10691099 : Blo 1977435 10691099 := bstep (se 1 (by rfl) ⟨8018324, by rfl⟩ : syracuseStep 10691099 = 16036649) B16036649
theorem B7127399 : Blo 1977435 7127399 := bstep (se 1 (by rfl) ⟨5345549, by rfl⟩ : syracuseStep 7127399 = 10691099) B10691099
theorem B19006397 : Blo 1977435 19006397 := bstep (se 3 (by rfl) ⟨3563699, by rfl⟩ : syracuseStep 19006397 = 7127399) B7127399
theorem B12670931 : Blo 1977435 12670931 := bstep (se 1 (by rfl) ⟨9503198, by rfl⟩ : syracuseStep 12670931 = 19006397) B19006397
theorem B33789149 : Blo 1977435 33789149 := bstep (se 3 (by rfl) ⟨6335465, by rfl⟩ : syracuseStep 33789149 = 12670931) B12670931
theorem B22526099 : Blo 1977435 22526099 := bstep (se 1 (by rfl) ⟨16894574, by rfl⟩ : syracuseStep 22526099 = 33789149) B33789149
theorem B15017399 : Blo 1977435 15017399 := bstep (se 1 (by rfl) ⟨11263049, by rfl⟩ : syracuseStep 15017399 = 22526099) B22526099
theorem B10011599 : Blo 1977435 10011599 := bstep (se 1 (by rfl) ⟨7508699, by rfl⟩ : syracuseStep 10011599 = 15017399) B15017399
theorem B6674399 : Blo 1977435 6674399 := bstep (se 1 (by rfl) ⟨5005799, by rfl⟩ : syracuseStep 6674399 = 10011599) B10011599
theorem B4449599 : Blo 1977435 4449599 := bstep (se 1 (by rfl) ⟨3337199, by rfl⟩ : syracuseStep 4449599 = 6674399) B6674399
theorem B2966399 : Blo 1977435 2966399 := bstep (se 1 (by rfl) ⟨2224799, by rfl⟩ : syracuseStep 2966399 = 4449599) B4449599
theorem B1977599 : Blo 1977435 1977599 := bstep (se 1 (by rfl) ⟨1483199, by rfl⟩ : syracuseStep 1977599 = 2966399) B2966399
theorem B2966405 : Blo 1977435 2966405 := bbase (se 4 (by rfl) ⟨278100, by rfl⟩ : syracuseStep 2966405 = 556201) (by norm_num)
theorem B1977603 : Blo 1977435 1977603 := bstep (se 1 (by rfl) ⟨1483202, by rfl⟩ : syracuseStep 1977603 = 2966405) B2966405
theorem B3337213 : Blo 1977435 3337213 := bbase (se 3 (by rfl) ⟨625727, by rfl⟩ : syracuseStep 3337213 = 1251455) (by norm_num)
theorem B4449617 : Blo 1977435 4449617 := bstep (se 2 (by rfl) ⟨1668606, by rfl⟩ : syracuseStep 4449617 = 3337213) B3337213
theorem B2966411 : Blo 1977435 2966411 := bstep (se 1 (by rfl) ⟨2224808, by rfl⟩ : syracuseStep 2966411 = 4449617) B4449617
theorem B1977607 : Blo 1977435 1977607 := bstep (se 1 (by rfl) ⟨1483205, by rfl⟩ : syracuseStep 1977607 = 2966411) B2966411
theorem B2224813 : Blo 1977435 2224813 := bbase (se 3 (by rfl) ⟨417152, by rfl⟩ : syracuseStep 2224813 = 834305) (by norm_num)
theorem B2966417 : Blo 1977435 2966417 := bstep (se 2 (by rfl) ⟨1112406, by rfl⟩ : syracuseStep 2966417 = 2224813) B2224813
theorem B1977611 : Blo 1977435 1977611 := bstep (se 1 (by rfl) ⟨1483208, by rfl⟩ : syracuseStep 1977611 = 2966417) B2966417
theorem B6674453 : Blo 1977435 6674453 := bbase (se 6 (by rfl) ⟨156432, by rfl⟩ : syracuseStep 6674453 = 312865) (by norm_num)
theorem B4449635 : Blo 1977435 4449635 := bstep (se 1 (by rfl) ⟨3337226, by rfl⟩ : syracuseStep 4449635 = 6674453) B6674453
theorem B2966423 : Blo 1977435 2966423 := bstep (se 1 (by rfl) ⟨2224817, by rfl⟩ : syracuseStep 2966423 = 4449635) B4449635
theorem B1977615 : Blo 1977435 1977615 := bstep (se 1 (by rfl) ⟨1483211, by rfl⟩ : syracuseStep 1977615 = 2966423) B2966423
theorem B2966429 : Blo 1977435 2966429 := bbase (se 3 (by rfl) ⟨556205, by rfl⟩ : syracuseStep 2966429 = 1112411) (by norm_num)
theorem B1977619 : Blo 1977435 1977619 := bstep (se 1 (by rfl) ⟨1483214, by rfl⟩ : syracuseStep 1977619 = 2966429) B2966429
theorem B4449653 : Blo 1977435 4449653 := bbase (se 5 (by rfl) ⟨208577, by rfl⟩ : syracuseStep 4449653 = 417155) (by norm_num)
theorem B2966435 : Blo 1977435 2966435 := bstep (se 1 (by rfl) ⟨2224826, by rfl⟩ : syracuseStep 2966435 = 4449653) B4449653
theorem B1977623 : Blo 1977435 1977623 := bstep (se 1 (by rfl) ⟨1483217, by rfl⟩ : syracuseStep 1977623 = 2966435) B2966435
theorem B2408249 : Blo 1977435 2408249 := bbase (se 2 (by rfl) ⟨903093, by rfl⟩ : syracuseStep 2408249 = 1806187) (by norm_num)
theorem B6421997 : Blo 1977435 6421997 := bstep (se 3 (by rfl) ⟨1204124, by rfl⟩ : syracuseStep 6421997 = 2408249) B2408249
theorem B4281331 : Blo 1977435 4281331 := bstep (se 1 (by rfl) ⟨3210998, by rfl⟩ : syracuseStep 4281331 = 6421997) B6421997
theorem B5708441 : Blo 1977435 5708441 := bstep (se 2 (by rfl) ⟨2140665, by rfl⟩ : syracuseStep 5708441 = 4281331) B4281331
theorem B3805627 : Blo 1977435 3805627 := bstep (se 1 (by rfl) ⟨2854220, by rfl⟩ : syracuseStep 3805627 = 5708441) B5708441
theorem B5074169 : Blo 1977435 5074169 := bstep (se 2 (by rfl) ⟨1902813, by rfl⟩ : syracuseStep 5074169 = 3805627) B3805627
theorem B54124469 : Blo 1977435 54124469 := bstep (se 5 (by rfl) ⟨2537084, by rfl⟩ : syracuseStep 54124469 = 5074169) B5074169
theorem B36082979 : Blo 1977435 36082979 := bstep (se 1 (by rfl) ⟨27062234, by rfl⟩ : syracuseStep 36082979 = 54124469) B54124469
theorem B24055319 : Blo 1977435 24055319 := bstep (se 1 (by rfl) ⟨18041489, by rfl⟩ : syracuseStep 24055319 = 36082979) B36082979
theorem B16036879 : Blo 1977435 16036879 := bstep (se 1 (by rfl) ⟨12027659, by rfl⟩ : syracuseStep 16036879 = 24055319) B24055319
theorem B21382505 : Blo 1977435 21382505 := bstep (se 2 (by rfl) ⟨8018439, by rfl⟩ : syracuseStep 21382505 = 16036879) B16036879
theorem B14255003 : Blo 1977435 14255003 := bstep (se 1 (by rfl) ⟨10691252, by rfl⟩ : syracuseStep 14255003 = 21382505) B21382505
theorem B9503335 : Blo 1977435 9503335 := bstep (se 1 (by rfl) ⟨7127501, by rfl⟩ : syracuseStep 9503335 = 14255003) B14255003
theorem B12671113 : Blo 1977435 12671113 := bstep (se 2 (by rfl) ⟨4751667, by rfl⟩ : syracuseStep 12671113 = 9503335) B9503335
theorem B16894817 : Blo 1977435 16894817 := bstep (se 2 (by rfl) ⟨6335556, by rfl⟩ : syracuseStep 16894817 = 12671113) B12671113
theorem B11263211 : Blo 1977435 11263211 := bstep (se 1 (by rfl) ⟨8447408, by rfl⟩ : syracuseStep 11263211 = 16894817) B16894817
theorem B7508807 : Blo 1977435 7508807 := bstep (se 1 (by rfl) ⟨5631605, by rfl⟩ : syracuseStep 7508807 = 11263211) B11263211
theorem B5005871 : Blo 1977435 5005871 := bstep (se 1 (by rfl) ⟨3754403, by rfl⟩ : syracuseStep 5005871 = 7508807) B7508807
theorem B3337247 : Blo 1977435 3337247 := bstep (se 1 (by rfl) ⟨2502935, by rfl⟩ : syracuseStep 3337247 = 5005871) B5005871
theorem B2224831 : Blo 1977435 2224831 := bstep (se 1 (by rfl) ⟨1668623, by rfl⟩ : syracuseStep 2224831 = 3337247) B3337247
theorem B2966441 : Blo 1977435 2966441 := bstep (se 2 (by rfl) ⟨1112415, by rfl⟩ : syracuseStep 2966441 = 2224831) B2224831
theorem B1977627 : Blo 1977435 1977627 := bstep (se 1 (by rfl) ⟨1483220, by rfl⟩ : syracuseStep 1977627 = 2966441) B2966441
theorem B7508821 : Blo 1977435 7508821 := bbase (se 9 (by rfl) ⟨21998, by rfl⟩ : syracuseStep 7508821 = 43997) (by norm_num)
theorem B10011761 : Blo 1977435 10011761 := bstep (se 2 (by rfl) ⟨3754410, by rfl⟩ : syracuseStep 10011761 = 7508821) B7508821
theorem B6674507 : Blo 1977435 6674507 := bstep (se 1 (by rfl) ⟨5005880, by rfl⟩ : syracuseStep 6674507 = 10011761) B10011761
theorem B4449671 : Blo 1977435 4449671 := bstep (se 1 (by rfl) ⟨3337253, by rfl⟩ : syracuseStep 4449671 = 6674507) B6674507
theorem B2966447 : Blo 1977435 2966447 := bstep (se 1 (by rfl) ⟨2224835, by rfl⟩ : syracuseStep 2966447 = 4449671) B4449671
theorem B1977631 : Blo 1977435 1977631 := bstep (se 1 (by rfl) ⟨1483223, by rfl⟩ : syracuseStep 1977631 = 2966447) B2966447
theorem B2966453 : Blo 1977435 2966453 := bbase (se 5 (by rfl) ⟨139052, by rfl⟩ : syracuseStep 2966453 = 278105) (by norm_num)
theorem B1977635 : Blo 1977435 1977635 := bstep (se 1 (by rfl) ⟨1483226, by rfl⟩ : syracuseStep 1977635 = 2966453) B2966453
theorem B5005901 : Blo 1977435 5005901 := bbase (se 3 (by rfl) ⟨938606, by rfl⟩ : syracuseStep 5005901 = 1877213) (by norm_num)
theorem B3337267 : Blo 1977435 3337267 := bstep (se 1 (by rfl) ⟨2502950, by rfl⟩ : syracuseStep 3337267 = 5005901) B5005901
theorem B4449689 : Blo 1977435 4449689 := bstep (se 2 (by rfl) ⟨1668633, by rfl⟩ : syracuseStep 4449689 = 3337267) B3337267
theorem B2966459 : Blo 1977435 2966459 := bstep (se 1 (by rfl) ⟨2224844, by rfl⟩ : syracuseStep 2966459 = 4449689) B4449689
theorem B1977639 : Blo 1977435 1977639 := bstep (se 1 (by rfl) ⟨1483229, by rfl⟩ : syracuseStep 1977639 = 2966459) B2966459
theorem B2224849 : Blo 1977435 2224849 := bbase (se 2 (by rfl) ⟨834318, by rfl⟩ : syracuseStep 2224849 = 1668637) (by norm_num)
theorem B2966465 : Blo 1977435 2966465 := bstep (se 2 (by rfl) ⟨1112424, by rfl⟩ : syracuseStep 2966465 = 2224849) B2224849
theorem B1977643 : Blo 1977435 1977643 := bstep (se 1 (by rfl) ⟨1483232, by rfl⟩ : syracuseStep 1977643 = 2966465) B2966465
theorem B6335621 : Blo 1977435 6335621 := bbase (se 4 (by rfl) ⟨593964, by rfl⟩ : syracuseStep 6335621 = 1187929) (by norm_num)
theorem B4223747 : Blo 1977435 4223747 := bstep (se 1 (by rfl) ⟨3167810, by rfl⟩ : syracuseStep 4223747 = 6335621) B6335621
theorem B2815831 : Blo 1977435 2815831 := bstep (se 1 (by rfl) ⟨2111873, by rfl⟩ : syracuseStep 2815831 = 4223747) B4223747
theorem B3754441 : Blo 1977435 3754441 := bstep (se 2 (by rfl) ⟨1407915, by rfl⟩ : syracuseStep 3754441 = 2815831) B2815831
theorem B5005921 : Blo 1977435 5005921 := bstep (se 2 (by rfl) ⟨1877220, by rfl⟩ : syracuseStep 5005921 = 3754441) B3754441
theorem B6674561 : Blo 1977435 6674561 := bstep (se 2 (by rfl) ⟨2502960, by rfl⟩ : syracuseStep 6674561 = 5005921) B5005921
theorem B4449707 : Blo 1977435 4449707 := bstep (se 1 (by rfl) ⟨3337280, by rfl⟩ : syracuseStep 4449707 = 6674561) B6674561
theorem B2966471 : Blo 1977435 2966471 := bstep (se 1 (by rfl) ⟨2224853, by rfl⟩ : syracuseStep 2966471 = 4449707) B4449707
theorem B1977647 : Blo 1977435 1977647 := bstep (se 1 (by rfl) ⟨1483235, by rfl⟩ : syracuseStep 1977647 = 2966471) B2966471
theorem B2966477 : Blo 1977435 2966477 := bbase (se 3 (by rfl) ⟨556214, by rfl⟩ : syracuseStep 2966477 = 1112429) (by norm_num)
theorem B1977651 : Blo 1977435 1977651 := bstep (se 1 (by rfl) ⟨1483238, by rfl⟩ : syracuseStep 1977651 = 2966477) B2966477
theorem B4449725 : Blo 1977435 4449725 := bbase (se 3 (by rfl) ⟨834323, by rfl⟩ : syracuseStep 4449725 = 1668647) (by norm_num)
theorem B2966483 : Blo 1977435 2966483 := bstep (se 1 (by rfl) ⟨2224862, by rfl⟩ : syracuseStep 2966483 = 4449725) B4449725
theorem B1977655 : Blo 1977435 1977655 := bstep (se 1 (by rfl) ⟨1483241, by rfl⟩ : syracuseStep 1977655 = 2966483) B2966483
theorem B3337301 : Blo 1977435 3337301 := bbase (se 8 (by rfl) ⟨19554, by rfl⟩ : syracuseStep 3337301 = 39109) (by norm_num)
theorem B2224867 : Blo 1977435 2224867 := bstep (se 1 (by rfl) ⟨1668650, by rfl⟩ : syracuseStep 2224867 = 3337301) B3337301
theorem B2966489 : Blo 1977435 2966489 := bstep (se 2 (by rfl) ⟨1112433, by rfl⟩ : syracuseStep 2966489 = 2224867) B2224867
theorem B1977659 : Blo 1977435 1977659 := bstep (se 1 (by rfl) ⟨1483244, by rfl⟩ : syracuseStep 1977659 = 2966489) B2966489
theorem B2140705 : Blo 1977435 2140705 := bbase (se 2 (by rfl) ⟨802764, by rfl⟩ : syracuseStep 2140705 = 1605529) (by norm_num)
theorem B2854273 : Blo 1977435 2854273 := bstep (se 2 (by rfl) ⟨1070352, by rfl⟩ : syracuseStep 2854273 = 2140705) B2140705
theorem B3805697 : Blo 1977435 3805697 := bstep (se 2 (by rfl) ⟨1427136, by rfl⟩ : syracuseStep 3805697 = 2854273) B2854273
theorem B2537131 : Blo 1977435 2537131 := bstep (se 1 (by rfl) ⟨1902848, by rfl⟩ : syracuseStep 2537131 = 3805697) B3805697
theorem B3382841 : Blo 1977435 3382841 := bstep (se 2 (by rfl) ⟨1268565, by rfl⟩ : syracuseStep 3382841 = 2537131) B2537131
theorem B9020909 : Blo 1977435 9020909 := bstep (se 3 (by rfl) ⟨1691420, by rfl⟩ : syracuseStep 9020909 = 3382841) B3382841
theorem B6013939 : Blo 1977435 6013939 := bstep (se 1 (by rfl) ⟨4510454, by rfl⟩ : syracuseStep 6013939 = 9020909) B9020909
theorem B8018585 : Blo 1977435 8018585 := bstep (se 2 (by rfl) ⟨3006969, by rfl⟩ : syracuseStep 8018585 = 6013939) B6013939
theorem B5345723 : Blo 1977435 5345723 := bstep (se 1 (by rfl) ⟨4009292, by rfl⟩ : syracuseStep 5345723 = 8018585) B8018585
theorem B14255261 : Blo 1977435 14255261 := bstep (se 3 (by rfl) ⟨2672861, by rfl⟩ : syracuseStep 14255261 = 5345723) B5345723
theorem B9503507 : Blo 1977435 9503507 := bstep (se 1 (by rfl) ⟨7127630, by rfl⟩ : syracuseStep 9503507 = 14255261) B14255261
theorem B6335671 : Blo 1977435 6335671 := bstep (se 1 (by rfl) ⟨4751753, by rfl⟩ : syracuseStep 6335671 = 9503507) B9503507
theorem B8447561 : Blo 1977435 8447561 := bstep (se 2 (by rfl) ⟨3167835, by rfl⟩ : syracuseStep 8447561 = 6335671) B6335671
theorem B5631707 : Blo 1977435 5631707 := bstep (se 1 (by rfl) ⟨4223780, by rfl⟩ : syracuseStep 5631707 = 8447561) B8447561
theorem B15017885 : Blo 1977435 15017885 := bstep (se 3 (by rfl) ⟨2815853, by rfl⟩ : syracuseStep 15017885 = 5631707) B5631707
theorem B10011923 : Blo 1977435 10011923 := bstep (se 1 (by rfl) ⟨7508942, by rfl⟩ : syracuseStep 10011923 = 15017885) B15017885
theorem B6674615 : Blo 1977435 6674615 := bstep (se 1 (by rfl) ⟨5005961, by rfl⟩ : syracuseStep 6674615 = 10011923) B10011923
theorem B4449743 : Blo 1977435 4449743 := bstep (se 1 (by rfl) ⟨3337307, by rfl⟩ : syracuseStep 4449743 = 6674615) B6674615
theorem B2966495 : Blo 1977435 2966495 := bstep (se 1 (by rfl) ⟨2224871, by rfl⟩ : syracuseStep 2966495 = 4449743) B4449743
theorem B1977663 : Blo 1977435 1977663 := bstep (se 1 (by rfl) ⟨1483247, by rfl⟩ : syracuseStep 1977663 = 2966495) B2966495
theorem B2966501 : Blo 1977435 2966501 := bbase (se 4 (by rfl) ⟨278109, by rfl⟩ : syracuseStep 2966501 = 556219) (by norm_num)
theorem B1977667 : Blo 1977435 1977667 := bstep (se 1 (by rfl) ⟨1483250, by rfl⟩ : syracuseStep 1977667 = 2966501) B2966501
theorem B5074285 : Blo 1977435 5074285 := bbase (se 3 (by rfl) ⟨951428, by rfl⟩ : syracuseStep 5074285 = 1902857) (by norm_num)
theorem B6765713 : Blo 1977435 6765713 := bstep (se 2 (by rfl) ⟨2537142, by rfl⟩ : syracuseStep 6765713 = 5074285) B5074285
theorem B4510475 : Blo 1977435 4510475 := bstep (se 1 (by rfl) ⟨3382856, by rfl⟩ : syracuseStep 4510475 = 6765713) B6765713
theorem B3006983 : Blo 1977435 3006983 := bstep (se 1 (by rfl) ⟨2255237, by rfl⟩ : syracuseStep 3006983 = 4510475) B4510475
theorem B8018621 : Blo 1977435 8018621 := bstep (se 3 (by rfl) ⟨1503491, by rfl⟩ : syracuseStep 8018621 = 3006983) B3006983
theorem B5345747 : Blo 1977435 5345747 := bstep (se 1 (by rfl) ⟨4009310, by rfl⟩ : syracuseStep 5345747 = 8018621) B8018621
theorem B3563831 : Blo 1977435 3563831 := bstep (se 1 (by rfl) ⟨2672873, by rfl⟩ : syracuseStep 3563831 = 5345747) B5345747
theorem B2375887 : Blo 1977435 2375887 := bstep (se 1 (by rfl) ⟨1781915, by rfl⟩ : syracuseStep 2375887 = 3563831) B3563831
theorem B3167849 : Blo 1977435 3167849 := bstep (se 2 (by rfl) ⟨1187943, by rfl⟩ : syracuseStep 3167849 = 2375887) B2375887
theorem B8447597 : Blo 1977435 8447597 := bstep (se 3 (by rfl) ⟨1583924, by rfl⟩ : syracuseStep 8447597 = 3167849) B3167849
theorem B5631731 : Blo 1977435 5631731 := bstep (se 1 (by rfl) ⟨4223798, by rfl⟩ : syracuseStep 5631731 = 8447597) B8447597
theorem B3754487 : Blo 1977435 3754487 := bstep (se 1 (by rfl) ⟨2815865, by rfl⟩ : syracuseStep 3754487 = 5631731) B5631731
theorem B2502991 : Blo 1977435 2502991 := bstep (se 1 (by rfl) ⟨1877243, by rfl⟩ : syracuseStep 2502991 = 3754487) B3754487
theorem B3337321 : Blo 1977435 3337321 := bstep (se 2 (by rfl) ⟨1251495, by rfl⟩ : syracuseStep 3337321 = 2502991) B2502991
theorem B4449761 : Blo 1977435 4449761 := bstep (se 2 (by rfl) ⟨1668660, by rfl⟩ : syracuseStep 4449761 = 3337321) B3337321
theorem B2966507 : Blo 1977435 2966507 := bstep (se 1 (by rfl) ⟨2224880, by rfl⟩ : syracuseStep 2966507 = 4449761) B4449761
theorem B1977671 : Blo 1977435 1977671 := bstep (se 1 (by rfl) ⟨1483253, by rfl⟩ : syracuseStep 1977671 = 2966507) B2966507
theorem B2224885 : Blo 1977435 2224885 := bbase (se 5 (by rfl) ⟨104291, by rfl⟩ : syracuseStep 2224885 = 208583) (by norm_num)
theorem B2966513 : Blo 1977435 2966513 := bstep (se 2 (by rfl) ⟨1112442, by rfl⟩ : syracuseStep 2966513 = 2224885) B2224885
theorem B1977675 : Blo 1977435 1977675 := bstep (se 1 (by rfl) ⟨1483256, by rfl⟩ : syracuseStep 1977675 = 2966513) B2966513
theorem B2503001 : Blo 1977435 2503001 := bbase (se 2 (by rfl) ⟨938625, by rfl⟩ : syracuseStep 2503001 = 1877251) (by norm_num)
theorem B6674669 : Blo 1977435 6674669 := bstep (se 3 (by rfl) ⟨1251500, by rfl⟩ : syracuseStep 6674669 = 2503001) B2503001
theorem B4449779 : Blo 1977435 4449779 := bstep (se 1 (by rfl) ⟨3337334, by rfl⟩ : syracuseStep 4449779 = 6674669) B6674669
theorem B2966519 : Blo 1977435 2966519 := bstep (se 1 (by rfl) ⟨2224889, by rfl⟩ : syracuseStep 2966519 = 4449779) B4449779
theorem B1977679 : Blo 1977435 1977679 := bstep (se 1 (by rfl) ⟨1483259, by rfl⟩ : syracuseStep 1977679 = 2966519) B2966519
theorem B2966525 : Blo 1977435 2966525 := bbase (se 3 (by rfl) ⟨556223, by rfl⟩ : syracuseStep 2966525 = 1112447) (by norm_num)
theorem B1977683 : Blo 1977435 1977683 := bstep (se 1 (by rfl) ⟨1483262, by rfl⟩ : syracuseStep 1977683 = 2966525) B2966525
theorem B4449797 : Blo 1977435 4449797 := bbase (se 4 (by rfl) ⟨417168, by rfl⟩ : syracuseStep 4449797 = 834337) (by norm_num)
theorem B2966531 : Blo 1977435 2966531 := bstep (se 1 (by rfl) ⟨2224898, by rfl⟩ : syracuseStep 2966531 = 4449797) B4449797
theorem B1977687 : Blo 1977435 1977687 := bstep (se 1 (by rfl) ⟨1483265, by rfl⟩ : syracuseStep 1977687 = 2966531) B2966531
theorem B3754525 : Blo 1977435 3754525 := bbase (se 3 (by rfl) ⟨703973, by rfl⟩ : syracuseStep 3754525 = 1407947) (by norm_num)
theorem B5006033 : Blo 1977435 5006033 := bstep (se 2 (by rfl) ⟨1877262, by rfl⟩ : syracuseStep 5006033 = 3754525) B3754525
theorem B3337355 : Blo 1977435 3337355 := bstep (se 1 (by rfl) ⟨2503016, by rfl⟩ : syracuseStep 3337355 = 5006033) B5006033
theorem B2224903 : Blo 1977435 2224903 := bstep (se 1 (by rfl) ⟨1668677, by rfl⟩ : syracuseStep 2224903 = 3337355) B3337355
theorem B2966537 : Blo 1977435 2966537 := bstep (se 2 (by rfl) ⟨1112451, by rfl⟩ : syracuseStep 2966537 = 2224903) B2224903
theorem B1977691 : Blo 1977435 1977691 := bstep (se 1 (by rfl) ⟨1483268, by rfl⟩ : syracuseStep 1977691 = 2966537) B2966537
theorem B10012085 : Blo 1977435 10012085 := bbase (se 5 (by rfl) ⟨469316, by rfl⟩ : syracuseStep 10012085 = 938633) (by norm_num)
theorem B6674723 : Blo 1977435 6674723 := bstep (se 1 (by rfl) ⟨5006042, by rfl⟩ : syracuseStep 6674723 = 10012085) B10012085
theorem B4449815 : Blo 1977435 4449815 := bstep (se 1 (by rfl) ⟨3337361, by rfl⟩ : syracuseStep 4449815 = 6674723) B6674723
theorem B2966543 : Blo 1977435 2966543 := bstep (se 1 (by rfl) ⟨2224907, by rfl⟩ : syracuseStep 2966543 = 4449815) B4449815
theorem B1977695 : Blo 1977435 1977695 := bstep (se 1 (by rfl) ⟨1483271, by rfl⟩ : syracuseStep 1977695 = 2966543) B2966543
theorem B2966549 : Blo 1977435 2966549 := bbase (se 6 (by rfl) ⟨69528, by rfl⟩ : syracuseStep 2966549 = 139057) (by norm_num)
theorem B1977699 : Blo 1977435 1977699 := bstep (se 1 (by rfl) ⟨1483274, by rfl⟩ : syracuseStep 1977699 = 2966549) B2966549
theorem B18288341 : Blo 1977435 18288341 := bbase (se 7 (by rfl) ⟨214316, by rfl⟩ : syracuseStep 18288341 = 428633) (by norm_num)
theorem B12192227 : Blo 1977435 12192227 := bstep (se 1 (by rfl) ⟨9144170, by rfl⟩ : syracuseStep 12192227 = 18288341) B18288341
theorem B8128151 : Blo 1977435 8128151 := bstep (se 1 (by rfl) ⟨6096113, by rfl⟩ : syracuseStep 8128151 = 12192227) B12192227
theorem B5418767 : Blo 1977435 5418767 := bstep (se 1 (by rfl) ⟨4064075, by rfl⟩ : syracuseStep 5418767 = 8128151) B8128151
theorem B3612511 : Blo 1977435 3612511 := bstep (se 1 (by rfl) ⟨2709383, by rfl⟩ : syracuseStep 3612511 = 5418767) B5418767
theorem B4816681 : Blo 1977435 4816681 := bstep (se 2 (by rfl) ⟨1806255, by rfl⟩ : syracuseStep 4816681 = 3612511) B3612511
theorem B102755861 : Blo 1977435 102755861 := bstep (se 6 (by rfl) ⟨2408340, by rfl⟩ : syracuseStep 102755861 = 4816681) B4816681
theorem B68503907 : Blo 1977435 68503907 := bstep (se 1 (by rfl) ⟨51377930, by rfl⟩ : syracuseStep 68503907 = 102755861) B102755861
theorem B45669271 : Blo 1977435 45669271 := bstep (se 1 (by rfl) ⟨34251953, by rfl⟩ : syracuseStep 45669271 = 68503907) B68503907
theorem B60892361 : Blo 1977435 60892361 := bstep (se 2 (by rfl) ⟨22834635, by rfl⟩ : syracuseStep 60892361 = 45669271) B45669271
theorem B40594907 : Blo 1977435 40594907 := bstep (se 1 (by rfl) ⟨30446180, by rfl⟩ : syracuseStep 40594907 = 60892361) B60892361
theorem B27063271 : Blo 1977435 27063271 := bstep (se 1 (by rfl) ⟨20297453, by rfl⟩ : syracuseStep 27063271 = 40594907) B40594907
theorem B36084361 : Blo 1977435 36084361 := bstep (se 2 (by rfl) ⟨13531635, by rfl⟩ : syracuseStep 36084361 = 27063271) B27063271
theorem B48112481 : Blo 1977435 48112481 := bstep (se 2 (by rfl) ⟨18042180, by rfl⟩ : syracuseStep 48112481 = 36084361) B36084361
theorem B32074987 : Blo 1977435 32074987 := bstep (se 1 (by rfl) ⟨24056240, by rfl⟩ : syracuseStep 32074987 = 48112481) B48112481
theorem B42766649 : Blo 1977435 42766649 := bstep (se 2 (by rfl) ⟨16037493, by rfl⟩ : syracuseStep 42766649 = 32074987) B32074987
theorem B28511099 : Blo 1977435 28511099 := bstep (se 1 (by rfl) ⟨21383324, by rfl⟩ : syracuseStep 28511099 = 42766649) B42766649
theorem B19007399 : Blo 1977435 19007399 := bstep (se 1 (by rfl) ⟨14255549, by rfl⟩ : syracuseStep 19007399 = 28511099) B28511099
theorem B12671599 : Blo 1977435 12671599 := bstep (se 1 (by rfl) ⟨9503699, by rfl⟩ : syracuseStep 12671599 = 19007399) B19007399
theorem B16895465 : Blo 1977435 16895465 := bstep (se 2 (by rfl) ⟨6335799, by rfl⟩ : syracuseStep 16895465 = 12671599) B12671599
theorem B11263643 : Blo 1977435 11263643 := bstep (se 1 (by rfl) ⟨8447732, by rfl⟩ : syracuseStep 11263643 = 16895465) B16895465
theorem B7509095 : Blo 1977435 7509095 := bstep (se 1 (by rfl) ⟨5631821, by rfl⟩ : syracuseStep 7509095 = 11263643) B11263643
theorem B5006063 : Blo 1977435 5006063 := bstep (se 1 (by rfl) ⟨3754547, by rfl⟩ : syracuseStep 5006063 = 7509095) B7509095
theorem B3337375 : Blo 1977435 3337375 := bstep (se 1 (by rfl) ⟨2503031, by rfl⟩ : syracuseStep 3337375 = 5006063) B5006063
theorem B4449833 : Blo 1977435 4449833 := bstep (se 2 (by rfl) ⟨1668687, by rfl⟩ : syracuseStep 4449833 = 3337375) B3337375
theorem B2966555 : Blo 1977435 2966555 := bstep (se 1 (by rfl) ⟨2224916, by rfl⟩ : syracuseStep 2966555 = 4449833) B4449833
theorem B1977703 : Blo 1977435 1977703 := bstep (se 1 (by rfl) ⟨1483277, by rfl⟩ : syracuseStep 1977703 = 2966555) B2966555
theorem B2224921 : Blo 1977435 2224921 := bbase (se 2 (by rfl) ⟨834345, by rfl⟩ : syracuseStep 2224921 = 1668691) (by norm_num)
theorem B2966561 : Blo 1977435 2966561 := bstep (se 2 (by rfl) ⟨1112460, by rfl⟩ : syracuseStep 2966561 = 2224921) B2224921
theorem B1977707 : Blo 1977435 1977707 := bstep (se 1 (by rfl) ⟨1483280, by rfl⟩ : syracuseStep 1977707 = 2966561) B2966561
theorem B7509125 : Blo 1977435 7509125 := bbase (se 4 (by rfl) ⟨703980, by rfl⟩ : syracuseStep 7509125 = 1407961) (by norm_num)
theorem B5006083 : Blo 1977435 5006083 := bstep (se 1 (by rfl) ⟨3754562, by rfl⟩ : syracuseStep 5006083 = 7509125) B7509125
theorem B6674777 : Blo 1977435 6674777 := bstep (se 2 (by rfl) ⟨2503041, by rfl⟩ : syracuseStep 6674777 = 5006083) B5006083
theorem B4449851 : Blo 1977435 4449851 := bstep (se 1 (by rfl) ⟨3337388, by rfl⟩ : syracuseStep 4449851 = 6674777) B6674777
theorem B2966567 : Blo 1977435 2966567 := bstep (se 1 (by rfl) ⟨2224925, by rfl⟩ : syracuseStep 2966567 = 4449851) B4449851
theorem B1977711 : Blo 1977435 1977711 := bstep (se 1 (by rfl) ⟨1483283, by rfl⟩ : syracuseStep 1977711 = 2966567) B2966567
theorem B2966573 : Blo 1977435 2966573 := bbase (se 3 (by rfl) ⟨556232, by rfl⟩ : syracuseStep 2966573 = 1112465) (by norm_num)
theorem B1977715 : Blo 1977435 1977715 := bstep (se 1 (by rfl) ⟨1483286, by rfl⟩ : syracuseStep 1977715 = 2966573) B2966573
theorem B4449869 : Blo 1977435 4449869 := bbase (se 3 (by rfl) ⟨834350, by rfl⟩ : syracuseStep 4449869 = 1668701) (by norm_num)
theorem B2966579 : Blo 1977435 2966579 := bstep (se 1 (by rfl) ⟨2224934, by rfl⟩ : syracuseStep 2966579 = 4449869) B4449869
theorem B1977719 : Blo 1977435 1977719 := bstep (se 1 (by rfl) ⟨1483289, by rfl⟩ : syracuseStep 1977719 = 2966579) B2966579
theorem B2503057 : Blo 1977435 2503057 := bbase (se 2 (by rfl) ⟨938646, by rfl⟩ : syracuseStep 2503057 = 1877293) (by norm_num)
theorem B3337409 : Blo 1977435 3337409 := bstep (se 2 (by rfl) ⟨1251528, by rfl⟩ : syracuseStep 3337409 = 2503057) B2503057
theorem B2224939 : Blo 1977435 2224939 := bstep (se 1 (by rfl) ⟨1668704, by rfl⟩ : syracuseStep 2224939 = 3337409) B3337409
theorem B2966585 : Blo 1977435 2966585 := bstep (se 2 (by rfl) ⟨1112469, by rfl⟩ : syracuseStep 2966585 = 2224939) B2224939
theorem B1977723 : Blo 1977435 1977723 := bstep (se 1 (by rfl) ⟨1483292, by rfl⟩ : syracuseStep 1977723 = 2966585) B2966585
theorem B4223917 : Blo 1977435 4223917 := bbase (se 3 (by rfl) ⟨791984, by rfl⟩ : syracuseStep 4223917 = 1583969) (by norm_num)
theorem B22527557 : Blo 1977435 22527557 := bstep (se 4 (by rfl) ⟨2111958, by rfl⟩ : syracuseStep 22527557 = 4223917) B4223917
theorem B15018371 : Blo 1977435 15018371 := bstep (se 1 (by rfl) ⟨11263778, by rfl⟩ : syracuseStep 15018371 = 22527557) B22527557
theorem B10012247 : Blo 1977435 10012247 := bstep (se 1 (by rfl) ⟨7509185, by rfl⟩ : syracuseStep 10012247 = 15018371) B15018371
theorem B6674831 : Blo 1977435 6674831 := bstep (se 1 (by rfl) ⟨5006123, by rfl⟩ : syracuseStep 6674831 = 10012247) B10012247
theorem B4449887 : Blo 1977435 4449887 := bstep (se 1 (by rfl) ⟨3337415, by rfl⟩ : syracuseStep 4449887 = 6674831) B6674831
theorem B2966591 : Blo 1977435 2966591 := bstep (se 1 (by rfl) ⟨2224943, by rfl⟩ : syracuseStep 2966591 = 4449887) B4449887
theorem B1977727 : Blo 1977435 1977727 := bstep (se 1 (by rfl) ⟨1483295, by rfl⟩ : syracuseStep 1977727 = 2966591) B2966591
theorem B2966597 : Blo 1977435 2966597 := bbase (se 4 (by rfl) ⟨278118, by rfl⟩ : syracuseStep 2966597 = 556237) (by norm_num)
theorem B1977731 : Blo 1977435 1977731 := bstep (se 1 (by rfl) ⟨1483298, by rfl⟩ : syracuseStep 1977731 = 2966597) B2966597
theorem B3337429 : Blo 1977435 3337429 := bbase (se 7 (by rfl) ⟨39110, by rfl⟩ : syracuseStep 3337429 = 78221) (by norm_num)
theorem B4449905 : Blo 1977435 4449905 := bstep (se 2 (by rfl) ⟨1668714, by rfl⟩ : syracuseStep 4449905 = 3337429) B3337429
theorem B2966603 : Blo 1977435 2966603 := bstep (se 1 (by rfl) ⟨2224952, by rfl⟩ : syracuseStep 2966603 = 4449905) B4449905
theorem B1977735 : Blo 1977435 1977735 := bstep (se 1 (by rfl) ⟨1483301, by rfl⟩ : syracuseStep 1977735 = 2966603) B2966603
theorem B2224957 : Blo 1977435 2224957 := bbase (se 3 (by rfl) ⟨417179, by rfl⟩ : syracuseStep 2224957 = 834359) (by norm_num)
theorem B2966609 : Blo 1977435 2966609 := bstep (se 2 (by rfl) ⟨1112478, by rfl⟩ : syracuseStep 2966609 = 2224957) B2224957
theorem B1977739 : Blo 1977435 1977739 := bstep (se 1 (by rfl) ⟨1483304, by rfl⟩ : syracuseStep 1977739 = 2966609) B2966609
theorem B6674885 : Blo 1977435 6674885 := bbase (se 4 (by rfl) ⟨625770, by rfl⟩ : syracuseStep 6674885 = 1251541) (by norm_num)
theorem B4449923 : Blo 1977435 4449923 := bstep (se 1 (by rfl) ⟨3337442, by rfl⟩ : syracuseStep 4449923 = 6674885) B6674885
theorem B2966615 : Blo 1977435 2966615 := bstep (se 1 (by rfl) ⟨2224961, by rfl⟩ : syracuseStep 2966615 = 4449923) B4449923
theorem B1977743 : Blo 1977435 1977743 := bstep (se 1 (by rfl) ⟨1483307, by rfl⟩ : syracuseStep 1977743 = 2966615) B2966615
theorem B2966621 : Blo 1977435 2966621 := bbase (se 3 (by rfl) ⟨556241, by rfl⟩ : syracuseStep 2966621 = 1112483) (by norm_num)
theorem B1977747 : Blo 1977435 1977747 := bstep (se 1 (by rfl) ⟨1483310, by rfl⟩ : syracuseStep 1977747 = 2966621) B2966621
theorem B4449941 : Blo 1977435 4449941 := bbase (se 6 (by rfl) ⟨104295, by rfl⟩ : syracuseStep 4449941 = 208591) (by norm_num)
theorem B2966627 : Blo 1977435 2966627 := bstep (se 1 (by rfl) ⟨2224970, by rfl⟩ : syracuseStep 2966627 = 4449941) B4449941
theorem B1977751 : Blo 1977435 1977751 := bstep (se 1 (by rfl) ⟨1483313, by rfl⟩ : syracuseStep 1977751 = 2966627) B2966627
theorem B2111989 : Blo 1977435 2111989 := bbase (se 5 (by rfl) ⟨98999, by rfl⟩ : syracuseStep 2111989 = 197999) (by norm_num)
theorem B2815985 : Blo 1977435 2815985 := bstep (se 2 (by rfl) ⟨1055994, by rfl⟩ : syracuseStep 2815985 = 2111989) B2111989
theorem B7509293 : Blo 1977435 7509293 := bstep (se 3 (by rfl) ⟨1407992, by rfl⟩ : syracuseStep 7509293 = 2815985) B2815985
theorem B5006195 : Blo 1977435 5006195 := bstep (se 1 (by rfl) ⟨3754646, by rfl⟩ : syracuseStep 5006195 = 7509293) B7509293
theorem B3337463 : Blo 1977435 3337463 := bstep (se 1 (by rfl) ⟨2503097, by rfl⟩ : syracuseStep 3337463 = 5006195) B5006195
theorem B2224975 : Blo 1977435 2224975 := bstep (se 1 (by rfl) ⟨1668731, by rfl⟩ : syracuseStep 2224975 = 3337463) B3337463
theorem B2966633 : Blo 1977435 2966633 := bstep (se 2 (by rfl) ⟨1112487, by rfl⟩ : syracuseStep 2966633 = 2224975) B2224975
theorem B1977755 : Blo 1977435 1977755 := bstep (se 1 (by rfl) ⟨1483316, by rfl⟩ : syracuseStep 1977755 = 2966633) B2966633
theorem B12671957 : Blo 1977435 12671957 := bbase (se 7 (by rfl) ⟨148499, by rfl⟩ : syracuseStep 12671957 = 296999) (by norm_num)
theorem B8447971 : Blo 1977435 8447971 := bstep (se 1 (by rfl) ⟨6335978, by rfl⟩ : syracuseStep 8447971 = 12671957) B12671957
theorem B11263961 : Blo 1977435 11263961 := bstep (se 2 (by rfl) ⟨4223985, by rfl⟩ : syracuseStep 11263961 = 8447971) B8447971
theorem B7509307 : Blo 1977435 7509307 := bstep (se 1 (by rfl) ⟨5631980, by rfl⟩ : syracuseStep 7509307 = 11263961) B11263961
theorem B10012409 : Blo 1977435 10012409 := bstep (se 2 (by rfl) ⟨3754653, by rfl⟩ : syracuseStep 10012409 = 7509307) B7509307
theorem B6674939 : Blo 1977435 6674939 := bstep (se 1 (by rfl) ⟨5006204, by rfl⟩ : syracuseStep 6674939 = 10012409) B10012409
theorem B4449959 : Blo 1977435 4449959 := bstep (se 1 (by rfl) ⟨3337469, by rfl⟩ : syracuseStep 4449959 = 6674939) B6674939
theorem B2966639 : Blo 1977435 2966639 := bstep (se 1 (by rfl) ⟨2224979, by rfl⟩ : syracuseStep 2966639 = 4449959) B4449959
theorem B1977759 : Blo 1977435 1977759 := bstep (se 1 (by rfl) ⟨1483319, by rfl⟩ : syracuseStep 1977759 = 2966639) B2966639
theorem B2966645 : Blo 1977435 2966645 := bbase (se 5 (by rfl) ⟨139061, by rfl⟩ : syracuseStep 2966645 = 278123) (by norm_num)
theorem B1977763 : Blo 1977435 1977763 := bstep (se 1 (by rfl) ⟨1483322, by rfl⟩ : syracuseStep 1977763 = 2966645) B2966645
theorem B3754669 : Blo 1977435 3754669 := bbase (se 3 (by rfl) ⟨704000, by rfl⟩ : syracuseStep 3754669 = 1408001) (by norm_num)
theorem B5006225 : Blo 1977435 5006225 := bstep (se 2 (by rfl) ⟨1877334, by rfl⟩ : syracuseStep 5006225 = 3754669) B3754669
theorem B3337483 : Blo 1977435 3337483 := bstep (se 1 (by rfl) ⟨2503112, by rfl⟩ : syracuseStep 3337483 = 5006225) B5006225
theorem B4449977 : Blo 1977435 4449977 := bstep (se 2 (by rfl) ⟨1668741, by rfl⟩ : syracuseStep 4449977 = 3337483) B3337483
theorem B2966651 : Blo 1977435 2966651 := bstep (se 1 (by rfl) ⟨2224988, by rfl⟩ : syracuseStep 2966651 = 4449977) B4449977
theorem B1977767 : Blo 1977435 1977767 := bstep (se 1 (by rfl) ⟨1483325, by rfl⟩ : syracuseStep 1977767 = 2966651) B2966651
theorem B2224993 : Blo 1977435 2224993 := bbase (se 2 (by rfl) ⟨834372, by rfl⟩ : syracuseStep 2224993 = 1668745) (by norm_num)
theorem B2966657 : Blo 1977435 2966657 := bstep (se 2 (by rfl) ⟨1112496, by rfl⟩ : syracuseStep 2966657 = 2224993) B2224993
theorem B1977771 : Blo 1977435 1977771 := bstep (se 1 (by rfl) ⟨1483328, by rfl⟩ : syracuseStep 1977771 = 2966657) B2966657
theorem B5006245 : Blo 1977435 5006245 := bbase (se 4 (by rfl) ⟨469335, by rfl⟩ : syracuseStep 5006245 = 938671) (by norm_num)
theorem B6674993 : Blo 1977435 6674993 := bstep (se 2 (by rfl) ⟨2503122, by rfl⟩ : syracuseStep 6674993 = 5006245) B5006245
theorem B4449995 : Blo 1977435 4449995 := bstep (se 1 (by rfl) ⟨3337496, by rfl⟩ : syracuseStep 4449995 = 6674993) B6674993
theorem B2966663 : Blo 1977435 2966663 := bstep (se 1 (by rfl) ⟨2224997, by rfl⟩ : syracuseStep 2966663 = 4449995) B4449995
theorem B1977775 : Blo 1977435 1977775 := bstep (se 1 (by rfl) ⟨1483331, by rfl⟩ : syracuseStep 1977775 = 2966663) B2966663
theorem B2966669 : Blo 1977435 2966669 := bbase (se 3 (by rfl) ⟨556250, by rfl⟩ : syracuseStep 2966669 = 1112501) (by norm_num)
theorem B1977779 : Blo 1977435 1977779 := bstep (se 1 (by rfl) ⟨1483334, by rfl⟩ : syracuseStep 1977779 = 2966669) B2966669
theorem B4450013 : Blo 1977435 4450013 := bbase (se 3 (by rfl) ⟨834377, by rfl⟩ : syracuseStep 4450013 = 1668755) (by norm_num)
theorem B2966675 : Blo 1977435 2966675 := bstep (se 1 (by rfl) ⟨2225006, by rfl⟩ : syracuseStep 2966675 = 4450013) B4450013
theorem B1977783 : Blo 1977435 1977783 := bstep (se 1 (by rfl) ⟨1483337, by rfl⟩ : syracuseStep 1977783 = 2966675) B2966675
theorem B3337517 : Blo 1977435 3337517 := bbase (se 3 (by rfl) ⟨625784, by rfl⟩ : syracuseStep 3337517 = 1251569) (by norm_num)
theorem B2225011 : Blo 1977435 2225011 := bstep (se 1 (by rfl) ⟨1668758, by rfl⟩ : syracuseStep 2225011 = 3337517) B3337517
theorem B2966681 : Blo 1977435 2966681 := bstep (se 2 (by rfl) ⟨1112505, by rfl⟩ : syracuseStep 2966681 = 2225011) B2225011
theorem B1977787 : Blo 1977435 1977787 := bstep (se 1 (by rfl) ⟨1483340, by rfl⟩ : syracuseStep 1977787 = 2966681) B2966681
theorem B18791605 : Blo 1977435 18791605 := bbase (se 5 (by rfl) ⟨880856, by rfl⟩ : syracuseStep 18791605 = 1761713) (by norm_num)
theorem B25055473 : Blo 1977435 25055473 := bstep (se 2 (by rfl) ⟨9395802, by rfl⟩ : syracuseStep 25055473 = 18791605) B18791605
theorem B33407297 : Blo 1977435 33407297 := bstep (se 2 (by rfl) ⟨12527736, by rfl⟩ : syracuseStep 33407297 = 25055473) B25055473
theorem B22271531 : Blo 1977435 22271531 := bstep (se 1 (by rfl) ⟨16703648, by rfl⟩ : syracuseStep 22271531 = 33407297) B33407297
theorem B59390749 : Blo 1977435 59390749 := bstep (se 3 (by rfl) ⟨11135765, by rfl⟩ : syracuseStep 59390749 = 22271531) B22271531
theorem B316750661 : Blo 1977435 316750661 := bstep (se 4 (by rfl) ⟨29695374, by rfl⟩ : syracuseStep 316750661 = 59390749) B59390749
theorem B211167107 : Blo 1977435 211167107 := bstep (se 1 (by rfl) ⟨158375330, by rfl⟩ : syracuseStep 211167107 = 316750661) B316750661
theorem B140778071 : Blo 1977435 140778071 := bstep (se 1 (by rfl) ⟨105583553, by rfl⟩ : syracuseStep 140778071 = 211167107) B211167107
theorem B93852047 : Blo 1977435 93852047 := bstep (se 1 (by rfl) ⟨70389035, by rfl⟩ : syracuseStep 93852047 = 140778071) B140778071
theorem B250272125 : Blo 1977435 250272125 := bstep (se 3 (by rfl) ⟨46926023, by rfl⟩ : syracuseStep 250272125 = 93852047) B93852047
theorem B166848083 : Blo 1977435 166848083 := bstep (se 1 (by rfl) ⟨125136062, by rfl⟩ : syracuseStep 166848083 = 250272125) B250272125
theorem B111232055 : Blo 1977435 111232055 := bstep (se 1 (by rfl) ⟨83424041, by rfl⟩ : syracuseStep 111232055 = 166848083) B166848083
theorem B296618813 : Blo 1977435 296618813 := bstep (se 3 (by rfl) ⟨55616027, by rfl⟩ : syracuseStep 296618813 = 111232055) B111232055
theorem B197745875 : Blo 1977435 197745875 := bstep (se 1 (by rfl) ⟨148309406, by rfl⟩ : syracuseStep 197745875 = 296618813) B296618813
theorem B131830583 : Blo 1977435 131830583 := bstep (se 1 (by rfl) ⟨98872937, by rfl⟩ : syracuseStep 131830583 = 197745875) B197745875
theorem B1406192885 : Blo 1977435 1406192885 := bstep (se 5 (by rfl) ⟨65915291, by rfl⟩ : syracuseStep 1406192885 = 131830583) B131830583
theorem B937461923 : Blo 1977435 937461923 := bstep (se 1 (by rfl) ⟨703096442, by rfl⟩ : syracuseStep 937461923 = 1406192885) B1406192885
theorem B624974615 : Blo 1977435 624974615 := bstep (se 1 (by rfl) ⟨468730961, by rfl⟩ : syracuseStep 624974615 = 937461923) B937461923
theorem B416649743 : Blo 1977435 416649743 := bstep (se 1 (by rfl) ⟨312487307, by rfl⟩ : syracuseStep 416649743 = 624974615) B624974615
theorem B277766495 : Blo 1977435 277766495 := bstep (se 1 (by rfl) ⟨208324871, by rfl⟩ : syracuseStep 277766495 = 416649743) B416649743
theorem B185177663 : Blo 1977435 185177663 := bstep (se 1 (by rfl) ⟨138883247, by rfl⟩ : syracuseStep 185177663 = 277766495) B277766495
theorem B123451775 : Blo 1977435 123451775 := bstep (se 1 (by rfl) ⟨92588831, by rfl⟩ : syracuseStep 123451775 = 185177663) B185177663
theorem B82301183 : Blo 1977435 82301183 := bstep (se 1 (by rfl) ⟨61725887, by rfl⟩ : syracuseStep 82301183 = 123451775) B123451775
theorem B54867455 : Blo 1977435 54867455 := bstep (se 1 (by rfl) ⟨41150591, by rfl⟩ : syracuseStep 54867455 = 82301183) B82301183
theorem B36578303 : Blo 1977435 36578303 := bstep (se 1 (by rfl) ⟨27433727, by rfl⟩ : syracuseStep 36578303 = 54867455) B54867455
theorem B24385535 : Blo 1977435 24385535 := bstep (se 1 (by rfl) ⟨18289151, by rfl⟩ : syracuseStep 24385535 = 36578303) B36578303
theorem B16257023 : Blo 1977435 16257023 := bstep (se 1 (by rfl) ⟨12192767, by rfl⟩ : syracuseStep 16257023 = 24385535) B24385535
theorem B10838015 : Blo 1977435 10838015 := bstep (se 1 (by rfl) ⟨8128511, by rfl⟩ : syracuseStep 10838015 = 16257023) B16257023
theorem B7225343 : Blo 1977435 7225343 := bstep (se 1 (by rfl) ⟨5419007, by rfl⟩ : syracuseStep 7225343 = 10838015) B10838015
theorem B77070325 : Blo 1977435 77070325 := bstep (se 5 (by rfl) ⟨3612671, by rfl⟩ : syracuseStep 77070325 = 7225343) B7225343
theorem B102760433 : Blo 1977435 102760433 := bstep (se 2 (by rfl) ⟨38535162, by rfl⟩ : syracuseStep 102760433 = 77070325) B77070325
theorem B68506955 : Blo 1977435 68506955 := bstep (se 1 (by rfl) ⟨51380216, by rfl⟩ : syracuseStep 68506955 = 102760433) B102760433
theorem B45671303 : Blo 1977435 45671303 := bstep (se 1 (by rfl) ⟨34253477, by rfl⟩ : syracuseStep 45671303 = 68506955) B68506955
theorem B30447535 : Blo 1977435 30447535 := bstep (se 1 (by rfl) ⟨22835651, by rfl⟩ : syracuseStep 30447535 = 45671303) B45671303
theorem B40596713 : Blo 1977435 40596713 := bstep (se 2 (by rfl) ⟨15223767, by rfl⟩ : syracuseStep 40596713 = 30447535) B30447535
theorem B27064475 : Blo 1977435 27064475 := bstep (se 1 (by rfl) ⟨20298356, by rfl⟩ : syracuseStep 27064475 = 40596713) B40596713
theorem B18042983 : Blo 1977435 18042983 := bstep (se 1 (by rfl) ⟨13532237, by rfl⟩ : syracuseStep 18042983 = 27064475) B27064475
theorem B12028655 : Blo 1977435 12028655 := bstep (se 1 (by rfl) ⟨9021491, by rfl⟩ : syracuseStep 12028655 = 18042983) B18042983
theorem B8019103 : Blo 1977435 8019103 := bstep (se 1 (by rfl) ⟨6014327, by rfl⟩ : syracuseStep 8019103 = 12028655) B12028655
theorem B10692137 : Blo 1977435 10692137 := bstep (se 2 (by rfl) ⟨4009551, by rfl⟩ : syracuseStep 10692137 = 8019103) B8019103
theorem B7128091 : Blo 1977435 7128091 := bstep (se 1 (by rfl) ⟨5346068, by rfl⟩ : syracuseStep 7128091 = 10692137) B10692137
theorem B38016485 : Blo 1977435 38016485 := bstep (se 4 (by rfl) ⟨3564045, by rfl⟩ : syracuseStep 38016485 = 7128091) B7128091
theorem B25344323 : Blo 1977435 25344323 := bstep (se 1 (by rfl) ⟨19008242, by rfl⟩ : syracuseStep 25344323 = 38016485) B38016485
theorem B16896215 : Blo 1977435 16896215 := bstep (se 1 (by rfl) ⟨12672161, by rfl⟩ : syracuseStep 16896215 = 25344323) B25344323
theorem B11264143 : Blo 1977435 11264143 := bstep (se 1 (by rfl) ⟨8448107, by rfl⟩ : syracuseStep 11264143 = 16896215) B16896215
theorem B15018857 : Blo 1977435 15018857 := bstep (se 2 (by rfl) ⟨5632071, by rfl⟩ : syracuseStep 15018857 = 11264143) B11264143
theorem B10012571 : Blo 1977435 10012571 := bstep (se 1 (by rfl) ⟨7509428, by rfl⟩ : syracuseStep 10012571 = 15018857) B15018857
theorem B6675047 : Blo 1977435 6675047 := bstep (se 1 (by rfl) ⟨5006285, by rfl⟩ : syracuseStep 6675047 = 10012571) B10012571
theorem B4450031 : Blo 1977435 4450031 := bstep (se 1 (by rfl) ⟨3337523, by rfl⟩ : syracuseStep 4450031 = 6675047) B6675047
theorem B2966687 : Blo 1977435 2966687 := bstep (se 1 (by rfl) ⟨2225015, by rfl⟩ : syracuseStep 2966687 = 4450031) B4450031
theorem B1977791 : Blo 1977435 1977791 := bstep (se 1 (by rfl) ⟨1483343, by rfl⟩ : syracuseStep 1977791 = 2966687) B2966687
theorem B2966693 : Blo 1977435 2966693 := bbase (se 4 (by rfl) ⟨278127, by rfl⟩ : syracuseStep 2966693 = 556255) (by norm_num)
theorem B1977795 : Blo 1977435 1977795 := bstep (se 1 (by rfl) ⟨1483346, by rfl⟩ : syracuseStep 1977795 = 2966693) B2966693
theorem B2503153 : Blo 1977435 2503153 := bbase (se 2 (by rfl) ⟨938682, by rfl⟩ : syracuseStep 2503153 = 1877365) (by norm_num)
theorem B3337537 : Blo 1977435 3337537 := bstep (se 2 (by rfl) ⟨1251576, by rfl⟩ : syracuseStep 3337537 = 2503153) B2503153
theorem B4450049 : Blo 1977435 4450049 := bstep (se 2 (by rfl) ⟨1668768, by rfl⟩ : syracuseStep 4450049 = 3337537) B3337537
theorem B2966699 : Blo 1977435 2966699 := bstep (se 1 (by rfl) ⟨2225024, by rfl⟩ : syracuseStep 2966699 = 4450049) B4450049
theorem B1977799 : Blo 1977435 1977799 := bstep (se 1 (by rfl) ⟨1483349, by rfl⟩ : syracuseStep 1977799 = 2966699) B2966699
theorem B2225029 : Blo 1977435 2225029 := bbase (se 4 (by rfl) ⟨208596, by rfl⟩ : syracuseStep 2225029 = 417193) (by norm_num)
theorem B2966705 : Blo 1977435 2966705 := bstep (se 2 (by rfl) ⟨1112514, by rfl⟩ : syracuseStep 2966705 = 2225029) B2225029
theorem B1977803 : Blo 1977435 1977803 := bstep (se 1 (by rfl) ⟨1483352, by rfl⟩ : syracuseStep 1977803 = 2966705) B2966705
theorem B4752101 : Blo 1977435 4752101 := bbase (se 4 (by rfl) ⟨445509, by rfl⟩ : syracuseStep 4752101 = 891019) (by norm_num)
theorem B3168067 : Blo 1977435 3168067 := bstep (se 1 (by rfl) ⟨2376050, by rfl⟩ : syracuseStep 3168067 = 4752101) B4752101
theorem B4224089 : Blo 1977435 4224089 := bstep (se 2 (by rfl) ⟨1584033, by rfl⟩ : syracuseStep 4224089 = 3168067) B3168067
theorem B2816059 : Blo 1977435 2816059 := bstep (se 1 (by rfl) ⟨2112044, by rfl⟩ : syracuseStep 2816059 = 4224089) B4224089
theorem B3754745 : Blo 1977435 3754745 := bstep (se 2 (by rfl) ⟨1408029, by rfl⟩ : syracuseStep 3754745 = 2816059) B2816059
theorem B2503163 : Blo 1977435 2503163 := bstep (se 1 (by rfl) ⟨1877372, by rfl⟩ : syracuseStep 2503163 = 3754745) B3754745
theorem B6675101 : Blo 1977435 6675101 := bstep (se 3 (by rfl) ⟨1251581, by rfl⟩ : syracuseStep 6675101 = 2503163) B2503163
theorem B4450067 : Blo 1977435 4450067 := bstep (se 1 (by rfl) ⟨3337550, by rfl⟩ : syracuseStep 4450067 = 6675101) B6675101
theorem B2966711 : Blo 1977435 2966711 := bstep (se 1 (by rfl) ⟨2225033, by rfl⟩ : syracuseStep 2966711 = 4450067) B4450067
theorem B1977807 : Blo 1977435 1977807 := bstep (se 1 (by rfl) ⟨1483355, by rfl⟩ : syracuseStep 1977807 = 2966711) B2966711
theorem B2966717 : Blo 1977435 2966717 := bbase (se 3 (by rfl) ⟨556259, by rfl⟩ : syracuseStep 2966717 = 1112519) (by norm_num)
theorem B1977811 : Blo 1977435 1977811 := bstep (se 1 (by rfl) ⟨1483358, by rfl⟩ : syracuseStep 1977811 = 2966717) B2966717
theorem B4450085 : Blo 1977435 4450085 := bbase (se 4 (by rfl) ⟨417195, by rfl⟩ : syracuseStep 4450085 = 834391) (by norm_num)
theorem B2966723 : Blo 1977435 2966723 := bstep (se 1 (by rfl) ⟨2225042, by rfl⟩ : syracuseStep 2966723 = 4450085) B4450085
theorem B1977815 : Blo 1977435 1977815 := bstep (se 1 (by rfl) ⟨1483361, by rfl⟩ : syracuseStep 1977815 = 2966723) B2966723
theorem B5006357 : Blo 1977435 5006357 := bbase (se 6 (by rfl) ⟨117336, by rfl⟩ : syracuseStep 5006357 = 234673) (by norm_num)
theorem B3337571 : Blo 1977435 3337571 := bstep (se 1 (by rfl) ⟨2503178, by rfl⟩ : syracuseStep 3337571 = 5006357) B5006357
theorem B2225047 : Blo 1977435 2225047 := bstep (se 1 (by rfl) ⟨1668785, by rfl⟩ : syracuseStep 2225047 = 3337571) B3337571
theorem B2966729 : Blo 1977435 2966729 := bstep (se 2 (by rfl) ⟨1112523, by rfl⟩ : syracuseStep 2966729 = 2225047) B2225047
theorem B1977819 : Blo 1977435 1977819 := bstep (se 1 (by rfl) ⟨1483364, by rfl⟩ : syracuseStep 1977819 = 2966729) B2966729
theorem B8448245 : Blo 1977435 8448245 := bbase (se 5 (by rfl) ⟨396011, by rfl⟩ : syracuseStep 8448245 = 792023) (by norm_num)
theorem B5632163 : Blo 1977435 5632163 := bstep (se 1 (by rfl) ⟨4224122, by rfl⟩ : syracuseStep 5632163 = 8448245) B8448245
theorem B3754775 : Blo 1977435 3754775 := bstep (se 1 (by rfl) ⟨2816081, by rfl⟩ : syracuseStep 3754775 = 5632163) B5632163
theorem B10012733 : Blo 1977435 10012733 := bstep (se 3 (by rfl) ⟨1877387, by rfl⟩ : syracuseStep 10012733 = 3754775) B3754775
theorem B6675155 : Blo 1977435 6675155 := bstep (se 1 (by rfl) ⟨5006366, by rfl⟩ : syracuseStep 6675155 = 10012733) B10012733
theorem B4450103 : Blo 1977435 4450103 := bstep (se 1 (by rfl) ⟨3337577, by rfl⟩ : syracuseStep 4450103 = 6675155) B6675155
theorem B2966735 : Blo 1977435 2966735 := bstep (se 1 (by rfl) ⟨2225051, by rfl⟩ : syracuseStep 2966735 = 4450103) B4450103
theorem B1977823 : Blo 1977435 1977823 := bstep (se 1 (by rfl) ⟨1483367, by rfl⟩ : syracuseStep 1977823 = 2966735) B2966735
theorem B2966741 : Blo 1977435 2966741 := bbase (se 7 (by rfl) ⟨34766, by rfl⟩ : syracuseStep 2966741 = 69533) (by norm_num)
theorem B1977827 : Blo 1977435 1977827 := bstep (se 1 (by rfl) ⟨1483370, by rfl⟩ : syracuseStep 1977827 = 2966741) B2966741
theorem B2816093 : Blo 1977435 2816093 := bbase (se 3 (by rfl) ⟨528017, by rfl⟩ : syracuseStep 2816093 = 1056035) (by norm_num)
theorem B7509581 : Blo 1977435 7509581 := bstep (se 3 (by rfl) ⟨1408046, by rfl⟩ : syracuseStep 7509581 = 2816093) B2816093
theorem B5006387 : Blo 1977435 5006387 := bstep (se 1 (by rfl) ⟨3754790, by rfl⟩ : syracuseStep 5006387 = 7509581) B7509581
theorem B3337591 : Blo 1977435 3337591 := bstep (se 1 (by rfl) ⟨2503193, by rfl⟩ : syracuseStep 3337591 = 5006387) B5006387
theorem B4450121 : Blo 1977435 4450121 := bstep (se 2 (by rfl) ⟨1668795, by rfl⟩ : syracuseStep 4450121 = 3337591) B3337591
theorem B2966747 : Blo 1977435 2966747 := bstep (se 1 (by rfl) ⟨2225060, by rfl⟩ : syracuseStep 2966747 = 4450121) B4450121
theorem B1977831 : Blo 1977435 1977831 := bstep (se 1 (by rfl) ⟨1483373, by rfl⟩ : syracuseStep 1977831 = 2966747) B2966747
theorem B2225065 : Blo 1977435 2225065 := bbase (se 2 (by rfl) ⟨834399, by rfl⟩ : syracuseStep 2225065 = 1668799) (by norm_num)
theorem B2966753 : Blo 1977435 2966753 := bstep (se 2 (by rfl) ⟨1112532, by rfl⟩ : syracuseStep 2966753 = 2225065) B2225065
theorem B1977835 : Blo 1977435 1977835 := bstep (se 1 (by rfl) ⟨1483376, by rfl⟩ : syracuseStep 1977835 = 2966753) B2966753
theorem B12028949 : Blo 1977435 12028949 := bbase (se 6 (by rfl) ⟨281928, by rfl⟩ : syracuseStep 12028949 = 563857) (by norm_num)
theorem B8019299 : Blo 1977435 8019299 := bstep (se 1 (by rfl) ⟨6014474, by rfl⟩ : syracuseStep 8019299 = 12028949) B12028949
theorem B5346199 : Blo 1977435 5346199 := bstep (se 1 (by rfl) ⟨4009649, by rfl⟩ : syracuseStep 5346199 = 8019299) B8019299
theorem B7128265 : Blo 1977435 7128265 := bstep (se 2 (by rfl) ⟨2673099, by rfl⟩ : syracuseStep 7128265 = 5346199) B5346199
theorem B9504353 : Blo 1977435 9504353 := bstep (se 2 (by rfl) ⟨3564132, by rfl⟩ : syracuseStep 9504353 = 7128265) B7128265
theorem B6336235 : Blo 1977435 6336235 := bstep (se 1 (by rfl) ⟨4752176, by rfl⟩ : syracuseStep 6336235 = 9504353) B9504353
theorem B8448313 : Blo 1977435 8448313 := bstep (se 2 (by rfl) ⟨3168117, by rfl⟩ : syracuseStep 8448313 = 6336235) B6336235
theorem B11264417 : Blo 1977435 11264417 := bstep (se 2 (by rfl) ⟨4224156, by rfl⟩ : syracuseStep 11264417 = 8448313) B8448313
theorem B7509611 : Blo 1977435 7509611 := bstep (se 1 (by rfl) ⟨5632208, by rfl⟩ : syracuseStep 7509611 = 11264417) B11264417
theorem B5006407 : Blo 1977435 5006407 := bstep (se 1 (by rfl) ⟨3754805, by rfl⟩ : syracuseStep 5006407 = 7509611) B7509611
theorem B6675209 : Blo 1977435 6675209 := bstep (se 2 (by rfl) ⟨2503203, by rfl⟩ : syracuseStep 6675209 = 5006407) B5006407
theorem B4450139 : Blo 1977435 4450139 := bstep (se 1 (by rfl) ⟨3337604, by rfl⟩ : syracuseStep 4450139 = 6675209) B6675209
theorem B2966759 : Blo 1977435 2966759 := bstep (se 1 (by rfl) ⟨2225069, by rfl⟩ : syracuseStep 2966759 = 4450139) B4450139
theorem B1977839 : Blo 1977435 1977839 := bstep (se 1 (by rfl) ⟨1483379, by rfl⟩ : syracuseStep 1977839 = 2966759) B2966759
theorem B2966765 : Blo 1977435 2966765 := bbase (se 3 (by rfl) ⟨556268, by rfl⟩ : syracuseStep 2966765 = 1112537) (by norm_num)
theorem B1977843 : Blo 1977435 1977843 := bstep (se 1 (by rfl) ⟨1483382, by rfl⟩ : syracuseStep 1977843 = 2966765) B2966765
theorem B4450157 : Blo 1977435 4450157 := bbase (se 3 (by rfl) ⟨834404, by rfl⟩ : syracuseStep 4450157 = 1668809) (by norm_num)
theorem B2966771 : Blo 1977435 2966771 := bstep (se 1 (by rfl) ⟨2225078, by rfl⟩ : syracuseStep 2966771 = 4450157) B4450157
theorem B1977847 : Blo 1977435 1977847 := bstep (se 1 (by rfl) ⟨1483385, by rfl⟩ : syracuseStep 1977847 = 2966771) B2966771
theorem B3754829 : Blo 1977435 3754829 := bbase (se 3 (by rfl) ⟨704030, by rfl⟩ : syracuseStep 3754829 = 1408061) (by norm_num)
theorem B2503219 : Blo 1977435 2503219 := bstep (se 1 (by rfl) ⟨1877414, by rfl⟩ : syracuseStep 2503219 = 3754829) B3754829
theorem B3337625 : Blo 1977435 3337625 := bstep (se 2 (by rfl) ⟨1251609, by rfl⟩ : syracuseStep 3337625 = 2503219) B2503219
theorem B2225083 : Blo 1977435 2225083 := bstep (se 1 (by rfl) ⟨1668812, by rfl⟩ : syracuseStep 2225083 = 3337625) B3337625
theorem B2966777 : Blo 1977435 2966777 := bstep (se 2 (by rfl) ⟨1112541, by rfl⟩ : syracuseStep 2966777 = 2225083) B2225083
theorem B1977851 : Blo 1977435 1977851 := bstep (se 1 (by rfl) ⟨1483388, by rfl⟩ : syracuseStep 1977851 = 2966777) B2966777
theorem B3007261 : Blo 1977435 3007261 := bbase (se 3 (by rfl) ⟨563861, by rfl⟩ : syracuseStep 3007261 = 1127723) (by norm_num)
theorem B4009681 : Blo 1977435 4009681 := bstep (se 2 (by rfl) ⟨1503630, by rfl⟩ : syracuseStep 4009681 = 3007261) B3007261
theorem B21384965 : Blo 1977435 21384965 := bstep (se 4 (by rfl) ⟨2004840, by rfl⟩ : syracuseStep 21384965 = 4009681) B4009681
theorem B14256643 : Blo 1977435 14256643 := bstep (se 1 (by rfl) ⟨10692482, by rfl⟩ : syracuseStep 14256643 = 21384965) B21384965
theorem B19008857 : Blo 1977435 19008857 := bstep (se 2 (by rfl) ⟨7128321, by rfl⟩ : syracuseStep 19008857 = 14256643) B14256643
theorem B50690285 : Blo 1977435 50690285 := bstep (se 3 (by rfl) ⟨9504428, by rfl⟩ : syracuseStep 50690285 = 19008857) B19008857
theorem B33793523 : Blo 1977435 33793523 := bstep (se 1 (by rfl) ⟨25345142, by rfl⟩ : syracuseStep 33793523 = 50690285) B50690285
theorem B22529015 : Blo 1977435 22529015 := bstep (se 1 (by rfl) ⟨16896761, by rfl⟩ : syracuseStep 22529015 = 33793523) B33793523
theorem B15019343 : Blo 1977435 15019343 := bstep (se 1 (by rfl) ⟨11264507, by rfl⟩ : syracuseStep 15019343 = 22529015) B22529015
theorem B10012895 : Blo 1977435 10012895 := bstep (se 1 (by rfl) ⟨7509671, by rfl⟩ : syracuseStep 10012895 = 15019343) B15019343
theorem B6675263 : Blo 1977435 6675263 := bstep (se 1 (by rfl) ⟨5006447, by rfl⟩ : syracuseStep 6675263 = 10012895) B10012895
theorem B4450175 : Blo 1977435 4450175 := bstep (se 1 (by rfl) ⟨3337631, by rfl⟩ : syracuseStep 4450175 = 6675263) B6675263
theorem B2966783 : Blo 1977435 2966783 := bstep (se 1 (by rfl) ⟨2225087, by rfl⟩ : syracuseStep 2966783 = 4450175) B4450175
theorem B1977855 : Blo 1977435 1977855 := bstep (se 1 (by rfl) ⟨1483391, by rfl⟩ : syracuseStep 1977855 = 2966783) B2966783
theorem B2966789 : Blo 1977435 2966789 := bbase (se 4 (by rfl) ⟨278136, by rfl⟩ : syracuseStep 2966789 = 556273) (by norm_num)
theorem B1977859 : Blo 1977435 1977859 := bstep (se 1 (by rfl) ⟨1483394, by rfl⟩ : syracuseStep 1977859 = 2966789) B2966789
theorem B3337645 : Blo 1977435 3337645 := bbase (se 3 (by rfl) ⟨625808, by rfl⟩ : syracuseStep 3337645 = 1251617) (by norm_num)
theorem B4450193 : Blo 1977435 4450193 := bstep (se 2 (by rfl) ⟨1668822, by rfl⟩ : syracuseStep 4450193 = 3337645) B3337645
theorem B2966795 : Blo 1977435 2966795 := bstep (se 1 (by rfl) ⟨2225096, by rfl⟩ : syracuseStep 2966795 = 4450193) B4450193
theorem B1977863 : Blo 1977435 1977863 := bstep (se 1 (by rfl) ⟨1483397, by rfl⟩ : syracuseStep 1977863 = 2966795) B2966795
theorem B2225101 : Blo 1977435 2225101 := bbase (se 3 (by rfl) ⟨417206, by rfl⟩ : syracuseStep 2225101 = 834413) (by norm_num)
theorem B2966801 : Blo 1977435 2966801 := bstep (se 2 (by rfl) ⟨1112550, by rfl⟩ : syracuseStep 2966801 = 2225101) B2225101
theorem B1977867 : Blo 1977435 1977867 := bstep (se 1 (by rfl) ⟨1483400, by rfl⟩ : syracuseStep 1977867 = 2966801) B2966801
theorem B6675317 : Blo 1977435 6675317 := bbase (se 5 (by rfl) ⟨312905, by rfl⟩ : syracuseStep 6675317 = 625811) (by norm_num)
theorem B4450211 : Blo 1977435 4450211 := bstep (se 1 (by rfl) ⟨3337658, by rfl⟩ : syracuseStep 4450211 = 6675317) B6675317
theorem B2966807 : Blo 1977435 2966807 := bstep (se 1 (by rfl) ⟨2225105, by rfl⟩ : syracuseStep 2966807 = 4450211) B4450211
theorem B1977871 : Blo 1977435 1977871 := bstep (se 1 (by rfl) ⟨1483403, by rfl⟩ : syracuseStep 1977871 = 2966807) B2966807
theorem B2966813 : Blo 1977435 2966813 := bbase (se 3 (by rfl) ⟨556277, by rfl⟩ : syracuseStep 2966813 = 1112555) (by norm_num)
theorem B1977875 : Blo 1977435 1977875 := bstep (se 1 (by rfl) ⟨1483406, by rfl⟩ : syracuseStep 1977875 = 2966813) B2966813
theorem B4450229 : Blo 1977435 4450229 := bbase (se 5 (by rfl) ⟨208604, by rfl⟩ : syracuseStep 4450229 = 417209) (by norm_num)
theorem B2966819 : Blo 1977435 2966819 := bstep (se 1 (by rfl) ⟨2225114, by rfl⟩ : syracuseStep 2966819 = 4450229) B4450229
theorem B1977879 : Blo 1977435 1977879 := bstep (se 1 (by rfl) ⟨1483409, by rfl⟩ : syracuseStep 1977879 = 2966819) B2966819
theorem B18043829 : Blo 1977435 18043829 := bbase (se 5 (by rfl) ⟨845804, by rfl⟩ : syracuseStep 18043829 = 1691609) (by norm_num)
theorem B12029219 : Blo 1977435 12029219 := bstep (se 1 (by rfl) ⟨9021914, by rfl⟩ : syracuseStep 12029219 = 18043829) B18043829
theorem B8019479 : Blo 1977435 8019479 := bstep (se 1 (by rfl) ⟨6014609, by rfl⟩ : syracuseStep 8019479 = 12029219) B12029219
theorem B5346319 : Blo 1977435 5346319 := bstep (se 1 (by rfl) ⟨4009739, by rfl⟩ : syracuseStep 5346319 = 8019479) B8019479
theorem B7128425 : Blo 1977435 7128425 := bstep (se 2 (by rfl) ⟨2673159, by rfl⟩ : syracuseStep 7128425 = 5346319) B5346319
theorem B4752283 : Blo 1977435 4752283 := bstep (se 1 (by rfl) ⟨3564212, by rfl⟩ : syracuseStep 4752283 = 7128425) B7128425
theorem B6336377 : Blo 1977435 6336377 := bstep (se 2 (by rfl) ⟨2376141, by rfl⟩ : syracuseStep 6336377 = 4752283) B4752283
theorem B4224251 : Blo 1977435 4224251 := bstep (se 1 (by rfl) ⟨3168188, by rfl⟩ : syracuseStep 4224251 = 6336377) B6336377
theorem B11264669 : Blo 1977435 11264669 := bstep (se 3 (by rfl) ⟨2112125, by rfl⟩ : syracuseStep 11264669 = 4224251) B4224251
theorem B7509779 : Blo 1977435 7509779 := bstep (se 1 (by rfl) ⟨5632334, by rfl⟩ : syracuseStep 7509779 = 11264669) B11264669
theorem B5006519 : Blo 1977435 5006519 := bstep (se 1 (by rfl) ⟨3754889, by rfl⟩ : syracuseStep 5006519 = 7509779) B7509779
theorem B3337679 : Blo 1977435 3337679 := bstep (se 1 (by rfl) ⟨2503259, by rfl⟩ : syracuseStep 3337679 = 5006519) B5006519
theorem B2225119 : Blo 1977435 2225119 := bstep (se 1 (by rfl) ⟨1668839, by rfl⟩ : syracuseStep 2225119 = 3337679) B3337679
theorem B2966825 : Blo 1977435 2966825 := bstep (se 2 (by rfl) ⟨1112559, by rfl⟩ : syracuseStep 2966825 = 2225119) B2225119
theorem B1977883 : Blo 1977435 1977883 := bstep (se 1 (by rfl) ⟨1483412, by rfl⟩ : syracuseStep 1977883 = 2966825) B2966825
theorem B6336389 : Blo 1977435 6336389 := bbase (se 4 (by rfl) ⟨594036, by rfl⟩ : syracuseStep 6336389 = 1188073) (by norm_num)
theorem B4224259 : Blo 1977435 4224259 := bstep (se 1 (by rfl) ⟨3168194, by rfl⟩ : syracuseStep 4224259 = 6336389) B6336389
theorem B5632345 : Blo 1977435 5632345 := bstep (se 2 (by rfl) ⟨2112129, by rfl⟩ : syracuseStep 5632345 = 4224259) B4224259
theorem B7509793 : Blo 1977435 7509793 := bstep (se 2 (by rfl) ⟨2816172, by rfl⟩ : syracuseStep 7509793 = 5632345) B5632345
theorem B10013057 : Blo 1977435 10013057 := bstep (se 2 (by rfl) ⟨3754896, by rfl⟩ : syracuseStep 10013057 = 7509793) B7509793
theorem B6675371 : Blo 1977435 6675371 := bstep (se 1 (by rfl) ⟨5006528, by rfl⟩ : syracuseStep 6675371 = 10013057) B10013057
theorem B4450247 : Blo 1977435 4450247 := bstep (se 1 (by rfl) ⟨3337685, by rfl⟩ : syracuseStep 4450247 = 6675371) B6675371
theorem B2966831 : Blo 1977435 2966831 := bstep (se 1 (by rfl) ⟨2225123, by rfl⟩ : syracuseStep 2966831 = 4450247) B4450247
theorem B1977887 : Blo 1977435 1977887 := bstep (se 1 (by rfl) ⟨1483415, by rfl⟩ : syracuseStep 1977887 = 2966831) B2966831
theorem B2966837 : Blo 1977435 2966837 := bbase (se 5 (by rfl) ⟨139070, by rfl⟩ : syracuseStep 2966837 = 278141) (by norm_num)
theorem B1977891 : Blo 1977435 1977891 := bstep (se 1 (by rfl) ⟨1483418, by rfl⟩ : syracuseStep 1977891 = 2966837) B2966837
theorem B5006549 : Blo 1977435 5006549 := bbase (se 7 (by rfl) ⟨58670, by rfl⟩ : syracuseStep 5006549 = 117341) (by norm_num)
theorem B3337699 : Blo 1977435 3337699 := bstep (se 1 (by rfl) ⟨2503274, by rfl⟩ : syracuseStep 3337699 = 5006549) B5006549
theorem B4450265 : Blo 1977435 4450265 := bstep (se 2 (by rfl) ⟨1668849, by rfl⟩ : syracuseStep 4450265 = 3337699) B3337699
theorem B2966843 : Blo 1977435 2966843 := bstep (se 1 (by rfl) ⟨2225132, by rfl⟩ : syracuseStep 2966843 = 4450265) B4450265
theorem B1977895 : Blo 1977435 1977895 := bstep (se 1 (by rfl) ⟨1483421, by rfl⟩ : syracuseStep 1977895 = 2966843) B2966843
theorem B2225137 : Blo 1977435 2225137 := bbase (se 2 (by rfl) ⟨834426, by rfl⟩ : syracuseStep 2225137 = 1668853) (by norm_num)
theorem B2966849 : Blo 1977435 2966849 := bstep (se 2 (by rfl) ⟨1112568, by rfl⟩ : syracuseStep 2966849 = 2225137) B2225137
theorem B1977899 : Blo 1977435 1977899 := bstep (se 1 (by rfl) ⟨1483424, by rfl⟩ : syracuseStep 1977899 = 2966849) B2966849
theorem B9504661 : Blo 1977435 9504661 := bbase (se 6 (by rfl) ⟨222765, by rfl⟩ : syracuseStep 9504661 = 445531) (by norm_num)
theorem B12672881 : Blo 1977435 12672881 := bstep (se 2 (by rfl) ⟨4752330, by rfl⟩ : syracuseStep 12672881 = 9504661) B9504661
theorem B8448587 : Blo 1977435 8448587 := bstep (se 1 (by rfl) ⟨6336440, by rfl⟩ : syracuseStep 8448587 = 12672881) B12672881
theorem B5632391 : Blo 1977435 5632391 := bstep (se 1 (by rfl) ⟨4224293, by rfl⟩ : syracuseStep 5632391 = 8448587) B8448587
theorem B3754927 : Blo 1977435 3754927 := bstep (se 1 (by rfl) ⟨2816195, by rfl⟩ : syracuseStep 3754927 = 5632391) B5632391
theorem B5006569 : Blo 1977435 5006569 := bstep (se 2 (by rfl) ⟨1877463, by rfl⟩ : syracuseStep 5006569 = 3754927) B3754927
theorem B6675425 : Blo 1977435 6675425 := bstep (se 2 (by rfl) ⟨2503284, by rfl⟩ : syracuseStep 6675425 = 5006569) B5006569
theorem B4450283 : Blo 1977435 4450283 := bstep (se 1 (by rfl) ⟨3337712, by rfl⟩ : syracuseStep 4450283 = 6675425) B6675425
theorem B2966855 : Blo 1977435 2966855 := bstep (se 1 (by rfl) ⟨2225141, by rfl⟩ : syracuseStep 2966855 = 4450283) B4450283
theorem B1977903 : Blo 1977435 1977903 := bstep (se 1 (by rfl) ⟨1483427, by rfl⟩ : syracuseStep 1977903 = 2966855) B2966855
theorem B2966861 : Blo 1977435 2966861 := bbase (se 3 (by rfl) ⟨556286, by rfl⟩ : syracuseStep 2966861 = 1112573) (by norm_num)
theorem B1977907 : Blo 1977435 1977907 := bstep (se 1 (by rfl) ⟨1483430, by rfl⟩ : syracuseStep 1977907 = 2966861) B2966861
theorem B4450301 : Blo 1977435 4450301 := bbase (se 3 (by rfl) ⟨834431, by rfl⟩ : syracuseStep 4450301 = 1668863) (by norm_num)
theorem B2966867 : Blo 1977435 2966867 := bstep (se 1 (by rfl) ⟨2225150, by rfl⟩ : syracuseStep 2966867 = 4450301) B4450301
theorem B1977911 : Blo 1977435 1977911 := bstep (se 1 (by rfl) ⟨1483433, by rfl⟩ : syracuseStep 1977911 = 2966867) B2966867
theorem B3337733 : Blo 1977435 3337733 := bbase (se 4 (by rfl) ⟨312912, by rfl⟩ : syracuseStep 3337733 = 625825) (by norm_num)
theorem B2225155 : Blo 1977435 2225155 := bstep (se 1 (by rfl) ⟨1668866, by rfl⟩ : syracuseStep 2225155 = 3337733) B3337733
theorem B2966873 : Blo 1977435 2966873 := bstep (se 2 (by rfl) ⟨1112577, by rfl⟩ : syracuseStep 2966873 = 2225155) B2225155
theorem B1977915 : Blo 1977435 1977915 := bstep (se 1 (by rfl) ⟨1483436, by rfl⟩ : syracuseStep 1977915 = 2966873) B2966873
theorem B15019829 : Blo 1977435 15019829 := bbase (se 5 (by rfl) ⟨704054, by rfl⟩ : syracuseStep 15019829 = 1408109) (by norm_num)
theorem B10013219 : Blo 1977435 10013219 := bstep (se 1 (by rfl) ⟨7509914, by rfl⟩ : syracuseStep 10013219 = 15019829) B15019829
theorem B6675479 : Blo 1977435 6675479 := bstep (se 1 (by rfl) ⟨5006609, by rfl⟩ : syracuseStep 6675479 = 10013219) B10013219
theorem B4450319 : Blo 1977435 4450319 := bstep (se 1 (by rfl) ⟨3337739, by rfl⟩ : syracuseStep 4450319 = 6675479) B6675479
theorem B2966879 : Blo 1977435 2966879 := bstep (se 1 (by rfl) ⟨2225159, by rfl⟩ : syracuseStep 2966879 = 4450319) B4450319
theorem B1977919 : Blo 1977435 1977919 := bstep (se 1 (by rfl) ⟨1483439, by rfl⟩ : syracuseStep 1977919 = 2966879) B2966879
theorem B2966885 : Blo 1977435 2966885 := bbase (se 4 (by rfl) ⟨278145, by rfl⟩ : syracuseStep 2966885 = 556291) (by norm_num)
theorem B1977923 : Blo 1977435 1977923 := bstep (se 1 (by rfl) ⟨1483442, by rfl⟩ : syracuseStep 1977923 = 2966885) B2966885
theorem B3754973 : Blo 1977435 3754973 := bbase (se 3 (by rfl) ⟨704057, by rfl⟩ : syracuseStep 3754973 = 1408115) (by norm_num)
theorem B2503315 : Blo 1977435 2503315 := bstep (se 1 (by rfl) ⟨1877486, by rfl⟩ : syracuseStep 2503315 = 3754973) B3754973
theorem B3337753 : Blo 1977435 3337753 := bstep (se 2 (by rfl) ⟨1251657, by rfl⟩ : syracuseStep 3337753 = 2503315) B2503315
theorem B4450337 : Blo 1977435 4450337 := bstep (se 2 (by rfl) ⟨1668876, by rfl⟩ : syracuseStep 4450337 = 3337753) B3337753
theorem B2966891 : Blo 1977435 2966891 := bstep (se 1 (by rfl) ⟨2225168, by rfl⟩ : syracuseStep 2966891 = 4450337) B4450337
theorem B1977927 : Blo 1977435 1977927 := bstep (se 1 (by rfl) ⟨1483445, by rfl⟩ : syracuseStep 1977927 = 2966891) B2966891
theorem B2225173 : Blo 1977435 2225173 := bbase (se 6 (by rfl) ⟨52152, by rfl⟩ : syracuseStep 2225173 = 104305) (by norm_num)
theorem B2966897 : Blo 1977435 2966897 := bstep (se 2 (by rfl) ⟨1112586, by rfl⟩ : syracuseStep 2966897 = 2225173) B2225173
theorem B1977931 : Blo 1977435 1977931 := bstep (se 1 (by rfl) ⟨1483448, by rfl⟩ : syracuseStep 1977931 = 2966897) B2966897
theorem B2503325 : Blo 1977435 2503325 := bbase (se 3 (by rfl) ⟨469373, by rfl⟩ : syracuseStep 2503325 = 938747) (by norm_num)
theorem B6675533 : Blo 1977435 6675533 := bstep (se 3 (by rfl) ⟨1251662, by rfl⟩ : syracuseStep 6675533 = 2503325) B2503325
theorem B4450355 : Blo 1977435 4450355 := bstep (se 1 (by rfl) ⟨3337766, by rfl⟩ : syracuseStep 4450355 = 6675533) B6675533
theorem B2966903 : Blo 1977435 2966903 := bstep (se 1 (by rfl) ⟨2225177, by rfl⟩ : syracuseStep 2966903 = 4450355) B4450355
theorem B1977935 : Blo 1977435 1977935 := bstep (se 1 (by rfl) ⟨1483451, by rfl⟩ : syracuseStep 1977935 = 2966903) B2966903
theorem B2966909 : Blo 1977435 2966909 := bbase (se 3 (by rfl) ⟨556295, by rfl⟩ : syracuseStep 2966909 = 1112591) (by norm_num)
theorem B1977939 : Blo 1977435 1977939 := bstep (se 1 (by rfl) ⟨1483454, by rfl⟩ : syracuseStep 1977939 = 2966909) B2966909
theorem B4450373 : Blo 1977435 4450373 := bbase (se 4 (by rfl) ⟨417222, by rfl⟩ : syracuseStep 4450373 = 834445) (by norm_num)
theorem B2966915 : Blo 1977435 2966915 := bstep (se 1 (by rfl) ⟨2225186, by rfl⟩ : syracuseStep 2966915 = 4450373) B4450373
theorem B1977943 : Blo 1977435 1977943 := bstep (se 1 (by rfl) ⟨1483457, by rfl⟩ : syracuseStep 1977943 = 2966915) B2966915
theorem B5632517 : Blo 1977435 5632517 := bbase (se 4 (by rfl) ⟨528048, by rfl⟩ : syracuseStep 5632517 = 1056097) (by norm_num)
theorem B3755011 : Blo 1977435 3755011 := bstep (se 1 (by rfl) ⟨2816258, by rfl⟩ : syracuseStep 3755011 = 5632517) B5632517
theorem B5006681 : Blo 1977435 5006681 := bstep (se 2 (by rfl) ⟨1877505, by rfl⟩ : syracuseStep 5006681 = 3755011) B3755011
theorem B3337787 : Blo 1977435 3337787 := bstep (se 1 (by rfl) ⟨2503340, by rfl⟩ : syracuseStep 3337787 = 5006681) B5006681
theorem B2225191 : Blo 1977435 2225191 := bstep (se 1 (by rfl) ⟨1668893, by rfl⟩ : syracuseStep 2225191 = 3337787) B3337787
theorem B2966921 : Blo 1977435 2966921 := bstep (se 2 (by rfl) ⟨1112595, by rfl⟩ : syracuseStep 2966921 = 2225191) B2225191
theorem B1977947 : Blo 1977435 1977947 := bstep (se 1 (by rfl) ⟨1483460, by rfl⟩ : syracuseStep 1977947 = 2966921) B2966921
theorem B10013381 : Blo 1977435 10013381 := bbase (se 4 (by rfl) ⟨938754, by rfl⟩ : syracuseStep 10013381 = 1877509) (by norm_num)
theorem B6675587 : Blo 1977435 6675587 := bstep (se 1 (by rfl) ⟨5006690, by rfl⟩ : syracuseStep 6675587 = 10013381) B10013381
theorem B4450391 : Blo 1977435 4450391 := bstep (se 1 (by rfl) ⟨3337793, by rfl⟩ : syracuseStep 4450391 = 6675587) B6675587
theorem B2966927 : Blo 1977435 2966927 := bstep (se 1 (by rfl) ⟨2225195, by rfl⟩ : syracuseStep 2966927 = 4450391) B4450391
theorem B1977951 : Blo 1977435 1977951 := bstep (se 1 (by rfl) ⟨1483463, by rfl⟩ : syracuseStep 1977951 = 2966927) B2966927
theorem B2966933 : Blo 1977435 2966933 := bbase (se 6 (by rfl) ⟨69537, by rfl⟩ : syracuseStep 2966933 = 139075) (by norm_num)
theorem B1977955 : Blo 1977435 1977955 := bstep (se 1 (by rfl) ⟨1483466, by rfl⟩ : syracuseStep 1977955 = 2966933) B2966933
theorem B4224413 : Blo 1977435 4224413 := bbase (se 3 (by rfl) ⟨792077, by rfl⟩ : syracuseStep 4224413 = 1584155) (by norm_num)
theorem B11265101 : Blo 1977435 11265101 := bstep (se 3 (by rfl) ⟨2112206, by rfl⟩ : syracuseStep 11265101 = 4224413) B4224413
theorem B7510067 : Blo 1977435 7510067 := bstep (se 1 (by rfl) ⟨5632550, by rfl⟩ : syracuseStep 7510067 = 11265101) B11265101
theorem B5006711 : Blo 1977435 5006711 := bstep (se 1 (by rfl) ⟨3755033, by rfl⟩ : syracuseStep 5006711 = 7510067) B7510067
theorem B3337807 : Blo 1977435 3337807 := bstep (se 1 (by rfl) ⟨2503355, by rfl⟩ : syracuseStep 3337807 = 5006711) B5006711
theorem B4450409 : Blo 1977435 4450409 := bstep (se 2 (by rfl) ⟨1668903, by rfl⟩ : syracuseStep 4450409 = 3337807) B3337807
theorem B2966939 : Blo 1977435 2966939 := bstep (se 1 (by rfl) ⟨2225204, by rfl⟩ : syracuseStep 2966939 = 4450409) B4450409
theorem B1977959 : Blo 1977435 1977959 := bstep (se 1 (by rfl) ⟨1483469, by rfl⟩ : syracuseStep 1977959 = 2966939) B2966939
theorem B2225209 : Blo 1977435 2225209 := bbase (se 2 (by rfl) ⟨834453, by rfl⟩ : syracuseStep 2225209 = 1668907) (by norm_num)
theorem B2966945 : Blo 1977435 2966945 := bstep (se 2 (by rfl) ⟨1112604, by rfl⟩ : syracuseStep 2966945 = 2225209) B2225209
theorem B1977963 : Blo 1977435 1977963 := bstep (se 1 (by rfl) ⟨1483472, by rfl⟩ : syracuseStep 1977963 = 2966945) B2966945
theorem B4752485 : Blo 1977435 4752485 := bbase (se 4 (by rfl) ⟨445545, by rfl⟩ : syracuseStep 4752485 = 891091) (by norm_num)
theorem B3168323 : Blo 1977435 3168323 := bstep (se 1 (by rfl) ⟨2376242, by rfl⟩ : syracuseStep 3168323 = 4752485) B4752485
theorem B2112215 : Blo 1977435 2112215 := bstep (se 1 (by rfl) ⟨1584161, by rfl⟩ : syracuseStep 2112215 = 3168323) B3168323
theorem B5632573 : Blo 1977435 5632573 := bstep (se 3 (by rfl) ⟨1056107, by rfl⟩ : syracuseStep 5632573 = 2112215) B2112215
theorem B7510097 : Blo 1977435 7510097 := bstep (se 2 (by rfl) ⟨2816286, by rfl⟩ : syracuseStep 7510097 = 5632573) B5632573
theorem B5006731 : Blo 1977435 5006731 := bstep (se 1 (by rfl) ⟨3755048, by rfl⟩ : syracuseStep 5006731 = 7510097) B7510097
theorem B6675641 : Blo 1977435 6675641 := bstep (se 2 (by rfl) ⟨2503365, by rfl⟩ : syracuseStep 6675641 = 5006731) B5006731
theorem B4450427 : Blo 1977435 4450427 := bstep (se 1 (by rfl) ⟨3337820, by rfl⟩ : syracuseStep 4450427 = 6675641) B6675641
theorem B2966951 : Blo 1977435 2966951 := bstep (se 1 (by rfl) ⟨2225213, by rfl⟩ : syracuseStep 2966951 = 4450427) B4450427
theorem B1977967 : Blo 1977435 1977967 := bstep (se 1 (by rfl) ⟨1483475, by rfl⟩ : syracuseStep 1977967 = 2966951) B2966951
theorem B2966957 : Blo 1977435 2966957 := bbase (se 3 (by rfl) ⟨556304, by rfl⟩ : syracuseStep 2966957 = 1112609) (by norm_num)
theorem B1977971 : Blo 1977435 1977971 := bstep (se 1 (by rfl) ⟨1483478, by rfl⟩ : syracuseStep 1977971 = 2966957) B2966957
theorem B4450445 : Blo 1977435 4450445 := bbase (se 3 (by rfl) ⟨834458, by rfl⟩ : syracuseStep 4450445 = 1668917) (by norm_num)
theorem B2966963 : Blo 1977435 2966963 := bstep (se 1 (by rfl) ⟨2225222, by rfl⟩ : syracuseStep 2966963 = 4450445) B4450445
theorem B1977975 : Blo 1977435 1977975 := bstep (se 1 (by rfl) ⟨1483481, by rfl⟩ : syracuseStep 1977975 = 2966963) B2966963
theorem B2503381 : Blo 1977435 2503381 := bbase (se 7 (by rfl) ⟨29336, by rfl⟩ : syracuseStep 2503381 = 58673) (by norm_num)
theorem B3337841 : Blo 1977435 3337841 := bstep (se 2 (by rfl) ⟨1251690, by rfl⟩ : syracuseStep 3337841 = 2503381) B2503381
theorem B2225227 : Blo 1977435 2225227 := bstep (se 1 (by rfl) ⟨1668920, by rfl⟩ : syracuseStep 2225227 = 3337841) B3337841
theorem B2966969 : Blo 1977435 2966969 := bstep (se 2 (by rfl) ⟨1112613, by rfl⟩ : syracuseStep 2966969 = 2225227) B2225227
theorem B1977979 : Blo 1977435 1977979 := bstep (se 1 (by rfl) ⟨1483484, by rfl⟩ : syracuseStep 1977979 = 2966969) B2966969
theorem B13718197 : Blo 1977435 13718197 := bbase (se 5 (by rfl) ⟨643040, by rfl⟩ : syracuseStep 13718197 = 1286081) (by norm_num)
theorem B18290929 : Blo 1977435 18290929 := bstep (se 2 (by rfl) ⟨6859098, by rfl⟩ : syracuseStep 18290929 = 13718197) B13718197
theorem B24387905 : Blo 1977435 24387905 := bstep (se 2 (by rfl) ⟨9145464, by rfl⟩ : syracuseStep 24387905 = 18290929) B18290929
theorem B16258603 : Blo 1977435 16258603 := bstep (se 1 (by rfl) ⟨12193952, by rfl⟩ : syracuseStep 16258603 = 24387905) B24387905
theorem B21678137 : Blo 1977435 21678137 := bstep (se 2 (by rfl) ⟨8129301, by rfl⟩ : syracuseStep 21678137 = 16258603) B16258603
theorem B14452091 : Blo 1977435 14452091 := bstep (se 1 (by rfl) ⟨10839068, by rfl⟩ : syracuseStep 14452091 = 21678137) B21678137
theorem B9634727 : Blo 1977435 9634727 := bstep (se 1 (by rfl) ⟨7226045, by rfl⟩ : syracuseStep 9634727 = 14452091) B14452091
theorem B6423151 : Blo 1977435 6423151 := bstep (se 1 (by rfl) ⟨4817363, by rfl⟩ : syracuseStep 6423151 = 9634727) B9634727
theorem B8564201 : Blo 1977435 8564201 := bstep (se 2 (by rfl) ⟨3211575, by rfl⟩ : syracuseStep 8564201 = 6423151) B6423151
theorem B5709467 : Blo 1977435 5709467 := bstep (se 1 (by rfl) ⟨4282100, by rfl⟩ : syracuseStep 5709467 = 8564201) B8564201
theorem B15225245 : Blo 1977435 15225245 := bstep (se 3 (by rfl) ⟨2854733, by rfl⟩ : syracuseStep 15225245 = 5709467) B5709467
theorem B10150163 : Blo 1977435 10150163 := bstep (se 1 (by rfl) ⟨7612622, by rfl⟩ : syracuseStep 10150163 = 15225245) B15225245
theorem B6766775 : Blo 1977435 6766775 := bstep (se 1 (by rfl) ⟨5075081, by rfl⟩ : syracuseStep 6766775 = 10150163) B10150163
theorem B4511183 : Blo 1977435 4511183 := bstep (se 1 (by rfl) ⟨3383387, by rfl⟩ : syracuseStep 4511183 = 6766775) B6766775
theorem B48119285 : Blo 1977435 48119285 := bstep (se 5 (by rfl) ⟨2255591, by rfl⟩ : syracuseStep 48119285 = 4511183) B4511183
theorem B128318093 : Blo 1977435 128318093 := bstep (se 3 (by rfl) ⟨24059642, by rfl⟩ : syracuseStep 128318093 = 48119285) B48119285
theorem B85545395 : Blo 1977435 85545395 := bstep (se 1 (by rfl) ⟨64159046, by rfl⟩ : syracuseStep 85545395 = 128318093) B128318093
theorem B57030263 : Blo 1977435 57030263 := bstep (se 1 (by rfl) ⟨42772697, by rfl⟩ : syracuseStep 57030263 = 85545395) B85545395
theorem B38020175 : Blo 1977435 38020175 := bstep (se 1 (by rfl) ⟨28515131, by rfl⟩ : syracuseStep 38020175 = 57030263) B57030263
theorem B25346783 : Blo 1977435 25346783 := bstep (se 1 (by rfl) ⟨19010087, by rfl⟩ : syracuseStep 25346783 = 38020175) B38020175
theorem B16897855 : Blo 1977435 16897855 := bstep (se 1 (by rfl) ⟨12673391, by rfl⟩ : syracuseStep 16897855 = 25346783) B25346783
theorem B22530473 : Blo 1977435 22530473 := bstep (se 2 (by rfl) ⟨8448927, by rfl⟩ : syracuseStep 22530473 = 16897855) B16897855
theorem B15020315 : Blo 1977435 15020315 := bstep (se 1 (by rfl) ⟨11265236, by rfl⟩ : syracuseStep 15020315 = 22530473) B22530473
theorem B10013543 : Blo 1977435 10013543 := bstep (se 1 (by rfl) ⟨7510157, by rfl⟩ : syracuseStep 10013543 = 15020315) B15020315
theorem B6675695 : Blo 1977435 6675695 := bstep (se 1 (by rfl) ⟨5006771, by rfl⟩ : syracuseStep 6675695 = 10013543) B10013543
theorem B4450463 : Blo 1977435 4450463 := bstep (se 1 (by rfl) ⟨3337847, by rfl⟩ : syracuseStep 4450463 = 6675695) B6675695
theorem B2966975 : Blo 1977435 2966975 := bstep (se 1 (by rfl) ⟨2225231, by rfl⟩ : syracuseStep 2966975 = 4450463) B4450463
theorem B1977983 : Blo 1977435 1977983 := bstep (se 1 (by rfl) ⟨1483487, by rfl⟩ : syracuseStep 1977983 = 2966975) B2966975
theorem B2966981 : Blo 1977435 2966981 := bbase (se 4 (by rfl) ⟨278154, by rfl⟩ : syracuseStep 2966981 = 556309) (by norm_num)
theorem B1977987 : Blo 1977435 1977987 := bstep (se 1 (by rfl) ⟨1483490, by rfl⟩ : syracuseStep 1977987 = 2966981) B2966981
theorem B3337861 : Blo 1977435 3337861 := bbase (se 4 (by rfl) ⟨312924, by rfl⟩ : syracuseStep 3337861 = 625849) (by norm_num)
theorem B4450481 : Blo 1977435 4450481 := bstep (se 2 (by rfl) ⟨1668930, by rfl⟩ : syracuseStep 4450481 = 3337861) B3337861
theorem B2966987 : Blo 1977435 2966987 := bstep (se 1 (by rfl) ⟨2225240, by rfl⟩ : syracuseStep 2966987 = 4450481) B4450481
theorem B1977991 : Blo 1977435 1977991 := bstep (se 1 (by rfl) ⟨1483493, by rfl⟩ : syracuseStep 1977991 = 2966987) B2966987
theorem B2225245 : Blo 1977435 2225245 := bbase (se 3 (by rfl) ⟨417233, by rfl⟩ : syracuseStep 2225245 = 834467) (by norm_num)
theorem B2966993 : Blo 1977435 2966993 := bstep (se 2 (by rfl) ⟨1112622, by rfl⟩ : syracuseStep 2966993 = 2225245) B2225245
theorem B1977995 : Blo 1977435 1977995 := bstep (se 1 (by rfl) ⟨1483496, by rfl⟩ : syracuseStep 1977995 = 2966993) B2966993
theorem B6675749 : Blo 1977435 6675749 := bbase (se 4 (by rfl) ⟨625851, by rfl⟩ : syracuseStep 6675749 = 1251703) (by norm_num)
theorem B4450499 : Blo 1977435 4450499 := bstep (se 1 (by rfl) ⟨3337874, by rfl⟩ : syracuseStep 4450499 = 6675749) B6675749
theorem B2966999 : Blo 1977435 2966999 := bstep (se 1 (by rfl) ⟨2225249, by rfl⟩ : syracuseStep 2966999 = 4450499) B4450499
theorem B1977999 : Blo 1977435 1977999 := bstep (se 1 (by rfl) ⟨1483499, by rfl⟩ : syracuseStep 1977999 = 2966999) B2966999
theorem B2967005 : Blo 1977435 2967005 := bbase (se 3 (by rfl) ⟨556313, by rfl⟩ : syracuseStep 2967005 = 1112627) (by norm_num)
theorem B1978003 : Blo 1977435 1978003 := bstep (se 1 (by rfl) ⟨1483502, by rfl⟩ : syracuseStep 1978003 = 2967005) B2967005
theorem B4450517 : Blo 1977435 4450517 := bbase (se 7 (by rfl) ⟨52154, by rfl⟩ : syracuseStep 4450517 = 104309) (by norm_num)
theorem B2967011 : Blo 1977435 2967011 := bstep (se 1 (by rfl) ⟨2225258, by rfl⟩ : syracuseStep 2967011 = 4450517) B4450517
theorem B1978007 : Blo 1977435 1978007 := bstep (se 1 (by rfl) ⟨1483505, by rfl⟩ : syracuseStep 1978007 = 2967011) B2967011
theorem B13533749 : Blo 1977435 13533749 := bbase (se 5 (by rfl) ⟨634394, by rfl⟩ : syracuseStep 13533749 = 1268789) (by norm_num)
theorem B9022499 : Blo 1977435 9022499 := bstep (se 1 (by rfl) ⟨6766874, by rfl⟩ : syracuseStep 9022499 = 13533749) B13533749
theorem B6014999 : Blo 1977435 6014999 := bstep (se 1 (by rfl) ⟨4511249, by rfl⟩ : syracuseStep 6014999 = 9022499) B9022499
theorem B4009999 : Blo 1977435 4009999 := bstep (se 1 (by rfl) ⟨3007499, by rfl⟩ : syracuseStep 4009999 = 6014999) B6014999
theorem B5346665 : Blo 1977435 5346665 := bstep (se 2 (by rfl) ⟨2004999, by rfl⟩ : syracuseStep 5346665 = 4009999) B4009999
theorem B3564443 : Blo 1977435 3564443 := bstep (se 1 (by rfl) ⟨2673332, by rfl⟩ : syracuseStep 3564443 = 5346665) B5346665
theorem B9505181 : Blo 1977435 9505181 := bstep (se 3 (by rfl) ⟨1782221, by rfl⟩ : syracuseStep 9505181 = 3564443) B3564443
theorem B6336787 : Blo 1977435 6336787 := bstep (se 1 (by rfl) ⟨4752590, by rfl⟩ : syracuseStep 6336787 = 9505181) B9505181
theorem B8449049 : Blo 1977435 8449049 := bstep (se 2 (by rfl) ⟨3168393, by rfl⟩ : syracuseStep 8449049 = 6336787) B6336787
theorem B5632699 : Blo 1977435 5632699 := bstep (se 1 (by rfl) ⟨4224524, by rfl⟩ : syracuseStep 5632699 = 8449049) B8449049
theorem B7510265 : Blo 1977435 7510265 := bstep (se 2 (by rfl) ⟨2816349, by rfl⟩ : syracuseStep 7510265 = 5632699) B5632699
theorem B5006843 : Blo 1977435 5006843 := bstep (se 1 (by rfl) ⟨3755132, by rfl⟩ : syracuseStep 5006843 = 7510265) B7510265
theorem B3337895 : Blo 1977435 3337895 := bstep (se 1 (by rfl) ⟨2503421, by rfl⟩ : syracuseStep 3337895 = 5006843) B5006843
theorem B2225263 : Blo 1977435 2225263 := bstep (se 1 (by rfl) ⟨1668947, by rfl⟩ : syracuseStep 2225263 = 3337895) B3337895
theorem B2967017 : Blo 1977435 2967017 := bstep (se 2 (by rfl) ⟨1112631, by rfl⟩ : syracuseStep 2967017 = 2225263) B2225263
theorem B1978011 : Blo 1977435 1978011 := bstep (se 1 (by rfl) ⟨1483508, by rfl⟩ : syracuseStep 1978011 = 2967017) B2967017
theorem B2255629 : Blo 1977435 2255629 := bbase (se 3 (by rfl) ⟨422930, by rfl⟩ : syracuseStep 2255629 = 845861) (by norm_num)
theorem B3007505 : Blo 1977435 3007505 := bstep (se 2 (by rfl) ⟨1127814, by rfl⟩ : syracuseStep 3007505 = 2255629) B2255629
theorem B2005003 : Blo 1977435 2005003 := bstep (se 1 (by rfl) ⟨1503752, by rfl⟩ : syracuseStep 2005003 = 3007505) B3007505
theorem B10693349 : Blo 1977435 10693349 := bstep (se 4 (by rfl) ⟨1002501, by rfl⟩ : syracuseStep 10693349 = 2005003) B2005003
theorem B7128899 : Blo 1977435 7128899 := bstep (se 1 (by rfl) ⟨5346674, by rfl⟩ : syracuseStep 7128899 = 10693349) B10693349
theorem B4752599 : Blo 1977435 4752599 := bstep (se 1 (by rfl) ⟨3564449, by rfl⟩ : syracuseStep 4752599 = 7128899) B7128899
theorem B12673597 : Blo 1977435 12673597 := bstep (se 3 (by rfl) ⟨2376299, by rfl⟩ : syracuseStep 12673597 = 4752599) B4752599
theorem B16898129 : Blo 1977435 16898129 := bstep (se 2 (by rfl) ⟨6336798, by rfl⟩ : syracuseStep 16898129 = 12673597) B12673597
theorem B11265419 : Blo 1977435 11265419 := bstep (se 1 (by rfl) ⟨8449064, by rfl⟩ : syracuseStep 11265419 = 16898129) B16898129
theorem B7510279 : Blo 1977435 7510279 := bstep (se 1 (by rfl) ⟨5632709, by rfl⟩ : syracuseStep 7510279 = 11265419) B11265419
theorem B10013705 : Blo 1977435 10013705 := bstep (se 2 (by rfl) ⟨3755139, by rfl⟩ : syracuseStep 10013705 = 7510279) B7510279
theorem B6675803 : Blo 1977435 6675803 := bstep (se 1 (by rfl) ⟨5006852, by rfl⟩ : syracuseStep 6675803 = 10013705) B10013705
theorem B4450535 : Blo 1977435 4450535 := bstep (se 1 (by rfl) ⟨3337901, by rfl⟩ : syracuseStep 4450535 = 6675803) B6675803
theorem B2967023 : Blo 1977435 2967023 := bstep (se 1 (by rfl) ⟨2225267, by rfl⟩ : syracuseStep 2967023 = 4450535) B4450535
theorem B1978015 : Blo 1977435 1978015 := bstep (se 1 (by rfl) ⟨1483511, by rfl⟩ : syracuseStep 1978015 = 2967023) B2967023
theorem B2967029 : Blo 1977435 2967029 := bbase (se 5 (by rfl) ⟨139079, by rfl⟩ : syracuseStep 2967029 = 278159) (by norm_num)
theorem B1978019 : Blo 1977435 1978019 := bstep (se 1 (by rfl) ⟨1483514, by rfl⟩ : syracuseStep 1978019 = 2967029) B2967029
theorem B3168413 : Blo 1977435 3168413 := bbase (se 3 (by rfl) ⟨594077, by rfl⟩ : syracuseStep 3168413 = 1188155) (by norm_num)
theorem B2112275 : Blo 1977435 2112275 := bstep (se 1 (by rfl) ⟨1584206, by rfl⟩ : syracuseStep 2112275 = 3168413) B3168413
theorem B5632733 : Blo 1977435 5632733 := bstep (se 3 (by rfl) ⟨1056137, by rfl⟩ : syracuseStep 5632733 = 2112275) B2112275
theorem B3755155 : Blo 1977435 3755155 := bstep (se 1 (by rfl) ⟨2816366, by rfl⟩ : syracuseStep 3755155 = 5632733) B5632733
theorem B5006873 : Blo 1977435 5006873 := bstep (se 2 (by rfl) ⟨1877577, by rfl⟩ : syracuseStep 5006873 = 3755155) B3755155
theorem B3337915 : Blo 1977435 3337915 := bstep (se 1 (by rfl) ⟨2503436, by rfl⟩ : syracuseStep 3337915 = 5006873) B5006873
theorem B4450553 : Blo 1977435 4450553 := bstep (se 2 (by rfl) ⟨1668957, by rfl⟩ : syracuseStep 4450553 = 3337915) B3337915
theorem B2967035 : Blo 1977435 2967035 := bstep (se 1 (by rfl) ⟨2225276, by rfl⟩ : syracuseStep 2967035 = 4450553) B4450553
theorem B1978023 : Blo 1977435 1978023 := bstep (se 1 (by rfl) ⟨1483517, by rfl⟩ : syracuseStep 1978023 = 2967035) B2967035
theorem B2225281 : Blo 1977435 2225281 := bbase (se 2 (by rfl) ⟨834480, by rfl⟩ : syracuseStep 2225281 = 1668961) (by norm_num)
theorem B2967041 : Blo 1977435 2967041 := bstep (se 2 (by rfl) ⟨1112640, by rfl⟩ : syracuseStep 2967041 = 2225281) B2225281
theorem B1978027 : Blo 1977435 1978027 := bstep (se 1 (by rfl) ⟨1483520, by rfl⟩ : syracuseStep 1978027 = 2967041) B2967041
theorem B5006893 : Blo 1977435 5006893 := bbase (se 3 (by rfl) ⟨938792, by rfl⟩ : syracuseStep 5006893 = 1877585) (by norm_num)
theorem B6675857 : Blo 1977435 6675857 := bstep (se 2 (by rfl) ⟨2503446, by rfl⟩ : syracuseStep 6675857 = 5006893) B5006893
theorem B4450571 : Blo 1977435 4450571 := bstep (se 1 (by rfl) ⟨3337928, by rfl⟩ : syracuseStep 4450571 = 6675857) B6675857
theorem B2967047 : Blo 1977435 2967047 := bstep (se 1 (by rfl) ⟨2225285, by rfl⟩ : syracuseStep 2967047 = 4450571) B4450571
theorem B1978031 : Blo 1977435 1978031 := bstep (se 1 (by rfl) ⟨1483523, by rfl⟩ : syracuseStep 1978031 = 2967047) B2967047
theorem B2967053 : Blo 1977435 2967053 := bbase (se 3 (by rfl) ⟨556322, by rfl⟩ : syracuseStep 2967053 = 1112645) (by norm_num)
theorem B1978035 : Blo 1977435 1978035 := bstep (se 1 (by rfl) ⟨1483526, by rfl⟩ : syracuseStep 1978035 = 2967053) B2967053
theorem B4450589 : Blo 1977435 4450589 := bbase (se 3 (by rfl) ⟨834485, by rfl⟩ : syracuseStep 4450589 = 1668971) (by norm_num)
theorem B2967059 : Blo 1977435 2967059 := bstep (se 1 (by rfl) ⟨2225294, by rfl⟩ : syracuseStep 2967059 = 4450589) B4450589
theorem B1978039 : Blo 1977435 1978039 := bstep (se 1 (by rfl) ⟨1483529, by rfl⟩ : syracuseStep 1978039 = 2967059) B2967059
theorem B3337949 : Blo 1977435 3337949 := bbase (se 3 (by rfl) ⟨625865, by rfl⟩ : syracuseStep 3337949 = 1251731) (by norm_num)
theorem B2225299 : Blo 1977435 2225299 := bstep (se 1 (by rfl) ⟨1668974, by rfl⟩ : syracuseStep 2225299 = 3337949) B3337949
theorem B2967065 : Blo 1977435 2967065 := bstep (se 2 (by rfl) ⟨1112649, by rfl⟩ : syracuseStep 2967065 = 2225299) B2225299
theorem B1978043 : Blo 1977435 1978043 := bstep (se 1 (by rfl) ⟨1483532, by rfl⟩ : syracuseStep 1978043 = 2967065) B2967065
theorem B6336901 : Blo 1977435 6336901 := bbase (se 4 (by rfl) ⟨594084, by rfl⟩ : syracuseStep 6336901 = 1188169) (by norm_num)
theorem B8449201 : Blo 1977435 8449201 := bstep (se 2 (by rfl) ⟨3168450, by rfl⟩ : syracuseStep 8449201 = 6336901) B6336901
theorem B11265601 : Blo 1977435 11265601 := bstep (se 2 (by rfl) ⟨4224600, by rfl⟩ : syracuseStep 11265601 = 8449201) B8449201
theorem B15020801 : Blo 1977435 15020801 := bstep (se 2 (by rfl) ⟨5632800, by rfl⟩ : syracuseStep 15020801 = 11265601) B11265601
theorem B10013867 : Blo 1977435 10013867 := bstep (se 1 (by rfl) ⟨7510400, by rfl⟩ : syracuseStep 10013867 = 15020801) B15020801
theorem B6675911 : Blo 1977435 6675911 := bstep (se 1 (by rfl) ⟨5006933, by rfl⟩ : syracuseStep 6675911 = 10013867) B10013867
theorem B4450607 : Blo 1977435 4450607 := bstep (se 1 (by rfl) ⟨3337955, by rfl⟩ : syracuseStep 4450607 = 6675911) B6675911
theorem B2967071 : Blo 1977435 2967071 := bstep (se 1 (by rfl) ⟨2225303, by rfl⟩ : syracuseStep 2967071 = 4450607) B4450607
theorem B1978047 : Blo 1977435 1978047 := bstep (se 1 (by rfl) ⟨1483535, by rfl⟩ : syracuseStep 1978047 = 2967071) B2967071
theorem B2967077 : Blo 1977435 2967077 := bbase (se 4 (by rfl) ⟨278163, by rfl⟩ : syracuseStep 2967077 = 556327) (by norm_num)
theorem B1978051 : Blo 1977435 1978051 := bstep (se 1 (by rfl) ⟨1483538, by rfl⟩ : syracuseStep 1978051 = 2967077) B2967077
theorem B2503477 : Blo 1977435 2503477 := bbase (se 5 (by rfl) ⟨117350, by rfl⟩ : syracuseStep 2503477 = 234701) (by norm_num)
theorem B3337969 : Blo 1977435 3337969 := bstep (se 2 (by rfl) ⟨1251738, by rfl⟩ : syracuseStep 3337969 = 2503477) B2503477
theorem B4450625 : Blo 1977435 4450625 := bstep (se 2 (by rfl) ⟨1668984, by rfl⟩ : syracuseStep 4450625 = 3337969) B3337969
theorem B2967083 : Blo 1977435 2967083 := bstep (se 1 (by rfl) ⟨2225312, by rfl⟩ : syracuseStep 2967083 = 4450625) B4450625
theorem B1978055 : Blo 1977435 1978055 := bstep (se 1 (by rfl) ⟨1483541, by rfl⟩ : syracuseStep 1978055 = 2967083) B2967083
theorem B2225317 : Blo 1977435 2225317 := bbase (se 4 (by rfl) ⟨208623, by rfl⟩ : syracuseStep 2225317 = 417247) (by norm_num)
theorem B2967089 : Blo 1977435 2967089 := bstep (se 2 (by rfl) ⟨1112658, by rfl⟩ : syracuseStep 2967089 = 2225317) B2225317
theorem B1978059 : Blo 1977435 1978059 := bstep (se 1 (by rfl) ⟨1483544, by rfl⟩ : syracuseStep 1978059 = 2967089) B2967089
theorem B5346805 : Blo 1977435 5346805 := bbase (se 5 (by rfl) ⟨250631, by rfl⟩ : syracuseStep 5346805 = 501263) (by norm_num)
theorem B7129073 : Blo 1977435 7129073 := bstep (se 2 (by rfl) ⟨2673402, by rfl⟩ : syracuseStep 7129073 = 5346805) B5346805
theorem B19010861 : Blo 1977435 19010861 := bstep (se 3 (by rfl) ⟨3564536, by rfl⟩ : syracuseStep 19010861 = 7129073) B7129073
theorem B12673907 : Blo 1977435 12673907 := bstep (se 1 (by rfl) ⟨9505430, by rfl⟩ : syracuseStep 12673907 = 19010861) B19010861
theorem B8449271 : Blo 1977435 8449271 := bstep (se 1 (by rfl) ⟨6336953, by rfl⟩ : syracuseStep 8449271 = 12673907) B12673907
theorem B5632847 : Blo 1977435 5632847 := bstep (se 1 (by rfl) ⟨4224635, by rfl⟩ : syracuseStep 5632847 = 8449271) B8449271
theorem B3755231 : Blo 1977435 3755231 := bstep (se 1 (by rfl) ⟨2816423, by rfl⟩ : syracuseStep 3755231 = 5632847) B5632847
theorem B2503487 : Blo 1977435 2503487 := bstep (se 1 (by rfl) ⟨1877615, by rfl⟩ : syracuseStep 2503487 = 3755231) B3755231
theorem B6675965 : Blo 1977435 6675965 := bstep (se 3 (by rfl) ⟨1251743, by rfl⟩ : syracuseStep 6675965 = 2503487) B2503487
theorem B4450643 : Blo 1977435 4450643 := bstep (se 1 (by rfl) ⟨3337982, by rfl⟩ : syracuseStep 4450643 = 6675965) B6675965
theorem B2967095 : Blo 1977435 2967095 := bstep (se 1 (by rfl) ⟨2225321, by rfl⟩ : syracuseStep 2967095 = 4450643) B4450643
theorem B1978063 : Blo 1977435 1978063 := bstep (se 1 (by rfl) ⟨1483547, by rfl⟩ : syracuseStep 1978063 = 2967095) B2967095
theorem B2967101 : Blo 1977435 2967101 := bbase (se 3 (by rfl) ⟨556331, by rfl⟩ : syracuseStep 2967101 = 1112663) (by norm_num)
theorem B1978067 : Blo 1977435 1978067 := bstep (se 1 (by rfl) ⟨1483550, by rfl⟩ : syracuseStep 1978067 = 2967101) B2967101
theorem B4450661 : Blo 1977435 4450661 := bbase (se 4 (by rfl) ⟨417249, by rfl⟩ : syracuseStep 4450661 = 834499) (by norm_num)
theorem B2967107 : Blo 1977435 2967107 := bstep (se 1 (by rfl) ⟨2225330, by rfl⟩ : syracuseStep 2967107 = 4450661) B4450661
theorem B1978071 : Blo 1977435 1978071 := bstep (se 1 (by rfl) ⟨1483553, by rfl⟩ : syracuseStep 1978071 = 2967107) B2967107
theorem B5007005 : Blo 1977435 5007005 := bbase (se 3 (by rfl) ⟨938813, by rfl⟩ : syracuseStep 5007005 = 1877627) (by norm_num)
theorem B3338003 : Blo 1977435 3338003 := bstep (se 1 (by rfl) ⟨2503502, by rfl⟩ : syracuseStep 3338003 = 5007005) B5007005
theorem B2225335 : Blo 1977435 2225335 := bstep (se 1 (by rfl) ⟨1669001, by rfl⟩ : syracuseStep 2225335 = 3338003) B3338003
theorem B2967113 : Blo 1977435 2967113 := bstep (se 2 (by rfl) ⟨1112667, by rfl⟩ : syracuseStep 2967113 = 2225335) B2225335
theorem B1978075 : Blo 1977435 1978075 := bstep (se 1 (by rfl) ⟨1483556, by rfl⟩ : syracuseStep 1978075 = 2967113) B2967113
theorem B3755261 : Blo 1977435 3755261 := bbase (se 3 (by rfl) ⟨704111, by rfl⟩ : syracuseStep 3755261 = 1408223) (by norm_num)
theorem B10014029 : Blo 1977435 10014029 := bstep (se 3 (by rfl) ⟨1877630, by rfl⟩ : syracuseStep 10014029 = 3755261) B3755261
theorem B6676019 : Blo 1977435 6676019 := bstep (se 1 (by rfl) ⟨5007014, by rfl⟩ : syracuseStep 6676019 = 10014029) B10014029
theorem B4450679 : Blo 1977435 4450679 := bstep (se 1 (by rfl) ⟨3338009, by rfl⟩ : syracuseStep 4450679 = 6676019) B6676019
theorem B2967119 : Blo 1977435 2967119 := bstep (se 1 (by rfl) ⟨2225339, by rfl⟩ : syracuseStep 2967119 = 4450679) B4450679
theorem B1978079 : Blo 1977435 1978079 := bstep (se 1 (by rfl) ⟨1483559, by rfl⟩ : syracuseStep 1978079 = 2967119) B2967119
theorem B2967125 : Blo 1977435 2967125 := bbase (se 8 (by rfl) ⟨17385, by rfl⟩ : syracuseStep 2967125 = 34771) (by norm_num)
theorem B1978083 : Blo 1977435 1978083 := bstep (se 1 (by rfl) ⟨1483562, by rfl⟩ : syracuseStep 1978083 = 2967125) B2967125
theorem B4752773 : Blo 1977435 4752773 := bbase (se 4 (by rfl) ⟨445572, by rfl⟩ : syracuseStep 4752773 = 891145) (by norm_num)
theorem B3168515 : Blo 1977435 3168515 := bstep (se 1 (by rfl) ⟨2376386, by rfl⟩ : syracuseStep 3168515 = 4752773) B4752773
theorem B8449373 : Blo 1977435 8449373 := bstep (se 3 (by rfl) ⟨1584257, by rfl⟩ : syracuseStep 8449373 = 3168515) B3168515
theorem B5632915 : Blo 1977435 5632915 := bstep (se 1 (by rfl) ⟨4224686, by rfl⟩ : syracuseStep 5632915 = 8449373) B8449373
theorem B7510553 : Blo 1977435 7510553 := bstep (se 2 (by rfl) ⟨2816457, by rfl⟩ : syracuseStep 7510553 = 5632915) B5632915
theorem B5007035 : Blo 1977435 5007035 := bstep (se 1 (by rfl) ⟨3755276, by rfl⟩ : syracuseStep 5007035 = 7510553) B7510553
theorem B3338023 : Blo 1977435 3338023 := bstep (se 1 (by rfl) ⟨2503517, by rfl⟩ : syracuseStep 3338023 = 5007035) B5007035
theorem B4450697 : Blo 1977435 4450697 := bstep (se 2 (by rfl) ⟨1669011, by rfl⟩ : syracuseStep 4450697 = 3338023) B3338023
theorem B2967131 : Blo 1977435 2967131 := bstep (se 1 (by rfl) ⟨2225348, by rfl⟩ : syracuseStep 2967131 = 4450697) B4450697
theorem B1978087 : Blo 1977435 1978087 := bstep (se 1 (by rfl) ⟨1483565, by rfl⟩ : syracuseStep 1978087 = 2967131) B2967131
theorem B2225353 : Blo 1977435 2225353 := bbase (se 2 (by rfl) ⟨834507, by rfl⟩ : syracuseStep 2225353 = 1669015) (by norm_num)
theorem B2967137 : Blo 1977435 2967137 := bstep (se 2 (by rfl) ⟨1112676, by rfl⟩ : syracuseStep 2967137 = 2225353) B2225353
theorem B1978091 : Blo 1977435 1978091 := bstep (se 1 (by rfl) ⟨1483568, by rfl⟩ : syracuseStep 1978091 = 2967137) B2967137
theorem B3048661 : Blo 1977435 3048661 := bbase (se 7 (by rfl) ⟨35726, by rfl⟩ : syracuseStep 3048661 = 71453) (by norm_num)
theorem B16259525 : Blo 1977435 16259525 := bstep (se 4 (by rfl) ⟨1524330, by rfl⟩ : syracuseStep 16259525 = 3048661) B3048661
theorem B10839683 : Blo 1977435 10839683 := bstep (se 1 (by rfl) ⟨8129762, by rfl⟩ : syracuseStep 10839683 = 16259525) B16259525
theorem B28905821 : Blo 1977435 28905821 := bstep (se 3 (by rfl) ⟨5419841, by rfl⟩ : syracuseStep 28905821 = 10839683) B10839683
theorem B19270547 : Blo 1977435 19270547 := bstep (se 1 (by rfl) ⟨14452910, by rfl⟩ : syracuseStep 19270547 = 28905821) B28905821
theorem B12847031 : Blo 1977435 12847031 := bstep (se 1 (by rfl) ⟨9635273, by rfl⟩ : syracuseStep 12847031 = 19270547) B19270547
theorem B8564687 : Blo 1977435 8564687 := bstep (se 1 (by rfl) ⟨6423515, by rfl⟩ : syracuseStep 8564687 = 12847031) B12847031
theorem B5709791 : Blo 1977435 5709791 := bstep (se 1 (by rfl) ⟨4282343, by rfl⟩ : syracuseStep 5709791 = 8564687) B8564687
theorem B15226109 : Blo 1977435 15226109 := bstep (se 3 (by rfl) ⟨2854895, by rfl⟩ : syracuseStep 15226109 = 5709791) B5709791
theorem B10150739 : Blo 1977435 10150739 := bstep (se 1 (by rfl) ⟨7613054, by rfl⟩ : syracuseStep 10150739 = 15226109) B15226109
theorem B6767159 : Blo 1977435 6767159 := bstep (se 1 (by rfl) ⟨5075369, by rfl⟩ : syracuseStep 6767159 = 10150739) B10150739
theorem B18045757 : Blo 1977435 18045757 := bstep (se 3 (by rfl) ⟨3383579, by rfl⟩ : syracuseStep 18045757 = 6767159) B6767159
theorem B24061009 : Blo 1977435 24061009 := bstep (se 2 (by rfl) ⟨9022878, by rfl⟩ : syracuseStep 24061009 = 18045757) B18045757
theorem B32081345 : Blo 1977435 32081345 := bstep (se 2 (by rfl) ⟨12030504, by rfl⟩ : syracuseStep 32081345 = 24061009) B24061009
theorem B21387563 : Blo 1977435 21387563 := bstep (se 1 (by rfl) ⟨16040672, by rfl⟩ : syracuseStep 21387563 = 32081345) B32081345
theorem B14258375 : Blo 1977435 14258375 := bstep (se 1 (by rfl) ⟨10693781, by rfl⟩ : syracuseStep 14258375 = 21387563) B21387563
theorem B9505583 : Blo 1977435 9505583 := bstep (se 1 (by rfl) ⟨7129187, by rfl⟩ : syracuseStep 9505583 = 14258375) B14258375
theorem B6337055 : Blo 1977435 6337055 := bstep (se 1 (by rfl) ⟨4752791, by rfl⟩ : syracuseStep 6337055 = 9505583) B9505583
theorem B16898813 : Blo 1977435 16898813 := bstep (se 3 (by rfl) ⟨3168527, by rfl⟩ : syracuseStep 16898813 = 6337055) B6337055
theorem B11265875 : Blo 1977435 11265875 := bstep (se 1 (by rfl) ⟨8449406, by rfl⟩ : syracuseStep 11265875 = 16898813) B16898813
theorem B7510583 : Blo 1977435 7510583 := bstep (se 1 (by rfl) ⟨5632937, by rfl⟩ : syracuseStep 7510583 = 11265875) B11265875
theorem B5007055 : Blo 1977435 5007055 := bstep (se 1 (by rfl) ⟨3755291, by rfl⟩ : syracuseStep 5007055 = 7510583) B7510583
theorem B6676073 : Blo 1977435 6676073 := bstep (se 2 (by rfl) ⟨2503527, by rfl⟩ : syracuseStep 6676073 = 5007055) B5007055
theorem B4450715 : Blo 1977435 4450715 := bstep (se 1 (by rfl) ⟨3338036, by rfl⟩ : syracuseStep 4450715 = 6676073) B6676073
theorem B2967143 : Blo 1977435 2967143 := bstep (se 1 (by rfl) ⟨2225357, by rfl⟩ : syracuseStep 2967143 = 4450715) B4450715
theorem B1978095 : Blo 1977435 1978095 := bstep (se 1 (by rfl) ⟨1483571, by rfl⟩ : syracuseStep 1978095 = 2967143) B2967143
theorem B2967149 : Blo 1977435 2967149 := bbase (se 3 (by rfl) ⟨556340, by rfl⟩ : syracuseStep 2967149 = 1112681) (by norm_num)
theorem B1978099 : Blo 1977435 1978099 := bstep (se 1 (by rfl) ⟨1483574, by rfl⟩ : syracuseStep 1978099 = 2967149) B2967149
theorem B4450733 : Blo 1977435 4450733 := bbase (se 3 (by rfl) ⟨834512, by rfl⟩ : syracuseStep 4450733 = 1669025) (by norm_num)
theorem B2967155 : Blo 1977435 2967155 := bstep (se 1 (by rfl) ⟨2225366, by rfl⟩ : syracuseStep 2967155 = 4450733) B4450733
theorem B1978103 : Blo 1977435 1978103 := bstep (se 1 (by rfl) ⟨1483577, by rfl⟩ : syracuseStep 1978103 = 2967155) B2967155
theorem B2112365 : Blo 1977435 2112365 := bbase (se 3 (by rfl) ⟨396068, by rfl⟩ : syracuseStep 2112365 = 792137) (by norm_num)
theorem B5632973 : Blo 1977435 5632973 := bstep (se 3 (by rfl) ⟨1056182, by rfl⟩ : syracuseStep 5632973 = 2112365) B2112365
theorem B3755315 : Blo 1977435 3755315 := bstep (se 1 (by rfl) ⟨2816486, by rfl⟩ : syracuseStep 3755315 = 5632973) B5632973
theorem B2503543 : Blo 1977435 2503543 := bstep (se 1 (by rfl) ⟨1877657, by rfl⟩ : syracuseStep 2503543 = 3755315) B3755315
theorem B3338057 : Blo 1977435 3338057 := bstep (se 2 (by rfl) ⟨1251771, by rfl⟩ : syracuseStep 3338057 = 2503543) B2503543
theorem B2225371 : Blo 1977435 2225371 := bstep (se 1 (by rfl) ⟨1669028, by rfl⟩ : syracuseStep 2225371 = 3338057) B3338057
theorem B2967161 : Blo 1977435 2967161 := bstep (se 2 (by rfl) ⟨1112685, by rfl⟩ : syracuseStep 2967161 = 2225371) B2225371
theorem B1978107 : Blo 1977435 1978107 := bstep (se 1 (by rfl) ⟨1483580, by rfl⟩ : syracuseStep 1978107 = 2967161) B2967161
theorem B2408837 : Blo 1977435 2408837 := bbase (se 4 (by rfl) ⟨225828, by rfl⟩ : syracuseStep 2408837 = 451657) (by norm_num)
theorem B6423565 : Blo 1977435 6423565 := bstep (se 3 (by rfl) ⟨1204418, by rfl⟩ : syracuseStep 6423565 = 2408837) B2408837
theorem B137036053 : Blo 1977435 137036053 := bstep (se 6 (by rfl) ⟨3211782, by rfl⟩ : syracuseStep 137036053 = 6423565) B6423565
theorem B182714737 : Blo 1977435 182714737 := bstep (se 2 (by rfl) ⟨68518026, by rfl⟩ : syracuseStep 182714737 = 137036053) B137036053
theorem B243619649 : Blo 1977435 243619649 := bstep (se 2 (by rfl) ⟨91357368, by rfl⟩ : syracuseStep 243619649 = 182714737) B182714737
theorem B162413099 : Blo 1977435 162413099 := bstep (se 1 (by rfl) ⟨121809824, by rfl⟩ : syracuseStep 162413099 = 243619649) B243619649
theorem B108275399 : Blo 1977435 108275399 := bstep (se 1 (by rfl) ⟨81206549, by rfl⟩ : syracuseStep 108275399 = 162413099) B162413099
theorem B72183599 : Blo 1977435 72183599 := bstep (se 1 (by rfl) ⟨54137699, by rfl⟩ : syracuseStep 72183599 = 108275399) B108275399
theorem B48122399 : Blo 1977435 48122399 := bstep (se 1 (by rfl) ⟨36091799, by rfl⟩ : syracuseStep 48122399 = 72183599) B72183599
theorem B32081599 : Blo 1977435 32081599 := bstep (se 1 (by rfl) ⟨24061199, by rfl⟩ : syracuseStep 32081599 = 48122399) B48122399
theorem B42775465 : Blo 1977435 42775465 := bstep (se 2 (by rfl) ⟨16040799, by rfl⟩ : syracuseStep 42775465 = 32081599) B32081599
theorem B57033953 : Blo 1977435 57033953 := bstep (se 2 (by rfl) ⟨21387732, by rfl⟩ : syracuseStep 57033953 = 42775465) B42775465
theorem B38022635 : Blo 1977435 38022635 := bstep (se 1 (by rfl) ⟨28516976, by rfl⟩ : syracuseStep 38022635 = 57033953) B57033953
theorem B25348423 : Blo 1977435 25348423 := bstep (se 1 (by rfl) ⟨19011317, by rfl⟩ : syracuseStep 25348423 = 38022635) B38022635
theorem B33797897 : Blo 1977435 33797897 := bstep (se 2 (by rfl) ⟨12674211, by rfl⟩ : syracuseStep 33797897 = 25348423) B25348423
theorem B22531931 : Blo 1977435 22531931 := bstep (se 1 (by rfl) ⟨16898948, by rfl⟩ : syracuseStep 22531931 = 33797897) B33797897
theorem B15021287 : Blo 1977435 15021287 := bstep (se 1 (by rfl) ⟨11265965, by rfl⟩ : syracuseStep 15021287 = 22531931) B22531931
theorem B10014191 : Blo 1977435 10014191 := bstep (se 1 (by rfl) ⟨7510643, by rfl⟩ : syracuseStep 10014191 = 15021287) B15021287
theorem B6676127 : Blo 1977435 6676127 := bstep (se 1 (by rfl) ⟨5007095, by rfl⟩ : syracuseStep 6676127 = 10014191) B10014191
theorem B4450751 : Blo 1977435 4450751 := bstep (se 1 (by rfl) ⟨3338063, by rfl⟩ : syracuseStep 4450751 = 6676127) B6676127
theorem B2967167 : Blo 1977435 2967167 := bstep (se 1 (by rfl) ⟨2225375, by rfl⟩ : syracuseStep 2967167 = 4450751) B4450751
theorem B1978111 : Blo 1977435 1978111 := bstep (se 1 (by rfl) ⟨1483583, by rfl⟩ : syracuseStep 1978111 = 2967167) B2967167
theorem B2967173 : Blo 1977435 2967173 := bbase (se 4 (by rfl) ⟨278172, by rfl⟩ : syracuseStep 2967173 = 556345) (by norm_num)
theorem B1978115 : Blo 1977435 1978115 := bstep (se 1 (by rfl) ⟨1483586, by rfl⟩ : syracuseStep 1978115 = 2967173) B2967173
theorem B3338077 : Blo 1977435 3338077 := bbase (se 3 (by rfl) ⟨625889, by rfl⟩ : syracuseStep 3338077 = 1251779) (by norm_num)
theorem B4450769 : Blo 1977435 4450769 := bstep (se 2 (by rfl) ⟨1669038, by rfl⟩ : syracuseStep 4450769 = 3338077) B3338077
theorem B2967179 : Blo 1977435 2967179 := bstep (se 1 (by rfl) ⟨2225384, by rfl⟩ : syracuseStep 2967179 = 4450769) B4450769
theorem B1978119 : Blo 1977435 1978119 := bstep (se 1 (by rfl) ⟨1483589, by rfl⟩ : syracuseStep 1978119 = 2967179) B2967179
theorem B2225389 : Blo 1977435 2225389 := bbase (se 3 (by rfl) ⟨417260, by rfl⟩ : syracuseStep 2225389 = 834521) (by norm_num)
theorem B2967185 : Blo 1977435 2967185 := bstep (se 2 (by rfl) ⟨1112694, by rfl⟩ : syracuseStep 2967185 = 2225389) B2225389
theorem B1978123 : Blo 1977435 1978123 := bstep (se 1 (by rfl) ⟨1483592, by rfl⟩ : syracuseStep 1978123 = 2967185) B2967185
theorem B6676181 : Blo 1977435 6676181 := bbase (se 7 (by rfl) ⟨78236, by rfl⟩ : syracuseStep 6676181 = 156473) (by norm_num)
theorem B4450787 : Blo 1977435 4450787 := bstep (se 1 (by rfl) ⟨3338090, by rfl⟩ : syracuseStep 4450787 = 6676181) B6676181
theorem B2967191 : Blo 1977435 2967191 := bstep (se 1 (by rfl) ⟨2225393, by rfl⟩ : syracuseStep 2967191 = 4450787) B4450787
theorem B1978127 : Blo 1977435 1978127 := bstep (se 1 (by rfl) ⟨1483595, by rfl⟩ : syracuseStep 1978127 = 2967191) B2967191
theorem B2967197 : Blo 1977435 2967197 := bbase (se 3 (by rfl) ⟨556349, by rfl⟩ : syracuseStep 2967197 = 1112699) (by norm_num)
theorem B1978131 : Blo 1977435 1978131 := bstep (se 1 (by rfl) ⟨1483598, by rfl⟩ : syracuseStep 1978131 = 2967197) B2967197
theorem B4450805 : Blo 1977435 4450805 := bbase (se 5 (by rfl) ⟨208631, by rfl⟩ : syracuseStep 4450805 = 417263) (by norm_num)
theorem B2967203 : Blo 1977435 2967203 := bstep (se 1 (by rfl) ⟨2225402, by rfl⟩ : syracuseStep 2967203 = 4450805) B4450805
theorem B1978135 : Blo 1977435 1978135 := bstep (se 1 (by rfl) ⟨1483601, by rfl⟩ : syracuseStep 1978135 = 2967203) B2967203
theorem B2005129 : Blo 1977435 2005129 := bbase (se 2 (by rfl) ⟨751923, by rfl⟩ : syracuseStep 2005129 = 1503847) (by norm_num)
theorem B2673505 : Blo 1977435 2673505 := bstep (se 2 (by rfl) ⟨1002564, by rfl⟩ : syracuseStep 2673505 = 2005129) B2005129
theorem B14258693 : Blo 1977435 14258693 := bstep (se 4 (by rfl) ⟨1336752, by rfl⟩ : syracuseStep 14258693 = 2673505) B2673505
theorem B38023181 : Blo 1977435 38023181 := bstep (se 3 (by rfl) ⟨7129346, by rfl⟩ : syracuseStep 38023181 = 14258693) B14258693
theorem B25348787 : Blo 1977435 25348787 := bstep (se 1 (by rfl) ⟨19011590, by rfl⟩ : syracuseStep 25348787 = 38023181) B38023181
theorem B16899191 : Blo 1977435 16899191 := bstep (se 1 (by rfl) ⟨12674393, by rfl⟩ : syracuseStep 16899191 = 25348787) B25348787
theorem B11266127 : Blo 1977435 11266127 := bstep (se 1 (by rfl) ⟨8449595, by rfl⟩ : syracuseStep 11266127 = 16899191) B16899191
theorem B7510751 : Blo 1977435 7510751 := bstep (se 1 (by rfl) ⟨5633063, by rfl⟩ : syracuseStep 7510751 = 11266127) B11266127
theorem B5007167 : Blo 1977435 5007167 := bstep (se 1 (by rfl) ⟨3755375, by rfl⟩ : syracuseStep 5007167 = 7510751) B7510751
theorem B3338111 : Blo 1977435 3338111 := bstep (se 1 (by rfl) ⟨2503583, by rfl⟩ : syracuseStep 3338111 = 5007167) B5007167
theorem B2225407 : Blo 1977435 2225407 := bstep (se 1 (by rfl) ⟨1669055, by rfl⟩ : syracuseStep 2225407 = 3338111) B3338111
theorem B2967209 : Blo 1977435 2967209 := bstep (se 2 (by rfl) ⟨1112703, by rfl⟩ : syracuseStep 2967209 = 2225407) B2225407
theorem B1978139 : Blo 1977435 1978139 := bstep (se 1 (by rfl) ⟨1483604, by rfl⟩ : syracuseStep 1978139 = 2967209) B2967209
theorem B3168605 : Blo 1977435 3168605 := bbase (se 3 (by rfl) ⟨594113, by rfl⟩ : syracuseStep 3168605 = 1188227) (by norm_num)
theorem B2112403 : Blo 1977435 2112403 := bstep (se 1 (by rfl) ⟨1584302, by rfl⟩ : syracuseStep 2112403 = 3168605) B3168605
theorem B2816537 : Blo 1977435 2816537 := bstep (se 2 (by rfl) ⟨1056201, by rfl⟩ : syracuseStep 2816537 = 2112403) B2112403
theorem B7510765 : Blo 1977435 7510765 := bstep (se 3 (by rfl) ⟨1408268, by rfl⟩ : syracuseStep 7510765 = 2816537) B2816537
theorem B10014353 : Blo 1977435 10014353 := bstep (se 2 (by rfl) ⟨3755382, by rfl⟩ : syracuseStep 10014353 = 7510765) B7510765
theorem B6676235 : Blo 1977435 6676235 := bstep (se 1 (by rfl) ⟨5007176, by rfl⟩ : syracuseStep 6676235 = 10014353) B10014353
theorem B4450823 : Blo 1977435 4450823 := bstep (se 1 (by rfl) ⟨3338117, by rfl⟩ : syracuseStep 4450823 = 6676235) B6676235
theorem B2967215 : Blo 1977435 2967215 := bstep (se 1 (by rfl) ⟨2225411, by rfl⟩ : syracuseStep 2967215 = 4450823) B4450823
theorem B1978143 : Blo 1977435 1978143 := bstep (se 1 (by rfl) ⟨1483607, by rfl⟩ : syracuseStep 1978143 = 2967215) B2967215
theorem B2967221 : Blo 1977435 2967221 := bbase (se 5 (by rfl) ⟨139088, by rfl⟩ : syracuseStep 2967221 = 278177) (by norm_num)
theorem B1978147 : Blo 1977435 1978147 := bstep (se 1 (by rfl) ⟨1483610, by rfl⟩ : syracuseStep 1978147 = 2967221) B2967221
theorem B5007197 : Blo 1977435 5007197 := bbase (se 3 (by rfl) ⟨938849, by rfl⟩ : syracuseStep 5007197 = 1877699) (by norm_num)
theorem B3338131 : Blo 1977435 3338131 := bstep (se 1 (by rfl) ⟨2503598, by rfl⟩ : syracuseStep 3338131 = 5007197) B5007197
theorem B4450841 : Blo 1977435 4450841 := bstep (se 2 (by rfl) ⟨1669065, by rfl⟩ : syracuseStep 4450841 = 3338131) B3338131
theorem B2967227 : Blo 1977435 2967227 := bstep (se 1 (by rfl) ⟨2225420, by rfl⟩ : syracuseStep 2967227 = 4450841) B4450841
theorem B1978151 : Blo 1977435 1978151 := bstep (se 1 (by rfl) ⟨1483613, by rfl⟩ : syracuseStep 1978151 = 2967227) B2967227
theorem B2225425 : Blo 1977435 2225425 := bbase (se 2 (by rfl) ⟨834534, by rfl⟩ : syracuseStep 2225425 = 1669069) (by norm_num)
theorem B2967233 : Blo 1977435 2967233 := bstep (se 2 (by rfl) ⟨1112712, by rfl⟩ : syracuseStep 2967233 = 2225425) B2225425
theorem B1978155 : Blo 1977435 1978155 := bstep (se 1 (by rfl) ⟨1483616, by rfl⟩ : syracuseStep 1978155 = 2967233) B2967233
theorem B3755413 : Blo 1977435 3755413 := bbase (se 6 (by rfl) ⟨88017, by rfl⟩ : syracuseStep 3755413 = 176035) (by norm_num)
theorem B5007217 : Blo 1977435 5007217 := bstep (se 2 (by rfl) ⟨1877706, by rfl⟩ : syracuseStep 5007217 = 3755413) B3755413
theorem B6676289 : Blo 1977435 6676289 := bstep (se 2 (by rfl) ⟨2503608, by rfl⟩ : syracuseStep 6676289 = 5007217) B5007217
theorem B4450859 : Blo 1977435 4450859 := bstep (se 1 (by rfl) ⟨3338144, by rfl⟩ : syracuseStep 4450859 = 6676289) B6676289
theorem B2967239 : Blo 1977435 2967239 := bstep (se 1 (by rfl) ⟨2225429, by rfl⟩ : syracuseStep 2967239 = 4450859) B4450859
theorem B1978159 : Blo 1977435 1978159 := bstep (se 1 (by rfl) ⟨1483619, by rfl⟩ : syracuseStep 1978159 = 2967239) B2967239
theorem B2967245 : Blo 1977435 2967245 := bbase (se 3 (by rfl) ⟨556358, by rfl⟩ : syracuseStep 2967245 = 1112717) (by norm_num)
theorem B1978163 : Blo 1977435 1978163 := bstep (se 1 (by rfl) ⟨1483622, by rfl⟩ : syracuseStep 1978163 = 2967245) B2967245
theorem B4450877 : Blo 1977435 4450877 := bbase (se 3 (by rfl) ⟨834539, by rfl⟩ : syracuseStep 4450877 = 1669079) (by norm_num)
theorem B2967251 : Blo 1977435 2967251 := bstep (se 1 (by rfl) ⟨2225438, by rfl⟩ : syracuseStep 2967251 = 4450877) B4450877
theorem B1978167 : Blo 1977435 1978167 := bstep (se 1 (by rfl) ⟨1483625, by rfl⟩ : syracuseStep 1978167 = 2967251) B2967251
theorem B3338165 : Blo 1977435 3338165 := bbase (se 5 (by rfl) ⟨156476, by rfl⟩ : syracuseStep 3338165 = 312953) (by norm_num)
theorem B2225443 : Blo 1977435 2225443 := bstep (se 1 (by rfl) ⟨1669082, by rfl⟩ : syracuseStep 2225443 = 3338165) B3338165
theorem B2967257 : Blo 1977435 2967257 := bstep (se 2 (by rfl) ⟨1112721, by rfl⟩ : syracuseStep 2967257 = 2225443) B2225443
theorem B1978171 : Blo 1977435 1978171 := bstep (se 1 (by rfl) ⟨1483628, by rfl⟩ : syracuseStep 1978171 = 2967257) B2967257
theorem B2112437 : Blo 1977435 2112437 := bbase (se 5 (by rfl) ⟨99020, by rfl⟩ : syracuseStep 2112437 = 198041) (by norm_num)
theorem B5633165 : Blo 1977435 5633165 := bstep (se 3 (by rfl) ⟨1056218, by rfl⟩ : syracuseStep 5633165 = 2112437) B2112437
theorem B15021773 : Blo 1977435 15021773 := bstep (se 3 (by rfl) ⟨2816582, by rfl⟩ : syracuseStep 15021773 = 5633165) B5633165
theorem B10014515 : Blo 1977435 10014515 := bstep (se 1 (by rfl) ⟨7510886, by rfl⟩ : syracuseStep 10014515 = 15021773) B15021773
theorem B6676343 : Blo 1977435 6676343 := bstep (se 1 (by rfl) ⟨5007257, by rfl⟩ : syracuseStep 6676343 = 10014515) B10014515
theorem B4450895 : Blo 1977435 4450895 := bstep (se 1 (by rfl) ⟨3338171, by rfl⟩ : syracuseStep 4450895 = 6676343) B6676343
theorem B2967263 : Blo 1977435 2967263 := bstep (se 1 (by rfl) ⟨2225447, by rfl⟩ : syracuseStep 2967263 = 4450895) B4450895
theorem B1978175 : Blo 1977435 1978175 := bstep (se 1 (by rfl) ⟨1483631, by rfl⟩ : syracuseStep 1978175 = 2967263) B2967263
theorem B2967269 : Blo 1977435 2967269 := bbase (se 4 (by rfl) ⟨278181, by rfl⟩ : syracuseStep 2967269 = 556363) (by norm_num)
theorem B1978179 : Blo 1977435 1978179 := bstep (se 1 (by rfl) ⟨1483634, by rfl⟩ : syracuseStep 1978179 = 2967269) B2967269
theorem B5633189 : Blo 1977435 5633189 := bbase (se 4 (by rfl) ⟨528111, by rfl⟩ : syracuseStep 5633189 = 1056223) (by norm_num)
theorem B3755459 : Blo 1977435 3755459 := bstep (se 1 (by rfl) ⟨2816594, by rfl⟩ : syracuseStep 3755459 = 5633189) B5633189
theorem B2503639 : Blo 1977435 2503639 := bstep (se 1 (by rfl) ⟨1877729, by rfl⟩ : syracuseStep 2503639 = 3755459) B3755459
theorem B3338185 : Blo 1977435 3338185 := bstep (se 2 (by rfl) ⟨1251819, by rfl⟩ : syracuseStep 3338185 = 2503639) B2503639
theorem B4450913 : Blo 1977435 4450913 := bstep (se 2 (by rfl) ⟨1669092, by rfl⟩ : syracuseStep 4450913 = 3338185) B3338185
theorem B2967275 : Blo 1977435 2967275 := bstep (se 1 (by rfl) ⟨2225456, by rfl⟩ : syracuseStep 2967275 = 4450913) B4450913
theorem B1978183 : Blo 1977435 1978183 := bstep (se 1 (by rfl) ⟨1483637, by rfl⟩ : syracuseStep 1978183 = 2967275) B2967275
theorem B2225461 : Blo 1977435 2225461 := bbase (se 5 (by rfl) ⟨104318, by rfl⟩ : syracuseStep 2225461 = 208637) (by norm_num)
theorem B2967281 : Blo 1977435 2967281 := bstep (se 2 (by rfl) ⟨1112730, by rfl⟩ : syracuseStep 2967281 = 2225461) B2225461
theorem B1978187 : Blo 1977435 1978187 := bstep (se 1 (by rfl) ⟨1483640, by rfl⟩ : syracuseStep 1978187 = 2967281) B2967281
theorem B2503649 : Blo 1977435 2503649 := bbase (se 2 (by rfl) ⟨938868, by rfl⟩ : syracuseStep 2503649 = 1877737) (by norm_num)
theorem B6676397 : Blo 1977435 6676397 := bstep (se 3 (by rfl) ⟨1251824, by rfl⟩ : syracuseStep 6676397 = 2503649) B2503649
theorem B4450931 : Blo 1977435 4450931 := bstep (se 1 (by rfl) ⟨3338198, by rfl⟩ : syracuseStep 4450931 = 6676397) B6676397
theorem B2967287 : Blo 1977435 2967287 := bstep (se 1 (by rfl) ⟨2225465, by rfl⟩ : syracuseStep 2967287 = 4450931) B4450931
theorem B1978191 : Blo 1977435 1978191 := bstep (se 1 (by rfl) ⟨1483643, by rfl⟩ : syracuseStep 1978191 = 2967287) B2967287
theorem B2967293 : Blo 1977435 2967293 := bbase (se 3 (by rfl) ⟨556367, by rfl⟩ : syracuseStep 2967293 = 1112735) (by norm_num)
theorem B1978195 : Blo 1977435 1978195 := bstep (se 1 (by rfl) ⟨1483646, by rfl⟩ : syracuseStep 1978195 = 2967293) B2967293
theorem B4450949 : Blo 1977435 4450949 := bbase (se 4 (by rfl) ⟨417276, by rfl⟩ : syracuseStep 4450949 = 834553) (by norm_num)
theorem B2967299 : Blo 1977435 2967299 := bstep (se 1 (by rfl) ⟨2225474, by rfl⟩ : syracuseStep 2967299 = 4450949) B4450949
theorem B1978199 : Blo 1977435 1978199 := bstep (se 1 (by rfl) ⟨1483649, by rfl⟩ : syracuseStep 1978199 = 2967299) B2967299
theorem B2032553 : Blo 1977435 2032553 := bbase (se 2 (by rfl) ⟨762207, by rfl⟩ : syracuseStep 2032553 = 1524415) (by norm_num)
theorem B5420141 : Blo 1977435 5420141 := bstep (se 3 (by rfl) ⟨1016276, by rfl⟩ : syracuseStep 5420141 = 2032553) B2032553
theorem B3613427 : Blo 1977435 3613427 := bstep (se 1 (by rfl) ⟨2710070, by rfl⟩ : syracuseStep 3613427 = 5420141) B5420141
theorem B2408951 : Blo 1977435 2408951 := bstep (se 1 (by rfl) ⟨1806713, by rfl⟩ : syracuseStep 2408951 = 3613427) B3613427
theorem B6423869 : Blo 1977435 6423869 := bstep (se 3 (by rfl) ⟨1204475, by rfl⟩ : syracuseStep 6423869 = 2408951) B2408951
theorem B4282579 : Blo 1977435 4282579 := bstep (se 1 (by rfl) ⟨3211934, by rfl⟩ : syracuseStep 4282579 = 6423869) B6423869
theorem B5710105 : Blo 1977435 5710105 := bstep (se 2 (by rfl) ⟨2141289, by rfl⟩ : syracuseStep 5710105 = 4282579) B4282579
theorem B30453893 : Blo 1977435 30453893 := bstep (se 4 (by rfl) ⟨2855052, by rfl⟩ : syracuseStep 30453893 = 5710105) B5710105
theorem B20302595 : Blo 1977435 20302595 := bstep (se 1 (by rfl) ⟨15226946, by rfl⟩ : syracuseStep 20302595 = 30453893) B30453893
theorem B13535063 : Blo 1977435 13535063 := bstep (se 1 (by rfl) ⟨10151297, by rfl⟩ : syracuseStep 13535063 = 20302595) B20302595
theorem B9023375 : Blo 1977435 9023375 := bstep (se 1 (by rfl) ⟨6767531, by rfl⟩ : syracuseStep 9023375 = 13535063) B13535063
theorem B6015583 : Blo 1977435 6015583 := bstep (se 1 (by rfl) ⟨4511687, by rfl⟩ : syracuseStep 6015583 = 9023375) B9023375
theorem B8020777 : Blo 1977435 8020777 := bstep (se 2 (by rfl) ⟨3007791, by rfl⟩ : syracuseStep 8020777 = 6015583) B6015583
theorem B10694369 : Blo 1977435 10694369 := bstep (se 2 (by rfl) ⟨4010388, by rfl⟩ : syracuseStep 10694369 = 8020777) B8020777
theorem B7129579 : Blo 1977435 7129579 := bstep (se 1 (by rfl) ⟨5347184, by rfl⟩ : syracuseStep 7129579 = 10694369) B10694369
theorem B9506105 : Blo 1977435 9506105 := bstep (se 2 (by rfl) ⟨3564789, by rfl⟩ : syracuseStep 9506105 = 7129579) B7129579
theorem B6337403 : Blo 1977435 6337403 := bstep (se 1 (by rfl) ⟨4753052, by rfl⟩ : syracuseStep 6337403 = 9506105) B9506105
theorem B4224935 : Blo 1977435 4224935 := bstep (se 1 (by rfl) ⟨3168701, by rfl⟩ : syracuseStep 4224935 = 6337403) B6337403
theorem B2816623 : Blo 1977435 2816623 := bstep (se 1 (by rfl) ⟨2112467, by rfl⟩ : syracuseStep 2816623 = 4224935) B4224935
theorem B3755497 : Blo 1977435 3755497 := bstep (se 2 (by rfl) ⟨1408311, by rfl⟩ : syracuseStep 3755497 = 2816623) B2816623
theorem B5007329 : Blo 1977435 5007329 := bstep (se 2 (by rfl) ⟨1877748, by rfl⟩ : syracuseStep 5007329 = 3755497) B3755497
theorem B3338219 : Blo 1977435 3338219 := bstep (se 1 (by rfl) ⟨2503664, by rfl⟩ : syracuseStep 3338219 = 5007329) B5007329
theorem B2225479 : Blo 1977435 2225479 := bstep (se 1 (by rfl) ⟨1669109, by rfl⟩ : syracuseStep 2225479 = 3338219) B3338219
theorem B2967305 : Blo 1977435 2967305 := bstep (se 2 (by rfl) ⟨1112739, by rfl⟩ : syracuseStep 2967305 = 2225479) B2225479
theorem B1978203 : Blo 1977435 1978203 := bstep (se 1 (by rfl) ⟨1483652, by rfl⟩ : syracuseStep 1978203 = 2967305) B2967305
theorem B10014677 : Blo 1977435 10014677 := bbase (se 7 (by rfl) ⟨117359, by rfl⟩ : syracuseStep 10014677 = 234719) (by norm_num)
theorem B6676451 : Blo 1977435 6676451 := bstep (se 1 (by rfl) ⟨5007338, by rfl⟩ : syracuseStep 6676451 = 10014677) B10014677
theorem B4450967 : Blo 1977435 4450967 := bstep (se 1 (by rfl) ⟨3338225, by rfl⟩ : syracuseStep 4450967 = 6676451) B6676451
theorem B2967311 : Blo 1977435 2967311 := bstep (se 1 (by rfl) ⟨2225483, by rfl⟩ : syracuseStep 2967311 = 4450967) B4450967
theorem B1978207 : Blo 1977435 1978207 := bstep (se 1 (by rfl) ⟨1483655, by rfl⟩ : syracuseStep 1978207 = 2967311) B2967311
theorem B2967317 : Blo 1977435 2967317 := bbase (se 6 (by rfl) ⟨69546, by rfl⟩ : syracuseStep 2967317 = 139093) (by norm_num)
theorem B1978211 : Blo 1977435 1978211 := bstep (se 1 (by rfl) ⟨1483658, by rfl⟩ : syracuseStep 1978211 = 2967317) B2967317
theorem B3048845 : Blo 1977435 3048845 := bbase (se 3 (by rfl) ⟨571658, by rfl⟩ : syracuseStep 3048845 = 1143317) (by norm_num)
theorem B8130253 : Blo 1977435 8130253 := bstep (se 3 (by rfl) ⟨1524422, by rfl⟩ : syracuseStep 8130253 = 3048845) B3048845
theorem B10840337 : Blo 1977435 10840337 := bstep (se 2 (by rfl) ⟨4065126, by rfl⟩ : syracuseStep 10840337 = 8130253) B8130253
theorem B115630261 : Blo 1977435 115630261 := bstep (se 5 (by rfl) ⟨5420168, by rfl⟩ : syracuseStep 115630261 = 10840337) B10840337
theorem B616694725 : Blo 1977435 616694725 := bstep (se 4 (by rfl) ⟨57815130, by rfl⟩ : syracuseStep 616694725 = 115630261) B115630261
theorem B822259633 : Blo 1977435 822259633 := bstep (se 2 (by rfl) ⟨308347362, by rfl⟩ : syracuseStep 822259633 = 616694725) B616694725
theorem B1096346177 : Blo 1977435 1096346177 := bstep (se 2 (by rfl) ⟨411129816, by rfl⟩ : syracuseStep 1096346177 = 822259633) B822259633
theorem B730897451 : Blo 1977435 730897451 := bstep (se 1 (by rfl) ⟨548173088, by rfl⟩ : syracuseStep 730897451 = 1096346177) B1096346177
theorem B487264967 : Blo 1977435 487264967 := bstep (se 1 (by rfl) ⟨365448725, by rfl⟩ : syracuseStep 487264967 = 730897451) B730897451
theorem B324843311 : Blo 1977435 324843311 := bstep (se 1 (by rfl) ⟨243632483, by rfl⟩ : syracuseStep 324843311 = 487264967) B487264967
theorem B216562207 : Blo 1977435 216562207 := bstep (se 1 (by rfl) ⟨162421655, by rfl⟩ : syracuseStep 216562207 = 324843311) B324843311
theorem B288749609 : Blo 1977435 288749609 := bstep (se 2 (by rfl) ⟨108281103, by rfl⟩ : syracuseStep 288749609 = 216562207) B216562207
theorem B192499739 : Blo 1977435 192499739 := bstep (se 1 (by rfl) ⟨144374804, by rfl⟩ : syracuseStep 192499739 = 288749609) B288749609
theorem B128333159 : Blo 1977435 128333159 := bstep (se 1 (by rfl) ⟨96249869, by rfl⟩ : syracuseStep 128333159 = 192499739) B192499739
theorem B85555439 : Blo 1977435 85555439 := bstep (se 1 (by rfl) ⟨64166579, by rfl⟩ : syracuseStep 85555439 = 128333159) B128333159
theorem B57036959 : Blo 1977435 57036959 := bstep (se 1 (by rfl) ⟨42777719, by rfl⟩ : syracuseStep 57036959 = 85555439) B85555439
theorem B38024639 : Blo 1977435 38024639 := bstep (se 1 (by rfl) ⟨28518479, by rfl⟩ : syracuseStep 38024639 = 57036959) B57036959
theorem B25349759 : Blo 1977435 25349759 := bstep (se 1 (by rfl) ⟨19012319, by rfl⟩ : syracuseStep 25349759 = 38024639) B38024639
theorem B16899839 : Blo 1977435 16899839 := bstep (se 1 (by rfl) ⟨12674879, by rfl⟩ : syracuseStep 16899839 = 25349759) B25349759
theorem B11266559 : Blo 1977435 11266559 := bstep (se 1 (by rfl) ⟨8449919, by rfl⟩ : syracuseStep 11266559 = 16899839) B16899839
theorem B7511039 : Blo 1977435 7511039 := bstep (se 1 (by rfl) ⟨5633279, by rfl⟩ : syracuseStep 7511039 = 11266559) B11266559
theorem B5007359 : Blo 1977435 5007359 := bstep (se 1 (by rfl) ⟨3755519, by rfl⟩ : syracuseStep 5007359 = 7511039) B7511039
theorem B3338239 : Blo 1977435 3338239 := bstep (se 1 (by rfl) ⟨2503679, by rfl⟩ : syracuseStep 3338239 = 5007359) B5007359
theorem B4450985 : Blo 1977435 4450985 := bstep (se 2 (by rfl) ⟨1669119, by rfl⟩ : syracuseStep 4450985 = 3338239) B3338239
theorem B2967323 : Blo 1977435 2967323 := bstep (se 1 (by rfl) ⟨2225492, by rfl⟩ : syracuseStep 2967323 = 4450985) B4450985
theorem B1978215 : Blo 1977435 1978215 := bstep (se 1 (by rfl) ⟨1483661, by rfl⟩ : syracuseStep 1978215 = 2967323) B2967323
theorem B2225497 : Blo 1977435 2225497 := bbase (se 2 (by rfl) ⟨834561, by rfl⟩ : syracuseStep 2225497 = 1669123) (by norm_num)
theorem B2967329 : Blo 1977435 2967329 := bstep (se 2 (by rfl) ⟨1112748, by rfl⟩ : syracuseStep 2967329 = 2225497) B2225497
theorem B1978219 : Blo 1977435 1978219 := bstep (se 1 (by rfl) ⟨1483664, by rfl⟩ : syracuseStep 1978219 = 2967329) B2967329
theorem B3168733 : Blo 1977435 3168733 := bbase (se 3 (by rfl) ⟨594137, by rfl⟩ : syracuseStep 3168733 = 1188275) (by norm_num)
theorem B4224977 : Blo 1977435 4224977 := bstep (se 2 (by rfl) ⟨1584366, by rfl⟩ : syracuseStep 4224977 = 3168733) B3168733
theorem B2816651 : Blo 1977435 2816651 := bstep (se 1 (by rfl) ⟨2112488, by rfl⟩ : syracuseStep 2816651 = 4224977) B4224977
theorem B7511069 : Blo 1977435 7511069 := bstep (se 3 (by rfl) ⟨1408325, by rfl⟩ : syracuseStep 7511069 = 2816651) B2816651
theorem B5007379 : Blo 1977435 5007379 := bstep (se 1 (by rfl) ⟨3755534, by rfl⟩ : syracuseStep 5007379 = 7511069) B7511069
theorem B6676505 : Blo 1977435 6676505 := bstep (se 2 (by rfl) ⟨2503689, by rfl⟩ : syracuseStep 6676505 = 5007379) B5007379
theorem B4451003 : Blo 1977435 4451003 := bstep (se 1 (by rfl) ⟨3338252, by rfl⟩ : syracuseStep 4451003 = 6676505) B6676505
theorem B2967335 : Blo 1977435 2967335 := bstep (se 1 (by rfl) ⟨2225501, by rfl⟩ : syracuseStep 2967335 = 4451003) B4451003
theorem B1978223 : Blo 1977435 1978223 := bstep (se 1 (by rfl) ⟨1483667, by rfl⟩ : syracuseStep 1978223 = 2967335) B2967335
theorem B2967341 : Blo 1977435 2967341 := bbase (se 3 (by rfl) ⟨556376, by rfl⟩ : syracuseStep 2967341 = 1112753) (by norm_num)
theorem B1978227 : Blo 1977435 1978227 := bstep (se 1 (by rfl) ⟨1483670, by rfl⟩ : syracuseStep 1978227 = 2967341) B2967341
theorem B4451021 : Blo 1977435 4451021 := bbase (se 3 (by rfl) ⟨834566, by rfl⟩ : syracuseStep 4451021 = 1669133) (by norm_num)
theorem B2967347 : Blo 1977435 2967347 := bstep (se 1 (by rfl) ⟨2225510, by rfl⟩ : syracuseStep 2967347 = 4451021) B4451021
theorem B1978231 : Blo 1977435 1978231 := bstep (se 1 (by rfl) ⟨1483673, by rfl⟩ : syracuseStep 1978231 = 2967347) B2967347
theorem B2503705 : Blo 1977435 2503705 := bbase (se 2 (by rfl) ⟨938889, by rfl⟩ : syracuseStep 2503705 = 1877779) (by norm_num)
theorem B3338273 : Blo 1977435 3338273 := bstep (se 2 (by rfl) ⟨1251852, by rfl⟩ : syracuseStep 3338273 = 2503705) B2503705
theorem B2225515 : Blo 1977435 2225515 := bstep (se 1 (by rfl) ⟨1669136, by rfl⟩ : syracuseStep 2225515 = 3338273) B3338273
theorem B2967353 : Blo 1977435 2967353 := bstep (se 2 (by rfl) ⟨1112757, by rfl⟩ : syracuseStep 2967353 = 2225515) B2225515
theorem B1978235 : Blo 1977435 1978235 := bstep (se 1 (by rfl) ⟨1483676, by rfl⟩ : syracuseStep 1978235 = 2967353) B2967353
theorem B8450021 : Blo 1977435 8450021 := bbase (se 4 (by rfl) ⟨792189, by rfl⟩ : syracuseStep 8450021 = 1584379) (by norm_num)
theorem B22533389 : Blo 1977435 22533389 := bstep (se 3 (by rfl) ⟨4225010, by rfl⟩ : syracuseStep 22533389 = 8450021) B8450021
theorem B15022259 : Blo 1977435 15022259 := bstep (se 1 (by rfl) ⟨11266694, by rfl⟩ : syracuseStep 15022259 = 22533389) B22533389
theorem B10014839 : Blo 1977435 10014839 := bstep (se 1 (by rfl) ⟨7511129, by rfl⟩ : syracuseStep 10014839 = 15022259) B15022259
theorem B6676559 : Blo 1977435 6676559 := bstep (se 1 (by rfl) ⟨5007419, by rfl⟩ : syracuseStep 6676559 = 10014839) B10014839
theorem B4451039 : Blo 1977435 4451039 := bstep (se 1 (by rfl) ⟨3338279, by rfl⟩ : syracuseStep 4451039 = 6676559) B6676559
theorem B2967359 : Blo 1977435 2967359 := bstep (se 1 (by rfl) ⟨2225519, by rfl⟩ : syracuseStep 2967359 = 4451039) B4451039
theorem B1978239 : Blo 1977435 1978239 := bstep (se 1 (by rfl) ⟨1483679, by rfl⟩ : syracuseStep 1978239 = 2967359) B2967359
theorem B2967365 : Blo 1977435 2967365 := bbase (se 4 (by rfl) ⟨278190, by rfl⟩ : syracuseStep 2967365 = 556381) (by norm_num)
theorem B1978243 : Blo 1977435 1978243 := bstep (se 1 (by rfl) ⟨1483682, by rfl⟩ : syracuseStep 1978243 = 2967365) B2967365
theorem B3338293 : Blo 1977435 3338293 := bbase (se 5 (by rfl) ⟨156482, by rfl⟩ : syracuseStep 3338293 = 312965) (by norm_num)
theorem B4451057 : Blo 1977435 4451057 := bstep (se 2 (by rfl) ⟨1669146, by rfl⟩ : syracuseStep 4451057 = 3338293) B3338293
theorem B2967371 : Blo 1977435 2967371 := bstep (se 1 (by rfl) ⟨2225528, by rfl⟩ : syracuseStep 2967371 = 4451057) B4451057
theorem B1978247 : Blo 1977435 1978247 := bstep (se 1 (by rfl) ⟨1483685, by rfl⟩ : syracuseStep 1978247 = 2967371) B2967371
theorem B2225533 : Blo 1977435 2225533 := bbase (se 3 (by rfl) ⟨417287, by rfl⟩ : syracuseStep 2225533 = 834575) (by norm_num)
theorem B2967377 : Blo 1977435 2967377 := bstep (se 2 (by rfl) ⟨1112766, by rfl⟩ : syracuseStep 2967377 = 2225533) B2225533
theorem B1978251 : Blo 1977435 1978251 := bstep (se 1 (by rfl) ⟨1483688, by rfl⟩ : syracuseStep 1978251 = 2967377) B2967377
theorem B6676613 : Blo 1977435 6676613 := bbase (se 4 (by rfl) ⟨625932, by rfl⟩ : syracuseStep 6676613 = 1251865) (by norm_num)
theorem B4451075 : Blo 1977435 4451075 := bstep (se 1 (by rfl) ⟨3338306, by rfl⟩ : syracuseStep 4451075 = 6676613) B6676613
theorem B2967383 : Blo 1977435 2967383 := bstep (se 1 (by rfl) ⟨2225537, by rfl⟩ : syracuseStep 2967383 = 4451075) B4451075
theorem B1978255 : Blo 1977435 1978255 := bstep (se 1 (by rfl) ⟨1483691, by rfl⟩ : syracuseStep 1978255 = 2967383) B2967383
theorem B2967389 : Blo 1977435 2967389 := bbase (se 3 (by rfl) ⟨556385, by rfl⟩ : syracuseStep 2967389 = 1112771) (by norm_num)
theorem B1978259 : Blo 1977435 1978259 := bstep (se 1 (by rfl) ⟨1483694, by rfl⟩ : syracuseStep 1978259 = 2967389) B2967389
theorem B4451093 : Blo 1977435 4451093 := bbase (se 6 (by rfl) ⟨104322, by rfl⟩ : syracuseStep 4451093 = 208645) (by norm_num)
theorem B2967395 : Blo 1977435 2967395 := bstep (se 1 (by rfl) ⟨2225546, by rfl⟩ : syracuseStep 2967395 = 4451093) B4451093
theorem B1978263 : Blo 1977435 1978263 := bstep (se 1 (by rfl) ⟨1483697, by rfl⟩ : syracuseStep 1978263 = 2967395) B2967395
theorem B7511237 : Blo 1977435 7511237 := bbase (se 4 (by rfl) ⟨704178, by rfl⟩ : syracuseStep 7511237 = 1408357) (by norm_num)
theorem B5007491 : Blo 1977435 5007491 := bstep (se 1 (by rfl) ⟨3755618, by rfl⟩ : syracuseStep 5007491 = 7511237) B7511237
theorem B3338327 : Blo 1977435 3338327 := bstep (se 1 (by rfl) ⟨2503745, by rfl⟩ : syracuseStep 3338327 = 5007491) B5007491
theorem B2225551 : Blo 1977435 2225551 := bstep (se 1 (by rfl) ⟨1669163, by rfl⟩ : syracuseStep 2225551 = 3338327) B3338327
theorem B2967401 : Blo 1977435 2967401 := bstep (se 2 (by rfl) ⟨1112775, by rfl⟩ : syracuseStep 2967401 = 2225551) B2225551
theorem B1978267 : Blo 1977435 1978267 := bstep (se 1 (by rfl) ⟨1483700, by rfl⟩ : syracuseStep 1978267 = 2967401) B2967401
theorem B3212045 : Blo 1977435 3212045 := bbase (se 3 (by rfl) ⟨602258, by rfl⟩ : syracuseStep 3212045 = 1204517) (by norm_num)
theorem B2141363 : Blo 1977435 2141363 := bstep (se 1 (by rfl) ⟨1606022, by rfl⟩ : syracuseStep 2141363 = 3212045) B3212045
theorem B5710301 : Blo 1977435 5710301 := bstep (se 3 (by rfl) ⟨1070681, by rfl⟩ : syracuseStep 5710301 = 2141363) B2141363
theorem B3806867 : Blo 1977435 3806867 := bstep (se 1 (by rfl) ⟨2855150, by rfl⟩ : syracuseStep 3806867 = 5710301) B5710301
theorem B2537911 : Blo 1977435 2537911 := bstep (se 1 (by rfl) ⟨1903433, by rfl⟩ : syracuseStep 2537911 = 3806867) B3806867
theorem B13535525 : Blo 1977435 13535525 := bstep (se 4 (by rfl) ⟨1268955, by rfl⟩ : syracuseStep 13535525 = 2537911) B2537911
theorem B9023683 : Blo 1977435 9023683 := bstep (se 1 (by rfl) ⟨6767762, by rfl⟩ : syracuseStep 9023683 = 13535525) B13535525
theorem B12031577 : Blo 1977435 12031577 := bstep (se 2 (by rfl) ⟨4511841, by rfl⟩ : syracuseStep 12031577 = 9023683) B9023683
theorem B8021051 : Blo 1977435 8021051 := bstep (se 1 (by rfl) ⟨6015788, by rfl⟩ : syracuseStep 8021051 = 12031577) B12031577
theorem B5347367 : Blo 1977435 5347367 := bstep (se 1 (by rfl) ⟨4010525, by rfl⟩ : syracuseStep 5347367 = 8021051) B8021051
theorem B3564911 : Blo 1977435 3564911 := bstep (se 1 (by rfl) ⟨2673683, by rfl⟩ : syracuseStep 3564911 = 5347367) B5347367
theorem B9506429 : Blo 1977435 9506429 := bstep (se 3 (by rfl) ⟨1782455, by rfl⟩ : syracuseStep 9506429 = 3564911) B3564911
theorem B6337619 : Blo 1977435 6337619 := bstep (se 1 (by rfl) ⟨4753214, by rfl⟩ : syracuseStep 6337619 = 9506429) B9506429
theorem B4225079 : Blo 1977435 4225079 := bstep (se 1 (by rfl) ⟨3168809, by rfl⟩ : syracuseStep 4225079 = 6337619) B6337619
theorem B11266877 : Blo 1977435 11266877 := bstep (se 3 (by rfl) ⟨2112539, by rfl⟩ : syracuseStep 11266877 = 4225079) B4225079
theorem B7511251 : Blo 1977435 7511251 := bstep (se 1 (by rfl) ⟨5633438, by rfl⟩ : syracuseStep 7511251 = 11266877) B11266877
theorem B10015001 : Blo 1977435 10015001 := bstep (se 2 (by rfl) ⟨3755625, by rfl⟩ : syracuseStep 10015001 = 7511251) B7511251
theorem B6676667 : Blo 1977435 6676667 := bstep (se 1 (by rfl) ⟨5007500, by rfl⟩ : syracuseStep 6676667 = 10015001) B10015001
theorem B4451111 : Blo 1977435 4451111 := bstep (se 1 (by rfl) ⟨3338333, by rfl⟩ : syracuseStep 4451111 = 6676667) B6676667
theorem B2967407 : Blo 1977435 2967407 := bstep (se 1 (by rfl) ⟨2225555, by rfl⟩ : syracuseStep 2967407 = 4451111) B4451111
theorem B1978271 : Blo 1977435 1978271 := bstep (se 1 (by rfl) ⟨1483703, by rfl⟩ : syracuseStep 1978271 = 2967407) B2967407
theorem B2967413 : Blo 1977435 2967413 := bbase (se 5 (by rfl) ⟨139097, by rfl⟩ : syracuseStep 2967413 = 278195) (by norm_num)
theorem B1978275 : Blo 1977435 1978275 := bstep (se 1 (by rfl) ⟨1483706, by rfl⟩ : syracuseStep 1978275 = 2967413) B2967413
theorem B6511765 : Blo 1977435 6511765 := bbase (se 6 (by rfl) ⟨152619, by rfl⟩ : syracuseStep 6511765 = 305239) (by norm_num)
theorem B8682353 : Blo 1977435 8682353 := bstep (se 2 (by rfl) ⟨3255882, by rfl⟩ : syracuseStep 8682353 = 6511765) B6511765
theorem B5788235 : Blo 1977435 5788235 := bstep (se 1 (by rfl) ⟨4341176, by rfl⟩ : syracuseStep 5788235 = 8682353) B8682353
theorem B3858823 : Blo 1977435 3858823 := bstep (se 1 (by rfl) ⟨2894117, by rfl⟩ : syracuseStep 3858823 = 5788235) B5788235
theorem B20580389 : Blo 1977435 20580389 := bstep (se 4 (by rfl) ⟨1929411, by rfl⟩ : syracuseStep 20580389 = 3858823) B3858823
theorem B13720259 : Blo 1977435 13720259 := bstep (se 1 (by rfl) ⟨10290194, by rfl⟩ : syracuseStep 13720259 = 20580389) B20580389
theorem B9146839 : Blo 1977435 9146839 := bstep (se 1 (by rfl) ⟨6860129, by rfl⟩ : syracuseStep 9146839 = 13720259) B13720259
theorem B12195785 : Blo 1977435 12195785 := bstep (se 2 (by rfl) ⟨4573419, by rfl⟩ : syracuseStep 12195785 = 9146839) B9146839
theorem B32522093 : Blo 1977435 32522093 := bstep (se 3 (by rfl) ⟨6097892, by rfl⟩ : syracuseStep 32522093 = 12195785) B12195785
theorem B21681395 : Blo 1977435 21681395 := bstep (se 1 (by rfl) ⟨16261046, by rfl⟩ : syracuseStep 21681395 = 32522093) B32522093
theorem B14454263 : Blo 1977435 14454263 := bstep (se 1 (by rfl) ⟨10840697, by rfl⟩ : syracuseStep 14454263 = 21681395) B21681395
theorem B9636175 : Blo 1977435 9636175 := bstep (se 1 (by rfl) ⟨7227131, by rfl⟩ : syracuseStep 9636175 = 14454263) B14454263
theorem B12848233 : Blo 1977435 12848233 := bstep (se 2 (by rfl) ⟨4818087, by rfl⟩ : syracuseStep 12848233 = 9636175) B9636175
theorem B17130977 : Blo 1977435 17130977 := bstep (se 2 (by rfl) ⟨6424116, by rfl⟩ : syracuseStep 17130977 = 12848233) B12848233
theorem B11420651 : Blo 1977435 11420651 := bstep (se 1 (by rfl) ⟨8565488, by rfl⟩ : syracuseStep 11420651 = 17130977) B17130977
theorem B7613767 : Blo 1977435 7613767 := bstep (se 1 (by rfl) ⟨5710325, by rfl⟩ : syracuseStep 7613767 = 11420651) B11420651
theorem B10151689 : Blo 1977435 10151689 := bstep (se 2 (by rfl) ⟨3806883, by rfl⟩ : syracuseStep 10151689 = 7613767) B7613767
theorem B13535585 : Blo 1977435 13535585 := bstep (se 2 (by rfl) ⟨5075844, by rfl⟩ : syracuseStep 13535585 = 10151689) B10151689
theorem B9023723 : Blo 1977435 9023723 := bstep (se 1 (by rfl) ⟨6767792, by rfl⟩ : syracuseStep 9023723 = 13535585) B13535585
theorem B6015815 : Blo 1977435 6015815 := bstep (se 1 (by rfl) ⟨4511861, by rfl⟩ : syracuseStep 6015815 = 9023723) B9023723
theorem B4010543 : Blo 1977435 4010543 := bstep (se 1 (by rfl) ⟨3007907, by rfl⟩ : syracuseStep 4010543 = 6015815) B6015815
theorem B2673695 : Blo 1977435 2673695 := bstep (se 1 (by rfl) ⟨2005271, by rfl⟩ : syracuseStep 2673695 = 4010543) B4010543
theorem B7129853 : Blo 1977435 7129853 := bstep (se 3 (by rfl) ⟨1336847, by rfl⟩ : syracuseStep 7129853 = 2673695) B2673695
theorem B4753235 : Blo 1977435 4753235 := bstep (se 1 (by rfl) ⟨3564926, by rfl⟩ : syracuseStep 4753235 = 7129853) B7129853
theorem B3168823 : Blo 1977435 3168823 := bstep (se 1 (by rfl) ⟨2376617, by rfl⟩ : syracuseStep 3168823 = 4753235) B4753235
theorem B4225097 : Blo 1977435 4225097 := bstep (se 2 (by rfl) ⟨1584411, by rfl⟩ : syracuseStep 4225097 = 3168823) B3168823
theorem B2816731 : Blo 1977435 2816731 := bstep (se 1 (by rfl) ⟨2112548, by rfl⟩ : syracuseStep 2816731 = 4225097) B4225097
theorem B3755641 : Blo 1977435 3755641 := bstep (se 2 (by rfl) ⟨1408365, by rfl⟩ : syracuseStep 3755641 = 2816731) B2816731
theorem B5007521 : Blo 1977435 5007521 := bstep (se 2 (by rfl) ⟨1877820, by rfl⟩ : syracuseStep 5007521 = 3755641) B3755641
theorem B3338347 : Blo 1977435 3338347 := bstep (se 1 (by rfl) ⟨2503760, by rfl⟩ : syracuseStep 3338347 = 5007521) B5007521
theorem B4451129 : Blo 1977435 4451129 := bstep (se 2 (by rfl) ⟨1669173, by rfl⟩ : syracuseStep 4451129 = 3338347) B3338347
theorem B2967419 : Blo 1977435 2967419 := bstep (se 1 (by rfl) ⟨2225564, by rfl⟩ : syracuseStep 2967419 = 4451129) B4451129
theorem B1978279 : Blo 1977435 1978279 := bstep (se 1 (by rfl) ⟨1483709, by rfl⟩ : syracuseStep 1978279 = 2967419) B2967419
theorem B2225569 : Blo 1977435 2225569 := bbase (se 2 (by rfl) ⟨834588, by rfl⟩ : syracuseStep 2225569 = 1669177) (by norm_num)
theorem B2967425 : Blo 1977435 2967425 := bstep (se 2 (by rfl) ⟨1112784, by rfl⟩ : syracuseStep 2967425 = 2225569) B2225569
theorem B1978283 : Blo 1977435 1978283 := bstep (se 1 (by rfl) ⟨1483712, by rfl⟩ : syracuseStep 1978283 = 2967425) B2967425
theorem B5007541 : Blo 1977435 5007541 := bbase (se 5 (by rfl) ⟨234728, by rfl⟩ : syracuseStep 5007541 = 469457) (by norm_num)
theorem B6676721 : Blo 1977435 6676721 := bstep (se 2 (by rfl) ⟨2503770, by rfl⟩ : syracuseStep 6676721 = 5007541) B5007541
theorem B4451147 : Blo 1977435 4451147 := bstep (se 1 (by rfl) ⟨3338360, by rfl⟩ : syracuseStep 4451147 = 6676721) B6676721
theorem B2967431 : Blo 1977435 2967431 := bstep (se 1 (by rfl) ⟨2225573, by rfl⟩ : syracuseStep 2967431 = 4451147) B4451147
theorem B1978287 : Blo 1977435 1978287 := bstep (se 1 (by rfl) ⟨1483715, by rfl⟩ : syracuseStep 1978287 = 2967431) B2967431
theorem B2967437 : Blo 1977435 2967437 := bbase (se 3 (by rfl) ⟨556394, by rfl⟩ : syracuseStep 2967437 = 1112789) (by norm_num)
theorem B1978291 : Blo 1977435 1978291 := bstep (se 1 (by rfl) ⟨1483718, by rfl⟩ : syracuseStep 1978291 = 2967437) B2967437
theorem B4451165 : Blo 1977435 4451165 := bbase (se 3 (by rfl) ⟨834593, by rfl⟩ : syracuseStep 4451165 = 1669187) (by norm_num)
theorem B2967443 : Blo 1977435 2967443 := bstep (se 1 (by rfl) ⟨2225582, by rfl⟩ : syracuseStep 2967443 = 4451165) B4451165
theorem B1978295 : Blo 1977435 1978295 := bstep (se 1 (by rfl) ⟨1483721, by rfl⟩ : syracuseStep 1978295 = 2967443) B2967443
theorem B3338381 : Blo 1977435 3338381 := bbase (se 3 (by rfl) ⟨625946, by rfl⟩ : syracuseStep 3338381 = 1251893) (by norm_num)
theorem B2225587 : Blo 1977435 2225587 := bstep (se 1 (by rfl) ⟨1669190, by rfl⟩ : syracuseStep 2225587 = 3338381) B3338381
theorem B2967449 : Blo 1977435 2967449 := bstep (se 2 (by rfl) ⟨1112793, by rfl⟩ : syracuseStep 2967449 = 2225587) B2225587
theorem B1978299 : Blo 1977435 1978299 := bstep (se 1 (by rfl) ⟨1483724, by rfl⟩ : syracuseStep 1978299 = 2967449) B2967449
theorem B2855197 : Blo 1977435 2855197 := bbase (se 3 (by rfl) ⟨535349, by rfl⟩ : syracuseStep 2855197 = 1070699) (by norm_num)
theorem B3806929 : Blo 1977435 3806929 := bstep (se 2 (by rfl) ⟨1427598, by rfl⟩ : syracuseStep 3806929 = 2855197) B2855197
theorem B5075905 : Blo 1977435 5075905 := bstep (se 2 (by rfl) ⟨1903464, by rfl⟩ : syracuseStep 5075905 = 3806929) B3806929
theorem B6767873 : Blo 1977435 6767873 := bstep (se 2 (by rfl) ⟨2537952, by rfl⟩ : syracuseStep 6767873 = 5075905) B5075905
theorem B4511915 : Blo 1977435 4511915 := bstep (se 1 (by rfl) ⟨3383936, by rfl⟩ : syracuseStep 4511915 = 6767873) B6767873
theorem B3007943 : Blo 1977435 3007943 := bstep (se 1 (by rfl) ⟨2255957, by rfl⟩ : syracuseStep 3007943 = 4511915) B4511915
theorem B2005295 : Blo 1977435 2005295 := bstep (se 1 (by rfl) ⟨1503971, by rfl⟩ : syracuseStep 2005295 = 3007943) B3007943
theorem B5347453 : Blo 1977435 5347453 := bstep (se 3 (by rfl) ⟨1002647, by rfl⟩ : syracuseStep 5347453 = 2005295) B2005295
theorem B7129937 : Blo 1977435 7129937 := bstep (se 2 (by rfl) ⟨2673726, by rfl⟩ : syracuseStep 7129937 = 5347453) B5347453
theorem B4753291 : Blo 1977435 4753291 := bstep (se 1 (by rfl) ⟨3564968, by rfl⟩ : syracuseStep 4753291 = 7129937) B7129937
theorem B6337721 : Blo 1977435 6337721 := bstep (se 2 (by rfl) ⟨2376645, by rfl⟩ : syracuseStep 6337721 = 4753291) B4753291
theorem B16900589 : Blo 1977435 16900589 := bstep (se 3 (by rfl) ⟨3168860, by rfl⟩ : syracuseStep 16900589 = 6337721) B6337721
theorem B11267059 : Blo 1977435 11267059 := bstep (se 1 (by rfl) ⟨8450294, by rfl⟩ : syracuseStep 11267059 = 16900589) B16900589
theorem B15022745 : Blo 1977435 15022745 := bstep (se 2 (by rfl) ⟨5633529, by rfl⟩ : syracuseStep 15022745 = 11267059) B11267059
theorem B10015163 : Blo 1977435 10015163 := bstep (se 1 (by rfl) ⟨7511372, by rfl⟩ : syracuseStep 10015163 = 15022745) B15022745
theorem B6676775 : Blo 1977435 6676775 := bstep (se 1 (by rfl) ⟨5007581, by rfl⟩ : syracuseStep 6676775 = 10015163) B10015163
theorem B4451183 : Blo 1977435 4451183 := bstep (se 1 (by rfl) ⟨3338387, by rfl⟩ : syracuseStep 4451183 = 6676775) B6676775
theorem B2967455 : Blo 1977435 2967455 := bstep (se 1 (by rfl) ⟨2225591, by rfl⟩ : syracuseStep 2967455 = 4451183) B4451183
theorem B1978303 : Blo 1977435 1978303 := bstep (se 1 (by rfl) ⟨1483727, by rfl⟩ : syracuseStep 1978303 = 2967455) B2967455
theorem B2967461 : Blo 1977435 2967461 := bbase (se 4 (by rfl) ⟨278199, by rfl⟩ : syracuseStep 2967461 = 556399) (by norm_num)
theorem B1978307 : Blo 1977435 1978307 := bstep (se 1 (by rfl) ⟨1483730, by rfl⟩ : syracuseStep 1978307 = 2967461) B2967461
theorem B2503801 : Blo 1977435 2503801 := bbase (se 2 (by rfl) ⟨938925, by rfl⟩ : syracuseStep 2503801 = 1877851) (by norm_num)
theorem B3338401 : Blo 1977435 3338401 := bstep (se 2 (by rfl) ⟨1251900, by rfl⟩ : syracuseStep 3338401 = 2503801) B2503801
theorem B4451201 : Blo 1977435 4451201 := bstep (se 2 (by rfl) ⟨1669200, by rfl⟩ : syracuseStep 4451201 = 3338401) B3338401
theorem B2967467 : Blo 1977435 2967467 := bstep (se 1 (by rfl) ⟨2225600, by rfl⟩ : syracuseStep 2967467 = 4451201) B4451201
theorem B1978311 : Blo 1977435 1978311 := bstep (se 1 (by rfl) ⟨1483733, by rfl⟩ : syracuseStep 1978311 = 2967467) B2967467
theorem B2225605 : Blo 1977435 2225605 := bbase (se 4 (by rfl) ⟨208650, by rfl⟩ : syracuseStep 2225605 = 417301) (by norm_num)
theorem B2967473 : Blo 1977435 2967473 := bstep (se 2 (by rfl) ⟨1112802, by rfl⟩ : syracuseStep 2967473 = 2225605) B2225605
theorem B1978315 : Blo 1977435 1978315 := bstep (se 1 (by rfl) ⟨1483736, by rfl⟩ : syracuseStep 1978315 = 2967473) B2967473
theorem B3755717 : Blo 1977435 3755717 := bbase (se 4 (by rfl) ⟨352098, by rfl⟩ : syracuseStep 3755717 = 704197) (by norm_num)
theorem B2503811 : Blo 1977435 2503811 := bstep (se 1 (by rfl) ⟨1877858, by rfl⟩ : syracuseStep 2503811 = 3755717) B3755717
theorem B6676829 : Blo 1977435 6676829 := bstep (se 3 (by rfl) ⟨1251905, by rfl⟩ : syracuseStep 6676829 = 2503811) B2503811
theorem B4451219 : Blo 1977435 4451219 := bstep (se 1 (by rfl) ⟨3338414, by rfl⟩ : syracuseStep 4451219 = 6676829) B6676829
theorem B2967479 : Blo 1977435 2967479 := bstep (se 1 (by rfl) ⟨2225609, by rfl⟩ : syracuseStep 2967479 = 4451219) B4451219
theorem B1978319 : Blo 1977435 1978319 := bstep (se 1 (by rfl) ⟨1483739, by rfl⟩ : syracuseStep 1978319 = 2967479) B2967479
theorem B2967485 : Blo 1977435 2967485 := bbase (se 3 (by rfl) ⟨556403, by rfl⟩ : syracuseStep 2967485 = 1112807) (by norm_num)
theorem B1978323 : Blo 1977435 1978323 := bstep (se 1 (by rfl) ⟨1483742, by rfl⟩ : syracuseStep 1978323 = 2967485) B2967485
theorem B4451237 : Blo 1977435 4451237 := bbase (se 4 (by rfl) ⟨417303, by rfl⟩ : syracuseStep 4451237 = 834607) (by norm_num)
theorem B2967491 : Blo 1977435 2967491 := bstep (se 1 (by rfl) ⟨2225618, by rfl⟩ : syracuseStep 2967491 = 4451237) B4451237
theorem B1978327 : Blo 1977435 1978327 := bstep (se 1 (by rfl) ⟨1483745, by rfl⟩ : syracuseStep 1978327 = 2967491) B2967491
theorem B5007653 : Blo 1977435 5007653 := bbase (se 4 (by rfl) ⟨469467, by rfl⟩ : syracuseStep 5007653 = 938935) (by norm_num)
theorem B3338435 : Blo 1977435 3338435 := bstep (se 1 (by rfl) ⟨2503826, by rfl⟩ : syracuseStep 3338435 = 5007653) B5007653
theorem B2225623 : Blo 1977435 2225623 := bstep (se 1 (by rfl) ⟨1669217, by rfl⟩ : syracuseStep 2225623 = 3338435) B3338435
theorem B2967497 : Blo 1977435 2967497 := bstep (se 2 (by rfl) ⟨1112811, by rfl⟩ : syracuseStep 2967497 = 2225623) B2225623
theorem B1978331 : Blo 1977435 1978331 := bstep (se 1 (by rfl) ⟨1483748, by rfl⟩ : syracuseStep 1978331 = 2967497) B2967497
theorem B5633621 : Blo 1977435 5633621 := bbase (se 8 (by rfl) ⟨33009, by rfl⟩ : syracuseStep 5633621 = 66019) (by norm_num)
theorem B3755747 : Blo 1977435 3755747 := bstep (se 1 (by rfl) ⟨2816810, by rfl⟩ : syracuseStep 3755747 = 5633621) B5633621
theorem B10015325 : Blo 1977435 10015325 := bstep (se 3 (by rfl) ⟨1877873, by rfl⟩ : syracuseStep 10015325 = 3755747) B3755747
theorem B6676883 : Blo 1977435 6676883 := bstep (se 1 (by rfl) ⟨5007662, by rfl⟩ : syracuseStep 6676883 = 10015325) B10015325
theorem B4451255 : Blo 1977435 4451255 := bstep (se 1 (by rfl) ⟨3338441, by rfl⟩ : syracuseStep 4451255 = 6676883) B6676883
theorem B2967503 : Blo 1977435 2967503 := bstep (se 1 (by rfl) ⟨2225627, by rfl⟩ : syracuseStep 2967503 = 4451255) B4451255
theorem B1978335 : Blo 1977435 1978335 := bstep (se 1 (by rfl) ⟨1483751, by rfl⟩ : syracuseStep 1978335 = 2967503) B2967503
theorem B2967509 : Blo 1977435 2967509 := bbase (se 7 (by rfl) ⟨34775, by rfl⟩ : syracuseStep 2967509 = 69551) (by norm_num)
theorem B1978339 : Blo 1977435 1978339 := bstep (se 1 (by rfl) ⟨1483754, by rfl⟩ : syracuseStep 1978339 = 2967509) B2967509
theorem B7511525 : Blo 1977435 7511525 := bbase (se 4 (by rfl) ⟨704205, by rfl⟩ : syracuseStep 7511525 = 1408411) (by norm_num)
theorem B5007683 : Blo 1977435 5007683 := bstep (se 1 (by rfl) ⟨3755762, by rfl⟩ : syracuseStep 5007683 = 7511525) B7511525
theorem B3338455 : Blo 1977435 3338455 := bstep (se 1 (by rfl) ⟨2503841, by rfl⟩ : syracuseStep 3338455 = 5007683) B5007683
theorem B4451273 : Blo 1977435 4451273 := bstep (se 2 (by rfl) ⟨1669227, by rfl⟩ : syracuseStep 4451273 = 3338455) B3338455
theorem B2967515 : Blo 1977435 2967515 := bstep (se 1 (by rfl) ⟨2225636, by rfl⟩ : syracuseStep 2967515 = 4451273) B4451273
theorem B1978343 : Blo 1977435 1978343 := bstep (se 1 (by rfl) ⟨1483757, by rfl⟩ : syracuseStep 1978343 = 2967515) B2967515
theorem B2225641 : Blo 1977435 2225641 := bbase (se 2 (by rfl) ⟨834615, by rfl⟩ : syracuseStep 2225641 = 1669231) (by norm_num)
theorem B2967521 : Blo 1977435 2967521 := bstep (se 2 (by rfl) ⟨1112820, by rfl⟩ : syracuseStep 2967521 = 2225641) B2225641
theorem B1978347 : Blo 1977435 1978347 := bstep (se 1 (by rfl) ⟨1483760, by rfl⟩ : syracuseStep 1978347 = 2967521) B2967521
theorem B2112625 : Blo 1977435 2112625 := bbase (se 2 (by rfl) ⟨792234, by rfl⟩ : syracuseStep 2112625 = 1584469) (by norm_num)
theorem B11267333 : Blo 1977435 11267333 := bstep (se 4 (by rfl) ⟨1056312, by rfl⟩ : syracuseStep 11267333 = 2112625) B2112625
theorem B7511555 : Blo 1977435 7511555 := bstep (se 1 (by rfl) ⟨5633666, by rfl⟩ : syracuseStep 7511555 = 11267333) B11267333
theorem B5007703 : Blo 1977435 5007703 := bstep (se 1 (by rfl) ⟨3755777, by rfl⟩ : syracuseStep 5007703 = 7511555) B7511555
theorem B6676937 : Blo 1977435 6676937 := bstep (se 2 (by rfl) ⟨2503851, by rfl⟩ : syracuseStep 6676937 = 5007703) B5007703
theorem B4451291 : Blo 1977435 4451291 := bstep (se 1 (by rfl) ⟨3338468, by rfl⟩ : syracuseStep 4451291 = 6676937) B6676937
theorem B2967527 : Blo 1977435 2967527 := bstep (se 1 (by rfl) ⟨2225645, by rfl⟩ : syracuseStep 2967527 = 4451291) B4451291
theorem B1978351 : Blo 1977435 1978351 := bstep (se 1 (by rfl) ⟨1483763, by rfl⟩ : syracuseStep 1978351 = 2967527) B2967527
theorem B2967533 : Blo 1977435 2967533 := bbase (se 3 (by rfl) ⟨556412, by rfl⟩ : syracuseStep 2967533 = 1112825) (by norm_num)
theorem B1978355 : Blo 1977435 1978355 := bstep (se 1 (by rfl) ⟨1483766, by rfl⟩ : syracuseStep 1978355 = 2967533) B2967533
theorem B4451309 : Blo 1977435 4451309 := bbase (se 3 (by rfl) ⟨834620, by rfl⟩ : syracuseStep 4451309 = 1669241) (by norm_num)
theorem B2967539 : Blo 1977435 2967539 := bstep (se 1 (by rfl) ⟨2225654, by rfl⟩ : syracuseStep 2967539 = 4451309) B4451309
theorem B1978359 : Blo 1977435 1978359 := bstep (se 1 (by rfl) ⟨1483769, by rfl⟩ : syracuseStep 1978359 = 2967539) B2967539
theorem B4225277 : Blo 1977435 4225277 := bbase (se 3 (by rfl) ⟨792239, by rfl⟩ : syracuseStep 4225277 = 1584479) (by norm_num)
theorem B2816851 : Blo 1977435 2816851 := bstep (se 1 (by rfl) ⟨2112638, by rfl⟩ : syracuseStep 2816851 = 4225277) B4225277
theorem B3755801 : Blo 1977435 3755801 := bstep (se 2 (by rfl) ⟨1408425, by rfl⟩ : syracuseStep 3755801 = 2816851) B2816851
theorem B2503867 : Blo 1977435 2503867 := bstep (se 1 (by rfl) ⟨1877900, by rfl⟩ : syracuseStep 2503867 = 3755801) B3755801
theorem B3338489 : Blo 1977435 3338489 := bstep (se 2 (by rfl) ⟨1251933, by rfl⟩ : syracuseStep 3338489 = 2503867) B2503867
theorem B2225659 : Blo 1977435 2225659 := bstep (se 1 (by rfl) ⟨1669244, by rfl⟩ : syracuseStep 2225659 = 3338489) B3338489
theorem B2967545 : Blo 1977435 2967545 := bstep (se 2 (by rfl) ⟨1112829, by rfl⟩ : syracuseStep 2967545 = 2225659) B2225659
theorem B1978363 : Blo 1977435 1978363 := bstep (se 1 (by rfl) ⟨1483772, by rfl⟩ : syracuseStep 1978363 = 2967545) B2967545
theorem B144385877 : Blo 1977435 144385877 := bbase (se 9 (by rfl) ⟨423005, by rfl⟩ : syracuseStep 144385877 = 846011) (by norm_num)
theorem B96257251 : Blo 1977435 96257251 := bstep (se 1 (by rfl) ⟨72192938, by rfl⟩ : syracuseStep 96257251 = 144385877) B144385877
theorem B128343001 : Blo 1977435 128343001 := bstep (se 2 (by rfl) ⟨48128625, by rfl⟩ : syracuseStep 128343001 = 96257251) B96257251
theorem B171124001 : Blo 1977435 171124001 := bstep (se 2 (by rfl) ⟨64171500, by rfl⟩ : syracuseStep 171124001 = 128343001) B128343001
theorem B114082667 : Blo 1977435 114082667 := bstep (se 1 (by rfl) ⟨85562000, by rfl⟩ : syracuseStep 114082667 = 171124001) B171124001
theorem B76055111 : Blo 1977435 76055111 := bstep (se 1 (by rfl) ⟨57041333, by rfl⟩ : syracuseStep 76055111 = 114082667) B114082667
theorem B50703407 : Blo 1977435 50703407 := bstep (se 1 (by rfl) ⟨38027555, by rfl⟩ : syracuseStep 50703407 = 76055111) B76055111
theorem B33802271 : Blo 1977435 33802271 := bstep (se 1 (by rfl) ⟨25351703, by rfl⟩ : syracuseStep 33802271 = 50703407) B50703407
theorem B22534847 : Blo 1977435 22534847 := bstep (se 1 (by rfl) ⟨16901135, by rfl⟩ : syracuseStep 22534847 = 33802271) B33802271
theorem B15023231 : Blo 1977435 15023231 := bstep (se 1 (by rfl) ⟨11267423, by rfl⟩ : syracuseStep 15023231 = 22534847) B22534847
theorem B10015487 : Blo 1977435 10015487 := bstep (se 1 (by rfl) ⟨7511615, by rfl⟩ : syracuseStep 10015487 = 15023231) B15023231
theorem B6676991 : Blo 1977435 6676991 := bstep (se 1 (by rfl) ⟨5007743, by rfl⟩ : syracuseStep 6676991 = 10015487) B10015487
theorem B4451327 : Blo 1977435 4451327 := bstep (se 1 (by rfl) ⟨3338495, by rfl⟩ : syracuseStep 4451327 = 6676991) B6676991
theorem B2967551 : Blo 1977435 2967551 := bstep (se 1 (by rfl) ⟨2225663, by rfl⟩ : syracuseStep 2967551 = 4451327) B4451327
theorem B1978367 : Blo 1977435 1978367 := bstep (se 1 (by rfl) ⟨1483775, by rfl⟩ : syracuseStep 1978367 = 2967551) B2967551
theorem B2967557 : Blo 1977435 2967557 := bbase (se 4 (by rfl) ⟨278208, by rfl⟩ : syracuseStep 2967557 = 556417) (by norm_num)
theorem B1978371 : Blo 1977435 1978371 := bstep (se 1 (by rfl) ⟨1483778, by rfl⟩ : syracuseStep 1978371 = 2967557) B2967557
theorem B3338509 : Blo 1977435 3338509 := bbase (se 3 (by rfl) ⟨625970, by rfl⟩ : syracuseStep 3338509 = 1251941) (by norm_num)
theorem B4451345 : Blo 1977435 4451345 := bstep (se 2 (by rfl) ⟨1669254, by rfl⟩ : syracuseStep 4451345 = 3338509) B3338509
theorem B2967563 : Blo 1977435 2967563 := bstep (se 1 (by rfl) ⟨2225672, by rfl⟩ : syracuseStep 2967563 = 4451345) B4451345
theorem B1978375 : Blo 1977435 1978375 := bstep (se 1 (by rfl) ⟨1483781, by rfl⟩ : syracuseStep 1978375 = 2967563) B2967563
theorem B2225677 : Blo 1977435 2225677 := bbase (se 3 (by rfl) ⟨417314, by rfl⟩ : syracuseStep 2225677 = 834629) (by norm_num)
theorem B2967569 : Blo 1977435 2967569 := bstep (se 2 (by rfl) ⟨1112838, by rfl⟩ : syracuseStep 2967569 = 2225677) B2225677
theorem B1978379 : Blo 1977435 1978379 := bstep (se 1 (by rfl) ⟨1483784, by rfl⟩ : syracuseStep 1978379 = 2967569) B2967569
theorem B6677045 : Blo 1977435 6677045 := bbase (se 5 (by rfl) ⟨312986, by rfl⟩ : syracuseStep 6677045 = 625973) (by norm_num)
theorem B4451363 : Blo 1977435 4451363 := bstep (se 1 (by rfl) ⟨3338522, by rfl⟩ : syracuseStep 4451363 = 6677045) B6677045
theorem B2967575 : Blo 1977435 2967575 := bstep (se 1 (by rfl) ⟨2225681, by rfl⟩ : syracuseStep 2967575 = 4451363) B4451363
theorem B1978383 : Blo 1977435 1978383 := bstep (se 1 (by rfl) ⟨1483787, by rfl⟩ : syracuseStep 1978383 = 2967575) B2967575
theorem B2967581 : Blo 1977435 2967581 := bbase (se 3 (by rfl) ⟨556421, by rfl⟩ : syracuseStep 2967581 = 1112843) (by norm_num)
theorem B1978387 : Blo 1977435 1978387 := bstep (se 1 (by rfl) ⟨1483790, by rfl⟩ : syracuseStep 1978387 = 2967581) B2967581
theorem B4451381 : Blo 1977435 4451381 := bbase (se 5 (by rfl) ⟨208658, by rfl⟩ : syracuseStep 4451381 = 417317) (by norm_num)
theorem B2967587 : Blo 1977435 2967587 := bstep (se 1 (by rfl) ⟨2225690, by rfl⟩ : syracuseStep 2967587 = 4451381) B4451381
theorem B1978391 : Blo 1977435 1978391 := bstep (se 1 (by rfl) ⟨1483793, by rfl⟩ : syracuseStep 1978391 = 2967587) B2967587
theorem B4512125 : Blo 1977435 4512125 := bbase (se 3 (by rfl) ⟨846023, by rfl⟩ : syracuseStep 4512125 = 1692047) (by norm_num)
theorem B12032333 : Blo 1977435 12032333 := bstep (se 3 (by rfl) ⟨2256062, by rfl⟩ : syracuseStep 12032333 = 4512125) B4512125
theorem B8021555 : Blo 1977435 8021555 := bstep (se 1 (by rfl) ⟨6016166, by rfl⟩ : syracuseStep 8021555 = 12032333) B12032333
theorem B5347703 : Blo 1977435 5347703 := bstep (se 1 (by rfl) ⟨4010777, by rfl⟩ : syracuseStep 5347703 = 8021555) B8021555
theorem B3565135 : Blo 1977435 3565135 := bstep (se 1 (by rfl) ⟨2673851, by rfl⟩ : syracuseStep 3565135 = 5347703) B5347703
theorem B4753513 : Blo 1977435 4753513 := bstep (se 2 (by rfl) ⟨1782567, by rfl⟩ : syracuseStep 4753513 = 3565135) B3565135
theorem B6338017 : Blo 1977435 6338017 := bstep (se 2 (by rfl) ⟨2376756, by rfl⟩ : syracuseStep 6338017 = 4753513) B4753513
theorem B8450689 : Blo 1977435 8450689 := bstep (se 2 (by rfl) ⟨3169008, by rfl⟩ : syracuseStep 8450689 = 6338017) B6338017
theorem B11267585 : Blo 1977435 11267585 := bstep (se 2 (by rfl) ⟨4225344, by rfl⟩ : syracuseStep 11267585 = 8450689) B8450689
theorem B7511723 : Blo 1977435 7511723 := bstep (se 1 (by rfl) ⟨5633792, by rfl⟩ : syracuseStep 7511723 = 11267585) B11267585
theorem B5007815 : Blo 1977435 5007815 := bstep (se 1 (by rfl) ⟨3755861, by rfl⟩ : syracuseStep 5007815 = 7511723) B7511723
theorem B3338543 : Blo 1977435 3338543 := bstep (se 1 (by rfl) ⟨2503907, by rfl⟩ : syracuseStep 3338543 = 5007815) B5007815
theorem B2225695 : Blo 1977435 2225695 := bstep (se 1 (by rfl) ⟨1669271, by rfl⟩ : syracuseStep 2225695 = 3338543) B3338543
theorem B2967593 : Blo 1977435 2967593 := bstep (se 2 (by rfl) ⟨1112847, by rfl⟩ : syracuseStep 2967593 = 2225695) B2225695
theorem B1978395 : Blo 1977435 1978395 := bstep (se 1 (by rfl) ⟨1483796, by rfl⟩ : syracuseStep 1978395 = 2967593) B2967593
theorem B2376761 : Blo 1977435 2376761 := bbase (se 2 (by rfl) ⟨891285, by rfl⟩ : syracuseStep 2376761 = 1782571) (by norm_num)
theorem B6338029 : Blo 1977435 6338029 := bstep (se 3 (by rfl) ⟨1188380, by rfl⟩ : syracuseStep 6338029 = 2376761) B2376761
theorem B8450705 : Blo 1977435 8450705 := bstep (se 2 (by rfl) ⟨3169014, by rfl⟩ : syracuseStep 8450705 = 6338029) B6338029
theorem B5633803 : Blo 1977435 5633803 := bstep (se 1 (by rfl) ⟨4225352, by rfl⟩ : syracuseStep 5633803 = 8450705) B8450705
theorem B7511737 : Blo 1977435 7511737 := bstep (se 2 (by rfl) ⟨2816901, by rfl⟩ : syracuseStep 7511737 = 5633803) B5633803
theorem B10015649 : Blo 1977435 10015649 := bstep (se 2 (by rfl) ⟨3755868, by rfl⟩ : syracuseStep 10015649 = 7511737) B7511737
theorem B6677099 : Blo 1977435 6677099 := bstep (se 1 (by rfl) ⟨5007824, by rfl⟩ : syracuseStep 6677099 = 10015649) B10015649
theorem B4451399 : Blo 1977435 4451399 := bstep (se 1 (by rfl) ⟨3338549, by rfl⟩ : syracuseStep 4451399 = 6677099) B6677099
theorem B2967599 : Blo 1977435 2967599 := bstep (se 1 (by rfl) ⟨2225699, by rfl⟩ : syracuseStep 2967599 = 4451399) B4451399
theorem B1978399 : Blo 1977435 1978399 := bstep (se 1 (by rfl) ⟨1483799, by rfl⟩ : syracuseStep 1978399 = 2967599) B2967599
theorem B2967605 : Blo 1977435 2967605 := bbase (se 5 (by rfl) ⟨139106, by rfl⟩ : syracuseStep 2967605 = 278213) (by norm_num)
theorem B1978403 : Blo 1977435 1978403 := bstep (se 1 (by rfl) ⟨1483802, by rfl⟩ : syracuseStep 1978403 = 2967605) B2967605
theorem B5007845 : Blo 1977435 5007845 := bbase (se 4 (by rfl) ⟨469485, by rfl⟩ : syracuseStep 5007845 = 938971) (by norm_num)
theorem B3338563 : Blo 1977435 3338563 := bstep (se 1 (by rfl) ⟨2503922, by rfl⟩ : syracuseStep 3338563 = 5007845) B5007845
theorem B4451417 : Blo 1977435 4451417 := bstep (se 2 (by rfl) ⟨1669281, by rfl⟩ : syracuseStep 4451417 = 3338563) B3338563
theorem B2967611 : Blo 1977435 2967611 := bstep (se 1 (by rfl) ⟨2225708, by rfl⟩ : syracuseStep 2967611 = 4451417) B4451417
theorem B1978407 : Blo 1977435 1978407 := bstep (se 1 (by rfl) ⟨1483805, by rfl⟩ : syracuseStep 1978407 = 2967611) B2967611
theorem B2225713 : Blo 1977435 2225713 := bbase (se 2 (by rfl) ⟨834642, by rfl⟩ : syracuseStep 2225713 = 1669285) (by norm_num)
theorem B2967617 : Blo 1977435 2967617 := bstep (se 2 (by rfl) ⟨1112856, by rfl⟩ : syracuseStep 2967617 = 2225713) B2225713
theorem B1978411 : Blo 1977435 1978411 := bstep (se 1 (by rfl) ⟨1483808, by rfl⟩ : syracuseStep 1978411 = 2967617) B2967617
theorem B2005409 : Blo 1977435 2005409 := bbase (se 2 (by rfl) ⟨752028, by rfl⟩ : syracuseStep 2005409 = 1504057) (by norm_num)
theorem B5347757 : Blo 1977435 5347757 := bstep (se 3 (by rfl) ⟨1002704, by rfl⟩ : syracuseStep 5347757 = 2005409) B2005409
theorem B3565171 : Blo 1977435 3565171 := bstep (se 1 (by rfl) ⟨2673878, by rfl⟩ : syracuseStep 3565171 = 5347757) B5347757
theorem B4753561 : Blo 1977435 4753561 := bstep (se 2 (by rfl) ⟨1782585, by rfl⟩ : syracuseStep 4753561 = 3565171) B3565171
theorem B6338081 : Blo 1977435 6338081 := bstep (se 2 (by rfl) ⟨2376780, by rfl⟩ : syracuseStep 6338081 = 4753561) B4753561
theorem B4225387 : Blo 1977435 4225387 := bstep (se 1 (by rfl) ⟨3169040, by rfl⟩ : syracuseStep 4225387 = 6338081) B6338081
theorem B5633849 : Blo 1977435 5633849 := bstep (se 2 (by rfl) ⟨2112693, by rfl⟩ : syracuseStep 5633849 = 4225387) B4225387
theorem B3755899 : Blo 1977435 3755899 := bstep (se 1 (by rfl) ⟨2816924, by rfl⟩ : syracuseStep 3755899 = 5633849) B5633849
theorem B5007865 : Blo 1977435 5007865 := bstep (se 2 (by rfl) ⟨1877949, by rfl⟩ : syracuseStep 5007865 = 3755899) B3755899
theorem B6677153 : Blo 1977435 6677153 := bstep (se 2 (by rfl) ⟨2503932, by rfl⟩ : syracuseStep 6677153 = 5007865) B5007865
theorem B4451435 : Blo 1977435 4451435 := bstep (se 1 (by rfl) ⟨3338576, by rfl⟩ : syracuseStep 4451435 = 6677153) B6677153
theorem B2967623 : Blo 1977435 2967623 := bstep (se 1 (by rfl) ⟨2225717, by rfl⟩ : syracuseStep 2967623 = 4451435) B4451435
theorem B1978415 : Blo 1977435 1978415 := bstep (se 1 (by rfl) ⟨1483811, by rfl⟩ : syracuseStep 1978415 = 2967623) B2967623
theorem B2967629 : Blo 1977435 2967629 := bbase (se 3 (by rfl) ⟨556430, by rfl⟩ : syracuseStep 2967629 = 1112861) (by norm_num)
theorem B1978419 : Blo 1977435 1978419 := bstep (se 1 (by rfl) ⟨1483814, by rfl⟩ : syracuseStep 1978419 = 2967629) B2967629
theorem B4451453 : Blo 1977435 4451453 := bbase (se 3 (by rfl) ⟨834647, by rfl⟩ : syracuseStep 4451453 = 1669295) (by norm_num)
theorem B2967635 : Blo 1977435 2967635 := bstep (se 1 (by rfl) ⟨2225726, by rfl⟩ : syracuseStep 2967635 = 4451453) B4451453
theorem B1978423 : Blo 1977435 1978423 := bstep (se 1 (by rfl) ⟨1483817, by rfl⟩ : syracuseStep 1978423 = 2967635) B2967635
theorem B3338597 : Blo 1977435 3338597 := bbase (se 4 (by rfl) ⟨312993, by rfl⟩ : syracuseStep 3338597 = 625987) (by norm_num)
theorem B2225731 : Blo 1977435 2225731 := bstep (se 1 (by rfl) ⟨1669298, by rfl⟩ : syracuseStep 2225731 = 3338597) B3338597
theorem B2967641 : Blo 1977435 2967641 := bstep (se 2 (by rfl) ⟨1112865, by rfl⟩ : syracuseStep 2967641 = 2225731) B2225731
theorem B1978427 : Blo 1977435 1978427 := bstep (se 1 (by rfl) ⟨1483820, by rfl⟩ : syracuseStep 1978427 = 2967641) B2967641
theorem B4225421 : Blo 1977435 4225421 := bbase (se 3 (by rfl) ⟨792266, by rfl⟩ : syracuseStep 4225421 = 1584533) (by norm_num)
theorem B2816947 : Blo 1977435 2816947 := bstep (se 1 (by rfl) ⟨2112710, by rfl⟩ : syracuseStep 2816947 = 4225421) B4225421
theorem B15023717 : Blo 1977435 15023717 := bstep (se 4 (by rfl) ⟨1408473, by rfl⟩ : syracuseStep 15023717 = 2816947) B2816947
theorem B10015811 : Blo 1977435 10015811 := bstep (se 1 (by rfl) ⟨7511858, by rfl⟩ : syracuseStep 10015811 = 15023717) B15023717
theorem B6677207 : Blo 1977435 6677207 := bstep (se 1 (by rfl) ⟨5007905, by rfl⟩ : syracuseStep 6677207 = 10015811) B10015811
theorem B4451471 : Blo 1977435 4451471 := bstep (se 1 (by rfl) ⟨3338603, by rfl⟩ : syracuseStep 4451471 = 6677207) B6677207
theorem B2967647 : Blo 1977435 2967647 := bstep (se 1 (by rfl) ⟨2225735, by rfl⟩ : syracuseStep 2967647 = 4451471) B4451471
theorem B1978431 : Blo 1977435 1978431 := bstep (se 1 (by rfl) ⟨1483823, by rfl⟩ : syracuseStep 1978431 = 2967647) B2967647
theorem B2967653 : Blo 1977435 2967653 := bbase (se 4 (by rfl) ⟨278217, by rfl⟩ : syracuseStep 2967653 = 556435) (by norm_num)
theorem B1978435 : Blo 1977435 1978435 := bstep (se 1 (by rfl) ⟨1483826, by rfl⟩ : syracuseStep 1978435 = 2967653) B2967653
theorem B8566181 : Blo 1977435 8566181 := bbase (se 4 (by rfl) ⟨803079, by rfl⟩ : syracuseStep 8566181 = 1606159) (by norm_num)
theorem B5710787 : Blo 1977435 5710787 := bstep (se 1 (by rfl) ⟨4283090, by rfl⟩ : syracuseStep 5710787 = 8566181) B8566181
theorem B3807191 : Blo 1977435 3807191 := bstep (se 1 (by rfl) ⟨2855393, by rfl⟩ : syracuseStep 3807191 = 5710787) B5710787
theorem B2538127 : Blo 1977435 2538127 := bstep (se 1 (by rfl) ⟨1903595, by rfl⟩ : syracuseStep 2538127 = 3807191) B3807191
theorem B3384169 : Blo 1977435 3384169 := bstep (se 2 (by rfl) ⟨1269063, by rfl⟩ : syracuseStep 3384169 = 2538127) B2538127
theorem B18048901 : Blo 1977435 18048901 := bstep (se 4 (by rfl) ⟨1692084, by rfl⟩ : syracuseStep 18048901 = 3384169) B3384169
theorem B24065201 : Blo 1977435 24065201 := bstep (se 2 (by rfl) ⟨9024450, by rfl⟩ : syracuseStep 24065201 = 18048901) B18048901
theorem B16043467 : Blo 1977435 16043467 := bstep (se 1 (by rfl) ⟨12032600, by rfl⟩ : syracuseStep 16043467 = 24065201) B24065201
theorem B21391289 : Blo 1977435 21391289 := bstep (se 2 (by rfl) ⟨8021733, by rfl⟩ : syracuseStep 21391289 = 16043467) B16043467
theorem B14260859 : Blo 1977435 14260859 := bstep (se 1 (by rfl) ⟨10695644, by rfl⟩ : syracuseStep 14260859 = 21391289) B21391289
theorem B9507239 : Blo 1977435 9507239 := bstep (se 1 (by rfl) ⟨7130429, by rfl⟩ : syracuseStep 9507239 = 14260859) B14260859
theorem B6338159 : Blo 1977435 6338159 := bstep (se 1 (by rfl) ⟨4753619, by rfl⟩ : syracuseStep 6338159 = 9507239) B9507239
theorem B4225439 : Blo 1977435 4225439 := bstep (se 1 (by rfl) ⟨3169079, by rfl⟩ : syracuseStep 4225439 = 6338159) B6338159
theorem B2816959 : Blo 1977435 2816959 := bstep (se 1 (by rfl) ⟨2112719, by rfl⟩ : syracuseStep 2816959 = 4225439) B4225439
theorem B3755945 : Blo 1977435 3755945 := bstep (se 2 (by rfl) ⟨1408479, by rfl⟩ : syracuseStep 3755945 = 2816959) B2816959
theorem B2503963 : Blo 1977435 2503963 := bstep (se 1 (by rfl) ⟨1877972, by rfl⟩ : syracuseStep 2503963 = 3755945) B3755945
theorem B3338617 : Blo 1977435 3338617 := bstep (se 2 (by rfl) ⟨1251981, by rfl⟩ : syracuseStep 3338617 = 2503963) B2503963
theorem B4451489 : Blo 1977435 4451489 := bstep (se 2 (by rfl) ⟨1669308, by rfl⟩ : syracuseStep 4451489 = 3338617) B3338617
theorem B2967659 : Blo 1977435 2967659 := bstep (se 1 (by rfl) ⟨2225744, by rfl⟩ : syracuseStep 2967659 = 4451489) B4451489
theorem B1978439 : Blo 1977435 1978439 := bstep (se 1 (by rfl) ⟨1483829, by rfl⟩ : syracuseStep 1978439 = 2967659) B2967659
theorem B2225749 : Blo 1977435 2225749 := bbase (se 8 (by rfl) ⟨13041, by rfl⟩ : syracuseStep 2225749 = 26083) (by norm_num)
theorem B2967665 : Blo 1977435 2967665 := bstep (se 2 (by rfl) ⟨1112874, by rfl⟩ : syracuseStep 2967665 = 2225749) B2225749
theorem B1978443 : Blo 1977435 1978443 := bstep (se 1 (by rfl) ⟨1483832, by rfl⟩ : syracuseStep 1978443 = 2967665) B2967665
theorem B2503973 : Blo 1977435 2503973 := bbase (se 4 (by rfl) ⟨234747, by rfl⟩ : syracuseStep 2503973 = 469495) (by norm_num)
theorem B6677261 : Blo 1977435 6677261 := bstep (se 3 (by rfl) ⟨1251986, by rfl⟩ : syracuseStep 6677261 = 2503973) B2503973
theorem B4451507 : Blo 1977435 4451507 := bstep (se 1 (by rfl) ⟨3338630, by rfl⟩ : syracuseStep 4451507 = 6677261) B6677261
theorem B2967671 : Blo 1977435 2967671 := bstep (se 1 (by rfl) ⟨2225753, by rfl⟩ : syracuseStep 2967671 = 4451507) B4451507
theorem B1978447 : Blo 1977435 1978447 := bstep (se 1 (by rfl) ⟨1483835, by rfl⟩ : syracuseStep 1978447 = 2967671) B2967671
theorem B2967677 : Blo 1977435 2967677 := bbase (se 3 (by rfl) ⟨556439, by rfl⟩ : syracuseStep 2967677 = 1112879) (by norm_num)
theorem B1978451 : Blo 1977435 1978451 := bstep (se 1 (by rfl) ⟨1483838, by rfl⟩ : syracuseStep 1978451 = 2967677) B2967677
theorem B4451525 : Blo 1977435 4451525 := bbase (se 4 (by rfl) ⟨417330, by rfl⟩ : syracuseStep 4451525 = 834661) (by norm_num)
theorem B2967683 : Blo 1977435 2967683 := bstep (se 1 (by rfl) ⟨2225762, by rfl⟩ : syracuseStep 2967683 = 4451525) B4451525
theorem B1978455 : Blo 1977435 1978455 := bstep (se 1 (by rfl) ⟨1483841, by rfl⟩ : syracuseStep 1978455 = 2967683) B2967683
theorem B7130501 : Blo 1977435 7130501 := bbase (se 4 (by rfl) ⟨668484, by rfl⟩ : syracuseStep 7130501 = 1336969) (by norm_num)
theorem B4753667 : Blo 1977435 4753667 := bstep (se 1 (by rfl) ⟨3565250, by rfl⟩ : syracuseStep 4753667 = 7130501) B7130501
theorem B12676445 : Blo 1977435 12676445 := bstep (se 3 (by rfl) ⟨2376833, by rfl⟩ : syracuseStep 12676445 = 4753667) B4753667
theorem B8450963 : Blo 1977435 8450963 := bstep (se 1 (by rfl) ⟨6338222, by rfl⟩ : syracuseStep 8450963 = 12676445) B12676445
theorem B5633975 : Blo 1977435 5633975 := bstep (se 1 (by rfl) ⟨4225481, by rfl⟩ : syracuseStep 5633975 = 8450963) B8450963
theorem B3755983 : Blo 1977435 3755983 := bstep (se 1 (by rfl) ⟨2816987, by rfl⟩ : syracuseStep 3755983 = 5633975) B5633975
theorem B5007977 : Blo 1977435 5007977 := bstep (se 2 (by rfl) ⟨1877991, by rfl⟩ : syracuseStep 5007977 = 3755983) B3755983
theorem B3338651 : Blo 1977435 3338651 := bstep (se 1 (by rfl) ⟨2503988, by rfl⟩ : syracuseStep 3338651 = 5007977) B5007977
theorem B2225767 : Blo 1977435 2225767 := bstep (se 1 (by rfl) ⟨1669325, by rfl⟩ : syracuseStep 2225767 = 3338651) B3338651
theorem B2967689 : Blo 1977435 2967689 := bstep (se 2 (by rfl) ⟨1112883, by rfl⟩ : syracuseStep 2967689 = 2225767) B2225767
theorem B1978459 : Blo 1977435 1978459 := bstep (se 1 (by rfl) ⟨1483844, by rfl⟩ : syracuseStep 1978459 = 2967689) B2967689
theorem B10015973 : Blo 1977435 10015973 := bbase (se 4 (by rfl) ⟨938997, by rfl⟩ : syracuseStep 10015973 = 1877995) (by norm_num)
theorem B6677315 : Blo 1977435 6677315 := bstep (se 1 (by rfl) ⟨5007986, by rfl⟩ : syracuseStep 6677315 = 10015973) B10015973
theorem B4451543 : Blo 1977435 4451543 := bstep (se 1 (by rfl) ⟨3338657, by rfl⟩ : syracuseStep 4451543 = 6677315) B6677315
theorem B2967695 : Blo 1977435 2967695 := bstep (se 1 (by rfl) ⟨2225771, by rfl⟩ : syracuseStep 2967695 = 4451543) B4451543
theorem B1978463 : Blo 1977435 1978463 := bstep (se 1 (by rfl) ⟨1483847, by rfl⟩ : syracuseStep 1978463 = 2967695) B2967695
theorem B2967701 : Blo 1977435 2967701 := bbase (se 6 (by rfl) ⟨69555, by rfl⟩ : syracuseStep 2967701 = 139111) (by norm_num)
theorem B1978467 : Blo 1977435 1978467 := bstep (se 1 (by rfl) ⟨1483850, by rfl⟩ : syracuseStep 1978467 = 2967701) B2967701
theorem B8451013 : Blo 1977435 8451013 := bbase (se 4 (by rfl) ⟨792282, by rfl⟩ : syracuseStep 8451013 = 1584565) (by norm_num)
theorem B11268017 : Blo 1977435 11268017 := bstep (se 2 (by rfl) ⟨4225506, by rfl⟩ : syracuseStep 11268017 = 8451013) B8451013
theorem B7512011 : Blo 1977435 7512011 := bstep (se 1 (by rfl) ⟨5634008, by rfl⟩ : syracuseStep 7512011 = 11268017) B11268017
theorem B5008007 : Blo 1977435 5008007 := bstep (se 1 (by rfl) ⟨3756005, by rfl⟩ : syracuseStep 5008007 = 7512011) B7512011
theorem B3338671 : Blo 1977435 3338671 := bstep (se 1 (by rfl) ⟨2504003, by rfl⟩ : syracuseStep 3338671 = 5008007) B5008007
theorem B4451561 : Blo 1977435 4451561 := bstep (se 2 (by rfl) ⟨1669335, by rfl⟩ : syracuseStep 4451561 = 3338671) B3338671
theorem B2967707 : Blo 1977435 2967707 := bstep (se 1 (by rfl) ⟨2225780, by rfl⟩ : syracuseStep 2967707 = 4451561) B4451561
theorem B1978471 : Blo 1977435 1978471 := bstep (se 1 (by rfl) ⟨1483853, by rfl⟩ : syracuseStep 1978471 = 2967707) B2967707
theorem B2225785 : Blo 1977435 2225785 := bbase (se 2 (by rfl) ⟨834669, by rfl⟩ : syracuseStep 2225785 = 1669339) (by norm_num)
theorem B2967713 : Blo 1977435 2967713 := bstep (se 2 (by rfl) ⟨1112892, by rfl⟩ : syracuseStep 2967713 = 2225785) B2225785
theorem B1978475 : Blo 1977435 1978475 := bstep (se 1 (by rfl) ⟨1483856, by rfl⟩ : syracuseStep 1978475 = 2967713) B2967713
theorem B32087573 : Blo 1977435 32087573 := bbase (se 6 (by rfl) ⟨752052, by rfl⟩ : syracuseStep 32087573 = 1504105) (by norm_num)
theorem B21391715 : Blo 1977435 21391715 := bstep (se 1 (by rfl) ⟨16043786, by rfl⟩ : syracuseStep 21391715 = 32087573) B32087573
theorem B14261143 : Blo 1977435 14261143 := bstep (se 1 (by rfl) ⟨10695857, by rfl⟩ : syracuseStep 14261143 = 21391715) B21391715
theorem B19014857 : Blo 1977435 19014857 := bstep (se 2 (by rfl) ⟨7130571, by rfl⟩ : syracuseStep 19014857 = 14261143) B14261143
theorem B12676571 : Blo 1977435 12676571 := bstep (se 1 (by rfl) ⟨9507428, by rfl⟩ : syracuseStep 12676571 = 19014857) B19014857
theorem B8451047 : Blo 1977435 8451047 := bstep (se 1 (by rfl) ⟨6338285, by rfl⟩ : syracuseStep 8451047 = 12676571) B12676571
theorem B5634031 : Blo 1977435 5634031 := bstep (se 1 (by rfl) ⟨4225523, by rfl⟩ : syracuseStep 5634031 = 8451047) B8451047
theorem B7512041 : Blo 1977435 7512041 := bstep (se 2 (by rfl) ⟨2817015, by rfl⟩ : syracuseStep 7512041 = 5634031) B5634031
theorem B5008027 : Blo 1977435 5008027 := bstep (se 1 (by rfl) ⟨3756020, by rfl⟩ : syracuseStep 5008027 = 7512041) B7512041
theorem B6677369 : Blo 1977435 6677369 := bstep (se 2 (by rfl) ⟨2504013, by rfl⟩ : syracuseStep 6677369 = 5008027) B5008027
theorem B4451579 : Blo 1977435 4451579 := bstep (se 1 (by rfl) ⟨3338684, by rfl⟩ : syracuseStep 4451579 = 6677369) B6677369
theorem B2967719 : Blo 1977435 2967719 := bstep (se 1 (by rfl) ⟨2225789, by rfl⟩ : syracuseStep 2967719 = 4451579) B4451579
theorem B1978479 : Blo 1977435 1978479 := bstep (se 1 (by rfl) ⟨1483859, by rfl⟩ : syracuseStep 1978479 = 2967719) B2967719
theorem B2967725 : Blo 1977435 2967725 := bbase (se 3 (by rfl) ⟨556448, by rfl⟩ : syracuseStep 2967725 = 1112897) (by norm_num)
theorem B1978483 : Blo 1977435 1978483 := bstep (se 1 (by rfl) ⟨1483862, by rfl⟩ : syracuseStep 1978483 = 2967725) B2967725
theorem B4451597 : Blo 1977435 4451597 := bbase (se 3 (by rfl) ⟨834674, by rfl⟩ : syracuseStep 4451597 = 1669349) (by norm_num)
theorem B2967731 : Blo 1977435 2967731 := bstep (se 1 (by rfl) ⟨2225798, by rfl⟩ : syracuseStep 2967731 = 4451597) B4451597
theorem B1978487 : Blo 1977435 1978487 := bstep (se 1 (by rfl) ⟨1483865, by rfl⟩ : syracuseStep 1978487 = 2967731) B2967731
theorem B2504029 : Blo 1977435 2504029 := bbase (se 3 (by rfl) ⟨469505, by rfl⟩ : syracuseStep 2504029 = 939011) (by norm_num)
theorem B3338705 : Blo 1977435 3338705 := bstep (se 2 (by rfl) ⟨1252014, by rfl⟩ : syracuseStep 3338705 = 2504029) B2504029
theorem B2225803 : Blo 1977435 2225803 := bstep (se 1 (by rfl) ⟨1669352, by rfl⟩ : syracuseStep 2225803 = 3338705) B3338705
theorem B2967737 : Blo 1977435 2967737 := bstep (se 2 (by rfl) ⟨1112901, by rfl⟩ : syracuseStep 2967737 = 2225803) B2225803
theorem B1978491 : Blo 1977435 1978491 := bstep (se 1 (by rfl) ⟨1483868, by rfl⟩ : syracuseStep 1978491 = 2967737) B2967737
theorem B16902229 : Blo 1977435 16902229 := bbase (se 8 (by rfl) ⟨99036, by rfl⟩ : syracuseStep 16902229 = 198073) (by norm_num)
theorem B22536305 : Blo 1977435 22536305 := bstep (se 2 (by rfl) ⟨8451114, by rfl⟩ : syracuseStep 22536305 = 16902229) B16902229
theorem B15024203 : Blo 1977435 15024203 := bstep (se 1 (by rfl) ⟨11268152, by rfl⟩ : syracuseStep 15024203 = 22536305) B22536305
theorem B10016135 : Blo 1977435 10016135 := bstep (se 1 (by rfl) ⟨7512101, by rfl⟩ : syracuseStep 10016135 = 15024203) B15024203
theorem B6677423 : Blo 1977435 6677423 := bstep (se 1 (by rfl) ⟨5008067, by rfl⟩ : syracuseStep 6677423 = 10016135) B10016135
theorem B4451615 : Blo 1977435 4451615 := bstep (se 1 (by rfl) ⟨3338711, by rfl⟩ : syracuseStep 4451615 = 6677423) B6677423
theorem B2967743 : Blo 1977435 2967743 := bstep (se 1 (by rfl) ⟨2225807, by rfl⟩ : syracuseStep 2967743 = 4451615) B4451615
theorem B1978495 : Blo 1977435 1978495 := bstep (se 1 (by rfl) ⟨1483871, by rfl⟩ : syracuseStep 1978495 = 2967743) B2967743
theorem B2967749 : Blo 1977435 2967749 := bbase (se 4 (by rfl) ⟨278226, by rfl⟩ : syracuseStep 2967749 = 556453) (by norm_num)
theorem B1978499 : Blo 1977435 1978499 := bstep (se 1 (by rfl) ⟨1483874, by rfl⟩ : syracuseStep 1978499 = 2967749) B2967749
theorem B3338725 : Blo 1977435 3338725 := bbase (se 4 (by rfl) ⟨313005, by rfl⟩ : syracuseStep 3338725 = 626011) (by norm_num)
theorem B4451633 : Blo 1977435 4451633 := bstep (se 2 (by rfl) ⟨1669362, by rfl⟩ : syracuseStep 4451633 = 3338725) B3338725
theorem B2967755 : Blo 1977435 2967755 := bstep (se 1 (by rfl) ⟨2225816, by rfl⟩ : syracuseStep 2967755 = 4451633) B4451633
theorem B1978503 : Blo 1977435 1978503 := bstep (se 1 (by rfl) ⟨1483877, by rfl⟩ : syracuseStep 1978503 = 2967755) B2967755
theorem B2225821 : Blo 1977435 2225821 := bbase (se 3 (by rfl) ⟨417341, by rfl⟩ : syracuseStep 2225821 = 834683) (by norm_num)
theorem B2967761 : Blo 1977435 2967761 := bstep (se 2 (by rfl) ⟨1112910, by rfl⟩ : syracuseStep 2967761 = 2225821) B2225821
theorem B1978507 : Blo 1977435 1978507 := bstep (se 1 (by rfl) ⟨1483880, by rfl⟩ : syracuseStep 1978507 = 2967761) B2967761
theorem B6677477 : Blo 1977435 6677477 := bbase (se 4 (by rfl) ⟨626013, by rfl⟩ : syracuseStep 6677477 = 1252027) (by norm_num)
theorem B4451651 : Blo 1977435 4451651 := bstep (se 1 (by rfl) ⟨3338738, by rfl⟩ : syracuseStep 4451651 = 6677477) B6677477
theorem B2967767 : Blo 1977435 2967767 := bstep (se 1 (by rfl) ⟨2225825, by rfl⟩ : syracuseStep 2967767 = 4451651) B4451651
theorem B1978511 : Blo 1977435 1978511 := bstep (se 1 (by rfl) ⟨1483883, by rfl⟩ : syracuseStep 1978511 = 2967767) B2967767
theorem B2967773 : Blo 1977435 2967773 := bbase (se 3 (by rfl) ⟨556457, by rfl⟩ : syracuseStep 2967773 = 1112915) (by norm_num)
theorem B1978515 : Blo 1977435 1978515 := bstep (se 1 (by rfl) ⟨1483886, by rfl⟩ : syracuseStep 1978515 = 2967773) B2967773
theorem B4451669 : Blo 1977435 4451669 := bbase (se 11 (by rfl) ⟨3260, by rfl⟩ : syracuseStep 4451669 = 6521) (by norm_num)
theorem B2967779 : Blo 1977435 2967779 := bstep (se 1 (by rfl) ⟨2225834, by rfl⟩ : syracuseStep 2967779 = 4451669) B4451669
theorem B1978519 : Blo 1977435 1978519 := bstep (se 1 (by rfl) ⟨1483889, by rfl⟩ : syracuseStep 1978519 = 2967779) B2967779
theorem B2112809 : Blo 1977435 2112809 := bbase (se 2 (by rfl) ⟨792303, by rfl⟩ : syracuseStep 2112809 = 1584607) (by norm_num)
theorem B5634157 : Blo 1977435 5634157 := bstep (se 3 (by rfl) ⟨1056404, by rfl⟩ : syracuseStep 5634157 = 2112809) B2112809
theorem B7512209 : Blo 1977435 7512209 := bstep (se 2 (by rfl) ⟨2817078, by rfl⟩ : syracuseStep 7512209 = 5634157) B5634157
theorem B5008139 : Blo 1977435 5008139 := bstep (se 1 (by rfl) ⟨3756104, by rfl⟩ : syracuseStep 5008139 = 7512209) B7512209
theorem B3338759 : Blo 1977435 3338759 := bstep (se 1 (by rfl) ⟨2504069, by rfl⟩ : syracuseStep 3338759 = 5008139) B5008139
theorem B2225839 : Blo 1977435 2225839 := bstep (se 1 (by rfl) ⟨1669379, by rfl⟩ : syracuseStep 2225839 = 3338759) B3338759
theorem B2967785 : Blo 1977435 2967785 := bstep (se 2 (by rfl) ⟨1112919, by rfl⟩ : syracuseStep 2967785 = 2225839) B2225839
theorem B1978523 : Blo 1977435 1978523 := bstep (se 1 (by rfl) ⟨1483892, by rfl⟩ : syracuseStep 1978523 = 2967785) B2967785
theorem B1982665 : Blo 1977435 1982665 := bbase (se 2 (by rfl) ⟨743499, by rfl⟩ : syracuseStep 1982665 = 1486999) (by norm_num)
theorem B169187413 : Blo 1977435 169187413 := bstep (se 8 (by rfl) ⟨991332, by rfl⟩ : syracuseStep 169187413 = 1982665) B1982665
theorem B225583217 : Blo 1977435 225583217 := bstep (se 2 (by rfl) ⟨84593706, by rfl⟩ : syracuseStep 225583217 = 169187413) B169187413
theorem B150388811 : Blo 1977435 150388811 := bstep (se 1 (by rfl) ⟨112791608, by rfl⟩ : syracuseStep 150388811 = 225583217) B225583217
theorem B100259207 : Blo 1977435 100259207 := bstep (se 1 (by rfl) ⟨75194405, by rfl⟩ : syracuseStep 100259207 = 150388811) B150388811
theorem B66839471 : Blo 1977435 66839471 := bstep (se 1 (by rfl) ⟨50129603, by rfl⟩ : syracuseStep 66839471 = 100259207) B100259207
theorem B44559647 : Blo 1977435 44559647 := bstep (se 1 (by rfl) ⟨33419735, by rfl⟩ : syracuseStep 44559647 = 66839471) B66839471
theorem B29706431 : Blo 1977435 29706431 := bstep (se 1 (by rfl) ⟨22279823, by rfl⟩ : syracuseStep 29706431 = 44559647) B44559647
theorem B79217149 : Blo 1977435 79217149 := bstep (se 3 (by rfl) ⟨14853215, by rfl⟩ : syracuseStep 79217149 = 29706431) B29706431
theorem B105622865 : Blo 1977435 105622865 := bstep (se 2 (by rfl) ⟨39608574, by rfl⟩ : syracuseStep 105622865 = 79217149) B79217149
theorem B70415243 : Blo 1977435 70415243 := bstep (se 1 (by rfl) ⟨52811432, by rfl⟩ : syracuseStep 70415243 = 105622865) B105622865
theorem B46943495 : Blo 1977435 46943495 := bstep (se 1 (by rfl) ⟨35207621, by rfl⟩ : syracuseStep 46943495 = 70415243) B70415243
theorem B31295663 : Blo 1977435 31295663 := bstep (se 1 (by rfl) ⟨23471747, by rfl⟩ : syracuseStep 31295663 = 46943495) B46943495
theorem B20863775 : Blo 1977435 20863775 := bstep (se 1 (by rfl) ⟨15647831, by rfl⟩ : syracuseStep 20863775 = 31295663) B31295663
theorem B55636733 : Blo 1977435 55636733 := bstep (se 3 (by rfl) ⟨10431887, by rfl⟩ : syracuseStep 55636733 = 20863775) B20863775
theorem B37091155 : Blo 1977435 37091155 := bstep (se 1 (by rfl) ⟨27818366, by rfl⟩ : syracuseStep 37091155 = 55636733) B55636733
theorem B49454873 : Blo 1977435 49454873 := bstep (se 2 (by rfl) ⟨18545577, by rfl⟩ : syracuseStep 49454873 = 37091155) B37091155
theorem B32969915 : Blo 1977435 32969915 := bstep (se 1 (by rfl) ⟨24727436, by rfl⟩ : syracuseStep 32969915 = 49454873) B49454873
theorem B21979943 : Blo 1977435 21979943 := bstep (se 1 (by rfl) ⟨16484957, by rfl⟩ : syracuseStep 21979943 = 32969915) B32969915
theorem B14653295 : Blo 1977435 14653295 := bstep (se 1 (by rfl) ⟨10989971, by rfl⟩ : syracuseStep 14653295 = 21979943) B21979943
theorem B9768863 : Blo 1977435 9768863 := bstep (se 1 (by rfl) ⟨7326647, by rfl⟩ : syracuseStep 9768863 = 14653295) B14653295
theorem B6512575 : Blo 1977435 6512575 := bstep (se 1 (by rfl) ⟨4884431, by rfl⟩ : syracuseStep 6512575 = 9768863) B9768863
theorem B8683433 : Blo 1977435 8683433 := bstep (se 2 (by rfl) ⟨3256287, by rfl⟩ : syracuseStep 8683433 = 6512575) B6512575
theorem B5788955 : Blo 1977435 5788955 := bstep (se 1 (by rfl) ⟨4341716, by rfl⟩ : syracuseStep 5788955 = 8683433) B8683433
theorem B3859303 : Blo 1977435 3859303 := bstep (se 1 (by rfl) ⟨2894477, by rfl⟩ : syracuseStep 3859303 = 5788955) B5788955
theorem B5145737 : Blo 1977435 5145737 := bstep (se 2 (by rfl) ⟨1929651, by rfl⟩ : syracuseStep 5145737 = 3859303) B3859303
theorem B54887861 : Blo 1977435 54887861 := bstep (se 5 (by rfl) ⟨2572868, by rfl⟩ : syracuseStep 54887861 = 5145737) B5145737
theorem B36591907 : Blo 1977435 36591907 := bstep (se 1 (by rfl) ⟨27443930, by rfl⟩ : syracuseStep 36591907 = 54887861) B54887861
theorem B48789209 : Blo 1977435 48789209 := bstep (se 2 (by rfl) ⟨18295953, by rfl⟩ : syracuseStep 48789209 = 36591907) B36591907
theorem B32526139 : Blo 1977435 32526139 := bstep (se 1 (by rfl) ⟨24394604, by rfl⟩ : syracuseStep 32526139 = 48789209) B48789209
theorem B43368185 : Blo 1977435 43368185 := bstep (se 2 (by rfl) ⟨16263069, by rfl⟩ : syracuseStep 43368185 = 32526139) B32526139
theorem B28912123 : Blo 1977435 28912123 := bstep (se 1 (by rfl) ⟨21684092, by rfl⟩ : syracuseStep 28912123 = 43368185) B43368185
theorem B154197989 : Blo 1977435 154197989 := bstep (se 4 (by rfl) ⟨14456061, by rfl⟩ : syracuseStep 154197989 = 28912123) B28912123
theorem B102798659 : Blo 1977435 102798659 := bstep (se 1 (by rfl) ⟨77098994, by rfl⟩ : syracuseStep 102798659 = 154197989) B154197989
theorem B274129757 : Blo 1977435 274129757 := bstep (se 3 (by rfl) ⟨51399329, by rfl⟩ : syracuseStep 274129757 = 102798659) B102798659
theorem B182753171 : Blo 1977435 182753171 := bstep (se 1 (by rfl) ⟨137064878, by rfl⟩ : syracuseStep 182753171 = 274129757) B274129757
theorem B121835447 : Blo 1977435 121835447 := bstep (se 1 (by rfl) ⟨91376585, by rfl⟩ : syracuseStep 121835447 = 182753171) B182753171
theorem B81223631 : Blo 1977435 81223631 := bstep (se 1 (by rfl) ⟨60917723, by rfl⟩ : syracuseStep 81223631 = 121835447) B121835447
theorem B54149087 : Blo 1977435 54149087 := bstep (se 1 (by rfl) ⟨40611815, by rfl⟩ : syracuseStep 54149087 = 81223631) B81223631
theorem B144397565 : Blo 1977435 144397565 := bstep (se 3 (by rfl) ⟨27074543, by rfl⟩ : syracuseStep 144397565 = 54149087) B54149087
theorem B96265043 : Blo 1977435 96265043 := bstep (se 1 (by rfl) ⟨72198782, by rfl⟩ : syracuseStep 96265043 = 144397565) B144397565
theorem B64176695 : Blo 1977435 64176695 := bstep (se 1 (by rfl) ⟨48132521, by rfl⟩ : syracuseStep 64176695 = 96265043) B96265043
theorem B42784463 : Blo 1977435 42784463 := bstep (se 1 (by rfl) ⟨32088347, by rfl⟩ : syracuseStep 42784463 = 64176695) B64176695
theorem B28522975 : Blo 1977435 28522975 := bstep (se 1 (by rfl) ⟨21392231, by rfl⟩ : syracuseStep 28522975 = 42784463) B42784463
theorem B38030633 : Blo 1977435 38030633 := bstep (se 2 (by rfl) ⟨14261487, by rfl⟩ : syracuseStep 38030633 = 28522975) B28522975
theorem B25353755 : Blo 1977435 25353755 := bstep (se 1 (by rfl) ⟨19015316, by rfl⟩ : syracuseStep 25353755 = 38030633) B38030633
theorem B16902503 : Blo 1977435 16902503 := bstep (se 1 (by rfl) ⟨12676877, by rfl⟩ : syracuseStep 16902503 = 25353755) B25353755
theorem B11268335 : Blo 1977435 11268335 := bstep (se 1 (by rfl) ⟨8451251, by rfl⟩ : syracuseStep 11268335 = 16902503) B16902503
theorem B7512223 : Blo 1977435 7512223 := bstep (se 1 (by rfl) ⟨5634167, by rfl⟩ : syracuseStep 7512223 = 11268335) B11268335
theorem B10016297 : Blo 1977435 10016297 := bstep (se 2 (by rfl) ⟨3756111, by rfl⟩ : syracuseStep 10016297 = 7512223) B7512223
theorem B6677531 : Blo 1977435 6677531 := bstep (se 1 (by rfl) ⟨5008148, by rfl⟩ : syracuseStep 6677531 = 10016297) B10016297
theorem B4451687 : Blo 1977435 4451687 := bstep (se 1 (by rfl) ⟨3338765, by rfl⟩ : syracuseStep 4451687 = 6677531) B6677531
theorem B2967791 : Blo 1977435 2967791 := bstep (se 1 (by rfl) ⟨2225843, by rfl⟩ : syracuseStep 2967791 = 4451687) B4451687
theorem B1978527 : Blo 1977435 1978527 := bstep (se 1 (by rfl) ⟨1483895, by rfl⟩ : syracuseStep 1978527 = 2967791) B2967791
theorem B2967797 : Blo 1977435 2967797 := bbase (se 5 (by rfl) ⟨139115, by rfl⟩ : syracuseStep 2967797 = 278231) (by norm_num)
theorem B1978531 : Blo 1977435 1978531 := bstep (se 1 (by rfl) ⟨1483898, by rfl⟩ : syracuseStep 1978531 = 2967797) B2967797
theorem B4011061 : Blo 1977435 4011061 := bbase (se 5 (by rfl) ⟨188018, by rfl⟩ : syracuseStep 4011061 = 376037) (by norm_num)
theorem B5348081 : Blo 1977435 5348081 := bstep (se 2 (by rfl) ⟨2005530, by rfl⟩ : syracuseStep 5348081 = 4011061) B4011061
theorem B3565387 : Blo 1977435 3565387 := bstep (se 1 (by rfl) ⟨2674040, by rfl⟩ : syracuseStep 3565387 = 5348081) B5348081
theorem B19015397 : Blo 1977435 19015397 := bstep (se 4 (by rfl) ⟨1782693, by rfl⟩ : syracuseStep 19015397 = 3565387) B3565387
theorem B12676931 : Blo 1977435 12676931 := bstep (se 1 (by rfl) ⟨9507698, by rfl⟩ : syracuseStep 12676931 = 19015397) B19015397
theorem B8451287 : Blo 1977435 8451287 := bstep (se 1 (by rfl) ⟨6338465, by rfl⟩ : syracuseStep 8451287 = 12676931) B12676931
theorem B5634191 : Blo 1977435 5634191 := bstep (se 1 (by rfl) ⟨4225643, by rfl⟩ : syracuseStep 5634191 = 8451287) B8451287
theorem B3756127 : Blo 1977435 3756127 := bstep (se 1 (by rfl) ⟨2817095, by rfl⟩ : syracuseStep 3756127 = 5634191) B5634191
theorem B5008169 : Blo 1977435 5008169 := bstep (se 2 (by rfl) ⟨1878063, by rfl⟩ : syracuseStep 5008169 = 3756127) B3756127
theorem B3338779 : Blo 1977435 3338779 := bstep (se 1 (by rfl) ⟨2504084, by rfl⟩ : syracuseStep 3338779 = 5008169) B5008169
theorem B4451705 : Blo 1977435 4451705 := bstep (se 2 (by rfl) ⟨1669389, by rfl⟩ : syracuseStep 4451705 = 3338779) B3338779
theorem B2967803 : Blo 1977435 2967803 := bstep (se 1 (by rfl) ⟨2225852, by rfl⟩ : syracuseStep 2967803 = 4451705) B4451705
theorem B1978535 : Blo 1977435 1978535 := bstep (se 1 (by rfl) ⟨1483901, by rfl⟩ : syracuseStep 1978535 = 2967803) B2967803
theorem B2225857 : Blo 1977435 2225857 := bbase (se 2 (by rfl) ⟨834696, by rfl⟩ : syracuseStep 2225857 = 1669393) (by norm_num)
theorem B2967809 : Blo 1977435 2967809 := bstep (se 2 (by rfl) ⟨1112928, by rfl⟩ : syracuseStep 2967809 = 2225857) B2225857
theorem B1978539 : Blo 1977435 1978539 := bstep (se 1 (by rfl) ⟨1483904, by rfl⟩ : syracuseStep 1978539 = 2967809) B2967809
theorem B5008189 : Blo 1977435 5008189 := bbase (se 3 (by rfl) ⟨939035, by rfl⟩ : syracuseStep 5008189 = 1878071) (by norm_num)
theorem B6677585 : Blo 1977435 6677585 := bstep (se 2 (by rfl) ⟨2504094, by rfl⟩ : syracuseStep 6677585 = 5008189) B5008189
theorem B4451723 : Blo 1977435 4451723 := bstep (se 1 (by rfl) ⟨3338792, by rfl⟩ : syracuseStep 4451723 = 6677585) B6677585
theorem B2967815 : Blo 1977435 2967815 := bstep (se 1 (by rfl) ⟨2225861, by rfl⟩ : syracuseStep 2967815 = 4451723) B4451723
theorem B1978543 : Blo 1977435 1978543 := bstep (se 1 (by rfl) ⟨1483907, by rfl⟩ : syracuseStep 1978543 = 2967815) B2967815
theorem B2967821 : Blo 1977435 2967821 := bbase (se 3 (by rfl) ⟨556466, by rfl⟩ : syracuseStep 2967821 = 1112933) (by norm_num)
theorem B1978547 : Blo 1977435 1978547 := bstep (se 1 (by rfl) ⟨1483910, by rfl⟩ : syracuseStep 1978547 = 2967821) B2967821
theorem B4451741 : Blo 1977435 4451741 := bbase (se 3 (by rfl) ⟨834701, by rfl⟩ : syracuseStep 4451741 = 1669403) (by norm_num)
theorem B2967827 : Blo 1977435 2967827 := bstep (se 1 (by rfl) ⟨2225870, by rfl⟩ : syracuseStep 2967827 = 4451741) B4451741
theorem B1978551 : Blo 1977435 1978551 := bstep (se 1 (by rfl) ⟨1483913, by rfl⟩ : syracuseStep 1978551 = 2967827) B2967827
theorem B3338813 : Blo 1977435 3338813 := bbase (se 3 (by rfl) ⟨626027, by rfl⟩ : syracuseStep 3338813 = 1252055) (by norm_num)
theorem B2225875 : Blo 1977435 2225875 := bstep (se 1 (by rfl) ⟨1669406, by rfl⟩ : syracuseStep 2225875 = 3338813) B3338813
theorem B2967833 : Blo 1977435 2967833 := bstep (se 2 (by rfl) ⟨1112937, by rfl⟩ : syracuseStep 2967833 = 2225875) B2225875
theorem B1978555 : Blo 1977435 1978555 := bstep (se 1 (by rfl) ⟨1483916, by rfl⟩ : syracuseStep 1978555 = 2967833) B2967833
theorem B3008333 : Blo 1977435 3008333 := bbase (se 3 (by rfl) ⟨564062, by rfl⟩ : syracuseStep 3008333 = 1128125) (by norm_num)
theorem B2005555 : Blo 1977435 2005555 := bstep (se 1 (by rfl) ⟨1504166, by rfl⟩ : syracuseStep 2005555 = 3008333) B3008333
theorem B2674073 : Blo 1977435 2674073 := bstep (se 2 (by rfl) ⟨1002777, by rfl⟩ : syracuseStep 2674073 = 2005555) B2005555
theorem B7130861 : Blo 1977435 7130861 := bstep (se 3 (by rfl) ⟨1337036, by rfl⟩ : syracuseStep 7130861 = 2674073) B2674073
theorem B4753907 : Blo 1977435 4753907 := bstep (se 1 (by rfl) ⟨3565430, by rfl⟩ : syracuseStep 4753907 = 7130861) B7130861
theorem B3169271 : Blo 1977435 3169271 := bstep (se 1 (by rfl) ⟨2376953, by rfl⟩ : syracuseStep 3169271 = 4753907) B4753907
theorem B2112847 : Blo 1977435 2112847 := bstep (se 1 (by rfl) ⟨1584635, by rfl⟩ : syracuseStep 2112847 = 3169271) B3169271
theorem B11268517 : Blo 1977435 11268517 := bstep (se 4 (by rfl) ⟨1056423, by rfl⟩ : syracuseStep 11268517 = 2112847) B2112847
theorem B15024689 : Blo 1977435 15024689 := bstep (se 2 (by rfl) ⟨5634258, by rfl⟩ : syracuseStep 15024689 = 11268517) B11268517
theorem B10016459 : Blo 1977435 10016459 := bstep (se 1 (by rfl) ⟨7512344, by rfl⟩ : syracuseStep 10016459 = 15024689) B15024689
theorem B6677639 : Blo 1977435 6677639 := bstep (se 1 (by rfl) ⟨5008229, by rfl⟩ : syracuseStep 6677639 = 10016459) B10016459
theorem B4451759 : Blo 1977435 4451759 := bstep (se 1 (by rfl) ⟨3338819, by rfl⟩ : syracuseStep 4451759 = 6677639) B6677639
theorem B2967839 : Blo 1977435 2967839 := bstep (se 1 (by rfl) ⟨2225879, by rfl⟩ : syracuseStep 2967839 = 4451759) B4451759
theorem B1978559 : Blo 1977435 1978559 := bstep (se 1 (by rfl) ⟨1483919, by rfl⟩ : syracuseStep 1978559 = 2967839) B2967839
theorem B2967845 : Blo 1977435 2967845 := bbase (se 4 (by rfl) ⟨278235, by rfl⟩ : syracuseStep 2967845 = 556471) (by norm_num)
theorem B1978563 : Blo 1977435 1978563 := bstep (se 1 (by rfl) ⟨1483922, by rfl⟩ : syracuseStep 1978563 = 2967845) B2967845
theorem B2504125 : Blo 1977435 2504125 := bbase (se 3 (by rfl) ⟨469523, by rfl⟩ : syracuseStep 2504125 = 939047) (by norm_num)
theorem B3338833 : Blo 1977435 3338833 := bstep (se 2 (by rfl) ⟨1252062, by rfl⟩ : syracuseStep 3338833 = 2504125) B2504125
theorem B4451777 : Blo 1977435 4451777 := bstep (se 2 (by rfl) ⟨1669416, by rfl⟩ : syracuseStep 4451777 = 3338833) B3338833
theorem B2967851 : Blo 1977435 2967851 := bstep (se 1 (by rfl) ⟨2225888, by rfl⟩ : syracuseStep 2967851 = 4451777) B4451777
theorem B1978567 : Blo 1977435 1978567 := bstep (se 1 (by rfl) ⟨1483925, by rfl⟩ : syracuseStep 1978567 = 2967851) B2967851
theorem B2225893 : Blo 1977435 2225893 := bbase (se 4 (by rfl) ⟨208677, by rfl⟩ : syracuseStep 2225893 = 417355) (by norm_num)
theorem B2967857 : Blo 1977435 2967857 := bstep (se 2 (by rfl) ⟨1112946, by rfl⟩ : syracuseStep 2967857 = 2225893) B2225893
theorem B1978571 : Blo 1977435 1978571 := bstep (se 1 (by rfl) ⟨1483928, by rfl⟩ : syracuseStep 1978571 = 2967857) B2967857
theorem B2376973 : Blo 1977435 2376973 := bbase (se 3 (by rfl) ⟨445682, by rfl⟩ : syracuseStep 2376973 = 891365) (by norm_num)
theorem B3169297 : Blo 1977435 3169297 := bstep (se 2 (by rfl) ⟨1188486, by rfl⟩ : syracuseStep 3169297 = 2376973) B2376973
theorem B4225729 : Blo 1977435 4225729 := bstep (se 2 (by rfl) ⟨1584648, by rfl⟩ : syracuseStep 4225729 = 3169297) B3169297
theorem B5634305 : Blo 1977435 5634305 := bstep (se 2 (by rfl) ⟨2112864, by rfl⟩ : syracuseStep 5634305 = 4225729) B4225729
theorem B3756203 : Blo 1977435 3756203 := bstep (se 1 (by rfl) ⟨2817152, by rfl⟩ : syracuseStep 3756203 = 5634305) B5634305
theorem B2504135 : Blo 1977435 2504135 := bstep (se 1 (by rfl) ⟨1878101, by rfl⟩ : syracuseStep 2504135 = 3756203) B3756203
theorem B6677693 : Blo 1977435 6677693 := bstep (se 3 (by rfl) ⟨1252067, by rfl⟩ : syracuseStep 6677693 = 2504135) B2504135
theorem B4451795 : Blo 1977435 4451795 := bstep (se 1 (by rfl) ⟨3338846, by rfl⟩ : syracuseStep 4451795 = 6677693) B6677693
theorem B2967863 : Blo 1977435 2967863 := bstep (se 1 (by rfl) ⟨2225897, by rfl⟩ : syracuseStep 2967863 = 4451795) B4451795
theorem B1978575 : Blo 1977435 1978575 := bstep (se 1 (by rfl) ⟨1483931, by rfl⟩ : syracuseStep 1978575 = 2967863) B2967863
theorem B2967869 : Blo 1977435 2967869 := bbase (se 3 (by rfl) ⟨556475, by rfl⟩ : syracuseStep 2967869 = 1112951) (by norm_num)
theorem B1978579 : Blo 1977435 1978579 := bstep (se 1 (by rfl) ⟨1483934, by rfl⟩ : syracuseStep 1978579 = 2967869) B2967869
theorem B4451813 : Blo 1977435 4451813 := bbase (se 4 (by rfl) ⟨417357, by rfl⟩ : syracuseStep 4451813 = 834715) (by norm_num)
theorem B2967875 : Blo 1977435 2967875 := bstep (se 1 (by rfl) ⟨2225906, by rfl⟩ : syracuseStep 2967875 = 4451813) B4451813
theorem B1978583 : Blo 1977435 1978583 := bstep (se 1 (by rfl) ⟨1483937, by rfl⟩ : syracuseStep 1978583 = 2967875) B2967875
theorem B5008301 : Blo 1977435 5008301 := bbase (se 3 (by rfl) ⟨939056, by rfl⟩ : syracuseStep 5008301 = 1878113) (by norm_num)
theorem B3338867 : Blo 1977435 3338867 := bstep (se 1 (by rfl) ⟨2504150, by rfl⟩ : syracuseStep 3338867 = 5008301) B5008301
theorem B2225911 : Blo 1977435 2225911 := bstep (se 1 (by rfl) ⟨1669433, by rfl⟩ : syracuseStep 2225911 = 3338867) B3338867
theorem B2967881 : Blo 1977435 2967881 := bstep (se 2 (by rfl) ⟨1112955, by rfl⟩ : syracuseStep 2967881 = 2225911) B2225911
theorem B1978587 : Blo 1977435 1978587 := bstep (se 1 (by rfl) ⟨1483940, by rfl⟩ : syracuseStep 1978587 = 2967881) B2967881
theorem B6338645 : Blo 1977435 6338645 := bbase (se 8 (by rfl) ⟨37140, by rfl⟩ : syracuseStep 6338645 = 74281) (by norm_num)
theorem B4225763 : Blo 1977435 4225763 := bstep (se 1 (by rfl) ⟨3169322, by rfl⟩ : syracuseStep 4225763 = 6338645) B6338645
theorem B2817175 : Blo 1977435 2817175 := bstep (se 1 (by rfl) ⟨2112881, by rfl⟩ : syracuseStep 2817175 = 4225763) B4225763
theorem B3756233 : Blo 1977435 3756233 := bstep (se 2 (by rfl) ⟨1408587, by rfl⟩ : syracuseStep 3756233 = 2817175) B2817175
theorem B10016621 : Blo 1977435 10016621 := bstep (se 3 (by rfl) ⟨1878116, by rfl⟩ : syracuseStep 10016621 = 3756233) B3756233
theorem B6677747 : Blo 1977435 6677747 := bstep (se 1 (by rfl) ⟨5008310, by rfl⟩ : syracuseStep 6677747 = 10016621) B10016621
theorem B4451831 : Blo 1977435 4451831 := bstep (se 1 (by rfl) ⟨3338873, by rfl⟩ : syracuseStep 4451831 = 6677747) B6677747
theorem B2967887 : Blo 1977435 2967887 := bstep (se 1 (by rfl) ⟨2225915, by rfl⟩ : syracuseStep 2967887 = 4451831) B4451831
theorem B1978591 : Blo 1977435 1978591 := bstep (se 1 (by rfl) ⟨1483943, by rfl⟩ : syracuseStep 1978591 = 2967887) B2967887
theorem B2967893 : Blo 1977435 2967893 := bbase (se 10 (by rfl) ⟨4347, by rfl⟩ : syracuseStep 2967893 = 8695) (by norm_num)
theorem B1978595 : Blo 1977435 1978595 := bstep (se 1 (by rfl) ⟨1483946, by rfl⟩ : syracuseStep 1978595 = 2967893) B2967893
theorem B5634373 : Blo 1977435 5634373 := bbase (se 4 (by rfl) ⟨528222, by rfl⟩ : syracuseStep 5634373 = 1056445) (by norm_num)
theorem B7512497 : Blo 1977435 7512497 := bstep (se 2 (by rfl) ⟨2817186, by rfl⟩ : syracuseStep 7512497 = 5634373) B5634373
theorem B5008331 : Blo 1977435 5008331 := bstep (se 1 (by rfl) ⟨3756248, by rfl⟩ : syracuseStep 5008331 = 7512497) B7512497
theorem B3338887 : Blo 1977435 3338887 := bstep (se 1 (by rfl) ⟨2504165, by rfl⟩ : syracuseStep 3338887 = 5008331) B5008331
theorem B4451849 : Blo 1977435 4451849 := bstep (se 2 (by rfl) ⟨1669443, by rfl⟩ : syracuseStep 4451849 = 3338887) B3338887
theorem B2967899 : Blo 1977435 2967899 := bstep (se 1 (by rfl) ⟨2225924, by rfl⟩ : syracuseStep 2967899 = 4451849) B4451849
theorem B1978599 : Blo 1977435 1978599 := bstep (se 1 (by rfl) ⟨1483949, by rfl⟩ : syracuseStep 1978599 = 2967899) B2967899
theorem B2225929 : Blo 1977435 2225929 := bbase (se 2 (by rfl) ⟨834723, by rfl⟩ : syracuseStep 2225929 = 1669447) (by norm_num)
theorem B2967905 : Blo 1977435 2967905 := bstep (se 2 (by rfl) ⟨1112964, by rfl⟩ : syracuseStep 2967905 = 2225929) B2225929
theorem B1978603 : Blo 1977435 1978603 := bstep (se 1 (by rfl) ⟨1483952, by rfl⟩ : syracuseStep 1978603 = 2967905) B2967905
theorem B3008405 : Blo 1977435 3008405 := bbase (se 6 (by rfl) ⟨70509, by rfl⟩ : syracuseStep 3008405 = 141019) (by norm_num)
theorem B2005603 : Blo 1977435 2005603 := bstep (se 1 (by rfl) ⟨1504202, by rfl⟩ : syracuseStep 2005603 = 3008405) B3008405
theorem B10696549 : Blo 1977435 10696549 := bstep (se 4 (by rfl) ⟨1002801, by rfl⟩ : syracuseStep 10696549 = 2005603) B2005603
theorem B14262065 : Blo 1977435 14262065 := bstep (se 2 (by rfl) ⟨5348274, by rfl⟩ : syracuseStep 14262065 = 10696549) B10696549
theorem B9508043 : Blo 1977435 9508043 := bstep (se 1 (by rfl) ⟨7131032, by rfl⟩ : syracuseStep 9508043 = 14262065) B14262065
theorem B25354781 : Blo 1977435 25354781 := bstep (se 3 (by rfl) ⟨4754021, by rfl⟩ : syracuseStep 25354781 = 9508043) B9508043
theorem B16903187 : Blo 1977435 16903187 := bstep (se 1 (by rfl) ⟨12677390, by rfl⟩ : syracuseStep 16903187 = 25354781) B25354781
theorem B11268791 : Blo 1977435 11268791 := bstep (se 1 (by rfl) ⟨8451593, by rfl⟩ : syracuseStep 11268791 = 16903187) B16903187
theorem B7512527 : Blo 1977435 7512527 := bstep (se 1 (by rfl) ⟨5634395, by rfl⟩ : syracuseStep 7512527 = 11268791) B11268791
theorem B5008351 : Blo 1977435 5008351 := bstep (se 1 (by rfl) ⟨3756263, by rfl⟩ : syracuseStep 5008351 = 7512527) B7512527
theorem B6677801 : Blo 1977435 6677801 := bstep (se 2 (by rfl) ⟨2504175, by rfl⟩ : syracuseStep 6677801 = 5008351) B5008351
theorem B4451867 : Blo 1977435 4451867 := bstep (se 1 (by rfl) ⟨3338900, by rfl⟩ : syracuseStep 4451867 = 6677801) B6677801
theorem B2967911 : Blo 1977435 2967911 := bstep (se 1 (by rfl) ⟨2225933, by rfl⟩ : syracuseStep 2967911 = 4451867) B4451867
theorem B1978607 : Blo 1977435 1978607 := bstep (se 1 (by rfl) ⟨1483955, by rfl⟩ : syracuseStep 1978607 = 2967911) B2967911
theorem B2967917 : Blo 1977435 2967917 := bbase (se 3 (by rfl) ⟨556484, by rfl⟩ : syracuseStep 2967917 = 1112969) (by norm_num)
theorem B1978611 : Blo 1977435 1978611 := bstep (se 1 (by rfl) ⟨1483958, by rfl⟩ : syracuseStep 1978611 = 2967917) B2967917
theorem B4451885 : Blo 1977435 4451885 := bbase (se 3 (by rfl) ⟨834728, by rfl⟩ : syracuseStep 4451885 = 1669457) (by norm_num)
theorem B2967923 : Blo 1977435 2967923 := bstep (se 1 (by rfl) ⟨2225942, by rfl⟩ : syracuseStep 2967923 = 4451885) B4451885
theorem B1978615 : Blo 1977435 1978615 := bstep (se 1 (by rfl) ⟨1483961, by rfl⟩ : syracuseStep 1978615 = 2967923) B2967923
theorem B9637829 : Blo 1977435 9637829 := bbase (se 4 (by rfl) ⟨903546, by rfl⟩ : syracuseStep 9637829 = 1807093) (by norm_num)
theorem B6425219 : Blo 1977435 6425219 := bstep (se 1 (by rfl) ⟨4818914, by rfl⟩ : syracuseStep 6425219 = 9637829) B9637829
theorem B4283479 : Blo 1977435 4283479 := bstep (se 1 (by rfl) ⟨3212609, by rfl⟩ : syracuseStep 4283479 = 6425219) B6425219
theorem B5711305 : Blo 1977435 5711305 := bstep (se 2 (by rfl) ⟨2141739, by rfl⟩ : syracuseStep 5711305 = 4283479) B4283479
theorem B7615073 : Blo 1977435 7615073 := bstep (se 2 (by rfl) ⟨2855652, by rfl⟩ : syracuseStep 7615073 = 5711305) B5711305
theorem B20306861 : Blo 1977435 20306861 := bstep (se 3 (by rfl) ⟨3807536, by rfl⟩ : syracuseStep 20306861 = 7615073) B7615073
theorem B13537907 : Blo 1977435 13537907 := bstep (se 1 (by rfl) ⟨10153430, by rfl⟩ : syracuseStep 13537907 = 20306861) B20306861
theorem B9025271 : Blo 1977435 9025271 := bstep (se 1 (by rfl) ⟨6768953, by rfl⟩ : syracuseStep 9025271 = 13537907) B13537907
theorem B6016847 : Blo 1977435 6016847 := bstep (se 1 (by rfl) ⟨4512635, by rfl⟩ : syracuseStep 6016847 = 9025271) B9025271
theorem B64179701 : Blo 1977435 64179701 := bstep (se 5 (by rfl) ⟨3008423, by rfl⟩ : syracuseStep 64179701 = 6016847) B6016847
theorem B42786467 : Blo 1977435 42786467 := bstep (se 1 (by rfl) ⟨32089850, by rfl⟩ : syracuseStep 42786467 = 64179701) B64179701
theorem B28524311 : Blo 1977435 28524311 := bstep (se 1 (by rfl) ⟨21393233, by rfl⟩ : syracuseStep 28524311 = 42786467) B42786467
theorem B19016207 : Blo 1977435 19016207 := bstep (se 1 (by rfl) ⟨14262155, by rfl⟩ : syracuseStep 19016207 = 28524311) B28524311
theorem B12677471 : Blo 1977435 12677471 := bstep (se 1 (by rfl) ⟨9508103, by rfl⟩ : syracuseStep 12677471 = 19016207) B19016207
theorem B8451647 : Blo 1977435 8451647 := bstep (se 1 (by rfl) ⟨6338735, by rfl⟩ : syracuseStep 8451647 = 12677471) B12677471
theorem B5634431 : Blo 1977435 5634431 := bstep (se 1 (by rfl) ⟨4225823, by rfl⟩ : syracuseStep 5634431 = 8451647) B8451647
theorem B3756287 : Blo 1977435 3756287 := bstep (se 1 (by rfl) ⟨2817215, by rfl⟩ : syracuseStep 3756287 = 5634431) B5634431
theorem B2504191 : Blo 1977435 2504191 := bstep (se 1 (by rfl) ⟨1878143, by rfl⟩ : syracuseStep 2504191 = 3756287) B3756287
theorem B3338921 : Blo 1977435 3338921 := bstep (se 2 (by rfl) ⟨1252095, by rfl⟩ : syracuseStep 3338921 = 2504191) B2504191
theorem B2225947 : Blo 1977435 2225947 := bstep (se 1 (by rfl) ⟨1669460, by rfl⟩ : syracuseStep 2225947 = 3338921) B3338921
theorem B2967929 : Blo 1977435 2967929 := bstep (se 2 (by rfl) ⟨1112973, by rfl⟩ : syracuseStep 2967929 = 2225947) B2225947
theorem B1978619 : Blo 1977435 1978619 := bstep (se 1 (by rfl) ⟨1483964, by rfl⟩ : syracuseStep 1978619 = 2967929) B2967929
theorem B3169373 : Blo 1977435 3169373 := bbase (se 3 (by rfl) ⟨594257, by rfl⟩ : syracuseStep 3169373 = 1188515) (by norm_num)
theorem B33806645 : Blo 1977435 33806645 := bstep (se 5 (by rfl) ⟨1584686, by rfl⟩ : syracuseStep 33806645 = 3169373) B3169373
theorem B22537763 : Blo 1977435 22537763 := bstep (se 1 (by rfl) ⟨16903322, by rfl⟩ : syracuseStep 22537763 = 33806645) B33806645
theorem B15025175 : Blo 1977435 15025175 := bstep (se 1 (by rfl) ⟨11268881, by rfl⟩ : syracuseStep 15025175 = 22537763) B22537763
theorem B10016783 : Blo 1977435 10016783 := bstep (se 1 (by rfl) ⟨7512587, by rfl⟩ : syracuseStep 10016783 = 15025175) B15025175
theorem B6677855 : Blo 1977435 6677855 := bstep (se 1 (by rfl) ⟨5008391, by rfl⟩ : syracuseStep 6677855 = 10016783) B10016783
theorem B4451903 : Blo 1977435 4451903 := bstep (se 1 (by rfl) ⟨3338927, by rfl⟩ : syracuseStep 4451903 = 6677855) B6677855
theorem B2967935 : Blo 1977435 2967935 := bstep (se 1 (by rfl) ⟨2225951, by rfl⟩ : syracuseStep 2967935 = 4451903) B4451903
theorem B1978623 : Blo 1977435 1978623 := bstep (se 1 (by rfl) ⟨1483967, by rfl⟩ : syracuseStep 1978623 = 2967935) B2967935
theorem B2967941 : Blo 1977435 2967941 := bbase (se 4 (by rfl) ⟨278244, by rfl⟩ : syracuseStep 2967941 = 556489) (by norm_num)
theorem B1978627 : Blo 1977435 1978627 := bstep (se 1 (by rfl) ⟨1483970, by rfl⟩ : syracuseStep 1978627 = 2967941) B2967941
theorem B3338941 : Blo 1977435 3338941 := bbase (se 3 (by rfl) ⟨626051, by rfl⟩ : syracuseStep 3338941 = 1252103) (by norm_num)
theorem B4451921 : Blo 1977435 4451921 := bstep (se 2 (by rfl) ⟨1669470, by rfl⟩ : syracuseStep 4451921 = 3338941) B3338941
theorem B2967947 : Blo 1977435 2967947 := bstep (se 1 (by rfl) ⟨2225960, by rfl⟩ : syracuseStep 2967947 = 4451921) B4451921
theorem B1978631 : Blo 1977435 1978631 := bstep (se 1 (by rfl) ⟨1483973, by rfl⟩ : syracuseStep 1978631 = 2967947) B2967947
theorem B2225965 : Blo 1977435 2225965 := bbase (se 3 (by rfl) ⟨417368, by rfl⟩ : syracuseStep 2225965 = 834737) (by norm_num)
theorem B2967953 : Blo 1977435 2967953 := bstep (se 2 (by rfl) ⟨1112982, by rfl⟩ : syracuseStep 2967953 = 2225965) B2225965
theorem B1978635 : Blo 1977435 1978635 := bstep (se 1 (by rfl) ⟨1483976, by rfl⟩ : syracuseStep 1978635 = 2967953) B2967953
theorem B6677909 : Blo 1977435 6677909 := bbase (se 6 (by rfl) ⟨156513, by rfl⟩ : syracuseStep 6677909 = 313027) (by norm_num)
theorem B4451939 : Blo 1977435 4451939 := bstep (se 1 (by rfl) ⟨3338954, by rfl⟩ : syracuseStep 4451939 = 6677909) B6677909
theorem B2967959 : Blo 1977435 2967959 := bstep (se 1 (by rfl) ⟨2225969, by rfl⟩ : syracuseStep 2967959 = 4451939) B4451939
theorem B1978639 : Blo 1977435 1978639 := bstep (se 1 (by rfl) ⟨1483979, by rfl⟩ : syracuseStep 1978639 = 2967959) B2967959
theorem B2967965 : Blo 1977435 2967965 := bbase (se 3 (by rfl) ⟨556493, by rfl⟩ : syracuseStep 2967965 = 1112987) (by norm_num)
theorem B1978643 : Blo 1977435 1978643 := bstep (se 1 (by rfl) ⟨1483982, by rfl⟩ : syracuseStep 1978643 = 2967965) B2967965
theorem B4451957 : Blo 1977435 4451957 := bbase (se 5 (by rfl) ⟨208685, by rfl⟩ : syracuseStep 4451957 = 417371) (by norm_num)
theorem B2967971 : Blo 1977435 2967971 := bstep (se 1 (by rfl) ⟨2225978, by rfl⟩ : syracuseStep 2967971 = 4451957) B4451957
theorem B1978647 : Blo 1977435 1978647 := bstep (se 1 (by rfl) ⟨1483985, by rfl⟩ : syracuseStep 1978647 = 2967971) B2967971
theorem B6338837 : Blo 1977435 6338837 := bbase (se 6 (by rfl) ⟨148566, by rfl⟩ : syracuseStep 6338837 = 297133) (by norm_num)
theorem B16903565 : Blo 1977435 16903565 := bstep (se 3 (by rfl) ⟨3169418, by rfl⟩ : syracuseStep 16903565 = 6338837) B6338837
theorem B11269043 : Blo 1977435 11269043 := bstep (se 1 (by rfl) ⟨8451782, by rfl⟩ : syracuseStep 11269043 = 16903565) B16903565
theorem B7512695 : Blo 1977435 7512695 := bstep (se 1 (by rfl) ⟨5634521, by rfl⟩ : syracuseStep 7512695 = 11269043) B11269043
theorem B5008463 : Blo 1977435 5008463 := bstep (se 1 (by rfl) ⟨3756347, by rfl⟩ : syracuseStep 5008463 = 7512695) B7512695
theorem B3338975 : Blo 1977435 3338975 := bstep (se 1 (by rfl) ⟨2504231, by rfl⟩ : syracuseStep 3338975 = 5008463) B5008463
theorem B2225983 : Blo 1977435 2225983 := bstep (se 1 (by rfl) ⟨1669487, by rfl⟩ : syracuseStep 2225983 = 3338975) B3338975
theorem B2967977 : Blo 1977435 2967977 := bstep (se 2 (by rfl) ⟨1112991, by rfl⟩ : syracuseStep 2967977 = 2225983) B2225983
theorem B1978651 : Blo 1977435 1978651 := bstep (se 1 (by rfl) ⟨1483988, by rfl⟩ : syracuseStep 1978651 = 2967977) B2967977
theorem B7512709 : Blo 1977435 7512709 := bbase (se 4 (by rfl) ⟨704316, by rfl⟩ : syracuseStep 7512709 = 1408633) (by norm_num)
theorem B10016945 : Blo 1977435 10016945 := bstep (se 2 (by rfl) ⟨3756354, by rfl⟩ : syracuseStep 10016945 = 7512709) B7512709
theorem B6677963 : Blo 1977435 6677963 := bstep (se 1 (by rfl) ⟨5008472, by rfl⟩ : syracuseStep 6677963 = 10016945) B10016945
theorem B4451975 : Blo 1977435 4451975 := bstep (se 1 (by rfl) ⟨3338981, by rfl⟩ : syracuseStep 4451975 = 6677963) B6677963
theorem B2967983 : Blo 1977435 2967983 := bstep (se 1 (by rfl) ⟨2225987, by rfl⟩ : syracuseStep 2967983 = 4451975) B4451975
theorem B1978655 : Blo 1977435 1978655 := bstep (se 1 (by rfl) ⟨1483991, by rfl⟩ : syracuseStep 1978655 = 2967983) B2967983
theorem B2967989 : Blo 1977435 2967989 := bbase (se 5 (by rfl) ⟨139124, by rfl⟩ : syracuseStep 2967989 = 278249) (by norm_num)
theorem B1978659 : Blo 1977435 1978659 := bstep (se 1 (by rfl) ⟨1483994, by rfl⟩ : syracuseStep 1978659 = 2967989) B2967989
theorem B5008493 : Blo 1977435 5008493 := bbase (se 3 (by rfl) ⟨939092, by rfl⟩ : syracuseStep 5008493 = 1878185) (by norm_num)
theorem B3338995 : Blo 1977435 3338995 := bstep (se 1 (by rfl) ⟨2504246, by rfl⟩ : syracuseStep 3338995 = 5008493) B5008493
theorem B4451993 : Blo 1977435 4451993 := bstep (se 2 (by rfl) ⟨1669497, by rfl⟩ : syracuseStep 4451993 = 3338995) B3338995
theorem B2967995 : Blo 1977435 2967995 := bstep (se 1 (by rfl) ⟨2225996, by rfl⟩ : syracuseStep 2967995 = 4451993) B4451993
theorem B1978663 : Blo 1977435 1978663 := bstep (se 1 (by rfl) ⟨1483997, by rfl⟩ : syracuseStep 1978663 = 2967995) B2967995
theorem B2226001 : Blo 1977435 2226001 := bbase (se 2 (by rfl) ⟨834750, by rfl⟩ : syracuseStep 2226001 = 1669501) (by norm_num)
theorem B2968001 : Blo 1977435 2968001 := bstep (se 2 (by rfl) ⟨1113000, by rfl⟩ : syracuseStep 2968001 = 2226001) B2226001
theorem B1978667 : Blo 1977435 1978667 := bstep (se 1 (by rfl) ⟨1484000, by rfl⟩ : syracuseStep 1978667 = 2968001) B2968001
theorem B2005669 : Blo 1977435 2005669 := bbase (se 4 (by rfl) ⟨188031, by rfl⟩ : syracuseStep 2005669 = 376063) (by norm_num)
theorem B2674225 : Blo 1977435 2674225 := bstep (se 2 (by rfl) ⟨1002834, by rfl⟩ : syracuseStep 2674225 = 2005669) B2005669
theorem B3565633 : Blo 1977435 3565633 := bstep (se 2 (by rfl) ⟨1337112, by rfl⟩ : syracuseStep 3565633 = 2674225) B2674225
theorem B4754177 : Blo 1977435 4754177 := bstep (se 2 (by rfl) ⟨1782816, by rfl⟩ : syracuseStep 4754177 = 3565633) B3565633
theorem B3169451 : Blo 1977435 3169451 := bstep (se 1 (by rfl) ⟨2377088, by rfl⟩ : syracuseStep 3169451 = 4754177) B4754177
theorem B2112967 : Blo 1977435 2112967 := bstep (se 1 (by rfl) ⟨1584725, by rfl⟩ : syracuseStep 2112967 = 3169451) B3169451
theorem B2817289 : Blo 1977435 2817289 := bstep (se 2 (by rfl) ⟨1056483, by rfl⟩ : syracuseStep 2817289 = 2112967) B2112967
theorem B3756385 : Blo 1977435 3756385 := bstep (se 2 (by rfl) ⟨1408644, by rfl⟩ : syracuseStep 3756385 = 2817289) B2817289
theorem B5008513 : Blo 1977435 5008513 := bstep (se 2 (by rfl) ⟨1878192, by rfl⟩ : syracuseStep 5008513 = 3756385) B3756385
theorem B6678017 : Blo 1977435 6678017 := bstep (se 2 (by rfl) ⟨2504256, by rfl⟩ : syracuseStep 6678017 = 5008513) B5008513
theorem B4452011 : Blo 1977435 4452011 := bstep (se 1 (by rfl) ⟨3339008, by rfl⟩ : syracuseStep 4452011 = 6678017) B6678017
theorem B2968007 : Blo 1977435 2968007 := bstep (se 1 (by rfl) ⟨2226005, by rfl⟩ : syracuseStep 2968007 = 4452011) B4452011
theorem B1978671 : Blo 1977435 1978671 := bstep (se 1 (by rfl) ⟨1484003, by rfl⟩ : syracuseStep 1978671 = 2968007) B2968007
theorem B2968013 : Blo 1977435 2968013 := bbase (se 3 (by rfl) ⟨556502, by rfl⟩ : syracuseStep 2968013 = 1113005) (by norm_num)
theorem B1978675 : Blo 1977435 1978675 := bstep (se 1 (by rfl) ⟨1484006, by rfl⟩ : syracuseStep 1978675 = 2968013) B2968013
theorem B4452029 : Blo 1977435 4452029 := bbase (se 3 (by rfl) ⟨834755, by rfl⟩ : syracuseStep 4452029 = 1669511) (by norm_num)
theorem B2968019 : Blo 1977435 2968019 := bstep (se 1 (by rfl) ⟨2226014, by rfl⟩ : syracuseStep 2968019 = 4452029) B4452029
theorem B1978679 : Blo 1977435 1978679 := bstep (se 1 (by rfl) ⟨1484009, by rfl⟩ : syracuseStep 1978679 = 2968019) B2968019
theorem B3339029 : Blo 1977435 3339029 := bbase (se 6 (by rfl) ⟨78258, by rfl⟩ : syracuseStep 3339029 = 156517) (by norm_num)
theorem B2226019 : Blo 1977435 2226019 := bstep (se 1 (by rfl) ⟨1669514, by rfl⟩ : syracuseStep 2226019 = 3339029) B3339029
theorem B2968025 : Blo 1977435 2968025 := bstep (se 2 (by rfl) ⟨1113009, by rfl⟩ : syracuseStep 2968025 = 2226019) B2226019
theorem B1978683 : Blo 1977435 1978683 := bstep (se 1 (by rfl) ⟨1484012, by rfl⟩ : syracuseStep 1978683 = 2968025) B2968025
theorem B42787925 : Blo 1977435 42787925 := bbase (se 8 (by rfl) ⟨250710, by rfl⟩ : syracuseStep 42787925 = 501421) (by norm_num)
theorem B28525283 : Blo 1977435 28525283 := bstep (se 1 (by rfl) ⟨21393962, by rfl⟩ : syracuseStep 28525283 = 42787925) B42787925
theorem B19016855 : Blo 1977435 19016855 := bstep (se 1 (by rfl) ⟨14262641, by rfl⟩ : syracuseStep 19016855 = 28525283) B28525283
theorem B12677903 : Blo 1977435 12677903 := bstep (se 1 (by rfl) ⟨9508427, by rfl⟩ : syracuseStep 12677903 = 19016855) B19016855
theorem B8451935 : Blo 1977435 8451935 := bstep (se 1 (by rfl) ⟨6338951, by rfl⟩ : syracuseStep 8451935 = 12677903) B12677903
theorem B5634623 : Blo 1977435 5634623 := bstep (se 1 (by rfl) ⟨4225967, by rfl⟩ : syracuseStep 5634623 = 8451935) B8451935
theorem B15025661 : Blo 1977435 15025661 := bstep (se 3 (by rfl) ⟨2817311, by rfl⟩ : syracuseStep 15025661 = 5634623) B5634623
theorem B10017107 : Blo 1977435 10017107 := bstep (se 1 (by rfl) ⟨7512830, by rfl⟩ : syracuseStep 10017107 = 15025661) B15025661
theorem B6678071 : Blo 1977435 6678071 := bstep (se 1 (by rfl) ⟨5008553, by rfl⟩ : syracuseStep 6678071 = 10017107) B10017107
theorem B4452047 : Blo 1977435 4452047 := bstep (se 1 (by rfl) ⟨3339035, by rfl⟩ : syracuseStep 4452047 = 6678071) B6678071
theorem B2968031 : Blo 1977435 2968031 := bstep (se 1 (by rfl) ⟨2226023, by rfl⟩ : syracuseStep 2968031 = 4452047) B4452047
theorem B1978687 : Blo 1977435 1978687 := bstep (se 1 (by rfl) ⟨1484015, by rfl⟩ : syracuseStep 1978687 = 2968031) B2968031
theorem B2968037 : Blo 1977435 2968037 := bbase (se 4 (by rfl) ⟨278253, by rfl⟩ : syracuseStep 2968037 = 556507) (by norm_num)
theorem B1978691 : Blo 1977435 1978691 := bstep (se 1 (by rfl) ⟨1484018, by rfl⟩ : syracuseStep 1978691 = 2968037) B2968037
theorem B2377117 : Blo 1977435 2377117 := bbase (se 3 (by rfl) ⟨445709, by rfl⟩ : syracuseStep 2377117 = 891419) (by norm_num)
theorem B12677957 : Blo 1977435 12677957 := bstep (se 4 (by rfl) ⟨1188558, by rfl⟩ : syracuseStep 12677957 = 2377117) B2377117
theorem B8451971 : Blo 1977435 8451971 := bstep (se 1 (by rfl) ⟨6338978, by rfl⟩ : syracuseStep 8451971 = 12677957) B12677957
theorem B5634647 : Blo 1977435 5634647 := bstep (se 1 (by rfl) ⟨4225985, by rfl⟩ : syracuseStep 5634647 = 8451971) B8451971
theorem B3756431 : Blo 1977435 3756431 := bstep (se 1 (by rfl) ⟨2817323, by rfl⟩ : syracuseStep 3756431 = 5634647) B5634647
theorem B2504287 : Blo 1977435 2504287 := bstep (se 1 (by rfl) ⟨1878215, by rfl⟩ : syracuseStep 2504287 = 3756431) B3756431
theorem B3339049 : Blo 1977435 3339049 := bstep (se 2 (by rfl) ⟨1252143, by rfl⟩ : syracuseStep 3339049 = 2504287) B2504287
theorem B4452065 : Blo 1977435 4452065 := bstep (se 2 (by rfl) ⟨1669524, by rfl⟩ : syracuseStep 4452065 = 3339049) B3339049
theorem B2968043 : Blo 1977435 2968043 := bstep (se 1 (by rfl) ⟨2226032, by rfl⟩ : syracuseStep 2968043 = 4452065) B4452065
theorem B1978695 : Blo 1977435 1978695 := bstep (se 1 (by rfl) ⟨1484021, by rfl⟩ : syracuseStep 1978695 = 2968043) B2968043
theorem B2226037 : Blo 1977435 2226037 := bbase (se 5 (by rfl) ⟨104345, by rfl⟩ : syracuseStep 2226037 = 208691) (by norm_num)
theorem B2968049 : Blo 1977435 2968049 := bstep (se 2 (by rfl) ⟨1113018, by rfl⟩ : syracuseStep 2968049 = 2226037) B2226037
theorem B1978699 : Blo 1977435 1978699 := bstep (se 1 (by rfl) ⟨1484024, by rfl⟩ : syracuseStep 1978699 = 2968049) B2968049
theorem B2504297 : Blo 1977435 2504297 := bbase (se 2 (by rfl) ⟨939111, by rfl⟩ : syracuseStep 2504297 = 1878223) (by norm_num)
theorem B6678125 : Blo 1977435 6678125 := bstep (se 3 (by rfl) ⟨1252148, by rfl⟩ : syracuseStep 6678125 = 2504297) B2504297
theorem B4452083 : Blo 1977435 4452083 := bstep (se 1 (by rfl) ⟨3339062, by rfl⟩ : syracuseStep 4452083 = 6678125) B6678125
theorem B2968055 : Blo 1977435 2968055 := bstep (se 1 (by rfl) ⟨2226041, by rfl⟩ : syracuseStep 2968055 = 4452083) B4452083
theorem B1978703 : Blo 1977435 1978703 := bstep (se 1 (by rfl) ⟨1484027, by rfl⟩ : syracuseStep 1978703 = 2968055) B2968055
theorem B2968061 : Blo 1977435 2968061 := bbase (se 3 (by rfl) ⟨556511, by rfl⟩ : syracuseStep 2968061 = 1113023) (by norm_num)
theorem B1978707 : Blo 1977435 1978707 := bstep (se 1 (by rfl) ⟨1484030, by rfl⟩ : syracuseStep 1978707 = 2968061) B2968061
theorem B4452101 : Blo 1977435 4452101 := bbase (se 4 (by rfl) ⟨417384, by rfl⟩ : syracuseStep 4452101 = 834769) (by norm_num)
theorem B2968067 : Blo 1977435 2968067 := bstep (se 1 (by rfl) ⟨2226050, by rfl⟩ : syracuseStep 2968067 = 4452101) B4452101
theorem B1978711 : Blo 1977435 1978711 := bstep (se 1 (by rfl) ⟨1484033, by rfl⟩ : syracuseStep 1978711 = 2968067) B2968067
theorem B3756469 : Blo 1977435 3756469 := bbase (se 5 (by rfl) ⟨176084, by rfl⟩ : syracuseStep 3756469 = 352169) (by norm_num)
theorem B5008625 : Blo 1977435 5008625 := bstep (se 2 (by rfl) ⟨1878234, by rfl⟩ : syracuseStep 5008625 = 3756469) B3756469
theorem B3339083 : Blo 1977435 3339083 := bstep (se 1 (by rfl) ⟨2504312, by rfl⟩ : syracuseStep 3339083 = 5008625) B5008625
theorem B2226055 : Blo 1977435 2226055 := bstep (se 1 (by rfl) ⟨1669541, by rfl⟩ : syracuseStep 2226055 = 3339083) B3339083
theorem B2968073 : Blo 1977435 2968073 := bstep (se 2 (by rfl) ⟨1113027, by rfl⟩ : syracuseStep 2968073 = 2226055) B2226055
theorem B1978715 : Blo 1977435 1978715 := bstep (se 1 (by rfl) ⟨1484036, by rfl⟩ : syracuseStep 1978715 = 2968073) B2968073
theorem B10017269 : Blo 1977435 10017269 := bbase (se 5 (by rfl) ⟨469559, by rfl⟩ : syracuseStep 10017269 = 939119) (by norm_num)
theorem B6678179 : Blo 1977435 6678179 := bstep (se 1 (by rfl) ⟨5008634, by rfl⟩ : syracuseStep 6678179 = 10017269) B10017269
theorem B4452119 : Blo 1977435 4452119 := bstep (se 1 (by rfl) ⟨3339089, by rfl⟩ : syracuseStep 4452119 = 6678179) B6678179
theorem B2968079 : Blo 1977435 2968079 := bstep (se 1 (by rfl) ⟨2226059, by rfl⟩ : syracuseStep 2968079 = 4452119) B4452119
theorem B1978719 : Blo 1977435 1978719 := bstep (se 1 (by rfl) ⟨1484039, by rfl⟩ : syracuseStep 1978719 = 2968079) B2968079
theorem B2968085 : Blo 1977435 2968085 := bbase (se 6 (by rfl) ⟨69564, by rfl⟩ : syracuseStep 2968085 = 139129) (by norm_num)
theorem B1978723 : Blo 1977435 1978723 := bstep (se 1 (by rfl) ⟨1484042, by rfl⟩ : syracuseStep 1978723 = 2968085) B2968085
theorem B16904213 : Blo 1977435 16904213 := bbase (se 6 (by rfl) ⟨396192, by rfl⟩ : syracuseStep 16904213 = 792385) (by norm_num)
theorem B11269475 : Blo 1977435 11269475 := bstep (se 1 (by rfl) ⟨8452106, by rfl⟩ : syracuseStep 11269475 = 16904213) B16904213
theorem B7512983 : Blo 1977435 7512983 := bstep (se 1 (by rfl) ⟨5634737, by rfl⟩ : syracuseStep 7512983 = 11269475) B11269475
theorem B5008655 : Blo 1977435 5008655 := bstep (se 1 (by rfl) ⟨3756491, by rfl⟩ : syracuseStep 5008655 = 7512983) B7512983
theorem B3339103 : Blo 1977435 3339103 := bstep (se 1 (by rfl) ⟨2504327, by rfl⟩ : syracuseStep 3339103 = 5008655) B5008655
theorem B4452137 : Blo 1977435 4452137 := bstep (se 2 (by rfl) ⟨1669551, by rfl⟩ : syracuseStep 4452137 = 3339103) B3339103
theorem B2968091 : Blo 1977435 2968091 := bstep (se 1 (by rfl) ⟨2226068, by rfl⟩ : syracuseStep 2968091 = 4452137) B4452137
theorem B1978727 : Blo 1977435 1978727 := bstep (se 1 (by rfl) ⟨1484045, by rfl⟩ : syracuseStep 1978727 = 2968091) B2968091
theorem B2226073 : Blo 1977435 2226073 := bbase (se 2 (by rfl) ⟨834777, by rfl⟩ : syracuseStep 2226073 = 1669555) (by norm_num)
theorem B2968097 : Blo 1977435 2968097 := bstep (se 2 (by rfl) ⟨1113036, by rfl⟩ : syracuseStep 2968097 = 2226073) B2226073
theorem B1978731 : Blo 1977435 1978731 := bstep (se 1 (by rfl) ⟨1484048, by rfl⟩ : syracuseStep 1978731 = 2968097) B2968097
theorem B7513013 : Blo 1977435 7513013 := bbase (se 5 (by rfl) ⟨352172, by rfl⟩ : syracuseStep 7513013 = 704345) (by norm_num)
theorem B5008675 : Blo 1977435 5008675 := bstep (se 1 (by rfl) ⟨3756506, by rfl⟩ : syracuseStep 5008675 = 7513013) B7513013
theorem B6678233 : Blo 1977435 6678233 := bstep (se 2 (by rfl) ⟨2504337, by rfl⟩ : syracuseStep 6678233 = 5008675) B5008675
theorem B4452155 : Blo 1977435 4452155 := bstep (se 1 (by rfl) ⟨3339116, by rfl⟩ : syracuseStep 4452155 = 6678233) B6678233
theorem B2968103 : Blo 1977435 2968103 := bstep (se 1 (by rfl) ⟨2226077, by rfl⟩ : syracuseStep 2968103 = 4452155) B4452155
theorem B1978735 : Blo 1977435 1978735 := bstep (se 1 (by rfl) ⟨1484051, by rfl⟩ : syracuseStep 1978735 = 2968103) B2968103
theorem B2968109 : Blo 1977435 2968109 := bbase (se 3 (by rfl) ⟨556520, by rfl⟩ : syracuseStep 2968109 = 1113041) (by norm_num)
theorem B1978739 : Blo 1977435 1978739 := bstep (se 1 (by rfl) ⟨1484054, by rfl⟩ : syracuseStep 1978739 = 2968109) B2968109
theorem B4452173 : Blo 1977435 4452173 := bbase (se 3 (by rfl) ⟨834782, by rfl⟩ : syracuseStep 4452173 = 1669565) (by norm_num)
theorem B2968115 : Blo 1977435 2968115 := bstep (se 1 (by rfl) ⟨2226086, by rfl⟩ : syracuseStep 2968115 = 4452173) B4452173
theorem B1978743 : Blo 1977435 1978743 := bstep (se 1 (by rfl) ⟨1484057, by rfl⟩ : syracuseStep 1978743 = 2968115) B2968115
theorem B2504353 : Blo 1977435 2504353 := bbase (se 2 (by rfl) ⟨939132, by rfl⟩ : syracuseStep 2504353 = 1878265) (by norm_num)
theorem B3339137 : Blo 1977435 3339137 := bstep (se 2 (by rfl) ⟨1252176, by rfl⟩ : syracuseStep 3339137 = 2504353) B2504353
theorem B2226091 : Blo 1977435 2226091 := bstep (se 1 (by rfl) ⟨1669568, by rfl⟩ : syracuseStep 2226091 = 3339137) B3339137
theorem B2968121 : Blo 1977435 2968121 := bstep (se 2 (by rfl) ⟨1113045, by rfl⟩ : syracuseStep 2968121 = 2226091) B2226091
theorem B1978747 : Blo 1977435 1978747 := bstep (se 1 (by rfl) ⟨1484060, by rfl⟩ : syracuseStep 1978747 = 2968121) B2968121
theorem B22539221 : Blo 1977435 22539221 := bbase (se 7 (by rfl) ⟨264131, by rfl⟩ : syracuseStep 22539221 = 528263) (by norm_num)
theorem B15026147 : Blo 1977435 15026147 := bstep (se 1 (by rfl) ⟨11269610, by rfl⟩ : syracuseStep 15026147 = 22539221) B22539221
theorem B10017431 : Blo 1977435 10017431 := bstep (se 1 (by rfl) ⟨7513073, by rfl⟩ : syracuseStep 10017431 = 15026147) B15026147
theorem B6678287 : Blo 1977435 6678287 := bstep (se 1 (by rfl) ⟨5008715, by rfl⟩ : syracuseStep 6678287 = 10017431) B10017431
theorem B4452191 : Blo 1977435 4452191 := bstep (se 1 (by rfl) ⟨3339143, by rfl⟩ : syracuseStep 4452191 = 6678287) B6678287
theorem B2968127 : Blo 1977435 2968127 := bstep (se 1 (by rfl) ⟨2226095, by rfl⟩ : syracuseStep 2968127 = 4452191) B4452191
theorem B1978751 : Blo 1977435 1978751 := bstep (se 1 (by rfl) ⟨1484063, by rfl⟩ : syracuseStep 1978751 = 2968127) B2968127
theorem B2968133 : Blo 1977435 2968133 := bbase (se 4 (by rfl) ⟨278262, by rfl⟩ : syracuseStep 2968133 = 556525) (by norm_num)
theorem B1978755 : Blo 1977435 1978755 := bstep (se 1 (by rfl) ⟨1484066, by rfl⟩ : syracuseStep 1978755 = 2968133) B2968133
theorem B3339157 : Blo 1977435 3339157 := bbase (se 6 (by rfl) ⟨78261, by rfl⟩ : syracuseStep 3339157 = 156523) (by norm_num)
theorem B4452209 : Blo 1977435 4452209 := bstep (se 2 (by rfl) ⟨1669578, by rfl⟩ : syracuseStep 4452209 = 3339157) B3339157
theorem B2968139 : Blo 1977435 2968139 := bstep (se 1 (by rfl) ⟨2226104, by rfl⟩ : syracuseStep 2968139 = 4452209) B4452209
theorem B1978759 : Blo 1977435 1978759 := bstep (se 1 (by rfl) ⟨1484069, by rfl⟩ : syracuseStep 1978759 = 2968139) B2968139
theorem B2226109 : Blo 1977435 2226109 := bbase (se 3 (by rfl) ⟨417395, by rfl⟩ : syracuseStep 2226109 = 834791) (by norm_num)
theorem B2968145 : Blo 1977435 2968145 := bstep (se 2 (by rfl) ⟨1113054, by rfl⟩ : syracuseStep 2968145 = 2226109) B2226109
theorem B1978763 : Blo 1977435 1978763 := bstep (se 1 (by rfl) ⟨1484072, by rfl⟩ : syracuseStep 1978763 = 2968145) B2968145
theorem B6678341 : Blo 1977435 6678341 := bbase (se 4 (by rfl) ⟨626094, by rfl⟩ : syracuseStep 6678341 = 1252189) (by norm_num)
theorem B4452227 : Blo 1977435 4452227 := bstep (se 1 (by rfl) ⟨3339170, by rfl⟩ : syracuseStep 4452227 = 6678341) B6678341
theorem B2968151 : Blo 1977435 2968151 := bstep (se 1 (by rfl) ⟨2226113, by rfl⟩ : syracuseStep 2968151 = 4452227) B4452227
theorem B1978767 : Blo 1977435 1978767 := bstep (se 1 (by rfl) ⟨1484075, by rfl⟩ : syracuseStep 1978767 = 2968151) B2968151
theorem B2968157 : Blo 1977435 2968157 := bbase (se 3 (by rfl) ⟨556529, by rfl⟩ : syracuseStep 2968157 = 1113059) (by norm_num)
theorem B1978771 : Blo 1977435 1978771 := bstep (se 1 (by rfl) ⟨1484078, by rfl⟩ : syracuseStep 1978771 = 2968157) B2968157
theorem B4452245 : Blo 1977435 4452245 := bbase (se 6 (by rfl) ⟨104349, by rfl⟩ : syracuseStep 4452245 = 208699) (by norm_num)
theorem B2968163 : Blo 1977435 2968163 := bstep (se 1 (by rfl) ⟨2226122, by rfl⟩ : syracuseStep 2968163 = 4452245) B4452245
theorem B1978775 : Blo 1977435 1978775 := bstep (se 1 (by rfl) ⟨1484081, by rfl⟩ : syracuseStep 1978775 = 2968163) B2968163
theorem B4226165 : Blo 1977435 4226165 := bbase (se 5 (by rfl) ⟨198101, by rfl⟩ : syracuseStep 4226165 = 396203) (by norm_num)
theorem B2817443 : Blo 1977435 2817443 := bstep (se 1 (by rfl) ⟨2113082, by rfl⟩ : syracuseStep 2817443 = 4226165) B4226165
theorem B7513181 : Blo 1977435 7513181 := bstep (se 3 (by rfl) ⟨1408721, by rfl⟩ : syracuseStep 7513181 = 2817443) B2817443
theorem B5008787 : Blo 1977435 5008787 := bstep (se 1 (by rfl) ⟨3756590, by rfl⟩ : syracuseStep 5008787 = 7513181) B7513181
theorem B3339191 : Blo 1977435 3339191 := bstep (se 1 (by rfl) ⟨2504393, by rfl⟩ : syracuseStep 3339191 = 5008787) B5008787
theorem B2226127 : Blo 1977435 2226127 := bstep (se 1 (by rfl) ⟨1669595, by rfl⟩ : syracuseStep 2226127 = 3339191) B3339191
theorem B2968169 : Blo 1977435 2968169 := bstep (se 2 (by rfl) ⟨1113063, by rfl⟩ : syracuseStep 2968169 = 2226127) B2226127
theorem B1978779 : Blo 1977435 1978779 := bstep (se 1 (by rfl) ⟨1484084, by rfl⟩ : syracuseStep 1978779 = 2968169) B2968169
theorem B3384757 : Blo 1977435 3384757 := bbase (se 5 (by rfl) ⟨158660, by rfl⟩ : syracuseStep 3384757 = 317321) (by norm_num)
theorem B4513009 : Blo 1977435 4513009 := bstep (se 2 (by rfl) ⟨1692378, by rfl⟩ : syracuseStep 4513009 = 3384757) B3384757
theorem B6017345 : Blo 1977435 6017345 := bstep (se 2 (by rfl) ⟨2256504, by rfl⟩ : syracuseStep 6017345 = 4513009) B4513009
theorem B4011563 : Blo 1977435 4011563 := bstep (se 1 (by rfl) ⟨3008672, by rfl⟩ : syracuseStep 4011563 = 6017345) B6017345
theorem B10697501 : Blo 1977435 10697501 := bstep (se 3 (by rfl) ⟨2005781, by rfl⟩ : syracuseStep 10697501 = 4011563) B4011563
theorem B7131667 : Blo 1977435 7131667 := bstep (se 1 (by rfl) ⟨5348750, by rfl⟩ : syracuseStep 7131667 = 10697501) B10697501
theorem B9508889 : Blo 1977435 9508889 := bstep (se 2 (by rfl) ⟨3565833, by rfl⟩ : syracuseStep 9508889 = 7131667) B7131667
theorem B6339259 : Blo 1977435 6339259 := bstep (se 1 (by rfl) ⟨4754444, by rfl⟩ : syracuseStep 6339259 = 9508889) B9508889
theorem B8452345 : Blo 1977435 8452345 := bstep (se 2 (by rfl) ⟨3169629, by rfl⟩ : syracuseStep 8452345 = 6339259) B6339259
theorem B11269793 : Blo 1977435 11269793 := bstep (se 2 (by rfl) ⟨4226172, by rfl⟩ : syracuseStep 11269793 = 8452345) B8452345
theorem B7513195 : Blo 1977435 7513195 := bstep (se 1 (by rfl) ⟨5634896, by rfl⟩ : syracuseStep 7513195 = 11269793) B11269793
theorem B10017593 : Blo 1977435 10017593 := bstep (se 2 (by rfl) ⟨3756597, by rfl⟩ : syracuseStep 10017593 = 7513195) B7513195
theorem B6678395 : Blo 1977435 6678395 := bstep (se 1 (by rfl) ⟨5008796, by rfl⟩ : syracuseStep 6678395 = 10017593) B10017593
theorem B4452263 : Blo 1977435 4452263 := bstep (se 1 (by rfl) ⟨3339197, by rfl⟩ : syracuseStep 4452263 = 6678395) B6678395
theorem B2968175 : Blo 1977435 2968175 := bstep (se 1 (by rfl) ⟨2226131, by rfl⟩ : syracuseStep 2968175 = 4452263) B4452263
theorem B1978783 : Blo 1977435 1978783 := bstep (se 1 (by rfl) ⟨1484087, by rfl⟩ : syracuseStep 1978783 = 2968175) B2968175
theorem B2968181 : Blo 1977435 2968181 := bbase (se 5 (by rfl) ⟨139133, by rfl⟩ : syracuseStep 2968181 = 278267) (by norm_num)
theorem B1978787 : Blo 1977435 1978787 := bstep (se 1 (by rfl) ⟨1484090, by rfl⟩ : syracuseStep 1978787 = 2968181) B2968181
theorem B3756613 : Blo 1977435 3756613 := bbase (se 4 (by rfl) ⟨352182, by rfl⟩ : syracuseStep 3756613 = 704365) (by norm_num)
theorem B5008817 : Blo 1977435 5008817 := bstep (se 2 (by rfl) ⟨1878306, by rfl⟩ : syracuseStep 5008817 = 3756613) B3756613
theorem B3339211 : Blo 1977435 3339211 := bstep (se 1 (by rfl) ⟨2504408, by rfl⟩ : syracuseStep 3339211 = 5008817) B5008817
theorem B4452281 : Blo 1977435 4452281 := bstep (se 2 (by rfl) ⟨1669605, by rfl⟩ : syracuseStep 4452281 = 3339211) B3339211
theorem B2968187 : Blo 1977435 2968187 := bstep (se 1 (by rfl) ⟨2226140, by rfl⟩ : syracuseStep 2968187 = 4452281) B4452281
theorem B1978791 : Blo 1977435 1978791 := bstep (se 1 (by rfl) ⟨1484093, by rfl⟩ : syracuseStep 1978791 = 2968187) B2968187
theorem B2226145 : Blo 1977435 2226145 := bbase (se 2 (by rfl) ⟨834804, by rfl⟩ : syracuseStep 2226145 = 1669609) (by norm_num)
theorem B2968193 : Blo 1977435 2968193 := bstep (se 2 (by rfl) ⟨1113072, by rfl⟩ : syracuseStep 2968193 = 2226145) B2226145
theorem B1978795 : Blo 1977435 1978795 := bstep (se 1 (by rfl) ⟨1484096, by rfl⟩ : syracuseStep 1978795 = 2968193) B2968193
theorem B5008837 : Blo 1977435 5008837 := bbase (se 4 (by rfl) ⟨469578, by rfl⟩ : syracuseStep 5008837 = 939157) (by norm_num)
theorem B6678449 : Blo 1977435 6678449 := bstep (se 2 (by rfl) ⟨2504418, by rfl⟩ : syracuseStep 6678449 = 5008837) B5008837
theorem B4452299 : Blo 1977435 4452299 := bstep (se 1 (by rfl) ⟨3339224, by rfl⟩ : syracuseStep 4452299 = 6678449) B6678449
theorem B2968199 : Blo 1977435 2968199 := bstep (se 1 (by rfl) ⟨2226149, by rfl⟩ : syracuseStep 2968199 = 4452299) B4452299
theorem B1978799 : Blo 1977435 1978799 := bstep (se 1 (by rfl) ⟨1484099, by rfl⟩ : syracuseStep 1978799 = 2968199) B2968199
theorem B2968205 : Blo 1977435 2968205 := bbase (se 3 (by rfl) ⟨556538, by rfl⟩ : syracuseStep 2968205 = 1113077) (by norm_num)
theorem B1978803 : Blo 1977435 1978803 := bstep (se 1 (by rfl) ⟨1484102, by rfl⟩ : syracuseStep 1978803 = 2968205) B2968205
theorem B4452317 : Blo 1977435 4452317 := bbase (se 3 (by rfl) ⟨834809, by rfl⟩ : syracuseStep 4452317 = 1669619) (by norm_num)
theorem B2968211 : Blo 1977435 2968211 := bstep (se 1 (by rfl) ⟨2226158, by rfl⟩ : syracuseStep 2968211 = 4452317) B4452317
theorem B1978807 : Blo 1977435 1978807 := bstep (se 1 (by rfl) ⟨1484105, by rfl⟩ : syracuseStep 1978807 = 2968211) B2968211
theorem B3339245 : Blo 1977435 3339245 := bbase (se 3 (by rfl) ⟨626108, by rfl⟩ : syracuseStep 3339245 = 1252217) (by norm_num)
theorem B2226163 : Blo 1977435 2226163 := bstep (se 1 (by rfl) ⟨1669622, by rfl⟩ : syracuseStep 2226163 = 3339245) B3339245
theorem B2968217 : Blo 1977435 2968217 := bstep (se 2 (by rfl) ⟨1113081, by rfl⟩ : syracuseStep 2968217 = 2226163) B2226163
theorem B1978811 : Blo 1977435 1978811 := bstep (se 1 (by rfl) ⟨1484108, by rfl⟩ : syracuseStep 1978811 = 2968217) B2968217
theorem B5348837 : Blo 1977435 5348837 := bbase (se 4 (by rfl) ⟨501453, by rfl⟩ : syracuseStep 5348837 = 1002907) (by norm_num)
theorem B3565891 : Blo 1977435 3565891 := bstep (se 1 (by rfl) ⟨2674418, by rfl⟩ : syracuseStep 3565891 = 5348837) B5348837
theorem B4754521 : Blo 1977435 4754521 := bstep (se 2 (by rfl) ⟨1782945, by rfl⟩ : syracuseStep 4754521 = 3565891) B3565891
theorem B25357445 : Blo 1977435 25357445 := bstep (se 4 (by rfl) ⟨2377260, by rfl⟩ : syracuseStep 25357445 = 4754521) B4754521
theorem B16904963 : Blo 1977435 16904963 := bstep (se 1 (by rfl) ⟨12678722, by rfl⟩ : syracuseStep 16904963 = 25357445) B25357445
theorem B11269975 : Blo 1977435 11269975 := bstep (se 1 (by rfl) ⟨8452481, by rfl⟩ : syracuseStep 11269975 = 16904963) B16904963
theorem B15026633 : Blo 1977435 15026633 := bstep (se 2 (by rfl) ⟨5634987, by rfl⟩ : syracuseStep 15026633 = 11269975) B11269975
theorem B10017755 : Blo 1977435 10017755 := bstep (se 1 (by rfl) ⟨7513316, by rfl⟩ : syracuseStep 10017755 = 15026633) B15026633
theorem B6678503 : Blo 1977435 6678503 := bstep (se 1 (by rfl) ⟨5008877, by rfl⟩ : syracuseStep 6678503 = 10017755) B10017755
theorem B4452335 : Blo 1977435 4452335 := bstep (se 1 (by rfl) ⟨3339251, by rfl⟩ : syracuseStep 4452335 = 6678503) B6678503
theorem B2968223 : Blo 1977435 2968223 := bstep (se 1 (by rfl) ⟨2226167, by rfl⟩ : syracuseStep 2968223 = 4452335) B4452335
theorem B1978815 : Blo 1977435 1978815 := bstep (se 1 (by rfl) ⟨1484111, by rfl⟩ : syracuseStep 1978815 = 2968223) B2968223
theorem B2968229 : Blo 1977435 2968229 := bbase (se 4 (by rfl) ⟨278271, by rfl⟩ : syracuseStep 2968229 = 556543) (by norm_num)
theorem B1978819 : Blo 1977435 1978819 := bstep (se 1 (by rfl) ⟨1484114, by rfl⟩ : syracuseStep 1978819 = 2968229) B2968229
theorem B2504449 : Blo 1977435 2504449 := bbase (se 2 (by rfl) ⟨939168, by rfl⟩ : syracuseStep 2504449 = 1878337) (by norm_num)
theorem B3339265 : Blo 1977435 3339265 := bstep (se 2 (by rfl) ⟨1252224, by rfl⟩ : syracuseStep 3339265 = 2504449) B2504449
theorem B4452353 : Blo 1977435 4452353 := bstep (se 2 (by rfl) ⟨1669632, by rfl⟩ : syracuseStep 4452353 = 3339265) B3339265
theorem B2968235 : Blo 1977435 2968235 := bstep (se 1 (by rfl) ⟨2226176, by rfl⟩ : syracuseStep 2968235 = 4452353) B4452353
theorem B1978823 : Blo 1977435 1978823 := bstep (se 1 (by rfl) ⟨1484117, by rfl⟩ : syracuseStep 1978823 = 2968235) B2968235
theorem B2226181 : Blo 1977435 2226181 := bbase (se 4 (by rfl) ⟨208704, by rfl⟩ : syracuseStep 2226181 = 417409) (by norm_num)
theorem B2968241 : Blo 1977435 2968241 := bstep (se 2 (by rfl) ⟨1113090, by rfl⟩ : syracuseStep 2968241 = 2226181) B2226181
theorem B1978827 : Blo 1977435 1978827 := bstep (se 1 (by rfl) ⟨1484120, by rfl⟩ : syracuseStep 1978827 = 2968241) B2968241
theorem B2817517 : Blo 1977435 2817517 := bbase (se 3 (by rfl) ⟨528284, by rfl⟩ : syracuseStep 2817517 = 1056569) (by norm_num)
theorem B3756689 : Blo 1977435 3756689 := bstep (se 2 (by rfl) ⟨1408758, by rfl⟩ : syracuseStep 3756689 = 2817517) B2817517
theorem B2504459 : Blo 1977435 2504459 := bstep (se 1 (by rfl) ⟨1878344, by rfl⟩ : syracuseStep 2504459 = 3756689) B3756689
theorem B6678557 : Blo 1977435 6678557 := bstep (se 3 (by rfl) ⟨1252229, by rfl⟩ : syracuseStep 6678557 = 2504459) B2504459
theorem B4452371 : Blo 1977435 4452371 := bstep (se 1 (by rfl) ⟨3339278, by rfl⟩ : syracuseStep 4452371 = 6678557) B6678557
theorem B2968247 : Blo 1977435 2968247 := bstep (se 1 (by rfl) ⟨2226185, by rfl⟩ : syracuseStep 2968247 = 4452371) B4452371
theorem B1978831 : Blo 1977435 1978831 := bstep (se 1 (by rfl) ⟨1484123, by rfl⟩ : syracuseStep 1978831 = 2968247) B2968247
theorem B2968253 : Blo 1977435 2968253 := bbase (se 3 (by rfl) ⟨556547, by rfl⟩ : syracuseStep 2968253 = 1113095) (by norm_num)
theorem B1978835 : Blo 1977435 1978835 := bstep (se 1 (by rfl) ⟨1484126, by rfl⟩ : syracuseStep 1978835 = 2968253) B2968253
theorem B4452389 : Blo 1977435 4452389 := bbase (se 4 (by rfl) ⟨417411, by rfl⟩ : syracuseStep 4452389 = 834823) (by norm_num)
theorem B2968259 : Blo 1977435 2968259 := bstep (se 1 (by rfl) ⟨2226194, by rfl⟩ : syracuseStep 2968259 = 4452389) B4452389
theorem B1978839 : Blo 1977435 1978839 := bstep (se 1 (by rfl) ⟨1484129, by rfl⟩ : syracuseStep 1978839 = 2968259) B2968259
theorem B5008949 : Blo 1977435 5008949 := bbase (se 5 (by rfl) ⟨234794, by rfl⟩ : syracuseStep 5008949 = 469589) (by norm_num)
theorem B3339299 : Blo 1977435 3339299 := bstep (se 1 (by rfl) ⟨2504474, by rfl⟩ : syracuseStep 3339299 = 5008949) B5008949
theorem B2226199 : Blo 1977435 2226199 := bstep (se 1 (by rfl) ⟨1669649, by rfl⟩ : syracuseStep 2226199 = 3339299) B3339299
theorem B2968265 : Blo 1977435 2968265 := bstep (se 2 (by rfl) ⟨1113099, by rfl⟩ : syracuseStep 2968265 = 2226199) B2226199
theorem B1978843 : Blo 1977435 1978843 := bstep (se 1 (by rfl) ⟨1484132, by rfl⟩ : syracuseStep 1978843 = 2968265) B2968265
theorem B3565949 : Blo 1977435 3565949 := bbase (se 3 (by rfl) ⟨668615, by rfl⟩ : syracuseStep 3565949 = 1337231) (by norm_num)
theorem B9509197 : Blo 1977435 9509197 := bstep (se 3 (by rfl) ⟨1782974, by rfl⟩ : syracuseStep 9509197 = 3565949) B3565949
theorem B12678929 : Blo 1977435 12678929 := bstep (se 2 (by rfl) ⟨4754598, by rfl⟩ : syracuseStep 12678929 = 9509197) B9509197
theorem B8452619 : Blo 1977435 8452619 := bstep (se 1 (by rfl) ⟨6339464, by rfl⟩ : syracuseStep 8452619 = 12678929) B12678929
theorem B5635079 : Blo 1977435 5635079 := bstep (se 1 (by rfl) ⟨4226309, by rfl⟩ : syracuseStep 5635079 = 8452619) B8452619
theorem B3756719 : Blo 1977435 3756719 := bstep (se 1 (by rfl) ⟨2817539, by rfl⟩ : syracuseStep 3756719 = 5635079) B5635079
theorem B10017917 : Blo 1977435 10017917 := bstep (se 3 (by rfl) ⟨1878359, by rfl⟩ : syracuseStep 10017917 = 3756719) B3756719
theorem B6678611 : Blo 1977435 6678611 := bstep (se 1 (by rfl) ⟨5008958, by rfl⟩ : syracuseStep 6678611 = 10017917) B10017917
theorem B4452407 : Blo 1977435 4452407 := bstep (se 1 (by rfl) ⟨3339305, by rfl⟩ : syracuseStep 4452407 = 6678611) B6678611
theorem B2968271 : Blo 1977435 2968271 := bstep (se 1 (by rfl) ⟨2226203, by rfl⟩ : syracuseStep 2968271 = 4452407) B4452407
theorem B1978847 : Blo 1977435 1978847 := bstep (se 1 (by rfl) ⟨1484135, by rfl⟩ : syracuseStep 1978847 = 2968271) B2968271
theorem B2968277 : Blo 1977435 2968277 := bbase (se 7 (by rfl) ⟨34784, by rfl⟩ : syracuseStep 2968277 = 69569) (by norm_num)
theorem B1978851 : Blo 1977435 1978851 := bstep (se 1 (by rfl) ⟨1484138, by rfl⟩ : syracuseStep 1978851 = 2968277) B2968277
theorem B9509237 : Blo 1977435 9509237 := bbase (se 5 (by rfl) ⟨445745, by rfl⟩ : syracuseStep 9509237 = 891491) (by norm_num)
theorem B6339491 : Blo 1977435 6339491 := bstep (se 1 (by rfl) ⟨4754618, by rfl⟩ : syracuseStep 6339491 = 9509237) B9509237
theorem B4226327 : Blo 1977435 4226327 := bstep (se 1 (by rfl) ⟨3169745, by rfl⟩ : syracuseStep 4226327 = 6339491) B6339491
theorem B2817551 : Blo 1977435 2817551 := bstep (se 1 (by rfl) ⟨2113163, by rfl⟩ : syracuseStep 2817551 = 4226327) B4226327
theorem B7513469 : Blo 1977435 7513469 := bstep (se 3 (by rfl) ⟨1408775, by rfl⟩ : syracuseStep 7513469 = 2817551) B2817551
theorem B5008979 : Blo 1977435 5008979 := bstep (se 1 (by rfl) ⟨3756734, by rfl⟩ : syracuseStep 5008979 = 7513469) B7513469
theorem B3339319 : Blo 1977435 3339319 := bstep (se 1 (by rfl) ⟨2504489, by rfl⟩ : syracuseStep 3339319 = 5008979) B5008979
theorem B4452425 : Blo 1977435 4452425 := bstep (se 2 (by rfl) ⟨1669659, by rfl⟩ : syracuseStep 4452425 = 3339319) B3339319
theorem B2968283 : Blo 1977435 2968283 := bstep (se 1 (by rfl) ⟨2226212, by rfl⟩ : syracuseStep 2968283 = 4452425) B4452425
theorem B1978855 : Blo 1977435 1978855 := bstep (se 1 (by rfl) ⟨1484141, by rfl⟩ : syracuseStep 1978855 = 2968283) B2968283
theorem B2226217 : Blo 1977435 2226217 := bbase (se 2 (by rfl) ⟨834831, by rfl⟩ : syracuseStep 2226217 = 1669663) (by norm_num)
theorem B2968289 : Blo 1977435 2968289 := bstep (se 2 (by rfl) ⟨1113108, by rfl⟩ : syracuseStep 2968289 = 2226217) B2226217
theorem B1978859 : Blo 1977435 1978859 := bstep (se 1 (by rfl) ⟨1484144, by rfl⟩ : syracuseStep 1978859 = 2968289) B2968289
theorem B4011725 : Blo 1977435 4011725 := bbase (se 3 (by rfl) ⟨752198, by rfl⟩ : syracuseStep 4011725 = 1504397) (by norm_num)
theorem B10697933 : Blo 1977435 10697933 := bstep (se 3 (by rfl) ⟨2005862, by rfl⟩ : syracuseStep 10697933 = 4011725) B4011725
theorem B28527821 : Blo 1977435 28527821 := bstep (se 3 (by rfl) ⟨5348966, by rfl⟩ : syracuseStep 28527821 = 10697933) B10697933
theorem B19018547 : Blo 1977435 19018547 := bstep (se 1 (by rfl) ⟨14263910, by rfl⟩ : syracuseStep 19018547 = 28527821) B28527821
theorem B12679031 : Blo 1977435 12679031 := bstep (se 1 (by rfl) ⟨9509273, by rfl⟩ : syracuseStep 12679031 = 19018547) B19018547
theorem B8452687 : Blo 1977435 8452687 := bstep (se 1 (by rfl) ⟨6339515, by rfl⟩ : syracuseStep 8452687 = 12679031) B12679031
theorem B11270249 : Blo 1977435 11270249 := bstep (se 2 (by rfl) ⟨4226343, by rfl⟩ : syracuseStep 11270249 = 8452687) B8452687
theorem B7513499 : Blo 1977435 7513499 := bstep (se 1 (by rfl) ⟨5635124, by rfl⟩ : syracuseStep 7513499 = 11270249) B11270249
theorem B5008999 : Blo 1977435 5008999 := bstep (se 1 (by rfl) ⟨3756749, by rfl⟩ : syracuseStep 5008999 = 7513499) B7513499
theorem B6678665 : Blo 1977435 6678665 := bstep (se 2 (by rfl) ⟨2504499, by rfl⟩ : syracuseStep 6678665 = 5008999) B5008999
theorem B4452443 : Blo 1977435 4452443 := bstep (se 1 (by rfl) ⟨3339332, by rfl⟩ : syracuseStep 4452443 = 6678665) B6678665
theorem B2968295 : Blo 1977435 2968295 := bstep (se 1 (by rfl) ⟨2226221, by rfl⟩ : syracuseStep 2968295 = 4452443) B4452443
theorem B1978863 : Blo 1977435 1978863 := bstep (se 1 (by rfl) ⟨1484147, by rfl⟩ : syracuseStep 1978863 = 2968295) B2968295
theorem B2968301 : Blo 1977435 2968301 := bbase (se 3 (by rfl) ⟨556556, by rfl⟩ : syracuseStep 2968301 = 1113113) (by norm_num)
theorem B1978867 : Blo 1977435 1978867 := bstep (se 1 (by rfl) ⟨1484150, by rfl⟩ : syracuseStep 1978867 = 2968301) B2968301
theorem B4452461 : Blo 1977435 4452461 := bbase (se 3 (by rfl) ⟨834836, by rfl⟩ : syracuseStep 4452461 = 1669673) (by norm_num)
theorem B2968307 : Blo 1977435 2968307 := bstep (se 1 (by rfl) ⟨2226230, by rfl⟩ : syracuseStep 2968307 = 4452461) B4452461
theorem B1978871 : Blo 1977435 1978871 := bstep (se 1 (by rfl) ⟨1484153, by rfl⟩ : syracuseStep 1978871 = 2968307) B2968307
theorem B3756773 : Blo 1977435 3756773 := bbase (se 4 (by rfl) ⟨352197, by rfl⟩ : syracuseStep 3756773 = 704395) (by norm_num)
theorem B2504515 : Blo 1977435 2504515 := bstep (se 1 (by rfl) ⟨1878386, by rfl⟩ : syracuseStep 2504515 = 3756773) B3756773
theorem B3339353 : Blo 1977435 3339353 := bstep (se 2 (by rfl) ⟨1252257, by rfl⟩ : syracuseStep 3339353 = 2504515) B2504515
theorem B2226235 : Blo 1977435 2226235 := bstep (se 1 (by rfl) ⟨1669676, by rfl⟩ : syracuseStep 2226235 = 3339353) B3339353
theorem B2968313 : Blo 1977435 2968313 := bstep (se 2 (by rfl) ⟨1113117, by rfl⟩ : syracuseStep 2968313 = 2226235) B2226235
theorem B1978875 : Blo 1977435 1978875 := bstep (se 1 (by rfl) ⟨1484156, by rfl⟩ : syracuseStep 1978875 = 2968313) B2968313
theorem B38037397 : Blo 1977435 38037397 := bbase (se 6 (by rfl) ⟨891501, by rfl⟩ : syracuseStep 38037397 = 1783003) (by norm_num)
theorem B50716529 : Blo 1977435 50716529 := bstep (se 2 (by rfl) ⟨19018698, by rfl⟩ : syracuseStep 50716529 = 38037397) B38037397
theorem B33811019 : Blo 1977435 33811019 := bstep (se 1 (by rfl) ⟨25358264, by rfl⟩ : syracuseStep 33811019 = 50716529) B50716529
theorem B22540679 : Blo 1977435 22540679 := bstep (se 1 (by rfl) ⟨16905509, by rfl⟩ : syracuseStep 22540679 = 33811019) B33811019
theorem B15027119 : Blo 1977435 15027119 := bstep (se 1 (by rfl) ⟨11270339, by rfl⟩ : syracuseStep 15027119 = 22540679) B22540679
theorem B10018079 : Blo 1977435 10018079 := bstep (se 1 (by rfl) ⟨7513559, by rfl⟩ : syracuseStep 10018079 = 15027119) B15027119
theorem B6678719 : Blo 1977435 6678719 := bstep (se 1 (by rfl) ⟨5009039, by rfl⟩ : syracuseStep 6678719 = 10018079) B10018079
theorem B4452479 : Blo 1977435 4452479 := bstep (se 1 (by rfl) ⟨3339359, by rfl⟩ : syracuseStep 4452479 = 6678719) B6678719
theorem B2968319 : Blo 1977435 2968319 := bstep (se 1 (by rfl) ⟨2226239, by rfl⟩ : syracuseStep 2968319 = 4452479) B4452479
theorem B1978879 : Blo 1977435 1978879 := bstep (se 1 (by rfl) ⟨1484159, by rfl⟩ : syracuseStep 1978879 = 2968319) B2968319
theorem B2968325 : Blo 1977435 2968325 := bbase (se 4 (by rfl) ⟨278280, by rfl⟩ : syracuseStep 2968325 = 556561) (by norm_num)
theorem B1978883 : Blo 1977435 1978883 := bstep (se 1 (by rfl) ⟨1484162, by rfl⟩ : syracuseStep 1978883 = 2968325) B2968325
theorem B3339373 : Blo 1977435 3339373 := bbase (se 3 (by rfl) ⟨626132, by rfl⟩ : syracuseStep 3339373 = 1252265) (by norm_num)
theorem B4452497 : Blo 1977435 4452497 := bstep (se 2 (by rfl) ⟨1669686, by rfl⟩ : syracuseStep 4452497 = 3339373) B3339373
theorem B2968331 : Blo 1977435 2968331 := bstep (se 1 (by rfl) ⟨2226248, by rfl⟩ : syracuseStep 2968331 = 4452497) B4452497
theorem B1978887 : Blo 1977435 1978887 := bstep (se 1 (by rfl) ⟨1484165, by rfl⟩ : syracuseStep 1978887 = 2968331) B2968331
theorem B2226253 : Blo 1977435 2226253 := bbase (se 3 (by rfl) ⟨417422, by rfl⟩ : syracuseStep 2226253 = 834845) (by norm_num)
theorem B2968337 : Blo 1977435 2968337 := bstep (se 2 (by rfl) ⟨1113126, by rfl⟩ : syracuseStep 2968337 = 2226253) B2226253
theorem B1978891 : Blo 1977435 1978891 := bstep (se 1 (by rfl) ⟨1484168, by rfl⟩ : syracuseStep 1978891 = 2968337) B2968337
theorem B6678773 : Blo 1977435 6678773 := bbase (se 5 (by rfl) ⟨313067, by rfl⟩ : syracuseStep 6678773 = 626135) (by norm_num)
theorem B4452515 : Blo 1977435 4452515 := bstep (se 1 (by rfl) ⟨3339386, by rfl⟩ : syracuseStep 4452515 = 6678773) B6678773
theorem B2968343 : Blo 1977435 2968343 := bstep (se 1 (by rfl) ⟨2226257, by rfl⟩ : syracuseStep 2968343 = 4452515) B4452515
theorem B1978895 : Blo 1977435 1978895 := bstep (se 1 (by rfl) ⟨1484171, by rfl⟩ : syracuseStep 1978895 = 2968343) B2968343
theorem B2968349 : Blo 1977435 2968349 := bbase (se 3 (by rfl) ⟨556565, by rfl⟩ : syracuseStep 2968349 = 1113131) (by norm_num)
theorem B1978899 : Blo 1977435 1978899 := bstep (se 1 (by rfl) ⟨1484174, by rfl⟩ : syracuseStep 1978899 = 2968349) B2968349
theorem B4452533 : Blo 1977435 4452533 := bbase (se 5 (by rfl) ⟨208712, by rfl⟩ : syracuseStep 4452533 = 417425) (by norm_num)
theorem B2968355 : Blo 1977435 2968355 := bstep (se 1 (by rfl) ⟨2226266, by rfl⟩ : syracuseStep 2968355 = 4452533) B4452533
theorem B1978903 : Blo 1977435 1978903 := bstep (se 1 (by rfl) ⟨1484177, by rfl⟩ : syracuseStep 1978903 = 2968355) B2968355
theorem B3169829 : Blo 1977435 3169829 := bbase (se 4 (by rfl) ⟨297171, by rfl⟩ : syracuseStep 3169829 = 594343) (by norm_num)
theorem B2113219 : Blo 1977435 2113219 := bstep (se 1 (by rfl) ⟨1584914, by rfl⟩ : syracuseStep 2113219 = 3169829) B3169829
theorem B11270501 : Blo 1977435 11270501 := bstep (se 4 (by rfl) ⟨1056609, by rfl⟩ : syracuseStep 11270501 = 2113219) B2113219
theorem B7513667 : Blo 1977435 7513667 := bstep (se 1 (by rfl) ⟨5635250, by rfl⟩ : syracuseStep 7513667 = 11270501) B11270501
theorem B5009111 : Blo 1977435 5009111 := bstep (se 1 (by rfl) ⟨3756833, by rfl⟩ : syracuseStep 5009111 = 7513667) B7513667
theorem B3339407 : Blo 1977435 3339407 := bstep (se 1 (by rfl) ⟨2504555, by rfl⟩ : syracuseStep 3339407 = 5009111) B5009111
theorem B2226271 : Blo 1977435 2226271 := bstep (se 1 (by rfl) ⟨1669703, by rfl⟩ : syracuseStep 2226271 = 3339407) B3339407
theorem B2968361 : Blo 1977435 2968361 := bstep (se 2 (by rfl) ⟨1113135, by rfl⟩ : syracuseStep 2968361 = 2226271) B2226271
theorem B1978907 : Blo 1977435 1978907 := bstep (se 1 (by rfl) ⟨1484180, by rfl⟩ : syracuseStep 1978907 = 2968361) B2968361
theorem B2674549 : Blo 1977435 2674549 := bbase (se 5 (by rfl) ⟨125369, by rfl⟩ : syracuseStep 2674549 = 250739) (by norm_num)
theorem B3566065 : Blo 1977435 3566065 := bstep (se 2 (by rfl) ⟨1337274, by rfl⟩ : syracuseStep 3566065 = 2674549) B2674549
theorem B4754753 : Blo 1977435 4754753 := bstep (se 2 (by rfl) ⟨1783032, by rfl⟩ : syracuseStep 4754753 = 3566065) B3566065
theorem B3169835 : Blo 1977435 3169835 := bstep (se 1 (by rfl) ⟨2377376, by rfl⟩ : syracuseStep 3169835 = 4754753) B4754753
theorem B2113223 : Blo 1977435 2113223 := bstep (se 1 (by rfl) ⟨1584917, by rfl⟩ : syracuseStep 2113223 = 3169835) B3169835
theorem B5635261 : Blo 1977435 5635261 := bstep (se 3 (by rfl) ⟨1056611, by rfl⟩ : syracuseStep 5635261 = 2113223) B2113223
theorem B7513681 : Blo 1977435 7513681 := bstep (se 2 (by rfl) ⟨2817630, by rfl⟩ : syracuseStep 7513681 = 5635261) B5635261
theorem B10018241 : Blo 1977435 10018241 := bstep (se 2 (by rfl) ⟨3756840, by rfl⟩ : syracuseStep 10018241 = 7513681) B7513681
theorem B6678827 : Blo 1977435 6678827 := bstep (se 1 (by rfl) ⟨5009120, by rfl⟩ : syracuseStep 6678827 = 10018241) B10018241
theorem B4452551 : Blo 1977435 4452551 := bstep (se 1 (by rfl) ⟨3339413, by rfl⟩ : syracuseStep 4452551 = 6678827) B6678827
theorem B2968367 : Blo 1977435 2968367 := bstep (se 1 (by rfl) ⟨2226275, by rfl⟩ : syracuseStep 2968367 = 4452551) B4452551
theorem B1978911 : Blo 1977435 1978911 := bstep (se 1 (by rfl) ⟨1484183, by rfl⟩ : syracuseStep 1978911 = 2968367) B2968367
theorem B2968373 : Blo 1977435 2968373 := bbase (se 5 (by rfl) ⟨139142, by rfl⟩ : syracuseStep 2968373 = 278285) (by norm_num)
theorem B1978915 : Blo 1977435 1978915 := bstep (se 1 (by rfl) ⟨1484186, by rfl⟩ : syracuseStep 1978915 = 2968373) B2968373
theorem B5009141 : Blo 1977435 5009141 := bbase (se 5 (by rfl) ⟨234803, by rfl⟩ : syracuseStep 5009141 = 469607) (by norm_num)
theorem B3339427 : Blo 1977435 3339427 := bstep (se 1 (by rfl) ⟨2504570, by rfl⟩ : syracuseStep 3339427 = 5009141) B5009141
theorem B4452569 : Blo 1977435 4452569 := bstep (se 2 (by rfl) ⟨1669713, by rfl⟩ : syracuseStep 4452569 = 3339427) B3339427
theorem B2968379 : Blo 1977435 2968379 := bstep (se 1 (by rfl) ⟨2226284, by rfl⟩ : syracuseStep 2968379 = 4452569) B4452569
theorem B1978919 : Blo 1977435 1978919 := bstep (se 1 (by rfl) ⟨1484189, by rfl⟩ : syracuseStep 1978919 = 2968379) B2968379
theorem B2226289 : Blo 1977435 2226289 := bbase (se 2 (by rfl) ⟨834858, by rfl⟩ : syracuseStep 2226289 = 1669717) (by norm_num)
theorem B2968385 : Blo 1977435 2968385 := bstep (se 2 (by rfl) ⟨1113144, by rfl⟩ : syracuseStep 2968385 = 2226289) B2226289
theorem B1978923 : Blo 1977435 1978923 := bstep (se 1 (by rfl) ⟨1484192, by rfl⟩ : syracuseStep 1978923 = 2968385) B2968385
theorem B15440341 : Blo 1977435 15440341 := bbase (se 7 (by rfl) ⟨180941, by rfl⟩ : syracuseStep 15440341 = 361883) (by norm_num)
theorem B20587121 : Blo 1977435 20587121 := bstep (se 2 (by rfl) ⟨7720170, by rfl⟩ : syracuseStep 20587121 = 15440341) B15440341
theorem B13724747 : Blo 1977435 13724747 := bstep (se 1 (by rfl) ⟨10293560, by rfl⟩ : syracuseStep 13724747 = 20587121) B20587121
theorem B9149831 : Blo 1977435 9149831 := bstep (se 1 (by rfl) ⟨6862373, by rfl⟩ : syracuseStep 9149831 = 13724747) B13724747
theorem B6099887 : Blo 1977435 6099887 := bstep (se 1 (by rfl) ⟨4574915, by rfl⟩ : syracuseStep 6099887 = 9149831) B9149831
theorem B16266365 : Blo 1977435 16266365 := bstep (se 3 (by rfl) ⟨3049943, by rfl⟩ : syracuseStep 16266365 = 6099887) B6099887
theorem B10844243 : Blo 1977435 10844243 := bstep (se 1 (by rfl) ⟨8133182, by rfl⟩ : syracuseStep 10844243 = 16266365) B16266365
theorem B7229495 : Blo 1977435 7229495 := bstep (se 1 (by rfl) ⟨5422121, by rfl⟩ : syracuseStep 7229495 = 10844243) B10844243
theorem B19278653 : Blo 1977435 19278653 := bstep (se 3 (by rfl) ⟨3614747, by rfl⟩ : syracuseStep 19278653 = 7229495) B7229495
theorem B51409741 : Blo 1977435 51409741 := bstep (se 3 (by rfl) ⟨9639326, by rfl⟩ : syracuseStep 51409741 = 19278653) B19278653
theorem B68546321 : Blo 1977435 68546321 := bstep (se 2 (by rfl) ⟨25704870, by rfl⟩ : syracuseStep 68546321 = 51409741) B51409741
theorem B45697547 : Blo 1977435 45697547 := bstep (se 1 (by rfl) ⟨34273160, by rfl⟩ : syracuseStep 45697547 = 68546321) B68546321
theorem B30465031 : Blo 1977435 30465031 := bstep (se 1 (by rfl) ⟨22848773, by rfl⟩ : syracuseStep 30465031 = 45697547) B45697547
theorem B40620041 : Blo 1977435 40620041 := bstep (se 2 (by rfl) ⟨15232515, by rfl⟩ : syracuseStep 40620041 = 30465031) B30465031
theorem B27080027 : Blo 1977435 27080027 := bstep (se 1 (by rfl) ⟨20310020, by rfl⟩ : syracuseStep 27080027 = 40620041) B40620041
theorem B18053351 : Blo 1977435 18053351 := bstep (se 1 (by rfl) ⟨13540013, by rfl⟩ : syracuseStep 18053351 = 27080027) B27080027
theorem B12035567 : Blo 1977435 12035567 := bstep (se 1 (by rfl) ⟨9026675, by rfl⟩ : syracuseStep 12035567 = 18053351) B18053351
theorem B8023711 : Blo 1977435 8023711 := bstep (se 1 (by rfl) ⟨6017783, by rfl⟩ : syracuseStep 8023711 = 12035567) B12035567
theorem B10698281 : Blo 1977435 10698281 := bstep (se 2 (by rfl) ⟨4011855, by rfl⟩ : syracuseStep 10698281 = 8023711) B8023711
theorem B7132187 : Blo 1977435 7132187 := bstep (se 1 (by rfl) ⟨5349140, by rfl⟩ : syracuseStep 7132187 = 10698281) B10698281
theorem B4754791 : Blo 1977435 4754791 := bstep (se 1 (by rfl) ⟨3566093, by rfl⟩ : syracuseStep 4754791 = 7132187) B7132187
theorem B6339721 : Blo 1977435 6339721 := bstep (se 2 (by rfl) ⟨2377395, by rfl⟩ : syracuseStep 6339721 = 4754791) B4754791
theorem B8452961 : Blo 1977435 8452961 := bstep (se 2 (by rfl) ⟨3169860, by rfl⟩ : syracuseStep 8452961 = 6339721) B6339721
theorem B5635307 : Blo 1977435 5635307 := bstep (se 1 (by rfl) ⟨4226480, by rfl⟩ : syracuseStep 5635307 = 8452961) B8452961
theorem B3756871 : Blo 1977435 3756871 := bstep (se 1 (by rfl) ⟨2817653, by rfl⟩ : syracuseStep 3756871 = 5635307) B5635307
theorem B5009161 : Blo 1977435 5009161 := bstep (se 2 (by rfl) ⟨1878435, by rfl⟩ : syracuseStep 5009161 = 3756871) B3756871
theorem B6678881 : Blo 1977435 6678881 := bstep (se 2 (by rfl) ⟨2504580, by rfl⟩ : syracuseStep 6678881 = 5009161) B5009161
theorem B4452587 : Blo 1977435 4452587 := bstep (se 1 (by rfl) ⟨3339440, by rfl⟩ : syracuseStep 4452587 = 6678881) B6678881
theorem B2968391 : Blo 1977435 2968391 := bstep (se 1 (by rfl) ⟨2226293, by rfl⟩ : syracuseStep 2968391 = 4452587) B4452587
theorem B1978927 : Blo 1977435 1978927 := bstep (se 1 (by rfl) ⟨1484195, by rfl⟩ : syracuseStep 1978927 = 2968391) B2968391
theorem B2968397 : Blo 1977435 2968397 := bbase (se 3 (by rfl) ⟨556574, by rfl⟩ : syracuseStep 2968397 = 1113149) (by norm_num)
theorem B1978931 : Blo 1977435 1978931 := bstep (se 1 (by rfl) ⟨1484198, by rfl⟩ : syracuseStep 1978931 = 2968397) B2968397
theorem B4452605 : Blo 1977435 4452605 := bbase (se 3 (by rfl) ⟨834863, by rfl⟩ : syracuseStep 4452605 = 1669727) (by norm_num)
theorem B2968403 : Blo 1977435 2968403 := bstep (se 1 (by rfl) ⟨2226302, by rfl⟩ : syracuseStep 2968403 = 4452605) B4452605
theorem B1978935 : Blo 1977435 1978935 := bstep (se 1 (by rfl) ⟨1484201, by rfl⟩ : syracuseStep 1978935 = 2968403) B2968403
theorem B3339461 : Blo 1977435 3339461 := bbase (se 4 (by rfl) ⟨313074, by rfl⟩ : syracuseStep 3339461 = 626149) (by norm_num)
theorem B2226307 : Blo 1977435 2226307 := bstep (se 1 (by rfl) ⟨1669730, by rfl⟩ : syracuseStep 2226307 = 3339461) B3339461
theorem B2968409 : Blo 1977435 2968409 := bstep (se 2 (by rfl) ⟨1113153, by rfl⟩ : syracuseStep 2968409 = 2226307) B2226307
theorem B1978939 : Blo 1977435 1978939 := bstep (se 1 (by rfl) ⟨1484204, by rfl⟩ : syracuseStep 1978939 = 2968409) B2968409
theorem B15027605 : Blo 1977435 15027605 := bbase (se 6 (by rfl) ⟨352209, by rfl⟩ : syracuseStep 15027605 = 704419) (by norm_num)
theorem B10018403 : Blo 1977435 10018403 := bstep (se 1 (by rfl) ⟨7513802, by rfl⟩ : syracuseStep 10018403 = 15027605) B15027605
theorem B6678935 : Blo 1977435 6678935 := bstep (se 1 (by rfl) ⟨5009201, by rfl⟩ : syracuseStep 6678935 = 10018403) B10018403
theorem B4452623 : Blo 1977435 4452623 := bstep (se 1 (by rfl) ⟨3339467, by rfl⟩ : syracuseStep 4452623 = 6678935) B6678935
theorem B2968415 : Blo 1977435 2968415 := bstep (se 1 (by rfl) ⟨2226311, by rfl⟩ : syracuseStep 2968415 = 4452623) B4452623
theorem B1978943 : Blo 1977435 1978943 := bstep (se 1 (by rfl) ⟨1484207, by rfl⟩ : syracuseStep 1978943 = 2968415) B2968415
theorem B2968421 : Blo 1977435 2968421 := bbase (se 4 (by rfl) ⟨278289, by rfl⟩ : syracuseStep 2968421 = 556579) (by norm_num)
theorem B1978947 : Blo 1977435 1978947 := bstep (se 1 (by rfl) ⟨1484210, by rfl⟩ : syracuseStep 1978947 = 2968421) B2968421
theorem B3756917 : Blo 1977435 3756917 := bbase (se 5 (by rfl) ⟨176105, by rfl⟩ : syracuseStep 3756917 = 352211) (by norm_num)
theorem B2504611 : Blo 1977435 2504611 := bstep (se 1 (by rfl) ⟨1878458, by rfl⟩ : syracuseStep 2504611 = 3756917) B3756917
theorem B3339481 : Blo 1977435 3339481 := bstep (se 2 (by rfl) ⟨1252305, by rfl⟩ : syracuseStep 3339481 = 2504611) B2504611
theorem B4452641 : Blo 1977435 4452641 := bstep (se 2 (by rfl) ⟨1669740, by rfl⟩ : syracuseStep 4452641 = 3339481) B3339481
theorem B2968427 : Blo 1977435 2968427 := bstep (se 1 (by rfl) ⟨2226320, by rfl⟩ : syracuseStep 2968427 = 4452641) B4452641
theorem B1978951 : Blo 1977435 1978951 := bstep (se 1 (by rfl) ⟨1484213, by rfl⟩ : syracuseStep 1978951 = 2968427) B2968427
theorem B2226325 : Blo 1977435 2226325 := bbase (se 6 (by rfl) ⟨52179, by rfl⟩ : syracuseStep 2226325 = 104359) (by norm_num)
theorem B2968433 : Blo 1977435 2968433 := bstep (se 2 (by rfl) ⟨1113162, by rfl⟩ : syracuseStep 2968433 = 2226325) B2226325
theorem B1978955 : Blo 1977435 1978955 := bstep (se 1 (by rfl) ⟨1484216, by rfl⟩ : syracuseStep 1978955 = 2968433) B2968433
theorem B2504621 : Blo 1977435 2504621 := bbase (se 3 (by rfl) ⟨469616, by rfl⟩ : syracuseStep 2504621 = 939233) (by norm_num)
theorem B6678989 : Blo 1977435 6678989 := bstep (se 3 (by rfl) ⟨1252310, by rfl⟩ : syracuseStep 6678989 = 2504621) B2504621
theorem B4452659 : Blo 1977435 4452659 := bstep (se 1 (by rfl) ⟨3339494, by rfl⟩ : syracuseStep 4452659 = 6678989) B6678989
theorem B2968439 : Blo 1977435 2968439 := bstep (se 1 (by rfl) ⟨2226329, by rfl⟩ : syracuseStep 2968439 = 4452659) B4452659
theorem B1978959 : Blo 1977435 1978959 := bstep (se 1 (by rfl) ⟨1484219, by rfl⟩ : syracuseStep 1978959 = 2968439) B2968439
theorem B2968445 : Blo 1977435 2968445 := bbase (se 3 (by rfl) ⟨556583, by rfl⟩ : syracuseStep 2968445 = 1113167) (by norm_num)
theorem B1978963 : Blo 1977435 1978963 := bstep (se 1 (by rfl) ⟨1484222, by rfl⟩ : syracuseStep 1978963 = 2968445) B2968445
theorem B4452677 : Blo 1977435 4452677 := bbase (se 4 (by rfl) ⟨417438, by rfl⟩ : syracuseStep 4452677 = 834877) (by norm_num)
theorem B2968451 : Blo 1977435 2968451 := bstep (se 1 (by rfl) ⟨2226338, by rfl⟩ : syracuseStep 2968451 = 4452677) B4452677
theorem B1978967 : Blo 1977435 1978967 := bstep (se 1 (by rfl) ⟨1484225, by rfl⟩ : syracuseStep 1978967 = 2968451) B2968451
theorem B14264693 : Blo 1977435 14264693 := bbase (se 5 (by rfl) ⟨668657, by rfl⟩ : syracuseStep 14264693 = 1337315) (by norm_num)
theorem B9509795 : Blo 1977435 9509795 := bstep (se 1 (by rfl) ⟨7132346, by rfl⟩ : syracuseStep 9509795 = 14264693) B14264693
theorem B6339863 : Blo 1977435 6339863 := bstep (se 1 (by rfl) ⟨4754897, by rfl⟩ : syracuseStep 6339863 = 9509795) B9509795
theorem B4226575 : Blo 1977435 4226575 := bstep (se 1 (by rfl) ⟨3169931, by rfl⟩ : syracuseStep 4226575 = 6339863) B6339863
theorem B5635433 : Blo 1977435 5635433 := bstep (se 2 (by rfl) ⟨2113287, by rfl⟩ : syracuseStep 5635433 = 4226575) B4226575
theorem B3756955 : Blo 1977435 3756955 := bstep (se 1 (by rfl) ⟨2817716, by rfl⟩ : syracuseStep 3756955 = 5635433) B5635433
theorem B5009273 : Blo 1977435 5009273 := bstep (se 2 (by rfl) ⟨1878477, by rfl⟩ : syracuseStep 5009273 = 3756955) B3756955
theorem B3339515 : Blo 1977435 3339515 := bstep (se 1 (by rfl) ⟨2504636, by rfl⟩ : syracuseStep 3339515 = 5009273) B5009273
theorem B2226343 : Blo 1977435 2226343 := bstep (se 1 (by rfl) ⟨1669757, by rfl⟩ : syracuseStep 2226343 = 3339515) B3339515
theorem B2968457 : Blo 1977435 2968457 := bstep (se 2 (by rfl) ⟨1113171, by rfl⟩ : syracuseStep 2968457 = 2226343) B2226343
theorem B1978971 : Blo 1977435 1978971 := bstep (se 1 (by rfl) ⟨1484228, by rfl⟩ : syracuseStep 1978971 = 2968457) B2968457
theorem B10018565 : Blo 1977435 10018565 := bbase (se 4 (by rfl) ⟨939240, by rfl⟩ : syracuseStep 10018565 = 1878481) (by norm_num)
theorem B6679043 : Blo 1977435 6679043 := bstep (se 1 (by rfl) ⟨5009282, by rfl⟩ : syracuseStep 6679043 = 10018565) B10018565
theorem B4452695 : Blo 1977435 4452695 := bstep (se 1 (by rfl) ⟨3339521, by rfl⟩ : syracuseStep 4452695 = 6679043) B6679043
theorem B2968463 : Blo 1977435 2968463 := bstep (se 1 (by rfl) ⟨2226347, by rfl⟩ : syracuseStep 2968463 = 4452695) B4452695
theorem B1978975 : Blo 1977435 1978975 := bstep (se 1 (by rfl) ⟨1484231, by rfl⟩ : syracuseStep 1978975 = 2968463) B2968463
theorem B2968469 : Blo 1977435 2968469 := bbase (se 6 (by rfl) ⟨69573, by rfl⟩ : syracuseStep 2968469 = 139147) (by norm_num)
theorem B1978979 : Blo 1977435 1978979 := bstep (se 1 (by rfl) ⟨1484234, by rfl⟩ : syracuseStep 1978979 = 2968469) B2968469
theorem B11270933 : Blo 1977435 11270933 := bbase (se 6 (by rfl) ⟨264162, by rfl⟩ : syracuseStep 11270933 = 528325) (by norm_num)
theorem B7513955 : Blo 1977435 7513955 := bstep (se 1 (by rfl) ⟨5635466, by rfl⟩ : syracuseStep 7513955 = 11270933) B11270933
theorem B5009303 : Blo 1977435 5009303 := bstep (se 1 (by rfl) ⟨3756977, by rfl⟩ : syracuseStep 5009303 = 7513955) B7513955
theorem B3339535 : Blo 1977435 3339535 := bstep (se 1 (by rfl) ⟨2504651, by rfl⟩ : syracuseStep 3339535 = 5009303) B5009303
theorem B4452713 : Blo 1977435 4452713 := bstep (se 2 (by rfl) ⟨1669767, by rfl⟩ : syracuseStep 4452713 = 3339535) B3339535
theorem B2968475 : Blo 1977435 2968475 := bstep (se 1 (by rfl) ⟨2226356, by rfl⟩ : syracuseStep 2968475 = 4452713) B4452713
theorem B1978983 : Blo 1977435 1978983 := bstep (se 1 (by rfl) ⟨1484237, by rfl⟩ : syracuseStep 1978983 = 2968475) B2968475
theorem B2226361 : Blo 1977435 2226361 := bbase (se 2 (by rfl) ⟨834885, by rfl⟩ : syracuseStep 2226361 = 1669771) (by norm_num)
theorem B2968481 : Blo 1977435 2968481 := bstep (se 2 (by rfl) ⟨1113180, by rfl⟩ : syracuseStep 2968481 = 2226361) B2226361
theorem B1978987 : Blo 1977435 1978987 := bstep (se 1 (by rfl) ⟨1484240, by rfl⟩ : syracuseStep 1978987 = 2968481) B2968481
theorem B2005993 : Blo 1977435 2005993 := bbase (se 2 (by rfl) ⟨752247, by rfl⟩ : syracuseStep 2005993 = 1504495) (by norm_num)
theorem B2674657 : Blo 1977435 2674657 := bstep (se 2 (by rfl) ⟨1002996, by rfl⟩ : syracuseStep 2674657 = 2005993) B2005993
theorem B3566209 : Blo 1977435 3566209 := bstep (se 2 (by rfl) ⟨1337328, by rfl⟩ : syracuseStep 3566209 = 2674657) B2674657
theorem B4754945 : Blo 1977435 4754945 := bstep (se 2 (by rfl) ⟨1783104, by rfl⟩ : syracuseStep 4754945 = 3566209) B3566209
theorem B3169963 : Blo 1977435 3169963 := bstep (se 1 (by rfl) ⟨2377472, by rfl⟩ : syracuseStep 3169963 = 4754945) B4754945
theorem B4226617 : Blo 1977435 4226617 := bstep (se 2 (by rfl) ⟨1584981, by rfl⟩ : syracuseStep 4226617 = 3169963) B3169963
theorem B5635489 : Blo 1977435 5635489 := bstep (se 2 (by rfl) ⟨2113308, by rfl⟩ : syracuseStep 5635489 = 4226617) B4226617
theorem B7513985 : Blo 1977435 7513985 := bstep (se 2 (by rfl) ⟨2817744, by rfl⟩ : syracuseStep 7513985 = 5635489) B5635489
theorem B5009323 : Blo 1977435 5009323 := bstep (se 1 (by rfl) ⟨3756992, by rfl⟩ : syracuseStep 5009323 = 7513985) B7513985
theorem B6679097 : Blo 1977435 6679097 := bstep (se 2 (by rfl) ⟨2504661, by rfl⟩ : syracuseStep 6679097 = 5009323) B5009323
theorem B4452731 : Blo 1977435 4452731 := bstep (se 1 (by rfl) ⟨3339548, by rfl⟩ : syracuseStep 4452731 = 6679097) B6679097
theorem B2968487 : Blo 1977435 2968487 := bstep (se 1 (by rfl) ⟨2226365, by rfl⟩ : syracuseStep 2968487 = 4452731) B4452731
theorem B1978991 : Blo 1977435 1978991 := bstep (se 1 (by rfl) ⟨1484243, by rfl⟩ : syracuseStep 1978991 = 2968487) B2968487
theorem B2968493 : Blo 1977435 2968493 := bbase (se 3 (by rfl) ⟨556592, by rfl⟩ : syracuseStep 2968493 = 1113185) (by norm_num)
theorem B1978995 : Blo 1977435 1978995 := bstep (se 1 (by rfl) ⟨1484246, by rfl⟩ : syracuseStep 1978995 = 2968493) B2968493
theorem B4452749 : Blo 1977435 4452749 := bbase (se 3 (by rfl) ⟨834890, by rfl⟩ : syracuseStep 4452749 = 1669781) (by norm_num)
theorem B2968499 : Blo 1977435 2968499 := bstep (se 1 (by rfl) ⟨2226374, by rfl⟩ : syracuseStep 2968499 = 4452749) B4452749
theorem B1978999 : Blo 1977435 1978999 := bstep (se 1 (by rfl) ⟨1484249, by rfl⟩ : syracuseStep 1978999 = 2968499) B2968499
theorem B2504677 : Blo 1977435 2504677 := bbase (se 4 (by rfl) ⟨234813, by rfl⟩ : syracuseStep 2504677 = 469627) (by norm_num)
theorem B3339569 : Blo 1977435 3339569 := bstep (se 2 (by rfl) ⟨1252338, by rfl⟩ : syracuseStep 3339569 = 2504677) B2504677
theorem B2226379 : Blo 1977435 2226379 := bstep (se 1 (by rfl) ⟨1669784, by rfl⟩ : syracuseStep 2226379 = 3339569) B3339569
theorem B2968505 : Blo 1977435 2968505 := bstep (se 2 (by rfl) ⟨1113189, by rfl⟩ : syracuseStep 2968505 = 2226379) B2226379
theorem B1979003 : Blo 1977435 1979003 := bstep (se 1 (by rfl) ⟨1484252, by rfl⟩ : syracuseStep 1979003 = 2968505) B2968505
theorem B14459573 : Blo 1977435 14459573 := bbase (se 5 (by rfl) ⟨677792, by rfl⟩ : syracuseStep 14459573 = 1355585) (by norm_num)
theorem B38558861 : Blo 1977435 38558861 := bstep (se 3 (by rfl) ⟨7229786, by rfl⟩ : syracuseStep 38558861 = 14459573) B14459573
theorem B25705907 : Blo 1977435 25705907 := bstep (se 1 (by rfl) ⟨19279430, by rfl⟩ : syracuseStep 25705907 = 38558861) B38558861
theorem B17137271 : Blo 1977435 17137271 := bstep (se 1 (by rfl) ⟨12852953, by rfl⟩ : syracuseStep 17137271 = 25705907) B25705907
theorem B11424847 : Blo 1977435 11424847 := bstep (se 1 (by rfl) ⟨8568635, by rfl⟩ : syracuseStep 11424847 = 17137271) B17137271
theorem B15233129 : Blo 1977435 15233129 := bstep (se 2 (by rfl) ⟨5712423, by rfl⟩ : syracuseStep 15233129 = 11424847) B11424847
theorem B10155419 : Blo 1977435 10155419 := bstep (se 1 (by rfl) ⟨7616564, by rfl⟩ : syracuseStep 10155419 = 15233129) B15233129
theorem B6770279 : Blo 1977435 6770279 := bstep (se 1 (by rfl) ⟨5077709, by rfl⟩ : syracuseStep 6770279 = 10155419) B10155419
theorem B4513519 : Blo 1977435 4513519 := bstep (se 1 (by rfl) ⟨3385139, by rfl⟩ : syracuseStep 4513519 = 6770279) B6770279
theorem B6018025 : Blo 1977435 6018025 := bstep (se 2 (by rfl) ⟨2256759, by rfl⟩ : syracuseStep 6018025 = 4513519) B4513519
theorem B8024033 : Blo 1977435 8024033 := bstep (se 2 (by rfl) ⟨3009012, by rfl⟩ : syracuseStep 8024033 = 6018025) B6018025
theorem B21397421 : Blo 1977435 21397421 := bstep (se 3 (by rfl) ⟨4012016, by rfl⟩ : syracuseStep 21397421 = 8024033) B8024033
theorem B14264947 : Blo 1977435 14264947 := bstep (se 1 (by rfl) ⟨10698710, by rfl⟩ : syracuseStep 14264947 = 21397421) B21397421
theorem B19019929 : Blo 1977435 19019929 := bstep (se 2 (by rfl) ⟨7132473, by rfl⟩ : syracuseStep 19019929 = 14264947) B14264947
theorem B25359905 : Blo 1977435 25359905 := bstep (se 2 (by rfl) ⟨9509964, by rfl⟩ : syracuseStep 25359905 = 19019929) B19019929
theorem B16906603 : Blo 1977435 16906603 := bstep (se 1 (by rfl) ⟨12679952, by rfl⟩ : syracuseStep 16906603 = 25359905) B25359905
theorem B22542137 : Blo 1977435 22542137 := bstep (se 2 (by rfl) ⟨8453301, by rfl⟩ : syracuseStep 22542137 = 16906603) B16906603
theorem B15028091 : Blo 1977435 15028091 := bstep (se 1 (by rfl) ⟨11271068, by rfl⟩ : syracuseStep 15028091 = 22542137) B22542137
theorem B10018727 : Blo 1977435 10018727 := bstep (se 1 (by rfl) ⟨7514045, by rfl⟩ : syracuseStep 10018727 = 15028091) B15028091
theorem B6679151 : Blo 1977435 6679151 := bstep (se 1 (by rfl) ⟨5009363, by rfl⟩ : syracuseStep 6679151 = 10018727) B10018727
theorem B4452767 : Blo 1977435 4452767 := bstep (se 1 (by rfl) ⟨3339575, by rfl⟩ : syracuseStep 4452767 = 6679151) B6679151
theorem B2968511 : Blo 1977435 2968511 := bstep (se 1 (by rfl) ⟨2226383, by rfl⟩ : syracuseStep 2968511 = 4452767) B4452767
theorem B1979007 : Blo 1977435 1979007 := bstep (se 1 (by rfl) ⟨1484255, by rfl⟩ : syracuseStep 1979007 = 2968511) B2968511
theorem B2968517 : Blo 1977435 2968517 := bbase (se 4 (by rfl) ⟨278298, by rfl⟩ : syracuseStep 2968517 = 556597) (by norm_num)
theorem B1979011 : Blo 1977435 1979011 := bstep (se 1 (by rfl) ⟨1484258, by rfl⟩ : syracuseStep 1979011 = 2968517) B2968517
theorem B3339589 : Blo 1977435 3339589 := bbase (se 4 (by rfl) ⟨313086, by rfl⟩ : syracuseStep 3339589 = 626173) (by norm_num)
theorem B4452785 : Blo 1977435 4452785 := bstep (se 2 (by rfl) ⟨1669794, by rfl⟩ : syracuseStep 4452785 = 3339589) B3339589
theorem B2968523 : Blo 1977435 2968523 := bstep (se 1 (by rfl) ⟨2226392, by rfl⟩ : syracuseStep 2968523 = 4452785) B4452785
theorem B1979015 : Blo 1977435 1979015 := bstep (se 1 (by rfl) ⟨1484261, by rfl⟩ : syracuseStep 1979015 = 2968523) B2968523
theorem B2226397 : Blo 1977435 2226397 := bbase (se 3 (by rfl) ⟨417449, by rfl⟩ : syracuseStep 2226397 = 834899) (by norm_num)
theorem B2968529 : Blo 1977435 2968529 := bstep (se 2 (by rfl) ⟨1113198, by rfl⟩ : syracuseStep 2968529 = 2226397) B2226397
theorem B1979019 : Blo 1977435 1979019 := bstep (se 1 (by rfl) ⟨1484264, by rfl⟩ : syracuseStep 1979019 = 2968529) B2968529
theorem B6679205 : Blo 1977435 6679205 := bbase (se 4 (by rfl) ⟨626175, by rfl⟩ : syracuseStep 6679205 = 1252351) (by norm_num)
theorem B4452803 : Blo 1977435 4452803 := bstep (se 1 (by rfl) ⟨3339602, by rfl⟩ : syracuseStep 4452803 = 6679205) B6679205
theorem B2968535 : Blo 1977435 2968535 := bstep (se 1 (by rfl) ⟨2226401, by rfl⟩ : syracuseStep 2968535 = 4452803) B4452803
theorem B1979023 : Blo 1977435 1979023 := bstep (se 1 (by rfl) ⟨1484267, by rfl⟩ : syracuseStep 1979023 = 2968535) B2968535
theorem B2968541 : Blo 1977435 2968541 := bbase (se 3 (by rfl) ⟨556601, by rfl⟩ : syracuseStep 2968541 = 1113203) (by norm_num)
theorem B1979027 : Blo 1977435 1979027 := bstep (se 1 (by rfl) ⟨1484270, by rfl⟩ : syracuseStep 1979027 = 2968541) B2968541
theorem B4452821 : Blo 1977435 4452821 := bbase (se 7 (by rfl) ⟨52181, by rfl⟩ : syracuseStep 4452821 = 104363) (by norm_num)
theorem B2968547 : Blo 1977435 2968547 := bstep (se 1 (by rfl) ⟨2226410, by rfl⟩ : syracuseStep 2968547 = 4452821) B4452821
theorem B1979031 : Blo 1977435 1979031 := bstep (se 1 (by rfl) ⟨1484273, by rfl⟩ : syracuseStep 1979031 = 2968547) B2968547
theorem B7825925 : Blo 1977435 7825925 := bbase (se 4 (by rfl) ⟨733680, by rfl⟩ : syracuseStep 7825925 = 1467361) (by norm_num)
theorem B5217283 : Blo 1977435 5217283 := bstep (se 1 (by rfl) ⟨3912962, by rfl⟩ : syracuseStep 5217283 = 7825925) B7825925
theorem B27825509 : Blo 1977435 27825509 := bstep (se 4 (by rfl) ⟨2608641, by rfl⟩ : syracuseStep 27825509 = 5217283) B5217283
theorem B18550339 : Blo 1977435 18550339 := bstep (se 1 (by rfl) ⟨13912754, by rfl⟩ : syracuseStep 18550339 = 27825509) B27825509
theorem B98935141 : Blo 1977435 98935141 := bstep (se 4 (by rfl) ⟨9275169, by rfl⟩ : syracuseStep 98935141 = 18550339) B18550339
theorem B131913521 : Blo 1977435 131913521 := bstep (se 2 (by rfl) ⟨49467570, by rfl⟩ : syracuseStep 131913521 = 98935141) B98935141
theorem B87942347 : Blo 1977435 87942347 := bstep (se 1 (by rfl) ⟨65956760, by rfl⟩ : syracuseStep 87942347 = 131913521) B131913521
theorem B58628231 : Blo 1977435 58628231 := bstep (se 1 (by rfl) ⟨43971173, by rfl⟩ : syracuseStep 58628231 = 87942347) B87942347
theorem B39085487 : Blo 1977435 39085487 := bstep (se 1 (by rfl) ⟨29314115, by rfl⟩ : syracuseStep 39085487 = 58628231) B58628231
theorem B26056991 : Blo 1977435 26056991 := bstep (se 1 (by rfl) ⟨19542743, by rfl⟩ : syracuseStep 26056991 = 39085487) B39085487
theorem B69485309 : Blo 1977435 69485309 := bstep (se 3 (by rfl) ⟨13028495, by rfl⟩ : syracuseStep 69485309 = 26056991) B26056991
theorem B46323539 : Blo 1977435 46323539 := bstep (se 1 (by rfl) ⟨34742654, by rfl⟩ : syracuseStep 46323539 = 69485309) B69485309
theorem B30882359 : Blo 1977435 30882359 := bstep (se 1 (by rfl) ⟨23161769, by rfl⟩ : syracuseStep 30882359 = 46323539) B46323539
theorem B20588239 : Blo 1977435 20588239 := bstep (se 1 (by rfl) ⟨15441179, by rfl⟩ : syracuseStep 20588239 = 30882359) B30882359
theorem B27450985 : Blo 1977435 27450985 := bstep (se 2 (by rfl) ⟨10294119, by rfl⟩ : syracuseStep 27450985 = 20588239) B20588239
theorem B36601313 : Blo 1977435 36601313 := bstep (se 2 (by rfl) ⟨13725492, by rfl⟩ : syracuseStep 36601313 = 27450985) B27450985
theorem B97603501 : Blo 1977435 97603501 := bstep (se 3 (by rfl) ⟨18300656, by rfl⟩ : syracuseStep 97603501 = 36601313) B36601313
theorem B130138001 : Blo 1977435 130138001 := bstep (se 2 (by rfl) ⟨48801750, by rfl⟩ : syracuseStep 130138001 = 97603501) B97603501
theorem B86758667 : Blo 1977435 86758667 := bstep (se 1 (by rfl) ⟨65069000, by rfl⟩ : syracuseStep 86758667 = 130138001) B130138001
theorem B57839111 : Blo 1977435 57839111 := bstep (se 1 (by rfl) ⟨43379333, by rfl⟩ : syracuseStep 57839111 = 86758667) B86758667
theorem B38559407 : Blo 1977435 38559407 := bstep (se 1 (by rfl) ⟨28919555, by rfl⟩ : syracuseStep 38559407 = 57839111) B57839111
theorem B102825085 : Blo 1977435 102825085 := bstep (se 3 (by rfl) ⟨19279703, by rfl⟩ : syracuseStep 102825085 = 38559407) B38559407
theorem B137100113 : Blo 1977435 137100113 := bstep (se 2 (by rfl) ⟨51412542, by rfl⟩ : syracuseStep 137100113 = 102825085) B102825085
theorem B91400075 : Blo 1977435 91400075 := bstep (se 1 (by rfl) ⟨68550056, by rfl⟩ : syracuseStep 91400075 = 137100113) B137100113
theorem B60933383 : Blo 1977435 60933383 := bstep (se 1 (by rfl) ⟨45700037, by rfl⟩ : syracuseStep 60933383 = 91400075) B91400075
theorem B40622255 : Blo 1977435 40622255 := bstep (se 1 (by rfl) ⟨30466691, by rfl⟩ : syracuseStep 40622255 = 60933383) B60933383
theorem B27081503 : Blo 1977435 27081503 := bstep (se 1 (by rfl) ⟨20311127, by rfl⟩ : syracuseStep 27081503 = 40622255) B40622255
theorem B18054335 : Blo 1977435 18054335 := bstep (se 1 (by rfl) ⟨13540751, by rfl⟩ : syracuseStep 18054335 = 27081503) B27081503
theorem B12036223 : Blo 1977435 12036223 := bstep (se 1 (by rfl) ⟨9027167, by rfl⟩ : syracuseStep 12036223 = 18054335) B18054335
theorem B16048297 : Blo 1977435 16048297 := bstep (se 2 (by rfl) ⟨6018111, by rfl⟩ : syracuseStep 16048297 = 12036223) B12036223
theorem B21397729 : Blo 1977435 21397729 := bstep (se 2 (by rfl) ⟨8024148, by rfl⟩ : syracuseStep 21397729 = 16048297) B16048297
theorem B28530305 : Blo 1977435 28530305 := bstep (se 2 (by rfl) ⟨10698864, by rfl⟩ : syracuseStep 28530305 = 21397729) B21397729
theorem B19020203 : Blo 1977435 19020203 := bstep (se 1 (by rfl) ⟨14265152, by rfl⟩ : syracuseStep 19020203 = 28530305) B28530305
theorem B12680135 : Blo 1977435 12680135 := bstep (se 1 (by rfl) ⟨9510101, by rfl⟩ : syracuseStep 12680135 = 19020203) B19020203
theorem B8453423 : Blo 1977435 8453423 := bstep (se 1 (by rfl) ⟨6340067, by rfl⟩ : syracuseStep 8453423 = 12680135) B12680135
theorem B5635615 : Blo 1977435 5635615 := bstep (se 1 (by rfl) ⟨4226711, by rfl⟩ : syracuseStep 5635615 = 8453423) B8453423
theorem B7514153 : Blo 1977435 7514153 := bstep (se 2 (by rfl) ⟨2817807, by rfl⟩ : syracuseStep 7514153 = 5635615) B5635615
theorem B5009435 : Blo 1977435 5009435 := bstep (se 1 (by rfl) ⟨3757076, by rfl⟩ : syracuseStep 5009435 = 7514153) B7514153
theorem B3339623 : Blo 1977435 3339623 := bstep (se 1 (by rfl) ⟨2504717, by rfl⟩ : syracuseStep 3339623 = 5009435) B5009435
theorem B2226415 : Blo 1977435 2226415 := bstep (se 1 (by rfl) ⟨1669811, by rfl⟩ : syracuseStep 2226415 = 3339623) B3339623
theorem B2968553 : Blo 1977435 2968553 := bstep (se 2 (by rfl) ⟨1113207, by rfl⟩ : syracuseStep 2968553 = 2226415) B2226415
theorem B1979035 : Blo 1977435 1979035 := bstep (se 1 (by rfl) ⟨1484276, by rfl⟩ : syracuseStep 1979035 = 2968553) B2968553
theorem B2748205 : Blo 1977435 2748205 := bbase (se 3 (by rfl) ⟨515288, by rfl⟩ : syracuseStep 2748205 = 1030577) (by norm_num)
theorem B3664273 : Blo 1977435 3664273 := bstep (se 2 (by rfl) ⟨1374102, by rfl⟩ : syracuseStep 3664273 = 2748205) B2748205
theorem B4885697 : Blo 1977435 4885697 := bstep (se 2 (by rfl) ⟨1832136, by rfl⟩ : syracuseStep 4885697 = 3664273) B3664273
theorem B13028525 : Blo 1977435 13028525 := bstep (se 3 (by rfl) ⟨2442848, by rfl⟩ : syracuseStep 13028525 = 4885697) B4885697
theorem B8685683 : Blo 1977435 8685683 := bstep (se 1 (by rfl) ⟨6514262, by rfl⟩ : syracuseStep 8685683 = 13028525) B13028525
theorem B5790455 : Blo 1977435 5790455 := bstep (se 1 (by rfl) ⟨4342841, by rfl⟩ : syracuseStep 5790455 = 8685683) B8685683
theorem B3860303 : Blo 1977435 3860303 := bstep (se 1 (by rfl) ⟨2895227, by rfl⟩ : syracuseStep 3860303 = 5790455) B5790455
theorem B10294141 : Blo 1977435 10294141 := bstep (se 3 (by rfl) ⟨1930151, by rfl⟩ : syracuseStep 10294141 = 3860303) B3860303
theorem B13725521 : Blo 1977435 13725521 := bstep (se 2 (by rfl) ⟨5147070, by rfl⟩ : syracuseStep 13725521 = 10294141) B10294141
theorem B9150347 : Blo 1977435 9150347 := bstep (se 1 (by rfl) ⟨6862760, by rfl⟩ : syracuseStep 9150347 = 13725521) B13725521
theorem B24400925 : Blo 1977435 24400925 := bstep (se 3 (by rfl) ⟨4575173, by rfl⟩ : syracuseStep 24400925 = 9150347) B9150347
theorem B16267283 : Blo 1977435 16267283 := bstep (se 1 (by rfl) ⟨12200462, by rfl⟩ : syracuseStep 16267283 = 24400925) B24400925
theorem B10844855 : Blo 1977435 10844855 := bstep (se 1 (by rfl) ⟨8133641, by rfl⟩ : syracuseStep 10844855 = 16267283) B16267283
theorem B7229903 : Blo 1977435 7229903 := bstep (se 1 (by rfl) ⟨5422427, by rfl⟩ : syracuseStep 7229903 = 10844855) B10844855
theorem B19279741 : Blo 1977435 19279741 := bstep (se 3 (by rfl) ⟨3614951, by rfl⟩ : syracuseStep 19279741 = 7229903) B7229903
theorem B25706321 : Blo 1977435 25706321 := bstep (se 2 (by rfl) ⟨9639870, by rfl⟩ : syracuseStep 25706321 = 19279741) B19279741
theorem B17137547 : Blo 1977435 17137547 := bstep (se 1 (by rfl) ⟨12853160, by rfl⟩ : syracuseStep 17137547 = 25706321) B25706321
theorem B11425031 : Blo 1977435 11425031 := bstep (se 1 (by rfl) ⟨8568773, by rfl⟩ : syracuseStep 11425031 = 17137547) B17137547
theorem B7616687 : Blo 1977435 7616687 := bstep (se 1 (by rfl) ⟨5712515, by rfl⟩ : syracuseStep 7616687 = 11425031) B11425031
theorem B20311165 : Blo 1977435 20311165 := bstep (se 3 (by rfl) ⟨3808343, by rfl⟩ : syracuseStep 20311165 = 7616687) B7616687
theorem B27081553 : Blo 1977435 27081553 := bstep (se 2 (by rfl) ⟨10155582, by rfl⟩ : syracuseStep 27081553 = 20311165) B20311165
theorem B36108737 : Blo 1977435 36108737 := bstep (se 2 (by rfl) ⟨13540776, by rfl⟩ : syracuseStep 36108737 = 27081553) B27081553
theorem B24072491 : Blo 1977435 24072491 := bstep (se 1 (by rfl) ⟨18054368, by rfl⟩ : syracuseStep 24072491 = 36108737) B36108737
theorem B16048327 : Blo 1977435 16048327 := bstep (se 1 (by rfl) ⟨12036245, by rfl⟩ : syracuseStep 16048327 = 24072491) B24072491
theorem B21397769 : Blo 1977435 21397769 := bstep (se 2 (by rfl) ⟨8024163, by rfl⟩ : syracuseStep 21397769 = 16048327) B16048327
theorem B14265179 : Blo 1977435 14265179 := bstep (se 1 (by rfl) ⟨10698884, by rfl⟩ : syracuseStep 14265179 = 21397769) B21397769
theorem B9510119 : Blo 1977435 9510119 := bstep (se 1 (by rfl) ⟨7132589, by rfl⟩ : syracuseStep 9510119 = 14265179) B14265179
theorem B6340079 : Blo 1977435 6340079 := bstep (se 1 (by rfl) ⟨4755059, by rfl⟩ : syracuseStep 6340079 = 9510119) B9510119
theorem B16906877 : Blo 1977435 16906877 := bstep (se 3 (by rfl) ⟨3170039, by rfl⟩ : syracuseStep 16906877 = 6340079) B6340079
theorem B11271251 : Blo 1977435 11271251 := bstep (se 1 (by rfl) ⟨8453438, by rfl⟩ : syracuseStep 11271251 = 16906877) B16906877
theorem B7514167 : Blo 1977435 7514167 := bstep (se 1 (by rfl) ⟨5635625, by rfl⟩ : syracuseStep 7514167 = 11271251) B11271251
theorem B10018889 : Blo 1977435 10018889 := bstep (se 2 (by rfl) ⟨3757083, by rfl⟩ : syracuseStep 10018889 = 7514167) B7514167
theorem B6679259 : Blo 1977435 6679259 := bstep (se 1 (by rfl) ⟨5009444, by rfl⟩ : syracuseStep 6679259 = 10018889) B10018889
theorem B4452839 : Blo 1977435 4452839 := bstep (se 1 (by rfl) ⟨3339629, by rfl⟩ : syracuseStep 4452839 = 6679259) B6679259
theorem B2968559 : Blo 1977435 2968559 := bstep (se 1 (by rfl) ⟨2226419, by rfl⟩ : syracuseStep 2968559 = 4452839) B4452839
theorem B1979039 : Blo 1977435 1979039 := bstep (se 1 (by rfl) ⟨1484279, by rfl⟩ : syracuseStep 1979039 = 2968559) B2968559
theorem B2968565 : Blo 1977435 2968565 := bbase (se 5 (by rfl) ⟨139151, by rfl⟩ : syracuseStep 2968565 = 278303) (by norm_num)
theorem B1979043 : Blo 1977435 1979043 := bstep (se 1 (by rfl) ⟨1484282, by rfl⟩ : syracuseStep 1979043 = 2968565) B2968565
theorem B3170053 : Blo 1977435 3170053 := bbase (se 4 (by rfl) ⟨297192, by rfl⟩ : syracuseStep 3170053 = 594385) (by norm_num)
theorem B4226737 : Blo 1977435 4226737 := bstep (se 2 (by rfl) ⟨1585026, by rfl⟩ : syracuseStep 4226737 = 3170053) B3170053
theorem B5635649 : Blo 1977435 5635649 := bstep (se 2 (by rfl) ⟨2113368, by rfl⟩ : syracuseStep 5635649 = 4226737) B4226737
theorem B3757099 : Blo 1977435 3757099 := bstep (se 1 (by rfl) ⟨2817824, by rfl⟩ : syracuseStep 3757099 = 5635649) B5635649
theorem B5009465 : Blo 1977435 5009465 := bstep (se 2 (by rfl) ⟨1878549, by rfl⟩ : syracuseStep 5009465 = 3757099) B3757099
theorem B3339643 : Blo 1977435 3339643 := bstep (se 1 (by rfl) ⟨2504732, by rfl⟩ : syracuseStep 3339643 = 5009465) B5009465
theorem B4452857 : Blo 1977435 4452857 := bstep (se 2 (by rfl) ⟨1669821, by rfl⟩ : syracuseStep 4452857 = 3339643) B3339643
theorem B2968571 : Blo 1977435 2968571 := bstep (se 1 (by rfl) ⟨2226428, by rfl⟩ : syracuseStep 2968571 = 4452857) B4452857
theorem B1979047 : Blo 1977435 1979047 := bstep (se 1 (by rfl) ⟨1484285, by rfl⟩ : syracuseStep 1979047 = 2968571) B2968571
theorem B2226433 : Blo 1977435 2226433 := bbase (se 2 (by rfl) ⟨834912, by rfl⟩ : syracuseStep 2226433 = 1669825) (by norm_num)
theorem B2968577 : Blo 1977435 2968577 := bstep (se 2 (by rfl) ⟨1113216, by rfl⟩ : syracuseStep 2968577 = 2226433) B2226433
theorem B1979051 : Blo 1977435 1979051 := bstep (se 1 (by rfl) ⟨1484288, by rfl⟩ : syracuseStep 1979051 = 2968577) B2968577
theorem B5009485 : Blo 1977435 5009485 := bbase (se 3 (by rfl) ⟨939278, by rfl⟩ : syracuseStep 5009485 = 1878557) (by norm_num)
theorem B6679313 : Blo 1977435 6679313 := bstep (se 2 (by rfl) ⟨2504742, by rfl⟩ : syracuseStep 6679313 = 5009485) B5009485
theorem B4452875 : Blo 1977435 4452875 := bstep (se 1 (by rfl) ⟨3339656, by rfl⟩ : syracuseStep 4452875 = 6679313) B6679313
theorem B2968583 : Blo 1977435 2968583 := bstep (se 1 (by rfl) ⟨2226437, by rfl⟩ : syracuseStep 2968583 = 4452875) B4452875
theorem B1979055 : Blo 1977435 1979055 := bstep (se 1 (by rfl) ⟨1484291, by rfl⟩ : syracuseStep 1979055 = 2968583) B2968583
theorem B2968589 : Blo 1977435 2968589 := bbase (se 3 (by rfl) ⟨556610, by rfl⟩ : syracuseStep 2968589 = 1113221) (by norm_num)
theorem B1979059 : Blo 1977435 1979059 := bstep (se 1 (by rfl) ⟨1484294, by rfl⟩ : syracuseStep 1979059 = 2968589) B2968589
theorem B4452893 : Blo 1977435 4452893 := bbase (se 3 (by rfl) ⟨834917, by rfl⟩ : syracuseStep 4452893 = 1669835) (by norm_num)
theorem B2968595 : Blo 1977435 2968595 := bstep (se 1 (by rfl) ⟨2226446, by rfl⟩ : syracuseStep 2968595 = 4452893) B4452893
theorem B1979063 : Blo 1977435 1979063 := bstep (se 1 (by rfl) ⟨1484297, by rfl⟩ : syracuseStep 1979063 = 2968595) B2968595
theorem B3339677 : Blo 1977435 3339677 := bbase (se 3 (by rfl) ⟨626189, by rfl⟩ : syracuseStep 3339677 = 1252379) (by norm_num)
theorem B2226451 : Blo 1977435 2226451 := bstep (se 1 (by rfl) ⟨1669838, by rfl⟩ : syracuseStep 2226451 = 3339677) B3339677
theorem B2968601 : Blo 1977435 2968601 := bstep (se 2 (by rfl) ⟨1113225, by rfl⟩ : syracuseStep 2968601 = 2226451) B2226451
theorem B1979067 : Blo 1977435 1979067 := bstep (se 1 (by rfl) ⟨1484300, by rfl⟩ : syracuseStep 1979067 = 2968601) B2968601
theorem B8024293 : Blo 1977435 8024293 := bbase (se 4 (by rfl) ⟨752277, by rfl⟩ : syracuseStep 8024293 = 1504555) (by norm_num)
theorem B10699057 : Blo 1977435 10699057 := bstep (se 2 (by rfl) ⟨4012146, by rfl⟩ : syracuseStep 10699057 = 8024293) B8024293
theorem B14265409 : Blo 1977435 14265409 := bstep (se 2 (by rfl) ⟨5349528, by rfl⟩ : syracuseStep 14265409 = 10699057) B10699057
theorem B19020545 : Blo 1977435 19020545 := bstep (se 2 (by rfl) ⟨7132704, by rfl⟩ : syracuseStep 19020545 = 14265409) B14265409
theorem B12680363 : Blo 1977435 12680363 := bstep (se 1 (by rfl) ⟨9510272, by rfl⟩ : syracuseStep 12680363 = 19020545) B19020545
theorem B8453575 : Blo 1977435 8453575 := bstep (se 1 (by rfl) ⟨6340181, by rfl⟩ : syracuseStep 8453575 = 12680363) B12680363
theorem B11271433 : Blo 1977435 11271433 := bstep (se 2 (by rfl) ⟨4226787, by rfl⟩ : syracuseStep 11271433 = 8453575) B8453575
theorem B15028577 : Blo 1977435 15028577 := bstep (se 2 (by rfl) ⟨5635716, by rfl⟩ : syracuseStep 15028577 = 11271433) B11271433
theorem B10019051 : Blo 1977435 10019051 := bstep (se 1 (by rfl) ⟨7514288, by rfl⟩ : syracuseStep 10019051 = 15028577) B15028577
theorem B6679367 : Blo 1977435 6679367 := bstep (se 1 (by rfl) ⟨5009525, by rfl⟩ : syracuseStep 6679367 = 10019051) B10019051
theorem B4452911 : Blo 1977435 4452911 := bstep (se 1 (by rfl) ⟨3339683, by rfl⟩ : syracuseStep 4452911 = 6679367) B6679367
theorem B2968607 : Blo 1977435 2968607 := bstep (se 1 (by rfl) ⟨2226455, by rfl⟩ : syracuseStep 2968607 = 4452911) B4452911
theorem B1979071 : Blo 1977435 1979071 := bstep (se 1 (by rfl) ⟨1484303, by rfl⟩ : syracuseStep 1979071 = 2968607) B2968607
theorem B2968613 : Blo 1977435 2968613 := bbase (se 4 (by rfl) ⟨278307, by rfl⟩ : syracuseStep 2968613 = 556615) (by norm_num)
theorem B1979075 : Blo 1977435 1979075 := bstep (se 1 (by rfl) ⟨1484306, by rfl⟩ : syracuseStep 1979075 = 2968613) B2968613
theorem B2504773 : Blo 1977435 2504773 := bbase (se 4 (by rfl) ⟨234822, by rfl⟩ : syracuseStep 2504773 = 469645) (by norm_num)
theorem B3339697 : Blo 1977435 3339697 := bstep (se 2 (by rfl) ⟨1252386, by rfl⟩ : syracuseStep 3339697 = 2504773) B2504773
theorem B4452929 : Blo 1977435 4452929 := bstep (se 2 (by rfl) ⟨1669848, by rfl⟩ : syracuseStep 4452929 = 3339697) B3339697
theorem B2968619 : Blo 1977435 2968619 := bstep (se 1 (by rfl) ⟨2226464, by rfl⟩ : syracuseStep 2968619 = 4452929) B4452929
theorem B1979079 : Blo 1977435 1979079 := bstep (se 1 (by rfl) ⟨1484309, by rfl⟩ : syracuseStep 1979079 = 2968619) B2968619
theorem B2226469 : Blo 1977435 2226469 := bbase (se 4 (by rfl) ⟨208731, by rfl⟩ : syracuseStep 2226469 = 417463) (by norm_num)
theorem B2968625 : Blo 1977435 2968625 := bstep (se 2 (by rfl) ⟨1113234, by rfl⟩ : syracuseStep 2968625 = 2226469) B2226469
theorem B1979083 : Blo 1977435 1979083 := bstep (se 1 (by rfl) ⟨1484312, by rfl⟩ : syracuseStep 1979083 = 2968625) B2968625
theorem B3170117 : Blo 1977435 3170117 := bbase (se 4 (by rfl) ⟨297198, by rfl⟩ : syracuseStep 3170117 = 594397) (by norm_num)
theorem B8453645 : Blo 1977435 8453645 := bstep (se 3 (by rfl) ⟨1585058, by rfl⟩ : syracuseStep 8453645 = 3170117) B3170117
theorem B5635763 : Blo 1977435 5635763 := bstep (se 1 (by rfl) ⟨4226822, by rfl⟩ : syracuseStep 5635763 = 8453645) B8453645
theorem B3757175 : Blo 1977435 3757175 := bstep (se 1 (by rfl) ⟨2817881, by rfl⟩ : syracuseStep 3757175 = 5635763) B5635763
theorem B2504783 : Blo 1977435 2504783 := bstep (se 1 (by rfl) ⟨1878587, by rfl⟩ : syracuseStep 2504783 = 3757175) B3757175
theorem B6679421 : Blo 1977435 6679421 := bstep (se 3 (by rfl) ⟨1252391, by rfl⟩ : syracuseStep 6679421 = 2504783) B2504783
theorem B4452947 : Blo 1977435 4452947 := bstep (se 1 (by rfl) ⟨3339710, by rfl⟩ : syracuseStep 4452947 = 6679421) B6679421
theorem B2968631 : Blo 1977435 2968631 := bstep (se 1 (by rfl) ⟨2226473, by rfl⟩ : syracuseStep 2968631 = 4452947) B4452947
theorem B1979087 : Blo 1977435 1979087 := bstep (se 1 (by rfl) ⟨1484315, by rfl⟩ : syracuseStep 1979087 = 2968631) B2968631
theorem B2968637 : Blo 1977435 2968637 := bbase (se 3 (by rfl) ⟨556619, by rfl⟩ : syracuseStep 2968637 = 1113239) (by norm_num)
theorem B1979091 : Blo 1977435 1979091 := bstep (se 1 (by rfl) ⟨1484318, by rfl⟩ : syracuseStep 1979091 = 2968637) B2968637
theorem B4452965 : Blo 1977435 4452965 := bbase (se 4 (by rfl) ⟨417465, by rfl⟩ : syracuseStep 4452965 = 834931) (by norm_num)
theorem B2968643 : Blo 1977435 2968643 := bstep (se 1 (by rfl) ⟨2226482, by rfl⟩ : syracuseStep 2968643 = 4452965) B4452965
theorem B1979095 : Blo 1977435 1979095 := bstep (se 1 (by rfl) ⟨1484321, by rfl⟩ : syracuseStep 1979095 = 2968643) B2968643
theorem B5009597 : Blo 1977435 5009597 := bbase (se 3 (by rfl) ⟨939299, by rfl⟩ : syracuseStep 5009597 = 1878599) (by norm_num)
theorem B3339731 : Blo 1977435 3339731 := bstep (se 1 (by rfl) ⟨2504798, by rfl⟩ : syracuseStep 3339731 = 5009597) B5009597
theorem B2226487 : Blo 1977435 2226487 := bstep (se 1 (by rfl) ⟨1669865, by rfl⟩ : syracuseStep 2226487 = 3339731) B3339731
theorem B2968649 : Blo 1977435 2968649 := bstep (se 2 (by rfl) ⟨1113243, by rfl⟩ : syracuseStep 2968649 = 2226487) B2226487
theorem B1979099 : Blo 1977435 1979099 := bstep (se 1 (by rfl) ⟨1484324, by rfl⟩ : syracuseStep 1979099 = 2968649) B2968649
theorem B3757205 : Blo 1977435 3757205 := bbase (se 6 (by rfl) ⟨88059, by rfl⟩ : syracuseStep 3757205 = 176119) (by norm_num)
theorem B10019213 : Blo 1977435 10019213 := bstep (se 3 (by rfl) ⟨1878602, by rfl⟩ : syracuseStep 10019213 = 3757205) B3757205
theorem B6679475 : Blo 1977435 6679475 := bstep (se 1 (by rfl) ⟨5009606, by rfl⟩ : syracuseStep 6679475 = 10019213) B10019213
theorem B4452983 : Blo 1977435 4452983 := bstep (se 1 (by rfl) ⟨3339737, by rfl⟩ : syracuseStep 4452983 = 6679475) B6679475
theorem B2968655 : Blo 1977435 2968655 := bstep (se 1 (by rfl) ⟨2226491, by rfl⟩ : syracuseStep 2968655 = 4452983) B4452983
theorem B1979103 : Blo 1977435 1979103 := bstep (se 1 (by rfl) ⟨1484327, by rfl⟩ : syracuseStep 1979103 = 2968655) B2968655
theorem B2968661 : Blo 1977435 2968661 := bbase (se 8 (by rfl) ⟨17394, by rfl⟩ : syracuseStep 2968661 = 34789) (by norm_num)
theorem B1979107 : Blo 1977435 1979107 := bstep (se 1 (by rfl) ⟨1484330, by rfl⟩ : syracuseStep 1979107 = 2968661) B2968661
theorem B4012229 : Blo 1977435 4012229 := bbase (se 4 (by rfl) ⟨376146, by rfl⟩ : syracuseStep 4012229 = 752293) (by norm_num)
theorem B2674819 : Blo 1977435 2674819 := bstep (se 1 (by rfl) ⟨2006114, by rfl⟩ : syracuseStep 2674819 = 4012229) B4012229
theorem B3566425 : Blo 1977435 3566425 := bstep (se 2 (by rfl) ⟨1337409, by rfl⟩ : syracuseStep 3566425 = 2674819) B2674819
theorem B4755233 : Blo 1977435 4755233 := bstep (se 2 (by rfl) ⟨1783212, by rfl⟩ : syracuseStep 4755233 = 3566425) B3566425
theorem B12680621 : Blo 1977435 12680621 := bstep (se 3 (by rfl) ⟨2377616, by rfl⟩ : syracuseStep 12680621 = 4755233) B4755233
theorem B8453747 : Blo 1977435 8453747 := bstep (se 1 (by rfl) ⟨6340310, by rfl⟩ : syracuseStep 8453747 = 12680621) B12680621
theorem B5635831 : Blo 1977435 5635831 := bstep (se 1 (by rfl) ⟨4226873, by rfl⟩ : syracuseStep 5635831 = 8453747) B8453747
theorem B7514441 : Blo 1977435 7514441 := bstep (se 2 (by rfl) ⟨2817915, by rfl⟩ : syracuseStep 7514441 = 5635831) B5635831
theorem B5009627 : Blo 1977435 5009627 := bstep (se 1 (by rfl) ⟨3757220, by rfl⟩ : syracuseStep 5009627 = 7514441) B7514441
theorem B3339751 : Blo 1977435 3339751 := bstep (se 1 (by rfl) ⟨2504813, by rfl⟩ : syracuseStep 3339751 = 5009627) B5009627
theorem B4453001 : Blo 1977435 4453001 := bstep (se 2 (by rfl) ⟨1669875, by rfl⟩ : syracuseStep 4453001 = 3339751) B3339751
theorem B2968667 : Blo 1977435 2968667 := bstep (se 1 (by rfl) ⟨2226500, by rfl⟩ : syracuseStep 2968667 = 4453001) B4453001
theorem B1979111 : Blo 1977435 1979111 := bstep (se 1 (by rfl) ⟨1484333, by rfl⟩ : syracuseStep 1979111 = 2968667) B2968667
theorem B2226505 : Blo 1977435 2226505 := bbase (se 2 (by rfl) ⟨834939, by rfl⟩ : syracuseStep 2226505 = 1669879) (by norm_num)
theorem B2968673 : Blo 1977435 2968673 := bstep (se 2 (by rfl) ⟨1113252, by rfl⟩ : syracuseStep 2968673 = 2226505) B2226505
theorem B1979115 : Blo 1977435 1979115 := bstep (se 1 (by rfl) ⟨1484336, by rfl⟩ : syracuseStep 1979115 = 2968673) B2968673
theorem B2856373 : Blo 1977435 2856373 := bbase (se 5 (by rfl) ⟨133892, by rfl⟩ : syracuseStep 2856373 = 267785) (by norm_num)
theorem B15233989 : Blo 1977435 15233989 := bstep (se 4 (by rfl) ⟨1428186, by rfl⟩ : syracuseStep 15233989 = 2856373) B2856373
theorem B20311985 : Blo 1977435 20311985 := bstep (se 2 (by rfl) ⟨7616994, by rfl⟩ : syracuseStep 20311985 = 15233989) B15233989
theorem B54165293 : Blo 1977435 54165293 := bstep (se 3 (by rfl) ⟨10155992, by rfl⟩ : syracuseStep 54165293 = 20311985) B20311985
theorem B36110195 : Blo 1977435 36110195 := bstep (se 1 (by rfl) ⟨27082646, by rfl⟩ : syracuseStep 36110195 = 54165293) B54165293
theorem B24073463 : Blo 1977435 24073463 := bstep (se 1 (by rfl) ⟨18055097, by rfl⟩ : syracuseStep 24073463 = 36110195) B36110195
theorem B64195901 : Blo 1977435 64195901 := bstep (se 3 (by rfl) ⟨12036731, by rfl⟩ : syracuseStep 64195901 = 24073463) B24073463
theorem B42797267 : Blo 1977435 42797267 := bstep (se 1 (by rfl) ⟨32097950, by rfl⟩ : syracuseStep 42797267 = 64195901) B64195901
theorem B28531511 : Blo 1977435 28531511 := bstep (se 1 (by rfl) ⟨21398633, by rfl⟩ : syracuseStep 28531511 = 42797267) B42797267
theorem B19021007 : Blo 1977435 19021007 := bstep (se 1 (by rfl) ⟨14265755, by rfl⟩ : syracuseStep 19021007 = 28531511) B28531511
theorem B12680671 : Blo 1977435 12680671 := bstep (se 1 (by rfl) ⟨9510503, by rfl⟩ : syracuseStep 12680671 = 19021007) B19021007
theorem B16907561 : Blo 1977435 16907561 := bstep (se 2 (by rfl) ⟨6340335, by rfl⟩ : syracuseStep 16907561 = 12680671) B12680671
theorem B11271707 : Blo 1977435 11271707 := bstep (se 1 (by rfl) ⟨8453780, by rfl⟩ : syracuseStep 11271707 = 16907561) B16907561
theorem B7514471 : Blo 1977435 7514471 := bstep (se 1 (by rfl) ⟨5635853, by rfl⟩ : syracuseStep 7514471 = 11271707) B11271707
theorem B5009647 : Blo 1977435 5009647 := bstep (se 1 (by rfl) ⟨3757235, by rfl⟩ : syracuseStep 5009647 = 7514471) B7514471
theorem B6679529 : Blo 1977435 6679529 := bstep (se 2 (by rfl) ⟨2504823, by rfl⟩ : syracuseStep 6679529 = 5009647) B5009647
theorem B4453019 : Blo 1977435 4453019 := bstep (se 1 (by rfl) ⟨3339764, by rfl⟩ : syracuseStep 4453019 = 6679529) B6679529
theorem B2968679 : Blo 1977435 2968679 := bstep (se 1 (by rfl) ⟨2226509, by rfl⟩ : syracuseStep 2968679 = 4453019) B4453019
theorem B1979119 : Blo 1977435 1979119 := bstep (se 1 (by rfl) ⟨1484339, by rfl⟩ : syracuseStep 1979119 = 2968679) B2968679
theorem B2968685 : Blo 1977435 2968685 := bbase (se 3 (by rfl) ⟨556628, by rfl⟩ : syracuseStep 2968685 = 1113257) (by norm_num)
theorem B1979123 : Blo 1977435 1979123 := bstep (se 1 (by rfl) ⟨1484342, by rfl⟩ : syracuseStep 1979123 = 2968685) B2968685
theorem B4453037 : Blo 1977435 4453037 := bbase (se 3 (by rfl) ⟨834944, by rfl⟩ : syracuseStep 4453037 = 1669889) (by norm_num)
theorem B2968691 : Blo 1977435 2968691 := bstep (se 1 (by rfl) ⟨2226518, by rfl⟩ : syracuseStep 2968691 = 4453037) B4453037
theorem B1979127 : Blo 1977435 1979127 := bstep (se 1 (by rfl) ⟨1484345, by rfl⟩ : syracuseStep 1979127 = 2968691) B2968691
theorem B4226917 : Blo 1977435 4226917 := bbase (se 4 (by rfl) ⟨396273, by rfl⟩ : syracuseStep 4226917 = 792547) (by norm_num)
theorem B5635889 : Blo 1977435 5635889 := bstep (se 2 (by rfl) ⟨2113458, by rfl⟩ : syracuseStep 5635889 = 4226917) B4226917
theorem B3757259 : Blo 1977435 3757259 := bstep (se 1 (by rfl) ⟨2817944, by rfl⟩ : syracuseStep 3757259 = 5635889) B5635889
theorem B2504839 : Blo 1977435 2504839 := bstep (se 1 (by rfl) ⟨1878629, by rfl⟩ : syracuseStep 2504839 = 3757259) B3757259
theorem B3339785 : Blo 1977435 3339785 := bstep (se 2 (by rfl) ⟨1252419, by rfl⟩ : syracuseStep 3339785 = 2504839) B2504839
theorem B2226523 : Blo 1977435 2226523 := bstep (se 1 (by rfl) ⟨1669892, by rfl⟩ : syracuseStep 2226523 = 3339785) B3339785
theorem B2968697 : Blo 1977435 2968697 := bstep (se 2 (by rfl) ⟨1113261, by rfl⟩ : syracuseStep 2968697 = 2226523) B2226523
theorem B1979131 : Blo 1977435 1979131 := bstep (se 1 (by rfl) ⟨1484348, by rfl⟩ : syracuseStep 1979131 = 2968697) B2968697
theorem B2171525 : Blo 1977435 2171525 := bbase (se 4 (by rfl) ⟨203580, by rfl⟩ : syracuseStep 2171525 = 407161) (by norm_num)
theorem B5790733 : Blo 1977435 5790733 := bstep (se 3 (by rfl) ⟨1085762, by rfl⟩ : syracuseStep 5790733 = 2171525) B2171525
theorem B30883909 : Blo 1977435 30883909 := bstep (se 4 (by rfl) ⟨2895366, by rfl⟩ : syracuseStep 30883909 = 5790733) B5790733
theorem B41178545 : Blo 1977435 41178545 := bstep (se 2 (by rfl) ⟨15441954, by rfl⟩ : syracuseStep 41178545 = 30883909) B30883909
theorem B27452363 : Blo 1977435 27452363 := bstep (se 1 (by rfl) ⟨20589272, by rfl⟩ : syracuseStep 27452363 = 41178545) B41178545
theorem B73206301 : Blo 1977435 73206301 := bstep (se 3 (by rfl) ⟨13726181, by rfl⟩ : syracuseStep 73206301 = 27452363) B27452363
theorem B97608401 : Blo 1977435 97608401 := bstep (se 2 (by rfl) ⟨36603150, by rfl⟩ : syracuseStep 97608401 = 73206301) B73206301
theorem B65072267 : Blo 1977435 65072267 := bstep (se 1 (by rfl) ⟨48804200, by rfl⟩ : syracuseStep 65072267 = 97608401) B97608401
theorem B43381511 : Blo 1977435 43381511 := bstep (se 1 (by rfl) ⟨32536133, by rfl⟩ : syracuseStep 43381511 = 65072267) B65072267
theorem B28921007 : Blo 1977435 28921007 := bstep (se 1 (by rfl) ⟨21690755, by rfl⟩ : syracuseStep 28921007 = 43381511) B43381511
theorem B77122685 : Blo 1977435 77122685 := bstep (se 3 (by rfl) ⟨14460503, by rfl⟩ : syracuseStep 77122685 = 28921007) B28921007
theorem B51415123 : Blo 1977435 51415123 := bstep (se 1 (by rfl) ⟨38561342, by rfl⟩ : syracuseStep 51415123 = 77122685) B77122685
theorem B68553497 : Blo 1977435 68553497 := bstep (se 2 (by rfl) ⟨25707561, by rfl⟩ : syracuseStep 68553497 = 51415123) B51415123
theorem B182809325 : Blo 1977435 182809325 := bstep (se 3 (by rfl) ⟨34276748, by rfl⟩ : syracuseStep 182809325 = 68553497) B68553497
theorem B121872883 : Blo 1977435 121872883 := bstep (se 1 (by rfl) ⟨91404662, by rfl⟩ : syracuseStep 121872883 = 182809325) B182809325
theorem B162497177 : Blo 1977435 162497177 := bstep (se 2 (by rfl) ⟨60936441, by rfl⟩ : syracuseStep 162497177 = 121872883) B121872883
theorem B108331451 : Blo 1977435 108331451 := bstep (se 1 (by rfl) ⟨81248588, by rfl⟩ : syracuseStep 108331451 = 162497177) B162497177
theorem B72220967 : Blo 1977435 72220967 := bstep (se 1 (by rfl) ⟨54165725, by rfl⟩ : syracuseStep 72220967 = 108331451) B108331451
theorem B48147311 : Blo 1977435 48147311 := bstep (se 1 (by rfl) ⟨36110483, by rfl⟩ : syracuseStep 48147311 = 72220967) B72220967
theorem B32098207 : Blo 1977435 32098207 := bstep (se 1 (by rfl) ⟨24073655, by rfl⟩ : syracuseStep 32098207 = 48147311) B48147311
theorem B42797609 : Blo 1977435 42797609 := bstep (se 2 (by rfl) ⟨16049103, by rfl⟩ : syracuseStep 42797609 = 32098207) B32098207
theorem B28531739 : Blo 1977435 28531739 := bstep (se 1 (by rfl) ⟨21398804, by rfl⟩ : syracuseStep 28531739 = 42797609) B42797609
theorem B19021159 : Blo 1977435 19021159 := bstep (se 1 (by rfl) ⟨14265869, by rfl⟩ : syracuseStep 19021159 = 28531739) B28531739
theorem B25361545 : Blo 1977435 25361545 := bstep (se 2 (by rfl) ⟨9510579, by rfl⟩ : syracuseStep 25361545 = 19021159) B19021159
theorem B33815393 : Blo 1977435 33815393 := bstep (se 2 (by rfl) ⟨12680772, by rfl⟩ : syracuseStep 33815393 = 25361545) B25361545
theorem B22543595 : Blo 1977435 22543595 := bstep (se 1 (by rfl) ⟨16907696, by rfl⟩ : syracuseStep 22543595 = 33815393) B33815393
theorem B15029063 : Blo 1977435 15029063 := bstep (se 1 (by rfl) ⟨11271797, by rfl⟩ : syracuseStep 15029063 = 22543595) B22543595
theorem B10019375 : Blo 1977435 10019375 := bstep (se 1 (by rfl) ⟨7514531, by rfl⟩ : syracuseStep 10019375 = 15029063) B15029063
theorem B6679583 : Blo 1977435 6679583 := bstep (se 1 (by rfl) ⟨5009687, by rfl⟩ : syracuseStep 6679583 = 10019375) B10019375
theorem B4453055 : Blo 1977435 4453055 := bstep (se 1 (by rfl) ⟨3339791, by rfl⟩ : syracuseStep 4453055 = 6679583) B6679583
theorem B2968703 : Blo 1977435 2968703 := bstep (se 1 (by rfl) ⟨2226527, by rfl⟩ : syracuseStep 2968703 = 4453055) B4453055
theorem B1979135 : Blo 1977435 1979135 := bstep (se 1 (by rfl) ⟨1484351, by rfl⟩ : syracuseStep 1979135 = 2968703) B2968703
theorem B2968709 : Blo 1977435 2968709 := bbase (se 4 (by rfl) ⟨278316, by rfl⟩ : syracuseStep 2968709 = 556633) (by norm_num)
theorem B1979139 : Blo 1977435 1979139 := bstep (se 1 (by rfl) ⟨1484354, by rfl⟩ : syracuseStep 1979139 = 2968709) B2968709
theorem B3339805 : Blo 1977435 3339805 := bbase (se 3 (by rfl) ⟨626213, by rfl⟩ : syracuseStep 3339805 = 1252427) (by norm_num)
theorem B4453073 : Blo 1977435 4453073 := bstep (se 2 (by rfl) ⟨1669902, by rfl⟩ : syracuseStep 4453073 = 3339805) B3339805
theorem B2968715 : Blo 1977435 2968715 := bstep (se 1 (by rfl) ⟨2226536, by rfl⟩ : syracuseStep 2968715 = 4453073) B4453073
theorem B1979143 : Blo 1977435 1979143 := bstep (se 1 (by rfl) ⟨1484357, by rfl⟩ : syracuseStep 1979143 = 2968715) B2968715
theorem B2226541 : Blo 1977435 2226541 := bbase (se 3 (by rfl) ⟨417476, by rfl⟩ : syracuseStep 2226541 = 834953) (by norm_num)
theorem B2968721 : Blo 1977435 2968721 := bstep (se 2 (by rfl) ⟨1113270, by rfl⟩ : syracuseStep 2968721 = 2226541) B2226541
theorem B1979147 : Blo 1977435 1979147 := bstep (se 1 (by rfl) ⟨1484360, by rfl⟩ : syracuseStep 1979147 = 2968721) B2968721
theorem B6679637 : Blo 1977435 6679637 := bbase (se 8 (by rfl) ⟨39138, by rfl⟩ : syracuseStep 6679637 = 78277) (by norm_num)
theorem B4453091 : Blo 1977435 4453091 := bstep (se 1 (by rfl) ⟨3339818, by rfl⟩ : syracuseStep 4453091 = 6679637) B6679637
theorem B2968727 : Blo 1977435 2968727 := bstep (se 1 (by rfl) ⟨2226545, by rfl⟩ : syracuseStep 2968727 = 4453091) B4453091
theorem B1979151 : Blo 1977435 1979151 := bstep (se 1 (by rfl) ⟨1484363, by rfl⟩ : syracuseStep 1979151 = 2968727) B2968727
theorem B2968733 : Blo 1977435 2968733 := bbase (se 3 (by rfl) ⟨556637, by rfl⟩ : syracuseStep 2968733 = 1113275) (by norm_num)
theorem B1979155 : Blo 1977435 1979155 := bstep (se 1 (by rfl) ⟨1484366, by rfl⟩ : syracuseStep 1979155 = 2968733) B2968733
theorem B4453109 : Blo 1977435 4453109 := bbase (se 5 (by rfl) ⟨208739, by rfl⟩ : syracuseStep 4453109 = 417479) (by norm_num)
theorem B2968739 : Blo 1977435 2968739 := bstep (se 1 (by rfl) ⟨2226554, by rfl⟩ : syracuseStep 2968739 = 4453109) B4453109
theorem B1979159 : Blo 1977435 1979159 := bstep (se 1 (by rfl) ⟨1484369, by rfl⟩ : syracuseStep 1979159 = 2968739) B2968739
theorem B4513877 : Blo 1977435 4513877 := bbase (se 8 (by rfl) ⟨26448, by rfl⟩ : syracuseStep 4513877 = 52897) (by norm_num)
theorem B3009251 : Blo 1977435 3009251 := bstep (se 1 (by rfl) ⟨2256938, by rfl⟩ : syracuseStep 3009251 = 4513877) B4513877
theorem B8024669 : Blo 1977435 8024669 := bstep (se 3 (by rfl) ⟨1504625, by rfl⟩ : syracuseStep 8024669 = 3009251) B3009251
theorem B5349779 : Blo 1977435 5349779 := bstep (se 1 (by rfl) ⟨4012334, by rfl⟩ : syracuseStep 5349779 = 8024669) B8024669
theorem B3566519 : Blo 1977435 3566519 := bstep (se 1 (by rfl) ⟨2674889, by rfl⟩ : syracuseStep 3566519 = 5349779) B5349779
theorem B2377679 : Blo 1977435 2377679 := bstep (se 1 (by rfl) ⟨1783259, by rfl⟩ : syracuseStep 2377679 = 3566519) B3566519
theorem B25361909 : Blo 1977435 25361909 := bstep (se 5 (by rfl) ⟨1188839, by rfl⟩ : syracuseStep 25361909 = 2377679) B2377679
theorem B16907939 : Blo 1977435 16907939 := bstep (se 1 (by rfl) ⟨12680954, by rfl⟩ : syracuseStep 16907939 = 25361909) B25361909
theorem B11271959 : Blo 1977435 11271959 := bstep (se 1 (by rfl) ⟨8453969, by rfl⟩ : syracuseStep 11271959 = 16907939) B16907939
theorem B7514639 : Blo 1977435 7514639 := bstep (se 1 (by rfl) ⟨5635979, by rfl⟩ : syracuseStep 7514639 = 11271959) B11271959
theorem B5009759 : Blo 1977435 5009759 := bstep (se 1 (by rfl) ⟨3757319, by rfl⟩ : syracuseStep 5009759 = 7514639) B7514639
theorem B3339839 : Blo 1977435 3339839 := bstep (se 1 (by rfl) ⟨2504879, by rfl⟩ : syracuseStep 3339839 = 5009759) B5009759
theorem B2226559 : Blo 1977435 2226559 := bstep (se 1 (by rfl) ⟨1669919, by rfl⟩ : syracuseStep 2226559 = 3339839) B3339839
theorem B2968745 : Blo 1977435 2968745 := bstep (se 2 (by rfl) ⟨1113279, by rfl⟩ : syracuseStep 2968745 = 2226559) B2226559
theorem B1979163 : Blo 1977435 1979163 := bstep (se 1 (by rfl) ⟨1484372, by rfl⟩ : syracuseStep 1979163 = 2968745) B2968745
theorem B3170245 : Blo 1977435 3170245 := bbase (se 4 (by rfl) ⟨297210, by rfl⟩ : syracuseStep 3170245 = 594421) (by norm_num)
theorem B4226993 : Blo 1977435 4226993 := bstep (se 2 (by rfl) ⟨1585122, by rfl⟩ : syracuseStep 4226993 = 3170245) B3170245
theorem B2817995 : Blo 1977435 2817995 := bstep (se 1 (by rfl) ⟨2113496, by rfl⟩ : syracuseStep 2817995 = 4226993) B4226993
theorem B7514653 : Blo 1977435 7514653 := bstep (se 3 (by rfl) ⟨1408997, by rfl⟩ : syracuseStep 7514653 = 2817995) B2817995
theorem B10019537 : Blo 1977435 10019537 := bstep (se 2 (by rfl) ⟨3757326, by rfl⟩ : syracuseStep 10019537 = 7514653) B7514653
theorem B6679691 : Blo 1977435 6679691 := bstep (se 1 (by rfl) ⟨5009768, by rfl⟩ : syracuseStep 6679691 = 10019537) B10019537
theorem B4453127 : Blo 1977435 4453127 := bstep (se 1 (by rfl) ⟨3339845, by rfl⟩ : syracuseStep 4453127 = 6679691) B6679691
theorem B2968751 : Blo 1977435 2968751 := bstep (se 1 (by rfl) ⟨2226563, by rfl⟩ : syracuseStep 2968751 = 4453127) B4453127
theorem B1979167 : Blo 1977435 1979167 := bstep (se 1 (by rfl) ⟨1484375, by rfl⟩ : syracuseStep 1979167 = 2968751) B2968751
theorem B2968757 : Blo 1977435 2968757 := bbase (se 5 (by rfl) ⟨139160, by rfl⟩ : syracuseStep 2968757 = 278321) (by norm_num)
theorem B1979171 : Blo 1977435 1979171 := bstep (se 1 (by rfl) ⟨1484378, by rfl⟩ : syracuseStep 1979171 = 2968757) B2968757
theorem B5009789 : Blo 1977435 5009789 := bbase (se 3 (by rfl) ⟨939335, by rfl⟩ : syracuseStep 5009789 = 1878671) (by norm_num)
theorem B3339859 : Blo 1977435 3339859 := bstep (se 1 (by rfl) ⟨2504894, by rfl⟩ : syracuseStep 3339859 = 5009789) B5009789
theorem B4453145 : Blo 1977435 4453145 := bstep (se 2 (by rfl) ⟨1669929, by rfl⟩ : syracuseStep 4453145 = 3339859) B3339859
theorem B2968763 : Blo 1977435 2968763 := bstep (se 1 (by rfl) ⟨2226572, by rfl⟩ : syracuseStep 2968763 = 4453145) B4453145
theorem B1979175 : Blo 1977435 1979175 := bstep (se 1 (by rfl) ⟨1484381, by rfl⟩ : syracuseStep 1979175 = 2968763) B2968763
theorem B2226577 : Blo 1977435 2226577 := bbase (se 2 (by rfl) ⟨834966, by rfl⟩ : syracuseStep 2226577 = 1669933) (by norm_num)
theorem B2968769 : Blo 1977435 2968769 := bstep (se 2 (by rfl) ⟨1113288, by rfl⟩ : syracuseStep 2968769 = 2226577) B2226577
theorem B1979179 : Blo 1977435 1979179 := bstep (se 1 (by rfl) ⟨1484384, by rfl⟩ : syracuseStep 1979179 = 2968769) B2968769
theorem B3757357 : Blo 1977435 3757357 := bbase (se 3 (by rfl) ⟨704504, by rfl⟩ : syracuseStep 3757357 = 1409009) (by norm_num)
theorem B5009809 : Blo 1977435 5009809 := bstep (se 2 (by rfl) ⟨1878678, by rfl⟩ : syracuseStep 5009809 = 3757357) B3757357
theorem B6679745 : Blo 1977435 6679745 := bstep (se 2 (by rfl) ⟨2504904, by rfl⟩ : syracuseStep 6679745 = 5009809) B5009809
theorem B4453163 : Blo 1977435 4453163 := bstep (se 1 (by rfl) ⟨3339872, by rfl⟩ : syracuseStep 4453163 = 6679745) B6679745
theorem B2968775 : Blo 1977435 2968775 := bstep (se 1 (by rfl) ⟨2226581, by rfl⟩ : syracuseStep 2968775 = 4453163) B4453163
theorem B1979183 : Blo 1977435 1979183 := bstep (se 1 (by rfl) ⟨1484387, by rfl⟩ : syracuseStep 1979183 = 2968775) B2968775
theorem B2968781 : Blo 1977435 2968781 := bbase (se 3 (by rfl) ⟨556646, by rfl⟩ : syracuseStep 2968781 = 1113293) (by norm_num)
theorem B1979187 : Blo 1977435 1979187 := bstep (se 1 (by rfl) ⟨1484390, by rfl⟩ : syracuseStep 1979187 = 2968781) B2968781
theorem B4453181 : Blo 1977435 4453181 := bbase (se 3 (by rfl) ⟨834971, by rfl⟩ : syracuseStep 4453181 = 1669943) (by norm_num)
theorem B2968787 : Blo 1977435 2968787 := bstep (se 1 (by rfl) ⟨2226590, by rfl⟩ : syracuseStep 2968787 = 4453181) B4453181
theorem B1979191 : Blo 1977435 1979191 := bstep (se 1 (by rfl) ⟨1484393, by rfl⟩ : syracuseStep 1979191 = 2968787) B2968787
theorem B3339893 : Blo 1977435 3339893 := bbase (se 5 (by rfl) ⟨156557, by rfl⟩ : syracuseStep 3339893 = 313115) (by norm_num)
theorem B2226595 : Blo 1977435 2226595 := bstep (se 1 (by rfl) ⟨1669946, by rfl⟩ : syracuseStep 2226595 = 3339893) B3339893
theorem B2968793 : Blo 1977435 2968793 := bstep (se 2 (by rfl) ⟨1113297, by rfl⟩ : syracuseStep 2968793 = 2226595) B2226595
theorem B1979195 : Blo 1977435 1979195 := bstep (se 1 (by rfl) ⟨1484396, by rfl⟩ : syracuseStep 1979195 = 2968793) B2968793
theorem B4227061 : Blo 1977435 4227061 := bbase (se 5 (by rfl) ⟨198143, by rfl⟩ : syracuseStep 4227061 = 396287) (by norm_num)
theorem B5636081 : Blo 1977435 5636081 := bstep (se 2 (by rfl) ⟨2113530, by rfl⟩ : syracuseStep 5636081 = 4227061) B4227061
theorem B15029549 : Blo 1977435 15029549 := bstep (se 3 (by rfl) ⟨2818040, by rfl⟩ : syracuseStep 15029549 = 5636081) B5636081
theorem B10019699 : Blo 1977435 10019699 := bstep (se 1 (by rfl) ⟨7514774, by rfl⟩ : syracuseStep 10019699 = 15029549) B15029549
theorem B6679799 : Blo 1977435 6679799 := bstep (se 1 (by rfl) ⟨5009849, by rfl⟩ : syracuseStep 6679799 = 10019699) B10019699
theorem B4453199 : Blo 1977435 4453199 := bstep (se 1 (by rfl) ⟨3339899, by rfl⟩ : syracuseStep 4453199 = 6679799) B6679799
theorem B2968799 : Blo 1977435 2968799 := bstep (se 1 (by rfl) ⟨2226599, by rfl⟩ : syracuseStep 2968799 = 4453199) B4453199
theorem B1979199 : Blo 1977435 1979199 := bstep (se 1 (by rfl) ⟨1484399, by rfl⟩ : syracuseStep 1979199 = 2968799) B2968799
theorem B2968805 : Blo 1977435 2968805 := bbase (se 4 (by rfl) ⟨278325, by rfl⟩ : syracuseStep 2968805 = 556651) (by norm_num)
theorem B1979203 : Blo 1977435 1979203 := bstep (se 1 (by rfl) ⟨1484402, by rfl⟩ : syracuseStep 1979203 = 2968805) B2968805
theorem B2674949 : Blo 1977435 2674949 := bbase (se 4 (by rfl) ⟨250776, by rfl⟩ : syracuseStep 2674949 = 501553) (by norm_num)
theorem B7133197 : Blo 1977435 7133197 := bstep (se 3 (by rfl) ⟨1337474, by rfl⟩ : syracuseStep 7133197 = 2674949) B2674949
theorem B9510929 : Blo 1977435 9510929 := bstep (se 2 (by rfl) ⟨3566598, by rfl⟩ : syracuseStep 9510929 = 7133197) B7133197
theorem B6340619 : Blo 1977435 6340619 := bstep (se 1 (by rfl) ⟨4755464, by rfl⟩ : syracuseStep 6340619 = 9510929) B9510929
theorem B4227079 : Blo 1977435 4227079 := bstep (se 1 (by rfl) ⟨3170309, by rfl⟩ : syracuseStep 4227079 = 6340619) B6340619
theorem B5636105 : Blo 1977435 5636105 := bstep (se 2 (by rfl) ⟨2113539, by rfl⟩ : syracuseStep 5636105 = 4227079) B4227079
theorem B3757403 : Blo 1977435 3757403 := bstep (se 1 (by rfl) ⟨2818052, by rfl⟩ : syracuseStep 3757403 = 5636105) B5636105
theorem B2504935 : Blo 1977435 2504935 := bstep (se 1 (by rfl) ⟨1878701, by rfl⟩ : syracuseStep 2504935 = 3757403) B3757403
theorem B3339913 : Blo 1977435 3339913 := bstep (se 2 (by rfl) ⟨1252467, by rfl⟩ : syracuseStep 3339913 = 2504935) B2504935
theorem B4453217 : Blo 1977435 4453217 := bstep (se 2 (by rfl) ⟨1669956, by rfl⟩ : syracuseStep 4453217 = 3339913) B3339913
theorem B2968811 : Blo 1977435 2968811 := bstep (se 1 (by rfl) ⟨2226608, by rfl⟩ : syracuseStep 2968811 = 4453217) B4453217
theorem B1979207 : Blo 1977435 1979207 := bstep (se 1 (by rfl) ⟨1484405, by rfl⟩ : syracuseStep 1979207 = 2968811) B2968811
theorem B2226613 : Blo 1977435 2226613 := bbase (se 5 (by rfl) ⟨104372, by rfl⟩ : syracuseStep 2226613 = 208745) (by norm_num)
theorem B2968817 : Blo 1977435 2968817 := bstep (se 2 (by rfl) ⟨1113306, by rfl⟩ : syracuseStep 2968817 = 2226613) B2226613
theorem B1979211 : Blo 1977435 1979211 := bstep (se 1 (by rfl) ⟨1484408, by rfl⟩ : syracuseStep 1979211 = 2968817) B2968817
theorem B2504945 : Blo 1977435 2504945 := bbase (se 2 (by rfl) ⟨939354, by rfl⟩ : syracuseStep 2504945 = 1878709) (by norm_num)
theorem B6679853 : Blo 1977435 6679853 := bstep (se 3 (by rfl) ⟨1252472, by rfl⟩ : syracuseStep 6679853 = 2504945) B2504945
theorem B4453235 : Blo 1977435 4453235 := bstep (se 1 (by rfl) ⟨3339926, by rfl⟩ : syracuseStep 4453235 = 6679853) B6679853
theorem B2968823 : Blo 1977435 2968823 := bstep (se 1 (by rfl) ⟨2226617, by rfl⟩ : syracuseStep 2968823 = 4453235) B4453235
theorem B1979215 : Blo 1977435 1979215 := bstep (se 1 (by rfl) ⟨1484411, by rfl⟩ : syracuseStep 1979215 = 2968823) B2968823
theorem B2968829 : Blo 1977435 2968829 := bbase (se 3 (by rfl) ⟨556655, by rfl⟩ : syracuseStep 2968829 = 1113311) (by norm_num)
theorem B1979219 : Blo 1977435 1979219 := bstep (se 1 (by rfl) ⟨1484414, by rfl⟩ : syracuseStep 1979219 = 2968829) B2968829
theorem B4453253 : Blo 1977435 4453253 := bbase (se 4 (by rfl) ⟨417492, by rfl⟩ : syracuseStep 4453253 = 834985) (by norm_num)
theorem B2968835 : Blo 1977435 2968835 := bstep (se 1 (by rfl) ⟨2226626, by rfl⟩ : syracuseStep 2968835 = 4453253) B4453253
theorem B1979223 : Blo 1977435 1979223 := bstep (se 1 (by rfl) ⟨1484417, by rfl⟩ : syracuseStep 1979223 = 2968835) B2968835
theorem B2113561 : Blo 1977435 2113561 := bbase (se 2 (by rfl) ⟨792585, by rfl⟩ : syracuseStep 2113561 = 1585171) (by norm_num)
theorem B2818081 : Blo 1977435 2818081 := bstep (se 2 (by rfl) ⟨1056780, by rfl⟩ : syracuseStep 2818081 = 2113561) B2113561
theorem B3757441 : Blo 1977435 3757441 := bstep (se 2 (by rfl) ⟨1409040, by rfl⟩ : syracuseStep 3757441 = 2818081) B2818081
theorem B5009921 : Blo 1977435 5009921 := bstep (se 2 (by rfl) ⟨1878720, by rfl⟩ : syracuseStep 5009921 = 3757441) B3757441
theorem B3339947 : Blo 1977435 3339947 := bstep (se 1 (by rfl) ⟨2504960, by rfl⟩ : syracuseStep 3339947 = 5009921) B5009921
theorem B2226631 : Blo 1977435 2226631 := bstep (se 1 (by rfl) ⟨1669973, by rfl⟩ : syracuseStep 2226631 = 3339947) B3339947
theorem B2968841 : Blo 1977435 2968841 := bstep (se 2 (by rfl) ⟨1113315, by rfl⟩ : syracuseStep 2968841 = 2226631) B2226631
theorem B1979227 : Blo 1977435 1979227 := bstep (se 1 (by rfl) ⟨1484420, by rfl⟩ : syracuseStep 1979227 = 2968841) B2968841
theorem B10019861 : Blo 1977435 10019861 := bbase (se 6 (by rfl) ⟨234840, by rfl⟩ : syracuseStep 10019861 = 469681) (by norm_num)
theorem B6679907 : Blo 1977435 6679907 := bstep (se 1 (by rfl) ⟨5009930, by rfl⟩ : syracuseStep 6679907 = 10019861) B10019861
theorem B4453271 : Blo 1977435 4453271 := bstep (se 1 (by rfl) ⟨3339953, by rfl⟩ : syracuseStep 4453271 = 6679907) B6679907
theorem B2968847 : Blo 1977435 2968847 := bstep (se 1 (by rfl) ⟨2226635, by rfl⟩ : syracuseStep 2968847 = 4453271) B4453271
theorem B1979231 : Blo 1977435 1979231 := bstep (se 1 (by rfl) ⟨1484423, by rfl⟩ : syracuseStep 1979231 = 2968847) B2968847
theorem B2968853 : Blo 1977435 2968853 := bbase (se 6 (by rfl) ⟨69582, by rfl⟩ : syracuseStep 2968853 = 139165) (by norm_num)
theorem B1979235 : Blo 1977435 1979235 := bstep (se 1 (by rfl) ⟨1484426, by rfl⟩ : syracuseStep 1979235 = 2968853) B2968853
theorem B4284821 : Blo 1977435 4284821 := bbase (se 6 (by rfl) ⟨100425, by rfl⟩ : syracuseStep 4284821 = 200851) (by norm_num)
theorem B2856547 : Blo 1977435 2856547 := bstep (se 1 (by rfl) ⟨2142410, by rfl⟩ : syracuseStep 2856547 = 4284821) B4284821
theorem B3808729 : Blo 1977435 3808729 := bstep (se 2 (by rfl) ⟨1428273, by rfl⟩ : syracuseStep 3808729 = 2856547) B2856547
theorem B5078305 : Blo 1977435 5078305 := bstep (se 2 (by rfl) ⟨1904364, by rfl⟩ : syracuseStep 5078305 = 3808729) B3808729
theorem B27084293 : Blo 1977435 27084293 := bstep (se 4 (by rfl) ⟨2539152, by rfl⟩ : syracuseStep 27084293 = 5078305) B5078305
theorem B18056195 : Blo 1977435 18056195 := bstep (se 1 (by rfl) ⟨13542146, by rfl⟩ : syracuseStep 18056195 = 27084293) B27084293
theorem B12037463 : Blo 1977435 12037463 := bstep (se 1 (by rfl) ⟨9028097, by rfl⟩ : syracuseStep 12037463 = 18056195) B18056195
theorem B8024975 : Blo 1977435 8024975 := bstep (se 1 (by rfl) ⟨6018731, by rfl⟩ : syracuseStep 8024975 = 12037463) B12037463
theorem B5349983 : Blo 1977435 5349983 := bstep (se 1 (by rfl) ⟨4012487, by rfl⟩ : syracuseStep 5349983 = 8024975) B8024975
theorem B14266621 : Blo 1977435 14266621 := bstep (se 3 (by rfl) ⟨2674991, by rfl⟩ : syracuseStep 14266621 = 5349983) B5349983
theorem B19022161 : Blo 1977435 19022161 := bstep (se 2 (by rfl) ⟨7133310, by rfl⟩ : syracuseStep 19022161 = 14266621) B14266621
theorem B25362881 : Blo 1977435 25362881 := bstep (se 2 (by rfl) ⟨9511080, by rfl⟩ : syracuseStep 25362881 = 19022161) B19022161
theorem B16908587 : Blo 1977435 16908587 := bstep (se 1 (by rfl) ⟨12681440, by rfl⟩ : syracuseStep 16908587 = 25362881) B25362881
theorem B11272391 : Blo 1977435 11272391 := bstep (se 1 (by rfl) ⟨8454293, by rfl⟩ : syracuseStep 11272391 = 16908587) B16908587
theorem B7514927 : Blo 1977435 7514927 := bstep (se 1 (by rfl) ⟨5636195, by rfl⟩ : syracuseStep 7514927 = 11272391) B11272391
theorem B5009951 : Blo 1977435 5009951 := bstep (se 1 (by rfl) ⟨3757463, by rfl⟩ : syracuseStep 5009951 = 7514927) B7514927
theorem B3339967 : Blo 1977435 3339967 := bstep (se 1 (by rfl) ⟨2504975, by rfl⟩ : syracuseStep 3339967 = 5009951) B5009951
theorem B4453289 : Blo 1977435 4453289 := bstep (se 2 (by rfl) ⟨1669983, by rfl⟩ : syracuseStep 4453289 = 3339967) B3339967
theorem B2968859 : Blo 1977435 2968859 := bstep (se 1 (by rfl) ⟨2226644, by rfl⟩ : syracuseStep 2968859 = 4453289) B4453289
theorem B1979239 : Blo 1977435 1979239 := bstep (se 1 (by rfl) ⟨1484429, by rfl⟩ : syracuseStep 1979239 = 2968859) B2968859
theorem B2226649 : Blo 1977435 2226649 := bbase (se 2 (by rfl) ⟨834993, by rfl⟩ : syracuseStep 2226649 = 1669987) (by norm_num)
theorem B2968865 : Blo 1977435 2968865 := bstep (se 2 (by rfl) ⟨1113324, by rfl⟩ : syracuseStep 2968865 = 2226649) B2226649
theorem B1979243 : Blo 1977435 1979243 := bstep (se 1 (by rfl) ⟨1484432, by rfl⟩ : syracuseStep 1979243 = 2968865) B2968865
theorem B2818109 : Blo 1977435 2818109 := bbase (se 3 (by rfl) ⟨528395, by rfl⟩ : syracuseStep 2818109 = 1056791) (by norm_num)
theorem B7514957 : Blo 1977435 7514957 := bstep (se 3 (by rfl) ⟨1409054, by rfl⟩ : syracuseStep 7514957 = 2818109) B2818109
theorem B5009971 : Blo 1977435 5009971 := bstep (se 1 (by rfl) ⟨3757478, by rfl⟩ : syracuseStep 5009971 = 7514957) B7514957
theorem B6679961 : Blo 1977435 6679961 := bstep (se 2 (by rfl) ⟨2504985, by rfl⟩ : syracuseStep 6679961 = 5009971) B5009971
theorem B4453307 : Blo 1977435 4453307 := bstep (se 1 (by rfl) ⟨3339980, by rfl⟩ : syracuseStep 4453307 = 6679961) B6679961
theorem B2968871 : Blo 1977435 2968871 := bstep (se 1 (by rfl) ⟨2226653, by rfl⟩ : syracuseStep 2968871 = 4453307) B4453307
theorem B1979247 : Blo 1977435 1979247 := bstep (se 1 (by rfl) ⟨1484435, by rfl⟩ : syracuseStep 1979247 = 2968871) B2968871
theorem B2968877 : Blo 1977435 2968877 := bbase (se 3 (by rfl) ⟨556664, by rfl⟩ : syracuseStep 2968877 = 1113329) (by norm_num)
theorem B1979251 : Blo 1977435 1979251 := bstep (se 1 (by rfl) ⟨1484438, by rfl⟩ : syracuseStep 1979251 = 2968877) B2968877
theorem B4453325 : Blo 1977435 4453325 := bbase (se 3 (by rfl) ⟨834998, by rfl⟩ : syracuseStep 4453325 = 1669997) (by norm_num)
theorem B2968883 : Blo 1977435 2968883 := bstep (se 1 (by rfl) ⟨2226662, by rfl⟩ : syracuseStep 2968883 = 4453325) B4453325
theorem B1979255 : Blo 1977435 1979255 := bstep (se 1 (by rfl) ⟨1484441, by rfl⟩ : syracuseStep 1979255 = 2968883) B2968883
theorem B2505001 : Blo 1977435 2505001 := bbase (se 2 (by rfl) ⟨939375, by rfl⟩ : syracuseStep 2505001 = 1878751) (by norm_num)
theorem B3340001 : Blo 1977435 3340001 := bstep (se 2 (by rfl) ⟨1252500, by rfl⟩ : syracuseStep 3340001 = 2505001) B2505001
theorem B2226667 : Blo 1977435 2226667 := bstep (se 1 (by rfl) ⟨1670000, by rfl⟩ : syracuseStep 2226667 = 3340001) B3340001
theorem B2968889 : Blo 1977435 2968889 := bstep (se 2 (by rfl) ⟨1113333, by rfl⟩ : syracuseStep 2968889 = 2226667) B2226667
theorem B1979259 : Blo 1977435 1979259 := bstep (se 1 (by rfl) ⟨1484444, by rfl⟩ : syracuseStep 1979259 = 2968889) B2968889
theorem B3050461 : Blo 1977435 3050461 := bbase (se 3 (by rfl) ⟨571961, by rfl⟩ : syracuseStep 3050461 = 1143923) (by norm_num)
theorem B4067281 : Blo 1977435 4067281 := bstep (se 2 (by rfl) ⟨1525230, by rfl⟩ : syracuseStep 4067281 = 3050461) B3050461
theorem B5423041 : Blo 1977435 5423041 := bstep (se 2 (by rfl) ⟨2033640, by rfl⟩ : syracuseStep 5423041 = 4067281) B4067281
theorem B7230721 : Blo 1977435 7230721 := bstep (se 2 (by rfl) ⟨2711520, by rfl⟩ : syracuseStep 7230721 = 5423041) B5423041
theorem B9640961 : Blo 1977435 9640961 := bstep (se 2 (by rfl) ⟨3615360, by rfl⟩ : syracuseStep 9640961 = 7230721) B7230721
theorem B6427307 : Blo 1977435 6427307 := bstep (se 1 (by rfl) ⟨4820480, by rfl⟩ : syracuseStep 6427307 = 9640961) B9640961
theorem B17139485 : Blo 1977435 17139485 := bstep (se 3 (by rfl) ⟨3213653, by rfl⟩ : syracuseStep 17139485 = 6427307) B6427307
theorem B45705293 : Blo 1977435 45705293 := bstep (se 3 (by rfl) ⟨8569742, by rfl⟩ : syracuseStep 45705293 = 17139485) B17139485
theorem B30470195 : Blo 1977435 30470195 := bstep (se 1 (by rfl) ⟨22852646, by rfl⟩ : syracuseStep 30470195 = 45705293) B45705293
theorem B81253853 : Blo 1977435 81253853 := bstep (se 3 (by rfl) ⟨15235097, by rfl⟩ : syracuseStep 81253853 = 30470195) B30470195
theorem B54169235 : Blo 1977435 54169235 := bstep (se 1 (by rfl) ⟨40626926, by rfl⟩ : syracuseStep 54169235 = 81253853) B81253853
theorem B36112823 : Blo 1977435 36112823 := bstep (se 1 (by rfl) ⟨27084617, by rfl⟩ : syracuseStep 36112823 = 54169235) B54169235
theorem B24075215 : Blo 1977435 24075215 := bstep (se 1 (by rfl) ⟨18056411, by rfl⟩ : syracuseStep 24075215 = 36112823) B36112823
theorem B16050143 : Blo 1977435 16050143 := bstep (se 1 (by rfl) ⟨12037607, by rfl⟩ : syracuseStep 16050143 = 24075215) B24075215
theorem B10700095 : Blo 1977435 10700095 := bstep (se 1 (by rfl) ⟨8025071, by rfl⟩ : syracuseStep 10700095 = 16050143) B16050143
theorem B14266793 : Blo 1977435 14266793 := bstep (se 2 (by rfl) ⟨5350047, by rfl⟩ : syracuseStep 14266793 = 10700095) B10700095
theorem B9511195 : Blo 1977435 9511195 := bstep (se 1 (by rfl) ⟨7133396, by rfl⟩ : syracuseStep 9511195 = 14266793) B14266793
theorem B12681593 : Blo 1977435 12681593 := bstep (se 2 (by rfl) ⟨4755597, by rfl⟩ : syracuseStep 12681593 = 9511195) B9511195
theorem B8454395 : Blo 1977435 8454395 := bstep (se 1 (by rfl) ⟨6340796, by rfl⟩ : syracuseStep 8454395 = 12681593) B12681593
theorem B22545053 : Blo 1977435 22545053 := bstep (se 3 (by rfl) ⟨4227197, by rfl⟩ : syracuseStep 22545053 = 8454395) B8454395
theorem B15030035 : Blo 1977435 15030035 := bstep (se 1 (by rfl) ⟨11272526, by rfl⟩ : syracuseStep 15030035 = 22545053) B22545053
theorem B10020023 : Blo 1977435 10020023 := bstep (se 1 (by rfl) ⟨7515017, by rfl⟩ : syracuseStep 10020023 = 15030035) B15030035
theorem B6680015 : Blo 1977435 6680015 := bstep (se 1 (by rfl) ⟨5010011, by rfl⟩ : syracuseStep 6680015 = 10020023) B10020023
theorem B4453343 : Blo 1977435 4453343 := bstep (se 1 (by rfl) ⟨3340007, by rfl⟩ : syracuseStep 4453343 = 6680015) B6680015
theorem B2968895 : Blo 1977435 2968895 := bstep (se 1 (by rfl) ⟨2226671, by rfl⟩ : syracuseStep 2968895 = 4453343) B4453343
theorem B1979263 : Blo 1977435 1979263 := bstep (se 1 (by rfl) ⟨1484447, by rfl⟩ : syracuseStep 1979263 = 2968895) B2968895
theorem B2968901 : Blo 1977435 2968901 := bbase (se 4 (by rfl) ⟨278334, by rfl⟩ : syracuseStep 2968901 = 556669) (by norm_num)
theorem B1979267 : Blo 1977435 1979267 := bstep (se 1 (by rfl) ⟨1484450, by rfl⟩ : syracuseStep 1979267 = 2968901) B2968901
theorem B3340021 : Blo 1977435 3340021 := bbase (se 5 (by rfl) ⟨156563, by rfl⟩ : syracuseStep 3340021 = 313127) (by norm_num)
theorem B4453361 : Blo 1977435 4453361 := bstep (se 2 (by rfl) ⟨1670010, by rfl⟩ : syracuseStep 4453361 = 3340021) B3340021
theorem B2968907 : Blo 1977435 2968907 := bstep (se 1 (by rfl) ⟨2226680, by rfl⟩ : syracuseStep 2968907 = 4453361) B4453361
theorem B1979271 : Blo 1977435 1979271 := bstep (se 1 (by rfl) ⟨1484453, by rfl⟩ : syracuseStep 1979271 = 2968907) B2968907
theorem B2226685 : Blo 1977435 2226685 := bbase (se 3 (by rfl) ⟨417503, by rfl⟩ : syracuseStep 2226685 = 835007) (by norm_num)
theorem B2968913 : Blo 1977435 2968913 := bstep (se 2 (by rfl) ⟨1113342, by rfl⟩ : syracuseStep 2968913 = 2226685) B2226685
theorem B1979275 : Blo 1977435 1979275 := bstep (se 1 (by rfl) ⟨1484456, by rfl⟩ : syracuseStep 1979275 = 2968913) B2968913
theorem B6680069 : Blo 1977435 6680069 := bbase (se 4 (by rfl) ⟨626256, by rfl⟩ : syracuseStep 6680069 = 1252513) (by norm_num)
theorem B4453379 : Blo 1977435 4453379 := bstep (se 1 (by rfl) ⟨3340034, by rfl⟩ : syracuseStep 4453379 = 6680069) B6680069
theorem B2968919 : Blo 1977435 2968919 := bstep (se 1 (by rfl) ⟨2226689, by rfl⟩ : syracuseStep 2968919 = 4453379) B4453379
theorem B1979279 : Blo 1977435 1979279 := bstep (se 1 (by rfl) ⟨1484459, by rfl⟩ : syracuseStep 1979279 = 2968919) B2968919
theorem B2968925 : Blo 1977435 2968925 := bbase (se 3 (by rfl) ⟨556673, by rfl⟩ : syracuseStep 2968925 = 1113347) (by norm_num)
theorem B1979283 : Blo 1977435 1979283 := bstep (se 1 (by rfl) ⟨1484462, by rfl⟩ : syracuseStep 1979283 = 2968925) B2968925
theorem B4453397 : Blo 1977435 4453397 := bbase (se 6 (by rfl) ⟨104376, by rfl⟩ : syracuseStep 4453397 = 208753) (by norm_num)
theorem B2968931 : Blo 1977435 2968931 := bstep (se 1 (by rfl) ⟨2226698, by rfl⟩ : syracuseStep 2968931 = 4453397) B4453397
theorem B1979287 : Blo 1977435 1979287 := bstep (se 1 (by rfl) ⟨1484465, by rfl⟩ : syracuseStep 1979287 = 2968931) B2968931
theorem B7515125 : Blo 1977435 7515125 := bbase (se 5 (by rfl) ⟨352271, by rfl⟩ : syracuseStep 7515125 = 704543) (by norm_num)
theorem B5010083 : Blo 1977435 5010083 := bstep (se 1 (by rfl) ⟨3757562, by rfl⟩ : syracuseStep 5010083 = 7515125) B7515125
theorem B3340055 : Blo 1977435 3340055 := bstep (se 1 (by rfl) ⟨2505041, by rfl⟩ : syracuseStep 3340055 = 5010083) B5010083
theorem B2226703 : Blo 1977435 2226703 := bstep (se 1 (by rfl) ⟨1670027, by rfl⟩ : syracuseStep 2226703 = 3340055) B3340055
theorem B2968937 : Blo 1977435 2968937 := bstep (se 2 (by rfl) ⟨1113351, by rfl⟩ : syracuseStep 2968937 = 2226703) B2226703
theorem B1979291 : Blo 1977435 1979291 := bstep (se 1 (by rfl) ⟨1484468, by rfl⟩ : syracuseStep 1979291 = 2968937) B2968937
theorem B2113633 : Blo 1977435 2113633 := bbase (se 2 (by rfl) ⟨792612, by rfl⟩ : syracuseStep 2113633 = 1585225) (by norm_num)
theorem B11272709 : Blo 1977435 11272709 := bstep (se 4 (by rfl) ⟨1056816, by rfl⟩ : syracuseStep 11272709 = 2113633) B2113633
theorem B7515139 : Blo 1977435 7515139 := bstep (se 1 (by rfl) ⟨5636354, by rfl⟩ : syracuseStep 7515139 = 11272709) B11272709
theorem B10020185 : Blo 1977435 10020185 := bstep (se 2 (by rfl) ⟨3757569, by rfl⟩ : syracuseStep 10020185 = 7515139) B7515139
theorem B6680123 : Blo 1977435 6680123 := bstep (se 1 (by rfl) ⟨5010092, by rfl⟩ : syracuseStep 6680123 = 10020185) B10020185
theorem B4453415 : Blo 1977435 4453415 := bstep (se 1 (by rfl) ⟨3340061, by rfl⟩ : syracuseStep 4453415 = 6680123) B6680123
theorem B2968943 : Blo 1977435 2968943 := bstep (se 1 (by rfl) ⟨2226707, by rfl⟩ : syracuseStep 2968943 = 4453415) B4453415
theorem B1979295 : Blo 1977435 1979295 := bstep (se 1 (by rfl) ⟨1484471, by rfl⟩ : syracuseStep 1979295 = 2968943) B2968943
theorem B2968949 : Blo 1977435 2968949 := bbase (se 5 (by rfl) ⟨139169, by rfl⟩ : syracuseStep 2968949 = 278339) (by norm_num)
theorem B1979299 : Blo 1977435 1979299 := bstep (se 1 (by rfl) ⟨1484474, by rfl⟩ : syracuseStep 1979299 = 2968949) B2968949
theorem B2818189 : Blo 1977435 2818189 := bbase (se 3 (by rfl) ⟨528410, by rfl⟩ : syracuseStep 2818189 = 1056821) (by norm_num)
theorem B3757585 : Blo 1977435 3757585 := bstep (se 2 (by rfl) ⟨1409094, by rfl⟩ : syracuseStep 3757585 = 2818189) B2818189
theorem B5010113 : Blo 1977435 5010113 := bstep (se 2 (by rfl) ⟨1878792, by rfl⟩ : syracuseStep 5010113 = 3757585) B3757585
theorem B3340075 : Blo 1977435 3340075 := bstep (se 1 (by rfl) ⟨2505056, by rfl⟩ : syracuseStep 3340075 = 5010113) B5010113
theorem B4453433 : Blo 1977435 4453433 := bstep (se 2 (by rfl) ⟨1670037, by rfl⟩ : syracuseStep 4453433 = 3340075) B3340075
theorem B2968955 : Blo 1977435 2968955 := bstep (se 1 (by rfl) ⟨2226716, by rfl⟩ : syracuseStep 2968955 = 4453433) B4453433
theorem B1979303 : Blo 1977435 1979303 := bstep (se 1 (by rfl) ⟨1484477, by rfl⟩ : syracuseStep 1979303 = 2968955) B2968955
theorem B2226721 : Blo 1977435 2226721 := bbase (se 2 (by rfl) ⟨835020, by rfl⟩ : syracuseStep 2226721 = 1670041) (by norm_num)
theorem B2968961 : Blo 1977435 2968961 := bstep (se 2 (by rfl) ⟨1113360, by rfl⟩ : syracuseStep 2968961 = 2226721) B2226721
theorem B1979307 : Blo 1977435 1979307 := bstep (se 1 (by rfl) ⟨1484480, by rfl⟩ : syracuseStep 1979307 = 2968961) B2968961
theorem B5010133 : Blo 1977435 5010133 := bbase (se 7 (by rfl) ⟨58712, by rfl⟩ : syracuseStep 5010133 = 117425) (by norm_num)
theorem B6680177 : Blo 1977435 6680177 := bstep (se 2 (by rfl) ⟨2505066, by rfl⟩ : syracuseStep 6680177 = 5010133) B5010133
theorem B4453451 : Blo 1977435 4453451 := bstep (se 1 (by rfl) ⟨3340088, by rfl⟩ : syracuseStep 4453451 = 6680177) B6680177
theorem B2968967 : Blo 1977435 2968967 := bstep (se 1 (by rfl) ⟨2226725, by rfl⟩ : syracuseStep 2968967 = 4453451) B4453451
theorem B1979311 : Blo 1977435 1979311 := bstep (se 1 (by rfl) ⟨1484483, by rfl⟩ : syracuseStep 1979311 = 2968967) B2968967
theorem B2968973 : Blo 1977435 2968973 := bbase (se 3 (by rfl) ⟨556682, by rfl⟩ : syracuseStep 2968973 = 1113365) (by norm_num)
theorem B1979315 : Blo 1977435 1979315 := bstep (se 1 (by rfl) ⟨1484486, by rfl⟩ : syracuseStep 1979315 = 2968973) B2968973
theorem B4453469 : Blo 1977435 4453469 := bbase (se 3 (by rfl) ⟨835025, by rfl⟩ : syracuseStep 4453469 = 1670051) (by norm_num)
theorem B2968979 : Blo 1977435 2968979 := bstep (se 1 (by rfl) ⟨2226734, by rfl⟩ : syracuseStep 2968979 = 4453469) B4453469
theorem B1979319 : Blo 1977435 1979319 := bstep (se 1 (by rfl) ⟨1484489, by rfl⟩ : syracuseStep 1979319 = 2968979) B2968979
theorem B3340109 : Blo 1977435 3340109 := bbase (se 3 (by rfl) ⟨626270, by rfl⟩ : syracuseStep 3340109 = 1252541) (by norm_num)
theorem B2226739 : Blo 1977435 2226739 := bstep (se 1 (by rfl) ⟨1670054, by rfl⟩ : syracuseStep 2226739 = 3340109) B3340109
theorem B2968985 : Blo 1977435 2968985 := bstep (se 2 (by rfl) ⟨1113369, by rfl⟩ : syracuseStep 2968985 = 2226739) B2226739
theorem B1979323 : Blo 1977435 1979323 := bstep (se 1 (by rfl) ⟨1484492, by rfl⟩ : syracuseStep 1979323 = 2968985) B2968985
theorem B7617797 : Blo 1977435 7617797 := bbase (se 4 (by rfl) ⟨714168, by rfl⟩ : syracuseStep 7617797 = 1428337) (by norm_num)
theorem B5078531 : Blo 1977435 5078531 := bstep (se 1 (by rfl) ⟨3808898, by rfl⟩ : syracuseStep 5078531 = 7617797) B7617797
theorem B3385687 : Blo 1977435 3385687 := bstep (se 1 (by rfl) ⟨2539265, by rfl⟩ : syracuseStep 3385687 = 5078531) B5078531
theorem B4514249 : Blo 1977435 4514249 := bstep (se 2 (by rfl) ⟨1692843, by rfl⟩ : syracuseStep 4514249 = 3385687) B3385687
theorem B12037997 : Blo 1977435 12037997 := bstep (se 3 (by rfl) ⟨2257124, by rfl⟩ : syracuseStep 12037997 = 4514249) B4514249
theorem B8025331 : Blo 1977435 8025331 := bstep (se 1 (by rfl) ⟨6018998, by rfl⟩ : syracuseStep 8025331 = 12037997) B12037997
theorem B10700441 : Blo 1977435 10700441 := bstep (se 2 (by rfl) ⟨4012665, by rfl⟩ : syracuseStep 10700441 = 8025331) B8025331
theorem B7133627 : Blo 1977435 7133627 := bstep (se 1 (by rfl) ⟨5350220, by rfl⟩ : syracuseStep 7133627 = 10700441) B10700441
theorem B19023005 : Blo 1977435 19023005 := bstep (se 3 (by rfl) ⟨3566813, by rfl⟩ : syracuseStep 19023005 = 7133627) B7133627
theorem B12682003 : Blo 1977435 12682003 := bstep (se 1 (by rfl) ⟨9511502, by rfl⟩ : syracuseStep 12682003 = 19023005) B19023005
theorem B16909337 : Blo 1977435 16909337 := bstep (se 2 (by rfl) ⟨6341001, by rfl⟩ : syracuseStep 16909337 = 12682003) B12682003
theorem B11272891 : Blo 1977435 11272891 := bstep (se 1 (by rfl) ⟨8454668, by rfl⟩ : syracuseStep 11272891 = 16909337) B16909337
theorem B15030521 : Blo 1977435 15030521 := bstep (se 2 (by rfl) ⟨5636445, by rfl⟩ : syracuseStep 15030521 = 11272891) B11272891
theorem B10020347 : Blo 1977435 10020347 := bstep (se 1 (by rfl) ⟨7515260, by rfl⟩ : syracuseStep 10020347 = 15030521) B15030521
theorem B6680231 : Blo 1977435 6680231 := bstep (se 1 (by rfl) ⟨5010173, by rfl⟩ : syracuseStep 6680231 = 10020347) B10020347
theorem B4453487 : Blo 1977435 4453487 := bstep (se 1 (by rfl) ⟨3340115, by rfl⟩ : syracuseStep 4453487 = 6680231) B6680231
theorem B2968991 : Blo 1977435 2968991 := bstep (se 1 (by rfl) ⟨2226743, by rfl⟩ : syracuseStep 2968991 = 4453487) B4453487
theorem B1979327 : Blo 1977435 1979327 := bstep (se 1 (by rfl) ⟨1484495, by rfl⟩ : syracuseStep 1979327 = 2968991) B2968991
theorem B2968997 : Blo 1977435 2968997 := bbase (se 4 (by rfl) ⟨278343, by rfl⟩ : syracuseStep 2968997 = 556687) (by norm_num)
theorem B1979331 : Blo 1977435 1979331 := bstep (se 1 (by rfl) ⟨1484498, by rfl⟩ : syracuseStep 1979331 = 2968997) B2968997
theorem B2505097 : Blo 1977435 2505097 := bbase (se 2 (by rfl) ⟨939411, by rfl⟩ : syracuseStep 2505097 = 1878823) (by norm_num)
theorem B3340129 : Blo 1977435 3340129 := bstep (se 2 (by rfl) ⟨1252548, by rfl⟩ : syracuseStep 3340129 = 2505097) B2505097
theorem B4453505 : Blo 1977435 4453505 := bstep (se 2 (by rfl) ⟨1670064, by rfl⟩ : syracuseStep 4453505 = 3340129) B3340129
theorem B2969003 : Blo 1977435 2969003 := bstep (se 1 (by rfl) ⟨2226752, by rfl⟩ : syracuseStep 2969003 = 4453505) B4453505
theorem B1979335 : Blo 1977435 1979335 := bstep (se 1 (by rfl) ⟨1484501, by rfl⟩ : syracuseStep 1979335 = 2969003) B2969003
theorem B2226757 : Blo 1977435 2226757 := bbase (se 4 (by rfl) ⟨208758, by rfl⟩ : syracuseStep 2226757 = 417517) (by norm_num)
theorem B2969009 : Blo 1977435 2969009 := bstep (se 2 (by rfl) ⟨1113378, by rfl⟩ : syracuseStep 2969009 = 2226757) B2226757
theorem B1979339 : Blo 1977435 1979339 := bstep (se 1 (by rfl) ⟨1484504, by rfl⟩ : syracuseStep 1979339 = 2969009) B2969009
theorem B3757661 : Blo 1977435 3757661 := bbase (se 3 (by rfl) ⟨704561, by rfl⟩ : syracuseStep 3757661 = 1409123) (by norm_num)
theorem B2505107 : Blo 1977435 2505107 := bstep (se 1 (by rfl) ⟨1878830, by rfl⟩ : syracuseStep 2505107 = 3757661) B3757661
theorem B6680285 : Blo 1977435 6680285 := bstep (se 3 (by rfl) ⟨1252553, by rfl⟩ : syracuseStep 6680285 = 2505107) B2505107
theorem B4453523 : Blo 1977435 4453523 := bstep (se 1 (by rfl) ⟨3340142, by rfl⟩ : syracuseStep 4453523 = 6680285) B6680285
theorem B2969015 : Blo 1977435 2969015 := bstep (se 1 (by rfl) ⟨2226761, by rfl⟩ : syracuseStep 2969015 = 4453523) B4453523
theorem B1979343 : Blo 1977435 1979343 := bstep (se 1 (by rfl) ⟨1484507, by rfl⟩ : syracuseStep 1979343 = 2969015) B2969015
theorem B2969021 : Blo 1977435 2969021 := bbase (se 3 (by rfl) ⟨556691, by rfl⟩ : syracuseStep 2969021 = 1113383) (by norm_num)
theorem B1979347 : Blo 1977435 1979347 := bstep (se 1 (by rfl) ⟨1484510, by rfl⟩ : syracuseStep 1979347 = 2969021) B2969021
theorem B4453541 : Blo 1977435 4453541 := bbase (se 4 (by rfl) ⟨417519, by rfl⟩ : syracuseStep 4453541 = 835039) (by norm_num)
theorem B2969027 : Blo 1977435 2969027 := bstep (se 1 (by rfl) ⟨2226770, by rfl⟩ : syracuseStep 2969027 = 4453541) B4453541
theorem B1979351 : Blo 1977435 1979351 := bstep (se 1 (by rfl) ⟨1484513, by rfl⟩ : syracuseStep 1979351 = 2969027) B2969027
theorem B5010245 : Blo 1977435 5010245 := bbase (se 4 (by rfl) ⟨469710, by rfl⟩ : syracuseStep 5010245 = 939421) (by norm_num)
theorem B3340163 : Blo 1977435 3340163 := bstep (se 1 (by rfl) ⟨2505122, by rfl⟩ : syracuseStep 3340163 = 5010245) B5010245
theorem B2226775 : Blo 1977435 2226775 := bstep (se 1 (by rfl) ⟨1670081, by rfl⟩ : syracuseStep 2226775 = 3340163) B3340163
theorem B2969033 : Blo 1977435 2969033 := bstep (se 2 (by rfl) ⟨1113387, by rfl⟩ : syracuseStep 2969033 = 2226775) B2226775
theorem B1979355 : Blo 1977435 1979355 := bstep (se 1 (by rfl) ⟨1484516, by rfl⟩ : syracuseStep 1979355 = 2969033) B2969033
theorem B4755829 : Blo 1977435 4755829 := bbase (se 5 (by rfl) ⟨222929, by rfl⟩ : syracuseStep 4755829 = 445859) (by norm_num)
theorem B6341105 : Blo 1977435 6341105 := bstep (se 2 (by rfl) ⟨2377914, by rfl⟩ : syracuseStep 6341105 = 4755829) B4755829
theorem B4227403 : Blo 1977435 4227403 := bstep (se 1 (by rfl) ⟨3170552, by rfl⟩ : syracuseStep 4227403 = 6341105) B6341105
theorem B5636537 : Blo 1977435 5636537 := bstep (se 2 (by rfl) ⟨2113701, by rfl⟩ : syracuseStep 5636537 = 4227403) B4227403
theorem B3757691 : Blo 1977435 3757691 := bstep (se 1 (by rfl) ⟨2818268, by rfl⟩ : syracuseStep 3757691 = 5636537) B5636537
theorem B10020509 : Blo 1977435 10020509 := bstep (se 3 (by rfl) ⟨1878845, by rfl⟩ : syracuseStep 10020509 = 3757691) B3757691
theorem B6680339 : Blo 1977435 6680339 := bstep (se 1 (by rfl) ⟨5010254, by rfl⟩ : syracuseStep 6680339 = 10020509) B10020509
theorem B4453559 : Blo 1977435 4453559 := bstep (se 1 (by rfl) ⟨3340169, by rfl⟩ : syracuseStep 4453559 = 6680339) B6680339
theorem B2969039 : Blo 1977435 2969039 := bstep (se 1 (by rfl) ⟨2226779, by rfl⟩ : syracuseStep 2969039 = 4453559) B4453559
theorem B1979359 : Blo 1977435 1979359 := bstep (se 1 (by rfl) ⟨1484519, by rfl⟩ : syracuseStep 1979359 = 2969039) B2969039
theorem B2969045 : Blo 1977435 2969045 := bbase (se 7 (by rfl) ⟨34793, by rfl⟩ : syracuseStep 2969045 = 69587) (by norm_num)
theorem B1979363 : Blo 1977435 1979363 := bstep (se 1 (by rfl) ⟨1484522, by rfl⟩ : syracuseStep 1979363 = 2969045) B2969045
theorem B7515413 : Blo 1977435 7515413 := bbase (se 6 (by rfl) ⟨176142, by rfl⟩ : syracuseStep 7515413 = 352285) (by norm_num)
theorem B5010275 : Blo 1977435 5010275 := bstep (se 1 (by rfl) ⟨3757706, by rfl⟩ : syracuseStep 5010275 = 7515413) B7515413
theorem B3340183 : Blo 1977435 3340183 := bstep (se 1 (by rfl) ⟨2505137, by rfl⟩ : syracuseStep 3340183 = 5010275) B5010275
theorem B4453577 : Blo 1977435 4453577 := bstep (se 2 (by rfl) ⟨1670091, by rfl⟩ : syracuseStep 4453577 = 3340183) B3340183
theorem B2969051 : Blo 1977435 2969051 := bstep (se 1 (by rfl) ⟨2226788, by rfl⟩ : syracuseStep 2969051 = 4453577) B4453577
theorem B1979367 : Blo 1977435 1979367 := bstep (se 1 (by rfl) ⟨1484525, by rfl⟩ : syracuseStep 1979367 = 2969051) B2969051
theorem B2226793 : Blo 1977435 2226793 := bbase (se 2 (by rfl) ⟨835047, by rfl⟩ : syracuseStep 2226793 = 1670095) (by norm_num)
theorem B2969057 : Blo 1977435 2969057 := bstep (se 2 (by rfl) ⟨1113396, by rfl⟩ : syracuseStep 2969057 = 2226793) B2226793
theorem B1979371 : Blo 1977435 1979371 := bstep (se 1 (by rfl) ⟨1484528, by rfl⟩ : syracuseStep 1979371 = 2969057) B2969057
theorem B4227437 : Blo 1977435 4227437 := bbase (se 3 (by rfl) ⟨792644, by rfl⟩ : syracuseStep 4227437 = 1585289) (by norm_num)
theorem B11273165 : Blo 1977435 11273165 := bstep (se 3 (by rfl) ⟨2113718, by rfl⟩ : syracuseStep 11273165 = 4227437) B4227437
theorem B7515443 : Blo 1977435 7515443 := bstep (se 1 (by rfl) ⟨5636582, by rfl⟩ : syracuseStep 7515443 = 11273165) B11273165
theorem B5010295 : Blo 1977435 5010295 := bstep (se 1 (by rfl) ⟨3757721, by rfl⟩ : syracuseStep 5010295 = 7515443) B7515443
theorem B6680393 : Blo 1977435 6680393 := bstep (se 2 (by rfl) ⟨2505147, by rfl⟩ : syracuseStep 6680393 = 5010295) B5010295
theorem B4453595 : Blo 1977435 4453595 := bstep (se 1 (by rfl) ⟨3340196, by rfl⟩ : syracuseStep 4453595 = 6680393) B6680393
theorem B2969063 : Blo 1977435 2969063 := bstep (se 1 (by rfl) ⟨2226797, by rfl⟩ : syracuseStep 2969063 = 4453595) B4453595
theorem B1979375 : Blo 1977435 1979375 := bstep (se 1 (by rfl) ⟨1484531, by rfl⟩ : syracuseStep 1979375 = 2969063) B2969063
theorem B2969069 : Blo 1977435 2969069 := bbase (se 3 (by rfl) ⟨556700, by rfl⟩ : syracuseStep 2969069 = 1113401) (by norm_num)
theorem B1979379 : Blo 1977435 1979379 := bstep (se 1 (by rfl) ⟨1484534, by rfl⟩ : syracuseStep 1979379 = 2969069) B2969069
theorem B4453613 : Blo 1977435 4453613 := bbase (se 3 (by rfl) ⟨835052, by rfl⟩ : syracuseStep 4453613 = 1670105) (by norm_num)
theorem B2969075 : Blo 1977435 2969075 := bstep (se 1 (by rfl) ⟨2226806, by rfl⟩ : syracuseStep 2969075 = 4453613) B4453613
theorem B1979383 : Blo 1977435 1979383 := bstep (se 1 (by rfl) ⟨1484537, by rfl⟩ : syracuseStep 1979383 = 2969075) B2969075
theorem B2818309 : Blo 1977435 2818309 := bbase (se 4 (by rfl) ⟨264216, by rfl⟩ : syracuseStep 2818309 = 528433) (by norm_num)
theorem B3757745 : Blo 1977435 3757745 := bstep (se 2 (by rfl) ⟨1409154, by rfl⟩ : syracuseStep 3757745 = 2818309) B2818309
theorem B2505163 : Blo 1977435 2505163 := bstep (se 1 (by rfl) ⟨1878872, by rfl⟩ : syracuseStep 2505163 = 3757745) B3757745
theorem B3340217 : Blo 1977435 3340217 := bstep (se 2 (by rfl) ⟨1252581, by rfl⟩ : syracuseStep 3340217 = 2505163) B2505163
theorem B2226811 : Blo 1977435 2226811 := bstep (se 1 (by rfl) ⟨1670108, by rfl⟩ : syracuseStep 2226811 = 3340217) B3340217
theorem B2969081 : Blo 1977435 2969081 := bstep (se 2 (by rfl) ⟨1113405, by rfl⟩ : syracuseStep 2969081 = 2226811) B2226811
theorem B1979387 : Blo 1977435 1979387 := bstep (se 1 (by rfl) ⟨1484540, by rfl⟩ : syracuseStep 1979387 = 2969081) B2969081
theorem B4575989 : Blo 1977435 4575989 := bbase (se 5 (by rfl) ⟨214499, by rfl⟩ : syracuseStep 4575989 = 428999) (by norm_num)
theorem B3050659 : Blo 1977435 3050659 := bstep (se 1 (by rfl) ⟨2287994, by rfl⟩ : syracuseStep 3050659 = 4575989) B4575989
theorem B4067545 : Blo 1977435 4067545 := bstep (se 2 (by rfl) ⟨1525329, by rfl⟩ : syracuseStep 4067545 = 3050659) B3050659
theorem B5423393 : Blo 1977435 5423393 := bstep (se 2 (by rfl) ⟨2033772, by rfl⟩ : syracuseStep 5423393 = 4067545) B4067545
theorem B14462381 : Blo 1977435 14462381 := bstep (se 3 (by rfl) ⟨2711696, by rfl⟩ : syracuseStep 14462381 = 5423393) B5423393
theorem B9641587 : Blo 1977435 9641587 := bstep (se 1 (by rfl) ⟨7231190, by rfl⟩ : syracuseStep 9641587 = 14462381) B14462381
theorem B12855449 : Blo 1977435 12855449 := bstep (se 2 (by rfl) ⟨4820793, by rfl⟩ : syracuseStep 12855449 = 9641587) B9641587
theorem B8570299 : Blo 1977435 8570299 := bstep (se 1 (by rfl) ⟨6427724, by rfl⟩ : syracuseStep 8570299 = 12855449) B12855449
theorem B11427065 : Blo 1977435 11427065 := bstep (se 2 (by rfl) ⟨4285149, by rfl⟩ : syracuseStep 11427065 = 8570299) B8570299
theorem B7618043 : Blo 1977435 7618043 := bstep (se 1 (by rfl) ⟨5713532, by rfl⟩ : syracuseStep 7618043 = 11427065) B11427065
theorem B5078695 : Blo 1977435 5078695 := bstep (se 1 (by rfl) ⟨3809021, by rfl⟩ : syracuseStep 5078695 = 7618043) B7618043
theorem B6771593 : Blo 1977435 6771593 := bstep (se 2 (by rfl) ⟨2539347, by rfl⟩ : syracuseStep 6771593 = 5078695) B5078695
theorem B4514395 : Blo 1977435 4514395 := bstep (se 1 (by rfl) ⟨3385796, by rfl⟩ : syracuseStep 4514395 = 6771593) B6771593
theorem B6019193 : Blo 1977435 6019193 := bstep (se 2 (by rfl) ⟨2257197, by rfl⟩ : syracuseStep 6019193 = 4514395) B4514395
theorem B4012795 : Blo 1977435 4012795 := bstep (se 1 (by rfl) ⟨3009596, by rfl⟩ : syracuseStep 4012795 = 6019193) B6019193
theorem B5350393 : Blo 1977435 5350393 := bstep (se 2 (by rfl) ⟨2006397, by rfl⟩ : syracuseStep 5350393 = 4012795) B4012795
theorem B28535429 : Blo 1977435 28535429 := bstep (se 4 (by rfl) ⟨2675196, by rfl⟩ : syracuseStep 28535429 = 5350393) B5350393
theorem B76094477 : Blo 1977435 76094477 := bstep (se 3 (by rfl) ⟨14267714, by rfl⟩ : syracuseStep 76094477 = 28535429) B28535429
theorem B50729651 : Blo 1977435 50729651 := bstep (se 1 (by rfl) ⟨38047238, by rfl⟩ : syracuseStep 50729651 = 76094477) B76094477
theorem B33819767 : Blo 1977435 33819767 := bstep (se 1 (by rfl) ⟨25364825, by rfl⟩ : syracuseStep 33819767 = 50729651) B50729651
theorem B22546511 : Blo 1977435 22546511 := bstep (se 1 (by rfl) ⟨16909883, by rfl⟩ : syracuseStep 22546511 = 33819767) B33819767
theorem B15031007 : Blo 1977435 15031007 := bstep (se 1 (by rfl) ⟨11273255, by rfl⟩ : syracuseStep 15031007 = 22546511) B22546511
theorem B10020671 : Blo 1977435 10020671 := bstep (se 1 (by rfl) ⟨7515503, by rfl⟩ : syracuseStep 10020671 = 15031007) B15031007
theorem B6680447 : Blo 1977435 6680447 := bstep (se 1 (by rfl) ⟨5010335, by rfl⟩ : syracuseStep 6680447 = 10020671) B10020671
theorem B4453631 : Blo 1977435 4453631 := bstep (se 1 (by rfl) ⟨3340223, by rfl⟩ : syracuseStep 4453631 = 6680447) B6680447
theorem B2969087 : Blo 1977435 2969087 := bstep (se 1 (by rfl) ⟨2226815, by rfl⟩ : syracuseStep 2969087 = 4453631) B4453631
theorem B1979391 : Blo 1977435 1979391 := bstep (se 1 (by rfl) ⟨1484543, by rfl⟩ : syracuseStep 1979391 = 2969087) B2969087
theorem B2969093 : Blo 1977435 2969093 := bbase (se 4 (by rfl) ⟨278352, by rfl⟩ : syracuseStep 2969093 = 556705) (by norm_num)
theorem B1979395 : Blo 1977435 1979395 := bstep (se 1 (by rfl) ⟨1484546, by rfl⟩ : syracuseStep 1979395 = 2969093) B2969093
theorem B3340237 : Blo 1977435 3340237 := bbase (se 3 (by rfl) ⟨626294, by rfl⟩ : syracuseStep 3340237 = 1252589) (by norm_num)
theorem B4453649 : Blo 1977435 4453649 := bstep (se 2 (by rfl) ⟨1670118, by rfl⟩ : syracuseStep 4453649 = 3340237) B3340237
theorem B2969099 : Blo 1977435 2969099 := bstep (se 1 (by rfl) ⟨2226824, by rfl⟩ : syracuseStep 2969099 = 4453649) B4453649
theorem B1979399 : Blo 1977435 1979399 := bstep (se 1 (by rfl) ⟨1484549, by rfl⟩ : syracuseStep 1979399 = 2969099) B2969099
theorem B2226829 : Blo 1977435 2226829 := bbase (se 3 (by rfl) ⟨417530, by rfl⟩ : syracuseStep 2226829 = 835061) (by norm_num)
theorem B2969105 : Blo 1977435 2969105 := bstep (se 2 (by rfl) ⟨1113414, by rfl⟩ : syracuseStep 2969105 = 2226829) B2226829
theorem B1979403 : Blo 1977435 1979403 := bstep (se 1 (by rfl) ⟨1484552, by rfl⟩ : syracuseStep 1979403 = 2969105) B2969105
theorem B6680501 : Blo 1977435 6680501 := bbase (se 5 (by rfl) ⟨313148, by rfl⟩ : syracuseStep 6680501 = 626297) (by norm_num)
theorem B4453667 : Blo 1977435 4453667 := bstep (se 1 (by rfl) ⟨3340250, by rfl⟩ : syracuseStep 4453667 = 6680501) B6680501
theorem B2969111 : Blo 1977435 2969111 := bstep (se 1 (by rfl) ⟨2226833, by rfl⟩ : syracuseStep 2969111 = 4453667) B4453667
theorem B1979407 : Blo 1977435 1979407 := bstep (se 1 (by rfl) ⟨1484555, by rfl⟩ : syracuseStep 1979407 = 2969111) B2969111
theorem B2969117 : Blo 1977435 2969117 := bbase (se 3 (by rfl) ⟨556709, by rfl⟩ : syracuseStep 2969117 = 1113419) (by norm_num)
theorem B1979411 : Blo 1977435 1979411 := bstep (se 1 (by rfl) ⟨1484558, by rfl⟩ : syracuseStep 1979411 = 2969117) B2969117
theorem B4453685 : Blo 1977435 4453685 := bbase (se 5 (by rfl) ⟨208766, by rfl⟩ : syracuseStep 4453685 = 417533) (by norm_num)
theorem B2969123 : Blo 1977435 2969123 := bstep (se 1 (by rfl) ⟨2226842, by rfl⟩ : syracuseStep 2969123 = 4453685) B4453685
theorem B1979415 : Blo 1977435 1979415 := bstep (se 1 (by rfl) ⟨1484561, by rfl⟩ : syracuseStep 1979415 = 2969123) B2969123
theorem B19023893 : Blo 1977435 19023893 := bbase (se 6 (by rfl) ⟨445872, by rfl⟩ : syracuseStep 19023893 = 891745) (by norm_num)
theorem B12682595 : Blo 1977435 12682595 := bstep (se 1 (by rfl) ⟨9511946, by rfl⟩ : syracuseStep 12682595 = 19023893) B19023893
theorem B8455063 : Blo 1977435 8455063 := bstep (se 1 (by rfl) ⟨6341297, by rfl⟩ : syracuseStep 8455063 = 12682595) B12682595
theorem B11273417 : Blo 1977435 11273417 := bstep (se 2 (by rfl) ⟨4227531, by rfl⟩ : syracuseStep 11273417 = 8455063) B8455063
theorem B7515611 : Blo 1977435 7515611 := bstep (se 1 (by rfl) ⟨5636708, by rfl⟩ : syracuseStep 7515611 = 11273417) B11273417
theorem B5010407 : Blo 1977435 5010407 := bstep (se 1 (by rfl) ⟨3757805, by rfl⟩ : syracuseStep 5010407 = 7515611) B7515611
theorem B3340271 : Blo 1977435 3340271 := bstep (se 1 (by rfl) ⟨2505203, by rfl⟩ : syracuseStep 3340271 = 5010407) B5010407
theorem B2226847 : Blo 1977435 2226847 := bstep (se 1 (by rfl) ⟨1670135, by rfl⟩ : syracuseStep 2226847 = 3340271) B3340271
theorem B2969129 : Blo 1977435 2969129 := bstep (se 2 (by rfl) ⟨1113423, by rfl⟩ : syracuseStep 2969129 = 2226847) B2226847
theorem B1979419 : Blo 1977435 1979419 := bstep (se 1 (by rfl) ⟨1484564, by rfl⟩ : syracuseStep 1979419 = 2969129) B2969129
theorem B12038581 : Blo 1977435 12038581 := bbase (se 5 (by rfl) ⟨564308, by rfl⟩ : syracuseStep 12038581 = 1128617) (by norm_num)
theorem B16051441 : Blo 1977435 16051441 := bstep (se 2 (by rfl) ⟨6019290, by rfl⟩ : syracuseStep 16051441 = 12038581) B12038581
theorem B21401921 : Blo 1977435 21401921 := bstep (se 2 (by rfl) ⟨8025720, by rfl⟩ : syracuseStep 21401921 = 16051441) B16051441
theorem B14267947 : Blo 1977435 14267947 := bstep (se 1 (by rfl) ⟨10700960, by rfl⟩ : syracuseStep 14267947 = 21401921) B21401921
theorem B19023929 : Blo 1977435 19023929 := bstep (se 2 (by rfl) ⟨7133973, by rfl⟩ : syracuseStep 19023929 = 14267947) B14267947
theorem B12682619 : Blo 1977435 12682619 := bstep (se 1 (by rfl) ⟨9511964, by rfl⟩ : syracuseStep 12682619 = 19023929) B19023929
theorem B8455079 : Blo 1977435 8455079 := bstep (se 1 (by rfl) ⟨6341309, by rfl⟩ : syracuseStep 8455079 = 12682619) B12682619
theorem B5636719 : Blo 1977435 5636719 := bstep (se 1 (by rfl) ⟨4227539, by rfl⟩ : syracuseStep 5636719 = 8455079) B8455079
theorem B7515625 : Blo 1977435 7515625 := bstep (se 2 (by rfl) ⟨2818359, by rfl⟩ : syracuseStep 7515625 = 5636719) B5636719
theorem B10020833 : Blo 1977435 10020833 := bstep (se 2 (by rfl) ⟨3757812, by rfl⟩ : syracuseStep 10020833 = 7515625) B7515625
theorem B6680555 : Blo 1977435 6680555 := bstep (se 1 (by rfl) ⟨5010416, by rfl⟩ : syracuseStep 6680555 = 10020833) B10020833
theorem B4453703 : Blo 1977435 4453703 := bstep (se 1 (by rfl) ⟨3340277, by rfl⟩ : syracuseStep 4453703 = 6680555) B6680555
theorem B2969135 : Blo 1977435 2969135 := bstep (se 1 (by rfl) ⟨2226851, by rfl⟩ : syracuseStep 2969135 = 4453703) B4453703
theorem B1979423 : Blo 1977435 1979423 := bstep (se 1 (by rfl) ⟨1484567, by rfl⟩ : syracuseStep 1979423 = 2969135) B2969135
theorem B2969141 : Blo 1977435 2969141 := bbase (se 5 (by rfl) ⟨139178, by rfl⟩ : syracuseStep 2969141 = 278357) (by norm_num)
theorem B1979427 : Blo 1977435 1979427 := bstep (se 1 (by rfl) ⟨1484570, by rfl⟩ : syracuseStep 1979427 = 2969141) B2969141
theorem B5010437 : Blo 1977435 5010437 := bbase (se 4 (by rfl) ⟨469728, by rfl⟩ : syracuseStep 5010437 = 939457) (by norm_num)
theorem B3340291 : Blo 1977435 3340291 := bstep (se 1 (by rfl) ⟨2505218, by rfl⟩ : syracuseStep 3340291 = 5010437) B5010437
theorem B4453721 : Blo 1977435 4453721 := bstep (se 2 (by rfl) ⟨1670145, by rfl⟩ : syracuseStep 4453721 = 3340291) B3340291
theorem B2969147 : Blo 1977435 2969147 := bstep (se 1 (by rfl) ⟨2226860, by rfl⟩ : syracuseStep 2969147 = 4453721) B4453721
theorem B1979431 : Blo 1977435 1979431 := bstep (se 1 (by rfl) ⟨1484573, by rfl⟩ : syracuseStep 1979431 = 2969147) B2969147
theorem B2226865 : Blo 1977435 2226865 := bbase (se 2 (by rfl) ⟨835074, by rfl⟩ : syracuseStep 2226865 = 1670149) (by norm_num)
theorem B2969153 : Blo 1977435 2969153 := bstep (se 2 (by rfl) ⟨1113432, by rfl⟩ : syracuseStep 2969153 = 2226865) B2226865
theorem B1979435 : Blo 1977435 1979435 := bstep (se 1 (by rfl) ⟨1484576, by rfl⟩ : syracuseStep 1979435 = 2969153) B2969153
theorem C0 (j : ℕ) (h1 : 494358 ≤ j) (h2 : j ≤ 494858) : Blo 1977435 (4 * j + 3) := by
  interval_cases j
  · exact B1977435
  · exact B1977439
  · exact B1977443
  · exact B1977447
  · exact B1977451
  · exact B1977455
  · exact B1977459
  · exact B1977463
  · exact B1977467
  · exact B1977471
  · exact B1977475
  · exact B1977479
  · exact B1977483
  · exact B1977487
  · exact B1977491
  · exact B1977495
  · exact B1977499
  · exact B1977503
  · exact B1977507
  · exact B1977511
  · exact B1977515
  · exact B1977519
  · exact B1977523
  · exact B1977527
  · exact B1977531
  · exact B1977535
  · exact B1977539
  · exact B1977543
  · exact B1977547
  · exact B1977551
  · exact B1977555
  · exact B1977559
  · exact B1977563
  · exact B1977567
  · exact B1977571
  · exact B1977575
  · exact B1977579
  · exact B1977583
  · exact B1977587
  · exact B1977591
  · exact B1977595
  · exact B1977599
  · exact B1977603
  · exact B1977607
  · exact B1977611
  · exact B1977615
  · exact B1977619
  · exact B1977623
  · exact B1977627
  · exact B1977631
  · exact B1977635
  · exact B1977639
  · exact B1977643
  · exact B1977647
  · exact B1977651
  · exact B1977655
  · exact B1977659
  · exact B1977663
  · exact B1977667
  · exact B1977671
  · exact B1977675
  · exact B1977679
  · exact B1977683
  · exact B1977687
  · exact B1977691
  · exact B1977695
  · exact B1977699
  · exact B1977703
  · exact B1977707
  · exact B1977711
  · exact B1977715
  · exact B1977719
  · exact B1977723
  · exact B1977727
  · exact B1977731
  · exact B1977735
  · exact B1977739
  · exact B1977743
  · exact B1977747
  · exact B1977751
  · exact B1977755
  · exact B1977759
  · exact B1977763
  · exact B1977767
  · exact B1977771
  · exact B1977775
  · exact B1977779
  · exact B1977783
  · exact B1977787
  · exact B1977791
  · exact B1977795
  · exact B1977799
  · exact B1977803
  · exact B1977807
  · exact B1977811
  · exact B1977815
  · exact B1977819
  · exact B1977823
  · exact B1977827
  · exact B1977831
  · exact B1977835
  · exact B1977839
  · exact B1977843
  · exact B1977847
  · exact B1977851
  · exact B1977855
  · exact B1977859
  · exact B1977863
  · exact B1977867
  · exact B1977871
  · exact B1977875
  · exact B1977879
  · exact B1977883
  · exact B1977887
  · exact B1977891
  · exact B1977895
  · exact B1977899
  · exact B1977903
  · exact B1977907
  · exact B1977911
  · exact B1977915
  · exact B1977919
  · exact B1977923
  · exact B1977927
  · exact B1977931
  · exact B1977935
  · exact B1977939
  · exact B1977943
  · exact B1977947
  · exact B1977951
  · exact B1977955
  · exact B1977959
  · exact B1977963
  · exact B1977967
  · exact B1977971
  · exact B1977975
  · exact B1977979
  · exact B1977983
  · exact B1977987
  · exact B1977991
  · exact B1977995
  · exact B1977999
  · exact B1978003
  · exact B1978007
  · exact B1978011
  · exact B1978015
  · exact B1978019
  · exact B1978023
  · exact B1978027
  · exact B1978031
  · exact B1978035
  · exact B1978039
  · exact B1978043
  · exact B1978047
  · exact B1978051
  · exact B1978055
  · exact B1978059
  · exact B1978063
  · exact B1978067
  · exact B1978071
  · exact B1978075
  · exact B1978079
  · exact B1978083
  · exact B1978087
  · exact B1978091
  · exact B1978095
  · exact B1978099
  · exact B1978103
  · exact B1978107
  · exact B1978111
  · exact B1978115
  · exact B1978119
  · exact B1978123
  · exact B1978127
  · exact B1978131
  · exact B1978135
  · exact B1978139
  · exact B1978143
  · exact B1978147
  · exact B1978151
  · exact B1978155
  · exact B1978159
  · exact B1978163
  · exact B1978167
  · exact B1978171
  · exact B1978175
  · exact B1978179
  · exact B1978183
  · exact B1978187
  · exact B1978191
  · exact B1978195
  · exact B1978199
  · exact B1978203
  · exact B1978207
  · exact B1978211
  · exact B1978215
  · exact B1978219
  · exact B1978223
  · exact B1978227
  · exact B1978231
  · exact B1978235
  · exact B1978239
  · exact B1978243
  · exact B1978247
  · exact B1978251
  · exact B1978255
  · exact B1978259
  · exact B1978263
  · exact B1978267
  · exact B1978271
  · exact B1978275
  · exact B1978279
  · exact B1978283
  · exact B1978287
  · exact B1978291
  · exact B1978295
  · exact B1978299
  · exact B1978303
  · exact B1978307
  · exact B1978311
  · exact B1978315
  · exact B1978319
  · exact B1978323
  · exact B1978327
  · exact B1978331
  · exact B1978335
  · exact B1978339
  · exact B1978343
  · exact B1978347
  · exact B1978351
  · exact B1978355
  · exact B1978359
  · exact B1978363
  · exact B1978367
  · exact B1978371
  · exact B1978375
  · exact B1978379
  · exact B1978383
  · exact B1978387
  · exact B1978391
  · exact B1978395
  · exact B1978399
  · exact B1978403
  · exact B1978407
  · exact B1978411
  · exact B1978415
  · exact B1978419
  · exact B1978423
  · exact B1978427
  · exact B1978431
  · exact B1978435
  · exact B1978439
  · exact B1978443
  · exact B1978447
  · exact B1978451
  · exact B1978455
  · exact B1978459
  · exact B1978463
  · exact B1978467
  · exact B1978471
  · exact B1978475
  · exact B1978479
  · exact B1978483
  · exact B1978487
  · exact B1978491
  · exact B1978495
  · exact B1978499
  · exact B1978503
  · exact B1978507
  · exact B1978511
  · exact B1978515
  · exact B1978519
  · exact B1978523
  · exact B1978527
  · exact B1978531
  · exact B1978535
  · exact B1978539
  · exact B1978543
  · exact B1978547
  · exact B1978551
  · exact B1978555
  · exact B1978559
  · exact B1978563
  · exact B1978567
  · exact B1978571
  · exact B1978575
  · exact B1978579
  · exact B1978583
  · exact B1978587
  · exact B1978591
  · exact B1978595
  · exact B1978599
  · exact B1978603
  · exact B1978607
  · exact B1978611
  · exact B1978615
  · exact B1978619
  · exact B1978623
  · exact B1978627
  · exact B1978631
  · exact B1978635
  · exact B1978639
  · exact B1978643
  · exact B1978647
  · exact B1978651
  · exact B1978655
  · exact B1978659
  · exact B1978663
  · exact B1978667
  · exact B1978671
  · exact B1978675
  · exact B1978679
  · exact B1978683
  · exact B1978687
  · exact B1978691
  · exact B1978695
  · exact B1978699
  · exact B1978703
  · exact B1978707
  · exact B1978711
  · exact B1978715
  · exact B1978719
  · exact B1978723
  · exact B1978727
  · exact B1978731
  · exact B1978735
  · exact B1978739
  · exact B1978743
  · exact B1978747
  · exact B1978751
  · exact B1978755
  · exact B1978759
  · exact B1978763
  · exact B1978767
  · exact B1978771
  · exact B1978775
  · exact B1978779
  · exact B1978783
  · exact B1978787
  · exact B1978791
  · exact B1978795
  · exact B1978799
  · exact B1978803
  · exact B1978807
  · exact B1978811
  · exact B1978815
  · exact B1978819
  · exact B1978823
  · exact B1978827
  · exact B1978831
  · exact B1978835
  · exact B1978839
  · exact B1978843
  · exact B1978847
  · exact B1978851
  · exact B1978855
  · exact B1978859
  · exact B1978863
  · exact B1978867
  · exact B1978871
  · exact B1978875
  · exact B1978879
  · exact B1978883
  · exact B1978887
  · exact B1978891
  · exact B1978895
  · exact B1978899
  · exact B1978903
  · exact B1978907
  · exact B1978911
  · exact B1978915
  · exact B1978919
  · exact B1978923
  · exact B1978927
  · exact B1978931
  · exact B1978935
  · exact B1978939
  · exact B1978943
  · exact B1978947
  · exact B1978951
  · exact B1978955
  · exact B1978959
  · exact B1978963
  · exact B1978967
  · exact B1978971
  · exact B1978975
  · exact B1978979
  · exact B1978983
  · exact B1978987
  · exact B1978991
  · exact B1978995
  · exact B1978999
  · exact B1979003
  · exact B1979007
  · exact B1979011
  · exact B1979015
  · exact B1979019
  · exact B1979023
  · exact B1979027
  · exact B1979031
  · exact B1979035
  · exact B1979039
  · exact B1979043
  · exact B1979047
  · exact B1979051
  · exact B1979055
  · exact B1979059
  · exact B1979063
  · exact B1979067
  · exact B1979071
  · exact B1979075
  · exact B1979079
  · exact B1979083
  · exact B1979087
  · exact B1979091
  · exact B1979095
  · exact B1979099
  · exact B1979103
  · exact B1979107
  · exact B1979111
  · exact B1979115
  · exact B1979119
  · exact B1979123
  · exact B1979127
  · exact B1979131
  · exact B1979135
  · exact B1979139
  · exact B1979143
  · exact B1979147
  · exact B1979151
  · exact B1979155
  · exact B1979159
  · exact B1979163
  · exact B1979167
  · exact B1979171
  · exact B1979175
  · exact B1979179
  · exact B1979183
  · exact B1979187
  · exact B1979191
  · exact B1979195
  · exact B1979199
  · exact B1979203
  · exact B1979207
  · exact B1979211
  · exact B1979215
  · exact B1979219
  · exact B1979223
  · exact B1979227
  · exact B1979231
  · exact B1979235
  · exact B1979239
  · exact B1979243
  · exact B1979247
  · exact B1979251
  · exact B1979255
  · exact B1979259
  · exact B1979263
  · exact B1979267
  · exact B1979271
  · exact B1979275
  · exact B1979279
  · exact B1979283
  · exact B1979287
  · exact B1979291
  · exact B1979295
  · exact B1979299
  · exact B1979303
  · exact B1979307
  · exact B1979311
  · exact B1979315
  · exact B1979319
  · exact B1979323
  · exact B1979327
  · exact B1979331
  · exact B1979335
  · exact B1979339
  · exact B1979343
  · exact B1979347
  · exact B1979351
  · exact B1979355
  · exact B1979359
  · exact B1979363
  · exact B1979367
  · exact B1979371
  · exact B1979375
  · exact B1979379
  · exact B1979383
  · exact B1979387
  · exact B1979391
  · exact B1979395
  · exact B1979399
  · exact B1979403
  · exact B1979407
  · exact B1979411
  · exact B1979415
  · exact B1979419
  · exact B1979423
  · exact B1979427
  · exact B1979431
  · exact B1979435
theorem solution (m : ℕ) (hlo : 1977435 ≤ m) (hhi : m ≤ 1979435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 494358 ≤ j := by omega
    have hj2 : j ≤ 494858 := by omega
    have hb : Blo 1977435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
