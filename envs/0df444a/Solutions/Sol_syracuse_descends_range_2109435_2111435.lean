-- Prove2me | solution 1 for syracuse_descends_range_2109435_2111435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:16:43.112987+00:00
-- url     : https://prove2.me/submissions/b891371e-c900-4af7-9b41-f881530b61a7

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

theorem B4505213 : Blo 2109435 4505213 := bbase (se 3 (by rfl) ⟨844727, by rfl⟩ : syracuseStep 4505213 = 1689455) (by norm_num)
theorem B3003475 : Blo 2109435 3003475 := bstep (se 1 (by rfl) ⟨2252606, by rfl⟩ : syracuseStep 3003475 = 4505213) B4505213
theorem B4004633 : Blo 2109435 4004633 := bstep (se 2 (by rfl) ⟨1501737, by rfl⟩ : syracuseStep 4004633 = 3003475) B3003475
theorem B2669755 : Blo 2109435 2669755 := bstep (se 1 (by rfl) ⟨2002316, by rfl⟩ : syracuseStep 2669755 = 4004633) B4004633
theorem B3559673 : Blo 2109435 3559673 := bstep (se 2 (by rfl) ⟨1334877, by rfl⟩ : syracuseStep 3559673 = 2669755) B2669755
theorem B2373115 : Blo 2109435 2373115 := bstep (se 1 (by rfl) ⟨1779836, by rfl⟩ : syracuseStep 2373115 = 3559673) B3559673
theorem B3164153 : Blo 2109435 3164153 := bstep (se 2 (by rfl) ⟨1186557, by rfl⟩ : syracuseStep 3164153 = 2373115) B2373115
theorem B2109435 : Blo 2109435 2109435 := bstep (se 1 (by rfl) ⟨1582076, by rfl⟩ : syracuseStep 2109435 = 3164153) B3164153
theorem B30063637 : Blo 2109435 30063637 := bbase (se 6 (by rfl) ⟨704616, by rfl⟩ : syracuseStep 30063637 = 1409233) (by norm_num)
theorem B160339397 : Blo 2109435 160339397 := bstep (se 4 (by rfl) ⟨15031818, by rfl⟩ : syracuseStep 160339397 = 30063637) B30063637
theorem B427571725 : Blo 2109435 427571725 := bstep (se 3 (by rfl) ⟨80169698, by rfl⟩ : syracuseStep 427571725 = 160339397) B160339397
theorem B570095633 : Blo 2109435 570095633 := bstep (se 2 (by rfl) ⟨213785862, by rfl⟩ : syracuseStep 570095633 = 427571725) B427571725
theorem B380063755 : Blo 2109435 380063755 := bstep (se 1 (by rfl) ⟨285047816, by rfl⟩ : syracuseStep 380063755 = 570095633) B570095633
theorem B506751673 : Blo 2109435 506751673 := bstep (se 2 (by rfl) ⟨190031877, by rfl⟩ : syracuseStep 506751673 = 380063755) B380063755
theorem B675668897 : Blo 2109435 675668897 := bstep (se 2 (by rfl) ⟨253375836, by rfl⟩ : syracuseStep 675668897 = 506751673) B506751673
theorem B450445931 : Blo 2109435 450445931 := bstep (se 1 (by rfl) ⟨337834448, by rfl⟩ : syracuseStep 450445931 = 675668897) B675668897
theorem B300297287 : Blo 2109435 300297287 := bstep (se 1 (by rfl) ⟨225222965, by rfl⟩ : syracuseStep 300297287 = 450445931) B450445931
theorem B200198191 : Blo 2109435 200198191 := bstep (se 1 (by rfl) ⟨150148643, by rfl⟩ : syracuseStep 200198191 = 300297287) B300297287
theorem B266930921 : Blo 2109435 266930921 := bstep (se 2 (by rfl) ⟨100099095, by rfl⟩ : syracuseStep 266930921 = 200198191) B200198191
theorem B711815789 : Blo 2109435 711815789 := bstep (se 3 (by rfl) ⟨133465460, by rfl⟩ : syracuseStep 711815789 = 266930921) B266930921
theorem B474543859 : Blo 2109435 474543859 := bstep (se 1 (by rfl) ⟨355907894, by rfl⟩ : syracuseStep 474543859 = 711815789) B711815789
theorem B632725145 : Blo 2109435 632725145 := bstep (se 2 (by rfl) ⟨237271929, by rfl⟩ : syracuseStep 632725145 = 474543859) B474543859
theorem B421816763 : Blo 2109435 421816763 := bstep (se 1 (by rfl) ⟨316362572, by rfl⟩ : syracuseStep 421816763 = 632725145) B632725145
theorem B281211175 : Blo 2109435 281211175 := bstep (se 1 (by rfl) ⟨210908381, by rfl⟩ : syracuseStep 281211175 = 421816763) B421816763
theorem B374948233 : Blo 2109435 374948233 := bstep (se 2 (by rfl) ⟨140605587, by rfl⟩ : syracuseStep 374948233 = 281211175) B281211175
theorem B7998895637 : Blo 2109435 7998895637 := bstep (se 6 (by rfl) ⟨187474116, by rfl⟩ : syracuseStep 7998895637 = 374948233) B374948233
theorem B5332597091 : Blo 2109435 5332597091 := bstep (se 1 (by rfl) ⟨3999447818, by rfl⟩ : syracuseStep 5332597091 = 7998895637) B7998895637
theorem B3555064727 : Blo 2109435 3555064727 := bstep (se 1 (by rfl) ⟨2666298545, by rfl⟩ : syracuseStep 3555064727 = 5332597091) B5332597091
theorem B2370043151 : Blo 2109435 2370043151 := bstep (se 1 (by rfl) ⟨1777532363, by rfl⟩ : syracuseStep 2370043151 = 3555064727) B3555064727
theorem B1580028767 : Blo 2109435 1580028767 := bstep (se 1 (by rfl) ⟨1185021575, by rfl⟩ : syracuseStep 1580028767 = 2370043151) B2370043151
theorem B1053352511 : Blo 2109435 1053352511 := bstep (se 1 (by rfl) ⟨790014383, by rfl⟩ : syracuseStep 1053352511 = 1580028767) B1580028767
theorem B702235007 : Blo 2109435 702235007 := bstep (se 1 (by rfl) ⟨526676255, by rfl⟩ : syracuseStep 702235007 = 1053352511) B1053352511
theorem B468156671 : Blo 2109435 468156671 := bstep (se 1 (by rfl) ⟨351117503, by rfl⟩ : syracuseStep 468156671 = 702235007) B702235007
theorem B312104447 : Blo 2109435 312104447 := bstep (se 1 (by rfl) ⟨234078335, by rfl⟩ : syracuseStep 312104447 = 468156671) B468156671
theorem B208069631 : Blo 2109435 208069631 := bstep (se 1 (by rfl) ⟨156052223, by rfl⟩ : syracuseStep 208069631 = 312104447) B312104447
theorem B138713087 : Blo 2109435 138713087 := bstep (se 1 (by rfl) ⟨104034815, by rfl⟩ : syracuseStep 138713087 = 208069631) B208069631
theorem B369901565 : Blo 2109435 369901565 := bstep (se 3 (by rfl) ⟨69356543, by rfl⟩ : syracuseStep 369901565 = 138713087) B138713087
theorem B246601043 : Blo 2109435 246601043 := bstep (se 1 (by rfl) ⟨184950782, by rfl⟩ : syracuseStep 246601043 = 369901565) B369901565
theorem B164400695 : Blo 2109435 164400695 := bstep (se 1 (by rfl) ⟨123300521, by rfl⟩ : syracuseStep 164400695 = 246601043) B246601043
theorem B109600463 : Blo 2109435 109600463 := bstep (se 1 (by rfl) ⟨82200347, by rfl⟩ : syracuseStep 109600463 = 164400695) B164400695
theorem B292267901 : Blo 2109435 292267901 := bstep (se 3 (by rfl) ⟨54800231, by rfl⟩ : syracuseStep 292267901 = 109600463) B109600463
theorem B194845267 : Blo 2109435 194845267 := bstep (se 1 (by rfl) ⟨146133950, by rfl⟩ : syracuseStep 194845267 = 292267901) B292267901
theorem B259793689 : Blo 2109435 259793689 := bstep (se 2 (by rfl) ⟨97422633, by rfl⟩ : syracuseStep 259793689 = 194845267) B194845267
theorem B346391585 : Blo 2109435 346391585 := bstep (se 2 (by rfl) ⟨129896844, by rfl⟩ : syracuseStep 346391585 = 259793689) B259793689
theorem B230927723 : Blo 2109435 230927723 := bstep (se 1 (by rfl) ⟨173195792, by rfl⟩ : syracuseStep 230927723 = 346391585) B346391585
theorem B153951815 : Blo 2109435 153951815 := bstep (se 1 (by rfl) ⟨115463861, by rfl⟩ : syracuseStep 153951815 = 230927723) B230927723
theorem B102634543 : Blo 2109435 102634543 := bstep (se 1 (by rfl) ⟨76975907, by rfl⟩ : syracuseStep 102634543 = 153951815) B153951815
theorem B136846057 : Blo 2109435 136846057 := bstep (se 2 (by rfl) ⟨51317271, by rfl⟩ : syracuseStep 136846057 = 102634543) B102634543
theorem B182461409 : Blo 2109435 182461409 := bstep (se 2 (by rfl) ⟨68423028, by rfl⟩ : syracuseStep 182461409 = 136846057) B136846057
theorem B121640939 : Blo 2109435 121640939 := bstep (se 1 (by rfl) ⟨91230704, by rfl⟩ : syracuseStep 121640939 = 182461409) B182461409
theorem B81093959 : Blo 2109435 81093959 := bstep (se 1 (by rfl) ⟨60820469, by rfl⟩ : syracuseStep 81093959 = 121640939) B121640939
theorem B54062639 : Blo 2109435 54062639 := bstep (se 1 (by rfl) ⟨40546979, by rfl⟩ : syracuseStep 54062639 = 81093959) B81093959
theorem B36041759 : Blo 2109435 36041759 := bstep (se 1 (by rfl) ⟨27031319, by rfl⟩ : syracuseStep 36041759 = 54062639) B54062639
theorem B24027839 : Blo 2109435 24027839 := bstep (se 1 (by rfl) ⟨18020879, by rfl⟩ : syracuseStep 24027839 = 36041759) B36041759
theorem B16018559 : Blo 2109435 16018559 := bstep (se 1 (by rfl) ⟨12013919, by rfl⟩ : syracuseStep 16018559 = 24027839) B24027839
theorem B10679039 : Blo 2109435 10679039 := bstep (se 1 (by rfl) ⟨8009279, by rfl⟩ : syracuseStep 10679039 = 16018559) B16018559
theorem B7119359 : Blo 2109435 7119359 := bstep (se 1 (by rfl) ⟨5339519, by rfl⟩ : syracuseStep 7119359 = 10679039) B10679039
theorem B4746239 : Blo 2109435 4746239 := bstep (se 1 (by rfl) ⟨3559679, by rfl⟩ : syracuseStep 4746239 = 7119359) B7119359
theorem B3164159 : Blo 2109435 3164159 := bstep (se 1 (by rfl) ⟨2373119, by rfl⟩ : syracuseStep 3164159 = 4746239) B4746239
theorem B2109439 : Blo 2109435 2109439 := bstep (se 1 (by rfl) ⟨1582079, by rfl⟩ : syracuseStep 2109439 = 3164159) B3164159
theorem B3164165 : Blo 2109435 3164165 := bbase (se 4 (by rfl) ⟨296640, by rfl⟩ : syracuseStep 3164165 = 593281) (by norm_num)
theorem B2109443 : Blo 2109435 2109443 := bstep (se 1 (by rfl) ⟨1582082, by rfl⟩ : syracuseStep 2109443 = 3164165) B3164165
theorem B3559693 : Blo 2109435 3559693 := bbase (se 3 (by rfl) ⟨667442, by rfl⟩ : syracuseStep 3559693 = 1334885) (by norm_num)
theorem B4746257 : Blo 2109435 4746257 := bstep (se 2 (by rfl) ⟨1779846, by rfl⟩ : syracuseStep 4746257 = 3559693) B3559693
theorem B3164171 : Blo 2109435 3164171 := bstep (se 1 (by rfl) ⟨2373128, by rfl⟩ : syracuseStep 3164171 = 4746257) B4746257
theorem B2109447 : Blo 2109435 2109447 := bstep (se 1 (by rfl) ⟨1582085, by rfl⟩ : syracuseStep 2109447 = 3164171) B3164171
theorem B2373133 : Blo 2109435 2373133 := bbase (se 3 (by rfl) ⟨444962, by rfl⟩ : syracuseStep 2373133 = 889925) (by norm_num)
theorem B3164177 : Blo 2109435 3164177 := bstep (se 2 (by rfl) ⟨1186566, by rfl⟩ : syracuseStep 3164177 = 2373133) B2373133
theorem B2109451 : Blo 2109435 2109451 := bstep (se 1 (by rfl) ⟨1582088, by rfl⟩ : syracuseStep 2109451 = 3164177) B3164177
theorem B7119413 : Blo 2109435 7119413 := bbase (se 5 (by rfl) ⟨333722, by rfl⟩ : syracuseStep 7119413 = 667445) (by norm_num)
theorem B4746275 : Blo 2109435 4746275 := bstep (se 1 (by rfl) ⟨3559706, by rfl⟩ : syracuseStep 4746275 = 7119413) B7119413
theorem B3164183 : Blo 2109435 3164183 := bstep (se 1 (by rfl) ⟨2373137, by rfl⟩ : syracuseStep 3164183 = 4746275) B4746275
theorem B2109455 : Blo 2109435 2109455 := bstep (se 1 (by rfl) ⟨1582091, by rfl⟩ : syracuseStep 2109455 = 3164183) B3164183
theorem B3164189 : Blo 2109435 3164189 := bbase (se 3 (by rfl) ⟨593285, by rfl⟩ : syracuseStep 3164189 = 1186571) (by norm_num)
theorem B2109459 : Blo 2109435 2109459 := bstep (se 1 (by rfl) ⟨1582094, by rfl⟩ : syracuseStep 2109459 = 3164189) B3164189
theorem B4746293 : Blo 2109435 4746293 := bbase (se 5 (by rfl) ⟨222482, by rfl⟩ : syracuseStep 4746293 = 444965) (by norm_num)
theorem B3164195 : Blo 2109435 3164195 := bstep (se 1 (by rfl) ⟨2373146, by rfl⟩ : syracuseStep 3164195 = 4746293) B4746293
theorem B2109463 : Blo 2109435 2109463 := bstep (se 1 (by rfl) ⟨1582097, by rfl⟩ : syracuseStep 2109463 = 3164195) B3164195
theorem B2138249 : Blo 2109435 2138249 := bbase (se 2 (by rfl) ⟨801843, by rfl⟩ : syracuseStep 2138249 = 1603687) (by norm_num)
theorem B5701997 : Blo 2109435 5701997 := bstep (se 3 (by rfl) ⟨1069124, by rfl⟩ : syracuseStep 5701997 = 2138249) B2138249
theorem B3801331 : Blo 2109435 3801331 := bstep (se 1 (by rfl) ⟨2850998, by rfl⟩ : syracuseStep 3801331 = 5701997) B5701997
theorem B5068441 : Blo 2109435 5068441 := bstep (se 2 (by rfl) ⟨1900665, by rfl⟩ : syracuseStep 5068441 = 3801331) B3801331
theorem B6757921 : Blo 2109435 6757921 := bstep (se 2 (by rfl) ⟨2534220, by rfl⟩ : syracuseStep 6757921 = 5068441) B5068441
theorem B9010561 : Blo 2109435 9010561 := bstep (se 2 (by rfl) ⟨3378960, by rfl⟩ : syracuseStep 9010561 = 6757921) B6757921
theorem B12014081 : Blo 2109435 12014081 := bstep (se 2 (by rfl) ⟨4505280, by rfl⟩ : syracuseStep 12014081 = 9010561) B9010561
theorem B8009387 : Blo 2109435 8009387 := bstep (se 1 (by rfl) ⟨6007040, by rfl⟩ : syracuseStep 8009387 = 12014081) B12014081
theorem B5339591 : Blo 2109435 5339591 := bstep (se 1 (by rfl) ⟨4004693, by rfl⟩ : syracuseStep 5339591 = 8009387) B8009387
theorem B3559727 : Blo 2109435 3559727 := bstep (se 1 (by rfl) ⟨2669795, by rfl⟩ : syracuseStep 3559727 = 5339591) B5339591
theorem B2373151 : Blo 2109435 2373151 := bstep (se 1 (by rfl) ⟨1779863, by rfl⟩ : syracuseStep 2373151 = 3559727) B3559727
theorem B3164201 : Blo 2109435 3164201 := bstep (se 2 (by rfl) ⟨1186575, by rfl⟩ : syracuseStep 3164201 = 2373151) B2373151
theorem B2109467 : Blo 2109435 2109467 := bstep (se 1 (by rfl) ⟨1582100, by rfl⟩ : syracuseStep 2109467 = 3164201) B3164201
theorem B2534225 : Blo 2109435 2534225 := bbase (se 2 (by rfl) ⟨950334, by rfl⟩ : syracuseStep 2534225 = 1900669) (by norm_num)
theorem B6757933 : Blo 2109435 6757933 := bstep (se 3 (by rfl) ⟨1267112, by rfl⟩ : syracuseStep 6757933 = 2534225) B2534225
theorem B9010577 : Blo 2109435 9010577 := bstep (se 2 (by rfl) ⟨3378966, by rfl⟩ : syracuseStep 9010577 = 6757933) B6757933
theorem B6007051 : Blo 2109435 6007051 := bstep (se 1 (by rfl) ⟨4505288, by rfl⟩ : syracuseStep 6007051 = 9010577) B9010577
theorem B8009401 : Blo 2109435 8009401 := bstep (se 2 (by rfl) ⟨3003525, by rfl⟩ : syracuseStep 8009401 = 6007051) B6007051
theorem B10679201 : Blo 2109435 10679201 := bstep (se 2 (by rfl) ⟨4004700, by rfl⟩ : syracuseStep 10679201 = 8009401) B8009401
theorem B7119467 : Blo 2109435 7119467 := bstep (se 1 (by rfl) ⟨5339600, by rfl⟩ : syracuseStep 7119467 = 10679201) B10679201
theorem B4746311 : Blo 2109435 4746311 := bstep (se 1 (by rfl) ⟨3559733, by rfl⟩ : syracuseStep 4746311 = 7119467) B7119467
theorem B3164207 : Blo 2109435 3164207 := bstep (se 1 (by rfl) ⟨2373155, by rfl⟩ : syracuseStep 3164207 = 4746311) B4746311
theorem B2109471 : Blo 2109435 2109471 := bstep (se 1 (by rfl) ⟨1582103, by rfl⟩ : syracuseStep 2109471 = 3164207) B3164207
theorem B3164213 : Blo 2109435 3164213 := bbase (se 5 (by rfl) ⟨148322, by rfl⟩ : syracuseStep 3164213 = 296645) (by norm_num)
theorem B2109475 : Blo 2109435 2109475 := bstep (se 1 (by rfl) ⟨1582106, by rfl⟩ : syracuseStep 2109475 = 3164213) B3164213
theorem B5339621 : Blo 2109435 5339621 := bbase (se 4 (by rfl) ⟨500589, by rfl⟩ : syracuseStep 5339621 = 1001179) (by norm_num)
theorem B3559747 : Blo 2109435 3559747 := bstep (se 1 (by rfl) ⟨2669810, by rfl⟩ : syracuseStep 3559747 = 5339621) B5339621
theorem B4746329 : Blo 2109435 4746329 := bstep (se 2 (by rfl) ⟨1779873, by rfl⟩ : syracuseStep 4746329 = 3559747) B3559747
theorem B3164219 : Blo 2109435 3164219 := bstep (se 1 (by rfl) ⟨2373164, by rfl⟩ : syracuseStep 3164219 = 4746329) B4746329
theorem B2109479 : Blo 2109435 2109479 := bstep (se 1 (by rfl) ⟨1582109, by rfl⟩ : syracuseStep 2109479 = 3164219) B3164219
theorem B2373169 : Blo 2109435 2373169 := bbase (se 2 (by rfl) ⟨889938, by rfl⟩ : syracuseStep 2373169 = 1779877) (by norm_num)
theorem B3164225 : Blo 2109435 3164225 := bstep (se 2 (by rfl) ⟨1186584, by rfl⟩ : syracuseStep 3164225 = 2373169) B2373169
theorem B2109483 : Blo 2109435 2109483 := bstep (se 1 (by rfl) ⟨1582112, by rfl⟩ : syracuseStep 2109483 = 3164225) B3164225
theorem B8553077 : Blo 2109435 8553077 := bbase (se 5 (by rfl) ⟨400925, by rfl⟩ : syracuseStep 8553077 = 801851) (by norm_num)
theorem B5702051 : Blo 2109435 5702051 := bstep (se 1 (by rfl) ⟨4276538, by rfl⟩ : syracuseStep 5702051 = 8553077) B8553077
theorem B3801367 : Blo 2109435 3801367 := bstep (se 1 (by rfl) ⟨2851025, by rfl⟩ : syracuseStep 3801367 = 5702051) B5702051
theorem B5068489 : Blo 2109435 5068489 := bstep (se 2 (by rfl) ⟨1900683, by rfl⟩ : syracuseStep 5068489 = 3801367) B3801367
theorem B6757985 : Blo 2109435 6757985 := bstep (se 2 (by rfl) ⟨2534244, by rfl⟩ : syracuseStep 6757985 = 5068489) B5068489
theorem B4505323 : Blo 2109435 4505323 := bstep (se 1 (by rfl) ⟨3378992, by rfl⟩ : syracuseStep 4505323 = 6757985) B6757985
theorem B6007097 : Blo 2109435 6007097 := bstep (se 2 (by rfl) ⟨2252661, by rfl⟩ : syracuseStep 6007097 = 4505323) B4505323
theorem B4004731 : Blo 2109435 4004731 := bstep (se 1 (by rfl) ⟨3003548, by rfl⟩ : syracuseStep 4004731 = 6007097) B6007097
theorem B5339641 : Blo 2109435 5339641 := bstep (se 2 (by rfl) ⟨2002365, by rfl⟩ : syracuseStep 5339641 = 4004731) B4004731
theorem B7119521 : Blo 2109435 7119521 := bstep (se 2 (by rfl) ⟨2669820, by rfl⟩ : syracuseStep 7119521 = 5339641) B5339641
theorem B4746347 : Blo 2109435 4746347 := bstep (se 1 (by rfl) ⟨3559760, by rfl⟩ : syracuseStep 4746347 = 7119521) B7119521
theorem B3164231 : Blo 2109435 3164231 := bstep (se 1 (by rfl) ⟨2373173, by rfl⟩ : syracuseStep 3164231 = 4746347) B4746347
theorem B2109487 : Blo 2109435 2109487 := bstep (se 1 (by rfl) ⟨1582115, by rfl⟩ : syracuseStep 2109487 = 3164231) B3164231
theorem B3164237 : Blo 2109435 3164237 := bbase (se 3 (by rfl) ⟨593294, by rfl⟩ : syracuseStep 3164237 = 1186589) (by norm_num)
theorem B2109491 : Blo 2109435 2109491 := bstep (se 1 (by rfl) ⟨1582118, by rfl⟩ : syracuseStep 2109491 = 3164237) B3164237
theorem B4746365 : Blo 2109435 4746365 := bbase (se 3 (by rfl) ⟨889943, by rfl⟩ : syracuseStep 4746365 = 1779887) (by norm_num)
theorem B3164243 : Blo 2109435 3164243 := bstep (se 1 (by rfl) ⟨2373182, by rfl⟩ : syracuseStep 3164243 = 4746365) B4746365
theorem B2109495 : Blo 2109435 2109495 := bstep (se 1 (by rfl) ⟨1582121, by rfl⟩ : syracuseStep 2109495 = 3164243) B3164243
theorem B3559781 : Blo 2109435 3559781 := bbase (se 4 (by rfl) ⟨333729, by rfl⟩ : syracuseStep 3559781 = 667459) (by norm_num)
theorem B2373187 : Blo 2109435 2373187 := bstep (se 1 (by rfl) ⟨1779890, by rfl⟩ : syracuseStep 2373187 = 3559781) B3559781
theorem B3164249 : Blo 2109435 3164249 := bstep (se 2 (by rfl) ⟨1186593, by rfl⟩ : syracuseStep 3164249 = 2373187) B2373187
theorem B2109499 : Blo 2109435 2109499 := bstep (se 1 (by rfl) ⟨1582124, by rfl⟩ : syracuseStep 2109499 = 3164249) B3164249
theorem B4505357 : Blo 2109435 4505357 := bbase (se 3 (by rfl) ⟨844754, by rfl⟩ : syracuseStep 4505357 = 1689509) (by norm_num)
theorem B3003571 : Blo 2109435 3003571 := bstep (se 1 (by rfl) ⟨2252678, by rfl⟩ : syracuseStep 3003571 = 4505357) B4505357
theorem B16019045 : Blo 2109435 16019045 := bstep (se 4 (by rfl) ⟨1501785, by rfl⟩ : syracuseStep 16019045 = 3003571) B3003571
theorem B10679363 : Blo 2109435 10679363 := bstep (se 1 (by rfl) ⟨8009522, by rfl⟩ : syracuseStep 10679363 = 16019045) B16019045
theorem B7119575 : Blo 2109435 7119575 := bstep (se 1 (by rfl) ⟨5339681, by rfl⟩ : syracuseStep 7119575 = 10679363) B10679363
theorem B4746383 : Blo 2109435 4746383 := bstep (se 1 (by rfl) ⟨3559787, by rfl⟩ : syracuseStep 4746383 = 7119575) B7119575
theorem B3164255 : Blo 2109435 3164255 := bstep (se 1 (by rfl) ⟨2373191, by rfl⟩ : syracuseStep 3164255 = 4746383) B4746383
theorem B2109503 : Blo 2109435 2109503 := bstep (se 1 (by rfl) ⟨1582127, by rfl⟩ : syracuseStep 2109503 = 3164255) B3164255
theorem B3164261 : Blo 2109435 3164261 := bbase (se 4 (by rfl) ⟨296649, by rfl⟩ : syracuseStep 3164261 = 593299) (by norm_num)
theorem B2109507 : Blo 2109435 2109507 := bstep (se 1 (by rfl) ⟨1582130, by rfl⟩ : syracuseStep 2109507 = 3164261) B3164261
theorem B5412557 : Blo 2109435 5412557 := bbase (se 3 (by rfl) ⟨1014854, by rfl⟩ : syracuseStep 5412557 = 2029709) (by norm_num)
theorem B3608371 : Blo 2109435 3608371 := bstep (se 1 (by rfl) ⟨2706278, by rfl⟩ : syracuseStep 3608371 = 5412557) B5412557
theorem B4811161 : Blo 2109435 4811161 := bstep (se 2 (by rfl) ⟨1804185, by rfl⟩ : syracuseStep 4811161 = 3608371) B3608371
theorem B6414881 : Blo 2109435 6414881 := bstep (se 2 (by rfl) ⟨2405580, by rfl⟩ : syracuseStep 6414881 = 4811161) B4811161
theorem B17106349 : Blo 2109435 17106349 := bstep (se 3 (by rfl) ⟨3207440, by rfl⟩ : syracuseStep 17106349 = 6414881) B6414881
theorem B22808465 : Blo 2109435 22808465 := bstep (se 2 (by rfl) ⟨8553174, by rfl⟩ : syracuseStep 22808465 = 17106349) B17106349
theorem B15205643 : Blo 2109435 15205643 := bstep (se 1 (by rfl) ⟨11404232, by rfl⟩ : syracuseStep 15205643 = 22808465) B22808465
theorem B10137095 : Blo 2109435 10137095 := bstep (se 1 (by rfl) ⟨7602821, by rfl⟩ : syracuseStep 10137095 = 15205643) B15205643
theorem B6758063 : Blo 2109435 6758063 := bstep (se 1 (by rfl) ⟨5068547, by rfl⟩ : syracuseStep 6758063 = 10137095) B10137095
theorem B4505375 : Blo 2109435 4505375 := bstep (se 1 (by rfl) ⟨3379031, by rfl⟩ : syracuseStep 4505375 = 6758063) B6758063
theorem B3003583 : Blo 2109435 3003583 := bstep (se 1 (by rfl) ⟨2252687, by rfl⟩ : syracuseStep 3003583 = 4505375) B4505375
theorem B4004777 : Blo 2109435 4004777 := bstep (se 2 (by rfl) ⟨1501791, by rfl⟩ : syracuseStep 4004777 = 3003583) B3003583
theorem B2669851 : Blo 2109435 2669851 := bstep (se 1 (by rfl) ⟨2002388, by rfl⟩ : syracuseStep 2669851 = 4004777) B4004777
theorem B3559801 : Blo 2109435 3559801 := bstep (se 2 (by rfl) ⟨1334925, by rfl⟩ : syracuseStep 3559801 = 2669851) B2669851
theorem B4746401 : Blo 2109435 4746401 := bstep (se 2 (by rfl) ⟨1779900, by rfl⟩ : syracuseStep 4746401 = 3559801) B3559801
theorem B3164267 : Blo 2109435 3164267 := bstep (se 1 (by rfl) ⟨2373200, by rfl⟩ : syracuseStep 3164267 = 4746401) B4746401
theorem B2109511 : Blo 2109435 2109511 := bstep (se 1 (by rfl) ⟨1582133, by rfl⟩ : syracuseStep 2109511 = 3164267) B3164267
theorem B2373205 : Blo 2109435 2373205 := bbase (se 8 (by rfl) ⟨13905, by rfl⟩ : syracuseStep 2373205 = 27811) (by norm_num)
theorem B3164273 : Blo 2109435 3164273 := bstep (se 2 (by rfl) ⟨1186602, by rfl⟩ : syracuseStep 3164273 = 2373205) B2373205
theorem B2109515 : Blo 2109435 2109515 := bstep (se 1 (by rfl) ⟨1582136, by rfl⟩ : syracuseStep 2109515 = 3164273) B3164273
theorem B2669861 : Blo 2109435 2669861 := bbase (se 4 (by rfl) ⟨250299, by rfl⟩ : syracuseStep 2669861 = 500599) (by norm_num)
theorem B7119629 : Blo 2109435 7119629 := bstep (se 3 (by rfl) ⟨1334930, by rfl⟩ : syracuseStep 7119629 = 2669861) B2669861
theorem B4746419 : Blo 2109435 4746419 := bstep (se 1 (by rfl) ⟨3559814, by rfl⟩ : syracuseStep 4746419 = 7119629) B7119629
theorem B3164279 : Blo 2109435 3164279 := bstep (se 1 (by rfl) ⟨2373209, by rfl⟩ : syracuseStep 3164279 = 4746419) B4746419
theorem B2109519 : Blo 2109435 2109519 := bstep (se 1 (by rfl) ⟨1582139, by rfl⟩ : syracuseStep 2109519 = 3164279) B3164279
theorem B3164285 : Blo 2109435 3164285 := bbase (se 3 (by rfl) ⟨593303, by rfl⟩ : syracuseStep 3164285 = 1186607) (by norm_num)
theorem B2109523 : Blo 2109435 2109523 := bstep (se 1 (by rfl) ⟨1582142, by rfl⟩ : syracuseStep 2109523 = 3164285) B3164285
theorem B4746437 : Blo 2109435 4746437 := bbase (se 4 (by rfl) ⟨444978, by rfl⟩ : syracuseStep 4746437 = 889957) (by norm_num)
theorem B3164291 : Blo 2109435 3164291 := bstep (se 1 (by rfl) ⟨2373218, by rfl⟩ : syracuseStep 3164291 = 4746437) B4746437
theorem B2109527 : Blo 2109435 2109527 := bstep (se 1 (by rfl) ⟨1582145, by rfl⟩ : syracuseStep 2109527 = 3164291) B3164291
theorem B2851085 : Blo 2109435 2851085 := bbase (se 3 (by rfl) ⟨534578, by rfl⟩ : syracuseStep 2851085 = 1069157) (by norm_num)
theorem B7602893 : Blo 2109435 7602893 := bstep (se 3 (by rfl) ⟨1425542, by rfl⟩ : syracuseStep 7602893 = 2851085) B2851085
theorem B5068595 : Blo 2109435 5068595 := bstep (se 1 (by rfl) ⟨3801446, by rfl⟩ : syracuseStep 5068595 = 7602893) B7602893
theorem B13516253 : Blo 2109435 13516253 := bstep (se 3 (by rfl) ⟨2534297, by rfl⟩ : syracuseStep 13516253 = 5068595) B5068595
theorem B9010835 : Blo 2109435 9010835 := bstep (se 1 (by rfl) ⟨6758126, by rfl⟩ : syracuseStep 9010835 = 13516253) B13516253
theorem B6007223 : Blo 2109435 6007223 := bstep (se 1 (by rfl) ⟨4505417, by rfl⟩ : syracuseStep 6007223 = 9010835) B9010835
theorem B4004815 : Blo 2109435 4004815 := bstep (se 1 (by rfl) ⟨3003611, by rfl⟩ : syracuseStep 4004815 = 6007223) B6007223
theorem B5339753 : Blo 2109435 5339753 := bstep (se 2 (by rfl) ⟨2002407, by rfl⟩ : syracuseStep 5339753 = 4004815) B4004815
theorem B3559835 : Blo 2109435 3559835 := bstep (se 1 (by rfl) ⟨2669876, by rfl⟩ : syracuseStep 3559835 = 5339753) B5339753
theorem B2373223 : Blo 2109435 2373223 := bstep (se 1 (by rfl) ⟨1779917, by rfl⟩ : syracuseStep 2373223 = 3559835) B3559835
theorem B3164297 : Blo 2109435 3164297 := bstep (se 2 (by rfl) ⟨1186611, by rfl⟩ : syracuseStep 3164297 = 2373223) B2373223
theorem B2109531 : Blo 2109435 2109531 := bstep (se 1 (by rfl) ⟨1582148, by rfl⟩ : syracuseStep 2109531 = 3164297) B3164297
theorem B10679525 : Blo 2109435 10679525 := bbase (se 4 (by rfl) ⟨1001205, by rfl⟩ : syracuseStep 10679525 = 2002411) (by norm_num)
theorem B7119683 : Blo 2109435 7119683 := bstep (se 1 (by rfl) ⟨5339762, by rfl⟩ : syracuseStep 7119683 = 10679525) B10679525
theorem B4746455 : Blo 2109435 4746455 := bstep (se 1 (by rfl) ⟨3559841, by rfl⟩ : syracuseStep 4746455 = 7119683) B7119683
theorem B3164303 : Blo 2109435 3164303 := bstep (se 1 (by rfl) ⟨2373227, by rfl⟩ : syracuseStep 3164303 = 4746455) B4746455
theorem B2109535 : Blo 2109435 2109535 := bstep (se 1 (by rfl) ⟨1582151, by rfl⟩ : syracuseStep 2109535 = 3164303) B3164303
theorem B3164309 : Blo 2109435 3164309 := bbase (se 6 (by rfl) ⟨74163, by rfl⟩ : syracuseStep 3164309 = 148327) (by norm_num)
theorem B2109539 : Blo 2109435 2109539 := bstep (se 1 (by rfl) ⟨1582154, by rfl⟩ : syracuseStep 2109539 = 3164309) B3164309
theorem B9010885 : Blo 2109435 9010885 := bbase (se 4 (by rfl) ⟨844770, by rfl⟩ : syracuseStep 9010885 = 1689541) (by norm_num)
theorem B12014513 : Blo 2109435 12014513 := bstep (se 2 (by rfl) ⟨4505442, by rfl⟩ : syracuseStep 12014513 = 9010885) B9010885
theorem B8009675 : Blo 2109435 8009675 := bstep (se 1 (by rfl) ⟨6007256, by rfl⟩ : syracuseStep 8009675 = 12014513) B12014513
theorem B5339783 : Blo 2109435 5339783 := bstep (se 1 (by rfl) ⟨4004837, by rfl⟩ : syracuseStep 5339783 = 8009675) B8009675
theorem B3559855 : Blo 2109435 3559855 := bstep (se 1 (by rfl) ⟨2669891, by rfl⟩ : syracuseStep 3559855 = 5339783) B5339783
theorem B4746473 : Blo 2109435 4746473 := bstep (se 2 (by rfl) ⟨1779927, by rfl⟩ : syracuseStep 4746473 = 3559855) B3559855
theorem B3164315 : Blo 2109435 3164315 := bstep (se 1 (by rfl) ⟨2373236, by rfl⟩ : syracuseStep 3164315 = 4746473) B4746473
theorem B2109543 : Blo 2109435 2109543 := bstep (se 1 (by rfl) ⟨1582157, by rfl⟩ : syracuseStep 2109543 = 3164315) B3164315
theorem B2373241 : Blo 2109435 2373241 := bbase (se 2 (by rfl) ⟨889965, by rfl⟩ : syracuseStep 2373241 = 1779931) (by norm_num)
theorem B3164321 : Blo 2109435 3164321 := bstep (se 2 (by rfl) ⟨1186620, by rfl⟩ : syracuseStep 3164321 = 2373241) B2373241
theorem B2109547 : Blo 2109435 2109547 := bstep (se 1 (by rfl) ⟨1582160, by rfl⟩ : syracuseStep 2109547 = 3164321) B3164321
theorem B38490005 : Blo 2109435 38490005 := bbase (se 6 (by rfl) ⟨902109, by rfl⟩ : syracuseStep 38490005 = 1804219) (by norm_num)
theorem B25660003 : Blo 2109435 25660003 := bstep (se 1 (by rfl) ⟨19245002, by rfl⟩ : syracuseStep 25660003 = 38490005) B38490005
theorem B34213337 : Blo 2109435 34213337 := bstep (se 2 (by rfl) ⟨12830001, by rfl⟩ : syracuseStep 34213337 = 25660003) B25660003
theorem B22808891 : Blo 2109435 22808891 := bstep (se 1 (by rfl) ⟨17106668, by rfl⟩ : syracuseStep 22808891 = 34213337) B34213337
theorem B15205927 : Blo 2109435 15205927 := bstep (se 1 (by rfl) ⟨11404445, by rfl⟩ : syracuseStep 15205927 = 22808891) B22808891
theorem B20274569 : Blo 2109435 20274569 := bstep (se 2 (by rfl) ⟨7602963, by rfl⟩ : syracuseStep 20274569 = 15205927) B15205927
theorem B13516379 : Blo 2109435 13516379 := bstep (se 1 (by rfl) ⟨10137284, by rfl⟩ : syracuseStep 13516379 = 20274569) B20274569
theorem B9010919 : Blo 2109435 9010919 := bstep (se 1 (by rfl) ⟨6758189, by rfl⟩ : syracuseStep 9010919 = 13516379) B13516379
theorem B6007279 : Blo 2109435 6007279 := bstep (se 1 (by rfl) ⟨4505459, by rfl⟩ : syracuseStep 6007279 = 9010919) B9010919
theorem B8009705 : Blo 2109435 8009705 := bstep (se 2 (by rfl) ⟨3003639, by rfl⟩ : syracuseStep 8009705 = 6007279) B6007279
theorem B5339803 : Blo 2109435 5339803 := bstep (se 1 (by rfl) ⟨4004852, by rfl⟩ : syracuseStep 5339803 = 8009705) B8009705
theorem B7119737 : Blo 2109435 7119737 := bstep (se 2 (by rfl) ⟨2669901, by rfl⟩ : syracuseStep 7119737 = 5339803) B5339803
theorem B4746491 : Blo 2109435 4746491 := bstep (se 1 (by rfl) ⟨3559868, by rfl⟩ : syracuseStep 4746491 = 7119737) B7119737
theorem B3164327 : Blo 2109435 3164327 := bstep (se 1 (by rfl) ⟨2373245, by rfl⟩ : syracuseStep 3164327 = 4746491) B4746491
theorem B2109551 : Blo 2109435 2109551 := bstep (se 1 (by rfl) ⟨1582163, by rfl⟩ : syracuseStep 2109551 = 3164327) B3164327
theorem B3164333 : Blo 2109435 3164333 := bbase (se 3 (by rfl) ⟨593312, by rfl⟩ : syracuseStep 3164333 = 1186625) (by norm_num)
theorem B2109555 : Blo 2109435 2109555 := bstep (se 1 (by rfl) ⟨1582166, by rfl⟩ : syracuseStep 2109555 = 3164333) B3164333
theorem B4746509 : Blo 2109435 4746509 := bbase (se 3 (by rfl) ⟨889970, by rfl⟩ : syracuseStep 4746509 = 1779941) (by norm_num)
theorem B3164339 : Blo 2109435 3164339 := bstep (se 1 (by rfl) ⟨2373254, by rfl⟩ : syracuseStep 3164339 = 4746509) B4746509
theorem B2109559 : Blo 2109435 2109559 := bstep (se 1 (by rfl) ⟨1582169, by rfl⟩ : syracuseStep 2109559 = 3164339) B3164339
theorem B2669917 : Blo 2109435 2669917 := bbase (se 3 (by rfl) ⟨500609, by rfl⟩ : syracuseStep 2669917 = 1001219) (by norm_num)
theorem B3559889 : Blo 2109435 3559889 := bstep (se 2 (by rfl) ⟨1334958, by rfl⟩ : syracuseStep 3559889 = 2669917) B2669917
theorem B2373259 : Blo 2109435 2373259 := bstep (se 1 (by rfl) ⟨1779944, by rfl⟩ : syracuseStep 2373259 = 3559889) B3559889
theorem B3164345 : Blo 2109435 3164345 := bstep (se 2 (by rfl) ⟨1186629, by rfl⟩ : syracuseStep 3164345 = 2373259) B2373259
theorem B2109563 : Blo 2109435 2109563 := bstep (se 1 (by rfl) ⟨1582172, by rfl⟩ : syracuseStep 2109563 = 3164345) B3164345
theorem B18021973 : Blo 2109435 18021973 := bbase (se 8 (by rfl) ⟨105597, by rfl⟩ : syracuseStep 18021973 = 211195) (by norm_num)
theorem B24029297 : Blo 2109435 24029297 := bstep (se 2 (by rfl) ⟨9010986, by rfl⟩ : syracuseStep 24029297 = 18021973) B18021973
theorem B16019531 : Blo 2109435 16019531 := bstep (se 1 (by rfl) ⟨12014648, by rfl⟩ : syracuseStep 16019531 = 24029297) B24029297
theorem B10679687 : Blo 2109435 10679687 := bstep (se 1 (by rfl) ⟨8009765, by rfl⟩ : syracuseStep 10679687 = 16019531) B16019531
theorem B7119791 : Blo 2109435 7119791 := bstep (se 1 (by rfl) ⟨5339843, by rfl⟩ : syracuseStep 7119791 = 10679687) B10679687
theorem B4746527 : Blo 2109435 4746527 := bstep (se 1 (by rfl) ⟨3559895, by rfl⟩ : syracuseStep 4746527 = 7119791) B7119791
theorem B3164351 : Blo 2109435 3164351 := bstep (se 1 (by rfl) ⟨2373263, by rfl⟩ : syracuseStep 3164351 = 4746527) B4746527
theorem B2109567 : Blo 2109435 2109567 := bstep (se 1 (by rfl) ⟨1582175, by rfl⟩ : syracuseStep 2109567 = 3164351) B3164351
theorem B3164357 : Blo 2109435 3164357 := bbase (se 4 (by rfl) ⟨296658, by rfl⟩ : syracuseStep 3164357 = 593317) (by norm_num)
theorem B2109571 : Blo 2109435 2109571 := bstep (se 1 (by rfl) ⟨1582178, by rfl⟩ : syracuseStep 2109571 = 3164357) B3164357
theorem B3559909 : Blo 2109435 3559909 := bbase (se 4 (by rfl) ⟨333741, by rfl⟩ : syracuseStep 3559909 = 667483) (by norm_num)
theorem B4746545 : Blo 2109435 4746545 := bstep (se 2 (by rfl) ⟨1779954, by rfl⟩ : syracuseStep 4746545 = 3559909) B3559909
theorem B3164363 : Blo 2109435 3164363 := bstep (se 1 (by rfl) ⟨2373272, by rfl⟩ : syracuseStep 3164363 = 4746545) B4746545
theorem B2109575 : Blo 2109435 2109575 := bstep (se 1 (by rfl) ⟨1582181, by rfl⟩ : syracuseStep 2109575 = 3164363) B3164363
theorem B2373277 : Blo 2109435 2373277 := bbase (se 3 (by rfl) ⟨444989, by rfl⟩ : syracuseStep 2373277 = 889979) (by norm_num)
theorem B3164369 : Blo 2109435 3164369 := bstep (se 2 (by rfl) ⟨1186638, by rfl⟩ : syracuseStep 3164369 = 2373277) B2373277
theorem B2109579 : Blo 2109435 2109579 := bstep (se 1 (by rfl) ⟨1582184, by rfl⟩ : syracuseStep 2109579 = 3164369) B3164369
theorem B7119845 : Blo 2109435 7119845 := bbase (se 4 (by rfl) ⟨667485, by rfl⟩ : syracuseStep 7119845 = 1334971) (by norm_num)
theorem B4746563 : Blo 2109435 4746563 := bstep (se 1 (by rfl) ⟨3559922, by rfl⟩ : syracuseStep 4746563 = 7119845) B7119845
theorem B3164375 : Blo 2109435 3164375 := bstep (se 1 (by rfl) ⟨2373281, by rfl⟩ : syracuseStep 3164375 = 4746563) B4746563
theorem B2109583 : Blo 2109435 2109583 := bstep (se 1 (by rfl) ⟨1582187, by rfl⟩ : syracuseStep 2109583 = 3164375) B3164375
theorem B3164381 : Blo 2109435 3164381 := bbase (se 3 (by rfl) ⟨593321, by rfl⟩ : syracuseStep 3164381 = 1186643) (by norm_num)
theorem B2109587 : Blo 2109435 2109587 := bstep (se 1 (by rfl) ⟨1582190, by rfl⟩ : syracuseStep 2109587 = 3164381) B3164381
theorem B4746581 : Blo 2109435 4746581 := bbase (se 11 (by rfl) ⟨3476, by rfl⟩ : syracuseStep 4746581 = 6953) (by norm_num)
theorem B3164387 : Blo 2109435 3164387 := bstep (se 1 (by rfl) ⟨2373290, by rfl⟩ : syracuseStep 3164387 = 4746581) B4746581
theorem B2109591 : Blo 2109435 2109591 := bstep (se 1 (by rfl) ⟨1582193, by rfl⟩ : syracuseStep 2109591 = 3164387) B3164387
theorem B2252777 : Blo 2109435 2252777 := bbase (se 2 (by rfl) ⟨844791, by rfl⟩ : syracuseStep 2252777 = 1689583) (by norm_num)
theorem B6007405 : Blo 2109435 6007405 := bstep (se 3 (by rfl) ⟨1126388, by rfl⟩ : syracuseStep 6007405 = 2252777) B2252777
theorem B8009873 : Blo 2109435 8009873 := bstep (se 2 (by rfl) ⟨3003702, by rfl⟩ : syracuseStep 8009873 = 6007405) B6007405
theorem B5339915 : Blo 2109435 5339915 := bstep (se 1 (by rfl) ⟨4004936, by rfl⟩ : syracuseStep 5339915 = 8009873) B8009873
theorem B3559943 : Blo 2109435 3559943 := bstep (se 1 (by rfl) ⟨2669957, by rfl⟩ : syracuseStep 3559943 = 5339915) B5339915
theorem B2373295 : Blo 2109435 2373295 := bstep (se 1 (by rfl) ⟨1779971, by rfl⟩ : syracuseStep 2373295 = 3559943) B3559943
theorem B3164393 : Blo 2109435 3164393 := bstep (se 2 (by rfl) ⟨1186647, by rfl⟩ : syracuseStep 3164393 = 2373295) B2373295
theorem B2109595 : Blo 2109435 2109595 := bstep (se 1 (by rfl) ⟨1582196, by rfl⟩ : syracuseStep 2109595 = 3164393) B3164393
theorem B7918597 : Blo 2109435 7918597 := bbase (se 4 (by rfl) ⟨742368, by rfl⟩ : syracuseStep 7918597 = 1484737) (by norm_num)
theorem B10558129 : Blo 2109435 10558129 := bstep (se 2 (by rfl) ⟨3959298, by rfl⟩ : syracuseStep 10558129 = 7918597) B7918597
theorem B14077505 : Blo 2109435 14077505 := bstep (se 2 (by rfl) ⟨5279064, by rfl⟩ : syracuseStep 14077505 = 10558129) B10558129
theorem B9385003 : Blo 2109435 9385003 := bstep (se 1 (by rfl) ⟨7038752, by rfl⟩ : syracuseStep 9385003 = 14077505) B14077505
theorem B12513337 : Blo 2109435 12513337 := bstep (se 2 (by rfl) ⟨4692501, by rfl⟩ : syracuseStep 12513337 = 9385003) B9385003
theorem B266951189 : Blo 2109435 266951189 := bstep (se 6 (by rfl) ⟨6256668, by rfl⟩ : syracuseStep 266951189 = 12513337) B12513337
theorem B177967459 : Blo 2109435 177967459 := bstep (se 1 (by rfl) ⟨133475594, by rfl⟩ : syracuseStep 177967459 = 266951189) B266951189
theorem B237289945 : Blo 2109435 237289945 := bstep (se 2 (by rfl) ⟨88983729, by rfl⟩ : syracuseStep 237289945 = 177967459) B177967459
theorem B316386593 : Blo 2109435 316386593 := bstep (se 2 (by rfl) ⟨118644972, by rfl⟩ : syracuseStep 316386593 = 237289945) B237289945
theorem B210924395 : Blo 2109435 210924395 := bstep (se 1 (by rfl) ⟨158193296, by rfl⟩ : syracuseStep 210924395 = 316386593) B316386593
theorem B140616263 : Blo 2109435 140616263 := bstep (se 1 (by rfl) ⟨105462197, by rfl⟩ : syracuseStep 140616263 = 210924395) B210924395
theorem B374976701 : Blo 2109435 374976701 := bstep (se 3 (by rfl) ⟨70308131, by rfl⟩ : syracuseStep 374976701 = 140616263) B140616263
theorem B249984467 : Blo 2109435 249984467 := bstep (se 1 (by rfl) ⟨187488350, by rfl⟩ : syracuseStep 249984467 = 374976701) B374976701
theorem B166656311 : Blo 2109435 166656311 := bstep (se 1 (by rfl) ⟨124992233, by rfl⟩ : syracuseStep 166656311 = 249984467) B249984467
theorem B111104207 : Blo 2109435 111104207 := bstep (se 1 (by rfl) ⟨83328155, by rfl⟩ : syracuseStep 111104207 = 166656311) B166656311
theorem B74069471 : Blo 2109435 74069471 := bstep (se 1 (by rfl) ⟨55552103, by rfl⟩ : syracuseStep 74069471 = 111104207) B111104207
theorem B49379647 : Blo 2109435 49379647 := bstep (se 1 (by rfl) ⟨37034735, by rfl⟩ : syracuseStep 49379647 = 74069471) B74069471
theorem B1053432469 : Blo 2109435 1053432469 := bstep (se 6 (by rfl) ⟨24689823, by rfl⟩ : syracuseStep 1053432469 = 49379647) B49379647
theorem B1404576625 : Blo 2109435 1404576625 := bstep (se 2 (by rfl) ⟨526716234, by rfl⟩ : syracuseStep 1404576625 = 1053432469) B1053432469
theorem B1872768833 : Blo 2109435 1872768833 := bstep (se 2 (by rfl) ⟨702288312, by rfl⟩ : syracuseStep 1872768833 = 1404576625) B1404576625
theorem B1248512555 : Blo 2109435 1248512555 := bstep (se 1 (by rfl) ⟨936384416, by rfl⟩ : syracuseStep 1248512555 = 1872768833) B1872768833
theorem B832341703 : Blo 2109435 832341703 := bstep (se 1 (by rfl) ⟨624256277, by rfl⟩ : syracuseStep 832341703 = 1248512555) B1248512555
theorem B1109788937 : Blo 2109435 1109788937 := bstep (se 2 (by rfl) ⟨416170851, by rfl⟩ : syracuseStep 1109788937 = 832341703) B832341703
theorem B739859291 : Blo 2109435 739859291 := bstep (se 1 (by rfl) ⟨554894468, by rfl⟩ : syracuseStep 739859291 = 1109788937) B1109788937
theorem B493239527 : Blo 2109435 493239527 := bstep (se 1 (by rfl) ⟨369929645, by rfl⟩ : syracuseStep 493239527 = 739859291) B739859291
theorem B328826351 : Blo 2109435 328826351 := bstep (se 1 (by rfl) ⟨246619763, by rfl⟩ : syracuseStep 328826351 = 493239527) B493239527
theorem B876870269 : Blo 2109435 876870269 := bstep (se 3 (by rfl) ⟨164413175, by rfl⟩ : syracuseStep 876870269 = 328826351) B328826351
theorem B584580179 : Blo 2109435 584580179 := bstep (se 1 (by rfl) ⟨438435134, by rfl⟩ : syracuseStep 584580179 = 876870269) B876870269
theorem B389720119 : Blo 2109435 389720119 := bstep (se 1 (by rfl) ⟨292290089, by rfl⟩ : syracuseStep 389720119 = 584580179) B584580179
theorem B519626825 : Blo 2109435 519626825 := bstep (se 2 (by rfl) ⟨194860059, by rfl⟩ : syracuseStep 519626825 = 389720119) B389720119
theorem B346417883 : Blo 2109435 346417883 := bstep (se 1 (by rfl) ⟨259813412, by rfl⟩ : syracuseStep 346417883 = 519626825) B519626825
theorem B230945255 : Blo 2109435 230945255 := bstep (se 1 (by rfl) ⟨173208941, by rfl⟩ : syracuseStep 230945255 = 346417883) B346417883
theorem B153963503 : Blo 2109435 153963503 := bstep (se 1 (by rfl) ⟨115472627, by rfl⟩ : syracuseStep 153963503 = 230945255) B230945255
theorem B102642335 : Blo 2109435 102642335 := bstep (se 1 (by rfl) ⟨76981751, by rfl⟩ : syracuseStep 102642335 = 153963503) B153963503
theorem B68428223 : Blo 2109435 68428223 := bstep (se 1 (by rfl) ⟨51321167, by rfl⟩ : syracuseStep 68428223 = 102642335) B102642335
theorem B45618815 : Blo 2109435 45618815 := bstep (se 1 (by rfl) ⟨34214111, by rfl⟩ : syracuseStep 45618815 = 68428223) B68428223
theorem B30412543 : Blo 2109435 30412543 := bstep (se 1 (by rfl) ⟨22809407, by rfl⟩ : syracuseStep 30412543 = 45618815) B45618815
theorem B40550057 : Blo 2109435 40550057 := bstep (se 2 (by rfl) ⟨15206271, by rfl⟩ : syracuseStep 40550057 = 30412543) B30412543
theorem B27033371 : Blo 2109435 27033371 := bstep (se 1 (by rfl) ⟨20275028, by rfl⟩ : syracuseStep 27033371 = 40550057) B40550057
theorem B18022247 : Blo 2109435 18022247 := bstep (se 1 (by rfl) ⟨13516685, by rfl⟩ : syracuseStep 18022247 = 27033371) B27033371
theorem B12014831 : Blo 2109435 12014831 := bstep (se 1 (by rfl) ⟨9011123, by rfl⟩ : syracuseStep 12014831 = 18022247) B18022247
theorem B8009887 : Blo 2109435 8009887 := bstep (se 1 (by rfl) ⟨6007415, by rfl⟩ : syracuseStep 8009887 = 12014831) B12014831
theorem B10679849 : Blo 2109435 10679849 := bstep (se 2 (by rfl) ⟨4004943, by rfl⟩ : syracuseStep 10679849 = 8009887) B8009887
theorem B7119899 : Blo 2109435 7119899 := bstep (se 1 (by rfl) ⟨5339924, by rfl⟩ : syracuseStep 7119899 = 10679849) B10679849
theorem B4746599 : Blo 2109435 4746599 := bstep (se 1 (by rfl) ⟨3559949, by rfl⟩ : syracuseStep 4746599 = 7119899) B7119899
theorem B3164399 : Blo 2109435 3164399 := bstep (se 1 (by rfl) ⟨2373299, by rfl⟩ : syracuseStep 3164399 = 4746599) B4746599
theorem B2109599 : Blo 2109435 2109599 := bstep (se 1 (by rfl) ⟨1582199, by rfl⟩ : syracuseStep 2109599 = 3164399) B3164399
theorem B3164405 : Blo 2109435 3164405 := bbase (se 5 (by rfl) ⟨148331, by rfl⟩ : syracuseStep 3164405 = 296663) (by norm_num)
theorem B2109603 : Blo 2109435 2109603 := bstep (se 1 (by rfl) ⟨1582202, by rfl⟩ : syracuseStep 2109603 = 3164405) B3164405
theorem B3295709 : Blo 2109435 3295709 := bbase (se 3 (by rfl) ⟨617945, by rfl⟩ : syracuseStep 3295709 = 1235891) (by norm_num)
theorem B2197139 : Blo 2109435 2197139 := bstep (se 1 (by rfl) ⟨1647854, by rfl⟩ : syracuseStep 2197139 = 3295709) B3295709
theorem B5859037 : Blo 2109435 5859037 := bstep (se 3 (by rfl) ⟨1098569, by rfl⟩ : syracuseStep 5859037 = 2197139) B2197139
theorem B7812049 : Blo 2109435 7812049 := bstep (se 2 (by rfl) ⟨2929518, by rfl⟩ : syracuseStep 7812049 = 5859037) B5859037
theorem B10416065 : Blo 2109435 10416065 := bstep (se 2 (by rfl) ⟨3906024, by rfl⟩ : syracuseStep 10416065 = 7812049) B7812049
theorem B111104693 : Blo 2109435 111104693 := bstep (se 5 (by rfl) ⟨5208032, by rfl⟩ : syracuseStep 111104693 = 10416065) B10416065
theorem B74069795 : Blo 2109435 74069795 := bstep (se 1 (by rfl) ⟨55552346, by rfl⟩ : syracuseStep 74069795 = 111104693) B111104693
theorem B49379863 : Blo 2109435 49379863 := bstep (se 1 (by rfl) ⟨37034897, by rfl⟩ : syracuseStep 49379863 = 74069795) B74069795
theorem B65839817 : Blo 2109435 65839817 := bstep (se 2 (by rfl) ⟨24689931, by rfl⟩ : syracuseStep 65839817 = 49379863) B49379863
theorem B43893211 : Blo 2109435 43893211 := bstep (se 1 (by rfl) ⟨32919908, by rfl⟩ : syracuseStep 43893211 = 65839817) B65839817
theorem B58524281 : Blo 2109435 58524281 := bstep (se 2 (by rfl) ⟨21946605, by rfl⟩ : syracuseStep 58524281 = 43893211) B43893211
theorem B39016187 : Blo 2109435 39016187 := bstep (se 1 (by rfl) ⟨29262140, by rfl⟩ : syracuseStep 39016187 = 58524281) B58524281
theorem B26010791 : Blo 2109435 26010791 := bstep (se 1 (by rfl) ⟨19508093, by rfl⟩ : syracuseStep 26010791 = 39016187) B39016187
theorem B17340527 : Blo 2109435 17340527 := bstep (se 1 (by rfl) ⟨13005395, by rfl⟩ : syracuseStep 17340527 = 26010791) B26010791
theorem B46241405 : Blo 2109435 46241405 := bstep (se 3 (by rfl) ⟨8670263, by rfl⟩ : syracuseStep 46241405 = 17340527) B17340527
theorem B30827603 : Blo 2109435 30827603 := bstep (se 1 (by rfl) ⟨23120702, by rfl⟩ : syracuseStep 30827603 = 46241405) B46241405
theorem B20551735 : Blo 2109435 20551735 := bstep (se 1 (by rfl) ⟨15413801, by rfl⟩ : syracuseStep 20551735 = 30827603) B30827603
theorem B27402313 : Blo 2109435 27402313 := bstep (se 2 (by rfl) ⟨10275867, by rfl⟩ : syracuseStep 27402313 = 20551735) B20551735
theorem B36536417 : Blo 2109435 36536417 := bstep (se 2 (by rfl) ⟨13701156, by rfl⟩ : syracuseStep 36536417 = 27402313) B27402313
theorem B24357611 : Blo 2109435 24357611 := bstep (se 1 (by rfl) ⟨18268208, by rfl⟩ : syracuseStep 24357611 = 36536417) B36536417
theorem B16238407 : Blo 2109435 16238407 := bstep (se 1 (by rfl) ⟨12178805, by rfl⟩ : syracuseStep 16238407 = 24357611) B24357611
theorem B21651209 : Blo 2109435 21651209 := bstep (se 2 (by rfl) ⟨8119203, by rfl⟩ : syracuseStep 21651209 = 16238407) B16238407
theorem B14434139 : Blo 2109435 14434139 := bstep (se 1 (by rfl) ⟨10825604, by rfl⟩ : syracuseStep 14434139 = 21651209) B21651209
theorem B9622759 : Blo 2109435 9622759 := bstep (se 1 (by rfl) ⟨7217069, by rfl⟩ : syracuseStep 9622759 = 14434139) B14434139
theorem B12830345 : Blo 2109435 12830345 := bstep (se 2 (by rfl) ⟨4811379, by rfl⟩ : syracuseStep 12830345 = 9622759) B9622759
theorem B8553563 : Blo 2109435 8553563 := bstep (se 1 (by rfl) ⟨6415172, by rfl⟩ : syracuseStep 8553563 = 12830345) B12830345
theorem B5702375 : Blo 2109435 5702375 := bstep (se 1 (by rfl) ⟨4276781, by rfl⟩ : syracuseStep 5702375 = 8553563) B8553563
theorem B3801583 : Blo 2109435 3801583 := bstep (se 1 (by rfl) ⟨2851187, by rfl⟩ : syracuseStep 3801583 = 5702375) B5702375
theorem B20275109 : Blo 2109435 20275109 := bstep (se 4 (by rfl) ⟨1900791, by rfl⟩ : syracuseStep 20275109 = 3801583) B3801583
theorem B13516739 : Blo 2109435 13516739 := bstep (se 1 (by rfl) ⟨10137554, by rfl⟩ : syracuseStep 13516739 = 20275109) B20275109
theorem B9011159 : Blo 2109435 9011159 := bstep (se 1 (by rfl) ⟨6758369, by rfl⟩ : syracuseStep 9011159 = 13516739) B13516739
theorem B6007439 : Blo 2109435 6007439 := bstep (se 1 (by rfl) ⟨4505579, by rfl⟩ : syracuseStep 6007439 = 9011159) B9011159
theorem B4004959 : Blo 2109435 4004959 := bstep (se 1 (by rfl) ⟨3003719, by rfl⟩ : syracuseStep 4004959 = 6007439) B6007439
theorem B5339945 : Blo 2109435 5339945 := bstep (se 2 (by rfl) ⟨2002479, by rfl⟩ : syracuseStep 5339945 = 4004959) B4004959
theorem B3559963 : Blo 2109435 3559963 := bstep (se 1 (by rfl) ⟨2669972, by rfl⟩ : syracuseStep 3559963 = 5339945) B5339945
theorem B4746617 : Blo 2109435 4746617 := bstep (se 2 (by rfl) ⟨1779981, by rfl⟩ : syracuseStep 4746617 = 3559963) B3559963
theorem B3164411 : Blo 2109435 3164411 := bstep (se 1 (by rfl) ⟨2373308, by rfl⟩ : syracuseStep 3164411 = 4746617) B4746617
theorem B2109607 : Blo 2109435 2109607 := bstep (se 1 (by rfl) ⟨1582205, by rfl⟩ : syracuseStep 2109607 = 3164411) B3164411
theorem B2373313 : Blo 2109435 2373313 := bbase (se 2 (by rfl) ⟨889992, by rfl⟩ : syracuseStep 2373313 = 1779985) (by norm_num)
theorem B3164417 : Blo 2109435 3164417 := bstep (se 2 (by rfl) ⟨1186656, by rfl⟩ : syracuseStep 3164417 = 2373313) B2373313
theorem B2109611 : Blo 2109435 2109611 := bstep (se 1 (by rfl) ⟨1582208, by rfl⟩ : syracuseStep 2109611 = 3164417) B3164417
theorem B5339965 : Blo 2109435 5339965 := bbase (se 3 (by rfl) ⟨1001243, by rfl⟩ : syracuseStep 5339965 = 2002487) (by norm_num)
theorem B7119953 : Blo 2109435 7119953 := bstep (se 2 (by rfl) ⟨2669982, by rfl⟩ : syracuseStep 7119953 = 5339965) B5339965
theorem B4746635 : Blo 2109435 4746635 := bstep (se 1 (by rfl) ⟨3559976, by rfl⟩ : syracuseStep 4746635 = 7119953) B7119953
theorem B3164423 : Blo 2109435 3164423 := bstep (se 1 (by rfl) ⟨2373317, by rfl⟩ : syracuseStep 3164423 = 4746635) B4746635
theorem B2109615 : Blo 2109435 2109615 := bstep (se 1 (by rfl) ⟨1582211, by rfl⟩ : syracuseStep 2109615 = 3164423) B3164423
theorem B3164429 : Blo 2109435 3164429 := bbase (se 3 (by rfl) ⟨593330, by rfl⟩ : syracuseStep 3164429 = 1186661) (by norm_num)
theorem B2109619 : Blo 2109435 2109619 := bstep (se 1 (by rfl) ⟨1582214, by rfl⟩ : syracuseStep 2109619 = 3164429) B3164429
theorem B4746653 : Blo 2109435 4746653 := bbase (se 3 (by rfl) ⟨889997, by rfl⟩ : syracuseStep 4746653 = 1779995) (by norm_num)
theorem B3164435 : Blo 2109435 3164435 := bstep (se 1 (by rfl) ⟨2373326, by rfl⟩ : syracuseStep 3164435 = 4746653) B4746653
theorem B2109623 : Blo 2109435 2109623 := bstep (se 1 (by rfl) ⟨1582217, by rfl⟩ : syracuseStep 2109623 = 3164435) B3164435
theorem B3559997 : Blo 2109435 3559997 := bbase (se 3 (by rfl) ⟨667499, by rfl⟩ : syracuseStep 3559997 = 1334999) (by norm_num)
theorem B2373331 : Blo 2109435 2373331 := bstep (se 1 (by rfl) ⟨1779998, by rfl⟩ : syracuseStep 2373331 = 3559997) B3559997
theorem B3164441 : Blo 2109435 3164441 := bstep (se 2 (by rfl) ⟨1186665, by rfl⟩ : syracuseStep 3164441 = 2373331) B2373331
theorem B2109627 : Blo 2109435 2109627 := bstep (se 1 (by rfl) ⟨1582220, by rfl⟩ : syracuseStep 2109627 = 3164441) B3164441
theorem B7603253 : Blo 2109435 7603253 := bbase (se 5 (by rfl) ⟨356402, by rfl⟩ : syracuseStep 7603253 = 712805) (by norm_num)
theorem B5068835 : Blo 2109435 5068835 := bstep (se 1 (by rfl) ⟨3801626, by rfl⟩ : syracuseStep 5068835 = 7603253) B7603253
theorem B3379223 : Blo 2109435 3379223 := bstep (se 1 (by rfl) ⟨2534417, by rfl⟩ : syracuseStep 3379223 = 5068835) B5068835
theorem B2252815 : Blo 2109435 2252815 := bstep (se 1 (by rfl) ⟨1689611, by rfl⟩ : syracuseStep 2252815 = 3379223) B3379223
theorem B12015013 : Blo 2109435 12015013 := bstep (se 4 (by rfl) ⟨1126407, by rfl⟩ : syracuseStep 12015013 = 2252815) B2252815
theorem B16020017 : Blo 2109435 16020017 := bstep (se 2 (by rfl) ⟨6007506, by rfl⟩ : syracuseStep 16020017 = 12015013) B12015013
theorem B10680011 : Blo 2109435 10680011 := bstep (se 1 (by rfl) ⟨8010008, by rfl⟩ : syracuseStep 10680011 = 16020017) B16020017
theorem B7120007 : Blo 2109435 7120007 := bstep (se 1 (by rfl) ⟨5340005, by rfl⟩ : syracuseStep 7120007 = 10680011) B10680011
theorem B4746671 : Blo 2109435 4746671 := bstep (se 1 (by rfl) ⟨3560003, by rfl⟩ : syracuseStep 4746671 = 7120007) B7120007
theorem B3164447 : Blo 2109435 3164447 := bstep (se 1 (by rfl) ⟨2373335, by rfl⟩ : syracuseStep 3164447 = 4746671) B4746671
theorem B2109631 : Blo 2109435 2109631 := bstep (se 1 (by rfl) ⟨1582223, by rfl⟩ : syracuseStep 2109631 = 3164447) B3164447
theorem B3164453 : Blo 2109435 3164453 := bbase (se 4 (by rfl) ⟨296667, by rfl⟩ : syracuseStep 3164453 = 593335) (by norm_num)
theorem B2109635 : Blo 2109435 2109635 := bstep (se 1 (by rfl) ⟨1582226, by rfl⟩ : syracuseStep 2109635 = 3164453) B3164453
theorem B2670013 : Blo 2109435 2670013 := bbase (se 3 (by rfl) ⟨500627, by rfl⟩ : syracuseStep 2670013 = 1001255) (by norm_num)
theorem B3560017 : Blo 2109435 3560017 := bstep (se 2 (by rfl) ⟨1335006, by rfl⟩ : syracuseStep 3560017 = 2670013) B2670013
theorem B4746689 : Blo 2109435 4746689 := bstep (se 2 (by rfl) ⟨1780008, by rfl⟩ : syracuseStep 4746689 = 3560017) B3560017
theorem B3164459 : Blo 2109435 3164459 := bstep (se 1 (by rfl) ⟨2373344, by rfl⟩ : syracuseStep 3164459 = 4746689) B4746689
theorem B2109639 : Blo 2109435 2109639 := bstep (se 1 (by rfl) ⟨1582229, by rfl⟩ : syracuseStep 2109639 = 3164459) B3164459
theorem B2373349 : Blo 2109435 2373349 := bbase (se 4 (by rfl) ⟨222501, by rfl⟩ : syracuseStep 2373349 = 445003) (by norm_num)
theorem B3164465 : Blo 2109435 3164465 := bstep (se 2 (by rfl) ⟨1186674, by rfl⟩ : syracuseStep 3164465 = 2373349) B2373349
theorem B2109643 : Blo 2109435 2109643 := bstep (se 1 (by rfl) ⟨1582232, by rfl⟩ : syracuseStep 2109643 = 3164465) B3164465
theorem B2534437 : Blo 2109435 2534437 := bbase (se 4 (by rfl) ⟨237603, by rfl⟩ : syracuseStep 2534437 = 475207) (by norm_num)
theorem B3379249 : Blo 2109435 3379249 := bstep (se 2 (by rfl) ⟨1267218, by rfl⟩ : syracuseStep 3379249 = 2534437) B2534437
theorem B4505665 : Blo 2109435 4505665 := bstep (se 2 (by rfl) ⟨1689624, by rfl⟩ : syracuseStep 4505665 = 3379249) B3379249
theorem B6007553 : Blo 2109435 6007553 := bstep (se 2 (by rfl) ⟨2252832, by rfl⟩ : syracuseStep 6007553 = 4505665) B4505665
theorem B4005035 : Blo 2109435 4005035 := bstep (se 1 (by rfl) ⟨3003776, by rfl⟩ : syracuseStep 4005035 = 6007553) B6007553
theorem B2670023 : Blo 2109435 2670023 := bstep (se 1 (by rfl) ⟨2002517, by rfl⟩ : syracuseStep 2670023 = 4005035) B4005035
theorem B7120061 : Blo 2109435 7120061 := bstep (se 3 (by rfl) ⟨1335011, by rfl⟩ : syracuseStep 7120061 = 2670023) B2670023
theorem B4746707 : Blo 2109435 4746707 := bstep (se 1 (by rfl) ⟨3560030, by rfl⟩ : syracuseStep 4746707 = 7120061) B7120061
theorem B3164471 : Blo 2109435 3164471 := bstep (se 1 (by rfl) ⟨2373353, by rfl⟩ : syracuseStep 3164471 = 4746707) B4746707
theorem B2109647 : Blo 2109435 2109647 := bstep (se 1 (by rfl) ⟨1582235, by rfl⟩ : syracuseStep 2109647 = 3164471) B3164471
theorem B3164477 : Blo 2109435 3164477 := bbase (se 3 (by rfl) ⟨593339, by rfl⟩ : syracuseStep 3164477 = 1186679) (by norm_num)
theorem B2109651 : Blo 2109435 2109651 := bstep (se 1 (by rfl) ⟨1582238, by rfl⟩ : syracuseStep 2109651 = 3164477) B3164477
theorem B4746725 : Blo 2109435 4746725 := bbase (se 4 (by rfl) ⟨445005, by rfl⟩ : syracuseStep 4746725 = 890011) (by norm_num)
theorem B3164483 : Blo 2109435 3164483 := bstep (se 1 (by rfl) ⟨2373362, by rfl⟩ : syracuseStep 3164483 = 4746725) B4746725
theorem B2109655 : Blo 2109435 2109655 := bstep (se 1 (by rfl) ⟨1582241, by rfl⟩ : syracuseStep 2109655 = 3164483) B3164483
theorem B5340077 : Blo 2109435 5340077 := bbase (se 3 (by rfl) ⟨1001264, by rfl⟩ : syracuseStep 5340077 = 2002529) (by norm_num)
theorem B3560051 : Blo 2109435 3560051 := bstep (se 1 (by rfl) ⟨2670038, by rfl⟩ : syracuseStep 3560051 = 5340077) B5340077
theorem B2373367 : Blo 2109435 2373367 := bstep (se 1 (by rfl) ⟨1780025, by rfl⟩ : syracuseStep 2373367 = 3560051) B3560051
theorem B3164489 : Blo 2109435 3164489 := bstep (se 2 (by rfl) ⟨1186683, by rfl⟩ : syracuseStep 3164489 = 2373367) B2373367
theorem B2109659 : Blo 2109435 2109659 := bstep (se 1 (by rfl) ⟨1582244, by rfl⟩ : syracuseStep 2109659 = 3164489) B3164489
theorem B6758549 : Blo 2109435 6758549 := bbase (se 6 (by rfl) ⟨158403, by rfl⟩ : syracuseStep 6758549 = 316807) (by norm_num)
theorem B4505699 : Blo 2109435 4505699 := bstep (se 1 (by rfl) ⟨3379274, by rfl⟩ : syracuseStep 4505699 = 6758549) B6758549
theorem B3003799 : Blo 2109435 3003799 := bstep (se 1 (by rfl) ⟨2252849, by rfl⟩ : syracuseStep 3003799 = 4505699) B4505699
theorem B4005065 : Blo 2109435 4005065 := bstep (se 2 (by rfl) ⟨1501899, by rfl⟩ : syracuseStep 4005065 = 3003799) B3003799
theorem B10680173 : Blo 2109435 10680173 := bstep (se 3 (by rfl) ⟨2002532, by rfl⟩ : syracuseStep 10680173 = 4005065) B4005065
theorem B7120115 : Blo 2109435 7120115 := bstep (se 1 (by rfl) ⟨5340086, by rfl⟩ : syracuseStep 7120115 = 10680173) B10680173
theorem B4746743 : Blo 2109435 4746743 := bstep (se 1 (by rfl) ⟨3560057, by rfl⟩ : syracuseStep 4746743 = 7120115) B7120115
theorem B3164495 : Blo 2109435 3164495 := bstep (se 1 (by rfl) ⟨2373371, by rfl⟩ : syracuseStep 3164495 = 4746743) B4746743
theorem B2109663 : Blo 2109435 2109663 := bstep (se 1 (by rfl) ⟨1582247, by rfl⟩ : syracuseStep 2109663 = 3164495) B3164495
theorem B3164501 : Blo 2109435 3164501 := bbase (se 10 (by rfl) ⟨4635, by rfl⟩ : syracuseStep 3164501 = 9271) (by norm_num)
theorem B2109667 : Blo 2109435 2109667 := bstep (se 1 (by rfl) ⟨1582250, by rfl⟩ : syracuseStep 2109667 = 3164501) B3164501
theorem B6007621 : Blo 2109435 6007621 := bbase (se 4 (by rfl) ⟨563214, by rfl⟩ : syracuseStep 6007621 = 1126429) (by norm_num)
theorem B8010161 : Blo 2109435 8010161 := bstep (se 2 (by rfl) ⟨3003810, by rfl⟩ : syracuseStep 8010161 = 6007621) B6007621
theorem B5340107 : Blo 2109435 5340107 := bstep (se 1 (by rfl) ⟨4005080, by rfl⟩ : syracuseStep 5340107 = 8010161) B8010161
theorem B3560071 : Blo 2109435 3560071 := bstep (se 1 (by rfl) ⟨2670053, by rfl⟩ : syracuseStep 3560071 = 5340107) B5340107
theorem B4746761 : Blo 2109435 4746761 := bstep (se 2 (by rfl) ⟨1780035, by rfl⟩ : syracuseStep 4746761 = 3560071) B3560071
theorem B3164507 : Blo 2109435 3164507 := bstep (se 1 (by rfl) ⟨2373380, by rfl⟩ : syracuseStep 3164507 = 4746761) B4746761
theorem B2109671 : Blo 2109435 2109671 := bstep (se 1 (by rfl) ⟨1582253, by rfl⟩ : syracuseStep 2109671 = 3164507) B3164507
theorem B2373385 : Blo 2109435 2373385 := bbase (se 2 (by rfl) ⟨890019, by rfl⟩ : syracuseStep 2373385 = 1780039) (by norm_num)
theorem B3164513 : Blo 2109435 3164513 := bstep (se 2 (by rfl) ⟨1186692, by rfl⟩ : syracuseStep 3164513 = 2373385) B2373385
theorem B2109675 : Blo 2109435 2109675 := bstep (se 1 (by rfl) ⟨1582256, by rfl⟩ : syracuseStep 2109675 = 3164513) B3164513
theorem B10825973 : Blo 2109435 10825973 := bbase (se 5 (by rfl) ⟨507467, by rfl⟩ : syracuseStep 10825973 = 1014935) (by norm_num)
theorem B7217315 : Blo 2109435 7217315 := bstep (se 1 (by rfl) ⟨5412986, by rfl⟩ : syracuseStep 7217315 = 10825973) B10825973
theorem B4811543 : Blo 2109435 4811543 := bstep (se 1 (by rfl) ⟨3608657, by rfl⟩ : syracuseStep 4811543 = 7217315) B7217315
theorem B3207695 : Blo 2109435 3207695 := bstep (se 1 (by rfl) ⟨2405771, by rfl⟩ : syracuseStep 3207695 = 4811543) B4811543
theorem B8553853 : Blo 2109435 8553853 := bstep (se 3 (by rfl) ⟨1603847, by rfl⟩ : syracuseStep 8553853 = 3207695) B3207695
theorem B11405137 : Blo 2109435 11405137 := bstep (se 2 (by rfl) ⟨4276926, by rfl⟩ : syracuseStep 11405137 = 8553853) B8553853
theorem B15206849 : Blo 2109435 15206849 := bstep (se 2 (by rfl) ⟨5702568, by rfl⟩ : syracuseStep 15206849 = 11405137) B11405137
theorem B10137899 : Blo 2109435 10137899 := bstep (se 1 (by rfl) ⟨7603424, by rfl⟩ : syracuseStep 10137899 = 15206849) B15206849
theorem B27034397 : Blo 2109435 27034397 := bstep (se 3 (by rfl) ⟨5068949, by rfl⟩ : syracuseStep 27034397 = 10137899) B10137899
theorem B18022931 : Blo 2109435 18022931 := bstep (se 1 (by rfl) ⟨13517198, by rfl⟩ : syracuseStep 18022931 = 27034397) B27034397
theorem B12015287 : Blo 2109435 12015287 := bstep (se 1 (by rfl) ⟨9011465, by rfl⟩ : syracuseStep 12015287 = 18022931) B18022931
theorem B8010191 : Blo 2109435 8010191 := bstep (se 1 (by rfl) ⟨6007643, by rfl⟩ : syracuseStep 8010191 = 12015287) B12015287
theorem B5340127 : Blo 2109435 5340127 := bstep (se 1 (by rfl) ⟨4005095, by rfl⟩ : syracuseStep 5340127 = 8010191) B8010191
theorem B7120169 : Blo 2109435 7120169 := bstep (se 2 (by rfl) ⟨2670063, by rfl⟩ : syracuseStep 7120169 = 5340127) B5340127
theorem B4746779 : Blo 2109435 4746779 := bstep (se 1 (by rfl) ⟨3560084, by rfl⟩ : syracuseStep 4746779 = 7120169) B7120169
theorem B3164519 : Blo 2109435 3164519 := bstep (se 1 (by rfl) ⟨2373389, by rfl⟩ : syracuseStep 3164519 = 4746779) B4746779
theorem B2109679 : Blo 2109435 2109679 := bstep (se 1 (by rfl) ⟨1582259, by rfl⟩ : syracuseStep 2109679 = 3164519) B3164519
theorem B3164525 : Blo 2109435 3164525 := bbase (se 3 (by rfl) ⟨593348, by rfl⟩ : syracuseStep 3164525 = 1186697) (by norm_num)
theorem B2109683 : Blo 2109435 2109683 := bstep (se 1 (by rfl) ⟨1582262, by rfl⟩ : syracuseStep 2109683 = 3164525) B3164525
theorem B4746797 : Blo 2109435 4746797 := bbase (se 3 (by rfl) ⟨890024, by rfl⟩ : syracuseStep 4746797 = 1780049) (by norm_num)
theorem B3164531 : Blo 2109435 3164531 := bstep (se 1 (by rfl) ⟨2373398, by rfl⟩ : syracuseStep 3164531 = 4746797) B4746797
theorem B2109687 : Blo 2109435 2109687 := bstep (se 1 (by rfl) ⟨1582265, by rfl⟩ : syracuseStep 2109687 = 3164531) B3164531
theorem B2283617 : Blo 2109435 2283617 := bbase (se 2 (by rfl) ⟨856356, by rfl⟩ : syracuseStep 2283617 = 1712713) (by norm_num)
theorem B6089645 : Blo 2109435 6089645 := bstep (se 3 (by rfl) ⟨1141808, by rfl⟩ : syracuseStep 6089645 = 2283617) B2283617
theorem B4059763 : Blo 2109435 4059763 := bstep (se 1 (by rfl) ⟨3044822, by rfl⟩ : syracuseStep 4059763 = 6089645) B6089645
theorem B86608277 : Blo 2109435 86608277 := bstep (se 6 (by rfl) ⟨2029881, by rfl⟩ : syracuseStep 86608277 = 4059763) B4059763
theorem B57738851 : Blo 2109435 57738851 := bstep (se 1 (by rfl) ⟨43304138, by rfl⟩ : syracuseStep 57738851 = 86608277) B86608277
theorem B38492567 : Blo 2109435 38492567 := bstep (se 1 (by rfl) ⟨28869425, by rfl⟩ : syracuseStep 38492567 = 57738851) B57738851
theorem B25661711 : Blo 2109435 25661711 := bstep (se 1 (by rfl) ⟨19246283, by rfl⟩ : syracuseStep 25661711 = 38492567) B38492567
theorem B68431229 : Blo 2109435 68431229 := bstep (se 3 (by rfl) ⟨12830855, by rfl⟩ : syracuseStep 68431229 = 25661711) B25661711
theorem B45620819 : Blo 2109435 45620819 := bstep (se 1 (by rfl) ⟨34215614, by rfl⟩ : syracuseStep 45620819 = 68431229) B68431229
theorem B30413879 : Blo 2109435 30413879 := bstep (se 1 (by rfl) ⟨22810409, by rfl⟩ : syracuseStep 30413879 = 45620819) B45620819
theorem B20275919 : Blo 2109435 20275919 := bstep (se 1 (by rfl) ⟨15206939, by rfl⟩ : syracuseStep 20275919 = 30413879) B30413879
theorem B13517279 : Blo 2109435 13517279 := bstep (se 1 (by rfl) ⟨10137959, by rfl⟩ : syracuseStep 13517279 = 20275919) B20275919
theorem B9011519 : Blo 2109435 9011519 := bstep (se 1 (by rfl) ⟨6758639, by rfl⟩ : syracuseStep 9011519 = 13517279) B13517279
theorem B6007679 : Blo 2109435 6007679 := bstep (se 1 (by rfl) ⟨4505759, by rfl⟩ : syracuseStep 6007679 = 9011519) B9011519
theorem B4005119 : Blo 2109435 4005119 := bstep (se 1 (by rfl) ⟨3003839, by rfl⟩ : syracuseStep 4005119 = 6007679) B6007679
theorem B2670079 : Blo 2109435 2670079 := bstep (se 1 (by rfl) ⟨2002559, by rfl⟩ : syracuseStep 2670079 = 4005119) B4005119
theorem B3560105 : Blo 2109435 3560105 := bstep (se 2 (by rfl) ⟨1335039, by rfl⟩ : syracuseStep 3560105 = 2670079) B2670079
theorem B2373403 : Blo 2109435 2373403 := bstep (se 1 (by rfl) ⟨1780052, by rfl⟩ : syracuseStep 2373403 = 3560105) B3560105
theorem B3164537 : Blo 2109435 3164537 := bstep (se 2 (by rfl) ⟨1186701, by rfl⟩ : syracuseStep 3164537 = 2373403) B2373403
theorem B2109691 : Blo 2109435 2109691 := bstep (se 1 (by rfl) ⟨1582268, by rfl⟩ : syracuseStep 2109691 = 3164537) B3164537
theorem B3379325 : Blo 2109435 3379325 := bbase (se 3 (by rfl) ⟨633623, by rfl⟩ : syracuseStep 3379325 = 1267247) (by norm_num)
theorem B36046133 : Blo 2109435 36046133 := bstep (se 5 (by rfl) ⟨1689662, by rfl⟩ : syracuseStep 36046133 = 3379325) B3379325
theorem B24030755 : Blo 2109435 24030755 := bstep (se 1 (by rfl) ⟨18023066, by rfl⟩ : syracuseStep 24030755 = 36046133) B36046133
theorem B16020503 : Blo 2109435 16020503 := bstep (se 1 (by rfl) ⟨12015377, by rfl⟩ : syracuseStep 16020503 = 24030755) B24030755
theorem B10680335 : Blo 2109435 10680335 := bstep (se 1 (by rfl) ⟨8010251, by rfl⟩ : syracuseStep 10680335 = 16020503) B16020503
theorem B7120223 : Blo 2109435 7120223 := bstep (se 1 (by rfl) ⟨5340167, by rfl⟩ : syracuseStep 7120223 = 10680335) B10680335
theorem B4746815 : Blo 2109435 4746815 := bstep (se 1 (by rfl) ⟨3560111, by rfl⟩ : syracuseStep 4746815 = 7120223) B7120223
theorem B3164543 : Blo 2109435 3164543 := bstep (se 1 (by rfl) ⟨2373407, by rfl⟩ : syracuseStep 3164543 = 4746815) B4746815
theorem B2109695 : Blo 2109435 2109695 := bstep (se 1 (by rfl) ⟨1582271, by rfl⟩ : syracuseStep 2109695 = 3164543) B3164543
theorem B3164549 : Blo 2109435 3164549 := bbase (se 4 (by rfl) ⟨296676, by rfl⟩ : syracuseStep 3164549 = 593353) (by norm_num)
theorem B2109699 : Blo 2109435 2109699 := bstep (se 1 (by rfl) ⟨1582274, by rfl⟩ : syracuseStep 2109699 = 3164549) B3164549
theorem B3560125 : Blo 2109435 3560125 := bbase (se 3 (by rfl) ⟨667523, by rfl⟩ : syracuseStep 3560125 = 1335047) (by norm_num)
theorem B4746833 : Blo 2109435 4746833 := bstep (se 2 (by rfl) ⟨1780062, by rfl⟩ : syracuseStep 4746833 = 3560125) B3560125
theorem B3164555 : Blo 2109435 3164555 := bstep (se 1 (by rfl) ⟨2373416, by rfl⟩ : syracuseStep 3164555 = 4746833) B4746833
theorem B2109703 : Blo 2109435 2109703 := bstep (se 1 (by rfl) ⟨1582277, by rfl⟩ : syracuseStep 2109703 = 3164555) B3164555
theorem B2373421 : Blo 2109435 2373421 := bbase (se 3 (by rfl) ⟨445016, by rfl⟩ : syracuseStep 2373421 = 890033) (by norm_num)
theorem B3164561 : Blo 2109435 3164561 := bstep (se 2 (by rfl) ⟨1186710, by rfl⟩ : syracuseStep 3164561 = 2373421) B2373421
theorem B2109707 : Blo 2109435 2109707 := bstep (se 1 (by rfl) ⟨1582280, by rfl⟩ : syracuseStep 2109707 = 3164561) B3164561
theorem B7120277 : Blo 2109435 7120277 := bbase (se 6 (by rfl) ⟨166881, by rfl⟩ : syracuseStep 7120277 = 333763) (by norm_num)
theorem B4746851 : Blo 2109435 4746851 := bstep (se 1 (by rfl) ⟨3560138, by rfl⟩ : syracuseStep 4746851 = 7120277) B7120277
theorem B3164567 : Blo 2109435 3164567 := bstep (se 1 (by rfl) ⟨2373425, by rfl⟩ : syracuseStep 3164567 = 4746851) B4746851
theorem B2109711 : Blo 2109435 2109711 := bstep (se 1 (by rfl) ⟨1582283, by rfl⟩ : syracuseStep 2109711 = 3164567) B3164567
theorem B3164573 : Blo 2109435 3164573 := bbase (se 3 (by rfl) ⟨593357, by rfl⟩ : syracuseStep 3164573 = 1186715) (by norm_num)
theorem B2109715 : Blo 2109435 2109715 := bstep (se 1 (by rfl) ⟨1582286, by rfl⟩ : syracuseStep 2109715 = 3164573) B3164573
theorem B4746869 : Blo 2109435 4746869 := bbase (se 5 (by rfl) ⟨222509, by rfl⟩ : syracuseStep 4746869 = 445019) (by norm_num)
theorem B3164579 : Blo 2109435 3164579 := bstep (se 1 (by rfl) ⟨2373434, by rfl⟩ : syracuseStep 3164579 = 4746869) B4746869
theorem B2109719 : Blo 2109435 2109719 := bstep (se 1 (by rfl) ⟨1582289, by rfl⟩ : syracuseStep 2109719 = 3164579) B3164579
theorem B6758741 : Blo 2109435 6758741 := bbase (se 10 (by rfl) ⟨9900, by rfl⟩ : syracuseStep 6758741 = 19801) (by norm_num)
theorem B18023309 : Blo 2109435 18023309 := bstep (se 3 (by rfl) ⟨3379370, by rfl⟩ : syracuseStep 18023309 = 6758741) B6758741
theorem B12015539 : Blo 2109435 12015539 := bstep (se 1 (by rfl) ⟨9011654, by rfl⟩ : syracuseStep 12015539 = 18023309) B18023309
theorem B8010359 : Blo 2109435 8010359 := bstep (se 1 (by rfl) ⟨6007769, by rfl⟩ : syracuseStep 8010359 = 12015539) B12015539
theorem B5340239 : Blo 2109435 5340239 := bstep (se 1 (by rfl) ⟨4005179, by rfl⟩ : syracuseStep 5340239 = 8010359) B8010359
theorem B3560159 : Blo 2109435 3560159 := bstep (se 1 (by rfl) ⟨2670119, by rfl⟩ : syracuseStep 3560159 = 5340239) B5340239
theorem B2373439 : Blo 2109435 2373439 := bstep (se 1 (by rfl) ⟨1780079, by rfl⟩ : syracuseStep 2373439 = 3560159) B3560159
theorem B3164585 : Blo 2109435 3164585 := bstep (se 2 (by rfl) ⟨1186719, by rfl⟩ : syracuseStep 3164585 = 2373439) B2373439
theorem B2109723 : Blo 2109435 2109723 := bstep (se 1 (by rfl) ⟨1582292, by rfl⟩ : syracuseStep 2109723 = 3164585) B3164585
theorem B8010373 : Blo 2109435 8010373 := bbase (se 4 (by rfl) ⟨750972, by rfl⟩ : syracuseStep 8010373 = 1501945) (by norm_num)
theorem B10680497 : Blo 2109435 10680497 := bstep (se 2 (by rfl) ⟨4005186, by rfl⟩ : syracuseStep 10680497 = 8010373) B8010373
theorem B7120331 : Blo 2109435 7120331 := bstep (se 1 (by rfl) ⟨5340248, by rfl⟩ : syracuseStep 7120331 = 10680497) B10680497
theorem B4746887 : Blo 2109435 4746887 := bstep (se 1 (by rfl) ⟨3560165, by rfl⟩ : syracuseStep 4746887 = 7120331) B7120331
theorem B3164591 : Blo 2109435 3164591 := bstep (se 1 (by rfl) ⟨2373443, by rfl⟩ : syracuseStep 3164591 = 4746887) B4746887
theorem B2109727 : Blo 2109435 2109727 := bstep (se 1 (by rfl) ⟨1582295, by rfl⟩ : syracuseStep 2109727 = 3164591) B3164591
theorem B3164597 : Blo 2109435 3164597 := bbase (se 5 (by rfl) ⟨148340, by rfl⟩ : syracuseStep 3164597 = 296681) (by norm_num)
theorem B2109731 : Blo 2109435 2109731 := bstep (se 1 (by rfl) ⟨1582298, by rfl⟩ : syracuseStep 2109731 = 3164597) B3164597
theorem B5340269 : Blo 2109435 5340269 := bbase (se 3 (by rfl) ⟨1001300, by rfl⟩ : syracuseStep 5340269 = 2002601) (by norm_num)
theorem B3560179 : Blo 2109435 3560179 := bstep (se 1 (by rfl) ⟨2670134, by rfl⟩ : syracuseStep 3560179 = 5340269) B5340269
theorem B4746905 : Blo 2109435 4746905 := bstep (se 2 (by rfl) ⟨1780089, by rfl⟩ : syracuseStep 4746905 = 3560179) B3560179
theorem B3164603 : Blo 2109435 3164603 := bstep (se 1 (by rfl) ⟨2373452, by rfl⟩ : syracuseStep 3164603 = 4746905) B4746905
theorem B2109735 : Blo 2109435 2109735 := bstep (se 1 (by rfl) ⟨1582301, by rfl⟩ : syracuseStep 2109735 = 3164603) B3164603
theorem B2373457 : Blo 2109435 2373457 := bbase (se 2 (by rfl) ⟨890046, by rfl⟩ : syracuseStep 2373457 = 1780093) (by norm_num)
theorem B3164609 : Blo 2109435 3164609 := bstep (se 2 (by rfl) ⟨1186728, by rfl⟩ : syracuseStep 3164609 = 2373457) B2373457
theorem B2109739 : Blo 2109435 2109739 := bstep (se 1 (by rfl) ⟨1582304, by rfl⟩ : syracuseStep 2109739 = 3164609) B3164609
theorem B3801829 : Blo 2109435 3801829 := bbase (se 4 (by rfl) ⟨356421, by rfl⟩ : syracuseStep 3801829 = 712843) (by norm_num)
theorem B5069105 : Blo 2109435 5069105 := bstep (se 2 (by rfl) ⟨1900914, by rfl⟩ : syracuseStep 5069105 = 3801829) B3801829
theorem B3379403 : Blo 2109435 3379403 := bstep (se 1 (by rfl) ⟨2534552, by rfl⟩ : syracuseStep 3379403 = 5069105) B5069105
theorem B2252935 : Blo 2109435 2252935 := bstep (se 1 (by rfl) ⟨1689701, by rfl⟩ : syracuseStep 2252935 = 3379403) B3379403
theorem B3003913 : Blo 2109435 3003913 := bstep (se 2 (by rfl) ⟨1126467, by rfl⟩ : syracuseStep 3003913 = 2252935) B2252935
theorem B4005217 : Blo 2109435 4005217 := bstep (se 2 (by rfl) ⟨1501956, by rfl⟩ : syracuseStep 4005217 = 3003913) B3003913
theorem B5340289 : Blo 2109435 5340289 := bstep (se 2 (by rfl) ⟨2002608, by rfl⟩ : syracuseStep 5340289 = 4005217) B4005217
theorem B7120385 : Blo 2109435 7120385 := bstep (se 2 (by rfl) ⟨2670144, by rfl⟩ : syracuseStep 7120385 = 5340289) B5340289
theorem B4746923 : Blo 2109435 4746923 := bstep (se 1 (by rfl) ⟨3560192, by rfl⟩ : syracuseStep 4746923 = 7120385) B7120385
theorem B3164615 : Blo 2109435 3164615 := bstep (se 1 (by rfl) ⟨2373461, by rfl⟩ : syracuseStep 3164615 = 4746923) B4746923
theorem B2109743 : Blo 2109435 2109743 := bstep (se 1 (by rfl) ⟨1582307, by rfl⟩ : syracuseStep 2109743 = 3164615) B3164615
theorem B3164621 : Blo 2109435 3164621 := bbase (se 3 (by rfl) ⟨593366, by rfl⟩ : syracuseStep 3164621 = 1186733) (by norm_num)
theorem B2109747 : Blo 2109435 2109747 := bstep (se 1 (by rfl) ⟨1582310, by rfl⟩ : syracuseStep 2109747 = 3164621) B3164621
theorem B4746941 : Blo 2109435 4746941 := bbase (se 3 (by rfl) ⟨890051, by rfl⟩ : syracuseStep 4746941 = 1780103) (by norm_num)
theorem B3164627 : Blo 2109435 3164627 := bstep (se 1 (by rfl) ⟨2373470, by rfl⟩ : syracuseStep 3164627 = 4746941) B4746941
theorem B2109751 : Blo 2109435 2109751 := bstep (se 1 (by rfl) ⟨1582313, by rfl⟩ : syracuseStep 2109751 = 3164627) B3164627
theorem B3560213 : Blo 2109435 3560213 := bbase (se 6 (by rfl) ⟨83442, by rfl⟩ : syracuseStep 3560213 = 166885) (by norm_num)
theorem B2373475 : Blo 2109435 2373475 := bstep (se 1 (by rfl) ⟨1780106, by rfl⟩ : syracuseStep 2373475 = 3560213) B3560213
theorem B3164633 : Blo 2109435 3164633 := bstep (se 2 (by rfl) ⟨1186737, by rfl⟩ : syracuseStep 3164633 = 2373475) B2373475
theorem B2109755 : Blo 2109435 2109755 := bstep (se 1 (by rfl) ⟨1582316, by rfl⟩ : syracuseStep 2109755 = 3164633) B3164633
theorem B4811725 : Blo 2109435 4811725 := bbase (se 3 (by rfl) ⟨902198, by rfl⟩ : syracuseStep 4811725 = 1804397) (by norm_num)
theorem B6415633 : Blo 2109435 6415633 := bstep (se 2 (by rfl) ⟨2405862, by rfl⟩ : syracuseStep 6415633 = 4811725) B4811725
theorem B8554177 : Blo 2109435 8554177 := bstep (se 2 (by rfl) ⟨3207816, by rfl⟩ : syracuseStep 8554177 = 6415633) B6415633
theorem B45622277 : Blo 2109435 45622277 := bstep (se 4 (by rfl) ⟨4277088, by rfl⟩ : syracuseStep 45622277 = 8554177) B8554177
theorem B30414851 : Blo 2109435 30414851 := bstep (se 1 (by rfl) ⟨22811138, by rfl⟩ : syracuseStep 30414851 = 45622277) B45622277
theorem B20276567 : Blo 2109435 20276567 := bstep (se 1 (by rfl) ⟨15207425, by rfl⟩ : syracuseStep 20276567 = 30414851) B30414851
theorem B13517711 : Blo 2109435 13517711 := bstep (se 1 (by rfl) ⟨10138283, by rfl⟩ : syracuseStep 13517711 = 20276567) B20276567
theorem B9011807 : Blo 2109435 9011807 := bstep (se 1 (by rfl) ⟨6758855, by rfl⟩ : syracuseStep 9011807 = 13517711) B13517711
theorem B6007871 : Blo 2109435 6007871 := bstep (se 1 (by rfl) ⟨4505903, by rfl⟩ : syracuseStep 6007871 = 9011807) B9011807
theorem B16020989 : Blo 2109435 16020989 := bstep (se 3 (by rfl) ⟨3003935, by rfl⟩ : syracuseStep 16020989 = 6007871) B6007871
theorem B10680659 : Blo 2109435 10680659 := bstep (se 1 (by rfl) ⟨8010494, by rfl⟩ : syracuseStep 10680659 = 16020989) B16020989
theorem B7120439 : Blo 2109435 7120439 := bstep (se 1 (by rfl) ⟨5340329, by rfl⟩ : syracuseStep 7120439 = 10680659) B10680659
theorem B4746959 : Blo 2109435 4746959 := bstep (se 1 (by rfl) ⟨3560219, by rfl⟩ : syracuseStep 4746959 = 7120439) B7120439
theorem B3164639 : Blo 2109435 3164639 := bstep (se 1 (by rfl) ⟨2373479, by rfl⟩ : syracuseStep 3164639 = 4746959) B4746959
theorem B2109759 : Blo 2109435 2109759 := bstep (se 1 (by rfl) ⟨1582319, by rfl⟩ : syracuseStep 2109759 = 3164639) B3164639
theorem B3164645 : Blo 2109435 3164645 := bbase (se 4 (by rfl) ⟨296685, by rfl⟩ : syracuseStep 3164645 = 593371) (by norm_num)
theorem B2109763 : Blo 2109435 2109763 := bstep (se 1 (by rfl) ⟨1582322, by rfl⟩ : syracuseStep 2109763 = 3164645) B3164645
theorem B2534581 : Blo 2109435 2534581 := bbase (se 5 (by rfl) ⟨118808, by rfl⟩ : syracuseStep 2534581 = 237617) (by norm_num)
theorem B13517765 : Blo 2109435 13517765 := bstep (se 4 (by rfl) ⟨1267290, by rfl⟩ : syracuseStep 13517765 = 2534581) B2534581
theorem B9011843 : Blo 2109435 9011843 := bstep (se 1 (by rfl) ⟨6758882, by rfl⟩ : syracuseStep 9011843 = 13517765) B13517765
theorem B6007895 : Blo 2109435 6007895 := bstep (se 1 (by rfl) ⟨4505921, by rfl⟩ : syracuseStep 6007895 = 9011843) B9011843
theorem B4005263 : Blo 2109435 4005263 := bstep (se 1 (by rfl) ⟨3003947, by rfl⟩ : syracuseStep 4005263 = 6007895) B6007895
theorem B2670175 : Blo 2109435 2670175 := bstep (se 1 (by rfl) ⟨2002631, by rfl⟩ : syracuseStep 2670175 = 4005263) B4005263
theorem B3560233 : Blo 2109435 3560233 := bstep (se 2 (by rfl) ⟨1335087, by rfl⟩ : syracuseStep 3560233 = 2670175) B2670175
theorem B4746977 : Blo 2109435 4746977 := bstep (se 2 (by rfl) ⟨1780116, by rfl⟩ : syracuseStep 4746977 = 3560233) B3560233
theorem B3164651 : Blo 2109435 3164651 := bstep (se 1 (by rfl) ⟨2373488, by rfl⟩ : syracuseStep 3164651 = 4746977) B4746977
theorem B2109767 : Blo 2109435 2109767 := bstep (se 1 (by rfl) ⟨1582325, by rfl⟩ : syracuseStep 2109767 = 3164651) B3164651
theorem B2373493 : Blo 2109435 2373493 := bbase (se 5 (by rfl) ⟨111257, by rfl⟩ : syracuseStep 2373493 = 222515) (by norm_num)
theorem B3164657 : Blo 2109435 3164657 := bstep (se 2 (by rfl) ⟨1186746, by rfl⟩ : syracuseStep 3164657 = 2373493) B2373493
theorem B2109771 : Blo 2109435 2109771 := bstep (se 1 (by rfl) ⟨1582328, by rfl⟩ : syracuseStep 2109771 = 3164657) B3164657
theorem B2670185 : Blo 2109435 2670185 := bbase (se 2 (by rfl) ⟨1001319, by rfl⟩ : syracuseStep 2670185 = 2002639) (by norm_num)
theorem B7120493 : Blo 2109435 7120493 := bstep (se 3 (by rfl) ⟨1335092, by rfl⟩ : syracuseStep 7120493 = 2670185) B2670185
theorem B4746995 : Blo 2109435 4746995 := bstep (se 1 (by rfl) ⟨3560246, by rfl⟩ : syracuseStep 4746995 = 7120493) B7120493
theorem B3164663 : Blo 2109435 3164663 := bstep (se 1 (by rfl) ⟨2373497, by rfl⟩ : syracuseStep 3164663 = 4746995) B4746995
theorem B2109775 : Blo 2109435 2109775 := bstep (se 1 (by rfl) ⟨1582331, by rfl⟩ : syracuseStep 2109775 = 3164663) B3164663
theorem B3164669 : Blo 2109435 3164669 := bbase (se 3 (by rfl) ⟨593375, by rfl⟩ : syracuseStep 3164669 = 1186751) (by norm_num)
theorem B2109779 : Blo 2109435 2109779 := bstep (se 1 (by rfl) ⟨1582334, by rfl⟩ : syracuseStep 2109779 = 3164669) B3164669
theorem B4747013 : Blo 2109435 4747013 := bbase (se 4 (by rfl) ⟨445032, by rfl⟩ : syracuseStep 4747013 = 890065) (by norm_num)
theorem B3164675 : Blo 2109435 3164675 := bstep (se 1 (by rfl) ⟨2373506, by rfl⟩ : syracuseStep 3164675 = 4747013) B4747013
theorem B2109783 : Blo 2109435 2109783 := bstep (se 1 (by rfl) ⟨1582337, by rfl⟩ : syracuseStep 2109783 = 3164675) B3164675
theorem B4005301 : Blo 2109435 4005301 := bbase (se 5 (by rfl) ⟨187748, by rfl⟩ : syracuseStep 4005301 = 375497) (by norm_num)
theorem B5340401 : Blo 2109435 5340401 := bstep (se 2 (by rfl) ⟨2002650, by rfl⟩ : syracuseStep 5340401 = 4005301) B4005301
theorem B3560267 : Blo 2109435 3560267 := bstep (se 1 (by rfl) ⟨2670200, by rfl⟩ : syracuseStep 3560267 = 5340401) B5340401
theorem B2373511 : Blo 2109435 2373511 := bstep (se 1 (by rfl) ⟨1780133, by rfl⟩ : syracuseStep 2373511 = 3560267) B3560267
theorem B3164681 : Blo 2109435 3164681 := bstep (se 2 (by rfl) ⟨1186755, by rfl⟩ : syracuseStep 3164681 = 2373511) B2373511
theorem B2109787 : Blo 2109435 2109787 := bstep (se 1 (by rfl) ⟨1582340, by rfl⟩ : syracuseStep 2109787 = 3164681) B3164681
theorem B10680821 : Blo 2109435 10680821 := bbase (se 5 (by rfl) ⟨500663, by rfl⟩ : syracuseStep 10680821 = 1001327) (by norm_num)
theorem B7120547 : Blo 2109435 7120547 := bstep (se 1 (by rfl) ⟨5340410, by rfl⟩ : syracuseStep 7120547 = 10680821) B10680821
theorem B4747031 : Blo 2109435 4747031 := bstep (se 1 (by rfl) ⟨3560273, by rfl⟩ : syracuseStep 4747031 = 7120547) B7120547
theorem B3164687 : Blo 2109435 3164687 := bstep (se 1 (by rfl) ⟨2373515, by rfl⟩ : syracuseStep 3164687 = 4747031) B4747031
theorem B2109791 : Blo 2109435 2109791 := bstep (se 1 (by rfl) ⟨1582343, by rfl⟩ : syracuseStep 2109791 = 3164687) B3164687
theorem B3164693 : Blo 2109435 3164693 := bbase (se 6 (by rfl) ⟨74172, by rfl⟩ : syracuseStep 3164693 = 148345) (by norm_num)
theorem B2109795 : Blo 2109435 2109795 := bstep (se 1 (by rfl) ⟨1582346, by rfl⟩ : syracuseStep 2109795 = 3164693) B3164693
theorem B18023957 : Blo 2109435 18023957 := bbase (se 6 (by rfl) ⟨422436, by rfl⟩ : syracuseStep 18023957 = 844873) (by norm_num)
theorem B12015971 : Blo 2109435 12015971 := bstep (se 1 (by rfl) ⟨9011978, by rfl⟩ : syracuseStep 12015971 = 18023957) B18023957
theorem B8010647 : Blo 2109435 8010647 := bstep (se 1 (by rfl) ⟨6007985, by rfl⟩ : syracuseStep 8010647 = 12015971) B12015971
theorem B5340431 : Blo 2109435 5340431 := bstep (se 1 (by rfl) ⟨4005323, by rfl⟩ : syracuseStep 5340431 = 8010647) B8010647
theorem B3560287 : Blo 2109435 3560287 := bstep (se 1 (by rfl) ⟨2670215, by rfl⟩ : syracuseStep 3560287 = 5340431) B5340431
theorem B4747049 : Blo 2109435 4747049 := bstep (se 2 (by rfl) ⟨1780143, by rfl⟩ : syracuseStep 4747049 = 3560287) B3560287
theorem B3164699 : Blo 2109435 3164699 := bstep (se 1 (by rfl) ⟨2373524, by rfl⟩ : syracuseStep 3164699 = 4747049) B4747049
theorem B2109799 : Blo 2109435 2109799 := bstep (se 1 (by rfl) ⟨1582349, by rfl⟩ : syracuseStep 2109799 = 3164699) B3164699
theorem B2373529 : Blo 2109435 2373529 := bbase (se 2 (by rfl) ⟨890073, by rfl⟩ : syracuseStep 2373529 = 1780147) (by norm_num)
theorem B3164705 : Blo 2109435 3164705 := bstep (se 2 (by rfl) ⟨1186764, by rfl⟩ : syracuseStep 3164705 = 2373529) B2373529
theorem B2109803 : Blo 2109435 2109803 := bstep (se 1 (by rfl) ⟨1582352, by rfl⟩ : syracuseStep 2109803 = 3164705) B3164705
theorem B8010677 : Blo 2109435 8010677 := bbase (se 5 (by rfl) ⟨375500, by rfl⟩ : syracuseStep 8010677 = 751001) (by norm_num)
theorem B5340451 : Blo 2109435 5340451 := bstep (se 1 (by rfl) ⟨4005338, by rfl⟩ : syracuseStep 5340451 = 8010677) B8010677
theorem B7120601 : Blo 2109435 7120601 := bstep (se 2 (by rfl) ⟨2670225, by rfl⟩ : syracuseStep 7120601 = 5340451) B5340451
theorem B4747067 : Blo 2109435 4747067 := bstep (se 1 (by rfl) ⟨3560300, by rfl⟩ : syracuseStep 4747067 = 7120601) B7120601
theorem B3164711 : Blo 2109435 3164711 := bstep (se 1 (by rfl) ⟨2373533, by rfl⟩ : syracuseStep 3164711 = 4747067) B4747067
theorem B2109807 : Blo 2109435 2109807 := bstep (se 1 (by rfl) ⟨1582355, by rfl⟩ : syracuseStep 2109807 = 3164711) B3164711
theorem B3164717 : Blo 2109435 3164717 := bbase (se 3 (by rfl) ⟨593384, by rfl⟩ : syracuseStep 3164717 = 1186769) (by norm_num)
theorem B2109811 : Blo 2109435 2109811 := bstep (se 1 (by rfl) ⟨1582358, by rfl⟩ : syracuseStep 2109811 = 3164717) B3164717
theorem B4747085 : Blo 2109435 4747085 := bbase (se 3 (by rfl) ⟨890078, by rfl⟩ : syracuseStep 4747085 = 1780157) (by norm_num)
theorem B3164723 : Blo 2109435 3164723 := bstep (se 1 (by rfl) ⟨2373542, by rfl⟩ : syracuseStep 3164723 = 4747085) B4747085
theorem B2109815 : Blo 2109435 2109815 := bstep (se 1 (by rfl) ⟨1582361, by rfl⟩ : syracuseStep 2109815 = 3164723) B3164723
theorem B2670241 : Blo 2109435 2670241 := bbase (se 2 (by rfl) ⟨1001340, by rfl⟩ : syracuseStep 2670241 = 2002681) (by norm_num)
theorem B3560321 : Blo 2109435 3560321 := bstep (se 2 (by rfl) ⟨1335120, by rfl⟩ : syracuseStep 3560321 = 2670241) B2670241
theorem B2373547 : Blo 2109435 2373547 := bstep (se 1 (by rfl) ⟨1780160, by rfl⟩ : syracuseStep 2373547 = 3560321) B3560321
theorem B3164729 : Blo 2109435 3164729 := bstep (se 2 (by rfl) ⟨1186773, by rfl⟩ : syracuseStep 3164729 = 2373547) B2373547
theorem B2109819 : Blo 2109435 2109819 := bstep (se 1 (by rfl) ⟨1582364, by rfl⟩ : syracuseStep 2109819 = 3164729) B3164729
theorem B24032213 : Blo 2109435 24032213 := bbase (se 7 (by rfl) ⟨281627, by rfl⟩ : syracuseStep 24032213 = 563255) (by norm_num)
theorem B16021475 : Blo 2109435 16021475 := bstep (se 1 (by rfl) ⟨12016106, by rfl⟩ : syracuseStep 16021475 = 24032213) B24032213
theorem B10680983 : Blo 2109435 10680983 := bstep (se 1 (by rfl) ⟨8010737, by rfl⟩ : syracuseStep 10680983 = 16021475) B16021475
theorem B7120655 : Blo 2109435 7120655 := bstep (se 1 (by rfl) ⟨5340491, by rfl⟩ : syracuseStep 7120655 = 10680983) B10680983
theorem B4747103 : Blo 2109435 4747103 := bstep (se 1 (by rfl) ⟨3560327, by rfl⟩ : syracuseStep 4747103 = 7120655) B7120655
theorem B3164735 : Blo 2109435 3164735 := bstep (se 1 (by rfl) ⟨2373551, by rfl⟩ : syracuseStep 3164735 = 4747103) B4747103
theorem B2109823 : Blo 2109435 2109823 := bstep (se 1 (by rfl) ⟨1582367, by rfl⟩ : syracuseStep 2109823 = 3164735) B3164735
theorem B3164741 : Blo 2109435 3164741 := bbase (se 4 (by rfl) ⟨296694, by rfl⟩ : syracuseStep 3164741 = 593389) (by norm_num)
theorem B2109827 : Blo 2109435 2109827 := bstep (se 1 (by rfl) ⟨1582370, by rfl⟩ : syracuseStep 2109827 = 3164741) B3164741
theorem B3560341 : Blo 2109435 3560341 := bbase (se 6 (by rfl) ⟨83445, by rfl⟩ : syracuseStep 3560341 = 166891) (by norm_num)
theorem B4747121 : Blo 2109435 4747121 := bstep (se 2 (by rfl) ⟨1780170, by rfl⟩ : syracuseStep 4747121 = 3560341) B3560341
theorem B3164747 : Blo 2109435 3164747 := bstep (se 1 (by rfl) ⟨2373560, by rfl⟩ : syracuseStep 3164747 = 4747121) B4747121
theorem B2109831 : Blo 2109435 2109831 := bstep (se 1 (by rfl) ⟨1582373, by rfl⟩ : syracuseStep 2109831 = 3164747) B3164747
theorem B2373565 : Blo 2109435 2373565 := bbase (se 3 (by rfl) ⟨445043, by rfl⟩ : syracuseStep 2373565 = 890087) (by norm_num)
theorem B3164753 : Blo 2109435 3164753 := bstep (se 2 (by rfl) ⟨1186782, by rfl⟩ : syracuseStep 3164753 = 2373565) B2373565
theorem B2109835 : Blo 2109435 2109835 := bstep (se 1 (by rfl) ⟨1582376, by rfl⟩ : syracuseStep 2109835 = 3164753) B3164753
theorem B7120709 : Blo 2109435 7120709 := bbase (se 4 (by rfl) ⟨667566, by rfl⟩ : syracuseStep 7120709 = 1335133) (by norm_num)
theorem B4747139 : Blo 2109435 4747139 := bstep (se 1 (by rfl) ⟨3560354, by rfl⟩ : syracuseStep 4747139 = 7120709) B7120709
theorem B3164759 : Blo 2109435 3164759 := bstep (se 1 (by rfl) ⟨2373569, by rfl⟩ : syracuseStep 3164759 = 4747139) B4747139
theorem B2109839 : Blo 2109435 2109839 := bstep (se 1 (by rfl) ⟨1582379, by rfl⟩ : syracuseStep 2109839 = 3164759) B3164759
theorem B3164765 : Blo 2109435 3164765 := bbase (se 3 (by rfl) ⟨593393, by rfl⟩ : syracuseStep 3164765 = 1186787) (by norm_num)
theorem B2109843 : Blo 2109435 2109843 := bstep (se 1 (by rfl) ⟨1582382, by rfl⟩ : syracuseStep 2109843 = 3164765) B3164765
theorem B4747157 : Blo 2109435 4747157 := bbase (se 6 (by rfl) ⟨111261, by rfl⟩ : syracuseStep 4747157 = 222523) (by norm_num)
theorem B3164771 : Blo 2109435 3164771 := bstep (se 1 (by rfl) ⟨2373578, by rfl⟩ : syracuseStep 3164771 = 4747157) B4747157
theorem B2109847 : Blo 2109435 2109847 := bstep (se 1 (by rfl) ⟨1582385, by rfl⟩ : syracuseStep 2109847 = 3164771) B3164771
theorem B4506101 : Blo 2109435 4506101 := bbase (se 5 (by rfl) ⟨211223, by rfl⟩ : syracuseStep 4506101 = 422447) (by norm_num)
theorem B3004067 : Blo 2109435 3004067 := bstep (se 1 (by rfl) ⟨2253050, by rfl⟩ : syracuseStep 3004067 = 4506101) B4506101
theorem B8010845 : Blo 2109435 8010845 := bstep (se 3 (by rfl) ⟨1502033, by rfl⟩ : syracuseStep 8010845 = 3004067) B3004067
theorem B5340563 : Blo 2109435 5340563 := bstep (se 1 (by rfl) ⟨4005422, by rfl⟩ : syracuseStep 5340563 = 8010845) B8010845
theorem B3560375 : Blo 2109435 3560375 := bstep (se 1 (by rfl) ⟨2670281, by rfl⟩ : syracuseStep 3560375 = 5340563) B5340563
theorem B2373583 : Blo 2109435 2373583 := bstep (se 1 (by rfl) ⟨1780187, by rfl⟩ : syracuseStep 2373583 = 3560375) B3560375
theorem B3164777 : Blo 2109435 3164777 := bstep (se 2 (by rfl) ⟨1186791, by rfl⟩ : syracuseStep 3164777 = 2373583) B2373583
theorem B2109851 : Blo 2109435 2109851 := bstep (se 1 (by rfl) ⟨1582388, by rfl⟩ : syracuseStep 2109851 = 3164777) B3164777
theorem B4877597 : Blo 2109435 4877597 := bbase (se 3 (by rfl) ⟨914549, by rfl⟩ : syracuseStep 4877597 = 1829099) (by norm_num)
theorem B13006925 : Blo 2109435 13006925 := bstep (se 3 (by rfl) ⟨2438798, by rfl⟩ : syracuseStep 13006925 = 4877597) B4877597
theorem B8671283 : Blo 2109435 8671283 := bstep (se 1 (by rfl) ⟨6503462, by rfl⟩ : syracuseStep 8671283 = 13006925) B13006925
theorem B5780855 : Blo 2109435 5780855 := bstep (se 1 (by rfl) ⟨4335641, by rfl⟩ : syracuseStep 5780855 = 8671283) B8671283
theorem B3853903 : Blo 2109435 3853903 := bstep (se 1 (by rfl) ⟨2890427, by rfl⟩ : syracuseStep 3853903 = 5780855) B5780855
theorem B5138537 : Blo 2109435 5138537 := bstep (se 2 (by rfl) ⟨1926951, by rfl⟩ : syracuseStep 5138537 = 3853903) B3853903
theorem B13702765 : Blo 2109435 13702765 := bstep (se 3 (by rfl) ⟨2569268, by rfl⟩ : syracuseStep 13702765 = 5138537) B5138537
theorem B18270353 : Blo 2109435 18270353 := bstep (se 2 (by rfl) ⟨6851382, by rfl⟩ : syracuseStep 18270353 = 13702765) B13702765
theorem B12180235 : Blo 2109435 12180235 := bstep (se 1 (by rfl) ⟨9135176, by rfl⟩ : syracuseStep 12180235 = 18270353) B18270353
theorem B16240313 : Blo 2109435 16240313 := bstep (se 2 (by rfl) ⟨6090117, by rfl⟩ : syracuseStep 16240313 = 12180235) B12180235
theorem B10826875 : Blo 2109435 10826875 := bstep (se 1 (by rfl) ⟨8120156, by rfl⟩ : syracuseStep 10826875 = 16240313) B16240313
theorem B14435833 : Blo 2109435 14435833 := bstep (se 2 (by rfl) ⟨5413437, by rfl⟩ : syracuseStep 14435833 = 10826875) B10826875
theorem B19247777 : Blo 2109435 19247777 := bstep (se 2 (by rfl) ⟨7217916, by rfl⟩ : syracuseStep 19247777 = 14435833) B14435833
theorem B12831851 : Blo 2109435 12831851 := bstep (se 1 (by rfl) ⟨9623888, by rfl⟩ : syracuseStep 12831851 = 19247777) B19247777
theorem B8554567 : Blo 2109435 8554567 := bstep (se 1 (by rfl) ⟨6415925, by rfl⟩ : syracuseStep 8554567 = 12831851) B12831851
theorem B11406089 : Blo 2109435 11406089 := bstep (se 2 (by rfl) ⟨4277283, by rfl⟩ : syracuseStep 11406089 = 8554567) B8554567
theorem B7604059 : Blo 2109435 7604059 := bstep (se 1 (by rfl) ⟨5703044, by rfl⟩ : syracuseStep 7604059 = 11406089) B11406089
theorem B10138745 : Blo 2109435 10138745 := bstep (se 2 (by rfl) ⟨3802029, by rfl⟩ : syracuseStep 10138745 = 7604059) B7604059
theorem B6759163 : Blo 2109435 6759163 := bstep (se 1 (by rfl) ⟨5069372, by rfl⟩ : syracuseStep 6759163 = 10138745) B10138745
theorem B9012217 : Blo 2109435 9012217 := bstep (se 2 (by rfl) ⟨3379581, by rfl⟩ : syracuseStep 9012217 = 6759163) B6759163
theorem B12016289 : Blo 2109435 12016289 := bstep (se 2 (by rfl) ⟨4506108, by rfl⟩ : syracuseStep 12016289 = 9012217) B9012217
theorem B8010859 : Blo 2109435 8010859 := bstep (se 1 (by rfl) ⟨6008144, by rfl⟩ : syracuseStep 8010859 = 12016289) B12016289
theorem B10681145 : Blo 2109435 10681145 := bstep (se 2 (by rfl) ⟨4005429, by rfl⟩ : syracuseStep 10681145 = 8010859) B8010859
theorem B7120763 : Blo 2109435 7120763 := bstep (se 1 (by rfl) ⟨5340572, by rfl⟩ : syracuseStep 7120763 = 10681145) B10681145
theorem B4747175 : Blo 2109435 4747175 := bstep (se 1 (by rfl) ⟨3560381, by rfl⟩ : syracuseStep 4747175 = 7120763) B7120763
theorem B3164783 : Blo 2109435 3164783 := bstep (se 1 (by rfl) ⟨2373587, by rfl⟩ : syracuseStep 3164783 = 4747175) B4747175
theorem B2109855 : Blo 2109435 2109855 := bstep (se 1 (by rfl) ⟨1582391, by rfl⟩ : syracuseStep 2109855 = 3164783) B3164783
theorem B3164789 : Blo 2109435 3164789 := bbase (se 5 (by rfl) ⟨148349, by rfl⟩ : syracuseStep 3164789 = 296699) (by norm_num)
theorem B2109859 : Blo 2109435 2109859 := bstep (se 1 (by rfl) ⟨1582394, by rfl⟩ : syracuseStep 2109859 = 3164789) B3164789
theorem B4005445 : Blo 2109435 4005445 := bbase (se 4 (by rfl) ⟨375510, by rfl⟩ : syracuseStep 4005445 = 751021) (by norm_num)
theorem B5340593 : Blo 2109435 5340593 := bstep (se 2 (by rfl) ⟨2002722, by rfl⟩ : syracuseStep 5340593 = 4005445) B4005445
theorem B3560395 : Blo 2109435 3560395 := bstep (se 1 (by rfl) ⟨2670296, by rfl⟩ : syracuseStep 3560395 = 5340593) B5340593
theorem B4747193 : Blo 2109435 4747193 := bstep (se 2 (by rfl) ⟨1780197, by rfl⟩ : syracuseStep 4747193 = 3560395) B3560395
theorem B3164795 : Blo 2109435 3164795 := bstep (se 1 (by rfl) ⟨2373596, by rfl⟩ : syracuseStep 3164795 = 4747193) B4747193
theorem B2109863 : Blo 2109435 2109863 := bstep (se 1 (by rfl) ⟨1582397, by rfl⟩ : syracuseStep 2109863 = 3164795) B3164795
theorem B2373601 : Blo 2109435 2373601 := bbase (se 2 (by rfl) ⟨890100, by rfl⟩ : syracuseStep 2373601 = 1780201) (by norm_num)
theorem B3164801 : Blo 2109435 3164801 := bstep (se 2 (by rfl) ⟨1186800, by rfl⟩ : syracuseStep 3164801 = 2373601) B2373601
theorem B2109867 : Blo 2109435 2109867 := bstep (se 1 (by rfl) ⟨1582400, by rfl⟩ : syracuseStep 2109867 = 3164801) B3164801
theorem B5340613 : Blo 2109435 5340613 := bbase (se 4 (by rfl) ⟨500682, by rfl⟩ : syracuseStep 5340613 = 1001365) (by norm_num)
theorem B7120817 : Blo 2109435 7120817 := bstep (se 2 (by rfl) ⟨2670306, by rfl⟩ : syracuseStep 7120817 = 5340613) B5340613
theorem B4747211 : Blo 2109435 4747211 := bstep (se 1 (by rfl) ⟨3560408, by rfl⟩ : syracuseStep 4747211 = 7120817) B7120817
theorem B3164807 : Blo 2109435 3164807 := bstep (se 1 (by rfl) ⟨2373605, by rfl⟩ : syracuseStep 3164807 = 4747211) B4747211
theorem B2109871 : Blo 2109435 2109871 := bstep (se 1 (by rfl) ⟨1582403, by rfl⟩ : syracuseStep 2109871 = 3164807) B3164807
theorem B3164813 : Blo 2109435 3164813 := bbase (se 3 (by rfl) ⟨593402, by rfl⟩ : syracuseStep 3164813 = 1186805) (by norm_num)
theorem B2109875 : Blo 2109435 2109875 := bstep (se 1 (by rfl) ⟨1582406, by rfl⟩ : syracuseStep 2109875 = 3164813) B3164813
theorem B4747229 : Blo 2109435 4747229 := bbase (se 3 (by rfl) ⟨890105, by rfl⟩ : syracuseStep 4747229 = 1780211) (by norm_num)
theorem B3164819 : Blo 2109435 3164819 := bstep (se 1 (by rfl) ⟨2373614, by rfl⟩ : syracuseStep 3164819 = 4747229) B4747229
theorem B2109879 : Blo 2109435 2109879 := bstep (se 1 (by rfl) ⟨1582409, by rfl⟩ : syracuseStep 2109879 = 3164819) B3164819
theorem B3560429 : Blo 2109435 3560429 := bbase (se 3 (by rfl) ⟨667580, by rfl⟩ : syracuseStep 3560429 = 1335161) (by norm_num)
theorem B2373619 : Blo 2109435 2373619 := bstep (se 1 (by rfl) ⟨1780214, by rfl⟩ : syracuseStep 2373619 = 3560429) B3560429
theorem B3164825 : Blo 2109435 3164825 := bstep (se 2 (by rfl) ⟨1186809, by rfl⟩ : syracuseStep 3164825 = 2373619) B2373619
theorem B2109883 : Blo 2109435 2109883 := bstep (se 1 (by rfl) ⟨1582412, by rfl⟩ : syracuseStep 2109883 = 3164825) B3164825
theorem B14436053 : Blo 2109435 14436053 := bbase (se 7 (by rfl) ⟨169172, by rfl⟩ : syracuseStep 14436053 = 338345) (by norm_num)
theorem B9624035 : Blo 2109435 9624035 := bstep (se 1 (by rfl) ⟨7218026, by rfl⟩ : syracuseStep 9624035 = 14436053) B14436053
theorem B6416023 : Blo 2109435 6416023 := bstep (se 1 (by rfl) ⟨4812017, by rfl⟩ : syracuseStep 6416023 = 9624035) B9624035
theorem B8554697 : Blo 2109435 8554697 := bstep (se 2 (by rfl) ⟨3208011, by rfl⟩ : syracuseStep 8554697 = 6416023) B6416023
theorem B5703131 : Blo 2109435 5703131 := bstep (se 1 (by rfl) ⟨4277348, by rfl⟩ : syracuseStep 5703131 = 8554697) B8554697
theorem B3802087 : Blo 2109435 3802087 := bstep (se 1 (by rfl) ⟨2851565, by rfl⟩ : syracuseStep 3802087 = 5703131) B5703131
theorem B5069449 : Blo 2109435 5069449 := bstep (se 2 (by rfl) ⟨1901043, by rfl⟩ : syracuseStep 5069449 = 3802087) B3802087
theorem B27037061 : Blo 2109435 27037061 := bstep (se 4 (by rfl) ⟨2534724, by rfl⟩ : syracuseStep 27037061 = 5069449) B5069449
theorem B18024707 : Blo 2109435 18024707 := bstep (se 1 (by rfl) ⟨13518530, by rfl⟩ : syracuseStep 18024707 = 27037061) B27037061
theorem B12016471 : Blo 2109435 12016471 := bstep (se 1 (by rfl) ⟨9012353, by rfl⟩ : syracuseStep 12016471 = 18024707) B18024707
theorem B16021961 : Blo 2109435 16021961 := bstep (se 2 (by rfl) ⟨6008235, by rfl⟩ : syracuseStep 16021961 = 12016471) B12016471
theorem B10681307 : Blo 2109435 10681307 := bstep (se 1 (by rfl) ⟨8010980, by rfl⟩ : syracuseStep 10681307 = 16021961) B16021961
theorem B7120871 : Blo 2109435 7120871 := bstep (se 1 (by rfl) ⟨5340653, by rfl⟩ : syracuseStep 7120871 = 10681307) B10681307
theorem B4747247 : Blo 2109435 4747247 := bstep (se 1 (by rfl) ⟨3560435, by rfl⟩ : syracuseStep 4747247 = 7120871) B7120871
theorem B3164831 : Blo 2109435 3164831 := bstep (se 1 (by rfl) ⟨2373623, by rfl⟩ : syracuseStep 3164831 = 4747247) B4747247
theorem B2109887 : Blo 2109435 2109887 := bstep (se 1 (by rfl) ⟨1582415, by rfl⟩ : syracuseStep 2109887 = 3164831) B3164831
theorem B3164837 : Blo 2109435 3164837 := bbase (se 4 (by rfl) ⟨296703, by rfl⟩ : syracuseStep 3164837 = 593407) (by norm_num)
theorem B2109891 : Blo 2109435 2109891 := bstep (se 1 (by rfl) ⟨1582418, by rfl⟩ : syracuseStep 2109891 = 3164837) B3164837
theorem B2670337 : Blo 2109435 2670337 := bbase (se 2 (by rfl) ⟨1001376, by rfl⟩ : syracuseStep 2670337 = 2002753) (by norm_num)
theorem B3560449 : Blo 2109435 3560449 := bstep (se 2 (by rfl) ⟨1335168, by rfl⟩ : syracuseStep 3560449 = 2670337) B2670337
theorem B4747265 : Blo 2109435 4747265 := bstep (se 2 (by rfl) ⟨1780224, by rfl⟩ : syracuseStep 4747265 = 3560449) B3560449
theorem B3164843 : Blo 2109435 3164843 := bstep (se 1 (by rfl) ⟨2373632, by rfl⟩ : syracuseStep 3164843 = 4747265) B4747265
theorem B2109895 : Blo 2109435 2109895 := bstep (se 1 (by rfl) ⟨1582421, by rfl⟩ : syracuseStep 2109895 = 3164843) B3164843
theorem B2373637 : Blo 2109435 2373637 := bbase (se 4 (by rfl) ⟨222528, by rfl⟩ : syracuseStep 2373637 = 445057) (by norm_num)
theorem B3164849 : Blo 2109435 3164849 := bstep (se 2 (by rfl) ⟨1186818, by rfl⟩ : syracuseStep 3164849 = 2373637) B2373637
theorem B2109899 : Blo 2109435 2109899 := bstep (se 1 (by rfl) ⟨1582424, by rfl⟩ : syracuseStep 2109899 = 3164849) B3164849
theorem B3004141 : Blo 2109435 3004141 := bbase (se 3 (by rfl) ⟨563276, by rfl⟩ : syracuseStep 3004141 = 1126553) (by norm_num)
theorem B4005521 : Blo 2109435 4005521 := bstep (se 2 (by rfl) ⟨1502070, by rfl⟩ : syracuseStep 4005521 = 3004141) B3004141
theorem B2670347 : Blo 2109435 2670347 := bstep (se 1 (by rfl) ⟨2002760, by rfl⟩ : syracuseStep 2670347 = 4005521) B4005521
theorem B7120925 : Blo 2109435 7120925 := bstep (se 3 (by rfl) ⟨1335173, by rfl⟩ : syracuseStep 7120925 = 2670347) B2670347
theorem B4747283 : Blo 2109435 4747283 := bstep (se 1 (by rfl) ⟨3560462, by rfl⟩ : syracuseStep 4747283 = 7120925) B7120925
theorem B3164855 : Blo 2109435 3164855 := bstep (se 1 (by rfl) ⟨2373641, by rfl⟩ : syracuseStep 3164855 = 4747283) B4747283
theorem B2109903 : Blo 2109435 2109903 := bstep (se 1 (by rfl) ⟨1582427, by rfl⟩ : syracuseStep 2109903 = 3164855) B3164855
theorem B3164861 : Blo 2109435 3164861 := bbase (se 3 (by rfl) ⟨593411, by rfl⟩ : syracuseStep 3164861 = 1186823) (by norm_num)
theorem B2109907 : Blo 2109435 2109907 := bstep (se 1 (by rfl) ⟨1582430, by rfl⟩ : syracuseStep 2109907 = 3164861) B3164861
theorem B4747301 : Blo 2109435 4747301 := bbase (se 4 (by rfl) ⟨445059, by rfl⟩ : syracuseStep 4747301 = 890119) (by norm_num)
theorem B3164867 : Blo 2109435 3164867 := bstep (se 1 (by rfl) ⟨2373650, by rfl⟩ : syracuseStep 3164867 = 4747301) B4747301
theorem B2109911 : Blo 2109435 2109911 := bstep (se 1 (by rfl) ⟨1582433, by rfl⟩ : syracuseStep 2109911 = 3164867) B3164867
theorem B5340725 : Blo 2109435 5340725 := bbase (se 5 (by rfl) ⟨250346, by rfl⟩ : syracuseStep 5340725 = 500693) (by norm_num)
theorem B3560483 : Blo 2109435 3560483 := bstep (se 1 (by rfl) ⟨2670362, by rfl⟩ : syracuseStep 3560483 = 5340725) B5340725
theorem B2373655 : Blo 2109435 2373655 := bstep (se 1 (by rfl) ⟨1780241, by rfl⟩ : syracuseStep 2373655 = 3560483) B3560483
theorem B3164873 : Blo 2109435 3164873 := bstep (se 2 (by rfl) ⟨1186827, by rfl⟩ : syracuseStep 3164873 = 2373655) B2373655
theorem B2109915 : Blo 2109435 2109915 := bstep (se 1 (by rfl) ⟨1582436, by rfl⟩ : syracuseStep 2109915 = 3164873) B3164873
theorem B3208061 : Blo 2109435 3208061 := bbase (se 3 (by rfl) ⟨601511, by rfl⟩ : syracuseStep 3208061 = 1203023) (by norm_num)
theorem B2138707 : Blo 2109435 2138707 := bstep (se 1 (by rfl) ⟨1604030, by rfl⟩ : syracuseStep 2138707 = 3208061) B3208061
theorem B2851609 : Blo 2109435 2851609 := bstep (se 2 (by rfl) ⟨1069353, by rfl⟩ : syracuseStep 2851609 = 2138707) B2138707
theorem B3802145 : Blo 2109435 3802145 := bstep (se 2 (by rfl) ⟨1425804, by rfl⟩ : syracuseStep 3802145 = 2851609) B2851609
theorem B10139053 : Blo 2109435 10139053 := bstep (se 3 (by rfl) ⟨1901072, by rfl⟩ : syracuseStep 10139053 = 3802145) B3802145
theorem B13518737 : Blo 2109435 13518737 := bstep (se 2 (by rfl) ⟨5069526, by rfl⟩ : syracuseStep 13518737 = 10139053) B10139053
theorem B9012491 : Blo 2109435 9012491 := bstep (se 1 (by rfl) ⟨6759368, by rfl⟩ : syracuseStep 9012491 = 13518737) B13518737
theorem B6008327 : Blo 2109435 6008327 := bstep (se 1 (by rfl) ⟨4506245, by rfl⟩ : syracuseStep 6008327 = 9012491) B9012491
theorem B4005551 : Blo 2109435 4005551 := bstep (se 1 (by rfl) ⟨3004163, by rfl⟩ : syracuseStep 4005551 = 6008327) B6008327
theorem B10681469 : Blo 2109435 10681469 := bstep (se 3 (by rfl) ⟨2002775, by rfl⟩ : syracuseStep 10681469 = 4005551) B4005551
theorem B7120979 : Blo 2109435 7120979 := bstep (se 1 (by rfl) ⟨5340734, by rfl⟩ : syracuseStep 7120979 = 10681469) B10681469
theorem B4747319 : Blo 2109435 4747319 := bstep (se 1 (by rfl) ⟨3560489, by rfl⟩ : syracuseStep 4747319 = 7120979) B7120979
theorem B3164879 : Blo 2109435 3164879 := bstep (se 1 (by rfl) ⟨2373659, by rfl⟩ : syracuseStep 3164879 = 4747319) B4747319
theorem B2109919 : Blo 2109435 2109919 := bstep (se 1 (by rfl) ⟨1582439, by rfl⟩ : syracuseStep 2109919 = 3164879) B3164879
theorem B3164885 : Blo 2109435 3164885 := bbase (se 7 (by rfl) ⟨37088, by rfl⟩ : syracuseStep 3164885 = 74177) (by norm_num)
theorem B2109923 : Blo 2109435 2109923 := bstep (se 1 (by rfl) ⟨1582442, by rfl⟩ : syracuseStep 2109923 = 3164885) B3164885
theorem B10139093 : Blo 2109435 10139093 := bbase (se 7 (by rfl) ⟨118817, by rfl⟩ : syracuseStep 10139093 = 237635) (by norm_num)
theorem B6759395 : Blo 2109435 6759395 := bstep (se 1 (by rfl) ⟨5069546, by rfl⟩ : syracuseStep 6759395 = 10139093) B10139093
theorem B4506263 : Blo 2109435 4506263 := bstep (se 1 (by rfl) ⟨3379697, by rfl⟩ : syracuseStep 4506263 = 6759395) B6759395
theorem B3004175 : Blo 2109435 3004175 := bstep (se 1 (by rfl) ⟨2253131, by rfl⟩ : syracuseStep 3004175 = 4506263) B4506263
theorem B8011133 : Blo 2109435 8011133 := bstep (se 3 (by rfl) ⟨1502087, by rfl⟩ : syracuseStep 8011133 = 3004175) B3004175
theorem B5340755 : Blo 2109435 5340755 := bstep (se 1 (by rfl) ⟨4005566, by rfl⟩ : syracuseStep 5340755 = 8011133) B8011133
theorem B3560503 : Blo 2109435 3560503 := bstep (se 1 (by rfl) ⟨2670377, by rfl⟩ : syracuseStep 3560503 = 5340755) B5340755
theorem B4747337 : Blo 2109435 4747337 := bstep (se 2 (by rfl) ⟨1780251, by rfl⟩ : syracuseStep 4747337 = 3560503) B3560503
theorem B3164891 : Blo 2109435 3164891 := bstep (se 1 (by rfl) ⟨2373668, by rfl⟩ : syracuseStep 3164891 = 4747337) B4747337
theorem B2109927 : Blo 2109435 2109927 := bstep (se 1 (by rfl) ⟨1582445, by rfl⟩ : syracuseStep 2109927 = 3164891) B3164891
theorem B2373673 : Blo 2109435 2373673 := bbase (se 2 (by rfl) ⟨890127, by rfl⟩ : syracuseStep 2373673 = 1780255) (by norm_num)
theorem B3164897 : Blo 2109435 3164897 := bstep (se 2 (by rfl) ⟨1186836, by rfl⟩ : syracuseStep 3164897 = 2373673) B2373673
theorem B2109931 : Blo 2109435 2109931 := bstep (se 1 (by rfl) ⟨1582448, by rfl⟩ : syracuseStep 2109931 = 3164897) B3164897
theorem B2283881 : Blo 2109435 2283881 := bbase (se 2 (by rfl) ⟨856455, by rfl⟩ : syracuseStep 2283881 = 1712911) (by norm_num)
theorem B6090349 : Blo 2109435 6090349 := bstep (se 3 (by rfl) ⟨1141940, by rfl⟩ : syracuseStep 6090349 = 2283881) B2283881
theorem B8120465 : Blo 2109435 8120465 := bstep (se 2 (by rfl) ⟨3045174, by rfl⟩ : syracuseStep 8120465 = 6090349) B6090349
theorem B5413643 : Blo 2109435 5413643 := bstep (se 1 (by rfl) ⟨4060232, by rfl⟩ : syracuseStep 5413643 = 8120465) B8120465
theorem B3609095 : Blo 2109435 3609095 := bstep (se 1 (by rfl) ⟨2706821, by rfl⟩ : syracuseStep 3609095 = 5413643) B5413643
theorem B9624253 : Blo 2109435 9624253 := bstep (se 3 (by rfl) ⟨1804547, by rfl⟩ : syracuseStep 9624253 = 3609095) B3609095
theorem B12832337 : Blo 2109435 12832337 := bstep (se 2 (by rfl) ⟨4812126, by rfl⟩ : syracuseStep 12832337 = 9624253) B9624253
theorem B8554891 : Blo 2109435 8554891 := bstep (se 1 (by rfl) ⟨6416168, by rfl⟩ : syracuseStep 8554891 = 12832337) B12832337
theorem B11406521 : Blo 2109435 11406521 := bstep (se 2 (by rfl) ⟨4277445, by rfl⟩ : syracuseStep 11406521 = 8554891) B8554891
theorem B30417389 : Blo 2109435 30417389 := bstep (se 3 (by rfl) ⟨5703260, by rfl⟩ : syracuseStep 30417389 = 11406521) B11406521
theorem B20278259 : Blo 2109435 20278259 := bstep (se 1 (by rfl) ⟨15208694, by rfl⟩ : syracuseStep 20278259 = 30417389) B30417389
theorem B13518839 : Blo 2109435 13518839 := bstep (se 1 (by rfl) ⟨10139129, by rfl⟩ : syracuseStep 13518839 = 20278259) B20278259
theorem B9012559 : Blo 2109435 9012559 := bstep (se 1 (by rfl) ⟨6759419, by rfl⟩ : syracuseStep 9012559 = 13518839) B13518839
theorem B12016745 : Blo 2109435 12016745 := bstep (se 2 (by rfl) ⟨4506279, by rfl⟩ : syracuseStep 12016745 = 9012559) B9012559
theorem B8011163 : Blo 2109435 8011163 := bstep (se 1 (by rfl) ⟨6008372, by rfl⟩ : syracuseStep 8011163 = 12016745) B12016745
theorem B5340775 : Blo 2109435 5340775 := bstep (se 1 (by rfl) ⟨4005581, by rfl⟩ : syracuseStep 5340775 = 8011163) B8011163
theorem B7121033 : Blo 2109435 7121033 := bstep (se 2 (by rfl) ⟨2670387, by rfl⟩ : syracuseStep 7121033 = 5340775) B5340775
theorem B4747355 : Blo 2109435 4747355 := bstep (se 1 (by rfl) ⟨3560516, by rfl⟩ : syracuseStep 4747355 = 7121033) B7121033
theorem B3164903 : Blo 2109435 3164903 := bstep (se 1 (by rfl) ⟨2373677, by rfl⟩ : syracuseStep 3164903 = 4747355) B4747355
theorem B2109935 : Blo 2109435 2109935 := bstep (se 1 (by rfl) ⟨1582451, by rfl⟩ : syracuseStep 2109935 = 3164903) B3164903
theorem B3164909 : Blo 2109435 3164909 := bbase (se 3 (by rfl) ⟨593420, by rfl⟩ : syracuseStep 3164909 = 1186841) (by norm_num)
theorem B2109939 : Blo 2109435 2109939 := bstep (se 1 (by rfl) ⟨1582454, by rfl⟩ : syracuseStep 2109939 = 3164909) B3164909
theorem B4747373 : Blo 2109435 4747373 := bbase (se 3 (by rfl) ⟨890132, by rfl⟩ : syracuseStep 4747373 = 1780265) (by norm_num)
theorem B3164915 : Blo 2109435 3164915 := bstep (se 1 (by rfl) ⟨2373686, by rfl⟩ : syracuseStep 3164915 = 4747373) B4747373
theorem B2109943 : Blo 2109435 2109943 := bstep (se 1 (by rfl) ⟨1582457, by rfl⟩ : syracuseStep 2109943 = 3164915) B3164915
theorem B4005605 : Blo 2109435 4005605 := bbase (se 4 (by rfl) ⟨375525, by rfl⟩ : syracuseStep 4005605 = 751051) (by norm_num)
theorem B2670403 : Blo 2109435 2670403 := bstep (se 1 (by rfl) ⟨2002802, by rfl⟩ : syracuseStep 2670403 = 4005605) B4005605
theorem B3560537 : Blo 2109435 3560537 := bstep (se 2 (by rfl) ⟨1335201, by rfl⟩ : syracuseStep 3560537 = 2670403) B2670403
theorem B2373691 : Blo 2109435 2373691 := bstep (se 1 (by rfl) ⟨1780268, by rfl⟩ : syracuseStep 2373691 = 3560537) B3560537
theorem B3164921 : Blo 2109435 3164921 := bstep (se 2 (by rfl) ⟨1186845, by rfl⟩ : syracuseStep 3164921 = 2373691) B2373691
theorem B2109947 : Blo 2109435 2109947 := bstep (se 1 (by rfl) ⟨1582460, by rfl⟩ : syracuseStep 2109947 = 3164921) B3164921
theorem B40556821 : Blo 2109435 40556821 := bbase (se 6 (by rfl) ⟨950550, by rfl⟩ : syracuseStep 40556821 = 1901101) (by norm_num)
theorem B54075761 : Blo 2109435 54075761 := bstep (se 2 (by rfl) ⟨20278410, by rfl⟩ : syracuseStep 54075761 = 40556821) B40556821
theorem B36050507 : Blo 2109435 36050507 := bstep (se 1 (by rfl) ⟨27037880, by rfl⟩ : syracuseStep 36050507 = 54075761) B54075761
theorem B24033671 : Blo 2109435 24033671 := bstep (se 1 (by rfl) ⟨18025253, by rfl⟩ : syracuseStep 24033671 = 36050507) B36050507
theorem B16022447 : Blo 2109435 16022447 := bstep (se 1 (by rfl) ⟨12016835, by rfl⟩ : syracuseStep 16022447 = 24033671) B24033671
theorem B10681631 : Blo 2109435 10681631 := bstep (se 1 (by rfl) ⟨8011223, by rfl⟩ : syracuseStep 10681631 = 16022447) B16022447
theorem B7121087 : Blo 2109435 7121087 := bstep (se 1 (by rfl) ⟨5340815, by rfl⟩ : syracuseStep 7121087 = 10681631) B10681631
theorem B4747391 : Blo 2109435 4747391 := bstep (se 1 (by rfl) ⟨3560543, by rfl⟩ : syracuseStep 4747391 = 7121087) B7121087
theorem B3164927 : Blo 2109435 3164927 := bstep (se 1 (by rfl) ⟨2373695, by rfl⟩ : syracuseStep 3164927 = 4747391) B4747391
theorem B2109951 : Blo 2109435 2109951 := bstep (se 1 (by rfl) ⟨1582463, by rfl⟩ : syracuseStep 2109951 = 3164927) B3164927
theorem B3164933 : Blo 2109435 3164933 := bbase (se 4 (by rfl) ⟨296712, by rfl⟩ : syracuseStep 3164933 = 593425) (by norm_num)
theorem B2109955 : Blo 2109435 2109955 := bstep (se 1 (by rfl) ⟨1582466, by rfl⟩ : syracuseStep 2109955 = 3164933) B3164933
theorem B3560557 : Blo 2109435 3560557 := bbase (se 3 (by rfl) ⟨667604, by rfl⟩ : syracuseStep 3560557 = 1335209) (by norm_num)
theorem B4747409 : Blo 2109435 4747409 := bstep (se 2 (by rfl) ⟨1780278, by rfl⟩ : syracuseStep 4747409 = 3560557) B3560557
theorem B3164939 : Blo 2109435 3164939 := bstep (se 1 (by rfl) ⟨2373704, by rfl⟩ : syracuseStep 3164939 = 4747409) B4747409
theorem B2109959 : Blo 2109435 2109959 := bstep (se 1 (by rfl) ⟨1582469, by rfl⟩ : syracuseStep 2109959 = 3164939) B3164939
theorem B2373709 : Blo 2109435 2373709 := bbase (se 3 (by rfl) ⟨445070, by rfl⟩ : syracuseStep 2373709 = 890141) (by norm_num)
theorem B3164945 : Blo 2109435 3164945 := bstep (se 2 (by rfl) ⟨1186854, by rfl⟩ : syracuseStep 3164945 = 2373709) B2373709
theorem B2109963 : Blo 2109435 2109963 := bstep (se 1 (by rfl) ⟨1582472, by rfl⟩ : syracuseStep 2109963 = 3164945) B3164945
theorem B7121141 : Blo 2109435 7121141 := bbase (se 5 (by rfl) ⟨333803, by rfl⟩ : syracuseStep 7121141 = 667607) (by norm_num)
theorem B4747427 : Blo 2109435 4747427 := bstep (se 1 (by rfl) ⟨3560570, by rfl⟩ : syracuseStep 4747427 = 7121141) B7121141
theorem B3164951 : Blo 2109435 3164951 := bstep (se 1 (by rfl) ⟨2373713, by rfl⟩ : syracuseStep 3164951 = 4747427) B4747427
theorem B2109967 : Blo 2109435 2109967 := bstep (se 1 (by rfl) ⟨1582475, by rfl⟩ : syracuseStep 2109967 = 3164951) B3164951
theorem B3164957 : Blo 2109435 3164957 := bbase (se 3 (by rfl) ⟨593429, by rfl⟩ : syracuseStep 3164957 = 1186859) (by norm_num)
theorem B2109971 : Blo 2109435 2109971 := bstep (se 1 (by rfl) ⟨1582478, by rfl⟩ : syracuseStep 2109971 = 3164957) B3164957
theorem B4747445 : Blo 2109435 4747445 := bbase (se 5 (by rfl) ⟨222536, by rfl⟩ : syracuseStep 4747445 = 445073) (by norm_num)
theorem B3164963 : Blo 2109435 3164963 := bstep (se 1 (by rfl) ⟨2373722, by rfl⟩ : syracuseStep 3164963 = 4747445) B4747445
theorem B2109975 : Blo 2109435 2109975 := bstep (se 1 (by rfl) ⟨1582481, by rfl⟩ : syracuseStep 2109975 = 3164963) B3164963
theorem B3379781 : Blo 2109435 3379781 := bbase (se 4 (by rfl) ⟨316854, by rfl⟩ : syracuseStep 3379781 = 633709) (by norm_num)
theorem B2253187 : Blo 2109435 2253187 := bstep (se 1 (by rfl) ⟨1689890, by rfl⟩ : syracuseStep 2253187 = 3379781) B3379781
theorem B12016997 : Blo 2109435 12016997 := bstep (se 4 (by rfl) ⟨1126593, by rfl⟩ : syracuseStep 12016997 = 2253187) B2253187
theorem B8011331 : Blo 2109435 8011331 := bstep (se 1 (by rfl) ⟨6008498, by rfl⟩ : syracuseStep 8011331 = 12016997) B12016997
theorem B5340887 : Blo 2109435 5340887 := bstep (se 1 (by rfl) ⟨4005665, by rfl⟩ : syracuseStep 5340887 = 8011331) B8011331
theorem B3560591 : Blo 2109435 3560591 := bstep (se 1 (by rfl) ⟨2670443, by rfl⟩ : syracuseStep 3560591 = 5340887) B5340887
theorem B2373727 : Blo 2109435 2373727 := bstep (se 1 (by rfl) ⟨1780295, by rfl⟩ : syracuseStep 2373727 = 3560591) B3560591
theorem B3164969 : Blo 2109435 3164969 := bstep (se 2 (by rfl) ⟨1186863, by rfl⟩ : syracuseStep 3164969 = 2373727) B2373727
theorem B2109979 : Blo 2109435 2109979 := bstep (se 1 (by rfl) ⟨1582484, by rfl⟩ : syracuseStep 2109979 = 3164969) B3164969
theorem B3802261 : Blo 2109435 3802261 := bbase (se 6 (by rfl) ⟨89115, by rfl⟩ : syracuseStep 3802261 = 178231) (by norm_num)
theorem B5069681 : Blo 2109435 5069681 := bstep (se 2 (by rfl) ⟨1901130, by rfl⟩ : syracuseStep 5069681 = 3802261) B3802261
theorem B3379787 : Blo 2109435 3379787 := bstep (se 1 (by rfl) ⟨2534840, by rfl⟩ : syracuseStep 3379787 = 5069681) B5069681
theorem B2253191 : Blo 2109435 2253191 := bstep (se 1 (by rfl) ⟨1689893, by rfl⟩ : syracuseStep 2253191 = 3379787) B3379787
theorem B6008509 : Blo 2109435 6008509 := bstep (se 3 (by rfl) ⟨1126595, by rfl⟩ : syracuseStep 6008509 = 2253191) B2253191
theorem B8011345 : Blo 2109435 8011345 := bstep (se 2 (by rfl) ⟨3004254, by rfl⟩ : syracuseStep 8011345 = 6008509) B6008509
theorem B10681793 : Blo 2109435 10681793 := bstep (se 2 (by rfl) ⟨4005672, by rfl⟩ : syracuseStep 10681793 = 8011345) B8011345
theorem B7121195 : Blo 2109435 7121195 := bstep (se 1 (by rfl) ⟨5340896, by rfl⟩ : syracuseStep 7121195 = 10681793) B10681793
theorem B4747463 : Blo 2109435 4747463 := bstep (se 1 (by rfl) ⟨3560597, by rfl⟩ : syracuseStep 4747463 = 7121195) B7121195
theorem B3164975 : Blo 2109435 3164975 := bstep (se 1 (by rfl) ⟨2373731, by rfl⟩ : syracuseStep 3164975 = 4747463) B4747463
theorem B2109983 : Blo 2109435 2109983 := bstep (se 1 (by rfl) ⟨1582487, by rfl⟩ : syracuseStep 2109983 = 3164975) B3164975
theorem B3164981 : Blo 2109435 3164981 := bbase (se 5 (by rfl) ⟨148358, by rfl⟩ : syracuseStep 3164981 = 296717) (by norm_num)
theorem B2109987 : Blo 2109435 2109987 := bstep (se 1 (by rfl) ⟨1582490, by rfl⟩ : syracuseStep 2109987 = 3164981) B3164981
theorem B5340917 : Blo 2109435 5340917 := bbase (se 5 (by rfl) ⟨250355, by rfl⟩ : syracuseStep 5340917 = 500711) (by norm_num)
theorem B3560611 : Blo 2109435 3560611 := bstep (se 1 (by rfl) ⟨2670458, by rfl⟩ : syracuseStep 3560611 = 5340917) B5340917
theorem B4747481 : Blo 2109435 4747481 := bstep (se 2 (by rfl) ⟨1780305, by rfl⟩ : syracuseStep 4747481 = 3560611) B3560611
theorem B3164987 : Blo 2109435 3164987 := bstep (se 1 (by rfl) ⟨2373740, by rfl⟩ : syracuseStep 3164987 = 4747481) B4747481
theorem B2109991 : Blo 2109435 2109991 := bstep (se 1 (by rfl) ⟨1582493, by rfl⟩ : syracuseStep 2109991 = 3164987) B3164987
theorem B2373745 : Blo 2109435 2373745 := bbase (se 2 (by rfl) ⟨890154, by rfl⟩ : syracuseStep 2373745 = 1780309) (by norm_num)
theorem B3164993 : Blo 2109435 3164993 := bstep (se 2 (by rfl) ⟨1186872, by rfl⟩ : syracuseStep 3164993 = 2373745) B2373745
theorem B2109995 : Blo 2109435 2109995 := bstep (se 1 (by rfl) ⟨1582496, by rfl⟩ : syracuseStep 2109995 = 3164993) B3164993
theorem B11406869 : Blo 2109435 11406869 := bbase (se 6 (by rfl) ⟨267348, by rfl⟩ : syracuseStep 11406869 = 534697) (by norm_num)
theorem B7604579 : Blo 2109435 7604579 := bstep (se 1 (by rfl) ⟨5703434, by rfl⟩ : syracuseStep 7604579 = 11406869) B11406869
theorem B5069719 : Blo 2109435 5069719 := bstep (se 1 (by rfl) ⟨3802289, by rfl⟩ : syracuseStep 5069719 = 7604579) B7604579
theorem B6759625 : Blo 2109435 6759625 := bstep (se 2 (by rfl) ⟨2534859, by rfl⟩ : syracuseStep 6759625 = 5069719) B5069719
theorem B9012833 : Blo 2109435 9012833 := bstep (se 2 (by rfl) ⟨3379812, by rfl⟩ : syracuseStep 9012833 = 6759625) B6759625
theorem B6008555 : Blo 2109435 6008555 := bstep (se 1 (by rfl) ⟨4506416, by rfl⟩ : syracuseStep 6008555 = 9012833) B9012833
theorem B4005703 : Blo 2109435 4005703 := bstep (se 1 (by rfl) ⟨3004277, by rfl⟩ : syracuseStep 4005703 = 6008555) B6008555
theorem B5340937 : Blo 2109435 5340937 := bstep (se 2 (by rfl) ⟨2002851, by rfl⟩ : syracuseStep 5340937 = 4005703) B4005703
theorem B7121249 : Blo 2109435 7121249 := bstep (se 2 (by rfl) ⟨2670468, by rfl⟩ : syracuseStep 7121249 = 5340937) B5340937
theorem B4747499 : Blo 2109435 4747499 := bstep (se 1 (by rfl) ⟨3560624, by rfl⟩ : syracuseStep 4747499 = 7121249) B7121249
theorem B3164999 : Blo 2109435 3164999 := bstep (se 1 (by rfl) ⟨2373749, by rfl⟩ : syracuseStep 3164999 = 4747499) B4747499
theorem B2109999 : Blo 2109435 2109999 := bstep (se 1 (by rfl) ⟨1582499, by rfl⟩ : syracuseStep 2109999 = 3164999) B3164999
theorem B3165005 : Blo 2109435 3165005 := bbase (se 3 (by rfl) ⟨593438, by rfl⟩ : syracuseStep 3165005 = 1186877) (by norm_num)
theorem B2110003 : Blo 2109435 2110003 := bstep (se 1 (by rfl) ⟨1582502, by rfl⟩ : syracuseStep 2110003 = 3165005) B3165005
theorem B4747517 : Blo 2109435 4747517 := bbase (se 3 (by rfl) ⟨890159, by rfl⟩ : syracuseStep 4747517 = 1780319) (by norm_num)
theorem B3165011 : Blo 2109435 3165011 := bstep (se 1 (by rfl) ⟨2373758, by rfl⟩ : syracuseStep 3165011 = 4747517) B4747517
theorem B2110007 : Blo 2109435 2110007 := bstep (se 1 (by rfl) ⟨1582505, by rfl⟩ : syracuseStep 2110007 = 3165011) B3165011
theorem B3560645 : Blo 2109435 3560645 := bbase (se 4 (by rfl) ⟨333810, by rfl⟩ : syracuseStep 3560645 = 667621) (by norm_num)
theorem B2373763 : Blo 2109435 2373763 := bstep (se 1 (by rfl) ⟨1780322, by rfl⟩ : syracuseStep 2373763 = 3560645) B3560645
theorem B3165017 : Blo 2109435 3165017 := bstep (se 2 (by rfl) ⟨1186881, by rfl⟩ : syracuseStep 3165017 = 2373763) B2373763
theorem B2110011 : Blo 2109435 2110011 := bstep (se 1 (by rfl) ⟨1582508, by rfl⟩ : syracuseStep 2110011 = 3165017) B3165017
theorem B16022933 : Blo 2109435 16022933 := bbase (se 6 (by rfl) ⟨375537, by rfl⟩ : syracuseStep 16022933 = 751075) (by norm_num)
theorem B10681955 : Blo 2109435 10681955 := bstep (se 1 (by rfl) ⟨8011466, by rfl⟩ : syracuseStep 10681955 = 16022933) B16022933
theorem B7121303 : Blo 2109435 7121303 := bstep (se 1 (by rfl) ⟨5340977, by rfl⟩ : syracuseStep 7121303 = 10681955) B10681955
theorem B4747535 : Blo 2109435 4747535 := bstep (se 1 (by rfl) ⟨3560651, by rfl⟩ : syracuseStep 4747535 = 7121303) B7121303
theorem B3165023 : Blo 2109435 3165023 := bstep (se 1 (by rfl) ⟨2373767, by rfl⟩ : syracuseStep 3165023 = 4747535) B4747535
theorem B2110015 : Blo 2109435 2110015 := bstep (se 1 (by rfl) ⟨1582511, by rfl⟩ : syracuseStep 2110015 = 3165023) B3165023
theorem B3165029 : Blo 2109435 3165029 := bbase (se 4 (by rfl) ⟨296721, by rfl⟩ : syracuseStep 3165029 = 593443) (by norm_num)
theorem B2110019 : Blo 2109435 2110019 := bstep (se 1 (by rfl) ⟨1582514, by rfl⟩ : syracuseStep 2110019 = 3165029) B3165029
theorem B4005749 : Blo 2109435 4005749 := bbase (se 5 (by rfl) ⟨187769, by rfl⟩ : syracuseStep 4005749 = 375539) (by norm_num)
theorem B2670499 : Blo 2109435 2670499 := bstep (se 1 (by rfl) ⟨2002874, by rfl⟩ : syracuseStep 2670499 = 4005749) B4005749
theorem B3560665 : Blo 2109435 3560665 := bstep (se 2 (by rfl) ⟨1335249, by rfl⟩ : syracuseStep 3560665 = 2670499) B2670499
theorem B4747553 : Blo 2109435 4747553 := bstep (se 2 (by rfl) ⟨1780332, by rfl⟩ : syracuseStep 4747553 = 3560665) B3560665
theorem B3165035 : Blo 2109435 3165035 := bstep (se 1 (by rfl) ⟨2373776, by rfl⟩ : syracuseStep 3165035 = 4747553) B4747553
theorem B2110023 : Blo 2109435 2110023 := bstep (se 1 (by rfl) ⟨1582517, by rfl⟩ : syracuseStep 2110023 = 3165035) B3165035
theorem B2373781 : Blo 2109435 2373781 := bbase (se 6 (by rfl) ⟨55635, by rfl⟩ : syracuseStep 2373781 = 111271) (by norm_num)
theorem B3165041 : Blo 2109435 3165041 := bstep (se 2 (by rfl) ⟨1186890, by rfl⟩ : syracuseStep 3165041 = 2373781) B2373781
theorem B2110027 : Blo 2109435 2110027 := bstep (se 1 (by rfl) ⟨1582520, by rfl⟩ : syracuseStep 2110027 = 3165041) B3165041
theorem B2670509 : Blo 2109435 2670509 := bbase (se 3 (by rfl) ⟨500720, by rfl⟩ : syracuseStep 2670509 = 1001441) (by norm_num)
theorem B7121357 : Blo 2109435 7121357 := bstep (se 3 (by rfl) ⟨1335254, by rfl⟩ : syracuseStep 7121357 = 2670509) B2670509
theorem B4747571 : Blo 2109435 4747571 := bstep (se 1 (by rfl) ⟨3560678, by rfl⟩ : syracuseStep 4747571 = 7121357) B7121357
theorem B3165047 : Blo 2109435 3165047 := bstep (se 1 (by rfl) ⟨2373785, by rfl⟩ : syracuseStep 3165047 = 4747571) B4747571
theorem B2110031 : Blo 2109435 2110031 := bstep (se 1 (by rfl) ⟨1582523, by rfl⟩ : syracuseStep 2110031 = 3165047) B3165047
theorem B3165053 : Blo 2109435 3165053 := bbase (se 3 (by rfl) ⟨593447, by rfl⟩ : syracuseStep 3165053 = 1186895) (by norm_num)
theorem B2110035 : Blo 2109435 2110035 := bstep (se 1 (by rfl) ⟨1582526, by rfl⟩ : syracuseStep 2110035 = 3165053) B3165053
theorem B4747589 : Blo 2109435 4747589 := bbase (se 4 (by rfl) ⟨445086, by rfl⟩ : syracuseStep 4747589 = 890173) (by norm_num)
theorem B3165059 : Blo 2109435 3165059 := bstep (se 1 (by rfl) ⟨2373794, by rfl⟩ : syracuseStep 3165059 = 4747589) B4747589
theorem B2110039 : Blo 2109435 2110039 := bstep (se 1 (by rfl) ⟨1582529, by rfl⟩ : syracuseStep 2110039 = 3165059) B3165059
theorem B2138833 : Blo 2109435 2138833 := bbase (se 2 (by rfl) ⟨802062, by rfl⟩ : syracuseStep 2138833 = 1604125) (by norm_num)
theorem B2851777 : Blo 2109435 2851777 := bstep (se 2 (by rfl) ⟨1069416, by rfl⟩ : syracuseStep 2851777 = 2138833) B2138833
theorem B15209477 : Blo 2109435 15209477 := bstep (se 4 (by rfl) ⟨1425888, by rfl⟩ : syracuseStep 15209477 = 2851777) B2851777
theorem B10139651 : Blo 2109435 10139651 := bstep (se 1 (by rfl) ⟨7604738, by rfl⟩ : syracuseStep 10139651 = 15209477) B15209477
theorem B6759767 : Blo 2109435 6759767 := bstep (se 1 (by rfl) ⟨5069825, by rfl⟩ : syracuseStep 6759767 = 10139651) B10139651
theorem B4506511 : Blo 2109435 4506511 := bstep (se 1 (by rfl) ⟨3379883, by rfl⟩ : syracuseStep 4506511 = 6759767) B6759767
theorem B6008681 : Blo 2109435 6008681 := bstep (se 2 (by rfl) ⟨2253255, by rfl⟩ : syracuseStep 6008681 = 4506511) B4506511
theorem B4005787 : Blo 2109435 4005787 := bstep (se 1 (by rfl) ⟨3004340, by rfl⟩ : syracuseStep 4005787 = 6008681) B6008681
theorem B5341049 : Blo 2109435 5341049 := bstep (se 2 (by rfl) ⟨2002893, by rfl⟩ : syracuseStep 5341049 = 4005787) B4005787
theorem B3560699 : Blo 2109435 3560699 := bstep (se 1 (by rfl) ⟨2670524, by rfl⟩ : syracuseStep 3560699 = 5341049) B5341049
theorem B2373799 : Blo 2109435 2373799 := bstep (se 1 (by rfl) ⟨1780349, by rfl⟩ : syracuseStep 2373799 = 3560699) B3560699
theorem B3165065 : Blo 2109435 3165065 := bstep (se 2 (by rfl) ⟨1186899, by rfl⟩ : syracuseStep 3165065 = 2373799) B2373799
theorem B2110043 : Blo 2109435 2110043 := bstep (se 1 (by rfl) ⟨1582532, by rfl⟩ : syracuseStep 2110043 = 3165065) B3165065
theorem B10682117 : Blo 2109435 10682117 := bbase (se 4 (by rfl) ⟨1001448, by rfl⟩ : syracuseStep 10682117 = 2002897) (by norm_num)
theorem B7121411 : Blo 2109435 7121411 := bstep (se 1 (by rfl) ⟨5341058, by rfl⟩ : syracuseStep 7121411 = 10682117) B10682117
theorem B4747607 : Blo 2109435 4747607 := bstep (se 1 (by rfl) ⟨3560705, by rfl⟩ : syracuseStep 4747607 = 7121411) B7121411
theorem B3165071 : Blo 2109435 3165071 := bstep (se 1 (by rfl) ⟨2373803, by rfl⟩ : syracuseStep 3165071 = 4747607) B4747607
theorem B2110047 : Blo 2109435 2110047 := bstep (se 1 (by rfl) ⟨1582535, by rfl⟩ : syracuseStep 2110047 = 3165071) B3165071
theorem B3165077 : Blo 2109435 3165077 := bbase (se 6 (by rfl) ⟨74181, by rfl⟩ : syracuseStep 3165077 = 148363) (by norm_num)
theorem B2110051 : Blo 2109435 2110051 := bstep (se 1 (by rfl) ⟨1582538, by rfl⟩ : syracuseStep 2110051 = 3165077) B3165077
theorem B12017429 : Blo 2109435 12017429 := bbase (se 6 (by rfl) ⟨281658, by rfl⟩ : syracuseStep 12017429 = 563317) (by norm_num)
theorem B8011619 : Blo 2109435 8011619 := bstep (se 1 (by rfl) ⟨6008714, by rfl⟩ : syracuseStep 8011619 = 12017429) B12017429
theorem B5341079 : Blo 2109435 5341079 := bstep (se 1 (by rfl) ⟨4005809, by rfl⟩ : syracuseStep 5341079 = 8011619) B8011619
theorem B3560719 : Blo 2109435 3560719 := bstep (se 1 (by rfl) ⟨2670539, by rfl⟩ : syracuseStep 3560719 = 5341079) B5341079
theorem B4747625 : Blo 2109435 4747625 := bstep (se 2 (by rfl) ⟨1780359, by rfl⟩ : syracuseStep 4747625 = 3560719) B3560719
theorem B3165083 : Blo 2109435 3165083 := bstep (se 1 (by rfl) ⟨2373812, by rfl⟩ : syracuseStep 3165083 = 4747625) B4747625
theorem B2110055 : Blo 2109435 2110055 := bstep (se 1 (by rfl) ⟨1582541, by rfl⟩ : syracuseStep 2110055 = 3165083) B3165083
theorem B2373817 : Blo 2109435 2373817 := bbase (se 2 (by rfl) ⟨890181, by rfl⟩ : syracuseStep 2373817 = 1780363) (by norm_num)
theorem B3165089 : Blo 2109435 3165089 := bstep (se 2 (by rfl) ⟨1186908, by rfl⟩ : syracuseStep 3165089 = 2373817) B2373817
theorem B2110059 : Blo 2109435 2110059 := bstep (se 1 (by rfl) ⟨1582544, by rfl⟩ : syracuseStep 2110059 = 3165089) B3165089
theorem B3802405 : Blo 2109435 3802405 := bbase (se 4 (by rfl) ⟨356475, by rfl⟩ : syracuseStep 3802405 = 712951) (by norm_num)
theorem B5069873 : Blo 2109435 5069873 := bstep (se 2 (by rfl) ⟨1901202, by rfl⟩ : syracuseStep 5069873 = 3802405) B3802405
theorem B3379915 : Blo 2109435 3379915 := bstep (se 1 (by rfl) ⟨2534936, by rfl⟩ : syracuseStep 3379915 = 5069873) B5069873
theorem B4506553 : Blo 2109435 4506553 := bstep (se 2 (by rfl) ⟨1689957, by rfl⟩ : syracuseStep 4506553 = 3379915) B3379915
theorem B6008737 : Blo 2109435 6008737 := bstep (se 2 (by rfl) ⟨2253276, by rfl⟩ : syracuseStep 6008737 = 4506553) B4506553
theorem B8011649 : Blo 2109435 8011649 := bstep (se 2 (by rfl) ⟨3004368, by rfl⟩ : syracuseStep 8011649 = 6008737) B6008737
theorem B5341099 : Blo 2109435 5341099 := bstep (se 1 (by rfl) ⟨4005824, by rfl⟩ : syracuseStep 5341099 = 8011649) B8011649
theorem B7121465 : Blo 2109435 7121465 := bstep (se 2 (by rfl) ⟨2670549, by rfl⟩ : syracuseStep 7121465 = 5341099) B5341099
theorem B4747643 : Blo 2109435 4747643 := bstep (se 1 (by rfl) ⟨3560732, by rfl⟩ : syracuseStep 4747643 = 7121465) B7121465
theorem B3165095 : Blo 2109435 3165095 := bstep (se 1 (by rfl) ⟨2373821, by rfl⟩ : syracuseStep 3165095 = 4747643) B4747643
theorem B2110063 : Blo 2109435 2110063 := bstep (se 1 (by rfl) ⟨1582547, by rfl⟩ : syracuseStep 2110063 = 3165095) B3165095
theorem B3165101 : Blo 2109435 3165101 := bbase (se 3 (by rfl) ⟨593456, by rfl⟩ : syracuseStep 3165101 = 1186913) (by norm_num)
theorem B2110067 : Blo 2109435 2110067 := bstep (se 1 (by rfl) ⟨1582550, by rfl⟩ : syracuseStep 2110067 = 3165101) B3165101
theorem B4747661 : Blo 2109435 4747661 := bbase (se 3 (by rfl) ⟨890186, by rfl⟩ : syracuseStep 4747661 = 1780373) (by norm_num)
theorem B3165107 : Blo 2109435 3165107 := bstep (se 1 (by rfl) ⟨2373830, by rfl⟩ : syracuseStep 3165107 = 4747661) B4747661
theorem B2110071 : Blo 2109435 2110071 := bstep (se 1 (by rfl) ⟨1582553, by rfl⟩ : syracuseStep 2110071 = 3165107) B3165107
theorem B2670565 : Blo 2109435 2670565 := bbase (se 4 (by rfl) ⟨250365, by rfl⟩ : syracuseStep 2670565 = 500731) (by norm_num)
theorem B3560753 : Blo 2109435 3560753 := bstep (se 2 (by rfl) ⟨1335282, by rfl⟩ : syracuseStep 3560753 = 2670565) B2670565
theorem B2373835 : Blo 2109435 2373835 := bstep (se 1 (by rfl) ⟨1780376, by rfl⟩ : syracuseStep 2373835 = 3560753) B3560753
theorem B3165113 : Blo 2109435 3165113 := bstep (se 2 (by rfl) ⟨1186917, by rfl⟩ : syracuseStep 3165113 = 2373835) B2373835
theorem B2110075 : Blo 2109435 2110075 := bstep (se 1 (by rfl) ⟨1582556, by rfl⟩ : syracuseStep 2110075 = 3165113) B3165113
theorem B3252077 : Blo 2109435 3252077 := bbase (se 3 (by rfl) ⟨609764, by rfl⟩ : syracuseStep 3252077 = 1219529) (by norm_num)
theorem B2168051 : Blo 2109435 2168051 := bstep (se 1 (by rfl) ⟨1626038, by rfl⟩ : syracuseStep 2168051 = 3252077) B3252077
theorem B5781469 : Blo 2109435 5781469 := bstep (se 3 (by rfl) ⟨1084025, by rfl⟩ : syracuseStep 5781469 = 2168051) B2168051
theorem B7708625 : Blo 2109435 7708625 := bstep (se 2 (by rfl) ⟨2890734, by rfl⟩ : syracuseStep 7708625 = 5781469) B5781469
theorem B5139083 : Blo 2109435 5139083 := bstep (se 1 (by rfl) ⟨3854312, by rfl⟩ : syracuseStep 5139083 = 7708625) B7708625
theorem B13704221 : Blo 2109435 13704221 := bstep (se 3 (by rfl) ⟨2569541, by rfl⟩ : syracuseStep 13704221 = 5139083) B5139083
theorem B9136147 : Blo 2109435 9136147 := bstep (se 1 (by rfl) ⟨6852110, by rfl⟩ : syracuseStep 9136147 = 13704221) B13704221
theorem B12181529 : Blo 2109435 12181529 := bstep (se 2 (by rfl) ⟨4568073, by rfl⟩ : syracuseStep 12181529 = 9136147) B9136147
theorem B8121019 : Blo 2109435 8121019 := bstep (se 1 (by rfl) ⟨6090764, by rfl⟩ : syracuseStep 8121019 = 12181529) B12181529
theorem B10828025 : Blo 2109435 10828025 := bstep (se 2 (by rfl) ⟨4060509, by rfl⟩ : syracuseStep 10828025 = 8121019) B8121019
theorem B7218683 : Blo 2109435 7218683 := bstep (se 1 (by rfl) ⟨5414012, by rfl⟩ : syracuseStep 7218683 = 10828025) B10828025
theorem B4812455 : Blo 2109435 4812455 := bstep (se 1 (by rfl) ⟨3609341, by rfl⟩ : syracuseStep 4812455 = 7218683) B7218683
theorem B3208303 : Blo 2109435 3208303 := bstep (se 1 (by rfl) ⟨2406227, by rfl⟩ : syracuseStep 3208303 = 4812455) B4812455
theorem B4277737 : Blo 2109435 4277737 := bstep (se 2 (by rfl) ⟨1604151, by rfl⟩ : syracuseStep 4277737 = 3208303) B3208303
theorem B22814597 : Blo 2109435 22814597 := bstep (se 4 (by rfl) ⟨2138868, by rfl⟩ : syracuseStep 22814597 = 4277737) B4277737
theorem B15209731 : Blo 2109435 15209731 := bstep (se 1 (by rfl) ⟨11407298, by rfl⟩ : syracuseStep 15209731 = 22814597) B22814597
theorem B20279641 : Blo 2109435 20279641 := bstep (se 2 (by rfl) ⟨7604865, by rfl⟩ : syracuseStep 20279641 = 15209731) B15209731
theorem B27039521 : Blo 2109435 27039521 := bstep (se 2 (by rfl) ⟨10139820, by rfl⟩ : syracuseStep 27039521 = 20279641) B20279641
theorem B18026347 : Blo 2109435 18026347 := bstep (se 1 (by rfl) ⟨13519760, by rfl⟩ : syracuseStep 18026347 = 27039521) B27039521
theorem B24035129 : Blo 2109435 24035129 := bstep (se 2 (by rfl) ⟨9013173, by rfl⟩ : syracuseStep 24035129 = 18026347) B18026347
theorem B16023419 : Blo 2109435 16023419 := bstep (se 1 (by rfl) ⟨12017564, by rfl⟩ : syracuseStep 16023419 = 24035129) B24035129
theorem B10682279 : Blo 2109435 10682279 := bstep (se 1 (by rfl) ⟨8011709, by rfl⟩ : syracuseStep 10682279 = 16023419) B16023419
theorem B7121519 : Blo 2109435 7121519 := bstep (se 1 (by rfl) ⟨5341139, by rfl⟩ : syracuseStep 7121519 = 10682279) B10682279
theorem B4747679 : Blo 2109435 4747679 := bstep (se 1 (by rfl) ⟨3560759, by rfl⟩ : syracuseStep 4747679 = 7121519) B7121519
theorem B3165119 : Blo 2109435 3165119 := bstep (se 1 (by rfl) ⟨2373839, by rfl⟩ : syracuseStep 3165119 = 4747679) B4747679
theorem B2110079 : Blo 2109435 2110079 := bstep (se 1 (by rfl) ⟨1582559, by rfl⟩ : syracuseStep 2110079 = 3165119) B3165119
theorem B3165125 : Blo 2109435 3165125 := bbase (se 4 (by rfl) ⟨296730, by rfl⟩ : syracuseStep 3165125 = 593461) (by norm_num)
theorem B2110083 : Blo 2109435 2110083 := bstep (se 1 (by rfl) ⟨1582562, by rfl⟩ : syracuseStep 2110083 = 3165125) B3165125
theorem B3560773 : Blo 2109435 3560773 := bbase (se 4 (by rfl) ⟨333822, by rfl⟩ : syracuseStep 3560773 = 667645) (by norm_num)
theorem B4747697 : Blo 2109435 4747697 := bstep (se 2 (by rfl) ⟨1780386, by rfl⟩ : syracuseStep 4747697 = 3560773) B3560773
theorem B3165131 : Blo 2109435 3165131 := bstep (se 1 (by rfl) ⟨2373848, by rfl⟩ : syracuseStep 3165131 = 4747697) B4747697
theorem B2110087 : Blo 2109435 2110087 := bstep (se 1 (by rfl) ⟨1582565, by rfl⟩ : syracuseStep 2110087 = 3165131) B3165131
theorem B2373853 : Blo 2109435 2373853 := bbase (se 3 (by rfl) ⟨445097, by rfl⟩ : syracuseStep 2373853 = 890195) (by norm_num)
theorem B3165137 : Blo 2109435 3165137 := bstep (se 2 (by rfl) ⟨1186926, by rfl⟩ : syracuseStep 3165137 = 2373853) B2373853
theorem B2110091 : Blo 2109435 2110091 := bstep (se 1 (by rfl) ⟨1582568, by rfl⟩ : syracuseStep 2110091 = 3165137) B3165137
theorem B7121573 : Blo 2109435 7121573 := bbase (se 4 (by rfl) ⟨667647, by rfl⟩ : syracuseStep 7121573 = 1335295) (by norm_num)
theorem B4747715 : Blo 2109435 4747715 := bstep (se 1 (by rfl) ⟨3560786, by rfl⟩ : syracuseStep 4747715 = 7121573) B7121573
theorem B3165143 : Blo 2109435 3165143 := bstep (se 1 (by rfl) ⟨2373857, by rfl⟩ : syracuseStep 3165143 = 4747715) B4747715
theorem B2110095 : Blo 2109435 2110095 := bstep (se 1 (by rfl) ⟨1582571, by rfl⟩ : syracuseStep 2110095 = 3165143) B3165143
theorem B3165149 : Blo 2109435 3165149 := bbase (se 3 (by rfl) ⟨593465, by rfl⟩ : syracuseStep 3165149 = 1186931) (by norm_num)
theorem B2110099 : Blo 2109435 2110099 := bstep (se 1 (by rfl) ⟨1582574, by rfl⟩ : syracuseStep 2110099 = 3165149) B3165149
theorem B4747733 : Blo 2109435 4747733 := bbase (se 7 (by rfl) ⟨55637, by rfl⟩ : syracuseStep 4747733 = 111275) (by norm_num)
theorem B3165155 : Blo 2109435 3165155 := bstep (se 1 (by rfl) ⟨2373866, by rfl⟩ : syracuseStep 3165155 = 4747733) B4747733
theorem B2110103 : Blo 2109435 2110103 := bstep (se 1 (by rfl) ⟨1582577, by rfl⟩ : syracuseStep 2110103 = 3165155) B3165155
theorem B12347893 : Blo 2109435 12347893 := bbase (se 5 (by rfl) ⟨578807, by rfl⟩ : syracuseStep 12347893 = 1157615) (by norm_num)
theorem B16463857 : Blo 2109435 16463857 := bstep (se 2 (by rfl) ⟨6173946, by rfl⟩ : syracuseStep 16463857 = 12347893) B12347893
theorem B21951809 : Blo 2109435 21951809 := bstep (se 2 (by rfl) ⟨8231928, by rfl⟩ : syracuseStep 21951809 = 16463857) B16463857
theorem B14634539 : Blo 2109435 14634539 := bstep (se 1 (by rfl) ⟨10975904, by rfl⟩ : syracuseStep 14634539 = 21951809) B21951809
theorem B9756359 : Blo 2109435 9756359 := bstep (se 1 (by rfl) ⟨7317269, by rfl⟩ : syracuseStep 9756359 = 14634539) B14634539
theorem B6504239 : Blo 2109435 6504239 := bstep (se 1 (by rfl) ⟨4878179, by rfl⟩ : syracuseStep 6504239 = 9756359) B9756359
theorem B17344637 : Blo 2109435 17344637 := bstep (se 3 (by rfl) ⟨3252119, by rfl⟩ : syracuseStep 17344637 = 6504239) B6504239
theorem B11563091 : Blo 2109435 11563091 := bstep (se 1 (by rfl) ⟨8672318, by rfl⟩ : syracuseStep 11563091 = 17344637) B17344637
theorem B7708727 : Blo 2109435 7708727 := bstep (se 1 (by rfl) ⟨5781545, by rfl⟩ : syracuseStep 7708727 = 11563091) B11563091
theorem B20556605 : Blo 2109435 20556605 := bstep (se 3 (by rfl) ⟨3854363, by rfl⟩ : syracuseStep 20556605 = 7708727) B7708727
theorem B13704403 : Blo 2109435 13704403 := bstep (se 1 (by rfl) ⟨10278302, by rfl⟩ : syracuseStep 13704403 = 20556605) B20556605
theorem B18272537 : Blo 2109435 18272537 := bstep (se 2 (by rfl) ⟨6852201, by rfl⟩ : syracuseStep 18272537 = 13704403) B13704403
theorem B12181691 : Blo 2109435 12181691 := bstep (se 1 (by rfl) ⟨9136268, by rfl⟩ : syracuseStep 12181691 = 18272537) B18272537
theorem B8121127 : Blo 2109435 8121127 := bstep (se 1 (by rfl) ⟨6090845, by rfl⟩ : syracuseStep 8121127 = 12181691) B12181691
theorem B10828169 : Blo 2109435 10828169 := bstep (se 2 (by rfl) ⟨4060563, by rfl⟩ : syracuseStep 10828169 = 8121127) B8121127
theorem B7218779 : Blo 2109435 7218779 := bstep (se 1 (by rfl) ⟨5414084, by rfl⟩ : syracuseStep 7218779 = 10828169) B10828169
theorem B19250077 : Blo 2109435 19250077 := bstep (se 3 (by rfl) ⟨3609389, by rfl⟩ : syracuseStep 19250077 = 7218779) B7218779
theorem B25666769 : Blo 2109435 25666769 := bstep (se 2 (by rfl) ⟨9625038, by rfl⟩ : syracuseStep 25666769 = 19250077) B19250077
theorem B17111179 : Blo 2109435 17111179 := bstep (se 1 (by rfl) ⟨12833384, by rfl⟩ : syracuseStep 17111179 = 25666769) B25666769
theorem B22814905 : Blo 2109435 22814905 := bstep (se 2 (by rfl) ⟨8555589, by rfl⟩ : syracuseStep 22814905 = 17111179) B17111179
theorem B30419873 : Blo 2109435 30419873 := bstep (se 2 (by rfl) ⟨11407452, by rfl⟩ : syracuseStep 30419873 = 22814905) B22814905
theorem B20279915 : Blo 2109435 20279915 := bstep (se 1 (by rfl) ⟨15209936, by rfl⟩ : syracuseStep 20279915 = 30419873) B30419873
theorem B13519943 : Blo 2109435 13519943 := bstep (se 1 (by rfl) ⟨10139957, by rfl⟩ : syracuseStep 13519943 = 20279915) B20279915
theorem B9013295 : Blo 2109435 9013295 := bstep (se 1 (by rfl) ⟨6759971, by rfl⟩ : syracuseStep 9013295 = 13519943) B13519943
theorem B6008863 : Blo 2109435 6008863 := bstep (se 1 (by rfl) ⟨4506647, by rfl⟩ : syracuseStep 6008863 = 9013295) B9013295
theorem B8011817 : Blo 2109435 8011817 := bstep (se 2 (by rfl) ⟨3004431, by rfl⟩ : syracuseStep 8011817 = 6008863) B6008863
theorem B5341211 : Blo 2109435 5341211 := bstep (se 1 (by rfl) ⟨4005908, by rfl⟩ : syracuseStep 5341211 = 8011817) B8011817
theorem B3560807 : Blo 2109435 3560807 := bstep (se 1 (by rfl) ⟨2670605, by rfl⟩ : syracuseStep 3560807 = 5341211) B5341211
theorem B2373871 : Blo 2109435 2373871 := bstep (se 1 (by rfl) ⟨1780403, by rfl⟩ : syracuseStep 2373871 = 3560807) B3560807
theorem B3165161 : Blo 2109435 3165161 := bstep (se 2 (by rfl) ⟨1186935, by rfl⟩ : syracuseStep 3165161 = 2373871) B2373871
theorem B2110107 : Blo 2109435 2110107 := bstep (se 1 (by rfl) ⟨1582580, by rfl⟩ : syracuseStep 2110107 = 3165161) B3165161
theorem B3252125 : Blo 2109435 3252125 := bbase (se 3 (by rfl) ⟨609773, by rfl⟩ : syracuseStep 3252125 = 1219547) (by norm_num)
theorem B2168083 : Blo 2109435 2168083 := bstep (se 1 (by rfl) ⟨1626062, by rfl⟩ : syracuseStep 2168083 = 3252125) B3252125
theorem B11563109 : Blo 2109435 11563109 := bstep (se 4 (by rfl) ⟨1084041, by rfl⟩ : syracuseStep 11563109 = 2168083) B2168083
theorem B123339829 : Blo 2109435 123339829 := bstep (se 5 (by rfl) ⟨5781554, by rfl⟩ : syracuseStep 123339829 = 11563109) B11563109
theorem B164453105 : Blo 2109435 164453105 := bstep (se 2 (by rfl) ⟨61669914, by rfl⟩ : syracuseStep 164453105 = 123339829) B123339829
theorem B109635403 : Blo 2109435 109635403 := bstep (se 1 (by rfl) ⟨82226552, by rfl⟩ : syracuseStep 109635403 = 164453105) B164453105
theorem B146180537 : Blo 2109435 146180537 := bstep (se 2 (by rfl) ⟨54817701, by rfl⟩ : syracuseStep 146180537 = 109635403) B109635403
theorem B97453691 : Blo 2109435 97453691 := bstep (se 1 (by rfl) ⟨73090268, by rfl⟩ : syracuseStep 97453691 = 146180537) B146180537
theorem B64969127 : Blo 2109435 64969127 := bstep (se 1 (by rfl) ⟨48726845, by rfl⟩ : syracuseStep 64969127 = 97453691) B97453691
theorem B43312751 : Blo 2109435 43312751 := bstep (se 1 (by rfl) ⟨32484563, by rfl⟩ : syracuseStep 43312751 = 64969127) B64969127
theorem B28875167 : Blo 2109435 28875167 := bstep (se 1 (by rfl) ⟨21656375, by rfl⟩ : syracuseStep 28875167 = 43312751) B43312751
theorem B19250111 : Blo 2109435 19250111 := bstep (se 1 (by rfl) ⟨14437583, by rfl⟩ : syracuseStep 19250111 = 28875167) B28875167
theorem B12833407 : Blo 2109435 12833407 := bstep (se 1 (by rfl) ⟨9625055, by rfl⟩ : syracuseStep 12833407 = 19250111) B19250111
theorem B17111209 : Blo 2109435 17111209 := bstep (se 2 (by rfl) ⟨6416703, by rfl⟩ : syracuseStep 17111209 = 12833407) B12833407
theorem B22814945 : Blo 2109435 22814945 := bstep (se 2 (by rfl) ⟨8555604, by rfl⟩ : syracuseStep 22814945 = 17111209) B17111209
theorem B15209963 : Blo 2109435 15209963 := bstep (se 1 (by rfl) ⟨11407472, by rfl⟩ : syracuseStep 15209963 = 22814945) B22814945
theorem B10139975 : Blo 2109435 10139975 := bstep (se 1 (by rfl) ⟨7604981, by rfl⟩ : syracuseStep 10139975 = 15209963) B15209963
theorem B6759983 : Blo 2109435 6759983 := bstep (se 1 (by rfl) ⟨5069987, by rfl⟩ : syracuseStep 6759983 = 10139975) B10139975
theorem B18026621 : Blo 2109435 18026621 := bstep (se 3 (by rfl) ⟨3379991, by rfl⟩ : syracuseStep 18026621 = 6759983) B6759983
theorem B12017747 : Blo 2109435 12017747 := bstep (se 1 (by rfl) ⟨9013310, by rfl⟩ : syracuseStep 12017747 = 18026621) B18026621
theorem B8011831 : Blo 2109435 8011831 := bstep (se 1 (by rfl) ⟨6008873, by rfl⟩ : syracuseStep 8011831 = 12017747) B12017747
theorem B10682441 : Blo 2109435 10682441 := bstep (se 2 (by rfl) ⟨4005915, by rfl⟩ : syracuseStep 10682441 = 8011831) B8011831
theorem B7121627 : Blo 2109435 7121627 := bstep (se 1 (by rfl) ⟨5341220, by rfl⟩ : syracuseStep 7121627 = 10682441) B10682441
theorem B4747751 : Blo 2109435 4747751 := bstep (se 1 (by rfl) ⟨3560813, by rfl⟩ : syracuseStep 4747751 = 7121627) B7121627
theorem B3165167 : Blo 2109435 3165167 := bstep (se 1 (by rfl) ⟨2373875, by rfl⟩ : syracuseStep 3165167 = 4747751) B4747751
theorem B2110111 : Blo 2109435 2110111 := bstep (se 1 (by rfl) ⟨1582583, by rfl⟩ : syracuseStep 2110111 = 3165167) B3165167
theorem B3165173 : Blo 2109435 3165173 := bbase (se 5 (by rfl) ⟨148367, by rfl⟩ : syracuseStep 3165173 = 296735) (by norm_num)
theorem B2110115 : Blo 2109435 2110115 := bstep (se 1 (by rfl) ⟨1582586, by rfl⟩ : syracuseStep 2110115 = 3165173) B3165173
theorem B3380005 : Blo 2109435 3380005 := bbase (se 4 (by rfl) ⟨316875, by rfl⟩ : syracuseStep 3380005 = 633751) (by norm_num)
theorem B4506673 : Blo 2109435 4506673 := bstep (se 2 (by rfl) ⟨1690002, by rfl⟩ : syracuseStep 4506673 = 3380005) B3380005
theorem B6008897 : Blo 2109435 6008897 := bstep (se 2 (by rfl) ⟨2253336, by rfl⟩ : syracuseStep 6008897 = 4506673) B4506673
theorem B4005931 : Blo 2109435 4005931 := bstep (se 1 (by rfl) ⟨3004448, by rfl⟩ : syracuseStep 4005931 = 6008897) B6008897
theorem B5341241 : Blo 2109435 5341241 := bstep (se 2 (by rfl) ⟨2002965, by rfl⟩ : syracuseStep 5341241 = 4005931) B4005931
theorem B3560827 : Blo 2109435 3560827 := bstep (se 1 (by rfl) ⟨2670620, by rfl⟩ : syracuseStep 3560827 = 5341241) B5341241
theorem B4747769 : Blo 2109435 4747769 := bstep (se 2 (by rfl) ⟨1780413, by rfl⟩ : syracuseStep 4747769 = 3560827) B3560827
theorem B3165179 : Blo 2109435 3165179 := bstep (se 1 (by rfl) ⟨2373884, by rfl⟩ : syracuseStep 3165179 = 4747769) B4747769
theorem B2110119 : Blo 2109435 2110119 := bstep (se 1 (by rfl) ⟨1582589, by rfl⟩ : syracuseStep 2110119 = 3165179) B3165179
theorem B2373889 : Blo 2109435 2373889 := bbase (se 2 (by rfl) ⟨890208, by rfl⟩ : syracuseStep 2373889 = 1780417) (by norm_num)
theorem B3165185 : Blo 2109435 3165185 := bstep (se 2 (by rfl) ⟨1186944, by rfl⟩ : syracuseStep 3165185 = 2373889) B2373889
theorem B2110123 : Blo 2109435 2110123 := bstep (se 1 (by rfl) ⟨1582592, by rfl⟩ : syracuseStep 2110123 = 3165185) B3165185
theorem B5341261 : Blo 2109435 5341261 := bbase (se 3 (by rfl) ⟨1001486, by rfl⟩ : syracuseStep 5341261 = 2002973) (by norm_num)
theorem B7121681 : Blo 2109435 7121681 := bstep (se 2 (by rfl) ⟨2670630, by rfl⟩ : syracuseStep 7121681 = 5341261) B5341261
theorem B4747787 : Blo 2109435 4747787 := bstep (se 1 (by rfl) ⟨3560840, by rfl⟩ : syracuseStep 4747787 = 7121681) B7121681
theorem B3165191 : Blo 2109435 3165191 := bstep (se 1 (by rfl) ⟨2373893, by rfl⟩ : syracuseStep 3165191 = 4747787) B4747787
theorem B2110127 : Blo 2109435 2110127 := bstep (se 1 (by rfl) ⟨1582595, by rfl⟩ : syracuseStep 2110127 = 3165191) B3165191
theorem B3165197 : Blo 2109435 3165197 := bbase (se 3 (by rfl) ⟨593474, by rfl⟩ : syracuseStep 3165197 = 1186949) (by norm_num)
theorem B2110131 : Blo 2109435 2110131 := bstep (se 1 (by rfl) ⟨1582598, by rfl⟩ : syracuseStep 2110131 = 3165197) B3165197
theorem B4747805 : Blo 2109435 4747805 := bbase (se 3 (by rfl) ⟨890213, by rfl⟩ : syracuseStep 4747805 = 1780427) (by norm_num)
theorem B3165203 : Blo 2109435 3165203 := bstep (se 1 (by rfl) ⟨2373902, by rfl⟩ : syracuseStep 3165203 = 4747805) B4747805
theorem B2110135 : Blo 2109435 2110135 := bstep (se 1 (by rfl) ⟨1582601, by rfl⟩ : syracuseStep 2110135 = 3165203) B3165203
theorem B3560861 : Blo 2109435 3560861 := bbase (se 3 (by rfl) ⟨667661, by rfl⟩ : syracuseStep 3560861 = 1335323) (by norm_num)
theorem B2373907 : Blo 2109435 2373907 := bstep (se 1 (by rfl) ⟨1780430, by rfl⟩ : syracuseStep 2373907 = 3560861) B3560861
theorem B3165209 : Blo 2109435 3165209 := bstep (se 2 (by rfl) ⟨1186953, by rfl⟩ : syracuseStep 3165209 = 2373907) B2373907
theorem B2110139 : Blo 2109435 2110139 := bstep (se 1 (by rfl) ⟨1582604, by rfl⟩ : syracuseStep 2110139 = 3165209) B3165209
theorem B4568213 : Blo 2109435 4568213 := bbase (se 6 (by rfl) ⟨107067, by rfl⟩ : syracuseStep 4568213 = 214135) (by norm_num)
theorem B3045475 : Blo 2109435 3045475 := bstep (se 1 (by rfl) ⟨2284106, by rfl⟩ : syracuseStep 3045475 = 4568213) B4568213
theorem B4060633 : Blo 2109435 4060633 := bstep (se 2 (by rfl) ⟨1522737, by rfl⟩ : syracuseStep 4060633 = 3045475) B3045475
theorem B5414177 : Blo 2109435 5414177 := bstep (se 2 (by rfl) ⟨2030316, by rfl⟩ : syracuseStep 5414177 = 4060633) B4060633
theorem B3609451 : Blo 2109435 3609451 := bstep (se 1 (by rfl) ⟨2707088, by rfl⟩ : syracuseStep 3609451 = 5414177) B5414177
theorem B4812601 : Blo 2109435 4812601 := bstep (se 2 (by rfl) ⟨1804725, by rfl⟩ : syracuseStep 4812601 = 3609451) B3609451
theorem B6416801 : Blo 2109435 6416801 := bstep (se 2 (by rfl) ⟨2406300, by rfl⟩ : syracuseStep 6416801 = 4812601) B4812601
theorem B4277867 : Blo 2109435 4277867 := bstep (se 1 (by rfl) ⟨3208400, by rfl⟩ : syracuseStep 4277867 = 6416801) B6416801
theorem B11407645 : Blo 2109435 11407645 := bstep (se 3 (by rfl) ⟨2138933, by rfl⟩ : syracuseStep 11407645 = 4277867) B4277867
theorem B15210193 : Blo 2109435 15210193 := bstep (se 2 (by rfl) ⟨5703822, by rfl⟩ : syracuseStep 15210193 = 11407645) B11407645
theorem B20280257 : Blo 2109435 20280257 := bstep (se 2 (by rfl) ⟨7605096, by rfl⟩ : syracuseStep 20280257 = 15210193) B15210193
theorem B13520171 : Blo 2109435 13520171 := bstep (se 1 (by rfl) ⟨10140128, by rfl⟩ : syracuseStep 13520171 = 20280257) B20280257
theorem B9013447 : Blo 2109435 9013447 := bstep (se 1 (by rfl) ⟨6760085, by rfl⟩ : syracuseStep 9013447 = 13520171) B13520171
theorem B12017929 : Blo 2109435 12017929 := bstep (se 2 (by rfl) ⟨4506723, by rfl⟩ : syracuseStep 12017929 = 9013447) B9013447
theorem B16023905 : Blo 2109435 16023905 := bstep (se 2 (by rfl) ⟨6008964, by rfl⟩ : syracuseStep 16023905 = 12017929) B12017929
theorem B10682603 : Blo 2109435 10682603 := bstep (se 1 (by rfl) ⟨8011952, by rfl⟩ : syracuseStep 10682603 = 16023905) B16023905
theorem B7121735 : Blo 2109435 7121735 := bstep (se 1 (by rfl) ⟨5341301, by rfl⟩ : syracuseStep 7121735 = 10682603) B10682603
theorem B4747823 : Blo 2109435 4747823 := bstep (se 1 (by rfl) ⟨3560867, by rfl⟩ : syracuseStep 4747823 = 7121735) B7121735
theorem B3165215 : Blo 2109435 3165215 := bstep (se 1 (by rfl) ⟨2373911, by rfl⟩ : syracuseStep 3165215 = 4747823) B4747823
theorem B2110143 : Blo 2109435 2110143 := bstep (se 1 (by rfl) ⟨1582607, by rfl⟩ : syracuseStep 2110143 = 3165215) B3165215
theorem B3165221 : Blo 2109435 3165221 := bbase (se 4 (by rfl) ⟨296739, by rfl⟩ : syracuseStep 3165221 = 593479) (by norm_num)
theorem B2110147 : Blo 2109435 2110147 := bstep (se 1 (by rfl) ⟨1582610, by rfl⟩ : syracuseStep 2110147 = 3165221) B3165221
theorem B2670661 : Blo 2109435 2670661 := bbase (se 4 (by rfl) ⟨250374, by rfl⟩ : syracuseStep 2670661 = 500749) (by norm_num)
theorem B3560881 : Blo 2109435 3560881 := bstep (se 2 (by rfl) ⟨1335330, by rfl⟩ : syracuseStep 3560881 = 2670661) B2670661
theorem B4747841 : Blo 2109435 4747841 := bstep (se 2 (by rfl) ⟨1780440, by rfl⟩ : syracuseStep 4747841 = 3560881) B3560881
theorem B3165227 : Blo 2109435 3165227 := bstep (se 1 (by rfl) ⟨2373920, by rfl⟩ : syracuseStep 3165227 = 4747841) B4747841
theorem B2110151 : Blo 2109435 2110151 := bstep (se 1 (by rfl) ⟨1582613, by rfl⟩ : syracuseStep 2110151 = 3165227) B3165227
theorem B2373925 : Blo 2109435 2373925 := bbase (se 4 (by rfl) ⟨222555, by rfl⟩ : syracuseStep 2373925 = 445111) (by norm_num)
theorem B3165233 : Blo 2109435 3165233 := bstep (se 2 (by rfl) ⟨1186962, by rfl⟩ : syracuseStep 3165233 = 2373925) B2373925
theorem B2110155 : Blo 2109435 2110155 := bstep (se 1 (by rfl) ⟨1582616, by rfl⟩ : syracuseStep 2110155 = 3165233) B3165233
theorem B3380069 : Blo 2109435 3380069 := bbase (se 4 (by rfl) ⟨316881, by rfl⟩ : syracuseStep 3380069 = 633763) (by norm_num)
theorem B9013517 : Blo 2109435 9013517 := bstep (se 3 (by rfl) ⟨1690034, by rfl⟩ : syracuseStep 9013517 = 3380069) B3380069
theorem B6009011 : Blo 2109435 6009011 := bstep (se 1 (by rfl) ⟨4506758, by rfl⟩ : syracuseStep 6009011 = 9013517) B9013517
theorem B4006007 : Blo 2109435 4006007 := bstep (se 1 (by rfl) ⟨3004505, by rfl⟩ : syracuseStep 4006007 = 6009011) B6009011
theorem B2670671 : Blo 2109435 2670671 := bstep (se 1 (by rfl) ⟨2003003, by rfl⟩ : syracuseStep 2670671 = 4006007) B4006007
theorem B7121789 : Blo 2109435 7121789 := bstep (se 3 (by rfl) ⟨1335335, by rfl⟩ : syracuseStep 7121789 = 2670671) B2670671
theorem B4747859 : Blo 2109435 4747859 := bstep (se 1 (by rfl) ⟨3560894, by rfl⟩ : syracuseStep 4747859 = 7121789) B7121789
theorem B3165239 : Blo 2109435 3165239 := bstep (se 1 (by rfl) ⟨2373929, by rfl⟩ : syracuseStep 3165239 = 4747859) B4747859
theorem B2110159 : Blo 2109435 2110159 := bstep (se 1 (by rfl) ⟨1582619, by rfl⟩ : syracuseStep 2110159 = 3165239) B3165239
theorem B3165245 : Blo 2109435 3165245 := bbase (se 3 (by rfl) ⟨593483, by rfl⟩ : syracuseStep 3165245 = 1186967) (by norm_num)
theorem B2110163 : Blo 2109435 2110163 := bstep (se 1 (by rfl) ⟨1582622, by rfl⟩ : syracuseStep 2110163 = 3165245) B3165245
theorem B4747877 : Blo 2109435 4747877 := bbase (se 4 (by rfl) ⟨445113, by rfl⟩ : syracuseStep 4747877 = 890227) (by norm_num)
theorem B3165251 : Blo 2109435 3165251 := bstep (se 1 (by rfl) ⟨2373938, by rfl⟩ : syracuseStep 3165251 = 4747877) B4747877
theorem B2110167 : Blo 2109435 2110167 := bstep (se 1 (by rfl) ⟨1582625, by rfl⟩ : syracuseStep 2110167 = 3165251) B3165251
theorem B5341373 : Blo 2109435 5341373 := bbase (se 3 (by rfl) ⟨1001507, by rfl⟩ : syracuseStep 5341373 = 2003015) (by norm_num)
theorem B3560915 : Blo 2109435 3560915 := bstep (se 1 (by rfl) ⟨2670686, by rfl⟩ : syracuseStep 3560915 = 5341373) B5341373
theorem B2373943 : Blo 2109435 2373943 := bstep (se 1 (by rfl) ⟨1780457, by rfl⟩ : syracuseStep 2373943 = 3560915) B3560915
theorem B3165257 : Blo 2109435 3165257 := bstep (se 2 (by rfl) ⟨1186971, by rfl⟩ : syracuseStep 3165257 = 2373943) B2373943
theorem B2110171 : Blo 2109435 2110171 := bstep (se 1 (by rfl) ⟨1582628, by rfl⟩ : syracuseStep 2110171 = 3165257) B3165257
theorem B4006037 : Blo 2109435 4006037 := bbase (se 6 (by rfl) ⟨93891, by rfl⟩ : syracuseStep 4006037 = 187783) (by norm_num)
theorem B10682765 : Blo 2109435 10682765 := bstep (se 3 (by rfl) ⟨2003018, by rfl⟩ : syracuseStep 10682765 = 4006037) B4006037
theorem B7121843 : Blo 2109435 7121843 := bstep (se 1 (by rfl) ⟨5341382, by rfl⟩ : syracuseStep 7121843 = 10682765) B10682765
theorem B4747895 : Blo 2109435 4747895 := bstep (se 1 (by rfl) ⟨3560921, by rfl⟩ : syracuseStep 4747895 = 7121843) B7121843
theorem B3165263 : Blo 2109435 3165263 := bstep (se 1 (by rfl) ⟨2373947, by rfl⟩ : syracuseStep 3165263 = 4747895) B4747895
theorem B2110175 : Blo 2109435 2110175 := bstep (se 1 (by rfl) ⟨1582631, by rfl⟩ : syracuseStep 2110175 = 3165263) B3165263
theorem B3165269 : Blo 2109435 3165269 := bbase (se 8 (by rfl) ⟨18546, by rfl⟩ : syracuseStep 3165269 = 37093) (by norm_num)
theorem B2110179 : Blo 2109435 2110179 := bstep (se 1 (by rfl) ⟨1582634, by rfl⟩ : syracuseStep 2110179 = 3165269) B3165269
theorem B3802621 : Blo 2109435 3802621 := bbase (se 3 (by rfl) ⟨712991, by rfl⟩ : syracuseStep 3802621 = 1425983) (by norm_num)
theorem B5070161 : Blo 2109435 5070161 := bstep (se 2 (by rfl) ⟨1901310, by rfl⟩ : syracuseStep 5070161 = 3802621) B3802621
theorem B13520429 : Blo 2109435 13520429 := bstep (se 3 (by rfl) ⟨2535080, by rfl⟩ : syracuseStep 13520429 = 5070161) B5070161
theorem B9013619 : Blo 2109435 9013619 := bstep (se 1 (by rfl) ⟨6760214, by rfl⟩ : syracuseStep 9013619 = 13520429) B13520429
theorem B6009079 : Blo 2109435 6009079 := bstep (se 1 (by rfl) ⟨4506809, by rfl⟩ : syracuseStep 6009079 = 9013619) B9013619
theorem B8012105 : Blo 2109435 8012105 := bstep (se 2 (by rfl) ⟨3004539, by rfl⟩ : syracuseStep 8012105 = 6009079) B6009079
theorem B5341403 : Blo 2109435 5341403 := bstep (se 1 (by rfl) ⟨4006052, by rfl⟩ : syracuseStep 5341403 = 8012105) B8012105
theorem B3560935 : Blo 2109435 3560935 := bstep (se 1 (by rfl) ⟨2670701, by rfl⟩ : syracuseStep 3560935 = 5341403) B5341403
theorem B4747913 : Blo 2109435 4747913 := bstep (se 2 (by rfl) ⟨1780467, by rfl⟩ : syracuseStep 4747913 = 3560935) B3560935
theorem B3165275 : Blo 2109435 3165275 := bstep (se 1 (by rfl) ⟨2373956, by rfl⟩ : syracuseStep 3165275 = 4747913) B4747913
theorem B2110183 : Blo 2109435 2110183 := bstep (se 1 (by rfl) ⟨1582637, by rfl⟩ : syracuseStep 2110183 = 3165275) B3165275
theorem B2373961 : Blo 2109435 2373961 := bbase (se 2 (by rfl) ⟨890235, by rfl⟩ : syracuseStep 2373961 = 1780471) (by norm_num)
theorem B3165281 : Blo 2109435 3165281 := bstep (se 2 (by rfl) ⟨1186980, by rfl⟩ : syracuseStep 3165281 = 2373961) B2373961
theorem B2110187 : Blo 2109435 2110187 := bstep (se 1 (by rfl) ⟨1582640, by rfl⟩ : syracuseStep 2110187 = 3165281) B3165281
theorem B3609533 : Blo 2109435 3609533 := bbase (se 3 (by rfl) ⟨676787, by rfl⟩ : syracuseStep 3609533 = 1353575) (by norm_num)
theorem B2406355 : Blo 2109435 2406355 := bstep (se 1 (by rfl) ⟨1804766, by rfl⟩ : syracuseStep 2406355 = 3609533) B3609533
theorem B12833893 : Blo 2109435 12833893 := bstep (se 4 (by rfl) ⟨1203177, by rfl⟩ : syracuseStep 12833893 = 2406355) B2406355
theorem B68447429 : Blo 2109435 68447429 := bstep (se 4 (by rfl) ⟨6416946, by rfl⟩ : syracuseStep 68447429 = 12833893) B12833893
theorem B45631619 : Blo 2109435 45631619 := bstep (se 1 (by rfl) ⟨34223714, by rfl⟩ : syracuseStep 45631619 = 68447429) B68447429
theorem B30421079 : Blo 2109435 30421079 := bstep (se 1 (by rfl) ⟨22815809, by rfl⟩ : syracuseStep 30421079 = 45631619) B45631619
theorem B20280719 : Blo 2109435 20280719 := bstep (se 1 (by rfl) ⟨15210539, by rfl⟩ : syracuseStep 20280719 = 30421079) B30421079
theorem B13520479 : Blo 2109435 13520479 := bstep (se 1 (by rfl) ⟨10140359, by rfl⟩ : syracuseStep 13520479 = 20280719) B20280719
theorem B18027305 : Blo 2109435 18027305 := bstep (se 2 (by rfl) ⟨6760239, by rfl⟩ : syracuseStep 18027305 = 13520479) B13520479
theorem B12018203 : Blo 2109435 12018203 := bstep (se 1 (by rfl) ⟨9013652, by rfl⟩ : syracuseStep 12018203 = 18027305) B18027305
theorem B8012135 : Blo 2109435 8012135 := bstep (se 1 (by rfl) ⟨6009101, by rfl⟩ : syracuseStep 8012135 = 12018203) B12018203
theorem B5341423 : Blo 2109435 5341423 := bstep (se 1 (by rfl) ⟨4006067, by rfl⟩ : syracuseStep 5341423 = 8012135) B8012135
theorem B7121897 : Blo 2109435 7121897 := bstep (se 2 (by rfl) ⟨2670711, by rfl⟩ : syracuseStep 7121897 = 5341423) B5341423
theorem B4747931 : Blo 2109435 4747931 := bstep (se 1 (by rfl) ⟨3560948, by rfl⟩ : syracuseStep 4747931 = 7121897) B7121897
theorem B3165287 : Blo 2109435 3165287 := bstep (se 1 (by rfl) ⟨2373965, by rfl⟩ : syracuseStep 3165287 = 4747931) B4747931
theorem B2110191 : Blo 2109435 2110191 := bstep (se 1 (by rfl) ⟨1582643, by rfl⟩ : syracuseStep 2110191 = 3165287) B3165287
theorem B3165293 : Blo 2109435 3165293 := bbase (se 3 (by rfl) ⟨593492, by rfl⟩ : syracuseStep 3165293 = 1186985) (by norm_num)
theorem B2110195 : Blo 2109435 2110195 := bstep (se 1 (by rfl) ⟨1582646, by rfl⟩ : syracuseStep 2110195 = 3165293) B3165293
theorem B4747949 : Blo 2109435 4747949 := bbase (se 3 (by rfl) ⟨890240, by rfl⟩ : syracuseStep 4747949 = 1780481) (by norm_num)
theorem B3165299 : Blo 2109435 3165299 := bstep (se 1 (by rfl) ⟨2373974, by rfl⟩ : syracuseStep 3165299 = 4747949) B4747949
theorem B2110199 : Blo 2109435 2110199 := bstep (se 1 (by rfl) ⟨1582649, by rfl⟩ : syracuseStep 2110199 = 3165299) B3165299
theorem B4506853 : Blo 2109435 4506853 := bbase (se 4 (by rfl) ⟨422517, by rfl⟩ : syracuseStep 4506853 = 845035) (by norm_num)
theorem B6009137 : Blo 2109435 6009137 := bstep (se 2 (by rfl) ⟨2253426, by rfl⟩ : syracuseStep 6009137 = 4506853) B4506853
theorem B4006091 : Blo 2109435 4006091 := bstep (se 1 (by rfl) ⟨3004568, by rfl⟩ : syracuseStep 4006091 = 6009137) B6009137
theorem B2670727 : Blo 2109435 2670727 := bstep (se 1 (by rfl) ⟨2003045, by rfl⟩ : syracuseStep 2670727 = 4006091) B4006091
theorem B3560969 : Blo 2109435 3560969 := bstep (se 2 (by rfl) ⟨1335363, by rfl⟩ : syracuseStep 3560969 = 2670727) B2670727
theorem B2373979 : Blo 2109435 2373979 := bstep (se 1 (by rfl) ⟨1780484, by rfl⟩ : syracuseStep 2373979 = 3560969) B3560969
theorem B3165305 : Blo 2109435 3165305 := bstep (se 2 (by rfl) ⟨1186989, by rfl⟩ : syracuseStep 3165305 = 2373979) B2373979
theorem B2110203 : Blo 2109435 2110203 := bstep (se 1 (by rfl) ⟨1582652, by rfl⟩ : syracuseStep 2110203 = 3165305) B3165305
theorem B2406373 : Blo 2109435 2406373 := bbase (se 4 (by rfl) ⟨225597, by rfl⟩ : syracuseStep 2406373 = 451195) (by norm_num)
theorem B51335957 : Blo 2109435 51335957 := bstep (se 6 (by rfl) ⟨1203186, by rfl⟩ : syracuseStep 51335957 = 2406373) B2406373
theorem B34223971 : Blo 2109435 34223971 := bstep (se 1 (by rfl) ⟨25667978, by rfl⟩ : syracuseStep 34223971 = 51335957) B51335957
theorem B45631961 : Blo 2109435 45631961 := bstep (se 2 (by rfl) ⟨17111985, by rfl⟩ : syracuseStep 45631961 = 34223971) B34223971
theorem B30421307 : Blo 2109435 30421307 := bstep (se 1 (by rfl) ⟨22815980, by rfl⟩ : syracuseStep 30421307 = 45631961) B45631961
theorem B20280871 : Blo 2109435 20280871 := bstep (se 1 (by rfl) ⟨15210653, by rfl⟩ : syracuseStep 20280871 = 30421307) B30421307
theorem B27041161 : Blo 2109435 27041161 := bstep (se 2 (by rfl) ⟨10140435, by rfl⟩ : syracuseStep 27041161 = 20280871) B20280871
theorem B36054881 : Blo 2109435 36054881 := bstep (se 2 (by rfl) ⟨13520580, by rfl⟩ : syracuseStep 36054881 = 27041161) B27041161
theorem B24036587 : Blo 2109435 24036587 := bstep (se 1 (by rfl) ⟨18027440, by rfl⟩ : syracuseStep 24036587 = 36054881) B36054881
theorem B16024391 : Blo 2109435 16024391 := bstep (se 1 (by rfl) ⟨12018293, by rfl⟩ : syracuseStep 16024391 = 24036587) B24036587
theorem B10682927 : Blo 2109435 10682927 := bstep (se 1 (by rfl) ⟨8012195, by rfl⟩ : syracuseStep 10682927 = 16024391) B16024391
theorem B7121951 : Blo 2109435 7121951 := bstep (se 1 (by rfl) ⟨5341463, by rfl⟩ : syracuseStep 7121951 = 10682927) B10682927
theorem B4747967 : Blo 2109435 4747967 := bstep (se 1 (by rfl) ⟨3560975, by rfl⟩ : syracuseStep 4747967 = 7121951) B7121951
theorem B3165311 : Blo 2109435 3165311 := bstep (se 1 (by rfl) ⟨2373983, by rfl⟩ : syracuseStep 3165311 = 4747967) B4747967
theorem B2110207 : Blo 2109435 2110207 := bstep (se 1 (by rfl) ⟨1582655, by rfl⟩ : syracuseStep 2110207 = 3165311) B3165311
theorem B3165317 : Blo 2109435 3165317 := bbase (se 4 (by rfl) ⟨296748, by rfl⟩ : syracuseStep 3165317 = 593497) (by norm_num)
theorem B2110211 : Blo 2109435 2110211 := bstep (se 1 (by rfl) ⟨1582658, by rfl⟩ : syracuseStep 2110211 = 3165317) B3165317
theorem B3560989 : Blo 2109435 3560989 := bbase (se 3 (by rfl) ⟨667685, by rfl⟩ : syracuseStep 3560989 = 1335371) (by norm_num)
theorem B4747985 : Blo 2109435 4747985 := bstep (se 2 (by rfl) ⟨1780494, by rfl⟩ : syracuseStep 4747985 = 3560989) B3560989
theorem B3165323 : Blo 2109435 3165323 := bstep (se 1 (by rfl) ⟨2373992, by rfl⟩ : syracuseStep 3165323 = 4747985) B4747985
theorem B2110215 : Blo 2109435 2110215 := bstep (se 1 (by rfl) ⟨1582661, by rfl⟩ : syracuseStep 2110215 = 3165323) B3165323
theorem B2373997 : Blo 2109435 2373997 := bbase (se 3 (by rfl) ⟨445124, by rfl⟩ : syracuseStep 2373997 = 890249) (by norm_num)
theorem B3165329 : Blo 2109435 3165329 := bstep (se 2 (by rfl) ⟨1186998, by rfl⟩ : syracuseStep 3165329 = 2373997) B2373997
theorem B2110219 : Blo 2109435 2110219 := bstep (se 1 (by rfl) ⟨1582664, by rfl⟩ : syracuseStep 2110219 = 3165329) B3165329
theorem B7122005 : Blo 2109435 7122005 := bbase (se 8 (by rfl) ⟨41730, by rfl⟩ : syracuseStep 7122005 = 83461) (by norm_num)
theorem B4748003 : Blo 2109435 4748003 := bstep (se 1 (by rfl) ⟨3561002, by rfl⟩ : syracuseStep 4748003 = 7122005) B7122005
theorem B3165335 : Blo 2109435 3165335 := bstep (se 1 (by rfl) ⟨2374001, by rfl⟩ : syracuseStep 3165335 = 4748003) B4748003
theorem B2110223 : Blo 2109435 2110223 := bstep (se 1 (by rfl) ⟨1582667, by rfl⟩ : syracuseStep 2110223 = 3165335) B3165335
theorem B3165341 : Blo 2109435 3165341 := bbase (se 3 (by rfl) ⟨593501, by rfl⟩ : syracuseStep 3165341 = 1187003) (by norm_num)
theorem B2110227 : Blo 2109435 2110227 := bstep (se 1 (by rfl) ⟨1582670, by rfl⟩ : syracuseStep 2110227 = 3165341) B3165341
theorem B4748021 : Blo 2109435 4748021 := bbase (se 5 (by rfl) ⟨222563, by rfl⟩ : syracuseStep 4748021 = 445127) (by norm_num)
theorem B3165347 : Blo 2109435 3165347 := bstep (se 1 (by rfl) ⟨2374010, by rfl⟩ : syracuseStep 3165347 = 4748021) B4748021
theorem B2110231 : Blo 2109435 2110231 := bstep (se 1 (by rfl) ⟨1582673, by rfl⟩ : syracuseStep 2110231 = 3165347) B3165347
theorem B4568413 : Blo 2109435 4568413 := bbase (se 3 (by rfl) ⟨856577, by rfl⟩ : syracuseStep 4568413 = 1713155) (by norm_num)
theorem B6091217 : Blo 2109435 6091217 := bstep (se 2 (by rfl) ⟨2284206, by rfl⟩ : syracuseStep 6091217 = 4568413) B4568413
theorem B4060811 : Blo 2109435 4060811 := bstep (se 1 (by rfl) ⟨3045608, by rfl⟩ : syracuseStep 4060811 = 6091217) B6091217
theorem B10828829 : Blo 2109435 10828829 := bstep (se 3 (by rfl) ⟨2030405, by rfl⟩ : syracuseStep 10828829 = 4060811) B4060811
theorem B7219219 : Blo 2109435 7219219 := bstep (se 1 (by rfl) ⟨5414414, by rfl⟩ : syracuseStep 7219219 = 10828829) B10828829
theorem B9625625 : Blo 2109435 9625625 := bstep (se 2 (by rfl) ⟨3609609, by rfl⟩ : syracuseStep 9625625 = 7219219) B7219219
theorem B6417083 : Blo 2109435 6417083 := bstep (se 1 (by rfl) ⟨4812812, by rfl⟩ : syracuseStep 6417083 = 9625625) B9625625
theorem B4278055 : Blo 2109435 4278055 := bstep (se 1 (by rfl) ⟨3208541, by rfl⟩ : syracuseStep 4278055 = 6417083) B6417083
theorem B5704073 : Blo 2109435 5704073 := bstep (se 2 (by rfl) ⟨2139027, by rfl⟩ : syracuseStep 5704073 = 4278055) B4278055
theorem B3802715 : Blo 2109435 3802715 := bstep (se 1 (by rfl) ⟨2852036, by rfl⟩ : syracuseStep 3802715 = 5704073) B5704073
theorem B2535143 : Blo 2109435 2535143 := bstep (se 1 (by rfl) ⟨1901357, by rfl⟩ : syracuseStep 2535143 = 3802715) B3802715
theorem B27041525 : Blo 2109435 27041525 := bstep (se 5 (by rfl) ⟨1267571, by rfl⟩ : syracuseStep 27041525 = 2535143) B2535143
theorem B18027683 : Blo 2109435 18027683 := bstep (se 1 (by rfl) ⟨13520762, by rfl⟩ : syracuseStep 18027683 = 27041525) B27041525
theorem B12018455 : Blo 2109435 12018455 := bstep (se 1 (by rfl) ⟨9013841, by rfl⟩ : syracuseStep 12018455 = 18027683) B18027683
theorem B8012303 : Blo 2109435 8012303 := bstep (se 1 (by rfl) ⟨6009227, by rfl⟩ : syracuseStep 8012303 = 12018455) B12018455
theorem B5341535 : Blo 2109435 5341535 := bstep (se 1 (by rfl) ⟨4006151, by rfl⟩ : syracuseStep 5341535 = 8012303) B8012303
theorem B3561023 : Blo 2109435 3561023 := bstep (se 1 (by rfl) ⟨2670767, by rfl⟩ : syracuseStep 3561023 = 5341535) B5341535
theorem B2374015 : Blo 2109435 2374015 := bstep (se 1 (by rfl) ⟨1780511, by rfl⟩ : syracuseStep 2374015 = 3561023) B3561023
theorem B3165353 : Blo 2109435 3165353 := bstep (se 2 (by rfl) ⟨1187007, by rfl⟩ : syracuseStep 3165353 = 2374015) B2374015
theorem B2110235 : Blo 2109435 2110235 := bstep (se 1 (by rfl) ⟨1582676, by rfl⟩ : syracuseStep 2110235 = 3165353) B3165353
theorem B3380197 : Blo 2109435 3380197 := bbase (se 4 (by rfl) ⟨316893, by rfl⟩ : syracuseStep 3380197 = 633787) (by norm_num)
theorem B4506929 : Blo 2109435 4506929 := bstep (se 2 (by rfl) ⟨1690098, by rfl⟩ : syracuseStep 4506929 = 3380197) B3380197
theorem B3004619 : Blo 2109435 3004619 := bstep (se 1 (by rfl) ⟨2253464, by rfl⟩ : syracuseStep 3004619 = 4506929) B4506929
theorem B8012317 : Blo 2109435 8012317 := bstep (se 3 (by rfl) ⟨1502309, by rfl⟩ : syracuseStep 8012317 = 3004619) B3004619
theorem B10683089 : Blo 2109435 10683089 := bstep (se 2 (by rfl) ⟨4006158, by rfl⟩ : syracuseStep 10683089 = 8012317) B8012317
theorem B7122059 : Blo 2109435 7122059 := bstep (se 1 (by rfl) ⟨5341544, by rfl⟩ : syracuseStep 7122059 = 10683089) B10683089
theorem B4748039 : Blo 2109435 4748039 := bstep (se 1 (by rfl) ⟨3561029, by rfl⟩ : syracuseStep 4748039 = 7122059) B7122059
theorem B3165359 : Blo 2109435 3165359 := bstep (se 1 (by rfl) ⟨2374019, by rfl⟩ : syracuseStep 3165359 = 4748039) B4748039
theorem B2110239 : Blo 2109435 2110239 := bstep (se 1 (by rfl) ⟨1582679, by rfl⟩ : syracuseStep 2110239 = 3165359) B3165359
theorem B3165365 : Blo 2109435 3165365 := bbase (se 5 (by rfl) ⟨148376, by rfl⟩ : syracuseStep 3165365 = 296753) (by norm_num)
theorem B2110243 : Blo 2109435 2110243 := bstep (se 1 (by rfl) ⟨1582682, by rfl⟩ : syracuseStep 2110243 = 3165365) B3165365
theorem B5341565 : Blo 2109435 5341565 := bbase (se 3 (by rfl) ⟨1001543, by rfl⟩ : syracuseStep 5341565 = 2003087) (by norm_num)
theorem B3561043 : Blo 2109435 3561043 := bstep (se 1 (by rfl) ⟨2670782, by rfl⟩ : syracuseStep 3561043 = 5341565) B5341565
theorem B4748057 : Blo 2109435 4748057 := bstep (se 2 (by rfl) ⟨1780521, by rfl⟩ : syracuseStep 4748057 = 3561043) B3561043
theorem B3165371 : Blo 2109435 3165371 := bstep (se 1 (by rfl) ⟨2374028, by rfl⟩ : syracuseStep 3165371 = 4748057) B4748057
theorem B2110247 : Blo 2109435 2110247 := bstep (se 1 (by rfl) ⟨1582685, by rfl⟩ : syracuseStep 2110247 = 3165371) B3165371
theorem B2374033 : Blo 2109435 2374033 := bbase (se 2 (by rfl) ⟨890262, by rfl⟩ : syracuseStep 2374033 = 1780525) (by norm_num)
theorem B3165377 : Blo 2109435 3165377 := bstep (se 2 (by rfl) ⟨1187016, by rfl⟩ : syracuseStep 3165377 = 2374033) B2374033
theorem B2110251 : Blo 2109435 2110251 := bstep (se 1 (by rfl) ⟨1582688, by rfl⟩ : syracuseStep 2110251 = 3165377) B3165377
theorem B4006189 : Blo 2109435 4006189 := bbase (se 3 (by rfl) ⟨751160, by rfl⟩ : syracuseStep 4006189 = 1502321) (by norm_num)
theorem B5341585 : Blo 2109435 5341585 := bstep (se 2 (by rfl) ⟨2003094, by rfl⟩ : syracuseStep 5341585 = 4006189) B4006189
theorem B7122113 : Blo 2109435 7122113 := bstep (se 2 (by rfl) ⟨2670792, by rfl⟩ : syracuseStep 7122113 = 5341585) B5341585
theorem B4748075 : Blo 2109435 4748075 := bstep (se 1 (by rfl) ⟨3561056, by rfl⟩ : syracuseStep 4748075 = 7122113) B7122113
theorem B3165383 : Blo 2109435 3165383 := bstep (se 1 (by rfl) ⟨2374037, by rfl⟩ : syracuseStep 3165383 = 4748075) B4748075
theorem B2110255 : Blo 2109435 2110255 := bstep (se 1 (by rfl) ⟨1582691, by rfl⟩ : syracuseStep 2110255 = 3165383) B3165383
theorem B3165389 : Blo 2109435 3165389 := bbase (se 3 (by rfl) ⟨593510, by rfl⟩ : syracuseStep 3165389 = 1187021) (by norm_num)
theorem B2110259 : Blo 2109435 2110259 := bstep (se 1 (by rfl) ⟨1582694, by rfl⟩ : syracuseStep 2110259 = 3165389) B3165389
theorem B4748093 : Blo 2109435 4748093 := bbase (se 3 (by rfl) ⟨890267, by rfl⟩ : syracuseStep 4748093 = 1780535) (by norm_num)
theorem B3165395 : Blo 2109435 3165395 := bstep (se 1 (by rfl) ⟨2374046, by rfl⟩ : syracuseStep 3165395 = 4748093) B4748093
theorem B2110263 : Blo 2109435 2110263 := bstep (se 1 (by rfl) ⟨1582697, by rfl⟩ : syracuseStep 2110263 = 3165395) B3165395
theorem B3561077 : Blo 2109435 3561077 := bbase (se 5 (by rfl) ⟨166925, by rfl⟩ : syracuseStep 3561077 = 333851) (by norm_num)
theorem B2374051 : Blo 2109435 2374051 := bstep (se 1 (by rfl) ⟨1780538, by rfl⟩ : syracuseStep 2374051 = 3561077) B3561077
theorem B3165401 : Blo 2109435 3165401 := bstep (se 2 (by rfl) ⟨1187025, by rfl⟩ : syracuseStep 3165401 = 2374051) B2374051
theorem B2110267 : Blo 2109435 2110267 := bstep (se 1 (by rfl) ⟨1582700, by rfl⟩ : syracuseStep 2110267 = 3165401) B3165401
theorem B4506997 : Blo 2109435 4506997 := bbase (se 5 (by rfl) ⟨211265, by rfl⟩ : syracuseStep 4506997 = 422531) (by norm_num)
theorem B6009329 : Blo 2109435 6009329 := bstep (se 2 (by rfl) ⟨2253498, by rfl⟩ : syracuseStep 6009329 = 4506997) B4506997
theorem B16024877 : Blo 2109435 16024877 := bstep (se 3 (by rfl) ⟨3004664, by rfl⟩ : syracuseStep 16024877 = 6009329) B6009329
theorem B10683251 : Blo 2109435 10683251 := bstep (se 1 (by rfl) ⟨8012438, by rfl⟩ : syracuseStep 10683251 = 16024877) B16024877
theorem B7122167 : Blo 2109435 7122167 := bstep (se 1 (by rfl) ⟨5341625, by rfl⟩ : syracuseStep 7122167 = 10683251) B10683251
theorem B4748111 : Blo 2109435 4748111 := bstep (se 1 (by rfl) ⟨3561083, by rfl⟩ : syracuseStep 4748111 = 7122167) B7122167
theorem B3165407 : Blo 2109435 3165407 := bstep (se 1 (by rfl) ⟨2374055, by rfl⟩ : syracuseStep 3165407 = 4748111) B4748111
theorem B2110271 : Blo 2109435 2110271 := bstep (se 1 (by rfl) ⟨1582703, by rfl⟩ : syracuseStep 2110271 = 3165407) B3165407
theorem B3165413 : Blo 2109435 3165413 := bbase (se 4 (by rfl) ⟨296757, by rfl⟩ : syracuseStep 3165413 = 593515) (by norm_num)
theorem B2110275 : Blo 2109435 2110275 := bstep (se 1 (by rfl) ⟨1582706, by rfl⟩ : syracuseStep 2110275 = 3165413) B3165413
theorem B7605589 : Blo 2109435 7605589 := bbase (se 11 (by rfl) ⟨5570, by rfl⟩ : syracuseStep 7605589 = 11141) (by norm_num)
theorem B10140785 : Blo 2109435 10140785 := bstep (se 2 (by rfl) ⟨3802794, by rfl⟩ : syracuseStep 10140785 = 7605589) B7605589
theorem B6760523 : Blo 2109435 6760523 := bstep (se 1 (by rfl) ⟨5070392, by rfl⟩ : syracuseStep 6760523 = 10140785) B10140785
theorem B4507015 : Blo 2109435 4507015 := bstep (se 1 (by rfl) ⟨3380261, by rfl⟩ : syracuseStep 4507015 = 6760523) B6760523
theorem B6009353 : Blo 2109435 6009353 := bstep (se 2 (by rfl) ⟨2253507, by rfl⟩ : syracuseStep 6009353 = 4507015) B4507015
theorem B4006235 : Blo 2109435 4006235 := bstep (se 1 (by rfl) ⟨3004676, by rfl⟩ : syracuseStep 4006235 = 6009353) B6009353
theorem B2670823 : Blo 2109435 2670823 := bstep (se 1 (by rfl) ⟨2003117, by rfl⟩ : syracuseStep 2670823 = 4006235) B4006235
theorem B3561097 : Blo 2109435 3561097 := bstep (se 2 (by rfl) ⟨1335411, by rfl⟩ : syracuseStep 3561097 = 2670823) B2670823
theorem B4748129 : Blo 2109435 4748129 := bstep (se 2 (by rfl) ⟨1780548, by rfl⟩ : syracuseStep 4748129 = 3561097) B3561097
theorem B3165419 : Blo 2109435 3165419 := bstep (se 1 (by rfl) ⟨2374064, by rfl⟩ : syracuseStep 3165419 = 4748129) B4748129
theorem B2110279 : Blo 2109435 2110279 := bstep (se 1 (by rfl) ⟨1582709, by rfl⟩ : syracuseStep 2110279 = 3165419) B3165419
theorem B2374069 : Blo 2109435 2374069 := bbase (se 5 (by rfl) ⟨111284, by rfl⟩ : syracuseStep 2374069 = 222569) (by norm_num)
theorem B3165425 : Blo 2109435 3165425 := bstep (se 2 (by rfl) ⟨1187034, by rfl⟩ : syracuseStep 3165425 = 2374069) B2374069
theorem B2110283 : Blo 2109435 2110283 := bstep (se 1 (by rfl) ⟨1582712, by rfl⟩ : syracuseStep 2110283 = 3165425) B3165425
theorem B2670833 : Blo 2109435 2670833 := bbase (se 2 (by rfl) ⟨1001562, by rfl⟩ : syracuseStep 2670833 = 2003125) (by norm_num)
theorem B7122221 : Blo 2109435 7122221 := bstep (se 3 (by rfl) ⟨1335416, by rfl⟩ : syracuseStep 7122221 = 2670833) B2670833
theorem B4748147 : Blo 2109435 4748147 := bstep (se 1 (by rfl) ⟨3561110, by rfl⟩ : syracuseStep 4748147 = 7122221) B7122221
theorem B3165431 : Blo 2109435 3165431 := bstep (se 1 (by rfl) ⟨2374073, by rfl⟩ : syracuseStep 3165431 = 4748147) B4748147
theorem B2110287 : Blo 2109435 2110287 := bstep (se 1 (by rfl) ⟨1582715, by rfl⟩ : syracuseStep 2110287 = 3165431) B3165431
theorem B3165437 : Blo 2109435 3165437 := bbase (se 3 (by rfl) ⟨593519, by rfl⟩ : syracuseStep 3165437 = 1187039) (by norm_num)
theorem B2110291 : Blo 2109435 2110291 := bstep (se 1 (by rfl) ⟨1582718, by rfl⟩ : syracuseStep 2110291 = 3165437) B3165437
theorem B4748165 : Blo 2109435 4748165 := bbase (se 4 (by rfl) ⟨445140, by rfl⟩ : syracuseStep 4748165 = 890281) (by norm_num)
theorem B3165443 : Blo 2109435 3165443 := bstep (se 1 (by rfl) ⟨2374082, by rfl⟩ : syracuseStep 3165443 = 4748165) B4748165
theorem B2110295 : Blo 2109435 2110295 := bstep (se 1 (by rfl) ⟨1582721, by rfl⟩ : syracuseStep 2110295 = 3165443) B3165443
theorem B2253529 : Blo 2109435 2253529 := bbase (se 2 (by rfl) ⟨845073, by rfl⟩ : syracuseStep 2253529 = 1690147) (by norm_num)
theorem B3004705 : Blo 2109435 3004705 := bstep (se 2 (by rfl) ⟨1126764, by rfl⟩ : syracuseStep 3004705 = 2253529) B2253529
theorem B4006273 : Blo 2109435 4006273 := bstep (se 2 (by rfl) ⟨1502352, by rfl⟩ : syracuseStep 4006273 = 3004705) B3004705
theorem B5341697 : Blo 2109435 5341697 := bstep (se 2 (by rfl) ⟨2003136, by rfl⟩ : syracuseStep 5341697 = 4006273) B4006273
theorem B3561131 : Blo 2109435 3561131 := bstep (se 1 (by rfl) ⟨2670848, by rfl⟩ : syracuseStep 3561131 = 5341697) B5341697
theorem B2374087 : Blo 2109435 2374087 := bstep (se 1 (by rfl) ⟨1780565, by rfl⟩ : syracuseStep 2374087 = 3561131) B3561131
theorem B3165449 : Blo 2109435 3165449 := bstep (se 2 (by rfl) ⟨1187043, by rfl⟩ : syracuseStep 3165449 = 2374087) B2374087
theorem B2110299 : Blo 2109435 2110299 := bstep (se 1 (by rfl) ⟨1582724, by rfl⟩ : syracuseStep 2110299 = 3165449) B3165449
theorem B10683413 : Blo 2109435 10683413 := bbase (se 6 (by rfl) ⟨250392, by rfl⟩ : syracuseStep 10683413 = 500785) (by norm_num)
theorem B7122275 : Blo 2109435 7122275 := bstep (se 1 (by rfl) ⟨5341706, by rfl⟩ : syracuseStep 7122275 = 10683413) B10683413
theorem B4748183 : Blo 2109435 4748183 := bstep (se 1 (by rfl) ⟨3561137, by rfl⟩ : syracuseStep 4748183 = 7122275) B7122275
theorem B3165455 : Blo 2109435 3165455 := bstep (se 1 (by rfl) ⟨2374091, by rfl⟩ : syracuseStep 3165455 = 4748183) B4748183
theorem B2110303 : Blo 2109435 2110303 := bstep (se 1 (by rfl) ⟨1582727, by rfl⟩ : syracuseStep 2110303 = 3165455) B3165455
theorem B3165461 : Blo 2109435 3165461 := bbase (se 6 (by rfl) ⟨74190, by rfl⟩ : syracuseStep 3165461 = 148381) (by norm_num)
theorem B2110307 : Blo 2109435 2110307 := bstep (se 1 (by rfl) ⟨1582730, by rfl⟩ : syracuseStep 2110307 = 3165461) B3165461
theorem B5704277 : Blo 2109435 5704277 := bbase (se 8 (by rfl) ⟨33423, by rfl⟩ : syracuseStep 5704277 = 66847) (by norm_num)
theorem B15211405 : Blo 2109435 15211405 := bstep (se 3 (by rfl) ⟨2852138, by rfl⟩ : syracuseStep 15211405 = 5704277) B5704277
theorem B20281873 : Blo 2109435 20281873 := bstep (se 2 (by rfl) ⟨7605702, by rfl⟩ : syracuseStep 20281873 = 15211405) B15211405
theorem B27042497 : Blo 2109435 27042497 := bstep (se 2 (by rfl) ⟨10140936, by rfl⟩ : syracuseStep 27042497 = 20281873) B20281873
theorem B18028331 : Blo 2109435 18028331 := bstep (se 1 (by rfl) ⟨13521248, by rfl⟩ : syracuseStep 18028331 = 27042497) B27042497
theorem B12018887 : Blo 2109435 12018887 := bstep (se 1 (by rfl) ⟨9014165, by rfl⟩ : syracuseStep 12018887 = 18028331) B18028331
theorem B8012591 : Blo 2109435 8012591 := bstep (se 1 (by rfl) ⟨6009443, by rfl⟩ : syracuseStep 8012591 = 12018887) B12018887
theorem B5341727 : Blo 2109435 5341727 := bstep (se 1 (by rfl) ⟨4006295, by rfl⟩ : syracuseStep 5341727 = 8012591) B8012591
theorem B3561151 : Blo 2109435 3561151 := bstep (se 1 (by rfl) ⟨2670863, by rfl⟩ : syracuseStep 3561151 = 5341727) B5341727
theorem B4748201 : Blo 2109435 4748201 := bstep (se 2 (by rfl) ⟨1780575, by rfl⟩ : syracuseStep 4748201 = 3561151) B3561151
theorem B3165467 : Blo 2109435 3165467 := bstep (se 1 (by rfl) ⟨2374100, by rfl⟩ : syracuseStep 3165467 = 4748201) B4748201
theorem B2110311 : Blo 2109435 2110311 := bstep (se 1 (by rfl) ⟨1582733, by rfl⟩ : syracuseStep 2110311 = 3165467) B3165467
theorem B2374105 : Blo 2109435 2374105 := bbase (se 2 (by rfl) ⟨890289, by rfl⟩ : syracuseStep 2374105 = 1780579) (by norm_num)
theorem B3165473 : Blo 2109435 3165473 := bstep (se 2 (by rfl) ⟨1187052, by rfl⟩ : syracuseStep 3165473 = 2374105) B2374105
theorem B2110315 : Blo 2109435 2110315 := bstep (se 1 (by rfl) ⟨1582736, by rfl⟩ : syracuseStep 2110315 = 3165473) B3165473
theorem B3004733 : Blo 2109435 3004733 := bbase (se 3 (by rfl) ⟨563387, by rfl⟩ : syracuseStep 3004733 = 1126775) (by norm_num)
theorem B8012621 : Blo 2109435 8012621 := bstep (se 3 (by rfl) ⟨1502366, by rfl⟩ : syracuseStep 8012621 = 3004733) B3004733
theorem B5341747 : Blo 2109435 5341747 := bstep (se 1 (by rfl) ⟨4006310, by rfl⟩ : syracuseStep 5341747 = 8012621) B8012621
theorem B7122329 : Blo 2109435 7122329 := bstep (se 2 (by rfl) ⟨2670873, by rfl⟩ : syracuseStep 7122329 = 5341747) B5341747
theorem B4748219 : Blo 2109435 4748219 := bstep (se 1 (by rfl) ⟨3561164, by rfl⟩ : syracuseStep 4748219 = 7122329) B7122329
theorem B3165479 : Blo 2109435 3165479 := bstep (se 1 (by rfl) ⟨2374109, by rfl⟩ : syracuseStep 3165479 = 4748219) B4748219
theorem B2110319 : Blo 2109435 2110319 := bstep (se 1 (by rfl) ⟨1582739, by rfl⟩ : syracuseStep 2110319 = 3165479) B3165479
theorem B3165485 : Blo 2109435 3165485 := bbase (se 3 (by rfl) ⟨593528, by rfl⟩ : syracuseStep 3165485 = 1187057) (by norm_num)
theorem B2110323 : Blo 2109435 2110323 := bstep (se 1 (by rfl) ⟨1582742, by rfl⟩ : syracuseStep 2110323 = 3165485) B3165485
theorem B4748237 : Blo 2109435 4748237 := bbase (se 3 (by rfl) ⟨890294, by rfl⟩ : syracuseStep 4748237 = 1780589) (by norm_num)
theorem B3165491 : Blo 2109435 3165491 := bstep (se 1 (by rfl) ⟨2374118, by rfl⟩ : syracuseStep 3165491 = 4748237) B4748237
theorem B2110327 : Blo 2109435 2110327 := bstep (se 1 (by rfl) ⟨1582745, by rfl⟩ : syracuseStep 2110327 = 3165491) B3165491
theorem B2670889 : Blo 2109435 2670889 := bbase (se 2 (by rfl) ⟨1001583, by rfl⟩ : syracuseStep 2670889 = 2003167) (by norm_num)
theorem B3561185 : Blo 2109435 3561185 := bstep (se 2 (by rfl) ⟨1335444, by rfl⟩ : syracuseStep 3561185 = 2670889) B2670889
theorem B2374123 : Blo 2109435 2374123 := bstep (se 1 (by rfl) ⟨1780592, by rfl⟩ : syracuseStep 2374123 = 3561185) B3561185
theorem B3165497 : Blo 2109435 3165497 := bstep (se 2 (by rfl) ⟨1187061, by rfl⟩ : syracuseStep 3165497 = 2374123) B2374123
theorem B2110331 : Blo 2109435 2110331 := bstep (se 1 (by rfl) ⟨1582748, by rfl⟩ : syracuseStep 2110331 = 3165497) B3165497
theorem B5414669 : Blo 2109435 5414669 := bbase (se 3 (by rfl) ⟨1015250, by rfl⟩ : syracuseStep 5414669 = 2030501) (by norm_num)
theorem B3609779 : Blo 2109435 3609779 := bstep (se 1 (by rfl) ⟨2707334, by rfl⟩ : syracuseStep 3609779 = 5414669) B5414669
theorem B9626077 : Blo 2109435 9626077 := bstep (se 3 (by rfl) ⟨1804889, by rfl⟩ : syracuseStep 9626077 = 3609779) B3609779
theorem B12834769 : Blo 2109435 12834769 := bstep (se 2 (by rfl) ⟨4813038, by rfl⟩ : syracuseStep 12834769 = 9626077) B9626077
theorem B17113025 : Blo 2109435 17113025 := bstep (se 2 (by rfl) ⟨6417384, by rfl⟩ : syracuseStep 17113025 = 12834769) B12834769
theorem B11408683 : Blo 2109435 11408683 := bstep (se 1 (by rfl) ⟨8556512, by rfl⟩ : syracuseStep 11408683 = 17113025) B17113025
theorem B15211577 : Blo 2109435 15211577 := bstep (se 2 (by rfl) ⟨5704341, by rfl⟩ : syracuseStep 15211577 = 11408683) B11408683
theorem B10141051 : Blo 2109435 10141051 := bstep (se 1 (by rfl) ⟨7605788, by rfl⟩ : syracuseStep 10141051 = 15211577) B15211577
theorem B13521401 : Blo 2109435 13521401 := bstep (se 2 (by rfl) ⟨5070525, by rfl⟩ : syracuseStep 13521401 = 10141051) B10141051
theorem B9014267 : Blo 2109435 9014267 := bstep (se 1 (by rfl) ⟨6760700, by rfl⟩ : syracuseStep 9014267 = 13521401) B13521401
theorem B24038045 : Blo 2109435 24038045 := bstep (se 3 (by rfl) ⟨4507133, by rfl⟩ : syracuseStep 24038045 = 9014267) B9014267
theorem B16025363 : Blo 2109435 16025363 := bstep (se 1 (by rfl) ⟨12019022, by rfl⟩ : syracuseStep 16025363 = 24038045) B24038045
theorem B10683575 : Blo 2109435 10683575 := bstep (se 1 (by rfl) ⟨8012681, by rfl⟩ : syracuseStep 10683575 = 16025363) B16025363
theorem B7122383 : Blo 2109435 7122383 := bstep (se 1 (by rfl) ⟨5341787, by rfl⟩ : syracuseStep 7122383 = 10683575) B10683575
theorem B4748255 : Blo 2109435 4748255 := bstep (se 1 (by rfl) ⟨3561191, by rfl⟩ : syracuseStep 4748255 = 7122383) B7122383
theorem B3165503 : Blo 2109435 3165503 := bstep (se 1 (by rfl) ⟨2374127, by rfl⟩ : syracuseStep 3165503 = 4748255) B4748255
theorem B2110335 : Blo 2109435 2110335 := bstep (se 1 (by rfl) ⟨1582751, by rfl⟩ : syracuseStep 2110335 = 3165503) B3165503
theorem B3165509 : Blo 2109435 3165509 := bbase (se 4 (by rfl) ⟨296766, by rfl⟩ : syracuseStep 3165509 = 593533) (by norm_num)
theorem B2110339 : Blo 2109435 2110339 := bstep (se 1 (by rfl) ⟨1582754, by rfl⟩ : syracuseStep 2110339 = 3165509) B3165509
theorem B3561205 : Blo 2109435 3561205 := bbase (se 5 (by rfl) ⟨166931, by rfl⟩ : syracuseStep 3561205 = 333863) (by norm_num)
theorem B4748273 : Blo 2109435 4748273 := bstep (se 2 (by rfl) ⟨1780602, by rfl⟩ : syracuseStep 4748273 = 3561205) B3561205
theorem B3165515 : Blo 2109435 3165515 := bstep (se 1 (by rfl) ⟨2374136, by rfl⟩ : syracuseStep 3165515 = 4748273) B4748273
theorem B2110343 : Blo 2109435 2110343 := bstep (se 1 (by rfl) ⟨1582757, by rfl⟩ : syracuseStep 2110343 = 3165515) B3165515
theorem B2374141 : Blo 2109435 2374141 := bbase (se 3 (by rfl) ⟨445151, by rfl⟩ : syracuseStep 2374141 = 890303) (by norm_num)
theorem B3165521 : Blo 2109435 3165521 := bstep (se 2 (by rfl) ⟨1187070, by rfl⟩ : syracuseStep 3165521 = 2374141) B2374141
theorem B2110347 : Blo 2109435 2110347 := bstep (se 1 (by rfl) ⟨1582760, by rfl⟩ : syracuseStep 2110347 = 3165521) B3165521
theorem B7122437 : Blo 2109435 7122437 := bbase (se 4 (by rfl) ⟨667728, by rfl⟩ : syracuseStep 7122437 = 1335457) (by norm_num)
theorem B4748291 : Blo 2109435 4748291 := bstep (se 1 (by rfl) ⟨3561218, by rfl⟩ : syracuseStep 4748291 = 7122437) B7122437
theorem B3165527 : Blo 2109435 3165527 := bstep (se 1 (by rfl) ⟨2374145, by rfl⟩ : syracuseStep 3165527 = 4748291) B4748291
theorem B2110351 : Blo 2109435 2110351 := bstep (se 1 (by rfl) ⟨1582763, by rfl⟩ : syracuseStep 2110351 = 3165527) B3165527
theorem B3165533 : Blo 2109435 3165533 := bbase (se 3 (by rfl) ⟨593537, by rfl⟩ : syracuseStep 3165533 = 1187075) (by norm_num)
theorem B2110355 : Blo 2109435 2110355 := bstep (se 1 (by rfl) ⟨1582766, by rfl⟩ : syracuseStep 2110355 = 3165533) B3165533
theorem B4748309 : Blo 2109435 4748309 := bbase (se 6 (by rfl) ⟨111288, by rfl⟩ : syracuseStep 4748309 = 222577) (by norm_num)
theorem B3165539 : Blo 2109435 3165539 := bstep (se 1 (by rfl) ⟨2374154, by rfl⟩ : syracuseStep 3165539 = 4748309) B4748309
theorem B2110359 : Blo 2109435 2110359 := bstep (se 1 (by rfl) ⟨1582769, by rfl⟩ : syracuseStep 2110359 = 3165539) B3165539
theorem B8012789 : Blo 2109435 8012789 := bbase (se 5 (by rfl) ⟨375599, by rfl⟩ : syracuseStep 8012789 = 751199) (by norm_num)
theorem B5341859 : Blo 2109435 5341859 := bstep (se 1 (by rfl) ⟨4006394, by rfl⟩ : syracuseStep 5341859 = 8012789) B8012789
theorem B3561239 : Blo 2109435 3561239 := bstep (se 1 (by rfl) ⟨2670929, by rfl⟩ : syracuseStep 3561239 = 5341859) B5341859
theorem B2374159 : Blo 2109435 2374159 := bstep (se 1 (by rfl) ⟨1780619, by rfl⟩ : syracuseStep 2374159 = 3561239) B3561239
theorem B3165545 : Blo 2109435 3165545 := bstep (se 2 (by rfl) ⟨1187079, by rfl⟩ : syracuseStep 3165545 = 2374159) B2374159
theorem B2110363 : Blo 2109435 2110363 := bstep (se 1 (by rfl) ⟨1582772, by rfl⟩ : syracuseStep 2110363 = 3165545) B3165545
theorem B2253601 : Blo 2109435 2253601 := bbase (se 2 (by rfl) ⟨845100, by rfl⟩ : syracuseStep 2253601 = 1690201) (by norm_num)
theorem B12019205 : Blo 2109435 12019205 := bstep (se 4 (by rfl) ⟨1126800, by rfl⟩ : syracuseStep 12019205 = 2253601) B2253601
theorem B8012803 : Blo 2109435 8012803 := bstep (se 1 (by rfl) ⟨6009602, by rfl⟩ : syracuseStep 8012803 = 12019205) B12019205
theorem B10683737 : Blo 2109435 10683737 := bstep (se 2 (by rfl) ⟨4006401, by rfl⟩ : syracuseStep 10683737 = 8012803) B8012803
theorem B7122491 : Blo 2109435 7122491 := bstep (se 1 (by rfl) ⟨5341868, by rfl⟩ : syracuseStep 7122491 = 10683737) B10683737
theorem B4748327 : Blo 2109435 4748327 := bstep (se 1 (by rfl) ⟨3561245, by rfl⟩ : syracuseStep 4748327 = 7122491) B7122491
theorem B3165551 : Blo 2109435 3165551 := bstep (se 1 (by rfl) ⟨2374163, by rfl⟩ : syracuseStep 3165551 = 4748327) B4748327
theorem B2110367 : Blo 2109435 2110367 := bstep (se 1 (by rfl) ⟨1582775, by rfl⟩ : syracuseStep 2110367 = 3165551) B3165551
theorem B3165557 : Blo 2109435 3165557 := bbase (se 5 (by rfl) ⟨148385, by rfl⟩ : syracuseStep 3165557 = 296771) (by norm_num)
theorem B2110371 : Blo 2109435 2110371 := bstep (se 1 (by rfl) ⟨1582778, by rfl⟩ : syracuseStep 2110371 = 3165557) B3165557
theorem B3004813 : Blo 2109435 3004813 := bbase (se 3 (by rfl) ⟨563402, by rfl⟩ : syracuseStep 3004813 = 1126805) (by norm_num)
theorem B4006417 : Blo 2109435 4006417 := bstep (se 2 (by rfl) ⟨1502406, by rfl⟩ : syracuseStep 4006417 = 3004813) B3004813
theorem B5341889 : Blo 2109435 5341889 := bstep (se 2 (by rfl) ⟨2003208, by rfl⟩ : syracuseStep 5341889 = 4006417) B4006417
theorem B3561259 : Blo 2109435 3561259 := bstep (se 1 (by rfl) ⟨2670944, by rfl⟩ : syracuseStep 3561259 = 5341889) B5341889
theorem B4748345 : Blo 2109435 4748345 := bstep (se 2 (by rfl) ⟨1780629, by rfl⟩ : syracuseStep 4748345 = 3561259) B3561259
theorem B3165563 : Blo 2109435 3165563 := bstep (se 1 (by rfl) ⟨2374172, by rfl⟩ : syracuseStep 3165563 = 4748345) B4748345
theorem B2110375 : Blo 2109435 2110375 := bstep (se 1 (by rfl) ⟨1582781, by rfl⟩ : syracuseStep 2110375 = 3165563) B3165563
theorem B2374177 : Blo 2109435 2374177 := bbase (se 2 (by rfl) ⟨890316, by rfl⟩ : syracuseStep 2374177 = 1780633) (by norm_num)
theorem B3165569 : Blo 2109435 3165569 := bstep (se 2 (by rfl) ⟨1187088, by rfl⟩ : syracuseStep 3165569 = 2374177) B2374177
theorem B2110379 : Blo 2109435 2110379 := bstep (se 1 (by rfl) ⟨1582784, by rfl⟩ : syracuseStep 2110379 = 3165569) B3165569
theorem B5341909 : Blo 2109435 5341909 := bbase (se 7 (by rfl) ⟨62600, by rfl⟩ : syracuseStep 5341909 = 125201) (by norm_num)
theorem B7122545 : Blo 2109435 7122545 := bstep (se 2 (by rfl) ⟨2670954, by rfl⟩ : syracuseStep 7122545 = 5341909) B5341909
theorem B4748363 : Blo 2109435 4748363 := bstep (se 1 (by rfl) ⟨3561272, by rfl⟩ : syracuseStep 4748363 = 7122545) B7122545
theorem B3165575 : Blo 2109435 3165575 := bstep (se 1 (by rfl) ⟨2374181, by rfl⟩ : syracuseStep 3165575 = 4748363) B4748363
theorem B2110383 : Blo 2109435 2110383 := bstep (se 1 (by rfl) ⟨1582787, by rfl⟩ : syracuseStep 2110383 = 3165575) B3165575
theorem B3165581 : Blo 2109435 3165581 := bbase (se 3 (by rfl) ⟨593546, by rfl⟩ : syracuseStep 3165581 = 1187093) (by norm_num)
theorem B2110387 : Blo 2109435 2110387 := bstep (se 1 (by rfl) ⟨1582790, by rfl⟩ : syracuseStep 2110387 = 3165581) B3165581
theorem B4748381 : Blo 2109435 4748381 := bbase (se 3 (by rfl) ⟨890321, by rfl⟩ : syracuseStep 4748381 = 1780643) (by norm_num)
theorem B3165587 : Blo 2109435 3165587 := bstep (se 1 (by rfl) ⟨2374190, by rfl⟩ : syracuseStep 3165587 = 4748381) B4748381
theorem B2110391 : Blo 2109435 2110391 := bstep (se 1 (by rfl) ⟨1582793, by rfl⟩ : syracuseStep 2110391 = 3165587) B3165587
theorem B3561293 : Blo 2109435 3561293 := bbase (se 3 (by rfl) ⟨667742, by rfl⟩ : syracuseStep 3561293 = 1335485) (by norm_num)
theorem B2374195 : Blo 2109435 2374195 := bstep (se 1 (by rfl) ⟨1780646, by rfl⟩ : syracuseStep 2374195 = 3561293) B3561293
theorem B3165593 : Blo 2109435 3165593 := bstep (se 2 (by rfl) ⟨1187097, by rfl⟩ : syracuseStep 3165593 = 2374195) B2374195
theorem B2110395 : Blo 2109435 2110395 := bstep (se 1 (by rfl) ⟨1582796, by rfl⟩ : syracuseStep 2110395 = 3165593) B3165593
theorem B2139193 : Blo 2109435 2139193 := bbase (se 2 (by rfl) ⟨802197, by rfl⟩ : syracuseStep 2139193 = 1604395) (by norm_num)
theorem B11409029 : Blo 2109435 11409029 := bstep (se 4 (by rfl) ⟨1069596, by rfl⟩ : syracuseStep 11409029 = 2139193) B2139193
theorem B7606019 : Blo 2109435 7606019 := bstep (se 1 (by rfl) ⟨5704514, by rfl⟩ : syracuseStep 7606019 = 11409029) B11409029
theorem B20282717 : Blo 2109435 20282717 := bstep (se 3 (by rfl) ⟨3803009, by rfl⟩ : syracuseStep 20282717 = 7606019) B7606019
theorem B13521811 : Blo 2109435 13521811 := bstep (se 1 (by rfl) ⟨10141358, by rfl⟩ : syracuseStep 13521811 = 20282717) B20282717
theorem B18029081 : Blo 2109435 18029081 := bstep (se 2 (by rfl) ⟨6760905, by rfl⟩ : syracuseStep 18029081 = 13521811) B13521811
theorem B12019387 : Blo 2109435 12019387 := bstep (se 1 (by rfl) ⟨9014540, by rfl⟩ : syracuseStep 12019387 = 18029081) B18029081
theorem B16025849 : Blo 2109435 16025849 := bstep (se 2 (by rfl) ⟨6009693, by rfl⟩ : syracuseStep 16025849 = 12019387) B12019387
theorem B10683899 : Blo 2109435 10683899 := bstep (se 1 (by rfl) ⟨8012924, by rfl⟩ : syracuseStep 10683899 = 16025849) B16025849
theorem B7122599 : Blo 2109435 7122599 := bstep (se 1 (by rfl) ⟨5341949, by rfl⟩ : syracuseStep 7122599 = 10683899) B10683899
theorem B4748399 : Blo 2109435 4748399 := bstep (se 1 (by rfl) ⟨3561299, by rfl⟩ : syracuseStep 4748399 = 7122599) B7122599
theorem B3165599 : Blo 2109435 3165599 := bstep (se 1 (by rfl) ⟨2374199, by rfl⟩ : syracuseStep 3165599 = 4748399) B4748399
theorem B2110399 : Blo 2109435 2110399 := bstep (se 1 (by rfl) ⟨1582799, by rfl⟩ : syracuseStep 2110399 = 3165599) B3165599
theorem B3165605 : Blo 2109435 3165605 := bbase (se 4 (by rfl) ⟨296775, by rfl⟩ : syracuseStep 3165605 = 593551) (by norm_num)
theorem B2110403 : Blo 2109435 2110403 := bstep (se 1 (by rfl) ⟨1582802, by rfl⟩ : syracuseStep 2110403 = 3165605) B3165605
theorem B2670985 : Blo 2109435 2670985 := bbase (se 2 (by rfl) ⟨1001619, by rfl⟩ : syracuseStep 2670985 = 2003239) (by norm_num)
theorem B3561313 : Blo 2109435 3561313 := bstep (se 2 (by rfl) ⟨1335492, by rfl⟩ : syracuseStep 3561313 = 2670985) B2670985
theorem B4748417 : Blo 2109435 4748417 := bstep (se 2 (by rfl) ⟨1780656, by rfl⟩ : syracuseStep 4748417 = 3561313) B3561313
theorem B3165611 : Blo 2109435 3165611 := bstep (se 1 (by rfl) ⟨2374208, by rfl⟩ : syracuseStep 3165611 = 4748417) B4748417
theorem B2110407 : Blo 2109435 2110407 := bstep (se 1 (by rfl) ⟨1582805, by rfl⟩ : syracuseStep 2110407 = 3165611) B3165611
theorem B2374213 : Blo 2109435 2374213 := bbase (se 4 (by rfl) ⟨222582, by rfl⟩ : syracuseStep 2374213 = 445165) (by norm_num)
theorem B3165617 : Blo 2109435 3165617 := bstep (se 2 (by rfl) ⟨1187106, by rfl⟩ : syracuseStep 3165617 = 2374213) B2374213
theorem B2110411 : Blo 2109435 2110411 := bstep (se 1 (by rfl) ⟨1582808, by rfl⟩ : syracuseStep 2110411 = 3165617) B3165617
theorem B4006493 : Blo 2109435 4006493 := bbase (se 3 (by rfl) ⟨751217, by rfl⟩ : syracuseStep 4006493 = 1502435) (by norm_num)
theorem B2670995 : Blo 2109435 2670995 := bstep (se 1 (by rfl) ⟨2003246, by rfl⟩ : syracuseStep 2670995 = 4006493) B4006493
theorem B7122653 : Blo 2109435 7122653 := bstep (se 3 (by rfl) ⟨1335497, by rfl⟩ : syracuseStep 7122653 = 2670995) B2670995
theorem B4748435 : Blo 2109435 4748435 := bstep (se 1 (by rfl) ⟨3561326, by rfl⟩ : syracuseStep 4748435 = 7122653) B7122653
theorem B3165623 : Blo 2109435 3165623 := bstep (se 1 (by rfl) ⟨2374217, by rfl⟩ : syracuseStep 3165623 = 4748435) B4748435
theorem B2110415 : Blo 2109435 2110415 := bstep (se 1 (by rfl) ⟨1582811, by rfl⟩ : syracuseStep 2110415 = 3165623) B3165623
theorem B3165629 : Blo 2109435 3165629 := bbase (se 3 (by rfl) ⟨593555, by rfl⟩ : syracuseStep 3165629 = 1187111) (by norm_num)
theorem B2110419 : Blo 2109435 2110419 := bstep (se 1 (by rfl) ⟨1582814, by rfl⟩ : syracuseStep 2110419 = 3165629) B3165629
theorem B4748453 : Blo 2109435 4748453 := bbase (se 4 (by rfl) ⟨445167, by rfl⟩ : syracuseStep 4748453 = 890335) (by norm_num)
theorem B3165635 : Blo 2109435 3165635 := bstep (se 1 (by rfl) ⟨2374226, by rfl⟩ : syracuseStep 3165635 = 4748453) B4748453
theorem B2110423 : Blo 2109435 2110423 := bstep (se 1 (by rfl) ⟨1582817, by rfl⟩ : syracuseStep 2110423 = 3165635) B3165635
theorem B5342021 : Blo 2109435 5342021 := bbase (se 4 (by rfl) ⟨500814, by rfl⟩ : syracuseStep 5342021 = 1001629) (by norm_num)
theorem B3561347 : Blo 2109435 3561347 := bstep (se 1 (by rfl) ⟨2671010, by rfl⟩ : syracuseStep 3561347 = 5342021) B5342021
theorem B2374231 : Blo 2109435 2374231 := bstep (se 1 (by rfl) ⟨1780673, by rfl⟩ : syracuseStep 2374231 = 3561347) B3561347
theorem B3165641 : Blo 2109435 3165641 := bstep (se 2 (by rfl) ⟨1187115, by rfl⟩ : syracuseStep 3165641 = 2374231) B2374231
theorem B2110427 : Blo 2109435 2110427 := bstep (se 1 (by rfl) ⟨1582820, by rfl⟩ : syracuseStep 2110427 = 3165641) B3165641
theorem B5070757 : Blo 2109435 5070757 := bbase (se 4 (by rfl) ⟨475383, by rfl⟩ : syracuseStep 5070757 = 950767) (by norm_num)
theorem B6761009 : Blo 2109435 6761009 := bstep (se 2 (by rfl) ⟨2535378, by rfl⟩ : syracuseStep 6761009 = 5070757) B5070757
theorem B4507339 : Blo 2109435 4507339 := bstep (se 1 (by rfl) ⟨3380504, by rfl⟩ : syracuseStep 4507339 = 6761009) B6761009
theorem B6009785 : Blo 2109435 6009785 := bstep (se 2 (by rfl) ⟨2253669, by rfl⟩ : syracuseStep 6009785 = 4507339) B4507339
theorem B4006523 : Blo 2109435 4006523 := bstep (se 1 (by rfl) ⟨3004892, by rfl⟩ : syracuseStep 4006523 = 6009785) B6009785
theorem B10684061 : Blo 2109435 10684061 := bstep (se 3 (by rfl) ⟨2003261, by rfl⟩ : syracuseStep 10684061 = 4006523) B4006523
theorem B7122707 : Blo 2109435 7122707 := bstep (se 1 (by rfl) ⟨5342030, by rfl⟩ : syracuseStep 7122707 = 10684061) B10684061
theorem B4748471 : Blo 2109435 4748471 := bstep (se 1 (by rfl) ⟨3561353, by rfl⟩ : syracuseStep 4748471 = 7122707) B7122707
theorem B3165647 : Blo 2109435 3165647 := bstep (se 1 (by rfl) ⟨2374235, by rfl⟩ : syracuseStep 3165647 = 4748471) B4748471
theorem B2110431 : Blo 2109435 2110431 := bstep (se 1 (by rfl) ⟨1582823, by rfl⟩ : syracuseStep 2110431 = 3165647) B3165647
theorem B3165653 : Blo 2109435 3165653 := bbase (se 7 (by rfl) ⟨37097, by rfl⟩ : syracuseStep 3165653 = 74195) (by norm_num)
theorem B2110435 : Blo 2109435 2110435 := bstep (se 1 (by rfl) ⟨1582826, by rfl⟩ : syracuseStep 2110435 = 3165653) B3165653
theorem B8013077 : Blo 2109435 8013077 := bbase (se 6 (by rfl) ⟨187806, by rfl⟩ : syracuseStep 8013077 = 375613) (by norm_num)
theorem B5342051 : Blo 2109435 5342051 := bstep (se 1 (by rfl) ⟨4006538, by rfl⟩ : syracuseStep 5342051 = 8013077) B8013077
theorem B3561367 : Blo 2109435 3561367 := bstep (se 1 (by rfl) ⟨2671025, by rfl⟩ : syracuseStep 3561367 = 5342051) B5342051
theorem B4748489 : Blo 2109435 4748489 := bstep (se 2 (by rfl) ⟨1780683, by rfl⟩ : syracuseStep 4748489 = 3561367) B3561367
theorem B3165659 : Blo 2109435 3165659 := bstep (se 1 (by rfl) ⟨2374244, by rfl⟩ : syracuseStep 3165659 = 4748489) B4748489
theorem B2110439 : Blo 2109435 2110439 := bstep (se 1 (by rfl) ⟨1582829, by rfl⟩ : syracuseStep 2110439 = 3165659) B3165659
theorem B2374249 : Blo 2109435 2374249 := bbase (se 2 (by rfl) ⟨890343, by rfl⟩ : syracuseStep 2374249 = 1780687) (by norm_num)
theorem B3165665 : Blo 2109435 3165665 := bstep (se 2 (by rfl) ⟨1187124, by rfl⟩ : syracuseStep 3165665 = 2374249) B2374249
theorem B2110443 : Blo 2109435 2110443 := bstep (se 1 (by rfl) ⟨1582832, by rfl⟩ : syracuseStep 2110443 = 3165665) B3165665
theorem B4507373 : Blo 2109435 4507373 := bbase (se 3 (by rfl) ⟨845132, by rfl⟩ : syracuseStep 4507373 = 1690265) (by norm_num)
theorem B12019661 : Blo 2109435 12019661 := bstep (se 3 (by rfl) ⟨2253686, by rfl⟩ : syracuseStep 12019661 = 4507373) B4507373
theorem B8013107 : Blo 2109435 8013107 := bstep (se 1 (by rfl) ⟨6009830, by rfl⟩ : syracuseStep 8013107 = 12019661) B12019661
theorem B5342071 : Blo 2109435 5342071 := bstep (se 1 (by rfl) ⟨4006553, by rfl⟩ : syracuseStep 5342071 = 8013107) B8013107
theorem B7122761 : Blo 2109435 7122761 := bstep (se 2 (by rfl) ⟨2671035, by rfl⟩ : syracuseStep 7122761 = 5342071) B5342071
theorem B4748507 : Blo 2109435 4748507 := bstep (se 1 (by rfl) ⟨3561380, by rfl⟩ : syracuseStep 4748507 = 7122761) B7122761
theorem B3165671 : Blo 2109435 3165671 := bstep (se 1 (by rfl) ⟨2374253, by rfl⟩ : syracuseStep 3165671 = 4748507) B4748507
theorem B2110447 : Blo 2109435 2110447 := bstep (se 1 (by rfl) ⟨1582835, by rfl⟩ : syracuseStep 2110447 = 3165671) B3165671
theorem B3165677 : Blo 2109435 3165677 := bbase (se 3 (by rfl) ⟨593564, by rfl⟩ : syracuseStep 3165677 = 1187129) (by norm_num)
theorem B2110451 : Blo 2109435 2110451 := bstep (se 1 (by rfl) ⟨1582838, by rfl⟩ : syracuseStep 2110451 = 3165677) B3165677
theorem B4748525 : Blo 2109435 4748525 := bbase (se 3 (by rfl) ⟨890348, by rfl⟩ : syracuseStep 4748525 = 1780697) (by norm_num)
theorem B3165683 : Blo 2109435 3165683 := bstep (se 1 (by rfl) ⟨2374262, by rfl⟩ : syracuseStep 3165683 = 4748525) B4748525
theorem B2110455 : Blo 2109435 2110455 := bstep (se 1 (by rfl) ⟨1582841, by rfl⟩ : syracuseStep 2110455 = 3165683) B3165683
theorem B3004933 : Blo 2109435 3004933 := bbase (se 4 (by rfl) ⟨281712, by rfl⟩ : syracuseStep 3004933 = 563425) (by norm_num)
theorem B4006577 : Blo 2109435 4006577 := bstep (se 2 (by rfl) ⟨1502466, by rfl⟩ : syracuseStep 4006577 = 3004933) B3004933
theorem B2671051 : Blo 2109435 2671051 := bstep (se 1 (by rfl) ⟨2003288, by rfl⟩ : syracuseStep 2671051 = 4006577) B4006577
theorem B3561401 : Blo 2109435 3561401 := bstep (se 2 (by rfl) ⟨1335525, by rfl⟩ : syracuseStep 3561401 = 2671051) B2671051
theorem B2374267 : Blo 2109435 2374267 := bstep (se 1 (by rfl) ⟨1780700, by rfl⟩ : syracuseStep 2374267 = 3561401) B3561401
theorem B3165689 : Blo 2109435 3165689 := bstep (se 2 (by rfl) ⟨1187133, by rfl⟩ : syracuseStep 3165689 = 2374267) B2374267
theorem B2110459 : Blo 2109435 2110459 := bstep (se 1 (by rfl) ⟨1582844, by rfl⟩ : syracuseStep 2110459 = 3165689) B3165689
theorem B5488877 : Blo 2109435 5488877 := bbase (se 3 (by rfl) ⟨1029164, by rfl⟩ : syracuseStep 5488877 = 2058329) (by norm_num)
theorem B3659251 : Blo 2109435 3659251 := bstep (se 1 (by rfl) ⟨2744438, by rfl⟩ : syracuseStep 3659251 = 5488877) B5488877
theorem B4879001 : Blo 2109435 4879001 := bstep (se 2 (by rfl) ⟨1829625, by rfl⟩ : syracuseStep 4879001 = 3659251) B3659251
theorem B3252667 : Blo 2109435 3252667 := bstep (se 1 (by rfl) ⟨2439500, by rfl⟩ : syracuseStep 3252667 = 4879001) B4879001
theorem B69390229 : Blo 2109435 69390229 := bstep (se 6 (by rfl) ⟨1626333, by rfl⟩ : syracuseStep 69390229 = 3252667) B3252667
theorem B92520305 : Blo 2109435 92520305 := bstep (se 2 (by rfl) ⟨34695114, by rfl⟩ : syracuseStep 92520305 = 69390229) B69390229
theorem B61680203 : Blo 2109435 61680203 := bstep (se 1 (by rfl) ⟨46260152, by rfl⟩ : syracuseStep 61680203 = 92520305) B92520305
theorem B41120135 : Blo 2109435 41120135 := bstep (se 1 (by rfl) ⟨30840101, by rfl⟩ : syracuseStep 41120135 = 61680203) B61680203
theorem B27413423 : Blo 2109435 27413423 := bstep (se 1 (by rfl) ⟨20560067, by rfl⟩ : syracuseStep 27413423 = 41120135) B41120135
theorem B18275615 : Blo 2109435 18275615 := bstep (se 1 (by rfl) ⟨13706711, by rfl⟩ : syracuseStep 18275615 = 27413423) B27413423
theorem B12183743 : Blo 2109435 12183743 := bstep (se 1 (by rfl) ⟨9137807, by rfl⟩ : syracuseStep 12183743 = 18275615) B18275615
theorem B32489981 : Blo 2109435 32489981 := bstep (se 3 (by rfl) ⟨6091871, by rfl⟩ : syracuseStep 32489981 = 12183743) B12183743
theorem B21659987 : Blo 2109435 21659987 := bstep (se 1 (by rfl) ⟨16244990, by rfl⟩ : syracuseStep 21659987 = 32489981) B32489981
theorem B14439991 : Blo 2109435 14439991 := bstep (se 1 (by rfl) ⟨10829993, by rfl⟩ : syracuseStep 14439991 = 21659987) B21659987
theorem B19253321 : Blo 2109435 19253321 := bstep (se 2 (by rfl) ⟨7219995, by rfl⟩ : syracuseStep 19253321 = 14439991) B14439991
theorem B12835547 : Blo 2109435 12835547 := bstep (se 1 (by rfl) ⟨9626660, by rfl⟩ : syracuseStep 12835547 = 19253321) B19253321
theorem B8557031 : Blo 2109435 8557031 := bstep (se 1 (by rfl) ⟨6417773, by rfl⟩ : syracuseStep 8557031 = 12835547) B12835547
theorem B5704687 : Blo 2109435 5704687 := bstep (se 1 (by rfl) ⟨4278515, by rfl⟩ : syracuseStep 5704687 = 8557031) B8557031
theorem B30424997 : Blo 2109435 30424997 := bstep (se 4 (by rfl) ⟨2852343, by rfl⟩ : syracuseStep 30424997 = 5704687) B5704687
theorem B81133325 : Blo 2109435 81133325 := bstep (se 3 (by rfl) ⟨15212498, by rfl⟩ : syracuseStep 81133325 = 30424997) B30424997
theorem B54088883 : Blo 2109435 54088883 := bstep (se 1 (by rfl) ⟨40566662, by rfl⟩ : syracuseStep 54088883 = 81133325) B81133325
theorem B36059255 : Blo 2109435 36059255 := bstep (se 1 (by rfl) ⟨27044441, by rfl⟩ : syracuseStep 36059255 = 54088883) B54088883
theorem B24039503 : Blo 2109435 24039503 := bstep (se 1 (by rfl) ⟨18029627, by rfl⟩ : syracuseStep 24039503 = 36059255) B36059255
theorem B16026335 : Blo 2109435 16026335 := bstep (se 1 (by rfl) ⟨12019751, by rfl⟩ : syracuseStep 16026335 = 24039503) B24039503
theorem B10684223 : Blo 2109435 10684223 := bstep (se 1 (by rfl) ⟨8013167, by rfl⟩ : syracuseStep 10684223 = 16026335) B16026335
theorem B7122815 : Blo 2109435 7122815 := bstep (se 1 (by rfl) ⟨5342111, by rfl⟩ : syracuseStep 7122815 = 10684223) B10684223
theorem B4748543 : Blo 2109435 4748543 := bstep (se 1 (by rfl) ⟨3561407, by rfl⟩ : syracuseStep 4748543 = 7122815) B7122815
theorem B3165695 : Blo 2109435 3165695 := bstep (se 1 (by rfl) ⟨2374271, by rfl⟩ : syracuseStep 3165695 = 4748543) B4748543
theorem B2110463 : Blo 2109435 2110463 := bstep (se 1 (by rfl) ⟨1582847, by rfl⟩ : syracuseStep 2110463 = 3165695) B3165695
theorem B3165701 : Blo 2109435 3165701 := bbase (se 4 (by rfl) ⟨296784, by rfl⟩ : syracuseStep 3165701 = 593569) (by norm_num)
theorem B2110467 : Blo 2109435 2110467 := bstep (se 1 (by rfl) ⟨1582850, by rfl⟩ : syracuseStep 2110467 = 3165701) B3165701
theorem B3561421 : Blo 2109435 3561421 := bbase (se 3 (by rfl) ⟨667766, by rfl⟩ : syracuseStep 3561421 = 1335533) (by norm_num)
theorem B4748561 : Blo 2109435 4748561 := bstep (se 2 (by rfl) ⟨1780710, by rfl⟩ : syracuseStep 4748561 = 3561421) B3561421
theorem B3165707 : Blo 2109435 3165707 := bstep (se 1 (by rfl) ⟨2374280, by rfl⟩ : syracuseStep 3165707 = 4748561) B4748561
theorem B2110471 : Blo 2109435 2110471 := bstep (se 1 (by rfl) ⟨1582853, by rfl⟩ : syracuseStep 2110471 = 3165707) B3165707
theorem B2374285 : Blo 2109435 2374285 := bbase (se 3 (by rfl) ⟨445178, by rfl⟩ : syracuseStep 2374285 = 890357) (by norm_num)
theorem B3165713 : Blo 2109435 3165713 := bstep (se 2 (by rfl) ⟨1187142, by rfl⟩ : syracuseStep 3165713 = 2374285) B2374285
theorem B2110475 : Blo 2109435 2110475 := bstep (se 1 (by rfl) ⟨1582856, by rfl⟩ : syracuseStep 2110475 = 3165713) B3165713
theorem B7122869 : Blo 2109435 7122869 := bbase (se 5 (by rfl) ⟨333884, by rfl⟩ : syracuseStep 7122869 = 667769) (by norm_num)
theorem B4748579 : Blo 2109435 4748579 := bstep (se 1 (by rfl) ⟨3561434, by rfl⟩ : syracuseStep 4748579 = 7122869) B7122869
theorem B3165719 : Blo 2109435 3165719 := bstep (se 1 (by rfl) ⟨2374289, by rfl⟩ : syracuseStep 3165719 = 4748579) B4748579
theorem B2110479 : Blo 2109435 2110479 := bstep (se 1 (by rfl) ⟨1582859, by rfl⟩ : syracuseStep 2110479 = 3165719) B3165719
theorem B3165725 : Blo 2109435 3165725 := bbase (se 3 (by rfl) ⟨593573, by rfl⟩ : syracuseStep 3165725 = 1187147) (by norm_num)
theorem B2110483 : Blo 2109435 2110483 := bstep (se 1 (by rfl) ⟨1582862, by rfl⟩ : syracuseStep 2110483 = 3165725) B3165725
theorem B4748597 : Blo 2109435 4748597 := bbase (se 5 (by rfl) ⟨222590, by rfl⟩ : syracuseStep 4748597 = 445181) (by norm_num)
theorem B3165731 : Blo 2109435 3165731 := bstep (se 1 (by rfl) ⟨2374298, by rfl⟩ : syracuseStep 3165731 = 4748597) B4748597
theorem B2110487 : Blo 2109435 2110487 := bstep (se 1 (by rfl) ⟨1582865, by rfl⟩ : syracuseStep 2110487 = 3165731) B3165731
theorem B20283605 : Blo 2109435 20283605 := bbase (se 7 (by rfl) ⟨237698, by rfl⟩ : syracuseStep 20283605 = 475397) (by norm_num)
theorem B13522403 : Blo 2109435 13522403 := bstep (se 1 (by rfl) ⟨10141802, by rfl⟩ : syracuseStep 13522403 = 20283605) B20283605
theorem B9014935 : Blo 2109435 9014935 := bstep (se 1 (by rfl) ⟨6761201, by rfl⟩ : syracuseStep 9014935 = 13522403) B13522403
theorem B12019913 : Blo 2109435 12019913 := bstep (se 2 (by rfl) ⟨4507467, by rfl⟩ : syracuseStep 12019913 = 9014935) B9014935
theorem B8013275 : Blo 2109435 8013275 := bstep (se 1 (by rfl) ⟨6009956, by rfl⟩ : syracuseStep 8013275 = 12019913) B12019913
theorem B5342183 : Blo 2109435 5342183 := bstep (se 1 (by rfl) ⟨4006637, by rfl⟩ : syracuseStep 5342183 = 8013275) B8013275
theorem B3561455 : Blo 2109435 3561455 := bstep (se 1 (by rfl) ⟨2671091, by rfl⟩ : syracuseStep 3561455 = 5342183) B5342183
theorem B2374303 : Blo 2109435 2374303 := bstep (se 1 (by rfl) ⟨1780727, by rfl⟩ : syracuseStep 2374303 = 3561455) B3561455
theorem B3165737 : Blo 2109435 3165737 := bstep (se 2 (by rfl) ⟨1187151, by rfl⟩ : syracuseStep 3165737 = 2374303) B2374303
theorem B2110491 : Blo 2109435 2110491 := bstep (se 1 (by rfl) ⟨1582868, by rfl⟩ : syracuseStep 2110491 = 3165737) B3165737
theorem B4516901 : Blo 2109435 4516901 := bbase (se 4 (by rfl) ⟨423459, by rfl⟩ : syracuseStep 4516901 = 846919) (by norm_num)
theorem B3011267 : Blo 2109435 3011267 := bstep (se 1 (by rfl) ⟨2258450, by rfl⟩ : syracuseStep 3011267 = 4516901) B4516901
theorem B8030045 : Blo 2109435 8030045 := bstep (se 3 (by rfl) ⟨1505633, by rfl⟩ : syracuseStep 8030045 = 3011267) B3011267
theorem B5353363 : Blo 2109435 5353363 := bstep (se 1 (by rfl) ⟨4015022, by rfl⟩ : syracuseStep 5353363 = 8030045) B8030045
theorem B7137817 : Blo 2109435 7137817 := bstep (se 2 (by rfl) ⟨2676681, by rfl⟩ : syracuseStep 7137817 = 5353363) B5353363
theorem B152273429 : Blo 2109435 152273429 := bstep (se 6 (by rfl) ⟨3568908, by rfl⟩ : syracuseStep 152273429 = 7137817) B7137817
theorem B101515619 : Blo 2109435 101515619 := bstep (se 1 (by rfl) ⟨76136714, by rfl⟩ : syracuseStep 101515619 = 152273429) B152273429
theorem B67677079 : Blo 2109435 67677079 := bstep (se 1 (by rfl) ⟨50757809, by rfl⟩ : syracuseStep 67677079 = 101515619) B101515619
theorem B90236105 : Blo 2109435 90236105 := bstep (se 2 (by rfl) ⟨33838539, by rfl⟩ : syracuseStep 90236105 = 67677079) B67677079
theorem B60157403 : Blo 2109435 60157403 := bstep (se 1 (by rfl) ⟨45118052, by rfl⟩ : syracuseStep 60157403 = 90236105) B90236105
theorem B40104935 : Blo 2109435 40104935 := bstep (se 1 (by rfl) ⟨30078701, by rfl⟩ : syracuseStep 40104935 = 60157403) B60157403
theorem B26736623 : Blo 2109435 26736623 := bstep (se 1 (by rfl) ⟨20052467, by rfl⟩ : syracuseStep 26736623 = 40104935) B40104935
theorem B285190645 : Blo 2109435 285190645 := bstep (se 5 (by rfl) ⟨13368311, by rfl⟩ : syracuseStep 285190645 = 26736623) B26736623
theorem B380254193 : Blo 2109435 380254193 := bstep (se 2 (by rfl) ⟨142595322, by rfl⟩ : syracuseStep 380254193 = 285190645) B285190645
theorem B253502795 : Blo 2109435 253502795 := bstep (se 1 (by rfl) ⟨190127096, by rfl⟩ : syracuseStep 253502795 = 380254193) B380254193
theorem B676007453 : Blo 2109435 676007453 := bstep (se 3 (by rfl) ⟨126751397, by rfl⟩ : syracuseStep 676007453 = 253502795) B253502795
theorem B450671635 : Blo 2109435 450671635 := bstep (se 1 (by rfl) ⟨338003726, by rfl⟩ : syracuseStep 450671635 = 676007453) B676007453
theorem B600895513 : Blo 2109435 600895513 := bstep (se 2 (by rfl) ⟨225335817, by rfl⟩ : syracuseStep 600895513 = 450671635) B450671635
theorem B801194017 : Blo 2109435 801194017 := bstep (se 2 (by rfl) ⟨300447756, by rfl⟩ : syracuseStep 801194017 = 600895513) B600895513
theorem B1068258689 : Blo 2109435 1068258689 := bstep (se 2 (by rfl) ⟨400597008, by rfl⟩ : syracuseStep 1068258689 = 801194017) B801194017
theorem B712172459 : Blo 2109435 712172459 := bstep (se 1 (by rfl) ⟨534129344, by rfl⟩ : syracuseStep 712172459 = 1068258689) B1068258689
theorem B1899126557 : Blo 2109435 1899126557 := bstep (se 3 (by rfl) ⟨356086229, by rfl⟩ : syracuseStep 1899126557 = 712172459) B712172459
theorem B1266084371 : Blo 2109435 1266084371 := bstep (se 1 (by rfl) ⟨949563278, by rfl⟩ : syracuseStep 1266084371 = 1899126557) B1899126557
theorem B844056247 : Blo 2109435 844056247 := bstep (se 1 (by rfl) ⟨633042185, by rfl⟩ : syracuseStep 844056247 = 1266084371) B1266084371
theorem B1125408329 : Blo 2109435 1125408329 := bstep (se 2 (by rfl) ⟨422028123, by rfl⟩ : syracuseStep 1125408329 = 844056247) B844056247
theorem B750272219 : Blo 2109435 750272219 := bstep (se 1 (by rfl) ⟨562704164, by rfl⟩ : syracuseStep 750272219 = 1125408329) B1125408329
theorem B500181479 : Blo 2109435 500181479 := bstep (se 1 (by rfl) ⟨375136109, by rfl⟩ : syracuseStep 500181479 = 750272219) B750272219
theorem B333454319 : Blo 2109435 333454319 := bstep (se 1 (by rfl) ⟨250090739, by rfl⟩ : syracuseStep 333454319 = 500181479) B500181479
theorem B222302879 : Blo 2109435 222302879 := bstep (se 1 (by rfl) ⟨166727159, by rfl⟩ : syracuseStep 222302879 = 333454319) B333454319
theorem B148201919 : Blo 2109435 148201919 := bstep (se 1 (by rfl) ⟨111151439, by rfl⟩ : syracuseStep 148201919 = 222302879) B222302879
theorem B98801279 : Blo 2109435 98801279 := bstep (se 1 (by rfl) ⟨74100959, by rfl⟩ : syracuseStep 98801279 = 148201919) B148201919
theorem B65867519 : Blo 2109435 65867519 := bstep (se 1 (by rfl) ⟨49400639, by rfl⟩ : syracuseStep 65867519 = 98801279) B98801279
theorem B175646717 : Blo 2109435 175646717 := bstep (se 3 (by rfl) ⟨32933759, by rfl⟩ : syracuseStep 175646717 = 65867519) B65867519
theorem B117097811 : Blo 2109435 117097811 := bstep (se 1 (by rfl) ⟨87823358, by rfl⟩ : syracuseStep 117097811 = 175646717) B175646717
theorem B78065207 : Blo 2109435 78065207 := bstep (se 1 (by rfl) ⟨58548905, by rfl⟩ : syracuseStep 78065207 = 117097811) B117097811
theorem B52043471 : Blo 2109435 52043471 := bstep (se 1 (by rfl) ⟨39032603, by rfl⟩ : syracuseStep 52043471 = 78065207) B78065207
theorem B34695647 : Blo 2109435 34695647 := bstep (se 1 (by rfl) ⟨26021735, by rfl⟩ : syracuseStep 34695647 = 52043471) B52043471
theorem B23130431 : Blo 2109435 23130431 := bstep (se 1 (by rfl) ⟨17347823, by rfl⟩ : syracuseStep 23130431 = 34695647) B34695647
theorem B15420287 : Blo 2109435 15420287 := bstep (se 1 (by rfl) ⟨11565215, by rfl⟩ : syracuseStep 15420287 = 23130431) B23130431
theorem B10280191 : Blo 2109435 10280191 := bstep (se 1 (by rfl) ⟨7710143, by rfl⟩ : syracuseStep 10280191 = 15420287) B15420287
theorem B13706921 : Blo 2109435 13706921 := bstep (se 2 (by rfl) ⟨5140095, by rfl⟩ : syracuseStep 13706921 = 10280191) B10280191
theorem B9137947 : Blo 2109435 9137947 := bstep (se 1 (by rfl) ⟨6853460, by rfl⟩ : syracuseStep 9137947 = 13706921) B13706921
theorem B12183929 : Blo 2109435 12183929 := bstep (se 2 (by rfl) ⟨4568973, by rfl⟩ : syracuseStep 12183929 = 9137947) B9137947
theorem B8122619 : Blo 2109435 8122619 := bstep (se 1 (by rfl) ⟨6091964, by rfl⟩ : syracuseStep 8122619 = 12183929) B12183929
theorem B21660317 : Blo 2109435 21660317 := bstep (se 3 (by rfl) ⟨4061309, by rfl⟩ : syracuseStep 21660317 = 8122619) B8122619
theorem B14440211 : Blo 2109435 14440211 := bstep (se 1 (by rfl) ⟨10830158, by rfl⟩ : syracuseStep 14440211 = 21660317) B21660317
theorem B9626807 : Blo 2109435 9626807 := bstep (se 1 (by rfl) ⟨7220105, by rfl⟩ : syracuseStep 9626807 = 14440211) B14440211
theorem B25671485 : Blo 2109435 25671485 := bstep (se 3 (by rfl) ⟨4813403, by rfl⟩ : syracuseStep 25671485 = 9626807) B9626807
theorem B17114323 : Blo 2109435 17114323 := bstep (se 1 (by rfl) ⟨12835742, by rfl⟩ : syracuseStep 17114323 = 25671485) B25671485
theorem B22819097 : Blo 2109435 22819097 := bstep (se 2 (by rfl) ⟨8557161, by rfl⟩ : syracuseStep 22819097 = 17114323) B17114323
theorem B15212731 : Blo 2109435 15212731 := bstep (se 1 (by rfl) ⟨11409548, by rfl⟩ : syracuseStep 15212731 = 22819097) B22819097
theorem B20283641 : Blo 2109435 20283641 := bstep (se 2 (by rfl) ⟨7606365, by rfl⟩ : syracuseStep 20283641 = 15212731) B15212731
theorem B13522427 : Blo 2109435 13522427 := bstep (se 1 (by rfl) ⟨10141820, by rfl⟩ : syracuseStep 13522427 = 20283641) B20283641
theorem B9014951 : Blo 2109435 9014951 := bstep (se 1 (by rfl) ⟨6761213, by rfl⟩ : syracuseStep 9014951 = 13522427) B13522427
theorem B6009967 : Blo 2109435 6009967 := bstep (se 1 (by rfl) ⟨4507475, by rfl⟩ : syracuseStep 6009967 = 9014951) B9014951
theorem B8013289 : Blo 2109435 8013289 := bstep (se 2 (by rfl) ⟨3004983, by rfl⟩ : syracuseStep 8013289 = 6009967) B6009967
theorem B10684385 : Blo 2109435 10684385 := bstep (se 2 (by rfl) ⟨4006644, by rfl⟩ : syracuseStep 10684385 = 8013289) B8013289
theorem B7122923 : Blo 2109435 7122923 := bstep (se 1 (by rfl) ⟨5342192, by rfl⟩ : syracuseStep 7122923 = 10684385) B10684385
theorem B4748615 : Blo 2109435 4748615 := bstep (se 1 (by rfl) ⟨3561461, by rfl⟩ : syracuseStep 4748615 = 7122923) B7122923
theorem B3165743 : Blo 2109435 3165743 := bstep (se 1 (by rfl) ⟨2374307, by rfl⟩ : syracuseStep 3165743 = 4748615) B4748615
theorem B2110495 : Blo 2109435 2110495 := bstep (se 1 (by rfl) ⟨1582871, by rfl⟩ : syracuseStep 2110495 = 3165743) B3165743
theorem B3165749 : Blo 2109435 3165749 := bbase (se 5 (by rfl) ⟨148394, by rfl⟩ : syracuseStep 3165749 = 296789) (by norm_num)
theorem B2110499 : Blo 2109435 2110499 := bstep (se 1 (by rfl) ⟨1582874, by rfl⟩ : syracuseStep 2110499 = 3165749) B3165749
theorem B5342213 : Blo 2109435 5342213 := bbase (se 4 (by rfl) ⟨500832, by rfl⟩ : syracuseStep 5342213 = 1001665) (by norm_num)
theorem B3561475 : Blo 2109435 3561475 := bstep (se 1 (by rfl) ⟨2671106, by rfl⟩ : syracuseStep 3561475 = 5342213) B5342213
theorem B4748633 : Blo 2109435 4748633 := bstep (se 2 (by rfl) ⟨1780737, by rfl⟩ : syracuseStep 4748633 = 3561475) B3561475
theorem B3165755 : Blo 2109435 3165755 := bstep (se 1 (by rfl) ⟨2374316, by rfl⟩ : syracuseStep 3165755 = 4748633) B4748633
theorem B2110503 : Blo 2109435 2110503 := bstep (se 1 (by rfl) ⟨1582877, by rfl⟩ : syracuseStep 2110503 = 3165755) B3165755
theorem B2374321 : Blo 2109435 2374321 := bbase (se 2 (by rfl) ⟨890370, by rfl⟩ : syracuseStep 2374321 = 1780741) (by norm_num)
theorem B3165761 : Blo 2109435 3165761 := bstep (se 2 (by rfl) ⟨1187160, by rfl⟩ : syracuseStep 3165761 = 2374321) B2374321
theorem B2110507 : Blo 2109435 2110507 := bstep (se 1 (by rfl) ⟨1582880, by rfl⟩ : syracuseStep 2110507 = 3165761) B3165761
theorem B3803213 : Blo 2109435 3803213 := bbase (se 3 (by rfl) ⟨713102, by rfl⟩ : syracuseStep 3803213 = 1426205) (by norm_num)
theorem B2535475 : Blo 2109435 2535475 := bstep (se 1 (by rfl) ⟨1901606, by rfl⟩ : syracuseStep 2535475 = 3803213) B3803213
theorem B3380633 : Blo 2109435 3380633 := bstep (se 2 (by rfl) ⟨1267737, by rfl⟩ : syracuseStep 3380633 = 2535475) B2535475
theorem B2253755 : Blo 2109435 2253755 := bstep (se 1 (by rfl) ⟨1690316, by rfl⟩ : syracuseStep 2253755 = 3380633) B3380633
theorem B6010013 : Blo 2109435 6010013 := bstep (se 3 (by rfl) ⟨1126877, by rfl⟩ : syracuseStep 6010013 = 2253755) B2253755
theorem B4006675 : Blo 2109435 4006675 := bstep (se 1 (by rfl) ⟨3005006, by rfl⟩ : syracuseStep 4006675 = 6010013) B6010013
theorem B5342233 : Blo 2109435 5342233 := bstep (se 2 (by rfl) ⟨2003337, by rfl⟩ : syracuseStep 5342233 = 4006675) B4006675
theorem B7122977 : Blo 2109435 7122977 := bstep (se 2 (by rfl) ⟨2671116, by rfl⟩ : syracuseStep 7122977 = 5342233) B5342233
theorem B4748651 : Blo 2109435 4748651 := bstep (se 1 (by rfl) ⟨3561488, by rfl⟩ : syracuseStep 4748651 = 7122977) B7122977
theorem B3165767 : Blo 2109435 3165767 := bstep (se 1 (by rfl) ⟨2374325, by rfl⟩ : syracuseStep 3165767 = 4748651) B4748651
theorem B2110511 : Blo 2109435 2110511 := bstep (se 1 (by rfl) ⟨1582883, by rfl⟩ : syracuseStep 2110511 = 3165767) B3165767
theorem B3165773 : Blo 2109435 3165773 := bbase (se 3 (by rfl) ⟨593582, by rfl⟩ : syracuseStep 3165773 = 1187165) (by norm_num)
theorem B2110515 : Blo 2109435 2110515 := bstep (se 1 (by rfl) ⟨1582886, by rfl⟩ : syracuseStep 2110515 = 3165773) B3165773
theorem B4748669 : Blo 2109435 4748669 := bbase (se 3 (by rfl) ⟨890375, by rfl⟩ : syracuseStep 4748669 = 1780751) (by norm_num)
theorem B3165779 : Blo 2109435 3165779 := bstep (se 1 (by rfl) ⟨2374334, by rfl⟩ : syracuseStep 3165779 = 4748669) B4748669
theorem B2110519 : Blo 2109435 2110519 := bstep (se 1 (by rfl) ⟨1582889, by rfl⟩ : syracuseStep 2110519 = 3165779) B3165779
theorem B3561509 : Blo 2109435 3561509 := bbase (se 4 (by rfl) ⟨333891, by rfl⟩ : syracuseStep 3561509 = 667783) (by norm_num)
theorem B2374339 : Blo 2109435 2374339 := bstep (se 1 (by rfl) ⟨1780754, by rfl⟩ : syracuseStep 2374339 = 3561509) B3561509
theorem B3165785 : Blo 2109435 3165785 := bstep (se 2 (by rfl) ⟨1187169, by rfl⟩ : syracuseStep 3165785 = 2374339) B2374339
theorem B2110523 : Blo 2109435 2110523 := bstep (se 1 (by rfl) ⟨1582892, by rfl⟩ : syracuseStep 2110523 = 3165785) B3165785
theorem B3005029 : Blo 2109435 3005029 := bbase (se 4 (by rfl) ⟨281721, by rfl⟩ : syracuseStep 3005029 = 563443) (by norm_num)
theorem B16026821 : Blo 2109435 16026821 := bstep (se 4 (by rfl) ⟨1502514, by rfl⟩ : syracuseStep 16026821 = 3005029) B3005029
theorem B10684547 : Blo 2109435 10684547 := bstep (se 1 (by rfl) ⟨8013410, by rfl⟩ : syracuseStep 10684547 = 16026821) B16026821
theorem B7123031 : Blo 2109435 7123031 := bstep (se 1 (by rfl) ⟨5342273, by rfl⟩ : syracuseStep 7123031 = 10684547) B10684547
theorem B4748687 : Blo 2109435 4748687 := bstep (se 1 (by rfl) ⟨3561515, by rfl⟩ : syracuseStep 4748687 = 7123031) B7123031
theorem B3165791 : Blo 2109435 3165791 := bstep (se 1 (by rfl) ⟨2374343, by rfl⟩ : syracuseStep 3165791 = 4748687) B4748687
theorem B2110527 : Blo 2109435 2110527 := bstep (se 1 (by rfl) ⟨1582895, by rfl⟩ : syracuseStep 2110527 = 3165791) B3165791
theorem B3165797 : Blo 2109435 3165797 := bbase (se 4 (by rfl) ⟨296793, by rfl⟩ : syracuseStep 3165797 = 593587) (by norm_num)
theorem B2110531 : Blo 2109435 2110531 := bstep (se 1 (by rfl) ⟨1582898, by rfl⟩ : syracuseStep 2110531 = 3165797) B3165797
theorem B2253781 : Blo 2109435 2253781 := bbase (se 7 (by rfl) ⟨26411, by rfl⟩ : syracuseStep 2253781 = 52823) (by norm_num)
theorem B3005041 : Blo 2109435 3005041 := bstep (se 2 (by rfl) ⟨1126890, by rfl⟩ : syracuseStep 3005041 = 2253781) B2253781
theorem B4006721 : Blo 2109435 4006721 := bstep (se 2 (by rfl) ⟨1502520, by rfl⟩ : syracuseStep 4006721 = 3005041) B3005041
theorem B2671147 : Blo 2109435 2671147 := bstep (se 1 (by rfl) ⟨2003360, by rfl⟩ : syracuseStep 2671147 = 4006721) B4006721
theorem B3561529 : Blo 2109435 3561529 := bstep (se 2 (by rfl) ⟨1335573, by rfl⟩ : syracuseStep 3561529 = 2671147) B2671147
theorem B4748705 : Blo 2109435 4748705 := bstep (se 2 (by rfl) ⟨1780764, by rfl⟩ : syracuseStep 4748705 = 3561529) B3561529
theorem B3165803 : Blo 2109435 3165803 := bstep (se 1 (by rfl) ⟨2374352, by rfl⟩ : syracuseStep 3165803 = 4748705) B4748705
theorem B2110535 : Blo 2109435 2110535 := bstep (se 1 (by rfl) ⟨1582901, by rfl⟩ : syracuseStep 2110535 = 3165803) B3165803
theorem B2374357 : Blo 2109435 2374357 := bbase (se 7 (by rfl) ⟨27824, by rfl⟩ : syracuseStep 2374357 = 55649) (by norm_num)
theorem B3165809 : Blo 2109435 3165809 := bstep (se 2 (by rfl) ⟨1187178, by rfl⟩ : syracuseStep 3165809 = 2374357) B2374357
theorem B2110539 : Blo 2109435 2110539 := bstep (se 1 (by rfl) ⟨1582904, by rfl⟩ : syracuseStep 2110539 = 3165809) B3165809
theorem B2671157 : Blo 2109435 2671157 := bbase (se 5 (by rfl) ⟨125210, by rfl⟩ : syracuseStep 2671157 = 250421) (by norm_num)
theorem B7123085 : Blo 2109435 7123085 := bstep (se 3 (by rfl) ⟨1335578, by rfl⟩ : syracuseStep 7123085 = 2671157) B2671157
theorem B4748723 : Blo 2109435 4748723 := bstep (se 1 (by rfl) ⟨3561542, by rfl⟩ : syracuseStep 4748723 = 7123085) B7123085
theorem B3165815 : Blo 2109435 3165815 := bstep (se 1 (by rfl) ⟨2374361, by rfl⟩ : syracuseStep 3165815 = 4748723) B4748723
theorem B2110543 : Blo 2109435 2110543 := bstep (se 1 (by rfl) ⟨1582907, by rfl⟩ : syracuseStep 2110543 = 3165815) B3165815
theorem B3165821 : Blo 2109435 3165821 := bbase (se 3 (by rfl) ⟨593591, by rfl⟩ : syracuseStep 3165821 = 1187183) (by norm_num)
theorem B2110547 : Blo 2109435 2110547 := bstep (se 1 (by rfl) ⟨1582910, by rfl⟩ : syracuseStep 2110547 = 3165821) B3165821
theorem B4748741 : Blo 2109435 4748741 := bbase (se 4 (by rfl) ⟨445194, by rfl⟩ : syracuseStep 4748741 = 890389) (by norm_num)
theorem B3165827 : Blo 2109435 3165827 := bstep (se 1 (by rfl) ⟨2374370, by rfl⟩ : syracuseStep 3165827 = 4748741) B4748741
theorem B2110551 : Blo 2109435 2110551 := bstep (se 1 (by rfl) ⟨1582913, by rfl⟩ : syracuseStep 2110551 = 3165827) B3165827
theorem B12184277 : Blo 2109435 12184277 := bbase (se 7 (by rfl) ⟨142784, by rfl⟩ : syracuseStep 12184277 = 285569) (by norm_num)
theorem B32491405 : Blo 2109435 32491405 := bstep (se 3 (by rfl) ⟨6092138, by rfl⟩ : syracuseStep 32491405 = 12184277) B12184277
theorem B43321873 : Blo 2109435 43321873 := bstep (se 2 (by rfl) ⟨16245702, by rfl⟩ : syracuseStep 43321873 = 32491405) B32491405
theorem B57762497 : Blo 2109435 57762497 := bstep (se 2 (by rfl) ⟨21660936, by rfl⟩ : syracuseStep 57762497 = 43321873) B43321873
theorem B38508331 : Blo 2109435 38508331 := bstep (se 1 (by rfl) ⟨28881248, by rfl⟩ : syracuseStep 38508331 = 57762497) B57762497
theorem B51344441 : Blo 2109435 51344441 := bstep (se 2 (by rfl) ⟨19254165, by rfl⟩ : syracuseStep 51344441 = 38508331) B38508331
theorem B34229627 : Blo 2109435 34229627 := bstep (se 1 (by rfl) ⟨25672220, by rfl⟩ : syracuseStep 34229627 = 51344441) B51344441
theorem B22819751 : Blo 2109435 22819751 := bstep (se 1 (by rfl) ⟨17114813, by rfl⟩ : syracuseStep 22819751 = 34229627) B34229627
theorem B15213167 : Blo 2109435 15213167 := bstep (se 1 (by rfl) ⟨11409875, by rfl⟩ : syracuseStep 15213167 = 22819751) B22819751
theorem B10142111 : Blo 2109435 10142111 := bstep (se 1 (by rfl) ⟨7606583, by rfl⟩ : syracuseStep 10142111 = 15213167) B15213167
theorem B6761407 : Blo 2109435 6761407 := bstep (se 1 (by rfl) ⟨5071055, by rfl⟩ : syracuseStep 6761407 = 10142111) B10142111
theorem B9015209 : Blo 2109435 9015209 := bstep (se 2 (by rfl) ⟨3380703, by rfl⟩ : syracuseStep 9015209 = 6761407) B6761407
theorem B6010139 : Blo 2109435 6010139 := bstep (se 1 (by rfl) ⟨4507604, by rfl⟩ : syracuseStep 6010139 = 9015209) B9015209
theorem B4006759 : Blo 2109435 4006759 := bstep (se 1 (by rfl) ⟨3005069, by rfl⟩ : syracuseStep 4006759 = 6010139) B6010139
theorem B5342345 : Blo 2109435 5342345 := bstep (se 2 (by rfl) ⟨2003379, by rfl⟩ : syracuseStep 5342345 = 4006759) B4006759
theorem B3561563 : Blo 2109435 3561563 := bstep (se 1 (by rfl) ⟨2671172, by rfl⟩ : syracuseStep 3561563 = 5342345) B5342345
theorem B2374375 : Blo 2109435 2374375 := bstep (se 1 (by rfl) ⟨1780781, by rfl⟩ : syracuseStep 2374375 = 3561563) B3561563
theorem B3165833 : Blo 2109435 3165833 := bstep (se 2 (by rfl) ⟨1187187, by rfl⟩ : syracuseStep 3165833 = 2374375) B2374375
theorem B2110555 : Blo 2109435 2110555 := bstep (se 1 (by rfl) ⟨1582916, by rfl⟩ : syracuseStep 2110555 = 3165833) B3165833
theorem B10684709 : Blo 2109435 10684709 := bbase (se 4 (by rfl) ⟨1001691, by rfl⟩ : syracuseStep 10684709 = 2003383) (by norm_num)
theorem B7123139 : Blo 2109435 7123139 := bstep (se 1 (by rfl) ⟨5342354, by rfl⟩ : syracuseStep 7123139 = 10684709) B10684709
theorem B4748759 : Blo 2109435 4748759 := bstep (se 1 (by rfl) ⟨3561569, by rfl⟩ : syracuseStep 4748759 = 7123139) B7123139
theorem B3165839 : Blo 2109435 3165839 := bstep (se 1 (by rfl) ⟨2374379, by rfl⟩ : syracuseStep 3165839 = 4748759) B4748759
theorem B2110559 : Blo 2109435 2110559 := bstep (se 1 (by rfl) ⟨1582919, by rfl⟩ : syracuseStep 2110559 = 3165839) B3165839
theorem B3165845 : Blo 2109435 3165845 := bbase (se 6 (by rfl) ⟨74199, by rfl⟩ : syracuseStep 3165845 = 148399) (by norm_num)
theorem B2110563 : Blo 2109435 2110563 := bstep (se 1 (by rfl) ⟨1582922, by rfl⟩ : syracuseStep 2110563 = 3165845) B3165845
theorem B3855205 : Blo 2109435 3855205 := bbase (se 4 (by rfl) ⟨361425, by rfl⟩ : syracuseStep 3855205 = 722851) (by norm_num)
theorem B5140273 : Blo 2109435 5140273 := bstep (se 2 (by rfl) ⟨1927602, by rfl⟩ : syracuseStep 5140273 = 3855205) B3855205
theorem B6853697 : Blo 2109435 6853697 := bstep (se 2 (by rfl) ⟨2570136, by rfl⟩ : syracuseStep 6853697 = 5140273) B5140273
theorem B4569131 : Blo 2109435 4569131 := bstep (se 1 (by rfl) ⟨3426848, by rfl⟩ : syracuseStep 4569131 = 6853697) B6853697
theorem B3046087 : Blo 2109435 3046087 := bstep (se 1 (by rfl) ⟨2284565, by rfl⟩ : syracuseStep 3046087 = 4569131) B4569131
theorem B4061449 : Blo 2109435 4061449 := bstep (se 2 (by rfl) ⟨1523043, by rfl⟩ : syracuseStep 4061449 = 3046087) B3046087
theorem B5415265 : Blo 2109435 5415265 := bstep (se 2 (by rfl) ⟨2030724, by rfl⟩ : syracuseStep 5415265 = 4061449) B4061449
theorem B7220353 : Blo 2109435 7220353 := bstep (se 2 (by rfl) ⟨2707632, by rfl⟩ : syracuseStep 7220353 = 5415265) B5415265
theorem B9627137 : Blo 2109435 9627137 := bstep (se 2 (by rfl) ⟨3610176, by rfl⟩ : syracuseStep 9627137 = 7220353) B7220353
theorem B6418091 : Blo 2109435 6418091 := bstep (se 1 (by rfl) ⟨4813568, by rfl⟩ : syracuseStep 6418091 = 9627137) B9627137
theorem B4278727 : Blo 2109435 4278727 := bstep (se 1 (by rfl) ⟨3209045, by rfl⟩ : syracuseStep 4278727 = 6418091) B6418091
theorem B22819877 : Blo 2109435 22819877 := bstep (se 4 (by rfl) ⟨2139363, by rfl⟩ : syracuseStep 22819877 = 4278727) B4278727
theorem B15213251 : Blo 2109435 15213251 := bstep (se 1 (by rfl) ⟨11409938, by rfl⟩ : syracuseStep 15213251 = 22819877) B22819877
theorem B10142167 : Blo 2109435 10142167 := bstep (se 1 (by rfl) ⟨7606625, by rfl⟩ : syracuseStep 10142167 = 15213251) B15213251
theorem B13522889 : Blo 2109435 13522889 := bstep (se 2 (by rfl) ⟨5071083, by rfl⟩ : syracuseStep 13522889 = 10142167) B10142167
theorem B9015259 : Blo 2109435 9015259 := bstep (se 1 (by rfl) ⟨6761444, by rfl⟩ : syracuseStep 9015259 = 13522889) B13522889
theorem B12020345 : Blo 2109435 12020345 := bstep (se 2 (by rfl) ⟨4507629, by rfl⟩ : syracuseStep 12020345 = 9015259) B9015259
theorem B8013563 : Blo 2109435 8013563 := bstep (se 1 (by rfl) ⟨6010172, by rfl⟩ : syracuseStep 8013563 = 12020345) B12020345
theorem B5342375 : Blo 2109435 5342375 := bstep (se 1 (by rfl) ⟨4006781, by rfl⟩ : syracuseStep 5342375 = 8013563) B8013563
theorem B3561583 : Blo 2109435 3561583 := bstep (se 1 (by rfl) ⟨2671187, by rfl⟩ : syracuseStep 3561583 = 5342375) B5342375
theorem B4748777 : Blo 2109435 4748777 := bstep (se 2 (by rfl) ⟨1780791, by rfl⟩ : syracuseStep 4748777 = 3561583) B3561583
theorem B3165851 : Blo 2109435 3165851 := bstep (se 1 (by rfl) ⟨2374388, by rfl⟩ : syracuseStep 3165851 = 4748777) B4748777
theorem B2110567 : Blo 2109435 2110567 := bstep (se 1 (by rfl) ⟨1582925, by rfl⟩ : syracuseStep 2110567 = 3165851) B3165851
theorem B2374393 : Blo 2109435 2374393 := bbase (se 2 (by rfl) ⟨890397, by rfl⟩ : syracuseStep 2374393 = 1780795) (by norm_num)
theorem B3165857 : Blo 2109435 3165857 := bstep (se 2 (by rfl) ⟨1187196, by rfl⟩ : syracuseStep 3165857 = 2374393) B2374393
theorem B2110571 : Blo 2109435 2110571 := bstep (se 1 (by rfl) ⟨1582928, by rfl⟩ : syracuseStep 2110571 = 3165857) B3165857
theorem B86644565 : Blo 2109435 86644565 := bbase (se 9 (by rfl) ⟨253841, by rfl⟩ : syracuseStep 86644565 = 507683) (by norm_num)
theorem B57763043 : Blo 2109435 57763043 := bstep (se 1 (by rfl) ⟨43322282, by rfl⟩ : syracuseStep 57763043 = 86644565) B86644565
theorem B38508695 : Blo 2109435 38508695 := bstep (se 1 (by rfl) ⟨28881521, by rfl⟩ : syracuseStep 38508695 = 57763043) B57763043
theorem B25672463 : Blo 2109435 25672463 := bstep (se 1 (by rfl) ⟨19254347, by rfl⟩ : syracuseStep 25672463 = 38508695) B38508695
theorem B17114975 : Blo 2109435 17114975 := bstep (se 1 (by rfl) ⟨12836231, by rfl⟩ : syracuseStep 17114975 = 25672463) B25672463
theorem B11409983 : Blo 2109435 11409983 := bstep (se 1 (by rfl) ⟨8557487, by rfl⟩ : syracuseStep 11409983 = 17114975) B17114975
theorem B7606655 : Blo 2109435 7606655 := bstep (se 1 (by rfl) ⟨5704991, by rfl⟩ : syracuseStep 7606655 = 11409983) B11409983
theorem B5071103 : Blo 2109435 5071103 := bstep (se 1 (by rfl) ⟨3803327, by rfl⟩ : syracuseStep 5071103 = 7606655) B7606655
theorem B3380735 : Blo 2109435 3380735 := bstep (se 1 (by rfl) ⟨2535551, by rfl⟩ : syracuseStep 3380735 = 5071103) B5071103
theorem B9015293 : Blo 2109435 9015293 := bstep (se 3 (by rfl) ⟨1690367, by rfl⟩ : syracuseStep 9015293 = 3380735) B3380735
theorem B6010195 : Blo 2109435 6010195 := bstep (se 1 (by rfl) ⟨4507646, by rfl⟩ : syracuseStep 6010195 = 9015293) B9015293
theorem B8013593 : Blo 2109435 8013593 := bstep (se 2 (by rfl) ⟨3005097, by rfl⟩ : syracuseStep 8013593 = 6010195) B6010195
theorem B5342395 : Blo 2109435 5342395 := bstep (se 1 (by rfl) ⟨4006796, by rfl⟩ : syracuseStep 5342395 = 8013593) B8013593
theorem B7123193 : Blo 2109435 7123193 := bstep (se 2 (by rfl) ⟨2671197, by rfl⟩ : syracuseStep 7123193 = 5342395) B5342395
theorem B4748795 : Blo 2109435 4748795 := bstep (se 1 (by rfl) ⟨3561596, by rfl⟩ : syracuseStep 4748795 = 7123193) B7123193
theorem B3165863 : Blo 2109435 3165863 := bstep (se 1 (by rfl) ⟨2374397, by rfl⟩ : syracuseStep 3165863 = 4748795) B4748795
theorem B2110575 : Blo 2109435 2110575 := bstep (se 1 (by rfl) ⟨1582931, by rfl⟩ : syracuseStep 2110575 = 3165863) B3165863
theorem B3165869 : Blo 2109435 3165869 := bbase (se 3 (by rfl) ⟨593600, by rfl⟩ : syracuseStep 3165869 = 1187201) (by norm_num)
theorem B2110579 : Blo 2109435 2110579 := bstep (se 1 (by rfl) ⟨1582934, by rfl⟩ : syracuseStep 2110579 = 3165869) B3165869
theorem B4748813 : Blo 2109435 4748813 := bbase (se 3 (by rfl) ⟨890402, by rfl⟩ : syracuseStep 4748813 = 1780805) (by norm_num)
theorem B3165875 : Blo 2109435 3165875 := bstep (se 1 (by rfl) ⟨2374406, by rfl⟩ : syracuseStep 3165875 = 4748813) B4748813
theorem B2110583 : Blo 2109435 2110583 := bstep (se 1 (by rfl) ⟨1582937, by rfl⟩ : syracuseStep 2110583 = 3165875) B3165875
theorem B2671213 : Blo 2109435 2671213 := bbase (se 3 (by rfl) ⟨500852, by rfl⟩ : syracuseStep 2671213 = 1001705) (by norm_num)
theorem B3561617 : Blo 2109435 3561617 := bstep (se 2 (by rfl) ⟨1335606, by rfl⟩ : syracuseStep 3561617 = 2671213) B2671213
theorem B2374411 : Blo 2109435 2374411 := bstep (se 1 (by rfl) ⟨1780808, by rfl⟩ : syracuseStep 2374411 = 3561617) B3561617
theorem B3165881 : Blo 2109435 3165881 := bstep (se 2 (by rfl) ⟨1187205, by rfl⟩ : syracuseStep 3165881 = 2374411) B2374411
theorem B2110587 : Blo 2109435 2110587 := bstep (se 1 (by rfl) ⟨1582940, by rfl⟩ : syracuseStep 2110587 = 3165881) B3165881
theorem B6505733 : Blo 2109435 6505733 := bbase (se 4 (by rfl) ⟨609912, by rfl⟩ : syracuseStep 6505733 = 1219825) (by norm_num)
theorem B4337155 : Blo 2109435 4337155 := bstep (se 1 (by rfl) ⟨3252866, by rfl⟩ : syracuseStep 4337155 = 6505733) B6505733
theorem B5782873 : Blo 2109435 5782873 := bstep (se 2 (by rfl) ⟨2168577, by rfl⟩ : syracuseStep 5782873 = 4337155) B4337155
theorem B7710497 : Blo 2109435 7710497 := bstep (se 2 (by rfl) ⟨2891436, by rfl⟩ : syracuseStep 7710497 = 5782873) B5782873
theorem B5140331 : Blo 2109435 5140331 := bstep (se 1 (by rfl) ⟨3855248, by rfl⟩ : syracuseStep 5140331 = 7710497) B7710497
theorem B3426887 : Blo 2109435 3426887 := bstep (se 1 (by rfl) ⟨2570165, by rfl⟩ : syracuseStep 3426887 = 5140331) B5140331
theorem B9138365 : Blo 2109435 9138365 := bstep (se 3 (by rfl) ⟨1713443, by rfl⟩ : syracuseStep 9138365 = 3426887) B3426887
theorem B6092243 : Blo 2109435 6092243 := bstep (se 1 (by rfl) ⟨4569182, by rfl⟩ : syracuseStep 6092243 = 9138365) B9138365
theorem B4061495 : Blo 2109435 4061495 := bstep (se 1 (by rfl) ⟨3046121, by rfl⟩ : syracuseStep 4061495 = 6092243) B6092243
theorem B2707663 : Blo 2109435 2707663 := bstep (se 1 (by rfl) ⟨2030747, by rfl⟩ : syracuseStep 2707663 = 4061495) B4061495
theorem B3610217 : Blo 2109435 3610217 := bstep (se 2 (by rfl) ⟨1353831, by rfl⟩ : syracuseStep 3610217 = 2707663) B2707663
theorem B9627245 : Blo 2109435 9627245 := bstep (se 3 (by rfl) ⟨1805108, by rfl⟩ : syracuseStep 9627245 = 3610217) B3610217
theorem B6418163 : Blo 2109435 6418163 := bstep (se 1 (by rfl) ⟨4813622, by rfl⟩ : syracuseStep 6418163 = 9627245) B9627245
theorem B17115101 : Blo 2109435 17115101 := bstep (se 3 (by rfl) ⟨3209081, by rfl⟩ : syracuseStep 17115101 = 6418163) B6418163
theorem B11410067 : Blo 2109435 11410067 := bstep (se 1 (by rfl) ⟨8557550, by rfl⟩ : syracuseStep 11410067 = 17115101) B17115101
theorem B7606711 : Blo 2109435 7606711 := bstep (se 1 (by rfl) ⟨5705033, by rfl⟩ : syracuseStep 7606711 = 11410067) B11410067
theorem B10142281 : Blo 2109435 10142281 := bstep (se 2 (by rfl) ⟨3803355, by rfl⟩ : syracuseStep 10142281 = 7606711) B7606711
theorem B13523041 : Blo 2109435 13523041 := bstep (se 2 (by rfl) ⟨5071140, by rfl⟩ : syracuseStep 13523041 = 10142281) B10142281
theorem B18030721 : Blo 2109435 18030721 := bstep (se 2 (by rfl) ⟨6761520, by rfl⟩ : syracuseStep 18030721 = 13523041) B13523041
theorem B24040961 : Blo 2109435 24040961 := bstep (se 2 (by rfl) ⟨9015360, by rfl⟩ : syracuseStep 24040961 = 18030721) B18030721
theorem B16027307 : Blo 2109435 16027307 := bstep (se 1 (by rfl) ⟨12020480, by rfl⟩ : syracuseStep 16027307 = 24040961) B24040961
theorem B10684871 : Blo 2109435 10684871 := bstep (se 1 (by rfl) ⟨8013653, by rfl⟩ : syracuseStep 10684871 = 16027307) B16027307
theorem B7123247 : Blo 2109435 7123247 := bstep (se 1 (by rfl) ⟨5342435, by rfl⟩ : syracuseStep 7123247 = 10684871) B10684871
theorem B4748831 : Blo 2109435 4748831 := bstep (se 1 (by rfl) ⟨3561623, by rfl⟩ : syracuseStep 4748831 = 7123247) B7123247
theorem B3165887 : Blo 2109435 3165887 := bstep (se 1 (by rfl) ⟨2374415, by rfl⟩ : syracuseStep 3165887 = 4748831) B4748831
theorem B2110591 : Blo 2109435 2110591 := bstep (se 1 (by rfl) ⟨1582943, by rfl⟩ : syracuseStep 2110591 = 3165887) B3165887
theorem B3165893 : Blo 2109435 3165893 := bbase (se 4 (by rfl) ⟨296802, by rfl⟩ : syracuseStep 3165893 = 593605) (by norm_num)
theorem B2110595 : Blo 2109435 2110595 := bstep (se 1 (by rfl) ⟨1582946, by rfl⟩ : syracuseStep 2110595 = 3165893) B3165893
theorem B3561637 : Blo 2109435 3561637 := bbase (se 4 (by rfl) ⟨333903, by rfl⟩ : syracuseStep 3561637 = 667807) (by norm_num)
theorem B4748849 : Blo 2109435 4748849 := bstep (se 2 (by rfl) ⟨1780818, by rfl⟩ : syracuseStep 4748849 = 3561637) B3561637
theorem B3165899 : Blo 2109435 3165899 := bstep (se 1 (by rfl) ⟨2374424, by rfl⟩ : syracuseStep 3165899 = 4748849) B4748849
theorem B2110599 : Blo 2109435 2110599 := bstep (se 1 (by rfl) ⟨1582949, by rfl⟩ : syracuseStep 2110599 = 3165899) B3165899
theorem B2374429 : Blo 2109435 2374429 := bbase (se 3 (by rfl) ⟨445205, by rfl⟩ : syracuseStep 2374429 = 890411) (by norm_num)
theorem B3165905 : Blo 2109435 3165905 := bstep (se 2 (by rfl) ⟨1187214, by rfl⟩ : syracuseStep 3165905 = 2374429) B2374429
theorem B2110603 : Blo 2109435 2110603 := bstep (se 1 (by rfl) ⟨1582952, by rfl⟩ : syracuseStep 2110603 = 3165905) B3165905
theorem B7123301 : Blo 2109435 7123301 := bbase (se 4 (by rfl) ⟨667809, by rfl⟩ : syracuseStep 7123301 = 1335619) (by norm_num)
theorem B4748867 : Blo 2109435 4748867 := bstep (se 1 (by rfl) ⟨3561650, by rfl⟩ : syracuseStep 4748867 = 7123301) B7123301
theorem B3165911 : Blo 2109435 3165911 := bstep (se 1 (by rfl) ⟨2374433, by rfl⟩ : syracuseStep 3165911 = 4748867) B4748867
theorem B2110607 : Blo 2109435 2110607 := bstep (se 1 (by rfl) ⟨1582955, by rfl⟩ : syracuseStep 2110607 = 3165911) B3165911
theorem B3165917 : Blo 2109435 3165917 := bbase (se 3 (by rfl) ⟨593609, by rfl⟩ : syracuseStep 3165917 = 1187219) (by norm_num)
theorem B2110611 : Blo 2109435 2110611 := bstep (se 1 (by rfl) ⟨1582958, by rfl⟩ : syracuseStep 2110611 = 3165917) B3165917
theorem B4748885 : Blo 2109435 4748885 := bbase (se 8 (by rfl) ⟨27825, by rfl⟩ : syracuseStep 4748885 = 55651) (by norm_num)
theorem B3165923 : Blo 2109435 3165923 := bstep (se 1 (by rfl) ⟨2374442, by rfl⟩ : syracuseStep 3165923 = 4748885) B4748885
theorem B2110615 : Blo 2109435 2110615 := bstep (se 1 (by rfl) ⟨1582961, by rfl⟩ : syracuseStep 2110615 = 3165923) B3165923
theorem B4507741 : Blo 2109435 4507741 := bbase (se 3 (by rfl) ⟨845201, by rfl⟩ : syracuseStep 4507741 = 1690403) (by norm_num)
theorem B6010321 : Blo 2109435 6010321 := bstep (se 2 (by rfl) ⟨2253870, by rfl⟩ : syracuseStep 6010321 = 4507741) B4507741
theorem B8013761 : Blo 2109435 8013761 := bstep (se 2 (by rfl) ⟨3005160, by rfl⟩ : syracuseStep 8013761 = 6010321) B6010321
theorem B5342507 : Blo 2109435 5342507 := bstep (se 1 (by rfl) ⟨4006880, by rfl⟩ : syracuseStep 5342507 = 8013761) B8013761
theorem B3561671 : Blo 2109435 3561671 := bstep (se 1 (by rfl) ⟨2671253, by rfl⟩ : syracuseStep 3561671 = 5342507) B5342507
theorem B2374447 : Blo 2109435 2374447 := bstep (se 1 (by rfl) ⟨1780835, by rfl⟩ : syracuseStep 2374447 = 3561671) B3561671
theorem B3165929 : Blo 2109435 3165929 := bstep (se 2 (by rfl) ⟨1187223, by rfl⟩ : syracuseStep 3165929 = 2374447) B2374447
theorem B2110619 : Blo 2109435 2110619 := bstep (se 1 (by rfl) ⟨1582964, by rfl⟩ : syracuseStep 2110619 = 3165929) B3165929
theorem B15213653 : Blo 2109435 15213653 := bbase (se 8 (by rfl) ⟨89142, by rfl⟩ : syracuseStep 15213653 = 178285) (by norm_num)
theorem B10142435 : Blo 2109435 10142435 := bstep (se 1 (by rfl) ⟨7606826, by rfl⟩ : syracuseStep 10142435 = 15213653) B15213653
theorem B27046493 : Blo 2109435 27046493 := bstep (se 3 (by rfl) ⟨5071217, by rfl⟩ : syracuseStep 27046493 = 10142435) B10142435
theorem B18030995 : Blo 2109435 18030995 := bstep (se 1 (by rfl) ⟨13523246, by rfl⟩ : syracuseStep 18030995 = 27046493) B27046493
theorem B12020663 : Blo 2109435 12020663 := bstep (se 1 (by rfl) ⟨9015497, by rfl⟩ : syracuseStep 12020663 = 18030995) B18030995
theorem B8013775 : Blo 2109435 8013775 := bstep (se 1 (by rfl) ⟨6010331, by rfl⟩ : syracuseStep 8013775 = 12020663) B12020663
theorem B10685033 : Blo 2109435 10685033 := bstep (se 2 (by rfl) ⟨4006887, by rfl⟩ : syracuseStep 10685033 = 8013775) B8013775
theorem B7123355 : Blo 2109435 7123355 := bstep (se 1 (by rfl) ⟨5342516, by rfl⟩ : syracuseStep 7123355 = 10685033) B10685033
theorem B4748903 : Blo 2109435 4748903 := bstep (se 1 (by rfl) ⟨3561677, by rfl⟩ : syracuseStep 4748903 = 7123355) B7123355
theorem B3165935 : Blo 2109435 3165935 := bstep (se 1 (by rfl) ⟨2374451, by rfl⟩ : syracuseStep 3165935 = 4748903) B4748903
theorem B2110623 : Blo 2109435 2110623 := bstep (se 1 (by rfl) ⟨1582967, by rfl⟩ : syracuseStep 2110623 = 3165935) B3165935
theorem B3165941 : Blo 2109435 3165941 := bbase (se 5 (by rfl) ⟨148403, by rfl⟩ : syracuseStep 3165941 = 296807) (by norm_num)
theorem B2110627 : Blo 2109435 2110627 := bstep (se 1 (by rfl) ⟨1582970, by rfl⟩ : syracuseStep 2110627 = 3165941) B3165941
theorem B3803429 : Blo 2109435 3803429 := bbase (se 4 (by rfl) ⟨356571, by rfl⟩ : syracuseStep 3803429 = 713143) (by norm_num)
theorem B2535619 : Blo 2109435 2535619 := bstep (se 1 (by rfl) ⟨1901714, by rfl⟩ : syracuseStep 2535619 = 3803429) B3803429
theorem B3380825 : Blo 2109435 3380825 := bstep (se 2 (by rfl) ⟨1267809, by rfl⟩ : syracuseStep 3380825 = 2535619) B2535619
theorem B9015533 : Blo 2109435 9015533 := bstep (se 3 (by rfl) ⟨1690412, by rfl⟩ : syracuseStep 9015533 = 3380825) B3380825
theorem B6010355 : Blo 2109435 6010355 := bstep (se 1 (by rfl) ⟨4507766, by rfl⟩ : syracuseStep 6010355 = 9015533) B9015533
theorem B4006903 : Blo 2109435 4006903 := bstep (se 1 (by rfl) ⟨3005177, by rfl⟩ : syracuseStep 4006903 = 6010355) B6010355
theorem B5342537 : Blo 2109435 5342537 := bstep (se 2 (by rfl) ⟨2003451, by rfl⟩ : syracuseStep 5342537 = 4006903) B4006903
theorem B3561691 : Blo 2109435 3561691 := bstep (se 1 (by rfl) ⟨2671268, by rfl⟩ : syracuseStep 3561691 = 5342537) B5342537
theorem B4748921 : Blo 2109435 4748921 := bstep (se 2 (by rfl) ⟨1780845, by rfl⟩ : syracuseStep 4748921 = 3561691) B3561691
theorem B3165947 : Blo 2109435 3165947 := bstep (se 1 (by rfl) ⟨2374460, by rfl⟩ : syracuseStep 3165947 = 4748921) B4748921
theorem B2110631 : Blo 2109435 2110631 := bstep (se 1 (by rfl) ⟨1582973, by rfl⟩ : syracuseStep 2110631 = 3165947) B3165947
theorem B2374465 : Blo 2109435 2374465 := bbase (se 2 (by rfl) ⟨890424, by rfl⟩ : syracuseStep 2374465 = 1780849) (by norm_num)
theorem B3165953 : Blo 2109435 3165953 := bstep (se 2 (by rfl) ⟨1187232, by rfl⟩ : syracuseStep 3165953 = 2374465) B2374465
theorem B2110635 : Blo 2109435 2110635 := bstep (se 1 (by rfl) ⟨1582976, by rfl⟩ : syracuseStep 2110635 = 3165953) B3165953
theorem B5342557 : Blo 2109435 5342557 := bbase (se 3 (by rfl) ⟨1001729, by rfl⟩ : syracuseStep 5342557 = 2003459) (by norm_num)
theorem B7123409 : Blo 2109435 7123409 := bstep (se 2 (by rfl) ⟨2671278, by rfl⟩ : syracuseStep 7123409 = 5342557) B5342557
theorem B4748939 : Blo 2109435 4748939 := bstep (se 1 (by rfl) ⟨3561704, by rfl⟩ : syracuseStep 4748939 = 7123409) B7123409
theorem B3165959 : Blo 2109435 3165959 := bstep (se 1 (by rfl) ⟨2374469, by rfl⟩ : syracuseStep 3165959 = 4748939) B4748939
theorem B2110639 : Blo 2109435 2110639 := bstep (se 1 (by rfl) ⟨1582979, by rfl⟩ : syracuseStep 2110639 = 3165959) B3165959
theorem B3165965 : Blo 2109435 3165965 := bbase (se 3 (by rfl) ⟨593618, by rfl⟩ : syracuseStep 3165965 = 1187237) (by norm_num)
theorem B2110643 : Blo 2109435 2110643 := bstep (se 1 (by rfl) ⟨1582982, by rfl⟩ : syracuseStep 2110643 = 3165965) B3165965
theorem B4748957 : Blo 2109435 4748957 := bbase (se 3 (by rfl) ⟨890429, by rfl⟩ : syracuseStep 4748957 = 1780859) (by norm_num)
theorem B3165971 : Blo 2109435 3165971 := bstep (se 1 (by rfl) ⟨2374478, by rfl⟩ : syracuseStep 3165971 = 4748957) B4748957
theorem B2110647 : Blo 2109435 2110647 := bstep (se 1 (by rfl) ⟨1582985, by rfl⟩ : syracuseStep 2110647 = 3165971) B3165971
theorem B3561725 : Blo 2109435 3561725 := bbase (se 3 (by rfl) ⟨667823, by rfl⟩ : syracuseStep 3561725 = 1335647) (by norm_num)
theorem B2374483 : Blo 2109435 2374483 := bstep (se 1 (by rfl) ⟨1780862, by rfl⟩ : syracuseStep 2374483 = 3561725) B3561725
theorem B3165977 : Blo 2109435 3165977 := bstep (se 2 (by rfl) ⟨1187241, by rfl⟩ : syracuseStep 3165977 = 2374483) B2374483
theorem B2110651 : Blo 2109435 2110651 := bstep (se 1 (by rfl) ⟨1582988, by rfl⟩ : syracuseStep 2110651 = 3165977) B3165977
theorem B20561941 : Blo 2109435 20561941 := bbase (se 6 (by rfl) ⟨481920, by rfl⟩ : syracuseStep 20561941 = 963841) (by norm_num)
theorem B27415921 : Blo 2109435 27415921 := bstep (se 2 (by rfl) ⟨10280970, by rfl⟩ : syracuseStep 27415921 = 20561941) B20561941
theorem B36554561 : Blo 2109435 36554561 := bstep (se 2 (by rfl) ⟨13707960, by rfl⟩ : syracuseStep 36554561 = 27415921) B27415921
theorem B24369707 : Blo 2109435 24369707 := bstep (se 1 (by rfl) ⟨18277280, by rfl⟩ : syracuseStep 24369707 = 36554561) B36554561
theorem B64985885 : Blo 2109435 64985885 := bstep (se 3 (by rfl) ⟨12184853, by rfl⟩ : syracuseStep 64985885 = 24369707) B24369707
theorem B43323923 : Blo 2109435 43323923 := bstep (se 1 (by rfl) ⟨32492942, by rfl⟩ : syracuseStep 43323923 = 64985885) B64985885
theorem B28882615 : Blo 2109435 28882615 := bstep (se 1 (by rfl) ⟨21661961, by rfl⟩ : syracuseStep 28882615 = 43323923) B43323923
theorem B38510153 : Blo 2109435 38510153 := bstep (se 2 (by rfl) ⟨14441307, by rfl⟩ : syracuseStep 38510153 = 28882615) B28882615
theorem B25673435 : Blo 2109435 25673435 := bstep (se 1 (by rfl) ⟨19255076, by rfl⟩ : syracuseStep 25673435 = 38510153) B38510153
theorem B17115623 : Blo 2109435 17115623 := bstep (se 1 (by rfl) ⟨12836717, by rfl⟩ : syracuseStep 17115623 = 25673435) B25673435
theorem B11410415 : Blo 2109435 11410415 := bstep (se 1 (by rfl) ⟨8557811, by rfl⟩ : syracuseStep 11410415 = 17115623) B17115623
theorem B7606943 : Blo 2109435 7606943 := bstep (se 1 (by rfl) ⟨5705207, by rfl⟩ : syracuseStep 7606943 = 11410415) B11410415
theorem B5071295 : Blo 2109435 5071295 := bstep (se 1 (by rfl) ⟨3803471, by rfl⟩ : syracuseStep 5071295 = 7606943) B7606943
theorem B3380863 : Blo 2109435 3380863 := bstep (se 1 (by rfl) ⟨2535647, by rfl⟩ : syracuseStep 3380863 = 5071295) B5071295
theorem B4507817 : Blo 2109435 4507817 := bstep (se 2 (by rfl) ⟨1690431, by rfl⟩ : syracuseStep 4507817 = 3380863) B3380863
theorem B12020845 : Blo 2109435 12020845 := bstep (se 3 (by rfl) ⟨2253908, by rfl⟩ : syracuseStep 12020845 = 4507817) B4507817
theorem B16027793 : Blo 2109435 16027793 := bstep (se 2 (by rfl) ⟨6010422, by rfl⟩ : syracuseStep 16027793 = 12020845) B12020845
theorem B10685195 : Blo 2109435 10685195 := bstep (se 1 (by rfl) ⟨8013896, by rfl⟩ : syracuseStep 10685195 = 16027793) B16027793
theorem B7123463 : Blo 2109435 7123463 := bstep (se 1 (by rfl) ⟨5342597, by rfl⟩ : syracuseStep 7123463 = 10685195) B10685195
theorem B4748975 : Blo 2109435 4748975 := bstep (se 1 (by rfl) ⟨3561731, by rfl⟩ : syracuseStep 4748975 = 7123463) B7123463
theorem B3165983 : Blo 2109435 3165983 := bstep (se 1 (by rfl) ⟨2374487, by rfl⟩ : syracuseStep 3165983 = 4748975) B4748975
theorem B2110655 : Blo 2109435 2110655 := bstep (se 1 (by rfl) ⟨1582991, by rfl⟩ : syracuseStep 2110655 = 3165983) B3165983
theorem B3165989 : Blo 2109435 3165989 := bbase (se 4 (by rfl) ⟨296811, by rfl⟩ : syracuseStep 3165989 = 593623) (by norm_num)
theorem B2110659 : Blo 2109435 2110659 := bstep (se 1 (by rfl) ⟨1582994, by rfl⟩ : syracuseStep 2110659 = 3165989) B3165989
theorem B2671309 : Blo 2109435 2671309 := bbase (se 3 (by rfl) ⟨500870, by rfl⟩ : syracuseStep 2671309 = 1001741) (by norm_num)
theorem B3561745 : Blo 2109435 3561745 := bstep (se 2 (by rfl) ⟨1335654, by rfl⟩ : syracuseStep 3561745 = 2671309) B2671309
theorem B4748993 : Blo 2109435 4748993 := bstep (se 2 (by rfl) ⟨1780872, by rfl⟩ : syracuseStep 4748993 = 3561745) B3561745
theorem B3165995 : Blo 2109435 3165995 := bstep (se 1 (by rfl) ⟨2374496, by rfl⟩ : syracuseStep 3165995 = 4748993) B4748993
theorem B2110663 : Blo 2109435 2110663 := bstep (se 1 (by rfl) ⟨1582997, by rfl⟩ : syracuseStep 2110663 = 3165995) B3165995
theorem B2374501 : Blo 2109435 2374501 := bbase (se 4 (by rfl) ⟨222609, by rfl⟩ : syracuseStep 2374501 = 445219) (by norm_num)
theorem B3166001 : Blo 2109435 3166001 := bstep (se 2 (by rfl) ⟨1187250, by rfl⟩ : syracuseStep 3166001 = 2374501) B2374501
theorem B2110667 : Blo 2109435 2110667 := bstep (se 1 (by rfl) ⟨1583000, by rfl⟩ : syracuseStep 2110667 = 3166001) B3166001
theorem B6010469 : Blo 2109435 6010469 := bbase (se 4 (by rfl) ⟨563481, by rfl⟩ : syracuseStep 6010469 = 1126963) (by norm_num)
theorem B4006979 : Blo 2109435 4006979 := bstep (se 1 (by rfl) ⟨3005234, by rfl⟩ : syracuseStep 4006979 = 6010469) B6010469
theorem B2671319 : Blo 2109435 2671319 := bstep (se 1 (by rfl) ⟨2003489, by rfl⟩ : syracuseStep 2671319 = 4006979) B4006979
theorem B7123517 : Blo 2109435 7123517 := bstep (se 3 (by rfl) ⟨1335659, by rfl⟩ : syracuseStep 7123517 = 2671319) B2671319
theorem B4749011 : Blo 2109435 4749011 := bstep (se 1 (by rfl) ⟨3561758, by rfl⟩ : syracuseStep 4749011 = 7123517) B7123517
theorem B3166007 : Blo 2109435 3166007 := bstep (se 1 (by rfl) ⟨2374505, by rfl⟩ : syracuseStep 3166007 = 4749011) B4749011
theorem B2110671 : Blo 2109435 2110671 := bstep (se 1 (by rfl) ⟨1583003, by rfl⟩ : syracuseStep 2110671 = 3166007) B3166007
theorem B3166013 : Blo 2109435 3166013 := bbase (se 3 (by rfl) ⟨593627, by rfl⟩ : syracuseStep 3166013 = 1187255) (by norm_num)
theorem B2110675 : Blo 2109435 2110675 := bstep (se 1 (by rfl) ⟨1583006, by rfl⟩ : syracuseStep 2110675 = 3166013) B3166013
theorem B4749029 : Blo 2109435 4749029 := bbase (se 4 (by rfl) ⟨445221, by rfl⟩ : syracuseStep 4749029 = 890443) (by norm_num)
theorem B3166019 : Blo 2109435 3166019 := bstep (se 1 (by rfl) ⟨2374514, by rfl⟩ : syracuseStep 3166019 = 4749029) B4749029
theorem B2110679 : Blo 2109435 2110679 := bstep (se 1 (by rfl) ⟨1583009, by rfl⟩ : syracuseStep 2110679 = 3166019) B3166019
theorem B5342669 : Blo 2109435 5342669 := bbase (se 3 (by rfl) ⟨1001750, by rfl⟩ : syracuseStep 5342669 = 2003501) (by norm_num)
theorem B3561779 : Blo 2109435 3561779 := bstep (se 1 (by rfl) ⟨2671334, by rfl⟩ : syracuseStep 3561779 = 5342669) B5342669
theorem B2374519 : Blo 2109435 2374519 := bstep (se 1 (by rfl) ⟨1780889, by rfl⟩ : syracuseStep 2374519 = 3561779) B3561779
theorem B3166025 : Blo 2109435 3166025 := bstep (se 2 (by rfl) ⟨1187259, by rfl⟩ : syracuseStep 3166025 = 2374519) B2374519
theorem B2110683 : Blo 2109435 2110683 := bstep (se 1 (by rfl) ⟨1583012, by rfl⟩ : syracuseStep 2110683 = 3166025) B3166025
theorem B5071373 : Blo 2109435 5071373 := bbase (se 3 (by rfl) ⟨950882, by rfl⟩ : syracuseStep 5071373 = 1901765) (by norm_num)
theorem B3380915 : Blo 2109435 3380915 := bstep (se 1 (by rfl) ⟨2535686, by rfl⟩ : syracuseStep 3380915 = 5071373) B5071373
theorem B2253943 : Blo 2109435 2253943 := bstep (se 1 (by rfl) ⟨1690457, by rfl⟩ : syracuseStep 2253943 = 3380915) B3380915
theorem B3005257 : Blo 2109435 3005257 := bstep (se 2 (by rfl) ⟨1126971, by rfl⟩ : syracuseStep 3005257 = 2253943) B2253943
theorem B4007009 : Blo 2109435 4007009 := bstep (se 2 (by rfl) ⟨1502628, by rfl⟩ : syracuseStep 4007009 = 3005257) B3005257
theorem B10685357 : Blo 2109435 10685357 := bstep (se 3 (by rfl) ⟨2003504, by rfl⟩ : syracuseStep 10685357 = 4007009) B4007009
theorem B7123571 : Blo 2109435 7123571 := bstep (se 1 (by rfl) ⟨5342678, by rfl⟩ : syracuseStep 7123571 = 10685357) B10685357
theorem B4749047 : Blo 2109435 4749047 := bstep (se 1 (by rfl) ⟨3561785, by rfl⟩ : syracuseStep 4749047 = 7123571) B7123571
theorem B3166031 : Blo 2109435 3166031 := bstep (se 1 (by rfl) ⟨2374523, by rfl⟩ : syracuseStep 3166031 = 4749047) B4749047
theorem B2110687 : Blo 2109435 2110687 := bstep (se 1 (by rfl) ⟨1583015, by rfl⟩ : syracuseStep 2110687 = 3166031) B3166031
theorem B3166037 : Blo 2109435 3166037 := bbase (se 9 (by rfl) ⟨9275, by rfl⟩ : syracuseStep 3166037 = 18551) (by norm_num)
theorem B2110691 : Blo 2109435 2110691 := bstep (se 1 (by rfl) ⟨1583018, by rfl⟩ : syracuseStep 2110691 = 3166037) B3166037
theorem B2782189 : Blo 2109435 2782189 := bbase (se 3 (by rfl) ⟨521660, by rfl⟩ : syracuseStep 2782189 = 1043321) (by norm_num)
theorem B3709585 : Blo 2109435 3709585 := bstep (se 2 (by rfl) ⟨1391094, by rfl⟩ : syracuseStep 3709585 = 2782189) B2782189
theorem B4946113 : Blo 2109435 4946113 := bstep (se 2 (by rfl) ⟨1854792, by rfl⟩ : syracuseStep 4946113 = 3709585) B3709585
theorem B6594817 : Blo 2109435 6594817 := bstep (se 2 (by rfl) ⟨2473056, by rfl⟩ : syracuseStep 6594817 = 4946113) B4946113
theorem B8793089 : Blo 2109435 8793089 := bstep (se 2 (by rfl) ⟨3297408, by rfl⟩ : syracuseStep 8793089 = 6594817) B6594817
theorem B5862059 : Blo 2109435 5862059 := bstep (se 1 (by rfl) ⟨4396544, by rfl⟩ : syracuseStep 5862059 = 8793089) B8793089
theorem B3908039 : Blo 2109435 3908039 := bstep (se 1 (by rfl) ⟨2931029, by rfl⟩ : syracuseStep 3908039 = 5862059) B5862059
theorem B41685749 : Blo 2109435 41685749 := bstep (se 5 (by rfl) ⟨1954019, by rfl⟩ : syracuseStep 41685749 = 3908039) B3908039
theorem B27790499 : Blo 2109435 27790499 := bstep (se 1 (by rfl) ⟨20842874, by rfl⟩ : syracuseStep 27790499 = 41685749) B41685749
theorem B18526999 : Blo 2109435 18526999 := bstep (se 1 (by rfl) ⟨13895249, by rfl⟩ : syracuseStep 18526999 = 27790499) B27790499
theorem B24702665 : Blo 2109435 24702665 := bstep (se 2 (by rfl) ⟨9263499, by rfl⟩ : syracuseStep 24702665 = 18526999) B18526999
theorem B65873773 : Blo 2109435 65873773 := bstep (se 3 (by rfl) ⟨12351332, by rfl⟩ : syracuseStep 65873773 = 24702665) B24702665
theorem B87831697 : Blo 2109435 87831697 := bstep (se 2 (by rfl) ⟨32936886, by rfl⟩ : syracuseStep 87831697 = 65873773) B65873773
theorem B117108929 : Blo 2109435 117108929 := bstep (se 2 (by rfl) ⟨43915848, by rfl⟩ : syracuseStep 117108929 = 87831697) B87831697
theorem B78072619 : Blo 2109435 78072619 := bstep (se 1 (by rfl) ⟨58554464, by rfl⟩ : syracuseStep 78072619 = 117108929) B117108929
theorem B104096825 : Blo 2109435 104096825 := bstep (se 2 (by rfl) ⟨39036309, by rfl⟩ : syracuseStep 104096825 = 78072619) B78072619
theorem B69397883 : Blo 2109435 69397883 := bstep (se 1 (by rfl) ⟨52048412, by rfl⟩ : syracuseStep 69397883 = 104096825) B104096825
theorem B46265255 : Blo 2109435 46265255 := bstep (se 1 (by rfl) ⟨34698941, by rfl⟩ : syracuseStep 46265255 = 69397883) B69397883
theorem B30843503 : Blo 2109435 30843503 := bstep (se 1 (by rfl) ⟨23132627, by rfl⟩ : syracuseStep 30843503 = 46265255) B46265255
theorem B20562335 : Blo 2109435 20562335 := bstep (se 1 (by rfl) ⟨15421751, by rfl⟩ : syracuseStep 20562335 = 30843503) B30843503
theorem B13708223 : Blo 2109435 13708223 := bstep (se 1 (by rfl) ⟨10281167, by rfl⟩ : syracuseStep 13708223 = 20562335) B20562335
theorem B9138815 : Blo 2109435 9138815 := bstep (se 1 (by rfl) ⟨6854111, by rfl⟩ : syracuseStep 9138815 = 13708223) B13708223
theorem B6092543 : Blo 2109435 6092543 := bstep (se 1 (by rfl) ⟨4569407, by rfl⟩ : syracuseStep 6092543 = 9138815) B9138815
theorem B4061695 : Blo 2109435 4061695 := bstep (se 1 (by rfl) ⟨3046271, by rfl⟩ : syracuseStep 4061695 = 6092543) B6092543
theorem B5415593 : Blo 2109435 5415593 := bstep (se 2 (by rfl) ⟨2030847, by rfl⟩ : syracuseStep 5415593 = 4061695) B4061695
theorem B14441581 : Blo 2109435 14441581 := bstep (se 3 (by rfl) ⟨2707796, by rfl⟩ : syracuseStep 14441581 = 5415593) B5415593
theorem B77021765 : Blo 2109435 77021765 := bstep (se 4 (by rfl) ⟨7220790, by rfl⟩ : syracuseStep 77021765 = 14441581) B14441581
theorem B51347843 : Blo 2109435 51347843 := bstep (se 1 (by rfl) ⟨38510882, by rfl⟩ : syracuseStep 51347843 = 77021765) B77021765
theorem B34231895 : Blo 2109435 34231895 := bstep (se 1 (by rfl) ⟨25673921, by rfl⟩ : syracuseStep 34231895 = 51347843) B51347843
theorem B22821263 : Blo 2109435 22821263 := bstep (se 1 (by rfl) ⟨17115947, by rfl⟩ : syracuseStep 22821263 = 34231895) B34231895
theorem B15214175 : Blo 2109435 15214175 := bstep (se 1 (by rfl) ⟨11410631, by rfl⟩ : syracuseStep 15214175 = 22821263) B22821263
theorem B10142783 : Blo 2109435 10142783 := bstep (se 1 (by rfl) ⟨7607087, by rfl⟩ : syracuseStep 10142783 = 15214175) B15214175
theorem B6761855 : Blo 2109435 6761855 := bstep (se 1 (by rfl) ⟨5071391, by rfl⟩ : syracuseStep 6761855 = 10142783) B10142783
theorem B4507903 : Blo 2109435 4507903 := bstep (se 1 (by rfl) ⟨3380927, by rfl⟩ : syracuseStep 4507903 = 6761855) B6761855
theorem B6010537 : Blo 2109435 6010537 := bstep (se 2 (by rfl) ⟨2253951, by rfl⟩ : syracuseStep 6010537 = 4507903) B4507903
theorem B8014049 : Blo 2109435 8014049 := bstep (se 2 (by rfl) ⟨3005268, by rfl⟩ : syracuseStep 8014049 = 6010537) B6010537
theorem B5342699 : Blo 2109435 5342699 := bstep (se 1 (by rfl) ⟨4007024, by rfl⟩ : syracuseStep 5342699 = 8014049) B8014049
theorem B3561799 : Blo 2109435 3561799 := bstep (se 1 (by rfl) ⟨2671349, by rfl⟩ : syracuseStep 3561799 = 5342699) B5342699
theorem B4749065 : Blo 2109435 4749065 := bstep (se 2 (by rfl) ⟨1780899, by rfl⟩ : syracuseStep 4749065 = 3561799) B3561799
theorem B3166043 : Blo 2109435 3166043 := bstep (se 1 (by rfl) ⟨2374532, by rfl⟩ : syracuseStep 3166043 = 4749065) B4749065
theorem B2110695 : Blo 2109435 2110695 := bstep (se 1 (by rfl) ⟨1583021, by rfl⟩ : syracuseStep 2110695 = 3166043) B3166043
theorem B2374537 : Blo 2109435 2374537 := bbase (se 2 (by rfl) ⟨890451, by rfl⟩ : syracuseStep 2374537 = 1780903) (by norm_num)
theorem B3166049 : Blo 2109435 3166049 := bstep (se 2 (by rfl) ⟨1187268, by rfl⟩ : syracuseStep 3166049 = 2374537) B2374537
theorem B2110699 : Blo 2109435 2110699 := bstep (se 1 (by rfl) ⟨1583024, by rfl⟩ : syracuseStep 2110699 = 3166049) B3166049
theorem B65874005 : Blo 2109435 65874005 := bbase (se 8 (by rfl) ⟨385980, by rfl⟩ : syracuseStep 65874005 = 771961) (by norm_num)
theorem B43916003 : Blo 2109435 43916003 := bstep (se 1 (by rfl) ⟨32937002, by rfl⟩ : syracuseStep 43916003 = 65874005) B65874005
theorem B29277335 : Blo 2109435 29277335 := bstep (se 1 (by rfl) ⟨21958001, by rfl⟩ : syracuseStep 29277335 = 43916003) B43916003
theorem B78072893 : Blo 2109435 78072893 := bstep (se 3 (by rfl) ⟨14638667, by rfl⟩ : syracuseStep 78072893 = 29277335) B29277335
theorem B52048595 : Blo 2109435 52048595 := bstep (se 1 (by rfl) ⟨39036446, by rfl⟩ : syracuseStep 52048595 = 78072893) B78072893
theorem B34699063 : Blo 2109435 34699063 := bstep (se 1 (by rfl) ⟨26024297, by rfl⟩ : syracuseStep 34699063 = 52048595) B52048595
theorem B46265417 : Blo 2109435 46265417 := bstep (se 2 (by rfl) ⟨17349531, by rfl⟩ : syracuseStep 46265417 = 34699063) B34699063
theorem B30843611 : Blo 2109435 30843611 := bstep (se 1 (by rfl) ⟨23132708, by rfl⟩ : syracuseStep 30843611 = 46265417) B46265417
theorem B20562407 : Blo 2109435 20562407 := bstep (se 1 (by rfl) ⟨15421805, by rfl⟩ : syracuseStep 20562407 = 30843611) B30843611
theorem B13708271 : Blo 2109435 13708271 := bstep (se 1 (by rfl) ⟨10281203, by rfl⟩ : syracuseStep 13708271 = 20562407) B20562407
theorem B9138847 : Blo 2109435 9138847 := bstep (se 1 (by rfl) ⟨6854135, by rfl⟩ : syracuseStep 9138847 = 13708271) B13708271
theorem B12185129 : Blo 2109435 12185129 := bstep (se 2 (by rfl) ⟨4569423, by rfl⟩ : syracuseStep 12185129 = 9138847) B9138847
theorem B8123419 : Blo 2109435 8123419 := bstep (se 1 (by rfl) ⟨6092564, by rfl⟩ : syracuseStep 8123419 = 12185129) B12185129
theorem B10831225 : Blo 2109435 10831225 := bstep (se 2 (by rfl) ⟨4061709, by rfl⟩ : syracuseStep 10831225 = 8123419) B8123419
theorem B14441633 : Blo 2109435 14441633 := bstep (se 2 (by rfl) ⟨5415612, by rfl⟩ : syracuseStep 14441633 = 10831225) B10831225
theorem B9627755 : Blo 2109435 9627755 := bstep (se 1 (by rfl) ⟨7220816, by rfl⟩ : syracuseStep 9627755 = 14441633) B14441633
theorem B25674013 : Blo 2109435 25674013 := bstep (se 3 (by rfl) ⟨4813877, by rfl⟩ : syracuseStep 25674013 = 9627755) B9627755
theorem B136928069 : Blo 2109435 136928069 := bstep (se 4 (by rfl) ⟨12837006, by rfl⟩ : syracuseStep 136928069 = 25674013) B25674013
theorem B91285379 : Blo 2109435 91285379 := bstep (se 1 (by rfl) ⟨68464034, by rfl⟩ : syracuseStep 91285379 = 136928069) B136928069
theorem B60856919 : Blo 2109435 60856919 := bstep (se 1 (by rfl) ⟨45642689, by rfl⟩ : syracuseStep 60856919 = 91285379) B91285379
theorem B40571279 : Blo 2109435 40571279 := bstep (se 1 (by rfl) ⟨30428459, by rfl⟩ : syracuseStep 40571279 = 60856919) B60856919
theorem B27047519 : Blo 2109435 27047519 := bstep (se 1 (by rfl) ⟨20285639, by rfl⟩ : syracuseStep 27047519 = 40571279) B40571279
theorem B18031679 : Blo 2109435 18031679 := bstep (se 1 (by rfl) ⟨13523759, by rfl⟩ : syracuseStep 18031679 = 27047519) B27047519
theorem B12021119 : Blo 2109435 12021119 := bstep (se 1 (by rfl) ⟨9015839, by rfl⟩ : syracuseStep 12021119 = 18031679) B18031679
theorem B8014079 : Blo 2109435 8014079 := bstep (se 1 (by rfl) ⟨6010559, by rfl⟩ : syracuseStep 8014079 = 12021119) B12021119
theorem B5342719 : Blo 2109435 5342719 := bstep (se 1 (by rfl) ⟨4007039, by rfl⟩ : syracuseStep 5342719 = 8014079) B8014079
theorem B7123625 : Blo 2109435 7123625 := bstep (se 2 (by rfl) ⟨2671359, by rfl⟩ : syracuseStep 7123625 = 5342719) B5342719
theorem B4749083 : Blo 2109435 4749083 := bstep (se 1 (by rfl) ⟨3561812, by rfl⟩ : syracuseStep 4749083 = 7123625) B7123625
theorem B3166055 : Blo 2109435 3166055 := bstep (se 1 (by rfl) ⟨2374541, by rfl⟩ : syracuseStep 3166055 = 4749083) B4749083
theorem B2110703 : Blo 2109435 2110703 := bstep (se 1 (by rfl) ⟨1583027, by rfl⟩ : syracuseStep 2110703 = 3166055) B3166055
theorem B3166061 : Blo 2109435 3166061 := bbase (se 3 (by rfl) ⟨593636, by rfl⟩ : syracuseStep 3166061 = 1187273) (by norm_num)
theorem B2110707 : Blo 2109435 2110707 := bstep (se 1 (by rfl) ⟨1583030, by rfl⟩ : syracuseStep 2110707 = 3166061) B3166061
theorem B4749101 : Blo 2109435 4749101 := bbase (se 3 (by rfl) ⟨890456, by rfl⟩ : syracuseStep 4749101 = 1780913) (by norm_num)
theorem B3166067 : Blo 2109435 3166067 := bstep (se 1 (by rfl) ⟨2374550, by rfl⟩ : syracuseStep 3166067 = 4749101) B4749101
theorem B2110711 : Blo 2109435 2110711 := bstep (se 1 (by rfl) ⟨1583033, by rfl⟩ : syracuseStep 2110711 = 3166067) B3166067
theorem B9015893 : Blo 2109435 9015893 := bbase (se 8 (by rfl) ⟨52827, by rfl⟩ : syracuseStep 9015893 = 105655) (by norm_num)
theorem B6010595 : Blo 2109435 6010595 := bstep (se 1 (by rfl) ⟨4507946, by rfl⟩ : syracuseStep 6010595 = 9015893) B9015893
theorem B4007063 : Blo 2109435 4007063 := bstep (se 1 (by rfl) ⟨3005297, by rfl⟩ : syracuseStep 4007063 = 6010595) B6010595
theorem B2671375 : Blo 2109435 2671375 := bstep (se 1 (by rfl) ⟨2003531, by rfl⟩ : syracuseStep 2671375 = 4007063) B4007063
theorem B3561833 : Blo 2109435 3561833 := bstep (se 2 (by rfl) ⟨1335687, by rfl⟩ : syracuseStep 3561833 = 2671375) B2671375
theorem B2374555 : Blo 2109435 2374555 := bstep (se 1 (by rfl) ⟨1780916, by rfl⟩ : syracuseStep 2374555 = 3561833) B3561833
theorem B3166073 : Blo 2109435 3166073 := bstep (se 2 (by rfl) ⟨1187277, by rfl⟩ : syracuseStep 3166073 = 2374555) B2374555
theorem B2110715 : Blo 2109435 2110715 := bstep (se 1 (by rfl) ⟨1583036, by rfl⟩ : syracuseStep 2110715 = 3166073) B3166073
theorem B13523861 : Blo 2109435 13523861 := bbase (se 6 (by rfl) ⟨316965, by rfl⟩ : syracuseStep 13523861 = 633931) (by norm_num)
theorem B36063629 : Blo 2109435 36063629 := bstep (se 3 (by rfl) ⟨6761930, by rfl⟩ : syracuseStep 36063629 = 13523861) B13523861
theorem B24042419 : Blo 2109435 24042419 := bstep (se 1 (by rfl) ⟨18031814, by rfl⟩ : syracuseStep 24042419 = 36063629) B36063629
theorem B16028279 : Blo 2109435 16028279 := bstep (se 1 (by rfl) ⟨12021209, by rfl⟩ : syracuseStep 16028279 = 24042419) B24042419
theorem B10685519 : Blo 2109435 10685519 := bstep (se 1 (by rfl) ⟨8014139, by rfl⟩ : syracuseStep 10685519 = 16028279) B16028279
theorem B7123679 : Blo 2109435 7123679 := bstep (se 1 (by rfl) ⟨5342759, by rfl⟩ : syracuseStep 7123679 = 10685519) B10685519
theorem B4749119 : Blo 2109435 4749119 := bstep (se 1 (by rfl) ⟨3561839, by rfl⟩ : syracuseStep 4749119 = 7123679) B7123679
theorem B3166079 : Blo 2109435 3166079 := bstep (se 1 (by rfl) ⟨2374559, by rfl⟩ : syracuseStep 3166079 = 4749119) B4749119
theorem B2110719 : Blo 2109435 2110719 := bstep (se 1 (by rfl) ⟨1583039, by rfl⟩ : syracuseStep 2110719 = 3166079) B3166079
theorem B3166085 : Blo 2109435 3166085 := bbase (se 4 (by rfl) ⟨296820, by rfl⟩ : syracuseStep 3166085 = 593641) (by norm_num)
theorem B2110723 : Blo 2109435 2110723 := bstep (se 1 (by rfl) ⟨1583042, by rfl⟩ : syracuseStep 2110723 = 3166085) B3166085
theorem B3561853 : Blo 2109435 3561853 := bbase (se 3 (by rfl) ⟨667847, by rfl⟩ : syracuseStep 3561853 = 1335695) (by norm_num)
theorem B4749137 : Blo 2109435 4749137 := bstep (se 2 (by rfl) ⟨1780926, by rfl⟩ : syracuseStep 4749137 = 3561853) B3561853
theorem B3166091 : Blo 2109435 3166091 := bstep (se 1 (by rfl) ⟨2374568, by rfl⟩ : syracuseStep 3166091 = 4749137) B4749137
theorem B2110727 : Blo 2109435 2110727 := bstep (se 1 (by rfl) ⟨1583045, by rfl⟩ : syracuseStep 2110727 = 3166091) B3166091
theorem B2374573 : Blo 2109435 2374573 := bbase (se 3 (by rfl) ⟨445232, by rfl⟩ : syracuseStep 2374573 = 890465) (by norm_num)
theorem B3166097 : Blo 2109435 3166097 := bstep (se 2 (by rfl) ⟨1187286, by rfl⟩ : syracuseStep 3166097 = 2374573) B2374573
theorem B2110731 : Blo 2109435 2110731 := bstep (se 1 (by rfl) ⟨1583048, by rfl⟩ : syracuseStep 2110731 = 3166097) B3166097
theorem B7123733 : Blo 2109435 7123733 := bbase (se 6 (by rfl) ⟨166962, by rfl⟩ : syracuseStep 7123733 = 333925) (by norm_num)
theorem B4749155 : Blo 2109435 4749155 := bstep (se 1 (by rfl) ⟨3561866, by rfl⟩ : syracuseStep 4749155 = 7123733) B7123733
theorem B3166103 : Blo 2109435 3166103 := bstep (se 1 (by rfl) ⟨2374577, by rfl⟩ : syracuseStep 3166103 = 4749155) B4749155
theorem B2110735 : Blo 2109435 2110735 := bstep (se 1 (by rfl) ⟨1583051, by rfl⟩ : syracuseStep 2110735 = 3166103) B3166103
theorem B3166109 : Blo 2109435 3166109 := bbase (se 3 (by rfl) ⟨593645, by rfl⟩ : syracuseStep 3166109 = 1187291) (by norm_num)
theorem B2110739 : Blo 2109435 2110739 := bstep (se 1 (by rfl) ⟨1583054, by rfl⟩ : syracuseStep 2110739 = 3166109) B3166109
theorem B4749173 : Blo 2109435 4749173 := bbase (se 5 (by rfl) ⟨222617, by rfl⟩ : syracuseStep 4749173 = 445235) (by norm_num)
theorem B3166115 : Blo 2109435 3166115 := bstep (se 1 (by rfl) ⟨2374586, by rfl⟩ : syracuseStep 3166115 = 4749173) B4749173
theorem B2110743 : Blo 2109435 2110743 := bstep (se 1 (by rfl) ⟨1583057, by rfl⟩ : syracuseStep 2110743 = 3166115) B3166115
theorem B15214549 : Blo 2109435 15214549 := bbase (se 7 (by rfl) ⟨178295, by rfl⟩ : syracuseStep 15214549 = 356591) (by norm_num)
theorem B20286065 : Blo 2109435 20286065 := bstep (se 2 (by rfl) ⟨7607274, by rfl⟩ : syracuseStep 20286065 = 15214549) B15214549
theorem B13524043 : Blo 2109435 13524043 := bstep (se 1 (by rfl) ⟨10143032, by rfl⟩ : syracuseStep 13524043 = 20286065) B20286065
theorem B18032057 : Blo 2109435 18032057 := bstep (se 2 (by rfl) ⟨6762021, by rfl⟩ : syracuseStep 18032057 = 13524043) B13524043
theorem B12021371 : Blo 2109435 12021371 := bstep (se 1 (by rfl) ⟨9016028, by rfl⟩ : syracuseStep 12021371 = 18032057) B18032057
theorem B8014247 : Blo 2109435 8014247 := bstep (se 1 (by rfl) ⟨6010685, by rfl⟩ : syracuseStep 8014247 = 12021371) B12021371
theorem B5342831 : Blo 2109435 5342831 := bstep (se 1 (by rfl) ⟨4007123, by rfl⟩ : syracuseStep 5342831 = 8014247) B8014247
theorem B3561887 : Blo 2109435 3561887 := bstep (se 1 (by rfl) ⟨2671415, by rfl⟩ : syracuseStep 3561887 = 5342831) B5342831
theorem B2374591 : Blo 2109435 2374591 := bstep (se 1 (by rfl) ⟨1780943, by rfl⟩ : syracuseStep 2374591 = 3561887) B3561887
theorem B3166121 : Blo 2109435 3166121 := bstep (se 2 (by rfl) ⟨1187295, by rfl⟩ : syracuseStep 3166121 = 2374591) B2374591
theorem B2110747 : Blo 2109435 2110747 := bstep (se 1 (by rfl) ⟨1583060, by rfl⟩ : syracuseStep 2110747 = 3166121) B3166121
theorem B8014261 : Blo 2109435 8014261 := bbase (se 5 (by rfl) ⟨375668, by rfl⟩ : syracuseStep 8014261 = 751337) (by norm_num)
theorem B10685681 : Blo 2109435 10685681 := bstep (se 2 (by rfl) ⟨4007130, by rfl⟩ : syracuseStep 10685681 = 8014261) B8014261
theorem B7123787 : Blo 2109435 7123787 := bstep (se 1 (by rfl) ⟨5342840, by rfl⟩ : syracuseStep 7123787 = 10685681) B10685681
theorem B4749191 : Blo 2109435 4749191 := bstep (se 1 (by rfl) ⟨3561893, by rfl⟩ : syracuseStep 4749191 = 7123787) B7123787
theorem B3166127 : Blo 2109435 3166127 := bstep (se 1 (by rfl) ⟨2374595, by rfl⟩ : syracuseStep 3166127 = 4749191) B4749191
theorem B2110751 : Blo 2109435 2110751 := bstep (se 1 (by rfl) ⟨1583063, by rfl⟩ : syracuseStep 2110751 = 3166127) B3166127
theorem B3166133 : Blo 2109435 3166133 := bbase (se 5 (by rfl) ⟨148412, by rfl⟩ : syracuseStep 3166133 = 296825) (by norm_num)
theorem B2110755 : Blo 2109435 2110755 := bstep (se 1 (by rfl) ⟨1583066, by rfl⟩ : syracuseStep 2110755 = 3166133) B3166133
theorem B5342861 : Blo 2109435 5342861 := bbase (se 3 (by rfl) ⟨1001786, by rfl⟩ : syracuseStep 5342861 = 2003573) (by norm_num)
theorem B3561907 : Blo 2109435 3561907 := bstep (se 1 (by rfl) ⟨2671430, by rfl⟩ : syracuseStep 3561907 = 5342861) B5342861
theorem B4749209 : Blo 2109435 4749209 := bstep (se 2 (by rfl) ⟨1780953, by rfl⟩ : syracuseStep 4749209 = 3561907) B3561907
theorem B3166139 : Blo 2109435 3166139 := bstep (se 1 (by rfl) ⟨2374604, by rfl⟩ : syracuseStep 3166139 = 4749209) B4749209
theorem B2110759 : Blo 2109435 2110759 := bstep (se 1 (by rfl) ⟨1583069, by rfl⟩ : syracuseStep 2110759 = 3166139) B3166139
theorem B2374609 : Blo 2109435 2374609 := bbase (se 2 (by rfl) ⟨890478, by rfl⟩ : syracuseStep 2374609 = 1780957) (by norm_num)
theorem B3166145 : Blo 2109435 3166145 := bstep (se 2 (by rfl) ⟨1187304, by rfl⟩ : syracuseStep 3166145 = 2374609) B2374609
theorem B2110763 : Blo 2109435 2110763 := bstep (se 1 (by rfl) ⟨1583072, by rfl⟩ : syracuseStep 2110763 = 3166145) B3166145
theorem B5071565 : Blo 2109435 5071565 := bbase (se 3 (by rfl) ⟨950918, by rfl⟩ : syracuseStep 5071565 = 1901837) (by norm_num)
theorem B3381043 : Blo 2109435 3381043 := bstep (se 1 (by rfl) ⟨2535782, by rfl⟩ : syracuseStep 3381043 = 5071565) B5071565
theorem B4508057 : Blo 2109435 4508057 := bstep (se 2 (by rfl) ⟨1690521, by rfl⟩ : syracuseStep 4508057 = 3381043) B3381043
theorem B3005371 : Blo 2109435 3005371 := bstep (se 1 (by rfl) ⟨2254028, by rfl⟩ : syracuseStep 3005371 = 4508057) B4508057
theorem B4007161 : Blo 2109435 4007161 := bstep (se 2 (by rfl) ⟨1502685, by rfl⟩ : syracuseStep 4007161 = 3005371) B3005371
theorem B5342881 : Blo 2109435 5342881 := bstep (se 2 (by rfl) ⟨2003580, by rfl⟩ : syracuseStep 5342881 = 4007161) B4007161
theorem B7123841 : Blo 2109435 7123841 := bstep (se 2 (by rfl) ⟨2671440, by rfl⟩ : syracuseStep 7123841 = 5342881) B5342881
theorem B4749227 : Blo 2109435 4749227 := bstep (se 1 (by rfl) ⟨3561920, by rfl⟩ : syracuseStep 4749227 = 7123841) B7123841
theorem B3166151 : Blo 2109435 3166151 := bstep (se 1 (by rfl) ⟨2374613, by rfl⟩ : syracuseStep 3166151 = 4749227) B4749227
theorem B2110767 : Blo 2109435 2110767 := bstep (se 1 (by rfl) ⟨1583075, by rfl⟩ : syracuseStep 2110767 = 3166151) B3166151
theorem B3166157 : Blo 2109435 3166157 := bbase (se 3 (by rfl) ⟨593654, by rfl⟩ : syracuseStep 3166157 = 1187309) (by norm_num)
theorem B2110771 : Blo 2109435 2110771 := bstep (se 1 (by rfl) ⟨1583078, by rfl⟩ : syracuseStep 2110771 = 3166157) B3166157
theorem B4749245 : Blo 2109435 4749245 := bbase (se 3 (by rfl) ⟨890483, by rfl⟩ : syracuseStep 4749245 = 1780967) (by norm_num)
theorem B3166163 : Blo 2109435 3166163 := bstep (se 1 (by rfl) ⟨2374622, by rfl⟩ : syracuseStep 3166163 = 4749245) B4749245
theorem B2110775 : Blo 2109435 2110775 := bstep (se 1 (by rfl) ⟨1583081, by rfl⟩ : syracuseStep 2110775 = 3166163) B3166163
theorem B3561941 : Blo 2109435 3561941 := bbase (se 7 (by rfl) ⟨41741, by rfl⟩ : syracuseStep 3561941 = 83483) (by norm_num)
theorem B2374627 : Blo 2109435 2374627 := bstep (se 1 (by rfl) ⟨1780970, by rfl⟩ : syracuseStep 2374627 = 3561941) B3561941
theorem B3166169 : Blo 2109435 3166169 := bstep (se 2 (by rfl) ⟨1187313, by rfl⟩ : syracuseStep 3166169 = 2374627) B2374627
theorem B2110779 : Blo 2109435 2110779 := bstep (se 1 (by rfl) ⟨1583084, by rfl⟩ : syracuseStep 2110779 = 3166169) B3166169
theorem B9016181 : Blo 2109435 9016181 := bbase (se 5 (by rfl) ⟨422633, by rfl⟩ : syracuseStep 9016181 = 845267) (by norm_num)
theorem B6010787 : Blo 2109435 6010787 := bstep (se 1 (by rfl) ⟨4508090, by rfl⟩ : syracuseStep 6010787 = 9016181) B9016181
theorem B16028765 : Blo 2109435 16028765 := bstep (se 3 (by rfl) ⟨3005393, by rfl⟩ : syracuseStep 16028765 = 6010787) B6010787
theorem B10685843 : Blo 2109435 10685843 := bstep (se 1 (by rfl) ⟨8014382, by rfl⟩ : syracuseStep 10685843 = 16028765) B16028765
theorem B7123895 : Blo 2109435 7123895 := bstep (se 1 (by rfl) ⟨5342921, by rfl⟩ : syracuseStep 7123895 = 10685843) B10685843
theorem B4749263 : Blo 2109435 4749263 := bstep (se 1 (by rfl) ⟨3561947, by rfl⟩ : syracuseStep 4749263 = 7123895) B7123895
theorem B3166175 : Blo 2109435 3166175 := bstep (se 1 (by rfl) ⟨2374631, by rfl⟩ : syracuseStep 3166175 = 4749263) B4749263
theorem B2110783 : Blo 2109435 2110783 := bstep (se 1 (by rfl) ⟨1583087, by rfl⟩ : syracuseStep 2110783 = 3166175) B3166175
theorem B3166181 : Blo 2109435 3166181 := bbase (se 4 (by rfl) ⟨296829, by rfl⟩ : syracuseStep 3166181 = 593659) (by norm_num)
theorem B2110787 : Blo 2109435 2110787 := bstep (se 1 (by rfl) ⟨1583090, by rfl⟩ : syracuseStep 2110787 = 3166181) B3166181
theorem B3803717 : Blo 2109435 3803717 := bbase (se 4 (by rfl) ⟨356598, by rfl⟩ : syracuseStep 3803717 = 713197) (by norm_num)
theorem B10143245 : Blo 2109435 10143245 := bstep (se 3 (by rfl) ⟨1901858, by rfl⟩ : syracuseStep 10143245 = 3803717) B3803717
theorem B6762163 : Blo 2109435 6762163 := bstep (se 1 (by rfl) ⟨5071622, by rfl⟩ : syracuseStep 6762163 = 10143245) B10143245
theorem B9016217 : Blo 2109435 9016217 := bstep (se 2 (by rfl) ⟨3381081, by rfl⟩ : syracuseStep 9016217 = 6762163) B6762163
theorem B6010811 : Blo 2109435 6010811 := bstep (se 1 (by rfl) ⟨4508108, by rfl⟩ : syracuseStep 6010811 = 9016217) B9016217
theorem B4007207 : Blo 2109435 4007207 := bstep (se 1 (by rfl) ⟨3005405, by rfl⟩ : syracuseStep 4007207 = 6010811) B6010811
theorem B2671471 : Blo 2109435 2671471 := bstep (se 1 (by rfl) ⟨2003603, by rfl⟩ : syracuseStep 2671471 = 4007207) B4007207
theorem B3561961 : Blo 2109435 3561961 := bstep (se 2 (by rfl) ⟨1335735, by rfl⟩ : syracuseStep 3561961 = 2671471) B2671471
theorem B4749281 : Blo 2109435 4749281 := bstep (se 2 (by rfl) ⟨1780980, by rfl⟩ : syracuseStep 4749281 = 3561961) B3561961
theorem B3166187 : Blo 2109435 3166187 := bstep (se 1 (by rfl) ⟨2374640, by rfl⟩ : syracuseStep 3166187 = 4749281) B4749281
theorem B2110791 : Blo 2109435 2110791 := bstep (se 1 (by rfl) ⟨1583093, by rfl⟩ : syracuseStep 2110791 = 3166187) B3166187
theorem B2374645 : Blo 2109435 2374645 := bbase (se 5 (by rfl) ⟨111311, by rfl⟩ : syracuseStep 2374645 = 222623) (by norm_num)
theorem B3166193 : Blo 2109435 3166193 := bstep (se 2 (by rfl) ⟨1187322, by rfl⟩ : syracuseStep 3166193 = 2374645) B2374645
theorem B2110795 : Blo 2109435 2110795 := bstep (se 1 (by rfl) ⟨1583096, by rfl⟩ : syracuseStep 2110795 = 3166193) B3166193
theorem B2671481 : Blo 2109435 2671481 := bbase (se 2 (by rfl) ⟨1001805, by rfl⟩ : syracuseStep 2671481 = 2003611) (by norm_num)
theorem B7123949 : Blo 2109435 7123949 := bstep (se 3 (by rfl) ⟨1335740, by rfl⟩ : syracuseStep 7123949 = 2671481) B2671481
theorem B4749299 : Blo 2109435 4749299 := bstep (se 1 (by rfl) ⟨3561974, by rfl⟩ : syracuseStep 4749299 = 7123949) B7123949
theorem B3166199 : Blo 2109435 3166199 := bstep (se 1 (by rfl) ⟨2374649, by rfl⟩ : syracuseStep 3166199 = 4749299) B4749299
theorem B2110799 : Blo 2109435 2110799 := bstep (se 1 (by rfl) ⟨1583099, by rfl⟩ : syracuseStep 2110799 = 3166199) B3166199
theorem B3166205 : Blo 2109435 3166205 := bbase (se 3 (by rfl) ⟨593663, by rfl⟩ : syracuseStep 3166205 = 1187327) (by norm_num)
theorem B2110803 : Blo 2109435 2110803 := bstep (se 1 (by rfl) ⟨1583102, by rfl⟩ : syracuseStep 2110803 = 3166205) B3166205
theorem B4749317 : Blo 2109435 4749317 := bbase (se 4 (by rfl) ⟨445248, by rfl⟩ : syracuseStep 4749317 = 890497) (by norm_num)
theorem B3166211 : Blo 2109435 3166211 := bstep (se 1 (by rfl) ⟨2374658, by rfl⟩ : syracuseStep 3166211 = 4749317) B4749317
theorem B2110807 : Blo 2109435 2110807 := bstep (se 1 (by rfl) ⟨1583105, by rfl⟩ : syracuseStep 2110807 = 3166211) B3166211
theorem B4007245 : Blo 2109435 4007245 := bbase (se 3 (by rfl) ⟨751358, by rfl⟩ : syracuseStep 4007245 = 1502717) (by norm_num)
theorem B5342993 : Blo 2109435 5342993 := bstep (se 2 (by rfl) ⟨2003622, by rfl⟩ : syracuseStep 5342993 = 4007245) B4007245
theorem B3561995 : Blo 2109435 3561995 := bstep (se 1 (by rfl) ⟨2671496, by rfl⟩ : syracuseStep 3561995 = 5342993) B5342993
theorem B2374663 : Blo 2109435 2374663 := bstep (se 1 (by rfl) ⟨1780997, by rfl⟩ : syracuseStep 2374663 = 3561995) B3561995
theorem B3166217 : Blo 2109435 3166217 := bstep (se 2 (by rfl) ⟨1187331, by rfl⟩ : syracuseStep 3166217 = 2374663) B2374663
theorem B2110811 : Blo 2109435 2110811 := bstep (se 1 (by rfl) ⟨1583108, by rfl⟩ : syracuseStep 2110811 = 3166217) B3166217
theorem B10686005 : Blo 2109435 10686005 := bbase (se 5 (by rfl) ⟨500906, by rfl⟩ : syracuseStep 10686005 = 1001813) (by norm_num)
theorem B7124003 : Blo 2109435 7124003 := bstep (se 1 (by rfl) ⟨5343002, by rfl⟩ : syracuseStep 7124003 = 10686005) B10686005
theorem B4749335 : Blo 2109435 4749335 := bstep (se 1 (by rfl) ⟨3562001, by rfl⟩ : syracuseStep 4749335 = 7124003) B7124003
theorem B3166223 : Blo 2109435 3166223 := bstep (se 1 (by rfl) ⟨2374667, by rfl⟩ : syracuseStep 3166223 = 4749335) B4749335
theorem B2110815 : Blo 2109435 2110815 := bstep (se 1 (by rfl) ⟨1583111, by rfl⟩ : syracuseStep 2110815 = 3166223) B3166223
theorem B3166229 : Blo 2109435 3166229 := bbase (se 6 (by rfl) ⟨74208, by rfl⟩ : syracuseStep 3166229 = 148417) (by norm_num)
theorem B2110819 : Blo 2109435 2110819 := bstep (se 1 (by rfl) ⟨1583114, by rfl⟩ : syracuseStep 2110819 = 3166229) B3166229
theorem B10143397 : Blo 2109435 10143397 := bbase (se 4 (by rfl) ⟨950943, by rfl⟩ : syracuseStep 10143397 = 1901887) (by norm_num)
theorem B13524529 : Blo 2109435 13524529 := bstep (se 2 (by rfl) ⟨5071698, by rfl⟩ : syracuseStep 13524529 = 10143397) B10143397
theorem B18032705 : Blo 2109435 18032705 := bstep (se 2 (by rfl) ⟨6762264, by rfl⟩ : syracuseStep 18032705 = 13524529) B13524529
theorem B12021803 : Blo 2109435 12021803 := bstep (se 1 (by rfl) ⟨9016352, by rfl⟩ : syracuseStep 12021803 = 18032705) B18032705
theorem B8014535 : Blo 2109435 8014535 := bstep (se 1 (by rfl) ⟨6010901, by rfl⟩ : syracuseStep 8014535 = 12021803) B12021803
theorem B5343023 : Blo 2109435 5343023 := bstep (se 1 (by rfl) ⟨4007267, by rfl⟩ : syracuseStep 5343023 = 8014535) B8014535
theorem B3562015 : Blo 2109435 3562015 := bstep (se 1 (by rfl) ⟨2671511, by rfl⟩ : syracuseStep 3562015 = 5343023) B5343023
theorem B4749353 : Blo 2109435 4749353 := bstep (se 2 (by rfl) ⟨1781007, by rfl⟩ : syracuseStep 4749353 = 3562015) B3562015
theorem B3166235 : Blo 2109435 3166235 := bstep (se 1 (by rfl) ⟨2374676, by rfl⟩ : syracuseStep 3166235 = 4749353) B4749353
theorem B2110823 : Blo 2109435 2110823 := bstep (se 1 (by rfl) ⟨1583117, by rfl⟩ : syracuseStep 2110823 = 3166235) B3166235
theorem B2374681 : Blo 2109435 2374681 := bbase (se 2 (by rfl) ⟨890505, by rfl⟩ : syracuseStep 2374681 = 1781011) (by norm_num)
theorem B3166241 : Blo 2109435 3166241 := bstep (se 2 (by rfl) ⟨1187340, by rfl⟩ : syracuseStep 3166241 = 2374681) B2374681
theorem B2110827 : Blo 2109435 2110827 := bstep (se 1 (by rfl) ⟨1583120, by rfl⟩ : syracuseStep 2110827 = 3166241) B3166241
theorem B8014565 : Blo 2109435 8014565 := bbase (se 4 (by rfl) ⟨751365, by rfl⟩ : syracuseStep 8014565 = 1502731) (by norm_num)
theorem B5343043 : Blo 2109435 5343043 := bstep (se 1 (by rfl) ⟨4007282, by rfl⟩ : syracuseStep 5343043 = 8014565) B8014565
theorem B7124057 : Blo 2109435 7124057 := bstep (se 2 (by rfl) ⟨2671521, by rfl⟩ : syracuseStep 7124057 = 5343043) B5343043
theorem B4749371 : Blo 2109435 4749371 := bstep (se 1 (by rfl) ⟨3562028, by rfl⟩ : syracuseStep 4749371 = 7124057) B7124057
theorem B3166247 : Blo 2109435 3166247 := bstep (se 1 (by rfl) ⟨2374685, by rfl⟩ : syracuseStep 3166247 = 4749371) B4749371
theorem B2110831 : Blo 2109435 2110831 := bstep (se 1 (by rfl) ⟨1583123, by rfl⟩ : syracuseStep 2110831 = 3166247) B3166247
theorem B3166253 : Blo 2109435 3166253 := bbase (se 3 (by rfl) ⟨593672, by rfl⟩ : syracuseStep 3166253 = 1187345) (by norm_num)
theorem B2110835 : Blo 2109435 2110835 := bstep (se 1 (by rfl) ⟨1583126, by rfl⟩ : syracuseStep 2110835 = 3166253) B3166253
theorem B4749389 : Blo 2109435 4749389 := bbase (se 3 (by rfl) ⟨890510, by rfl⟩ : syracuseStep 4749389 = 1781021) (by norm_num)
theorem B3166259 : Blo 2109435 3166259 := bstep (se 1 (by rfl) ⟨2374694, by rfl⟩ : syracuseStep 3166259 = 4749389) B4749389
theorem B2110839 : Blo 2109435 2110839 := bstep (se 1 (by rfl) ⟨1583129, by rfl⟩ : syracuseStep 2110839 = 3166259) B3166259
theorem B2671537 : Blo 2109435 2671537 := bbase (se 2 (by rfl) ⟨1001826, by rfl⟩ : syracuseStep 2671537 = 2003653) (by norm_num)
theorem B3562049 : Blo 2109435 3562049 := bstep (se 2 (by rfl) ⟨1335768, by rfl⟩ : syracuseStep 3562049 = 2671537) B2671537
theorem B2374699 : Blo 2109435 2374699 := bstep (se 1 (by rfl) ⟨1781024, by rfl⟩ : syracuseStep 2374699 = 3562049) B3562049
theorem B3166265 : Blo 2109435 3166265 := bstep (se 2 (by rfl) ⟨1187349, by rfl⟩ : syracuseStep 3166265 = 2374699) B2374699
theorem B2110843 : Blo 2109435 2110843 := bstep (se 1 (by rfl) ⟨1583132, by rfl⟩ : syracuseStep 2110843 = 3166265) B3166265
theorem B6762341 : Blo 2109435 6762341 := bbase (se 4 (by rfl) ⟨633969, by rfl⟩ : syracuseStep 6762341 = 1267939) (by norm_num)
theorem B4508227 : Blo 2109435 4508227 := bstep (se 1 (by rfl) ⟨3381170, by rfl⟩ : syracuseStep 4508227 = 6762341) B6762341
theorem B24043877 : Blo 2109435 24043877 := bstep (se 4 (by rfl) ⟨2254113, by rfl⟩ : syracuseStep 24043877 = 4508227) B4508227
theorem B16029251 : Blo 2109435 16029251 := bstep (se 1 (by rfl) ⟨12021938, by rfl⟩ : syracuseStep 16029251 = 24043877) B24043877
theorem B10686167 : Blo 2109435 10686167 := bstep (se 1 (by rfl) ⟨8014625, by rfl⟩ : syracuseStep 10686167 = 16029251) B16029251
theorem B7124111 : Blo 2109435 7124111 := bstep (se 1 (by rfl) ⟨5343083, by rfl⟩ : syracuseStep 7124111 = 10686167) B10686167
theorem B4749407 : Blo 2109435 4749407 := bstep (se 1 (by rfl) ⟨3562055, by rfl⟩ : syracuseStep 4749407 = 7124111) B7124111
theorem B3166271 : Blo 2109435 3166271 := bstep (se 1 (by rfl) ⟨2374703, by rfl⟩ : syracuseStep 3166271 = 4749407) B4749407
theorem B2110847 : Blo 2109435 2110847 := bstep (se 1 (by rfl) ⟨1583135, by rfl⟩ : syracuseStep 2110847 = 3166271) B3166271
theorem B3166277 : Blo 2109435 3166277 := bbase (se 4 (by rfl) ⟨296838, by rfl⟩ : syracuseStep 3166277 = 593677) (by norm_num)
theorem B2110851 : Blo 2109435 2110851 := bstep (se 1 (by rfl) ⟨1583138, by rfl⟩ : syracuseStep 2110851 = 3166277) B3166277
theorem B3562069 : Blo 2109435 3562069 := bbase (se 8 (by rfl) ⟨20871, by rfl⟩ : syracuseStep 3562069 = 41743) (by norm_num)
theorem B4749425 : Blo 2109435 4749425 := bstep (se 2 (by rfl) ⟨1781034, by rfl⟩ : syracuseStep 4749425 = 3562069) B3562069
theorem B3166283 : Blo 2109435 3166283 := bstep (se 1 (by rfl) ⟨2374712, by rfl⟩ : syracuseStep 3166283 = 4749425) B4749425
theorem B2110855 : Blo 2109435 2110855 := bstep (se 1 (by rfl) ⟨1583141, by rfl⟩ : syracuseStep 2110855 = 3166283) B3166283
theorem B2374717 : Blo 2109435 2374717 := bbase (se 3 (by rfl) ⟨445259, by rfl⟩ : syracuseStep 2374717 = 890519) (by norm_num)
theorem B3166289 : Blo 2109435 3166289 := bstep (se 2 (by rfl) ⟨1187358, by rfl⟩ : syracuseStep 3166289 = 2374717) B2374717
theorem B2110859 : Blo 2109435 2110859 := bstep (se 1 (by rfl) ⟨1583144, by rfl⟩ : syracuseStep 2110859 = 3166289) B3166289
theorem B7124165 : Blo 2109435 7124165 := bbase (se 4 (by rfl) ⟨667890, by rfl⟩ : syracuseStep 7124165 = 1335781) (by norm_num)
theorem B4749443 : Blo 2109435 4749443 := bstep (se 1 (by rfl) ⟨3562082, by rfl⟩ : syracuseStep 4749443 = 7124165) B7124165
theorem B3166295 : Blo 2109435 3166295 := bstep (se 1 (by rfl) ⟨2374721, by rfl⟩ : syracuseStep 3166295 = 4749443) B4749443
theorem B2110863 : Blo 2109435 2110863 := bstep (se 1 (by rfl) ⟨1583147, by rfl⟩ : syracuseStep 2110863 = 3166295) B3166295
theorem B3166301 : Blo 2109435 3166301 := bbase (se 3 (by rfl) ⟨593681, by rfl⟩ : syracuseStep 3166301 = 1187363) (by norm_num)
theorem B2110867 : Blo 2109435 2110867 := bstep (se 1 (by rfl) ⟨1583150, by rfl⟩ : syracuseStep 2110867 = 3166301) B3166301
theorem B4749461 : Blo 2109435 4749461 := bbase (se 6 (by rfl) ⟨111315, by rfl⟩ : syracuseStep 4749461 = 222631) (by norm_num)
theorem B3166307 : Blo 2109435 3166307 := bstep (se 1 (by rfl) ⟨2374730, by rfl⟩ : syracuseStep 3166307 = 4749461) B4749461
theorem B2110871 : Blo 2109435 2110871 := bstep (se 1 (by rfl) ⟨1583153, by rfl⟩ : syracuseStep 2110871 = 3166307) B3166307
theorem B3005525 : Blo 2109435 3005525 := bbase (se 8 (by rfl) ⟨17610, by rfl⟩ : syracuseStep 3005525 = 35221) (by norm_num)
theorem B8014733 : Blo 2109435 8014733 := bstep (se 3 (by rfl) ⟨1502762, by rfl⟩ : syracuseStep 8014733 = 3005525) B3005525
theorem B5343155 : Blo 2109435 5343155 := bstep (se 1 (by rfl) ⟨4007366, by rfl⟩ : syracuseStep 5343155 = 8014733) B8014733
theorem B3562103 : Blo 2109435 3562103 := bstep (se 1 (by rfl) ⟨2671577, by rfl⟩ : syracuseStep 3562103 = 5343155) B5343155
theorem B2374735 : Blo 2109435 2374735 := bstep (se 1 (by rfl) ⟨1781051, by rfl⟩ : syracuseStep 2374735 = 3562103) B3562103
theorem B3166313 : Blo 2109435 3166313 := bstep (se 2 (by rfl) ⟨1187367, by rfl⟩ : syracuseStep 3166313 = 2374735) B2374735
theorem B2110875 : Blo 2109435 2110875 := bstep (se 1 (by rfl) ⟨1583156, by rfl⟩ : syracuseStep 2110875 = 3166313) B3166313
theorem B30430997 : Blo 2109435 30430997 := bbase (se 6 (by rfl) ⟨713226, by rfl⟩ : syracuseStep 30430997 = 1426453) (by norm_num)
theorem B20287331 : Blo 2109435 20287331 := bstep (se 1 (by rfl) ⟨15215498, by rfl⟩ : syracuseStep 20287331 = 30430997) B30430997
theorem B13524887 : Blo 2109435 13524887 := bstep (se 1 (by rfl) ⟨10143665, by rfl⟩ : syracuseStep 13524887 = 20287331) B20287331
theorem B9016591 : Blo 2109435 9016591 := bstep (se 1 (by rfl) ⟨6762443, by rfl⟩ : syracuseStep 9016591 = 13524887) B13524887
theorem B12022121 : Blo 2109435 12022121 := bstep (se 2 (by rfl) ⟨4508295, by rfl⟩ : syracuseStep 12022121 = 9016591) B9016591
theorem B8014747 : Blo 2109435 8014747 := bstep (se 1 (by rfl) ⟨6011060, by rfl⟩ : syracuseStep 8014747 = 12022121) B12022121
theorem B10686329 : Blo 2109435 10686329 := bstep (se 2 (by rfl) ⟨4007373, by rfl⟩ : syracuseStep 10686329 = 8014747) B8014747
theorem B7124219 : Blo 2109435 7124219 := bstep (se 1 (by rfl) ⟨5343164, by rfl⟩ : syracuseStep 7124219 = 10686329) B10686329
theorem B4749479 : Blo 2109435 4749479 := bstep (se 1 (by rfl) ⟨3562109, by rfl⟩ : syracuseStep 4749479 = 7124219) B7124219
theorem B3166319 : Blo 2109435 3166319 := bstep (se 1 (by rfl) ⟨2374739, by rfl⟩ : syracuseStep 3166319 = 4749479) B4749479
theorem B2110879 : Blo 2109435 2110879 := bstep (se 1 (by rfl) ⟨1583159, by rfl⟩ : syracuseStep 2110879 = 3166319) B3166319
theorem B3166325 : Blo 2109435 3166325 := bbase (se 5 (by rfl) ⟨148421, by rfl⟩ : syracuseStep 3166325 = 296843) (by norm_num)
theorem B2110883 : Blo 2109435 2110883 := bstep (se 1 (by rfl) ⟨1583162, by rfl⟩ : syracuseStep 2110883 = 3166325) B3166325
theorem B4007389 : Blo 2109435 4007389 := bbase (se 3 (by rfl) ⟨751385, by rfl⟩ : syracuseStep 4007389 = 1502771) (by norm_num)
theorem B5343185 : Blo 2109435 5343185 := bstep (se 2 (by rfl) ⟨2003694, by rfl⟩ : syracuseStep 5343185 = 4007389) B4007389
theorem B3562123 : Blo 2109435 3562123 := bstep (se 1 (by rfl) ⟨2671592, by rfl⟩ : syracuseStep 3562123 = 5343185) B5343185
theorem B4749497 : Blo 2109435 4749497 := bstep (se 2 (by rfl) ⟨1781061, by rfl⟩ : syracuseStep 4749497 = 3562123) B3562123
theorem B3166331 : Blo 2109435 3166331 := bstep (se 1 (by rfl) ⟨2374748, by rfl⟩ : syracuseStep 3166331 = 4749497) B4749497
theorem B2110887 : Blo 2109435 2110887 := bstep (se 1 (by rfl) ⟨1583165, by rfl⟩ : syracuseStep 2110887 = 3166331) B3166331
theorem B2374753 : Blo 2109435 2374753 := bbase (se 2 (by rfl) ⟨890532, by rfl⟩ : syracuseStep 2374753 = 1781065) (by norm_num)
theorem B3166337 : Blo 2109435 3166337 := bstep (se 2 (by rfl) ⟨1187376, by rfl⟩ : syracuseStep 3166337 = 2374753) B2374753
theorem B2110891 : Blo 2109435 2110891 := bstep (se 1 (by rfl) ⟨1583168, by rfl⟩ : syracuseStep 2110891 = 3166337) B3166337
theorem B5343205 : Blo 2109435 5343205 := bbase (se 4 (by rfl) ⟨500925, by rfl⟩ : syracuseStep 5343205 = 1001851) (by norm_num)
theorem B7124273 : Blo 2109435 7124273 := bstep (se 2 (by rfl) ⟨2671602, by rfl⟩ : syracuseStep 7124273 = 5343205) B5343205
theorem B4749515 : Blo 2109435 4749515 := bstep (se 1 (by rfl) ⟨3562136, by rfl⟩ : syracuseStep 4749515 = 7124273) B7124273
theorem B3166343 : Blo 2109435 3166343 := bstep (se 1 (by rfl) ⟨2374757, by rfl⟩ : syracuseStep 3166343 = 4749515) B4749515
theorem B2110895 : Blo 2109435 2110895 := bstep (se 1 (by rfl) ⟨1583171, by rfl⟩ : syracuseStep 2110895 = 3166343) B3166343
theorem B3166349 : Blo 2109435 3166349 := bbase (se 3 (by rfl) ⟨593690, by rfl⟩ : syracuseStep 3166349 = 1187381) (by norm_num)
theorem B2110899 : Blo 2109435 2110899 := bstep (se 1 (by rfl) ⟨1583174, by rfl⟩ : syracuseStep 2110899 = 3166349) B3166349
theorem B4749533 : Blo 2109435 4749533 := bbase (se 3 (by rfl) ⟨890537, by rfl⟩ : syracuseStep 4749533 = 1781075) (by norm_num)
theorem B3166355 : Blo 2109435 3166355 := bstep (se 1 (by rfl) ⟨2374766, by rfl⟩ : syracuseStep 3166355 = 4749533) B4749533
theorem B2110903 : Blo 2109435 2110903 := bstep (se 1 (by rfl) ⟨1583177, by rfl⟩ : syracuseStep 2110903 = 3166355) B3166355
theorem B3562157 : Blo 2109435 3562157 := bbase (se 3 (by rfl) ⟨667904, by rfl⟩ : syracuseStep 3562157 = 1335809) (by norm_num)
theorem B2374771 : Blo 2109435 2374771 := bstep (se 1 (by rfl) ⟨1781078, by rfl⟩ : syracuseStep 2374771 = 3562157) B3562157
theorem B3166361 : Blo 2109435 3166361 := bstep (se 2 (by rfl) ⟨1187385, by rfl⟩ : syracuseStep 3166361 = 2374771) B2374771
theorem B2110907 : Blo 2109435 2110907 := bstep (se 1 (by rfl) ⟨1583180, by rfl⟩ : syracuseStep 2110907 = 3166361) B3166361
theorem B15633749 : Blo 2109435 15633749 := bbase (se 11 (by rfl) ⟨11450, by rfl⟩ : syracuseStep 15633749 = 22901) (by norm_num)
theorem B41689997 : Blo 2109435 41689997 := bstep (se 3 (by rfl) ⟨7816874, by rfl⟩ : syracuseStep 41689997 = 15633749) B15633749
theorem B27793331 : Blo 2109435 27793331 := bstep (se 1 (by rfl) ⟨20844998, by rfl⟩ : syracuseStep 27793331 = 41689997) B41689997
theorem B18528887 : Blo 2109435 18528887 := bstep (se 1 (by rfl) ⟨13896665, by rfl⟩ : syracuseStep 18528887 = 27793331) B27793331
theorem B12352591 : Blo 2109435 12352591 := bstep (se 1 (by rfl) ⟨9264443, by rfl⟩ : syracuseStep 12352591 = 18528887) B18528887
theorem B16470121 : Blo 2109435 16470121 := bstep (se 2 (by rfl) ⟨6176295, by rfl⟩ : syracuseStep 16470121 = 12352591) B12352591
theorem B21960161 : Blo 2109435 21960161 := bstep (se 2 (by rfl) ⟨8235060, by rfl⟩ : syracuseStep 21960161 = 16470121) B16470121
theorem B14640107 : Blo 2109435 14640107 := bstep (se 1 (by rfl) ⟨10980080, by rfl⟩ : syracuseStep 14640107 = 21960161) B21960161
theorem B156161141 : Blo 2109435 156161141 := bstep (se 5 (by rfl) ⟨7320053, by rfl⟩ : syracuseStep 156161141 = 14640107) B14640107
theorem B104107427 : Blo 2109435 104107427 := bstep (se 1 (by rfl) ⟨78080570, by rfl⟩ : syracuseStep 104107427 = 156161141) B156161141
theorem B69404951 : Blo 2109435 69404951 := bstep (se 1 (by rfl) ⟨52053713, by rfl⟩ : syracuseStep 69404951 = 104107427) B104107427
theorem B46269967 : Blo 2109435 46269967 := bstep (se 1 (by rfl) ⟨34702475, by rfl⟩ : syracuseStep 46269967 = 69404951) B69404951
theorem B61693289 : Blo 2109435 61693289 := bstep (se 2 (by rfl) ⟨23134983, by rfl⟩ : syracuseStep 61693289 = 46269967) B46269967
theorem B41128859 : Blo 2109435 41128859 := bstep (se 1 (by rfl) ⟨30846644, by rfl⟩ : syracuseStep 41128859 = 61693289) B61693289
theorem B27419239 : Blo 2109435 27419239 := bstep (se 1 (by rfl) ⟨20564429, by rfl⟩ : syracuseStep 27419239 = 41128859) B41128859
theorem B146235941 : Blo 2109435 146235941 := bstep (se 4 (by rfl) ⟨13709619, by rfl⟩ : syracuseStep 146235941 = 27419239) B27419239
theorem B97490627 : Blo 2109435 97490627 := bstep (se 1 (by rfl) ⟨73117970, by rfl⟩ : syracuseStep 97490627 = 146235941) B146235941
theorem B64993751 : Blo 2109435 64993751 := bstep (se 1 (by rfl) ⟨48745313, by rfl⟩ : syracuseStep 64993751 = 97490627) B97490627
theorem B43329167 : Blo 2109435 43329167 := bstep (se 1 (by rfl) ⟨32496875, by rfl⟩ : syracuseStep 43329167 = 64993751) B64993751
theorem B28886111 : Blo 2109435 28886111 := bstep (se 1 (by rfl) ⟨21664583, by rfl⟩ : syracuseStep 28886111 = 43329167) B43329167
theorem B19257407 : Blo 2109435 19257407 := bstep (se 1 (by rfl) ⟨14443055, by rfl⟩ : syracuseStep 19257407 = 28886111) B28886111
theorem B12838271 : Blo 2109435 12838271 := bstep (se 1 (by rfl) ⟨9628703, by rfl⟩ : syracuseStep 12838271 = 19257407) B19257407
theorem B34235389 : Blo 2109435 34235389 := bstep (se 3 (by rfl) ⟨6419135, by rfl⟩ : syracuseStep 34235389 = 12838271) B12838271
theorem B45647185 : Blo 2109435 45647185 := bstep (se 2 (by rfl) ⟨17117694, by rfl⟩ : syracuseStep 45647185 = 34235389) B34235389
theorem B60862913 : Blo 2109435 60862913 := bstep (se 2 (by rfl) ⟨22823592, by rfl⟩ : syracuseStep 60862913 = 45647185) B45647185
theorem B40575275 : Blo 2109435 40575275 := bstep (se 1 (by rfl) ⟨30431456, by rfl⟩ : syracuseStep 40575275 = 60862913) B60862913
theorem B27050183 : Blo 2109435 27050183 := bstep (se 1 (by rfl) ⟨20287637, by rfl⟩ : syracuseStep 27050183 = 40575275) B40575275
theorem B18033455 : Blo 2109435 18033455 := bstep (se 1 (by rfl) ⟨13525091, by rfl⟩ : syracuseStep 18033455 = 27050183) B27050183
theorem B12022303 : Blo 2109435 12022303 := bstep (se 1 (by rfl) ⟨9016727, by rfl⟩ : syracuseStep 12022303 = 18033455) B18033455
theorem B16029737 : Blo 2109435 16029737 := bstep (se 2 (by rfl) ⟨6011151, by rfl⟩ : syracuseStep 16029737 = 12022303) B12022303
theorem B10686491 : Blo 2109435 10686491 := bstep (se 1 (by rfl) ⟨8014868, by rfl⟩ : syracuseStep 10686491 = 16029737) B16029737
theorem B7124327 : Blo 2109435 7124327 := bstep (se 1 (by rfl) ⟨5343245, by rfl⟩ : syracuseStep 7124327 = 10686491) B10686491
theorem B4749551 : Blo 2109435 4749551 := bstep (se 1 (by rfl) ⟨3562163, by rfl⟩ : syracuseStep 4749551 = 7124327) B7124327
theorem B3166367 : Blo 2109435 3166367 := bstep (se 1 (by rfl) ⟨2374775, by rfl⟩ : syracuseStep 3166367 = 4749551) B4749551
theorem B2110911 : Blo 2109435 2110911 := bstep (se 1 (by rfl) ⟨1583183, by rfl⟩ : syracuseStep 2110911 = 3166367) B3166367
theorem B3166373 : Blo 2109435 3166373 := bbase (se 4 (by rfl) ⟨296847, by rfl⟩ : syracuseStep 3166373 = 593695) (by norm_num)
theorem B2110915 : Blo 2109435 2110915 := bstep (se 1 (by rfl) ⟨1583186, by rfl⟩ : syracuseStep 2110915 = 3166373) B3166373
theorem B2671633 : Blo 2109435 2671633 := bbase (se 2 (by rfl) ⟨1001862, by rfl⟩ : syracuseStep 2671633 = 2003725) (by norm_num)
theorem B3562177 : Blo 2109435 3562177 := bstep (se 2 (by rfl) ⟨1335816, by rfl⟩ : syracuseStep 3562177 = 2671633) B2671633
theorem B4749569 : Blo 2109435 4749569 := bstep (se 2 (by rfl) ⟨1781088, by rfl⟩ : syracuseStep 4749569 = 3562177) B3562177
theorem B3166379 : Blo 2109435 3166379 := bstep (se 1 (by rfl) ⟨2374784, by rfl⟩ : syracuseStep 3166379 = 4749569) B4749569
theorem B2110919 : Blo 2109435 2110919 := bstep (se 1 (by rfl) ⟨1583189, by rfl⟩ : syracuseStep 2110919 = 3166379) B3166379
theorem B2374789 : Blo 2109435 2374789 := bbase (se 4 (by rfl) ⟨222636, by rfl⟩ : syracuseStep 2374789 = 445273) (by norm_num)
theorem B3166385 : Blo 2109435 3166385 := bstep (se 2 (by rfl) ⟨1187394, by rfl⟩ : syracuseStep 3166385 = 2374789) B2374789
theorem B2110923 : Blo 2109435 2110923 := bstep (se 1 (by rfl) ⟨1583192, by rfl⟩ : syracuseStep 2110923 = 3166385) B3166385
theorem B5416189 : Blo 2109435 5416189 := bbase (se 3 (by rfl) ⟨1015535, by rfl⟩ : syracuseStep 5416189 = 2031071) (by norm_num)
theorem B28886341 : Blo 2109435 28886341 := bstep (se 4 (by rfl) ⟨2708094, by rfl⟩ : syracuseStep 28886341 = 5416189) B5416189
theorem B38515121 : Blo 2109435 38515121 := bstep (se 2 (by rfl) ⟨14443170, by rfl⟩ : syracuseStep 38515121 = 28886341) B28886341
theorem B25676747 : Blo 2109435 25676747 := bstep (se 1 (by rfl) ⟨19257560, by rfl⟩ : syracuseStep 25676747 = 38515121) B38515121
theorem B17117831 : Blo 2109435 17117831 := bstep (se 1 (by rfl) ⟨12838373, by rfl⟩ : syracuseStep 17117831 = 25676747) B25676747
theorem B11411887 : Blo 2109435 11411887 := bstep (se 1 (by rfl) ⟨8558915, by rfl⟩ : syracuseStep 11411887 = 17117831) B17117831
theorem B15215849 : Blo 2109435 15215849 := bstep (se 2 (by rfl) ⟨5705943, by rfl⟩ : syracuseStep 15215849 = 11411887) B11411887
theorem B10143899 : Blo 2109435 10143899 := bstep (se 1 (by rfl) ⟨7607924, by rfl⟩ : syracuseStep 10143899 = 15215849) B15215849
theorem B6762599 : Blo 2109435 6762599 := bstep (se 1 (by rfl) ⟨5071949, by rfl⟩ : syracuseStep 6762599 = 10143899) B10143899
theorem B4508399 : Blo 2109435 4508399 := bstep (se 1 (by rfl) ⟨3381299, by rfl⟩ : syracuseStep 4508399 = 6762599) B6762599
theorem B3005599 : Blo 2109435 3005599 := bstep (se 1 (by rfl) ⟨2254199, by rfl⟩ : syracuseStep 3005599 = 4508399) B4508399
theorem B4007465 : Blo 2109435 4007465 := bstep (se 2 (by rfl) ⟨1502799, by rfl⟩ : syracuseStep 4007465 = 3005599) B3005599
theorem B2671643 : Blo 2109435 2671643 := bstep (se 1 (by rfl) ⟨2003732, by rfl⟩ : syracuseStep 2671643 = 4007465) B4007465
theorem B7124381 : Blo 2109435 7124381 := bstep (se 3 (by rfl) ⟨1335821, by rfl⟩ : syracuseStep 7124381 = 2671643) B2671643
theorem B4749587 : Blo 2109435 4749587 := bstep (se 1 (by rfl) ⟨3562190, by rfl⟩ : syracuseStep 4749587 = 7124381) B7124381
theorem B3166391 : Blo 2109435 3166391 := bstep (se 1 (by rfl) ⟨2374793, by rfl⟩ : syracuseStep 3166391 = 4749587) B4749587
theorem B2110927 : Blo 2109435 2110927 := bstep (se 1 (by rfl) ⟨1583195, by rfl⟩ : syracuseStep 2110927 = 3166391) B3166391
theorem B3166397 : Blo 2109435 3166397 := bbase (se 3 (by rfl) ⟨593699, by rfl⟩ : syracuseStep 3166397 = 1187399) (by norm_num)
theorem B2110931 : Blo 2109435 2110931 := bstep (se 1 (by rfl) ⟨1583198, by rfl⟩ : syracuseStep 2110931 = 3166397) B3166397
theorem B4749605 : Blo 2109435 4749605 := bbase (se 4 (by rfl) ⟨445275, by rfl⟩ : syracuseStep 4749605 = 890551) (by norm_num)
theorem B3166403 : Blo 2109435 3166403 := bstep (se 1 (by rfl) ⟨2374802, by rfl⟩ : syracuseStep 3166403 = 4749605) B4749605
theorem B2110935 : Blo 2109435 2110935 := bstep (se 1 (by rfl) ⟨1583201, by rfl⟩ : syracuseStep 2110935 = 3166403) B3166403
theorem B5343317 : Blo 2109435 5343317 := bbase (se 8 (by rfl) ⟨31308, by rfl⟩ : syracuseStep 5343317 = 62617) (by norm_num)
theorem B3562211 : Blo 2109435 3562211 := bstep (se 1 (by rfl) ⟨2671658, by rfl⟩ : syracuseStep 3562211 = 5343317) B5343317
theorem B2374807 : Blo 2109435 2374807 := bstep (se 1 (by rfl) ⟨1781105, by rfl⟩ : syracuseStep 2374807 = 3562211) B3562211
theorem B3166409 : Blo 2109435 3166409 := bstep (se 2 (by rfl) ⟨1187403, by rfl⟩ : syracuseStep 3166409 = 2374807) B2374807
theorem B2110939 : Blo 2109435 2110939 := bstep (se 1 (by rfl) ⟨1583204, by rfl⟩ : syracuseStep 2110939 = 3166409) B3166409
theorem B2139745 : Blo 2109435 2139745 := bbase (se 2 (by rfl) ⟨802404, by rfl⟩ : syracuseStep 2139745 = 1604809) (by norm_num)
theorem B2852993 : Blo 2109435 2852993 := bstep (se 2 (by rfl) ⟨1069872, by rfl⟩ : syracuseStep 2852993 = 2139745) B2139745
theorem B7607981 : Blo 2109435 7607981 := bstep (se 3 (by rfl) ⟨1426496, by rfl⟩ : syracuseStep 7607981 = 2852993) B2852993
theorem B5071987 : Blo 2109435 5071987 := bstep (se 1 (by rfl) ⟨3803990, by rfl⟩ : syracuseStep 5071987 = 7607981) B7607981
theorem B6762649 : Blo 2109435 6762649 := bstep (se 2 (by rfl) ⟨2535993, by rfl⟩ : syracuseStep 6762649 = 5071987) B5071987
theorem B9016865 : Blo 2109435 9016865 := bstep (se 2 (by rfl) ⟨3381324, by rfl⟩ : syracuseStep 9016865 = 6762649) B6762649
theorem B6011243 : Blo 2109435 6011243 := bstep (se 1 (by rfl) ⟨4508432, by rfl⟩ : syracuseStep 6011243 = 9016865) B9016865
theorem B4007495 : Blo 2109435 4007495 := bstep (se 1 (by rfl) ⟨3005621, by rfl⟩ : syracuseStep 4007495 = 6011243) B6011243
theorem B10686653 : Blo 2109435 10686653 := bstep (se 3 (by rfl) ⟨2003747, by rfl⟩ : syracuseStep 10686653 = 4007495) B4007495
theorem B7124435 : Blo 2109435 7124435 := bstep (se 1 (by rfl) ⟨5343326, by rfl⟩ : syracuseStep 7124435 = 10686653) B10686653
theorem B4749623 : Blo 2109435 4749623 := bstep (se 1 (by rfl) ⟨3562217, by rfl⟩ : syracuseStep 4749623 = 7124435) B7124435
theorem B3166415 : Blo 2109435 3166415 := bstep (se 1 (by rfl) ⟨2374811, by rfl⟩ : syracuseStep 3166415 = 4749623) B4749623
theorem B2110943 : Blo 2109435 2110943 := bstep (se 1 (by rfl) ⟨1583207, by rfl⟩ : syracuseStep 2110943 = 3166415) B3166415
theorem B3166421 : Blo 2109435 3166421 := bbase (se 7 (by rfl) ⟨37106, by rfl⟩ : syracuseStep 3166421 = 74213) (by norm_num)
theorem B2110947 : Blo 2109435 2110947 := bstep (se 1 (by rfl) ⟨1583210, by rfl⟩ : syracuseStep 2110947 = 3166421) B3166421
theorem B2254225 : Blo 2109435 2254225 := bbase (se 2 (by rfl) ⟨845334, by rfl⟩ : syracuseStep 2254225 = 1690669) (by norm_num)
theorem B3005633 : Blo 2109435 3005633 := bstep (se 2 (by rfl) ⟨1127112, by rfl⟩ : syracuseStep 3005633 = 2254225) B2254225
theorem B8015021 : Blo 2109435 8015021 := bstep (se 3 (by rfl) ⟨1502816, by rfl⟩ : syracuseStep 8015021 = 3005633) B3005633
theorem B5343347 : Blo 2109435 5343347 := bstep (se 1 (by rfl) ⟨4007510, by rfl⟩ : syracuseStep 5343347 = 8015021) B8015021
theorem B3562231 : Blo 2109435 3562231 := bstep (se 1 (by rfl) ⟨2671673, by rfl⟩ : syracuseStep 3562231 = 5343347) B5343347
theorem B4749641 : Blo 2109435 4749641 := bstep (se 2 (by rfl) ⟨1781115, by rfl⟩ : syracuseStep 4749641 = 3562231) B3562231
theorem B3166427 : Blo 2109435 3166427 := bstep (se 1 (by rfl) ⟨2374820, by rfl⟩ : syracuseStep 3166427 = 4749641) B4749641
theorem B2110951 : Blo 2109435 2110951 := bstep (se 1 (by rfl) ⟨1583213, by rfl⟩ : syracuseStep 2110951 = 3166427) B3166427
theorem B2374825 : Blo 2109435 2374825 := bbase (se 2 (by rfl) ⟨890559, by rfl⟩ : syracuseStep 2374825 = 1781119) (by norm_num)
theorem B3166433 : Blo 2109435 3166433 := bstep (se 2 (by rfl) ⟨1187412, by rfl⟩ : syracuseStep 3166433 = 2374825) B2374825
theorem B2110955 : Blo 2109435 2110955 := bstep (se 1 (by rfl) ⟨1583216, by rfl⟩ : syracuseStep 2110955 = 3166433) B3166433
theorem B9016933 : Blo 2109435 9016933 := bbase (se 4 (by rfl) ⟨845337, by rfl⟩ : syracuseStep 9016933 = 1690675) (by norm_num)
theorem B12022577 : Blo 2109435 12022577 := bstep (se 2 (by rfl) ⟨4508466, by rfl⟩ : syracuseStep 12022577 = 9016933) B9016933
theorem B8015051 : Blo 2109435 8015051 := bstep (se 1 (by rfl) ⟨6011288, by rfl⟩ : syracuseStep 8015051 = 12022577) B12022577
theorem B5343367 : Blo 2109435 5343367 := bstep (se 1 (by rfl) ⟨4007525, by rfl⟩ : syracuseStep 5343367 = 8015051) B8015051
theorem B7124489 : Blo 2109435 7124489 := bstep (se 2 (by rfl) ⟨2671683, by rfl⟩ : syracuseStep 7124489 = 5343367) B5343367
theorem B4749659 : Blo 2109435 4749659 := bstep (se 1 (by rfl) ⟨3562244, by rfl⟩ : syracuseStep 4749659 = 7124489) B7124489
theorem B3166439 : Blo 2109435 3166439 := bstep (se 1 (by rfl) ⟨2374829, by rfl⟩ : syracuseStep 3166439 = 4749659) B4749659
theorem B2110959 : Blo 2109435 2110959 := bstep (se 1 (by rfl) ⟨1583219, by rfl⟩ : syracuseStep 2110959 = 3166439) B3166439
theorem B3166445 : Blo 2109435 3166445 := bbase (se 3 (by rfl) ⟨593708, by rfl⟩ : syracuseStep 3166445 = 1187417) (by norm_num)
theorem B2110963 : Blo 2109435 2110963 := bstep (se 1 (by rfl) ⟨1583222, by rfl⟩ : syracuseStep 2110963 = 3166445) B3166445
theorem B4749677 : Blo 2109435 4749677 := bbase (se 3 (by rfl) ⟨890564, by rfl⟩ : syracuseStep 4749677 = 1781129) (by norm_num)
theorem B3166451 : Blo 2109435 3166451 := bstep (se 1 (by rfl) ⟨2374838, by rfl⟩ : syracuseStep 3166451 = 4749677) B4749677
theorem B2110967 : Blo 2109435 2110967 := bstep (se 1 (by rfl) ⟨1583225, by rfl⟩ : syracuseStep 2110967 = 3166451) B3166451
theorem B4007549 : Blo 2109435 4007549 := bbase (se 3 (by rfl) ⟨751415, by rfl⟩ : syracuseStep 4007549 = 1502831) (by norm_num)
theorem B2671699 : Blo 2109435 2671699 := bstep (se 1 (by rfl) ⟨2003774, by rfl⟩ : syracuseStep 2671699 = 4007549) B4007549
theorem B3562265 : Blo 2109435 3562265 := bstep (se 2 (by rfl) ⟨1335849, by rfl⟩ : syracuseStep 3562265 = 2671699) B2671699
theorem B2374843 : Blo 2109435 2374843 := bstep (se 1 (by rfl) ⟨1781132, by rfl⟩ : syracuseStep 2374843 = 3562265) B3562265
theorem B3166457 : Blo 2109435 3166457 := bstep (se 2 (by rfl) ⟨1187421, by rfl⟩ : syracuseStep 3166457 = 2374843) B2374843
theorem B2110971 : Blo 2109435 2110971 := bstep (se 1 (by rfl) ⟨1583228, by rfl⟩ : syracuseStep 2110971 = 3166457) B3166457
theorem B4570013 : Blo 2109435 4570013 := bbase (se 3 (by rfl) ⟨856877, by rfl⟩ : syracuseStep 4570013 = 1713755) (by norm_num)
theorem B3046675 : Blo 2109435 3046675 := bstep (se 1 (by rfl) ⟨2285006, by rfl⟩ : syracuseStep 3046675 = 4570013) B4570013
theorem B4062233 : Blo 2109435 4062233 := bstep (se 2 (by rfl) ⟨1523337, by rfl⟩ : syracuseStep 4062233 = 3046675) B3046675
theorem B10832621 : Blo 2109435 10832621 := bstep (se 3 (by rfl) ⟨2031116, by rfl⟩ : syracuseStep 10832621 = 4062233) B4062233
theorem B28886989 : Blo 2109435 28886989 := bstep (se 3 (by rfl) ⟨5416310, by rfl⟩ : syracuseStep 28886989 = 10832621) B10832621
theorem B38515985 : Blo 2109435 38515985 := bstep (se 2 (by rfl) ⟨14443494, by rfl⟩ : syracuseStep 38515985 = 28886989) B28886989
theorem B25677323 : Blo 2109435 25677323 := bstep (se 1 (by rfl) ⟨19257992, by rfl⟩ : syracuseStep 25677323 = 38515985) B38515985
theorem B17118215 : Blo 2109435 17118215 := bstep (se 1 (by rfl) ⟨12838661, by rfl⟩ : syracuseStep 17118215 = 25677323) B25677323
theorem B11412143 : Blo 2109435 11412143 := bstep (se 1 (by rfl) ⟨8559107, by rfl⟩ : syracuseStep 11412143 = 17118215) B17118215
theorem B7608095 : Blo 2109435 7608095 := bstep (se 1 (by rfl) ⟨5706071, by rfl⟩ : syracuseStep 7608095 = 11412143) B11412143
theorem B5072063 : Blo 2109435 5072063 := bstep (se 1 (by rfl) ⟨3804047, by rfl⟩ : syracuseStep 5072063 = 7608095) B7608095
theorem B54102005 : Blo 2109435 54102005 := bstep (se 5 (by rfl) ⟨2536031, by rfl⟩ : syracuseStep 54102005 = 5072063) B5072063
theorem B36068003 : Blo 2109435 36068003 := bstep (se 1 (by rfl) ⟨27051002, by rfl⟩ : syracuseStep 36068003 = 54102005) B54102005
theorem B24045335 : Blo 2109435 24045335 := bstep (se 1 (by rfl) ⟨18034001, by rfl⟩ : syracuseStep 24045335 = 36068003) B36068003
theorem B16030223 : Blo 2109435 16030223 := bstep (se 1 (by rfl) ⟨12022667, by rfl⟩ : syracuseStep 16030223 = 24045335) B24045335
theorem B10686815 : Blo 2109435 10686815 := bstep (se 1 (by rfl) ⟨8015111, by rfl⟩ : syracuseStep 10686815 = 16030223) B16030223
theorem B7124543 : Blo 2109435 7124543 := bstep (se 1 (by rfl) ⟨5343407, by rfl⟩ : syracuseStep 7124543 = 10686815) B10686815
theorem B4749695 : Blo 2109435 4749695 := bstep (se 1 (by rfl) ⟨3562271, by rfl⟩ : syracuseStep 4749695 = 7124543) B7124543
theorem B3166463 : Blo 2109435 3166463 := bstep (se 1 (by rfl) ⟨2374847, by rfl⟩ : syracuseStep 3166463 = 4749695) B4749695
theorem B2110975 : Blo 2109435 2110975 := bstep (se 1 (by rfl) ⟨1583231, by rfl⟩ : syracuseStep 2110975 = 3166463) B3166463
theorem B3166469 : Blo 2109435 3166469 := bbase (se 4 (by rfl) ⟨296856, by rfl⟩ : syracuseStep 3166469 = 593713) (by norm_num)
theorem B2110979 : Blo 2109435 2110979 := bstep (se 1 (by rfl) ⟨1583234, by rfl⟩ : syracuseStep 2110979 = 3166469) B3166469
theorem B3562285 : Blo 2109435 3562285 := bbase (se 3 (by rfl) ⟨667928, by rfl⟩ : syracuseStep 3562285 = 1335857) (by norm_num)
theorem B4749713 : Blo 2109435 4749713 := bstep (se 2 (by rfl) ⟨1781142, by rfl⟩ : syracuseStep 4749713 = 3562285) B3562285
theorem B3166475 : Blo 2109435 3166475 := bstep (se 1 (by rfl) ⟨2374856, by rfl⟩ : syracuseStep 3166475 = 4749713) B4749713
theorem B2110983 : Blo 2109435 2110983 := bstep (se 1 (by rfl) ⟨1583237, by rfl⟩ : syracuseStep 2110983 = 3166475) B3166475
theorem B2374861 : Blo 2109435 2374861 := bbase (se 3 (by rfl) ⟨445286, by rfl⟩ : syracuseStep 2374861 = 890573) (by norm_num)
theorem B3166481 : Blo 2109435 3166481 := bstep (se 2 (by rfl) ⟨1187430, by rfl⟩ : syracuseStep 3166481 = 2374861) B2374861
theorem B2110987 : Blo 2109435 2110987 := bstep (se 1 (by rfl) ⟨1583240, by rfl⟩ : syracuseStep 2110987 = 3166481) B3166481
theorem B7124597 : Blo 2109435 7124597 := bbase (se 5 (by rfl) ⟨333965, by rfl⟩ : syracuseStep 7124597 = 667931) (by norm_num)
theorem B4749731 : Blo 2109435 4749731 := bstep (se 1 (by rfl) ⟨3562298, by rfl⟩ : syracuseStep 4749731 = 7124597) B7124597
theorem B3166487 : Blo 2109435 3166487 := bstep (se 1 (by rfl) ⟨2374865, by rfl⟩ : syracuseStep 3166487 = 4749731) B4749731
theorem B2110991 : Blo 2109435 2110991 := bstep (se 1 (by rfl) ⟨1583243, by rfl⟩ : syracuseStep 2110991 = 3166487) B3166487
theorem B3166493 : Blo 2109435 3166493 := bbase (se 3 (by rfl) ⟨593717, by rfl⟩ : syracuseStep 3166493 = 1187435) (by norm_num)
theorem B2110995 : Blo 2109435 2110995 := bstep (se 1 (by rfl) ⟨1583246, by rfl⟩ : syracuseStep 2110995 = 3166493) B3166493
theorem B4749749 : Blo 2109435 4749749 := bbase (se 5 (by rfl) ⟨222644, by rfl⟩ : syracuseStep 4749749 = 445289) (by norm_num)
theorem B3166499 : Blo 2109435 3166499 := bstep (se 1 (by rfl) ⟨2374874, by rfl⟩ : syracuseStep 3166499 = 4749749) B4749749
theorem B2110999 : Blo 2109435 2110999 := bstep (se 1 (by rfl) ⟨1583249, by rfl⟩ : syracuseStep 2110999 = 3166499) B3166499
theorem B3381421 : Blo 2109435 3381421 := bbase (se 3 (by rfl) ⟨634016, by rfl⟩ : syracuseStep 3381421 = 1268033) (by norm_num)
theorem B4508561 : Blo 2109435 4508561 := bstep (se 2 (by rfl) ⟨1690710, by rfl⟩ : syracuseStep 4508561 = 3381421) B3381421
theorem B12022829 : Blo 2109435 12022829 := bstep (se 3 (by rfl) ⟨2254280, by rfl⟩ : syracuseStep 12022829 = 4508561) B4508561
theorem B8015219 : Blo 2109435 8015219 := bstep (se 1 (by rfl) ⟨6011414, by rfl⟩ : syracuseStep 8015219 = 12022829) B12022829
theorem B5343479 : Blo 2109435 5343479 := bstep (se 1 (by rfl) ⟨4007609, by rfl⟩ : syracuseStep 5343479 = 8015219) B8015219
theorem B3562319 : Blo 2109435 3562319 := bstep (se 1 (by rfl) ⟨2671739, by rfl⟩ : syracuseStep 3562319 = 5343479) B5343479
theorem B2374879 : Blo 2109435 2374879 := bstep (se 1 (by rfl) ⟨1781159, by rfl⟩ : syracuseStep 2374879 = 3562319) B3562319
theorem B3166505 : Blo 2109435 3166505 := bstep (se 2 (by rfl) ⟨1187439, by rfl⟩ : syracuseStep 3166505 = 2374879) B2374879
theorem B2111003 : Blo 2109435 2111003 := bstep (se 1 (by rfl) ⟨1583252, by rfl⟩ : syracuseStep 2111003 = 3166505) B3166505
theorem B5072141 : Blo 2109435 5072141 := bbase (se 3 (by rfl) ⟨951026, by rfl⟩ : syracuseStep 5072141 = 1902053) (by norm_num)
theorem B3381427 : Blo 2109435 3381427 := bstep (se 1 (by rfl) ⟨2536070, by rfl⟩ : syracuseStep 3381427 = 5072141) B5072141
theorem B4508569 : Blo 2109435 4508569 := bstep (se 2 (by rfl) ⟨1690713, by rfl⟩ : syracuseStep 4508569 = 3381427) B3381427
theorem B6011425 : Blo 2109435 6011425 := bstep (se 2 (by rfl) ⟨2254284, by rfl⟩ : syracuseStep 6011425 = 4508569) B4508569
theorem B8015233 : Blo 2109435 8015233 := bstep (se 2 (by rfl) ⟨3005712, by rfl⟩ : syracuseStep 8015233 = 6011425) B6011425
theorem B10686977 : Blo 2109435 10686977 := bstep (se 2 (by rfl) ⟨4007616, by rfl⟩ : syracuseStep 10686977 = 8015233) B8015233
theorem B7124651 : Blo 2109435 7124651 := bstep (se 1 (by rfl) ⟨5343488, by rfl⟩ : syracuseStep 7124651 = 10686977) B10686977
theorem B4749767 : Blo 2109435 4749767 := bstep (se 1 (by rfl) ⟨3562325, by rfl⟩ : syracuseStep 4749767 = 7124651) B7124651
theorem B3166511 : Blo 2109435 3166511 := bstep (se 1 (by rfl) ⟨2374883, by rfl⟩ : syracuseStep 3166511 = 4749767) B4749767
theorem B2111007 : Blo 2109435 2111007 := bstep (se 1 (by rfl) ⟨1583255, by rfl⟩ : syracuseStep 2111007 = 3166511) B3166511
theorem B3166517 : Blo 2109435 3166517 := bbase (se 5 (by rfl) ⟨148430, by rfl⟩ : syracuseStep 3166517 = 296861) (by norm_num)
theorem B2111011 : Blo 2109435 2111011 := bstep (se 1 (by rfl) ⟨1583258, by rfl⟩ : syracuseStep 2111011 = 3166517) B3166517
theorem B5343509 : Blo 2109435 5343509 := bbase (se 6 (by rfl) ⟨125238, by rfl⟩ : syracuseStep 5343509 = 250477) (by norm_num)
theorem B3562339 : Blo 2109435 3562339 := bstep (se 1 (by rfl) ⟨2671754, by rfl⟩ : syracuseStep 3562339 = 5343509) B5343509
theorem B4749785 : Blo 2109435 4749785 := bstep (se 2 (by rfl) ⟨1781169, by rfl⟩ : syracuseStep 4749785 = 3562339) B3562339
theorem B3166523 : Blo 2109435 3166523 := bstep (se 1 (by rfl) ⟨2374892, by rfl⟩ : syracuseStep 3166523 = 4749785) B4749785
theorem B2111015 : Blo 2109435 2111015 := bstep (se 1 (by rfl) ⟨1583261, by rfl⟩ : syracuseStep 2111015 = 3166523) B3166523
theorem B2374897 : Blo 2109435 2374897 := bbase (se 2 (by rfl) ⟨890586, by rfl⟩ : syracuseStep 2374897 = 1781173) (by norm_num)
theorem B3166529 : Blo 2109435 3166529 := bstep (se 2 (by rfl) ⟨1187448, by rfl⟩ : syracuseStep 3166529 = 2374897) B2374897
theorem B2111019 : Blo 2109435 2111019 := bstep (se 1 (by rfl) ⟨1583264, by rfl⟩ : syracuseStep 2111019 = 3166529) B3166529
theorem B2853101 : Blo 2109435 2853101 := bbase (se 3 (by rfl) ⟨534956, by rfl⟩ : syracuseStep 2853101 = 1069913) (by norm_num)
theorem B7608269 : Blo 2109435 7608269 := bstep (se 3 (by rfl) ⟨1426550, by rfl⟩ : syracuseStep 7608269 = 2853101) B2853101
theorem B20288717 : Blo 2109435 20288717 := bstep (se 3 (by rfl) ⟨3804134, by rfl⟩ : syracuseStep 20288717 = 7608269) B7608269
theorem B13525811 : Blo 2109435 13525811 := bstep (se 1 (by rfl) ⟨10144358, by rfl⟩ : syracuseStep 13525811 = 20288717) B20288717
theorem B9017207 : Blo 2109435 9017207 := bstep (se 1 (by rfl) ⟨6762905, by rfl⟩ : syracuseStep 9017207 = 13525811) B13525811
theorem B6011471 : Blo 2109435 6011471 := bstep (se 1 (by rfl) ⟨4508603, by rfl⟩ : syracuseStep 6011471 = 9017207) B9017207
theorem B4007647 : Blo 2109435 4007647 := bstep (se 1 (by rfl) ⟨3005735, by rfl⟩ : syracuseStep 4007647 = 6011471) B6011471
theorem B5343529 : Blo 2109435 5343529 := bstep (se 2 (by rfl) ⟨2003823, by rfl⟩ : syracuseStep 5343529 = 4007647) B4007647
theorem B7124705 : Blo 2109435 7124705 := bstep (se 2 (by rfl) ⟨2671764, by rfl⟩ : syracuseStep 7124705 = 5343529) B5343529
theorem B4749803 : Blo 2109435 4749803 := bstep (se 1 (by rfl) ⟨3562352, by rfl⟩ : syracuseStep 4749803 = 7124705) B7124705
theorem B3166535 : Blo 2109435 3166535 := bstep (se 1 (by rfl) ⟨2374901, by rfl⟩ : syracuseStep 3166535 = 4749803) B4749803
theorem B2111023 : Blo 2109435 2111023 := bstep (se 1 (by rfl) ⟨1583267, by rfl⟩ : syracuseStep 2111023 = 3166535) B3166535
theorem B3166541 : Blo 2109435 3166541 := bbase (se 3 (by rfl) ⟨593726, by rfl⟩ : syracuseStep 3166541 = 1187453) (by norm_num)
theorem B2111027 : Blo 2109435 2111027 := bstep (se 1 (by rfl) ⟨1583270, by rfl⟩ : syracuseStep 2111027 = 3166541) B3166541
theorem B4749821 : Blo 2109435 4749821 := bbase (se 3 (by rfl) ⟨890591, by rfl⟩ : syracuseStep 4749821 = 1781183) (by norm_num)
theorem B3166547 : Blo 2109435 3166547 := bstep (se 1 (by rfl) ⟨2374910, by rfl⟩ : syracuseStep 3166547 = 4749821) B4749821
theorem B2111031 : Blo 2109435 2111031 := bstep (se 1 (by rfl) ⟨1583273, by rfl⟩ : syracuseStep 2111031 = 3166547) B3166547
theorem B3562373 : Blo 2109435 3562373 := bbase (se 4 (by rfl) ⟨333972, by rfl⟩ : syracuseStep 3562373 = 667945) (by norm_num)
theorem B2374915 : Blo 2109435 2374915 := bstep (se 1 (by rfl) ⟨1781186, by rfl⟩ : syracuseStep 2374915 = 3562373) B3562373
theorem B3166553 : Blo 2109435 3166553 := bstep (se 2 (by rfl) ⟨1187457, by rfl⟩ : syracuseStep 3166553 = 2374915) B2374915
theorem B2111035 : Blo 2109435 2111035 := bstep (se 1 (by rfl) ⟨1583276, by rfl⟩ : syracuseStep 2111035 = 3166553) B3166553
theorem B16030709 : Blo 2109435 16030709 := bbase (se 5 (by rfl) ⟨751439, by rfl⟩ : syracuseStep 16030709 = 1502879) (by norm_num)
theorem B10687139 : Blo 2109435 10687139 := bstep (se 1 (by rfl) ⟨8015354, by rfl⟩ : syracuseStep 10687139 = 16030709) B16030709
theorem B7124759 : Blo 2109435 7124759 := bstep (se 1 (by rfl) ⟨5343569, by rfl⟩ : syracuseStep 7124759 = 10687139) B10687139
theorem B4749839 : Blo 2109435 4749839 := bstep (se 1 (by rfl) ⟨3562379, by rfl⟩ : syracuseStep 4749839 = 7124759) B7124759
theorem B3166559 : Blo 2109435 3166559 := bstep (se 1 (by rfl) ⟨2374919, by rfl⟩ : syracuseStep 3166559 = 4749839) B4749839
theorem B2111039 : Blo 2109435 2111039 := bstep (se 1 (by rfl) ⟨1583279, by rfl⟩ : syracuseStep 2111039 = 3166559) B3166559
theorem B3166565 : Blo 2109435 3166565 := bbase (se 4 (by rfl) ⟨296865, by rfl⟩ : syracuseStep 3166565 = 593731) (by norm_num)
theorem B2111043 : Blo 2109435 2111043 := bstep (se 1 (by rfl) ⟨1583282, by rfl⟩ : syracuseStep 2111043 = 3166565) B3166565
theorem B4007693 : Blo 2109435 4007693 := bbase (se 3 (by rfl) ⟨751442, by rfl⟩ : syracuseStep 4007693 = 1502885) (by norm_num)
theorem B2671795 : Blo 2109435 2671795 := bstep (se 1 (by rfl) ⟨2003846, by rfl⟩ : syracuseStep 2671795 = 4007693) B4007693
theorem B3562393 : Blo 2109435 3562393 := bstep (se 2 (by rfl) ⟨1335897, by rfl⟩ : syracuseStep 3562393 = 2671795) B2671795
theorem B4749857 : Blo 2109435 4749857 := bstep (se 2 (by rfl) ⟨1781196, by rfl⟩ : syracuseStep 4749857 = 3562393) B3562393
theorem B3166571 : Blo 2109435 3166571 := bstep (se 1 (by rfl) ⟨2374928, by rfl⟩ : syracuseStep 3166571 = 4749857) B4749857
theorem B2111047 : Blo 2109435 2111047 := bstep (se 1 (by rfl) ⟨1583285, by rfl⟩ : syracuseStep 2111047 = 3166571) B3166571
theorem B2374933 : Blo 2109435 2374933 := bbase (se 6 (by rfl) ⟨55662, by rfl⟩ : syracuseStep 2374933 = 111325) (by norm_num)
theorem B3166577 : Blo 2109435 3166577 := bstep (se 2 (by rfl) ⟨1187466, by rfl⟩ : syracuseStep 3166577 = 2374933) B2374933
theorem B2111051 : Blo 2109435 2111051 := bstep (se 1 (by rfl) ⟨1583288, by rfl⟩ : syracuseStep 2111051 = 3166577) B3166577
theorem B2671805 : Blo 2109435 2671805 := bbase (se 3 (by rfl) ⟨500963, by rfl⟩ : syracuseStep 2671805 = 1001927) (by norm_num)
theorem B7124813 : Blo 2109435 7124813 := bstep (se 3 (by rfl) ⟨1335902, by rfl⟩ : syracuseStep 7124813 = 2671805) B2671805
theorem B4749875 : Blo 2109435 4749875 := bstep (se 1 (by rfl) ⟨3562406, by rfl⟩ : syracuseStep 4749875 = 7124813) B7124813
theorem B3166583 : Blo 2109435 3166583 := bstep (se 1 (by rfl) ⟨2374937, by rfl⟩ : syracuseStep 3166583 = 4749875) B4749875
theorem B2111055 : Blo 2109435 2111055 := bstep (se 1 (by rfl) ⟨1583291, by rfl⟩ : syracuseStep 2111055 = 3166583) B3166583
theorem B3166589 : Blo 2109435 3166589 := bbase (se 3 (by rfl) ⟨593735, by rfl⟩ : syracuseStep 3166589 = 1187471) (by norm_num)
theorem B2111059 : Blo 2109435 2111059 := bstep (se 1 (by rfl) ⟨1583294, by rfl⟩ : syracuseStep 2111059 = 3166589) B3166589
theorem B4749893 : Blo 2109435 4749893 := bbase (se 4 (by rfl) ⟨445302, by rfl⟩ : syracuseStep 4749893 = 890605) (by norm_num)
theorem B3166595 : Blo 2109435 3166595 := bstep (se 1 (by rfl) ⟨2374946, by rfl⟩ : syracuseStep 3166595 = 4749893) B4749893
theorem B2111063 : Blo 2109435 2111063 := bstep (se 1 (by rfl) ⟨1583297, by rfl⟩ : syracuseStep 2111063 = 3166595) B3166595
theorem B2254349 : Blo 2109435 2254349 := bbase (se 3 (by rfl) ⟨422690, by rfl⟩ : syracuseStep 2254349 = 845381) (by norm_num)
theorem B6011597 : Blo 2109435 6011597 := bstep (se 3 (by rfl) ⟨1127174, by rfl⟩ : syracuseStep 6011597 = 2254349) B2254349
theorem B4007731 : Blo 2109435 4007731 := bstep (se 1 (by rfl) ⟨3005798, by rfl⟩ : syracuseStep 4007731 = 6011597) B6011597
theorem B5343641 : Blo 2109435 5343641 := bstep (se 2 (by rfl) ⟨2003865, by rfl⟩ : syracuseStep 5343641 = 4007731) B4007731
theorem B3562427 : Blo 2109435 3562427 := bstep (se 1 (by rfl) ⟨2671820, by rfl⟩ : syracuseStep 3562427 = 5343641) B5343641
theorem B2374951 : Blo 2109435 2374951 := bstep (se 1 (by rfl) ⟨1781213, by rfl⟩ : syracuseStep 2374951 = 3562427) B3562427
theorem B3166601 : Blo 2109435 3166601 := bstep (se 2 (by rfl) ⟨1187475, by rfl⟩ : syracuseStep 3166601 = 2374951) B2374951
theorem B2111067 : Blo 2109435 2111067 := bstep (se 1 (by rfl) ⟨1583300, by rfl⟩ : syracuseStep 2111067 = 3166601) B3166601
theorem B10687301 : Blo 2109435 10687301 := bbase (se 4 (by rfl) ⟨1001934, by rfl⟩ : syracuseStep 10687301 = 2003869) (by norm_num)
theorem B7124867 : Blo 2109435 7124867 := bstep (se 1 (by rfl) ⟨5343650, by rfl⟩ : syracuseStep 7124867 = 10687301) B10687301
theorem B4749911 : Blo 2109435 4749911 := bstep (se 1 (by rfl) ⟨3562433, by rfl⟩ : syracuseStep 4749911 = 7124867) B7124867
theorem B3166607 : Blo 2109435 3166607 := bstep (se 1 (by rfl) ⟨2374955, by rfl⟩ : syracuseStep 3166607 = 4749911) B4749911
theorem B2111071 : Blo 2109435 2111071 := bstep (se 1 (by rfl) ⟨1583303, by rfl⟩ : syracuseStep 2111071 = 3166607) B3166607
theorem B3166613 : Blo 2109435 3166613 := bbase (se 6 (by rfl) ⟨74217, by rfl⟩ : syracuseStep 3166613 = 148435) (by norm_num)
theorem B2111075 : Blo 2109435 2111075 := bstep (se 1 (by rfl) ⟨1583306, by rfl⟩ : syracuseStep 2111075 = 3166613) B3166613
theorem B2536157 : Blo 2109435 2536157 := bbase (se 3 (by rfl) ⟨475529, by rfl⟩ : syracuseStep 2536157 = 951059) (by norm_num)
theorem B6763085 : Blo 2109435 6763085 := bstep (se 3 (by rfl) ⟨1268078, by rfl⟩ : syracuseStep 6763085 = 2536157) B2536157
theorem B4508723 : Blo 2109435 4508723 := bstep (se 1 (by rfl) ⟨3381542, by rfl⟩ : syracuseStep 4508723 = 6763085) B6763085
theorem B12023261 : Blo 2109435 12023261 := bstep (se 3 (by rfl) ⟨2254361, by rfl⟩ : syracuseStep 12023261 = 4508723) B4508723
theorem B8015507 : Blo 2109435 8015507 := bstep (se 1 (by rfl) ⟨6011630, by rfl⟩ : syracuseStep 8015507 = 12023261) B12023261
theorem B5343671 : Blo 2109435 5343671 := bstep (se 1 (by rfl) ⟨4007753, by rfl⟩ : syracuseStep 5343671 = 8015507) B8015507
theorem B3562447 : Blo 2109435 3562447 := bstep (se 1 (by rfl) ⟨2671835, by rfl⟩ : syracuseStep 3562447 = 5343671) B5343671
theorem B4749929 : Blo 2109435 4749929 := bstep (se 2 (by rfl) ⟨1781223, by rfl⟩ : syracuseStep 4749929 = 3562447) B3562447
theorem B3166619 : Blo 2109435 3166619 := bstep (se 1 (by rfl) ⟨2374964, by rfl⟩ : syracuseStep 3166619 = 4749929) B4749929
theorem B2111079 : Blo 2109435 2111079 := bstep (se 1 (by rfl) ⟨1583309, by rfl⟩ : syracuseStep 2111079 = 3166619) B3166619
theorem B2374969 : Blo 2109435 2374969 := bbase (se 2 (by rfl) ⟨890613, by rfl⟩ : syracuseStep 2374969 = 1781227) (by norm_num)
theorem B3166625 : Blo 2109435 3166625 := bstep (se 2 (by rfl) ⟨1187484, by rfl⟩ : syracuseStep 3166625 = 2374969) B2374969
theorem B2111083 : Blo 2109435 2111083 := bstep (se 1 (by rfl) ⟨1583312, by rfl⟩ : syracuseStep 2111083 = 3166625) B3166625
theorem B6011653 : Blo 2109435 6011653 := bbase (se 4 (by rfl) ⟨563592, by rfl⟩ : syracuseStep 6011653 = 1127185) (by norm_num)
theorem B8015537 : Blo 2109435 8015537 := bstep (se 2 (by rfl) ⟨3005826, by rfl⟩ : syracuseStep 8015537 = 6011653) B6011653
theorem B5343691 : Blo 2109435 5343691 := bstep (se 1 (by rfl) ⟨4007768, by rfl⟩ : syracuseStep 5343691 = 8015537) B8015537
theorem B7124921 : Blo 2109435 7124921 := bstep (se 2 (by rfl) ⟨2671845, by rfl⟩ : syracuseStep 7124921 = 5343691) B5343691
theorem B4749947 : Blo 2109435 4749947 := bstep (se 1 (by rfl) ⟨3562460, by rfl⟩ : syracuseStep 4749947 = 7124921) B7124921
theorem B3166631 : Blo 2109435 3166631 := bstep (se 1 (by rfl) ⟨2374973, by rfl⟩ : syracuseStep 3166631 = 4749947) B4749947
theorem B2111087 : Blo 2109435 2111087 := bstep (se 1 (by rfl) ⟨1583315, by rfl⟩ : syracuseStep 2111087 = 3166631) B3166631
theorem B3166637 : Blo 2109435 3166637 := bbase (se 3 (by rfl) ⟨593744, by rfl⟩ : syracuseStep 3166637 = 1187489) (by norm_num)
theorem B2111091 : Blo 2109435 2111091 := bstep (se 1 (by rfl) ⟨1583318, by rfl⟩ : syracuseStep 2111091 = 3166637) B3166637
theorem B4749965 : Blo 2109435 4749965 := bbase (se 3 (by rfl) ⟨890618, by rfl⟩ : syracuseStep 4749965 = 1781237) (by norm_num)
theorem B3166643 : Blo 2109435 3166643 := bstep (se 1 (by rfl) ⟨2374982, by rfl⟩ : syracuseStep 3166643 = 4749965) B4749965
theorem B2111095 : Blo 2109435 2111095 := bstep (se 1 (by rfl) ⟨1583321, by rfl⟩ : syracuseStep 2111095 = 3166643) B3166643
theorem B2671861 : Blo 2109435 2671861 := bbase (se 5 (by rfl) ⟨125243, by rfl⟩ : syracuseStep 2671861 = 250487) (by norm_num)
theorem B3562481 : Blo 2109435 3562481 := bstep (se 2 (by rfl) ⟨1335930, by rfl⟩ : syracuseStep 3562481 = 2671861) B2671861
theorem B2374987 : Blo 2109435 2374987 := bstep (se 1 (by rfl) ⟨1781240, by rfl⟩ : syracuseStep 2374987 = 3562481) B3562481
theorem B3166649 : Blo 2109435 3166649 := bstep (se 2 (by rfl) ⟨1187493, by rfl⟩ : syracuseStep 3166649 = 2374987) B2374987
theorem B2111099 : Blo 2109435 2111099 := bstep (se 1 (by rfl) ⟨1583324, by rfl⟩ : syracuseStep 2111099 = 3166649) B3166649
theorem B40578965 : Blo 2109435 40578965 := bbase (se 6 (by rfl) ⟨951069, by rfl⟩ : syracuseStep 40578965 = 1902139) (by norm_num)
theorem B27052643 : Blo 2109435 27052643 := bstep (se 1 (by rfl) ⟨20289482, by rfl⟩ : syracuseStep 27052643 = 40578965) B40578965
theorem B18035095 : Blo 2109435 18035095 := bstep (se 1 (by rfl) ⟨13526321, by rfl⟩ : syracuseStep 18035095 = 27052643) B27052643
theorem B24046793 : Blo 2109435 24046793 := bstep (se 2 (by rfl) ⟨9017547, by rfl⟩ : syracuseStep 24046793 = 18035095) B18035095
theorem B16031195 : Blo 2109435 16031195 := bstep (se 1 (by rfl) ⟨12023396, by rfl⟩ : syracuseStep 16031195 = 24046793) B24046793
theorem B10687463 : Blo 2109435 10687463 := bstep (se 1 (by rfl) ⟨8015597, by rfl⟩ : syracuseStep 10687463 = 16031195) B16031195
theorem B7124975 : Blo 2109435 7124975 := bstep (se 1 (by rfl) ⟨5343731, by rfl⟩ : syracuseStep 7124975 = 10687463) B10687463
theorem B4749983 : Blo 2109435 4749983 := bstep (se 1 (by rfl) ⟨3562487, by rfl⟩ : syracuseStep 4749983 = 7124975) B7124975
theorem B3166655 : Blo 2109435 3166655 := bstep (se 1 (by rfl) ⟨2374991, by rfl⟩ : syracuseStep 3166655 = 4749983) B4749983
theorem B2111103 : Blo 2109435 2111103 := bstep (se 1 (by rfl) ⟨1583327, by rfl⟩ : syracuseStep 2111103 = 3166655) B3166655
theorem B3166661 : Blo 2109435 3166661 := bbase (se 4 (by rfl) ⟨296874, by rfl⟩ : syracuseStep 3166661 = 593749) (by norm_num)
theorem B2111107 : Blo 2109435 2111107 := bstep (se 1 (by rfl) ⟨1583330, by rfl⟩ : syracuseStep 2111107 = 3166661) B3166661
theorem B3562501 : Blo 2109435 3562501 := bbase (se 4 (by rfl) ⟨333984, by rfl⟩ : syracuseStep 3562501 = 667969) (by norm_num)
theorem B4750001 : Blo 2109435 4750001 := bstep (se 2 (by rfl) ⟨1781250, by rfl⟩ : syracuseStep 4750001 = 3562501) B3562501
theorem B3166667 : Blo 2109435 3166667 := bstep (se 1 (by rfl) ⟨2375000, by rfl⟩ : syracuseStep 3166667 = 4750001) B4750001
theorem B2111111 : Blo 2109435 2111111 := bstep (se 1 (by rfl) ⟨1583333, by rfl⟩ : syracuseStep 2111111 = 3166667) B3166667
theorem B2375005 : Blo 2109435 2375005 := bbase (se 3 (by rfl) ⟨445313, by rfl⟩ : syracuseStep 2375005 = 890627) (by norm_num)
theorem B3166673 : Blo 2109435 3166673 := bstep (se 2 (by rfl) ⟨1187502, by rfl⟩ : syracuseStep 3166673 = 2375005) B2375005
theorem B2111115 : Blo 2109435 2111115 := bstep (se 1 (by rfl) ⟨1583336, by rfl⟩ : syracuseStep 2111115 = 3166673) B3166673
theorem B7125029 : Blo 2109435 7125029 := bbase (se 4 (by rfl) ⟨667971, by rfl⟩ : syracuseStep 7125029 = 1335943) (by norm_num)
theorem B4750019 : Blo 2109435 4750019 := bstep (se 1 (by rfl) ⟨3562514, by rfl⟩ : syracuseStep 4750019 = 7125029) B7125029
theorem B3166679 : Blo 2109435 3166679 := bstep (se 1 (by rfl) ⟨2375009, by rfl⟩ : syracuseStep 3166679 = 4750019) B4750019
theorem B2111119 : Blo 2109435 2111119 := bstep (se 1 (by rfl) ⟨1583339, by rfl⟩ : syracuseStep 2111119 = 3166679) B3166679
theorem B3166685 : Blo 2109435 3166685 := bbase (se 3 (by rfl) ⟨593753, by rfl⟩ : syracuseStep 3166685 = 1187507) (by norm_num)
theorem B2111123 : Blo 2109435 2111123 := bstep (se 1 (by rfl) ⟨1583342, by rfl⟩ : syracuseStep 2111123 = 3166685) B3166685
theorem B4750037 : Blo 2109435 4750037 := bbase (se 7 (by rfl) ⟨55664, by rfl⟩ : syracuseStep 4750037 = 111329) (by norm_num)
theorem B3166691 : Blo 2109435 3166691 := bstep (se 1 (by rfl) ⟨2375018, by rfl⟩ : syracuseStep 3166691 = 4750037) B4750037
theorem B2111127 : Blo 2109435 2111127 := bstep (se 1 (by rfl) ⟨1583345, by rfl⟩ : syracuseStep 2111127 = 3166691) B3166691
theorem B9017669 : Blo 2109435 9017669 := bbase (se 4 (by rfl) ⟨845406, by rfl⟩ : syracuseStep 9017669 = 1690813) (by norm_num)
theorem B6011779 : Blo 2109435 6011779 := bstep (se 1 (by rfl) ⟨4508834, by rfl⟩ : syracuseStep 6011779 = 9017669) B9017669
theorem B8015705 : Blo 2109435 8015705 := bstep (se 2 (by rfl) ⟨3005889, by rfl⟩ : syracuseStep 8015705 = 6011779) B6011779
theorem B5343803 : Blo 2109435 5343803 := bstep (se 1 (by rfl) ⟨4007852, by rfl⟩ : syracuseStep 5343803 = 8015705) B8015705
theorem B3562535 : Blo 2109435 3562535 := bstep (se 1 (by rfl) ⟨2671901, by rfl⟩ : syracuseStep 3562535 = 5343803) B5343803
theorem B2375023 : Blo 2109435 2375023 := bstep (se 1 (by rfl) ⟨1781267, by rfl⟩ : syracuseStep 2375023 = 3562535) B3562535
theorem B3166697 : Blo 2109435 3166697 := bstep (se 2 (by rfl) ⟨1187511, by rfl⟩ : syracuseStep 3166697 = 2375023) B2375023
theorem B2111131 : Blo 2109435 2111131 := bstep (se 1 (by rfl) ⟨1583348, by rfl⟩ : syracuseStep 2111131 = 3166697) B3166697
theorem B3710357 : Blo 2109435 3710357 := bbase (se 6 (by rfl) ⟨86961, by rfl⟩ : syracuseStep 3710357 = 173923) (by norm_num)
theorem B2473571 : Blo 2109435 2473571 := bstep (se 1 (by rfl) ⟨1855178, by rfl⟩ : syracuseStep 2473571 = 3710357) B3710357
theorem B6596189 : Blo 2109435 6596189 := bstep (se 3 (by rfl) ⟨1236785, by rfl⟩ : syracuseStep 6596189 = 2473571) B2473571
theorem B4397459 : Blo 2109435 4397459 := bstep (se 1 (by rfl) ⟨3298094, by rfl⟩ : syracuseStep 4397459 = 6596189) B6596189
theorem B46906229 : Blo 2109435 46906229 := bstep (se 5 (by rfl) ⟨2198729, by rfl⟩ : syracuseStep 46906229 = 4397459) B4397459
theorem B31270819 : Blo 2109435 31270819 := bstep (se 1 (by rfl) ⟨23453114, by rfl⟩ : syracuseStep 31270819 = 46906229) B46906229
theorem B41694425 : Blo 2109435 41694425 := bstep (se 2 (by rfl) ⟨15635409, by rfl⟩ : syracuseStep 41694425 = 31270819) B31270819
theorem B27796283 : Blo 2109435 27796283 := bstep (se 1 (by rfl) ⟨20847212, by rfl⟩ : syracuseStep 27796283 = 41694425) B41694425
theorem B18530855 : Blo 2109435 18530855 := bstep (se 1 (by rfl) ⟨13898141, by rfl⟩ : syracuseStep 18530855 = 27796283) B27796283
theorem B12353903 : Blo 2109435 12353903 := bstep (se 1 (by rfl) ⟨9265427, by rfl⟩ : syracuseStep 12353903 = 18530855) B18530855
theorem B8235935 : Blo 2109435 8235935 := bstep (se 1 (by rfl) ⟨6176951, by rfl⟩ : syracuseStep 8235935 = 12353903) B12353903
theorem B5490623 : Blo 2109435 5490623 := bstep (se 1 (by rfl) ⟨4117967, by rfl⟩ : syracuseStep 5490623 = 8235935) B8235935
theorem B14641661 : Blo 2109435 14641661 := bstep (se 3 (by rfl) ⟨2745311, by rfl⟩ : syracuseStep 14641661 = 5490623) B5490623
theorem B39044429 : Blo 2109435 39044429 := bstep (se 3 (by rfl) ⟨7320830, by rfl⟩ : syracuseStep 39044429 = 14641661) B14641661
theorem B26029619 : Blo 2109435 26029619 := bstep (se 1 (by rfl) ⟨19522214, by rfl⟩ : syracuseStep 26029619 = 39044429) B39044429
theorem B17353079 : Blo 2109435 17353079 := bstep (se 1 (by rfl) ⟨13014809, by rfl⟩ : syracuseStep 17353079 = 26029619) B26029619
theorem B11568719 : Blo 2109435 11568719 := bstep (se 1 (by rfl) ⟨8676539, by rfl⟩ : syracuseStep 11568719 = 17353079) B17353079
theorem B30849917 : Blo 2109435 30849917 := bstep (se 3 (by rfl) ⟨5784359, by rfl⟩ : syracuseStep 30849917 = 11568719) B11568719
theorem B82266445 : Blo 2109435 82266445 := bstep (se 3 (by rfl) ⟨15424958, by rfl⟩ : syracuseStep 82266445 = 30849917) B30849917
theorem B109688593 : Blo 2109435 109688593 := bstep (se 2 (by rfl) ⟨41133222, by rfl⟩ : syracuseStep 109688593 = 82266445) B82266445
theorem B146251457 : Blo 2109435 146251457 := bstep (se 2 (by rfl) ⟨54844296, by rfl⟩ : syracuseStep 146251457 = 109688593) B109688593
theorem B97500971 : Blo 2109435 97500971 := bstep (se 1 (by rfl) ⟨73125728, by rfl⟩ : syracuseStep 97500971 = 146251457) B146251457
theorem B65000647 : Blo 2109435 65000647 := bstep (se 1 (by rfl) ⟨48750485, by rfl⟩ : syracuseStep 65000647 = 97500971) B97500971
theorem B346670117 : Blo 2109435 346670117 := bstep (se 4 (by rfl) ⟨32500323, by rfl⟩ : syracuseStep 346670117 = 65000647) B65000647
theorem B231113411 : Blo 2109435 231113411 := bstep (se 1 (by rfl) ⟨173335058, by rfl⟩ : syracuseStep 231113411 = 346670117) B346670117
theorem B154075607 : Blo 2109435 154075607 := bstep (se 1 (by rfl) ⟨115556705, by rfl⟩ : syracuseStep 154075607 = 231113411) B231113411
theorem B102717071 : Blo 2109435 102717071 := bstep (se 1 (by rfl) ⟨77037803, by rfl⟩ : syracuseStep 102717071 = 154075607) B154075607
theorem B68478047 : Blo 2109435 68478047 := bstep (se 1 (by rfl) ⟨51358535, by rfl⟩ : syracuseStep 68478047 = 102717071) B102717071
theorem B45652031 : Blo 2109435 45652031 := bstep (se 1 (by rfl) ⟨34239023, by rfl⟩ : syracuseStep 45652031 = 68478047) B68478047
theorem B30434687 : Blo 2109435 30434687 := bstep (se 1 (by rfl) ⟨22826015, by rfl⟩ : syracuseStep 30434687 = 45652031) B45652031
theorem B20289791 : Blo 2109435 20289791 := bstep (se 1 (by rfl) ⟨15217343, by rfl⟩ : syracuseStep 20289791 = 30434687) B30434687
theorem B13526527 : Blo 2109435 13526527 := bstep (se 1 (by rfl) ⟨10144895, by rfl⟩ : syracuseStep 13526527 = 20289791) B20289791
theorem B18035369 : Blo 2109435 18035369 := bstep (se 2 (by rfl) ⟨6763263, by rfl⟩ : syracuseStep 18035369 = 13526527) B13526527
theorem B12023579 : Blo 2109435 12023579 := bstep (se 1 (by rfl) ⟨9017684, by rfl⟩ : syracuseStep 12023579 = 18035369) B18035369
theorem B8015719 : Blo 2109435 8015719 := bstep (se 1 (by rfl) ⟨6011789, by rfl⟩ : syracuseStep 8015719 = 12023579) B12023579
theorem B10687625 : Blo 2109435 10687625 := bstep (se 2 (by rfl) ⟨4007859, by rfl⟩ : syracuseStep 10687625 = 8015719) B8015719
theorem B7125083 : Blo 2109435 7125083 := bstep (se 1 (by rfl) ⟨5343812, by rfl⟩ : syracuseStep 7125083 = 10687625) B10687625
theorem B4750055 : Blo 2109435 4750055 := bstep (se 1 (by rfl) ⟨3562541, by rfl⟩ : syracuseStep 4750055 = 7125083) B7125083
theorem B3166703 : Blo 2109435 3166703 := bstep (se 1 (by rfl) ⟨2375027, by rfl⟩ : syracuseStep 3166703 = 4750055) B4750055
theorem B2111135 : Blo 2109435 2111135 := bstep (se 1 (by rfl) ⟨1583351, by rfl⟩ : syracuseStep 2111135 = 3166703) B3166703
theorem B3166709 : Blo 2109435 3166709 := bbase (se 5 (by rfl) ⟨148439, by rfl⟩ : syracuseStep 3166709 = 296879) (by norm_num)
theorem B2111139 : Blo 2109435 2111139 := bstep (se 1 (by rfl) ⟨1583354, by rfl⟩ : syracuseStep 2111139 = 3166709) B3166709
theorem B6011813 : Blo 2109435 6011813 := bbase (se 4 (by rfl) ⟨563607, by rfl⟩ : syracuseStep 6011813 = 1127215) (by norm_num)
theorem B4007875 : Blo 2109435 4007875 := bstep (se 1 (by rfl) ⟨3005906, by rfl⟩ : syracuseStep 4007875 = 6011813) B6011813
theorem B5343833 : Blo 2109435 5343833 := bstep (se 2 (by rfl) ⟨2003937, by rfl⟩ : syracuseStep 5343833 = 4007875) B4007875
theorem B3562555 : Blo 2109435 3562555 := bstep (se 1 (by rfl) ⟨2671916, by rfl⟩ : syracuseStep 3562555 = 5343833) B5343833
theorem B4750073 : Blo 2109435 4750073 := bstep (se 2 (by rfl) ⟨1781277, by rfl⟩ : syracuseStep 4750073 = 3562555) B3562555
theorem B3166715 : Blo 2109435 3166715 := bstep (se 1 (by rfl) ⟨2375036, by rfl⟩ : syracuseStep 3166715 = 4750073) B4750073
theorem B2111143 : Blo 2109435 2111143 := bstep (se 1 (by rfl) ⟨1583357, by rfl⟩ : syracuseStep 2111143 = 3166715) B3166715
theorem B2375041 : Blo 2109435 2375041 := bbase (se 2 (by rfl) ⟨890640, by rfl⟩ : syracuseStep 2375041 = 1781281) (by norm_num)
theorem B3166721 : Blo 2109435 3166721 := bstep (se 2 (by rfl) ⟨1187520, by rfl⟩ : syracuseStep 3166721 = 2375041) B2375041
theorem B2111147 : Blo 2109435 2111147 := bstep (se 1 (by rfl) ⟨1583360, by rfl⟩ : syracuseStep 2111147 = 3166721) B3166721
theorem B5343853 : Blo 2109435 5343853 := bbase (se 3 (by rfl) ⟨1001972, by rfl⟩ : syracuseStep 5343853 = 2003945) (by norm_num)
theorem B7125137 : Blo 2109435 7125137 := bstep (se 2 (by rfl) ⟨2671926, by rfl⟩ : syracuseStep 7125137 = 5343853) B5343853
theorem B4750091 : Blo 2109435 4750091 := bstep (se 1 (by rfl) ⟨3562568, by rfl⟩ : syracuseStep 4750091 = 7125137) B7125137
theorem B3166727 : Blo 2109435 3166727 := bstep (se 1 (by rfl) ⟨2375045, by rfl⟩ : syracuseStep 3166727 = 4750091) B4750091
theorem B2111151 : Blo 2109435 2111151 := bstep (se 1 (by rfl) ⟨1583363, by rfl⟩ : syracuseStep 2111151 = 3166727) B3166727
theorem B3166733 : Blo 2109435 3166733 := bbase (se 3 (by rfl) ⟨593762, by rfl⟩ : syracuseStep 3166733 = 1187525) (by norm_num)
theorem B2111155 : Blo 2109435 2111155 := bstep (se 1 (by rfl) ⟨1583366, by rfl⟩ : syracuseStep 2111155 = 3166733) B3166733
theorem B4750109 : Blo 2109435 4750109 := bbase (se 3 (by rfl) ⟨890645, by rfl⟩ : syracuseStep 4750109 = 1781291) (by norm_num)
theorem B3166739 : Blo 2109435 3166739 := bstep (se 1 (by rfl) ⟨2375054, by rfl⟩ : syracuseStep 3166739 = 4750109) B4750109
theorem B2111159 : Blo 2109435 2111159 := bstep (se 1 (by rfl) ⟨1583369, by rfl⟩ : syracuseStep 2111159 = 3166739) B3166739
theorem B3562589 : Blo 2109435 3562589 := bbase (se 3 (by rfl) ⟨667985, by rfl⟩ : syracuseStep 3562589 = 1335971) (by norm_num)
theorem B2375059 : Blo 2109435 2375059 := bstep (se 1 (by rfl) ⟨1781294, by rfl⟩ : syracuseStep 2375059 = 3562589) B3562589
theorem B3166745 : Blo 2109435 3166745 := bstep (se 2 (by rfl) ⟨1187529, by rfl⟩ : syracuseStep 3166745 = 2375059) B2375059
theorem B2111163 : Blo 2109435 2111163 := bstep (se 1 (by rfl) ⟨1583372, by rfl⟩ : syracuseStep 2111163 = 3166745) B3166745
theorem B5072525 : Blo 2109435 5072525 := bbase (se 3 (by rfl) ⟨951098, by rfl⟩ : syracuseStep 5072525 = 1902197) (by norm_num)
theorem B3381683 : Blo 2109435 3381683 := bstep (se 1 (by rfl) ⟨2536262, by rfl⟩ : syracuseStep 3381683 = 5072525) B5072525
theorem B9017821 : Blo 2109435 9017821 := bstep (se 3 (by rfl) ⟨1690841, by rfl⟩ : syracuseStep 9017821 = 3381683) B3381683
theorem B12023761 : Blo 2109435 12023761 := bstep (se 2 (by rfl) ⟨4508910, by rfl⟩ : syracuseStep 12023761 = 9017821) B9017821
theorem B16031681 : Blo 2109435 16031681 := bstep (se 2 (by rfl) ⟨6011880, by rfl⟩ : syracuseStep 16031681 = 12023761) B12023761
theorem B10687787 : Blo 2109435 10687787 := bstep (se 1 (by rfl) ⟨8015840, by rfl⟩ : syracuseStep 10687787 = 16031681) B16031681
theorem B7125191 : Blo 2109435 7125191 := bstep (se 1 (by rfl) ⟨5343893, by rfl⟩ : syracuseStep 7125191 = 10687787) B10687787
theorem B4750127 : Blo 2109435 4750127 := bstep (se 1 (by rfl) ⟨3562595, by rfl⟩ : syracuseStep 4750127 = 7125191) B7125191
theorem B3166751 : Blo 2109435 3166751 := bstep (se 1 (by rfl) ⟨2375063, by rfl⟩ : syracuseStep 3166751 = 4750127) B4750127
theorem B2111167 : Blo 2109435 2111167 := bstep (se 1 (by rfl) ⟨1583375, by rfl⟩ : syracuseStep 2111167 = 3166751) B3166751
theorem B3166757 : Blo 2109435 3166757 := bbase (se 4 (by rfl) ⟨296883, by rfl⟩ : syracuseStep 3166757 = 593767) (by norm_num)
theorem B2111171 : Blo 2109435 2111171 := bstep (se 1 (by rfl) ⟨1583378, by rfl⟩ : syracuseStep 2111171 = 3166757) B3166757
theorem B2671957 : Blo 2109435 2671957 := bbase (se 12 (by rfl) ⟨978, by rfl⟩ : syracuseStep 2671957 = 1957) (by norm_num)
theorem B3562609 : Blo 2109435 3562609 := bstep (se 2 (by rfl) ⟨1335978, by rfl⟩ : syracuseStep 3562609 = 2671957) B2671957
theorem B4750145 : Blo 2109435 4750145 := bstep (se 2 (by rfl) ⟨1781304, by rfl⟩ : syracuseStep 4750145 = 3562609) B3562609
theorem B3166763 : Blo 2109435 3166763 := bstep (se 1 (by rfl) ⟨2375072, by rfl⟩ : syracuseStep 3166763 = 4750145) B4750145
theorem B2111175 : Blo 2109435 2111175 := bstep (se 1 (by rfl) ⟨1583381, by rfl⟩ : syracuseStep 2111175 = 3166763) B3166763
theorem B2375077 : Blo 2109435 2375077 := bbase (se 4 (by rfl) ⟨222663, by rfl⟩ : syracuseStep 2375077 = 445327) (by norm_num)
theorem B3166769 : Blo 2109435 3166769 := bstep (se 2 (by rfl) ⟨1187538, by rfl⟩ : syracuseStep 3166769 = 2375077) B2375077
theorem B2111179 : Blo 2109435 2111179 := bstep (se 1 (by rfl) ⟨1583384, by rfl⟩ : syracuseStep 2111179 = 3166769) B3166769
theorem B13526837 : Blo 2109435 13526837 := bbase (se 5 (by rfl) ⟨634070, by rfl⟩ : syracuseStep 13526837 = 1268141) (by norm_num)
theorem B9017891 : Blo 2109435 9017891 := bstep (se 1 (by rfl) ⟨6763418, by rfl⟩ : syracuseStep 9017891 = 13526837) B13526837
theorem B6011927 : Blo 2109435 6011927 := bstep (se 1 (by rfl) ⟨4508945, by rfl⟩ : syracuseStep 6011927 = 9017891) B9017891
theorem B4007951 : Blo 2109435 4007951 := bstep (se 1 (by rfl) ⟨3005963, by rfl⟩ : syracuseStep 4007951 = 6011927) B6011927
theorem B2671967 : Blo 2109435 2671967 := bstep (se 1 (by rfl) ⟨2003975, by rfl⟩ : syracuseStep 2671967 = 4007951) B4007951
theorem B7125245 : Blo 2109435 7125245 := bstep (se 3 (by rfl) ⟨1335983, by rfl⟩ : syracuseStep 7125245 = 2671967) B2671967
theorem B4750163 : Blo 2109435 4750163 := bstep (se 1 (by rfl) ⟨3562622, by rfl⟩ : syracuseStep 4750163 = 7125245) B7125245
theorem B3166775 : Blo 2109435 3166775 := bstep (se 1 (by rfl) ⟨2375081, by rfl⟩ : syracuseStep 3166775 = 4750163) B4750163
theorem B2111183 : Blo 2109435 2111183 := bstep (se 1 (by rfl) ⟨1583387, by rfl⟩ : syracuseStep 2111183 = 3166775) B3166775
theorem B3166781 : Blo 2109435 3166781 := bbase (se 3 (by rfl) ⟨593771, by rfl⟩ : syracuseStep 3166781 = 1187543) (by norm_num)
theorem B2111187 : Blo 2109435 2111187 := bstep (se 1 (by rfl) ⟨1583390, by rfl⟩ : syracuseStep 2111187 = 3166781) B3166781
theorem B4750181 : Blo 2109435 4750181 := bbase (se 4 (by rfl) ⟨445329, by rfl⟩ : syracuseStep 4750181 = 890659) (by norm_num)
theorem B3166787 : Blo 2109435 3166787 := bstep (se 1 (by rfl) ⟨2375090, by rfl⟩ : syracuseStep 3166787 = 4750181) B4750181
theorem B2111191 : Blo 2109435 2111191 := bstep (se 1 (by rfl) ⟨1583393, by rfl⟩ : syracuseStep 2111191 = 3166787) B3166787
theorem B5343965 : Blo 2109435 5343965 := bbase (se 3 (by rfl) ⟨1001993, by rfl⟩ : syracuseStep 5343965 = 2003987) (by norm_num)
theorem B3562643 : Blo 2109435 3562643 := bstep (se 1 (by rfl) ⟨2671982, by rfl⟩ : syracuseStep 3562643 = 5343965) B5343965
theorem B2375095 : Blo 2109435 2375095 := bstep (se 1 (by rfl) ⟨1781321, by rfl⟩ : syracuseStep 2375095 = 3562643) B3562643
theorem B3166793 : Blo 2109435 3166793 := bstep (se 2 (by rfl) ⟨1187547, by rfl⟩ : syracuseStep 3166793 = 2375095) B2375095
theorem B2111195 : Blo 2109435 2111195 := bstep (se 1 (by rfl) ⟨1583396, by rfl⟩ : syracuseStep 2111195 = 3166793) B3166793
theorem B4007981 : Blo 2109435 4007981 := bbase (se 3 (by rfl) ⟨751496, by rfl⟩ : syracuseStep 4007981 = 1502993) (by norm_num)
theorem B10687949 : Blo 2109435 10687949 := bstep (se 3 (by rfl) ⟨2003990, by rfl⟩ : syracuseStep 10687949 = 4007981) B4007981
theorem B7125299 : Blo 2109435 7125299 := bstep (se 1 (by rfl) ⟨5343974, by rfl⟩ : syracuseStep 7125299 = 10687949) B10687949
theorem B4750199 : Blo 2109435 4750199 := bstep (se 1 (by rfl) ⟨3562649, by rfl⟩ : syracuseStep 4750199 = 7125299) B7125299
theorem B3166799 : Blo 2109435 3166799 := bstep (se 1 (by rfl) ⟨2375099, by rfl⟩ : syracuseStep 3166799 = 4750199) B4750199
theorem B2111199 : Blo 2109435 2111199 := bstep (se 1 (by rfl) ⟨1583399, by rfl⟩ : syracuseStep 2111199 = 3166799) B3166799
theorem B3166805 : Blo 2109435 3166805 := bbase (se 8 (by rfl) ⟨18555, by rfl⟩ : syracuseStep 3166805 = 37111) (by norm_num)
theorem B2111203 : Blo 2109435 2111203 := bstep (se 1 (by rfl) ⟨1583402, by rfl⟩ : syracuseStep 2111203 = 3166805) B3166805
theorem B25680149 : Blo 2109435 25680149 := bbase (se 6 (by rfl) ⟨601878, by rfl⟩ : syracuseStep 25680149 = 1203757) (by norm_num)
theorem B17120099 : Blo 2109435 17120099 := bstep (se 1 (by rfl) ⟨12840074, by rfl⟩ : syracuseStep 17120099 = 25680149) B25680149
theorem B11413399 : Blo 2109435 11413399 := bstep (se 1 (by rfl) ⟨8560049, by rfl⟩ : syracuseStep 11413399 = 17120099) B17120099
theorem B15217865 : Blo 2109435 15217865 := bstep (se 2 (by rfl) ⟨5706699, by rfl⟩ : syracuseStep 15217865 = 11413399) B11413399
theorem B10145243 : Blo 2109435 10145243 := bstep (se 1 (by rfl) ⟨7608932, by rfl⟩ : syracuseStep 10145243 = 15217865) B15217865
theorem B6763495 : Blo 2109435 6763495 := bstep (se 1 (by rfl) ⟨5072621, by rfl⟩ : syracuseStep 6763495 = 10145243) B10145243
theorem B9017993 : Blo 2109435 9017993 := bstep (se 2 (by rfl) ⟨3381747, by rfl⟩ : syracuseStep 9017993 = 6763495) B6763495
theorem B6011995 : Blo 2109435 6011995 := bstep (se 1 (by rfl) ⟨4508996, by rfl⟩ : syracuseStep 6011995 = 9017993) B9017993
theorem B8015993 : Blo 2109435 8015993 := bstep (se 2 (by rfl) ⟨3005997, by rfl⟩ : syracuseStep 8015993 = 6011995) B6011995
theorem B5343995 : Blo 2109435 5343995 := bstep (se 1 (by rfl) ⟨4007996, by rfl⟩ : syracuseStep 5343995 = 8015993) B8015993
theorem B3562663 : Blo 2109435 3562663 := bstep (se 1 (by rfl) ⟨2671997, by rfl⟩ : syracuseStep 3562663 = 5343995) B5343995
theorem B4750217 : Blo 2109435 4750217 := bstep (se 2 (by rfl) ⟨1781331, by rfl⟩ : syracuseStep 4750217 = 3562663) B3562663
theorem B3166811 : Blo 2109435 3166811 := bstep (se 1 (by rfl) ⟨2375108, by rfl⟩ : syracuseStep 3166811 = 4750217) B4750217
theorem B2111207 : Blo 2109435 2111207 := bstep (se 1 (by rfl) ⟨1583405, by rfl⟩ : syracuseStep 2111207 = 3166811) B3166811
theorem B2375113 : Blo 2109435 2375113 := bbase (se 2 (by rfl) ⟨890667, by rfl⟩ : syracuseStep 2375113 = 1781335) (by norm_num)
theorem B3166817 : Blo 2109435 3166817 := bstep (se 2 (by rfl) ⟨1187556, by rfl⟩ : syracuseStep 3166817 = 2375113) B2375113
theorem B2111211 : Blo 2109435 2111211 := bstep (se 1 (by rfl) ⟨1583408, by rfl⟩ : syracuseStep 2111211 = 3166817) B3166817
theorem B18036053 : Blo 2109435 18036053 := bbase (se 13 (by rfl) ⟨3302, by rfl⟩ : syracuseStep 18036053 = 6605) (by norm_num)
theorem B12024035 : Blo 2109435 12024035 := bstep (se 1 (by rfl) ⟨9018026, by rfl⟩ : syracuseStep 12024035 = 18036053) B18036053
theorem B8016023 : Blo 2109435 8016023 := bstep (se 1 (by rfl) ⟨6012017, by rfl⟩ : syracuseStep 8016023 = 12024035) B12024035
theorem B5344015 : Blo 2109435 5344015 := bstep (se 1 (by rfl) ⟨4008011, by rfl⟩ : syracuseStep 5344015 = 8016023) B8016023
theorem B7125353 : Blo 2109435 7125353 := bstep (se 2 (by rfl) ⟨2672007, by rfl⟩ : syracuseStep 7125353 = 5344015) B5344015
theorem B4750235 : Blo 2109435 4750235 := bstep (se 1 (by rfl) ⟨3562676, by rfl⟩ : syracuseStep 4750235 = 7125353) B7125353
theorem B3166823 : Blo 2109435 3166823 := bstep (se 1 (by rfl) ⟨2375117, by rfl⟩ : syracuseStep 3166823 = 4750235) B4750235
theorem B2111215 : Blo 2109435 2111215 := bstep (se 1 (by rfl) ⟨1583411, by rfl⟩ : syracuseStep 2111215 = 3166823) B3166823
theorem B3166829 : Blo 2109435 3166829 := bbase (se 3 (by rfl) ⟨593780, by rfl⟩ : syracuseStep 3166829 = 1187561) (by norm_num)
theorem B2111219 : Blo 2109435 2111219 := bstep (se 1 (by rfl) ⟨1583414, by rfl⟩ : syracuseStep 2111219 = 3166829) B3166829
theorem B4750253 : Blo 2109435 4750253 := bbase (se 3 (by rfl) ⟨890672, by rfl⟩ : syracuseStep 4750253 = 1781345) (by norm_num)
theorem B3166835 : Blo 2109435 3166835 := bstep (se 1 (by rfl) ⟨2375126, by rfl⟩ : syracuseStep 3166835 = 4750253) B4750253
theorem B2111223 : Blo 2109435 2111223 := bstep (se 1 (by rfl) ⟨1583417, by rfl⟩ : syracuseStep 2111223 = 3166835) B3166835
theorem B6012053 : Blo 2109435 6012053 := bbase (se 6 (by rfl) ⟨140907, by rfl⟩ : syracuseStep 6012053 = 281815) (by norm_num)
theorem B4008035 : Blo 2109435 4008035 := bstep (se 1 (by rfl) ⟨3006026, by rfl⟩ : syracuseStep 4008035 = 6012053) B6012053
theorem B2672023 : Blo 2109435 2672023 := bstep (se 1 (by rfl) ⟨2004017, by rfl⟩ : syracuseStep 2672023 = 4008035) B4008035
theorem B3562697 : Blo 2109435 3562697 := bstep (se 2 (by rfl) ⟨1336011, by rfl⟩ : syracuseStep 3562697 = 2672023) B2672023
theorem B2375131 : Blo 2109435 2375131 := bstep (se 1 (by rfl) ⟨1781348, by rfl⟩ : syracuseStep 2375131 = 3562697) B3562697
theorem B3166841 : Blo 2109435 3166841 := bstep (se 2 (by rfl) ⟨1187565, by rfl⟩ : syracuseStep 3166841 = 2375131) B2375131
theorem B2111227 : Blo 2109435 2111227 := bstep (se 1 (by rfl) ⟨1583420, by rfl⟩ : syracuseStep 2111227 = 3166841) B3166841
theorem B2407541 : Blo 2109435 2407541 := bbase (se 5 (by rfl) ⟨112853, by rfl⟩ : syracuseStep 2407541 = 225707) (by norm_num)
theorem B6420109 : Blo 2109435 6420109 := bstep (se 3 (by rfl) ⟨1203770, by rfl⟩ : syracuseStep 6420109 = 2407541) B2407541
theorem B8560145 : Blo 2109435 8560145 := bstep (se 2 (by rfl) ⟨3210054, by rfl⟩ : syracuseStep 8560145 = 6420109) B6420109
theorem B5706763 : Blo 2109435 5706763 := bstep (se 1 (by rfl) ⟨4280072, by rfl⟩ : syracuseStep 5706763 = 8560145) B8560145
theorem B30436069 : Blo 2109435 30436069 := bstep (se 4 (by rfl) ⟨2853381, by rfl⟩ : syracuseStep 30436069 = 5706763) B5706763
theorem B40581425 : Blo 2109435 40581425 := bstep (se 2 (by rfl) ⟨15218034, by rfl⟩ : syracuseStep 40581425 = 30436069) B30436069
theorem B27054283 : Blo 2109435 27054283 := bstep (se 1 (by rfl) ⟨20290712, by rfl⟩ : syracuseStep 27054283 = 40581425) B40581425
theorem B36072377 : Blo 2109435 36072377 := bstep (se 2 (by rfl) ⟨13527141, by rfl⟩ : syracuseStep 36072377 = 27054283) B27054283
theorem B24048251 : Blo 2109435 24048251 := bstep (se 1 (by rfl) ⟨18036188, by rfl⟩ : syracuseStep 24048251 = 36072377) B36072377
theorem B16032167 : Blo 2109435 16032167 := bstep (se 1 (by rfl) ⟨12024125, by rfl⟩ : syracuseStep 16032167 = 24048251) B24048251
theorem B10688111 : Blo 2109435 10688111 := bstep (se 1 (by rfl) ⟨8016083, by rfl⟩ : syracuseStep 10688111 = 16032167) B16032167
theorem B7125407 : Blo 2109435 7125407 := bstep (se 1 (by rfl) ⟨5344055, by rfl⟩ : syracuseStep 7125407 = 10688111) B10688111
theorem B4750271 : Blo 2109435 4750271 := bstep (se 1 (by rfl) ⟨3562703, by rfl⟩ : syracuseStep 4750271 = 7125407) B7125407
theorem B3166847 : Blo 2109435 3166847 := bstep (se 1 (by rfl) ⟨2375135, by rfl⟩ : syracuseStep 3166847 = 4750271) B4750271
theorem B2111231 : Blo 2109435 2111231 := bstep (se 1 (by rfl) ⟨1583423, by rfl⟩ : syracuseStep 2111231 = 3166847) B3166847
theorem B3166853 : Blo 2109435 3166853 := bbase (se 4 (by rfl) ⟨296892, by rfl⟩ : syracuseStep 3166853 = 593785) (by norm_num)
theorem B2111235 : Blo 2109435 2111235 := bstep (se 1 (by rfl) ⟨1583426, by rfl⟩ : syracuseStep 2111235 = 3166853) B3166853
theorem B3562717 : Blo 2109435 3562717 := bbase (se 3 (by rfl) ⟨668009, by rfl⟩ : syracuseStep 3562717 = 1336019) (by norm_num)
theorem B4750289 : Blo 2109435 4750289 := bstep (se 2 (by rfl) ⟨1781358, by rfl⟩ : syracuseStep 4750289 = 3562717) B3562717
theorem B3166859 : Blo 2109435 3166859 := bstep (se 1 (by rfl) ⟨2375144, by rfl⟩ : syracuseStep 3166859 = 4750289) B4750289
theorem B2111239 : Blo 2109435 2111239 := bstep (se 1 (by rfl) ⟨1583429, by rfl⟩ : syracuseStep 2111239 = 3166859) B3166859
theorem B2375149 : Blo 2109435 2375149 := bbase (se 3 (by rfl) ⟨445340, by rfl⟩ : syracuseStep 2375149 = 890681) (by norm_num)
theorem B3166865 : Blo 2109435 3166865 := bstep (se 2 (by rfl) ⟨1187574, by rfl⟩ : syracuseStep 3166865 = 2375149) B2375149
theorem B2111243 : Blo 2109435 2111243 := bstep (se 1 (by rfl) ⟨1583432, by rfl⟩ : syracuseStep 2111243 = 3166865) B3166865
theorem B7125461 : Blo 2109435 7125461 := bbase (se 7 (by rfl) ⟨83501, by rfl⟩ : syracuseStep 7125461 = 167003) (by norm_num)
theorem B4750307 : Blo 2109435 4750307 := bstep (se 1 (by rfl) ⟨3562730, by rfl⟩ : syracuseStep 4750307 = 7125461) B7125461
theorem B3166871 : Blo 2109435 3166871 := bstep (se 1 (by rfl) ⟨2375153, by rfl⟩ : syracuseStep 3166871 = 4750307) B4750307
theorem B2111247 : Blo 2109435 2111247 := bstep (se 1 (by rfl) ⟨1583435, by rfl⟩ : syracuseStep 2111247 = 3166871) B3166871
theorem B3166877 : Blo 2109435 3166877 := bbase (se 3 (by rfl) ⟨593789, by rfl⟩ : syracuseStep 3166877 = 1187579) (by norm_num)
theorem B2111251 : Blo 2109435 2111251 := bstep (se 1 (by rfl) ⟨1583438, by rfl⟩ : syracuseStep 2111251 = 3166877) B3166877
theorem B4750325 : Blo 2109435 4750325 := bbase (se 5 (by rfl) ⟨222671, by rfl⟩ : syracuseStep 4750325 = 445343) (by norm_num)
theorem B3166883 : Blo 2109435 3166883 := bstep (se 1 (by rfl) ⟨2375162, by rfl⟩ : syracuseStep 3166883 = 4750325) B4750325
theorem B2111255 : Blo 2109435 2111255 := bstep (se 1 (by rfl) ⟨1583441, by rfl⟩ : syracuseStep 2111255 = 3166883) B3166883
theorem B2316493 : Blo 2109435 2316493 := bbase (se 3 (by rfl) ⟨434342, by rfl⟩ : syracuseStep 2316493 = 868685) (by norm_num)
theorem B12354629 : Blo 2109435 12354629 := bstep (se 4 (by rfl) ⟨1158246, by rfl⟩ : syracuseStep 12354629 = 2316493) B2316493
theorem B131782709 : Blo 2109435 131782709 := bstep (se 5 (by rfl) ⟨6177314, by rfl⟩ : syracuseStep 131782709 = 12354629) B12354629
theorem B87855139 : Blo 2109435 87855139 := bstep (se 1 (by rfl) ⟨65891354, by rfl⟩ : syracuseStep 87855139 = 131782709) B131782709
theorem B117140185 : Blo 2109435 117140185 := bstep (se 2 (by rfl) ⟨43927569, by rfl⟩ : syracuseStep 117140185 = 87855139) B87855139
theorem B156186913 : Blo 2109435 156186913 := bstep (se 2 (by rfl) ⟨58570092, by rfl⟩ : syracuseStep 156186913 = 117140185) B117140185
theorem B208249217 : Blo 2109435 208249217 := bstep (se 2 (by rfl) ⟨78093456, by rfl⟩ : syracuseStep 208249217 = 156186913) B156186913
theorem B138832811 : Blo 2109435 138832811 := bstep (se 1 (by rfl) ⟨104124608, by rfl⟩ : syracuseStep 138832811 = 208249217) B208249217
theorem B92555207 : Blo 2109435 92555207 := bstep (se 1 (by rfl) ⟨69416405, by rfl⟩ : syracuseStep 92555207 = 138832811) B138832811
theorem B61703471 : Blo 2109435 61703471 := bstep (se 1 (by rfl) ⟨46277603, by rfl⟩ : syracuseStep 61703471 = 92555207) B92555207
theorem B41135647 : Blo 2109435 41135647 := bstep (se 1 (by rfl) ⟨30851735, by rfl⟩ : syracuseStep 41135647 = 61703471) B61703471
theorem B54847529 : Blo 2109435 54847529 := bstep (se 2 (by rfl) ⟨20567823, by rfl⟩ : syracuseStep 54847529 = 41135647) B41135647
theorem B36565019 : Blo 2109435 36565019 := bstep (se 1 (by rfl) ⟨27423764, by rfl⟩ : syracuseStep 36565019 = 54847529) B54847529
theorem B24376679 : Blo 2109435 24376679 := bstep (se 1 (by rfl) ⟨18282509, by rfl⟩ : syracuseStep 24376679 = 36565019) B36565019
theorem B16251119 : Blo 2109435 16251119 := bstep (se 1 (by rfl) ⟨12188339, by rfl⟩ : syracuseStep 16251119 = 24376679) B24376679
theorem B10834079 : Blo 2109435 10834079 := bstep (se 1 (by rfl) ⟨8125559, by rfl⟩ : syracuseStep 10834079 = 16251119) B16251119
theorem B115563509 : Blo 2109435 115563509 := bstep (se 5 (by rfl) ⟨5417039, by rfl⟩ : syracuseStep 115563509 = 10834079) B10834079
theorem B77042339 : Blo 2109435 77042339 := bstep (se 1 (by rfl) ⟨57781754, by rfl⟩ : syracuseStep 77042339 = 115563509) B115563509
theorem B51361559 : Blo 2109435 51361559 := bstep (se 1 (by rfl) ⟨38521169, by rfl⟩ : syracuseStep 51361559 = 77042339) B77042339
theorem B34241039 : Blo 2109435 34241039 := bstep (se 1 (by rfl) ⟨25680779, by rfl⟩ : syracuseStep 34241039 = 51361559) B51361559
theorem B22827359 : Blo 2109435 22827359 := bstep (se 1 (by rfl) ⟨17120519, by rfl⟩ : syracuseStep 22827359 = 34241039) B34241039
theorem B60872957 : Blo 2109435 60872957 := bstep (se 3 (by rfl) ⟨11413679, by rfl⟩ : syracuseStep 60872957 = 22827359) B22827359
theorem B40581971 : Blo 2109435 40581971 := bstep (se 1 (by rfl) ⟨30436478, by rfl⟩ : syracuseStep 40581971 = 60872957) B60872957
theorem B27054647 : Blo 2109435 27054647 := bstep (se 1 (by rfl) ⟨20290985, by rfl⟩ : syracuseStep 27054647 = 40581971) B40581971
theorem B18036431 : Blo 2109435 18036431 := bstep (se 1 (by rfl) ⟨13527323, by rfl⟩ : syracuseStep 18036431 = 27054647) B27054647
theorem B12024287 : Blo 2109435 12024287 := bstep (se 1 (by rfl) ⟨9018215, by rfl⟩ : syracuseStep 12024287 = 18036431) B18036431
theorem B8016191 : Blo 2109435 8016191 := bstep (se 1 (by rfl) ⟨6012143, by rfl⟩ : syracuseStep 8016191 = 12024287) B12024287
theorem B5344127 : Blo 2109435 5344127 := bstep (se 1 (by rfl) ⟨4008095, by rfl⟩ : syracuseStep 5344127 = 8016191) B8016191
theorem B3562751 : Blo 2109435 3562751 := bstep (se 1 (by rfl) ⟨2672063, by rfl⟩ : syracuseStep 3562751 = 5344127) B5344127
theorem B2375167 : Blo 2109435 2375167 := bstep (se 1 (by rfl) ⟨1781375, by rfl⟩ : syracuseStep 2375167 = 3562751) B3562751
theorem B3166889 : Blo 2109435 3166889 := bstep (se 2 (by rfl) ⟨1187583, by rfl⟩ : syracuseStep 3166889 = 2375167) B2375167
theorem B2111259 : Blo 2109435 2111259 := bstep (se 1 (by rfl) ⟨1583444, by rfl⟩ : syracuseStep 2111259 = 3166889) B3166889
theorem B3006077 : Blo 2109435 3006077 := bbase (se 3 (by rfl) ⟨563639, by rfl⟩ : syracuseStep 3006077 = 1127279) (by norm_num)
theorem B8016205 : Blo 2109435 8016205 := bstep (se 3 (by rfl) ⟨1503038, by rfl⟩ : syracuseStep 8016205 = 3006077) B3006077
theorem B10688273 : Blo 2109435 10688273 := bstep (se 2 (by rfl) ⟨4008102, by rfl⟩ : syracuseStep 10688273 = 8016205) B8016205
theorem B7125515 : Blo 2109435 7125515 := bstep (se 1 (by rfl) ⟨5344136, by rfl⟩ : syracuseStep 7125515 = 10688273) B10688273
theorem B4750343 : Blo 2109435 4750343 := bstep (se 1 (by rfl) ⟨3562757, by rfl⟩ : syracuseStep 4750343 = 7125515) B7125515
theorem B3166895 : Blo 2109435 3166895 := bstep (se 1 (by rfl) ⟨2375171, by rfl⟩ : syracuseStep 3166895 = 4750343) B4750343
theorem B2111263 : Blo 2109435 2111263 := bstep (se 1 (by rfl) ⟨1583447, by rfl⟩ : syracuseStep 2111263 = 3166895) B3166895
theorem B3166901 : Blo 2109435 3166901 := bbase (se 5 (by rfl) ⟨148448, by rfl⟩ : syracuseStep 3166901 = 296897) (by norm_num)
theorem B2111267 : Blo 2109435 2111267 := bstep (se 1 (by rfl) ⟨1583450, by rfl⟩ : syracuseStep 2111267 = 3166901) B3166901
theorem B5344157 : Blo 2109435 5344157 := bbase (se 3 (by rfl) ⟨1002029, by rfl⟩ : syracuseStep 5344157 = 2004059) (by norm_num)
theorem B3562771 : Blo 2109435 3562771 := bstep (se 1 (by rfl) ⟨2672078, by rfl⟩ : syracuseStep 3562771 = 5344157) B5344157
theorem B4750361 : Blo 2109435 4750361 := bstep (se 2 (by rfl) ⟨1781385, by rfl⟩ : syracuseStep 4750361 = 3562771) B3562771
theorem B3166907 : Blo 2109435 3166907 := bstep (se 1 (by rfl) ⟨2375180, by rfl⟩ : syracuseStep 3166907 = 4750361) B4750361
theorem B2111271 : Blo 2109435 2111271 := bstep (se 1 (by rfl) ⟨1583453, by rfl⟩ : syracuseStep 2111271 = 3166907) B3166907
theorem B2375185 : Blo 2109435 2375185 := bbase (se 2 (by rfl) ⟨890694, by rfl⟩ : syracuseStep 2375185 = 1781389) (by norm_num)
theorem B3166913 : Blo 2109435 3166913 := bstep (se 2 (by rfl) ⟨1187592, by rfl⟩ : syracuseStep 3166913 = 2375185) B2375185
theorem B2111275 : Blo 2109435 2111275 := bstep (se 1 (by rfl) ⟨1583456, by rfl⟩ : syracuseStep 2111275 = 3166913) B3166913
theorem B4008133 : Blo 2109435 4008133 := bbase (se 4 (by rfl) ⟨375762, by rfl⟩ : syracuseStep 4008133 = 751525) (by norm_num)
theorem B5344177 : Blo 2109435 5344177 := bstep (se 2 (by rfl) ⟨2004066, by rfl⟩ : syracuseStep 5344177 = 4008133) B4008133
theorem B7125569 : Blo 2109435 7125569 := bstep (se 2 (by rfl) ⟨2672088, by rfl⟩ : syracuseStep 7125569 = 5344177) B5344177
theorem B4750379 : Blo 2109435 4750379 := bstep (se 1 (by rfl) ⟨3562784, by rfl⟩ : syracuseStep 4750379 = 7125569) B7125569
theorem B3166919 : Blo 2109435 3166919 := bstep (se 1 (by rfl) ⟨2375189, by rfl⟩ : syracuseStep 3166919 = 4750379) B4750379
theorem B2111279 : Blo 2109435 2111279 := bstep (se 1 (by rfl) ⟨1583459, by rfl⟩ : syracuseStep 2111279 = 3166919) B3166919
theorem B3166925 : Blo 2109435 3166925 := bbase (se 3 (by rfl) ⟨593798, by rfl⟩ : syracuseStep 3166925 = 1187597) (by norm_num)
theorem B2111283 : Blo 2109435 2111283 := bstep (se 1 (by rfl) ⟨1583462, by rfl⟩ : syracuseStep 2111283 = 3166925) B3166925
theorem B4750397 : Blo 2109435 4750397 := bbase (se 3 (by rfl) ⟨890699, by rfl⟩ : syracuseStep 4750397 = 1781399) (by norm_num)
theorem B3166931 : Blo 2109435 3166931 := bstep (se 1 (by rfl) ⟨2375198, by rfl⟩ : syracuseStep 3166931 = 4750397) B4750397
theorem B2111287 : Blo 2109435 2111287 := bstep (se 1 (by rfl) ⟨1583465, by rfl⟩ : syracuseStep 2111287 = 3166931) B3166931
theorem B3562805 : Blo 2109435 3562805 := bbase (se 5 (by rfl) ⟨167006, by rfl⟩ : syracuseStep 3562805 = 334013) (by norm_num)
theorem B2375203 : Blo 2109435 2375203 := bstep (se 1 (by rfl) ⟨1781402, by rfl⟩ : syracuseStep 2375203 = 3562805) B3562805
theorem B3166937 : Blo 2109435 3166937 := bstep (se 2 (by rfl) ⟨1187601, by rfl⟩ : syracuseStep 3166937 = 2375203) B2375203
theorem B2111291 : Blo 2109435 2111291 := bstep (se 1 (by rfl) ⟨1583468, by rfl⟩ : syracuseStep 2111291 = 3166937) B3166937
theorem B6012245 : Blo 2109435 6012245 := bbase (se 11 (by rfl) ⟨4403, by rfl⟩ : syracuseStep 6012245 = 8807) (by norm_num)
theorem B16032653 : Blo 2109435 16032653 := bstep (se 3 (by rfl) ⟨3006122, by rfl⟩ : syracuseStep 16032653 = 6012245) B6012245
theorem B10688435 : Blo 2109435 10688435 := bstep (se 1 (by rfl) ⟨8016326, by rfl⟩ : syracuseStep 10688435 = 16032653) B16032653
theorem B7125623 : Blo 2109435 7125623 := bstep (se 1 (by rfl) ⟨5344217, by rfl⟩ : syracuseStep 7125623 = 10688435) B10688435
theorem B4750415 : Blo 2109435 4750415 := bstep (se 1 (by rfl) ⟨3562811, by rfl⟩ : syracuseStep 4750415 = 7125623) B7125623
theorem B3166943 : Blo 2109435 3166943 := bstep (se 1 (by rfl) ⟨2375207, by rfl⟩ : syracuseStep 3166943 = 4750415) B4750415
theorem B2111295 : Blo 2109435 2111295 := bstep (se 1 (by rfl) ⟨1583471, by rfl⟩ : syracuseStep 2111295 = 3166943) B3166943
theorem B3166949 : Blo 2109435 3166949 := bbase (se 4 (by rfl) ⟨296901, by rfl⟩ : syracuseStep 3166949 = 593803) (by norm_num)
theorem B2111299 : Blo 2109435 2111299 := bstep (se 1 (by rfl) ⟨1583474, by rfl⟩ : syracuseStep 2111299 = 3166949) B3166949
theorem B2254601 : Blo 2109435 2254601 := bbase (se 2 (by rfl) ⟨845475, by rfl⟩ : syracuseStep 2254601 = 1690951) (by norm_num)
theorem B6012269 : Blo 2109435 6012269 := bstep (se 3 (by rfl) ⟨1127300, by rfl⟩ : syracuseStep 6012269 = 2254601) B2254601
theorem B4008179 : Blo 2109435 4008179 := bstep (se 1 (by rfl) ⟨3006134, by rfl⟩ : syracuseStep 4008179 = 6012269) B6012269
theorem B2672119 : Blo 2109435 2672119 := bstep (se 1 (by rfl) ⟨2004089, by rfl⟩ : syracuseStep 2672119 = 4008179) B4008179
theorem B3562825 : Blo 2109435 3562825 := bstep (se 2 (by rfl) ⟨1336059, by rfl⟩ : syracuseStep 3562825 = 2672119) B2672119
theorem B4750433 : Blo 2109435 4750433 := bstep (se 2 (by rfl) ⟨1781412, by rfl⟩ : syracuseStep 4750433 = 3562825) B3562825
theorem B3166955 : Blo 2109435 3166955 := bstep (se 1 (by rfl) ⟨2375216, by rfl⟩ : syracuseStep 3166955 = 4750433) B4750433
theorem B2111303 : Blo 2109435 2111303 := bstep (se 1 (by rfl) ⟨1583477, by rfl⟩ : syracuseStep 2111303 = 3166955) B3166955
theorem B2375221 : Blo 2109435 2375221 := bbase (se 5 (by rfl) ⟨111338, by rfl⟩ : syracuseStep 2375221 = 222677) (by norm_num)
theorem B3166961 : Blo 2109435 3166961 := bstep (se 2 (by rfl) ⟨1187610, by rfl⟩ : syracuseStep 3166961 = 2375221) B2375221
theorem B2111307 : Blo 2109435 2111307 := bstep (se 1 (by rfl) ⟨1583480, by rfl⟩ : syracuseStep 2111307 = 3166961) B3166961
theorem B2672129 : Blo 2109435 2672129 := bbase (se 2 (by rfl) ⟨1002048, by rfl⟩ : syracuseStep 2672129 = 2004097) (by norm_num)
theorem B7125677 : Blo 2109435 7125677 := bstep (se 3 (by rfl) ⟨1336064, by rfl⟩ : syracuseStep 7125677 = 2672129) B2672129
theorem B4750451 : Blo 2109435 4750451 := bstep (se 1 (by rfl) ⟨3562838, by rfl⟩ : syracuseStep 4750451 = 7125677) B7125677
theorem B3166967 : Blo 2109435 3166967 := bstep (se 1 (by rfl) ⟨2375225, by rfl⟩ : syracuseStep 3166967 = 4750451) B4750451
theorem B2111311 : Blo 2109435 2111311 := bstep (se 1 (by rfl) ⟨1583483, by rfl⟩ : syracuseStep 2111311 = 3166967) B3166967
theorem B3166973 : Blo 2109435 3166973 := bbase (se 3 (by rfl) ⟨593807, by rfl⟩ : syracuseStep 3166973 = 1187615) (by norm_num)
theorem B2111315 : Blo 2109435 2111315 := bstep (se 1 (by rfl) ⟨1583486, by rfl⟩ : syracuseStep 2111315 = 3166973) B3166973
theorem B4750469 : Blo 2109435 4750469 := bbase (se 4 (by rfl) ⟨445356, by rfl⟩ : syracuseStep 4750469 = 890713) (by norm_num)
theorem B3166979 : Blo 2109435 3166979 := bstep (se 1 (by rfl) ⟨2375234, by rfl⟩ : syracuseStep 3166979 = 4750469) B4750469
theorem B2111319 : Blo 2109435 2111319 := bstep (se 1 (by rfl) ⟨1583489, by rfl⟩ : syracuseStep 2111319 = 3166979) B3166979
theorem B4509245 : Blo 2109435 4509245 := bbase (se 3 (by rfl) ⟨845483, by rfl⟩ : syracuseStep 4509245 = 1690967) (by norm_num)
theorem B3006163 : Blo 2109435 3006163 := bstep (se 1 (by rfl) ⟨2254622, by rfl⟩ : syracuseStep 3006163 = 4509245) B4509245
theorem B4008217 : Blo 2109435 4008217 := bstep (se 2 (by rfl) ⟨1503081, by rfl⟩ : syracuseStep 4008217 = 3006163) B3006163
theorem B5344289 : Blo 2109435 5344289 := bstep (se 2 (by rfl) ⟨2004108, by rfl⟩ : syracuseStep 5344289 = 4008217) B4008217
theorem B3562859 : Blo 2109435 3562859 := bstep (se 1 (by rfl) ⟨2672144, by rfl⟩ : syracuseStep 3562859 = 5344289) B5344289
theorem B2375239 : Blo 2109435 2375239 := bstep (se 1 (by rfl) ⟨1781429, by rfl⟩ : syracuseStep 2375239 = 3562859) B3562859
theorem B3166985 : Blo 2109435 3166985 := bstep (se 2 (by rfl) ⟨1187619, by rfl⟩ : syracuseStep 3166985 = 2375239) B2375239
theorem B2111323 : Blo 2109435 2111323 := bstep (se 1 (by rfl) ⟨1583492, by rfl⟩ : syracuseStep 2111323 = 3166985) B3166985
theorem B10688597 : Blo 2109435 10688597 := bbase (se 8 (by rfl) ⟨62628, by rfl⟩ : syracuseStep 10688597 = 125257) (by norm_num)
theorem B7125731 : Blo 2109435 7125731 := bstep (se 1 (by rfl) ⟨5344298, by rfl⟩ : syracuseStep 7125731 = 10688597) B10688597
theorem B4750487 : Blo 2109435 4750487 := bstep (se 1 (by rfl) ⟨3562865, by rfl⟩ : syracuseStep 4750487 = 7125731) B7125731
theorem B3166991 : Blo 2109435 3166991 := bstep (se 1 (by rfl) ⟨2375243, by rfl⟩ : syracuseStep 3166991 = 4750487) B4750487
theorem B2111327 : Blo 2109435 2111327 := bstep (se 1 (by rfl) ⟨1583495, by rfl⟩ : syracuseStep 2111327 = 3166991) B3166991
theorem B3166997 : Blo 2109435 3166997 := bbase (se 6 (by rfl) ⟨74226, by rfl⟩ : syracuseStep 3166997 = 148453) (by norm_num)
theorem B2111331 : Blo 2109435 2111331 := bstep (se 1 (by rfl) ⟨1583498, by rfl⟩ : syracuseStep 2111331 = 3166997) B3166997
theorem B5707045 : Blo 2109435 5707045 := bbase (se 4 (by rfl) ⟨535035, by rfl⟩ : syracuseStep 5707045 = 1070071) (by norm_num)
theorem B7609393 : Blo 2109435 7609393 := bstep (se 2 (by rfl) ⟨2853522, by rfl⟩ : syracuseStep 7609393 = 5707045) B5707045
theorem B40583429 : Blo 2109435 40583429 := bstep (se 4 (by rfl) ⟨3804696, by rfl⟩ : syracuseStep 40583429 = 7609393) B7609393
theorem B27055619 : Blo 2109435 27055619 := bstep (se 1 (by rfl) ⟨20291714, by rfl⟩ : syracuseStep 27055619 = 40583429) B40583429
theorem B18037079 : Blo 2109435 18037079 := bstep (se 1 (by rfl) ⟨13527809, by rfl⟩ : syracuseStep 18037079 = 27055619) B27055619
theorem B12024719 : Blo 2109435 12024719 := bstep (se 1 (by rfl) ⟨9018539, by rfl⟩ : syracuseStep 12024719 = 18037079) B18037079
theorem B8016479 : Blo 2109435 8016479 := bstep (se 1 (by rfl) ⟨6012359, by rfl⟩ : syracuseStep 8016479 = 12024719) B12024719
theorem B5344319 : Blo 2109435 5344319 := bstep (se 1 (by rfl) ⟨4008239, by rfl⟩ : syracuseStep 5344319 = 8016479) B8016479
theorem B3562879 : Blo 2109435 3562879 := bstep (se 1 (by rfl) ⟨2672159, by rfl⟩ : syracuseStep 3562879 = 5344319) B5344319
theorem B4750505 : Blo 2109435 4750505 := bstep (se 2 (by rfl) ⟨1781439, by rfl⟩ : syracuseStep 4750505 = 3562879) B3562879
theorem B3167003 : Blo 2109435 3167003 := bstep (se 1 (by rfl) ⟨2375252, by rfl⟩ : syracuseStep 3167003 = 4750505) B4750505
theorem B2111335 : Blo 2109435 2111335 := bstep (se 1 (by rfl) ⟨1583501, by rfl⟩ : syracuseStep 2111335 = 3167003) B3167003
theorem B2375257 : Blo 2109435 2375257 := bbase (se 2 (by rfl) ⟨890721, by rfl⟩ : syracuseStep 2375257 = 1781443) (by norm_num)
theorem B3167009 : Blo 2109435 3167009 := bstep (se 2 (by rfl) ⟨1187628, by rfl⟩ : syracuseStep 3167009 = 2375257) B2375257
theorem B2111339 : Blo 2109435 2111339 := bstep (se 1 (by rfl) ⟨1583504, by rfl⟩ : syracuseStep 2111339 = 3167009) B3167009
theorem B9630677 : Blo 2109435 9630677 := bbase (se 7 (by rfl) ⟨112859, by rfl⟩ : syracuseStep 9630677 = 225719) (by norm_num)
theorem B25681805 : Blo 2109435 25681805 := bstep (se 3 (by rfl) ⟨4815338, by rfl⟩ : syracuseStep 25681805 = 9630677) B9630677
theorem B17121203 : Blo 2109435 17121203 := bstep (se 1 (by rfl) ⟨12840902, by rfl⟩ : syracuseStep 17121203 = 25681805) B25681805
theorem B11414135 : Blo 2109435 11414135 := bstep (se 1 (by rfl) ⟨8560601, by rfl⟩ : syracuseStep 11414135 = 17121203) B17121203
theorem B7609423 : Blo 2109435 7609423 := bstep (se 1 (by rfl) ⟨5707067, by rfl⟩ : syracuseStep 7609423 = 11414135) B11414135
theorem B10145897 : Blo 2109435 10145897 := bstep (se 2 (by rfl) ⟨3804711, by rfl⟩ : syracuseStep 10145897 = 7609423) B7609423
theorem B6763931 : Blo 2109435 6763931 := bstep (se 1 (by rfl) ⟨5072948, by rfl⟩ : syracuseStep 6763931 = 10145897) B10145897
theorem B4509287 : Blo 2109435 4509287 := bstep (se 1 (by rfl) ⟨3381965, by rfl⟩ : syracuseStep 4509287 = 6763931) B6763931
theorem B3006191 : Blo 2109435 3006191 := bstep (se 1 (by rfl) ⟨2254643, by rfl⟩ : syracuseStep 3006191 = 4509287) B4509287
theorem B8016509 : Blo 2109435 8016509 := bstep (se 3 (by rfl) ⟨1503095, by rfl⟩ : syracuseStep 8016509 = 3006191) B3006191
theorem B5344339 : Blo 2109435 5344339 := bstep (se 1 (by rfl) ⟨4008254, by rfl⟩ : syracuseStep 5344339 = 8016509) B8016509
theorem B7125785 : Blo 2109435 7125785 := bstep (se 2 (by rfl) ⟨2672169, by rfl⟩ : syracuseStep 7125785 = 5344339) B5344339
theorem B4750523 : Blo 2109435 4750523 := bstep (se 1 (by rfl) ⟨3562892, by rfl⟩ : syracuseStep 4750523 = 7125785) B7125785
theorem B3167015 : Blo 2109435 3167015 := bstep (se 1 (by rfl) ⟨2375261, by rfl⟩ : syracuseStep 3167015 = 4750523) B4750523
theorem B2111343 : Blo 2109435 2111343 := bstep (se 1 (by rfl) ⟨1583507, by rfl⟩ : syracuseStep 2111343 = 3167015) B3167015
theorem B3167021 : Blo 2109435 3167021 := bbase (se 3 (by rfl) ⟨593816, by rfl⟩ : syracuseStep 3167021 = 1187633) (by norm_num)
theorem B2111347 : Blo 2109435 2111347 := bstep (se 1 (by rfl) ⟨1583510, by rfl⟩ : syracuseStep 2111347 = 3167021) B3167021
theorem B4750541 : Blo 2109435 4750541 := bbase (se 3 (by rfl) ⟨890726, by rfl⟩ : syracuseStep 4750541 = 1781453) (by norm_num)
theorem B3167027 : Blo 2109435 3167027 := bstep (se 1 (by rfl) ⟨2375270, by rfl⟩ : syracuseStep 3167027 = 4750541) B4750541
theorem B2111351 : Blo 2109435 2111351 := bstep (se 1 (by rfl) ⟨1583513, by rfl⟩ : syracuseStep 2111351 = 3167027) B3167027
theorem B2672185 : Blo 2109435 2672185 := bbase (se 2 (by rfl) ⟨1002069, by rfl⟩ : syracuseStep 2672185 = 2004139) (by norm_num)
theorem B3562913 : Blo 2109435 3562913 := bstep (se 2 (by rfl) ⟨1336092, by rfl⟩ : syracuseStep 3562913 = 2672185) B2672185
theorem B2375275 : Blo 2109435 2375275 := bstep (se 1 (by rfl) ⟨1781456, by rfl⟩ : syracuseStep 2375275 = 3562913) B3562913
theorem B3167033 : Blo 2109435 3167033 := bstep (se 2 (by rfl) ⟨1187637, by rfl⟩ : syracuseStep 3167033 = 2375275) B2375275
theorem B2111355 : Blo 2109435 2111355 := bstep (se 1 (by rfl) ⟨1583516, by rfl⟩ : syracuseStep 2111355 = 3167033) B3167033
theorem B2536493 : Blo 2109435 2536493 := bbase (se 3 (by rfl) ⟨475592, by rfl⟩ : syracuseStep 2536493 = 951185) (by norm_num)
theorem B6763981 : Blo 2109435 6763981 := bstep (se 3 (by rfl) ⟨1268246, by rfl⟩ : syracuseStep 6763981 = 2536493) B2536493
theorem B9018641 : Blo 2109435 9018641 := bstep (se 2 (by rfl) ⟨3381990, by rfl⟩ : syracuseStep 9018641 = 6763981) B6763981
theorem B24049709 : Blo 2109435 24049709 := bstep (se 3 (by rfl) ⟨4509320, by rfl⟩ : syracuseStep 24049709 = 9018641) B9018641
theorem B16033139 : Blo 2109435 16033139 := bstep (se 1 (by rfl) ⟨12024854, by rfl⟩ : syracuseStep 16033139 = 24049709) B24049709
theorem B10688759 : Blo 2109435 10688759 := bstep (se 1 (by rfl) ⟨8016569, by rfl⟩ : syracuseStep 10688759 = 16033139) B16033139
theorem B7125839 : Blo 2109435 7125839 := bstep (se 1 (by rfl) ⟨5344379, by rfl⟩ : syracuseStep 7125839 = 10688759) B10688759
theorem B4750559 : Blo 2109435 4750559 := bstep (se 1 (by rfl) ⟨3562919, by rfl⟩ : syracuseStep 4750559 = 7125839) B7125839
theorem B3167039 : Blo 2109435 3167039 := bstep (se 1 (by rfl) ⟨2375279, by rfl⟩ : syracuseStep 3167039 = 4750559) B4750559
theorem B2111359 : Blo 2109435 2111359 := bstep (se 1 (by rfl) ⟨1583519, by rfl⟩ : syracuseStep 2111359 = 3167039) B3167039
theorem B3167045 : Blo 2109435 3167045 := bbase (se 4 (by rfl) ⟨296910, by rfl⟩ : syracuseStep 3167045 = 593821) (by norm_num)
theorem B2111363 : Blo 2109435 2111363 := bstep (se 1 (by rfl) ⟨1583522, by rfl⟩ : syracuseStep 2111363 = 3167045) B3167045
theorem B3562933 : Blo 2109435 3562933 := bbase (se 5 (by rfl) ⟨167012, by rfl⟩ : syracuseStep 3562933 = 334025) (by norm_num)
theorem B4750577 : Blo 2109435 4750577 := bstep (se 2 (by rfl) ⟨1781466, by rfl⟩ : syracuseStep 4750577 = 3562933) B3562933
theorem B3167051 : Blo 2109435 3167051 := bstep (se 1 (by rfl) ⟨2375288, by rfl⟩ : syracuseStep 3167051 = 4750577) B4750577
theorem B2111367 : Blo 2109435 2111367 := bstep (se 1 (by rfl) ⟨1583525, by rfl⟩ : syracuseStep 2111367 = 3167051) B3167051
theorem B2375293 : Blo 2109435 2375293 := bbase (se 3 (by rfl) ⟨445367, by rfl⟩ : syracuseStep 2375293 = 890735) (by norm_num)
theorem B3167057 : Blo 2109435 3167057 := bstep (se 2 (by rfl) ⟨1187646, by rfl⟩ : syracuseStep 3167057 = 2375293) B2375293
theorem B2111371 : Blo 2109435 2111371 := bstep (se 1 (by rfl) ⟨1583528, by rfl⟩ : syracuseStep 2111371 = 3167057) B3167057
theorem B7125893 : Blo 2109435 7125893 := bbase (se 4 (by rfl) ⟨668052, by rfl⟩ : syracuseStep 7125893 = 1336105) (by norm_num)
theorem B4750595 : Blo 2109435 4750595 := bstep (se 1 (by rfl) ⟨3562946, by rfl⟩ : syracuseStep 4750595 = 7125893) B7125893
theorem B3167063 : Blo 2109435 3167063 := bstep (se 1 (by rfl) ⟨2375297, by rfl⟩ : syracuseStep 3167063 = 4750595) B4750595
theorem B2111375 : Blo 2109435 2111375 := bstep (se 1 (by rfl) ⟨1583531, by rfl⟩ : syracuseStep 2111375 = 3167063) B3167063
theorem B3167069 : Blo 2109435 3167069 := bbase (se 3 (by rfl) ⟨593825, by rfl⟩ : syracuseStep 3167069 = 1187651) (by norm_num)
theorem B2111379 : Blo 2109435 2111379 := bstep (se 1 (by rfl) ⟨1583534, by rfl⟩ : syracuseStep 2111379 = 3167069) B3167069
theorem B4750613 : Blo 2109435 4750613 := bbase (se 6 (by rfl) ⟨111342, by rfl⟩ : syracuseStep 4750613 = 222685) (by norm_num)
theorem B3167075 : Blo 2109435 3167075 := bstep (se 1 (by rfl) ⟨2375306, by rfl⟩ : syracuseStep 3167075 = 4750613) B4750613
theorem B2111383 : Blo 2109435 2111383 := bstep (se 1 (by rfl) ⟨1583537, by rfl⟩ : syracuseStep 2111383 = 3167075) B3167075
theorem B8016677 : Blo 2109435 8016677 := bbase (se 4 (by rfl) ⟨751563, by rfl⟩ : syracuseStep 8016677 = 1503127) (by norm_num)
theorem B5344451 : Blo 2109435 5344451 := bstep (se 1 (by rfl) ⟨4008338, by rfl⟩ : syracuseStep 5344451 = 8016677) B8016677
theorem B3562967 : Blo 2109435 3562967 := bstep (se 1 (by rfl) ⟨2672225, by rfl⟩ : syracuseStep 3562967 = 5344451) B5344451
theorem B2375311 : Blo 2109435 2375311 := bstep (se 1 (by rfl) ⟨1781483, by rfl⟩ : syracuseStep 2375311 = 3562967) B3562967
theorem B3167081 : Blo 2109435 3167081 := bstep (se 2 (by rfl) ⟨1187655, by rfl⟩ : syracuseStep 3167081 = 2375311) B2375311
theorem B2111387 : Blo 2109435 2111387 := bstep (se 1 (by rfl) ⟨1583540, by rfl⟩ : syracuseStep 2111387 = 3167081) B3167081
theorem B4509389 : Blo 2109435 4509389 := bbase (se 3 (by rfl) ⟨845510, by rfl⟩ : syracuseStep 4509389 = 1691021) (by norm_num)
theorem B12025037 : Blo 2109435 12025037 := bstep (se 3 (by rfl) ⟨2254694, by rfl⟩ : syracuseStep 12025037 = 4509389) B4509389
theorem B8016691 : Blo 2109435 8016691 := bstep (se 1 (by rfl) ⟨6012518, by rfl⟩ : syracuseStep 8016691 = 12025037) B12025037
theorem B10688921 : Blo 2109435 10688921 := bstep (se 2 (by rfl) ⟨4008345, by rfl⟩ : syracuseStep 10688921 = 8016691) B8016691
theorem B7125947 : Blo 2109435 7125947 := bstep (se 1 (by rfl) ⟨5344460, by rfl⟩ : syracuseStep 7125947 = 10688921) B10688921
theorem B4750631 : Blo 2109435 4750631 := bstep (se 1 (by rfl) ⟨3562973, by rfl⟩ : syracuseStep 4750631 = 7125947) B7125947
theorem B3167087 : Blo 2109435 3167087 := bstep (se 1 (by rfl) ⟨2375315, by rfl⟩ : syracuseStep 3167087 = 4750631) B4750631
theorem B2111391 : Blo 2109435 2111391 := bstep (se 1 (by rfl) ⟨1583543, by rfl⟩ : syracuseStep 2111391 = 3167087) B3167087
theorem B3167093 : Blo 2109435 3167093 := bbase (se 5 (by rfl) ⟨148457, by rfl⟩ : syracuseStep 3167093 = 296915) (by norm_num)
theorem B2111395 : Blo 2109435 2111395 := bstep (se 1 (by rfl) ⟨1583546, by rfl⟩ : syracuseStep 2111395 = 3167093) B3167093
theorem B4570933 : Blo 2109435 4570933 := bbase (se 5 (by rfl) ⟨214262, by rfl⟩ : syracuseStep 4570933 = 428525) (by norm_num)
theorem B6094577 : Blo 2109435 6094577 := bstep (se 2 (by rfl) ⟨2285466, by rfl⟩ : syracuseStep 6094577 = 4570933) B4570933
theorem B4063051 : Blo 2109435 4063051 := bstep (se 1 (by rfl) ⟨3047288, by rfl⟩ : syracuseStep 4063051 = 6094577) B6094577
theorem B5417401 : Blo 2109435 5417401 := bstep (se 2 (by rfl) ⟨2031525, by rfl⟩ : syracuseStep 5417401 = 4063051) B4063051
theorem B7223201 : Blo 2109435 7223201 := bstep (se 2 (by rfl) ⟨2708700, by rfl⟩ : syracuseStep 7223201 = 5417401) B5417401
theorem B4815467 : Blo 2109435 4815467 := bstep (se 1 (by rfl) ⟨3611600, by rfl⟩ : syracuseStep 4815467 = 7223201) B7223201
theorem B3210311 : Blo 2109435 3210311 := bstep (se 1 (by rfl) ⟨2407733, by rfl⟩ : syracuseStep 3210311 = 4815467) B4815467
theorem B8560829 : Blo 2109435 8560829 := bstep (se 3 (by rfl) ⟨1605155, by rfl⟩ : syracuseStep 8560829 = 3210311) B3210311
theorem B22828877 : Blo 2109435 22828877 := bstep (se 3 (by rfl) ⟨4280414, by rfl⟩ : syracuseStep 22828877 = 8560829) B8560829
theorem B15219251 : Blo 2109435 15219251 := bstep (se 1 (by rfl) ⟨11414438, by rfl⟩ : syracuseStep 15219251 = 22828877) B22828877
theorem B10146167 : Blo 2109435 10146167 := bstep (se 1 (by rfl) ⟨7609625, by rfl⟩ : syracuseStep 10146167 = 15219251) B15219251
theorem B6764111 : Blo 2109435 6764111 := bstep (se 1 (by rfl) ⟨5073083, by rfl⟩ : syracuseStep 6764111 = 10146167) B10146167
theorem B4509407 : Blo 2109435 4509407 := bstep (se 1 (by rfl) ⟨3382055, by rfl⟩ : syracuseStep 4509407 = 6764111) B6764111
theorem B3006271 : Blo 2109435 3006271 := bstep (se 1 (by rfl) ⟨2254703, by rfl⟩ : syracuseStep 3006271 = 4509407) B4509407
theorem B4008361 : Blo 2109435 4008361 := bstep (se 2 (by rfl) ⟨1503135, by rfl⟩ : syracuseStep 4008361 = 3006271) B3006271
theorem B5344481 : Blo 2109435 5344481 := bstep (se 2 (by rfl) ⟨2004180, by rfl⟩ : syracuseStep 5344481 = 4008361) B4008361
theorem B3562987 : Blo 2109435 3562987 := bstep (se 1 (by rfl) ⟨2672240, by rfl⟩ : syracuseStep 3562987 = 5344481) B5344481
theorem B4750649 : Blo 2109435 4750649 := bstep (se 2 (by rfl) ⟨1781493, by rfl⟩ : syracuseStep 4750649 = 3562987) B3562987
theorem B3167099 : Blo 2109435 3167099 := bstep (se 1 (by rfl) ⟨2375324, by rfl⟩ : syracuseStep 3167099 = 4750649) B4750649
theorem B2111399 : Blo 2109435 2111399 := bstep (se 1 (by rfl) ⟨1583549, by rfl⟩ : syracuseStep 2111399 = 3167099) B3167099
theorem B2375329 : Blo 2109435 2375329 := bbase (se 2 (by rfl) ⟨890748, by rfl⟩ : syracuseStep 2375329 = 1781497) (by norm_num)
theorem B3167105 : Blo 2109435 3167105 := bstep (se 2 (by rfl) ⟨1187664, by rfl⟩ : syracuseStep 3167105 = 2375329) B2375329
theorem B2111403 : Blo 2109435 2111403 := bstep (se 1 (by rfl) ⟨1583552, by rfl⟩ : syracuseStep 2111403 = 3167105) B3167105
theorem B5344501 : Blo 2109435 5344501 := bbase (se 5 (by rfl) ⟨250523, by rfl⟩ : syracuseStep 5344501 = 501047) (by norm_num)
theorem B7126001 : Blo 2109435 7126001 := bstep (se 2 (by rfl) ⟨2672250, by rfl⟩ : syracuseStep 7126001 = 5344501) B5344501
theorem B4750667 : Blo 2109435 4750667 := bstep (se 1 (by rfl) ⟨3563000, by rfl⟩ : syracuseStep 4750667 = 7126001) B7126001
theorem B3167111 : Blo 2109435 3167111 := bstep (se 1 (by rfl) ⟨2375333, by rfl⟩ : syracuseStep 3167111 = 4750667) B4750667
theorem B2111407 : Blo 2109435 2111407 := bstep (se 1 (by rfl) ⟨1583555, by rfl⟩ : syracuseStep 2111407 = 3167111) B3167111
theorem B3167117 : Blo 2109435 3167117 := bbase (se 3 (by rfl) ⟨593834, by rfl⟩ : syracuseStep 3167117 = 1187669) (by norm_num)
theorem B2111411 : Blo 2109435 2111411 := bstep (se 1 (by rfl) ⟨1583558, by rfl⟩ : syracuseStep 2111411 = 3167117) B3167117
theorem B4750685 : Blo 2109435 4750685 := bbase (se 3 (by rfl) ⟨890753, by rfl⟩ : syracuseStep 4750685 = 1781507) (by norm_num)
theorem B3167123 : Blo 2109435 3167123 := bstep (se 1 (by rfl) ⟨2375342, by rfl⟩ : syracuseStep 3167123 = 4750685) B4750685
theorem B2111415 : Blo 2109435 2111415 := bstep (se 1 (by rfl) ⟨1583561, by rfl⟩ : syracuseStep 2111415 = 3167123) B3167123
theorem B3563021 : Blo 2109435 3563021 := bbase (se 3 (by rfl) ⟨668066, by rfl⟩ : syracuseStep 3563021 = 1336133) (by norm_num)
theorem B2375347 : Blo 2109435 2375347 := bstep (se 1 (by rfl) ⟨1781510, by rfl⟩ : syracuseStep 2375347 = 3563021) B3563021
theorem B3167129 : Blo 2109435 3167129 := bstep (se 2 (by rfl) ⟨1187673, by rfl⟩ : syracuseStep 3167129 = 2375347) B2375347
theorem B2111419 : Blo 2109435 2111419 := bstep (se 1 (by rfl) ⟨1583564, by rfl⟩ : syracuseStep 2111419 = 3167129) B3167129
theorem B3382093 : Blo 2109435 3382093 := bbase (se 3 (by rfl) ⟨634142, by rfl⟩ : syracuseStep 3382093 = 1268285) (by norm_num)
theorem B18037829 : Blo 2109435 18037829 := bstep (se 4 (by rfl) ⟨1691046, by rfl⟩ : syracuseStep 18037829 = 3382093) B3382093
theorem B12025219 : Blo 2109435 12025219 := bstep (se 1 (by rfl) ⟨9018914, by rfl⟩ : syracuseStep 12025219 = 18037829) B18037829
theorem B16033625 : Blo 2109435 16033625 := bstep (se 2 (by rfl) ⟨6012609, by rfl⟩ : syracuseStep 16033625 = 12025219) B12025219
theorem B10689083 : Blo 2109435 10689083 := bstep (se 1 (by rfl) ⟨8016812, by rfl⟩ : syracuseStep 10689083 = 16033625) B16033625
theorem B7126055 : Blo 2109435 7126055 := bstep (se 1 (by rfl) ⟨5344541, by rfl⟩ : syracuseStep 7126055 = 10689083) B10689083
theorem B4750703 : Blo 2109435 4750703 := bstep (se 1 (by rfl) ⟨3563027, by rfl⟩ : syracuseStep 4750703 = 7126055) B7126055
theorem B3167135 : Blo 2109435 3167135 := bstep (se 1 (by rfl) ⟨2375351, by rfl⟩ : syracuseStep 3167135 = 4750703) B4750703
theorem B2111423 : Blo 2109435 2111423 := bstep (se 1 (by rfl) ⟨1583567, by rfl⟩ : syracuseStep 2111423 = 3167135) B3167135
theorem B3167141 : Blo 2109435 3167141 := bbase (se 4 (by rfl) ⟨296919, by rfl⟩ : syracuseStep 3167141 = 593839) (by norm_num)
theorem B2111427 : Blo 2109435 2111427 := bstep (se 1 (by rfl) ⟨1583570, by rfl⟩ : syracuseStep 2111427 = 3167141) B3167141
theorem B2672281 : Blo 2109435 2672281 := bbase (se 2 (by rfl) ⟨1002105, by rfl⟩ : syracuseStep 2672281 = 2004211) (by norm_num)
theorem B3563041 : Blo 2109435 3563041 := bstep (se 2 (by rfl) ⟨1336140, by rfl⟩ : syracuseStep 3563041 = 2672281) B2672281
theorem B4750721 : Blo 2109435 4750721 := bstep (se 2 (by rfl) ⟨1781520, by rfl⟩ : syracuseStep 4750721 = 3563041) B3563041
theorem B3167147 : Blo 2109435 3167147 := bstep (se 1 (by rfl) ⟨2375360, by rfl⟩ : syracuseStep 3167147 = 4750721) B4750721
theorem B2111431 : Blo 2109435 2111431 := bstep (se 1 (by rfl) ⟨1583573, by rfl⟩ : syracuseStep 2111431 = 3167147) B3167147
theorem B2375365 : Blo 2109435 2375365 := bbase (se 4 (by rfl) ⟨222690, by rfl⟩ : syracuseStep 2375365 = 445381) (by norm_num)
theorem B3167153 : Blo 2109435 3167153 := bstep (se 2 (by rfl) ⟨1187682, by rfl⟩ : syracuseStep 3167153 = 2375365) B2375365
theorem B2111435 : Blo 2109435 2111435 := bstep (se 1 (by rfl) ⟨1583576, by rfl⟩ : syracuseStep 2111435 = 3167153) B3167153
theorem C0 (j : ℕ) (h1 : 527358 ≤ j) (h2 : j ≤ 527858) : Blo 2109435 (4 * j + 3) := by
  interval_cases j
  · exact B2109435
  · exact B2109439
  · exact B2109443
  · exact B2109447
  · exact B2109451
  · exact B2109455
  · exact B2109459
  · exact B2109463
  · exact B2109467
  · exact B2109471
  · exact B2109475
  · exact B2109479
  · exact B2109483
  · exact B2109487
  · exact B2109491
  · exact B2109495
  · exact B2109499
  · exact B2109503
  · exact B2109507
  · exact B2109511
  · exact B2109515
  · exact B2109519
  · exact B2109523
  · exact B2109527
  · exact B2109531
  · exact B2109535
  · exact B2109539
  · exact B2109543
  · exact B2109547
  · exact B2109551
  · exact B2109555
  · exact B2109559
  · exact B2109563
  · exact B2109567
  · exact B2109571
  · exact B2109575
  · exact B2109579
  · exact B2109583
  · exact B2109587
  · exact B2109591
  · exact B2109595
  · exact B2109599
  · exact B2109603
  · exact B2109607
  · exact B2109611
  · exact B2109615
  · exact B2109619
  · exact B2109623
  · exact B2109627
  · exact B2109631
  · exact B2109635
  · exact B2109639
  · exact B2109643
  · exact B2109647
  · exact B2109651
  · exact B2109655
  · exact B2109659
  · exact B2109663
  · exact B2109667
  · exact B2109671
  · exact B2109675
  · exact B2109679
  · exact B2109683
  · exact B2109687
  · exact B2109691
  · exact B2109695
  · exact B2109699
  · exact B2109703
  · exact B2109707
  · exact B2109711
  · exact B2109715
  · exact B2109719
  · exact B2109723
  · exact B2109727
  · exact B2109731
  · exact B2109735
  · exact B2109739
  · exact B2109743
  · exact B2109747
  · exact B2109751
  · exact B2109755
  · exact B2109759
  · exact B2109763
  · exact B2109767
  · exact B2109771
  · exact B2109775
  · exact B2109779
  · exact B2109783
  · exact B2109787
  · exact B2109791
  · exact B2109795
  · exact B2109799
  · exact B2109803
  · exact B2109807
  · exact B2109811
  · exact B2109815
  · exact B2109819
  · exact B2109823
  · exact B2109827
  · exact B2109831
  · exact B2109835
  · exact B2109839
  · exact B2109843
  · exact B2109847
  · exact B2109851
  · exact B2109855
  · exact B2109859
  · exact B2109863
  · exact B2109867
  · exact B2109871
  · exact B2109875
  · exact B2109879
  · exact B2109883
  · exact B2109887
  · exact B2109891
  · exact B2109895
  · exact B2109899
  · exact B2109903
  · exact B2109907
  · exact B2109911
  · exact B2109915
  · exact B2109919
  · exact B2109923
  · exact B2109927
  · exact B2109931
  · exact B2109935
  · exact B2109939
  · exact B2109943
  · exact B2109947
  · exact B2109951
  · exact B2109955
  · exact B2109959
  · exact B2109963
  · exact B2109967
  · exact B2109971
  · exact B2109975
  · exact B2109979
  · exact B2109983
  · exact B2109987
  · exact B2109991
  · exact B2109995
  · exact B2109999
  · exact B2110003
  · exact B2110007
  · exact B2110011
  · exact B2110015
  · exact B2110019
  · exact B2110023
  · exact B2110027
  · exact B2110031
  · exact B2110035
  · exact B2110039
  · exact B2110043
  · exact B2110047
  · exact B2110051
  · exact B2110055
  · exact B2110059
  · exact B2110063
  · exact B2110067
  · exact B2110071
  · exact B2110075
  · exact B2110079
  · exact B2110083
  · exact B2110087
  · exact B2110091
  · exact B2110095
  · exact B2110099
  · exact B2110103
  · exact B2110107
  · exact B2110111
  · exact B2110115
  · exact B2110119
  · exact B2110123
  · exact B2110127
  · exact B2110131
  · exact B2110135
  · exact B2110139
  · exact B2110143
  · exact B2110147
  · exact B2110151
  · exact B2110155
  · exact B2110159
  · exact B2110163
  · exact B2110167
  · exact B2110171
  · exact B2110175
  · exact B2110179
  · exact B2110183
  · exact B2110187
  · exact B2110191
  · exact B2110195
  · exact B2110199
  · exact B2110203
  · exact B2110207
  · exact B2110211
  · exact B2110215
  · exact B2110219
  · exact B2110223
  · exact B2110227
  · exact B2110231
  · exact B2110235
  · exact B2110239
  · exact B2110243
  · exact B2110247
  · exact B2110251
  · exact B2110255
  · exact B2110259
  · exact B2110263
  · exact B2110267
  · exact B2110271
  · exact B2110275
  · exact B2110279
  · exact B2110283
  · exact B2110287
  · exact B2110291
  · exact B2110295
  · exact B2110299
  · exact B2110303
  · exact B2110307
  · exact B2110311
  · exact B2110315
  · exact B2110319
  · exact B2110323
  · exact B2110327
  · exact B2110331
  · exact B2110335
  · exact B2110339
  · exact B2110343
  · exact B2110347
  · exact B2110351
  · exact B2110355
  · exact B2110359
  · exact B2110363
  · exact B2110367
  · exact B2110371
  · exact B2110375
  · exact B2110379
  · exact B2110383
  · exact B2110387
  · exact B2110391
  · exact B2110395
  · exact B2110399
  · exact B2110403
  · exact B2110407
  · exact B2110411
  · exact B2110415
  · exact B2110419
  · exact B2110423
  · exact B2110427
  · exact B2110431
  · exact B2110435
  · exact B2110439
  · exact B2110443
  · exact B2110447
  · exact B2110451
  · exact B2110455
  · exact B2110459
  · exact B2110463
  · exact B2110467
  · exact B2110471
  · exact B2110475
  · exact B2110479
  · exact B2110483
  · exact B2110487
  · exact B2110491
  · exact B2110495
  · exact B2110499
  · exact B2110503
  · exact B2110507
  · exact B2110511
  · exact B2110515
  · exact B2110519
  · exact B2110523
  · exact B2110527
  · exact B2110531
  · exact B2110535
  · exact B2110539
  · exact B2110543
  · exact B2110547
  · exact B2110551
  · exact B2110555
  · exact B2110559
  · exact B2110563
  · exact B2110567
  · exact B2110571
  · exact B2110575
  · exact B2110579
  · exact B2110583
  · exact B2110587
  · exact B2110591
  · exact B2110595
  · exact B2110599
  · exact B2110603
  · exact B2110607
  · exact B2110611
  · exact B2110615
  · exact B2110619
  · exact B2110623
  · exact B2110627
  · exact B2110631
  · exact B2110635
  · exact B2110639
  · exact B2110643
  · exact B2110647
  · exact B2110651
  · exact B2110655
  · exact B2110659
  · exact B2110663
  · exact B2110667
  · exact B2110671
  · exact B2110675
  · exact B2110679
  · exact B2110683
  · exact B2110687
  · exact B2110691
  · exact B2110695
  · exact B2110699
  · exact B2110703
  · exact B2110707
  · exact B2110711
  · exact B2110715
  · exact B2110719
  · exact B2110723
  · exact B2110727
  · exact B2110731
  · exact B2110735
  · exact B2110739
  · exact B2110743
  · exact B2110747
  · exact B2110751
  · exact B2110755
  · exact B2110759
  · exact B2110763
  · exact B2110767
  · exact B2110771
  · exact B2110775
  · exact B2110779
  · exact B2110783
  · exact B2110787
  · exact B2110791
  · exact B2110795
  · exact B2110799
  · exact B2110803
  · exact B2110807
  · exact B2110811
  · exact B2110815
  · exact B2110819
  · exact B2110823
  · exact B2110827
  · exact B2110831
  · exact B2110835
  · exact B2110839
  · exact B2110843
  · exact B2110847
  · exact B2110851
  · exact B2110855
  · exact B2110859
  · exact B2110863
  · exact B2110867
  · exact B2110871
  · exact B2110875
  · exact B2110879
  · exact B2110883
  · exact B2110887
  · exact B2110891
  · exact B2110895
  · exact B2110899
  · exact B2110903
  · exact B2110907
  · exact B2110911
  · exact B2110915
  · exact B2110919
  · exact B2110923
  · exact B2110927
  · exact B2110931
  · exact B2110935
  · exact B2110939
  · exact B2110943
  · exact B2110947
  · exact B2110951
  · exact B2110955
  · exact B2110959
  · exact B2110963
  · exact B2110967
  · exact B2110971
  · exact B2110975
  · exact B2110979
  · exact B2110983
  · exact B2110987
  · exact B2110991
  · exact B2110995
  · exact B2110999
  · exact B2111003
  · exact B2111007
  · exact B2111011
  · exact B2111015
  · exact B2111019
  · exact B2111023
  · exact B2111027
  · exact B2111031
  · exact B2111035
  · exact B2111039
  · exact B2111043
  · exact B2111047
  · exact B2111051
  · exact B2111055
  · exact B2111059
  · exact B2111063
  · exact B2111067
  · exact B2111071
  · exact B2111075
  · exact B2111079
  · exact B2111083
  · exact B2111087
  · exact B2111091
  · exact B2111095
  · exact B2111099
  · exact B2111103
  · exact B2111107
  · exact B2111111
  · exact B2111115
  · exact B2111119
  · exact B2111123
  · exact B2111127
  · exact B2111131
  · exact B2111135
  · exact B2111139
  · exact B2111143
  · exact B2111147
  · exact B2111151
  · exact B2111155
  · exact B2111159
  · exact B2111163
  · exact B2111167
  · exact B2111171
  · exact B2111175
  · exact B2111179
  · exact B2111183
  · exact B2111187
  · exact B2111191
  · exact B2111195
  · exact B2111199
  · exact B2111203
  · exact B2111207
  · exact B2111211
  · exact B2111215
  · exact B2111219
  · exact B2111223
  · exact B2111227
  · exact B2111231
  · exact B2111235
  · exact B2111239
  · exact B2111243
  · exact B2111247
  · exact B2111251
  · exact B2111255
  · exact B2111259
  · exact B2111263
  · exact B2111267
  · exact B2111271
  · exact B2111275
  · exact B2111279
  · exact B2111283
  · exact B2111287
  · exact B2111291
  · exact B2111295
  · exact B2111299
  · exact B2111303
  · exact B2111307
  · exact B2111311
  · exact B2111315
  · exact B2111319
  · exact B2111323
  · exact B2111327
  · exact B2111331
  · exact B2111335
  · exact B2111339
  · exact B2111343
  · exact B2111347
  · exact B2111351
  · exact B2111355
  · exact B2111359
  · exact B2111363
  · exact B2111367
  · exact B2111371
  · exact B2111375
  · exact B2111379
  · exact B2111383
  · exact B2111387
  · exact B2111391
  · exact B2111395
  · exact B2111399
  · exact B2111403
  · exact B2111407
  · exact B2111411
  · exact B2111415
  · exact B2111419
  · exact B2111423
  · exact B2111427
  · exact B2111431
  · exact B2111435
theorem solution (m : ℕ) (hlo : 2109435 ≤ m) (hhi : m ≤ 2111435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 527358 ≤ j := by omega
    have hj2 : j ≤ 527858 := by omega
    have hb : Blo 2109435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
