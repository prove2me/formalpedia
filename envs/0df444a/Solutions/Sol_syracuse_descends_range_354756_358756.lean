-- Prove2me | solution 1 for syracuse_descends_range_354756_358756
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T17:47:37.476123+00:00
-- url     : https://prove2.me/submissions/fa0b0a51-cc63-424b-ae57-edcfb98d14a0

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


theorem B458897 : Blo 354756 458897 := bbase (se 2 (by rfl) ⟨172086, by rfl⟩ : syracuseStep 458897 = 344173) (by norm_num)
theorem B4063445 : Blo 354756 4063445 := bbase (se 7 (by rfl) ⟨47618, by rfl⟩ : syracuseStep 4063445 = 95237) (by norm_num)
theorem B426241 : Blo 354756 426241 := bbase (se 2 (by rfl) ⟨159840, by rfl⟩ : syracuseStep 426241 = 319681) (by norm_num)
theorem B885109 : Blo 354756 885109 := bbase (se 5 (by rfl) ⟨41489, by rfl⟩ : syracuseStep 885109 = 82979) (by norm_num)
theorem B361117 : Blo 354756 361117 := bbase (se 3 (by rfl) ⟨67709, by rfl⟩ : syracuseStep 361117 = 135419) (by norm_num)
theorem B459497 : Blo 354756 459497 := bbase (se 2 (by rfl) ⟨172311, by rfl⟩ : syracuseStep 459497 = 344623) (by norm_num)
theorem B1147765 : Blo 354756 1147765 := bbase (se 5 (by rfl) ⟨53801, by rfl⟩ : syracuseStep 1147765 = 107603) (by norm_num)
theorem B721813 : Blo 354756 721813 := bbase (se 6 (by rfl) ⟨16917, by rfl⟩ : syracuseStep 721813 = 33835) (by norm_num)
theorem B852925 : Blo 354756 852925 := bbase (se 3 (by rfl) ⟨159923, by rfl⟩ : syracuseStep 852925 = 319847) (by norm_num)
theorem B721877 : Blo 354756 721877 := bbase (se 7 (by rfl) ⟨8459, by rfl⟩ : syracuseStep 721877 = 16919) (by norm_num)
theorem B1803221 : Blo 354756 1803221 := bbase (se 7 (by rfl) ⟨21131, by rfl⟩ : syracuseStep 1803221 = 42263) (by norm_num)
theorem B853021 : Blo 354756 853021 := bbase (se 3 (by rfl) ⟨159941, by rfl⟩ : syracuseStep 853021 = 319883) (by norm_num)
theorem B853213 : Blo 354756 853213 := bbase (se 3 (by rfl) ⟨159977, by rfl⟩ : syracuseStep 853213 = 319955) (by norm_num)
theorem B427241 : Blo 354756 427241 := bbase (se 2 (by rfl) ⟨160215, by rfl⟩ : syracuseStep 427241 = 320431) (by norm_num)
theorem B361733 : Blo 354756 361733 := bbase (se 4 (by rfl) ⟨33912, by rfl⟩ : syracuseStep 361733 = 67825) (by norm_num)
theorem B1148165 : Blo 354756 1148165 := bbase (se 4 (by rfl) ⟨107640, by rfl⟩ : syracuseStep 1148165 = 215281) (by norm_num)
theorem B2033045 : Blo 354756 2033045 := bbase (se 6 (by rfl) ⟨47649, by rfl⟩ : syracuseStep 2033045 = 95299) (by norm_num)
theorem B361945 : Blo 354756 361945 := bbase (se 2 (by rfl) ⟨135729, by rfl⟩ : syracuseStep 361945 = 271459) (by norm_num)
theorem B427529 : Blo 354756 427529 := bbase (se 2 (by rfl) ⟨160323, by rfl⟩ : syracuseStep 427529 = 320647) (by norm_num)
theorem B853541 : Blo 354756 853541 := bbase (se 4 (by rfl) ⟨80019, by rfl⟩ : syracuseStep 853541 = 160039) (by norm_num)
theorem B427693 : Blo 354756 427693 := bbase (se 3 (by rfl) ⟨80192, by rfl⟩ : syracuseStep 427693 = 160385) (by norm_num)
theorem B427721 : Blo 354756 427721 := bbase (se 2 (by rfl) ⟨160395, by rfl⟩ : syracuseStep 427721 = 320791) (by norm_num)
theorem B362281 : Blo 354756 362281 := bbase (se 2 (by rfl) ⟨135855, by rfl⟩ : syracuseStep 362281 = 271711) (by norm_num)
theorem B427837 : Blo 354756 427837 := bbase (se 3 (by rfl) ⟨80219, by rfl⟩ : syracuseStep 427837 = 160439) (by norm_num)
theorem B427933 : Blo 354756 427933 := bbase (se 3 (by rfl) ⟨80237, by rfl⟩ : syracuseStep 427933 = 160475) (by norm_num)
theorem B853973 : Blo 354756 853973 := bbase (se 7 (by rfl) ⟨10007, by rfl⟩ : syracuseStep 853973 = 20015) (by norm_num)
theorem B362561 : Blo 354756 362561 := bbase (se 2 (by rfl) ⟨135960, by rfl⟩ : syracuseStep 362561 = 271921) (by norm_num)
theorem B1804517 : Blo 354756 1804517 := bbase (se 4 (by rfl) ⟨169173, by rfl⟩ : syracuseStep 1804517 = 338347) (by norm_num)
theorem B5146901 : Blo 354756 5146901 := bbase (se 6 (by rfl) ⟨120630, by rfl⟩ : syracuseStep 5146901 = 241261) (by norm_num)
theorem B854309 : Blo 354756 854309 := bbase (se 4 (by rfl) ⟨80091, by rfl⟩ : syracuseStep 854309 = 160183) (by norm_num)
theorem B428413 : Blo 354756 428413 := bbase (se 3 (by rfl) ⟨80327, by rfl⟩ : syracuseStep 428413 = 160655) (by norm_num)
theorem B1018277 : Blo 354756 1018277 := bbase (se 4 (by rfl) ⟨95463, by rfl⟩ : syracuseStep 1018277 = 190927) (by norm_num)
theorem B1215157 : Blo 354756 1215157 := bbase (se 5 (by rfl) ⟨56960, by rfl⟩ : syracuseStep 1215157 = 113921) (by norm_num)
theorem B1084229 : Blo 354756 1084229 := bbase (se 4 (by rfl) ⟨101646, by rfl⟩ : syracuseStep 1084229 = 203293) (by norm_num)
theorem B3476405 : Blo 354756 3476405 := bbase (se 5 (by rfl) ⟨162956, by rfl⟩ : syracuseStep 3476405 = 325913) (by norm_num)
theorem B724133 : Blo 354756 724133 := bbase (se 4 (by rfl) ⟨67887, by rfl⟩ : syracuseStep 724133 = 135775) (by norm_num)
theorem B855365 : Blo 354756 855365 := bbase (se 4 (by rfl) ⟨80190, by rfl⟩ : syracuseStep 855365 = 160381) (by norm_num)
theorem B1805813 : Blo 354756 1805813 := bbase (se 5 (by rfl) ⟨84647, by rfl⟩ : syracuseStep 1805813 = 169295) (by norm_num)
theorem B1019461 : Blo 354756 1019461 := bbase (se 4 (by rfl) ⟨95574, by rfl⟩ : syracuseStep 1019461 = 191149) (by norm_num)
theorem B2297429 : Blo 354756 2297429 := bbase (se 8 (by rfl) ⟨13461, by rfl⟩ : syracuseStep 2297429 = 26923) (by norm_num)
theorem B1707637 : Blo 354756 1707637 := bbase (se 5 (by rfl) ⟨80045, by rfl⟩ : syracuseStep 1707637 = 160091) (by norm_num)
theorem B1216133 : Blo 354756 1216133 := bbase (se 4 (by rfl) ⟨114012, by rfl⟩ : syracuseStep 1216133 = 228025) (by norm_num)
theorem B429797 : Blo 354756 429797 := bbase (se 4 (by rfl) ⟨40293, by rfl⟩ : syracuseStep 429797 = 80587) (by norm_num)
theorem B1019621 : Blo 354756 1019621 := bbase (se 4 (by rfl) ⟨95589, by rfl⟩ : syracuseStep 1019621 = 191179) (by norm_num)
theorem B429985 : Blo 354756 429985 := bbase (se 2 (by rfl) ⟨161244, by rfl⟩ : syracuseStep 429985 = 322489) (by norm_num)
theorem B1019861 : Blo 354756 1019861 := bbase (se 7 (by rfl) ⟨11951, by rfl⟩ : syracuseStep 1019861 = 23903) (by norm_num)
theorem B430201 : Blo 354756 430201 := bbase (se 2 (by rfl) ⟨161325, by rfl⟩ : syracuseStep 430201 = 322651) (by norm_num)
theorem B1020053 : Blo 354756 1020053 := bbase (se 6 (by rfl) ⟨23907, by rfl⟩ : syracuseStep 1020053 = 47815) (by norm_num)
theorem B3117365 : Blo 354756 3117365 := bbase (se 5 (by rfl) ⟨146126, by rfl⟩ : syracuseStep 3117365 = 292253) (by norm_num)
theorem B430489 : Blo 354756 430489 := bbase (se 2 (by rfl) ⟨161433, by rfl⟩ : syracuseStep 430489 = 322867) (by norm_num)
theorem B1282645 : Blo 354756 1282645 := bbase (se 8 (by rfl) ⟨7515, by rfl⟩ : syracuseStep 1282645 = 15031) (by norm_num)
theorem B1807109 : Blo 354756 1807109 := bbase (se 4 (by rfl) ⟨169416, by rfl⟩ : syracuseStep 1807109 = 338833) (by norm_num)
theorem B726013 : Blo 354756 726013 := bbase (se 3 (by rfl) ⟨136127, by rfl⟩ : syracuseStep 726013 = 272255) (by norm_num)
theorem B758821 : Blo 354756 758821 := bbase (se 4 (by rfl) ⟨71139, by rfl⟩ : syracuseStep 758821 = 142279) (by norm_num)
theorem B1840229 : Blo 354756 1840229 := bbase (se 4 (by rfl) ⟨172521, by rfl⟩ : syracuseStep 1840229 = 345043) (by norm_num)
theorem B1021045 : Blo 354756 1021045 := bbase (se 5 (by rfl) ⟨47861, by rfl⟩ : syracuseStep 1021045 = 95723) (by norm_num)
theorem B1348757 : Blo 354756 1348757 := bbase (se 6 (by rfl) ⟨31611, by rfl⟩ : syracuseStep 1348757 = 63223) (by norm_num)
theorem B464233 : Blo 354756 464233 := bbase (se 2 (by rfl) ⟨174087, by rfl⟩ : syracuseStep 464233 = 348175) (by norm_num)
theorem B1349045 : Blo 354756 1349045 := bbase (se 5 (by rfl) ⟨63236, by rfl⟩ : syracuseStep 1349045 = 126473) (by norm_num)
theorem B857557 : Blo 354756 857557 := bbase (se 7 (by rfl) ⟨10049, by rfl⟩ : syracuseStep 857557 = 20099) (by norm_num)
theorem B2168309 : Blo 354756 2168309 := bbase (se 5 (by rfl) ⟨101639, by rfl⟩ : syracuseStep 2168309 = 203279) (by norm_num)
theorem B399109 : Blo 354756 399109 := bbase (se 4 (by rfl) ⟨37416, by rfl⟩ : syracuseStep 399109 = 74833) (by norm_num)
theorem B628517 : Blo 354756 628517 := bbase (se 4 (by rfl) ⟨58923, by rfl⟩ : syracuseStep 628517 = 117847) (by norm_num)
theorem B399145 : Blo 354756 399145 := bbase (se 2 (by rfl) ⟨149679, by rfl⟩ : syracuseStep 399145 = 299359) (by norm_num)
theorem B399181 : Blo 354756 399181 := bbase (se 3 (by rfl) ⟨74846, by rfl⟩ : syracuseStep 399181 = 149693) (by norm_num)
theorem B399217 : Blo 354756 399217 := bbase (se 2 (by rfl) ⟨149706, by rfl⟩ : syracuseStep 399217 = 299413) (by norm_num)
theorem B399253 : Blo 354756 399253 := bbase (se 6 (by rfl) ⟨9357, by rfl⟩ : syracuseStep 399253 = 18715) (by norm_num)
theorem B759709 : Blo 354756 759709 := bbase (se 3 (by rfl) ⟨142445, by rfl⟩ : syracuseStep 759709 = 284891) (by norm_num)
theorem B399289 : Blo 354756 399289 := bbase (se 2 (by rfl) ⟨149733, by rfl⟩ : syracuseStep 399289 = 299467) (by norm_num)
theorem B399325 : Blo 354756 399325 := bbase (se 3 (by rfl) ⟨74873, by rfl⟩ : syracuseStep 399325 = 149747) (by norm_num)
theorem B399361 : Blo 354756 399361 := bbase (se 2 (by rfl) ⟨149760, by rfl⟩ : syracuseStep 399361 = 299521) (by norm_num)
theorem B1808405 : Blo 354756 1808405 := bbase (se 6 (by rfl) ⟨42384, by rfl⟩ : syracuseStep 1808405 = 84769) (by norm_num)
theorem B399397 : Blo 354756 399397 := bbase (se 4 (by rfl) ⟨37443, by rfl⟩ : syracuseStep 399397 = 74887) (by norm_num)
theorem B399433 : Blo 354756 399433 := bbase (se 2 (by rfl) ⟨149787, by rfl⟩ : syracuseStep 399433 = 299575) (by norm_num)
theorem B399469 : Blo 354756 399469 := bbase (se 3 (by rfl) ⟨74900, by rfl⟩ : syracuseStep 399469 = 149801) (by norm_num)
theorem B727157 : Blo 354756 727157 := bbase (se 5 (by rfl) ⟨34085, by rfl⟩ : syracuseStep 727157 = 68171) (by norm_num)
theorem B399505 : Blo 354756 399505 := bbase (se 2 (by rfl) ⟨149814, by rfl⟩ : syracuseStep 399505 = 299629) (by norm_num)
theorem B399541 : Blo 354756 399541 := bbase (se 5 (by rfl) ⟨18728, by rfl⟩ : syracuseStep 399541 = 37457) (by norm_num)
theorem B727229 : Blo 354756 727229 := bbase (se 3 (by rfl) ⟨136355, by rfl⟩ : syracuseStep 727229 = 272711) (by norm_num)
theorem B399577 : Blo 354756 399577 := bbase (se 2 (by rfl) ⟨149841, by rfl⟩ : syracuseStep 399577 = 299683) (by norm_num)
theorem B399613 : Blo 354756 399613 := bbase (se 3 (by rfl) ⟨74927, by rfl⟩ : syracuseStep 399613 = 149855) (by norm_num)
theorem B399649 : Blo 354756 399649 := bbase (se 2 (by rfl) ⟨149868, by rfl⟩ : syracuseStep 399649 = 299737) (by norm_num)
theorem B399685 : Blo 354756 399685 := bbase (se 4 (by rfl) ⟨37470, by rfl⟩ : syracuseStep 399685 = 74941) (by norm_num)
theorem B399721 : Blo 354756 399721 := bbase (se 2 (by rfl) ⟨149895, by rfl⟩ : syracuseStep 399721 = 299791) (by norm_num)
theorem B399757 : Blo 354756 399757 := bbase (se 3 (by rfl) ⟨74954, by rfl⟩ : syracuseStep 399757 = 149909) (by norm_num)
theorem B760205 : Blo 354756 760205 := bbase (se 3 (by rfl) ⟨142538, by rfl⟩ : syracuseStep 760205 = 285077) (by norm_num)
theorem B399793 : Blo 354756 399793 := bbase (se 2 (by rfl) ⟨149922, by rfl⟩ : syracuseStep 399793 = 299845) (by norm_num)
theorem B399829 : Blo 354756 399829 := bbase (se 7 (by rfl) ⟨4685, by rfl⟩ : syracuseStep 399829 = 9371) (by norm_num)
theorem B399865 : Blo 354756 399865 := bbase (se 2 (by rfl) ⟨149949, by rfl⟩ : syracuseStep 399865 = 299899) (by norm_num)
theorem B399901 : Blo 354756 399901 := bbase (se 3 (by rfl) ⟨74981, by rfl⟩ : syracuseStep 399901 = 149963) (by norm_num)
theorem B399937 : Blo 354756 399937 := bbase (se 2 (by rfl) ⟨149976, by rfl⟩ : syracuseStep 399937 = 299953) (by norm_num)
theorem B1350229 : Blo 354756 1350229 := bbase (se 8 (by rfl) ⟨7911, by rfl⟩ : syracuseStep 1350229 = 15823) (by norm_num)
theorem B399973 : Blo 354756 399973 := bbase (se 4 (by rfl) ⟨37497, by rfl⟩ : syracuseStep 399973 = 74995) (by norm_num)
theorem B400009 : Blo 354756 400009 := bbase (se 2 (by rfl) ⟨150003, by rfl⟩ : syracuseStep 400009 = 300007) (by norm_num)
theorem B400045 : Blo 354756 400045 := bbase (se 3 (by rfl) ⟨75008, by rfl⟩ : syracuseStep 400045 = 150017) (by norm_num)
theorem B400081 : Blo 354756 400081 := bbase (se 2 (by rfl) ⟨150030, by rfl⟩ : syracuseStep 400081 = 300061) (by norm_num)
theorem B400117 : Blo 354756 400117 := bbase (se 5 (by rfl) ⟨18755, by rfl⟩ : syracuseStep 400117 = 37511) (by norm_num)
theorem B400153 : Blo 354756 400153 := bbase (se 2 (by rfl) ⟨150057, by rfl⟩ : syracuseStep 400153 = 300115) (by norm_num)
theorem B400189 : Blo 354756 400189 := bbase (se 3 (by rfl) ⟨75035, by rfl⟩ : syracuseStep 400189 = 150071) (by norm_num)
theorem B858941 : Blo 354756 858941 := bbase (se 3 (by rfl) ⟨161051, by rfl⟩ : syracuseStep 858941 = 322103) (by norm_num)
theorem B400225 : Blo 354756 400225 := bbase (se 2 (by rfl) ⟨150084, by rfl⟩ : syracuseStep 400225 = 300169) (by norm_num)
theorem B1350533 : Blo 354756 1350533 := bbase (se 4 (by rfl) ⟨126612, by rfl⟩ : syracuseStep 1350533 = 253225) (by norm_num)
theorem B400261 : Blo 354756 400261 := bbase (se 4 (by rfl) ⟨37524, by rfl⟩ : syracuseStep 400261 = 75049) (by norm_num)
theorem B400297 : Blo 354756 400297 := bbase (se 2 (by rfl) ⟨150111, by rfl⟩ : syracuseStep 400297 = 300223) (by norm_num)
theorem B400333 : Blo 354756 400333 := bbase (se 3 (by rfl) ⟨75062, by rfl⟩ : syracuseStep 400333 = 150125) (by norm_num)
theorem B400369 : Blo 354756 400369 := bbase (se 2 (by rfl) ⟨150138, by rfl⟩ : syracuseStep 400369 = 300277) (by norm_num)
theorem B859133 : Blo 354756 859133 := bbase (se 3 (by rfl) ⟨161087, by rfl⟩ : syracuseStep 859133 = 322175) (by norm_num)
theorem B400405 : Blo 354756 400405 := bbase (se 6 (by rfl) ⟨9384, by rfl⟩ : syracuseStep 400405 = 18769) (by norm_num)
theorem B400441 : Blo 354756 400441 := bbase (se 2 (by rfl) ⟨150165, by rfl⟩ : syracuseStep 400441 = 300331) (by norm_num)
theorem B400477 : Blo 354756 400477 := bbase (se 3 (by rfl) ⟨75089, by rfl⟩ : syracuseStep 400477 = 150179) (by norm_num)
theorem B400513 : Blo 354756 400513 := bbase (se 2 (by rfl) ⟨150192, by rfl⟩ : syracuseStep 400513 = 300385) (by norm_num)
theorem B400549 : Blo 354756 400549 := bbase (se 4 (by rfl) ⟨37551, by rfl⟩ : syracuseStep 400549 = 75103) (by norm_num)
theorem B400585 : Blo 354756 400585 := bbase (se 2 (by rfl) ⟨150219, by rfl⟩ : syracuseStep 400585 = 300439) (by norm_num)
theorem B400621 : Blo 354756 400621 := bbase (se 3 (by rfl) ⟨75116, by rfl⟩ : syracuseStep 400621 = 150233) (by norm_num)
theorem B761069 : Blo 354756 761069 := bbase (se 3 (by rfl) ⟨142700, by rfl⟩ : syracuseStep 761069 = 285401) (by norm_num)
theorem B400657 : Blo 354756 400657 := bbase (se 2 (by rfl) ⟨150246, by rfl⟩ : syracuseStep 400657 = 300493) (by norm_num)
theorem B1809701 : Blo 354756 1809701 := bbase (se 4 (by rfl) ⟨169659, by rfl⟩ : syracuseStep 1809701 = 339319) (by norm_num)
theorem B400693 : Blo 354756 400693 := bbase (se 5 (by rfl) ⟨18782, by rfl⟩ : syracuseStep 400693 = 37565) (by norm_num)
theorem B400729 : Blo 354756 400729 := bbase (se 2 (by rfl) ⟨150273, by rfl⟩ : syracuseStep 400729 = 300547) (by norm_num)
theorem B400765 : Blo 354756 400765 := bbase (se 3 (by rfl) ⟨75143, by rfl⟩ : syracuseStep 400765 = 150287) (by norm_num)
theorem B761213 : Blo 354756 761213 := bbase (se 3 (by rfl) ⟨142727, by rfl⟩ : syracuseStep 761213 = 285455) (by norm_num)
theorem B400801 : Blo 354756 400801 := bbase (se 2 (by rfl) ⟨150300, by rfl⟩ : syracuseStep 400801 = 300601) (by norm_num)
theorem B400837 : Blo 354756 400837 := bbase (se 4 (by rfl) ⟨37578, by rfl⟩ : syracuseStep 400837 = 75157) (by norm_num)
theorem B400873 : Blo 354756 400873 := bbase (se 2 (by rfl) ⟨150327, by rfl⟩ : syracuseStep 400873 = 300655) (by norm_num)
theorem B400909 : Blo 354756 400909 := bbase (se 3 (by rfl) ⟨75170, by rfl⟩ : syracuseStep 400909 = 150341) (by norm_num)
theorem B1711637 : Blo 354756 1711637 := bbase (se 6 (by rfl) ⟨40116, by rfl⟩ : syracuseStep 1711637 = 80233) (by norm_num)
theorem B3317269 : Blo 354756 3317269 := bbase (se 6 (by rfl) ⟨77748, by rfl⟩ : syracuseStep 3317269 = 155497) (by norm_num)
theorem B400945 : Blo 354756 400945 := bbase (se 2 (by rfl) ⟨150354, by rfl⟩ : syracuseStep 400945 = 300709) (by norm_num)
theorem B400981 : Blo 354756 400981 := bbase (se 8 (by rfl) ⟨2349, by rfl⟩ : syracuseStep 400981 = 4699) (by norm_num)
theorem B401017 : Blo 354756 401017 := bbase (se 2 (by rfl) ⟨150381, by rfl⟩ : syracuseStep 401017 = 300763) (by norm_num)
theorem B401053 : Blo 354756 401053 := bbase (se 3 (by rfl) ⟨75197, by rfl⟩ : syracuseStep 401053 = 150395) (by norm_num)
theorem B532157 : Blo 354756 532157 := bbase (se 3 (by rfl) ⟨99779, by rfl⟩ : syracuseStep 532157 = 199559) (by norm_num)
theorem B401089 : Blo 354756 401089 := bbase (se 2 (by rfl) ⟨150408, by rfl⟩ : syracuseStep 401089 = 300817) (by norm_num)
theorem B532181 : Blo 354756 532181 := bbase (se 7 (by rfl) ⟨6236, by rfl⟩ : syracuseStep 532181 = 12473) (by norm_num)
theorem B2694869 : Blo 354756 2694869 := bbase (se 7 (by rfl) ⟨31580, by rfl⟩ : syracuseStep 2694869 = 63161) (by norm_num)
theorem B401125 : Blo 354756 401125 := bbase (se 4 (by rfl) ⟨37605, by rfl⟩ : syracuseStep 401125 = 75211) (by norm_num)
theorem B532205 : Blo 354756 532205 := bbase (se 3 (by rfl) ⟨99788, by rfl⟩ : syracuseStep 532205 = 199577) (by norm_num)
theorem B859901 : Blo 354756 859901 := bbase (se 3 (by rfl) ⟨161231, by rfl⟩ : syracuseStep 859901 = 322463) (by norm_num)
theorem B532229 : Blo 354756 532229 := bbase (se 4 (by rfl) ⟨49896, by rfl⟩ : syracuseStep 532229 = 99793) (by norm_num)
theorem B401161 : Blo 354756 401161 := bbase (se 2 (by rfl) ⟨150435, by rfl⟩ : syracuseStep 401161 = 300871) (by norm_num)
theorem B532253 : Blo 354756 532253 := bbase (se 3 (by rfl) ⟨99797, by rfl⟩ : syracuseStep 532253 = 199595) (by norm_num)
theorem B401197 : Blo 354756 401197 := bbase (se 3 (by rfl) ⟨75224, by rfl⟩ : syracuseStep 401197 = 150449) (by norm_num)
theorem B532277 : Blo 354756 532277 := bbase (se 5 (by rfl) ⟨24950, by rfl⟩ : syracuseStep 532277 = 49901) (by norm_num)
theorem B532301 : Blo 354756 532301 := bbase (se 3 (by rfl) ⟨99806, by rfl⟩ : syracuseStep 532301 = 199613) (by norm_num)
theorem B401233 : Blo 354756 401233 := bbase (se 2 (by rfl) ⟨150462, by rfl⟩ : syracuseStep 401233 = 300925) (by norm_num)
theorem B532325 : Blo 354756 532325 := bbase (se 4 (by rfl) ⟨49905, by rfl⟩ : syracuseStep 532325 = 99811) (by norm_num)
theorem B401269 : Blo 354756 401269 := bbase (se 5 (by rfl) ⟨18809, by rfl⟩ : syracuseStep 401269 = 37619) (by norm_num)
theorem B532349 : Blo 354756 532349 := bbase (se 3 (by rfl) ⟨99815, by rfl⟩ : syracuseStep 532349 = 199631) (by norm_num)
theorem B532373 : Blo 354756 532373 := bbase (se 6 (by rfl) ⟨12477, by rfl⟩ : syracuseStep 532373 = 24955) (by norm_num)
theorem B401305 : Blo 354756 401305 := bbase (se 2 (by rfl) ⟨150489, by rfl⟩ : syracuseStep 401305 = 300979) (by norm_num)
theorem B532397 : Blo 354756 532397 := bbase (se 3 (by rfl) ⟨99824, by rfl⟩ : syracuseStep 532397 = 199649) (by norm_num)
theorem B401341 : Blo 354756 401341 := bbase (se 3 (by rfl) ⟨75251, by rfl⟩ : syracuseStep 401341 = 150503) (by norm_num)
theorem B532421 : Blo 354756 532421 := bbase (se 4 (by rfl) ⟨49914, by rfl⟩ : syracuseStep 532421 = 99829) (by norm_num)
theorem B532445 : Blo 354756 532445 := bbase (se 3 (by rfl) ⟨99833, by rfl⟩ : syracuseStep 532445 = 199667) (by norm_num)
theorem B401377 : Blo 354756 401377 := bbase (se 2 (by rfl) ⟨150516, by rfl⟩ : syracuseStep 401377 = 301033) (by norm_num)
theorem B532469 : Blo 354756 532469 := bbase (se 5 (by rfl) ⟨24959, by rfl⟩ : syracuseStep 532469 = 49919) (by norm_num)
theorem B401413 : Blo 354756 401413 := bbase (se 4 (by rfl) ⟨37632, by rfl⟩ : syracuseStep 401413 = 75265) (by norm_num)
theorem B532493 : Blo 354756 532493 := bbase (se 3 (by rfl) ⟨99842, by rfl⟩ : syracuseStep 532493 = 199685) (by norm_num)
theorem B532517 : Blo 354756 532517 := bbase (se 4 (by rfl) ⟨49923, by rfl⟩ : syracuseStep 532517 = 99847) (by norm_num)
theorem B401449 : Blo 354756 401449 := bbase (se 2 (by rfl) ⟨150543, by rfl⟩ : syracuseStep 401449 = 301087) (by norm_num)
theorem B532541 : Blo 354756 532541 := bbase (se 3 (by rfl) ⟨99851, by rfl⟩ : syracuseStep 532541 = 199703) (by norm_num)
theorem B1089605 : Blo 354756 1089605 := bbase (se 4 (by rfl) ⟨102150, by rfl⟩ : syracuseStep 1089605 = 204301) (by norm_num)
theorem B401485 : Blo 354756 401485 := bbase (se 3 (by rfl) ⟨75278, by rfl⟩ : syracuseStep 401485 = 150557) (by norm_num)
theorem B532565 : Blo 354756 532565 := bbase (se 8 (by rfl) ⟨3120, by rfl⟩ : syracuseStep 532565 = 6241) (by norm_num)
theorem B761957 : Blo 354756 761957 := bbase (se 4 (by rfl) ⟨71433, by rfl⟩ : syracuseStep 761957 = 142867) (by norm_num)
theorem B532589 : Blo 354756 532589 := bbase (se 3 (by rfl) ⟨99860, by rfl⟩ : syracuseStep 532589 = 199721) (by norm_num)
theorem B401521 : Blo 354756 401521 := bbase (se 2 (by rfl) ⟨150570, by rfl⟩ : syracuseStep 401521 = 301141) (by norm_num)
theorem B532613 : Blo 354756 532613 := bbase (se 4 (by rfl) ⟨49932, by rfl⟩ : syracuseStep 532613 = 99865) (by norm_num)
theorem B401557 : Blo 354756 401557 := bbase (se 6 (by rfl) ⟨9411, by rfl⟩ : syracuseStep 401557 = 18823) (by norm_num)
theorem B532637 : Blo 354756 532637 := bbase (se 3 (by rfl) ⟨99869, by rfl⟩ : syracuseStep 532637 = 199739) (by norm_num)
theorem B532661 : Blo 354756 532661 := bbase (se 5 (by rfl) ⟨24968, by rfl⟩ : syracuseStep 532661 = 49937) (by norm_num)
theorem B401593 : Blo 354756 401593 := bbase (se 2 (by rfl) ⟨150597, by rfl⟩ : syracuseStep 401593 = 301195) (by norm_num)
theorem B532685 : Blo 354756 532685 := bbase (se 3 (by rfl) ⟨99878, by rfl⟩ : syracuseStep 532685 = 199757) (by norm_num)
theorem B401629 : Blo 354756 401629 := bbase (se 3 (by rfl) ⟨75305, by rfl⟩ : syracuseStep 401629 = 150611) (by norm_num)
theorem B532709 : Blo 354756 532709 := bbase (se 4 (by rfl) ⟨49941, by rfl⟩ : syracuseStep 532709 = 99883) (by norm_num)
theorem B532733 : Blo 354756 532733 := bbase (se 3 (by rfl) ⟨99887, by rfl⟩ : syracuseStep 532733 = 199775) (by norm_num)
theorem B401665 : Blo 354756 401665 := bbase (se 2 (by rfl) ⟨150624, by rfl⟩ : syracuseStep 401665 = 301249) (by norm_num)
theorem B1515797 : Blo 354756 1515797 := bbase (se 6 (by rfl) ⟨35526, by rfl⟩ : syracuseStep 1515797 = 71053) (by norm_num)
theorem B532757 : Blo 354756 532757 := bbase (se 6 (by rfl) ⟨12486, by rfl⟩ : syracuseStep 532757 = 24973) (by norm_num)
theorem B401701 : Blo 354756 401701 := bbase (se 4 (by rfl) ⟨37659, by rfl⟩ : syracuseStep 401701 = 75319) (by norm_num)
theorem B532781 : Blo 354756 532781 := bbase (se 3 (by rfl) ⟨99896, by rfl⟩ : syracuseStep 532781 = 199793) (by norm_num)
theorem B532805 : Blo 354756 532805 := bbase (se 4 (by rfl) ⟨49950, by rfl⟩ : syracuseStep 532805 = 99901) (by norm_num)
theorem B401737 : Blo 354756 401737 := bbase (se 2 (by rfl) ⟨150651, by rfl⟩ : syracuseStep 401737 = 301303) (by norm_num)
theorem B532829 : Blo 354756 532829 := bbase (se 3 (by rfl) ⟨99905, by rfl⟩ : syracuseStep 532829 = 199811) (by norm_num)
theorem B401773 : Blo 354756 401773 := bbase (se 3 (by rfl) ⟨75332, by rfl⟩ : syracuseStep 401773 = 150665) (by norm_num)
theorem B532853 : Blo 354756 532853 := bbase (se 5 (by rfl) ⟨24977, by rfl⟩ : syracuseStep 532853 = 49955) (by norm_num)
theorem B532877 : Blo 354756 532877 := bbase (se 3 (by rfl) ⟨99914, by rfl⟩ : syracuseStep 532877 = 199829) (by norm_num)
theorem B401809 : Blo 354756 401809 := bbase (se 2 (by rfl) ⟨150678, by rfl⟩ : syracuseStep 401809 = 301357) (by norm_num)
theorem B532901 : Blo 354756 532901 := bbase (se 4 (by rfl) ⟨49959, by rfl⟩ : syracuseStep 532901 = 99919) (by norm_num)
theorem B401845 : Blo 354756 401845 := bbase (se 5 (by rfl) ⟨18836, by rfl⟩ : syracuseStep 401845 = 37673) (by norm_num)
theorem B532925 : Blo 354756 532925 := bbase (se 3 (by rfl) ⟨99923, by rfl⟩ : syracuseStep 532925 = 199847) (by norm_num)
theorem B532949 : Blo 354756 532949 := bbase (se 7 (by rfl) ⟨6245, by rfl⟩ : syracuseStep 532949 = 12491) (by norm_num)
theorem B401881 : Blo 354756 401881 := bbase (se 2 (by rfl) ⟨150705, by rfl⟩ : syracuseStep 401881 = 301411) (by norm_num)
theorem B1450469 : Blo 354756 1450469 := bbase (se 4 (by rfl) ⟨135981, by rfl⟩ : syracuseStep 1450469 = 271963) (by norm_num)
theorem B532973 : Blo 354756 532973 := bbase (se 3 (by rfl) ⟨99932, by rfl⟩ : syracuseStep 532973 = 199865) (by norm_num)
theorem B401917 : Blo 354756 401917 := bbase (se 3 (by rfl) ⟨75359, by rfl⟩ : syracuseStep 401917 = 150719) (by norm_num)
theorem B532997 : Blo 354756 532997 := bbase (se 4 (by rfl) ⟨49968, by rfl⟩ : syracuseStep 532997 = 99937) (by norm_num)
theorem B533021 : Blo 354756 533021 := bbase (se 3 (by rfl) ⟨99941, by rfl⟩ : syracuseStep 533021 = 199883) (by norm_num)
theorem B401953 : Blo 354756 401953 := bbase (se 2 (by rfl) ⟨150732, by rfl⟩ : syracuseStep 401953 = 301465) (by norm_num)
theorem B533045 : Blo 354756 533045 := bbase (se 5 (by rfl) ⟨24986, by rfl⟩ : syracuseStep 533045 = 49973) (by norm_num)
theorem B1810997 : Blo 354756 1810997 := bbase (se 5 (by rfl) ⟨84890, by rfl⟩ : syracuseStep 1810997 = 169781) (by norm_num)
theorem B401989 : Blo 354756 401989 := bbase (se 4 (by rfl) ⟨37686, by rfl⟩ : syracuseStep 401989 = 75373) (by norm_num)
theorem B533069 : Blo 354756 533069 := bbase (se 3 (by rfl) ⟨99950, by rfl⟩ : syracuseStep 533069 = 199901) (by norm_num)
theorem B533093 : Blo 354756 533093 := bbase (se 4 (by rfl) ⟨49977, by rfl⟩ : syracuseStep 533093 = 99955) (by norm_num)
theorem B402025 : Blo 354756 402025 := bbase (se 2 (by rfl) ⟨150759, by rfl⟩ : syracuseStep 402025 = 301519) (by norm_num)
theorem B2433653 : Blo 354756 2433653 := bbase (se 5 (by rfl) ⟨114077, by rfl⟩ : syracuseStep 2433653 = 228155) (by norm_num)
theorem B533117 : Blo 354756 533117 := bbase (se 3 (by rfl) ⟨99959, by rfl⟩ : syracuseStep 533117 = 199919) (by norm_num)
theorem B402061 : Blo 354756 402061 := bbase (se 3 (by rfl) ⟨75386, by rfl⟩ : syracuseStep 402061 = 150773) (by norm_num)
theorem B533141 : Blo 354756 533141 := bbase (se 6 (by rfl) ⟨12495, by rfl⟩ : syracuseStep 533141 = 24991) (by norm_num)
theorem B533165 : Blo 354756 533165 := bbase (se 3 (by rfl) ⟨99968, by rfl⟩ : syracuseStep 533165 = 199937) (by norm_num)
theorem B402097 : Blo 354756 402097 := bbase (se 2 (by rfl) ⟨150786, by rfl⟩ : syracuseStep 402097 = 301573) (by norm_num)
theorem B533189 : Blo 354756 533189 := bbase (se 4 (by rfl) ⟨49986, by rfl⟩ : syracuseStep 533189 = 99973) (by norm_num)
theorem B402133 : Blo 354756 402133 := bbase (se 7 (by rfl) ⟨4712, by rfl⟩ : syracuseStep 402133 = 9425) (by norm_num)
theorem B533213 : Blo 354756 533213 := bbase (se 3 (by rfl) ⟨99977, by rfl⟩ : syracuseStep 533213 = 199955) (by norm_num)
theorem B598765 : Blo 354756 598765 := bbase (se 3 (by rfl) ⟨112268, by rfl⟩ : syracuseStep 598765 = 224537) (by norm_num)
theorem B533237 : Blo 354756 533237 := bbase (se 5 (by rfl) ⟨24995, by rfl⟩ : syracuseStep 533237 = 49991) (by norm_num)
theorem B402169 : Blo 354756 402169 := bbase (se 2 (by rfl) ⟨150813, by rfl⟩ : syracuseStep 402169 = 301627) (by norm_num)
theorem B533261 : Blo 354756 533261 := bbase (se 3 (by rfl) ⟨99986, by rfl⟩ : syracuseStep 533261 = 199973) (by norm_num)
theorem B402205 : Blo 354756 402205 := bbase (se 3 (by rfl) ⟨75413, by rfl⟩ : syracuseStep 402205 = 150827) (by norm_num)
theorem B533285 : Blo 354756 533285 := bbase (se 4 (by rfl) ⟨49995, by rfl⟩ : syracuseStep 533285 = 99991) (by norm_num)
theorem B533309 : Blo 354756 533309 := bbase (se 3 (by rfl) ⟨99995, by rfl⟩ : syracuseStep 533309 = 199991) (by norm_num)
theorem B402241 : Blo 354756 402241 := bbase (se 2 (by rfl) ⟨150840, by rfl⟩ : syracuseStep 402241 = 301681) (by norm_num)
theorem B598853 : Blo 354756 598853 := bbase (se 4 (by rfl) ⟨56142, by rfl⟩ : syracuseStep 598853 = 112285) (by norm_num)
theorem B533333 : Blo 354756 533333 := bbase (se 9 (by rfl) ⟨1562, by rfl⟩ : syracuseStep 533333 = 3125) (by norm_num)
theorem B762709 : Blo 354756 762709 := bbase (se 9 (by rfl) ⟨2234, by rfl⟩ : syracuseStep 762709 = 4469) (by norm_num)
theorem B402277 : Blo 354756 402277 := bbase (se 4 (by rfl) ⟨37713, by rfl⟩ : syracuseStep 402277 = 75427) (by norm_num)
theorem B533357 : Blo 354756 533357 := bbase (se 3 (by rfl) ⟨100004, by rfl⟩ : syracuseStep 533357 = 200009) (by norm_num)
theorem B533381 : Blo 354756 533381 := bbase (se 4 (by rfl) ⟨50004, by rfl⟩ : syracuseStep 533381 = 100009) (by norm_num)
theorem B402313 : Blo 354756 402313 := bbase (se 2 (by rfl) ⟨150867, by rfl⟩ : syracuseStep 402313 = 301735) (by norm_num)
theorem B533405 : Blo 354756 533405 := bbase (se 3 (by rfl) ⟨100013, by rfl⟩ : syracuseStep 533405 = 200027) (by norm_num)
theorem B402349 : Blo 354756 402349 := bbase (se 3 (by rfl) ⟨75440, by rfl⟩ : syracuseStep 402349 = 150881) (by norm_num)
theorem B533429 : Blo 354756 533429 := bbase (se 5 (by rfl) ⟨25004, by rfl⟩ : syracuseStep 533429 = 50009) (by norm_num)
theorem B598981 : Blo 354756 598981 := bbase (se 4 (by rfl) ⟨56154, by rfl⟩ : syracuseStep 598981 = 112309) (by norm_num)
theorem B1352645 : Blo 354756 1352645 := bbase (se 4 (by rfl) ⟨126810, by rfl⟩ : syracuseStep 1352645 = 253621) (by norm_num)
theorem B533453 : Blo 354756 533453 := bbase (se 3 (by rfl) ⟨100022, by rfl⟩ : syracuseStep 533453 = 200045) (by norm_num)
theorem B402385 : Blo 354756 402385 := bbase (se 2 (by rfl) ⟨150894, by rfl⟩ : syracuseStep 402385 = 301789) (by norm_num)
theorem B533477 : Blo 354756 533477 := bbase (se 4 (by rfl) ⟨50013, by rfl⟩ : syracuseStep 533477 = 100027) (by norm_num)
theorem B762853 : Blo 354756 762853 := bbase (se 4 (by rfl) ⟨71517, by rfl⟩ : syracuseStep 762853 = 143035) (by norm_num)
theorem B402421 : Blo 354756 402421 := bbase (se 5 (by rfl) ⟨18863, by rfl⟩ : syracuseStep 402421 = 37727) (by norm_num)
theorem B533501 : Blo 354756 533501 := bbase (se 3 (by rfl) ⟨100031, by rfl⟩ : syracuseStep 533501 = 200063) (by norm_num)
theorem B533525 : Blo 354756 533525 := bbase (se 6 (by rfl) ⟨12504, by rfl⟩ : syracuseStep 533525 = 25009) (by norm_num)
theorem B402457 : Blo 354756 402457 := bbase (se 2 (by rfl) ⟨150921, by rfl⟩ : syracuseStep 402457 = 301843) (by norm_num)
theorem B599069 : Blo 354756 599069 := bbase (se 3 (by rfl) ⟨112325, by rfl⟩ : syracuseStep 599069 = 224651) (by norm_num)
theorem B533549 : Blo 354756 533549 := bbase (se 3 (by rfl) ⟨100040, by rfl⟩ : syracuseStep 533549 = 200081) (by norm_num)
theorem B402493 : Blo 354756 402493 := bbase (se 3 (by rfl) ⟨75467, by rfl⟩ : syracuseStep 402493 = 150935) (by norm_num)
theorem B533573 : Blo 354756 533573 := bbase (se 4 (by rfl) ⟨50022, by rfl⟩ : syracuseStep 533573 = 100045) (by norm_num)
theorem B533597 : Blo 354756 533597 := bbase (se 3 (by rfl) ⟨100049, by rfl⟩ : syracuseStep 533597 = 200099) (by norm_num)
theorem B402529 : Blo 354756 402529 := bbase (se 2 (by rfl) ⟨150948, by rfl⟩ : syracuseStep 402529 = 301897) (by norm_num)
theorem B533621 : Blo 354756 533621 := bbase (se 5 (by rfl) ⟨25013, by rfl⟩ : syracuseStep 533621 = 50027) (by norm_num)
theorem B402565 : Blo 354756 402565 := bbase (se 4 (by rfl) ⟨37740, by rfl⟩ : syracuseStep 402565 = 75481) (by norm_num)
theorem B533645 : Blo 354756 533645 := bbase (se 3 (by rfl) ⟨100058, by rfl⟩ : syracuseStep 533645 = 200117) (by norm_num)
theorem B599197 : Blo 354756 599197 := bbase (se 3 (by rfl) ⟨112349, by rfl⟩ : syracuseStep 599197 = 224699) (by norm_num)
theorem B533669 : Blo 354756 533669 := bbase (se 4 (by rfl) ⟨50031, by rfl⟩ : syracuseStep 533669 = 100063) (by norm_num)
theorem B402601 : Blo 354756 402601 := bbase (se 2 (by rfl) ⟨150975, by rfl⟩ : syracuseStep 402601 = 301951) (by norm_num)
theorem B533693 : Blo 354756 533693 := bbase (se 3 (by rfl) ⟨100067, by rfl⟩ : syracuseStep 533693 = 200135) (by norm_num)
theorem B402637 : Blo 354756 402637 := bbase (se 3 (by rfl) ⟨75494, by rfl⟩ : syracuseStep 402637 = 150989) (by norm_num)
theorem B533717 : Blo 354756 533717 := bbase (se 7 (by rfl) ⟨6254, by rfl⟩ : syracuseStep 533717 = 12509) (by norm_num)
theorem B1352933 : Blo 354756 1352933 := bbase (se 4 (by rfl) ⟨126837, by rfl⟩ : syracuseStep 1352933 = 253675) (by norm_num)
theorem B533741 : Blo 354756 533741 := bbase (se 3 (by rfl) ⟨100076, by rfl⟩ : syracuseStep 533741 = 200153) (by norm_num)
theorem B402673 : Blo 354756 402673 := bbase (se 2 (by rfl) ⟨151002, by rfl⟩ : syracuseStep 402673 = 302005) (by norm_num)
theorem B599285 : Blo 354756 599285 := bbase (se 5 (by rfl) ⟨28091, by rfl⟩ : syracuseStep 599285 = 56183) (by norm_num)
theorem B533765 : Blo 354756 533765 := bbase (se 4 (by rfl) ⟨50040, by rfl⟩ : syracuseStep 533765 = 100081) (by norm_num)
theorem B402709 : Blo 354756 402709 := bbase (se 6 (by rfl) ⟨9438, by rfl⟩ : syracuseStep 402709 = 18877) (by norm_num)
theorem B2041109 : Blo 354756 2041109 := bbase (se 6 (by rfl) ⟨47838, by rfl⟩ : syracuseStep 2041109 = 95677) (by norm_num)
theorem B533789 : Blo 354756 533789 := bbase (se 3 (by rfl) ⟨100085, by rfl⟩ : syracuseStep 533789 = 200171) (by norm_num)
theorem B533813 : Blo 354756 533813 := bbase (se 5 (by rfl) ⟨25022, by rfl⟩ : syracuseStep 533813 = 50045) (by norm_num)
theorem B402745 : Blo 354756 402745 := bbase (se 2 (by rfl) ⟨151029, by rfl⟩ : syracuseStep 402745 = 302059) (by norm_num)
theorem B533837 : Blo 354756 533837 := bbase (se 3 (by rfl) ⟨100094, by rfl⟩ : syracuseStep 533837 = 200189) (by norm_num)
theorem B763229 : Blo 354756 763229 := bbase (se 3 (by rfl) ⟨143105, by rfl⟩ : syracuseStep 763229 = 286211) (by norm_num)
theorem B402781 : Blo 354756 402781 := bbase (se 3 (by rfl) ⟨75521, by rfl⟩ : syracuseStep 402781 = 151043) (by norm_num)
theorem B533861 : Blo 354756 533861 := bbase (se 4 (by rfl) ⟨50049, by rfl⟩ : syracuseStep 533861 = 100099) (by norm_num)
theorem B599413 : Blo 354756 599413 := bbase (se 5 (by rfl) ⟨28097, by rfl⟩ : syracuseStep 599413 = 56195) (by norm_num)
theorem B3417461 : Blo 354756 3417461 := bbase (se 5 (by rfl) ⟨160193, by rfl⟩ : syracuseStep 3417461 = 320387) (by norm_num)
theorem B533885 : Blo 354756 533885 := bbase (se 3 (by rfl) ⟨100103, by rfl⟩ : syracuseStep 533885 = 200207) (by norm_num)
theorem B402817 : Blo 354756 402817 := bbase (se 2 (by rfl) ⟨151056, by rfl⟩ : syracuseStep 402817 = 302113) (by norm_num)
theorem B533909 : Blo 354756 533909 := bbase (se 6 (by rfl) ⟨12513, by rfl⟩ : syracuseStep 533909 = 25027) (by norm_num)
theorem B402853 : Blo 354756 402853 := bbase (se 4 (by rfl) ⟨37767, by rfl⟩ : syracuseStep 402853 = 75535) (by norm_num)
theorem B533933 : Blo 354756 533933 := bbase (se 3 (by rfl) ⟨100112, by rfl⟩ : syracuseStep 533933 = 200225) (by norm_num)
theorem B533957 : Blo 354756 533957 := bbase (se 4 (by rfl) ⟨50058, by rfl⟩ : syracuseStep 533957 = 100117) (by norm_num)
theorem B402889 : Blo 354756 402889 := bbase (se 2 (by rfl) ⟨151083, by rfl⟩ : syracuseStep 402889 = 302167) (by norm_num)
theorem B599501 : Blo 354756 599501 := bbase (se 3 (by rfl) ⟨112406, by rfl⟩ : syracuseStep 599501 = 224813) (by norm_num)
theorem B533981 : Blo 354756 533981 := bbase (se 3 (by rfl) ⟨100121, by rfl⟩ : syracuseStep 533981 = 200243) (by norm_num)
theorem B402925 : Blo 354756 402925 := bbase (se 3 (by rfl) ⟨75548, by rfl⟩ : syracuseStep 402925 = 151097) (by norm_num)
theorem B534005 : Blo 354756 534005 := bbase (se 5 (by rfl) ⟨25031, by rfl⟩ : syracuseStep 534005 = 50063) (by norm_num)
theorem B534029 : Blo 354756 534029 := bbase (se 3 (by rfl) ⟨100130, by rfl⟩ : syracuseStep 534029 = 200261) (by norm_num)
theorem B402961 : Blo 354756 402961 := bbase (se 2 (by rfl) ⟨151110, by rfl⟩ : syracuseStep 402961 = 302221) (by norm_num)
theorem B534053 : Blo 354756 534053 := bbase (se 4 (by rfl) ⟨50067, by rfl⟩ : syracuseStep 534053 = 100135) (by norm_num)
theorem B402997 : Blo 354756 402997 := bbase (se 5 (by rfl) ⟨18890, by rfl⟩ : syracuseStep 402997 = 37781) (by norm_num)
theorem B468541 : Blo 354756 468541 := bbase (se 3 (by rfl) ⟨87851, by rfl⟩ : syracuseStep 468541 = 175703) (by norm_num)
theorem B534077 : Blo 354756 534077 := bbase (se 3 (by rfl) ⟨100139, by rfl⟩ : syracuseStep 534077 = 200279) (by norm_num)
theorem B599629 : Blo 354756 599629 := bbase (se 3 (by rfl) ⟨112430, by rfl⟩ : syracuseStep 599629 = 224861) (by norm_num)
theorem B534101 : Blo 354756 534101 := bbase (se 8 (by rfl) ⟨3129, by rfl⟩ : syracuseStep 534101 = 6259) (by norm_num)
theorem B403033 : Blo 354756 403033 := bbase (se 2 (by rfl) ⟨151137, by rfl⟩ : syracuseStep 403033 = 302275) (by norm_num)
theorem B534125 : Blo 354756 534125 := bbase (se 3 (by rfl) ⟨100148, by rfl⟩ : syracuseStep 534125 = 200297) (by norm_num)
theorem B403069 : Blo 354756 403069 := bbase (se 3 (by rfl) ⟨75575, by rfl⟩ : syracuseStep 403069 = 151151) (by norm_num)
theorem B534149 : Blo 354756 534149 := bbase (se 4 (by rfl) ⟨50076, by rfl⟩ : syracuseStep 534149 = 100153) (by norm_num)
theorem B534173 : Blo 354756 534173 := bbase (se 3 (by rfl) ⟨100157, by rfl⟩ : syracuseStep 534173 = 200315) (by norm_num)
theorem B403105 : Blo 354756 403105 := bbase (se 2 (by rfl) ⟨151164, by rfl⟩ : syracuseStep 403105 = 302329) (by norm_num)
theorem B599717 : Blo 354756 599717 := bbase (se 4 (by rfl) ⟨56223, by rfl⟩ : syracuseStep 599717 = 112447) (by norm_num)
theorem B534197 : Blo 354756 534197 := bbase (se 5 (by rfl) ⟨25040, by rfl⟩ : syracuseStep 534197 = 50081) (by norm_num)
theorem B403141 : Blo 354756 403141 := bbase (se 4 (by rfl) ⟨37794, by rfl⟩ : syracuseStep 403141 = 75589) (by norm_num)
theorem B534221 : Blo 354756 534221 := bbase (se 3 (by rfl) ⟨100166, by rfl⟩ : syracuseStep 534221 = 200333) (by norm_num)
theorem B763597 : Blo 354756 763597 := bbase (se 3 (by rfl) ⟨143174, by rfl⟩ : syracuseStep 763597 = 286349) (by norm_num)
theorem B1287893 : Blo 354756 1287893 := bbase (se 7 (by rfl) ⟨15092, by rfl⟩ : syracuseStep 1287893 = 30185) (by norm_num)
theorem B534245 : Blo 354756 534245 := bbase (se 4 (by rfl) ⟨50085, by rfl⟩ : syracuseStep 534245 = 100171) (by norm_num)
theorem B403177 : Blo 354756 403177 := bbase (se 2 (by rfl) ⟨151191, by rfl⟩ : syracuseStep 403177 = 302383) (by norm_num)
theorem B534269 : Blo 354756 534269 := bbase (se 3 (by rfl) ⟨100175, by rfl⟩ : syracuseStep 534269 = 200351) (by norm_num)
theorem B403213 : Blo 354756 403213 := bbase (se 3 (by rfl) ⟨75602, by rfl⟩ : syracuseStep 403213 = 151205) (by norm_num)
theorem B534293 : Blo 354756 534293 := bbase (se 6 (by rfl) ⟨12522, by rfl⟩ : syracuseStep 534293 = 25045) (by norm_num)
theorem B599845 : Blo 354756 599845 := bbase (se 4 (by rfl) ⟨56235, by rfl⟩ : syracuseStep 599845 = 112471) (by norm_num)
theorem B534317 : Blo 354756 534317 := bbase (se 3 (by rfl) ⟨100184, by rfl⟩ : syracuseStep 534317 = 200369) (by norm_num)
theorem B403249 : Blo 354756 403249 := bbase (se 2 (by rfl) ⟨151218, by rfl⟩ : syracuseStep 403249 = 302437) (by norm_num)
theorem B534341 : Blo 354756 534341 := bbase (se 4 (by rfl) ⟨50094, by rfl⟩ : syracuseStep 534341 = 100189) (by norm_num)
theorem B1812293 : Blo 354756 1812293 := bbase (se 4 (by rfl) ⟨169902, by rfl⟩ : syracuseStep 1812293 = 339805) (by norm_num)
theorem B403285 : Blo 354756 403285 := bbase (se 9 (by rfl) ⟨1181, by rfl⟩ : syracuseStep 403285 = 2363) (by norm_num)
theorem B534365 : Blo 354756 534365 := bbase (se 3 (by rfl) ⟨100193, by rfl⟩ : syracuseStep 534365 = 200387) (by norm_num)
theorem B534389 : Blo 354756 534389 := bbase (se 5 (by rfl) ⟨25049, by rfl⟩ : syracuseStep 534389 = 50099) (by norm_num)
theorem B403321 : Blo 354756 403321 := bbase (se 2 (by rfl) ⟨151245, by rfl⟩ : syracuseStep 403321 = 302491) (by norm_num)
theorem B599933 : Blo 354756 599933 := bbase (se 3 (by rfl) ⟨112487, by rfl⟩ : syracuseStep 599933 = 224975) (by norm_num)
theorem B534413 : Blo 354756 534413 := bbase (se 3 (by rfl) ⟨100202, by rfl⟩ : syracuseStep 534413 = 200405) (by norm_num)
theorem B403357 : Blo 354756 403357 := bbase (se 3 (by rfl) ⟨75629, by rfl⟩ : syracuseStep 403357 = 151259) (by norm_num)
theorem B534437 : Blo 354756 534437 := bbase (se 4 (by rfl) ⟨50103, by rfl⟩ : syracuseStep 534437 = 100207) (by norm_num)
theorem B534461 : Blo 354756 534461 := bbase (se 3 (by rfl) ⟨100211, by rfl⟩ : syracuseStep 534461 = 200423) (by norm_num)
theorem B403393 : Blo 354756 403393 := bbase (se 2 (by rfl) ⟨151272, by rfl⟩ : syracuseStep 403393 = 302545) (by norm_num)
theorem B534485 : Blo 354756 534485 := bbase (se 7 (by rfl) ⟨6263, by rfl⟩ : syracuseStep 534485 = 12527) (by norm_num)
theorem B403429 : Blo 354756 403429 := bbase (se 4 (by rfl) ⟨37821, by rfl⟩ : syracuseStep 403429 = 75643) (by norm_num)
theorem B534509 : Blo 354756 534509 := bbase (se 3 (by rfl) ⟨100220, by rfl⟩ : syracuseStep 534509 = 200441) (by norm_num)
theorem B600061 : Blo 354756 600061 := bbase (se 3 (by rfl) ⟨112511, by rfl⟩ : syracuseStep 600061 = 225023) (by norm_num)
theorem B534533 : Blo 354756 534533 := bbase (se 4 (by rfl) ⟨50112, by rfl⟩ : syracuseStep 534533 = 100225) (by norm_num)
theorem B403465 : Blo 354756 403465 := bbase (se 2 (by rfl) ⟨151299, by rfl⟩ : syracuseStep 403465 = 302599) (by norm_num)
theorem B534557 : Blo 354756 534557 := bbase (se 3 (by rfl) ⟨100229, by rfl⟩ : syracuseStep 534557 = 200459) (by norm_num)
theorem B403501 : Blo 354756 403501 := bbase (se 3 (by rfl) ⟨75656, by rfl⟩ : syracuseStep 403501 = 151313) (by norm_num)
theorem B534581 : Blo 354756 534581 := bbase (se 5 (by rfl) ⟨25058, by rfl⟩ : syracuseStep 534581 = 50117) (by norm_num)
theorem B534605 : Blo 354756 534605 := bbase (se 3 (by rfl) ⟨100238, by rfl⟩ : syracuseStep 534605 = 200477) (by norm_num)
theorem B403537 : Blo 354756 403537 := bbase (se 2 (by rfl) ⟨151326, by rfl⟩ : syracuseStep 403537 = 302653) (by norm_num)
theorem B600149 : Blo 354756 600149 := bbase (se 8 (by rfl) ⟨3516, by rfl⟩ : syracuseStep 600149 = 7033) (by norm_num)
theorem B534629 : Blo 354756 534629 := bbase (se 4 (by rfl) ⟨50121, by rfl⟩ : syracuseStep 534629 = 100243) (by norm_num)
theorem B403573 : Blo 354756 403573 := bbase (se 5 (by rfl) ⟨18917, by rfl⟩ : syracuseStep 403573 = 37835) (by norm_num)
theorem B534653 : Blo 354756 534653 := bbase (se 3 (by rfl) ⟨100247, by rfl⟩ : syracuseStep 534653 = 200495) (by norm_num)
theorem B534677 : Blo 354756 534677 := bbase (se 6 (by rfl) ⟨12531, by rfl⟩ : syracuseStep 534677 = 25063) (by norm_num)
theorem B534701 : Blo 354756 534701 := bbase (se 3 (by rfl) ⟨100256, by rfl⟩ : syracuseStep 534701 = 200513) (by norm_num)
theorem B534725 : Blo 354756 534725 := bbase (se 4 (by rfl) ⟨50130, by rfl⟩ : syracuseStep 534725 = 100261) (by norm_num)
theorem B600277 : Blo 354756 600277 := bbase (se 7 (by rfl) ⟨7034, by rfl⟩ : syracuseStep 600277 = 14069) (by norm_num)
theorem B534749 : Blo 354756 534749 := bbase (se 3 (by rfl) ⟨100265, by rfl⟩ : syracuseStep 534749 = 200531) (by norm_num)
theorem B534773 : Blo 354756 534773 := bbase (se 5 (by rfl) ⟨25067, by rfl⟩ : syracuseStep 534773 = 50135) (by norm_num)
theorem B1714421 : Blo 354756 1714421 := bbase (se 5 (by rfl) ⟨80363, by rfl⟩ : syracuseStep 1714421 = 160727) (by norm_num)
theorem B534797 : Blo 354756 534797 := bbase (se 3 (by rfl) ⟨100274, by rfl⟩ : syracuseStep 534797 = 200549) (by norm_num)
theorem B534821 : Blo 354756 534821 := bbase (se 4 (by rfl) ⟨50139, by rfl⟩ : syracuseStep 534821 = 100279) (by norm_num)
theorem B600365 : Blo 354756 600365 := bbase (se 3 (by rfl) ⟨112568, by rfl⟩ : syracuseStep 600365 = 225137) (by norm_num)
theorem B534845 : Blo 354756 534845 := bbase (se 3 (by rfl) ⟨100283, by rfl⟩ : syracuseStep 534845 = 200567) (by norm_num)
theorem B436553 : Blo 354756 436553 := bbase (se 2 (by rfl) ⟨163707, by rfl⟩ : syracuseStep 436553 = 327415) (by norm_num)
theorem B534869 : Blo 354756 534869 := bbase (se 10 (by rfl) ⟨783, by rfl⟩ : syracuseStep 534869 = 1567) (by norm_num)
theorem B1845605 : Blo 354756 1845605 := bbase (se 4 (by rfl) ⟨173025, by rfl⟩ : syracuseStep 1845605 = 346051) (by norm_num)
theorem B534893 : Blo 354756 534893 := bbase (se 3 (by rfl) ⟨100292, by rfl⟩ : syracuseStep 534893 = 200585) (by norm_num)
theorem B534917 : Blo 354756 534917 := bbase (se 4 (by rfl) ⟨50148, by rfl⟩ : syracuseStep 534917 = 100297) (by norm_num)
theorem B1354117 : Blo 354756 1354117 := bbase (se 4 (by rfl) ⟨126948, by rfl⟩ : syracuseStep 1354117 = 253897) (by norm_num)
theorem B534941 : Blo 354756 534941 := bbase (se 3 (by rfl) ⟨100301, by rfl⟩ : syracuseStep 534941 = 200603) (by norm_num)
theorem B993701 : Blo 354756 993701 := bbase (se 4 (by rfl) ⟨93159, by rfl⟩ : syracuseStep 993701 = 186319) (by norm_num)
theorem B600493 : Blo 354756 600493 := bbase (se 3 (by rfl) ⟨112592, by rfl⟩ : syracuseStep 600493 = 225185) (by norm_num)
theorem B534965 : Blo 354756 534965 := bbase (se 5 (by rfl) ⟨25076, by rfl⟩ : syracuseStep 534965 = 50153) (by norm_num)
theorem B2042293 : Blo 354756 2042293 := bbase (se 5 (by rfl) ⟨95732, by rfl⟩ : syracuseStep 2042293 = 191465) (by norm_num)
theorem B534989 : Blo 354756 534989 := bbase (se 3 (by rfl) ⟨100310, by rfl⟩ : syracuseStep 534989 = 200621) (by norm_num)
theorem B535013 : Blo 354756 535013 := bbase (se 4 (by rfl) ⟨50157, by rfl⟩ : syracuseStep 535013 = 100315) (by norm_num)
theorem B535037 : Blo 354756 535037 := bbase (se 3 (by rfl) ⟨100319, by rfl⟩ : syracuseStep 535037 = 200639) (by norm_num)
theorem B600581 : Blo 354756 600581 := bbase (se 4 (by rfl) ⟨56304, by rfl⟩ : syracuseStep 600581 = 112609) (by norm_num)
theorem B535061 : Blo 354756 535061 := bbase (se 6 (by rfl) ⟨12540, by rfl⟩ : syracuseStep 535061 = 25081) (by norm_num)
theorem B535085 : Blo 354756 535085 := bbase (se 3 (by rfl) ⟨100328, by rfl⟩ : syracuseStep 535085 = 200657) (by norm_num)
theorem B535109 : Blo 354756 535109 := bbase (se 4 (by rfl) ⟨50166, by rfl⟩ : syracuseStep 535109 = 100333) (by norm_num)
theorem B535133 : Blo 354756 535133 := bbase (se 3 (by rfl) ⟨100337, by rfl⟩ : syracuseStep 535133 = 200675) (by norm_num)
theorem B535157 : Blo 354756 535157 := bbase (se 5 (by rfl) ⟨25085, by rfl⟩ : syracuseStep 535157 = 50171) (by norm_num)
theorem B600709 : Blo 354756 600709 := bbase (se 4 (by rfl) ⟨56316, by rfl⟩ : syracuseStep 600709 = 112633) (by norm_num)
theorem B535181 : Blo 354756 535181 := bbase (se 3 (by rfl) ⟨100346, by rfl⟩ : syracuseStep 535181 = 200693) (by norm_num)
theorem B535205 : Blo 354756 535205 := bbase (se 4 (by rfl) ⟨50175, by rfl⟩ : syracuseStep 535205 = 100351) (by norm_num)
theorem B1354421 : Blo 354756 1354421 := bbase (se 5 (by rfl) ⟨63488, by rfl⟩ : syracuseStep 1354421 = 126977) (by norm_num)
theorem B535229 : Blo 354756 535229 := bbase (se 3 (by rfl) ⟨100355, by rfl⟩ : syracuseStep 535229 = 200711) (by norm_num)
theorem B371401 : Blo 354756 371401 := bbase (se 2 (by rfl) ⟨139275, by rfl⟩ : syracuseStep 371401 = 278551) (by norm_num)
theorem B535253 : Blo 354756 535253 := bbase (se 7 (by rfl) ⟨6272, by rfl⟩ : syracuseStep 535253 = 12545) (by norm_num)
theorem B600797 : Blo 354756 600797 := bbase (se 3 (by rfl) ⟨112649, by rfl⟩ : syracuseStep 600797 = 225299) (by norm_num)
theorem B535277 : Blo 354756 535277 := bbase (se 3 (by rfl) ⟨100364, by rfl⟩ : syracuseStep 535277 = 200729) (by norm_num)
theorem B535301 : Blo 354756 535301 := bbase (se 4 (by rfl) ⟨50184, by rfl⟩ : syracuseStep 535301 = 100369) (by norm_num)
theorem B535325 : Blo 354756 535325 := bbase (se 3 (by rfl) ⟨100373, by rfl⟩ : syracuseStep 535325 = 200747) (by norm_num)
theorem B535349 : Blo 354756 535349 := bbase (se 5 (by rfl) ⟨25094, by rfl⟩ : syracuseStep 535349 = 50189) (by norm_num)
theorem B535373 : Blo 354756 535373 := bbase (se 3 (by rfl) ⟨100382, by rfl⟩ : syracuseStep 535373 = 200765) (by norm_num)
theorem B2796373 : Blo 354756 2796373 := bbase (se 9 (by rfl) ⟨8192, by rfl⟩ : syracuseStep 2796373 = 16385) (by norm_num)
theorem B600925 : Blo 354756 600925 := bbase (se 3 (by rfl) ⟨112673, by rfl⟩ : syracuseStep 600925 = 225347) (by norm_num)
theorem B535397 : Blo 354756 535397 := bbase (se 4 (by rfl) ⟨50193, by rfl⟩ : syracuseStep 535397 = 100387) (by norm_num)
theorem B535421 : Blo 354756 535421 := bbase (se 3 (by rfl) ⟨100391, by rfl⟩ : syracuseStep 535421 = 200783) (by norm_num)
theorem B535445 : Blo 354756 535445 := bbase (se 6 (by rfl) ⟨12549, by rfl⟩ : syracuseStep 535445 = 25099) (by norm_num)
theorem B535469 : Blo 354756 535469 := bbase (se 3 (by rfl) ⟨100400, by rfl⟩ : syracuseStep 535469 = 200801) (by norm_num)
theorem B601013 : Blo 354756 601013 := bbase (se 5 (by rfl) ⟨28172, by rfl⟩ : syracuseStep 601013 = 56345) (by norm_num)
theorem B535493 : Blo 354756 535493 := bbase (se 4 (by rfl) ⟨50202, by rfl⟩ : syracuseStep 535493 = 100405) (by norm_num)
theorem B535517 : Blo 354756 535517 := bbase (se 3 (by rfl) ⟨100409, by rfl⟩ : syracuseStep 535517 = 200819) (by norm_num)
theorem B568309 : Blo 354756 568309 := bbase (se 5 (by rfl) ⟨26639, by rfl⟩ : syracuseStep 568309 = 53279) (by norm_num)
theorem B535541 : Blo 354756 535541 := bbase (se 5 (by rfl) ⟨25103, by rfl⟩ : syracuseStep 535541 = 50207) (by norm_num)
theorem B535565 : Blo 354756 535565 := bbase (se 3 (by rfl) ⟨100418, by rfl⟩ : syracuseStep 535565 = 200837) (by norm_num)
theorem B1027093 : Blo 354756 1027093 := bbase (se 6 (by rfl) ⟨24072, by rfl⟩ : syracuseStep 1027093 = 48145) (by norm_num)
theorem B535589 : Blo 354756 535589 := bbase (se 4 (by rfl) ⟨50211, by rfl⟩ : syracuseStep 535589 = 100423) (by norm_num)
theorem B601141 : Blo 354756 601141 := bbase (se 5 (by rfl) ⟨28178, by rfl⟩ : syracuseStep 601141 = 56357) (by norm_num)
theorem B535613 : Blo 354756 535613 := bbase (se 3 (by rfl) ⟨100427, by rfl⟩ : syracuseStep 535613 = 200855) (by norm_num)
theorem B404561 : Blo 354756 404561 := bbase (se 2 (by rfl) ⟨151710, by rfl⟩ : syracuseStep 404561 = 303421) (by norm_num)
theorem B535637 : Blo 354756 535637 := bbase (se 8 (by rfl) ⟨3138, by rfl⟩ : syracuseStep 535637 = 6277) (by norm_num)
theorem B1813589 : Blo 354756 1813589 := bbase (se 8 (by rfl) ⟨10626, by rfl⟩ : syracuseStep 1813589 = 21253) (by norm_num)
theorem B535661 : Blo 354756 535661 := bbase (se 3 (by rfl) ⟨100436, by rfl⟩ : syracuseStep 535661 = 200873) (by norm_num)
theorem B535685 : Blo 354756 535685 := bbase (se 4 (by rfl) ⟨50220, by rfl⟩ : syracuseStep 535685 = 100441) (by norm_num)
theorem B601229 : Blo 354756 601229 := bbase (se 3 (by rfl) ⟨112730, by rfl⟩ : syracuseStep 601229 = 225461) (by norm_num)
theorem B535709 : Blo 354756 535709 := bbase (se 3 (by rfl) ⟨100445, by rfl⟩ : syracuseStep 535709 = 200891) (by norm_num)
theorem B765101 : Blo 354756 765101 := bbase (se 3 (by rfl) ⟨143456, by rfl⟩ : syracuseStep 765101 = 286913) (by norm_num)
theorem B535733 : Blo 354756 535733 := bbase (se 5 (by rfl) ⟨25112, by rfl⟩ : syracuseStep 535733 = 50225) (by norm_num)
theorem B535757 : Blo 354756 535757 := bbase (se 3 (by rfl) ⟨100454, by rfl⟩ : syracuseStep 535757 = 200909) (by norm_num)
theorem B535781 : Blo 354756 535781 := bbase (se 4 (by rfl) ⟨50229, by rfl⟩ : syracuseStep 535781 = 100459) (by norm_num)
theorem B535805 : Blo 354756 535805 := bbase (se 3 (by rfl) ⟨100463, by rfl⟩ : syracuseStep 535805 = 200927) (by norm_num)
theorem B601357 : Blo 354756 601357 := bbase (se 3 (by rfl) ⟨112754, by rfl⟩ : syracuseStep 601357 = 225509) (by norm_num)
theorem B535829 : Blo 354756 535829 := bbase (se 6 (by rfl) ⟨12558, by rfl⟩ : syracuseStep 535829 = 25117) (by norm_num)
theorem B535853 : Blo 354756 535853 := bbase (se 3 (by rfl) ⟨100472, by rfl⟩ : syracuseStep 535853 = 200945) (by norm_num)
theorem B765245 : Blo 354756 765245 := bbase (se 3 (by rfl) ⟨143483, by rfl⟩ : syracuseStep 765245 = 286967) (by norm_num)
theorem B535877 : Blo 354756 535877 := bbase (se 4 (by rfl) ⟨50238, by rfl⟩ : syracuseStep 535877 = 100477) (by norm_num)
theorem B535901 : Blo 354756 535901 := bbase (se 3 (by rfl) ⟨100481, by rfl⟩ : syracuseStep 535901 = 200963) (by norm_num)
theorem B601445 : Blo 354756 601445 := bbase (se 4 (by rfl) ⟨56385, by rfl⟩ : syracuseStep 601445 = 112771) (by norm_num)
theorem B535925 : Blo 354756 535925 := bbase (se 5 (by rfl) ⟨25121, by rfl⟩ : syracuseStep 535925 = 50243) (by norm_num)
theorem B535949 : Blo 354756 535949 := bbase (se 3 (by rfl) ⟨100490, by rfl⟩ : syracuseStep 535949 = 200981) (by norm_num)
theorem B535973 : Blo 354756 535973 := bbase (se 4 (by rfl) ⟨50247, by rfl⟩ : syracuseStep 535973 = 100495) (by norm_num)
theorem B535997 : Blo 354756 535997 := bbase (se 3 (by rfl) ⟨100499, by rfl⟩ : syracuseStep 535997 = 200999) (by norm_num)
theorem B536021 : Blo 354756 536021 := bbase (se 7 (by rfl) ⟨6281, by rfl⟩ : syracuseStep 536021 = 12563) (by norm_num)
theorem B601573 : Blo 354756 601573 := bbase (se 4 (by rfl) ⟨56397, by rfl⟩ : syracuseStep 601573 = 112795) (by norm_num)
theorem B536045 : Blo 354756 536045 := bbase (se 3 (by rfl) ⟨100508, by rfl⟩ : syracuseStep 536045 = 201017) (by norm_num)
theorem B536069 : Blo 354756 536069 := bbase (se 4 (by rfl) ⟨50256, by rfl⟩ : syracuseStep 536069 = 100513) (by norm_num)
theorem B536093 : Blo 354756 536093 := bbase (se 3 (by rfl) ⟨100517, by rfl⟩ : syracuseStep 536093 = 201035) (by norm_num)
theorem B798245 : Blo 354756 798245 := bbase (se 4 (by rfl) ⟨74835, by rfl⟩ : syracuseStep 798245 = 149671) (by norm_num)
theorem B536117 : Blo 354756 536117 := bbase (se 5 (by rfl) ⟨25130, by rfl⟩ : syracuseStep 536117 = 50261) (by norm_num)
theorem B601661 : Blo 354756 601661 := bbase (se 3 (by rfl) ⟨112811, by rfl⟩ : syracuseStep 601661 = 225623) (by norm_num)
theorem B536141 : Blo 354756 536141 := bbase (se 3 (by rfl) ⟨100526, by rfl⟩ : syracuseStep 536141 = 201053) (by norm_num)
theorem B10923605 : Blo 354756 10923605 := bbase (se 8 (by rfl) ⟨64005, by rfl⟩ : syracuseStep 10923605 = 128011) (by norm_num)
theorem B536165 : Blo 354756 536165 := bbase (se 4 (by rfl) ⟨50265, by rfl⟩ : syracuseStep 536165 = 100531) (by norm_num)
theorem B798317 : Blo 354756 798317 := bbase (se 3 (by rfl) ⟨149684, by rfl⟩ : syracuseStep 798317 = 299369) (by norm_num)
theorem B536189 : Blo 354756 536189 := bbase (se 3 (by rfl) ⟨100535, by rfl⟩ : syracuseStep 536189 = 201071) (by norm_num)
theorem B536213 : Blo 354756 536213 := bbase (se 6 (by rfl) ⟨12567, by rfl⟩ : syracuseStep 536213 = 25135) (by norm_num)
theorem B765605 : Blo 354756 765605 := bbase (se 4 (by rfl) ⟨71775, by rfl⟩ : syracuseStep 765605 = 143551) (by norm_num)
theorem B536237 : Blo 354756 536237 := bbase (se 3 (by rfl) ⟨100544, by rfl⟩ : syracuseStep 536237 = 201089) (by norm_num)
theorem B798389 : Blo 354756 798389 := bbase (se 5 (by rfl) ⟨37424, by rfl⟩ : syracuseStep 798389 = 74849) (by norm_num)
theorem B601789 : Blo 354756 601789 := bbase (se 3 (by rfl) ⟨112835, by rfl⟩ : syracuseStep 601789 = 225671) (by norm_num)
theorem B536261 : Blo 354756 536261 := bbase (se 4 (by rfl) ⟨50274, by rfl⟩ : syracuseStep 536261 = 100549) (by norm_num)
theorem B536285 : Blo 354756 536285 := bbase (se 3 (by rfl) ⟨100553, by rfl⟩ : syracuseStep 536285 = 201107) (by norm_num)
theorem B536309 : Blo 354756 536309 := bbase (se 5 (by rfl) ⟨25139, by rfl⟩ : syracuseStep 536309 = 50279) (by norm_num)
theorem B798461 : Blo 354756 798461 := bbase (se 3 (by rfl) ⟨149711, by rfl⟩ : syracuseStep 798461 = 299423) (by norm_num)
theorem B536333 : Blo 354756 536333 := bbase (se 3 (by rfl) ⟨100562, by rfl⟩ : syracuseStep 536333 = 201125) (by norm_num)
theorem B601877 : Blo 354756 601877 := bbase (se 6 (by rfl) ⟨14106, by rfl⟩ : syracuseStep 601877 = 28213) (by norm_num)
theorem B3059477 : Blo 354756 3059477 := bbase (se 6 (by rfl) ⟨71706, by rfl⟩ : syracuseStep 3059477 = 143413) (by norm_num)
theorem B536357 : Blo 354756 536357 := bbase (se 4 (by rfl) ⟨50283, by rfl⟩ : syracuseStep 536357 = 100567) (by norm_num)
theorem B1945397 : Blo 354756 1945397 := bbase (se 5 (by rfl) ⟨91190, by rfl⟩ : syracuseStep 1945397 = 182381) (by norm_num)
theorem B536381 : Blo 354756 536381 := bbase (se 3 (by rfl) ⟨100571, by rfl⟩ : syracuseStep 536381 = 201143) (by norm_num)
theorem B798533 : Blo 354756 798533 := bbase (se 4 (by rfl) ⟨74862, by rfl⟩ : syracuseStep 798533 = 149725) (by norm_num)
theorem B536405 : Blo 354756 536405 := bbase (se 9 (by rfl) ⟨1571, by rfl⟩ : syracuseStep 536405 = 3143) (by norm_num)
theorem B536429 : Blo 354756 536429 := bbase (se 3 (by rfl) ⟨100580, by rfl⟩ : syracuseStep 536429 = 201161) (by norm_num)
theorem B1027957 : Blo 354756 1027957 := bbase (se 5 (by rfl) ⟨48185, by rfl⟩ : syracuseStep 1027957 = 96371) (by norm_num)
theorem B536453 : Blo 354756 536453 := bbase (se 4 (by rfl) ⟨50292, by rfl⟩ : syracuseStep 536453 = 100585) (by norm_num)
theorem B798605 : Blo 354756 798605 := bbase (se 3 (by rfl) ⟨149738, by rfl⟩ : syracuseStep 798605 = 299477) (by norm_num)
theorem B602005 : Blo 354756 602005 := bbase (se 6 (by rfl) ⟨14109, by rfl⟩ : syracuseStep 602005 = 28219) (by norm_num)
theorem B536477 : Blo 354756 536477 := bbase (se 3 (by rfl) ⟨100589, by rfl⟩ : syracuseStep 536477 = 201179) (by norm_num)
theorem B536501 : Blo 354756 536501 := bbase (se 5 (by rfl) ⟨25148, by rfl⟩ : syracuseStep 536501 = 50297) (by norm_num)
theorem B536525 : Blo 354756 536525 := bbase (se 3 (by rfl) ⟨100598, by rfl⟩ : syracuseStep 536525 = 201197) (by norm_num)
theorem B798677 : Blo 354756 798677 := bbase (se 7 (by rfl) ⟨9359, by rfl⟩ : syracuseStep 798677 = 18719) (by norm_num)
theorem B536549 : Blo 354756 536549 := bbase (se 4 (by rfl) ⟨50301, by rfl⟩ : syracuseStep 536549 = 100603) (by norm_num)
theorem B602093 : Blo 354756 602093 := bbase (se 3 (by rfl) ⟨112892, by rfl⟩ : syracuseStep 602093 = 225785) (by norm_num)
theorem B536573 : Blo 354756 536573 := bbase (se 3 (by rfl) ⟨100607, by rfl⟩ : syracuseStep 536573 = 201215) (by norm_num)
theorem B536597 : Blo 354756 536597 := bbase (se 6 (by rfl) ⟨12576, by rfl⟩ : syracuseStep 536597 = 25153) (by norm_num)
theorem B798749 : Blo 354756 798749 := bbase (se 3 (by rfl) ⟨149765, by rfl⟩ : syracuseStep 798749 = 299531) (by norm_num)
theorem B536621 : Blo 354756 536621 := bbase (se 3 (by rfl) ⟨100616, by rfl⟩ : syracuseStep 536621 = 201233) (by norm_num)
theorem B536645 : Blo 354756 536645 := bbase (se 4 (by rfl) ⟨50310, by rfl⟩ : syracuseStep 536645 = 100621) (by norm_num)
theorem B536669 : Blo 354756 536669 := bbase (se 3 (by rfl) ⟨100625, by rfl⟩ : syracuseStep 536669 = 201251) (by norm_num)
theorem B798821 : Blo 354756 798821 := bbase (se 4 (by rfl) ⟨74889, by rfl⟩ : syracuseStep 798821 = 149779) (by norm_num)
theorem B602221 : Blo 354756 602221 := bbase (se 3 (by rfl) ⟨112916, by rfl⟩ : syracuseStep 602221 = 225833) (by norm_num)
theorem B536693 : Blo 354756 536693 := bbase (se 5 (by rfl) ⟨25157, by rfl⟩ : syracuseStep 536693 = 50315) (by norm_num)
theorem B536717 : Blo 354756 536717 := bbase (se 3 (by rfl) ⟨100634, by rfl⟩ : syracuseStep 536717 = 201269) (by norm_num)
theorem B569501 : Blo 354756 569501 := bbase (se 3 (by rfl) ⟨106781, by rfl⟩ : syracuseStep 569501 = 213563) (by norm_num)
theorem B536741 : Blo 354756 536741 := bbase (se 4 (by rfl) ⟨50319, by rfl⟩ : syracuseStep 536741 = 100639) (by norm_num)
theorem B798893 : Blo 354756 798893 := bbase (se 3 (by rfl) ⟨149792, by rfl⟩ : syracuseStep 798893 = 299585) (by norm_num)
theorem B536765 : Blo 354756 536765 := bbase (se 3 (by rfl) ⟨100643, by rfl⟩ : syracuseStep 536765 = 201287) (by norm_num)
theorem B602309 : Blo 354756 602309 := bbase (se 4 (by rfl) ⟨56466, by rfl⟩ : syracuseStep 602309 = 112933) (by norm_num)
theorem B1519829 : Blo 354756 1519829 := bbase (se 7 (by rfl) ⟨17810, by rfl⟩ : syracuseStep 1519829 = 35621) (by norm_num)
theorem B536789 : Blo 354756 536789 := bbase (se 7 (by rfl) ⟨6290, by rfl⟩ : syracuseStep 536789 = 12581) (by norm_num)
theorem B536813 : Blo 354756 536813 := bbase (se 3 (by rfl) ⟨100652, by rfl⟩ : syracuseStep 536813 = 201305) (by norm_num)
theorem B798965 : Blo 354756 798965 := bbase (se 5 (by rfl) ⟨37451, by rfl⟩ : syracuseStep 798965 = 74903) (by norm_num)
theorem B536837 : Blo 354756 536837 := bbase (se 4 (by rfl) ⟨50328, by rfl⟩ : syracuseStep 536837 = 100657) (by norm_num)
theorem B536861 : Blo 354756 536861 := bbase (se 3 (by rfl) ⟨100661, by rfl⟩ : syracuseStep 536861 = 201323) (by norm_num)
theorem B536885 : Blo 354756 536885 := bbase (se 5 (by rfl) ⟨25166, by rfl⟩ : syracuseStep 536885 = 50333) (by norm_num)
theorem B799037 : Blo 354756 799037 := bbase (se 3 (by rfl) ⟨149819, by rfl⟩ : syracuseStep 799037 = 299639) (by norm_num)
theorem B602437 : Blo 354756 602437 := bbase (se 4 (by rfl) ⟨56478, by rfl⟩ : syracuseStep 602437 = 112957) (by norm_num)
theorem B536909 : Blo 354756 536909 := bbase (se 3 (by rfl) ⟨100670, by rfl⟩ : syracuseStep 536909 = 201341) (by norm_num)
theorem B569693 : Blo 354756 569693 := bbase (se 3 (by rfl) ⟨106817, by rfl⟩ : syracuseStep 569693 = 213635) (by norm_num)
theorem B536933 : Blo 354756 536933 := bbase (se 4 (by rfl) ⟨50337, by rfl⟩ : syracuseStep 536933 = 100675) (by norm_num)
theorem B1814885 : Blo 354756 1814885 := bbase (se 4 (by rfl) ⟨170145, by rfl⟩ : syracuseStep 1814885 = 340291) (by norm_num)
theorem B536957 : Blo 354756 536957 := bbase (se 3 (by rfl) ⟨100679, by rfl⟩ : syracuseStep 536957 = 201359) (by norm_num)
theorem B799109 : Blo 354756 799109 := bbase (se 4 (by rfl) ⟨74916, by rfl⟩ : syracuseStep 799109 = 149833) (by norm_num)
theorem B536981 : Blo 354756 536981 := bbase (se 6 (by rfl) ⟨12585, by rfl⟩ : syracuseStep 536981 = 25171) (by norm_num)
theorem B602525 : Blo 354756 602525 := bbase (se 3 (by rfl) ⟨112973, by rfl⟩ : syracuseStep 602525 = 225947) (by norm_num)
theorem B537005 : Blo 354756 537005 := bbase (se 3 (by rfl) ⟨100688, by rfl⟩ : syracuseStep 537005 = 201377) (by norm_num)
theorem B537029 : Blo 354756 537029 := bbase (se 4 (by rfl) ⟨50346, by rfl⟩ : syracuseStep 537029 = 100693) (by norm_num)
theorem B799181 : Blo 354756 799181 := bbase (se 3 (by rfl) ⟨149846, by rfl⟩ : syracuseStep 799181 = 299693) (by norm_num)
theorem B537053 : Blo 354756 537053 := bbase (se 3 (by rfl) ⟨100697, by rfl⟩ : syracuseStep 537053 = 201395) (by norm_num)
theorem B537077 : Blo 354756 537077 := bbase (se 5 (by rfl) ⟨25175, by rfl⟩ : syracuseStep 537077 = 50351) (by norm_num)
theorem B537101 : Blo 354756 537101 := bbase (se 3 (by rfl) ⟨100706, by rfl⟩ : syracuseStep 537101 = 201413) (by norm_num)
theorem B799253 : Blo 354756 799253 := bbase (se 6 (by rfl) ⟨18732, by rfl⟩ : syracuseStep 799253 = 37465) (by norm_num)
theorem B3650069 : Blo 354756 3650069 := bbase (se 6 (by rfl) ⟨85548, by rfl⟩ : syracuseStep 3650069 = 171097) (by norm_num)
theorem B602653 : Blo 354756 602653 := bbase (se 3 (by rfl) ⟨112997, by rfl⟩ : syracuseStep 602653 = 225995) (by norm_num)
theorem B537125 : Blo 354756 537125 := bbase (se 4 (by rfl) ⟨50355, by rfl⟩ : syracuseStep 537125 = 100711) (by norm_num)
theorem B2142773 : Blo 354756 2142773 := bbase (se 5 (by rfl) ⟨100442, by rfl⟩ : syracuseStep 2142773 = 200885) (by norm_num)
theorem B537149 : Blo 354756 537149 := bbase (se 3 (by rfl) ⟨100715, by rfl⟩ : syracuseStep 537149 = 201431) (by norm_num)
theorem B537173 : Blo 354756 537173 := bbase (se 8 (by rfl) ⟨3147, by rfl⟩ : syracuseStep 537173 = 6295) (by norm_num)
theorem B799325 : Blo 354756 799325 := bbase (se 3 (by rfl) ⟨149873, by rfl⟩ : syracuseStep 799325 = 299747) (by norm_num)
theorem B537197 : Blo 354756 537197 := bbase (se 3 (by rfl) ⟨100724, by rfl⟩ : syracuseStep 537197 = 201449) (by norm_num)
theorem B602741 : Blo 354756 602741 := bbase (se 5 (by rfl) ⟨28253, by rfl⟩ : syracuseStep 602741 = 56507) (by norm_num)
theorem B537221 : Blo 354756 537221 := bbase (se 4 (by rfl) ⟨50364, by rfl⟩ : syracuseStep 537221 = 100729) (by norm_num)
theorem B537245 : Blo 354756 537245 := bbase (se 3 (by rfl) ⟨100733, by rfl⟩ : syracuseStep 537245 = 201467) (by norm_num)
theorem B799397 : Blo 354756 799397 := bbase (se 4 (by rfl) ⟨74943, by rfl⟩ : syracuseStep 799397 = 149887) (by norm_num)
theorem B537269 : Blo 354756 537269 := bbase (se 5 (by rfl) ⟨25184, by rfl⟩ : syracuseStep 537269 = 50369) (by norm_num)
theorem B537293 : Blo 354756 537293 := bbase (se 3 (by rfl) ⟨100742, by rfl⟩ : syracuseStep 537293 = 201485) (by norm_num)
theorem B537317 : Blo 354756 537317 := bbase (se 4 (by rfl) ⟨50373, by rfl⟩ : syracuseStep 537317 = 100747) (by norm_num)
theorem B799469 : Blo 354756 799469 := bbase (se 3 (by rfl) ⟨149900, by rfl⟩ : syracuseStep 799469 = 299801) (by norm_num)
theorem B602869 : Blo 354756 602869 := bbase (se 5 (by rfl) ⟨28259, by rfl⟩ : syracuseStep 602869 = 56519) (by norm_num)
theorem B1356533 : Blo 354756 1356533 := bbase (se 5 (by rfl) ⟨63587, by rfl⟩ : syracuseStep 1356533 = 127175) (by norm_num)
theorem B537341 : Blo 354756 537341 := bbase (se 3 (by rfl) ⟨100751, by rfl⟩ : syracuseStep 537341 = 201503) (by norm_num)
theorem B537365 : Blo 354756 537365 := bbase (se 6 (by rfl) ⟨12594, by rfl⟩ : syracuseStep 537365 = 25189) (by norm_num)
theorem B537389 : Blo 354756 537389 := bbase (se 3 (by rfl) ⟨100760, by rfl⟩ : syracuseStep 537389 = 201521) (by norm_num)
theorem B799541 : Blo 354756 799541 := bbase (se 5 (by rfl) ⟨37478, by rfl⟩ : syracuseStep 799541 = 74957) (by norm_num)
theorem B930629 : Blo 354756 930629 := bbase (se 4 (by rfl) ⟨87246, by rfl⟩ : syracuseStep 930629 = 174493) (by norm_num)
theorem B537413 : Blo 354756 537413 := bbase (se 4 (by rfl) ⟨50382, by rfl⟩ : syracuseStep 537413 = 100765) (by norm_num)
theorem B602957 : Blo 354756 602957 := bbase (se 3 (by rfl) ⟨113054, by rfl⟩ : syracuseStep 602957 = 226109) (by norm_num)
theorem B537437 : Blo 354756 537437 := bbase (se 3 (by rfl) ⟨100769, by rfl⟩ : syracuseStep 537437 = 201539) (by norm_num)
theorem B537461 : Blo 354756 537461 := bbase (se 5 (by rfl) ⟨25193, by rfl⟩ : syracuseStep 537461 = 50387) (by norm_num)
theorem B799613 : Blo 354756 799613 := bbase (se 3 (by rfl) ⟨149927, by rfl⟩ : syracuseStep 799613 = 299855) (by norm_num)
theorem B1848197 : Blo 354756 1848197 := bbase (se 4 (by rfl) ⟨173268, by rfl⟩ : syracuseStep 1848197 = 346537) (by norm_num)
theorem B537485 : Blo 354756 537485 := bbase (se 3 (by rfl) ⟨100778, by rfl⟩ : syracuseStep 537485 = 201557) (by norm_num)
theorem B1160101 : Blo 354756 1160101 := bbase (se 4 (by rfl) ⟨108759, by rfl⟩ : syracuseStep 1160101 = 217519) (by norm_num)
theorem B537509 : Blo 354756 537509 := bbase (se 4 (by rfl) ⟨50391, by rfl⟩ : syracuseStep 537509 = 100783) (by norm_num)
theorem B537533 : Blo 354756 537533 := bbase (se 3 (by rfl) ⟨100787, by rfl⟩ : syracuseStep 537533 = 201575) (by norm_num)
theorem B799685 : Blo 354756 799685 := bbase (se 4 (by rfl) ⟨74970, by rfl⟩ : syracuseStep 799685 = 149941) (by norm_num)
theorem B603085 : Blo 354756 603085 := bbase (se 3 (by rfl) ⟨113078, by rfl⟩ : syracuseStep 603085 = 226157) (by norm_num)
theorem B1029077 : Blo 354756 1029077 := bbase (se 7 (by rfl) ⟨12059, by rfl⟩ : syracuseStep 1029077 = 24119) (by norm_num)
theorem B537557 : Blo 354756 537557 := bbase (se 7 (by rfl) ⟨6299, by rfl⟩ : syracuseStep 537557 = 12599) (by norm_num)
theorem B537581 : Blo 354756 537581 := bbase (se 3 (by rfl) ⟨100796, by rfl⟩ : syracuseStep 537581 = 201593) (by norm_num)
theorem B898037 : Blo 354756 898037 := bbase (se 5 (by rfl) ⟨42095, by rfl⟩ : syracuseStep 898037 = 84191) (by norm_num)
theorem B537605 : Blo 354756 537605 := bbase (se 4 (by rfl) ⟨50400, by rfl⟩ : syracuseStep 537605 = 100801) (by norm_num)
theorem B799757 : Blo 354756 799757 := bbase (se 3 (by rfl) ⟨149954, by rfl⟩ : syracuseStep 799757 = 299909) (by norm_num)
theorem B1356821 : Blo 354756 1356821 := bbase (se 6 (by rfl) ⟨31800, by rfl⟩ : syracuseStep 1356821 = 63601) (by norm_num)
theorem B537629 : Blo 354756 537629 := bbase (se 3 (by rfl) ⟨100805, by rfl⟩ : syracuseStep 537629 = 201611) (by norm_num)
theorem B603173 : Blo 354756 603173 := bbase (se 4 (by rfl) ⟨56547, by rfl⟩ : syracuseStep 603173 = 113095) (by norm_num)
theorem B537653 : Blo 354756 537653 := bbase (se 5 (by rfl) ⟨25202, by rfl⟩ : syracuseStep 537653 = 50405) (by norm_num)
theorem B537677 : Blo 354756 537677 := bbase (se 3 (by rfl) ⟨100814, by rfl⟩ : syracuseStep 537677 = 201629) (by norm_num)
theorem B2274389 : Blo 354756 2274389 := bbase (se 8 (by rfl) ⟨13326, by rfl⟩ : syracuseStep 2274389 = 26653) (by norm_num)
theorem B799829 : Blo 354756 799829 := bbase (se 8 (by rfl) ⟨4686, by rfl⟩ : syracuseStep 799829 = 9373) (by norm_num)
theorem B537701 : Blo 354756 537701 := bbase (se 4 (by rfl) ⟨50409, by rfl⟩ : syracuseStep 537701 = 100819) (by norm_num)
theorem B537725 : Blo 354756 537725 := bbase (se 3 (by rfl) ⟨100823, by rfl⟩ : syracuseStep 537725 = 201647) (by norm_num)
theorem B537749 : Blo 354756 537749 := bbase (se 6 (by rfl) ⟨12603, by rfl⟩ : syracuseStep 537749 = 25207) (by norm_num)
theorem B799901 : Blo 354756 799901 := bbase (se 3 (by rfl) ⟨149981, by rfl⟩ : syracuseStep 799901 = 299963) (by norm_num)
theorem B603301 : Blo 354756 603301 := bbase (se 4 (by rfl) ⟨56559, by rfl⟩ : syracuseStep 603301 = 113119) (by norm_num)
theorem B537773 : Blo 354756 537773 := bbase (se 3 (by rfl) ⟨100832, by rfl⟩ : syracuseStep 537773 = 201665) (by norm_num)
theorem B898229 : Blo 354756 898229 := bbase (se 5 (by rfl) ⟨42104, by rfl⟩ : syracuseStep 898229 = 84209) (by norm_num)
theorem B537797 : Blo 354756 537797 := bbase (se 4 (by rfl) ⟨50418, by rfl⟩ : syracuseStep 537797 = 100837) (by norm_num)
theorem B537821 : Blo 354756 537821 := bbase (se 3 (by rfl) ⟨100841, by rfl⟩ : syracuseStep 537821 = 201683) (by norm_num)
theorem B799973 : Blo 354756 799973 := bbase (se 4 (by rfl) ⟨74997, by rfl⟩ : syracuseStep 799973 = 149995) (by norm_num)
theorem B537845 : Blo 354756 537845 := bbase (se 5 (by rfl) ⟨25211, by rfl⟩ : syracuseStep 537845 = 50423) (by norm_num)
theorem B603389 : Blo 354756 603389 := bbase (se 3 (by rfl) ⟨113135, by rfl⟩ : syracuseStep 603389 = 226271) (by norm_num)
theorem B963845 : Blo 354756 963845 := bbase (se 4 (by rfl) ⟨90360, by rfl⟩ : syracuseStep 963845 = 180721) (by norm_num)
theorem B537869 : Blo 354756 537869 := bbase (se 3 (by rfl) ⟨100850, by rfl⟩ : syracuseStep 537869 = 201701) (by norm_num)
theorem B537893 : Blo 354756 537893 := bbase (se 4 (by rfl) ⟨50427, by rfl⟩ : syracuseStep 537893 = 100855) (by norm_num)
theorem B800045 : Blo 354756 800045 := bbase (se 3 (by rfl) ⟨150008, by rfl⟩ : syracuseStep 800045 = 300017) (by norm_num)
theorem B537917 : Blo 354756 537917 := bbase (se 3 (by rfl) ⟨100859, by rfl⟩ : syracuseStep 537917 = 201719) (by norm_num)
theorem B537941 : Blo 354756 537941 := bbase (se 13 (by rfl) ⟨98, by rfl⟩ : syracuseStep 537941 = 197) (by norm_num)
theorem B406877 : Blo 354756 406877 := bbase (se 3 (by rfl) ⟨76289, by rfl⟩ : syracuseStep 406877 = 152579) (by norm_num)
theorem B537965 : Blo 354756 537965 := bbase (se 3 (by rfl) ⟨100868, by rfl⟩ : syracuseStep 537965 = 201737) (by norm_num)
theorem B800117 : Blo 354756 800117 := bbase (se 5 (by rfl) ⟨37505, by rfl⟩ : syracuseStep 800117 = 75011) (by norm_num)
theorem B603517 : Blo 354756 603517 := bbase (se 3 (by rfl) ⟨113159, by rfl⟩ : syracuseStep 603517 = 226319) (by norm_num)
theorem B537989 : Blo 354756 537989 := bbase (se 4 (by rfl) ⟨50436, by rfl⟩ : syracuseStep 537989 = 100873) (by norm_num)
theorem B538013 : Blo 354756 538013 := bbase (se 3 (by rfl) ⟨100877, by rfl⟩ : syracuseStep 538013 = 201755) (by norm_num)
theorem B538037 : Blo 354756 538037 := bbase (se 5 (by rfl) ⟨25220, by rfl⟩ : syracuseStep 538037 = 50441) (by norm_num)
theorem B800189 : Blo 354756 800189 := bbase (se 3 (by rfl) ⟨150035, by rfl⟩ : syracuseStep 800189 = 300071) (by norm_num)
theorem B538061 : Blo 354756 538061 := bbase (se 3 (by rfl) ⟨100886, by rfl⟩ : syracuseStep 538061 = 201773) (by norm_num)
theorem B603605 : Blo 354756 603605 := bbase (se 7 (by rfl) ⟨7073, by rfl⟩ : syracuseStep 603605 = 14147) (by norm_num)
theorem B538085 : Blo 354756 538085 := bbase (se 4 (by rfl) ⟨50445, by rfl⟩ : syracuseStep 538085 = 100891) (by norm_num)
theorem B538109 : Blo 354756 538109 := bbase (se 3 (by rfl) ⟨100895, by rfl⟩ : syracuseStep 538109 = 201791) (by norm_num)
theorem B800261 : Blo 354756 800261 := bbase (se 4 (by rfl) ⟨75024, by rfl⟩ : syracuseStep 800261 = 150049) (by norm_num)
theorem B898573 : Blo 354756 898573 := bbase (se 3 (by rfl) ⟨168482, by rfl⟩ : syracuseStep 898573 = 336965) (by norm_num)
theorem B538133 : Blo 354756 538133 := bbase (se 6 (by rfl) ⟨12612, by rfl⟩ : syracuseStep 538133 = 25225) (by norm_num)
theorem B800333 : Blo 354756 800333 := bbase (se 3 (by rfl) ⟨150062, by rfl⟩ : syracuseStep 800333 = 300125) (by norm_num)
theorem B603733 : Blo 354756 603733 := bbase (se 8 (by rfl) ⟨3537, by rfl⟩ : syracuseStep 603733 = 7075) (by norm_num)
theorem B1816181 : Blo 354756 1816181 := bbase (se 5 (by rfl) ⟨85133, by rfl⟩ : syracuseStep 1816181 = 170267) (by norm_num)
theorem B898685 : Blo 354756 898685 := bbase (se 3 (by rfl) ⟨168503, by rfl⟩ : syracuseStep 898685 = 337007) (by norm_num)
theorem B800405 : Blo 354756 800405 := bbase (se 6 (by rfl) ⟨18759, by rfl⟩ : syracuseStep 800405 = 37519) (by norm_num)
theorem B603821 : Blo 354756 603821 := bbase (se 3 (by rfl) ⟨113216, by rfl⟩ : syracuseStep 603821 = 226433) (by norm_num)
theorem B1717957 : Blo 354756 1717957 := bbase (se 4 (by rfl) ⟨161058, by rfl⟩ : syracuseStep 1717957 = 322117) (by norm_num)
theorem B800477 : Blo 354756 800477 := bbase (se 3 (by rfl) ⟨150089, by rfl⟩ : syracuseStep 800477 = 300179) (by norm_num)
theorem B571141 : Blo 354756 571141 := bbase (se 4 (by rfl) ⟨53544, by rfl⟩ : syracuseStep 571141 = 107089) (by norm_num)
theorem B800549 : Blo 354756 800549 := bbase (se 4 (by rfl) ⟨75051, by rfl⟩ : syracuseStep 800549 = 150103) (by norm_num)
theorem B603949 : Blo 354756 603949 := bbase (se 3 (by rfl) ⟨113240, by rfl⟩ : syracuseStep 603949 = 226481) (by norm_num)
theorem B898877 : Blo 354756 898877 := bbase (se 3 (by rfl) ⟨168539, by rfl⟩ : syracuseStep 898877 = 337079) (by norm_num)
theorem B505693 : Blo 354756 505693 := bbase (se 3 (by rfl) ⟨94817, by rfl⟩ : syracuseStep 505693 = 189635) (by norm_num)
theorem B800621 : Blo 354756 800621 := bbase (se 3 (by rfl) ⟨150116, by rfl⟩ : syracuseStep 800621 = 300233) (by norm_num)
theorem B604037 : Blo 354756 604037 := bbase (se 4 (by rfl) ⟨56628, by rfl⟩ : syracuseStep 604037 = 113257) (by norm_num)
theorem B800693 : Blo 354756 800693 := bbase (se 5 (by rfl) ⟨37532, by rfl⟩ : syracuseStep 800693 = 75065) (by norm_num)
theorem B1521605 : Blo 354756 1521605 := bbase (se 4 (by rfl) ⟨142650, by rfl⟩ : syracuseStep 1521605 = 285301) (by norm_num)
theorem B800765 : Blo 354756 800765 := bbase (se 3 (by rfl) ⟨150143, by rfl⟩ : syracuseStep 800765 = 300287) (by norm_num)
theorem B604165 : Blo 354756 604165 := bbase (se 4 (by rfl) ⟨56640, by rfl⟩ : syracuseStep 604165 = 113281) (by norm_num)
theorem B800837 : Blo 354756 800837 := bbase (se 4 (by rfl) ⟨75078, by rfl⟩ : syracuseStep 800837 = 150157) (by norm_num)
theorem B8697941 : Blo 354756 8697941 := bbase (se 8 (by rfl) ⟨50964, by rfl⟩ : syracuseStep 8697941 = 101929) (by norm_num)
theorem B604253 : Blo 354756 604253 := bbase (se 3 (by rfl) ⟨113297, by rfl⟩ : syracuseStep 604253 = 226595) (by norm_num)
theorem B1620101 : Blo 354756 1620101 := bbase (se 4 (by rfl) ⟨151884, by rfl⟩ : syracuseStep 1620101 = 303769) (by norm_num)
theorem B800909 : Blo 354756 800909 := bbase (se 3 (by rfl) ⟨150170, by rfl⟩ : syracuseStep 800909 = 300341) (by norm_num)
theorem B899221 : Blo 354756 899221 := bbase (se 6 (by rfl) ⟨21075, by rfl⟩ : syracuseStep 899221 = 42151) (by norm_num)
theorem B506029 : Blo 354756 506029 := bbase (se 3 (by rfl) ⟨94880, by rfl⟩ : syracuseStep 506029 = 189761) (by norm_num)
theorem B1358005 : Blo 354756 1358005 := bbase (se 5 (by rfl) ⟨63656, by rfl⟩ : syracuseStep 1358005 = 127313) (by norm_num)
theorem B800981 : Blo 354756 800981 := bbase (se 7 (by rfl) ⟨9386, by rfl⟩ : syracuseStep 800981 = 18773) (by norm_num)
theorem B604381 : Blo 354756 604381 := bbase (se 3 (by rfl) ⟨113321, by rfl⟩ : syracuseStep 604381 = 226643) (by norm_num)
theorem B899333 : Blo 354756 899333 := bbase (se 4 (by rfl) ⟨84312, by rfl⟩ : syracuseStep 899333 = 168625) (by norm_num)
theorem B801053 : Blo 354756 801053 := bbase (se 3 (by rfl) ⟨150197, by rfl⟩ : syracuseStep 801053 = 300395) (by norm_num)
theorem B604469 : Blo 354756 604469 := bbase (se 5 (by rfl) ⟨28334, by rfl⟩ : syracuseStep 604469 = 56669) (by norm_num)
theorem B440641 : Blo 354756 440641 := bbase (se 2 (by rfl) ⟨165240, by rfl⟩ : syracuseStep 440641 = 330481) (by norm_num)
theorem B801125 : Blo 354756 801125 := bbase (se 4 (by rfl) ⟨75105, by rfl⟩ : syracuseStep 801125 = 150211) (by norm_num)
theorem B506245 : Blo 354756 506245 := bbase (se 4 (by rfl) ⟨47460, by rfl⟩ : syracuseStep 506245 = 94921) (by norm_num)
theorem B768413 : Blo 354756 768413 := bbase (se 3 (by rfl) ⟨144077, by rfl⟩ : syracuseStep 768413 = 288155) (by norm_num)
theorem B801197 : Blo 354756 801197 := bbase (se 3 (by rfl) ⟨150224, by rfl⟩ : syracuseStep 801197 = 300449) (by norm_num)
theorem B604597 : Blo 354756 604597 := bbase (se 5 (by rfl) ⟨28340, by rfl⟩ : syracuseStep 604597 = 56681) (by norm_num)
theorem B899525 : Blo 354756 899525 := bbase (se 4 (by rfl) ⟨84330, by rfl⟩ : syracuseStep 899525 = 168661) (by norm_num)
theorem B1358309 : Blo 354756 1358309 := bbase (se 4 (by rfl) ⟨127341, by rfl⟩ : syracuseStep 1358309 = 254683) (by norm_num)
theorem B801269 : Blo 354756 801269 := bbase (se 5 (by rfl) ⟨37559, by rfl⟩ : syracuseStep 801269 = 75119) (by norm_num)
theorem B604685 : Blo 354756 604685 := bbase (se 3 (by rfl) ⟨113378, by rfl⟩ : syracuseStep 604685 = 226757) (by norm_num)
theorem B801341 : Blo 354756 801341 := bbase (se 3 (by rfl) ⟨150251, by rfl⟩ : syracuseStep 801341 = 300503) (by norm_num)
theorem B801413 : Blo 354756 801413 := bbase (se 4 (by rfl) ⟨75132, by rfl⟩ : syracuseStep 801413 = 150265) (by norm_num)
theorem B604813 : Blo 354756 604813 := bbase (se 3 (by rfl) ⟨113402, by rfl⟩ : syracuseStep 604813 = 226805) (by norm_num)
theorem B801485 : Blo 354756 801485 := bbase (se 3 (by rfl) ⟨150278, by rfl⟩ : syracuseStep 801485 = 300557) (by norm_num)
theorem B604901 : Blo 354756 604901 := bbase (se 4 (by rfl) ⟨56709, by rfl⟩ : syracuseStep 604901 = 113419) (by norm_num)
theorem B506621 : Blo 354756 506621 := bbase (se 3 (by rfl) ⟨94991, by rfl⟩ : syracuseStep 506621 = 189983) (by norm_num)
theorem B801557 : Blo 354756 801557 := bbase (se 6 (by rfl) ⟨18786, by rfl⟩ : syracuseStep 801557 = 37573) (by norm_num)
theorem B899869 : Blo 354756 899869 := bbase (se 3 (by rfl) ⟨168725, by rfl⟩ : syracuseStep 899869 = 337451) (by norm_num)
theorem B801629 : Blo 354756 801629 := bbase (se 3 (by rfl) ⟨150305, by rfl⟩ : syracuseStep 801629 = 300611) (by norm_num)
theorem B605029 : Blo 354756 605029 := bbase (se 4 (by rfl) ⟨56721, by rfl⟩ : syracuseStep 605029 = 113443) (by norm_num)
theorem B899981 : Blo 354756 899981 := bbase (se 3 (by rfl) ⟨168746, by rfl⟩ : syracuseStep 899981 = 337493) (by norm_num)
theorem B801701 : Blo 354756 801701 := bbase (se 4 (by rfl) ⟨75159, by rfl⟩ : syracuseStep 801701 = 150319) (by norm_num)
theorem B1522597 : Blo 354756 1522597 := bbase (se 4 (by rfl) ⟨142743, by rfl⟩ : syracuseStep 1522597 = 285487) (by norm_num)
theorem B605117 : Blo 354756 605117 := bbase (se 3 (by rfl) ⟨113459, by rfl⟩ : syracuseStep 605117 = 226919) (by norm_num)
theorem B801773 : Blo 354756 801773 := bbase (se 3 (by rfl) ⟨150332, by rfl⟩ : syracuseStep 801773 = 300665) (by norm_num)
theorem B801845 : Blo 354756 801845 := bbase (se 5 (by rfl) ⟨37586, by rfl⟩ : syracuseStep 801845 = 75173) (by norm_num)
theorem B605245 : Blo 354756 605245 := bbase (se 3 (by rfl) ⟨113483, by rfl⟩ : syracuseStep 605245 = 226967) (by norm_num)
theorem B900173 : Blo 354756 900173 := bbase (se 3 (by rfl) ⟨168782, by rfl⟩ : syracuseStep 900173 = 337565) (by norm_num)
theorem B572525 : Blo 354756 572525 := bbase (se 3 (by rfl) ⟨107348, by rfl⟩ : syracuseStep 572525 = 214697) (by norm_num)
theorem B801917 : Blo 354756 801917 := bbase (se 3 (by rfl) ⟨150359, by rfl⟩ : syracuseStep 801917 = 300719) (by norm_num)
theorem B605333 : Blo 354756 605333 := bbase (se 6 (by rfl) ⟨14187, by rfl⟩ : syracuseStep 605333 = 28375) (by norm_num)
theorem B801989 : Blo 354756 801989 := bbase (se 4 (by rfl) ⟨75186, by rfl⟩ : syracuseStep 801989 = 150373) (by norm_num)
theorem B802061 : Blo 354756 802061 := bbase (se 3 (by rfl) ⟨150386, by rfl⟩ : syracuseStep 802061 = 300773) (by norm_num)
theorem B572717 : Blo 354756 572717 := bbase (se 3 (by rfl) ⟨107384, by rfl⟩ : syracuseStep 572717 = 214769) (by norm_num)
theorem B2702645 : Blo 354756 2702645 := bbase (se 5 (by rfl) ⟨126686, by rfl⟩ : syracuseStep 2702645 = 253373) (by norm_num)
theorem B802133 : Blo 354756 802133 := bbase (se 11 (by rfl) ⟨587, by rfl⟩ : syracuseStep 802133 = 1175) (by norm_num)
theorem B802205 : Blo 354756 802205 := bbase (se 3 (by rfl) ⟨150413, by rfl⟩ : syracuseStep 802205 = 300827) (by norm_num)
theorem B900517 : Blo 354756 900517 := bbase (se 4 (by rfl) ⟨84423, by rfl⟩ : syracuseStep 900517 = 168847) (by norm_num)
theorem B802277 : Blo 354756 802277 := bbase (se 4 (by rfl) ⟨75213, by rfl⟩ : syracuseStep 802277 = 150427) (by norm_num)
theorem B900629 : Blo 354756 900629 := bbase (se 6 (by rfl) ⟨21108, by rfl⟩ : syracuseStep 900629 = 42217) (by norm_num)
theorem B802349 : Blo 354756 802349 := bbase (se 3 (by rfl) ⟨150440, by rfl⟩ : syracuseStep 802349 = 300881) (by norm_num)
theorem B802421 : Blo 354756 802421 := bbase (se 5 (by rfl) ⟨37613, by rfl⟩ : syracuseStep 802421 = 75227) (by norm_num)
theorem B802493 : Blo 354756 802493 := bbase (se 3 (by rfl) ⟨150467, by rfl⟩ : syracuseStep 802493 = 300935) (by norm_num)
theorem B900821 : Blo 354756 900821 := bbase (se 7 (by rfl) ⟨10556, by rfl⟩ : syracuseStep 900821 = 21113) (by norm_num)
theorem B802565 : Blo 354756 802565 := bbase (se 4 (by rfl) ⟨75240, by rfl⟩ : syracuseStep 802565 = 150481) (by norm_num)
theorem B802637 : Blo 354756 802637 := bbase (se 3 (by rfl) ⟨150494, by rfl⟩ : syracuseStep 802637 = 300989) (by norm_num)
theorem B802709 : Blo 354756 802709 := bbase (se 6 (by rfl) ⟨18813, by rfl⟩ : syracuseStep 802709 = 37627) (by norm_num)
theorem B540629 : Blo 354756 540629 := bbase (se 7 (by rfl) ⟨6335, by rfl⟩ : syracuseStep 540629 = 12671) (by norm_num)
theorem B966613 : Blo 354756 966613 := bbase (se 7 (by rfl) ⟨11327, by rfl⟩ : syracuseStep 966613 = 22655) (by norm_num)
theorem B802781 : Blo 354756 802781 := bbase (se 3 (by rfl) ⟨150521, by rfl⟩ : syracuseStep 802781 = 301043) (by norm_num)
theorem B802853 : Blo 354756 802853 := bbase (se 4 (by rfl) ⟨75267, by rfl⟩ : syracuseStep 802853 = 150535) (by norm_num)
theorem B901165 : Blo 354756 901165 := bbase (se 3 (by rfl) ⟨168968, by rfl⟩ : syracuseStep 901165 = 337937) (by norm_num)
theorem B802925 : Blo 354756 802925 := bbase (se 3 (by rfl) ⟨150548, by rfl⟩ : syracuseStep 802925 = 301097) (by norm_num)
theorem B606341 : Blo 354756 606341 := bbase (se 4 (by rfl) ⟨56844, by rfl⟩ : syracuseStep 606341 = 113689) (by norm_num)
theorem B508045 : Blo 354756 508045 := bbase (se 3 (by rfl) ⟨95258, by rfl⟩ : syracuseStep 508045 = 190517) (by norm_num)
theorem B901277 : Blo 354756 901277 := bbase (se 3 (by rfl) ⟨168989, by rfl⟩ : syracuseStep 901277 = 337979) (by norm_num)
theorem B802997 : Blo 354756 802997 := bbase (se 5 (by rfl) ⟨37640, by rfl⟩ : syracuseStep 802997 = 75281) (by norm_num)
theorem B868589 : Blo 354756 868589 := bbase (se 3 (by rfl) ⟨162860, by rfl⟩ : syracuseStep 868589 = 325721) (by norm_num)
theorem B803069 : Blo 354756 803069 := bbase (se 3 (by rfl) ⟨150575, by rfl⟩ : syracuseStep 803069 = 301151) (by norm_num)
theorem B803141 : Blo 354756 803141 := bbase (se 4 (by rfl) ⟨75294, by rfl⟩ : syracuseStep 803141 = 150589) (by norm_num)
theorem B901469 : Blo 354756 901469 := bbase (se 3 (by rfl) ⟨169025, by rfl⟩ : syracuseStep 901469 = 338051) (by norm_num)
theorem B803213 : Blo 354756 803213 := bbase (se 3 (by rfl) ⟨150602, by rfl⟩ : syracuseStep 803213 = 301205) (by norm_num)
theorem B803285 : Blo 354756 803285 := bbase (se 7 (by rfl) ⟨9413, by rfl⟩ : syracuseStep 803285 = 18827) (by norm_num)
theorem B803357 : Blo 354756 803357 := bbase (se 3 (by rfl) ⟨150629, by rfl⟩ : syracuseStep 803357 = 301259) (by norm_num)
theorem B1360421 : Blo 354756 1360421 := bbase (se 4 (by rfl) ⟨127539, by rfl⟩ : syracuseStep 1360421 = 255079) (by norm_num)
theorem B770629 : Blo 354756 770629 := bbase (se 4 (by rfl) ⟨72246, by rfl⟩ : syracuseStep 770629 = 144493) (by norm_num)
theorem B574037 : Blo 354756 574037 := bbase (se 8 (by rfl) ⟨3363, by rfl⟩ : syracuseStep 574037 = 6727) (by norm_num)
theorem B803429 : Blo 354756 803429 := bbase (se 4 (by rfl) ⟨75321, by rfl⟩ : syracuseStep 803429 = 150643) (by norm_num)
theorem B1622693 : Blo 354756 1622693 := bbase (se 4 (by rfl) ⟨152127, by rfl⟩ : syracuseStep 1622693 = 304255) (by norm_num)
theorem B803501 : Blo 354756 803501 := bbase (se 3 (by rfl) ⟨150656, by rfl⟩ : syracuseStep 803501 = 301313) (by norm_num)
theorem B901813 : Blo 354756 901813 := bbase (se 5 (by rfl) ⟨42272, by rfl⟩ : syracuseStep 901813 = 84545) (by norm_num)
theorem B574133 : Blo 354756 574133 := bbase (se 5 (by rfl) ⟨26912, by rfl⟩ : syracuseStep 574133 = 53825) (by norm_num)
theorem B541397 : Blo 354756 541397 := bbase (se 7 (by rfl) ⟨6344, by rfl⟩ : syracuseStep 541397 = 12689) (by norm_num)
theorem B574165 : Blo 354756 574165 := bbase (se 7 (by rfl) ⟨6728, by rfl⟩ : syracuseStep 574165 = 13457) (by norm_num)
theorem B508637 : Blo 354756 508637 := bbase (se 3 (by rfl) ⟨95369, by rfl⟩ : syracuseStep 508637 = 190739) (by norm_num)
theorem B803573 : Blo 354756 803573 := bbase (se 5 (by rfl) ⟨37667, by rfl⟩ : syracuseStep 803573 = 75335) (by norm_num)
theorem B901925 : Blo 354756 901925 := bbase (se 4 (by rfl) ⟨84555, by rfl⟩ : syracuseStep 901925 = 169111) (by norm_num)
theorem B508717 : Blo 354756 508717 := bbase (se 3 (by rfl) ⟨95384, by rfl⟩ : syracuseStep 508717 = 190769) (by norm_num)
theorem B967477 : Blo 354756 967477 := bbase (se 5 (by rfl) ⟨45350, by rfl⟩ : syracuseStep 967477 = 90701) (by norm_num)
theorem B803645 : Blo 354756 803645 := bbase (se 3 (by rfl) ⟨150683, by rfl⟩ : syracuseStep 803645 = 301367) (by norm_num)
theorem B1360709 : Blo 354756 1360709 := bbase (se 4 (by rfl) ⟨127566, by rfl⟩ : syracuseStep 1360709 = 255133) (by norm_num)
theorem B803717 : Blo 354756 803717 := bbase (se 4 (by rfl) ⟨75348, by rfl⟩ : syracuseStep 803717 = 150697) (by norm_num)
theorem B508837 : Blo 354756 508837 := bbase (se 4 (by rfl) ⟨47703, by rfl⟩ : syracuseStep 508837 = 95407) (by norm_num)
theorem B803789 : Blo 354756 803789 := bbase (se 3 (by rfl) ⟨150710, by rfl⟩ : syracuseStep 803789 = 301421) (by norm_num)
theorem B902117 : Blo 354756 902117 := bbase (se 4 (by rfl) ⟨84573, by rfl⟩ : syracuseStep 902117 = 169147) (by norm_num)
theorem B508933 : Blo 354756 508933 := bbase (se 4 (by rfl) ⟨47712, by rfl⟩ : syracuseStep 508933 = 95425) (by norm_num)
theorem B803861 : Blo 354756 803861 := bbase (se 6 (by rfl) ⟨18840, by rfl⟩ : syracuseStep 803861 = 37681) (by norm_num)
theorem B803933 : Blo 354756 803933 := bbase (se 3 (by rfl) ⟨150737, by rfl⟩ : syracuseStep 803933 = 301475) (by norm_num)
theorem B607333 : Blo 354756 607333 := bbase (se 4 (by rfl) ⟨56937, by rfl⟩ : syracuseStep 607333 = 113875) (by norm_num)
theorem B804005 : Blo 354756 804005 := bbase (se 4 (by rfl) ⟨75375, by rfl⟩ : syracuseStep 804005 = 150751) (by norm_num)
theorem B967909 : Blo 354756 967909 := bbase (se 4 (by rfl) ⟨90741, by rfl⟩ : syracuseStep 967909 = 181483) (by norm_num)
theorem B1721573 : Blo 354756 1721573 := bbase (se 4 (by rfl) ⟨161397, by rfl⟩ : syracuseStep 1721573 = 322795) (by norm_num)
theorem B804077 : Blo 354756 804077 := bbase (se 3 (by rfl) ⟨150764, by rfl⟩ : syracuseStep 804077 = 301529) (by norm_num)
theorem B2770229 : Blo 354756 2770229 := bbase (se 5 (by rfl) ⟨129854, by rfl⟩ : syracuseStep 2770229 = 259709) (by norm_num)
theorem B804149 : Blo 354756 804149 := bbase (se 5 (by rfl) ⟨37694, by rfl⟩ : syracuseStep 804149 = 75389) (by norm_num)
theorem B902461 : Blo 354756 902461 := bbase (se 3 (by rfl) ⟨169211, by rfl⟩ : syracuseStep 902461 = 338423) (by norm_num)
theorem B804221 : Blo 354756 804221 := bbase (se 3 (by rfl) ⟨150791, by rfl⟩ : syracuseStep 804221 = 301583) (by norm_num)
theorem B902573 : Blo 354756 902573 := bbase (se 3 (by rfl) ⟨169232, by rfl⟩ : syracuseStep 902573 = 338465) (by norm_num)
theorem B804293 : Blo 354756 804293 := bbase (se 4 (by rfl) ⟨75402, by rfl⟩ : syracuseStep 804293 = 150805) (by norm_num)
theorem B1197557 : Blo 354756 1197557 := bbase (se 5 (by rfl) ⟨56135, by rfl⟩ : syracuseStep 1197557 = 112271) (by norm_num)
theorem B509429 : Blo 354756 509429 := bbase (se 5 (by rfl) ⟨23879, by rfl⟩ : syracuseStep 509429 = 47759) (by norm_num)
theorem B804365 : Blo 354756 804365 := bbase (se 3 (by rfl) ⟨150818, by rfl⟩ : syracuseStep 804365 = 301637) (by norm_num)
theorem B804437 : Blo 354756 804437 := bbase (se 8 (by rfl) ⟨4713, by rfl⟩ : syracuseStep 804437 = 9427) (by norm_num)
theorem B607853 : Blo 354756 607853 := bbase (se 3 (by rfl) ⟨113972, by rfl⟩ : syracuseStep 607853 = 227945) (by norm_num)
theorem B902765 : Blo 354756 902765 := bbase (se 3 (by rfl) ⟨169268, by rfl⟩ : syracuseStep 902765 = 338537) (by norm_num)
theorem B804509 : Blo 354756 804509 := bbase (se 3 (by rfl) ⟨150845, by rfl⟩ : syracuseStep 804509 = 301691) (by norm_num)
theorem B804581 : Blo 354756 804581 := bbase (se 4 (by rfl) ⟨75429, by rfl⟩ : syracuseStep 804581 = 150859) (by norm_num)
theorem B804653 : Blo 354756 804653 := bbase (se 3 (by rfl) ⟨150872, by rfl⟩ : syracuseStep 804653 = 301745) (by norm_num)
theorem B673589 : Blo 354756 673589 := bbase (se 5 (by rfl) ⟨31574, by rfl⟩ : syracuseStep 673589 = 63149) (by norm_num)
theorem B804725 : Blo 354756 804725 := bbase (se 5 (by rfl) ⟨37721, by rfl⟩ : syracuseStep 804725 = 75443) (by norm_num)
theorem B1197989 : Blo 354756 1197989 := bbase (se 4 (by rfl) ⟨112311, by rfl⟩ : syracuseStep 1197989 = 224623) (by norm_num)
theorem B804797 : Blo 354756 804797 := bbase (se 3 (by rfl) ⟨150899, by rfl⟩ : syracuseStep 804797 = 301799) (by norm_num)
theorem B673733 : Blo 354756 673733 := bbase (se 4 (by rfl) ⟨63162, by rfl⟩ : syracuseStep 673733 = 126325) (by norm_num)
theorem B903109 : Blo 354756 903109 := bbase (se 4 (by rfl) ⟨84666, by rfl⟩ : syracuseStep 903109 = 169333) (by norm_num)
theorem B1361893 : Blo 354756 1361893 := bbase (se 4 (by rfl) ⟨127677, by rfl⟩ : syracuseStep 1361893 = 255355) (by norm_num)
theorem B804869 : Blo 354756 804869 := bbase (se 4 (by rfl) ⟨75456, by rfl⟩ : syracuseStep 804869 = 150913) (by norm_num)
theorem B608285 : Blo 354756 608285 := bbase (se 3 (by rfl) ⟨114053, by rfl⟩ : syracuseStep 608285 = 228107) (by norm_num)
theorem B509981 : Blo 354756 509981 := bbase (se 3 (by rfl) ⟨95621, by rfl⟩ : syracuseStep 509981 = 191243) (by norm_num)
theorem B3655733 : Blo 354756 3655733 := bbase (se 5 (by rfl) ⟨171362, by rfl⟩ : syracuseStep 3655733 = 342725) (by norm_num)
theorem B903221 : Blo 354756 903221 := bbase (se 5 (by rfl) ⟨42338, by rfl⟩ : syracuseStep 903221 = 84677) (by norm_num)
theorem B804941 : Blo 354756 804941 := bbase (se 3 (by rfl) ⟨150926, by rfl⟩ : syracuseStep 804941 = 301853) (by norm_num)
theorem B379009 : Blo 354756 379009 := bbase (se 2 (by rfl) ⟨142128, by rfl⟩ : syracuseStep 379009 = 284257) (by norm_num)
theorem B1099909 : Blo 354756 1099909 := bbase (se 4 (by rfl) ⟨103116, by rfl⟩ : syracuseStep 1099909 = 206233) (by norm_num)
theorem B805013 : Blo 354756 805013 := bbase (se 6 (by rfl) ⟨18867, by rfl⟩ : syracuseStep 805013 = 37735) (by norm_num)
theorem B805085 : Blo 354756 805085 := bbase (se 3 (by rfl) ⟨150953, by rfl⟩ : syracuseStep 805085 = 301907) (by norm_num)
theorem B674021 : Blo 354756 674021 := bbase (se 4 (by rfl) ⟨63189, by rfl⟩ : syracuseStep 674021 = 126379) (by norm_num)
theorem B903413 : Blo 354756 903413 := bbase (se 5 (by rfl) ⟨42347, by rfl⟩ : syracuseStep 903413 = 84695) (by norm_num)
theorem B805157 : Blo 354756 805157 := bbase (se 4 (by rfl) ⟨75483, by rfl⟩ : syracuseStep 805157 = 150967) (by norm_num)
theorem B1198421 : Blo 354756 1198421 := bbase (se 10 (by rfl) ⟨1755, by rfl⟩ : syracuseStep 1198421 = 3511) (by norm_num)
theorem B805229 : Blo 354756 805229 := bbase (se 3 (by rfl) ⟨150980, by rfl⟩ : syracuseStep 805229 = 301961) (by norm_num)
theorem B969077 : Blo 354756 969077 := bbase (se 5 (by rfl) ⟨45425, by rfl⟩ : syracuseStep 969077 = 90851) (by norm_num)
theorem B674173 : Blo 354756 674173 := bbase (se 3 (by rfl) ⟨126407, by rfl⟩ : syracuseStep 674173 = 252815) (by norm_num)
theorem B805301 : Blo 354756 805301 := bbase (se 5 (by rfl) ⟨37748, by rfl⟩ : syracuseStep 805301 = 75497) (by norm_num)
theorem B805373 : Blo 354756 805373 := bbase (se 3 (by rfl) ⟨151007, by rfl⟩ : syracuseStep 805373 = 302015) (by norm_num)
theorem B379441 : Blo 354756 379441 := bbase (se 2 (by rfl) ⟨142290, by rfl⟩ : syracuseStep 379441 = 284581) (by norm_num)
theorem B805445 : Blo 354756 805445 := bbase (se 4 (by rfl) ⟨75510, by rfl⟩ : syracuseStep 805445 = 151021) (by norm_num)
theorem B903757 : Blo 354756 903757 := bbase (se 3 (by rfl) ⟨169454, by rfl⟩ : syracuseStep 903757 = 338909) (by norm_num)
theorem B379513 : Blo 354756 379513 := bbase (se 2 (by rfl) ⟨142317, by rfl⟩ : syracuseStep 379513 = 284635) (by norm_num)
theorem B805517 : Blo 354756 805517 := bbase (se 3 (by rfl) ⟨151034, by rfl⟩ : syracuseStep 805517 = 302069) (by norm_num)
theorem B674477 : Blo 354756 674477 := bbase (se 3 (by rfl) ⟨126464, by rfl⟩ : syracuseStep 674477 = 252929) (by norm_num)
theorem B608941 : Blo 354756 608941 := bbase (se 3 (by rfl) ⟨114176, by rfl⟩ : syracuseStep 608941 = 228353) (by norm_num)
theorem B903869 : Blo 354756 903869 := bbase (se 3 (by rfl) ⟨169475, by rfl⟩ : syracuseStep 903869 = 338951) (by norm_num)
theorem B805589 : Blo 354756 805589 := bbase (se 7 (by rfl) ⟨9440, by rfl⟩ : syracuseStep 805589 = 18881) (by norm_num)
theorem B1854181 : Blo 354756 1854181 := bbase (se 4 (by rfl) ⟨173829, by rfl⟩ : syracuseStep 1854181 = 347659) (by norm_num)
theorem B1198853 : Blo 354756 1198853 := bbase (se 4 (by rfl) ⟨112392, by rfl⟩ : syracuseStep 1198853 = 224785) (by norm_num)
theorem B510733 : Blo 354756 510733 := bbase (se 3 (by rfl) ⟨95762, by rfl⟩ : syracuseStep 510733 = 191525) (by norm_num)
theorem B805661 : Blo 354756 805661 := bbase (se 3 (by rfl) ⟨151061, by rfl⟩ : syracuseStep 805661 = 302123) (by norm_num)
theorem B805733 : Blo 354756 805733 := bbase (se 4 (by rfl) ⟨75537, by rfl⟩ : syracuseStep 805733 = 151075) (by norm_num)
theorem B904061 : Blo 354756 904061 := bbase (se 3 (by rfl) ⟨169511, by rfl⟩ : syracuseStep 904061 = 339023) (by norm_num)
theorem B805805 : Blo 354756 805805 := bbase (se 3 (by rfl) ⟨151088, by rfl⟩ : syracuseStep 805805 = 302177) (by norm_num)
theorem B412609 : Blo 354756 412609 := bbase (se 2 (by rfl) ⟨154728, by rfl⟩ : syracuseStep 412609 = 309457) (by norm_num)
theorem B379885 : Blo 354756 379885 := bbase (se 3 (by rfl) ⟨71228, by rfl⟩ : syracuseStep 379885 = 142457) (by norm_num)
theorem B805877 : Blo 354756 805877 := bbase (se 5 (by rfl) ⟨37775, by rfl⟩ : syracuseStep 805877 = 75551) (by norm_num)
theorem B805949 : Blo 354756 805949 := bbase (se 3 (by rfl) ⟨151115, by rfl⟩ : syracuseStep 805949 = 302231) (by norm_num)
theorem B1723477 : Blo 354756 1723477 := bbase (se 8 (by rfl) ⟨10098, by rfl⟩ : syracuseStep 1723477 = 20197) (by norm_num)
theorem B1723493 : Blo 354756 1723493 := bbase (se 4 (by rfl) ⟨161577, by rfl⟩ : syracuseStep 1723493 = 323155) (by norm_num)
theorem B412781 : Blo 354756 412781 := bbase (se 3 (by rfl) ⟨77396, by rfl⟩ : syracuseStep 412781 = 154793) (by norm_num)
theorem B806021 : Blo 354756 806021 := bbase (se 4 (by rfl) ⟨75564, by rfl⟩ : syracuseStep 806021 = 151129) (by norm_num)
theorem B1199285 : Blo 354756 1199285 := bbase (se 5 (by rfl) ⟨56216, by rfl⟩ : syracuseStep 1199285 = 112433) (by norm_num)
theorem B806093 : Blo 354756 806093 := bbase (se 3 (by rfl) ⟨151142, by rfl⟩ : syracuseStep 806093 = 302285) (by norm_num)
theorem B904405 : Blo 354756 904405 := bbase (se 7 (by rfl) ⟨10598, by rfl⟩ : syracuseStep 904405 = 21197) (by norm_num)
theorem B642325 : Blo 354756 642325 := bbase (se 6 (by rfl) ⟨15054, by rfl⟩ : syracuseStep 642325 = 30109) (by norm_num)
theorem B806165 : Blo 354756 806165 := bbase (se 6 (by rfl) ⟨18894, by rfl⟩ : syracuseStep 806165 = 37789) (by norm_num)
theorem B904517 : Blo 354756 904517 := bbase (se 4 (by rfl) ⟨84798, by rfl⟩ : syracuseStep 904517 = 169597) (by norm_num)
theorem B544085 : Blo 354756 544085 := bbase (se 11 (by rfl) ⟨398, by rfl⟩ : syracuseStep 544085 = 797) (by norm_num)
theorem B806237 : Blo 354756 806237 := bbase (se 3 (by rfl) ⟨151169, by rfl⟩ : syracuseStep 806237 = 302339) (by norm_num)
theorem B380261 : Blo 354756 380261 := bbase (se 4 (by rfl) ⟨35649, by rfl⟩ : syracuseStep 380261 = 71299) (by norm_num)
theorem B675229 : Blo 354756 675229 := bbase (se 3 (by rfl) ⟨126605, by rfl⟩ : syracuseStep 675229 = 253211) (by norm_num)
theorem B806309 : Blo 354756 806309 := bbase (se 4 (by rfl) ⟨75591, by rfl⟩ : syracuseStep 806309 = 151183) (by norm_num)
theorem B380333 : Blo 354756 380333 := bbase (se 3 (by rfl) ⟨71312, by rfl⟩ : syracuseStep 380333 = 142625) (by norm_num)
theorem B806381 : Blo 354756 806381 := bbase (se 3 (by rfl) ⟨151196, by rfl⟩ : syracuseStep 806381 = 302393) (by norm_num)
theorem B380413 : Blo 354756 380413 := bbase (se 3 (by rfl) ⟨71327, by rfl⟩ : syracuseStep 380413 = 142655) (by norm_num)
theorem B904709 : Blo 354756 904709 := bbase (se 4 (by rfl) ⟨84816, by rfl⟩ : syracuseStep 904709 = 169633) (by norm_num)
theorem B675373 : Blo 354756 675373 := bbase (se 3 (by rfl) ⟨126632, by rfl⟩ : syracuseStep 675373 = 253265) (by norm_num)
theorem B773677 : Blo 354756 773677 := bbase (se 3 (by rfl) ⟨145064, by rfl⟩ : syracuseStep 773677 = 290129) (by norm_num)
theorem B806453 : Blo 354756 806453 := bbase (se 5 (by rfl) ⟨37802, by rfl⟩ : syracuseStep 806453 = 75605) (by norm_num)
theorem B1199717 : Blo 354756 1199717 := bbase (se 4 (by rfl) ⟨112473, by rfl⟩ : syracuseStep 1199717 = 224947) (by norm_num)
theorem B380521 : Blo 354756 380521 := bbase (se 2 (by rfl) ⟨142695, by rfl⟩ : syracuseStep 380521 = 285391) (by norm_num)
theorem B806525 : Blo 354756 806525 := bbase (se 3 (by rfl) ⟨151223, by rfl⟩ : syracuseStep 806525 = 302447) (by norm_num)
theorem B806597 : Blo 354756 806597 := bbase (se 4 (by rfl) ⟨75618, by rfl⟩ : syracuseStep 806597 = 151237) (by norm_num)
theorem B675533 : Blo 354756 675533 := bbase (se 3 (by rfl) ⟨126662, by rfl⟩ : syracuseStep 675533 = 253325) (by norm_num)
theorem B806669 : Blo 354756 806669 := bbase (se 3 (by rfl) ⟨151250, by rfl⟩ : syracuseStep 806669 = 302501) (by norm_num)
theorem B380705 : Blo 354756 380705 := bbase (se 2 (by rfl) ⟨142764, by rfl⟩ : syracuseStep 380705 = 285529) (by norm_num)
theorem B1527605 : Blo 354756 1527605 := bbase (se 5 (by rfl) ⟨71606, by rfl⟩ : syracuseStep 1527605 = 143213) (by norm_num)
theorem B806741 : Blo 354756 806741 := bbase (se 9 (by rfl) ⟨2363, by rfl⟩ : syracuseStep 806741 = 4727) (by norm_num)
theorem B675677 : Blo 354756 675677 := bbase (se 3 (by rfl) ⟨126689, by rfl⟩ : syracuseStep 675677 = 253379) (by norm_num)
theorem B905053 : Blo 354756 905053 := bbase (se 3 (by rfl) ⟨169697, by rfl⟩ : syracuseStep 905053 = 339395) (by norm_num)
theorem B2576245 : Blo 354756 2576245 := bbase (se 5 (by rfl) ⟨120761, by rfl⟩ : syracuseStep 2576245 = 241523) (by norm_num)
theorem B806813 : Blo 354756 806813 := bbase (se 3 (by rfl) ⟨151277, by rfl⟩ : syracuseStep 806813 = 302555) (by norm_num)
theorem B1822661 : Blo 354756 1822661 := bbase (se 4 (by rfl) ⟨170874, by rfl⟩ : syracuseStep 1822661 = 341749) (by norm_num)
theorem B905165 : Blo 354756 905165 := bbase (se 3 (by rfl) ⟨169718, by rfl⟩ : syracuseStep 905165 = 339437) (by norm_num)
theorem B806885 : Blo 354756 806885 := bbase (se 4 (by rfl) ⟨75645, by rfl⟩ : syracuseStep 806885 = 151291) (by norm_num)
theorem B1200149 : Blo 354756 1200149 := bbase (se 6 (by rfl) ⟨28128, by rfl⟩ : syracuseStep 1200149 = 56257) (by norm_num)
theorem B774181 : Blo 354756 774181 := bbase (se 4 (by rfl) ⟨72579, by rfl⟩ : syracuseStep 774181 = 145159) (by norm_num)
theorem B806957 : Blo 354756 806957 := bbase (se 3 (by rfl) ⟨151304, by rfl⟩ : syracuseStep 806957 = 302609) (by norm_num)
theorem B643133 : Blo 354756 643133 := bbase (se 3 (by rfl) ⟨120587, by rfl⟩ : syracuseStep 643133 = 241175) (by norm_num)
theorem B1527893 : Blo 354756 1527893 := bbase (se 8 (by rfl) ⟨8952, by rfl⟩ : syracuseStep 1527893 = 17905) (by norm_num)
theorem B807029 : Blo 354756 807029 := bbase (se 5 (by rfl) ⟨37829, by rfl⟩ : syracuseStep 807029 = 75659) (by norm_num)
theorem B675965 : Blo 354756 675965 := bbase (se 3 (by rfl) ⟨126743, by rfl⟩ : syracuseStep 675965 = 253487) (by norm_num)
theorem B905357 : Blo 354756 905357 := bbase (se 3 (by rfl) ⟨169754, by rfl⟩ : syracuseStep 905357 = 339509) (by norm_num)
theorem B774293 : Blo 354756 774293 := bbase (se 6 (by rfl) ⟨18147, by rfl⟩ : syracuseStep 774293 = 36295) (by norm_num)
theorem B807101 : Blo 354756 807101 := bbase (se 3 (by rfl) ⟨151331, by rfl⟩ : syracuseStep 807101 = 302663) (by norm_num)
theorem B807173 : Blo 354756 807173 := bbase (se 4 (by rfl) ⟨75672, by rfl⟩ : syracuseStep 807173 = 151345) (by norm_num)
theorem B676117 : Blo 354756 676117 := bbase (se 6 (by rfl) ⟨15846, by rfl⟩ : syracuseStep 676117 = 31693) (by norm_num)
theorem B1200581 : Blo 354756 1200581 := bbase (se 4 (by rfl) ⟨112554, by rfl⟩ : syracuseStep 1200581 = 225109) (by norm_num)
theorem B905701 : Blo 354756 905701 := bbase (se 4 (by rfl) ⟨84909, by rfl⟩ : syracuseStep 905701 = 169819) (by norm_num)
theorem B381457 : Blo 354756 381457 := bbase (se 2 (by rfl) ⟨143046, by rfl⟩ : syracuseStep 381457 = 286093) (by norm_num)
theorem B676421 : Blo 354756 676421 := bbase (se 4 (by rfl) ⟨63414, by rfl⟩ : syracuseStep 676421 = 126829) (by norm_num)
theorem B905813 : Blo 354756 905813 := bbase (se 8 (by rfl) ⟨5307, by rfl⟩ : syracuseStep 905813 = 10615) (by norm_num)
theorem B16536149 : Blo 354756 16536149 := bbase (se 8 (by rfl) ⟨96891, by rfl⟩ : syracuseStep 16536149 = 193783) (by norm_num)
theorem B381529 : Blo 354756 381529 := bbase (se 2 (by rfl) ⟨143073, by rfl⟩ : syracuseStep 381529 = 286147) (by norm_num)
theorem B840389 : Blo 354756 840389 := bbase (se 4 (by rfl) ⟨78786, by rfl⟩ : syracuseStep 840389 = 157573) (by norm_num)
theorem B381709 : Blo 354756 381709 := bbase (se 3 (by rfl) ⟨71570, by rfl⟩ : syracuseStep 381709 = 143141) (by norm_num)
theorem B906005 : Blo 354756 906005 := bbase (se 6 (by rfl) ⟨21234, by rfl⟩ : syracuseStep 906005 = 42469) (by norm_num)
theorem B1528645 : Blo 354756 1528645 := bbase (se 4 (by rfl) ⟨143310, by rfl⟩ : syracuseStep 1528645 = 286621) (by norm_num)
theorem B1201013 : Blo 354756 1201013 := bbase (se 5 (by rfl) ⟨56297, by rfl⟩ : syracuseStep 1201013 = 112595) (by norm_num)
theorem B906349 : Blo 354756 906349 := bbase (se 3 (by rfl) ⟨169940, by rfl⟩ : syracuseStep 906349 = 339881) (by norm_num)
theorem B382153 : Blo 354756 382153 := bbase (se 2 (by rfl) ⟨143307, by rfl⟩ : syracuseStep 382153 = 286615) (by norm_num)
theorem B906461 : Blo 354756 906461 := bbase (se 3 (by rfl) ⟨169961, by rfl⟩ : syracuseStep 906461 = 339923) (by norm_num)
theorem B1201445 : Blo 354756 1201445 := bbase (se 4 (by rfl) ⟨112635, by rfl⟩ : syracuseStep 1201445 = 225271) (by norm_num)
theorem B677173 : Blo 354756 677173 := bbase (se 5 (by rfl) ⟨31742, by rfl⟩ : syracuseStep 677173 = 63485) (by norm_num)
theorem B382277 : Blo 354756 382277 := bbase (se 4 (by rfl) ⟨35838, by rfl⟩ : syracuseStep 382277 = 71677) (by norm_num)
theorem B4576661 : Blo 354756 4576661 := bbase (se 6 (by rfl) ⟨107265, by rfl⟩ : syracuseStep 4576661 = 214531) (by norm_num)
theorem B906653 : Blo 354756 906653 := bbase (se 3 (by rfl) ⟨169997, by rfl⟩ : syracuseStep 906653 = 339995) (by norm_num)
theorem B677317 : Blo 354756 677317 := bbase (se 4 (by rfl) ⟨63498, by rfl⟩ : syracuseStep 677317 = 126997) (by norm_num)
theorem B1529381 : Blo 354756 1529381 := bbase (se 4 (by rfl) ⟨143379, by rfl⟩ : syracuseStep 1529381 = 286759) (by norm_num)
theorem B382529 : Blo 354756 382529 := bbase (se 2 (by rfl) ⟨143448, by rfl⟩ : syracuseStep 382529 = 286897) (by norm_num)
theorem B2020949 : Blo 354756 2020949 := bbase (se 8 (by rfl) ⟨11841, by rfl⟩ : syracuseStep 2020949 = 23683) (by norm_num)
theorem B677477 : Blo 354756 677477 := bbase (se 4 (by rfl) ⟨63513, by rfl⟩ : syracuseStep 677477 = 127027) (by norm_num)
theorem B1201877 : Blo 354756 1201877 := bbase (se 7 (by rfl) ⟨14084, by rfl⟩ : syracuseStep 1201877 = 28169) (by norm_num)
theorem B677621 : Blo 354756 677621 := bbase (se 5 (by rfl) ⟨31763, by rfl⟩ : syracuseStep 677621 = 63527) (by norm_num)
theorem B906997 : Blo 354756 906997 := bbase (se 5 (by rfl) ⟨42515, by rfl⟩ : syracuseStep 906997 = 85031) (by norm_num)
theorem B644869 : Blo 354756 644869 := bbase (se 4 (by rfl) ⟨60456, by rfl⟩ : syracuseStep 644869 = 120913) (by norm_num)
theorem B13850453 : Blo 354756 13850453 := bbase (se 9 (by rfl) ⟨40577, by rfl⟩ : syracuseStep 13850453 = 81155) (by norm_num)
theorem B907109 : Blo 354756 907109 := bbase (se 4 (by rfl) ⟨85041, by rfl⟩ : syracuseStep 907109 = 170083) (by norm_num)
theorem B645013 : Blo 354756 645013 := bbase (se 6 (by rfl) ⟨15117, by rfl⟩ : syracuseStep 645013 = 30235) (by norm_num)
theorem B382973 : Blo 354756 382973 := bbase (se 3 (by rfl) ⟨71807, by rfl⟩ : syracuseStep 382973 = 143615) (by norm_num)
theorem B677909 : Blo 354756 677909 := bbase (se 6 (by rfl) ⟨15888, by rfl⟩ : syracuseStep 677909 = 31777) (by norm_num)
theorem B907301 : Blo 354756 907301 := bbase (se 4 (by rfl) ⟨85059, by rfl⟩ : syracuseStep 907301 = 170119) (by norm_num)
theorem B1202309 : Blo 354756 1202309 := bbase (se 4 (by rfl) ⟨112716, by rfl⟩ : syracuseStep 1202309 = 225433) (by norm_num)
theorem B678061 : Blo 354756 678061 := bbase (se 3 (by rfl) ⟨127136, by rfl⟩ : syracuseStep 678061 = 254273) (by norm_num)
theorem B481501 : Blo 354756 481501 := bbase (se 3 (by rfl) ⟨90281, by rfl⟩ : syracuseStep 481501 = 180563) (by norm_num)
theorem B6838613 : Blo 354756 6838613 := bbase (se 10 (by rfl) ⟨10017, by rfl⟩ : syracuseStep 6838613 = 20035) (by norm_num)
theorem B907645 : Blo 354756 907645 := bbase (se 3 (by rfl) ⟨170183, by rfl⟩ : syracuseStep 907645 = 340367) (by norm_num)
theorem B481717 : Blo 354756 481717 := bbase (se 5 (by rfl) ⟨22580, by rfl⟩ : syracuseStep 481717 = 45161) (by norm_num)
theorem B678365 : Blo 354756 678365 := bbase (se 3 (by rfl) ⟨127193, by rfl⟩ : syracuseStep 678365 = 254387) (by norm_num)
theorem B448993 : Blo 354756 448993 := bbase (se 2 (by rfl) ⟨168372, by rfl⟩ : syracuseStep 448993 = 336745) (by norm_num)
theorem B907757 : Blo 354756 907757 := bbase (se 3 (by rfl) ⟨170204, by rfl⟩ : syracuseStep 907757 = 340409) (by norm_num)
theorem B1202741 : Blo 354756 1202741 := bbase (se 5 (by rfl) ⟨56378, by rfl⟩ : syracuseStep 1202741 = 112757) (by norm_num)
theorem B449165 : Blo 354756 449165 := bbase (se 3 (by rfl) ⟨84218, by rfl⟩ : syracuseStep 449165 = 168437) (by norm_num)
theorem B907949 : Blo 354756 907949 := bbase (se 3 (by rfl) ⟨170240, by rfl⟩ : syracuseStep 907949 = 340481) (by norm_num)
theorem B449221 : Blo 354756 449221 := bbase (se 4 (by rfl) ⟨42114, by rfl⟩ : syracuseStep 449221 = 84229) (by norm_num)
theorem B613109 : Blo 354756 613109 := bbase (se 5 (by rfl) ⟨28739, by rfl⟩ : syracuseStep 613109 = 57479) (by norm_num)
theorem B449317 : Blo 354756 449317 := bbase (se 4 (by rfl) ⟨42123, by rfl⟩ : syracuseStep 449317 = 84247) (by norm_num)
theorem B645965 : Blo 354756 645965 := bbase (se 3 (by rfl) ⟨121118, by rfl⟩ : syracuseStep 645965 = 242237) (by norm_num)
theorem B809813 : Blo 354756 809813 := bbase (se 9 (by rfl) ⟨2372, by rfl⟩ : syracuseStep 809813 = 4745) (by norm_num)
theorem B2710421 : Blo 354756 2710421 := bbase (se 6 (by rfl) ⟨63525, by rfl⟩ : syracuseStep 2710421 = 127051) (by norm_num)
theorem B646037 : Blo 354756 646037 := bbase (se 6 (by rfl) ⟨15141, by rfl⟩ : syracuseStep 646037 = 30283) (by norm_num)
theorem B449489 : Blo 354756 449489 := bbase (se 2 (by rfl) ⟨168558, by rfl⟩ : syracuseStep 449489 = 337117) (by norm_num)
theorem B1203173 : Blo 354756 1203173 := bbase (se 4 (by rfl) ⟨112797, by rfl⟩ : syracuseStep 1203173 = 225595) (by norm_num)
theorem B449545 : Blo 354756 449545 := bbase (se 2 (by rfl) ⟨168579, by rfl⟩ : syracuseStep 449545 = 337159) (by norm_num)
theorem B449641 : Blo 354756 449641 := bbase (se 2 (by rfl) ⟨168615, by rfl⟩ : syracuseStep 449641 = 337231) (by norm_num)
theorem B679117 : Blo 354756 679117 := bbase (se 3 (by rfl) ⟨127334, by rfl⟩ : syracuseStep 679117 = 254669) (by norm_num)
theorem B449813 : Blo 354756 449813 := bbase (se 6 (by rfl) ⟨10542, by rfl⟩ : syracuseStep 449813 = 21085) (by norm_num)
theorem B449869 : Blo 354756 449869 := bbase (se 3 (by rfl) ⟨84350, by rfl⟩ : syracuseStep 449869 = 168701) (by norm_num)
theorem B679261 : Blo 354756 679261 := bbase (se 3 (by rfl) ⟨127361, by rfl⟩ : syracuseStep 679261 = 254723) (by norm_num)
theorem B482701 : Blo 354756 482701 := bbase (se 3 (by rfl) ⟨90506, by rfl⟩ : syracuseStep 482701 = 181013) (by norm_num)
theorem B1203605 : Blo 354756 1203605 := bbase (se 6 (by rfl) ⟨28209, by rfl⟩ : syracuseStep 1203605 = 56419) (by norm_num)
theorem B449965 : Blo 354756 449965 := bbase (se 3 (by rfl) ⟨84368, by rfl⟩ : syracuseStep 449965 = 168737) (by norm_num)
theorem B679421 : Blo 354756 679421 := bbase (se 3 (by rfl) ⟨127391, by rfl⟩ : syracuseStep 679421 = 254783) (by norm_num)
theorem B450137 : Blo 354756 450137 := bbase (se 2 (by rfl) ⟨168801, by rfl⟩ : syracuseStep 450137 = 337603) (by norm_num)
theorem B679565 : Blo 354756 679565 := bbase (se 3 (by rfl) ⟨127418, by rfl⟩ : syracuseStep 679565 = 254837) (by norm_num)
theorem B450193 : Blo 354756 450193 := bbase (se 2 (by rfl) ⟨168822, by rfl⟩ : syracuseStep 450193 = 337645) (by norm_num)
theorem B5758613 : Blo 354756 5758613 := bbase (se 6 (by rfl) ⟨134967, by rfl⟩ : syracuseStep 5758613 = 269935) (by norm_num)
theorem B450289 : Blo 354756 450289 := bbase (se 2 (by rfl) ⟨168858, by rfl⟩ : syracuseStep 450289 = 337717) (by norm_num)
theorem B2023157 : Blo 354756 2023157 := bbase (se 5 (by rfl) ⟨94835, by rfl⟩ : syracuseStep 2023157 = 189671) (by norm_num)
theorem B2285333 : Blo 354756 2285333 := bbase (se 6 (by rfl) ⟨53562, by rfl⟩ : syracuseStep 2285333 = 107125) (by norm_num)
theorem B1204037 : Blo 354756 1204037 := bbase (se 4 (by rfl) ⟨112878, by rfl⟩ : syracuseStep 1204037 = 225757) (by norm_num)
theorem B450461 : Blo 354756 450461 := bbase (se 3 (by rfl) ⟨84461, by rfl⟩ : syracuseStep 450461 = 168923) (by norm_num)
theorem B679853 : Blo 354756 679853 := bbase (se 3 (by rfl) ⟨127472, by rfl⟩ : syracuseStep 679853 = 254945) (by norm_num)
theorem B450517 : Blo 354756 450517 := bbase (se 7 (by rfl) ⟨5279, by rfl⟩ : syracuseStep 450517 = 10559) (by norm_num)
theorem B810973 : Blo 354756 810973 := bbase (se 3 (by rfl) ⟨152057, by rfl⟩ : syracuseStep 810973 = 304115) (by norm_num)
theorem B1138693 : Blo 354756 1138693 := bbase (se 4 (by rfl) ⟨106752, by rfl⟩ : syracuseStep 1138693 = 213505) (by norm_num)
theorem B483349 : Blo 354756 483349 := bbase (se 6 (by rfl) ⟨11328, by rfl⟩ : syracuseStep 483349 = 22657) (by norm_num)
theorem B450613 : Blo 354756 450613 := bbase (se 5 (by rfl) ⟨21122, by rfl⟩ : syracuseStep 450613 = 42245) (by norm_num)
theorem B680005 : Blo 354756 680005 := bbase (se 4 (by rfl) ⟨63750, by rfl⟩ : syracuseStep 680005 = 127501) (by norm_num)
theorem B1368197 : Blo 354756 1368197 := bbase (se 4 (by rfl) ⟨128268, by rfl⟩ : syracuseStep 1368197 = 256537) (by norm_num)
theorem B450785 : Blo 354756 450785 := bbase (se 2 (by rfl) ⟨169044, by rfl⟩ : syracuseStep 450785 = 338089) (by norm_num)
theorem B1204469 : Blo 354756 1204469 := bbase (se 5 (by rfl) ⟨56459, by rfl⟩ : syracuseStep 1204469 = 112919) (by norm_num)
theorem B1138949 : Blo 354756 1138949 := bbase (se 4 (by rfl) ⟨106776, by rfl⟩ : syracuseStep 1138949 = 213553) (by norm_num)
theorem B450841 : Blo 354756 450841 := bbase (se 2 (by rfl) ⟨169065, by rfl⟩ : syracuseStep 450841 = 338131) (by norm_num)
theorem B680309 : Blo 354756 680309 := bbase (se 5 (by rfl) ⟨31889, by rfl⟩ : syracuseStep 680309 = 63779) (by norm_num)
theorem B450937 : Blo 354756 450937 := bbase (se 2 (by rfl) ⟨169101, by rfl⟩ : syracuseStep 450937 = 338203) (by norm_num)
theorem B451109 : Blo 354756 451109 := bbase (se 4 (by rfl) ⟨42291, by rfl⟩ : syracuseStep 451109 = 84583) (by norm_num)
theorem B811565 : Blo 354756 811565 := bbase (se 3 (by rfl) ⟨152168, by rfl⟩ : syracuseStep 811565 = 304337) (by norm_num)
theorem B451165 : Blo 354756 451165 := bbase (se 3 (by rfl) ⟨84593, by rfl⟩ : syracuseStep 451165 = 169187) (by norm_num)
theorem B516709 : Blo 354756 516709 := bbase (se 4 (by rfl) ⟨48441, by rfl⟩ : syracuseStep 516709 = 96883) (by norm_num)
theorem B1204901 : Blo 354756 1204901 := bbase (se 4 (by rfl) ⟨112959, by rfl⟩ : syracuseStep 1204901 = 225919) (by norm_num)
theorem B451261 : Blo 354756 451261 := bbase (se 3 (by rfl) ⟨84611, by rfl⟩ : syracuseStep 451261 = 169223) (by norm_num)
theorem B451433 : Blo 354756 451433 := bbase (se 2 (by rfl) ⟨169287, by rfl⟩ : syracuseStep 451433 = 338575) (by norm_num)
theorem B451489 : Blo 354756 451489 := bbase (se 2 (by rfl) ⟨169308, by rfl⟩ : syracuseStep 451489 = 338617) (by norm_num)
theorem B517045 : Blo 354756 517045 := bbase (se 5 (by rfl) ⟨24236, by rfl⟩ : syracuseStep 517045 = 48473) (by norm_num)
theorem B451585 : Blo 354756 451585 := bbase (se 2 (by rfl) ⟨169344, by rfl⟩ : syracuseStep 451585 = 338689) (by norm_num)
theorem B386077 : Blo 354756 386077 := bbase (se 3 (by rfl) ⟨72389, by rfl⟩ : syracuseStep 386077 = 144779) (by norm_num)
theorem B1205333 : Blo 354756 1205333 := bbase (se 8 (by rfl) ⟨7062, by rfl⟩ : syracuseStep 1205333 = 14125) (by norm_num)
theorem B681061 : Blo 354756 681061 := bbase (se 4 (by rfl) ⟨63849, by rfl⟩ : syracuseStep 681061 = 127699) (by norm_num)
theorem B451757 : Blo 354756 451757 := bbase (se 3 (by rfl) ⟨84704, by rfl⟩ : syracuseStep 451757 = 169409) (by norm_num)
theorem B451813 : Blo 354756 451813 := bbase (se 4 (by rfl) ⟨42357, by rfl⟩ : syracuseStep 451813 = 84715) (by norm_num)
theorem B451909 : Blo 354756 451909 := bbase (se 4 (by rfl) ⟨42366, by rfl⟩ : syracuseStep 451909 = 84733) (by norm_num)
theorem B386537 : Blo 354756 386537 := bbase (se 2 (by rfl) ⟨144951, by rfl⟩ : syracuseStep 386537 = 289903) (by norm_num)
theorem B452081 : Blo 354756 452081 := bbase (se 2 (by rfl) ⟨169530, by rfl⟩ : syracuseStep 452081 = 339061) (by norm_num)
theorem B1205765 : Blo 354756 1205765 := bbase (se 4 (by rfl) ⟨113040, by rfl⟩ : syracuseStep 1205765 = 226081) (by norm_num)
theorem B452137 : Blo 354756 452137 := bbase (se 2 (by rfl) ⟨169551, by rfl⟩ : syracuseStep 452137 = 339103) (by norm_num)
theorem B3434069 : Blo 354756 3434069 := bbase (se 8 (by rfl) ⟨20121, by rfl⟩ : syracuseStep 3434069 = 40243) (by norm_num)
theorem B452233 : Blo 354756 452233 := bbase (se 2 (by rfl) ⟨169587, by rfl⟩ : syracuseStep 452233 = 339175) (by norm_num)
theorem B1828645 : Blo 354756 1828645 := bbase (se 4 (by rfl) ⟨171435, by rfl⟩ : syracuseStep 1828645 = 342871) (by norm_num)
theorem B452405 : Blo 354756 452405 := bbase (se 5 (by rfl) ⟨21206, by rfl⟩ : syracuseStep 452405 = 42413) (by norm_num)
theorem B452461 : Blo 354756 452461 := bbase (se 3 (by rfl) ⟨84836, by rfl⟩ : syracuseStep 452461 = 169673) (by norm_num)
theorem B1206197 : Blo 354756 1206197 := bbase (se 5 (by rfl) ⟨56540, by rfl⟩ : syracuseStep 1206197 = 113081) (by norm_num)
theorem B452557 : Blo 354756 452557 := bbase (se 3 (by rfl) ⟨84854, by rfl⟩ : syracuseStep 452557 = 169709) (by norm_num)
theorem B452729 : Blo 354756 452729 := bbase (se 2 (by rfl) ⟨169773, by rfl⟩ : syracuseStep 452729 = 339547) (by norm_num)
theorem B911533 : Blo 354756 911533 := bbase (se 3 (by rfl) ⟨170912, by rfl⟩ : syracuseStep 911533 = 341825) (by norm_num)
theorem B452785 : Blo 354756 452785 := bbase (se 2 (by rfl) ⟨169794, by rfl⟩ : syracuseStep 452785 = 339589) (by norm_num)
theorem B452881 : Blo 354756 452881 := bbase (se 2 (by rfl) ⟨169830, by rfl⟩ : syracuseStep 452881 = 339661) (by norm_num)
theorem B1206629 : Blo 354756 1206629 := bbase (se 4 (by rfl) ⟨113121, by rfl⟩ : syracuseStep 1206629 = 226243) (by norm_num)
theorem B453053 : Blo 354756 453053 := bbase (se 3 (by rfl) ⟨84947, by rfl⟩ : syracuseStep 453053 = 169895) (by norm_num)
theorem B453109 : Blo 354756 453109 := bbase (se 5 (by rfl) ⟨21239, by rfl⟩ : syracuseStep 453109 = 42479) (by norm_num)
theorem B453205 : Blo 354756 453205 := bbase (se 8 (by rfl) ⟨2655, by rfl⟩ : syracuseStep 453205 = 5311) (by norm_num)
theorem B1796741 : Blo 354756 1796741 := bbase (se 4 (by rfl) ⟨168444, by rfl⟩ : syracuseStep 1796741 = 336889) (by norm_num)
theorem B453377 : Blo 354756 453377 := bbase (se 2 (by rfl) ⟨170016, by rfl⟩ : syracuseStep 453377 = 340033) (by norm_num)
theorem B1207061 : Blo 354756 1207061 := bbase (se 6 (by rfl) ⟨28290, by rfl⟩ : syracuseStep 1207061 = 56581) (by norm_num)
theorem B1010485 : Blo 354756 1010485 := bbase (se 5 (by rfl) ⟨47366, by rfl⟩ : syracuseStep 1010485 = 94733) (by norm_num)
theorem B453433 : Blo 354756 453433 := bbase (se 2 (by rfl) ⟨170037, by rfl⟩ : syracuseStep 453433 = 340075) (by norm_num)
theorem B453529 : Blo 354756 453529 := bbase (se 2 (by rfl) ⟨170073, by rfl⟩ : syracuseStep 453529 = 340147) (by norm_num)
theorem B1141717 : Blo 354756 1141717 := bbase (se 7 (by rfl) ⟨13379, by rfl⟩ : syracuseStep 1141717 = 26759) (by norm_num)
theorem B683005 : Blo 354756 683005 := bbase (se 3 (by rfl) ⟨128063, by rfl⟩ : syracuseStep 683005 = 256127) (by norm_num)
theorem B3894293 : Blo 354756 3894293 := bbase (se 6 (by rfl) ⟨91272, by rfl⟩ : syracuseStep 3894293 = 182545) (by norm_num)
theorem B453701 : Blo 354756 453701 := bbase (se 4 (by rfl) ⟨42534, by rfl⟩ : syracuseStep 453701 = 85069) (by norm_num)
theorem B453757 : Blo 354756 453757 := bbase (se 3 (by rfl) ⟨85079, by rfl⟩ : syracuseStep 453757 = 170159) (by norm_num)
theorem B1207493 : Blo 354756 1207493 := bbase (se 4 (by rfl) ⟨113202, by rfl⟩ : syracuseStep 1207493 = 226405) (by norm_num)
theorem B453853 : Blo 354756 453853 := bbase (se 3 (by rfl) ⟨85097, by rfl⟩ : syracuseStep 453853 = 170195) (by norm_num)
theorem B3075317 : Blo 354756 3075317 := bbase (se 5 (by rfl) ⟨144155, by rfl⟩ : syracuseStep 3075317 = 288311) (by norm_num)
theorem B3665173 : Blo 354756 3665173 := bbase (se 6 (by rfl) ⟨85902, by rfl⟩ : syracuseStep 3665173 = 171805) (by norm_num)
theorem B1633637 : Blo 354756 1633637 := bbase (se 4 (by rfl) ⟨153153, by rfl⟩ : syracuseStep 1633637 = 306307) (by norm_num)
theorem B454025 : Blo 354756 454025 := bbase (se 2 (by rfl) ⟨170259, by rfl⟩ : syracuseStep 454025 = 340519) (by norm_num)
theorem B1207925 : Blo 354756 1207925 := bbase (se 5 (by rfl) ⟨56621, by rfl⟩ : syracuseStep 1207925 = 113243) (by norm_num)
theorem B913085 : Blo 354756 913085 := bbase (se 3 (by rfl) ⟨171203, by rfl⟩ : syracuseStep 913085 = 342407) (by norm_num)
theorem B1798037 : Blo 354756 1798037 := bbase (se 6 (by rfl) ⟨42141, by rfl⟩ : syracuseStep 1798037 = 84283) (by norm_num)
theorem B913301 : Blo 354756 913301 := bbase (se 6 (by rfl) ⟨21405, by rfl⟩ : syracuseStep 913301 = 42811) (by norm_num)
theorem B1208357 : Blo 354756 1208357 := bbase (se 4 (by rfl) ⟨113283, by rfl⟩ : syracuseStep 1208357 = 226567) (by norm_num)
theorem B1831157 : Blo 354756 1831157 := bbase (se 5 (by rfl) ⟨85835, by rfl⟩ : syracuseStep 1831157 = 171671) (by norm_num)
theorem B1011989 : Blo 354756 1011989 := bbase (se 6 (by rfl) ⟨23718, by rfl⟩ : syracuseStep 1011989 = 47437) (by norm_num)
theorem B389485 : Blo 354756 389485 := bbase (se 3 (by rfl) ⟨73028, by rfl⟩ : syracuseStep 389485 = 146057) (by norm_num)
theorem B1208789 : Blo 354756 1208789 := bbase (se 7 (by rfl) ⟨14165, by rfl⟩ : syracuseStep 1208789 = 28331) (by norm_num)
theorem B1536677 : Blo 354756 1536677 := bbase (se 4 (by rfl) ⟨144063, by rfl⟩ : syracuseStep 1536677 = 288127) (by norm_num)
theorem B455557 : Blo 354756 455557 := bbase (se 4 (by rfl) ⟨42708, by rfl⟩ : syracuseStep 455557 = 85417) (by norm_num)
theorem B1209221 : Blo 354756 1209221 := bbase (se 4 (by rfl) ⟨113364, by rfl⟩ : syracuseStep 1209221 = 226729) (by norm_num)
theorem B1799333 : Blo 354756 1799333 := bbase (se 4 (by rfl) ⟨168687, by rfl⟩ : syracuseStep 1799333 = 337375) (by norm_num)
theorem B619805 : Blo 354756 619805 := bbase (se 3 (by rfl) ⟨116213, by rfl⟩ : syracuseStep 619805 = 232427) (by norm_num)
theorem B1209653 : Blo 354756 1209653 := bbase (se 5 (by rfl) ⟨56702, by rfl⟩ : syracuseStep 1209653 = 113405) (by norm_num)
theorem B521677 : Blo 354756 521677 := bbase (se 3 (by rfl) ⟨97814, by rfl⟩ : syracuseStep 521677 = 195629) (by norm_num)
theorem B685621 : Blo 354756 685621 := bbase (se 5 (by rfl) ⟨32138, by rfl⟩ : syracuseStep 685621 = 64277) (by norm_num)
theorem B489125 : Blo 354756 489125 := bbase (se 4 (by rfl) ⟨45855, by rfl⟩ : syracuseStep 489125 = 91711) (by norm_num)
theorem B1210085 : Blo 354756 1210085 := bbase (se 4 (by rfl) ⟨113445, by rfl⟩ : syracuseStep 1210085 = 226891) (by norm_num)
theorem B456445 : Blo 354756 456445 := bbase (se 3 (by rfl) ⟨85583, by rfl⟩ : syracuseStep 456445 = 171167) (by norm_num)
theorem B685837 : Blo 354756 685837 := bbase (se 3 (by rfl) ⟨128594, by rfl⟩ : syracuseStep 685837 = 257189) (by norm_num)
theorem B1013573 : Blo 354756 1013573 := bbase (se 4 (by rfl) ⟨95022, by rfl⟩ : syracuseStep 1013573 = 190045) (by norm_num)
theorem B3045397 : Blo 354756 3045397 := bbase (se 6 (by rfl) ⟨71376, by rfl⟩ : syracuseStep 3045397 = 142753) (by norm_num)
theorem B456833 : Blo 354756 456833 := bbase (se 2 (by rfl) ⟨171312, by rfl⟩ : syracuseStep 456833 = 342625) (by norm_num)
theorem B1210517 : Blo 354756 1210517 := bbase (se 6 (by rfl) ⟨28371, by rfl⟩ : syracuseStep 1210517 = 56743) (by norm_num)
theorem B1800629 : Blo 354756 1800629 := bbase (se 5 (by rfl) ⟨84404, by rfl⟩ : syracuseStep 1800629 = 168809) (by norm_num)
theorem B1014245 : Blo 354756 1014245 := bbase (se 4 (by rfl) ⟨95085, by rfl⟩ : syracuseStep 1014245 = 190171) (by norm_num)
theorem B2718197 : Blo 354756 2718197 := bbase (se 5 (by rfl) ⟨127415, by rfl⟩ : syracuseStep 2718197 = 254831) (by norm_num)
theorem B1243669 : Blo 354756 1243669 := bbase (se 6 (by rfl) ⟨29148, by rfl⟩ : syracuseStep 1243669 = 58297) (by norm_num)
theorem B457553 : Blo 354756 457553 := bbase (se 2 (by rfl) ⟨171582, by rfl⟩ : syracuseStep 457553 = 343165) (by norm_num)
theorem B1014677 : Blo 354756 1014677 := bbase (se 6 (by rfl) ⟨23781, by rfl⟩ : syracuseStep 1014677 = 47563) (by norm_num)
theorem B687037 : Blo 354756 687037 := bbase (se 3 (by rfl) ⟨128819, by rfl⟩ : syracuseStep 687037 = 257639) (by norm_num)
theorem B457861 : Blo 354756 457861 := bbase (se 4 (by rfl) ⟨42924, by rfl⟩ : syracuseStep 457861 = 85849) (by norm_num)
theorem B687421 : Blo 354756 687421 := bbase (se 3 (by rfl) ⟨128891, by rfl⟩ : syracuseStep 687421 = 257783) (by norm_num)
theorem B458065 : Blo 354756 458065 := bbase (se 2 (by rfl) ⟨171774, by rfl⟩ : syracuseStep 458065 = 343549) (by norm_num)
theorem B1375829 : Blo 354756 1375829 := bbase (se 8 (by rfl) ⟨8061, by rfl⟩ : syracuseStep 1375829 = 16123) (by norm_num)
theorem B1015429 : Blo 354756 1015429 := bbase (se 4 (by rfl) ⟨95196, by rfl⟩ : syracuseStep 1015429 = 190393) (by norm_num)
theorem B1801925 : Blo 354756 1801925 := bbase (se 4 (by rfl) ⟨168930, by rfl⟩ : syracuseStep 1801925 = 337861) (by norm_num)
theorem B3047381 : Blo 354756 3047381 := bbase (se 7 (by rfl) ⟨35711, by rfl⟩ : syracuseStep 3047381 = 71423) (by norm_num)
theorem B1146869 : Blo 354756 1146869 := bbase (se 5 (by rfl) ⟨53759, by rfl⟩ : syracuseStep 1146869 = 107519) (by norm_num)
theorem B4128965 : Blo 354756 4128965 := bstep (se 4 (by rfl) ⟨387090, by rfl⟩ : syracuseStep 4128965 = 774181) B774181
theorem B1802573 : Blo 354756 1802573 := bstep (se 3 (by rfl) ⟨337982, by rfl⟩ : syracuseStep 1802573 = 675965) B675965
theorem B2064781 : Blo 354756 2064781 := bstep (se 3 (by rfl) ⟨387146, by rfl⟩ : syracuseStep 2064781 = 774293) B774293
theorem B2720141 : Blo 354756 2720141 := bstep (se 3 (by rfl) ⟨510026, by rfl⟩ : syracuseStep 2720141 = 1020053) B1020053
theorem B1081795 : Blo 354756 1081795 := bstep (se 1 (by rfl) ⟨811346, by rfl⟩ : syracuseStep 1081795 = 1622693) B1622693
theorem B360931 : Blo 354756 360931 := bstep (se 1 (by rfl) ⟨270698, by rfl⟩ : syracuseStep 360931 = 541397) B541397
theorem B1180145 : Blo 354756 1180145 := bstep (se 2 (by rfl) ⟨442554, by rfl⟩ : syracuseStep 1180145 = 885109) B885109
theorem B2294405 : Blo 354756 2294405 := bstep (se 4 (by rfl) ⟨215100, by rfl⟩ : syracuseStep 2294405 = 430201) B430201
theorem B1147715 : Blo 354756 1147715 := bstep (se 1 (by rfl) ⟨860786, by rfl⟩ : syracuseStep 1147715 = 1721573) B1721573
theorem B1016945 : Blo 354756 1016945 := bstep (se 2 (by rfl) ⟨381354, by rfl⟩ : syracuseStep 1016945 = 762709) B762709
theorem B689393 : Blo 354756 689393 := bstep (se 2 (by rfl) ⟨258522, by rfl⟩ : syracuseStep 689393 = 517045) B517045
theorem B1017137 : Blo 354756 1017137 := bstep (se 2 (by rfl) ⟨381426, by rfl⟩ : syracuseStep 1017137 = 762853) B762853
theorem B9733517 : Blo 354756 9733517 := bstep (se 3 (by rfl) ⟨1825034, by rfl⟩ : syracuseStep 9733517 = 3650069) B3650069
theorem B722819 : Blo 354756 722819 := bstep (se 1 (by rfl) ⟨542114, by rfl⟩ : syracuseStep 722819 = 1084229) B1084229
theorem B1148995 : Blo 354756 1148995 := bstep (se 1 (by rfl) ⟨861746, by rfl⟩ : syracuseStep 1148995 = 1723493) B1723493
theorem B624721 : Blo 354756 624721 := bstep (se 2 (by rfl) ⟨234270, by rfl⟩ : syracuseStep 624721 = 468541) B468541
theorem B362723 : Blo 354756 362723 := bstep (se 1 (by rfl) ⟨272042, by rfl⟩ : syracuseStep 362723 = 544085) B544085
theorem B1018129 : Blo 354756 1018129 := bstep (se 2 (by rfl) ⟨381798, by rfl⟩ : syracuseStep 1018129 = 763597) B763597
theorem B1018403 : Blo 354756 1018403 := bstep (se 1 (by rfl) ⟨763802, by rfl⟩ : syracuseStep 1018403 = 1527605) B1527605
theorem B1215107 : Blo 354756 1215107 := bstep (se 1 (by rfl) ⟨911330, by rfl⟩ : syracuseStep 1215107 = 1822661) B1822661
theorem B428755 : Blo 354756 428755 := bstep (se 1 (by rfl) ⟨321566, by rfl⟩ : syracuseStep 428755 = 643133) B643133
theorem B1018595 : Blo 354756 1018595 := bstep (se 1 (by rfl) ⟨763946, by rfl⟩ : syracuseStep 1018595 = 1527893) B1527893
theorem B1215377 : Blo 354756 1215377 := bstep (se 2 (by rfl) ⟨455766, by rfl⟩ : syracuseStep 1215377 = 911533) B911533
theorem B2034821 : Blo 354756 2034821 := bstep (se 4 (by rfl) ⟨190764, by rfl⟩ : syracuseStep 2034821 = 381529) B381529
theorem B1805489 : Blo 354756 1805489 := bstep (se 2 (by rfl) ⟨677058, by rfl⟩ : syracuseStep 1805489 = 1354117) B1354117
theorem B2755781 : Blo 354756 2755781 := bstep (se 4 (by rfl) ⟨258354, by rfl⟩ : syracuseStep 2755781 = 516709) B516709
theorem B2723057 : Blo 354756 2723057 := bstep (se 2 (by rfl) ⟨1021146, by rfl⟩ : syracuseStep 2723057 = 2042293) B2042293
theorem B4656565 : Blo 354756 4656565 := bstep (se 5 (by rfl) ⟨218276, by rfl⟩ : syracuseStep 4656565 = 436553) B436553
theorem B1019405 : Blo 354756 1019405 := bstep (se 3 (by rfl) ⟨191138, by rfl⟩ : syracuseStep 1019405 = 382277) B382277
theorem B3247685 : Blo 354756 3247685 := bstep (se 4 (by rfl) ⟨304470, by rfl⟩ : syracuseStep 3247685 = 608941) B608941
theorem B1085005 : Blo 354756 1085005 := bstep (se 3 (by rfl) ⟨203438, by rfl⟩ : syracuseStep 1085005 = 406877) B406877
theorem B2035277 : Blo 354756 2035277 := bstep (se 3 (by rfl) ⟨381614, by rfl⟩ : syracuseStep 2035277 = 763229) B763229
theorem B3051107 : Blo 354756 3051107 := bstep (se 1 (by rfl) ⟨2288330, by rfl⟩ : syracuseStep 3051107 = 4576661) B4576661
theorem B1445539 : Blo 354756 1445539 := bstep (se 1 (by rfl) ⟨1084154, by rfl⟩ : syracuseStep 1445539 = 2168309) B2168309
theorem B1019587 : Blo 354756 1019587 := bstep (se 1 (by rfl) ⟨764690, by rfl⟩ : syracuseStep 1019587 = 1529381) B1529381
theorem B1347299 : Blo 354756 1347299 := bstep (se 1 (by rfl) ⟨1010474, by rfl⟩ : syracuseStep 1347299 = 2020949) B2020949
theorem B1347313 : Blo 354756 1347313 := bstep (se 2 (by rfl) ⟨505242, by rfl⟩ : syracuseStep 1347313 = 1010485) B1010485
theorem B757745 : Blo 354756 757745 := bstep (se 2 (by rfl) ⟨284154, by rfl⟩ : syracuseStep 757745 = 568309) B568309
theorem B2297969 : Blo 354756 2297969 := bstep (se 2 (by rfl) ⟨861738, by rfl⟩ : syracuseStep 2297969 = 1723477) B1723477
theorem B1020077 : Blo 354756 1020077 := bstep (se 3 (by rfl) ⟨191264, by rfl⟩ : syracuseStep 1020077 = 382529) B382529
theorem B4559075 : Blo 354756 4559075 := bstep (se 1 (by rfl) ⟨3419306, by rfl⟩ : syracuseStep 4559075 = 6838613) B6838613
theorem B856433 : Blo 354756 856433 := bstep (se 2 (by rfl) ⟨321162, by rfl⟩ : syracuseStep 856433 = 642325) B642325
theorem B4886897 : Blo 354756 4886897 := bstep (se 2 (by rfl) ⟨1832586, by rfl⟩ : syracuseStep 4886897 = 3665173) B3665173
theorem B14913989 : Blo 354756 14913989 := bstep (se 4 (by rfl) ⟨1398186, by rfl⟩ : syracuseStep 14913989 = 2796373) B2796373
theorem B430643 : Blo 354756 430643 := bstep (se 1 (by rfl) ⟨322982, by rfl⟩ : syracuseStep 430643 = 645965) B645965
theorem B1806947 : Blo 354756 1806947 := bstep (se 1 (by rfl) ⟨1355210, by rfl⟩ : syracuseStep 1806947 = 2710421) B2710421
theorem B430691 : Blo 354756 430691 := bstep (se 1 (by rfl) ⟨323018, by rfl⟩ : syracuseStep 430691 = 646037) B646037
theorem B1676045 : Blo 354756 1676045 := bstep (se 3 (by rfl) ⟨314258, by rfl⟩ : syracuseStep 1676045 = 628517) B628517
theorem B3839075 : Blo 354756 3839075 := bstep (se 1 (by rfl) ⟨2879306, by rfl⟩ : syracuseStep 3839075 = 5758613) B5758613
theorem B1348771 : Blo 354756 1348771 := bstep (se 1 (by rfl) ⟨1011578, by rfl⟩ : syracuseStep 1348771 = 2023157) B2023157
theorem B3872069 : Blo 354756 3872069 := bstep (se 4 (by rfl) ⟨363006, by rfl⟩ : syracuseStep 3872069 = 726013) B726013
theorem B1021261 : Blo 354756 1021261 := bstep (se 3 (by rfl) ⟨191486, by rfl⟩ : syracuseStep 1021261 = 382973) B382973
theorem B726403 : Blo 354756 726403 := bstep (se 1 (by rfl) ⟨544802, by rfl⟩ : syracuseStep 726403 = 1089605) B1089605
theorem B1807757 : Blo 354756 1807757 := bstep (se 3 (by rfl) ⟨338954, by rfl⟩ : syracuseStep 1807757 = 677909) B677909
theorem B759299 : Blo 354756 759299 := bstep (se 1 (by rfl) ⟨569474, by rfl⟩ : syracuseStep 759299 = 1138949) B1138949
theorem B1939085 : Blo 354756 1939085 := bstep (se 3 (by rfl) ⟨363578, by rfl⟩ : syracuseStep 1939085 = 727157) B727157
theorem B1218221 : Blo 354756 1218221 := bstep (se 3 (by rfl) ⟨228416, by rfl⟩ : syracuseStep 1218221 = 456833) B456833
theorem B1939277 : Blo 354756 1939277 := bstep (se 3 (by rfl) ⟨363614, by rfl⟩ : syracuseStep 1939277 = 727229) B727229
theorem B399235 : Blo 354756 399235 := bstep (se 1 (by rfl) ⟨299426, by rfl⟩ : syracuseStep 399235 = 598853) B598853
theorem B399379 : Blo 354756 399379 := bstep (se 1 (by rfl) ⟨299534, by rfl⟩ : syracuseStep 399379 = 599069) B599069
theorem B1710193 : Blo 354756 1710193 := bstep (se 2 (by rfl) ⟨641322, by rfl⟩ : syracuseStep 1710193 = 1282645) B1282645
theorem B399523 : Blo 354756 399523 := bstep (se 1 (by rfl) ⟨299642, by rfl⟩ : syracuseStep 399523 = 599285) B599285
theorem B4921613 : Blo 354756 4921613 := bstep (se 3 (by rfl) ⟨922802, by rfl⟩ : syracuseStep 4921613 = 1845605) B1845605
theorem B399667 : Blo 354756 399667 := bstep (se 1 (by rfl) ⟨299750, by rfl⟩ : syracuseStep 399667 = 599501) B599501
theorem B2038193 : Blo 354756 2038193 := bstep (se 2 (by rfl) ⟨764322, by rfl⟩ : syracuseStep 2038193 = 1528645) B1528645
theorem B399811 : Blo 354756 399811 := bstep (se 1 (by rfl) ⟨299858, by rfl⟩ : syracuseStep 399811 = 599717) B599717
theorem B858595 : Blo 354756 858595 := bstep (se 1 (by rfl) ⟨643946, by rfl⟩ : syracuseStep 858595 = 1287893) B1287893
theorem B399955 : Blo 354756 399955 := bstep (se 1 (by rfl) ⟨299966, by rfl⟩ : syracuseStep 399955 = 599933) B599933
theorem B400099 : Blo 354756 400099 := bstep (se 1 (by rfl) ⟨300074, by rfl⟩ : syracuseStep 400099 = 600149) B600149
theorem B400243 : Blo 354756 400243 := bstep (se 1 (by rfl) ⟨300182, by rfl⟩ : syracuseStep 400243 = 600365) B600365
theorem B662467 : Blo 354756 662467 := bstep (se 1 (by rfl) ⟨496850, by rfl⟩ : syracuseStep 662467 = 993701) B993701
theorem B400387 : Blo 354756 400387 := bstep (se 1 (by rfl) ⟨300290, by rfl⟩ : syracuseStep 400387 = 600581) B600581
theorem B400531 : Blo 354756 400531 := bstep (se 1 (by rfl) ⟨300398, by rfl⟩ : syracuseStep 400531 = 600797) B600797
theorem B695569 : Blo 354756 695569 := bstep (se 2 (by rfl) ⟨260838, by rfl⟩ : syracuseStep 695569 = 521677) B521677
theorem B400675 : Blo 354756 400675 := bstep (se 1 (by rfl) ⟨300506, by rfl⟩ : syracuseStep 400675 = 601013) B601013
theorem B1350989 : Blo 354756 1350989 := bstep (se 3 (by rfl) ⟨253310, by rfl⟩ : syracuseStep 1350989 = 506621) B506621
theorem B2596195 : Blo 354756 2596195 := bstep (se 1 (by rfl) ⟨1947146, by rfl⟩ : syracuseStep 2596195 = 3894293) B3894293
theorem B400819 : Blo 354756 400819 := bstep (se 1 (by rfl) ⟨300614, by rfl⟩ : syracuseStep 400819 = 601229) B601229
theorem B1220141 : Blo 354756 1220141 := bstep (se 3 (by rfl) ⟨228776, by rfl⟩ : syracuseStep 1220141 = 457553) B457553
theorem B400963 : Blo 354756 400963 := bstep (se 1 (by rfl) ⟨300722, by rfl⟩ : syracuseStep 400963 = 601445) B601445
theorem B1089091 : Blo 354756 1089091 := bstep (se 1 (by rfl) ⟨816818, by rfl⟩ : syracuseStep 1089091 = 1633637) B1633637
theorem B532145 : Blo 354756 532145 := bstep (se 2 (by rfl) ⟨199554, by rfl⟩ : syracuseStep 532145 = 399109) B399109
theorem B761521 : Blo 354756 761521 := bstep (se 2 (by rfl) ⟨285570, by rfl⟩ : syracuseStep 761521 = 571141) B571141
theorem B859825 : Blo 354756 859825 := bstep (se 2 (by rfl) ⟨322434, by rfl⟩ : syracuseStep 859825 = 644869) B644869
theorem B532163 : Blo 354756 532163 := bstep (se 1 (by rfl) ⟨399122, by rfl⟩ : syracuseStep 532163 = 798245) B798245
theorem B401107 : Blo 354756 401107 := bstep (se 1 (by rfl) ⟨300830, by rfl⟩ : syracuseStep 401107 = 601661) B601661
theorem B532193 : Blo 354756 532193 := bstep (se 2 (by rfl) ⟨199572, by rfl⟩ : syracuseStep 532193 = 399145) B399145
theorem B7282403 : Blo 354756 7282403 := bstep (se 1 (by rfl) ⟨5461802, by rfl⟩ : syracuseStep 7282403 = 10923605) B10923605
theorem B532211 : Blo 354756 532211 := bstep (se 1 (by rfl) ⟨399158, by rfl⟩ : syracuseStep 532211 = 798317) B798317
theorem B532241 : Blo 354756 532241 := bstep (se 2 (by rfl) ⟨199590, by rfl⟩ : syracuseStep 532241 = 399181) B399181
theorem B532259 : Blo 354756 532259 := bstep (se 1 (by rfl) ⟨399194, by rfl⟩ : syracuseStep 532259 = 798389) B798389
theorem B532289 : Blo 354756 532289 := bstep (se 2 (by rfl) ⟨199608, by rfl⟩ : syracuseStep 532289 = 399217) B399217
theorem B532307 : Blo 354756 532307 := bstep (se 1 (by rfl) ⟨399230, by rfl⟩ : syracuseStep 532307 = 798461) B798461
theorem B401251 : Blo 354756 401251 := bstep (se 1 (by rfl) ⟨300938, by rfl⟩ : syracuseStep 401251 = 601877) B601877
theorem B2039651 : Blo 354756 2039651 := bstep (se 1 (by rfl) ⟨1529738, by rfl⟩ : syracuseStep 2039651 = 3059477) B3059477
theorem B532337 : Blo 354756 532337 := bstep (se 2 (by rfl) ⟨199626, by rfl⟩ : syracuseStep 532337 = 399253) B399253
theorem B532355 : Blo 354756 532355 := bstep (se 1 (by rfl) ⟨399266, by rfl⟩ : syracuseStep 532355 = 798533) B798533
theorem B532385 : Blo 354756 532385 := bstep (se 2 (by rfl) ⟨199644, by rfl⟩ : syracuseStep 532385 = 399289) B399289
theorem B532403 : Blo 354756 532403 := bstep (se 1 (by rfl) ⟨399302, by rfl⟩ : syracuseStep 532403 = 798605) B798605
theorem B532433 : Blo 354756 532433 := bstep (se 2 (by rfl) ⟨199662, by rfl⟩ : syracuseStep 532433 = 399325) B399325
theorem B532451 : Blo 354756 532451 := bstep (se 1 (by rfl) ⟨399338, by rfl⟩ : syracuseStep 532451 = 798677) B798677
theorem B401395 : Blo 354756 401395 := bstep (se 1 (by rfl) ⟨301046, by rfl⟩ : syracuseStep 401395 = 602093) B602093
theorem B532481 : Blo 354756 532481 := bstep (se 2 (by rfl) ⟨199680, by rfl⟩ : syracuseStep 532481 = 399361) B399361
theorem B532499 : Blo 354756 532499 := bstep (se 1 (by rfl) ⟨399374, by rfl⟩ : syracuseStep 532499 = 798749) B798749
theorem B532529 : Blo 354756 532529 := bstep (se 2 (by rfl) ⟨199698, by rfl⟩ : syracuseStep 532529 = 399397) B399397
theorem B532547 : Blo 354756 532547 := bstep (se 1 (by rfl) ⟨399410, by rfl⟩ : syracuseStep 532547 = 798821) B798821
theorem B532577 : Blo 354756 532577 := bstep (se 2 (by rfl) ⟨199716, by rfl⟩ : syracuseStep 532577 = 399433) B399433
theorem B532595 : Blo 354756 532595 := bstep (se 1 (by rfl) ⟨399446, by rfl⟩ : syracuseStep 532595 = 798893) B798893
theorem B401539 : Blo 354756 401539 := bstep (se 1 (by rfl) ⟨301154, by rfl⟩ : syracuseStep 401539 = 602309) B602309
theorem B532625 : Blo 354756 532625 := bstep (se 2 (by rfl) ⟨199734, by rfl⟩ : syracuseStep 532625 = 399469) B399469
theorem B532643 : Blo 354756 532643 := bstep (se 1 (by rfl) ⟨399482, by rfl⟩ : syracuseStep 532643 = 798965) B798965
theorem B1220771 : Blo 354756 1220771 := bstep (se 1 (by rfl) ⟨915578, by rfl⟩ : syracuseStep 1220771 = 1831157) B1831157
theorem B532673 : Blo 354756 532673 := bstep (se 2 (by rfl) ⟨199752, by rfl⟩ : syracuseStep 532673 = 399505) B399505
theorem B532691 : Blo 354756 532691 := bstep (se 1 (by rfl) ⟨399518, by rfl⟩ : syracuseStep 532691 = 799037) B799037
theorem B532721 : Blo 354756 532721 := bstep (se 2 (by rfl) ⟨199770, by rfl⟩ : syracuseStep 532721 = 399541) B399541
theorem B1810673 : Blo 354756 1810673 := bstep (se 2 (by rfl) ⟨679002, by rfl⟩ : syracuseStep 1810673 = 1358005) B1358005
theorem B532739 : Blo 354756 532739 := bstep (se 1 (by rfl) ⟨399554, by rfl⟩ : syracuseStep 532739 = 799109) B799109
theorem B401683 : Blo 354756 401683 := bstep (se 1 (by rfl) ⟨301262, by rfl⟩ : syracuseStep 401683 = 602525) B602525
theorem B532769 : Blo 354756 532769 := bstep (se 2 (by rfl) ⟨199788, by rfl⟩ : syracuseStep 532769 = 399577) B399577
theorem B532787 : Blo 354756 532787 := bstep (se 1 (by rfl) ⟨399590, by rfl⟩ : syracuseStep 532787 = 799181) B799181
theorem B532817 : Blo 354756 532817 := bstep (se 2 (by rfl) ⟨199806, by rfl⟩ : syracuseStep 532817 = 399613) B399613
theorem B532835 : Blo 354756 532835 := bstep (se 1 (by rfl) ⟨399626, by rfl⟩ : syracuseStep 532835 = 799253) B799253
theorem B532865 : Blo 354756 532865 := bstep (se 2 (by rfl) ⟨199824, by rfl⟩ : syracuseStep 532865 = 399649) B399649
theorem B532883 : Blo 354756 532883 := bstep (se 1 (by rfl) ⟨399662, by rfl⟩ : syracuseStep 532883 = 799325) B799325
theorem B401827 : Blo 354756 401827 := bstep (se 1 (by rfl) ⟨301370, by rfl⟩ : syracuseStep 401827 = 602741) B602741
theorem B532913 : Blo 354756 532913 := bstep (se 2 (by rfl) ⟨199842, by rfl⟩ : syracuseStep 532913 = 399685) B399685
theorem B1024451 : Blo 354756 1024451 := bstep (se 1 (by rfl) ⟨768338, by rfl⟩ : syracuseStep 1024451 = 1536677) B1536677
theorem B532931 : Blo 354756 532931 := bstep (se 1 (by rfl) ⟨399698, by rfl⟩ : syracuseStep 532931 = 799397) B799397
theorem B532961 : Blo 354756 532961 := bstep (se 2 (by rfl) ⟨199860, by rfl⟩ : syracuseStep 532961 = 399721) B399721
theorem B532979 : Blo 354756 532979 := bstep (se 1 (by rfl) ⟨399734, by rfl⟩ : syracuseStep 532979 = 799469) B799469
theorem B533009 : Blo 354756 533009 := bstep (se 2 (by rfl) ⟨199878, by rfl⟩ : syracuseStep 533009 = 399757) B399757
theorem B533027 : Blo 354756 533027 := bstep (se 1 (by rfl) ⟨399770, by rfl⟩ : syracuseStep 533027 = 799541) B799541
theorem B401971 : Blo 354756 401971 := bstep (se 1 (by rfl) ⟨301478, by rfl⟩ : syracuseStep 401971 = 602957) B602957
theorem B533057 : Blo 354756 533057 := bstep (se 2 (by rfl) ⟨199896, by rfl⟩ : syracuseStep 533057 = 399793) B399793
theorem B533075 : Blo 354756 533075 := bstep (se 1 (by rfl) ⟨399806, by rfl⟩ : syracuseStep 533075 = 799613) B799613
theorem B533105 : Blo 354756 533105 := bstep (se 2 (by rfl) ⟨199914, by rfl⟩ : syracuseStep 533105 = 399829) B399829
theorem B598657 : Blo 354756 598657 := bstep (se 2 (by rfl) ⟨224496, by rfl⟩ : syracuseStep 598657 = 448993) B448993
theorem B533123 : Blo 354756 533123 := bstep (se 1 (by rfl) ⟨399842, by rfl⟩ : syracuseStep 533123 = 799685) B799685
theorem B533153 : Blo 354756 533153 := bstep (se 2 (by rfl) ⟨199932, by rfl⟩ : syracuseStep 533153 = 399865) B399865
theorem B598691 : Blo 354756 598691 := bstep (se 1 (by rfl) ⟨449018, by rfl⟩ : syracuseStep 598691 = 898037) B898037
theorem B533171 : Blo 354756 533171 := bstep (se 1 (by rfl) ⟨399878, by rfl⟩ : syracuseStep 533171 = 799757) B799757
theorem B402115 : Blo 354756 402115 := bstep (se 1 (by rfl) ⟨301586, by rfl⟩ : syracuseStep 402115 = 603173) B603173
theorem B533201 : Blo 354756 533201 := bstep (se 2 (by rfl) ⟨199950, by rfl⟩ : syracuseStep 533201 = 399901) B399901
theorem B1516259 : Blo 354756 1516259 := bstep (se 1 (by rfl) ⟨1137194, by rfl⟩ : syracuseStep 1516259 = 2274389) B2274389
theorem B533219 : Blo 354756 533219 := bstep (se 1 (by rfl) ⟨399914, by rfl⟩ : syracuseStep 533219 = 799829) B799829
theorem B533249 : Blo 354756 533249 := bstep (se 2 (by rfl) ⟨199968, by rfl⟩ : syracuseStep 533249 = 399937) B399937
theorem B533267 : Blo 354756 533267 := bstep (se 1 (by rfl) ⟨399950, by rfl⟩ : syracuseStep 533267 = 799901) B799901
theorem B598819 : Blo 354756 598819 := bstep (se 1 (by rfl) ⟨449114, by rfl⟩ : syracuseStep 598819 = 898229) B898229
theorem B533297 : Blo 354756 533297 := bstep (se 2 (by rfl) ⟨199986, by rfl⟩ : syracuseStep 533297 = 399973) B399973
theorem B533315 : Blo 354756 533315 := bstep (se 1 (by rfl) ⟨399986, by rfl⟩ : syracuseStep 533315 = 799973) B799973
theorem B2040653 : Blo 354756 2040653 := bstep (se 3 (by rfl) ⟨382622, by rfl⟩ : syracuseStep 2040653 = 765245) B765245
theorem B402259 : Blo 354756 402259 := bstep (se 1 (by rfl) ⟨301694, by rfl⟩ : syracuseStep 402259 = 603389) B603389
theorem B533345 : Blo 354756 533345 := bstep (se 2 (by rfl) ⟨200004, by rfl⟩ : syracuseStep 533345 = 400009) B400009
theorem B533363 : Blo 354756 533363 := bstep (se 1 (by rfl) ⟨400022, by rfl⟩ : syracuseStep 533363 = 800045) B800045
theorem B533393 : Blo 354756 533393 := bstep (se 2 (by rfl) ⟨200022, by rfl⟩ : syracuseStep 533393 = 400045) B400045
theorem B533411 : Blo 354756 533411 := bstep (se 1 (by rfl) ⟨400058, by rfl⟩ : syracuseStep 533411 = 800117) B800117
theorem B598961 : Blo 354756 598961 := bstep (se 2 (by rfl) ⟨224610, by rfl⟩ : syracuseStep 598961 = 449221) B449221
theorem B533441 : Blo 354756 533441 := bstep (se 2 (by rfl) ⟨200040, by rfl⟩ : syracuseStep 533441 = 400081) B400081
theorem B533459 : Blo 354756 533459 := bstep (se 1 (by rfl) ⟨400094, by rfl⟩ : syracuseStep 533459 = 800189) B800189
theorem B402403 : Blo 354756 402403 := bstep (se 1 (by rfl) ⟨301802, by rfl⟩ : syracuseStep 402403 = 603605) B603605
theorem B533489 : Blo 354756 533489 := bstep (se 2 (by rfl) ⟨200058, by rfl⟩ : syracuseStep 533489 = 400117) B400117
theorem B533507 : Blo 354756 533507 := bstep (se 1 (by rfl) ⟨400130, by rfl⟩ : syracuseStep 533507 = 800261) B800261
theorem B533537 : Blo 354756 533537 := bstep (se 2 (by rfl) ⟨200076, by rfl⟩ : syracuseStep 533537 = 400153) B400153
theorem B599089 : Blo 354756 599089 := bstep (se 2 (by rfl) ⟨224658, by rfl⟩ : syracuseStep 599089 = 449317) B449317
theorem B533555 : Blo 354756 533555 := bstep (se 1 (by rfl) ⟨400166, by rfl⟩ : syracuseStep 533555 = 800333) B800333
theorem B533585 : Blo 354756 533585 := bstep (se 2 (by rfl) ⟨200094, by rfl⟩ : syracuseStep 533585 = 400189) B400189
theorem B599123 : Blo 354756 599123 := bstep (se 1 (by rfl) ⟨449342, by rfl⟩ : syracuseStep 599123 = 898685) B898685
theorem B533603 : Blo 354756 533603 := bstep (se 1 (by rfl) ⟨400202, by rfl⟩ : syracuseStep 533603 = 800405) B800405
theorem B402547 : Blo 354756 402547 := bstep (se 1 (by rfl) ⟨301910, by rfl⟩ : syracuseStep 402547 = 603821) B603821
theorem B533633 : Blo 354756 533633 := bstep (se 2 (by rfl) ⟨200112, by rfl⟩ : syracuseStep 533633 = 400225) B400225
theorem B533651 : Blo 354756 533651 := bstep (se 1 (by rfl) ⟨400238, by rfl⟩ : syracuseStep 533651 = 800477) B800477
theorem B533681 : Blo 354756 533681 := bstep (se 2 (by rfl) ⟨200130, by rfl⟩ : syracuseStep 533681 = 400261) B400261
theorem B533699 : Blo 354756 533699 := bstep (se 1 (by rfl) ⟨400274, by rfl⟩ : syracuseStep 533699 = 800549) B800549
theorem B599251 : Blo 354756 599251 := bstep (se 1 (by rfl) ⟨449438, by rfl⟩ : syracuseStep 599251 = 898877) B898877
theorem B533729 : Blo 354756 533729 := bstep (se 2 (by rfl) ⟨200148, by rfl⟩ : syracuseStep 533729 = 400297) B400297
theorem B533747 : Blo 354756 533747 := bstep (se 1 (by rfl) ⟨400310, by rfl⟩ : syracuseStep 533747 = 800621) B800621
theorem B402691 : Blo 354756 402691 := bstep (se 1 (by rfl) ⟨302018, by rfl⟩ : syracuseStep 402691 = 604037) B604037
theorem B533777 : Blo 354756 533777 := bstep (se 2 (by rfl) ⟨200166, by rfl⟩ : syracuseStep 533777 = 400333) B400333
theorem B533795 : Blo 354756 533795 := bstep (se 1 (by rfl) ⟨400346, by rfl⟩ : syracuseStep 533795 = 800693) B800693
theorem B533825 : Blo 354756 533825 := bstep (se 2 (by rfl) ⟨200184, by rfl⟩ : syracuseStep 533825 = 400369) B400369
theorem B2434373 : Blo 354756 2434373 := bstep (se 4 (by rfl) ⟨228222, by rfl⟩ : syracuseStep 2434373 = 456445) B456445
theorem B533843 : Blo 354756 533843 := bstep (se 1 (by rfl) ⟨400382, by rfl⟩ : syracuseStep 533843 = 800765) B800765
theorem B599393 : Blo 354756 599393 := bstep (se 2 (by rfl) ⟨224772, by rfl⟩ : syracuseStep 599393 = 449545) B449545
theorem B533873 : Blo 354756 533873 := bstep (se 2 (by rfl) ⟨200202, by rfl⟩ : syracuseStep 533873 = 400405) B400405
theorem B533891 : Blo 354756 533891 := bstep (se 1 (by rfl) ⟨400418, by rfl⟩ : syracuseStep 533891 = 800837) B800837
theorem B402835 : Blo 354756 402835 := bstep (se 1 (by rfl) ⟨302126, by rfl⟩ : syracuseStep 402835 = 604253) B604253
theorem B533921 : Blo 354756 533921 := bstep (se 2 (by rfl) ⟨200220, by rfl⟩ : syracuseStep 533921 = 400441) B400441
theorem B533939 : Blo 354756 533939 := bstep (se 1 (by rfl) ⟨400454, by rfl⟩ : syracuseStep 533939 = 800909) B800909
theorem B533969 : Blo 354756 533969 := bstep (se 2 (by rfl) ⟨200238, by rfl⟩ : syracuseStep 533969 = 400477) B400477
theorem B599521 : Blo 354756 599521 := bstep (se 2 (by rfl) ⟨224820, by rfl⟩ : syracuseStep 599521 = 449641) B449641
theorem B533987 : Blo 354756 533987 := bstep (se 1 (by rfl) ⟨400490, by rfl⟩ : syracuseStep 533987 = 800981) B800981
theorem B534017 : Blo 354756 534017 := bstep (se 2 (by rfl) ⟨200256, by rfl⟩ : syracuseStep 534017 = 400513) B400513
theorem B599555 : Blo 354756 599555 := bstep (se 1 (by rfl) ⟨449666, by rfl⟩ : syracuseStep 599555 = 899333) B899333
theorem B534035 : Blo 354756 534035 := bstep (se 1 (by rfl) ⟨400526, by rfl⟩ : syracuseStep 534035 = 801053) B801053
theorem B402979 : Blo 354756 402979 := bstep (se 1 (by rfl) ⟨302234, by rfl⟩ : syracuseStep 402979 = 604469) B604469
theorem B534065 : Blo 354756 534065 := bstep (se 2 (by rfl) ⟨200274, by rfl⟩ : syracuseStep 534065 = 400549) B400549
theorem B534083 : Blo 354756 534083 := bstep (se 1 (by rfl) ⟨400562, by rfl⟩ : syracuseStep 534083 = 801125) B801125
theorem B534113 : Blo 354756 534113 := bstep (se 2 (by rfl) ⟨200292, by rfl⟩ : syracuseStep 534113 = 400585) B400585
theorem B534131 : Blo 354756 534131 := bstep (se 1 (by rfl) ⟨400598, by rfl⟩ : syracuseStep 534131 = 801197) B801197
theorem B599683 : Blo 354756 599683 := bstep (se 1 (by rfl) ⟨449762, by rfl⟩ : syracuseStep 599683 = 899525) B899525
theorem B534161 : Blo 354756 534161 := bstep (se 2 (by rfl) ⟨200310, by rfl⟩ : syracuseStep 534161 = 400621) B400621
theorem B534179 : Blo 354756 534179 := bstep (se 1 (by rfl) ⟨400634, by rfl⟩ : syracuseStep 534179 = 801269) B801269
theorem B1812131 : Blo 354756 1812131 := bstep (se 1 (by rfl) ⟨1359098, by rfl⟩ : syracuseStep 1812131 = 2718197) B2718197
theorem B403123 : Blo 354756 403123 := bstep (se 1 (by rfl) ⟨302342, by rfl⟩ : syracuseStep 403123 = 604685) B604685
theorem B534209 : Blo 354756 534209 := bstep (se 2 (by rfl) ⟨200328, by rfl⟩ : syracuseStep 534209 = 400657) B400657
theorem B534227 : Blo 354756 534227 := bstep (se 1 (by rfl) ⟨400670, by rfl⟩ : syracuseStep 534227 = 801341) B801341
theorem B534257 : Blo 354756 534257 := bstep (se 2 (by rfl) ⟨200346, by rfl⟩ : syracuseStep 534257 = 400693) B400693
theorem B534275 : Blo 354756 534275 := bstep (se 1 (by rfl) ⟨400706, by rfl⟩ : syracuseStep 534275 = 801413) B801413
theorem B599825 : Blo 354756 599825 := bstep (se 2 (by rfl) ⟨224934, by rfl⟩ : syracuseStep 599825 = 449869) B449869
theorem B534305 : Blo 354756 534305 := bstep (se 2 (by rfl) ⟨200364, by rfl⟩ : syracuseStep 534305 = 400729) B400729
theorem B534323 : Blo 354756 534323 := bstep (se 1 (by rfl) ⟨400742, by rfl⟩ : syracuseStep 534323 = 801485) B801485
theorem B403267 : Blo 354756 403267 := bstep (se 1 (by rfl) ⟨302450, by rfl⟩ : syracuseStep 403267 = 604901) B604901
theorem B534353 : Blo 354756 534353 := bstep (se 2 (by rfl) ⟨200382, by rfl⟩ : syracuseStep 534353 = 400765) B400765
theorem B534371 : Blo 354756 534371 := bstep (se 1 (by rfl) ⟨400778, by rfl⟩ : syracuseStep 534371 = 801557) B801557
theorem B534401 : Blo 354756 534401 := bstep (se 2 (by rfl) ⟨200400, by rfl⟩ : syracuseStep 534401 = 400801) B400801
theorem B599953 : Blo 354756 599953 := bstep (se 2 (by rfl) ⟨224982, by rfl⟩ : syracuseStep 599953 = 449965) B449965
theorem B534419 : Blo 354756 534419 := bstep (se 1 (by rfl) ⟨400814, by rfl⟩ : syracuseStep 534419 = 801629) B801629
theorem B534449 : Blo 354756 534449 := bstep (se 2 (by rfl) ⟨200418, by rfl⟩ : syracuseStep 534449 = 400837) B400837
theorem B599987 : Blo 354756 599987 := bstep (se 1 (by rfl) ⟨449990, by rfl⟩ : syracuseStep 599987 = 899981) B899981
theorem B534467 : Blo 354756 534467 := bstep (se 1 (by rfl) ⟨400850, by rfl⟩ : syracuseStep 534467 = 801701) B801701
theorem B403411 : Blo 354756 403411 := bstep (se 1 (by rfl) ⟨302558, by rfl⟩ : syracuseStep 403411 = 605117) B605117
theorem B534497 : Blo 354756 534497 := bstep (se 2 (by rfl) ⟨200436, by rfl⟩ : syracuseStep 534497 = 400873) B400873
theorem B534515 : Blo 354756 534515 := bstep (se 1 (by rfl) ⟨400886, by rfl⟩ : syracuseStep 534515 = 801773) B801773
theorem B534545 : Blo 354756 534545 := bstep (se 2 (by rfl) ⟨200454, by rfl⟩ : syracuseStep 534545 = 400909) B400909
theorem B534563 : Blo 354756 534563 := bstep (se 1 (by rfl) ⟨400922, by rfl⟩ : syracuseStep 534563 = 801845) B801845
theorem B600115 : Blo 354756 600115 := bstep (se 1 (by rfl) ⟨450086, by rfl⟩ : syracuseStep 600115 = 900173) B900173
theorem B534593 : Blo 354756 534593 := bstep (se 2 (by rfl) ⟨200472, by rfl⟩ : syracuseStep 534593 = 400945) B400945
theorem B534611 : Blo 354756 534611 := bstep (se 1 (by rfl) ⟨400958, by rfl⟩ : syracuseStep 534611 = 801917) B801917
theorem B403555 : Blo 354756 403555 := bstep (se 1 (by rfl) ⟨302666, by rfl⟩ : syracuseStep 403555 = 605333) B605333
theorem B534641 : Blo 354756 534641 := bstep (se 2 (by rfl) ⟨200490, by rfl⟩ : syracuseStep 534641 = 400981) B400981
theorem B534659 : Blo 354756 534659 := bstep (se 1 (by rfl) ⟨400994, by rfl⟩ : syracuseStep 534659 = 801989) B801989
theorem B5187725 : Blo 354756 5187725 := bstep (se 3 (by rfl) ⟨972698, by rfl⟩ : syracuseStep 5187725 = 1945397) B1945397
theorem B534689 : Blo 354756 534689 := bstep (se 2 (by rfl) ⟨200508, by rfl⟩ : syracuseStep 534689 = 401017) B401017
theorem B1353905 : Blo 354756 1353905 := bstep (se 2 (by rfl) ⟨507714, by rfl⟩ : syracuseStep 1353905 = 1015429) B1015429
theorem B534707 : Blo 354756 534707 := bstep (se 1 (by rfl) ⟨401030, by rfl⟩ : syracuseStep 534707 = 802061) B802061
theorem B600257 : Blo 354756 600257 := bstep (se 2 (by rfl) ⟨225096, by rfl⟩ : syracuseStep 600257 = 450193) B450193
theorem B534737 : Blo 354756 534737 := bstep (se 2 (by rfl) ⟨200526, by rfl⟩ : syracuseStep 534737 = 401053) B401053
theorem B534755 : Blo 354756 534755 := bstep (se 1 (by rfl) ⟨401066, by rfl⟩ : syracuseStep 534755 = 802133) B802133
theorem B534785 : Blo 354756 534785 := bstep (se 2 (by rfl) ⟨200544, by rfl⟩ : syracuseStep 534785 = 401089) B401089
theorem B534803 : Blo 354756 534803 := bstep (se 1 (by rfl) ⟨401102, by rfl⟩ : syracuseStep 534803 = 802205) B802205
theorem B534833 : Blo 354756 534833 := bstep (se 2 (by rfl) ⟨200562, by rfl⟩ : syracuseStep 534833 = 401125) B401125
theorem B600385 : Blo 354756 600385 := bstep (se 2 (by rfl) ⟨225144, by rfl⟩ : syracuseStep 600385 = 450289) B450289
theorem B534851 : Blo 354756 534851 := bstep (se 1 (by rfl) ⟨401138, by rfl⟩ : syracuseStep 534851 = 802277) B802277
theorem B534881 : Blo 354756 534881 := bstep (se 2 (by rfl) ⟨200580, by rfl⟩ : syracuseStep 534881 = 401161) B401161
theorem B600419 : Blo 354756 600419 := bstep (se 1 (by rfl) ⟨450314, by rfl⟩ : syracuseStep 600419 = 900629) B900629
theorem B534899 : Blo 354756 534899 := bstep (se 1 (by rfl) ⟨401174, by rfl⟩ : syracuseStep 534899 = 802349) B802349
theorem B534929 : Blo 354756 534929 := bstep (se 2 (by rfl) ⟨200598, by rfl⟩ : syracuseStep 534929 = 401197) B401197
theorem B534947 : Blo 354756 534947 := bstep (se 1 (by rfl) ⟨401210, by rfl⟩ : syracuseStep 534947 = 802421) B802421
theorem B534977 : Blo 354756 534977 := bstep (se 2 (by rfl) ⟨200616, by rfl⟩ : syracuseStep 534977 = 401233) B401233
theorem B1812941 : Blo 354756 1812941 := bstep (se 3 (by rfl) ⟨339926, by rfl⟩ : syracuseStep 1812941 = 679853) B679853
theorem B534995 : Blo 354756 534995 := bstep (se 1 (by rfl) ⟨401246, by rfl⟩ : syracuseStep 534995 = 802493) B802493
theorem B600547 : Blo 354756 600547 := bstep (se 1 (by rfl) ⟨450410, by rfl⟩ : syracuseStep 600547 = 900821) B900821
theorem B535025 : Blo 354756 535025 := bstep (se 2 (by rfl) ⟨200634, by rfl⟩ : syracuseStep 535025 = 401269) B401269
theorem B535043 : Blo 354756 535043 := bstep (se 1 (by rfl) ⟨401282, by rfl⟩ : syracuseStep 535043 = 802565) B802565
theorem B535073 : Blo 354756 535073 := bstep (se 2 (by rfl) ⟨200652, by rfl⟩ : syracuseStep 535073 = 401305) B401305
theorem B535091 : Blo 354756 535091 := bstep (se 1 (by rfl) ⟨401318, by rfl⟩ : syracuseStep 535091 = 802637) B802637
theorem B535121 : Blo 354756 535121 := bstep (se 2 (by rfl) ⟨200670, by rfl⟩ : syracuseStep 535121 = 401341) B401341
theorem B535139 : Blo 354756 535139 := bstep (se 1 (by rfl) ⟨401354, by rfl⟩ : syracuseStep 535139 = 802709) B802709
theorem B600689 : Blo 354756 600689 := bstep (se 2 (by rfl) ⟨225258, by rfl⟩ : syracuseStep 600689 = 450517) B450517
theorem B1288817 : Blo 354756 1288817 := bstep (se 2 (by rfl) ⟨483306, by rfl⟩ : syracuseStep 1288817 = 966613) B966613
theorem B535169 : Blo 354756 535169 := bstep (se 2 (by rfl) ⟨200688, by rfl⟩ : syracuseStep 535169 = 401377) B401377
theorem B535187 : Blo 354756 535187 := bstep (se 1 (by rfl) ⟨401390, by rfl⟩ : syracuseStep 535187 = 802781) B802781
theorem B764579 : Blo 354756 764579 := bstep (se 1 (by rfl) ⟨573434, by rfl⟩ : syracuseStep 764579 = 1146869) B1146869
theorem B1518257 : Blo 354756 1518257 := bstep (se 2 (by rfl) ⟨569346, by rfl⟩ : syracuseStep 1518257 = 1138693) B1138693
theorem B535217 : Blo 354756 535217 := bstep (se 2 (by rfl) ⟨200706, by rfl⟩ : syracuseStep 535217 = 401413) B401413
theorem B535235 : Blo 354756 535235 := bstep (se 1 (by rfl) ⟨401426, by rfl⟩ : syracuseStep 535235 = 802853) B802853
theorem B535265 : Blo 354756 535265 := bstep (se 2 (by rfl) ⟨200724, by rfl⟩ : syracuseStep 535265 = 401449) B401449
theorem B600817 : Blo 354756 600817 := bstep (se 2 (by rfl) ⟨225306, by rfl⟩ : syracuseStep 600817 = 450613) B450613
theorem B535283 : Blo 354756 535283 := bstep (se 1 (by rfl) ⟨401462, by rfl⟩ : syracuseStep 535283 = 802925) B802925
theorem B404227 : Blo 354756 404227 := bstep (se 1 (by rfl) ⟨303170, by rfl⟩ : syracuseStep 404227 = 606341) B606341
theorem B535313 : Blo 354756 535313 := bstep (se 2 (by rfl) ⟨200742, by rfl⟩ : syracuseStep 535313 = 401485) B401485
theorem B600851 : Blo 354756 600851 := bstep (se 1 (by rfl) ⟨450638, by rfl⟩ : syracuseStep 600851 = 901277) B901277
theorem B535331 : Blo 354756 535331 := bstep (se 1 (by rfl) ⟨401498, by rfl⟩ : syracuseStep 535331 = 802997) B802997
theorem B535361 : Blo 354756 535361 := bstep (se 2 (by rfl) ⟨200760, by rfl⟩ : syracuseStep 535361 = 401521) B401521
theorem B535379 : Blo 354756 535379 := bstep (se 1 (by rfl) ⟨401534, by rfl⟩ : syracuseStep 535379 = 803069) B803069
theorem B535409 : Blo 354756 535409 := bstep (se 2 (by rfl) ⟨200778, by rfl⟩ : syracuseStep 535409 = 401557) B401557
theorem B535427 : Blo 354756 535427 := bstep (se 1 (by rfl) ⟨401570, by rfl⟩ : syracuseStep 535427 = 803141) B803141
theorem B600979 : Blo 354756 600979 := bstep (se 1 (by rfl) ⟨450734, by rfl⟩ : syracuseStep 600979 = 901469) B901469
theorem B535457 : Blo 354756 535457 := bstep (se 2 (by rfl) ⟨200796, by rfl⟩ : syracuseStep 535457 = 401593) B401593
theorem B535475 : Blo 354756 535475 := bstep (se 1 (by rfl) ⟨401606, by rfl⟩ : syracuseStep 535475 = 803213) B803213
theorem B535505 : Blo 354756 535505 := bstep (se 2 (by rfl) ⟨200814, by rfl⟩ : syracuseStep 535505 = 401629) B401629
theorem B535523 : Blo 354756 535523 := bstep (se 1 (by rfl) ⟨401642, by rfl⟩ : syracuseStep 535523 = 803285) B803285
theorem B535553 : Blo 354756 535553 := bstep (se 2 (by rfl) ⟨200832, by rfl⟩ : syracuseStep 535553 = 401665) B401665
theorem B535571 : Blo 354756 535571 := bstep (se 1 (by rfl) ⟨401678, by rfl⟩ : syracuseStep 535571 = 803357) B803357
theorem B601121 : Blo 354756 601121 := bstep (se 2 (by rfl) ⟨225420, by rfl⟩ : syracuseStep 601121 = 450841) B450841
theorem B535601 : Blo 354756 535601 := bstep (se 2 (by rfl) ⟨200850, by rfl⟩ : syracuseStep 535601 = 401701) B401701
theorem B535619 : Blo 354756 535619 := bstep (se 1 (by rfl) ⟨401714, by rfl⟩ : syracuseStep 535619 = 803429) B803429
theorem B535649 : Blo 354756 535649 := bstep (se 2 (by rfl) ⟨200868, by rfl⟩ : syracuseStep 535649 = 401737) B401737
theorem B535667 : Blo 354756 535667 := bstep (se 1 (by rfl) ⟨401750, by rfl⟩ : syracuseStep 535667 = 803501) B803501
theorem B535697 : Blo 354756 535697 := bstep (se 2 (by rfl) ⟨200886, by rfl⟩ : syracuseStep 535697 = 401773) B401773
theorem B601249 : Blo 354756 601249 := bstep (se 2 (by rfl) ⟨225468, by rfl⟩ : syracuseStep 601249 = 450937) B450937
theorem B535715 : Blo 354756 535715 := bstep (se 1 (by rfl) ⟨401786, by rfl⟩ : syracuseStep 535715 = 803573) B803573
theorem B535745 : Blo 354756 535745 := bstep (se 2 (by rfl) ⟨200904, by rfl⟩ : syracuseStep 535745 = 401809) B401809
theorem B601283 : Blo 354756 601283 := bstep (se 1 (by rfl) ⟨450962, by rfl⟩ : syracuseStep 601283 = 901925) B901925
theorem B535763 : Blo 354756 535763 := bstep (se 1 (by rfl) ⟨401822, by rfl⟩ : syracuseStep 535763 = 803645) B803645
theorem B535793 : Blo 354756 535793 := bstep (se 2 (by rfl) ⟨200922, by rfl⟩ : syracuseStep 535793 = 401845) B401845
theorem B535811 : Blo 354756 535811 := bstep (se 1 (by rfl) ⟨401858, by rfl⟩ : syracuseStep 535811 = 803717) B803717
theorem B535841 : Blo 354756 535841 := bstep (se 2 (by rfl) ⟨200940, by rfl⟩ : syracuseStep 535841 = 401881) B401881
theorem B535859 : Blo 354756 535859 := bstep (se 1 (by rfl) ⟨401894, by rfl⟩ : syracuseStep 535859 = 803789) B803789
theorem B601411 : Blo 354756 601411 := bstep (se 1 (by rfl) ⟨451058, by rfl⟩ : syracuseStep 601411 = 902117) B902117
theorem B535889 : Blo 354756 535889 := bstep (se 2 (by rfl) ⟨200958, by rfl⟩ : syracuseStep 535889 = 401917) B401917
theorem B535907 : Blo 354756 535907 := bstep (se 1 (by rfl) ⟨401930, by rfl⟩ : syracuseStep 535907 = 803861) B803861
theorem B535937 : Blo 354756 535937 := bstep (se 2 (by rfl) ⟨200976, by rfl⟩ : syracuseStep 535937 = 401953) B401953
theorem B535955 : Blo 354756 535955 := bstep (se 1 (by rfl) ⟨401966, by rfl⟩ : syracuseStep 535955 = 803933) B803933
theorem B1027505 : Blo 354756 1027505 := bstep (se 2 (by rfl) ⟨385314, by rfl⟩ : syracuseStep 1027505 = 770629) B770629
theorem B535985 : Blo 354756 535985 := bstep (se 2 (by rfl) ⟨200994, by rfl⟩ : syracuseStep 535985 = 401989) B401989
theorem B536003 : Blo 354756 536003 := bstep (se 1 (by rfl) ⟨402002, by rfl⟩ : syracuseStep 536003 = 804005) B804005
theorem B601553 : Blo 354756 601553 := bstep (se 2 (by rfl) ⟨225582, by rfl⟩ : syracuseStep 601553 = 451165) B451165
theorem B536033 : Blo 354756 536033 := bstep (se 2 (by rfl) ⟨201012, by rfl⟩ : syracuseStep 536033 = 402025) B402025
theorem B536051 : Blo 354756 536051 := bstep (se 1 (by rfl) ⟨402038, by rfl⟩ : syracuseStep 536051 = 804077) B804077
theorem B765443 : Blo 354756 765443 := bstep (se 1 (by rfl) ⟨574082, by rfl⟩ : syracuseStep 765443 = 1148165) B1148165
theorem B536081 : Blo 354756 536081 := bstep (se 2 (by rfl) ⟨201030, by rfl⟩ : syracuseStep 536081 = 402061) B402061
theorem B1846819 : Blo 354756 1846819 := bstep (se 1 (by rfl) ⟨1385114, by rfl⟩ : syracuseStep 1846819 = 2770229) B2770229
theorem B536099 : Blo 354756 536099 := bstep (se 1 (by rfl) ⟨402074, by rfl⟩ : syracuseStep 536099 = 804149) B804149
theorem B536129 : Blo 354756 536129 := bstep (se 2 (by rfl) ⟨201048, by rfl⟩ : syracuseStep 536129 = 402097) B402097
theorem B1519181 : Blo 354756 1519181 := bstep (se 3 (by rfl) ⟨284846, by rfl⟩ : syracuseStep 1519181 = 569693) B569693
theorem B601681 : Blo 354756 601681 := bstep (se 2 (by rfl) ⟨225630, by rfl⟩ : syracuseStep 601681 = 451261) B451261
theorem B536147 : Blo 354756 536147 := bstep (se 1 (by rfl) ⟨402110, by rfl⟩ : syracuseStep 536147 = 804221) B804221
theorem B1355363 : Blo 354756 1355363 := bstep (se 1 (by rfl) ⟨1016522, by rfl⟩ : syracuseStep 1355363 = 2033045) B2033045
theorem B536177 : Blo 354756 536177 := bstep (se 2 (by rfl) ⟨201066, by rfl⟩ : syracuseStep 536177 = 402133) B402133
theorem B765553 : Blo 354756 765553 := bstep (se 2 (by rfl) ⟨287082, by rfl⟩ : syracuseStep 765553 = 574165) B574165
theorem B601715 : Blo 354756 601715 := bstep (se 1 (by rfl) ⟨451286, by rfl⟩ : syracuseStep 601715 = 902573) B902573
theorem B536195 : Blo 354756 536195 := bstep (se 1 (by rfl) ⟨402146, by rfl⟩ : syracuseStep 536195 = 804293) B804293
theorem B798353 : Blo 354756 798353 := bstep (se 2 (by rfl) ⟨299382, by rfl⟩ : syracuseStep 798353 = 598765) B598765
theorem B536225 : Blo 354756 536225 := bstep (se 2 (by rfl) ⟨201084, by rfl⟩ : syracuseStep 536225 = 402169) B402169
theorem B798371 : Blo 354756 798371 := bstep (se 1 (by rfl) ⟨598778, by rfl⟩ : syracuseStep 798371 = 1197557) B1197557
theorem B536243 : Blo 354756 536243 := bstep (se 1 (by rfl) ⟨402182, by rfl⟩ : syracuseStep 536243 = 804365) B804365
theorem B569027 : Blo 354756 569027 := bstep (se 1 (by rfl) ⟨426770, by rfl⟩ : syracuseStep 569027 = 853541) B853541
theorem B536273 : Blo 354756 536273 := bstep (se 2 (by rfl) ⟨201102, by rfl⟩ : syracuseStep 536273 = 402205) B402205
theorem B536291 : Blo 354756 536291 := bstep (se 1 (by rfl) ⟨402218, by rfl⟩ : syracuseStep 536291 = 804437) B804437
theorem B1289969 : Blo 354756 1289969 := bstep (se 2 (by rfl) ⟨483738, by rfl⟩ : syracuseStep 1289969 = 967477) B967477
theorem B405235 : Blo 354756 405235 := bstep (se 1 (by rfl) ⟨303926, by rfl⟩ : syracuseStep 405235 = 607853) B607853
theorem B601843 : Blo 354756 601843 := bstep (se 1 (by rfl) ⟨451382, by rfl⟩ : syracuseStep 601843 = 902765) B902765
theorem B536321 : Blo 354756 536321 := bstep (se 2 (by rfl) ⟨201120, by rfl⟩ : syracuseStep 536321 = 402241) B402241
theorem B536339 : Blo 354756 536339 := bstep (se 1 (by rfl) ⟨402254, by rfl⟩ : syracuseStep 536339 = 804509) B804509
theorem B536369 : Blo 354756 536369 := bstep (se 2 (by rfl) ⟨201138, by rfl⟩ : syracuseStep 536369 = 402277) B402277
theorem B536387 : Blo 354756 536387 := bstep (se 1 (by rfl) ⟨402290, by rfl⟩ : syracuseStep 536387 = 804581) B804581
theorem B536417 : Blo 354756 536417 := bstep (se 2 (by rfl) ⟨201156, by rfl⟩ : syracuseStep 536417 = 402313) B402313
theorem B962417 : Blo 354756 962417 := bstep (se 2 (by rfl) ⟨360906, by rfl⟩ : syracuseStep 962417 = 721813) B721813
theorem B536435 : Blo 354756 536435 := bstep (se 1 (by rfl) ⟨402326, by rfl⟩ : syracuseStep 536435 = 804653) B804653
theorem B601985 : Blo 354756 601985 := bstep (se 2 (by rfl) ⟨225744, by rfl⟩ : syracuseStep 601985 = 451489) B451489
theorem B536465 : Blo 354756 536465 := bstep (se 2 (by rfl) ⟨201174, by rfl⟩ : syracuseStep 536465 = 402349) B402349
theorem B536483 : Blo 354756 536483 := bstep (se 1 (by rfl) ⟨402362, by rfl⟩ : syracuseStep 536483 = 804725) B804725
theorem B798641 : Blo 354756 798641 := bstep (se 2 (by rfl) ⟨299490, by rfl⟩ : syracuseStep 798641 = 598981) B598981
theorem B536513 : Blo 354756 536513 := bstep (se 2 (by rfl) ⟨201192, by rfl⟩ : syracuseStep 536513 = 402385) B402385
theorem B798659 : Blo 354756 798659 := bstep (se 1 (by rfl) ⟨598994, by rfl⟩ : syracuseStep 798659 = 1197989) B1197989
theorem B536531 : Blo 354756 536531 := bstep (se 1 (by rfl) ⟨402398, by rfl⟩ : syracuseStep 536531 = 804797) B804797
theorem B569315 : Blo 354756 569315 := bstep (se 1 (by rfl) ⟨426986, by rfl⟩ : syracuseStep 569315 = 853973) B853973
theorem B536561 : Blo 354756 536561 := bstep (se 2 (by rfl) ⟨201210, by rfl⟩ : syracuseStep 536561 = 402421) B402421
theorem B602113 : Blo 354756 602113 := bstep (se 2 (by rfl) ⟨225792, by rfl⟩ : syracuseStep 602113 = 451585) B451585
theorem B536579 : Blo 354756 536579 := bstep (se 1 (by rfl) ⟨402434, by rfl⟩ : syracuseStep 536579 = 804869) B804869
theorem B2273285 : Blo 354756 2273285 := bstep (se 4 (by rfl) ⟨213120, by rfl⟩ : syracuseStep 2273285 = 426241) B426241
theorem B405523 : Blo 354756 405523 := bstep (se 1 (by rfl) ⟨304142, by rfl⟩ : syracuseStep 405523 = 608285) B608285
theorem B536609 : Blo 354756 536609 := bstep (se 2 (by rfl) ⟨201228, by rfl⟩ : syracuseStep 536609 = 402457) B402457
theorem B602147 : Blo 354756 602147 := bstep (se 1 (by rfl) ⟨451610, by rfl⟩ : syracuseStep 602147 = 903221) B903221
theorem B536627 : Blo 354756 536627 := bstep (se 1 (by rfl) ⟨402470, by rfl⟩ : syracuseStep 536627 = 804941) B804941
theorem B536657 : Blo 354756 536657 := bstep (se 2 (by rfl) ⟨201246, by rfl⟩ : syracuseStep 536657 = 402493) B402493
theorem B536675 : Blo 354756 536675 := bstep (se 1 (by rfl) ⟨402506, by rfl⟩ : syracuseStep 536675 = 805013) B805013
theorem B536705 : Blo 354756 536705 := bstep (se 2 (by rfl) ⟨201264, by rfl⟩ : syracuseStep 536705 = 402529) B402529
theorem B536723 : Blo 354756 536723 := bstep (se 1 (by rfl) ⟨402542, by rfl⟩ : syracuseStep 536723 = 805085) B805085
theorem B602275 : Blo 354756 602275 := bstep (se 1 (by rfl) ⟨451706, by rfl⟩ : syracuseStep 602275 = 903413) B903413
theorem B536753 : Blo 354756 536753 := bstep (se 2 (by rfl) ⟨201282, by rfl⟩ : syracuseStep 536753 = 402565) B402565
theorem B4894901 : Blo 354756 4894901 := bstep (se 5 (by rfl) ⟨229448, by rfl⟩ : syracuseStep 4894901 = 458897) B458897
theorem B569539 : Blo 354756 569539 := bstep (se 1 (by rfl) ⟨427154, by rfl⟩ : syracuseStep 569539 = 854309) B854309
theorem B536771 : Blo 354756 536771 := bstep (se 1 (by rfl) ⟨402578, by rfl⟩ : syracuseStep 536771 = 805157) B805157
theorem B798929 : Blo 354756 798929 := bstep (se 2 (by rfl) ⟨299598, by rfl⟩ : syracuseStep 798929 = 599197) B599197
theorem B536801 : Blo 354756 536801 := bstep (se 2 (by rfl) ⟨201300, by rfl⟩ : syracuseStep 536801 = 402601) B402601
theorem B798947 : Blo 354756 798947 := bstep (se 1 (by rfl) ⟨599210, by rfl⟩ : syracuseStep 798947 = 1198421) B1198421
theorem B536819 : Blo 354756 536819 := bstep (se 1 (by rfl) ⟨402614, by rfl⟩ : syracuseStep 536819 = 805229) B805229
theorem B536849 : Blo 354756 536849 := bstep (se 2 (by rfl) ⟨201318, by rfl⟩ : syracuseStep 536849 = 402637) B402637
theorem B536867 : Blo 354756 536867 := bstep (se 1 (by rfl) ⟨402650, by rfl⟩ : syracuseStep 536867 = 805301) B805301
theorem B602417 : Blo 354756 602417 := bstep (se 2 (by rfl) ⟨225906, by rfl⟩ : syracuseStep 602417 = 451813) B451813
theorem B1290545 : Blo 354756 1290545 := bstep (se 2 (by rfl) ⟨483954, by rfl⟩ : syracuseStep 1290545 = 967909) B967909
theorem B536897 : Blo 354756 536897 := bstep (se 2 (by rfl) ⟨201336, by rfl⟩ : syracuseStep 536897 = 402673) B402673
theorem B536915 : Blo 354756 536915 := bstep (se 1 (by rfl) ⟨402686, by rfl⟩ : syracuseStep 536915 = 805373) B805373
theorem B536945 : Blo 354756 536945 := bstep (se 2 (by rfl) ⟨201354, by rfl⟩ : syracuseStep 536945 = 402709) B402709
theorem B536963 : Blo 354756 536963 := bstep (se 1 (by rfl) ⟨402722, by rfl⟩ : syracuseStep 536963 = 805445) B805445
theorem B536993 : Blo 354756 536993 := bstep (se 2 (by rfl) ⟨201372, by rfl⟩ : syracuseStep 536993 = 402745) B402745
theorem B602545 : Blo 354756 602545 := bstep (se 2 (by rfl) ⟨225954, by rfl⟩ : syracuseStep 602545 = 451909) B451909
theorem B537011 : Blo 354756 537011 := bstep (se 1 (by rfl) ⟨402758, by rfl⟩ : syracuseStep 537011 = 805517) B805517
theorem B537041 : Blo 354756 537041 := bstep (se 2 (by rfl) ⟨201390, by rfl⟩ : syracuseStep 537041 = 402781) B402781
theorem B602579 : Blo 354756 602579 := bstep (se 1 (by rfl) ⟨451934, by rfl⟩ : syracuseStep 602579 = 903869) B903869
theorem B537059 : Blo 354756 537059 := bstep (se 1 (by rfl) ⟨402794, by rfl⟩ : syracuseStep 537059 = 805589) B805589
theorem B799217 : Blo 354756 799217 := bstep (se 2 (by rfl) ⟨299706, by rfl⟩ : syracuseStep 799217 = 599413) B599413
theorem B537089 : Blo 354756 537089 := bstep (se 2 (by rfl) ⟨201408, by rfl⟩ : syracuseStep 537089 = 402817) B402817
theorem B799235 : Blo 354756 799235 := bstep (se 1 (by rfl) ⟨599426, by rfl⟩ : syracuseStep 799235 = 1198853) B1198853
theorem B2241037 : Blo 354756 2241037 := bstep (se 3 (by rfl) ⟨420194, by rfl⟩ : syracuseStep 2241037 = 840389) B840389
theorem B537107 : Blo 354756 537107 := bstep (se 1 (by rfl) ⟨402830, by rfl⟩ : syracuseStep 537107 = 805661) B805661
theorem B537137 : Blo 354756 537137 := bstep (se 2 (by rfl) ⟨201426, by rfl⟩ : syracuseStep 537137 = 402853) B402853
theorem B537155 : Blo 354756 537155 := bstep (se 1 (by rfl) ⟨402866, by rfl⟩ : syracuseStep 537155 = 805733) B805733
theorem B1356365 : Blo 354756 1356365 := bstep (se 3 (by rfl) ⟨254318, by rfl⟩ : syracuseStep 1356365 = 508637) B508637
theorem B602707 : Blo 354756 602707 := bstep (se 1 (by rfl) ⟨452030, by rfl⟩ : syracuseStep 602707 = 904061) B904061
theorem B537185 : Blo 354756 537185 := bstep (se 2 (by rfl) ⟨201444, by rfl⟩ : syracuseStep 537185 = 402889) B402889
theorem B1225325 : Blo 354756 1225325 := bstep (se 3 (by rfl) ⟨229748, by rfl⟩ : syracuseStep 1225325 = 459497) B459497
theorem B537203 : Blo 354756 537203 := bstep (se 1 (by rfl) ⟨402902, by rfl⟩ : syracuseStep 537203 = 805805) B805805
theorem B537233 : Blo 354756 537233 := bstep (se 2 (by rfl) ⟨201462, by rfl⟩ : syracuseStep 537233 = 402925) B402925
theorem B537251 : Blo 354756 537251 := bstep (se 1 (by rfl) ⟨402938, by rfl⟩ : syracuseStep 537251 = 805877) B805877
theorem B537281 : Blo 354756 537281 := bstep (se 2 (by rfl) ⟨201480, by rfl⟩ : syracuseStep 537281 = 402961) B402961
theorem B537299 : Blo 354756 537299 := bstep (se 1 (by rfl) ⟨402974, by rfl⟩ : syracuseStep 537299 = 805949) B805949
theorem B602849 : Blo 354756 602849 := bstep (se 2 (by rfl) ⟨226068, by rfl⟩ : syracuseStep 602849 = 452137) B452137
theorem B537329 : Blo 354756 537329 := bstep (se 2 (by rfl) ⟨201498, by rfl⟩ : syracuseStep 537329 = 402997) B402997
theorem B537347 : Blo 354756 537347 := bstep (se 1 (by rfl) ⟨403010, by rfl⟩ : syracuseStep 537347 = 806021) B806021
theorem B799505 : Blo 354756 799505 := bstep (se 2 (by rfl) ⟨299814, by rfl⟩ : syracuseStep 799505 = 599629) B599629
theorem B537377 : Blo 354756 537377 := bstep (se 2 (by rfl) ⟨201516, by rfl⟩ : syracuseStep 537377 = 403033) B403033
theorem B799523 : Blo 354756 799523 := bstep (se 1 (by rfl) ⟨599642, by rfl⟩ : syracuseStep 799523 = 1199285) B1199285
theorem B537395 : Blo 354756 537395 := bstep (se 1 (by rfl) ⟨403046, by rfl⟩ : syracuseStep 537395 = 806093) B806093
theorem B537425 : Blo 354756 537425 := bstep (se 2 (by rfl) ⟨201534, by rfl⟩ : syracuseStep 537425 = 403069) B403069
theorem B602977 : Blo 354756 602977 := bstep (se 2 (by rfl) ⟨226116, by rfl⟩ : syracuseStep 602977 = 452233) B452233
theorem B537443 : Blo 354756 537443 := bstep (se 1 (by rfl) ⟨403082, by rfl⟩ : syracuseStep 537443 = 806165) B806165
theorem B537473 : Blo 354756 537473 := bstep (se 2 (by rfl) ⟨201552, by rfl⟩ : syracuseStep 537473 = 403105) B403105
theorem B603011 : Blo 354756 603011 := bstep (se 1 (by rfl) ⟨452258, by rfl⟩ : syracuseStep 603011 = 904517) B904517
theorem B570257 : Blo 354756 570257 := bstep (se 2 (by rfl) ⟨213846, by rfl⟩ : syracuseStep 570257 = 427693) B427693
theorem B537491 : Blo 354756 537491 := bstep (se 1 (by rfl) ⟨403118, by rfl⟩ : syracuseStep 537491 = 806237) B806237
theorem B537521 : Blo 354756 537521 := bstep (se 2 (by rfl) ⟨201570, by rfl⟩ : syracuseStep 537521 = 403141) B403141
theorem B537539 : Blo 354756 537539 := bstep (se 1 (by rfl) ⟨403154, by rfl⟩ : syracuseStep 537539 = 806309) B806309
theorem B2569157 : Blo 354756 2569157 := bstep (se 4 (by rfl) ⟨240858, by rfl⟩ : syracuseStep 2569157 = 481717) B481717
theorem B537569 : Blo 354756 537569 := bstep (se 2 (by rfl) ⟨201588, by rfl⟩ : syracuseStep 537569 = 403177) B403177
theorem B537587 : Blo 354756 537587 := bstep (se 1 (by rfl) ⟨403190, by rfl⟩ : syracuseStep 537587 = 806381) B806381
theorem B603139 : Blo 354756 603139 := bstep (se 1 (by rfl) ⟨452354, by rfl⟩ : syracuseStep 603139 = 904709) B904709
theorem B537617 : Blo 354756 537617 := bstep (se 2 (by rfl) ⟨201606, by rfl⟩ : syracuseStep 537617 = 403213) B403213
theorem B537635 : Blo 354756 537635 := bstep (se 1 (by rfl) ⟨403226, by rfl⟩ : syracuseStep 537635 = 806453) B806453
theorem B799793 : Blo 354756 799793 := bstep (se 2 (by rfl) ⟨299922, by rfl⟩ : syracuseStep 799793 = 599845) B599845
theorem B537665 : Blo 354756 537665 := bstep (se 2 (by rfl) ⟨201624, by rfl⟩ : syracuseStep 537665 = 403249) B403249
theorem B799811 : Blo 354756 799811 := bstep (se 1 (by rfl) ⟨599858, by rfl⟩ : syracuseStep 799811 = 1199717) B1199717
theorem B570449 : Blo 354756 570449 := bstep (se 2 (by rfl) ⟨213918, by rfl⟩ : syracuseStep 570449 = 427837) B427837
theorem B537683 : Blo 354756 537683 := bstep (se 1 (by rfl) ⟨403262, by rfl⟩ : syracuseStep 537683 = 806525) B806525
theorem B537713 : Blo 354756 537713 := bstep (se 2 (by rfl) ⟨201642, by rfl⟩ : syracuseStep 537713 = 403285) B403285
theorem B537731 : Blo 354756 537731 := bstep (se 1 (by rfl) ⟨403298, by rfl⟩ : syracuseStep 537731 = 806597) B806597
theorem B603281 : Blo 354756 603281 := bstep (se 2 (by rfl) ⟨226230, by rfl⟩ : syracuseStep 603281 = 452461) B452461
theorem B537761 : Blo 354756 537761 := bstep (se 2 (by rfl) ⟨201660, by rfl⟩ : syracuseStep 537761 = 403321) B403321
theorem B537779 : Blo 354756 537779 := bstep (se 1 (by rfl) ⟨403334, by rfl⟩ : syracuseStep 537779 = 806669) B806669
theorem B570577 : Blo 354756 570577 := bstep (se 2 (by rfl) ⟨213966, by rfl⟩ : syracuseStep 570577 = 427933) B427933
theorem B537809 : Blo 354756 537809 := bstep (se 2 (by rfl) ⟨201678, by rfl⟩ : syracuseStep 537809 = 403357) B403357
theorem B537827 : Blo 354756 537827 := bstep (se 1 (by rfl) ⟨403370, by rfl⟩ : syracuseStep 537827 = 806741) B806741
theorem B537857 : Blo 354756 537857 := bstep (se 2 (by rfl) ⟨201696, by rfl⟩ : syracuseStep 537857 = 403393) B403393
theorem B603409 : Blo 354756 603409 := bstep (se 2 (by rfl) ⟨226278, by rfl⟩ : syracuseStep 603409 = 452557) B452557
theorem B537875 : Blo 354756 537875 := bstep (se 1 (by rfl) ⟨403406, by rfl⟩ : syracuseStep 537875 = 806813) B806813
theorem B537905 : Blo 354756 537905 := bstep (se 2 (by rfl) ⟨201714, by rfl⟩ : syracuseStep 537905 = 403429) B403429
theorem B1815857 : Blo 354756 1815857 := bstep (se 2 (by rfl) ⟨680946, by rfl⟩ : syracuseStep 1815857 = 1361893) B1361893
theorem B603443 : Blo 354756 603443 := bstep (se 1 (by rfl) ⟨452582, by rfl⟩ : syracuseStep 603443 = 905165) B905165
theorem B537923 : Blo 354756 537923 := bstep (se 1 (by rfl) ⟨403442, by rfl⟩ : syracuseStep 537923 = 806885) B806885
theorem B800081 : Blo 354756 800081 := bstep (se 2 (by rfl) ⟨300030, by rfl⟩ : syracuseStep 800081 = 600061) B600061
theorem B537953 : Blo 354756 537953 := bstep (se 2 (by rfl) ⟨201732, by rfl⟩ : syracuseStep 537953 = 403465) B403465
theorem B800099 : Blo 354756 800099 := bstep (se 1 (by rfl) ⟨600074, by rfl⟩ : syracuseStep 800099 = 1200149) B1200149
theorem B537971 : Blo 354756 537971 := bstep (se 1 (by rfl) ⟨403478, by rfl⟩ : syracuseStep 537971 = 806957) B806957
theorem B538001 : Blo 354756 538001 := bstep (se 2 (by rfl) ⟨201750, by rfl⟩ : syracuseStep 538001 = 403501) B403501
theorem B538019 : Blo 354756 538019 := bstep (se 1 (by rfl) ⟨403514, by rfl⟩ : syracuseStep 538019 = 807029) B807029
theorem B603571 : Blo 354756 603571 := bstep (se 1 (by rfl) ⟨452678, by rfl⟩ : syracuseStep 603571 = 905357) B905357
theorem B538049 : Blo 354756 538049 := bstep (se 2 (by rfl) ⟨201768, by rfl⟩ : syracuseStep 538049 = 403537) B403537
theorem B538067 : Blo 354756 538067 := bstep (se 1 (by rfl) ⟨403550, by rfl⟩ : syracuseStep 538067 = 807101) B807101
theorem B538097 : Blo 354756 538097 := bstep (se 2 (by rfl) ⟨201786, by rfl⟩ : syracuseStep 538097 = 403573) B403573
theorem B538115 : Blo 354756 538115 := bstep (se 1 (by rfl) ⟨403586, by rfl⟩ : syracuseStep 538115 = 807173) B807173
theorem B2078243 : Blo 354756 2078243 := bstep (se 1 (by rfl) ⟨1558682, by rfl⟩ : syracuseStep 2078243 = 3117365) B3117365
theorem B603713 : Blo 354756 603713 := bstep (se 2 (by rfl) ⟨226392, by rfl⟩ : syracuseStep 603713 = 452785) B452785
theorem B800369 : Blo 354756 800369 := bstep (se 2 (by rfl) ⟨300138, by rfl⟩ : syracuseStep 800369 = 600277) B600277
theorem B800387 : Blo 354756 800387 := bstep (se 1 (by rfl) ⟨600290, by rfl⟩ : syracuseStep 800387 = 1200581) B1200581
theorem B603841 : Blo 354756 603841 := bstep (se 2 (by rfl) ⟨226440, by rfl⟩ : syracuseStep 603841 = 452881) B452881
theorem B603875 : Blo 354756 603875 := bstep (se 1 (by rfl) ⟨452906, by rfl⟩ : syracuseStep 603875 = 905813) B905813
theorem B11024099 : Blo 354756 11024099 := bstep (se 1 (by rfl) ⟨8268074, by rfl⟩ : syracuseStep 11024099 = 16536149) B16536149
theorem B898897 : Blo 354756 898897 := bstep (se 2 (by rfl) ⟨337086, by rfl⟩ : syracuseStep 898897 = 674173) B674173
theorem B571217 : Blo 354756 571217 := bstep (se 2 (by rfl) ⟨214206, by rfl⟩ : syracuseStep 571217 = 428413) B428413
theorem B604003 : Blo 354756 604003 := bstep (se 1 (by rfl) ⟨453002, by rfl⟩ : syracuseStep 604003 = 906005) B906005
theorem B800657 : Blo 354756 800657 := bstep (se 2 (by rfl) ⟨300246, by rfl⟩ : syracuseStep 800657 = 600493) B600493
theorem B800675 : Blo 354756 800675 := bstep (se 1 (by rfl) ⟨600506, by rfl⟩ : syracuseStep 800675 = 1201013) B1201013
theorem B604145 : Blo 354756 604145 := bstep (se 2 (by rfl) ⟨226554, by rfl⟩ : syracuseStep 604145 = 453109) B453109
theorem B964621 : Blo 354756 964621 := bstep (se 3 (by rfl) ⟨180866, by rfl⟩ : syracuseStep 964621 = 361733) B361733
theorem B505921 : Blo 354756 505921 := bstep (se 2 (by rfl) ⟨189720, by rfl⟩ : syracuseStep 505921 = 379441) B379441
theorem B1226819 : Blo 354756 1226819 := bstep (se 1 (by rfl) ⟨920114, by rfl⟩ : syracuseStep 1226819 = 1840229) B1840229
theorem B899171 : Blo 354756 899171 := bstep (se 1 (by rfl) ⟨674378, by rfl⟩ : syracuseStep 899171 = 1348757) B1348757
theorem B604273 : Blo 354756 604273 := bstep (se 2 (by rfl) ⟨226602, by rfl⟩ : syracuseStep 604273 = 453205) B453205
theorem B604307 : Blo 354756 604307 := bstep (se 1 (by rfl) ⟨453230, by rfl⟩ : syracuseStep 604307 = 906461) B906461
theorem B506017 : Blo 354756 506017 := bstep (se 2 (by rfl) ⟨189756, by rfl⟩ : syracuseStep 506017 = 379513) B379513
theorem B800945 : Blo 354756 800945 := bstep (se 2 (by rfl) ⟨300354, by rfl⟩ : syracuseStep 800945 = 600709) B600709
theorem B800963 : Blo 354756 800963 := bstep (se 1 (by rfl) ⟨600722, by rfl⟩ : syracuseStep 800963 = 1201445) B1201445
theorem B1620209 : Blo 354756 1620209 := bstep (se 2 (by rfl) ⟨607578, by rfl⟩ : syracuseStep 1620209 = 1215157) B1215157
theorem B604435 : Blo 354756 604435 := bstep (se 1 (by rfl) ⟨453326, by rfl⟩ : syracuseStep 604435 = 906653) B906653
theorem B899363 : Blo 354756 899363 := bstep (se 1 (by rfl) ⟨674522, by rfl⟩ : syracuseStep 899363 = 1349045) B1349045
theorem B2472241 : Blo 354756 2472241 := bstep (se 2 (by rfl) ⟨927090, by rfl⟩ : syracuseStep 2472241 = 1854181) B1854181
theorem B1980805 : Blo 354756 1980805 := bstep (se 4 (by rfl) ⟨185700, by rfl⟩ : syracuseStep 1980805 = 371401) B371401
theorem B604577 : Blo 354756 604577 := bstep (se 2 (by rfl) ⟨226716, by rfl⟩ : syracuseStep 604577 = 453433) B453433
theorem B801233 : Blo 354756 801233 := bstep (se 2 (by rfl) ⟨300462, by rfl⟩ : syracuseStep 801233 = 600925) B600925
theorem B801251 : Blo 354756 801251 := bstep (se 1 (by rfl) ⟨600938, by rfl⟩ : syracuseStep 801251 = 1201877) B1201877
theorem B604705 : Blo 354756 604705 := bstep (se 2 (by rfl) ⟨226764, by rfl⟩ : syracuseStep 604705 = 453529) B453529
theorem B604739 : Blo 354756 604739 := bstep (se 1 (by rfl) ⟨453554, by rfl⟩ : syracuseStep 604739 = 907109) B907109
theorem B1030765 : Blo 354756 1030765 := bstep (se 3 (by rfl) ⟨193268, by rfl⟩ : syracuseStep 1030765 = 386537) B386537
theorem B1522289 : Blo 354756 1522289 := bstep (se 2 (by rfl) ⟨570858, by rfl⟩ : syracuseStep 1522289 = 1141717) B1141717
theorem B1358477 : Blo 354756 1358477 := bstep (se 3 (by rfl) ⟨254714, by rfl⟩ : syracuseStep 1358477 = 509429) B509429
theorem B506513 : Blo 354756 506513 := bstep (se 2 (by rfl) ⟨189942, by rfl⟩ : syracuseStep 506513 = 379885) B379885
theorem B604867 : Blo 354756 604867 := bstep (se 1 (by rfl) ⟨453650, by rfl⟩ : syracuseStep 604867 = 907301) B907301
theorem B801521 : Blo 354756 801521 := bstep (se 2 (by rfl) ⟨300570, by rfl⟩ : syracuseStep 801521 = 601141) B601141
theorem B801539 : Blo 354756 801539 := bstep (se 1 (by rfl) ⟨601154, by rfl⟩ : syracuseStep 801539 = 1202309) B1202309
theorem B605009 : Blo 354756 605009 := bstep (se 2 (by rfl) ⟨226878, by rfl⟩ : syracuseStep 605009 = 453757) B453757
theorem B605137 : Blo 354756 605137 := bstep (se 2 (by rfl) ⟨226926, by rfl⟩ : syracuseStep 605137 = 453853) B453853
theorem B605171 : Blo 354756 605171 := bstep (se 1 (by rfl) ⟨453878, by rfl⟩ : syracuseStep 605171 = 907757) B907757
theorem B801809 : Blo 354756 801809 := bstep (se 2 (by rfl) ⟨300678, by rfl⟩ : syracuseStep 801809 = 601357) B601357
theorem B801827 : Blo 354756 801827 := bstep (se 1 (by rfl) ⟨601370, by rfl⟩ : syracuseStep 801827 = 1202741) B1202741
theorem B605299 : Blo 354756 605299 := bstep (se 1 (by rfl) ⟨453974, by rfl⟩ : syracuseStep 605299 = 907949) B907949
theorem B408739 : Blo 354756 408739 := bstep (se 1 (by rfl) ⟨306554, by rfl⟩ : syracuseStep 408739 = 613109) B613109
theorem B900305 : Blo 354756 900305 := bstep (se 2 (by rfl) ⟨337614, by rfl⟩ : syracuseStep 900305 = 675229) B675229
theorem B572627 : Blo 354756 572627 := bstep (se 1 (by rfl) ⟨429470, by rfl⟩ : syracuseStep 572627 = 858941) B858941
theorem B539875 : Blo 354756 539875 := bstep (se 1 (by rfl) ⟨404906, by rfl⟩ : syracuseStep 539875 = 809813) B809813
theorem B900355 : Blo 354756 900355 := bstep (se 1 (by rfl) ⟨675266, by rfl⟩ : syracuseStep 900355 = 1350533) B1350533
theorem B802097 : Blo 354756 802097 := bstep (se 2 (by rfl) ⟨300786, by rfl⟩ : syracuseStep 802097 = 601573) B601573
theorem B802115 : Blo 354756 802115 := bstep (se 1 (by rfl) ⟨601586, by rfl⟩ : syracuseStep 802115 = 1203173) B1203173
theorem B507217 : Blo 354756 507217 := bstep (se 2 (by rfl) ⟨190206, by rfl⟩ : syracuseStep 507217 = 380413) B380413
theorem B572755 : Blo 354756 572755 := bstep (se 1 (by rfl) ⟨429566, by rfl⟩ : syracuseStep 572755 = 859133) B859133
theorem B900497 : Blo 354756 900497 := bstep (se 2 (by rfl) ⟨337686, by rfl⟩ : syracuseStep 900497 = 675373) B675373
theorem B1359281 : Blo 354756 1359281 := bstep (se 2 (by rfl) ⟨509730, by rfl⟩ : syracuseStep 1359281 = 1019461) B1019461
theorem B2276849 : Blo 354756 2276849 := bstep (se 2 (by rfl) ⟨853818, by rfl⟩ : syracuseStep 2276849 = 1707637) B1707637
theorem B507379 : Blo 354756 507379 := bstep (se 1 (by rfl) ⟨380534, by rfl⟩ : syracuseStep 507379 = 761069) B761069
theorem B802385 : Blo 354756 802385 := bstep (se 2 (by rfl) ⟨300894, by rfl⟩ : syracuseStep 802385 = 601789) B601789
theorem B507475 : Blo 354756 507475 := bstep (se 1 (by rfl) ⟨380606, by rfl⟩ : syracuseStep 507475 = 761213) B761213
theorem B802403 : Blo 354756 802403 := bstep (se 1 (by rfl) ⟨601802, by rfl⟩ : syracuseStep 802403 = 1203605) B1203605
theorem B1523555 : Blo 354756 1523555 := bstep (se 1 (by rfl) ⟨1142666, by rfl⟩ : syracuseStep 1523555 = 2285333) B2285333
theorem B802673 : Blo 354756 802673 := bstep (se 2 (by rfl) ⟨301002, by rfl⟩ : syracuseStep 802673 = 602005) B602005
theorem B573313 : Blo 354756 573313 := bstep (se 2 (by rfl) ⟨214992, by rfl⟩ : syracuseStep 573313 = 429985) B429985
theorem B802691 : Blo 354756 802691 := bstep (se 1 (by rfl) ⟨602018, by rfl⟩ : syracuseStep 802691 = 1204037) B1204037
theorem B507971 : Blo 354756 507971 := bstep (se 1 (by rfl) ⟨380978, by rfl⟩ : syracuseStep 507971 = 761957) B761957
theorem B1359949 : Blo 354756 1359949 := bstep (se 3 (by rfl) ⟨254990, by rfl⟩ : syracuseStep 1359949 = 509981) B509981
theorem B9748621 : Blo 354756 9748621 := bstep (se 3 (by rfl) ⟨1827866, by rfl⟩ : syracuseStep 9748621 = 3655733) B3655733
theorem B802961 : Blo 354756 802961 := bstep (se 2 (by rfl) ⟨301110, by rfl⟩ : syracuseStep 802961 = 602221) B602221
theorem B802979 : Blo 354756 802979 := bstep (se 1 (by rfl) ⟨602234, by rfl⟩ : syracuseStep 802979 = 1204469) B1204469
theorem B966829 : Blo 354756 966829 := bstep (se 3 (by rfl) ⟨181280, by rfl⟩ : syracuseStep 966829 = 362561) B362561
theorem B966979 : Blo 354756 966979 := bstep (se 1 (by rfl) ⟨725234, by rfl⟩ : syracuseStep 966979 = 1450469) B1450469
theorem B901489 : Blo 354756 901489 := bstep (se 2 (by rfl) ⟨338058, by rfl⟩ : syracuseStep 901489 = 676117) B676117
theorem B541043 : Blo 354756 541043 := bstep (se 1 (by rfl) ⟨405782, by rfl⟩ : syracuseStep 541043 = 811565) B811565
theorem B1622435 : Blo 354756 1622435 := bstep (se 1 (by rfl) ⟨1216826, by rfl⟩ : syracuseStep 1622435 = 2433653) B2433653
theorem B803249 : Blo 354756 803249 := bstep (se 2 (by rfl) ⟨301218, by rfl⟩ : syracuseStep 803249 = 602437) B602437
theorem B803267 : Blo 354756 803267 := bstep (se 1 (by rfl) ⟨602450, by rfl⟩ : syracuseStep 803267 = 1204901) B1204901
theorem B573985 : Blo 354756 573985 := bstep (se 2 (by rfl) ⟨215244, by rfl⟩ : syracuseStep 573985 = 430489) B430489
theorem B901763 : Blo 354756 901763 := bstep (se 1 (by rfl) ⟨676322, by rfl⟩ : syracuseStep 901763 = 1352645) B1352645
theorem B508609 : Blo 354756 508609 := bstep (se 2 (by rfl) ⟨190728, by rfl⟩ : syracuseStep 508609 = 381457) B381457
theorem B803537 : Blo 354756 803537 := bstep (se 2 (by rfl) ⟨301326, by rfl⟩ : syracuseStep 803537 = 602653) B602653
theorem B803555 : Blo 354756 803555 := bstep (se 1 (by rfl) ⟨602666, by rfl⟩ : syracuseStep 803555 = 1205333) B1205333
theorem B901955 : Blo 354756 901955 := bstep (se 1 (by rfl) ⟨676466, by rfl⟩ : syracuseStep 901955 = 1352933) B1352933
theorem B1360739 : Blo 354756 1360739 := bstep (se 1 (by rfl) ⟨1020554, by rfl⟩ : syracuseStep 1360739 = 2041109) B2041109
theorem B2278307 : Blo 354756 2278307 := bstep (se 1 (by rfl) ⟨1708730, by rfl⟩ : syracuseStep 2278307 = 3417461) B3417461
theorem B803825 : Blo 354756 803825 := bstep (se 2 (by rfl) ⟨301434, by rfl⟩ : syracuseStep 803825 = 602869) B602869
theorem B803843 : Blo 354756 803843 := bstep (se 1 (by rfl) ⟨602882, by rfl⟩ : syracuseStep 803843 = 1205765) B1205765
theorem B508945 : Blo 354756 508945 := bstep (se 2 (by rfl) ⟨190854, by rfl⟩ : syracuseStep 508945 = 381709) B381709
theorem B2049101 : Blo 354756 2049101 := bstep (se 3 (by rfl) ⟨384206, by rfl⟩ : syracuseStep 2049101 = 768413) B768413
theorem B607409 : Blo 354756 607409 := bstep (se 2 (by rfl) ⟨227778, by rfl⟩ : syracuseStep 607409 = 455557) B455557
theorem B804113 : Blo 354756 804113 := bstep (se 2 (by rfl) ⟨301542, by rfl⟩ : syracuseStep 804113 = 603085) B603085
theorem B804131 : Blo 354756 804131 := bstep (se 1 (by rfl) ⟨603098, by rfl⟩ : syracuseStep 804131 = 1206197) B1206197
theorem B1361393 : Blo 354756 1361393 := bstep (se 2 (by rfl) ⟨510522, by rfl⟩ : syracuseStep 1361393 = 1021045) B1021045
theorem B804401 : Blo 354756 804401 := bstep (se 2 (by rfl) ⟨301650, by rfl⟩ : syracuseStep 804401 = 603301) B603301
theorem B804419 : Blo 354756 804419 := bstep (se 1 (by rfl) ⟨603314, by rfl⟩ : syracuseStep 804419 = 1206629) B1206629
theorem B509537 : Blo 354756 509537 := bstep (se 2 (by rfl) ⟨191076, by rfl⟩ : syracuseStep 509537 = 382153) B382153
theorem B1197773 : Blo 354756 1197773 := bstep (se 3 (by rfl) ⟨224582, by rfl⟩ : syracuseStep 1197773 = 449165) B449165
theorem B902897 : Blo 354756 902897 := bstep (se 2 (by rfl) ⟨338586, by rfl⟩ : syracuseStep 902897 = 677173) B677173
theorem B1197827 : Blo 354756 1197827 := bstep (se 1 (by rfl) ⟨898370, by rfl⟩ : syracuseStep 1197827 = 1796741) B1796741
theorem B2443013 : Blo 354756 2443013 := bstep (se 4 (by rfl) ⟨229032, by rfl⟩ : syracuseStep 2443013 = 458065) B458065
theorem B902947 : Blo 354756 902947 := bstep (se 1 (by rfl) ⟨677210, by rfl⟩ : syracuseStep 902947 = 1354421) B1354421
theorem B804689 : Blo 354756 804689 := bstep (se 2 (by rfl) ⟨301758, by rfl⟩ : syracuseStep 804689 = 603517) B603517
theorem B804707 : Blo 354756 804707 := bstep (se 1 (by rfl) ⟨603530, by rfl⟩ : syracuseStep 804707 = 1207061) B1207061
theorem B903089 : Blo 354756 903089 := bstep (se 2 (by rfl) ⟨338658, by rfl⟩ : syracuseStep 903089 = 677317) B677317
theorem B1198097 : Blo 354756 1198097 := bstep (se 2 (by rfl) ⟨449286, by rfl⟩ : syracuseStep 1198097 = 898573) B898573
theorem B804977 : Blo 354756 804977 := bstep (se 2 (by rfl) ⟨301866, by rfl⟩ : syracuseStep 804977 = 603733) B603733
theorem B510067 : Blo 354756 510067 := bstep (se 1 (by rfl) ⟨382550, by rfl⟩ : syracuseStep 510067 = 765101) B765101
theorem B804995 : Blo 354756 804995 := bstep (se 1 (by rfl) ⟨603746, by rfl⟩ : syracuseStep 804995 = 1207493) B1207493
theorem B2050211 : Blo 354756 2050211 := bstep (se 1 (by rfl) ⟨1537658, by rfl⟩ : syracuseStep 2050211 = 3075317) B3075317
theorem B805265 : Blo 354756 805265 := bstep (se 2 (by rfl) ⟨301974, by rfl⟩ : syracuseStep 805265 = 603949) B603949
theorem B805283 : Blo 354756 805283 := bstep (se 1 (by rfl) ⟨603962, by rfl⟩ : syracuseStep 805283 = 1207925) B1207925
theorem B510403 : Blo 354756 510403 := bstep (se 1 (by rfl) ⟨382802, by rfl⟩ : syracuseStep 510403 = 765605) B765605
theorem B674257 : Blo 354756 674257 := bstep (se 2 (by rfl) ⟨252846, by rfl⟩ : syracuseStep 674257 = 505693) B505693
theorem B608723 : Blo 354756 608723 := bstep (se 1 (by rfl) ⟨456542, by rfl⟩ : syracuseStep 608723 = 913085) B913085
theorem B1198637 : Blo 354756 1198637 := bstep (se 3 (by rfl) ⟨224744, by rfl⟩ : syracuseStep 1198637 = 449489) B449489
theorem B1198691 : Blo 354756 1198691 := bstep (se 1 (by rfl) ⟨899018, by rfl⟩ : syracuseStep 1198691 = 1798037) B1798037
theorem B608867 : Blo 354756 608867 := bstep (se 1 (by rfl) ⟨456650, by rfl⟩ : syracuseStep 608867 = 913301) B913301
theorem B805553 : Blo 354756 805553 := bstep (se 2 (by rfl) ⟨302082, by rfl⟩ : syracuseStep 805553 = 604165) B604165
theorem B805571 : Blo 354756 805571 := bstep (se 1 (by rfl) ⟨604178, by rfl⟩ : syracuseStep 805571 = 1208357) B1208357
theorem B379667 : Blo 354756 379667 := bstep (se 1 (by rfl) ⟨284750, by rfl⟩ : syracuseStep 379667 = 569501) B569501
theorem B674659 : Blo 354756 674659 := bstep (se 1 (by rfl) ⟨505994, by rfl⟩ : syracuseStep 674659 = 1011989) B1011989
theorem B1198961 : Blo 354756 1198961 := bstep (se 2 (by rfl) ⟨449610, by rfl⟩ : syracuseStep 1198961 = 899221) B899221
theorem B674705 : Blo 354756 674705 := bstep (se 2 (by rfl) ⟨253014, by rfl⟩ : syracuseStep 674705 = 506029) B506029
theorem B904081 : Blo 354756 904081 := bstep (se 2 (by rfl) ⟨339030, by rfl⟩ : syracuseStep 904081 = 678061) B678061
theorem B1100749 : Blo 354756 1100749 := bstep (se 3 (by rfl) ⟨206390, by rfl⟩ : syracuseStep 1100749 = 412781) B412781
theorem B642001 : Blo 354756 642001 := bstep (se 2 (by rfl) ⟨240750, by rfl⟩ : syracuseStep 642001 = 481501) B481501
theorem B805841 : Blo 354756 805841 := bstep (se 2 (by rfl) ⟨302190, by rfl⟩ : syracuseStep 805841 = 604381) B604381
theorem B805859 : Blo 354756 805859 := bstep (se 1 (by rfl) ⟨604394, by rfl⟩ : syracuseStep 805859 = 1208789) B1208789
theorem B1428515 : Blo 354756 1428515 := bstep (se 1 (by rfl) ⟨1071386, by rfl⟩ : syracuseStep 1428515 = 2142773) B2142773
theorem B904355 : Blo 354756 904355 := bstep (se 1 (by rfl) ⟨678266, by rfl⟩ : syracuseStep 904355 = 1356533) B1356533
theorem B674993 : Blo 354756 674993 := bstep (se 2 (by rfl) ⟨253122, by rfl⟩ : syracuseStep 674993 = 506245) B506245
theorem B806129 : Blo 354756 806129 := bstep (se 2 (by rfl) ⟨302298, by rfl⟩ : syracuseStep 806129 = 604597) B604597
theorem B1232131 : Blo 354756 1232131 := bstep (se 1 (by rfl) ⟨924098, by rfl⟩ : syracuseStep 1232131 = 1848197) B1848197
theorem B806147 : Blo 354756 806147 := bstep (se 1 (by rfl) ⟨604610, by rfl⟩ : syracuseStep 806147 = 1209221) B1209221
theorem B904547 : Blo 354756 904547 := bstep (se 1 (by rfl) ⟨678410, by rfl⟩ : syracuseStep 904547 = 1356821) B1356821
theorem B1658225 : Blo 354756 1658225 := bstep (se 2 (by rfl) ⟨621834, by rfl⟩ : syracuseStep 1658225 = 1243669) B1243669
theorem B1199501 : Blo 354756 1199501 := bstep (se 3 (by rfl) ⟨224906, by rfl⟩ : syracuseStep 1199501 = 449813) B449813
theorem B1199555 : Blo 354756 1199555 := bstep (se 1 (by rfl) ⟨899666, by rfl⟩ : syracuseStep 1199555 = 1799333) B1799333
theorem B1527245 : Blo 354756 1527245 := bstep (se 3 (by rfl) ⟨286358, by rfl⟩ : syracuseStep 1527245 = 572717) B572717
theorem B642563 : Blo 354756 642563 := bstep (se 1 (by rfl) ⟨481922, by rfl⟩ : syracuseStep 642563 = 963845) B963845
theorem B2280973 : Blo 354756 2280973 := bstep (se 3 (by rfl) ⟨427682, by rfl⟩ : syracuseStep 2280973 = 855365) B855365
theorem B806417 : Blo 354756 806417 := bstep (se 2 (by rfl) ⟨302406, by rfl⟩ : syracuseStep 806417 = 604813) B604813
theorem B413203 : Blo 354756 413203 := bstep (se 1 (by rfl) ⟨309902, by rfl⟩ : syracuseStep 413203 = 619805) B619805
theorem B806435 : Blo 354756 806435 := bstep (se 1 (by rfl) ⟨604826, by rfl⟩ : syracuseStep 806435 = 1209653) B1209653
theorem B1199825 : Blo 354756 1199825 := bstep (se 2 (by rfl) ⟨449934, by rfl⟩ : syracuseStep 1199825 = 899869) B899869
theorem B806705 : Blo 354756 806705 := bstep (se 2 (by rfl) ⟨302514, by rfl⟩ : syracuseStep 806705 = 605029) B605029
theorem B806723 : Blo 354756 806723 := bstep (se 1 (by rfl) ⟨605042, by rfl⟩ : syracuseStep 806723 = 1210085) B1210085
theorem B675715 : Blo 354756 675715 := bstep (se 1 (by rfl) ⟨506786, by rfl⟩ : syracuseStep 675715 = 1013573) B1013573
theorem B8802325 : Blo 354756 8802325 := bstep (se 6 (by rfl) ⟨206304, by rfl⟩ : syracuseStep 8802325 = 412609) B412609
theorem B806993 : Blo 354756 806993 := bstep (se 2 (by rfl) ⟨302622, by rfl⟩ : syracuseStep 806993 = 605245) B605245
theorem B807011 : Blo 354756 807011 := bstep (se 1 (by rfl) ⟨605258, by rfl⟩ : syracuseStep 807011 = 1210517) B1210517
theorem B610481 : Blo 354756 610481 := bstep (se 2 (by rfl) ⟨228930, by rfl⟩ : syracuseStep 610481 = 457861) B457861
theorem B9752773 : Blo 354756 9752773 := bstep (se 4 (by rfl) ⟨914322, by rfl⟩ : syracuseStep 9752773 = 1828645) B1828645
theorem B1200365 : Blo 354756 1200365 := bstep (se 3 (by rfl) ⟨225068, by rfl⟩ : syracuseStep 1200365 = 450137) B450137
theorem B905489 : Blo 354756 905489 := bstep (se 2 (by rfl) ⟨339558, by rfl⟩ : syracuseStep 905489 = 679117) B679117
theorem B1200419 : Blo 354756 1200419 := bstep (se 1 (by rfl) ⟨900314, by rfl⟩ : syracuseStep 1200419 = 1800629) B1800629
theorem B676163 : Blo 354756 676163 := bstep (se 1 (by rfl) ⟨507122, by rfl⟩ : syracuseStep 676163 = 1014245) B1014245
theorem B905539 : Blo 354756 905539 := bstep (se 1 (by rfl) ⟨679154, by rfl⟩ : syracuseStep 905539 = 1358309) B1358309
theorem B905681 : Blo 354756 905681 := bstep (se 2 (by rfl) ⟨339630, by rfl⟩ : syracuseStep 905681 = 679261) B679261
theorem B643601 : Blo 354756 643601 := bstep (se 2 (by rfl) ⟨241350, by rfl⟩ : syracuseStep 643601 = 482701) B482701
theorem B1200689 : Blo 354756 1200689 := bstep (se 2 (by rfl) ⟨450258, by rfl⟩ : syracuseStep 1200689 = 900517) B900517
theorem B676451 : Blo 354756 676451 := bstep (se 1 (by rfl) ⟨507338, by rfl⟩ : syracuseStep 676451 = 1014677) B1014677
theorem B381683 : Blo 354756 381683 := bstep (se 1 (by rfl) ⟨286262, by rfl⟩ : syracuseStep 381683 = 572525) B572525
theorem B4051781 : Blo 354756 4051781 := bstep (se 4 (by rfl) ⟨379854, by rfl⟩ : syracuseStep 4051781 = 759709) B759709
theorem B1201229 : Blo 354756 1201229 := bstep (se 3 (by rfl) ⟨225230, by rfl⟩ : syracuseStep 1201229 = 450461) B450461
theorem B1201283 : Blo 354756 1201283 := bstep (se 1 (by rfl) ⟨900962, by rfl⟩ : syracuseStep 1201283 = 1801925) B1801925
theorem B644465 : Blo 354756 644465 := bstep (se 2 (by rfl) ⟨241674, by rfl⟩ : syracuseStep 644465 = 483349) B483349
theorem B1201553 : Blo 354756 1201553 := bstep (se 2 (by rfl) ⟨450582, by rfl⟩ : syracuseStep 1201553 = 901165) B901165
theorem B906673 : Blo 354756 906673 := bstep (se 2 (by rfl) ⟨340002, by rfl⟩ : syracuseStep 906673 = 680005) B680005
theorem B2708963 : Blo 354756 2708963 := bstep (se 1 (by rfl) ⟨2031722, by rfl⟩ : syracuseStep 2708963 = 4063445) B4063445
theorem B579059 : Blo 354756 579059 := bstep (se 1 (by rfl) ⟨434294, by rfl⟩ : syracuseStep 579059 = 868589) B868589
theorem B677393 : Blo 354756 677393 := bstep (se 2 (by rfl) ⟨254022, by rfl⟩ : syracuseStep 677393 = 508045) B508045
theorem B906947 : Blo 354756 906947 := bstep (se 1 (by rfl) ⟨680210, by rfl⟩ : syracuseStep 906947 = 1360421) B1360421
theorem B382691 : Blo 354756 382691 := bstep (se 1 (by rfl) ⟨287018, by rfl⟩ : syracuseStep 382691 = 574037) B574037
theorem B907139 : Blo 354756 907139 := bstep (se 1 (by rfl) ⟨680354, by rfl⟩ : syracuseStep 907139 = 1360709) B1360709
theorem B1202093 : Blo 354756 1202093 := bstep (se 3 (by rfl) ⟨225392, by rfl⟩ : syracuseStep 1202093 = 450785) B450785
theorem B1202147 : Blo 354756 1202147 := bstep (se 1 (by rfl) ⟨901610, by rfl⟩ : syracuseStep 1202147 = 1803221) B1803221
theorem B2021381 : Blo 354756 2021381 := bstep (se 4 (by rfl) ⟨189504, by rfl⟩ : syracuseStep 2021381 = 379009) B379009
theorem B1202417 : Blo 354756 1202417 := bstep (se 2 (by rfl) ⟨450906, by rfl⟩ : syracuseStep 1202417 = 901813) B901813
theorem B678289 : Blo 354756 678289 := bstep (se 2 (by rfl) ⟨254358, by rfl⟩ : syracuseStep 678289 = 508717) B508717
theorem B1530353 : Blo 354756 1530353 := bstep (se 2 (by rfl) ⟨573882, by rfl⟩ : syracuseStep 1530353 = 1147765) B1147765
theorem B449059 : Blo 354756 449059 := bstep (se 1 (by rfl) ⟨336794, by rfl⟩ : syracuseStep 449059 = 673589) B673589
theorem B678449 : Blo 354756 678449 := bstep (se 2 (by rfl) ⟨254418, by rfl⟩ : syracuseStep 678449 = 508837) B508837
theorem B1137233 : Blo 354756 1137233 := bstep (se 2 (by rfl) ⟨426462, by rfl⟩ : syracuseStep 1137233 = 852925) B852925
theorem B449155 : Blo 354756 449155 := bstep (se 1 (by rfl) ⟨336866, by rfl⟩ : syracuseStep 449155 = 673733) B673733
theorem B1137361 : Blo 354756 1137361 := bstep (se 2 (by rfl) ⟨426510, by rfl⟩ : syracuseStep 1137361 = 853021) B853021
theorem B514769 : Blo 354756 514769 := bstep (se 2 (by rfl) ⟨193038, by rfl⟩ : syracuseStep 514769 = 386077) B386077
theorem B1202957 : Blo 354756 1202957 := bstep (se 3 (by rfl) ⟨225554, by rfl⟩ : syracuseStep 1202957 = 451109) B451109
theorem B809777 : Blo 354756 809777 := bstep (se 2 (by rfl) ⟨303666, by rfl⟩ : syracuseStep 809777 = 607333) B607333
theorem B908081 : Blo 354756 908081 := bstep (se 2 (by rfl) ⟨340530, by rfl⟩ : syracuseStep 908081 = 681061) B681061
theorem B1203011 : Blo 354756 1203011 := bstep (se 1 (by rfl) ⟨902258, by rfl⟩ : syracuseStep 1203011 = 1804517) B1804517
theorem B3431267 : Blo 354756 3431267 := bstep (se 1 (by rfl) ⟨2573450, by rfl⟩ : syracuseStep 3431267 = 5146901) B5146901
theorem B646051 : Blo 354756 646051 := bstep (se 1 (by rfl) ⟨484538, by rfl⟩ : syracuseStep 646051 = 969077) B969077
theorem B678851 : Blo 354756 678851 := bstep (se 1 (by rfl) ⟨509138, by rfl⟩ : syracuseStep 678851 = 1018277) B1018277
theorem B1137617 : Blo 354756 1137617 := bstep (se 2 (by rfl) ⟨426606, by rfl⟩ : syracuseStep 1137617 = 853213) B853213
theorem B1203281 : Blo 354756 1203281 := bstep (se 2 (by rfl) ⟨451230, by rfl⟩ : syracuseStep 1203281 = 902461) B902461
theorem B449651 : Blo 354756 449651 := bstep (se 1 (by rfl) ⟨337238, by rfl⟩ : syracuseStep 449651 = 674477) B674477
theorem B1531021 : Blo 354756 1531021 := bstep (se 3 (by rfl) ⟨287066, by rfl⟩ : syracuseStep 1531021 = 574133) B574133
theorem B482593 : Blo 354756 482593 := bstep (se 2 (by rfl) ⟨180972, by rfl⟩ : syracuseStep 482593 = 361945) B361945
theorem B482755 : Blo 354756 482755 := bstep (se 1 (by rfl) ⟨362066, by rfl⟩ : syracuseStep 482755 = 724133) B724133
theorem B2481677 : Blo 354756 2481677 := bstep (se 3 (by rfl) ⟨465314, by rfl⟩ : syracuseStep 2481677 = 930629) B930629
theorem B1203821 : Blo 354756 1203821 := bstep (se 3 (by rfl) ⟨225716, by rfl⟩ : syracuseStep 1203821 = 451433) B451433
theorem B1203875 : Blo 354756 1203875 := bstep (se 1 (by rfl) ⟨902906, by rfl⟩ : syracuseStep 1203875 = 1805813) B1805813
theorem B483041 : Blo 354756 483041 := bstep (se 2 (by rfl) ⟨181140, by rfl⟩ : syracuseStep 483041 = 362281) B362281
theorem B1531619 : Blo 354756 1531619 := bstep (se 1 (by rfl) ⟨1148714, by rfl⟩ : syracuseStep 1531619 = 2297429) B2297429
theorem B810755 : Blo 354756 810755 := bstep (se 1 (by rfl) ⟨608066, by rfl⟩ : syracuseStep 810755 = 1216133) B1216133
theorem B450355 : Blo 354756 450355 := bstep (se 1 (by rfl) ⟨337766, by rfl⟩ : syracuseStep 450355 = 675533) B675533
theorem B679747 : Blo 354756 679747 := bstep (se 1 (by rfl) ⟨509810, by rfl⟩ : syracuseStep 679747 = 1019621) B1019621
theorem B1925005 : Blo 354756 1925005 := bstep (se 3 (by rfl) ⟨360938, by rfl⟩ : syracuseStep 1925005 = 721877) B721877
theorem B450451 : Blo 354756 450451 := bstep (se 1 (by rfl) ⟨337838, by rfl⟩ : syracuseStep 450451 = 675677) B675677
theorem B1204145 : Blo 354756 1204145 := bstep (se 2 (by rfl) ⟨451554, by rfl⟩ : syracuseStep 1204145 = 903109) B903109
theorem B679907 : Blo 354756 679907 := bstep (se 1 (by rfl) ⟨509930, by rfl⟩ : syracuseStep 679907 = 1019861) B1019861
theorem B1466545 : Blo 354756 1466545 := bstep (se 2 (by rfl) ⟨549954, by rfl⟩ : syracuseStep 1466545 = 1099909) B1099909
theorem B450947 : Blo 354756 450947 := bstep (se 1 (by rfl) ⟨338210, by rfl⟩ : syracuseStep 450947 = 676421) B676421
theorem B1204685 : Blo 354756 1204685 := bstep (se 3 (by rfl) ⟨225878, by rfl⟩ : syracuseStep 1204685 = 451757) B451757
theorem B1204739 : Blo 354756 1204739 := bstep (se 1 (by rfl) ⟨903554, by rfl⟩ : syracuseStep 1204739 = 1807109) B1807109
theorem B1139309 : Blo 354756 1139309 := bstep (se 3 (by rfl) ⟨213620, by rfl⟩ : syracuseStep 1139309 = 427241) B427241
theorem B1205009 : Blo 354756 1205009 := bstep (se 2 (by rfl) ⟨451878, by rfl⟩ : syracuseStep 1205009 = 903757) B903757
theorem B1925957 : Blo 354756 1925957 := bstep (se 4 (by rfl) ⟨180558, by rfl⟩ : syracuseStep 1925957 = 361117) B361117
theorem B680977 : Blo 354756 680977 := bstep (se 2 (by rfl) ⟨255366, by rfl⟩ : syracuseStep 680977 = 510733) B510733
theorem B451651 : Blo 354756 451651 := bstep (se 1 (by rfl) ⟨338738, by rfl⟩ : syracuseStep 451651 = 677477) B677477
theorem B451747 : Blo 354756 451747 := bstep (se 1 (by rfl) ⟨338810, by rfl⟩ : syracuseStep 451747 = 677621) B677621
theorem B9233635 : Blo 354756 9233635 := bstep (se 1 (by rfl) ⟨6925226, by rfl⟩ : syracuseStep 9233635 = 13850453) B13850453
theorem B1205549 : Blo 354756 1205549 := bstep (se 3 (by rfl) ⟨226040, by rfl⟩ : syracuseStep 1205549 = 452081) B452081
theorem B910673 : Blo 354756 910673 := bstep (se 2 (by rfl) ⟨341502, by rfl⟩ : syracuseStep 910673 = 683005) B683005
theorem B1205603 : Blo 354756 1205603 := bstep (se 1 (by rfl) ⟨904202, by rfl⟩ : syracuseStep 1205603 = 1808405) B1808405
theorem B1140077 : Blo 354756 1140077 := bstep (se 3 (by rfl) ⟨213764, by rfl⟩ : syracuseStep 1140077 = 427529) B427529
theorem B1369457 : Blo 354756 1369457 := bstep (se 2 (by rfl) ⟨513546, by rfl⟩ : syracuseStep 1369457 = 1027093) B1027093
theorem B1205873 : Blo 354756 1205873 := bstep (se 2 (by rfl) ⟨452202, by rfl⟩ : syracuseStep 1205873 = 904405) B904405
theorem B452243 : Blo 354756 452243 := bstep (se 1 (by rfl) ⟨339182, by rfl⟩ : syracuseStep 452243 = 678365) B678365
theorem B1304333 : Blo 354756 1304333 := bstep (se 3 (by rfl) ⟨244562, by rfl⟩ : syracuseStep 1304333 = 489125) B489125
theorem B1140589 : Blo 354756 1140589 := bstep (se 3 (by rfl) ⟨213860, by rfl⟩ : syracuseStep 1140589 = 427721) B427721
theorem B1206413 : Blo 354756 1206413 := bstep (se 3 (by rfl) ⟨226202, by rfl⟩ : syracuseStep 1206413 = 452405) B452405
theorem B1206467 : Blo 354756 1206467 := bstep (se 1 (by rfl) ⟨904850, by rfl⟩ : syracuseStep 1206467 = 1809701) B1809701
theorem B6187205 : Blo 354756 6187205 := bstep (se 4 (by rfl) ⟨580050, by rfl⟩ : syracuseStep 6187205 = 1160101) B1160101
theorem B452947 : Blo 354756 452947 := bstep (se 1 (by rfl) ⟨339710, by rfl⟩ : syracuseStep 452947 = 679421) B679421
theorem B1141091 : Blo 354756 1141091 := bstep (se 1 (by rfl) ⟨855818, by rfl⟩ : syracuseStep 1141091 = 1711637) B1711637
theorem B453043 : Blo 354756 453043 := bstep (se 1 (by rfl) ⟨339782, by rfl⟩ : syracuseStep 453043 = 679565) B679565
theorem B1206737 : Blo 354756 1206737 := bstep (se 2 (by rfl) ⟨452526, by rfl⟩ : syracuseStep 1206737 = 905053) B905053
theorem B354771 : Blo 354756 354771 := bstep (se 1 (by rfl) ⟨266078, by rfl⟩ : syracuseStep 354771 = 532157) B532157
theorem B354787 : Blo 354756 354787 := bstep (se 1 (by rfl) ⟨266090, by rfl⟩ : syracuseStep 354787 = 532181) B532181
theorem B1796579 : Blo 354756 1796579 := bstep (se 1 (by rfl) ⟨1347434, by rfl⟩ : syracuseStep 1796579 = 2694869) B2694869
theorem B1370609 : Blo 354756 1370609 := bstep (se 2 (by rfl) ⟨513978, by rfl⟩ : syracuseStep 1370609 = 1027957) B1027957
theorem B3434993 : Blo 354756 3434993 := bstep (se 2 (by rfl) ⟨1288122, by rfl⟩ : syracuseStep 3434993 = 2576245) B2576245
theorem B354803 : Blo 354756 354803 := bstep (se 1 (by rfl) ⟨266102, by rfl⟩ : syracuseStep 354803 = 532205) B532205
theorem B354819 : Blo 354756 354819 := bstep (se 1 (by rfl) ⟨266114, by rfl⟩ : syracuseStep 354819 = 532229) B532229
theorem B4057613 : Blo 354756 4057613 := bstep (se 3 (by rfl) ⟨760802, by rfl⟩ : syracuseStep 4057613 = 1521605) B1521605
theorem B354835 : Blo 354756 354835 := bstep (se 1 (by rfl) ⟨266126, by rfl⟩ : syracuseStep 354835 = 532253) B532253
theorem B354851 : Blo 354756 354851 := bstep (se 1 (by rfl) ⟨266138, by rfl⟩ : syracuseStep 354851 = 532277) B532277
theorem B354867 : Blo 354756 354867 := bstep (se 1 (by rfl) ⟨266150, by rfl⟩ : syracuseStep 354867 = 532301) B532301
theorem B354883 : Blo 354756 354883 := bstep (se 1 (by rfl) ⟨266162, by rfl⟩ : syracuseStep 354883 = 532325) B532325
theorem B354899 : Blo 354756 354899 := bstep (se 1 (by rfl) ⟨266174, by rfl⟩ : syracuseStep 354899 = 532349) B532349
theorem B354915 : Blo 354756 354915 := bstep (se 1 (by rfl) ⟨266186, by rfl⟩ : syracuseStep 354915 = 532373) B532373
theorem B354931 : Blo 354756 354931 := bstep (se 1 (by rfl) ⟨266198, by rfl⟩ : syracuseStep 354931 = 532397) B532397
theorem B354947 : Blo 354756 354947 := bstep (se 1 (by rfl) ⟨266210, by rfl⟩ : syracuseStep 354947 = 532421) B532421
theorem B354963 : Blo 354756 354963 := bstep (se 1 (by rfl) ⟨266222, by rfl⟩ : syracuseStep 354963 = 532445) B532445
theorem B354979 : Blo 354756 354979 := bstep (se 1 (by rfl) ⟨266234, by rfl⟩ : syracuseStep 354979 = 532469) B532469
theorem B354995 : Blo 354756 354995 := bstep (se 1 (by rfl) ⟨266246, by rfl⟩ : syracuseStep 354995 = 532493) B532493
theorem B355011 : Blo 354756 355011 := bstep (se 1 (by rfl) ⟨266258, by rfl⟩ : syracuseStep 355011 = 532517) B532517
theorem B2714309 : Blo 354756 2714309 := bstep (se 4 (by rfl) ⟨254466, by rfl⟩ : syracuseStep 2714309 = 508933) B508933
theorem B355027 : Blo 354756 355027 := bstep (se 1 (by rfl) ⟨266270, by rfl⟩ : syracuseStep 355027 = 532541) B532541
theorem B355043 : Blo 354756 355043 := bstep (se 1 (by rfl) ⟨266282, by rfl⟩ : syracuseStep 355043 = 532565) B532565
theorem B355059 : Blo 354756 355059 := bstep (se 1 (by rfl) ⟨266294, by rfl⟩ : syracuseStep 355059 = 532589) B532589
theorem B355075 : Blo 354756 355075 := bstep (se 1 (by rfl) ⟨266306, by rfl⟩ : syracuseStep 355075 = 532613) B532613
theorem B912131 : Blo 354756 912131 := bstep (se 1 (by rfl) ⟨684098, by rfl⟩ : syracuseStep 912131 = 1368197) B1368197
theorem B355091 : Blo 354756 355091 := bstep (se 1 (by rfl) ⟨266318, by rfl⟩ : syracuseStep 355091 = 532637) B532637
theorem B355107 : Blo 354756 355107 := bstep (se 1 (by rfl) ⟨266330, by rfl⟩ : syracuseStep 355107 = 532661) B532661
theorem B355123 : Blo 354756 355123 := bstep (se 1 (by rfl) ⟨266342, by rfl⟩ : syracuseStep 355123 = 532685) B532685
theorem B355139 : Blo 354756 355139 := bstep (se 1 (by rfl) ⟨266354, by rfl⟩ : syracuseStep 355139 = 532709) B532709
theorem B355155 : Blo 354756 355155 := bstep (se 1 (by rfl) ⟨266366, by rfl⟩ : syracuseStep 355155 = 532733) B532733
theorem B1010531 : Blo 354756 1010531 := bstep (se 1 (by rfl) ⟨757898, by rfl⟩ : syracuseStep 1010531 = 1515797) B1515797
theorem B355171 : Blo 354756 355171 := bstep (se 1 (by rfl) ⟨266378, by rfl⟩ : syracuseStep 355171 = 532757) B532757
theorem B355187 : Blo 354756 355187 := bstep (se 1 (by rfl) ⟨266390, by rfl⟩ : syracuseStep 355187 = 532781) B532781
theorem B355203 : Blo 354756 355203 := bstep (se 1 (by rfl) ⟨266402, by rfl⟩ : syracuseStep 355203 = 532805) B532805
theorem B355219 : Blo 354756 355219 := bstep (se 1 (by rfl) ⟨266414, by rfl⟩ : syracuseStep 355219 = 532829) B532829
theorem B355235 : Blo 354756 355235 := bstep (se 1 (by rfl) ⟨266426, by rfl⟩ : syracuseStep 355235 = 532853) B532853
theorem B453539 : Blo 354756 453539 := bstep (se 1 (by rfl) ⟨340154, by rfl⟩ : syracuseStep 453539 = 680309) B680309
theorem B355251 : Blo 354756 355251 := bstep (se 1 (by rfl) ⟨266438, by rfl⟩ : syracuseStep 355251 = 532877) B532877
theorem B355267 : Blo 354756 355267 := bstep (se 1 (by rfl) ⟨266450, by rfl⟩ : syracuseStep 355267 = 532901) B532901
theorem B355283 : Blo 354756 355283 := bstep (se 1 (by rfl) ⟨266462, by rfl⟩ : syracuseStep 355283 = 532925) B532925
theorem B355299 : Blo 354756 355299 := bstep (se 1 (by rfl) ⟨266474, by rfl⟩ : syracuseStep 355299 = 532949) B532949
theorem B1207277 : Blo 354756 1207277 := bstep (se 3 (by rfl) ⟨226364, by rfl⟩ : syracuseStep 1207277 = 452729) B452729
theorem B355315 : Blo 354756 355315 := bstep (se 1 (by rfl) ⟨266486, by rfl⟩ : syracuseStep 355315 = 532973) B532973
theorem B355331 : Blo 354756 355331 := bstep (se 1 (by rfl) ⟨266498, by rfl⟩ : syracuseStep 355331 = 532997) B532997
theorem B355347 : Blo 354756 355347 := bstep (se 1 (by rfl) ⟨266510, by rfl⟩ : syracuseStep 355347 = 533021) B533021
theorem B355363 : Blo 354756 355363 := bstep (se 1 (by rfl) ⟨266522, by rfl⟩ : syracuseStep 355363 = 533045) B533045
theorem B1207331 : Blo 354756 1207331 := bstep (se 1 (by rfl) ⟨905498, by rfl⟩ : syracuseStep 1207331 = 1810997) B1810997
theorem B355379 : Blo 354756 355379 := bstep (se 1 (by rfl) ⟨266534, by rfl⟩ : syracuseStep 355379 = 533069) B533069
theorem B355395 : Blo 354756 355395 := bstep (se 1 (by rfl) ⟨266546, by rfl⟩ : syracuseStep 355395 = 533093) B533093
theorem B355411 : Blo 354756 355411 := bstep (se 1 (by rfl) ⟨266558, by rfl⟩ : syracuseStep 355411 = 533117) B533117
theorem B355427 : Blo 354756 355427 := bstep (se 1 (by rfl) ⟨266570, by rfl⟩ : syracuseStep 355427 = 533141) B533141
theorem B355443 : Blo 354756 355443 := bstep (se 1 (by rfl) ⟨266582, by rfl⟩ : syracuseStep 355443 = 533165) B533165
theorem B355459 : Blo 354756 355459 := bstep (se 1 (by rfl) ⟨266594, by rfl⟩ : syracuseStep 355459 = 533189) B533189
theorem B519313 : Blo 354756 519313 := bstep (se 2 (by rfl) ⟨194742, by rfl⟩ : syracuseStep 519313 = 389485) B389485
theorem B355475 : Blo 354756 355475 := bstep (se 1 (by rfl) ⟨266606, by rfl⟩ : syracuseStep 355475 = 533213) B533213
theorem B355491 : Blo 354756 355491 := bstep (se 1 (by rfl) ⟨266618, by rfl⟩ : syracuseStep 355491 = 533237) B533237
theorem B355507 : Blo 354756 355507 := bstep (se 1 (by rfl) ⟨266630, by rfl⟩ : syracuseStep 355507 = 533261) B533261
theorem B355523 : Blo 354756 355523 := bstep (se 1 (by rfl) ⟨266642, by rfl⟩ : syracuseStep 355523 = 533285) B533285
theorem B355539 : Blo 354756 355539 := bstep (se 1 (by rfl) ⟨266654, by rfl⟩ : syracuseStep 355539 = 533309) B533309
theorem B355555 : Blo 354756 355555 := bstep (se 1 (by rfl) ⟨266666, by rfl⟩ : syracuseStep 355555 = 533333) B533333
theorem B355571 : Blo 354756 355571 := bstep (se 1 (by rfl) ⟨266678, by rfl⟩ : syracuseStep 355571 = 533357) B533357
theorem B355587 : Blo 354756 355587 := bstep (se 1 (by rfl) ⟨266690, by rfl⟩ : syracuseStep 355587 = 533381) B533381
theorem B1797389 : Blo 354756 1797389 := bstep (se 3 (by rfl) ⟨337010, by rfl⟩ : syracuseStep 1797389 = 674021) B674021
theorem B355603 : Blo 354756 355603 := bstep (se 1 (by rfl) ⟨266702, by rfl⟩ : syracuseStep 355603 = 533405) B533405
theorem B355619 : Blo 354756 355619 := bstep (se 1 (by rfl) ⟨266714, by rfl⟩ : syracuseStep 355619 = 533429) B533429
theorem B1207601 : Blo 354756 1207601 := bstep (se 2 (by rfl) ⟨452850, by rfl⟩ : syracuseStep 1207601 = 905701) B905701
theorem B355635 : Blo 354756 355635 := bstep (se 1 (by rfl) ⟨266726, by rfl⟩ : syracuseStep 355635 = 533453) B533453
theorem B355651 : Blo 354756 355651 := bstep (se 1 (by rfl) ⟨266738, by rfl⟩ : syracuseStep 355651 = 533477) B533477
theorem B355667 : Blo 354756 355667 := bstep (se 1 (by rfl) ⟨266750, by rfl⟩ : syracuseStep 355667 = 533501) B533501
theorem B355683 : Blo 354756 355683 := bstep (se 1 (by rfl) ⟨266762, by rfl⟩ : syracuseStep 355683 = 533525) B533525
theorem B355699 : Blo 354756 355699 := bstep (se 1 (by rfl) ⟨266774, by rfl⟩ : syracuseStep 355699 = 533549) B533549
theorem B355715 : Blo 354756 355715 := bstep (se 1 (by rfl) ⟨266786, by rfl⟩ : syracuseStep 355715 = 533573) B533573
theorem B355731 : Blo 354756 355731 := bstep (se 1 (by rfl) ⟨266798, by rfl⟩ : syracuseStep 355731 = 533597) B533597
theorem B355747 : Blo 354756 355747 := bstep (se 1 (by rfl) ⟨266810, by rfl⟩ : syracuseStep 355747 = 533621) B533621
theorem B355763 : Blo 354756 355763 := bstep (se 1 (by rfl) ⟨266822, by rfl⟩ : syracuseStep 355763 = 533645) B533645
theorem B355779 : Blo 354756 355779 := bstep (se 1 (by rfl) ⟨266834, by rfl⟩ : syracuseStep 355779 = 533669) B533669
theorem B355795 : Blo 354756 355795 := bstep (se 1 (by rfl) ⟨266846, by rfl⟩ : syracuseStep 355795 = 533693) B533693
theorem B355811 : Blo 354756 355811 := bstep (se 1 (by rfl) ⟨266858, by rfl⟩ : syracuseStep 355811 = 533717) B533717
theorem B355827 : Blo 354756 355827 := bstep (se 1 (by rfl) ⟨266870, by rfl⟩ : syracuseStep 355827 = 533741) B533741
theorem B355843 : Blo 354756 355843 := bstep (se 1 (by rfl) ⟨266882, by rfl⟩ : syracuseStep 355843 = 533765) B533765
theorem B355859 : Blo 354756 355859 := bstep (se 1 (by rfl) ⟨266894, by rfl⟩ : syracuseStep 355859 = 533789) B533789
theorem B355875 : Blo 354756 355875 := bstep (se 1 (by rfl) ⟨266906, by rfl⟩ : syracuseStep 355875 = 533813) B533813
theorem B355891 : Blo 354756 355891 := bstep (se 1 (by rfl) ⟨266918, by rfl⟩ : syracuseStep 355891 = 533837) B533837
theorem B355907 : Blo 354756 355907 := bstep (se 1 (by rfl) ⟨266930, by rfl⟩ : syracuseStep 355907 = 533861) B533861
theorem B355923 : Blo 354756 355923 := bstep (se 1 (by rfl) ⟨266942, by rfl⟩ : syracuseStep 355923 = 533885) B533885
theorem B355939 : Blo 354756 355939 := bstep (se 1 (by rfl) ⟨266954, by rfl⟩ : syracuseStep 355939 = 533909) B533909
theorem B355955 : Blo 354756 355955 := bstep (se 1 (by rfl) ⟨266966, by rfl⟩ : syracuseStep 355955 = 533933) B533933
theorem B355971 : Blo 354756 355971 := bstep (se 1 (by rfl) ⟨266978, by rfl⟩ : syracuseStep 355971 = 533957) B533957
theorem B355987 : Blo 354756 355987 := bstep (se 1 (by rfl) ⟨266990, by rfl⟩ : syracuseStep 355987 = 533981) B533981
theorem B356003 : Blo 354756 356003 := bstep (se 1 (by rfl) ⟨267002, by rfl⟩ : syracuseStep 356003 = 534005) B534005
theorem B356019 : Blo 354756 356019 := bstep (se 1 (by rfl) ⟨267014, by rfl⟩ : syracuseStep 356019 = 534029) B534029
theorem B356035 : Blo 354756 356035 := bstep (se 1 (by rfl) ⟨267026, by rfl⟩ : syracuseStep 356035 = 534053) B534053
theorem B2027213 : Blo 354756 2027213 := bstep (se 3 (by rfl) ⟨380102, by rfl⟩ : syracuseStep 2027213 = 760205) B760205
theorem B356051 : Blo 354756 356051 := bstep (se 1 (by rfl) ⟨267038, by rfl⟩ : syracuseStep 356051 = 534077) B534077
theorem B356067 : Blo 354756 356067 := bstep (se 1 (by rfl) ⟨267050, by rfl⟩ : syracuseStep 356067 = 534101) B534101
theorem B2289379 : Blo 354756 2289379 := bstep (se 1 (by rfl) ⟨1717034, by rfl⟩ : syracuseStep 2289379 = 3434069) B3434069
theorem B356083 : Blo 354756 356083 := bstep (se 1 (by rfl) ⟨267062, by rfl⟩ : syracuseStep 356083 = 534125) B534125
theorem B356099 : Blo 354756 356099 := bstep (se 1 (by rfl) ⟨267074, by rfl⟩ : syracuseStep 356099 = 534149) B534149
theorem B356115 : Blo 354756 356115 := bstep (se 1 (by rfl) ⟨267086, by rfl⟩ : syracuseStep 356115 = 534173) B534173
theorem B356131 : Blo 354756 356131 := bstep (se 1 (by rfl) ⟨267098, by rfl⟩ : syracuseStep 356131 = 534197) B534197
theorem B356147 : Blo 354756 356147 := bstep (se 1 (by rfl) ⟨267110, by rfl⟩ : syracuseStep 356147 = 534221) B534221
theorem B356163 : Blo 354756 356163 := bstep (se 1 (by rfl) ⟨267122, by rfl⟩ : syracuseStep 356163 = 534245) B534245
theorem B1208141 : Blo 354756 1208141 := bstep (se 3 (by rfl) ⟨226526, by rfl⟩ : syracuseStep 1208141 = 453053) B453053
theorem B356179 : Blo 354756 356179 := bstep (se 1 (by rfl) ⟨267134, by rfl⟩ : syracuseStep 356179 = 534269) B534269
theorem B356195 : Blo 354756 356195 := bstep (se 1 (by rfl) ⟨267146, by rfl⟩ : syracuseStep 356195 = 534293) B534293
theorem B356211 : Blo 354756 356211 := bstep (se 1 (by rfl) ⟨267158, by rfl⟩ : syracuseStep 356211 = 534317) B534317
theorem B356227 : Blo 354756 356227 := bstep (se 1 (by rfl) ⟨267170, by rfl⟩ : syracuseStep 356227 = 534341) B534341
theorem B1208195 : Blo 354756 1208195 := bstep (se 1 (by rfl) ⟨906146, by rfl⟩ : syracuseStep 1208195 = 1812293) B1812293
theorem B356243 : Blo 354756 356243 := bstep (se 1 (by rfl) ⟨267182, by rfl⟩ : syracuseStep 356243 = 534365) B534365
theorem B356259 : Blo 354756 356259 := bstep (se 1 (by rfl) ⟨267194, by rfl⟩ : syracuseStep 356259 = 534389) B534389
theorem B356275 : Blo 354756 356275 := bstep (se 1 (by rfl) ⟨267206, by rfl⟩ : syracuseStep 356275 = 534413) B534413
theorem B356291 : Blo 354756 356291 := bstep (se 1 (by rfl) ⟨267218, by rfl⟩ : syracuseStep 356291 = 534437) B534437
theorem B356307 : Blo 354756 356307 := bstep (se 1 (by rfl) ⟨267230, by rfl⟩ : syracuseStep 356307 = 534461) B534461
theorem B356323 : Blo 354756 356323 := bstep (se 1 (by rfl) ⟨267242, by rfl⟩ : syracuseStep 356323 = 534485) B534485
theorem B356339 : Blo 354756 356339 := bstep (se 1 (by rfl) ⟨267254, by rfl⟩ : syracuseStep 356339 = 534509) B534509
theorem B356355 : Blo 354756 356355 := bstep (se 1 (by rfl) ⟨267266, by rfl⟩ : syracuseStep 356355 = 534533) B534533
theorem B356371 : Blo 354756 356371 := bstep (se 1 (by rfl) ⟨267278, by rfl⟩ : syracuseStep 356371 = 534557) B534557
theorem B356387 : Blo 354756 356387 := bstep (se 1 (by rfl) ⟨267290, by rfl⟩ : syracuseStep 356387 = 534581) B534581
theorem B1011761 : Blo 354756 1011761 := bstep (se 2 (by rfl) ⟨379410, by rfl⟩ : syracuseStep 1011761 = 758821) B758821
theorem B356403 : Blo 354756 356403 := bstep (se 1 (by rfl) ⟨267302, by rfl⟩ : syracuseStep 356403 = 534605) B534605
theorem B356419 : Blo 354756 356419 := bstep (se 1 (by rfl) ⟨267314, by rfl⟩ : syracuseStep 356419 = 534629) B534629
theorem B356435 : Blo 354756 356435 := bstep (se 1 (by rfl) ⟨267326, by rfl⟩ : syracuseStep 356435 = 534653) B534653
theorem B356451 : Blo 354756 356451 := bstep (se 1 (by rfl) ⟨267338, by rfl⟩ : syracuseStep 356451 = 534677) B534677
theorem B356467 : Blo 354756 356467 := bstep (se 1 (by rfl) ⟨267350, by rfl⟩ : syracuseStep 356467 = 534701) B534701
theorem B356483 : Blo 354756 356483 := bstep (se 1 (by rfl) ⟨267362, by rfl⟩ : syracuseStep 356483 = 534725) B534725
theorem B1208465 : Blo 354756 1208465 := bstep (se 2 (by rfl) ⟨453174, by rfl⟩ : syracuseStep 1208465 = 906349) B906349
theorem B356499 : Blo 354756 356499 := bstep (se 1 (by rfl) ⟨267374, by rfl⟩ : syracuseStep 356499 = 534749) B534749
theorem B356515 : Blo 354756 356515 := bstep (se 1 (by rfl) ⟨267386, by rfl⟩ : syracuseStep 356515 = 534773) B534773
theorem B1142947 : Blo 354756 1142947 := bstep (se 1 (by rfl) ⟨857210, by rfl⟩ : syracuseStep 1142947 = 1714421) B1714421
theorem B356531 : Blo 354756 356531 := bstep (se 1 (by rfl) ⟨267398, by rfl⟩ : syracuseStep 356531 = 534797) B534797
theorem B356547 : Blo 354756 356547 := bstep (se 1 (by rfl) ⟨267410, by rfl⟩ : syracuseStep 356547 = 534821) B534821
theorem B356563 : Blo 354756 356563 := bstep (se 1 (by rfl) ⟨267422, by rfl⟩ : syracuseStep 356563 = 534845) B534845
theorem B356579 : Blo 354756 356579 := bstep (se 1 (by rfl) ⟨267434, by rfl⟩ : syracuseStep 356579 = 534869) B534869
theorem B356595 : Blo 354756 356595 := bstep (se 1 (by rfl) ⟨267446, by rfl⟩ : syracuseStep 356595 = 534893) B534893
theorem B356611 : Blo 354756 356611 := bstep (se 1 (by rfl) ⟨267458, by rfl⟩ : syracuseStep 356611 = 534917) B534917
theorem B356627 : Blo 354756 356627 := bstep (se 1 (by rfl) ⟨267470, by rfl⟩ : syracuseStep 356627 = 534941) B534941
theorem B356643 : Blo 354756 356643 := bstep (se 1 (by rfl) ⟨267482, by rfl⟩ : syracuseStep 356643 = 534965) B534965
theorem B356659 : Blo 354756 356659 := bstep (se 1 (by rfl) ⟨267494, by rfl⟩ : syracuseStep 356659 = 534989) B534989
theorem B356675 : Blo 354756 356675 := bstep (se 1 (by rfl) ⟨267506, by rfl⟩ : syracuseStep 356675 = 535013) B535013
theorem B356691 : Blo 354756 356691 := bstep (se 1 (by rfl) ⟨267518, by rfl⟩ : syracuseStep 356691 = 535037) B535037
theorem B356707 : Blo 354756 356707 := bstep (se 1 (by rfl) ⟨267530, by rfl⟩ : syracuseStep 356707 = 535061) B535061
theorem B356723 : Blo 354756 356723 := bstep (se 1 (by rfl) ⟨267542, by rfl⟩ : syracuseStep 356723 = 535085) B535085
theorem B356739 : Blo 354756 356739 := bstep (se 1 (by rfl) ⟨267554, by rfl⟩ : syracuseStep 356739 = 535109) B535109
theorem B356755 : Blo 354756 356755 := bstep (se 1 (by rfl) ⟨267566, by rfl⟩ : syracuseStep 356755 = 535133) B535133
theorem B356771 : Blo 354756 356771 := bstep (se 1 (by rfl) ⟨267578, by rfl⟩ : syracuseStep 356771 = 535157) B535157
theorem B356787 : Blo 354756 356787 := bstep (se 1 (by rfl) ⟨267590, by rfl⟩ : syracuseStep 356787 = 535181) B535181
theorem B356803 : Blo 354756 356803 := bstep (se 1 (by rfl) ⟨267602, by rfl⟩ : syracuseStep 356803 = 535205) B535205
theorem B356819 : Blo 354756 356819 := bstep (se 1 (by rfl) ⟨267614, by rfl⟩ : syracuseStep 356819 = 535229) B535229
theorem B618977 : Blo 354756 618977 := bstep (se 2 (by rfl) ⟨232116, by rfl⟩ : syracuseStep 618977 = 464233) B464233
theorem B356835 : Blo 354756 356835 := bstep (se 1 (by rfl) ⟨267626, by rfl⟩ : syracuseStep 356835 = 535253) B535253
theorem B356851 : Blo 354756 356851 := bstep (se 1 (by rfl) ⟨267638, by rfl⟩ : syracuseStep 356851 = 535277) B535277
theorem B356867 : Blo 354756 356867 := bstep (se 1 (by rfl) ⟨267650, by rfl⟩ : syracuseStep 356867 = 535301) B535301
theorem B356883 : Blo 354756 356883 := bstep (se 1 (by rfl) ⟨267662, by rfl⟩ : syracuseStep 356883 = 535325) B535325
theorem B356899 : Blo 354756 356899 := bstep (se 1 (by rfl) ⟨267674, by rfl⟩ : syracuseStep 356899 = 535349) B535349
theorem B356915 : Blo 354756 356915 := bstep (se 1 (by rfl) ⟨267686, by rfl⟩ : syracuseStep 356915 = 535373) B535373
theorem B356931 : Blo 354756 356931 := bstep (se 1 (by rfl) ⟨267698, by rfl⟩ : syracuseStep 356931 = 535397) B535397
theorem B356947 : Blo 354756 356947 := bstep (se 1 (by rfl) ⟨267710, by rfl⟩ : syracuseStep 356947 = 535421) B535421
theorem B356963 : Blo 354756 356963 := bstep (se 1 (by rfl) ⟨267722, by rfl⟩ : syracuseStep 356963 = 535445) B535445
theorem B1143409 : Blo 354756 1143409 := bstep (se 2 (by rfl) ⟨428778, by rfl⟩ : syracuseStep 1143409 = 857557) B857557
theorem B356979 : Blo 354756 356979 := bstep (se 1 (by rfl) ⟨267734, by rfl⟩ : syracuseStep 356979 = 535469) B535469
theorem B356995 : Blo 354756 356995 := bstep (se 1 (by rfl) ⟨267746, by rfl⟩ : syracuseStep 356995 = 535493) B535493
theorem B357011 : Blo 354756 357011 := bstep (se 1 (by rfl) ⟨267758, by rfl⟩ : syracuseStep 357011 = 535517) B535517
theorem B357027 : Blo 354756 357027 := bstep (se 1 (by rfl) ⟨267770, by rfl⟩ : syracuseStep 357027 = 535541) B535541
theorem B1209005 : Blo 354756 1209005 := bstep (se 3 (by rfl) ⟨226688, by rfl⟩ : syracuseStep 1209005 = 453377) B453377
theorem B357043 : Blo 354756 357043 := bstep (se 1 (by rfl) ⟨267782, by rfl⟩ : syracuseStep 357043 = 535565) B535565
theorem B357059 : Blo 354756 357059 := bstep (se 1 (by rfl) ⟨267794, by rfl⟩ : syracuseStep 357059 = 535589) B535589
theorem B357075 : Blo 354756 357075 := bstep (se 1 (by rfl) ⟨267806, by rfl⟩ : syracuseStep 357075 = 535613) B535613
theorem B357091 : Blo 354756 357091 := bstep (se 1 (by rfl) ⟨267818, by rfl⟩ : syracuseStep 357091 = 535637) B535637
theorem B1209059 : Blo 354756 1209059 := bstep (se 1 (by rfl) ⟨906794, by rfl⟩ : syracuseStep 1209059 = 1813589) B1813589
theorem B914161 : Blo 354756 914161 := bstep (se 2 (by rfl) ⟨342810, by rfl⟩ : syracuseStep 914161 = 685621) B685621
theorem B357107 : Blo 354756 357107 := bstep (se 1 (by rfl) ⟨267830, by rfl⟩ : syracuseStep 357107 = 535661) B535661
theorem B357123 : Blo 354756 357123 := bstep (se 1 (by rfl) ⟨267842, by rfl⟩ : syracuseStep 357123 = 535685) B535685
theorem B357139 : Blo 354756 357139 := bstep (se 1 (by rfl) ⟨267854, by rfl⟩ : syracuseStep 357139 = 535709) B535709
theorem B357155 : Blo 354756 357155 := bstep (se 1 (by rfl) ⟨267866, by rfl⟩ : syracuseStep 357155 = 535733) B535733
theorem B357171 : Blo 354756 357171 := bstep (se 1 (by rfl) ⟨267878, by rfl⟩ : syracuseStep 357171 = 535757) B535757
theorem B357187 : Blo 354756 357187 := bstep (se 1 (by rfl) ⟨267890, by rfl⟩ : syracuseStep 357187 = 535781) B535781
theorem B357203 : Blo 354756 357203 := bstep (se 1 (by rfl) ⟨267902, by rfl⟩ : syracuseStep 357203 = 535805) B535805
theorem B357219 : Blo 354756 357219 := bstep (se 1 (by rfl) ⟨267914, by rfl⟩ : syracuseStep 357219 = 535829) B535829
theorem B357235 : Blo 354756 357235 := bstep (se 1 (by rfl) ⟨267926, by rfl⟩ : syracuseStep 357235 = 535853) B535853
theorem B357251 : Blo 354756 357251 := bstep (se 1 (by rfl) ⟨267938, by rfl⟩ : syracuseStep 357251 = 535877) B535877
theorem B357267 : Blo 354756 357267 := bstep (se 1 (by rfl) ⟨267950, by rfl⟩ : syracuseStep 357267 = 535901) B535901
theorem B357283 : Blo 354756 357283 := bstep (se 1 (by rfl) ⟨267962, by rfl⟩ : syracuseStep 357283 = 535925) B535925
theorem B2290609 : Blo 354756 2290609 := bstep (se 2 (by rfl) ⟨858978, by rfl⟩ : syracuseStep 2290609 = 1717957) B1717957
theorem B357299 : Blo 354756 357299 := bstep (se 1 (by rfl) ⟨267974, by rfl⟩ : syracuseStep 357299 = 535949) B535949
theorem B357315 : Blo 354756 357315 := bstep (se 1 (by rfl) ⟨267986, by rfl⟩ : syracuseStep 357315 = 535973) B535973
theorem B357331 : Blo 354756 357331 := bstep (se 1 (by rfl) ⟨267998, by rfl⟩ : syracuseStep 357331 = 535997) B535997
theorem B357347 : Blo 354756 357347 := bstep (se 1 (by rfl) ⟨268010, by rfl⟩ : syracuseStep 357347 = 536021) B536021
theorem B1209329 : Blo 354756 1209329 := bstep (se 2 (by rfl) ⟨453498, by rfl⟩ : syracuseStep 1209329 = 906997) B906997
theorem B357363 : Blo 354756 357363 := bstep (se 1 (by rfl) ⟨268022, by rfl⟩ : syracuseStep 357363 = 536045) B536045
theorem B357379 : Blo 354756 357379 := bstep (se 1 (by rfl) ⟨268034, by rfl⟩ : syracuseStep 357379 = 536069) B536069
theorem B914449 : Blo 354756 914449 := bstep (se 2 (by rfl) ⟨342918, by rfl⟩ : syracuseStep 914449 = 685837) B685837
theorem B357395 : Blo 354756 357395 := bstep (se 1 (by rfl) ⟨268046, by rfl⟩ : syracuseStep 357395 = 536093) B536093
theorem B357411 : Blo 354756 357411 := bstep (se 1 (by rfl) ⟨268058, by rfl⟩ : syracuseStep 357411 = 536117) B536117
theorem B357427 : Blo 354756 357427 := bstep (se 1 (by rfl) ⟨268070, by rfl⟩ : syracuseStep 357427 = 536141) B536141
theorem B357443 : Blo 354756 357443 := bstep (se 1 (by rfl) ⟨268082, by rfl⟩ : syracuseStep 357443 = 536165) B536165
theorem B357459 : Blo 354756 357459 := bstep (se 1 (by rfl) ⟨268094, by rfl⟩ : syracuseStep 357459 = 536189) B536189
theorem B357475 : Blo 354756 357475 := bstep (se 1 (by rfl) ⟨268106, by rfl⟩ : syracuseStep 357475 = 536213) B536213
theorem B357491 : Blo 354756 357491 := bstep (se 1 (by rfl) ⟨268118, by rfl⟩ : syracuseStep 357491 = 536237) B536237
theorem B357507 : Blo 354756 357507 := bstep (se 1 (by rfl) ⟨268130, by rfl⟩ : syracuseStep 357507 = 536261) B536261
theorem B9270413 : Blo 354756 9270413 := bstep (se 3 (by rfl) ⟨1738202, by rfl⟩ : syracuseStep 9270413 = 3476405) B3476405
theorem B357523 : Blo 354756 357523 := bstep (se 1 (by rfl) ⟨268142, by rfl⟩ : syracuseStep 357523 = 536285) B536285
theorem B357539 : Blo 354756 357539 := bstep (se 1 (by rfl) ⟨268154, by rfl⟩ : syracuseStep 357539 = 536309) B536309
theorem B357555 : Blo 354756 357555 := bstep (se 1 (by rfl) ⟨268166, by rfl⟩ : syracuseStep 357555 = 536333) B536333
theorem B357571 : Blo 354756 357571 := bstep (se 1 (by rfl) ⟨268178, by rfl⟩ : syracuseStep 357571 = 536357) B536357
theorem B357587 : Blo 354756 357587 := bstep (se 1 (by rfl) ⟨268190, by rfl⟩ : syracuseStep 357587 = 536381) B536381
theorem B357603 : Blo 354756 357603 := bstep (se 1 (by rfl) ⟨268202, by rfl⟩ : syracuseStep 357603 = 536405) B536405
theorem B357619 : Blo 354756 357619 := bstep (se 1 (by rfl) ⟨268214, by rfl⟩ : syracuseStep 357619 = 536429) B536429
theorem B357635 : Blo 354756 357635 := bstep (se 1 (by rfl) ⟨268226, by rfl⟩ : syracuseStep 357635 = 536453) B536453
theorem B357651 : Blo 354756 357651 := bstep (se 1 (by rfl) ⟨268238, by rfl⟩ : syracuseStep 357651 = 536477) B536477
theorem B357667 : Blo 354756 357667 := bstep (se 1 (by rfl) ⟨268250, by rfl⟩ : syracuseStep 357667 = 536501) B536501
theorem B357683 : Blo 354756 357683 := bstep (se 1 (by rfl) ⟨268262, by rfl⟩ : syracuseStep 357683 = 536525) B536525
theorem B9172277 : Blo 354756 9172277 := bstep (se 5 (by rfl) ⟨429950, by rfl⟩ : syracuseStep 9172277 = 859901) B859901
theorem B357699 : Blo 354756 357699 := bstep (se 1 (by rfl) ⟨268274, by rfl⟩ : syracuseStep 357699 = 536549) B536549
theorem B357715 : Blo 354756 357715 := bstep (se 1 (by rfl) ⟨268286, by rfl⟩ : syracuseStep 357715 = 536573) B536573
theorem B357731 : Blo 354756 357731 := bstep (se 1 (by rfl) ⟨268298, by rfl⟩ : syracuseStep 357731 = 536597) B536597
theorem B4060529 : Blo 354756 4060529 := bstep (se 2 (by rfl) ⟨1522698, by rfl⟩ : syracuseStep 4060529 = 3045397) B3045397
theorem B357747 : Blo 354756 357747 := bstep (se 1 (by rfl) ⟨268310, by rfl⟩ : syracuseStep 357747 = 536621) B536621
theorem B357763 : Blo 354756 357763 := bstep (se 1 (by rfl) ⟨268322, by rfl⟩ : syracuseStep 357763 = 536645) B536645
theorem B357779 : Blo 354756 357779 := bstep (se 1 (by rfl) ⟨268334, by rfl⟩ : syracuseStep 357779 = 536669) B536669
theorem B357795 : Blo 354756 357795 := bstep (se 1 (by rfl) ⟨268346, by rfl⟩ : syracuseStep 357795 = 536693) B536693
theorem B357811 : Blo 354756 357811 := bstep (se 1 (by rfl) ⟨268358, by rfl⟩ : syracuseStep 357811 = 536717) B536717
theorem B357827 : Blo 354756 357827 := bstep (se 1 (by rfl) ⟨268370, by rfl⟩ : syracuseStep 357827 = 536741) B536741
theorem B357843 : Blo 354756 357843 := bstep (se 1 (by rfl) ⟨268382, by rfl⟩ : syracuseStep 357843 = 536765) B536765
theorem B1013219 : Blo 354756 1013219 := bstep (se 1 (by rfl) ⟨759914, by rfl⟩ : syracuseStep 1013219 = 1519829) B1519829
theorem B357859 : Blo 354756 357859 := bstep (se 1 (by rfl) ⟨268394, by rfl⟩ : syracuseStep 357859 = 536789) B536789
theorem B357875 : Blo 354756 357875 := bstep (se 1 (by rfl) ⟨268406, by rfl⟩ : syracuseStep 357875 = 536813) B536813
theorem B357891 : Blo 354756 357891 := bstep (se 1 (by rfl) ⟨268418, by rfl⟩ : syracuseStep 357891 = 536837) B536837
theorem B1209869 : Blo 354756 1209869 := bstep (se 3 (by rfl) ⟨226850, by rfl⟩ : syracuseStep 1209869 = 453701) B453701
theorem B357907 : Blo 354756 357907 := bstep (se 1 (by rfl) ⟨268430, by rfl⟩ : syracuseStep 357907 = 536861) B536861
theorem B357923 : Blo 354756 357923 := bstep (se 1 (by rfl) ⟨268442, by rfl⟩ : syracuseStep 357923 = 536885) B536885
theorem B1078829 : Blo 354756 1078829 := bstep (se 3 (by rfl) ⟨202280, by rfl⟩ : syracuseStep 1078829 = 404561) B404561
theorem B357939 : Blo 354756 357939 := bstep (se 1 (by rfl) ⟨268454, by rfl⟩ : syracuseStep 357939 = 536909) B536909
theorem B357955 : Blo 354756 357955 := bstep (se 1 (by rfl) ⟨268466, by rfl⟩ : syracuseStep 357955 = 536933) B536933
theorem B1209923 : Blo 354756 1209923 := bstep (se 1 (by rfl) ⟨907442, by rfl⟩ : syracuseStep 1209923 = 1814885) B1814885
theorem B4126277 : Blo 354756 4126277 := bstep (se 4 (by rfl) ⟨386838, by rfl⟩ : syracuseStep 4126277 = 773677) B773677
theorem B357971 : Blo 354756 357971 := bstep (se 1 (by rfl) ⟨268478, by rfl⟩ : syracuseStep 357971 = 536957) B536957
theorem B357987 : Blo 354756 357987 := bstep (se 1 (by rfl) ⟨268490, by rfl⟩ : syracuseStep 357987 = 536981) B536981
theorem B358003 : Blo 354756 358003 := bstep (se 1 (by rfl) ⟨268502, by rfl⟩ : syracuseStep 358003 = 537005) B537005
theorem B358019 : Blo 354756 358019 := bstep (se 1 (by rfl) ⟨268514, by rfl⟩ : syracuseStep 358019 = 537029) B537029
theorem B358035 : Blo 354756 358035 := bstep (se 1 (by rfl) ⟨268526, by rfl⟩ : syracuseStep 358035 = 537053) B537053
theorem B358051 : Blo 354756 358051 := bstep (se 1 (by rfl) ⟨268538, by rfl⟩ : syracuseStep 358051 = 537077) B537077
theorem B358067 : Blo 354756 358067 := bstep (se 1 (by rfl) ⟨268550, by rfl⟩ : syracuseStep 358067 = 537101) B537101
theorem B358083 : Blo 354756 358083 := bstep (se 1 (by rfl) ⟨268562, by rfl⟩ : syracuseStep 358083 = 537125) B537125
theorem B358099 : Blo 354756 358099 := bstep (se 1 (by rfl) ⟨268574, by rfl⟩ : syracuseStep 358099 = 537149) B537149
theorem B358115 : Blo 354756 358115 := bstep (se 1 (by rfl) ⟨268586, by rfl⟩ : syracuseStep 358115 = 537173) B537173
theorem B358131 : Blo 354756 358131 := bstep (se 1 (by rfl) ⟨268598, by rfl⟩ : syracuseStep 358131 = 537197) B537197
theorem B587521 : Blo 354756 587521 := bstep (se 2 (by rfl) ⟨220320, by rfl⟩ : syracuseStep 587521 = 440641) B440641
theorem B358147 : Blo 354756 358147 := bstep (se 1 (by rfl) ⟨268610, by rfl⟩ : syracuseStep 358147 = 537221) B537221
theorem B358163 : Blo 354756 358163 := bstep (se 1 (by rfl) ⟨268622, by rfl⟩ : syracuseStep 358163 = 537245) B537245
theorem B358179 : Blo 354756 358179 := bstep (se 1 (by rfl) ⟨268634, by rfl⟩ : syracuseStep 358179 = 537269) B537269
theorem B358195 : Blo 354756 358195 := bstep (se 1 (by rfl) ⟨268646, by rfl⟩ : syracuseStep 358195 = 537293) B537293
theorem B358211 : Blo 354756 358211 := bstep (se 1 (by rfl) ⟨268658, by rfl⟩ : syracuseStep 358211 = 537317) B537317
theorem B1210193 : Blo 354756 1210193 := bstep (se 2 (by rfl) ⟨453822, by rfl⟩ : syracuseStep 1210193 = 907645) B907645
theorem B358227 : Blo 354756 358227 := bstep (se 1 (by rfl) ⟨268670, by rfl⟩ : syracuseStep 358227 = 537341) B537341
theorem B358243 : Blo 354756 358243 := bstep (se 1 (by rfl) ⟨268682, by rfl⟩ : syracuseStep 358243 = 537365) B537365
theorem B358259 : Blo 354756 358259 := bstep (se 1 (by rfl) ⟨268694, by rfl⟩ : syracuseStep 358259 = 537389) B537389
theorem B358275 : Blo 354756 358275 := bstep (se 1 (by rfl) ⟨268706, by rfl⟩ : syracuseStep 358275 = 537413) B537413
theorem B2029445 : Blo 354756 2029445 := bstep (se 4 (by rfl) ⟨190260, by rfl⟩ : syracuseStep 2029445 = 380521) B380521
theorem B358291 : Blo 354756 358291 := bstep (se 1 (by rfl) ⟨268718, by rfl⟩ : syracuseStep 358291 = 537437) B537437
theorem B358307 : Blo 354756 358307 := bstep (se 1 (by rfl) ⟨268730, by rfl⟩ : syracuseStep 358307 = 537461) B537461
theorem B358323 : Blo 354756 358323 := bstep (se 1 (by rfl) ⟨268742, by rfl⟩ : syracuseStep 358323 = 537485) B537485
theorem B358339 : Blo 354756 358339 := bstep (se 1 (by rfl) ⟨268754, by rfl⟩ : syracuseStep 358339 = 537509) B537509
theorem B358355 : Blo 354756 358355 := bstep (se 1 (by rfl) ⟨268766, by rfl⟩ : syracuseStep 358355 = 537533) B537533
theorem B686051 : Blo 354756 686051 := bstep (se 1 (by rfl) ⟨514538, by rfl⟩ : syracuseStep 686051 = 1029077) B1029077
theorem B358371 : Blo 354756 358371 := bstep (se 1 (by rfl) ⟨268778, by rfl⟩ : syracuseStep 358371 = 537557) B537557
theorem B358387 : Blo 354756 358387 := bstep (se 1 (by rfl) ⟨268790, by rfl⟩ : syracuseStep 358387 = 537581) B537581
theorem B358403 : Blo 354756 358403 := bstep (se 1 (by rfl) ⟨268802, by rfl⟩ : syracuseStep 358403 = 537605) B537605
theorem B358419 : Blo 354756 358419 := bstep (se 1 (by rfl) ⟨268814, by rfl⟩ : syracuseStep 358419 = 537629) B537629
theorem B358435 : Blo 354756 358435 := bstep (se 1 (by rfl) ⟨268826, by rfl⟩ : syracuseStep 358435 = 537653) B537653
theorem B358451 : Blo 354756 358451 := bstep (se 1 (by rfl) ⟨268838, by rfl⟩ : syracuseStep 358451 = 537677) B537677
theorem B358467 : Blo 354756 358467 := bstep (se 1 (by rfl) ⟨268850, by rfl⟩ : syracuseStep 358467 = 537701) B537701
theorem B358483 : Blo 354756 358483 := bstep (se 1 (by rfl) ⟨268862, by rfl⟩ : syracuseStep 358483 = 537725) B537725
theorem B358499 : Blo 354756 358499 := bstep (se 1 (by rfl) ⟨268874, by rfl⟩ : syracuseStep 358499 = 537749) B537749
theorem B1800305 : Blo 354756 1800305 := bstep (se 2 (by rfl) ⟨675114, by rfl⟩ : syracuseStep 1800305 = 1350229) B1350229
theorem B358515 : Blo 354756 358515 := bstep (se 1 (by rfl) ⟨268886, by rfl⟩ : syracuseStep 358515 = 537773) B537773
theorem B358531 : Blo 354756 358531 := bstep (se 1 (by rfl) ⟨268898, by rfl⟩ : syracuseStep 358531 = 537797) B537797
theorem B358547 : Blo 354756 358547 := bstep (se 1 (by rfl) ⟨268910, by rfl⟩ : syracuseStep 358547 = 537821) B537821
theorem B358563 : Blo 354756 358563 := bstep (se 1 (by rfl) ⟨268922, by rfl⟩ : syracuseStep 358563 = 537845) B537845
theorem B358579 : Blo 354756 358579 := bstep (se 1 (by rfl) ⟨268934, by rfl⟩ : syracuseStep 358579 = 537869) B537869
theorem B358595 : Blo 354756 358595 := bstep (se 1 (by rfl) ⟨268946, by rfl⟩ : syracuseStep 358595 = 537893) B537893
theorem B358611 : Blo 354756 358611 := bstep (se 1 (by rfl) ⟨268958, by rfl⟩ : syracuseStep 358611 = 537917) B537917
theorem B358627 : Blo 354756 358627 := bstep (se 1 (by rfl) ⟨268970, by rfl⟩ : syracuseStep 358627 = 537941) B537941
theorem B358643 : Blo 354756 358643 := bstep (se 1 (by rfl) ⟨268982, by rfl⟩ : syracuseStep 358643 = 537965) B537965
theorem B358659 : Blo 354756 358659 := bstep (se 1 (by rfl) ⟨268994, by rfl⟩ : syracuseStep 358659 = 537989) B537989
theorem B1014029 : Blo 354756 1014029 := bstep (se 3 (by rfl) ⟨190130, by rfl⟩ : syracuseStep 1014029 = 380261) B380261
theorem B358675 : Blo 354756 358675 := bstep (se 1 (by rfl) ⟨269006, by rfl⟩ : syracuseStep 358675 = 538013) B538013
theorem B358691 : Blo 354756 358691 := bstep (se 1 (by rfl) ⟨269018, by rfl⟩ : syracuseStep 358691 = 538037) B538037
theorem B358707 : Blo 354756 358707 := bstep (se 1 (by rfl) ⟨269030, by rfl⟩ : syracuseStep 358707 = 538061) B538061
theorem B358723 : Blo 354756 358723 := bstep (se 1 (by rfl) ⟨269042, by rfl⟩ : syracuseStep 358723 = 538085) B538085
theorem B358739 : Blo 354756 358739 := bstep (se 1 (by rfl) ⟨269054, by rfl⟩ : syracuseStep 358739 = 538109) B538109
theorem B358755 : Blo 354756 358755 := bstep (se 1 (by rfl) ⟨269066, by rfl⟩ : syracuseStep 358755 = 538133) B538133
theorem B1210733 : Blo 354756 1210733 := bstep (se 3 (by rfl) ⟨227012, by rfl⟩ : syracuseStep 1210733 = 454025) B454025
theorem B1210787 : Blo 354756 1210787 := bstep (se 1 (by rfl) ⟨908090, by rfl⟩ : syracuseStep 1210787 = 1816181) B1816181
theorem B1014221 : Blo 354756 1014221 := bstep (se 3 (by rfl) ⟨190166, by rfl⟩ : syracuseStep 1014221 = 380333) B380333
theorem B2030129 : Blo 354756 2030129 := bstep (se 2 (by rfl) ⟨761298, by rfl⟩ : syracuseStep 2030129 = 1522597) B1522597
theorem B916049 : Blo 354756 916049 := bstep (se 2 (by rfl) ⟨343518, by rfl⟩ : syracuseStep 916049 = 687037) B687037
theorem B5798627 : Blo 354756 5798627 := bstep (se 1 (by rfl) ⟨4348970, by rfl⟩ : syracuseStep 5798627 = 8697941) B8697941
theorem B1080067 : Blo 354756 1080067 := bstep (se 1 (by rfl) ⟨810050, by rfl⟩ : syracuseStep 1080067 = 1620101) B1620101
theorem B916561 : Blo 354756 916561 := bstep (se 2 (by rfl) ⟨343710, by rfl⟩ : syracuseStep 916561 = 687421) B687421
theorem B1146125 : Blo 354756 1146125 := bstep (se 3 (by rfl) ⟨214898, by rfl⟩ : syracuseStep 1146125 = 429797) B429797
theorem B4423025 : Blo 354756 4423025 := bstep (se 2 (by rfl) ⟨1658634, by rfl⟩ : syracuseStep 4423025 = 3317269) B3317269
theorem B1015213 : Blo 354756 1015213 := bstep (se 3 (by rfl) ⟨190352, by rfl⟩ : syracuseStep 1015213 = 380705) B380705
theorem B3440069 : Blo 354756 3440069 := bstep (se 4 (by rfl) ⟨322506, by rfl⟩ : syracuseStep 3440069 = 645013) B645013
theorem B1801763 : Blo 354756 1801763 := bstep (se 1 (by rfl) ⟨1351322, by rfl⟩ : syracuseStep 1801763 = 2702645) B2702645
theorem B5766709 : Blo 354756 5766709 := bstep (se 5 (by rfl) ⟨270314, by rfl⟩ : syracuseStep 5766709 = 540629) B540629
theorem B917219 : Blo 354756 917219 := bstep (se 1 (by rfl) ⟨687914, by rfl⟩ : syracuseStep 917219 = 1375829) B1375829
theorem B1081297 : Blo 354756 1081297 := bstep (se 2 (by rfl) ⟨405486, by rfl⟩ : syracuseStep 1081297 = 810973) B810973
theorem B2031587 : Blo 354756 2031587 := bstep (se 1 (by rfl) ⟨1523690, by rfl⟩ : syracuseStep 2031587 = 3047381) B3047381
theorem B2752643 : Blo 354756 2752643 := bstep (se 1 (by rfl) ⟨2064482, by rfl⟩ : syracuseStep 2752643 = 4128965) B4128965
theorem B360695 : Blo 354756 360695 := bstep (se 1 (by rfl) ⟨270521, by rfl⟩ : syracuseStep 360695 = 541043) B541043
theorem B786763 : Blo 354756 786763 := bstep (se 1 (by rfl) ⟨590072, by rfl⟩ : syracuseStep 786763 = 1180145) B1180145
theorem B6127973 : Blo 354756 6127973 := bstep (se 4 (by rfl) ⟨574497, by rfl⟩ : syracuseStep 6127973 = 1148995) B1148995
theorem B2753041 : Blo 354756 2753041 := bstep (se 2 (by rfl) ⟨1032390, by rfl⟩ : syracuseStep 2753041 = 2064781) B2064781
theorem B1442393 : Blo 354756 1442393 := bstep (se 2 (by rfl) ⟨540897, by rfl⟩ : syracuseStep 1442393 = 1081795) B1081795
theorem B459595 : Blo 354756 459595 := bstep (se 1 (by rfl) ⟨344696, by rfl⟩ : syracuseStep 459595 = 689393) B689393
theorem B6489011 : Blo 354756 6489011 := bstep (se 1 (by rfl) ⟨4866758, by rfl⟩ : syracuseStep 6489011 = 9733517) B9733517
theorem B1148381 : Blo 354756 1148381 := bstep (se 3 (by rfl) ⟨215321, by rfl⟩ : syracuseStep 1148381 = 430643) B430643
theorem B1803869 : Blo 354756 1803869 := bstep (se 3 (by rfl) ⟨338225, by rfl⟩ : syracuseStep 1803869 = 676451) B676451
theorem B1148509 : Blo 354756 1148509 := bstep (se 3 (by rfl) ⟨215345, by rfl⟩ : syracuseStep 1148509 = 430691) B430691
theorem B1017821 : Blo 354756 1017821 := bstep (se 3 (by rfl) ⟨190841, by rfl⟩ : syracuseStep 1017821 = 381683) B381683
theorem B952343 : Blo 354756 952343 := bstep (se 1 (by rfl) ⟨714257, by rfl⟩ : syracuseStep 952343 = 1428515) B1428515
theorem B1837187 : Blo 354756 1837187 := bstep (se 1 (by rfl) ⟨1377890, by rfl⟩ : syracuseStep 1837187 = 2755781) B2755781
theorem B1018163 : Blo 354756 1018163 := bstep (se 1 (by rfl) ⟨763622, by rfl⟩ : syracuseStep 1018163 = 1527245) B1527245
theorem B428375 : Blo 354756 428375 := bstep (se 1 (by rfl) ⟨321281, by rfl⟩ : syracuseStep 428375 = 642563) B642563
theorem B3869045 : Blo 354756 3869045 := bstep (se 5 (by rfl) ⟨181361, by rfl⟩ : syracuseStep 3869045 = 362723) B362723
theorem B2165123 : Blo 354756 2165123 := bstep (se 1 (by rfl) ⟨1623842, by rfl⟩ : syracuseStep 2165123 = 3247685) B3247685
theorem B2034071 : Blo 354756 2034071 := bstep (se 1 (by rfl) ⟨1525553, by rfl⟩ : syracuseStep 2034071 = 3051107) B3051107
theorem B429067 : Blo 354756 429067 := bstep (se 1 (by rfl) ⟨321800, by rfl⟩ : syracuseStep 429067 = 643601) B643601
theorem B1117363 : Blo 354756 1117363 := bstep (se 1 (by rfl) ⟨838022, by rfl⟩ : syracuseStep 1117363 = 1676045) B1676045
theorem B2559383 : Blo 354756 2559383 := bstep (se 1 (by rfl) ⟨1919537, by rfl⟩ : syracuseStep 2559383 = 3839075) B3839075
theorem B429643 : Blo 354756 429643 := bstep (se 1 (by rfl) ⟨322232, by rfl⟩ : syracuseStep 429643 = 644465) B644465
theorem B1805975 : Blo 354756 1805975 := bstep (se 1 (by rfl) ⟨1354481, by rfl⟩ : syracuseStep 1805975 = 2708963) B2708963
theorem B856001 : Blo 354756 856001 := bstep (se 2 (by rfl) ⟨321000, by rfl⟩ : syracuseStep 856001 = 642001) B642001
theorem B1347587 : Blo 354756 1347587 := bstep (se 1 (by rfl) ⟨1010690, by rfl⟩ : syracuseStep 1347587 = 2021381) B2021381
theorem B3281075 : Blo 354756 3281075 := bstep (se 1 (by rfl) ⟨2460806, by rfl⟩ : syracuseStep 3281075 = 4921613) B4921613
theorem B692417 : Blo 354756 692417 := bstep (se 2 (by rfl) ⟨259656, by rfl⟩ : syracuseStep 692417 = 519313) B519313
theorem B1642841 : Blo 354756 1642841 := bstep (se 2 (by rfl) ⟨616065, by rfl⟩ : syracuseStep 1642841 = 1232131) B1232131
theorem B17305973 : Blo 354756 17305973 := bstep (se 5 (by rfl) ⟨811217, by rfl⟩ : syracuseStep 17305973 = 1622435) B1622435
theorem B758155 : Blo 354756 758155 := bstep (se 1 (by rfl) ⟨568616, by rfl⟩ : syracuseStep 758155 = 1137233) B1137233
theorem B1020509 : Blo 354756 1020509 := bstep (se 3 (by rfl) ⟨191345, by rfl⟩ : syracuseStep 1020509 = 382691) B382691
theorem B758411 : Blo 354756 758411 := bstep (se 1 (by rfl) ⟨568808, by rfl⟩ : syracuseStep 758411 = 1137617) B1137617
theorem B1446673 : Blo 354756 1446673 := bstep (se 2 (by rfl) ⟨542502, by rfl⟩ : syracuseStep 1446673 = 1085005) B1085005
theorem B1020737 : Blo 354756 1020737 := bstep (se 2 (by rfl) ⟨382776, by rfl⟩ : syracuseStep 1020737 = 765553) B765553
theorem B3052505 : Blo 354756 3052505 := bstep (se 2 (by rfl) ⟨1144689, by rfl⟩ : syracuseStep 3052505 = 2289379) B2289379
theorem B4854935 : Blo 354756 4854935 := bstep (se 1 (by rfl) ⟨3641201, by rfl⟩ : syracuseStep 4854935 = 7282403) B7282403
theorem B1021079 : Blo 354756 1021079 := bstep (se 1 (by rfl) ⟨765809, by rfl⟩ : syracuseStep 1021079 = 1531619) B1531619
theorem B11736433 : Blo 354756 11736433 := bstep (se 2 (by rfl) ⟨4401162, by rfl⟩ : syracuseStep 11736433 = 8802325) B8802325
theorem B759385 : Blo 354756 759385 := bstep (se 2 (by rfl) ⟨284769, by rfl⟩ : syracuseStep 759385 = 569539) B569539
theorem B759539 : Blo 354756 759539 := bstep (se 1 (by rfl) ⟨569654, by rfl⟩ : syracuseStep 759539 = 1139309) B1139309
theorem B4888325 : Blo 354756 4888325 := bstep (se 4 (by rfl) ⟨458280, by rfl⟩ : syracuseStep 4888325 = 916561) B916561
theorem B399127 : Blo 354756 399127 := bstep (se 1 (by rfl) ⟨299345, by rfl⟩ : syracuseStep 399127 = 598691) B598691
theorem B1283971 : Blo 354756 1283971 := bstep (se 1 (by rfl) ⟨962978, by rfl⟩ : syracuseStep 1283971 = 1925957) B1925957
theorem B399307 : Blo 354756 399307 := bstep (se 1 (by rfl) ⟨299480, by rfl⟩ : syracuseStep 399307 = 598961) B598961
theorem B399415 : Blo 354756 399415 := bstep (se 1 (by rfl) ⟨299561, by rfl⟩ : syracuseStep 399415 = 599123) B599123
theorem B399595 : Blo 354756 399595 := bstep (se 1 (by rfl) ⟨299696, by rfl⟩ : syracuseStep 399595 = 599393) B599393
theorem B760051 : Blo 354756 760051 := bstep (se 1 (by rfl) ⟨570038, by rfl⟩ : syracuseStep 760051 = 1140077) B1140077
theorem B1218881 : Blo 354756 1218881 := bstep (se 2 (by rfl) ⟨457080, by rfl⟩ : syracuseStep 1218881 = 914161) B914161
theorem B399703 : Blo 354756 399703 := bstep (se 1 (by rfl) ⟨299777, by rfl⟩ : syracuseStep 399703 = 599555) B599555
theorem B399883 : Blo 354756 399883 := bstep (se 1 (by rfl) ⟨299912, by rfl⟩ : syracuseStep 399883 = 599825) B599825
theorem B3054145 : Blo 354756 3054145 := bstep (se 2 (by rfl) ⟨1145304, by rfl⟩ : syracuseStep 3054145 = 2290609) B2290609
theorem B399991 : Blo 354756 399991 := bstep (se 1 (by rfl) ⟨299993, by rfl⟩ : syracuseStep 399991 = 599987) B599987
theorem B1219265 : Blo 354756 1219265 := bstep (se 2 (by rfl) ⟨457224, by rfl⟩ : syracuseStep 1219265 = 914449) B914449
theorem B400171 : Blo 354756 400171 := bstep (se 1 (by rfl) ⟨300128, by rfl⟩ : syracuseStep 400171 = 600257) B600257
theorem B400279 : Blo 354756 400279 := bstep (se 1 (by rfl) ⟨300209, by rfl⟩ : syracuseStep 400279 = 600419) B600419
theorem B760727 : Blo 354756 760727 := bstep (se 1 (by rfl) ⟨570545, by rfl⟩ : syracuseStep 760727 = 1141091) B1141091
theorem B760769 : Blo 354756 760769 := bstep (se 2 (by rfl) ⟨285288, by rfl⟩ : syracuseStep 760769 = 570577) B570577
theorem B1350701 : Blo 354756 1350701 := bstep (se 3 (by rfl) ⟨253256, by rfl⟩ : syracuseStep 1350701 = 506513) B506513
theorem B400459 : Blo 354756 400459 := bstep (se 1 (by rfl) ⟨300344, by rfl⟩ : syracuseStep 400459 = 600689) B600689
theorem B859211 : Blo 354756 859211 := bstep (se 1 (by rfl) ⟨644408, by rfl⟩ : syracuseStep 859211 = 1288817) B1288817
theorem B2038877 : Blo 354756 2038877 := bstep (se 3 (by rfl) ⟨382289, by rfl⟩ : syracuseStep 2038877 = 764579) B764579
theorem B1809539 : Blo 354756 1809539 := bstep (se 1 (by rfl) ⟨1357154, by rfl⟩ : syracuseStep 1809539 = 2714309) B2714309
theorem B400567 : Blo 354756 400567 := bstep (se 1 (by rfl) ⟨300425, by rfl⟩ : syracuseStep 400567 = 600851) B600851
theorem B400747 : Blo 354756 400747 := bstep (se 1 (by rfl) ⟨300560, by rfl⟩ : syracuseStep 400747 = 601121) B601121
theorem B400855 : Blo 354756 400855 := bstep (se 1 (by rfl) ⟨300641, by rfl⟩ : syracuseStep 400855 = 601283) B601283
theorem B401035 : Blo 354756 401035 := bstep (se 1 (by rfl) ⟨300776, by rfl⟩ : syracuseStep 401035 = 601553) B601553
theorem B401143 : Blo 354756 401143 := bstep (se 1 (by rfl) ⟨300857, by rfl⟩ : syracuseStep 401143 = 601715) B601715
theorem B532235 : Blo 354756 532235 := bstep (se 1 (by rfl) ⟨399176, by rfl⟩ : syracuseStep 532235 = 798353) B798353
theorem B532247 : Blo 354756 532247 := bstep (se 1 (by rfl) ⟨399185, by rfl⟩ : syracuseStep 532247 = 798371) B798371
theorem B1351475 : Blo 354756 1351475 := bstep (se 1 (by rfl) ⟨1013606, by rfl⟩ : syracuseStep 1351475 = 2027213) B2027213
theorem B859979 : Blo 354756 859979 := bstep (se 1 (by rfl) ⟨644984, by rfl⟩ : syracuseStep 859979 = 1289969) B1289969
theorem B532313 : Blo 354756 532313 := bstep (se 2 (by rfl) ⟨199617, by rfl⟩ : syracuseStep 532313 = 399235) B399235
theorem B401323 : Blo 354756 401323 := bstep (se 1 (by rfl) ⟨300992, by rfl⟩ : syracuseStep 401323 = 601985) B601985
theorem B532427 : Blo 354756 532427 := bstep (se 1 (by rfl) ⟨399320, by rfl⟩ : syracuseStep 532427 = 798641) B798641
theorem B532439 : Blo 354756 532439 := bstep (se 1 (by rfl) ⟨399329, by rfl⟩ : syracuseStep 532439 = 798659) B798659
theorem B1515523 : Blo 354756 1515523 := bstep (se 1 (by rfl) ⟨1136642, by rfl⟩ : syracuseStep 1515523 = 2273285) B2273285
theorem B1286161 : Blo 354756 1286161 := bstep (se 2 (by rfl) ⟨482310, by rfl⟩ : syracuseStep 1286161 = 964621) B964621
theorem B401431 : Blo 354756 401431 := bstep (se 1 (by rfl) ⟨301073, by rfl⟩ : syracuseStep 401431 = 602147) B602147
theorem B532505 : Blo 354756 532505 := bstep (se 2 (by rfl) ⟨199689, by rfl⟩ : syracuseStep 532505 = 399379) B399379
theorem B532619 : Blo 354756 532619 := bstep (se 1 (by rfl) ⟨399464, by rfl⟩ : syracuseStep 532619 = 798929) B798929
theorem B532631 : Blo 354756 532631 := bstep (se 1 (by rfl) ⟨399473, by rfl⟩ : syracuseStep 532631 = 798947) B798947
theorem B401611 : Blo 354756 401611 := bstep (se 1 (by rfl) ⟨301208, by rfl⟩ : syracuseStep 401611 = 602417) B602417
theorem B860363 : Blo 354756 860363 := bstep (se 1 (by rfl) ⟨645272, by rfl⟩ : syracuseStep 860363 = 1290545) B1290545
theorem B532697 : Blo 354756 532697 := bstep (se 2 (by rfl) ⟨199761, by rfl⟩ : syracuseStep 532697 = 399523) B399523
theorem B401719 : Blo 354756 401719 := bstep (se 1 (by rfl) ⟨301289, by rfl⟩ : syracuseStep 401719 = 602579) B602579
theorem B532811 : Blo 354756 532811 := bstep (se 1 (by rfl) ⟨399608, by rfl⟩ : syracuseStep 532811 = 799217) B799217
theorem B532823 : Blo 354756 532823 := bstep (se 1 (by rfl) ⟨399617, by rfl⟩ : syracuseStep 532823 = 799235) B799235
theorem B5808485 : Blo 354756 5808485 := bstep (se 4 (by rfl) ⟨544545, by rfl⟩ : syracuseStep 5808485 = 1089091) B1089091
theorem B532889 : Blo 354756 532889 := bstep (se 2 (by rfl) ⟨199833, by rfl⟩ : syracuseStep 532889 = 399667) B399667
theorem B401899 : Blo 354756 401899 := bstep (se 1 (by rfl) ⟨301424, by rfl⟩ : syracuseStep 401899 = 602849) B602849
theorem B533003 : Blo 354756 533003 := bstep (se 1 (by rfl) ⟨399752, by rfl⟩ : syracuseStep 533003 = 799505) B799505
theorem B533015 : Blo 354756 533015 := bstep (se 1 (by rfl) ⟨399761, by rfl⟩ : syracuseStep 533015 = 799523) B799523
theorem B402007 : Blo 354756 402007 := bstep (se 1 (by rfl) ⟨301505, by rfl⟩ : syracuseStep 402007 = 603011) B603011
theorem B533081 : Blo 354756 533081 := bstep (se 2 (by rfl) ⟨199905, by rfl⟩ : syracuseStep 533081 = 399811) B399811
theorem B1712771 : Blo 354756 1712771 := bstep (se 1 (by rfl) ⟨1284578, by rfl⟩ : syracuseStep 1712771 = 2569157) B2569157
theorem B533195 : Blo 354756 533195 := bstep (se 1 (by rfl) ⟨399896, by rfl⟩ : syracuseStep 533195 = 799793) B799793
theorem B533207 : Blo 354756 533207 := bstep (se 1 (by rfl) ⟨399905, by rfl⟩ : syracuseStep 533207 = 799811) B799811
theorem B598745 : Blo 354756 598745 := bstep (se 2 (by rfl) ⟨224529, by rfl⟩ : syracuseStep 598745 = 449059) B449059
theorem B402187 : Blo 354756 402187 := bstep (se 1 (by rfl) ⟨301640, by rfl⟩ : syracuseStep 402187 = 603281) B603281
theorem B533273 : Blo 354756 533273 := bstep (se 2 (by rfl) ⟨199977, by rfl⟩ : syracuseStep 533273 = 399955) B399955
theorem B598873 : Blo 354756 598873 := bstep (se 2 (by rfl) ⟨224577, by rfl⟩ : syracuseStep 598873 = 449155) B449155
theorem B402295 : Blo 354756 402295 := bstep (se 1 (by rfl) ⟨301721, by rfl⟩ : syracuseStep 402295 = 603443) B603443
theorem B533387 : Blo 354756 533387 := bstep (se 1 (by rfl) ⟨400040, by rfl⟩ : syracuseStep 533387 = 800081) B800081
theorem B533399 : Blo 354756 533399 := bstep (se 1 (by rfl) ⟨400049, by rfl⟩ : syracuseStep 533399 = 800099) B800099
theorem B1516481 : Blo 354756 1516481 := bstep (se 2 (by rfl) ⟨568680, by rfl⟩ : syracuseStep 1516481 = 1137361) B1137361
theorem B533465 : Blo 354756 533465 := bstep (se 2 (by rfl) ⟨200049, by rfl⟩ : syracuseStep 533465 = 400099) B400099
theorem B1385495 : Blo 354756 1385495 := bstep (se 1 (by rfl) ⟨1039121, by rfl⟩ : syracuseStep 1385495 = 2078243) B2078243
theorem B402475 : Blo 354756 402475 := bstep (se 1 (by rfl) ⟨301856, by rfl⟩ : syracuseStep 402475 = 603713) B603713
theorem B533579 : Blo 354756 533579 := bstep (se 1 (by rfl) ⟨400184, by rfl⟩ : syracuseStep 533579 = 800369) B800369
theorem B533591 : Blo 354756 533591 := bstep (se 1 (by rfl) ⟨400193, by rfl⟩ : syracuseStep 533591 = 800387) B800387
theorem B402583 : Blo 354756 402583 := bstep (se 1 (by rfl) ⟨301937, by rfl⟩ : syracuseStep 402583 = 603875) B603875
theorem B7349399 : Blo 354756 7349399 := bstep (se 1 (by rfl) ⟨5512049, by rfl⟩ : syracuseStep 7349399 = 11024099) B11024099
theorem B533657 : Blo 354756 533657 := bstep (se 2 (by rfl) ⟨200121, by rfl⟩ : syracuseStep 533657 = 400243) B400243
theorem B861401 : Blo 354756 861401 := bstep (se 2 (by rfl) ⟨323025, by rfl⟩ : syracuseStep 861401 = 646051) B646051
theorem B1352963 : Blo 354756 1352963 := bstep (se 1 (by rfl) ⟨1014722, by rfl⟩ : syracuseStep 1352963 = 2029445) B2029445
theorem B533771 : Blo 354756 533771 := bstep (se 1 (by rfl) ⟨400328, by rfl⟩ : syracuseStep 533771 = 800657) B800657
theorem B533783 : Blo 354756 533783 := bstep (se 1 (by rfl) ⟨400337, by rfl⟩ : syracuseStep 533783 = 800675) B800675
theorem B402763 : Blo 354756 402763 := bstep (se 1 (by rfl) ⟨302072, by rfl⟩ : syracuseStep 402763 = 604145) B604145
theorem B533849 : Blo 354756 533849 := bstep (se 2 (by rfl) ⟨200193, by rfl⟩ : syracuseStep 533849 = 400387) B400387
theorem B599447 : Blo 354756 599447 := bstep (se 1 (by rfl) ⟨449585, by rfl⟩ : syracuseStep 599447 = 899171) B899171
theorem B402871 : Blo 354756 402871 := bstep (se 1 (by rfl) ⟨302153, by rfl⟩ : syracuseStep 402871 = 604307) B604307
theorem B533963 : Blo 354756 533963 := bstep (se 1 (by rfl) ⟨400472, by rfl⟩ : syracuseStep 533963 = 800945) B800945
theorem B3253709 : Blo 354756 3253709 := bstep (se 3 (by rfl) ⟨610070, by rfl⟩ : syracuseStep 3253709 = 1220141) B1220141
theorem B533975 : Blo 354756 533975 := bstep (se 1 (by rfl) ⟨400481, by rfl⟩ : syracuseStep 533975 = 800963) B800963
theorem B2041361 : Blo 354756 2041361 := bstep (se 2 (by rfl) ⟨765510, by rfl⟩ : syracuseStep 2041361 = 1531021) B1531021
theorem B599575 : Blo 354756 599575 := bstep (se 1 (by rfl) ⟨449681, by rfl⟩ : syracuseStep 599575 = 899363) B899363
theorem B534041 : Blo 354756 534041 := bstep (se 2 (by rfl) ⟨200265, by rfl⟩ : syracuseStep 534041 = 400531) B400531
theorem B403051 : Blo 354756 403051 := bstep (se 1 (by rfl) ⟨302288, by rfl⟩ : syracuseStep 403051 = 604577) B604577
theorem B534155 : Blo 354756 534155 := bstep (se 1 (by rfl) ⟨400616, by rfl⟩ : syracuseStep 534155 = 801233) B801233
theorem B534167 : Blo 354756 534167 := bstep (se 1 (by rfl) ⟨400625, by rfl⟩ : syracuseStep 534167 = 801251) B801251
theorem B927425 : Blo 354756 927425 := bstep (se 2 (by rfl) ⟨347784, by rfl⟩ : syracuseStep 927425 = 695569) B695569
theorem B1353419 : Blo 354756 1353419 := bstep (se 1 (by rfl) ⟨1015064, by rfl⟩ : syracuseStep 1353419 = 2030129) B2030129
theorem B403159 : Blo 354756 403159 := bstep (se 1 (by rfl) ⟨302369, by rfl⟩ : syracuseStep 403159 = 604739) B604739
theorem B534233 : Blo 354756 534233 := bstep (se 2 (by rfl) ⟨200337, by rfl⟩ : syracuseStep 534233 = 400675) B400675
theorem B763673 : Blo 354756 763673 := bstep (se 2 (by rfl) ⟨286377, by rfl⟩ : syracuseStep 763673 = 572755) B572755
theorem B534347 : Blo 354756 534347 := bstep (se 1 (by rfl) ⟨400760, by rfl⟩ : syracuseStep 534347 = 801521) B801521
theorem B534359 : Blo 354756 534359 := bstep (se 1 (by rfl) ⟨400769, by rfl⟩ : syracuseStep 534359 = 801539) B801539
theorem B403339 : Blo 354756 403339 := bstep (se 1 (by rfl) ⟨302504, by rfl⟩ : syracuseStep 403339 = 605009) B605009
theorem B1353617 : Blo 354756 1353617 := bstep (se 2 (by rfl) ⟨507606, by rfl⟩ : syracuseStep 1353617 = 1015213) B1015213
theorem B534425 : Blo 354756 534425 := bstep (se 2 (by rfl) ⟨200409, by rfl⟩ : syracuseStep 534425 = 400819) B400819
theorem B1288109 : Blo 354756 1288109 := bstep (se 3 (by rfl) ⟨241520, by rfl⟩ : syracuseStep 1288109 = 483041) B483041
theorem B403447 : Blo 354756 403447 := bstep (se 1 (by rfl) ⟨302585, by rfl⟩ : syracuseStep 403447 = 605171) B605171
theorem B534539 : Blo 354756 534539 := bstep (se 1 (by rfl) ⟨400904, by rfl⟩ : syracuseStep 534539 = 801809) B801809
theorem B534551 : Blo 354756 534551 := bstep (se 1 (by rfl) ⟨400913, by rfl⟩ : syracuseStep 534551 = 801827) B801827
theorem B534617 : Blo 354756 534617 := bstep (se 2 (by rfl) ⟨200481, by rfl⟩ : syracuseStep 534617 = 400963) B400963
theorem B600203 : Blo 354756 600203 := bstep (se 1 (by rfl) ⟨450152, by rfl⟩ : syracuseStep 600203 = 900305) B900305
theorem B764083 : Blo 354756 764083 := bstep (se 1 (by rfl) ⟨573062, by rfl⟩ : syracuseStep 764083 = 1146125) B1146125
theorem B534731 : Blo 354756 534731 := bstep (se 1 (by rfl) ⟨401048, by rfl⟩ : syracuseStep 534731 = 802097) B802097
theorem B534743 : Blo 354756 534743 := bstep (se 1 (by rfl) ⟨401057, by rfl⟩ : syracuseStep 534743 = 802115) B802115
theorem B600331 : Blo 354756 600331 := bstep (se 1 (by rfl) ⟨450248, by rfl⟩ : syracuseStep 600331 = 900497) B900497
theorem B534809 : Blo 354756 534809 := bstep (se 2 (by rfl) ⟨200553, by rfl⟩ : syracuseStep 534809 = 401107) B401107
theorem B1517899 : Blo 354756 1517899 := bstep (se 1 (by rfl) ⟨1138424, by rfl⟩ : syracuseStep 1517899 = 2276849) B2276849
theorem B534923 : Blo 354756 534923 := bstep (se 1 (by rfl) ⟨401192, by rfl⟩ : syracuseStep 534923 = 802385) B802385
theorem B534935 : Blo 354756 534935 := bstep (se 1 (by rfl) ⟨401201, by rfl⟩ : syracuseStep 534935 = 802403) B802403
theorem B600473 : Blo 354756 600473 := bstep (se 2 (by rfl) ⟨225177, by rfl⟩ : syracuseStep 600473 = 450355) B450355
theorem B535001 : Blo 354756 535001 := bstep (se 2 (by rfl) ⟨200625, by rfl⟩ : syracuseStep 535001 = 401251) B401251
theorem B764417 : Blo 354756 764417 := bstep (se 2 (by rfl) ⟨286656, by rfl⟩ : syracuseStep 764417 = 573313) B573313
theorem B2566673 : Blo 354756 2566673 := bstep (se 2 (by rfl) ⟨962502, by rfl⟩ : syracuseStep 2566673 = 1925005) B1925005
theorem B600601 : Blo 354756 600601 := bstep (se 2 (by rfl) ⟨225225, by rfl⟩ : syracuseStep 600601 = 450451) B450451
theorem B535115 : Blo 354756 535115 := bstep (se 1 (by rfl) ⟨401336, by rfl⟩ : syracuseStep 535115 = 802673) B802673
theorem B535127 : Blo 354756 535127 := bstep (se 1 (by rfl) ⟨401345, by rfl⟩ : syracuseStep 535127 = 802691) B802691
theorem B1518173 : Blo 354756 1518173 := bstep (se 3 (by rfl) ⟨284657, by rfl⟩ : syracuseStep 1518173 = 569315) B569315
theorem B1354391 : Blo 354756 1354391 := bstep (se 1 (by rfl) ⟨1015793, by rfl⟩ : syracuseStep 1354391 = 2031587) B2031587
theorem B535193 : Blo 354756 535193 := bstep (se 2 (by rfl) ⟨200697, by rfl⟩ : syracuseStep 535193 = 401395) B401395
theorem B535307 : Blo 354756 535307 := bstep (se 1 (by rfl) ⟨401480, by rfl⟩ : syracuseStep 535307 = 802961) B802961
theorem B1813265 : Blo 354756 1813265 := bstep (se 2 (by rfl) ⟨679974, by rfl⟩ : syracuseStep 1813265 = 1359949) B1359949
theorem B535319 : Blo 354756 535319 := bstep (se 1 (by rfl) ⟨401489, by rfl⟩ : syracuseStep 535319 = 802979) B802979
theorem B535385 : Blo 354756 535385 := bstep (se 2 (by rfl) ⟨200769, by rfl⟩ : syracuseStep 535385 = 401539) B401539
theorem B1354589 : Blo 354756 1354589 := bstep (se 3 (by rfl) ⟨253985, by rfl⟩ : syracuseStep 1354589 = 507971) B507971
theorem B1289105 : Blo 354756 1289105 := bstep (se 2 (by rfl) ⟨483414, by rfl⟩ : syracuseStep 1289105 = 966829) B966829
theorem B1813427 : Blo 354756 1813427 := bstep (se 1 (by rfl) ⟨1360070, by rfl⟩ : syracuseStep 1813427 = 2720141) B2720141
theorem B535499 : Blo 354756 535499 := bstep (se 1 (by rfl) ⟨401624, by rfl⟩ : syracuseStep 535499 = 803249) B803249
theorem B535511 : Blo 354756 535511 := bstep (se 1 (by rfl) ⟨401633, by rfl⟩ : syracuseStep 535511 = 803267) B803267
theorem B535577 : Blo 354756 535577 := bstep (se 2 (by rfl) ⟨200841, by rfl⟩ : syracuseStep 535577 = 401683) B401683
theorem B601175 : Blo 354756 601175 := bstep (se 1 (by rfl) ⟨450881, by rfl⟩ : syracuseStep 601175 = 901763) B901763
theorem B1289305 : Blo 354756 1289305 := bstep (se 2 (by rfl) ⟨483489, by rfl⟩ : syracuseStep 1289305 = 966979) B966979
theorem B535691 : Blo 354756 535691 := bstep (se 1 (by rfl) ⟨401768, by rfl⟩ : syracuseStep 535691 = 803537) B803537
theorem B535703 : Blo 354756 535703 := bstep (se 1 (by rfl) ⟨401777, by rfl⟩ : syracuseStep 535703 = 803555) B803555
theorem B601303 : Blo 354756 601303 := bstep (se 1 (by rfl) ⟨450977, by rfl⟩ : syracuseStep 601303 = 901955) B901955
theorem B765143 : Blo 354756 765143 := bstep (se 1 (by rfl) ⟨573857, by rfl⟩ : syracuseStep 765143 = 1147715) B1147715
theorem B535769 : Blo 354756 535769 := bstep (se 2 (by rfl) ⟨200913, by rfl⟩ : syracuseStep 535769 = 401827) B401827
theorem B535883 : Blo 354756 535883 := bstep (se 1 (by rfl) ⟨401912, by rfl⟩ : syracuseStep 535883 = 803825) B803825
theorem B535895 : Blo 354756 535895 := bstep (se 1 (by rfl) ⟨401921, by rfl⟩ : syracuseStep 535895 = 803843) B803843
theorem B535961 : Blo 354756 535961 := bstep (se 2 (by rfl) ⟨200985, by rfl⟩ : syracuseStep 535961 = 401971) B401971
theorem B404939 : Blo 354756 404939 := bstep (se 1 (by rfl) ⟨303704, by rfl⟩ : syracuseStep 404939 = 607409) B607409
theorem B798209 : Blo 354756 798209 := bstep (se 2 (by rfl) ⟨299328, by rfl⟩ : syracuseStep 798209 = 598657) B598657
theorem B2698757 : Blo 354756 2698757 := bstep (se 4 (by rfl) ⟨253008, by rfl⟩ : syracuseStep 2698757 = 506017) B506017
theorem B536075 : Blo 354756 536075 := bstep (se 1 (by rfl) ⟨402056, by rfl⟩ : syracuseStep 536075 = 804113) B804113
theorem B536087 : Blo 354756 536087 := bstep (se 1 (by rfl) ⟨402065, by rfl⟩ : syracuseStep 536087 = 804131) B804131
theorem B536153 : Blo 354756 536153 := bstep (se 2 (by rfl) ⟨201057, by rfl⟩ : syracuseStep 536153 = 402115) B402115
theorem B536267 : Blo 354756 536267 := bstep (se 1 (by rfl) ⟨402200, by rfl⟩ : syracuseStep 536267 = 804401) B804401
theorem B536279 : Blo 354756 536279 := bstep (se 1 (by rfl) ⟨402209, by rfl⟩ : syracuseStep 536279 = 804419) B804419
theorem B798425 : Blo 354756 798425 := bstep (se 2 (by rfl) ⟨299409, by rfl⟩ : syracuseStep 798425 = 598819) B598819
theorem B536345 : Blo 354756 536345 := bstep (se 2 (by rfl) ⟨201129, by rfl⟩ : syracuseStep 536345 = 402259) B402259
theorem B798515 : Blo 354756 798515 := bstep (se 1 (by rfl) ⟨598886, by rfl⟩ : syracuseStep 798515 = 1197773) B1197773
theorem B601931 : Blo 354756 601931 := bstep (se 1 (by rfl) ⟨451448, by rfl⟩ : syracuseStep 601931 = 902897) B902897
theorem B798551 : Blo 354756 798551 := bstep (se 1 (by rfl) ⟨598913, by rfl⟩ : syracuseStep 798551 = 1197827) B1197827
theorem B536459 : Blo 354756 536459 := bstep (se 1 (by rfl) ⟨402344, by rfl⟩ : syracuseStep 536459 = 804689) B804689
theorem B536471 : Blo 354756 536471 := bstep (se 1 (by rfl) ⟨402353, by rfl⟩ : syracuseStep 536471 = 804707) B804707
theorem B602059 : Blo 354756 602059 := bstep (se 1 (by rfl) ⟨451544, by rfl⟩ : syracuseStep 602059 = 903089) B903089
theorem B536537 : Blo 354756 536537 := bstep (se 2 (by rfl) ⟨201201, by rfl⟩ : syracuseStep 536537 = 402403) B402403
theorem B798731 : Blo 354756 798731 := bstep (se 1 (by rfl) ⟨599048, by rfl⟩ : syracuseStep 798731 = 1198097) B1198097
theorem B798785 : Blo 354756 798785 := bstep (se 2 (by rfl) ⟨299544, by rfl⟩ : syracuseStep 798785 = 599089) B599089
theorem B536651 : Blo 354756 536651 := bstep (se 1 (by rfl) ⟨402488, by rfl⟩ : syracuseStep 536651 = 804977) B804977
theorem B536663 : Blo 354756 536663 := bstep (se 1 (by rfl) ⟨402497, by rfl⟩ : syracuseStep 536663 = 804995) B804995
theorem B602201 : Blo 354756 602201 := bstep (se 2 (by rfl) ⟨225825, by rfl⟩ : syracuseStep 602201 = 451651) B451651
theorem B536729 : Blo 354756 536729 := bstep (se 2 (by rfl) ⟨201273, by rfl⟩ : syracuseStep 536729 = 402547) B402547
theorem B602329 : Blo 354756 602329 := bstep (se 2 (by rfl) ⟨225873, by rfl⟩ : syracuseStep 602329 = 451747) B451747
theorem B536843 : Blo 354756 536843 := bstep (se 1 (by rfl) ⟨402632, by rfl⟩ : syracuseStep 536843 = 805265) B805265
theorem B536855 : Blo 354756 536855 := bstep (se 1 (by rfl) ⟨402641, by rfl⟩ : syracuseStep 536855 = 805283) B805283
theorem B799001 : Blo 354756 799001 := bstep (se 2 (by rfl) ⟨299625, by rfl⟩ : syracuseStep 799001 = 599251) B599251
theorem B405815 : Blo 354756 405815 := bstep (se 1 (by rfl) ⟨304361, by rfl⟩ : syracuseStep 405815 = 608723) B608723
theorem B536921 : Blo 354756 536921 := bstep (se 2 (by rfl) ⟨201345, by rfl⟩ : syracuseStep 536921 = 402691) B402691
theorem B799091 : Blo 354756 799091 := bstep (se 1 (by rfl) ⟨599318, by rfl⟩ : syracuseStep 799091 = 1198637) B1198637
theorem B799127 : Blo 354756 799127 := bstep (se 1 (by rfl) ⟨599345, by rfl⟩ : syracuseStep 799127 = 1198691) B1198691
theorem B405911 : Blo 354756 405911 := bstep (se 1 (by rfl) ⟨304433, by rfl⟩ : syracuseStep 405911 = 608867) B608867
theorem B537035 : Blo 354756 537035 := bstep (se 1 (by rfl) ⟨402776, by rfl⟩ : syracuseStep 537035 = 805553) B805553
theorem B537047 : Blo 354756 537047 := bstep (se 1 (by rfl) ⟨402785, by rfl⟩ : syracuseStep 537047 = 805571) B805571
theorem B537113 : Blo 354756 537113 := bstep (se 2 (by rfl) ⟨201417, by rfl⟩ : syracuseStep 537113 = 402835) B402835
theorem B799307 : Blo 354756 799307 := bstep (se 1 (by rfl) ⟨599480, by rfl⟩ : syracuseStep 799307 = 1198961) B1198961
theorem B799361 : Blo 354756 799361 := bstep (se 2 (by rfl) ⟨299760, by rfl⟩ : syracuseStep 799361 = 599521) B599521
theorem B537227 : Blo 354756 537227 := bstep (se 1 (by rfl) ⟨402920, by rfl⟩ : syracuseStep 537227 = 805841) B805841
theorem B537239 : Blo 354756 537239 := bstep (se 1 (by rfl) ⟨402929, by rfl⟩ : syracuseStep 537239 = 805859) B805859
theorem B537305 : Blo 354756 537305 := bstep (se 2 (by rfl) ⟨201489, by rfl⟩ : syracuseStep 537305 = 402979) B402979
theorem B1356547 : Blo 354756 1356547 := bstep (se 1 (by rfl) ⟨1017410, by rfl⟩ : syracuseStep 1356547 = 2034821) B2034821
theorem B602903 : Blo 354756 602903 := bstep (se 1 (by rfl) ⟨452177, by rfl⟩ : syracuseStep 602903 = 904355) B904355
theorem B537419 : Blo 354756 537419 := bstep (se 1 (by rfl) ⟨403064, by rfl⟩ : syracuseStep 537419 = 806129) B806129
theorem B1815371 : Blo 354756 1815371 := bstep (se 1 (by rfl) ⟨1361528, by rfl⟩ : syracuseStep 1815371 = 2723057) B2723057
theorem B537431 : Blo 354756 537431 := bstep (se 1 (by rfl) ⟨403073, by rfl⟩ : syracuseStep 537431 = 806147) B806147
theorem B799577 : Blo 354756 799577 := bstep (se 2 (by rfl) ⟨299841, by rfl⟩ : syracuseStep 799577 = 599683) B599683
theorem B603031 : Blo 354756 603031 := bstep (se 1 (by rfl) ⟨452273, by rfl⟩ : syracuseStep 603031 = 904547) B904547
theorem B537497 : Blo 354756 537497 := bstep (se 2 (by rfl) ⟨201561, by rfl⟩ : syracuseStep 537497 = 403123) B403123
theorem B799667 : Blo 354756 799667 := bstep (se 1 (by rfl) ⟨599750, by rfl⟩ : syracuseStep 799667 = 1199501) B1199501
theorem B799703 : Blo 354756 799703 := bstep (se 1 (by rfl) ⟨599777, by rfl⟩ : syracuseStep 799703 = 1199555) B1199555
theorem B537611 : Blo 354756 537611 := bstep (se 1 (by rfl) ⟨403208, by rfl⟩ : syracuseStep 537611 = 806417) B806417
theorem B537623 : Blo 354756 537623 := bstep (se 1 (by rfl) ⟨403217, by rfl⟩ : syracuseStep 537623 = 806435) B806435
theorem B1356851 : Blo 354756 1356851 := bstep (se 1 (by rfl) ⟨1017638, by rfl⟩ : syracuseStep 1356851 = 2035277) B2035277
theorem B537689 : Blo 354756 537689 := bstep (se 2 (by rfl) ⟨201633, by rfl⟩ : syracuseStep 537689 = 403267) B403267
theorem B6075485 : Blo 354756 6075485 := bstep (se 3 (by rfl) ⟨1139153, by rfl⟩ : syracuseStep 6075485 = 2278307) B2278307
theorem B799883 : Blo 354756 799883 := bstep (se 1 (by rfl) ⟨599912, by rfl⟩ : syracuseStep 799883 = 1199825) B1199825
theorem B1520785 : Blo 354756 1520785 := bstep (se 2 (by rfl) ⟨570294, by rfl⟩ : syracuseStep 1520785 = 1140589) B1140589
theorem B898199 : Blo 354756 898199 := bstep (se 1 (by rfl) ⟨673649, by rfl⟩ : syracuseStep 898199 = 1347299) B1347299
theorem B799937 : Blo 354756 799937 := bstep (se 2 (by rfl) ⟨299976, by rfl⟩ : syracuseStep 799937 = 599953) B599953
theorem B537803 : Blo 354756 537803 := bstep (se 1 (by rfl) ⟨403352, by rfl⟩ : syracuseStep 537803 = 806705) B806705
theorem B537815 : Blo 354756 537815 := bstep (se 1 (by rfl) ⟨403361, by rfl⟩ : syracuseStep 537815 = 806723) B806723
theorem B537881 : Blo 354756 537881 := bstep (se 2 (by rfl) ⟨201705, by rfl⟩ : syracuseStep 537881 = 403411) B403411
theorem B505163 : Blo 354756 505163 := bstep (se 1 (by rfl) ⟨378872, by rfl⟩ : syracuseStep 505163 = 757745) B757745
theorem B537995 : Blo 354756 537995 := bstep (se 1 (by rfl) ⟨403496, by rfl⟩ : syracuseStep 537995 = 806993) B806993
theorem B538007 : Blo 354756 538007 := bstep (se 1 (by rfl) ⟨403505, by rfl⟩ : syracuseStep 538007 = 807011) B807011
theorem B800153 : Blo 354756 800153 := bstep (se 2 (by rfl) ⟨300057, by rfl⟩ : syracuseStep 800153 = 600115) B600115
theorem B832961 : Blo 354756 832961 := bstep (se 2 (by rfl) ⟨312360, by rfl⟩ : syracuseStep 832961 = 624721) B624721
theorem B406987 : Blo 354756 406987 := bstep (se 1 (by rfl) ⟨305240, by rfl⟩ : syracuseStep 406987 = 610481) B610481
theorem B538073 : Blo 354756 538073 := bstep (se 2 (by rfl) ⟨201777, by rfl⟩ : syracuseStep 538073 = 403555) B403555
theorem B800243 : Blo 354756 800243 := bstep (se 1 (by rfl) ⟨600182, by rfl⟩ : syracuseStep 800243 = 1200365) B1200365
theorem B3061253 : Blo 354756 3061253 := bstep (se 4 (by rfl) ⟨286992, by rfl⟩ : syracuseStep 3061253 = 573985) B573985
theorem B603659 : Blo 354756 603659 := bstep (se 1 (by rfl) ⟨452744, by rfl⟩ : syracuseStep 603659 = 905489) B905489
theorem B800279 : Blo 354756 800279 := bstep (se 1 (by rfl) ⟨600209, by rfl⟩ : syracuseStep 800279 = 1200419) B1200419
theorem B9942659 : Blo 354756 9942659 := bstep (se 1 (by rfl) ⟨7456994, by rfl⟩ : syracuseStep 9942659 = 14913989) B14913989
theorem B603787 : Blo 354756 603787 := bstep (se 1 (by rfl) ⟨452840, by rfl⟩ : syracuseStep 603787 = 905681) B905681
theorem B1357505 : Blo 354756 1357505 := bstep (se 2 (by rfl) ⟨509064, by rfl⟩ : syracuseStep 1357505 = 1018129) B1018129
theorem B800459 : Blo 354756 800459 := bstep (se 1 (by rfl) ⟨600344, by rfl⟩ : syracuseStep 800459 = 1200689) B1200689
theorem B800513 : Blo 354756 800513 := bstep (se 2 (by rfl) ⟨300192, by rfl⟩ : syracuseStep 800513 = 600385) B600385
theorem B603929 : Blo 354756 603929 := bstep (se 2 (by rfl) ⟨226473, by rfl⟩ : syracuseStep 603929 = 452947) B452947
theorem B2701187 : Blo 354756 2701187 := bstep (se 1 (by rfl) ⟨2025890, by rfl⟩ : syracuseStep 2701187 = 4051781) B4051781
theorem B604057 : Blo 354756 604057 := bstep (se 2 (by rfl) ⟨226521, by rfl⟩ : syracuseStep 604057 = 453043) B453043
theorem B899009 : Blo 354756 899009 := bstep (se 2 (by rfl) ⟨337128, by rfl⟩ : syracuseStep 899009 = 674257) B674257
theorem B800729 : Blo 354756 800729 := bstep (se 2 (by rfl) ⟨300273, by rfl⟩ : syracuseStep 800729 = 600547) B600547
theorem B800819 : Blo 354756 800819 := bstep (se 1 (by rfl) ⟨600614, by rfl⟩ : syracuseStep 800819 = 1201229) B1201229
theorem B800855 : Blo 354756 800855 := bstep (se 1 (by rfl) ⟨600641, by rfl⟩ : syracuseStep 800855 = 1201283) B1201283
theorem B801035 : Blo 354756 801035 := bstep (se 1 (by rfl) ⟨600776, by rfl⟩ : syracuseStep 801035 = 1201553) B1201553
theorem B571673 : Blo 354756 571673 := bstep (se 2 (by rfl) ⟨214377, by rfl⟩ : syracuseStep 571673 = 428755) B428755
theorem B801089 : Blo 354756 801089 := bstep (se 2 (by rfl) ⟨300408, by rfl⟩ : syracuseStep 801089 = 600817) B600817
theorem B538969 : Blo 354756 538969 := bstep (se 2 (by rfl) ⟨202113, by rfl⟩ : syracuseStep 538969 = 404227) B404227
theorem B1292723 : Blo 354756 1292723 := bstep (se 1 (by rfl) ⟨969542, by rfl⟩ : syracuseStep 1292723 = 1939085) B1939085
theorem B604631 : Blo 354756 604631 := bstep (se 1 (by rfl) ⟨453473, by rfl⟩ : syracuseStep 604631 = 906947) B906947
theorem B899545 : Blo 354756 899545 := bstep (se 2 (by rfl) ⟨337329, by rfl⟩ : syracuseStep 899545 = 674659) B674659
theorem B801305 : Blo 354756 801305 := bstep (se 2 (by rfl) ⟨300489, by rfl⟩ : syracuseStep 801305 = 600979) B600979
theorem B1292851 : Blo 354756 1292851 := bstep (se 1 (by rfl) ⟨969638, by rfl⟩ : syracuseStep 1292851 = 1939277) B1939277
theorem B604759 : Blo 354756 604759 := bstep (se 1 (by rfl) ⟨453569, by rfl⟩ : syracuseStep 604759 = 907139) B907139
theorem B801395 : Blo 354756 801395 := bstep (se 1 (by rfl) ⟨601046, by rfl⟩ : syracuseStep 801395 = 1202093) B1202093
theorem B801431 : Blo 354756 801431 := bstep (se 1 (by rfl) ⟨601073, by rfl⟩ : syracuseStep 801431 = 1202147) B1202147
theorem B801611 : Blo 354756 801611 := bstep (se 1 (by rfl) ⟨601208, by rfl⟩ : syracuseStep 801611 = 1202417) B1202417
theorem B801665 : Blo 354756 801665 := bstep (se 2 (by rfl) ⟨300624, by rfl⟩ : syracuseStep 801665 = 601249) B601249
theorem B1358765 : Blo 354756 1358765 := bstep (se 3 (by rfl) ⟨254768, by rfl⟩ : syracuseStep 1358765 = 509537) B509537
theorem B1358795 : Blo 354756 1358795 := bstep (se 1 (by rfl) ⟨1019096, by rfl⟩ : syracuseStep 1358795 = 2038193) B2038193
theorem B801881 : Blo 354756 801881 := bstep (se 2 (by rfl) ⟨300705, by rfl⟩ : syracuseStep 801881 = 601411) B601411
theorem B801971 : Blo 354756 801971 := bstep (se 1 (by rfl) ⟨601478, by rfl⟩ : syracuseStep 801971 = 1202957) B1202957
theorem B605387 : Blo 354756 605387 := bstep (se 1 (by rfl) ⟨454040, by rfl⟩ : syracuseStep 605387 = 908081) B908081
theorem B802007 : Blo 354756 802007 := bstep (se 1 (by rfl) ⟨601505, by rfl⟩ : syracuseStep 802007 = 1203011) B1203011
theorem B6208753 : Blo 354756 6208753 := bstep (se 2 (by rfl) ⟨2328282, by rfl⟩ : syracuseStep 6208753 = 4656565) B4656565
theorem B802187 : Blo 354756 802187 := bstep (se 1 (by rfl) ⟨601640, by rfl⟩ : syracuseStep 802187 = 1203281) B1203281
theorem B802241 : Blo 354756 802241 := bstep (se 2 (by rfl) ⟨300840, by rfl⟩ : syracuseStep 802241 = 601681) B601681
theorem B900659 : Blo 354756 900659 := bstep (se 1 (by rfl) ⟨675494, by rfl⟩ : syracuseStep 900659 = 1350989) B1350989
theorem B1359449 : Blo 354756 1359449 := bstep (se 2 (by rfl) ⟨509793, by rfl⟩ : syracuseStep 1359449 = 1019587) B1019587
theorem B540313 : Blo 354756 540313 := bstep (se 2 (by rfl) ⟨202617, by rfl⟩ : syracuseStep 540313 = 405235) B405235
theorem B802457 : Blo 354756 802457 := bstep (se 2 (by rfl) ⟨300921, by rfl⟩ : syracuseStep 802457 = 601843) B601843
theorem B1654451 : Blo 354756 1654451 := bstep (se 1 (by rfl) ⟨1240838, by rfl⟩ : syracuseStep 1654451 = 2481677) B2481677
theorem B802547 : Blo 354756 802547 := bstep (se 1 (by rfl) ⟨601910, by rfl⟩ : syracuseStep 802547 = 1203821) B1203821
theorem B802583 : Blo 354756 802583 := bstep (se 1 (by rfl) ⟨601937, by rfl⟩ : syracuseStep 802583 = 1203875) B1203875
theorem B540503 : Blo 354756 540503 := bstep (se 1 (by rfl) ⟨405377, by rfl⟩ : syracuseStep 540503 = 810755) B810755
theorem B900953 : Blo 354756 900953 := bstep (se 2 (by rfl) ⟨337857, by rfl⟩ : syracuseStep 900953 = 675715) B675715
theorem B1359767 : Blo 354756 1359767 := bstep (se 1 (by rfl) ⟨1019825, by rfl⟩ : syracuseStep 1359767 = 2039651) B2039651
theorem B802763 : Blo 354756 802763 := bstep (se 1 (by rfl) ⟨602072, by rfl⟩ : syracuseStep 802763 = 1204145) B1204145
theorem B802817 : Blo 354756 802817 := bstep (se 2 (by rfl) ⟨301056, by rfl⟩ : syracuseStep 802817 = 602113) B602113
theorem B540697 : Blo 354756 540697 := bstep (se 2 (by rfl) ⟨202761, by rfl⟩ : syracuseStep 540697 = 405523) B405523
theorem B1523929 : Blo 354756 1523929 := bstep (se 2 (by rfl) ⟨571473, by rfl⟩ : syracuseStep 1523929 = 1142947) B1142947
theorem B803033 : Blo 354756 803033 := bstep (se 2 (by rfl) ⟨301137, by rfl⟩ : syracuseStep 803033 = 602275) B602275
theorem B803123 : Blo 354756 803123 := bstep (se 1 (by rfl) ⟨602342, by rfl⟩ : syracuseStep 803123 = 1204685) B1204685
theorem B803159 : Blo 354756 803159 := bstep (se 1 (by rfl) ⟨602369, by rfl⟩ : syracuseStep 803159 = 1204739) B1204739
theorem B803339 : Blo 354756 803339 := bstep (se 1 (by rfl) ⟨602504, by rfl⟩ : syracuseStep 803339 = 1205009) B1205009
theorem B1360435 : Blo 354756 1360435 := bstep (se 1 (by rfl) ⟨1020326, by rfl⟩ : syracuseStep 1360435 = 2040653) B2040653
theorem B803393 : Blo 354756 803393 := bstep (se 2 (by rfl) ⟨301272, by rfl⟩ : syracuseStep 803393 = 602545) B602545
theorem B803609 : Blo 354756 803609 := bstep (se 2 (by rfl) ⟨301353, by rfl⟩ : syracuseStep 803609 = 602707) B602707
theorem B1524545 : Blo 354756 1524545 := bstep (se 2 (by rfl) ⟨571704, by rfl⟩ : syracuseStep 1524545 = 1143409) B1143409
theorem B803699 : Blo 354756 803699 := bstep (se 1 (by rfl) ⟨602774, by rfl⟩ : syracuseStep 803699 = 1205549) B1205549
theorem B1622915 : Blo 354756 1622915 := bstep (se 1 (by rfl) ⟨1217186, by rfl⟩ : syracuseStep 1622915 = 2434373) B2434373
theorem B607115 : Blo 354756 607115 := bstep (se 1 (by rfl) ⟨455336, by rfl⟩ : syracuseStep 607115 = 910673) B910673
theorem B803735 : Blo 354756 803735 := bstep (se 1 (by rfl) ⟨602801, by rfl⟩ : syracuseStep 803735 = 1205603) B1205603
theorem B803915 : Blo 354756 803915 := bstep (se 1 (by rfl) ⟨602936, by rfl⟩ : syracuseStep 803915 = 1205873) B1205873
theorem B803969 : Blo 354756 803969 := bstep (se 2 (by rfl) ⟨301488, by rfl⟩ : syracuseStep 803969 = 602977) B602977
theorem B869555 : Blo 354756 869555 := bstep (se 1 (by rfl) ⟨652166, by rfl⟩ : syracuseStep 869555 = 1304333) B1304333
theorem B2704589 : Blo 354756 2704589 := bstep (se 3 (by rfl) ⟨507110, by rfl⟩ : syracuseStep 2704589 = 1014221) B1014221
theorem B4080941 : Blo 354756 4080941 := bstep (se 3 (by rfl) ⟨765176, by rfl⟩ : syracuseStep 4080941 = 1530353) B1530353
theorem B804185 : Blo 354756 804185 := bstep (se 2 (by rfl) ⟨301569, by rfl⟩ : syracuseStep 804185 = 603139) B603139
theorem B3458483 : Blo 354756 3458483 := bstep (se 1 (by rfl) ⟨2593862, by rfl⟩ : syracuseStep 3458483 = 5187725) B5187725
theorem B804275 : Blo 354756 804275 := bstep (se 1 (by rfl) ⟨603206, by rfl⟩ : syracuseStep 804275 = 1206413) B1206413
theorem B902603 : Blo 354756 902603 := bstep (se 1 (by rfl) ⟨676952, by rfl⟩ : syracuseStep 902603 = 1353905) B1353905
theorem B804311 : Blo 354756 804311 := bstep (se 1 (by rfl) ⟨603233, by rfl⟩ : syracuseStep 804311 = 1206467) B1206467
theorem B2442797 : Blo 354756 2442797 := bstep (se 3 (by rfl) ⟨458024, by rfl⟩ : syracuseStep 2442797 = 916049) B916049
theorem B804491 : Blo 354756 804491 := bstep (se 1 (by rfl) ⟨603368, by rfl⟩ : syracuseStep 804491 = 1206737) B1206737
theorem B1197719 : Blo 354756 1197719 := bstep (se 1 (by rfl) ⟨898289, by rfl⟩ : syracuseStep 1197719 = 1796579) B1796579
theorem B2705075 : Blo 354756 2705075 := bstep (se 1 (by rfl) ⟨2028806, by rfl⟩ : syracuseStep 2705075 = 4057613) B4057613
theorem B804545 : Blo 354756 804545 := bstep (se 2 (by rfl) ⟨301704, by rfl⟩ : syracuseStep 804545 = 603409) B603409
theorem B1361681 : Blo 354756 1361681 := bstep (se 2 (by rfl) ⟨510630, by rfl⟩ : syracuseStep 1361681 = 1021261) B1021261
theorem B12994357 : Blo 354756 12994357 := bstep (se 5 (by rfl) ⟨609110, by rfl⟩ : syracuseStep 12994357 = 1218221) B1218221
theorem B608087 : Blo 354756 608087 := bstep (se 1 (by rfl) ⟨456065, by rfl⟩ : syracuseStep 608087 = 912131) B912131
theorem B968537 : Blo 354756 968537 := bstep (se 2 (by rfl) ⟨363201, by rfl⟩ : syracuseStep 968537 = 726403) B726403
theorem B13846373 : Blo 354756 13846373 := bstep (se 4 (by rfl) ⟨1298097, by rfl⟩ : syracuseStep 13846373 = 2596195) B2596195
theorem B673687 : Blo 354756 673687 := bstep (se 1 (by rfl) ⟨505265, by rfl⟩ : syracuseStep 673687 = 1010531) B1010531
theorem B804761 : Blo 354756 804761 := bstep (se 2 (by rfl) ⟨301785, by rfl⟩ : syracuseStep 804761 = 603571) B603571
theorem B804851 : Blo 354756 804851 := bstep (se 1 (by rfl) ⟨603638, by rfl⟩ : syracuseStep 804851 = 1207277) B1207277
theorem B804887 : Blo 354756 804887 := bstep (se 1 (by rfl) ⟨603665, by rfl⟩ : syracuseStep 804887 = 1207331) B1207331
theorem B1198259 : Blo 354756 1198259 := bstep (se 1 (by rfl) ⟨898694, by rfl⟩ : syracuseStep 1198259 = 1797389) B1797389
theorem B805067 : Blo 354756 805067 := bstep (se 1 (by rfl) ⟨603800, by rfl⟩ : syracuseStep 805067 = 1207601) B1207601
theorem B805121 : Blo 354756 805121 := bstep (se 2 (by rfl) ⟨301920, by rfl⟩ : syracuseStep 805121 = 603841) B603841
theorem B510295 : Blo 354756 510295 := bstep (se 1 (by rfl) ⟨382721, by rfl⟩ : syracuseStep 510295 = 765443) B765443
theorem B903575 : Blo 354756 903575 := bstep (se 1 (by rfl) ⟨677681, by rfl⟩ : syracuseStep 903575 = 1355363) B1355363
theorem B1198529 : Blo 354756 1198529 := bstep (se 2 (by rfl) ⟨449448, by rfl⟩ : syracuseStep 1198529 = 898897) B898897
theorem B379351 : Blo 354756 379351 := bstep (se 1 (by rfl) ⟨284513, by rfl⟩ : syracuseStep 379351 = 569027) B569027
theorem B805337 : Blo 354756 805337 := bstep (se 2 (by rfl) ⟨302001, by rfl⟩ : syracuseStep 805337 = 604003) B604003
theorem B805427 : Blo 354756 805427 := bstep (se 1 (by rfl) ⟨604070, by rfl⟩ : syracuseStep 805427 = 1208141) B1208141
theorem B641611 : Blo 354756 641611 := bstep (se 1 (by rfl) ⟨481208, by rfl⟩ : syracuseStep 641611 = 962417) B962417
theorem B805463 : Blo 354756 805463 := bstep (se 1 (by rfl) ⟨604097, by rfl⟩ : syracuseStep 805463 = 1208195) B1208195
theorem B674507 : Blo 354756 674507 := bstep (se 1 (by rfl) ⟨505880, by rfl⟩ : syracuseStep 674507 = 1011761) B1011761
theorem B674561 : Blo 354756 674561 := bstep (se 2 (by rfl) ⟨252960, by rfl⟩ : syracuseStep 674561 = 505921) B505921
theorem B805643 : Blo 354756 805643 := bstep (se 1 (by rfl) ⟨604232, by rfl⟩ : syracuseStep 805643 = 1208465) B1208465
theorem B42257173 : Blo 354756 42257173 := bstep (se 6 (by rfl) ⟨990402, by rfl⟩ : syracuseStep 42257173 = 1980805) B1980805
theorem B3263267 : Blo 354756 3263267 := bstep (se 1 (by rfl) ⟨2447450, by rfl⟩ : syracuseStep 3263267 = 4894901) B4894901
theorem B2280257 : Blo 354756 2280257 := bstep (se 2 (by rfl) ⟨855096, by rfl⟩ : syracuseStep 2280257 = 1710193) B1710193
theorem B805697 : Blo 354756 805697 := bstep (se 2 (by rfl) ⟨302136, by rfl⟩ : syracuseStep 805697 = 604273) B604273
theorem B9849701 : Blo 354756 9849701 := bstep (se 4 (by rfl) ⟨923409, by rfl⟩ : syracuseStep 9849701 = 1846819) B1846819
theorem B1199069 : Blo 354756 1199069 := bstep (se 3 (by rfl) ⟨224825, by rfl⟩ : syracuseStep 1199069 = 449651) B449651
theorem B412651 : Blo 354756 412651 := bstep (se 1 (by rfl) ⟨309488, by rfl⟩ : syracuseStep 412651 = 618977) B618977
theorem B805913 : Blo 354756 805913 := bstep (se 2 (by rfl) ⟨302217, by rfl⟩ : syracuseStep 805913 = 604435) B604435
theorem B904243 : Blo 354756 904243 := bstep (se 1 (by rfl) ⟨678182, by rfl⟩ : syracuseStep 904243 = 1356365) B1356365
theorem B3296321 : Blo 354756 3296321 := bstep (se 2 (by rfl) ⟨1236120, by rfl⟩ : syracuseStep 3296321 = 2472241) B2472241
theorem B2706533 : Blo 354756 2706533 := bstep (se 4 (by rfl) ⟨253737, by rfl⟩ : syracuseStep 2706533 = 507475) B507475
theorem B806003 : Blo 354756 806003 := bstep (se 1 (by rfl) ⟨604502, by rfl⟩ : syracuseStep 806003 = 1209005) B1209005
theorem B806039 : Blo 354756 806039 := bstep (se 1 (by rfl) ⟨604529, by rfl⟩ : syracuseStep 806039 = 1209059) B1209059
theorem B904385 : Blo 354756 904385 := bstep (se 2 (by rfl) ⟨339144, by rfl⟩ : syracuseStep 904385 = 678289) B678289
theorem B1527005 : Blo 354756 1527005 := bstep (se 3 (by rfl) ⟨286313, by rfl⟩ : syracuseStep 1527005 = 572627) B572627
theorem B380171 : Blo 354756 380171 := bstep (se 1 (by rfl) ⟨285128, by rfl⟩ : syracuseStep 380171 = 570257) B570257
theorem B806219 : Blo 354756 806219 := bstep (se 1 (by rfl) ⟨604664, by rfl⟩ : syracuseStep 806219 = 1209329) B1209329
theorem B806273 : Blo 354756 806273 := bstep (se 2 (by rfl) ⟨302352, by rfl⟩ : syracuseStep 806273 = 604705) B604705
theorem B380299 : Blo 354756 380299 := bstep (se 1 (by rfl) ⟨285224, by rfl⟩ : syracuseStep 380299 = 570449) B570449
theorem B6180275 : Blo 354756 6180275 := bstep (se 1 (by rfl) ⟨4635206, by rfl⟩ : syracuseStep 6180275 = 9270413) B9270413
theorem B6114851 : Blo 354756 6114851 := bstep (se 1 (by rfl) ⟨4586138, by rfl⟩ : syracuseStep 6114851 = 9172277) B9172277
theorem B2707019 : Blo 354756 2707019 := bstep (se 1 (by rfl) ⟨2030264, by rfl⟩ : syracuseStep 2707019 = 4060529) B4060529
theorem B806489 : Blo 354756 806489 := bstep (se 2 (by rfl) ⟨302433, by rfl⟩ : syracuseStep 806489 = 604867) B604867
theorem B675479 : Blo 354756 675479 := bstep (se 1 (by rfl) ⟨506609, by rfl⟩ : syracuseStep 675479 = 1013219) B1013219
theorem B806579 : Blo 354756 806579 := bstep (se 1 (by rfl) ⟨604934, by rfl⟩ : syracuseStep 806579 = 1209869) B1209869
theorem B806615 : Blo 354756 806615 := bstep (se 1 (by rfl) ⟨604961, by rfl⟩ : syracuseStep 806615 = 1209923) B1209923
theorem B806795 : Blo 354756 806795 := bstep (se 1 (by rfl) ⟨605096, by rfl⟩ : syracuseStep 806795 = 1210193) B1210193
theorem B806849 : Blo 354756 806849 := bstep (se 2 (by rfl) ⟨302568, by rfl⟩ : syracuseStep 806849 = 605137) B605137
theorem B1200203 : Blo 354756 1200203 := bstep (se 1 (by rfl) ⟨900152, by rfl⟩ : syracuseStep 1200203 = 1800305) B1800305
theorem B807065 : Blo 354756 807065 := bstep (se 2 (by rfl) ⟨302649, by rfl⟩ : syracuseStep 807065 = 605299) B605299
theorem B676019 : Blo 354756 676019 := bstep (se 1 (by rfl) ⟨507014, by rfl⟩ : syracuseStep 676019 = 1014029) B1014029
theorem B544985 : Blo 354756 544985 := bstep (se 2 (by rfl) ⟨204369, by rfl⟩ : syracuseStep 544985 = 408739) B408739
theorem B807155 : Blo 354756 807155 := bstep (se 1 (by rfl) ⟨605366, by rfl⟩ : syracuseStep 807155 = 1210733) B1210733
theorem B807191 : Blo 354756 807191 := bstep (se 1 (by rfl) ⟨605393, by rfl⟩ : syracuseStep 807191 = 1210787) B1210787
theorem B1200473 : Blo 354756 1200473 := bstep (se 2 (by rfl) ⟨450177, by rfl⟩ : syracuseStep 1200473 = 900355) B900355
theorem B643457 : Blo 354756 643457 := bstep (se 2 (by rfl) ⟨241296, by rfl⟩ : syracuseStep 643457 = 482593) B482593
theorem B905651 : Blo 354756 905651 := bstep (se 1 (by rfl) ⟨679238, by rfl⟩ : syracuseStep 905651 = 1358477) B1358477
theorem B676289 : Blo 354756 676289 := bstep (se 2 (by rfl) ⟨253608, by rfl⟩ : syracuseStep 676289 = 507217) B507217
theorem B643673 : Blo 354756 643673 := bstep (se 2 (by rfl) ⟨241377, by rfl⟩ : syracuseStep 643673 = 482755) B482755
theorem B676505 : Blo 354756 676505 := bstep (se 2 (by rfl) ⟨253689, by rfl⟩ : syracuseStep 676505 = 507379) B507379
theorem B7688945 : Blo 354756 7688945 := bstep (se 2 (by rfl) ⟨2883354, by rfl⟩ : syracuseStep 7688945 = 5766709) B5766709
theorem B906187 : Blo 354756 906187 := bstep (se 1 (by rfl) ⟨679640, by rfl⟩ : syracuseStep 906187 = 1359281) B1359281
theorem B1201175 : Blo 354756 1201175 := bstep (se 1 (by rfl) ⟨900881, by rfl⟩ : syracuseStep 1201175 = 1801763) B1801763
theorem B906329 : Blo 354756 906329 := bstep (se 2 (by rfl) ⟨339873, by rfl⟩ : syracuseStep 906329 = 679747) B679747
theorem B611479 : Blo 354756 611479 := bstep (se 1 (by rfl) ⟨458609, by rfl⟩ : syracuseStep 611479 = 917219) B917219
theorem B12998161 : Blo 354756 12998161 := bstep (se 2 (by rfl) ⟨4874310, by rfl⟩ : syracuseStep 12998161 = 9748621) B9748621
theorem B1201715 : Blo 354756 1201715 := bstep (se 1 (by rfl) ⟨901286, by rfl⟩ : syracuseStep 1201715 = 1802573) B1802573
theorem B1955393 : Blo 354756 1955393 := bstep (se 2 (by rfl) ⟨733272, by rfl⟩ : syracuseStep 1955393 = 1466545) B1466545
theorem B1529603 : Blo 354756 1529603 := bstep (se 1 (by rfl) ⟨1147202, by rfl⟩ : syracuseStep 1529603 = 2294405) B2294405
theorem B1201985 : Blo 354756 1201985 := bstep (se 2 (by rfl) ⟨450744, by rfl⟩ : syracuseStep 1201985 = 901489) B901489
theorem B907159 : Blo 354756 907159 := bstep (se 1 (by rfl) ⟨680369, by rfl⟩ : syracuseStep 907159 = 1360739) B1360739
theorem B481241 : Blo 354756 481241 := bstep (se 2 (by rfl) ⟨180465, by rfl⟩ : syracuseStep 481241 = 360931) B360931
theorem B1366067 : Blo 354756 1366067 := bstep (se 1 (by rfl) ⟨1024550, by rfl⟩ : syracuseStep 1366067 = 2049101) B2049101
theorem B677963 : Blo 354756 677963 := bstep (se 1 (by rfl) ⟨508472, by rfl⟩ : syracuseStep 677963 = 1016945) B1016945
theorem B678145 : Blo 354756 678145 := bstep (se 2 (by rfl) ⟨254304, by rfl⟩ : syracuseStep 678145 = 508609) B508609
theorem B2283821 : Blo 354756 2283821 := bstep (se 3 (by rfl) ⟨428216, by rfl⟩ : syracuseStep 2283821 = 856433) B856433
theorem B13031725 : Blo 354756 13031725 := bstep (se 3 (by rfl) ⟨2443448, by rfl⟩ : syracuseStep 13031725 = 4886897) B4886897
theorem B907595 : Blo 354756 907595 := bstep (se 1 (by rfl) ⟨680696, by rfl⟩ : syracuseStep 907595 = 1361393) B1361393
theorem B1202525 : Blo 354756 1202525 := bstep (se 3 (by rfl) ⟨225473, by rfl⟩ : syracuseStep 1202525 = 450947) B450947
theorem B1628675 : Blo 354756 1628675 := bstep (se 1 (by rfl) ⟨1221506, by rfl⟩ : syracuseStep 1628675 = 2443013) B2443013
theorem B481879 : Blo 354756 481879 := bstep (se 1 (by rfl) ⟨361409, by rfl⟩ : syracuseStep 481879 = 722819) B722819
theorem B678593 : Blo 354756 678593 := bstep (se 2 (by rfl) ⟨254472, by rfl⟩ : syracuseStep 678593 = 508945) B508945
theorem B907969 : Blo 354756 907969 := bstep (se 2 (by rfl) ⟨340488, by rfl⟩ : syracuseStep 907969 = 680977) B680977
theorem B1366807 : Blo 354756 1366807 := bstep (se 1 (by rfl) ⟨1025105, by rfl⟩ : syracuseStep 1366807 = 2050211) B2050211
theorem B3267533 : Blo 354756 3267533 := bstep (se 3 (by rfl) ⟨612662, by rfl⟩ : syracuseStep 3267533 = 1225325) B1225325
theorem B12311513 : Blo 354756 12311513 := bstep (se 2 (by rfl) ⟨4616817, by rfl⟩ : syracuseStep 12311513 = 9233635) B9233635
theorem B678935 : Blo 354756 678935 := bstep (se 1 (by rfl) ⟨509201, by rfl⟩ : syracuseStep 678935 = 1018403) B1018403
theorem B810071 : Blo 354756 810071 := bstep (se 1 (by rfl) ⟨607553, by rfl⟩ : syracuseStep 810071 = 1215107) B1215107
theorem B810251 : Blo 354756 810251 := bstep (se 1 (by rfl) ⟨607688, by rfl⟩ : syracuseStep 810251 = 1215377) B1215377
theorem B449803 : Blo 354756 449803 := bstep (se 1 (by rfl) ⟨337352, by rfl⟩ : syracuseStep 449803 = 674705) B674705
theorem B1203659 : Blo 354756 1203659 := bstep (se 1 (by rfl) ⟨902744, by rfl⟩ : syracuseStep 1203659 = 1805489) B1805489
theorem B1105483 : Blo 354756 1105483 := bstep (se 1 (by rfl) ⟨829112, by rfl⟩ : syracuseStep 1105483 = 1658225) B1658225
theorem B679603 : Blo 354756 679603 := bstep (se 1 (by rfl) ⟨509702, by rfl⟩ : syracuseStep 679603 = 1019405) B1019405
theorem B1203929 : Blo 354756 1203929 := bstep (se 2 (by rfl) ⟨451473, by rfl⟩ : syracuseStep 1203929 = 902947) B902947
theorem B11952197 : Blo 354756 11952197 := bstep (se 4 (by rfl) ⟨1120518, by rfl⟩ : syracuseStep 11952197 = 2241037) B2241037
theorem B1531979 : Blo 354756 1531979 := bstep (se 1 (by rfl) ⟨1148984, by rfl⟩ : syracuseStep 1531979 = 2297969) B2297969
theorem B680051 : Blo 354756 680051 := bstep (se 1 (by rfl) ⟨510038, by rfl⟩ : syracuseStep 680051 = 1020077) B1020077
theorem B3039383 : Blo 354756 3039383 := bstep (se 1 (by rfl) ⟨2279537, by rfl⟩ : syracuseStep 3039383 = 4559075) B4559075
theorem B680089 : Blo 354756 680089 := bstep (se 2 (by rfl) ⟨255033, by rfl⟩ : syracuseStep 680089 = 510067) B510067
theorem B450775 : Blo 354756 450775 := bstep (se 1 (by rfl) ⟨338081, by rfl⟩ : syracuseStep 450775 = 676163) B676163
theorem B1204631 : Blo 354756 1204631 := bstep (se 1 (by rfl) ⟨903473, by rfl⟩ : syracuseStep 1204631 = 1806947) B1806947
theorem B680537 : Blo 354756 680537 := bstep (se 2 (by rfl) ⟨255201, by rfl⟩ : syracuseStep 680537 = 510403) B510403
theorem B2712365 : Blo 354756 2712365 := bstep (se 3 (by rfl) ⟨508568, by rfl⟩ : syracuseStep 2712365 = 1017137) B1017137
theorem B2581379 : Blo 354756 2581379 := bstep (se 1 (by rfl) ⟨1936034, by rfl⟩ : syracuseStep 2581379 = 3872069) B3872069
theorem B1205171 : Blo 354756 1205171 := bstep (se 1 (by rfl) ⟨903878, by rfl⟩ : syracuseStep 1205171 = 1807757) B1807757
theorem B386039 : Blo 354756 386039 := bstep (se 1 (by rfl) ⟨289529, by rfl⟩ : syracuseStep 386039 = 579059) B579059
theorem B451595 : Blo 354756 451595 := bstep (se 1 (by rfl) ⟨338696, by rfl⟩ : syracuseStep 451595 = 677393) B677393
theorem B1205441 : Blo 354756 1205441 := bstep (se 2 (by rfl) ⟨452040, by rfl⟩ : syracuseStep 1205441 = 904081) B904081
theorem B1467665 : Blo 354756 1467665 := bstep (se 2 (by rfl) ⟨550374, by rfl⟩ : syracuseStep 1467665 = 1100749) B1100749
theorem B2024797 : Blo 354756 2024797 := bstep (se 3 (by rfl) ⟨379649, by rfl⟩ : syracuseStep 2024797 = 759299) B759299
theorem B452299 : Blo 354756 452299 := bstep (se 1 (by rfl) ⟨339224, by rfl⟩ : syracuseStep 452299 = 678449) B678449
theorem B1205981 : Blo 354756 1205981 := bstep (se 3 (by rfl) ⟨226121, by rfl⟩ : syracuseStep 1205981 = 452243) B452243
theorem B2287511 : Blo 354756 2287511 := bstep (se 1 (by rfl) ⟨1715633, by rfl⟩ : syracuseStep 2287511 = 3431267) B3431267
theorem B452567 : Blo 354756 452567 := bstep (se 1 (by rfl) ⟨339425, by rfl⟩ : syracuseStep 452567 = 678851) B678851
theorem B3041297 : Blo 354756 3041297 := bstep (se 2 (by rfl) ⟨1140486, by rfl⟩ : syracuseStep 3041297 = 2280973) B2280973
theorem B550937 : Blo 354756 550937 := bstep (se 2 (by rfl) ⟨206601, by rfl⟩ : syracuseStep 550937 = 413203) B413203
theorem B1927385 : Blo 354756 1927385 := bstep (se 2 (by rfl) ⟨722769, by rfl⟩ : syracuseStep 1927385 = 1445539) B1445539
theorem B1796417 : Blo 354756 1796417 := bstep (se 2 (by rfl) ⟨673656, by rfl⟩ : syracuseStep 1796417 = 1347313) B1347313
theorem B354763 : Blo 354756 354763 := bstep (se 1 (by rfl) ⟨266072, by rfl⟩ : syracuseStep 354763 = 532145) B532145
theorem B354775 : Blo 354756 354775 := bstep (se 1 (by rfl) ⟨266081, by rfl⟩ : syracuseStep 354775 = 532163) B532163
theorem B354795 : Blo 354756 354795 := bstep (se 1 (by rfl) ⟨266096, by rfl⟩ : syracuseStep 354795 = 532193) B532193
theorem B354807 : Blo 354756 354807 := bstep (se 1 (by rfl) ⟨266105, by rfl⟩ : syracuseStep 354807 = 532211) B532211
theorem B354827 : Blo 354756 354827 := bstep (se 1 (by rfl) ⟨266120, by rfl⟩ : syracuseStep 354827 = 532241) B532241
theorem B354839 : Blo 354756 354839 := bstep (se 1 (by rfl) ⟨266129, by rfl⟩ : syracuseStep 354839 = 532259) B532259
theorem B354859 : Blo 354756 354859 := bstep (se 1 (by rfl) ⟨266144, by rfl⟩ : syracuseStep 354859 = 532289) B532289
theorem B354871 : Blo 354756 354871 := bstep (se 1 (by rfl) ⟨266153, by rfl⟩ : syracuseStep 354871 = 532307) B532307
theorem B354891 : Blo 354756 354891 := bstep (se 1 (by rfl) ⟨266168, by rfl⟩ : syracuseStep 354891 = 532337) B532337
theorem B354903 : Blo 354756 354903 := bstep (se 1 (by rfl) ⟨266177, by rfl⟩ : syracuseStep 354903 = 532355) B532355
theorem B354923 : Blo 354756 354923 := bstep (se 1 (by rfl) ⟨266192, by rfl⟩ : syracuseStep 354923 = 532385) B532385
theorem B354935 : Blo 354756 354935 := bstep (se 1 (by rfl) ⟨266201, by rfl⟩ : syracuseStep 354935 = 532403) B532403
theorem B354955 : Blo 354756 354955 := bstep (se 1 (by rfl) ⟨266216, by rfl⟩ : syracuseStep 354955 = 532433) B532433
theorem B354967 : Blo 354756 354967 := bstep (se 1 (by rfl) ⟨266225, by rfl⟩ : syracuseStep 354967 = 532451) B532451
theorem B453271 : Blo 354756 453271 := bstep (se 1 (by rfl) ⟨339953, by rfl⟩ : syracuseStep 453271 = 679907) B679907
theorem B354987 : Blo 354756 354987 := bstep (se 1 (by rfl) ⟨266240, by rfl⟩ : syracuseStep 354987 = 532481) B532481
theorem B354999 : Blo 354756 354999 := bstep (se 1 (by rfl) ⟨266249, by rfl⟩ : syracuseStep 354999 = 532499) B532499
theorem B355019 : Blo 354756 355019 := bstep (se 1 (by rfl) ⟨266264, by rfl⟩ : syracuseStep 355019 = 532529) B532529
theorem B355031 : Blo 354756 355031 := bstep (se 1 (by rfl) ⟨266273, by rfl⟩ : syracuseStep 355031 = 532547) B532547
theorem B355051 : Blo 354756 355051 := bstep (se 1 (by rfl) ⟨266288, by rfl⟩ : syracuseStep 355051 = 532577) B532577
theorem B355063 : Blo 354756 355063 := bstep (se 1 (by rfl) ⟨266297, by rfl⟩ : syracuseStep 355063 = 532595) B532595
theorem B355083 : Blo 354756 355083 := bstep (se 1 (by rfl) ⟨266312, by rfl⟩ : syracuseStep 355083 = 532625) B532625
theorem B355095 : Blo 354756 355095 := bstep (se 1 (by rfl) ⟨266321, by rfl⟩ : syracuseStep 355095 = 532643) B532643
theorem B813847 : Blo 354756 813847 := bstep (se 1 (by rfl) ⟨610385, by rfl⟩ : syracuseStep 813847 = 1220771) B1220771
theorem B355115 : Blo 354756 355115 := bstep (se 1 (by rfl) ⟨266336, by rfl⟩ : syracuseStep 355115 = 532673) B532673
theorem B355127 : Blo 354756 355127 := bstep (se 1 (by rfl) ⟨266345, by rfl⟩ : syracuseStep 355127 = 532691) B532691
theorem B355147 : Blo 354756 355147 := bstep (se 1 (by rfl) ⟨266360, by rfl⟩ : syracuseStep 355147 = 532721) B532721
theorem B1207115 : Blo 354756 1207115 := bstep (se 1 (by rfl) ⟨905336, by rfl⟩ : syracuseStep 1207115 = 1810673) B1810673
theorem B355159 : Blo 354756 355159 := bstep (se 1 (by rfl) ⟨266369, by rfl⟩ : syracuseStep 355159 = 532739) B532739
theorem B355179 : Blo 354756 355179 := bstep (se 1 (by rfl) ⟨266384, by rfl⟩ : syracuseStep 355179 = 532769) B532769
theorem B355191 : Blo 354756 355191 := bstep (se 1 (by rfl) ⟨266393, by rfl⟩ : syracuseStep 355191 = 532787) B532787
theorem B355211 : Blo 354756 355211 := bstep (se 1 (by rfl) ⟨266408, by rfl⟩ : syracuseStep 355211 = 532817) B532817
theorem B355223 : Blo 354756 355223 := bstep (se 1 (by rfl) ⟨266417, by rfl⟩ : syracuseStep 355223 = 532835) B532835
theorem B355243 : Blo 354756 355243 := bstep (se 1 (by rfl) ⟨266432, by rfl⟩ : syracuseStep 355243 = 532865) B532865
theorem B13003697 : Blo 354756 13003697 := bstep (se 2 (by rfl) ⟨4876386, by rfl⟩ : syracuseStep 13003697 = 9752773) B9752773
theorem B355255 : Blo 354756 355255 := bstep (se 1 (by rfl) ⟨266441, by rfl⟩ : syracuseStep 355255 = 532883) B532883
theorem B355275 : Blo 354756 355275 := bstep (se 1 (by rfl) ⟨266456, by rfl⟩ : syracuseStep 355275 = 532913) B532913
theorem B682967 : Blo 354756 682967 := bstep (se 1 (by rfl) ⟨512225, by rfl⟩ : syracuseStep 682967 = 1024451) B1024451
theorem B355287 : Blo 354756 355287 := bstep (se 1 (by rfl) ⟨266465, by rfl⟩ : syracuseStep 355287 = 532931) B532931
theorem B355307 : Blo 354756 355307 := bstep (se 1 (by rfl) ⟨266480, by rfl⟩ : syracuseStep 355307 = 532961) B532961
theorem B355319 : Blo 354756 355319 := bstep (se 1 (by rfl) ⟨266489, by rfl⟩ : syracuseStep 355319 = 532979) B532979
theorem B355339 : Blo 354756 355339 := bstep (se 1 (by rfl) ⟨266504, by rfl⟩ : syracuseStep 355339 = 533009) B533009
theorem B355351 : Blo 354756 355351 := bstep (se 1 (by rfl) ⟨266513, by rfl⟩ : syracuseStep 355351 = 533027) B533027
theorem B355371 : Blo 354756 355371 := bstep (se 1 (by rfl) ⟨266528, by rfl⟩ : syracuseStep 355371 = 533057) B533057
theorem B355383 : Blo 354756 355383 := bstep (se 1 (by rfl) ⟨266537, by rfl⟩ : syracuseStep 355383 = 533075) B533075
theorem B355403 : Blo 354756 355403 := bstep (se 1 (by rfl) ⟨266552, by rfl⟩ : syracuseStep 355403 = 533105) B533105
theorem B355415 : Blo 354756 355415 := bstep (se 1 (by rfl) ⟨266561, by rfl⟩ : syracuseStep 355415 = 533123) B533123
theorem B1207385 : Blo 354756 1207385 := bstep (se 2 (by rfl) ⟨452769, by rfl⟩ : syracuseStep 1207385 = 905539) B905539
theorem B355435 : Blo 354756 355435 := bstep (se 1 (by rfl) ⟨266576, by rfl⟩ : syracuseStep 355435 = 533153) B533153
theorem B355447 : Blo 354756 355447 := bstep (se 1 (by rfl) ⟨266585, by rfl⟩ : syracuseStep 355447 = 533171) B533171
theorem B355467 : Blo 354756 355467 := bstep (se 1 (by rfl) ⟨266600, by rfl⟩ : syracuseStep 355467 = 533201) B533201
theorem B1010839 : Blo 354756 1010839 := bstep (se 1 (by rfl) ⟨758129, by rfl⟩ : syracuseStep 1010839 = 1516259) B1516259
theorem B355479 : Blo 354756 355479 := bstep (se 1 (by rfl) ⟨266609, by rfl⟩ : syracuseStep 355479 = 533219) B533219
theorem B355499 : Blo 354756 355499 := bstep (se 1 (by rfl) ⟨266624, by rfl⟩ : syracuseStep 355499 = 533249) B533249
theorem B355511 : Blo 354756 355511 := bstep (se 1 (by rfl) ⟨266633, by rfl⟩ : syracuseStep 355511 = 533267) B533267
theorem B355531 : Blo 354756 355531 := bstep (se 1 (by rfl) ⟨266648, by rfl⟩ : syracuseStep 355531 = 533297) B533297
theorem B355543 : Blo 354756 355543 := bstep (se 1 (by rfl) ⟨266657, by rfl⟩ : syracuseStep 355543 = 533315) B533315
theorem B355563 : Blo 354756 355563 := bstep (se 1 (by rfl) ⟨266672, by rfl⟩ : syracuseStep 355563 = 533345) B533345
theorem B355575 : Blo 354756 355575 := bstep (se 1 (by rfl) ⟨266681, by rfl⟩ : syracuseStep 355575 = 533363) B533363
theorem B355595 : Blo 354756 355595 := bstep (se 1 (by rfl) ⟨266696, by rfl⟩ : syracuseStep 355595 = 533393) B533393
theorem B355607 : Blo 354756 355607 := bstep (se 1 (by rfl) ⟨266705, by rfl⟩ : syracuseStep 355607 = 533411) B533411
theorem B355627 : Blo 354756 355627 := bstep (se 1 (by rfl) ⟨266720, by rfl⟩ : syracuseStep 355627 = 533441) B533441
theorem B355639 : Blo 354756 355639 := bstep (se 1 (by rfl) ⟨266729, by rfl⟩ : syracuseStep 355639 = 533459) B533459
theorem B355659 : Blo 354756 355659 := bstep (se 1 (by rfl) ⟨266744, by rfl⟩ : syracuseStep 355659 = 533489) B533489
theorem B355671 : Blo 354756 355671 := bstep (se 1 (by rfl) ⟨266753, by rfl⟩ : syracuseStep 355671 = 533507) B533507
theorem B355691 : Blo 354756 355691 := bstep (se 1 (by rfl) ⟨266768, by rfl⟩ : syracuseStep 355691 = 533537) B533537
theorem B355703 : Blo 354756 355703 := bstep (se 1 (by rfl) ⟨266777, by rfl⟩ : syracuseStep 355703 = 533555) B533555
theorem B355723 : Blo 354756 355723 := bstep (se 1 (by rfl) ⟨266792, by rfl⟩ : syracuseStep 355723 = 533585) B533585
theorem B355735 : Blo 354756 355735 := bstep (se 1 (by rfl) ⟨266801, by rfl⟩ : syracuseStep 355735 = 533603) B533603
theorem B355755 : Blo 354756 355755 := bstep (se 1 (by rfl) ⟨266816, by rfl⟩ : syracuseStep 355755 = 533633) B533633
theorem B355767 : Blo 354756 355767 := bstep (se 1 (by rfl) ⟨266825, by rfl⟩ : syracuseStep 355767 = 533651) B533651
theorem B355787 : Blo 354756 355787 := bstep (se 1 (by rfl) ⟨266840, by rfl⟩ : syracuseStep 355787 = 533681) B533681
theorem B355799 : Blo 354756 355799 := bstep (se 1 (by rfl) ⟨266849, by rfl⟩ : syracuseStep 355799 = 533699) B533699
theorem B355819 : Blo 354756 355819 := bstep (se 1 (by rfl) ⟨266864, by rfl⟩ : syracuseStep 355819 = 533729) B533729
theorem B355831 : Blo 354756 355831 := bstep (se 1 (by rfl) ⟨266873, by rfl⟩ : syracuseStep 355831 = 533747) B533747
theorem B355851 : Blo 354756 355851 := bstep (se 1 (by rfl) ⟨266888, by rfl⟩ : syracuseStep 355851 = 533777) B533777
theorem B355863 : Blo 354756 355863 := bstep (se 1 (by rfl) ⟨266897, by rfl⟩ : syracuseStep 355863 = 533795) B533795
theorem B355883 : Blo 354756 355883 := bstep (se 1 (by rfl) ⟨266912, by rfl⟩ : syracuseStep 355883 = 533825) B533825
theorem B355895 : Blo 354756 355895 := bstep (se 1 (by rfl) ⟨266921, by rfl⟩ : syracuseStep 355895 = 533843) B533843
theorem B912971 : Blo 354756 912971 := bstep (se 1 (by rfl) ⟨684728, by rfl⟩ : syracuseStep 912971 = 1369457) B1369457
theorem B355915 : Blo 354756 355915 := bstep (se 1 (by rfl) ⟨266936, by rfl⟩ : syracuseStep 355915 = 533873) B533873
theorem B355927 : Blo 354756 355927 := bstep (se 1 (by rfl) ⟨266945, by rfl⟩ : syracuseStep 355927 = 533891) B533891
theorem B355947 : Blo 354756 355947 := bstep (se 1 (by rfl) ⟨266960, by rfl⟩ : syracuseStep 355947 = 533921) B533921
theorem B355959 : Blo 354756 355959 := bstep (se 1 (by rfl) ⟨266969, by rfl⟩ : syracuseStep 355959 = 533939) B533939
theorem B355979 : Blo 354756 355979 := bstep (se 1 (by rfl) ⟨266984, by rfl⟩ : syracuseStep 355979 = 533969) B533969
theorem B355991 : Blo 354756 355991 := bstep (se 1 (by rfl) ⟨266993, by rfl⟩ : syracuseStep 355991 = 533987) B533987
theorem B356011 : Blo 354756 356011 := bstep (se 1 (by rfl) ⟨267008, by rfl⟩ : syracuseStep 356011 = 534017) B534017
theorem B356023 : Blo 354756 356023 := bstep (se 1 (by rfl) ⟨267017, by rfl⟩ : syracuseStep 356023 = 534035) B534035
theorem B356043 : Blo 354756 356043 := bstep (se 1 (by rfl) ⟨267032, by rfl⟩ : syracuseStep 356043 = 534065) B534065
theorem B356055 : Blo 354756 356055 := bstep (se 1 (by rfl) ⟨267041, by rfl⟩ : syracuseStep 356055 = 534083) B534083
theorem B356075 : Blo 354756 356075 := bstep (se 1 (by rfl) ⟨267056, by rfl⟩ : syracuseStep 356075 = 534113) B534113
theorem B356087 : Blo 354756 356087 := bstep (se 1 (by rfl) ⟨267065, by rfl⟩ : syracuseStep 356087 = 534131) B534131
theorem B356107 : Blo 354756 356107 := bstep (se 1 (by rfl) ⟨267080, by rfl⟩ : syracuseStep 356107 = 534161) B534161
theorem B356119 : Blo 354756 356119 := bstep (se 1 (by rfl) ⟨267089, by rfl⟩ : syracuseStep 356119 = 534179) B534179
theorem B1208087 : Blo 354756 1208087 := bstep (se 1 (by rfl) ⟨906065, by rfl⟩ : syracuseStep 1208087 = 1812131) B1812131
theorem B356139 : Blo 354756 356139 := bstep (se 1 (by rfl) ⟨267104, by rfl⟩ : syracuseStep 356139 = 534209) B534209
theorem B356151 : Blo 354756 356151 := bstep (se 1 (by rfl) ⟨267113, by rfl⟩ : syracuseStep 356151 = 534227) B534227
theorem B356171 : Blo 354756 356171 := bstep (se 1 (by rfl) ⟨267128, by rfl⟩ : syracuseStep 356171 = 534257) B534257
theorem B356183 : Blo 354756 356183 := bstep (se 1 (by rfl) ⟨267137, by rfl⟩ : syracuseStep 356183 = 534275) B534275
theorem B2879333 : Blo 354756 2879333 := bstep (se 4 (by rfl) ⟨269937, by rfl⟩ : syracuseStep 2879333 = 539875) B539875
theorem B356203 : Blo 354756 356203 := bstep (se 1 (by rfl) ⟨267152, by rfl⟩ : syracuseStep 356203 = 534305) B534305
theorem B356215 : Blo 354756 356215 := bstep (se 1 (by rfl) ⟨267161, by rfl⟩ : syracuseStep 356215 = 534323) B534323
theorem B356235 : Blo 354756 356235 := bstep (se 1 (by rfl) ⟨267176, by rfl⟩ : syracuseStep 356235 = 534353) B534353
theorem B356247 : Blo 354756 356247 := bstep (se 1 (by rfl) ⟨267185, by rfl⟩ : syracuseStep 356247 = 534371) B534371
theorem B356267 : Blo 354756 356267 := bstep (se 1 (by rfl) ⟨267200, by rfl⟩ : syracuseStep 356267 = 534401) B534401
theorem B356279 : Blo 354756 356279 := bstep (se 1 (by rfl) ⟨267209, by rfl⟩ : syracuseStep 356279 = 534419) B534419
theorem B356299 : Blo 354756 356299 := bstep (se 1 (by rfl) ⟨267224, by rfl⟩ : syracuseStep 356299 = 534449) B534449
theorem B356311 : Blo 354756 356311 := bstep (se 1 (by rfl) ⟨267233, by rfl⟩ : syracuseStep 356311 = 534467) B534467
theorem B356331 : Blo 354756 356331 := bstep (se 1 (by rfl) ⟨267248, by rfl⟩ : syracuseStep 356331 = 534497) B534497
theorem B356343 : Blo 354756 356343 := bstep (se 1 (by rfl) ⟨267257, by rfl⟩ : syracuseStep 356343 = 534515) B534515
theorem B356363 : Blo 354756 356363 := bstep (se 1 (by rfl) ⟨267272, by rfl⟩ : syracuseStep 356363 = 534545) B534545
theorem B356375 : Blo 354756 356375 := bstep (se 1 (by rfl) ⟨267281, by rfl⟩ : syracuseStep 356375 = 534563) B534563
theorem B356395 : Blo 354756 356395 := bstep (se 1 (by rfl) ⟨267296, by rfl⟩ : syracuseStep 356395 = 534593) B534593
theorem B356407 : Blo 354756 356407 := bstep (se 1 (by rfl) ⟨267305, by rfl⟩ : syracuseStep 356407 = 534611) B534611
theorem B356427 : Blo 354756 356427 := bstep (se 1 (by rfl) ⟨267320, by rfl⟩ : syracuseStep 356427 = 534641) B534641
theorem B356439 : Blo 354756 356439 := bstep (se 1 (by rfl) ⟨267329, by rfl⟩ : syracuseStep 356439 = 534659) B534659
theorem B356459 : Blo 354756 356459 := bstep (se 1 (by rfl) ⟨267344, by rfl⟩ : syracuseStep 356459 = 534689) B534689
theorem B356471 : Blo 354756 356471 := bstep (se 1 (by rfl) ⟨267353, by rfl⟩ : syracuseStep 356471 = 534707) B534707
theorem B4124803 : Blo 354756 4124803 := bstep (se 1 (by rfl) ⟨3093602, by rfl⟩ : syracuseStep 4124803 = 6187205) B6187205
theorem B356491 : Blo 354756 356491 := bstep (se 1 (by rfl) ⟨267368, by rfl⟩ : syracuseStep 356491 = 534737) B534737
theorem B356503 : Blo 354756 356503 := bstep (se 1 (by rfl) ⟨267377, by rfl⟩ : syracuseStep 356503 = 534755) B534755
theorem B356523 : Blo 354756 356523 := bstep (se 1 (by rfl) ⟨267392, by rfl⟩ : syracuseStep 356523 = 534785) B534785
theorem B356535 : Blo 354756 356535 := bstep (se 1 (by rfl) ⟨267401, by rfl⟩ : syracuseStep 356535 = 534803) B534803
theorem B356555 : Blo 354756 356555 := bstep (se 1 (by rfl) ⟨267416, by rfl⟩ : syracuseStep 356555 = 534833) B534833
theorem B356567 : Blo 354756 356567 := bstep (se 1 (by rfl) ⟨267425, by rfl⟩ : syracuseStep 356567 = 534851) B534851
theorem B1798361 : Blo 354756 1798361 := bstep (se 2 (by rfl) ⟨674385, by rfl⟩ : syracuseStep 1798361 = 1348771) B1348771
theorem B356587 : Blo 354756 356587 := bstep (se 1 (by rfl) ⟨267440, by rfl⟩ : syracuseStep 356587 = 534881) B534881
theorem B356599 : Blo 354756 356599 := bstep (se 1 (by rfl) ⟨267449, by rfl⟩ : syracuseStep 356599 = 534899) B534899
theorem B356619 : Blo 354756 356619 := bstep (se 1 (by rfl) ⟨267464, by rfl⟩ : syracuseStep 356619 = 534929) B534929
theorem B356631 : Blo 354756 356631 := bstep (se 1 (by rfl) ⟨267473, by rfl⟩ : syracuseStep 356631 = 534947) B534947
theorem B356651 : Blo 354756 356651 := bstep (se 1 (by rfl) ⟨267488, by rfl⟩ : syracuseStep 356651 = 534977) B534977
theorem B1208627 : Blo 354756 1208627 := bstep (se 1 (by rfl) ⟨906470, by rfl⟩ : syracuseStep 1208627 = 1812941) B1812941
theorem B356663 : Blo 354756 356663 := bstep (se 1 (by rfl) ⟨267497, by rfl⟩ : syracuseStep 356663 = 534995) B534995
theorem B913739 : Blo 354756 913739 := bstep (se 1 (by rfl) ⟨685304, by rfl⟩ : syracuseStep 913739 = 1370609) B1370609
theorem B356683 : Blo 354756 356683 := bstep (se 1 (by rfl) ⟨267512, by rfl⟩ : syracuseStep 356683 = 535025) B535025
theorem B2289995 : Blo 354756 2289995 := bstep (se 1 (by rfl) ⟨1717496, by rfl⟩ : syracuseStep 2289995 = 3434993) B3434993
theorem B356695 : Blo 354756 356695 := bstep (se 1 (by rfl) ⟨267521, by rfl⟩ : syracuseStep 356695 = 535043) B535043
theorem B356715 : Blo 354756 356715 := bstep (se 1 (by rfl) ⟨267536, by rfl⟩ : syracuseStep 356715 = 535073) B535073
theorem B356727 : Blo 354756 356727 := bstep (se 1 (by rfl) ⟨267545, by rfl⟩ : syracuseStep 356727 = 535091) B535091
theorem B356747 : Blo 354756 356747 := bstep (se 1 (by rfl) ⟨267560, by rfl⟩ : syracuseStep 356747 = 535121) B535121
theorem B356759 : Blo 354756 356759 := bstep (se 1 (by rfl) ⟨267569, by rfl⟩ : syracuseStep 356759 = 535139) B535139
theorem B356779 : Blo 354756 356779 := bstep (se 1 (by rfl) ⟨267584, by rfl⟩ : syracuseStep 356779 = 535169) B535169
theorem B356791 : Blo 354756 356791 := bstep (se 1 (by rfl) ⟨267593, by rfl⟩ : syracuseStep 356791 = 535187) B535187
theorem B1012171 : Blo 354756 1012171 := bstep (se 1 (by rfl) ⟨759128, by rfl⟩ : syracuseStep 1012171 = 1518257) B1518257
theorem B356811 : Blo 354756 356811 := bstep (se 1 (by rfl) ⟨267608, by rfl⟩ : syracuseStep 356811 = 535217) B535217
theorem B356823 : Blo 354756 356823 := bstep (se 1 (by rfl) ⟨267617, by rfl⟩ : syracuseStep 356823 = 535235) B535235
theorem B356843 : Blo 354756 356843 := bstep (se 1 (by rfl) ⟨267632, by rfl⟩ : syracuseStep 356843 = 535265) B535265
theorem B356855 : Blo 354756 356855 := bstep (se 1 (by rfl) ⟨267641, by rfl⟩ : syracuseStep 356855 = 535283) B535283
theorem B356875 : Blo 354756 356875 := bstep (se 1 (by rfl) ⟨267656, by rfl⟩ : syracuseStep 356875 = 535313) B535313
theorem B356887 : Blo 354756 356887 := bstep (se 1 (by rfl) ⟨267665, by rfl⟩ : syracuseStep 356887 = 535331) B535331
theorem B356907 : Blo 354756 356907 := bstep (se 1 (by rfl) ⟨267680, by rfl⟩ : syracuseStep 356907 = 535361) B535361
theorem B1372717 : Blo 354756 1372717 := bstep (se 3 (by rfl) ⟨257384, by rfl⟩ : syracuseStep 1372717 = 514769) B514769
theorem B356919 : Blo 354756 356919 := bstep (se 1 (by rfl) ⟨267689, by rfl⟩ : syracuseStep 356919 = 535379) B535379
theorem B1208897 : Blo 354756 1208897 := bstep (se 2 (by rfl) ⟨453336, by rfl⟩ : syracuseStep 1208897 = 906673) B906673
theorem B356939 : Blo 354756 356939 := bstep (se 1 (by rfl) ⟨267704, by rfl⟩ : syracuseStep 356939 = 535409) B535409
theorem B356951 : Blo 354756 356951 := bstep (se 1 (by rfl) ⟨267713, by rfl⟩ : syracuseStep 356951 = 535427) B535427
theorem B2716253 : Blo 354756 2716253 := bstep (se 3 (by rfl) ⟨509297, by rfl⟩ : syracuseStep 2716253 = 1018595) B1018595
theorem B356971 : Blo 354756 356971 := bstep (se 1 (by rfl) ⟨267728, by rfl⟩ : syracuseStep 356971 = 535457) B535457
theorem B356983 : Blo 354756 356983 := bstep (se 1 (by rfl) ⟨267737, by rfl⟩ : syracuseStep 356983 = 535475) B535475
theorem B357003 : Blo 354756 357003 := bstep (se 1 (by rfl) ⟨267752, by rfl⟩ : syracuseStep 357003 = 535505) B535505
theorem B357015 : Blo 354756 357015 := bstep (se 1 (by rfl) ⟨267761, by rfl⟩ : syracuseStep 357015 = 535523) B535523
theorem B357035 : Blo 354756 357035 := bstep (se 1 (by rfl) ⟨267776, by rfl⟩ : syracuseStep 357035 = 535553) B535553
theorem B357047 : Blo 354756 357047 := bstep (se 1 (by rfl) ⟨267785, by rfl⟩ : syracuseStep 357047 = 535571) B535571
theorem B357067 : Blo 354756 357067 := bstep (se 1 (by rfl) ⟨267800, by rfl⟩ : syracuseStep 357067 = 535601) B535601
theorem B357079 : Blo 354756 357079 := bstep (se 1 (by rfl) ⟨267809, by rfl⟩ : syracuseStep 357079 = 535619) B535619
theorem B1012445 : Blo 354756 1012445 := bstep (se 3 (by rfl) ⟨189833, by rfl⟩ : syracuseStep 1012445 = 379667) B379667
theorem B357099 : Blo 354756 357099 := bstep (se 1 (by rfl) ⟨267824, by rfl⟩ : syracuseStep 357099 = 535649) B535649
theorem B357111 : Blo 354756 357111 := bstep (se 1 (by rfl) ⟨267833, by rfl⟩ : syracuseStep 357111 = 535667) B535667
theorem B357131 : Blo 354756 357131 := bstep (se 1 (by rfl) ⟨267848, by rfl⟩ : syracuseStep 357131 = 535697) B535697
theorem B357143 : Blo 354756 357143 := bstep (se 1 (by rfl) ⟨267857, by rfl⟩ : syracuseStep 357143 = 535715) B535715
theorem B357163 : Blo 354756 357163 := bstep (se 1 (by rfl) ⟨267872, by rfl⟩ : syracuseStep 357163 = 535745) B535745
theorem B2159405 : Blo 354756 2159405 := bstep (se 3 (by rfl) ⟨404888, by rfl⟩ : syracuseStep 2159405 = 809777) B809777
theorem B357175 : Blo 354756 357175 := bstep (se 1 (by rfl) ⟨267881, by rfl⟩ : syracuseStep 357175 = 535763) B535763
theorem B357195 : Blo 354756 357195 := bstep (se 1 (by rfl) ⟨267896, by rfl⟩ : syracuseStep 357195 = 535793) B535793
theorem B357207 : Blo 354756 357207 := bstep (se 1 (by rfl) ⟨267905, by rfl⟩ : syracuseStep 357207 = 535811) B535811
theorem B357227 : Blo 354756 357227 := bstep (se 1 (by rfl) ⟨267920, by rfl⟩ : syracuseStep 357227 = 535841) B535841
theorem B357239 : Blo 354756 357239 := bstep (se 1 (by rfl) ⟨267929, by rfl⟩ : syracuseStep 357239 = 535859) B535859
theorem B357259 : Blo 354756 357259 := bstep (se 1 (by rfl) ⟨267944, by rfl⟩ : syracuseStep 357259 = 535889) B535889
theorem B357271 : Blo 354756 357271 := bstep (se 1 (by rfl) ⟨267953, by rfl⟩ : syracuseStep 357271 = 535907) B535907
theorem B357291 : Blo 354756 357291 := bstep (se 1 (by rfl) ⟨267968, by rfl⟩ : syracuseStep 357291 = 535937) B535937
theorem B357303 : Blo 354756 357303 := bstep (se 1 (by rfl) ⟨267977, by rfl⟩ : syracuseStep 357303 = 535955) B535955
theorem B685003 : Blo 354756 685003 := bstep (se 1 (by rfl) ⟨513752, by rfl⟩ : syracuseStep 685003 = 1027505) B1027505
theorem B357323 : Blo 354756 357323 := bstep (se 1 (by rfl) ⟨267992, by rfl⟩ : syracuseStep 357323 = 535985) B535985
theorem B357335 : Blo 354756 357335 := bstep (se 1 (by rfl) ⟨268001, by rfl⟩ : syracuseStep 357335 = 536003) B536003
theorem B357355 : Blo 354756 357355 := bstep (se 1 (by rfl) ⟨268016, by rfl⟩ : syracuseStep 357355 = 536033) B536033
theorem B357367 : Blo 354756 357367 := bstep (se 1 (by rfl) ⟨268025, by rfl⟩ : syracuseStep 357367 = 536051) B536051
theorem B783361 : Blo 354756 783361 := bstep (se 2 (by rfl) ⟨293760, by rfl⟩ : syracuseStep 783361 = 587521) B587521
theorem B357387 : Blo 354756 357387 := bstep (se 1 (by rfl) ⟨268040, by rfl⟩ : syracuseStep 357387 = 536081) B536081
theorem B357399 : Blo 354756 357399 := bstep (se 1 (by rfl) ⟨268049, by rfl⟩ : syracuseStep 357399 = 536099) B536099
theorem B357419 : Blo 354756 357419 := bstep (se 1 (by rfl) ⟨268064, by rfl⟩ : syracuseStep 357419 = 536129) B536129
theorem B1012787 : Blo 354756 1012787 := bstep (se 1 (by rfl) ⟨759590, by rfl⟩ : syracuseStep 1012787 = 1519181) B1519181
theorem B357431 : Blo 354756 357431 := bstep (se 1 (by rfl) ⟨268073, by rfl⟩ : syracuseStep 357431 = 536147) B536147
theorem B357451 : Blo 354756 357451 := bstep (se 1 (by rfl) ⟨268088, by rfl⟩ : syracuseStep 357451 = 536177) B536177
theorem B357463 : Blo 354756 357463 := bstep (se 1 (by rfl) ⟨268097, by rfl⟩ : syracuseStep 357463 = 536195) B536195
theorem B1209437 : Blo 354756 1209437 := bstep (se 3 (by rfl) ⟨226769, by rfl⟩ : syracuseStep 1209437 = 453539) B453539
theorem B357483 : Blo 354756 357483 := bstep (se 1 (by rfl) ⟨268112, by rfl⟩ : syracuseStep 357483 = 536225) B536225
theorem B357495 : Blo 354756 357495 := bstep (se 1 (by rfl) ⟨268121, by rfl⟩ : syracuseStep 357495 = 536243) B536243
theorem B357515 : Blo 354756 357515 := bstep (se 1 (by rfl) ⟨268136, by rfl⟩ : syracuseStep 357515 = 536273) B536273
theorem B357527 : Blo 354756 357527 := bstep (se 1 (by rfl) ⟨268145, by rfl⟩ : syracuseStep 357527 = 536291) B536291
theorem B357547 : Blo 354756 357547 := bstep (se 1 (by rfl) ⟨268160, by rfl⟩ : syracuseStep 357547 = 536321) B536321
theorem B357559 : Blo 354756 357559 := bstep (se 1 (by rfl) ⟨268169, by rfl⟩ : syracuseStep 357559 = 536339) B536339
theorem B357579 : Blo 354756 357579 := bstep (se 1 (by rfl) ⟨268184, by rfl⟩ : syracuseStep 357579 = 536369) B536369
theorem B357591 : Blo 354756 357591 := bstep (se 1 (by rfl) ⟨268193, by rfl⟩ : syracuseStep 357591 = 536387) B536387
theorem B357611 : Blo 354756 357611 := bstep (se 1 (by rfl) ⟨268208, by rfl⟩ : syracuseStep 357611 = 536417) B536417
theorem B357623 : Blo 354756 357623 := bstep (se 1 (by rfl) ⟨268217, by rfl⟩ : syracuseStep 357623 = 536435) B536435
theorem B357643 : Blo 354756 357643 := bstep (se 1 (by rfl) ⟨268232, by rfl⟩ : syracuseStep 357643 = 536465) B536465
theorem B357655 : Blo 354756 357655 := bstep (se 1 (by rfl) ⟨268241, by rfl⟩ : syracuseStep 357655 = 536483) B536483
theorem B357675 : Blo 354756 357675 := bstep (se 1 (by rfl) ⟨268256, by rfl⟩ : syracuseStep 357675 = 536513) B536513
theorem B357687 : Blo 354756 357687 := bstep (se 1 (by rfl) ⟨268265, by rfl⟩ : syracuseStep 357687 = 536531) B536531
theorem B357707 : Blo 354756 357707 := bstep (se 1 (by rfl) ⟨268280, by rfl⟩ : syracuseStep 357707 = 536561) B536561
theorem B357719 : Blo 354756 357719 := bstep (se 1 (by rfl) ⟨268289, by rfl⟩ : syracuseStep 357719 = 536579) B536579
theorem B357739 : Blo 354756 357739 := bstep (se 1 (by rfl) ⟨268304, by rfl⟩ : syracuseStep 357739 = 536609) B536609
theorem B357751 : Blo 354756 357751 := bstep (se 1 (by rfl) ⟨268313, by rfl⟩ : syracuseStep 357751 = 536627) B536627
theorem B357771 : Blo 354756 357771 := bstep (se 1 (by rfl) ⟨268328, by rfl⟩ : syracuseStep 357771 = 536657) B536657
theorem B357783 : Blo 354756 357783 := bstep (se 1 (by rfl) ⟨268337, by rfl⟩ : syracuseStep 357783 = 536675) B536675
theorem B357803 : Blo 354756 357803 := bstep (se 1 (by rfl) ⟨268352, by rfl⟩ : syracuseStep 357803 = 536705) B536705
theorem B357815 : Blo 354756 357815 := bstep (se 1 (by rfl) ⟨268361, by rfl⟩ : syracuseStep 357815 = 536723) B536723
theorem B357835 : Blo 354756 357835 := bstep (se 1 (by rfl) ⟨268376, by rfl⟩ : syracuseStep 357835 = 536753) B536753
theorem B357847 : Blo 354756 357847 := bstep (se 1 (by rfl) ⟨268385, by rfl⟩ : syracuseStep 357847 = 536771) B536771
theorem B357867 : Blo 354756 357867 := bstep (se 1 (by rfl) ⟨268400, by rfl⟩ : syracuseStep 357867 = 536801) B536801
theorem B357879 : Blo 354756 357879 := bstep (se 1 (by rfl) ⟨268409, by rfl⟩ : syracuseStep 357879 = 536819) B536819
theorem B357899 : Blo 354756 357899 := bstep (se 1 (by rfl) ⟨268424, by rfl⟩ : syracuseStep 357899 = 536849) B536849
theorem B357911 : Blo 354756 357911 := bstep (se 1 (by rfl) ⟨268433, by rfl⟩ : syracuseStep 357911 = 536867) B536867
theorem B357931 : Blo 354756 357931 := bstep (se 1 (by rfl) ⟨268448, by rfl⟩ : syracuseStep 357931 = 536897) B536897
theorem B357943 : Blo 354756 357943 := bstep (se 1 (by rfl) ⟨268457, by rfl⟩ : syracuseStep 357943 = 536915) B536915
theorem B357963 : Blo 354756 357963 := bstep (se 1 (by rfl) ⟨268472, by rfl⟩ : syracuseStep 357963 = 536945) B536945
theorem B357975 : Blo 354756 357975 := bstep (se 1 (by rfl) ⟨268481, by rfl⟩ : syracuseStep 357975 = 536963) B536963
theorem B357995 : Blo 354756 357995 := bstep (se 1 (by rfl) ⟨268496, by rfl⟩ : syracuseStep 357995 = 536993) B536993
theorem B358007 : Blo 354756 358007 := bstep (se 1 (by rfl) ⟨268505, by rfl⟩ : syracuseStep 358007 = 537011) B537011
theorem B358027 : Blo 354756 358027 := bstep (se 1 (by rfl) ⟨268520, by rfl⟩ : syracuseStep 358027 = 537041) B537041
theorem B358039 : Blo 354756 358039 := bstep (se 1 (by rfl) ⟨268529, by rfl⟩ : syracuseStep 358039 = 537059) B537059
theorem B358059 : Blo 354756 358059 := bstep (se 1 (by rfl) ⟨268544, by rfl⟩ : syracuseStep 358059 = 537089) B537089
theorem B358071 : Blo 354756 358071 := bstep (se 1 (by rfl) ⟨268553, by rfl⟩ : syracuseStep 358071 = 537107) B537107
theorem B358091 : Blo 354756 358091 := bstep (se 1 (by rfl) ⟨268568, by rfl⟩ : syracuseStep 358091 = 537137) B537137
theorem B358103 : Blo 354756 358103 := bstep (se 1 (by rfl) ⟨268577, by rfl⟩ : syracuseStep 358103 = 537155) B537155
theorem B358123 : Blo 354756 358123 := bstep (se 1 (by rfl) ⟨268592, by rfl⟩ : syracuseStep 358123 = 537185) B537185
theorem B358135 : Blo 354756 358135 := bstep (se 1 (by rfl) ⟨268601, by rfl⟩ : syracuseStep 358135 = 537203) B537203
theorem B358155 : Blo 354756 358155 := bstep (se 1 (by rfl) ⟨268616, by rfl⟩ : syracuseStep 358155 = 537233) B537233
theorem B358167 : Blo 354756 358167 := bstep (se 1 (by rfl) ⟨268625, by rfl⟩ : syracuseStep 358167 = 537251) B537251
theorem B358187 : Blo 354756 358187 := bstep (se 1 (by rfl) ⟨268640, by rfl⟩ : syracuseStep 358187 = 537281) B537281
theorem B1799981 : Blo 354756 1799981 := bstep (se 3 (by rfl) ⟨337496, by rfl⟩ : syracuseStep 1799981 = 674993) B674993
theorem B358199 : Blo 354756 358199 := bstep (se 1 (by rfl) ⟨268649, by rfl⟩ : syracuseStep 358199 = 537299) B537299
theorem B358219 : Blo 354756 358219 := bstep (se 1 (by rfl) ⟨268664, by rfl⟩ : syracuseStep 358219 = 537329) B537329
theorem B358231 : Blo 354756 358231 := bstep (se 1 (by rfl) ⟨268673, by rfl⟩ : syracuseStep 358231 = 537347) B537347
theorem B358251 : Blo 354756 358251 := bstep (se 1 (by rfl) ⟨268688, by rfl⟩ : syracuseStep 358251 = 537377) B537377
theorem B358263 : Blo 354756 358263 := bstep (se 1 (by rfl) ⟨268697, by rfl⟩ : syracuseStep 358263 = 537395) B537395
theorem B358283 : Blo 354756 358283 := bstep (se 1 (by rfl) ⟨268712, by rfl⟩ : syracuseStep 358283 = 537425) B537425
theorem B358295 : Blo 354756 358295 := bstep (se 1 (by rfl) ⟨268721, by rfl⟩ : syracuseStep 358295 = 537443) B537443
theorem B358315 : Blo 354756 358315 := bstep (se 1 (by rfl) ⟨268736, by rfl⟩ : syracuseStep 358315 = 537473) B537473
theorem B358327 : Blo 354756 358327 := bstep (se 1 (by rfl) ⟨268745, by rfl⟩ : syracuseStep 358327 = 537491) B537491
theorem B358347 : Blo 354756 358347 := bstep (se 1 (by rfl) ⟨268760, by rfl⟩ : syracuseStep 358347 = 537521) B537521
theorem B358359 : Blo 354756 358359 := bstep (se 1 (by rfl) ⟨268769, by rfl⟩ : syracuseStep 358359 = 537539) B537539
theorem B1144793 : Blo 354756 1144793 := bstep (se 2 (by rfl) ⟨429297, by rfl⟩ : syracuseStep 1144793 = 858595) B858595
theorem B358379 : Blo 354756 358379 := bstep (se 1 (by rfl) ⟨268784, by rfl⟩ : syracuseStep 358379 = 537569) B537569
theorem B358391 : Blo 354756 358391 := bstep (se 1 (by rfl) ⟨268793, by rfl⟩ : syracuseStep 358391 = 537587) B537587
theorem B358411 : Blo 354756 358411 := bstep (se 1 (by rfl) ⟨268808, by rfl⟩ : syracuseStep 358411 = 537617) B537617
theorem B358423 : Blo 354756 358423 := bstep (se 1 (by rfl) ⟨268817, by rfl⟩ : syracuseStep 358423 = 537635) B537635
theorem B358443 : Blo 354756 358443 := bstep (se 1 (by rfl) ⟨268832, by rfl⟩ : syracuseStep 358443 = 537665) B537665
theorem B358455 : Blo 354756 358455 := bstep (se 1 (by rfl) ⟨268841, by rfl⟩ : syracuseStep 358455 = 537683) B537683
theorem B358475 : Blo 354756 358475 := bstep (se 1 (by rfl) ⟨268856, by rfl⟩ : syracuseStep 358475 = 537713) B537713
theorem B358487 : Blo 354756 358487 := bstep (se 1 (by rfl) ⟨268865, by rfl⟩ : syracuseStep 358487 = 537731) B537731
theorem B358507 : Blo 354756 358507 := bstep (se 1 (by rfl) ⟨268880, by rfl⟩ : syracuseStep 358507 = 537761) B537761
theorem B358519 : Blo 354756 358519 := bstep (se 1 (by rfl) ⟨268889, by rfl⟩ : syracuseStep 358519 = 537779) B537779
theorem B358539 : Blo 354756 358539 := bstep (se 1 (by rfl) ⟨268904, by rfl⟩ : syracuseStep 358539 = 537809) B537809
theorem B1374353 : Blo 354756 1374353 := bstep (se 2 (by rfl) ⟨515382, by rfl⟩ : syracuseStep 1374353 = 1030765) B1030765
theorem B358551 : Blo 354756 358551 := bstep (se 1 (by rfl) ⟨268913, by rfl⟩ : syracuseStep 358551 = 537827) B537827
theorem B358571 : Blo 354756 358571 := bstep (se 1 (by rfl) ⟨268928, by rfl⟩ : syracuseStep 358571 = 537857) B537857
theorem B6092981 : Blo 354756 6092981 := bstep (se 5 (by rfl) ⟨285608, by rfl⟩ : syracuseStep 6092981 = 571217) B571217
theorem B358583 : Blo 354756 358583 := bstep (se 1 (by rfl) ⟨268937, by rfl⟩ : syracuseStep 358583 = 537875) B537875
theorem B358603 : Blo 354756 358603 := bstep (se 1 (by rfl) ⟨268952, by rfl⟩ : syracuseStep 358603 = 537905) B537905
theorem B1210571 : Blo 354756 1210571 := bstep (se 1 (by rfl) ⟨907928, by rfl⟩ : syracuseStep 1210571 = 1815857) B1815857
theorem B358615 : Blo 354756 358615 := bstep (se 1 (by rfl) ⟨268961, by rfl⟩ : syracuseStep 358615 = 537923) B537923
theorem B358635 : Blo 354756 358635 := bstep (se 1 (by rfl) ⟨268976, by rfl⟩ : syracuseStep 358635 = 537953) B537953
theorem B358647 : Blo 354756 358647 := bstep (se 1 (by rfl) ⟨268985, by rfl⟩ : syracuseStep 358647 = 537971) B537971
theorem B358667 : Blo 354756 358667 := bstep (se 1 (by rfl) ⟨269000, by rfl⟩ : syracuseStep 358667 = 538001) B538001
theorem B358679 : Blo 354756 358679 := bstep (se 1 (by rfl) ⟨269009, by rfl⟩ : syracuseStep 358679 = 538019) B538019
theorem B358699 : Blo 354756 358699 := bstep (se 1 (by rfl) ⟨269024, by rfl⟩ : syracuseStep 358699 = 538049) B538049
theorem B11794733 : Blo 354756 11794733 := bstep (se 3 (by rfl) ⟨2211512, by rfl⟩ : syracuseStep 11794733 = 4423025) B4423025
theorem B358711 : Blo 354756 358711 := bstep (se 1 (by rfl) ⟨269033, by rfl⟩ : syracuseStep 358711 = 538067) B538067
theorem B358731 : Blo 354756 358731 := bstep (se 1 (by rfl) ⟨269048, by rfl⟩ : syracuseStep 358731 = 538097) B538097
theorem B358743 : Blo 354756 358743 := bstep (se 1 (by rfl) ⟨269057, by rfl⟩ : syracuseStep 358743 = 538115) B538115
theorem B1440089 : Blo 354756 1440089 := bstep (se 2 (by rfl) ⟨540033, by rfl⟩ : syracuseStep 1440089 = 1080067) B1080067
theorem B719219 : Blo 354756 719219 := bstep (se 1 (by rfl) ⟨539414, by rfl⟩ : syracuseStep 719219 = 1078829) B1078829
theorem B2750851 : Blo 354756 2750851 := bstep (se 1 (by rfl) ⟨2063138, by rfl⟩ : syracuseStep 2750851 = 4126277) B4126277
theorem B883289 : Blo 354756 883289 := bstep (se 2 (by rfl) ⟨331233, by rfl⟩ : syracuseStep 883289 = 662467) B662467
theorem B457367 : Blo 354756 457367 := bstep (se 1 (by rfl) ⟨343025, by rfl⟩ : syracuseStep 457367 = 686051) B686051
theorem B817879 : Blo 354756 817879 := bstep (se 1 (by rfl) ⟨613409, by rfl⟩ : syracuseStep 817879 = 1226819) B1226819
theorem B1080139 : Blo 354756 1080139 := bstep (se 1 (by rfl) ⟨810104, by rfl⟩ : syracuseStep 1080139 = 1620209) B1620209
theorem B1014859 : Blo 354756 1014859 := bstep (se 1 (by rfl) ⟨761144, by rfl⟩ : syracuseStep 1014859 = 1522289) B1522289
theorem B3865751 : Blo 354756 3865751 := bstep (se 1 (by rfl) ⟨2899313, by rfl⟩ : syracuseStep 3865751 = 5798627) B5798627
theorem B1015361 : Blo 354756 1015361 := bstep (se 2 (by rfl) ⟨380760, by rfl⟩ : syracuseStep 1015361 = 761521) B761521
theorem B1146433 : Blo 354756 1146433 := bstep (se 2 (by rfl) ⟨429912, by rfl⟩ : syracuseStep 1146433 = 859825) B859825
theorem B2293379 : Blo 354756 2293379 := bstep (se 1 (by rfl) ⟨1720034, by rfl⟩ : syracuseStep 2293379 = 3440069) B3440069
theorem B1015703 : Blo 354756 1015703 := bstep (se 1 (by rfl) ⟨761777, by rfl⟩ : syracuseStep 1015703 = 1523555) B1523555
theorem B1441729 : Blo 354756 1441729 := bstep (se 2 (by rfl) ⟨540648, by rfl⟩ : syracuseStep 1441729 = 1081297) B1081297
theorem B720929 : Blo 354756 720929 := bstep (se 2 (by rfl) ⟨270348, by rfl⟩ : syracuseStep 720929 = 540697) B540697
theorem B1835095 : Blo 354756 1835095 := bstep (se 1 (by rfl) ⟨1376321, by rfl⟩ : syracuseStep 1835095 = 2752643) B2752643
theorem B2031905 : Blo 354756 2031905 := bstep (se 2 (by rfl) ⟨761964, by rfl⟩ : syracuseStep 2031905 = 1523929) B1523929
theorem B1016363 : Blo 354756 1016363 := bstep (se 1 (by rfl) ⟨762272, by rfl⟩ : syracuseStep 1016363 = 1524545) B1524545
theorem B1081943 : Blo 354756 1081943 := bstep (se 1 (by rfl) ⟨811457, by rfl⟩ : syracuseStep 1081943 = 1622915) B1622915
theorem B4326007 : Blo 354756 4326007 := bstep (se 1 (by rfl) ⟨3244505, by rfl⟩ : syracuseStep 4326007 = 6489011) B6489011
theorem B3670721 : Blo 354756 3670721 := bstep (se 2 (by rfl) ⟨1376520, by rfl⟩ : syracuseStep 3670721 = 2753041) B2753041
theorem B1803059 : Blo 354756 1803059 := bstep (se 1 (by rfl) ⟨1352294, by rfl⟩ : syracuseStep 1803059 = 2704589) B2704589
theorem B1082173 : Blo 354756 1082173 := bstep (se 3 (by rfl) ⟨202907, by rfl⟩ : syracuseStep 1082173 = 405815) B405815
theorem B2720627 : Blo 354756 2720627 := bstep (se 1 (by rfl) ⟨2040470, by rfl⟩ : syracuseStep 2720627 = 4080941) B4080941
theorem B1082429 : Blo 354756 1082429 := bstep (se 3 (by rfl) ⟨202955, by rfl⟩ : syracuseStep 1082429 = 405911) B405911
theorem B1803383 : Blo 354756 1803383 := bstep (se 1 (by rfl) ⟨1352537, by rfl⟩ : syracuseStep 1803383 = 2705075) B2705075
theorem B1443415 : Blo 354756 1443415 := bstep (se 1 (by rfl) ⟨1082561, by rfl⟩ : syracuseStep 1443415 = 2165123) B2165123
theorem B4196069 : Blo 354756 4196069 := bstep (se 4 (by rfl) ⟨393381, by rfl⟩ : syracuseStep 4196069 = 786763) B786763
theorem B2197547 : Blo 354756 2197547 := bstep (se 1 (by rfl) ⟨1648160, by rfl⟩ : syracuseStep 2197547 = 3296321) B3296321
theorem B1804355 : Blo 354756 1804355 := bstep (se 1 (by rfl) ⟨1353266, by rfl⟩ : syracuseStep 1804355 = 2706533) B2706533
theorem B1018003 : Blo 354756 1018003 := bstep (se 1 (by rfl) ⟨763502, by rfl⟩ : syracuseStep 1018003 = 1527005) B1527005
theorem B1706255 : Blo 354756 1706255 := bstep (se 1 (by rfl) ⟨1279691, by rfl⟩ : syracuseStep 1706255 = 2559383) B2559383
theorem B1804679 : Blo 354756 1804679 := bstep (se 1 (by rfl) ⟨1353509, by rfl⟩ : syracuseStep 1804679 = 2707019) B2707019
theorem B461611 : Blo 354756 461611 := bstep (se 1 (by rfl) ⟨346208, by rfl⟩ : syracuseStep 461611 = 692417) B692417
theorem B363323 : Blo 354756 363323 := bstep (se 1 (by rfl) ⟨272492, by rfl⟩ : syracuseStep 363323 = 544985) B544985
theorem B11537315 : Blo 354756 11537315 := bstep (se 1 (by rfl) ⟨8652986, by rfl⟩ : syracuseStep 11537315 = 17305973) B17305973
theorem B428971 : Blo 354756 428971 := bstep (se 1 (by rfl) ⟨321728, by rfl⟩ : syracuseStep 428971 = 643457) B643457
theorem B12946493 : Blo 354756 12946493 := bstep (se 3 (by rfl) ⟨2427467, by rfl⟩ : syracuseStep 12946493 = 4854935) B4854935
theorem B2297069 : Blo 354756 2297069 := bstep (se 3 (by rfl) ⟨430700, by rfl⟩ : syracuseStep 2297069 = 861401) B861401
theorem B2035003 : Blo 354756 2035003 := bstep (se 1 (by rfl) ⟨1526252, by rfl⟩ : syracuseStep 2035003 = 3052505) B3052505
theorem B1347101 : Blo 354756 1347101 := bstep (se 3 (by rfl) ⟨252581, by rfl⟩ : syracuseStep 1347101 = 505163) B505163
theorem B1085129 : Blo 354756 1085129 := bstep (se 2 (by rfl) ⟨406923, by rfl⟩ : syracuseStep 1085129 = 813847) B813847
theorem B1019735 : Blo 354756 1019735 := bstep (se 1 (by rfl) ⟨764801, by rfl⟩ : syracuseStep 1019735 = 1529603) B1529603
theorem B1347785 : Blo 354756 1347785 := bstep (se 2 (by rfl) ⟨505419, by rfl⟩ : syracuseStep 1347785 = 1010839) B1010839
theorem B1085783 : Blo 354756 1085783 := bstep (se 1 (by rfl) ⟨814337, by rfl⟩ : syracuseStep 1085783 = 1628675) B1628675
theorem B2036461 : Blo 354756 2036461 := bstep (se 3 (by rfl) ⟨381836, by rfl⟩ : syracuseStep 2036461 = 763673) B763673
theorem B1283309 : Blo 354756 1283309 := bstep (se 3 (by rfl) ⟨240620, by rfl⟩ : syracuseStep 1283309 = 481241) B481241
theorem B7968131 : Blo 354756 7968131 := bstep (se 1 (by rfl) ⟨5976098, by rfl⟩ : syracuseStep 7968131 = 11952197) B11952197
theorem B1021319 : Blo 354756 1021319 := bstep (se 1 (by rfl) ⟨765989, by rfl⟩ : syracuseStep 1021319 = 1531979) B1531979
theorem B3872323 : Blo 354756 3872323 := bstep (se 1 (by rfl) ⟨2904242, by rfl⟩ : syracuseStep 3872323 = 5808485) B5808485
theorem B399163 : Blo 354756 399163 := bstep (se 1 (by rfl) ⟨299372, by rfl⟩ : syracuseStep 399163 = 598745) B598745
theorem B1808243 : Blo 354756 1808243 := bstep (se 1 (by rfl) ⟨1356182, by rfl⟩ : syracuseStep 1808243 = 2712365) B2712365
theorem B1349561 : Blo 354756 1349561 := bstep (se 2 (by rfl) ⟨506085, by rfl⟩ : syracuseStep 1349561 = 1012171) B1012171
theorem B923663 : Blo 354756 923663 := bstep (se 1 (by rfl) ⟨692747, by rfl⟩ : syracuseStep 923663 = 1385495) B1385495
theorem B399631 : Blo 354756 399631 := bstep (se 1 (by rfl) ⟨299723, by rfl⟩ : syracuseStep 399631 = 599447) B599447
theorem B2169139 : Blo 354756 2169139 := bstep (se 1 (by rfl) ⟨1626854, by rfl⟩ : syracuseStep 2169139 = 3253709) B3253709
theorem B1808729 : Blo 354756 1808729 := bstep (se 2 (by rfl) ⟨678273, by rfl⟩ : syracuseStep 1808729 = 1356547) B1356547
theorem B2038445 : Blo 354756 2038445 := bstep (se 3 (by rfl) ⟨382208, by rfl⟩ : syracuseStep 2038445 = 764417) B764417
theorem B367291 : Blo 354756 367291 := bstep (se 1 (by rfl) ⟨275468, by rfl⟩ : syracuseStep 367291 = 550937) B550937
theorem B400135 : Blo 354756 400135 := bstep (se 1 (by rfl) ⟨300101, by rfl⟩ : syracuseStep 400135 = 600203) B600203
theorem B1284923 : Blo 354756 1284923 := bstep (se 1 (by rfl) ⟨963692, by rfl⟩ : syracuseStep 1284923 = 1927385) B1927385
theorem B400315 : Blo 354756 400315 := bstep (se 1 (by rfl) ⟨300236, by rfl⟩ : syracuseStep 400315 = 600473) B600473
theorem B1711115 : Blo 354756 1711115 := bstep (se 1 (by rfl) ⟨1283336, by rfl⟩ : syracuseStep 1711115 = 2566673) B2566673
theorem B1219645 : Blo 354756 1219645 := bstep (se 3 (by rfl) ⟨228683, by rfl⟩ : syracuseStep 1219645 = 457367) B457367
theorem B62594309 : Blo 354756 62594309 := bstep (se 4 (by rfl) ⟨5868216, by rfl⟩ : syracuseStep 62594309 = 11736433) B11736433
theorem B859403 : Blo 354756 859403 := bstep (se 1 (by rfl) ⟨644552, by rfl⟩ : syracuseStep 859403 = 1289105) B1289105
theorem B400783 : Blo 354756 400783 := bstep (se 1 (by rfl) ⟨300587, by rfl⟩ : syracuseStep 400783 = 601175) B601175
theorem B532139 : Blo 354756 532139 := bstep (se 1 (by rfl) ⟨399104, by rfl⟩ : syracuseStep 532139 = 798209) B798209
theorem B532169 : Blo 354756 532169 := bstep (se 2 (by rfl) ⟨199563, by rfl⟩ : syracuseStep 532169 = 399127) B399127
theorem B2170597 : Blo 354756 2170597 := bstep (se 4 (by rfl) ⟨203493, by rfl⟩ : syracuseStep 2170597 = 406987) B406987
theorem B34676525 : Blo 354756 34676525 := bstep (se 3 (by rfl) ⟨6501848, by rfl⟩ : syracuseStep 34676525 = 13003697) B13003697
theorem B532283 : Blo 354756 532283 := bstep (se 1 (by rfl) ⟨399212, by rfl⟩ : syracuseStep 532283 = 798425) B798425
theorem B1711961 : Blo 354756 1711961 := bstep (se 2 (by rfl) ⟨641985, by rfl⟩ : syracuseStep 1711961 = 1283971) B1283971
theorem B532343 : Blo 354756 532343 := bstep (se 1 (by rfl) ⟨399257, by rfl⟩ : syracuseStep 532343 = 798515) B798515
theorem B401287 : Blo 354756 401287 := bstep (se 1 (by rfl) ⟨300965, by rfl⟩ : syracuseStep 401287 = 601931) B601931
theorem B532367 : Blo 354756 532367 := bstep (se 1 (by rfl) ⟨399275, by rfl⟩ : syracuseStep 532367 = 798551) B798551
theorem B532409 : Blo 354756 532409 := bstep (se 2 (by rfl) ⟨199653, by rfl⟩ : syracuseStep 532409 = 399307) B399307
theorem B532487 : Blo 354756 532487 := bstep (se 1 (by rfl) ⟨399365, by rfl⟩ : syracuseStep 532487 = 798731) B798731
theorem B532523 : Blo 354756 532523 := bstep (se 1 (by rfl) ⟨399392, by rfl⟩ : syracuseStep 532523 = 798785) B798785
theorem B401467 : Blo 354756 401467 := bstep (se 1 (by rfl) ⟨301100, by rfl⟩ : syracuseStep 401467 = 602201) B602201
theorem B532553 : Blo 354756 532553 := bstep (se 2 (by rfl) ⟨199707, by rfl⟩ : syracuseStep 532553 = 399415) B399415
theorem B532667 : Blo 354756 532667 := bstep (se 1 (by rfl) ⟨399500, by rfl⟩ : syracuseStep 532667 = 799001) B799001
theorem B532727 : Blo 354756 532727 := bstep (se 1 (by rfl) ⟨399545, by rfl⟩ : syracuseStep 532727 = 799091) B799091
theorem B532751 : Blo 354756 532751 := bstep (se 1 (by rfl) ⟨399563, by rfl⟩ : syracuseStep 532751 = 799127) B799127
theorem B532793 : Blo 354756 532793 := bstep (se 2 (by rfl) ⟨199797, by rfl⟩ : syracuseStep 532793 = 399595) B399595
theorem B532871 : Blo 354756 532871 := bstep (se 1 (by rfl) ⟨399653, by rfl⟩ : syracuseStep 532871 = 799307) B799307
theorem B17375633 : Blo 354756 17375633 := bstep (se 2 (by rfl) ⟨6515862, by rfl⟩ : syracuseStep 17375633 = 13031725) B13031725
theorem B1810835 : Blo 354756 1810835 := bstep (se 1 (by rfl) ⟨1358126, by rfl⟩ : syracuseStep 1810835 = 2716253) B2716253
theorem B532907 : Blo 354756 532907 := bstep (se 1 (by rfl) ⟨399680, by rfl⟩ : syracuseStep 532907 = 799361) B799361
theorem B532937 : Blo 354756 532937 := bstep (se 2 (by rfl) ⟨199851, by rfl⟩ : syracuseStep 532937 = 399703) B399703
theorem B401935 : Blo 354756 401935 := bstep (se 1 (by rfl) ⟨301451, by rfl⟩ : syracuseStep 401935 = 602903) B602903
theorem B533051 : Blo 354756 533051 := bstep (se 1 (by rfl) ⟨399788, by rfl⟩ : syracuseStep 533051 = 799577) B799577
theorem B533111 : Blo 354756 533111 := bstep (se 1 (by rfl) ⟨399833, by rfl⟩ : syracuseStep 533111 = 799667) B799667
theorem B533135 : Blo 354756 533135 := bstep (se 1 (by rfl) ⟨399851, by rfl⟩ : syracuseStep 533135 = 799703) B799703
theorem B533177 : Blo 354756 533177 := bstep (se 2 (by rfl) ⟨199941, by rfl⟩ : syracuseStep 533177 = 399883) B399883
theorem B4072193 : Blo 354756 4072193 := bstep (se 2 (by rfl) ⟨1527072, by rfl⟩ : syracuseStep 4072193 = 3054145) B3054145
theorem B533255 : Blo 354756 533255 := bstep (se 1 (by rfl) ⟨399941, by rfl⟩ : syracuseStep 533255 = 799883) B799883
theorem B598799 : Blo 354756 598799 := bstep (se 1 (by rfl) ⟨449099, by rfl⟩ : syracuseStep 598799 = 898199) B898199
theorem B533291 : Blo 354756 533291 := bstep (se 1 (by rfl) ⟨399968, by rfl⟩ : syracuseStep 533291 = 799937) B799937
theorem B533321 : Blo 354756 533321 := bstep (se 2 (by rfl) ⟨199995, by rfl⟩ : syracuseStep 533321 = 399991) B399991
theorem B533435 : Blo 354756 533435 := bstep (se 1 (by rfl) ⟨400076, by rfl⟩ : syracuseStep 533435 = 800153) B800153
theorem B1090505 : Blo 354756 1090505 := bstep (se 2 (by rfl) ⟨408939, by rfl⟩ : syracuseStep 1090505 = 817879) B817879
theorem B533495 : Blo 354756 533495 := bstep (se 1 (by rfl) ⟨400121, by rfl⟩ : syracuseStep 533495 = 800243) B800243
theorem B2040835 : Blo 354756 2040835 := bstep (se 1 (by rfl) ⟨1530626, by rfl⟩ : syracuseStep 2040835 = 3061253) B3061253
theorem B402439 : Blo 354756 402439 := bstep (se 1 (by rfl) ⟨301829, by rfl⟩ : syracuseStep 402439 = 603659) B603659
theorem B533519 : Blo 354756 533519 := bstep (se 1 (by rfl) ⟨400139, by rfl⟩ : syracuseStep 533519 = 800279) B800279
theorem B533561 : Blo 354756 533561 := bstep (se 2 (by rfl) ⟨200085, by rfl⟩ : syracuseStep 533561 = 400171) B400171
theorem B6628439 : Blo 354756 6628439 := bstep (se 1 (by rfl) ⟨4971329, by rfl⟩ : syracuseStep 6628439 = 9942659) B9942659
theorem B533639 : Blo 354756 533639 := bstep (se 1 (by rfl) ⟨400229, by rfl⟩ : syracuseStep 533639 = 800459) B800459
theorem B533675 : Blo 354756 533675 := bstep (se 1 (by rfl) ⟨400256, by rfl⟩ : syracuseStep 533675 = 800513) B800513
theorem B402619 : Blo 354756 402619 := bstep (se 1 (by rfl) ⟨301964, by rfl⟩ : syracuseStep 402619 = 603929) B603929
theorem B533705 : Blo 354756 533705 := bstep (se 2 (by rfl) ⟨200139, by rfl⟩ : syracuseStep 533705 = 400279) B400279
theorem B599339 : Blo 354756 599339 := bstep (se 1 (by rfl) ⟨449504, by rfl⟩ : syracuseStep 599339 = 899009) B899009
theorem B533819 : Blo 354756 533819 := bstep (se 1 (by rfl) ⟨400364, by rfl⟩ : syracuseStep 533819 = 800729) B800729
theorem B763195 : Blo 354756 763195 := bstep (se 1 (by rfl) ⟨572396, by rfl⟩ : syracuseStep 763195 = 1144793) B1144793
theorem B533879 : Blo 354756 533879 := bstep (se 1 (by rfl) ⟨400409, by rfl⟩ : syracuseStep 533879 = 800819) B800819
theorem B533903 : Blo 354756 533903 := bstep (se 1 (by rfl) ⟨400427, by rfl⟩ : syracuseStep 533903 = 800855) B800855
theorem B533945 : Blo 354756 533945 := bstep (se 2 (by rfl) ⟨200229, by rfl⟩ : syracuseStep 533945 = 400459) B400459
theorem B1353145 : Blo 354756 1353145 := bstep (se 2 (by rfl) ⟨507429, by rfl⟩ : syracuseStep 1353145 = 1014859) B1014859
theorem B534023 : Blo 354756 534023 := bstep (se 1 (by rfl) ⟨400517, by rfl⟩ : syracuseStep 534023 = 801035) B801035
theorem B534059 : Blo 354756 534059 := bstep (se 1 (by rfl) ⟨400544, by rfl⟩ : syracuseStep 534059 = 801089) B801089
theorem B960059 : Blo 354756 960059 := bstep (se 1 (by rfl) ⟨720044, by rfl⟩ : syracuseStep 960059 = 1440089) B1440089
theorem B534089 : Blo 354756 534089 := bstep (se 2 (by rfl) ⟨200283, by rfl⟩ : syracuseStep 534089 = 400567) B400567
theorem B861815 : Blo 354756 861815 := bstep (se 1 (by rfl) ⟨646361, by rfl⟩ : syracuseStep 861815 = 1292723) B1292723
theorem B403087 : Blo 354756 403087 := bstep (se 1 (by rfl) ⟨302315, by rfl⟩ : syracuseStep 403087 = 604631) B604631
theorem B599737 : Blo 354756 599737 := bstep (se 2 (by rfl) ⟨224901, by rfl⟩ : syracuseStep 599737 = 449803) B449803
theorem B534203 : Blo 354756 534203 := bstep (se 1 (by rfl) ⟨400652, by rfl⟩ : syracuseStep 534203 = 801305) B801305
theorem B534263 : Blo 354756 534263 := bstep (se 1 (by rfl) ⟨400697, by rfl⟩ : syracuseStep 534263 = 801395) B801395
theorem B534287 : Blo 354756 534287 := bstep (se 1 (by rfl) ⟨400715, by rfl⟩ : syracuseStep 534287 = 801431) B801431
theorem B534329 : Blo 354756 534329 := bstep (se 2 (by rfl) ⟨200373, by rfl⟩ : syracuseStep 534329 = 400747) B400747
theorem B534407 : Blo 354756 534407 := bstep (se 1 (by rfl) ⟨400805, by rfl⟩ : syracuseStep 534407 = 801611) B801611
theorem B534443 : Blo 354756 534443 := bstep (se 1 (by rfl) ⟨400832, by rfl⟩ : syracuseStep 534443 = 801665) B801665
theorem B534473 : Blo 354756 534473 := bstep (se 2 (by rfl) ⟨200427, by rfl⟩ : syracuseStep 534473 = 400855) B400855
theorem B534587 : Blo 354756 534587 := bstep (se 1 (by rfl) ⟨400940, by rfl⟩ : syracuseStep 534587 = 801881) B801881
theorem B534647 : Blo 354756 534647 := bstep (se 1 (by rfl) ⟨400985, by rfl⟩ : syracuseStep 534647 = 801971) B801971
theorem B403591 : Blo 354756 403591 := bstep (se 1 (by rfl) ⟨302693, by rfl⟩ : syracuseStep 403591 = 605387) B605387
theorem B534671 : Blo 354756 534671 := bstep (se 1 (by rfl) ⟨401003, by rfl⟩ : syracuseStep 534671 = 802007) B802007
theorem B534713 : Blo 354756 534713 := bstep (se 2 (by rfl) ⟨200517, by rfl⟩ : syracuseStep 534713 = 401035) B401035
theorem B534791 : Blo 354756 534791 := bstep (se 1 (by rfl) ⟨401093, by rfl⟩ : syracuseStep 534791 = 802187) B802187
theorem B534827 : Blo 354756 534827 := bstep (se 1 (by rfl) ⟨401120, by rfl⟩ : syracuseStep 534827 = 802241) B802241
theorem B534857 : Blo 354756 534857 := bstep (se 2 (by rfl) ⟨200571, by rfl⟩ : syracuseStep 534857 = 401143) B401143
theorem B600439 : Blo 354756 600439 := bstep (se 1 (by rfl) ⟨450329, by rfl⟩ : syracuseStep 600439 = 900659) B900659
theorem B534971 : Blo 354756 534971 := bstep (se 1 (by rfl) ⟨401228, by rfl⟩ : syracuseStep 534971 = 802457) B802457
theorem B535031 : Blo 354756 535031 := bstep (se 1 (by rfl) ⟨401273, by rfl⟩ : syracuseStep 535031 = 802547) B802547
theorem B535055 : Blo 354756 535055 := bstep (se 1 (by rfl) ⟨401291, by rfl⟩ : syracuseStep 535055 = 802583) B802583
theorem B535097 : Blo 354756 535097 := bstep (se 2 (by rfl) ⟨200661, by rfl⟩ : syracuseStep 535097 = 401323) B401323
theorem B600635 : Blo 354756 600635 := bstep (se 1 (by rfl) ⟨450476, by rfl⟩ : syracuseStep 600635 = 900953) B900953
theorem B535175 : Blo 354756 535175 := bstep (se 1 (by rfl) ⟨401381, by rfl⟩ : syracuseStep 535175 = 802763) B802763
theorem B535211 : Blo 354756 535211 := bstep (se 1 (by rfl) ⟨401408, by rfl⟩ : syracuseStep 535211 = 802817) B802817
theorem B535241 : Blo 354756 535241 := bstep (se 2 (by rfl) ⟨200715, by rfl⟩ : syracuseStep 535241 = 401431) B401431
theorem B6859525 : Blo 354756 6859525 := bstep (se 4 (by rfl) ⟨643080, by rfl⟩ : syracuseStep 6859525 = 1286161) B1286161
theorem B535355 : Blo 354756 535355 := bstep (se 1 (by rfl) ⟨401516, by rfl⟩ : syracuseStep 535355 = 803033) B803033
theorem B535415 : Blo 354756 535415 := bstep (se 1 (by rfl) ⟨401561, by rfl⟩ : syracuseStep 535415 = 803123) B803123
theorem B535439 : Blo 354756 535439 := bstep (se 1 (by rfl) ⟨401579, by rfl⟩ : syracuseStep 535439 = 803159) B803159
theorem B535481 : Blo 354756 535481 := bstep (se 2 (by rfl) ⟨200805, by rfl⟩ : syracuseStep 535481 = 401611) B401611
theorem B601033 : Blo 354756 601033 := bstep (se 2 (by rfl) ⟨225387, by rfl⟩ : syracuseStep 601033 = 450775) B450775
theorem B535559 : Blo 354756 535559 := bstep (se 1 (by rfl) ⟨401669, by rfl⟩ : syracuseStep 535559 = 803339) B803339
theorem B535595 : Blo 354756 535595 := bstep (se 1 (by rfl) ⟨401696, by rfl⟩ : syracuseStep 535595 = 803393) B803393
theorem B961595 : Blo 354756 961595 := bstep (se 1 (by rfl) ⟨721196, by rfl⟩ : syracuseStep 961595 = 1442393) B1442393
theorem B535625 : Blo 354756 535625 := bstep (se 2 (by rfl) ⟨200859, by rfl⟩ : syracuseStep 535625 = 401719) B401719
theorem B535739 : Blo 354756 535739 := bstep (se 1 (by rfl) ⟨401804, by rfl⟩ : syracuseStep 535739 = 803609) B803609
theorem B535799 : Blo 354756 535799 := bstep (se 1 (by rfl) ⟨401849, by rfl⟩ : syracuseStep 535799 = 803699) B803699
theorem B535823 : Blo 354756 535823 := bstep (se 1 (by rfl) ⟨401867, by rfl⟩ : syracuseStep 535823 = 803735) B803735
theorem B535865 : Blo 354756 535865 := bstep (se 2 (by rfl) ⟨200949, by rfl⟩ : syracuseStep 535865 = 401899) B401899
theorem B961853 : Blo 354756 961853 := bstep (se 3 (by rfl) ⟨180347, by rfl⟩ : syracuseStep 961853 = 360695) B360695
theorem B535943 : Blo 354756 535943 := bstep (se 1 (by rfl) ⟨401957, by rfl⟩ : syracuseStep 535943 = 803915) B803915
theorem B1813913 : Blo 354756 1813913 := bstep (se 2 (by rfl) ⟨680217, by rfl⟩ : syracuseStep 1813913 = 1360435) B1360435
theorem B535979 : Blo 354756 535979 := bstep (se 1 (by rfl) ⟨401984, by rfl⟩ : syracuseStep 535979 = 803969) B803969
theorem B536009 : Blo 354756 536009 := bstep (se 2 (by rfl) ⟨201003, by rfl⟩ : syracuseStep 536009 = 402007) B402007
theorem B2436637 : Blo 354756 2436637 := bstep (se 3 (by rfl) ⟨456869, by rfl⟩ : syracuseStep 2436637 = 913739) B913739
theorem B536123 : Blo 354756 536123 := bstep (se 1 (by rfl) ⟨402092, by rfl⟩ : syracuseStep 536123 = 804185) B804185
theorem B4075109 : Blo 354756 4075109 := bstep (se 4 (by rfl) ⟨382041, by rfl⟩ : syracuseStep 4075109 = 764083) B764083
theorem B2305655 : Blo 354756 2305655 := bstep (se 1 (by rfl) ⟨1729241, by rfl⟩ : syracuseStep 2305655 = 3458483) B3458483
theorem B536183 : Blo 354756 536183 := bstep (se 1 (by rfl) ⟨402137, by rfl⟩ : syracuseStep 536183 = 804275) B804275
theorem B601735 : Blo 354756 601735 := bstep (se 1 (by rfl) ⟨451301, by rfl⟩ : syracuseStep 601735 = 902603) B902603
theorem B536207 : Blo 354756 536207 := bstep (se 1 (by rfl) ⟨402155, by rfl⟩ : syracuseStep 536207 = 804311) B804311
theorem B765587 : Blo 354756 765587 := bstep (se 1 (by rfl) ⟨574190, by rfl⟩ : syracuseStep 765587 = 1148381) B1148381
theorem B536249 : Blo 354756 536249 := bstep (se 2 (by rfl) ⟨201093, by rfl⟩ : syracuseStep 536249 = 402187) B402187
theorem B536327 : Blo 354756 536327 := bstep (se 1 (by rfl) ⟨402245, by rfl⟩ : syracuseStep 536327 = 804491) B804491
theorem B798479 : Blo 354756 798479 := bstep (se 1 (by rfl) ⟨598859, by rfl⟩ : syracuseStep 798479 = 1197719) B1197719
theorem B798497 : Blo 354756 798497 := bstep (se 2 (by rfl) ⟨299436, by rfl⟩ : syracuseStep 798497 = 598873) B598873
theorem B536363 : Blo 354756 536363 := bstep (se 1 (by rfl) ⟨402272, by rfl⟩ : syracuseStep 536363 = 804545) B804545
theorem B536393 : Blo 354756 536393 := bstep (se 2 (by rfl) ⟨201147, by rfl⟩ : syracuseStep 536393 = 402295) B402295
theorem B405391 : Blo 354756 405391 := bstep (se 1 (by rfl) ⟨304043, by rfl⟩ : syracuseStep 405391 = 608087) B608087
theorem B536507 : Blo 354756 536507 := bstep (se 1 (by rfl) ⟨402380, by rfl⟩ : syracuseStep 536507 = 804761) B804761
theorem B536567 : Blo 354756 536567 := bstep (se 1 (by rfl) ⟨402425, by rfl⟩ : syracuseStep 536567 = 804851) B804851
theorem B634895 : Blo 354756 634895 := bstep (se 1 (by rfl) ⟨476171, by rfl⟩ : syracuseStep 634895 = 952343) B952343
theorem B536591 : Blo 354756 536591 := bstep (se 1 (by rfl) ⟨402443, by rfl⟩ : syracuseStep 536591 = 804887) B804887
theorem B536633 : Blo 354756 536633 := bstep (se 2 (by rfl) ⟨201237, by rfl⟩ : syracuseStep 536633 = 402475) B402475
theorem B1224791 : Blo 354756 1224791 := bstep (se 1 (by rfl) ⟨918593, by rfl⟩ : syracuseStep 1224791 = 1837187) B1837187
theorem B798839 : Blo 354756 798839 := bstep (se 1 (by rfl) ⟨599129, by rfl⟩ : syracuseStep 798839 = 1198259) B1198259
theorem B536711 : Blo 354756 536711 := bstep (se 1 (by rfl) ⟨402533, by rfl⟩ : syracuseStep 536711 = 805067) B805067
theorem B536747 : Blo 354756 536747 := bstep (se 1 (by rfl) ⟨402560, by rfl⟩ : syracuseStep 536747 = 805121) B805121
theorem B536777 : Blo 354756 536777 := bstep (se 2 (by rfl) ⟨201291, by rfl⟩ : syracuseStep 536777 = 402583) B402583
theorem B1716461 : Blo 354756 1716461 := bstep (se 3 (by rfl) ⟨321836, by rfl⟩ : syracuseStep 1716461 = 643673) B643673
theorem B602383 : Blo 354756 602383 := bstep (se 1 (by rfl) ⟨451787, by rfl⟩ : syracuseStep 602383 = 903575) B903575
theorem B1356047 : Blo 354756 1356047 := bstep (se 1 (by rfl) ⟨1017035, by rfl⟩ : syracuseStep 1356047 = 2034071) B2034071
theorem B799019 : Blo 354756 799019 := bstep (se 1 (by rfl) ⟨599264, by rfl⟩ : syracuseStep 799019 = 1198529) B1198529
theorem B536891 : Blo 354756 536891 := bstep (se 1 (by rfl) ⟨402668, by rfl⟩ : syracuseStep 536891 = 805337) B805337
theorem B536951 : Blo 354756 536951 := bstep (se 1 (by rfl) ⟨402713, by rfl⟩ : syracuseStep 536951 = 805427) B805427
theorem B536975 : Blo 354756 536975 := bstep (se 1 (by rfl) ⟨402731, by rfl⟩ : syracuseStep 536975 = 805463) B805463
theorem B537017 : Blo 354756 537017 := bstep (se 2 (by rfl) ⟨201381, by rfl⟩ : syracuseStep 537017 = 402763) B402763
theorem B2699729 : Blo 354756 2699729 := bstep (se 2 (by rfl) ⟨1012398, by rfl⟩ : syracuseStep 2699729 = 2024797) B2024797
theorem B537095 : Blo 354756 537095 := bstep (se 1 (by rfl) ⟨402821, by rfl⟩ : syracuseStep 537095 = 805643) B805643
theorem B2175511 : Blo 354756 2175511 := bstep (se 1 (by rfl) ⟨1631633, by rfl⟩ : syracuseStep 2175511 = 3263267) B3263267
theorem B1520171 : Blo 354756 1520171 := bstep (se 1 (by rfl) ⟨1140128, by rfl⟩ : syracuseStep 1520171 = 2280257) B2280257
theorem B537131 : Blo 354756 537131 := bstep (se 1 (by rfl) ⟨402848, by rfl⟩ : syracuseStep 537131 = 805697) B805697
theorem B6566467 : Blo 354756 6566467 := bstep (se 1 (by rfl) ⟨4924850, by rfl⟩ : syracuseStep 6566467 = 9849701) B9849701
theorem B537161 : Blo 354756 537161 := bstep (se 2 (by rfl) ⟨201435, by rfl⟩ : syracuseStep 537161 = 402871) B402871
theorem B799379 : Blo 354756 799379 := bstep (se 1 (by rfl) ⟨599534, by rfl⟩ : syracuseStep 799379 = 1199069) B1199069
theorem B537275 : Blo 354756 537275 := bstep (se 1 (by rfl) ⟨402956, by rfl⟩ : syracuseStep 537275 = 805913) B805913
theorem B799433 : Blo 354756 799433 := bstep (se 2 (by rfl) ⟨299787, by rfl⟩ : syracuseStep 799433 = 599575) B599575
theorem B537335 : Blo 354756 537335 := bstep (se 1 (by rfl) ⟨403001, by rfl⟩ : syracuseStep 537335 = 806003) B806003
theorem B537359 : Blo 354756 537359 := bstep (se 1 (by rfl) ⟨403019, by rfl⟩ : syracuseStep 537359 = 806039) B806039
theorem B602923 : Blo 354756 602923 := bstep (se 1 (by rfl) ⟨452192, by rfl⟩ : syracuseStep 602923 = 904385) B904385
theorem B537401 : Blo 354756 537401 := bstep (se 2 (by rfl) ⟨201525, by rfl⟩ : syracuseStep 537401 = 403051) B403051
theorem B537479 : Blo 354756 537479 := bstep (se 1 (by rfl) ⟨403109, by rfl⟩ : syracuseStep 537479 = 806219) B806219
theorem B537515 : Blo 354756 537515 := bstep (se 1 (by rfl) ⟨403136, by rfl⟩ : syracuseStep 537515 = 806273) B806273
theorem B603065 : Blo 354756 603065 := bstep (se 2 (by rfl) ⟨226149, by rfl⟩ : syracuseStep 603065 = 452299) B452299
theorem B537545 : Blo 354756 537545 := bstep (se 2 (by rfl) ⟨201579, by rfl⟩ : syracuseStep 537545 = 403159) B403159
theorem B4076567 : Blo 354756 4076567 := bstep (se 1 (by rfl) ⟨3057425, by rfl⟩ : syracuseStep 4076567 = 6114851) B6114851
theorem B1618973 : Blo 354756 1618973 := bstep (se 3 (by rfl) ⟨303557, by rfl⟩ : syracuseStep 1618973 = 607115) B607115
theorem B537659 : Blo 354756 537659 := bstep (se 1 (by rfl) ⟨403244, by rfl⟩ : syracuseStep 537659 = 806489) B806489
theorem B537719 : Blo 354756 537719 := bstep (se 1 (by rfl) ⟨403289, by rfl⟩ : syracuseStep 537719 = 806579) B806579
theorem B537743 : Blo 354756 537743 := bstep (se 1 (by rfl) ⟨403307, by rfl⟩ : syracuseStep 537743 = 806615) B806615
theorem B537785 : Blo 354756 537785 := bstep (se 2 (by rfl) ⟨201669, by rfl⟩ : syracuseStep 537785 = 403339) B403339
theorem B898249 : Blo 354756 898249 := bstep (se 2 (by rfl) ⟨336843, by rfl⟩ : syracuseStep 898249 = 673687) B673687
theorem B537863 : Blo 354756 537863 := bstep (se 1 (by rfl) ⟨403397, by rfl⟩ : syracuseStep 537863 = 806795) B806795
theorem B570667 : Blo 354756 570667 := bstep (se 1 (by rfl) ⟨428000, by rfl⟩ : syracuseStep 570667 = 856001) B856001
theorem B537899 : Blo 354756 537899 := bstep (se 1 (by rfl) ⟨403424, by rfl⟩ : syracuseStep 537899 = 806849) B806849
theorem B1029437 : Blo 354756 1029437 := bstep (se 3 (by rfl) ⟨193019, by rfl⟩ : syracuseStep 1029437 = 386039) B386039
theorem B537929 : Blo 354756 537929 := bstep (se 2 (by rfl) ⟨201723, by rfl⟩ : syracuseStep 537929 = 403447) B403447
theorem B898391 : Blo 354756 898391 := bstep (se 1 (by rfl) ⟨673793, by rfl⟩ : syracuseStep 898391 = 1347587) B1347587
theorem B800135 : Blo 354756 800135 := bstep (se 1 (by rfl) ⟨600101, by rfl⟩ : syracuseStep 800135 = 1200203) B1200203
theorem B538043 : Blo 354756 538043 := bstep (se 1 (by rfl) ⟨403532, by rfl⟩ : syracuseStep 538043 = 807065) B807065
theorem B538103 : Blo 354756 538103 := bstep (se 1 (by rfl) ⟨403577, by rfl⟩ : syracuseStep 538103 = 807155) B807155
theorem B538127 : Blo 354756 538127 := bstep (se 1 (by rfl) ⟨403595, by rfl⟩ : syracuseStep 538127 = 807191) B807191
theorem B1095227 : Blo 354756 1095227 := bstep (se 1 (by rfl) ⟨821420, by rfl⟩ : syracuseStep 1095227 = 1642841) B1642841
theorem B800315 : Blo 354756 800315 := bstep (se 1 (by rfl) ⟨600236, by rfl⟩ : syracuseStep 800315 = 1200473) B1200473
theorem B603767 : Blo 354756 603767 := bstep (se 1 (by rfl) ⟨452825, by rfl⟩ : syracuseStep 603767 = 905651) B905651
theorem B800441 : Blo 354756 800441 := bstep (se 2 (by rfl) ⟨300165, by rfl⟩ : syracuseStep 800441 = 600331) B600331
theorem B3421925 : Blo 354756 3421925 := bstep (se 4 (by rfl) ⟨320805, by rfl⟩ : syracuseStep 3421925 = 641611) B641611
theorem B505607 : Blo 354756 505607 := bstep (se 1 (by rfl) ⟨379205, by rfl⟩ : syracuseStep 505607 = 758411) B758411
theorem B5125963 : Blo 354756 5125963 := bstep (se 1 (by rfl) ⟨3844472, by rfl⟩ : syracuseStep 5125963 = 7688945) B7688945
theorem B505801 : Blo 354756 505801 := bstep (se 2 (by rfl) ⟨189675, by rfl⟩ : syracuseStep 505801 = 379351) B379351
theorem B800783 : Blo 354756 800783 := bstep (se 1 (by rfl) ⟨600587, by rfl⟩ : syracuseStep 800783 = 1201175) B1201175
theorem B800801 : Blo 354756 800801 := bstep (se 2 (by rfl) ⟨300300, by rfl⟩ : syracuseStep 800801 = 600601) B600601
theorem B604219 : Blo 354756 604219 := bstep (se 1 (by rfl) ⟨453164, by rfl⟩ : syracuseStep 604219 = 906329) B906329
theorem B604361 : Blo 354756 604361 := bstep (se 2 (by rfl) ⟨226635, by rfl⟩ : syracuseStep 604361 = 453271) B453271
theorem B56342897 : Blo 354756 56342897 := bstep (se 2 (by rfl) ⟨21128586, by rfl⟩ : syracuseStep 56342897 = 42257173) B42257173
theorem B801143 : Blo 354756 801143 := bstep (se 1 (by rfl) ⟨600857, by rfl⟩ : syracuseStep 801143 = 1201715) B1201715
theorem B506359 : Blo 354756 506359 := bstep (se 1 (by rfl) ⟨379769, by rfl⟩ : syracuseStep 506359 = 759539) B759539
theorem B3258883 : Blo 354756 3258883 := bstep (se 1 (by rfl) ⟨2444162, by rfl⟩ : syracuseStep 3258883 = 4888325) B4888325
theorem B801323 : Blo 354756 801323 := bstep (se 1 (by rfl) ⟨600992, by rfl⟩ : syracuseStep 801323 = 1201985) B1201985
theorem B572089 : Blo 354756 572089 := bstep (se 2 (by rfl) ⟨214533, by rfl⟩ : syracuseStep 572089 = 429067) B429067
theorem B1719073 : Blo 354756 1719073 := bstep (se 2 (by rfl) ⟨644652, by rfl⟩ : syracuseStep 1719073 = 1289305) B1289305
theorem B1522547 : Blo 354756 1522547 := bstep (se 1 (by rfl) ⟨1141910, by rfl⟩ : syracuseStep 1522547 = 2283821) B2283821
theorem B605063 : Blo 354756 605063 := bstep (se 1 (by rfl) ⟨453797, by rfl⟩ : syracuseStep 605063 = 907595) B907595
theorem B801683 : Blo 354756 801683 := bstep (se 1 (by rfl) ⟨601262, by rfl⟩ : syracuseStep 801683 = 1202525) B1202525
theorem B1489817 : Blo 354756 1489817 := bstep (se 2 (by rfl) ⟨558681, by rfl⟩ : syracuseStep 1489817 = 1117363) B1117363
theorem B801737 : Blo 354756 801737 := bstep (se 2 (by rfl) ⟨300651, by rfl⟩ : syracuseStep 801737 = 601303) B601303
theorem B507065 : Blo 354756 507065 := bstep (se 2 (by rfl) ⟨190149, by rfl⟩ : syracuseStep 507065 = 380299) B380299
theorem B507151 : Blo 354756 507151 := bstep (se 1 (by rfl) ⟨380363, by rfl⟩ : syracuseStep 507151 = 760727) B760727
theorem B507179 : Blo 354756 507179 := bstep (se 1 (by rfl) ⟨380384, by rfl⟩ : syracuseStep 507179 = 760769) B760769
theorem B2178355 : Blo 354756 2178355 := bstep (se 1 (by rfl) ⟨1633766, by rfl⟩ : syracuseStep 2178355 = 3267533) B3267533
theorem B8207675 : Blo 354756 8207675 := bstep (se 1 (by rfl) ⟨6155756, by rfl⟩ : syracuseStep 8207675 = 12311513) B12311513
theorem B900467 : Blo 354756 900467 := bstep (se 1 (by rfl) ⟨675350, by rfl⟩ : syracuseStep 900467 = 1350701) B1350701
theorem B572807 : Blo 354756 572807 := bstep (se 1 (by rfl) ⟨429605, by rfl⟩ : syracuseStep 572807 = 859211) B859211
theorem B540047 : Blo 354756 540047 := bstep (se 1 (by rfl) ⟨405035, by rfl⟩ : syracuseStep 540047 = 810071) B810071
theorem B1359251 : Blo 354756 1359251 := bstep (se 1 (by rfl) ⟨1019438, by rfl⟩ : syracuseStep 1359251 = 2038877) B2038877
theorem B540167 : Blo 354756 540167 := bstep (se 1 (by rfl) ⟨405125, by rfl⟩ : syracuseStep 540167 = 810251) B810251
theorem B802439 : Blo 354756 802439 := bstep (se 1 (by rfl) ⟨601829, by rfl⟩ : syracuseStep 802439 = 1203659) B1203659
theorem B802619 : Blo 354756 802619 := bstep (se 1 (by rfl) ⟨601964, by rfl⟩ : syracuseStep 802619 = 1203929) B1203929
theorem B900983 : Blo 354756 900983 := bstep (se 1 (by rfl) ⟨675737, by rfl⟩ : syracuseStep 900983 = 1351475) B1351475
theorem B573319 : Blo 354756 573319 := bstep (se 1 (by rfl) ⟨429989, by rfl⟩ : syracuseStep 573319 = 859979) B859979
theorem B802745 : Blo 354756 802745 := bstep (se 2 (by rfl) ⟨301029, by rfl⟩ : syracuseStep 802745 = 602059) B602059
theorem B573575 : Blo 354756 573575 := bstep (se 1 (by rfl) ⟨430181, by rfl⟩ : syracuseStep 573575 = 860363) B860363
theorem B803087 : Blo 354756 803087 := bstep (se 1 (by rfl) ⟨602315, by rfl⟩ : syracuseStep 803087 = 1204631) B1204631
theorem B803105 : Blo 354756 803105 := bstep (se 2 (by rfl) ⟨301164, by rfl⟩ : syracuseStep 803105 = 602329) B602329
theorem B1720919 : Blo 354756 1720919 := bstep (se 1 (by rfl) ⟨1290689, by rfl⟩ : syracuseStep 1720919 = 2581379) B2581379
theorem B803447 : Blo 354756 803447 := bstep (se 1 (by rfl) ⟨602585, by rfl⟩ : syracuseStep 803447 = 1205171) B1205171
theorem B4899599 : Blo 354756 4899599 := bstep (se 1 (by rfl) ⟨3674699, by rfl⟩ : syracuseStep 4899599 = 7349399) B7349399
theorem B3261221 : Blo 354756 3261221 := bstep (se 4 (by rfl) ⟨305739, by rfl⟩ : syracuseStep 3261221 = 611479) B611479
theorem B803627 : Blo 354756 803627 := bstep (se 1 (by rfl) ⟨602720, by rfl⟩ : syracuseStep 803627 = 1205441) B1205441
theorem B901975 : Blo 354756 901975 := bstep (se 1 (by rfl) ⟨676481, by rfl⟩ : syracuseStep 901975 = 1352963) B1352963
theorem B1917917 : Blo 354756 1917917 := bstep (se 3 (by rfl) ⟨359609, by rfl⟩ : syracuseStep 1917917 = 719219) B719219
theorem B1360907 : Blo 354756 1360907 := bstep (se 1 (by rfl) ⟨1020680, by rfl⟩ : syracuseStep 1360907 = 2041361) B2041361
theorem B902279 : Blo 354756 902279 := bstep (se 1 (by rfl) ⟨676709, by rfl⟩ : syracuseStep 902279 = 1353419) B1353419
theorem B803987 : Blo 354756 803987 := bstep (se 1 (by rfl) ⟨602990, by rfl⟩ : syracuseStep 803987 = 1205981) B1205981
theorem B804041 : Blo 354756 804041 := bstep (se 2 (by rfl) ⟨301515, by rfl⟩ : syracuseStep 804041 = 603031) B603031
theorem B902411 : Blo 354756 902411 := bstep (se 1 (by rfl) ⟨676808, by rfl⟩ : syracuseStep 902411 = 1353617) B1353617
theorem B1525007 : Blo 354756 1525007 := bstep (se 1 (by rfl) ⟨1143755, by rfl⟩ : syracuseStep 1525007 = 2287511) B2287511
theorem B1197611 : Blo 354756 1197611 := bstep (se 1 (by rfl) ⟨898208, by rfl⟩ : syracuseStep 1197611 = 1796417) B1796417
theorem B902927 : Blo 354756 902927 := bstep (se 1 (by rfl) ⟨677195, by rfl⟩ : syracuseStep 902927 = 1354391) B1354391
theorem B804743 : Blo 354756 804743 := bstep (se 1 (by rfl) ⟨603557, by rfl⟩ : syracuseStep 804743 = 1207115) B1207115
theorem B903059 : Blo 354756 903059 := bstep (se 1 (by rfl) ⟨677294, by rfl⟩ : syracuseStep 903059 = 1354589) B1354589
theorem B804923 : Blo 354756 804923 := bstep (se 1 (by rfl) ⟨603692, by rfl⟩ : syracuseStep 804923 = 1207385) B1207385
theorem B510095 : Blo 354756 510095 := bstep (se 1 (by rfl) ⟨382571, by rfl⟩ : syracuseStep 510095 = 765143) B765143
theorem B805049 : Blo 354756 805049 := bstep (se 2 (by rfl) ⟨301893, by rfl⟩ : syracuseStep 805049 = 603787) B603787
theorem B608647 : Blo 354756 608647 := bstep (se 1 (by rfl) ⟨456485, by rfl⟩ : syracuseStep 608647 = 912971) B912971
theorem B805391 : Blo 354756 805391 := bstep (se 1 (by rfl) ⟨604043, by rfl⟩ : syracuseStep 805391 = 1208087) B1208087
theorem B805409 : Blo 354756 805409 := bstep (se 2 (by rfl) ⟨302028, by rfl⟩ : syracuseStep 805409 = 604057) B604057
theorem B1919555 : Blo 354756 1919555 := bstep (se 1 (by rfl) ⟨1439666, by rfl⟩ : syracuseStep 1919555 = 2879333) B2879333
theorem B1198907 : Blo 354756 1198907 := bstep (se 1 (by rfl) ⟨899180, by rfl⟩ : syracuseStep 1198907 = 1798361) B1798361
theorem B805751 : Blo 354756 805751 := bstep (se 1 (by rfl) ⟨604313, by rfl⟩ : syracuseStep 805751 = 1208627) B1208627
theorem B1526663 : Blo 354756 1526663 := bstep (se 1 (by rfl) ⟨1144997, by rfl⟩ : syracuseStep 1526663 = 2289995) B2289995
theorem B904193 : Blo 354756 904193 := bstep (se 2 (by rfl) ⟨339072, by rfl⟩ : syracuseStep 904193 = 678145) B678145
theorem B805931 : Blo 354756 805931 := bstep (se 1 (by rfl) ⟨604448, by rfl⟩ : syracuseStep 805931 = 1208897) B1208897
theorem B674963 : Blo 354756 674963 := bstep (se 1 (by rfl) ⟨506222, by rfl⟩ : syracuseStep 674963 = 1012445) B1012445
theorem B1199393 : Blo 354756 1199393 := bstep (se 2 (by rfl) ⟨449772, by rfl⟩ : syracuseStep 1199393 = 899545) B899545
theorem B675191 : Blo 354756 675191 := bstep (se 1 (by rfl) ⟨506393, by rfl⟩ : syracuseStep 675191 = 1012787) B1012787
theorem B904567 : Blo 354756 904567 := bstep (se 1 (by rfl) ⟨678425, by rfl⟩ : syracuseStep 904567 = 1356851) B1356851
theorem B4050323 : Blo 354756 4050323 := bstep (se 1 (by rfl) ⟨3037742, by rfl⟩ : syracuseStep 4050323 = 6075485) B6075485
theorem B806291 : Blo 354756 806291 := bstep (se 1 (by rfl) ⟨604718, by rfl⟩ : syracuseStep 806291 = 1209437) B1209437
theorem B1723801 : Blo 354756 1723801 := bstep (se 2 (by rfl) ⟨646425, by rfl⟩ : syracuseStep 1723801 = 1292851) B1292851
theorem B642505 : Blo 354756 642505 := bstep (se 2 (by rfl) ⟨240939, by rfl⟩ : syracuseStep 642505 = 481879) B481879
theorem B806345 : Blo 354756 806345 := bstep (se 2 (by rfl) ⟨302379, by rfl⟩ : syracuseStep 806345 = 604759) B604759
theorem B1822409 : Blo 354756 1822409 := bstep (se 2 (by rfl) ⟨683403, by rfl⟩ : syracuseStep 1822409 = 1366807) B1366807
theorem B905003 : Blo 354756 905003 := bstep (se 1 (by rfl) ⟨678752, by rfl⟩ : syracuseStep 905003 = 1357505) B1357505
theorem B1199987 : Blo 354756 1199987 := bstep (se 1 (by rfl) ⟨899990, by rfl⟩ : syracuseStep 1199987 = 1799981) B1799981
theorem B807047 : Blo 354756 807047 := bstep (se 1 (by rfl) ⟨605285, by rfl⟩ : syracuseStep 807047 = 1210571) B1210571
theorem B381115 : Blo 354756 381115 := bstep (se 1 (by rfl) ⟨285836, by rfl⟩ : syracuseStep 381115 = 571673) B571673
theorem B8278337 : Blo 354756 8278337 := bstep (se 2 (by rfl) ⟨3104376, by rfl⟩ : syracuseStep 8278337 = 6208753) B6208753
theorem B905843 : Blo 354756 905843 := bstep (se 1 (by rfl) ⟨679382, by rfl⟩ : syracuseStep 905843 = 1358765) B1358765
theorem B905863 : Blo 354756 905863 := bstep (se 1 (by rfl) ⟨679397, by rfl⟩ : syracuseStep 905863 = 1358795) B1358795
theorem B1528577 : Blo 354756 1528577 := bstep (se 2 (by rfl) ⟨573216, by rfl⟩ : syracuseStep 1528577 = 1146433) B1146433
theorem B2577167 : Blo 354756 2577167 := bstep (se 1 (by rfl) ⟨1932875, by rfl⟩ : syracuseStep 2577167 = 3865751) B3865751
theorem B906137 : Blo 354756 906137 := bstep (se 2 (by rfl) ⟨339801, by rfl⟩ : syracuseStep 906137 = 679603) B679603
theorem B676907 : Blo 354756 676907 := bstep (se 1 (by rfl) ⟨507680, by rfl⟩ : syracuseStep 676907 = 1015361) B1015361
theorem B906299 : Blo 354756 906299 := bstep (se 1 (by rfl) ⟨679724, by rfl⟩ : syracuseStep 906299 = 1359449) B1359449
theorem B1528919 : Blo 354756 1528919 := bstep (se 1 (by rfl) ⟨1146689, by rfl⟩ : syracuseStep 1528919 = 2293379) B2293379
theorem B1102967 : Blo 354756 1102967 := bstep (se 1 (by rfl) ⟨827225, by rfl⟩ : syracuseStep 1102967 = 1654451) B1654451
theorem B1922305 : Blo 354756 1922305 := bstep (se 2 (by rfl) ⟨720864, by rfl⟩ : syracuseStep 1922305 = 1441729) B1441729
theorem B677135 : Blo 354756 677135 := bstep (se 1 (by rfl) ⟨507851, by rfl⟩ : syracuseStep 677135 = 1015703) B1015703
theorem B906511 : Blo 354756 906511 := bstep (se 1 (by rfl) ⟨679883, by rfl⟩ : syracuseStep 906511 = 1359767) B1359767
theorem B2020697 : Blo 354756 2020697 := bstep (se 2 (by rfl) ⟨757761, by rfl⟩ : syracuseStep 2020697 = 1515523) B1515523
theorem B906785 : Blo 354756 906785 := bstep (se 2 (by rfl) ⟨340044, by rfl⟩ : syracuseStep 906785 = 680089) B680089
theorem B4085315 : Blo 354756 4085315 := bstep (se 1 (by rfl) ⟨3063986, by rfl⟩ : syracuseStep 4085315 = 6127973) B6127973
theorem B1628531 : Blo 354756 1628531 := bstep (se 1 (by rfl) ⟨1221398, by rfl⟩ : syracuseStep 1628531 = 2442797) B2442797
theorem B1202579 : Blo 354756 1202579 := bstep (se 1 (by rfl) ⟨901934, by rfl⟩ : syracuseStep 1202579 = 1803869) B1803869
theorem B612793 : Blo 354756 612793 := bstep (se 2 (by rfl) ⟨229797, by rfl⟩ : syracuseStep 612793 = 459595) B459595
theorem B907787 : Blo 354756 907787 := bstep (se 1 (by rfl) ⟨680840, by rfl⟩ : syracuseStep 907787 = 1361681) B1361681
theorem B9230915 : Blo 354756 9230915 := bstep (se 1 (by rfl) ⟨6923186, by rfl⟩ : syracuseStep 9230915 = 13846373) B13846373
theorem B678547 : Blo 354756 678547 := bstep (se 1 (by rfl) ⟨508910, by rfl⟩ : syracuseStep 678547 = 1017821) B1017821
theorem B678775 : Blo 354756 678775 := bstep (se 1 (by rfl) ⟨509081, by rfl⟩ : syracuseStep 678775 = 1018163) B1018163
theorem B2579363 : Blo 354756 2579363 := bstep (se 1 (by rfl) ⟨1934522, by rfl⟩ : syracuseStep 2579363 = 3869045) B3869045
theorem B449707 : Blo 354756 449707 := bstep (se 1 (by rfl) ⟨337280, by rfl⟩ : syracuseStep 449707 = 674561) B674561
theorem B1531345 : Blo 354756 1531345 := bstep (se 2 (by rfl) ⟨574254, by rfl⟩ : syracuseStep 1531345 = 1148509) B1148509
theorem B4120183 : Blo 354756 4120183 := bstep (se 1 (by rfl) ⟨3090137, by rfl⟩ : syracuseStep 4120183 = 6180275) B6180275
theorem B17325809 : Blo 354756 17325809 := bstep (se 2 (by rfl) ⟨6497178, by rfl⟩ : syracuseStep 17325809 = 12994357) B12994357
theorem B1203983 : Blo 354756 1203983 := bstep (se 1 (by rfl) ⟨902987, by rfl⟩ : syracuseStep 1203983 = 1805975) B1805975
theorem B1204253 : Blo 354756 1204253 := bstep (se 3 (by rfl) ⟨225797, by rfl⟩ : syracuseStep 1204253 = 451595) B451595
theorem B2187383 : Blo 354756 2187383 := bstep (se 1 (by rfl) ⟨1640537, by rfl⟩ : syracuseStep 2187383 = 3281075) B3281075
theorem B450679 : Blo 354756 450679 := bstep (se 1 (by rfl) ⟨338009, by rfl⟩ : syracuseStep 450679 = 676019) B676019
theorem B450859 : Blo 354756 450859 := bstep (se 1 (by rfl) ⟨338144, by rfl⟩ : syracuseStep 450859 = 676289) B676289
theorem B680339 : Blo 354756 680339 := bstep (se 1 (by rfl) ⟨510254, by rfl⟩ : syracuseStep 680339 = 1020509) B1020509
theorem B2023865 : Blo 354756 2023865 := bstep (se 2 (by rfl) ⟨758949, by rfl⟩ : syracuseStep 2023865 = 1517899) B1517899
theorem B451003 : Blo 354756 451003 := bstep (se 1 (by rfl) ⟨338252, by rfl⟩ : syracuseStep 451003 = 676505) B676505
theorem B680393 : Blo 354756 680393 := bstep (se 2 (by rfl) ⟨255147, by rfl⟩ : syracuseStep 680393 = 510295) B510295
theorem B2318813 : Blo 354756 2318813 := bstep (se 3 (by rfl) ⟨434777, by rfl⟩ : syracuseStep 2318813 = 869555) B869555
theorem B680491 : Blo 354756 680491 := bstep (se 1 (by rfl) ⟨510368, by rfl⟩ : syracuseStep 680491 = 1020737) B1020737
theorem B680719 : Blo 354756 680719 := bstep (se 1 (by rfl) ⟨510539, by rfl⟩ : syracuseStep 680719 = 1021079) B1021079
theorem B1303595 : Blo 354756 1303595 := bstep (se 1 (by rfl) ⟨977696, by rfl⟩ : syracuseStep 1303595 = 1955393) B1955393
theorem B2221229 : Blo 354756 2221229 := bstep (se 3 (by rfl) ⟨416480, by rfl⟩ : syracuseStep 2221229 = 832961) B832961
theorem B550201 : Blo 354756 550201 := bstep (se 2 (by rfl) ⟨206325, by rfl⟩ : syracuseStep 550201 = 412651) B412651
theorem B910711 : Blo 354756 910711 := bstep (se 1 (by rfl) ⟨683033, by rfl⟩ : syracuseStep 910711 = 1366067) B1366067
theorem B451975 : Blo 354756 451975 := bstep (se 1 (by rfl) ⟨338981, by rfl⟩ : syracuseStep 451975 = 677963) B677963
theorem B1205657 : Blo 354756 1205657 := bstep (se 2 (by rfl) ⟨452121, by rfl⟩ : syracuseStep 1205657 = 904243) B904243
theorem B812587 : Blo 354756 812587 := bstep (se 1 (by rfl) ⟨609440, by rfl⟩ : syracuseStep 812587 = 1218881) B1218881
theorem B812843 : Blo 354756 812843 := bstep (se 1 (by rfl) ⟨609632, by rfl⟩ : syracuseStep 812843 = 1219265) B1219265
theorem B452395 : Blo 354756 452395 := bstep (se 1 (by rfl) ⟨339296, by rfl⟩ : syracuseStep 452395 = 678593) B678593
theorem B452623 : Blo 354756 452623 := bstep (se 1 (by rfl) ⟨339467, by rfl⟩ : syracuseStep 452623 = 678935) B678935
theorem B1206359 : Blo 354756 1206359 := bstep (se 1 (by rfl) ⟨904769, by rfl⟩ : syracuseStep 1206359 = 1809539) B1809539
theorem B2582765 : Blo 354756 2582765 := bstep (se 3 (by rfl) ⟨484268, by rfl⟩ : syracuseStep 2582765 = 968537) B968537
theorem B3434957 : Blo 354756 3434957 := bstep (se 3 (by rfl) ⟨644054, by rfl⟩ : syracuseStep 3434957 = 1288109) B1288109
theorem B354823 : Blo 354756 354823 := bstep (se 1 (by rfl) ⟨266117, by rfl⟩ : syracuseStep 354823 = 532235) B532235
theorem B354831 : Blo 354756 354831 := bstep (se 1 (by rfl) ⟨266123, by rfl⟩ : syracuseStep 354831 = 532247) B532247
theorem B354875 : Blo 354756 354875 := bstep (se 1 (by rfl) ⟨266156, by rfl⟩ : syracuseStep 354875 = 532313) B532313
theorem B1206845 : Blo 354756 1206845 := bstep (se 3 (by rfl) ⟨226283, by rfl⟩ : syracuseStep 1206845 = 452567) B452567
theorem B354951 : Blo 354756 354951 := bstep (se 1 (by rfl) ⟨266213, by rfl⟩ : syracuseStep 354951 = 532427) B532427
theorem B354959 : Blo 354756 354959 := bstep (se 1 (by rfl) ⟨266219, by rfl⟩ : syracuseStep 354959 = 532439) B532439
theorem B355003 : Blo 354756 355003 := bstep (se 1 (by rfl) ⟨266252, by rfl⟩ : syracuseStep 355003 = 532505) B532505
theorem B453367 : Blo 354756 453367 := bstep (se 1 (by rfl) ⟨340025, by rfl⟩ : syracuseStep 453367 = 680051) B680051
theorem B355079 : Blo 354756 355079 := bstep (se 1 (by rfl) ⟨266309, by rfl⟩ : syracuseStep 355079 = 532619) B532619
theorem B355087 : Blo 354756 355087 := bstep (se 1 (by rfl) ⟨266315, by rfl⟩ : syracuseStep 355087 = 532631) B532631
theorem B2026255 : Blo 354756 2026255 := bstep (se 1 (by rfl) ⟨1519691, by rfl⟩ : syracuseStep 2026255 = 3039383) B3039383
theorem B355131 : Blo 354756 355131 := bstep (se 1 (by rfl) ⟨266348, by rfl⟩ : syracuseStep 355131 = 532697) B532697
theorem B5499737 : Blo 354756 5499737 := bstep (se 2 (by rfl) ⟨2062401, by rfl⟩ : syracuseStep 5499737 = 4124803) B4124803
theorem B355207 : Blo 354756 355207 := bstep (se 1 (by rfl) ⟨266405, by rfl⟩ : syracuseStep 355207 = 532811) B532811
theorem B355215 : Blo 354756 355215 := bstep (se 1 (by rfl) ⟨266411, by rfl⟩ : syracuseStep 355215 = 532823) B532823
theorem B355259 : Blo 354756 355259 := bstep (se 1 (by rfl) ⟨266444, by rfl⟩ : syracuseStep 355259 = 532889) B532889
theorem B355335 : Blo 354756 355335 := bstep (se 1 (by rfl) ⟨266501, by rfl⟩ : syracuseStep 355335 = 533003) B533003
theorem B355343 : Blo 354756 355343 := bstep (se 1 (by rfl) ⟨266507, by rfl⟩ : syracuseStep 355343 = 533015) B533015
theorem B355387 : Blo 354756 355387 := bstep (se 1 (by rfl) ⟨266540, by rfl⟩ : syracuseStep 355387 = 533081) B533081
theorem B453691 : Blo 354756 453691 := bstep (se 1 (by rfl) ⟨340268, by rfl⟩ : syracuseStep 453691 = 680537) B680537
theorem B1141847 : Blo 354756 1141847 := bstep (se 1 (by rfl) ⟨856385, by rfl⟩ : syracuseStep 1141847 = 1712771) B1712771
theorem B355463 : Blo 354756 355463 := bstep (se 1 (by rfl) ⟨266597, by rfl⟩ : syracuseStep 355463 = 533195) B533195
theorem B355471 : Blo 354756 355471 := bstep (se 1 (by rfl) ⟨266603, by rfl⟩ : syracuseStep 355471 = 533207) B533207
theorem B1010873 : Blo 354756 1010873 := bstep (se 2 (by rfl) ⟨379077, by rfl⟩ : syracuseStep 1010873 = 758155) B758155
theorem B355515 : Blo 354756 355515 := bstep (se 1 (by rfl) ⟨266636, by rfl⟩ : syracuseStep 355515 = 533273) B533273
theorem B355591 : Blo 354756 355591 := bstep (se 1 (by rfl) ⟨266693, by rfl⟩ : syracuseStep 355591 = 533387) B533387
theorem B355599 : Blo 354756 355599 := bstep (se 1 (by rfl) ⟨266699, by rfl⟩ : syracuseStep 355599 = 533399) B533399
theorem B1010987 : Blo 354756 1010987 := bstep (se 1 (by rfl) ⟨758240, by rfl⟩ : syracuseStep 1010987 = 1516481) B1516481
theorem B355643 : Blo 354756 355643 := bstep (se 1 (by rfl) ⟨266732, by rfl⟩ : syracuseStep 355643 = 533465) B533465
theorem B355719 : Blo 354756 355719 := bstep (se 1 (by rfl) ⟨266789, by rfl⟩ : syracuseStep 355719 = 533579) B533579
theorem B355727 : Blo 354756 355727 := bstep (se 1 (by rfl) ⟨266795, by rfl⟩ : syracuseStep 355727 = 533591) B533591
theorem B1830289 : Blo 354756 1830289 := bstep (se 2 (by rfl) ⟨686358, by rfl⟩ : syracuseStep 1830289 = 1372717) B1372717
theorem B355771 : Blo 354756 355771 := bstep (se 1 (by rfl) ⟨266828, by rfl⟩ : syracuseStep 355771 = 533657) B533657
theorem B355847 : Blo 354756 355847 := bstep (se 1 (by rfl) ⟨266885, by rfl⟩ : syracuseStep 355847 = 533771) B533771
theorem B978443 : Blo 354756 978443 := bstep (se 1 (by rfl) ⟨733832, by rfl⟩ : syracuseStep 978443 = 1467665) B1467665
theorem B355855 : Blo 354756 355855 := bstep (se 1 (by rfl) ⟨266891, by rfl⟩ : syracuseStep 355855 = 533783) B533783
theorem B355899 : Blo 354756 355899 := bstep (se 1 (by rfl) ⟨266924, by rfl⟩ : syracuseStep 355899 = 533849) B533849
theorem B1142333 : Blo 354756 1142333 := bstep (se 3 (by rfl) ⟨214187, by rfl⟩ : syracuseStep 1142333 = 428375) B428375
theorem B58453589 : Blo 354756 58453589 := bstep (se 8 (by rfl) ⟨342501, by rfl⟩ : syracuseStep 58453589 = 685003) B685003
theorem B355975 : Blo 354756 355975 := bstep (se 1 (by rfl) ⟨266981, by rfl⟩ : syracuseStep 355975 = 533963) B533963
theorem B355983 : Blo 354756 355983 := bstep (se 1 (by rfl) ⟨266987, by rfl⟩ : syracuseStep 355983 = 533975) B533975
theorem B356027 : Blo 354756 356027 := bstep (se 1 (by rfl) ⟨267020, by rfl⟩ : syracuseStep 356027 = 534041) B534041
theorem B1928897 : Blo 354756 1928897 := bstep (se 2 (by rfl) ⟨723336, by rfl⟩ : syracuseStep 1928897 = 1446673) B1446673
theorem B356103 : Blo 354756 356103 := bstep (se 1 (by rfl) ⟨267077, by rfl⟩ : syracuseStep 356103 = 534155) B534155
theorem B356111 : Blo 354756 356111 := bstep (se 1 (by rfl) ⟨267083, by rfl⟩ : syracuseStep 356111 = 534167) B534167
theorem B618283 : Blo 354756 618283 := bstep (se 1 (by rfl) ⟨463712, by rfl⟩ : syracuseStep 618283 = 927425) B927425
theorem B356155 : Blo 354756 356155 := bstep (se 1 (by rfl) ⟨267116, by rfl⟩ : syracuseStep 356155 = 534233) B534233
theorem B356231 : Blo 354756 356231 := bstep (se 1 (by rfl) ⟨267173, by rfl⟩ : syracuseStep 356231 = 534347) B534347
theorem B356239 : Blo 354756 356239 := bstep (se 1 (by rfl) ⟨267179, by rfl⟩ : syracuseStep 356239 = 534359) B534359
theorem B1208249 : Blo 354756 1208249 := bstep (se 2 (by rfl) ⟨453093, by rfl⟩ : syracuseStep 1208249 = 906187) B906187
theorem B356283 : Blo 354756 356283 := bstep (se 1 (by rfl) ⟨267212, by rfl⟩ : syracuseStep 356283 = 534425) B534425
theorem B1044481 : Blo 354756 1044481 := bstep (se 2 (by rfl) ⟨391680, by rfl⟩ : syracuseStep 1044481 = 783361) B783361
theorem B356359 : Blo 354756 356359 := bstep (se 1 (by rfl) ⟨267269, by rfl⟩ : syracuseStep 356359 = 534539) B534539
theorem B2027531 : Blo 354756 2027531 := bstep (se 1 (by rfl) ⟨1520648, by rfl⟩ : syracuseStep 2027531 = 3041297) B3041297
theorem B356367 : Blo 354756 356367 := bstep (se 1 (by rfl) ⟨267275, by rfl⟩ : syracuseStep 356367 = 534551) B534551
theorem B356411 : Blo 354756 356411 := bstep (se 1 (by rfl) ⟨267308, by rfl⟩ : syracuseStep 356411 = 534617) B534617
theorem B356487 : Blo 354756 356487 := bstep (se 1 (by rfl) ⟨267365, by rfl⟩ : syracuseStep 356487 = 534731) B534731
theorem B356495 : Blo 354756 356495 := bstep (se 1 (by rfl) ⟨267371, by rfl⟩ : syracuseStep 356495 = 534743) B534743
theorem B356539 : Blo 354756 356539 := bstep (se 1 (by rfl) ⟨267404, by rfl⟩ : syracuseStep 356539 = 534809) B534809
theorem B2027713 : Blo 354756 2027713 := bstep (se 2 (by rfl) ⟨760392, by rfl⟩ : syracuseStep 2027713 = 1520785) B1520785
theorem B2355437 : Blo 354756 2355437 := bstep (se 3 (by rfl) ⟨441644, by rfl⟩ : syracuseStep 2355437 = 883289) B883289
theorem B356615 : Blo 354756 356615 := bstep (se 1 (by rfl) ⟨267461, by rfl⟩ : syracuseStep 356615 = 534923) B534923
theorem B356623 : Blo 354756 356623 := bstep (se 1 (by rfl) ⟨267467, by rfl⟩ : syracuseStep 356623 = 534935) B534935
theorem B356667 : Blo 354756 356667 := bstep (se 1 (by rfl) ⟨267500, by rfl⟩ : syracuseStep 356667 = 535001) B535001
theorem B356743 : Blo 354756 356743 := bstep (se 1 (by rfl) ⟨267557, by rfl⟩ : syracuseStep 356743 = 535115) B535115
theorem B356751 : Blo 354756 356751 := bstep (se 1 (by rfl) ⟨267563, by rfl⟩ : syracuseStep 356751 = 535127) B535127
theorem B1012115 : Blo 354756 1012115 := bstep (se 1 (by rfl) ⟨759086, by rfl⟩ : syracuseStep 1012115 = 1518173) B1518173
theorem B356795 : Blo 354756 356795 := bstep (se 1 (by rfl) ⟨267596, by rfl⟩ : syracuseStep 356795 = 535193) B535193
theorem B356871 : Blo 354756 356871 := bstep (se 1 (by rfl) ⟨267653, by rfl⟩ : syracuseStep 356871 = 535307) B535307
theorem B1208843 : Blo 354756 1208843 := bstep (se 1 (by rfl) ⟨906632, by rfl⟩ : syracuseStep 1208843 = 1813265) B1813265
theorem B356879 : Blo 354756 356879 := bstep (se 1 (by rfl) ⟨267659, by rfl⟩ : syracuseStep 356879 = 535319) B535319
theorem B1798685 : Blo 354756 1798685 := bstep (se 3 (by rfl) ⟨337253, by rfl⟩ : syracuseStep 1798685 = 674507) B674507
theorem B356923 : Blo 354756 356923 := bstep (se 1 (by rfl) ⟨267692, by rfl⟩ : syracuseStep 356923 = 535385) B535385
theorem B1208951 : Blo 354756 1208951 := bstep (se 1 (by rfl) ⟨906713, by rfl⟩ : syracuseStep 1208951 = 1813427) B1813427
theorem B356999 : Blo 354756 356999 := bstep (se 1 (by rfl) ⟨267749, by rfl⟩ : syracuseStep 356999 = 535499) B535499
theorem B455311 : Blo 354756 455311 := bstep (se 1 (by rfl) ⟨341483, by rfl⟩ : syracuseStep 455311 = 682967) B682967
theorem B357007 : Blo 354756 357007 := bstep (se 1 (by rfl) ⟨267755, by rfl⟩ : syracuseStep 357007 = 535511) B535511
theorem B357051 : Blo 354756 357051 := bstep (se 1 (by rfl) ⟨267788, by rfl⟩ : syracuseStep 357051 = 535577) B535577
theorem B17330881 : Blo 354756 17330881 := bstep (se 2 (by rfl) ⟨6499080, by rfl⟩ : syracuseStep 17330881 = 12998161) B12998161
theorem B357127 : Blo 354756 357127 := bstep (se 1 (by rfl) ⟨267845, by rfl⟩ : syracuseStep 357127 = 535691) B535691
theorem B357135 : Blo 354756 357135 := bstep (se 1 (by rfl) ⟨267851, by rfl⟩ : syracuseStep 357135 = 535703) B535703
theorem B1012513 : Blo 354756 1012513 := bstep (se 2 (by rfl) ⟨379692, by rfl⟩ : syracuseStep 1012513 = 759385) B759385
theorem B357179 : Blo 354756 357179 := bstep (se 1 (by rfl) ⟨267884, by rfl⟩ : syracuseStep 357179 = 535769) B535769
theorem B357255 : Blo 354756 357255 := bstep (se 1 (by rfl) ⟨267941, by rfl⟩ : syracuseStep 357255 = 535883) B535883
theorem B357263 : Blo 354756 357263 := bstep (se 1 (by rfl) ⟨267947, by rfl⟩ : syracuseStep 357263 = 535895) B535895
theorem B357307 : Blo 354756 357307 := bstep (se 1 (by rfl) ⟨267980, by rfl⟩ : syracuseStep 357307 = 535961) B535961
theorem B1799171 : Blo 354756 1799171 := bstep (se 1 (by rfl) ⟨1349378, by rfl⟩ : syracuseStep 1799171 = 2698757) B2698757
theorem B357383 : Blo 354756 357383 := bstep (se 1 (by rfl) ⟨268037, by rfl⟩ : syracuseStep 357383 = 536075) B536075
theorem B357391 : Blo 354756 357391 := bstep (se 1 (by rfl) ⟨268043, by rfl⟩ : syracuseStep 357391 = 536087) B536087
theorem B357435 : Blo 354756 357435 := bstep (se 1 (by rfl) ⟨268076, by rfl⟩ : syracuseStep 357435 = 536153) B536153
theorem B357511 : Blo 354756 357511 := bstep (se 1 (by rfl) ⟨268133, by rfl⟩ : syracuseStep 357511 = 536267) B536267
theorem B357519 : Blo 354756 357519 := bstep (se 1 (by rfl) ⟨268139, by rfl⟩ : syracuseStep 357519 = 536279) B536279
theorem B357563 : Blo 354756 357563 := bstep (se 1 (by rfl) ⟨268172, by rfl⟩ : syracuseStep 357563 = 536345) B536345
theorem B1209545 : Blo 354756 1209545 := bstep (se 2 (by rfl) ⟨453579, by rfl⟩ : syracuseStep 1209545 = 907159) B907159
theorem B357639 : Blo 354756 357639 := bstep (se 1 (by rfl) ⟨268229, by rfl⟩ : syracuseStep 357639 = 536459) B536459
theorem B357647 : Blo 354756 357647 := bstep (se 1 (by rfl) ⟨268235, by rfl⟩ : syracuseStep 357647 = 536471) B536471
theorem B357691 : Blo 354756 357691 := bstep (se 1 (by rfl) ⟨268268, by rfl⟩ : syracuseStep 357691 = 536537) B536537
theorem B357767 : Blo 354756 357767 := bstep (se 1 (by rfl) ⟨268325, by rfl⟩ : syracuseStep 357767 = 536651) B536651
theorem B357775 : Blo 354756 357775 := bstep (se 1 (by rfl) ⟨268331, by rfl⟩ : syracuseStep 357775 = 536663) B536663
theorem B357819 : Blo 354756 357819 := bstep (se 1 (by rfl) ⟨268364, by rfl⟩ : syracuseStep 357819 = 536729) B536729
theorem B357895 : Blo 354756 357895 := bstep (se 1 (by rfl) ⟨268421, by rfl⟩ : syracuseStep 357895 = 536843) B536843
theorem B357903 : Blo 354756 357903 := bstep (se 1 (by rfl) ⟨268427, by rfl⟩ : syracuseStep 357903 = 536855) B536855
theorem B357947 : Blo 354756 357947 := bstep (se 1 (by rfl) ⟨268460, by rfl⟩ : syracuseStep 357947 = 536921) B536921
theorem B358023 : Blo 354756 358023 := bstep (se 1 (by rfl) ⟨268517, by rfl⟩ : syracuseStep 358023 = 537035) B537035
theorem B358031 : Blo 354756 358031 := bstep (se 1 (by rfl) ⟨268523, by rfl⟩ : syracuseStep 358031 = 537047) B537047
theorem B1013401 : Blo 354756 1013401 := bstep (se 2 (by rfl) ⟨380025, by rfl⟩ : syracuseStep 1013401 = 760051) B760051
theorem B358075 : Blo 354756 358075 := bstep (se 1 (by rfl) ⟨268556, by rfl⟩ : syracuseStep 358075 = 537113) B537113
theorem B2291429 : Blo 354756 2291429 := bstep (se 4 (by rfl) ⟨214821, by rfl⟩ : syracuseStep 2291429 = 429643) B429643
theorem B358151 : Blo 354756 358151 := bstep (se 1 (by rfl) ⟨268613, by rfl⟩ : syracuseStep 358151 = 537227) B537227
theorem B358159 : Blo 354756 358159 := bstep (se 1 (by rfl) ⟨268619, by rfl⟩ : syracuseStep 358159 = 537239) B537239
theorem B718625 : Blo 354756 718625 := bstep (se 2 (by rfl) ⟨269484, by rfl⟩ : syracuseStep 718625 = 538969) B538969
theorem B358203 : Blo 354756 358203 := bstep (se 1 (by rfl) ⟨268652, by rfl⟩ : syracuseStep 358203 = 537305) B537305
theorem B3667801 : Blo 354756 3667801 := bstep (se 2 (by rfl) ⟨1375425, by rfl⟩ : syracuseStep 3667801 = 2750851) B2750851
theorem B1439603 : Blo 354756 1439603 := bstep (se 1 (by rfl) ⟨1079702, by rfl⟩ : syracuseStep 1439603 = 2159405) B2159405
theorem B358279 : Blo 354756 358279 := bstep (se 1 (by rfl) ⟨268709, by rfl⟩ : syracuseStep 358279 = 537419) B537419
theorem B1210247 : Blo 354756 1210247 := bstep (se 1 (by rfl) ⟨907685, by rfl⟩ : syracuseStep 1210247 = 1815371) B1815371
theorem B358287 : Blo 354756 358287 := bstep (se 1 (by rfl) ⟨268715, by rfl⟩ : syracuseStep 358287 = 537431) B537431
theorem B358331 : Blo 354756 358331 := bstep (se 1 (by rfl) ⟨268748, by rfl⟩ : syracuseStep 358331 = 537497) B537497
theorem B358407 : Blo 354756 358407 := bstep (se 1 (by rfl) ⟨268805, by rfl⟩ : syracuseStep 358407 = 537611) B537611
theorem B358415 : Blo 354756 358415 := bstep (se 1 (by rfl) ⟨268811, by rfl⟩ : syracuseStep 358415 = 537623) B537623
theorem B1013789 : Blo 354756 1013789 := bstep (se 3 (by rfl) ⟨190085, by rfl⟩ : syracuseStep 1013789 = 380171) B380171
theorem B358459 : Blo 354756 358459 := bstep (se 1 (by rfl) ⟨268844, by rfl⟩ : syracuseStep 358459 = 537689) B537689
theorem B2881669 : Blo 354756 2881669 := bstep (se 4 (by rfl) ⟨270156, by rfl⟩ : syracuseStep 2881669 = 540313) B540313
theorem B358535 : Blo 354756 358535 := bstep (se 1 (by rfl) ⟨268901, by rfl⟩ : syracuseStep 358535 = 537803) B537803
theorem B358543 : Blo 354756 358543 := bstep (se 1 (by rfl) ⟨268907, by rfl⟩ : syracuseStep 358543 = 537815) B537815
theorem B358587 : Blo 354756 358587 := bstep (se 1 (by rfl) ⟨268940, by rfl⟩ : syracuseStep 358587 = 537881) B537881
theorem B1210625 : Blo 354756 1210625 := bstep (se 2 (by rfl) ⟨453984, by rfl⟩ : syracuseStep 1210625 = 907969) B907969
theorem B358663 : Blo 354756 358663 := bstep (se 1 (by rfl) ⟨268997, by rfl⟩ : syracuseStep 358663 = 537995) B537995
theorem B358671 : Blo 354756 358671 := bstep (se 1 (by rfl) ⟨269003, by rfl⟩ : syracuseStep 358671 = 538007) B538007
theorem B358715 : Blo 354756 358715 := bstep (se 1 (by rfl) ⟨269036, by rfl⟩ : syracuseStep 358715 = 538073) B538073
theorem B1440185 : Blo 354756 1440185 := bstep (se 2 (by rfl) ⟨540069, by rfl⟩ : syracuseStep 1440185 = 1080139) B1080139
theorem B1079837 : Blo 354756 1079837 := bstep (se 3 (by rfl) ⟨202469, by rfl⟩ : syracuseStep 1079837 = 404939) B404939
theorem B1800791 : Blo 354756 1800791 := bstep (se 1 (by rfl) ⟨1350593, by rfl⟩ : syracuseStep 1800791 = 2701187) B2701187
theorem B916235 : Blo 354756 916235 := bstep (se 1 (by rfl) ⟨687176, by rfl⟩ : syracuseStep 916235 = 1374353) B1374353
theorem B4061987 : Blo 354756 4061987 := bstep (se 1 (by rfl) ⟨3046490, by rfl⟩ : syracuseStep 4061987 = 6092981) B6092981
theorem B7863155 : Blo 354756 7863155 := bstep (se 1 (by rfl) ⟨5897366, by rfl⟩ : syracuseStep 7863155 = 11794733) B11794733
theorem B1801277 : Blo 354756 1801277 := bstep (se 3 (by rfl) ⟨337739, by rfl⟩ : syracuseStep 1801277 = 675479) B675479
theorem B1473977 : Blo 354756 1473977 := bstep (se 2 (by rfl) ⟨552741, by rfl⟩ : syracuseStep 1473977 = 1105483) B1105483
theorem B360335 : Blo 354756 360335 := bstep (se 1 (by rfl) ⟨270251, by rfl⟩ : syracuseStep 360335 = 540503) B540503
theorem B5833021 : Blo 354756 5833021 := bstep (se 3 (by rfl) ⟨1093691, by rfl⟩ : syracuseStep 5833021 = 2187383) B2187383
theorem B721295 : Blo 354756 721295 := bstep (se 1 (by rfl) ⟨540971, by rfl⟩ : syracuseStep 721295 = 1081943) B1081943
theorem B1147279 : Blo 354756 1147279 := bstep (se 1 (by rfl) ⟨860459, by rfl⟩ : syracuseStep 1147279 = 1720919) B1720919
theorem B1278611 : Blo 354756 1278611 := bstep (se 1 (by rfl) ⟨958958, by rfl⟩ : syracuseStep 1278611 = 1917917) B1917917
theorem B721619 : Blo 354756 721619 := bstep (se 1 (by rfl) ⟨541214, by rfl⟩ : syracuseStep 721619 = 1082429) B1082429
theorem B5768009 : Blo 354756 5768009 := bstep (se 2 (by rfl) ⟨2163003, by rfl⟩ : syracuseStep 5768009 = 4326007) B4326007
theorem B1016671 : Blo 354756 1016671 := bstep (se 1 (by rfl) ⟨762503, by rfl⟩ : syracuseStep 1016671 = 1525007) B1525007
theorem B2032613 : Blo 354756 2032613 := bstep (se 4 (by rfl) ⟨190557, by rfl⟩ : syracuseStep 2032613 = 381115) B381115
theorem B1442897 : Blo 354756 1442897 := bstep (se 2 (by rfl) ⟨541086, by rfl⟩ : syracuseStep 1442897 = 1082173) B1082173
theorem B2721113 : Blo 354756 2721113 := bstep (se 2 (by rfl) ⟨1020417, by rfl⟩ : syracuseStep 2721113 = 2040835) B2040835
theorem B1279703 : Blo 354756 1279703 := bstep (se 1 (by rfl) ⟨959777, by rfl⟩ : syracuseStep 1279703 = 1919555) B1919555
theorem B1017593 : Blo 354756 1017593 := bstep (se 2 (by rfl) ⟨381597, by rfl⟩ : syracuseStep 1017593 = 763195) B763195
theorem B1214281 : Blo 354756 1214281 := bstep (se 2 (by rfl) ⟨455355, by rfl⟩ : syracuseStep 1214281 = 910711) B910711
theorem B1804193 : Blo 354756 1804193 := bstep (se 2 (by rfl) ⟨676572, by rfl⟩ : syracuseStep 1804193 = 1353145) B1353145
theorem B1017775 : Blo 354756 1017775 := bstep (se 1 (by rfl) ⟨763331, by rfl⟩ : syracuseStep 1017775 = 1526663) B1526663
theorem B1083449 : Blo 354756 1083449 := bstep (se 2 (by rfl) ⟨406293, by rfl⟩ : syracuseStep 1083449 = 812587) B812587
theorem B1214939 : Blo 354756 1214939 := bstep (se 1 (by rfl) ⟨911204, by rfl⟩ : syracuseStep 1214939 = 1822409) B1822409
theorem B723419 : Blo 354756 723419 := bstep (se 1 (by rfl) ⟨542564, by rfl⟩ : syracuseStep 723419 = 1085129) B1085129
theorem B1019051 : Blo 354756 1019051 := bstep (se 1 (by rfl) ⟨764288, by rfl⟩ : syracuseStep 1019051 = 1528577) B1528577
theorem B1019279 : Blo 354756 1019279 := bstep (se 1 (by rfl) ⟨764459, by rfl⟩ : syracuseStep 1019279 = 1528919) B1528919
theorem B855539 : Blo 354756 855539 := bstep (se 1 (by rfl) ⟨641654, by rfl⟩ : syracuseStep 855539 = 1283309) B1283309
theorem B1347131 : Blo 354756 1347131 := bstep (se 1 (by rfl) ⟨1010348, by rfl⟩ : syracuseStep 1347131 = 2020697) B2020697
theorem B5312087 : Blo 354756 5312087 := bstep (se 1 (by rfl) ⟨3984065, by rfl⟩ : syracuseStep 5312087 = 7968131) B7968131
theorem B9146033 : Blo 354756 9146033 := bstep (se 2 (by rfl) ⟨3429762, by rfl⟩ : syracuseStep 9146033 = 6859525) B6859525
theorem B2723543 : Blo 354756 2723543 := bstep (se 1 (by rfl) ⟨2042657, by rfl⟩ : syracuseStep 2723543 = 4085315) B4085315
theorem B2560157 : Blo 354756 2560157 := bstep (se 3 (by rfl) ⟨480029, by rfl⟩ : syracuseStep 2560157 = 960059) B960059
theorem B1085687 : Blo 354756 1085687 := bstep (se 1 (by rfl) ⟨814265, by rfl⟩ : syracuseStep 1085687 = 1628531) B1628531
theorem B2298401 : Blo 354756 2298401 := bstep (se 2 (by rfl) ⟨861900, by rfl⟩ : syracuseStep 2298401 = 1723801) B1723801
theorem B856673 : Blo 354756 856673 := bstep (se 2 (by rfl) ⟨321252, by rfl⟩ : syracuseStep 856673 = 642505) B642505
theorem B1348285 : Blo 354756 1348285 := bstep (se 3 (by rfl) ⟨252803, by rfl⟩ : syracuseStep 1348285 = 505607) B505607
theorem B3248849 : Blo 354756 3248849 := bstep (se 2 (by rfl) ⟨1218318, by rfl⟩ : syracuseStep 3248849 = 2436637) B2436637
theorem B1349243 : Blo 354756 1349243 := bstep (se 1 (by rfl) ⟨1011932, by rfl⟩ : syracuseStep 1349243 = 2023865) B2023865
theorem B1545875 : Blo 354756 1545875 := bstep (se 1 (by rfl) ⟨1159406, by rfl⟩ : syracuseStep 1545875 = 2318813) B2318813
theorem B399199 : Blo 354756 399199 := bstep (se 1 (by rfl) ⟨299399, by rfl⟩ : syracuseStep 399199 = 598799) B598799
theorem B727003 : Blo 354756 727003 := bstep (se 1 (by rfl) ⟨545252, by rfl⟩ : syracuseStep 727003 = 1090505) B1090505
theorem B8755289 : Blo 354756 8755289 := bstep (se 2 (by rfl) ⟨3283233, by rfl⟩ : syracuseStep 8755289 = 6566467) B6566467
theorem B399559 : Blo 354756 399559 := bstep (se 1 (by rfl) ⟨299669, by rfl⟩ : syracuseStep 399559 = 599339) B599339
theorem B23107841 : Blo 354756 23107841 := bstep (se 2 (by rfl) ⟨8665440, by rfl⟩ : syracuseStep 23107841 = 17330881) B17330881
theorem B1350017 : Blo 354756 1350017 := bstep (se 2 (by rfl) ⟨506256, by rfl⟩ : syracuseStep 1350017 = 1012513) B1012513
theorem B3840493 : Blo 354756 3840493 := bstep (se 3 (by rfl) ⟨720092, by rfl⟩ : syracuseStep 3840493 = 1440185) B1440185
theorem B2563073 : Blo 354756 2563073 := bstep (se 2 (by rfl) ⟨961152, by rfl⟩ : syracuseStep 2563073 = 1922305) B1922305
theorem B400423 : Blo 354756 400423 := bstep (se 1 (by rfl) ⟨300317, by rfl⟩ : syracuseStep 400423 = 600635) B600635
theorem B760889 : Blo 354756 760889 := bstep (se 2 (by rfl) ⟨285333, by rfl⟩ : syracuseStep 760889 = 570667) B570667
theorem B761231 : Blo 354756 761231 := bstep (se 1 (by rfl) ⟨570923, by rfl⟩ : syracuseStep 761231 = 1141847) B1141847
theorem B1351201 : Blo 354756 1351201 := bstep (se 2 (by rfl) ⟨506700, by rfl⟩ : syracuseStep 1351201 = 1013401) B1013401
theorem B761555 : Blo 354756 761555 := bstep (se 1 (by rfl) ⟨571166, by rfl⟩ : syracuseStep 761555 = 1142333) B1142333
theorem B38969059 : Blo 354756 38969059 := bstep (se 1 (by rfl) ⟨29226794, by rfl⟩ : syracuseStep 38969059 = 58453589) B58453589
theorem B532217 : Blo 354756 532217 := bstep (se 2 (by rfl) ⟨199581, by rfl⟩ : syracuseStep 532217 = 399163) B399163
theorem B4890401 : Blo 354756 4890401 := bstep (se 2 (by rfl) ⟨1833900, by rfl⟩ : syracuseStep 4890401 = 3667801) B3667801
theorem B1285931 : Blo 354756 1285931 := bstep (se 1 (by rfl) ⟨964448, by rfl⟩ : syracuseStep 1285931 = 1928897) B1928897
theorem B532319 : Blo 354756 532319 := bstep (se 1 (by rfl) ⟨399239, by rfl⟩ : syracuseStep 532319 = 798479) B798479
theorem B532331 : Blo 354756 532331 := bstep (se 1 (by rfl) ⟨399248, by rfl⟩ : syracuseStep 532331 = 798497) B798497
theorem B1351687 : Blo 354756 1351687 := bstep (se 1 (by rfl) ⟨1013765, by rfl⟩ : syracuseStep 1351687 = 2027531) B2027531
theorem B532559 : Blo 354756 532559 := bstep (se 1 (by rfl) ⟨399419, by rfl⟩ : syracuseStep 532559 = 798839) B798839
theorem B3842225 : Blo 354756 3842225 := bstep (se 2 (by rfl) ⟨1440834, by rfl⟩ : syracuseStep 3842225 = 2881669) B2881669
theorem B532679 : Blo 354756 532679 := bstep (se 1 (by rfl) ⟨399509, by rfl⟩ : syracuseStep 532679 = 799019) B799019
theorem B532841 : Blo 354756 532841 := bstep (se 2 (by rfl) ⟨199815, by rfl⟩ : syracuseStep 532841 = 399631) B399631
theorem B2892185 : Blo 354756 2892185 := bstep (se 2 (by rfl) ⟨1084569, by rfl⟩ : syracuseStep 2892185 = 2169139) B2169139
theorem B532919 : Blo 354756 532919 := bstep (se 1 (by rfl) ⟨399689, by rfl⟩ : syracuseStep 532919 = 799379) B799379
theorem B532955 : Blo 354756 532955 := bstep (se 1 (by rfl) ⟨399716, by rfl⟩ : syracuseStep 532955 = 799433) B799433
theorem B1352173 : Blo 354756 1352173 := bstep (se 3 (by rfl) ⟨253532, by rfl⟩ : syracuseStep 1352173 = 507065) B507065
theorem B402043 : Blo 354756 402043 := bstep (se 1 (by rfl) ⟨301532, by rfl⟩ : syracuseStep 402043 = 603065) B603065
theorem B1352477 : Blo 354756 1352477 := bstep (se 3 (by rfl) ⟨253589, by rfl⟩ : syracuseStep 1352477 = 507179) B507179
theorem B2564941 : Blo 354756 2564941 := bstep (se 3 (by rfl) ⟨480926, by rfl⟩ : syracuseStep 2564941 = 961853) B961853
theorem B598927 : Blo 354756 598927 := bstep (se 1 (by rfl) ⟨449195, by rfl⟩ : syracuseStep 598927 = 898391) B898391
theorem B762785 : Blo 354756 762785 := bstep (se 2 (by rfl) ⟨286044, by rfl⟩ : syracuseStep 762785 = 572089) B572089
theorem B533423 : Blo 354756 533423 := bstep (se 1 (by rfl) ⟨400067, by rfl⟩ : syracuseStep 533423 = 800135) B800135
theorem B533513 : Blo 354756 533513 := bstep (se 2 (by rfl) ⟨200067, by rfl⟩ : syracuseStep 533513 = 400135) B400135
theorem B730151 : Blo 354756 730151 := bstep (se 1 (by rfl) ⟨547613, by rfl⟩ : syracuseStep 730151 = 1095227) B1095227
theorem B533543 : Blo 354756 533543 := bstep (se 1 (by rfl) ⟨400157, by rfl⟩ : syracuseStep 533543 = 800315) B800315
theorem B402511 : Blo 354756 402511 := bstep (se 1 (by rfl) ⟨301883, by rfl⟩ : syracuseStep 402511 = 603767) B603767
theorem B533627 : Blo 354756 533627 := bstep (se 1 (by rfl) ⟨400220, by rfl⟩ : syracuseStep 533627 = 800441) B800441
theorem B959735 : Blo 354756 959735 := bstep (se 1 (by rfl) ⟨719801, by rfl⟩ : syracuseStep 959735 = 1439603) B1439603
theorem B533753 : Blo 354756 533753 := bstep (se 2 (by rfl) ⟨200157, by rfl⟩ : syracuseStep 533753 = 400315) B400315
theorem B533855 : Blo 354756 533855 := bstep (se 1 (by rfl) ⟨400391, by rfl⟩ : syracuseStep 533855 = 800783) B800783
theorem B533867 : Blo 354756 533867 := bstep (se 1 (by rfl) ⟨400400, by rfl⟩ : syracuseStep 533867 = 800801) B800801
theorem B402907 : Blo 354756 402907 := bstep (se 1 (by rfl) ⟨302180, by rfl⟩ : syracuseStep 402907 = 604361) B604361
theorem B599609 : Blo 354756 599609 := bstep (se 2 (by rfl) ⟨224853, by rfl⟩ : syracuseStep 599609 = 449707) B449707
theorem B37561931 : Blo 354756 37561931 := bstep (se 1 (by rfl) ⟨28171448, by rfl⟩ : syracuseStep 37561931 = 56342897) B56342897
theorem B534095 : Blo 354756 534095 := bstep (se 1 (by rfl) ⟨400571, by rfl⟩ : syracuseStep 534095 = 801143) B801143
theorem B534215 : Blo 354756 534215 := bstep (se 1 (by rfl) ⟨400661, by rfl⟩ : syracuseStep 534215 = 801323) B801323
theorem B534377 : Blo 354756 534377 := bstep (se 2 (by rfl) ⟨200391, by rfl⟩ : syracuseStep 534377 = 400783) B400783
theorem B403375 : Blo 354756 403375 := bstep (se 1 (by rfl) ⟨302531, by rfl⟩ : syracuseStep 403375 = 605063) B605063
theorem B534455 : Blo 354756 534455 := bstep (se 1 (by rfl) ⟨400841, by rfl⟩ : syracuseStep 534455 = 801683) B801683
theorem B993211 : Blo 354756 993211 := bstep (se 1 (by rfl) ⟨744908, by rfl⟩ : syracuseStep 993211 = 1489817) B1489817
theorem B2041793 : Blo 354756 2041793 := bstep (se 2 (by rfl) ⟨765672, by rfl⟩ : syracuseStep 2041793 = 1531345) B1531345
theorem B534491 : Blo 354756 534491 := bstep (se 1 (by rfl) ⟨400868, by rfl⟩ : syracuseStep 534491 = 801737) B801737
theorem B600311 : Blo 354756 600311 := bstep (se 1 (by rfl) ⟨450233, by rfl⟩ : syracuseStep 600311 = 900467) B900467
theorem B2894129 : Blo 354756 2894129 := bstep (se 2 (by rfl) ⟨1085298, by rfl⟩ : syracuseStep 2894129 = 2170597) B2170597
theorem B960893 : Blo 354756 960893 := bstep (se 3 (by rfl) ⟨180167, by rfl⟩ : syracuseStep 960893 = 360335) B360335
theorem B534959 : Blo 354756 534959 := bstep (se 1 (by rfl) ⟨401219, by rfl⟩ : syracuseStep 534959 = 802439) B802439
theorem B535049 : Blo 354756 535049 := bstep (se 2 (by rfl) ⟨200643, by rfl⟩ : syracuseStep 535049 = 401287) B401287
theorem B764425 : Blo 354756 764425 := bstep (se 2 (by rfl) ⟨286659, by rfl⟩ : syracuseStep 764425 = 573319) B573319
theorem B535079 : Blo 354756 535079 := bstep (se 1 (by rfl) ⟨401309, by rfl⟩ : syracuseStep 535079 = 802619) B802619
theorem B600655 : Blo 354756 600655 := bstep (se 1 (by rfl) ⟨450491, by rfl⟩ : syracuseStep 600655 = 900983) B900983
theorem B535163 : Blo 354756 535163 := bstep (se 1 (by rfl) ⟨401372, by rfl⟩ : syracuseStep 535163 = 802745) B802745
theorem B535289 : Blo 354756 535289 := bstep (se 2 (by rfl) ⟨200733, by rfl⟩ : syracuseStep 535289 = 401467) B401467
theorem B600905 : Blo 354756 600905 := bstep (se 2 (by rfl) ⟨225339, by rfl⟩ : syracuseStep 600905 = 450679) B450679
theorem B535391 : Blo 354756 535391 := bstep (se 1 (by rfl) ⟨401543, by rfl⟩ : syracuseStep 535391 = 803087) B803087
theorem B1354603 : Blo 354756 1354603 := bstep (se 1 (by rfl) ⟨1015952, by rfl⟩ : syracuseStep 1354603 = 2031905) B2031905
theorem B535403 : Blo 354756 535403 := bstep (se 1 (by rfl) ⟨401552, by rfl⟩ : syracuseStep 535403 = 803105) B803105
theorem B601145 : Blo 354756 601145 := bstep (se 2 (by rfl) ⟨225429, by rfl⟩ : syracuseStep 601145 = 450859) B450859
theorem B535631 : Blo 354756 535631 := bstep (se 1 (by rfl) ⟨401723, by rfl⟩ : syracuseStep 535631 = 803447) B803447
theorem B2174147 : Blo 354756 2174147 := bstep (se 1 (by rfl) ⟨1630610, by rfl⟩ : syracuseStep 2174147 = 3261221) B3261221
theorem B535751 : Blo 354756 535751 := bstep (se 1 (by rfl) ⟨401813, by rfl⟩ : syracuseStep 535751 = 803627) B803627
theorem B1813751 : Blo 354756 1813751 := bstep (se 1 (by rfl) ⟨1360313, by rfl⟩ : syracuseStep 1813751 = 2720627) B2720627
theorem B601337 : Blo 354756 601337 := bstep (se 2 (by rfl) ⟨225501, by rfl⟩ : syracuseStep 601337 = 451003) B451003
theorem B535913 : Blo 354756 535913 := bstep (se 2 (by rfl) ⟨200967, by rfl⟩ : syracuseStep 535913 = 401935) B401935
theorem B601519 : Blo 354756 601519 := bstep (se 1 (by rfl) ⟨451139, by rfl⟩ : syracuseStep 601519 = 902279) B902279
theorem B535991 : Blo 354756 535991 := bstep (se 1 (by rfl) ⟨401993, by rfl⟩ : syracuseStep 535991 = 803987) B803987
theorem B536027 : Blo 354756 536027 := bstep (se 1 (by rfl) ⟨402020, by rfl⟩ : syracuseStep 536027 = 804041) B804041
theorem B601607 : Blo 354756 601607 := bstep (se 1 (by rfl) ⟨451205, by rfl⟩ : syracuseStep 601607 = 902411) B902411
theorem B2895421 : Blo 354756 2895421 := bstep (se 3 (by rfl) ⟨542891, by rfl⟩ : syracuseStep 2895421 = 1085783) B1085783
theorem B798407 : Blo 354756 798407 := bstep (se 1 (by rfl) ⟨598805, by rfl⟩ : syracuseStep 798407 = 1197611) B1197611
theorem B1814237 : Blo 354756 1814237 := bstep (se 3 (by rfl) ⟨340169, by rfl⟩ : syracuseStep 1814237 = 680339) B680339
theorem B2797379 : Blo 354756 2797379 := bstep (se 1 (by rfl) ⟨2098034, by rfl⟩ : syracuseStep 2797379 = 4196069) B4196069
theorem B601951 : Blo 354756 601951 := bstep (se 1 (by rfl) ⟨451463, by rfl⟩ : syracuseStep 601951 = 902927) B902927
theorem B536495 : Blo 354756 536495 := bstep (se 1 (by rfl) ⟨402371, by rfl⟩ : syracuseStep 536495 = 804743) B804743
theorem B602039 : Blo 354756 602039 := bstep (se 1 (by rfl) ⟨451529, by rfl⟩ : syracuseStep 602039 = 903059) B903059
theorem B536585 : Blo 354756 536585 := bstep (se 2 (by rfl) ⟨201219, by rfl⟩ : syracuseStep 536585 = 402439) B402439
theorem B536615 : Blo 354756 536615 := bstep (se 1 (by rfl) ⟨402461, by rfl⟩ : syracuseStep 536615 = 804923) B804923
theorem B536699 : Blo 354756 536699 := bstep (se 1 (by rfl) ⟨402524, by rfl⟩ : syracuseStep 536699 = 805049) B805049
theorem B536825 : Blo 354756 536825 := bstep (se 2 (by rfl) ⟨201309, by rfl⟩ : syracuseStep 536825 = 402619) B402619
theorem B536927 : Blo 354756 536927 := bstep (se 1 (by rfl) ⟨402695, by rfl⟩ : syracuseStep 536927 = 805391) B805391
theorem B536939 : Blo 354756 536939 := bstep (se 1 (by rfl) ⟨402704, by rfl⟩ : syracuseStep 536939 = 805409) B805409
theorem B733601 : Blo 354756 733601 := bstep (se 2 (by rfl) ⟨275100, by rfl⟩ : syracuseStep 733601 = 550201) B550201
theorem B602633 : Blo 354756 602633 := bstep (se 2 (by rfl) ⟨225987, by rfl⟩ : syracuseStep 602633 = 451975) B451975
theorem B799271 : Blo 354756 799271 := bstep (se 1 (by rfl) ⟨599453, by rfl⟩ : syracuseStep 799271 = 1198907) B1198907
theorem B537167 : Blo 354756 537167 := bstep (se 1 (by rfl) ⟨402875, by rfl⟩ : syracuseStep 537167 = 805751) B805751
theorem B602795 : Blo 354756 602795 := bstep (se 1 (by rfl) ⟨452096, by rfl⟩ : syracuseStep 602795 = 904193) B904193
theorem B537287 : Blo 354756 537287 := bstep (se 1 (by rfl) ⟨402965, by rfl⟩ : syracuseStep 537287 = 805931) B805931
theorem B8630995 : Blo 354756 8630995 := bstep (se 1 (by rfl) ⟨6473246, by rfl⟩ : syracuseStep 8630995 = 12946493) B12946493
theorem B537449 : Blo 354756 537449 := bstep (se 2 (by rfl) ⟨201543, by rfl⟩ : syracuseStep 537449 = 403087) B403087
theorem B799595 : Blo 354756 799595 := bstep (se 1 (by rfl) ⟨599696, by rfl⟩ : syracuseStep 799595 = 1199393) B1199393
theorem B799649 : Blo 354756 799649 := bstep (se 2 (by rfl) ⟨299868, by rfl⟩ : syracuseStep 799649 = 599737) B599737
theorem B2700215 : Blo 354756 2700215 := bstep (se 1 (by rfl) ⟨2025161, by rfl⟩ : syracuseStep 2700215 = 4050323) B4050323
theorem B537527 : Blo 354756 537527 := bstep (se 1 (by rfl) ⟨403145, by rfl⟩ : syracuseStep 537527 = 806291) B806291
theorem B537563 : Blo 354756 537563 := bstep (se 1 (by rfl) ⟨403172, by rfl⟩ : syracuseStep 537563 = 806345) B806345
theorem B898067 : Blo 354756 898067 := bstep (se 1 (by rfl) ⟨673550, by rfl⟩ : syracuseStep 898067 = 1347101) B1347101
theorem B603193 : Blo 354756 603193 := bstep (se 2 (by rfl) ⟨226197, by rfl⟩ : syracuseStep 603193 = 452395) B452395
theorem B603335 : Blo 354756 603335 := bstep (se 1 (by rfl) ⟨452501, by rfl⟩ : syracuseStep 603335 = 905003) B905003
theorem B799991 : Blo 354756 799991 := bstep (se 1 (by rfl) ⟨599993, by rfl⟩ : syracuseStep 799991 = 1199987) B1199987
theorem B603497 : Blo 354756 603497 := bstep (se 2 (by rfl) ⟨226311, by rfl⟩ : syracuseStep 603497 = 452623) B452623
theorem B538031 : Blo 354756 538031 := bstep (se 1 (by rfl) ⟨403523, by rfl⟩ : syracuseStep 538031 = 807047) B807047
theorem B898523 : Blo 354756 898523 := bstep (se 1 (by rfl) ⟨673892, by rfl⟩ : syracuseStep 898523 = 1347785) B1347785
theorem B538121 : Blo 354756 538121 := bstep (se 2 (by rfl) ⟨201795, by rfl⟩ : syracuseStep 538121 = 403591) B403591
theorem B1357337 : Blo 354756 1357337 := bstep (se 2 (by rfl) ⟨509001, by rfl⟩ : syracuseStep 1357337 = 1018003) B1018003
theorem B5518891 : Blo 354756 5518891 := bstep (se 1 (by rfl) ⟨4139168, by rfl⟩ : syracuseStep 5518891 = 8278337) B8278337
theorem B603895 : Blo 354756 603895 := bstep (se 1 (by rfl) ⟨452921, by rfl⟩ : syracuseStep 603895 = 905843) B905843
theorem B800585 : Blo 354756 800585 := bstep (se 2 (by rfl) ⟨300219, by rfl⟩ : syracuseStep 800585 = 600439) B600439
theorem B1718111 : Blo 354756 1718111 := bstep (se 1 (by rfl) ⟨1288583, by rfl⟩ : syracuseStep 1718111 = 2577167) B2577167
theorem B604091 : Blo 354756 604091 := bstep (se 1 (by rfl) ⟨453068, by rfl⟩ : syracuseStep 604091 = 906137) B906137
theorem B604199 : Blo 354756 604199 := bstep (se 1 (by rfl) ⟨453149, by rfl⟩ : syracuseStep 604199 = 906299) B906299
theorem B735311 : Blo 354756 735311 := bstep (se 1 (by rfl) ⟨551483, by rfl⟩ : syracuseStep 735311 = 1102967) B1102967
theorem B604489 : Blo 354756 604489 := bstep (se 2 (by rfl) ⟨226683, by rfl⟩ : syracuseStep 604489 = 453367) B453367
theorem B2701673 : Blo 354756 2701673 := bstep (se 2 (by rfl) ⟨1013127, by rfl⟩ : syracuseStep 2701673 = 2026255) B2026255
theorem B604523 : Blo 354756 604523 := bstep (se 1 (by rfl) ⟨453392, by rfl⟩ : syracuseStep 604523 = 906785) B906785
theorem B571961 : Blo 354756 571961 := bstep (se 2 (by rfl) ⟨214485, by rfl⟩ : syracuseStep 571961 = 428971) B428971
theorem B801377 : Blo 354756 801377 := bstep (se 2 (by rfl) ⟨300516, by rfl⟩ : syracuseStep 801377 = 601033) B601033
theorem B899707 : Blo 354756 899707 := bstep (se 1 (by rfl) ⟨674780, by rfl⟩ : syracuseStep 899707 = 1349561) B1349561
theorem B604921 : Blo 354756 604921 := bstep (se 2 (by rfl) ⟨226845, by rfl⟩ : syracuseStep 604921 = 453691) B453691
theorem B801719 : Blo 354756 801719 := bstep (se 1 (by rfl) ⟨601289, by rfl⟩ : syracuseStep 801719 = 1202579) B1202579
theorem B605191 : Blo 354756 605191 := bstep (se 1 (by rfl) ⟨453893, by rfl⟩ : syracuseStep 605191 = 907787) B907787
theorem B1358963 : Blo 354756 1358963 := bstep (se 1 (by rfl) ⟨1019222, by rfl⟩ : syracuseStep 1358963 = 2038445) B2038445
theorem B2440385 : Blo 354756 2440385 := bstep (se 2 (by rfl) ⟨915144, by rfl⟩ : syracuseStep 2440385 = 1830289) B1830289
theorem B6110477 : Blo 354756 6110477 := bstep (se 3 (by rfl) ⟨1145714, by rfl⟩ : syracuseStep 6110477 = 2291429) B2291429
theorem B1719575 : Blo 354756 1719575 := bstep (se 1 (by rfl) ⟨1289681, by rfl⟩ : syracuseStep 1719575 = 2579363) B2579363
theorem B41729539 : Blo 354756 41729539 := bstep (se 1 (by rfl) ⟨31297154, by rfl⟩ : syracuseStep 41729539 = 62594309) B62594309
theorem B572935 : Blo 354756 572935 := bstep (se 1 (by rfl) ⟨429701, by rfl⟩ : syracuseStep 572935 = 859403) B859403
theorem B802313 : Blo 354756 802313 := bstep (se 2 (by rfl) ⟨300867, by rfl⟩ : syracuseStep 802313 = 601735) B601735
theorem B11550539 : Blo 354756 11550539 := bstep (se 1 (by rfl) ⟨8662904, by rfl⟩ : syracuseStep 11550539 = 17325809) B17325809
theorem B802655 : Blo 354756 802655 := bstep (se 1 (by rfl) ⟨601991, by rfl⟩ : syracuseStep 802655 = 1203983) B1203983
theorem B540521 : Blo 354756 540521 := bstep (se 2 (by rfl) ⟨202695, by rfl⟩ : syracuseStep 540521 = 405391) B405391
theorem B23117683 : Blo 354756 23117683 := bstep (se 1 (by rfl) ⟨17338262, by rfl⟩ : syracuseStep 23117683 = 34676525) B34676525
theorem B1392641 : Blo 354756 1392641 := bstep (se 2 (by rfl) ⟨522240, by rfl⟩ : syracuseStep 1392641 = 1044481) B1044481
theorem B802835 : Blo 354756 802835 := bstep (se 1 (by rfl) ⟨602126, by rfl⟩ : syracuseStep 802835 = 1204253) B1204253
theorem B2703617 : Blo 354756 2703617 := bstep (se 2 (by rfl) ⟨1013856, by rfl⟩ : syracuseStep 2703617 = 2027713) B2027713
theorem B11583755 : Blo 354756 11583755 := bstep (se 1 (by rfl) ⟨8687816, by rfl⟩ : syracuseStep 11583755 = 17375633) B17375633
theorem B803177 : Blo 354756 803177 := bstep (se 2 (by rfl) ⟨301191, by rfl⟩ : syracuseStep 803177 = 602383) B602383
theorem B1360253 : Blo 354756 1360253 := bstep (se 3 (by rfl) ⟨255047, by rfl⟩ : syracuseStep 1360253 = 510095) B510095
theorem B869063 : Blo 354756 869063 := bstep (se 1 (by rfl) ⟨651797, by rfl⟩ : syracuseStep 869063 = 1303595) B1303595
theorem B2900681 : Blo 354756 2900681 := bstep (se 2 (by rfl) ⟨1087755, by rfl⟩ : syracuseStep 2900681 = 2175511) B2175511
theorem B607081 : Blo 354756 607081 := bstep (se 2 (by rfl) ⟨227655, by rfl⟩ : syracuseStep 607081 = 455311) B455311
theorem B803771 : Blo 354756 803771 := bstep (se 1 (by rfl) ⟨602828, by rfl⟩ : syracuseStep 803771 = 1205657) B1205657
theorem B803897 : Blo 354756 803897 := bstep (se 2 (by rfl) ⟨301461, by rfl⟩ : syracuseStep 803897 = 602923) B602923
theorem B574543 : Blo 354756 574543 := bstep (se 1 (by rfl) ⟨430907, by rfl⟩ : syracuseStep 574543 = 861815) B861815
theorem B541895 : Blo 354756 541895 := bstep (se 1 (by rfl) ⟨406421, by rfl⟩ : syracuseStep 541895 = 812843) B812843
theorem B804239 : Blo 354756 804239 := bstep (se 1 (by rfl) ⟨603179, by rfl⟩ : syracuseStep 804239 = 1206359) B1206359
theorem B1721843 : Blo 354756 1721843 := bstep (se 1 (by rfl) ⟨1291382, by rfl⟩ : syracuseStep 1721843 = 2582765) B2582765
theorem B1197665 : Blo 354756 1197665 := bstep (se 2 (by rfl) ⟨449124, by rfl⟩ : syracuseStep 1197665 = 898249) B898249
theorem B804563 : Blo 354756 804563 := bstep (se 1 (by rfl) ⟨603422, by rfl⟩ : syracuseStep 804563 = 1206845) B1206845
theorem B641063 : Blo 354756 641063 := bstep (se 1 (by rfl) ⟨480797, by rfl⟩ : syracuseStep 641063 = 961595) B961595
theorem B5163097 : Blo 354756 5163097 := bstep (se 2 (by rfl) ⟨1936161, by rfl⟩ : syracuseStep 5163097 = 3872323) B3872323
theorem B673915 : Blo 354756 673915 := bstep (se 1 (by rfl) ⟨505436, by rfl⟩ : syracuseStep 673915 = 1010873) B1010873
theorem B3426461 : Blo 354756 3426461 := bstep (se 3 (by rfl) ⟨642461, by rfl⟩ : syracuseStep 3426461 = 1284923) B1284923
theorem B968861 : Blo 354756 968861 := bstep (se 3 (by rfl) ⟨181661, by rfl⟩ : syracuseStep 968861 = 363323) B363323
theorem B673991 : Blo 354756 673991 := bstep (se 1 (by rfl) ⟨505493, by rfl⟩ : syracuseStep 673991 = 1010987) B1010987
theorem B510391 : Blo 354756 510391 := bstep (se 1 (by rfl) ⟨382793, by rfl⟩ : syracuseStep 510391 = 765587) B765587
theorem B6834617 : Blo 354756 6834617 := bstep (se 2 (by rfl) ⟨2562981, by rfl⟩ : syracuseStep 6834617 = 5125963) B5125963
theorem B674401 : Blo 354756 674401 := bstep (se 2 (by rfl) ⟨252900, by rfl⟩ : syracuseStep 674401 = 505801) B505801
theorem B805499 : Blo 354756 805499 := bstep (se 1 (by rfl) ⟨604124, by rfl⟩ : syracuseStep 805499 = 1208249) B1208249
theorem B805625 : Blo 354756 805625 := bstep (se 2 (by rfl) ⟨302109, by rfl⟩ : syracuseStep 805625 = 604219) B604219
theorem B904031 : Blo 354756 904031 := bstep (se 1 (by rfl) ⟨678023, by rfl⟩ : syracuseStep 904031 = 1356047) B1356047
theorem B674743 : Blo 354756 674743 := bstep (se 1 (by rfl) ⟨506057, by rfl⟩ : syracuseStep 674743 = 1012115) B1012115
theorem B805895 : Blo 354756 805895 := bstep (se 1 (by rfl) ⟨604421, by rfl⟩ : syracuseStep 805895 = 1208843) B1208843
theorem B1199123 : Blo 354756 1199123 := bstep (se 1 (by rfl) ⟨899342, by rfl⟩ : syracuseStep 1199123 = 1798685) B1798685
theorem B805967 : Blo 354756 805967 := bstep (se 1 (by rfl) ⟨604475, by rfl⟩ : syracuseStep 805967 = 1208951) B1208951
theorem B675145 : Blo 354756 675145 := bstep (se 2 (by rfl) ⟨253179, by rfl⟩ : syracuseStep 675145 = 506359) B506359
theorem B1199447 : Blo 354756 1199447 := bstep (se 1 (by rfl) ⟨899585, by rfl⟩ : syracuseStep 1199447 = 1799171) B1799171
theorem B4345177 : Blo 354756 4345177 := bstep (se 2 (by rfl) ⟨1629441, by rfl⟩ : syracuseStep 4345177 = 3258883) B3258883
theorem B806363 : Blo 354756 806363 := bstep (se 1 (by rfl) ⟨604772, by rfl⟩ : syracuseStep 806363 = 1209545) B1209545
theorem B904729 : Blo 354756 904729 := bstep (se 2 (by rfl) ⟨339273, by rfl⟩ : syracuseStep 904729 = 678547) B678547
theorem B2281283 : Blo 354756 2281283 := bstep (se 1 (by rfl) ⟨1710962, by rfl⟩ : syracuseStep 2281283 = 3421925) B3421925
theorem B905033 : Blo 354756 905033 := bstep (se 2 (by rfl) ⟨339387, by rfl⟩ : syracuseStep 905033 = 678775) B678775
theorem B479083 : Blo 354756 479083 := bstep (se 1 (by rfl) ⟨359312, by rfl⟩ : syracuseStep 479083 = 718625) B718625
theorem B806831 : Blo 354756 806831 := bstep (se 1 (by rfl) ⟨605123, by rfl⟩ : syracuseStep 806831 = 1210247) B1210247
theorem B675859 : Blo 354756 675859 := bstep (se 1 (by rfl) ⟨506894, by rfl⟩ : syracuseStep 675859 = 1013789) B1013789
theorem B1626193 : Blo 354756 1626193 := bstep (se 2 (by rfl) ⟨609822, by rfl⟩ : syracuseStep 1626193 = 1219645) B1219645
theorem B807083 : Blo 354756 807083 := bstep (se 1 (by rfl) ⟨605312, by rfl⟩ : syracuseStep 807083 = 1210625) B1210625
theorem B3297509 : Blo 354756 3297509 := bstep (se 4 (by rfl) ⟨309141, by rfl⟩ : syracuseStep 3297509 = 618283) B618283
theorem B676201 : Blo 354756 676201 := bstep (se 2 (by rfl) ⟨253575, by rfl⟩ : syracuseStep 676201 = 507151) B507151
theorem B1200527 : Blo 354756 1200527 := bstep (se 1 (by rfl) ⟨900395, by rfl⟩ : syracuseStep 1200527 = 1800791) B1800791
theorem B2904473 : Blo 354756 2904473 := bstep (se 2 (by rfl) ⟨1089177, by rfl⟩ : syracuseStep 2904473 = 2178355) B2178355
theorem B610823 : Blo 354756 610823 := bstep (se 1 (by rfl) ⟨458117, by rfl⟩ : syracuseStep 610823 = 916235) B916235
theorem B2707991 : Blo 354756 2707991 := bstep (se 1 (by rfl) ⟨2030993, by rfl⟩ : syracuseStep 2707991 = 4061987) B4061987
theorem B1200851 : Blo 354756 1200851 := bstep (se 1 (by rfl) ⟨900638, by rfl⟩ : syracuseStep 1200851 = 1801277) B1801277
theorem B5493577 : Blo 354756 5493577 := bstep (se 2 (by rfl) ⟨2060091, by rfl⟩ : syracuseStep 5493577 = 4120183) B4120183
theorem B381871 : Blo 354756 381871 := bstep (se 1 (by rfl) ⟨286403, by rfl⟩ : syracuseStep 381871 = 572807) B572807
theorem B906167 : Blo 354756 906167 := bstep (se 1 (by rfl) ⟨679625, by rfl⟩ : syracuseStep 906167 = 1359251) B1359251
theorem B480619 : Blo 354756 480619 := bstep (se 1 (by rfl) ⟨360464, by rfl⟩ : syracuseStep 480619 = 720929) B720929
theorem B2446793 : Blo 354756 2446793 := bstep (se 2 (by rfl) ⟨917547, by rfl⟩ : syracuseStep 2446793 = 1835095) B1835095
theorem B1529533 : Blo 354756 1529533 := bstep (se 3 (by rfl) ⟨286787, by rfl⟩ : syracuseStep 1529533 = 573575) B573575
theorem B677575 : Blo 354756 677575 := bstep (se 1 (by rfl) ⟨508181, by rfl⟩ : syracuseStep 677575 = 1016363) B1016363
theorem B2447147 : Blo 354756 2447147 := bstep (se 1 (by rfl) ⟨1835360, by rfl⟩ : syracuseStep 2447147 = 3670721) B3670721
theorem B3266399 : Blo 354756 3266399 := bstep (se 1 (by rfl) ⟨2449799, by rfl⟩ : syracuseStep 3266399 = 4899599) B4899599
theorem B1202039 : Blo 354756 1202039 := bstep (se 1 (by rfl) ⟨901529, by rfl⟩ : syracuseStep 1202039 = 1803059) B1803059
theorem B907271 : Blo 354756 907271 := bstep (se 1 (by rfl) ⟨680453, by rfl⟩ : syracuseStep 907271 = 1360907) B1360907
theorem B907321 : Blo 354756 907321 := bstep (se 2 (by rfl) ⟨340245, by rfl⟩ : syracuseStep 907321 = 680491) B680491
theorem B1202255 : Blo 354756 1202255 := bstep (se 1 (by rfl) ⟨901691, by rfl⟩ : syracuseStep 1202255 = 1803383) B1803383
theorem B907625 : Blo 354756 907625 := bstep (se 2 (by rfl) ⟨340359, by rfl⟩ : syracuseStep 907625 = 680719) B680719
theorem B1202633 : Blo 354756 1202633 := bstep (se 2 (by rfl) ⟨450987, by rfl⟩ : syracuseStep 1202633 = 901975) B901975
theorem B1465031 : Blo 354756 1465031 := bstep (se 1 (by rfl) ⟨1098773, by rfl⟩ : syracuseStep 1465031 = 2197547) B2197547
theorem B1202903 : Blo 354756 1202903 := bstep (se 1 (by rfl) ⟨902177, by rfl⟩ : syracuseStep 1202903 = 1804355) B1804355
theorem B1137503 : Blo 354756 1137503 := bstep (se 1 (by rfl) ⟨853127, by rfl⟩ : syracuseStep 1137503 = 1706255) B1706255
theorem B1203119 : Blo 354756 1203119 := bstep (se 1 (by rfl) ⟨902339, by rfl⟩ : syracuseStep 1203119 = 1804679) B1804679
theorem B7691543 : Blo 354756 7691543 := bstep (se 1 (by rfl) ⟨5768657, by rfl⟩ : syracuseStep 7691543 = 11537315) B11537315
theorem B449975 : Blo 354756 449975 := bstep (se 1 (by rfl) ⟨337481, by rfl⟩ : syracuseStep 449975 = 674963) B674963
theorem B1924553 : Blo 354756 1924553 := bstep (se 2 (by rfl) ⟨721707, by rfl⟩ : syracuseStep 1924553 = 1443415) B1443415
theorem B1531379 : Blo 354756 1531379 := bstep (se 1 (by rfl) ⟨1148534, by rfl⟩ : syracuseStep 1531379 = 2297069) B2297069
theorem B450127 : Blo 354756 450127 := bstep (se 1 (by rfl) ⟨337595, by rfl⟩ : syracuseStep 450127 = 675191) B675191
theorem B679823 : Blo 354756 679823 := bstep (se 1 (by rfl) ⟨509867, by rfl⟩ : syracuseStep 679823 = 1019735) B1019735
theorem B5923277 : Blo 354756 5923277 := bstep (se 3 (by rfl) ⟨1110614, by rfl⟩ : syracuseStep 5923277 = 2221229) B2221229
theorem B811529 : Blo 354756 811529 := bstep (se 2 (by rfl) ⟨304323, by rfl⟩ : syracuseStep 811529 = 608647) B608647
theorem B451271 : Blo 354756 451271 := bstep (se 1 (by rfl) ⟨338453, by rfl⟩ : syracuseStep 451271 = 676907) B676907
theorem B451423 : Blo 354756 451423 := bstep (se 1 (by rfl) ⟨338567, by rfl⟩ : syracuseStep 451423 = 677135) B677135
theorem B680879 : Blo 354756 680879 := bstep (se 1 (by rfl) ⟨510659, by rfl⟩ : syracuseStep 680879 = 1021319) B1021319
theorem B615481 : Blo 354756 615481 := bstep (se 2 (by rfl) ⟨230805, by rfl⟩ : syracuseStep 615481 = 461611) B461611
theorem B1205495 : Blo 354756 1205495 := bstep (se 1 (by rfl) ⟨904121, by rfl⟩ : syracuseStep 1205495 = 1808243) B1808243
theorem B615775 : Blo 354756 615775 := bstep (se 1 (by rfl) ⟨461831, by rfl⟩ : syracuseStep 615775 = 923663) B923663
theorem B1205819 : Blo 354756 1205819 := bstep (se 1 (by rfl) ⟨904364, by rfl⟩ : syracuseStep 1205819 = 1808729) B1808729
theorem B6153943 : Blo 354756 6153943 := bstep (se 1 (by rfl) ⟨4615457, by rfl⟩ : syracuseStep 6153943 = 9230915) B9230915
theorem B2713337 : Blo 354756 2713337 := bstep (se 2 (by rfl) ⟨1017501, by rfl⟩ : syracuseStep 2713337 = 2035003) B2035003
theorem B1206089 : Blo 354756 1206089 := bstep (se 2 (by rfl) ⟨452283, by rfl⟩ : syracuseStep 1206089 = 904567) B904567
theorem B1140743 : Blo 354756 1140743 := bstep (se 1 (by rfl) ⟨855557, by rfl⟩ : syracuseStep 1140743 = 1711115) B1711115
theorem B354759 : Blo 354756 354759 := bstep (se 1 (by rfl) ⟨266069, by rfl⟩ : syracuseStep 354759 = 532139) B532139
theorem B354779 : Blo 354756 354779 := bstep (se 1 (by rfl) ⟨266084, by rfl⟩ : syracuseStep 354779 = 532169) B532169
theorem B354855 : Blo 354756 354855 := bstep (se 1 (by rfl) ⟨266141, by rfl⟩ : syracuseStep 354855 = 532283) B532283
theorem B1141307 : Blo 354756 1141307 := bstep (se 1 (by rfl) ⟨855980, by rfl⟩ : syracuseStep 1141307 = 1711961) B1711961
theorem B354895 : Blo 354756 354895 := bstep (se 1 (by rfl) ⟨266171, by rfl⟩ : syracuseStep 354895 = 532343) B532343
theorem B354911 : Blo 354756 354911 := bstep (se 1 (by rfl) ⟨266183, by rfl⟩ : syracuseStep 354911 = 532367) B532367
theorem B354939 : Blo 354756 354939 := bstep (se 1 (by rfl) ⟨266204, by rfl⟩ : syracuseStep 354939 = 532409) B532409
theorem B354991 : Blo 354756 354991 := bstep (se 1 (by rfl) ⟨266243, by rfl⟩ : syracuseStep 354991 = 532487) B532487
theorem B355015 : Blo 354756 355015 := bstep (se 1 (by rfl) ⟨266261, by rfl⟩ : syracuseStep 355015 = 532523) B532523
theorem B355035 : Blo 354756 355035 := bstep (se 1 (by rfl) ⟨266276, by rfl⟩ : syracuseStep 355035 = 532553) B532553
theorem B355111 : Blo 354756 355111 := bstep (se 1 (by rfl) ⟨266333, by rfl⟩ : syracuseStep 355111 = 532667) B532667
theorem B355151 : Blo 354756 355151 := bstep (se 1 (by rfl) ⟨266363, by rfl⟩ : syracuseStep 355151 = 532727) B532727
theorem B355167 : Blo 354756 355167 := bstep (se 1 (by rfl) ⟨266375, by rfl⟩ : syracuseStep 355167 = 532751) B532751
theorem B355195 : Blo 354756 355195 := bstep (se 1 (by rfl) ⟨266396, by rfl⟩ : syracuseStep 355195 = 532793) B532793
theorem B355247 : Blo 354756 355247 := bstep (se 1 (by rfl) ⟨266435, by rfl⟩ : syracuseStep 355247 = 532871) B532871
theorem B1207223 : Blo 354756 1207223 := bstep (se 1 (by rfl) ⟨905417, by rfl⟩ : syracuseStep 1207223 = 1810835) B1810835
theorem B355271 : Blo 354756 355271 := bstep (se 1 (by rfl) ⟨266453, by rfl⟩ : syracuseStep 355271 = 532907) B532907
theorem B355291 : Blo 354756 355291 := bstep (se 1 (by rfl) ⟨266468, by rfl⟩ : syracuseStep 355291 = 532937) B532937
theorem B453595 : Blo 354756 453595 := bstep (se 1 (by rfl) ⟨340196, by rfl⟩ : syracuseStep 453595 = 680393) B680393
theorem B355367 : Blo 354756 355367 := bstep (se 1 (by rfl) ⟨266525, by rfl⟩ : syracuseStep 355367 = 533051) B533051
theorem B355407 : Blo 354756 355407 := bstep (se 1 (by rfl) ⟨266555, by rfl⟩ : syracuseStep 355407 = 533111) B533111
theorem B355423 : Blo 354756 355423 := bstep (se 1 (by rfl) ⟨266567, by rfl⟩ : syracuseStep 355423 = 533135) B533135
theorem B355451 : Blo 354756 355451 := bstep (se 1 (by rfl) ⟨266588, by rfl⟩ : syracuseStep 355451 = 533177) B533177
theorem B2714795 : Blo 354756 2714795 := bstep (se 1 (by rfl) ⟨2036096, by rfl⟩ : syracuseStep 2714795 = 4072193) B4072193
theorem B355503 : Blo 354756 355503 := bstep (se 1 (by rfl) ⟨266627, by rfl⟩ : syracuseStep 355503 = 533255) B533255
theorem B355527 : Blo 354756 355527 := bstep (se 1 (by rfl) ⟨266645, by rfl⟩ : syracuseStep 355527 = 533291) B533291
theorem B355547 : Blo 354756 355547 := bstep (se 1 (by rfl) ⟨266660, by rfl⟩ : syracuseStep 355547 = 533321) B533321
theorem B355623 : Blo 354756 355623 := bstep (se 1 (by rfl) ⟨266717, by rfl⟩ : syracuseStep 355623 = 533435) B533435
theorem B355663 : Blo 354756 355663 := bstep (se 1 (by rfl) ⟨266747, by rfl⟩ : syracuseStep 355663 = 533495) B533495
theorem B355679 : Blo 354756 355679 := bstep (se 1 (by rfl) ⟨266759, by rfl⟩ : syracuseStep 355679 = 533519) B533519
theorem B355707 : Blo 354756 355707 := bstep (se 1 (by rfl) ⟨266780, by rfl⟩ : syracuseStep 355707 = 533561) B533561
theorem B4418959 : Blo 354756 4418959 := bstep (se 1 (by rfl) ⟨3314219, by rfl⟩ : syracuseStep 4418959 = 6628439) B6628439
theorem B355759 : Blo 354756 355759 := bstep (se 1 (by rfl) ⟨266819, by rfl⟩ : syracuseStep 355759 = 533639) B533639
theorem B355783 : Blo 354756 355783 := bstep (se 1 (by rfl) ⟨266837, by rfl⟩ : syracuseStep 355783 = 533675) B533675
theorem B355803 : Blo 354756 355803 := bstep (se 1 (by rfl) ⟨266852, by rfl⟩ : syracuseStep 355803 = 533705) B533705
theorem B1207817 : Blo 354756 1207817 := bstep (se 2 (by rfl) ⟨452931, by rfl⟩ : syracuseStep 1207817 = 905863) B905863
theorem B355879 : Blo 354756 355879 := bstep (se 1 (by rfl) ⟨266909, by rfl⟩ : syracuseStep 355879 = 533819) B533819
theorem B355919 : Blo 354756 355919 := bstep (se 1 (by rfl) ⟨266939, by rfl⟩ : syracuseStep 355919 = 533879) B533879
theorem B355935 : Blo 354756 355935 := bstep (se 1 (by rfl) ⟨266951, by rfl⟩ : syracuseStep 355935 = 533903) B533903
theorem B355963 : Blo 354756 355963 := bstep (se 1 (by rfl) ⟨266972, by rfl⟩ : syracuseStep 355963 = 533945) B533945
theorem B2715281 : Blo 354756 2715281 := bstep (se 2 (by rfl) ⟨1018230, by rfl⟩ : syracuseStep 2715281 = 2036461) B2036461
theorem B356015 : Blo 354756 356015 := bstep (se 1 (by rfl) ⟨267011, by rfl⟩ : syracuseStep 356015 = 534023) B534023
theorem B356039 : Blo 354756 356039 := bstep (se 1 (by rfl) ⟨267029, by rfl⟩ : syracuseStep 356039 = 534059) B534059
theorem B356059 : Blo 354756 356059 := bstep (se 1 (by rfl) ⟨267044, by rfl⟩ : syracuseStep 356059 = 534089) B534089
theorem B356135 : Blo 354756 356135 := bstep (se 1 (by rfl) ⟨267101, by rfl⟩ : syracuseStep 356135 = 534203) B534203
theorem B356175 : Blo 354756 356175 := bstep (se 1 (by rfl) ⟨267131, by rfl⟩ : syracuseStep 356175 = 534263) B534263
theorem B356191 : Blo 354756 356191 := bstep (se 1 (by rfl) ⟨267143, by rfl⟩ : syracuseStep 356191 = 534287) B534287
theorem B356219 : Blo 354756 356219 := bstep (se 1 (by rfl) ⟨267164, by rfl⟩ : syracuseStep 356219 = 534329) B534329
theorem B356271 : Blo 354756 356271 := bstep (se 1 (by rfl) ⟨267203, by rfl⟩ : syracuseStep 356271 = 534407) B534407
theorem B356295 : Blo 354756 356295 := bstep (se 1 (by rfl) ⟨267221, by rfl⟩ : syracuseStep 356295 = 534443) B534443
theorem B356315 : Blo 354756 356315 := bstep (se 1 (by rfl) ⟨267236, by rfl⟩ : syracuseStep 356315 = 534473) B534473
theorem B356391 : Blo 354756 356391 := bstep (se 1 (by rfl) ⟨267293, by rfl⟩ : syracuseStep 356391 = 534587) B534587
theorem B356431 : Blo 354756 356431 := bstep (se 1 (by rfl) ⟨267323, by rfl⟩ : syracuseStep 356431 = 534647) B534647
theorem B356447 : Blo 354756 356447 := bstep (se 1 (by rfl) ⟨267335, by rfl⟩ : syracuseStep 356447 = 534671) B534671
theorem B356475 : Blo 354756 356475 := bstep (se 1 (by rfl) ⟨267356, by rfl⟩ : syracuseStep 356475 = 534713) B534713
theorem B356527 : Blo 354756 356527 := bstep (se 1 (by rfl) ⟨267395, by rfl⟩ : syracuseStep 356527 = 534791) B534791
theorem B356551 : Blo 354756 356551 := bstep (se 1 (by rfl) ⟨267413, by rfl⟩ : syracuseStep 356551 = 534827) B534827
theorem B356571 : Blo 354756 356571 := bstep (se 1 (by rfl) ⟨267428, by rfl⟩ : syracuseStep 356571 = 534857) B534857
theorem B356647 : Blo 354756 356647 := bstep (se 1 (by rfl) ⟨267485, by rfl⟩ : syracuseStep 356647 = 534971) B534971
theorem B2289971 : Blo 354756 2289971 := bstep (se 1 (by rfl) ⟨1717478, by rfl⟩ : syracuseStep 2289971 = 3434957) B3434957
theorem B356687 : Blo 354756 356687 := bstep (se 1 (by rfl) ⟨267515, by rfl⟩ : syracuseStep 356687 = 535031) B535031
theorem B356703 : Blo 354756 356703 := bstep (se 1 (by rfl) ⟨267527, by rfl⟩ : syracuseStep 356703 = 535055) B535055
theorem B1208681 : Blo 354756 1208681 := bstep (se 2 (by rfl) ⟨453255, by rfl⟩ : syracuseStep 1208681 = 906511) B906511
theorem B356731 : Blo 354756 356731 := bstep (se 1 (by rfl) ⟨267548, by rfl⟩ : syracuseStep 356731 = 535097) B535097
theorem B356783 : Blo 354756 356783 := bstep (se 1 (by rfl) ⟨267587, by rfl⟩ : syracuseStep 356783 = 535175) B535175
theorem B356807 : Blo 354756 356807 := bstep (se 1 (by rfl) ⟨267605, by rfl⟩ : syracuseStep 356807 = 535211) B535211
theorem B356827 : Blo 354756 356827 := bstep (se 1 (by rfl) ⟨267620, by rfl⟩ : syracuseStep 356827 = 535241) B535241
theorem B356903 : Blo 354756 356903 := bstep (se 1 (by rfl) ⟨267677, by rfl⟩ : syracuseStep 356903 = 535355) B535355
theorem B3666491 : Blo 354756 3666491 := bstep (se 1 (by rfl) ⟨2749868, by rfl⟩ : syracuseStep 3666491 = 5499737) B5499737
theorem B356943 : Blo 354756 356943 := bstep (se 1 (by rfl) ⟨267707, by rfl⟩ : syracuseStep 356943 = 535415) B535415
theorem B356959 : Blo 354756 356959 := bstep (se 1 (by rfl) ⟨267719, by rfl⟩ : syracuseStep 356959 = 535439) B535439
theorem B356987 : Blo 354756 356987 := bstep (se 1 (by rfl) ⟨267740, by rfl⟩ : syracuseStep 356987 = 535481) B535481
theorem B357039 : Blo 354756 357039 := bstep (se 1 (by rfl) ⟨267779, by rfl⟩ : syracuseStep 357039 = 535559) B535559
theorem B357063 : Blo 354756 357063 := bstep (se 1 (by rfl) ⟨267797, by rfl⟩ : syracuseStep 357063 = 535595) B535595
theorem B357083 : Blo 354756 357083 := bstep (se 1 (by rfl) ⟨267812, by rfl⟩ : syracuseStep 357083 = 535625) B535625
theorem B357159 : Blo 354756 357159 := bstep (se 1 (by rfl) ⟨267869, by rfl⟩ : syracuseStep 357159 = 535739) B535739
theorem B357199 : Blo 354756 357199 := bstep (se 1 (by rfl) ⟨267899, by rfl⟩ : syracuseStep 357199 = 535799) B535799
theorem B357215 : Blo 354756 357215 := bstep (se 1 (by rfl) ⟨267911, by rfl⟩ : syracuseStep 357215 = 535823) B535823
theorem B357243 : Blo 354756 357243 := bstep (se 1 (by rfl) ⟨267932, by rfl⟩ : syracuseStep 357243 = 535865) B535865
theorem B357295 : Blo 354756 357295 := bstep (se 1 (by rfl) ⟨267971, by rfl⟩ : syracuseStep 357295 = 535943) B535943
theorem B1209275 : Blo 354756 1209275 := bstep (se 1 (by rfl) ⟨906956, by rfl⟩ : syracuseStep 1209275 = 1813913) B1813913
theorem B357319 : Blo 354756 357319 := bstep (se 1 (by rfl) ⟨267989, by rfl⟩ : syracuseStep 357319 = 535979) B535979
theorem B357339 : Blo 354756 357339 := bstep (se 1 (by rfl) ⟨268004, by rfl⟩ : syracuseStep 357339 = 536009) B536009
theorem B652295 : Blo 354756 652295 := bstep (se 1 (by rfl) ⟨489221, by rfl⟩ : syracuseStep 652295 = 978443) B978443
theorem B357415 : Blo 354756 357415 := bstep (se 1 (by rfl) ⟨268061, by rfl⟩ : syracuseStep 357415 = 536123) B536123
theorem B2716739 : Blo 354756 2716739 := bstep (se 1 (by rfl) ⟨2037554, by rfl⟩ : syracuseStep 2716739 = 4075109) B4075109
theorem B1537103 : Blo 354756 1537103 := bstep (se 1 (by rfl) ⟨1152827, by rfl⟩ : syracuseStep 1537103 = 2305655) B2305655
theorem B357455 : Blo 354756 357455 := bstep (se 1 (by rfl) ⟨268091, by rfl⟩ : syracuseStep 357455 = 536183) B536183
theorem B357471 : Blo 354756 357471 := bstep (se 1 (by rfl) ⟨268103, by rfl⟩ : syracuseStep 357471 = 536207) B536207
theorem B357499 : Blo 354756 357499 := bstep (se 1 (by rfl) ⟨268124, by rfl⟩ : syracuseStep 357499 = 536249) B536249
theorem B357551 : Blo 354756 357551 := bstep (se 1 (by rfl) ⟨268163, by rfl⟩ : syracuseStep 357551 = 536327) B536327
theorem B357575 : Blo 354756 357575 := bstep (se 1 (by rfl) ⟨268181, by rfl⟩ : syracuseStep 357575 = 536363) B536363
theorem B357595 : Blo 354756 357595 := bstep (se 1 (by rfl) ⟨268196, by rfl⟩ : syracuseStep 357595 = 536393) B536393
theorem B357671 : Blo 354756 357671 := bstep (se 1 (by rfl) ⟨268253, by rfl⟩ : syracuseStep 357671 = 536507) B536507
theorem B357711 : Blo 354756 357711 := bstep (se 1 (by rfl) ⟨268283, by rfl⟩ : syracuseStep 357711 = 536567) B536567
theorem B423263 : Blo 354756 423263 := bstep (se 1 (by rfl) ⟨317447, by rfl⟩ : syracuseStep 423263 = 634895) B634895
theorem B357727 : Blo 354756 357727 := bstep (se 1 (by rfl) ⟨268295, by rfl⟩ : syracuseStep 357727 = 536591) B536591
theorem B357755 : Blo 354756 357755 := bstep (se 1 (by rfl) ⟨268316, by rfl⟩ : syracuseStep 357755 = 536633) B536633
theorem B816527 : Blo 354756 816527 := bstep (se 1 (by rfl) ⟨612395, by rfl⟩ : syracuseStep 816527 = 1224791) B1224791
theorem B357807 : Blo 354756 357807 := bstep (se 1 (by rfl) ⟨268355, by rfl⟩ : syracuseStep 357807 = 536711) B536711
theorem B357831 : Blo 354756 357831 := bstep (se 1 (by rfl) ⟨268373, by rfl⟩ : syracuseStep 357831 = 536747) B536747
theorem B357851 : Blo 354756 357851 := bstep (se 1 (by rfl) ⟨268388, by rfl⟩ : syracuseStep 357851 = 536777) B536777
theorem B1144307 : Blo 354756 1144307 := bstep (se 1 (by rfl) ⟨858230, by rfl⟩ : syracuseStep 1144307 = 1716461) B1716461
theorem B1570291 : Blo 354756 1570291 := bstep (se 1 (by rfl) ⟨1177718, by rfl⟩ : syracuseStep 1570291 = 2355437) B2355437
theorem B357927 : Blo 354756 357927 := bstep (se 1 (by rfl) ⟨268445, by rfl⟩ : syracuseStep 357927 = 536891) B536891
theorem B357967 : Blo 354756 357967 := bstep (se 1 (by rfl) ⟨268475, by rfl⟩ : syracuseStep 357967 = 536951) B536951
theorem B357983 : Blo 354756 357983 := bstep (se 1 (by rfl) ⟨268487, by rfl⟩ : syracuseStep 357983 = 536975) B536975
theorem B358011 : Blo 354756 358011 := bstep (se 1 (by rfl) ⟨268508, by rfl⟩ : syracuseStep 358011 = 537017) B537017
theorem B1799819 : Blo 354756 1799819 := bstep (se 1 (by rfl) ⟨1349864, by rfl⟩ : syracuseStep 1799819 = 2699729) B2699729
theorem B358063 : Blo 354756 358063 := bstep (se 1 (by rfl) ⟨268547, by rfl⟩ : syracuseStep 358063 = 537095) B537095
theorem B1013447 : Blo 354756 1013447 := bstep (se 1 (by rfl) ⟨760085, by rfl⟩ : syracuseStep 1013447 = 1520171) B1520171
theorem B358087 : Blo 354756 358087 := bstep (se 1 (by rfl) ⟨268565, by rfl⟩ : syracuseStep 358087 = 537131) B537131
theorem B358107 : Blo 354756 358107 := bstep (se 1 (by rfl) ⟨268580, by rfl⟩ : syracuseStep 358107 = 537161) B537161
theorem B358183 : Blo 354756 358183 := bstep (se 1 (by rfl) ⟨268637, by rfl⟩ : syracuseStep 358183 = 537275) B537275
theorem B358223 : Blo 354756 358223 := bstep (se 1 (by rfl) ⟨268667, by rfl⟩ : syracuseStep 358223 = 537335) B537335
theorem B358239 : Blo 354756 358239 := bstep (se 1 (by rfl) ⟨268679, by rfl⟩ : syracuseStep 358239 = 537359) B537359
theorem B358267 : Blo 354756 358267 := bstep (se 1 (by rfl) ⟨268700, by rfl⟩ : syracuseStep 358267 = 537401) B537401
theorem B817057 : Blo 354756 817057 := bstep (se 2 (by rfl) ⟨306396, by rfl⟩ : syracuseStep 817057 = 612793) B612793
theorem B358319 : Blo 354756 358319 := bstep (se 1 (by rfl) ⟨268739, by rfl⟩ : syracuseStep 358319 = 537479) B537479
theorem B358343 : Blo 354756 358343 := bstep (se 1 (by rfl) ⟨268757, by rfl⟩ : syracuseStep 358343 = 537515) B537515
theorem B358363 : Blo 354756 358363 := bstep (se 1 (by rfl) ⟨268772, by rfl⟩ : syracuseStep 358363 = 537545) B537545
theorem B2717711 : Blo 354756 2717711 := bstep (se 1 (by rfl) ⟨2038283, by rfl⟩ : syracuseStep 2717711 = 4076567) B4076567
theorem B1079315 : Blo 354756 1079315 := bstep (se 1 (by rfl) ⟨809486, by rfl⟩ : syracuseStep 1079315 = 1618973) B1618973
theorem B358439 : Blo 354756 358439 := bstep (se 1 (by rfl) ⟨268829, by rfl⟩ : syracuseStep 358439 = 537659) B537659
theorem B358479 : Blo 354756 358479 := bstep (se 1 (by rfl) ⟨268859, by rfl⟩ : syracuseStep 358479 = 537719) B537719
theorem B358495 : Blo 354756 358495 := bstep (se 1 (by rfl) ⟨268871, by rfl⟩ : syracuseStep 358495 = 537743) B537743
theorem B358523 : Blo 354756 358523 := bstep (se 1 (by rfl) ⟨268892, by rfl⟩ : syracuseStep 358523 = 537785) B537785
theorem B358575 : Blo 354756 358575 := bstep (se 1 (by rfl) ⟨268931, by rfl⟩ : syracuseStep 358575 = 537863) B537863
theorem B358599 : Blo 354756 358599 := bstep (se 1 (by rfl) ⟨268949, by rfl⟩ : syracuseStep 358599 = 537899) B537899
theorem B686291 : Blo 354756 686291 := bstep (se 1 (by rfl) ⟨514718, by rfl⟩ : syracuseStep 686291 = 1029437) B1029437
theorem B358619 : Blo 354756 358619 := bstep (se 1 (by rfl) ⟨268964, by rfl⟩ : syracuseStep 358619 = 537929) B537929
theorem B489721 : Blo 354756 489721 := bstep (se 2 (by rfl) ⟨183645, by rfl⟩ : syracuseStep 489721 = 367291) B367291
theorem B358695 : Blo 354756 358695 := bstep (se 1 (by rfl) ⟨269021, by rfl⟩ : syracuseStep 358695 = 538043) B538043
theorem B358735 : Blo 354756 358735 := bstep (se 1 (by rfl) ⟨269051, by rfl⟩ : syracuseStep 358735 = 538103) B538103
theorem B358751 : Blo 354756 358751 := bstep (se 1 (by rfl) ⟨269063, by rfl⟩ : syracuseStep 358751 = 538127) B538127
theorem B1440125 : Blo 354756 1440125 := bstep (se 3 (by rfl) ⟨270023, by rfl⟩ : syracuseStep 1440125 = 540047) B540047
theorem B2292097 : Blo 354756 2292097 := bstep (se 2 (by rfl) ⟨859536, by rfl⟩ : syracuseStep 2292097 = 1719073) B1719073
theorem B3930605 : Blo 354756 3930605 := bstep (se 3 (by rfl) ⟨736988, by rfl⟩ : syracuseStep 3930605 = 1473977) B1473977
theorem B1440445 : Blo 354756 1440445 := bstep (se 3 (by rfl) ⟨270083, by rfl⟩ : syracuseStep 1440445 = 540167) B540167
theorem B719891 : Blo 354756 719891 := bstep (se 1 (by rfl) ⟨539918, by rfl⟩ : syracuseStep 719891 = 1079837) B1079837
theorem B1015031 : Blo 354756 1015031 := bstep (se 1 (by rfl) ⟨761273, by rfl⟩ : syracuseStep 1015031 = 1522547) B1522547
theorem B5242103 : Blo 354756 5242103 := bstep (se 1 (by rfl) ⟨3931577, by rfl⟩ : syracuseStep 5242103 = 7863155) B7863155
theorem B5471783 : Blo 354756 5471783 := bstep (se 1 (by rfl) ⟨4103837, by rfl⟩ : syracuseStep 5471783 = 8207675) B8207675
theorem B1802249 : Blo 354756 1802249 := bstep (se 2 (by rfl) ⟨675843, by rfl⟩ : syracuseStep 1802249 = 1351687) B1351687
theorem B1802411 : Blo 354756 1802411 := bstep (se 1 (by rfl) ⟨1351808, by rfl⟩ : syracuseStep 1802411 = 2703617) B2703617
theorem B852407 : Blo 354756 852407 := bstep (se 1 (by rfl) ⟨639305, by rfl⟩ : syracuseStep 852407 = 1278611) B1278611
theorem B1933787 : Blo 354756 1933787 := bstep (se 1 (by rfl) ⟨1450340, by rfl⟩ : syracuseStep 1933787 = 2900681) B2900681
theorem B1802897 : Blo 354756 1802897 := bstep (se 2 (by rfl) ⟨676086, by rfl⟩ : syracuseStep 1802897 = 1352173) B1352173
theorem B1147895 : Blo 354756 1147895 := bstep (se 1 (by rfl) ⟨860921, by rfl⟩ : syracuseStep 1147895 = 1721843) B1721843
theorem B853135 : Blo 354756 853135 := bstep (se 1 (by rfl) ⟨639851, by rfl⟩ : syracuseStep 853135 = 1279703) B1279703
theorem B427375 : Blo 354756 427375 := bstep (se 1 (by rfl) ⟨320531, by rfl⟩ : syracuseStep 427375 = 641063) B641063
theorem B722299 : Blo 354756 722299 := bstep (se 1 (by rfl) ⟨541724, by rfl⟩ : syracuseStep 722299 = 1083449) B1083449
theorem B4556411 : Blo 354756 4556411 := bstep (se 1 (by rfl) ⟨3417308, by rfl⟩ : syracuseStep 4556411 = 6834617) B6834617
theorem B821033 : Blo 354756 821033 := bstep (se 2 (by rfl) ⟨307887, by rfl⟩ : syracuseStep 821033 = 615775) B615775
theorem B2722085 : Blo 354756 2722085 := bstep (se 4 (by rfl) ⟨255195, by rfl⟩ : syracuseStep 2722085 = 510391) B510391
theorem B3541391 : Blo 354756 3541391 := bstep (se 1 (by rfl) ⟨2656043, by rfl⟩ : syracuseStep 3541391 = 5312087) B5312087
theorem B6097355 : Blo 354756 6097355 := bstep (se 1 (by rfl) ⟨4573016, by rfl⟩ : syracuseStep 6097355 = 9146033) B9146033
theorem B1706771 : Blo 354756 1706771 := bstep (se 1 (by rfl) ⟨1280078, by rfl⟩ : syracuseStep 1706771 = 2560157) B2560157
theorem B6884129 : Blo 354756 6884129 := bstep (se 2 (by rfl) ⟨2581548, by rfl⟩ : syracuseStep 6884129 = 5163097) B5163097
theorem B2198339 : Blo 354756 2198339 := bstep (se 1 (by rfl) ⟨1648754, by rfl⟩ : syracuseStep 2198339 = 3297509) B3297509
theorem B723791 : Blo 354756 723791 := bstep (se 1 (by rfl) ⟨542843, by rfl⟩ : syracuseStep 723791 = 1085687) B1085687
theorem B1936315 : Blo 354756 1936315 := bstep (se 1 (by rfl) ⟨1452236, by rfl⟩ : syracuseStep 1936315 = 2904473) B2904473
theorem B1805327 : Blo 354756 1805327 := bstep (se 1 (by rfl) ⟨1353995, by rfl⟩ : syracuseStep 1805327 = 2707991) B2707991
theorem B1445053 : Blo 354756 1445053 := bstep (se 3 (by rfl) ⟨270947, by rfl⟩ : syracuseStep 1445053 = 541895) B541895
theorem B1019233 : Blo 354756 1019233 := bstep (se 2 (by rfl) ⟨382212, by rfl⟩ : syracuseStep 1019233 = 764425) B764425
theorem B1806137 : Blo 354756 1806137 := bstep (se 2 (by rfl) ⟨677301, by rfl⟩ : syracuseStep 1806137 = 1354603) B1354603
theorem B5836859 : Blo 354756 5836859 := bstep (se 1 (by rfl) ⟨4377644, by rfl⟩ : syracuseStep 5836859 = 8755289) B8755289
theorem B15405227 : Blo 354756 15405227 := bstep (se 1 (by rfl) ⟨11553920, by rfl⟩ : syracuseStep 15405227 = 23107841) B23107841
theorem B758335 : Blo 354756 758335 := bstep (se 1 (by rfl) ⟨568751, by rfl⟩ : syracuseStep 758335 = 1137503) B1137503
theorem B1708715 : Blo 354756 1708715 := bstep (se 1 (by rfl) ⟨1281536, by rfl⟩ : syracuseStep 1708715 = 2563073) B2563073
theorem B1283035 : Blo 354756 1283035 := bstep (se 1 (by rfl) ⟨962276, by rfl⟩ : syracuseStep 1283035 = 1924553) B1924553
theorem B1020919 : Blo 354756 1020919 := bstep (se 1 (by rfl) ⟨765689, by rfl⟩ : syracuseStep 1020919 = 1531379) B1531379
theorem B857287 : Blo 354756 857287 := bstep (se 1 (by rfl) ⟨642965, by rfl⟩ : syracuseStep 857287 = 1285931) B1285931
theorem B2168257 : Blo 354756 2168257 := bstep (se 2 (by rfl) ⟨813096, by rfl⟩ : syracuseStep 2168257 = 1626193) B1626193
theorem B2561483 : Blo 354756 2561483 := bstep (se 1 (by rfl) ⟨1921112, by rfl⟩ : syracuseStep 2561483 = 3842225) B3842225
theorem B3282565 : Blo 354756 3282565 := bstep (se 4 (by rfl) ⟨307740, by rfl⟩ : syracuseStep 3282565 = 615481) B615481
theorem B11507993 : Blo 354756 11507993 := bstep (se 2 (by rfl) ⟨4315497, by rfl⟩ : syracuseStep 11507993 = 8630995) B8630995
theorem B399739 : Blo 354756 399739 := bstep (se 1 (by rfl) ⟨299804, by rfl⟩ : syracuseStep 399739 = 599609) B599609
theorem B25041287 : Blo 354756 25041287 := bstep (se 1 (by rfl) ⟨18780965, by rfl⟩ : syracuseStep 25041287 = 37561931) B37561931
theorem B1808891 : Blo 354756 1808891 := bstep (se 1 (by rfl) ⟨1356668, by rfl⟩ : syracuseStep 1808891 = 2713337) B2713337
theorem B400207 : Blo 354756 400207 := bstep (se 1 (by rfl) ⟨300155, by rfl⟩ : syracuseStep 400207 = 600311) B600311
theorem B760871 : Blo 354756 760871 := bstep (se 1 (by rfl) ⟨570653, by rfl⟩ : syracuseStep 760871 = 1141307) B1141307
theorem B3906749 : Blo 354756 3906749 := bstep (se 3 (by rfl) ⟨732515, by rfl⟩ : syracuseStep 3906749 = 1465031) B1465031
theorem B400603 : Blo 354756 400603 := bstep (se 1 (by rfl) ⟨300452, by rfl⟩ : syracuseStep 400603 = 600905) B600905
theorem B2563301 : Blo 354756 2563301 := bstep (se 4 (by rfl) ⟨240309, by rfl⟩ : syracuseStep 2563301 = 480619) B480619
theorem B400763 : Blo 354756 400763 := bstep (se 1 (by rfl) ⟨300572, by rfl⟩ : syracuseStep 400763 = 601145) B601145
theorem B1809863 : Blo 354756 1809863 := bstep (se 1 (by rfl) ⟨1357397, by rfl⟩ : syracuseStep 1809863 = 2714795) B2714795
theorem B1449431 : Blo 354756 1449431 := bstep (se 1 (by rfl) ⟨1087073, by rfl⟩ : syracuseStep 1449431 = 2174147) B2174147
theorem B400891 : Blo 354756 400891 := bstep (se 1 (by rfl) ⟨300668, by rfl⟩ : syracuseStep 400891 = 601337) B601337
theorem B2039377 : Blo 354756 2039377 := bstep (se 2 (by rfl) ⟨764766, by rfl⟩ : syracuseStep 2039377 = 1529533) B1529533
theorem B401071 : Blo 354756 401071 := bstep (se 1 (by rfl) ⟨300803, by rfl⟩ : syracuseStep 401071 = 601607) B601607
theorem B1810187 : Blo 354756 1810187 := bstep (se 1 (by rfl) ⟨1357640, by rfl⟩ : syracuseStep 1810187 = 2715281) B2715281
theorem B532265 : Blo 354756 532265 := bstep (se 2 (by rfl) ⟨199599, by rfl⟩ : syracuseStep 532265 = 399199) B399199
theorem B532271 : Blo 354756 532271 := bstep (se 1 (by rfl) ⟨399203, by rfl⟩ : syracuseStep 532271 = 798407) B798407
theorem B1089409 : Blo 354756 1089409 := bstep (se 2 (by rfl) ⟨408528, by rfl⟩ : syracuseStep 1089409 = 817057) B817057
theorem B401359 : Blo 354756 401359 := bstep (se 1 (by rfl) ⟨301019, by rfl⟩ : syracuseStep 401359 = 602039) B602039
theorem B532745 : Blo 354756 532745 := bstep (se 2 (by rfl) ⟨199779, by rfl⟩ : syracuseStep 532745 = 399559) B399559
theorem B401755 : Blo 354756 401755 := bstep (se 1 (by rfl) ⟨301316, by rfl⟩ : syracuseStep 401755 = 602633) B602633
theorem B532847 : Blo 354756 532847 := bstep (se 1 (by rfl) ⟨399635, by rfl⟩ : syracuseStep 532847 = 799271) B799271
theorem B401863 : Blo 354756 401863 := bstep (se 1 (by rfl) ⟨301397, by rfl⟩ : syracuseStep 401863 = 602795) B602795
theorem B3056129 : Blo 354756 3056129 := bstep (se 2 (by rfl) ⟨1146048, by rfl⟩ : syracuseStep 3056129 = 2292097) B2292097
theorem B533063 : Blo 354756 533063 := bstep (se 1 (by rfl) ⟨399797, by rfl⟩ : syracuseStep 533063 = 799595) B799595
theorem B533099 : Blo 354756 533099 := bstep (se 1 (by rfl) ⟨399824, by rfl⟩ : syracuseStep 533099 = 799649) B799649
theorem B5120657 : Blo 354756 5120657 := bstep (se 2 (by rfl) ⟨1920246, by rfl⟩ : syracuseStep 5120657 = 3840493) B3840493
theorem B434863 : Blo 354756 434863 := bstep (se 1 (by rfl) ⟨326147, by rfl⟩ : syracuseStep 434863 = 652295) B652295
theorem B598711 : Blo 354756 598711 := bstep (se 1 (by rfl) ⟨449033, by rfl⟩ : syracuseStep 598711 = 898067) B898067
theorem B1811159 : Blo 354756 1811159 := bstep (se 1 (by rfl) ⟨1358369, by rfl⟩ : syracuseStep 1811159 = 2716739) B2716739
theorem B1024735 : Blo 354756 1024735 := bstep (se 1 (by rfl) ⟨768551, by rfl⟩ : syracuseStep 1024735 = 1537103) B1537103
theorem B402223 : Blo 354756 402223 := bstep (se 1 (by rfl) ⟨301667, by rfl⟩ : syracuseStep 402223 = 603335) B603335
theorem B533327 : Blo 354756 533327 := bstep (se 1 (by rfl) ⟨399995, by rfl⟩ : syracuseStep 533327 = 799991) B799991
theorem B402331 : Blo 354756 402331 := bstep (se 1 (by rfl) ⟨301748, by rfl⟩ : syracuseStep 402331 = 603497) B603497
theorem B599015 : Blo 354756 599015 := bstep (se 1 (by rfl) ⟨449261, by rfl⟩ : syracuseStep 599015 = 898523) B898523
theorem B762871 : Blo 354756 762871 := bstep (se 1 (by rfl) ⟨572153, by rfl⟩ : syracuseStep 762871 = 1144307) B1144307
theorem B533723 : Blo 354756 533723 := bstep (se 1 (by rfl) ⟨400292, by rfl⟩ : syracuseStep 533723 = 800585) B800585
theorem B402727 : Blo 354756 402727 := bstep (se 1 (by rfl) ⟨302045, by rfl⟩ : syracuseStep 402727 = 604091) B604091
theorem B1811807 : Blo 354756 1811807 := bstep (se 1 (by rfl) ⟨1358855, by rfl⟩ : syracuseStep 1811807 = 2717711) B2717711
theorem B402799 : Blo 354756 402799 := bstep (se 1 (by rfl) ⟨302099, by rfl⟩ : syracuseStep 402799 = 604199) B604199
theorem B533897 : Blo 354756 533897 := bstep (se 2 (by rfl) ⟨200211, by rfl⟩ : syracuseStep 533897 = 400423) B400423
theorem B403015 : Blo 354756 403015 := bstep (se 1 (by rfl) ⟨302261, by rfl⟩ : syracuseStep 403015 = 604523) B604523
theorem B960083 : Blo 354756 960083 := bstep (se 1 (by rfl) ⟨720062, by rfl⟩ : syracuseStep 960083 = 1440125) B1440125
theorem B534251 : Blo 354756 534251 := bstep (se 1 (by rfl) ⟨400688, by rfl⟩ : syracuseStep 534251 = 801377) B801377
theorem B534479 : Blo 354756 534479 := bstep (se 1 (by rfl) ⟨400859, by rfl⟩ : syracuseStep 534479 = 801719) B801719
theorem B763913 : Blo 354756 763913 := bstep (se 2 (by rfl) ⟨286467, by rfl⟩ : syracuseStep 763913 = 572935) B572935
theorem B600169 : Blo 354756 600169 := bstep (se 2 (by rfl) ⟨225063, by rfl⟩ : syracuseStep 600169 = 450127) B450127
theorem B4073651 : Blo 354756 4073651 := bstep (se 1 (by rfl) ⟨3055238, by rfl⟩ : syracuseStep 4073651 = 6110477) B6110477
theorem B534875 : Blo 354756 534875 := bstep (se 1 (by rfl) ⟨401156, by rfl⟩ : syracuseStep 534875 = 802313) B802313
theorem B3647855 : Blo 354756 3647855 := bstep (se 1 (by rfl) ⟨2735891, by rfl⟩ : syracuseStep 3647855 = 5471783) B5471783
theorem B33499541 : Blo 354756 33499541 := bstep (se 6 (by rfl) ⟨785145, by rfl⟩ : syracuseStep 33499541 = 1570291) B1570291
theorem B535103 : Blo 354756 535103 := bstep (se 1 (by rfl) ⟨401327, by rfl⟩ : syracuseStep 535103 = 802655) B802655
theorem B928427 : Blo 354756 928427 := bstep (se 1 (by rfl) ⟨696320, by rfl⟩ : syracuseStep 928427 = 1392641) B1392641
theorem B535223 : Blo 354756 535223 := bstep (se 1 (by rfl) ⟨401417, by rfl⟩ : syracuseStep 535223 = 802835) B802835
theorem B535451 : Blo 354756 535451 := bstep (se 1 (by rfl) ⟨401588, by rfl⟩ : syracuseStep 535451 = 803177) B803177
theorem B7777361 : Blo 354756 7777361 := bstep (se 2 (by rfl) ⟨2916510, by rfl⟩ : syracuseStep 7777361 = 5833021) B5833021
theorem B3845339 : Blo 354756 3845339 := bstep (se 1 (by rfl) ⟨2884004, by rfl⟩ : syracuseStep 3845339 = 5768009) B5768009
theorem B535847 : Blo 354756 535847 := bstep (se 1 (by rfl) ⟨401885, by rfl⟩ : syracuseStep 535847 = 803771) B803771
theorem B1355075 : Blo 354756 1355075 := bstep (se 1 (by rfl) ⟨1016306, by rfl⟩ : syracuseStep 1355075 = 2032613) B2032613
theorem B535931 : Blo 354756 535931 := bstep (se 1 (by rfl) ⟨401948, by rfl⟩ : syracuseStep 535931 = 803897) B803897
theorem B961931 : Blo 354756 961931 := bstep (se 1 (by rfl) ⟨721448, by rfl⟩ : syracuseStep 961931 = 1442897) B1442897
theorem B536057 : Blo 354756 536057 := bstep (se 2 (by rfl) ⟨201021, by rfl⟩ : syracuseStep 536057 = 402043) B402043
theorem B1814075 : Blo 354756 1814075 := bstep (se 1 (by rfl) ⟨1360556, by rfl⟩ : syracuseStep 1814075 = 2721113) B2721113
theorem B536159 : Blo 354756 536159 := bstep (se 1 (by rfl) ⟨402119, by rfl⟩ : syracuseStep 536159 = 804239) B804239
theorem B798443 : Blo 354756 798443 := bstep (se 1 (by rfl) ⟨598832, by rfl⟩ : syracuseStep 798443 = 1197665) B1197665
theorem B3419921 : Blo 354756 3419921 := bstep (se 2 (by rfl) ⟨1282470, by rfl⟩ : syracuseStep 3419921 = 2564941) B2564941
theorem B601897 : Blo 354756 601897 := bstep (se 2 (by rfl) ⟨225711, by rfl⟩ : syracuseStep 601897 = 451423) B451423
theorem B1355561 : Blo 354756 1355561 := bstep (se 2 (by rfl) ⟨508335, by rfl⟩ : syracuseStep 1355561 = 1016671) B1016671
theorem B536375 : Blo 354756 536375 := bstep (se 1 (by rfl) ⟨402281, by rfl⟩ : syracuseStep 536375 = 804563) B804563
theorem B798569 : Blo 354756 798569 := bstep (se 2 (by rfl) ⟨299463, by rfl⟩ : syracuseStep 798569 = 598927) B598927
theorem B536681 : Blo 354756 536681 := bstep (se 2 (by rfl) ⟨201255, by rfl⟩ : syracuseStep 536681 = 402511) B402511
theorem B536999 : Blo 354756 536999 := bstep (se 1 (by rfl) ⟨402749, by rfl⟩ : syracuseStep 536999 = 805499) B805499
theorem B537083 : Blo 354756 537083 := bstep (se 1 (by rfl) ⟨402812, by rfl⟩ : syracuseStep 537083 = 805625) B805625
theorem B8663597 : Blo 354756 8663597 := bstep (se 3 (by rfl) ⟨1624424, by rfl⟩ : syracuseStep 8663597 = 3248849) B3248849
theorem B602687 : Blo 354756 602687 := bstep (se 1 (by rfl) ⟨452015, by rfl⟩ : syracuseStep 602687 = 904031) B904031
theorem B537209 : Blo 354756 537209 := bstep (se 2 (by rfl) ⟨201453, by rfl⟩ : syracuseStep 537209 = 402907) B402907
theorem B537263 : Blo 354756 537263 := bstep (se 1 (by rfl) ⟨402947, by rfl⟩ : syracuseStep 537263 = 805895) B805895
theorem B799415 : Blo 354756 799415 := bstep (se 1 (by rfl) ⟨599561, by rfl⟩ : syracuseStep 799415 = 1199123) B1199123
theorem B537311 : Blo 354756 537311 := bstep (se 1 (by rfl) ⟨402983, by rfl⟩ : syracuseStep 537311 = 805967) B805967
theorem B799631 : Blo 354756 799631 := bstep (se 1 (by rfl) ⟨599723, by rfl⟩ : syracuseStep 799631 = 1199447) B1199447
theorem B8205257 : Blo 354756 8205257 := bstep (se 2 (by rfl) ⟨3076971, by rfl⟩ : syracuseStep 8205257 = 6153943) B6153943
theorem B537575 : Blo 354756 537575 := bstep (se 1 (by rfl) ⟨403181, by rfl⟩ : syracuseStep 537575 = 806363) B806363
theorem B570359 : Blo 354756 570359 := bstep (se 1 (by rfl) ⟨427769, by rfl⟩ : syracuseStep 570359 = 855539) B855539
theorem B898087 : Blo 354756 898087 := bstep (se 1 (by rfl) ⟨673565, by rfl⟩ : syracuseStep 898087 = 1347131) B1347131
theorem B1619041 : Blo 354756 1619041 := bstep (se 2 (by rfl) ⟨607140, by rfl⟩ : syracuseStep 1619041 = 1214281) B1214281
theorem B1815695 : Blo 354756 1815695 := bstep (se 1 (by rfl) ⟨1361771, by rfl⟩ : syracuseStep 1815695 = 2723543) B2723543
theorem B1520855 : Blo 354756 1520855 := bstep (se 1 (by rfl) ⟨1140641, by rfl⟩ : syracuseStep 1520855 = 2281283) B2281283
theorem B603355 : Blo 354756 603355 := bstep (se 1 (by rfl) ⟨452516, by rfl⟩ : syracuseStep 603355 = 905033) B905033
theorem B1357033 : Blo 354756 1357033 := bstep (se 2 (by rfl) ⟨508887, by rfl⟩ : syracuseStep 1357033 = 1017775) B1017775
theorem B537833 : Blo 354756 537833 := bstep (se 2 (by rfl) ⟨201687, by rfl⟩ : syracuseStep 537833 = 403375) B403375
theorem B537887 : Blo 354756 537887 := bstep (se 1 (by rfl) ⟨403415, by rfl⟩ : syracuseStep 537887 = 806831) B806831
theorem B538055 : Blo 354756 538055 := bstep (se 1 (by rfl) ⟨403541, by rfl⟩ : syracuseStep 538055 = 807083) B807083
theorem B898553 : Blo 354756 898553 := bstep (se 2 (by rfl) ⟨336957, by rfl⟩ : syracuseStep 898553 = 673915) B673915
theorem B800351 : Blo 354756 800351 := bstep (se 1 (by rfl) ⟨600263, by rfl⟩ : syracuseStep 800351 = 1200527) B1200527
theorem B407215 : Blo 354756 407215 := bstep (se 1 (by rfl) ⟨305411, by rfl⟩ : syracuseStep 407215 = 610823) B610823
theorem B571115 : Blo 354756 571115 := bstep (se 1 (by rfl) ⟨428336, by rfl⟩ : syracuseStep 571115 = 856673) B856673
theorem B800567 : Blo 354756 800567 := bstep (se 1 (by rfl) ⟨600425, by rfl⟩ : syracuseStep 800567 = 1200851) B1200851
theorem B604111 : Blo 354756 604111 := bstep (se 1 (by rfl) ⟨453083, by rfl⟩ : syracuseStep 604111 = 906167) B906167
theorem B800873 : Blo 354756 800873 := bstep (se 2 (by rfl) ⟨300327, by rfl⟩ : syracuseStep 800873 = 600655) B600655
theorem B899201 : Blo 354756 899201 := bstep (se 2 (by rfl) ⟨337200, by rfl⟩ : syracuseStep 899201 = 674401) B674401
theorem B1128701 : Blo 354756 1128701 := bstep (se 3 (by rfl) ⟨211631, by rfl⟩ : syracuseStep 1128701 = 423263) B423263
theorem B2177405 : Blo 354756 2177405 := bstep (se 3 (by rfl) ⟨408263, by rfl⟩ : syracuseStep 2177405 = 816527) B816527
theorem B899495 : Blo 354756 899495 := bstep (se 1 (by rfl) ⟨674621, by rfl⟩ : syracuseStep 899495 = 1349243) B1349243
theorem B1030583 : Blo 354756 1030583 := bstep (se 1 (by rfl) ⟨772937, by rfl⟩ : syracuseStep 1030583 = 1545875) B1545875
theorem B2177599 : Blo 354756 2177599 := bstep (se 1 (by rfl) ⟨1633199, by rfl⟩ : syracuseStep 2177599 = 3266399) B3266399
theorem B899657 : Blo 354756 899657 := bstep (se 2 (by rfl) ⟨337371, by rfl⟩ : syracuseStep 899657 = 674743) B674743
theorem B801359 : Blo 354756 801359 := bstep (se 1 (by rfl) ⟨601019, by rfl⟩ : syracuseStep 801359 = 1202039) B1202039
theorem B604793 : Blo 354756 604793 := bstep (se 2 (by rfl) ⟨226797, by rfl⟩ : syracuseStep 604793 = 453595) B453595
theorem B604847 : Blo 354756 604847 := bstep (se 1 (by rfl) ⟨453635, by rfl⟩ : syracuseStep 604847 = 907271) B907271
theorem B801503 : Blo 354756 801503 := bstep (se 1 (by rfl) ⟨601127, by rfl⟩ : syracuseStep 801503 = 1202255) B1202255
theorem B605083 : Blo 354756 605083 := bstep (se 1 (by rfl) ⟨453812, by rfl⟩ : syracuseStep 605083 = 907625) B907625
theorem B900011 : Blo 354756 900011 := bstep (se 1 (by rfl) ⟨675008, by rfl⟩ : syracuseStep 900011 = 1350017) B1350017
theorem B801755 : Blo 354756 801755 := bstep (se 1 (by rfl) ⟨601316, by rfl⟩ : syracuseStep 801755 = 1202633) B1202633
theorem B900193 : Blo 354756 900193 := bstep (se 2 (by rfl) ⟨337572, by rfl⟩ : syracuseStep 900193 = 675145) B675145
theorem B801935 : Blo 354756 801935 := bstep (se 1 (by rfl) ⟨601451, by rfl⟩ : syracuseStep 801935 = 1202903) B1202903
theorem B802025 : Blo 354756 802025 := bstep (se 2 (by rfl) ⟨300759, by rfl⟩ : syracuseStep 802025 = 601519) B601519
theorem B802079 : Blo 354756 802079 := bstep (se 1 (by rfl) ⟨601559, by rfl⟩ : syracuseStep 802079 = 1203119) B1203119
theorem B507259 : Blo 354756 507259 := bstep (se 1 (by rfl) ⟨380444, by rfl⟩ : syracuseStep 507259 = 760889) B760889
theorem B5127695 : Blo 354756 5127695 := bstep (se 1 (by rfl) ⟨3845771, by rfl⟩ : syracuseStep 5127695 = 7691543) B7691543
theorem B507487 : Blo 354756 507487 := bstep (se 1 (by rfl) ⟨380615, by rfl⟩ : syracuseStep 507487 = 761231) B761231
theorem B802601 : Blo 354756 802601 := bstep (se 2 (by rfl) ⟨300975, by rfl⟩ : syracuseStep 802601 = 601951) B601951
theorem B507703 : Blo 354756 507703 := bstep (se 1 (by rfl) ⟨380777, by rfl⟩ : syracuseStep 507703 = 761555) B761555
theorem B638777 : Blo 354756 638777 := bstep (se 2 (by rfl) ⟨239541, by rfl⟩ : syracuseStep 638777 = 479083) B479083
theorem B3260267 : Blo 354756 3260267 := bstep (se 1 (by rfl) ⟨2445200, by rfl⟩ : syracuseStep 3260267 = 4890401) B4890401
theorem B901145 : Blo 354756 901145 := bstep (se 2 (by rfl) ⟨337929, by rfl⟩ : syracuseStep 901145 = 675859) B675859
theorem B3948851 : Blo 354756 3948851 := bstep (se 1 (by rfl) ⟨2961638, by rfl⟩ : syracuseStep 3948851 = 5923277) B5923277
theorem B541019 : Blo 354756 541019 := bstep (se 1 (by rfl) ⟨405764, by rfl⟩ : syracuseStep 541019 = 811529) B811529
theorem B3064229 : Blo 354756 3064229 := bstep (se 4 (by rfl) ⟨287271, by rfl⟩ : syracuseStep 3064229 = 574543) B574543
theorem B901601 : Blo 354756 901601 := bstep (se 2 (by rfl) ⟨338100, by rfl⟩ : syracuseStep 901601 = 676201) B676201
theorem B901651 : Blo 354756 901651 := bstep (se 1 (by rfl) ⟨676238, by rfl⟩ : syracuseStep 901651 = 1352477) B1352477
theorem B508523 : Blo 354756 508523 := bstep (se 1 (by rfl) ⟨381392, by rfl⟩ : syracuseStep 508523 = 762785) B762785
theorem B639823 : Blo 354756 639823 := bstep (se 1 (by rfl) ⟨479867, by rfl⟩ : syracuseStep 639823 = 959735) B959735
theorem B803663 : Blo 354756 803663 := bstep (se 1 (by rfl) ⟨602747, by rfl⟩ : syracuseStep 803663 = 1205495) B1205495
theorem B803879 : Blo 354756 803879 := bstep (se 1 (by rfl) ⟨602909, by rfl⟩ : syracuseStep 803879 = 1205819) B1205819
theorem B7324769 : Blo 354756 7324769 := bstep (se 2 (by rfl) ⟨2746788, by rfl⟩ : syracuseStep 7324769 = 5493577) B5493577
theorem B804059 : Blo 354756 804059 := bstep (se 1 (by rfl) ⟨603044, by rfl⟩ : syracuseStep 804059 = 1206089) B1206089
theorem B509161 : Blo 354756 509161 := bstep (se 2 (by rfl) ⟨190935, by rfl⟩ : syracuseStep 509161 = 381871) B381871
theorem B1361195 : Blo 354756 1361195 := bstep (se 1 (by rfl) ⟨1020896, by rfl⟩ : syracuseStep 1361195 = 2041793) B2041793
theorem B804257 : Blo 354756 804257 := bstep (se 2 (by rfl) ⟨301596, by rfl⟩ : syracuseStep 804257 = 603193) B603193
theorem B1525229 : Blo 354756 1525229 := bstep (se 3 (by rfl) ⟨285980, by rfl⟩ : syracuseStep 1525229 = 571961) B571961
theorem B640595 : Blo 354756 640595 := bstep (se 1 (by rfl) ⟨480446, by rfl⟩ : syracuseStep 640595 = 960893) B960893
theorem B804815 : Blo 354756 804815 := bstep (se 1 (by rfl) ⟨603611, by rfl⟩ : syracuseStep 804815 = 1207223) B1207223
theorem B7358521 : Blo 354756 7358521 := bstep (se 2 (by rfl) ⟨2759445, by rfl⟩ : syracuseStep 7358521 = 5518891) B5518891
theorem B903433 : Blo 354756 903433 := bstep (se 2 (by rfl) ⟨338787, by rfl⟩ : syracuseStep 903433 = 677575) B677575
theorem B805193 : Blo 354756 805193 := bstep (se 2 (by rfl) ⟨301947, by rfl⟩ : syracuseStep 805193 = 603895) B603895
theorem B805211 : Blo 354756 805211 := bstep (se 1 (by rfl) ⟨603908, by rfl⟩ : syracuseStep 805211 = 1207817) B1207817
theorem B969337 : Blo 354756 969337 := bstep (se 2 (by rfl) ⟨363501, by rfl⟩ : syracuseStep 969337 = 727003) B727003
theorem B1526647 : Blo 354756 1526647 := bstep (se 1 (by rfl) ⟨1144985, by rfl⟩ : syracuseStep 1526647 = 2289971) B2289971
theorem B805787 : Blo 354756 805787 := bstep (se 1 (by rfl) ⟨604340, by rfl⟩ : syracuseStep 805787 = 1208681) B1208681
theorem B2444327 : Blo 354756 2444327 := bstep (se 1 (by rfl) ⟨1833245, by rfl⟩ : syracuseStep 2444327 = 3666491) B3666491
theorem B805985 : Blo 354756 805985 := bstep (se 2 (by rfl) ⟨302244, by rfl⟩ : syracuseStep 805985 = 604489) B604489
theorem B806183 : Blo 354756 806183 := bstep (se 1 (by rfl) ⟨604637, by rfl⟩ : syracuseStep 806183 = 1209275) B1209275
theorem B1199609 : Blo 354756 1199609 := bstep (se 2 (by rfl) ⟨449853, by rfl⟩ : syracuseStep 1199609 = 899707) B899707
theorem B1920593 : Blo 354756 1920593 := bstep (se 2 (by rfl) ⟨720222, by rfl⟩ : syracuseStep 1920593 = 1440445) B1440445
theorem B806561 : Blo 354756 806561 := bstep (se 2 (by rfl) ⟨302460, by rfl⟩ : syracuseStep 806561 = 604921) B604921
theorem B904891 : Blo 354756 904891 := bstep (se 1 (by rfl) ⟨678668, by rfl⟩ : syracuseStep 904891 = 1357337) B1357337
theorem B1199879 : Blo 354756 1199879 := bstep (se 1 (by rfl) ⟨899909, by rfl⟩ : syracuseStep 1199879 = 1799819) B1799819
theorem B675631 : Blo 354756 675631 := bstep (se 1 (by rfl) ⟨506723, by rfl⟩ : syracuseStep 675631 = 1013447) B1013447
theorem B1199933 : Blo 354756 1199933 := bstep (se 3 (by rfl) ⟨224987, by rfl⟩ : syracuseStep 1199933 = 449975) B449975
theorem B806921 : Blo 354756 806921 := bstep (se 2 (by rfl) ⟨302595, by rfl⟩ : syracuseStep 806921 = 605191) B605191
theorem B479927 : Blo 354756 479927 := bstep (se 1 (by rfl) ⟨359945, by rfl⟩ : syracuseStep 479927 = 719891) B719891
theorem B905975 : Blo 354756 905975 := bstep (se 1 (by rfl) ⟨679481, by rfl⟩ : syracuseStep 905975 = 1358963) B1358963
theorem B1626923 : Blo 354756 1626923 := bstep (se 1 (by rfl) ⟨1220192, by rfl⟩ : syracuseStep 1626923 = 2440385) B2440385
theorem B676687 : Blo 354756 676687 := bstep (se 1 (by rfl) ⟨507515, by rfl⟩ : syracuseStep 676687 = 1015031) B1015031
theorem B3494735 : Blo 354756 3494735 := bstep (se 1 (by rfl) ⟨2621051, by rfl⟩ : syracuseStep 3494735 = 5242103) B5242103
theorem B51958745 : Blo 354756 51958745 := bstep (se 2 (by rfl) ⟨19484529, by rfl⟩ : syracuseStep 51958745 = 38969059) B38969059
theorem B5297125 : Blo 354756 5297125 := bstep (se 4 (by rfl) ⟨496605, by rfl⟩ : syracuseStep 5297125 = 993211) B993211
theorem B30823577 : Blo 354756 30823577 := bstep (se 2 (by rfl) ⟨11558841, by rfl⟩ : syracuseStep 30823577 = 23117683) B23117683
theorem B7722503 : Blo 354756 7722503 := bstep (se 1 (by rfl) ⟨5791877, by rfl⟩ : syracuseStep 7722503 = 11583755) B11583755
theorem B906835 : Blo 354756 906835 := bstep (se 1 (by rfl) ⟨680126, by rfl⟩ : syracuseStep 906835 = 1360253) B1360253
theorem B480863 : Blo 354756 480863 := bstep (se 1 (by rfl) ⟨360647, by rfl⟩ : syracuseStep 480863 = 721295) B721295
theorem B481079 : Blo 354756 481079 := bstep (se 1 (by rfl) ⟨360809, by rfl⟩ : syracuseStep 481079 = 721619) B721619
theorem B1529705 : Blo 354756 1529705 := bstep (se 2 (by rfl) ⟨573639, by rfl⟩ : syracuseStep 1529705 = 1147279) B1147279
theorem B809441 : Blo 354756 809441 := bstep (se 2 (by rfl) ⟨303540, by rfl⟩ : syracuseStep 809441 = 607081) B607081
theorem B678395 : Blo 354756 678395 := bstep (se 1 (by rfl) ⟨508796, by rfl⟩ : syracuseStep 678395 = 1017593) B1017593
theorem B1202795 : Blo 354756 1202795 := bstep (se 1 (by rfl) ⟨902096, by rfl⟩ : syracuseStep 1202795 = 1804193) B1804193
theorem B2284307 : Blo 354756 2284307 := bstep (se 1 (by rfl) ⟨1713230, by rfl⟩ : syracuseStep 2284307 = 3426461) B3426461
theorem B645907 : Blo 354756 645907 := bstep (se 1 (by rfl) ⟨484430, by rfl⟩ : syracuseStep 645907 = 968861) B968861
theorem B449327 : Blo 354756 449327 := bstep (se 1 (by rfl) ⟨336995, by rfl⟩ : syracuseStep 449327 = 673991) B673991
theorem B482279 : Blo 354756 482279 := bstep (se 1 (by rfl) ⟨361709, by rfl⟩ : syracuseStep 482279 = 723419) B723419
theorem B1203389 : Blo 354756 1203389 := bstep (se 3 (by rfl) ⟨225635, by rfl⟩ : syracuseStep 1203389 = 451271) B451271
theorem B2317501 : Blo 354756 2317501 := bstep (se 3 (by rfl) ⟨434531, by rfl⟩ : syracuseStep 2317501 = 869063) B869063
theorem B679367 : Blo 354756 679367 := bstep (se 1 (by rfl) ⟨509525, by rfl⟩ : syracuseStep 679367 = 1019051) B1019051
theorem B679519 : Blo 354756 679519 := bstep (se 1 (by rfl) ⟨509639, by rfl⟩ : syracuseStep 679519 = 1019279) B1019279
theorem B1532267 : Blo 354756 1532267 := bstep (se 1 (by rfl) ⟨1149200, by rfl⟩ : syracuseStep 1532267 = 2298401) B2298401
theorem B1631195 : Blo 354756 1631195 := bstep (se 1 (by rfl) ⟨1223396, by rfl⟩ : syracuseStep 1631195 = 2446793) B2446793
theorem B1631431 : Blo 354756 1631431 := bstep (se 1 (by rfl) ⟨1223573, by rfl⟩ : syracuseStep 1631431 = 2447147) B2447147
theorem B5793569 : Blo 354756 5793569 := bstep (se 2 (by rfl) ⟨2172588, by rfl⟩ : syracuseStep 5793569 = 4345177) B4345177
theorem B5891945 : Blo 354756 5891945 := bstep (se 2 (by rfl) ⟨2209479, by rfl⟩ : syracuseStep 5891945 = 4418959) B4418959
theorem B1206305 : Blo 354756 1206305 := bstep (se 2 (by rfl) ⟨452364, by rfl⟩ : syracuseStep 1206305 = 904729) B904729
theorem B3860561 : Blo 354756 3860561 := bstep (se 2 (by rfl) ⟨1447710, by rfl⟩ : syracuseStep 3860561 = 2895421) B2895421
theorem B4581629 : Blo 354756 4581629 := bstep (se 3 (by rfl) ⟨859055, by rfl⟩ : syracuseStep 4581629 = 1718111) B1718111
theorem B354811 : Blo 354756 354811 := bstep (se 1 (by rfl) ⟨266108, by rfl⟩ : syracuseStep 354811 = 532217) B532217
theorem B354879 : Blo 354756 354879 := bstep (se 1 (by rfl) ⟨266159, by rfl⟩ : syracuseStep 354879 = 532319) B532319
theorem B354887 : Blo 354756 354887 := bstep (se 1 (by rfl) ⟨266165, by rfl⟩ : syracuseStep 354887 = 532331) B532331
theorem B453215 : Blo 354756 453215 := bstep (se 1 (by rfl) ⟨339911, by rfl⟩ : syracuseStep 453215 = 679823) B679823
theorem B3041981 : Blo 354756 3041981 := bstep (se 3 (by rfl) ⟨570371, by rfl⟩ : syracuseStep 3041981 = 1140743) B1140743
theorem B355039 : Blo 354756 355039 := bstep (se 1 (by rfl) ⟨266279, by rfl⟩ : syracuseStep 355039 = 532559) B532559
theorem B355119 : Blo 354756 355119 := bstep (se 1 (by rfl) ⟨266339, by rfl⟩ : syracuseStep 355119 = 532679) B532679
theorem B355227 : Blo 354756 355227 := bstep (se 1 (by rfl) ⟨266420, by rfl⟩ : syracuseStep 355227 = 532841) B532841
theorem B1928123 : Blo 354756 1928123 := bstep (se 1 (by rfl) ⟨1446092, by rfl⟩ : syracuseStep 1928123 = 2892185) B2892185
theorem B355279 : Blo 354756 355279 := bstep (se 1 (by rfl) ⟨266459, by rfl⟩ : syracuseStep 355279 = 532919) B532919
theorem B355303 : Blo 354756 355303 := bstep (se 1 (by rfl) ⟨266477, by rfl⟩ : syracuseStep 355303 = 532955) B532955
theorem B1830109 : Blo 354756 1830109 := bstep (se 3 (by rfl) ⟨343145, by rfl⟩ : syracuseStep 1830109 = 686291) B686291
theorem B355615 : Blo 354756 355615 := bstep (se 1 (by rfl) ⟨266711, by rfl⟩ : syracuseStep 355615 = 533423) B533423
theorem B453919 : Blo 354756 453919 := bstep (se 1 (by rfl) ⟨340439, by rfl⟩ : syracuseStep 453919 = 680879) B680879
theorem B355675 : Blo 354756 355675 := bstep (se 1 (by rfl) ⟨266756, by rfl⟩ : syracuseStep 355675 = 533513) B533513
theorem B486767 : Blo 354756 486767 := bstep (se 1 (by rfl) ⟨365075, by rfl⟩ : syracuseStep 486767 = 730151) B730151
theorem B355695 : Blo 354756 355695 := bstep (se 1 (by rfl) ⟨266771, by rfl⟩ : syracuseStep 355695 = 533543) B533543
theorem B355751 : Blo 354756 355751 := bstep (se 1 (by rfl) ⟨266813, by rfl⟩ : syracuseStep 355751 = 533627) B533627
theorem B355835 : Blo 354756 355835 := bstep (se 1 (by rfl) ⟨266876, by rfl⟩ : syracuseStep 355835 = 533753) B533753
theorem B355903 : Blo 354756 355903 := bstep (se 1 (by rfl) ⟨266927, by rfl⟩ : syracuseStep 355903 = 533855) B533855
theorem B355911 : Blo 354756 355911 := bstep (se 1 (by rfl) ⟨266933, by rfl⟩ : syracuseStep 355911 = 533867) B533867
theorem B1797713 : Blo 354756 1797713 := bstep (se 2 (by rfl) ⟨674142, by rfl⟩ : syracuseStep 1797713 = 1348285) B1348285
theorem B356063 : Blo 354756 356063 := bstep (se 1 (by rfl) ⟨267047, by rfl⟩ : syracuseStep 356063 = 534095) B534095
theorem B356143 : Blo 354756 356143 := bstep (se 1 (by rfl) ⟨267107, by rfl⟩ : syracuseStep 356143 = 534215) B534215
theorem B356251 : Blo 354756 356251 := bstep (se 1 (by rfl) ⟨267188, by rfl⟩ : syracuseStep 356251 = 534377) B534377
theorem B3239837 : Blo 354756 3239837 := bstep (se 3 (by rfl) ⟨607469, by rfl⟩ : syracuseStep 3239837 = 1214939) B1214939
theorem B356303 : Blo 354756 356303 := bstep (se 1 (by rfl) ⟨267227, by rfl⟩ : syracuseStep 356303 = 534455) B534455
theorem B356327 : Blo 354756 356327 := bstep (se 1 (by rfl) ⟨267245, by rfl⟩ : syracuseStep 356327 = 534491) B534491
theorem B1929419 : Blo 354756 1929419 := bstep (se 1 (by rfl) ⟨1447064, by rfl⟩ : syracuseStep 1929419 = 2894129) B2894129
theorem B356639 : Blo 354756 356639 := bstep (se 1 (by rfl) ⟨267479, by rfl⟩ : syracuseStep 356639 = 534959) B534959
theorem B356699 : Blo 354756 356699 := bstep (se 1 (by rfl) ⟨267524, by rfl⟩ : syracuseStep 356699 = 535049) B535049
theorem B356719 : Blo 354756 356719 := bstep (se 1 (by rfl) ⟨267539, by rfl⟩ : syracuseStep 356719 = 535079) B535079
theorem B356775 : Blo 354756 356775 := bstep (se 1 (by rfl) ⟨267581, by rfl⟩ : syracuseStep 356775 = 535163) B535163
theorem B356859 : Blo 354756 356859 := bstep (se 1 (by rfl) ⟨267644, by rfl⟩ : syracuseStep 356859 = 535289) B535289
theorem B356927 : Blo 354756 356927 := bstep (se 1 (by rfl) ⟨267695, by rfl⟩ : syracuseStep 356927 = 535391) B535391
theorem B356935 : Blo 354756 356935 := bstep (se 1 (by rfl) ⟨267701, by rfl⟩ : syracuseStep 356935 = 535403) B535403
theorem B357087 : Blo 354756 357087 := bstep (se 1 (by rfl) ⟨267815, by rfl⟩ : syracuseStep 357087 = 535631) B535631
theorem B357167 : Blo 354756 357167 := bstep (se 1 (by rfl) ⟨267875, by rfl⟩ : syracuseStep 357167 = 535751) B535751
theorem B1209167 : Blo 354756 1209167 := bstep (se 1 (by rfl) ⟨906875, by rfl⟩ : syracuseStep 1209167 = 1813751) B1813751
theorem B357275 : Blo 354756 357275 := bstep (se 1 (by rfl) ⟨267956, by rfl⟩ : syracuseStep 357275 = 535913) B535913
theorem B357327 : Blo 354756 357327 := bstep (se 1 (by rfl) ⟨267995, by rfl⟩ : syracuseStep 357327 = 535991) B535991
theorem B357351 : Blo 354756 357351 := bstep (se 1 (by rfl) ⟨268013, by rfl⟩ : syracuseStep 357351 = 536027) B536027
theorem B1209491 : Blo 354756 1209491 := bstep (se 1 (by rfl) ⟨907118, by rfl⟩ : syracuseStep 1209491 = 1814237) B1814237
theorem B1864919 : Blo 354756 1864919 := bstep (se 1 (by rfl) ⟨1398689, by rfl⟩ : syracuseStep 1864919 = 2797379) B2797379
theorem B357663 : Blo 354756 357663 := bstep (se 1 (by rfl) ⟨268247, by rfl⟩ : syracuseStep 357663 = 536495) B536495
theorem B357723 : Blo 354756 357723 := bstep (se 1 (by rfl) ⟨268292, by rfl⟩ : syracuseStep 357723 = 536585) B536585
theorem B357743 : Blo 354756 357743 := bstep (se 1 (by rfl) ⟨268307, by rfl⟩ : syracuseStep 357743 = 536615) B536615
theorem B1209761 : Blo 354756 1209761 := bstep (se 2 (by rfl) ⟨453660, by rfl⟩ : syracuseStep 1209761 = 907321) B907321
theorem B357799 : Blo 354756 357799 := bstep (se 1 (by rfl) ⟨268349, by rfl⟩ : syracuseStep 357799 = 536699) B536699
theorem B357883 : Blo 354756 357883 := bstep (se 1 (by rfl) ⟨268412, by rfl⟩ : syracuseStep 357883 = 536825) B536825
theorem B357951 : Blo 354756 357951 := bstep (se 1 (by rfl) ⟨268463, by rfl⟩ : syracuseStep 357951 = 536927) B536927
theorem B357959 : Blo 354756 357959 := bstep (se 1 (by rfl) ⟨268469, by rfl⟩ : syracuseStep 357959 = 536939) B536939
theorem B489067 : Blo 354756 489067 := bstep (se 1 (by rfl) ⟨366800, by rfl⟩ : syracuseStep 489067 = 733601) B733601
theorem B652961 : Blo 354756 652961 := bstep (se 2 (by rfl) ⟨244860, by rfl⟩ : syracuseStep 652961 = 489721) B489721
theorem B358111 : Blo 354756 358111 := bstep (se 1 (by rfl) ⟨268583, by rfl⟩ : syracuseStep 358111 = 537167) B537167
theorem B358191 : Blo 354756 358191 := bstep (se 1 (by rfl) ⟨268643, by rfl⟩ : syracuseStep 358191 = 537287) B537287
theorem B358299 : Blo 354756 358299 := bstep (se 1 (by rfl) ⟨268724, by rfl⟩ : syracuseStep 358299 = 537449) B537449
theorem B1800143 : Blo 354756 1800143 := bstep (se 1 (by rfl) ⟨1350107, by rfl⟩ : syracuseStep 1800143 = 2700215) B2700215
theorem B358351 : Blo 354756 358351 := bstep (se 1 (by rfl) ⟨268763, by rfl⟩ : syracuseStep 358351 = 537527) B537527
theorem B358375 : Blo 354756 358375 := bstep (se 1 (by rfl) ⟨268781, by rfl⟩ : syracuseStep 358375 = 537563) B537563
theorem B358687 : Blo 354756 358687 := bstep (se 1 (by rfl) ⟨269015, by rfl⟩ : syracuseStep 358687 = 538031) B538031
theorem B358747 : Blo 354756 358747 := bstep (se 1 (by rfl) ⟨269060, by rfl⟩ : syracuseStep 358747 = 538121) B538121
theorem B719543 : Blo 354756 719543 := bstep (se 1 (by rfl) ⟨539657, by rfl⟩ : syracuseStep 719543 = 1079315) B1079315
theorem B490207 : Blo 354756 490207 := bstep (se 1 (by rfl) ⟨367655, by rfl⟩ : syracuseStep 490207 = 735311) B735311
theorem B1801115 : Blo 354756 1801115 := bstep (se 1 (by rfl) ⟨1350836, by rfl⟩ : syracuseStep 1801115 = 2701673) B2701673
theorem B2620403 : Blo 354756 2620403 := bstep (se 1 (by rfl) ⟨1965302, by rfl⟩ : syracuseStep 2620403 = 3930605) B3930605
theorem B55639385 : Blo 354756 55639385 := bstep (se 2 (by rfl) ⟨20864769, by rfl⟩ : syracuseStep 55639385 = 41729539) B41729539
theorem B1801601 : Blo 354756 1801601 := bstep (se 2 (by rfl) ⟨675600, by rfl⟩ : syracuseStep 1801601 = 1351201) B1351201
theorem B1146383 : Blo 354756 1146383 := bstep (se 1 (by rfl) ⟨859787, by rfl⟩ : syracuseStep 1146383 = 1719575) B1719575
theorem B7700359 : Blo 354756 7700359 := bstep (se 1 (by rfl) ⟨5775269, by rfl⟩ : syracuseStep 7700359 = 11550539) B11550539
theorem B360347 : Blo 354756 360347 := bstep (se 1 (by rfl) ⟨270260, by rfl⟩ : syracuseStep 360347 = 540521) B540521
theorem B4883179 : Blo 354756 4883179 := bstep (se 1 (by rfl) ⟨3662384, by rfl⟩ : syracuseStep 4883179 = 7324769) B7324769
theorem B1442717 : Blo 354756 1442717 := bstep (se 3 (by rfl) ⟨270509, by rfl⟩ : syracuseStep 1442717 = 541019) B541019
theorem B1016819 : Blo 354756 1016819 := bstep (se 1 (by rfl) ⟨762614, by rfl⟩ : syracuseStep 1016819 = 1525229) B1525229
theorem B853097 : Blo 354756 853097 := bstep (se 2 (by rfl) ⟨319911, by rfl⟩ : syracuseStep 853097 = 639823) B639823
theorem B1017161 : Blo 354756 1017161 := bstep (se 2 (by rfl) ⟨381435, by rfl⟩ : syracuseStep 1017161 = 762871) B762871
theorem B2360927 : Blo 354756 2360927 := bstep (se 1 (by rfl) ⟨1770695, by rfl⟩ : syracuseStep 2360927 = 3541391) B3541391
theorem B4064903 : Blo 354756 4064903 := bstep (se 1 (by rfl) ⟨3048677, by rfl⟩ : syracuseStep 4064903 = 6097355) B6097355
theorem B1279805 : Blo 354756 1279805 := bstep (se 3 (by rfl) ⟨239963, by rfl⟩ : syracuseStep 1279805 = 479927) B479927
theorem B4589419 : Blo 354756 4589419 := bstep (se 1 (by rfl) ⟨3442064, by rfl⟩ : syracuseStep 4589419 = 6884129) B6884129
theorem B1280395 : Blo 354756 1280395 := bstep (se 1 (by rfl) ⟨960296, by rfl⟩ : syracuseStep 1280395 = 1920593) B1920593
theorem B2329823 : Blo 354756 2329823 := bstep (se 1 (by rfl) ⟨1747367, by rfl⟩ : syracuseStep 2329823 = 3494735) B3494735
theorem B34639163 : Blo 354756 34639163 := bstep (se 1 (by rfl) ⟨25979372, by rfl⟩ : syracuseStep 34639163 = 51958745) B51958745
theorem B20549051 : Blo 354756 20549051 := bstep (se 1 (by rfl) ⟨15411788, by rfl⟩ : syracuseStep 20549051 = 30823577) B30823577
theorem B1707655 : Blo 354756 1707655 := bstep (se 1 (by rfl) ⟨1280741, by rfl⟩ : syracuseStep 1707655 = 2561483) B2561483
theorem B5148335 : Blo 354756 5148335 := bstep (se 1 (by rfl) ⟨3861251, by rfl⟩ : syracuseStep 5148335 = 7722503) B7722503
theorem B2035529 : Blo 354756 2035529 := bstep (se 2 (by rfl) ⟨763323, by rfl⟩ : syracuseStep 2035529 = 1526647) B1526647
theorem B1019803 : Blo 354756 1019803 := bstep (se 1 (by rfl) ⟨764852, by rfl⟩ : syracuseStep 1019803 = 1529705) B1529705
theorem B7671995 : Blo 354756 7671995 := bstep (se 1 (by rfl) ⟨5753996, by rfl⟩ : syracuseStep 7671995 = 11507993) B11507993
theorem B1708253 : Blo 354756 1708253 := bstep (se 3 (by rfl) ⟨320297, by rfl⟩ : syracuseStep 1708253 = 640595) B640595
theorem B1282301 : Blo 354756 1282301 := bstep (se 3 (by rfl) ⟨240431, by rfl⟩ : syracuseStep 1282301 = 480863) B480863
theorem B1282877 : Blo 354756 1282877 := bstep (se 3 (by rfl) ⟨240539, by rfl⟩ : syracuseStep 1282877 = 481079) B481079
theorem B1708867 : Blo 354756 1708867 := bstep (se 1 (by rfl) ⟨1281650, by rfl⟩ : syracuseStep 1708867 = 2563301) B2563301
theorem B10327013 : Blo 354756 10327013 := bstep (se 4 (by rfl) ⟨968157, by rfl⟩ : syracuseStep 10327013 = 1936315) B1936315
theorem B1021511 : Blo 354756 1021511 := bstep (se 1 (by rfl) ⟨766133, by rfl⟩ : syracuseStep 1021511 = 1532267) B1532267
theorem B2037419 : Blo 354756 2037419 := bstep (se 1 (by rfl) ⟨1528064, by rfl⟩ : syracuseStep 2037419 = 3056129) B3056129
theorem B3413771 : Blo 354756 3413771 := bstep (se 1 (by rfl) ⟨2560328, by rfl⟩ : syracuseStep 3413771 = 5120657) B5120657
theorem B1087463 : Blo 354756 1087463 := bstep (se 1 (by rfl) ⟨815597, by rfl⟩ : syracuseStep 1087463 = 1631195) B1631195
theorem B399343 : Blo 354756 399343 := bstep (se 1 (by rfl) ⟨299507, by rfl⟩ : syracuseStep 399343 = 599015) B599015
theorem B89332109 : Blo 354756 89332109 := bstep (se 3 (by rfl) ⟨16749770, by rfl⟩ : syracuseStep 89332109 = 33499541) B33499541
theorem B1710713 : Blo 354756 1710713 := bstep (se 2 (by rfl) ⟨641517, by rfl⟩ : syracuseStep 1710713 = 1283035) B1283035
theorem B1809053 : Blo 354756 1809053 := bstep (se 3 (by rfl) ⟨339197, by rfl⟩ : syracuseStep 1809053 = 678395) B678395
theorem B3054419 : Blo 354756 3054419 := bstep (se 1 (by rfl) ⟨2290814, by rfl⟩ : syracuseStep 3054419 = 4581629) B4581629
theorem B2431903 : Blo 354756 2431903 := bstep (se 1 (by rfl) ⟨1823927, by rfl⟩ : syracuseStep 2431903 = 3647855) B3647855
theorem B1809377 : Blo 354756 1809377 := bstep (se 2 (by rfl) ⟨678516, by rfl⟩ : syracuseStep 1809377 = 1357033) B1357033
theorem B2891009 : Blo 354756 2891009 := bstep (se 2 (by rfl) ⟨1084128, by rfl⟩ : syracuseStep 2891009 = 2168257) B2168257
theorem B1285415 : Blo 354756 1285415 := bstep (se 1 (by rfl) ⟨964061, by rfl⟩ : syracuseStep 1285415 = 1928123) B1928123
theorem B2563559 : Blo 354756 2563559 := bstep (se 1 (by rfl) ⟨1922669, by rfl⟩ : syracuseStep 2563559 = 3845339) B3845339
theorem B532295 : Blo 354756 532295 := bstep (se 1 (by rfl) ⟨399221, by rfl⟩ : syracuseStep 532295 = 798443) B798443
theorem B532379 : Blo 354756 532379 := bstep (se 1 (by rfl) ⟨399284, by rfl⟩ : syracuseStep 532379 = 798569) B798569
theorem B1286077 : Blo 354756 1286077 := bstep (se 3 (by rfl) ⟨241139, by rfl⟩ : syracuseStep 1286077 = 482279) B482279
theorem B1286279 : Blo 354756 1286279 := bstep (se 1 (by rfl) ⟨964709, by rfl⟩ : syracuseStep 1286279 = 1929419) B1929419
theorem B5775731 : Blo 354756 5775731 := bstep (se 1 (by rfl) ⟨4331798, by rfl⟩ : syracuseStep 5775731 = 8663597) B8663597
theorem B401791 : Blo 354756 401791 := bstep (se 1 (by rfl) ⟨301343, by rfl⟩ : syracuseStep 401791 = 602687) B602687
theorem B532943 : Blo 354756 532943 := bstep (se 1 (by rfl) ⟨399707, by rfl⟩ : syracuseStep 532943 = 799415) B799415
theorem B532985 : Blo 354756 532985 := bstep (se 2 (by rfl) ⟨199869, by rfl⟩ : syracuseStep 532985 = 399739) B399739
theorem B533087 : Blo 354756 533087 := bstep (se 1 (by rfl) ⟨399815, by rfl⟩ : syracuseStep 533087 = 799631) B799631
theorem B599035 : Blo 354756 599035 := bstep (se 1 (by rfl) ⟨449276, by rfl⟩ : syracuseStep 599035 = 898553) B898553
theorem B861209 : Blo 354756 861209 := bstep (se 2 (by rfl) ⟨322953, by rfl⟩ : syracuseStep 861209 = 645907) B645907
theorem B533567 : Blo 354756 533567 := bstep (se 1 (by rfl) ⟨400175, by rfl⟩ : syracuseStep 533567 = 800351) B800351
theorem B533609 : Blo 354756 533609 := bstep (se 2 (by rfl) ⟨200103, by rfl⟩ : syracuseStep 533609 = 400207) B400207
theorem B435307 : Blo 354756 435307 := bstep (se 1 (by rfl) ⟨326480, by rfl⟩ : syracuseStep 435307 = 652961) B652961
theorem B1811645 : Blo 354756 1811645 := bstep (se 3 (by rfl) ⟨339683, by rfl⟩ : syracuseStep 1811645 = 679367) B679367
theorem B533711 : Blo 354756 533711 := bstep (se 1 (by rfl) ⟨400283, by rfl⟩ : syracuseStep 533711 = 800567) B800567
theorem B533915 : Blo 354756 533915 := bstep (se 1 (by rfl) ⟨400436, by rfl⟩ : syracuseStep 533915 = 800873) B800873
theorem B599467 : Blo 354756 599467 := bstep (se 1 (by rfl) ⟨449600, by rfl⟩ : syracuseStep 599467 = 899201) B899201
theorem B3090001 : Blo 354756 3090001 := bstep (se 2 (by rfl) ⟨1158750, by rfl⟩ : syracuseStep 3090001 = 2317501) B2317501
theorem B1451603 : Blo 354756 1451603 := bstep (se 1 (by rfl) ⟨1088702, by rfl⟩ : syracuseStep 1451603 = 2177405) B2177405
theorem B599663 : Blo 354756 599663 := bstep (se 1 (by rfl) ⟨449747, by rfl⟩ : syracuseStep 599663 = 899495) B899495
theorem B534137 : Blo 354756 534137 := bstep (se 2 (by rfl) ⟨200301, by rfl⟩ : syracuseStep 534137 = 400603) B400603
theorem B599771 : Blo 354756 599771 := bstep (se 1 (by rfl) ⟨449828, by rfl⟩ : syracuseStep 599771 = 899657) B899657
theorem B534239 : Blo 354756 534239 := bstep (se 1 (by rfl) ⟨400679, by rfl⟩ : syracuseStep 534239 = 801359) B801359
theorem B403195 : Blo 354756 403195 := bstep (se 1 (by rfl) ⟨302396, by rfl⟩ : syracuseStep 403195 = 604793) B604793
theorem B403231 : Blo 354756 403231 := bstep (se 1 (by rfl) ⟨302423, by rfl⟩ : syracuseStep 403231 = 604847) B604847
theorem B534335 : Blo 354756 534335 := bstep (se 1 (by rfl) ⟨400751, by rfl⟩ : syracuseStep 534335 = 801503) B801503
theorem B600007 : Blo 354756 600007 := bstep (se 1 (by rfl) ⟨450005, by rfl⟩ : syracuseStep 600007 = 900011) B900011
theorem B534503 : Blo 354756 534503 := bstep (se 1 (by rfl) ⟨400877, by rfl⟩ : syracuseStep 534503 = 801755) B801755
theorem B1746935 : Blo 354756 1746935 := bstep (se 1 (by rfl) ⟨1310201, by rfl⟩ : syracuseStep 1746935 = 2620403) B2620403
theorem B534521 : Blo 354756 534521 := bstep (se 2 (by rfl) ⟨200445, by rfl⟩ : syracuseStep 534521 = 400891) B400891
theorem B9119789 : Blo 354756 9119789 := bstep (se 3 (by rfl) ⟨1709960, by rfl⟩ : syracuseStep 9119789 = 3419921) B3419921
theorem B534623 : Blo 354756 534623 := bstep (se 1 (by rfl) ⟨400967, by rfl⟩ : syracuseStep 534623 = 801935) B801935
theorem B534683 : Blo 354756 534683 := bstep (se 1 (by rfl) ⟨401012, by rfl⟩ : syracuseStep 534683 = 802025) B802025
theorem B534719 : Blo 354756 534719 := bstep (se 1 (by rfl) ⟨401039, by rfl⟩ : syracuseStep 534719 = 802079) B802079
theorem B534761 : Blo 354756 534761 := bstep (se 2 (by rfl) ⟨200535, by rfl⟩ : syracuseStep 534761 = 401071) B401071
theorem B3418463 : Blo 354756 3418463 := bstep (se 1 (by rfl) ⟨2563847, by rfl⟩ : syracuseStep 3418463 = 5127695) B5127695
theorem B764255 : Blo 354756 764255 := bstep (se 1 (by rfl) ⟨573191, by rfl⟩ : syracuseStep 764255 = 1146383) B1146383
theorem B960925 : Blo 354756 960925 := bstep (se 3 (by rfl) ⟨180173, by rfl⟩ : syracuseStep 960925 = 360347) B360347
theorem B1452545 : Blo 354756 1452545 := bstep (se 2 (by rfl) ⟨544704, by rfl⟩ : syracuseStep 1452545 = 1089409) B1089409
theorem B10267145 : Blo 354756 10267145 := bstep (se 2 (by rfl) ⟨3850179, by rfl⟩ : syracuseStep 10267145 = 7700359) B7700359
theorem B535067 : Blo 354756 535067 := bstep (se 1 (by rfl) ⟨401300, by rfl⟩ : syracuseStep 535067 = 802601) B802601
theorem B2173511 : Blo 354756 2173511 := bstep (se 1 (by rfl) ⟨1630133, by rfl⟩ : syracuseStep 2173511 = 3260267) B3260267
theorem B535145 : Blo 354756 535145 := bstep (se 2 (by rfl) ⟨200679, by rfl⟩ : syracuseStep 535145 = 401359) B401359
theorem B600763 : Blo 354756 600763 := bstep (se 1 (by rfl) ⟨450572, by rfl⟩ : syracuseStep 600763 = 901145) B901145
theorem B2042819 : Blo 354756 2042819 := bstep (se 1 (by rfl) ⟨1532114, by rfl⟩ : syracuseStep 2042819 = 3064229) B3064229
theorem B568271 : Blo 354756 568271 := bstep (se 1 (by rfl) ⟨426203, by rfl⟩ : syracuseStep 568271 = 852407) B852407
theorem B1289191 : Blo 354756 1289191 := bstep (se 1 (by rfl) ⟨966893, by rfl⟩ : syracuseStep 1289191 = 1933787) B1933787
theorem B601067 : Blo 354756 601067 := bstep (se 1 (by rfl) ⟨450800, by rfl⟩ : syracuseStep 601067 = 901601) B901601
theorem B535673 : Blo 354756 535673 := bstep (se 2 (by rfl) ⟨200877, by rfl⟩ : syracuseStep 535673 = 401755) B401755
theorem B535775 : Blo 354756 535775 := bstep (se 1 (by rfl) ⟨401831, by rfl⟩ : syracuseStep 535775 = 803663) B803663
theorem B535817 : Blo 354756 535817 := bstep (se 2 (by rfl) ⟨200931, by rfl⟩ : syracuseStep 535817 = 401863) B401863
theorem B765263 : Blo 354756 765263 := bstep (se 1 (by rfl) ⟨573947, by rfl⟩ : syracuseStep 765263 = 1147895) B1147895
theorem B535919 : Blo 354756 535919 := bstep (se 1 (by rfl) ⟨401939, by rfl⟩ : syracuseStep 535919 = 803879) B803879
theorem B10530269 : Blo 354756 10530269 := bstep (se 3 (by rfl) ⟨1974425, by rfl⟩ : syracuseStep 10530269 = 3948851) B3948851
theorem B536039 : Blo 354756 536039 := bstep (se 1 (by rfl) ⟨402029, by rfl⟩ : syracuseStep 536039 = 804059) B804059
theorem B798281 : Blo 354756 798281 := bstep (se 2 (by rfl) ⟨299355, by rfl⟩ : syracuseStep 798281 = 598711) B598711
theorem B536171 : Blo 354756 536171 := bstep (se 1 (by rfl) ⟨402128, by rfl⟩ : syracuseStep 536171 = 804257) B804257
theorem B536297 : Blo 354756 536297 := bstep (se 2 (by rfl) ⟨201111, by rfl⟩ : syracuseStep 536297 = 402223) B402223
theorem B536441 : Blo 354756 536441 := bstep (se 2 (by rfl) ⟨201165, by rfl⟩ : syracuseStep 536441 = 402331) B402331
theorem B536543 : Blo 354756 536543 := bstep (se 1 (by rfl) ⟨402407, by rfl⟩ : syracuseStep 536543 = 804815) B804815
theorem B1814723 : Blo 354756 1814723 := bstep (se 1 (by rfl) ⟨1361042, by rfl⟩ : syracuseStep 1814723 = 2722085) B2722085
theorem B536795 : Blo 354756 536795 := bstep (se 1 (by rfl) ⟨402596, by rfl⟩ : syracuseStep 536795 = 805193) B805193
theorem B536807 : Blo 354756 536807 := bstep (se 1 (by rfl) ⟨402605, by rfl⟩ : syracuseStep 536807 = 805211) B805211
theorem B1356061 : Blo 354756 1356061 := bstep (se 3 (by rfl) ⟨254261, by rfl⟩ : syracuseStep 1356061 = 508523) B508523
theorem B536969 : Blo 354756 536969 := bstep (se 2 (by rfl) ⟨201363, by rfl⟩ : syracuseStep 536969 = 402727) B402727
theorem B537065 : Blo 354756 537065 := bstep (se 2 (by rfl) ⟨201399, by rfl⟩ : syracuseStep 537065 = 402799) B402799
theorem B963065 : Blo 354756 963065 := bstep (se 2 (by rfl) ⟨361149, by rfl⟩ : syracuseStep 963065 = 722299) B722299
theorem B537191 : Blo 354756 537191 := bstep (se 1 (by rfl) ⟨402893, by rfl⟩ : syracuseStep 537191 = 805787) B805787
theorem B537323 : Blo 354756 537323 := bstep (se 1 (by rfl) ⟨402992, by rfl⟩ : syracuseStep 537323 = 805985) B805985
theorem B537353 : Blo 354756 537353 := bstep (se 2 (by rfl) ⟨201507, by rfl⟩ : syracuseStep 537353 = 403015) B403015
theorem B4338461 : Blo 354756 4338461 := bstep (se 3 (by rfl) ⟨813461, by rfl⟩ : syracuseStep 4338461 = 1626923) B1626923
theorem B537455 : Blo 354756 537455 := bstep (se 1 (by rfl) ⟨403091, by rfl⟩ : syracuseStep 537455 = 806183) B806183
theorem B799739 : Blo 354756 799739 := bstep (se 1 (by rfl) ⟨599804, by rfl⟩ : syracuseStep 799739 = 1199609) B1199609
theorem B537707 : Blo 354756 537707 := bstep (se 1 (by rfl) ⟨403280, by rfl⟩ : syracuseStep 537707 = 806561) B806561
theorem B799919 : Blo 354756 799919 := bstep (se 1 (by rfl) ⟨599939, by rfl⟩ : syracuseStep 799919 = 1199879) B1199879
theorem B799955 : Blo 354756 799955 := bstep (se 1 (by rfl) ⟨599966, by rfl⟩ : syracuseStep 799955 = 1199933) B1199933
theorem B1520957 : Blo 354756 1520957 := bstep (se 3 (by rfl) ⟨285179, by rfl⟩ : syracuseStep 1520957 = 570359) B570359
theorem B537947 : Blo 354756 537947 := bstep (se 1 (by rfl) ⟨403460, by rfl⟩ : syracuseStep 537947 = 806921) B806921
theorem B9811361 : Blo 354756 9811361 := bstep (se 2 (by rfl) ⟨3679260, by rfl⟩ : syracuseStep 9811361 = 7358521) B7358521
theorem B10270151 : Blo 354756 10270151 := bstep (se 1 (by rfl) ⟨7702613, by rfl⟩ : syracuseStep 10270151 = 15405227) B15405227
theorem B800225 : Blo 354756 800225 := bstep (se 2 (by rfl) ⟨300084, by rfl⟩ : syracuseStep 800225 = 600169) B600169
theorem B603983 : Blo 354756 603983 := bstep (se 1 (by rfl) ⟨452987, by rfl⟩ : syracuseStep 603983 = 905975) B905975
theorem B1292449 : Blo 354756 1292449 := bstep (se 2 (by rfl) ⟨484668, by rfl⟩ : syracuseStep 1292449 = 969337) B969337
theorem B16694191 : Blo 354756 16694191 := bstep (se 1 (by rfl) ⟨12520643, by rfl⟩ : syracuseStep 16694191 = 25041287) B25041287
theorem B2440145 : Blo 354756 2440145 := bstep (se 2 (by rfl) ⟨915054, by rfl⟩ : syracuseStep 2440145 = 1830109) B1830109
theorem B539627 : Blo 354756 539627 := bstep (se 1 (by rfl) ⟨404720, by rfl⟩ : syracuseStep 539627 = 809441) B809441
theorem B605225 : Blo 354756 605225 := bstep (se 2 (by rfl) ⟨226959, by rfl⟩ : syracuseStep 605225 = 453919) B453919
theorem B801863 : Blo 354756 801863 := bstep (se 1 (by rfl) ⟨601397, by rfl⟩ : syracuseStep 801863 = 1202795) B1202795
theorem B1358977 : Blo 354756 1358977 := bstep (se 2 (by rfl) ⟨509616, by rfl⟩ : syracuseStep 1358977 = 1019233) B1019233
theorem B1522871 : Blo 354756 1522871 := bstep (se 1 (by rfl) ⟨1142153, by rfl⟩ : syracuseStep 1522871 = 2284307) B2284307
theorem B802259 : Blo 354756 802259 := bstep (se 1 (by rfl) ⟨601694, by rfl⟩ : syracuseStep 802259 = 1203389) B1203389
theorem B15711853 : Blo 354756 15711853 := bstep (se 3 (by rfl) ⟨2945972, by rfl⟩ : syracuseStep 15711853 = 5891945) B5891945
theorem B966287 : Blo 354756 966287 := bstep (se 1 (by rfl) ⟨724715, by rfl⟩ : syracuseStep 966287 = 1449431) B1449431
theorem B802529 : Blo 354756 802529 := bstep (se 2 (by rfl) ⟨300948, by rfl⟩ : syracuseStep 802529 = 601897) B601897
theorem B900841 : Blo 354756 900841 := bstep (se 2 (by rfl) ⟨337815, by rfl⟩ : syracuseStep 900841 = 675631) B675631
theorem B4572197 : Blo 354756 4572197 := bstep (se 4 (by rfl) ⟨428643, by rfl⟩ : syracuseStep 4572197 = 857287) B857287
theorem B8700965 : Blo 354756 8700965 := bstep (se 4 (by rfl) ⟨815715, by rfl⟩ : syracuseStep 8700965 = 1631431) B1631431
theorem B640055 : Blo 354756 640055 := bstep (se 1 (by rfl) ⟨480041, by rfl⟩ : syracuseStep 640055 = 960083) B960083
theorem B902249 : Blo 354756 902249 := bstep (se 2 (by rfl) ⟨338343, by rfl⟩ : syracuseStep 902249 = 676687) B676687
theorem B7062833 : Blo 354756 7062833 := bstep (se 2 (by rfl) ⟨2648562, by rfl⟩ : syracuseStep 7062833 = 5297125) B5297125
theorem B1361225 : Blo 354756 1361225 := bstep (se 2 (by rfl) ⟨510459, by rfl⟩ : syracuseStep 1361225 = 1020919) B1020919
theorem B509275 : Blo 354756 509275 := bstep (se 1 (by rfl) ⟨381956, by rfl⟩ : syracuseStep 509275 = 763913) B763913
theorem B804203 : Blo 354756 804203 := bstep (se 1 (by rfl) ⟨603152, by rfl⟩ : syracuseStep 804203 = 1206305) B1206305
theorem B1197449 : Blo 354756 1197449 := bstep (se 2 (by rfl) ⟨449043, by rfl⟩ : syracuseStep 1197449 = 898087) B898087
theorem B2573707 : Blo 354756 2573707 := bstep (se 1 (by rfl) ⟨1930280, by rfl⟩ : syracuseStep 2573707 = 3860561) B3860561
theorem B804473 : Blo 354756 804473 := bstep (se 2 (by rfl) ⟨301677, by rfl⟩ : syracuseStep 804473 = 603355) B603355
theorem B2475805 : Blo 354756 2475805 := bstep (se 3 (by rfl) ⟨464213, by rfl⟩ : syracuseStep 2475805 = 928427) B928427
theorem B2279333 : Blo 354756 2279333 := bstep (se 4 (by rfl) ⟨213687, by rfl⟩ : syracuseStep 2279333 = 427375) B427375
theorem B1198205 : Blo 354756 1198205 := bstep (se 3 (by rfl) ⟨224663, by rfl⟩ : syracuseStep 1198205 = 449327) B449327
theorem B4376753 : Blo 354756 4376753 := bstep (se 2 (by rfl) ⟨1641282, by rfl⟩ : syracuseStep 4376753 = 3282565) B3282565
theorem B903383 : Blo 354756 903383 := bstep (se 1 (by rfl) ⟨677537, by rfl⟩ : syracuseStep 903383 = 1355075) B1355075
theorem B542953 : Blo 354756 542953 := bstep (se 2 (by rfl) ⟨203607, by rfl⟩ : syracuseStep 542953 = 407215) B407215
theorem B641287 : Blo 354756 641287 := bstep (se 1 (by rfl) ⟨480965, by rfl⟩ : syracuseStep 641287 = 961931) B961931
theorem B1198475 : Blo 354756 1198475 := bstep (se 1 (by rfl) ⟨898856, by rfl⟩ : syracuseStep 1198475 = 1797713) B1797713
theorem B903707 : Blo 354756 903707 := bstep (se 1 (by rfl) ⟨677780, by rfl⟩ : syracuseStep 903707 = 1355561) B1355561
theorem B805481 : Blo 354756 805481 := bstep (se 2 (by rfl) ⟨302055, by rfl⟩ : syracuseStep 805481 = 604111) B604111
theorem B806111 : Blo 354756 806111 := bstep (se 1 (by rfl) ⟨604583, by rfl⟩ : syracuseStep 806111 = 1209167) B1209167
theorem B2608357 : Blo 354756 2608357 := bstep (se 4 (by rfl) ⟨244533, by rfl⟩ : syracuseStep 2608357 = 489067) B489067
theorem B2903465 : Blo 354756 2903465 := bstep (se 2 (by rfl) ⟨1088799, by rfl⟩ : syracuseStep 2903465 = 2177599) B2177599
theorem B806327 : Blo 354756 806327 := bstep (se 1 (by rfl) ⟨604745, by rfl⟩ : syracuseStep 806327 = 1209491) B1209491
theorem B806507 : Blo 354756 806507 := bstep (se 1 (by rfl) ⟨604880, by rfl⟩ : syracuseStep 806507 = 1209761) B1209761
theorem B1298045 : Blo 354756 1298045 := bstep (se 3 (by rfl) ⟨243383, by rfl⟩ : syracuseStep 1298045 = 486767) B486767
theorem B1068701 : Blo 354756 1068701 := bstep (se 3 (by rfl) ⟨200381, by rfl⟩ : syracuseStep 1068701 = 400763) B400763
theorem B380743 : Blo 354756 380743 := bstep (se 1 (by rfl) ⟨285557, by rfl⟩ : syracuseStep 380743 = 571115) B571115
theorem B806777 : Blo 354756 806777 := bstep (se 2 (by rfl) ⟨302541, by rfl⟩ : syracuseStep 806777 = 605083) B605083
theorem B1200095 : Blo 354756 1200095 := bstep (se 1 (by rfl) ⟨900071, by rfl⟩ : syracuseStep 1200095 = 1800143) B1800143
theorem B1200257 : Blo 354756 1200257 := bstep (se 2 (by rfl) ⟨450096, by rfl⟩ : syracuseStep 1200257 = 900193) B900193
theorem B479695 : Blo 354756 479695 := bstep (se 1 (by rfl) ⟨359771, by rfl⟩ : syracuseStep 479695 = 719543) B719543
theorem B676345 : Blo 354756 676345 := bstep (se 2 (by rfl) ⟨253629, by rfl⟩ : syracuseStep 676345 = 507259) B507259
theorem B1200743 : Blo 354756 1200743 := bstep (se 1 (by rfl) ⟨900557, by rfl⟩ : syracuseStep 1200743 = 1801115) B1801115
theorem B676649 : Blo 354756 676649 := bstep (se 2 (by rfl) ⟨253743, by rfl⟩ : syracuseStep 676649 = 507487) B507487
theorem B906025 : Blo 354756 906025 := bstep (se 2 (by rfl) ⟨339759, by rfl⟩ : syracuseStep 906025 = 679519) B679519
theorem B1201067 : Blo 354756 1201067 := bstep (se 1 (by rfl) ⟨900800, by rfl⟩ : syracuseStep 1201067 = 1801601) B1801601
theorem B676937 : Blo 354756 676937 := bstep (se 2 (by rfl) ⟨253851, by rfl⟩ : syracuseStep 676937 = 507703) B507703
theorem B1201499 : Blo 354756 1201499 := bstep (se 1 (by rfl) ⟨901124, by rfl⟩ : syracuseStep 1201499 = 1802249) B1802249
theorem B1201607 : Blo 354756 1201607 := bstep (se 1 (by rfl) ⟨901205, by rfl⟩ : syracuseStep 1201607 = 1802411) B1802411
theorem B1201931 : Blo 354756 1201931 := bstep (se 1 (by rfl) ⟨901448, by rfl⟩ : syracuseStep 1201931 = 1802897) B1802897
theorem B1202201 : Blo 354756 1202201 := bstep (se 2 (by rfl) ⟨450825, by rfl⟩ : syracuseStep 1202201 = 901651) B901651
theorem B907463 : Blo 354756 907463 := bstep (se 1 (by rfl) ⟨680597, by rfl⟩ : syracuseStep 907463 = 1361195) B1361195
theorem B579817 : Blo 354756 579817 := bstep (se 2 (by rfl) ⟨217431, by rfl⟩ : syracuseStep 579817 = 434863) B434863
theorem B1366313 : Blo 354756 1366313 := bstep (se 2 (by rfl) ⟨512367, by rfl⟩ : syracuseStep 1366313 = 1024735) B1024735
theorem B3037607 : Blo 354756 3037607 := bstep (se 1 (by rfl) ⟨2278205, by rfl⟩ : syracuseStep 3037607 = 4556411) B4556411
theorem B547355 : Blo 354756 547355 := bstep (se 1 (by rfl) ⟨410516, by rfl⟩ : syracuseStep 547355 = 821033) B821033
theorem B678881 : Blo 354756 678881 := bstep (se 2 (by rfl) ⟨254580, by rfl⟩ : syracuseStep 678881 = 509161) B509161
theorem B1465559 : Blo 354756 1465559 := bstep (se 1 (by rfl) ⟨1099169, by rfl⟩ : syracuseStep 1465559 = 2198339) B2198339
theorem B482527 : Blo 354756 482527 := bstep (se 1 (by rfl) ⟨361895, by rfl⟩ : syracuseStep 482527 = 723791) B723791
theorem B1203551 : Blo 354756 1203551 := bstep (se 1 (by rfl) ⟨902663, by rfl⟩ : syracuseStep 1203551 = 1805327) B1805327
theorem B1629551 : Blo 354756 1629551 := bstep (se 1 (by rfl) ⟨1222163, by rfl⟩ : syracuseStep 1629551 = 2444327) B2444327
theorem B21880685 : Blo 354756 21880685 := bstep (se 3 (by rfl) ⟨4102628, by rfl⟩ : syracuseStep 21880685 = 8205257) B8205257
theorem B1204091 : Blo 354756 1204091 := bstep (se 1 (by rfl) ⟨903068, by rfl⟩ : syracuseStep 1204091 = 1806137) B1806137
theorem B3891239 : Blo 354756 3891239 := bstep (se 1 (by rfl) ⟨2918429, by rfl⟩ : syracuseStep 3891239 = 5836859) B5836859
theorem B1204577 : Blo 354756 1204577 := bstep (se 2 (by rfl) ⟨451716, by rfl⟩ : syracuseStep 1204577 = 903433) B903433
theorem B1139143 : Blo 354756 1139143 := bstep (se 1 (by rfl) ⟨854357, by rfl⟩ : syracuseStep 1139143 = 1708715) B1708715
theorem B1926737 : Blo 354756 1926737 := bstep (se 2 (by rfl) ⟨722526, by rfl⟩ : syracuseStep 1926737 = 1445053) B1445053
theorem B1205927 : Blo 354756 1205927 := bstep (se 1 (by rfl) ⟨904445, by rfl⟩ : syracuseStep 1205927 = 1808891) B1808891
theorem B1206521 : Blo 354756 1206521 := bstep (se 2 (by rfl) ⟨452445, by rfl⟩ : syracuseStep 1206521 = 904891) B904891
theorem B1206575 : Blo 354756 1206575 := bstep (se 1 (by rfl) ⟨904931, by rfl⟩ : syracuseStep 1206575 = 1809863) B1809863
theorem B1206791 : Blo 354756 1206791 := bstep (se 1 (by rfl) ⟨905093, by rfl⟩ : syracuseStep 1206791 = 1810187) B1810187
theorem B354843 : Blo 354756 354843 := bstep (se 1 (by rfl) ⟨266132, by rfl⟩ : syracuseStep 354843 = 532265) B532265
theorem B354847 : Blo 354756 354847 := bstep (se 1 (by rfl) ⟨266135, by rfl⟩ : syracuseStep 354847 = 532271) B532271
theorem B355163 : Blo 354756 355163 := bstep (se 1 (by rfl) ⟨266372, by rfl⟩ : syracuseStep 355163 = 532745) B532745
theorem B355231 : Blo 354756 355231 := bstep (se 1 (by rfl) ⟨266423, by rfl⟩ : syracuseStep 355231 = 532847) B532847
theorem B355375 : Blo 354756 355375 := bstep (se 1 (by rfl) ⟨266531, by rfl⟩ : syracuseStep 355375 = 533063) B533063
theorem B355399 : Blo 354756 355399 := bstep (se 1 (by rfl) ⟨266549, by rfl⟩ : syracuseStep 355399 = 533099) B533099
theorem B1207439 : Blo 354756 1207439 := bstep (se 1 (by rfl) ⟨905579, by rfl⟩ : syracuseStep 1207439 = 1811159) B1811159
theorem B355551 : Blo 354756 355551 := bstep (se 1 (by rfl) ⟨266663, by rfl⟩ : syracuseStep 355551 = 533327) B533327
theorem B3009869 : Blo 354756 3009869 := bstep (se 3 (by rfl) ⟨564350, by rfl⟩ : syracuseStep 3009869 = 1128701) B1128701
theorem B4550053 : Blo 354756 4550053 := bstep (se 4 (by rfl) ⟨426567, by rfl⟩ : syracuseStep 4550053 = 853135) B853135
theorem B1011113 : Blo 354756 1011113 := bstep (se 2 (by rfl) ⟨379167, by rfl⟩ : syracuseStep 1011113 = 758335) B758335
theorem B355815 : Blo 354756 355815 := bstep (se 1 (by rfl) ⟨266861, by rfl⟩ : syracuseStep 355815 = 533723) B533723
theorem B1207871 : Blo 354756 1207871 := bstep (se 1 (by rfl) ⟨905903, by rfl⟩ : syracuseStep 1207871 = 1811807) B1811807
theorem B355931 : Blo 354756 355931 := bstep (se 1 (by rfl) ⟨266948, by rfl⟩ : syracuseStep 355931 = 533897) B533897
theorem B356167 : Blo 354756 356167 := bstep (se 1 (by rfl) ⟨267125, by rfl⟩ : syracuseStep 356167 = 534251) B534251
theorem B3862379 : Blo 354756 3862379 := bstep (se 1 (by rfl) ⟨2896784, by rfl⟩ : syracuseStep 3862379 = 5793569) B5793569
theorem B356319 : Blo 354756 356319 := bstep (se 1 (by rfl) ⟨267239, by rfl⟩ : syracuseStep 356319 = 534479) B534479
theorem B2715767 : Blo 354756 2715767 := bstep (se 1 (by rfl) ⟨2036825, by rfl⟩ : syracuseStep 2715767 = 4073651) B4073651
theorem B2158721 : Blo 354756 2158721 := bstep (se 2 (by rfl) ⟨809520, by rfl⟩ : syracuseStep 2158721 = 1619041) B1619041
theorem B356583 : Blo 354756 356583 := bstep (se 1 (by rfl) ⟨267437, by rfl⟩ : syracuseStep 356583 = 534875) B534875
theorem B1208573 : Blo 354756 1208573 := bstep (se 3 (by rfl) ⟨226607, by rfl⟩ : syracuseStep 1208573 = 453215) B453215
theorem B356735 : Blo 354756 356735 := bstep (se 1 (by rfl) ⟨267551, by rfl⟩ : syracuseStep 356735 = 535103) B535103
theorem B356815 : Blo 354756 356815 := bstep (se 1 (by rfl) ⟨267611, by rfl⟩ : syracuseStep 356815 = 535223) B535223
theorem B2027987 : Blo 354756 2027987 := bstep (se 1 (by rfl) ⟨1520990, by rfl⟩ : syracuseStep 2027987 = 3041981) B3041981
theorem B356967 : Blo 354756 356967 := bstep (se 1 (by rfl) ⟨267725, by rfl⟩ : syracuseStep 356967 = 535451) B535451
theorem B4551389 : Blo 354756 4551389 := bstep (se 3 (by rfl) ⟨853385, by rfl⟩ : syracuseStep 4551389 = 1706771) B1706771
theorem B1209113 : Blo 354756 1209113 := bstep (se 2 (by rfl) ⟨453417, by rfl⟩ : syracuseStep 1209113 = 906835) B906835
theorem B357231 : Blo 354756 357231 := bstep (se 1 (by rfl) ⟨267923, by rfl⟩ : syracuseStep 357231 = 535847) B535847
theorem B357287 : Blo 354756 357287 := bstep (se 1 (by rfl) ⟨267965, by rfl⟩ : syracuseStep 357287 = 535931) B535931
theorem B357371 : Blo 354756 357371 := bstep (se 1 (by rfl) ⟨268028, by rfl⟩ : syracuseStep 357371 = 536057) B536057
theorem B1209383 : Blo 354756 1209383 := bstep (se 1 (by rfl) ⟨907037, by rfl⟩ : syracuseStep 1209383 = 1814075) B1814075
theorem B357439 : Blo 354756 357439 := bstep (se 1 (by rfl) ⟨268079, by rfl⟩ : syracuseStep 357439 = 536159) B536159
theorem B357583 : Blo 354756 357583 := bstep (se 1 (by rfl) ⟨268187, by rfl⟩ : syracuseStep 357583 = 536375) B536375
theorem B2159891 : Blo 354756 2159891 := bstep (se 1 (by rfl) ⟨1619918, by rfl⟩ : syracuseStep 2159891 = 3239837) B3239837
theorem B357787 : Blo 354756 357787 := bstep (se 1 (by rfl) ⟨268340, by rfl⟩ : syracuseStep 357787 = 536681) B536681
theorem B2028989 : Blo 354756 2028989 := bstep (se 3 (by rfl) ⟨380435, by rfl⟩ : syracuseStep 2028989 = 760871) B760871
theorem B20739629 : Blo 354756 20739629 := bstep (se 3 (by rfl) ⟨3888680, by rfl⟩ : syracuseStep 20739629 = 7777361) B7777361
theorem B357999 : Blo 354756 357999 := bstep (se 1 (by rfl) ⟨268499, by rfl⟩ : syracuseStep 357999 = 536999) B536999
theorem B358055 : Blo 354756 358055 := bstep (se 1 (by rfl) ⟨268541, by rfl⟩ : syracuseStep 358055 = 537083) B537083
theorem B358139 : Blo 354756 358139 := bstep (se 1 (by rfl) ⟨268604, by rfl⟩ : syracuseStep 358139 = 537209) B537209
theorem B358175 : Blo 354756 358175 := bstep (se 1 (by rfl) ⟨268631, by rfl⟩ : syracuseStep 358175 = 537263) B537263
theorem B358207 : Blo 354756 358207 := bstep (se 1 (by rfl) ⟨268655, by rfl⟩ : syracuseStep 358207 = 537311) B537311
theorem B10417997 : Blo 354756 10417997 := bstep (se 3 (by rfl) ⟨1953374, by rfl⟩ : syracuseStep 10417997 = 3906749) B3906749
theorem B358383 : Blo 354756 358383 := bstep (se 1 (by rfl) ⟨268787, by rfl⟩ : syracuseStep 358383 = 537575) B537575
theorem B1210463 : Blo 354756 1210463 := bstep (se 1 (by rfl) ⟨907847, by rfl⟩ : syracuseStep 1210463 = 1815695) B1815695
theorem B1013903 : Blo 354756 1013903 := bstep (se 1 (by rfl) ⟨760427, by rfl⟩ : syracuseStep 1013903 = 1520855) B1520855
theorem B1243279 : Blo 354756 1243279 := bstep (se 1 (by rfl) ⟨932459, by rfl⟩ : syracuseStep 1243279 = 1864919) B1864919
theorem B358555 : Blo 354756 358555 := bstep (se 1 (by rfl) ⟨268916, by rfl⟩ : syracuseStep 358555 = 537833) B537833
theorem B358591 : Blo 354756 358591 := bstep (se 1 (by rfl) ⟨268943, by rfl⟩ : syracuseStep 358591 = 537887) B537887
theorem B653609 : Blo 354756 653609 := bstep (se 2 (by rfl) ⟨245103, by rfl⟩ : syracuseStep 653609 = 490207) B490207
theorem B358703 : Blo 354756 358703 := bstep (se 1 (by rfl) ⟨269027, by rfl⟩ : syracuseStep 358703 = 538055) B538055
theorem B687055 : Blo 354756 687055 := bstep (se 1 (by rfl) ⟨515291, by rfl⟩ : syracuseStep 687055 = 1030583) B1030583
theorem B2719169 : Blo 354756 2719169 := bstep (se 2 (by rfl) ⟨1019688, by rfl⟩ : syracuseStep 2719169 = 2039377) B2039377
theorem B1703405 : Blo 354756 1703405 := bstep (se 3 (by rfl) ⟨319388, by rfl⟩ : syracuseStep 1703405 = 638777) B638777
theorem B37092923 : Blo 354756 37092923 := bstep (se 1 (by rfl) ⟨27819692, by rfl⟩ : syracuseStep 37092923 = 55639385) B55639385
theorem B3048131 : Blo 354756 3048131 := bstep (se 1 (by rfl) ⟨2286098, by rfl⟩ : syracuseStep 3048131 = 4572197) B4572197
theorem B5800643 : Blo 354756 5800643 := bstep (se 1 (by rfl) ⟨4350482, by rfl⟩ : syracuseStep 5800643 = 8700965) B8700965
theorem B426703 : Blo 354756 426703 := bstep (se 1 (by rfl) ⟨320027, by rfl⟩ : syracuseStep 426703 = 640055) B640055
theorem B2917835 : Blo 354756 2917835 := bstep (se 1 (by rfl) ⟨2188376, by rfl⟩ : syracuseStep 2917835 = 4376753) B4376753
theorem B11569229 : Blo 354756 11569229 := bstep (se 3 (by rfl) ⟨2169230, by rfl⟩ : syracuseStep 11569229 = 4338461) B4338461
theorem B13699367 : Blo 354756 13699367 := bstep (se 1 (by rfl) ⟨10274525, by rfl⟩ : syracuseStep 13699367 = 20549051) B20549051
theorem B5114663 : Blo 354756 5114663 := bstep (se 1 (by rfl) ⟨3835997, by rfl⟩ : syracuseStep 5114663 = 7671995) B7671995
theorem B854867 : Blo 354756 854867 := bstep (se 1 (by rfl) ⟨641150, by rfl⟩ : syracuseStep 854867 = 1282301) B1282301
theorem B1805165 : Blo 354756 1805165 := bstep (se 3 (by rfl) ⟨338468, by rfl⟩ : syracuseStep 1805165 = 676937) B676937
theorem B855049 : Blo 354756 855049 := bstep (se 2 (by rfl) ⟨320643, by rfl⟩ : syracuseStep 855049 = 641287) B641287
theorem B1707193 : Blo 354756 1707193 := bstep (se 2 (by rfl) ⟨640197, by rfl⟩ : syracuseStep 1707193 = 1280395) B1280395
theorem B1281233 : Blo 354756 1281233 := bstep (se 2 (by rfl) ⟨480462, by rfl⟩ : syracuseStep 1281233 = 960925) B960925
theorem B855251 : Blo 354756 855251 := bstep (se 1 (by rfl) ⟨641438, by rfl⟩ : syracuseStep 855251 = 1282877) B1282877
theorem B6884675 : Blo 354756 6884675 := bstep (se 1 (by rfl) ⟨5163506, by rfl⟩ : syracuseStep 6884675 = 10327013) B10327013
theorem B2724029 : Blo 354756 2724029 := bstep (se 3 (by rfl) ⟨510755, by rfl⟩ : syracuseStep 2724029 = 1021511) B1021511
theorem B6295805 : Blo 354756 6295805 := bstep (se 3 (by rfl) ⟨1180463, by rfl⟩ : syracuseStep 6295805 = 2360927) B2360927
theorem B3477809 : Blo 354756 3477809 := bstep (se 2 (by rfl) ⟨1304178, by rfl⟩ : syracuseStep 3477809 = 2608357) B2608357
theorem B6066737 : Blo 354756 6066737 := bstep (se 2 (by rfl) ⟨2275026, by rfl⟩ : syracuseStep 6066737 = 4550053) B4550053
theorem B2036279 : Blo 354756 2036279 := bstep (se 1 (by rfl) ⟨1527209, by rfl⟩ : syracuseStep 2036279 = 3054419) B3054419
theorem B3412813 : Blo 354756 3412813 := bstep (se 3 (by rfl) ⟨639902, by rfl⟩ : syracuseStep 3412813 = 1279805) B1279805
theorem B856943 : Blo 354756 856943 := bstep (se 1 (by rfl) ⟨642707, by rfl⟩ : syracuseStep 856943 = 1285415) B1285415
theorem B1086367 : Blo 354756 1086367 := bstep (se 1 (by rfl) ⟨814775, by rfl⟩ : syracuseStep 1086367 = 1629551) B1629551
theorem B1709039 : Blo 354756 1709039 := bstep (se 1 (by rfl) ⟨1281779, by rfl⟩ : syracuseStep 1709039 = 2563559) B2563559
theorem B14587123 : Blo 354756 14587123 := bstep (se 1 (by rfl) ⟨10940342, by rfl⟩ : syracuseStep 14587123 = 21880685) B21880685
theorem B2594159 : Blo 354756 2594159 := bstep (se 1 (by rfl) ⟨1945619, by rfl⟩ : syracuseStep 2594159 = 3891239) B3891239
theorem B857519 : Blo 354756 857519 := bstep (se 1 (by rfl) ⟨643139, by rfl⟩ : syracuseStep 857519 = 1286279) B1286279
theorem B1808081 : Blo 354756 1808081 := bstep (se 2 (by rfl) ⟨678030, by rfl⟩ : syracuseStep 1808081 = 1356061) B1356061
theorem B3643501 : Blo 354756 3643501 := bstep (se 3 (by rfl) ⟨683156, by rfl⟩ : syracuseStep 3643501 = 1366313) B1366313
theorem B1742957 : Blo 354756 1742957 := bstep (se 3 (by rfl) ⟨326804, by rfl⟩ : syracuseStep 1742957 = 653609) B653609
theorem B1284491 : Blo 354756 1284491 := bstep (se 1 (by rfl) ⟨963368, by rfl⟩ : syracuseStep 1284491 = 1926737) B1926737
theorem B399775 : Blo 354756 399775 := bstep (se 1 (by rfl) ⟨299831, by rfl⟩ : syracuseStep 399775 = 599663) B599663
theorem B399847 : Blo 354756 399847 := bstep (se 1 (by rfl) ⟨299885, by rfl⟩ : syracuseStep 399847 = 599771) B599771
theorem B400711 : Blo 354756 400711 := bstep (se 1 (by rfl) ⟨300533, by rfl⟩ : syracuseStep 400711 = 601067) B601067
theorem B2006579 : Blo 354756 2006579 := bstep (se 1 (by rfl) ⟨1504934, by rfl⟩ : syracuseStep 2006579 = 3009869) B3009869
theorem B7020179 : Blo 354756 7020179 := bstep (se 1 (by rfl) ⟨5265134, by rfl⟩ : syracuseStep 7020179 = 10530269) B10530269
theorem B532187 : Blo 354756 532187 := bstep (se 1 (by rfl) ⟨399140, by rfl⟩ : syracuseStep 532187 = 798281) B798281
theorem B1810349 : Blo 354756 1810349 := bstep (se 3 (by rfl) ⟨339440, by rfl⟩ : syracuseStep 1810349 = 678881) B678881
theorem B532457 : Blo 354756 532457 := bstep (se 2 (by rfl) ⟨199671, by rfl⟩ : syracuseStep 532457 = 399343) B399343
theorem B1810511 : Blo 354756 1810511 := bstep (se 1 (by rfl) ⟨1357883, by rfl⟩ : syracuseStep 1810511 = 2715767) B2715767
theorem B1351991 : Blo 354756 1351991 := bstep (se 1 (by rfl) ⟨1013993, by rfl⟩ : syracuseStep 1351991 = 2027987) B2027987
theorem B533159 : Blo 354756 533159 := bstep (se 1 (by rfl) ⟨399869, by rfl⟩ : syracuseStep 533159 = 799739) B799739
theorem B7709357 : Blo 354756 7709357 := bstep (se 3 (by rfl) ⟨1445504, by rfl⟩ : syracuseStep 7709357 = 2891009) B2891009
theorem B533279 : Blo 354756 533279 := bstep (se 1 (by rfl) ⟨399959, by rfl⟩ : syracuseStep 533279 = 799919) B799919
theorem B533303 : Blo 354756 533303 := bstep (se 1 (by rfl) ⟨399977, by rfl⟩ : syracuseStep 533303 = 799955) B799955
theorem B1352659 : Blo 354756 1352659 := bstep (se 1 (by rfl) ⟨1014494, by rfl⟩ : syracuseStep 1352659 = 2028989) B2028989
theorem B533483 : Blo 354756 533483 := bstep (se 1 (by rfl) ⟨400112, by rfl⟩ : syracuseStep 533483 = 800225) B800225
theorem B7742573 : Blo 354756 7742573 := bstep (se 3 (by rfl) ⟨1451732, by rfl⟩ : syracuseStep 7742573 = 2903465) B2903465
theorem B402655 : Blo 354756 402655 := bstep (se 1 (by rfl) ⟨301991, by rfl⟩ : syracuseStep 402655 = 603983) B603983
theorem B22258921 : Blo 354756 22258921 := bstep (se 2 (by rfl) ⟨8347095, by rfl⟩ : syracuseStep 22258921 = 16694191) B16694191
theorem B1811969 : Blo 354756 1811969 := bstep (se 2 (by rfl) ⟨679488, by rfl⟩ : syracuseStep 1811969 = 1358977) B1358977
theorem B403483 : Blo 354756 403483 := bstep (se 1 (by rfl) ⟨302612, by rfl⟩ : syracuseStep 403483 = 605225) B605225
theorem B534575 : Blo 354756 534575 := bstep (se 1 (by rfl) ⟨400931, by rfl⟩ : syracuseStep 534575 = 801863) B801863
theorem B20949137 : Blo 354756 20949137 := bstep (se 2 (by rfl) ⟨7855926, by rfl⟩ : syracuseStep 20949137 = 15711853) B15711853
theorem B1812779 : Blo 354756 1812779 := bstep (se 1 (by rfl) ⟨1359584, by rfl⟩ : syracuseStep 1812779 = 2719169) B2719169
theorem B534839 : Blo 354756 534839 := bstep (se 1 (by rfl) ⟨401129, by rfl⟩ : syracuseStep 534839 = 802259) B802259
theorem B535019 : Blo 354756 535019 := bstep (se 1 (by rfl) ⟨401264, by rfl⟩ : syracuseStep 535019 = 802529) B802529
theorem B1714769 : Blo 354756 1714769 := bstep (se 2 (by rfl) ⟨643038, by rfl⟩ : syracuseStep 1714769 = 1286077) B1286077
theorem B535721 : Blo 354756 535721 := bstep (se 2 (by rfl) ⟨200895, by rfl⟩ : syracuseStep 535721 = 401791) B401791
theorem B1518857 : Blo 354756 1518857 := bstep (se 2 (by rfl) ⟨569571, by rfl⟩ : syracuseStep 1518857 = 1139143) B1139143
theorem B961811 : Blo 354756 961811 := bstep (se 1 (by rfl) ⟨721358, by rfl⟩ : syracuseStep 961811 = 1442717) B1442717
theorem B601499 : Blo 354756 601499 := bstep (se 1 (by rfl) ⟨451124, by rfl⟩ : syracuseStep 601499 = 902249) B902249
theorem B536135 : Blo 354756 536135 := bstep (se 1 (by rfl) ⟨402101, by rfl⟩ : syracuseStep 536135 = 804203) B804203
theorem B798299 : Blo 354756 798299 := bstep (se 1 (by rfl) ⟨598724, by rfl⟩ : syracuseStep 798299 = 1197449) B1197449
theorem B536315 : Blo 354756 536315 := bstep (se 1 (by rfl) ⟨402236, by rfl⟩ : syracuseStep 536315 = 804473) B804473
theorem B2895749 : Blo 354756 2895749 := bstep (se 4 (by rfl) ⟨271476, by rfl⟩ : syracuseStep 2895749 = 542953) B542953
theorem B3092357 : Blo 354756 3092357 := bstep (se 4 (by rfl) ⟨289908, by rfl⟩ : syracuseStep 3092357 = 579817) B579817
theorem B1519555 : Blo 354756 1519555 := bstep (se 1 (by rfl) ⟨1139666, by rfl⟩ : syracuseStep 1519555 = 2279333) B2279333
theorem B798713 : Blo 354756 798713 := bstep (se 2 (by rfl) ⟨299517, by rfl⟩ : syracuseStep 798713 = 599035) B599035
theorem B798803 : Blo 354756 798803 := bstep (se 1 (by rfl) ⟨599102, by rfl⟩ : syracuseStep 798803 = 1198205) B1198205
theorem B602255 : Blo 354756 602255 := bstep (se 1 (by rfl) ⟨451691, by rfl⟩ : syracuseStep 602255 = 903383) B903383
theorem B798983 : Blo 354756 798983 := bstep (se 1 (by rfl) ⟨599237, by rfl⟩ : syracuseStep 798983 = 1198475) B1198475
theorem B602471 : Blo 354756 602471 := bstep (se 1 (by rfl) ⟨451853, by rfl⟩ : syracuseStep 602471 = 903707) B903707
theorem B536987 : Blo 354756 536987 := bstep (se 1 (by rfl) ⟨402740, by rfl⟩ : syracuseStep 536987 = 805481) B805481
theorem B799289 : Blo 354756 799289 := bstep (se 2 (by rfl) ⟨299733, by rfl⟩ : syracuseStep 799289 = 599467) B599467
theorem B537407 : Blo 354756 537407 := bstep (se 1 (by rfl) ⟨403055, by rfl⟩ : syracuseStep 537407 = 806111) B806111
theorem B1553215 : Blo 354756 1553215 := bstep (se 1 (by rfl) ⟨1164911, by rfl⟩ : syracuseStep 1553215 = 2329823) B2329823
theorem B537551 : Blo 354756 537551 := bstep (se 1 (by rfl) ⟨403163, by rfl⟩ : syracuseStep 537551 = 806327) B806327
theorem B537593 : Blo 354756 537593 := bstep (se 2 (by rfl) ⟨201597, by rfl⟩ : syracuseStep 537593 = 403195) B403195
theorem B537641 : Blo 354756 537641 := bstep (se 2 (by rfl) ⟨201615, by rfl⟩ : syracuseStep 537641 = 403231) B403231
theorem B537671 : Blo 354756 537671 := bstep (se 1 (by rfl) ⟨403253, by rfl⟩ : syracuseStep 537671 = 806507) B806507
theorem B1357019 : Blo 354756 1357019 := bstep (se 1 (by rfl) ⟨1017764, by rfl⟩ : syracuseStep 1357019 = 2035529) B2035529
theorem B537851 : Blo 354756 537851 := bstep (se 1 (by rfl) ⟨403388, by rfl⟩ : syracuseStep 537851 = 806777) B806777
theorem B800009 : Blo 354756 800009 := bstep (se 2 (by rfl) ⟨300003, by rfl⟩ : syracuseStep 800009 = 600007) B600007
theorem B800063 : Blo 354756 800063 := bstep (se 1 (by rfl) ⟨600047, by rfl⟩ : syracuseStep 800063 = 1200095) B1200095
theorem B800171 : Blo 354756 800171 := bstep (se 1 (by rfl) ⟨600128, by rfl⟩ : syracuseStep 800171 = 1200257) B1200257
theorem B2274925 : Blo 354756 2274925 := bstep (se 3 (by rfl) ⟨426548, by rfl⟩ : syracuseStep 2274925 = 853097) B853097
theorem B800495 : Blo 354756 800495 := bstep (se 1 (by rfl) ⟨600371, by rfl⟩ : syracuseStep 800495 = 1200743) B1200743
theorem B800711 : Blo 354756 800711 := bstep (se 1 (by rfl) ⟨600533, by rfl⟩ : syracuseStep 800711 = 1201067) B1201067
theorem B800999 : Blo 354756 800999 := bstep (se 1 (by rfl) ⟨600749, by rfl⟩ : syracuseStep 800999 = 1201499) B1201499
theorem B801017 : Blo 354756 801017 := bstep (se 2 (by rfl) ⟨300381, by rfl⟩ : syracuseStep 801017 = 600763) B600763
theorem B801071 : Blo 354756 801071 := bstep (se 1 (by rfl) ⟨600803, by rfl⟩ : syracuseStep 801071 = 1201607) B1201607
theorem B1358279 : Blo 354756 1358279 := bstep (se 1 (by rfl) ⟨1018709, by rfl⟩ : syracuseStep 1358279 = 2037419) B2037419
theorem B2275847 : Blo 354756 2275847 := bstep (se 1 (by rfl) ⟨1706885, by rfl⟩ : syracuseStep 2275847 = 3413771) B3413771
theorem B801287 : Blo 354756 801287 := bstep (se 1 (by rfl) ⟨600965, by rfl⟩ : syracuseStep 801287 = 1201931) B1201931
theorem B1718921 : Blo 354756 1718921 := bstep (se 2 (by rfl) ⟨644595, by rfl⟩ : syracuseStep 1718921 = 1289191) B1289191
theorem B801467 : Blo 354756 801467 := bstep (se 1 (by rfl) ⟨601100, by rfl⟩ : syracuseStep 801467 = 1202201) B1202201
theorem B604975 : Blo 354756 604975 := bstep (se 1 (by rfl) ⟨453731, by rfl⟩ : syracuseStep 604975 = 907463) B907463
theorem B59554739 : Blo 354756 59554739 := bstep (se 1 (by rfl) ⟨44666054, by rfl⟩ : syracuseStep 59554739 = 89332109) B89332109
theorem B2276873 : Blo 354756 2276873 := bstep (se 2 (by rfl) ⟨853827, by rfl⟩ : syracuseStep 2276873 = 1707655) B1707655
theorem B802367 : Blo 354756 802367 := bstep (se 1 (by rfl) ⟨601775, by rfl⟩ : syracuseStep 802367 = 1203551) B1203551
theorem B1359737 : Blo 354756 1359737 := bstep (se 2 (by rfl) ⟨509901, by rfl⟩ : syracuseStep 1359737 = 1019803) B1019803
theorem B802727 : Blo 354756 802727 := bstep (se 1 (by rfl) ⟨602045, by rfl⟩ : syracuseStep 802727 = 1204091) B1204091
theorem B2899901 : Blo 354756 2899901 := bstep (se 3 (by rfl) ⟨543731, by rfl⟩ : syracuseStep 2899901 = 1087463) B1087463
theorem B803051 : Blo 354756 803051 := bstep (se 1 (by rfl) ⟨602288, by rfl⟩ : syracuseStep 803051 = 1204577) B1204577
theorem B3850487 : Blo 354756 3850487 := bstep (se 1 (by rfl) ⟨2887865, by rfl⟩ : syracuseStep 3850487 = 5775731) B5775731
theorem B639593 : Blo 354756 639593 := bstep (se 2 (by rfl) ⟨239847, by rfl⟩ : syracuseStep 639593 = 479695) B479695
theorem B901793 : Blo 354756 901793 := bstep (se 2 (by rfl) ⟨338172, by rfl⟩ : syracuseStep 901793 = 676345) B676345
theorem B574139 : Blo 354756 574139 := bstep (se 1 (by rfl) ⟨430604, by rfl⟩ : syracuseStep 574139 = 861209) B861209
theorem B967735 : Blo 354756 967735 := bstep (se 1 (by rfl) ⟨725801, by rfl⟩ : syracuseStep 967735 = 1451603) B1451603
theorem B2278489 : Blo 354756 2278489 := bstep (se 2 (by rfl) ⟨854433, by rfl⟩ : syracuseStep 2278489 = 1708867) B1708867
theorem B803951 : Blo 354756 803951 := bstep (se 1 (by rfl) ⟨602963, by rfl⟩ : syracuseStep 803951 = 1205927) B1205927
theorem B2573477 : Blo 354756 2573477 := bstep (se 4 (by rfl) ⟨241263, by rfl⟩ : syracuseStep 2573477 = 482527) B482527
theorem B1164623 : Blo 354756 1164623 := bstep (se 1 (by rfl) ⟨873467, by rfl⟩ : syracuseStep 1164623 = 1746935) B1746935
theorem B6079859 : Blo 354756 6079859 := bstep (se 1 (by rfl) ⟨4559894, by rfl⟩ : syracuseStep 6079859 = 9119789) B9119789
theorem B1459613 : Blo 354756 1459613 := bstep (se 3 (by rfl) ⟨273677, by rfl⟩ : syracuseStep 1459613 = 547355) B547355
theorem B804347 : Blo 354756 804347 := bstep (se 1 (by rfl) ⟨603260, by rfl⟩ : syracuseStep 804347 = 1206521) B1206521
theorem B804383 : Blo 354756 804383 := bstep (se 1 (by rfl) ⟨603287, by rfl⟩ : syracuseStep 804383 = 1206575) B1206575
theorem B2278975 : Blo 354756 2278975 := bstep (se 1 (by rfl) ⟨1709231, by rfl⟩ : syracuseStep 2278975 = 3418463) B3418463
theorem B509503 : Blo 354756 509503 := bstep (se 1 (by rfl) ⟨382127, by rfl⟩ : syracuseStep 509503 = 764255) B764255
theorem B968363 : Blo 354756 968363 := bstep (se 1 (by rfl) ⟨726272, by rfl⟩ : syracuseStep 968363 = 1452545) B1452545
theorem B804527 : Blo 354756 804527 := bstep (se 1 (by rfl) ⟨603395, by rfl⟩ : syracuseStep 804527 = 1206791) B1206791
theorem B1361879 : Blo 354756 1361879 := bstep (se 1 (by rfl) ⟨1021409, by rfl⟩ : syracuseStep 1361879 = 2042819) B2042819
theorem B378847 : Blo 354756 378847 := bstep (se 1 (by rfl) ⟨284135, by rfl⟩ : syracuseStep 378847 = 568271) B568271
theorem B804959 : Blo 354756 804959 := bstep (se 1 (by rfl) ⟨603719, by rfl⟩ : syracuseStep 804959 = 1207439) B1207439
theorem B510175 : Blo 354756 510175 := bstep (se 1 (by rfl) ⟨382631, by rfl⟩ : syracuseStep 510175 = 765263) B765263
theorem B674075 : Blo 354756 674075 := bstep (se 1 (by rfl) ⟨505556, by rfl⟩ : syracuseStep 674075 = 1011113) B1011113
theorem B805247 : Blo 354756 805247 := bstep (se 1 (by rfl) ⟨603935, by rfl⟩ : syracuseStep 805247 = 1207871) B1207871
theorem B2574919 : Blo 354756 2574919 := bstep (se 1 (by rfl) ⟨1931189, by rfl⟩ : syracuseStep 2574919 = 3862379) B3862379
theorem B805715 : Blo 354756 805715 := bstep (se 1 (by rfl) ⟨604286, by rfl⟩ : syracuseStep 805715 = 1208573) B1208573
theorem B1657705 : Blo 354756 1657705 := bstep (se 2 (by rfl) ⟨621639, by rfl⟩ : syracuseStep 1657705 = 1243279) B1243279
theorem B1723265 : Blo 354756 1723265 := bstep (se 2 (by rfl) ⟨646224, by rfl⟩ : syracuseStep 1723265 = 1292449) B1292449
theorem B642043 : Blo 354756 642043 := bstep (se 1 (by rfl) ⟨481532, by rfl⟩ : syracuseStep 642043 = 963065) B963065
theorem B3034259 : Blo 354756 3034259 := bstep (se 1 (by rfl) ⟨2275694, by rfl⟩ : syracuseStep 3034259 = 4551389) B4551389
theorem B806075 : Blo 354756 806075 := bstep (se 1 (by rfl) ⟨604556, by rfl⟩ : syracuseStep 806075 = 1209113) B1209113
theorem B806255 : Blo 354756 806255 := bstep (se 1 (by rfl) ⟨604691, by rfl⟩ : syracuseStep 806255 = 1209383) B1209383
theorem B6540907 : Blo 354756 6540907 := bstep (se 1 (by rfl) ⟨4905680, by rfl⟩ : syracuseStep 6540907 = 9811361) B9811361
theorem B806975 : Blo 354756 806975 := bstep (se 1 (by rfl) ⟨605231, by rfl⟩ : syracuseStep 806975 = 1210463) B1210463
theorem B675935 : Blo 354756 675935 := bstep (se 1 (by rfl) ⟨506951, by rfl⟩ : syracuseStep 675935 = 1013903) B1013903
theorem B3461453 : Blo 354756 3461453 := bstep (se 3 (by rfl) ⟨649022, by rfl⟩ : syracuseStep 3461453 = 1298045) B1298045
theorem B2576765 : Blo 354756 2576765 := bstep (se 3 (by rfl) ⟨483143, by rfl⟩ : syracuseStep 2576765 = 966287) B966287
theorem B1626763 : Blo 354756 1626763 := bstep (se 1 (by rfl) ⟨1220072, by rfl⟩ : syracuseStep 1626763 = 2440145) B2440145
theorem B1201121 : Blo 354756 1201121 := bstep (se 2 (by rfl) ⟨450420, by rfl⟩ : syracuseStep 1201121 = 900841) B900841
theorem B1135603 : Blo 354756 1135603 := bstep (se 1 (by rfl) ⟨851702, by rfl⟩ : syracuseStep 1135603 = 1703405) B1703405
theorem B24728615 : Blo 354756 24728615 := bstep (se 1 (by rfl) ⟨18546461, by rfl⟩ : syracuseStep 24728615 = 37092923) B37092923
theorem B677879 : Blo 354756 677879 := bstep (se 1 (by rfl) ⟨508409, by rfl⟩ : syracuseStep 677879 = 1016819) B1016819
theorem B678107 : Blo 354756 678107 := bstep (se 1 (by rfl) ⟨508580, by rfl⟩ : syracuseStep 678107 = 1017161) B1017161
theorem B907483 : Blo 354756 907483 := bstep (se 1 (by rfl) ⟨680612, by rfl⟩ : syracuseStep 907483 = 1361225) B1361225
theorem B6510905 : Blo 354756 6510905 := bstep (se 2 (by rfl) ⟨2441589, by rfl⟩ : syracuseStep 6510905 = 4883179) B4883179
theorem B2709935 : Blo 354756 2709935 := bstep (se 1 (by rfl) ⟨2032451, by rfl⟩ : syracuseStep 2709935 = 4064903) B4064903
theorem B580409 : Blo 354756 580409 := bstep (se 2 (by rfl) ⟨217653, by rfl⟩ : syracuseStep 580409 = 435307) B435307
theorem B679033 : Blo 354756 679033 := bstep (se 2 (by rfl) ⟨254637, by rfl⟩ : syracuseStep 679033 = 509275) B509275
theorem B3431609 : Blo 354756 3431609 := bstep (se 2 (by rfl) ⟨1286853, by rfl⟩ : syracuseStep 3431609 = 2573707) B2573707
theorem B4120001 : Blo 354756 4120001 := bstep (se 2 (by rfl) ⟨1545000, by rfl⟩ : syracuseStep 4120001 = 3090001) B3090001
theorem B23092775 : Blo 354756 23092775 := bstep (se 1 (by rfl) ⟨17319581, by rfl⟩ : syracuseStep 23092775 = 34639163) B34639163
theorem B3301073 : Blo 354756 3301073 := bstep (se 2 (by rfl) ⟨1237902, by rfl⟩ : syracuseStep 3301073 = 2475805) B2475805
theorem B3432223 : Blo 354756 3432223 := bstep (se 1 (by rfl) ⟨2574167, by rfl⟩ : syracuseStep 3432223 = 5148335) B5148335
theorem B6119225 : Blo 354756 6119225 := bstep (se 2 (by rfl) ⟨2294709, by rfl⟩ : syracuseStep 6119225 = 4589419) B4589419
theorem B1138835 : Blo 354756 1138835 := bstep (se 1 (by rfl) ⟨854126, by rfl⟩ : syracuseStep 1138835 = 1708253) B1708253
theorem B451099 : Blo 354756 451099 := bstep (se 1 (by rfl) ⟨338324, by rfl⟩ : syracuseStep 451099 = 676649) B676649
theorem B18834221 : Blo 354756 18834221 := bstep (se 3 (by rfl) ⟨3531416, by rfl⟩ : syracuseStep 18834221 = 7062833) B7062833
theorem B2025071 : Blo 354756 2025071 := bstep (se 1 (by rfl) ⟨1518803, by rfl⟩ : syracuseStep 2025071 = 3037607) B3037607
theorem B1140475 : Blo 354756 1140475 := bstep (se 1 (by rfl) ⟨855356, by rfl⟩ : syracuseStep 1140475 = 1710713) B1710713
theorem B1206035 : Blo 354756 1206035 := bstep (se 1 (by rfl) ⟨904526, by rfl⟩ : syracuseStep 1206035 = 1809053) B1809053
theorem B1206251 : Blo 354756 1206251 := bstep (se 1 (by rfl) ⟨904688, by rfl⟩ : syracuseStep 1206251 = 1809377) B1809377
theorem B977039 : Blo 354756 977039 := bstep (se 1 (by rfl) ⟨732779, by rfl⟩ : syracuseStep 977039 = 1465559) B1465559
theorem B27781325 : Blo 354756 27781325 := bstep (se 3 (by rfl) ⟨5208998, by rfl⟩ : syracuseStep 27781325 = 10417997) B10417997
theorem B354863 : Blo 354756 354863 := bstep (se 1 (by rfl) ⟨266147, by rfl⟩ : syracuseStep 354863 = 532295) B532295
theorem B354919 : Blo 354756 354919 := bstep (se 1 (by rfl) ⟨266189, by rfl⟩ : syracuseStep 354919 = 532379) B532379
theorem B355295 : Blo 354756 355295 := bstep (se 1 (by rfl) ⟨266471, by rfl⟩ : syracuseStep 355295 = 532943) B532943
theorem B355323 : Blo 354756 355323 := bstep (se 1 (by rfl) ⟨266492, by rfl⟩ : syracuseStep 355323 = 532985) B532985
theorem B355391 : Blo 354756 355391 := bstep (se 1 (by rfl) ⟨266543, by rfl⟩ : syracuseStep 355391 = 533087) B533087
theorem B355711 : Blo 354756 355711 := bstep (se 1 (by rfl) ⟨266783, by rfl⟩ : syracuseStep 355711 = 533567) B533567
theorem B355739 : Blo 354756 355739 := bstep (se 1 (by rfl) ⟨266804, by rfl⟩ : syracuseStep 355739 = 533609) B533609
theorem B1207763 : Blo 354756 1207763 := bstep (se 1 (by rfl) ⟨905822, by rfl⟩ : syracuseStep 1207763 = 1811645) B1811645
theorem B355807 : Blo 354756 355807 := bstep (se 1 (by rfl) ⟨266855, by rfl⟩ : syracuseStep 355807 = 533711) B533711
theorem B355943 : Blo 354756 355943 := bstep (se 1 (by rfl) ⟨266957, by rfl⟩ : syracuseStep 355943 = 533915) B533915
theorem B1208033 : Blo 354756 1208033 := bstep (se 2 (by rfl) ⟨453012, by rfl⟩ : syracuseStep 1208033 = 906025) B906025
theorem B356091 : Blo 354756 356091 := bstep (se 1 (by rfl) ⟨267068, by rfl⟩ : syracuseStep 356091 = 534137) B534137
theorem B356159 : Blo 354756 356159 := bstep (se 1 (by rfl) ⟨267119, by rfl⟩ : syracuseStep 356159 = 534239) B534239
theorem B356223 : Blo 354756 356223 := bstep (se 1 (by rfl) ⟨267167, by rfl⟩ : syracuseStep 356223 = 534335) B534335
theorem B356335 : Blo 354756 356335 := bstep (se 1 (by rfl) ⟨267251, by rfl⟩ : syracuseStep 356335 = 534503) B534503
theorem B356347 : Blo 354756 356347 := bstep (se 1 (by rfl) ⟨267260, by rfl⟩ : syracuseStep 356347 = 534521) B534521
theorem B356415 : Blo 354756 356415 := bstep (se 1 (by rfl) ⟨267311, by rfl⟩ : syracuseStep 356415 = 534623) B534623
theorem B356455 : Blo 354756 356455 := bstep (se 1 (by rfl) ⟨267341, by rfl⟩ : syracuseStep 356455 = 534683) B534683
theorem B356479 : Blo 354756 356479 := bstep (se 1 (by rfl) ⟨267359, by rfl⟩ : syracuseStep 356479 = 534719) B534719
theorem B356507 : Blo 354756 356507 := bstep (se 1 (by rfl) ⟨267380, by rfl⟩ : syracuseStep 356507 = 534761) B534761
theorem B5796029 : Blo 354756 5796029 := bstep (se 3 (by rfl) ⟨1086755, by rfl⟩ : syracuseStep 5796029 = 2173511) B2173511
theorem B6844763 : Blo 354756 6844763 := bstep (se 1 (by rfl) ⟨5133572, by rfl⟩ : syracuseStep 6844763 = 10267145) B10267145
theorem B356711 : Blo 354756 356711 := bstep (se 1 (by rfl) ⟨267533, by rfl⟩ : syracuseStep 356711 = 535067) B535067
theorem B356763 : Blo 354756 356763 := bstep (se 1 (by rfl) ⟨267572, by rfl⟩ : syracuseStep 356763 = 535145) B535145
theorem B357115 : Blo 354756 357115 := bstep (se 1 (by rfl) ⟨267836, by rfl⟩ : syracuseStep 357115 = 535673) B535673
theorem B357183 : Blo 354756 357183 := bstep (se 1 (by rfl) ⟨267887, by rfl⟩ : syracuseStep 357183 = 535775) B535775
theorem B357211 : Blo 354756 357211 := bstep (se 1 (by rfl) ⟨267908, by rfl⟩ : syracuseStep 357211 = 535817) B535817
theorem B357279 : Blo 354756 357279 := bstep (se 1 (by rfl) ⟨267959, by rfl⟩ : syracuseStep 357279 = 535919) B535919
theorem B357359 : Blo 354756 357359 := bstep (se 1 (by rfl) ⟨268019, by rfl⟩ : syracuseStep 357359 = 536039) B536039
theorem B357447 : Blo 354756 357447 := bstep (se 1 (by rfl) ⟨268085, by rfl⟩ : syracuseStep 357447 = 536171) B536171
theorem B357531 : Blo 354756 357531 := bstep (se 1 (by rfl) ⟨268148, by rfl⟩ : syracuseStep 357531 = 536297) B536297
theorem B357627 : Blo 354756 357627 := bstep (se 1 (by rfl) ⟨268220, by rfl⟩ : syracuseStep 357627 = 536441) B536441
theorem B1439005 : Blo 354756 1439005 := bstep (se 3 (by rfl) ⟨269813, by rfl⟩ : syracuseStep 1439005 = 539627) B539627
theorem B357695 : Blo 354756 357695 := bstep (se 1 (by rfl) ⟨268271, by rfl⟩ : syracuseStep 357695 = 536543) B536543
theorem B1439147 : Blo 354756 1439147 := bstep (se 1 (by rfl) ⟨1079360, by rfl⟩ : syracuseStep 1439147 = 2158721) B2158721
theorem B1209815 : Blo 354756 1209815 := bstep (se 1 (by rfl) ⟨907361, by rfl⟩ : syracuseStep 1209815 = 1814723) B1814723
theorem B357863 : Blo 354756 357863 := bstep (se 1 (by rfl) ⟨268397, by rfl⟩ : syracuseStep 357863 = 536795) B536795
theorem B357871 : Blo 354756 357871 := bstep (se 1 (by rfl) ⟨268403, by rfl⟩ : syracuseStep 357871 = 536807) B536807
theorem B357979 : Blo 354756 357979 := bstep (se 1 (by rfl) ⟨268484, by rfl⟩ : syracuseStep 357979 = 536969) B536969
theorem B358043 : Blo 354756 358043 := bstep (se 1 (by rfl) ⟨268532, by rfl⟩ : syracuseStep 358043 = 537065) B537065
theorem B358127 : Blo 354756 358127 := bstep (se 1 (by rfl) ⟨268595, by rfl⟩ : syracuseStep 358127 = 537191) B537191
theorem B358215 : Blo 354756 358215 := bstep (se 1 (by rfl) ⟨268661, by rfl⟩ : syracuseStep 358215 = 537323) B537323
theorem B358235 : Blo 354756 358235 := bstep (se 1 (by rfl) ⟨268676, by rfl⟩ : syracuseStep 358235 = 537353) B537353
theorem B358303 : Blo 354756 358303 := bstep (se 1 (by rfl) ⟨268727, by rfl⟩ : syracuseStep 358303 = 537455) B537455
theorem B358471 : Blo 354756 358471 := bstep (se 1 (by rfl) ⟨268853, by rfl⟩ : syracuseStep 358471 = 537707) B537707
theorem B1439927 : Blo 354756 1439927 := bstep (se 1 (by rfl) ⟨1079945, by rfl⟩ : syracuseStep 1439927 = 2159891) B2159891
theorem B1013971 : Blo 354756 1013971 := bstep (se 1 (by rfl) ⟨760478, by rfl⟩ : syracuseStep 1013971 = 1520957) B1520957
theorem B358631 : Blo 354756 358631 := bstep (se 1 (by rfl) ⟨268973, by rfl⟩ : syracuseStep 358631 = 537947) B537947
theorem B6846767 : Blo 354756 6846767 := bstep (se 1 (by rfl) ⟨5135075, by rfl⟩ : syracuseStep 6846767 = 10270151) B10270151
theorem B13826419 : Blo 354756 13826419 := bstep (se 1 (by rfl) ⟨10369814, by rfl⟩ : syracuseStep 13826419 = 20739629) B20739629
theorem B3242537 : Blo 354756 3242537 := bstep (se 2 (by rfl) ⟨1215951, by rfl⟩ : syracuseStep 3242537 = 2431903) B2431903
theorem B916073 : Blo 354756 916073 := bstep (se 2 (by rfl) ⟨343527, by rfl⟩ : syracuseStep 916073 = 687055) B687055
theorem B2030629 : Blo 354756 2030629 := bstep (se 4 (by rfl) ⟨190371, by rfl⟩ : syracuseStep 2030629 = 380743) B380743
theorem B2849869 : Blo 354756 2849869 := bstep (se 3 (by rfl) ⟨534350, by rfl⟩ : syracuseStep 2849869 = 1068701) B1068701
theorem B1015247 : Blo 354756 1015247 := bstep (se 1 (by rfl) ⟨761435, by rfl⟩ : syracuseStep 1015247 = 1522871) B1522871
theorem B426395 : Blo 354756 426395 := bstep (se 1 (by rfl) ⟨319796, by rfl⟩ : syracuseStep 426395 = 639593) B639593
theorem B2032087 : Blo 354756 2032087 := bstep (se 1 (by rfl) ⟨1524065, by rfl⟩ : syracuseStep 2032087 = 3048131) B3048131
theorem B3867095 : Blo 354756 3867095 := bstep (se 1 (by rfl) ⟨2900321, by rfl⟩ : syracuseStep 3867095 = 5800643) B5800643
theorem B1803545 : Blo 354756 1803545 := bstep (se 2 (by rfl) ⟨676329, by rfl⟩ : syracuseStep 1803545 = 1352659) B1352659
theorem B3409775 : Blo 354756 3409775 := bstep (se 1 (by rfl) ⟨2557331, by rfl⟩ : syracuseStep 3409775 = 5114663) B5114663
theorem B1148843 : Blo 354756 1148843 := bstep (se 1 (by rfl) ⟨861632, by rfl⟩ : syracuseStep 1148843 = 1723265) B1723265
theorem B854155 : Blo 354756 854155 := bstep (se 1 (by rfl) ⟨640616, by rfl⟩ : syracuseStep 854155 = 1281233) B1281233
theorem B4589783 : Blo 354756 4589783 := bstep (se 1 (by rfl) ⟨3442337, by rfl⟩ : syracuseStep 4589783 = 6884675) B6884675
theorem B4197203 : Blo 354756 4197203 := bstep (se 1 (by rfl) ⟨3147902, by rfl⟩ : syracuseStep 4197203 = 6295805) B6295805
theorem B16485743 : Blo 354756 16485743 := bstep (se 1 (by rfl) ⟨12364307, by rfl⟩ : syracuseStep 16485743 = 24728615) B24728615
theorem B3837725 : Blo 354756 3837725 := bstep (se 3 (by rfl) ⟨719573, by rfl⟩ : syracuseStep 3837725 = 1439147) B1439147
theorem B856057 : Blo 354756 856057 := bstep (se 2 (by rfl) ⟨321021, by rfl⟩ : syracuseStep 856057 = 642043) B642043
theorem B856327 : Blo 354756 856327 := bstep (se 1 (by rfl) ⟨642245, by rfl⟩ : syracuseStep 856327 = 1284491) B1284491
theorem B1806623 : Blo 354756 1806623 := bstep (se 1 (by rfl) ⟨1354967, by rfl⟩ : syracuseStep 1806623 = 2709935) B2709935
theorem B8721209 : Blo 354756 8721209 := bstep (se 2 (by rfl) ⟨3270453, by rfl⟩ : syracuseStep 8721209 = 6540907) B6540907
theorem B2200715 : Blo 354756 2200715 := bstep (se 1 (by rfl) ⟨1650536, by rfl⟩ : syracuseStep 2200715 = 3301073) B3301073
theorem B759223 : Blo 354756 759223 := bstep (se 1 (by rfl) ⟨569417, by rfl⟩ : syracuseStep 759223 = 1138835) B1138835
theorem B12556147 : Blo 354756 12556147 := bstep (se 1 (by rfl) ⟨9417110, by rfl⟩ : syracuseStep 12556147 = 18834221) B18834221
theorem B2169017 : Blo 354756 2169017 := bstep (se 2 (by rfl) ⟨813381, by rfl⟩ : syracuseStep 2169017 = 1626763) B1626763
theorem B1350047 : Blo 354756 1350047 := bstep (se 1 (by rfl) ⟨1012535, by rfl⟩ : syracuseStep 1350047 = 2025071) B2025071
theorem B2070953 : Blo 354756 2070953 := bstep (se 2 (by rfl) ⟨776607, by rfl⟩ : syracuseStep 2070953 = 1553215) B1553215
theorem B1448489 : Blo 354756 1448489 := bstep (se 2 (by rfl) ⟨543183, by rfl⟩ : syracuseStep 1448489 = 1086367) B1086367
theorem B1514137 : Blo 354756 1514137 := bstep (se 2 (by rfl) ⟨567801, by rfl⟩ : syracuseStep 1514137 = 1135603) B1135603
theorem B13966091 : Blo 354756 13966091 := bstep (se 1 (by rfl) ⟨10474568, by rfl⟩ : syracuseStep 13966091 = 20949137) B20949137
theorem B18520883 : Blo 354756 18520883 := bstep (se 1 (by rfl) ⟨13890662, by rfl⟩ : syracuseStep 18520883 = 27781325) B27781325
theorem B400999 : Blo 354756 400999 := bstep (se 1 (by rfl) ⟨300749, by rfl⟩ : syracuseStep 400999 = 601499) B601499
theorem B532199 : Blo 354756 532199 := bstep (se 1 (by rfl) ⟨399149, by rfl⟩ : syracuseStep 532199 = 798299) B798299
theorem B532475 : Blo 354756 532475 := bstep (se 1 (by rfl) ⟨399356, by rfl⟩ : syracuseStep 532475 = 798713) B798713
theorem B532535 : Blo 354756 532535 := bstep (se 1 (by rfl) ⟨399401, by rfl⟩ : syracuseStep 532535 = 798803) B798803
theorem B401503 : Blo 354756 401503 := bstep (se 1 (by rfl) ⟨301127, by rfl⟩ : syracuseStep 401503 = 602255) B602255
theorem B4858001 : Blo 354756 4858001 := bstep (se 2 (by rfl) ⟨1821750, by rfl⟩ : syracuseStep 4858001 = 3643501) B3643501
theorem B532655 : Blo 354756 532655 := bstep (se 1 (by rfl) ⟨399491, by rfl⟩ : syracuseStep 532655 = 798983) B798983
theorem B4563175 : Blo 354756 4563175 := bstep (se 1 (by rfl) ⟨3422381, by rfl⟩ : syracuseStep 4563175 = 6844763) B6844763
theorem B401647 : Blo 354756 401647 := bstep (se 1 (by rfl) ⟨301235, by rfl⟩ : syracuseStep 401647 = 602471) B602471
theorem B1351961 : Blo 354756 1351961 := bstep (se 2 (by rfl) ⟨506985, by rfl⟩ : syracuseStep 1351961 = 1013971) B1013971
theorem B532859 : Blo 354756 532859 := bstep (se 1 (by rfl) ⟨399644, by rfl⟩ : syracuseStep 532859 = 799289) B799289
theorem B533033 : Blo 354756 533033 := bstep (se 2 (by rfl) ⟨199887, by rfl⟩ : syracuseStep 533033 = 399775) B399775
theorem B533129 : Blo 354756 533129 := bstep (se 2 (by rfl) ⟨199923, by rfl⟩ : syracuseStep 533129 = 399847) B399847
theorem B533339 : Blo 354756 533339 := bstep (se 1 (by rfl) ⟨400004, by rfl⟩ : syracuseStep 533339 = 800009) B800009
theorem B533375 : Blo 354756 533375 := bstep (se 1 (by rfl) ⟨400031, by rfl⟩ : syracuseStep 533375 = 800063) B800063
theorem B533447 : Blo 354756 533447 := bstep (se 1 (by rfl) ⟨400085, by rfl⟩ : syracuseStep 533447 = 800171) B800171
theorem B533663 : Blo 354756 533663 := bstep (se 1 (by rfl) ⟨400247, by rfl⟩ : syracuseStep 533663 = 800495) B800495
theorem B533807 : Blo 354756 533807 := bstep (se 1 (by rfl) ⟨400355, by rfl⟩ : syracuseStep 533807 = 800711) B800711
theorem B959951 : Blo 354756 959951 := bstep (se 1 (by rfl) ⟨719963, by rfl⟩ : syracuseStep 959951 = 1439927) B1439927
theorem B533999 : Blo 354756 533999 := bstep (se 1 (by rfl) ⟨400499, by rfl⟩ : syracuseStep 533999 = 800999) B800999
theorem B534011 : Blo 354756 534011 := bstep (se 1 (by rfl) ⟨400508, by rfl⟩ : syracuseStep 534011 = 801017) B801017
theorem B534047 : Blo 354756 534047 := bstep (se 1 (by rfl) ⟨400535, by rfl⟩ : syracuseStep 534047 = 801071) B801071
theorem B4564511 : Blo 354756 4564511 := bstep (se 1 (by rfl) ⟨3423383, by rfl⟩ : syracuseStep 4564511 = 6846767) B6846767
theorem B1517231 : Blo 354756 1517231 := bstep (se 1 (by rfl) ⟨1137923, by rfl⟩ : syracuseStep 1517231 = 2275847) B2275847
theorem B534191 : Blo 354756 534191 := bstep (se 1 (by rfl) ⟨400643, by rfl⟩ : syracuseStep 534191 = 801287) B801287
theorem B534281 : Blo 354756 534281 := bstep (se 2 (by rfl) ⟨200355, by rfl⟩ : syracuseStep 534281 = 400711) B400711
theorem B534311 : Blo 354756 534311 := bstep (se 1 (by rfl) ⟨400733, by rfl⟩ : syracuseStep 534311 = 801467) B801467
theorem B1517915 : Blo 354756 1517915 := bstep (se 1 (by rfl) ⟨1138436, by rfl⟩ : syracuseStep 1517915 = 2276873) B2276873
theorem B534911 : Blo 354756 534911 := bstep (se 1 (by rfl) ⟨401183, by rfl⟩ : syracuseStep 534911 = 802367) B802367
theorem B535151 : Blo 354756 535151 := bstep (se 1 (by rfl) ⟨401363, by rfl⟩ : syracuseStep 535151 = 802727) B802727
theorem B535367 : Blo 354756 535367 := bstep (se 1 (by rfl) ⟨401525, by rfl⟩ : syracuseStep 535367 = 803051) B803051
theorem B2566991 : Blo 354756 2566991 := bstep (se 1 (by rfl) ⟨1925243, by rfl⟩ : syracuseStep 2566991 = 3850487) B3850487
theorem B601195 : Blo 354756 601195 := bstep (se 1 (by rfl) ⟨450896, by rfl⟩ : syracuseStep 601195 = 901793) B901793
theorem B601465 : Blo 354756 601465 := bstep (se 2 (by rfl) ⟨225549, by rfl⟩ : syracuseStep 601465 = 451099) B451099
theorem B535967 : Blo 354756 535967 := bstep (se 1 (by rfl) ⟨401975, by rfl⟩ : syracuseStep 535967 = 803951) B803951
theorem B1715651 : Blo 354756 1715651 := bstep (se 1 (by rfl) ⟨1286738, by rfl⟩ : syracuseStep 1715651 = 2573477) B2573477
theorem B568937 : Blo 354756 568937 := bstep (se 2 (by rfl) ⟨213351, by rfl⟩ : syracuseStep 568937 = 426703) B426703
theorem B1945223 : Blo 354756 1945223 := bstep (se 1 (by rfl) ⟨1458917, by rfl⟩ : syracuseStep 1945223 = 2917835) B2917835
theorem B536231 : Blo 354756 536231 := bstep (se 1 (by rfl) ⟨402173, by rfl⟩ : syracuseStep 536231 = 804347) B804347
theorem B536255 : Blo 354756 536255 := bstep (se 1 (by rfl) ⟨402191, by rfl⟩ : syracuseStep 536255 = 804383) B804383
theorem B536351 : Blo 354756 536351 := bstep (se 1 (by rfl) ⟨402263, by rfl⟩ : syracuseStep 536351 = 804527) B804527
theorem B7712819 : Blo 354756 7712819 := bstep (se 1 (by rfl) ⟨5784614, by rfl⟩ : syracuseStep 7712819 = 11569229) B11569229
theorem B536639 : Blo 354756 536639 := bstep (se 1 (by rfl) ⟨402479, by rfl⟩ : syracuseStep 536639 = 804959) B804959
theorem B1290313 : Blo 354756 1290313 := bstep (se 2 (by rfl) ⟨483867, by rfl⟩ : syracuseStep 1290313 = 967735) B967735
theorem B536831 : Blo 354756 536831 := bstep (se 1 (by rfl) ⟨402623, by rfl⟩ : syracuseStep 536831 = 805247) B805247
theorem B536873 : Blo 354756 536873 := bstep (se 2 (by rfl) ⟨201327, by rfl⟩ : syracuseStep 536873 = 402655) B402655
theorem B569911 : Blo 354756 569911 := bstep (se 1 (by rfl) ⟨427433, by rfl⟩ : syracuseStep 569911 = 854867) B854867
theorem B537143 : Blo 354756 537143 := bstep (se 1 (by rfl) ⟨402857, by rfl⟩ : syracuseStep 537143 = 805715) B805715
theorem B73740901 : Blo 354756 73740901 := bstep (se 4 (by rfl) ⟨6913209, by rfl⟩ : syracuseStep 73740901 = 13826419) B13826419
theorem B537383 : Blo 354756 537383 := bstep (se 1 (by rfl) ⟨403037, by rfl⟩ : syracuseStep 537383 = 806075) B806075
theorem B570167 : Blo 354756 570167 := bstep (se 1 (by rfl) ⟨427625, by rfl⟩ : syracuseStep 570167 = 855251) B855251
theorem B537503 : Blo 354756 537503 := bstep (se 1 (by rfl) ⟨403127, by rfl⟩ : syracuseStep 537503 = 806255) B806255
theorem B1520633 : Blo 354756 1520633 := bstep (se 2 (by rfl) ⟨570237, by rfl⟩ : syracuseStep 1520633 = 1140475) B1140475
theorem B505129 : Blo 354756 505129 := bstep (se 2 (by rfl) ⟨189423, by rfl⟩ : syracuseStep 505129 = 378847) B378847
theorem B537977 : Blo 354756 537977 := bstep (se 2 (by rfl) ⟨201741, by rfl⟩ : syracuseStep 537977 = 403483) B403483
theorem B537983 : Blo 354756 537983 := bstep (se 1 (by rfl) ⟨403487, by rfl⟩ : syracuseStep 537983 = 806975) B806975
theorem B1816019 : Blo 354756 1816019 := bstep (se 1 (by rfl) ⟨1362014, by rfl⟩ : syracuseStep 1816019 = 2724029) B2724029
theorem B2307635 : Blo 354756 2307635 := bstep (se 1 (by rfl) ⟨1730726, by rfl⟩ : syracuseStep 2307635 = 3461453) B3461453
theorem B1717843 : Blo 354756 1717843 := bstep (se 1 (by rfl) ⟨1288382, by rfl⟩ : syracuseStep 1717843 = 2576765) B2576765
theorem B4044491 : Blo 354756 4044491 := bstep (se 1 (by rfl) ⟨3033368, by rfl⟩ : syracuseStep 4044491 = 6066737) B6066737
theorem B1357519 : Blo 354756 1357519 := bstep (se 1 (by rfl) ⟨1018139, by rfl⟩ : syracuseStep 1357519 = 2036279) B2036279
theorem B571295 : Blo 354756 571295 := bstep (se 1 (by rfl) ⟨428471, by rfl⟩ : syracuseStep 571295 = 856943) B856943
theorem B800747 : Blo 354756 800747 := bstep (se 1 (by rfl) ⟨600560, by rfl⟩ : syracuseStep 800747 = 1201121) B1201121
theorem B571679 : Blo 354756 571679 := bstep (se 1 (by rfl) ⟨428759, by rfl⟩ : syracuseStep 571679 = 857519) B857519
theorem B2210273 : Blo 354756 2210273 := bstep (se 2 (by rfl) ⟨828852, by rfl⟩ : syracuseStep 2210273 = 1657705) B1657705
theorem B1161971 : Blo 354756 1161971 := bstep (se 1 (by rfl) ⟨871478, by rfl⟩ : syracuseStep 1161971 = 1742957) B1742957
theorem B4340603 : Blo 354756 4340603 := bstep (se 1 (by rfl) ⟨3255452, by rfl⟩ : syracuseStep 4340603 = 6510905) B6510905
theorem B2276257 : Blo 354756 2276257 := bstep (se 2 (by rfl) ⟨853596, by rfl⟩ : syracuseStep 2276257 = 1707193) B1707193
theorem B4079483 : Blo 354756 4079483 := bstep (se 1 (by rfl) ⟨3059612, by rfl⟩ : syracuseStep 4079483 = 6119225) B6119225
theorem B901327 : Blo 354756 901327 := bstep (se 1 (by rfl) ⟨675995, by rfl⟩ : syracuseStep 901327 = 1351991) B1351991
theorem B5161715 : Blo 354756 5161715 := bstep (se 1 (by rfl) ⟨3871286, by rfl⟩ : syracuseStep 5161715 = 7742573) B7742573
theorem B804023 : Blo 354756 804023 := bstep (se 1 (by rfl) ⟨603017, by rfl⟩ : syracuseStep 804023 = 1206035) B1206035
theorem B804167 : Blo 354756 804167 := bstep (se 1 (by rfl) ⟨603125, by rfl⟩ : syracuseStep 804167 = 1206251) B1206251
theorem B19449497 : Blo 354756 19449497 := bstep (se 2 (by rfl) ⟨7293561, by rfl⟩ : syracuseStep 19449497 = 14587123) B14587123
theorem B1918673 : Blo 354756 1918673 := bstep (se 2 (by rfl) ⟨719502, by rfl⟩ : syracuseStep 1918673 = 1439005) B1439005
theorem B3033233 : Blo 354756 3033233 := bstep (se 2 (by rfl) ⟨1137462, by rfl⟩ : syracuseStep 3033233 = 2274925) B2274925
theorem B641207 : Blo 354756 641207 := bstep (se 1 (by rfl) ⟨480905, by rfl⟩ : syracuseStep 641207 = 961811) B961811
theorem B805175 : Blo 354756 805175 := bstep (se 1 (by rfl) ⟨603881, by rfl⟩ : syracuseStep 805175 = 1207763) B1207763
theorem B805355 : Blo 354756 805355 := bstep (se 1 (by rfl) ⟨604016, by rfl⟩ : syracuseStep 805355 = 1208033) B1208033
theorem B904679 : Blo 354756 904679 := bstep (se 1 (by rfl) ⟨678509, by rfl⟩ : syracuseStep 904679 = 1357019) B1357019
theorem B806543 : Blo 354756 806543 := bstep (se 1 (by rfl) ⟨604907, by rfl⟩ : syracuseStep 806543 = 1209815) B1209815
theorem B806633 : Blo 354756 806633 := bstep (se 2 (by rfl) ⟨302487, by rfl⟩ : syracuseStep 806633 = 604975) B604975
theorem B2707505 : Blo 354756 2707505 := bstep (se 2 (by rfl) ⟨1015314, by rfl⟩ : syracuseStep 2707505 = 2030629) B2030629
theorem B905377 : Blo 354756 905377 := bstep (se 2 (by rfl) ⟨339516, by rfl⟩ : syracuseStep 905377 = 679033) B679033
theorem B905519 : Blo 354756 905519 := bstep (se 1 (by rfl) ⟨679139, by rfl⟩ : syracuseStep 905519 = 1358279) B1358279
theorem B610715 : Blo 354756 610715 := bstep (se 1 (by rfl) ⟨458036, by rfl⟩ : syracuseStep 610715 = 916073) B916073
theorem B39703159 : Blo 354756 39703159 := bstep (se 1 (by rfl) ⟨29777369, by rfl⟩ : syracuseStep 39703159 = 59554739) B59554739
theorem B676831 : Blo 354756 676831 := bstep (se 1 (by rfl) ⟨507623, by rfl⟩ : syracuseStep 676831 = 1015247) B1015247
theorem B4576297 : Blo 354756 4576297 := bstep (se 2 (by rfl) ⟨1716111, by rfl⟩ : syracuseStep 4576297 = 3432223) B3432223
theorem B906491 : Blo 354756 906491 := bstep (se 1 (by rfl) ⟨679868, by rfl⟩ : syracuseStep 906491 = 1359737) B1359737
theorem B4053239 : Blo 354756 4053239 := bstep (se 1 (by rfl) ⟨3039929, by rfl⟩ : syracuseStep 4053239 = 6079859) B6079859
theorem B973075 : Blo 354756 973075 := bstep (se 1 (by rfl) ⟨729806, by rfl⟩ : syracuseStep 973075 = 1459613) B1459613
theorem B645575 : Blo 354756 645575 := bstep (se 1 (by rfl) ⟨484181, by rfl⟩ : syracuseStep 645575 = 968363) B968363
theorem B907919 : Blo 354756 907919 := bstep (se 1 (by rfl) ⟨680939, by rfl⟩ : syracuseStep 907919 = 1361879) B1361879
theorem B3037985 : Blo 354756 3037985 := bstep (se 2 (by rfl) ⟨1139244, by rfl⟩ : syracuseStep 3037985 = 2278489) B2278489
theorem B449383 : Blo 354756 449383 := bstep (se 1 (by rfl) ⟨337037, by rfl⟩ : syracuseStep 449383 = 674075) B674075
theorem B9132911 : Blo 354756 9132911 := bstep (se 1 (by rfl) ⟨6849683, by rfl⟩ : syracuseStep 9132911 = 13699367) B13699367
theorem B29678561 : Blo 354756 29678561 := bstep (se 2 (by rfl) ⟨11129460, by rfl⟩ : syracuseStep 29678561 = 22258921) B22258921
theorem B1531037 : Blo 354756 1531037 := bstep (se 3 (by rfl) ⟨287069, by rfl⟩ : syracuseStep 1531037 = 574139) B574139
theorem B1203443 : Blo 354756 1203443 := bstep (se 1 (by rfl) ⟨902582, by rfl⟩ : syracuseStep 1203443 = 1805165) B1805165
theorem B3038633 : Blo 354756 3038633 := bstep (se 2 (by rfl) ⟨1139487, by rfl⟩ : syracuseStep 3038633 = 2278975) B2278975
theorem B679337 : Blo 354756 679337 := bstep (se 2 (by rfl) ⟨254751, by rfl⟩ : syracuseStep 679337 = 509503) B509503
theorem B2022839 : Blo 354756 2022839 := bstep (se 1 (by rfl) ⟨1517129, by rfl⟩ : syracuseStep 2022839 = 3034259) B3034259
theorem B450623 : Blo 354756 450623 := bstep (se 1 (by rfl) ⟨337967, by rfl⟩ : syracuseStep 450623 = 675935) B675935
theorem B2318539 : Blo 354756 2318539 := bstep (se 1 (by rfl) ⟨1738904, by rfl⟩ : syracuseStep 2318539 = 3477809) B3477809
theorem B680233 : Blo 354756 680233 := bstep (se 2 (by rfl) ⟨255087, by rfl⟩ : syracuseStep 680233 = 510175) B510175
theorem B1139359 : Blo 354756 1139359 := bstep (se 1 (by rfl) ⟨854519, by rfl⟩ : syracuseStep 1139359 = 1709039) B1709039
theorem B3433225 : Blo 354756 3433225 := bstep (se 2 (by rfl) ⟨1287459, by rfl⟩ : syracuseStep 3433225 = 2574919) B2574919
theorem B3105661 : Blo 354756 3105661 := bstep (se 3 (by rfl) ⟨582311, by rfl⟩ : syracuseStep 3105661 = 1164623) B1164623
theorem B1729439 : Blo 354756 1729439 := bstep (se 1 (by rfl) ⟨1297079, by rfl⟩ : syracuseStep 1729439 = 2594159) B2594159
theorem B1205387 : Blo 354756 1205387 := bstep (se 1 (by rfl) ⟨904040, by rfl⟩ : syracuseStep 1205387 = 1808081) B1808081
theorem B451919 : Blo 354756 451919 := bstep (se 1 (by rfl) ⟨338939, by rfl⟩ : syracuseStep 451919 = 677879) B677879
theorem B1140065 : Blo 354756 1140065 := bstep (se 2 (by rfl) ⟨427524, by rfl⟩ : syracuseStep 1140065 = 855049) B855049
theorem B452071 : Blo 354756 452071 := bstep (se 1 (by rfl) ⟨339053, by rfl⟩ : syracuseStep 452071 = 678107) B678107
theorem B386939 : Blo 354756 386939 := bstep (se 1 (by rfl) ⟨290204, by rfl⟩ : syracuseStep 386939 = 580409) B580409
theorem B2287739 : Blo 354756 2287739 := bstep (se 1 (by rfl) ⟨1715804, by rfl⟩ : syracuseStep 2287739 = 3431609) B3431609
theorem B2746667 : Blo 354756 2746667 := bstep (se 1 (by rfl) ⟨2060000, by rfl⟩ : syracuseStep 2746667 = 4120001) B4120001
theorem B15395183 : Blo 354756 15395183 := bstep (se 1 (by rfl) ⟨11546387, by rfl⟩ : syracuseStep 15395183 = 23092775) B23092775
theorem B1337719 : Blo 354756 1337719 := bstep (se 1 (by rfl) ⟨1003289, by rfl⟩ : syracuseStep 1337719 = 2006579) B2006579
theorem B4680119 : Blo 354756 4680119 := bstep (se 1 (by rfl) ⟨3510089, by rfl⟩ : syracuseStep 4680119 = 7020179) B7020179
theorem B354791 : Blo 354756 354791 := bstep (se 1 (by rfl) ⟨266093, by rfl⟩ : syracuseStep 354791 = 532187) B532187
theorem B2026073 : Blo 354756 2026073 := bstep (se 2 (by rfl) ⟨759777, by rfl⟩ : syracuseStep 2026073 = 1519555) B1519555
theorem B1206899 : Blo 354756 1206899 := bstep (se 1 (by rfl) ⟨905174, by rfl⟩ : syracuseStep 1206899 = 1810349) B1810349
theorem B354971 : Blo 354756 354971 := bstep (se 1 (by rfl) ⟨266228, by rfl⟩ : syracuseStep 354971 = 532457) B532457
theorem B1207007 : Blo 354756 1207007 := bstep (se 1 (by rfl) ⟨905255, by rfl⟩ : syracuseStep 1207007 = 1810511) B1810511
theorem B15199301 : Blo 354756 15199301 := bstep (se 4 (by rfl) ⟨1424934, by rfl⟩ : syracuseStep 15199301 = 2849869) B2849869
theorem B355439 : Blo 354756 355439 := bstep (se 1 (by rfl) ⟨266579, by rfl⟩ : syracuseStep 355439 = 533159) B533159
theorem B5139571 : Blo 354756 5139571 := bstep (se 1 (by rfl) ⟨3854678, by rfl⟩ : syracuseStep 5139571 = 7709357) B7709357
theorem B355519 : Blo 354756 355519 := bstep (se 1 (by rfl) ⟨266639, by rfl⟩ : syracuseStep 355519 = 533279) B533279
theorem B355535 : Blo 354756 355535 := bstep (se 1 (by rfl) ⟨266651, by rfl⟩ : syracuseStep 355535 = 533303) B533303
theorem B355655 : Blo 354756 355655 := bstep (se 1 (by rfl) ⟨266741, by rfl⟩ : syracuseStep 355655 = 533483) B533483
theorem B1207979 : Blo 354756 1207979 := bstep (se 1 (by rfl) ⟨905984, by rfl⟩ : syracuseStep 1207979 = 1811969) B1811969
theorem B4550417 : Blo 354756 4550417 := bstep (se 2 (by rfl) ⟨1706406, by rfl⟩ : syracuseStep 4550417 = 3412813) B3412813
theorem B356383 : Blo 354756 356383 := bstep (se 1 (by rfl) ⟨267287, by rfl⟩ : syracuseStep 356383 = 534575) B534575
theorem B651359 : Blo 354756 651359 := bstep (se 1 (by rfl) ⟨488519, by rfl⟩ : syracuseStep 651359 = 977039) B977039
theorem B1208519 : Blo 354756 1208519 := bstep (se 1 (by rfl) ⟨906389, by rfl⟩ : syracuseStep 1208519 = 1812779) B1812779
theorem B356559 : Blo 354756 356559 := bstep (se 1 (by rfl) ⟨267419, by rfl⟩ : syracuseStep 356559 = 534839) B534839
theorem B356679 : Blo 354756 356679 := bstep (se 1 (by rfl) ⟨267509, by rfl⟩ : syracuseStep 356679 = 535019) B535019
theorem B1143179 : Blo 354756 1143179 := bstep (se 1 (by rfl) ⟨857384, by rfl⟩ : syracuseStep 1143179 = 1714769) B1714769
theorem B357147 : Blo 354756 357147 := bstep (se 1 (by rfl) ⟨267860, by rfl⟩ : syracuseStep 357147 = 535721) B535721
theorem B1012571 : Blo 354756 1012571 := bstep (se 1 (by rfl) ⟨759428, by rfl⟩ : syracuseStep 1012571 = 1518857) B1518857
theorem B357423 : Blo 354756 357423 := bstep (se 1 (by rfl) ⟨268067, by rfl⟩ : syracuseStep 357423 = 536135) B536135
theorem B357543 : Blo 354756 357543 := bstep (se 1 (by rfl) ⟨268157, by rfl⟩ : syracuseStep 357543 = 536315) B536315
theorem B1930499 : Blo 354756 1930499 := bstep (se 1 (by rfl) ⟨1447874, by rfl⟩ : syracuseStep 1930499 = 2895749) B2895749
theorem B2061571 : Blo 354756 2061571 := bstep (se 1 (by rfl) ⟨1546178, by rfl⟩ : syracuseStep 2061571 = 3092357) B3092357
theorem B3864019 : Blo 354756 3864019 := bstep (se 1 (by rfl) ⟨2898014, by rfl⟩ : syracuseStep 3864019 = 5796029) B5796029
theorem B357991 : Blo 354756 357991 := bstep (se 1 (by rfl) ⟨268493, by rfl⟩ : syracuseStep 357991 = 536987) B536987
theorem B1209977 : Blo 354756 1209977 := bstep (se 2 (by rfl) ⟨453741, by rfl⟩ : syracuseStep 1209977 = 907483) B907483
theorem B358271 : Blo 354756 358271 := bstep (se 1 (by rfl) ⟨268703, by rfl⟩ : syracuseStep 358271 = 537407) B537407
theorem B358367 : Blo 354756 358367 := bstep (se 1 (by rfl) ⟨268775, by rfl⟩ : syracuseStep 358367 = 537551) B537551
theorem B358395 : Blo 354756 358395 := bstep (se 1 (by rfl) ⟨268796, by rfl⟩ : syracuseStep 358395 = 537593) B537593
theorem B358427 : Blo 354756 358427 := bstep (se 1 (by rfl) ⟨268820, by rfl⟩ : syracuseStep 358427 = 537641) B537641
theorem B358447 : Blo 354756 358447 := bstep (se 1 (by rfl) ⟨268835, by rfl⟩ : syracuseStep 358447 = 537671) B537671
theorem B358567 : Blo 354756 358567 := bstep (se 1 (by rfl) ⟨268925, by rfl⟩ : syracuseStep 358567 = 537851) B537851
theorem B2161691 : Blo 354756 2161691 := bstep (se 1 (by rfl) ⟨1621268, by rfl⟩ : syracuseStep 2161691 = 3242537) B3242537
theorem B1145947 : Blo 354756 1145947 := bstep (se 1 (by rfl) ⟨859460, by rfl⟩ : syracuseStep 1145947 = 1718921) B1718921
theorem B1933267 : Blo 354756 1933267 := bstep (se 1 (by rfl) ⟨1449950, by rfl⟩ : syracuseStep 1933267 = 2899901) B2899901
theorem B1736957 : Blo 354756 1736957 := bstep (se 3 (by rfl) ⟨325679, by rfl⟩ : syracuseStep 1736957 = 651359) B651359
theorem B6881669 : Blo 354756 6881669 := bstep (se 4 (by rfl) ⟨645156, by rfl⟩ : syracuseStep 6881669 = 1290313) B1290313
theorem B3441143 : Blo 354756 3441143 := bstep (se 1 (by rfl) ⟨2580857, by rfl⟩ : syracuseStep 3441143 = 5161715) B5161715
theorem B1279115 : Blo 354756 1279115 := bstep (se 1 (by rfl) ⟨959336, by rfl⟩ : syracuseStep 1279115 = 1918673) B1918673
theorem B2558483 : Blo 354756 2558483 := bstep (se 1 (by rfl) ⟨1918862, by rfl⟩ : syracuseStep 2558483 = 3837725) B3837725
theorem B1805003 : Blo 354756 1805003 := bstep (se 1 (by rfl) ⟨1353752, by rfl⟩ : syracuseStep 1805003 = 2707505) B2707505
theorem B2559869 : Blo 354756 2559869 := bstep (se 3 (by rfl) ⟨479975, by rfl⟩ : syracuseStep 2559869 = 959951) B959951
theorem B1446011 : Blo 354756 1446011 := bstep (se 1 (by rfl) ⟨1084508, by rfl⟩ : syracuseStep 1446011 = 2169017) B2169017
theorem B6852761 : Blo 354756 6852761 := bstep (se 2 (by rfl) ⟨2569785, by rfl⟩ : syracuseStep 6852761 = 5139571) B5139571
theorem B1380635 : Blo 354756 1380635 := bstep (se 1 (by rfl) ⟨1035476, by rfl⟩ : syracuseStep 1380635 = 2070953) B2070953
theorem B9310727 : Blo 354756 9310727 := bstep (se 1 (by rfl) ⟨6983045, by rfl⟩ : syracuseStep 9310727 = 13966091) B13966091
theorem B6886133 : Blo 354756 6886133 := bstep (se 5 (by rfl) ⟨322787, by rfl⟩ : syracuseStep 6886133 = 645575) B645575
theorem B1020691 : Blo 354756 1020691 := bstep (se 1 (by rfl) ⟨765518, by rfl⟩ : syracuseStep 1020691 = 1531037) B1531037
theorem B1348559 : Blo 354756 1348559 := bstep (se 1 (by rfl) ⟨1011419, by rfl⟩ : syracuseStep 1348559 = 2022839) B2022839
theorem B1709885 : Blo 354756 1709885 := bstep (se 3 (by rfl) ⟨320603, by rfl⟩ : syracuseStep 1709885 = 641207) B641207
theorem B1152959 : Blo 354756 1152959 := bstep (se 1 (by rfl) ⟨864719, by rfl⟩ : syracuseStep 1152959 = 1729439) B1729439
theorem B759881 : Blo 354756 759881 := bstep (se 2 (by rfl) ⟨284955, by rfl⟩ : syracuseStep 759881 = 569911) B569911
theorem B760043 : Blo 354756 760043 := bstep (se 1 (by rfl) ⟨570032, by rfl⟩ : syracuseStep 760043 = 1140065) B1140065
theorem B6101729 : Blo 354756 6101729 := bstep (se 2 (by rfl) ⟨2288148, by rfl⟩ : syracuseStep 6101729 = 4576297) B4576297
theorem B10263455 : Blo 354756 10263455 := bstep (se 1 (by rfl) ⟨7697591, by rfl⟩ : syracuseStep 10263455 = 15395183) B15395183
theorem B3120079 : Blo 354756 3120079 := bstep (se 1 (by rfl) ⟨2340059, by rfl⟩ : syracuseStep 3120079 = 4680119) B4680119
theorem B1350715 : Blo 354756 1350715 := bstep (se 1 (by rfl) ⟨1013036, by rfl⟩ : syracuseStep 1350715 = 2026073) B2026073
theorem B5152025 : Blo 354756 5152025 := bstep (se 2 (by rfl) ⟨1932009, by rfl⟩ : syracuseStep 5152025 = 3864019) B3864019
theorem B10132867 : Blo 354756 10132867 := bstep (se 1 (by rfl) ⟨7599650, by rfl⟩ : syracuseStep 10132867 = 15199301) B15199301
theorem B1810025 : Blo 354756 1810025 := bstep (se 2 (by rfl) ⟨678759, by rfl⟩ : syracuseStep 1810025 = 1357519) B1357519
theorem B762119 : Blo 354756 762119 := bstep (se 1 (by rfl) ⟨571589, by rfl⟩ : syracuseStep 762119 = 1143179) B1143179
theorem B1286999 : Blo 354756 1286999 := bstep (se 1 (by rfl) ⟨965249, by rfl⟩ : syracuseStep 1286999 = 1930499) B1930499
theorem B2696327 : Blo 354756 2696327 := bstep (se 1 (by rfl) ⟨2022245, by rfl⟩ : syracuseStep 2696327 = 4044491) B4044491
theorem B599177 : Blo 354756 599177 := bstep (se 2 (by rfl) ⟨224691, by rfl⟩ : syracuseStep 599177 = 449383) B449383
theorem B533831 : Blo 354756 533831 := bstep (se 1 (by rfl) ⟨400373, by rfl⟩ : syracuseStep 533831 = 800747) B800747
theorem B2893735 : Blo 354756 2893735 := bstep (se 1 (by rfl) ⟨2170301, by rfl⟩ : syracuseStep 2893735 = 4340603) B4340603
theorem B534665 : Blo 354756 534665 := bstep (se 2 (by rfl) ⟨200499, by rfl⟩ : syracuseStep 534665 = 400999) B400999
theorem B535337 : Blo 354756 535337 := bstep (se 2 (by rfl) ⟨200751, by rfl⟩ : syracuseStep 535337 = 401503) B401503
theorem B3091385 : Blo 354756 3091385 := bstep (se 2 (by rfl) ⟨1159269, by rfl⟩ : syracuseStep 3091385 = 2318539) B2318539
theorem B535529 : Blo 354756 535529 := bstep (se 2 (by rfl) ⟨200823, by rfl⟩ : syracuseStep 535529 = 401647) B401647
theorem B536015 : Blo 354756 536015 := bstep (se 1 (by rfl) ⟨402011, by rfl⟩ : syracuseStep 536015 = 804023) B804023
theorem B1519145 : Blo 354756 1519145 := bstep (se 2 (by rfl) ⟨569679, by rfl⟩ : syracuseStep 1519145 = 1139359) B1139359
theorem B536111 : Blo 354756 536111 := bstep (se 1 (by rfl) ⟨402083, by rfl⟩ : syracuseStep 536111 = 804167) B804167
theorem B4140881 : Blo 354756 4140881 := bstep (se 2 (by rfl) ⟨1552830, by rfl⟩ : syracuseStep 4140881 = 3105661) B3105661
theorem B2273183 : Blo 354756 2273183 := bstep (se 1 (by rfl) ⟨1704887, by rfl⟩ : syracuseStep 2273183 = 3409775) B3409775
theorem B765895 : Blo 354756 765895 := bstep (se 1 (by rfl) ⟨574421, by rfl⟩ : syracuseStep 765895 = 1148843) B1148843
theorem B3059855 : Blo 354756 3059855 := bstep (se 1 (by rfl) ⟨2294891, by rfl⟩ : syracuseStep 3059855 = 4589783) B4589783
theorem B536783 : Blo 354756 536783 := bstep (se 1 (by rfl) ⟨402587, by rfl⟩ : syracuseStep 536783 = 805175) B805175
theorem B536903 : Blo 354756 536903 := bstep (se 1 (by rfl) ⟨402677, by rfl⟩ : syracuseStep 536903 = 805355) B805355
theorem B2798135 : Blo 354756 2798135 := bstep (se 1 (by rfl) ⟨2098601, by rfl⟩ : syracuseStep 2798135 = 4197203) B4197203
theorem B602761 : Blo 354756 602761 := bstep (se 2 (by rfl) ⟨226035, by rfl⟩ : syracuseStep 602761 = 452071) B452071
theorem B10990495 : Blo 354756 10990495 := bstep (se 1 (by rfl) ⟨8242871, by rfl⟩ : syracuseStep 10990495 = 16485743) B16485743
theorem B603119 : Blo 354756 603119 := bstep (se 1 (by rfl) ⟨452339, by rfl⟩ : syracuseStep 603119 = 904679) B904679
theorem B537695 : Blo 354756 537695 := bstep (se 1 (by rfl) ⟨403271, by rfl⟩ : syracuseStep 537695 = 806543) B806543
theorem B537755 : Blo 354756 537755 := bstep (se 1 (by rfl) ⟨403316, by rfl⟩ : syracuseStep 537755 = 806633) B806633
theorem B603679 : Blo 354756 603679 := bstep (se 1 (by rfl) ⟨452759, by rfl⟩ : syracuseStep 603679 = 905519) B905519
theorem B407143 : Blo 354756 407143 := bstep (se 1 (by rfl) ⟨305357, by rfl⟩ : syracuseStep 407143 = 610715) B610715
theorem B1783625 : Blo 354756 1783625 := bstep (se 2 (by rfl) ⟨668859, by rfl⟩ : syracuseStep 1783625 = 1337719) B1337719
theorem B5814139 : Blo 354756 5814139 := bstep (se 1 (by rfl) ⟨4360604, by rfl⟩ : syracuseStep 5814139 = 8721209) B8721209
theorem B604327 : Blo 354756 604327 := bstep (se 1 (by rfl) ⟨453245, by rfl⟩ : syracuseStep 604327 = 906491) B906491
theorem B801593 : Blo 354756 801593 := bstep (se 2 (by rfl) ⟨300597, by rfl⟩ : syracuseStep 801593 = 601195) B601195
theorem B2702159 : Blo 354756 2702159 := bstep (se 1 (by rfl) ⟨2026619, by rfl⟩ : syracuseStep 2702159 = 4053239) B4053239
theorem B900031 : Blo 354756 900031 := bstep (se 1 (by rfl) ⟨675023, by rfl⟩ : syracuseStep 900031 = 1350047) B1350047
theorem B605279 : Blo 354756 605279 := bstep (se 1 (by rfl) ⟨453959, by rfl⟩ : syracuseStep 605279 = 907919) B907919
theorem B4045949 : Blo 354756 4045949 := bstep (se 3 (by rfl) ⟨758615, by rfl⟩ : syracuseStep 4045949 = 1517231) B1517231
theorem B801953 : Blo 354756 801953 := bstep (se 2 (by rfl) ⟨300732, by rfl⟩ : syracuseStep 801953 = 601465) B601465
theorem B802295 : Blo 354756 802295 := bstep (se 1 (by rfl) ⟨601721, by rfl⟩ : syracuseStep 802295 = 1203443) B1203443
theorem B1031837 : Blo 354756 1031837 := bstep (se 3 (by rfl) ⟨193469, by rfl⟩ : syracuseStep 1031837 = 386939) B386939
theorem B901307 : Blo 354756 901307 := bstep (se 1 (by rfl) ⟨675980, by rfl⟩ : syracuseStep 901307 = 1351961) B1351961
theorem B803591 : Blo 354756 803591 := bstep (se 1 (by rfl) ⟨602693, by rfl⟩ : syracuseStep 803591 = 1205387) B1205387
theorem B7324445 : Blo 354756 7324445 := bstep (se 3 (by rfl) ⟨1373333, by rfl⟩ : syracuseStep 7324445 = 2746667) B2746667
theorem B98321201 : Blo 354756 98321201 := bstep (se 2 (by rfl) ⟨36870450, by rfl⟩ : syracuseStep 98321201 = 73740901) B73740901
theorem B52937545 : Blo 354756 52937545 := bstep (se 2 (by rfl) ⟨19851579, by rfl⟩ : syracuseStep 52937545 = 39703159) B39703159
theorem B902441 : Blo 354756 902441 := bstep (se 2 (by rfl) ⟨338415, by rfl⟩ : syracuseStep 902441 = 676831) B676831
theorem B1525159 : Blo 354756 1525159 := bstep (se 1 (by rfl) ⟨1143869, by rfl⟩ : syracuseStep 1525159 = 2287739) B2287739
theorem B673505 : Blo 354756 673505 := bstep (se 2 (by rfl) ⟨252564, by rfl⟩ : syracuseStep 673505 = 505129) B505129
theorem B804599 : Blo 354756 804599 := bstep (se 1 (by rfl) ⟨603449, by rfl⟩ : syracuseStep 804599 = 1206899) B1206899
theorem B804671 : Blo 354756 804671 := bstep (se 1 (by rfl) ⟨603503, by rfl⟩ : syracuseStep 804671 = 1207007) B1207007
theorem B379291 : Blo 354756 379291 := bstep (se 1 (by rfl) ⟨284468, by rfl⟩ : syracuseStep 379291 = 568937) B568937
theorem B1296815 : Blo 354756 1296815 := bstep (se 1 (by rfl) ⟨972611, by rfl⟩ : syracuseStep 1296815 = 1945223) B1945223
theorem B805319 : Blo 354756 805319 := bstep (se 1 (by rfl) ⟨603989, by rfl⟩ : syracuseStep 805319 = 1207979) B1207979
theorem B3033611 : Blo 354756 3033611 := bstep (se 1 (by rfl) ⟨2275208, by rfl⟩ : syracuseStep 3033611 = 4550417) B4550417
theorem B805679 : Blo 354756 805679 := bstep (se 1 (by rfl) ⟨604259, by rfl⟩ : syracuseStep 805679 = 1208519) B1208519
theorem B1297433 : Blo 354756 1297433 := bstep (se 2 (by rfl) ⟨486537, by rfl⟩ : syracuseStep 1297433 = 973075) B973075
theorem B380111 : Blo 354756 380111 := bstep (se 1 (by rfl) ⟨285083, by rfl⟩ : syracuseStep 380111 = 570167) B570167
theorem B675047 : Blo 354756 675047 := bstep (se 1 (by rfl) ⟨506285, by rfl⟩ : syracuseStep 675047 = 1012571) B1012571
theorem B2018849 : Blo 354756 2018849 := bstep (se 2 (by rfl) ⟨757068, by rfl⟩ : syracuseStep 2018849 = 1514137) B1514137
theorem B806651 : Blo 354756 806651 := bstep (se 1 (by rfl) ⟨604988, by rfl⟩ : syracuseStep 806651 = 1209977) B1209977
theorem B3035009 : Blo 354756 3035009 := bstep (se 2 (by rfl) ⟨1138128, by rfl⟩ : syracuseStep 3035009 = 2276257) B2276257
theorem B380863 : Blo 354756 380863 := bstep (se 1 (by rfl) ⟨285647, by rfl⟩ : syracuseStep 380863 = 571295) B571295
theorem B1527929 : Blo 354756 1527929 := bstep (se 2 (by rfl) ⟨572973, by rfl⟩ : syracuseStep 1527929 = 1145947) B1145947
theorem B381119 : Blo 354756 381119 := bstep (se 1 (by rfl) ⟨285839, by rfl⟩ : syracuseStep 381119 = 571679) B571679
theorem B774647 : Blo 354756 774647 := bstep (se 1 (by rfl) ⟨580985, by rfl⟩ : syracuseStep 774647 = 1161971) B1161971
theorem B2577689 : Blo 354756 2577689 := bstep (se 2 (by rfl) ⟨966633, by rfl⟩ : syracuseStep 2577689 = 1933267) B1933267
theorem B1201661 : Blo 354756 1201661 := bstep (se 3 (by rfl) ⟨225311, by rfl⟩ : syracuseStep 1201661 = 450623) B450623
theorem B1201769 : Blo 354756 1201769 := bstep (se 2 (by rfl) ⟨450663, by rfl⟩ : syracuseStep 1201769 = 901327) B901327
theorem B6084233 : Blo 354756 6084233 := bstep (se 2 (by rfl) ⟨2281587, by rfl⟩ : syracuseStep 6084233 = 4563175) B4563175
theorem B2578063 : Blo 354756 2578063 := bstep (se 1 (by rfl) ⟨1933547, by rfl⟩ : syracuseStep 2578063 = 3867095) B3867095
theorem B906977 : Blo 354756 906977 := bstep (se 2 (by rfl) ⟨340116, by rfl⟩ : syracuseStep 906977 = 680233) B680233
theorem B2709449 : Blo 354756 2709449 := bstep (se 2 (by rfl) ⟨1016043, by rfl⟩ : syracuseStep 2709449 = 2032087) B2032087
theorem B1202363 : Blo 354756 1202363 := bstep (se 1 (by rfl) ⟨901772, by rfl⟩ : syracuseStep 1202363 = 1803545) B1803545
theorem B4577633 : Blo 354756 4577633 := bstep (se 2 (by rfl) ⟨1716612, by rfl⟩ : syracuseStep 4577633 = 3433225) B3433225
theorem B1137053 : Blo 354756 1137053 := bstep (se 3 (by rfl) ⟨213197, by rfl⟩ : syracuseStep 1137053 = 426395) B426395
theorem B12966331 : Blo 354756 12966331 := bstep (se 1 (by rfl) ⟨9724748, by rfl⟩ : syracuseStep 12966331 = 19449497) B19449497
theorem B2022155 : Blo 354756 2022155 := bstep (se 1 (by rfl) ⟨1516616, by rfl⟩ : syracuseStep 2022155 = 3033233) B3033233
theorem B1138873 : Blo 354756 1138873 := bstep (se 2 (by rfl) ⟨427077, by rfl⟩ : syracuseStep 1138873 = 854155) B854155
theorem B1204415 : Blo 354756 1204415 := bstep (se 1 (by rfl) ⟨903311, by rfl⟩ : syracuseStep 1204415 = 1806623) B1806623
theorem B1467143 : Blo 354756 1467143 := bstep (se 1 (by rfl) ⟨1100357, by rfl⟩ : syracuseStep 1467143 = 2200715) B2200715
theorem B1205117 : Blo 354756 1205117 := bstep (se 3 (by rfl) ⟨225959, by rfl⟩ : syracuseStep 1205117 = 451919) B451919
theorem B2025323 : Blo 354756 2025323 := bstep (se 1 (by rfl) ⟨1518992, by rfl⟩ : syracuseStep 2025323 = 3037985) B3037985
theorem B12347255 : Blo 354756 12347255 := bstep (se 1 (by rfl) ⟨9260441, by rfl⟩ : syracuseStep 12347255 = 18520883) B18520883
theorem B6088607 : Blo 354756 6088607 := bstep (se 1 (by rfl) ⟨4566455, by rfl⟩ : syracuseStep 6088607 = 9132911) B9132911
theorem B19785707 : Blo 354756 19785707 := bstep (se 1 (by rfl) ⟨14839280, by rfl⟩ : syracuseStep 19785707 = 29678561) B29678561
theorem B2025755 : Blo 354756 2025755 := bstep (se 1 (by rfl) ⟨1519316, by rfl⟩ : syracuseStep 2025755 = 3038633) B3038633
theorem B452891 : Blo 354756 452891 := bstep (se 1 (by rfl) ⟨339668, by rfl⟩ : syracuseStep 452891 = 679337) B679337
theorem B354799 : Blo 354756 354799 := bstep (se 1 (by rfl) ⟨266099, by rfl⟩ : syracuseStep 354799 = 532199) B532199
theorem B1141409 : Blo 354756 1141409 := bstep (se 2 (by rfl) ⟨428028, by rfl⟩ : syracuseStep 1141409 = 856057) B856057
theorem B354983 : Blo 354756 354983 := bstep (se 1 (by rfl) ⟨266237, by rfl⟩ : syracuseStep 354983 = 532475) B532475
theorem B355023 : Blo 354756 355023 := bstep (se 1 (by rfl) ⟨266267, by rfl⟩ : syracuseStep 355023 = 532535) B532535
theorem B3238667 : Blo 354756 3238667 := bstep (se 1 (by rfl) ⟨2429000, by rfl⟩ : syracuseStep 3238667 = 4858001) B4858001
theorem B355103 : Blo 354756 355103 := bstep (se 1 (by rfl) ⟨266327, by rfl⟩ : syracuseStep 355103 = 532655) B532655
theorem B1207169 : Blo 354756 1207169 := bstep (se 2 (by rfl) ⟨452688, by rfl⟩ : syracuseStep 1207169 = 905377) B905377
theorem B355239 : Blo 354756 355239 := bstep (se 1 (by rfl) ⟨266429, by rfl⟩ : syracuseStep 355239 = 532859) B532859
theorem B1141769 : Blo 354756 1141769 := bstep (se 2 (by rfl) ⟨428163, by rfl⟩ : syracuseStep 1141769 = 856327) B856327
theorem B355355 : Blo 354756 355355 := bstep (se 1 (by rfl) ⟨266516, by rfl⟩ : syracuseStep 355355 = 533033) B533033
theorem B355419 : Blo 354756 355419 := bstep (se 1 (by rfl) ⟨266564, by rfl⟩ : syracuseStep 355419 = 533129) B533129
theorem B355559 : Blo 354756 355559 := bstep (se 1 (by rfl) ⟨266669, by rfl⟩ : syracuseStep 355559 = 533339) B533339
theorem B355583 : Blo 354756 355583 := bstep (se 1 (by rfl) ⟨266687, by rfl⟩ : syracuseStep 355583 = 533375) B533375
theorem B355631 : Blo 354756 355631 := bstep (se 1 (by rfl) ⟨266723, by rfl⟩ : syracuseStep 355631 = 533447) B533447
theorem B355775 : Blo 354756 355775 := bstep (se 1 (by rfl) ⟨266831, by rfl⟩ : syracuseStep 355775 = 533663) B533663
theorem B355871 : Blo 354756 355871 := bstep (se 1 (by rfl) ⟨266903, by rfl⟩ : syracuseStep 355871 = 533807) B533807
theorem B355999 : Blo 354756 355999 := bstep (se 1 (by rfl) ⟨266999, by rfl⟩ : syracuseStep 355999 = 533999) B533999
theorem B356007 : Blo 354756 356007 := bstep (se 1 (by rfl) ⟨267005, by rfl⟩ : syracuseStep 356007 = 534011) B534011
theorem B356031 : Blo 354756 356031 := bstep (se 1 (by rfl) ⟨267023, by rfl⟩ : syracuseStep 356031 = 534047) B534047
theorem B3043007 : Blo 354756 3043007 := bstep (se 1 (by rfl) ⟨2282255, by rfl⟩ : syracuseStep 3043007 = 4564511) B4564511
theorem B356127 : Blo 354756 356127 := bstep (se 1 (by rfl) ⟨267095, by rfl⟩ : syracuseStep 356127 = 534191) B534191
theorem B356187 : Blo 354756 356187 := bstep (se 1 (by rfl) ⟨267140, by rfl⟩ : syracuseStep 356187 = 534281) B534281
theorem B356207 : Blo 354756 356207 := bstep (se 1 (by rfl) ⟨267155, by rfl⟩ : syracuseStep 356207 = 534311) B534311
theorem B3862637 : Blo 354756 3862637 := bstep (se 3 (by rfl) ⟨724244, by rfl⟩ : syracuseStep 3862637 = 1448489) B1448489
theorem B1011943 : Blo 354756 1011943 := bstep (se 1 (by rfl) ⟨758957, by rfl⟩ : syracuseStep 1011943 = 1517915) B1517915
theorem B356607 : Blo 354756 356607 := bstep (se 1 (by rfl) ⟨267455, by rfl⟩ : syracuseStep 356607 = 534911) B534911
theorem B2748761 : Blo 354756 2748761 := bstep (se 2 (by rfl) ⟨1030785, by rfl⟩ : syracuseStep 2748761 = 2061571) B2061571
theorem B356767 : Blo 354756 356767 := bstep (se 1 (by rfl) ⟨267575, by rfl⟩ : syracuseStep 356767 = 535151) B535151
theorem B356911 : Blo 354756 356911 := bstep (se 1 (by rfl) ⟨267683, by rfl⟩ : syracuseStep 356911 = 535367) B535367
theorem B1012297 : Blo 354756 1012297 := bstep (se 2 (by rfl) ⟨379611, by rfl⟩ : syracuseStep 1012297 = 759223) B759223
theorem B2290457 : Blo 354756 2290457 := bstep (se 2 (by rfl) ⟨858921, by rfl⟩ : syracuseStep 2290457 = 1717843) B1717843
theorem B6845309 : Blo 354756 6845309 := bstep (se 3 (by rfl) ⟨1283495, by rfl⟩ : syracuseStep 6845309 = 2566991) B2566991
theorem B357311 : Blo 354756 357311 := bstep (se 1 (by rfl) ⟨267983, by rfl⟩ : syracuseStep 357311 = 535967) B535967
theorem B1143767 : Blo 354756 1143767 := bstep (se 1 (by rfl) ⟨857825, by rfl⟩ : syracuseStep 1143767 = 1715651) B1715651
theorem B357487 : Blo 354756 357487 := bstep (se 1 (by rfl) ⟨268115, by rfl⟩ : syracuseStep 357487 = 536231) B536231
theorem B357503 : Blo 354756 357503 := bstep (se 1 (by rfl) ⟨268127, by rfl⟩ : syracuseStep 357503 = 536255) B536255
theorem B16741529 : Blo 354756 16741529 := bstep (se 2 (by rfl) ⟨6278073, by rfl⟩ : syracuseStep 16741529 = 12556147) B12556147
theorem B357567 : Blo 354756 357567 := bstep (se 1 (by rfl) ⟨268175, by rfl⟩ : syracuseStep 357567 = 536351) B536351
theorem B5141879 : Blo 354756 5141879 := bstep (se 1 (by rfl) ⟨3856409, by rfl⟩ : syracuseStep 5141879 = 7712819) B7712819
theorem B357759 : Blo 354756 357759 := bstep (se 1 (by rfl) ⟨268319, by rfl⟩ : syracuseStep 357759 = 536639) B536639
theorem B357887 : Blo 354756 357887 := bstep (se 1 (by rfl) ⟨268415, by rfl⟩ : syracuseStep 357887 = 536831) B536831
theorem B357915 : Blo 354756 357915 := bstep (se 1 (by rfl) ⟨268436, by rfl⟩ : syracuseStep 357915 = 536873) B536873
theorem B358095 : Blo 354756 358095 := bstep (se 1 (by rfl) ⟨268571, by rfl⟩ : syracuseStep 358095 = 537143) B537143
theorem B358255 : Blo 354756 358255 := bstep (se 1 (by rfl) ⟨268691, by rfl⟩ : syracuseStep 358255 = 537383) B537383
theorem B358335 : Blo 354756 358335 := bstep (se 1 (by rfl) ⟨268751, by rfl⟩ : syracuseStep 358335 = 537503) B537503
theorem B1013755 : Blo 354756 1013755 := bstep (se 1 (by rfl) ⟨760316, by rfl⟩ : syracuseStep 1013755 = 1520633) B1520633
theorem B358651 : Blo 354756 358651 := bstep (se 1 (by rfl) ⟨268988, by rfl⟩ : syracuseStep 358651 = 537977) B537977
theorem B358655 : Blo 354756 358655 := bstep (se 1 (by rfl) ⟨268991, by rfl⟩ : syracuseStep 358655 = 537983) B537983
theorem B1210679 : Blo 354756 1210679 := bstep (se 1 (by rfl) ⟨908009, by rfl⟩ : syracuseStep 1210679 = 1816019) B1816019
theorem B1538423 : Blo 354756 1538423 := bstep (se 1 (by rfl) ⟨1153817, by rfl⟩ : syracuseStep 1538423 = 2307635) B2307635
theorem B1473515 : Blo 354756 1473515 := bstep (se 1 (by rfl) ⟨1105136, by rfl⟩ : syracuseStep 1473515 = 2210273) B2210273
theorem B1441127 : Blo 354756 1441127 := bstep (se 1 (by rfl) ⟨1080845, by rfl⟩ : syracuseStep 1441127 = 2161691) B2161691
theorem B2719655 : Blo 354756 2719655 := bstep (se 1 (by rfl) ⟨2039741, by rfl⟩ : syracuseStep 2719655 = 4079483) B4079483
theorem B4587779 : Blo 354756 4587779 := bstep (se 1 (by rfl) ⟨3440834, by rfl⟩ : syracuseStep 4587779 = 6881669) B6881669
theorem B2294095 : Blo 354756 2294095 := bstep (se 1 (by rfl) ⟨1720571, by rfl⟩ : syracuseStep 2294095 = 3441143) B3441143
theorem B1016317 : Blo 354756 1016317 := bstep (se 3 (by rfl) ⟨190559, by rfl⟩ : syracuseStep 1016317 = 381119) B381119
theorem B4882963 : Blo 354756 4882963 := bstep (se 1 (by rfl) ⟨3662222, by rfl⟩ : syracuseStep 4882963 = 7324445) B7324445
theorem B852743 : Blo 354756 852743 := bstep (se 1 (by rfl) ⟨639557, by rfl⟩ : syracuseStep 852743 = 1279115) B1279115
theorem B70583393 : Blo 354756 70583393 := bstep (se 2 (by rfl) ⟨26468772, by rfl⟩ : syracuseStep 70583393 = 52937545) B52937545
theorem B1705655 : Blo 354756 1705655 := bstep (se 1 (by rfl) ⟨1279241, by rfl⟩ : syracuseStep 1705655 = 2558483) B2558483
theorem B2033545 : Blo 354756 2033545 := bstep (se 2 (by rfl) ⟨762579, by rfl⟩ : syracuseStep 2033545 = 1525159) B1525159
theorem B3050045 : Blo 354756 3050045 := bstep (se 3 (by rfl) ⟨571883, by rfl⟩ : syracuseStep 3050045 = 1143767) B1143767
theorem B1706579 : Blo 354756 1706579 := bstep (se 1 (by rfl) ⟨1279934, by rfl⟩ : syracuseStep 1706579 = 2559869) B2559869
theorem B1018619 : Blo 354756 1018619 := bstep (se 1 (by rfl) ⟨763964, by rfl⟩ : syracuseStep 1018619 = 1527929) B1527929
theorem B920423 : Blo 354756 920423 := bstep (se 1 (by rfl) ⟨690317, by rfl⟩ : syracuseStep 920423 = 1380635) B1380635
theorem B4590755 : Blo 354756 4590755 := bstep (se 1 (by rfl) ⟨3443066, by rfl⟩ : syracuseStep 4590755 = 6886133) B6886133
theorem B1806299 : Blo 354756 1806299 := bstep (se 1 (by rfl) ⟨1354724, by rfl⟩ : syracuseStep 1806299 = 2709449) B2709449
theorem B3051755 : Blo 354756 3051755 := bstep (se 1 (by rfl) ⟨2288816, by rfl⟩ : syracuseStep 3051755 = 4577633) B4577633
theorem B758035 : Blo 354756 758035 := bstep (se 1 (by rfl) ⟨568526, by rfl⟩ : syracuseStep 758035 = 1137053) B1137053
theorem B4067819 : Blo 354756 4067819 := bstep (se 1 (by rfl) ⟨3050864, by rfl⟩ : syracuseStep 4067819 = 6101729) B6101729
theorem B13832693 : Blo 354756 13832693 := bstep (se 5 (by rfl) ⟨648407, by rfl⟩ : syracuseStep 13832693 = 1296815) B1296815
theorem B1348103 : Blo 354756 1348103 := bstep (se 1 (by rfl) ⟨1011077, by rfl⟩ : syracuseStep 1348103 = 2022155) B2022155
theorem B4756333 : Blo 354756 4756333 := bstep (se 3 (by rfl) ⟨891812, by rfl⟩ : syracuseStep 4756333 = 1783625) B1783625
theorem B1021193 : Blo 354756 1021193 := bstep (se 2 (by rfl) ⟨382947, by rfl⟩ : syracuseStep 1021193 = 765895) B765895
theorem B1349257 : Blo 354756 1349257 := bstep (se 2 (by rfl) ⟨505971, by rfl⟩ : syracuseStep 1349257 = 1011943) B1011943
theorem B857999 : Blo 354756 857999 := bstep (se 1 (by rfl) ⟨643499, by rfl⟩ : syracuseStep 857999 = 1286999) B1286999
theorem B399451 : Blo 354756 399451 := bstep (se 1 (by rfl) ⟨299588, by rfl⟩ : syracuseStep 399451 = 599177) B599177
theorem B1349729 : Blo 354756 1349729 := bstep (se 2 (by rfl) ⟨506148, by rfl⟩ : syracuseStep 1349729 = 1012297) B1012297
theorem B14653993 : Blo 354756 14653993 := bstep (se 2 (by rfl) ⟨5495247, by rfl⟩ : syracuseStep 14653993 = 10990495) B10990495
theorem B1350215 : Blo 354756 1350215 := bstep (se 1 (by rfl) ⟨1012661, by rfl⟩ : syracuseStep 1350215 = 2025323) B2025323
theorem B8231503 : Blo 354756 8231503 := bstep (se 1 (by rfl) ⟨6173627, by rfl⟩ : syracuseStep 8231503 = 12347255) B12347255
theorem B1350503 : Blo 354756 1350503 := bstep (se 1 (by rfl) ⟨1012877, by rfl⟩ : syracuseStep 1350503 = 2025755) B2025755
theorem B761179 : Blo 354756 761179 := bstep (se 1 (by rfl) ⟨570884, by rfl⟩ : syracuseStep 761179 = 1141769) B1141769
theorem B2760587 : Blo 354756 2760587 := bstep (se 1 (by rfl) ⟨2070440, by rfl⟩ : syracuseStep 2760587 = 4140881) B4140881
theorem B1515455 : Blo 354756 1515455 := bstep (se 1 (by rfl) ⟨1136591, by rfl⟩ : syracuseStep 1515455 = 2273183) B2273183
theorem B1351673 : Blo 354756 1351673 := bstep (se 2 (by rfl) ⟨506877, by rfl⟩ : syracuseStep 1351673 = 1013755) B1013755
theorem B2039903 : Blo 354756 2039903 := bstep (se 1 (by rfl) ⟨1529927, by rfl⟩ : syracuseStep 2039903 = 3059855) B3059855
theorem B4563539 : Blo 354756 4563539 := bstep (se 1 (by rfl) ⟨3422654, by rfl⟩ : syracuseStep 4563539 = 6845309) B6845309
theorem B402079 : Blo 354756 402079 := bstep (se 1 (by rfl) ⟨301559, by rfl⟩ : syracuseStep 402079 = 603119) B603119
theorem B13738733 : Blo 354756 13738733 := bstep (se 3 (by rfl) ⟨2576012, by rfl⟩ : syracuseStep 13738733 = 5152025) B5152025
theorem B5383597 : Blo 354756 5383597 := bstep (se 3 (by rfl) ⟨1009424, by rfl⟩ : syracuseStep 5383597 = 2018849) B2018849
theorem B1025615 : Blo 354756 1025615 := bstep (se 1 (by rfl) ⟨769211, by rfl⟩ : syracuseStep 1025615 = 1538423) B1538423
theorem B13510489 : Blo 354756 13510489 := bstep (se 2 (by rfl) ⟨5066433, by rfl⟩ : syracuseStep 13510489 = 10132867) B10132867
theorem B534395 : Blo 354756 534395 := bstep (se 1 (by rfl) ⟨400796, by rfl⟩ : syracuseStep 534395 = 801593) B801593
theorem B403519 : Blo 354756 403519 := bstep (se 1 (by rfl) ⟨302639, by rfl⟩ : syracuseStep 403519 = 605279) B605279
theorem B2697299 : Blo 354756 2697299 := bstep (se 1 (by rfl) ⟨2022974, by rfl⟩ : syracuseStep 2697299 = 4045949) B4045949
theorem B534635 : Blo 354756 534635 := bstep (se 1 (by rfl) ⟨400976, by rfl⟩ : syracuseStep 534635 = 801953) B801953
theorem B960751 : Blo 354756 960751 := bstep (se 1 (by rfl) ⟨720563, by rfl⟩ : syracuseStep 960751 = 1441127) B1441127
theorem B534863 : Blo 354756 534863 := bstep (se 1 (by rfl) ⟨401147, by rfl⟩ : syracuseStep 534863 = 802295) B802295
theorem B1813103 : Blo 354756 1813103 := bstep (se 1 (by rfl) ⟨1359827, by rfl⟩ : syracuseStep 1813103 = 2719655) B2719655
theorem B600871 : Blo 354756 600871 := bstep (se 1 (by rfl) ⟨450653, by rfl⟩ : syracuseStep 600871 = 901307) B901307
theorem B1157971 : Blo 354756 1157971 := bstep (se 1 (by rfl) ⟨868478, by rfl⟩ : syracuseStep 1157971 = 1736957) B1736957
theorem B1518497 : Blo 354756 1518497 := bstep (se 2 (by rfl) ⟨569436, by rfl⟩ : syracuseStep 1518497 = 1138873) B1138873
theorem B535727 : Blo 354756 535727 := bstep (se 1 (by rfl) ⟨401795, by rfl⟩ : syracuseStep 535727 = 803591) B803591
theorem B65547467 : Blo 354756 65547467 := bstep (se 1 (by rfl) ⟨49160600, by rfl⟩ : syracuseStep 65547467 = 98321201) B98321201
theorem B601627 : Blo 354756 601627 := bstep (se 1 (by rfl) ⟨451220, by rfl⟩ : syracuseStep 601627 = 902441) B902441
theorem B536399 : Blo 354756 536399 := bstep (se 1 (by rfl) ⟨402299, by rfl⟩ : syracuseStep 536399 = 804599) B804599
theorem B536447 : Blo 354756 536447 := bstep (se 1 (by rfl) ⟨402335, by rfl⟩ : syracuseStep 536447 = 804671) B804671
theorem B536879 : Blo 354756 536879 := bstep (se 1 (by rfl) ⟨402659, by rfl⟩ : syracuseStep 536879 = 805319) B805319
theorem B537119 : Blo 354756 537119 := bstep (se 1 (by rfl) ⟨402839, by rfl⟩ : syracuseStep 537119 = 805679) B805679
theorem B864955 : Blo 354756 864955 := bstep (se 1 (by rfl) ⟨648716, by rfl⟩ : syracuseStep 864955 = 1297433) B1297433
theorem B537767 : Blo 354756 537767 := bstep (se 1 (by rfl) ⟨403325, by rfl⟩ : syracuseStep 537767 = 806651) B806651
theorem B964007 : Blo 354756 964007 := bstep (se 1 (by rfl) ⟨723005, by rfl⟩ : syracuseStep 964007 = 1446011) B1446011
theorem B4568507 : Blo 354756 4568507 := bstep (se 1 (by rfl) ⟨3426380, by rfl⟩ : syracuseStep 4568507 = 6852761) B6852761
theorem B6207151 : Blo 354756 6207151 := bstep (se 1 (by rfl) ⟨4655363, by rfl⟩ : syracuseStep 6207151 = 9310727) B9310727
theorem B505721 : Blo 354756 505721 := bstep (se 2 (by rfl) ⟨189645, by rfl⟩ : syracuseStep 505721 = 379291) B379291
theorem B899039 : Blo 354756 899039 := bstep (se 1 (by rfl) ⟨674279, by rfl⟩ : syracuseStep 899039 = 1348559) B1348559
theorem B1718459 : Blo 354756 1718459 := bstep (se 1 (by rfl) ⟨1288844, by rfl⟩ : syracuseStep 1718459 = 2577689) B2577689
theorem B801107 : Blo 354756 801107 := bstep (se 1 (by rfl) ⟨600830, by rfl⟩ : syracuseStep 801107 = 1201661) B1201661
theorem B801179 : Blo 354756 801179 := bstep (se 1 (by rfl) ⟨600884, by rfl⟩ : syracuseStep 801179 = 1201769) B1201769
theorem B604651 : Blo 354756 604651 := bstep (se 1 (by rfl) ⟨453488, by rfl⟩ : syracuseStep 604651 = 906977) B906977
theorem B506587 : Blo 354756 506587 := bstep (se 1 (by rfl) ⟨379940, by rfl⟩ : syracuseStep 506587 = 759881) B759881
theorem B801575 : Blo 354756 801575 := bstep (se 1 (by rfl) ⟨601181, by rfl⟩ : syracuseStep 801575 = 1202363) B1202363
theorem B507817 : Blo 354756 507817 := bstep (se 2 (by rfl) ⟨190431, by rfl⟩ : syracuseStep 507817 = 380863) B380863
theorem B802943 : Blo 354756 802943 := bstep (se 1 (by rfl) ⟨602207, by rfl⟩ : syracuseStep 802943 = 1204415) B1204415
theorem B508079 : Blo 354756 508079 := bstep (se 1 (by rfl) ⟨381059, by rfl⟩ : syracuseStep 508079 = 762119) B762119
theorem B803411 : Blo 354756 803411 := bstep (se 1 (by rfl) ⟨602558, by rfl⟩ : syracuseStep 803411 = 1205117) B1205117
theorem B803681 : Blo 354756 803681 := bstep (se 2 (by rfl) ⟨301380, by rfl⟩ : syracuseStep 803681 = 602761) B602761
theorem B1360921 : Blo 354756 1360921 := bstep (se 2 (by rfl) ⟨510345, by rfl⟩ : syracuseStep 1360921 = 1020691) B1020691
theorem B13190471 : Blo 354756 13190471 := bstep (se 1 (by rfl) ⟨9892853, by rfl⟩ : syracuseStep 13190471 = 19785707) B19785707
theorem B804779 : Blo 354756 804779 := bstep (se 1 (by rfl) ⟨603584, by rfl⟩ : syracuseStep 804779 = 1207169) B1207169
theorem B804905 : Blo 354756 804905 := bstep (se 2 (by rfl) ⟨301839, by rfl⟩ : syracuseStep 804905 = 603679) B603679
theorem B542857 : Blo 354756 542857 := bstep (se 2 (by rfl) ⟨203571, by rfl⟩ : syracuseStep 542857 = 407143) B407143
theorem B8243693 : Blo 354756 8243693 := bstep (se 3 (by rfl) ⟨1545692, by rfl⟩ : syracuseStep 8243693 = 3091385) B3091385
theorem B7752185 : Blo 354756 7752185 := bstep (se 2 (by rfl) ⟨2907069, by rfl⟩ : syracuseStep 7752185 = 5814139) B5814139
theorem B2575091 : Blo 354756 2575091 := bstep (se 1 (by rfl) ⟨1931318, by rfl⟩ : syracuseStep 2575091 = 3862637) B3862637
theorem B805769 : Blo 354756 805769 := bstep (se 2 (by rfl) ⟨302163, by rfl⟩ : syracuseStep 805769 = 604327) B604327
theorem B1526971 : Blo 354756 1526971 := bstep (se 1 (by rfl) ⟨1145228, by rfl⟩ : syracuseStep 1526971 = 2290457) B2290457
theorem B17288441 : Blo 354756 17288441 := bstep (se 2 (by rfl) ⟨6483165, by rfl⟩ : syracuseStep 17288441 = 12966331) B12966331
theorem B11161019 : Blo 354756 11161019 := bstep (se 1 (by rfl) ⟨8370764, by rfl⟩ : syracuseStep 11161019 = 16741529) B16741529
theorem B3427919 : Blo 354756 3427919 := bstep (se 1 (by rfl) ⟨2570939, by rfl⟩ : syracuseStep 3427919 = 5141879) B5141879
theorem B1200041 : Blo 354756 1200041 := bstep (se 2 (by rfl) ⟨450015, by rfl⟩ : syracuseStep 1200041 = 900031) B900031
theorem B807119 : Blo 354756 807119 := bstep (se 1 (by rfl) ⟨605339, by rfl⟩ : syracuseStep 807119 = 1210679) B1210679
theorem B449003 : Blo 354756 449003 := bstep (se 1 (by rfl) ⟨336752, by rfl⟩ : syracuseStep 449003 = 673505) B673505
theorem B2022407 : Blo 354756 2022407 := bstep (se 1 (by rfl) ⟨1516805, by rfl⟩ : syracuseStep 2022407 = 3033611) B3033611
theorem B1203335 : Blo 354756 1203335 := bstep (se 1 (by rfl) ⟨902501, by rfl⟩ : syracuseStep 1203335 = 1805003) B1805003
theorem B450031 : Blo 354756 450031 := bstep (se 1 (by rfl) ⟨337523, by rfl⟩ : syracuseStep 450031 = 675047) B675047
theorem B3858313 : Blo 354756 3858313 := bstep (se 2 (by rfl) ⟨1446867, by rfl⟩ : syracuseStep 3858313 = 2893735) B2893735
theorem B2023339 : Blo 354756 2023339 := bstep (se 1 (by rfl) ⟨1517504, by rfl⟩ : syracuseStep 2023339 = 3035009) B3035009
theorem B516431 : Blo 354756 516431 := bstep (se 1 (by rfl) ⟨387323, by rfl⟩ : syracuseStep 516431 = 774647) B774647
theorem B4056155 : Blo 354756 4056155 := bstep (se 1 (by rfl) ⟨3042116, by rfl⟩ : syracuseStep 4056155 = 6084233) B6084233
theorem B1139923 : Blo 354756 1139923 := bstep (se 1 (by rfl) ⟨854942, by rfl⟩ : syracuseStep 1139923 = 1709885) B1709885
theorem B6842303 : Blo 354756 6842303 := bstep (se 1 (by rfl) ⟨5131727, by rfl⟩ : syracuseStep 6842303 = 10263455) B10263455
theorem B1206683 : Blo 354756 1206683 := bstep (se 1 (by rfl) ⟨905012, by rfl⟩ : syracuseStep 1206683 = 1810025) B1810025
theorem B3074557 : Blo 354756 3074557 := bstep (se 3 (by rfl) ⟨576479, by rfl⟩ : syracuseStep 3074557 = 1152959) B1152959
theorem B978095 : Blo 354756 978095 := bstep (se 1 (by rfl) ⟨733571, by rfl⟩ : syracuseStep 978095 = 1467143) B1467143
theorem B2026781 : Blo 354756 2026781 := bstep (se 3 (by rfl) ⟨380021, by rfl⟩ : syracuseStep 2026781 = 760043) B760043
theorem B1207709 : Blo 354756 1207709 := bstep (se 3 (by rfl) ⟨226445, by rfl⟩ : syracuseStep 1207709 = 452891) B452891
theorem B1797551 : Blo 354756 1797551 := bstep (se 1 (by rfl) ⟨1348163, by rfl⟩ : syracuseStep 1797551 = 2696327) B2696327
theorem B355887 : Blo 354756 355887 := bstep (se 1 (by rfl) ⟨266915, by rfl⟩ : syracuseStep 355887 = 533831) B533831
theorem B4059071 : Blo 354756 4059071 := bstep (se 1 (by rfl) ⟨3044303, by rfl⟩ : syracuseStep 4059071 = 6088607) B6088607
theorem B356443 : Blo 354756 356443 := bstep (se 1 (by rfl) ⟨267332, by rfl⟩ : syracuseStep 356443 = 534665) B534665
theorem B3043757 : Blo 354756 3043757 := bstep (se 3 (by rfl) ⟨570704, by rfl⟩ : syracuseStep 3043757 = 1141409) B1141409
theorem B2159111 : Blo 354756 2159111 := bstep (se 1 (by rfl) ⟨1619333, by rfl⟩ : syracuseStep 2159111 = 3238667) B3238667
theorem B356891 : Blo 354756 356891 := bstep (se 1 (by rfl) ⟨267668, by rfl⟩ : syracuseStep 356891 = 535337) B535337
theorem B357019 : Blo 354756 357019 := bstep (se 1 (by rfl) ⟨267764, by rfl⟩ : syracuseStep 357019 = 535529) B535529
theorem B3437417 : Blo 354756 3437417 := bstep (se 2 (by rfl) ⟨1289031, by rfl⟩ : syracuseStep 3437417 = 2578063) B2578063
theorem B357343 : Blo 354756 357343 := bstep (se 1 (by rfl) ⟨268007, by rfl⟩ : syracuseStep 357343 = 536015) B536015
theorem B1012763 : Blo 354756 1012763 := bstep (se 1 (by rfl) ⟨759572, by rfl⟩ : syracuseStep 1012763 = 1519145) B1519145
theorem B357407 : Blo 354756 357407 := bstep (se 1 (by rfl) ⟨268055, by rfl⟩ : syracuseStep 357407 = 536111) B536111
theorem B2028671 : Blo 354756 2028671 := bstep (se 1 (by rfl) ⟨1521503, by rfl⟩ : syracuseStep 2028671 = 3043007) B3043007
theorem B357855 : Blo 354756 357855 := bstep (se 1 (by rfl) ⟨268391, by rfl⟩ : syracuseStep 357855 = 536783) B536783
theorem B357935 : Blo 354756 357935 := bstep (se 1 (by rfl) ⟨268451, by rfl⟩ : syracuseStep 357935 = 536903) B536903
theorem B1832507 : Blo 354756 1832507 := bstep (se 1 (by rfl) ⟨1374380, by rfl⟩ : syracuseStep 1832507 = 2748761) B2748761
theorem B1865423 : Blo 354756 1865423 := bstep (se 1 (by rfl) ⟨1399067, by rfl⟩ : syracuseStep 1865423 = 2798135) B2798135
theorem B1013629 : Blo 354756 1013629 := bstep (se 3 (by rfl) ⟨190055, by rfl⟩ : syracuseStep 1013629 = 380111) B380111
theorem B358463 : Blo 354756 358463 := bstep (se 1 (by rfl) ⟨268847, by rfl⟩ : syracuseStep 358463 = 537695) B537695
theorem B358503 : Blo 354756 358503 := bstep (se 1 (by rfl) ⟨268877, by rfl⟩ : syracuseStep 358503 = 537755) B537755
theorem B4160105 : Blo 354756 4160105 := bstep (se 2 (by rfl) ⟨1560039, by rfl⟩ : syracuseStep 4160105 = 3120079) B3120079
theorem B1800953 : Blo 354756 1800953 := bstep (se 2 (by rfl) ⟨675357, by rfl⟩ : syracuseStep 1800953 = 1350715) B1350715
theorem B2751565 : Blo 354756 2751565 := bstep (se 3 (by rfl) ⟨515918, by rfl⟩ : syracuseStep 2751565 = 1031837) B1031837
theorem B1801439 : Blo 354756 1801439 := bstep (se 1 (by rfl) ⟨1351079, by rfl⟩ : syracuseStep 1801439 = 2702159) B2702159
theorem B982343 : Blo 354756 982343 := bstep (se 1 (by rfl) ⟨736757, by rfl⟩ : syracuseStep 982343 = 1473515) B1473515
theorem B47055595 : Blo 354756 47055595 := bstep (se 1 (by rfl) ⟨35291696, by rfl⟩ : syracuseStep 47055595 = 70583393) B70583393
theorem B2033363 : Blo 354756 2033363 := bstep (se 1 (by rfl) ⟨1525022, by rfl⟩ : syracuseStep 2033363 = 3050045) B3050045
theorem B7178129 : Blo 354756 7178129 := bstep (se 2 (by rfl) ⟨2691798, by rfl⟩ : syracuseStep 7178129 = 5383597) B5383597
theorem B7440679 : Blo 354756 7440679 := bstep (se 1 (by rfl) ⟨5580509, by rfl⟩ : syracuseStep 7440679 = 11161019) B11161019
theorem B2034503 : Blo 354756 2034503 := bstep (se 1 (by rfl) ⟨1525877, by rfl⟩ : syracuseStep 2034503 = 3051755) B3051755
theorem B723809 : Blo 354756 723809 := bstep (se 2 (by rfl) ⟨271428, by rfl⟩ : syracuseStep 723809 = 542857) B542857
theorem B4099409 : Blo 354756 4099409 := bstep (se 2 (by rfl) ⟨1537278, by rfl⟩ : syracuseStep 4099409 = 3074557) B3074557
theorem B1543961 : Blo 354756 1543961 := bstep (se 2 (by rfl) ⟨578985, by rfl⟩ : syracuseStep 1543961 = 1157971) B1157971
theorem B2035961 : Blo 354756 2035961 := bstep (se 2 (by rfl) ⟨763485, by rfl⟩ : syracuseStep 2035961 = 1526971) B1526971
theorem B1348271 : Blo 354756 1348271 := bstep (se 1 (by rfl) ⟨1011203, by rfl⟩ : syracuseStep 1348271 = 2022407) B2022407
theorem B1348589 : Blo 354756 1348589 := bstep (se 3 (by rfl) ⟨252860, by rfl⟩ : syracuseStep 1348589 = 505721) B505721
theorem B1840391 : Blo 354756 1840391 := bstep (se 1 (by rfl) ⟨1380293, by rfl⟩ : syracuseStep 1840391 = 2760587) B2760587
theorem B1153273 : Blo 354756 1153273 := bstep (se 2 (by rfl) ⟨432477, by rfl⟩ : syracuseStep 1153273 = 864955) B864955
theorem B4561535 : Blo 354756 4561535 := bstep (se 1 (by rfl) ⟨3421151, by rfl⟩ : syracuseStep 4561535 = 6842303) B6842303
theorem B1351187 : Blo 354756 1351187 := bstep (se 1 (by rfl) ⟨1013390, by rfl⟩ : syracuseStep 1351187 = 2026781) B2026781
theorem B1351505 : Blo 354756 1351505 := bstep (se 2 (by rfl) ⟨506814, by rfl⟩ : syracuseStep 1351505 = 1013629) B1013629
theorem B532601 : Blo 354756 532601 := bstep (se 2 (by rfl) ⟨199725, by rfl⟩ : syracuseStep 532601 = 399451) B399451
theorem B19538657 : Blo 354756 19538657 := bstep (se 2 (by rfl) ⟨7326996, by rfl⟩ : syracuseStep 19538657 = 14653993) B14653993
theorem B1352447 : Blo 354756 1352447 := bstep (se 1 (by rfl) ⟨1014335, by rfl⟩ : syracuseStep 1352447 = 2028671) B2028671
theorem B1221671 : Blo 354756 1221671 := bstep (se 1 (by rfl) ⟨916253, by rfl⟩ : syracuseStep 1221671 = 1832507) B1832507
theorem B599359 : Blo 354756 599359 := bstep (se 1 (by rfl) ⟨449519, by rfl⟩ : syracuseStep 599359 = 899039) B899039
theorem B534071 : Blo 354756 534071 := bstep (se 1 (by rfl) ⟨400553, by rfl⟩ : syracuseStep 534071 = 801107) B801107
theorem B534119 : Blo 354756 534119 := bstep (se 1 (by rfl) ⟨400589, by rfl⟩ : syracuseStep 534119 = 801179) B801179
theorem B534383 : Blo 354756 534383 := bstep (se 1 (by rfl) ⟨400787, by rfl⟩ : syracuseStep 534383 = 801575) B801575
theorem B600041 : Blo 354756 600041 := bstep (se 2 (by rfl) ⟨225015, by rfl⟩ : syracuseStep 600041 = 450031) B450031
theorem B2697785 : Blo 354756 2697785 := bstep (se 2 (by rfl) ⟨1011669, by rfl⟩ : syracuseStep 2697785 = 2023339) B2023339
theorem B535295 : Blo 354756 535295 := bstep (se 1 (by rfl) ⟨401471, by rfl⟩ : syracuseStep 535295 = 802943) B802943
theorem B3058519 : Blo 354756 3058519 := bstep (se 1 (by rfl) ⟨2293889, by rfl⟩ : syracuseStep 3058519 = 4587779) B4587779
theorem B535607 : Blo 354756 535607 := bstep (se 1 (by rfl) ⟨401705, by rfl⟩ : syracuseStep 535607 = 803411) B803411
theorem B3058793 : Blo 354756 3058793 := bstep (se 2 (by rfl) ⟨1147047, by rfl⟩ : syracuseStep 3058793 = 2294095) B2294095
theorem B1354877 : Blo 354756 1354877 := bstep (se 3 (by rfl) ⟨254039, by rfl⟩ : syracuseStep 1354877 = 508079) B508079
theorem B568495 : Blo 354756 568495 := bstep (se 1 (by rfl) ⟨426371, by rfl⟩ : syracuseStep 568495 = 852743) B852743
theorem B535787 : Blo 354756 535787 := bstep (se 1 (by rfl) ⟨401840, by rfl⟩ : syracuseStep 535787 = 803681) B803681
theorem B1355089 : Blo 354756 1355089 := bstep (se 2 (by rfl) ⟨508158, by rfl⟩ : syracuseStep 1355089 = 1016317) B1016317
theorem B536105 : Blo 354756 536105 := bstep (se 2 (by rfl) ⟨201039, by rfl⟩ : syracuseStep 536105 = 402079) B402079
theorem B8793647 : Blo 354756 8793647 := bstep (se 1 (by rfl) ⟨6595235, by rfl⟩ : syracuseStep 8793647 = 13190471) B13190471
theorem B5124005 : Blo 354756 5124005 := bstep (se 4 (by rfl) ⟨480375, by rfl⟩ : syracuseStep 5124005 = 960751) B960751
theorem B536519 : Blo 354756 536519 := bstep (se 1 (by rfl) ⟨402389, by rfl⟩ : syracuseStep 536519 = 804779) B804779
theorem B536603 : Blo 354756 536603 := bstep (se 1 (by rfl) ⟨402452, by rfl⟩ : syracuseStep 536603 = 804905) B804905
theorem B1814561 : Blo 354756 1814561 := bstep (se 2 (by rfl) ⟨680460, by rfl⟩ : syracuseStep 1814561 = 1360921) B1360921
theorem B1519897 : Blo 354756 1519897 := bstep (se 2 (by rfl) ⟨569961, by rfl⟩ : syracuseStep 1519897 = 1139923) B1139923
theorem B1716727 : Blo 354756 1716727 := bstep (se 1 (by rfl) ⟨1287545, by rfl⟩ : syracuseStep 1716727 = 2575091) B2575091
theorem B537179 : Blo 354756 537179 := bstep (se 1 (by rfl) ⟨402884, by rfl⟩ : syracuseStep 537179 = 805769) B805769
theorem B3060503 : Blo 354756 3060503 := bstep (se 1 (by rfl) ⟨2295377, by rfl⟩ : syracuseStep 3060503 = 4590755) B4590755
theorem B800027 : Blo 354756 800027 := bstep (se 1 (by rfl) ⟨600020, by rfl⟩ : syracuseStep 800027 = 1200041) B1200041
theorem B2700701 : Blo 354756 2700701 := bstep (se 3 (by rfl) ⟨506381, by rfl⟩ : syracuseStep 2700701 = 1012763) B1012763
theorem B538025 : Blo 354756 538025 := bstep (se 2 (by rfl) ⟨201759, by rfl⟩ : syracuseStep 538025 = 403519) B403519
theorem B538079 : Blo 354756 538079 := bstep (se 1 (by rfl) ⟨403559, by rfl⟩ : syracuseStep 538079 = 807119) B807119
theorem B9221795 : Blo 354756 9221795 := bstep (se 1 (by rfl) ⟨6916346, by rfl⟩ : syracuseStep 9221795 = 13832693) B13832693
theorem B898735 : Blo 354756 898735 := bstep (se 1 (by rfl) ⟨674051, by rfl⟩ : syracuseStep 898735 = 1348103) B1348103
theorem B801161 : Blo 354756 801161 := bstep (se 2 (by rfl) ⟨300435, by rfl⟩ : syracuseStep 801161 = 600871) B600871
theorem B899819 : Blo 354756 899819 := bstep (se 1 (by rfl) ⟨674864, by rfl⟩ : syracuseStep 899819 = 1349729) B1349729
theorem B900143 : Blo 354756 900143 := bstep (se 1 (by rfl) ⟨675107, by rfl⟩ : syracuseStep 900143 = 1350215) B1350215
theorem B900335 : Blo 354756 900335 := bstep (se 1 (by rfl) ⟨675251, by rfl⟩ : syracuseStep 900335 = 1350503) B1350503
theorem B802169 : Blo 354756 802169 := bstep (se 2 (by rfl) ⟨300813, by rfl⟩ : syracuseStep 802169 = 601627) B601627
theorem B802223 : Blo 354756 802223 := bstep (se 1 (by rfl) ⟨601667, by rfl⟩ : syracuseStep 802223 = 1203335) B1203335
theorem B901115 : Blo 354756 901115 := bstep (se 1 (by rfl) ⟨675836, by rfl⟩ : syracuseStep 901115 = 1351673) B1351673
theorem B1359935 : Blo 354756 1359935 := bstep (se 1 (by rfl) ⟨1019951, by rfl⟩ : syracuseStep 1359935 = 2039903) B2039903
theorem B9159155 : Blo 354756 9159155 := bstep (se 1 (by rfl) ⟨6869366, by rfl⟩ : syracuseStep 9159155 = 13738733) B13738733
theorem B2704103 : Blo 354756 2704103 := bstep (se 1 (by rfl) ⟨2028077, by rfl⟩ : syracuseStep 2704103 = 4056155) B4056155
theorem B6341777 : Blo 354756 6341777 := bstep (se 2 (by rfl) ⟨2378166, by rfl⟩ : syracuseStep 6341777 = 4756333) B4756333
theorem B1197341 : Blo 354756 1197341 := bstep (se 3 (by rfl) ⟨224501, by rfl⟩ : syracuseStep 1197341 = 449003) B449003
theorem B804455 : Blo 354756 804455 := bstep (se 1 (by rfl) ⟨603341, by rfl⟩ : syracuseStep 804455 = 1206683) B1206683
theorem B43698311 : Blo 354756 43698311 := bstep (se 1 (by rfl) ⟨32773733, by rfl⟩ : syracuseStep 43698311 = 65547467) B65547467
theorem B8276201 : Blo 354756 8276201 := bstep (se 2 (by rfl) ⟨3103575, by rfl⟩ : syracuseStep 8276201 = 6207151) B6207151
theorem B805139 : Blo 354756 805139 := bstep (se 1 (by rfl) ⟨603854, by rfl⟩ : syracuseStep 805139 = 1207709) B1207709
theorem B1198367 : Blo 354756 1198367 := bstep (se 1 (by rfl) ⟨898775, by rfl⟩ : syracuseStep 1198367 = 1797551) B1797551
theorem B2706047 : Blo 354756 2706047 := bstep (se 1 (by rfl) ⟨2029535, by rfl⟩ : syracuseStep 2706047 = 4059071) B4059071
theorem B806201 : Blo 354756 806201 := bstep (se 2 (by rfl) ⟨302325, by rfl⟩ : syracuseStep 806201 = 604651) B604651
theorem B642671 : Blo 354756 642671 := bstep (se 1 (by rfl) ⟨482003, by rfl⟩ : syracuseStep 642671 = 964007) B964007
theorem B675449 : Blo 354756 675449 := bstep (se 2 (by rfl) ⟨253293, by rfl⟩ : syracuseStep 675449 = 506587) B506587
theorem B2773403 : Blo 354756 2773403 := bstep (se 1 (by rfl) ⟨2080052, by rfl⟩ : syracuseStep 2773403 = 4160105) B4160105
theorem B1200635 : Blo 354756 1200635 := bstep (se 1 (by rfl) ⟨900476, by rfl⟩ : syracuseStep 1200635 = 1800953) B1800953
theorem B1200959 : Blo 354756 1200959 := bstep (se 1 (by rfl) ⟨900719, by rfl⟩ : syracuseStep 1200959 = 1801439) B1801439
theorem B677089 : Blo 354756 677089 := bstep (se 2 (by rfl) ⟨253908, by rfl⟩ : syracuseStep 677089 = 507817) B507817
theorem B6510617 : Blo 354756 6510617 := bstep (se 2 (by rfl) ⟨2441481, by rfl⟩ : syracuseStep 6510617 = 4882963) B4882963
theorem B5495795 : Blo 354756 5495795 := bstep (se 1 (by rfl) ⟨4121846, by rfl⟩ : syracuseStep 5495795 = 8243693) B8243693
theorem B5168123 : Blo 354756 5168123 := bstep (se 1 (by rfl) ⟨3876092, by rfl⟩ : syracuseStep 5168123 = 7752185) B7752185
theorem B1137719 : Blo 354756 1137719 := bstep (se 1 (by rfl) ⟨853289, by rfl⟩ : syracuseStep 1137719 = 1706579) B1706579
theorem B679079 : Blo 354756 679079 := bstep (se 1 (by rfl) ⟨509309, by rfl⟩ : syracuseStep 679079 = 1018619) B1018619
theorem B613615 : Blo 354756 613615 := bstep (se 1 (by rfl) ⟨460211, by rfl⟩ : syracuseStep 613615 = 920423) B920423
theorem B11525627 : Blo 354756 11525627 := bstep (se 1 (by rfl) ⟨8644220, by rfl⟩ : syracuseStep 11525627 = 17288441) B17288441
theorem B2285279 : Blo 354756 2285279 := bstep (se 1 (by rfl) ⟨1713959, by rfl⟩ : syracuseStep 2285279 = 3427919) B3427919
theorem B18013985 : Blo 354756 18013985 := bstep (se 2 (by rfl) ⟨6755244, by rfl⟩ : syracuseStep 18013985 = 13510489) B13510489
theorem B88137557 : Blo 354756 88137557 := bstep (se 9 (by rfl) ⟨258215, by rfl⟩ : syracuseStep 88137557 = 516431) B516431
theorem B2711393 : Blo 354756 2711393 := bstep (se 2 (by rfl) ⟨1016772, by rfl⟩ : syracuseStep 2711393 = 2033545) B2033545
theorem B1204199 : Blo 354756 1204199 := bstep (se 1 (by rfl) ⟨903149, by rfl⟩ : syracuseStep 1204199 = 1806299) B1806299
theorem B2711879 : Blo 354756 2711879 := bstep (se 1 (by rfl) ⟨2033909, by rfl⟩ : syracuseStep 2711879 = 4067819) B4067819
theorem B680795 : Blo 354756 680795 := bstep (se 1 (by rfl) ⟨510596, by rfl⟩ : syracuseStep 680795 = 1021193) B1021193
theorem B4548413 : Blo 354756 4548413 := bstep (se 3 (by rfl) ⟨852827, by rfl⟩ : syracuseStep 4548413 = 1705655) B1705655
theorem B2287997 : Blo 354756 2287997 := bstep (se 3 (by rfl) ⟨428999, by rfl⟩ : syracuseStep 2287997 = 857999) B857999
theorem B1010303 : Blo 354756 1010303 := bstep (se 1 (by rfl) ⟨757727, by rfl⟩ : syracuseStep 1010303 = 1515455) B1515455
theorem B1010713 : Blo 354756 1010713 := bstep (se 2 (by rfl) ⟨379017, by rfl⟩ : syracuseStep 1010713 = 758035) B758035
theorem B3042359 : Blo 354756 3042359 := bstep (se 1 (by rfl) ⟨2281769, by rfl⟩ : syracuseStep 3042359 = 4563539) B4563539
theorem B683743 : Blo 354756 683743 := bstep (se 1 (by rfl) ⟨512807, by rfl⟩ : syracuseStep 683743 = 1025615) B1025615
theorem B356263 : Blo 354756 356263 := bstep (se 1 (by rfl) ⟨267197, by rfl⟩ : syracuseStep 356263 = 534395) B534395
theorem B1798199 : Blo 354756 1798199 := bstep (se 1 (by rfl) ⟨1348649, by rfl⟩ : syracuseStep 1798199 = 2697299) B2697299
theorem B356423 : Blo 354756 356423 := bstep (se 1 (by rfl) ⟨267317, by rfl⟩ : syracuseStep 356423 = 534635) B534635
theorem B356575 : Blo 354756 356575 := bstep (se 1 (by rfl) ⟨267431, by rfl⟩ : syracuseStep 356575 = 534863) B534863
theorem B1208735 : Blo 354756 1208735 := bstep (se 1 (by rfl) ⟨906551, by rfl⟩ : syracuseStep 1208735 = 1813103) B1813103
theorem B1012331 : Blo 354756 1012331 := bstep (se 1 (by rfl) ⟨759248, by rfl⟩ : syracuseStep 1012331 = 1518497) B1518497
theorem B652063 : Blo 354756 652063 := bstep (se 1 (by rfl) ⟨489047, by rfl⟩ : syracuseStep 652063 = 978095) B978095
theorem B357151 : Blo 354756 357151 := bstep (se 1 (by rfl) ⟨267863, by rfl⟩ : syracuseStep 357151 = 535727) B535727
theorem B1799009 : Blo 354756 1799009 := bstep (se 2 (by rfl) ⟨674628, by rfl⟩ : syracuseStep 1799009 = 1349257) B1349257
theorem B357599 : Blo 354756 357599 := bstep (se 1 (by rfl) ⟨268199, by rfl⟩ : syracuseStep 357599 = 536399) B536399
theorem B357631 : Blo 354756 357631 := bstep (se 1 (by rfl) ⟨268223, by rfl⟩ : syracuseStep 357631 = 536447) B536447
theorem B357919 : Blo 354756 357919 := bstep (se 1 (by rfl) ⟨268439, by rfl⟩ : syracuseStep 357919 = 536879) B536879
theorem B2029171 : Blo 354756 2029171 := bstep (se 1 (by rfl) ⟨1521878, by rfl⟩ : syracuseStep 2029171 = 3043757) B3043757
theorem B1439407 : Blo 354756 1439407 := bstep (se 1 (by rfl) ⟨1079555, by rfl⟩ : syracuseStep 1439407 = 2159111) B2159111
theorem B358079 : Blo 354756 358079 := bstep (se 1 (by rfl) ⟨268559, by rfl⟩ : syracuseStep 358079 = 537119) B537119
theorem B2291611 : Blo 354756 2291611 := bstep (se 1 (by rfl) ⟨1718708, by rfl⟩ : syracuseStep 2291611 = 3437417) B3437417
theorem B10975337 : Blo 354756 10975337 := bstep (se 2 (by rfl) ⟨4115751, by rfl⟩ : syracuseStep 10975337 = 8231503) B8231503
theorem B358511 : Blo 354756 358511 := bstep (se 1 (by rfl) ⟨268883, by rfl⟩ : syracuseStep 358511 = 537767) B537767
theorem B3045671 : Blo 354756 3045671 := bstep (se 1 (by rfl) ⟨2284253, by rfl⟩ : syracuseStep 3045671 = 4568507) B4568507
theorem B1243615 : Blo 354756 1243615 := bstep (se 1 (by rfl) ⟨932711, by rfl⟩ : syracuseStep 1243615 = 1865423) B1865423
theorem B3668753 : Blo 354756 3668753 := bstep (se 2 (by rfl) ⟨1375782, by rfl⟩ : syracuseStep 3668753 = 2751565) B2751565
theorem B1145639 : Blo 354756 1145639 := bstep (se 1 (by rfl) ⟨859229, by rfl⟩ : syracuseStep 1145639 = 1718459) B1718459
theorem B1014905 : Blo 354756 1014905 := bstep (se 2 (by rfl) ⟨380589, by rfl⟩ : syracuseStep 1014905 = 761179) B761179
theorem B654895 : Blo 354756 654895 := bstep (se 1 (by rfl) ⟨491171, by rfl⟩ : syracuseStep 654895 = 982343) B982343
theorem B5144417 : Blo 354756 5144417 := bstep (se 2 (by rfl) ⟨1929156, by rfl⟩ : syracuseStep 5144417 = 3858313) B3858313
theorem B1802735 : Blo 354756 1802735 := bstep (se 1 (by rfl) ⟨1352051, by rfl⟩ : syracuseStep 1802735 = 2704103) B2704103
theorem B4227851 : Blo 354756 4227851 := bstep (se 1 (by rfl) ⟨3170888, by rfl⟩ : syracuseStep 4227851 = 6341777) B6341777
theorem B4785419 : Blo 354756 4785419 := bstep (se 1 (by rfl) ⟨3589064, by rfl⟩ : syracuseStep 4785419 = 7178129) B7178129
theorem B29132207 : Blo 354756 29132207 := bstep (se 1 (by rfl) ⟨21849155, by rfl⟩ : syracuseStep 29132207 = 43698311) B43698311
theorem B39683621 : Blo 354756 39683621 := bstep (se 4 (by rfl) ⟨3720339, by rfl⟩ : syracuseStep 39683621 = 7440679) B7440679
theorem B1804031 : Blo 354756 1804031 := bstep (se 1 (by rfl) ⟨1353023, by rfl⟩ : syracuseStep 1804031 = 2706047) B2706047
theorem B428447 : Blo 354756 428447 := bstep (se 1 (by rfl) ⟨321335, by rfl⟩ : syracuseStep 428447 = 642671) B642671
theorem B1347617 : Blo 354756 1347617 := bstep (se 2 (by rfl) ⟨505356, by rfl⟩ : syracuseStep 1347617 = 1010713) B1010713
theorem B757993 : Blo 354756 757993 := bstep (se 2 (by rfl) ⟨284247, by rfl⟩ : syracuseStep 757993 = 568495) B568495
theorem B1806785 : Blo 354756 1806785 := bstep (se 2 (by rfl) ⟨677544, by rfl⟩ : syracuseStep 1806785 = 1355089) B1355089
theorem B3445415 : Blo 354756 3445415 := bstep (se 1 (by rfl) ⟨2584061, by rfl⟩ : syracuseStep 3445415 = 5168123) B5168123
theorem B758479 : Blo 354756 758479 := bstep (se 1 (by rfl) ⟨568859, by rfl⟩ : syracuseStep 758479 = 1137719) B1137719
theorem B58758371 : Blo 354756 58758371 := bstep (se 1 (by rfl) ⟨44068778, by rfl⟩ : syracuseStep 58758371 = 88137557) B88137557
theorem B1807595 : Blo 354756 1807595 := bstep (se 1 (by rfl) ⟨1355696, by rfl⟩ : syracuseStep 1807595 = 2711393) B2711393
theorem B1807919 : Blo 354756 1807919 := bstep (se 1 (by rfl) ⟨1355939, by rfl⟩ : syracuseStep 1807919 = 2711879) B2711879
theorem B400027 : Blo 354756 400027 := bstep (se 1 (by rfl) ⟨300020, by rfl⟩ : syracuseStep 400027 = 600041) B600041
theorem B2039195 : Blo 354756 2039195 := bstep (se 1 (by rfl) ⟨1529396, by rfl⟩ : syracuseStep 2039195 = 3058793) B3058793
theorem B3055481 : Blo 354756 3055481 := bstep (se 2 (by rfl) ⟨1145805, by rfl⟩ : syracuseStep 3055481 = 2291611) B2291611
theorem B3416003 : Blo 354756 3416003 := bstep (se 1 (by rfl) ⟨2562002, by rfl⟩ : syracuseStep 3416003 = 5124005) B5124005
theorem B2040335 : Blo 354756 2040335 := bstep (se 1 (by rfl) ⟨1530251, by rfl⟩ : syracuseStep 2040335 = 3060503) B3060503
theorem B533351 : Blo 354756 533351 := bstep (se 1 (by rfl) ⟨400013, by rfl⟩ : syracuseStep 533351 = 800027) B800027
theorem B7316891 : Blo 354756 7316891 := bstep (se 1 (by rfl) ⟨5487668, by rfl⟩ : syracuseStep 7316891 = 10975337) B10975337
theorem B534107 : Blo 354756 534107 := bstep (se 1 (by rfl) ⟨400580, by rfl⟩ : syracuseStep 534107 = 801161) B801161
theorem B599879 : Blo 354756 599879 := bstep (se 1 (by rfl) ⟨449909, by rfl⟩ : syracuseStep 599879 = 899819) B899819
theorem B763759 : Blo 354756 763759 := bstep (se 1 (by rfl) ⟨572819, by rfl⟩ : syracuseStep 763759 = 1145639) B1145639
theorem B600095 : Blo 354756 600095 := bstep (se 1 (by rfl) ⟨450071, by rfl⟩ : syracuseStep 600095 = 900143) B900143
theorem B600223 : Blo 354756 600223 := bstep (se 1 (by rfl) ⟨450167, by rfl⟩ : syracuseStep 600223 = 900335) B900335
theorem B534779 : Blo 354756 534779 := bstep (se 1 (by rfl) ⟨401084, by rfl⟩ : syracuseStep 534779 = 802169) B802169
theorem B534815 : Blo 354756 534815 := bstep (se 1 (by rfl) ⟨401111, by rfl⟩ : syracuseStep 534815 = 802223) B802223
theorem B600743 : Blo 354756 600743 := bstep (se 1 (by rfl) ⟨450557, by rfl⟩ : syracuseStep 600743 = 901115) B901115
theorem B6106103 : Blo 354756 6106103 := bstep (se 1 (by rfl) ⟨4579577, by rfl⟩ : syracuseStep 6106103 = 9159155) B9159155
theorem B798227 : Blo 354756 798227 := bstep (se 1 (by rfl) ⟨598670, by rfl⟩ : syracuseStep 798227 = 1197341) B1197341
theorem B536303 : Blo 354756 536303 := bstep (se 1 (by rfl) ⟨402227, by rfl⟩ : syracuseStep 536303 = 804455) B804455
theorem B1355575 : Blo 354756 1355575 := bstep (se 1 (by rfl) ⟨1016681, by rfl⟩ : syracuseStep 1355575 = 2033363) B2033363
theorem B5517467 : Blo 354756 5517467 := bstep (se 1 (by rfl) ⟨4138100, by rfl⟩ : syracuseStep 5517467 = 8276201) B8276201
theorem B536759 : Blo 354756 536759 := bstep (se 1 (by rfl) ⟨402569, by rfl⟩ : syracuseStep 536759 = 805139) B805139
theorem B798911 : Blo 354756 798911 := bstep (se 1 (by rfl) ⟨599183, by rfl⟩ : syracuseStep 798911 = 1198367) B1198367
theorem B799145 : Blo 354756 799145 := bstep (se 2 (by rfl) ⟨299679, by rfl⟩ : syracuseStep 799145 = 599359) B599359
theorem B1356335 : Blo 354756 1356335 := bstep (se 1 (by rfl) ⟨1017251, by rfl⟩ : syracuseStep 1356335 = 2034503) B2034503
theorem B537467 : Blo 354756 537467 := bstep (se 1 (by rfl) ⟨403100, by rfl⟩ : syracuseStep 537467 = 806201) B806201
theorem B2732939 : Blo 354756 2732939 := bstep (se 1 (by rfl) ⟨2049704, by rfl⟩ : syracuseStep 2732939 = 4099409) B4099409
theorem B1357307 : Blo 354756 1357307 := bstep (se 1 (by rfl) ⟨1017980, by rfl⟩ : syracuseStep 1357307 = 2035961) B2035961
theorem B1848935 : Blo 354756 1848935 := bstep (se 1 (by rfl) ⟨1386701, by rfl⟩ : syracuseStep 1848935 = 2773403) B2773403
theorem B800423 : Blo 354756 800423 := bstep (se 1 (by rfl) ⟨600317, by rfl⟩ : syracuseStep 800423 = 1200635) B1200635
theorem B898847 : Blo 354756 898847 := bstep (se 1 (by rfl) ⟨674135, by rfl⟩ : syracuseStep 898847 = 1348271) B1348271
theorem B800639 : Blo 354756 800639 := bstep (se 1 (by rfl) ⟨600479, by rfl⟩ : syracuseStep 800639 = 1200959) B1200959
theorem B899059 : Blo 354756 899059 := bstep (se 1 (by rfl) ⟨674294, by rfl⟩ : syracuseStep 899059 = 1348589) B1348589
theorem B1226927 : Blo 354756 1226927 := bstep (se 1 (by rfl) ⟨920195, by rfl⟩ : syracuseStep 1226927 = 1840391) B1840391
theorem B4078025 : Blo 354756 4078025 := bstep (se 2 (by rfl) ⟨1529259, by rfl⟩ : syracuseStep 4078025 = 3058519) B3058519
theorem B4340411 : Blo 354756 4340411 := bstep (se 1 (by rfl) ⟨3255308, by rfl⟩ : syracuseStep 4340411 = 6510617) B6510617
theorem B7683751 : Blo 354756 7683751 := bstep (se 1 (by rfl) ⟨5762813, by rfl⟩ : syracuseStep 7683751 = 11525627) B11525627
theorem B900791 : Blo 354756 900791 := bstep (se 1 (by rfl) ⟨675593, by rfl⟩ : syracuseStep 900791 = 1351187) B1351187
theorem B1523519 : Blo 354756 1523519 := bstep (se 1 (by rfl) ⟨1142639, by rfl⟩ : syracuseStep 1523519 = 2285279) B2285279
theorem B12009323 : Blo 354756 12009323 := bstep (se 1 (by rfl) ⟨9006992, by rfl⟩ : syracuseStep 12009323 = 18013985) B18013985
theorem B901003 : Blo 354756 901003 := bstep (se 1 (by rfl) ⟨675752, by rfl⟩ : syracuseStep 901003 = 1351505) B1351505
theorem B802799 : Blo 354756 802799 := bstep (se 1 (by rfl) ⟨602099, by rfl⟩ : syracuseStep 802799 = 1204199) B1204199
theorem B13025771 : Blo 354756 13025771 := bstep (se 1 (by rfl) ⟨9769328, by rfl⟩ : syracuseStep 13025771 = 19538657) B19538657
theorem B901631 : Blo 354756 901631 := bstep (se 1 (by rfl) ⟨676223, by rfl⟩ : syracuseStep 901631 = 1352447) B1352447
theorem B869417 : Blo 354756 869417 := bstep (se 2 (by rfl) ⟨326031, by rfl⟩ : syracuseStep 869417 = 652063) B652063
theorem B3032275 : Blo 354756 3032275 := bstep (se 1 (by rfl) ⟨2274206, by rfl⟩ : syracuseStep 3032275 = 4548413) B4548413
theorem B1525331 : Blo 354756 1525331 := bstep (se 1 (by rfl) ⟨1143998, by rfl⟩ : syracuseStep 1525331 = 2287997) B2287997
theorem B902785 : Blo 354756 902785 := bstep (se 2 (by rfl) ⟨338544, by rfl⟩ : syracuseStep 902785 = 677089) B677089
theorem B673535 : Blo 354756 673535 := bstep (se 1 (by rfl) ⟨505151, by rfl⟩ : syracuseStep 673535 = 1010303) B1010303
theorem B9783341 : Blo 354756 9783341 := bstep (se 3 (by rfl) ⟨1834376, by rfl⟩ : syracuseStep 9783341 = 3668753) B3668753
theorem B903251 : Blo 354756 903251 := bstep (se 1 (by rfl) ⟨677438, by rfl⟩ : syracuseStep 903251 = 1354877) B1354877
theorem B2705561 : Blo 354756 2705561 := bstep (se 2 (by rfl) ⟨1014585, by rfl⟩ : syracuseStep 2705561 = 2029171) B2029171
theorem B1919209 : Blo 354756 1919209 := bstep (se 2 (by rfl) ⟨719703, by rfl⟩ : syracuseStep 1919209 = 1439407) B1439407
theorem B1198313 : Blo 354756 1198313 := bstep (se 2 (by rfl) ⟨449367, by rfl⟩ : syracuseStep 1198313 = 898735) B898735
theorem B1198799 : Blo 354756 1198799 := bstep (se 1 (by rfl) ⟨899099, by rfl⟩ : syracuseStep 1198799 = 1798199) B1798199
theorem B3492773 : Blo 354756 3492773 := bstep (se 4 (by rfl) ⟨327447, by rfl⟩ : syracuseStep 3492773 = 654895) B654895
theorem B805823 : Blo 354756 805823 := bstep (se 1 (by rfl) ⟨604367, by rfl⟩ : syracuseStep 805823 = 1208735) B1208735
theorem B674887 : Blo 354756 674887 := bstep (se 1 (by rfl) ⟨506165, by rfl⟩ : syracuseStep 674887 = 1012331) B1012331
theorem B1199339 : Blo 354756 1199339 := bstep (se 1 (by rfl) ⟨899504, by rfl⟩ : syracuseStep 1199339 = 1799009) B1799009
theorem B1658153 : Blo 354756 1658153 := bstep (se 2 (by rfl) ⟨621807, by rfl⟩ : syracuseStep 1658153 = 1243615) B1243615
theorem B6147863 : Blo 354756 6147863 := bstep (se 1 (by rfl) ⟨4610897, by rfl⟩ : syracuseStep 6147863 = 9221795) B9221795
theorem B4117229 : Blo 354756 4117229 := bstep (se 3 (by rfl) ⟨771980, by rfl⟩ : syracuseStep 4117229 = 1543961) B1543961
theorem B676603 : Blo 354756 676603 := bstep (se 1 (by rfl) ⟨507452, by rfl⟩ : syracuseStep 676603 = 1014905) B1014905
theorem B3429611 : Blo 354756 3429611 := bstep (se 1 (by rfl) ⟨2572208, by rfl⟩ : syracuseStep 3429611 = 5144417) B5144417
theorem B906623 : Blo 354756 906623 := bstep (se 1 (by rfl) ⟨679967, by rfl⟩ : syracuseStep 906623 = 1359935) B1359935
theorem B62740793 : Blo 354756 62740793 := bstep (se 2 (by rfl) ⟨23527797, by rfl⟩ : syracuseStep 62740793 = 47055595) B47055595
theorem B482539 : Blo 354756 482539 := bstep (se 1 (by rfl) ⟨361904, by rfl⟩ : syracuseStep 482539 = 723809) B723809
theorem B450299 : Blo 354756 450299 := bstep (se 1 (by rfl) ⟨337724, by rfl⟩ : syracuseStep 450299 = 675449) B675449
theorem B3041023 : Blo 354756 3041023 := bstep (se 1 (by rfl) ⟨2280767, by rfl⟩ : syracuseStep 3041023 = 4561535) B4561535
theorem B3663863 : Blo 354756 3663863 := bstep (se 1 (by rfl) ⟨2747897, by rfl⟩ : syracuseStep 3663863 = 5495795) B5495795
theorem B452719 : Blo 354756 452719 := bstep (se 1 (by rfl) ⟨339539, by rfl⟩ : syracuseStep 452719 = 679079) B679079
theorem B911657 : Blo 354756 911657 := bstep (se 2 (by rfl) ⟨341871, by rfl⟩ : syracuseStep 911657 = 683743) B683743
theorem B355067 : Blo 354756 355067 := bstep (se 1 (by rfl) ⟨266300, by rfl⟩ : syracuseStep 355067 = 532601) B532601
theorem B2026529 : Blo 354756 2026529 := bstep (se 2 (by rfl) ⟨759948, by rfl⟩ : syracuseStep 2026529 = 1519897) B1519897
theorem B453863 : Blo 354756 453863 := bstep (se 1 (by rfl) ⟨340397, by rfl⟩ : syracuseStep 453863 = 680795) B680795
theorem B2288969 : Blo 354756 2288969 := bstep (se 2 (by rfl) ⟨858363, by rfl⟩ : syracuseStep 2288969 = 1716727) B1716727
theorem B814447 : Blo 354756 814447 := bstep (se 1 (by rfl) ⟨610835, by rfl⟩ : syracuseStep 814447 = 1221671) B1221671
theorem B356047 : Blo 354756 356047 := bstep (se 1 (by rfl) ⟨267035, by rfl⟩ : syracuseStep 356047 = 534071) B534071
theorem B356079 : Blo 354756 356079 := bstep (se 1 (by rfl) ⟨267059, by rfl⟩ : syracuseStep 356079 = 534119) B534119
theorem B356255 : Blo 354756 356255 := bstep (se 1 (by rfl) ⟨267191, by rfl⟩ : syracuseStep 356255 = 534383) B534383
theorem B1798523 : Blo 354756 1798523 := bstep (se 1 (by rfl) ⟨1348892, by rfl⟩ : syracuseStep 1798523 = 2697785) B2697785
theorem B356863 : Blo 354756 356863 := bstep (se 1 (by rfl) ⟨267647, by rfl⟩ : syracuseStep 356863 = 535295) B535295
theorem B2028239 : Blo 354756 2028239 := bstep (se 1 (by rfl) ⟨1521179, by rfl⟩ : syracuseStep 2028239 = 3042359) B3042359
theorem B357071 : Blo 354756 357071 := bstep (se 1 (by rfl) ⟨267803, by rfl⟩ : syracuseStep 357071 = 535607) B535607
theorem B357191 : Blo 354756 357191 := bstep (se 1 (by rfl) ⟨267893, by rfl⟩ : syracuseStep 357191 = 535787) B535787
theorem B357403 : Blo 354756 357403 := bstep (se 1 (by rfl) ⟨268052, by rfl⟩ : syracuseStep 357403 = 536105) B536105
theorem B5862431 : Blo 354756 5862431 := bstep (se 1 (by rfl) ⟨4396823, by rfl⟩ : syracuseStep 5862431 = 8793647) B8793647
theorem B357679 : Blo 354756 357679 := bstep (se 1 (by rfl) ⟨268259, by rfl⟩ : syracuseStep 357679 = 536519) B536519
theorem B357735 : Blo 354756 357735 := bstep (se 1 (by rfl) ⟨268301, by rfl⟩ : syracuseStep 357735 = 536603) B536603
theorem B1209707 : Blo 354756 1209707 := bstep (se 1 (by rfl) ⟨907280, by rfl⟩ : syracuseStep 1209707 = 1814561) B1814561
theorem B1537697 : Blo 354756 1537697 := bstep (se 2 (by rfl) ⟨576636, by rfl⟩ : syracuseStep 1537697 = 1153273) B1153273
theorem B358119 : Blo 354756 358119 := bstep (se 1 (by rfl) ⟨268589, by rfl⟩ : syracuseStep 358119 = 537179) B537179
theorem B1800467 : Blo 354756 1800467 := bstep (se 1 (by rfl) ⟨1350350, by rfl⟩ : syracuseStep 1800467 = 2700701) B2700701
theorem B358683 : Blo 354756 358683 := bstep (se 1 (by rfl) ⟨269012, by rfl⟩ : syracuseStep 358683 = 538025) B538025
theorem B358719 : Blo 354756 358719 := bstep (se 1 (by rfl) ⟨269039, by rfl⟩ : syracuseStep 358719 = 538079) B538079
theorem B2030447 : Blo 354756 2030447 := bstep (se 1 (by rfl) ⟨1522835, by rfl⟩ : syracuseStep 2030447 = 3045671) B3045671
theorem B818153 : Blo 354756 818153 := bstep (se 2 (by rfl) ⟨306807, by rfl⟩ : syracuseStep 818153 = 613615) B613615
theorem B8683847 : Blo 354756 8683847 := bstep (se 1 (by rfl) ⟨6512885, by rfl⟩ : syracuseStep 8683847 = 13025771) B13025771
theorem B2818567 : Blo 354756 2818567 := bstep (se 1 (by rfl) ⟨2113925, by rfl⟩ : syracuseStep 2818567 = 4227851) B4227851
theorem B1016887 : Blo 354756 1016887 := bstep (se 1 (by rfl) ⟨762665, by rfl⟩ : syracuseStep 1016887 = 1525331) B1525331
theorem B6522227 : Blo 354756 6522227 := bstep (se 1 (by rfl) ⟨4891670, by rfl⟩ : syracuseStep 6522227 = 9783341) B9783341
theorem B1803707 : Blo 354756 1803707 := bstep (se 1 (by rfl) ⟨1352780, by rfl⟩ : syracuseStep 1803707 = 2705561) B2705561
theorem B2328515 : Blo 354756 2328515 := bstep (se 1 (by rfl) ⟨1746386, by rfl⟩ : syracuseStep 2328515 = 3492773) B3492773
theorem B1018345 : Blo 354756 1018345 := bstep (se 2 (by rfl) ⟨381879, by rfl⟩ : syracuseStep 1018345 = 763759) B763759
theorem B4098575 : Blo 354756 4098575 := bstep (se 1 (by rfl) ⟨3073931, by rfl⟩ : syracuseStep 4098575 = 6147863) B6147863
theorem B2558945 : Blo 354756 2558945 := bstep (se 2 (by rfl) ⟨959604, by rfl⟩ : syracuseStep 2558945 = 1919209) B1919209
theorem B2296943 : Blo 354756 2296943 := bstep (se 1 (by rfl) ⟨1722707, by rfl⟩ : syracuseStep 2296943 = 3445415) B3445415
theorem B1085929 : Blo 354756 1085929 := bstep (se 2 (by rfl) ⟨407223, by rfl⟩ : syracuseStep 1085929 = 814447) B814447
theorem B1807433 : Blo 354756 1807433 := bstep (se 2 (by rfl) ⟨677787, by rfl⟩ : syracuseStep 1807433 = 1355575) B1355575
theorem B2036987 : Blo 354756 2036987 := bstep (se 1 (by rfl) ⟨1527740, by rfl⟩ : syracuseStep 2036987 = 3055481) B3055481
theorem B399919 : Blo 354756 399919 := bstep (se 1 (by rfl) ⟨299939, by rfl⟩ : syracuseStep 399919 = 599879) B599879
theorem B400063 : Blo 354756 400063 := bstep (se 1 (by rfl) ⟨300047, by rfl⟩ : syracuseStep 400063 = 600095) B600095
theorem B400495 : Blo 354756 400495 := bstep (se 1 (by rfl) ⟨300371, by rfl⟩ : syracuseStep 400495 = 600743) B600743
theorem B4070735 : Blo 354756 4070735 := bstep (se 1 (by rfl) ⟨3053051, by rfl⟩ : syracuseStep 4070735 = 6106103) B6106103
theorem B1351019 : Blo 354756 1351019 := bstep (se 1 (by rfl) ⟨1013264, by rfl⟩ : syracuseStep 1351019 = 2026529) B2026529
theorem B532151 : Blo 354756 532151 := bstep (se 1 (by rfl) ⟨399113, by rfl⟩ : syracuseStep 532151 = 798227) B798227
theorem B3678311 : Blo 354756 3678311 := bstep (se 1 (by rfl) ⟨2758733, by rfl⟩ : syracuseStep 3678311 = 5517467) B5517467
theorem B532607 : Blo 354756 532607 := bstep (se 1 (by rfl) ⟨399455, by rfl⟩ : syracuseStep 532607 = 798911) B798911
theorem B532763 : Blo 354756 532763 := bstep (se 1 (by rfl) ⟨399572, by rfl⟩ : syracuseStep 532763 = 799145) B799145
theorem B1352159 : Blo 354756 1352159 := bstep (se 1 (by rfl) ⟨1014119, by rfl⟩ : syracuseStep 1352159 = 2028239) B2028239
theorem B3908287 : Blo 354756 3908287 := bstep (se 1 (by rfl) ⟨2931215, by rfl⟩ : syracuseStep 3908287 = 5862431) B5862431
theorem B533369 : Blo 354756 533369 := bstep (se 2 (by rfl) ⟨200013, by rfl⟩ : syracuseStep 533369 = 400027) B400027
theorem B1025131 : Blo 354756 1025131 := bstep (se 1 (by rfl) ⟨768848, by rfl⟩ : syracuseStep 1025131 = 1537697) B1537697
theorem B533615 : Blo 354756 533615 := bstep (se 1 (by rfl) ⟨400211, by rfl⟩ : syracuseStep 533615 = 800423) B800423
theorem B599231 : Blo 354756 599231 := bstep (se 1 (by rfl) ⟨449423, by rfl⟩ : syracuseStep 599231 = 898847) B898847
theorem B533759 : Blo 354756 533759 := bstep (se 1 (by rfl) ⟨400319, by rfl⟩ : syracuseStep 533759 = 800639) B800639
theorem B2893607 : Blo 354756 2893607 := bstep (se 1 (by rfl) ⟨2170205, by rfl⟩ : syracuseStep 2893607 = 4340411) B4340411
theorem B1353631 : Blo 354756 1353631 := bstep (se 1 (by rfl) ⟨1015223, by rfl⟩ : syracuseStep 1353631 = 2030447) B2030447
theorem B600527 : Blo 354756 600527 := bstep (se 1 (by rfl) ⟨450395, by rfl⟩ : syracuseStep 600527 = 900791) B900791
theorem B8006215 : Blo 354756 8006215 := bstep (se 1 (by rfl) ⟨6004661, by rfl⟩ : syracuseStep 8006215 = 12009323) B12009323
theorem B535199 : Blo 354756 535199 := bstep (se 1 (by rfl) ⟨401399, by rfl⟩ : syracuseStep 535199 = 802799) B802799
theorem B601087 : Blo 354756 601087 := bstep (se 1 (by rfl) ⟨450815, by rfl⟩ : syracuseStep 601087 = 901631) B901631
theorem B3190279 : Blo 354756 3190279 := bstep (se 1 (by rfl) ⟨2392709, by rfl⟩ : syracuseStep 3190279 = 4785419) B4785419
theorem B26455747 : Blo 354756 26455747 := bstep (se 1 (by rfl) ⟨19841810, by rfl⟩ : syracuseStep 26455747 = 39683621) B39683621
theorem B602167 : Blo 354756 602167 := bstep (se 1 (by rfl) ⟨451625, by rfl⟩ : syracuseStep 602167 = 903251) B903251
theorem B798875 : Blo 354756 798875 := bstep (se 1 (by rfl) ⟨599156, by rfl⟩ : syracuseStep 798875 = 1198313) B1198313
theorem B4043033 : Blo 354756 4043033 := bstep (se 2 (by rfl) ⟨1516137, by rfl⟩ : syracuseStep 4043033 = 3032275) B3032275
theorem B799199 : Blo 354756 799199 := bstep (se 1 (by rfl) ⟨599399, by rfl⟩ : syracuseStep 799199 = 1198799) B1198799
theorem B537215 : Blo 354756 537215 := bstep (se 1 (by rfl) ⟨402911, by rfl⟩ : syracuseStep 537215 = 805823) B805823
theorem B799559 : Blo 354756 799559 := bstep (se 1 (by rfl) ⟨599669, by rfl⟩ : syracuseStep 799559 = 1199339) B1199339
theorem B898411 : Blo 354756 898411 := bstep (se 1 (by rfl) ⟨673808, by rfl⟩ : syracuseStep 898411 = 1347617) B1347617
theorem B603625 : Blo 354756 603625 := bstep (se 2 (by rfl) ⟨226359, by rfl⟩ : syracuseStep 603625 = 452719) B452719
theorem B800297 : Blo 354756 800297 := bstep (se 2 (by rfl) ⟨300111, by rfl⟩ : syracuseStep 800297 = 600223) B600223
theorem B39172247 : Blo 354756 39172247 := bstep (se 1 (by rfl) ⟨29379185, by rfl⟩ : syracuseStep 39172247 = 58758371) B58758371
theorem B604415 : Blo 354756 604415 := bstep (se 1 (by rfl) ⟨453311, by rfl⟩ : syracuseStep 604415 = 906623) B906623
theorem B899849 : Blo 354756 899849 := bstep (se 2 (by rfl) ⟨337443, by rfl⟩ : syracuseStep 899849 = 674887) B674887
theorem B41827195 : Blo 354756 41827195 := bstep (se 1 (by rfl) ⟨31370396, by rfl⟩ : syracuseStep 41827195 = 62740793) B62740793
theorem B1359463 : Blo 354756 1359463 := bstep (se 1 (by rfl) ⟨1019597, by rfl⟩ : syracuseStep 1359463 = 2039195) B2039195
theorem B2277335 : Blo 354756 2277335 := bstep (se 1 (by rfl) ⟨1708001, by rfl⟩ : syracuseStep 2277335 = 3416003) B3416003
theorem B1360223 : Blo 354756 1360223 := bstep (se 1 (by rfl) ⟨1020167, by rfl⟩ : syracuseStep 1360223 = 2040335) B2040335
theorem B902137 : Blo 354756 902137 := bstep (se 2 (by rfl) ⟨338301, by rfl⟩ : syracuseStep 902137 = 676603) B676603
theorem B2442575 : Blo 354756 2442575 := bstep (se 1 (by rfl) ⟨1831931, by rfl⟩ : syracuseStep 2442575 = 3663863) B3663863
theorem B607771 : Blo 354756 607771 := bstep (se 1 (by rfl) ⟨455828, by rfl⟩ : syracuseStep 607771 = 911657) B911657
theorem B1525979 : Blo 354756 1525979 := bstep (se 1 (by rfl) ⟨1144484, by rfl⟩ : syracuseStep 1525979 = 2288969) B2288969
theorem B1198745 : Blo 354756 1198745 := bstep (se 2 (by rfl) ⟨449529, by rfl⟩ : syracuseStep 1198745 = 899059) B899059
theorem B1199015 : Blo 354756 1199015 := bstep (se 1 (by rfl) ⟨899261, by rfl⟩ : syracuseStep 1199015 = 1798523) B1798523
theorem B904223 : Blo 354756 904223 := bstep (se 1 (by rfl) ⟨678167, by rfl⟩ : syracuseStep 904223 = 1356335) B1356335
theorem B1821959 : Blo 354756 1821959 := bstep (se 1 (by rfl) ⟨1366469, by rfl⟩ : syracuseStep 1821959 = 2732939) B2732939
theorem B806471 : Blo 354756 806471 := bstep (se 1 (by rfl) ⟨604853, by rfl⟩ : syracuseStep 806471 = 1209707) B1209707
theorem B904871 : Blo 354756 904871 := bstep (se 1 (by rfl) ⟨678653, by rfl⟩ : syracuseStep 904871 = 1357307) B1357307
theorem B1232623 : Blo 354756 1232623 := bstep (se 1 (by rfl) ⟨924467, by rfl⟩ : syracuseStep 1232623 = 1848935) B1848935
theorem B1200311 : Blo 354756 1200311 := bstep (se 1 (by rfl) ⟨900233, by rfl⟩ : syracuseStep 1200311 = 1800467) B1800467
theorem B643385 : Blo 354756 643385 := bstep (se 2 (by rfl) ⟨241269, by rfl⟩ : syracuseStep 643385 = 482539) B482539
theorem B545435 : Blo 354756 545435 := bstep (se 1 (by rfl) ⟨409076, by rfl⟩ : syracuseStep 545435 = 818153) B818153
theorem B1200797 : Blo 354756 1200797 := bstep (se 3 (by rfl) ⟨225149, by rfl⟩ : syracuseStep 1200797 = 450299) B450299
theorem B10245001 : Blo 354756 10245001 := bstep (se 2 (by rfl) ⟨3841875, by rfl⟩ : syracuseStep 10245001 = 7683751) B7683751
theorem B1201337 : Blo 354756 1201337 := bstep (se 2 (by rfl) ⟨450501, by rfl⟩ : syracuseStep 1201337 = 901003) B901003
theorem B1201823 : Blo 354756 1201823 := bstep (se 1 (by rfl) ⟨901367, by rfl⟩ : syracuseStep 1201823 = 1802735) B1802735
theorem B579611 : Blo 354756 579611 := bstep (se 1 (by rfl) ⟨434708, by rfl⟩ : syracuseStep 579611 = 869417) B869417
theorem B19421471 : Blo 354756 19421471 := bstep (se 1 (by rfl) ⟨14566103, by rfl⟩ : syracuseStep 19421471 = 29132207) B29132207
theorem B1202687 : Blo 354756 1202687 := bstep (se 1 (by rfl) ⟨902015, by rfl⟩ : syracuseStep 1202687 = 1804031) B1804031
theorem B1203713 : Blo 354756 1203713 := bstep (se 2 (by rfl) ⟨451392, by rfl⟩ : syracuseStep 1203713 = 902785) B902785
theorem B1105435 : Blo 354756 1105435 := bstep (se 1 (by rfl) ⟨829076, by rfl⟩ : syracuseStep 1105435 = 1658153) B1658153
theorem B4054697 : Blo 354756 4054697 := bstep (se 2 (by rfl) ⟨1520511, by rfl⟩ : syracuseStep 4054697 = 3041023) B3041023
theorem B1204523 : Blo 354756 1204523 := bstep (se 1 (by rfl) ⟨903392, by rfl⟩ : syracuseStep 1204523 = 1806785) B1806785
theorem B2744819 : Blo 354756 2744819 := bstep (se 1 (by rfl) ⟨2058614, by rfl⟩ : syracuseStep 2744819 = 4117229) B4117229
theorem B2286407 : Blo 354756 2286407 := bstep (se 1 (by rfl) ⟨1714805, by rfl⟩ : syracuseStep 2286407 = 3429611) B3429611
theorem B1205063 : Blo 354756 1205063 := bstep (se 1 (by rfl) ⟨903797, by rfl⟩ : syracuseStep 1205063 = 1807595) B1807595
theorem B1205279 : Blo 354756 1205279 := bstep (se 1 (by rfl) ⟨903959, by rfl⟩ : syracuseStep 1205279 = 1807919) B1807919
theorem B1796093 : Blo 354756 1796093 := bstep (se 3 (by rfl) ⟨336767, by rfl⟩ : syracuseStep 1796093 = 673535) B673535
theorem B1010657 : Blo 354756 1010657 := bstep (se 2 (by rfl) ⟨378996, by rfl⟩ : syracuseStep 1010657 = 757993) B757993
theorem B355567 : Blo 354756 355567 := bstep (se 1 (by rfl) ⟨266675, by rfl⟩ : syracuseStep 355567 = 533351) B533351
theorem B4877927 : Blo 354756 4877927 := bstep (se 1 (by rfl) ⟨3658445, by rfl⟩ : syracuseStep 4877927 = 7316891) B7316891
theorem B1011305 : Blo 354756 1011305 := bstep (se 2 (by rfl) ⟨379239, by rfl⟩ : syracuseStep 1011305 = 758479) B758479
theorem B356071 : Blo 354756 356071 := bstep (se 1 (by rfl) ⟨267053, by rfl⟩ : syracuseStep 356071 = 534107) B534107
theorem B1142525 : Blo 354756 1142525 := bstep (se 3 (by rfl) ⟨214223, by rfl⟩ : syracuseStep 1142525 = 428447) B428447
theorem B356519 : Blo 354756 356519 := bstep (se 1 (by rfl) ⟨267389, by rfl⟩ : syracuseStep 356519 = 534779) B534779
theorem B356543 : Blo 354756 356543 := bstep (se 1 (by rfl) ⟨267407, by rfl⟩ : syracuseStep 356543 = 534815) B534815
theorem B357535 : Blo 354756 357535 := bstep (se 1 (by rfl) ⟨268151, by rfl⟩ : syracuseStep 357535 = 536303) B536303
theorem B357839 : Blo 354756 357839 := bstep (se 1 (by rfl) ⟨268379, by rfl⟩ : syracuseStep 357839 = 536759) B536759
theorem B358311 : Blo 354756 358311 := bstep (se 1 (by rfl) ⟨268733, by rfl⟩ : syracuseStep 358311 = 537467) B537467
theorem B1210301 : Blo 354756 1210301 := bstep (se 3 (by rfl) ⟨226931, by rfl⟩ : syracuseStep 1210301 = 453863) B453863
theorem B817951 : Blo 354756 817951 := bstep (se 1 (by rfl) ⟨613463, by rfl⟩ : syracuseStep 817951 = 1226927) B1226927
theorem B2718683 : Blo 354756 2718683 := bstep (se 1 (by rfl) ⟨2039012, by rfl⟩ : syracuseStep 2718683 = 4078025) B4078025
theorem B1015679 : Blo 354756 1015679 := bstep (se 1 (by rfl) ⟨761759, by rfl⟩ : syracuseStep 1015679 = 1523519) B1523519
theorem B5211049 : Blo 354756 5211049 := bstep (se 2 (by rfl) ⟨1954143, by rfl⟩ : syracuseStep 5211049 = 3908287) B3908287
theorem B1705963 : Blo 354756 1705963 := bstep (se 1 (by rfl) ⟨1279472, by rfl⟩ : syracuseStep 1705963 = 2558945) B2558945
theorem B1214639 : Blo 354756 1214639 := bstep (se 1 (by rfl) ⟨910979, by rfl⟩ : syracuseStep 1214639 = 1821959) B1821959
theorem B1804841 : Blo 354756 1804841 := bstep (se 2 (by rfl) ⟨676815, by rfl⟩ : syracuseStep 1804841 = 1353631) B1353631
theorem B428923 : Blo 354756 428923 := bstep (se 1 (by rfl) ⟨321692, by rfl⟩ : syracuseStep 428923 = 643385) B643385
theorem B363623 : Blo 354756 363623 := bstep (se 1 (by rfl) ⟨272717, by rfl⟩ : syracuseStep 363623 = 545435) B545435
theorem B1643497 : Blo 354756 1643497 := bstep (se 2 (by rfl) ⟨616311, by rfl⟩ : syracuseStep 1643497 = 1232623) B1232623
theorem B4069277 : Blo 354756 4069277 := bstep (se 3 (by rfl) ⟨762989, by rfl⟩ : syracuseStep 4069277 = 1525979) B1525979
theorem B399487 : Blo 354756 399487 := bstep (se 1 (by rfl) ⟨299615, by rfl⟩ : syracuseStep 399487 = 599231) B599231
theorem B400351 : Blo 354756 400351 := bstep (se 1 (by rfl) ⟨300263, by rfl⟩ : syracuseStep 400351 = 600527) B600527
theorem B3251951 : Blo 354756 3251951 := bstep (se 1 (by rfl) ⟨2438963, by rfl⟩ : syracuseStep 3251951 = 4877927) B4877927
theorem B532583 : Blo 354756 532583 := bstep (se 1 (by rfl) ⟨399437, by rfl⟩ : syracuseStep 532583 = 798875) B798875
theorem B2695355 : Blo 354756 2695355 := bstep (se 1 (by rfl) ⟨2021516, by rfl⟩ : syracuseStep 2695355 = 4043033) B4043033
theorem B532799 : Blo 354756 532799 := bstep (se 1 (by rfl) ⟨399599, by rfl⟩ : syracuseStep 532799 = 799199) B799199
theorem B533039 : Blo 354756 533039 := bstep (se 1 (by rfl) ⟨399779, by rfl⟩ : syracuseStep 533039 = 799559) B799559
theorem B533225 : Blo 354756 533225 := bstep (se 2 (by rfl) ⟨199959, by rfl⟩ : syracuseStep 533225 = 399919) B399919
theorem B533417 : Blo 354756 533417 := bstep (se 2 (by rfl) ⟨200031, by rfl⟩ : syracuseStep 533417 = 400063) B400063
theorem B533531 : Blo 354756 533531 := bstep (se 1 (by rfl) ⟨400148, by rfl⟩ : syracuseStep 533531 = 800297) B800297
theorem B1090601 : Blo 354756 1090601 := bstep (se 2 (by rfl) ⟨408975, by rfl⟩ : syracuseStep 1090601 = 817951) B817951
theorem B533993 : Blo 354756 533993 := bstep (se 2 (by rfl) ⟨200247, by rfl⟩ : syracuseStep 533993 = 400495) B400495
theorem B402943 : Blo 354756 402943 := bstep (se 1 (by rfl) ⟨302207, by rfl⟩ : syracuseStep 402943 = 604415) B604415
theorem B2696813 : Blo 354756 2696813 := bstep (se 3 (by rfl) ⟨505652, by rfl⟩ : syracuseStep 2696813 = 1011305) B1011305
theorem B599899 : Blo 354756 599899 := bstep (se 1 (by rfl) ⟨449924, by rfl⟩ : syracuseStep 599899 = 899849) B899849
theorem B1812455 : Blo 354756 1812455 := bstep (se 1 (by rfl) ⟨1359341, by rfl⟩ : syracuseStep 1812455 = 2718683) B2718683
theorem B1812617 : Blo 354756 1812617 := bstep (se 2 (by rfl) ⟨679731, by rfl⟩ : syracuseStep 1812617 = 1359463) B1359463
theorem B1518223 : Blo 354756 1518223 := bstep (se 1 (by rfl) ⟨1138667, by rfl⟩ : syracuseStep 1518223 = 2277335) B2277335
theorem B1552343 : Blo 354756 1552343 := bstep (se 1 (by rfl) ⟨1164257, by rfl⟩ : syracuseStep 1552343 = 2328515) B2328515
theorem B1355849 : Blo 354756 1355849 := bstep (se 2 (by rfl) ⟨508443, by rfl⟩ : syracuseStep 1355849 = 1016887) B1016887
theorem B2732383 : Blo 354756 2732383 := bstep (se 1 (by rfl) ⟨2049287, by rfl⟩ : syracuseStep 2732383 = 4098575) B4098575
theorem B799163 : Blo 354756 799163 := bstep (se 1 (by rfl) ⟨599372, by rfl⟩ : syracuseStep 799163 = 1198745) B1198745
theorem B799343 : Blo 354756 799343 := bstep (se 1 (by rfl) ⟨599507, by rfl⟩ : syracuseStep 799343 = 1199015) B1199015
theorem B602815 : Blo 354756 602815 := bstep (se 1 (by rfl) ⟨452111, by rfl⟩ : syracuseStep 602815 = 904223) B904223
theorem B537647 : Blo 354756 537647 := bstep (se 1 (by rfl) ⟨403235, by rfl⟩ : syracuseStep 537647 = 806471) B806471
theorem B603247 : Blo 354756 603247 := bstep (se 1 (by rfl) ⟨452435, by rfl⟩ : syracuseStep 603247 = 904871) B904871
theorem B800207 : Blo 354756 800207 := bstep (se 1 (by rfl) ⟨600155, by rfl⟩ : syracuseStep 800207 = 1200311) B1200311
theorem B800531 : Blo 354756 800531 := bstep (se 1 (by rfl) ⟨600398, by rfl⟩ : syracuseStep 800531 = 1200797) B1200797
theorem B1357793 : Blo 354756 1357793 := bstep (se 2 (by rfl) ⟨509172, by rfl⟩ : syracuseStep 1357793 = 1018345) B1018345
theorem B800891 : Blo 354756 800891 := bstep (se 1 (by rfl) ⟨600668, by rfl⟩ : syracuseStep 800891 = 1201337) B1201337
theorem B1357991 : Blo 354756 1357991 := bstep (se 1 (by rfl) ⟨1018493, by rfl⟩ : syracuseStep 1357991 = 2036987) B2036987
theorem B801215 : Blo 354756 801215 := bstep (se 1 (by rfl) ⟨600911, by rfl⟩ : syracuseStep 801215 = 1201823) B1201823
theorem B801449 : Blo 354756 801449 := bstep (se 2 (by rfl) ⟨300543, by rfl⟩ : syracuseStep 801449 = 601087) B601087
theorem B801791 : Blo 354756 801791 := bstep (se 1 (by rfl) ⟨601343, by rfl⟩ : syracuseStep 801791 = 1202687) B1202687
theorem B900679 : Blo 354756 900679 := bstep (se 1 (by rfl) ⟨675509, by rfl⟩ : syracuseStep 900679 = 1351019) B1351019
theorem B35274329 : Blo 354756 35274329 := bstep (se 2 (by rfl) ⟨13227873, by rfl⟩ : syracuseStep 35274329 = 26455747) B26455747
theorem B802475 : Blo 354756 802475 := bstep (se 1 (by rfl) ⟨601856, by rfl⟩ : syracuseStep 802475 = 1203713) B1203713
theorem B2703131 : Blo 354756 2703131 := bstep (se 1 (by rfl) ⟨2027348, by rfl⟩ : syracuseStep 2703131 = 4054697) B4054697
theorem B802889 : Blo 354756 802889 := bstep (se 2 (by rfl) ⟨301083, by rfl⟩ : syracuseStep 802889 = 602167) B602167
theorem B803015 : Blo 354756 803015 := bstep (se 1 (by rfl) ⟨602261, by rfl⟩ : syracuseStep 803015 = 1204523) B1204523
theorem B901439 : Blo 354756 901439 := bstep (se 1 (by rfl) ⟨676079, by rfl⟩ : syracuseStep 901439 = 1352159) B1352159
theorem B1524271 : Blo 354756 1524271 := bstep (se 1 (by rfl) ⟨1143203, by rfl⟩ : syracuseStep 1524271 = 2286407) B2286407
theorem B803375 : Blo 354756 803375 := bstep (se 1 (by rfl) ⟨602531, by rfl⟩ : syracuseStep 803375 = 1205063) B1205063
theorem B803519 : Blo 354756 803519 := bstep (se 1 (by rfl) ⟨602639, by rfl⟩ : syracuseStep 803519 = 1205279) B1205279
theorem B51790589 : Blo 354756 51790589 := bstep (se 3 (by rfl) ⟨9710735, by rfl⟩ : syracuseStep 51790589 = 19421471) B19421471
theorem B1197395 : Blo 354756 1197395 := bstep (se 1 (by rfl) ⟨898046, by rfl⟩ : syracuseStep 1197395 = 1796093) B1796093
theorem B1197881 : Blo 354756 1197881 := bstep (se 2 (by rfl) ⟨449205, by rfl⟩ : syracuseStep 1197881 = 898411) B898411
theorem B804833 : Blo 354756 804833 := bstep (se 2 (by rfl) ⟨301812, by rfl⟩ : syracuseStep 804833 = 603625) B603625
theorem B673771 : Blo 354756 673771 := bstep (se 1 (by rfl) ⟨505328, by rfl⟩ : syracuseStep 673771 = 1010657) B1010657
theorem B806867 : Blo 354756 806867 := bstep (se 1 (by rfl) ⟨605150, by rfl⟩ : syracuseStep 806867 = 1210301) B1210301
theorem B2708477 : Blo 354756 2708477 := bstep (se 3 (by rfl) ⟨507839, by rfl⟩ : syracuseStep 2708477 = 1015679) B1015679
theorem B5789231 : Blo 354756 5789231 := bstep (se 1 (by rfl) ⟨4341923, by rfl⟩ : syracuseStep 5789231 = 8683847) B8683847
theorem B906815 : Blo 354756 906815 := bstep (se 1 (by rfl) ⟨680111, by rfl⟩ : syracuseStep 906815 = 1360223) B1360223
theorem B3758089 : Blo 354756 3758089 := bstep (se 2 (by rfl) ⟨1409283, by rfl⟩ : syracuseStep 3758089 = 2818567) B2818567
theorem B1628383 : Blo 354756 1628383 := bstep (se 1 (by rfl) ⟨1221287, by rfl⟩ : syracuseStep 1628383 = 2442575) B2442575
theorem B4348151 : Blo 354756 4348151 := bstep (se 1 (by rfl) ⟨3261113, by rfl⟩ : syracuseStep 4348151 = 6522227) B6522227
theorem B1202471 : Blo 354756 1202471 := bstep (se 1 (by rfl) ⟨901853, by rfl⟩ : syracuseStep 1202471 = 1803707) B1803707
theorem B1202849 : Blo 354756 1202849 := bstep (se 2 (by rfl) ⟨451068, by rfl⟩ : syracuseStep 1202849 = 902137) B902137
theorem B1366841 : Blo 354756 1366841 := bstep (se 2 (by rfl) ⟨512565, by rfl⟩ : syracuseStep 1366841 = 1025131) B1025131
theorem B810361 : Blo 354756 810361 := bstep (se 2 (by rfl) ⟨303885, by rfl⟩ : syracuseStep 810361 = 607771) B607771
theorem B1531295 : Blo 354756 1531295 := bstep (se 1 (by rfl) ⟨1148471, by rfl⟩ : syracuseStep 1531295 = 2296943) B2296943
theorem B5791621 : Blo 354756 5791621 := bstep (se 4 (by rfl) ⟨542964, by rfl⟩ : syracuseStep 5791621 = 1085929) B1085929
theorem B1204955 : Blo 354756 1204955 := bstep (se 1 (by rfl) ⟨903716, by rfl⟩ : syracuseStep 1204955 = 1807433) B1807433
theorem B10674953 : Blo 354756 10674953 := bstep (se 2 (by rfl) ⟨4003107, by rfl⟩ : syracuseStep 10674953 = 8006215) B8006215
theorem B386407 : Blo 354756 386407 := bstep (se 1 (by rfl) ⟨289805, by rfl⟩ : syracuseStep 386407 = 579611) B579611
theorem B4253705 : Blo 354756 4253705 := bstep (se 2 (by rfl) ⟨1595139, by rfl⟩ : syracuseStep 4253705 = 3190279) B3190279
theorem B2713823 : Blo 354756 2713823 := bstep (se 1 (by rfl) ⟨2035367, by rfl⟩ : syracuseStep 2713823 = 4070735) B4070735
theorem B354767 : Blo 354756 354767 := bstep (se 1 (by rfl) ⟨266075, by rfl⟩ : syracuseStep 354767 = 532151) B532151
theorem B2452207 : Blo 354756 2452207 := bstep (se 1 (by rfl) ⟨1839155, by rfl⟩ : syracuseStep 2452207 = 3678311) B3678311
theorem B355071 : Blo 354756 355071 := bstep (se 1 (by rfl) ⟨266303, by rfl⟩ : syracuseStep 355071 = 532607) B532607
theorem B355175 : Blo 354756 355175 := bstep (se 1 (by rfl) ⟨266381, by rfl⟩ : syracuseStep 355175 = 532763) B532763
theorem B1829879 : Blo 354756 1829879 := bstep (se 1 (by rfl) ⟨1372409, by rfl⟩ : syracuseStep 1829879 = 2744819) B2744819
theorem B355579 : Blo 354756 355579 := bstep (se 1 (by rfl) ⟨266684, by rfl⟩ : syracuseStep 355579 = 533369) B533369
theorem B355743 : Blo 354756 355743 := bstep (se 1 (by rfl) ⟨266807, by rfl⟩ : syracuseStep 355743 = 533615) B533615
theorem B355839 : Blo 354756 355839 := bstep (se 1 (by rfl) ⟨266879, by rfl⟩ : syracuseStep 355839 = 533759) B533759
theorem B13660001 : Blo 354756 13660001 := bstep (se 2 (by rfl) ⟨5122500, by rfl⟩ : syracuseStep 13660001 = 10245001) B10245001
theorem B1929071 : Blo 354756 1929071 := bstep (se 1 (by rfl) ⟨1446803, by rfl⟩ : syracuseStep 1929071 = 2893607) B2893607
theorem B356799 : Blo 354756 356799 := bstep (se 1 (by rfl) ⟨267599, by rfl⟩ : syracuseStep 356799 = 535199) B535199
theorem B358143 : Blo 354756 358143 := bstep (se 1 (by rfl) ⟨268607, by rfl⟩ : syracuseStep 358143 = 537215) B537215
theorem B55769593 : Blo 354756 55769593 := bstep (se 2 (by rfl) ⟨20913597, by rfl⟩ : syracuseStep 55769593 = 41827195) B41827195
theorem B26114831 : Blo 354756 26114831 := bstep (se 1 (by rfl) ⟨19586123, by rfl⟩ : syracuseStep 26114831 = 39172247) B39172247
theorem B3046733 : Blo 354756 3046733 := bstep (se 3 (by rfl) ⟨571262, by rfl⟩ : syracuseStep 3046733 = 1142525) B1142525
theorem B1473913 : Blo 354756 1473913 := bstep (se 2 (by rfl) ⟨552717, by rfl⟩ : syracuseStep 1473913 = 1105435) B1105435
theorem B2032361 : Blo 354756 2032361 := bstep (se 2 (by rfl) ⟨762135, by rfl⟩ : syracuseStep 2032361 = 1524271) B1524271
theorem B6948065 : Blo 354756 6948065 := bstep (se 2 (by rfl) ⟨2605524, by rfl⟩ : syracuseStep 6948065 = 5211049) B5211049
theorem B1805651 : Blo 354756 1805651 := bstep (se 1 (by rfl) ⟨1354238, by rfl⟩ : syracuseStep 1805651 = 2708477) B2708477
theorem B1020863 : Blo 354756 1020863 := bstep (se 1 (by rfl) ⟨765647, by rfl⟩ : syracuseStep 1020863 = 1531295) B1531295
theorem B2167967 : Blo 354756 2167967 := bstep (se 1 (by rfl) ⟨1625975, by rfl⟩ : syracuseStep 2167967 = 3251951) B3251951
theorem B3643177 : Blo 354756 3643177 := bstep (se 2 (by rfl) ⟨1366191, by rfl⟩ : syracuseStep 3643177 = 2732383) B2732383
theorem B7116635 : Blo 354756 7116635 := bstep (se 1 (by rfl) ⟨5337476, by rfl⟩ : syracuseStep 7116635 = 10674953) B10674953
theorem B727067 : Blo 354756 727067 := bstep (se 1 (by rfl) ⟨545300, by rfl⟩ : syracuseStep 727067 = 1090601) B1090601
theorem B1809215 : Blo 354756 1809215 := bstep (se 1 (by rfl) ⟨1356911, by rfl⟩ : syracuseStep 1809215 = 2713823) B2713823
theorem B1219919 : Blo 354756 1219919 := bstep (se 1 (by rfl) ⟨914939, by rfl⟩ : syracuseStep 1219919 = 1829879) B1829879
theorem B3644909 : Blo 354756 3644909 := bstep (se 3 (by rfl) ⟨683420, by rfl⟩ : syracuseStep 3644909 = 1366841) B1366841
theorem B1286047 : Blo 354756 1286047 := bstep (se 1 (by rfl) ⟨964535, by rfl⟩ : syracuseStep 1286047 = 1929071) B1929071
theorem B532649 : Blo 354756 532649 := bstep (se 2 (by rfl) ⟨199743, by rfl⟩ : syracuseStep 532649 = 399487) B399487
theorem B532775 : Blo 354756 532775 := bstep (se 1 (by rfl) ⟨399581, by rfl⟩ : syracuseStep 532775 = 799163) B799163
theorem B2171177 : Blo 354756 2171177 := bstep (se 2 (by rfl) ⟨814191, by rfl⟩ : syracuseStep 2171177 = 1628383) B1628383
theorem B532895 : Blo 354756 532895 := bstep (se 1 (by rfl) ⟨399671, by rfl⟩ : syracuseStep 532895 = 799343) B799343
theorem B74359457 : Blo 354756 74359457 := bstep (se 2 (by rfl) ⟨27884796, by rfl⟩ : syracuseStep 74359457 = 55769593) B55769593
theorem B533471 : Blo 354756 533471 := bstep (se 1 (by rfl) ⟨400103, by rfl⟩ : syracuseStep 533471 = 800207) B800207
theorem B533687 : Blo 354756 533687 := bstep (se 1 (by rfl) ⟨400265, by rfl⟩ : syracuseStep 533687 = 800531) B800531
theorem B533801 : Blo 354756 533801 := bstep (se 2 (by rfl) ⟨200175, by rfl⟩ : syracuseStep 533801 = 400351) B400351
theorem B533927 : Blo 354756 533927 := bstep (se 1 (by rfl) ⟨400445, by rfl⟩ : syracuseStep 533927 = 800891) B800891
theorem B534143 : Blo 354756 534143 := bstep (se 1 (by rfl) ⟨400607, by rfl⟩ : syracuseStep 534143 = 801215) B801215
theorem B534299 : Blo 354756 534299 := bstep (se 1 (by rfl) ⟨400724, by rfl⟩ : syracuseStep 534299 = 801449) B801449
theorem B17409887 : Blo 354756 17409887 := bstep (se 1 (by rfl) ⟨13057415, by rfl⟩ : syracuseStep 17409887 = 26114831) B26114831
theorem B534527 : Blo 354756 534527 := bstep (se 1 (by rfl) ⟨400895, by rfl⟩ : syracuseStep 534527 = 801791) B801791
theorem B534983 : Blo 354756 534983 := bstep (se 1 (by rfl) ⟨401237, by rfl⟩ : syracuseStep 534983 = 802475) B802475
theorem B4139581 : Blo 354756 4139581 := bstep (se 3 (by rfl) ⟨776171, by rfl⟩ : syracuseStep 4139581 = 1552343) B1552343
theorem B535259 : Blo 354756 535259 := bstep (se 1 (by rfl) ⟨401444, by rfl⟩ : syracuseStep 535259 = 802889) B802889
theorem B535343 : Blo 354756 535343 := bstep (se 1 (by rfl) ⟨401507, by rfl⟩ : syracuseStep 535343 = 803015) B803015
theorem B600959 : Blo 354756 600959 := bstep (se 1 (by rfl) ⟨450719, by rfl⟩ : syracuseStep 600959 = 901439) B901439
theorem B535583 : Blo 354756 535583 := bstep (se 1 (by rfl) ⟨401687, by rfl⟩ : syracuseStep 535583 = 803375) B803375
theorem B535679 : Blo 354756 535679 := bstep (se 1 (by rfl) ⟨401759, by rfl⟩ : syracuseStep 535679 = 803519) B803519
theorem B798263 : Blo 354756 798263 := bstep (se 1 (by rfl) ⟨598697, by rfl⟩ : syracuseStep 798263 = 1197395) B1197395
theorem B798587 : Blo 354756 798587 := bstep (se 1 (by rfl) ⟨598940, by rfl⟩ : syracuseStep 798587 = 1197881) B1197881
theorem B536555 : Blo 354756 536555 := bstep (se 1 (by rfl) ⟨402416, by rfl⟩ : syracuseStep 536555 = 804833) B804833
theorem B537257 : Blo 354756 537257 := bstep (se 2 (by rfl) ⟨201471, by rfl⟩ : syracuseStep 537257 = 402943) B402943
theorem B799865 : Blo 354756 799865 := bstep (se 2 (by rfl) ⟨299949, by rfl⟩ : syracuseStep 799865 = 599899) B599899
theorem B537911 : Blo 354756 537911 := bstep (se 1 (by rfl) ⟨403433, by rfl⟩ : syracuseStep 537911 = 806867) B806867
theorem B898361 : Blo 354756 898361 := bstep (se 2 (by rfl) ⟨336885, by rfl⟩ : syracuseStep 898361 = 673771) B673771
theorem B2274617 : Blo 354756 2274617 := bstep (se 2 (by rfl) ⟨852981, by rfl⟩ : syracuseStep 2274617 = 1705963) B1705963
theorem B604543 : Blo 354756 604543 := bstep (se 1 (by rfl) ⟨453407, by rfl⟩ : syracuseStep 604543 = 906815) B906815
theorem B571897 : Blo 354756 571897 := bstep (se 2 (by rfl) ⟨214461, by rfl⟩ : syracuseStep 571897 = 428923) B428923
theorem B2898767 : Blo 354756 2898767 := bstep (se 1 (by rfl) ⟨2174075, by rfl⟩ : syracuseStep 2898767 = 4348151) B4348151
theorem B801647 : Blo 354756 801647 := bstep (se 1 (by rfl) ⟨601235, by rfl⟩ : syracuseStep 801647 = 1202471) B1202471
theorem B801899 : Blo 354756 801899 := bstep (se 1 (by rfl) ⟨601424, by rfl⟩ : syracuseStep 801899 = 1202849) B1202849
theorem B8765317 : Blo 354756 8765317 := bstep (se 4 (by rfl) ⟨821748, by rfl⟩ : syracuseStep 8765317 = 1643497) B1643497
theorem B803303 : Blo 354756 803303 := bstep (se 1 (by rfl) ⟨602477, by rfl⟩ : syracuseStep 803303 = 1204955) B1204955
theorem B803753 : Blo 354756 803753 := bstep (se 2 (by rfl) ⟨301407, by rfl⟩ : syracuseStep 803753 = 602815) B602815
theorem B2835803 : Blo 354756 2835803 := bstep (se 1 (by rfl) ⟨2126852, by rfl⟩ : syracuseStep 2835803 = 4253705) B4253705
theorem B804329 : Blo 354756 804329 := bstep (se 2 (by rfl) ⟨301623, by rfl⟩ : syracuseStep 804329 = 603247) B603247
theorem B903899 : Blo 354756 903899 := bstep (se 1 (by rfl) ⟨677924, by rfl⟩ : syracuseStep 903899 = 1355849) B1355849
theorem B969661 : Blo 354756 969661 := bstep (se 3 (by rfl) ⟨181811, by rfl⟩ : syracuseStep 969661 = 363623) B363623
theorem B905195 : Blo 354756 905195 := bstep (se 1 (by rfl) ⟨678896, by rfl⟩ : syracuseStep 905195 = 1357793) B1357793
theorem B905327 : Blo 354756 905327 := bstep (se 1 (by rfl) ⟨678995, by rfl⟩ : syracuseStep 905327 = 1357991) B1357991
theorem B1200905 : Blo 354756 1200905 := bstep (se 2 (by rfl) ⟨450339, by rfl⟩ : syracuseStep 1200905 = 900679) B900679
theorem B23516219 : Blo 354756 23516219 := bstep (se 1 (by rfl) ⟨17637164, by rfl⟩ : syracuseStep 23516219 = 35274329) B35274329
theorem B7722161 : Blo 354756 7722161 := bstep (se 2 (by rfl) ⟨2895810, by rfl⟩ : syracuseStep 7722161 = 5791621) B5791621
theorem B34527059 : Blo 354756 34527059 := bstep (se 1 (by rfl) ⟨25895294, by rfl⟩ : syracuseStep 34527059 = 51790589) B51790589
theorem B809759 : Blo 354756 809759 := bstep (se 1 (by rfl) ⟨607319, by rfl⟩ : syracuseStep 809759 = 1214639) B1214639
theorem B1203227 : Blo 354756 1203227 := bstep (se 1 (by rfl) ⟨902420, by rfl⟩ : syracuseStep 1203227 = 1804841) B1804841
theorem B515209 : Blo 354756 515209 := bstep (se 2 (by rfl) ⟨193203, by rfl⟩ : syracuseStep 515209 = 386407) B386407
theorem B2024297 : Blo 354756 2024297 := bstep (se 2 (by rfl) ⟨759111, by rfl⟩ : syracuseStep 2024297 = 1518223) B1518223
theorem B3269609 : Blo 354756 3269609 := bstep (se 2 (by rfl) ⟨1226103, by rfl⟩ : syracuseStep 3269609 = 2452207) B2452207
theorem B3859487 : Blo 354756 3859487 := bstep (se 1 (by rfl) ⟨2894615, by rfl⟩ : syracuseStep 3859487 = 5789231) B5789231
theorem B2712851 : Blo 354756 2712851 := bstep (se 1 (by rfl) ⟨2034638, by rfl⟩ : syracuseStep 2712851 = 4069277) B4069277
theorem B355055 : Blo 354756 355055 := bstep (se 1 (by rfl) ⟨266291, by rfl⟩ : syracuseStep 355055 = 532583) B532583
theorem B1796903 : Blo 354756 1796903 := bstep (se 1 (by rfl) ⟨1347677, by rfl⟩ : syracuseStep 1796903 = 2695355) B2695355
theorem B355199 : Blo 354756 355199 := bstep (se 1 (by rfl) ⟨266399, by rfl⟩ : syracuseStep 355199 = 532799) B532799
theorem B355359 : Blo 354756 355359 := bstep (se 1 (by rfl) ⟨266519, by rfl⟩ : syracuseStep 355359 = 533039) B533039
theorem B355483 : Blo 354756 355483 := bstep (se 1 (by rfl) ⟨266612, by rfl⟩ : syracuseStep 355483 = 533225) B533225
theorem B355611 : Blo 354756 355611 := bstep (se 1 (by rfl) ⟨266708, by rfl⟩ : syracuseStep 355611 = 533417) B533417
theorem B355687 : Blo 354756 355687 := bstep (se 1 (by rfl) ⟨266765, by rfl⟩ : syracuseStep 355687 = 533531) B533531
theorem B355995 : Blo 354756 355995 := bstep (se 1 (by rfl) ⟨266996, by rfl⟩ : syracuseStep 355995 = 533993) B533993
theorem B1797875 : Blo 354756 1797875 := bstep (se 1 (by rfl) ⟨1348406, by rfl⟩ : syracuseStep 1797875 = 2696813) B2696813
theorem B1208303 : Blo 354756 1208303 := bstep (se 1 (by rfl) ⟨906227, by rfl⟩ : syracuseStep 1208303 = 1812455) B1812455
theorem B1208411 : Blo 354756 1208411 := bstep (se 1 (by rfl) ⟨906308, by rfl⟩ : syracuseStep 1208411 = 1812617) B1812617
theorem B9106667 : Blo 354756 9106667 := bstep (se 1 (by rfl) ⟨6830000, by rfl⟩ : syracuseStep 9106667 = 13660001) B13660001
theorem B5010785 : Blo 354756 5010785 := bstep (se 2 (by rfl) ⟨1879044, by rfl⟩ : syracuseStep 5010785 = 3758089) B3758089
theorem B358431 : Blo 354756 358431 := bstep (se 1 (by rfl) ⟨268823, by rfl⟩ : syracuseStep 358431 = 537647) B537647
theorem B1080481 : Blo 354756 1080481 := bstep (se 2 (by rfl) ⟨405180, by rfl⟩ : syracuseStep 1080481 = 810361) B810361
theorem B1965217 : Blo 354756 1965217 := bstep (se 2 (by rfl) ⟨736956, by rfl⟩ : syracuseStep 1965217 = 1473913) B1473913
theorem B2031155 : Blo 354756 2031155 := bstep (se 1 (by rfl) ⟨1523366, by rfl⟩ : syracuseStep 2031155 = 3046733) B3046733
theorem B1802087 : Blo 354756 1802087 := bstep (se 1 (by rfl) ⟨1351565, by rfl⟩ : syracuseStep 1802087 = 2703131) B2703131
theorem B1445311 : Blo 354756 1445311 := bstep (se 1 (by rfl) ⟨1083983, by rfl⟩ : syracuseStep 1445311 = 2167967) B2167967
theorem B5148107 : Blo 354756 5148107 := bstep (se 1 (by rfl) ⟨3861080, by rfl⟩ : syracuseStep 5148107 = 7722161) B7722161
theorem B2429939 : Blo 354756 2429939 := bstep (se 1 (by rfl) ⟨1822454, by rfl⟩ : syracuseStep 2429939 = 3644909) B3644909
theorem B1447451 : Blo 354756 1447451 := bstep (se 1 (by rfl) ⟨1085588, by rfl⟩ : syracuseStep 1447451 = 2171177) B2171177
theorem B1349531 : Blo 354756 1349531 := bstep (se 1 (by rfl) ⟨1012148, by rfl⟩ : syracuseStep 1349531 = 2024297) B2024297
theorem B1808567 : Blo 354756 1808567 := bstep (se 1 (by rfl) ⟨1356425, by rfl⟩ : syracuseStep 1808567 = 2712851) B2712851
theorem B11606591 : Blo 354756 11606591 := bstep (se 1 (by rfl) ⟨8704943, by rfl⟩ : syracuseStep 11606591 = 17409887) B17409887
theorem B400639 : Blo 354756 400639 := bstep (se 1 (by rfl) ⟨300479, by rfl⟩ : syracuseStep 400639 = 600959) B600959
theorem B532175 : Blo 354756 532175 := bstep (se 1 (by rfl) ⟨399131, by rfl⟩ : syracuseStep 532175 = 798263) B798263
theorem B4857569 : Blo 354756 4857569 := bstep (se 2 (by rfl) ⟨1821588, by rfl⟩ : syracuseStep 4857569 = 3643177) B3643177
theorem B532391 : Blo 354756 532391 := bstep (se 1 (by rfl) ⟨399293, by rfl⟩ : syracuseStep 532391 = 798587) B798587
theorem B762529 : Blo 354756 762529 := bstep (se 2 (by rfl) ⟨285948, by rfl⟩ : syracuseStep 762529 = 571897) B571897
theorem B533243 : Blo 354756 533243 := bstep (se 1 (by rfl) ⟨399932, by rfl⟩ : syracuseStep 533243 = 799865) B799865
theorem B6071111 : Blo 354756 6071111 := bstep (se 1 (by rfl) ⟨4553333, by rfl⟩ : syracuseStep 6071111 = 9106667) B9106667
theorem B598907 : Blo 354756 598907 := bstep (se 1 (by rfl) ⟨449180, by rfl⟩ : syracuseStep 598907 = 898361) B898361
theorem B1516411 : Blo 354756 1516411 := bstep (se 1 (by rfl) ⟨1137308, by rfl⟩ : syracuseStep 1516411 = 2274617) B2274617
theorem B3253117 : Blo 354756 3253117 := bstep (se 3 (by rfl) ⟨609959, by rfl⟩ : syracuseStep 3253117 = 1219919) B1219919
theorem B534431 : Blo 354756 534431 := bstep (se 1 (by rfl) ⟨400823, by rfl⟩ : syracuseStep 534431 = 801647) B801647
theorem B534599 : Blo 354756 534599 := bstep (se 1 (by rfl) ⟨400949, by rfl⟩ : syracuseStep 534599 = 801899) B801899
theorem B1354103 : Blo 354756 1354103 := bstep (se 1 (by rfl) ⟨1015577, by rfl⟩ : syracuseStep 1354103 = 2031155) B2031155
theorem B1714729 : Blo 354756 1714729 := bstep (se 2 (by rfl) ⟨643023, by rfl⟩ : syracuseStep 1714729 = 1286047) B1286047
theorem B535535 : Blo 354756 535535 := bstep (se 1 (by rfl) ⟨401651, by rfl⟩ : syracuseStep 535535 = 803303) B803303
theorem B1354907 : Blo 354756 1354907 := bstep (se 1 (by rfl) ⟨1016180, by rfl⟩ : syracuseStep 1354907 = 2032361) B2032361
theorem B535835 : Blo 354756 535835 := bstep (se 1 (by rfl) ⟨401876, by rfl⟩ : syracuseStep 535835 = 803753) B803753
theorem B536219 : Blo 354756 536219 := bstep (se 1 (by rfl) ⟨402164, by rfl⟩ : syracuseStep 536219 = 804329) B804329
theorem B602599 : Blo 354756 602599 := bstep (se 1 (by rfl) ⟨451949, by rfl⟩ : syracuseStep 602599 = 903899) B903899
theorem B603463 : Blo 354756 603463 := bstep (se 1 (by rfl) ⟨452597, by rfl⟩ : syracuseStep 603463 = 905195) B905195
theorem B603551 : Blo 354756 603551 := bstep (se 1 (by rfl) ⟨452663, by rfl⟩ : syracuseStep 603551 = 905327) B905327
theorem B800603 : Blo 354756 800603 := bstep (se 1 (by rfl) ⟨600452, by rfl⟩ : syracuseStep 800603 = 1200905) B1200905
theorem B18528173 : Blo 354756 18528173 := bstep (se 3 (by rfl) ⟨3474032, by rfl⟩ : syracuseStep 18528173 = 6948065) B6948065
theorem B15677479 : Blo 354756 15677479 := bstep (se 1 (by rfl) ⟨11758109, by rfl⟩ : syracuseStep 15677479 = 23516219) B23516219
theorem B5519441 : Blo 354756 5519441 := bstep (se 2 (by rfl) ⟨2069790, by rfl⟩ : syracuseStep 5519441 = 4139581) B4139581
theorem B23018039 : Blo 354756 23018039 := bstep (se 1 (by rfl) ⟨17263529, by rfl⟩ : syracuseStep 23018039 = 34527059) B34527059
theorem B539839 : Blo 354756 539839 := bstep (se 1 (by rfl) ⟨404879, by rfl⟩ : syracuseStep 539839 = 809759) B809759
theorem B802151 : Blo 354756 802151 := bstep (se 1 (by rfl) ⟨601613, by rfl⟩ : syracuseStep 802151 = 1203227) B1203227
theorem B2179739 : Blo 354756 2179739 := bstep (se 1 (by rfl) ⟨1634804, by rfl⟩ : syracuseStep 2179739 = 3269609) B3269609
theorem B2572991 : Blo 354756 2572991 := bstep (se 1 (by rfl) ⟨1929743, by rfl⟩ : syracuseStep 2572991 = 3859487) B3859487
theorem B1197935 : Blo 354756 1197935 := bstep (se 1 (by rfl) ⟨898451, by rfl⟩ : syracuseStep 1197935 = 1796903) B1796903
theorem B1198583 : Blo 354756 1198583 := bstep (se 1 (by rfl) ⟨898937, by rfl⟩ : syracuseStep 1198583 = 1797875) B1797875
theorem B805535 : Blo 354756 805535 := bstep (se 1 (by rfl) ⟨604151, by rfl⟩ : syracuseStep 805535 = 1208303) B1208303
theorem B805607 : Blo 354756 805607 := bstep (se 1 (by rfl) ⟨604205, by rfl⟩ : syracuseStep 805607 = 1208411) B1208411
theorem B806057 : Blo 354756 806057 := bstep (se 2 (by rfl) ⟨302271, by rfl⟩ : syracuseStep 806057 = 604543) B604543
theorem B11687089 : Blo 354756 11687089 := bstep (se 2 (by rfl) ⟨4382658, by rfl⟩ : syracuseStep 11687089 = 8765317) B8765317
theorem B1201391 : Blo 354756 1201391 := bstep (se 1 (by rfl) ⟨901043, by rfl⟩ : syracuseStep 1201391 = 1802087) B1802087
theorem B1890535 : Blo 354756 1890535 := bstep (se 1 (by rfl) ⟨1417901, by rfl⟩ : syracuseStep 1890535 = 2835803) B2835803
theorem B1203767 : Blo 354756 1203767 := bstep (se 1 (by rfl) ⟨902825, by rfl⟩ : syracuseStep 1203767 = 1805651) B1805651
theorem B680575 : Blo 354756 680575 := bstep (se 1 (by rfl) ⟨510431, by rfl⟩ : syracuseStep 680575 = 1020863) B1020863
theorem B4744423 : Blo 354756 4744423 := bstep (se 1 (by rfl) ⟨3558317, by rfl⟩ : syracuseStep 4744423 = 7116635) B7116635
theorem B484711 : Blo 354756 484711 := bstep (se 1 (by rfl) ⟨363533, by rfl⟩ : syracuseStep 484711 = 727067) B727067
theorem B1206143 : Blo 354756 1206143 := bstep (se 1 (by rfl) ⟨904607, by rfl⟩ : syracuseStep 1206143 = 1809215) B1809215
theorem B5171525 : Blo 354756 5171525 := bstep (se 4 (by rfl) ⟨484830, by rfl⟩ : syracuseStep 5171525 = 969661) B969661
theorem B355099 : Blo 354756 355099 := bstep (se 1 (by rfl) ⟨266324, by rfl⟩ : syracuseStep 355099 = 532649) B532649
theorem B355183 : Blo 354756 355183 := bstep (se 1 (by rfl) ⟨266387, by rfl⟩ : syracuseStep 355183 = 532775) B532775
theorem B355263 : Blo 354756 355263 := bstep (se 1 (by rfl) ⟨266447, by rfl⟩ : syracuseStep 355263 = 532895) B532895
theorem B49572971 : Blo 354756 49572971 := bstep (se 1 (by rfl) ⟨37179728, by rfl⟩ : syracuseStep 49572971 = 74359457) B74359457
theorem B355647 : Blo 354756 355647 := bstep (se 1 (by rfl) ⟨266735, by rfl⟩ : syracuseStep 355647 = 533471) B533471
theorem B355791 : Blo 354756 355791 := bstep (se 1 (by rfl) ⟨266843, by rfl⟩ : syracuseStep 355791 = 533687) B533687
theorem B355867 : Blo 354756 355867 := bstep (se 1 (by rfl) ⟨266900, by rfl⟩ : syracuseStep 355867 = 533801) B533801
theorem B355951 : Blo 354756 355951 := bstep (se 1 (by rfl) ⟨266963, by rfl⟩ : syracuseStep 355951 = 533927) B533927
theorem B356095 : Blo 354756 356095 := bstep (se 1 (by rfl) ⟨267071, by rfl⟩ : syracuseStep 356095 = 534143) B534143
theorem B356199 : Blo 354756 356199 := bstep (se 1 (by rfl) ⟨267149, by rfl⟩ : syracuseStep 356199 = 534299) B534299
theorem B356351 : Blo 354756 356351 := bstep (se 1 (by rfl) ⟨267263, by rfl⟩ : syracuseStep 356351 = 534527) B534527
theorem B356655 : Blo 354756 356655 := bstep (se 1 (by rfl) ⟨267491, by rfl⟩ : syracuseStep 356655 = 534983) B534983
theorem B356839 : Blo 354756 356839 := bstep (se 1 (by rfl) ⟨267629, by rfl⟩ : syracuseStep 356839 = 535259) B535259
theorem B356895 : Blo 354756 356895 := bstep (se 1 (by rfl) ⟨267671, by rfl⟩ : syracuseStep 356895 = 535343) B535343
theorem B357055 : Blo 354756 357055 := bstep (se 1 (by rfl) ⟨267791, by rfl⟩ : syracuseStep 357055 = 535583) B535583
theorem B357119 : Blo 354756 357119 := bstep (se 1 (by rfl) ⟨267839, by rfl⟩ : syracuseStep 357119 = 535679) B535679
theorem B357703 : Blo 354756 357703 := bstep (se 1 (by rfl) ⟨268277, by rfl⟩ : syracuseStep 357703 = 536555) B536555
theorem B358171 : Blo 354756 358171 := bstep (se 1 (by rfl) ⟨268628, by rfl⟩ : syracuseStep 358171 = 537257) B537257
theorem B358607 : Blo 354756 358607 := bstep (se 1 (by rfl) ⟨268955, by rfl⟩ : syracuseStep 358607 = 537911) B537911
theorem B3340523 : Blo 354756 3340523 := bstep (se 1 (by rfl) ⟨2505392, by rfl⟩ : syracuseStep 3340523 = 5010785) B5010785
theorem B686945 : Blo 354756 686945 := bstep (se 2 (by rfl) ⟨257604, by rfl⟩ : syracuseStep 686945 = 515209) B515209
theorem B1440641 : Blo 354756 1440641 := bstep (se 2 (by rfl) ⟨540240, by rfl⟩ : syracuseStep 1440641 = 1080481) B1080481
theorem B2620289 : Blo 354756 2620289 := bstep (se 2 (by rfl) ⟨982608, by rfl⟩ : syracuseStep 2620289 = 1965217) B1965217
theorem B1932511 : Blo 354756 1932511 := bstep (se 1 (by rfl) ⟨1449383, by rfl⟩ : syracuseStep 1932511 = 2898767) B2898767
theorem B1016705 : Blo 354756 1016705 := bstep (se 2 (by rfl) ⟨381264, by rfl⟩ : syracuseStep 1016705 = 762529) B762529
theorem B6325897 : Blo 354756 6325897 := bstep (se 2 (by rfl) ⟨2372211, by rfl⟩ : syracuseStep 6325897 = 4744423) B4744423
theorem B7737727 : Blo 354756 7737727 := bstep (se 1 (by rfl) ⟨5803295, by rfl⟩ : syracuseStep 7737727 = 11606591) B11606591
theorem B14718509 : Blo 354756 14718509 := bstep (se 3 (by rfl) ⟨2759720, by rfl⟩ : syracuseStep 14718509 = 5519441) B5519441
theorem B399271 : Blo 354756 399271 := bstep (se 1 (by rfl) ⟨299453, by rfl⟩ : syracuseStep 399271 = 598907) B598907
theorem B3447683 : Blo 354756 3447683 := bstep (se 1 (by rfl) ⟨2585762, by rfl⟩ : syracuseStep 3447683 = 5171525) B5171525
theorem B402367 : Blo 354756 402367 := bstep (se 1 (by rfl) ⟨301775, by rfl⟩ : syracuseStep 402367 = 603551) B603551
theorem B533735 : Blo 354756 533735 := bstep (se 1 (by rfl) ⟨400301, by rfl⟩ : syracuseStep 533735 = 800603) B800603
theorem B534185 : Blo 354756 534185 := bstep (se 2 (by rfl) ⟨200319, by rfl⟩ : syracuseStep 534185 = 400639) B400639
theorem B15345359 : Blo 354756 15345359 := bstep (se 1 (by rfl) ⟨11509019, by rfl⟩ : syracuseStep 15345359 = 23018039) B23018039
theorem B960427 : Blo 354756 960427 := bstep (se 1 (by rfl) ⟨720320, by rfl⟩ : syracuseStep 960427 = 1440641) B1440641
theorem B1746859 : Blo 354756 1746859 := bstep (se 1 (by rfl) ⟨1310144, by rfl⟩ : syracuseStep 1746859 = 2620289) B2620289
theorem B534767 : Blo 354756 534767 := bstep (se 1 (by rfl) ⟨401075, by rfl⟩ : syracuseStep 534767 = 802151) B802151
theorem B1453159 : Blo 354756 1453159 := bstep (se 1 (by rfl) ⟨1089869, by rfl⟩ : syracuseStep 1453159 = 2179739) B2179739
theorem B1715327 : Blo 354756 1715327 := bstep (se 1 (by rfl) ⟨1286495, by rfl⟩ : syracuseStep 1715327 = 2572991) B2572991
theorem B4337489 : Blo 354756 4337489 := bstep (se 2 (by rfl) ⟨1626558, by rfl⟩ : syracuseStep 4337489 = 3253117) B3253117
theorem B798623 : Blo 354756 798623 := bstep (se 1 (by rfl) ⟨598967, by rfl⟩ : syracuseStep 798623 = 1197935) B1197935
theorem B799055 : Blo 354756 799055 := bstep (se 1 (by rfl) ⟨599291, by rfl⟩ : syracuseStep 799055 = 1198583) B1198583
theorem B537023 : Blo 354756 537023 := bstep (se 1 (by rfl) ⟨402767, by rfl⟩ : syracuseStep 537023 = 805535) B805535
theorem B537071 : Blo 354756 537071 := bstep (se 1 (by rfl) ⟨402803, by rfl⟩ : syracuseStep 537071 = 805607) B805607
theorem B537371 : Blo 354756 537371 := bstep (se 1 (by rfl) ⟨403028, by rfl⟩ : syracuseStep 537371 = 806057) B806057
theorem B1619959 : Blo 354756 1619959 := bstep (se 1 (by rfl) ⟨1214969, by rfl⟩ : syracuseStep 1619959 = 2429939) B2429939
theorem B800927 : Blo 354756 800927 := bstep (se 1 (by rfl) ⟨600695, by rfl⟩ : syracuseStep 800927 = 1201391) B1201391
theorem B964967 : Blo 354756 964967 := bstep (se 1 (by rfl) ⟨723725, by rfl⟩ : syracuseStep 964967 = 1447451) B1447451
theorem B899687 : Blo 354756 899687 := bstep (se 1 (by rfl) ⟨674765, by rfl⟩ : syracuseStep 899687 = 1349531) B1349531
theorem B802511 : Blo 354756 802511 := bstep (se 1 (by rfl) ⟨601883, by rfl⟩ : syracuseStep 802511 = 1203767) B1203767
theorem B4047407 : Blo 354756 4047407 := bstep (se 1 (by rfl) ⟨3035555, by rfl⟩ : syracuseStep 4047407 = 6071111) B6071111
theorem B803465 : Blo 354756 803465 := bstep (se 2 (by rfl) ⟨301299, by rfl⟩ : syracuseStep 803465 = 602599) B602599
theorem B804095 : Blo 354756 804095 := bstep (se 1 (by rfl) ⟨603071, by rfl⟩ : syracuseStep 804095 = 1206143) B1206143
theorem B15582785 : Blo 354756 15582785 := bstep (se 2 (by rfl) ⟨5843544, by rfl⟩ : syracuseStep 15582785 = 11687089) B11687089
theorem B902735 : Blo 354756 902735 := bstep (se 1 (by rfl) ⟨677051, by rfl⟩ : syracuseStep 902735 = 1354103) B1354103
theorem B804617 : Blo 354756 804617 := bstep (se 2 (by rfl) ⟨301731, by rfl⟩ : syracuseStep 804617 = 603463) B603463
theorem B33048647 : Blo 354756 33048647 := bstep (se 1 (by rfl) ⟨24786485, by rfl⟩ : syracuseStep 33048647 = 49572971) B49572971
theorem B903271 : Blo 354756 903271 := bstep (se 1 (by rfl) ⟨677453, by rfl⟩ : syracuseStep 903271 = 1354907) B1354907
theorem B2576681 : Blo 354756 2576681 := bstep (se 2 (by rfl) ⟨966255, by rfl⟩ : syracuseStep 2576681 = 1932511) B1932511
theorem B907433 : Blo 354756 907433 := bstep (se 2 (by rfl) ⟨340287, by rfl⟩ : syracuseStep 907433 = 680575) B680575
theorem B2021881 : Blo 354756 2021881 := bstep (se 2 (by rfl) ⟨758205, by rfl⟩ : syracuseStep 2021881 = 1516411) B1516411
theorem B3432071 : Blo 354756 3432071 := bstep (se 1 (by rfl) ⟨2574053, by rfl⟩ : syracuseStep 3432071 = 5148107) B5148107
theorem B2286305 : Blo 354756 2286305 := bstep (se 2 (by rfl) ⟨857364, by rfl⟩ : syracuseStep 2286305 = 1714729) B1714729
theorem B1205711 : Blo 354756 1205711 := bstep (se 1 (by rfl) ⟨904283, by rfl⟩ : syracuseStep 1205711 = 1808567) B1808567
theorem B1927081 : Blo 354756 1927081 := bstep (se 2 (by rfl) ⟨722655, by rfl⟩ : syracuseStep 1927081 = 1445311) B1445311
theorem B354783 : Blo 354756 354783 := bstep (se 1 (by rfl) ⟨266087, by rfl⟩ : syracuseStep 354783 = 532175) B532175
theorem B3238379 : Blo 354756 3238379 := bstep (se 1 (by rfl) ⟨2428784, by rfl⟩ : syracuseStep 3238379 = 4857569) B4857569
theorem B354927 : Blo 354756 354927 := bstep (se 1 (by rfl) ⟨266195, by rfl⟩ : syracuseStep 354927 = 532391) B532391
theorem B355495 : Blo 354756 355495 := bstep (se 1 (by rfl) ⟨266621, by rfl⟩ : syracuseStep 355495 = 533243) B533243
theorem B8908061 : Blo 354756 8908061 := bstep (se 3 (by rfl) ⟨1670261, by rfl⟩ : syracuseStep 8908061 = 3340523) B3340523
theorem B356287 : Blo 354756 356287 := bstep (se 1 (by rfl) ⟨267215, by rfl⟩ : syracuseStep 356287 = 534431) B534431
theorem B356399 : Blo 354756 356399 := bstep (se 1 (by rfl) ⟨267299, by rfl⟩ : syracuseStep 356399 = 534599) B534599
theorem B2585125 : Blo 354756 2585125 := bstep (se 4 (by rfl) ⟨242355, by rfl⟩ : syracuseStep 2585125 = 484711) B484711
theorem B357023 : Blo 354756 357023 := bstep (se 1 (by rfl) ⟨267767, by rfl⟩ : syracuseStep 357023 = 535535) B535535
theorem B357223 : Blo 354756 357223 := bstep (se 1 (by rfl) ⟨267917, by rfl⟩ : syracuseStep 357223 = 535835) B535835
theorem B357479 : Blo 354756 357479 := bstep (se 1 (by rfl) ⟨268109, by rfl⟩ : syracuseStep 357479 = 536219) B536219
theorem B20903305 : Blo 354756 20903305 := bstep (se 2 (by rfl) ⟨7838739, by rfl⟩ : syracuseStep 20903305 = 15677479) B15677479
theorem B2520713 : Blo 354756 2520713 := bstep (se 2 (by rfl) ⟨945267, by rfl⟩ : syracuseStep 2520713 = 1890535) B1890535
theorem B12352115 : Blo 354756 12352115 := bstep (se 1 (by rfl) ⟨9264086, by rfl⟩ : syracuseStep 12352115 = 18528173) B18528173
theorem B719785 : Blo 354756 719785 := bstep (se 2 (by rfl) ⟨269919, by rfl⟩ : syracuseStep 719785 = 539839) B539839
theorem B457963 : Blo 354756 457963 := bstep (se 1 (by rfl) ⟨343472, by rfl⟩ : syracuseStep 457963 = 686945) B686945
theorem B1280569 : Blo 354756 1280569 := bstep (se 2 (by rfl) ⟨480213, by rfl⟩ : syracuseStep 1280569 = 960427) B960427
theorem B2329145 : Blo 354756 2329145 := bstep (se 2 (by rfl) ⟨873429, by rfl⟩ : syracuseStep 2329145 = 1746859) B1746859
theorem B2298455 : Blo 354756 2298455 := bstep (se 1 (by rfl) ⟨1723841, by rfl⟩ : syracuseStep 2298455 = 3447683) B3447683
theorem B3838853 : Blo 354756 3838853 := bstep (se 4 (by rfl) ⟨359892, by rfl⟩ : syracuseStep 3838853 = 719785) B719785
theorem B3446833 : Blo 354756 3446833 := bstep (se 2 (by rfl) ⟨1292562, by rfl⟩ : syracuseStep 3446833 = 2585125) B2585125
theorem B10230239 : Blo 354756 10230239 := bstep (se 1 (by rfl) ⟨7672679, by rfl⟩ : syracuseStep 10230239 = 15345359) B15345359
theorem B532361 : Blo 354756 532361 := bstep (se 2 (by rfl) ⟨199635, by rfl⟩ : syracuseStep 532361 = 399271) B399271
theorem B2891659 : Blo 354756 2891659 := bstep (se 1 (by rfl) ⟨2168744, by rfl⟩ : syracuseStep 2891659 = 4337489) B4337489
theorem B532415 : Blo 354756 532415 := bstep (se 1 (by rfl) ⟨399311, by rfl⟩ : syracuseStep 532415 = 798623) B798623
theorem B532703 : Blo 354756 532703 := bstep (se 1 (by rfl) ⟨399527, by rfl⟩ : syracuseStep 532703 = 799055) B799055
theorem B2695841 : Blo 354756 2695841 := bstep (se 2 (by rfl) ⟨1010940, by rfl⟩ : syracuseStep 2695841 = 2021881) B2021881
theorem B1680475 : Blo 354756 1680475 := bstep (se 1 (by rfl) ⟨1260356, by rfl⟩ : syracuseStep 1680475 = 2520713) B2520713
theorem B533951 : Blo 354756 533951 := bstep (se 1 (by rfl) ⟨400463, by rfl⟩ : syracuseStep 533951 = 800927) B800927
theorem B599791 : Blo 354756 599791 := bstep (se 1 (by rfl) ⟨449843, by rfl⟩ : syracuseStep 599791 = 899687) B899687
theorem B8234743 : Blo 354756 8234743 := bstep (se 1 (by rfl) ⟨6176057, by rfl⟩ : syracuseStep 8234743 = 12352115) B12352115
theorem B535007 : Blo 354756 535007 := bstep (se 1 (by rfl) ⟨401255, by rfl⟩ : syracuseStep 535007 = 802511) B802511
theorem B2698271 : Blo 354756 2698271 := bstep (se 1 (by rfl) ⟨2023703, by rfl⟩ : syracuseStep 2698271 = 4047407) B4047407
theorem B535643 : Blo 354756 535643 := bstep (se 1 (by rfl) ⟨401732, by rfl⟩ : syracuseStep 535643 = 803465) B803465
theorem B536063 : Blo 354756 536063 := bstep (se 1 (by rfl) ⟨402047, by rfl⟩ : syracuseStep 536063 = 804095) B804095
theorem B601823 : Blo 354756 601823 := bstep (se 1 (by rfl) ⟨451367, by rfl⟩ : syracuseStep 601823 = 902735) B902735
theorem B536411 : Blo 354756 536411 := bstep (se 1 (by rfl) ⟨402308, by rfl⟩ : syracuseStep 536411 = 804617) B804617
theorem B536489 : Blo 354756 536489 := bstep (se 2 (by rfl) ⟨201183, by rfl⟩ : syracuseStep 536489 = 402367) B402367
theorem B22032431 : Blo 354756 22032431 := bstep (se 1 (by rfl) ⟨16524323, by rfl⟩ : syracuseStep 22032431 = 33048647) B33048647
theorem B8434529 : Blo 354756 8434529 := bstep (se 2 (by rfl) ⟨3162948, by rfl⟩ : syracuseStep 8434529 = 6325897) B6325897
theorem B2569441 : Blo 354756 2569441 := bstep (se 2 (by rfl) ⟨963540, by rfl⟩ : syracuseStep 2569441 = 1927081) B1927081
theorem B1717787 : Blo 354756 1717787 := bstep (se 1 (by rfl) ⟨1288340, by rfl⟩ : syracuseStep 1717787 = 2576681) B2576681
theorem B9812339 : Blo 354756 9812339 := bstep (se 1 (by rfl) ⟨7359254, by rfl⟩ : syracuseStep 9812339 = 14718509) B14718509
theorem B604955 : Blo 354756 604955 := bstep (se 1 (by rfl) ⟨453716, by rfl⟩ : syracuseStep 604955 = 907433) B907433
theorem B1524203 : Blo 354756 1524203 := bstep (se 1 (by rfl) ⟨1143152, by rfl⟩ : syracuseStep 1524203 = 2286305) B2286305
theorem B7750181 : Blo 354756 7750181 := bstep (se 4 (by rfl) ⟨726579, by rfl⟩ : syracuseStep 7750181 = 1453159) B1453159
theorem B166216373 : Blo 354756 166216373 := bstep (se 5 (by rfl) ⟨7791392, by rfl⟩ : syracuseStep 166216373 = 15582785) B15582785
theorem B2573245 : Blo 354756 2573245 := bstep (se 3 (by rfl) ⟨482483, by rfl⟩ : syracuseStep 2573245 = 964967) B964967
theorem B803807 : Blo 354756 803807 := bstep (se 1 (by rfl) ⟨602855, by rfl⟩ : syracuseStep 803807 = 1205711) B1205711
theorem B2442469 : Blo 354756 2442469 := bstep (se 4 (by rfl) ⟨228981, by rfl⟩ : syracuseStep 2442469 = 457963) B457963
theorem B27871073 : Blo 354756 27871073 := bstep (se 2 (by rfl) ⟨10451652, by rfl⟩ : syracuseStep 27871073 = 20903305) B20903305
theorem B677803 : Blo 354756 677803 := bstep (se 1 (by rfl) ⟨508352, by rfl⟩ : syracuseStep 677803 = 1016705) B1016705
theorem B1204361 : Blo 354756 1204361 := bstep (se 2 (by rfl) ⟨451635, by rfl⟩ : syracuseStep 1204361 = 903271) B903271
theorem B2288047 : Blo 354756 2288047 := bstep (se 1 (by rfl) ⟨1716035, by rfl⟩ : syracuseStep 2288047 = 3432071) B3432071
theorem B10316969 : Blo 354756 10316969 := bstep (se 2 (by rfl) ⟨3868863, by rfl⟩ : syracuseStep 10316969 = 7737727) B7737727
theorem B355823 : Blo 354756 355823 := bstep (se 1 (by rfl) ⟨266867, by rfl⟩ : syracuseStep 355823 = 533735) B533735
theorem B356123 : Blo 354756 356123 := bstep (se 1 (by rfl) ⟨267092, by rfl⟩ : syracuseStep 356123 = 534185) B534185
theorem B356511 : Blo 354756 356511 := bstep (se 1 (by rfl) ⟨267383, by rfl⟩ : syracuseStep 356511 = 534767) B534767
theorem B2158919 : Blo 354756 2158919 := bstep (se 1 (by rfl) ⟨1619189, by rfl⟩ : syracuseStep 2158919 = 3238379) B3238379
theorem B1143551 : Blo 354756 1143551 := bstep (se 1 (by rfl) ⟨857663, by rfl⟩ : syracuseStep 1143551 = 1715327) B1715327
theorem B2159945 : Blo 354756 2159945 := bstep (se 2 (by rfl) ⟨809979, by rfl⟩ : syracuseStep 2159945 = 1619959) B1619959
theorem B358015 : Blo 354756 358015 := bstep (se 1 (by rfl) ⟨268511, by rfl⟩ : syracuseStep 358015 = 537023) B537023
theorem B358047 : Blo 354756 358047 := bstep (se 1 (by rfl) ⟨268535, by rfl⟩ : syracuseStep 358047 = 537071) B537071
theorem B358247 : Blo 354756 358247 := bstep (se 1 (by rfl) ⟨268685, by rfl⟩ : syracuseStep 358247 = 537371) B537371
theorem B23754829 : Blo 354756 23754829 := bstep (se 3 (by rfl) ⟨4454030, by rfl⟩ : syracuseStep 23754829 = 8908061) B8908061
theorem B1016135 : Blo 354756 1016135 := bstep (se 1 (by rfl) ⟨762101, by rfl⟩ : syracuseStep 1016135 = 1524203) B1524203
theorem B18580715 : Blo 354756 18580715 := bstep (se 1 (by rfl) ⟨13935536, by rfl⟩ : syracuseStep 18580715 = 27871073) B27871073
theorem B10979657 : Blo 354756 10979657 := bstep (se 2 (by rfl) ⟨4117371, by rfl⟩ : syracuseStep 10979657 = 8234743) B8234743
theorem B3050729 : Blo 354756 3050729 := bstep (se 2 (by rfl) ⟨1144023, by rfl⟩ : syracuseStep 3050729 = 2288047) B2288047
theorem B2559235 : Blo 354756 2559235 := bstep (se 1 (by rfl) ⟨1919426, by rfl⟩ : syracuseStep 2559235 = 3838853) B3838853
theorem B1707425 : Blo 354756 1707425 := bstep (se 2 (by rfl) ⟨640284, by rfl⟩ : syracuseStep 1707425 = 1280569) B1280569
theorem B6820159 : Blo 354756 6820159 := bstep (se 1 (by rfl) ⟨5115119, by rfl⟩ : syracuseStep 6820159 = 10230239) B10230239
theorem B401215 : Blo 354756 401215 := bstep (se 1 (by rfl) ⟨300911, by rfl⟩ : syracuseStep 401215 = 601823) B601823
theorem B14688287 : Blo 354756 14688287 := bstep (se 1 (by rfl) ⟨11016215, by rfl⟩ : syracuseStep 14688287 = 22032431) B22032431
theorem B4595777 : Blo 354756 4595777 := bstep (se 2 (by rfl) ⟨1723416, by rfl⟩ : syracuseStep 4595777 = 3446833) B3446833
theorem B762367 : Blo 354756 762367 := bstep (se 1 (by rfl) ⟨571775, by rfl⟩ : syracuseStep 762367 = 1143551) B1143551
theorem B403303 : Blo 354756 403303 := bstep (se 1 (by rfl) ⟨302477, by rfl⟩ : syracuseStep 403303 = 604955) B604955
theorem B535871 : Blo 354756 535871 := bstep (se 1 (by rfl) ⟨401903, by rfl⟩ : syracuseStep 535871 = 803807) B803807
theorem B2240633 : Blo 354756 2240633 := bstep (se 2 (by rfl) ⟨840237, by rfl⟩ : syracuseStep 2240633 = 1680475) B1680475
theorem B3256625 : Blo 354756 3256625 := bstep (se 2 (by rfl) ⟨1221234, by rfl⟩ : syracuseStep 3256625 = 2442469) B2442469
theorem B1552763 : Blo 354756 1552763 := bstep (se 1 (by rfl) ⟨1164572, by rfl⟩ : syracuseStep 1552763 = 2329145) B2329145
theorem B799721 : Blo 354756 799721 := bstep (se 2 (by rfl) ⟨299895, by rfl⟩ : syracuseStep 799721 = 599791) B599791
theorem B802907 : Blo 354756 802907 := bstep (se 1 (by rfl) ⟨602180, by rfl⟩ : syracuseStep 802907 = 1204361) B1204361
theorem B3425921 : Blo 354756 3425921 := bstep (se 2 (by rfl) ⟨1284720, by rfl⟩ : syracuseStep 3425921 = 2569441) B2569441
theorem B903737 : Blo 354756 903737 := bstep (se 2 (by rfl) ⟨338901, by rfl⟩ : syracuseStep 903737 = 677803) B677803
theorem B31673105 : Blo 354756 31673105 := bstep (se 2 (by rfl) ⟨11877414, by rfl⟩ : syracuseStep 31673105 = 23754829) B23754829
theorem B5623019 : Blo 354756 5623019 := bstep (se 1 (by rfl) ⟨4217264, by rfl⟩ : syracuseStep 5623019 = 8434529) B8434529
theorem B6541559 : Blo 354756 6541559 := bstep (se 1 (by rfl) ⟨4906169, by rfl⟩ : syracuseStep 6541559 = 9812339) B9812339
theorem B3855545 : Blo 354756 3855545 := bstep (se 2 (by rfl) ⟨1445829, by rfl⟩ : syracuseStep 3855545 = 2891659) B2891659
theorem B110810915 : Blo 354756 110810915 := bstep (se 1 (by rfl) ⟨83108186, by rfl⟩ : syracuseStep 110810915 = 166216373) B166216373
theorem B3430993 : Blo 354756 3430993 := bstep (se 2 (by rfl) ⟨1286622, by rfl⟩ : syracuseStep 3430993 = 2573245) B2573245
theorem B20667149 : Blo 354756 20667149 := bstep (se 3 (by rfl) ⟨3875090, by rfl⟩ : syracuseStep 20667149 = 7750181) B7750181
theorem B1532303 : Blo 354756 1532303 := bstep (se 1 (by rfl) ⟨1149227, by rfl⟩ : syracuseStep 1532303 = 2298455) B2298455
theorem B354907 : Blo 354756 354907 := bstep (se 1 (by rfl) ⟨266180, by rfl⟩ : syracuseStep 354907 = 532361) B532361
theorem B354943 : Blo 354756 354943 := bstep (se 1 (by rfl) ⟨266207, by rfl⟩ : syracuseStep 354943 = 532415) B532415
theorem B355135 : Blo 354756 355135 := bstep (se 1 (by rfl) ⟨266351, by rfl⟩ : syracuseStep 355135 = 532703) B532703
theorem B1797227 : Blo 354756 1797227 := bstep (se 1 (by rfl) ⟨1347920, by rfl⟩ : syracuseStep 1797227 = 2695841) B2695841
theorem B355967 : Blo 354756 355967 := bstep (se 1 (by rfl) ⟨266975, by rfl⟩ : syracuseStep 355967 = 533951) B533951
theorem B356671 : Blo 354756 356671 := bstep (se 1 (by rfl) ⟨267503, by rfl⟩ : syracuseStep 356671 = 535007) B535007
theorem B1798847 : Blo 354756 1798847 := bstep (se 1 (by rfl) ⟨1349135, by rfl⟩ : syracuseStep 1798847 = 2698271) B2698271
theorem B357095 : Blo 354756 357095 := bstep (se 1 (by rfl) ⟨267821, by rfl⟩ : syracuseStep 357095 = 535643) B535643
theorem B6877979 : Blo 354756 6877979 := bstep (se 1 (by rfl) ⟨5158484, by rfl⟩ : syracuseStep 6877979 = 10316969) B10316969
theorem B357375 : Blo 354756 357375 := bstep (se 1 (by rfl) ⟨268031, by rfl⟩ : syracuseStep 357375 = 536063) B536063
theorem B357607 : Blo 354756 357607 := bstep (se 1 (by rfl) ⟨268205, by rfl⟩ : syracuseStep 357607 = 536411) B536411
theorem B357659 : Blo 354756 357659 := bstep (se 1 (by rfl) ⟨268244, by rfl⟩ : syracuseStep 357659 = 536489) B536489
theorem B1439279 : Blo 354756 1439279 := bstep (se 1 (by rfl) ⟨1079459, by rfl⟩ : syracuseStep 1439279 = 2158919) B2158919
theorem B1439963 : Blo 354756 1439963 := bstep (se 1 (by rfl) ⟨1079972, by rfl⟩ : syracuseStep 1439963 = 2159945) B2159945
theorem B1145191 : Blo 354756 1145191 := bstep (se 1 (by rfl) ⟨858893, by rfl⟩ : syracuseStep 1145191 = 1717787) B1717787
theorem B1016489 : Blo 354756 1016489 := bstep (se 2 (by rfl) ⟨381183, by rfl⟩ : syracuseStep 1016489 = 762367) B762367
theorem B12387143 : Blo 354756 12387143 := bstep (se 1 (by rfl) ⟨9290357, by rfl⟩ : syracuseStep 12387143 = 18580715) B18580715
theorem B2033819 : Blo 354756 2033819 := bstep (se 1 (by rfl) ⟨1525364, by rfl⟩ : syracuseStep 2033819 = 3050729) B3050729
theorem B4361039 : Blo 354756 4361039 := bstep (se 1 (by rfl) ⟨3270779, by rfl⟩ : syracuseStep 4361039 = 6541559) B6541559
theorem B3412313 : Blo 354756 3412313 := bstep (se 2 (by rfl) ⟨1279617, by rfl⟩ : syracuseStep 3412313 = 2559235) B2559235
theorem B1021535 : Blo 354756 1021535 := bstep (se 1 (by rfl) ⟨766151, by rfl⟩ : syracuseStep 1021535 = 1532303) B1532303
theorem B2171083 : Blo 354756 2171083 := bstep (se 1 (by rfl) ⟨1628312, by rfl⟩ : syracuseStep 2171083 = 3256625) B3256625
theorem B533147 : Blo 354756 533147 := bstep (se 1 (by rfl) ⟨399860, by rfl⟩ : syracuseStep 533147 = 799721) B799721
theorem B959519 : Blo 354756 959519 := bstep (se 1 (by rfl) ⟨719639, by rfl⟩ : syracuseStep 959519 = 1439279) B1439279
theorem B959975 : Blo 354756 959975 := bstep (se 1 (by rfl) ⟨719981, by rfl⟩ : syracuseStep 959975 = 1439963) B1439963
theorem B534953 : Blo 354756 534953 := bstep (se 2 (by rfl) ⟨200607, by rfl⟩ : syracuseStep 534953 = 401215) B401215
theorem B535271 : Blo 354756 535271 := bstep (se 1 (by rfl) ⟨401453, by rfl⟩ : syracuseStep 535271 = 802907) B802907
theorem B5975021 : Blo 354756 5975021 := bstep (se 3 (by rfl) ⟨1120316, by rfl⟩ : syracuseStep 5975021 = 2240633) B2240633
theorem B7319771 : Blo 354756 7319771 := bstep (se 1 (by rfl) ⟨5489828, by rfl⟩ : syracuseStep 7319771 = 10979657) B10979657
theorem B602491 : Blo 354756 602491 := bstep (se 1 (by rfl) ⟨451868, by rfl⟩ : syracuseStep 602491 = 903737) B903737
theorem B21115403 : Blo 354756 21115403 := bstep (se 1 (by rfl) ⟨15836552, by rfl⟩ : syracuseStep 21115403 = 31673105) B31673105
theorem B3748679 : Blo 354756 3748679 := bstep (se 1 (by rfl) ⟨2811509, by rfl⟩ : syracuseStep 3748679 = 5623019) B5623019
theorem B537737 : Blo 354756 537737 := bstep (se 2 (by rfl) ⟨201651, by rfl⟩ : syracuseStep 537737 = 403303) B403303
theorem B2570363 : Blo 354756 2570363 := bstep (se 1 (by rfl) ⟨1927772, by rfl⟩ : syracuseStep 2570363 = 3855545) B3855545
theorem B73873943 : Blo 354756 73873943 := bstep (se 1 (by rfl) ⟨55405457, by rfl⟩ : syracuseStep 73873943 = 110810915) B110810915
theorem B13778099 : Blo 354756 13778099 := bstep (se 1 (by rfl) ⟨10333574, by rfl⟩ : syracuseStep 13778099 = 20667149) B20667149
theorem B3063851 : Blo 354756 3063851 := bstep (se 1 (by rfl) ⟨2297888, by rfl⟩ : syracuseStep 3063851 = 4595777) B4595777
theorem B9093545 : Blo 354756 9093545 := bstep (se 2 (by rfl) ⟨3410079, by rfl⟩ : syracuseStep 9093545 = 6820159) B6820159
theorem B1198151 : Blo 354756 1198151 := bstep (se 1 (by rfl) ⟨898613, by rfl⟩ : syracuseStep 1198151 = 1797227) B1797227
theorem B1035175 : Blo 354756 1035175 := bstep (se 1 (by rfl) ⟨776381, by rfl⟩ : syracuseStep 1035175 = 1552763) B1552763
theorem B1199231 : Blo 354756 1199231 := bstep (se 1 (by rfl) ⟨899423, by rfl⟩ : syracuseStep 1199231 = 1798847) B1798847
theorem B1526921 : Blo 354756 1526921 := bstep (se 2 (by rfl) ⟨572595, by rfl⟩ : syracuseStep 1526921 = 1145191) B1145191
theorem B4574657 : Blo 354756 4574657 := bstep (se 2 (by rfl) ⟨1715496, by rfl⟩ : syracuseStep 4574657 = 3430993) B3430993
theorem B677423 : Blo 354756 677423 := bstep (se 1 (by rfl) ⟨508067, by rfl⟩ : syracuseStep 677423 = 1016135) B1016135
theorem B2283947 : Blo 354756 2283947 := bstep (se 1 (by rfl) ⟨1712960, by rfl⟩ : syracuseStep 2283947 = 3425921) B3425921
theorem B1138283 : Blo 354756 1138283 := bstep (se 1 (by rfl) ⟨853712, by rfl⟩ : syracuseStep 1138283 = 1707425) B1707425
theorem B9792191 : Blo 354756 9792191 := bstep (se 1 (by rfl) ⟨7344143, by rfl⟩ : syracuseStep 9792191 = 14688287) B14688287
theorem B357247 : Blo 354756 357247 := bstep (se 1 (by rfl) ⟨267935, by rfl⟩ : syracuseStep 357247 = 535871) B535871
theorem B4585319 : Blo 354756 4585319 := bstep (se 1 (by rfl) ⟨3438989, by rfl⟩ : syracuseStep 4585319 = 6877979) B6877979
theorem B6062363 : Blo 354756 6062363 := bstep (se 1 (by rfl) ⟨4546772, by rfl⟩ : syracuseStep 6062363 = 9093545) B9093545
theorem B8258095 : Blo 354756 8258095 := bstep (se 1 (by rfl) ⟨6193571, by rfl⟩ : syracuseStep 8258095 = 12387143) B12387143
theorem B1017947 : Blo 354756 1017947 := bstep (se 1 (by rfl) ⟨763460, by rfl⟩ : syracuseStep 1017947 = 1526921) B1526921
theorem B3049771 : Blo 354756 3049771 := bstep (se 1 (by rfl) ⟨2287328, by rfl⟩ : syracuseStep 3049771 = 4574657) B4574657
theorem B1380233 : Blo 354756 1380233 := bstep (se 2 (by rfl) ⟨517587, by rfl⟩ : syracuseStep 1380233 = 1035175) B1035175
theorem B1806461 : Blo 354756 1806461 := bstep (se 3 (by rfl) ⟨338711, by rfl⟩ : syracuseStep 1806461 = 677423) B677423
theorem B758855 : Blo 354756 758855 := bstep (se 1 (by rfl) ⟨569141, by rfl⟩ : syracuseStep 758855 = 1138283) B1138283
theorem B6528127 : Blo 354756 6528127 := bstep (se 1 (by rfl) ⟨4896095, by rfl⟩ : syracuseStep 6528127 = 9792191) B9792191
theorem B2499119 : Blo 354756 2499119 := bstep (se 1 (by rfl) ⟨1874339, by rfl⟩ : syracuseStep 2499119 = 3748679) B3748679
theorem B3056879 : Blo 354756 3056879 := bstep (se 1 (by rfl) ⟨2292659, by rfl⟩ : syracuseStep 3056879 = 4585319) B4585319
theorem B1713575 : Blo 354756 1713575 := bstep (se 1 (by rfl) ⟨1285181, by rfl⟩ : syracuseStep 1713575 = 2570363) B2570363
theorem B9185399 : Blo 354756 9185399 := bstep (se 1 (by rfl) ⟨6889049, by rfl⟩ : syracuseStep 9185399 = 13778099) B13778099
theorem B2042567 : Blo 354756 2042567 := bstep (se 1 (by rfl) ⟨1531925, by rfl⟩ : syracuseStep 2042567 = 3063851) B3063851
theorem B2894777 : Blo 354756 2894777 := bstep (se 2 (by rfl) ⟨1085541, by rfl⟩ : syracuseStep 2894777 = 2171083) B2171083
theorem B798767 : Blo 354756 798767 := bstep (se 1 (by rfl) ⟨599075, by rfl⟩ : syracuseStep 798767 = 1198151) B1198151
theorem B1355879 : Blo 354756 1355879 := bstep (se 1 (by rfl) ⟨1016909, by rfl⟩ : syracuseStep 1355879 = 2033819) B2033819
theorem B799487 : Blo 354756 799487 := bstep (se 1 (by rfl) ⟨599615, by rfl⟩ : syracuseStep 799487 = 1199231) B1199231
theorem B2274875 : Blo 354756 2274875 := bstep (se 1 (by rfl) ⟨1706156, by rfl⟩ : syracuseStep 2274875 = 3412313) B3412313
theorem B1522631 : Blo 354756 1522631 := bstep (se 1 (by rfl) ⟨1141973, by rfl⟩ : syracuseStep 1522631 = 2283947) B2283947
theorem B803321 : Blo 354756 803321 := bstep (se 2 (by rfl) ⟨301245, by rfl⟩ : syracuseStep 803321 = 602491) B602491
theorem B639679 : Blo 354756 639679 := bstep (se 1 (by rfl) ⟨479759, by rfl⟩ : syracuseStep 639679 = 959519) B959519
theorem B639983 : Blo 354756 639983 := bstep (se 1 (by rfl) ⟨479987, by rfl⟩ : syracuseStep 639983 = 959975) B959975
theorem B3983347 : Blo 354756 3983347 := bstep (se 1 (by rfl) ⟨2987510, by rfl⟩ : syracuseStep 3983347 = 5975021) B5975021
theorem B14076935 : Blo 354756 14076935 := bstep (se 1 (by rfl) ⟨10557701, by rfl⟩ : syracuseStep 14076935 = 21115403) B21115403
theorem B677659 : Blo 354756 677659 := bstep (se 1 (by rfl) ⟨508244, by rfl⟩ : syracuseStep 677659 = 1016489) B1016489
theorem B2907359 : Blo 354756 2907359 := bstep (se 1 (by rfl) ⟨2180519, by rfl⟩ : syracuseStep 2907359 = 4361039) B4361039
theorem B681023 : Blo 354756 681023 := bstep (se 1 (by rfl) ⟨510767, by rfl⟩ : syracuseStep 681023 = 1021535) B1021535
theorem B355431 : Blo 354756 355431 := bstep (se 1 (by rfl) ⟨266573, by rfl⟩ : syracuseStep 355431 = 533147) B533147
theorem B356635 : Blo 354756 356635 := bstep (se 1 (by rfl) ⟨267476, by rfl⟩ : syracuseStep 356635 = 534953) B534953
theorem B356847 : Blo 354756 356847 := bstep (se 1 (by rfl) ⟨267635, by rfl⟩ : syracuseStep 356847 = 535271) B535271
theorem B4879847 : Blo 354756 4879847 := bstep (se 1 (by rfl) ⟨3659885, by rfl⟩ : syracuseStep 4879847 = 7319771) B7319771
theorem B358491 : Blo 354756 358491 := bstep (se 1 (by rfl) ⟨268868, by rfl⟩ : syracuseStep 358491 = 537737) B537737
theorem B49249295 : Blo 354756 49249295 := bstep (se 1 (by rfl) ⟨36936971, by rfl⟩ : syracuseStep 49249295 = 73873943) B73873943
theorem B426655 : Blo 354756 426655 := bstep (se 1 (by rfl) ⟨319991, by rfl⟩ : syracuseStep 426655 = 639983) B639983
theorem B852905 : Blo 354756 852905 := bstep (se 2 (by rfl) ⟨319839, by rfl⟩ : syracuseStep 852905 = 639679) B639679
theorem B920155 : Blo 354756 920155 := bstep (se 1 (by rfl) ⟨690116, by rfl⟩ : syracuseStep 920155 = 1380233) B1380233
theorem B5311129 : Blo 354756 5311129 := bstep (se 2 (by rfl) ⟨1991673, by rfl⟩ : syracuseStep 5311129 = 3983347) B3983347
theorem B44043173 : Blo 354756 44043173 := bstep (se 4 (by rfl) ⟨4129047, by rfl⟩ : syracuseStep 44043173 = 8258095) B8258095
theorem B4066361 : Blo 354756 4066361 := bstep (se 2 (by rfl) ⟨1524885, by rfl⟩ : syracuseStep 4066361 = 3049771) B3049771
theorem B1938239 : Blo 354756 1938239 := bstep (se 1 (by rfl) ⟨1453679, by rfl⟩ : syracuseStep 1938239 = 2907359) B2907359
theorem B2037919 : Blo 354756 2037919 := bstep (se 1 (by rfl) ⟨1528439, by rfl⟩ : syracuseStep 2037919 = 3056879) B3056879
theorem B532511 : Blo 354756 532511 := bstep (se 1 (by rfl) ⟨399383, by rfl⟩ : syracuseStep 532511 = 798767) B798767
theorem B532991 : Blo 354756 532991 := bstep (se 1 (by rfl) ⟨399743, by rfl⟩ : syracuseStep 532991 = 799487) B799487
theorem B3253231 : Blo 354756 3253231 := bstep (se 1 (by rfl) ⟨2439923, by rfl⟩ : syracuseStep 3253231 = 4879847) B4879847
theorem B1516583 : Blo 354756 1516583 := bstep (se 1 (by rfl) ⟨1137437, by rfl⟩ : syracuseStep 1516583 = 2274875) B2274875
theorem B4041575 : Blo 354756 4041575 := bstep (se 1 (by rfl) ⟨3031181, by rfl⟩ : syracuseStep 4041575 = 6062363) B6062363
theorem B535547 : Blo 354756 535547 := bstep (se 1 (by rfl) ⟨401660, by rfl⟩ : syracuseStep 535547 = 803321) B803321
theorem B9384623 : Blo 354756 9384623 := bstep (se 1 (by rfl) ⟨7038467, by rfl⟩ : syracuseStep 9384623 = 14076935) B14076935
theorem B4569533 : Blo 354756 4569533 := bstep (se 3 (by rfl) ⟨856787, by rfl⟩ : syracuseStep 4569533 = 1713575) B1713575
theorem B1361711 : Blo 354756 1361711 := bstep (se 1 (by rfl) ⟨1021283, by rfl⟩ : syracuseStep 1361711 = 2042567) B2042567
theorem B903545 : Blo 354756 903545 := bstep (se 2 (by rfl) ⟨338829, by rfl⟩ : syracuseStep 903545 = 677659) B677659
theorem B903919 : Blo 354756 903919 := bstep (se 1 (by rfl) ⟨677939, by rfl⟩ : syracuseStep 903919 = 1355879) B1355879
theorem B8704169 : Blo 354756 8704169 := bstep (se 2 (by rfl) ⟨3264063, by rfl⟩ : syracuseStep 8704169 = 6528127) B6528127
theorem B678631 : Blo 354756 678631 := bstep (se 1 (by rfl) ⟨508973, by rfl⟩ : syracuseStep 678631 = 1017947) B1017947
theorem B1204307 : Blo 354756 1204307 := bstep (se 1 (by rfl) ⟨903230, by rfl⟩ : syracuseStep 1204307 = 1806461) B1806461
theorem B2023613 : Blo 354756 2023613 := bstep (se 3 (by rfl) ⟨379427, by rfl⟩ : syracuseStep 2023613 = 758855) B758855
theorem B1666079 : Blo 354756 1666079 := bstep (se 1 (by rfl) ⟨1249559, by rfl⟩ : syracuseStep 1666079 = 2499119) B2499119
theorem B454015 : Blo 354756 454015 := bstep (se 1 (by rfl) ⟨340511, by rfl⟩ : syracuseStep 454015 = 681023) B681023
theorem B6123599 : Blo 354756 6123599 := bstep (se 1 (by rfl) ⟨4592699, by rfl⟩ : syracuseStep 6123599 = 9185399) B9185399
theorem B1929851 : Blo 354756 1929851 := bstep (se 1 (by rfl) ⟨1447388, by rfl⟩ : syracuseStep 1929851 = 2894777) B2894777
theorem B1015087 : Blo 354756 1015087 := bstep (se 1 (by rfl) ⟨761315, by rfl⟩ : syracuseStep 1015087 = 1522631) B1522631
theorem B32832863 : Blo 354756 32832863 := bstep (se 1 (by rfl) ⟨24624647, by rfl⟩ : syracuseStep 32832863 = 49249295) B49249295
theorem B29362115 : Blo 354756 29362115 := bstep (se 1 (by rfl) ⟨22021586, by rfl⟩ : syracuseStep 29362115 = 44043173) B44043173
theorem B5802779 : Blo 354756 5802779 := bstep (se 1 (by rfl) ⟨4352084, by rfl⟩ : syracuseStep 5802779 = 8704169) B8704169
theorem B7081505 : Blo 354756 7081505 := bstep (se 2 (by rfl) ⟨2655564, by rfl⟩ : syracuseStep 7081505 = 5311129) B5311129
theorem B1349075 : Blo 354756 1349075 := bstep (se 1 (by rfl) ⟨1011806, by rfl⟩ : syracuseStep 1349075 = 2023613) B2023613
theorem B2694383 : Blo 354756 2694383 := bstep (se 1 (by rfl) ⟨2020787, by rfl⟩ : syracuseStep 2694383 = 4041575) B4041575
theorem B1286567 : Blo 354756 1286567 := bstep (se 1 (by rfl) ⟨964925, by rfl⟩ : syracuseStep 1286567 = 1929851) B1929851
theorem B1353449 : Blo 354756 1353449 := bstep (se 2 (by rfl) ⟨507543, by rfl⟩ : syracuseStep 1353449 = 1015087) B1015087
theorem B568603 : Blo 354756 568603 := bstep (se 1 (by rfl) ⟨426452, by rfl⟩ : syracuseStep 568603 = 852905) B852905
theorem B568873 : Blo 354756 568873 := bstep (se 2 (by rfl) ⟨213327, by rfl⟩ : syracuseStep 568873 = 426655) B426655
theorem B4337641 : Blo 354756 4337641 := bstep (se 2 (by rfl) ⟨1626615, by rfl⟩ : syracuseStep 4337641 = 3253231) B3253231
theorem B602363 : Blo 354756 602363 := bstep (se 1 (by rfl) ⟨451772, by rfl⟩ : syracuseStep 602363 = 903545) B903545
theorem B1292159 : Blo 354756 1292159 := bstep (se 1 (by rfl) ⟨969119, by rfl⟩ : syracuseStep 1292159 = 1938239) B1938239
theorem B1226873 : Blo 354756 1226873 := bstep (se 2 (by rfl) ⟨460077, by rfl⟩ : syracuseStep 1226873 = 920155) B920155
theorem B605353 : Blo 354756 605353 := bstep (se 2 (by rfl) ⟨227007, by rfl⟩ : syracuseStep 605353 = 454015) B454015
theorem B802871 : Blo 354756 802871 := bstep (se 1 (by rfl) ⟨602153, by rfl⟩ : syracuseStep 802871 = 1204307) B1204307
theorem B4082399 : Blo 354756 4082399 := bstep (se 1 (by rfl) ⟨3061799, by rfl⟩ : syracuseStep 4082399 = 6123599) B6123599
theorem B904841 : Blo 354756 904841 := bstep (se 2 (by rfl) ⟨339315, by rfl⟩ : syracuseStep 904841 = 678631) B678631
theorem B907807 : Blo 354756 907807 := bstep (se 1 (by rfl) ⟨680855, by rfl⟩ : syracuseStep 907807 = 1361711) B1361711
theorem B2710907 : Blo 354756 2710907 := bstep (se 1 (by rfl) ⟨2033180, by rfl⟩ : syracuseStep 2710907 = 4066361) B4066361
theorem B1205225 : Blo 354756 1205225 := bstep (se 2 (by rfl) ⟨451959, by rfl⟩ : syracuseStep 1205225 = 903919) B903919
theorem B355007 : Blo 354756 355007 := bstep (se 1 (by rfl) ⟨266255, by rfl⟩ : syracuseStep 355007 = 532511) B532511
theorem B355327 : Blo 354756 355327 := bstep (se 1 (by rfl) ⟨266495, by rfl⟩ : syracuseStep 355327 = 532991) B532991
theorem B1011055 : Blo 354756 1011055 := bstep (se 1 (by rfl) ⟨758291, by rfl⟩ : syracuseStep 1011055 = 1516583) B1516583
theorem B357031 : Blo 354756 357031 := bstep (se 1 (by rfl) ⟨267773, by rfl⟩ : syracuseStep 357031 = 535547) B535547
theorem B1110719 : Blo 354756 1110719 := bstep (se 1 (by rfl) ⟨833039, by rfl⟩ : syracuseStep 1110719 = 1666079) B1666079
theorem B2717225 : Blo 354756 2717225 := bstep (se 2 (by rfl) ⟨1018959, by rfl⟩ : syracuseStep 2717225 = 2037919) B2037919
theorem B6256415 : Blo 354756 6256415 := bstep (se 1 (by rfl) ⟨4692311, by rfl⟩ : syracuseStep 6256415 = 9384623) B9384623
theorem B3046355 : Blo 354756 3046355 := bstep (se 1 (by rfl) ⟨2284766, by rfl⟩ : syracuseStep 3046355 = 4569533) B4569533
theorem B21888575 : Blo 354756 21888575 := bstep (se 1 (by rfl) ⟨16416431, by rfl⟩ : syracuseStep 21888575 = 32832863) B32832863
theorem B2721599 : Blo 354756 2721599 := bstep (se 1 (by rfl) ⟨2041199, by rfl⟩ : syracuseStep 2721599 = 4082399) B4082399
theorem B3868519 : Blo 354756 3868519 := bstep (se 1 (by rfl) ⟨2901389, by rfl⟩ : syracuseStep 3868519 = 5802779) B5802779
theorem B4721003 : Blo 354756 4721003 := bstep (se 1 (by rfl) ⟨3540752, by rfl⟩ : syracuseStep 4721003 = 7081505) B7081505
theorem B1348073 : Blo 354756 1348073 := bstep (se 2 (by rfl) ⟨505527, by rfl⟩ : syracuseStep 1348073 = 1011055) B1011055
theorem B758497 : Blo 354756 758497 := bstep (se 2 (by rfl) ⟨284436, by rfl⟩ : syracuseStep 758497 = 568873) B568873
theorem B1807271 : Blo 354756 1807271 := bstep (se 1 (by rfl) ⟨1355453, by rfl⟩ : syracuseStep 1807271 = 2710907) B2710907
theorem B857711 : Blo 354756 857711 := bstep (se 1 (by rfl) ⟨643283, by rfl⟩ : syracuseStep 857711 = 1286567) B1286567
theorem B401575 : Blo 354756 401575 := bstep (se 1 (by rfl) ⟨301181, by rfl⟩ : syracuseStep 401575 = 602363) B602363
theorem B1811483 : Blo 354756 1811483 := bstep (se 1 (by rfl) ⟨1358612, by rfl⟩ : syracuseStep 1811483 = 2717225) B2717225
theorem B4170943 : Blo 354756 4170943 := bstep (se 1 (by rfl) ⟨3128207, by rfl⟩ : syracuseStep 4170943 = 6256415) B6256415
theorem B861439 : Blo 354756 861439 := bstep (se 1 (by rfl) ⟨646079, by rfl⟩ : syracuseStep 861439 = 1292159) B1292159
theorem B14592383 : Blo 354756 14592383 := bstep (se 1 (by rfl) ⟨10944287, by rfl⟩ : syracuseStep 14592383 = 21888575) B21888575
theorem B535247 : Blo 354756 535247 := bstep (se 1 (by rfl) ⟨401435, by rfl⟩ : syracuseStep 535247 = 802871) B802871
theorem B2961917 : Blo 354756 2961917 := bstep (se 3 (by rfl) ⟨555359, by rfl⟩ : syracuseStep 2961917 = 1110719) B1110719
theorem B603227 : Blo 354756 603227 := bstep (se 1 (by rfl) ⟨452420, by rfl⟩ : syracuseStep 603227 = 904841) B904841
theorem B899383 : Blo 354756 899383 := bstep (se 1 (by rfl) ⟨674537, by rfl⟩ : syracuseStep 899383 = 1349075) B1349075
theorem B78298973 : Blo 354756 78298973 := bstep (se 3 (by rfl) ⟨14681057, by rfl⟩ : syracuseStep 78298973 = 29362115) B29362115
theorem B5783521 : Blo 354756 5783521 := bstep (se 2 (by rfl) ⟨2168820, by rfl⟩ : syracuseStep 5783521 = 4337641) B4337641
theorem B803483 : Blo 354756 803483 := bstep (se 1 (by rfl) ⟨602612, by rfl⟩ : syracuseStep 803483 = 1205225) B1205225
theorem B902299 : Blo 354756 902299 := bstep (se 1 (by rfl) ⟨676724, by rfl⟩ : syracuseStep 902299 = 1353449) B1353449
theorem B3032549 : Blo 354756 3032549 := bstep (se 4 (by rfl) ⟨284301, by rfl⟩ : syracuseStep 3032549 = 568603) B568603
theorem B807137 : Blo 354756 807137 := bstep (se 2 (by rfl) ⟨302676, by rfl⟩ : syracuseStep 807137 = 605353) B605353
theorem B1796255 : Blo 354756 1796255 := bstep (se 1 (by rfl) ⟨1347191, by rfl⟩ : syracuseStep 1796255 = 2694383) B2694383
theorem B3271661 : Blo 354756 3271661 := bstep (se 3 (by rfl) ⟨613436, by rfl⟩ : syracuseStep 3271661 = 1226873) B1226873
theorem B1210409 : Blo 354756 1210409 := bstep (se 2 (by rfl) ⟨453903, by rfl⟩ : syracuseStep 1210409 = 907807) B907807
theorem B2030903 : Blo 354756 2030903 := bstep (se 1 (by rfl) ⟨1523177, by rfl⟩ : syracuseStep 2030903 = 3046355) B3046355
theorem B3147335 : Blo 354756 3147335 := bstep (se 1 (by rfl) ⟨2360501, by rfl⟩ : syracuseStep 3147335 = 4721003) B4721003
theorem B1148585 : Blo 354756 1148585 := bstep (se 2 (by rfl) ⟨430719, by rfl⟩ : syracuseStep 1148585 = 861439) B861439
theorem B1974611 : Blo 354756 1974611 := bstep (se 1 (by rfl) ⟨1480958, by rfl⟩ : syracuseStep 1974611 = 2961917) B2961917
theorem B402151 : Blo 354756 402151 := bstep (se 1 (by rfl) ⟨301613, by rfl⟩ : syracuseStep 402151 = 603227) B603227
theorem B1353935 : Blo 354756 1353935 := bstep (se 1 (by rfl) ⟨1015451, by rfl⟩ : syracuseStep 1353935 = 2030903) B2030903
theorem B7711361 : Blo 354756 7711361 := bstep (se 2 (by rfl) ⟨2891760, by rfl⟩ : syracuseStep 7711361 = 5783521) B5783521
theorem B535433 : Blo 354756 535433 := bstep (se 2 (by rfl) ⟨200787, by rfl⟩ : syracuseStep 535433 = 401575) B401575
theorem B535655 : Blo 354756 535655 := bstep (se 1 (by rfl) ⟨401741, by rfl⟩ : syracuseStep 535655 = 803483) B803483
theorem B1814399 : Blo 354756 1814399 := bstep (se 1 (by rfl) ⟨1360799, by rfl⟩ : syracuseStep 1814399 = 2721599) B2721599
theorem B5158025 : Blo 354756 5158025 := bstep (se 2 (by rfl) ⟨1934259, by rfl⟩ : syracuseStep 5158025 = 3868519) B3868519
theorem B538091 : Blo 354756 538091 := bstep (se 1 (by rfl) ⟨403568, by rfl⟩ : syracuseStep 538091 = 807137) B807137
theorem B898715 : Blo 354756 898715 := bstep (se 1 (by rfl) ⟨674036, by rfl⟩ : syracuseStep 898715 = 1348073) B1348073
theorem B571807 : Blo 354756 571807 := bstep (se 1 (by rfl) ⟨428855, by rfl⟩ : syracuseStep 571807 = 857711) B857711
theorem B1197503 : Blo 354756 1197503 := bstep (se 1 (by rfl) ⟨898127, by rfl⟩ : syracuseStep 1197503 = 1796255) B1796255
theorem B2181107 : Blo 354756 2181107 := bstep (se 1 (by rfl) ⟨1635830, by rfl⟩ : syracuseStep 2181107 = 3271661) B3271661
theorem B1199177 : Blo 354756 1199177 := bstep (se 2 (by rfl) ⟨449691, by rfl⟩ : syracuseStep 1199177 = 899383) B899383
theorem B806939 : Blo 354756 806939 := bstep (se 1 (by rfl) ⟨605204, by rfl⟩ : syracuseStep 806939 = 1210409) B1210409
theorem B2021699 : Blo 354756 2021699 := bstep (se 1 (by rfl) ⟨1516274, by rfl⟩ : syracuseStep 2021699 = 3032549) B3032549
theorem B1203065 : Blo 354756 1203065 := bstep (se 2 (by rfl) ⟨451149, by rfl⟩ : syracuseStep 1203065 = 902299) B902299
theorem B5561257 : Blo 354756 5561257 := bstep (se 2 (by rfl) ⟨2085471, by rfl⟩ : syracuseStep 5561257 = 4170943) B4170943
theorem B1204847 : Blo 354756 1204847 := bstep (se 1 (by rfl) ⟨903635, by rfl⟩ : syracuseStep 1204847 = 1807271) B1807271
theorem B1207655 : Blo 354756 1207655 := bstep (se 1 (by rfl) ⟨905741, by rfl⟩ : syracuseStep 1207655 = 1811483) B1811483
theorem B1011329 : Blo 354756 1011329 := bstep (se 2 (by rfl) ⟨379248, by rfl⟩ : syracuseStep 1011329 = 758497) B758497
theorem B9728255 : Blo 354756 9728255 := bstep (se 1 (by rfl) ⟨7296191, by rfl⟩ : syracuseStep 9728255 = 14592383) B14592383
theorem B356831 : Blo 354756 356831 := bstep (se 1 (by rfl) ⟨267623, by rfl⟩ : syracuseStep 356831 = 535247) B535247
theorem B52199315 : Blo 354756 52199315 := bstep (se 1 (by rfl) ⟨39149486, by rfl⟩ : syracuseStep 52199315 = 78298973) B78298973
theorem B2098223 : Blo 354756 2098223 := bstep (se 1 (by rfl) ⟨1573667, by rfl⟩ : syracuseStep 2098223 = 3147335) B3147335
theorem B1347799 : Blo 354756 1347799 := bstep (se 1 (by rfl) ⟨1010849, by rfl⟩ : syracuseStep 1347799 = 2021699) B2021699
theorem B1316407 : Blo 354756 1316407 := bstep (se 1 (by rfl) ⟨987305, by rfl⟩ : syracuseStep 1316407 = 1974611) B1974611
theorem B762409 : Blo 354756 762409 := bstep (se 2 (by rfl) ⟨285903, by rfl⟩ : syracuseStep 762409 = 571807) B571807
theorem B599143 : Blo 354756 599143 := bstep (se 1 (by rfl) ⟨449357, by rfl⟩ : syracuseStep 599143 = 898715) B898715
theorem B7415009 : Blo 354756 7415009 := bstep (se 2 (by rfl) ⟨2780628, by rfl⟩ : syracuseStep 7415009 = 5561257) B5561257
theorem B798335 : Blo 354756 798335 := bstep (se 1 (by rfl) ⟨598751, by rfl⟩ : syracuseStep 798335 = 1197503) B1197503
theorem B536201 : Blo 354756 536201 := bstep (se 2 (by rfl) ⟨201075, by rfl⟩ : syracuseStep 536201 = 402151) B402151
theorem B1454071 : Blo 354756 1454071 := bstep (se 1 (by rfl) ⟨1090553, by rfl⟩ : syracuseStep 1454071 = 2181107) B2181107
theorem B799451 : Blo 354756 799451 := bstep (se 1 (by rfl) ⟨599588, by rfl⟩ : syracuseStep 799451 = 1199177) B1199177
theorem B537959 : Blo 354756 537959 := bstep (se 1 (by rfl) ⟨403469, by rfl⟩ : syracuseStep 537959 = 806939) B806939
theorem B3062893 : Blo 354756 3062893 := bstep (se 3 (by rfl) ⟨574292, by rfl⟩ : syracuseStep 3062893 = 1148585) B1148585
theorem B802043 : Blo 354756 802043 := bstep (se 1 (by rfl) ⟨601532, by rfl⟩ : syracuseStep 802043 = 1203065) B1203065
theorem B803231 : Blo 354756 803231 := bstep (se 1 (by rfl) ⟨602423, by rfl⟩ : syracuseStep 803231 = 1204847) B1204847
theorem B902623 : Blo 354756 902623 := bstep (se 1 (by rfl) ⟨676967, by rfl⟩ : syracuseStep 902623 = 1353935) B1353935
theorem B805103 : Blo 354756 805103 := bstep (se 1 (by rfl) ⟨603827, by rfl⟩ : syracuseStep 805103 = 1207655) B1207655
theorem B674219 : Blo 354756 674219 := bstep (se 1 (by rfl) ⟨505664, by rfl⟩ : syracuseStep 674219 = 1011329) B1011329
theorem B5140907 : Blo 354756 5140907 := bstep (se 1 (by rfl) ⟨3855680, by rfl⟩ : syracuseStep 5140907 = 7711361) B7711361
theorem B356955 : Blo 354756 356955 := bstep (se 1 (by rfl) ⟨267716, by rfl⟩ : syracuseStep 356955 = 535433) B535433
theorem B357103 : Blo 354756 357103 := bstep (se 1 (by rfl) ⟨267827, by rfl⟩ : syracuseStep 357103 = 535655) B535655
theorem B1209599 : Blo 354756 1209599 := bstep (se 1 (by rfl) ⟨907199, by rfl⟩ : syracuseStep 1209599 = 1814399) B1814399
theorem B6485503 : Blo 354756 6485503 := bstep (se 1 (by rfl) ⟨4864127, by rfl⟩ : syracuseStep 6485503 = 9728255) B9728255
theorem B3438683 : Blo 354756 3438683 := bstep (se 1 (by rfl) ⟨2579012, by rfl⟩ : syracuseStep 3438683 = 5158025) B5158025
theorem B358727 : Blo 354756 358727 := bstep (se 1 (by rfl) ⟨269045, by rfl⟩ : syracuseStep 358727 = 538091) B538091
theorem B34799543 : Blo 354756 34799543 := bstep (se 1 (by rfl) ⟨26099657, by rfl⟩ : syracuseStep 34799543 = 52199315) B52199315
theorem B1016545 : Blo 354756 1016545 := bstep (se 2 (by rfl) ⟨381204, by rfl⟩ : syracuseStep 1016545 = 762409) B762409
theorem B1938761 : Blo 354756 1938761 := bstep (se 2 (by rfl) ⟨727035, by rfl⟩ : syracuseStep 1938761 = 1454071) B1454071
theorem B532223 : Blo 354756 532223 := bstep (se 1 (by rfl) ⟨399167, by rfl⟩ : syracuseStep 532223 = 798335) B798335
theorem B532967 : Blo 354756 532967 := bstep (se 1 (by rfl) ⟨399725, by rfl⟩ : syracuseStep 532967 = 799451) B799451
theorem B534695 : Blo 354756 534695 := bstep (se 1 (by rfl) ⟨401021, by rfl⟩ : syracuseStep 534695 = 802043) B802043
theorem B535487 : Blo 354756 535487 := bstep (se 1 (by rfl) ⟨401615, by rfl⟩ : syracuseStep 535487 = 803231) B803231
theorem B798857 : Blo 354756 798857 := bstep (se 2 (by rfl) ⟨299571, by rfl⟩ : syracuseStep 798857 = 599143) B599143
theorem B536735 : Blo 354756 536735 := bstep (se 1 (by rfl) ⟨402551, by rfl⟩ : syracuseStep 536735 = 805103) B805103
theorem B1755209 : Blo 354756 1755209 := bstep (se 2 (by rfl) ⟨658203, by rfl⟩ : syracuseStep 1755209 = 1316407) B1316407
theorem B3427271 : Blo 354756 3427271 := bstep (se 1 (by rfl) ⟨2570453, by rfl⟩ : syracuseStep 3427271 = 5140907) B5140907
theorem B806399 : Blo 354756 806399 := bstep (se 1 (by rfl) ⟨604799, by rfl⟩ : syracuseStep 806399 = 1209599) B1209599
theorem B4083857 : Blo 354756 4083857 := bstep (se 2 (by rfl) ⟨1531446, by rfl⟩ : syracuseStep 4083857 = 3062893) B3062893
theorem B1398815 : Blo 354756 1398815 := bstep (se 1 (by rfl) ⟨1049111, by rfl⟩ : syracuseStep 1398815 = 2098223) B2098223
theorem B449479 : Blo 354756 449479 := bstep (se 1 (by rfl) ⟨337109, by rfl⟩ : syracuseStep 449479 = 674219) B674219
theorem B1203497 : Blo 354756 1203497 := bstep (se 2 (by rfl) ⟨451311, by rfl⟩ : syracuseStep 1203497 = 902623) B902623
theorem B1797065 : Blo 354756 1797065 := bstep (se 2 (by rfl) ⟨673899, by rfl⟩ : syracuseStep 1797065 = 1347799) B1347799
theorem B4943339 : Blo 354756 4943339 := bstep (se 1 (by rfl) ⟨3707504, by rfl⟩ : syracuseStep 4943339 = 7415009) B7415009
theorem B8647337 : Blo 354756 8647337 := bstep (se 2 (by rfl) ⟨3242751, by rfl⟩ : syracuseStep 8647337 = 6485503) B6485503
theorem B357467 : Blo 354756 357467 := bstep (se 1 (by rfl) ⟨268100, by rfl⟩ : syracuseStep 357467 = 536201) B536201
theorem B358639 : Blo 354756 358639 := bstep (se 1 (by rfl) ⟨268979, by rfl⟩ : syracuseStep 358639 = 537959) B537959
theorem B2292455 : Blo 354756 2292455 := bstep (se 1 (by rfl) ⟨1719341, by rfl⟩ : syracuseStep 2292455 = 3438683) B3438683
theorem B23199695 : Blo 354756 23199695 := bstep (se 1 (by rfl) ⟨17399771, by rfl⟩ : syracuseStep 23199695 = 34799543) B34799543
theorem B2722571 : Blo 354756 2722571 := bstep (se 1 (by rfl) ⟨2041928, by rfl⟩ : syracuseStep 2722571 = 4083857) B4083857
theorem B532571 : Blo 354756 532571 := bstep (se 1 (by rfl) ⟨399428, by rfl⟩ : syracuseStep 532571 = 798857) B798857
theorem B599305 : Blo 354756 599305 := bstep (se 2 (by rfl) ⟨224739, by rfl⟩ : syracuseStep 599305 = 449479) B449479
theorem B1355393 : Blo 354756 1355393 := bstep (se 2 (by rfl) ⟨508272, by rfl⟩ : syracuseStep 1355393 = 1016545) B1016545
theorem B537599 : Blo 354756 537599 := bstep (se 1 (by rfl) ⟨403199, by rfl⟩ : syracuseStep 537599 = 806399) B806399
theorem B1292507 : Blo 354756 1292507 := bstep (se 1 (by rfl) ⟨969380, by rfl⟩ : syracuseStep 1292507 = 1938761) B1938761
theorem B932543 : Blo 354756 932543 := bstep (se 1 (by rfl) ⟨699407, by rfl⟩ : syracuseStep 932543 = 1398815) B1398815
theorem B802331 : Blo 354756 802331 := bstep (se 1 (by rfl) ⟨601748, by rfl⟩ : syracuseStep 802331 = 1203497) B1203497
theorem B1198043 : Blo 354756 1198043 := bstep (se 1 (by rfl) ⟨898532, by rfl⟩ : syracuseStep 1198043 = 1797065) B1797065
theorem B3295559 : Blo 354756 3295559 := bstep (se 1 (by rfl) ⟨2471669, by rfl⟩ : syracuseStep 3295559 = 4943339) B4943339
theorem B1528303 : Blo 354756 1528303 := bstep (se 1 (by rfl) ⟨1146227, by rfl⟩ : syracuseStep 1528303 = 2292455) B2292455
theorem B2284847 : Blo 354756 2284847 := bstep (se 1 (by rfl) ⟨1713635, by rfl⟩ : syracuseStep 2284847 = 3427271) B3427271
theorem B354815 : Blo 354756 354815 := bstep (se 1 (by rfl) ⟨266111, by rfl⟩ : syracuseStep 354815 = 532223) B532223
theorem B4680557 : Blo 354756 4680557 := bstep (se 3 (by rfl) ⟨877604, by rfl⟩ : syracuseStep 4680557 = 1755209) B1755209
theorem B355311 : Blo 354756 355311 := bstep (se 1 (by rfl) ⟨266483, by rfl⟩ : syracuseStep 355311 = 532967) B532967
theorem B356463 : Blo 354756 356463 := bstep (se 1 (by rfl) ⟨267347, by rfl⟩ : syracuseStep 356463 = 534695) B534695
theorem B356991 : Blo 354756 356991 := bstep (se 1 (by rfl) ⟨267743, by rfl⟩ : syracuseStep 356991 = 535487) B535487
theorem B357823 : Blo 354756 357823 := bstep (se 1 (by rfl) ⟨268367, by rfl⟩ : syracuseStep 357823 = 536735) B536735
theorem B5764891 : Blo 354756 5764891 := bstep (se 1 (by rfl) ⟨4323668, by rfl⟩ : syracuseStep 5764891 = 8647337) B8647337
theorem B15466463 : Blo 354756 15466463 := bstep (se 1 (by rfl) ⟨11599847, by rfl⟩ : syracuseStep 15466463 = 23199695) B23199695
theorem B2197039 : Blo 354756 2197039 := bstep (se 1 (by rfl) ⟨1647779, by rfl⟩ : syracuseStep 2197039 = 3295559) B3295559
theorem B2037737 : Blo 354756 2037737 := bstep (se 2 (by rfl) ⟨764151, by rfl⟩ : syracuseStep 2037737 = 1528303) B1528303
theorem B3120371 : Blo 354756 3120371 := bstep (se 1 (by rfl) ⟨2340278, by rfl⟩ : syracuseStep 3120371 = 4680557) B4680557
theorem B861671 : Blo 354756 861671 := bstep (se 1 (by rfl) ⟨646253, by rfl⟩ : syracuseStep 861671 = 1292507) B1292507
theorem B534887 : Blo 354756 534887 := bstep (se 1 (by rfl) ⟨401165, by rfl⟩ : syracuseStep 534887 = 802331) B802331
theorem B798695 : Blo 354756 798695 := bstep (se 1 (by rfl) ⟨599021, by rfl⟩ : syracuseStep 798695 = 1198043) B1198043
theorem B799073 : Blo 354756 799073 := bstep (se 2 (by rfl) ⟨299652, by rfl⟩ : syracuseStep 799073 = 599305) B599305
theorem B1815047 : Blo 354756 1815047 := bstep (se 1 (by rfl) ⟨1361285, by rfl⟩ : syracuseStep 1815047 = 2722571) B2722571
theorem B1523231 : Blo 354756 1523231 := bstep (se 1 (by rfl) ⟨1142423, by rfl⟩ : syracuseStep 1523231 = 2284847) B2284847
theorem B7686521 : Blo 354756 7686521 := bstep (se 2 (by rfl) ⟨2882445, by rfl⟩ : syracuseStep 7686521 = 5764891) B5764891
theorem B903595 : Blo 354756 903595 := bstep (se 1 (by rfl) ⟨677696, by rfl⟩ : syracuseStep 903595 = 1355393) B1355393
theorem B10310975 : Blo 354756 10310975 := bstep (se 1 (by rfl) ⟨7733231, by rfl⟩ : syracuseStep 10310975 = 15466463) B15466463
theorem B355047 : Blo 354756 355047 := bstep (se 1 (by rfl) ⟨266285, by rfl⟩ : syracuseStep 355047 = 532571) B532571
theorem B358399 : Blo 354756 358399 := bstep (se 1 (by rfl) ⟨268799, by rfl⟩ : syracuseStep 358399 = 537599) B537599
theorem B621695 : Blo 354756 621695 := bstep (se 1 (by rfl) ⟨466271, by rfl⟩ : syracuseStep 621695 = 932543) B932543
theorem B532463 : Blo 354756 532463 := bstep (se 1 (by rfl) ⟨399347, by rfl⟩ : syracuseStep 532463 = 798695) B798695
theorem B532715 : Blo 354756 532715 := bstep (se 1 (by rfl) ⟨399536, by rfl⟩ : syracuseStep 532715 = 799073) B799073
theorem B5124347 : Blo 354756 5124347 := bstep (se 1 (by rfl) ⟨3843260, by rfl⟩ : syracuseStep 5124347 = 7686521) B7686521
theorem B2929385 : Blo 354756 2929385 := bstep (se 2 (by rfl) ⟨1098519, by rfl⟩ : syracuseStep 2929385 = 2197039) B2197039
theorem B1358491 : Blo 354756 1358491 := bstep (se 1 (by rfl) ⟨1018868, by rfl⟩ : syracuseStep 1358491 = 2037737) B2037737
theorem B2080247 : Blo 354756 2080247 := bstep (se 1 (by rfl) ⟨1560185, by rfl⟩ : syracuseStep 2080247 = 3120371) B3120371
theorem B574447 : Blo 354756 574447 := bstep (se 1 (by rfl) ⟨430835, by rfl⟩ : syracuseStep 574447 = 861671) B861671
theorem B414463 : Blo 354756 414463 := bstep (se 1 (by rfl) ⟨310847, by rfl⟩ : syracuseStep 414463 = 621695) B621695
theorem B1204793 : Blo 354756 1204793 := bstep (se 2 (by rfl) ⟨451797, by rfl⟩ : syracuseStep 1204793 = 903595) B903595
theorem B6873983 : Blo 354756 6873983 := bstep (se 1 (by rfl) ⟨5155487, by rfl⟩ : syracuseStep 6873983 = 10310975) B10310975
theorem B356591 : Blo 354756 356591 := bstep (se 1 (by rfl) ⟨267443, by rfl⟩ : syracuseStep 356591 = 534887) B534887
theorem B1210031 : Blo 354756 1210031 := bstep (se 1 (by rfl) ⟨907523, by rfl⟩ : syracuseStep 1210031 = 1815047) B1815047
theorem B1015487 : Blo 354756 1015487 := bstep (se 1 (by rfl) ⟨761615, by rfl⟩ : syracuseStep 1015487 = 1523231) B1523231
theorem B3416231 : Blo 354756 3416231 := bstep (se 1 (by rfl) ⟨2562173, by rfl⟩ : syracuseStep 3416231 = 5124347) B5124347
theorem B1811321 : Blo 354756 1811321 := bstep (se 2 (by rfl) ⟨679245, by rfl⟩ : syracuseStep 1811321 = 1358491) B1358491
theorem B5547325 : Blo 354756 5547325 := bstep (se 3 (by rfl) ⟨1040123, by rfl⟩ : syracuseStep 5547325 = 2080247) B2080247
theorem B765929 : Blo 354756 765929 := bstep (se 2 (by rfl) ⟨287223, by rfl⟩ : syracuseStep 765929 = 574447) B574447
theorem B803195 : Blo 354756 803195 := bstep (se 1 (by rfl) ⟨602396, by rfl⟩ : syracuseStep 803195 = 1204793) B1204793
theorem B1952923 : Blo 354756 1952923 := bstep (se 1 (by rfl) ⟨1464692, by rfl⟩ : syracuseStep 1952923 = 2929385) B2929385
theorem B806687 : Blo 354756 806687 := bstep (se 1 (by rfl) ⟨605015, by rfl⟩ : syracuseStep 806687 = 1210031) B1210031
theorem B676991 : Blo 354756 676991 := bstep (se 1 (by rfl) ⟨507743, by rfl⟩ : syracuseStep 676991 = 1015487) B1015487
theorem B354975 : Blo 354756 354975 := bstep (se 1 (by rfl) ⟨266231, by rfl⟩ : syracuseStep 354975 = 532463) B532463
theorem B355143 : Blo 354756 355143 := bstep (se 1 (by rfl) ⟨266357, by rfl⟩ : syracuseStep 355143 = 532715) B532715
theorem B4582655 : Blo 354756 4582655 := bstep (se 1 (by rfl) ⟨3436991, by rfl⟩ : syracuseStep 4582655 = 6873983) B6873983
theorem B552617 : Blo 354756 552617 := bstep (se 2 (by rfl) ⟨207231, by rfl⟩ : syracuseStep 552617 = 414463) B414463
theorem B3055103 : Blo 354756 3055103 := bstep (se 1 (by rfl) ⟨2291327, by rfl⟩ : syracuseStep 3055103 = 4582655) B4582655
theorem B368411 : Blo 354756 368411 := bstep (se 1 (by rfl) ⟨276308, by rfl⟩ : syracuseStep 368411 = 552617) B552617
theorem B535463 : Blo 354756 535463 := bstep (se 1 (by rfl) ⟨401597, by rfl⟩ : syracuseStep 535463 = 803195) B803195
theorem B537791 : Blo 354756 537791 := bstep (se 1 (by rfl) ⟨403343, by rfl⟩ : syracuseStep 537791 = 806687) B806687
theorem B2603897 : Blo 354756 2603897 := bstep (se 2 (by rfl) ⟨976461, by rfl⟩ : syracuseStep 2603897 = 1952923) B1952923
theorem B2277487 : Blo 354756 2277487 := bstep (se 1 (by rfl) ⟨1708115, by rfl⟩ : syracuseStep 2277487 = 3416231) B3416231
theorem B510619 : Blo 354756 510619 := bstep (se 1 (by rfl) ⟨382964, by rfl⟩ : syracuseStep 510619 = 765929) B765929
theorem B7396433 : Blo 354756 7396433 := bstep (se 2 (by rfl) ⟨2773662, by rfl⟩ : syracuseStep 7396433 = 5547325) B5547325
theorem B451327 : Blo 354756 451327 := bstep (se 1 (by rfl) ⟨338495, by rfl⟩ : syracuseStep 451327 = 676991) B676991
theorem B1207547 : Blo 354756 1207547 := bstep (se 1 (by rfl) ⟨905660, by rfl⟩ : syracuseStep 1207547 = 1811321) B1811321
theorem B2036735 : Blo 354756 2036735 := bstep (se 1 (by rfl) ⟨1527551, by rfl⟩ : syracuseStep 2036735 = 3055103) B3055103
theorem B601769 : Blo 354756 601769 := bstep (se 2 (by rfl) ⟨225663, by rfl⟩ : syracuseStep 601769 = 451327) B451327
theorem B4930955 : Blo 354756 4930955 := bstep (se 1 (by rfl) ⟨3698216, by rfl⟩ : syracuseStep 4930955 = 7396433) B7396433
theorem B805031 : Blo 354756 805031 := bstep (se 1 (by rfl) ⟨603773, by rfl⟩ : syracuseStep 805031 = 1207547) B1207547
theorem B3036649 : Blo 354756 3036649 := bstep (se 2 (by rfl) ⟨1138743, by rfl⟩ : syracuseStep 3036649 = 2277487) B2277487
theorem B680825 : Blo 354756 680825 := bstep (se 2 (by rfl) ⟨255309, by rfl⟩ : syracuseStep 680825 = 510619) B510619
theorem B356975 : Blo 354756 356975 := bstep (se 1 (by rfl) ⟨267731, by rfl⟩ : syracuseStep 356975 = 535463) B535463
theorem B3929717 : Blo 354756 3929717 := bstep (se 5 (by rfl) ⟨184205, by rfl⟩ : syracuseStep 3929717 = 368411) B368411
theorem B358527 : Blo 354756 358527 := bstep (se 1 (by rfl) ⟨268895, by rfl⟩ : syracuseStep 358527 = 537791) B537791
theorem B1735931 : Blo 354756 1735931 := bstep (se 1 (by rfl) ⟨1301948, by rfl⟩ : syracuseStep 1735931 = 2603897) B2603897
theorem B401179 : Blo 354756 401179 := bstep (se 1 (by rfl) ⟨300884, by rfl⟩ : syracuseStep 401179 = 601769) B601769
theorem B4629149 : Blo 354756 4629149 := bstep (se 3 (by rfl) ⟨867965, by rfl⟩ : syracuseStep 4629149 = 1735931) B1735931
theorem B3287303 : Blo 354756 3287303 := bstep (se 1 (by rfl) ⟨2465477, by rfl⟩ : syracuseStep 3287303 = 4930955) B4930955
theorem B536687 : Blo 354756 536687 := bstep (se 1 (by rfl) ⟨402515, by rfl⟩ : syracuseStep 536687 = 805031) B805031
theorem B1815533 : Blo 354756 1815533 := bstep (se 3 (by rfl) ⟨340412, by rfl⟩ : syracuseStep 1815533 = 680825) B680825
theorem B1357823 : Blo 354756 1357823 := bstep (se 1 (by rfl) ⟨1018367, by rfl⟩ : syracuseStep 1357823 = 2036735) B2036735
theorem B4048865 : Blo 354756 4048865 := bstep (se 2 (by rfl) ⟨1518324, by rfl⟩ : syracuseStep 4048865 = 3036649) B3036649
theorem B2619811 : Blo 354756 2619811 := bstep (se 1 (by rfl) ⟨1964858, by rfl⟩ : syracuseStep 2619811 = 3929717) B3929717
theorem B3086099 : Blo 354756 3086099 := bstep (se 1 (by rfl) ⟨2314574, by rfl⟩ : syracuseStep 3086099 = 4629149) B4629149
theorem B534905 : Blo 354756 534905 := bstep (se 2 (by rfl) ⟨200589, by rfl⟩ : syracuseStep 534905 = 401179) B401179
theorem B2699243 : Blo 354756 2699243 := bstep (se 1 (by rfl) ⟨2024432, by rfl⟩ : syracuseStep 2699243 = 4048865) B4048865
theorem B3493081 : Blo 354756 3493081 := bstep (se 2 (by rfl) ⟨1309905, by rfl⟩ : syracuseStep 3493081 = 2619811) B2619811
theorem B905215 : Blo 354756 905215 := bstep (se 1 (by rfl) ⟨678911, by rfl⟩ : syracuseStep 905215 = 1357823) B1357823
theorem B2191535 : Blo 354756 2191535 := bstep (se 1 (by rfl) ⟨1643651, by rfl⟩ : syracuseStep 2191535 = 3287303) B3287303
theorem B357791 : Blo 354756 357791 := bstep (se 1 (by rfl) ⟨268343, by rfl⟩ : syracuseStep 357791 = 536687) B536687
theorem B1210355 : Blo 354756 1210355 := bstep (se 1 (by rfl) ⟨907766, by rfl⟩ : syracuseStep 1210355 = 1815533) B1815533
theorem B4657441 : Blo 354756 4657441 := bstep (se 2 (by rfl) ⟨1746540, by rfl⟩ : syracuseStep 4657441 = 3493081) B3493081
theorem B1461023 : Blo 354756 1461023 := bstep (se 1 (by rfl) ⟨1095767, by rfl⟩ : syracuseStep 1461023 = 2191535) B2191535
theorem B806903 : Blo 354756 806903 := bstep (se 1 (by rfl) ⟨605177, by rfl⟩ : syracuseStep 806903 = 1210355) B1210355
theorem B2057399 : Blo 354756 2057399 := bstep (se 1 (by rfl) ⟨1543049, by rfl⟩ : syracuseStep 2057399 = 3086099) B3086099
theorem B1206953 : Blo 354756 1206953 := bstep (se 2 (by rfl) ⟨452607, by rfl⟩ : syracuseStep 1206953 = 905215) B905215
theorem B356603 : Blo 354756 356603 := bstep (se 1 (by rfl) ⟨267452, by rfl⟩ : syracuseStep 356603 = 534905) B534905
theorem B1799495 : Blo 354756 1799495 := bstep (se 1 (by rfl) ⟨1349621, by rfl⟩ : syracuseStep 1799495 = 2699243) B2699243
theorem B537935 : Blo 354756 537935 := bstep (se 1 (by rfl) ⟨403451, by rfl⟩ : syracuseStep 537935 = 806903) B806903
theorem B6209921 : Blo 354756 6209921 := bstep (se 2 (by rfl) ⟨2328720, by rfl⟩ : syracuseStep 6209921 = 4657441) B4657441
theorem B804635 : Blo 354756 804635 := bstep (se 1 (by rfl) ⟨603476, by rfl⟩ : syracuseStep 804635 = 1206953) B1206953
theorem B1199663 : Blo 354756 1199663 := bstep (se 1 (by rfl) ⟨899747, by rfl⟩ : syracuseStep 1199663 = 1799495) B1799495
theorem B974015 : Blo 354756 974015 := bstep (se 1 (by rfl) ⟨730511, by rfl⟩ : syracuseStep 974015 = 1461023) B1461023
theorem B1371599 : Blo 354756 1371599 := bstep (se 1 (by rfl) ⟨1028699, by rfl⟩ : syracuseStep 1371599 = 2057399) B2057399
theorem B4139947 : Blo 354756 4139947 := bstep (se 1 (by rfl) ⟨3104960, by rfl⟩ : syracuseStep 4139947 = 6209921) B6209921
theorem B536423 : Blo 354756 536423 := bstep (se 1 (by rfl) ⟨402317, by rfl⟩ : syracuseStep 536423 = 804635) B804635
theorem B799775 : Blo 354756 799775 := bstep (se 1 (by rfl) ⟨599831, by rfl⟩ : syracuseStep 799775 = 1199663) B1199663
theorem B649343 : Blo 354756 649343 := bstep (se 1 (by rfl) ⟨487007, by rfl⟩ : syracuseStep 649343 = 974015) B974015
theorem B914399 : Blo 354756 914399 := bstep (se 1 (by rfl) ⟨685799, by rfl⟩ : syracuseStep 914399 = 1371599) B1371599
theorem B358623 : Blo 354756 358623 := bstep (se 1 (by rfl) ⟨268967, by rfl⟩ : syracuseStep 358623 = 537935) B537935
theorem B533183 : Blo 354756 533183 := bstep (se 1 (by rfl) ⟨399887, by rfl⟩ : syracuseStep 533183 = 799775) B799775
theorem B5519929 : Blo 354756 5519929 := bstep (se 2 (by rfl) ⟨2069973, by rfl⟩ : syracuseStep 5519929 = 4139947) B4139947
theorem B609599 : Blo 354756 609599 := bstep (se 1 (by rfl) ⟨457199, by rfl⟩ : syracuseStep 609599 = 914399) B914399
theorem B1731581 : Blo 354756 1731581 := bstep (se 3 (by rfl) ⟨324671, by rfl⟩ : syracuseStep 1731581 = 649343) B649343
theorem B357615 : Blo 354756 357615 := bstep (se 1 (by rfl) ⟨268211, by rfl⟩ : syracuseStep 357615 = 536423) B536423
theorem B1154387 : Blo 354756 1154387 := bstep (se 1 (by rfl) ⟨865790, by rfl⟩ : syracuseStep 1154387 = 1731581) B1731581
theorem B406399 : Blo 354756 406399 := bstep (se 1 (by rfl) ⟨304799, by rfl⟩ : syracuseStep 406399 = 609599) B609599
theorem B7359905 : Blo 354756 7359905 := bstep (se 2 (by rfl) ⟨2759964, by rfl⟩ : syracuseStep 7359905 = 5519929) B5519929
theorem B355455 : Blo 354756 355455 := bstep (se 1 (by rfl) ⟨266591, by rfl⟩ : syracuseStep 355455 = 533183) B533183
theorem B769591 : Blo 354756 769591 := bstep (se 1 (by rfl) ⟨577193, by rfl⟩ : syracuseStep 769591 = 1154387) B1154387
theorem B541865 : Blo 354756 541865 := bstep (se 2 (by rfl) ⟨203199, by rfl⟩ : syracuseStep 541865 = 406399) B406399
theorem B4906603 : Blo 354756 4906603 := bstep (se 1 (by rfl) ⟨3679952, by rfl⟩ : syracuseStep 4906603 = 7359905) B7359905
theorem B361243 : Blo 354756 361243 := bstep (se 1 (by rfl) ⟨270932, by rfl⟩ : syracuseStep 361243 = 541865) B541865
theorem B1026121 : Blo 354756 1026121 := bstep (se 2 (by rfl) ⟨384795, by rfl⟩ : syracuseStep 1026121 = 769591) B769591
theorem B6542137 : Blo 354756 6542137 := bstep (se 2 (by rfl) ⟨2453301, by rfl⟩ : syracuseStep 6542137 = 4906603) B4906603
theorem B1368161 : Blo 354756 1368161 := bstep (se 2 (by rfl) ⟨513060, by rfl⟩ : syracuseStep 1368161 = 1026121) B1026121
theorem B1926629 : Blo 354756 1926629 := bstep (se 4 (by rfl) ⟨180621, by rfl⟩ : syracuseStep 1926629 = 361243) B361243
theorem B34891397 : Blo 354756 34891397 := bstep (se 4 (by rfl) ⟨3271068, by rfl⟩ : syracuseStep 34891397 = 6542137) B6542137
theorem B1284419 : Blo 354756 1284419 := bstep (se 1 (by rfl) ⟨963314, by rfl⟩ : syracuseStep 1284419 = 1926629) B1926629
theorem B912107 : Blo 354756 912107 := bstep (se 1 (by rfl) ⟨684080, by rfl⟩ : syracuseStep 912107 = 1368161) B1368161
theorem B23260931 : Blo 354756 23260931 := bstep (se 1 (by rfl) ⟨17445698, by rfl⟩ : syracuseStep 23260931 = 34891397) B34891397
theorem B856279 : Blo 354756 856279 := bstep (se 1 (by rfl) ⟨642209, by rfl⟩ : syracuseStep 856279 = 1284419) B1284419
theorem B15507287 : Blo 354756 15507287 := bstep (se 1 (by rfl) ⟨11630465, by rfl⟩ : syracuseStep 15507287 = 23260931) B23260931
theorem B608071 : Blo 354756 608071 := bstep (se 1 (by rfl) ⟨456053, by rfl⟩ : syracuseStep 608071 = 912107) B912107
theorem B10338191 : Blo 354756 10338191 := bstep (se 1 (by rfl) ⟨7753643, by rfl⟩ : syracuseStep 10338191 = 15507287) B15507287
theorem B810761 : Blo 354756 810761 := bstep (se 2 (by rfl) ⟨304035, by rfl⟩ : syracuseStep 810761 = 608071) B608071
theorem B1141705 : Blo 354756 1141705 := bstep (se 2 (by rfl) ⟨428139, by rfl⟩ : syracuseStep 1141705 = 856279) B856279
theorem B6892127 : Blo 354756 6892127 := bstep (se 1 (by rfl) ⟨5169095, by rfl⟩ : syracuseStep 6892127 = 10338191) B10338191
theorem B1522273 : Blo 354756 1522273 := bstep (se 2 (by rfl) ⟨570852, by rfl⟩ : syracuseStep 1522273 = 1141705) B1141705
theorem B8648117 : Blo 354756 8648117 := bstep (se 5 (by rfl) ⟨405380, by rfl⟩ : syracuseStep 8648117 = 810761) B810761
theorem B4594751 : Blo 354756 4594751 := bstep (se 1 (by rfl) ⟨3446063, by rfl⟩ : syracuseStep 4594751 = 6892127) B6892127
theorem B2029697 : Blo 354756 2029697 := bstep (se 2 (by rfl) ⟨761136, by rfl⟩ : syracuseStep 2029697 = 1522273) B1522273
theorem B5765411 : Blo 354756 5765411 := bstep (se 1 (by rfl) ⟨4324058, by rfl⟩ : syracuseStep 5765411 = 8648117) B8648117
theorem B1353131 : Blo 354756 1353131 := bstep (se 1 (by rfl) ⟨1014848, by rfl⟩ : syracuseStep 1353131 = 2029697) B2029697
theorem B3843607 : Blo 354756 3843607 := bstep (se 1 (by rfl) ⟨2882705, by rfl⟩ : syracuseStep 3843607 = 5765411) B5765411
theorem B3063167 : Blo 354756 3063167 := bstep (se 1 (by rfl) ⟨2297375, by rfl⟩ : syracuseStep 3063167 = 4594751) B4594751
theorem B2042111 : Blo 354756 2042111 := bstep (se 1 (by rfl) ⟨1531583, by rfl⟩ : syracuseStep 2042111 = 3063167) B3063167
theorem B5124809 : Blo 354756 5124809 := bstep (se 2 (by rfl) ⟨1921803, by rfl⟩ : syracuseStep 5124809 = 3843607) B3843607
theorem B902087 : Blo 354756 902087 := bstep (se 1 (by rfl) ⟨676565, by rfl⟩ : syracuseStep 902087 = 1353131) B1353131
theorem B3416539 : Blo 354756 3416539 := bstep (se 1 (by rfl) ⟨2562404, by rfl⟩ : syracuseStep 3416539 = 5124809) B5124809
theorem B601391 : Blo 354756 601391 := bstep (se 1 (by rfl) ⟨451043, by rfl⟩ : syracuseStep 601391 = 902087) B902087
theorem B1361407 : Blo 354756 1361407 := bstep (se 1 (by rfl) ⟨1021055, by rfl⟩ : syracuseStep 1361407 = 2042111) B2042111
theorem B4555385 : Blo 354756 4555385 := bstep (se 2 (by rfl) ⟨1708269, by rfl⟩ : syracuseStep 4555385 = 3416539) B3416539
theorem B400927 : Blo 354756 400927 := bstep (se 1 (by rfl) ⟨300695, by rfl⟩ : syracuseStep 400927 = 601391) B601391
theorem B1815209 : Blo 354756 1815209 := bstep (se 2 (by rfl) ⟨680703, by rfl⟩ : syracuseStep 1815209 = 1361407) B1361407
theorem B534569 : Blo 354756 534569 := bstep (se 2 (by rfl) ⟨200463, by rfl⟩ : syracuseStep 534569 = 400927) B400927
theorem B3036923 : Blo 354756 3036923 := bstep (se 1 (by rfl) ⟨2277692, by rfl⟩ : syracuseStep 3036923 = 4555385) B4555385
theorem B1210139 : Blo 354756 1210139 := bstep (se 1 (by rfl) ⟨907604, by rfl⟩ : syracuseStep 1210139 = 1815209) B1815209
theorem B806759 : Blo 354756 806759 := bstep (se 1 (by rfl) ⟨605069, by rfl⟩ : syracuseStep 806759 = 1210139) B1210139
theorem B2024615 : Blo 354756 2024615 := bstep (se 1 (by rfl) ⟨1518461, by rfl⟩ : syracuseStep 2024615 = 3036923) B3036923
theorem B356379 : Blo 354756 356379 := bstep (se 1 (by rfl) ⟨267284, by rfl⟩ : syracuseStep 356379 = 534569) B534569
theorem B1349743 : Blo 354756 1349743 := bstep (se 1 (by rfl) ⟨1012307, by rfl⟩ : syracuseStep 1349743 = 2024615) B2024615
theorem B537839 : Blo 354756 537839 := bstep (se 1 (by rfl) ⟨403379, by rfl⟩ : syracuseStep 537839 = 806759) B806759
theorem B1799657 : Blo 354756 1799657 := bstep (se 2 (by rfl) ⟨674871, by rfl⟩ : syracuseStep 1799657 = 1349743) B1349743
theorem B358559 : Blo 354756 358559 := bstep (se 1 (by rfl) ⟨268919, by rfl⟩ : syracuseStep 358559 = 537839) B537839
theorem B1199771 : Blo 354756 1199771 := bstep (se 1 (by rfl) ⟨899828, by rfl⟩ : syracuseStep 1199771 = 1799657) B1799657
theorem B799847 : Blo 354756 799847 := bstep (se 1 (by rfl) ⟨599885, by rfl⟩ : syracuseStep 799847 = 1199771) B1199771
theorem B533231 : Blo 354756 533231 := bstep (se 1 (by rfl) ⟨399923, by rfl⟩ : syracuseStep 533231 = 799847) B799847
theorem B355487 : Blo 354756 355487 := bstep (se 1 (by rfl) ⟨266615, by rfl⟩ : syracuseStep 355487 = 533231) B533231

theorem C0 (j : ℕ) (h1 : 88689 ≤ j) (h2 : j ≤ 89388) : Blo 354756 (4 * j + 3) := by
  interval_cases j
  · exact B354759
  · exact B354763
  · exact B354767
  · exact B354771
  · exact B354775
  · exact B354779
  · exact B354783
  · exact B354787
  · exact B354791
  · exact B354795
  · exact B354799
  · exact B354803
  · exact B354807
  · exact B354811
  · exact B354815
  · exact B354819
  · exact B354823
  · exact B354827
  · exact B354831
  · exact B354835
  · exact B354839
  · exact B354843
  · exact B354847
  · exact B354851
  · exact B354855
  · exact B354859
  · exact B354863
  · exact B354867
  · exact B354871
  · exact B354875
  · exact B354879
  · exact B354883
  · exact B354887
  · exact B354891
  · exact B354895
  · exact B354899
  · exact B354903
  · exact B354907
  · exact B354911
  · exact B354915
  · exact B354919
  · exact B354923
  · exact B354927
  · exact B354931
  · exact B354935
  · exact B354939
  · exact B354943
  · exact B354947
  · exact B354951
  · exact B354955
  · exact B354959
  · exact B354963
  · exact B354967
  · exact B354971
  · exact B354975
  · exact B354979
  · exact B354983
  · exact B354987
  · exact B354991
  · exact B354995
  · exact B354999
  · exact B355003
  · exact B355007
  · exact B355011
  · exact B355015
  · exact B355019
  · exact B355023
  · exact B355027
  · exact B355031
  · exact B355035
  · exact B355039
  · exact B355043
  · exact B355047
  · exact B355051
  · exact B355055
  · exact B355059
  · exact B355063
  · exact B355067
  · exact B355071
  · exact B355075
  · exact B355079
  · exact B355083
  · exact B355087
  · exact B355091
  · exact B355095
  · exact B355099
  · exact B355103
  · exact B355107
  · exact B355111
  · exact B355115
  · exact B355119
  · exact B355123
  · exact B355127
  · exact B355131
  · exact B355135
  · exact B355139
  · exact B355143
  · exact B355147
  · exact B355151
  · exact B355155
  · exact B355159
  · exact B355163
  · exact B355167
  · exact B355171
  · exact B355175
  · exact B355179
  · exact B355183
  · exact B355187
  · exact B355191
  · exact B355195
  · exact B355199
  · exact B355203
  · exact B355207
  · exact B355211
  · exact B355215
  · exact B355219
  · exact B355223
  · exact B355227
  · exact B355231
  · exact B355235
  · exact B355239
  · exact B355243
  · exact B355247
  · exact B355251
  · exact B355255
  · exact B355259
  · exact B355263
  · exact B355267
  · exact B355271
  · exact B355275
  · exact B355279
  · exact B355283
  · exact B355287
  · exact B355291
  · exact B355295
  · exact B355299
  · exact B355303
  · exact B355307
  · exact B355311
  · exact B355315
  · exact B355319
  · exact B355323
  · exact B355327
  · exact B355331
  · exact B355335
  · exact B355339
  · exact B355343
  · exact B355347
  · exact B355351
  · exact B355355
  · exact B355359
  · exact B355363
  · exact B355367
  · exact B355371
  · exact B355375
  · exact B355379
  · exact B355383
  · exact B355387
  · exact B355391
  · exact B355395
  · exact B355399
  · exact B355403
  · exact B355407
  · exact B355411
  · exact B355415
  · exact B355419
  · exact B355423
  · exact B355427
  · exact B355431
  · exact B355435
  · exact B355439
  · exact B355443
  · exact B355447
  · exact B355451
  · exact B355455
  · exact B355459
  · exact B355463
  · exact B355467
  · exact B355471
  · exact B355475
  · exact B355479
  · exact B355483
  · exact B355487
  · exact B355491
  · exact B355495
  · exact B355499
  · exact B355503
  · exact B355507
  · exact B355511
  · exact B355515
  · exact B355519
  · exact B355523
  · exact B355527
  · exact B355531
  · exact B355535
  · exact B355539
  · exact B355543
  · exact B355547
  · exact B355551
  · exact B355555
  · exact B355559
  · exact B355563
  · exact B355567
  · exact B355571
  · exact B355575
  · exact B355579
  · exact B355583
  · exact B355587
  · exact B355591
  · exact B355595
  · exact B355599
  · exact B355603
  · exact B355607
  · exact B355611
  · exact B355615
  · exact B355619
  · exact B355623
  · exact B355627
  · exact B355631
  · exact B355635
  · exact B355639
  · exact B355643
  · exact B355647
  · exact B355651
  · exact B355655
  · exact B355659
  · exact B355663
  · exact B355667
  · exact B355671
  · exact B355675
  · exact B355679
  · exact B355683
  · exact B355687
  · exact B355691
  · exact B355695
  · exact B355699
  · exact B355703
  · exact B355707
  · exact B355711
  · exact B355715
  · exact B355719
  · exact B355723
  · exact B355727
  · exact B355731
  · exact B355735
  · exact B355739
  · exact B355743
  · exact B355747
  · exact B355751
  · exact B355755
  · exact B355759
  · exact B355763
  · exact B355767
  · exact B355771
  · exact B355775
  · exact B355779
  · exact B355783
  · exact B355787
  · exact B355791
  · exact B355795
  · exact B355799
  · exact B355803
  · exact B355807
  · exact B355811
  · exact B355815
  · exact B355819
  · exact B355823
  · exact B355827
  · exact B355831
  · exact B355835
  · exact B355839
  · exact B355843
  · exact B355847
  · exact B355851
  · exact B355855
  · exact B355859
  · exact B355863
  · exact B355867
  · exact B355871
  · exact B355875
  · exact B355879
  · exact B355883
  · exact B355887
  · exact B355891
  · exact B355895
  · exact B355899
  · exact B355903
  · exact B355907
  · exact B355911
  · exact B355915
  · exact B355919
  · exact B355923
  · exact B355927
  · exact B355931
  · exact B355935
  · exact B355939
  · exact B355943
  · exact B355947
  · exact B355951
  · exact B355955
  · exact B355959
  · exact B355963
  · exact B355967
  · exact B355971
  · exact B355975
  · exact B355979
  · exact B355983
  · exact B355987
  · exact B355991
  · exact B355995
  · exact B355999
  · exact B356003
  · exact B356007
  · exact B356011
  · exact B356015
  · exact B356019
  · exact B356023
  · exact B356027
  · exact B356031
  · exact B356035
  · exact B356039
  · exact B356043
  · exact B356047
  · exact B356051
  · exact B356055
  · exact B356059
  · exact B356063
  · exact B356067
  · exact B356071
  · exact B356075
  · exact B356079
  · exact B356083
  · exact B356087
  · exact B356091
  · exact B356095
  · exact B356099
  · exact B356103
  · exact B356107
  · exact B356111
  · exact B356115
  · exact B356119
  · exact B356123
  · exact B356127
  · exact B356131
  · exact B356135
  · exact B356139
  · exact B356143
  · exact B356147
  · exact B356151
  · exact B356155
  · exact B356159
  · exact B356163
  · exact B356167
  · exact B356171
  · exact B356175
  · exact B356179
  · exact B356183
  · exact B356187
  · exact B356191
  · exact B356195
  · exact B356199
  · exact B356203
  · exact B356207
  · exact B356211
  · exact B356215
  · exact B356219
  · exact B356223
  · exact B356227
  · exact B356231
  · exact B356235
  · exact B356239
  · exact B356243
  · exact B356247
  · exact B356251
  · exact B356255
  · exact B356259
  · exact B356263
  · exact B356267
  · exact B356271
  · exact B356275
  · exact B356279
  · exact B356283
  · exact B356287
  · exact B356291
  · exact B356295
  · exact B356299
  · exact B356303
  · exact B356307
  · exact B356311
  · exact B356315
  · exact B356319
  · exact B356323
  · exact B356327
  · exact B356331
  · exact B356335
  · exact B356339
  · exact B356343
  · exact B356347
  · exact B356351
  · exact B356355
  · exact B356359
  · exact B356363
  · exact B356367
  · exact B356371
  · exact B356375
  · exact B356379
  · exact B356383
  · exact B356387
  · exact B356391
  · exact B356395
  · exact B356399
  · exact B356403
  · exact B356407
  · exact B356411
  · exact B356415
  · exact B356419
  · exact B356423
  · exact B356427
  · exact B356431
  · exact B356435
  · exact B356439
  · exact B356443
  · exact B356447
  · exact B356451
  · exact B356455
  · exact B356459
  · exact B356463
  · exact B356467
  · exact B356471
  · exact B356475
  · exact B356479
  · exact B356483
  · exact B356487
  · exact B356491
  · exact B356495
  · exact B356499
  · exact B356503
  · exact B356507
  · exact B356511
  · exact B356515
  · exact B356519
  · exact B356523
  · exact B356527
  · exact B356531
  · exact B356535
  · exact B356539
  · exact B356543
  · exact B356547
  · exact B356551
  · exact B356555
  · exact B356559
  · exact B356563
  · exact B356567
  · exact B356571
  · exact B356575
  · exact B356579
  · exact B356583
  · exact B356587
  · exact B356591
  · exact B356595
  · exact B356599
  · exact B356603
  · exact B356607
  · exact B356611
  · exact B356615
  · exact B356619
  · exact B356623
  · exact B356627
  · exact B356631
  · exact B356635
  · exact B356639
  · exact B356643
  · exact B356647
  · exact B356651
  · exact B356655
  · exact B356659
  · exact B356663
  · exact B356667
  · exact B356671
  · exact B356675
  · exact B356679
  · exact B356683
  · exact B356687
  · exact B356691
  · exact B356695
  · exact B356699
  · exact B356703
  · exact B356707
  · exact B356711
  · exact B356715
  · exact B356719
  · exact B356723
  · exact B356727
  · exact B356731
  · exact B356735
  · exact B356739
  · exact B356743
  · exact B356747
  · exact B356751
  · exact B356755
  · exact B356759
  · exact B356763
  · exact B356767
  · exact B356771
  · exact B356775
  · exact B356779
  · exact B356783
  · exact B356787
  · exact B356791
  · exact B356795
  · exact B356799
  · exact B356803
  · exact B356807
  · exact B356811
  · exact B356815
  · exact B356819
  · exact B356823
  · exact B356827
  · exact B356831
  · exact B356835
  · exact B356839
  · exact B356843
  · exact B356847
  · exact B356851
  · exact B356855
  · exact B356859
  · exact B356863
  · exact B356867
  · exact B356871
  · exact B356875
  · exact B356879
  · exact B356883
  · exact B356887
  · exact B356891
  · exact B356895
  · exact B356899
  · exact B356903
  · exact B356907
  · exact B356911
  · exact B356915
  · exact B356919
  · exact B356923
  · exact B356927
  · exact B356931
  · exact B356935
  · exact B356939
  · exact B356943
  · exact B356947
  · exact B356951
  · exact B356955
  · exact B356959
  · exact B356963
  · exact B356967
  · exact B356971
  · exact B356975
  · exact B356979
  · exact B356983
  · exact B356987
  · exact B356991
  · exact B356995
  · exact B356999
  · exact B357003
  · exact B357007
  · exact B357011
  · exact B357015
  · exact B357019
  · exact B357023
  · exact B357027
  · exact B357031
  · exact B357035
  · exact B357039
  · exact B357043
  · exact B357047
  · exact B357051
  · exact B357055
  · exact B357059
  · exact B357063
  · exact B357067
  · exact B357071
  · exact B357075
  · exact B357079
  · exact B357083
  · exact B357087
  · exact B357091
  · exact B357095
  · exact B357099
  · exact B357103
  · exact B357107
  · exact B357111
  · exact B357115
  · exact B357119
  · exact B357123
  · exact B357127
  · exact B357131
  · exact B357135
  · exact B357139
  · exact B357143
  · exact B357147
  · exact B357151
  · exact B357155
  · exact B357159
  · exact B357163
  · exact B357167
  · exact B357171
  · exact B357175
  · exact B357179
  · exact B357183
  · exact B357187
  · exact B357191
  · exact B357195
  · exact B357199
  · exact B357203
  · exact B357207
  · exact B357211
  · exact B357215
  · exact B357219
  · exact B357223
  · exact B357227
  · exact B357231
  · exact B357235
  · exact B357239
  · exact B357243
  · exact B357247
  · exact B357251
  · exact B357255
  · exact B357259
  · exact B357263
  · exact B357267
  · exact B357271
  · exact B357275
  · exact B357279
  · exact B357283
  · exact B357287
  · exact B357291
  · exact B357295
  · exact B357299
  · exact B357303
  · exact B357307
  · exact B357311
  · exact B357315
  · exact B357319
  · exact B357323
  · exact B357327
  · exact B357331
  · exact B357335
  · exact B357339
  · exact B357343
  · exact B357347
  · exact B357351
  · exact B357355
  · exact B357359
  · exact B357363
  · exact B357367
  · exact B357371
  · exact B357375
  · exact B357379
  · exact B357383
  · exact B357387
  · exact B357391
  · exact B357395
  · exact B357399
  · exact B357403
  · exact B357407
  · exact B357411
  · exact B357415
  · exact B357419
  · exact B357423
  · exact B357427
  · exact B357431
  · exact B357435
  · exact B357439
  · exact B357443
  · exact B357447
  · exact B357451
  · exact B357455
  · exact B357459
  · exact B357463
  · exact B357467
  · exact B357471
  · exact B357475
  · exact B357479
  · exact B357483
  · exact B357487
  · exact B357491
  · exact B357495
  · exact B357499
  · exact B357503
  · exact B357507
  · exact B357511
  · exact B357515
  · exact B357519
  · exact B357523
  · exact B357527
  · exact B357531
  · exact B357535
  · exact B357539
  · exact B357543
  · exact B357547
  · exact B357551
  · exact B357555

theorem C1 (j : ℕ) (h1 : 89389 ≤ j) (h2 : j ≤ 89688) : Blo 354756 (4 * j + 3) := by
  interval_cases j
  · exact B357559
  · exact B357563
  · exact B357567
  · exact B357571
  · exact B357575
  · exact B357579
  · exact B357583
  · exact B357587
  · exact B357591
  · exact B357595
  · exact B357599
  · exact B357603
  · exact B357607
  · exact B357611
  · exact B357615
  · exact B357619
  · exact B357623
  · exact B357627
  · exact B357631
  · exact B357635
  · exact B357639
  · exact B357643
  · exact B357647
  · exact B357651
  · exact B357655
  · exact B357659
  · exact B357663
  · exact B357667
  · exact B357671
  · exact B357675
  · exact B357679
  · exact B357683
  · exact B357687
  · exact B357691
  · exact B357695
  · exact B357699
  · exact B357703
  · exact B357707
  · exact B357711
  · exact B357715
  · exact B357719
  · exact B357723
  · exact B357727
  · exact B357731
  · exact B357735
  · exact B357739
  · exact B357743
  · exact B357747
  · exact B357751
  · exact B357755
  · exact B357759
  · exact B357763
  · exact B357767
  · exact B357771
  · exact B357775
  · exact B357779
  · exact B357783
  · exact B357787
  · exact B357791
  · exact B357795
  · exact B357799
  · exact B357803
  · exact B357807
  · exact B357811
  · exact B357815
  · exact B357819
  · exact B357823
  · exact B357827
  · exact B357831
  · exact B357835
  · exact B357839
  · exact B357843
  · exact B357847
  · exact B357851
  · exact B357855
  · exact B357859
  · exact B357863
  · exact B357867
  · exact B357871
  · exact B357875
  · exact B357879
  · exact B357883
  · exact B357887
  · exact B357891
  · exact B357895
  · exact B357899
  · exact B357903
  · exact B357907
  · exact B357911
  · exact B357915
  · exact B357919
  · exact B357923
  · exact B357927
  · exact B357931
  · exact B357935
  · exact B357939
  · exact B357943
  · exact B357947
  · exact B357951
  · exact B357955
  · exact B357959
  · exact B357963
  · exact B357967
  · exact B357971
  · exact B357975
  · exact B357979
  · exact B357983
  · exact B357987
  · exact B357991
  · exact B357995
  · exact B357999
  · exact B358003
  · exact B358007
  · exact B358011
  · exact B358015
  · exact B358019
  · exact B358023
  · exact B358027
  · exact B358031
  · exact B358035
  · exact B358039
  · exact B358043
  · exact B358047
  · exact B358051
  · exact B358055
  · exact B358059
  · exact B358063
  · exact B358067
  · exact B358071
  · exact B358075
  · exact B358079
  · exact B358083
  · exact B358087
  · exact B358091
  · exact B358095
  · exact B358099
  · exact B358103
  · exact B358107
  · exact B358111
  · exact B358115
  · exact B358119
  · exact B358123
  · exact B358127
  · exact B358131
  · exact B358135
  · exact B358139
  · exact B358143
  · exact B358147
  · exact B358151
  · exact B358155
  · exact B358159
  · exact B358163
  · exact B358167
  · exact B358171
  · exact B358175
  · exact B358179
  · exact B358183
  · exact B358187
  · exact B358191
  · exact B358195
  · exact B358199
  · exact B358203
  · exact B358207
  · exact B358211
  · exact B358215
  · exact B358219
  · exact B358223
  · exact B358227
  · exact B358231
  · exact B358235
  · exact B358239
  · exact B358243
  · exact B358247
  · exact B358251
  · exact B358255
  · exact B358259
  · exact B358263
  · exact B358267
  · exact B358271
  · exact B358275
  · exact B358279
  · exact B358283
  · exact B358287
  · exact B358291
  · exact B358295
  · exact B358299
  · exact B358303
  · exact B358307
  · exact B358311
  · exact B358315
  · exact B358319
  · exact B358323
  · exact B358327
  · exact B358331
  · exact B358335
  · exact B358339
  · exact B358343
  · exact B358347
  · exact B358351
  · exact B358355
  · exact B358359
  · exact B358363
  · exact B358367
  · exact B358371
  · exact B358375
  · exact B358379
  · exact B358383
  · exact B358387
  · exact B358391
  · exact B358395
  · exact B358399
  · exact B358403
  · exact B358407
  · exact B358411
  · exact B358415
  · exact B358419
  · exact B358423
  · exact B358427
  · exact B358431
  · exact B358435
  · exact B358439
  · exact B358443
  · exact B358447
  · exact B358451
  · exact B358455
  · exact B358459
  · exact B358463
  · exact B358467
  · exact B358471
  · exact B358475
  · exact B358479
  · exact B358483
  · exact B358487
  · exact B358491
  · exact B358495
  · exact B358499
  · exact B358503
  · exact B358507
  · exact B358511
  · exact B358515
  · exact B358519
  · exact B358523
  · exact B358527
  · exact B358531
  · exact B358535
  · exact B358539
  · exact B358543
  · exact B358547
  · exact B358551
  · exact B358555
  · exact B358559
  · exact B358563
  · exact B358567
  · exact B358571
  · exact B358575
  · exact B358579
  · exact B358583
  · exact B358587
  · exact B358591
  · exact B358595
  · exact B358599
  · exact B358603
  · exact B358607
  · exact B358611
  · exact B358615
  · exact B358619
  · exact B358623
  · exact B358627
  · exact B358631
  · exact B358635
  · exact B358639
  · exact B358643
  · exact B358647
  · exact B358651
  · exact B358655
  · exact B358659
  · exact B358663
  · exact B358667
  · exact B358671
  · exact B358675
  · exact B358679
  · exact B358683
  · exact B358687
  · exact B358691
  · exact B358695
  · exact B358699
  · exact B358703
  · exact B358707
  · exact B358711
  · exact B358715
  · exact B358719
  · exact B358723
  · exact B358727
  · exact B358731
  · exact B358735
  · exact B358739
  · exact B358743
  · exact B358747
  · exact B358751
  · exact B358755

theorem solution (m : ℕ) (hlo : 354756 ≤ m) (hhi : m ≤ 358756) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 88689 ≤ j := by omega
    have hj2 : j ≤ 89688 := by omega
    have hb : Blo 354756 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 89389 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
