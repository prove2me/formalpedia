-- Prove2me | solution 1 for syracuse_descends_range_1064615_1068615
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:22:29.421994+00:00
-- url     : https://prove2.me/submissions/abdca3d3-f20a-47dd-b200-7582de609240

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


theorem B1802317 : Blo 1064615 1802317 := bbase (se 3 (by rfl) ⟨337934, by rfl⟩ : syracuseStep 1802317 = 675869) (by norm_num)
theorem B1081469 : Blo 1064615 1081469 := bbase (se 3 (by rfl) ⟨202775, by rfl⟩ : syracuseStep 1081469 = 405551) (by norm_num)
theorem B1802405 : Blo 1064615 1802405 := bbase (se 4 (by rfl) ⟨168975, by rfl⟩ : syracuseStep 1802405 = 337951) (by norm_num)
theorem B3604661 : Blo 1064615 3604661 := bbase (se 5 (by rfl) ⟨168968, by rfl⟩ : syracuseStep 3604661 = 337937) (by norm_num)
theorem B1802533 : Blo 1064615 1802533 := bbase (se 4 (by rfl) ⟨168987, by rfl⟩ : syracuseStep 1802533 = 337975) (by norm_num)
theorem B1802621 : Blo 1064615 1802621 := bbase (se 3 (by rfl) ⟨337991, by rfl⟩ : syracuseStep 1802621 = 675983) (by norm_num)
theorem B1802749 : Blo 1064615 1802749 := bbase (se 3 (by rfl) ⟨338015, by rfl⟩ : syracuseStep 1802749 = 676031) (by norm_num)
theorem B1802837 : Blo 1064615 1802837 := bbase (se 8 (by rfl) ⟨10563, by rfl⟩ : syracuseStep 1802837 = 21127) (by norm_num)
theorem B3605093 : Blo 1064615 3605093 := bbase (se 4 (by rfl) ⟨337977, by rfl⟩ : syracuseStep 3605093 = 675955) (by norm_num)
theorem B5407397 : Blo 1064615 5407397 := bbase (se 4 (by rfl) ⟨506943, by rfl⟩ : syracuseStep 5407397 = 1013887) (by norm_num)
theorem B1802965 : Blo 1064615 1802965 := bbase (se 7 (by rfl) ⟨21128, by rfl⟩ : syracuseStep 1802965 = 42257) (by norm_num)
theorem B2884373 : Blo 1064615 2884373 := bbase (se 6 (by rfl) ⟨67602, by rfl⟩ : syracuseStep 2884373 = 135205) (by norm_num)
theorem B1803053 : Blo 1064615 1803053 := bbase (se 3 (by rfl) ⟨338072, by rfl⟩ : syracuseStep 1803053 = 676145) (by norm_num)
theorem B1442693 : Blo 1064615 1442693 := bbase (se 4 (by rfl) ⟨135252, by rfl⟩ : syracuseStep 1442693 = 270505) (by norm_num)
theorem B1803181 : Blo 1064615 1803181 := bbase (se 3 (by rfl) ⟨338096, by rfl⟩ : syracuseStep 1803181 = 676193) (by norm_num)
theorem B11535317 : Blo 1064615 11535317 := bbase (se 7 (by rfl) ⟨135179, by rfl⟩ : syracuseStep 11535317 = 270359) (by norm_num)
theorem B1082341 : Blo 1064615 1082341 := bbase (se 4 (by rfl) ⟨101469, by rfl⟩ : syracuseStep 1082341 = 202939) (by norm_num)
theorem B1803269 : Blo 1064615 1803269 := bbase (se 4 (by rfl) ⟨169056, by rfl⟩ : syracuseStep 1803269 = 338113) (by norm_num)
theorem B3605525 : Blo 1064615 3605525 := bbase (se 6 (by rfl) ⟨84504, by rfl⟩ : syracuseStep 3605525 = 169009) (by norm_num)
theorem B1279165 : Blo 1064615 1279165 := bbase (se 3 (by rfl) ⟨239843, by rfl⟩ : syracuseStep 1279165 = 479687) (by norm_num)
theorem B2884805 : Blo 1064615 2884805 := bbase (se 4 (by rfl) ⟨270450, by rfl⟩ : syracuseStep 2884805 = 540901) (by norm_num)
theorem B3605957 : Blo 1064615 3605957 := bbase (se 4 (by rfl) ⟨338058, by rfl⟩ : syracuseStep 3605957 = 676117) (by norm_num)
theorem B1705445 : Blo 1064615 1705445 := bbase (se 4 (by rfl) ⟨159885, by rfl⟩ : syracuseStep 1705445 = 319771) (by norm_num)
theorem B1541605 : Blo 1064615 1541605 := bbase (se 4 (by rfl) ⟨144525, by rfl⟩ : syracuseStep 1541605 = 289051) (by norm_num)
theorem B4556341 : Blo 1064615 4556341 := bbase (se 5 (by rfl) ⟨213578, by rfl⟩ : syracuseStep 4556341 = 427157) (by norm_num)
theorem B1279549 : Blo 1064615 1279549 := bbase (se 3 (by rfl) ⟨239915, by rfl⟩ : syracuseStep 1279549 = 479831) (by norm_num)
theorem B2164429 : Blo 1064615 2164429 := bbase (se 3 (by rfl) ⟨405830, by rfl⟩ : syracuseStep 2164429 = 811661) (by norm_num)
theorem B24610517 : Blo 1064615 24610517 := bbase (se 7 (by rfl) ⟨288404, by rfl⟩ : syracuseStep 24610517 = 576809) (by norm_num)
theorem B1214281 : Blo 1064615 1214281 := bbase (se 2 (by rfl) ⟨455355, by rfl⟩ : syracuseStep 1214281 = 910711) (by norm_num)
theorem B3606389 : Blo 1064615 3606389 := bbase (se 5 (by rfl) ⟨169049, by rfl⟩ : syracuseStep 3606389 = 338099) (by norm_num)
theorem B5408693 : Blo 1064615 5408693 := bbase (se 5 (by rfl) ⟨253532, by rfl⟩ : syracuseStep 5408693 = 507065) (by norm_num)
theorem B4622597 : Blo 1064615 4622597 := bbase (se 4 (by rfl) ⟨433368, by rfl⟩ : syracuseStep 4622597 = 866737) (by norm_num)
theorem B1280405 : Blo 1064615 1280405 := bbase (se 6 (by rfl) ⟨30009, by rfl⟩ : syracuseStep 1280405 = 60019) (by norm_num)
theorem B1706437 : Blo 1064615 1706437 := bbase (se 4 (by rfl) ⟨159978, by rfl⟩ : syracuseStep 1706437 = 319957) (by norm_num)
theorem B1280713 : Blo 1064615 1280713 := bbase (se 2 (by rfl) ⟨480267, by rfl⟩ : syracuseStep 1280713 = 960535) (by norm_num)
theorem B1215229 : Blo 1064615 1215229 := bbase (se 3 (by rfl) ⟨227855, by rfl⟩ : syracuseStep 1215229 = 455711) (by norm_num)
theorem B2886533 : Blo 1064615 2886533 := bbase (se 4 (by rfl) ⟨270612, by rfl⟩ : syracuseStep 2886533 = 541225) (by norm_num)
theorem B1280929 : Blo 1064615 1280929 := bbase (se 2 (by rfl) ⟨480348, by rfl⟩ : syracuseStep 1280929 = 960697) (by norm_num)
theorem B2558965 : Blo 1064615 2558965 := bbase (se 5 (by rfl) ⟨119951, by rfl⟩ : syracuseStep 2558965 = 239903) (by norm_num)
theorem B4557829 : Blo 1064615 4557829 := bbase (se 4 (by rfl) ⟨427296, by rfl⟩ : syracuseStep 4557829 = 854593) (by norm_num)
theorem B4557845 : Blo 1064615 4557845 := bbase (se 6 (by rfl) ⟨106824, by rfl⟩ : syracuseStep 4557845 = 213649) (by norm_num)
theorem B1707085 : Blo 1064615 1707085 := bbase (se 3 (by rfl) ⟨320078, by rfl⟩ : syracuseStep 1707085 = 640157) (by norm_num)
theorem B2395421 : Blo 1064615 2395421 := bbase (se 3 (by rfl) ⟨449141, by rfl⟩ : syracuseStep 2395421 = 898283) (by norm_num)
theorem B2395493 : Blo 1064615 2395493 := bbase (se 4 (by rfl) ⟨224577, by rfl⟩ : syracuseStep 2395493 = 449155) (by norm_num)
theorem B2395565 : Blo 1064615 2395565 := bbase (se 3 (by rfl) ⟨449168, by rfl⟩ : syracuseStep 2395565 = 898337) (by norm_num)
theorem B6917557 : Blo 1064615 6917557 := bbase (se 5 (by rfl) ⟨324260, by rfl⟩ : syracuseStep 6917557 = 648521) (by norm_num)
theorem B3411413 : Blo 1064615 3411413 := bbase (se 7 (by rfl) ⟨39977, by rfl⟩ : syracuseStep 3411413 = 79955) (by norm_num)
theorem B2395637 : Blo 1064615 2395637 := bbase (se 5 (by rfl) ⟨112295, by rfl⟩ : syracuseStep 2395637 = 224591) (by norm_num)
theorem B1281529 : Blo 1064615 1281529 := bbase (se 2 (by rfl) ⟨480573, by rfl⟩ : syracuseStep 1281529 = 961147) (by norm_num)
theorem B2395709 : Blo 1064615 2395709 := bbase (se 3 (by rfl) ⟨449195, by rfl⟩ : syracuseStep 2395709 = 898391) (by norm_num)
theorem B2395781 : Blo 1064615 2395781 := bbase (se 4 (by rfl) ⟨224604, by rfl⟩ : syracuseStep 2395781 = 449209) (by norm_num)
theorem B2395853 : Blo 1064615 2395853 := bbase (se 3 (by rfl) ⟨449222, by rfl⟩ : syracuseStep 2395853 = 898445) (by norm_num)
theorem B2395925 : Blo 1064615 2395925 := bbase (se 6 (by rfl) ⟨56154, by rfl⟩ : syracuseStep 2395925 = 112309) (by norm_num)
theorem B1216297 : Blo 1064615 1216297 := bbase (se 2 (by rfl) ⟨456111, by rfl⟩ : syracuseStep 1216297 = 912223) (by norm_num)
theorem B2395997 : Blo 1064615 2395997 := bbase (se 3 (by rfl) ⟨449249, by rfl⟩ : syracuseStep 2395997 = 898499) (by norm_num)
theorem B1347445 : Blo 1064615 1347445 := bbase (se 5 (by rfl) ⟨63161, by rfl⟩ : syracuseStep 1347445 = 126323) (by norm_num)
theorem B2396069 : Blo 1064615 2396069 := bbase (se 4 (by rfl) ⟨224631, by rfl⟩ : syracuseStep 2396069 = 449263) (by norm_num)
theorem B2396141 : Blo 1064615 2396141 := bbase (se 3 (by rfl) ⟨449276, by rfl⟩ : syracuseStep 2396141 = 898553) (by norm_num)
theorem B1708013 : Blo 1064615 1708013 := bbase (se 3 (by rfl) ⟨320252, by rfl⟩ : syracuseStep 1708013 = 640505) (by norm_num)
theorem B1347617 : Blo 1064615 1347617 := bbase (se 2 (by rfl) ⟨505356, by rfl⟩ : syracuseStep 1347617 = 1010713) (by norm_num)
theorem B1216553 : Blo 1064615 1216553 := bbase (se 2 (by rfl) ⟨456207, by rfl⟩ : syracuseStep 1216553 = 912415) (by norm_num)
theorem B2396213 : Blo 1064615 2396213 := bbase (se 5 (by rfl) ⟨112322, by rfl⟩ : syracuseStep 2396213 = 224645) (by norm_num)
theorem B1347673 : Blo 1064615 1347673 := bbase (se 2 (by rfl) ⟨505377, by rfl⟩ : syracuseStep 1347673 = 1010755) (by norm_num)
theorem B2396285 : Blo 1064615 2396285 := bbase (se 3 (by rfl) ⟨449303, by rfl⟩ : syracuseStep 2396285 = 898607) (by norm_num)
theorem B1347769 : Blo 1064615 1347769 := bbase (se 2 (by rfl) ⟨505413, by rfl⟩ : syracuseStep 1347769 = 1010827) (by norm_num)
theorem B2396357 : Blo 1064615 2396357 := bbase (se 4 (by rfl) ⟨224658, by rfl⟩ : syracuseStep 2396357 = 449317) (by norm_num)
theorem B2396429 : Blo 1064615 2396429 := bbase (se 3 (by rfl) ⟨449330, by rfl⟩ : syracuseStep 2396429 = 898661) (by norm_num)
theorem B2396501 : Blo 1064615 2396501 := bbase (se 10 (by rfl) ⟨3510, by rfl⟩ : syracuseStep 2396501 = 7021) (by norm_num)
theorem B1347941 : Blo 1064615 1347941 := bbase (se 4 (by rfl) ⟨126369, by rfl⟩ : syracuseStep 1347941 = 252739) (by norm_num)
theorem B2560405 : Blo 1064615 2560405 := bbase (se 6 (by rfl) ⟨60009, by rfl⟩ : syracuseStep 2560405 = 120019) (by norm_num)
theorem B1347997 : Blo 1064615 1347997 := bbase (se 3 (by rfl) ⟨252749, by rfl⟩ : syracuseStep 1347997 = 505499) (by norm_num)
theorem B2396573 : Blo 1064615 2396573 := bbase (se 3 (by rfl) ⟨449357, by rfl⟩ : syracuseStep 2396573 = 898715) (by norm_num)
theorem B2429365 : Blo 1064615 2429365 := bbase (se 5 (by rfl) ⟨113876, by rfl⟩ : syracuseStep 2429365 = 227753) (by norm_num)
theorem B1708469 : Blo 1064615 1708469 := bbase (se 5 (by rfl) ⟨80084, by rfl⟩ : syracuseStep 1708469 = 160169) (by norm_num)
theorem B2396645 : Blo 1064615 2396645 := bbase (se 4 (by rfl) ⟨224685, by rfl⟩ : syracuseStep 2396645 = 449371) (by norm_num)
theorem B1348093 : Blo 1064615 1348093 := bbase (se 3 (by rfl) ⟨252767, by rfl⟩ : syracuseStep 1348093 = 505535) (by norm_num)
theorem B2396717 : Blo 1064615 2396717 := bbase (se 3 (by rfl) ⟨449384, by rfl⟩ : syracuseStep 2396717 = 898769) (by norm_num)
theorem B1282673 : Blo 1064615 1282673 := bbase (se 2 (by rfl) ⟨481002, by rfl⟩ : syracuseStep 1282673 = 962005) (by norm_num)
theorem B2396789 : Blo 1064615 2396789 := bbase (se 5 (by rfl) ⟨112349, by rfl⟩ : syracuseStep 2396789 = 224699) (by norm_num)
theorem B1217173 : Blo 1064615 1217173 := bbase (se 6 (by rfl) ⟨28527, by rfl⟩ : syracuseStep 1217173 = 57055) (by norm_num)
theorem B1282721 : Blo 1064615 1282721 := bbase (se 2 (by rfl) ⟨481020, by rfl⟩ : syracuseStep 1282721 = 962041) (by norm_num)
theorem B1348265 : Blo 1064615 1348265 := bbase (se 2 (by rfl) ⟨505599, by rfl⟩ : syracuseStep 1348265 = 1011199) (by norm_num)
theorem B2396861 : Blo 1064615 2396861 := bbase (se 3 (by rfl) ⟨449411, by rfl⟩ : syracuseStep 2396861 = 898823) (by norm_num)
theorem B2888405 : Blo 1064615 2888405 := bbase (se 7 (by rfl) ⟨33848, by rfl⟩ : syracuseStep 2888405 = 67697) (by norm_num)
theorem B1348321 : Blo 1064615 1348321 := bbase (se 2 (by rfl) ⟨505620, by rfl⟩ : syracuseStep 1348321 = 1011241) (by norm_num)
theorem B1282817 : Blo 1064615 1282817 := bbase (se 2 (by rfl) ⟨481056, by rfl⟩ : syracuseStep 1282817 = 962113) (by norm_num)
theorem B2396933 : Blo 1064615 2396933 := bbase (se 4 (by rfl) ⟨224712, by rfl⟩ : syracuseStep 2396933 = 449425) (by norm_num)
theorem B1348417 : Blo 1064615 1348417 := bbase (se 2 (by rfl) ⟨505656, by rfl⟩ : syracuseStep 1348417 = 1011313) (by norm_num)
theorem B2397005 : Blo 1064615 2397005 := bbase (se 3 (by rfl) ⟨449438, by rfl⟩ : syracuseStep 2397005 = 898877) (by norm_num)
theorem B2397077 : Blo 1064615 2397077 := bbase (se 6 (by rfl) ⟨56181, by rfl⟩ : syracuseStep 2397077 = 112363) (by norm_num)
theorem B1282981 : Blo 1064615 1282981 := bbase (se 4 (by rfl) ⟨120279, by rfl⟩ : syracuseStep 1282981 = 240559) (by norm_num)
theorem B2397149 : Blo 1064615 2397149 := bbase (se 3 (by rfl) ⟨449465, by rfl⟩ : syracuseStep 2397149 = 898931) (by norm_num)
theorem B1348589 : Blo 1064615 1348589 := bbase (se 3 (by rfl) ⟨252860, by rfl⟩ : syracuseStep 1348589 = 505721) (by norm_num)
theorem B2561021 : Blo 1064615 2561021 := bbase (se 3 (by rfl) ⟨480191, by rfl⟩ : syracuseStep 2561021 = 960383) (by norm_num)
theorem B2397221 : Blo 1064615 2397221 := bbase (se 4 (by rfl) ⟨224739, by rfl⟩ : syracuseStep 2397221 = 449479) (by norm_num)
theorem B1348645 : Blo 1064615 1348645 := bbase (se 4 (by rfl) ⟨126435, by rfl⟩ : syracuseStep 1348645 = 252871) (by norm_num)
theorem B2397293 : Blo 1064615 2397293 := bbase (se 3 (by rfl) ⟨449492, by rfl⟩ : syracuseStep 2397293 = 898985) (by norm_num)
theorem B1283197 : Blo 1064615 1283197 := bbase (se 3 (by rfl) ⟨240599, by rfl⟩ : syracuseStep 1283197 = 481199) (by norm_num)
theorem B1348741 : Blo 1064615 1348741 := bbase (se 4 (by rfl) ⟨126444, by rfl⟩ : syracuseStep 1348741 = 252889) (by norm_num)
theorem B2397365 : Blo 1064615 2397365 := bbase (se 5 (by rfl) ⟨112376, by rfl⟩ : syracuseStep 2397365 = 224753) (by norm_num)
theorem B2561213 : Blo 1064615 2561213 := bbase (se 3 (by rfl) ⟨480227, by rfl⟩ : syracuseStep 2561213 = 960455) (by norm_num)
theorem B4560101 : Blo 1064615 4560101 := bbase (se 4 (by rfl) ⟨427509, by rfl⟩ : syracuseStep 4560101 = 855019) (by norm_num)
theorem B9114869 : Blo 1064615 9114869 := bbase (se 5 (by rfl) ⟨427259, by rfl⟩ : syracuseStep 9114869 = 854519) (by norm_num)
theorem B2397437 : Blo 1064615 2397437 := bbase (se 3 (by rfl) ⟨449519, by rfl⟩ : syracuseStep 2397437 = 899039) (by norm_num)
theorem B3413285 : Blo 1064615 3413285 := bbase (se 4 (by rfl) ⟨319995, by rfl⟩ : syracuseStep 3413285 = 639991) (by norm_num)
theorem B1283365 : Blo 1064615 1283365 := bbase (se 4 (by rfl) ⟨120315, by rfl⟩ : syracuseStep 1283365 = 240631) (by norm_num)
theorem B1348913 : Blo 1064615 1348913 := bbase (se 2 (by rfl) ⟨505842, by rfl⟩ : syracuseStep 1348913 = 1011685) (by norm_num)
theorem B1217857 : Blo 1064615 1217857 := bbase (se 2 (by rfl) ⟨456696, by rfl⟩ : syracuseStep 1217857 = 913393) (by norm_num)
theorem B2397509 : Blo 1064615 2397509 := bbase (se 4 (by rfl) ⟨224766, by rfl⟩ : syracuseStep 2397509 = 449533) (by norm_num)
theorem B4330837 : Blo 1064615 4330837 := bbase (se 14 (by rfl) ⟨396, by rfl⟩ : syracuseStep 4330837 = 793) (by norm_num)
theorem B1348969 : Blo 1064615 1348969 := bbase (se 2 (by rfl) ⟨505863, by rfl⟩ : syracuseStep 1348969 = 1011727) (by norm_num)
theorem B8099189 : Blo 1064615 8099189 := bbase (se 5 (by rfl) ⟨379649, by rfl⟩ : syracuseStep 8099189 = 759299) (by norm_num)
theorem B2397581 : Blo 1064615 2397581 := bbase (se 3 (by rfl) ⟨449546, by rfl⟩ : syracuseStep 2397581 = 899093) (by norm_num)
theorem B1349065 : Blo 1064615 1349065 := bbase (se 2 (by rfl) ⟨505899, by rfl⟩ : syracuseStep 1349065 = 1011799) (by norm_num)
theorem B2397653 : Blo 1064615 2397653 := bbase (se 7 (by rfl) ⟨28097, by rfl⟩ : syracuseStep 2397653 = 56195) (by norm_num)
theorem B2561501 : Blo 1064615 2561501 := bbase (se 3 (by rfl) ⟨480281, by rfl⟩ : syracuseStep 2561501 = 960563) (by norm_num)
theorem B2397725 : Blo 1064615 2397725 := bbase (se 3 (by rfl) ⟨449573, by rfl⟩ : syracuseStep 2397725 = 899147) (by norm_num)
theorem B2397797 : Blo 1064615 2397797 := bbase (se 4 (by rfl) ⟨224793, by rfl⟩ : syracuseStep 2397797 = 449587) (by norm_num)
theorem B1349237 : Blo 1064615 1349237 := bbase (se 5 (by rfl) ⟨63245, by rfl⟩ : syracuseStep 1349237 = 126491) (by norm_num)
theorem B2397869 : Blo 1064615 2397869 := bbase (se 3 (by rfl) ⟨449600, by rfl⟩ : syracuseStep 2397869 = 899201) (by norm_num)
theorem B1349293 : Blo 1064615 1349293 := bbase (se 3 (by rfl) ⟨252992, by rfl⟩ : syracuseStep 1349293 = 505985) (by norm_num)
theorem B1218221 : Blo 1064615 1218221 := bbase (se 3 (by rfl) ⟨228416, by rfl⟩ : syracuseStep 1218221 = 456833) (by norm_num)
theorem B1218277 : Blo 1064615 1218277 := bbase (se 4 (by rfl) ⟨114213, by rfl⟩ : syracuseStep 1218277 = 228427) (by norm_num)
theorem B2397941 : Blo 1064615 2397941 := bbase (se 5 (by rfl) ⟨112403, by rfl⟩ : syracuseStep 2397941 = 224807) (by norm_num)
theorem B1349389 : Blo 1064615 1349389 := bbase (se 3 (by rfl) ⟨253010, by rfl⟩ : syracuseStep 1349389 = 506021) (by norm_num)
theorem B5117717 : Blo 1064615 5117717 := bbase (se 6 (by rfl) ⟨119946, by rfl⟩ : syracuseStep 5117717 = 239893) (by norm_num)
theorem B2398013 : Blo 1064615 2398013 := bbase (se 3 (by rfl) ⟨449627, by rfl⟩ : syracuseStep 2398013 = 899255) (by norm_num)
theorem B1709885 : Blo 1064615 1709885 := bbase (se 3 (by rfl) ⟨320603, by rfl⟩ : syracuseStep 1709885 = 641207) (by norm_num)
theorem B5117813 : Blo 1064615 5117813 := bbase (se 5 (by rfl) ⟨239897, by rfl⟩ : syracuseStep 5117813 = 479795) (by norm_num)
theorem B2398085 : Blo 1064615 2398085 := bbase (se 4 (by rfl) ⟨224820, by rfl⟩ : syracuseStep 2398085 = 449641) (by norm_num)
theorem B1349561 : Blo 1064615 1349561 := bbase (se 2 (by rfl) ⟨506085, by rfl⟩ : syracuseStep 1349561 = 1012171) (by norm_num)
theorem B2398157 : Blo 1064615 2398157 := bbase (se 3 (by rfl) ⟨449654, by rfl⟩ : syracuseStep 2398157 = 899309) (by norm_num)
theorem B1349617 : Blo 1064615 1349617 := bbase (se 2 (by rfl) ⟨506106, by rfl⟩ : syracuseStep 1349617 = 1012213) (by norm_num)
theorem B2398229 : Blo 1064615 2398229 := bbase (se 6 (by rfl) ⟨56208, by rfl⟩ : syracuseStep 2398229 = 112417) (by norm_num)
theorem B1710109 : Blo 1064615 1710109 := bbase (se 3 (by rfl) ⟨320645, by rfl⟩ : syracuseStep 1710109 = 641291) (by norm_num)
theorem B1349713 : Blo 1064615 1349713 := bbase (se 2 (by rfl) ⟨506142, by rfl⟩ : syracuseStep 1349713 = 1012285) (by norm_num)
theorem B2398301 : Blo 1064615 2398301 := bbase (se 3 (by rfl) ⟨449681, by rfl⟩ : syracuseStep 2398301 = 899363) (by norm_num)
theorem B2398373 : Blo 1064615 2398373 := bbase (se 4 (by rfl) ⟨224847, by rfl⟩ : syracuseStep 2398373 = 449695) (by norm_num)
theorem B2398445 : Blo 1064615 2398445 := bbase (se 3 (by rfl) ⟨449708, by rfl⟩ : syracuseStep 2398445 = 899417) (by norm_num)
theorem B1349885 : Blo 1064615 1349885 := bbase (se 3 (by rfl) ⟨253103, by rfl⟩ : syracuseStep 1349885 = 506207) (by norm_num)
theorem B2398517 : Blo 1064615 2398517 := bbase (se 5 (by rfl) ⟨112430, by rfl⟩ : syracuseStep 2398517 = 224861) (by norm_num)
theorem B1349941 : Blo 1064615 1349941 := bbase (se 5 (by rfl) ⟨63278, by rfl⟩ : syracuseStep 1349941 = 126557) (by norm_num)
theorem B1644853 : Blo 1064615 1644853 := bbase (se 5 (by rfl) ⟨77102, by rfl⟩ : syracuseStep 1644853 = 154205) (by norm_num)
theorem B2398589 : Blo 1064615 2398589 := bbase (se 3 (by rfl) ⟨449735, by rfl⟩ : syracuseStep 2398589 = 899471) (by norm_num)
theorem B1350037 : Blo 1064615 1350037 := bbase (se 6 (by rfl) ⟨31641, by rfl⟩ : syracuseStep 1350037 = 63283) (by norm_num)
theorem B2398661 : Blo 1064615 2398661 := bbase (se 4 (by rfl) ⟨224874, by rfl⟩ : syracuseStep 2398661 = 449749) (by norm_num)
theorem B2398733 : Blo 1064615 2398733 := bbase (se 3 (by rfl) ⟨449762, by rfl⟩ : syracuseStep 2398733 = 899525) (by norm_num)
theorem B1972765 : Blo 1064615 1972765 := bbase (se 3 (by rfl) ⟨369893, by rfl⟩ : syracuseStep 1972765 = 739787) (by norm_num)
theorem B6068789 : Blo 1064615 6068789 := bbase (se 5 (by rfl) ⟨284474, by rfl⟩ : syracuseStep 6068789 = 568949) (by norm_num)
theorem B1350209 : Blo 1064615 1350209 := bbase (se 2 (by rfl) ⟨506328, by rfl⟩ : syracuseStep 1350209 = 1012657) (by norm_num)
theorem B2398805 : Blo 1064615 2398805 := bbase (se 8 (by rfl) ⟨14055, by rfl⟩ : syracuseStep 2398805 = 28111) (by norm_num)
theorem B1350265 : Blo 1064615 1350265 := bbase (se 2 (by rfl) ⟨506349, by rfl⟩ : syracuseStep 1350265 = 1012699) (by norm_num)
theorem B2398877 : Blo 1064615 2398877 := bbase (se 3 (by rfl) ⟨449789, by rfl⟩ : syracuseStep 2398877 = 899579) (by norm_num)
theorem B1350361 : Blo 1064615 1350361 := bbase (se 2 (by rfl) ⟨506385, by rfl⟩ : syracuseStep 1350361 = 1012771) (by norm_num)
theorem B2398949 : Blo 1064615 2398949 := bbase (se 4 (by rfl) ⟨224901, by rfl⟩ : syracuseStep 2398949 = 449803) (by norm_num)
theorem B2399021 : Blo 1064615 2399021 := bbase (se 3 (by rfl) ⟨449816, by rfl⟩ : syracuseStep 2399021 = 899633) (by norm_num)
theorem B2399093 : Blo 1064615 2399093 := bbase (se 5 (by rfl) ⟨112457, by rfl⟩ : syracuseStep 2399093 = 224915) (by norm_num)
theorem B1350533 : Blo 1064615 1350533 := bbase (se 4 (by rfl) ⟨126612, by rfl⟩ : syracuseStep 1350533 = 253225) (by norm_num)
theorem B2399165 : Blo 1064615 2399165 := bbase (se 3 (by rfl) ⟨449843, by rfl⟩ : syracuseStep 2399165 = 899687) (by norm_num)
theorem B1350589 : Blo 1064615 1350589 := bbase (se 3 (by rfl) ⟨253235, by rfl⟩ : syracuseStep 1350589 = 506471) (by norm_num)
theorem B2399237 : Blo 1064615 2399237 := bbase (se 4 (by rfl) ⟨224928, by rfl⟩ : syracuseStep 2399237 = 449857) (by norm_num)
theorem B1350685 : Blo 1064615 1350685 := bbase (se 3 (by rfl) ⟨253253, by rfl⟩ : syracuseStep 1350685 = 506507) (by norm_num)
theorem B2399309 : Blo 1064615 2399309 := bbase (se 3 (by rfl) ⟨449870, by rfl⟩ : syracuseStep 2399309 = 899741) (by norm_num)
theorem B2399381 : Blo 1064615 2399381 := bbase (se 6 (by rfl) ⟨56235, by rfl⟩ : syracuseStep 2399381 = 112471) (by norm_num)
theorem B1350857 : Blo 1064615 1350857 := bbase (se 2 (by rfl) ⟨506571, by rfl⟩ : syracuseStep 1350857 = 1013143) (by norm_num)
theorem B2399453 : Blo 1064615 2399453 := bbase (se 3 (by rfl) ⟨449897, by rfl⟩ : syracuseStep 2399453 = 899795) (by norm_num)
theorem B1350913 : Blo 1064615 1350913 := bbase (se 2 (by rfl) ⟨506592, by rfl⟩ : syracuseStep 1350913 = 1013185) (by norm_num)
theorem B2399525 : Blo 1064615 2399525 := bbase (se 4 (by rfl) ⟨224955, by rfl⟩ : syracuseStep 2399525 = 449911) (by norm_num)
theorem B1351009 : Blo 1064615 1351009 := bbase (se 2 (by rfl) ⟨506628, by rfl⟩ : syracuseStep 1351009 = 1013257) (by norm_num)
theorem B2399597 : Blo 1064615 2399597 := bbase (se 3 (by rfl) ⟨449924, by rfl⟩ : syracuseStep 2399597 = 899849) (by norm_num)
theorem B1711525 : Blo 1064615 1711525 := bbase (se 4 (by rfl) ⟨160455, by rfl⟩ : syracuseStep 1711525 = 320911) (by norm_num)
theorem B2563501 : Blo 1064615 2563501 := bbase (se 3 (by rfl) ⟨480656, by rfl⟩ : syracuseStep 2563501 = 961313) (by norm_num)
theorem B2399669 : Blo 1064615 2399669 := bbase (se 5 (by rfl) ⟨112484, by rfl⟩ : syracuseStep 2399669 = 224969) (by norm_num)
theorem B2399741 : Blo 1064615 2399741 := bbase (se 3 (by rfl) ⟨449951, by rfl⟩ : syracuseStep 2399741 = 899903) (by norm_num)
theorem B1351181 : Blo 1064615 1351181 := bbase (se 3 (by rfl) ⟨253346, by rfl⟩ : syracuseStep 1351181 = 506693) (by norm_num)
theorem B2399813 : Blo 1064615 2399813 := bbase (se 4 (by rfl) ⟨224982, by rfl⟩ : syracuseStep 2399813 = 449965) (by norm_num)
theorem B1351237 : Blo 1064615 1351237 := bbase (se 4 (by rfl) ⟨126678, by rfl⟩ : syracuseStep 1351237 = 253357) (by norm_num)
theorem B2399885 : Blo 1064615 2399885 := bbase (se 3 (by rfl) ⟨449978, by rfl⟩ : syracuseStep 2399885 = 899957) (by norm_num)
theorem B1351333 : Blo 1064615 1351333 := bbase (se 4 (by rfl) ⟨126687, by rfl⟩ : syracuseStep 1351333 = 253375) (by norm_num)
theorem B2694829 : Blo 1064615 2694829 := bbase (se 3 (by rfl) ⟨505280, by rfl⟩ : syracuseStep 2694829 = 1010561) (by norm_num)
theorem B2399957 : Blo 1064615 2399957 := bbase (se 7 (by rfl) ⟨28124, by rfl⟩ : syracuseStep 2399957 = 56249) (by norm_num)
theorem B5119733 : Blo 1064615 5119733 := bbase (se 5 (by rfl) ⟨239987, by rfl⟩ : syracuseStep 5119733 = 479975) (by norm_num)
theorem B2694941 : Blo 1064615 2694941 := bbase (se 3 (by rfl) ⟨505301, by rfl⟩ : syracuseStep 2694941 = 1010603) (by norm_num)
theorem B2400029 : Blo 1064615 2400029 := bbase (se 3 (by rfl) ⟨450005, by rfl⟩ : syracuseStep 2400029 = 900011) (by norm_num)
theorem B1351505 : Blo 1064615 1351505 := bbase (se 2 (by rfl) ⟨506814, by rfl⟩ : syracuseStep 1351505 = 1013629) (by norm_num)
theorem B2400101 : Blo 1064615 2400101 := bbase (se 4 (by rfl) ⟨225009, by rfl⟩ : syracuseStep 2400101 = 450019) (by norm_num)
theorem B1351561 : Blo 1064615 1351561 := bbase (se 2 (by rfl) ⟨506835, by rfl⟩ : syracuseStep 1351561 = 1013671) (by norm_num)
theorem B2400173 : Blo 1064615 2400173 := bbase (se 3 (by rfl) ⟨450032, by rfl⟩ : syracuseStep 2400173 = 900065) (by norm_num)
theorem B2695133 : Blo 1064615 2695133 := bbase (se 3 (by rfl) ⟨505337, by rfl⟩ : syracuseStep 2695133 = 1010675) (by norm_num)
theorem B1351657 : Blo 1064615 1351657 := bbase (se 2 (by rfl) ⟨506871, by rfl⟩ : syracuseStep 1351657 = 1013743) (by norm_num)
theorem B3416053 : Blo 1064615 3416053 := bbase (se 5 (by rfl) ⟨160127, by rfl⟩ : syracuseStep 3416053 = 320255) (by norm_num)
theorem B2400245 : Blo 1064615 2400245 := bbase (se 5 (by rfl) ⟨112511, by rfl⟩ : syracuseStep 2400245 = 225023) (by norm_num)
theorem B2400317 : Blo 1064615 2400317 := bbase (se 3 (by rfl) ⟨450059, by rfl⟩ : syracuseStep 2400317 = 900119) (by norm_num)
theorem B1384537 : Blo 1064615 1384537 := bbase (se 2 (by rfl) ⟨519201, by rfl⟩ : syracuseStep 1384537 = 1038403) (by norm_num)
theorem B2400389 : Blo 1064615 2400389 := bbase (se 4 (by rfl) ⟨225036, by rfl⟩ : syracuseStep 2400389 = 450073) (by norm_num)
theorem B9117845 : Blo 1064615 9117845 := bbase (se 6 (by rfl) ⟨213699, by rfl⟩ : syracuseStep 9117845 = 427399) (by norm_num)
theorem B1351829 : Blo 1064615 1351829 := bbase (se 6 (by rfl) ⟨31683, by rfl⟩ : syracuseStep 1351829 = 63367) (by norm_num)
theorem B2400461 : Blo 1064615 2400461 := bbase (se 3 (by rfl) ⟨450086, by rfl⟩ : syracuseStep 2400461 = 900173) (by norm_num)
theorem B1351885 : Blo 1064615 1351885 := bbase (se 3 (by rfl) ⟨253478, by rfl⟩ : syracuseStep 1351885 = 506957) (by norm_num)
theorem B2400533 : Blo 1064615 2400533 := bbase (se 6 (by rfl) ⟨56262, by rfl⟩ : syracuseStep 2400533 = 112525) (by norm_num)
theorem B1351981 : Blo 1064615 1351981 := bbase (se 3 (by rfl) ⟨253496, by rfl⟩ : syracuseStep 1351981 = 506993) (by norm_num)
theorem B2695477 : Blo 1064615 2695477 := bbase (se 5 (by rfl) ⟨126350, by rfl⟩ : syracuseStep 2695477 = 252701) (by norm_num)
theorem B2466133 : Blo 1064615 2466133 := bbase (se 10 (by rfl) ⟨3612, by rfl⟩ : syracuseStep 2466133 = 7225) (by norm_num)
theorem B2400605 : Blo 1064615 2400605 := bbase (se 3 (by rfl) ⟨450113, by rfl⟩ : syracuseStep 2400605 = 900227) (by norm_num)
theorem B1155421 : Blo 1064615 1155421 := bbase (se 3 (by rfl) ⟨216641, by rfl⟩ : syracuseStep 1155421 = 433283) (by norm_num)
theorem B3842453 : Blo 1064615 3842453 := bbase (se 6 (by rfl) ⟨90057, by rfl⟩ : syracuseStep 3842453 = 180115) (by norm_num)
theorem B2695589 : Blo 1064615 2695589 := bbase (se 4 (by rfl) ⟨252711, by rfl⟩ : syracuseStep 2695589 = 505423) (by norm_num)
theorem B2400677 : Blo 1064615 2400677 := bbase (se 4 (by rfl) ⟨225063, by rfl⟩ : syracuseStep 2400677 = 450127) (by norm_num)
theorem B1352153 : Blo 1064615 1352153 := bbase (se 2 (by rfl) ⟨507057, by rfl⟩ : syracuseStep 1352153 = 1014115) (by norm_num)
theorem B2400749 : Blo 1064615 2400749 := bbase (se 3 (by rfl) ⟨450140, by rfl⟩ : syracuseStep 2400749 = 900281) (by norm_num)
theorem B1352209 : Blo 1064615 1352209 := bbase (se 2 (by rfl) ⟨507078, by rfl⟩ : syracuseStep 1352209 = 1014157) (by norm_num)
theorem B2400821 : Blo 1064615 2400821 := bbase (se 5 (by rfl) ⟨112538, by rfl⟩ : syracuseStep 2400821 = 225077) (by norm_num)
theorem B2695781 : Blo 1064615 2695781 := bbase (se 4 (by rfl) ⟨252729, by rfl⟩ : syracuseStep 2695781 = 505459) (by norm_num)
theorem B1352305 : Blo 1064615 1352305 := bbase (se 2 (by rfl) ⟨507114, by rfl⟩ : syracuseStep 1352305 = 1014229) (by norm_num)
theorem B2400893 : Blo 1064615 2400893 := bbase (se 3 (by rfl) ⟨450167, by rfl⟩ : syracuseStep 2400893 = 900335) (by norm_num)
theorem B2400965 : Blo 1064615 2400965 := bbase (se 4 (by rfl) ⟨225090, by rfl⟩ : syracuseStep 2400965 = 450181) (by norm_num)
theorem B2401037 : Blo 1064615 2401037 := bbase (se 3 (by rfl) ⟨450194, by rfl⟩ : syracuseStep 2401037 = 900389) (by norm_num)
theorem B2564885 : Blo 1064615 2564885 := bbase (se 6 (by rfl) ⟨60114, by rfl⟩ : syracuseStep 2564885 = 120229) (by norm_num)
theorem B2401109 : Blo 1064615 2401109 := bbase (se 9 (by rfl) ⟨7034, by rfl⟩ : syracuseStep 2401109 = 14069) (by norm_num)
theorem B4105093 : Blo 1064615 4105093 := bbase (se 4 (by rfl) ⟨384852, by rfl⟩ : syracuseStep 4105093 = 769705) (by norm_num)
theorem B2401181 : Blo 1064615 2401181 := bbase (se 3 (by rfl) ⟨450221, by rfl⟩ : syracuseStep 2401181 = 900443) (by norm_num)
theorem B2696125 : Blo 1064615 2696125 := bbase (se 3 (by rfl) ⟨505523, by rfl⟩ : syracuseStep 2696125 = 1011047) (by norm_num)
theorem B2401253 : Blo 1064615 2401253 := bbase (se 4 (by rfl) ⟨225117, by rfl⟩ : syracuseStep 2401253 = 450235) (by norm_num)
theorem B4105205 : Blo 1064615 4105205 := bbase (se 5 (by rfl) ⟨192431, by rfl⟩ : syracuseStep 4105205 = 384863) (by norm_num)
theorem B2696237 : Blo 1064615 2696237 := bbase (se 3 (by rfl) ⟨505544, by rfl⟩ : syracuseStep 2696237 = 1011089) (by norm_num)
theorem B2401325 : Blo 1064615 2401325 := bbase (se 3 (by rfl) ⟨450248, by rfl⟩ : syracuseStep 2401325 = 900497) (by norm_num)
theorem B3646565 : Blo 1064615 3646565 := bbase (se 4 (by rfl) ⟨341865, by rfl⟩ : syracuseStep 3646565 = 683731) (by norm_num)
theorem B2401397 : Blo 1064615 2401397 := bbase (se 5 (by rfl) ⟨112565, by rfl⟩ : syracuseStep 2401397 = 225131) (by norm_num)
theorem B5121157 : Blo 1064615 5121157 := bbase (se 4 (by rfl) ⟨480108, by rfl⟩ : syracuseStep 5121157 = 960217) (by norm_num)
theorem B1483909 : Blo 1064615 1483909 := bbase (se 4 (by rfl) ⟨139116, by rfl⟩ : syracuseStep 1483909 = 278233) (by norm_num)
theorem B4564133 : Blo 1064615 4564133 := bbase (se 4 (by rfl) ⟨427887, by rfl⟩ : syracuseStep 4564133 = 855775) (by norm_num)
theorem B2401469 : Blo 1064615 2401469 := bbase (se 3 (by rfl) ⟨450275, by rfl⟩ : syracuseStep 2401469 = 900551) (by norm_num)
theorem B2565317 : Blo 1064615 2565317 := bbase (se 4 (by rfl) ⟨240498, by rfl⟩ : syracuseStep 2565317 = 480997) (by norm_num)
theorem B2696429 : Blo 1064615 2696429 := bbase (se 3 (by rfl) ⟨505580, by rfl⟩ : syracuseStep 2696429 = 1011161) (by norm_num)
theorem B9250037 : Blo 1064615 9250037 := bbase (se 5 (by rfl) ⟨433595, by rfl⟩ : syracuseStep 9250037 = 867191) (by norm_num)
theorem B2401541 : Blo 1064615 2401541 := bbase (se 4 (by rfl) ⟨225144, by rfl⟩ : syracuseStep 2401541 = 450289) (by norm_num)
theorem B2401613 : Blo 1064615 2401613 := bbase (se 3 (by rfl) ⟨450302, by rfl⟩ : syracuseStep 2401613 = 900605) (by norm_num)
theorem B2401685 : Blo 1064615 2401685 := bbase (se 6 (by rfl) ⟨56289, by rfl⟩ : syracuseStep 2401685 = 112579) (by norm_num)
theorem B1516981 : Blo 1064615 1516981 := bbase (se 5 (by rfl) ⟨71108, by rfl⟩ : syracuseStep 1516981 = 142217) (by norm_num)
theorem B2401757 : Blo 1064615 2401757 := bbase (se 3 (by rfl) ⟨450329, by rfl⟩ : syracuseStep 2401757 = 900659) (by norm_num)
theorem B6497813 : Blo 1064615 6497813 := bbase (se 6 (by rfl) ⟨152292, by rfl⟩ : syracuseStep 6497813 = 304585) (by norm_num)
theorem B2401829 : Blo 1064615 2401829 := bbase (se 4 (by rfl) ⟨225171, by rfl⟩ : syracuseStep 2401829 = 450343) (by norm_num)
theorem B2696773 : Blo 1064615 2696773 := bbase (se 4 (by rfl) ⟨252822, by rfl⟩ : syracuseStep 2696773 = 505645) (by norm_num)
theorem B2401901 : Blo 1064615 2401901 := bbase (se 3 (by rfl) ⟨450356, by rfl⟩ : syracuseStep 2401901 = 900713) (by norm_num)
theorem B2696885 : Blo 1064615 2696885 := bbase (se 5 (by rfl) ⟨126416, by rfl⟩ : syracuseStep 2696885 = 252833) (by norm_num)
theorem B2401973 : Blo 1064615 2401973 := bbase (se 5 (by rfl) ⟨112592, by rfl⟩ : syracuseStep 2401973 = 225185) (by norm_num)
theorem B2402045 : Blo 1064615 2402045 := bbase (se 3 (by rfl) ⟨450383, by rfl⟩ : syracuseStep 2402045 = 900767) (by norm_num)
theorem B2402117 : Blo 1064615 2402117 := bbase (se 4 (by rfl) ⟨225198, by rfl⟩ : syracuseStep 2402117 = 450397) (by norm_num)
theorem B2697077 : Blo 1064615 2697077 := bbase (se 5 (by rfl) ⟨126425, by rfl⟩ : syracuseStep 2697077 = 252851) (by norm_num)
theorem B2402189 : Blo 1064615 2402189 := bbase (se 3 (by rfl) ⟨450410, by rfl⟩ : syracuseStep 2402189 = 900821) (by norm_num)
theorem B2402261 : Blo 1064615 2402261 := bbase (se 7 (by rfl) ⟨28151, by rfl⟩ : syracuseStep 2402261 = 56303) (by norm_num)
theorem B3123173 : Blo 1064615 3123173 := bbase (se 4 (by rfl) ⟨292797, by rfl⟩ : syracuseStep 3123173 = 585595) (by norm_num)
theorem B1517573 : Blo 1064615 1517573 := bbase (se 4 (by rfl) ⟨142272, by rfl⟩ : syracuseStep 1517573 = 284545) (by norm_num)
theorem B2402333 : Blo 1064615 2402333 := bbase (se 3 (by rfl) ⟨450437, by rfl⟩ : syracuseStep 2402333 = 900875) (by norm_num)
theorem B1517653 : Blo 1064615 1517653 := bbase (se 8 (by rfl) ⟨8892, by rfl⟩ : syracuseStep 1517653 = 17785) (by norm_num)
theorem B2402405 : Blo 1064615 2402405 := bbase (se 4 (by rfl) ⟨225225, by rfl⟩ : syracuseStep 2402405 = 450451) (by norm_num)
theorem B2435221 : Blo 1064615 2435221 := bbase (se 6 (by rfl) ⟨57075, by rfl⟩ : syracuseStep 2435221 = 114151) (by norm_num)
theorem B2402477 : Blo 1064615 2402477 := bbase (se 3 (by rfl) ⟨450464, by rfl⟩ : syracuseStep 2402477 = 900929) (by norm_num)
theorem B2697421 : Blo 1064615 2697421 := bbase (se 3 (by rfl) ⟨505766, by rfl⟩ : syracuseStep 2697421 = 1011533) (by norm_num)
theorem B1517773 : Blo 1064615 1517773 := bbase (se 3 (by rfl) ⟨284582, by rfl⟩ : syracuseStep 1517773 = 569165) (by norm_num)
theorem B2402549 : Blo 1064615 2402549 := bbase (se 5 (by rfl) ⟨112619, by rfl⟩ : syracuseStep 2402549 = 225239) (by norm_num)
theorem B1517869 : Blo 1064615 1517869 := bbase (se 3 (by rfl) ⟨284600, by rfl⟩ : syracuseStep 1517869 = 569201) (by norm_num)
theorem B2697533 : Blo 1064615 2697533 := bbase (se 3 (by rfl) ⟨505787, by rfl⟩ : syracuseStep 2697533 = 1011575) (by norm_num)
theorem B2402621 : Blo 1064615 2402621 := bbase (se 3 (by rfl) ⟨450491, by rfl⟩ : syracuseStep 2402621 = 900983) (by norm_num)
theorem B2402693 : Blo 1064615 2402693 := bbase (se 4 (by rfl) ⟨225252, by rfl⟩ : syracuseStep 2402693 = 450505) (by norm_num)
theorem B2402765 : Blo 1064615 2402765 := bbase (se 3 (by rfl) ⟨450518, by rfl⟩ : syracuseStep 2402765 = 901037) (by norm_num)
theorem B7678421 : Blo 1064615 7678421 := bbase (se 7 (by rfl) ⟨89981, by rfl⟩ : syracuseStep 7678421 = 179963) (by norm_num)
theorem B2697725 : Blo 1064615 2697725 := bbase (se 3 (by rfl) ⟨505823, by rfl⟩ : syracuseStep 2697725 = 1011647) (by norm_num)
theorem B12134933 : Blo 1064615 12134933 := bbase (se 6 (by rfl) ⟨284412, by rfl⟩ : syracuseStep 12134933 = 568825) (by norm_num)
theorem B6826517 : Blo 1064615 6826517 := bbase (se 6 (by rfl) ⟨159996, by rfl⟩ : syracuseStep 6826517 = 319993) (by norm_num)
theorem B2402837 : Blo 1064615 2402837 := bbase (se 6 (by rfl) ⟨56316, by rfl⟩ : syracuseStep 2402837 = 112633) (by norm_num)
theorem B4106821 : Blo 1064615 4106821 := bbase (se 4 (by rfl) ⟨385014, by rfl⟩ : syracuseStep 4106821 = 770029) (by norm_num)
theorem B2402909 : Blo 1064615 2402909 := bbase (se 3 (by rfl) ⟨450545, by rfl⟩ : syracuseStep 2402909 = 901091) (by norm_num)
theorem B2402981 : Blo 1064615 2402981 := bbase (se 4 (by rfl) ⟨225279, by rfl⟩ : syracuseStep 2402981 = 450559) (by norm_num)
theorem B2403053 : Blo 1064615 2403053 := bbase (se 3 (by rfl) ⟨450572, by rfl⟩ : syracuseStep 2403053 = 901145) (by norm_num)
theorem B1518365 : Blo 1064615 1518365 := bbase (se 3 (by rfl) ⟨284693, by rfl⟩ : syracuseStep 1518365 = 569387) (by norm_num)
theorem B2304821 : Blo 1064615 2304821 := bbase (se 5 (by rfl) ⟨108038, by rfl⟩ : syracuseStep 2304821 = 216077) (by norm_num)
theorem B2403125 : Blo 1064615 2403125 := bbase (se 5 (by rfl) ⟨112646, by rfl⟩ : syracuseStep 2403125 = 225293) (by norm_num)
theorem B3418949 : Blo 1064615 3418949 := bbase (se 4 (by rfl) ⟨320526, by rfl⟩ : syracuseStep 3418949 = 641053) (by norm_num)
theorem B2698069 : Blo 1064615 2698069 := bbase (se 9 (by rfl) ⟨7904, by rfl⟩ : syracuseStep 2698069 = 15809) (by norm_num)
theorem B2435933 : Blo 1064615 2435933 := bbase (se 3 (by rfl) ⟨456737, by rfl⟩ : syracuseStep 2435933 = 913475) (by norm_num)
theorem B2403197 : Blo 1064615 2403197 := bbase (se 3 (by rfl) ⟨450599, by rfl⟩ : syracuseStep 2403197 = 901199) (by norm_num)
theorem B2698181 : Blo 1064615 2698181 := bbase (se 4 (by rfl) ⟨252954, by rfl⟩ : syracuseStep 2698181 = 505909) (by norm_num)
theorem B2403269 : Blo 1064615 2403269 := bbase (se 4 (by rfl) ⟨225306, by rfl⟩ : syracuseStep 2403269 = 450613) (by norm_num)
theorem B5483477 : Blo 1064615 5483477 := bbase (se 7 (by rfl) ⟨64259, by rfl⟩ : syracuseStep 5483477 = 128519) (by norm_num)
theorem B2403341 : Blo 1064615 2403341 := bbase (se 3 (by rfl) ⟨450626, by rfl⟩ : syracuseStep 2403341 = 901253) (by norm_num)
theorem B2403413 : Blo 1064615 2403413 := bbase (se 8 (by rfl) ⟨14082, by rfl⟩ : syracuseStep 2403413 = 28165) (by norm_num)
theorem B2698373 : Blo 1064615 2698373 := bbase (se 4 (by rfl) ⟨252972, by rfl⟩ : syracuseStep 2698373 = 505945) (by norm_num)
theorem B2403485 : Blo 1064615 2403485 := bbase (se 3 (by rfl) ⟨450653, by rfl⟩ : syracuseStep 2403485 = 901307) (by norm_num)
theorem B1846493 : Blo 1064615 1846493 := bbase (se 3 (by rfl) ⟨346217, by rfl⟩ : syracuseStep 1846493 = 692435) (by norm_num)
theorem B1387741 : Blo 1064615 1387741 := bbase (se 3 (by rfl) ⟨260201, by rfl⟩ : syracuseStep 1387741 = 520403) (by norm_num)
theorem B2403557 : Blo 1064615 2403557 := bbase (se 4 (by rfl) ⟨225333, by rfl⟩ : syracuseStep 2403557 = 450667) (by norm_num)
theorem B2403629 : Blo 1064615 2403629 := bbase (se 3 (by rfl) ⟨450680, by rfl⟩ : syracuseStep 2403629 = 901361) (by norm_num)
theorem B1518917 : Blo 1064615 1518917 := bbase (se 4 (by rfl) ⟨142398, by rfl⟩ : syracuseStep 1518917 = 284797) (by norm_num)
theorem B2403701 : Blo 1064615 2403701 := bbase (se 5 (by rfl) ⟨112673, by rfl⟩ : syracuseStep 2403701 = 225347) (by norm_num)
theorem B2403773 : Blo 1064615 2403773 := bbase (se 3 (by rfl) ⟨450707, by rfl⟩ : syracuseStep 2403773 = 901415) (by norm_num)
theorem B2698717 : Blo 1064615 2698717 := bbase (se 3 (by rfl) ⟨506009, by rfl⟩ : syracuseStep 2698717 = 1012019) (by norm_num)
theorem B2436589 : Blo 1064615 2436589 := bbase (se 3 (by rfl) ⟨456860, by rfl⟩ : syracuseStep 2436589 = 913721) (by norm_num)
theorem B2403845 : Blo 1064615 2403845 := bbase (se 4 (by rfl) ⟨225360, by rfl⟩ : syracuseStep 2403845 = 450721) (by norm_num)
theorem B2698829 : Blo 1064615 2698829 := bbase (se 3 (by rfl) ⟨506030, by rfl⟩ : syracuseStep 2698829 = 1012061) (by norm_num)
theorem B2403917 : Blo 1064615 2403917 := bbase (se 3 (by rfl) ⟨450734, by rfl⟩ : syracuseStep 2403917 = 901469) (by norm_num)
theorem B2403989 : Blo 1064615 2403989 := bbase (se 6 (by rfl) ⟨56343, by rfl⟩ : syracuseStep 2403989 = 112687) (by norm_num)
theorem B8335061 : Blo 1064615 8335061 := bbase (se 7 (by rfl) ⟨97676, by rfl⟩ : syracuseStep 8335061 = 195353) (by norm_num)
theorem B2404061 : Blo 1064615 2404061 := bbase (se 3 (by rfl) ⟨450761, by rfl⟩ : syracuseStep 2404061 = 901523) (by norm_num)
theorem B2699021 : Blo 1064615 2699021 := bbase (se 3 (by rfl) ⟨506066, by rfl⟩ : syracuseStep 2699021 = 1012133) (by norm_num)
theorem B2404133 : Blo 1064615 2404133 := bbase (se 4 (by rfl) ⟨225387, by rfl⟩ : syracuseStep 2404133 = 450775) (by norm_num)
theorem B2404205 : Blo 1064615 2404205 := bbase (se 3 (by rfl) ⟨450788, by rfl⟩ : syracuseStep 2404205 = 901577) (by norm_num)
theorem B16396181 : Blo 1064615 16396181 := bbase (se 6 (by rfl) ⟨384285, by rfl⟩ : syracuseStep 16396181 = 768571) (by norm_num)
theorem B2404277 : Blo 1064615 2404277 := bbase (se 5 (by rfl) ⟨112700, by rfl⟩ : syracuseStep 2404277 = 225401) (by norm_num)
theorem B2404349 : Blo 1064615 2404349 := bbase (se 3 (by rfl) ⟨450815, by rfl⟩ : syracuseStep 2404349 = 901631) (by norm_num)
theorem B1519669 : Blo 1064615 1519669 := bbase (se 5 (by rfl) ⟨71234, by rfl⟩ : syracuseStep 1519669 = 142469) (by norm_num)
theorem B2699365 : Blo 1064615 2699365 := bbase (se 4 (by rfl) ⟨253065, by rfl⟩ : syracuseStep 2699365 = 506131) (by norm_num)
theorem B4108421 : Blo 1064615 4108421 := bbase (se 4 (by rfl) ⟨385164, by rfl⟩ : syracuseStep 4108421 = 770329) (by norm_num)
theorem B2699477 : Blo 1064615 2699477 := bbase (se 7 (by rfl) ⟨31634, by rfl⟩ : syracuseStep 2699477 = 63269) (by norm_num)
theorem B12955925 : Blo 1064615 12955925 := bbase (se 6 (by rfl) ⟨303654, by rfl⟩ : syracuseStep 12955925 = 607309) (by norm_num)
theorem B4043141 : Blo 1064615 4043141 := bbase (se 4 (by rfl) ⟨379044, by rfl⟩ : syracuseStep 4043141 = 758089) (by norm_num)
theorem B2699669 : Blo 1064615 2699669 := bbase (se 6 (by rfl) ⟨63273, by rfl⟩ : syracuseStep 2699669 = 126547) (by norm_num)
theorem B4043429 : Blo 1064615 4043429 := bbase (se 4 (by rfl) ⟨379071, by rfl⟩ : syracuseStep 4043429 = 758143) (by norm_num)
theorem B1094333 : Blo 1064615 1094333 := bbase (se 3 (by rfl) ⟨205187, by rfl⟩ : syracuseStep 1094333 = 410375) (by norm_num)
theorem B2700013 : Blo 1064615 2700013 := bbase (se 3 (by rfl) ⟨506252, by rfl⟩ : syracuseStep 2700013 = 1012505) (by norm_num)
theorem B1520461 : Blo 1064615 1520461 := bbase (se 3 (by rfl) ⟨285086, by rfl⟩ : syracuseStep 1520461 = 570173) (by norm_num)
theorem B2700125 : Blo 1064615 2700125 := bbase (se 3 (by rfl) ⟨506273, by rfl⟩ : syracuseStep 2700125 = 1012547) (by norm_num)
theorem B2274173 : Blo 1064615 2274173 := bbase (se 3 (by rfl) ⟨426407, by rfl⟩ : syracuseStep 2274173 = 852815) (by norm_num)
theorem B8106965 : Blo 1064615 8106965 := bbase (se 7 (by rfl) ⟨95003, by rfl⟩ : syracuseStep 8106965 = 190007) (by norm_num)
theorem B2274293 : Blo 1064615 2274293 := bbase (se 5 (by rfl) ⟨106607, by rfl⟩ : syracuseStep 2274293 = 213215) (by norm_num)
theorem B2700317 : Blo 1064615 2700317 := bbase (se 3 (by rfl) ⟨506309, by rfl⟩ : syracuseStep 2700317 = 1012619) (by norm_num)
theorem B4502645 : Blo 1064615 4502645 := bbase (se 5 (by rfl) ⟨211061, by rfl⟩ : syracuseStep 4502645 = 422123) (by norm_num)
theorem B1520797 : Blo 1064615 1520797 := bbase (se 3 (by rfl) ⟨285149, by rfl⟩ : syracuseStep 1520797 = 570299) (by norm_num)
theorem B1127689 : Blo 1064615 1127689 := bbase (se 2 (by rfl) ⟨422883, by rfl⟩ : syracuseStep 1127689 = 845767) (by norm_num)
theorem B1848685 : Blo 1064615 1848685 := bbase (se 3 (by rfl) ⟨346628, by rfl⟩ : syracuseStep 1848685 = 693257) (by norm_num)
theorem B2700661 : Blo 1064615 2700661 := bbase (se 5 (by rfl) ⟨126593, by rfl⟩ : syracuseStep 2700661 = 253187) (by norm_num)
theorem B1521013 : Blo 1064615 1521013 := bbase (se 5 (by rfl) ⟨71297, by rfl⟩ : syracuseStep 1521013 = 142595) (by norm_num)
theorem B2700773 : Blo 1064615 2700773 := bbase (se 4 (by rfl) ⟨253197, by rfl⟩ : syracuseStep 2700773 = 506395) (by norm_num)
theorem B1947205 : Blo 1064615 1947205 := bbase (se 4 (by rfl) ⟨182550, by rfl⟩ : syracuseStep 1947205 = 365101) (by norm_num)
theorem B2274925 : Blo 1064615 2274925 := bbase (se 3 (by rfl) ⟨426548, by rfl⟩ : syracuseStep 2274925 = 853097) (by norm_num)
theorem B10237589 : Blo 1064615 10237589 := bbase (se 6 (by rfl) ⟨239943, by rfl⟩ : syracuseStep 10237589 = 479887) (by norm_num)
theorem B18200213 : Blo 1064615 18200213 := bbase (se 6 (by rfl) ⟨426567, by rfl⟩ : syracuseStep 18200213 = 853135) (by norm_num)
theorem B2700965 : Blo 1064615 2700965 := bbase (se 4 (by rfl) ⟨253215, by rfl⟩ : syracuseStep 2700965 = 506431) (by norm_num)
theorem B1521389 : Blo 1064615 1521389 := bbase (se 3 (by rfl) ⟨285260, by rfl⟩ : syracuseStep 1521389 = 570521) (by norm_num)
theorem B8664853 : Blo 1064615 8664853 := bbase (se 6 (by rfl) ⟨203082, by rfl⟩ : syracuseStep 8664853 = 406165) (by norm_num)
theorem B4044613 : Blo 1064615 4044613 := bbase (se 4 (by rfl) ⟨379182, by rfl⟩ : syracuseStep 4044613 = 758365) (by norm_num)
theorem B3422101 : Blo 1064615 3422101 := bbase (se 6 (by rfl) ⟨80205, by rfl⟩ : syracuseStep 3422101 = 160411) (by norm_num)
theorem B4437925 : Blo 1064615 4437925 := bbase (se 4 (by rfl) ⟨416055, by rfl⟩ : syracuseStep 4437925 = 832111) (by norm_num)
theorem B2734013 : Blo 1064615 2734013 := bbase (se 3 (by rfl) ⟨512627, by rfl⟩ : syracuseStep 2734013 = 1025255) (by norm_num)
theorem B2701309 : Blo 1064615 2701309 := bbase (se 3 (by rfl) ⟨506495, by rfl⟩ : syracuseStep 2701309 = 1012991) (by norm_num)
theorem B1619989 : Blo 1064615 1619989 := bbase (se 6 (by rfl) ⟨37968, by rfl⟩ : syracuseStep 1619989 = 75937) (by norm_num)
theorem B1095773 : Blo 1064615 1095773 := bbase (se 3 (by rfl) ⟨205457, by rfl⟩ : syracuseStep 1095773 = 410915) (by norm_num)
theorem B2701421 : Blo 1064615 2701421 := bbase (se 3 (by rfl) ⟨506516, by rfl⟩ : syracuseStep 2701421 = 1013033) (by norm_num)
theorem B4044917 : Blo 1064615 4044917 := bbase (se 5 (by rfl) ⟨189605, by rfl⟩ : syracuseStep 4044917 = 379211) (by norm_num)
theorem B2701613 : Blo 1064615 2701613 := bbase (se 3 (by rfl) ⟨506552, by rfl⟩ : syracuseStep 2701613 = 1013105) (by norm_num)
theorem B3848597 : Blo 1064615 3848597 := bbase (se 6 (by rfl) ⟨90201, by rfl⟩ : syracuseStep 3848597 = 180403) (by norm_num)
theorem B6076853 : Blo 1064615 6076853 := bbase (se 5 (by rfl) ⟨284852, by rfl⟩ : syracuseStep 6076853 = 569705) (by norm_num)
theorem B2275813 : Blo 1064615 2275813 := bbase (se 4 (by rfl) ⟨213357, by rfl⟩ : syracuseStep 2275813 = 426715) (by norm_num)
theorem B3848741 : Blo 1064615 3848741 := bbase (se 4 (by rfl) ⟨360819, by rfl⟩ : syracuseStep 3848741 = 721639) (by norm_num)
theorem B2734669 : Blo 1064615 2734669 := bbase (se 3 (by rfl) ⟨512750, by rfl⟩ : syracuseStep 2734669 = 1025501) (by norm_num)
theorem B2275933 : Blo 1064615 2275933 := bbase (se 3 (by rfl) ⟨426737, by rfl⟩ : syracuseStep 2275933 = 853475) (by norm_num)
theorem B2701957 : Blo 1064615 2701957 := bbase (se 4 (by rfl) ⟨253308, by rfl⟩ : syracuseStep 2701957 = 506617) (by norm_num)
theorem B2702069 : Blo 1064615 2702069 := bbase (se 5 (by rfl) ⟨126659, by rfl⟩ : syracuseStep 2702069 = 253319) (by norm_num)
theorem B2276189 : Blo 1064615 2276189 := bbase (se 3 (by rfl) ⟨426785, by rfl⟩ : syracuseStep 2276189 = 853571) (by norm_num)
theorem B4111253 : Blo 1064615 4111253 := bbase (se 6 (by rfl) ⟨96357, by rfl⟩ : syracuseStep 4111253 = 192715) (by norm_num)
theorem B2702261 : Blo 1064615 2702261 := bbase (se 5 (by rfl) ⟨126668, by rfl⟩ : syracuseStep 2702261 = 253337) (by norm_num)
theorem B1850485 : Blo 1064615 1850485 := bbase (se 5 (by rfl) ⟨86741, by rfl⟩ : syracuseStep 1850485 = 173483) (by norm_num)
theorem B1621181 : Blo 1064615 1621181 := bbase (se 3 (by rfl) ⟨303971, by rfl⟩ : syracuseStep 1621181 = 607943) (by norm_num)
theorem B2702605 : Blo 1064615 2702605 := bbase (se 3 (by rfl) ⟨506738, by rfl⟩ : syracuseStep 2702605 = 1013477) (by norm_num)
theorem B2702717 : Blo 1064615 2702717 := bbase (se 3 (by rfl) ⟨506759, by rfl⟩ : syracuseStep 2702717 = 1013519) (by norm_num)
theorem B2702909 : Blo 1064615 2702909 := bbase (se 3 (by rfl) ⟨506795, by rfl⟩ : syracuseStep 2702909 = 1013591) (by norm_num)
theorem B6078037 : Blo 1064615 6078037 := bbase (se 8 (by rfl) ⟨35613, by rfl⟩ : syracuseStep 6078037 = 71227) (by norm_num)
theorem B2277077 : Blo 1064615 2277077 := bbase (se 7 (by rfl) ⟨26684, by rfl⟩ : syracuseStep 2277077 = 53369) (by norm_num)
theorem B5128037 : Blo 1064615 5128037 := bbase (se 4 (by rfl) ⟨480753, by rfl⟩ : syracuseStep 5128037 = 961507) (by norm_num)
theorem B2703253 : Blo 1064615 2703253 := bbase (se 6 (by rfl) ⟨63357, by rfl⟩ : syracuseStep 2703253 = 126715) (by norm_num)
theorem B2277317 : Blo 1064615 2277317 := bbase (se 4 (by rfl) ⟨213498, by rfl⟩ : syracuseStep 2277317 = 426997) (by norm_num)
theorem B2703365 : Blo 1064615 2703365 := bbase (se 4 (by rfl) ⟨253440, by rfl⟩ : syracuseStep 2703365 = 506881) (by norm_num)
theorem B1622101 : Blo 1064615 1622101 := bbase (se 8 (by rfl) ⟨9504, by rfl⟩ : syracuseStep 1622101 = 19009) (by norm_num)
theorem B4047029 : Blo 1064615 4047029 := bbase (se 5 (by rfl) ⟨189704, by rfl⟩ : syracuseStep 4047029 = 379409) (by norm_num)
theorem B6832309 : Blo 1064615 6832309 := bbase (se 5 (by rfl) ⟨320264, by rfl⟩ : syracuseStep 6832309 = 640529) (by norm_num)
theorem B2703557 : Blo 1064615 2703557 := bbase (se 4 (by rfl) ⟨253458, by rfl⟩ : syracuseStep 2703557 = 506917) (by norm_num)
theorem B5390549 : Blo 1064615 5390549 := bbase (se 7 (by rfl) ⟨63170, by rfl⟩ : syracuseStep 5390549 = 126341) (by norm_num)
theorem B8536277 : Blo 1064615 8536277 := bbase (se 7 (by rfl) ⟨100034, by rfl⟩ : syracuseStep 8536277 = 200069) (by norm_num)
theorem B2277821 : Blo 1064615 2277821 := bbase (se 3 (by rfl) ⟨427091, by rfl⟩ : syracuseStep 2277821 = 854183) (by norm_num)
theorem B2277829 : Blo 1064615 2277829 := bbase (se 4 (by rfl) ⟨213546, by rfl⟩ : syracuseStep 2277829 = 427093) (by norm_num)
theorem B4047317 : Blo 1064615 4047317 := bbase (se 7 (by rfl) ⟨47429, by rfl⟩ : syracuseStep 4047317 = 94859) (by norm_num)
theorem B1851869 : Blo 1064615 1851869 := bbase (se 3 (by rfl) ⟨347225, by rfl⟩ : syracuseStep 1851869 = 694451) (by norm_num)
theorem B3850757 : Blo 1064615 3850757 := bbase (se 4 (by rfl) ⟨361008, by rfl⟩ : syracuseStep 3850757 = 722017) (by norm_num)
theorem B2703901 : Blo 1064615 2703901 := bbase (se 3 (by rfl) ⟨506981, by rfl⟩ : syracuseStep 2703901 = 1013963) (by norm_num)
theorem B2704013 : Blo 1064615 2704013 := bbase (se 3 (by rfl) ⟨507002, by rfl⟩ : syracuseStep 2704013 = 1014005) (by norm_num)
theorem B2704205 : Blo 1064615 2704205 := bbase (se 3 (by rfl) ⟨507038, by rfl⟩ : syracuseStep 2704205 = 1014077) (by norm_num)
theorem B2311021 : Blo 1064615 2311021 := bbase (se 3 (by rfl) ⟨433316, by rfl⟩ : syracuseStep 2311021 = 866633) (by norm_num)
theorem B14599061 : Blo 1064615 14599061 := bbase (se 6 (by rfl) ⟨342165, by rfl⟩ : syracuseStep 14599061 = 684331) (by norm_num)
theorem B3032117 : Blo 1064615 3032117 := bbase (se 5 (by rfl) ⟨142130, by rfl⟩ : syracuseStep 3032117 = 284261) (by norm_num)
theorem B2704549 : Blo 1064615 2704549 := bbase (se 4 (by rfl) ⟨253551, by rfl⟩ : syracuseStep 2704549 = 507103) (by norm_num)
theorem B2704661 : Blo 1064615 2704661 := bbase (se 6 (by rfl) ⟨63390, by rfl⟩ : syracuseStep 2704661 = 126781) (by norm_num)
theorem B1623493 : Blo 1064615 1623493 := bbase (se 4 (by rfl) ⟨152202, by rfl⟩ : syracuseStep 1623493 = 304405) (by norm_num)
theorem B2704853 : Blo 1064615 2704853 := bbase (se 7 (by rfl) ⟨31697, by rfl⟩ : syracuseStep 2704853 = 63395) (by norm_num)
theorem B3032549 : Blo 1064615 3032549 := bbase (se 4 (by rfl) ⟨284301, by rfl⟩ : syracuseStep 3032549 = 568603) (by norm_num)
theorem B5391845 : Blo 1064615 5391845 := bbase (se 4 (by rfl) ⟨505485, by rfl⟩ : syracuseStep 5391845 = 1010971) (by norm_num)
theorem B6080021 : Blo 1064615 6080021 := bbase (se 6 (by rfl) ⟨142500, by rfl⟩ : syracuseStep 6080021 = 285001) (by norm_num)
theorem B2278957 : Blo 1064615 2278957 := bbase (se 3 (by rfl) ⟨427304, by rfl⟩ : syracuseStep 2278957 = 854609) (by norm_num)
theorem B26297941 : Blo 1064615 26297941 := bbase (se 8 (by rfl) ⟨154089, by rfl⟩ : syracuseStep 26297941 = 308179) (by norm_num)
theorem B4048501 : Blo 1064615 4048501 := bbase (se 5 (by rfl) ⟨189773, by rfl⟩ : syracuseStep 4048501 = 379547) (by norm_num)
theorem B1197697 : Blo 1064615 1197697 := bbase (se 2 (by rfl) ⟨449136, by rfl⟩ : syracuseStep 1197697 = 898273) (by norm_num)
theorem B1197733 : Blo 1064615 1197733 := bbase (se 4 (by rfl) ⟨112287, by rfl⟩ : syracuseStep 1197733 = 224575) (by norm_num)
theorem B1197769 : Blo 1064615 1197769 := bbase (se 2 (by rfl) ⟨449163, by rfl⟩ : syracuseStep 1197769 = 898327) (by norm_num)
theorem B1197805 : Blo 1064615 1197805 := bbase (se 3 (by rfl) ⟨224588, by rfl⟩ : syracuseStep 1197805 = 449177) (by norm_num)
theorem B1197841 : Blo 1064615 1197841 := bbase (se 2 (by rfl) ⟨449190, by rfl⟩ : syracuseStep 1197841 = 898381) (by norm_num)
theorem B1197877 : Blo 1064615 1197877 := bbase (se 5 (by rfl) ⟨56150, by rfl⟩ : syracuseStep 1197877 = 112301) (by norm_num)
theorem B1197913 : Blo 1064615 1197913 := bbase (se 2 (by rfl) ⟨449217, by rfl⟩ : syracuseStep 1197913 = 898435) (by norm_num)
theorem B1197949 : Blo 1064615 1197949 := bbase (se 3 (by rfl) ⟨224615, by rfl⟩ : syracuseStep 1197949 = 449231) (by norm_num)
theorem B1197985 : Blo 1064615 1197985 := bbase (se 2 (by rfl) ⟨449244, by rfl⟩ : syracuseStep 1197985 = 898489) (by norm_num)
theorem B4048805 : Blo 1064615 4048805 := bbase (se 4 (by rfl) ⟨379575, by rfl⟩ : syracuseStep 4048805 = 759151) (by norm_num)
theorem B2279333 : Blo 1064615 2279333 := bbase (se 4 (by rfl) ⟨213687, by rfl⟩ : syracuseStep 2279333 = 427375) (by norm_num)
theorem B1198021 : Blo 1064615 1198021 := bbase (se 4 (by rfl) ⟨112314, by rfl⟩ : syracuseStep 1198021 = 224629) (by norm_num)
theorem B1198057 : Blo 1064615 1198057 := bbase (se 2 (by rfl) ⟨449271, by rfl⟩ : syracuseStep 1198057 = 898543) (by norm_num)
theorem B1198093 : Blo 1064615 1198093 := bbase (se 3 (by rfl) ⟨224642, by rfl⟩ : syracuseStep 1198093 = 449285) (by norm_num)
theorem B1198129 : Blo 1064615 1198129 := bbase (se 2 (by rfl) ⟨449298, by rfl⟩ : syracuseStep 1198129 = 898597) (by norm_num)
theorem B1198165 : Blo 1064615 1198165 := bbase (se 8 (by rfl) ⟨7020, by rfl⟩ : syracuseStep 1198165 = 14041) (by norm_num)
theorem B1198201 : Blo 1064615 1198201 := bbase (se 2 (by rfl) ⟨449325, by rfl⟩ : syracuseStep 1198201 = 898651) (by norm_num)
theorem B1198237 : Blo 1064615 1198237 := bbase (se 3 (by rfl) ⟨224669, by rfl⟩ : syracuseStep 1198237 = 449339) (by norm_num)
theorem B1231033 : Blo 1064615 1231033 := bbase (se 2 (by rfl) ⟨461637, by rfl⟩ : syracuseStep 1231033 = 923275) (by norm_num)
theorem B1198273 : Blo 1064615 1198273 := bbase (se 2 (by rfl) ⟨449352, by rfl⟩ : syracuseStep 1198273 = 898705) (by norm_num)
theorem B3033301 : Blo 1064615 3033301 := bbase (se 7 (by rfl) ⟨35546, by rfl⟩ : syracuseStep 3033301 = 71093) (by norm_num)
theorem B1198309 : Blo 1064615 1198309 := bbase (se 4 (by rfl) ⟨112341, by rfl⟩ : syracuseStep 1198309 = 224683) (by norm_num)
theorem B1198345 : Blo 1064615 1198345 := bbase (se 2 (by rfl) ⟨449379, by rfl⟩ : syracuseStep 1198345 = 898759) (by norm_num)
theorem B13682965 : Blo 1064615 13682965 := bbase (se 6 (by rfl) ⟨320694, by rfl⟩ : syracuseStep 13682965 = 641389) (by norm_num)
theorem B1198381 : Blo 1064615 1198381 := bbase (se 3 (by rfl) ⟨224696, by rfl⟩ : syracuseStep 1198381 = 449393) (by norm_num)
theorem B1198417 : Blo 1064615 1198417 := bbase (se 2 (by rfl) ⟨449406, by rfl⟩ : syracuseStep 1198417 = 898813) (by norm_num)
theorem B10242389 : Blo 1064615 10242389 := bbase (se 10 (by rfl) ⟨15003, by rfl⟩ : syracuseStep 10242389 = 30007) (by norm_num)
theorem B1198453 : Blo 1064615 1198453 := bbase (se 5 (by rfl) ⟨56177, by rfl⟩ : syracuseStep 1198453 = 112355) (by norm_num)
theorem B2738557 : Blo 1064615 2738557 := bbase (se 3 (by rfl) ⟨513479, by rfl⟩ : syracuseStep 2738557 = 1026959) (by norm_num)
theorem B1919381 : Blo 1064615 1919381 := bbase (se 6 (by rfl) ⟨44985, by rfl⟩ : syracuseStep 1919381 = 89971) (by norm_num)
theorem B1198489 : Blo 1064615 1198489 := bbase (se 2 (by rfl) ⟨449433, by rfl⟩ : syracuseStep 1198489 = 898867) (by norm_num)
theorem B1198525 : Blo 1064615 1198525 := bbase (se 3 (by rfl) ⟨224723, by rfl⟩ : syracuseStep 1198525 = 449447) (by norm_num)
theorem B1198561 : Blo 1064615 1198561 := bbase (se 2 (by rfl) ⟨449460, by rfl⟩ : syracuseStep 1198561 = 898921) (by norm_num)
theorem B1198597 : Blo 1064615 1198597 := bbase (se 4 (by rfl) ⟨112368, by rfl⟩ : syracuseStep 1198597 = 224737) (by norm_num)
theorem B1198633 : Blo 1064615 1198633 := bbase (se 2 (by rfl) ⟨449487, by rfl⟩ : syracuseStep 1198633 = 898975) (by norm_num)
theorem B5130805 : Blo 1064615 5130805 := bbase (se 5 (by rfl) ⟨240506, by rfl⟩ : syracuseStep 5130805 = 481013) (by norm_num)
theorem B1198669 : Blo 1064615 1198669 := bbase (se 3 (by rfl) ⟨224750, by rfl⟩ : syracuseStep 1198669 = 449501) (by norm_num)
theorem B1198705 : Blo 1064615 1198705 := bbase (se 2 (by rfl) ⟨449514, by rfl⟩ : syracuseStep 1198705 = 899029) (by norm_num)
theorem B1198741 : Blo 1064615 1198741 := bbase (se 6 (by rfl) ⟨28095, by rfl⟩ : syracuseStep 1198741 = 56191) (by norm_num)
theorem B1198777 : Blo 1064615 1198777 := bbase (se 2 (by rfl) ⟨449541, by rfl⟩ : syracuseStep 1198777 = 899083) (by norm_num)
theorem B1198813 : Blo 1064615 1198813 := bbase (se 3 (by rfl) ⟨224777, by rfl⟩ : syracuseStep 1198813 = 449555) (by norm_num)
theorem B5393141 : Blo 1064615 5393141 := bbase (se 5 (by rfl) ⟨252803, by rfl⟩ : syracuseStep 5393141 = 505607) (by norm_num)
theorem B1198849 : Blo 1064615 1198849 := bbase (se 2 (by rfl) ⟨449568, by rfl⟩ : syracuseStep 1198849 = 899137) (by norm_num)
theorem B1198885 : Blo 1064615 1198885 := bbase (se 4 (by rfl) ⟨112395, by rfl⟩ : syracuseStep 1198885 = 224791) (by norm_num)
theorem B1198921 : Blo 1064615 1198921 := bbase (se 2 (by rfl) ⟨449595, by rfl⟩ : syracuseStep 1198921 = 899191) (by norm_num)
theorem B1919837 : Blo 1064615 1919837 := bbase (se 3 (by rfl) ⟨359969, by rfl⟩ : syracuseStep 1919837 = 719939) (by norm_num)
theorem B1198957 : Blo 1064615 1198957 := bbase (se 3 (by rfl) ⟨224804, by rfl⟩ : syracuseStep 1198957 = 449609) (by norm_num)
theorem B1198993 : Blo 1064615 1198993 := bbase (se 2 (by rfl) ⟨449622, by rfl⟩ : syracuseStep 1198993 = 899245) (by norm_num)
theorem B1199029 : Blo 1064615 1199029 := bbase (se 5 (by rfl) ⟨56204, by rfl⟩ : syracuseStep 1199029 = 112409) (by norm_num)
theorem B1199065 : Blo 1064615 1199065 := bbase (se 2 (by rfl) ⟨449649, by rfl⟩ : syracuseStep 1199065 = 899299) (by norm_num)
theorem B1199101 : Blo 1064615 1199101 := bbase (se 3 (by rfl) ⟨224831, by rfl⟩ : syracuseStep 1199101 = 449663) (by norm_num)
theorem B12471317 : Blo 1064615 12471317 := bbase (se 6 (by rfl) ⟨292296, by rfl⟩ : syracuseStep 12471317 = 584593) (by norm_num)
theorem B1199137 : Blo 1064615 1199137 := bbase (se 2 (by rfl) ⟨449676, by rfl⟩ : syracuseStep 1199137 = 899353) (by norm_num)
theorem B1199173 : Blo 1064615 1199173 := bbase (se 4 (by rfl) ⟨112422, by rfl⟩ : syracuseStep 1199173 = 224845) (by norm_num)
theorem B1199209 : Blo 1064615 1199209 := bbase (se 2 (by rfl) ⟨449703, by rfl⟩ : syracuseStep 1199209 = 899407) (by norm_num)
theorem B1232005 : Blo 1064615 1232005 := bbase (se 4 (by rfl) ⟨115500, by rfl⟩ : syracuseStep 1232005 = 231001) (by norm_num)
theorem B1199245 : Blo 1064615 1199245 := bbase (se 3 (by rfl) ⟨224858, by rfl⟩ : syracuseStep 1199245 = 449717) (by norm_num)
theorem B1199281 : Blo 1064615 1199281 := bbase (se 2 (by rfl) ⟨449730, by rfl⟩ : syracuseStep 1199281 = 899461) (by norm_num)
theorem B1199317 : Blo 1064615 1199317 := bbase (se 7 (by rfl) ⟨14054, by rfl⟩ : syracuseStep 1199317 = 28109) (by norm_num)
theorem B1199353 : Blo 1064615 1199353 := bbase (se 2 (by rfl) ⟨449757, by rfl⟩ : syracuseStep 1199353 = 899515) (by norm_num)
theorem B1199389 : Blo 1064615 1199389 := bbase (se 3 (by rfl) ⟨224885, by rfl⟩ : syracuseStep 1199389 = 449771) (by norm_num)
theorem B1199425 : Blo 1064615 1199425 := bbase (se 2 (by rfl) ⟨449784, by rfl⟩ : syracuseStep 1199425 = 899569) (by norm_num)
theorem B1199461 : Blo 1064615 1199461 := bbase (se 4 (by rfl) ⟨112449, by rfl⟩ : syracuseStep 1199461 = 224899) (by norm_num)
theorem B1199497 : Blo 1064615 1199497 := bbase (se 2 (by rfl) ⟨449811, by rfl⟩ : syracuseStep 1199497 = 899623) (by norm_num)
theorem B1199533 : Blo 1064615 1199533 := bbase (se 3 (by rfl) ⟨224912, by rfl⟩ : syracuseStep 1199533 = 449825) (by norm_num)
theorem B1199569 : Blo 1064615 1199569 := bbase (se 2 (by rfl) ⟨449838, by rfl⟩ : syracuseStep 1199569 = 899677) (by norm_num)
theorem B1199605 : Blo 1064615 1199605 := bbase (se 5 (by rfl) ⟨56231, by rfl⟩ : syracuseStep 1199605 = 112463) (by norm_num)
theorem B2280973 : Blo 1064615 2280973 := bbase (se 3 (by rfl) ⟨427682, by rfl⟩ : syracuseStep 2280973 = 855365) (by norm_num)
theorem B1199641 : Blo 1064615 1199641 := bbase (se 2 (by rfl) ⟨449865, by rfl⟩ : syracuseStep 1199641 = 899731) (by norm_num)
theorem B1199677 : Blo 1064615 1199677 := bbase (se 3 (by rfl) ⟨224939, by rfl⟩ : syracuseStep 1199677 = 449879) (by norm_num)
theorem B1199713 : Blo 1064615 1199713 := bbase (se 2 (by rfl) ⟨449892, by rfl⟩ : syracuseStep 1199713 = 899785) (by norm_num)
theorem B1199749 : Blo 1064615 1199749 := bbase (se 4 (by rfl) ⟨112476, by rfl⟩ : syracuseStep 1199749 = 224953) (by norm_num)
theorem B1199785 : Blo 1064615 1199785 := bbase (se 2 (by rfl) ⟨449919, by rfl⟩ : syracuseStep 1199785 = 899839) (by norm_num)
theorem B6082229 : Blo 1064615 6082229 := bbase (se 5 (by rfl) ⟨285104, by rfl⟩ : syracuseStep 6082229 = 570209) (by norm_num)
theorem B1199821 : Blo 1064615 1199821 := bbase (se 3 (by rfl) ⟨224966, by rfl⟩ : syracuseStep 1199821 = 449933) (by norm_num)
theorem B1199857 : Blo 1064615 1199857 := bbase (se 2 (by rfl) ⟨449946, by rfl⟩ : syracuseStep 1199857 = 899893) (by norm_num)
theorem B1199893 : Blo 1064615 1199893 := bbase (se 6 (by rfl) ⟨28122, by rfl⟩ : syracuseStep 1199893 = 56245) (by norm_num)
theorem B1199929 : Blo 1064615 1199929 := bbase (se 2 (by rfl) ⟨449973, by rfl⟩ : syracuseStep 1199929 = 899947) (by norm_num)
theorem B1199965 : Blo 1064615 1199965 := bbase (se 3 (by rfl) ⟨224993, by rfl⟩ : syracuseStep 1199965 = 449987) (by norm_num)
theorem B1200001 : Blo 1064615 1200001 := bbase (se 2 (by rfl) ⟨450000, by rfl⟩ : syracuseStep 1200001 = 900001) (by norm_num)
theorem B1200037 : Blo 1064615 1200037 := bbase (se 4 (by rfl) ⟨112503, by rfl⟩ : syracuseStep 1200037 = 225007) (by norm_num)
theorem B1200073 : Blo 1064615 1200073 := bbase (se 2 (by rfl) ⟨450027, by rfl⟩ : syracuseStep 1200073 = 900055) (by norm_num)
theorem B4050917 : Blo 1064615 4050917 := bbase (se 4 (by rfl) ⟨379773, by rfl⟩ : syracuseStep 4050917 = 759547) (by norm_num)
theorem B1200109 : Blo 1064615 1200109 := bbase (se 3 (by rfl) ⟨225020, by rfl⟩ : syracuseStep 1200109 = 450041) (by norm_num)
theorem B5394437 : Blo 1064615 5394437 := bbase (se 4 (by rfl) ⟨505728, by rfl⟩ : syracuseStep 5394437 = 1011457) (by norm_num)
theorem B1200145 : Blo 1064615 1200145 := bbase (se 2 (by rfl) ⟨450054, by rfl⟩ : syracuseStep 1200145 = 900109) (by norm_num)
theorem B1200181 : Blo 1064615 1200181 := bbase (se 5 (by rfl) ⟨56258, by rfl⟩ : syracuseStep 1200181 = 112517) (by norm_num)
theorem B1200217 : Blo 1064615 1200217 := bbase (se 2 (by rfl) ⟨450081, by rfl⟩ : syracuseStep 1200217 = 900163) (by norm_num)
theorem B1200253 : Blo 1064615 1200253 := bbase (se 3 (by rfl) ⟨225047, by rfl⟩ : syracuseStep 1200253 = 450095) (by norm_num)
theorem B1200289 : Blo 1064615 1200289 := bbase (se 2 (by rfl) ⟨450108, by rfl⟩ : syracuseStep 1200289 = 900217) (by norm_num)
theorem B1298605 : Blo 1064615 1298605 := bbase (se 3 (by rfl) ⟨243488, by rfl⟩ : syracuseStep 1298605 = 486977) (by norm_num)
theorem B1200325 : Blo 1064615 1200325 := bbase (se 4 (by rfl) ⟨112530, by rfl⟩ : syracuseStep 1200325 = 225061) (by norm_num)
theorem B1200361 : Blo 1064615 1200361 := bbase (se 2 (by rfl) ⟨450135, by rfl⟩ : syracuseStep 1200361 = 900271) (by norm_num)
theorem B4051205 : Blo 1064615 4051205 := bbase (se 4 (by rfl) ⟨379800, by rfl⟩ : syracuseStep 4051205 = 759601) (by norm_num)
theorem B1200397 : Blo 1064615 1200397 := bbase (se 3 (by rfl) ⟨225074, by rfl⟩ : syracuseStep 1200397 = 450149) (by norm_num)
theorem B1200433 : Blo 1064615 1200433 := bbase (se 2 (by rfl) ⟨450162, by rfl⟩ : syracuseStep 1200433 = 900325) (by norm_num)
theorem B1921357 : Blo 1064615 1921357 := bbase (se 3 (by rfl) ⟨360254, by rfl⟩ : syracuseStep 1921357 = 720509) (by norm_num)
theorem B1200469 : Blo 1064615 1200469 := bbase (se 10 (by rfl) ⟨1758, by rfl⟩ : syracuseStep 1200469 = 3517) (by norm_num)
theorem B1200505 : Blo 1064615 1200505 := bbase (se 2 (by rfl) ⟨450189, by rfl⟩ : syracuseStep 1200505 = 900379) (by norm_num)
theorem B2281861 : Blo 1064615 2281861 := bbase (se 4 (by rfl) ⟨213924, by rfl⟩ : syracuseStep 2281861 = 427849) (by norm_num)
theorem B1200541 : Blo 1064615 1200541 := bbase (se 3 (by rfl) ⟨225101, by rfl⟩ : syracuseStep 1200541 = 450203) (by norm_num)
theorem B1200577 : Blo 1064615 1200577 := bbase (se 2 (by rfl) ⟨450216, by rfl⟩ : syracuseStep 1200577 = 900433) (by norm_num)
theorem B1200613 : Blo 1064615 1200613 := bbase (se 4 (by rfl) ⟨112557, by rfl⟩ : syracuseStep 1200613 = 225115) (by norm_num)
theorem B1200649 : Blo 1064615 1200649 := bbase (se 2 (by rfl) ⟨450243, by rfl⟩ : syracuseStep 1200649 = 900487) (by norm_num)
theorem B1200685 : Blo 1064615 1200685 := bbase (se 3 (by rfl) ⟨225128, by rfl⟩ : syracuseStep 1200685 = 450257) (by norm_num)
theorem B8114741 : Blo 1064615 8114741 := bbase (se 5 (by rfl) ⟨380378, by rfl⟩ : syracuseStep 8114741 = 760757) (by norm_num)
theorem B1200721 : Blo 1064615 1200721 := bbase (se 2 (by rfl) ⟨450270, by rfl⟩ : syracuseStep 1200721 = 900541) (by norm_num)
theorem B1200757 : Blo 1064615 1200757 := bbase (se 5 (by rfl) ⟨56285, by rfl⟩ : syracuseStep 1200757 = 112571) (by norm_num)
theorem B1200793 : Blo 1064615 1200793 := bbase (se 2 (by rfl) ⟨450297, by rfl⟩ : syracuseStep 1200793 = 900595) (by norm_num)
theorem B1200829 : Blo 1064615 1200829 := bbase (se 3 (by rfl) ⟨225155, by rfl⟩ : syracuseStep 1200829 = 450311) (by norm_num)
theorem B1200865 : Blo 1064615 1200865 := bbase (se 2 (by rfl) ⟨450324, by rfl⟩ : syracuseStep 1200865 = 900649) (by norm_num)
theorem B5755637 : Blo 1064615 5755637 := bbase (se 5 (by rfl) ⟨269795, by rfl⟩ : syracuseStep 5755637 = 539591) (by norm_num)
theorem B1200901 : Blo 1064615 1200901 := bbase (se 4 (by rfl) ⟨112584, by rfl⟩ : syracuseStep 1200901 = 225169) (by norm_num)
theorem B1200937 : Blo 1064615 1200937 := bbase (se 2 (by rfl) ⟨450351, by rfl⟩ : syracuseStep 1200937 = 900703) (by norm_num)
theorem B1200973 : Blo 1064615 1200973 := bbase (se 3 (by rfl) ⟨225182, by rfl⟩ : syracuseStep 1200973 = 450365) (by norm_num)
theorem B1201009 : Blo 1064615 1201009 := bbase (se 2 (by rfl) ⟨450378, by rfl⟩ : syracuseStep 1201009 = 900757) (by norm_num)
theorem B1299341 : Blo 1064615 1299341 := bbase (se 3 (by rfl) ⟨243626, by rfl⟩ : syracuseStep 1299341 = 487253) (by norm_num)
theorem B1201045 : Blo 1064615 1201045 := bbase (se 6 (by rfl) ⟨28149, by rfl⟩ : syracuseStep 1201045 = 56299) (by norm_num)
theorem B1201081 : Blo 1064615 1201081 := bbase (se 2 (by rfl) ⟨450405, by rfl⟩ : syracuseStep 1201081 = 900811) (by norm_num)
theorem B1201117 : Blo 1064615 1201117 := bbase (se 3 (by rfl) ⟨225209, by rfl⟩ : syracuseStep 1201117 = 450419) (by norm_num)
theorem B3036149 : Blo 1064615 3036149 := bbase (se 5 (by rfl) ⟨142319, by rfl⟩ : syracuseStep 3036149 = 284639) (by norm_num)
theorem B1201153 : Blo 1064615 1201153 := bbase (se 2 (by rfl) ⟨450432, by rfl⟩ : syracuseStep 1201153 = 900865) (by norm_num)
theorem B1201189 : Blo 1064615 1201189 := bbase (se 4 (by rfl) ⟨112611, by rfl⟩ : syracuseStep 1201189 = 225223) (by norm_num)
theorem B1201225 : Blo 1064615 1201225 := bbase (se 2 (by rfl) ⟨450459, by rfl⟩ : syracuseStep 1201225 = 900919) (by norm_num)
theorem B1922149 : Blo 1064615 1922149 := bbase (se 4 (by rfl) ⟨180201, by rfl⟩ : syracuseStep 1922149 = 360403) (by norm_num)
theorem B1201261 : Blo 1064615 1201261 := bbase (se 3 (by rfl) ⟨225236, by rfl⟩ : syracuseStep 1201261 = 450473) (by norm_num)
theorem B1201297 : Blo 1064615 1201297 := bbase (se 2 (by rfl) ⟨450486, by rfl⟩ : syracuseStep 1201297 = 900973) (by norm_num)
theorem B1201333 : Blo 1064615 1201333 := bbase (se 5 (by rfl) ⟨56312, by rfl⟩ : syracuseStep 1201333 = 112625) (by norm_num)
theorem B3593429 : Blo 1064615 3593429 := bbase (se 7 (by rfl) ⟨42110, by rfl⟩ : syracuseStep 3593429 = 84221) (by norm_num)
theorem B1201369 : Blo 1064615 1201369 := bbase (se 2 (by rfl) ⟨450513, by rfl⟩ : syracuseStep 1201369 = 901027) (by norm_num)
theorem B5133557 : Blo 1064615 5133557 := bbase (se 5 (by rfl) ⟨240635, by rfl⟩ : syracuseStep 5133557 = 481271) (by norm_num)
theorem B1201405 : Blo 1064615 1201405 := bbase (se 3 (by rfl) ⟨225263, by rfl⟩ : syracuseStep 1201405 = 450527) (by norm_num)
theorem B5395733 : Blo 1064615 5395733 := bbase (se 6 (by rfl) ⟨126462, by rfl⟩ : syracuseStep 5395733 = 252925) (by norm_num)
theorem B1201441 : Blo 1064615 1201441 := bbase (se 2 (by rfl) ⟨450540, by rfl⟩ : syracuseStep 1201441 = 901081) (by norm_num)
theorem B1201477 : Blo 1064615 1201477 := bbase (se 4 (by rfl) ⟨112638, by rfl⟩ : syracuseStep 1201477 = 225277) (by norm_num)
theorem B1201513 : Blo 1064615 1201513 := bbase (se 2 (by rfl) ⟨450567, by rfl⟩ : syracuseStep 1201513 = 901135) (by norm_num)
theorem B1201549 : Blo 1064615 1201549 := bbase (se 3 (by rfl) ⟨225290, by rfl⟩ : syracuseStep 1201549 = 450581) (by norm_num)
theorem B4052389 : Blo 1064615 4052389 := bbase (se 4 (by rfl) ⟨379911, by rfl⟩ : syracuseStep 4052389 = 759823) (by norm_num)
theorem B1201585 : Blo 1064615 1201585 := bbase (se 2 (by rfl) ⟨450594, by rfl⟩ : syracuseStep 1201585 = 901189) (by norm_num)
theorem B1201621 : Blo 1064615 1201621 := bbase (se 7 (by rfl) ⟨14081, by rfl⟩ : syracuseStep 1201621 = 28163) (by norm_num)
theorem B1922525 : Blo 1064615 1922525 := bbase (se 3 (by rfl) ⟨360473, by rfl⟩ : syracuseStep 1922525 = 720947) (by norm_num)
theorem B1201657 : Blo 1064615 1201657 := bbase (se 2 (by rfl) ⟨450621, by rfl⟩ : syracuseStep 1201657 = 901243) (by norm_num)
theorem B1201693 : Blo 1064615 1201693 := bbase (se 3 (by rfl) ⟨225317, by rfl⟩ : syracuseStep 1201693 = 450635) (by norm_num)
theorem B4871717 : Blo 1064615 4871717 := bbase (se 4 (by rfl) ⟨456723, by rfl⟩ : syracuseStep 4871717 = 913447) (by norm_num)
theorem B1201729 : Blo 1064615 1201729 := bbase (se 2 (by rfl) ⟨450648, by rfl⟩ : syracuseStep 1201729 = 901297) (by norm_num)
theorem B1201765 : Blo 1064615 1201765 := bbase (se 4 (by rfl) ⟨112665, by rfl⟩ : syracuseStep 1201765 = 225331) (by norm_num)
theorem B3593861 : Blo 1064615 3593861 := bbase (se 4 (by rfl) ⟨336924, by rfl⟩ : syracuseStep 3593861 = 673849) (by norm_num)
theorem B1201801 : Blo 1064615 1201801 := bbase (se 2 (by rfl) ⟨450675, by rfl⟩ : syracuseStep 1201801 = 901351) (by norm_num)
theorem B1201837 : Blo 1064615 1201837 := bbase (se 3 (by rfl) ⟨225344, by rfl⟩ : syracuseStep 1201837 = 450689) (by norm_num)
theorem B1201873 : Blo 1064615 1201873 := bbase (se 2 (by rfl) ⟨450702, by rfl⟩ : syracuseStep 1201873 = 901405) (by norm_num)
theorem B4052693 : Blo 1064615 4052693 := bbase (se 7 (by rfl) ⟨47492, by rfl⟩ : syracuseStep 4052693 = 94985) (by norm_num)
theorem B17323733 : Blo 1064615 17323733 := bbase (se 7 (by rfl) ⟨203012, by rfl⟩ : syracuseStep 17323733 = 406025) (by norm_num)
theorem B1201909 : Blo 1064615 1201909 := bbase (se 5 (by rfl) ⟨56339, by rfl⟩ : syracuseStep 1201909 = 112679) (by norm_num)
theorem B1201945 : Blo 1064615 1201945 := bbase (se 2 (by rfl) ⟨450729, by rfl⟩ : syracuseStep 1201945 = 901459) (by norm_num)
theorem B1201981 : Blo 1064615 1201981 := bbase (se 3 (by rfl) ⟨225371, by rfl⟩ : syracuseStep 1201981 = 450743) (by norm_num)
theorem B2021213 : Blo 1064615 2021213 := bbase (se 3 (by rfl) ⟨378977, by rfl⟩ : syracuseStep 2021213 = 757955) (by norm_num)
theorem B1202017 : Blo 1064615 1202017 := bbase (se 2 (by rfl) ⟨450756, by rfl⟩ : syracuseStep 1202017 = 901513) (by norm_num)
theorem B1202053 : Blo 1064615 1202053 := bbase (se 4 (by rfl) ⟨112692, by rfl⟩ : syracuseStep 1202053 = 225385) (by norm_num)
theorem B1202089 : Blo 1064615 1202089 := bbase (se 2 (by rfl) ⟨450783, by rfl⟩ : syracuseStep 1202089 = 901567) (by norm_num)
theorem B1202125 : Blo 1064615 1202125 := bbase (se 3 (by rfl) ⟨225398, by rfl⟩ : syracuseStep 1202125 = 450797) (by norm_num)
theorem B1202161 : Blo 1064615 1202161 := bbase (se 2 (by rfl) ⟨450810, by rfl⟩ : syracuseStep 1202161 = 901621) (by norm_num)
theorem B2021365 : Blo 1064615 2021365 := bbase (se 5 (by rfl) ⟨94751, by rfl⟩ : syracuseStep 2021365 = 189503) (by norm_num)
theorem B1366021 : Blo 1064615 1366021 := bbase (se 4 (by rfl) ⟨128064, by rfl⟩ : syracuseStep 1366021 = 256129) (by norm_num)
theorem B3594293 : Blo 1064615 3594293 := bbase (se 5 (by rfl) ⟨168482, by rfl⟩ : syracuseStep 3594293 = 336965) (by norm_num)
theorem B1300573 : Blo 1064615 1300573 := bbase (se 3 (by rfl) ⟨243857, by rfl⟩ : syracuseStep 1300573 = 487715) (by norm_num)
theorem B3037333 : Blo 1064615 3037333 := bbase (se 6 (by rfl) ⟨71187, by rfl⟩ : syracuseStep 3037333 = 142375) (by norm_num)
theorem B1923245 : Blo 1064615 1923245 := bbase (se 3 (by rfl) ⟨360608, by rfl⟩ : syracuseStep 1923245 = 721217) (by norm_num)
theorem B1136873 : Blo 1064615 1136873 := bbase (se 2 (by rfl) ⟨426327, by rfl⟩ : syracuseStep 1136873 = 852655) (by norm_num)
theorem B2021669 : Blo 1064615 2021669 := bbase (se 4 (by rfl) ⟨189531, by rfl⟩ : syracuseStep 2021669 = 379063) (by norm_num)
theorem B1366313 : Blo 1064615 1366313 := bbase (se 2 (by rfl) ⟨512367, by rfl⟩ : syracuseStep 1366313 = 1024735) (by norm_num)
theorem B3037493 : Blo 1064615 3037493 := bbase (se 5 (by rfl) ⟨142382, by rfl⟩ : syracuseStep 3037493 = 284765) (by norm_num)
theorem B6838613 : Blo 1064615 6838613 := bbase (se 10 (by rfl) ⟨10017, by rfl⟩ : syracuseStep 6838613 = 20035) (by norm_num)
theorem B1137001 : Blo 1064615 1137001 := bbase (se 2 (by rfl) ⟨426375, by rfl⟩ : syracuseStep 1137001 = 852751) (by norm_num)
theorem B7297397 : Blo 1064615 7297397 := bbase (se 5 (by rfl) ⟨342065, by rfl⟩ : syracuseStep 7297397 = 684131) (by norm_num)
theorem B3594725 : Blo 1064615 3594725 := bbase (se 4 (by rfl) ⟨337005, by rfl⟩ : syracuseStep 3594725 = 674011) (by norm_num)
theorem B5397029 : Blo 1064615 5397029 := bbase (se 4 (by rfl) ⟨505971, by rfl⟩ : syracuseStep 5397029 = 1011943) (by norm_num)
theorem B3037733 : Blo 1064615 3037733 := bbase (se 4 (by rfl) ⟨284787, by rfl⟩ : syracuseStep 3037733 = 569575) (by norm_num)
theorem B3037925 : Blo 1064615 3037925 := bbase (se 4 (by rfl) ⟨284805, by rfl⟩ : syracuseStep 3037925 = 569611) (by norm_num)
theorem B1137445 : Blo 1064615 1137445 := bbase (se 4 (by rfl) ⟨106635, by rfl⟩ : syracuseStep 1137445 = 213271) (by norm_num)
theorem B13130581 : Blo 1064615 13130581 := bbase (se 9 (by rfl) ⟨38468, by rfl⟩ : syracuseStep 13130581 = 76937) (by norm_num)
theorem B3595157 : Blo 1064615 3595157 := bbase (se 6 (by rfl) ⟨84261, by rfl⟩ : syracuseStep 3595157 = 168523) (by norm_num)
theorem B1137565 : Blo 1064615 1137565 := bbase (se 3 (by rfl) ⟨213293, by rfl⟩ : syracuseStep 1137565 = 426587) (by norm_num)
theorem B2022421 : Blo 1064615 2022421 := bbase (se 6 (by rfl) ⟨47400, by rfl⟩ : syracuseStep 2022421 = 94801) (by norm_num)
theorem B1137817 : Blo 1064615 1137817 := bbase (se 2 (by rfl) ⟨426681, by rfl⟩ : syracuseStep 1137817 = 853363) (by norm_num)
theorem B1137821 : Blo 1064615 1137821 := bbase (se 3 (by rfl) ⟨213341, by rfl⟩ : syracuseStep 1137821 = 426683) (by norm_num)
theorem B2022565 : Blo 1064615 2022565 := bbase (se 4 (by rfl) ⟨189615, by rfl⟩ : syracuseStep 2022565 = 379231) (by norm_num)
theorem B3595589 : Blo 1064615 3595589 := bbase (se 4 (by rfl) ⟨337086, by rfl⟩ : syracuseStep 3595589 = 674173) (by norm_num)
theorem B2022725 : Blo 1064615 2022725 := bbase (se 4 (by rfl) ⟨189630, by rfl⟩ : syracuseStep 2022725 = 379261) (by norm_num)
theorem B2022869 : Blo 1064615 2022869 := bbase (se 7 (by rfl) ⟨23705, by rfl⟩ : syracuseStep 2022869 = 47411) (by norm_num)
theorem B1596941 : Blo 1064615 1596941 := bbase (se 3 (by rfl) ⟨299426, by rfl⟩ : syracuseStep 1596941 = 598853) (by norm_num)
theorem B1596965 : Blo 1064615 1596965 := bbase (se 4 (by rfl) ⟨149715, by rfl⟩ : syracuseStep 1596965 = 299431) (by norm_num)
theorem B1596989 : Blo 1064615 1596989 := bbase (se 3 (by rfl) ⟨299435, by rfl⟩ : syracuseStep 1596989 = 598871) (by norm_num)
theorem B1597013 : Blo 1064615 1597013 := bbase (se 8 (by rfl) ⟨9357, by rfl⟩ : syracuseStep 1597013 = 18715) (by norm_num)
theorem B20012629 : Blo 1064615 20012629 := bbase (se 8 (by rfl) ⟨117261, by rfl⟩ : syracuseStep 20012629 = 234523) (by norm_num)
theorem B1597037 : Blo 1064615 1597037 := bbase (se 3 (by rfl) ⟨299444, by rfl⟩ : syracuseStep 1597037 = 598889) (by norm_num)
theorem B2252405 : Blo 1064615 2252405 := bbase (se 5 (by rfl) ⟨105581, by rfl⟩ : syracuseStep 2252405 = 211163) (by norm_num)
theorem B1597061 : Blo 1064615 1597061 := bbase (se 4 (by rfl) ⟨149724, by rfl⟩ : syracuseStep 1597061 = 299449) (by norm_num)
theorem B1597085 : Blo 1064615 1597085 := bbase (se 3 (by rfl) ⟨299453, by rfl⟩ : syracuseStep 1597085 = 598907) (by norm_num)
theorem B1597109 : Blo 1064615 1597109 := bbase (se 5 (by rfl) ⟨74864, by rfl⟩ : syracuseStep 1597109 = 149729) (by norm_num)
theorem B5463749 : Blo 1064615 5463749 := bbase (se 4 (by rfl) ⟨512226, by rfl⟩ : syracuseStep 5463749 = 1024453) (by norm_num)
theorem B3038917 : Blo 1064615 3038917 := bbase (se 4 (by rfl) ⟨284898, by rfl⟩ : syracuseStep 3038917 = 569797) (by norm_num)
theorem B1597133 : Blo 1064615 1597133 := bbase (se 3 (by rfl) ⟨299462, by rfl⟩ : syracuseStep 1597133 = 598925) (by norm_num)
theorem B1138385 : Blo 1064615 1138385 := bbase (se 2 (by rfl) ⟨426894, by rfl⟩ : syracuseStep 1138385 = 853789) (by norm_num)
theorem B1597157 : Blo 1064615 1597157 := bbase (se 4 (by rfl) ⟨149733, by rfl⟩ : syracuseStep 1597157 = 299467) (by norm_num)
theorem B3596021 : Blo 1064615 3596021 := bbase (se 5 (by rfl) ⟨168563, by rfl⟩ : syracuseStep 3596021 = 337127) (by norm_num)
theorem B2023157 : Blo 1064615 2023157 := bbase (se 5 (by rfl) ⟨94835, by rfl⟩ : syracuseStep 2023157 = 189671) (by norm_num)
theorem B1597181 : Blo 1064615 1597181 := bbase (se 3 (by rfl) ⟨299471, by rfl⟩ : syracuseStep 1597181 = 598943) (by norm_num)
theorem B1597205 : Blo 1064615 1597205 := bbase (se 6 (by rfl) ⟨37434, by rfl⟩ : syracuseStep 1597205 = 74869) (by norm_num)
theorem B4054805 : Blo 1064615 4054805 := bbase (se 6 (by rfl) ⟨95034, by rfl⟩ : syracuseStep 4054805 = 190069) (by norm_num)
theorem B1597229 : Blo 1064615 1597229 := bbase (se 3 (by rfl) ⟨299480, by rfl⟩ : syracuseStep 1597229 = 598961) (by norm_num)
theorem B5398325 : Blo 1064615 5398325 := bbase (se 5 (by rfl) ⟨253046, by rfl⟩ : syracuseStep 5398325 = 506093) (by norm_num)
theorem B1597253 : Blo 1064615 1597253 := bbase (se 4 (by rfl) ⟨149742, by rfl⟩ : syracuseStep 1597253 = 299485) (by norm_num)
theorem B4874053 : Blo 1064615 4874053 := bbase (se 4 (by rfl) ⟨456942, by rfl⟩ : syracuseStep 4874053 = 913885) (by norm_num)
theorem B1597277 : Blo 1064615 1597277 := bbase (se 3 (by rfl) ⟨299489, by rfl⟩ : syracuseStep 1597277 = 598979) (by norm_num)
theorem B1597301 : Blo 1064615 1597301 := bbase (se 5 (by rfl) ⟨74873, by rfl⟩ : syracuseStep 1597301 = 149747) (by norm_num)
theorem B1597325 : Blo 1064615 1597325 := bbase (se 3 (by rfl) ⟨299498, by rfl⟩ : syracuseStep 1597325 = 598997) (by norm_num)
theorem B2023309 : Blo 1064615 2023309 := bbase (se 3 (by rfl) ⟨379370, by rfl⟩ : syracuseStep 2023309 = 758741) (by norm_num)
theorem B1138573 : Blo 1064615 1138573 := bbase (se 3 (by rfl) ⟨213482, by rfl⟩ : syracuseStep 1138573 = 426965) (by norm_num)
theorem B1925005 : Blo 1064615 1925005 := bbase (se 3 (by rfl) ⟨360938, by rfl⟩ : syracuseStep 1925005 = 721877) (by norm_num)
theorem B1597349 : Blo 1064615 1597349 := bbase (se 4 (by rfl) ⟨149751, by rfl⟩ : syracuseStep 1597349 = 299503) (by norm_num)
theorem B1597373 : Blo 1064615 1597373 := bbase (se 3 (by rfl) ⟨299507, by rfl⟩ : syracuseStep 1597373 = 599015) (by norm_num)
theorem B1597397 : Blo 1064615 1597397 := bbase (se 7 (by rfl) ⟨18719, by rfl⟩ : syracuseStep 1597397 = 37439) (by norm_num)
theorem B1597421 : Blo 1064615 1597421 := bbase (se 3 (by rfl) ⟨299516, by rfl⟩ : syracuseStep 1597421 = 599033) (by norm_num)
theorem B1597445 : Blo 1064615 1597445 := bbase (se 4 (by rfl) ⟨149760, by rfl⟩ : syracuseStep 1597445 = 299521) (by norm_num)
theorem B1925141 : Blo 1064615 1925141 := bbase (se 6 (by rfl) ⟨45120, by rfl⟩ : syracuseStep 1925141 = 90241) (by norm_num)
theorem B1597469 : Blo 1064615 1597469 := bbase (se 3 (by rfl) ⟨299525, by rfl⟩ : syracuseStep 1597469 = 599051) (by norm_num)
theorem B1597493 : Blo 1064615 1597493 := bbase (se 5 (by rfl) ⟨74882, by rfl⟩ : syracuseStep 1597493 = 149765) (by norm_num)
theorem B2777141 : Blo 1064615 2777141 := bbase (se 5 (by rfl) ⟨130178, by rfl⟩ : syracuseStep 2777141 = 260357) (by norm_num)
theorem B4055093 : Blo 1064615 4055093 := bbase (se 5 (by rfl) ⟨190082, by rfl⟩ : syracuseStep 4055093 = 380165) (by norm_num)
theorem B1597517 : Blo 1064615 1597517 := bbase (se 3 (by rfl) ⟨299534, by rfl⟩ : syracuseStep 1597517 = 599069) (by norm_num)
theorem B1597541 : Blo 1064615 1597541 := bbase (se 4 (by rfl) ⟨149769, by rfl⟩ : syracuseStep 1597541 = 299539) (by norm_num)
theorem B1925221 : Blo 1064615 1925221 := bbase (se 4 (by rfl) ⟨180489, by rfl⟩ : syracuseStep 1925221 = 360979) (by norm_num)
theorem B1368181 : Blo 1064615 1368181 := bbase (se 5 (by rfl) ⟨64133, by rfl⟩ : syracuseStep 1368181 = 128267) (by norm_num)
theorem B1597565 : Blo 1064615 1597565 := bbase (se 3 (by rfl) ⟨299543, by rfl⟩ : syracuseStep 1597565 = 599087) (by norm_num)
theorem B1597589 : Blo 1064615 1597589 := bbase (se 6 (by rfl) ⟨37443, by rfl⟩ : syracuseStep 1597589 = 74887) (by norm_num)
theorem B3596453 : Blo 1064615 3596453 := bbase (se 4 (by rfl) ⟨337167, by rfl⟩ : syracuseStep 3596453 = 674335) (by norm_num)
theorem B1597613 : Blo 1064615 1597613 := bbase (se 3 (by rfl) ⟨299552, by rfl⟩ : syracuseStep 1597613 = 599105) (by norm_num)
theorem B2023613 : Blo 1064615 2023613 := bbase (se 3 (by rfl) ⟨379427, by rfl⟩ : syracuseStep 2023613 = 758855) (by norm_num)
theorem B1597637 : Blo 1064615 1597637 := bbase (se 4 (by rfl) ⟨149778, by rfl⟩ : syracuseStep 1597637 = 299557) (by norm_num)
theorem B1597661 : Blo 1064615 1597661 := bbase (se 3 (by rfl) ⟨299561, by rfl⟩ : syracuseStep 1597661 = 599123) (by norm_num)
theorem B1597685 : Blo 1064615 1597685 := bbase (se 5 (by rfl) ⟨74891, by rfl⟩ : syracuseStep 1597685 = 149783) (by norm_num)
theorem B1597709 : Blo 1064615 1597709 := bbase (se 3 (by rfl) ⟨299570, by rfl⟩ : syracuseStep 1597709 = 599141) (by norm_num)
theorem B1597733 : Blo 1064615 1597733 := bbase (se 4 (by rfl) ⟨149787, by rfl⟩ : syracuseStep 1597733 = 299575) (by norm_num)
theorem B1597757 : Blo 1064615 1597757 := bbase (se 3 (by rfl) ⟨299579, by rfl⟩ : syracuseStep 1597757 = 599159) (by norm_num)
theorem B1597781 : Blo 1064615 1597781 := bbase (se 10 (by rfl) ⟨2340, by rfl⟩ : syracuseStep 1597781 = 4681) (by norm_num)
theorem B1597805 : Blo 1064615 1597805 := bbase (se 3 (by rfl) ⟨299588, by rfl⟩ : syracuseStep 1597805 = 599177) (by norm_num)
theorem B1597829 : Blo 1064615 1597829 := bbase (se 4 (by rfl) ⟨149796, by rfl⟩ : syracuseStep 1597829 = 299593) (by norm_num)
theorem B1597853 : Blo 1064615 1597853 := bbase (se 3 (by rfl) ⟨299597, by rfl⟩ : syracuseStep 1597853 = 599195) (by norm_num)
theorem B1597877 : Blo 1064615 1597877 := bbase (se 5 (by rfl) ⟨74900, by rfl⟩ : syracuseStep 1597877 = 149801) (by norm_num)
theorem B1597901 : Blo 1064615 1597901 := bbase (se 3 (by rfl) ⟨299606, by rfl⟩ : syracuseStep 1597901 = 599213) (by norm_num)
theorem B1597925 : Blo 1064615 1597925 := bbase (se 4 (by rfl) ⟨149805, by rfl⟩ : syracuseStep 1597925 = 299611) (by norm_num)
theorem B1597949 : Blo 1064615 1597949 := bbase (se 3 (by rfl) ⟨299615, by rfl⟩ : syracuseStep 1597949 = 599231) (by norm_num)
theorem B1597973 : Blo 1064615 1597973 := bbase (se 6 (by rfl) ⟨37452, by rfl⟩ : syracuseStep 1597973 = 74905) (by norm_num)
theorem B1597997 : Blo 1064615 1597997 := bbase (se 3 (by rfl) ⟨299624, by rfl⟩ : syracuseStep 1597997 = 599249) (by norm_num)
theorem B1598021 : Blo 1064615 1598021 := bbase (se 4 (by rfl) ⟨149814, by rfl⟩ : syracuseStep 1598021 = 299629) (by norm_num)
theorem B3596885 : Blo 1064615 3596885 := bbase (se 8 (by rfl) ⟨21075, by rfl⟩ : syracuseStep 3596885 = 42151) (by norm_num)
theorem B1598045 : Blo 1064615 1598045 := bbase (se 3 (by rfl) ⟨299633, by rfl⟩ : syracuseStep 1598045 = 599267) (by norm_num)
theorem B1598069 : Blo 1064615 1598069 := bbase (se 5 (by rfl) ⟨74909, by rfl⟩ : syracuseStep 1598069 = 149819) (by norm_num)
theorem B1598093 : Blo 1064615 1598093 := bbase (se 3 (by rfl) ⟨299642, by rfl⟩ : syracuseStep 1598093 = 599285) (by norm_num)
theorem B1598117 : Blo 1064615 1598117 := bbase (se 4 (by rfl) ⟨149823, by rfl⟩ : syracuseStep 1598117 = 299647) (by norm_num)
theorem B1598141 : Blo 1064615 1598141 := bbase (se 3 (by rfl) ⟨299651, by rfl⟩ : syracuseStep 1598141 = 599303) (by norm_num)
theorem B1139393 : Blo 1064615 1139393 := bbase (se 2 (by rfl) ⟨427272, by rfl⟩ : syracuseStep 1139393 = 854545) (by norm_num)
theorem B1598165 : Blo 1064615 1598165 := bbase (se 7 (by rfl) ⟨18728, by rfl⟩ : syracuseStep 1598165 = 37457) (by norm_num)
theorem B1598189 : Blo 1064615 1598189 := bbase (se 3 (by rfl) ⟨299660, by rfl⟩ : syracuseStep 1598189 = 599321) (by norm_num)
theorem B1598213 : Blo 1064615 1598213 := bbase (se 4 (by rfl) ⟨149832, by rfl⟩ : syracuseStep 1598213 = 299665) (by norm_num)
theorem B3040021 : Blo 1064615 3040021 := bbase (se 6 (by rfl) ⟨71250, by rfl⟩ : syracuseStep 3040021 = 142501) (by norm_num)
theorem B1598237 : Blo 1064615 1598237 := bbase (se 3 (by rfl) ⟨299669, by rfl⟩ : syracuseStep 1598237 = 599339) (by norm_num)
theorem B1598261 : Blo 1064615 1598261 := bbase (se 5 (by rfl) ⟨74918, by rfl⟩ : syracuseStep 1598261 = 149837) (by norm_num)
theorem B1598285 : Blo 1064615 1598285 := bbase (se 3 (by rfl) ⟨299678, by rfl⟩ : syracuseStep 1598285 = 599357) (by norm_num)
theorem B1598309 : Blo 1064615 1598309 := bbase (se 4 (by rfl) ⟨149841, by rfl⟩ : syracuseStep 1598309 = 299683) (by norm_num)
theorem B1598333 : Blo 1064615 1598333 := bbase (se 3 (by rfl) ⟨299687, by rfl⟩ : syracuseStep 1598333 = 599375) (by norm_num)
theorem B1598357 : Blo 1064615 1598357 := bbase (se 6 (by rfl) ⟨37461, by rfl⟩ : syracuseStep 1598357 = 74923) (by norm_num)
theorem B1598381 : Blo 1064615 1598381 := bbase (se 3 (by rfl) ⟨299696, by rfl⟩ : syracuseStep 1598381 = 599393) (by norm_num)
theorem B2024365 : Blo 1064615 2024365 := bbase (se 3 (by rfl) ⟨379568, by rfl⟩ : syracuseStep 2024365 = 759137) (by norm_num)
theorem B1598405 : Blo 1064615 1598405 := bbase (se 4 (by rfl) ⟨149850, by rfl⟩ : syracuseStep 1598405 = 299701) (by norm_num)
theorem B1598429 : Blo 1064615 1598429 := bbase (se 3 (by rfl) ⟨299705, by rfl⟩ : syracuseStep 1598429 = 599411) (by norm_num)
theorem B1369073 : Blo 1064615 1369073 := bbase (se 2 (by rfl) ⟨513402, by rfl⟩ : syracuseStep 1369073 = 1026805) (by norm_num)
theorem B1598453 : Blo 1064615 1598453 := bbase (se 5 (by rfl) ⟨74927, by rfl⟩ : syracuseStep 1598453 = 149855) (by norm_num)
theorem B3597317 : Blo 1064615 3597317 := bbase (se 4 (by rfl) ⟨337248, by rfl⟩ : syracuseStep 3597317 = 674497) (by norm_num)
theorem B1598477 : Blo 1064615 1598477 := bbase (se 3 (by rfl) ⟨299714, by rfl⟩ : syracuseStep 1598477 = 599429) (by norm_num)
theorem B1598501 : Blo 1064615 1598501 := bbase (se 4 (by rfl) ⟨149859, by rfl⟩ : syracuseStep 1598501 = 299719) (by norm_num)
theorem B1598525 : Blo 1064615 1598525 := bbase (se 3 (by rfl) ⟨299723, by rfl⟩ : syracuseStep 1598525 = 599447) (by norm_num)
theorem B2024509 : Blo 1064615 2024509 := bbase (se 3 (by rfl) ⟨379595, by rfl⟩ : syracuseStep 2024509 = 759191) (by norm_num)
theorem B5399621 : Blo 1064615 5399621 := bbase (se 4 (by rfl) ⟨506214, by rfl⟩ : syracuseStep 5399621 = 1012429) (by norm_num)
theorem B1598549 : Blo 1064615 1598549 := bbase (se 8 (by rfl) ⟨9366, by rfl⟩ : syracuseStep 1598549 = 18733) (by norm_num)
theorem B1598573 : Blo 1064615 1598573 := bbase (se 3 (by rfl) ⟨299732, by rfl⟩ : syracuseStep 1598573 = 599465) (by norm_num)
theorem B1139837 : Blo 1064615 1139837 := bbase (se 3 (by rfl) ⟨213719, by rfl⟩ : syracuseStep 1139837 = 427439) (by norm_num)
theorem B1729669 : Blo 1064615 1729669 := bbase (se 4 (by rfl) ⟨162156, by rfl⟩ : syracuseStep 1729669 = 324313) (by norm_num)
theorem B1598597 : Blo 1064615 1598597 := bbase (se 4 (by rfl) ⟨149868, by rfl⟩ : syracuseStep 1598597 = 299737) (by norm_num)
theorem B1598621 : Blo 1064615 1598621 := bbase (se 3 (by rfl) ⟨299741, by rfl⟩ : syracuseStep 1598621 = 599483) (by norm_num)
theorem B2221229 : Blo 1064615 2221229 := bbase (se 3 (by rfl) ⟨416480, by rfl⟩ : syracuseStep 2221229 = 832961) (by norm_num)
theorem B4547765 : Blo 1064615 4547765 := bbase (se 5 (by rfl) ⟨213176, by rfl⟩ : syracuseStep 4547765 = 426353) (by norm_num)
theorem B1598645 : Blo 1064615 1598645 := bbase (se 5 (by rfl) ⟨74936, by rfl⟩ : syracuseStep 1598645 = 149873) (by norm_num)
theorem B1598669 : Blo 1064615 1598669 := bbase (se 3 (by rfl) ⟨299750, by rfl⟩ : syracuseStep 1598669 = 599501) (by norm_num)
theorem B4056277 : Blo 1064615 4056277 := bbase (se 7 (by rfl) ⟨47534, by rfl⟩ : syracuseStep 4056277 = 95069) (by norm_num)
theorem B2024669 : Blo 1064615 2024669 := bbase (se 3 (by rfl) ⟨379625, by rfl⟩ : syracuseStep 2024669 = 759251) (by norm_num)
theorem B1598693 : Blo 1064615 1598693 := bbase (se 4 (by rfl) ⟨149877, by rfl⟩ : syracuseStep 1598693 = 299755) (by norm_num)
theorem B1598717 : Blo 1064615 1598717 := bbase (se 3 (by rfl) ⟨299759, by rfl⟩ : syracuseStep 1598717 = 599519) (by norm_num)
theorem B1598741 : Blo 1064615 1598741 := bbase (se 6 (by rfl) ⟨37470, by rfl⟩ : syracuseStep 1598741 = 74941) (by norm_num)
theorem B1598765 : Blo 1064615 1598765 := bbase (se 3 (by rfl) ⟨299768, by rfl⟩ : syracuseStep 1598765 = 599537) (by norm_num)
theorem B1598789 : Blo 1064615 1598789 := bbase (se 4 (by rfl) ⟨149886, by rfl⟩ : syracuseStep 1598789 = 299773) (by norm_num)
theorem B1598813 : Blo 1064615 1598813 := bbase (se 3 (by rfl) ⟨299777, by rfl⟩ : syracuseStep 1598813 = 599555) (by norm_num)
theorem B2024813 : Blo 1064615 2024813 := bbase (se 3 (by rfl) ⟨379652, by rfl⟩ : syracuseStep 2024813 = 759305) (by norm_num)
theorem B1598837 : Blo 1064615 1598837 := bbase (se 5 (by rfl) ⟨74945, by rfl⟩ : syracuseStep 1598837 = 149891) (by norm_num)
theorem B1140085 : Blo 1064615 1140085 := bbase (se 5 (by rfl) ⟨53441, by rfl⟩ : syracuseStep 1140085 = 106883) (by norm_num)
theorem B1598861 : Blo 1064615 1598861 := bbase (se 3 (by rfl) ⟨299786, by rfl⟩ : syracuseStep 1598861 = 599573) (by norm_num)
theorem B1598885 : Blo 1064615 1598885 := bbase (se 4 (by rfl) ⟨149895, by rfl⟩ : syracuseStep 1598885 = 299791) (by norm_num)
theorem B3597749 : Blo 1064615 3597749 := bbase (se 5 (by rfl) ⟨168644, by rfl⟩ : syracuseStep 3597749 = 337289) (by norm_num)
theorem B1598909 : Blo 1064615 1598909 := bbase (se 3 (by rfl) ⟨299795, by rfl⟩ : syracuseStep 1598909 = 599591) (by norm_num)
theorem B1598933 : Blo 1064615 1598933 := bbase (se 7 (by rfl) ⟨18737, by rfl⟩ : syracuseStep 1598933 = 37475) (by norm_num)
theorem B1598957 : Blo 1064615 1598957 := bbase (se 3 (by rfl) ⟨299804, by rfl⟩ : syracuseStep 1598957 = 599609) (by norm_num)
theorem B1598981 : Blo 1064615 1598981 := bbase (se 4 (by rfl) ⟨149904, by rfl⟩ : syracuseStep 1598981 = 299809) (by norm_num)
theorem B4056581 : Blo 1064615 4056581 := bbase (se 4 (by rfl) ⟨380304, by rfl⟩ : syracuseStep 4056581 = 760609) (by norm_num)
theorem B1599005 : Blo 1064615 1599005 := bbase (se 3 (by rfl) ⟨299813, by rfl⟩ : syracuseStep 1599005 = 599627) (by norm_num)
theorem B1599029 : Blo 1064615 1599029 := bbase (se 5 (by rfl) ⟨74954, by rfl⟩ : syracuseStep 1599029 = 149909) (by norm_num)
theorem B1599053 : Blo 1064615 1599053 := bbase (se 3 (by rfl) ⟨299822, by rfl⟩ : syracuseStep 1599053 = 599645) (by norm_num)
theorem B1599077 : Blo 1064615 1599077 := bbase (se 4 (by rfl) ⟨149913, by rfl⟩ : syracuseStep 1599077 = 299827) (by norm_num)
theorem B1599101 : Blo 1064615 1599101 := bbase (se 3 (by rfl) ⟨299831, by rfl⟩ : syracuseStep 1599101 = 599663) (by norm_num)
theorem B2025101 : Blo 1064615 2025101 := bbase (se 3 (by rfl) ⟨379706, by rfl⟩ : syracuseStep 2025101 = 759413) (by norm_num)
theorem B1599125 : Blo 1064615 1599125 := bbase (se 6 (by rfl) ⟨37479, by rfl⟩ : syracuseStep 1599125 = 74959) (by norm_num)
theorem B1599149 : Blo 1064615 1599149 := bbase (se 3 (by rfl) ⟨299840, by rfl⟩ : syracuseStep 1599149 = 599681) (by norm_num)
theorem B1599173 : Blo 1064615 1599173 := bbase (se 4 (by rfl) ⟨149922, by rfl⟩ : syracuseStep 1599173 = 299845) (by norm_num)
theorem B4318933 : Blo 1064615 4318933 := bbase (se 7 (by rfl) ⟨50612, by rfl⟩ : syracuseStep 4318933 = 101225) (by norm_num)
theorem B1599197 : Blo 1064615 1599197 := bbase (se 3 (by rfl) ⟨299849, by rfl⟩ : syracuseStep 1599197 = 599699) (by norm_num)
theorem B1599221 : Blo 1064615 1599221 := bbase (se 5 (by rfl) ⟨74963, by rfl⟩ : syracuseStep 1599221 = 149927) (by norm_num)
theorem B3892997 : Blo 1064615 3892997 := bbase (se 4 (by rfl) ⟨364968, by rfl⟩ : syracuseStep 3892997 = 729937) (by norm_num)
theorem B1599245 : Blo 1064615 1599245 := bbase (se 3 (by rfl) ⟨299858, by rfl⟩ : syracuseStep 1599245 = 599717) (by norm_num)
theorem B1599269 : Blo 1064615 1599269 := bbase (se 4 (by rfl) ⟨149931, by rfl⟩ : syracuseStep 1599269 = 299863) (by norm_num)
theorem B2025253 : Blo 1064615 2025253 := bbase (se 4 (by rfl) ⟨189867, by rfl⟩ : syracuseStep 2025253 = 379735) (by norm_num)
theorem B1140517 : Blo 1064615 1140517 := bbase (se 4 (by rfl) ⟨106923, by rfl⟩ : syracuseStep 1140517 = 213847) (by norm_num)
theorem B1599293 : Blo 1064615 1599293 := bbase (se 3 (by rfl) ⟨299867, by rfl⟩ : syracuseStep 1599293 = 599735) (by norm_num)
theorem B1599317 : Blo 1064615 1599317 := bbase (se 9 (by rfl) ⟨4685, by rfl⟩ : syracuseStep 1599317 = 9371) (by norm_num)
theorem B3598181 : Blo 1064615 3598181 := bbase (se 4 (by rfl) ⟨337329, by rfl⟩ : syracuseStep 3598181 = 674659) (by norm_num)
theorem B1599341 : Blo 1064615 1599341 := bbase (se 3 (by rfl) ⟨299876, by rfl⟩ : syracuseStep 1599341 = 599753) (by norm_num)
theorem B1140589 : Blo 1064615 1140589 := bbase (se 3 (by rfl) ⟨213860, by rfl⟩ : syracuseStep 1140589 = 427721) (by norm_num)
theorem B1599365 : Blo 1064615 1599365 := bbase (se 4 (by rfl) ⟨149940, by rfl⟩ : syracuseStep 1599365 = 299881) (by norm_num)
theorem B1599389 : Blo 1064615 1599389 := bbase (se 3 (by rfl) ⟨299885, by rfl⟩ : syracuseStep 1599389 = 599771) (by norm_num)
theorem B1599413 : Blo 1064615 1599413 := bbase (se 5 (by rfl) ⟨74972, by rfl⟩ : syracuseStep 1599413 = 149945) (by norm_num)
theorem B1599437 : Blo 1064615 1599437 := bbase (se 3 (by rfl) ⟨299894, by rfl⟩ : syracuseStep 1599437 = 599789) (by norm_num)
theorem B1599461 : Blo 1064615 1599461 := bbase (se 4 (by rfl) ⟨149949, by rfl⟩ : syracuseStep 1599461 = 299899) (by norm_num)
theorem B1599485 : Blo 1064615 1599485 := bbase (se 3 (by rfl) ⟨299903, by rfl⟩ : syracuseStep 1599485 = 599807) (by norm_num)
theorem B1599509 : Blo 1064615 1599509 := bbase (se 6 (by rfl) ⟨37488, by rfl⟩ : syracuseStep 1599509 = 74977) (by norm_num)
theorem B1599533 : Blo 1064615 1599533 := bbase (se 3 (by rfl) ⟨299912, by rfl⟩ : syracuseStep 1599533 = 599825) (by norm_num)
theorem B1599557 : Blo 1064615 1599557 := bbase (se 4 (by rfl) ⟨149958, by rfl⟩ : syracuseStep 1599557 = 299917) (by norm_num)
theorem B2025557 : Blo 1064615 2025557 := bbase (se 8 (by rfl) ⟨11868, by rfl⟩ : syracuseStep 2025557 = 23737) (by norm_num)
theorem B1599581 : Blo 1064615 1599581 := bbase (se 3 (by rfl) ⟨299921, by rfl⟩ : syracuseStep 1599581 = 599843) (by norm_num)
theorem B1599605 : Blo 1064615 1599605 := bbase (se 5 (by rfl) ⟨74981, by rfl⟩ : syracuseStep 1599605 = 149963) (by norm_num)
theorem B1599629 : Blo 1064615 1599629 := bbase (se 3 (by rfl) ⟨299930, by rfl⟩ : syracuseStep 1599629 = 599861) (by norm_num)
theorem B1599653 : Blo 1064615 1599653 := bbase (se 4 (by rfl) ⟨149967, by rfl⟩ : syracuseStep 1599653 = 299935) (by norm_num)
theorem B1599677 : Blo 1064615 1599677 := bbase (se 3 (by rfl) ⟨299939, by rfl⟩ : syracuseStep 1599677 = 599879) (by norm_num)
theorem B1599701 : Blo 1064615 1599701 := bbase (se 7 (by rfl) ⟨18746, by rfl⟩ : syracuseStep 1599701 = 37493) (by norm_num)
theorem B1140961 : Blo 1064615 1140961 := bbase (se 2 (by rfl) ⟨427860, by rfl⟩ : syracuseStep 1140961 = 855721) (by norm_num)
theorem B1599725 : Blo 1064615 1599725 := bbase (se 3 (by rfl) ⟨299948, by rfl⟩ : syracuseStep 1599725 = 599897) (by norm_num)
theorem B3041525 : Blo 1064615 3041525 := bbase (se 5 (by rfl) ⟨142571, by rfl⟩ : syracuseStep 3041525 = 285143) (by norm_num)
theorem B1599749 : Blo 1064615 1599749 := bbase (se 4 (by rfl) ⟨149976, by rfl⟩ : syracuseStep 1599749 = 299953) (by norm_num)
theorem B3598613 : Blo 1064615 3598613 := bbase (se 6 (by rfl) ⟨84342, by rfl⟩ : syracuseStep 3598613 = 168685) (by norm_num)
theorem B1599773 : Blo 1064615 1599773 := bbase (se 3 (by rfl) ⟨299957, by rfl⟩ : syracuseStep 1599773 = 599915) (by norm_num)
theorem B1599797 : Blo 1064615 1599797 := bbase (se 5 (by rfl) ⟨74990, by rfl⟩ : syracuseStep 1599797 = 149981) (by norm_num)
theorem B1599821 : Blo 1064615 1599821 := bbase (se 3 (by rfl) ⟨299966, by rfl⟩ : syracuseStep 1599821 = 599933) (by norm_num)
theorem B5400917 : Blo 1064615 5400917 := bbase (se 10 (by rfl) ⟨7911, by rfl⟩ : syracuseStep 5400917 = 15823) (by norm_num)
theorem B1599845 : Blo 1064615 1599845 := bbase (se 4 (by rfl) ⟨149985, by rfl⟩ : syracuseStep 1599845 = 299971) (by norm_num)
theorem B1599869 : Blo 1064615 1599869 := bbase (se 3 (by rfl) ⟨299975, by rfl⟩ : syracuseStep 1599869 = 599951) (by norm_num)
theorem B1599893 : Blo 1064615 1599893 := bbase (se 6 (by rfl) ⟨37497, by rfl⟩ : syracuseStep 1599893 = 74995) (by norm_num)
theorem B1599917 : Blo 1064615 1599917 := bbase (se 3 (by rfl) ⟨299984, by rfl⟩ : syracuseStep 1599917 = 599969) (by norm_num)
theorem B1599941 : Blo 1064615 1599941 := bbase (se 4 (by rfl) ⟨149994, by rfl⟩ : syracuseStep 1599941 = 299989) (by norm_num)
theorem B6482389 : Blo 1064615 6482389 := bbase (se 7 (by rfl) ⟨75965, by rfl⟩ : syracuseStep 6482389 = 151931) (by norm_num)
theorem B1796573 : Blo 1064615 1796573 := bbase (se 3 (by rfl) ⟨336857, by rfl⟩ : syracuseStep 1796573 = 673715) (by norm_num)
theorem B1599965 : Blo 1064615 1599965 := bbase (se 3 (by rfl) ⟨299993, by rfl⟩ : syracuseStep 1599965 = 599987) (by norm_num)
theorem B1731053 : Blo 1064615 1731053 := bbase (se 3 (by rfl) ⟨324572, by rfl⟩ : syracuseStep 1731053 = 649145) (by norm_num)
theorem B1599989 : Blo 1064615 1599989 := bbase (se 5 (by rfl) ⟨74999, by rfl⟩ : syracuseStep 1599989 = 149999) (by norm_num)
theorem B1600013 : Blo 1064615 1600013 := bbase (se 3 (by rfl) ⟨300002, by rfl⟩ : syracuseStep 1600013 = 600005) (by norm_num)
theorem B1600037 : Blo 1064615 1600037 := bbase (se 4 (by rfl) ⟨150003, by rfl⟩ : syracuseStep 1600037 = 300007) (by norm_num)
theorem B1600061 : Blo 1064615 1600061 := bbase (se 3 (by rfl) ⟨300011, by rfl⟩ : syracuseStep 1600061 = 600023) (by norm_num)
theorem B1600085 : Blo 1064615 1600085 := bbase (se 8 (by rfl) ⟨9375, by rfl⟩ : syracuseStep 1600085 = 18751) (by norm_num)
theorem B1796701 : Blo 1064615 1796701 := bbase (se 3 (by rfl) ⟨336881, by rfl⟩ : syracuseStep 1796701 = 673763) (by norm_num)
theorem B1600109 : Blo 1064615 1600109 := bbase (se 3 (by rfl) ⟨300020, by rfl⟩ : syracuseStep 1600109 = 600041) (by norm_num)
theorem B1600133 : Blo 1064615 1600133 := bbase (se 4 (by rfl) ⟨150012, by rfl⟩ : syracuseStep 1600133 = 300025) (by norm_num)
theorem B1600157 : Blo 1064615 1600157 := bbase (se 3 (by rfl) ⟨300029, by rfl⟩ : syracuseStep 1600157 = 600059) (by norm_num)
theorem B1796789 : Blo 1064615 1796789 := bbase (se 5 (by rfl) ⟨84224, by rfl⟩ : syracuseStep 1796789 = 168449) (by norm_num)
theorem B1600181 : Blo 1064615 1600181 := bbase (se 5 (by rfl) ⟨75008, by rfl⟩ : syracuseStep 1600181 = 150017) (by norm_num)
theorem B3599045 : Blo 1064615 3599045 := bbase (se 4 (by rfl) ⟨337410, by rfl⟩ : syracuseStep 3599045 = 674821) (by norm_num)
theorem B1600205 : Blo 1064615 1600205 := bbase (se 3 (by rfl) ⟨300038, by rfl⟩ : syracuseStep 1600205 = 600077) (by norm_num)
theorem B1600229 : Blo 1064615 1600229 := bbase (se 4 (by rfl) ⟨150021, by rfl⟩ : syracuseStep 1600229 = 300043) (by norm_num)
theorem B1600253 : Blo 1064615 1600253 := bbase (se 3 (by rfl) ⟨300047, by rfl⟩ : syracuseStep 1600253 = 600095) (by norm_num)
theorem B1600277 : Blo 1064615 1600277 := bbase (se 6 (by rfl) ⟨37506, by rfl⟩ : syracuseStep 1600277 = 75013) (by norm_num)
theorem B1600301 : Blo 1064615 1600301 := bbase (se 3 (by rfl) ⟨300056, by rfl⟩ : syracuseStep 1600301 = 600113) (by norm_num)
theorem B1796917 : Blo 1064615 1796917 := bbase (se 5 (by rfl) ⟨84230, by rfl⟩ : syracuseStep 1796917 = 168461) (by norm_num)
theorem B1600325 : Blo 1064615 1600325 := bbase (se 4 (by rfl) ⟨150030, by rfl⟩ : syracuseStep 1600325 = 300061) (by norm_num)
theorem B2026309 : Blo 1064615 2026309 := bbase (se 4 (by rfl) ⟨189966, by rfl⟩ : syracuseStep 2026309 = 379933) (by norm_num)
theorem B1600349 : Blo 1064615 1600349 := bbase (se 3 (by rfl) ⟨300065, by rfl⟩ : syracuseStep 1600349 = 600131) (by norm_num)
theorem B1600373 : Blo 1064615 1600373 := bbase (se 5 (by rfl) ⟨75017, by rfl⟩ : syracuseStep 1600373 = 150035) (by norm_num)
theorem B1797005 : Blo 1064615 1797005 := bbase (se 3 (by rfl) ⟨336938, by rfl⟩ : syracuseStep 1797005 = 673877) (by norm_num)
theorem B1600397 : Blo 1064615 1600397 := bbase (se 3 (by rfl) ⟨300074, by rfl⟩ : syracuseStep 1600397 = 600149) (by norm_num)
theorem B1600421 : Blo 1064615 1600421 := bbase (se 4 (by rfl) ⟨150039, by rfl⟩ : syracuseStep 1600421 = 300079) (by norm_num)
theorem B1600445 : Blo 1064615 1600445 := bbase (se 3 (by rfl) ⟨300083, by rfl⟩ : syracuseStep 1600445 = 600167) (by norm_num)
theorem B1600469 : Blo 1064615 1600469 := bbase (se 7 (by rfl) ⟨18755, by rfl⟩ : syracuseStep 1600469 = 37511) (by norm_num)
theorem B2026453 : Blo 1064615 2026453 := bbase (se 7 (by rfl) ⟨23747, by rfl⟩ : syracuseStep 2026453 = 47495) (by norm_num)
theorem B1600493 : Blo 1064615 1600493 := bbase (se 3 (by rfl) ⟨300092, by rfl⟩ : syracuseStep 1600493 = 600185) (by norm_num)
theorem B1600517 : Blo 1064615 1600517 := bbase (se 4 (by rfl) ⟨150048, by rfl⟩ : syracuseStep 1600517 = 300097) (by norm_num)
theorem B1797133 : Blo 1064615 1797133 := bbase (se 3 (by rfl) ⟨336962, by rfl⟩ : syracuseStep 1797133 = 673925) (by norm_num)
theorem B3894293 : Blo 1064615 3894293 := bbase (se 6 (by rfl) ⟨91272, by rfl⟩ : syracuseStep 3894293 = 182545) (by norm_num)
theorem B1600541 : Blo 1064615 1600541 := bbase (se 3 (by rfl) ⟨300101, by rfl⟩ : syracuseStep 1600541 = 600203) (by norm_num)
theorem B1731629 : Blo 1064615 1731629 := bbase (se 3 (by rfl) ⟨324680, by rfl⟩ : syracuseStep 1731629 = 649361) (by norm_num)
theorem B1600565 : Blo 1064615 1600565 := bbase (se 5 (by rfl) ⟨75026, by rfl⟩ : syracuseStep 1600565 = 150053) (by norm_num)
theorem B1600589 : Blo 1064615 1600589 := bbase (se 3 (by rfl) ⟨300110, by rfl⟩ : syracuseStep 1600589 = 600221) (by norm_num)
theorem B1797221 : Blo 1064615 1797221 := bbase (se 4 (by rfl) ⟨168489, by rfl⟩ : syracuseStep 1797221 = 336979) (by norm_num)
theorem B1600613 : Blo 1064615 1600613 := bbase (se 4 (by rfl) ⟨150057, by rfl⟩ : syracuseStep 1600613 = 300115) (by norm_num)
theorem B3599477 : Blo 1064615 3599477 := bbase (se 5 (by rfl) ⟨168725, by rfl⟩ : syracuseStep 3599477 = 337451) (by norm_num)
theorem B2026613 : Blo 1064615 2026613 := bbase (se 5 (by rfl) ⟨94997, by rfl⟩ : syracuseStep 2026613 = 189995) (by norm_num)
theorem B1600637 : Blo 1064615 1600637 := bbase (se 3 (by rfl) ⟨300119, by rfl⟩ : syracuseStep 1600637 = 600239) (by norm_num)
theorem B1600661 : Blo 1064615 1600661 := bbase (se 6 (by rfl) ⟨37515, by rfl⟩ : syracuseStep 1600661 = 75031) (by norm_num)
theorem B1141933 : Blo 1064615 1141933 := bbase (se 3 (by rfl) ⟨214112, by rfl⟩ : syracuseStep 1141933 = 428225) (by norm_num)
theorem B1600685 : Blo 1064615 1600685 := bbase (se 3 (by rfl) ⟨300128, by rfl⟩ : syracuseStep 1600685 = 600257) (by norm_num)
theorem B1600709 : Blo 1064615 1600709 := bbase (se 4 (by rfl) ⟨150066, by rfl⟩ : syracuseStep 1600709 = 300133) (by norm_num)
theorem B1600733 : Blo 1064615 1600733 := bbase (se 3 (by rfl) ⟨300137, by rfl⟩ : syracuseStep 1600733 = 600275) (by norm_num)
theorem B1797349 : Blo 1064615 1797349 := bbase (se 4 (by rfl) ⟨168501, by rfl⟩ : syracuseStep 1797349 = 337003) (by norm_num)
theorem B1600757 : Blo 1064615 1600757 := bbase (se 5 (by rfl) ⟨75035, by rfl⟩ : syracuseStep 1600757 = 150071) (by norm_num)
theorem B2026757 : Blo 1064615 2026757 := bbase (se 4 (by rfl) ⟨190008, by rfl⟩ : syracuseStep 2026757 = 380017) (by norm_num)
theorem B1600781 : Blo 1064615 1600781 := bbase (se 3 (by rfl) ⟨300146, by rfl⟩ : syracuseStep 1600781 = 600293) (by norm_num)
theorem B1600805 : Blo 1064615 1600805 := bbase (se 4 (by rfl) ⟨150075, by rfl⟩ : syracuseStep 1600805 = 300151) (by norm_num)
theorem B1797437 : Blo 1064615 1797437 := bbase (se 3 (by rfl) ⟨337019, by rfl⟩ : syracuseStep 1797437 = 674039) (by norm_num)
theorem B1600829 : Blo 1064615 1600829 := bbase (se 3 (by rfl) ⟨300155, by rfl⟩ : syracuseStep 1600829 = 600311) (by norm_num)
theorem B1600853 : Blo 1064615 1600853 := bbase (se 11 (by rfl) ⟨1172, by rfl⟩ : syracuseStep 1600853 = 2345) (by norm_num)
theorem B1600877 : Blo 1064615 1600877 := bbase (se 3 (by rfl) ⟨300164, by rfl⟩ : syracuseStep 1600877 = 600329) (by norm_num)
theorem B1600901 : Blo 1064615 1600901 := bbase (se 4 (by rfl) ⟨150084, by rfl⟩ : syracuseStep 1600901 = 300169) (by norm_num)
theorem B1600925 : Blo 1064615 1600925 := bbase (se 3 (by rfl) ⟨300173, by rfl⟩ : syracuseStep 1600925 = 600347) (by norm_num)
theorem B1600949 : Blo 1064615 1600949 := bbase (se 5 (by rfl) ⟨75044, by rfl⟩ : syracuseStep 1600949 = 150089) (by norm_num)
theorem B1797565 : Blo 1064615 1797565 := bbase (se 3 (by rfl) ⟨337043, by rfl⟩ : syracuseStep 1797565 = 674087) (by norm_num)
theorem B1600973 : Blo 1064615 1600973 := bbase (se 3 (by rfl) ⟨300182, by rfl⟩ : syracuseStep 1600973 = 600365) (by norm_num)
theorem B1600997 : Blo 1064615 1600997 := bbase (se 4 (by rfl) ⟨150093, by rfl⟩ : syracuseStep 1600997 = 300187) (by norm_num)
theorem B1601021 : Blo 1064615 1601021 := bbase (se 3 (by rfl) ⟨300191, by rfl⟩ : syracuseStep 1601021 = 600383) (by norm_num)
theorem B1797653 : Blo 1064615 1797653 := bbase (se 6 (by rfl) ⟨42132, by rfl⟩ : syracuseStep 1797653 = 84265) (by norm_num)
theorem B1601045 : Blo 1064615 1601045 := bbase (se 6 (by rfl) ⟨37524, by rfl⟩ : syracuseStep 1601045 = 75049) (by norm_num)
theorem B3599909 : Blo 1064615 3599909 := bbase (se 4 (by rfl) ⟨337491, by rfl⟩ : syracuseStep 3599909 = 674983) (by norm_num)
theorem B2027045 : Blo 1064615 2027045 := bbase (se 4 (by rfl) ⟨190035, by rfl⟩ : syracuseStep 2027045 = 380071) (by norm_num)
theorem B1601069 : Blo 1064615 1601069 := bbase (se 3 (by rfl) ⟨300200, by rfl⟩ : syracuseStep 1601069 = 600401) (by norm_num)
theorem B1601093 : Blo 1064615 1601093 := bbase (se 4 (by rfl) ⟨150102, by rfl⟩ : syracuseStep 1601093 = 300205) (by norm_num)
theorem B58453589 : Blo 1064615 58453589 := bbase (se 8 (by rfl) ⟨342501, by rfl⟩ : syracuseStep 58453589 = 685003) (by norm_num)
theorem B1601117 : Blo 1064615 1601117 := bbase (se 3 (by rfl) ⟨300209, by rfl⟩ : syracuseStep 1601117 = 600419) (by norm_num)
theorem B5402213 : Blo 1064615 5402213 := bbase (se 4 (by rfl) ⟨506457, by rfl⟩ : syracuseStep 5402213 = 1012915) (by norm_num)
theorem B1601141 : Blo 1064615 1601141 := bbase (se 5 (by rfl) ⟨75053, by rfl⟩ : syracuseStep 1601141 = 150107) (by norm_num)
theorem B1601165 : Blo 1064615 1601165 := bbase (se 3 (by rfl) ⟨300218, by rfl⟩ : syracuseStep 1601165 = 600437) (by norm_num)
theorem B1797781 : Blo 1064615 1797781 := bbase (se 6 (by rfl) ⟨42135, by rfl⟩ : syracuseStep 1797781 = 84271) (by norm_num)
theorem B1601189 : Blo 1064615 1601189 := bbase (se 4 (by rfl) ⟨150111, by rfl⟩ : syracuseStep 1601189 = 300223) (by norm_num)
theorem B1601213 : Blo 1064615 1601213 := bbase (se 3 (by rfl) ⟨300227, by rfl⟩ : syracuseStep 1601213 = 600455) (by norm_num)
theorem B2027197 : Blo 1064615 2027197 := bbase (se 3 (by rfl) ⟨380099, by rfl⟩ : syracuseStep 2027197 = 760199) (by norm_num)
theorem B1601237 : Blo 1064615 1601237 := bbase (se 7 (by rfl) ⟨18764, by rfl⟩ : syracuseStep 1601237 = 37529) (by norm_num)
theorem B1797869 : Blo 1064615 1797869 := bbase (se 3 (by rfl) ⟨337100, by rfl⟩ : syracuseStep 1797869 = 674201) (by norm_num)
theorem B1601261 : Blo 1064615 1601261 := bbase (se 3 (by rfl) ⟨300236, by rfl⟩ : syracuseStep 1601261 = 600473) (by norm_num)
theorem B1601285 : Blo 1064615 1601285 := bbase (se 4 (by rfl) ⟨150120, by rfl⟩ : syracuseStep 1601285 = 300241) (by norm_num)
theorem B1601309 : Blo 1064615 1601309 := bbase (se 3 (by rfl) ⟨300245, by rfl⟩ : syracuseStep 1601309 = 600491) (by norm_num)
theorem B1601333 : Blo 1064615 1601333 := bbase (se 5 (by rfl) ⟨75062, by rfl⟩ : syracuseStep 1601333 = 150125) (by norm_num)
theorem B1601357 : Blo 1064615 1601357 := bbase (se 3 (by rfl) ⟨300254, by rfl⟩ : syracuseStep 1601357 = 600509) (by norm_num)
theorem B2158429 : Blo 1064615 2158429 := bbase (se 3 (by rfl) ⟨404705, by rfl⟩ : syracuseStep 2158429 = 809411) (by norm_num)
theorem B1601381 : Blo 1064615 1601381 := bbase (se 4 (by rfl) ⟨150129, by rfl⟩ : syracuseStep 1601381 = 300259) (by norm_num)
theorem B1797997 : Blo 1064615 1797997 := bbase (se 3 (by rfl) ⟨337124, by rfl⟩ : syracuseStep 1797997 = 674249) (by norm_num)
theorem B1601405 : Blo 1064615 1601405 := bbase (se 3 (by rfl) ⟨300263, by rfl⟩ : syracuseStep 1601405 = 600527) (by norm_num)
theorem B1601429 : Blo 1064615 1601429 := bbase (se 6 (by rfl) ⟨37533, by rfl⟩ : syracuseStep 1601429 = 75067) (by norm_num)
theorem B1601453 : Blo 1064615 1601453 := bbase (se 3 (by rfl) ⟨300272, by rfl⟩ : syracuseStep 1601453 = 600545) (by norm_num)
theorem B1798085 : Blo 1064615 1798085 := bbase (se 4 (by rfl) ⟨168570, by rfl⟩ : syracuseStep 1798085 = 337141) (by norm_num)
theorem B1601477 : Blo 1064615 1601477 := bbase (se 4 (by rfl) ⟨150138, by rfl⟩ : syracuseStep 1601477 = 300277) (by norm_num)
theorem B3600341 : Blo 1064615 3600341 := bbase (se 7 (by rfl) ⟨42191, by rfl⟩ : syracuseStep 3600341 = 84383) (by norm_num)
theorem B1601501 : Blo 1064615 1601501 := bbase (se 3 (by rfl) ⟨300281, by rfl⟩ : syracuseStep 1601501 = 600563) (by norm_num)
theorem B2027501 : Blo 1064615 2027501 := bbase (se 3 (by rfl) ⟨380156, by rfl⟩ : syracuseStep 2027501 = 760313) (by norm_num)
theorem B1601525 : Blo 1064615 1601525 := bbase (se 5 (by rfl) ⟨75071, by rfl⟩ : syracuseStep 1601525 = 150143) (by norm_num)
theorem B1601549 : Blo 1064615 1601549 := bbase (se 3 (by rfl) ⟨300290, by rfl⟩ : syracuseStep 1601549 = 600581) (by norm_num)
theorem B1601573 : Blo 1064615 1601573 := bbase (se 4 (by rfl) ⟨150147, by rfl⟩ : syracuseStep 1601573 = 300295) (by norm_num)
theorem B1601597 : Blo 1064615 1601597 := bbase (se 3 (by rfl) ⟨300299, by rfl⟩ : syracuseStep 1601597 = 600599) (by norm_num)
theorem B1798213 : Blo 1064615 1798213 := bbase (se 4 (by rfl) ⟨168582, by rfl⟩ : syracuseStep 1798213 = 337165) (by norm_num)
theorem B1601621 : Blo 1064615 1601621 := bbase (se 8 (by rfl) ⟨9384, by rfl⟩ : syracuseStep 1601621 = 18769) (by norm_num)
theorem B1601645 : Blo 1064615 1601645 := bbase (se 3 (by rfl) ⟨300308, by rfl⟩ : syracuseStep 1601645 = 600617) (by norm_num)
theorem B1601669 : Blo 1064615 1601669 := bbase (se 4 (by rfl) ⟨150156, by rfl⟩ : syracuseStep 1601669 = 300313) (by norm_num)
theorem B1798301 : Blo 1064615 1798301 := bbase (se 3 (by rfl) ⟨337181, by rfl⟩ : syracuseStep 1798301 = 674363) (by norm_num)
theorem B1601693 : Blo 1064615 1601693 := bbase (se 3 (by rfl) ⟨300317, by rfl⟩ : syracuseStep 1601693 = 600635) (by norm_num)
theorem B1601717 : Blo 1064615 1601717 := bbase (se 5 (by rfl) ⟨75080, by rfl⟩ : syracuseStep 1601717 = 150161) (by norm_num)
theorem B3338437 : Blo 1064615 3338437 := bbase (se 4 (by rfl) ⟨312978, by rfl⟩ : syracuseStep 3338437 = 625957) (by norm_num)
theorem B1601741 : Blo 1064615 1601741 := bbase (se 3 (by rfl) ⟨300326, by rfl⟩ : syracuseStep 1601741 = 600653) (by norm_num)
theorem B1405153 : Blo 1064615 1405153 := bbase (se 2 (by rfl) ⟨526932, by rfl⟩ : syracuseStep 1405153 = 1053865) (by norm_num)
theorem B1601765 : Blo 1064615 1601765 := bbase (se 4 (by rfl) ⟨150165, by rfl⟩ : syracuseStep 1601765 = 300331) (by norm_num)
theorem B1601789 : Blo 1064615 1601789 := bbase (se 3 (by rfl) ⟨300335, by rfl⟩ : syracuseStep 1601789 = 600671) (by norm_num)
theorem B2879765 : Blo 1064615 2879765 := bbase (se 6 (by rfl) ⟨67494, by rfl⟩ : syracuseStep 2879765 = 134989) (by norm_num)
theorem B1601813 : Blo 1064615 1601813 := bbase (se 6 (by rfl) ⟨37542, by rfl⟩ : syracuseStep 1601813 = 75085) (by norm_num)
theorem B1798429 : Blo 1064615 1798429 := bbase (se 3 (by rfl) ⟨337205, by rfl⟩ : syracuseStep 1798429 = 674411) (by norm_num)
theorem B1601837 : Blo 1064615 1601837 := bbase (se 3 (by rfl) ⟨300344, by rfl⟩ : syracuseStep 1601837 = 600689) (by norm_num)
theorem B1601861 : Blo 1064615 1601861 := bbase (se 4 (by rfl) ⟨150174, by rfl⟩ : syracuseStep 1601861 = 300349) (by norm_num)
theorem B1601885 : Blo 1064615 1601885 := bbase (se 3 (by rfl) ⟨300353, by rfl⟩ : syracuseStep 1601885 = 600707) (by norm_num)
theorem B2158949 : Blo 1064615 2158949 := bbase (se 4 (by rfl) ⟨202401, by rfl⟩ : syracuseStep 2158949 = 404803) (by norm_num)
theorem B1798517 : Blo 1064615 1798517 := bbase (se 5 (by rfl) ⟨84305, by rfl⟩ : syracuseStep 1798517 = 168611) (by norm_num)
theorem B1601909 : Blo 1064615 1601909 := bbase (se 5 (by rfl) ⟨75089, by rfl⟩ : syracuseStep 1601909 = 150179) (by norm_num)
theorem B3600773 : Blo 1064615 3600773 := bbase (se 4 (by rfl) ⟨337572, by rfl⟩ : syracuseStep 3600773 = 675145) (by norm_num)
theorem B1601933 : Blo 1064615 1601933 := bbase (se 3 (by rfl) ⟨300362, by rfl⟩ : syracuseStep 1601933 = 600725) (by norm_num)
theorem B1601957 : Blo 1064615 1601957 := bbase (se 4 (by rfl) ⟨150183, by rfl⟩ : syracuseStep 1601957 = 300367) (by norm_num)
theorem B1601981 : Blo 1064615 1601981 := bbase (se 3 (by rfl) ⟨300371, by rfl⟩ : syracuseStep 1601981 = 600743) (by norm_num)
theorem B1602005 : Blo 1064615 1602005 := bbase (se 7 (by rfl) ⟨18773, by rfl⟩ : syracuseStep 1602005 = 37547) (by norm_num)
theorem B1602029 : Blo 1064615 1602029 := bbase (se 3 (by rfl) ⟨300380, by rfl⟩ : syracuseStep 1602029 = 600761) (by norm_num)
theorem B1798645 : Blo 1064615 1798645 := bbase (se 5 (by rfl) ⟨84311, by rfl⟩ : syracuseStep 1798645 = 168623) (by norm_num)
theorem B1602053 : Blo 1064615 1602053 := bbase (se 4 (by rfl) ⟨150192, by rfl⟩ : syracuseStep 1602053 = 300385) (by norm_num)
theorem B1602077 : Blo 1064615 1602077 := bbase (se 3 (by rfl) ⟨300389, by rfl⟩ : syracuseStep 1602077 = 600779) (by norm_num)
theorem B1602101 : Blo 1064615 1602101 := bbase (se 5 (by rfl) ⟨75098, by rfl⟩ : syracuseStep 1602101 = 150197) (by norm_num)
theorem B1798733 : Blo 1064615 1798733 := bbase (se 3 (by rfl) ⟨337262, by rfl⟩ : syracuseStep 1798733 = 674525) (by norm_num)
theorem B1602125 : Blo 1064615 1602125 := bbase (se 3 (by rfl) ⟨300398, by rfl⟩ : syracuseStep 1602125 = 600797) (by norm_num)
theorem B1602149 : Blo 1064615 1602149 := bbase (se 4 (by rfl) ⟨150201, by rfl⟩ : syracuseStep 1602149 = 300403) (by norm_num)
theorem B1602173 : Blo 1064615 1602173 := bbase (se 3 (by rfl) ⟨300407, by rfl⟩ : syracuseStep 1602173 = 600815) (by norm_num)
theorem B1602197 : Blo 1064615 1602197 := bbase (se 6 (by rfl) ⟨37551, by rfl⟩ : syracuseStep 1602197 = 75103) (by norm_num)
theorem B1602221 : Blo 1064615 1602221 := bbase (se 3 (by rfl) ⟨300416, by rfl⟩ : syracuseStep 1602221 = 600833) (by norm_num)
theorem B1602245 : Blo 1064615 1602245 := bbase (se 4 (by rfl) ⟨150210, by rfl⟩ : syracuseStep 1602245 = 300421) (by norm_num)
theorem B1798861 : Blo 1064615 1798861 := bbase (se 3 (by rfl) ⟨337286, by rfl⟩ : syracuseStep 1798861 = 674573) (by norm_num)
theorem B1602269 : Blo 1064615 1602269 := bbase (se 3 (by rfl) ⟨300425, by rfl⟩ : syracuseStep 1602269 = 600851) (by norm_num)
theorem B2028253 : Blo 1064615 2028253 := bbase (se 3 (by rfl) ⟨380297, by rfl⟩ : syracuseStep 2028253 = 760595) (by norm_num)
theorem B1602293 : Blo 1064615 1602293 := bbase (se 5 (by rfl) ⟨75107, by rfl⟩ : syracuseStep 1602293 = 150215) (by norm_num)
theorem B1602317 : Blo 1064615 1602317 := bbase (se 3 (by rfl) ⟨300434, by rfl⟩ : syracuseStep 1602317 = 600869) (by norm_num)
theorem B1798949 : Blo 1064615 1798949 := bbase (se 4 (by rfl) ⟨168651, by rfl⟩ : syracuseStep 1798949 = 337303) (by norm_num)
theorem B1602341 : Blo 1064615 1602341 := bbase (se 4 (by rfl) ⟨150219, by rfl⟩ : syracuseStep 1602341 = 300439) (by norm_num)
theorem B3601205 : Blo 1064615 3601205 := bbase (se 5 (by rfl) ⟨168806, by rfl⟩ : syracuseStep 3601205 = 337613) (by norm_num)
theorem B1602365 : Blo 1064615 1602365 := bbase (se 3 (by rfl) ⟨300443, by rfl⟩ : syracuseStep 1602365 = 600887) (by norm_num)
theorem B1602389 : Blo 1064615 1602389 := bbase (se 9 (by rfl) ⟨4694, by rfl⟩ : syracuseStep 1602389 = 9389) (by norm_num)
theorem B3240805 : Blo 1064615 3240805 := bbase (se 4 (by rfl) ⟨303825, by rfl⟩ : syracuseStep 3240805 = 607651) (by norm_num)
theorem B1602413 : Blo 1064615 1602413 := bbase (se 3 (by rfl) ⟨300452, by rfl⟩ : syracuseStep 1602413 = 600905) (by norm_num)
theorem B2028397 : Blo 1064615 2028397 := bbase (se 3 (by rfl) ⟨380324, by rfl⟩ : syracuseStep 2028397 = 760649) (by norm_num)
theorem B9237365 : Blo 1064615 9237365 := bbase (se 5 (by rfl) ⟨433001, by rfl⟩ : syracuseStep 9237365 = 866003) (by norm_num)
theorem B5403509 : Blo 1064615 5403509 := bbase (se 5 (by rfl) ⟨253289, by rfl⟩ : syracuseStep 5403509 = 506579) (by norm_num)
theorem B1602437 : Blo 1064615 1602437 := bbase (se 4 (by rfl) ⟨150228, by rfl⟩ : syracuseStep 1602437 = 300457) (by norm_num)
theorem B1602461 : Blo 1064615 1602461 := bbase (se 3 (by rfl) ⟨300461, by rfl⟩ : syracuseStep 1602461 = 600923) (by norm_num)
theorem B1799077 : Blo 1064615 1799077 := bbase (se 4 (by rfl) ⟨168663, by rfl⟩ : syracuseStep 1799077 = 337327) (by norm_num)
theorem B1602485 : Blo 1064615 1602485 := bbase (se 5 (by rfl) ⟨75116, by rfl⟩ : syracuseStep 1602485 = 150233) (by norm_num)
theorem B1602509 : Blo 1064615 1602509 := bbase (se 3 (by rfl) ⟨300470, by rfl⟩ : syracuseStep 1602509 = 600941) (by norm_num)
theorem B1602533 : Blo 1064615 1602533 := bbase (se 4 (by rfl) ⟨150237, by rfl⟩ : syracuseStep 1602533 = 300475) (by norm_num)
theorem B1799165 : Blo 1064615 1799165 := bbase (se 3 (by rfl) ⟨337343, by rfl⟩ : syracuseStep 1799165 = 674687) (by norm_num)
theorem B1602557 : Blo 1064615 1602557 := bbase (se 3 (by rfl) ⟨300479, by rfl⟩ : syracuseStep 1602557 = 600959) (by norm_num)
theorem B2028557 : Blo 1064615 2028557 := bbase (se 3 (by rfl) ⟨380354, by rfl⟩ : syracuseStep 2028557 = 760709) (by norm_num)
theorem B1602581 : Blo 1064615 1602581 := bbase (se 6 (by rfl) ⟨37560, by rfl⟩ : syracuseStep 1602581 = 75121) (by norm_num)
theorem B1602605 : Blo 1064615 1602605 := bbase (se 3 (by rfl) ⟨300488, by rfl⟩ : syracuseStep 1602605 = 600977) (by norm_num)
theorem B1602629 : Blo 1064615 1602629 := bbase (se 4 (by rfl) ⟨150246, by rfl⟩ : syracuseStep 1602629 = 300493) (by norm_num)
theorem B1602653 : Blo 1064615 1602653 := bbase (se 3 (by rfl) ⟨300497, by rfl⟩ : syracuseStep 1602653 = 600995) (by norm_num)
theorem B1602677 : Blo 1064615 1602677 := bbase (se 5 (by rfl) ⟨75125, by rfl⟩ : syracuseStep 1602677 = 150251) (by norm_num)
theorem B1799293 : Blo 1064615 1799293 := bbase (se 3 (by rfl) ⟨337367, by rfl⟩ : syracuseStep 1799293 = 674735) (by norm_num)
theorem B1602701 : Blo 1064615 1602701 := bbase (se 3 (by rfl) ⟨300506, by rfl⟩ : syracuseStep 1602701 = 601013) (by norm_num)
theorem B2028701 : Blo 1064615 2028701 := bbase (se 3 (by rfl) ⟨380381, by rfl⟩ : syracuseStep 2028701 = 760763) (by norm_num)
theorem B1602725 : Blo 1064615 1602725 := bbase (se 4 (by rfl) ⟨150255, by rfl⟩ : syracuseStep 1602725 = 300511) (by norm_num)
theorem B4617397 : Blo 1064615 4617397 := bbase (se 5 (by rfl) ⟨216440, by rfl⟩ : syracuseStep 4617397 = 432881) (by norm_num)
theorem B1733813 : Blo 1064615 1733813 := bbase (se 5 (by rfl) ⟨81272, by rfl⟩ : syracuseStep 1733813 = 162545) (by norm_num)
theorem B1602749 : Blo 1064615 1602749 := bbase (se 3 (by rfl) ⟨300515, by rfl⟩ : syracuseStep 1602749 = 601031) (by norm_num)
theorem B1799381 : Blo 1064615 1799381 := bbase (se 7 (by rfl) ⟨21086, by rfl⟩ : syracuseStep 1799381 = 42173) (by norm_num)
theorem B1602773 : Blo 1064615 1602773 := bbase (se 7 (by rfl) ⟨18782, by rfl⟩ : syracuseStep 1602773 = 37565) (by norm_num)
theorem B3601637 : Blo 1064615 3601637 := bbase (se 4 (by rfl) ⟨337653, by rfl⟩ : syracuseStep 3601637 = 675307) (by norm_num)
theorem B1602797 : Blo 1064615 1602797 := bbase (se 3 (by rfl) ⟨300524, by rfl⟩ : syracuseStep 1602797 = 601049) (by norm_num)
theorem B2192645 : Blo 1064615 2192645 := bbase (se 4 (by rfl) ⟨205560, by rfl⟩ : syracuseStep 2192645 = 411121) (by norm_num)
theorem B1602821 : Blo 1064615 1602821 := bbase (se 4 (by rfl) ⟨150264, by rfl⟩ : syracuseStep 1602821 = 300529) (by norm_num)
theorem B1602845 : Blo 1064615 1602845 := bbase (se 3 (by rfl) ⟨300533, by rfl⟩ : syracuseStep 1602845 = 601067) (by norm_num)
theorem B1602869 : Blo 1064615 1602869 := bbase (se 5 (by rfl) ⟨75134, by rfl⟩ : syracuseStep 1602869 = 150269) (by norm_num)
theorem B1602893 : Blo 1064615 1602893 := bbase (se 3 (by rfl) ⟨300542, by rfl⟩ : syracuseStep 1602893 = 601085) (by norm_num)
theorem B1799509 : Blo 1064615 1799509 := bbase (se 13 (by rfl) ⟨329, by rfl⟩ : syracuseStep 1799509 = 659) (by norm_num)
theorem B4552037 : Blo 1064615 4552037 := bbase (se 4 (by rfl) ⟨426753, by rfl⟩ : syracuseStep 4552037 = 853507) (by norm_num)
theorem B1602917 : Blo 1064615 1602917 := bbase (se 4 (by rfl) ⟨150273, by rfl⟩ : syracuseStep 1602917 = 300547) (by norm_num)
theorem B1799597 : Blo 1064615 1799597 := bbase (se 3 (by rfl) ⟨337424, by rfl⟩ : syracuseStep 1799597 = 674849) (by norm_num)
theorem B8648117 : Blo 1064615 8648117 := bbase (se 5 (by rfl) ⟨405380, by rfl⟩ : syracuseStep 8648117 = 810761) (by norm_num)
theorem B2192861 : Blo 1064615 2192861 := bbase (se 3 (by rfl) ⟨411161, by rfl⟩ : syracuseStep 2192861 = 822323) (by norm_num)
theorem B1799725 : Blo 1064615 1799725 := bbase (se 3 (by rfl) ⟨337448, by rfl⟩ : syracuseStep 1799725 = 674897) (by norm_num)
theorem B1799813 : Blo 1064615 1799813 := bbase (se 4 (by rfl) ⟨168732, by rfl⟩ : syracuseStep 1799813 = 337465) (by norm_num)
theorem B3602069 : Blo 1064615 3602069 := bbase (se 6 (by rfl) ⟨84423, by rfl⟩ : syracuseStep 3602069 = 168847) (by norm_num)
theorem B1439461 : Blo 1064615 1439461 := bbase (se 4 (by rfl) ⟨134949, by rfl⟩ : syracuseStep 1439461 = 269899) (by norm_num)
theorem B1799941 : Blo 1064615 1799941 := bbase (se 4 (by rfl) ⟨168744, by rfl⟩ : syracuseStep 1799941 = 337489) (by norm_num)
theorem B8091413 : Blo 1064615 8091413 := bbase (se 6 (by rfl) ⟨189642, by rfl⟩ : syracuseStep 8091413 = 379285) (by norm_num)
theorem B1800029 : Blo 1064615 1800029 := bbase (se 3 (by rfl) ⟨337505, by rfl⟩ : syracuseStep 1800029 = 675011) (by norm_num)
theorem B7305173 : Blo 1064615 7305173 := bbase (se 7 (by rfl) ⟨85607, by rfl⟩ : syracuseStep 7305173 = 171215) (by norm_num)
theorem B1800157 : Blo 1064615 1800157 := bbase (se 3 (by rfl) ⟨337529, by rfl⟩ : syracuseStep 1800157 = 675059) (by norm_num)
theorem B1800245 : Blo 1064615 1800245 := bbase (se 5 (by rfl) ⟨84386, by rfl⟩ : syracuseStep 1800245 = 168773) (by norm_num)
theorem B3602501 : Blo 1064615 3602501 := bbase (se 4 (by rfl) ⟨337734, by rfl⟩ : syracuseStep 3602501 = 675469) (by norm_num)
theorem B1079425 : Blo 1064615 1079425 := bbase (se 2 (by rfl) ⟨404784, by rfl⟩ : syracuseStep 1079425 = 809569) (by norm_num)
theorem B5404805 : Blo 1064615 5404805 := bbase (se 4 (by rfl) ⟨506700, by rfl⟩ : syracuseStep 5404805 = 1013401) (by norm_num)
theorem B1800373 : Blo 1064615 1800373 := bbase (se 5 (by rfl) ⟨84392, by rfl⟩ : syracuseStep 1800373 = 168785) (by norm_num)
theorem B1800461 : Blo 1064615 1800461 := bbase (se 3 (by rfl) ⟨337586, by rfl⟩ : syracuseStep 1800461 = 675173) (by norm_num)
theorem B1440077 : Blo 1064615 1440077 := bbase (se 3 (by rfl) ⟨270014, by rfl⟩ : syracuseStep 1440077 = 540029) (by norm_num)
theorem B1800589 : Blo 1064615 1800589 := bbase (se 3 (by rfl) ⟨337610, by rfl⟩ : syracuseStep 1800589 = 675221) (by norm_num)
theorem B1800677 : Blo 1064615 1800677 := bbase (se 4 (by rfl) ⟨168813, by rfl⟩ : syracuseStep 1800677 = 337627) (by norm_num)
theorem B3602933 : Blo 1064615 3602933 := bbase (se 5 (by rfl) ⟨168887, by rfl⟩ : syracuseStep 3602933 = 337775) (by norm_num)
theorem B1800805 : Blo 1064615 1800805 := bbase (se 4 (by rfl) ⟨168825, by rfl⟩ : syracuseStep 1800805 = 337651) (by norm_num)
theorem B1440445 : Blo 1064615 1440445 := bbase (se 3 (by rfl) ⟨270083, by rfl⟩ : syracuseStep 1440445 = 540167) (by norm_num)
theorem B1800893 : Blo 1064615 1800893 := bbase (se 3 (by rfl) ⟨337667, by rfl⟩ : syracuseStep 1800893 = 675335) (by norm_num)
theorem B1801021 : Blo 1064615 1801021 := bbase (se 3 (by rfl) ⟨337691, by rfl⟩ : syracuseStep 1801021 = 675383) (by norm_num)
theorem B1440661 : Blo 1064615 1440661 := bbase (se 6 (by rfl) ⟨33765, by rfl⟩ : syracuseStep 1440661 = 67531) (by norm_num)
theorem B1801109 : Blo 1064615 1801109 := bbase (se 6 (by rfl) ⟨42213, by rfl⟩ : syracuseStep 1801109 = 84427) (by norm_num)
theorem B3603365 : Blo 1064615 3603365 := bbase (se 4 (by rfl) ⟨337815, by rfl⟩ : syracuseStep 3603365 = 675631) (by norm_num)
theorem B1801237 : Blo 1064615 1801237 := bbase (se 6 (by rfl) ⟨42216, by rfl⟩ : syracuseStep 1801237 = 84433) (by norm_num)
theorem B1440829 : Blo 1064615 1440829 := bbase (se 3 (by rfl) ⟨270155, by rfl⟩ : syracuseStep 1440829 = 540311) (by norm_num)
theorem B4553813 : Blo 1064615 4553813 := bbase (se 8 (by rfl) ⟨26682, by rfl⟩ : syracuseStep 4553813 = 53365) (by norm_num)
theorem B1440877 : Blo 1064615 1440877 := bbase (se 3 (by rfl) ⟨270164, by rfl⟩ : syracuseStep 1440877 = 540329) (by norm_num)
theorem B1801325 : Blo 1064615 1801325 := bbase (se 3 (by rfl) ⟨337748, by rfl⟩ : syracuseStep 1801325 = 675497) (by norm_num)
theorem B1801453 : Blo 1064615 1801453 := bbase (se 3 (by rfl) ⟨337772, by rfl⟩ : syracuseStep 1801453 = 675545) (by norm_num)
theorem B4554053 : Blo 1064615 4554053 := bbase (se 4 (by rfl) ⟨426942, by rfl⟩ : syracuseStep 4554053 = 853885) (by norm_num)
theorem B1801541 : Blo 1064615 1801541 := bbase (se 4 (by rfl) ⟨168894, by rfl⟩ : syracuseStep 1801541 = 337789) (by norm_num)
theorem B3603797 : Blo 1064615 3603797 := bbase (se 11 (by rfl) ⟨2639, by rfl⟩ : syracuseStep 3603797 = 5279) (by norm_num)
theorem B10255733 : Blo 1064615 10255733 := bbase (se 5 (by rfl) ⟨480737, by rfl⟩ : syracuseStep 10255733 = 961475) (by norm_num)
theorem B5406101 : Blo 1064615 5406101 := bbase (se 6 (by rfl) ⟨126705, by rfl⟩ : syracuseStep 5406101 = 253411) (by norm_num)
theorem B1801669 : Blo 1064615 1801669 := bbase (se 4 (by rfl) ⟨168906, by rfl⟩ : syracuseStep 1801669 = 337813) (by norm_num)
theorem B1801757 : Blo 1064615 1801757 := bbase (se 3 (by rfl) ⟨337829, by rfl⟩ : syracuseStep 1801757 = 675659) (by norm_num)
theorem B5766709 : Blo 1064615 5766709 := bbase (se 5 (by rfl) ⟨270314, by rfl⟩ : syracuseStep 5766709 = 540629) (by norm_num)
theorem B1801885 : Blo 1064615 1801885 := bbase (se 3 (by rfl) ⟨337853, by rfl⟩ : syracuseStep 1801885 = 675707) (by norm_num)
theorem B1801973 : Blo 1064615 1801973 := bbase (se 5 (by rfl) ⟨84467, by rfl⟩ : syracuseStep 1801973 = 168935) (by norm_num)
theorem B3604229 : Blo 1064615 3604229 := bbase (se 4 (by rfl) ⟨337896, by rfl⟩ : syracuseStep 3604229 = 675793) (by norm_num)
theorem B1802101 : Blo 1064615 1802101 := bbase (se 5 (by rfl) ⟨84473, by rfl⟩ : syracuseStep 1802101 = 168947) (by norm_num)
theorem B1802189 : Blo 1064615 1802189 := bbase (se 3 (by rfl) ⟨337910, by rfl⟩ : syracuseStep 1802189 = 675821) (by norm_num)
theorem B1802243 : Blo 1064615 1802243 := bstep (se 1 (by rfl) ⟨1351682, by rfl⟩ : syracuseStep 1802243 = 2703365) B2703365
theorem B3244141 : Blo 1064615 3244141 := bstep (se 3 (by rfl) ⟨608276, by rfl⟩ : syracuseStep 3244141 = 1216553) B1216553
theorem B2162801 : Blo 1064615 2162801 := bstep (se 2 (by rfl) ⟨811050, by rfl⟩ : syracuseStep 2162801 = 1622101) B1622101
theorem B1802371 : Blo 1064615 1802371 := bstep (se 1 (by rfl) ⟨1351778, by rfl⟩ : syracuseStep 1802371 = 2703557) B2703557
theorem B9109745 : Blo 1064615 9109745 := bstep (se 2 (by rfl) ⟨3416154, by rfl⟩ : syracuseStep 9109745 = 6832309) B6832309
theorem B1802513 : Blo 1064615 1802513 := bstep (se 2 (by rfl) ⟨675942, by rfl⟩ : syracuseStep 1802513 = 1351885) B1351885
theorem B2883917 : Blo 1064615 2883917 := bstep (se 3 (by rfl) ⟨540734, by rfl⟩ : syracuseStep 2883917 = 1081469) B1081469
theorem B3604877 : Blo 1064615 3604877 := bstep (se 3 (by rfl) ⟨675914, by rfl⟩ : syracuseStep 3604877 = 1351829) B1351829
theorem B1802641 : Blo 1064615 1802641 := bstep (se 2 (by rfl) ⟨675990, by rfl⟩ : syracuseStep 1802641 = 1351981) B1351981
theorem B1802675 : Blo 1064615 1802675 := bstep (se 1 (by rfl) ⟨1352006, by rfl⟩ : syracuseStep 1802675 = 2704013) B2704013
theorem B3604931 : Blo 1064615 3604931 := bstep (se 1 (by rfl) ⟨2703698, by rfl⟩ : syracuseStep 3604931 = 5407397) B5407397
theorem B1540561 : Blo 1064615 1540561 := bstep (se 2 (by rfl) ⟨577710, by rfl⟩ : syracuseStep 1540561 = 1155421) B1155421
theorem B1802803 : Blo 1064615 1802803 := bstep (se 1 (by rfl) ⟨1352102, by rfl⟩ : syracuseStep 1802803 = 2704205) B2704205
theorem B9732707 : Blo 1064615 9732707 := bstep (se 1 (by rfl) ⟨7299530, by rfl⟩ : syracuseStep 9732707 = 14599061) B14599061
theorem B1802945 : Blo 1064615 1802945 := bstep (se 2 (by rfl) ⟨676104, by rfl⟩ : syracuseStep 1802945 = 1352209) B1352209
theorem B3605201 : Blo 1064615 3605201 := bstep (se 2 (by rfl) ⟨1351950, by rfl⟩ : syracuseStep 3605201 = 2703901) B2703901
theorem B1803073 : Blo 1064615 1803073 := bstep (se 2 (by rfl) ⟨676152, by rfl⟩ : syracuseStep 1803073 = 1352305) B1352305
theorem B1803107 : Blo 1064615 1803107 := bstep (se 1 (by rfl) ⟨1352330, by rfl⟩ : syracuseStep 1803107 = 2704661) B2704661
theorem B1803235 : Blo 1064615 1803235 := bstep (se 1 (by rfl) ⟨1352426, by rfl⟩ : syracuseStep 1803235 = 2704853) B2704853
theorem B5473457 : Blo 1064615 5473457 := bstep (se 2 (by rfl) ⟨2052546, by rfl⟩ : syracuseStep 5473457 = 4105093) B4105093
theorem B3605741 : Blo 1064615 3605741 := bstep (se 3 (by rfl) ⟨676076, by rfl⟩ : syracuseStep 3605741 = 1352153) B1352153
theorem B3605795 : Blo 1064615 3605795 := bstep (se 1 (by rfl) ⟨2704346, by rfl⟩ : syracuseStep 3605795 = 5408693) B5408693
theorem B12158261 : Blo 1064615 12158261 := bstep (se 5 (by rfl) ⟨569918, by rfl⟩ : syracuseStep 12158261 = 1139837) B1139837
theorem B3081731 : Blo 1064615 3081731 := bstep (se 1 (by rfl) ⟨2311298, by rfl⟩ : syracuseStep 3081731 = 4622597) B4622597
theorem B3606065 : Blo 1064615 3606065 := bstep (se 2 (by rfl) ⟨1352274, by rfl⟩ : syracuseStep 3606065 = 2704549) B2704549
theorem B8095301 : Blo 1064615 8095301 := bstep (se 4 (by rfl) ⟨758934, by rfl⟩ : syracuseStep 8095301 = 1517869) B1517869
theorem B1705553 : Blo 1064615 1705553 := bstep (se 2 (by rfl) ⟨639582, by rfl⟩ : syracuseStep 1705553 = 1279165) B1279165
theorem B5408369 : Blo 1064615 5408369 := bstep (se 2 (by rfl) ⟨2028138, by rfl⟩ : syracuseStep 5408369 = 4056277) B4056277
theorem B1279891 : Blo 1064615 1279891 := bstep (se 1 (by rfl) ⟨959918, by rfl⟩ : syracuseStep 1279891 = 1919837) B1919837
theorem B2164657 : Blo 1064615 2164657 := bstep (se 2 (by rfl) ⟨811746, by rfl⟩ : syracuseStep 2164657 = 1623493) B1623493
theorem B1706065 : Blo 1064615 1706065 := bstep (se 2 (by rfl) ⟨639774, by rfl⟩ : syracuseStep 1706065 = 1279549) B1279549
theorem B35063921 : Blo 1064615 35063921 := bstep (se 2 (by rfl) ⟨13148970, by rfl⟩ : syracuseStep 35063921 = 26297941) B26297941
theorem B2885905 : Blo 1064615 2885905 := bstep (se 2 (by rfl) ⟨1082214, by rfl⟩ : syracuseStep 2885905 = 2164429) B2164429
theorem B10521413 : Blo 1064615 10521413 := bstep (se 4 (by rfl) ⟨986382, by rfl⟩ : syracuseStep 10521413 = 1972765) B1972765
theorem B3246961 : Blo 1064615 3246961 := bstep (se 2 (by rfl) ⟨1217610, by rfl⟩ : syracuseStep 3246961 = 2435221) B2435221
theorem B1641377 : Blo 1064615 1641377 := bstep (se 2 (by rfl) ⟨615516, by rfl⟩ : syracuseStep 1641377 = 1231033) B1231033
theorem B5409827 : Blo 1064615 5409827 := bstep (se 1 (by rfl) ⟨4057370, by rfl⟩ : syracuseStep 5409827 = 8114741) B8114741
theorem B1707347 : Blo 1064615 1707347 := bstep (se 1 (by rfl) ⟨1280510, by rfl⟩ : syracuseStep 1707347 = 2561021) B2561021
theorem B5475761 : Blo 1064615 5475761 := bstep (se 2 (by rfl) ⟨2053410, by rfl⟩ : syracuseStep 5475761 = 4106821) B4106821
theorem B2395601 : Blo 1064615 2395601 := bstep (se 2 (by rfl) ⟨898350, by rfl⟩ : syracuseStep 2395601 = 1796701) B1796701
theorem B1707475 : Blo 1064615 1707475 := bstep (se 1 (by rfl) ⟨1280606, by rfl⟩ : syracuseStep 1707475 = 2561213) B2561213
theorem B2395619 : Blo 1064615 2395619 := bstep (se 1 (by rfl) ⟨1796714, by rfl⟩ : syracuseStep 2395619 = 3593429) B3593429
theorem B1707617 : Blo 1064615 1707617 := bstep (se 2 (by rfl) ⟨640356, by rfl⟩ : syracuseStep 1707617 = 1280713) B1280713
theorem B1281683 : Blo 1064615 1281683 := bstep (se 1 (by rfl) ⟨961262, by rfl⟩ : syracuseStep 1281683 = 1922525) B1922525
theorem B3247811 : Blo 1064615 3247811 := bstep (se 1 (by rfl) ⟨2435858, by rfl⟩ : syracuseStep 3247811 = 4871717) B4871717
theorem B2395889 : Blo 1064615 2395889 := bstep (se 2 (by rfl) ⟨898458, by rfl⟩ : syracuseStep 2395889 = 1796917) B1796917
theorem B2395907 : Blo 1064615 2395907 := bstep (se 1 (by rfl) ⟨1796930, by rfl⟩ : syracuseStep 2395907 = 3593861) B3593861
theorem B3411811 : Blo 1064615 3411811 := bstep (se 1 (by rfl) ⟨2558858, by rfl⟩ : syracuseStep 3411811 = 5117717) B5117717
theorem B1707905 : Blo 1064615 1707905 := bstep (se 2 (by rfl) ⟨640464, by rfl⟩ : syracuseStep 1707905 = 1280929) B1280929
theorem B3411875 : Blo 1064615 3411875 := bstep (se 1 (by rfl) ⟨2558906, by rfl⟩ : syracuseStep 3411875 = 5117813) B5117813
theorem B3411953 : Blo 1064615 3411953 := bstep (se 2 (by rfl) ⟨1279482, by rfl⟩ : syracuseStep 3411953 = 2558965) B2558965
theorem B2396177 : Blo 1064615 2396177 := bstep (se 2 (by rfl) ⟨898566, by rfl⟩ : syracuseStep 2396177 = 1797133) B1797133
theorem B2396195 : Blo 1064615 2396195 := bstep (se 1 (by rfl) ⟨1797146, by rfl⟩ : syracuseStep 2396195 = 3594293) B3594293
theorem B1282163 : Blo 1064615 1282163 := bstep (se 1 (by rfl) ⟨961622, by rfl⟩ : syracuseStep 1282163 = 1923245) B1923245
theorem B1642673 : Blo 1064615 1642673 := bstep (se 2 (by rfl) ⟨616002, by rfl⟩ : syracuseStep 1642673 = 1232005) B1232005
theorem B1347779 : Blo 1064615 1347779 := bstep (se 1 (by rfl) ⟨1010834, by rfl⟩ : syracuseStep 1347779 = 2021669) B2021669
theorem B6066373 : Blo 1064615 6066373 := bstep (se 4 (by rfl) ⟨568722, by rfl⟩ : syracuseStep 6066373 = 1137445) B1137445
theorem B4559075 : Blo 1064615 4559075 := bstep (se 1 (by rfl) ⟨3419306, by rfl⟩ : syracuseStep 4559075 = 6838613) B6838613
theorem B2396465 : Blo 1064615 2396465 := bstep (se 2 (by rfl) ⟨898674, by rfl⟩ : syracuseStep 2396465 = 1797349) B1797349
theorem B2396483 : Blo 1064615 2396483 := bstep (se 1 (by rfl) ⟨1797362, by rfl⟩ : syracuseStep 2396483 = 3594725) B3594725
theorem B12325445 : Blo 1064615 12325445 := bstep (se 4 (by rfl) ⟨1155510, by rfl⟩ : syracuseStep 12325445 = 2311021) B2311021
theorem B2396753 : Blo 1064615 2396753 := bstep (se 2 (by rfl) ⟨898782, by rfl⟩ : syracuseStep 2396753 = 1797565) B1797565
theorem B2396771 : Blo 1064615 2396771 := bstep (se 1 (by rfl) ⟨1797578, by rfl⟩ : syracuseStep 2396771 = 3595157) B3595157
theorem B3248785 : Blo 1064615 3248785 := bstep (se 2 (by rfl) ⟨1218294, by rfl⟩ : syracuseStep 3248785 = 2436589) B2436589
theorem B1708705 : Blo 1064615 1708705 := bstep (se 2 (by rfl) ⟨640764, by rfl⟩ : syracuseStep 1708705 = 1281529) B1281529
theorem B2397041 : Blo 1064615 2397041 := bstep (se 2 (by rfl) ⟨898890, by rfl⟩ : syracuseStep 2397041 = 1797781) B1797781
theorem B2397059 : Blo 1064615 2397059 := bstep (se 1 (by rfl) ⟨1797794, by rfl⟩ : syracuseStep 2397059 = 3595589) B3595589
theorem B1348483 : Blo 1064615 1348483 := bstep (se 1 (by rfl) ⟨1011362, by rfl⟩ : syracuseStep 1348483 = 2022725) B2022725
theorem B1348579 : Blo 1064615 1348579 := bstep (se 1 (by rfl) ⟨1011434, by rfl⟩ : syracuseStep 1348579 = 2022869) B2022869
theorem B3642499 : Blo 1064615 3642499 := bstep (se 1 (by rfl) ⟨2731874, by rfl⟩ : syracuseStep 3642499 = 5463749) B5463749
theorem B2397329 : Blo 1064615 2397329 := bstep (se 2 (by rfl) ⟨898998, by rfl⟩ : syracuseStep 2397329 = 1797997) B1797997
theorem B2397347 : Blo 1064615 2397347 := bstep (se 1 (by rfl) ⟨1798010, by rfl⟩ : syracuseStep 2397347 = 3596021) B3596021
theorem B5772485 : Blo 1064615 5772485 := bstep (se 4 (by rfl) ⟨541170, by rfl⟩ : syracuseStep 5772485 = 1082341) B1082341
theorem B2397617 : Blo 1064615 2397617 := bstep (se 2 (by rfl) ⟨899106, by rfl⟩ : syracuseStep 2397617 = 1798213) B1798213
theorem B2397635 : Blo 1064615 2397635 := bstep (se 1 (by rfl) ⟨1798226, by rfl⟩ : syracuseStep 2397635 = 3596453) B3596453
theorem B1349075 : Blo 1064615 1349075 := bstep (se 1 (by rfl) ⟨1011806, by rfl⟩ : syracuseStep 1349075 = 2023613) B2023613
theorem B2561635 : Blo 1064615 2561635 := bstep (se 1 (by rfl) ⟨1921226, by rfl⟩ : syracuseStep 2561635 = 3842453) B3842453
theorem B2397905 : Blo 1064615 2397905 := bstep (se 2 (by rfl) ⟨899214, by rfl⟩ : syracuseStep 2397905 = 1798429) B1798429
theorem B2397923 : Blo 1064615 2397923 := bstep (se 1 (by rfl) ⟨1798442, by rfl⟩ : syracuseStep 2397923 = 3596885) B3596885
theorem B2561809 : Blo 1064615 2561809 := bstep (se 2 (by rfl) ⟨960678, by rfl⟩ : syracuseStep 2561809 = 1921357) B1921357
theorem B1709923 : Blo 1064615 1709923 := bstep (se 1 (by rfl) ⟨1282442, by rfl⟩ : syracuseStep 1709923 = 2564885) B2564885
theorem B3413873 : Blo 1064615 3413873 := bstep (se 2 (by rfl) ⟨1280202, by rfl⟩ : syracuseStep 3413873 = 2560405) B2560405
theorem B2398193 : Blo 1064615 2398193 := bstep (se 2 (by rfl) ⟨899322, by rfl⟩ : syracuseStep 2398193 = 1798645) B1798645
theorem B2398211 : Blo 1064615 2398211 := bstep (se 1 (by rfl) ⟨1798658, by rfl⟩ : syracuseStep 2398211 = 3597317) B3597317
theorem B2431043 : Blo 1064615 2431043 := bstep (se 1 (by rfl) ⟨1823282, by rfl⟩ : syracuseStep 2431043 = 3646565) B3646565
theorem B3643501 : Blo 1064615 3643501 := bstep (se 3 (by rfl) ⟨683156, by rfl⟩ : syracuseStep 3643501 = 1366313) B1366313
theorem B6068357 : Blo 1064615 6068357 := bstep (se 4 (by rfl) ⟨568908, by rfl⟩ : syracuseStep 6068357 = 1137817) B1137817
theorem B1349779 : Blo 1064615 1349779 := bstep (se 1 (by rfl) ⟨1012334, by rfl⟩ : syracuseStep 1349779 = 2024669) B2024669
theorem B6166691 : Blo 1064615 6166691 := bstep (se 1 (by rfl) ⟨4625018, by rfl⟩ : syracuseStep 6166691 = 9250037) B9250037
theorem B3840205 : Blo 1064615 3840205 := bstep (se 3 (by rfl) ⟨720038, by rfl⟩ : syracuseStep 3840205 = 1440077) B1440077
theorem B1349875 : Blo 1064615 1349875 := bstep (se 1 (by rfl) ⟨1012406, by rfl⟩ : syracuseStep 1349875 = 2024813) B2024813
theorem B2398481 : Blo 1064615 2398481 := bstep (se 2 (by rfl) ⟨899430, by rfl⟩ : syracuseStep 2398481 = 1798861) B1798861
theorem B2398499 : Blo 1064615 2398499 := bstep (se 1 (by rfl) ⟨1798874, by rfl⟩ : syracuseStep 2398499 = 3597749) B3597749
theorem B4331875 : Blo 1064615 4331875 := bstep (se 1 (by rfl) ⟨3248906, by rfl⟩ : syracuseStep 4331875 = 6497813) B6497813
theorem B3414413 : Blo 1064615 3414413 := bstep (se 3 (by rfl) ⟨640202, by rfl⟩ : syracuseStep 3414413 = 1280405) B1280405
theorem B2595331 : Blo 1064615 2595331 := bstep (se 1 (by rfl) ⟨1946498, by rfl⟩ : syracuseStep 2595331 = 3892997) B3892997
theorem B2398769 : Blo 1064615 2398769 := bstep (se 2 (by rfl) ⟨899538, by rfl⟩ : syracuseStep 2398769 = 1799077) B1799077
theorem B1710641 : Blo 1064615 1710641 := bstep (se 2 (by rfl) ⟨641490, by rfl⟩ : syracuseStep 1710641 = 1282981) B1282981
theorem B2398787 : Blo 1064615 2398787 := bstep (se 1 (by rfl) ⟨1799090, by rfl⟩ : syracuseStep 2398787 = 3598181) B3598181
theorem B1350371 : Blo 1064615 1350371 := bstep (se 1 (by rfl) ⟨1012778, by rfl⟩ : syracuseStep 1350371 = 2025557) B2025557
theorem B2399057 : Blo 1064615 2399057 := bstep (se 2 (by rfl) ⟨899646, by rfl⟩ : syracuseStep 2399057 = 1799293) B1799293
theorem B1710929 : Blo 1064615 1710929 := bstep (se 2 (by rfl) ⟨641598, by rfl⟩ : syracuseStep 1710929 = 1283197) B1283197
theorem B2399075 : Blo 1064615 2399075 := bstep (se 1 (by rfl) ⟨1799306, by rfl⟩ : syracuseStep 2399075 = 3598613) B3598613
theorem B5118947 : Blo 1064615 5118947 := bstep (se 1 (by rfl) ⟨3839210, by rfl⟩ : syracuseStep 5118947 = 7678421) B7678421
theorem B1154035 : Blo 1064615 1154035 := bstep (se 1 (by rfl) ⟨865526, by rfl⟩ : syracuseStep 1154035 = 1731053) B1731053
theorem B1711153 : Blo 1064615 1711153 := bstep (se 2 (by rfl) ⟨641682, by rfl⟩ : syracuseStep 1711153 = 1283365) B1283365
theorem B2399345 : Blo 1064615 2399345 := bstep (se 2 (by rfl) ⟨899754, by rfl⟩ : syracuseStep 2399345 = 1799509) B1799509
theorem B2399363 : Blo 1064615 2399363 := bstep (se 1 (by rfl) ⟨1799522, by rfl⟩ : syracuseStep 2399363 = 3599045) B3599045
theorem B2464913 : Blo 1064615 2464913 := bstep (se 2 (by rfl) ⟨924342, by rfl⟩ : syracuseStep 2464913 = 1848685) B1848685
theorem B8101133 : Blo 1064615 8101133 := bstep (se 3 (by rfl) ⟨1518962, by rfl⟩ : syracuseStep 8101133 = 3037925) B3037925
theorem B11672885 : Blo 1064615 11672885 := bstep (se 5 (by rfl) ⟨547166, by rfl⟩ : syracuseStep 11672885 = 1094333) B1094333
theorem B2596195 : Blo 1064615 2596195 := bstep (se 1 (by rfl) ⟨1947146, by rfl⟩ : syracuseStep 2596195 = 3894293) B3894293
theorem B1154419 : Blo 1064615 1154419 := bstep (se 1 (by rfl) ⟨865814, by rfl⟩ : syracuseStep 1154419 = 1731629) B1731629
theorem B2399633 : Blo 1064615 2399633 := bstep (se 2 (by rfl) ⟨899862, by rfl⟩ : syracuseStep 2399633 = 1799725) B1799725
theorem B2399651 : Blo 1064615 2399651 := bstep (se 1 (by rfl) ⟨1799738, by rfl⟩ : syracuseStep 2399651 = 3599477) B3599477
theorem B1351075 : Blo 1064615 1351075 := bstep (se 1 (by rfl) ⟨1013306, by rfl⟩ : syracuseStep 1351075 = 2026613) B2026613
theorem B1351171 : Blo 1064615 1351171 := bstep (se 1 (by rfl) ⟨1013378, by rfl⟩ : syracuseStep 1351171 = 2026757) B2026757
theorem B2399921 : Blo 1064615 2399921 := bstep (se 2 (by rfl) ⟨899970, by rfl⟩ : syracuseStep 2399921 = 1799941) B1799941
theorem B2399939 : Blo 1064615 2399939 := bstep (se 1 (by rfl) ⟨1799954, by rfl⟩ : syracuseStep 2399939 = 3599909) B3599909
theorem B38969059 : Blo 1064615 38969059 := bstep (se 1 (by rfl) ⟨29226794, by rfl⟩ : syracuseStep 38969059 = 58453589) B58453589
theorem B4562801 : Blo 1064615 4562801 := bstep (se 2 (by rfl) ⟨1711050, by rfl⟩ : syracuseStep 4562801 = 3422101) B3422101
theorem B2400209 : Blo 1064615 2400209 := bstep (se 2 (by rfl) ⟨900078, by rfl⟩ : syracuseStep 2400209 = 1800157) B1800157
theorem B2400227 : Blo 1064615 2400227 := bstep (se 1 (by rfl) ⟨1800170, by rfl⟩ : syracuseStep 2400227 = 3600341) B3600341
theorem B2695153 : Blo 1064615 2695153 := bstep (se 2 (by rfl) ⟨1010682, by rfl⟩ : syracuseStep 2695153 = 2021365) B2021365
theorem B1351667 : Blo 1064615 1351667 := bstep (se 1 (by rfl) ⟨1013750, by rfl⟩ : syracuseStep 1351667 = 2027501) B2027501
theorem B2400497 : Blo 1064615 2400497 := bstep (se 2 (by rfl) ⟨900186, by rfl⟩ : syracuseStep 2400497 = 1800373) B1800373
theorem B2695427 : Blo 1064615 2695427 := bstep (se 1 (by rfl) ⟨2021570, by rfl⟩ : syracuseStep 2695427 = 4043141) B4043141
theorem B2400515 : Blo 1064615 2400515 := bstep (se 1 (by rfl) ⟨1800386, by rfl⟩ : syracuseStep 2400515 = 3600773) B3600773
theorem B2695619 : Blo 1064615 2695619 := bstep (se 1 (by rfl) ⟨2021714, by rfl⟩ : syracuseStep 2695619 = 4043429) B4043429
theorem B1516001 : Blo 1064615 1516001 := bstep (se 2 (by rfl) ⟨568500, by rfl⟩ : syracuseStep 1516001 = 1137001) B1137001
theorem B2400785 : Blo 1064615 2400785 := bstep (se 2 (by rfl) ⟨900294, by rfl⟩ : syracuseStep 2400785 = 1800589) B1800589
theorem B2400803 : Blo 1064615 2400803 := bstep (se 1 (by rfl) ⟨1800602, by rfl⟩ : syracuseStep 2400803 = 3601205) B3601205
theorem B1516115 : Blo 1064615 1516115 := bstep (se 1 (by rfl) ⟨1137086, by rfl⟩ : syracuseStep 1516115 = 2274173) B2274173
theorem B1516195 : Blo 1064615 1516195 := bstep (se 1 (by rfl) ⟨1137146, by rfl⟩ : syracuseStep 1516195 = 2274293) B2274293
theorem B1352371 : Blo 1064615 1352371 := bstep (se 1 (by rfl) ⟨1014278, by rfl⟩ : syracuseStep 1352371 = 2028557) B2028557
theorem B3646225 : Blo 1064615 3646225 := bstep (se 2 (by rfl) ⟨1367334, by rfl⟩ : syracuseStep 3646225 = 2734669) B2734669
theorem B1352467 : Blo 1064615 1352467 := bstep (se 1 (by rfl) ⟨1014350, by rfl⟩ : syracuseStep 1352467 = 2028701) B2028701
theorem B1155875 : Blo 1064615 1155875 := bstep (se 1 (by rfl) ⟨866906, by rfl⟩ : syracuseStep 1155875 = 1733813) B1733813
theorem B2401073 : Blo 1064615 2401073 := bstep (se 2 (by rfl) ⟨900402, by rfl⟩ : syracuseStep 2401073 = 1800805) B1800805
theorem B2401091 : Blo 1064615 2401091 := bstep (se 1 (by rfl) ⟨1800818, by rfl⟩ : syracuseStep 2401091 = 3601637) B3601637
theorem B2401361 : Blo 1064615 2401361 := bstep (se 2 (by rfl) ⟨900510, by rfl⟩ : syracuseStep 2401361 = 1801021) B1801021
theorem B6825059 : Blo 1064615 6825059 := bstep (se 1 (by rfl) ⟨5118794, by rfl⟩ : syracuseStep 6825059 = 10237589) B10237589
theorem B12133475 : Blo 1064615 12133475 := bstep (se 1 (by rfl) ⟨9100106, by rfl⟩ : syracuseStep 12133475 = 18200213) B18200213
theorem B2401379 : Blo 1064615 2401379 := bstep (se 1 (by rfl) ⟨1801034, by rfl⟩ : syracuseStep 2401379 = 3602069) B3602069
theorem B17507441 : Blo 1064615 17507441 := bstep (se 2 (by rfl) ⟨6565290, by rfl⟩ : syracuseStep 17507441 = 13130581) B13130581
theorem B1516753 : Blo 1064615 1516753 := bstep (se 2 (by rfl) ⟨568782, by rfl⟩ : syracuseStep 1516753 = 1137565) B1137565
theorem B2696561 : Blo 1064615 2696561 := bstep (se 2 (by rfl) ⟨1011210, by rfl⟩ : syracuseStep 2696561 = 2022421) B2022421
theorem B2401649 : Blo 1064615 2401649 := bstep (se 2 (by rfl) ⟨900618, by rfl⟩ : syracuseStep 2401649 = 1801237) B1801237
theorem B2401667 : Blo 1064615 2401667 := bstep (se 1 (by rfl) ⟨1801250, by rfl⟩ : syracuseStep 2401667 = 3602501) B3602501
theorem B2696611 : Blo 1064615 2696611 := bstep (se 1 (by rfl) ⟨2022458, by rfl⟩ : syracuseStep 2696611 = 4044917) B4044917
theorem B2467313 : Blo 1064615 2467313 := bstep (se 2 (by rfl) ⟨925242, by rfl⟩ : syracuseStep 2467313 = 1850485) B1850485
theorem B2696753 : Blo 1064615 2696753 := bstep (se 2 (by rfl) ⟨1011282, by rfl⟩ : syracuseStep 2696753 = 2022565) B2022565
theorem B2565731 : Blo 1064615 2565731 := bstep (se 1 (by rfl) ⟨1924298, by rfl⟩ : syracuseStep 2565731 = 3848597) B3848597
theorem B6006413 : Blo 1064615 6006413 := bstep (se 3 (by rfl) ⟨1126202, by rfl⟩ : syracuseStep 6006413 = 2252405) B2252405
theorem B2401937 : Blo 1064615 2401937 := bstep (se 2 (by rfl) ⟨900726, by rfl⟩ : syracuseStep 2401937 = 1801453) B1801453
theorem B2401955 : Blo 1064615 2401955 := bstep (se 1 (by rfl) ⟨1801466, by rfl⟩ : syracuseStep 2401955 = 3602933) B3602933
theorem B2565827 : Blo 1064615 2565827 := bstep (se 1 (by rfl) ⟨1924370, by rfl⟩ : syracuseStep 2565827 = 3848741) B3848741
theorem B6072205 : Blo 1064615 6072205 := bstep (se 3 (by rfl) ⟨1138538, by rfl⟩ : syracuseStep 6072205 = 2277077) B2277077
theorem B3418001 : Blo 1064615 3418001 := bstep (se 2 (by rfl) ⟨1281750, by rfl⟩ : syracuseStep 3418001 = 2563501) B2563501
theorem B1517459 : Blo 1064615 1517459 := bstep (se 1 (by rfl) ⟨1138094, by rfl⟩ : syracuseStep 1517459 = 2276189) B2276189
theorem B2402225 : Blo 1064615 2402225 := bstep (se 2 (by rfl) ⟨900834, by rfl⟩ : syracuseStep 2402225 = 1801669) B1801669
theorem B2402243 : Blo 1064615 2402243 := bstep (se 1 (by rfl) ⟨1801682, by rfl⟩ : syracuseStep 2402243 = 3603365) B3603365
theorem B8104049 : Blo 1064615 8104049 := bstep (se 2 (by rfl) ⟨3039018, by rfl⟩ : syracuseStep 8104049 = 6078037) B6078037
theorem B26683505 : Blo 1064615 26683505 := bstep (se 2 (by rfl) ⟨10006314, by rfl⟩ : syracuseStep 26683505 = 20012629) B20012629
theorem B23668933 : Blo 1064615 23668933 := bstep (se 4 (by rfl) ⟨2218962, by rfl⟩ : syracuseStep 23668933 = 4437925) B4437925
theorem B2402513 : Blo 1064615 2402513 := bstep (se 2 (by rfl) ⟨900942, by rfl⟩ : syracuseStep 2402513 = 1801885) B1801885
theorem B2402531 : Blo 1064615 2402531 := bstep (se 1 (by rfl) ⟨1801898, by rfl⟩ : syracuseStep 2402531 = 3603797) B3603797
theorem B6498737 : Blo 1064615 6498737 := bstep (se 2 (by rfl) ⟨2437026, by rfl⟩ : syracuseStep 6498737 = 4874053) B4874053
theorem B2402801 : Blo 1064615 2402801 := bstep (se 2 (by rfl) ⟨901050, by rfl⟩ : syracuseStep 2402801 = 1802101) B1802101
theorem B2402819 : Blo 1064615 2402819 := bstep (se 1 (by rfl) ⟨1802114, by rfl⟩ : syracuseStep 2402819 = 3604229) B3604229
theorem B2697745 : Blo 1064615 2697745 := bstep (se 2 (by rfl) ⟨1011654, by rfl⟩ : syracuseStep 2697745 = 2023309) B2023309
theorem B1518097 : Blo 1064615 1518097 := bstep (se 2 (by rfl) ⟨569286, by rfl⟩ : syracuseStep 1518097 = 1138573) B1138573
theorem B2566673 : Blo 1064615 2566673 := bstep (se 2 (by rfl) ⟨962502, by rfl⟩ : syracuseStep 2566673 = 1925005) B1925005
theorem B3418691 : Blo 1064615 3418691 := bstep (se 1 (by rfl) ⟨2564018, by rfl⟩ : syracuseStep 3418691 = 5128037) B5128037
theorem B1518211 : Blo 1064615 1518211 := bstep (se 1 (by rfl) ⟨1138658, by rfl⟩ : syracuseStep 1518211 = 2277317) B2277317
theorem B2403089 : Blo 1064615 2403089 := bstep (se 2 (by rfl) ⟨901158, by rfl⟩ : syracuseStep 2403089 = 1802317) B1802317
theorem B1846049 : Blo 1064615 1846049 := bstep (se 2 (by rfl) ⟨692268, by rfl⟩ : syracuseStep 1846049 = 1384537) B1384537
theorem B2698019 : Blo 1064615 2698019 := bstep (se 1 (by rfl) ⟨2023514, by rfl⟩ : syracuseStep 2698019 = 4047029) B4047029
theorem B2403107 : Blo 1064615 2403107 := bstep (se 1 (by rfl) ⟨1802330, by rfl⟩ : syracuseStep 2403107 = 3604661) B3604661
theorem B2566961 : Blo 1064615 2566961 := bstep (se 2 (by rfl) ⟨962610, by rfl⟩ : syracuseStep 2566961 = 1925221) B1925221
theorem B2698211 : Blo 1064615 2698211 := bstep (se 1 (by rfl) ⟨2023658, by rfl⟩ : syracuseStep 2698211 = 4047317) B4047317
theorem B2567171 : Blo 1064615 2567171 := bstep (se 1 (by rfl) ⟨1925378, by rfl⟩ : syracuseStep 2567171 = 3850757) B3850757
theorem B2403377 : Blo 1064615 2403377 := bstep (se 2 (by rfl) ⟨901266, by rfl⟩ : syracuseStep 2403377 = 1802533) B1802533
theorem B2403395 : Blo 1064615 2403395 := bstep (se 1 (by rfl) ⟨1802546, by rfl⟩ : syracuseStep 2403395 = 3605093) B3605093
theorem B2403665 : Blo 1064615 2403665 := bstep (se 2 (by rfl) ⟨901374, by rfl⟩ : syracuseStep 2403665 = 1802749) B1802749
theorem B2403683 : Blo 1064615 2403683 := bstep (se 1 (by rfl) ⟨1802762, by rfl⟩ : syracuseStep 2403683 = 3605525) B3605525
theorem B2403953 : Blo 1064615 2403953 := bstep (se 2 (by rfl) ⟨901482, by rfl⟩ : syracuseStep 2403953 = 1802965) B1802965
theorem B2403971 : Blo 1064615 2403971 := bstep (se 1 (by rfl) ⟨1802978, by rfl⟩ : syracuseStep 2403971 = 3605957) B3605957
theorem B6074189 : Blo 1064615 6074189 := bstep (se 3 (by rfl) ⟨1138910, by rfl⟩ : syracuseStep 6074189 = 2277821) B2277821
theorem B2699153 : Blo 1064615 2699153 := bstep (se 2 (by rfl) ⟨1012182, by rfl⟩ : syracuseStep 2699153 = 2024365) B2024365
theorem B2404241 : Blo 1064615 2404241 := bstep (se 2 (by rfl) ⟨901590, by rfl⟩ : syracuseStep 2404241 = 1803181) B1803181
theorem B2404259 : Blo 1064615 2404259 := bstep (se 1 (by rfl) ⟨1803194, by rfl⟩ : syracuseStep 2404259 = 3606389) B3606389
theorem B2699203 : Blo 1064615 2699203 := bstep (se 1 (by rfl) ⟨2024402, by rfl⟩ : syracuseStep 2699203 = 4048805) B4048805
theorem B1519555 : Blo 1064615 1519555 := bstep (se 1 (by rfl) ⟨1139666, by rfl⟩ : syracuseStep 1519555 = 2279333) B2279333
theorem B2699345 : Blo 1064615 2699345 := bstep (se 2 (by rfl) ⟨1012254, by rfl⟩ : syracuseStep 2699345 = 2024509) B2024509
theorem B2306225 : Blo 1064615 2306225 := bstep (se 2 (by rfl) ⟨864834, by rfl⟩ : syracuseStep 2306225 = 1729669) B1729669
theorem B6828209 : Blo 1064615 6828209 := bstep (se 2 (by rfl) ⟨2560578, by rfl⟩ : syracuseStep 6828209 = 5121157) B5121157
theorem B6828259 : Blo 1064615 6828259 := bstep (se 1 (by rfl) ⟨5121194, by rfl⟩ : syracuseStep 6828259 = 10242389) B10242389
theorem B3420461 : Blo 1064615 3420461 := bstep (se 3 (by rfl) ⟨641336, by rfl⟩ : syracuseStep 3420461 = 1282673) B1282673
theorem B3420589 : Blo 1064615 3420589 := bstep (se 3 (by rfl) ⟨641360, by rfl⟩ : syracuseStep 3420589 = 1282721) B1282721
theorem B13152709 : Blo 1064615 13152709 := bstep (se 4 (by rfl) ⟨1233066, by rfl⟩ : syracuseStep 13152709 = 2466133) B2466133
theorem B15348365 : Blo 1064615 15348365 := bstep (se 3 (by rfl) ⟨2877818, by rfl⟩ : syracuseStep 15348365 = 5755637) B5755637
theorem B3420845 : Blo 1064615 3420845 := bstep (se 3 (by rfl) ⟨641408, by rfl⟩ : syracuseStep 3420845 = 1282817) B1282817
theorem B12169925 : Blo 1064615 12169925 := bstep (se 4 (by rfl) ⟨1140930, by rfl⟩ : syracuseStep 12169925 = 2281861) B2281861
theorem B6075121 : Blo 1064615 6075121 := bstep (se 2 (by rfl) ⟨2278170, by rfl⟩ : syracuseStep 6075121 = 4556341) B4556341
theorem B2274275 : Blo 1064615 2274275 := bstep (se 1 (by rfl) ⟨1705706, by rfl⟩ : syracuseStep 2274275 = 3411413) B3411413
theorem B3847181 : Blo 1064615 3847181 := bstep (se 3 (by rfl) ⟨721346, by rfl⟩ : syracuseStep 3847181 = 1442693) B1442693
theorem B2700337 : Blo 1064615 2700337 := bstep (se 2 (by rfl) ⟨1012626, by rfl⟩ : syracuseStep 2700337 = 2025253) B2025253
theorem B1520689 : Blo 1064615 1520689 := bstep (se 2 (by rfl) ⟨570258, by rfl⟩ : syracuseStep 1520689 = 1140517) B1140517
theorem B1619041 : Blo 1064615 1619041 := bstep (se 2 (by rfl) ⟨607140, by rfl⟩ : syracuseStep 1619041 = 1214281) B1214281
theorem B1520785 : Blo 1064615 1520785 := bstep (se 2 (by rfl) ⟨570294, by rfl⟩ : syracuseStep 1520785 = 1140589) B1140589
theorem B3650861 : Blo 1064615 3650861 := bstep (se 3 (by rfl) ⟨684536, by rfl⟩ : syracuseStep 3650861 = 1369073) B1369073
theorem B2700611 : Blo 1064615 2700611 := bstep (se 1 (by rfl) ⟨2025458, by rfl⟩ : syracuseStep 2700611 = 4050917) B4050917
theorem B2700803 : Blo 1064615 2700803 := bstep (se 1 (by rfl) ⟨2025602, by rfl⟩ : syracuseStep 2700803 = 4051205) B4051205
theorem B4044401 : Blo 1064615 4044401 := bstep (se 2 (by rfl) ⟨1516650, by rfl⟩ : syracuseStep 4044401 = 3033301) B3033301
theorem B1521281 : Blo 1064615 1521281 := bstep (se 2 (by rfl) ⟨570480, by rfl⟩ : syracuseStep 1521281 = 1140961) B1140961
theorem B3651409 : Blo 1064615 3651409 := bstep (se 2 (by rfl) ⟨1369278, by rfl⟩ : syracuseStep 3651409 = 2738557) B2738557
theorem B6076579 : Blo 1064615 6076579 := bstep (se 1 (by rfl) ⟨4557434, by rfl⟩ : syracuseStep 6076579 = 9114869) B9114869
theorem B3422371 : Blo 1064615 3422371 := bstep (se 1 (by rfl) ⟨2566778, by rfl⟩ : syracuseStep 3422371 = 5133557) B5133557
theorem B2275523 : Blo 1064615 2275523 := bstep (se 1 (by rfl) ⟨1706642, by rfl⟩ : syracuseStep 2275523 = 3413285) B3413285
theorem B1620305 : Blo 1064615 1620305 := bstep (se 2 (by rfl) ⟨607614, by rfl⟩ : syracuseStep 1620305 = 1215229) B1215229
theorem B2701745 : Blo 1064615 2701745 := bstep (se 2 (by rfl) ⟨1013154, by rfl⟩ : syracuseStep 2701745 = 2026309) B2026309
theorem B2701795 : Blo 1064615 2701795 := bstep (se 1 (by rfl) ⟨2026346, by rfl⟩ : syracuseStep 2701795 = 4052693) B4052693
theorem B11549155 : Blo 1064615 11549155 := bstep (se 1 (by rfl) ⟨8661866, by rfl⟩ : syracuseStep 11549155 = 17323733) B17323733
theorem B6830669 : Blo 1064615 6830669 := bstep (se 3 (by rfl) ⟨1280750, by rfl⟩ : syracuseStep 6830669 = 2561501) B2561501
theorem B2701937 : Blo 1064615 2701937 := bstep (se 2 (by rfl) ⟨1013226, by rfl⟩ : syracuseStep 2701937 = 2026453) B2026453
theorem B6077105 : Blo 1064615 6077105 := bstep (se 2 (by rfl) ⟨2278914, by rfl⟩ : syracuseStep 6077105 = 4557829) B4557829
theorem B2276113 : Blo 1064615 2276113 := bstep (se 2 (by rfl) ⟨853542, by rfl⟩ : syracuseStep 2276113 = 1707085) B1707085
theorem B71219989 : Blo 1064615 71219989 := bstep (se 6 (by rfl) ⟨1669218, by rfl⟩ : syracuseStep 71219989 = 3338437) B3338437
theorem B1522577 : Blo 1064615 1522577 := bstep (se 2 (by rfl) ⟨570966, by rfl⟩ : syracuseStep 1522577 = 1141933) B1141933
theorem B4864931 : Blo 1064615 4864931 := bstep (se 1 (by rfl) ⟨3648698, by rfl⟩ : syracuseStep 4864931 = 7297397) B7297397
theorem B1850321 : Blo 1064615 1850321 := bstep (se 2 (by rfl) ⟨693870, by rfl⟩ : syracuseStep 1850321 = 1387741) B1387741
theorem B4045859 : Blo 1064615 4045859 := bstep (se 1 (by rfl) ⟨3034394, by rfl⟩ : syracuseStep 4045859 = 6068789) B6068789
theorem B9223409 : Blo 1064615 9223409 := bstep (se 2 (by rfl) ⟨3458778, by rfl⟩ : syracuseStep 9223409 = 6917557) B6917557
theorem B5389901 : Blo 1064615 5389901 := bstep (se 3 (by rfl) ⟨1010606, by rfl⟩ : syracuseStep 5389901 = 2021213) B2021213
theorem B2702929 : Blo 1064615 2702929 := bstep (se 2 (by rfl) ⟨1013598, by rfl⟩ : syracuseStep 2702929 = 2027197) B2027197
theorem B1064627 : Blo 1064615 1064627 := bstep (se 1 (by rfl) ⟨798470, by rfl⟩ : syracuseStep 1064627 = 1596941) B1596941
theorem B1064643 : Blo 1064615 1064643 := bstep (se 1 (by rfl) ⟨798482, by rfl⟩ : syracuseStep 1064643 = 1596965) B1596965
theorem B1064659 : Blo 1064615 1064659 := bstep (se 1 (by rfl) ⟨798494, by rfl⟩ : syracuseStep 1064659 = 1596989) B1596989
theorem B1621729 : Blo 1064615 1621729 := bstep (se 2 (by rfl) ⟨608148, by rfl⟩ : syracuseStep 1621729 = 1216297) B1216297
theorem B1064675 : Blo 1064615 1064675 := bstep (se 1 (by rfl) ⟨798506, by rfl⟩ : syracuseStep 1064675 = 1597013) B1597013
theorem B1064691 : Blo 1064615 1064691 := bstep (se 1 (by rfl) ⟨798518, by rfl⟩ : syracuseStep 1064691 = 1597037) B1597037
theorem B1064707 : Blo 1064615 1064707 := bstep (se 1 (by rfl) ⟨798530, by rfl⟩ : syracuseStep 1064707 = 1597061) B1597061
theorem B1064723 : Blo 1064615 1064723 := bstep (se 1 (by rfl) ⟨798542, by rfl⟩ : syracuseStep 1064723 = 1597085) B1597085
theorem B1064739 : Blo 1064615 1064739 := bstep (se 1 (by rfl) ⟨798554, by rfl⟩ : syracuseStep 1064739 = 1597109) B1597109
theorem B1064755 : Blo 1064615 1064755 := bstep (se 1 (by rfl) ⟨798566, by rfl⟩ : syracuseStep 1064755 = 1597133) B1597133
theorem B1064771 : Blo 1064615 1064771 := bstep (se 1 (by rfl) ⟨798578, by rfl⟩ : syracuseStep 1064771 = 1597157) B1597157
theorem B1064787 : Blo 1064615 1064787 := bstep (se 1 (by rfl) ⟨798590, by rfl⟩ : syracuseStep 1064787 = 1597181) B1597181
theorem B1064803 : Blo 1064615 1064803 := bstep (se 1 (by rfl) ⟨798602, by rfl⟩ : syracuseStep 1064803 = 1597205) B1597205
theorem B2703203 : Blo 1064615 2703203 := bstep (se 1 (by rfl) ⟨2027402, by rfl⟩ : syracuseStep 2703203 = 4054805) B4054805
theorem B1064819 : Blo 1064615 1064819 := bstep (se 1 (by rfl) ⟨798614, by rfl⟩ : syracuseStep 1064819 = 1597229) B1597229
theorem B1064835 : Blo 1064615 1064835 := bstep (se 1 (by rfl) ⟨798626, by rfl⟩ : syracuseStep 1064835 = 1597253) B1597253
theorem B1064851 : Blo 1064615 1064851 := bstep (se 1 (by rfl) ⟨798638, by rfl⟩ : syracuseStep 1064851 = 1597277) B1597277
theorem B1064867 : Blo 1064615 1064867 := bstep (se 1 (by rfl) ⟨798650, by rfl⟩ : syracuseStep 1064867 = 1597301) B1597301
theorem B1064883 : Blo 1064615 1064883 := bstep (se 1 (by rfl) ⟨798662, by rfl⟩ : syracuseStep 1064883 = 1597325) B1597325
theorem B1064899 : Blo 1064615 1064899 := bstep (se 1 (by rfl) ⟨798674, by rfl⟩ : syracuseStep 1064899 = 1597349) B1597349
theorem B1064915 : Blo 1064615 1064915 := bstep (se 1 (by rfl) ⟨798686, by rfl⟩ : syracuseStep 1064915 = 1597373) B1597373
theorem B1064931 : Blo 1064615 1064931 := bstep (se 1 (by rfl) ⟨798698, by rfl⟩ : syracuseStep 1064931 = 1597397) B1597397
theorem B1064947 : Blo 1064615 1064947 := bstep (se 1 (by rfl) ⟨798710, by rfl⟩ : syracuseStep 1064947 = 1597421) B1597421
theorem B1064963 : Blo 1064615 1064963 := bstep (se 1 (by rfl) ⟨798722, by rfl⟩ : syracuseStep 1064963 = 1597445) B1597445
theorem B4046861 : Blo 1064615 4046861 := bstep (se 3 (by rfl) ⟨758786, by rfl⟩ : syracuseStep 4046861 = 1517573) B1517573
theorem B1064979 : Blo 1064615 1064979 := bstep (se 1 (by rfl) ⟨798734, by rfl⟩ : syracuseStep 1064979 = 1597469) B1597469
theorem B1064995 : Blo 1064615 1064995 := bstep (se 1 (by rfl) ⟨798746, by rfl⟩ : syracuseStep 1064995 = 1597493) B1597493
theorem B1851427 : Blo 1064615 1851427 := bstep (se 1 (by rfl) ⟨1388570, by rfl⟩ : syracuseStep 1851427 = 2777141) B2777141
theorem B2703395 : Blo 1064615 2703395 := bstep (se 1 (by rfl) ⟨2027546, by rfl⟩ : syracuseStep 2703395 = 4055093) B4055093
theorem B1065011 : Blo 1064615 1065011 := bstep (se 1 (by rfl) ⟨798758, by rfl⟩ : syracuseStep 1065011 = 1597517) B1597517
theorem B1065027 : Blo 1064615 1065027 := bstep (se 1 (by rfl) ⟨798770, by rfl⟩ : syracuseStep 1065027 = 1597541) B1597541
theorem B1065043 : Blo 1064615 1065043 := bstep (se 1 (by rfl) ⟨798782, by rfl⟩ : syracuseStep 1065043 = 1597565) B1597565
theorem B1065059 : Blo 1064615 1065059 := bstep (se 1 (by rfl) ⟨798794, by rfl⟩ : syracuseStep 1065059 = 1597589) B1597589
theorem B6078563 : Blo 1064615 6078563 := bstep (se 1 (by rfl) ⟨4558922, by rfl⟩ : syracuseStep 6078563 = 9117845) B9117845
theorem B1065075 : Blo 1064615 1065075 := bstep (se 1 (by rfl) ⟨798806, by rfl⟩ : syracuseStep 1065075 = 1597613) B1597613
theorem B1065091 : Blo 1064615 1065091 := bstep (se 1 (by rfl) ⟨798818, by rfl⟩ : syracuseStep 1065091 = 1597637) B1597637
theorem B1065107 : Blo 1064615 1065107 := bstep (se 1 (by rfl) ⟨798830, by rfl⟩ : syracuseStep 1065107 = 1597661) B1597661
theorem B1065123 : Blo 1064615 1065123 := bstep (se 1 (by rfl) ⟨798842, by rfl⟩ : syracuseStep 1065123 = 1597685) B1597685
theorem B1065139 : Blo 1064615 1065139 := bstep (se 1 (by rfl) ⟨798854, by rfl⟩ : syracuseStep 1065139 = 1597709) B1597709
theorem B1065155 : Blo 1064615 1065155 := bstep (se 1 (by rfl) ⟨798866, by rfl⟩ : syracuseStep 1065155 = 1597733) B1597733
theorem B1065171 : Blo 1064615 1065171 := bstep (se 1 (by rfl) ⟨798878, by rfl⟩ : syracuseStep 1065171 = 1597757) B1597757
theorem B1065187 : Blo 1064615 1065187 := bstep (se 1 (by rfl) ⟨798890, by rfl⟩ : syracuseStep 1065187 = 1597781) B1597781
theorem B1065203 : Blo 1064615 1065203 := bstep (se 1 (by rfl) ⟨798902, by rfl⟩ : syracuseStep 1065203 = 1597805) B1597805
theorem B1065219 : Blo 1064615 1065219 := bstep (se 1 (by rfl) ⟨798914, by rfl⟩ : syracuseStep 1065219 = 1597829) B1597829
theorem B1065235 : Blo 1064615 1065235 := bstep (se 1 (by rfl) ⟨798926, by rfl⟩ : syracuseStep 1065235 = 1597853) B1597853
theorem B1065251 : Blo 1064615 1065251 := bstep (se 1 (by rfl) ⟨798938, by rfl⟩ : syracuseStep 1065251 = 1597877) B1597877
theorem B1065267 : Blo 1064615 1065267 := bstep (se 1 (by rfl) ⟨798950, by rfl⟩ : syracuseStep 1065267 = 1597901) B1597901
theorem B1065283 : Blo 1064615 1065283 := bstep (se 1 (by rfl) ⟨798962, by rfl⟩ : syracuseStep 1065283 = 1597925) B1597925
theorem B1065299 : Blo 1064615 1065299 := bstep (se 1 (by rfl) ⟨798974, by rfl⟩ : syracuseStep 1065299 = 1597949) B1597949
theorem B1065315 : Blo 1064615 1065315 := bstep (se 1 (by rfl) ⟨798986, by rfl⟩ : syracuseStep 1065315 = 1597973) B1597973
theorem B1065331 : Blo 1064615 1065331 := bstep (se 1 (by rfl) ⟨798998, by rfl⟩ : syracuseStep 1065331 = 1597997) B1597997
theorem B1065347 : Blo 1064615 1065347 := bstep (se 1 (by rfl) ⟨799010, by rfl⟩ : syracuseStep 1065347 = 1598021) B1598021
theorem B1065363 : Blo 1064615 1065363 := bstep (se 1 (by rfl) ⟨799022, by rfl⟩ : syracuseStep 1065363 = 1598045) B1598045
theorem B1065379 : Blo 1064615 1065379 := bstep (se 1 (by rfl) ⟨799034, by rfl⟩ : syracuseStep 1065379 = 1598069) B1598069
theorem B1065395 : Blo 1064615 1065395 := bstep (se 1 (by rfl) ⟨799046, by rfl⟩ : syracuseStep 1065395 = 1598093) B1598093
theorem B1065411 : Blo 1064615 1065411 := bstep (se 1 (by rfl) ⟨799058, by rfl⟩ : syracuseStep 1065411 = 1598117) B1598117
theorem B1065427 : Blo 1064615 1065427 := bstep (se 1 (by rfl) ⟨799070, by rfl⟩ : syracuseStep 1065427 = 1598141) B1598141
theorem B1065443 : Blo 1064615 1065443 := bstep (se 1 (by rfl) ⟨799082, by rfl⟩ : syracuseStep 1065443 = 1598165) B1598165
theorem B1065459 : Blo 1064615 1065459 := bstep (se 1 (by rfl) ⟨799094, by rfl⟩ : syracuseStep 1065459 = 1598189) B1598189
theorem B1065475 : Blo 1064615 1065475 := bstep (se 1 (by rfl) ⟨799106, by rfl⟩ : syracuseStep 1065475 = 1598213) B1598213
theorem B1065491 : Blo 1064615 1065491 := bstep (se 1 (by rfl) ⟨799118, by rfl⟩ : syracuseStep 1065491 = 1598237) B1598237
theorem B1065507 : Blo 1064615 1065507 := bstep (se 1 (by rfl) ⟨799130, by rfl⟩ : syracuseStep 1065507 = 1598261) B1598261
theorem B1065523 : Blo 1064615 1065523 := bstep (se 1 (by rfl) ⟨799142, by rfl⟩ : syracuseStep 1065523 = 1598285) B1598285
theorem B1065539 : Blo 1064615 1065539 := bstep (se 1 (by rfl) ⟨799154, by rfl⟩ : syracuseStep 1065539 = 1598309) B1598309
theorem B1065555 : Blo 1064615 1065555 := bstep (se 1 (by rfl) ⟨799166, by rfl⟩ : syracuseStep 1065555 = 1598333) B1598333
theorem B1065571 : Blo 1064615 1065571 := bstep (se 1 (by rfl) ⟨799178, by rfl⟩ : syracuseStep 1065571 = 1598357) B1598357
theorem B3031661 : Blo 1064615 3031661 := bstep (se 3 (by rfl) ⟨568436, by rfl⟩ : syracuseStep 3031661 = 1136873) B1136873
theorem B1065587 : Blo 1064615 1065587 := bstep (se 1 (by rfl) ⟨799190, by rfl⟩ : syracuseStep 1065587 = 1598381) B1598381
theorem B1065603 : Blo 1064615 1065603 := bstep (se 1 (by rfl) ⟨799202, by rfl⟩ : syracuseStep 1065603 = 1598405) B1598405
theorem B1065619 : Blo 1064615 1065619 := bstep (se 1 (by rfl) ⟨799214, by rfl⟩ : syracuseStep 1065619 = 1598429) B1598429
theorem B1065635 : Blo 1064615 1065635 := bstep (se 1 (by rfl) ⟨799226, by rfl⟩ : syracuseStep 1065635 = 1598453) B1598453
theorem B2736803 : Blo 1064615 2736803 := bstep (se 1 (by rfl) ⟨2052602, by rfl⟩ : syracuseStep 2736803 = 4105205) B4105205
theorem B1065651 : Blo 1064615 1065651 := bstep (se 1 (by rfl) ⟨799238, by rfl⟩ : syracuseStep 1065651 = 1598477) B1598477
theorem B1065667 : Blo 1064615 1065667 := bstep (se 1 (by rfl) ⟨799250, by rfl⟩ : syracuseStep 1065667 = 1598501) B1598501
theorem B7914181 : Blo 1064615 7914181 := bstep (se 4 (by rfl) ⟨741954, by rfl⟩ : syracuseStep 7914181 = 1483909) B1483909
theorem B1065683 : Blo 1064615 1065683 := bstep (se 1 (by rfl) ⟨799262, by rfl⟩ : syracuseStep 1065683 = 1598525) B1598525
theorem B1065699 : Blo 1064615 1065699 := bstep (se 1 (by rfl) ⟨799274, by rfl⟩ : syracuseStep 1065699 = 1598549) B1598549
theorem B1065715 : Blo 1064615 1065715 := bstep (se 1 (by rfl) ⟨799286, by rfl⟩ : syracuseStep 1065715 = 1598573) B1598573
theorem B1065731 : Blo 1064615 1065731 := bstep (se 1 (by rfl) ⟨799298, by rfl⟩ : syracuseStep 1065731 = 1598597) B1598597
theorem B1065747 : Blo 1064615 1065747 := bstep (se 1 (by rfl) ⟨799310, by rfl⟩ : syracuseStep 1065747 = 1598621) B1598621
theorem B3031843 : Blo 1064615 3031843 := bstep (se 1 (by rfl) ⟨2273882, by rfl⟩ : syracuseStep 3031843 = 4547765) B4547765
theorem B1065763 : Blo 1064615 1065763 := bstep (se 1 (by rfl) ⟨799322, by rfl⟩ : syracuseStep 1065763 = 1598645) B1598645
theorem B1065779 : Blo 1064615 1065779 := bstep (se 1 (by rfl) ⟨799334, by rfl⟩ : syracuseStep 1065779 = 1598669) B1598669
theorem B1065795 : Blo 1064615 1065795 := bstep (se 1 (by rfl) ⟨799346, by rfl⟩ : syracuseStep 1065795 = 1598693) B1598693
theorem B1065811 : Blo 1064615 1065811 := bstep (se 1 (by rfl) ⟨799358, by rfl⟩ : syracuseStep 1065811 = 1598717) B1598717
theorem B1065827 : Blo 1064615 1065827 := bstep (se 1 (by rfl) ⟨799370, by rfl⟩ : syracuseStep 1065827 = 1598741) B1598741
theorem B1622897 : Blo 1064615 1622897 := bstep (se 2 (by rfl) ⟨608586, by rfl⟩ : syracuseStep 1622897 = 1217173) B1217173
theorem B1065843 : Blo 1064615 1065843 := bstep (se 1 (by rfl) ⟨799382, by rfl⟩ : syracuseStep 1065843 = 1598765) B1598765
theorem B1065859 : Blo 1064615 1065859 := bstep (se 1 (by rfl) ⟨799394, by rfl⟩ : syracuseStep 1065859 = 1598789) B1598789
theorem B1065875 : Blo 1064615 1065875 := bstep (se 1 (by rfl) ⟨799406, by rfl⟩ : syracuseStep 1065875 = 1598813) B1598813
theorem B1065891 : Blo 1064615 1065891 := bstep (se 1 (by rfl) ⟨799418, by rfl⟩ : syracuseStep 1065891 = 1598837) B1598837
theorem B1065907 : Blo 1064615 1065907 := bstep (se 1 (by rfl) ⟨799430, by rfl⟩ : syracuseStep 1065907 = 1598861) B1598861
theorem B1065923 : Blo 1064615 1065923 := bstep (se 1 (by rfl) ⟨799442, by rfl⟩ : syracuseStep 1065923 = 1598885) B1598885
theorem B2704337 : Blo 1064615 2704337 := bstep (se 2 (by rfl) ⟨1014126, by rfl⟩ : syracuseStep 2704337 = 2028253) B2028253
theorem B1065939 : Blo 1064615 1065939 := bstep (se 1 (by rfl) ⟨799454, by rfl⟩ : syracuseStep 1065939 = 1598909) B1598909
theorem B1065955 : Blo 1064615 1065955 := bstep (se 1 (by rfl) ⟨799466, by rfl⟩ : syracuseStep 1065955 = 1598933) B1598933
theorem B1065971 : Blo 1064615 1065971 := bstep (se 1 (by rfl) ⟨799478, by rfl⟩ : syracuseStep 1065971 = 1598957) B1598957
theorem B1065987 : Blo 1064615 1065987 := bstep (se 1 (by rfl) ⟨799490, by rfl⟩ : syracuseStep 1065987 = 1598981) B1598981
theorem B2704387 : Blo 1064615 2704387 := bstep (se 1 (by rfl) ⟨2028290, by rfl⟩ : syracuseStep 2704387 = 4056581) B4056581
theorem B1066003 : Blo 1064615 1066003 := bstep (se 1 (by rfl) ⟨799502, by rfl⟩ : syracuseStep 1066003 = 1599005) B1599005
theorem B1066019 : Blo 1064615 1066019 := bstep (se 1 (by rfl) ⟨799514, by rfl⟩ : syracuseStep 1066019 = 1599029) B1599029
theorem B1066035 : Blo 1064615 1066035 := bstep (se 1 (by rfl) ⟨799526, by rfl⟩ : syracuseStep 1066035 = 1599053) B1599053
theorem B1066051 : Blo 1064615 1066051 := bstep (se 1 (by rfl) ⟨799538, by rfl⟩ : syracuseStep 1066051 = 1599077) B1599077
theorem B1066067 : Blo 1064615 1066067 := bstep (se 1 (by rfl) ⟨799550, by rfl⟩ : syracuseStep 1066067 = 1599101) B1599101
theorem B1066083 : Blo 1064615 1066083 := bstep (se 1 (by rfl) ⟨799562, by rfl⟩ : syracuseStep 1066083 = 1599125) B1599125
theorem B1066099 : Blo 1064615 1066099 := bstep (se 1 (by rfl) ⟨799574, by rfl⟩ : syracuseStep 1066099 = 1599149) B1599149
theorem B1066115 : Blo 1064615 1066115 := bstep (se 1 (by rfl) ⟨799586, by rfl⟩ : syracuseStep 1066115 = 1599173) B1599173
theorem B2704529 : Blo 1064615 2704529 := bstep (se 2 (by rfl) ⟨1014198, by rfl⟩ : syracuseStep 2704529 = 2028397) B2028397
theorem B1066131 : Blo 1064615 1066131 := bstep (se 1 (by rfl) ⟨799598, by rfl⟩ : syracuseStep 1066131 = 1599197) B1599197
theorem B1066147 : Blo 1064615 1066147 := bstep (se 1 (by rfl) ⟨799610, by rfl⟩ : syracuseStep 1066147 = 1599221) B1599221
theorem B1066163 : Blo 1064615 1066163 := bstep (se 1 (by rfl) ⟨799622, by rfl⟩ : syracuseStep 1066163 = 1599245) B1599245
theorem B1066179 : Blo 1064615 1066179 := bstep (se 1 (by rfl) ⟨799634, by rfl⟩ : syracuseStep 1066179 = 1599269) B1599269
theorem B1066195 : Blo 1064615 1066195 := bstep (se 1 (by rfl) ⟨799646, by rfl⟩ : syracuseStep 1066195 = 1599293) B1599293
theorem B1066211 : Blo 1064615 1066211 := bstep (se 1 (by rfl) ⟨799658, by rfl⟩ : syracuseStep 1066211 = 1599317) B1599317
theorem B1066227 : Blo 1064615 1066227 := bstep (se 1 (by rfl) ⟨799670, by rfl⟩ : syracuseStep 1066227 = 1599341) B1599341
theorem B1066243 : Blo 1064615 1066243 := bstep (se 1 (by rfl) ⟨799682, by rfl⟩ : syracuseStep 1066243 = 1599365) B1599365
theorem B1066259 : Blo 1064615 1066259 := bstep (se 1 (by rfl) ⟨799694, by rfl⟩ : syracuseStep 1066259 = 1599389) B1599389
theorem B1066275 : Blo 1064615 1066275 := bstep (se 1 (by rfl) ⟨799706, by rfl⟩ : syracuseStep 1066275 = 1599413) B1599413
theorem B1066291 : Blo 1064615 1066291 := bstep (se 1 (by rfl) ⟨799718, by rfl⟩ : syracuseStep 1066291 = 1599437) B1599437
theorem B1066307 : Blo 1064615 1066307 := bstep (se 1 (by rfl) ⟨799730, by rfl⟩ : syracuseStep 1066307 = 1599461) B1599461
theorem B2082115 : Blo 1064615 2082115 := bstep (se 1 (by rfl) ⟨1561586, by rfl⟩ : syracuseStep 2082115 = 3123173) B3123173
theorem B1066323 : Blo 1064615 1066323 := bstep (se 1 (by rfl) ⟨799742, by rfl⟩ : syracuseStep 1066323 = 1599485) B1599485
theorem B1066339 : Blo 1064615 1066339 := bstep (se 1 (by rfl) ⟨799754, by rfl⟩ : syracuseStep 1066339 = 1599509) B1599509
theorem B1066355 : Blo 1064615 1066355 := bstep (se 1 (by rfl) ⟨799766, by rfl⟩ : syracuseStep 1066355 = 1599533) B1599533
theorem B1066371 : Blo 1064615 1066371 := bstep (se 1 (by rfl) ⟨799778, by rfl⟩ : syracuseStep 1066371 = 1599557) B1599557
theorem B6014341 : Blo 1064615 6014341 := bstep (se 4 (by rfl) ⟨563844, by rfl⟩ : syracuseStep 6014341 = 1127689) B1127689
theorem B1066387 : Blo 1064615 1066387 := bstep (se 1 (by rfl) ⟨799790, by rfl⟩ : syracuseStep 1066387 = 1599581) B1599581
theorem B1066403 : Blo 1064615 1066403 := bstep (se 1 (by rfl) ⟨799802, by rfl⟩ : syracuseStep 1066403 = 1599605) B1599605
theorem B1066419 : Blo 1064615 1066419 := bstep (se 1 (by rfl) ⟨799814, by rfl⟩ : syracuseStep 1066419 = 1599629) B1599629
theorem B1066435 : Blo 1064615 1066435 := bstep (se 1 (by rfl) ⟨799826, by rfl⟩ : syracuseStep 1066435 = 1599653) B1599653
theorem B1066451 : Blo 1064615 1066451 := bstep (se 1 (by rfl) ⟨799838, by rfl⟩ : syracuseStep 1066451 = 1599677) B1599677
theorem B1066467 : Blo 1064615 1066467 := bstep (se 1 (by rfl) ⟨799850, by rfl⟩ : syracuseStep 1066467 = 1599701) B1599701
theorem B1066483 : Blo 1064615 1066483 := bstep (se 1 (by rfl) ⟨799862, by rfl⟩ : syracuseStep 1066483 = 1599725) B1599725
theorem B1066499 : Blo 1064615 1066499 := bstep (se 1 (by rfl) ⟨799874, by rfl⟩ : syracuseStep 1066499 = 1599749) B1599749
theorem B1066515 : Blo 1064615 1066515 := bstep (se 1 (by rfl) ⟨799886, by rfl⟩ : syracuseStep 1066515 = 1599773) B1599773
theorem B1066531 : Blo 1064615 1066531 := bstep (se 1 (by rfl) ⟨799898, by rfl⟩ : syracuseStep 1066531 = 1599797) B1599797
theorem B1066547 : Blo 1064615 1066547 := bstep (se 1 (by rfl) ⟨799910, by rfl⟩ : syracuseStep 1066547 = 1599821) B1599821
theorem B1066563 : Blo 1064615 1066563 := bstep (se 1 (by rfl) ⟨799922, by rfl⟩ : syracuseStep 1066563 = 1599845) B1599845
theorem B1066579 : Blo 1064615 1066579 := bstep (se 1 (by rfl) ⟨799934, by rfl⟩ : syracuseStep 1066579 = 1599869) B1599869
theorem B1066595 : Blo 1064615 1066595 := bstep (se 1 (by rfl) ⟨799946, by rfl⟩ : syracuseStep 1066595 = 1599893) B1599893
theorem B1066611 : Blo 1064615 1066611 := bstep (se 1 (by rfl) ⟨799958, by rfl⟩ : syracuseStep 1066611 = 1599917) B1599917
theorem B1066627 : Blo 1064615 1066627 := bstep (se 1 (by rfl) ⟨799970, by rfl⟩ : syracuseStep 1066627 = 1599941) B1599941
theorem B1197715 : Blo 1064615 1197715 := bstep (se 1 (by rfl) ⟨898286, by rfl⟩ : syracuseStep 1197715 = 1796573) B1796573
theorem B1066643 : Blo 1064615 1066643 := bstep (se 1 (by rfl) ⟨799982, by rfl⟩ : syracuseStep 1066643 = 1599965) B1599965
theorem B1066659 : Blo 1064615 1066659 := bstep (se 1 (by rfl) ⟨799994, by rfl⟩ : syracuseStep 1066659 = 1599989) B1599989
theorem B1066675 : Blo 1064615 1066675 := bstep (se 1 (by rfl) ⟨800006, by rfl⟩ : syracuseStep 1066675 = 1600013) B1600013
theorem B1066691 : Blo 1064615 1066691 := bstep (se 1 (by rfl) ⟨800018, by rfl⟩ : syracuseStep 1066691 = 1600037) B1600037
theorem B1066707 : Blo 1064615 1066707 := bstep (se 1 (by rfl) ⟨800030, by rfl⟩ : syracuseStep 1066707 = 1600061) B1600061
theorem B1066723 : Blo 1064615 1066723 := bstep (se 1 (by rfl) ⟨800042, by rfl⟩ : syracuseStep 1066723 = 1600085) B1600085
theorem B1066739 : Blo 1064615 1066739 := bstep (se 1 (by rfl) ⟨800054, by rfl⟩ : syracuseStep 1066739 = 1600109) B1600109
theorem B1623809 : Blo 1064615 1623809 := bstep (se 2 (by rfl) ⟨608928, by rfl⟩ : syracuseStep 1623809 = 1217857) B1217857
theorem B1066755 : Blo 1064615 1066755 := bstep (se 1 (by rfl) ⟨800066, by rfl⟩ : syracuseStep 1066755 = 1600133) B1600133
theorem B1066771 : Blo 1064615 1066771 := bstep (se 1 (by rfl) ⟨800078, by rfl⟩ : syracuseStep 1066771 = 1600157) B1600157
theorem B1197859 : Blo 1064615 1197859 := bstep (se 1 (by rfl) ⟨898394, by rfl⟩ : syracuseStep 1197859 = 1796789) B1796789
theorem B1066787 : Blo 1064615 1066787 := bstep (se 1 (by rfl) ⟨800090, by rfl⟩ : syracuseStep 1066787 = 1600181) B1600181
theorem B1066803 : Blo 1064615 1066803 := bstep (se 1 (by rfl) ⟨800102, by rfl⟩ : syracuseStep 1066803 = 1600205) B1600205
theorem B12994357 : Blo 1064615 12994357 := bstep (se 5 (by rfl) ⟨609110, by rfl⟩ : syracuseStep 12994357 = 1218221) B1218221
theorem B1066819 : Blo 1064615 1066819 := bstep (se 1 (by rfl) ⟨800114, by rfl⟩ : syracuseStep 1066819 = 1600229) B1600229
theorem B1066835 : Blo 1064615 1066835 := bstep (se 1 (by rfl) ⟨800126, by rfl⟩ : syracuseStep 1066835 = 1600253) B1600253
theorem B1066851 : Blo 1064615 1066851 := bstep (se 1 (by rfl) ⟨800138, by rfl⟩ : syracuseStep 1066851 = 1600277) B1600277
theorem B1066867 : Blo 1064615 1066867 := bstep (se 1 (by rfl) ⟨800150, by rfl⟩ : syracuseStep 1066867 = 1600301) B1600301
theorem B1066883 : Blo 1064615 1066883 := bstep (se 1 (by rfl) ⟨800162, by rfl⟩ : syracuseStep 1066883 = 1600325) B1600325
theorem B2279299 : Blo 1064615 2279299 := bstep (se 1 (by rfl) ⟨1709474, by rfl⟩ : syracuseStep 2279299 = 3418949) B3418949
theorem B1066899 : Blo 1064615 1066899 := bstep (se 1 (by rfl) ⟨800174, by rfl⟩ : syracuseStep 1066899 = 1600349) B1600349
theorem B1623955 : Blo 1064615 1623955 := bstep (se 1 (by rfl) ⟨1217966, by rfl⟩ : syracuseStep 1623955 = 2435933) B2435933
theorem B1066915 : Blo 1064615 1066915 := bstep (se 1 (by rfl) ⟨800186, by rfl⟩ : syracuseStep 1066915 = 1600373) B1600373
theorem B1198003 : Blo 1064615 1198003 := bstep (se 1 (by rfl) ⟨898502, by rfl⟩ : syracuseStep 1198003 = 1797005) B1797005
theorem B1066931 : Blo 1064615 1066931 := bstep (se 1 (by rfl) ⟨800198, by rfl⟩ : syracuseStep 1066931 = 1600397) B1600397
theorem B1066947 : Blo 1064615 1066947 := bstep (se 1 (by rfl) ⟨800210, by rfl⟩ : syracuseStep 1066947 = 1600421) B1600421
theorem B6080453 : Blo 1064615 6080453 := bstep (se 4 (by rfl) ⟨570042, by rfl⟩ : syracuseStep 6080453 = 1140085) B1140085
theorem B1066963 : Blo 1064615 1066963 := bstep (se 1 (by rfl) ⟨800222, by rfl⟩ : syracuseStep 1066963 = 1600445) B1600445
theorem B1066979 : Blo 1064615 1066979 := bstep (se 1 (by rfl) ⟨800234, by rfl⟩ : syracuseStep 1066979 = 1600469) B1600469
theorem B3655651 : Blo 1064615 3655651 := bstep (se 1 (by rfl) ⟨2741738, by rfl⟩ : syracuseStep 3655651 = 5483477) B5483477
theorem B1066995 : Blo 1064615 1066995 := bstep (se 1 (by rfl) ⟨800246, by rfl⟩ : syracuseStep 1066995 = 1600493) B1600493
theorem B1067011 : Blo 1064615 1067011 := bstep (se 1 (by rfl) ⟨800258, by rfl⟩ : syracuseStep 1067011 = 1600517) B1600517
theorem B1067027 : Blo 1064615 1067027 := bstep (se 1 (by rfl) ⟨800270, by rfl⟩ : syracuseStep 1067027 = 1600541) B1600541
theorem B1067043 : Blo 1064615 1067043 := bstep (se 1 (by rfl) ⟨800282, by rfl⟩ : syracuseStep 1067043 = 1600565) B1600565
theorem B1067059 : Blo 1064615 1067059 := bstep (se 1 (by rfl) ⟨800294, by rfl⟩ : syracuseStep 1067059 = 1600589) B1600589
theorem B1198147 : Blo 1064615 1198147 := bstep (se 1 (by rfl) ⟨898610, by rfl⟩ : syracuseStep 1198147 = 1797221) B1797221
theorem B1067075 : Blo 1064615 1067075 := bstep (se 1 (by rfl) ⟨800306, by rfl⟩ : syracuseStep 1067075 = 1600613) B1600613
theorem B4048973 : Blo 1064615 4048973 := bstep (se 3 (by rfl) ⟨759182, by rfl⟩ : syracuseStep 4048973 = 1518365) B1518365
theorem B1067091 : Blo 1064615 1067091 := bstep (se 1 (by rfl) ⟨800318, by rfl⟩ : syracuseStep 1067091 = 1600637) B1600637
theorem B1067107 : Blo 1064615 1067107 := bstep (se 1 (by rfl) ⟨800330, by rfl⟩ : syracuseStep 1067107 = 1600661) B1600661
theorem B1067123 : Blo 1064615 1067123 := bstep (se 1 (by rfl) ⟨800342, by rfl⟩ : syracuseStep 1067123 = 1600685) B1600685
theorem B1067139 : Blo 1064615 1067139 := bstep (se 1 (by rfl) ⟨800354, by rfl⟩ : syracuseStep 1067139 = 1600709) B1600709
theorem B6146189 : Blo 1064615 6146189 := bstep (se 3 (by rfl) ⟨1152410, by rfl⟩ : syracuseStep 6146189 = 2304821) B2304821
theorem B3033233 : Blo 1064615 3033233 := bstep (se 2 (by rfl) ⟨1137462, by rfl⟩ : syracuseStep 3033233 = 2274925) B2274925
theorem B1230995 : Blo 1064615 1230995 := bstep (se 1 (by rfl) ⟨923246, by rfl⟩ : syracuseStep 1230995 = 1846493) B1846493
theorem B1067155 : Blo 1064615 1067155 := bstep (se 1 (by rfl) ⟨800366, by rfl⟩ : syracuseStep 1067155 = 1600733) B1600733
theorem B1067171 : Blo 1064615 1067171 := bstep (se 1 (by rfl) ⟨800378, by rfl⟩ : syracuseStep 1067171 = 1600757) B1600757
theorem B1067187 : Blo 1064615 1067187 := bstep (se 1 (by rfl) ⟨800390, by rfl⟩ : syracuseStep 1067187 = 1600781) B1600781
theorem B1067203 : Blo 1064615 1067203 := bstep (se 1 (by rfl) ⟨800402, by rfl⟩ : syracuseStep 1067203 = 1600805) B1600805
theorem B1198291 : Blo 1064615 1198291 := bstep (se 1 (by rfl) ⟨898718, by rfl⟩ : syracuseStep 1198291 = 1797437) B1797437
theorem B1067219 : Blo 1064615 1067219 := bstep (se 1 (by rfl) ⟨800414, by rfl⟩ : syracuseStep 1067219 = 1600829) B1600829
theorem B1067235 : Blo 1064615 1067235 := bstep (se 1 (by rfl) ⟨800426, by rfl⟩ : syracuseStep 1067235 = 1600853) B1600853
theorem B1067251 : Blo 1064615 1067251 := bstep (se 1 (by rfl) ⟨800438, by rfl⟩ : syracuseStep 1067251 = 1600877) B1600877
theorem B1067267 : Blo 1064615 1067267 := bstep (se 1 (by rfl) ⟨800450, by rfl⟩ : syracuseStep 1067267 = 1600901) B1600901
theorem B1067283 : Blo 1064615 1067283 := bstep (se 1 (by rfl) ⟨800462, by rfl⟩ : syracuseStep 1067283 = 1600925) B1600925
theorem B1067299 : Blo 1064615 1067299 := bstep (se 1 (by rfl) ⟨800474, by rfl⟩ : syracuseStep 1067299 = 1600949) B1600949
theorem B1919281 : Blo 1064615 1919281 := bstep (se 2 (by rfl) ⟨719730, by rfl⟩ : syracuseStep 1919281 = 1439461) B1439461
theorem B1624369 : Blo 1064615 1624369 := bstep (se 2 (by rfl) ⟨609138, by rfl⟩ : syracuseStep 1624369 = 1218277) B1218277
theorem B1067315 : Blo 1064615 1067315 := bstep (se 1 (by rfl) ⟨800486, by rfl⟩ : syracuseStep 1067315 = 1600973) B1600973
theorem B1067331 : Blo 1064615 1067331 := bstep (se 1 (by rfl) ⟨800498, by rfl⟩ : syracuseStep 1067331 = 1600997) B1600997
theorem B1067347 : Blo 1064615 1067347 := bstep (se 1 (by rfl) ⟨800510, by rfl⟩ : syracuseStep 1067347 = 1601021) B1601021
theorem B1198435 : Blo 1064615 1198435 := bstep (se 1 (by rfl) ⟨898826, by rfl⟩ : syracuseStep 1198435 = 1797653) B1797653
theorem B1067363 : Blo 1064615 1067363 := bstep (se 1 (by rfl) ⟨800522, by rfl⟩ : syracuseStep 1067363 = 1601045) B1601045
theorem B11553137 : Blo 1064615 11553137 := bstep (se 2 (by rfl) ⟨4332426, by rfl⟩ : syracuseStep 11553137 = 8664853) B8664853
theorem B1067379 : Blo 1064615 1067379 := bstep (se 1 (by rfl) ⟨800534, by rfl⟩ : syracuseStep 1067379 = 1601069) B1601069
theorem B1067395 : Blo 1064615 1067395 := bstep (se 1 (by rfl) ⟨800546, by rfl⟩ : syracuseStep 1067395 = 1601093) B1601093
theorem B1067411 : Blo 1064615 1067411 := bstep (se 1 (by rfl) ⟨800558, by rfl⟩ : syracuseStep 1067411 = 1601117) B1601117
theorem B1067427 : Blo 1064615 1067427 := bstep (se 1 (by rfl) ⟨800570, by rfl⟩ : syracuseStep 1067427 = 1601141) B1601141
theorem B5392817 : Blo 1064615 5392817 := bstep (se 2 (by rfl) ⟨2022306, by rfl⟩ : syracuseStep 5392817 = 4044613) B4044613
theorem B1067443 : Blo 1064615 1067443 := bstep (se 1 (by rfl) ⟨800582, by rfl⟩ : syracuseStep 1067443 = 1601165) B1601165
theorem B1067459 : Blo 1064615 1067459 := bstep (se 1 (by rfl) ⟨800594, by rfl⟩ : syracuseStep 1067459 = 1601189) B1601189
theorem B1067475 : Blo 1064615 1067475 := bstep (se 1 (by rfl) ⟨800606, by rfl⟩ : syracuseStep 1067475 = 1601213) B1601213
theorem B1067491 : Blo 1064615 1067491 := bstep (se 1 (by rfl) ⟨800618, by rfl⟩ : syracuseStep 1067491 = 1601237) B1601237
theorem B5556707 : Blo 1064615 5556707 := bstep (se 1 (by rfl) ⟨4167530, by rfl⟩ : syracuseStep 5556707 = 8335061) B8335061
theorem B1198579 : Blo 1064615 1198579 := bstep (se 1 (by rfl) ⟨898934, by rfl⟩ : syracuseStep 1198579 = 1797869) B1797869
theorem B1067507 : Blo 1064615 1067507 := bstep (se 1 (by rfl) ⟨800630, by rfl⟩ : syracuseStep 1067507 = 1601261) B1601261
theorem B1067523 : Blo 1064615 1067523 := bstep (se 1 (by rfl) ⟨800642, by rfl⟩ : syracuseStep 1067523 = 1601285) B1601285
theorem B1067539 : Blo 1064615 1067539 := bstep (se 1 (by rfl) ⟨800654, by rfl⟩ : syracuseStep 1067539 = 1601309) B1601309
theorem B1067555 : Blo 1064615 1067555 := bstep (se 1 (by rfl) ⟨800666, by rfl⟩ : syracuseStep 1067555 = 1601333) B1601333
theorem B1067571 : Blo 1064615 1067571 := bstep (se 1 (by rfl) ⟨800678, by rfl⟩ : syracuseStep 1067571 = 1601357) B1601357
theorem B1067587 : Blo 1064615 1067587 := bstep (se 1 (by rfl) ⟨800690, by rfl⟩ : syracuseStep 1067587 = 1601381) B1601381
theorem B1067603 : Blo 1064615 1067603 := bstep (se 1 (by rfl) ⟨800702, by rfl⟩ : syracuseStep 1067603 = 1601405) B1601405
theorem B10930787 : Blo 1064615 10930787 := bstep (se 1 (by rfl) ⟨8198090, by rfl⟩ : syracuseStep 10930787 = 16396181) B16396181
theorem B1067619 : Blo 1064615 1067619 := bstep (se 1 (by rfl) ⟨800714, by rfl⟩ : syracuseStep 1067619 = 1601429) B1601429
theorem B1067635 : Blo 1064615 1067635 := bstep (se 1 (by rfl) ⟨800726, by rfl⟩ : syracuseStep 1067635 = 1601453) B1601453
theorem B1198723 : Blo 1064615 1198723 := bstep (se 1 (by rfl) ⟨899042, by rfl⟩ : syracuseStep 1198723 = 1798085) B1798085
theorem B1067651 : Blo 1064615 1067651 := bstep (se 1 (by rfl) ⟨800738, by rfl⟩ : syracuseStep 1067651 = 1601477) B1601477
theorem B1067667 : Blo 1064615 1067667 := bstep (se 1 (by rfl) ⟨800750, by rfl⟩ : syracuseStep 1067667 = 1601501) B1601501
theorem B1067683 : Blo 1064615 1067683 := bstep (se 1 (by rfl) ⟨800762, by rfl⟩ : syracuseStep 1067683 = 1601525) B1601525
theorem B1821361 : Blo 1064615 1821361 := bstep (se 2 (by rfl) ⟨683010, by rfl⟩ : syracuseStep 1821361 = 1366021) B1366021
theorem B1067699 : Blo 1064615 1067699 := bstep (se 1 (by rfl) ⟨800774, by rfl⟩ : syracuseStep 1067699 = 1601549) B1601549
theorem B1067715 : Blo 1064615 1067715 := bstep (se 1 (by rfl) ⟨800786, by rfl⟩ : syracuseStep 1067715 = 1601573) B1601573
theorem B2280145 : Blo 1064615 2280145 := bstep (se 2 (by rfl) ⟨855054, by rfl⟩ : syracuseStep 2280145 = 1710109) B1710109
theorem B1067731 : Blo 1064615 1067731 := bstep (se 1 (by rfl) ⟨800798, by rfl⟩ : syracuseStep 1067731 = 1601597) B1601597
theorem B1067747 : Blo 1064615 1067747 := bstep (se 1 (by rfl) ⟨800810, by rfl⟩ : syracuseStep 1067747 = 1601621) B1601621
theorem B1067763 : Blo 1064615 1067763 := bstep (se 1 (by rfl) ⟨800822, by rfl⟩ : syracuseStep 1067763 = 1601645) B1601645
theorem B2738947 : Blo 1064615 2738947 := bstep (se 1 (by rfl) ⟨2054210, by rfl⟩ : syracuseStep 2738947 = 4108421) B4108421
theorem B1067779 : Blo 1064615 1067779 := bstep (se 1 (by rfl) ⟨800834, by rfl⟩ : syracuseStep 1067779 = 1601669) B1601669
theorem B1198867 : Blo 1064615 1198867 := bstep (se 1 (by rfl) ⟨899150, by rfl⟩ : syracuseStep 1198867 = 1798301) B1798301
theorem B1067795 : Blo 1064615 1067795 := bstep (se 1 (by rfl) ⟨800846, by rfl⟩ : syracuseStep 1067795 = 1601693) B1601693
theorem B1067811 : Blo 1064615 1067811 := bstep (se 1 (by rfl) ⟨800858, by rfl⟩ : syracuseStep 1067811 = 1601717) B1601717
theorem B1067827 : Blo 1064615 1067827 := bstep (se 1 (by rfl) ⟨800870, by rfl⟩ : syracuseStep 1067827 = 1601741) B1601741
theorem B1067843 : Blo 1064615 1067843 := bstep (se 1 (by rfl) ⟨800882, by rfl⟩ : syracuseStep 1067843 = 1601765) B1601765
theorem B1067859 : Blo 1064615 1067859 := bstep (se 1 (by rfl) ⟨800894, by rfl⟩ : syracuseStep 1067859 = 1601789) B1601789
theorem B8637283 : Blo 1064615 8637283 := bstep (se 1 (by rfl) ⟨6477962, by rfl⟩ : syracuseStep 8637283 = 12955925) B12955925
theorem B1919843 : Blo 1064615 1919843 := bstep (se 1 (by rfl) ⟨1439882, by rfl⟩ : syracuseStep 1919843 = 2879765) B2879765
theorem B1067875 : Blo 1064615 1067875 := bstep (se 1 (by rfl) ⟨800906, by rfl⟩ : syracuseStep 1067875 = 1601813) B1601813
theorem B4049777 : Blo 1064615 4049777 := bstep (se 2 (by rfl) ⟨1518666, by rfl⟩ : syracuseStep 4049777 = 3037333) B3037333
theorem B1067891 : Blo 1064615 1067891 := bstep (se 1 (by rfl) ⟨800918, by rfl⟩ : syracuseStep 1067891 = 1601837) B1601837
theorem B1067907 : Blo 1064615 1067907 := bstep (se 1 (by rfl) ⟨800930, by rfl⟩ : syracuseStep 1067907 = 1601861) B1601861
theorem B1067923 : Blo 1064615 1067923 := bstep (se 1 (by rfl) ⟨800942, by rfl⟩ : syracuseStep 1067923 = 1601885) B1601885
theorem B1199011 : Blo 1064615 1199011 := bstep (se 1 (by rfl) ⟨899258, by rfl⟩ : syracuseStep 1199011 = 1798517) B1798517
theorem B1067939 : Blo 1064615 1067939 := bstep (se 1 (by rfl) ⟨800954, by rfl⟩ : syracuseStep 1067939 = 1601909) B1601909
theorem B1067955 : Blo 1064615 1067955 := bstep (se 1 (by rfl) ⟨800966, by rfl⟩ : syracuseStep 1067955 = 1601933) B1601933
theorem B1067971 : Blo 1064615 1067971 := bstep (se 1 (by rfl) ⟨800978, by rfl⟩ : syracuseStep 1067971 = 1601957) B1601957
theorem B1067987 : Blo 1064615 1067987 := bstep (se 1 (by rfl) ⟨800990, by rfl⟩ : syracuseStep 1067987 = 1601981) B1601981
theorem B1068003 : Blo 1064615 1068003 := bstep (se 1 (by rfl) ⟨801002, by rfl⟩ : syracuseStep 1068003 = 1602005) B1602005
theorem B1068019 : Blo 1064615 1068019 := bstep (se 1 (by rfl) ⟨801014, by rfl⟩ : syracuseStep 1068019 = 1602029) B1602029
theorem B1068035 : Blo 1064615 1068035 := bstep (se 1 (by rfl) ⟨801026, by rfl⟩ : syracuseStep 1068035 = 1602053) B1602053
theorem B1068051 : Blo 1064615 1068051 := bstep (se 1 (by rfl) ⟨801038, by rfl⟩ : syracuseStep 1068051 = 1602077) B1602077
theorem B1068067 : Blo 1064615 1068067 := bstep (se 1 (by rfl) ⟨801050, by rfl⟩ : syracuseStep 1068067 = 1602101) B1602101
theorem B1199155 : Blo 1064615 1199155 := bstep (se 1 (by rfl) ⟨899366, by rfl⟩ : syracuseStep 1199155 = 1798733) B1798733
theorem B1068083 : Blo 1064615 1068083 := bstep (se 1 (by rfl) ⟨801062, by rfl⟩ : syracuseStep 1068083 = 1602125) B1602125
theorem B1068099 : Blo 1064615 1068099 := bstep (se 1 (by rfl) ⟨801074, by rfl⟩ : syracuseStep 1068099 = 1602149) B1602149
theorem B3034189 : Blo 1064615 3034189 := bstep (se 3 (by rfl) ⟨568910, by rfl⟩ : syracuseStep 3034189 = 1137821) B1137821
theorem B1068115 : Blo 1064615 1068115 := bstep (se 1 (by rfl) ⟨801086, by rfl⟩ : syracuseStep 1068115 = 1602173) B1602173
theorem B1068131 : Blo 1064615 1068131 := bstep (se 1 (by rfl) ⟨801098, by rfl⟩ : syracuseStep 1068131 = 1602197) B1602197
theorem B1068147 : Blo 1064615 1068147 := bstep (se 1 (by rfl) ⟨801110, by rfl⟩ : syracuseStep 1068147 = 1602221) B1602221
theorem B1068163 : Blo 1064615 1068163 := bstep (se 1 (by rfl) ⟨801122, by rfl⟩ : syracuseStep 1068163 = 1602245) B1602245
theorem B1068179 : Blo 1064615 1068179 := bstep (se 1 (by rfl) ⟨801134, by rfl⟩ : syracuseStep 1068179 = 1602269) B1602269
theorem B1068195 : Blo 1064615 1068195 := bstep (se 1 (by rfl) ⟨801146, by rfl⟩ : syracuseStep 1068195 = 1602293) B1602293
theorem B1068211 : Blo 1064615 1068211 := bstep (se 1 (by rfl) ⟨801158, by rfl⟩ : syracuseStep 1068211 = 1602317) B1602317
theorem B1199299 : Blo 1064615 1199299 := bstep (se 1 (by rfl) ⟨899474, by rfl⟩ : syracuseStep 1199299 = 1798949) B1798949
theorem B1068227 : Blo 1064615 1068227 := bstep (se 1 (by rfl) ⟨801170, by rfl⟩ : syracuseStep 1068227 = 1602341) B1602341
theorem B1068243 : Blo 1064615 1068243 := bstep (se 1 (by rfl) ⟨801182, by rfl⟩ : syracuseStep 1068243 = 1602365) B1602365
theorem B1068259 : Blo 1064615 1068259 := bstep (se 1 (by rfl) ⟨801194, by rfl⟩ : syracuseStep 1068259 = 1602389) B1602389
theorem B1068275 : Blo 1064615 1068275 := bstep (se 1 (by rfl) ⟨801206, by rfl⟩ : syracuseStep 1068275 = 1602413) B1602413
theorem B1068291 : Blo 1064615 1068291 := bstep (se 1 (by rfl) ⟨801218, by rfl⟩ : syracuseStep 1068291 = 1602437) B1602437
theorem B1068307 : Blo 1064615 1068307 := bstep (se 1 (by rfl) ⟨801230, by rfl⟩ : syracuseStep 1068307 = 1602461) B1602461
theorem B1068323 : Blo 1064615 1068323 := bstep (se 1 (by rfl) ⟨801242, by rfl⟩ : syracuseStep 1068323 = 1602485) B1602485
theorem B3034417 : Blo 1064615 3034417 := bstep (se 2 (by rfl) ⟨1137906, by rfl⟩ : syracuseStep 3034417 = 2275813) B2275813
theorem B1068339 : Blo 1064615 1068339 := bstep (se 1 (by rfl) ⟨801254, by rfl⟩ : syracuseStep 1068339 = 1602509) B1602509
theorem B1068355 : Blo 1064615 1068355 := bstep (se 1 (by rfl) ⟨801266, by rfl⟩ : syracuseStep 1068355 = 1602533) B1602533
theorem B1199443 : Blo 1064615 1199443 := bstep (se 1 (by rfl) ⟨899582, by rfl⟩ : syracuseStep 1199443 = 1799165) B1799165
theorem B1068371 : Blo 1064615 1068371 := bstep (se 1 (by rfl) ⟨801278, by rfl⟩ : syracuseStep 1068371 = 1602557) B1602557
theorem B1068387 : Blo 1064615 1068387 := bstep (se 1 (by rfl) ⟨801290, by rfl⟩ : syracuseStep 1068387 = 1602581) B1602581
theorem B1068403 : Blo 1064615 1068403 := bstep (se 1 (by rfl) ⟨801302, by rfl⟩ : syracuseStep 1068403 = 1602605) B1602605
theorem B1068419 : Blo 1064615 1068419 := bstep (se 1 (by rfl) ⟨801314, by rfl⟩ : syracuseStep 1068419 = 1602629) B1602629
theorem B1068435 : Blo 1064615 1068435 := bstep (se 1 (by rfl) ⟨801326, by rfl⟩ : syracuseStep 1068435 = 1602653) B1602653
theorem B3001763 : Blo 1064615 3001763 := bstep (se 1 (by rfl) ⟨2251322, by rfl⟩ : syracuseStep 3001763 = 4502645) B4502645
theorem B1068451 : Blo 1064615 1068451 := bstep (se 1 (by rfl) ⟨801338, by rfl⟩ : syracuseStep 1068451 = 1602677) B1602677
theorem B1068467 : Blo 1064615 1068467 := bstep (se 1 (by rfl) ⟨801350, by rfl⟩ : syracuseStep 1068467 = 1602701) B1602701
theorem B1068483 : Blo 1064615 1068483 := bstep (se 1 (by rfl) ⟨801362, by rfl⟩ : syracuseStep 1068483 = 1602725) B1602725
theorem B3034577 : Blo 1064615 3034577 := bstep (se 2 (by rfl) ⟨1137966, by rfl⟩ : syracuseStep 3034577 = 2275933) B2275933
theorem B1068499 : Blo 1064615 1068499 := bstep (se 1 (by rfl) ⟨801374, by rfl⟩ : syracuseStep 1068499 = 1602749) B1602749
theorem B1199587 : Blo 1064615 1199587 := bstep (se 1 (by rfl) ⟨899690, by rfl⟩ : syracuseStep 1199587 = 1799381) B1799381
theorem B1068515 : Blo 1064615 1068515 := bstep (se 1 (by rfl) ⟨801386, by rfl⟩ : syracuseStep 1068515 = 1602773) B1602773
theorem B1068531 : Blo 1064615 1068531 := bstep (se 1 (by rfl) ⟨801398, by rfl⟩ : syracuseStep 1068531 = 1602797) B1602797
theorem B1461763 : Blo 1064615 1461763 := bstep (se 1 (by rfl) ⟨1096322, by rfl⟩ : syracuseStep 1461763 = 2192645) B2192645
theorem B1068547 : Blo 1064615 1068547 := bstep (se 1 (by rfl) ⟨801410, by rfl⟩ : syracuseStep 1068547 = 1602821) B1602821
theorem B4050445 : Blo 1064615 4050445 := bstep (se 3 (by rfl) ⟨759458, by rfl⟩ : syracuseStep 4050445 = 1518917) B1518917
theorem B1068563 : Blo 1064615 1068563 := bstep (se 1 (by rfl) ⟨801422, by rfl⟩ : syracuseStep 1068563 = 1602845) B1602845
theorem B1068579 : Blo 1064615 1068579 := bstep (se 1 (by rfl) ⟨801434, by rfl⟩ : syracuseStep 1068579 = 1602869) B1602869
theorem B1068595 : Blo 1064615 1068595 := bstep (se 1 (by rfl) ⟨801446, by rfl⟩ : syracuseStep 1068595 = 1602893) B1602893
theorem B3034691 : Blo 1064615 3034691 := bstep (se 1 (by rfl) ⟨2276018, by rfl⟩ : syracuseStep 3034691 = 4552037) B4552037
theorem B1068611 : Blo 1064615 1068611 := bstep (se 1 (by rfl) ⟨801458, by rfl⟩ : syracuseStep 1068611 = 1602917) B1602917
theorem B1920593 : Blo 1064615 1920593 := bstep (se 2 (by rfl) ⟨720222, by rfl⟩ : syracuseStep 1920593 = 1440445) B1440445
theorem B1199731 : Blo 1064615 1199731 := bstep (se 1 (by rfl) ⟨899798, by rfl⟩ : syracuseStep 1199731 = 1799597) B1799597
theorem B1461907 : Blo 1064615 1461907 := bstep (se 1 (by rfl) ⟨1096430, by rfl⟩ : syracuseStep 1461907 = 2192861) B2192861
theorem B1199875 : Blo 1064615 1199875 := bstep (se 1 (by rfl) ⟨899906, by rfl⟩ : syracuseStep 1199875 = 1799813) B1799813
theorem B5394275 : Blo 1064615 5394275 := bstep (se 1 (by rfl) ⟨4045706, by rfl⟩ : syracuseStep 5394275 = 8091413) B8091413
theorem B1920881 : Blo 1064615 1920881 := bstep (se 2 (by rfl) ⟨720330, by rfl⟩ : syracuseStep 1920881 = 1440661) B1440661
theorem B1200019 : Blo 1064615 1200019 := bstep (se 1 (by rfl) ⟨900014, by rfl⟩ : syracuseStep 1200019 = 1800029) B1800029
theorem B1822675 : Blo 1064615 1822675 := bstep (se 1 (by rfl) ⟨1367006, by rfl⟩ : syracuseStep 1822675 = 2734013) B2734013
theorem B4870115 : Blo 1064615 4870115 := bstep (se 1 (by rfl) ⟨3652586, by rfl⟩ : syracuseStep 4870115 = 7305173) B7305173
theorem B1200163 : Blo 1064615 1200163 := bstep (se 1 (by rfl) ⟨900122, by rfl⟩ : syracuseStep 1200163 = 1800245) B1800245
theorem B1921105 : Blo 1064615 1921105 := bstep (se 2 (by rfl) ⟨720414, by rfl⟩ : syracuseStep 1921105 = 1440829) B1440829
theorem B1921169 : Blo 1064615 1921169 := bstep (se 2 (by rfl) ⟨720438, by rfl⟩ : syracuseStep 1921169 = 1440877) B1440877
theorem B1200307 : Blo 1064615 1200307 := bstep (se 1 (by rfl) ⟨900230, by rfl⟩ : syracuseStep 1200307 = 1800461) B1800461
theorem B4051235 : Blo 1064615 4051235 := bstep (se 1 (by rfl) ⟨3038426, by rfl⟩ : syracuseStep 4051235 = 6076853) B6076853
theorem B1200451 : Blo 1064615 1200451 := bstep (se 1 (by rfl) ⟨900338, by rfl⟩ : syracuseStep 1200451 = 1800677) B1800677
theorem B1200595 : Blo 1064615 1200595 := bstep (se 1 (by rfl) ⟨900446, by rfl⟩ : syracuseStep 1200595 = 1800893) B1800893
theorem B3035693 : Blo 1064615 3035693 := bstep (se 3 (by rfl) ⟨569192, by rfl⟩ : syracuseStep 3035693 = 1138385) B1138385
theorem B2282033 : Blo 1064615 2282033 := bstep (se 2 (by rfl) ⟨855762, by rfl⟩ : syracuseStep 2282033 = 1711525) B1711525
theorem B1200739 : Blo 1064615 1200739 := bstep (se 1 (by rfl) ⟨900554, by rfl⟩ : syracuseStep 1200739 = 1801109) B1801109
theorem B2740835 : Blo 1064615 2740835 := bstep (se 1 (by rfl) ⟨2055626, by rfl⟩ : syracuseStep 2740835 = 4111253) B4111253
theorem B13652621 : Blo 1064615 13652621 := bstep (se 3 (by rfl) ⟨2559866, by rfl⟩ : syracuseStep 13652621 = 5119733) B5119733
theorem B5395085 : Blo 1064615 5395085 := bstep (se 3 (by rfl) ⟨1011578, by rfl⟩ : syracuseStep 5395085 = 2023157) B2023157
theorem B3035875 : Blo 1064615 3035875 := bstep (se 1 (by rfl) ⟨2276906, by rfl⟩ : syracuseStep 3035875 = 4553813) B4553813
theorem B7688945 : Blo 1064615 7688945 := bstep (se 2 (by rfl) ⟨2883354, by rfl⟩ : syracuseStep 7688945 = 5766709) B5766709
theorem B1200883 : Blo 1064615 1200883 := bstep (se 1 (by rfl) ⟨900662, by rfl⟩ : syracuseStep 1200883 = 1801325) B1801325
theorem B3036035 : Blo 1064615 3036035 := bstep (se 1 (by rfl) ⟨2277026, by rfl⟩ : syracuseStep 3036035 = 4554053) B4554053
theorem B1201027 : Blo 1064615 1201027 := bstep (se 1 (by rfl) ⟨900770, by rfl⟩ : syracuseStep 1201027 = 1801541) B1801541
theorem B3593105 : Blo 1064615 3593105 := bstep (se 2 (by rfl) ⟨1347414, by rfl⟩ : syracuseStep 3593105 = 2694829) B2694829
theorem B6837155 : Blo 1064615 6837155 := bstep (se 1 (by rfl) ⟨5127866, by rfl⟩ : syracuseStep 6837155 = 10255733) B10255733
theorem B4051889 : Blo 1064615 4051889 := bstep (se 2 (by rfl) ⟨1519458, by rfl⟩ : syracuseStep 4051889 = 3038917) B3038917
theorem B1201171 : Blo 1064615 1201171 := bstep (se 1 (by rfl) ⟨900878, by rfl⟩ : syracuseStep 1201171 = 1801757) B1801757
theorem B1201315 : Blo 1064615 1201315 := bstep (se 1 (by rfl) ⟨900986, by rfl⟩ : syracuseStep 1201315 = 1801973) B1801973
theorem B1201459 : Blo 1064615 1201459 := bstep (se 1 (by rfl) ⟨901094, by rfl⟩ : syracuseStep 1201459 = 1802189) B1802189
theorem B5133709 : Blo 1064615 5133709 := bstep (se 3 (by rfl) ⟨962570, by rfl⟩ : syracuseStep 5133709 = 1925141) B1925141
theorem B3593645 : Blo 1064615 3593645 := bstep (se 3 (by rfl) ⟨673808, by rfl⟩ : syracuseStep 3593645 = 1347617) B1347617
theorem B1201603 : Blo 1064615 1201603 := bstep (se 1 (by rfl) ⟨901202, by rfl⟩ : syracuseStep 1201603 = 1802405) B1802405
theorem B8639941 : Blo 1064615 8639941 := bstep (se 4 (by rfl) ⟨809994, by rfl⟩ : syracuseStep 8639941 = 1619989) B1619989
theorem B3593699 : Blo 1064615 3593699 := bstep (se 1 (by rfl) ⟨2695274, by rfl⟩ : syracuseStep 3593699 = 5390549) B5390549
theorem B1824241 : Blo 1064615 1824241 := bstep (se 2 (by rfl) ⟨684090, by rfl⟩ : syracuseStep 1824241 = 1368181) B1368181
theorem B1201747 : Blo 1064615 1201747 := bstep (se 1 (by rfl) ⟨901310, by rfl⟩ : syracuseStep 1201747 = 1802621) B1802621
theorem B1201891 : Blo 1064615 1201891 := bstep (se 1 (by rfl) ⟨901418, by rfl⟩ : syracuseStep 1201891 = 1802837) B1802837
theorem B3593969 : Blo 1064615 3593969 := bstep (se 2 (by rfl) ⟨1347738, by rfl⟩ : syracuseStep 3593969 = 2695477) B2695477
theorem B1922915 : Blo 1064615 1922915 := bstep (se 1 (by rfl) ⟨1442186, by rfl⟩ : syracuseStep 1922915 = 2884373) B2884373
theorem B1202035 : Blo 1064615 1202035 := bstep (se 1 (by rfl) ⟨901526, by rfl⟩ : syracuseStep 1202035 = 1803053) B1803053
theorem B22763405 : Blo 1064615 22763405 := bstep (se 3 (by rfl) ⟨4268138, by rfl⟩ : syracuseStep 22763405 = 8536277) B8536277
theorem B3037105 : Blo 1064615 3037105 := bstep (se 2 (by rfl) ⟨1138914, by rfl⟩ : syracuseStep 3037105 = 2277829) B2277829
theorem B7690211 : Blo 1064615 7690211 := bstep (se 1 (by rfl) ⟨5767658, by rfl⟩ : syracuseStep 7690211 = 11535317) B11535317
theorem B1202179 : Blo 1064615 1202179 := bstep (se 1 (by rfl) ⟨901634, by rfl⟩ : syracuseStep 1202179 = 1803269) B1803269
theorem B5756933 : Blo 1064615 5756933 := bstep (se 4 (by rfl) ⟨539712, by rfl⟩ : syracuseStep 5756933 = 1079425) B1079425
theorem B2021411 : Blo 1064615 2021411 := bstep (se 1 (by rfl) ⟨1516058, by rfl⟩ : syracuseStep 2021411 = 3032117) B3032117
theorem B1923203 : Blo 1064615 1923203 := bstep (se 1 (by rfl) ⟨1442402, by rfl⟩ : syracuseStep 1923203 = 2884805) B2884805
theorem B3594509 : Blo 1064615 3594509 := bstep (se 3 (by rfl) ⟨673970, by rfl⟩ : syracuseStep 3594509 = 1347941) B1347941
theorem B11688245 : Blo 1064615 11688245 := bstep (se 5 (by rfl) ⟨547886, by rfl⟩ : syracuseStep 11688245 = 1095773) B1095773
theorem B1136963 : Blo 1064615 1136963 := bstep (se 1 (by rfl) ⟨852722, by rfl⟩ : syracuseStep 1136963 = 1705445) B1705445
theorem B2021699 : Blo 1064615 2021699 := bstep (se 1 (by rfl) ⟨1516274, by rfl⟩ : syracuseStep 2021699 = 3032549) B3032549
theorem B3594563 : Blo 1064615 3594563 := bstep (se 1 (by rfl) ⟨2695922, by rfl⟩ : syracuseStep 3594563 = 5391845) B5391845
theorem B4053347 : Blo 1064615 4053347 := bstep (se 1 (by rfl) ⟨3040010, by rfl⟩ : syracuseStep 4053347 = 6080021) B6080021
theorem B4053361 : Blo 1064615 4053361 := bstep (se 2 (by rfl) ⟨1520010, by rfl⟩ : syracuseStep 4053361 = 3040021) B3040021
theorem B16407011 : Blo 1064615 16407011 := bstep (se 1 (by rfl) ⟨12305258, by rfl⟩ : syracuseStep 16407011 = 24610517) B24610517
theorem B7494149 : Blo 1064615 7494149 := bstep (se 4 (by rfl) ⟨702576, by rfl⟩ : syracuseStep 7494149 = 1405153) B1405153
theorem B4938317 : Blo 1064615 4938317 := bstep (se 3 (by rfl) ⟨925934, by rfl⟩ : syracuseStep 4938317 = 1851869) B1851869
theorem B3594833 : Blo 1064615 3594833 := bstep (se 2 (by rfl) ⟨1348062, by rfl⟩ : syracuseStep 3594833 = 2696125) B2696125
theorem B3595373 : Blo 1064615 3595373 := bstep (se 3 (by rfl) ⟨674132, by rfl⟩ : syracuseStep 3595373 = 1348265) B1348265
theorem B3595427 : Blo 1064615 3595427 := bstep (se 1 (by rfl) ⟨2696570, by rfl⟩ : syracuseStep 3595427 = 5393141) B5393141
theorem B3038381 : Blo 1064615 3038381 := bstep (se 3 (by rfl) ⟨569696, by rfl⟩ : syracuseStep 3038381 = 1139393) B1139393
theorem B2022641 : Blo 1064615 2022641 := bstep (se 2 (by rfl) ⟨758490, by rfl⟩ : syracuseStep 2022641 = 1516981) B1516981
theorem B1924355 : Blo 1064615 1924355 := bstep (se 1 (by rfl) ⟨1443266, by rfl⟩ : syracuseStep 1924355 = 2886533) B2886533
theorem B2055473 : Blo 1064615 2055473 := bstep (se 2 (by rfl) ⟨770802, by rfl⟩ : syracuseStep 2055473 = 1541605) B1541605
theorem B8314211 : Blo 1064615 8314211 := bstep (se 1 (by rfl) ⟨6235658, by rfl⟩ : syracuseStep 8314211 = 12471317) B12471317
theorem B3038563 : Blo 1064615 3038563 := bstep (se 1 (by rfl) ⟨2278922, by rfl⟩ : syracuseStep 3038563 = 4557845) B4557845
theorem B3038609 : Blo 1064615 3038609 := bstep (se 2 (by rfl) ⟨1139478, by rfl⟩ : syracuseStep 3038609 = 2278957) B2278957
theorem B3595697 : Blo 1064615 3595697 := bstep (se 2 (by rfl) ⟨1348386, by rfl⟩ : syracuseStep 3595697 = 2696773) B2696773
theorem B5398001 : Blo 1064615 5398001 := bstep (se 2 (by rfl) ⟨2024250, by rfl⟩ : syracuseStep 5398001 = 4048501) B4048501
theorem B1596929 : Blo 1064615 1596929 := bstep (se 2 (by rfl) ⟨598848, by rfl⟩ : syracuseStep 1596929 = 1197697) B1197697
theorem B1596947 : Blo 1064615 1596947 := bstep (se 1 (by rfl) ⟨1197710, by rfl⟩ : syracuseStep 1596947 = 2395421) B2395421
theorem B1596977 : Blo 1064615 1596977 := bstep (se 2 (by rfl) ⟨598866, by rfl⟩ : syracuseStep 1596977 = 1197733) B1197733
theorem B1596995 : Blo 1064615 1596995 := bstep (se 1 (by rfl) ⟨1197746, by rfl⟩ : syracuseStep 1596995 = 2395493) B2395493
theorem B1597025 : Blo 1064615 1597025 := bstep (se 2 (by rfl) ⟨598884, by rfl⟩ : syracuseStep 1597025 = 1197769) B1197769
theorem B5758577 : Blo 1064615 5758577 := bstep (se 2 (by rfl) ⟨2159466, by rfl⟩ : syracuseStep 5758577 = 4318933) B4318933
theorem B1597043 : Blo 1064615 1597043 := bstep (se 1 (by rfl) ⟨1197782, by rfl⟩ : syracuseStep 1597043 = 2395565) B2395565
theorem B1597073 : Blo 1064615 1597073 := bstep (se 2 (by rfl) ⟨598902, by rfl⟩ : syracuseStep 1597073 = 1197805) B1197805
theorem B1597091 : Blo 1064615 1597091 := bstep (se 1 (by rfl) ⟨1197818, by rfl⟩ : syracuseStep 1597091 = 2395637) B2395637
theorem B1597121 : Blo 1064615 1597121 := bstep (se 2 (by rfl) ⟨598920, by rfl⟩ : syracuseStep 1597121 = 1197841) B1197841
theorem B9100997 : Blo 1064615 9100997 := bstep (se 4 (by rfl) ⟨853218, by rfl⟩ : syracuseStep 9100997 = 1706437) B1706437
theorem B3464909 : Blo 1064615 3464909 := bstep (se 3 (by rfl) ⟨649670, by rfl⟩ : syracuseStep 3464909 = 1299341) B1299341
theorem B1597139 : Blo 1064615 1597139 := bstep (se 1 (by rfl) ⟨1197854, by rfl⟩ : syracuseStep 1597139 = 2395709) B2395709
theorem B1597169 : Blo 1064615 1597169 := bstep (se 2 (by rfl) ⟨598938, by rfl⟩ : syracuseStep 1597169 = 1197877) B1197877
theorem B1597187 : Blo 1064615 1597187 := bstep (se 1 (by rfl) ⟨1197890, by rfl⟩ : syracuseStep 1597187 = 2395781) B2395781
theorem B1597217 : Blo 1064615 1597217 := bstep (se 2 (by rfl) ⟨598956, by rfl⟩ : syracuseStep 1597217 = 1197913) B1197913
theorem B4054819 : Blo 1064615 4054819 := bstep (se 1 (by rfl) ⟨3041114, by rfl⟩ : syracuseStep 4054819 = 6082229) B6082229
theorem B1597235 : Blo 1064615 1597235 := bstep (se 1 (by rfl) ⟨1197926, by rfl⟩ : syracuseStep 1597235 = 2395853) B2395853
theorem B1597265 : Blo 1064615 1597265 := bstep (se 2 (by rfl) ⟨598974, by rfl⟩ : syracuseStep 1597265 = 1197949) B1197949
theorem B1597283 : Blo 1064615 1597283 := bstep (se 1 (by rfl) ⟨1197962, by rfl⟩ : syracuseStep 1597283 = 2395925) B2395925
theorem B1597313 : Blo 1064615 1597313 := bstep (se 2 (by rfl) ⟨598992, by rfl⟩ : syracuseStep 1597313 = 1197985) B1197985
theorem B1597331 : Blo 1064615 1597331 := bstep (se 1 (by rfl) ⟨1197998, by rfl⟩ : syracuseStep 1597331 = 2395997) B2395997
theorem B1597361 : Blo 1064615 1597361 := bstep (se 2 (by rfl) ⟨599010, by rfl⟩ : syracuseStep 1597361 = 1198021) B1198021
theorem B1597379 : Blo 1064615 1597379 := bstep (se 1 (by rfl) ⟨1198034, by rfl⟩ : syracuseStep 1597379 = 2396069) B2396069
theorem B3596237 : Blo 1064615 3596237 := bstep (se 3 (by rfl) ⟨674294, by rfl⟩ : syracuseStep 3596237 = 1348589) B1348589
theorem B1597409 : Blo 1064615 1597409 := bstep (se 2 (by rfl) ⟨599028, by rfl⟩ : syracuseStep 1597409 = 1198057) B1198057
theorem B1597427 : Blo 1064615 1597427 := bstep (se 1 (by rfl) ⟨1198070, by rfl⟩ : syracuseStep 1597427 = 2396141) B2396141
theorem B3596291 : Blo 1064615 3596291 := bstep (se 1 (by rfl) ⟨2697218, by rfl⟩ : syracuseStep 3596291 = 5394437) B5394437
theorem B1597457 : Blo 1064615 1597457 := bstep (se 2 (by rfl) ⟨599046, by rfl⟩ : syracuseStep 1597457 = 1198093) B1198093
theorem B1597475 : Blo 1064615 1597475 := bstep (se 1 (by rfl) ⟨1198106, by rfl⟩ : syracuseStep 1597475 = 2396213) B2396213
theorem B1597505 : Blo 1064615 1597505 := bstep (se 2 (by rfl) ⟨599064, by rfl⟩ : syracuseStep 1597505 = 1198129) B1198129
theorem B1597523 : Blo 1064615 1597523 := bstep (se 1 (by rfl) ⟨1198142, by rfl⟩ : syracuseStep 1597523 = 2396285) B2396285
theorem B1597553 : Blo 1064615 1597553 := bstep (se 2 (by rfl) ⟨599082, by rfl⟩ : syracuseStep 1597553 = 1198165) B1198165
theorem B2023537 : Blo 1064615 2023537 := bstep (se 2 (by rfl) ⟨758826, by rfl⟩ : syracuseStep 2023537 = 1517653) B1517653
theorem B1597571 : Blo 1064615 1597571 := bstep (se 1 (by rfl) ⟨1198178, by rfl⟩ : syracuseStep 1597571 = 2396357) B2396357
theorem B1597601 : Blo 1064615 1597601 := bstep (se 2 (by rfl) ⟨599100, by rfl⟩ : syracuseStep 1597601 = 1198201) B1198201
theorem B1597619 : Blo 1064615 1597619 := bstep (se 1 (by rfl) ⟨1198214, by rfl⟩ : syracuseStep 1597619 = 2396429) B2396429
theorem B1597649 : Blo 1064615 1597649 := bstep (se 2 (by rfl) ⟨599118, by rfl⟩ : syracuseStep 1597649 = 1198237) B1198237
theorem B1597667 : Blo 1064615 1597667 := bstep (se 1 (by rfl) ⟨1198250, by rfl⟩ : syracuseStep 1597667 = 2396501) B2396501
theorem B1597697 : Blo 1064615 1597697 := bstep (se 2 (by rfl) ⟨599136, by rfl⟩ : syracuseStep 1597697 = 1198273) B1198273
theorem B3596561 : Blo 1064615 3596561 := bstep (se 2 (by rfl) ⟨1348710, by rfl⟩ : syracuseStep 3596561 = 2697421) B2697421
theorem B2023697 : Blo 1064615 2023697 := bstep (se 2 (by rfl) ⟨758886, by rfl⟩ : syracuseStep 2023697 = 1517773) B1517773
theorem B1597715 : Blo 1064615 1597715 := bstep (se 1 (by rfl) ⟨1198286, by rfl⟩ : syracuseStep 1597715 = 2396573) B2396573
theorem B1138979 : Blo 1064615 1138979 := bstep (se 1 (by rfl) ⟨854234, by rfl⟩ : syracuseStep 1138979 = 1708469) B1708469
theorem B1597745 : Blo 1064615 1597745 := bstep (se 2 (by rfl) ⟨599154, by rfl⟩ : syracuseStep 1597745 = 1198309) B1198309
theorem B1597763 : Blo 1064615 1597763 := bstep (se 1 (by rfl) ⟨1198322, by rfl⟩ : syracuseStep 1597763 = 2396645) B2396645
theorem B1597793 : Blo 1064615 1597793 := bstep (se 2 (by rfl) ⟨599172, by rfl⟩ : syracuseStep 1597793 = 1198345) B1198345
theorem B18243953 : Blo 1064615 18243953 := bstep (se 2 (by rfl) ⟨6841482, by rfl⟩ : syracuseStep 18243953 = 13682965) B13682965
theorem B1597811 : Blo 1064615 1597811 := bstep (se 1 (by rfl) ⟨1198358, by rfl⟩ : syracuseStep 1597811 = 2396717) B2396717
theorem B1597841 : Blo 1064615 1597841 := bstep (se 2 (by rfl) ⟨599190, by rfl⟩ : syracuseStep 1597841 = 1198381) B1198381
theorem B1597859 : Blo 1064615 1597859 := bstep (se 1 (by rfl) ⟨1198394, by rfl⟩ : syracuseStep 1597859 = 2396789) B2396789
theorem B1597889 : Blo 1064615 1597889 := bstep (se 2 (by rfl) ⟨599208, by rfl⟩ : syracuseStep 1597889 = 1198417) B1198417
theorem B5923277 : Blo 1064615 5923277 := bstep (se 3 (by rfl) ⟨1110614, by rfl⟩ : syracuseStep 5923277 = 2221229) B2221229
theorem B1597907 : Blo 1064615 1597907 := bstep (se 1 (by rfl) ⟨1198430, by rfl⟩ : syracuseStep 1597907 = 2396861) B2396861
theorem B1925603 : Blo 1064615 1925603 := bstep (se 1 (by rfl) ⟨1444202, by rfl⟩ : syracuseStep 1925603 = 2888405) B2888405
theorem B1597937 : Blo 1064615 1597937 := bstep (se 2 (by rfl) ⟨599226, by rfl⟩ : syracuseStep 1597937 = 1198453) B1198453
theorem B1597955 : Blo 1064615 1597955 := bstep (se 1 (by rfl) ⟨1198466, by rfl⟩ : syracuseStep 1597955 = 2396933) B2396933
theorem B6840845 : Blo 1064615 6840845 := bstep (se 3 (by rfl) ⟨1282658, by rfl⟩ : syracuseStep 6840845 = 2565317) B2565317
theorem B1597985 : Blo 1064615 1597985 := bstep (se 2 (by rfl) ⟨599244, by rfl⟩ : syracuseStep 1597985 = 1198489) B1198489
theorem B1598003 : Blo 1064615 1598003 := bstep (se 1 (by rfl) ⟨1198502, by rfl⟩ : syracuseStep 1598003 = 2397005) B2397005
theorem B1598033 : Blo 1064615 1598033 := bstep (se 2 (by rfl) ⟨599262, by rfl⟩ : syracuseStep 1598033 = 1198525) B1198525
theorem B1598051 : Blo 1064615 1598051 := bstep (se 1 (by rfl) ⟨1198538, by rfl⟩ : syracuseStep 1598051 = 2397077) B2397077
theorem B8643185 : Blo 1064615 8643185 := bstep (se 2 (by rfl) ⟨3241194, by rfl⟩ : syracuseStep 8643185 = 6482389) B6482389
theorem B1598081 : Blo 1064615 1598081 := bstep (se 2 (by rfl) ⟨599280, by rfl⟩ : syracuseStep 1598081 = 1198561) B1198561
theorem B1598099 : Blo 1064615 1598099 := bstep (se 1 (by rfl) ⟨1198574, by rfl⟩ : syracuseStep 1598099 = 2397149) B2397149
theorem B2024099 : Blo 1064615 2024099 := bstep (se 1 (by rfl) ⟨1518074, by rfl⟩ : syracuseStep 2024099 = 3036149) B3036149
theorem B1598129 : Blo 1064615 1598129 := bstep (se 2 (by rfl) ⟨599298, by rfl⟩ : syracuseStep 1598129 = 1198597) B1198597
theorem B1598147 : Blo 1064615 1598147 := bstep (se 1 (by rfl) ⟨1198610, by rfl⟩ : syracuseStep 1598147 = 2397221) B2397221
theorem B1598177 : Blo 1064615 1598177 := bstep (se 2 (by rfl) ⟨599316, by rfl⟩ : syracuseStep 1598177 = 1198633) B1198633
theorem B6841073 : Blo 1064615 6841073 := bstep (se 2 (by rfl) ⟨2565402, by rfl⟩ : syracuseStep 6841073 = 5130805) B5130805
theorem B1598195 : Blo 1064615 1598195 := bstep (se 1 (by rfl) ⟨1198646, by rfl⟩ : syracuseStep 1598195 = 2397293) B2397293
theorem B1598225 : Blo 1064615 1598225 := bstep (se 2 (by rfl) ⟨599334, by rfl⟩ : syracuseStep 1598225 = 1198669) B1198669
theorem B1598243 : Blo 1064615 1598243 := bstep (se 1 (by rfl) ⟨1198682, by rfl⟩ : syracuseStep 1598243 = 2397365) B2397365
theorem B3597101 : Blo 1064615 3597101 := bstep (se 3 (by rfl) ⟨674456, by rfl⟩ : syracuseStep 3597101 = 1348913) B1348913
theorem B1598273 : Blo 1064615 1598273 := bstep (se 2 (by rfl) ⟨599352, by rfl⟩ : syracuseStep 1598273 = 1198705) B1198705
theorem B3040067 : Blo 1064615 3040067 := bstep (se 1 (by rfl) ⟨2280050, by rfl⟩ : syracuseStep 3040067 = 4560101) B4560101
theorem B1598291 : Blo 1064615 1598291 := bstep (se 1 (by rfl) ⟨1198718, by rfl⟩ : syracuseStep 1598291 = 2397437) B2397437
theorem B3597155 : Blo 1064615 3597155 := bstep (se 1 (by rfl) ⟨2697866, by rfl⟩ : syracuseStep 3597155 = 5395733) B5395733
theorem B1598321 : Blo 1064615 1598321 := bstep (se 2 (by rfl) ⟨599370, by rfl⟩ : syracuseStep 1598321 = 1198741) B1198741
theorem B1598339 : Blo 1064615 1598339 := bstep (se 1 (by rfl) ⟨1198754, by rfl⟩ : syracuseStep 1598339 = 2397509) B2397509
theorem B1598369 : Blo 1064615 1598369 := bstep (se 2 (by rfl) ⟨599388, by rfl⟩ : syracuseStep 1598369 = 1198777) B1198777
theorem B5399459 : Blo 1064615 5399459 := bstep (se 1 (by rfl) ⟨4049594, by rfl⟩ : syracuseStep 5399459 = 8099189) B8099189
theorem B1598387 : Blo 1064615 1598387 := bstep (se 1 (by rfl) ⟨1198790, by rfl⟩ : syracuseStep 1598387 = 2397581) B2397581
theorem B1598417 : Blo 1064615 1598417 := bstep (se 2 (by rfl) ⟨599406, by rfl⟩ : syracuseStep 1598417 = 1198813) B1198813
theorem B1598435 : Blo 1064615 1598435 := bstep (se 1 (by rfl) ⟨1198826, by rfl⟩ : syracuseStep 1598435 = 2397653) B2397653
theorem B1598465 : Blo 1064615 1598465 := bstep (se 2 (by rfl) ⟨599424, by rfl⟩ : syracuseStep 1598465 = 1198849) B1198849
theorem B1598483 : Blo 1064615 1598483 := bstep (se 1 (by rfl) ⟨1198862, by rfl⟩ : syracuseStep 1598483 = 2397725) B2397725
theorem B1598513 : Blo 1064615 1598513 := bstep (se 2 (by rfl) ⟨599442, by rfl⟩ : syracuseStep 1598513 = 1198885) B1198885
theorem B1598531 : Blo 1064615 1598531 := bstep (se 1 (by rfl) ⟨1198898, by rfl⟩ : syracuseStep 1598531 = 2397797) B2397797
theorem B1598561 : Blo 1064615 1598561 := bstep (se 2 (by rfl) ⟨599460, by rfl⟩ : syracuseStep 1598561 = 1198921) B1198921
theorem B3597425 : Blo 1064615 3597425 := bstep (se 2 (by rfl) ⟨1349034, by rfl⟩ : syracuseStep 3597425 = 2698069) B2698069
theorem B1598579 : Blo 1064615 1598579 := bstep (se 1 (by rfl) ⟨1198934, by rfl⟩ : syracuseStep 1598579 = 2397869) B2397869
theorem B1598609 : Blo 1064615 1598609 := bstep (se 2 (by rfl) ⟨599478, by rfl⟩ : syracuseStep 1598609 = 1198957) B1198957
theorem B1598627 : Blo 1064615 1598627 := bstep (se 1 (by rfl) ⟨1198970, by rfl⟩ : syracuseStep 1598627 = 2397941) B2397941
theorem B1598657 : Blo 1064615 1598657 := bstep (se 2 (by rfl) ⟨599496, by rfl⟩ : syracuseStep 1598657 = 1198993) B1198993
theorem B1598675 : Blo 1064615 1598675 := bstep (se 1 (by rfl) ⟨1199006, by rfl⟩ : syracuseStep 1598675 = 2398013) B2398013
theorem B1139923 : Blo 1064615 1139923 := bstep (se 1 (by rfl) ⟨854942, by rfl⟩ : syracuseStep 1139923 = 1709885) B1709885
theorem B1598705 : Blo 1064615 1598705 := bstep (se 2 (by rfl) ⟨599514, by rfl⟩ : syracuseStep 1598705 = 1199029) B1199029
theorem B1598723 : Blo 1064615 1598723 := bstep (se 1 (by rfl) ⟨1199042, by rfl⟩ : syracuseStep 1598723 = 2398085) B2398085
theorem B1598753 : Blo 1064615 1598753 := bstep (se 2 (by rfl) ⟨599532, by rfl⟩ : syracuseStep 1598753 = 1199065) B1199065
theorem B1598771 : Blo 1064615 1598771 := bstep (se 1 (by rfl) ⟨1199078, by rfl⟩ : syracuseStep 1598771 = 2398157) B2398157
theorem B1598801 : Blo 1064615 1598801 := bstep (se 2 (by rfl) ⟨599550, by rfl⟩ : syracuseStep 1598801 = 1199101) B1199101
theorem B1598819 : Blo 1064615 1598819 := bstep (se 1 (by rfl) ⟨1199114, by rfl⟩ : syracuseStep 1598819 = 2398229) B2398229
theorem B1598849 : Blo 1064615 1598849 := bstep (se 2 (by rfl) ⟨599568, by rfl⟩ : syracuseStep 1598849 = 1199137) B1199137
theorem B1598867 : Blo 1064615 1598867 := bstep (se 1 (by rfl) ⟨1199150, by rfl⟩ : syracuseStep 1598867 = 2398301) B2398301
theorem B1598897 : Blo 1064615 1598897 := bstep (se 2 (by rfl) ⟨599586, by rfl⟩ : syracuseStep 1598897 = 1199173) B1199173
theorem B1598915 : Blo 1064615 1598915 := bstep (se 1 (by rfl) ⟨1199186, by rfl⟩ : syracuseStep 1598915 = 2398373) B2398373
theorem B1598945 : Blo 1064615 1598945 := bstep (se 2 (by rfl) ⟨599604, by rfl⟩ : syracuseStep 1598945 = 1199209) B1199209
theorem B1598963 : Blo 1064615 1598963 := bstep (se 1 (by rfl) ⟨1199222, by rfl⟩ : syracuseStep 1598963 = 2398445) B2398445
theorem B1598993 : Blo 1064615 1598993 := bstep (se 2 (by rfl) ⟨599622, by rfl⟩ : syracuseStep 1598993 = 1199245) B1199245
theorem B1599011 : Blo 1064615 1599011 := bstep (se 1 (by rfl) ⟨1199258, by rfl⟩ : syracuseStep 1599011 = 2398517) B2398517
theorem B2024995 : Blo 1064615 2024995 := bstep (se 1 (by rfl) ⟨1518746, by rfl⟩ : syracuseStep 2024995 = 3037493) B3037493
theorem B20473397 : Blo 1064615 20473397 := bstep (se 5 (by rfl) ⟨959690, by rfl⟩ : syracuseStep 20473397 = 1919381) B1919381
theorem B1599041 : Blo 1064615 1599041 := bstep (se 2 (by rfl) ⟨599640, by rfl⟩ : syracuseStep 1599041 = 1199281) B1199281
theorem B1599059 : Blo 1064615 1599059 := bstep (se 1 (by rfl) ⟨1199294, by rfl⟩ : syracuseStep 1599059 = 2398589) B2398589
theorem B1599089 : Blo 1064615 1599089 := bstep (se 2 (by rfl) ⟨599658, by rfl⟩ : syracuseStep 1599089 = 1199317) B1199317
theorem B1599107 : Blo 1064615 1599107 := bstep (se 1 (by rfl) ⟨1199330, by rfl⟩ : syracuseStep 1599107 = 2398661) B2398661
theorem B3597965 : Blo 1064615 3597965 := bstep (se 3 (by rfl) ⟨674618, by rfl⟩ : syracuseStep 3597965 = 1349237) B1349237
theorem B1599137 : Blo 1064615 1599137 := bstep (se 2 (by rfl) ⟨599676, by rfl⟩ : syracuseStep 1599137 = 1199353) B1199353
theorem B1599155 : Blo 1064615 1599155 := bstep (se 1 (by rfl) ⟨1199366, by rfl⟩ : syracuseStep 1599155 = 2398733) B2398733
theorem B3598019 : Blo 1064615 3598019 := bstep (se 1 (by rfl) ⟨2698514, by rfl⟩ : syracuseStep 3598019 = 5397029) B5397029
theorem B2025155 : Blo 1064615 2025155 := bstep (se 1 (by rfl) ⟨1518866, by rfl⟩ : syracuseStep 2025155 = 3037733) B3037733
theorem B5400269 : Blo 1064615 5400269 := bstep (se 3 (by rfl) ⟨1012550, by rfl⟩ : syracuseStep 5400269 = 2025101) B2025101
theorem B1599185 : Blo 1064615 1599185 := bstep (se 2 (by rfl) ⟨599694, by rfl⟩ : syracuseStep 1599185 = 1199389) B1199389
theorem B1599203 : Blo 1064615 1599203 := bstep (se 1 (by rfl) ⟨1199402, by rfl⟩ : syracuseStep 1599203 = 2398805) B2398805
theorem B1599233 : Blo 1064615 1599233 := bstep (se 2 (by rfl) ⟨599712, by rfl⟩ : syracuseStep 1599233 = 1199425) B1199425
theorem B1599251 : Blo 1064615 1599251 := bstep (se 1 (by rfl) ⟨1199438, by rfl⟩ : syracuseStep 1599251 = 2398877) B2398877
theorem B1599281 : Blo 1064615 1599281 := bstep (se 2 (by rfl) ⟨599730, by rfl⟩ : syracuseStep 1599281 = 1199461) B1199461
theorem B1599299 : Blo 1064615 1599299 := bstep (se 1 (by rfl) ⟨1199474, by rfl⟩ : syracuseStep 1599299 = 2398949) B2398949
theorem B1599329 : Blo 1064615 1599329 := bstep (se 2 (by rfl) ⟨599748, by rfl⟩ : syracuseStep 1599329 = 1199497) B1199497
theorem B1599347 : Blo 1064615 1599347 := bstep (se 1 (by rfl) ⟨1199510, by rfl⟩ : syracuseStep 1599347 = 2399021) B2399021
theorem B1599377 : Blo 1064615 1599377 := bstep (se 2 (by rfl) ⟨599766, by rfl⟩ : syracuseStep 1599377 = 1199533) B1199533
theorem B1599395 : Blo 1064615 1599395 := bstep (se 1 (by rfl) ⟨1199546, by rfl⟩ : syracuseStep 1599395 = 2399093) B2399093
theorem B1599425 : Blo 1064615 1599425 := bstep (se 2 (by rfl) ⟨599784, by rfl⟩ : syracuseStep 1599425 = 1199569) B1199569
theorem B4057037 : Blo 1064615 4057037 := bstep (se 3 (by rfl) ⟨760694, by rfl⟩ : syracuseStep 4057037 = 1521389) B1521389
theorem B3598289 : Blo 1064615 3598289 := bstep (se 2 (by rfl) ⟨1349358, by rfl⟩ : syracuseStep 3598289 = 2698717) B2698717
theorem B1599443 : Blo 1064615 1599443 := bstep (se 1 (by rfl) ⟨1199582, by rfl⟩ : syracuseStep 1599443 = 2399165) B2399165
theorem B1599473 : Blo 1064615 1599473 := bstep (se 2 (by rfl) ⟨599802, by rfl⟩ : syracuseStep 1599473 = 1199605) B1199605
theorem B1599491 : Blo 1064615 1599491 := bstep (se 1 (by rfl) ⟨1199618, by rfl⟩ : syracuseStep 1599491 = 2399237) B2399237
theorem B3041297 : Blo 1064615 3041297 := bstep (se 2 (by rfl) ⟨1140486, by rfl⟩ : syracuseStep 3041297 = 2280973) B2280973
theorem B1599521 : Blo 1064615 1599521 := bstep (se 2 (by rfl) ⟨599820, by rfl⟩ : syracuseStep 1599521 = 1199641) B1199641
theorem B1599539 : Blo 1064615 1599539 := bstep (se 1 (by rfl) ⟨1199654, by rfl⟩ : syracuseStep 1599539 = 2399309) B2399309
theorem B1599569 : Blo 1064615 1599569 := bstep (se 2 (by rfl) ⟨599838, by rfl⟩ : syracuseStep 1599569 = 1199677) B1199677
theorem B1599587 : Blo 1064615 1599587 := bstep (se 1 (by rfl) ⟨1199690, by rfl⟩ : syracuseStep 1599587 = 2399381) B2399381
theorem B1599617 : Blo 1064615 1599617 := bstep (se 2 (by rfl) ⟨599856, by rfl⟩ : syracuseStep 1599617 = 1199713) B1199713
theorem B1599635 : Blo 1064615 1599635 := bstep (se 1 (by rfl) ⟨1199726, by rfl⟩ : syracuseStep 1599635 = 2399453) B2399453
theorem B1599665 : Blo 1064615 1599665 := bstep (se 2 (by rfl) ⟨599874, by rfl⟩ : syracuseStep 1599665 = 1199749) B1199749
theorem B1599683 : Blo 1064615 1599683 := bstep (se 1 (by rfl) ⟨1199762, by rfl⟩ : syracuseStep 1599683 = 2399525) B2399525
theorem B1599713 : Blo 1064615 1599713 := bstep (se 2 (by rfl) ⟨599892, by rfl⟩ : syracuseStep 1599713 = 1199785) B1199785
theorem B1599731 : Blo 1064615 1599731 := bstep (se 1 (by rfl) ⟨1199798, by rfl⟩ : syracuseStep 1599731 = 2399597) B2399597
theorem B1599761 : Blo 1064615 1599761 := bstep (se 2 (by rfl) ⟨599910, by rfl⟩ : syracuseStep 1599761 = 1199821) B1199821
theorem B1599779 : Blo 1064615 1599779 := bstep (se 1 (by rfl) ⟨1199834, by rfl⟩ : syracuseStep 1599779 = 2399669) B2399669
theorem B1599809 : Blo 1064615 1599809 := bstep (se 2 (by rfl) ⟨599928, by rfl⟩ : syracuseStep 1599809 = 1199857) B1199857
theorem B1599827 : Blo 1064615 1599827 := bstep (se 1 (by rfl) ⟨1199870, by rfl⟩ : syracuseStep 1599827 = 2399741) B2399741
theorem B1599857 : Blo 1064615 1599857 := bstep (se 2 (by rfl) ⟨599946, by rfl⟩ : syracuseStep 1599857 = 1199893) B1199893
theorem B1599875 : Blo 1064615 1599875 := bstep (se 1 (by rfl) ⟨1199906, by rfl⟩ : syracuseStep 1599875 = 2399813) B2399813
theorem B1599905 : Blo 1064615 1599905 := bstep (se 2 (by rfl) ⟨599964, by rfl⟩ : syracuseStep 1599905 = 1199929) B1199929
theorem B1599923 : Blo 1064615 1599923 := bstep (se 1 (by rfl) ⟨1199942, by rfl⟩ : syracuseStep 1599923 = 2399885) B2399885
theorem B2877905 : Blo 1064615 2877905 := bstep (se 2 (by rfl) ⟨1079214, by rfl⟩ : syracuseStep 2877905 = 2158429) B2158429
theorem B1599953 : Blo 1064615 1599953 := bstep (se 2 (by rfl) ⟨599982, by rfl⟩ : syracuseStep 1599953 = 1199965) B1199965
theorem B1599971 : Blo 1064615 1599971 := bstep (se 1 (by rfl) ⟨1199978, by rfl⟩ : syracuseStep 1599971 = 2399957) B2399957
theorem B3598829 : Blo 1064615 3598829 := bstep (se 3 (by rfl) ⟨674780, by rfl⟩ : syracuseStep 3598829 = 1349561) B1349561
theorem B1796593 : Blo 1064615 1796593 := bstep (se 2 (by rfl) ⟨673722, by rfl⟩ : syracuseStep 1796593 = 1347445) B1347445
theorem B1600001 : Blo 1064615 1600001 := bstep (se 2 (by rfl) ⟨600000, by rfl⟩ : syracuseStep 1600001 = 1200001) B1200001
theorem B1796627 : Blo 1064615 1796627 := bstep (se 1 (by rfl) ⟨1347470, by rfl⟩ : syracuseStep 1796627 = 2694941) B2694941
theorem B1600019 : Blo 1064615 1600019 := bstep (se 1 (by rfl) ⟨1200014, by rfl⟩ : syracuseStep 1600019 = 2400029) B2400029
theorem B3598883 : Blo 1064615 3598883 := bstep (se 1 (by rfl) ⟨2699162, by rfl⟩ : syracuseStep 3598883 = 5398325) B5398325
theorem B1600049 : Blo 1064615 1600049 := bstep (se 2 (by rfl) ⟨600018, by rfl⟩ : syracuseStep 1600049 = 1200037) B1200037
theorem B1600067 : Blo 1064615 1600067 := bstep (se 1 (by rfl) ⟨1200050, by rfl⟩ : syracuseStep 1600067 = 2400101) B2400101
theorem B1600097 : Blo 1064615 1600097 := bstep (se 2 (by rfl) ⟨600036, by rfl⟩ : syracuseStep 1600097 = 1200073) B1200073
theorem B1600115 : Blo 1064615 1600115 := bstep (se 1 (by rfl) ⟨1200086, by rfl⟩ : syracuseStep 1600115 = 2400173) B2400173
theorem B1600145 : Blo 1064615 1600145 := bstep (se 2 (by rfl) ⟨600054, by rfl⟩ : syracuseStep 1600145 = 1200109) B1200109
theorem B1796755 : Blo 1064615 1796755 := bstep (se 1 (by rfl) ⟨1347566, by rfl⟩ : syracuseStep 1796755 = 2695133) B2695133
theorem B1600163 : Blo 1064615 1600163 := bstep (se 1 (by rfl) ⟨1200122, by rfl⟩ : syracuseStep 1600163 = 2400245) B2400245
theorem B1600193 : Blo 1064615 1600193 := bstep (se 2 (by rfl) ⟨600072, by rfl⟩ : syracuseStep 1600193 = 1200145) B1200145
theorem B1600211 : Blo 1064615 1600211 := bstep (se 1 (by rfl) ⟨1200158, by rfl⟩ : syracuseStep 1600211 = 2400317) B2400317
theorem B1600241 : Blo 1064615 1600241 := bstep (se 2 (by rfl) ⟨600090, by rfl⟩ : syracuseStep 1600241 = 1200181) B1200181
theorem B2026225 : Blo 1064615 2026225 := bstep (se 2 (by rfl) ⟨759834, by rfl⟩ : syracuseStep 2026225 = 1519669) B1519669
theorem B1600259 : Blo 1064615 1600259 := bstep (se 1 (by rfl) ⟨1200194, by rfl⟩ : syracuseStep 1600259 = 2400389) B2400389
theorem B1796897 : Blo 1064615 1796897 := bstep (se 2 (by rfl) ⟨673836, by rfl⟩ : syracuseStep 1796897 = 1347673) B1347673
theorem B1600289 : Blo 1064615 1600289 := bstep (se 2 (by rfl) ⟨600108, by rfl⟩ : syracuseStep 1600289 = 1200217) B1200217
theorem B3599153 : Blo 1064615 3599153 := bstep (se 2 (by rfl) ⟨1349682, by rfl⟩ : syracuseStep 3599153 = 2699365) B2699365
theorem B1600307 : Blo 1064615 1600307 := bstep (se 1 (by rfl) ⟨1200230, by rfl⟩ : syracuseStep 1600307 = 2400461) B2400461
theorem B1600337 : Blo 1064615 1600337 := bstep (se 2 (by rfl) ⟨600126, by rfl⟩ : syracuseStep 1600337 = 1200253) B1200253
theorem B1600355 : Blo 1064615 1600355 := bstep (se 1 (by rfl) ⟨1200266, by rfl⟩ : syracuseStep 1600355 = 2400533) B2400533
theorem B1600385 : Blo 1064615 1600385 := bstep (se 2 (by rfl) ⟨600144, by rfl⟩ : syracuseStep 1600385 = 1200289) B1200289
theorem B1731473 : Blo 1064615 1731473 := bstep (se 2 (by rfl) ⟨649302, by rfl⟩ : syracuseStep 1731473 = 1298605) B1298605
theorem B1600403 : Blo 1064615 1600403 := bstep (se 1 (by rfl) ⟨1200302, by rfl⟩ : syracuseStep 1600403 = 2400605) B2400605
theorem B1797025 : Blo 1064615 1797025 := bstep (se 2 (by rfl) ⟨673884, by rfl⟩ : syracuseStep 1797025 = 1347769) B1347769
theorem B1600433 : Blo 1064615 1600433 := bstep (se 2 (by rfl) ⟨600162, by rfl⟩ : syracuseStep 1600433 = 1200325) B1200325
theorem B1797059 : Blo 1064615 1797059 := bstep (se 1 (by rfl) ⟨1347794, by rfl⟩ : syracuseStep 1797059 = 2695589) B2695589
theorem B1600451 : Blo 1064615 1600451 := bstep (se 1 (by rfl) ⟨1200338, by rfl⟩ : syracuseStep 1600451 = 2400677) B2400677
theorem B1600481 : Blo 1064615 1600481 := bstep (se 2 (by rfl) ⟨600180, by rfl⟩ : syracuseStep 1600481 = 1200361) B1200361
theorem B1600499 : Blo 1064615 1600499 := bstep (se 1 (by rfl) ⟨1200374, by rfl⟩ : syracuseStep 1600499 = 2400749) B2400749
theorem B1600529 : Blo 1064615 1600529 := bstep (se 2 (by rfl) ⟨600198, by rfl⟩ : syracuseStep 1600529 = 1200397) B1200397
theorem B1600547 : Blo 1064615 1600547 := bstep (se 1 (by rfl) ⟨1200410, by rfl⟩ : syracuseStep 1600547 = 2400821) B2400821
theorem B1600577 : Blo 1064615 1600577 := bstep (se 2 (by rfl) ⟨600216, by rfl⟩ : syracuseStep 1600577 = 1200433) B1200433
theorem B1797187 : Blo 1064615 1797187 := bstep (se 1 (by rfl) ⟨1347890, by rfl⟩ : syracuseStep 1797187 = 2695781) B2695781
theorem B1600595 : Blo 1064615 1600595 := bstep (se 1 (by rfl) ⟨1200446, by rfl⟩ : syracuseStep 1600595 = 2400893) B2400893
theorem B1600625 : Blo 1064615 1600625 := bstep (se 2 (by rfl) ⟨600234, by rfl⟩ : syracuseStep 1600625 = 1200469) B1200469
theorem B1600643 : Blo 1064615 1600643 := bstep (se 1 (by rfl) ⟨1200482, by rfl⟩ : syracuseStep 1600643 = 2400965) B2400965
theorem B1600673 : Blo 1064615 1600673 := bstep (se 2 (by rfl) ⟨600252, by rfl⟩ : syracuseStep 1600673 = 1200505) B1200505
theorem B1600691 : Blo 1064615 1600691 := bstep (se 1 (by rfl) ⟨1200518, by rfl⟩ : syracuseStep 1600691 = 2401037) B2401037
theorem B10251461 : Blo 1064615 10251461 := bstep (se 4 (by rfl) ⟨961074, by rfl⟩ : syracuseStep 10251461 = 1922149) B1922149
theorem B1797329 : Blo 1064615 1797329 := bstep (se 2 (by rfl) ⟨673998, by rfl⟩ : syracuseStep 1797329 = 1347997) B1347997
theorem B1600721 : Blo 1064615 1600721 := bstep (se 2 (by rfl) ⟨600270, by rfl⟩ : syracuseStep 1600721 = 1200541) B1200541
theorem B1600739 : Blo 1064615 1600739 := bstep (se 1 (by rfl) ⟨1200554, by rfl⟩ : syracuseStep 1600739 = 2401109) B2401109
theorem B3239153 : Blo 1064615 3239153 := bstep (se 2 (by rfl) ⟨1214682, by rfl⟩ : syracuseStep 3239153 = 2429365) B2429365
theorem B1600769 : Blo 1064615 1600769 := bstep (se 2 (by rfl) ⟨600288, by rfl⟩ : syracuseStep 1600769 = 1200577) B1200577
theorem B1600787 : Blo 1064615 1600787 := bstep (se 1 (by rfl) ⟨1200590, by rfl⟩ : syracuseStep 1600787 = 2401181) B2401181
theorem B1600817 : Blo 1064615 1600817 := bstep (se 2 (by rfl) ⟨600306, by rfl⟩ : syracuseStep 1600817 = 1200613) B1200613
theorem B1600835 : Blo 1064615 1600835 := bstep (se 1 (by rfl) ⟨1200626, by rfl⟩ : syracuseStep 1600835 = 2401253) B2401253
theorem B3599693 : Blo 1064615 3599693 := bstep (se 3 (by rfl) ⟨674942, by rfl⟩ : syracuseStep 3599693 = 1349885) B1349885
theorem B1797457 : Blo 1064615 1797457 := bstep (se 2 (by rfl) ⟨674046, by rfl⟩ : syracuseStep 1797457 = 1348093) B1348093
theorem B1600865 : Blo 1064615 1600865 := bstep (se 2 (by rfl) ⟨600324, by rfl⟩ : syracuseStep 1600865 = 1200649) B1200649
theorem B1797491 : Blo 1064615 1797491 := bstep (se 1 (by rfl) ⟨1348118, by rfl⟩ : syracuseStep 1797491 = 2696237) B2696237
theorem B1600883 : Blo 1064615 1600883 := bstep (se 1 (by rfl) ⟨1200662, by rfl⟩ : syracuseStep 1600883 = 2401325) B2401325
theorem B3599747 : Blo 1064615 3599747 := bstep (se 1 (by rfl) ⟨2699810, by rfl⟩ : syracuseStep 3599747 = 5399621) B5399621
theorem B1600913 : Blo 1064615 1600913 := bstep (se 2 (by rfl) ⟨600342, by rfl⟩ : syracuseStep 1600913 = 1200685) B1200685
theorem B1600931 : Blo 1064615 1600931 := bstep (se 1 (by rfl) ⟨1200698, by rfl⟩ : syracuseStep 1600931 = 2401397) B2401397
theorem B1600961 : Blo 1064615 1600961 := bstep (se 2 (by rfl) ⟨600360, by rfl⟩ : syracuseStep 1600961 = 1200721) B1200721
theorem B3042755 : Blo 1064615 3042755 := bstep (se 1 (by rfl) ⟨2282066, by rfl⟩ : syracuseStep 3042755 = 4564133) B4564133
theorem B1600979 : Blo 1064615 1600979 := bstep (se 1 (by rfl) ⟨1200734, by rfl⟩ : syracuseStep 1600979 = 2401469) B2401469
theorem B1601009 : Blo 1064615 1601009 := bstep (se 2 (by rfl) ⟨600378, by rfl⟩ : syracuseStep 1601009 = 1200757) B1200757
theorem B1797619 : Blo 1064615 1797619 := bstep (se 1 (by rfl) ⟨1348214, by rfl⟩ : syracuseStep 1797619 = 2696429) B2696429
theorem B1601027 : Blo 1064615 1601027 := bstep (se 1 (by rfl) ⟨1200770, by rfl⟩ : syracuseStep 1601027 = 2401541) B2401541
theorem B1601057 : Blo 1064615 1601057 := bstep (se 2 (by rfl) ⟨600396, by rfl⟩ : syracuseStep 1601057 = 1200793) B1200793
theorem B1601075 : Blo 1064615 1601075 := bstep (se 1 (by rfl) ⟨1200806, by rfl⟩ : syracuseStep 1601075 = 2401613) B2401613
theorem B1601105 : Blo 1064615 1601105 := bstep (se 2 (by rfl) ⟨600414, by rfl⟩ : syracuseStep 1601105 = 1200829) B1200829
theorem B1601123 : Blo 1064615 1601123 := bstep (se 1 (by rfl) ⟨1200842, by rfl⟩ : syracuseStep 1601123 = 2401685) B2401685
theorem B1797761 : Blo 1064615 1797761 := bstep (se 2 (by rfl) ⟨674160, by rfl⟩ : syracuseStep 1797761 = 1348321) B1348321
theorem B1601153 : Blo 1064615 1601153 := bstep (se 2 (by rfl) ⟨600432, by rfl⟩ : syracuseStep 1601153 = 1200865) B1200865
theorem B3600017 : Blo 1064615 3600017 := bstep (se 2 (by rfl) ⟨1350006, by rfl⟩ : syracuseStep 3600017 = 2700013) B2700013
theorem B1601171 : Blo 1064615 1601171 := bstep (se 1 (by rfl) ⟨1200878, by rfl⟩ : syracuseStep 1601171 = 2401757) B2401757
theorem B1601201 : Blo 1064615 1601201 := bstep (se 2 (by rfl) ⟨600450, by rfl⟩ : syracuseStep 1601201 = 1200901) B1200901
theorem B1601219 : Blo 1064615 1601219 := bstep (se 1 (by rfl) ⟨1200914, by rfl⟩ : syracuseStep 1601219 = 2401829) B2401829
theorem B1601249 : Blo 1064615 1601249 := bstep (se 2 (by rfl) ⟨600468, by rfl⟩ : syracuseStep 1601249 = 1200937) B1200937
theorem B1601267 : Blo 1064615 1601267 := bstep (se 1 (by rfl) ⟨1200950, by rfl⟩ : syracuseStep 1601267 = 2401901) B2401901
theorem B1797889 : Blo 1064615 1797889 := bstep (se 2 (by rfl) ⟨674208, by rfl⟩ : syracuseStep 1797889 = 1348417) B1348417
theorem B1601297 : Blo 1064615 1601297 := bstep (se 2 (by rfl) ⟨600486, by rfl⟩ : syracuseStep 1601297 = 1200973) B1200973
theorem B2027281 : Blo 1064615 2027281 := bstep (se 2 (by rfl) ⟨760230, by rfl⟩ : syracuseStep 2027281 = 1520461) B1520461
theorem B1797923 : Blo 1064615 1797923 := bstep (se 1 (by rfl) ⟨1348442, by rfl⟩ : syracuseStep 1797923 = 2696885) B2696885
theorem B1601315 : Blo 1064615 1601315 := bstep (se 1 (by rfl) ⟨1200986, by rfl⟩ : syracuseStep 1601315 = 2401973) B2401973
theorem B4321073 : Blo 1064615 4321073 := bstep (se 2 (by rfl) ⟨1620402, by rfl⟩ : syracuseStep 4321073 = 3240805) B3240805
theorem B1601345 : Blo 1064615 1601345 := bstep (se 2 (by rfl) ⟨600504, by rfl⟩ : syracuseStep 1601345 = 1201009) B1201009
theorem B1601363 : Blo 1064615 1601363 := bstep (se 1 (by rfl) ⟨1201022, by rfl⟩ : syracuseStep 1601363 = 2402045) B2402045
theorem B1601393 : Blo 1064615 1601393 := bstep (se 2 (by rfl) ⟨600522, by rfl⟩ : syracuseStep 1601393 = 1201045) B1201045
theorem B1601411 : Blo 1064615 1601411 := bstep (se 1 (by rfl) ⟨1201058, by rfl⟩ : syracuseStep 1601411 = 2402117) B2402117
theorem B1601441 : Blo 1064615 1601441 := bstep (se 2 (by rfl) ⟨600540, by rfl⟩ : syracuseStep 1601441 = 1201081) B1201081
theorem B1798051 : Blo 1064615 1798051 := bstep (se 1 (by rfl) ⟨1348538, by rfl⟩ : syracuseStep 1798051 = 2697077) B2697077
theorem B1601459 : Blo 1064615 1601459 := bstep (se 1 (by rfl) ⟨1201094, by rfl⟩ : syracuseStep 1601459 = 2402189) B2402189
theorem B1601489 : Blo 1064615 1601489 := bstep (se 2 (by rfl) ⟨600558, by rfl⟩ : syracuseStep 1601489 = 1201117) B1201117
theorem B1601507 : Blo 1064615 1601507 := bstep (se 1 (by rfl) ⟨1201130, by rfl⟩ : syracuseStep 1601507 = 2402261) B2402261
theorem B1601537 : Blo 1064615 1601537 := bstep (se 2 (by rfl) ⟨600576, by rfl⟩ : syracuseStep 1601537 = 1201153) B1201153
theorem B1601555 : Blo 1064615 1601555 := bstep (se 1 (by rfl) ⟨1201166, by rfl⟩ : syracuseStep 1601555 = 2402333) B2402333
theorem B1798193 : Blo 1064615 1798193 := bstep (se 2 (by rfl) ⟨674322, by rfl⟩ : syracuseStep 1798193 = 1348645) B1348645
theorem B1601585 : Blo 1064615 1601585 := bstep (se 2 (by rfl) ⟨600594, by rfl⟩ : syracuseStep 1601585 = 1201189) B1201189
theorem B1601603 : Blo 1064615 1601603 := bstep (se 1 (by rfl) ⟨1201202, by rfl⟩ : syracuseStep 1601603 = 2402405) B2402405
theorem B1601633 : Blo 1064615 1601633 := bstep (se 2 (by rfl) ⟨600612, by rfl⟩ : syracuseStep 1601633 = 1201225) B1201225
theorem B1601651 : Blo 1064615 1601651 := bstep (se 1 (by rfl) ⟨1201238, by rfl⟩ : syracuseStep 1601651 = 2402477) B2402477
theorem B1601681 : Blo 1064615 1601681 := bstep (se 2 (by rfl) ⟨600630, by rfl⟩ : syracuseStep 1601681 = 1201261) B1201261
theorem B1601699 : Blo 1064615 1601699 := bstep (se 1 (by rfl) ⟨1201274, by rfl⟩ : syracuseStep 1601699 = 2402549) B2402549
theorem B2027683 : Blo 1064615 2027683 := bstep (se 1 (by rfl) ⟨1520762, by rfl⟩ : syracuseStep 2027683 = 3041525) B3041525
theorem B3600557 : Blo 1064615 3600557 := bstep (se 3 (by rfl) ⟨675104, by rfl⟩ : syracuseStep 3600557 = 1350209) B1350209
theorem B1798321 : Blo 1064615 1798321 := bstep (se 2 (by rfl) ⟨674370, by rfl⟩ : syracuseStep 1798321 = 1348741) B1348741
theorem B1601729 : Blo 1064615 1601729 := bstep (se 2 (by rfl) ⟨600648, by rfl⟩ : syracuseStep 1601729 = 1201297) B1201297
theorem B2027729 : Blo 1064615 2027729 := bstep (se 2 (by rfl) ⟨760398, by rfl⟩ : syracuseStep 2027729 = 1520797) B1520797
theorem B1798355 : Blo 1064615 1798355 := bstep (se 1 (by rfl) ⟨1348766, by rfl⟩ : syracuseStep 1798355 = 2697533) B2697533
theorem B1601747 : Blo 1064615 1601747 := bstep (se 1 (by rfl) ⟨1201310, by rfl⟩ : syracuseStep 1601747 = 2402621) B2402621
theorem B3600611 : Blo 1064615 3600611 := bstep (se 1 (by rfl) ⟨2700458, by rfl⟩ : syracuseStep 3600611 = 5400917) B5400917
theorem B6156529 : Blo 1064615 6156529 := bstep (se 2 (by rfl) ⟨2308698, by rfl⟩ : syracuseStep 6156529 = 4617397) B4617397
theorem B1601777 : Blo 1064615 1601777 := bstep (se 2 (by rfl) ⟨600666, by rfl⟩ : syracuseStep 1601777 = 1201333) B1201333
theorem B1601795 : Blo 1064615 1601795 := bstep (se 1 (by rfl) ⟨1201346, by rfl⟩ : syracuseStep 1601795 = 2402693) B2402693
theorem B1601825 : Blo 1064615 1601825 := bstep (se 2 (by rfl) ⟨600684, by rfl⟩ : syracuseStep 1601825 = 1201369) B1201369
theorem B1601843 : Blo 1064615 1601843 := bstep (se 1 (by rfl) ⟨1201382, by rfl⟩ : syracuseStep 1601843 = 2402765) B2402765
theorem B1601873 : Blo 1064615 1601873 := bstep (se 2 (by rfl) ⟨600702, by rfl⟩ : syracuseStep 1601873 = 1201405) B1201405
theorem B1798483 : Blo 1064615 1798483 := bstep (se 1 (by rfl) ⟨1348862, by rfl⟩ : syracuseStep 1798483 = 2697725) B2697725
theorem B8089955 : Blo 1064615 8089955 := bstep (se 1 (by rfl) ⟨6067466, by rfl⟩ : syracuseStep 8089955 = 12134933) B12134933
theorem B4551011 : Blo 1064615 4551011 := bstep (se 1 (by rfl) ⟨3413258, by rfl⟩ : syracuseStep 4551011 = 6826517) B6826517
theorem B1601891 : Blo 1064615 1601891 := bstep (se 1 (by rfl) ⟨1201418, by rfl⟩ : syracuseStep 1601891 = 2402837) B2402837
theorem B1601921 : Blo 1064615 1601921 := bstep (se 2 (by rfl) ⟨600720, by rfl⟩ : syracuseStep 1601921 = 1201441) B1201441
theorem B1601939 : Blo 1064615 1601939 := bstep (se 1 (by rfl) ⟨1201454, by rfl⟩ : syracuseStep 1601939 = 2402909) B2402909
theorem B1601969 : Blo 1064615 1601969 := bstep (se 2 (by rfl) ⟨600738, by rfl⟩ : syracuseStep 1601969 = 1201477) B1201477
theorem B1601987 : Blo 1064615 1601987 := bstep (se 1 (by rfl) ⟨1201490, by rfl⟩ : syracuseStep 1601987 = 2402981) B2402981
theorem B23097797 : Blo 1064615 23097797 := bstep (se 4 (by rfl) ⟨2165418, by rfl⟩ : syracuseStep 23097797 = 4330837) B4330837
theorem B1798625 : Blo 1064615 1798625 := bstep (se 2 (by rfl) ⟨674484, by rfl⟩ : syracuseStep 1798625 = 1348969) B1348969
theorem B1602017 : Blo 1064615 1602017 := bstep (se 2 (by rfl) ⟨600756, by rfl⟩ : syracuseStep 1602017 = 1201513) B1201513
theorem B3600881 : Blo 1064615 3600881 := bstep (se 2 (by rfl) ⟨1350330, by rfl⟩ : syracuseStep 3600881 = 2700661) B2700661
theorem B2028017 : Blo 1064615 2028017 := bstep (se 2 (by rfl) ⟨760506, by rfl⟩ : syracuseStep 2028017 = 1521013) B1521013
theorem B1602035 : Blo 1064615 1602035 := bstep (se 1 (by rfl) ⟨1201526, by rfl⟩ : syracuseStep 1602035 = 2403053) B2403053
theorem B1602065 : Blo 1064615 1602065 := bstep (se 2 (by rfl) ⟨600774, by rfl⟩ : syracuseStep 1602065 = 1201549) B1201549
theorem B1602083 : Blo 1064615 1602083 := bstep (se 1 (by rfl) ⟨1201562, by rfl⟩ : syracuseStep 1602083 = 2403125) B2403125
theorem B5403185 : Blo 1064615 5403185 := bstep (se 2 (by rfl) ⟨2026194, by rfl⟩ : syracuseStep 5403185 = 4052389) B4052389
theorem B1602113 : Blo 1064615 1602113 := bstep (se 2 (by rfl) ⟨600792, by rfl⟩ : syracuseStep 1602113 = 1201585) B1201585
theorem B1602131 : Blo 1064615 1602131 := bstep (se 1 (by rfl) ⟨1201598, by rfl⟩ : syracuseStep 1602131 = 2403197) B2403197
theorem B1798753 : Blo 1064615 1798753 := bstep (se 2 (by rfl) ⟨674532, by rfl⟩ : syracuseStep 1798753 = 1349065) B1349065
theorem B1602161 : Blo 1064615 1602161 := bstep (se 2 (by rfl) ⟨600810, by rfl⟩ : syracuseStep 1602161 = 1201621) B1201621
theorem B1798787 : Blo 1064615 1798787 := bstep (se 1 (by rfl) ⟨1349090, by rfl⟩ : syracuseStep 1798787 = 2698181) B2698181
theorem B1602179 : Blo 1064615 1602179 := bstep (se 1 (by rfl) ⟨1201634, by rfl⟩ : syracuseStep 1602179 = 2403269) B2403269
theorem B1602209 : Blo 1064615 1602209 := bstep (se 2 (by rfl) ⟨600828, by rfl⟩ : syracuseStep 1602209 = 1201657) B1201657
theorem B1602227 : Blo 1064615 1602227 := bstep (se 1 (by rfl) ⟨1201670, by rfl⟩ : syracuseStep 1602227 = 2403341) B2403341
theorem B1602257 : Blo 1064615 1602257 := bstep (se 2 (by rfl) ⟨600846, by rfl⟩ : syracuseStep 1602257 = 1201693) B1201693
theorem B1602275 : Blo 1064615 1602275 := bstep (se 1 (by rfl) ⟨1201706, by rfl⟩ : syracuseStep 1602275 = 2403413) B2403413
theorem B1602305 : Blo 1064615 1602305 := bstep (se 2 (by rfl) ⟨600864, by rfl⟩ : syracuseStep 1602305 = 1201729) B1201729
theorem B1798915 : Blo 1064615 1798915 := bstep (se 1 (by rfl) ⟨1349186, by rfl⟩ : syracuseStep 1798915 = 2698373) B2698373
theorem B1602323 : Blo 1064615 1602323 := bstep (se 1 (by rfl) ⟨1201742, by rfl⟩ : syracuseStep 1602323 = 2403485) B2403485
theorem B1602353 : Blo 1064615 1602353 := bstep (se 2 (by rfl) ⟨600882, by rfl⟩ : syracuseStep 1602353 = 1201765) B1201765
theorem B1602371 : Blo 1064615 1602371 := bstep (se 1 (by rfl) ⟨1201778, by rfl⟩ : syracuseStep 1602371 = 2403557) B2403557
theorem B1602401 : Blo 1064615 1602401 := bstep (se 2 (by rfl) ⟨600900, by rfl⟩ : syracuseStep 1602401 = 1201801) B1201801
theorem B1602419 : Blo 1064615 1602419 := bstep (se 1 (by rfl) ⟨1201814, by rfl⟩ : syracuseStep 1602419 = 2403629) B2403629
theorem B1799057 : Blo 1064615 1799057 := bstep (se 2 (by rfl) ⟨674646, by rfl⟩ : syracuseStep 1799057 = 1349293) B1349293
theorem B1602449 : Blo 1064615 1602449 := bstep (se 2 (by rfl) ⟨600918, by rfl⟩ : syracuseStep 1602449 = 1201837) B1201837
theorem B1602467 : Blo 1064615 1602467 := bstep (se 1 (by rfl) ⟨1201850, by rfl⟩ : syracuseStep 1602467 = 2403701) B2403701
theorem B1602497 : Blo 1064615 1602497 := bstep (se 2 (by rfl) ⟨600936, by rfl⟩ : syracuseStep 1602497 = 1201873) B1201873
theorem B1602515 : Blo 1064615 1602515 := bstep (se 1 (by rfl) ⟨1201886, by rfl⟩ : syracuseStep 1602515 = 2403773) B2403773
theorem B1602545 : Blo 1064615 1602545 := bstep (se 2 (by rfl) ⟨600954, by rfl⟩ : syracuseStep 1602545 = 1201909) B1201909
theorem B1602563 : Blo 1064615 1602563 := bstep (se 1 (by rfl) ⟨1201922, by rfl⟩ : syracuseStep 1602563 = 2403845) B2403845
theorem B3601421 : Blo 1064615 3601421 := bstep (se 3 (by rfl) ⟨675266, by rfl⟩ : syracuseStep 3601421 = 1350533) B1350533
theorem B1799185 : Blo 1064615 1799185 := bstep (se 2 (by rfl) ⟨674694, by rfl⟩ : syracuseStep 1799185 = 1349389) B1349389
theorem B1602593 : Blo 1064615 1602593 := bstep (se 2 (by rfl) ⟨600972, by rfl⟩ : syracuseStep 1602593 = 1201945) B1201945
theorem B1799219 : Blo 1064615 1799219 := bstep (se 1 (by rfl) ⟨1349414, by rfl⟩ : syracuseStep 1799219 = 2698829) B2698829
theorem B1602611 : Blo 1064615 1602611 := bstep (se 1 (by rfl) ⟨1201958, by rfl⟩ : syracuseStep 1602611 = 2403917) B2403917
theorem B3601475 : Blo 1064615 3601475 := bstep (se 1 (by rfl) ⟨2701106, by rfl⟩ : syracuseStep 3601475 = 5402213) B5402213
theorem B1602641 : Blo 1064615 1602641 := bstep (se 2 (by rfl) ⟨600990, by rfl⟩ : syracuseStep 1602641 = 1201981) B1201981
theorem B1602659 : Blo 1064615 1602659 := bstep (se 1 (by rfl) ⟨1201994, by rfl⟩ : syracuseStep 1602659 = 2403989) B2403989
theorem B1602689 : Blo 1064615 1602689 := bstep (se 2 (by rfl) ⟨601008, by rfl⟩ : syracuseStep 1602689 = 1202017) B1202017
theorem B1602707 : Blo 1064615 1602707 := bstep (se 1 (by rfl) ⟨1202030, by rfl⟩ : syracuseStep 1602707 = 2404061) B2404061
theorem B1602737 : Blo 1064615 1602737 := bstep (se 2 (by rfl) ⟨601026, by rfl⟩ : syracuseStep 1602737 = 1202053) B1202053
theorem B1799347 : Blo 1064615 1799347 := bstep (se 1 (by rfl) ⟨1349510, by rfl⟩ : syracuseStep 1799347 = 2699021) B2699021
theorem B1602755 : Blo 1064615 1602755 := bstep (se 1 (by rfl) ⟨1202066, by rfl⟩ : syracuseStep 1602755 = 2404133) B2404133
theorem B1602785 : Blo 1064615 1602785 := bstep (se 2 (by rfl) ⟨601044, by rfl⟩ : syracuseStep 1602785 = 1202089) B1202089
theorem B1602803 : Blo 1064615 1602803 := bstep (se 1 (by rfl) ⟨1202102, by rfl⟩ : syracuseStep 1602803 = 2404205) B2404205
theorem B1602833 : Blo 1064615 1602833 := bstep (se 2 (by rfl) ⟨601062, by rfl⟩ : syracuseStep 1602833 = 1202125) B1202125
theorem B1602851 : Blo 1064615 1602851 := bstep (se 1 (by rfl) ⟨1202138, by rfl⟩ : syracuseStep 1602851 = 2404277) B2404277
theorem B1799489 : Blo 1064615 1799489 := bstep (se 2 (by rfl) ⟨674808, by rfl⟩ : syracuseStep 1799489 = 1349617) B1349617
theorem B1602881 : Blo 1064615 1602881 := bstep (se 2 (by rfl) ⟨601080, by rfl⟩ : syracuseStep 1602881 = 1202161) B1202161
theorem B3601745 : Blo 1064615 3601745 := bstep (se 2 (by rfl) ⟨1350654, by rfl⟩ : syracuseStep 3601745 = 2701309) B2701309
theorem B1602899 : Blo 1064615 1602899 := bstep (se 1 (by rfl) ⟨1202174, by rfl⟩ : syracuseStep 1602899 = 2404349) B2404349
theorem B1799617 : Blo 1064615 1799617 := bstep (se 2 (by rfl) ⟨674856, by rfl⟩ : syracuseStep 1799617 = 1349713) B1349713
theorem B1734097 : Blo 1064615 1734097 := bstep (se 2 (by rfl) ⟨650286, by rfl⟩ : syracuseStep 1734097 = 1300573) B1300573
theorem B1799651 : Blo 1064615 1799651 := bstep (se 1 (by rfl) ⟨1349738, by rfl⟩ : syracuseStep 1799651 = 2699477) B2699477
theorem B1439299 : Blo 1064615 1439299 := bstep (se 1 (by rfl) ⟨1079474, by rfl⟩ : syracuseStep 1439299 = 2158949) B2158949
theorem B1799779 : Blo 1064615 1799779 := bstep (se 1 (by rfl) ⟨1349834, by rfl⟩ : syracuseStep 1799779 = 2699669) B2699669
theorem B10385093 : Blo 1064615 10385093 := bstep (se 4 (by rfl) ⟨973602, by rfl⟩ : syracuseStep 10385093 = 1947205) B1947205
theorem B1799921 : Blo 1064615 1799921 := bstep (se 2 (by rfl) ⟨674970, by rfl⟩ : syracuseStep 1799921 = 1349941) B1349941
theorem B2193137 : Blo 1064615 2193137 := bstep (se 2 (by rfl) ⟨822426, by rfl⟩ : syracuseStep 2193137 = 1644853) B1644853
theorem B4323149 : Blo 1064615 4323149 := bstep (se 3 (by rfl) ⟨810590, by rfl⟩ : syracuseStep 4323149 = 1621181) B1621181
theorem B3602285 : Blo 1064615 3602285 := bstep (se 3 (by rfl) ⟨675428, by rfl⟩ : syracuseStep 3602285 = 1350857) B1350857
theorem B1800049 : Blo 1064615 1800049 := bstep (se 2 (by rfl) ⟨675018, by rfl⟩ : syracuseStep 1800049 = 1350037) B1350037
theorem B1800083 : Blo 1064615 1800083 := bstep (se 1 (by rfl) ⟨1350062, by rfl⟩ : syracuseStep 1800083 = 2700125) B2700125
theorem B6158243 : Blo 1064615 6158243 := bstep (se 1 (by rfl) ⟨4618682, by rfl⟩ : syracuseStep 6158243 = 9237365) B9237365
theorem B3602339 : Blo 1064615 3602339 := bstep (se 1 (by rfl) ⟨2701754, by rfl⟩ : syracuseStep 3602339 = 5403509) B5403509
theorem B5404643 : Blo 1064615 5404643 := bstep (se 1 (by rfl) ⟨4053482, by rfl⟩ : syracuseStep 5404643 = 8106965) B8106965
theorem B1800211 : Blo 1064615 1800211 := bstep (se 1 (by rfl) ⟨1350158, by rfl⟩ : syracuseStep 1800211 = 2700317) B2700317
theorem B1800353 : Blo 1064615 1800353 := bstep (se 2 (by rfl) ⟨675132, by rfl⟩ : syracuseStep 1800353 = 1350265) B1350265
theorem B3602609 : Blo 1064615 3602609 := bstep (se 2 (by rfl) ⟨1350978, by rfl⟩ : syracuseStep 3602609 = 2701957) B2701957
theorem B1800481 : Blo 1064615 1800481 := bstep (se 2 (by rfl) ⟨675180, by rfl⟩ : syracuseStep 1800481 = 1350361) B1350361
theorem B5765411 : Blo 1064615 5765411 := bstep (se 1 (by rfl) ⟨4324058, by rfl⟩ : syracuseStep 5765411 = 8648117) B8648117
theorem B1800515 : Blo 1064615 1800515 := bstep (se 1 (by rfl) ⟨1350386, by rfl⟩ : syracuseStep 1800515 = 2700773) B2700773
theorem B1800643 : Blo 1064615 1800643 := bstep (se 1 (by rfl) ⟨1350482, by rfl⟩ : syracuseStep 1800643 = 2700965) B2700965
theorem B1800785 : Blo 1064615 1800785 := bstep (se 2 (by rfl) ⟨675294, by rfl⟩ : syracuseStep 1800785 = 1350589) B1350589
theorem B3603149 : Blo 1064615 3603149 := bstep (se 3 (by rfl) ⟨675590, by rfl⟩ : syracuseStep 3603149 = 1351181) B1351181
theorem B1800913 : Blo 1064615 1800913 := bstep (se 2 (by rfl) ⟨675342, by rfl⟩ : syracuseStep 1800913 = 1350685) B1350685
theorem B1800947 : Blo 1064615 1800947 := bstep (se 1 (by rfl) ⟨1350710, by rfl⟩ : syracuseStep 1800947 = 2701421) B2701421
theorem B3603203 : Blo 1064615 3603203 := bstep (se 1 (by rfl) ⟨2702402, by rfl⟩ : syracuseStep 3603203 = 5404805) B5404805
theorem B5405453 : Blo 1064615 5405453 := bstep (se 3 (by rfl) ⟨1013522, by rfl⟩ : syracuseStep 5405453 = 2027045) B2027045
theorem B1801075 : Blo 1064615 1801075 := bstep (se 1 (by rfl) ⟨1350806, by rfl⟩ : syracuseStep 1801075 = 2701613) B2701613
theorem B1801217 : Blo 1064615 1801217 := bstep (se 2 (by rfl) ⟨675456, by rfl⟩ : syracuseStep 1801217 = 1350913) B1350913
theorem B3603473 : Blo 1064615 3603473 := bstep (se 2 (by rfl) ⟨1351302, by rfl⟩ : syracuseStep 3603473 = 2702605) B2702605
theorem B1801345 : Blo 1064615 1801345 := bstep (se 2 (by rfl) ⟨675504, by rfl⟩ : syracuseStep 1801345 = 1351009) B1351009
theorem B1801379 : Blo 1064615 1801379 := bstep (se 1 (by rfl) ⟨1351034, by rfl⟩ : syracuseStep 1801379 = 2702069) B2702069
theorem B1801507 : Blo 1064615 1801507 := bstep (se 1 (by rfl) ⟨1351130, by rfl⟩ : syracuseStep 1801507 = 2702261) B2702261
theorem B1801649 : Blo 1064615 1801649 := bstep (se 2 (by rfl) ⟨675618, by rfl⟩ : syracuseStep 1801649 = 1351237) B1351237
theorem B3604013 : Blo 1064615 3604013 := bstep (se 3 (by rfl) ⟨675752, by rfl⟩ : syracuseStep 3604013 = 1351505) B1351505
theorem B1801777 : Blo 1064615 1801777 := bstep (se 2 (by rfl) ⟨675666, by rfl⟩ : syracuseStep 1801777 = 1351333) B1351333
theorem B1801811 : Blo 1064615 1801811 := bstep (se 1 (by rfl) ⟨1351358, by rfl⟩ : syracuseStep 1801811 = 2702717) B2702717
theorem B3604067 : Blo 1064615 3604067 := bstep (se 1 (by rfl) ⟨2703050, by rfl⟩ : syracuseStep 3604067 = 5406101) B5406101
theorem B1801939 : Blo 1064615 1801939 := bstep (se 1 (by rfl) ⟨1351454, by rfl⟩ : syracuseStep 1801939 = 2702909) B2702909
theorem B1802081 : Blo 1064615 1802081 := bstep (se 2 (by rfl) ⟨675780, by rfl⟩ : syracuseStep 1802081 = 1351561) B1351561
theorem B3604337 : Blo 1064615 3604337 := bstep (se 2 (by rfl) ⟨1351626, by rfl⟩ : syracuseStep 3604337 = 2703253) B2703253
theorem B4554701 : Blo 1064615 4554701 := bstep (se 3 (by rfl) ⟨854006, by rfl⟩ : syracuseStep 4554701 = 1708013) B1708013
theorem B1802209 : Blo 1064615 1802209 := bstep (se 2 (by rfl) ⟨675828, by rfl⟩ : syracuseStep 1802209 = 1351657) B1351657
theorem B4554737 : Blo 1064615 4554737 := bstep (se 2 (by rfl) ⟨1708026, by rfl⟩ : syracuseStep 4554737 = 3416053) B3416053
theorem B1802263 : Blo 1064615 1802263 := bstep (se 1 (by rfl) ⟨1351697, by rfl⟩ : syracuseStep 1802263 = 2703395) B2703395
theorem B4325521 : Blo 1064615 4325521 := bstep (se 2 (by rfl) ⟨1622070, by rfl⟩ : syracuseStep 4325521 = 3244141) B3244141
theorem B5767469 : Blo 1064615 5767469 := bstep (se 3 (by rfl) ⟨1081400, by rfl⟩ : syracuseStep 5767469 = 2162801) B2162801
theorem B6488471 : Blo 1064615 6488471 := bstep (se 1 (by rfl) ⟨4866353, by rfl⟩ : syracuseStep 6488471 = 9732707) B9732707
theorem B1081931 : Blo 1064615 1081931 := bstep (se 1 (by rfl) ⟨811448, by rfl⟩ : syracuseStep 1081931 = 1622897) B1622897
theorem B1802891 : Blo 1064615 1802891 := bstep (se 1 (by rfl) ⟨1352168, by rfl⟩ : syracuseStep 1802891 = 2704337) B2704337
theorem B1803019 : Blo 1064615 1803019 := bstep (se 1 (by rfl) ⟨1352264, by rfl⟩ : syracuseStep 1803019 = 2704529) B2704529
theorem B1803161 : Blo 1064615 1803161 := bstep (se 2 (by rfl) ⟨676185, by rfl⟩ : syracuseStep 1803161 = 1352371) B1352371
theorem B10552241 : Blo 1064615 10552241 := bstep (se 2 (by rfl) ⟨3957090, by rfl⟩ : syracuseStep 10552241 = 7914181) B7914181
theorem B1803289 : Blo 1064615 1803289 := bstep (se 2 (by rfl) ⟨676233, by rfl⟩ : syracuseStep 1803289 = 1352467) B1352467
theorem B3605579 : Blo 1064615 3605579 := bstep (se 1 (by rfl) ⟨2704184, by rfl⟩ : syracuseStep 3605579 = 5408369) B5408369
theorem B1082539 : Blo 1064615 1082539 := bstep (se 1 (by rfl) ⟨811904, by rfl⟩ : syracuseStep 1082539 = 1623809) B1623809
theorem B32834821 : Blo 1064615 32834821 := bstep (se 4 (by rfl) ⟨3078264, by rfl⟩ : syracuseStep 32834821 = 6156529) B6156529
theorem B5408045 : Blo 1064615 5408045 := bstep (se 3 (by rfl) ⟨1014008, by rfl⟩ : syracuseStep 5408045 = 2028017) B2028017
theorem B3605849 : Blo 1064615 3605849 := bstep (se 2 (by rfl) ⟨1352193, by rfl⟩ : syracuseStep 3605849 = 2704387) B2704387
theorem B4097459 : Blo 1064615 4097459 := bstep (se 1 (by rfl) ⟨3073094, by rfl⟩ : syracuseStep 4097459 = 6146189) B6146189
theorem B7702091 : Blo 1064615 7702091 := bstep (se 1 (by rfl) ⟨5776568, by rfl⟩ : syracuseStep 7702091 = 11553137) B11553137
theorem B7308893 : Blo 1064615 7308893 := bstep (se 3 (by rfl) ⟨1370417, by rfl⟩ : syracuseStep 7308893 = 2740835) B2740835
theorem B3704471 : Blo 1064615 3704471 := bstep (se 1 (by rfl) ⟨2778353, by rfl⟩ : syracuseStep 3704471 = 5556707) B5556707
theorem B7014275 : Blo 1064615 7014275 := bstep (se 1 (by rfl) ⟨5260706, by rfl⟩ : syracuseStep 7014275 = 10521413) B10521413
theorem B1279895 : Blo 1064615 1279895 := bstep (se 1 (by rfl) ⟨959921, by rfl⟩ : syracuseStep 1279895 = 1919843) B1919843
theorem B3606551 : Blo 1064615 3606551 := bstep (se 1 (by rfl) ⟨2704913, by rfl⟩ : syracuseStep 3606551 = 5409827) B5409827
theorem B3082333 : Blo 1064615 3082333 := bstep (se 3 (by rfl) ⟨577937, by rfl⟩ : syracuseStep 3082333 = 1155875) B1155875
theorem B1280395 : Blo 1064615 1280395 := bstep (se 1 (by rfl) ⟨960296, by rfl⟩ : syracuseStep 1280395 = 1920593) B1920593
theorem B2165207 : Blo 1064615 2165207 := bstep (se 1 (by rfl) ⟨1623905, by rfl⟩ : syracuseStep 2165207 = 3247811) B3247811
theorem B8096273 : Blo 1064615 8096273 := bstep (se 2 (by rfl) ⟨3036102, by rfl⟩ : syracuseStep 8096273 = 6072205) B6072205
theorem B1706521 : Blo 1064615 1706521 := bstep (se 2 (by rfl) ⟨639945, by rfl⟩ : syracuseStep 1706521 = 1279891) B1279891
theorem B2165273 : Blo 1064615 2165273 := bstep (se 2 (by rfl) ⟨811977, by rfl⟩ : syracuseStep 2165273 = 1623955) B1623955
theorem B2886209 : Blo 1064615 2886209 := bstep (se 2 (by rfl) ⟨1082328, by rfl⟩ : syracuseStep 2886209 = 2164657) B2164657
theorem B6064733 : Blo 1064615 6064733 := bstep (se 3 (by rfl) ⟨1137137, by rfl⟩ : syracuseStep 6064733 = 2274275) B2274275
theorem B3246743 : Blo 1064615 3246743 := bstep (se 1 (by rfl) ⟨2435057, by rfl⟩ : syracuseStep 3246743 = 4870115) B4870115
theorem B10259149 : Blo 1064615 10259149 := bstep (se 3 (by rfl) ⟨1923590, by rfl⟩ : syracuseStep 10259149 = 3847181) B3847181
theorem B1280779 : Blo 1064615 1280779 := bstep (se 1 (by rfl) ⟨960584, by rfl⟩ : syracuseStep 1280779 = 1921169) B1921169
theorem B31558577 : Blo 1064615 31558577 := bstep (se 2 (by rfl) ⟨11834466, by rfl⟩ : syracuseStep 31558577 = 23668933) B23668933
theorem B2559041 : Blo 1064615 2559041 := bstep (se 2 (by rfl) ⟨959640, by rfl⟩ : syracuseStep 2559041 = 1919281) B1919281
theorem B2165825 : Blo 1064615 2165825 := bstep (se 2 (by rfl) ⟨812184, by rfl⟩ : syracuseStep 2165825 = 1624369) B1624369
theorem B2395403 : Blo 1064615 2395403 := bstep (se 1 (by rfl) ⟨1796552, by rfl⟩ : syracuseStep 2395403 = 3593105) B3593105
theorem B4558103 : Blo 1064615 4558103 := bstep (se 1 (by rfl) ⟨3418577, by rfl⟩ : syracuseStep 4558103 = 6837155) B6837155
theorem B2395457 : Blo 1064615 2395457 := bstep (se 2 (by rfl) ⟨898296, by rfl⟩ : syracuseStep 2395457 = 1796593) B1796593
theorem B9113093 : Blo 1064615 9113093 := bstep (se 4 (by rfl) ⟨854352, by rfl⟩ : syracuseStep 9113093 = 1708705) B1708705
theorem B2395673 : Blo 1064615 2395673 := bstep (se 2 (by rfl) ⟨898377, by rfl⟩ : syracuseStep 2395673 = 1796755) B1796755
theorem B2428481 : Blo 1064615 2428481 := bstep (se 2 (by rfl) ⟨910680, by rfl⟩ : syracuseStep 2428481 = 1821361) B1821361
theorem B2395763 : Blo 1064615 2395763 := bstep (se 1 (by rfl) ⟨1796822, by rfl⟩ : syracuseStep 2395763 = 3593645) B3593645
theorem B2395799 : Blo 1064615 2395799 := bstep (se 1 (by rfl) ⟨1796849, by rfl⟩ : syracuseStep 2395799 = 3593699) B3593699
theorem B4329281 : Blo 1064615 4329281 := bstep (se 2 (by rfl) ⟨1623480, by rfl⟩ : syracuseStep 4329281 = 3246961) B3246961
theorem B2395979 : Blo 1064615 2395979 := bstep (se 1 (by rfl) ⟨1796984, by rfl⟩ : syracuseStep 2395979 = 3593969) B3593969
theorem B2396033 : Blo 1064615 2396033 := bstep (se 2 (by rfl) ⟨898512, by rfl⟩ : syracuseStep 2396033 = 1797025) B1797025
theorem B1281943 : Blo 1064615 1281943 := bstep (se 1 (by rfl) ⟨961457, by rfl⟩ : syracuseStep 1281943 = 1922915) B1922915
theorem B15175603 : Blo 1064615 15175603 := bstep (se 1 (by rfl) ⟨11381702, by rfl⟩ : syracuseStep 15175603 = 22763405) B22763405
theorem B3837955 : Blo 1064615 3837955 := bstep (se 1 (by rfl) ⟨2878466, by rfl⟩ : syracuseStep 3837955 = 5756933) B5756933
theorem B1347607 : Blo 1064615 1347607 := bstep (se 1 (by rfl) ⟨1010705, by rfl⟩ : syracuseStep 1347607 = 2021411) B2021411
theorem B1282135 : Blo 1064615 1282135 := bstep (se 1 (by rfl) ⟨961601, by rfl⟩ : syracuseStep 1282135 = 1923203) B1923203
theorem B2396249 : Blo 1064615 2396249 := bstep (se 2 (by rfl) ⟨898593, by rfl⟩ : syracuseStep 2396249 = 1797187) B1797187
theorem B2396339 : Blo 1064615 2396339 := bstep (se 1 (by rfl) ⟨1797254, by rfl⟩ : syracuseStep 2396339 = 3594509) B3594509
theorem B2396375 : Blo 1064615 2396375 := bstep (se 1 (by rfl) ⟨1797281, by rfl⟩ : syracuseStep 2396375 = 3594563) B3594563
theorem B2396555 : Blo 1064615 2396555 := bstep (se 1 (by rfl) ⟨1797416, by rfl⟩ : syracuseStep 2396555 = 3594833) B3594833
theorem B2396609 : Blo 1064615 2396609 := bstep (se 2 (by rfl) ⟨898728, by rfl⟩ : syracuseStep 2396609 = 1797457) B1797457
theorem B3412631 : Blo 1064615 3412631 := bstep (se 1 (by rfl) ⟨2559473, by rfl⟩ : syracuseStep 3412631 = 5118947) B5118947
theorem B2396825 : Blo 1064615 2396825 := bstep (se 2 (by rfl) ⟨898809, by rfl⟩ : syracuseStep 2396825 = 1797619) B1797619
theorem B2396915 : Blo 1064615 2396915 := bstep (se 1 (by rfl) ⟨1797686, by rfl⟩ : syracuseStep 2396915 = 3595373) B3595373
theorem B1643275 : Blo 1064615 1643275 := bstep (se 1 (by rfl) ⟨1232456, by rfl⟩ : syracuseStep 1643275 = 2464913) B2464913
theorem B2396951 : Blo 1064615 2396951 := bstep (se 1 (by rfl) ⟨1797713, by rfl⟩ : syracuseStep 2396951 = 3595427) B3595427
theorem B1348427 : Blo 1064615 1348427 := bstep (se 1 (by rfl) ⟨1011320, by rfl⟩ : syracuseStep 1348427 = 2022641) B2022641
theorem B2397131 : Blo 1064615 2397131 := bstep (se 1 (by rfl) ⟨1797848, by rfl⟩ : syracuseStep 2397131 = 3595697) B3595697
theorem B2397185 : Blo 1064615 2397185 := bstep (se 2 (by rfl) ⟨898944, by rfl⟩ : syracuseStep 2397185 = 1797889) B1797889
theorem B3839051 : Blo 1064615 3839051 := bstep (se 1 (by rfl) ⟨2879288, by rfl⟩ : syracuseStep 3839051 = 5758577) B5758577
theorem B6067331 : Blo 1064615 6067331 := bstep (se 1 (by rfl) ⟨4550498, by rfl⟩ : syracuseStep 6067331 = 9100997) B9100997
theorem B2397401 : Blo 1064615 2397401 := bstep (se 2 (by rfl) ⟨899025, by rfl⟩ : syracuseStep 2397401 = 1798051) B1798051
theorem B2430233 : Blo 1064615 2430233 := bstep (se 2 (by rfl) ⟨911337, by rfl⟩ : syracuseStep 2430233 = 1822675) B1822675
theorem B2397491 : Blo 1064615 2397491 := bstep (se 1 (by rfl) ⟨1798118, by rfl⟩ : syracuseStep 2397491 = 3596237) B3596237
theorem B2397527 : Blo 1064615 2397527 := bstep (se 1 (by rfl) ⟨1798145, by rfl⟩ : syracuseStep 2397527 = 3596291) B3596291
theorem B2561473 : Blo 1064615 2561473 := bstep (se 2 (by rfl) ⟨960552, by rfl⟩ : syracuseStep 2561473 = 1921105) B1921105
theorem B2397707 : Blo 1064615 2397707 := bstep (se 1 (by rfl) ⟨1798280, by rfl⟩ : syracuseStep 2397707 = 3596561) B3596561
theorem B1349131 : Blo 1064615 1349131 := bstep (se 1 (by rfl) ⟨1011848, by rfl⟩ : syracuseStep 1349131 = 2023697) B2023697
theorem B2397761 : Blo 1064615 2397761 := bstep (se 2 (by rfl) ⟨899160, by rfl⟩ : syracuseStep 2397761 = 1798321) B1798321
theorem B12162635 : Blo 1064615 12162635 := bstep (se 1 (by rfl) ⟨9121976, by rfl⟩ : syracuseStep 12162635 = 18243953) B18243953
theorem B1283735 : Blo 1064615 1283735 := bstep (se 1 (by rfl) ⟨962801, by rfl⟩ : syracuseStep 1283735 = 1925603) B1925603
theorem B4560563 : Blo 1064615 4560563 := bstep (se 1 (by rfl) ⟨3420422, by rfl⟩ : syracuseStep 4560563 = 6840845) B6840845
theorem B3282653 : Blo 1064615 3282653 := bstep (se 3 (by rfl) ⟨615497, by rfl⟩ : syracuseStep 3282653 = 1230995) B1230995
theorem B1349399 : Blo 1064615 1349399 := bstep (se 1 (by rfl) ⟨1012049, by rfl⟩ : syracuseStep 1349399 = 2024099) B2024099
theorem B2397977 : Blo 1064615 2397977 := bstep (se 2 (by rfl) ⟨899241, by rfl⟩ : syracuseStep 2397977 = 1798483) B1798483
theorem B4560715 : Blo 1064615 4560715 := bstep (se 1 (by rfl) ⟨3420536, by rfl⟩ : syracuseStep 4560715 = 6841073) B6841073
theorem B2398067 : Blo 1064615 2398067 := bstep (se 1 (by rfl) ⟨1798550, by rfl⟩ : syracuseStep 2398067 = 3597101) B3597101
theorem B4560785 : Blo 1064615 4560785 := bstep (se 2 (by rfl) ⟨1710294, by rfl⟩ : syracuseStep 4560785 = 3420589) B3420589
theorem B2398103 : Blo 1064615 2398103 := bstep (se 1 (by rfl) ⟨1798577, by rfl⟩ : syracuseStep 2398103 = 3597155) B3597155
theorem B17536945 : Blo 1064615 17536945 := bstep (se 2 (by rfl) ⟨6576354, by rfl⟩ : syracuseStep 17536945 = 13152709) B13152709
theorem B11671627 : Blo 1064615 11671627 := bstep (se 1 (by rfl) ⟨8753720, by rfl⟩ : syracuseStep 11671627 = 17507441) B17507441
theorem B2398283 : Blo 1064615 2398283 := bstep (se 1 (by rfl) ⟨1798712, by rfl⟩ : syracuseStep 2398283 = 3597425) B3597425
theorem B2398337 : Blo 1064615 2398337 := bstep (se 2 (by rfl) ⟨899376, by rfl⟩ : syracuseStep 2398337 = 1798753) B1798753
theorem B4331713 : Blo 1064615 4331713 := bstep (se 2 (by rfl) ⟨1624392, by rfl⟩ : syracuseStep 4331713 = 3248785) B3248785
theorem B8100161 : Blo 1064615 8100161 := bstep (se 2 (by rfl) ⟨3037560, by rfl⟩ : syracuseStep 8100161 = 6075121) B6075121
theorem B1644875 : Blo 1064615 1644875 := bstep (se 1 (by rfl) ⟨1233656, by rfl⟩ : syracuseStep 1644875 = 2467313) B2467313
theorem B2398553 : Blo 1064615 2398553 := bstep (se 2 (by rfl) ⟨899457, by rfl⟩ : syracuseStep 2398553 = 1798915) B1798915
theorem B1710487 : Blo 1064615 1710487 := bstep (se 1 (by rfl) ⟨1282865, by rfl⟩ : syracuseStep 1710487 = 2565731) B2565731
theorem B2398643 : Blo 1064615 2398643 := bstep (se 1 (by rfl) ⟨1798982, by rfl⟩ : syracuseStep 2398643 = 3597965) B3597965
theorem B4004275 : Blo 1064615 4004275 := bstep (se 1 (by rfl) ⟨3003206, by rfl⟩ : syracuseStep 4004275 = 6006413) B6006413
theorem B2398679 : Blo 1064615 2398679 := bstep (se 1 (by rfl) ⟨1799009, by rfl⟩ : syracuseStep 2398679 = 3598019) B3598019
theorem B1350103 : Blo 1064615 1350103 := bstep (se 1 (by rfl) ⟨1012577, by rfl⟩ : syracuseStep 1350103 = 2025155) B2025155
theorem B1710551 : Blo 1064615 1710551 := bstep (se 1 (by rfl) ⟨1282913, by rfl⟩ : syracuseStep 1710551 = 2565827) B2565827
theorem B2398859 : Blo 1064615 2398859 := bstep (se 1 (by rfl) ⟨1799144, by rfl⟩ : syracuseStep 2398859 = 3598289) B3598289
theorem B2398913 : Blo 1064615 2398913 := bstep (se 2 (by rfl) ⟨899592, by rfl⟩ : syracuseStep 2398913 = 1799185) B1799185
theorem B9116509 : Blo 1064615 9116509 := bstep (se 3 (by rfl) ⟨1709345, by rfl⟩ : syracuseStep 9116509 = 3418691) B3418691
theorem B2399129 : Blo 1064615 2399129 := bstep (se 2 (by rfl) ⟨899673, by rfl⟩ : syracuseStep 2399129 = 1799347) B1799347
theorem B4332491 : Blo 1064615 4332491 := bstep (se 1 (by rfl) ⟨3249368, by rfl⟩ : syracuseStep 4332491 = 6498737) B6498737
theorem B2399219 : Blo 1064615 2399219 := bstep (se 1 (by rfl) ⟨1799414, by rfl⟩ : syracuseStep 2399219 = 3598829) B3598829
theorem B1711115 : Blo 1064615 1711115 := bstep (se 1 (by rfl) ⟨1283336, by rfl⟩ : syracuseStep 1711115 = 2566673) B2566673
theorem B2399255 : Blo 1064615 2399255 := bstep (se 1 (by rfl) ⟨1799441, by rfl⟩ : syracuseStep 2399255 = 3598883) B3598883
theorem B2399435 : Blo 1064615 2399435 := bstep (se 1 (by rfl) ⟨1799576, by rfl⟩ : syracuseStep 2399435 = 3599153) B3599153
theorem B1711307 : Blo 1064615 1711307 := bstep (se 1 (by rfl) ⟨1283480, by rfl⟩ : syracuseStep 1711307 = 2566961) B2566961
theorem B2399489 : Blo 1064615 2399489 := bstep (se 2 (by rfl) ⟨899808, by rfl⟩ : syracuseStep 2399489 = 1799617) B1799617
theorem B1154315 : Blo 1064615 1154315 := bstep (se 1 (by rfl) ⟨865736, by rfl⟩ : syracuseStep 1154315 = 1731473) B1731473
theorem B2432321 : Blo 1064615 2432321 := bstep (se 2 (by rfl) ⟨912120, by rfl⟩ : syracuseStep 2432321 = 1824241) B1824241
theorem B4922797 : Blo 1064615 4922797 := bstep (se 3 (by rfl) ⟨923024, by rfl⟩ : syracuseStep 4922797 = 1846049) B1846049
theorem B2399705 : Blo 1064615 2399705 := bstep (se 2 (by rfl) ⟨899889, by rfl⟩ : syracuseStep 2399705 = 1799779) B1799779
theorem B4562477 : Blo 1064615 4562477 := bstep (se 3 (by rfl) ⟨855464, by rfl⟩ : syracuseStep 4562477 = 1710929) B1710929
theorem B2399795 : Blo 1064615 2399795 := bstep (se 1 (by rfl) ⟨1799846, by rfl⟩ : syracuseStep 2399795 = 3599693) B3599693
theorem B2399831 : Blo 1064615 2399831 := bstep (se 1 (by rfl) ⟨1799873, by rfl⟩ : syracuseStep 2399831 = 3599747) B3599747
theorem B3415745 : Blo 1064615 3415745 := bstep (se 2 (by rfl) ⟨1280904, by rfl⟩ : syracuseStep 3415745 = 2561809) B2561809
theorem B2400011 : Blo 1064615 2400011 := bstep (se 1 (by rfl) ⟨1800008, by rfl⟩ : syracuseStep 2400011 = 3600017) B3600017
theorem B2400065 : Blo 1064615 2400065 := bstep (se 2 (by rfl) ⟨900024, by rfl⟩ : syracuseStep 2400065 = 1800049) B1800049
theorem B2400281 : Blo 1064615 2400281 := bstep (se 2 (by rfl) ⟨900105, by rfl⟩ : syracuseStep 2400281 = 1800211) B1800211
theorem B2400371 : Blo 1064615 2400371 := bstep (se 1 (by rfl) ⟨1800278, by rfl⟩ : syracuseStep 2400371 = 3600557) B3600557
theorem B1351819 : Blo 1064615 1351819 := bstep (se 1 (by rfl) ⟨1013864, by rfl⟩ : syracuseStep 1351819 = 2027729) B2027729
theorem B4858001 : Blo 1064615 4858001 := bstep (se 2 (by rfl) ⟨1821750, by rfl⟩ : syracuseStep 4858001 = 3643501) B3643501
theorem B2400407 : Blo 1064615 2400407 := bstep (se 1 (by rfl) ⟨1800305, by rfl⟩ : syracuseStep 2400407 = 3600611) B3600611
theorem B8102105 : Blo 1064615 8102105 := bstep (se 2 (by rfl) ⟨3038289, by rfl⟩ : syracuseStep 8102105 = 6076579) B6076579
theorem B4563161 : Blo 1064615 4563161 := bstep (se 2 (by rfl) ⟨1711185, by rfl⟩ : syracuseStep 4563161 = 3422371) B3422371
theorem B5120273 : Blo 1064615 5120273 := bstep (se 2 (by rfl) ⟨1920102, by rfl⟩ : syracuseStep 5120273 = 3840205) B3840205
theorem B2400587 : Blo 1064615 2400587 := bstep (se 1 (by rfl) ⟨1800440, by rfl⟩ : syracuseStep 2400587 = 3600881) B3600881
theorem B2400641 : Blo 1064615 2400641 := bstep (se 2 (by rfl) ⟨900240, by rfl⟩ : syracuseStep 2400641 = 1800481) B1800481
theorem B10232243 : Blo 1064615 10232243 := bstep (se 1 (by rfl) ⟨7674182, by rfl⟩ : syracuseStep 10232243 = 15348365) B15348365
theorem B5775833 : Blo 1064615 5775833 := bstep (se 2 (by rfl) ⟨2165937, by rfl⟩ : syracuseStep 5775833 = 4331875) B4331875
theorem B2400857 : Blo 1064615 2400857 := bstep (se 2 (by rfl) ⟨900321, by rfl⟩ : syracuseStep 2400857 = 1800643) B1800643
theorem B2400947 : Blo 1064615 2400947 := bstep (se 1 (by rfl) ⟨1800710, by rfl⟩ : syracuseStep 2400947 = 3601421) B3601421
theorem B2400983 : Blo 1064615 2400983 := bstep (se 1 (by rfl) ⟨1800737, by rfl⟩ : syracuseStep 2400983 = 3601475) B3601475
theorem B2433907 : Blo 1064615 2433907 := bstep (se 1 (by rfl) ⟨1825430, by rfl⟩ : syracuseStep 2433907 = 3650861) B3650861
theorem B2401163 : Blo 1064615 2401163 := bstep (se 1 (by rfl) ⟨1800872, by rfl⟩ : syracuseStep 2401163 = 3601745) B3601745
theorem B2401217 : Blo 1064615 2401217 := bstep (se 2 (by rfl) ⟨900456, by rfl⟩ : syracuseStep 2401217 = 1800913) B1800913
theorem B2696267 : Blo 1064615 2696267 := bstep (se 1 (by rfl) ⟨2022200, by rfl⟩ : syracuseStep 2696267 = 4044401) B4044401
theorem B8004701 : Blo 1064615 8004701 := bstep (se 3 (by rfl) ⟨1500881, by rfl⟩ : syracuseStep 8004701 = 3001763) B3001763
theorem B6923395 : Blo 1064615 6923395 := bstep (se 1 (by rfl) ⟨5192546, by rfl⟩ : syracuseStep 6923395 = 10385093) B10385093
theorem B2401433 : Blo 1064615 2401433 := bstep (se 2 (by rfl) ⟨900537, by rfl⟩ : syracuseStep 2401433 = 1801075) B1801075
theorem B2401523 : Blo 1064615 2401523 := bstep (se 1 (by rfl) ⟨1801142, by rfl⟩ : syracuseStep 2401523 = 3602285) B3602285
theorem B4105495 : Blo 1064615 4105495 := bstep (se 1 (by rfl) ⟨3079121, by rfl⟩ : syracuseStep 4105495 = 6158243) B6158243
theorem B2401559 : Blo 1064615 2401559 := bstep (se 1 (by rfl) ⟨1801169, by rfl⟩ : syracuseStep 2401559 = 3602339) B3602339
theorem B2401739 : Blo 1064615 2401739 := bstep (se 1 (by rfl) ⟨1801304, by rfl⟩ : syracuseStep 2401739 = 3602609) B3602609
theorem B1517015 : Blo 1064615 1517015 := bstep (se 1 (by rfl) ⟨1137761, by rfl⟩ : syracuseStep 1517015 = 2275523) B2275523
theorem B2401793 : Blo 1064615 2401793 := bstep (se 2 (by rfl) ⟨900672, by rfl⟩ : syracuseStep 2401793 = 1801345) B1801345
theorem B3843607 : Blo 1064615 3843607 := bstep (se 1 (by rfl) ⟨2882705, by rfl⟩ : syracuseStep 3843607 = 5765411) B5765411
theorem B2402009 : Blo 1064615 2402009 := bstep (se 2 (by rfl) ⟨900753, by rfl⟩ : syracuseStep 2402009 = 1801507) B1801507
theorem B3417821 : Blo 1064615 3417821 := bstep (se 3 (by rfl) ⟨640841, by rfl⟩ : syracuseStep 3417821 = 1281683) B1281683
theorem B2402099 : Blo 1064615 2402099 := bstep (se 1 (by rfl) ⟨1801574, by rfl⟩ : syracuseStep 2402099 = 3603149) B3603149
theorem B2402135 : Blo 1064615 2402135 := bstep (se 1 (by rfl) ⟨1801601, by rfl⟩ : syracuseStep 2402135 = 3603203) B3603203
theorem B2402315 : Blo 1064615 2402315 := bstep (se 1 (by rfl) ⟨1801736, by rfl⟩ : syracuseStep 2402315 = 3603473) B3603473
theorem B2697239 : Blo 1064615 2697239 := bstep (se 1 (by rfl) ⟨2022929, by rfl⟩ : syracuseStep 2697239 = 4045859) B4045859
theorem B2402369 : Blo 1064615 2402369 := bstep (se 2 (by rfl) ⟨900888, by rfl⟩ : syracuseStep 2402369 = 1801777) B1801777
theorem B2402585 : Blo 1064615 2402585 := bstep (se 2 (by rfl) ⟨900969, by rfl⟩ : syracuseStep 2402585 = 1801939) B1801939
theorem B5122349 : Blo 1064615 5122349 := bstep (se 3 (by rfl) ⟨960440, by rfl⟩ : syracuseStep 5122349 = 1920881) B1920881
theorem B2402675 : Blo 1064615 2402675 := bstep (se 1 (by rfl) ⟨1802006, by rfl⟩ : syracuseStep 2402675 = 3604013) B3604013
theorem B2402711 : Blo 1064615 2402711 := bstep (se 1 (by rfl) ⟨1802033, by rfl⟩ : syracuseStep 2402711 = 3604067) B3604067
theorem B2402891 : Blo 1064615 2402891 := bstep (se 1 (by rfl) ⟨1802168, by rfl⟩ : syracuseStep 2402891 = 3604337) B3604337
theorem B2402945 : Blo 1064615 2402945 := bstep (se 2 (by rfl) ⟨901104, by rfl⟩ : syracuseStep 2402945 = 1802209) B1802209
theorem B2697907 : Blo 1064615 2697907 := bstep (se 1 (by rfl) ⟨2023430, by rfl⟩ : syracuseStep 2697907 = 4046861) B4046861
theorem B2468569 : Blo 1064615 2468569 := bstep (se 2 (by rfl) ⟨925713, by rfl⟩ : syracuseStep 2468569 = 1851427) B1851427
theorem B2698049 : Blo 1064615 2698049 := bstep (se 2 (by rfl) ⟨1011768, by rfl⟩ : syracuseStep 2698049 = 2023537) B2023537
theorem B6073163 : Blo 1064615 6073163 := bstep (se 1 (by rfl) ⟨4554872, by rfl⟩ : syracuseStep 6073163 = 9109745) B9109745
theorem B2403161 : Blo 1064615 2403161 := bstep (se 2 (by rfl) ⟨901185, by rfl⟩ : syracuseStep 2403161 = 1802371) B1802371
theorem B2403251 : Blo 1064615 2403251 := bstep (se 1 (by rfl) ⟨1802438, by rfl⟩ : syracuseStep 2403251 = 3604877) B3604877
theorem B2403287 : Blo 1064615 2403287 := bstep (se 1 (by rfl) ⟨1802465, by rfl⟩ : syracuseStep 2403287 = 3604931) B3604931
theorem B3419101 : Blo 1064615 3419101 := bstep (se 3 (by rfl) ⟨641081, by rfl⟩ : syracuseStep 3419101 = 1282163) B1282163
theorem B2403467 : Blo 1064615 2403467 := bstep (se 1 (by rfl) ⟨1802600, by rfl⟩ : syracuseStep 2403467 = 3605201) B3605201
theorem B2403521 : Blo 1064615 2403521 := bstep (se 2 (by rfl) ⟨901320, by rfl⟩ : syracuseStep 2403521 = 1802641) B1802641
theorem B2403737 : Blo 1064615 2403737 := bstep (se 2 (by rfl) ⟨901401, by rfl⟩ : syracuseStep 2403737 = 1802803) B1802803
theorem B3648971 : Blo 1064615 3648971 := bstep (se 1 (by rfl) ⟨2736728, by rfl⟩ : syracuseStep 3648971 = 5473457) B5473457
theorem B2403827 : Blo 1064615 2403827 := bstep (se 1 (by rfl) ⟨1802870, by rfl⟩ : syracuseStep 2403827 = 3605741) B3605741
theorem B2403863 : Blo 1064615 2403863 := bstep (se 1 (by rfl) ⟨1802897, by rfl⟩ : syracuseStep 2403863 = 3605795) B3605795
theorem B8105507 : Blo 1064615 8105507 := bstep (se 1 (by rfl) ⟨6079130, by rfl⟩ : syracuseStep 8105507 = 12158261) B12158261
theorem B4861633 : Blo 1064615 4861633 := bstep (se 2 (by rfl) ⟨1823112, by rfl⟩ : syracuseStep 4861633 = 3646225) B3646225
theorem B2404043 : Blo 1064615 2404043 := bstep (se 1 (by rfl) ⟨1803032, by rfl⟩ : syracuseStep 2404043 = 3606065) B3606065
theorem B4042457 : Blo 1064615 4042457 := bstep (se 2 (by rfl) ⟨1515921, by rfl⟩ : syracuseStep 4042457 = 3031843) B3031843
theorem B2404097 : Blo 1064615 2404097 := bstep (se 2 (by rfl) ⟨901536, by rfl⟩ : syracuseStep 2404097 = 1803073) B1803073
theorem B4042669 : Blo 1064615 4042669 := bstep (se 3 (by rfl) ⟨758000, by rfl⟩ : syracuseStep 4042669 = 1516001) B1516001
theorem B2404313 : Blo 1064615 2404313 := bstep (se 2 (by rfl) ⟨901617, by rfl⟩ : syracuseStep 2404313 = 1803235) B1803235
theorem B2699315 : Blo 1064615 2699315 := bstep (se 1 (by rfl) ⟨2024486, by rfl⟩ : syracuseStep 2699315 = 4048973) B4048973
theorem B23375947 : Blo 1064615 23375947 := bstep (se 1 (by rfl) ⟨17531960, by rfl⟩ : syracuseStep 23375947 = 35063921) B35063921
theorem B4042973 : Blo 1064615 4042973 := bstep (se 3 (by rfl) ⟨758057, by rfl⟩ : syracuseStep 4042973 = 1516115) B1516115
theorem B1519897 : Blo 1064615 1519897 := bstep (se 2 (by rfl) ⟨569961, by rfl⟩ : syracuseStep 1519897 = 1139923) B1139923
theorem B7287191 : Blo 1064615 7287191 := bstep (se 1 (by rfl) ⟨5465393, by rfl⟩ : syracuseStep 7287191 = 10930787) B10930787
theorem B2699851 : Blo 1064615 2699851 := bstep (se 1 (by rfl) ⟨2024888, by rfl⟩ : syracuseStep 2699851 = 4049777) B4049777
theorem B2699993 : Blo 1064615 2699993 := bstep (se 2 (by rfl) ⟨1012497, by rfl⟩ : syracuseStep 2699993 = 2024995) B2024995
theorem B3650507 : Blo 1064615 3650507 := bstep (se 1 (by rfl) ⟨2737880, by rfl⟩ : syracuseStep 3650507 = 5475761) B5475761
theorem B2274583 : Blo 1064615 2274583 := bstep (se 1 (by rfl) ⟨1705937, by rfl⟩ : syracuseStep 2274583 = 3411875) B3411875
theorem B2274635 : Blo 1064615 2274635 := bstep (se 1 (by rfl) ⟨1705976, by rfl⟩ : syracuseStep 2274635 = 3411953) B3411953
theorem B13841765 : Blo 1064615 13841765 := bstep (se 4 (by rfl) ⟨1297665, by rfl⟩ : syracuseStep 13841765 = 2595331) B2595331
theorem B1095115 : Blo 1064615 1095115 := bstep (se 1 (by rfl) ⟨821336, by rfl⟩ : syracuseStep 1095115 = 1642673) B1642673
theorem B2700823 : Blo 1064615 2700823 := bstep (se 1 (by rfl) ⟨2025617, by rfl⟩ : syracuseStep 2700823 = 4051235) B4051235
theorem B3847873 : Blo 1064615 3847873 := bstep (se 2 (by rfl) ⟨1442952, by rfl⟩ : syracuseStep 3847873 = 2885905) B2885905
theorem B1521355 : Blo 1064615 1521355 := bstep (se 1 (by rfl) ⟨1141016, by rfl⟩ : syracuseStep 1521355 = 2282033) B2282033
theorem B5125963 : Blo 1064615 5125963 := bstep (se 1 (by rfl) ⟨3844472, by rfl⟩ : syracuseStep 5125963 = 7688945) B7688945
theorem B2701259 : Blo 1064615 2701259 := bstep (se 1 (by rfl) ⟨2025944, by rfl⟩ : syracuseStep 2701259 = 4051889) B4051889
theorem B3848323 : Blo 1064615 3848323 := bstep (se 1 (by rfl) ⟨2886242, by rfl⟩ : syracuseStep 3848323 = 5772485) B5772485
theorem B17283253 : Blo 1064615 17283253 := bstep (se 5 (by rfl) ⟨810152, by rfl⟩ : syracuseStep 17283253 = 1620305) B1620305
theorem B2701633 : Blo 1064615 2701633 := bstep (se 2 (by rfl) ⟨1013112, by rfl⟩ : syracuseStep 2701633 = 2026225) B2026225
theorem B3651929 : Blo 1064615 3651929 := bstep (se 2 (by rfl) ⟨1369473, by rfl⟩ : syracuseStep 3651929 = 2738947) B2738947
theorem B11516377 : Blo 1064615 11516377 := bstep (se 2 (by rfl) ⟨4318641, by rfl⟩ : syracuseStep 11516377 = 8637283) B8637283
theorem B5126807 : Blo 1064615 5126807 := bstep (se 1 (by rfl) ⟨3845105, by rfl⟩ : syracuseStep 5126807 = 7690211) B7690211
theorem B1620695 : Blo 1064615 1620695 := bstep (se 1 (by rfl) ⟨1215521, by rfl⟩ : syracuseStep 1620695 = 2431043) B2431043
theorem B4045571 : Blo 1064615 4045571 := bstep (se 1 (by rfl) ⟨3034178, by rfl⟩ : syracuseStep 4045571 = 6068357) B6068357
theorem B4045585 : Blo 1064615 4045585 := bstep (se 2 (by rfl) ⟨1517094, by rfl⟩ : syracuseStep 4045585 = 3034189) B3034189
theorem B4111127 : Blo 1064615 4111127 := bstep (se 1 (by rfl) ⟨3083345, by rfl⟩ : syracuseStep 4111127 = 6166691) B6166691
theorem B2702231 : Blo 1064615 2702231 := bstep (se 1 (by rfl) ⟨2026673, by rfl⟩ : syracuseStep 2702231 = 4053347) B4053347
theorem B2276275 : Blo 1064615 2276275 := bstep (se 1 (by rfl) ⟨1707206, by rfl⟩ : syracuseStep 2276275 = 3414413) B3414413
theorem B4996099 : Blo 1064615 4996099 := bstep (se 1 (by rfl) ⟨3747074, by rfl⟩ : syracuseStep 4996099 = 7494149) B7494149
theorem B3292211 : Blo 1064615 3292211 := bstep (se 1 (by rfl) ⟨2469158, by rfl⟩ : syracuseStep 3292211 = 4938317) B4938317
theorem B4045889 : Blo 1064615 4045889 := bstep (se 2 (by rfl) ⟨1517208, by rfl⟩ : syracuseStep 4045889 = 3034417) B3034417
theorem B2276633 : Blo 1064615 2276633 := bstep (se 2 (by rfl) ⟨853737, by rfl⟩ : syracuseStep 2276633 = 1707475) B1707475
theorem B1949017 : Blo 1064615 1949017 := bstep (se 2 (by rfl) ⟨730881, by rfl⟩ : syracuseStep 1949017 = 1461763) B1461763
theorem B7781923 : Blo 1064615 7781923 := bstep (se 1 (by rfl) ⟨5836442, by rfl⟩ : syracuseStep 7781923 = 11672885) B11672885
theorem B1064619 : Blo 1064615 1064619 := bstep (se 1 (by rfl) ⟨798464, by rfl⟩ : syracuseStep 1064619 = 1596929) B1596929
theorem B1064631 : Blo 1064615 1064631 := bstep (se 1 (by rfl) ⟨798473, by rfl⟩ : syracuseStep 1064631 = 1596947) B1596947
theorem B2703041 : Blo 1064615 2703041 := bstep (se 2 (by rfl) ⟨1013640, by rfl⟩ : syracuseStep 2703041 = 2027281) B2027281
theorem B1064651 : Blo 1064615 1064651 := bstep (se 1 (by rfl) ⟨798488, by rfl⟩ : syracuseStep 1064651 = 1596977) B1596977
theorem B1064663 : Blo 1064615 1064663 := bstep (se 1 (by rfl) ⟨798497, by rfl⟩ : syracuseStep 1064663 = 1596995) B1596995
theorem B4046557 : Blo 1064615 4046557 := bstep (se 3 (by rfl) ⟨758729, by rfl⟩ : syracuseStep 4046557 = 1517459) B1517459
theorem B1064683 : Blo 1064615 1064683 := bstep (se 1 (by rfl) ⟨798512, by rfl⟩ : syracuseStep 1064683 = 1597025) B1597025
theorem B1064695 : Blo 1064615 1064695 := bstep (se 1 (by rfl) ⟨798521, by rfl⟩ : syracuseStep 1064695 = 1597043) B1597043
theorem B1064715 : Blo 1064615 1064715 := bstep (se 1 (by rfl) ⟨798536, by rfl⟩ : syracuseStep 1064715 = 1597073) B1597073
theorem B1064727 : Blo 1064615 1064727 := bstep (se 1 (by rfl) ⟨798545, by rfl⟩ : syracuseStep 1064727 = 1597091) B1597091
theorem B1064747 : Blo 1064615 1064747 := bstep (se 1 (by rfl) ⟨798560, by rfl⟩ : syracuseStep 1064747 = 1597121) B1597121
theorem B2309939 : Blo 1064615 2309939 := bstep (se 1 (by rfl) ⟨1732454, by rfl⟩ : syracuseStep 2309939 = 3464909) B3464909
theorem B1064759 : Blo 1064615 1064759 := bstep (se 1 (by rfl) ⟨798569, by rfl⟩ : syracuseStep 1064759 = 1597139) B1597139
theorem B1064779 : Blo 1064615 1064779 := bstep (se 1 (by rfl) ⟨798584, by rfl⟩ : syracuseStep 1064779 = 1597169) B1597169
theorem B1064791 : Blo 1064615 1064791 := bstep (se 1 (by rfl) ⟨798593, by rfl⟩ : syracuseStep 1064791 = 1597187) B1597187
theorem B1064811 : Blo 1064615 1064811 := bstep (se 1 (by rfl) ⟨798608, by rfl⟩ : syracuseStep 1064811 = 1597217) B1597217
theorem B1064823 : Blo 1064615 1064823 := bstep (se 1 (by rfl) ⟨798617, by rfl⟩ : syracuseStep 1064823 = 1597235) B1597235
theorem B1064843 : Blo 1064615 1064843 := bstep (se 1 (by rfl) ⟨798632, by rfl⟩ : syracuseStep 1064843 = 1597265) B1597265
theorem B1064855 : Blo 1064615 1064855 := bstep (se 1 (by rfl) ⟨798641, by rfl⟩ : syracuseStep 1064855 = 1597283) B1597283
theorem B1064875 : Blo 1064615 1064875 := bstep (se 1 (by rfl) ⟨798656, by rfl⟩ : syracuseStep 1064875 = 1597313) B1597313
theorem B1064887 : Blo 1064615 1064887 := bstep (se 1 (by rfl) ⟨798665, by rfl⟩ : syracuseStep 1064887 = 1597331) B1597331
theorem B1064907 : Blo 1064615 1064907 := bstep (se 1 (by rfl) ⟨798680, by rfl⟩ : syracuseStep 1064907 = 1597361) B1597361
theorem B1064919 : Blo 1064615 1064919 := bstep (se 1 (by rfl) ⟨798689, by rfl⟩ : syracuseStep 1064919 = 1597379) B1597379
theorem B1064939 : Blo 1064615 1064939 := bstep (se 1 (by rfl) ⟨798704, by rfl⟩ : syracuseStep 1064939 = 1597409) B1597409
theorem B1064951 : Blo 1064615 1064951 := bstep (se 1 (by rfl) ⟨798713, by rfl⟩ : syracuseStep 1064951 = 1597427) B1597427
theorem B1064971 : Blo 1064615 1064971 := bstep (se 1 (by rfl) ⟨798728, by rfl⟩ : syracuseStep 1064971 = 1597457) B1597457
theorem B1064983 : Blo 1064615 1064983 := bstep (se 1 (by rfl) ⟨798737, by rfl⟩ : syracuseStep 1064983 = 1597475) B1597475
theorem B1065003 : Blo 1064615 1065003 := bstep (se 1 (by rfl) ⟨798752, by rfl⟩ : syracuseStep 1065003 = 1597505) B1597505
theorem B1065015 : Blo 1064615 1065015 := bstep (se 1 (by rfl) ⟨798761, by rfl⟩ : syracuseStep 1065015 = 1597523) B1597523
theorem B1065035 : Blo 1064615 1065035 := bstep (se 1 (by rfl) ⟨798776, by rfl⟩ : syracuseStep 1065035 = 1597553) B1597553
theorem B1065047 : Blo 1064615 1065047 := bstep (se 1 (by rfl) ⟨798785, by rfl⟩ : syracuseStep 1065047 = 1597571) B1597571
theorem B1065067 : Blo 1064615 1065067 := bstep (se 1 (by rfl) ⟨798800, by rfl⟩ : syracuseStep 1065067 = 1597601) B1597601
theorem B1065079 : Blo 1064615 1065079 := bstep (se 1 (by rfl) ⟨798809, by rfl⟩ : syracuseStep 1065079 = 1597619) B1597619
theorem B1065099 : Blo 1064615 1065099 := bstep (se 1 (by rfl) ⟨798824, by rfl⟩ : syracuseStep 1065099 = 1597649) B1597649
theorem B1065111 : Blo 1064615 1065111 := bstep (se 1 (by rfl) ⟨798833, by rfl⟩ : syracuseStep 1065111 = 1597667) B1597667
theorem B1065131 : Blo 1064615 1065131 := bstep (se 1 (by rfl) ⟨798848, by rfl⟩ : syracuseStep 1065131 = 1597697) B1597697
theorem B1065143 : Blo 1064615 1065143 := bstep (se 1 (by rfl) ⟨798857, by rfl⟩ : syracuseStep 1065143 = 1597715) B1597715
theorem B1065163 : Blo 1064615 1065163 := bstep (se 1 (by rfl) ⟨798872, by rfl⟩ : syracuseStep 1065163 = 1597745) B1597745
theorem B1065175 : Blo 1064615 1065175 := bstep (se 1 (by rfl) ⟨798881, by rfl⟩ : syracuseStep 1065175 = 1597763) B1597763
theorem B2703577 : Blo 1064615 2703577 := bstep (se 2 (by rfl) ⟨1013841, by rfl⟩ : syracuseStep 2703577 = 2027683) B2027683
theorem B1065195 : Blo 1064615 1065195 := bstep (se 1 (by rfl) ⟨798896, by rfl⟩ : syracuseStep 1065195 = 1597793) B1597793
theorem B1065207 : Blo 1064615 1065207 := bstep (se 1 (by rfl) ⟨798905, by rfl⟩ : syracuseStep 1065207 = 1597811) B1597811
theorem B1065227 : Blo 1064615 1065227 := bstep (se 1 (by rfl) ⟨798920, by rfl⟩ : syracuseStep 1065227 = 1597841) B1597841
theorem B1065239 : Blo 1064615 1065239 := bstep (se 1 (by rfl) ⟨798929, by rfl⟩ : syracuseStep 1065239 = 1597859) B1597859
theorem B1065259 : Blo 1064615 1065259 := bstep (se 1 (by rfl) ⟨798944, by rfl⟩ : syracuseStep 1065259 = 1597889) B1597889
theorem B3948851 : Blo 1064615 3948851 := bstep (se 1 (by rfl) ⟨2961638, by rfl⟩ : syracuseStep 3948851 = 5923277) B5923277
theorem B1065271 : Blo 1064615 1065271 := bstep (se 1 (by rfl) ⟨798953, by rfl⟩ : syracuseStep 1065271 = 1597907) B1597907
theorem B1065291 : Blo 1064615 1065291 := bstep (se 1 (by rfl) ⟨798968, by rfl⟩ : syracuseStep 1065291 = 1597937) B1597937
theorem B1065303 : Blo 1064615 1065303 := bstep (se 1 (by rfl) ⟨798977, by rfl⟩ : syracuseStep 1065303 = 1597955) B1597955
theorem B1065323 : Blo 1064615 1065323 := bstep (se 1 (by rfl) ⟨798992, by rfl⟩ : syracuseStep 1065323 = 1597985) B1597985
theorem B1065335 : Blo 1064615 1065335 := bstep (se 1 (by rfl) ⟨799001, by rfl⟩ : syracuseStep 1065335 = 1598003) B1598003
theorem B1065355 : Blo 1064615 1065355 := bstep (se 1 (by rfl) ⟨799016, by rfl⟩ : syracuseStep 1065355 = 1598033) B1598033
theorem B1065367 : Blo 1064615 1065367 := bstep (se 1 (by rfl) ⟨799025, by rfl⟩ : syracuseStep 1065367 = 1598051) B1598051
theorem B1065387 : Blo 1064615 1065387 := bstep (se 1 (by rfl) ⟨799040, by rfl⟩ : syracuseStep 1065387 = 1598081) B1598081
theorem B1065399 : Blo 1064615 1065399 := bstep (se 1 (by rfl) ⟨799049, by rfl⟩ : syracuseStep 1065399 = 1598099) B1598099
theorem B1065419 : Blo 1064615 1065419 := bstep (se 1 (by rfl) ⟨799064, by rfl⟩ : syracuseStep 1065419 = 1598129) B1598129
theorem B1065431 : Blo 1064615 1065431 := bstep (se 1 (by rfl) ⟨799073, by rfl⟩ : syracuseStep 1065431 = 1598147) B1598147
theorem B1065451 : Blo 1064615 1065451 := bstep (se 1 (by rfl) ⟨799088, by rfl⟩ : syracuseStep 1065451 = 1598177) B1598177
theorem B1065463 : Blo 1064615 1065463 := bstep (se 1 (by rfl) ⟨799097, by rfl⟩ : syracuseStep 1065463 = 1598195) B1598195
theorem B1065483 : Blo 1064615 1065483 := bstep (se 1 (by rfl) ⟨799112, by rfl⟩ : syracuseStep 1065483 = 1598225) B1598225
theorem B1065495 : Blo 1064615 1065495 := bstep (se 1 (by rfl) ⟨799121, by rfl⟩ : syracuseStep 1065495 = 1598243) B1598243
theorem B1065515 : Blo 1064615 1065515 := bstep (se 1 (by rfl) ⟨799136, by rfl⟩ : syracuseStep 1065515 = 1598273) B1598273
theorem B1065527 : Blo 1064615 1065527 := bstep (se 1 (by rfl) ⟨799145, by rfl⟩ : syracuseStep 1065527 = 1598291) B1598291
theorem B1065547 : Blo 1064615 1065547 := bstep (se 1 (by rfl) ⟨799160, by rfl⟩ : syracuseStep 1065547 = 1598321) B1598321
theorem B1065559 : Blo 1064615 1065559 := bstep (se 1 (by rfl) ⟨799169, by rfl⟩ : syracuseStep 1065559 = 1598339) B1598339
theorem B1065579 : Blo 1064615 1065579 := bstep (se 1 (by rfl) ⟨799184, by rfl⟩ : syracuseStep 1065579 = 1598369) B1598369
theorem B1065591 : Blo 1064615 1065591 := bstep (se 1 (by rfl) ⟨799193, by rfl⟩ : syracuseStep 1065591 = 1598387) B1598387
theorem B1065611 : Blo 1064615 1065611 := bstep (se 1 (by rfl) ⟨799208, by rfl⟩ : syracuseStep 1065611 = 1598417) B1598417
theorem B1065623 : Blo 1064615 1065623 := bstep (se 1 (by rfl) ⟨799217, by rfl⟩ : syracuseStep 1065623 = 1598435) B1598435
theorem B1065643 : Blo 1064615 1065643 := bstep (se 1 (by rfl) ⟨799232, by rfl⟩ : syracuseStep 1065643 = 1598465) B1598465
theorem B1065655 : Blo 1064615 1065655 := bstep (se 1 (by rfl) ⟨799241, by rfl⟩ : syracuseStep 1065655 = 1598483) B1598483
theorem B1065675 : Blo 1064615 1065675 := bstep (se 1 (by rfl) ⟨799256, by rfl⟩ : syracuseStep 1065675 = 1598513) B1598513
theorem B1065687 : Blo 1064615 1065687 := bstep (se 1 (by rfl) ⟨799265, by rfl⟩ : syracuseStep 1065687 = 1598531) B1598531
theorem B1065707 : Blo 1064615 1065707 := bstep (se 1 (by rfl) ⟨799280, by rfl⟩ : syracuseStep 1065707 = 1598561) B1598561
theorem B1065719 : Blo 1064615 1065719 := bstep (se 1 (by rfl) ⟨799289, by rfl⟩ : syracuseStep 1065719 = 1598579) B1598579
theorem B8110853 : Blo 1064615 8110853 := bstep (se 4 (by rfl) ⟨760392, by rfl⟩ : syracuseStep 8110853 = 1520785) B1520785
theorem B1065739 : Blo 1064615 1065739 := bstep (se 1 (by rfl) ⟨799304, by rfl⟩ : syracuseStep 1065739 = 1598609) B1598609
theorem B1065751 : Blo 1064615 1065751 := bstep (se 1 (by rfl) ⟨799313, by rfl⟩ : syracuseStep 1065751 = 1598627) B1598627
theorem B1065771 : Blo 1064615 1065771 := bstep (se 1 (by rfl) ⟨799328, by rfl⟩ : syracuseStep 1065771 = 1598657) B1598657
theorem B1065783 : Blo 1064615 1065783 := bstep (se 1 (by rfl) ⟨799337, by rfl⟩ : syracuseStep 1065783 = 1598675) B1598675
theorem B1065803 : Blo 1064615 1065803 := bstep (se 1 (by rfl) ⟨799352, by rfl⟩ : syracuseStep 1065803 = 1598705) B1598705
theorem B1065815 : Blo 1064615 1065815 := bstep (se 1 (by rfl) ⟨799361, by rfl⟩ : syracuseStep 1065815 = 1598723) B1598723
theorem B3031901 : Blo 1064615 3031901 := bstep (se 3 (by rfl) ⟨568481, by rfl⟩ : syracuseStep 3031901 = 1136963) B1136963
theorem B5391197 : Blo 1064615 5391197 := bstep (se 3 (by rfl) ⟨1010849, by rfl⟩ : syracuseStep 5391197 = 2021699) B2021699
theorem B1065835 : Blo 1064615 1065835 := bstep (se 1 (by rfl) ⟨799376, by rfl⟩ : syracuseStep 1065835 = 1598753) B1598753
theorem B1065847 : Blo 1064615 1065847 := bstep (se 1 (by rfl) ⟨799385, by rfl⟩ : syracuseStep 1065847 = 1598771) B1598771
theorem B1065867 : Blo 1064615 1065867 := bstep (se 1 (by rfl) ⟨799400, by rfl⟩ : syracuseStep 1065867 = 1598801) B1598801
theorem B1065879 : Blo 1064615 1065879 := bstep (se 1 (by rfl) ⟨799409, by rfl⟩ : syracuseStep 1065879 = 1598819) B1598819
theorem B1065899 : Blo 1064615 1065899 := bstep (se 1 (by rfl) ⟨799424, by rfl⟩ : syracuseStep 1065899 = 1598849) B1598849
theorem B1065911 : Blo 1064615 1065911 := bstep (se 1 (by rfl) ⟨799433, by rfl⟩ : syracuseStep 1065911 = 1598867) B1598867
theorem B1065931 : Blo 1064615 1065931 := bstep (se 1 (by rfl) ⟨799448, by rfl⟩ : syracuseStep 1065931 = 1598897) B1598897
theorem B1065943 : Blo 1064615 1065943 := bstep (se 1 (by rfl) ⟨799457, by rfl⟩ : syracuseStep 1065943 = 1598915) B1598915
theorem B4047833 : Blo 1064615 4047833 := bstep (se 2 (by rfl) ⟨1517937, by rfl⟩ : syracuseStep 4047833 = 3035875) B3035875
theorem B1065963 : Blo 1064615 1065963 := bstep (se 1 (by rfl) ⟨799472, by rfl⟩ : syracuseStep 1065963 = 1598945) B1598945
theorem B1065975 : Blo 1064615 1065975 := bstep (se 1 (by rfl) ⟨799481, by rfl⟩ : syracuseStep 1065975 = 1598963) B1598963
theorem B1065995 : Blo 1064615 1065995 := bstep (se 1 (by rfl) ⟨799496, by rfl⟩ : syracuseStep 1065995 = 1598993) B1598993
theorem B1066007 : Blo 1064615 1066007 := bstep (se 1 (by rfl) ⟨799505, by rfl⟩ : syracuseStep 1066007 = 1599011) B1599011
theorem B13648931 : Blo 1064615 13648931 := bstep (se 1 (by rfl) ⟨10236698, by rfl⟩ : syracuseStep 13648931 = 20473397) B20473397
theorem B1066027 : Blo 1064615 1066027 := bstep (se 1 (by rfl) ⟨799520, by rfl⟩ : syracuseStep 1066027 = 1599041) B1599041
theorem B1066039 : Blo 1064615 1066039 := bstep (se 1 (by rfl) ⟨799529, by rfl⟩ : syracuseStep 1066039 = 1599059) B1599059
theorem B1066059 : Blo 1064615 1066059 := bstep (se 1 (by rfl) ⟨799544, by rfl⟩ : syracuseStep 1066059 = 1599089) B1599089
theorem B1066071 : Blo 1064615 1066071 := bstep (se 1 (by rfl) ⟨799553, by rfl⟩ : syracuseStep 1066071 = 1599107) B1599107
theorem B1066091 : Blo 1064615 1066091 := bstep (se 1 (by rfl) ⟨799568, by rfl⟩ : syracuseStep 1066091 = 1599137) B1599137
theorem B1066103 : Blo 1064615 1066103 := bstep (se 1 (by rfl) ⟨799577, by rfl⟩ : syracuseStep 1066103 = 1599155) B1599155
theorem B1066123 : Blo 1064615 1066123 := bstep (se 1 (by rfl) ⟨799592, by rfl⟩ : syracuseStep 1066123 = 1599185) B1599185
theorem B1066135 : Blo 1064615 1066135 := bstep (se 1 (by rfl) ⟨799601, by rfl⟩ : syracuseStep 1066135 = 1599203) B1599203
theorem B1066155 : Blo 1064615 1066155 := bstep (se 1 (by rfl) ⟨799616, by rfl⟩ : syracuseStep 1066155 = 1599233) B1599233
theorem B1066167 : Blo 1064615 1066167 := bstep (se 1 (by rfl) ⟨799625, by rfl⟩ : syracuseStep 1066167 = 1599251) B1599251
theorem B1066187 : Blo 1064615 1066187 := bstep (se 1 (by rfl) ⟨799640, by rfl⟩ : syracuseStep 1066187 = 1599281) B1599281
theorem B1066199 : Blo 1064615 1066199 := bstep (se 1 (by rfl) ⟨799649, by rfl⟩ : syracuseStep 1066199 = 1599299) B1599299
theorem B1066219 : Blo 1064615 1066219 := bstep (se 1 (by rfl) ⟨799664, by rfl⟩ : syracuseStep 1066219 = 1599329) B1599329
theorem B1066231 : Blo 1064615 1066231 := bstep (se 1 (by rfl) ⟨799673, by rfl⟩ : syracuseStep 1066231 = 1599347) B1599347
theorem B1066251 : Blo 1064615 1066251 := bstep (se 1 (by rfl) ⟨799688, by rfl⟩ : syracuseStep 1066251 = 1599377) B1599377
theorem B2278667 : Blo 1064615 2278667 := bstep (se 1 (by rfl) ⟨1709000, by rfl⟩ : syracuseStep 2278667 = 3418001) B3418001
theorem B1066263 : Blo 1064615 1066263 := bstep (se 1 (by rfl) ⟨799697, by rfl⟩ : syracuseStep 1066263 = 1599395) B1599395
theorem B1066283 : Blo 1064615 1066283 := bstep (se 1 (by rfl) ⟨799712, by rfl⟩ : syracuseStep 1066283 = 1599425) B1599425
theorem B2704691 : Blo 1064615 2704691 := bstep (se 1 (by rfl) ⟨2028518, by rfl⟩ : syracuseStep 2704691 = 4057037) B4057037
theorem B1066295 : Blo 1064615 1066295 := bstep (se 1 (by rfl) ⟨799721, by rfl⟩ : syracuseStep 1066295 = 1599443) B1599443
theorem B1066315 : Blo 1064615 1066315 := bstep (se 1 (by rfl) ⟨799736, by rfl⟩ : syracuseStep 1066315 = 1599473) B1599473
theorem B1066327 : Blo 1064615 1066327 := bstep (se 1 (by rfl) ⟨799745, by rfl⟩ : syracuseStep 1066327 = 1599491) B1599491
theorem B1066347 : Blo 1064615 1066347 := bstep (se 1 (by rfl) ⟨799760, by rfl⟩ : syracuseStep 1066347 = 1599521) B1599521
theorem B1066359 : Blo 1064615 1066359 := bstep (se 1 (by rfl) ⟨799769, by rfl⟩ : syracuseStep 1066359 = 1599539) B1599539
theorem B1066379 : Blo 1064615 1066379 := bstep (se 1 (by rfl) ⟨799784, by rfl⟩ : syracuseStep 1066379 = 1599569) B1599569
theorem B1066391 : Blo 1064615 1066391 := bstep (se 1 (by rfl) ⟨799793, by rfl⟩ : syracuseStep 1066391 = 1599587) B1599587
theorem B1066411 : Blo 1064615 1066411 := bstep (se 1 (by rfl) ⟨799808, by rfl⟩ : syracuseStep 1066411 = 1599617) B1599617
theorem B1066423 : Blo 1064615 1066423 := bstep (se 1 (by rfl) ⟨799817, by rfl⟩ : syracuseStep 1066423 = 1599635) B1599635
theorem B1066443 : Blo 1064615 1066443 := bstep (se 1 (by rfl) ⟨799832, by rfl⟩ : syracuseStep 1066443 = 1599665) B1599665
theorem B1066455 : Blo 1064615 1066455 := bstep (se 1 (by rfl) ⟨799841, by rfl⟩ : syracuseStep 1066455 = 1599683) B1599683
theorem B1066475 : Blo 1064615 1066475 := bstep (se 1 (by rfl) ⟨799856, by rfl⟩ : syracuseStep 1066475 = 1599713) B1599713
theorem B1066487 : Blo 1064615 1066487 := bstep (se 1 (by rfl) ⟨799865, by rfl⟩ : syracuseStep 1066487 = 1599731) B1599731
theorem B1066507 : Blo 1064615 1066507 := bstep (se 1 (by rfl) ⟨799880, by rfl⟩ : syracuseStep 1066507 = 1599761) B1599761
theorem B1066519 : Blo 1064615 1066519 := bstep (se 1 (by rfl) ⟨799889, by rfl⟩ : syracuseStep 1066519 = 1599779) B1599779
theorem B1066539 : Blo 1064615 1066539 := bstep (se 1 (by rfl) ⟨799904, by rfl⟩ : syracuseStep 1066539 = 1599809) B1599809
theorem B1066551 : Blo 1064615 1066551 := bstep (se 1 (by rfl) ⟨799913, by rfl⟩ : syracuseStep 1066551 = 1599827) B1599827
theorem B1066571 : Blo 1064615 1066571 := bstep (se 1 (by rfl) ⟨799928, by rfl⟩ : syracuseStep 1066571 = 1599857) B1599857
theorem B1066583 : Blo 1064615 1066583 := bstep (se 1 (by rfl) ⟨799937, by rfl⟩ : syracuseStep 1066583 = 1599875) B1599875
theorem B1066603 : Blo 1064615 1066603 := bstep (se 1 (by rfl) ⟨799952, by rfl⟩ : syracuseStep 1066603 = 1599905) B1599905
theorem B1066615 : Blo 1064615 1066615 := bstep (se 1 (by rfl) ⟨799961, by rfl⟩ : syracuseStep 1066615 = 1599923) B1599923
theorem B1918603 : Blo 1064615 1918603 := bstep (se 1 (by rfl) ⟨1438952, by rfl⟩ : syracuseStep 1918603 = 2877905) B2877905
theorem B1066635 : Blo 1064615 1066635 := bstep (se 1 (by rfl) ⟨799976, by rfl⟩ : syracuseStep 1066635 = 1599953) B1599953
theorem B1066647 : Blo 1064615 1066647 := bstep (se 1 (by rfl) ⟨799985, by rfl⟩ : syracuseStep 1066647 = 1599971) B1599971
theorem B1066667 : Blo 1064615 1066667 := bstep (se 1 (by rfl) ⟨800000, by rfl⟩ : syracuseStep 1066667 = 1600001) B1600001
theorem B1197751 : Blo 1064615 1197751 := bstep (se 1 (by rfl) ⟨898313, by rfl⟩ : syracuseStep 1197751 = 1796627) B1796627
theorem B1066679 : Blo 1064615 1066679 := bstep (se 1 (by rfl) ⟨800009, by rfl⟩ : syracuseStep 1066679 = 1600019) B1600019
theorem B1066699 : Blo 1064615 1066699 := bstep (se 1 (by rfl) ⟨800024, by rfl⟩ : syracuseStep 1066699 = 1600049) B1600049
theorem B1066711 : Blo 1064615 1066711 := bstep (se 1 (by rfl) ⟨800033, by rfl⟩ : syracuseStep 1066711 = 1600067) B1600067
theorem B1066731 : Blo 1064615 1066731 := bstep (se 1 (by rfl) ⟨800048, by rfl⟩ : syracuseStep 1066731 = 1600097) B1600097
theorem B1066743 : Blo 1064615 1066743 := bstep (se 1 (by rfl) ⟨800057, by rfl⟩ : syracuseStep 1066743 = 1600115) B1600115
theorem B1066763 : Blo 1064615 1066763 := bstep (se 1 (by rfl) ⟨800072, by rfl⟩ : syracuseStep 1066763 = 1600145) B1600145
theorem B1066775 : Blo 1064615 1066775 := bstep (se 1 (by rfl) ⟨800081, by rfl⟩ : syracuseStep 1066775 = 1600163) B1600163
theorem B1066795 : Blo 1064615 1066795 := bstep (se 1 (by rfl) ⟨800096, by rfl⟩ : syracuseStep 1066795 = 1600193) B1600193
theorem B1066807 : Blo 1064615 1066807 := bstep (se 1 (by rfl) ⟨800105, by rfl⟩ : syracuseStep 1066807 = 1600211) B1600211
theorem B1066827 : Blo 1064615 1066827 := bstep (se 1 (by rfl) ⟨800120, by rfl⟩ : syracuseStep 1066827 = 1600241) B1600241
theorem B1066839 : Blo 1064615 1066839 := bstep (se 1 (by rfl) ⟨800129, by rfl⟩ : syracuseStep 1066839 = 1600259) B1600259
theorem B13846373 : Blo 1064615 13846373 := bstep (se 4 (by rfl) ⟨1298097, by rfl⟩ : syracuseStep 13846373 = 2596195) B2596195
theorem B1197931 : Blo 1064615 1197931 := bstep (se 1 (by rfl) ⟨898448, by rfl⟩ : syracuseStep 1197931 = 1796897) B1796897
theorem B1066859 : Blo 1064615 1066859 := bstep (se 1 (by rfl) ⟨800144, by rfl⟩ : syracuseStep 1066859 = 1600289) B1600289
theorem B1066871 : Blo 1064615 1066871 := bstep (se 1 (by rfl) ⟨800153, by rfl⟩ : syracuseStep 1066871 = 1600307) B1600307
theorem B1066891 : Blo 1064615 1066891 := bstep (se 1 (by rfl) ⟨800168, by rfl⟩ : syracuseStep 1066891 = 1600337) B1600337
theorem B1066903 : Blo 1064615 1066903 := bstep (se 1 (by rfl) ⟨800177, by rfl⟩ : syracuseStep 1066903 = 1600355) B1600355
theorem B1066923 : Blo 1064615 1066923 := bstep (se 1 (by rfl) ⟨800192, by rfl⟩ : syracuseStep 1066923 = 1600385) B1600385
theorem B11519921 : Blo 1064615 11519921 := bstep (se 2 (by rfl) ⟨4319970, by rfl⟩ : syracuseStep 11519921 = 8639941) B8639941
theorem B1066935 : Blo 1064615 1066935 := bstep (se 1 (by rfl) ⟨800201, by rfl⟩ : syracuseStep 1066935 = 1600403) B1600403
theorem B2312129 : Blo 1064615 2312129 := bstep (se 2 (by rfl) ⟨867048, by rfl⟩ : syracuseStep 2312129 = 1734097) B1734097
theorem B1066955 : Blo 1064615 1066955 := bstep (se 1 (by rfl) ⟨800216, by rfl⟩ : syracuseStep 1066955 = 1600433) B1600433
theorem B1198039 : Blo 1064615 1198039 := bstep (se 1 (by rfl) ⟨898529, by rfl⟩ : syracuseStep 1198039 = 1797059) B1797059
theorem B1066967 : Blo 1064615 1066967 := bstep (se 1 (by rfl) ⟨800225, by rfl⟩ : syracuseStep 1066967 = 1600451) B1600451
theorem B1066987 : Blo 1064615 1066987 := bstep (se 1 (by rfl) ⟨800240, by rfl⟩ : syracuseStep 1066987 = 1600481) B1600481
theorem B1066999 : Blo 1064615 1066999 := bstep (se 1 (by rfl) ⟨800249, by rfl⟩ : syracuseStep 1066999 = 1600499) B1600499
theorem B1067019 : Blo 1064615 1067019 := bstep (se 1 (by rfl) ⟨800264, by rfl⟩ : syracuseStep 1067019 = 1600529) B1600529
theorem B1067031 : Blo 1064615 1067031 := bstep (se 1 (by rfl) ⟨800273, by rfl⟩ : syracuseStep 1067031 = 1600547) B1600547
theorem B1067051 : Blo 1064615 1067051 := bstep (se 1 (by rfl) ⟨800288, by rfl⟩ : syracuseStep 1067051 = 1600577) B1600577
theorem B1067063 : Blo 1064615 1067063 := bstep (se 1 (by rfl) ⟨800297, by rfl⟩ : syracuseStep 1067063 = 1600595) B1600595
theorem B1067083 : Blo 1064615 1067083 := bstep (se 1 (by rfl) ⟨800312, by rfl⟩ : syracuseStep 1067083 = 1600625) B1600625
theorem B1067095 : Blo 1064615 1067095 := bstep (se 1 (by rfl) ⟨800321, by rfl⟩ : syracuseStep 1067095 = 1600643) B1600643
theorem B1919065 : Blo 1064615 1919065 := bstep (se 2 (by rfl) ⟨719649, by rfl⟩ : syracuseStep 1919065 = 1439299) B1439299
theorem B1067115 : Blo 1064615 1067115 := bstep (se 1 (by rfl) ⟨800336, by rfl⟩ : syracuseStep 1067115 = 1600673) B1600673
theorem B1067127 : Blo 1064615 1067127 := bstep (se 1 (by rfl) ⟨800345, by rfl⟩ : syracuseStep 1067127 = 1600691) B1600691
theorem B6834307 : Blo 1064615 6834307 := bstep (se 1 (by rfl) ⟨5125730, by rfl⟩ : syracuseStep 6834307 = 10251461) B10251461
theorem B1198219 : Blo 1064615 1198219 := bstep (se 1 (by rfl) ⟨898664, by rfl⟩ : syracuseStep 1198219 = 1797329) B1797329
theorem B1067147 : Blo 1064615 1067147 := bstep (se 1 (by rfl) ⟨800360, by rfl⟩ : syracuseStep 1067147 = 1600721) B1600721
theorem B1067159 : Blo 1064615 1067159 := bstep (se 1 (by rfl) ⟨800369, by rfl⟩ : syracuseStep 1067159 = 1600739) B1600739
theorem B1067179 : Blo 1064615 1067179 := bstep (se 1 (by rfl) ⟨800384, by rfl⟩ : syracuseStep 1067179 = 1600769) B1600769
theorem B1067191 : Blo 1064615 1067191 := bstep (se 1 (by rfl) ⟨800393, by rfl⟩ : syracuseStep 1067191 = 1600787) B1600787
theorem B1067211 : Blo 1064615 1067211 := bstep (se 1 (by rfl) ⟨800408, by rfl⟩ : syracuseStep 1067211 = 1600817) B1600817
theorem B1067223 : Blo 1064615 1067223 := bstep (se 1 (by rfl) ⟨800417, by rfl⟩ : syracuseStep 1067223 = 1600835) B1600835
theorem B1067243 : Blo 1064615 1067243 := bstep (se 1 (by rfl) ⟨800432, by rfl⟩ : syracuseStep 1067243 = 1600865) B1600865
theorem B1198327 : Blo 1064615 1198327 := bstep (se 1 (by rfl) ⟨898745, by rfl⟩ : syracuseStep 1198327 = 1797491) B1797491
theorem B1067255 : Blo 1064615 1067255 := bstep (se 1 (by rfl) ⟨800441, by rfl⟩ : syracuseStep 1067255 = 1600883) B1600883
theorem B1067275 : Blo 1064615 1067275 := bstep (se 1 (by rfl) ⟨800456, by rfl⟩ : syracuseStep 1067275 = 1600913) B1600913
theorem B1067287 : Blo 1064615 1067287 := bstep (se 1 (by rfl) ⟨800465, by rfl⟩ : syracuseStep 1067287 = 1600931) B1600931
theorem B1067307 : Blo 1064615 1067307 := bstep (se 1 (by rfl) ⟨800480, by rfl⟩ : syracuseStep 1067307 = 1600961) B1600961
theorem B1067319 : Blo 1064615 1067319 := bstep (se 1 (by rfl) ⟨800489, by rfl⟩ : syracuseStep 1067319 = 1600979) B1600979
theorem B1067339 : Blo 1064615 1067339 := bstep (se 1 (by rfl) ⟨800504, by rfl⟩ : syracuseStep 1067339 = 1601009) B1601009
theorem B1067351 : Blo 1064615 1067351 := bstep (se 1 (by rfl) ⟨800513, by rfl⟩ : syracuseStep 1067351 = 1601027) B1601027
theorem B1067371 : Blo 1064615 1067371 := bstep (se 1 (by rfl) ⟨800528, by rfl⟩ : syracuseStep 1067371 = 1601057) B1601057
theorem B1067383 : Blo 1064615 1067383 := bstep (se 1 (by rfl) ⟨800537, by rfl⟩ : syracuseStep 1067383 = 1601075) B1601075
theorem B1067403 : Blo 1064615 1067403 := bstep (se 1 (by rfl) ⟨800552, by rfl⟩ : syracuseStep 1067403 = 1601105) B1601105
theorem B1067415 : Blo 1064615 1067415 := bstep (se 1 (by rfl) ⟨800561, by rfl⟩ : syracuseStep 1067415 = 1601123) B1601123
theorem B1198507 : Blo 1064615 1198507 := bstep (se 1 (by rfl) ⟨898880, by rfl⟩ : syracuseStep 1198507 = 1797761) B1797761
theorem B1067435 : Blo 1064615 1067435 := bstep (se 1 (by rfl) ⟨800576, by rfl⟩ : syracuseStep 1067435 = 1601153) B1601153
theorem B4377005 : Blo 1064615 4377005 := bstep (se 3 (by rfl) ⟨820688, by rfl⟩ : syracuseStep 4377005 = 1641377) B1641377
theorem B1067447 : Blo 1064615 1067447 := bstep (se 1 (by rfl) ⟨800585, by rfl⟩ : syracuseStep 1067447 = 1601171) B1601171
theorem B4868545 : Blo 1064615 4868545 := bstep (se 2 (by rfl) ⟨1825704, by rfl⟩ : syracuseStep 4868545 = 3651409) B3651409
theorem B1067467 : Blo 1064615 1067467 := bstep (se 1 (by rfl) ⟨800600, by rfl⟩ : syracuseStep 1067467 = 1601201) B1601201
theorem B1067479 : Blo 1064615 1067479 := bstep (se 1 (by rfl) ⟨800609, by rfl⟩ : syracuseStep 1067479 = 1601219) B1601219
theorem B2279897 : Blo 1064615 2279897 := bstep (se 2 (by rfl) ⟨854961, by rfl⟩ : syracuseStep 2279897 = 1709923) B1709923
theorem B1067499 : Blo 1064615 1067499 := bstep (se 1 (by rfl) ⟨800624, by rfl⟩ : syracuseStep 1067499 = 1601249) B1601249
theorem B1067511 : Blo 1064615 1067511 := bstep (se 1 (by rfl) ⟨800633, by rfl⟩ : syracuseStep 1067511 = 1601267) B1601267
theorem B1067531 : Blo 1064615 1067531 := bstep (se 1 (by rfl) ⟨800648, by rfl⟩ : syracuseStep 1067531 = 1601297) B1601297
theorem B1198615 : Blo 1064615 1198615 := bstep (se 1 (by rfl) ⟨898961, by rfl⟩ : syracuseStep 1198615 = 1797923) B1797923
theorem B1067543 : Blo 1064615 1067543 := bstep (se 1 (by rfl) ⟨800657, by rfl⟩ : syracuseStep 1067543 = 1601315) B1601315
theorem B1067563 : Blo 1064615 1067563 := bstep (se 1 (by rfl) ⟨800672, by rfl⟩ : syracuseStep 1067563 = 1601345) B1601345
theorem B4934189 : Blo 1064615 4934189 := bstep (se 3 (by rfl) ⟨925160, by rfl⟩ : syracuseStep 4934189 = 1850321) B1850321
theorem B4049459 : Blo 1064615 4049459 := bstep (se 1 (by rfl) ⟨3037094, by rfl⟩ : syracuseStep 4049459 = 6074189) B6074189
theorem B1067575 : Blo 1064615 1067575 := bstep (se 1 (by rfl) ⟨800681, by rfl⟩ : syracuseStep 1067575 = 1601363) B1601363
theorem B4049473 : Blo 1064615 4049473 := bstep (se 2 (by rfl) ⟨1518552, by rfl⟩ : syracuseStep 4049473 = 3037105) B3037105
theorem B1067595 : Blo 1064615 1067595 := bstep (se 1 (by rfl) ⟨800696, by rfl⟩ : syracuseStep 1067595 = 1601393) B1601393
theorem B1067607 : Blo 1064615 1067607 := bstep (se 1 (by rfl) ⟨800705, by rfl⟩ : syracuseStep 1067607 = 1601411) B1601411
theorem B1067627 : Blo 1064615 1067627 := bstep (se 1 (by rfl) ⟨800720, by rfl⟩ : syracuseStep 1067627 = 1601441) B1601441
theorem B1067639 : Blo 1064615 1067639 := bstep (se 1 (by rfl) ⟨800729, by rfl⟩ : syracuseStep 1067639 = 1601459) B1601459
theorem B1067659 : Blo 1064615 1067659 := bstep (se 1 (by rfl) ⟨800744, by rfl⟩ : syracuseStep 1067659 = 1601489) B1601489
theorem B1067671 : Blo 1064615 1067671 := bstep (se 1 (by rfl) ⟨800753, by rfl⟩ : syracuseStep 1067671 = 1601507) B1601507
theorem B1067691 : Blo 1064615 1067691 := bstep (se 1 (by rfl) ⟨800768, by rfl⟩ : syracuseStep 1067691 = 1601537) B1601537
theorem B1067703 : Blo 1064615 1067703 := bstep (se 1 (by rfl) ⟨800777, by rfl⟩ : syracuseStep 1067703 = 1601555) B1601555
theorem B1198795 : Blo 1064615 1198795 := bstep (se 1 (by rfl) ⟨899096, by rfl⟩ : syracuseStep 1198795 = 1798193) B1798193
theorem B1067723 : Blo 1064615 1067723 := bstep (se 1 (by rfl) ⟨800792, by rfl⟩ : syracuseStep 1067723 = 1601585) B1601585
theorem B1067735 : Blo 1064615 1067735 := bstep (se 1 (by rfl) ⟨800801, by rfl⟩ : syracuseStep 1067735 = 1601603) B1601603
theorem B1067755 : Blo 1064615 1067755 := bstep (se 1 (by rfl) ⟨800816, by rfl⟩ : syracuseStep 1067755 = 1601633) B1601633
theorem B1067767 : Blo 1064615 1067767 := bstep (se 1 (by rfl) ⟨800825, by rfl⟩ : syracuseStep 1067767 = 1601651) B1601651
theorem B1067787 : Blo 1064615 1067787 := bstep (se 1 (by rfl) ⟨800840, by rfl⟩ : syracuseStep 1067787 = 1601681) B1601681
theorem B1067799 : Blo 1064615 1067799 := bstep (se 1 (by rfl) ⟨800849, by rfl⟩ : syracuseStep 1067799 = 1601699) B1601699
theorem B1067819 : Blo 1064615 1067819 := bstep (se 1 (by rfl) ⟨800864, by rfl⟩ : syracuseStep 1067819 = 1601729) B1601729
theorem B1198903 : Blo 1064615 1198903 := bstep (se 1 (by rfl) ⟨899177, by rfl⟩ : syracuseStep 1198903 = 1798355) B1798355
theorem B1067831 : Blo 1064615 1067831 := bstep (se 1 (by rfl) ⟨800873, by rfl⟩ : syracuseStep 1067831 = 1601747) B1601747
theorem B1067851 : Blo 1064615 1067851 := bstep (se 1 (by rfl) ⟨800888, by rfl⟩ : syracuseStep 1067851 = 1601777) B1601777
theorem B1067863 : Blo 1064615 1067863 := bstep (se 1 (by rfl) ⟨800897, by rfl⟩ : syracuseStep 1067863 = 1601795) B1601795
theorem B1067883 : Blo 1064615 1067883 := bstep (se 1 (by rfl) ⟨800912, by rfl⟩ : syracuseStep 1067883 = 1601825) B1601825
theorem B2280307 : Blo 1064615 2280307 := bstep (se 1 (by rfl) ⟨1710230, by rfl⟩ : syracuseStep 2280307 = 3420461) B3420461
theorem B1067895 : Blo 1064615 1067895 := bstep (se 1 (by rfl) ⟨800921, by rfl⟩ : syracuseStep 1067895 = 1601843) B1601843
theorem B1067915 : Blo 1064615 1067915 := bstep (se 1 (by rfl) ⟨800936, by rfl⟩ : syracuseStep 1067915 = 1601873) B1601873
theorem B5393303 : Blo 1064615 5393303 := bstep (se 1 (by rfl) ⟨4044977, by rfl⟩ : syracuseStep 5393303 = 8089955) B8089955
theorem B3034007 : Blo 1064615 3034007 := bstep (se 1 (by rfl) ⟨2275505, by rfl⟩ : syracuseStep 3034007 = 4551011) B4551011
theorem B1067927 : Blo 1064615 1067927 := bstep (se 1 (by rfl) ⟨800945, by rfl⟩ : syracuseStep 1067927 = 1601891) B1601891
theorem B1067947 : Blo 1064615 1067947 := bstep (se 1 (by rfl) ⟨800960, by rfl⟩ : syracuseStep 1067947 = 1601921) B1601921
theorem B1067959 : Blo 1064615 1067959 := bstep (se 1 (by rfl) ⟨800969, by rfl⟩ : syracuseStep 1067959 = 1601939) B1601939
theorem B1067979 : Blo 1064615 1067979 := bstep (se 1 (by rfl) ⟨800984, by rfl⟩ : syracuseStep 1067979 = 1601969) B1601969
theorem B1067991 : Blo 1064615 1067991 := bstep (se 1 (by rfl) ⟨800993, by rfl⟩ : syracuseStep 1067991 = 1601987) B1601987
theorem B1199083 : Blo 1064615 1199083 := bstep (se 1 (by rfl) ⟨899312, by rfl⟩ : syracuseStep 1199083 = 1798625) B1798625
theorem B1068011 : Blo 1064615 1068011 := bstep (se 1 (by rfl) ⟨801008, by rfl⟩ : syracuseStep 1068011 = 1602017) B1602017
theorem B1068023 : Blo 1064615 1068023 := bstep (se 1 (by rfl) ⟨801017, by rfl⟩ : syracuseStep 1068023 = 1602035) B1602035
theorem B1068043 : Blo 1064615 1068043 := bstep (se 1 (by rfl) ⟨801032, by rfl⟩ : syracuseStep 1068043 = 1602065) B1602065
theorem B1068055 : Blo 1064615 1068055 := bstep (se 1 (by rfl) ⟨801041, by rfl⟩ : syracuseStep 1068055 = 1602083) B1602083
theorem B1068075 : Blo 1064615 1068075 := bstep (se 1 (by rfl) ⟨801056, by rfl⟩ : syracuseStep 1068075 = 1602113) B1602113
theorem B1068087 : Blo 1064615 1068087 := bstep (se 1 (by rfl) ⟨801065, by rfl⟩ : syracuseStep 1068087 = 1602131) B1602131
theorem B1068107 : Blo 1064615 1068107 := bstep (se 1 (by rfl) ⟨801080, by rfl⟩ : syracuseStep 1068107 = 1602161) B1602161
theorem B1199191 : Blo 1064615 1199191 := bstep (se 1 (by rfl) ⟨899393, by rfl⟩ : syracuseStep 1199191 = 1798787) B1798787
theorem B1068119 : Blo 1064615 1068119 := bstep (se 1 (by rfl) ⟨801089, by rfl⟩ : syracuseStep 1068119 = 1602179) B1602179
theorem B1068139 : Blo 1064615 1068139 := bstep (se 1 (by rfl) ⟨801104, by rfl⟩ : syracuseStep 1068139 = 1602209) B1602209
theorem B2280563 : Blo 1064615 2280563 := bstep (se 1 (by rfl) ⟨1710422, by rfl⟩ : syracuseStep 2280563 = 3420845) B3420845
theorem B1068151 : Blo 1064615 1068151 := bstep (se 1 (by rfl) ⟨801113, by rfl⟩ : syracuseStep 1068151 = 1602227) B1602227
theorem B8113283 : Blo 1064615 8113283 := bstep (se 1 (by rfl) ⟨6084962, by rfl⟩ : syracuseStep 8113283 = 12169925) B12169925
theorem B1068171 : Blo 1064615 1068171 := bstep (se 1 (by rfl) ⟨801128, by rfl⟩ : syracuseStep 1068171 = 1602257) B1602257
theorem B1068183 : Blo 1064615 1068183 := bstep (se 1 (by rfl) ⟨801137, by rfl⟩ : syracuseStep 1068183 = 1602275) B1602275
theorem B1068203 : Blo 1064615 1068203 := bstep (se 1 (by rfl) ⟨801152, by rfl⟩ : syracuseStep 1068203 = 1602305) B1602305
theorem B1068215 : Blo 1064615 1068215 := bstep (se 1 (by rfl) ⟨801161, by rfl⟩ : syracuseStep 1068215 = 1602323) B1602323
theorem B1068235 : Blo 1064615 1068235 := bstep (se 1 (by rfl) ⟨801176, by rfl⟩ : syracuseStep 1068235 = 1602353) B1602353
theorem B1068247 : Blo 1064615 1068247 := bstep (se 1 (by rfl) ⟨801185, by rfl⟩ : syracuseStep 1068247 = 1602371) B1602371
theorem B1068267 : Blo 1064615 1068267 := bstep (se 1 (by rfl) ⟨801200, by rfl⟩ : syracuseStep 1068267 = 1602401) B1602401
theorem B1068279 : Blo 1064615 1068279 := bstep (se 1 (by rfl) ⟨801209, by rfl⟩ : syracuseStep 1068279 = 1602419) B1602419
theorem B1199371 : Blo 1064615 1199371 := bstep (se 1 (by rfl) ⟨899528, by rfl⟩ : syracuseStep 1199371 = 1799057) B1799057
theorem B1068299 : Blo 1064615 1068299 := bstep (se 1 (by rfl) ⟨801224, by rfl⟩ : syracuseStep 1068299 = 1602449) B1602449
theorem B1068311 : Blo 1064615 1068311 := bstep (se 1 (by rfl) ⟨801233, by rfl⟩ : syracuseStep 1068311 = 1602467) B1602467
theorem B1068331 : Blo 1064615 1068331 := bstep (se 1 (by rfl) ⟨801248, by rfl⟩ : syracuseStep 1068331 = 1602497) B1602497
theorem B1068343 : Blo 1064615 1068343 := bstep (se 1 (by rfl) ⟨801257, by rfl⟩ : syracuseStep 1068343 = 1602515) B1602515
theorem B1068363 : Blo 1064615 1068363 := bstep (se 1 (by rfl) ⟨801272, by rfl⟩ : syracuseStep 1068363 = 1602545) B1602545
theorem B1068375 : Blo 1064615 1068375 := bstep (se 1 (by rfl) ⟨801281, by rfl⟩ : syracuseStep 1068375 = 1602563) B1602563
theorem B5131613 : Blo 1064615 5131613 := bstep (se 3 (by rfl) ⟨962177, by rfl⟩ : syracuseStep 5131613 = 1924355) B1924355
theorem B1068395 : Blo 1064615 1068395 := bstep (se 1 (by rfl) ⟨801296, by rfl⟩ : syracuseStep 1068395 = 1602593) B1602593
theorem B1199479 : Blo 1064615 1199479 := bstep (se 1 (by rfl) ⟨899609, by rfl⟩ : syracuseStep 1199479 = 1799219) B1799219
theorem B1068407 : Blo 1064615 1068407 := bstep (se 1 (by rfl) ⟨801305, by rfl⟩ : syracuseStep 1068407 = 1602611) B1602611
theorem B1068427 : Blo 1064615 1068427 := bstep (se 1 (by rfl) ⟨801320, by rfl⟩ : syracuseStep 1068427 = 1602641) B1602641
theorem B1068439 : Blo 1064615 1068439 := bstep (se 1 (by rfl) ⟨801329, by rfl⟩ : syracuseStep 1068439 = 1602659) B1602659
theorem B1068459 : Blo 1064615 1068459 := bstep (se 1 (by rfl) ⟨801344, by rfl⟩ : syracuseStep 1068459 = 1602689) B1602689
theorem B1068471 : Blo 1064615 1068471 := bstep (se 1 (by rfl) ⟨801353, by rfl⟩ : syracuseStep 1068471 = 1602707) B1602707
theorem B1068491 : Blo 1064615 1068491 := bstep (se 1 (by rfl) ⟨801368, by rfl⟩ : syracuseStep 1068491 = 1602737) B1602737
theorem B1068503 : Blo 1064615 1068503 := bstep (se 1 (by rfl) ⟨801377, by rfl⟩ : syracuseStep 1068503 = 1602755) B1602755
theorem B1068523 : Blo 1064615 1068523 := bstep (se 1 (by rfl) ⟨801392, by rfl⟩ : syracuseStep 1068523 = 1602785) B1602785
theorem B1068535 : Blo 1064615 1068535 := bstep (se 1 (by rfl) ⟨801401, by rfl⟩ : syracuseStep 1068535 = 1602803) B1602803
theorem B1068555 : Blo 1064615 1068555 := bstep (se 1 (by rfl) ⟨801416, by rfl⟩ : syracuseStep 1068555 = 1602833) B1602833
theorem B1068567 : Blo 1064615 1068567 := bstep (se 1 (by rfl) ⟨801425, by rfl⟩ : syracuseStep 1068567 = 1602851) B1602851
theorem B1199659 : Blo 1064615 1199659 := bstep (se 1 (by rfl) ⟨899744, by rfl⟩ : syracuseStep 1199659 = 1799489) B1799489
theorem B1068587 : Blo 1064615 1068587 := bstep (se 1 (by rfl) ⟨801440, by rfl⟩ : syracuseStep 1068587 = 1602881) B1602881
theorem B1068599 : Blo 1064615 1068599 := bstep (se 1 (by rfl) ⟨801449, by rfl⟩ : syracuseStep 1068599 = 1602899) B1602899
theorem B22171229 : Blo 1064615 22171229 := bstep (se 3 (by rfl) ⟨4157105, by rfl⟩ : syracuseStep 22171229 = 8314211) B8314211
theorem B1199767 : Blo 1064615 1199767 := bstep (se 1 (by rfl) ⟨899825, by rfl⟩ : syracuseStep 1199767 = 1799651) B1799651
theorem B3034817 : Blo 1064615 3034817 := bstep (se 2 (by rfl) ⟨1138056, by rfl⟩ : syracuseStep 3034817 = 2276113) B2276113
theorem B1199947 : Blo 1064615 1199947 := bstep (se 1 (by rfl) ⟨899960, by rfl⟩ : syracuseStep 1199947 = 1799921) B1799921
theorem B1200055 : Blo 1064615 1200055 := bstep (se 1 (by rfl) ⟨900041, by rfl⟩ : syracuseStep 1200055 = 1800083) B1800083
theorem B2281537 : Blo 1064615 2281537 := bstep (se 2 (by rfl) ⟨855576, by rfl⟩ : syracuseStep 2281537 = 1711153) B1711153
theorem B1200235 : Blo 1064615 1200235 := bstep (se 1 (by rfl) ⟨900176, by rfl⟩ : syracuseStep 1200235 = 1800353) B1800353
theorem B1200343 : Blo 1064615 1200343 := bstep (se 1 (by rfl) ⟨900257, by rfl⟩ : syracuseStep 1200343 = 1800515) B1800515
theorem B1200523 : Blo 1064615 1200523 := bstep (se 1 (by rfl) ⟨900392, by rfl⟩ : syracuseStep 1200523 = 1800785) B1800785
theorem B4051403 : Blo 1064615 4051403 := bstep (se 1 (by rfl) ⟨3038552, by rfl⟩ : syracuseStep 4051403 = 6077105) B6077105
theorem B4051417 : Blo 1064615 4051417 := bstep (se 2 (by rfl) ⟨1519281, by rfl⟩ : syracuseStep 4051417 = 3038563) B3038563
theorem B1200631 : Blo 1064615 1200631 := bstep (se 1 (by rfl) ⟨900473, by rfl⟩ : syracuseStep 1200631 = 1800947) B1800947
theorem B1200811 : Blo 1064615 1200811 := bstep (se 1 (by rfl) ⟨900608, by rfl⟩ : syracuseStep 1200811 = 1801217) B1801217
theorem B1200919 : Blo 1064615 1200919 := bstep (se 1 (by rfl) ⟨900689, by rfl⟩ : syracuseStep 1200919 = 1801379) B1801379
theorem B6148939 : Blo 1064615 6148939 := bstep (se 1 (by rfl) ⟨4611704, by rfl⟩ : syracuseStep 6148939 = 9223409) B9223409
theorem B1201099 : Blo 1064615 1201099 := bstep (se 1 (by rfl) ⟨900824, by rfl⟩ : syracuseStep 1201099 = 1801649) B1801649
theorem B51958745 : Blo 1064615 51958745 := bstep (se 2 (by rfl) ⟨19484529, by rfl⟩ : syracuseStep 51958745 = 38969059) B38969059
theorem B3593267 : Blo 1064615 3593267 := bstep (se 1 (by rfl) ⟨2694950, by rfl⟩ : syracuseStep 3593267 = 5389901) B5389901
theorem B1201207 : Blo 1064615 1201207 := bstep (se 1 (by rfl) ⟨900905, by rfl⟩ : syracuseStep 1201207 = 1801811) B1801811
theorem B1201387 : Blo 1064615 1201387 := bstep (se 1 (by rfl) ⟨901040, by rfl⟩ : syracuseStep 1201387 = 1802081) B1802081
theorem B3036467 : Blo 1064615 3036467 := bstep (se 1 (by rfl) ⟨2277350, by rfl⟩ : syracuseStep 3036467 = 4554701) B4554701
theorem B3593537 : Blo 1064615 3593537 := bstep (se 2 (by rfl) ⟨1347576, by rfl⟩ : syracuseStep 3593537 = 2695153) B2695153
theorem B3036491 : Blo 1064615 3036491 := bstep (se 1 (by rfl) ⟨2277368, by rfl⟩ : syracuseStep 3036491 = 4554737) B4554737
theorem B1201495 : Blo 1064615 1201495 := bstep (se 1 (by rfl) ⟨901121, by rfl⟩ : syracuseStep 1201495 = 1802243) B1802243
theorem B4052375 : Blo 1064615 4052375 := bstep (se 1 (by rfl) ⟨3039281, by rfl⟩ : syracuseStep 4052375 = 6078563) B6078563
theorem B1201675 : Blo 1064615 1201675 := bstep (se 1 (by rfl) ⟨901256, by rfl⟩ : syracuseStep 1201675 = 1802513) B1802513
theorem B1922611 : Blo 1064615 1922611 := bstep (se 1 (by rfl) ⟨1441958, by rfl⟩ : syracuseStep 1922611 = 2883917) B2883917
theorem B1201783 : Blo 1064615 1201783 := bstep (se 1 (by rfl) ⟨901337, by rfl⟩ : syracuseStep 1201783 = 1802675) B1802675
theorem B2021107 : Blo 1064615 2021107 := bstep (se 1 (by rfl) ⟨1515830, by rfl⟩ : syracuseStep 2021107 = 3031661) B3031661
theorem B9099013 : Blo 1064615 9099013 := bstep (se 4 (by rfl) ⟨853032, by rfl⟩ : syracuseStep 9099013 = 1706065) B1706065
theorem B1824535 : Blo 1064615 1824535 := bstep (se 1 (by rfl) ⟨1368401, by rfl⟩ : syracuseStep 1824535 = 2736803) B2736803
theorem B1201963 : Blo 1064615 1201963 := bstep (se 1 (by rfl) ⟨901472, by rfl⟩ : syracuseStep 1201963 = 1802945) B1802945
theorem B3594077 : Blo 1064615 3594077 := bstep (se 3 (by rfl) ⟨673889, by rfl⟩ : syracuseStep 3594077 = 1347779) B1347779
theorem B1202071 : Blo 1064615 1202071 := bstep (se 1 (by rfl) ⟨901553, by rfl⟩ : syracuseStep 1202071 = 1803107) B1803107
theorem B2054081 : Blo 1064615 2054081 := bstep (se 2 (by rfl) ⟨770280, by rfl⟩ : syracuseStep 2054081 = 1540561) B1540561
theorem B3037277 : Blo 1064615 3037277 := bstep (se 3 (by rfl) ⟨569489, by rfl⟩ : syracuseStep 3037277 = 1138979) B1138979
theorem B2021593 : Blo 1064615 2021593 := bstep (se 2 (by rfl) ⟨758097, by rfl⟩ : syracuseStep 2021593 = 1516195) B1516195
theorem B5396867 : Blo 1064615 5396867 := bstep (se 1 (by rfl) ⟨4047650, by rfl⟩ : syracuseStep 5396867 = 8095301) B8095301
theorem B1137035 : Blo 1064615 1137035 := bstep (se 1 (by rfl) ⟨852776, by rfl⟩ : syracuseStep 1137035 = 1705553) B1705553
theorem B4053635 : Blo 1064615 4053635 := bstep (se 1 (by rfl) ⟨3040226, by rfl⟩ : syracuseStep 4053635 = 6080453) B6080453
theorem B2022155 : Blo 1064615 2022155 := bstep (se 1 (by rfl) ⟨1516616, by rfl⟩ : syracuseStep 2022155 = 3033233) B3033233
theorem B2022337 : Blo 1064615 2022337 := bstep (se 2 (by rfl) ⟨758376, by rfl⟩ : syracuseStep 2022337 = 1516753) B1516753
theorem B3595211 : Blo 1064615 3595211 := bstep (se 1 (by rfl) ⟨2696408, by rfl⟩ : syracuseStep 3595211 = 5392817) B5392817
theorem B2776153 : Blo 1064615 2776153 := bstep (se 2 (by rfl) ⟨1041057, by rfl⟩ : syracuseStep 2776153 = 2082115) B2082115
theorem B8019121 : Blo 1064615 8019121 := bstep (se 2 (by rfl) ⟨3007170, by rfl⟩ : syracuseStep 8019121 = 6014341) B6014341
theorem B3595481 : Blo 1064615 3595481 := bstep (se 2 (by rfl) ⟨1348305, by rfl⟩ : syracuseStep 3595481 = 2696611) B2696611
theorem B1596953 : Blo 1064615 1596953 := bstep (se 2 (by rfl) ⟨598857, by rfl⟩ : syracuseStep 1596953 = 1197715) B1197715
theorem B1138231 : Blo 1064615 1138231 := bstep (se 1 (by rfl) ⟨853673, by rfl⟩ : syracuseStep 1138231 = 1707347) B1707347
theorem B1597067 : Blo 1064615 1597067 := bstep (se 1 (by rfl) ⟨1197800, by rfl⟩ : syracuseStep 1597067 = 2395601) B2395601
theorem B2023051 : Blo 1064615 2023051 := bstep (se 1 (by rfl) ⟨1517288, by rfl⟩ : syracuseStep 2023051 = 3034577) B3034577
theorem B1597079 : Blo 1064615 1597079 := bstep (se 1 (by rfl) ⟨1197809, by rfl⟩ : syracuseStep 1597079 = 2395619) B2395619
theorem B2023127 : Blo 1064615 2023127 := bstep (se 1 (by rfl) ⟨1517345, by rfl⟩ : syracuseStep 2023127 = 3034691) B3034691
theorem B1597145 : Blo 1064615 1597145 := bstep (se 2 (by rfl) ⟨598929, by rfl⟩ : syracuseStep 1597145 = 1197859) B1197859
theorem B1138411 : Blo 1064615 1138411 := bstep (se 1 (by rfl) ⟨853808, by rfl⟩ : syracuseStep 1138411 = 1707617) B1707617
theorem B17325809 : Blo 1064615 17325809 := bstep (se 2 (by rfl) ⟨6497178, by rfl⟩ : syracuseStep 17325809 = 12994357) B12994357
theorem B1597259 : Blo 1064615 1597259 := bstep (se 1 (by rfl) ⟨1197944, by rfl⟩ : syracuseStep 1597259 = 2395889) B2395889
theorem B1597271 : Blo 1064615 1597271 := bstep (se 1 (by rfl) ⟨1197953, by rfl⟩ : syracuseStep 1597271 = 2395907) B2395907
theorem B3039065 : Blo 1064615 3039065 := bstep (se 2 (by rfl) ⟨1139649, by rfl⟩ : syracuseStep 3039065 = 2279299) B2279299
theorem B3596183 : Blo 1064615 3596183 := bstep (se 1 (by rfl) ⟨2697137, by rfl⟩ : syracuseStep 3596183 = 5394275) B5394275
theorem B1597337 : Blo 1064615 1597337 := bstep (se 2 (by rfl) ⟨599001, by rfl⟩ : syracuseStep 1597337 = 1198003) B1198003
theorem B4874201 : Blo 1064615 4874201 := bstep (se 2 (by rfl) ⟨1827825, by rfl⟩ : syracuseStep 4874201 = 3655651) B3655651
theorem B1597451 : Blo 1064615 1597451 := bstep (se 1 (by rfl) ⟨1198088, by rfl⟩ : syracuseStep 1597451 = 2396177) B2396177
theorem B1597463 : Blo 1064615 1597463 := bstep (se 1 (by rfl) ⟨1198097, by rfl⟩ : syracuseStep 1597463 = 2396195) B2396195
theorem B1597529 : Blo 1064615 1597529 := bstep (se 2 (by rfl) ⟨599073, by rfl⟩ : syracuseStep 1597529 = 1198147) B1198147
theorem B3039383 : Blo 1064615 3039383 := bstep (se 1 (by rfl) ⟨2279537, by rfl⟩ : syracuseStep 3039383 = 4559075) B4559075
theorem B1597643 : Blo 1064615 1597643 := bstep (se 1 (by rfl) ⟨1198232, by rfl⟩ : syracuseStep 1597643 = 2396465) B2396465
theorem B1597655 : Blo 1064615 1597655 := bstep (se 1 (by rfl) ⟨1198241, by rfl⟩ : syracuseStep 1597655 = 2396483) B2396483
theorem B1597721 : Blo 1064615 1597721 := bstep (se 2 (by rfl) ⟨599145, by rfl⟩ : syracuseStep 1597721 = 1198291) B1198291
theorem B2023795 : Blo 1064615 2023795 := bstep (se 1 (by rfl) ⟨1517846, by rfl⟩ : syracuseStep 2023795 = 3035693) B3035693
theorem B8216963 : Blo 1064615 8216963 := bstep (se 1 (by rfl) ⟨6162722, by rfl⟩ : syracuseStep 8216963 = 12325445) B12325445
theorem B1597835 : Blo 1064615 1597835 := bstep (se 1 (by rfl) ⟨1198376, by rfl⟩ : syracuseStep 1597835 = 2396753) B2396753
theorem B1597847 : Blo 1064615 1597847 := bstep (se 1 (by rfl) ⟨1198385, by rfl⟩ : syracuseStep 1597847 = 2396771) B2396771
theorem B9101747 : Blo 1064615 9101747 := bstep (se 1 (by rfl) ⟨6826310, by rfl⟩ : syracuseStep 9101747 = 13652621) B13652621
theorem B3596723 : Blo 1064615 3596723 := bstep (se 1 (by rfl) ⟨2697542, by rfl⟩ : syracuseStep 3596723 = 5395085) B5395085
theorem B1597913 : Blo 1064615 1597913 := bstep (se 2 (by rfl) ⟨599217, by rfl⟩ : syracuseStep 1597913 = 1198435) B1198435
theorem B1598027 : Blo 1064615 1598027 := bstep (se 1 (by rfl) ⟨1198520, by rfl⟩ : syracuseStep 1598027 = 2397041) B2397041
theorem B1598039 : Blo 1064615 1598039 := bstep (se 1 (by rfl) ⟨1198529, by rfl⟩ : syracuseStep 1598039 = 2397059) B2397059
theorem B2024023 : Blo 1064615 2024023 := bstep (se 1 (by rfl) ⟨1518017, by rfl⟩ : syracuseStep 2024023 = 3036035) B3036035
theorem B1598105 : Blo 1064615 1598105 := bstep (se 2 (by rfl) ⟨599289, by rfl⟩ : syracuseStep 1598105 = 1198579) B1198579
theorem B3596993 : Blo 1064615 3596993 := bstep (se 2 (by rfl) ⟨1348872, by rfl⟩ : syracuseStep 3596993 = 2697745) B2697745
theorem B2024129 : Blo 1064615 2024129 := bstep (se 2 (by rfl) ⟨759048, by rfl⟩ : syracuseStep 2024129 = 1518097) B1518097
theorem B1598219 : Blo 1064615 1598219 := bstep (se 1 (by rfl) ⟨1198664, by rfl⟩ : syracuseStep 1598219 = 2397329) B2397329
theorem B1598231 : Blo 1064615 1598231 := bstep (se 1 (by rfl) ⟨1198673, by rfl⟩ : syracuseStep 1598231 = 2397347) B2397347
theorem B1598297 : Blo 1064615 1598297 := bstep (se 2 (by rfl) ⟨599361, by rfl⟩ : syracuseStep 1598297 = 1198723) B1198723
theorem B2024281 : Blo 1064615 2024281 := bstep (se 2 (by rfl) ⟨759105, by rfl⟩ : syracuseStep 2024281 = 1518211) B1518211
theorem B3040193 : Blo 1064615 3040193 := bstep (se 2 (by rfl) ⟨1140072, by rfl⟩ : syracuseStep 3040193 = 2280145) B2280145
theorem B1598411 : Blo 1064615 1598411 := bstep (se 1 (by rfl) ⟨1198808, by rfl⟩ : syracuseStep 1598411 = 2397617) B2397617
theorem B1598423 : Blo 1064615 1598423 := bstep (se 1 (by rfl) ⟨1198817, by rfl⟩ : syracuseStep 1598423 = 2397635) B2397635
theorem B1598489 : Blo 1064615 1598489 := bstep (se 2 (by rfl) ⟨599433, by rfl⟩ : syracuseStep 1598489 = 1198867) B1198867
theorem B1598603 : Blo 1064615 1598603 := bstep (se 1 (by rfl) ⟨1198952, by rfl⟩ : syracuseStep 1598603 = 2397905) B2397905
theorem B1598615 : Blo 1064615 1598615 := bstep (se 1 (by rfl) ⟨1198961, by rfl⟩ : syracuseStep 1598615 = 2397923) B2397923
theorem B1598681 : Blo 1064615 1598681 := bstep (se 2 (by rfl) ⟨599505, by rfl⟩ : syracuseStep 1598681 = 1199011) B1199011
theorem B3597533 : Blo 1064615 3597533 := bstep (se 3 (by rfl) ⟨674537, by rfl⟩ : syracuseStep 3597533 = 1349075) B1349075
theorem B1598795 : Blo 1064615 1598795 := bstep (se 1 (by rfl) ⟨1199096, by rfl⟩ : syracuseStep 1598795 = 2398193) B2398193
theorem B1598807 : Blo 1064615 1598807 := bstep (se 1 (by rfl) ⟨1199105, by rfl⟩ : syracuseStep 1598807 = 2398211) B2398211
theorem B8217949 : Blo 1064615 8217949 := bstep (se 3 (by rfl) ⟨1540865, by rfl⟩ : syracuseStep 8217949 = 3081731) B3081731
theorem B1598873 : Blo 1064615 1598873 := bstep (se 2 (by rfl) ⟨599577, by rfl⟩ : syracuseStep 1598873 = 1199155) B1199155
theorem B1598987 : Blo 1064615 1598987 := bstep (se 1 (by rfl) ⟨1199240, by rfl⟩ : syracuseStep 1598987 = 2398481) B2398481
theorem B1598999 : Blo 1064615 1598999 := bstep (se 1 (by rfl) ⟨1199249, by rfl⟩ : syracuseStep 1598999 = 2398499) B2398499
theorem B7792163 : Blo 1064615 7792163 := bstep (se 1 (by rfl) ⟨5844122, by rfl⟩ : syracuseStep 7792163 = 11688245) B11688245
theorem B1599065 : Blo 1064615 1599065 := bstep (se 2 (by rfl) ⟨599649, by rfl⟩ : syracuseStep 1599065 = 1199299) B1199299
theorem B10938007 : Blo 1064615 10938007 := bstep (se 1 (by rfl) ⟨8203505, by rfl⟩ : syracuseStep 10938007 = 16407011) B16407011
theorem B4056749 : Blo 1064615 4056749 := bstep (se 3 (by rfl) ⟨760640, by rfl⟩ : syracuseStep 4056749 = 1521281) B1521281
theorem B1599179 : Blo 1064615 1599179 := bstep (se 1 (by rfl) ⟨1199384, by rfl⟩ : syracuseStep 1599179 = 2398769) B2398769
theorem B1140427 : Blo 1064615 1140427 := bstep (se 1 (by rfl) ⟨855320, by rfl⟩ : syracuseStep 1140427 = 1710641) B1710641
theorem B1599191 : Blo 1064615 1599191 := bstep (se 1 (by rfl) ⟨1199393, by rfl⟩ : syracuseStep 1599191 = 2398787) B2398787
theorem B1599257 : Blo 1064615 1599257 := bstep (se 2 (by rfl) ⟨599721, by rfl⟩ : syracuseStep 1599257 = 1199443) B1199443
theorem B1599371 : Blo 1064615 1599371 := bstep (se 1 (by rfl) ⟨1199528, by rfl⟩ : syracuseStep 1599371 = 2399057) B2399057
theorem B1599383 : Blo 1064615 1599383 := bstep (se 1 (by rfl) ⟨1199537, by rfl⟩ : syracuseStep 1599383 = 2399075) B2399075
theorem B1599449 : Blo 1064615 1599449 := bstep (se 2 (by rfl) ⟨599793, by rfl⟩ : syracuseStep 1599449 = 1199587) B1199587
theorem B5400593 : Blo 1064615 5400593 := bstep (se 2 (by rfl) ⟨2025222, by rfl⟩ : syracuseStep 5400593 = 4050445) B4050445
theorem B1599563 : Blo 1064615 1599563 := bstep (se 1 (by rfl) ⟨1199672, by rfl⟩ : syracuseStep 1599563 = 2399345) B2399345
theorem B1599575 : Blo 1064615 1599575 := bstep (se 1 (by rfl) ⟨1199681, by rfl⟩ : syracuseStep 1599575 = 2399363) B2399363
theorem B2025587 : Blo 1064615 2025587 := bstep (se 1 (by rfl) ⟨1519190, by rfl⟩ : syracuseStep 2025587 = 3038381) B3038381
theorem B1599641 : Blo 1064615 1599641 := bstep (se 2 (by rfl) ⟨599865, by rfl⟩ : syracuseStep 1599641 = 1199731) B1199731
theorem B5400755 : Blo 1064615 5400755 := bstep (se 1 (by rfl) ⟨4050566, by rfl⟩ : syracuseStep 5400755 = 8101133) B8101133
theorem B1370315 : Blo 1064615 1370315 := bstep (se 1 (by rfl) ⟨1027736, by rfl⟩ : syracuseStep 1370315 = 2055473) B2055473
theorem B1599755 : Blo 1064615 1599755 := bstep (se 1 (by rfl) ⟨1199816, by rfl⟩ : syracuseStep 1599755 = 2399633) B2399633
theorem B2025739 : Blo 1064615 2025739 := bstep (se 1 (by rfl) ⟨1519304, by rfl⟩ : syracuseStep 2025739 = 3038609) B3038609
theorem B1599767 : Blo 1064615 1599767 := bstep (se 1 (by rfl) ⟨1199825, by rfl⟩ : syracuseStep 1599767 = 2399651) B2399651
theorem B9103661 : Blo 1064615 9103661 := bstep (se 3 (by rfl) ⟨1706936, by rfl⟩ : syracuseStep 9103661 = 3413873) B3413873
theorem B3598667 : Blo 1064615 3598667 := bstep (se 1 (by rfl) ⟨2699000, by rfl⟩ : syracuseStep 3598667 = 5398001) B5398001
theorem B1599833 : Blo 1064615 1599833 := bstep (se 2 (by rfl) ⟨599937, by rfl⟩ : syracuseStep 1599833 = 1199875) B1199875
theorem B1599947 : Blo 1064615 1599947 := bstep (se 1 (by rfl) ⟨1199960, by rfl⟩ : syracuseStep 1599947 = 2399921) B2399921
theorem B1599959 : Blo 1064615 1599959 := bstep (se 1 (by rfl) ⟨1199969, by rfl⟩ : syracuseStep 1599959 = 2399939) B2399939
theorem B4549081 : Blo 1064615 4549081 := bstep (se 2 (by rfl) ⟨1705905, by rfl⟩ : syracuseStep 4549081 = 3411811) B3411811
theorem B1600025 : Blo 1064615 1600025 := bstep (se 2 (by rfl) ⟨600009, by rfl⟩ : syracuseStep 1600025 = 1200019) B1200019
theorem B3041867 : Blo 1064615 3041867 := bstep (se 1 (by rfl) ⟨2281400, by rfl⟩ : syracuseStep 3041867 = 4562801) B4562801
theorem B3598937 : Blo 1064615 3598937 := bstep (se 2 (by rfl) ⟨1349601, by rfl⟩ : syracuseStep 3598937 = 2699203) B2699203
theorem B2026073 : Blo 1064615 2026073 := bstep (se 2 (by rfl) ⟨759777, by rfl⟩ : syracuseStep 2026073 = 1519555) B1519555
theorem B1600139 : Blo 1064615 1600139 := bstep (se 1 (by rfl) ⟨1200104, by rfl⟩ : syracuseStep 1600139 = 2400209) B2400209
theorem B1600151 : Blo 1064615 1600151 := bstep (se 1 (by rfl) ⟨1200113, by rfl⟩ : syracuseStep 1600151 = 2400227) B2400227
theorem B1600217 : Blo 1064615 1600217 := bstep (se 2 (by rfl) ⟨600081, by rfl⟩ : syracuseStep 1600217 = 1200163) B1200163
theorem B1600331 : Blo 1064615 1600331 := bstep (se 1 (by rfl) ⟨1200248, by rfl⟩ : syracuseStep 1600331 = 2400497) B2400497
theorem B1796951 : Blo 1064615 1796951 := bstep (se 1 (by rfl) ⟨1347713, by rfl⟩ : syracuseStep 1796951 = 2695427) B2695427
theorem B1600343 : Blo 1064615 1600343 := bstep (se 1 (by rfl) ⟨1200257, by rfl⟩ : syracuseStep 1600343 = 2400515) B2400515
theorem B1600409 : Blo 1064615 1600409 := bstep (se 2 (by rfl) ⟨600153, by rfl⟩ : syracuseStep 1600409 = 1200307) B1200307
theorem B8088497 : Blo 1064615 8088497 := bstep (se 2 (by rfl) ⟨3033186, by rfl⟩ : syracuseStep 8088497 = 6066373) B6066373
theorem B1797079 : Blo 1064615 1797079 := bstep (se 1 (by rfl) ⟨1347809, by rfl⟩ : syracuseStep 1797079 = 2695619) B2695619
theorem B9104345 : Blo 1064615 9104345 := bstep (se 2 (by rfl) ⟨3414129, by rfl⟩ : syracuseStep 9104345 = 6828259) B6828259
theorem B1600523 : Blo 1064615 1600523 := bstep (se 1 (by rfl) ⟨1200392, by rfl⟩ : syracuseStep 1600523 = 2400785) B2400785
theorem B1600535 : Blo 1064615 1600535 := bstep (se 1 (by rfl) ⟨1200401, by rfl⟩ : syracuseStep 1600535 = 2400803) B2400803
theorem B5762123 : Blo 1064615 5762123 := bstep (se 1 (by rfl) ⟨4321592, by rfl⟩ : syracuseStep 5762123 = 8643185) B8643185
theorem B1600601 : Blo 1064615 1600601 := bstep (se 2 (by rfl) ⟨600225, by rfl⟩ : syracuseStep 1600601 = 1200451) B1200451
theorem B1600715 : Blo 1064615 1600715 := bstep (se 1 (by rfl) ⟨1200536, by rfl⟩ : syracuseStep 1600715 = 2401073) B2401073
theorem B1600727 : Blo 1064615 1600727 := bstep (se 1 (by rfl) ⟨1200545, by rfl⟩ : syracuseStep 1600727 = 2401091) B2401091
theorem B2026711 : Blo 1064615 2026711 := bstep (se 1 (by rfl) ⟨1520033, by rfl⟩ : syracuseStep 2026711 = 3040067) B3040067
theorem B3599639 : Blo 1064615 3599639 := bstep (se 1 (by rfl) ⟨2699729, by rfl⟩ : syracuseStep 3599639 = 5399459) B5399459
theorem B1600793 : Blo 1064615 1600793 := bstep (se 2 (by rfl) ⟨600297, by rfl⟩ : syracuseStep 1600793 = 1200595) B1200595
theorem B19426661 : Blo 1064615 19426661 := bstep (se 4 (by rfl) ⟨1821249, by rfl⟩ : syracuseStep 19426661 = 3642499) B3642499
theorem B1600907 : Blo 1064615 1600907 := bstep (se 1 (by rfl) ⟨1200680, by rfl⟩ : syracuseStep 1600907 = 2401361) B2401361
theorem B4550039 : Blo 1064615 4550039 := bstep (se 1 (by rfl) ⟨3412529, by rfl⟩ : syracuseStep 4550039 = 6825059) B6825059
theorem B8088983 : Blo 1064615 8088983 := bstep (se 1 (by rfl) ⟨6066737, by rfl⟩ : syracuseStep 8088983 = 12133475) B12133475
theorem B1600919 : Blo 1064615 1600919 := bstep (se 1 (by rfl) ⟨1200689, by rfl⟩ : syracuseStep 1600919 = 2401379) B2401379
theorem B1600985 : Blo 1064615 1600985 := bstep (se 2 (by rfl) ⟨600369, by rfl⟩ : syracuseStep 1600985 = 1200739) B1200739
theorem B1797707 : Blo 1064615 1797707 := bstep (se 1 (by rfl) ⟨1348280, by rfl⟩ : syracuseStep 1797707 = 2696561) B2696561
theorem B1601099 : Blo 1064615 1601099 := bstep (se 1 (by rfl) ⟨1200824, by rfl⟩ : syracuseStep 1601099 = 2401649) B2401649
theorem B1601111 : Blo 1064615 1601111 := bstep (se 1 (by rfl) ⟨1200833, by rfl⟩ : syracuseStep 1601111 = 2401667) B2401667
theorem B1601177 : Blo 1064615 1601177 := bstep (se 2 (by rfl) ⟨600441, by rfl⟩ : syracuseStep 1601177 = 1200883) B1200883
theorem B1797835 : Blo 1064615 1797835 := bstep (se 1 (by rfl) ⟨1348376, by rfl⟩ : syracuseStep 1797835 = 2696753) B2696753
theorem B1601291 : Blo 1064615 1601291 := bstep (se 1 (by rfl) ⟨1200968, by rfl⟩ : syracuseStep 1601291 = 2401937) B2401937
theorem B1601303 : Blo 1064615 1601303 := bstep (se 1 (by rfl) ⟨1200977, by rfl⟩ : syracuseStep 1601303 = 2401955) B2401955
theorem B3600179 : Blo 1064615 3600179 := bstep (se 1 (by rfl) ⟨2700134, by rfl⟩ : syracuseStep 3600179 = 5400269) B5400269
theorem B1797977 : Blo 1064615 1797977 := bstep (se 2 (by rfl) ⟨674241, by rfl⟩ : syracuseStep 1797977 = 1348483) B1348483
theorem B1601369 : Blo 1064615 1601369 := bstep (se 2 (by rfl) ⟨600513, by rfl⟩ : syracuseStep 1601369 = 1201027) B1201027
theorem B1601483 : Blo 1064615 1601483 := bstep (se 1 (by rfl) ⟨1201112, by rfl⟩ : syracuseStep 1601483 = 2402225) B2402225
theorem B1601495 : Blo 1064615 1601495 := bstep (se 1 (by rfl) ⟨1201121, by rfl⟩ : syracuseStep 1601495 = 2402243) B2402243
theorem B1798105 : Blo 1064615 1798105 := bstep (se 2 (by rfl) ⟨674289, by rfl⟩ : syracuseStep 1798105 = 1348579) B1348579
theorem B2027531 : Blo 1064615 2027531 := bstep (se 1 (by rfl) ⟨1520648, by rfl⟩ : syracuseStep 2027531 = 3041297) B3041297
theorem B1601561 : Blo 1064615 1601561 := bstep (se 2 (by rfl) ⟨600585, by rfl⟩ : syracuseStep 1601561 = 1201171) B1201171
theorem B3600449 : Blo 1064615 3600449 := bstep (se 2 (by rfl) ⟨1350168, by rfl⟩ : syracuseStep 3600449 = 2700337) B2700337
theorem B2027585 : Blo 1064615 2027585 := bstep (se 2 (by rfl) ⟨760344, by rfl⟩ : syracuseStep 2027585 = 1520689) B1520689
theorem B5402699 : Blo 1064615 5402699 := bstep (se 1 (by rfl) ⟨4052024, by rfl⟩ : syracuseStep 5402699 = 8104049) B8104049
theorem B17789003 : Blo 1064615 17789003 := bstep (se 1 (by rfl) ⟨13341752, by rfl⟩ : syracuseStep 17789003 = 26683505) B26683505
theorem B2158721 : Blo 1064615 2158721 := bstep (se 2 (by rfl) ⟨809520, by rfl⟩ : syracuseStep 2158721 = 1619041) B1619041
theorem B1601675 : Blo 1064615 1601675 := bstep (se 1 (by rfl) ⟨1201256, by rfl⟩ : syracuseStep 1601675 = 2402513) B2402513
theorem B1601687 : Blo 1064615 1601687 := bstep (se 1 (by rfl) ⟨1201265, by rfl⟩ : syracuseStep 1601687 = 2402531) B2402531
theorem B1601753 : Blo 1064615 1601753 := bstep (se 2 (by rfl) ⟨600657, by rfl⟩ : syracuseStep 1601753 = 1201315) B1201315
theorem B1601867 : Blo 1064615 1601867 := bstep (se 1 (by rfl) ⟨1201400, by rfl⟩ : syracuseStep 1601867 = 2402801) B2402801
theorem B1601879 : Blo 1064615 1601879 := bstep (se 1 (by rfl) ⟨1201409, by rfl⟩ : syracuseStep 1601879 = 2402819) B2402819
theorem B1601945 : Blo 1064615 1601945 := bstep (se 2 (by rfl) ⟨600729, by rfl⟩ : syracuseStep 1601945 = 1201459) B1201459
theorem B1602059 : Blo 1064615 1602059 := bstep (se 1 (by rfl) ⟨1201544, by rfl⟩ : syracuseStep 1602059 = 2403089) B2403089
theorem B6844945 : Blo 1064615 6844945 := bstep (se 2 (by rfl) ⟨2566854, by rfl⟩ : syracuseStep 6844945 = 5133709) B5133709
theorem B1798679 : Blo 1064615 1798679 := bstep (se 1 (by rfl) ⟨1349009, by rfl⟩ : syracuseStep 1798679 = 2698019) B2698019
theorem B1602071 : Blo 1064615 1602071 := bstep (se 1 (by rfl) ⟨1201553, by rfl⟩ : syracuseStep 1602071 = 2403107) B2403107
theorem B1602137 : Blo 1064615 1602137 := bstep (se 2 (by rfl) ⟨600801, by rfl⟩ : syracuseStep 1602137 = 1201603) B1201603
theorem B3600989 : Blo 1064615 3600989 := bstep (se 3 (by rfl) ⟨675185, by rfl⟩ : syracuseStep 3600989 = 1350371) B1350371
theorem B6156901 : Blo 1064615 6156901 := bstep (se 4 (by rfl) ⟨577209, by rfl⟩ : syracuseStep 6156901 = 1154419) B1154419
theorem B1798807 : Blo 1064615 1798807 := bstep (se 1 (by rfl) ⟨1349105, by rfl⟩ : syracuseStep 1798807 = 2698211) B2698211
theorem B1602251 : Blo 1064615 1602251 := bstep (se 1 (by rfl) ⟨1201688, by rfl⟩ : syracuseStep 1602251 = 2403377) B2403377
theorem B1602263 : Blo 1064615 1602263 := bstep (se 1 (by rfl) ⟨1201697, by rfl⟩ : syracuseStep 1602263 = 2403395) B2403395
theorem B1602329 : Blo 1064615 1602329 := bstep (se 2 (by rfl) ⟨600873, by rfl⟩ : syracuseStep 1602329 = 1201747) B1201747
theorem B2159435 : Blo 1064615 2159435 := bstep (se 1 (by rfl) ⟨1619576, by rfl⟩ : syracuseStep 2159435 = 3239153) B3239153
theorem B1602443 : Blo 1064615 1602443 := bstep (se 1 (by rfl) ⟨1201832, by rfl⟩ : syracuseStep 1602443 = 2403665) B2403665
theorem B1602455 : Blo 1064615 1602455 := bstep (se 1 (by rfl) ⟨1201841, by rfl⟩ : syracuseStep 1602455 = 2403683) B2403683
theorem B2028503 : Blo 1064615 2028503 := bstep (se 1 (by rfl) ⟨1521377, by rfl⟩ : syracuseStep 2028503 = 3042755) B3042755
theorem B1602521 : Blo 1064615 1602521 := bstep (se 2 (by rfl) ⟨600945, by rfl⟩ : syracuseStep 1602521 = 1201891) B1201891
theorem B4060205 : Blo 1064615 4060205 := bstep (se 3 (by rfl) ⟨761288, by rfl⟩ : syracuseStep 4060205 = 1522577) B1522577
theorem B1602635 : Blo 1064615 1602635 := bstep (se 1 (by rfl) ⟨1201976, by rfl⟩ : syracuseStep 1602635 = 2403953) B2403953
theorem B1602647 : Blo 1064615 1602647 := bstep (se 1 (by rfl) ⟨1201985, by rfl⟩ : syracuseStep 1602647 = 2403971) B2403971
theorem B1602713 : Blo 1064615 1602713 := bstep (se 2 (by rfl) ⟨601017, by rfl⟩ : syracuseStep 1602713 = 1202035) B1202035
theorem B23393461 : Blo 1064615 23393461 := bstep (se 5 (by rfl) ⟨1096568, by rfl⟩ : syracuseStep 23393461 = 2193137) B2193137
theorem B2880715 : Blo 1064615 2880715 := bstep (se 1 (by rfl) ⟨2160536, by rfl⟩ : syracuseStep 2880715 = 4321073) B4321073
theorem B1799435 : Blo 1064615 1799435 := bstep (se 1 (by rfl) ⟨1349576, by rfl⟩ : syracuseStep 1799435 = 2699153) B2699153
theorem B1602827 : Blo 1064615 1602827 := bstep (se 1 (by rfl) ⟨1202120, by rfl⟩ : syracuseStep 1602827 = 2404241) B2404241
theorem B1602839 : Blo 1064615 1602839 := bstep (se 1 (by rfl) ⟨1202129, by rfl⟩ : syracuseStep 1602839 = 2404259) B2404259
theorem B1602905 : Blo 1064615 1602905 := bstep (se 2 (by rfl) ⟨601089, by rfl⟩ : syracuseStep 1602905 = 1202179) B1202179
theorem B6845789 : Blo 1064615 6845789 := bstep (se 3 (by rfl) ⟨1283585, by rfl⟩ : syracuseStep 6845789 = 2567171) B2567171
theorem B1799563 : Blo 1064615 1799563 := bstep (se 1 (by rfl) ⟨1349672, by rfl⟩ : syracuseStep 1799563 = 2699345) B2699345
theorem B1537483 : Blo 1064615 1537483 := bstep (se 1 (by rfl) ⟨1153112, by rfl⟩ : syracuseStep 1537483 = 2306225) B2306225
theorem B4552139 : Blo 1064615 4552139 := bstep (se 1 (by rfl) ⟨3414104, by rfl⟩ : syracuseStep 4552139 = 6828209) B6828209
theorem B1799705 : Blo 1064615 1799705 := bstep (se 2 (by rfl) ⟨674889, by rfl⟩ : syracuseStep 1799705 = 1349779) B1349779
theorem B15398531 : Blo 1064615 15398531 := bstep (se 1 (by rfl) ⟨11548898, by rfl⟩ : syracuseStep 15398531 = 23097797) B23097797
theorem B1799833 : Blo 1064615 1799833 := bstep (se 2 (by rfl) ⟨674937, by rfl⟩ : syracuseStep 1799833 = 1349875) B1349875
theorem B3602123 : Blo 1064615 3602123 := bstep (se 1 (by rfl) ⟨2701592, by rfl⟩ : syracuseStep 3602123 = 5403185) B5403185
theorem B5404481 : Blo 1064615 5404481 := bstep (se 2 (by rfl) ⟨2026680, by rfl⟩ : syracuseStep 5404481 = 4053361) B4053361
theorem B13662053 : Blo 1064615 13662053 := bstep (se 4 (by rfl) ⟨1280817, by rfl⟩ : syracuseStep 13662053 = 2561635) B2561635
theorem B3602393 : Blo 1064615 3602393 := bstep (se 2 (by rfl) ⟨1350897, by rfl⟩ : syracuseStep 3602393 = 2701795) B2701795
theorem B15398873 : Blo 1064615 15398873 := bstep (se 2 (by rfl) ⟨5774577, by rfl⟩ : syracuseStep 15398873 = 11549155) B11549155
theorem B7796837 : Blo 1064615 7796837 := bstep (se 4 (by rfl) ⟨730953, by rfl⟩ : syracuseStep 7796837 = 1461907) B1461907
theorem B1800407 : Blo 1064615 1800407 := bstep (se 1 (by rfl) ⟨1350305, by rfl⟩ : syracuseStep 1800407 = 2700611) B2700611
theorem B1800535 : Blo 1064615 1800535 := bstep (se 1 (by rfl) ⟨1350401, by rfl⟩ : syracuseStep 1800535 = 2700803) B2700803
theorem B94959985 : Blo 1064615 94959985 := bstep (se 2 (by rfl) ⟨35609994, by rfl⟩ : syracuseStep 94959985 = 71219989) B71219989
theorem B2882099 : Blo 1064615 2882099 := bstep (se 1 (by rfl) ⟨2161574, by rfl⟩ : syracuseStep 2882099 = 4323149) B4323149
theorem B3603095 : Blo 1064615 3603095 := bstep (se 1 (by rfl) ⟨2702321, by rfl⟩ : syracuseStep 3603095 = 5404643) B5404643
theorem B1538713 : Blo 1064615 1538713 := bstep (se 2 (by rfl) ⟨577017, by rfl⟩ : syracuseStep 1538713 = 1154035) B1154035
theorem B1801163 : Blo 1064615 1801163 := bstep (se 1 (by rfl) ⟨1350872, by rfl⟩ : syracuseStep 1801163 = 2701745) B2701745
theorem B4553779 : Blo 1064615 4553779 := bstep (se 1 (by rfl) ⟨3415334, by rfl⟩ : syracuseStep 4553779 = 6830669) B6830669
theorem B1801291 : Blo 1064615 1801291 := bstep (se 1 (by rfl) ⟨1350968, by rfl⟩ : syracuseStep 1801291 = 2701937) B2701937
theorem B3603635 : Blo 1064615 3603635 := bstep (se 1 (by rfl) ⟨2702726, by rfl⟩ : syracuseStep 3603635 = 5405453) B5405453
theorem B1801433 : Blo 1064615 1801433 := bstep (se 2 (by rfl) ⟨675537, by rfl⟩ : syracuseStep 1801433 = 1351075) B1351075
theorem B3243287 : Blo 1064615 3243287 := bstep (se 1 (by rfl) ⟨2432465, by rfl⟩ : syracuseStep 3243287 = 4864931) B4864931
theorem B1801561 : Blo 1064615 1801561 := bstep (se 2 (by rfl) ⟨675585, by rfl⟩ : syracuseStep 1801561 = 1351171) B1351171
theorem B3603905 : Blo 1064615 3603905 := bstep (se 2 (by rfl) ⟨1351464, by rfl⟩ : syracuseStep 3603905 = 2702929) B2702929
theorem B2162305 : Blo 1064615 2162305 := bstep (se 2 (by rfl) ⟨810864, by rfl⟩ : syracuseStep 2162305 = 1621729) B1621729
theorem B4554413 : Blo 1064615 4554413 := bstep (se 3 (by rfl) ⟨853952, by rfl⟩ : syracuseStep 4554413 = 1707905) B1707905
theorem B5406425 : Blo 1064615 5406425 := bstep (se 2 (by rfl) ⟨2027409, by rfl⟩ : syracuseStep 5406425 = 4054819) B4054819
theorem B1802135 : Blo 1064615 1802135 := bstep (se 1 (by rfl) ⟨1351601, by rfl⟩ : syracuseStep 1802135 = 2703203) B2703203
theorem B3604445 : Blo 1064615 3604445 := bstep (se 3 (by rfl) ⟨675833, by rfl⟩ : syracuseStep 3604445 = 1351667) B1351667
theorem B5406749 : Blo 1064615 5406749 := bstep (se 3 (by rfl) ⟨1013765, by rfl⟩ : syracuseStep 5406749 = 2027531) B2027531
theorem B1802425 : Blo 1064615 1802425 := bstep (se 2 (by rfl) ⟨675909, by rfl⟩ : syracuseStep 1802425 = 1351819) B1351819
theorem B5767361 : Blo 1064615 5767361 := bstep (se 2 (by rfl) ⟨2162760, by rfl⟩ : syracuseStep 5767361 = 4325521) B4325521
theorem B4325647 : Blo 1064615 4325647 := bstep (se 1 (by rfl) ⟨3244235, by rfl⟩ : syracuseStep 4325647 = 6488471) B6488471
theorem B3604769 : Blo 1064615 3604769 := bstep (se 2 (by rfl) ⟨1351788, by rfl⟩ : syracuseStep 3604769 = 2703577) B2703577
theorem B5407235 : Blo 1064615 5407235 := bstep (se 1 (by rfl) ⟨4055426, by rfl⟩ : syracuseStep 5407235 = 8110853) B8110853
theorem B3605363 : Blo 1064615 3605363 := bstep (se 1 (by rfl) ⟨2704022, by rfl⟩ : syracuseStep 3605363 = 5408045) B5408045
theorem B1803127 : Blo 1064615 1803127 := bstep (se 1 (by rfl) ⟨1352345, by rfl⟩ : syracuseStep 1803127 = 2704691) B2704691
theorem B15402221 : Blo 1064615 15402221 := bstep (se 3 (by rfl) ⟨2887916, by rfl⟩ : syracuseStep 15402221 = 5775833) B5775833
theorem B2885149 : Blo 1064615 2885149 := bstep (se 3 (by rfl) ⟨540965, by rfl⟩ : syracuseStep 2885149 = 1081931) B1081931
theorem B1443385 : Blo 1064615 1443385 := bstep (se 2 (by rfl) ⟨541269, by rfl⟩ : syracuseStep 1443385 = 1082539) B1082539
theorem B2918003 : Blo 1064615 2918003 := bstep (se 1 (by rfl) ⟨2188502, by rfl⟩ : syracuseStep 2918003 = 4377005) B4377005
theorem B43779761 : Blo 1064615 43779761 := bstep (se 2 (by rfl) ⟨16417410, by rfl⟩ : syracuseStep 43779761 = 32834821) B32834821
theorem B1443515 : Blo 1064615 1443515 := bstep (se 1 (by rfl) ⟨1082636, by rfl⟩ : syracuseStep 1443515 = 2165273) B2165273
theorem B5473993 : Blo 1064615 5473993 := bstep (se 2 (by rfl) ⟨2052747, by rfl⟩ : syracuseStep 5473993 = 4105495) B4105495
theorem B2164495 : Blo 1064615 2164495 := bstep (se 1 (by rfl) ⟨1623371, by rfl⟩ : syracuseStep 2164495 = 3246743) B3246743
theorem B1706027 : Blo 1064615 1706027 := bstep (se 1 (by rfl) ⟨1279520, by rfl⟩ : syracuseStep 1706027 = 2559041) B2559041
theorem B5408855 : Blo 1064615 5408855 := bstep (se 1 (by rfl) ⟨4056641, by rfl⟩ : syracuseStep 5408855 = 8113283) B8113283
theorem B2558137 : Blo 1064615 2558137 := bstep (se 2 (by rfl) ⟨959301, by rfl⟩ : syracuseStep 2558137 = 1918603) B1918603
theorem B14780819 : Blo 1064615 14780819 := bstep (se 1 (by rfl) ⟨11085614, by rfl⟩ : syracuseStep 14780819 = 22171229) B22171229
theorem B2886187 : Blo 1064615 2886187 := bstep (se 1 (by rfl) ⟨2164640, by rfl⟩ : syracuseStep 2886187 = 4329281) B4329281
theorem B5409341 : Blo 1064615 5409341 := bstep (se 3 (by rfl) ⟨1014251, by rfl⟩ : syracuseStep 5409341 = 2028503) B2028503
theorem B2558753 : Blo 1064615 2558753 := bstep (se 2 (by rfl) ⟨959532, by rfl⟩ : syracuseStep 2558753 = 1919065) B1919065
theorem B9112409 : Blo 1064615 9112409 := bstep (se 2 (by rfl) ⟨3417153, by rfl⟩ : syracuseStep 9112409 = 6834307) B6834307
theorem B1707193 : Blo 1064615 1707193 := bstep (se 2 (by rfl) ⟨640197, by rfl⟩ : syracuseStep 1707193 = 1280395) B1280395
theorem B6491393 : Blo 1064615 6491393 := bstep (se 2 (by rfl) ⟨2434272, by rfl⟩ : syracuseStep 6491393 = 4868545) B4868545
theorem B6065441 : Blo 1064615 6065441 := bstep (se 2 (by rfl) ⟨2274540, by rfl⟩ : syracuseStep 6065441 = 4549081) B4549081
theorem B34639163 : Blo 1064615 34639163 := bstep (se 1 (by rfl) ⟨25979372, by rfl⟩ : syracuseStep 34639163 = 51958745) B51958745
theorem B2395511 : Blo 1064615 2395511 := bstep (se 1 (by rfl) ⟨1796633, by rfl⟩ : syracuseStep 2395511 = 3593267) B3593267
theorem B2559367 : Blo 1064615 2559367 := bstep (se 1 (by rfl) ⟨1919525, by rfl⟩ : syracuseStep 2559367 = 3839051) B3839051
theorem B8097245 : Blo 1064615 8097245 := bstep (se 3 (by rfl) ⟨1518233, by rfl⟩ : syracuseStep 8097245 = 3036467) B3036467
theorem B2395691 : Blo 1064615 2395691 := bstep (se 1 (by rfl) ⟨1796768, by rfl⟩ : syracuseStep 2395691 = 3593537) B3593537
theorem B2396051 : Blo 1064615 2396051 := bstep (se 1 (by rfl) ⟨1797038, by rfl⟩ : syracuseStep 2396051 = 3594077) B3594077
theorem B2396105 : Blo 1064615 2396105 := bstep (se 2 (by rfl) ⟨898539, by rfl⟩ : syracuseStep 2396105 = 1797079) B1797079
theorem B1348103 : Blo 1064615 1348103 := bstep (se 1 (by rfl) ⟨1011077, by rfl⟩ : syracuseStep 1348103 = 2022155) B2022155
theorem B12980837 : Blo 1064615 12980837 := bstep (se 4 (by rfl) ⟨1216953, by rfl⟩ : syracuseStep 12980837 = 2433907) B2433907
theorem B2396807 : Blo 1064615 2396807 := bstep (se 1 (by rfl) ⟨1797605, by rfl⟩ : syracuseStep 2396807 = 3595211) B3595211
theorem B2888327 : Blo 1064615 2888327 := bstep (se 1 (by rfl) ⟨2166245, by rfl⟩ : syracuseStep 2888327 = 4332491) B4332491
theorem B2396987 : Blo 1064615 2396987 := bstep (se 1 (by rfl) ⟨1797740, by rfl⟩ : syracuseStep 2396987 = 3595481) B3595481
theorem B2397113 : Blo 1064615 2397113 := bstep (se 2 (by rfl) ⟨898917, by rfl⟩ : syracuseStep 2397113 = 1797835) B1797835
theorem B3413053 : Blo 1064615 3413053 := bstep (se 3 (by rfl) ⟨639947, by rfl⟩ : syracuseStep 3413053 = 1279895) B1279895
theorem B1348751 : Blo 1064615 1348751 := bstep (se 1 (by rfl) ⟨1011563, by rfl⟩ : syracuseStep 1348751 = 2023127) B2023127
theorem B6165677 : Blo 1064615 6165677 := bstep (se 3 (by rfl) ⟨1156064, by rfl⟩ : syracuseStep 6165677 = 2312129) B2312129
theorem B1709257 : Blo 1064615 1709257 := bstep (se 2 (by rfl) ⟨640971, by rfl⟩ : syracuseStep 1709257 = 1281943) B1281943
theorem B2397455 : Blo 1064615 2397455 := bstep (se 1 (by rfl) ⟨1798091, by rfl⟩ : syracuseStep 2397455 = 3596183) B3596183
theorem B2397473 : Blo 1064615 2397473 := bstep (se 2 (by rfl) ⟨899052, by rfl⟩ : syracuseStep 2397473 = 1798105) B1798105
theorem B3249467 : Blo 1064615 3249467 := bstep (se 1 (by rfl) ⟨2437100, by rfl⟩ : syracuseStep 3249467 = 4874201) B4874201
theorem B5117273 : Blo 1064615 5117273 := bstep (se 2 (by rfl) ⟨1918977, by rfl⟩ : syracuseStep 5117273 = 3837955) B3837955
theorem B26645861 : Blo 1064615 26645861 := bstep (se 4 (by rfl) ⟨2498049, by rfl⟩ : syracuseStep 26645861 = 4996099) B4996099
theorem B31167929 : Blo 1064615 31167929 := bstep (se 2 (by rfl) ⟨11687973, by rfl⟩ : syracuseStep 31167929 = 23375947) B23375947
theorem B1709513 : Blo 1064615 1709513 := bstep (se 2 (by rfl) ⟨641067, by rfl⟩ : syracuseStep 1709513 = 1282135) B1282135
theorem B3413515 : Blo 1064615 3413515 := bstep (se 1 (by rfl) ⟨2560136, by rfl⟩ : syracuseStep 3413515 = 5120273) B5120273
theorem B5477975 : Blo 1064615 5477975 := bstep (se 1 (by rfl) ⟨4108481, by rfl⟩ : syracuseStep 5477975 = 8216963) B8216963
theorem B6821495 : Blo 1064615 6821495 := bstep (se 1 (by rfl) ⟨5116121, by rfl⟩ : syracuseStep 6821495 = 10232243) B10232243
theorem B6067831 : Blo 1064615 6067831 := bstep (se 1 (by rfl) ⟨4550873, by rfl⟩ : syracuseStep 6067831 = 9101747) B9101747
theorem B2397815 : Blo 1064615 2397815 := bstep (se 1 (by rfl) ⟨1798361, by rfl⟩ : syracuseStep 2397815 = 3596723) B3596723
theorem B2397995 : Blo 1064615 2397995 := bstep (se 1 (by rfl) ⟨1798496, by rfl⟩ : syracuseStep 2397995 = 3596993) B3596993
theorem B2398355 : Blo 1064615 2398355 := bstep (se 1 (by rfl) ⟨1798766, by rfl⟩ : syracuseStep 2398355 = 3597533) B3597533
theorem B2398409 : Blo 1064615 2398409 := bstep (se 2 (by rfl) ⟨899403, by rfl⟩ : syracuseStep 2398409 = 1798807) B1798807
theorem B8198585 : Blo 1064615 8198585 := bstep (se 2 (by rfl) ⟨3074469, by rfl⟩ : syracuseStep 8198585 = 6148939) B6148939
theorem B5773885 : Blo 1064615 5773885 := bstep (se 3 (by rfl) ⟨1082603, by rfl⟩ : syracuseStep 5773885 = 2165207) B2165207
theorem B6069107 : Blo 1064615 6069107 := bstep (se 1 (by rfl) ⟨4551830, by rfl⟩ : syracuseStep 6069107 = 9103661) B9103661
theorem B3414899 : Blo 1064615 3414899 := bstep (se 1 (by rfl) ⟨2561174, by rfl⟩ : syracuseStep 3414899 = 5122349) B5122349
theorem B2399111 : Blo 1064615 2399111 := bstep (se 1 (by rfl) ⟨1799333, by rfl⟩ : syracuseStep 2399111 = 3598667) B3598667
theorem B3840953 : Blo 1064615 3840953 := bstep (se 2 (by rfl) ⟨1440357, by rfl⟩ : syracuseStep 3840953 = 2880715) B2880715
theorem B2399291 : Blo 1064615 2399291 := bstep (se 1 (by rfl) ⟨1799468, by rfl⟩ : syracuseStep 2399291 = 3598937) B3598937
theorem B2399417 : Blo 1064615 2399417 := bstep (se 2 (by rfl) ⟨899781, by rfl⟩ : syracuseStep 2399417 = 1799563) B1799563
theorem B3415297 : Blo 1064615 3415297 := bstep (se 2 (by rfl) ⟨1280736, by rfl⟩ : syracuseStep 3415297 = 2561473) B2561473
theorem B6069563 : Blo 1064615 6069563 := bstep (se 1 (by rfl) ⟨4552172, by rfl⟩ : syracuseStep 6069563 = 9104345) B9104345
theorem B3841415 : Blo 1064615 3841415 := bstep (se 1 (by rfl) ⟨2881061, by rfl⟩ : syracuseStep 3841415 = 5762123) B5762123
theorem B2563481 : Blo 1064615 2563481 := bstep (se 2 (by rfl) ⟨961305, by rfl⟩ : syracuseStep 2563481 = 1922611) B1922611
theorem B2399759 : Blo 1064615 2399759 := bstep (se 1 (by rfl) ⟨1799819, by rfl⟩ : syracuseStep 2399759 = 3599639) B3599639
theorem B2399777 : Blo 1064615 2399777 := bstep (se 2 (by rfl) ⟨899916, by rfl⟩ : syracuseStep 2399777 = 1799833) B1799833
theorem B12951107 : Blo 1064615 12951107 := bstep (se 1 (by rfl) ⟨9713330, by rfl⟩ : syracuseStep 12951107 = 19426661) B19426661
theorem B2432647 : Blo 1064615 2432647 := bstep (se 1 (by rfl) ⟨1824485, by rfl⟩ : syracuseStep 2432647 = 3648971) B3648971
theorem B2694809 : Blo 1064615 2694809 := bstep (se 2 (by rfl) ⟨1010553, by rfl⟩ : syracuseStep 2694809 = 2021107) B2021107
theorem B12132017 : Blo 1064615 12132017 := bstep (se 2 (by rfl) ⟨4549506, by rfl⟩ : syracuseStep 12132017 = 9099013) B9099013
theorem B84156205 : Blo 1064615 84156205 := bstep (se 3 (by rfl) ⟨15779288, by rfl⟩ : syracuseStep 84156205 = 31558577) B31558577
theorem B2694971 : Blo 1064615 2694971 := bstep (se 1 (by rfl) ⟨2021228, by rfl⟩ : syracuseStep 2694971 = 4042457) B4042457
theorem B2400119 : Blo 1064615 2400119 := bstep (se 1 (by rfl) ⟨1800089, by rfl⟩ : syracuseStep 2400119 = 3600179) B3600179
theorem B2400299 : Blo 1064615 2400299 := bstep (se 1 (by rfl) ⟨1800224, by rfl⟩ : syracuseStep 2400299 = 3600449) B3600449
theorem B1351723 : Blo 1064615 1351723 := bstep (se 1 (by rfl) ⟨1013792, by rfl⟩ : syracuseStep 1351723 = 2027585) B2027585
theorem B2695315 : Blo 1064615 2695315 := bstep (se 1 (by rfl) ⟨2021486, by rfl⟩ : syracuseStep 2695315 = 4042973) B4042973
theorem B5775533 : Blo 1064615 5775533 := bstep (se 3 (by rfl) ⟨1082912, by rfl⟩ : syracuseStep 5775533 = 2165825) B2165825
theorem B23044337 : Blo 1064615 23044337 := bstep (se 2 (by rfl) ⟨8641626, by rfl⟩ : syracuseStep 23044337 = 17283253) B17283253
theorem B5775617 : Blo 1064615 5775617 := bstep (se 2 (by rfl) ⟨2165856, by rfl⟩ : syracuseStep 5775617 = 4331713) B4331713
theorem B4858127 : Blo 1064615 4858127 := bstep (se 1 (by rfl) ⟨3643595, by rfl⟩ : syracuseStep 4858127 = 7287191) B7287191
theorem B2695457 : Blo 1064615 2695457 := bstep (se 2 (by rfl) ⟨1010796, by rfl⟩ : syracuseStep 2695457 = 2021593) B2021593
theorem B6070565 : Blo 1064615 6070565 := bstep (se 4 (by rfl) ⟨569115, by rfl⟩ : syracuseStep 6070565 = 1138231) B1138231
theorem B2400659 : Blo 1064615 2400659 := bstep (se 1 (by rfl) ⟨1800494, by rfl⟩ : syracuseStep 2400659 = 3600989) B3600989
theorem B2400713 : Blo 1064615 2400713 := bstep (se 2 (by rfl) ⟨900267, by rfl⟩ : syracuseStep 2400713 = 1800535) B1800535
theorem B4563485 : Blo 1064615 4563485 := bstep (se 3 (by rfl) ⟨855653, by rfl⟩ : syracuseStep 4563485 = 1711307) B1711307
theorem B2433671 : Blo 1064615 2433671 := bstep (se 1 (by rfl) ⟨1825253, by rfl⟩ : syracuseStep 2433671 = 3650507) B3650507
theorem B6071021 : Blo 1064615 6071021 := bstep (se 3 (by rfl) ⟨1138316, by rfl⟩ : syracuseStep 6071021 = 2276633) B2276633
theorem B58336037 : Blo 1064615 58336037 := bstep (se 4 (by rfl) ⟨5469003, by rfl⟩ : syracuseStep 58336037 = 10938007) B10938007
theorem B1516423 : Blo 1064615 1516423 := bstep (se 1 (by rfl) ⟨1137317, by rfl⟩ : syracuseStep 1516423 = 2274635) B2274635
theorem B4563859 : Blo 1064615 4563859 := bstep (se 1 (by rfl) ⟨3422894, by rfl⟩ : syracuseStep 4563859 = 6845789) B6845789
theorem B10265687 : Blo 1064615 10265687 := bstep (se 1 (by rfl) ⟨7699265, by rfl⟩ : syracuseStep 10265687 = 15398531) B15398531
theorem B2401415 : Blo 1064615 2401415 := bstep (se 1 (by rfl) ⟨1801061, by rfl⟩ : syracuseStep 2401415 = 3602123) B3602123
theorem B2696449 : Blo 1064615 2696449 := bstep (se 2 (by rfl) ⟨1011168, by rfl⟩ : syracuseStep 2696449 = 2022337) B2022337
theorem B2401595 : Blo 1064615 2401595 := bstep (se 1 (by rfl) ⟨1801196, by rfl⟩ : syracuseStep 2401595 = 3602393) B3602393
theorem B10265915 : Blo 1064615 10265915 := bstep (se 1 (by rfl) ⟨7699436, by rfl⟩ : syracuseStep 10265915 = 15398873) B15398873
theorem B6071705 : Blo 1064615 6071705 := bstep (se 2 (by rfl) ⟨2276889, by rfl⟩ : syracuseStep 6071705 = 4553779) B4553779
theorem B2401721 : Blo 1064615 2401721 := bstep (se 2 (by rfl) ⟨900645, by rfl⟩ : syracuseStep 2401721 = 1801291) B1801291
theorem B2434619 : Blo 1064615 2434619 := bstep (se 1 (by rfl) ⟨1825964, by rfl⟩ : syracuseStep 2434619 = 3651929) B3651929
theorem B10692161 : Blo 1064615 10692161 := bstep (se 2 (by rfl) ⟨4009560, by rfl⟩ : syracuseStep 10692161 = 8019121) B8019121
theorem B3417871 : Blo 1064615 3417871 := bstep (se 1 (by rfl) ⟨2563403, by rfl⟩ : syracuseStep 3417871 = 5126807) B5126807
theorem B2402063 : Blo 1064615 2402063 := bstep (se 1 (by rfl) ⟨1801547, by rfl⟩ : syracuseStep 2402063 = 3603095) B3603095
theorem B2598689 : Blo 1064615 2598689 := bstep (se 2 (by rfl) ⟨974508, by rfl⟩ : syracuseStep 2598689 = 1949017) B1949017
theorem B2402081 : Blo 1064615 2402081 := bstep (se 2 (by rfl) ⟨900780, by rfl⟩ : syracuseStep 2402081 = 1801561) B1801561
theorem B2697047 : Blo 1064615 2697047 := bstep (se 1 (by rfl) ⟨2022785, by rfl⟩ : syracuseStep 2697047 = 4045571) B4045571
theorem B6563729 : Blo 1064615 6563729 := bstep (se 2 (by rfl) ⟨2461398, by rfl⟩ : syracuseStep 6563729 = 4922797) B4922797
theorem B2697259 : Blo 1064615 2697259 := bstep (se 1 (by rfl) ⟨2022944, by rfl⟩ : syracuseStep 2697259 = 4045889) B4045889
theorem B2402423 : Blo 1064615 2402423 := bstep (se 1 (by rfl) ⟨1801817, by rfl⟩ : syracuseStep 2402423 = 3603635) B3603635
theorem B2697401 : Blo 1064615 2697401 := bstep (se 2 (by rfl) ⟨1011525, by rfl⟩ : syracuseStep 2697401 = 2023051) B2023051
theorem B2402603 : Blo 1064615 2402603 := bstep (se 1 (by rfl) ⟨1801952, by rfl⟩ : syracuseStep 2402603 = 3603905) B3603905
theorem B1517881 : Blo 1064615 1517881 := bstep (se 2 (by rfl) ⟨569205, by rfl⟩ : syracuseStep 1517881 = 1138411) B1138411
theorem B2402963 : Blo 1064615 2402963 := bstep (se 1 (by rfl) ⟨1802222, by rfl⟩ : syracuseStep 2402963 = 3604445) B3604445
theorem B2403017 : Blo 1064615 2403017 := bstep (se 2 (by rfl) ⟨901131, by rfl⟩ : syracuseStep 2403017 = 1802263) B1802263
theorem B3844979 : Blo 1064615 3844979 := bstep (se 1 (by rfl) ⟨2883734, by rfl⟩ : syracuseStep 3844979 = 5767469) B5767469
theorem B8105021 : Blo 1064615 8105021 := bstep (se 3 (by rfl) ⟨1519691, by rfl⟩ : syracuseStep 8105021 = 3039383) B3039383
theorem B2698393 : Blo 1064615 2698393 := bstep (se 2 (by rfl) ⟨1011897, by rfl⟩ : syracuseStep 2698393 = 2023795) B2023795
theorem B2698555 : Blo 1064615 2698555 := bstep (se 1 (by rfl) ⟨2023916, by rfl⟩ : syracuseStep 2698555 = 4047833) B4047833
theorem B2403719 : Blo 1064615 2403719 := bstep (se 1 (by rfl) ⟨1802789, by rfl⟩ : syracuseStep 2403719 = 3605579) B3605579
theorem B2698697 : Blo 1064615 2698697 := bstep (se 2 (by rfl) ⟨1012011, by rfl⟩ : syracuseStep 2698697 = 2024023) B2024023
theorem B10530269 : Blo 1064615 10530269 := bstep (se 3 (by rfl) ⟨1974425, by rfl⟩ : syracuseStep 10530269 = 3948851) B3948851
theorem B1519111 : Blo 1064615 1519111 := bstep (se 1 (by rfl) ⟨1139333, by rfl⟩ : syracuseStep 1519111 = 2278667) B2278667
theorem B2403899 : Blo 1064615 2403899 := bstep (se 1 (by rfl) ⟨1802924, by rfl⟩ : syracuseStep 2403899 = 3605849) B3605849
theorem B2731639 : Blo 1064615 2731639 := bstep (se 1 (by rfl) ⟨2048729, by rfl⟩ : syracuseStep 2731639 = 4097459) B4097459
theorem B2404025 : Blo 1064615 2404025 := bstep (se 2 (by rfl) ⟨901509, by rfl⟩ : syracuseStep 2404025 = 1803019) B1803019
theorem B2469647 : Blo 1064615 2469647 := bstep (se 1 (by rfl) ⟨1852235, by rfl⟩ : syracuseStep 2469647 = 3704471) B3704471
theorem B2699041 : Blo 1064615 2699041 := bstep (se 2 (by rfl) ⟨1012140, by rfl⟩ : syracuseStep 2699041 = 2024281) B2024281
theorem B7679947 : Blo 1064615 7679947 := bstep (se 1 (by rfl) ⟨5759960, by rfl⟩ : syracuseStep 7679947 = 11519921) B11519921
theorem B2404367 : Blo 1064615 2404367 := bstep (se 1 (by rfl) ⟨1803275, by rfl⟩ : syracuseStep 2404367 = 3606551) B3606551
theorem B2404385 : Blo 1064615 2404385 := bstep (se 2 (by rfl) ⟨901644, by rfl⟩ : syracuseStep 2404385 = 1803289) B1803289
theorem B1519931 : Blo 1064615 1519931 := bstep (se 1 (by rfl) ⟨1139948, by rfl⟩ : syracuseStep 1519931 = 2279897) B2279897
theorem B3289459 : Blo 1064615 3289459 := bstep (se 1 (by rfl) ⟨2467094, by rfl⟩ : syracuseStep 3289459 = 4934189) B4934189
theorem B2699639 : Blo 1064615 2699639 := bstep (se 1 (by rfl) ⟨2024729, by rfl⟩ : syracuseStep 2699639 = 4049459) B4049459
theorem B4043155 : Blo 1064615 4043155 := bstep (se 1 (by rfl) ⟨3032366, by rfl⟩ : syracuseStep 4043155 = 6064733) B6064733
theorem B10957265 : Blo 1064615 10957265 := bstep (se 2 (by rfl) ⟨4108974, by rfl⟩ : syracuseStep 10957265 = 8217949) B8217949
theorem B5124809 : Blo 1064615 5124809 := bstep (se 2 (by rfl) ⟨1921803, by rfl⟩ : syracuseStep 5124809 = 3843607) B3843607
theorem B1520375 : Blo 1064615 1520375 := bstep (se 1 (by rfl) ⟨1140281, by rfl⟩ : syracuseStep 1520375 = 2280563) B2280563
theorem B1520569 : Blo 1064615 1520569 := bstep (se 2 (by rfl) ⟨570213, by rfl⟩ : syracuseStep 1520569 = 1140427) B1140427
theorem B6075395 : Blo 1064615 6075395 := bstep (se 1 (by rfl) ⟨4556546, by rfl⟩ : syracuseStep 6075395 = 9113093) B9113093
theorem B4109777 : Blo 1064615 4109777 := bstep (se 2 (by rfl) ⟨1541166, by rfl⟩ : syracuseStep 4109777 = 3082333) B3082333
theorem B21345869 : Blo 1064615 21345869 := bstep (se 3 (by rfl) ⟨4002350, by rfl⟩ : syracuseStep 21345869 = 8004701) B8004701
theorem B2700935 : Blo 1064615 2700935 := bstep (se 1 (by rfl) ⟨2025701, by rfl⟩ : syracuseStep 2700935 = 4051403) B4051403
theorem B2700985 : Blo 1064615 2700985 := bstep (se 2 (by rfl) ⟨1012869, by rfl⟩ : syracuseStep 2700985 = 2025739) B2025739
theorem B2275361 : Blo 1064615 2275361 := bstep (se 2 (by rfl) ⟨853260, by rfl⟩ : syracuseStep 2275361 = 1706521) B1706521
theorem B4044887 : Blo 1064615 4044887 := bstep (se 1 (by rfl) ⟨3033665, by rfl⟩ : syracuseStep 4044887 = 6067331) B6067331
theorem B1620155 : Blo 1064615 1620155 := bstep (se 1 (by rfl) ⟨1215116, by rfl⟩ : syracuseStep 1620155 = 2430233) B2430233
theorem B2701583 : Blo 1064615 2701583 := bstep (se 1 (by rfl) ⟨2026187, by rfl⟩ : syracuseStep 2701583 = 4052375) B4052375
theorem B13678865 : Blo 1064615 13678865 := bstep (se 2 (by rfl) ⟨5129574, by rfl⟩ : syracuseStep 13678865 = 10259149) B10259149
theorem B3291425 : Blo 1064615 3291425 := bstep (se 2 (by rfl) ⟨1234284, by rfl⟩ : syracuseStep 3291425 = 2468569) B2468569
theorem B8108423 : Blo 1064615 8108423 := bstep (se 1 (by rfl) ⟨6081317, by rfl⟩ : syracuseStep 8108423 = 12162635) B12162635
theorem B4045373 : Blo 1064615 4045373 := bstep (se 3 (by rfl) ⟨758507, by rfl⟩ : syracuseStep 4045373 = 1517015) B1517015
theorem B6830821 : Blo 1064615 6830821 := bstep (se 4 (by rfl) ⟨640389, by rfl⟩ : syracuseStep 6830821 = 1280779) B1280779
theorem B1096583 : Blo 1064615 1096583 := bstep (se 1 (by rfl) ⟨822437, by rfl⟩ : syracuseStep 1096583 = 1644875) B1644875
theorem B2702281 : Blo 1064615 2702281 := bstep (se 2 (by rfl) ⟨1013355, by rfl⟩ : syracuseStep 2702281 = 2026711) B2026711
theorem B3423293 : Blo 1064615 3423293 := bstep (se 3 (by rfl) ⟨641867, by rfl⟩ : syracuseStep 3423293 = 1283735) B1283735
theorem B2702423 : Blo 1064615 2702423 := bstep (se 1 (by rfl) ⟨2026817, by rfl⟩ : syracuseStep 2702423 = 4053635) B4053635
theorem B1621547 : Blo 1064615 1621547 := bstep (se 1 (by rfl) ⟨1216160, by rfl⟩ : syracuseStep 1621547 = 2432321) B2432321
theorem B1064635 : Blo 1064615 1064635 := bstep (se 1 (by rfl) ⟨798476, by rfl⟩ : syracuseStep 1064635 = 1596953) B1596953
theorem B1064711 : Blo 1064615 1064711 := bstep (se 1 (by rfl) ⟨798533, by rfl⟩ : syracuseStep 1064711 = 1597067) B1597067
theorem B1064719 : Blo 1064615 1064719 := bstep (se 1 (by rfl) ⟨798539, by rfl⟩ : syracuseStep 1064719 = 1597079) B1597079
theorem B2277163 : Blo 1064615 2277163 := bstep (se 1 (by rfl) ⟨1707872, by rfl⟩ : syracuseStep 2277163 = 3415745) B3415745
theorem B1064763 : Blo 1064615 1064763 := bstep (se 1 (by rfl) ⟨798572, by rfl⟩ : syracuseStep 1064763 = 1597145) B1597145
theorem B18235205 : Blo 1064615 18235205 := bstep (se 4 (by rfl) ⟨1709550, by rfl⟩ : syracuseStep 18235205 = 3419101) B3419101
theorem B11550539 : Blo 1064615 11550539 := bstep (se 1 (by rfl) ⟨8662904, by rfl⟩ : syracuseStep 11550539 = 17325809) B17325809
theorem B1064839 : Blo 1064615 1064839 := bstep (se 1 (by rfl) ⟨798629, by rfl⟩ : syracuseStep 1064839 = 1597259) B1597259
theorem B1064847 : Blo 1064615 1064847 := bstep (se 1 (by rfl) ⟨798635, by rfl⟩ : syracuseStep 1064847 = 1597271) B1597271
theorem B5390225 : Blo 1064615 5390225 := bstep (se 2 (by rfl) ⟨2021334, by rfl⟩ : syracuseStep 5390225 = 4042669) B4042669
theorem B20234137 : Blo 1064615 20234137 := bstep (se 2 (by rfl) ⟨7587801, by rfl⟩ : syracuseStep 20234137 = 15175603) B15175603
theorem B1064891 : Blo 1064615 1064891 := bstep (se 1 (by rfl) ⟨798668, by rfl⟩ : syracuseStep 1064891 = 1597337) B1597337
theorem B1064967 : Blo 1064615 1064967 := bstep (se 1 (by rfl) ⟨798725, by rfl⟩ : syracuseStep 1064967 = 1597451) B1597451
theorem B1064975 : Blo 1064615 1064975 := bstep (se 1 (by rfl) ⟨798731, by rfl⟩ : syracuseStep 1064975 = 1597463) B1597463
theorem B1065019 : Blo 1064615 1065019 := bstep (se 1 (by rfl) ⟨798764, by rfl⟩ : syracuseStep 1065019 = 1597529) B1597529
theorem B1065095 : Blo 1064615 1065095 := bstep (se 1 (by rfl) ⟨798821, by rfl⟩ : syracuseStep 1065095 = 1597643) B1597643
theorem B1065103 : Blo 1064615 1065103 := bstep (se 1 (by rfl) ⟨798827, by rfl⟩ : syracuseStep 1065103 = 1597655) B1597655
theorem B1065147 : Blo 1064615 1065147 := bstep (se 1 (by rfl) ⟨798860, by rfl⟩ : syracuseStep 1065147 = 1597721) B1597721
theorem B1065223 : Blo 1064615 1065223 := bstep (se 1 (by rfl) ⟨798917, by rfl⟩ : syracuseStep 1065223 = 1597835) B1597835
theorem B1065231 : Blo 1064615 1065231 := bstep (se 1 (by rfl) ⟨798923, by rfl⟩ : syracuseStep 1065231 = 1597847) B1597847
theorem B1065275 : Blo 1064615 1065275 := bstep (se 1 (by rfl) ⟨798956, by rfl⟩ : syracuseStep 1065275 = 1597913) B1597913
theorem B1065351 : Blo 1064615 1065351 := bstep (se 1 (by rfl) ⟨799013, by rfl⟩ : syracuseStep 1065351 = 1598027) B1598027
theorem B1065359 : Blo 1064615 1065359 := bstep (se 1 (by rfl) ⟨799019, by rfl⟩ : syracuseStep 1065359 = 1598039) B1598039
theorem B1065403 : Blo 1064615 1065403 := bstep (se 1 (by rfl) ⟨799052, by rfl⟩ : syracuseStep 1065403 = 1598105) B1598105
theorem B1065479 : Blo 1064615 1065479 := bstep (se 1 (by rfl) ⟨799109, by rfl⟩ : syracuseStep 1065479 = 1598219) B1598219
theorem B1065487 : Blo 1064615 1065487 := bstep (se 1 (by rfl) ⟨799115, by rfl⟩ : syracuseStep 1065487 = 1598231) B1598231
theorem B3654173 : Blo 1064615 3654173 := bstep (se 3 (by rfl) ⟨685157, by rfl⟩ : syracuseStep 3654173 = 1370315) B1370315
theorem B1065531 : Blo 1064615 1065531 := bstep (se 1 (by rfl) ⟨799148, by rfl⟩ : syracuseStep 1065531 = 1598297) B1598297
theorem B1065607 : Blo 1064615 1065607 := bstep (se 1 (by rfl) ⟨799205, by rfl⟩ : syracuseStep 1065607 = 1598411) B1598411
theorem B1065615 : Blo 1064615 1065615 := bstep (se 1 (by rfl) ⟨799211, by rfl⟩ : syracuseStep 1065615 = 1598423) B1598423
theorem B1065659 : Blo 1064615 1065659 := bstep (se 1 (by rfl) ⟨799244, by rfl⟩ : syracuseStep 1065659 = 1598489) B1598489
theorem B9126593 : Blo 1064615 9126593 := bstep (se 2 (by rfl) ⟨3422472, by rfl⟩ : syracuseStep 9126593 = 6844945) B6844945
theorem B1065735 : Blo 1064615 1065735 := bstep (se 1 (by rfl) ⟨799301, by rfl⟩ : syracuseStep 1065735 = 1598603) B1598603
theorem B1065743 : Blo 1064615 1065743 := bstep (se 1 (by rfl) ⟨799307, by rfl⟩ : syracuseStep 1065743 = 1598615) B1598615
theorem B8209201 : Blo 1064615 8209201 := bstep (se 2 (by rfl) ⟨3078450, by rfl⟩ : syracuseStep 8209201 = 6156901) B6156901
theorem B1065787 : Blo 1064615 1065787 := bstep (se 1 (by rfl) ⟨799340, by rfl⟩ : syracuseStep 1065787 = 1598681) B1598681
theorem B1065863 : Blo 1064615 1065863 := bstep (se 1 (by rfl) ⟨799397, by rfl⟩ : syracuseStep 1065863 = 1598795) B1598795
theorem B1065871 : Blo 1064615 1065871 := bstep (se 1 (by rfl) ⟨799403, by rfl⟩ : syracuseStep 1065871 = 1598807) B1598807
theorem B1065915 : Blo 1064615 1065915 := bstep (se 1 (by rfl) ⟨799436, by rfl⟩ : syracuseStep 1065915 = 1598873) B1598873
theorem B1065991 : Blo 1064615 1065991 := bstep (se 1 (by rfl) ⟨799493, by rfl⟩ : syracuseStep 1065991 = 1598987) B1598987
theorem B1065999 : Blo 1064615 1065999 := bstep (se 1 (by rfl) ⟨799499, by rfl⟩ : syracuseStep 1065999 = 1598999) B1598999
theorem B5194775 : Blo 1064615 5194775 := bstep (se 1 (by rfl) ⟨3896081, by rfl⟩ : syracuseStep 5194775 = 7792163) B7792163
theorem B3032093 : Blo 1064615 3032093 := bstep (se 3 (by rfl) ⟨568517, by rfl⟩ : syracuseStep 3032093 = 1137035) B1137035
theorem B1066043 : Blo 1064615 1066043 := bstep (se 1 (by rfl) ⟨799532, by rfl⟩ : syracuseStep 1066043 = 1599065) B1599065
theorem B2704499 : Blo 1064615 2704499 := bstep (se 1 (by rfl) ⟨2028374, by rfl⟩ : syracuseStep 2704499 = 4056749) B4056749
theorem B1066119 : Blo 1064615 1066119 := bstep (se 1 (by rfl) ⟨799589, by rfl⟩ : syracuseStep 1066119 = 1599179) B1599179
theorem B1066127 : Blo 1064615 1066127 := bstep (se 1 (by rfl) ⟨799595, by rfl⟩ : syracuseStep 1066127 = 1599191) B1599191
theorem B2278547 : Blo 1064615 2278547 := bstep (se 1 (by rfl) ⟨1708910, by rfl⟩ : syracuseStep 2278547 = 3417821) B3417821
theorem B1066171 : Blo 1064615 1066171 := bstep (se 1 (by rfl) ⟨799628, by rfl⟩ : syracuseStep 1066171 = 1599257) B1599257
theorem B1066247 : Blo 1064615 1066247 := bstep (se 1 (by rfl) ⟨799685, by rfl⟩ : syracuseStep 1066247 = 1599371) B1599371
theorem B1066255 : Blo 1064615 1066255 := bstep (se 1 (by rfl) ⟨799691, by rfl⟩ : syracuseStep 1066255 = 1599383) B1599383
theorem B1066299 : Blo 1064615 1066299 := bstep (se 1 (by rfl) ⟨799724, by rfl⟩ : syracuseStep 1066299 = 1599449) B1599449
theorem B1066375 : Blo 1064615 1066375 := bstep (se 1 (by rfl) ⟨799781, by rfl⟩ : syracuseStep 1066375 = 1599563) B1599563
theorem B1066383 : Blo 1064615 1066383 := bstep (se 1 (by rfl) ⟨799787, by rfl⟩ : syracuseStep 1066383 = 1599575) B1599575
theorem B1066427 : Blo 1064615 1066427 := bstep (se 1 (by rfl) ⟨799820, by rfl⟩ : syracuseStep 1066427 = 1599641) B1599641
theorem B7685597 : Blo 1064615 7685597 := bstep (se 3 (by rfl) ⟨1441049, by rfl⟩ : syracuseStep 7685597 = 2882099) B2882099
theorem B1066503 : Blo 1064615 1066503 := bstep (se 1 (by rfl) ⟨799877, by rfl⟩ : syracuseStep 1066503 = 1599755) B1599755
theorem B1066511 : Blo 1064615 1066511 := bstep (se 1 (by rfl) ⟨799883, by rfl⟩ : syracuseStep 1066511 = 1599767) B1599767
theorem B1066555 : Blo 1064615 1066555 := bstep (se 1 (by rfl) ⟨799916, by rfl⟩ : syracuseStep 1066555 = 1599833) B1599833
theorem B1066631 : Blo 1064615 1066631 := bstep (se 1 (by rfl) ⟨799973, by rfl⟩ : syracuseStep 1066631 = 1599947) B1599947
theorem B1066639 : Blo 1064615 1066639 := bstep (se 1 (by rfl) ⟨799979, by rfl⟩ : syracuseStep 1066639 = 1599959) B1599959
theorem B1066683 : Blo 1064615 1066683 := bstep (se 1 (by rfl) ⟨800012, by rfl⟩ : syracuseStep 1066683 = 1600025) B1600025
theorem B3032777 : Blo 1064615 3032777 := bstep (se 2 (by rfl) ⟨1137291, by rfl⟩ : syracuseStep 3032777 = 2274583) B2274583
theorem B1066759 : Blo 1064615 1066759 := bstep (se 1 (by rfl) ⟨800069, by rfl⟩ : syracuseStep 1066759 = 1600139) B1600139
theorem B1066767 : Blo 1064615 1066767 := bstep (se 1 (by rfl) ⟨800075, by rfl⟩ : syracuseStep 1066767 = 1600151) B1600151
theorem B1066811 : Blo 1064615 1066811 := bstep (se 1 (by rfl) ⟨800108, by rfl⟩ : syracuseStep 1066811 = 1600217) B1600217
theorem B4048775 : Blo 1064615 4048775 := bstep (se 1 (by rfl) ⟨3036581, by rfl⟩ : syracuseStep 4048775 = 6073163) B6073163
theorem B1066887 : Blo 1064615 1066887 := bstep (se 1 (by rfl) ⟨800165, by rfl⟩ : syracuseStep 1066887 = 1600331) B1600331
theorem B1197967 : Blo 1064615 1197967 := bstep (se 1 (by rfl) ⟨898475, by rfl⟩ : syracuseStep 1197967 = 1796951) B1796951
theorem B1066895 : Blo 1064615 1066895 := bstep (se 1 (by rfl) ⟨800171, by rfl⟩ : syracuseStep 1066895 = 1600343) B1600343
theorem B2049977 : Blo 1064615 2049977 := bstep (se 2 (by rfl) ⟨768741, by rfl⟩ : syracuseStep 2049977 = 1537483) B1537483
theorem B1460153 : Blo 1064615 1460153 := bstep (se 2 (by rfl) ⟨547557, by rfl⟩ : syracuseStep 1460153 = 1095115) B1095115
theorem B1066939 : Blo 1064615 1066939 := bstep (se 1 (by rfl) ⟨800204, by rfl⟩ : syracuseStep 1066939 = 1600409) B1600409
theorem B5392331 : Blo 1064615 5392331 := bstep (se 1 (by rfl) ⟨4044248, by rfl⟩ : syracuseStep 5392331 = 8088497) B8088497
theorem B1067015 : Blo 1064615 1067015 := bstep (se 1 (by rfl) ⟨800261, by rfl⟩ : syracuseStep 1067015 = 1600523) B1600523
theorem B1067023 : Blo 1064615 1067023 := bstep (se 1 (by rfl) ⟨800267, by rfl⟩ : syracuseStep 1067023 = 1600535) B1600535
theorem B1067067 : Blo 1064615 1067067 := bstep (se 1 (by rfl) ⟨800300, by rfl⟩ : syracuseStep 1067067 = 1600601) B1600601
theorem B1067143 : Blo 1064615 1067143 := bstep (se 1 (by rfl) ⟨800357, by rfl⟩ : syracuseStep 1067143 = 1600715) B1600715
theorem B1067151 : Blo 1064615 1067151 := bstep (se 1 (by rfl) ⟨800363, by rfl⟩ : syracuseStep 1067151 = 1600727) B1600727
theorem B1067195 : Blo 1064615 1067195 := bstep (se 1 (by rfl) ⟨800396, by rfl⟩ : syracuseStep 1067195 = 1600793) B1600793
theorem B5130497 : Blo 1064615 5130497 := bstep (se 2 (by rfl) ⟨1923936, by rfl⟩ : syracuseStep 5130497 = 3847873) B3847873
theorem B1067271 : Blo 1064615 1067271 := bstep (se 1 (by rfl) ⟨800453, by rfl⟩ : syracuseStep 1067271 = 1600907) B1600907
theorem B3033359 : Blo 1064615 3033359 := bstep (se 1 (by rfl) ⟨2275019, by rfl⟩ : syracuseStep 3033359 = 4550039) B4550039
theorem B5392655 : Blo 1064615 5392655 := bstep (se 1 (by rfl) ⟨4044491, by rfl⟩ : syracuseStep 5392655 = 8088983) B8088983
theorem B1067279 : Blo 1064615 1067279 := bstep (se 1 (by rfl) ⟨800459, by rfl⟩ : syracuseStep 1067279 = 1600919) B1600919
theorem B1067323 : Blo 1064615 1067323 := bstep (se 1 (by rfl) ⟨800492, by rfl⟩ : syracuseStep 1067323 = 1600985) B1600985
theorem B1198471 : Blo 1064615 1198471 := bstep (se 1 (by rfl) ⟨898853, by rfl⟩ : syracuseStep 1198471 = 1797707) B1797707
theorem B1067399 : Blo 1064615 1067399 := bstep (se 1 (by rfl) ⟨800549, by rfl⟩ : syracuseStep 1067399 = 1601099) B1601099
theorem B1067407 : Blo 1064615 1067407 := bstep (se 1 (by rfl) ⟨800555, by rfl⟩ : syracuseStep 1067407 = 1601111) B1601111
theorem B6834617 : Blo 1064615 6834617 := bstep (se 2 (by rfl) ⟨2562981, by rfl⟩ : syracuseStep 6834617 = 5125963) B5125963
theorem B6080953 : Blo 1064615 6080953 := bstep (se 2 (by rfl) ⟨2280357, by rfl⟩ : syracuseStep 6080953 = 4560715) B4560715
theorem B1067451 : Blo 1064615 1067451 := bstep (se 1 (by rfl) ⟨800588, by rfl⟩ : syracuseStep 1067451 = 1601177) B1601177
theorem B1067527 : Blo 1064615 1067527 := bstep (se 1 (by rfl) ⟨800645, by rfl⟩ : syracuseStep 1067527 = 1601291) B1601291
theorem B1067535 : Blo 1064615 1067535 := bstep (se 1 (by rfl) ⟨800651, by rfl⟩ : syracuseStep 1067535 = 1601303) B1601303
theorem B1198651 : Blo 1064615 1198651 := bstep (se 1 (by rfl) ⟨898988, by rfl⟩ : syracuseStep 1198651 = 1797977) B1797977
theorem B1067579 : Blo 1064615 1067579 := bstep (se 1 (by rfl) ⟨800684, by rfl⟩ : syracuseStep 1067579 = 1601369) B1601369
theorem B23382593 : Blo 1064615 23382593 := bstep (se 2 (by rfl) ⟨8768472, by rfl⟩ : syracuseStep 23382593 = 17536945) B17536945
theorem B1067655 : Blo 1064615 1067655 := bstep (se 1 (by rfl) ⟨800741, by rfl⟩ : syracuseStep 1067655 = 1601483) B1601483
theorem B1067663 : Blo 1064615 1067663 := bstep (se 1 (by rfl) ⟨800747, by rfl⟩ : syracuseStep 1067663 = 1601495) B1601495
theorem B1067707 : Blo 1064615 1067707 := bstep (se 1 (by rfl) ⟨800780, by rfl⟩ : syracuseStep 1067707 = 1601561) B1601561
theorem B1067783 : Blo 1064615 1067783 := bstep (se 1 (by rfl) ⟨800837, by rfl⟩ : syracuseStep 1067783 = 1601675) B1601675
theorem B1067791 : Blo 1064615 1067791 := bstep (se 1 (by rfl) ⟨800843, by rfl⟩ : syracuseStep 1067791 = 1601687) B1601687
theorem B1067835 : Blo 1064615 1067835 := bstep (se 1 (by rfl) ⟨800876, by rfl⟩ : syracuseStep 1067835 = 1601753) B1601753
theorem B5131097 : Blo 1064615 5131097 := bstep (se 2 (by rfl) ⟨1924161, by rfl⟩ : syracuseStep 5131097 = 3848323) B3848323
theorem B41503589 : Blo 1064615 41503589 := bstep (se 4 (by rfl) ⟨3890961, by rfl⟩ : syracuseStep 41503589 = 7781923) B7781923
theorem B1067911 : Blo 1064615 1067911 := bstep (se 1 (by rfl) ⟨800933, by rfl⟩ : syracuseStep 1067911 = 1601867) B1601867
theorem B1067919 : Blo 1064615 1067919 := bstep (se 1 (by rfl) ⟨800939, by rfl⟩ : syracuseStep 1067919 = 1601879) B1601879
theorem B1067963 : Blo 1064615 1067963 := bstep (se 1 (by rfl) ⟨800972, by rfl⟩ : syracuseStep 1067963 = 1601945) B1601945
theorem B1068039 : Blo 1064615 1068039 := bstep (se 1 (by rfl) ⟨801029, by rfl⟩ : syracuseStep 1068039 = 1602059) B1602059
theorem B1199119 : Blo 1064615 1199119 := bstep (se 1 (by rfl) ⟨899339, by rfl⟩ : syracuseStep 1199119 = 1798679) B1798679
theorem B1068047 : Blo 1064615 1068047 := bstep (se 1 (by rfl) ⟨801035, by rfl⟩ : syracuseStep 1068047 = 1602071) B1602071
theorem B1068091 : Blo 1064615 1068091 := bstep (se 1 (by rfl) ⟨801068, by rfl⟩ : syracuseStep 1068091 = 1602137) B1602137
theorem B1068167 : Blo 1064615 1068167 := bstep (se 1 (by rfl) ⟨801125, by rfl⟩ : syracuseStep 1068167 = 1602251) B1602251
theorem B1068175 : Blo 1064615 1068175 := bstep (se 1 (by rfl) ⟨801131, by rfl⟩ : syracuseStep 1068175 = 1602263) B1602263
theorem B1068219 : Blo 1064615 1068219 := bstep (se 1 (by rfl) ⟨801164, by rfl⟩ : syracuseStep 1068219 = 1602329) B1602329
theorem B2280649 : Blo 1064615 2280649 := bstep (se 2 (by rfl) ⟨855243, by rfl⟩ : syracuseStep 2280649 = 1710487) B1710487
theorem B1068295 : Blo 1064615 1068295 := bstep (se 1 (by rfl) ⟨801221, by rfl⟩ : syracuseStep 1068295 = 1602443) B1602443
theorem B1068303 : Blo 1064615 1068303 := bstep (se 1 (by rfl) ⟨801227, by rfl⟩ : syracuseStep 1068303 = 1602455) B1602455
theorem B15355169 : Blo 1064615 15355169 := bstep (se 2 (by rfl) ⟨5758188, by rfl⟩ : syracuseStep 15355169 = 11516377) B11516377
theorem B1068347 : Blo 1064615 1068347 := bstep (se 1 (by rfl) ⟨801260, by rfl⟩ : syracuseStep 1068347 = 1602521) B1602521
theorem B2706803 : Blo 1064615 2706803 := bstep (se 1 (by rfl) ⟨2030102, by rfl⟩ : syracuseStep 2706803 = 4060205) B4060205
theorem B1068423 : Blo 1064615 1068423 := bstep (se 1 (by rfl) ⟨801317, by rfl⟩ : syracuseStep 1068423 = 1602635) B1602635
theorem B1068431 : Blo 1064615 1068431 := bstep (se 1 (by rfl) ⟨801323, by rfl⟩ : syracuseStep 1068431 = 1602647) B1602647
theorem B1068475 : Blo 1064615 1068475 := bstep (se 1 (by rfl) ⟨801356, by rfl⟩ : syracuseStep 1068475 = 1602713) B1602713
theorem B1199623 : Blo 1064615 1199623 := bstep (se 1 (by rfl) ⟨899717, by rfl⟩ : syracuseStep 1199623 = 1799435) B1799435
theorem B1068551 : Blo 1064615 1068551 := bstep (se 1 (by rfl) ⟨801413, by rfl⟩ : syracuseStep 1068551 = 1602827) B1602827
theorem B1068559 : Blo 1064615 1068559 := bstep (se 1 (by rfl) ⟨801419, by rfl⟩ : syracuseStep 1068559 = 1602839) B1602839
theorem B2051617 : Blo 1064615 2051617 := bstep (se 2 (by rfl) ⟨769356, by rfl⟩ : syracuseStep 2051617 = 1538713) B1538713
theorem B1068603 : Blo 1064615 1068603 := bstep (se 1 (by rfl) ⟨801452, by rfl⟩ : syracuseStep 1068603 = 1602905) B1602905
theorem B9227843 : Blo 1064615 9227843 := bstep (se 1 (by rfl) ⟨6920882, by rfl⟩ : syracuseStep 9227843 = 13841765) B13841765
theorem B13684301 : Blo 1064615 13684301 := bstep (se 3 (by rfl) ⟨2565806, by rfl⟩ : syracuseStep 13684301 = 5131613) B5131613
theorem B3034759 : Blo 1064615 3034759 := bstep (se 1 (by rfl) ⟨2276069, by rfl⟩ : syracuseStep 3034759 = 4552139) B4552139
theorem B1199803 : Blo 1064615 1199803 := bstep (se 1 (by rfl) ⟨899852, by rfl⟩ : syracuseStep 1199803 = 1799705) B1799705
theorem B5394113 : Blo 1064615 5394113 := bstep (se 2 (by rfl) ⟨2022792, by rfl⟩ : syracuseStep 5394113 = 4045585) B4045585
theorem B3035033 : Blo 1064615 3035033 := bstep (se 2 (by rfl) ⟨1138137, by rfl⟩ : syracuseStep 3035033 = 2276275) B2276275
theorem B5197891 : Blo 1064615 5197891 := bstep (se 1 (by rfl) ⟨3898418, by rfl⟩ : syracuseStep 5197891 = 7796837) B7796837
theorem B1200271 : Blo 1064615 1200271 := bstep (se 1 (by rfl) ⟨900203, by rfl⟩ : syracuseStep 1200271 = 1800407) B1800407
theorem B6475949 : Blo 1064615 6475949 := bstep (se 3 (by rfl) ⟨1214240, by rfl⟩ : syracuseStep 6475949 = 2428481) B2428481
theorem B2740751 : Blo 1064615 2740751 := bstep (se 1 (by rfl) ⟨2055563, by rfl⟩ : syracuseStep 2740751 = 4111127) B4111127
theorem B1200775 : Blo 1064615 1200775 := bstep (se 1 (by rfl) ⟨900581, by rfl⟩ : syracuseStep 1200775 = 1801163) B1801163
theorem B1200955 : Blo 1064615 1200955 := bstep (se 1 (by rfl) ⟨900716, by rfl⟩ : syracuseStep 1200955 = 1801433) B1801433
theorem B5395409 : Blo 1064615 5395409 := bstep (se 2 (by rfl) ⟨2023278, by rfl⟩ : syracuseStep 5395409 = 4046557) B4046557
theorem B3036275 : Blo 1064615 3036275 := bstep (se 1 (by rfl) ⟨2277206, by rfl⟩ : syracuseStep 3036275 = 4554413) B4554413
theorem B1201423 : Blo 1064615 1201423 := bstep (se 1 (by rfl) ⟨901067, by rfl⟩ : syracuseStep 1201423 = 1802135) B1802135
theorem B1201927 : Blo 1064615 1201927 := bstep (se 1 (by rfl) ⟨901445, by rfl⟩ : syracuseStep 1201927 = 1802891) B1802891
theorem B2021267 : Blo 1064615 2021267 := bstep (se 1 (by rfl) ⟨1515950, by rfl⟩ : syracuseStep 2021267 = 3031901) B3031901
theorem B3594131 : Blo 1064615 3594131 := bstep (se 1 (by rfl) ⟨2695598, by rfl⟩ : syracuseStep 3594131 = 5391197) B5391197
theorem B1202107 : Blo 1064615 1202107 := bstep (se 1 (by rfl) ⟨901580, by rfl⟩ : syracuseStep 1202107 = 1803161) B1803161
theorem B9099287 : Blo 1064615 9099287 := bstep (se 1 (by rfl) ⟨6824465, by rfl⟩ : syracuseStep 9099287 = 13648931) B13648931
theorem B5134727 : Blo 1064615 5134727 := bstep (se 1 (by rfl) ⟨3851045, by rfl⟩ : syracuseStep 5134727 = 7702091) B7702091
theorem B4872595 : Blo 1064615 4872595 := bstep (se 1 (by rfl) ⟨3654446, by rfl⟩ : syracuseStep 4872595 = 7308893) B7308893
theorem B9230915 : Blo 1064615 9230915 := bstep (se 1 (by rfl) ⟨6923186, by rfl⟩ : syracuseStep 9230915 = 13846373) B13846373
theorem B4676183 : Blo 1064615 4676183 := bstep (se 1 (by rfl) ⟨3507137, by rfl⟩ : syracuseStep 4676183 = 7014275) B7014275
theorem B9231193 : Blo 1064615 9231193 := bstep (se 2 (by rfl) ⟨3461697, by rfl⟩ : syracuseStep 9231193 = 6923395) B6923395
theorem B5397515 : Blo 1064615 5397515 := bstep (se 1 (by rfl) ⟨4048136, by rfl⟩ : syracuseStep 5397515 = 8096273) B8096273
theorem B1924139 : Blo 1064615 1924139 := bstep (se 1 (by rfl) ⟨1443104, by rfl⟩ : syracuseStep 1924139 = 2886209) B2886209
theorem B9100349 : Blo 1064615 9100349 := bstep (se 3 (by rfl) ⟨1706315, by rfl⟩ : syracuseStep 9100349 = 3412631) B3412631
theorem B5397677 : Blo 1064615 5397677 := bstep (se 3 (by rfl) ⟨1012064, by rfl⟩ : syracuseStep 5397677 = 2024129) B2024129
theorem B3595535 : Blo 1064615 3595535 := bstep (se 1 (by rfl) ⟨2696651, by rfl⟩ : syracuseStep 3595535 = 5393303) B5393303
theorem B2022671 : Blo 1064615 2022671 := bstep (se 1 (by rfl) ⟨1517003, by rfl⟩ : syracuseStep 2022671 = 3034007) B3034007
theorem B98557397 : Blo 1064615 98557397 := bstep (se 7 (by rfl) ⟨1154969, by rfl⟩ : syracuseStep 98557397 = 2309939) B2309939
theorem B1596935 : Blo 1064615 1596935 := bstep (se 1 (by rfl) ⟨1197701, by rfl⟩ : syracuseStep 1596935 = 2395403) B2395403
theorem B3038735 : Blo 1064615 3038735 := bstep (se 1 (by rfl) ⟨2279051, by rfl⟩ : syracuseStep 3038735 = 4558103) B4558103
theorem B3595805 : Blo 1064615 3595805 := bstep (se 3 (by rfl) ⟨674213, by rfl⟩ : syracuseStep 3595805 = 1348427) B1348427
theorem B1596971 : Blo 1064615 1596971 := bstep (se 1 (by rfl) ⟨1197728, by rfl⟩ : syracuseStep 1596971 = 2395457) B2395457
theorem B1597001 : Blo 1064615 1597001 := bstep (se 2 (by rfl) ⟨598875, by rfl⟩ : syracuseStep 1597001 = 1197751) B1197751
theorem B1597115 : Blo 1064615 1597115 := bstep (se 1 (by rfl) ⟨1197836, by rfl⟩ : syracuseStep 1597115 = 2395673) B2395673
theorem B1597175 : Blo 1064615 1597175 := bstep (se 1 (by rfl) ⟨1197881, by rfl⟩ : syracuseStep 1597175 = 2395763) B2395763
theorem B1597199 : Blo 1064615 1597199 := bstep (se 1 (by rfl) ⟨1197899, by rfl⟩ : syracuseStep 1597199 = 2395799) B2395799
theorem B2023211 : Blo 1064615 2023211 := bstep (se 1 (by rfl) ⟨1517408, by rfl⟩ : syracuseStep 2023211 = 3034817) B3034817
theorem B28139309 : Blo 1064615 28139309 := bstep (se 3 (by rfl) ⟨5276120, by rfl⟩ : syracuseStep 28139309 = 10552241) B10552241
theorem B1597241 : Blo 1064615 1597241 := bstep (se 2 (by rfl) ⟨598965, by rfl⟩ : syracuseStep 1597241 = 1197931) B1197931
theorem B1597319 : Blo 1064615 1597319 := bstep (se 1 (by rfl) ⟨1197989, by rfl⟩ : syracuseStep 1597319 = 2395979) B2395979
theorem B1597355 : Blo 1064615 1597355 := bstep (se 1 (by rfl) ⟨1198016, by rfl⟩ : syracuseStep 1597355 = 2396033) B2396033
theorem B1597385 : Blo 1064615 1597385 := bstep (se 2 (by rfl) ⟨599019, by rfl⟩ : syracuseStep 1597385 = 1198039) B1198039
theorem B1597499 : Blo 1064615 1597499 := bstep (se 1 (by rfl) ⟨1198124, by rfl⟩ : syracuseStep 1597499 = 2396249) B2396249
theorem B1597559 : Blo 1064615 1597559 := bstep (se 1 (by rfl) ⟨1198169, by rfl⟩ : syracuseStep 1597559 = 2396339) B2396339
theorem B1597583 : Blo 1064615 1597583 := bstep (se 1 (by rfl) ⟨1198187, by rfl⟩ : syracuseStep 1597583 = 2396375) B2396375
theorem B1597625 : Blo 1064615 1597625 := bstep (se 2 (by rfl) ⟨599109, by rfl⟩ : syracuseStep 1597625 = 1198219) B1198219
theorem B1597703 : Blo 1064615 1597703 := bstep (se 1 (by rfl) ⟨1198277, by rfl⟩ : syracuseStep 1597703 = 2396555) B2396555
theorem B1597739 : Blo 1064615 1597739 := bstep (se 1 (by rfl) ⟨1198304, by rfl⟩ : syracuseStep 1597739 = 2396609) B2396609
theorem B1597769 : Blo 1064615 1597769 := bstep (se 2 (by rfl) ⟨599163, by rfl⟩ : syracuseStep 1597769 = 1198327) B1198327
theorem B1597883 : Blo 1064615 1597883 := bstep (se 1 (by rfl) ⟨1198412, by rfl⟩ : syracuseStep 1597883 = 2396825) B2396825
theorem B1597943 : Blo 1064615 1597943 := bstep (se 1 (by rfl) ⟨1198457, by rfl⟩ : syracuseStep 1597943 = 2396915) B2396915
theorem B1597967 : Blo 1064615 1597967 := bstep (se 1 (by rfl) ⟨1198475, by rfl⟩ : syracuseStep 1597967 = 2396951) B2396951
theorem B1598009 : Blo 1064615 1598009 := bstep (se 2 (by rfl) ⟨599253, by rfl⟩ : syracuseStep 1598009 = 1198507) B1198507
theorem B1598087 : Blo 1064615 1598087 := bstep (se 1 (by rfl) ⟨1198565, by rfl⟩ : syracuseStep 1598087 = 2397131) B2397131
theorem B1598123 : Blo 1064615 1598123 := bstep (se 1 (by rfl) ⟨1198592, by rfl⟩ : syracuseStep 1598123 = 2397185) B2397185
theorem B1598153 : Blo 1064615 1598153 := bstep (se 2 (by rfl) ⟨599307, by rfl⟩ : syracuseStep 1598153 = 1198615) B1198615
theorem B5399297 : Blo 1064615 5399297 := bstep (se 2 (by rfl) ⟨2024736, by rfl⟩ : syracuseStep 5399297 = 4049473) B4049473
theorem B1598267 : Blo 1064615 1598267 := bstep (se 1 (by rfl) ⟨1198700, by rfl⟩ : syracuseStep 1598267 = 2397401) B2397401
theorem B1598327 : Blo 1064615 1598327 := bstep (se 1 (by rfl) ⟨1198745, by rfl⟩ : syracuseStep 1598327 = 2397491) B2397491
theorem B2024327 : Blo 1064615 2024327 := bstep (se 1 (by rfl) ⟨1518245, by rfl⟩ : syracuseStep 2024327 = 3036491) B3036491
theorem B1598351 : Blo 1064615 1598351 := bstep (se 1 (by rfl) ⟨1198763, by rfl⟩ : syracuseStep 1598351 = 2397527) B2397527
theorem B3597209 : Blo 1064615 3597209 := bstep (se 2 (by rfl) ⟨1348953, by rfl⟩ : syracuseStep 3597209 = 2697907) B2697907
theorem B1598393 : Blo 1064615 1598393 := bstep (se 2 (by rfl) ⟨599397, by rfl⟩ : syracuseStep 1598393 = 1198795) B1198795
theorem B1598471 : Blo 1064615 1598471 := bstep (se 1 (by rfl) ⟨1198853, by rfl⟩ : syracuseStep 1598471 = 2397707) B2397707
theorem B1598507 : Blo 1064615 1598507 := bstep (se 1 (by rfl) ⟨1198880, by rfl⟩ : syracuseStep 1598507 = 2397761) B2397761
theorem B1598537 : Blo 1064615 1598537 := bstep (se 2 (by rfl) ⟨599451, by rfl⟩ : syracuseStep 1598537 = 1198903) B1198903
theorem B3040375 : Blo 1064615 3040375 := bstep (se 1 (by rfl) ⟨2280281, by rfl⟩ : syracuseStep 3040375 = 4560563) B4560563
theorem B2188435 : Blo 1064615 2188435 := bstep (se 1 (by rfl) ⟨1641326, by rfl⟩ : syracuseStep 2188435 = 3282653) B3282653
theorem B3040409 : Blo 1064615 3040409 := bstep (se 2 (by rfl) ⟨1140153, by rfl⟩ : syracuseStep 3040409 = 2280307) B2280307
theorem B1598651 : Blo 1064615 1598651 := bstep (se 1 (by rfl) ⟨1198988, by rfl⟩ : syracuseStep 1598651 = 2397977) B2397977
theorem B1598711 : Blo 1064615 1598711 := bstep (se 1 (by rfl) ⟨1199033, by rfl⟩ : syracuseStep 1598711 = 2398067) B2398067
theorem B3040523 : Blo 1064615 3040523 := bstep (se 1 (by rfl) ⟨2280392, by rfl⟩ : syracuseStep 3040523 = 4560785) B4560785
theorem B1598735 : Blo 1064615 1598735 := bstep (se 1 (by rfl) ⟨1199051, by rfl⟩ : syracuseStep 1598735 = 2398103) B2398103
theorem B1369387 : Blo 1064615 1369387 := bstep (se 1 (by rfl) ⟨1027040, by rfl⟩ : syracuseStep 1369387 = 2054081) B2054081
theorem B1598777 : Blo 1064615 1598777 := bstep (se 2 (by rfl) ⟨599541, by rfl⟩ : syracuseStep 1598777 = 1199083) B1199083
theorem B1598855 : Blo 1064615 1598855 := bstep (se 1 (by rfl) ⟨1199141, by rfl⟩ : syracuseStep 1598855 = 2398283) B2398283
theorem B2024851 : Blo 1064615 2024851 := bstep (se 1 (by rfl) ⟨1518638, by rfl⟩ : syracuseStep 2024851 = 3037277) B3037277
theorem B1598891 : Blo 1064615 1598891 := bstep (se 1 (by rfl) ⟨1199168, by rfl⟩ : syracuseStep 1598891 = 2398337) B2398337
theorem B1598921 : Blo 1064615 1598921 := bstep (se 2 (by rfl) ⟨599595, by rfl⟩ : syracuseStep 1598921 = 1199191) B1199191
theorem B5400107 : Blo 1064615 5400107 := bstep (se 1 (by rfl) ⟨4050080, by rfl⟩ : syracuseStep 5400107 = 8100161) B8100161
theorem B1599035 : Blo 1064615 1599035 := bstep (se 1 (by rfl) ⟨1199276, by rfl⟩ : syracuseStep 1599035 = 2398553) B2398553
theorem B3597911 : Blo 1064615 3597911 := bstep (se 1 (by rfl) ⟨2698433, by rfl⟩ : syracuseStep 3597911 = 5396867) B5396867
theorem B1599095 : Blo 1064615 1599095 := bstep (se 1 (by rfl) ⟨1199321, by rfl⟩ : syracuseStep 1599095 = 2398643) B2398643
theorem B1599119 : Blo 1064615 1599119 := bstep (se 1 (by rfl) ⟨1199339, by rfl⟩ : syracuseStep 1599119 = 2398679) B2398679
theorem B1140367 : Blo 1064615 1140367 := bstep (se 1 (by rfl) ⟨855275, by rfl⟩ : syracuseStep 1140367 = 1710551) B1710551
theorem B1599161 : Blo 1064615 1599161 := bstep (se 2 (by rfl) ⟨599685, by rfl⟩ : syracuseStep 1599161 = 1199371) B1199371
theorem B1599239 : Blo 1064615 1599239 := bstep (se 1 (by rfl) ⟨1199429, by rfl⟩ : syracuseStep 1599239 = 2398859) B2398859
theorem B1599275 : Blo 1064615 1599275 := bstep (se 1 (by rfl) ⟨1199456, by rfl⟩ : syracuseStep 1599275 = 2398913) B2398913
theorem B1599305 : Blo 1064615 1599305 := bstep (se 2 (by rfl) ⟨599739, by rfl⟩ : syracuseStep 1599305 = 1199479) B1199479
theorem B1599419 : Blo 1064615 1599419 := bstep (se 1 (by rfl) ⟨1199564, by rfl⟩ : syracuseStep 1599419 = 2399129) B2399129
theorem B1599479 : Blo 1064615 1599479 := bstep (se 1 (by rfl) ⟨1199609, by rfl⟩ : syracuseStep 1599479 = 2399219) B2399219
theorem B1140743 : Blo 1064615 1140743 := bstep (se 1 (by rfl) ⟨855557, by rfl⟩ : syracuseStep 1140743 = 1711115) B1711115
theorem B1599503 : Blo 1064615 1599503 := bstep (se 1 (by rfl) ⟨1199627, by rfl⟩ : syracuseStep 1599503 = 2399255) B2399255
theorem B1599545 : Blo 1064615 1599545 := bstep (se 2 (by rfl) ⟨599829, by rfl⟩ : syracuseStep 1599545 = 1199659) B1199659
theorem B3598397 : Blo 1064615 3598397 := bstep (se 3 (by rfl) ⟨674699, by rfl⟩ : syracuseStep 3598397 = 1349399) B1349399
theorem B1599623 : Blo 1064615 1599623 := bstep (se 1 (by rfl) ⟨1199717, by rfl⟩ : syracuseStep 1599623 = 2399435) B2399435
theorem B1599659 : Blo 1064615 1599659 := bstep (se 1 (by rfl) ⟨1199744, by rfl⟩ : syracuseStep 1599659 = 2399489) B2399489
theorem B1599689 : Blo 1064615 1599689 := bstep (se 2 (by rfl) ⟨599883, by rfl⟩ : syracuseStep 1599689 = 1199767) B1199767
theorem B6482177 : Blo 1064615 6482177 := bstep (se 2 (by rfl) ⟨2430816, by rfl⟩ : syracuseStep 6482177 = 4861633) B4861633
theorem B1599803 : Blo 1064615 1599803 := bstep (se 1 (by rfl) ⟨1199852, by rfl⟩ : syracuseStep 1599803 = 2399705) B2399705
theorem B3041651 : Blo 1064615 3041651 := bstep (se 1 (by rfl) ⟨2281238, by rfl⟩ : syracuseStep 3041651 = 4562477) B4562477
theorem B1599863 : Blo 1064615 1599863 := bstep (se 1 (by rfl) ⟨1199897, by rfl⟩ : syracuseStep 1599863 = 2399795) B2399795
theorem B1599887 : Blo 1064615 1599887 := bstep (se 1 (by rfl) ⟨1199915, by rfl⟩ : syracuseStep 1599887 = 2399831) B2399831
theorem B1599929 : Blo 1064615 1599929 := bstep (se 2 (by rfl) ⟨599973, by rfl⟩ : syracuseStep 1599929 = 1199947) B1199947
theorem B1600007 : Blo 1064615 1600007 := bstep (se 1 (by rfl) ⟨1200005, by rfl⟩ : syracuseStep 1600007 = 2400011) B2400011
theorem B1600043 : Blo 1064615 1600043 := bstep (se 1 (by rfl) ⟨1200032, by rfl⟩ : syracuseStep 1600043 = 2400065) B2400065
theorem B2026043 : Blo 1064615 2026043 := bstep (se 1 (by rfl) ⟨1519532, by rfl⟩ : syracuseStep 2026043 = 3039065) B3039065
theorem B1600073 : Blo 1064615 1600073 := bstep (se 2 (by rfl) ⟨600027, by rfl⟩ : syracuseStep 1600073 = 1200055) B1200055
theorem B1600187 : Blo 1064615 1600187 := bstep (se 1 (by rfl) ⟨1200140, by rfl⟩ : syracuseStep 1600187 = 2400281) B2400281
theorem B1796809 : Blo 1064615 1796809 := bstep (se 2 (by rfl) ⟨673803, by rfl⟩ : syracuseStep 1796809 = 1347607) B1347607
theorem B1600247 : Blo 1064615 1600247 := bstep (se 1 (by rfl) ⟨1200185, by rfl⟩ : syracuseStep 1600247 = 2400371) B2400371
theorem B3042049 : Blo 1064615 3042049 := bstep (se 2 (by rfl) ⟨1140768, by rfl⟩ : syracuseStep 3042049 = 2281537) B2281537
theorem B3238667 : Blo 1064615 3238667 := bstep (se 1 (by rfl) ⟨2429000, by rfl⟩ : syracuseStep 3238667 = 4858001) B4858001
theorem B1600271 : Blo 1064615 1600271 := bstep (se 1 (by rfl) ⟨1200203, by rfl⟩ : syracuseStep 1600271 = 2400407) B2400407
theorem B1600313 : Blo 1064615 1600313 := bstep (se 2 (by rfl) ⟨600117, by rfl⟩ : syracuseStep 1600313 = 1200235) B1200235
theorem B5401403 : Blo 1064615 5401403 := bstep (se 1 (by rfl) ⟨4051052, by rfl⟩ : syracuseStep 5401403 = 8102105) B8102105
theorem B3042107 : Blo 1064615 3042107 := bstep (se 1 (by rfl) ⟨2281580, by rfl⟩ : syracuseStep 3042107 = 4563161) B4563161
theorem B1600391 : Blo 1064615 1600391 := bstep (se 1 (by rfl) ⟨1200293, by rfl⟩ : syracuseStep 1600391 = 2400587) B2400587
theorem B1600427 : Blo 1064615 1600427 := bstep (se 1 (by rfl) ⟨1200320, by rfl⟩ : syracuseStep 1600427 = 2400641) B2400641
theorem B1600457 : Blo 1064615 1600457 := bstep (se 2 (by rfl) ⟨600171, by rfl⟩ : syracuseStep 1600457 = 1200343) B1200343
theorem B5401565 : Blo 1064615 5401565 := bstep (se 3 (by rfl) ⟨1012793, by rfl⟩ : syracuseStep 5401565 = 2025587) B2025587
theorem B2026529 : Blo 1064615 2026529 := bstep (se 2 (by rfl) ⟨759948, by rfl⟩ : syracuseStep 2026529 = 1519897) B1519897
theorem B1600571 : Blo 1064615 1600571 := bstep (se 1 (by rfl) ⟨1200428, by rfl⟩ : syracuseStep 1600571 = 2400857) B2400857
theorem B1600631 : Blo 1064615 1600631 := bstep (se 1 (by rfl) ⟨1200473, by rfl⟩ : syracuseStep 1600631 = 2400947) B2400947
theorem B1600655 : Blo 1064615 1600655 := bstep (se 1 (by rfl) ⟨1200491, by rfl⟩ : syracuseStep 1600655 = 2400983) B2400983
theorem B1600697 : Blo 1064615 1600697 := bstep (se 2 (by rfl) ⟨600261, by rfl⟩ : syracuseStep 1600697 = 1200523) B1200523
theorem B1600775 : Blo 1064615 1600775 := bstep (se 1 (by rfl) ⟨1200581, by rfl⟩ : syracuseStep 1600775 = 2401163) B2401163
theorem B5401889 : Blo 1064615 5401889 := bstep (se 2 (by rfl) ⟨2025708, by rfl⟩ : syracuseStep 5401889 = 4051417) B4051417
theorem B1600811 : Blo 1064615 1600811 := bstep (se 1 (by rfl) ⟨1200608, by rfl⟩ : syracuseStep 1600811 = 2401217) B2401217
theorem B2026795 : Blo 1064615 2026795 := bstep (se 1 (by rfl) ⟨1520096, by rfl⟩ : syracuseStep 2026795 = 3040193) B3040193
theorem B1600841 : Blo 1064615 1600841 := bstep (se 2 (by rfl) ⟨600315, by rfl⟩ : syracuseStep 1600841 = 1200631) B1200631
theorem B1797511 : Blo 1064615 1797511 := bstep (se 1 (by rfl) ⟨1348133, by rfl⟩ : syracuseStep 1797511 = 2696267) B2696267
theorem B3599801 : Blo 1064615 3599801 := bstep (se 2 (by rfl) ⟨1349925, by rfl⟩ : syracuseStep 3599801 = 2699851) B2699851
theorem B1600955 : Blo 1064615 1600955 := bstep (se 1 (by rfl) ⟨1200716, by rfl⟩ : syracuseStep 1600955 = 2401433) B2401433
theorem B1601015 : Blo 1064615 1601015 := bstep (se 1 (by rfl) ⟨1200761, by rfl⟩ : syracuseStep 1601015 = 2401523) B2401523
theorem B1601039 : Blo 1064615 1601039 := bstep (se 1 (by rfl) ⟨1200779, by rfl⟩ : syracuseStep 1601039 = 2401559) B2401559
theorem B1601081 : Blo 1064615 1601081 := bstep (se 2 (by rfl) ⟨600405, by rfl⟩ : syracuseStep 1601081 = 1200811) B1200811
theorem B1601159 : Blo 1064615 1601159 := bstep (se 1 (by rfl) ⟨1200869, by rfl⟩ : syracuseStep 1601159 = 2401739) B2401739
theorem B1601195 : Blo 1064615 1601195 := bstep (se 1 (by rfl) ⟨1200896, by rfl⟩ : syracuseStep 1601195 = 2401793) B2401793
theorem B2191033 : Blo 1064615 2191033 := bstep (se 2 (by rfl) ⟨821637, by rfl⟩ : syracuseStep 2191033 = 1643275) B1643275
theorem B1601225 : Blo 1064615 1601225 := bstep (se 2 (by rfl) ⟨600459, by rfl⟩ : syracuseStep 1601225 = 1200919) B1200919
theorem B1601339 : Blo 1064615 1601339 := bstep (se 1 (by rfl) ⟨1201004, by rfl⟩ : syracuseStep 1601339 = 2402009) B2402009
theorem B1601399 : Blo 1064615 1601399 := bstep (se 1 (by rfl) ⟨1201049, by rfl⟩ : syracuseStep 1601399 = 2402099) B2402099
theorem B1601423 : Blo 1064615 1601423 := bstep (se 1 (by rfl) ⟨1201067, by rfl⟩ : syracuseStep 1601423 = 2402135) B2402135
theorem B1601465 : Blo 1064615 1601465 := bstep (se 2 (by rfl) ⟨600549, by rfl⟩ : syracuseStep 1601465 = 1201099) B1201099
theorem B1601543 : Blo 1064615 1601543 := bstep (se 1 (by rfl) ⟨1201157, by rfl⟩ : syracuseStep 1601543 = 2402315) B2402315
theorem B3600395 : Blo 1064615 3600395 := bstep (se 1 (by rfl) ⟨2700296, by rfl⟩ : syracuseStep 3600395 = 5400593) B5400593
theorem B1798159 : Blo 1064615 1798159 := bstep (se 1 (by rfl) ⟨1348619, by rfl⟩ : syracuseStep 1798159 = 2697239) B2697239
theorem B1601579 : Blo 1064615 1601579 := bstep (se 1 (by rfl) ⟨1201184, by rfl⟩ : syracuseStep 1601579 = 2402369) B2402369
theorem B1601609 : Blo 1064615 1601609 := bstep (se 2 (by rfl) ⟨600603, by rfl⟩ : syracuseStep 1601609 = 1201207) B1201207
theorem B3600503 : Blo 1064615 3600503 := bstep (se 1 (by rfl) ⟨2700377, by rfl⟩ : syracuseStep 3600503 = 5400755) B5400755
theorem B1601723 : Blo 1064615 1601723 := bstep (se 1 (by rfl) ⟨1201292, by rfl⟩ : syracuseStep 1601723 = 2402585) B2402585
theorem B5402861 : Blo 1064615 5402861 := bstep (se 3 (by rfl) ⟨1013036, by rfl⟩ : syracuseStep 5402861 = 2026073) B2026073
theorem B31191281 : Blo 1064615 31191281 := bstep (se 2 (by rfl) ⟨11696730, by rfl⟩ : syracuseStep 31191281 = 23393461) B23393461
theorem B1601783 : Blo 1064615 1601783 := bstep (se 1 (by rfl) ⟨1201337, by rfl⟩ : syracuseStep 1601783 = 2402675) B2402675
theorem B1601807 : Blo 1064615 1601807 := bstep (se 1 (by rfl) ⟨1201355, by rfl⟩ : syracuseStep 1601807 = 2402711) B2402711
theorem B1601849 : Blo 1064615 1601849 := bstep (se 2 (by rfl) ⟨600693, by rfl⟩ : syracuseStep 1601849 = 1201387) B1201387
theorem B1601927 : Blo 1064615 1601927 := bstep (se 1 (by rfl) ⟨1201445, by rfl⟩ : syracuseStep 1601927 = 2402891) B2402891
theorem B2027911 : Blo 1064615 2027911 := bstep (se 1 (by rfl) ⟨1520933, by rfl⟩ : syracuseStep 2027911 = 3041867) B3041867
theorem B1601963 : Blo 1064615 1601963 := bstep (se 1 (by rfl) ⟨1201472, by rfl⟩ : syracuseStep 1601963 = 2402945) B2402945
theorem B1601993 : Blo 1064615 1601993 := bstep (se 2 (by rfl) ⟨600747, by rfl⟩ : syracuseStep 1601993 = 1201495) B1201495
theorem B1798699 : Blo 1064615 1798699 := bstep (se 1 (by rfl) ⟨1349024, by rfl⟩ : syracuseStep 1798699 = 2698049) B2698049
theorem B1602107 : Blo 1064615 1602107 := bstep (se 1 (by rfl) ⟨1201580, by rfl⟩ : syracuseStep 1602107 = 2403161) B2403161
theorem B1602167 : Blo 1064615 1602167 := bstep (se 1 (by rfl) ⟨1201625, by rfl⟩ : syracuseStep 1602167 = 2403251) B2403251
theorem B1602191 : Blo 1064615 1602191 := bstep (se 1 (by rfl) ⟨1201643, by rfl⟩ : syracuseStep 1602191 = 2403287) B2403287
theorem B1798841 : Blo 1064615 1798841 := bstep (se 2 (by rfl) ⟨674565, by rfl⟩ : syracuseStep 1798841 = 1349131) B1349131
theorem B1602233 : Blo 1064615 1602233 := bstep (se 2 (by rfl) ⟨600837, by rfl⟩ : syracuseStep 1602233 = 1201675) B1201675
theorem B3601097 : Blo 1064615 3601097 := bstep (se 2 (by rfl) ⟨1350411, by rfl⟩ : syracuseStep 3601097 = 2700823) B2700823
theorem B1602311 : Blo 1064615 1602311 := bstep (se 1 (by rfl) ⟨1201733, by rfl⟩ : syracuseStep 1602311 = 2403467) B2403467
theorem B1602347 : Blo 1064615 1602347 := bstep (se 1 (by rfl) ⟨1201760, by rfl⟩ : syracuseStep 1602347 = 2403521) B2403521
theorem B1602377 : Blo 1064615 1602377 := bstep (se 2 (by rfl) ⟨600891, by rfl⟩ : syracuseStep 1602377 = 1201783) B1201783
theorem B2028473 : Blo 1064615 2028473 := bstep (se 2 (by rfl) ⟨760677, by rfl⟩ : syracuseStep 2028473 = 1521355) B1521355
theorem B1602491 : Blo 1064615 1602491 := bstep (se 1 (by rfl) ⟨1201868, by rfl⟩ : syracuseStep 1602491 = 2403737) B2403737
theorem B1602551 : Blo 1064615 1602551 := bstep (se 1 (by rfl) ⟨1201913, by rfl⟩ : syracuseStep 1602551 = 2403827) B2403827
theorem B1602575 : Blo 1064615 1602575 := bstep (se 1 (by rfl) ⟨1201931, by rfl⟩ : syracuseStep 1602575 = 2403863) B2403863
theorem B5403671 : Blo 1064615 5403671 := bstep (se 1 (by rfl) ⟨4052753, by rfl⟩ : syracuseStep 5403671 = 8105507) B8105507
theorem B1602617 : Blo 1064615 1602617 := bstep (se 2 (by rfl) ⟨600981, by rfl⟩ : syracuseStep 1602617 = 1201963) B1201963
theorem B1602695 : Blo 1064615 1602695 := bstep (se 1 (by rfl) ⟨1202021, by rfl⟩ : syracuseStep 1602695 = 2404043) B2404043
theorem B1602731 : Blo 1064615 1602731 := bstep (se 1 (by rfl) ⟨1202048, by rfl⟩ : syracuseStep 1602731 = 2404097) B2404097
theorem B1602761 : Blo 1064615 1602761 := bstep (se 2 (by rfl) ⟨601035, by rfl⟩ : syracuseStep 1602761 = 1202071) B1202071
theorem B1602875 : Blo 1064615 1602875 := bstep (se 1 (by rfl) ⟨1202156, by rfl⟩ : syracuseStep 1602875 = 2404313) B2404313
theorem B1799543 : Blo 1064615 1799543 := bstep (se 1 (by rfl) ⟨1349657, by rfl⟩ : syracuseStep 1799543 = 2699315) B2699315
theorem B3601799 : Blo 1064615 3601799 := bstep (se 1 (by rfl) ⟨2701349, by rfl⟩ : syracuseStep 3601799 = 5402699) B5402699
theorem B11859335 : Blo 1064615 11859335 := bstep (se 1 (by rfl) ⟨8894501, by rfl⟩ : syracuseStep 11859335 = 17789003) B17789003
theorem B1439147 : Blo 1064615 1439147 := bstep (se 1 (by rfl) ⟨1079360, by rfl⟩ : syracuseStep 1439147 = 2158721) B2158721
theorem B15562169 : Blo 1064615 15562169 := bstep (se 2 (by rfl) ⟨5835813, by rfl⟩ : syracuseStep 15562169 = 11671627) B11671627
theorem B8779229 : Blo 1064615 8779229 := bstep (se 3 (by rfl) ⟨1646105, by rfl⟩ : syracuseStep 8779229 = 3292211) B3292211
theorem B3602177 : Blo 1064615 3602177 := bstep (se 2 (by rfl) ⟨1350816, by rfl⟩ : syracuseStep 3602177 = 2701633) B2701633
theorem B1799995 : Blo 1064615 1799995 := bstep (se 1 (by rfl) ⟨1349996, by rfl⟩ : syracuseStep 1799995 = 2699993) B2699993
theorem B126613313 : Blo 1064615 126613313 := bstep (se 2 (by rfl) ⟨47479992, by rfl⟩ : syracuseStep 126613313 = 94959985) B94959985
theorem B1439623 : Blo 1064615 1439623 := bstep (se 1 (by rfl) ⟨1079717, by rfl⟩ : syracuseStep 1439623 = 2159435) B2159435
theorem B5339033 : Blo 1064615 5339033 := bstep (se 2 (by rfl) ⟨2002137, by rfl⟩ : syracuseStep 5339033 = 4004275) B4004275
theorem B1800137 : Blo 1064615 1800137 := bstep (se 2 (by rfl) ⟨675051, by rfl⟩ : syracuseStep 1800137 = 1350103) B1350103
theorem B11532293 : Blo 1064615 11532293 := bstep (se 4 (by rfl) ⟨1081152, by rfl⟩ : syracuseStep 11532293 = 2162305) B2162305
theorem B3078173 : Blo 1064615 3078173 := bstep (se 3 (by rfl) ⟨577157, by rfl⟩ : syracuseStep 3078173 = 1154315) B1154315
theorem B8648765 : Blo 1064615 8648765 := bstep (se 3 (by rfl) ⟨1621643, by rfl⟩ : syracuseStep 8648765 = 3243287) B3243287
theorem B12155345 : Blo 1064615 12155345 := bstep (se 2 (by rfl) ⟨4558254, by rfl⟩ : syracuseStep 12155345 = 9116509) B9116509
theorem B3602987 : Blo 1064615 3602987 := bstep (se 1 (by rfl) ⟨2702240, by rfl⟩ : syracuseStep 3602987 = 5404481) B5404481
theorem B9108035 : Blo 1064615 9108035 := bstep (se 1 (by rfl) ⟨6831026, by rfl⟩ : syracuseStep 9108035 = 13662053) B13662053
theorem B1800839 : Blo 1064615 1800839 := bstep (se 1 (by rfl) ⟨1350629, by rfl⟩ : syracuseStep 1800839 = 2701259) B2701259
theorem B3701537 : Blo 1064615 3701537 := bstep (se 2 (by rfl) ⟨1388076, by rfl⟩ : syracuseStep 3701537 = 2776153) B2776153
theorem B9730853 : Blo 1064615 9730853 := bstep (se 4 (by rfl) ⟨912267, by rfl⟩ : syracuseStep 9730853 = 1824535) B1824535
theorem B1080463 : Blo 1064615 1080463 := bstep (se 1 (by rfl) ⟨810347, by rfl⟩ : syracuseStep 1080463 = 1620695) B1620695
theorem B1801487 : Blo 1064615 1801487 := bstep (se 1 (by rfl) ⟨1351115, by rfl⟩ : syracuseStep 1801487 = 2702231) B2702231
theorem B1802027 : Blo 1064615 1802027 := bstep (se 1 (by rfl) ⟨1351520, by rfl⟩ : syracuseStep 1802027 = 2703041) B2703041
theorem B3604283 : Blo 1064615 3604283 := bstep (se 1 (by rfl) ⟨2703212, by rfl⟩ : syracuseStep 3604283 = 5406425) B5406425
theorem B3604499 : Blo 1064615 3604499 := bstep (se 1 (by rfl) ⟨2703374, by rfl⟩ : syracuseStep 3604499 = 5406749) B5406749
theorem B1802297 : Blo 1064615 1802297 := bstep (se 2 (by rfl) ⟨675861, by rfl⟩ : syracuseStep 1802297 = 1351723) B1351723
theorem B3604823 : Blo 1064615 3604823 := bstep (se 1 (by rfl) ⟨2703617, by rfl⟩ : syracuseStep 3604823 = 5407235) B5407235
theorem B5767529 : Blo 1064615 5767529 := bstep (se 2 (by rfl) ⟨2162823, by rfl⟩ : syracuseStep 5767529 = 4325647) B4325647
theorem B1802999 : Blo 1064615 1802999 := bstep (se 1 (by rfl) ⟨1352249, by rfl⟩ : syracuseStep 1802999 = 2704499) B2704499
theorem B10945601 : Blo 1064615 10945601 := bstep (se 2 (by rfl) ⟨4104600, by rfl⟩ : syracuseStep 10945601 = 8209201) B8209201
theorem B3605903 : Blo 1064615 3605903 := bstep (se 1 (by rfl) ⟨2704427, by rfl⟩ : syracuseStep 3605903 = 5408855) B5408855
theorem B2917913 : Blo 1064615 2917913 := bstep (se 2 (by rfl) ⟨1094217, by rfl⟩ : syracuseStep 2917913 = 2188435) B2188435
theorem B4556411 : Blo 1064615 4556411 := bstep (se 1 (by rfl) ⟨3417308, by rfl⟩ : syracuseStep 4556411 = 6834617) B6834617
theorem B3606227 : Blo 1064615 3606227 := bstep (se 1 (by rfl) ⟨2704670, by rfl⟩ : syracuseStep 3606227 = 5409341) B5409341
theorem B1705835 : Blo 1064615 1705835 := bstep (se 1 (by rfl) ⟨1279376, by rfl⟩ : syracuseStep 1705835 = 2558753) B2558753
theorem B4327595 : Blo 1064615 4327595 := bstep (se 1 (by rfl) ⟨3245696, by rfl⟩ : syracuseStep 4327595 = 6491393) B6491393
theorem B1804535 : Blo 1064615 1804535 := bstep (se 1 (by rfl) ⟨1353401, by rfl⟩ : syracuseStep 1804535 = 2706803) B2706803
theorem B4557161 : Blo 1064615 4557161 := bstep (se 2 (by rfl) ⟨1708935, by rfl⟩ : syracuseStep 4557161 = 3417871) B3417871
theorem B2885993 : Blo 1064615 2885993 := bstep (se 2 (by rfl) ⟨1082247, by rfl⟩ : syracuseStep 2885993 = 2164495) B2164495
theorem B3410849 : Blo 1064615 3410849 := bstep (se 2 (by rfl) ⟨1279068, by rfl⟩ : syracuseStep 3410849 = 2558137) B2558137
theorem B8653891 : Blo 1064615 8653891 := bstep (se 1 (by rfl) ⟨6490418, by rfl⟩ : syracuseStep 8653891 = 12980837) B12980837
theorem B2166311 : Blo 1064615 2166311 := bstep (se 1 (by rfl) ⟨1624733, by rfl⟩ : syracuseStep 2166311 = 3249467) B3249467
theorem B3411515 : Blo 1064615 3411515 := bstep (se 1 (by rfl) ⟨2558636, by rfl⟩ : syracuseStep 3411515 = 5117273) B5117273
theorem B17763907 : Blo 1064615 17763907 := bstep (se 1 (by rfl) ⟨13322930, by rfl⟩ : syracuseStep 17763907 = 26645861) B26645861
theorem B2395745 : Blo 1064615 2395745 := bstep (se 2 (by rfl) ⟨898404, by rfl⟩ : syracuseStep 2395745 = 1796809) B1796809
theorem B20778619 : Blo 1064615 20778619 := bstep (se 1 (by rfl) ⟨15583964, by rfl⟩ : syracuseStep 20778619 = 31167929) B31167929
theorem B3837725 : Blo 1064615 3837725 := bstep (se 3 (by rfl) ⟨719573, by rfl⟩ : syracuseStep 3837725 = 1439147) B1439147
theorem B1347511 : Blo 1064615 1347511 := bstep (se 1 (by rfl) ⟨1010633, by rfl⟩ : syracuseStep 1347511 = 2021267) B2021267
theorem B2396087 : Blo 1064615 2396087 := bstep (se 1 (by rfl) ⟨1797065, by rfl⟩ : syracuseStep 2396087 = 3594131) B3594131
theorem B6066191 : Blo 1064615 6066191 := bstep (se 1 (by rfl) ⟨4549643, by rfl⟩ : syracuseStep 6066191 = 9099287) B9099287
theorem B3117455 : Blo 1064615 3117455 := bstep (se 1 (by rfl) ⟨2338091, by rfl⟩ : syracuseStep 3117455 = 4676183) B4676183
theorem B2396681 : Blo 1064615 2396681 := bstep (se 2 (by rfl) ⟨898755, by rfl⟩ : syracuseStep 2396681 = 1797511) B1797511
theorem B1282759 : Blo 1064615 1282759 := bstep (se 1 (by rfl) ⟨962069, by rfl⟩ : syracuseStep 1282759 = 1924139) B1924139
theorem B6066899 : Blo 1064615 6066899 := bstep (se 1 (by rfl) ⟨4550174, by rfl⟩ : syracuseStep 6066899 = 9100349) B9100349
theorem B3642185 : Blo 1064615 3642185 := bstep (se 2 (by rfl) ⟨1365819, by rfl⟩ : syracuseStep 3642185 = 2731639) B2731639
theorem B2397023 : Blo 1064615 2397023 := bstep (se 1 (by rfl) ⟨1797767, by rfl⟩ : syracuseStep 2397023 = 3595535) B3595535
theorem B2560943 : Blo 1064615 2560943 := bstep (se 1 (by rfl) ⟨1920707, by rfl⟩ : syracuseStep 2560943 = 3841415) B3841415
theorem B1708987 : Blo 1064615 1708987 := bstep (se 1 (by rfl) ⟨1281740, by rfl⟩ : syracuseStep 1708987 = 2563481) B2563481
theorem B65704931 : Blo 1064615 65704931 := bstep (se 1 (by rfl) ⟨49278698, by rfl⟩ : syracuseStep 65704931 = 98557397) B98557397
theorem B2397203 : Blo 1064615 2397203 := bstep (se 1 (by rfl) ⟨1797902, by rfl⟩ : syracuseStep 2397203 = 3595805) B3595805
theorem B1348807 : Blo 1064615 1348807 := bstep (se 1 (by rfl) ⟨1011605, by rfl⟩ : syracuseStep 1348807 = 2023211) B2023211
theorem B2397545 : Blo 1064615 2397545 := bstep (se 2 (by rfl) ⟨899079, by rfl⟩ : syracuseStep 2397545 = 1798159) B1798159
theorem B29234677 : Blo 1064615 29234677 := bstep (se 5 (by rfl) ⟨1370375, by rfl⟩ : syracuseStep 29234677 = 2740751) B2740751
theorem B1349551 : Blo 1064615 1349551 := bstep (se 1 (by rfl) ⟨1012163, by rfl⟩ : syracuseStep 1349551 = 2024327) B2024327
theorem B2398139 : Blo 1064615 2398139 := bstep (se 1 (by rfl) ⟨1798604, by rfl⟩ : syracuseStep 2398139 = 3597209) B3597209
theorem B2398265 : Blo 1064615 2398265 := bstep (se 2 (by rfl) ⟨899349, by rfl⟩ : syracuseStep 2398265 = 1798699) B1798699
theorem B2398607 : Blo 1064615 2398607 := bstep (se 1 (by rfl) ⟨1798955, by rfl⟩ : syracuseStep 2398607 = 3597911) B3597911
theorem B2398931 : Blo 1064615 2398931 := bstep (se 1 (by rfl) ⟨1799198, by rfl⟩ : syracuseStep 2398931 = 3598397) B3598397
theorem B1350695 : Blo 1064615 1350695 := bstep (se 1 (by rfl) ⟨1013021, by rfl⟩ : syracuseStep 1350695 = 2026043) B2026043
theorem B2563319 : Blo 1064615 2563319 := bstep (se 1 (by rfl) ⟨1922489, by rfl⟩ : syracuseStep 2563319 = 3844979) B3844979
theorem B1351019 : Blo 1064615 1351019 := bstep (se 1 (by rfl) ⟨1013264, by rfl⟩ : syracuseStep 1351019 = 2026529) B2026529
theorem B2399867 : Blo 1064615 2399867 := bstep (se 1 (by rfl) ⟨1799900, by rfl⟩ : syracuseStep 2399867 = 3599801) B3599801
theorem B7020179 : Blo 1064615 7020179 := bstep (se 1 (by rfl) ⟨5265134, by rfl⟩ : syracuseStep 7020179 = 10530269) B10530269
theorem B2924221 : Blo 1064615 2924221 := bstep (se 3 (by rfl) ⟨548291, by rfl⟩ : syracuseStep 2924221 = 1096583) B1096583
theorem B2399993 : Blo 1064615 2399993 := bstep (se 2 (by rfl) ⟨899997, by rfl⟩ : syracuseStep 2399993 = 1799995) B1799995
theorem B2400263 : Blo 1064615 2400263 := bstep (se 1 (by rfl) ⟨1800197, by rfl⟩ : syracuseStep 2400263 = 3600395) B3600395
theorem B2400335 : Blo 1064615 2400335 := bstep (se 1 (by rfl) ⟨1800251, by rfl⟩ : syracuseStep 2400335 = 3600503) B3600503
theorem B3416539 : Blo 1064615 3416539 := bstep (se 1 (by rfl) ⟨2562404, by rfl⟩ : syracuseStep 3416539 = 5124809) B5124809
theorem B2400731 : Blo 1064615 2400731 := bstep (se 1 (by rfl) ⟨1800548, by rfl⟩ : syracuseStep 2400731 = 3601097) B3601097
theorem B6496793 : Blo 1064615 6496793 := bstep (se 2 (by rfl) ⟨2436297, by rfl⟩ : syracuseStep 6496793 = 4872595) B4872595
theorem B1352315 : Blo 1064615 1352315 := bstep (se 1 (by rfl) ⟨1014236, by rfl⟩ : syracuseStep 1352315 = 2028473) B2028473
theorem B2401199 : Blo 1064615 2401199 := bstep (se 1 (by rfl) ⟨1800899, by rfl⟩ : syracuseStep 2401199 = 3601799) B3601799
theorem B7906223 : Blo 1064615 7906223 := bstep (se 1 (by rfl) ⟨5929667, by rfl⟩ : syracuseStep 7906223 = 11859335) B11859335
theorem B14230579 : Blo 1064615 14230579 := bstep (se 1 (by rfl) ⟨10672934, by rfl⟩ : syracuseStep 14230579 = 21345869) B21345869
theorem B2401451 : Blo 1064615 2401451 := bstep (se 1 (by rfl) ⟨1801088, by rfl⟩ : syracuseStep 2401451 = 3602177) B3602177
theorem B1516907 : Blo 1064615 1516907 := bstep (se 1 (by rfl) ⟨1137680, by rfl⟩ : syracuseStep 1516907 = 2275361) B2275361
theorem B2696591 : Blo 1064615 2696591 := bstep (se 1 (by rfl) ⟨2022443, by rfl⟩ : syracuseStep 2696591 = 4044887) B4044887
theorem B9119243 : Blo 1064615 9119243 := bstep (se 1 (by rfl) ⟨6839432, by rfl⟩ : syracuseStep 9119243 = 13678865) B13678865
theorem B8103563 : Blo 1064615 8103563 := bstep (se 1 (by rfl) ⟨6077672, by rfl⟩ : syracuseStep 8103563 = 12155345) B12155345
theorem B2401991 : Blo 1064615 2401991 := bstep (se 1 (by rfl) ⟨1801493, by rfl⟩ : syracuseStep 2401991 = 3602987) B3602987
theorem B2696915 : Blo 1064615 2696915 := bstep (se 1 (by rfl) ⟨2022686, by rfl⟩ : syracuseStep 2696915 = 4045373) B4045373
theorem B6072023 : Blo 1064615 6072023 := bstep (se 1 (by rfl) ⟨4554017, by rfl⟩ : syracuseStep 6072023 = 9108035) B9108035
theorem B2467691 : Blo 1064615 2467691 := bstep (se 1 (by rfl) ⟨1850768, by rfl⟩ : syracuseStep 2467691 = 3701537) B3701537
theorem B7677989 : Blo 1064615 7677989 := bstep (se 4 (by rfl) ⟨719811, by rfl⟩ : syracuseStep 7677989 = 1439623) B1439623
theorem B112208273 : Blo 1064615 112208273 := bstep (se 2 (by rfl) ⟨42078102, by rfl⟩ : syracuseStep 112208273 = 84156205) B84156205
theorem B26978849 : Blo 1064615 26978849 := bstep (se 2 (by rfl) ⟨10117068, by rfl⟩ : syracuseStep 26978849 = 20234137) B20234137
theorem B2402855 : Blo 1064615 2402855 := bstep (se 1 (by rfl) ⟨1802141, by rfl⟩ : syracuseStep 2402855 = 3604283) B3604283
theorem B3844907 : Blo 1064615 3844907 := bstep (se 1 (by rfl) ⟨2883680, by rfl⟩ : syracuseStep 3844907 = 5767361) B5767361
theorem B2403179 : Blo 1064615 2403179 := bstep (se 1 (by rfl) ⟨1802384, by rfl⟩ : syracuseStep 2403179 = 3604769) B3604769
theorem B2403233 : Blo 1064615 2403233 := bstep (se 2 (by rfl) ⟨901212, by rfl⟩ : syracuseStep 2403233 = 1802425) B1802425
theorem B2403575 : Blo 1064615 2403575 := bstep (se 1 (by rfl) ⟨1802681, by rfl⟩ : syracuseStep 2403575 = 3605363) B3605363
theorem B1519031 : Blo 1064615 1519031 := bstep (se 1 (by rfl) ⟨1139273, by rfl⟩ : syracuseStep 1519031 = 2278547) B2278547
theorem B10268147 : Blo 1064615 10268147 := bstep (se 1 (by rfl) ⟨7701110, by rfl⟩ : syracuseStep 10268147 = 15402221) B15402221
theorem B5123731 : Blo 1064615 5123731 := bstep (se 1 (by rfl) ⟨3842798, by rfl⟩ : syracuseStep 5123731 = 7685597) B7685597
theorem B2404169 : Blo 1064615 2404169 := bstep (se 2 (by rfl) ⟨901563, by rfl⟩ : syracuseStep 2404169 = 1803127) B1803127
theorem B2699183 : Blo 1064615 2699183 := bstep (se 1 (by rfl) ⟨2024387, by rfl⟩ : syracuseStep 2699183 = 4048775) B4048775
theorem B9744461 : Blo 1064615 9744461 := bstep (se 3 (by rfl) ⟨1827086, by rfl⟩ : syracuseStep 9744461 = 3654173) B3654173
theorem B2699801 : Blo 1064615 2699801 := bstep (se 2 (by rfl) ⟨1012425, by rfl⟩ : syracuseStep 2699801 = 2024851) B2024851
theorem B6074939 : Blo 1064615 6074939 := bstep (se 1 (by rfl) ⟨4556204, by rfl⟩ : syracuseStep 6074939 = 9112409) B9112409
theorem B3420731 : Blo 1064615 3420731 := bstep (se 1 (by rfl) ⟨2565548, by rfl⟩ : syracuseStep 3420731 = 5131097) B5131097
theorem B27669059 : Blo 1064615 27669059 := bstep (se 1 (by rfl) ⟨20751794, by rfl⟩ : syracuseStep 27669059 = 41503589) B41503589
theorem B3846865 : Blo 1064615 3846865 := bstep (se 2 (by rfl) ⟨1442574, by rfl⟩ : syracuseStep 3846865 = 2885149) B2885149
theorem B1520489 : Blo 1064615 1520489 := bstep (se 2 (by rfl) ⟨570183, by rfl⟩ : syracuseStep 1520489 = 1140367) B1140367
theorem B4043627 : Blo 1064615 4043627 := bstep (se 1 (by rfl) ⟨3032720, by rfl⟩ : syracuseStep 4043627 = 6065441) B6065441
theorem B10236779 : Blo 1064615 10236779 := bstep (se 1 (by rfl) ⟨7677584, by rfl⟩ : syracuseStep 10236779 = 15355169) B15355169
theorem B9122867 : Blo 1064615 9122867 := bstep (se 1 (by rfl) ⟨6842150, by rfl⟩ : syracuseStep 9122867 = 13684301) B13684301
theorem B8107937 : Blo 1064615 8107937 := bstep (se 2 (by rfl) ⟨3040476, by rfl⟩ : syracuseStep 8107937 = 6080953) B6080953
theorem B3848249 : Blo 1064615 3848249 := bstep (se 2 (by rfl) ⟨1443093, by rfl⟩ : syracuseStep 3848249 = 2886187) B2886187
theorem B3651983 : Blo 1064615 3651983 := bstep (se 1 (by rfl) ⟨2738987, by rfl⟩ : syracuseStep 3651983 = 5477975) B5477975
theorem B2276257 : Blo 1064615 2276257 := bstep (se 2 (by rfl) ⟨853596, by rfl⟩ : syracuseStep 2276257 = 1707193) B1707193
theorem B3423151 : Blo 1064615 3423151 := bstep (se 1 (by rfl) ⟨2567363, by rfl⟩ : syracuseStep 3423151 = 5134727) B5134727
theorem B7781341 : Blo 1064615 7781341 := bstep (se 3 (by rfl) ⟨1459001, by rfl⟩ : syracuseStep 7781341 = 2918003) B2918003
theorem B2702393 : Blo 1064615 2702393 := bstep (se 2 (by rfl) ⟨1013397, by rfl⟩ : syracuseStep 2702393 = 2026795) B2026795
theorem B3849373 : Blo 1064615 3849373 := bstep (se 3 (by rfl) ⟨721757, by rfl⟩ : syracuseStep 3849373 = 1443515) B1443515
theorem B4046071 : Blo 1064615 4046071 := bstep (se 1 (by rfl) ⟨3034553, by rfl⟩ : syracuseStep 4046071 = 6069107) B6069107
theorem B2276599 : Blo 1064615 2276599 := bstep (se 1 (by rfl) ⟨1707449, by rfl⟩ : syracuseStep 2276599 = 3414899) B3414899
theorem B2735489 : Blo 1064615 2735489 := bstep (se 2 (by rfl) ⟨1025808, by rfl⟩ : syracuseStep 2735489 = 2051617) B2051617
theorem B6929837 : Blo 1064615 6929837 := bstep (se 3 (by rfl) ⟨1299344, by rfl⟩ : syracuseStep 6929837 = 2598689) B2598689
theorem B4046345 : Blo 1064615 4046345 := bstep (se 2 (by rfl) ⟨1517379, by rfl⟩ : syracuseStep 4046345 = 3034759) B3034759
theorem B4046375 : Blo 1064615 4046375 := bstep (se 1 (by rfl) ⟨3034781, by rfl⟩ : syracuseStep 4046375 = 6069563) B6069563
theorem B1064623 : Blo 1064615 1064623 := bstep (se 1 (by rfl) ⟨798467, by rfl⟩ : syracuseStep 1064623 = 1596935) B1596935
theorem B1064647 : Blo 1064615 1064647 := bstep (se 1 (by rfl) ⟨798485, by rfl⟩ : syracuseStep 1064647 = 1596971) B1596971
theorem B8634071 : Blo 1064615 8634071 := bstep (se 1 (by rfl) ⟨6475553, by rfl⟩ : syracuseStep 8634071 = 12951107) B12951107
theorem B1064667 : Blo 1064615 1064667 := bstep (se 1 (by rfl) ⟨798500, by rfl⟩ : syracuseStep 1064667 = 1597001) B1597001
theorem B1064743 : Blo 1064615 1064743 := bstep (se 1 (by rfl) ⟨798557, by rfl⟩ : syracuseStep 1064743 = 1597115) B1597115
theorem B1064783 : Blo 1064615 1064783 := bstep (se 1 (by rfl) ⟨798587, by rfl⟩ : syracuseStep 1064783 = 1597175) B1597175
theorem B1064799 : Blo 1064615 1064799 := bstep (se 1 (by rfl) ⟨798599, by rfl⟩ : syracuseStep 1064799 = 1597199) B1597199
theorem B18759539 : Blo 1064615 18759539 := bstep (se 1 (by rfl) ⟨14069654, by rfl⟩ : syracuseStep 18759539 = 28139309) B28139309
theorem B1064827 : Blo 1064615 1064827 := bstep (se 1 (by rfl) ⟨798620, by rfl⟩ : syracuseStep 1064827 = 1597241) B1597241
theorem B1064879 : Blo 1064615 1064879 := bstep (se 1 (by rfl) ⟨798659, by rfl⟩ : syracuseStep 1064879 = 1597319) B1597319
theorem B10239929 : Blo 1064615 10239929 := bstep (se 2 (by rfl) ⟨3839973, by rfl⟩ : syracuseStep 10239929 = 7679947) B7679947
theorem B1064903 : Blo 1064615 1064903 := bstep (se 1 (by rfl) ⟨798677, by rfl⟩ : syracuseStep 1064903 = 1597355) B1597355
theorem B1064923 : Blo 1064615 1064923 := bstep (se 1 (by rfl) ⟨798692, by rfl⟩ : syracuseStep 1064923 = 1597385) B1597385
theorem B1064999 : Blo 1064615 1064999 := bstep (se 1 (by rfl) ⟨798749, by rfl⟩ : syracuseStep 1064999 = 1597499) B1597499
theorem B8208461 : Blo 1064615 8208461 := bstep (se 3 (by rfl) ⟨1539086, by rfl⟩ : syracuseStep 8208461 = 3078173) B3078173
theorem B1065039 : Blo 1064615 1065039 := bstep (se 1 (by rfl) ⟨798779, by rfl⟩ : syracuseStep 1065039 = 1597559) B1597559
theorem B6930521 : Blo 1064615 6930521 := bstep (se 2 (by rfl) ⟨2598945, by rfl⟩ : syracuseStep 6930521 = 5197891) B5197891
theorem B1065055 : Blo 1064615 1065055 := bstep (se 1 (by rfl) ⟨798791, by rfl⟩ : syracuseStep 1065055 = 1597583) B1597583
theorem B3850355 : Blo 1064615 3850355 := bstep (se 1 (by rfl) ⟨2887766, by rfl⟩ : syracuseStep 3850355 = 5775533) B5775533
theorem B1065083 : Blo 1064615 1065083 := bstep (se 1 (by rfl) ⟨798812, by rfl⟩ : syracuseStep 1065083 = 1597625) B1597625
theorem B3850411 : Blo 1064615 3850411 := bstep (se 1 (by rfl) ⟨2887808, by rfl⟩ : syracuseStep 3850411 = 5775617) B5775617
theorem B1065135 : Blo 1064615 1065135 := bstep (se 1 (by rfl) ⟨798851, by rfl⟩ : syracuseStep 1065135 = 1597703) B1597703
theorem B4047043 : Blo 1064615 4047043 := bstep (se 1 (by rfl) ⟨3035282, by rfl⟩ : syracuseStep 4047043 = 6070565) B6070565
theorem B1065159 : Blo 1064615 1065159 := bstep (se 1 (by rfl) ⟨798869, by rfl⟩ : syracuseStep 1065159 = 1597739) B1597739
theorem B1065179 : Blo 1064615 1065179 := bstep (se 1 (by rfl) ⟨798884, by rfl⟩ : syracuseStep 1065179 = 1597769) B1597769
theorem B1065255 : Blo 1064615 1065255 := bstep (se 1 (by rfl) ⟨798941, by rfl⟩ : syracuseStep 1065255 = 1597883) B1597883
theorem B1065295 : Blo 1064615 1065295 := bstep (se 1 (by rfl) ⟨798971, by rfl⟩ : syracuseStep 1065295 = 1597943) B1597943
theorem B1065311 : Blo 1064615 1065311 := bstep (se 1 (by rfl) ⟨798983, by rfl⟩ : syracuseStep 1065311 = 1597967) B1597967
theorem B1065339 : Blo 1064615 1065339 := bstep (se 1 (by rfl) ⟨799004, by rfl⟩ : syracuseStep 1065339 = 1598009) B1598009
theorem B1065391 : Blo 1064615 1065391 := bstep (se 1 (by rfl) ⟨799043, by rfl⟩ : syracuseStep 1065391 = 1598087) B1598087
theorem B1622447 : Blo 1064615 1622447 := bstep (se 1 (by rfl) ⟨1216835, by rfl⟩ : syracuseStep 1622447 = 2433671) B2433671
theorem B1065415 : Blo 1064615 1065415 := bstep (se 1 (by rfl) ⟨799061, by rfl⟩ : syracuseStep 1065415 = 1598123) B1598123
theorem B1065435 : Blo 1064615 1065435 := bstep (se 1 (by rfl) ⟨799076, by rfl⟩ : syracuseStep 1065435 = 1598153) B1598153
theorem B4047347 : Blo 1064615 4047347 := bstep (se 1 (by rfl) ⟨3035510, by rfl⟩ : syracuseStep 4047347 = 6071021) B6071021
theorem B2703881 : Blo 1064615 2703881 := bstep (se 2 (by rfl) ⟨1013955, by rfl⟩ : syracuseStep 2703881 = 2027911) B2027911
theorem B5390873 : Blo 1064615 5390873 := bstep (se 2 (by rfl) ⟨2021577, by rfl⟩ : syracuseStep 5390873 = 4043155) B4043155
theorem B1065511 : Blo 1064615 1065511 := bstep (se 1 (by rfl) ⟨799133, by rfl⟩ : syracuseStep 1065511 = 1598267) B1598267
theorem B1065551 : Blo 1064615 1065551 := bstep (se 1 (by rfl) ⟨799163, by rfl⟩ : syracuseStep 1065551 = 1598327) B1598327
theorem B1065567 : Blo 1064615 1065567 := bstep (se 1 (by rfl) ⟨799175, by rfl⟩ : syracuseStep 1065567 = 1598351) B1598351
theorem B1065595 : Blo 1064615 1065595 := bstep (se 1 (by rfl) ⟨799196, by rfl⟩ : syracuseStep 1065595 = 1598393) B1598393
theorem B13681325 : Blo 1064615 13681325 := bstep (se 3 (by rfl) ⟨2565248, by rfl⟩ : syracuseStep 13681325 = 5130497) B5130497
theorem B1065647 : Blo 1064615 1065647 := bstep (se 1 (by rfl) ⟨799235, by rfl⟩ : syracuseStep 1065647 = 1598471) B1598471
theorem B1065671 : Blo 1064615 1065671 := bstep (se 1 (by rfl) ⟨799253, by rfl⟩ : syracuseStep 1065671 = 1598507) B1598507
theorem B1065691 : Blo 1064615 1065691 := bstep (se 1 (by rfl) ⟨799268, by rfl⟩ : syracuseStep 1065691 = 1598537) B1598537
theorem B1065767 : Blo 1064615 1065767 := bstep (se 1 (by rfl) ⟨799325, by rfl⟩ : syracuseStep 1065767 = 1598651) B1598651
theorem B1065807 : Blo 1064615 1065807 := bstep (se 1 (by rfl) ⟨799355, by rfl⟩ : syracuseStep 1065807 = 1598711) B1598711
theorem B1065823 : Blo 1064615 1065823 := bstep (se 1 (by rfl) ⟨799367, by rfl⟩ : syracuseStep 1065823 = 1598735) B1598735
theorem B1065851 : Blo 1064615 1065851 := bstep (se 1 (by rfl) ⟨799388, by rfl⟩ : syracuseStep 1065851 = 1598777) B1598777
theorem B1065903 : Blo 1064615 1065903 := bstep (se 1 (by rfl) ⟨799427, by rfl⟩ : syracuseStep 1065903 = 1598855) B1598855
theorem B4047803 : Blo 1064615 4047803 := bstep (se 1 (by rfl) ⟨3035852, by rfl⟩ : syracuseStep 4047803 = 6071705) B6071705
theorem B1065927 : Blo 1064615 1065927 := bstep (se 1 (by rfl) ⟨799445, by rfl⟩ : syracuseStep 1065927 = 1598891) B1598891
theorem B1065947 : Blo 1064615 1065947 := bstep (se 1 (by rfl) ⟨799460, by rfl⟩ : syracuseStep 1065947 = 1598921) B1598921
theorem B1066023 : Blo 1064615 1066023 := bstep (se 1 (by rfl) ⟨799517, by rfl⟩ : syracuseStep 1066023 = 1599035) B1599035
theorem B1623079 : Blo 1064615 1623079 := bstep (se 1 (by rfl) ⟨1217309, by rfl⟩ : syracuseStep 1623079 = 2434619) B2434619
theorem B7128107 : Blo 1064615 7128107 := bstep (se 1 (by rfl) ⟨5346080, by rfl⟩ : syracuseStep 7128107 = 10692161) B10692161
theorem B1066063 : Blo 1064615 1066063 := bstep (se 1 (by rfl) ⟨799547, by rfl⟩ : syracuseStep 1066063 = 1599095) B1599095
theorem B1066079 : Blo 1064615 1066079 := bstep (se 1 (by rfl) ⟨799559, by rfl⟩ : syracuseStep 1066079 = 1599119) B1599119
theorem B1066107 : Blo 1064615 1066107 := bstep (se 1 (by rfl) ⟨799580, by rfl⟩ : syracuseStep 1066107 = 1599161) B1599161
theorem B1066159 : Blo 1064615 1066159 := bstep (se 1 (by rfl) ⟨799619, by rfl⟩ : syracuseStep 1066159 = 1599239) B1599239
theorem B1066183 : Blo 1064615 1066183 := bstep (se 1 (by rfl) ⟨799637, by rfl⟩ : syracuseStep 1066183 = 1599275) B1599275
theorem B1066203 : Blo 1064615 1066203 := bstep (se 1 (by rfl) ⟨799652, by rfl⟩ : syracuseStep 1066203 = 1599305) B1599305
theorem B4375819 : Blo 1064615 4375819 := bstep (se 1 (by rfl) ⟨3281864, by rfl⟩ : syracuseStep 4375819 = 6563729) B6563729
theorem B1066279 : Blo 1064615 1066279 := bstep (se 1 (by rfl) ⟨799709, by rfl⟩ : syracuseStep 1066279 = 1599419) B1599419
theorem B1066319 : Blo 1064615 1066319 := bstep (se 1 (by rfl) ⟨799739, by rfl⟩ : syracuseStep 1066319 = 1599479) B1599479
theorem B1066335 : Blo 1064615 1066335 := bstep (se 1 (by rfl) ⟨799751, by rfl⟩ : syracuseStep 1066335 = 1599503) B1599503
theorem B1066363 : Blo 1064615 1066363 := bstep (se 1 (by rfl) ⟨799772, by rfl⟩ : syracuseStep 1066363 = 1599545) B1599545
theorem B1066415 : Blo 1064615 1066415 := bstep (se 1 (by rfl) ⟨799811, by rfl⟩ : syracuseStep 1066415 = 1599623) B1599623
theorem B1066439 : Blo 1064615 1066439 := bstep (se 1 (by rfl) ⟨799829, by rfl⟩ : syracuseStep 1066439 = 1599659) B1599659
theorem B1066459 : Blo 1064615 1066459 := bstep (se 1 (by rfl) ⟨799844, by rfl⟩ : syracuseStep 1066459 = 1599689) B1599689
theorem B1066535 : Blo 1064615 1066535 := bstep (se 1 (by rfl) ⟨799901, by rfl⟩ : syracuseStep 1066535 = 1599803) B1599803
theorem B1066575 : Blo 1064615 1066575 := bstep (se 1 (by rfl) ⟨799931, by rfl⟩ : syracuseStep 1066575 = 1599863) B1599863
theorem B1066591 : Blo 1064615 1066591 := bstep (se 1 (by rfl) ⟨799943, by rfl⟩ : syracuseStep 1066591 = 1599887) B1599887
theorem B2279009 : Blo 1064615 2279009 := bstep (se 2 (by rfl) ⟨854628, by rfl⟩ : syracuseStep 2279009 = 1709257) B1709257
theorem B1066619 : Blo 1064615 1066619 := bstep (se 1 (by rfl) ⟨799964, by rfl⟩ : syracuseStep 1066619 = 1599929) B1599929
theorem B1066671 : Blo 1064615 1066671 := bstep (se 1 (by rfl) ⟨800003, by rfl⟩ : syracuseStep 1066671 = 1600007) B1600007
theorem B1066695 : Blo 1064615 1066695 := bstep (se 1 (by rfl) ⟨800021, by rfl⟩ : syracuseStep 1066695 = 1600043) B1600043
theorem B1066715 : Blo 1064615 1066715 := bstep (se 1 (by rfl) ⟨800036, by rfl⟩ : syracuseStep 1066715 = 1600073) B1600073
theorem B1066791 : Blo 1064615 1066791 := bstep (se 1 (by rfl) ⟨800093, by rfl⟩ : syracuseStep 1066791 = 1600187) B1600187
theorem B1066831 : Blo 1064615 1066831 := bstep (se 1 (by rfl) ⟨800123, by rfl⟩ : syracuseStep 1066831 = 1600247) B1600247
theorem B1066847 : Blo 1064615 1066847 := bstep (se 1 (by rfl) ⟨800135, by rfl⟩ : syracuseStep 1066847 = 1600271) B1600271
theorem B1066875 : Blo 1064615 1066875 := bstep (se 1 (by rfl) ⟨800156, by rfl⟩ : syracuseStep 1066875 = 1600313) B1600313
theorem B1066927 : Blo 1064615 1066927 := bstep (se 1 (by rfl) ⟨800195, by rfl⟩ : syracuseStep 1066927 = 1600391) B1600391
theorem B1066951 : Blo 1064615 1066951 := bstep (se 1 (by rfl) ⟨800213, by rfl⟩ : syracuseStep 1066951 = 1600427) B1600427
theorem B1066971 : Blo 1064615 1066971 := bstep (se 1 (by rfl) ⟨800228, by rfl⟩ : syracuseStep 1066971 = 1600457) B1600457
theorem B13649957 : Blo 1064615 13649957 := bstep (se 4 (by rfl) ⟨1279683, by rfl⟩ : syracuseStep 13649957 = 2559367) B2559367
theorem B1067047 : Blo 1064615 1067047 := bstep (se 1 (by rfl) ⟨800285, by rfl⟩ : syracuseStep 1067047 = 1600571) B1600571
theorem B1067087 : Blo 1064615 1067087 := bstep (se 1 (by rfl) ⟨800315, by rfl⟩ : syracuseStep 1067087 = 1600631) B1600631
theorem B1067103 : Blo 1064615 1067103 := bstep (se 1 (by rfl) ⟨800327, by rfl⟩ : syracuseStep 1067103 = 1600655) B1600655
theorem B1067131 : Blo 1064615 1067131 := bstep (se 1 (by rfl) ⟨800348, by rfl⟩ : syracuseStep 1067131 = 1600697) B1600697
theorem B1067183 : Blo 1064615 1067183 := bstep (se 1 (by rfl) ⟨800387, by rfl⟩ : syracuseStep 1067183 = 1600775) B1600775
theorem B1067207 : Blo 1064615 1067207 := bstep (se 1 (by rfl) ⟨800405, by rfl⟩ : syracuseStep 1067207 = 1600811) B1600811
theorem B1067227 : Blo 1064615 1067227 := bstep (se 1 (by rfl) ⟨800420, by rfl⟩ : syracuseStep 1067227 = 1600841) B1600841
theorem B1067303 : Blo 1064615 1067303 := bstep (se 1 (by rfl) ⟨800477, by rfl⟩ : syracuseStep 1067303 = 1600955) B1600955
theorem B1067343 : Blo 1064615 1067343 := bstep (se 1 (by rfl) ⟨800507, by rfl⟩ : syracuseStep 1067343 = 1601015) B1601015
theorem B1067359 : Blo 1064615 1067359 := bstep (se 1 (by rfl) ⟨800519, by rfl⟩ : syracuseStep 1067359 = 1601039) B1601039
theorem B1067387 : Blo 1064615 1067387 := bstep (se 1 (by rfl) ⟨800540, by rfl⟩ : syracuseStep 1067387 = 1601081) B1601081
theorem B1067439 : Blo 1064615 1067439 := bstep (se 1 (by rfl) ⟨800579, by rfl⟩ : syracuseStep 1067439 = 1601159) B1601159
theorem B1067463 : Blo 1064615 1067463 := bstep (se 1 (by rfl) ⟨800597, by rfl⟩ : syracuseStep 1067463 = 1601195) B1601195
theorem B1067483 : Blo 1064615 1067483 := bstep (se 1 (by rfl) ⟨800612, by rfl⟩ : syracuseStep 1067483 = 1601225) B1601225
theorem B10242541 : Blo 1064615 10242541 := bstep (se 3 (by rfl) ⟨1920476, by rfl⟩ : syracuseStep 10242541 = 3840953) B3840953
theorem B1067559 : Blo 1064615 1067559 := bstep (se 1 (by rfl) ⟨800669, by rfl⟩ : syracuseStep 1067559 = 1601339) B1601339
theorem B1067599 : Blo 1064615 1067599 := bstep (se 1 (by rfl) ⟨800699, by rfl⟩ : syracuseStep 1067599 = 1601399) B1601399
theorem B1067615 : Blo 1064615 1067615 := bstep (se 1 (by rfl) ⟨800711, by rfl⟩ : syracuseStep 1067615 = 1601423) B1601423
theorem B1067643 : Blo 1064615 1067643 := bstep (se 1 (by rfl) ⟨800732, by rfl⟩ : syracuseStep 1067643 = 1601465) B1601465
theorem B1067695 : Blo 1064615 1067695 := bstep (se 1 (by rfl) ⟨800771, by rfl⟩ : syracuseStep 1067695 = 1601543) B1601543
theorem B1067719 : Blo 1064615 1067719 := bstep (se 1 (by rfl) ⟨800789, by rfl⟩ : syracuseStep 1067719 = 1601579) B1601579
theorem B1067739 : Blo 1064615 1067739 := bstep (se 1 (by rfl) ⟨800804, by rfl⟩ : syracuseStep 1067739 = 1601609) B1601609
theorem B1067815 : Blo 1064615 1067815 := bstep (se 1 (by rfl) ⟨800861, by rfl⟩ : syracuseStep 1067815 = 1601723) B1601723
theorem B20794187 : Blo 1064615 20794187 := bstep (se 1 (by rfl) ⟨15595640, by rfl⟩ : syracuseStep 20794187 = 31191281) B31191281
theorem B1067855 : Blo 1064615 1067855 := bstep (se 1 (by rfl) ⟨800891, by rfl⟩ : syracuseStep 1067855 = 1601783) B1601783
theorem B1067871 : Blo 1064615 1067871 := bstep (se 1 (by rfl) ⟨800903, by rfl⟩ : syracuseStep 1067871 = 1601807) B1601807
theorem B1067899 : Blo 1064615 1067899 := bstep (se 1 (by rfl) ⟨800924, by rfl⟩ : syracuseStep 1067899 = 1601849) B1601849
theorem B1067951 : Blo 1064615 1067951 := bstep (se 1 (by rfl) ⟨800963, by rfl⟩ : syracuseStep 1067951 = 1601927) B1601927
theorem B1067975 : Blo 1064615 1067975 := bstep (se 1 (by rfl) ⟨800981, by rfl⟩ : syracuseStep 1067975 = 1601963) B1601963
theorem B1067995 : Blo 1064615 1067995 := bstep (se 1 (by rfl) ⟨800996, by rfl⟩ : syracuseStep 1067995 = 1601993) B1601993
theorem B1068071 : Blo 1064615 1068071 := bstep (se 1 (by rfl) ⟨801053, by rfl⟩ : syracuseStep 1068071 = 1602107) B1602107
theorem B1068111 : Blo 1064615 1068111 := bstep (se 1 (by rfl) ⟨801083, by rfl⟩ : syracuseStep 1068111 = 1602167) B1602167
theorem B1068127 : Blo 1064615 1068127 := bstep (se 1 (by rfl) ⟨801095, by rfl⟩ : syracuseStep 1068127 = 1602191) B1602191
theorem B1199227 : Blo 1064615 1199227 := bstep (se 1 (by rfl) ⟨899420, by rfl⟩ : syracuseStep 1199227 = 1798841) B1798841
theorem B1068155 : Blo 1064615 1068155 := bstep (se 1 (by rfl) ⟨801116, by rfl⟩ : syracuseStep 1068155 = 1602233) B1602233
theorem B1068207 : Blo 1064615 1068207 := bstep (se 1 (by rfl) ⟨801155, by rfl⟩ : syracuseStep 1068207 = 1602311) B1602311
theorem B1068231 : Blo 1064615 1068231 := bstep (se 1 (by rfl) ⟨801173, by rfl⟩ : syracuseStep 1068231 = 1602347) B1602347
theorem B1068251 : Blo 1064615 1068251 := bstep (se 1 (by rfl) ⟨801188, by rfl⟩ : syracuseStep 1068251 = 1602377) B1602377
theorem B1068327 : Blo 1064615 1068327 := bstep (se 1 (by rfl) ⟨801245, by rfl⟩ : syracuseStep 1068327 = 1602491) B1602491
theorem B1068367 : Blo 1064615 1068367 := bstep (se 1 (by rfl) ⟨801275, by rfl⟩ : syracuseStep 1068367 = 1602551) B1602551
theorem B4050263 : Blo 1064615 4050263 := bstep (se 1 (by rfl) ⟨3037697, by rfl⟩ : syracuseStep 4050263 = 6075395) B6075395
theorem B1068383 : Blo 1064615 1068383 := bstep (se 1 (by rfl) ⟨801287, by rfl⟩ : syracuseStep 1068383 = 1602575) B1602575
theorem B1068411 : Blo 1064615 1068411 := bstep (se 1 (by rfl) ⟨801308, by rfl⟩ : syracuseStep 1068411 = 1602617) B1602617
theorem B5393789 : Blo 1064615 5393789 := bstep (se 3 (by rfl) ⟨1011335, by rfl⟩ : syracuseStep 5393789 = 2022671) B2022671
theorem B1068463 : Blo 1064615 1068463 := bstep (se 1 (by rfl) ⟨801347, by rfl⟩ : syracuseStep 1068463 = 1602695) B1602695
theorem B1068487 : Blo 1064615 1068487 := bstep (se 1 (by rfl) ⟨801365, by rfl⟩ : syracuseStep 1068487 = 1602731) B1602731
theorem B1068507 : Blo 1064615 1068507 := bstep (se 1 (by rfl) ⟨801380, by rfl⟩ : syracuseStep 1068507 = 1602761) B1602761
theorem B1068583 : Blo 1064615 1068583 := bstep (se 1 (by rfl) ⟨801437, by rfl⟩ : syracuseStep 1068583 = 1602875) B1602875
theorem B1199695 : Blo 1064615 1199695 := bstep (se 1 (by rfl) ⟨899771, by rfl⟩ : syracuseStep 1199695 = 1799543) B1799543
theorem B10374779 : Blo 1064615 10374779 := bstep (se 1 (by rfl) ⟨7781084, by rfl⟩ : syracuseStep 10374779 = 15562169) B15562169
theorem B11685509 : Blo 1064615 11685509 := bstep (se 4 (by rfl) ⟨1095516, by rfl⟩ : syracuseStep 11685509 = 2191033) B2191033
theorem B2739851 : Blo 1064615 2739851 := bstep (se 1 (by rfl) ⟨2054888, by rfl⟩ : syracuseStep 2739851 = 4109777) B4109777
theorem B5852819 : Blo 1064615 5852819 := bstep (se 1 (by rfl) ⟨4389614, by rfl⟩ : syracuseStep 5852819 = 8779229) B8779229
theorem B12308257 : Blo 1064615 12308257 := bstep (se 2 (by rfl) ⟨4615596, by rfl⟩ : syracuseStep 12308257 = 9231193) B9231193
theorem B3559355 : Blo 1064615 3559355 := bstep (se 1 (by rfl) ⟨2669516, by rfl⟩ : syracuseStep 3559355 = 5339033) B5339033
theorem B1200091 : Blo 1064615 1200091 := bstep (se 1 (by rfl) ⟨900068, by rfl⟩ : syracuseStep 1200091 = 1800137) B1800137
theorem B7688195 : Blo 1064615 7688195 := bstep (se 1 (by rfl) ⟨5766146, by rfl⟩ : syracuseStep 7688195 = 11532293) B11532293
theorem B1200559 : Blo 1064615 1200559 := bstep (se 1 (by rfl) ⟨900419, by rfl⟩ : syracuseStep 1200559 = 1800839) B1800839
theorem B2282195 : Blo 1064615 2282195 := bstep (se 1 (by rfl) ⟨1711646, by rfl⟩ : syracuseStep 2282195 = 3423293) B3423293
theorem B1200991 : Blo 1064615 1200991 := bstep (se 1 (by rfl) ⟨900743, by rfl⟩ : syracuseStep 1200991 = 1801487) B1801487
theorem B3036217 : Blo 1064615 3036217 := bstep (se 2 (by rfl) ⟨1138581, by rfl⟩ : syracuseStep 3036217 = 2277163) B2277163
theorem B1201351 : Blo 1064615 1201351 := bstep (se 1 (by rfl) ⟨901013, by rfl⟩ : syracuseStep 1201351 = 1802027) B1802027
theorem B3593483 : Blo 1064615 3593483 := bstep (se 1 (by rfl) ⟨2695112, by rfl⟩ : syracuseStep 3593483 = 5390225) B5390225
theorem B3593753 : Blo 1064615 3593753 := bstep (se 2 (by rfl) ⟨1347657, by rfl⟩ : syracuseStep 3593753 = 2695315) B2695315
theorem B6084395 : Blo 1064615 6084395 := bstep (se 1 (by rfl) ⟨4563296, by rfl⟩ : syracuseStep 6084395 = 9126593) B9126593
theorem B3463183 : Blo 1064615 3463183 := bstep (se 1 (by rfl) ⟨2597387, by rfl⟩ : syracuseStep 3463183 = 5194775) B5194775
theorem B4053149 : Blo 1064615 4053149 := bstep (se 3 (by rfl) ⟨759965, by rfl⟩ : syracuseStep 4053149 = 1519931) B1519931
theorem B29186507 : Blo 1064615 29186507 := bstep (se 1 (by rfl) ⟨21889880, by rfl⟩ : syracuseStep 29186507 = 43779761) B43779761
theorem B2021851 : Blo 1064615 2021851 := bstep (se 1 (by rfl) ⟨1516388, by rfl⟩ : syracuseStep 2021851 = 3032777) B3032777
theorem B2021897 : Blo 1064615 2021897 := bstep (se 2 (by rfl) ⟨758211, by rfl⟩ : syracuseStep 2021897 = 1516423) B1516423
theorem B6085145 : Blo 1064615 6085145 := bstep (se 2 (by rfl) ⟨2281929, by rfl⟩ : syracuseStep 6085145 = 4563859) B4563859
theorem B1366651 : Blo 1064615 1366651 := bstep (se 1 (by rfl) ⟨1024988, by rfl⟩ : syracuseStep 1366651 = 2049977) B2049977
theorem B3594887 : Blo 1064615 3594887 := bstep (se 1 (by rfl) ⟨2696165, by rfl⟩ : syracuseStep 3594887 = 5392331) B5392331
theorem B3594941 : Blo 1064615 3594941 := bstep (se 3 (by rfl) ⟨674051, by rfl⟩ : syracuseStep 3594941 = 1348103) B1348103
theorem B4053833 : Blo 1064615 4053833 := bstep (se 2 (by rfl) ⟨1520187, by rfl⟩ : syracuseStep 4053833 = 3040375) B3040375
theorem B2022239 : Blo 1064615 2022239 := bstep (se 1 (by rfl) ⟨1516679, by rfl⟩ : syracuseStep 2022239 = 3033359) B3033359
theorem B3595103 : Blo 1064615 3595103 := bstep (se 1 (by rfl) ⟨2696327, by rfl⟩ : syracuseStep 3595103 = 5392655) B5392655
theorem B3595265 : Blo 1064615 3595265 := bstep (se 2 (by rfl) ⟨1348224, by rfl⟩ : syracuseStep 3595265 = 2696449) B2696449
theorem B15588395 : Blo 1064615 15588395 := bstep (se 1 (by rfl) ⟨11691296, by rfl⟩ : syracuseStep 15588395 = 23382593) B23382593
theorem B1825849 : Blo 1064615 1825849 := bstep (se 2 (by rfl) ⟨684693, by rfl⟩ : syracuseStep 1825849 = 1369387) B1369387
theorem B4054333 : Blo 1064615 4054333 := bstep (se 3 (by rfl) ⟨760187, by rfl⟩ : syracuseStep 4054333 = 1520375) B1520375
theorem B23092775 : Blo 1064615 23092775 := bstep (se 1 (by rfl) ⟨17319581, by rfl⟩ : syracuseStep 23092775 = 34639163) B34639163
theorem B1597007 : Blo 1064615 1597007 := bstep (se 1 (by rfl) ⟨1197755, by rfl⟩ : syracuseStep 1597007 = 2395511) B2395511
theorem B7298657 : Blo 1064615 7298657 := bstep (se 2 (by rfl) ⟨2736996, by rfl⟩ : syracuseStep 7298657 = 5473993) B5473993
theorem B5398163 : Blo 1064615 5398163 := bstep (se 1 (by rfl) ⟨4048622, by rfl⟩ : syracuseStep 5398163 = 8097245) B8097245
theorem B1597127 : Blo 1064615 1597127 := bstep (se 1 (by rfl) ⟨1197845, by rfl⟩ : syracuseStep 1597127 = 2395691) B2395691
theorem B6151895 : Blo 1064615 6151895 := bstep (se 1 (by rfl) ⟨4613921, by rfl⟩ : syracuseStep 6151895 = 9227843) B9227843
theorem B3596075 : Blo 1064615 3596075 := bstep (se 1 (by rfl) ⟨2697056, by rfl⟩ : syracuseStep 3596075 = 5394113) B5394113
theorem B1597289 : Blo 1064615 1597289 := bstep (se 2 (by rfl) ⟨598983, by rfl⟩ : syracuseStep 1597289 = 1197967) B1197967
theorem B1597367 : Blo 1064615 1597367 := bstep (se 1 (by rfl) ⟨1198025, by rfl⟩ : syracuseStep 1597367 = 2396051) B2396051
theorem B2023355 : Blo 1064615 2023355 := bstep (se 1 (by rfl) ⟨1517516, by rfl⟩ : syracuseStep 2023355 = 3035033) B3035033
theorem B1597403 : Blo 1064615 1597403 := bstep (se 1 (by rfl) ⟨1198052, by rfl⟩ : syracuseStep 1597403 = 2396105) B2396105
theorem B3596345 : Blo 1064615 3596345 := bstep (se 2 (by rfl) ⟨1348629, by rfl⟩ : syracuseStep 3596345 = 2697259) B2697259
theorem B8085581 : Blo 1064615 8085581 := bstep (se 3 (by rfl) ⟨1516046, by rfl⟩ : syracuseStep 8085581 = 3032093) B3032093
theorem B4317299 : Blo 1064615 4317299 := bstep (se 1 (by rfl) ⟨3237974, by rfl⟩ : syracuseStep 4317299 = 6475949) B6475949
theorem B30794053 : Blo 1064615 30794053 := bstep (se 4 (by rfl) ⟨2886942, by rfl⟩ : syracuseStep 30794053 = 5773885) B5773885
theorem B3596669 : Blo 1064615 3596669 := bstep (se 3 (by rfl) ⟨674375, by rfl⟩ : syracuseStep 3596669 = 1348751) B1348751
theorem B2023841 : Blo 1064615 2023841 := bstep (se 2 (by rfl) ⟨758940, by rfl⟩ : syracuseStep 2023841 = 1517881) B1517881
theorem B1597871 : Blo 1064615 1597871 := bstep (se 1 (by rfl) ⟨1198403, by rfl⟩ : syracuseStep 1597871 = 2396807) B2396807
theorem B1925551 : Blo 1064615 1925551 := bstep (se 1 (by rfl) ⟨1444163, by rfl⟩ : syracuseStep 1925551 = 2888327) B2888327
theorem B16441805 : Blo 1064615 16441805 := bstep (se 3 (by rfl) ⟨3082838, by rfl⟩ : syracuseStep 16441805 = 6165677) B6165677
theorem B1597961 : Blo 1064615 1597961 := bstep (se 2 (by rfl) ⟨599235, by rfl⟩ : syracuseStep 1597961 = 1198471) B1198471
theorem B1597991 : Blo 1064615 1597991 := bstep (se 1 (by rfl) ⟨1198493, by rfl⟩ : syracuseStep 1597991 = 2396987) B2396987
theorem B1598075 : Blo 1064615 1598075 := bstep (se 1 (by rfl) ⟨1198556, by rfl⟩ : syracuseStep 1598075 = 2397113) B2397113
theorem B3596939 : Blo 1064615 3596939 := bstep (se 1 (by rfl) ⟨2697704, by rfl⟩ : syracuseStep 3596939 = 5395409) B5395409
theorem B2024183 : Blo 1064615 2024183 := bstep (se 1 (by rfl) ⟨1518137, by rfl⟩ : syracuseStep 2024183 = 3036275) B3036275
theorem B1598201 : Blo 1064615 1598201 := bstep (se 2 (by rfl) ⟨599325, by rfl⟩ : syracuseStep 1598201 = 1198651) B1198651
theorem B1598303 : Blo 1064615 1598303 := bstep (se 1 (by rfl) ⟨1198727, by rfl⟩ : syracuseStep 1598303 = 2397455) B2397455
theorem B1598315 : Blo 1064615 1598315 := bstep (se 1 (by rfl) ⟨1198736, by rfl⟩ : syracuseStep 1598315 = 2397473) B2397473
theorem B1139675 : Blo 1064615 1139675 := bstep (se 1 (by rfl) ⟨854756, by rfl⟩ : syracuseStep 1139675 = 1709513) B1709513
theorem B4056065 : Blo 1064615 4056065 := bstep (se 2 (by rfl) ⟨1521024, by rfl⟩ : syracuseStep 4056065 = 3042049) B3042049
theorem B4547663 : Blo 1064615 4547663 := bstep (se 1 (by rfl) ⟨3410747, by rfl⟩ : syracuseStep 4547663 = 6821495) B6821495
theorem B1598543 : Blo 1064615 1598543 := bstep (se 1 (by rfl) ⟨1198907, by rfl⟩ : syracuseStep 1598543 = 2397815) B2397815
theorem B1598663 : Blo 1064615 1598663 := bstep (se 1 (by rfl) ⟨1198997, by rfl⟩ : syracuseStep 1598663 = 2397995) B2397995
theorem B1598825 : Blo 1064615 1598825 := bstep (se 2 (by rfl) ⟨599559, by rfl⟩ : syracuseStep 1598825 = 1199119) B1199119
theorem B1598903 : Blo 1064615 1598903 := bstep (se 1 (by rfl) ⟨1199177, by rfl⟩ : syracuseStep 1598903 = 2398355) B2398355
theorem B1598939 : Blo 1064615 1598939 := bstep (se 1 (by rfl) ⟨1199204, by rfl⟩ : syracuseStep 1598939 = 2398409) B2398409
theorem B3597857 : Blo 1064615 3597857 := bstep (se 2 (by rfl) ⟨1349196, by rfl⟩ : syracuseStep 3597857 = 2698393) B2698393
theorem B3040865 : Blo 1064615 3040865 := bstep (se 2 (by rfl) ⟨1140324, by rfl⟩ : syracuseStep 3040865 = 2280649) B2280649
theorem B5465723 : Blo 1064615 5465723 := bstep (se 1 (by rfl) ⟨4099292, by rfl⟩ : syracuseStep 5465723 = 8198585) B8198585
theorem B6153943 : Blo 1064615 6153943 := bstep (se 1 (by rfl) ⟨4615457, by rfl⟩ : syracuseStep 6153943 = 9230915) B9230915
theorem B3598073 : Blo 1064615 3598073 := bstep (se 2 (by rfl) ⟨1349277, by rfl⟩ : syracuseStep 3598073 = 2698555) B2698555
theorem B1599407 : Blo 1064615 1599407 := bstep (se 1 (by rfl) ⟨1199555, by rfl⟩ : syracuseStep 1599407 = 2399111) B2399111
theorem B3598343 : Blo 1064615 3598343 := bstep (se 1 (by rfl) ⟨2698757, by rfl⟩ : syracuseStep 3598343 = 5397515) B5397515
theorem B1599497 : Blo 1064615 1599497 := bstep (se 2 (by rfl) ⟨599811, by rfl⟩ : syracuseStep 1599497 = 1199623) B1199623
theorem B2025481 : Blo 1064615 2025481 := bstep (se 2 (by rfl) ⟨759555, by rfl⟩ : syracuseStep 2025481 = 1519111) B1519111
theorem B1599527 : Blo 1064615 1599527 := bstep (se 1 (by rfl) ⟨1199645, by rfl⟩ : syracuseStep 1599527 = 2399291) B2399291
theorem B3598451 : Blo 1064615 3598451 := bstep (se 1 (by rfl) ⟨2698838, by rfl⟩ : syracuseStep 3598451 = 5397677) B5397677
theorem B1599611 : Blo 1064615 1599611 := bstep (se 1 (by rfl) ⟨1199708, by rfl⟩ : syracuseStep 1599611 = 2399417) B2399417
theorem B1599737 : Blo 1064615 1599737 := bstep (se 2 (by rfl) ⟨599901, by rfl⟩ : syracuseStep 1599737 = 1199803) B1199803
theorem B1599839 : Blo 1064615 1599839 := bstep (se 1 (by rfl) ⟨1199879, by rfl⟩ : syracuseStep 1599839 = 2399759) B2399759
theorem B2025823 : Blo 1064615 2025823 := bstep (se 1 (by rfl) ⟨1519367, by rfl⟩ : syracuseStep 2025823 = 3038735) B3038735
theorem B1599851 : Blo 1064615 1599851 := bstep (se 1 (by rfl) ⟨1199888, by rfl⟩ : syracuseStep 1599851 = 2399777) B2399777
theorem B3598721 : Blo 1064615 3598721 := bstep (se 2 (by rfl) ⟨1349520, by rfl⟩ : syracuseStep 3598721 = 2699041) B2699041
theorem B1796539 : Blo 1064615 1796539 := bstep (se 1 (by rfl) ⟨1347404, by rfl⟩ : syracuseStep 1796539 = 2694809) B2694809
theorem B8088011 : Blo 1064615 8088011 := bstep (se 1 (by rfl) ⟨6066008, by rfl⟩ : syracuseStep 8088011 = 12132017) B12132017
theorem B3893741 : Blo 1064615 3893741 := bstep (se 3 (by rfl) ⟨730076, by rfl⟩ : syracuseStep 3893741 = 1460153) B1460153
theorem B1796647 : Blo 1064615 1796647 := bstep (se 1 (by rfl) ⟨1347485, by rfl⟩ : syracuseStep 1796647 = 2694971) B2694971
theorem B1600079 : Blo 1064615 1600079 := bstep (se 1 (by rfl) ⟨1200059, by rfl⟩ : syracuseStep 1600079 = 2400119) B2400119
theorem B3041981 : Blo 1064615 3041981 := bstep (se 3 (by rfl) ⟨570371, by rfl⟩ : syracuseStep 3041981 = 1140743) B1140743
theorem B1600199 : Blo 1064615 1600199 := bstep (se 1 (by rfl) ⟨1200149, by rfl⟩ : syracuseStep 1600199 = 2400299) B2400299
theorem B4549405 : Blo 1064615 4549405 := bstep (se 3 (by rfl) ⟨853013, by rfl⟩ : syracuseStep 4549405 = 1706027) B1706027
theorem B15362891 : Blo 1064615 15362891 := bstep (se 1 (by rfl) ⟨11522168, by rfl⟩ : syracuseStep 15362891 = 23044337) B23044337
theorem B3238751 : Blo 1064615 3238751 := bstep (se 1 (by rfl) ⟨2429063, by rfl⟩ : syracuseStep 3238751 = 4858127) B4858127
theorem B1600361 : Blo 1064615 1600361 := bstep (se 2 (by rfl) ⟨600135, by rfl⟩ : syracuseStep 1600361 = 1200271) B1200271
theorem B1796971 : Blo 1064615 1796971 := bstep (se 1 (by rfl) ⟨1347728, by rfl⟩ : syracuseStep 1796971 = 2695457) B2695457
theorem B1600439 : Blo 1064615 1600439 := bstep (se 1 (by rfl) ⟨1200329, by rfl⟩ : syracuseStep 1600439 = 2400659) B2400659
theorem B1600475 : Blo 1064615 1600475 := bstep (se 1 (by rfl) ⟨1200356, by rfl⟩ : syracuseStep 1600475 = 2400713) B2400713
theorem B3042323 : Blo 1064615 3042323 := bstep (se 1 (by rfl) ⟨2281742, by rfl⟩ : syracuseStep 3042323 = 4563485) B4563485
theorem B4385945 : Blo 1064615 4385945 := bstep (se 2 (by rfl) ⟨1644729, by rfl⟩ : syracuseStep 4385945 = 3289459) B3289459
theorem B3599531 : Blo 1064615 3599531 := bstep (se 1 (by rfl) ⟨2699648, by rfl⟩ : syracuseStep 3599531 = 5399297) B5399297
theorem B38890691 : Blo 1064615 38890691 := bstep (se 1 (by rfl) ⟨29168018, by rfl⟩ : syracuseStep 38890691 = 58336037) B58336037
theorem B6843791 : Blo 1064615 6843791 := bstep (se 1 (by rfl) ⟨5132843, by rfl⟩ : syracuseStep 6843791 = 10265687) B10265687
theorem B1600943 : Blo 1064615 1600943 := bstep (se 1 (by rfl) ⟨1200707, by rfl⟩ : syracuseStep 1600943 = 2401415) B2401415
theorem B2026939 : Blo 1064615 2026939 := bstep (se 1 (by rfl) ⟨1520204, by rfl⟩ : syracuseStep 2026939 = 3040409) B3040409
theorem B2027015 : Blo 1064615 2027015 := bstep (se 1 (by rfl) ⟨1520261, by rfl⟩ : syracuseStep 2027015 = 3040523) B3040523
theorem B1601033 : Blo 1064615 1601033 := bstep (se 2 (by rfl) ⟨600387, by rfl⟩ : syracuseStep 1601033 = 1200775) B1200775
theorem B1601063 : Blo 1064615 1601063 := bstep (se 1 (by rfl) ⟨1200797, by rfl⟩ : syracuseStep 1601063 = 2401595) B2401595
theorem B6843943 : Blo 1064615 6843943 := bstep (se 1 (by rfl) ⟨5132957, by rfl⟩ : syracuseStep 6843943 = 10265915) B10265915
theorem B1601147 : Blo 1064615 1601147 := bstep (se 1 (by rfl) ⟨1200860, by rfl⟩ : syracuseStep 1601147 = 2401721) B2401721
theorem B3600071 : Blo 1064615 3600071 := bstep (se 1 (by rfl) ⟨2700053, by rfl⟩ : syracuseStep 3600071 = 5400107) B5400107
theorem B39415517 : Blo 1064615 39415517 := bstep (se 3 (by rfl) ⟨7390409, by rfl⟩ : syracuseStep 39415517 = 14780819) B14780819
theorem B1601273 : Blo 1064615 1601273 := bstep (se 2 (by rfl) ⟨600477, by rfl⟩ : syracuseStep 1601273 = 1200955) B1200955
theorem B1601375 : Blo 1064615 1601375 := bstep (se 1 (by rfl) ⟨1201031, by rfl⟩ : syracuseStep 1601375 = 2402063) B2402063
theorem B1601387 : Blo 1064615 1601387 := bstep (se 1 (by rfl) ⟨1201040, by rfl⟩ : syracuseStep 1601387 = 2402081) B2402081
theorem B1798031 : Blo 1064615 1798031 := bstep (se 1 (by rfl) ⟨1348523, by rfl⟩ : syracuseStep 1798031 = 2697047) B2697047
theorem B2027425 : Blo 1064615 2027425 := bstep (se 2 (by rfl) ⟨760284, by rfl⟩ : syracuseStep 2027425 = 1520569) B1520569
theorem B1601615 : Blo 1064615 1601615 := bstep (se 1 (by rfl) ⟨1201211, by rfl⟩ : syracuseStep 1601615 = 2402423) B2402423
theorem B4550737 : Blo 1064615 4550737 := bstep (se 2 (by rfl) ⟨1706526, by rfl⟩ : syracuseStep 4550737 = 3413053) B3413053
theorem B1798267 : Blo 1064615 1798267 := bstep (se 1 (by rfl) ⟨1348700, by rfl⟩ : syracuseStep 1798267 = 2697401) B2697401
theorem B4321451 : Blo 1064615 4321451 := bstep (se 1 (by rfl) ⟨3241088, by rfl⟩ : syracuseStep 4321451 = 6482177) B6482177
theorem B1601735 : Blo 1064615 1601735 := bstep (se 1 (by rfl) ⟨1201301, by rfl⟩ : syracuseStep 1601735 = 2402603) B2402603
theorem B2027767 : Blo 1064615 2027767 := bstep (se 1 (by rfl) ⟨1520825, by rfl⟩ : syracuseStep 2027767 = 3041651) B3041651
theorem B1601897 : Blo 1064615 1601897 := bstep (se 2 (by rfl) ⟨600711, by rfl⟩ : syracuseStep 1601897 = 1201423) B1201423
theorem B1601975 : Blo 1064615 1601975 := bstep (se 1 (by rfl) ⟨1201481, by rfl⟩ : syracuseStep 1601975 = 2402963) B2402963
theorem B1602011 : Blo 1064615 1602011 := bstep (se 1 (by rfl) ⟨1201508, by rfl⟩ : syracuseStep 1602011 = 2403017) B2403017
theorem B2159111 : Blo 1064615 2159111 := bstep (se 1 (by rfl) ⟨1619333, by rfl⟩ : syracuseStep 2159111 = 3238667) B3238667
theorem B3600935 : Blo 1064615 3600935 := bstep (se 1 (by rfl) ⟨2700701, by rfl⟩ : syracuseStep 3600935 = 5401403) B5401403
theorem B2028071 : Blo 1064615 2028071 := bstep (se 1 (by rfl) ⟨1521053, by rfl⟩ : syracuseStep 2028071 = 3042107) B3042107
theorem B3601043 : Blo 1064615 3601043 := bstep (se 1 (by rfl) ⟨2700782, by rfl⟩ : syracuseStep 3601043 = 5401565) B5401565
theorem B4551353 : Blo 1064615 4551353 := bstep (se 2 (by rfl) ⟨1706757, by rfl⟩ : syracuseStep 4551353 = 3413515) B3413515
theorem B5403347 : Blo 1064615 5403347 := bstep (se 1 (by rfl) ⟨4052510, by rfl⟩ : syracuseStep 5403347 = 8105021) B8105021
theorem B8090441 : Blo 1064615 8090441 := bstep (se 2 (by rfl) ⟨3033915, by rfl⟩ : syracuseStep 8090441 = 6067831) B6067831
theorem B3601259 : Blo 1064615 3601259 := bstep (se 1 (by rfl) ⟨2700944, by rfl⟩ : syracuseStep 3601259 = 5401889) B5401889
theorem B3601313 : Blo 1064615 3601313 := bstep (se 2 (by rfl) ⟨1350492, by rfl⟩ : syracuseStep 3601313 = 2700985) B2700985
theorem B1602479 : Blo 1064615 1602479 := bstep (se 1 (by rfl) ⟨1201859, by rfl⟩ : syracuseStep 1602479 = 2403719) B2403719
theorem B1799131 : Blo 1064615 1799131 := bstep (se 1 (by rfl) ⟨1349348, by rfl⟩ : syracuseStep 1799131 = 2698697) B2698697
theorem B1602569 : Blo 1064615 1602569 := bstep (se 2 (by rfl) ⟨600963, by rfl⟩ : syracuseStep 1602569 = 1201927) B1201927
theorem B1602599 : Blo 1064615 1602599 := bstep (se 1 (by rfl) ⟨1201949, by rfl⟩ : syracuseStep 1602599 = 2403899) B2403899
theorem B1602683 : Blo 1064615 1602683 := bstep (se 1 (by rfl) ⟨1202012, by rfl⟩ : syracuseStep 1602683 = 2404025) B2404025
theorem B1602809 : Blo 1064615 1602809 := bstep (se 2 (by rfl) ⟨601053, by rfl⟩ : syracuseStep 1602809 = 1202107) B1202107
theorem B1602911 : Blo 1064615 1602911 := bstep (se 1 (by rfl) ⟨1202183, by rfl⟩ : syracuseStep 1602911 = 2404367) B2404367
theorem B1602923 : Blo 1064615 1602923 := bstep (se 1 (by rfl) ⟨1202192, by rfl⟩ : syracuseStep 1602923 = 2404385) B2404385
theorem B3601907 : Blo 1064615 3601907 := bstep (se 1 (by rfl) ⟨2701430, by rfl⟩ : syracuseStep 3601907 = 5402861) B5402861
theorem B1799759 : Blo 1064615 1799759 := bstep (se 1 (by rfl) ⟨1349819, by rfl⟩ : syracuseStep 1799759 = 2699639) B2699639
theorem B7698053 : Blo 1064615 7698053 := bstep (se 4 (by rfl) ⟨721692, by rfl⟩ : syracuseStep 7698053 = 1443385) B1443385
theorem B7304843 : Blo 1064615 7304843 := bstep (se 1 (by rfl) ⟨5478632, by rfl⟩ : syracuseStep 7304843 = 10957265) B10957265
theorem B3602447 : Blo 1064615 3602447 := bstep (se 1 (by rfl) ⟨2701835, by rfl⟩ : syracuseStep 3602447 = 5403671) B5403671
theorem B9107761 : Blo 1064615 9107761 := bstep (se 2 (by rfl) ⟨3415410, by rfl⟩ : syracuseStep 9107761 = 6830821) B6830821
theorem B1800623 : Blo 1064615 1800623 := bstep (se 1 (by rfl) ⟨1350467, by rfl⟩ : syracuseStep 1800623 = 2700935) B2700935
theorem B84408875 : Blo 1064615 84408875 := bstep (se 1 (by rfl) ⟨63306656, by rfl⟩ : syracuseStep 84408875 = 126613313) B126613313
theorem B3603041 : Blo 1064615 3603041 := bstep (se 2 (by rfl) ⟨1351140, by rfl⟩ : syracuseStep 3603041 = 2702281) B2702281
theorem B5765843 : Blo 1064615 5765843 := bstep (se 1 (by rfl) ⟨4324382, by rfl⟩ : syracuseStep 5765843 = 8648765) B8648765
theorem B1080103 : Blo 1064615 1080103 := bstep (se 1 (by rfl) ⟨810077, by rfl⟩ : syracuseStep 1080103 = 1620155) B1620155
theorem B1801055 : Blo 1064615 1801055 := bstep (se 1 (by rfl) ⟨1350791, by rfl⟩ : syracuseStep 1801055 = 2701583) B2701583
theorem B1440617 : Blo 1064615 1440617 := bstep (se 2 (by rfl) ⟨540231, by rfl⟩ : syracuseStep 1440617 = 1080463) B1080463
theorem B2194283 : Blo 1064615 2194283 := bstep (se 1 (by rfl) ⟨1645712, by rfl⟩ : syracuseStep 2194283 = 3291425) B3291425
theorem B5405615 : Blo 1064615 5405615 := bstep (se 1 (by rfl) ⟨4054211, by rfl⟩ : syracuseStep 5405615 = 8108423) B8108423
theorem B4553729 : Blo 1064615 4553729 := bstep (se 2 (by rfl) ⟨1707648, by rfl⟩ : syracuseStep 4553729 = 3415297) B3415297
theorem B6487235 : Blo 1064615 6487235 := bstep (se 1 (by rfl) ⟨4865426, by rfl⟩ : syracuseStep 6487235 = 9730853) B9730853
theorem B6585725 : Blo 1064615 6585725 := bstep (se 3 (by rfl) ⟨1234823, by rfl⟩ : syracuseStep 6585725 = 2469647) B2469647
theorem B1801615 : Blo 1064615 1801615 := bstep (se 1 (by rfl) ⟨1351211, by rfl⟩ : syracuseStep 1801615 = 2702423) B2702423
theorem B3243529 : Blo 1064615 3243529 := bstep (se 2 (by rfl) ⟨1216323, by rfl⟩ : syracuseStep 3243529 = 2432647) B2432647
theorem B1081031 : Blo 1064615 1081031 := bstep (se 1 (by rfl) ⟨810773, by rfl⟩ : syracuseStep 1081031 = 1621547) B1621547
theorem B12156803 : Blo 1064615 12156803 := bstep (se 1 (by rfl) ⟨9117602, by rfl⟩ : syracuseStep 12156803 = 18235205) B18235205
theorem B7700359 : Blo 1064615 7700359 := bstep (se 1 (by rfl) ⟨5775269, by rfl⟩ : syracuseStep 7700359 = 11550539) B11550539
theorem B5472307 : Blo 1064615 5472307 := bstep (se 1 (by rfl) ⟨4104230, by rfl⟩ : syracuseStep 5472307 = 8208461) B8208461
theorem B4620347 : Blo 1064615 4620347 := bstep (se 1 (by rfl) ⟨3465260, by rfl⟩ : syracuseStep 4620347 = 6930521) B6930521
theorem B1081631 : Blo 1064615 1081631 := bstep (se 1 (by rfl) ⟨811223, by rfl⟩ : syracuseStep 1081631 = 1622447) B1622447
theorem B1802587 : Blo 1064615 1802587 := bstep (se 1 (by rfl) ⟨1351940, by rfl⟩ : syracuseStep 1802587 = 2703881) B2703881
theorem B41058737 : Blo 1064615 41058737 := bstep (se 2 (by rfl) ⟨15397026, by rfl⟩ : syracuseStep 41058737 = 30794053) B30794053
theorem B4555385 : Blo 1064615 4555385 := bstep (se 2 (by rfl) ⟨1708269, by rfl⟩ : syracuseStep 4555385 = 3416539) B3416539
theorem B4752071 : Blo 1064615 4752071 := bstep (se 1 (by rfl) ⟨3564053, by rfl⟩ : syracuseStep 4752071 = 7128107) B7128107
theorem B2164105 : Blo 1064615 2164105 := bstep (se 2 (by rfl) ⟨811539, by rfl⟩ : syracuseStep 2164105 = 1623079) B1623079
theorem B18974105 : Blo 1064615 18974105 := bstep (se 2 (by rfl) ⟨7115289, by rfl⟩ : syracuseStep 18974105 = 14230579) B14230579
theorem B2885063 : Blo 1064615 2885063 := bstep (se 1 (by rfl) ⟨2163797, by rfl⟩ : syracuseStep 2885063 = 4327595) B4327595
theorem B3606173 : Blo 1064615 3606173 := bstep (se 3 (by rfl) ⟨676157, by rfl⟩ : syracuseStep 3606173 = 1352315) B1352315
theorem B5834425 : Blo 1064615 5834425 := bstep (se 2 (by rfl) ⟨2187909, by rfl⟩ : syracuseStep 5834425 = 4375819) B4375819
theorem B13862791 : Blo 1064615 13862791 := bstep (se 1 (by rfl) ⟨10397093, by rfl⟩ : syracuseStep 13862791 = 20794187) B20794187
theorem B6916519 : Blo 1064615 6916519 := bstep (se 1 (by rfl) ⟨5187389, by rfl⟩ : syracuseStep 6916519 = 10374779) B10374779
theorem B3901879 : Blo 1064615 3901879 := bstep (se 1 (by rfl) ⟨2926409, by rfl⟩ : syracuseStep 3901879 = 5852819) B5852819
theorem B2558483 : Blo 1064615 2558483 := bstep (se 1 (by rfl) ⟨1918862, by rfl⟩ : syracuseStep 2558483 = 3837725) B3837725
theorem B2428123 : Blo 1064615 2428123 := bstep (se 1 (by rfl) ⟨1821092, by rfl⟩ : syracuseStep 2428123 = 3642185) B3642185
theorem B2395385 : Blo 1064615 2395385 := bstep (se 2 (by rfl) ⟨898269, by rfl⟩ : syracuseStep 2395385 = 1796539) B1796539
theorem B2395529 : Blo 1064615 2395529 := bstep (se 2 (by rfl) ⟨898323, by rfl⟩ : syracuseStep 2395529 = 1796647) B1796647
theorem B2395655 : Blo 1064615 2395655 := bstep (se 1 (by rfl) ⟨1796741, by rfl⟩ : syracuseStep 2395655 = 3593483) B3593483
theorem B2395835 : Blo 1064615 2395835 := bstep (se 1 (by rfl) ⟨1796876, by rfl⟩ : syracuseStep 2395835 = 3593753) B3593753
theorem B6065873 : Blo 1064615 6065873 := bstep (se 2 (by rfl) ⟨2274702, by rfl⟩ : syracuseStep 6065873 = 4549405) B4549405
theorem B2395961 : Blo 1064615 2395961 := bstep (se 2 (by rfl) ⟨898485, by rfl⟩ : syracuseStep 2395961 = 1796971) B1796971
theorem B11538521 : Blo 1064615 11538521 := bstep (se 2 (by rfl) ⟨4326945, by rfl⟩ : syracuseStep 11538521 = 8653891) B8653891
theorem B1347931 : Blo 1064615 1347931 := bstep (se 1 (by rfl) ⟨1010948, by rfl⟩ : syracuseStep 1347931 = 2021897) B2021897
theorem B2396591 : Blo 1064615 2396591 := bstep (se 1 (by rfl) ⟨1797443, by rfl⟩ : syracuseStep 2396591 = 3594887) B3594887
theorem B2396627 : Blo 1064615 2396627 := bstep (se 1 (by rfl) ⟨1797470, by rfl⟩ : syracuseStep 2396627 = 3594941) B3594941
theorem B1348159 : Blo 1064615 1348159 := bstep (se 1 (by rfl) ⟨1011119, by rfl⟩ : syracuseStep 1348159 = 2022239) B2022239
theorem B2396735 : Blo 1064615 2396735 := bstep (se 1 (by rfl) ⟨1797551, by rfl⟩ : syracuseStep 2396735 = 3595103) B3595103
theorem B2396843 : Blo 1064615 2396843 := bstep (se 1 (by rfl) ⟨1797632, by rfl⟩ : syracuseStep 2396843 = 3595265) B3595265
theorem B10392263 : Blo 1064615 10392263 := bstep (se 1 (by rfl) ⟨7794197, by rfl⟩ : syracuseStep 10392263 = 15588395) B15588395
theorem B1708879 : Blo 1064615 1708879 := bstep (se 1 (by rfl) ⟨1281659, by rfl⟩ : syracuseStep 1708879 = 2563319) B2563319
theorem B4101263 : Blo 1064615 4101263 := bstep (se 1 (by rfl) ⟨3075947, by rfl⟩ : syracuseStep 4101263 = 6151895) B6151895
theorem B2397383 : Blo 1064615 2397383 := bstep (se 1 (by rfl) ⟨1798037, by rfl⟩ : syracuseStep 2397383 = 3596075) B3596075
theorem B1348903 : Blo 1064615 1348903 := bstep (se 1 (by rfl) ⟨1011677, by rfl⟩ : syracuseStep 1348903 = 2023355) B2023355
theorem B2397563 : Blo 1064615 2397563 := bstep (se 1 (by rfl) ⟨1798172, by rfl⟩ : syracuseStep 2397563 = 3596345) B3596345
theorem B6067649 : Blo 1064615 6067649 := bstep (se 2 (by rfl) ⟨2275368, by rfl⟩ : syracuseStep 6067649 = 4550737) B4550737
theorem B10261997 : Blo 1064615 10261997 := bstep (se 3 (by rfl) ⟨1924124, by rfl⟩ : syracuseStep 10261997 = 3848249) B3848249
theorem B2397689 : Blo 1064615 2397689 := bstep (se 2 (by rfl) ⟨899133, by rfl⟩ : syracuseStep 2397689 = 1798267) B1798267
theorem B2397779 : Blo 1064615 2397779 := bstep (se 1 (by rfl) ⟨1798334, by rfl⟩ : syracuseStep 2397779 = 3596669) B3596669
theorem B1349227 : Blo 1064615 1349227 := bstep (se 1 (by rfl) ⟨1011920, by rfl⟩ : syracuseStep 1349227 = 2023841) B2023841
theorem B4331195 : Blo 1064615 4331195 := bstep (se 1 (by rfl) ⟨3248396, by rfl⟩ : syracuseStep 4331195 = 6496793) B6496793
theorem B2397959 : Blo 1064615 2397959 := bstep (se 1 (by rfl) ⟨1798469, by rfl⟩ : syracuseStep 2397959 = 3596939) B3596939
theorem B1349455 : Blo 1064615 1349455 := bstep (se 1 (by rfl) ⟨1012091, by rfl⟩ : syracuseStep 1349455 = 2024183) B2024183
theorem B2398571 : Blo 1064615 2398571 := bstep (se 1 (by rfl) ⟨1798928, by rfl⟩ : syracuseStep 2398571 = 3597857) B3597857
theorem B2398715 : Blo 1064615 2398715 := bstep (se 1 (by rfl) ⟨1799036, by rfl⟩ : syracuseStep 2398715 = 3598073) B3598073
theorem B1645127 : Blo 1064615 1645127 := bstep (se 1 (by rfl) ⟨1233845, by rfl⟩ : syracuseStep 1645127 = 2467691) B2467691
theorem B2398841 : Blo 1064615 2398841 := bstep (se 2 (by rfl) ⟨899565, by rfl⟩ : syracuseStep 2398841 = 1799131) B1799131
theorem B2398895 : Blo 1064615 2398895 := bstep (se 1 (by rfl) ⟨1799171, by rfl⟩ : syracuseStep 2398895 = 3598343) B3598343
theorem B5118659 : Blo 1064615 5118659 := bstep (se 1 (by rfl) ⟨3838994, by rfl⟩ : syracuseStep 5118659 = 7677989) B7677989
theorem B2398967 : Blo 1064615 2398967 := bstep (se 1 (by rfl) ⟨1799225, by rfl⟩ : syracuseStep 2398967 = 3598451) B3598451
theorem B2399147 : Blo 1064615 2399147 := bstep (se 1 (by rfl) ⟨1799360, by rfl⟩ : syracuseStep 2399147 = 3598721) B3598721
theorem B2595827 : Blo 1064615 2595827 := bstep (se 1 (by rfl) ⟨1946870, by rfl⟩ : syracuseStep 2595827 = 3893741) B3893741
theorem B2563271 : Blo 1064615 2563271 := bstep (se 1 (by rfl) ⟨1922453, by rfl⟩ : syracuseStep 2563271 = 3844907) B3844907
theorem B15375581 : Blo 1064615 15375581 := bstep (se 3 (by rfl) ⟨2882921, by rfl⟩ : syracuseStep 15375581 = 5765843) B5765843
theorem B2399687 : Blo 1064615 2399687 := bstep (se 1 (by rfl) ⟨1799765, by rfl⟩ : syracuseStep 2399687 = 3599531) B3599531
theorem B25927127 : Blo 1064615 25927127 := bstep (se 1 (by rfl) ⟨19445345, by rfl⟩ : syracuseStep 25927127 = 38890691) B38890691
theorem B4562527 : Blo 1064615 4562527 := bstep (se 1 (by rfl) ⟨3421895, by rfl⟩ : syracuseStep 4562527 = 6843791) B6843791
theorem B1351343 : Blo 1064615 1351343 := bstep (se 1 (by rfl) ⟨1013507, by rfl⟩ : syracuseStep 1351343 = 2027015) B2027015
theorem B2400047 : Blo 1064615 2400047 := bstep (se 1 (by rfl) ⟨1800035, by rfl⟩ : syracuseStep 2400047 = 3600071) B3600071
theorem B6496307 : Blo 1064615 6496307 := bstep (se 1 (by rfl) ⟨4872230, by rfl⟩ : syracuseStep 6496307 = 9744461) B9744461
theorem B2400623 : Blo 1064615 2400623 := bstep (se 1 (by rfl) ⟨1800467, by rfl⟩ : syracuseStep 2400623 = 3600935) B3600935
theorem B1352047 : Blo 1064615 1352047 := bstep (se 1 (by rfl) ⟨1014035, by rfl⟩ : syracuseStep 1352047 = 2028071) B2028071
theorem B2400695 : Blo 1064615 2400695 := bstep (se 1 (by rfl) ⟨1800521, by rfl⟩ : syracuseStep 2400695 = 3601043) B3601043
theorem B2695751 : Blo 1064615 2695751 := bstep (se 1 (by rfl) ⟨2021813, by rfl⟩ : syracuseStep 2695751 = 4043627) B4043627
theorem B6824519 : Blo 1064615 6824519 := bstep (se 1 (by rfl) ⟨5118389, by rfl⟩ : syracuseStep 6824519 = 10236779) B10236779
theorem B2400839 : Blo 1064615 2400839 := bstep (se 1 (by rfl) ⟨1800629, by rfl⟩ : syracuseStep 2400839 = 3601259) B3601259
theorem B2400875 : Blo 1064615 2400875 := bstep (se 1 (by rfl) ⟨1800656, by rfl⟩ : syracuseStep 2400875 = 3601313) B3601313
theorem B2695801 : Blo 1064615 2695801 := bstep (se 2 (by rfl) ⟨1010925, by rfl⟩ : syracuseStep 2695801 = 2021851) B2021851
theorem B2401271 : Blo 1064615 2401271 := bstep (se 1 (by rfl) ⟨1800953, by rfl⟩ : syracuseStep 2401271 = 3601907) B3601907
theorem B4564201 : Blo 1064615 4564201 := bstep (se 2 (by rfl) ⟨1711575, by rfl⟩ : syracuseStep 4564201 = 3423151) B3423151
theorem B2401631 : Blo 1064615 2401631 := bstep (se 1 (by rfl) ⟨1801223, by rfl⟩ : syracuseStep 2401631 = 3602447) B3602447
theorem B2434465 : Blo 1064615 2434465 := bstep (se 2 (by rfl) ⟨912924, by rfl⟩ : syracuseStep 2434465 = 1825849) B1825849
theorem B5776829 : Blo 1064615 5776829 := bstep (se 3 (by rfl) ⟨1083155, by rfl⟩ : syracuseStep 5776829 = 2166311) B2166311
theorem B2434655 : Blo 1064615 2434655 := bstep (se 1 (by rfl) ⟨1825991, by rfl⟩ : syracuseStep 2434655 = 3651983) B3651983
theorem B56272583 : Blo 1064615 56272583 := bstep (se 1 (by rfl) ⟨42204437, by rfl⟩ : syracuseStep 56272583 = 84408875) B84408875
theorem B2402027 : Blo 1064615 2402027 := bstep (se 1 (by rfl) ⟨1801520, by rfl⟩ : syracuseStep 2402027 = 3603041) B3603041
theorem B2402153 : Blo 1064615 2402153 := bstep (se 2 (by rfl) ⟨900807, by rfl⟩ : syracuseStep 2402153 = 1801615) B1801615
theorem B2697563 : Blo 1064615 2697563 := bstep (se 1 (by rfl) ⟨2023172, by rfl⟩ : syracuseStep 2697563 = 4046345) B4046345
theorem B2697583 : Blo 1064615 2697583 := bstep (se 1 (by rfl) ⟨2023187, by rfl⟩ : syracuseStep 2697583 = 4046375) B4046375
theorem B10267145 : Blo 1064615 10267145 := bstep (se 2 (by rfl) ⟨3850179, by rfl⟩ : syracuseStep 10267145 = 7700359) B7700359
theorem B8104535 : Blo 1064615 8104535 := bstep (se 1 (by rfl) ⟨6078401, by rfl⟩ : syracuseStep 8104535 = 12156803) B12156803
theorem B6826619 : Blo 1064615 6826619 := bstep (se 1 (by rfl) ⟨5119964, by rfl⟩ : syracuseStep 6826619 = 10239929) B10239929
theorem B2402999 : Blo 1064615 2402999 := bstep (se 1 (by rfl) ⟨1802249, by rfl⟩ : syracuseStep 2402999 = 3604499) B3604499
theorem B2566903 : Blo 1064615 2566903 := bstep (se 1 (by rfl) ⟨1925177, by rfl⟩ : syracuseStep 2566903 = 3850355) B3850355
theorem B2403215 : Blo 1064615 2403215 := bstep (se 1 (by rfl) ⟨1802411, by rfl⟩ : syracuseStep 2403215 = 3604823) B3604823
theorem B2698231 : Blo 1064615 2698231 := bstep (se 1 (by rfl) ⟨2023673, by rfl⟩ : syracuseStep 2698231 = 4047347) B4047347
theorem B9120883 : Blo 1064615 9120883 := bstep (se 1 (by rfl) ⟨6840662, by rfl⟩ : syracuseStep 9120883 = 13681325) B13681325
theorem B2698535 : Blo 1064615 2698535 := bstep (se 1 (by rfl) ⟨2023901, by rfl⟩ : syracuseStep 2698535 = 4047803) B4047803
theorem B2403935 : Blo 1064615 2403935 := bstep (se 1 (by rfl) ⟨1802951, by rfl⟩ : syracuseStep 2403935 = 3605903) B3605903
theorem B15380077 : Blo 1064615 15380077 := bstep (se 3 (by rfl) ⟨2883764, by rfl⟩ : syracuseStep 15380077 = 5767529) B5767529
theorem B1519339 : Blo 1064615 1519339 := bstep (se 1 (by rfl) ⟨1139504, by rfl⟩ : syracuseStep 1519339 = 2279009) B2279009
theorem B2404151 : Blo 1064615 2404151 := bstep (se 1 (by rfl) ⟨1803113, by rfl⟩ : syracuseStep 2404151 = 3606227) B3606227
theorem B2700175 : Blo 1064615 2700175 := bstep (se 1 (by rfl) ⟨2025131, by rfl⟩ : syracuseStep 2700175 = 4050263) B4050263
theorem B10269605 : Blo 1064615 10269605 := bstep (se 4 (by rfl) ⟨962775, by rfl⟩ : syracuseStep 10269605 = 1925551) B1925551
theorem B8205257 : Blo 1064615 8205257 := bstep (se 2 (by rfl) ⟨3076971, by rfl⟩ : syracuseStep 8205257 = 6153943) B6153943
theorem B6829181 : Blo 1064615 6829181 := bstep (se 3 (by rfl) ⟨1280471, by rfl⟩ : syracuseStep 6829181 = 2560943) B2560943
theorem B21083261 : Blo 1064615 21083261 := bstep (se 3 (by rfl) ⟨3953111, by rfl⟩ : syracuseStep 21083261 = 7906223) B7906223
theorem B2372903 : Blo 1064615 2372903 := bstep (se 1 (by rfl) ⟨1779677, by rfl⟩ : syracuseStep 2372903 = 3559355) B3559355
theorem B5125463 : Blo 1064615 5125463 := bstep (se 1 (by rfl) ⟨3844097, by rfl⟩ : syracuseStep 5125463 = 7688195) B7688195
theorem B4044127 : Blo 1064615 4044127 := bstep (se 1 (by rfl) ⟨3033095, by rfl⟩ : syracuseStep 4044127 = 6066191) B6066191
theorem B2700641 : Blo 1064615 2700641 := bstep (se 2 (by rfl) ⟨1012740, by rfl⟩ : syracuseStep 2700641 = 2025481) B2025481
theorem B2078303 : Blo 1064615 2078303 := bstep (se 1 (by rfl) ⟨1558727, by rfl⟩ : syracuseStep 2078303 = 3117455) B3117455
theorem B2701097 : Blo 1064615 2701097 := bstep (se 2 (by rfl) ⟨1012911, by rfl⟩ : syracuseStep 2701097 = 2025823) B2025823
theorem B4044599 : Blo 1064615 4044599 := bstep (se 1 (by rfl) ⟨3033449, by rfl⟩ : syracuseStep 4044599 = 6066899) B6066899
theorem B7288805 : Blo 1064615 7288805 := bstep (se 4 (by rfl) ⟨683325, by rfl⟩ : syracuseStep 7288805 = 1366651) B1366651
theorem B4045085 : Blo 1064615 4045085 := bstep (se 3 (by rfl) ⟨758453, by rfl⟩ : syracuseStep 4045085 = 1516907) B1516907
theorem B2702099 : Blo 1064615 2702099 := bstep (se 1 (by rfl) ⟨2026574, by rfl⟩ : syracuseStep 2702099 = 4053149) B4053149
theorem B2702555 : Blo 1064615 2702555 := bstep (se 1 (by rfl) ⟨2026916, by rfl⟩ : syracuseStep 2702555 = 4053833) B4053833
theorem B2702585 : Blo 1064615 2702585 := bstep (se 2 (by rfl) ⟨1013469, by rfl⟩ : syracuseStep 2702585 = 2026939) B2026939
theorem B9125257 : Blo 1064615 9125257 := bstep (se 2 (by rfl) ⟨3421971, by rfl⟩ : syracuseStep 9125257 = 6843943) B6843943
theorem B27704825 : Blo 1064615 27704825 := bstep (se 2 (by rfl) ⟨10389309, by rfl⟩ : syracuseStep 27704825 = 20778619) B20778619
theorem B6831641 : Blo 1064615 6831641 := bstep (se 2 (by rfl) ⟨2561865, by rfl⟩ : syracuseStep 6831641 = 5123731) B5123731
theorem B1064671 : Blo 1064615 1064671 := bstep (se 1 (by rfl) ⟨798503, by rfl⟩ : syracuseStep 1064671 = 1597007) B1597007
theorem B4865771 : Blo 1064615 4865771 := bstep (se 1 (by rfl) ⟨3649328, by rfl⟩ : syracuseStep 4865771 = 7298657) B7298657
theorem B1064751 : Blo 1064615 1064751 := bstep (se 1 (by rfl) ⟨798563, by rfl⟩ : syracuseStep 1064751 = 1597127) B1597127
theorem B2703233 : Blo 1064615 2703233 := bstep (se 2 (by rfl) ⟨1013712, by rfl⟩ : syracuseStep 2703233 = 2027425) B2027425
theorem B1064859 : Blo 1064615 1064859 := bstep (se 1 (by rfl) ⟨798644, by rfl⟩ : syracuseStep 1064859 = 1597289) B1597289
theorem B1064911 : Blo 1064615 1064911 := bstep (se 1 (by rfl) ⟨798683, by rfl⟩ : syracuseStep 1064911 = 1597367) B1597367
theorem B1064935 : Blo 1064615 1064935 := bstep (se 1 (by rfl) ⟨798701, by rfl⟩ : syracuseStep 1064935 = 1597403) B1597403
theorem B5390387 : Blo 1064615 5390387 := bstep (se 1 (by rfl) ⟨4042790, by rfl⟩ : syracuseStep 5390387 = 8085581) B8085581
theorem B1065247 : Blo 1064615 1065247 := bstep (se 1 (by rfl) ⟨798935, by rfl⟩ : syracuseStep 1065247 = 1597871) B1597871
theorem B10961203 : Blo 1064615 10961203 := bstep (se 1 (by rfl) ⟨8220902, by rfl⟩ : syracuseStep 10961203 = 16441805) B16441805
theorem B2703689 : Blo 1064615 2703689 := bstep (se 2 (by rfl) ⟨1013883, by rfl⟩ : syracuseStep 2703689 = 2027767) B2027767
theorem B1065307 : Blo 1064615 1065307 := bstep (se 1 (by rfl) ⟨798980, by rfl⟩ : syracuseStep 1065307 = 1597961) B1597961
theorem B1065327 : Blo 1064615 1065327 := bstep (se 1 (by rfl) ⟨798995, by rfl⟩ : syracuseStep 1065327 = 1597991) B1597991
theorem B1065383 : Blo 1064615 1065383 := bstep (se 1 (by rfl) ⟨799037, by rfl⟩ : syracuseStep 1065383 = 1598075) B1598075
theorem B1065467 : Blo 1064615 1065467 := bstep (se 1 (by rfl) ⟨799100, by rfl⟩ : syracuseStep 1065467 = 1598201) B1598201
theorem B1065535 : Blo 1064615 1065535 := bstep (se 1 (by rfl) ⟨799151, by rfl⟩ : syracuseStep 1065535 = 1598303) B1598303
theorem B1065543 : Blo 1064615 1065543 := bstep (se 1 (by rfl) ⟨799157, by rfl⟩ : syracuseStep 1065543 = 1598315) B1598315
theorem B2704043 : Blo 1064615 2704043 := bstep (se 1 (by rfl) ⟨2028032, by rfl⟩ : syracuseStep 2704043 = 4056065) B4056065
theorem B3031775 : Blo 1064615 3031775 := bstep (se 1 (by rfl) ⟨2273831, by rfl⟩ : syracuseStep 3031775 = 4547663) B4547663
theorem B1065695 : Blo 1064615 1065695 := bstep (se 1 (by rfl) ⟨799271, by rfl⟩ : syracuseStep 1065695 = 1598543) B1598543
theorem B1065775 : Blo 1064615 1065775 := bstep (se 1 (by rfl) ⟨799331, by rfl⟩ : syracuseStep 1065775 = 1598663) B1598663
theorem B1065883 : Blo 1064615 1065883 := bstep (se 1 (by rfl) ⟨799412, by rfl⟩ : syracuseStep 1065883 = 1598825) B1598825
theorem B5129153 : Blo 1064615 5129153 := bstep (se 2 (by rfl) ⟨1923432, by rfl⟩ : syracuseStep 5129153 = 3846865) B3846865
theorem B1065935 : Blo 1064615 1065935 := bstep (se 1 (by rfl) ⟨799451, by rfl⟩ : syracuseStep 1065935 = 1598903) B1598903
theorem B1065959 : Blo 1064615 1065959 := bstep (se 1 (by rfl) ⟨799469, by rfl⟩ : syracuseStep 1065959 = 1598939) B1598939
theorem B6079495 : Blo 1064615 6079495 := bstep (se 1 (by rfl) ⟨4559621, by rfl⟩ : syracuseStep 6079495 = 9119243) B9119243
theorem B4048015 : Blo 1064615 4048015 := bstep (se 1 (by rfl) ⟨3036011, by rfl⟩ : syracuseStep 4048015 = 6072023) B6072023
theorem B2278649 : Blo 1064615 2278649 := bstep (se 2 (by rfl) ⟨854493, by rfl⟩ : syracuseStep 2278649 = 1708987) B1708987
theorem B1066271 : Blo 1064615 1066271 := bstep (se 1 (by rfl) ⟨799703, by rfl⟩ : syracuseStep 1066271 = 1599407) B1599407
theorem B1066331 : Blo 1064615 1066331 := bstep (se 1 (by rfl) ⟨799748, by rfl⟩ : syracuseStep 1066331 = 1599497) B1599497
theorem B1066351 : Blo 1064615 1066351 := bstep (se 1 (by rfl) ⟨799763, by rfl⟩ : syracuseStep 1066351 = 1599527) B1599527
theorem B4048289 : Blo 1064615 4048289 := bstep (se 2 (by rfl) ⟨1518108, by rfl⟩ : syracuseStep 4048289 = 3036217) B3036217
theorem B1066407 : Blo 1064615 1066407 := bstep (se 1 (by rfl) ⟨799805, by rfl⟩ : syracuseStep 1066407 = 1599611) B1599611
theorem B1066491 : Blo 1064615 1066491 := bstep (se 1 (by rfl) ⟨799868, by rfl⟩ : syracuseStep 1066491 = 1599737) B1599737
theorem B1066559 : Blo 1064615 1066559 := bstep (se 1 (by rfl) ⟨799919, by rfl⟩ : syracuseStep 1066559 = 1599839) B1599839
theorem B1066567 : Blo 1064615 1066567 := bstep (se 1 (by rfl) ⟨799925, by rfl⟩ : syracuseStep 1066567 = 1599851) B1599851
theorem B5392007 : Blo 1064615 5392007 := bstep (se 1 (by rfl) ⟨4044005, by rfl⟩ : syracuseStep 5392007 = 8088011) B8088011
theorem B1066719 : Blo 1064615 1066719 := bstep (se 1 (by rfl) ⟨800039, by rfl⟩ : syracuseStep 1066719 = 1600079) B1600079
theorem B1066799 : Blo 1064615 1066799 := bstep (se 1 (by rfl) ⟨800099, by rfl⟩ : syracuseStep 1066799 = 1600199) B1600199
theorem B10241927 : Blo 1064615 10241927 := bstep (se 1 (by rfl) ⟨7681445, by rfl⟩ : syracuseStep 10241927 = 15362891) B15362891
theorem B1066907 : Blo 1064615 1066907 := bstep (se 1 (by rfl) ⟨800180, by rfl⟩ : syracuseStep 1066907 = 1600361) B1600361
theorem B1066959 : Blo 1064615 1066959 := bstep (se 1 (by rfl) ⟨800219, by rfl⟩ : syracuseStep 1066959 = 1600439) B1600439
theorem B1066983 : Blo 1064615 1066983 := bstep (se 1 (by rfl) ⟨800237, by rfl⟩ : syracuseStep 1066983 = 1600475) B1600475
theorem B38979569 : Blo 1064615 38979569 := bstep (se 2 (by rfl) ⟨14617338, by rfl⟩ : syracuseStep 38979569 = 29234677) B29234677
theorem B8636669 : Blo 1064615 8636669 := bstep (se 3 (by rfl) ⟨1619375, by rfl⟩ : syracuseStep 8636669 = 3238751) B3238751
theorem B1067295 : Blo 1064615 1067295 := bstep (se 1 (by rfl) ⟨800471, by rfl⟩ : syracuseStep 1067295 = 1600943) B1600943
theorem B1067355 : Blo 1064615 1067355 := bstep (se 1 (by rfl) ⟨800516, by rfl⟩ : syracuseStep 1067355 = 1601033) B1601033
theorem B1067375 : Blo 1064615 1067375 := bstep (se 1 (by rfl) ⟨800531, by rfl⟩ : syracuseStep 1067375 = 1601063) B1601063
theorem B1067431 : Blo 1064615 1067431 := bstep (se 1 (by rfl) ⟨800573, by rfl⟩ : syracuseStep 1067431 = 1601147) B1601147
theorem B9095597 : Blo 1064615 9095597 := bstep (se 3 (by rfl) ⟨1705424, by rfl⟩ : syracuseStep 9095597 = 3410849) B3410849
theorem B1067515 : Blo 1064615 1067515 := bstep (se 1 (by rfl) ⟨800636, by rfl⟩ : syracuseStep 1067515 = 1601273) B1601273
theorem B1067583 : Blo 1064615 1067583 := bstep (se 1 (by rfl) ⟨800687, by rfl⟩ : syracuseStep 1067583 = 1601375) B1601375
theorem B1067591 : Blo 1064615 1067591 := bstep (se 1 (by rfl) ⟨800693, by rfl⟩ : syracuseStep 1067591 = 1601387) B1601387
theorem B1198687 : Blo 1064615 1198687 := bstep (se 1 (by rfl) ⟨899015, by rfl⟩ : syracuseStep 1198687 = 1798031) B1798031
theorem B1067743 : Blo 1064615 1067743 := bstep (se 1 (by rfl) ⟨800807, by rfl⟩ : syracuseStep 1067743 = 1601615) B1601615
theorem B1067823 : Blo 1064615 1067823 := bstep (se 1 (by rfl) ⟨800867, by rfl⟩ : syracuseStep 1067823 = 1601735) B1601735
theorem B1067931 : Blo 1064615 1067931 := bstep (se 1 (by rfl) ⟨800948, by rfl⟩ : syracuseStep 1067931 = 1601897) B1601897
theorem B1067983 : Blo 1064615 1067983 := bstep (se 1 (by rfl) ⟨800987, by rfl⟩ : syracuseStep 1067983 = 1601975) B1601975
theorem B1068007 : Blo 1064615 1068007 := bstep (se 1 (by rfl) ⟨801005, by rfl⟩ : syracuseStep 1068007 = 1602011) B1602011
theorem B4049959 : Blo 1064615 4049959 := bstep (se 1 (by rfl) ⟨3037469, by rfl⟩ : syracuseStep 4049959 = 6074939) B6074939
theorem B2280487 : Blo 1064615 2280487 := bstep (se 1 (by rfl) ⟨1710365, by rfl⟩ : syracuseStep 2280487 = 3420731) B3420731
theorem B12143681 : Blo 1064615 12143681 := bstep (se 2 (by rfl) ⟨4553880, by rfl⟩ : syracuseStep 12143681 = 9107761) B9107761
theorem B3034235 : Blo 1064615 3034235 := bstep (se 1 (by rfl) ⟨2275676, by rfl⟩ : syracuseStep 3034235 = 4551353) B4551353
theorem B5393627 : Blo 1064615 5393627 := bstep (se 1 (by rfl) ⟨4045220, by rfl⟩ : syracuseStep 5393627 = 8090441) B8090441
theorem B1068319 : Blo 1064615 1068319 := bstep (se 1 (by rfl) ⟨801239, by rfl⟩ : syracuseStep 1068319 = 1602479) B1602479
theorem B1068379 : Blo 1064615 1068379 := bstep (se 1 (by rfl) ⟨801284, by rfl⟩ : syracuseStep 1068379 = 1602569) B1602569
theorem B1068399 : Blo 1064615 1068399 := bstep (se 1 (by rfl) ⟨801299, by rfl⟩ : syracuseStep 1068399 = 1602599) B1602599
theorem B6081911 : Blo 1064615 6081911 := bstep (se 1 (by rfl) ⟨4561433, by rfl⟩ : syracuseStep 6081911 = 9122867) B9122867
theorem B1068455 : Blo 1064615 1068455 := bstep (se 1 (by rfl) ⟨801341, by rfl⟩ : syracuseStep 1068455 = 1602683) B1602683
theorem B1068539 : Blo 1064615 1068539 := bstep (se 1 (by rfl) ⟨801404, by rfl⟩ : syracuseStep 1068539 = 1602809) B1602809
theorem B1068607 : Blo 1064615 1068607 := bstep (se 1 (by rfl) ⟨801455, by rfl⟩ : syracuseStep 1068607 = 1602911) B1602911
theorem B1068615 : Blo 1064615 1068615 := bstep (se 1 (by rfl) ⟨801461, by rfl⟩ : syracuseStep 1068615 = 1602923) B1602923
theorem B7294637 : Blo 1064615 7294637 := bstep (se 3 (by rfl) ⟨1367744, by rfl⟩ : syracuseStep 7294637 = 2735489) B2735489
theorem B1199839 : Blo 1064615 1199839 := bstep (se 1 (by rfl) ⟨899879, by rfl⟩ : syracuseStep 1199839 = 1799759) B1799759
theorem B5132035 : Blo 1064615 5132035 := bstep (se 1 (by rfl) ⟨3849026, by rfl⟩ : syracuseStep 5132035 = 7698053) B7698053
theorem B4869895 : Blo 1064615 4869895 := bstep (se 1 (by rfl) ⟨3652421, by rfl⟩ : syracuseStep 4869895 = 7304843) B7304843
theorem B4050749 : Blo 1064615 4050749 := bstep (se 3 (by rfl) ⟨759515, by rfl⟩ : syracuseStep 4050749 = 1519031) B1519031
theorem B3035009 : Blo 1064615 3035009 := bstep (se 2 (by rfl) ⟨1138128, by rfl⟩ : syracuseStep 3035009 = 2276257) B2276257
theorem B10375121 : Blo 1064615 10375121 := bstep (se 2 (by rfl) ⟨3890670, by rfl⟩ : syracuseStep 10375121 = 7781341) B7781341
theorem B9097373 : Blo 1064615 9097373 := bstep (se 3 (by rfl) ⟨1705757, by rfl⟩ : syracuseStep 9097373 = 3411515) B3411515
theorem B5132497 : Blo 1064615 5132497 := bstep (se 2 (by rfl) ⟨1924686, by rfl⟩ : syracuseStep 5132497 = 3849373) B3849373
theorem B1200415 : Blo 1064615 1200415 := bstep (se 1 (by rfl) ⟨900311, by rfl⟩ : syracuseStep 1200415 = 1800623) B1800623
theorem B5394761 : Blo 1064615 5394761 := bstep (se 2 (by rfl) ⟨2023035, by rfl⟩ : syracuseStep 5394761 = 4046071) B4046071
theorem B3035465 : Blo 1064615 3035465 := bstep (se 2 (by rfl) ⟨1138299, by rfl⟩ : syracuseStep 3035465 = 2276599) B2276599
theorem B23024189 : Blo 1064615 23024189 := bstep (se 3 (by rfl) ⟨4317035, by rfl⟩ : syracuseStep 23024189 = 8634071) B8634071
theorem B1200703 : Blo 1064615 1200703 := bstep (se 1 (by rfl) ⟨900527, by rfl⟩ : syracuseStep 1200703 = 1801055) B1801055
theorem B1462855 : Blo 1064615 1462855 := bstep (se 1 (by rfl) ⟨1097141, by rfl⟩ : syracuseStep 1462855 = 2194283) B2194283
theorem B3035819 : Blo 1064615 3035819 := bstep (se 1 (by rfl) ⟨2276864, by rfl⟩ : syracuseStep 3035819 = 4553729) B4553729
theorem B12506359 : Blo 1064615 12506359 := bstep (se 1 (by rfl) ⟨9379769, by rfl⟩ : syracuseStep 12506359 = 18759539) B18759539
theorem B1201531 : Blo 1064615 1201531 := bstep (se 1 (by rfl) ⟨901148, by rfl⟩ : syracuseStep 1201531 = 1802297) B1802297
theorem B5133881 : Blo 1064615 5133881 := bstep (se 2 (by rfl) ⟨1925205, by rfl⟩ : syracuseStep 5133881 = 3850411) B3850411
theorem B5396057 : Blo 1064615 5396057 := bstep (se 2 (by rfl) ⟨2023521, by rfl⟩ : syracuseStep 5396057 = 4047043) B4047043
theorem B3593915 : Blo 1064615 3593915 := bstep (se 1 (by rfl) ⟨2695436, by rfl⟩ : syracuseStep 3593915 = 5390873) B5390873
theorem B1201999 : Blo 1064615 1201999 := bstep (se 1 (by rfl) ⟨901499, by rfl⟩ : syracuseStep 1201999 = 1802999) B1802999
theorem B7297067 : Blo 1064615 7297067 := bstep (se 1 (by rfl) ⟨5472800, by rfl⟩ : syracuseStep 7297067 = 10945601) B10945601
theorem B3037607 : Blo 1064615 3037607 := bstep (se 1 (by rfl) ⟨2278205, by rfl⟩ : syracuseStep 3037607 = 4556411) B4556411
theorem B1137223 : Blo 1064615 1137223 := bstep (se 1 (by rfl) ⟨852917, by rfl⟩ : syracuseStep 1137223 = 1705835) B1705835
theorem B9099971 : Blo 1064615 9099971 := bstep (se 1 (by rfl) ⟨6824978, by rfl⟩ : syracuseStep 9099971 = 13649957) B13649957
theorem B1203023 : Blo 1064615 1203023 := bstep (se 1 (by rfl) ⟨902267, by rfl⟩ : syracuseStep 1203023 = 1804535) B1804535
theorem B1923995 : Blo 1064615 1923995 := bstep (se 1 (by rfl) ⟨1442996, by rfl⟩ : syracuseStep 1923995 = 2885993) B2885993
theorem B6085853 : Blo 1064615 6085853 := bstep (se 3 (by rfl) ⟨1141097, by rfl⟩ : syracuseStep 6085853 = 2282195) B2282195
theorem B3595859 : Blo 1064615 3595859 := bstep (se 1 (by rfl) ⟨2696894, by rfl⟩ : syracuseStep 3595859 = 5393789) B5393789
theorem B4054637 : Blo 1064615 4054637 := bstep (se 3 (by rfl) ⟨760244, by rfl⟩ : syracuseStep 4054637 = 1520489) B1520489
theorem B1597163 : Blo 1064615 1597163 := bstep (se 1 (by rfl) ⟨1197872, by rfl⟩ : syracuseStep 1597163 = 2395745) B2395745
theorem B7790339 : Blo 1064615 7790339 := bstep (se 1 (by rfl) ⟨5842754, by rfl⟩ : syracuseStep 7790339 = 11685509) B11685509
theorem B1826567 : Blo 1064615 1826567 := bstep (se 1 (by rfl) ⟨1369925, by rfl⟩ : syracuseStep 1826567 = 2739851) B2739851
theorem B3039133 : Blo 1064615 3039133 := bstep (se 3 (by rfl) ⟨569837, by rfl⟩ : syracuseStep 3039133 = 1139675) B1139675
theorem B1597391 : Blo 1064615 1597391 := bstep (se 1 (by rfl) ⟨1198043, by rfl⟩ : syracuseStep 1597391 = 2396087) B2396087
theorem B1597787 : Blo 1064615 1597787 := bstep (se 1 (by rfl) ⟨1198340, by rfl⟩ : syracuseStep 1597787 = 2396681) B2396681
theorem B1598015 : Blo 1064615 1598015 := bstep (se 1 (by rfl) ⟨1198511, by rfl⟩ : syracuseStep 1598015 = 2397023) B2397023
theorem B13656721 : Blo 1064615 13656721 := bstep (se 2 (by rfl) ⟨5121270, by rfl⟩ : syracuseStep 13656721 = 10242541) B10242541
theorem B43803287 : Blo 1064615 43803287 := bstep (se 1 (by rfl) ⟨32852465, by rfl⟩ : syracuseStep 43803287 = 65704931) B65704931
theorem B1598135 : Blo 1064615 1598135 := bstep (se 1 (by rfl) ⟨1198601, by rfl⟩ : syracuseStep 1598135 = 2397203) B2397203
theorem B1598363 : Blo 1064615 1598363 := bstep (se 1 (by rfl) ⟨1198772, by rfl⟩ : syracuseStep 1598363 = 2397545) B2397545
theorem B6841381 : Blo 1064615 6841381 := bstep (se 4 (by rfl) ⟨641379, by rfl⟩ : syracuseStep 6841381 = 1282759) B1282759
theorem B4056263 : Blo 1064615 4056263 := bstep (se 1 (by rfl) ⟨3042197, by rfl⟩ : syracuseStep 4056263 = 6084395) B6084395
theorem B1598759 : Blo 1064615 1598759 := bstep (se 1 (by rfl) ⟨1199069, by rfl⟩ : syracuseStep 1598759 = 2398139) B2398139
theorem B1598843 : Blo 1064615 1598843 := bstep (se 1 (by rfl) ⟨1199132, by rfl⟩ : syracuseStep 1598843 = 2398265) B2398265
theorem B1598969 : Blo 1064615 1598969 := bstep (se 2 (by rfl) ⟨599613, by rfl⟩ : syracuseStep 1598969 = 1199227) B1199227
theorem B1599071 : Blo 1064615 1599071 := bstep (se 1 (by rfl) ⟨1199303, by rfl⟩ : syracuseStep 1599071 = 2398607) B2398607
theorem B19457671 : Blo 1064615 19457671 := bstep (se 1 (by rfl) ⟨14593253, by rfl⟩ : syracuseStep 19457671 = 29186507) B29186507
theorem B14575261 : Blo 1064615 14575261 := bstep (se 3 (by rfl) ⟨2732861, by rfl⟩ : syracuseStep 14575261 = 5465723) B5465723
theorem B4056763 : Blo 1064615 4056763 := bstep (se 1 (by rfl) ⟨3042572, by rfl⟩ : syracuseStep 4056763 = 6085145) B6085145
theorem B1599287 : Blo 1064615 1599287 := bstep (se 1 (by rfl) ⟨1199465, by rfl⟩ : syracuseStep 1599287 = 2398931) B2398931
theorem B23685209 : Blo 1064615 23685209 := bstep (se 2 (by rfl) ⟨8881953, by rfl⟩ : syracuseStep 23685209 = 17763907) B17763907
theorem B1599593 : Blo 1064615 1599593 := bstep (se 2 (by rfl) ⟨599847, by rfl⟩ : syracuseStep 1599593 = 1199695) B1199695
theorem B15395183 : Blo 1064615 15395183 := bstep (se 1 (by rfl) ⟨11546387, by rfl⟩ : syracuseStep 15395183 = 23092775) B23092775
theorem B16411009 : Blo 1064615 16411009 := bstep (se 2 (by rfl) ⟨6154128, by rfl⟩ : syracuseStep 16411009 = 12308257) B12308257
theorem B1599911 : Blo 1064615 1599911 := bstep (se 1 (by rfl) ⟨1199933, by rfl⟩ : syracuseStep 1599911 = 2399867) B2399867
theorem B3598775 : Blo 1064615 3598775 := bstep (se 1 (by rfl) ⟨2699081, by rfl⟩ : syracuseStep 3598775 = 5398163) B5398163
theorem B4680119 : Blo 1064615 4680119 := bstep (se 1 (by rfl) ⟨3510089, by rfl⟩ : syracuseStep 4680119 = 7020179) B7020179
theorem B1599995 : Blo 1064615 1599995 := bstep (se 1 (by rfl) ⟨1199996, by rfl⟩ : syracuseStep 1599995 = 2399993) B2399993
theorem B1796681 : Blo 1064615 1796681 := bstep (se 2 (by rfl) ⟨673755, by rfl⟩ : syracuseStep 1796681 = 1347511) B1347511
theorem B1600121 : Blo 1064615 1600121 := bstep (se 2 (by rfl) ⟨600045, by rfl⟩ : syracuseStep 1600121 = 1200091) B1200091
theorem B1600175 : Blo 1064615 1600175 := bstep (se 1 (by rfl) ⟨1200131, by rfl⟩ : syracuseStep 1600175 = 2400263) B2400263
theorem B1600223 : Blo 1064615 1600223 := bstep (se 1 (by rfl) ⟨1200167, by rfl⟩ : syracuseStep 1600223 = 2400335) B2400335
theorem B2878199 : Blo 1064615 2878199 := bstep (se 1 (by rfl) ⟨2158649, by rfl⟩ : syracuseStep 2878199 = 4317299) B4317299
theorem B31124405 : Blo 1064615 31124405 := bstep (se 5 (by rfl) ⟨1458956, by rfl⟩ : syracuseStep 31124405 = 2917913) B2917913
theorem B1600487 : Blo 1064615 1600487 := bstep (se 1 (by rfl) ⟨1200365, by rfl⟩ : syracuseStep 1600487 = 2400731) B2400731
theorem B1600745 : Blo 1064615 1600745 := bstep (se 2 (by rfl) ⟨600279, by rfl⟩ : syracuseStep 1600745 = 1200559) B1200559
theorem B1600799 : Blo 1064615 1600799 := bstep (se 1 (by rfl) ⟨1200599, by rfl⟩ : syracuseStep 1600799 = 2401199) B2401199
theorem B1600967 : Blo 1064615 1600967 := bstep (se 1 (by rfl) ⟨1200725, by rfl⟩ : syracuseStep 1600967 = 2401451) B2401451
theorem B1797727 : Blo 1064615 1797727 := bstep (se 1 (by rfl) ⟨1348295, by rfl⟩ : syracuseStep 1797727 = 2696591) B2696591
theorem B12152429 : Blo 1064615 12152429 := bstep (se 3 (by rfl) ⟨2278580, by rfl⟩ : syracuseStep 12152429 = 4557161) B4557161
theorem B2027243 : Blo 1064615 2027243 := bstep (se 1 (by rfl) ⟨1520432, by rfl⟩ : syracuseStep 2027243 = 3040865) B3040865
theorem B5402375 : Blo 1064615 5402375 := bstep (se 1 (by rfl) ⟨4051781, by rfl⟩ : syracuseStep 5402375 = 8103563) B8103563
theorem B1601321 : Blo 1064615 1601321 := bstep (se 2 (by rfl) ⟨600495, by rfl⟩ : syracuseStep 1601321 = 1200991) B1200991
theorem B1601327 : Blo 1064615 1601327 := bstep (se 1 (by rfl) ⟨1200995, by rfl⟩ : syracuseStep 1601327 = 2401991) B2401991
theorem B1797943 : Blo 1064615 1797943 := bstep (se 1 (by rfl) ⟨1348457, by rfl⟩ : syracuseStep 1797943 = 2696915) B2696915
theorem B1798409 : Blo 1064615 1798409 := bstep (se 2 (by rfl) ⟨674403, by rfl⟩ : syracuseStep 1798409 = 1348807) B1348807
theorem B1601801 : Blo 1064615 1601801 := bstep (se 2 (by rfl) ⟨600675, by rfl⟩ : syracuseStep 1601801 = 1201351) B1201351
theorem B74805515 : Blo 1064615 74805515 := bstep (se 1 (by rfl) ⟨56104136, by rfl⟩ : syracuseStep 74805515 = 112208273) B112208273
theorem B17985899 : Blo 1064615 17985899 := bstep (se 1 (by rfl) ⟨13489424, by rfl⟩ : syracuseStep 17985899 = 26978849) B26978849
theorem B1601903 : Blo 1064615 1601903 := bstep (se 1 (by rfl) ⟨1201427, by rfl⟩ : syracuseStep 1601903 = 2402855) B2402855
theorem B2027987 : Blo 1064615 2027987 := bstep (se 1 (by rfl) ⟨1520990, by rfl⟩ : syracuseStep 2027987 = 3041981) B3041981
theorem B1602119 : Blo 1064615 1602119 := bstep (se 1 (by rfl) ⟨1201589, by rfl⟩ : syracuseStep 1602119 = 2403179) B2403179
theorem B1602155 : Blo 1064615 1602155 := bstep (se 1 (by rfl) ⟨1201616, by rfl⟩ : syracuseStep 1602155 = 2403233) B2403233
theorem B2028215 : Blo 1064615 2028215 := bstep (se 1 (by rfl) ⟨1521161, by rfl⟩ : syracuseStep 2028215 = 3042323) B3042323
theorem B1602383 : Blo 1064615 1602383 := bstep (se 1 (by rfl) ⟨1201787, by rfl⟩ : syracuseStep 1602383 = 2403575) B2403575
theorem B6845431 : Blo 1064615 6845431 := bstep (se 1 (by rfl) ⟨5134073, by rfl⟩ : syracuseStep 6845431 = 10268147) B10268147
theorem B26277011 : Blo 1064615 26277011 := bstep (se 1 (by rfl) ⟨19707758, by rfl⟩ : syracuseStep 26277011 = 39415517) B39415517
theorem B1602779 : Blo 1064615 1602779 := bstep (se 1 (by rfl) ⟨1202084, by rfl⟩ : syracuseStep 1602779 = 2404169) B2404169
theorem B1799401 : Blo 1064615 1799401 := bstep (se 2 (by rfl) ⟨674775, by rfl⟩ : syracuseStep 1799401 = 1349551) B1349551
theorem B1799455 : Blo 1064615 1799455 := bstep (se 1 (by rfl) ⟨1349591, by rfl⟩ : syracuseStep 1799455 = 2699183) B2699183
theorem B4617577 : Blo 1064615 4617577 := bstep (se 2 (by rfl) ⟨1731591, by rfl⟩ : syracuseStep 4617577 = 3463183) B3463183
theorem B17298821 : Blo 1064615 17298821 := bstep (se 4 (by rfl) ⟨1621764, by rfl⟩ : syracuseStep 17298821 = 3243529) B3243529
theorem B3601853 : Blo 1064615 3601853 := bstep (se 3 (by rfl) ⟨675347, by rfl⟩ : syracuseStep 3601853 = 1350695) B1350695
theorem B2880967 : Blo 1064615 2880967 := bstep (se 1 (by rfl) ⟨2160725, by rfl⟩ : syracuseStep 2880967 = 4321451) B4321451
theorem B1439407 : Blo 1064615 1439407 := bstep (se 1 (by rfl) ⟨1079555, by rfl⟩ : syracuseStep 1439407 = 2159111) B2159111
theorem B1799867 : Blo 1064615 1799867 := bstep (se 1 (by rfl) ⟨1349900, by rfl⟩ : syracuseStep 1799867 = 2699801) B2699801
theorem B18446039 : Blo 1064615 18446039 := bstep (se 1 (by rfl) ⟨13834529, by rfl⟩ : syracuseStep 18446039 = 27669059) B27669059
theorem B11695853 : Blo 1064615 11695853 := bstep (se 3 (by rfl) ⟨2192972, by rfl⟩ : syracuseStep 11695853 = 4385945) B4385945
theorem B3602231 : Blo 1064615 3602231 := bstep (se 1 (by rfl) ⟨2701673, by rfl⟩ : syracuseStep 3602231 = 5403347) B5403347
theorem B3602717 : Blo 1064615 3602717 := bstep (se 3 (by rfl) ⟨675509, by rfl⟩ : syracuseStep 3602717 = 1351019) B1351019
theorem B1440137 : Blo 1064615 1440137 := bstep (se 2 (by rfl) ⟨540051, by rfl⟩ : syracuseStep 1440137 = 1080103) B1080103
theorem B15366581 : Blo 1064615 15366581 := bstep (se 5 (by rfl) ⟨720308, by rfl⟩ : syracuseStep 15366581 = 1440617) B1440617
theorem B5405291 : Blo 1064615 5405291 := bstep (se 1 (by rfl) ⟨4053968, by rfl⟩ : syracuseStep 5405291 = 8107937) B8107937
theorem B5405777 : Blo 1064615 5405777 := bstep (se 2 (by rfl) ⟨2027166, by rfl⟩ : syracuseStep 5405777 = 4054333) B4054333
theorem B2882749 : Blo 1064615 2882749 := bstep (se 3 (by rfl) ⟨540515, by rfl⟩ : syracuseStep 2882749 = 1081031) B1081031
theorem B3603743 : Blo 1064615 3603743 := bstep (se 1 (by rfl) ⟨2702807, by rfl⟩ : syracuseStep 3603743 = 5405615) B5405615
theorem B1801595 : Blo 1064615 1801595 := bstep (se 1 (by rfl) ⟨1351196, by rfl⟩ : syracuseStep 1801595 = 2702393) B2702393
theorem B4324823 : Blo 1064615 4324823 := bstep (se 1 (by rfl) ⟨3243617, by rfl⟩ : syracuseStep 4324823 = 6487235) B6487235
theorem B3898961 : Blo 1064615 3898961 := bstep (se 2 (by rfl) ⟨1462110, by rfl⟩ : syracuseStep 3898961 = 2924221) B2924221
theorem B4390483 : Blo 1064615 4390483 := bstep (se 1 (by rfl) ⟨3292862, by rfl⟩ : syracuseStep 4390483 = 6585725) B6585725
theorem B4619891 : Blo 1064615 4619891 := bstep (se 1 (by rfl) ⟨3464918, by rfl⟩ : syracuseStep 4619891 = 6929837) B6929837
theorem B3080231 : Blo 1064615 3080231 := bstep (se 1 (by rfl) ⟨2310173, by rfl⟩ : syracuseStep 3080231 = 4620347) B4620347
theorem B1802459 : Blo 1064615 1802459 := bstep (se 1 (by rfl) ⟨1351844, by rfl⟩ : syracuseStep 1802459 = 2703689) B2703689
theorem B14614937 : Blo 1064615 14614937 := bstep (se 2 (by rfl) ⟨5480601, by rfl⟩ : syracuseStep 14614937 = 10961203) B10961203
theorem B1802695 : Blo 1064615 1802695 := bstep (se 1 (by rfl) ⟨1352021, by rfl⟩ : syracuseStep 1802695 = 2704043) B2704043
theorem B1802729 : Blo 1064615 1802729 := bstep (se 2 (by rfl) ⟨676023, by rfl⟩ : syracuseStep 1802729 = 1352047) B1352047
theorem B2884349 : Blo 1064615 2884349 := bstep (se 3 (by rfl) ⟨540815, by rfl⟩ : syracuseStep 2884349 = 1081631) B1081631
theorem B12649403 : Blo 1064615 12649403 := bstep (se 1 (by rfl) ⟨9487052, by rfl⟩ : syracuseStep 12649403 = 18974105) B18974105
theorem B25986379 : Blo 1064615 25986379 := bstep (se 1 (by rfl) ⟨19489784, by rfl⟩ : syracuseStep 25986379 = 38979569) B38979569
theorem B6063731 : Blo 1064615 6063731 := bstep (se 1 (by rfl) ⟨4547798, by rfl⟩ : syracuseStep 6063731 = 9095597) B9095597
theorem B1705655 : Blo 1064615 1705655 := bstep (se 1 (by rfl) ⟨1279241, by rfl⟩ : syracuseStep 1705655 = 2558483) B2558483
theorem B2885473 : Blo 1064615 2885473 := bstep (se 2 (by rfl) ⟨1082052, by rfl⟩ : syracuseStep 2885473 = 2164105) B2164105
theorem B3245953 : Blo 1064615 3245953 := bstep (se 2 (by rfl) ⟨1217232, by rfl⟩ : syracuseStep 3245953 = 2434465) B2434465
theorem B8095787 : Blo 1064615 8095787 := bstep (se 1 (by rfl) ⟨6071840, by rfl⟩ : syracuseStep 8095787 = 12143681) B12143681
theorem B19433681 : Blo 1064615 19433681 := bstep (se 2 (by rfl) ⟨7287630, by rfl⟩ : syracuseStep 19433681 = 14575261) B14575261
theorem B5409017 : Blo 1064615 5409017 := bstep (se 2 (by rfl) ⟨2028381, by rfl⟩ : syracuseStep 5409017 = 4056763) B4056763
theorem B18483721 : Blo 1064615 18483721 := bstep (se 2 (by rfl) ⟨6931395, by rfl⟩ : syracuseStep 18483721 = 13862791) B13862791
theorem B6916747 : Blo 1064615 6916747 := bstep (se 1 (by rfl) ⟨5187560, by rfl⟩ : syracuseStep 6916747 = 10375121) B10375121
theorem B6064915 : Blo 1064615 6064915 := bstep (se 1 (by rfl) ⟨4548686, by rfl⟩ : syracuseStep 6064915 = 9097373) B9097373
theorem B6065189 : Blo 1064615 6065189 := bstep (se 4 (by rfl) ⟨568611, by rfl⟩ : syracuseStep 6065189 = 1137223) B1137223
theorem B2395943 : Blo 1064615 2395943 := bstep (se 1 (by rfl) ⟨1796957, by rfl⟩ : syracuseStep 2395943 = 3593915) B3593915
theorem B2887463 : Blo 1064615 2887463 := bstep (se 1 (by rfl) ⟨2165597, by rfl⟩ : syracuseStep 2887463 = 4331195) B4331195
theorem B12161177 : Blo 1064615 12161177 := bstep (se 2 (by rfl) ⟨4560441, by rfl⟩ : syracuseStep 12161177 = 9120883) B9120883
theorem B5542141 : Blo 1064615 5542141 := bstep (se 3 (by rfl) ⟨1039151, by rfl⟩ : syracuseStep 5542141 = 2078303) B2078303
theorem B6492413 : Blo 1064615 6492413 := bstep (se 3 (by rfl) ⟨1217327, by rfl⟩ : syracuseStep 6492413 = 2434655) B2434655
theorem B3412439 : Blo 1064615 3412439 := bstep (se 1 (by rfl) ⟨2559329, by rfl⟩ : syracuseStep 3412439 = 5118659) B5118659
theorem B6066647 : Blo 1064615 6066647 := bstep (se 1 (by rfl) ⟨4549985, by rfl⟩ : syracuseStep 6066647 = 9099971) B9099971
theorem B1282663 : Blo 1064615 1282663 := bstep (se 1 (by rfl) ⟨961997, by rfl⟩ : syracuseStep 1282663 = 1923995) B1923995
theorem B2396969 : Blo 1064615 2396969 := bstep (se 2 (by rfl) ⟨898863, by rfl⟩ : syracuseStep 2396969 = 1797727) B1797727
theorem B1708847 : Blo 1064615 1708847 := bstep (se 1 (by rfl) ⟨1281635, by rfl⟩ : syracuseStep 1708847 = 2563271) B2563271
theorem B6493193 : Blo 1064615 6493193 := bstep (se 2 (by rfl) ⟨2434947, by rfl⟩ : syracuseStep 6493193 = 4869895) B4869895
theorem B2397239 : Blo 1064615 2397239 := bstep (se 1 (by rfl) ⟨1797929, by rfl⟩ : syracuseStep 2397239 = 3595859) B3595859
theorem B2397257 : Blo 1064615 2397257 := bstep (se 2 (by rfl) ⟨898971, by rfl⟩ : syracuseStep 2397257 = 1797943) B1797943
theorem B1217711 : Blo 1064615 1217711 := bstep (se 1 (by rfl) ⟨913283, by rfl⟩ : syracuseStep 1217711 = 1826567) B1826567
theorem B4330871 : Blo 1064615 4330871 := bstep (se 1 (by rfl) ⟨3248153, by rfl⟩ : syracuseStep 4330871 = 6496307) B6496307
theorem B29202191 : Blo 1064615 29202191 := bstep (se 1 (by rfl) ⟨21901643, by rfl⟩ : syracuseStep 29202191 = 43803287) B43803287
theorem B3840365 : Blo 1064615 3840365 := bstep (se 3 (by rfl) ⟨720068, by rfl⟩ : syracuseStep 3840365 = 1440137) B1440137
theorem B10263455 : Blo 1064615 10263455 := bstep (se 1 (by rfl) ⟨7697591, by rfl⟩ : syracuseStep 10263455 = 15395183) B15395183
theorem B2399183 : Blo 1064615 2399183 := bstep (se 1 (by rfl) ⟨1799387, by rfl⟩ : syracuseStep 2399183 = 3598775) B3598775
theorem B3120079 : Blo 1064615 3120079 := bstep (se 1 (by rfl) ⟨2340059, by rfl⟩ : syracuseStep 3120079 = 4680119) B4680119
theorem B2399201 : Blo 1064615 2399201 := bstep (se 2 (by rfl) ⟨899700, by rfl⟩ : syracuseStep 2399201 = 1799401) B1799401
theorem B2399273 : Blo 1064615 2399273 := bstep (se 2 (by rfl) ⟨899727, by rfl⟩ : syracuseStep 2399273 = 1799455) B1799455
theorem B3841289 : Blo 1064615 3841289 := bstep (se 2 (by rfl) ⟨1440483, by rfl⟩ : syracuseStep 3841289 = 2880967) B2880967
theorem B20749603 : Blo 1064615 20749603 := bstep (se 1 (by rfl) ⟨15562202, by rfl⟩ : syracuseStep 20749603 = 31124405) B31124405
theorem B8101619 : Blo 1064615 8101619 := bstep (se 1 (by rfl) ⟨6076214, by rfl⟩ : syracuseStep 8101619 = 12152429) B12152429
theorem B1351495 : Blo 1064615 1351495 := bstep (se 1 (by rfl) ⟨1013621, by rfl⟩ : syracuseStep 1351495 = 2027243) B2027243
theorem B6922205 : Blo 1064615 6922205 := bstep (se 3 (by rfl) ⟨1297913, by rfl⟩ : syracuseStep 6922205 = 2595827) B2595827
theorem B1351991 : Blo 1064615 1351991 := bstep (se 1 (by rfl) ⟨1013993, by rfl⟩ : syracuseStep 1351991 = 2027987) B2027987
theorem B1352143 : Blo 1064615 1352143 := bstep (se 1 (by rfl) ⟨1014107, by rfl⟩ : syracuseStep 1352143 = 2028215) B2028215
theorem B1581935 : Blo 1064615 1581935 := bstep (se 1 (by rfl) ⟨1186451, by rfl⟩ : syracuseStep 1581935 = 2372903) B2372903
theorem B3416975 : Blo 1064615 3416975 := bstep (se 1 (by rfl) ⟨2562731, by rfl⟩ : syracuseStep 3416975 = 5125463) B5125463
theorem B2401235 : Blo 1064615 2401235 := bstep (se 1 (by rfl) ⟨1800926, by rfl⟩ : syracuseStep 2401235 = 3601853) B3601853
theorem B12297359 : Blo 1064615 12297359 := bstep (se 1 (by rfl) ⟨9223019, by rfl⟩ : syracuseStep 12297359 = 18446039) B18446039
theorem B2696399 : Blo 1064615 2696399 := bstep (se 1 (by rfl) ⟨2022299, by rfl⟩ : syracuseStep 2696399 = 4044599) B4044599
theorem B2401487 : Blo 1064615 2401487 := bstep (se 1 (by rfl) ⟨1801115, by rfl⟩ : syracuseStep 2401487 = 3602231) B3602231
theorem B4859203 : Blo 1064615 4859203 := bstep (se 1 (by rfl) ⟨3644402, by rfl⟩ : syracuseStep 4859203 = 7288805) B7288805
theorem B2401811 : Blo 1064615 2401811 := bstep (se 1 (by rfl) ⟨1801358, by rfl⟩ : syracuseStep 2401811 = 3602717) B3602717
theorem B2696723 : Blo 1064615 2696723 := bstep (se 1 (by rfl) ⟨2022542, by rfl⟩ : syracuseStep 2696723 = 4045085) B4045085
theorem B3843665 : Blo 1064615 3843665 := bstep (se 2 (by rfl) ⟨1441374, by rfl⟩ : syracuseStep 3843665 = 2882749) B2882749
theorem B12167009 : Blo 1064615 12167009 := bstep (se 2 (by rfl) ⟨4562628, by rfl⟩ : syracuseStep 12167009 = 9125257) B9125257
theorem B2402495 : Blo 1064615 2402495 := bstep (se 1 (by rfl) ⟨1801871, by rfl⟩ : syracuseStep 2402495 = 3603743) B3603743
theorem B2599307 : Blo 1064615 2599307 := bstep (se 1 (by rfl) ⟨1949480, by rfl⟩ : syracuseStep 2599307 = 3898961) B3898961
theorem B27372491 : Blo 1064615 27372491 := bstep (se 1 (by rfl) ⟨20529368, by rfl⟩ : syracuseStep 27372491 = 41058737) B41058737
theorem B2403449 : Blo 1064615 2403449 := bstep (se 2 (by rfl) ⟨901293, by rfl⟩ : syracuseStep 2403449 = 1802587) B1802587
theorem B3419435 : Blo 1064615 3419435 := bstep (se 1 (by rfl) ⟨2564576, by rfl⟩ : syracuseStep 3419435 = 5129153) B5129153
theorem B2698859 : Blo 1064615 2698859 := bstep (se 1 (by rfl) ⟨2024144, by rfl⟩ : syracuseStep 2698859 = 4048289) B4048289
theorem B2404115 : Blo 1064615 2404115 := bstep (se 1 (by rfl) ⟨1803086, by rfl⟩ : syracuseStep 2404115 = 3606173) B3606173
theorem B6827951 : Blo 1064615 6827951 := bstep (se 1 (by rfl) ⟨5120963, by rfl⟩ : syracuseStep 6827951 = 10241927) B10241927
theorem B8105993 : Blo 1064615 8105993 := bstep (se 2 (by rfl) ⟨3039747, by rfl⟩ : syracuseStep 8105993 = 6079495) B6079495
theorem B9121841 : Blo 1064615 9121841 := bstep (se 2 (by rfl) ⟨3420690, by rfl⟩ : syracuseStep 9121841 = 6841381) B6841381
theorem B7779233 : Blo 1064615 7779233 := bstep (se 2 (by rfl) ⟨2917212, by rfl⟩ : syracuseStep 7779233 = 5834425) B5834425
theorem B4863091 : Blo 1064615 4863091 := bstep (se 1 (by rfl) ⟨3647318, by rfl⟩ : syracuseStep 4863091 = 7294637) B7294637
theorem B4043915 : Blo 1064615 4043915 := bstep (se 1 (by rfl) ⟨3032936, by rfl⟩ : syracuseStep 4043915 = 6065873) B6065873
theorem B2700499 : Blo 1064615 2700499 := bstep (se 1 (by rfl) ⟨2025374, by rfl⟩ : syracuseStep 2700499 = 4050749) B4050749
theorem B15349459 : Blo 1064615 15349459 := bstep (se 1 (by rfl) ⟨11512094, by rfl⟩ : syracuseStep 15349459 = 23024189) B23024189
theorem B6928175 : Blo 1064615 6928175 := bstep (se 1 (by rfl) ⟨5196131, by rfl⟩ : syracuseStep 6928175 = 10392263) B10392263
theorem B9222025 : Blo 1064615 9222025 := bstep (se 2 (by rfl) ⟨3458259, by rfl⟩ : syracuseStep 9222025 = 6916519) B6916519
theorem B6076397 : Blo 1064615 6076397 := bstep (se 3 (by rfl) ⟨1139324, by rfl⟩ : syracuseStep 6076397 = 2278649) B2278649
theorem B2734175 : Blo 1064615 2734175 := bstep (se 1 (by rfl) ⟨2050631, by rfl⟩ : syracuseStep 2734175 = 4101263) B4101263
theorem B4045099 : Blo 1064615 4045099 := bstep (se 1 (by rfl) ⟨3033824, by rfl⟩ : syracuseStep 4045099 = 6067649) B6067649
theorem B3422537 : Blo 1064615 3422537 := bstep (se 2 (by rfl) ⟨1283451, by rfl⟩ : syracuseStep 3422537 = 2566903) B2566903
theorem B3422587 : Blo 1064615 3422587 := bstep (se 1 (by rfl) ⟨2566940, by rfl⟩ : syracuseStep 3422587 = 5133881) B5133881
theorem B4864711 : Blo 1064615 4864711 := bstep (se 1 (by rfl) ⟨3648533, by rfl⟩ : syracuseStep 4864711 = 7297067) B7297067
theorem B1096751 : Blo 1064615 1096751 := bstep (se 1 (by rfl) ⟨822563, by rfl⟩ : syracuseStep 1096751 = 1645127) B1645127
theorem B150060221 : Blo 1064615 150060221 := bstep (se 3 (by rfl) ⟨28136291, by rfl⟩ : syracuseStep 150060221 = 56272583) B56272583
theorem B17284751 : Blo 1064615 17284751 := bstep (se 1 (by rfl) ⟨12963563, by rfl⟩ : syracuseStep 17284751 = 25927127) B25927127
theorem B2703091 : Blo 1064615 2703091 := bstep (se 1 (by rfl) ⟨2027318, by rfl⟩ : syracuseStep 2703091 = 4054637) B4054637
theorem B1064775 : Blo 1064615 1064775 := bstep (se 1 (by rfl) ⟨798581, by rfl⟩ : syracuseStep 1064775 = 1597163) B1597163
theorem B5193559 : Blo 1064615 5193559 := bstep (se 1 (by rfl) ⟨3895169, by rfl⟩ : syracuseStep 5193559 = 7790339) B7790339
theorem B1064927 : Blo 1064615 1064927 := bstep (se 1 (by rfl) ⟨798695, by rfl⟩ : syracuseStep 1064927 = 1597391) B1597391
theorem B1065191 : Blo 1064615 1065191 := bstep (se 1 (by rfl) ⟨798893, by rfl⟩ : syracuseStep 1065191 = 1597787) B1597787
theorem B1065343 : Blo 1064615 1065343 := bstep (se 1 (by rfl) ⟨799007, by rfl⟩ : syracuseStep 1065343 = 1598015) B1598015
theorem B1065423 : Blo 1064615 1065423 := bstep (se 1 (by rfl) ⟨799067, by rfl⟩ : syracuseStep 1065423 = 1598135) B1598135
theorem B1065575 : Blo 1064615 1065575 := bstep (se 1 (by rfl) ⟨799181, by rfl⟩ : syracuseStep 1065575 = 1598363) B1598363
theorem B1950473 : Blo 1064615 1950473 := bstep (se 2 (by rfl) ⟨731427, by rfl⟩ : syracuseStep 1950473 = 1462855) B1462855
theorem B2704175 : Blo 1064615 2704175 := bstep (se 1 (by rfl) ⟨2028131, by rfl⟩ : syracuseStep 2704175 = 4056263) B4056263
theorem B1065839 : Blo 1064615 1065839 := bstep (se 1 (by rfl) ⟨799379, by rfl⟩ : syracuseStep 1065839 = 1598759) B1598759
theorem B1065895 : Blo 1064615 1065895 := bstep (se 1 (by rfl) ⟨799421, by rfl⟩ : syracuseStep 1065895 = 1598843) B1598843
theorem B3851219 : Blo 1064615 3851219 := bstep (se 1 (by rfl) ⟨2888414, by rfl⟩ : syracuseStep 3851219 = 5776829) B5776829
theorem B1065979 : Blo 1064615 1065979 := bstep (se 1 (by rfl) ⟨799484, by rfl⟩ : syracuseStep 1065979 = 1598969) B1598969
theorem B1066047 : Blo 1064615 1066047 := bstep (se 1 (by rfl) ⟨799535, by rfl⟩ : syracuseStep 1066047 = 1599071) B1599071
theorem B2278505 : Blo 1064615 2278505 := bstep (se 2 (by rfl) ⟨854439, by rfl⟩ : syracuseStep 2278505 = 1708879) B1708879
theorem B1066191 : Blo 1064615 1066191 := bstep (se 1 (by rfl) ⟨799643, by rfl⟩ : syracuseStep 1066191 = 1599287) B1599287
theorem B9127241 : Blo 1064615 9127241 := bstep (se 2 (by rfl) ⟨3422715, by rfl⟩ : syracuseStep 9127241 = 6845431) B6845431
theorem B1066395 : Blo 1064615 1066395 := bstep (se 1 (by rfl) ⟨799796, by rfl⟩ : syracuseStep 1066395 = 1599593) B1599593
theorem B1066607 : Blo 1064615 1066607 := bstep (se 1 (by rfl) ⟨799955, by rfl⟩ : syracuseStep 1066607 = 1599911) B1599911
theorem B1066663 : Blo 1064615 1066663 := bstep (se 1 (by rfl) ⟨799997, by rfl⟩ : syracuseStep 1066663 = 1599995) B1599995
theorem B1197787 : Blo 1064615 1197787 := bstep (se 1 (by rfl) ⟨898340, by rfl⟩ : syracuseStep 1197787 = 1796681) B1796681
theorem B1066747 : Blo 1064615 1066747 := bstep (se 1 (by rfl) ⟨800060, by rfl⟩ : syracuseStep 1066747 = 1600121) B1600121
theorem B1066783 : Blo 1064615 1066783 := bstep (se 1 (by rfl) ⟨800087, by rfl⟩ : syracuseStep 1066783 = 1600175) B1600175
theorem B5392169 : Blo 1064615 5392169 := bstep (se 2 (by rfl) ⟨2022063, by rfl⟩ : syracuseStep 5392169 = 4044127) B4044127
theorem B1066815 : Blo 1064615 1066815 := bstep (se 1 (by rfl) ⟨800111, by rfl⟩ : syracuseStep 1066815 = 1600223) B1600223
theorem B1918799 : Blo 1064615 1918799 := bstep (se 1 (by rfl) ⟨1439099, by rfl⟩ : syracuseStep 1918799 = 2878199) B2878199
theorem B24627077 : Blo 1064615 24627077 := bstep (se 4 (by rfl) ⟨2308788, by rfl⟩ : syracuseStep 24627077 = 4617577) B4617577
theorem B1066991 : Blo 1064615 1066991 := bstep (se 1 (by rfl) ⟨800243, by rfl⟩ : syracuseStep 1066991 = 1600487) B1600487
theorem B1067163 : Blo 1064615 1067163 := bstep (se 1 (by rfl) ⟨800372, by rfl⟩ : syracuseStep 1067163 = 1600745) B1600745
theorem B1067199 : Blo 1064615 1067199 := bstep (se 1 (by rfl) ⟨800399, by rfl⟩ : syracuseStep 1067199 = 1600799) B1600799
theorem B1919209 : Blo 1064615 1919209 := bstep (se 2 (by rfl) ⟨719703, by rfl⟩ : syracuseStep 1919209 = 1439407) B1439407
theorem B1067311 : Blo 1064615 1067311 := bstep (se 1 (by rfl) ⟨800483, by rfl⟩ : syracuseStep 1067311 = 1600967) B1600967
theorem B1067547 : Blo 1064615 1067547 := bstep (se 1 (by rfl) ⟨800660, by rfl⟩ : syracuseStep 1067547 = 1601321) B1601321
theorem B1067551 : Blo 1064615 1067551 := bstep (se 1 (by rfl) ⟨800663, by rfl⟩ : syracuseStep 1067551 = 1601327) B1601327
theorem B1198939 : Blo 1064615 1198939 := bstep (se 1 (by rfl) ⟨899204, by rfl⟩ : syracuseStep 1198939 = 1798409) B1798409
theorem B1067867 : Blo 1064615 1067867 := bstep (se 1 (by rfl) ⟨800900, by rfl⟩ : syracuseStep 1067867 = 1601801) B1601801
theorem B1067935 : Blo 1064615 1067935 := bstep (se 1 (by rfl) ⟨800951, by rfl⟩ : syracuseStep 1067935 = 1601903) B1601903
theorem B1068079 : Blo 1064615 1068079 := bstep (se 1 (by rfl) ⟨801059, by rfl⟩ : syracuseStep 1068079 = 1602119) B1602119
theorem B1068103 : Blo 1064615 1068103 := bstep (se 1 (by rfl) ⟨801077, by rfl⟩ : syracuseStep 1068103 = 1602155) B1602155
theorem B1068255 : Blo 1064615 1068255 := bstep (se 1 (by rfl) ⟨801191, by rfl⟩ : syracuseStep 1068255 = 1602383) B1602383
theorem B17518007 : Blo 1064615 17518007 := bstep (se 1 (by rfl) ⟨13138505, by rfl⟩ : syracuseStep 17518007 = 26277011) B26277011
theorem B1068519 : Blo 1064615 1068519 := bstep (se 1 (by rfl) ⟨801389, by rfl⟩ : syracuseStep 1068519 = 1602779) B1602779
theorem B1199911 : Blo 1064615 1199911 := bstep (se 1 (by rfl) ⟨899933, by rfl⟩ : syracuseStep 1199911 = 1799867) B1799867
theorem B10244387 : Blo 1064615 10244387 := bstep (se 1 (by rfl) ⟨7683290, by rfl⟩ : syracuseStep 10244387 = 15366581) B15366581
theorem B5853977 : Blo 1064615 5853977 := bstep (se 2 (by rfl) ⟨2195241, by rfl⟩ : syracuseStep 5853977 = 4390483) B4390483
theorem B6083369 : Blo 1064615 6083369 := bstep (se 2 (by rfl) ⟨2281263, by rfl⟩ : syracuseStep 6083369 = 4562527) B4562527
theorem B1201063 : Blo 1064615 1201063 := bstep (se 1 (by rfl) ⟨900797, by rfl⟩ : syracuseStep 1201063 = 1801595) B1801595
theorem B18469883 : Blo 1064615 18469883 := bstep (se 1 (by rfl) ⟨13852412, by rfl⟩ : syracuseStep 18469883 = 27704825) B27704825
theorem B4052177 : Blo 1064615 4052177 := bstep (se 2 (by rfl) ⟨1519566, by rfl⟩ : syracuseStep 4052177 = 3039133) B3039133
theorem B3593591 : Blo 1064615 3593591 := bstep (se 1 (by rfl) ⟨2695193, by rfl⟩ : syracuseStep 3593591 = 5390387) B5390387
theorem B7296409 : Blo 1064615 7296409 := bstep (se 2 (by rfl) ⟨2736153, by rfl⟩ : syracuseStep 7296409 = 5472307) B5472307
theorem B3036923 : Blo 1064615 3036923 := bstep (se 1 (by rfl) ⟨2277692, by rfl⟩ : syracuseStep 3036923 = 4555385) B4555385
theorem B3168047 : Blo 1064615 3168047 := bstep (se 1 (by rfl) ⟨2376035, by rfl⟩ : syracuseStep 3168047 = 4752071) B4752071
theorem B2021183 : Blo 1064615 2021183 := bstep (se 1 (by rfl) ⟨1515887, by rfl⟩ : syracuseStep 2021183 = 3031775) B3031775
theorem B3594401 : Blo 1064615 3594401 := bstep (se 2 (by rfl) ⟨1347900, by rfl⟩ : syracuseStep 3594401 = 2695801) B2695801
theorem B18208961 : Blo 1064615 18208961 := bstep (se 2 (by rfl) ⟨6828360, by rfl⟩ : syracuseStep 18208961 = 13656721) B13656721
theorem B47962397 : Blo 1064615 47962397 := bstep (se 3 (by rfl) ⟨8992949, by rfl⟩ : syracuseStep 47962397 = 17985899) B17985899
theorem B3594671 : Blo 1064615 3594671 := bstep (se 1 (by rfl) ⟨2696003, by rfl⟩ : syracuseStep 3594671 = 5392007) B5392007
theorem B5757779 : Blo 1064615 5757779 := bstep (se 1 (by rfl) ⟨4318334, by rfl⟩ : syracuseStep 5757779 = 8636669) B8636669
theorem B5397353 : Blo 1064615 5397353 := bstep (se 2 (by rfl) ⟨2024007, by rfl⟩ : syracuseStep 5397353 = 4048015) B4048015
theorem B6085601 : Blo 1064615 6085601 := bstep (se 2 (by rfl) ⟨2282100, by rfl⟩ : syracuseStep 6085601 = 4564201) B4564201
theorem B2022823 : Blo 1064615 2022823 := bstep (se 1 (by rfl) ⟨1517117, by rfl⟩ : syracuseStep 2022823 = 3034235) B3034235
theorem B3595751 : Blo 1064615 3595751 := bstep (se 1 (by rfl) ⟨2696813, by rfl⟩ : syracuseStep 3595751 = 5393627) B5393627
theorem B1596923 : Blo 1064615 1596923 := bstep (se 1 (by rfl) ⟨1197692, by rfl⟩ : syracuseStep 1596923 = 2395385) B2395385
theorem B25943561 : Blo 1064615 25943561 := bstep (se 2 (by rfl) ⟨9728835, by rfl⟩ : syracuseStep 25943561 = 19457671) B19457671
theorem B4054607 : Blo 1064615 4054607 := bstep (se 1 (by rfl) ⟨3040955, by rfl⟩ : syracuseStep 4054607 = 6081911) B6081911
theorem B1597019 : Blo 1064615 1597019 := bstep (se 1 (by rfl) ⟨1197764, by rfl⟩ : syracuseStep 1597019 = 2395529) B2395529
theorem B1597103 : Blo 1064615 1597103 := bstep (se 1 (by rfl) ⟨1197827, by rfl⟩ : syracuseStep 1597103 = 2395655) B2395655
theorem B27385613 : Blo 1064615 27385613 := bstep (se 3 (by rfl) ⟨5134802, by rfl⟩ : syracuseStep 27385613 = 10269605) B10269605
theorem B1597223 : Blo 1064615 1597223 := bstep (se 1 (by rfl) ⟨1197917, by rfl⟩ : syracuseStep 1597223 = 2395835) B2395835
theorem B21880685 : Blo 1064615 21880685 := bstep (se 3 (by rfl) ⟨4102628, by rfl⟩ : syracuseStep 21880685 = 8205257) B8205257
theorem B1597307 : Blo 1064615 1597307 := bstep (se 1 (by rfl) ⟨1197980, by rfl⟩ : syracuseStep 1597307 = 2395961) B2395961
theorem B7692347 : Blo 1064615 7692347 := bstep (se 1 (by rfl) ⟨5769260, by rfl⟩ : syracuseStep 7692347 = 11538521) B11538521
theorem B3596507 : Blo 1064615 3596507 := bstep (se 1 (by rfl) ⟨2697380, by rfl⟩ : syracuseStep 3596507 = 5394761) B5394761
theorem B2023643 : Blo 1064615 2023643 := bstep (se 1 (by rfl) ⟨1517732, by rfl⟩ : syracuseStep 2023643 = 3035465) B3035465
theorem B1597727 : Blo 1064615 1597727 := bstep (se 1 (by rfl) ⟨1198295, by rfl⟩ : syracuseStep 1597727 = 2396591) B2396591
theorem B1597751 : Blo 1064615 1597751 := bstep (se 1 (by rfl) ⟨1198313, by rfl⟩ : syracuseStep 1597751 = 2396627) B2396627
theorem B56222029 : Blo 1064615 56222029 := bstep (se 3 (by rfl) ⟨10541630, by rfl⟩ : syracuseStep 56222029 = 21083261) B21083261
theorem B1597823 : Blo 1064615 1597823 := bstep (se 1 (by rfl) ⟨1198367, by rfl⟩ : syracuseStep 1597823 = 2396735) B2396735
theorem B1597895 : Blo 1064615 1597895 := bstep (se 1 (by rfl) ⟨1198421, by rfl⟩ : syracuseStep 1597895 = 2396843) B2396843
theorem B2023879 : Blo 1064615 2023879 := bstep (se 1 (by rfl) ⟨1517909, by rfl⟩ : syracuseStep 2023879 = 3035819) B3035819
theorem B3596777 : Blo 1064615 3596777 := bstep (se 2 (by rfl) ⟨1348791, by rfl⟩ : syracuseStep 3596777 = 2697583) B2697583
theorem B21881345 : Blo 1064615 21881345 := bstep (se 2 (by rfl) ⟨8205504, by rfl⟩ : syracuseStep 21881345 = 16411009) B16411009
theorem B5202505 : Blo 1064615 5202505 := bstep (se 2 (by rfl) ⟨1950939, by rfl⟩ : syracuseStep 5202505 = 3901879) B3901879
theorem B1598249 : Blo 1064615 1598249 := bstep (se 2 (by rfl) ⟨599343, by rfl⟩ : syracuseStep 1598249 = 1198687) B1198687
theorem B1598255 : Blo 1064615 1598255 := bstep (se 1 (by rfl) ⟨1198691, by rfl⟩ : syracuseStep 1598255 = 2397383) B2397383
theorem B1598375 : Blo 1064615 1598375 := bstep (se 1 (by rfl) ⟨1198781, by rfl⟩ : syracuseStep 1598375 = 2397563) B2397563
theorem B6841331 : Blo 1064615 6841331 := bstep (se 1 (by rfl) ⟨5130998, by rfl⟩ : syracuseStep 6841331 = 10261997) B10261997
theorem B1598459 : Blo 1064615 1598459 := bstep (se 1 (by rfl) ⟨1198844, by rfl⟩ : syracuseStep 1598459 = 2397689) B2397689
theorem B1598519 : Blo 1064615 1598519 := bstep (se 1 (by rfl) ⟨1198889, by rfl⟩ : syracuseStep 1598519 = 2397779) B2397779
theorem B3597371 : Blo 1064615 3597371 := bstep (se 1 (by rfl) ⟨2698028, by rfl⟩ : syracuseStep 3597371 = 5396057) B5396057
theorem B1598639 : Blo 1064615 1598639 := bstep (se 1 (by rfl) ⟨1198979, by rfl⟩ : syracuseStep 1598639 = 2397959) B2397959
theorem B7693501 : Blo 1064615 7693501 := bstep (se 3 (by rfl) ⟨1442531, by rfl⟩ : syracuseStep 7693501 = 2885063) B2885063
theorem B3597641 : Blo 1064615 3597641 := bstep (se 2 (by rfl) ⟨1349115, by rfl⟩ : syracuseStep 3597641 = 2698231) B2698231
theorem B5399945 : Blo 1064615 5399945 := bstep (se 2 (by rfl) ⟨2024979, by rfl⟩ : syracuseStep 5399945 = 4049959) B4049959
theorem B3040649 : Blo 1064615 3040649 := bstep (se 2 (by rfl) ⟨1140243, by rfl⟩ : syracuseStep 3040649 = 2280487) B2280487
theorem B1599047 : Blo 1064615 1599047 := bstep (se 1 (by rfl) ⟨1199285, by rfl⟩ : syracuseStep 1599047 = 2398571) B2398571
theorem B2025071 : Blo 1064615 2025071 := bstep (se 1 (by rfl) ⟨1518803, by rfl⟩ : syracuseStep 2025071 = 3037607) B3037607
theorem B3237497 : Blo 1064615 3237497 := bstep (se 2 (by rfl) ⟨1214061, by rfl⟩ : syracuseStep 3237497 = 2428123) B2428123
theorem B1599143 : Blo 1064615 1599143 := bstep (se 1 (by rfl) ⟨1199357, by rfl⟩ : syracuseStep 1599143 = 2398715) B2398715
theorem B1599227 : Blo 1064615 1599227 := bstep (se 1 (by rfl) ⟨1199420, by rfl⟩ : syracuseStep 1599227 = 2398841) B2398841
theorem B1599263 : Blo 1064615 1599263 := bstep (se 1 (by rfl) ⟨1199447, by rfl⟩ : syracuseStep 1599263 = 2398895) B2398895
theorem B1599311 : Blo 1064615 1599311 := bstep (se 1 (by rfl) ⟨1199483, by rfl⟩ : syracuseStep 1599311 = 2398967) B2398967
theorem B1599431 : Blo 1064615 1599431 := bstep (se 1 (by rfl) ⟨1199573, by rfl⟩ : syracuseStep 1599431 = 2399147) B2399147
theorem B31188941 : Blo 1064615 31188941 := bstep (se 3 (by rfl) ⟨5847926, by rfl⟩ : syracuseStep 31188941 = 11695853) B11695853
theorem B20506769 : Blo 1064615 20506769 := bstep (se 2 (by rfl) ⟨7690038, by rfl⟩ : syracuseStep 20506769 = 15380077) B15380077
theorem B10250387 : Blo 1064615 10250387 := bstep (se 1 (by rfl) ⟨7687790, by rfl⟩ : syracuseStep 10250387 = 15375581) B15375581
theorem B4057235 : Blo 1064615 4057235 := bstep (se 1 (by rfl) ⟨3042926, by rfl⟩ : syracuseStep 4057235 = 6085853) B6085853
theorem B1599785 : Blo 1064615 1599785 := bstep (se 2 (by rfl) ⟨599919, by rfl⟩ : syracuseStep 1599785 = 1199839) B1199839
theorem B1599791 : Blo 1064615 1599791 := bstep (se 1 (by rfl) ⟨1199843, by rfl⟩ : syracuseStep 1599791 = 2399687) B2399687
theorem B2025785 : Blo 1064615 2025785 := bstep (se 2 (by rfl) ⟨759669, by rfl⟩ : syracuseStep 2025785 = 1519339) B1519339
theorem B6842713 : Blo 1064615 6842713 := bstep (se 2 (by rfl) ⟨2566017, by rfl⟩ : syracuseStep 6842713 = 5132035) B5132035
theorem B1600031 : Blo 1064615 1600031 := bstep (se 1 (by rfl) ⟨1200023, by rfl⟩ : syracuseStep 1600031 = 2400047) B2400047
theorem B1600415 : Blo 1064615 1600415 := bstep (se 1 (by rfl) ⟨1200311, by rfl⟩ : syracuseStep 1600415 = 2400623) B2400623
theorem B6843329 : Blo 1064615 6843329 := bstep (se 2 (by rfl) ⟨2566248, by rfl⟩ : syracuseStep 6843329 = 5132497) B5132497
theorem B1600463 : Blo 1064615 1600463 := bstep (se 1 (by rfl) ⟨1200347, by rfl⟩ : syracuseStep 1600463 = 2400695) B2400695
theorem B1600553 : Blo 1064615 1600553 := bstep (se 2 (by rfl) ⟨600207, by rfl⟩ : syracuseStep 1600553 = 1200415) B1200415
theorem B1797167 : Blo 1064615 1797167 := bstep (se 1 (by rfl) ⟨1347875, by rfl⟩ : syracuseStep 1797167 = 2695751) B2695751
theorem B4549679 : Blo 1064615 4549679 := bstep (se 1 (by rfl) ⟨3412259, by rfl⟩ : syracuseStep 4549679 = 6824519) B6824519
theorem B1600559 : Blo 1064615 1600559 := bstep (se 1 (by rfl) ⟨1200419, by rfl⟩ : syracuseStep 1600559 = 2400839) B2400839
theorem B1600583 : Blo 1064615 1600583 := bstep (se 1 (by rfl) ⟨1200437, by rfl⟩ : syracuseStep 1600583 = 2400875) B2400875
theorem B1797241 : Blo 1064615 1797241 := bstep (se 2 (by rfl) ⟨673965, by rfl⟩ : syracuseStep 1797241 = 1347931) B1347931
theorem B1600847 : Blo 1064615 1600847 := bstep (se 1 (by rfl) ⟨1200635, by rfl⟩ : syracuseStep 1600847 = 2401271) B2401271
theorem B1797545 : Blo 1064615 1797545 := bstep (se 2 (by rfl) ⟨674079, by rfl⟩ : syracuseStep 1797545 = 1348159) B1348159
theorem B1600937 : Blo 1064615 1600937 := bstep (se 2 (by rfl) ⟨600351, by rfl⟩ : syracuseStep 1600937 = 1200703) B1200703
theorem B1601087 : Blo 1064615 1601087 := bstep (se 1 (by rfl) ⟨1200815, by rfl⟩ : syracuseStep 1601087 = 2401631) B2401631
theorem B1601351 : Blo 1064615 1601351 := bstep (se 1 (by rfl) ⟨1201013, by rfl⟩ : syracuseStep 1601351 = 2402027) B2402027
theorem B3600233 : Blo 1064615 3600233 := bstep (se 2 (by rfl) ⟨1350087, by rfl⟩ : syracuseStep 3600233 = 2700175) B2700175
theorem B1601435 : Blo 1064615 1601435 := bstep (se 1 (by rfl) ⟨1201076, by rfl⟩ : syracuseStep 1601435 = 2402153) B2402153
theorem B15790139 : Blo 1064615 15790139 := bstep (se 1 (by rfl) ⟨11842604, by rfl⟩ : syracuseStep 15790139 = 23685209) B23685209
theorem B1798375 : Blo 1064615 1798375 := bstep (se 1 (by rfl) ⟨1348781, by rfl⟩ : syracuseStep 1798375 = 2697563) B2697563
theorem B16675145 : Blo 1064615 16675145 := bstep (se 2 (by rfl) ⟨6253179, by rfl⟩ : syracuseStep 16675145 = 12506359) B12506359
theorem B6844763 : Blo 1064615 6844763 := bstep (se 1 (by rfl) ⟨5133572, by rfl⟩ : syracuseStep 6844763 = 10267145) B10267145
theorem B1798537 : Blo 1064615 1798537 := bstep (se 2 (by rfl) ⟨674451, by rfl⟩ : syracuseStep 1798537 = 1348903) B1348903
theorem B5403023 : Blo 1064615 5403023 := bstep (se 1 (by rfl) ⟨4052267, by rfl⟩ : syracuseStep 5403023 = 8104535) B8104535
theorem B4551079 : Blo 1064615 4551079 := bstep (se 1 (by rfl) ⟨3413309, by rfl⟩ : syracuseStep 4551079 = 6826619) B6826619
theorem B1601999 : Blo 1064615 1601999 := bstep (se 1 (by rfl) ⟨1201499, by rfl⟩ : syracuseStep 1601999 = 2402999) B2402999
theorem B1602041 : Blo 1064615 1602041 := bstep (se 2 (by rfl) ⟨600765, by rfl⟩ : syracuseStep 1602041 = 1201531) B1201531
theorem B1602143 : Blo 1064615 1602143 := bstep (se 1 (by rfl) ⟨1201607, by rfl⟩ : syracuseStep 1602143 = 2403215) B2403215
theorem B1798969 : Blo 1064615 1798969 := bstep (se 2 (by rfl) ⟨674613, by rfl⟩ : syracuseStep 1798969 = 1349227) B1349227
theorem B1799023 : Blo 1064615 1799023 := bstep (se 1 (by rfl) ⟨1349267, by rfl⟩ : syracuseStep 1799023 = 2698535) B2698535
theorem B3208061 : Blo 1064615 3208061 := bstep (se 3 (by rfl) ⟨601511, by rfl⟩ : syracuseStep 3208061 = 1203023) B1203023
theorem B1602623 : Blo 1064615 1602623 := bstep (se 1 (by rfl) ⟨1201967, by rfl⟩ : syracuseStep 1602623 = 2403935) B2403935
theorem B1799273 : Blo 1064615 1799273 := bstep (se 2 (by rfl) ⟨674727, by rfl⟩ : syracuseStep 1799273 = 1349455) B1349455
theorem B1602665 : Blo 1064615 1602665 := bstep (se 2 (by rfl) ⟨600999, by rfl⟩ : syracuseStep 1602665 = 1201999) B1201999
theorem B3601583 : Blo 1064615 3601583 := bstep (se 1 (by rfl) ⟨2701187, by rfl⟩ : syracuseStep 3601583 = 5402375) B5402375
theorem B1602767 : Blo 1064615 1602767 := bstep (se 1 (by rfl) ⟨1202075, by rfl⟩ : syracuseStep 1602767 = 2404151) B2404151
theorem B49870343 : Blo 1064615 49870343 := bstep (se 1 (by rfl) ⟨37402757, by rfl⟩ : syracuseStep 49870343 = 74805515) B74805515
theorem B4552787 : Blo 1064615 4552787 := bstep (se 1 (by rfl) ⟨3414590, by rfl⟩ : syracuseStep 4552787 = 6829181) B6829181
theorem B1800427 : Blo 1064615 1800427 := bstep (se 1 (by rfl) ⟨1350320, by rfl⟩ : syracuseStep 1800427 = 2700641) B2700641
theorem B11532547 : Blo 1064615 11532547 := bstep (se 1 (by rfl) ⟨8649410, by rfl⟩ : syracuseStep 11532547 = 17298821) B17298821
theorem B1800731 : Blo 1064615 1800731 := bstep (se 1 (by rfl) ⟨1350548, by rfl⟩ : syracuseStep 1800731 = 2701097) B2701097
theorem B18217709 : Blo 1064615 18217709 := bstep (se 3 (by rfl) ⟨3415820, by rfl⟩ : syracuseStep 18217709 = 6831641) B6831641
theorem B3603527 : Blo 1064615 3603527 := bstep (se 1 (by rfl) ⟨2702645, by rfl⟩ : syracuseStep 3603527 = 5405291) B5405291
theorem B3603581 : Blo 1064615 3603581 := bstep (se 3 (by rfl) ⟨675671, by rfl⟩ : syracuseStep 3603581 = 1351343) B1351343
theorem B1801399 : Blo 1064615 1801399 := bstep (se 1 (by rfl) ⟨1351049, by rfl⟩ : syracuseStep 1801399 = 2702099) B2702099
theorem B12975389 : Blo 1064615 12975389 := bstep (se 3 (by rfl) ⟨2432885, by rfl⟩ : syracuseStep 12975389 = 4865771) B4865771
theorem B3603851 : Blo 1064615 3603851 := bstep (se 1 (by rfl) ⟨2702888, by rfl⟩ : syracuseStep 3603851 = 5405777) B5405777
theorem B1801703 : Blo 1064615 1801703 := bstep (se 1 (by rfl) ⟨1351277, by rfl⟩ : syracuseStep 1801703 = 2702555) B2702555
theorem B1801723 : Blo 1064615 1801723 := bstep (se 1 (by rfl) ⟨1351292, by rfl⟩ : syracuseStep 1801723 = 2702585) B2702585
theorem B2883215 : Blo 1064615 2883215 := bstep (se 1 (by rfl) ⟨2162411, by rfl⟩ : syracuseStep 2883215 = 4324823) B4324823
theorem B8093357 : Blo 1064615 8093357 := bstep (se 3 (by rfl) ⟨1517504, by rfl⟩ : syracuseStep 8093357 = 3035009) B3035009
theorem B3079927 : Blo 1064615 3079927 := bstep (se 1 (by rfl) ⟨2309945, by rfl⟩ : syracuseStep 3079927 = 4619891) B4619891
theorem B1802155 : Blo 1064615 1802155 := bstep (se 1 (by rfl) ⟨1351616, by rfl⟩ : syracuseStep 1802155 = 2703233) B2703233
theorem B1802783 : Blo 1064615 1802783 := bstep (se 1 (by rfl) ⟨1352087, by rfl⟩ : syracuseStep 1802783 = 2704175) B2704175
theorem B1802857 : Blo 1064615 1802857 := bstep (se 2 (by rfl) ⟨676071, by rfl⟩ : syracuseStep 1802857 = 1352143) B1352143
theorem B3605309 : Blo 1064615 3605309 := bstep (se 3 (by rfl) ⟨675995, by rfl⟩ : syracuseStep 3605309 = 1351991) B1351991
theorem B18252701 : Blo 1064615 18252701 := bstep (se 3 (by rfl) ⟨3422381, by rfl⟩ : syracuseStep 18252701 = 6844763) B6844763
theorem B1279199 : Blo 1064615 1279199 := bstep (se 1 (by rfl) ⟨959399, by rfl⟩ : syracuseStep 1279199 = 1918799) B1918799
theorem B16418051 : Blo 1064615 16418051 := bstep (se 1 (by rfl) ⟨12313538, by rfl⟩ : syracuseStep 16418051 = 24627077) B24627077
theorem B3606011 : Blo 1064615 3606011 := bstep (se 1 (by rfl) ⟨2704508, by rfl⟩ : syracuseStep 3606011 = 5409017) B5409017
theorem B10258001 : Blo 1064615 10258001 := bstep (se 2 (by rfl) ⟨3846750, by rfl⟩ : syracuseStep 10258001 = 7693501) B7693501
theorem B4327937 : Blo 1064615 4327937 := bstep (se 2 (by rfl) ⟨1622976, by rfl⟩ : syracuseStep 4327937 = 3245953) B3245953
theorem B4328275 : Blo 1064615 4328275 := bstep (se 1 (by rfl) ⟨3246206, by rfl⟩ : syracuseStep 4328275 = 6492413) B6492413
theorem B2558945 : Blo 1064615 2558945 := bstep (se 2 (by rfl) ⟨959604, by rfl⟩ : syracuseStep 2558945 = 1919209) B1919209
theorem B3247229 : Blo 1064615 3247229 := bstep (se 3 (by rfl) ⟨608855, by rfl⟩ : syracuseStep 3247229 = 1217711) B1217711
theorem B3902651 : Blo 1064615 3902651 := bstep (se 1 (by rfl) ⟨2926988, by rfl⟩ : syracuseStep 3902651 = 5853977) B5853977
theorem B4328795 : Blo 1064615 4328795 := bstep (se 1 (by rfl) ⟨3246596, by rfl⟩ : syracuseStep 4328795 = 6493193) B6493193
theorem B2395727 : Blo 1064615 2395727 := bstep (se 1 (by rfl) ⟨1796795, by rfl⟩ : syracuseStep 2395727 = 3593591) B3593591
theorem B2887247 : Blo 1064615 2887247 := bstep (se 1 (by rfl) ⟨2165435, by rfl⟩ : syracuseStep 2887247 = 4330871) B4330871
theorem B19468127 : Blo 1064615 19468127 := bstep (se 1 (by rfl) ⟨14601095, by rfl⟩ : syracuseStep 19468127 = 29202191) B29202191
theorem B1347455 : Blo 1064615 1347455 := bstep (se 1 (by rfl) ⟨1010591, by rfl⟩ : syracuseStep 1347455 = 2021183) B2021183
theorem B2396267 : Blo 1064615 2396267 := bstep (se 1 (by rfl) ⟨1797200, by rfl⟩ : syracuseStep 2396267 = 3594401) B3594401
theorem B2396321 : Blo 1064615 2396321 := bstep (se 2 (by rfl) ⟨898620, by rfl⟩ : syracuseStep 2396321 = 1797241) B1797241
theorem B2560243 : Blo 1064615 2560243 := bstep (se 1 (by rfl) ⟨1920182, by rfl⟩ : syracuseStep 2560243 = 3840365) B3840365
theorem B2396447 : Blo 1064615 2396447 := bstep (se 1 (by rfl) ⟨1797335, by rfl⟩ : syracuseStep 2396447 = 3594671) B3594671
theorem B3838519 : Blo 1064615 3838519 := bstep (se 1 (by rfl) ⟨2878889, by rfl⟩ : syracuseStep 3838519 = 5757779) B5757779
theorem B2560859 : Blo 1064615 2560859 := bstep (se 1 (by rfl) ⟨1920644, by rfl⟩ : syracuseStep 2560859 = 3841289) B3841289
theorem B2397167 : Blo 1064615 2397167 := bstep (se 1 (by rfl) ⟨1797875, by rfl⟩ : syracuseStep 2397167 = 3595751) B3595751
theorem B18257075 : Blo 1064615 18257075 := bstep (se 1 (by rfl) ⟨13692806, by rfl⟩ : syracuseStep 18257075 = 27385613) B27385613
theorem B14587123 : Blo 1064615 14587123 := bstep (se 1 (by rfl) ⟨10940342, by rfl⟩ : syracuseStep 14587123 = 21880685) B21880685
theorem B2397671 : Blo 1064615 2397671 := bstep (se 1 (by rfl) ⟨1798253, by rfl⟩ : syracuseStep 2397671 = 3596507) B3596507
theorem B2397833 : Blo 1064615 2397833 := bstep (se 2 (by rfl) ⟨899187, by rfl⟩ : syracuseStep 2397833 = 1798375) B1798375
theorem B2397851 : Blo 1064615 2397851 := bstep (se 1 (by rfl) ⟨1798388, by rfl⟩ : syracuseStep 2397851 = 3596777) B3596777
theorem B2398049 : Blo 1064615 2398049 := bstep (se 2 (by rfl) ⟨899268, by rfl⟩ : syracuseStep 2398049 = 1798537) B1798537
theorem B6068105 : Blo 1064615 6068105 := bstep (se 2 (by rfl) ⟨2275539, by rfl⟩ : syracuseStep 6068105 = 4551079) B4551079
theorem B4560887 : Blo 1064615 4560887 := bstep (se 1 (by rfl) ⟨3420665, by rfl⟩ : syracuseStep 4560887 = 6841331) B6841331
theorem B2398247 : Blo 1064615 2398247 := bstep (se 1 (by rfl) ⟨1798685, by rfl⟩ : syracuseStep 2398247 = 3597371) B3597371
theorem B1710217 : Blo 1064615 1710217 := bstep (se 2 (by rfl) ⟨641331, by rfl⟩ : syracuseStep 1710217 = 1282663) B1282663
theorem B2398427 : Blo 1064615 2398427 := bstep (se 1 (by rfl) ⟨1798820, by rfl⟩ : syracuseStep 2398427 = 3597641) B3597641
theorem B2562443 : Blo 1064615 2562443 := bstep (se 1 (by rfl) ⟨1921832, by rfl⟩ : syracuseStep 2562443 = 3843665) B3843665
theorem B1350047 : Blo 1064615 1350047 := bstep (se 1 (by rfl) ⟨1012535, by rfl⟩ : syracuseStep 1350047 = 2025071) B2025071
theorem B2398625 : Blo 1064615 2398625 := bstep (se 2 (by rfl) ⟨899484, by rfl⟩ : syracuseStep 2398625 = 1798969) B1798969
theorem B2398697 : Blo 1064615 2398697 := bstep (se 2 (by rfl) ⟨899511, by rfl⟩ : syracuseStep 2398697 = 1799023) B1799023
theorem B13671179 : Blo 1064615 13671179 := bstep (se 1 (by rfl) ⟨10253384, by rfl⟩ : syracuseStep 13671179 = 20506769) B20506769
theorem B1350523 : Blo 1064615 1350523 := bstep (se 1 (by rfl) ⟨1012892, by rfl⟩ : syracuseStep 1350523 = 2025785) B2025785
theorem B4562219 : Blo 1064615 4562219 := bstep (se 1 (by rfl) ⟨3421664, by rfl⟩ : syracuseStep 4562219 = 6843329) B6843329
theorem B12296033 : Blo 1064615 12296033 := bstep (se 2 (by rfl) ⟨4611012, by rfl⟩ : syracuseStep 12296033 = 9222025) B9222025
theorem B2400155 : Blo 1064615 2400155 := bstep (se 1 (by rfl) ⟨1800116, by rfl⟩ : syracuseStep 2400155 = 3600233) B3600233
theorem B10526759 : Blo 1064615 10526759 := bstep (se 1 (by rfl) ⟨7895069, by rfl⟩ : syracuseStep 10526759 = 15790139) B15790139
theorem B2924669 : Blo 1064615 2924669 := bstep (se 3 (by rfl) ⟨548375, by rfl⟩ : syracuseStep 2924669 = 1096751) B1096751
theorem B11116763 : Blo 1064615 11116763 := bstep (se 1 (by rfl) ⟨8337572, by rfl⟩ : syracuseStep 11116763 = 16675145) B16675145
theorem B2400569 : Blo 1064615 2400569 := bstep (se 2 (by rfl) ⟨900213, by rfl⟩ : syracuseStep 2400569 = 1800427) B1800427
theorem B15376729 : Blo 1064615 15376729 := bstep (se 2 (by rfl) ⟨5766273, by rfl⟩ : syracuseStep 15376729 = 11532547) B11532547
theorem B4563449 : Blo 1064615 4563449 := bstep (se 2 (by rfl) ⟨1711293, by rfl⟩ : syracuseStep 4563449 = 3422587) B3422587
theorem B2138707 : Blo 1064615 2138707 := bstep (se 1 (by rfl) ⟨1604030, by rfl⟩ : syracuseStep 2138707 = 3208061) B3208061
theorem B5186155 : Blo 1064615 5186155 := bstep (se 1 (by rfl) ⟨3889616, by rfl⟩ : syracuseStep 5186155 = 7779233) B7779233
theorem B2695943 : Blo 1064615 2695943 := bstep (se 1 (by rfl) ⟨2021957, by rfl⟩ : syracuseStep 2695943 = 4043915) B4043915
theorem B9118493 : Blo 1064615 9118493 := bstep (se 3 (by rfl) ⟨1709717, by rfl⟩ : syracuseStep 9118493 = 3419435) B3419435
theorem B2401055 : Blo 1064615 2401055 := bstep (se 1 (by rfl) ⟨1800791, by rfl⟩ : syracuseStep 2401055 = 3601583) B3601583
theorem B2401865 : Blo 1064615 2401865 := bstep (se 2 (by rfl) ⟨900699, by rfl⟩ : syracuseStep 2401865 = 1801399) B1801399
theorem B27666137 : Blo 1064615 27666137 := bstep (se 2 (by rfl) ⟨10374801, by rfl⟩ : syracuseStep 27666137 = 20749603) B20749603
theorem B2697097 : Blo 1064615 2697097 := bstep (se 2 (by rfl) ⟨1011411, by rfl⟩ : syracuseStep 2697097 = 2022823) B2022823
theorem B2402297 : Blo 1064615 2402297 := bstep (se 2 (by rfl) ⟨900861, by rfl⟩ : syracuseStep 2402297 = 1801723) B1801723
theorem B2402351 : Blo 1064615 2402351 := bstep (se 1 (by rfl) ⟨1801763, by rfl⟩ : syracuseStep 2402351 = 3603527) B3603527
theorem B2402387 : Blo 1064615 2402387 := bstep (se 1 (by rfl) ⟨1801790, by rfl⟩ : syracuseStep 2402387 = 3603581) B3603581
theorem B2402567 : Blo 1064615 2402567 := bstep (se 1 (by rfl) ⟨1801925, by rfl⟩ : syracuseStep 2402567 = 3603851) B3603851
theorem B4106569 : Blo 1064615 4106569 := bstep (se 2 (by rfl) ⟨1539963, by rfl⟩ : syracuseStep 4106569 = 3079927) B3079927
theorem B6924745 : Blo 1064615 6924745 := bstep (se 2 (by rfl) ⟨2596779, by rfl⟩ : syracuseStep 6924745 = 5193559) B5193559
theorem B2402873 : Blo 1064615 2402873 := bstep (se 2 (by rfl) ⟨901077, by rfl⟩ : syracuseStep 2402873 = 1802155) B1802155
theorem B9743291 : Blo 1064615 9743291 := bstep (se 1 (by rfl) ⟨7307468, by rfl⟩ : syracuseStep 9743291 = 14614937) B14614937
theorem B2698505 : Blo 1064615 2698505 := bstep (se 2 (by rfl) ⟨1011939, by rfl⟩ : syracuseStep 2698505 = 2023879) B2023879
theorem B2403593 : Blo 1064615 2403593 := bstep (se 2 (by rfl) ⟨901347, by rfl⟩ : syracuseStep 2403593 = 1802695) B1802695
theorem B2567479 : Blo 1064615 2567479 := bstep (se 1 (by rfl) ⟨1925609, by rfl⟩ : syracuseStep 2567479 = 3851219) B3851219
theorem B1519003 : Blo 1064615 1519003 := bstep (se 1 (by rfl) ⟨1139252, by rfl⟩ : syracuseStep 1519003 = 2278505) B2278505
theorem B4042487 : Blo 1064615 4042487 := bstep (se 1 (by rfl) ⟨3031865, by rfl⟩ : syracuseStep 4042487 = 6063731) B6063731
theorem B12955787 : Blo 1064615 12955787 := bstep (se 1 (by rfl) ⟨9716840, by rfl⟩ : syracuseStep 12955787 = 19433681) B19433681
theorem B34648505 : Blo 1064615 34648505 := bstep (se 2 (by rfl) ⟨12993189, by rfl⟩ : syracuseStep 34648505 = 25986379) B25986379
theorem B4043459 : Blo 1064615 4043459 := bstep (se 1 (by rfl) ⟨3032594, by rfl⟩ : syracuseStep 4043459 = 6065189) B6065189
theorem B11678671 : Blo 1064615 11678671 := bstep (se 1 (by rfl) ⟨8759003, by rfl⟩ : syracuseStep 11678671 = 17518007) B17518007
theorem B33731741 : Blo 1064615 33731741 := bstep (se 3 (by rfl) ⟨6324701, by rfl⟩ : syracuseStep 33731741 = 12649403) B12649403
theorem B98579845 : Blo 1064615 98579845 := bstep (se 4 (by rfl) ⟨9241860, by rfl⟩ : syracuseStep 98579845 = 18483721) B18483721
theorem B8107451 : Blo 1064615 8107451 := bstep (se 1 (by rfl) ⟨6080588, by rfl⟩ : syracuseStep 8107451 = 12161177) B12161177
theorem B6829591 : Blo 1064615 6829591 := bstep (se 1 (by rfl) ⟨5122193, by rfl⟩ : syracuseStep 6829591 = 10244387) B10244387
theorem B2274959 : Blo 1064615 2274959 := bstep (se 1 (by rfl) ⟨1706219, by rfl⟩ : syracuseStep 2274959 = 3412439) B3412439
theorem B4044431 : Blo 1064615 4044431 := bstep (se 1 (by rfl) ⟨3033323, by rfl⟩ : syracuseStep 4044431 = 6066647) B6066647
theorem B9123617 : Blo 1064615 9123617 := bstep (se 2 (by rfl) ⟨3421356, by rfl⟩ : syracuseStep 9123617 = 6842713) B6842713
theorem B2701451 : Blo 1064615 2701451 := bstep (se 1 (by rfl) ⟨2026088, by rfl⟩ : syracuseStep 2701451 = 4052177) B4052177
theorem B9222329 : Blo 1064615 9222329 := bstep (se 2 (by rfl) ⟨3458373, by rfl⟩ : syracuseStep 9222329 = 6916747) B6916747
theorem B2112031 : Blo 1064615 2112031 := bstep (se 1 (by rfl) ⟨1584023, by rfl⟩ : syracuseStep 2112031 = 3168047) B3168047
theorem B12139307 : Blo 1064615 12139307 := bstep (se 1 (by rfl) ⟨9104480, by rfl⟩ : syracuseStep 12139307 = 18208961) B18208961
theorem B1064615 : Blo 1064615 1064615 := bstep (se 1 (by rfl) ⟨798461, by rfl⟩ : syracuseStep 1064615 = 1596923) B1596923
theorem B2703071 : Blo 1064615 2703071 := bstep (se 1 (by rfl) ⟨2027303, by rfl⟩ : syracuseStep 2703071 = 4054607) B4054607
theorem B1064679 : Blo 1064615 1064679 := bstep (se 1 (by rfl) ⟨798509, by rfl⟩ : syracuseStep 1064679 = 1597019) B1597019
theorem B1064735 : Blo 1064615 1064735 := bstep (se 1 (by rfl) ⟨798551, by rfl⟩ : syracuseStep 1064735 = 1597103) B1597103
theorem B1064815 : Blo 1064615 1064815 := bstep (se 1 (by rfl) ⟨798611, by rfl⟩ : syracuseStep 1064815 = 1597223) B1597223
theorem B1064871 : Blo 1064615 1064871 := bstep (se 1 (by rfl) ⟨798653, by rfl⟩ : syracuseStep 1064871 = 1597307) B1597307
theorem B5128231 : Blo 1064615 5128231 := bstep (se 1 (by rfl) ⟨3846173, by rfl⟩ : syracuseStep 5128231 = 7692347) B7692347
theorem B1065151 : Blo 1064615 1065151 := bstep (se 1 (by rfl) ⟨798863, by rfl⟩ : syracuseStep 1065151 = 1597727) B1597727
theorem B1065167 : Blo 1064615 1065167 := bstep (se 1 (by rfl) ⟨798875, by rfl⟩ : syracuseStep 1065167 = 1597751) B1597751
theorem B12140765 : Blo 1064615 12140765 := bstep (se 3 (by rfl) ⟨2276393, by rfl⟩ : syracuseStep 12140765 = 4552787) B4552787
theorem B7291133 : Blo 1064615 7291133 := bstep (se 3 (by rfl) ⟨1367087, by rfl⟩ : syracuseStep 7291133 = 2734175) B2734175
theorem B1065215 : Blo 1064615 1065215 := bstep (se 1 (by rfl) ⟨798911, by rfl⟩ : syracuseStep 1065215 = 1597823) B1597823
theorem B1065263 : Blo 1064615 1065263 := bstep (se 1 (by rfl) ⟨798947, by rfl⟩ : syracuseStep 1065263 = 1597895) B1597895
theorem B7389521 : Blo 1064615 7389521 := bstep (se 2 (by rfl) ⟨2771070, by rfl⟩ : syracuseStep 7389521 = 5542141) B5542141
theorem B1065499 : Blo 1064615 1065499 := bstep (se 1 (by rfl) ⟨799124, by rfl⟩ : syracuseStep 1065499 = 1598249) B1598249
theorem B1065503 : Blo 1064615 1065503 := bstep (se 1 (by rfl) ⟨799127, by rfl⟩ : syracuseStep 1065503 = 1598255) B1598255
theorem B2277983 : Blo 1064615 2277983 := bstep (se 1 (by rfl) ⟨1708487, by rfl⟩ : syracuseStep 2277983 = 3416975) B3416975
theorem B1065583 : Blo 1064615 1065583 := bstep (se 1 (by rfl) ⟨799187, by rfl⟩ : syracuseStep 1065583 = 1598375) B1598375
theorem B1065639 : Blo 1064615 1065639 := bstep (se 1 (by rfl) ⟨799229, by rfl⟩ : syracuseStep 1065639 = 1598459) B1598459
theorem B1065679 : Blo 1064615 1065679 := bstep (se 1 (by rfl) ⟨799259, by rfl⟩ : syracuseStep 1065679 = 1598519) B1598519
theorem B1065759 : Blo 1064615 1065759 := bstep (se 1 (by rfl) ⟨799319, by rfl⟩ : syracuseStep 1065759 = 1598639) B1598639
theorem B1066031 : Blo 1064615 1066031 := bstep (se 1 (by rfl) ⟨799523, by rfl⟩ : syracuseStep 1066031 = 1599047) B1599047
theorem B1066095 : Blo 1064615 1066095 := bstep (se 1 (by rfl) ⟨799571, by rfl⟩ : syracuseStep 1066095 = 1599143) B1599143
theorem B1066151 : Blo 1064615 1066151 := bstep (se 1 (by rfl) ⟨799613, by rfl⟩ : syracuseStep 1066151 = 1599227) B1599227
theorem B1066175 : Blo 1064615 1066175 := bstep (se 1 (by rfl) ⟨799631, by rfl⟩ : syracuseStep 1066175 = 1599263) B1599263
theorem B1066207 : Blo 1064615 1066207 := bstep (se 1 (by rfl) ⟨799655, by rfl⟩ : syracuseStep 1066207 = 1599311) B1599311
theorem B8111339 : Blo 1064615 8111339 := bstep (se 1 (by rfl) ⟨6083504, by rfl⟩ : syracuseStep 8111339 = 12167009) B12167009
theorem B1066287 : Blo 1064615 1066287 := bstep (se 1 (by rfl) ⟨799715, by rfl⟩ : syracuseStep 1066287 = 1599431) B1599431
theorem B20792627 : Blo 1064615 20792627 := bstep (se 1 (by rfl) ⟨15594470, by rfl⟩ : syracuseStep 20792627 = 31188941) B31188941
theorem B6833591 : Blo 1064615 6833591 := bstep (se 1 (by rfl) ⟨5125193, by rfl⟩ : syracuseStep 6833591 = 10250387) B10250387
theorem B2704823 : Blo 1064615 2704823 := bstep (se 1 (by rfl) ⟨2028617, by rfl⟩ : syracuseStep 2704823 = 4057235) B4057235
theorem B1066523 : Blo 1064615 1066523 := bstep (se 1 (by rfl) ⟨799892, by rfl⟩ : syracuseStep 1066523 = 1599785) B1599785
theorem B1066527 : Blo 1064615 1066527 := bstep (se 1 (by rfl) ⟨799895, by rfl⟩ : syracuseStep 1066527 = 1599791) B1599791
theorem B1066687 : Blo 1064615 1066687 := bstep (se 1 (by rfl) ⟨800015, by rfl⟩ : syracuseStep 1066687 = 1600031) B1600031
theorem B1066943 : Blo 1064615 1066943 := bstep (se 1 (by rfl) ⟨800207, by rfl⟩ : syracuseStep 1066943 = 1600415) B1600415
theorem B1066975 : Blo 1064615 1066975 := bstep (se 1 (by rfl) ⟨800231, by rfl⟩ : syracuseStep 1066975 = 1600463) B1600463
theorem B1067035 : Blo 1064615 1067035 := bstep (se 1 (by rfl) ⟨800276, by rfl⟩ : syracuseStep 1067035 = 1600553) B1600553
theorem B1198111 : Blo 1064615 1198111 := bstep (se 1 (by rfl) ⟨898583, by rfl⟩ : syracuseStep 1198111 = 1797167) B1797167
theorem B3033119 : Blo 1064615 3033119 := bstep (se 1 (by rfl) ⟨2274839, by rfl⟩ : syracuseStep 3033119 = 4549679) B4549679
theorem B1067039 : Blo 1064615 1067039 := bstep (se 1 (by rfl) ⟨800279, by rfl⟩ : syracuseStep 1067039 = 1600559) B1600559
theorem B1067055 : Blo 1064615 1067055 := bstep (se 1 (by rfl) ⟨800291, by rfl⟩ : syracuseStep 1067055 = 1600583) B1600583
theorem B38914181 : Blo 1064615 38914181 := bstep (se 4 (by rfl) ⟨3648204, by rfl⟩ : syracuseStep 38914181 = 7296409) B7296409
theorem B1067231 : Blo 1064615 1067231 := bstep (se 1 (by rfl) ⟨800423, by rfl⟩ : syracuseStep 1067231 = 1600847) B1600847
theorem B20465945 : Blo 1064615 20465945 := bstep (se 2 (by rfl) ⟨7674729, by rfl⟩ : syracuseStep 20465945 = 15349459) B15349459
theorem B1198363 : Blo 1064615 1198363 := bstep (se 1 (by rfl) ⟨898772, by rfl⟩ : syracuseStep 1198363 = 1797545) B1797545
theorem B1067291 : Blo 1064615 1067291 := bstep (se 1 (by rfl) ⟨800468, by rfl⟩ : syracuseStep 1067291 = 1600937) B1600937
theorem B1067391 : Blo 1064615 1067391 := bstep (se 1 (by rfl) ⟨800543, by rfl⟩ : syracuseStep 1067391 = 1601087) B1601087
theorem B1067567 : Blo 1064615 1067567 := bstep (se 1 (by rfl) ⟨800675, by rfl⟩ : syracuseStep 1067567 = 1601351) B1601351
theorem B1067623 : Blo 1064615 1067623 := bstep (se 1 (by rfl) ⟨800717, by rfl⟩ : syracuseStep 1067623 = 1601435) B1601435
theorem B6081227 : Blo 1064615 6081227 := bstep (se 1 (by rfl) ⟨4560920, by rfl⟩ : syracuseStep 6081227 = 9121841) B9121841
theorem B1067999 : Blo 1064615 1067999 := bstep (se 1 (by rfl) ⟨800999, by rfl⟩ : syracuseStep 1067999 = 1601999) B1601999
theorem B1068027 : Blo 1064615 1068027 := bstep (se 1 (by rfl) ⟨801020, by rfl⟩ : syracuseStep 1068027 = 1602041) B1602041
theorem B5393465 : Blo 1064615 5393465 := bstep (se 2 (by rfl) ⟨2022549, by rfl⟩ : syracuseStep 5393465 = 4045099) B4045099
theorem B1068095 : Blo 1064615 1068095 := bstep (se 1 (by rfl) ⟨801071, by rfl⟩ : syracuseStep 1068095 = 1602143) B1602143
theorem B1068415 : Blo 1064615 1068415 := bstep (se 1 (by rfl) ⟨801311, by rfl⟩ : syracuseStep 1068415 = 1602623) B1602623
theorem B1199515 : Blo 1064615 1199515 := bstep (se 1 (by rfl) ⟨899636, by rfl⟩ : syracuseStep 1199515 = 1799273) B1799273
theorem B1068443 : Blo 1064615 1068443 := bstep (se 1 (by rfl) ⟨801332, by rfl⟩ : syracuseStep 1068443 = 1602665) B1602665
theorem B1068511 : Blo 1064615 1068511 := bstep (se 1 (by rfl) ⟨801383, by rfl⟩ : syracuseStep 1068511 = 1602767) B1602767
theorem B33246895 : Blo 1064615 33246895 := bstep (se 1 (by rfl) ⟨24935171, by rfl⟩ : syracuseStep 33246895 = 49870343) B49870343
theorem B4050931 : Blo 1064615 4050931 := bstep (se 1 (by rfl) ⟨3038198, by rfl⟩ : syracuseStep 4050931 = 6076397) B6076397
theorem B2281691 : Blo 1064615 2281691 := bstep (se 1 (by rfl) ⟨1711268, by rfl⟩ : syracuseStep 2281691 = 3422537) B3422537
theorem B1200487 : Blo 1064615 1200487 := bstep (se 1 (by rfl) ⟨900365, by rfl⟩ : syracuseStep 1200487 = 1800731) B1800731
theorem B12145139 : Blo 1064615 12145139 := bstep (se 1 (by rfl) ⟨9108854, by rfl⟩ : syracuseStep 12145139 = 18217709) B18217709
theorem B15389189 : Blo 1064615 15389189 := bstep (se 4 (by rfl) ⟨1442736, by rfl⟩ : syracuseStep 15389189 = 2885473) B2885473
theorem B1201135 : Blo 1064615 1201135 := bstep (se 1 (by rfl) ⟨900851, by rfl⟩ : syracuseStep 1201135 = 1801703) B1801703
theorem B11523167 : Blo 1064615 11523167 := bstep (se 1 (by rfl) ⟨8642375, by rfl⟩ : syracuseStep 11523167 = 17284751) B17284751
theorem B1922143 : Blo 1064615 1922143 := bstep (se 1 (by rfl) ⟨1441607, by rfl⟩ : syracuseStep 1922143 = 2883215) B2883215
theorem B5395571 : Blo 1064615 5395571 := bstep (se 1 (by rfl) ⟨4046678, by rfl⟩ : syracuseStep 5395571 = 8093357) B8093357
theorem B2053487 : Blo 1064615 2053487 := bstep (se 1 (by rfl) ⟨1540115, by rfl⟩ : syracuseStep 2053487 = 3080231) B3080231
theorem B1201639 : Blo 1064615 1201639 := bstep (se 1 (by rfl) ⟨901229, by rfl⟩ : syracuseStep 1201639 = 1802459) B1802459
theorem B1201819 : Blo 1064615 1201819 := bstep (se 1 (by rfl) ⟨901364, by rfl⟩ : syracuseStep 1201819 = 1802729) B1802729
theorem B1300315 : Blo 1064615 1300315 := bstep (se 1 (by rfl) ⟨975236, by rfl⟩ : syracuseStep 1300315 = 1950473) B1950473
theorem B5396381 : Blo 1064615 5396381 := bstep (se 3 (by rfl) ⟨1011821, by rfl⟩ : syracuseStep 5396381 = 2023643) B2023643
theorem B6936673 : Blo 1064615 6936673 := bstep (se 2 (by rfl) ⟨2601252, by rfl⟩ : syracuseStep 6936673 = 5202505) B5202505
theorem B6084827 : Blo 1064615 6084827 := bstep (se 1 (by rfl) ⟨4563620, by rfl⟩ : syracuseStep 6084827 = 9127241) B9127241
theorem B3594779 : Blo 1064615 3594779 := bstep (se 1 (by rfl) ⟨2696084, by rfl⟩ : syracuseStep 3594779 = 5392169) B5392169
theorem B58350253 : Blo 1064615 58350253 := bstep (se 3 (by rfl) ⟨10940672, by rfl⟩ : syracuseStep 58350253 = 21881345) B21881345
theorem B5397191 : Blo 1064615 5397191 := bstep (se 1 (by rfl) ⟨4047893, by rfl⟩ : syracuseStep 5397191 = 8095787) B8095787
theorem B299850821 : Blo 1064615 299850821 := bstep (se 4 (by rfl) ⟨28111014, by rfl⟩ : syracuseStep 299850821 = 56222029) B56222029
theorem B6478937 : Blo 1064615 6478937 := bstep (se 2 (by rfl) ⟨2429601, by rfl⟩ : syracuseStep 6478937 = 4859203) B4859203
theorem B7691597 : Blo 1064615 7691597 := bstep (se 3 (by rfl) ⟨1442174, by rfl⟩ : syracuseStep 7691597 = 2884349) B2884349
theorem B1597049 : Blo 1064615 1597049 := bstep (se 2 (by rfl) ⟨598893, by rfl⟩ : syracuseStep 1597049 = 1197787) B1197787
theorem B4218493 : Blo 1064615 4218493 := bstep (se 3 (by rfl) ⟨790967, by rfl⟩ : syracuseStep 4218493 = 1581935) B1581935
theorem B1597295 : Blo 1064615 1597295 := bstep (se 1 (by rfl) ⟨1197971, by rfl⟩ : syracuseStep 1597295 = 2395943) B2395943
theorem B1924975 : Blo 1064615 1924975 := bstep (se 1 (by rfl) ⟨1443731, by rfl⟩ : syracuseStep 1924975 = 2887463) B2887463
theorem B32792957 : Blo 1064615 32792957 := bstep (se 3 (by rfl) ⟨6148679, by rfl⟩ : syracuseStep 32792957 = 12297359) B12297359
theorem B1597979 : Blo 1064615 1597979 := bstep (se 1 (by rfl) ⟨1198484, by rfl⟩ : syracuseStep 1597979 = 2396969) B2396969
theorem B4055579 : Blo 1064615 4055579 := bstep (se 1 (by rfl) ⟨3041684, by rfl⟩ : syracuseStep 4055579 = 6083369) B6083369
theorem B1139231 : Blo 1064615 1139231 := bstep (se 1 (by rfl) ⟨854423, by rfl⟩ : syracuseStep 1139231 = 1708847) B1708847
theorem B12313255 : Blo 1064615 12313255 := bstep (se 1 (by rfl) ⟨9234941, by rfl⟩ : syracuseStep 12313255 = 18469883) B18469883
theorem B1598159 : Blo 1064615 1598159 := bstep (se 1 (by rfl) ⟨1198619, by rfl⟩ : syracuseStep 1598159 = 2397239) B2397239
theorem B1598171 : Blo 1064615 1598171 := bstep (se 1 (by rfl) ⟨1198628, by rfl⟩ : syracuseStep 1598171 = 2397257) B2397257
theorem B8086553 : Blo 1064615 8086553 := bstep (se 2 (by rfl) ⟨3032457, by rfl⟩ : syracuseStep 8086553 = 6064915) B6064915
theorem B1598585 : Blo 1064615 1598585 := bstep (se 2 (by rfl) ⟨599469, by rfl⟩ : syracuseStep 1598585 = 1198939) B1198939
theorem B2024615 : Blo 1064615 2024615 := bstep (se 1 (by rfl) ⟨1518461, by rfl⟩ : syracuseStep 2024615 = 3036923) B3036923
theorem B31974931 : Blo 1064615 31974931 := bstep (se 1 (by rfl) ⟨23981198, by rfl⟩ : syracuseStep 31974931 = 47962397) B47962397
theorem B4548413 : Blo 1064615 4548413 := bstep (se 3 (by rfl) ⟨852827, by rfl⟩ : syracuseStep 4548413 = 1705655) B1705655
theorem B3598235 : Blo 1064615 3598235 := bstep (se 1 (by rfl) ⟨2698676, by rfl⟩ : syracuseStep 3598235 = 5397353) B5397353
theorem B6842303 : Blo 1064615 6842303 := bstep (se 1 (by rfl) ⟨5131727, by rfl⟩ : syracuseStep 6842303 = 10263455) B10263455
theorem B1599455 : Blo 1064615 1599455 := bstep (se 1 (by rfl) ⟨1199591, by rfl⟩ : syracuseStep 1599455 = 2399183) B2399183
theorem B1599467 : Blo 1064615 1599467 := bstep (se 1 (by rfl) ⟨1199600, by rfl⟩ : syracuseStep 1599467 = 2399201) B2399201
theorem B4057067 : Blo 1064615 4057067 := bstep (se 1 (by rfl) ⟨3042800, by rfl⟩ : syracuseStep 4057067 = 6085601) B6085601
theorem B1599515 : Blo 1064615 1599515 := bstep (se 1 (by rfl) ⟨1199636, by rfl⟩ : syracuseStep 1599515 = 2399273) B2399273
theorem B17295707 : Blo 1064615 17295707 := bstep (se 1 (by rfl) ⟨12971780, by rfl⟩ : syracuseStep 17295707 = 25943561) B25943561
theorem B1599881 : Blo 1064615 1599881 := bstep (se 2 (by rfl) ⟨599955, by rfl⟩ : syracuseStep 1599881 = 1199911) B1199911
theorem B5401079 : Blo 1064615 5401079 := bstep (se 1 (by rfl) ⟨4050809, by rfl⟩ : syracuseStep 5401079 = 8101619) B8101619
theorem B4614803 : Blo 1064615 4614803 := bstep (se 1 (by rfl) ⟨3461102, by rfl⟩ : syracuseStep 4614803 = 6922205) B6922205
theorem B1600823 : Blo 1064615 1600823 := bstep (se 1 (by rfl) ⟨1200617, by rfl⟩ : syracuseStep 1600823 = 2401235) B2401235
theorem B1797599 : Blo 1064615 1797599 := bstep (se 1 (by rfl) ⟨1348199, by rfl⟩ : syracuseStep 1797599 = 2696399) B2696399
theorem B1600991 : Blo 1064615 1600991 := bstep (se 1 (by rfl) ⟨1200743, by rfl⟩ : syracuseStep 1600991 = 2401487) B2401487
theorem B3599963 : Blo 1064615 3599963 := bstep (se 1 (by rfl) ⟨2699972, by rfl⟩ : syracuseStep 3599963 = 5399945) B5399945
theorem B2027099 : Blo 1064615 2027099 := bstep (se 1 (by rfl) ⟨1520324, by rfl⟩ : syracuseStep 2027099 = 3040649) B3040649
theorem B1797815 : Blo 1064615 1797815 := bstep (se 1 (by rfl) ⟨1348361, by rfl⟩ : syracuseStep 1797815 = 2696723) B2696723
theorem B1601207 : Blo 1064615 1601207 := bstep (se 1 (by rfl) ⟨1200905, by rfl⟩ : syracuseStep 1601207 = 2401811) B2401811
theorem B2158331 : Blo 1064615 2158331 := bstep (se 1 (by rfl) ⟨1618748, by rfl⟩ : syracuseStep 2158331 = 3237497) B3237497
theorem B1601417 : Blo 1064615 1601417 := bstep (se 2 (by rfl) ⟨600531, by rfl⟩ : syracuseStep 1601417 = 1201063) B1201063
theorem B1601663 : Blo 1064615 1601663 := bstep (se 1 (by rfl) ⟨1201247, by rfl⟩ : syracuseStep 1601663 = 2402495) B2402495
theorem B6484121 : Blo 1064615 6484121 := bstep (se 2 (by rfl) ⟨2431545, by rfl⟩ : syracuseStep 6484121 = 4863091) B4863091
theorem B1732871 : Blo 1064615 1732871 := bstep (se 1 (by rfl) ⟨1299653, by rfl⟩ : syracuseStep 1732871 = 2599307) B2599307
theorem B3600665 : Blo 1064615 3600665 := bstep (se 2 (by rfl) ⟨1350249, by rfl⟩ : syracuseStep 3600665 = 2700499) B2700499
theorem B18248327 : Blo 1064615 18248327 := bstep (se 1 (by rfl) ⟨13686245, by rfl⟩ : syracuseStep 18248327 = 27372491) B27372491
theorem B1602299 : Blo 1064615 1602299 := bstep (se 1 (by rfl) ⟨1201724, by rfl⟩ : syracuseStep 1602299 = 2403449) B2403449
theorem B1799239 : Blo 1064615 1799239 := bstep (se 1 (by rfl) ⟨1349429, by rfl⟩ : syracuseStep 1799239 = 2698859) B2698859
theorem B1602743 : Blo 1064615 1602743 := bstep (se 1 (by rfl) ⟨1202057, by rfl⟩ : syracuseStep 1602743 = 2404115) B2404115
theorem B4551967 : Blo 1064615 4551967 := bstep (se 1 (by rfl) ⟨3413975, by rfl⟩ : syracuseStep 4551967 = 6827951) B6827951
theorem B5403995 : Blo 1064615 5403995 := bstep (se 1 (by rfl) ⟨4052996, by rfl⟩ : syracuseStep 5403995 = 8105993) B8105993
theorem B3602015 : Blo 1064615 3602015 := bstep (se 1 (by rfl) ⟨2701511, by rfl⟩ : syracuseStep 3602015 = 5403023) B5403023
theorem B6486281 : Blo 1064615 6486281 := bstep (se 2 (by rfl) ⟨2432355, by rfl⟩ : syracuseStep 6486281 = 4864711) B4864711
theorem B4618783 : Blo 1064615 4618783 := bstep (se 1 (by rfl) ⟨3464087, by rfl⟩ : syracuseStep 4618783 = 6928175) B6928175
theorem B4160105 : Blo 1064615 4160105 := bstep (se 2 (by rfl) ⟨1560039, by rfl⟩ : syracuseStep 4160105 = 3120079) B3120079
theorem B100040147 : Blo 1064615 100040147 := bstep (se 1 (by rfl) ⟨75030110, by rfl⟩ : syracuseStep 100040147 = 150060221) B150060221
theorem B8650259 : Blo 1064615 8650259 := bstep (se 1 (by rfl) ⟨6487694, by rfl⟩ : syracuseStep 8650259 = 12975389) B12975389
theorem B3604121 : Blo 1064615 3604121 := bstep (se 2 (by rfl) ⟨1351545, by rfl⟩ : syracuseStep 3604121 = 2703091) B2703091
theorem B1801993 : Blo 1064615 1801993 := bstep (se 2 (by rfl) ⟨675747, by rfl⟩ : syracuseStep 1801993 = 1351495) B1351495
theorem B8093843 : Blo 1064615 8093843 := bstep (se 1 (by rfl) ⟨6070382, by rfl⟩ : syracuseStep 8093843 = 12140765) B12140765
theorem B4620989 : Blo 1064615 4620989 := bstep (se 3 (by rfl) ⟨866435, by rfl⟩ : syracuseStep 4620989 = 1732871) B1732871
theorem B2851609 : Blo 1064615 2851609 := bstep (se 2 (by rfl) ⟨1069353, by rfl⟩ : syracuseStep 2851609 = 2138707) B2138707
theorem B6914873 : Blo 1064615 6914873 := bstep (se 2 (by rfl) ⟨2593077, by rfl⟩ : syracuseStep 6914873 = 5186155) B5186155
theorem B5407559 : Blo 1064615 5407559 := bstep (se 1 (by rfl) ⟨4055669, by rfl⟩ : syracuseStep 5407559 = 8111339) B8111339
theorem B10945367 : Blo 1064615 10945367 := bstep (se 1 (by rfl) ⟨8209025, by rfl⟩ : syracuseStep 10945367 = 16418051) B16418051
theorem B13861751 : Blo 1064615 13861751 := bstep (se 1 (by rfl) ⟨10396313, by rfl⟩ : syracuseStep 13861751 = 20792627) B20792627
theorem B16417673 : Blo 1064615 16417673 := bstep (se 2 (by rfl) ⟨6156627, by rfl⟩ : syracuseStep 16417673 = 12313255) B12313255
theorem B4555727 : Blo 1064615 4555727 := bstep (se 1 (by rfl) ⟨3416795, by rfl⟩ : syracuseStep 4555727 = 6833591) B6833591
theorem B1803215 : Blo 1064615 1803215 := bstep (se 1 (by rfl) ⟨1352411, by rfl⟩ : syracuseStep 1803215 = 2704823) B2704823
theorem B2885291 : Blo 1064615 2885291 := bstep (se 1 (by rfl) ⟨2163968, by rfl⟩ : syracuseStep 2885291 = 4327937) B4327937
theorem B1705963 : Blo 1064615 1705963 := bstep (se 1 (by rfl) ⟨1279472, by rfl⟩ : syracuseStep 1705963 = 2558945) B2558945
theorem B2164819 : Blo 1064615 2164819 := bstep (se 1 (by rfl) ⟨1623614, by rfl⟩ : syracuseStep 2164819 = 3247229) B3247229
theorem B2885863 : Blo 1064615 2885863 := bstep (se 1 (by rfl) ⟨2164397, by rfl⟩ : syracuseStep 2885863 = 4328795) B4328795
theorem B12978751 : Blo 1064615 12978751 := bstep (se 1 (by rfl) ⟨9734063, by rfl⟩ : syracuseStep 12978751 = 19468127) B19468127
theorem B8096759 : Blo 1064615 8096759 := bstep (se 1 (by rfl) ⟨6072569, by rfl⟩ : syracuseStep 8096759 = 12145139) B12145139
theorem B10259459 : Blo 1064615 10259459 := bstep (se 1 (by rfl) ⟨7694594, by rfl⟩ : syracuseStep 10259459 = 15389189) B15389189
theorem B1707239 : Blo 1064615 1707239 := bstep (se 1 (by rfl) ⟨1280429, by rfl⟩ : syracuseStep 1707239 = 2560859) B2560859
theorem B3411197 : Blo 1064615 3411197 := bstep (se 3 (by rfl) ⟨639599, by rfl⟩ : syracuseStep 3411197 = 1279199) B1279199
theorem B5771033 : Blo 1064615 5771033 := bstep (se 2 (by rfl) ⟨2164137, by rfl⟩ : syracuseStep 5771033 = 4328275) B4328275
theorem B1708295 : Blo 1064615 1708295 := bstep (se 1 (by rfl) ⟨1281221, by rfl⟩ : syracuseStep 1708295 = 2562443) B2562443
theorem B2396519 : Blo 1064615 2396519 := bstep (se 1 (by rfl) ⟨1797389, by rfl⟩ : syracuseStep 2396519 = 3594779) B3594779
theorem B9114119 : Blo 1064615 9114119 := bstep (se 1 (by rfl) ⟨6835589, by rfl⟩ : syracuseStep 9114119 = 13671179) B13671179
theorem B12129101 : Blo 1064615 12129101 := bstep (se 3 (by rfl) ⟨2274206, by rfl⟩ : syracuseStep 12129101 = 4548413) B4548413
theorem B8197355 : Blo 1064615 8197355 := bstep (se 1 (by rfl) ⟨6148016, by rfl⟩ : syracuseStep 8197355 = 12296033) B12296033
theorem B7017839 : Blo 1064615 7017839 := bstep (se 1 (by rfl) ⟨5263379, by rfl⟩ : syracuseStep 7017839 = 10526759) B10526759
theorem B7411175 : Blo 1064615 7411175 := bstep (se 1 (by rfl) ⟨5558381, by rfl⟩ : syracuseStep 7411175 = 11116763) B11116763
theorem B21861971 : Blo 1064615 21861971 := bstep (se 1 (by rfl) ⟨16396478, by rfl⟩ : syracuseStep 21861971 = 32792957) B32792957
theorem B3413657 : Blo 1064615 3413657 := bstep (se 2 (by rfl) ⟨1280121, by rfl⟩ : syracuseStep 3413657 = 2560243) B2560243
theorem B5118025 : Blo 1064615 5118025 := bstep (se 2 (by rfl) ⟨1919259, by rfl⟩ : syracuseStep 5118025 = 3838519) B3838519
theorem B2398823 : Blo 1064615 2398823 := bstep (se 1 (by rfl) ⟨1799117, by rfl⟩ : syracuseStep 2398823 = 3598235) B3598235
theorem B15571561 : Blo 1064615 15571561 := bstep (se 2 (by rfl) ⟨5839335, by rfl⟩ : syracuseStep 15571561 = 11678671) B11678671
theorem B4561535 : Blo 1064615 4561535 := bstep (se 1 (by rfl) ⟨3421151, by rfl⟩ : syracuseStep 4561535 = 6842303) B6842303
theorem B2398985 : Blo 1064615 2398985 := bstep (se 2 (by rfl) ⟨899619, by rfl⟩ : syracuseStep 2398985 = 1799239) B1799239
theorem B2562857 : Blo 1064615 2562857 := bstep (se 2 (by rfl) ⟨961071, by rfl⟩ : syracuseStep 2562857 = 1922143) B1922143
theorem B6069289 : Blo 1064615 6069289 := bstep (se 2 (by rfl) ⟨2275983, by rfl⟩ : syracuseStep 6069289 = 4551967) B4551967
theorem B131439793 : Blo 1064615 131439793 := bstep (se 2 (by rfl) ⟨49289922, by rfl⟩ : syracuseStep 131439793 = 98579845) B98579845
theorem B6495527 : Blo 1064615 6495527 := bstep (se 1 (by rfl) ⟨4871645, by rfl⟩ : syracuseStep 6495527 = 9743291) B9743291
theorem B2399975 : Blo 1064615 2399975 := bstep (se 1 (by rfl) ⟨1799981, by rfl⟩ : syracuseStep 2399975 = 3599963) B3599963
theorem B1351399 : Blo 1064615 1351399 := bstep (se 1 (by rfl) ⟨1013549, by rfl⟩ : syracuseStep 1351399 = 2027099) B2027099
theorem B2694991 : Blo 1064615 2694991 := bstep (se 1 (by rfl) ⟨2021243, by rfl⟩ : syracuseStep 2694991 = 4042487) B4042487
theorem B170532965 : Blo 1064615 170532965 := bstep (se 4 (by rfl) ⟨15987465, by rfl⟩ : syracuseStep 170532965 = 31974931) B31974931
theorem B9248897 : Blo 1064615 9248897 := bstep (se 2 (by rfl) ⟨3468336, by rfl⟩ : syracuseStep 9248897 = 6936673) B6936673
theorem B2400443 : Blo 1064615 2400443 := bstep (se 1 (by rfl) ⟨1800332, by rfl⟩ : syracuseStep 2400443 = 3600665) B3600665
theorem B12165551 : Blo 1064615 12165551 := bstep (se 1 (by rfl) ⟨9124163, by rfl⟩ : syracuseStep 12165551 = 18248327) B18248327
theorem B2695639 : Blo 1064615 2695639 := bstep (se 1 (by rfl) ⟨2021729, by rfl⟩ : syracuseStep 2695639 = 4043459) B4043459
theorem B22487827 : Blo 1064615 22487827 := bstep (se 1 (by rfl) ⟨16865870, by rfl⟩ : syracuseStep 22487827 = 33731741) B33731741
theorem B77800337 : Blo 1064615 77800337 := bstep (se 2 (by rfl) ⟨29175126, by rfl⟩ : syracuseStep 77800337 = 58350253) B58350253
theorem B2401343 : Blo 1064615 2401343 := bstep (se 1 (by rfl) ⟨1801007, by rfl⟩ : syracuseStep 2401343 = 3602015) B3602015
theorem B1516639 : Blo 1064615 1516639 := bstep (se 1 (by rfl) ⟨1137479, by rfl⟩ : syracuseStep 1516639 = 2274959) B2274959
theorem B2696287 : Blo 1064615 2696287 := bstep (se 1 (by rfl) ⟨2022215, by rfl⟩ : syracuseStep 2696287 = 4044431) B4044431
theorem B66693431 : Blo 1064615 66693431 := bstep (se 1 (by rfl) ⟨50020073, by rfl⟩ : syracuseStep 66693431 = 100040147) B100040147
theorem B2402657 : Blo 1064615 2402657 := bstep (se 2 (by rfl) ⟨900996, by rfl⟩ : syracuseStep 2402657 = 1801993) B1801993
theorem B2402747 : Blo 1064615 2402747 := bstep (se 1 (by rfl) ⟨1802060, by rfl⟩ : syracuseStep 2402747 = 3604121) B3604121
theorem B2566633 : Blo 1064615 2566633 := bstep (se 2 (by rfl) ⟨962487, by rfl⟩ : syracuseStep 2566633 = 1924975) B1924975
theorem B4860755 : Blo 1064615 4860755 := bstep (se 1 (by rfl) ⟨3645566, by rfl⟩ : syracuseStep 4860755 = 7291133) B7291133
theorem B4926347 : Blo 1064615 4926347 := bstep (se 1 (by rfl) ⟨3694760, by rfl⟩ : syracuseStep 4926347 = 7389521) B7389521
theorem B2403539 : Blo 1064615 2403539 := bstep (se 1 (by rfl) ⟨1802654, by rfl⟩ : syracuseStep 2403539 = 3605309) B3605309
theorem B12168467 : Blo 1064615 12168467 := bstep (se 1 (by rfl) ⟨9126350, by rfl⟩ : syracuseStep 12168467 = 18252701) B18252701
theorem B9121157 : Blo 1064615 9121157 := bstep (se 4 (by rfl) ⟨855108, by rfl⟩ : syracuseStep 9121157 = 1710217) B1710217
theorem B2403809 : Blo 1064615 2403809 := bstep (se 2 (by rfl) ⟨901428, by rfl⟩ : syracuseStep 2403809 = 1802857) B1802857
theorem B2404007 : Blo 1064615 2404007 := bstep (se 1 (by rfl) ⟨1803005, by rfl⟩ : syracuseStep 2404007 = 3606011) B3606011
theorem B13643963 : Blo 1064615 13643963 := bstep (se 1 (by rfl) ⟨10232972, by rfl⟩ : syracuseStep 13643963 = 20465945) B20465945
theorem B6074621 : Blo 1064615 6074621 := bstep (se 3 (by rfl) ⟨1138991, by rfl⟩ : syracuseStep 6074621 = 2277983) B2277983
theorem B41628277 : Blo 1064615 41628277 := bstep (se 5 (by rfl) ⟨1951325, by rfl⟩ : syracuseStep 41628277 = 3902651) B3902651
theorem B1521127 : Blo 1064615 1521127 := bstep (se 1 (by rfl) ⟨1140845, by rfl⟩ : syracuseStep 1521127 = 2281691) B2281691
theorem B7682111 : Blo 1064615 7682111 := bstep (se 1 (by rfl) ⟨5761583, by rfl⟩ : syracuseStep 7682111 = 11523167) B11523167
theorem B12171383 : Blo 1064615 12171383 := bstep (se 1 (by rfl) ⟨9128537, by rfl⟩ : syracuseStep 12171383 = 18257075) B18257075
theorem B4045403 : Blo 1064615 4045403 := bstep (se 1 (by rfl) ⟨3034052, by rfl⟩ : syracuseStep 4045403 = 6068105) B6068105
theorem B3423305 : Blo 1064615 3423305 := bstep (se 2 (by rfl) ⟨1283739, by rfl⟩ : syracuseStep 3423305 = 2567479) B2567479
theorem B73776365 : Blo 1064615 73776365 := bstep (se 3 (by rfl) ⟨13833068, by rfl⟩ : syracuseStep 73776365 = 27666137) B27666137
theorem B199900547 : Blo 1064615 199900547 := bstep (se 1 (by rfl) ⟨149925410, by rfl⟩ : syracuseStep 199900547 = 299850821) B299850821
theorem B5127731 : Blo 1064615 5127731 := bstep (se 1 (by rfl) ⟨3845798, by rfl⟩ : syracuseStep 5127731 = 7691597) B7691597
theorem B1064699 : Blo 1064615 1064699 := bstep (se 1 (by rfl) ⟨798524, by rfl⟩ : syracuseStep 1064699 = 1597049) B1597049
theorem B1064863 : Blo 1064615 1064863 := bstep (se 1 (by rfl) ⟨798647, by rfl⟩ : syracuseStep 1064863 = 1597295) B1597295
theorem B1949779 : Blo 1064615 1949779 := bstep (se 1 (by rfl) ⟨1462334, by rfl⟩ : syracuseStep 1949779 = 2924669) B2924669
theorem B1065319 : Blo 1064615 1065319 := bstep (se 1 (by rfl) ⟨798989, by rfl⟩ : syracuseStep 1065319 = 1597979) B1597979
theorem B2703719 : Blo 1064615 2703719 := bstep (se 1 (by rfl) ⟨2027789, by rfl⟩ : syracuseStep 2703719 = 4055579) B4055579
theorem B1065439 : Blo 1064615 1065439 := bstep (se 1 (by rfl) ⟨799079, by rfl⟩ : syracuseStep 1065439 = 1598159) B1598159
theorem B1065447 : Blo 1064615 1065447 := bstep (se 1 (by rfl) ⟨799085, by rfl⟩ : syracuseStep 1065447 = 1598171) B1598171
theorem B6078995 : Blo 1064615 6078995 := bstep (se 1 (by rfl) ⟨4559246, by rfl⟩ : syracuseStep 6078995 = 9118493) B9118493
theorem B5391035 : Blo 1064615 5391035 := bstep (se 1 (by rfl) ⟨4043276, by rfl⟩ : syracuseStep 5391035 = 8086553) B8086553
theorem B1065723 : Blo 1064615 1065723 := bstep (se 1 (by rfl) ⟨799292, by rfl⟩ : syracuseStep 1065723 = 1598585) B1598585
theorem B46121885 : Blo 1064615 46121885 := bstep (se 3 (by rfl) ⟨8647853, by rfl⟩ : syracuseStep 46121885 = 17295707) B17295707
theorem B1066303 : Blo 1064615 1066303 := bstep (se 1 (by rfl) ⟨799727, by rfl⟩ : syracuseStep 1066303 = 1599455) B1599455
theorem B1066311 : Blo 1064615 1066311 := bstep (se 1 (by rfl) ⟨799733, by rfl⟩ : syracuseStep 1066311 = 1599467) B1599467
theorem B2704711 : Blo 1064615 2704711 := bstep (se 1 (by rfl) ⟨2028533, by rfl⟩ : syracuseStep 2704711 = 4057067) B4057067
theorem B1066343 : Blo 1064615 1066343 := bstep (se 1 (by rfl) ⟨799757, by rfl⟩ : syracuseStep 1066343 = 1599515) B1599515
theorem B87606805 : Blo 1064615 87606805 := bstep (se 6 (by rfl) ⟨2053284, by rfl⟩ : syracuseStep 87606805 = 4106569) B4106569
theorem B1066587 : Blo 1064615 1066587 := bstep (se 1 (by rfl) ⟨799940, by rfl⟩ : syracuseStep 1066587 = 1599881) B1599881
theorem B19449497 : Blo 1064615 19449497 := bstep (se 2 (by rfl) ⟨7293561, by rfl⟩ : syracuseStep 19449497 = 14587123) B14587123
theorem B1067215 : Blo 1064615 1067215 := bstep (se 1 (by rfl) ⟨800411, by rfl⟩ : syracuseStep 1067215 = 1600823) B1600823
theorem B1198399 : Blo 1064615 1198399 := bstep (se 1 (by rfl) ⟨898799, by rfl⟩ : syracuseStep 1198399 = 1797599) B1797599
theorem B1067327 : Blo 1064615 1067327 := bstep (se 1 (by rfl) ⟨800495, by rfl⟩ : syracuseStep 1067327 = 1600991) B1600991
theorem B1198543 : Blo 1064615 1198543 := bstep (se 1 (by rfl) ⟨898907, by rfl⟩ : syracuseStep 1198543 = 1797815) B1797815
theorem B1067471 : Blo 1064615 1067471 := bstep (se 1 (by rfl) ⟨800603, by rfl⟩ : syracuseStep 1067471 = 1601207) B1601207
theorem B1067611 : Blo 1064615 1067611 := bstep (se 1 (by rfl) ⟨800708, by rfl⟩ : syracuseStep 1067611 = 1601417) B1601417
theorem B1067775 : Blo 1064615 1067775 := bstep (se 1 (by rfl) ⟨800831, by rfl⟩ : syracuseStep 1067775 = 1601663) B1601663
theorem B8637191 : Blo 1064615 8637191 := bstep (se 1 (by rfl) ⟨6477893, by rfl⟩ : syracuseStep 8637191 = 12955787) B12955787
theorem B1068199 : Blo 1064615 1068199 := bstep (se 1 (by rfl) ⟨801149, by rfl⟩ : syracuseStep 1068199 = 1602299) B1602299
theorem B1068495 : Blo 1064615 1068495 := bstep (se 1 (by rfl) ⟨801371, by rfl⟩ : syracuseStep 1068495 = 1602743) B1602743
theorem B6082411 : Blo 1064615 6082411 := bstep (se 1 (by rfl) ⟨4561808, by rfl⟩ : syracuseStep 6082411 = 9123617) B9123617
theorem B6148219 : Blo 1064615 6148219 := bstep (se 1 (by rfl) ⟨4611164, by rfl⟩ : syracuseStep 6148219 = 9222329) B9222329
theorem B2773403 : Blo 1064615 2773403 := bstep (se 1 (by rfl) ⟨2080052, by rfl⟩ : syracuseStep 2773403 = 4160105) B4160105
theorem B5755549 : Blo 1064615 5755549 := bstep (se 3 (by rfl) ⟨1079165, by rfl⟩ : syracuseStep 5755549 = 2158331) B2158331
theorem B5624657 : Blo 1064615 5624657 := bstep (se 2 (by rfl) ⟨2109246, by rfl⟩ : syracuseStep 5624657 = 4218493) B4218493
theorem B3593213 : Blo 1064615 3593213 := bstep (se 3 (by rfl) ⟨673727, by rfl⟩ : syracuseStep 3593213 = 1347455) B1347455
theorem B6837641 : Blo 1064615 6837641 := bstep (se 2 (by rfl) ⟨2564115, by rfl⟩ : syracuseStep 6837641 = 5128231) B5128231
theorem B1201855 : Blo 1064615 1201855 := bstep (se 1 (by rfl) ⟨901391, by rfl⟩ : syracuseStep 1201855 = 1802783) B1802783
theorem B20502305 : Blo 1064615 20502305 := bstep (se 2 (by rfl) ⟨7688364, by rfl⟩ : syracuseStep 20502305 = 15376729) B15376729
theorem B6838667 : Blo 1064615 6838667 := bstep (se 1 (by rfl) ⟨5129000, by rfl⟩ : syracuseStep 6838667 = 10258001) B10258001
theorem B2022079 : Blo 1064615 2022079 := bstep (se 1 (by rfl) ⟨1516559, by rfl⟩ : syracuseStep 2022079 = 3033119) B3033119
theorem B3037949 : Blo 1064615 3037949 := bstep (se 3 (by rfl) ⟨569615, by rfl⟩ : syracuseStep 3037949 = 1139231) B1139231
theorem B25942787 : Blo 1064615 25942787 := bstep (se 1 (by rfl) ⟨19457090, by rfl⟩ : syracuseStep 25942787 = 38914181) B38914181
theorem B4054151 : Blo 1064615 4054151 := bstep (se 1 (by rfl) ⟨3040613, by rfl⟩ : syracuseStep 4054151 = 6081227) B6081227
theorem B3595643 : Blo 1064615 3595643 := bstep (se 1 (by rfl) ⟨2696732, by rfl⟩ : syracuseStep 3595643 = 5393465) B5393465
theorem B1597151 : Blo 1064615 1597151 := bstep (se 1 (by rfl) ⟨1197863, by rfl⟩ : syracuseStep 1597151 = 2395727) B2395727
theorem B1924831 : Blo 1064615 1924831 := bstep (se 1 (by rfl) ⟨1443623, by rfl⟩ : syracuseStep 1924831 = 2887247) B2887247
theorem B3596129 : Blo 1064615 3596129 := bstep (se 2 (by rfl) ⟨1348548, by rfl⟩ : syracuseStep 3596129 = 2697097) B2697097
theorem B1597481 : Blo 1064615 1597481 := bstep (se 2 (by rfl) ⟨599055, by rfl⟩ : syracuseStep 1597481 = 1198111) B1198111
theorem B1597511 : Blo 1064615 1597511 := bstep (se 1 (by rfl) ⟨1198133, by rfl⟩ : syracuseStep 1597511 = 2396267) B2396267
theorem B1597547 : Blo 1064615 1597547 := bstep (se 1 (by rfl) ⟨1198160, by rfl⟩ : syracuseStep 1597547 = 2396321) B2396321
theorem B1597631 : Blo 1064615 1597631 := bstep (se 1 (by rfl) ⟨1198223, by rfl⟩ : syracuseStep 1597631 = 2396447) B2396447
theorem B1597817 : Blo 1064615 1597817 := bstep (se 2 (by rfl) ⟨599181, by rfl⟩ : syracuseStep 1597817 = 1198363) B1198363
theorem B5398973 : Blo 1064615 5398973 := bstep (se 3 (by rfl) ⟨1012307, by rfl⟩ : syracuseStep 5398973 = 2024615) B2024615
theorem B9232993 : Blo 1064615 9232993 := bstep (se 2 (by rfl) ⟨3462372, by rfl⟩ : syracuseStep 9232993 = 6924745) B6924745
theorem B1598111 : Blo 1064615 1598111 := bstep (se 1 (by rfl) ⟨1198583, by rfl⟩ : syracuseStep 1598111 = 2397167) B2397167
theorem B3597047 : Blo 1064615 3597047 := bstep (se 1 (by rfl) ⟨2697785, by rfl⟩ : syracuseStep 3597047 = 5395571) B5395571
theorem B1368991 : Blo 1064615 1368991 := bstep (se 1 (by rfl) ⟨1026743, by rfl⟩ : syracuseStep 1368991 = 2053487) B2053487
theorem B1598447 : Blo 1064615 1598447 := bstep (se 1 (by rfl) ⟨1198835, by rfl⟩ : syracuseStep 1598447 = 2397671) B2397671
theorem B1598555 : Blo 1064615 1598555 := bstep (se 1 (by rfl) ⟨1198916, by rfl⟩ : syracuseStep 1598555 = 2397833) B2397833
theorem B1598567 : Blo 1064615 1598567 := bstep (se 1 (by rfl) ⟨1198925, by rfl⟩ : syracuseStep 1598567 = 2397851) B2397851
theorem B1598699 : Blo 1064615 1598699 := bstep (se 1 (by rfl) ⟨1199024, by rfl⟩ : syracuseStep 1598699 = 2398049) B2398049
theorem B3597587 : Blo 1064615 3597587 := bstep (se 1 (by rfl) ⟨2698190, by rfl⟩ : syracuseStep 3597587 = 5396381) B5396381
theorem B3040591 : Blo 1064615 3040591 := bstep (se 1 (by rfl) ⟨2280443, by rfl⟩ : syracuseStep 3040591 = 4560887) B4560887
theorem B1598831 : Blo 1064615 1598831 := bstep (se 1 (by rfl) ⟨1199123, by rfl⟩ : syracuseStep 1598831 = 2398247) B2398247
theorem B1598951 : Blo 1064615 1598951 := bstep (se 1 (by rfl) ⟨1199213, by rfl⟩ : syracuseStep 1598951 = 2398427) B2398427
theorem B4056551 : Blo 1064615 4056551 := bstep (se 1 (by rfl) ⟨3042413, by rfl⟩ : syracuseStep 4056551 = 6084827) B6084827
theorem B1599083 : Blo 1064615 1599083 := bstep (se 1 (by rfl) ⟨1199312, by rfl⟩ : syracuseStep 1599083 = 2398625) B2398625
theorem B1599131 : Blo 1064615 1599131 := bstep (se 1 (by rfl) ⟨1199348, by rfl⟩ : syracuseStep 1599131 = 2398697) B2398697
theorem B3598127 : Blo 1064615 3598127 := bstep (se 1 (by rfl) ⟨2698595, by rfl⟩ : syracuseStep 3598127 = 5397191) B5397191
theorem B1599353 : Blo 1064615 1599353 := bstep (se 2 (by rfl) ⟨599757, by rfl⟩ : syracuseStep 1599353 = 1199515) B1199515
theorem B2025337 : Blo 1064615 2025337 := bstep (se 2 (by rfl) ⟨759501, by rfl⟩ : syracuseStep 2025337 = 1519003) B1519003
theorem B4319291 : Blo 1064615 4319291 := bstep (se 1 (by rfl) ⟨3239468, by rfl⟩ : syracuseStep 4319291 = 6478937) B6478937
theorem B3041479 : Blo 1064615 3041479 := bstep (se 1 (by rfl) ⟨2281109, by rfl⟩ : syracuseStep 3041479 = 4562219) B4562219
theorem B44329193 : Blo 1064615 44329193 := bstep (se 2 (by rfl) ⟨16623447, by rfl⟩ : syracuseStep 44329193 = 33246895) B33246895
theorem B1600103 : Blo 1064615 1600103 := bstep (se 1 (by rfl) ⟨1200077, by rfl⟩ : syracuseStep 1600103 = 2400155) B2400155
theorem B5401241 : Blo 1064615 5401241 := bstep (se 2 (by rfl) ⟨2025465, by rfl⟩ : syracuseStep 5401241 = 4050931) B4050931
theorem B1600379 : Blo 1064615 1600379 := bstep (se 1 (by rfl) ⟨1200284, by rfl⟩ : syracuseStep 1600379 = 2400569) B2400569
theorem B3042299 : Blo 1064615 3042299 := bstep (se 1 (by rfl) ⟨2281724, by rfl⟩ : syracuseStep 3042299 = 4563449) B4563449
theorem B1600649 : Blo 1064615 1600649 := bstep (se 2 (by rfl) ⟨600243, by rfl⟩ : syracuseStep 1600649 = 1200487) B1200487
theorem B1797295 : Blo 1064615 1797295 := bstep (se 1 (by rfl) ⟨1347971, by rfl⟩ : syracuseStep 1797295 = 2695943) B2695943
theorem B1600703 : Blo 1064615 1600703 := bstep (se 1 (by rfl) ⟨1200527, by rfl⟩ : syracuseStep 1600703 = 2401055) B2401055
theorem B1601243 : Blo 1064615 1601243 := bstep (se 1 (by rfl) ⟨1200932, by rfl⟩ : syracuseStep 1601243 = 2401865) B2401865
theorem B3600125 : Blo 1064615 3600125 := bstep (se 3 (by rfl) ⟨675023, by rfl⟩ : syracuseStep 3600125 = 1350047) B1350047
theorem B1601513 : Blo 1064615 1601513 := bstep (se 2 (by rfl) ⟨600567, by rfl⟩ : syracuseStep 1601513 = 1201135) B1201135
theorem B1601531 : Blo 1064615 1601531 := bstep (se 1 (by rfl) ⟨1201148, by rfl⟩ : syracuseStep 1601531 = 2402297) B2402297
theorem B1601567 : Blo 1064615 1601567 := bstep (se 1 (by rfl) ⟨1201175, by rfl⟩ : syracuseStep 1601567 = 2402351) B2402351
theorem B1601591 : Blo 1064615 1601591 := bstep (se 1 (by rfl) ⟨1201193, by rfl⟩ : syracuseStep 1601591 = 2402387) B2402387
theorem B1601711 : Blo 1064615 1601711 := bstep (se 1 (by rfl) ⟨1201283, by rfl⟩ : syracuseStep 1601711 = 2402567) B2402567
theorem B3600719 : Blo 1064615 3600719 := bstep (se 1 (by rfl) ⟨2700539, by rfl⟩ : syracuseStep 3600719 = 5401079) B5401079
theorem B1601915 : Blo 1064615 1601915 := bstep (se 1 (by rfl) ⟨1201436, by rfl⟩ : syracuseStep 1601915 = 2402873) B2402873
theorem B3076535 : Blo 1064615 3076535 := bstep (se 1 (by rfl) ⟨2307401, by rfl⟩ : syracuseStep 3076535 = 4614803) B4614803
theorem B1602185 : Blo 1064615 1602185 := bstep (se 2 (by rfl) ⟨600819, by rfl⟩ : syracuseStep 1602185 = 1201639) B1201639
theorem B9106121 : Blo 1064615 9106121 := bstep (se 2 (by rfl) ⟨3414795, by rfl⟩ : syracuseStep 9106121 = 6829591) B6829591
theorem B1799003 : Blo 1064615 1799003 := bstep (se 1 (by rfl) ⟨1349252, by rfl⟩ : syracuseStep 1799003 = 2698505) B2698505
theorem B1602395 : Blo 1064615 1602395 := bstep (se 1 (by rfl) ⟨1201796, by rfl⟩ : syracuseStep 1602395 = 2403593) B2403593
theorem B1602425 : Blo 1064615 1602425 := bstep (se 2 (by rfl) ⟨600909, by rfl⟩ : syracuseStep 1602425 = 1201819) B1201819
theorem B1733753 : Blo 1064615 1733753 := bstep (se 2 (by rfl) ⟨650157, by rfl⟩ : syracuseStep 1733753 = 1300315) B1300315
theorem B4322747 : Blo 1064615 4322747 := bstep (se 1 (by rfl) ⟨3242060, by rfl⟩ : syracuseStep 4322747 = 6484121) B6484121
theorem B23099003 : Blo 1064615 23099003 := bstep (se 1 (by rfl) ⟨17324252, by rfl⟩ : syracuseStep 23099003 = 34648505) B34648505
theorem B6158377 : Blo 1064615 6158377 := bstep (se 2 (by rfl) ⟨2309391, by rfl⟩ : syracuseStep 6158377 = 4618783) B4618783
theorem B2816041 : Blo 1064615 2816041 := bstep (se 2 (by rfl) ⟨1056015, by rfl⟩ : syracuseStep 2816041 = 2112031) B2112031
theorem B3602663 : Blo 1064615 3602663 := bstep (se 1 (by rfl) ⟨2701997, by rfl⟩ : syracuseStep 3602663 = 5403995) B5403995
theorem B5404967 : Blo 1064615 5404967 := bstep (se 1 (by rfl) ⟨4053725, by rfl⟩ : syracuseStep 5404967 = 8107451) B8107451
theorem B1800697 : Blo 1064615 1800697 := bstep (se 2 (by rfl) ⟨675261, by rfl⟩ : syracuseStep 1800697 = 1350523) B1350523
theorem B1800967 : Blo 1064615 1800967 := bstep (se 1 (by rfl) ⟨1350725, by rfl⟩ : syracuseStep 1800967 = 2701451) B2701451
theorem B4324187 : Blo 1064615 4324187 := bstep (se 1 (by rfl) ⟨3243140, by rfl⟩ : syracuseStep 4324187 = 6486281) B6486281
theorem B8092871 : Blo 1064615 8092871 := bstep (se 1 (by rfl) ⟨6069653, by rfl⟩ : syracuseStep 8092871 = 12139307) B12139307
theorem B5766839 : Blo 1064615 5766839 := bstep (se 1 (by rfl) ⟨4325129, by rfl⟩ : syracuseStep 5766839 = 8650259) B8650259
theorem B1802047 : Blo 1064615 1802047 := bstep (se 1 (by rfl) ⟨1351535, by rfl⟩ : syracuseStep 1802047 = 2703071) B2703071
theorem B1802479 : Blo 1064615 1802479 := bstep (se 1 (by rfl) ⟨1351859, by rfl⟩ : syracuseStep 1802479 = 2703719) B2703719
theorem B3605039 : Blo 1064615 3605039 := bstep (se 1 (by rfl) ⟨2703779, by rfl⟩ : syracuseStep 3605039 = 5407559) B5407559
theorem B10945115 : Blo 1064615 10945115 := bstep (se 1 (by rfl) ⟨8208836, by rfl⟩ : syracuseStep 10945115 = 16417673) B16417673
theorem B4555453 : Blo 1064615 4555453 := bstep (se 3 (by rfl) ⟨854147, by rfl⟩ : syracuseStep 4555453 = 1708295) B1708295
theorem B29983769 : Blo 1064615 29983769 := bstep (se 2 (by rfl) ⟨11243913, by rfl⟩ : syracuseStep 29983769 = 22487827) B22487827
theorem B3802145 : Blo 1064615 3802145 := bstep (se 2 (by rfl) ⟨1425804, by rfl⟩ : syracuseStep 3802145 = 2851609) B2851609
theorem B3606281 : Blo 1064615 3606281 := bstep (se 2 (by rfl) ⟨1352355, by rfl⟩ : syracuseStep 3606281 = 2704711) B2704711
theorem B12322637 : Blo 1064615 12322637 := bstep (se 3 (by rfl) ⟨2310494, by rfl⟩ : syracuseStep 12322637 = 4620989) B4620989
theorem B36964669 : Blo 1064615 36964669 := bstep (se 3 (by rfl) ⟨6930875, by rfl⟩ : syracuseStep 36964669 = 13861751) B13861751
theorem B2886425 : Blo 1064615 2886425 := bstep (se 2 (by rfl) ⟨1082409, by rfl⟩ : syracuseStep 2886425 = 2164819) B2164819
theorem B2395475 : Blo 1064615 2395475 := bstep (se 1 (by rfl) ⟨1796606, by rfl⟩ : syracuseStep 2395475 = 3593213) B3593213
theorem B17305001 : Blo 1064615 17305001 := bstep (se 2 (by rfl) ⟨6489375, by rfl⟩ : syracuseStep 17305001 = 12978751) B12978751
theorem B4558427 : Blo 1064615 4558427 := bstep (se 1 (by rfl) ⟨3418820, by rfl⟩ : syracuseStep 4558427 = 6837641) B6837641
theorem B13668203 : Blo 1064615 13668203 := bstep (se 1 (by rfl) ⟨10251152, by rfl⟩ : syracuseStep 13668203 = 20502305) B20502305
theorem B2396393 : Blo 1064615 2396393 := bstep (se 2 (by rfl) ⟨898647, by rfl⟩ : syracuseStep 2396393 = 1797295) B1797295
theorem B4559111 : Blo 1064615 4559111 := bstep (se 1 (by rfl) ⟨3419333, by rfl⟩ : syracuseStep 4559111 = 6838667) B6838667
theorem B1708571 : Blo 1064615 1708571 := bstep (se 1 (by rfl) ⟨1281428, by rfl⟩ : syracuseStep 1708571 = 2562857) B2562857
theorem B4330351 : Blo 1064615 4330351 := bstep (se 1 (by rfl) ⟨3247763, by rfl⟩ : syracuseStep 4330351 = 6495527) B6495527
theorem B2397095 : Blo 1064615 2397095 := bstep (se 1 (by rfl) ⟨1797821, by rfl⟩ : syracuseStep 2397095 = 3595643) B3595643
theorem B2397419 : Blo 1064615 2397419 := bstep (se 1 (by rfl) ⟨1798064, by rfl⟩ : syracuseStep 2397419 = 3596129) B3596129
theorem B6165931 : Blo 1064615 6165931 := bstep (se 1 (by rfl) ⟨4624448, by rfl⟩ : syracuseStep 6165931 = 9248897) B9248897
theorem B8197625 : Blo 1064615 8197625 := bstep (se 2 (by rfl) ⟨3074109, by rfl⟩ : syracuseStep 8197625 = 6148219) B6148219
theorem B2398031 : Blo 1064615 2398031 := bstep (se 1 (by rfl) ⟨1798523, by rfl⟩ : syracuseStep 2398031 = 3597047) B3597047
theorem B2398391 : Blo 1064615 2398391 := bstep (se 1 (by rfl) ⟨1798793, by rfl⟩ : syracuseStep 2398391 = 3597587) B3597587
theorem B7674065 : Blo 1064615 7674065 := bstep (se 2 (by rfl) ⟨2877774, by rfl⟩ : syracuseStep 7674065 = 5755549) B5755549
theorem B2398751 : Blo 1064615 2398751 := bstep (se 1 (by rfl) ⟨1799063, by rfl⟩ : syracuseStep 2398751 = 3598127) B3598127
theorem B12164093 : Blo 1064615 12164093 := bstep (se 3 (by rfl) ⟨2280767, by rfl⟩ : syracuseStep 12164093 = 4561535) B4561535
theorem B3284231 : Blo 1064615 3284231 := bstep (se 1 (by rfl) ⟨2463173, by rfl⟩ : syracuseStep 3284231 = 4926347) B4926347
theorem B2400083 : Blo 1064615 2400083 := bstep (se 1 (by rfl) ⟨1800062, by rfl⟩ : syracuseStep 2400083 = 3600125) B3600125
theorem B6824033 : Blo 1064615 6824033 := bstep (se 2 (by rfl) ⟨2559012, by rfl⟩ : syracuseStep 6824033 = 5118025) B5118025
theorem B2400479 : Blo 1064615 2400479 := bstep (se 1 (by rfl) ⟨1800359, by rfl⟩ : syracuseStep 2400479 = 3600719) B3600719
theorem B6070747 : Blo 1064615 6070747 := bstep (se 1 (by rfl) ⟨4553060, by rfl⟩ : syracuseStep 6070747 = 9106121) B9106121
theorem B2400929 : Blo 1064615 2400929 := bstep (se 2 (by rfl) ⟨900348, by rfl⟩ : syracuseStep 2400929 = 1800697) B1800697
theorem B1155835 : Blo 1064615 1155835 := bstep (se 1 (by rfl) ⟨866876, by rfl⟩ : syracuseStep 1155835 = 1733753) B1733753
theorem B2696105 : Blo 1064615 2696105 := bstep (se 2 (by rfl) ⟨1011039, by rfl⟩ : syracuseStep 2696105 = 2022079) B2022079
theorem B2401289 : Blo 1064615 2401289 := bstep (se 2 (by rfl) ⟨900483, by rfl⟩ : syracuseStep 2401289 = 1800967) B1800967
theorem B5121407 : Blo 1064615 5121407 := bstep (se 1 (by rfl) ⟨3841055, by rfl⟩ : syracuseStep 5121407 = 7682111) B7682111
theorem B2401775 : Blo 1064615 2401775 := bstep (se 1 (by rfl) ⟨1801331, by rfl⟩ : syracuseStep 2401775 = 3602663) B3602663
theorem B175253057 : Blo 1064615 175253057 := bstep (se 2 (by rfl) ⟨65719896, by rfl⟩ : syracuseStep 175253057 = 131439793) B131439793
theorem B2696935 : Blo 1064615 2696935 := bstep (se 1 (by rfl) ⟨2022701, by rfl⟩ : syracuseStep 2696935 = 4045403) B4045403
theorem B2566441 : Blo 1064615 2566441 := bstep (se 2 (by rfl) ⟨962415, by rfl⟩ : syracuseStep 2566441 = 1924831) B1924831
theorem B3418487 : Blo 1064615 3418487 := bstep (se 1 (by rfl) ⟨2563865, by rfl⟩ : syracuseStep 3418487 = 5127731) B5127731
theorem B2402729 : Blo 1064615 2402729 := bstep (se 2 (by rfl) ⟨901023, by rfl⟩ : syracuseStep 2402729 = 1802047) B1802047
theorem B3844559 : Blo 1064615 3844559 := bstep (se 1 (by rfl) ⟨2883419, by rfl⟩ : syracuseStep 3844559 = 5766839) B5766839
theorem B2599705 : Blo 1064615 2599705 := bstep (se 2 (by rfl) ⟨974889, by rfl⟩ : syracuseStep 2599705 = 1949779) B1949779
theorem B30747923 : Blo 1064615 30747923 := bstep (se 1 (by rfl) ⟨23060942, by rfl⟩ : syracuseStep 30747923 = 46121885) B46121885
theorem B2274131 : Blo 1064615 2274131 := bstep (se 1 (by rfl) ⟨1705598, by rfl⟩ : syracuseStep 2274131 = 3411197) B3411197
theorem B2700449 : Blo 1064615 2700449 := bstep (se 2 (by rfl) ⟨1012668, by rfl⟩ : syracuseStep 2700449 = 2025337) B2025337
theorem B3847355 : Blo 1064615 3847355 := bstep (se 1 (by rfl) ⟨2885516, by rfl⟩ : syracuseStep 3847355 = 5771033) B5771033
theorem B2274617 : Blo 1064615 2274617 := bstep (se 2 (by rfl) ⟨852981, by rfl⟩ : syracuseStep 2274617 = 1705963) B1705963
theorem B1848935 : Blo 1064615 1848935 := bstep (se 1 (by rfl) ⟨1386701, by rfl⟩ : syracuseStep 1848935 = 2773403) B2773403
theorem B3847817 : Blo 1064615 3847817 := bstep (se 2 (by rfl) ⟨1442931, by rfl⟩ : syracuseStep 3847817 = 2885863) B2885863
theorem B6076079 : Blo 1064615 6076079 := bstep (se 1 (by rfl) ⟨4557059, by rfl⟩ : syracuseStep 6076079 = 9114119) B9114119
theorem B3749771 : Blo 1064615 3749771 := bstep (se 1 (by rfl) ⟨2812328, by rfl⟩ : syracuseStep 3749771 = 5624657) B5624657
theorem B3422177 : Blo 1064615 3422177 := bstep (se 2 (by rfl) ⟨1283316, by rfl⟩ : syracuseStep 3422177 = 2566633) B2566633
theorem B2275771 : Blo 1064615 2275771 := bstep (se 1 (by rfl) ⟨1706828, by rfl⟩ : syracuseStep 2275771 = 3413657) B3413657
theorem B2702767 : Blo 1064615 2702767 := bstep (se 1 (by rfl) ⟨2027075, by rfl⟩ : syracuseStep 2702767 = 4054151) B4054151
theorem B8109881 : Blo 1064615 8109881 := bstep (se 2 (by rfl) ⟨3041205, by rfl⟩ : syracuseStep 8109881 = 6082411) B6082411
theorem B1064767 : Blo 1064615 1064767 := bstep (se 1 (by rfl) ⟨798575, by rfl⟩ : syracuseStep 1064767 = 1597151) B1597151
theorem B1064987 : Blo 1064615 1064987 := bstep (se 1 (by rfl) ⟨798740, by rfl⟩ : syracuseStep 1064987 = 1597481) B1597481
theorem B1065007 : Blo 1064615 1065007 := bstep (se 1 (by rfl) ⟨798755, by rfl⟩ : syracuseStep 1065007 = 1597511) B1597511
theorem B113688643 : Blo 1064615 113688643 := bstep (se 1 (by rfl) ⟨85266482, by rfl⟩ : syracuseStep 113688643 = 170532965) B170532965
theorem B1065031 : Blo 1064615 1065031 := bstep (se 1 (by rfl) ⟨798773, by rfl⟩ : syracuseStep 1065031 = 1597547) B1597547
theorem B1065087 : Blo 1064615 1065087 := bstep (se 1 (by rfl) ⟨798815, by rfl⟩ : syracuseStep 1065087 = 1597631) B1597631
theorem B11518109 : Blo 1064615 11518109 := bstep (se 3 (by rfl) ⟨2159645, by rfl⟩ : syracuseStep 11518109 = 4319291) B4319291
theorem B1065211 : Blo 1064615 1065211 := bstep (se 1 (by rfl) ⟨798908, by rfl⟩ : syracuseStep 1065211 = 1597817) B1597817
theorem B8110367 : Blo 1064615 8110367 := bstep (se 1 (by rfl) ⟨6082775, by rfl⟩ : syracuseStep 8110367 = 12165551) B12165551
theorem B1065407 : Blo 1064615 1065407 := bstep (se 1 (by rfl) ⟨799055, by rfl⟩ : syracuseStep 1065407 = 1598111) B1598111
theorem B1065631 : Blo 1064615 1065631 := bstep (se 1 (by rfl) ⟨799223, by rfl⟩ : syracuseStep 1065631 = 1598447) B1598447
theorem B1065703 : Blo 1064615 1065703 := bstep (se 1 (by rfl) ⟨799277, by rfl⟩ : syracuseStep 1065703 = 1598555) B1598555
theorem B1065711 : Blo 1064615 1065711 := bstep (se 1 (by rfl) ⟨799283, by rfl⟩ : syracuseStep 1065711 = 1598567) B1598567
theorem B1065799 : Blo 1064615 1065799 := bstep (se 1 (by rfl) ⟨799349, by rfl⟩ : syracuseStep 1065799 = 1598699) B1598699
theorem B1065887 : Blo 1064615 1065887 := bstep (se 1 (by rfl) ⟨799415, by rfl⟩ : syracuseStep 1065887 = 1598831) B1598831
theorem B1065967 : Blo 1064615 1065967 := bstep (se 1 (by rfl) ⟨799475, by rfl⟩ : syracuseStep 1065967 = 1598951) B1598951
theorem B2704367 : Blo 1064615 2704367 := bstep (se 1 (by rfl) ⟨2028275, by rfl⟩ : syracuseStep 2704367 = 4056551) B4056551
theorem B1066055 : Blo 1064615 1066055 := bstep (se 1 (by rfl) ⟨799541, by rfl⟩ : syracuseStep 1066055 = 1599083) B1599083
theorem B1066087 : Blo 1064615 1066087 := bstep (se 1 (by rfl) ⟨799565, by rfl⟩ : syracuseStep 1066087 = 1599131) B1599131
theorem B1066235 : Blo 1064615 1066235 := bstep (se 1 (by rfl) ⟨799676, by rfl⟩ : syracuseStep 1066235 = 1599353) B1599353
theorem B1066735 : Blo 1064615 1066735 := bstep (se 1 (by rfl) ⟨800051, by rfl⟩ : syracuseStep 1066735 = 1600103) B1600103
theorem B1066919 : Blo 1064615 1066919 := bstep (se 1 (by rfl) ⟨800189, by rfl⟩ : syracuseStep 1066919 = 1600379) B1600379
theorem B1067099 : Blo 1064615 1067099 := bstep (se 1 (by rfl) ⟨800324, by rfl⟩ : syracuseStep 1067099 = 1600649) B1600649
theorem B1067135 : Blo 1064615 1067135 := bstep (se 1 (by rfl) ⟨800351, by rfl⟩ : syracuseStep 1067135 = 1600703) B1600703
theorem B8112311 : Blo 1064615 8112311 := bstep (se 1 (by rfl) ⟨6084233, by rfl⟩ : syracuseStep 8112311 = 12168467) B12168467
theorem B6080771 : Blo 1064615 6080771 := bstep (se 1 (by rfl) ⟨4560578, by rfl⟩ : syracuseStep 6080771 = 9121157) B9121157
theorem B1067495 : Blo 1064615 1067495 := bstep (se 1 (by rfl) ⟨800621, by rfl⟩ : syracuseStep 1067495 = 1601243) B1601243
theorem B1067675 : Blo 1064615 1067675 := bstep (se 1 (by rfl) ⟨800756, by rfl⟩ : syracuseStep 1067675 = 1601513) B1601513
theorem B8112797 : Blo 1064615 8112797 := bstep (se 3 (by rfl) ⟨1521149, by rfl⟩ : syracuseStep 8112797 = 3042299) B3042299
theorem B1067687 : Blo 1064615 1067687 := bstep (se 1 (by rfl) ⟨800765, by rfl⟩ : syracuseStep 1067687 = 1601531) B1601531
theorem B1067711 : Blo 1064615 1067711 := bstep (se 1 (by rfl) ⟨800783, by rfl⟩ : syracuseStep 1067711 = 1601567) B1601567
theorem B1067727 : Blo 1064615 1067727 := bstep (se 1 (by rfl) ⟨800795, by rfl⟩ : syracuseStep 1067727 = 1601591) B1601591
theorem B8211169 : Blo 1064615 8211169 := bstep (se 2 (by rfl) ⟨3079188, by rfl⟩ : syracuseStep 8211169 = 6158377) B6158377
theorem B3754721 : Blo 1064615 3754721 := bstep (se 2 (by rfl) ⟨1408020, by rfl⟩ : syracuseStep 3754721 = 2816041) B2816041
theorem B1067807 : Blo 1064615 1067807 := bstep (se 1 (by rfl) ⟨800855, by rfl⟩ : syracuseStep 1067807 = 1601711) B1601711
theorem B9095975 : Blo 1064615 9095975 := bstep (se 1 (by rfl) ⟨6821981, by rfl⟩ : syracuseStep 9095975 = 13643963) B13643963
theorem B4049747 : Blo 1064615 4049747 := bstep (se 1 (by rfl) ⟨3037310, by rfl⟩ : syracuseStep 4049747 = 6074621) B6074621
theorem B1067943 : Blo 1064615 1067943 := bstep (se 1 (by rfl) ⟨800957, by rfl⟩ : syracuseStep 1067943 = 1601915) B1601915
theorem B2051023 : Blo 1064615 2051023 := bstep (se 1 (by rfl) ⟨1538267, by rfl⟩ : syracuseStep 2051023 = 3076535) B3076535
theorem B1068123 : Blo 1064615 1068123 := bstep (se 1 (by rfl) ⟨801092, by rfl⟩ : syracuseStep 1068123 = 1602185) B1602185
theorem B1199335 : Blo 1064615 1199335 := bstep (se 1 (by rfl) ⟨899501, by rfl⟩ : syracuseStep 1199335 = 1799003) B1799003
theorem B1068263 : Blo 1064615 1068263 := bstep (se 1 (by rfl) ⟨801197, by rfl⟩ : syracuseStep 1068263 = 1602395) B1602395
theorem B1068283 : Blo 1064615 1068283 := bstep (se 1 (by rfl) ⟨801212, by rfl⟩ : syracuseStep 1068283 = 1602425) B1602425
theorem B20762081 : Blo 1064615 20762081 := bstep (se 2 (by rfl) ⟨7785780, by rfl⟩ : syracuseStep 20762081 = 15571561) B15571561
theorem B8114255 : Blo 1064615 8114255 := bstep (se 1 (by rfl) ⟨6085691, by rfl⟩ : syracuseStep 8114255 = 12171383) B12171383
theorem B2282203 : Blo 1064615 2282203 := bstep (se 1 (by rfl) ⟨1711652, by rfl⟩ : syracuseStep 2282203 = 3423305) B3423305
theorem B5395247 : Blo 1064615 5395247 := bstep (se 1 (by rfl) ⟨4046435, by rfl⟩ : syracuseStep 5395247 = 8092871) B8092871
theorem B3593321 : Blo 1064615 3593321 := bstep (se 2 (by rfl) ⟨1347495, by rfl⟩ : syracuseStep 3593321 = 2694991) B2694991
theorem B5395895 : Blo 1064615 5395895 := bstep (se 1 (by rfl) ⟨4046921, by rfl⟩ : syracuseStep 5395895 = 8093843) B8093843
theorem B4052663 : Blo 1064615 4052663 := bstep (se 1 (by rfl) ⟨3039497, by rfl⟩ : syracuseStep 4052663 = 6078995) B6078995
theorem B3594023 : Blo 1064615 3594023 := bstep (se 1 (by rfl) ⟨2695517, by rfl⟩ : syracuseStep 3594023 = 5391035) B5391035
theorem B4609915 : Blo 1064615 4609915 := bstep (se 1 (by rfl) ⟨3457436, by rfl⟩ : syracuseStep 4609915 = 6914873) B6914873
theorem B7296911 : Blo 1064615 7296911 := bstep (se 1 (by rfl) ⟨5472683, by rfl⟩ : syracuseStep 7296911 = 10945367) B10945367
theorem B3594185 : Blo 1064615 3594185 := bstep (se 2 (by rfl) ⟨1347819, by rfl⟩ : syracuseStep 3594185 = 2695639) B2695639
theorem B3037151 : Blo 1064615 3037151 := bstep (se 1 (by rfl) ⟨2277863, by rfl⟩ : syracuseStep 3037151 = 4555727) B4555727
theorem B1202143 : Blo 1064615 1202143 := bstep (se 1 (by rfl) ⟨901607, by rfl⟩ : syracuseStep 1202143 = 1803215) B1803215
theorem B12966331 : Blo 1064615 12966331 := bstep (se 1 (by rfl) ⟨9724748, by rfl⟩ : syracuseStep 12966331 = 19449497) B19449497
theorem B1923527 : Blo 1064615 1923527 := bstep (se 1 (by rfl) ⟨1442645, by rfl⟩ : syracuseStep 1923527 = 2885291) B2885291
theorem B2022185 : Blo 1064615 2022185 := bstep (se 2 (by rfl) ⟨758319, by rfl⟩ : syracuseStep 2022185 = 1516639) B1516639
theorem B3595049 : Blo 1064615 3595049 := bstep (se 2 (by rfl) ⟨1348143, by rfl⟩ : syracuseStep 3595049 = 2696287) B2696287
theorem B4054121 : Blo 1064615 4054121 := bstep (se 2 (by rfl) ⟨1520295, by rfl⟩ : syracuseStep 4054121 = 3040591) B3040591
theorem B5758127 : Blo 1064615 5758127 := bstep (se 1 (by rfl) ⟨4318595, by rfl⟩ : syracuseStep 5758127 = 8637191) B8637191
theorem B5397839 : Blo 1064615 5397839 := bstep (se 1 (by rfl) ⟨4048379, by rfl⟩ : syracuseStep 5397839 = 8096759) B8096759
theorem B6839639 : Blo 1064615 6839639 := bstep (se 1 (by rfl) ⟨5129729, by rfl⟩ : syracuseStep 6839639 = 10259459) B10259459
theorem B116809073 : Blo 1064615 116809073 := bstep (se 2 (by rfl) ⟨43803402, by rfl⟩ : syracuseStep 116809073 = 87606805) B87606805
theorem B1138159 : Blo 1064615 1138159 := bstep (se 1 (by rfl) ⟨853619, by rfl⟩ : syracuseStep 1138159 = 1707239) B1707239
theorem B1597679 : Blo 1064615 1597679 := bstep (se 1 (by rfl) ⟨1198259, by rfl⟩ : syracuseStep 1597679 = 2396519) B2396519
theorem B4055305 : Blo 1064615 4055305 := bstep (se 2 (by rfl) ⟨1520739, by rfl⟩ : syracuseStep 4055305 = 3041479) B3041479
theorem B1597865 : Blo 1064615 1597865 := bstep (se 2 (by rfl) ⟨599199, by rfl⟩ : syracuseStep 1597865 = 1198399) B1198399
theorem B49242629 : Blo 1064615 49242629 := bstep (se 4 (by rfl) ⟨4616496, by rfl⟩ : syracuseStep 49242629 = 9232993) B9232993
theorem B8086067 : Blo 1064615 8086067 := bstep (se 1 (by rfl) ⟨6064550, by rfl⟩ : syracuseStep 8086067 = 12129101) B12129101
theorem B1598057 : Blo 1064615 1598057 := bstep (se 2 (by rfl) ⟨599271, by rfl⟩ : syracuseStep 1598057 = 1198543) B1198543
theorem B5464903 : Blo 1064615 5464903 := bstep (se 1 (by rfl) ⟨4098677, by rfl⟩ : syracuseStep 5464903 = 8197355) B8197355
theorem B4678559 : Blo 1064615 4678559 := bstep (se 1 (by rfl) ⟨3508919, by rfl⟩ : syracuseStep 4678559 = 7017839) B7017839
theorem B4940783 : Blo 1064615 4940783 := bstep (se 1 (by rfl) ⟨3705587, by rfl⟩ : syracuseStep 4940783 = 7411175) B7411175
theorem B14574647 : Blo 1064615 14574647 := bstep (se 1 (by rfl) ⟨10930985, by rfl⟩ : syracuseStep 14574647 = 21861971) B21861971
theorem B1599215 : Blo 1064615 1599215 := bstep (se 1 (by rfl) ⟨1199411, by rfl⟩ : syracuseStep 1599215 = 2398823) B2398823
theorem B2025299 : Blo 1064615 2025299 := bstep (se 1 (by rfl) ⟨1518974, by rfl⟩ : syracuseStep 2025299 = 3037949) B3037949
theorem B17295191 : Blo 1064615 17295191 := bstep (se 1 (by rfl) ⟨12971393, by rfl⟩ : syracuseStep 17295191 = 25942787) B25942787
theorem B1599323 : Blo 1064615 1599323 := bstep (se 1 (by rfl) ⟨1199492, by rfl⟩ : syracuseStep 1599323 = 2398985) B2398985
theorem B7301285 : Blo 1064615 7301285 := bstep (se 4 (by rfl) ⟨684495, by rfl⟩ : syracuseStep 7301285 = 1368991) B1368991
theorem B1599983 : Blo 1064615 1599983 := bstep (se 1 (by rfl) ⟨1199987, by rfl⟩ : syracuseStep 1599983 = 2399975) B2399975
theorem B1600295 : Blo 1064615 1600295 := bstep (se 1 (by rfl) ⟨1200221, by rfl⟩ : syracuseStep 1600295 = 2400443) B2400443
theorem B3599315 : Blo 1064615 3599315 := bstep (se 1 (by rfl) ⟨2699486, by rfl⟩ : syracuseStep 3599315 = 5398973) B5398973
theorem B51866891 : Blo 1064615 51866891 := bstep (se 1 (by rfl) ⟨38900168, by rfl⟩ : syracuseStep 51866891 = 77800337) B77800337
theorem B1600895 : Blo 1064615 1600895 := bstep (se 1 (by rfl) ⟨1200671, by rfl⟩ : syracuseStep 1600895 = 2401343) B2401343
theorem B55504369 : Blo 1064615 55504369 := bstep (se 2 (by rfl) ⟨20814138, by rfl⟩ : syracuseStep 55504369 = 41628277) B41628277
theorem B29552795 : Blo 1064615 29552795 := bstep (se 1 (by rfl) ⟨22164596, by rfl⟩ : syracuseStep 29552795 = 44329193) B44329193
theorem B44462287 : Blo 1064615 44462287 := bstep (se 1 (by rfl) ⟨33346715, by rfl⟩ : syracuseStep 44462287 = 66693431) B66693431
theorem B1601771 : Blo 1064615 1601771 := bstep (se 1 (by rfl) ⟨1201328, by rfl⟩ : syracuseStep 1601771 = 2402657) B2402657
theorem B1601831 : Blo 1064615 1601831 := bstep (se 1 (by rfl) ⟨1201373, by rfl⟩ : syracuseStep 1601831 = 2402747) B2402747
theorem B3600827 : Blo 1064615 3600827 := bstep (se 1 (by rfl) ⟨2700620, by rfl⟩ : syracuseStep 3600827 = 5401241) B5401241
theorem B3240503 : Blo 1064615 3240503 := bstep (se 1 (by rfl) ⟨2430377, by rfl⟩ : syracuseStep 3240503 = 4860755) B4860755
theorem B2028169 : Blo 1064615 2028169 := bstep (se 2 (by rfl) ⟨760563, by rfl⟩ : syracuseStep 2028169 = 1521127) B1521127
theorem B1602359 : Blo 1064615 1602359 := bstep (se 1 (by rfl) ⟨1201769, by rfl⟩ : syracuseStep 1602359 = 2403539) B2403539
theorem B1602473 : Blo 1064615 1602473 := bstep (se 2 (by rfl) ⟨600927, by rfl⟩ : syracuseStep 1602473 = 1201855) B1201855
theorem B1602539 : Blo 1064615 1602539 := bstep (se 1 (by rfl) ⟨1201904, by rfl⟩ : syracuseStep 1602539 = 2403809) B2403809
theorem B1602671 : Blo 1064615 1602671 := bstep (se 1 (by rfl) ⟨1202003, by rfl⟩ : syracuseStep 1602671 = 2404007) B2404007
theorem B2881831 : Blo 1064615 2881831 := bstep (se 1 (by rfl) ⟨2161373, by rfl⟩ : syracuseStep 2881831 = 4322747) B4322747
theorem B15399335 : Blo 1064615 15399335 := bstep (se 1 (by rfl) ⟨11549501, by rfl⟩ : syracuseStep 15399335 = 23099003) B23099003
theorem B8092385 : Blo 1064615 8092385 := bstep (se 2 (by rfl) ⟨3034644, by rfl⟩ : syracuseStep 8092385 = 6069289) B6069289
theorem B3603311 : Blo 1064615 3603311 := bstep (se 1 (by rfl) ⟨2702483, by rfl⟩ : syracuseStep 3603311 = 5404967) B5404967
theorem B2882791 : Blo 1064615 2882791 := bstep (se 1 (by rfl) ⟨2162093, by rfl⟩ : syracuseStep 2882791 = 4324187) B4324187
theorem B49184243 : Blo 1064615 49184243 := bstep (se 1 (by rfl) ⟨36888182, by rfl⟩ : syracuseStep 49184243 = 73776365) B73776365
theorem B133267031 : Blo 1064615 133267031 := bstep (se 1 (by rfl) ⟨99950273, by rfl⟩ : syracuseStep 133267031 = 199900547) B199900547
theorem B1801865 : Blo 1064615 1801865 := bstep (se 2 (by rfl) ⟨675699, by rfl⟩ : syracuseStep 1801865 = 1351399) B1351399
theorem B151584857 : Blo 1064615 151584857 := bstep (se 2 (by rfl) ⟨56844321, by rfl⟩ : syracuseStep 151584857 = 113688643) B113688643
theorem B5406911 : Blo 1064615 5406911 := bstep (se 1 (by rfl) ⟨4055183, by rfl⟩ : syracuseStep 5406911 = 8110367) B8110367
theorem B5407073 : Blo 1064615 5407073 := bstep (se 2 (by rfl) ⟨2027652, by rfl⟩ : syracuseStep 5407073 = 4055305) B4055305
theorem B8094329 : Blo 1064615 8094329 := bstep (se 2 (by rfl) ⟨3035373, by rfl⟩ : syracuseStep 8094329 = 6070747) B6070747
theorem B1802911 : Blo 1064615 1802911 := bstep (se 1 (by rfl) ⟨1352183, by rfl⟩ : syracuseStep 1802911 = 2704367) B2704367
theorem B19989179 : Blo 1064615 19989179 := bstep (se 1 (by rfl) ⟨14991884, by rfl⟩ : syracuseStep 19989179 = 29983769) B29983769
theorem B4556189 : Blo 1064615 4556189 := bstep (se 3 (by rfl) ⟨854285, by rfl⟩ : syracuseStep 4556189 = 1708571) B1708571
theorem B5408207 : Blo 1064615 5408207 := bstep (se 1 (by rfl) ⟨4056155, by rfl⟩ : syracuseStep 5408207 = 8112311) B8112311
theorem B5408531 : Blo 1064615 5408531 := bstep (se 1 (by rfl) ⟨4056398, by rfl⟩ : syracuseStep 5408531 = 8112797) B8112797
theorem B6063983 : Blo 1064615 6063983 := bstep (se 1 (by rfl) ⟨4547987, by rfl⟩ : syracuseStep 6063983 = 9095975) B9095975
theorem B11536667 : Blo 1064615 11536667 := bstep (se 1 (by rfl) ⟨8652500, by rfl⟩ : syracuseStep 11536667 = 17305001) B17305001
theorem B9112135 : Blo 1064615 9112135 := bstep (se 1 (by rfl) ⟨6834101, by rfl⟩ : syracuseStep 9112135 = 13668203) B13668203
theorem B5409503 : Blo 1064615 5409503 := bstep (se 1 (by rfl) ⟨4057127, by rfl⟩ : syracuseStep 5409503 = 8114255) B8114255
theorem B49286225 : Blo 1064615 49286225 := bstep (se 2 (by rfl) ⟨18482334, by rfl⟩ : syracuseStep 49286225 = 36964669) B36964669
theorem B2395547 : Blo 1064615 2395547 := bstep (se 1 (by rfl) ⟨1796660, by rfl⟩ : syracuseStep 2395547 = 3593321) B3593321
theorem B10948225 : Blo 1064615 10948225 := bstep (se 2 (by rfl) ⟨4105584, by rfl⟩ : syracuseStep 10948225 = 8211169) B8211169
theorem B2396015 : Blo 1064615 2396015 := bstep (se 1 (by rfl) ⟨1797011, by rfl⟩ : syracuseStep 2396015 = 3594023) B3594023
theorem B2396123 : Blo 1064615 2396123 := bstep (se 1 (by rfl) ⟨1797092, by rfl⟩ : syracuseStep 2396123 = 3594185) B3594185
theorem B6164453 : Blo 1064615 6164453 := bstep (se 4 (by rfl) ⟨577917, by rfl⟩ : syracuseStep 6164453 = 1155835) B1155835
theorem B5116043 : Blo 1064615 5116043 := bstep (se 1 (by rfl) ⟨3837032, by rfl⟩ : syracuseStep 5116043 = 7674065) B7674065
theorem B2396699 : Blo 1064615 2396699 := bstep (se 1 (by rfl) ⟨1797524, by rfl⟩ : syracuseStep 2396699 = 3595049) B3595049
theorem B3838751 : Blo 1064615 3838751 := bstep (se 1 (by rfl) ⟨2879063, by rfl⟩ : syracuseStep 3838751 = 5758127) B5758127
theorem B4559759 : Blo 1064615 4559759 := bstep (se 1 (by rfl) ⟨3419819, by rfl⟩ : syracuseStep 4559759 = 6839639) B6839639
theorem B9999389 : Blo 1064615 9999389 := bstep (se 3 (by rfl) ⟨1874885, by rfl⟩ : syracuseStep 9999389 = 3749771) B3749771
theorem B3119039 : Blo 1064615 3119039 := bstep (se 1 (by rfl) ⟨2339279, by rfl⟩ : syracuseStep 3119039 = 4678559) B4678559
theorem B5773801 : Blo 1064615 5773801 := bstep (se 2 (by rfl) ⟨2165175, by rfl⟩ : syracuseStep 5773801 = 4330351) B4330351
theorem B1350199 : Blo 1064615 1350199 := bstep (se 1 (by rfl) ⟨1012649, by rfl⟩ : syracuseStep 1350199 = 2025299) B2025299
theorem B2563039 : Blo 1064615 2563039 := bstep (se 1 (by rfl) ⟨1922279, by rfl⟩ : syracuseStep 2563039 = 3844559) B3844559
theorem B2399543 : Blo 1064615 2399543 := bstep (se 1 (by rfl) ⟨1799657, by rfl⟩ : syracuseStep 2399543 = 3599315) B3599315
theorem B34577927 : Blo 1064615 34577927 := bstep (se 1 (by rfl) ⟨25933445, by rfl⟩ : syracuseStep 34577927 = 51866891) B51866891
theorem B19701863 : Blo 1064615 19701863 := bstep (se 1 (by rfl) ⟨14776397, by rfl⟩ : syracuseStep 19701863 = 29552795) B29552795
theorem B2400551 : Blo 1064615 2400551 := bstep (se 1 (by rfl) ⟨1800413, by rfl⟩ : syracuseStep 2400551 = 3600827) B3600827
theorem B3842441 : Blo 1064615 3842441 := bstep (se 2 (by rfl) ⟨1440915, by rfl⟩ : syracuseStep 3842441 = 2881831) B2881831
theorem B1516087 : Blo 1064615 1516087 := bstep (se 1 (by rfl) ⟨1137065, by rfl⟩ : syracuseStep 1516087 = 2274131) B2274131
theorem B8757949 : Blo 1064615 8757949 := bstep (se 3 (by rfl) ⟨1642115, by rfl⟩ : syracuseStep 8757949 = 3284231) B3284231
theorem B2564903 : Blo 1064615 2564903 := bstep (se 1 (by rfl) ⟨1923677, by rfl⟩ : syracuseStep 2564903 = 3847355) B3847355
theorem B1516411 : Blo 1064615 1516411 := bstep (se 1 (by rfl) ⟨1137308, by rfl⟩ : syracuseStep 1516411 = 2274617) B2274617
theorem B2565211 : Blo 1064615 2565211 := bstep (se 1 (by rfl) ⟨1923908, by rfl⟩ : syracuseStep 2565211 = 3847817) B3847817
theorem B10266223 : Blo 1064615 10266223 := bstep (se 1 (by rfl) ⟨7699667, by rfl⟩ : syracuseStep 10266223 = 15399335) B15399335
theorem B3843721 : Blo 1064615 3843721 := bstep (se 2 (by rfl) ⟨1441395, by rfl⟩ : syracuseStep 3843721 = 2882791) B2882791
theorem B2402207 : Blo 1064615 2402207 := bstep (se 1 (by rfl) ⟨1801655, by rfl⟩ : syracuseStep 2402207 = 3603311) B3603311
theorem B24586213 : Blo 1064615 24586213 := bstep (se 4 (by rfl) ⟨2304957, by rfl⟩ : syracuseStep 24586213 = 4609915) B4609915
theorem B1517545 : Blo 1064615 1517545 := bstep (se 2 (by rfl) ⟨569079, by rfl⟩ : syracuseStep 1517545 = 1138159) B1138159
theorem B88844687 : Blo 1064615 88844687 := bstep (se 1 (by rfl) ⟨66633515, by rfl⟩ : syracuseStep 88844687 = 133267031) B133267031
theorem B7678739 : Blo 1064615 7678739 := bstep (se 1 (by rfl) ⟨5759054, by rfl⟩ : syracuseStep 7678739 = 11518109) B11518109
theorem B2403305 : Blo 1064615 2403305 := bstep (se 2 (by rfl) ⟨901239, by rfl⟩ : syracuseStep 2403305 = 1802479) B1802479
theorem B2403359 : Blo 1064615 2403359 := bstep (se 1 (by rfl) ⟨1802519, by rfl⟩ : syracuseStep 2403359 = 3605039) B3605039
theorem B6073937 : Blo 1064615 6073937 := bstep (se 2 (by rfl) ⟨2277726, by rfl⟩ : syracuseStep 6073937 = 4555453) B4555453
theorem B7286537 : Blo 1064615 7286537 := bstep (se 2 (by rfl) ⟨2732451, by rfl⟩ : syracuseStep 7286537 = 5464903) B5464903
theorem B2404187 : Blo 1064615 2404187 := bstep (se 1 (by rfl) ⟨1803140, by rfl⟩ : syracuseStep 2404187 = 3606281) B3606281
theorem B2503147 : Blo 1064615 2503147 := bstep (se 1 (by rfl) ⟨1877360, by rfl⟩ : syracuseStep 2503147 = 3754721) B3754721
theorem B2699831 : Blo 1064615 2699831 := bstep (se 1 (by rfl) ⟨2024873, by rfl⟩ : syracuseStep 2699831 = 4049747) B4049747
theorem B13841387 : Blo 1064615 13841387 := bstep (se 1 (by rfl) ⟨10381040, by rfl⟩ : syracuseStep 13841387 = 20762081) B20762081
theorem B10139053 : Blo 1064615 10139053 := bstep (se 3 (by rfl) ⟨1901072, by rfl⟩ : syracuseStep 10139053 = 3802145) B3802145
theorem B3421921 : Blo 1064615 3421921 := bstep (se 2 (by rfl) ⟨1283220, by rfl⟩ : syracuseStep 3421921 = 2566441) B2566441
theorem B2701775 : Blo 1064615 2701775 := bstep (se 1 (by rfl) ⟨2026331, by rfl⟩ : syracuseStep 2701775 = 4052663) B4052663
theorem B4864607 : Blo 1064615 4864607 := bstep (se 1 (by rfl) ⟨3648455, by rfl⟩ : syracuseStep 4864607 = 7296911) B7296911
theorem B2734697 : Blo 1064615 2734697 := bstep (se 2 (by rfl) ⟨1025511, by rfl⟩ : syracuseStep 2734697 = 2051023) B2051023
theorem B74005825 : Blo 1064615 74005825 := bstep (se 2 (by rfl) ⟨27752184, by rfl⟩ : syracuseStep 74005825 = 55504369) B55504369
theorem B8109395 : Blo 1064615 8109395 := bstep (se 1 (by rfl) ⟨6082046, by rfl⟩ : syracuseStep 8109395 = 12164093) B12164093
theorem B2702747 : Blo 1064615 2702747 := bstep (se 1 (by rfl) ⟨2027060, by rfl⟩ : syracuseStep 2702747 = 4054121) B4054121
theorem B77872715 : Blo 1064615 77872715 := bstep (se 1 (by rfl) ⟨58404536, by rfl⟩ : syracuseStep 77872715 = 116809073) B116809073
theorem B1065119 : Blo 1064615 1065119 := bstep (se 1 (by rfl) ⟨798839, by rfl⟩ : syracuseStep 1065119 = 1597679) B1597679
theorem B1065243 : Blo 1064615 1065243 := bstep (se 1 (by rfl) ⟨798932, by rfl⟩ : syracuseStep 1065243 = 1597865) B1597865
theorem B5390711 : Blo 1064615 5390711 := bstep (se 1 (by rfl) ⟨4043033, by rfl⟩ : syracuseStep 5390711 = 8086067) B8086067
theorem B1065371 : Blo 1064615 1065371 := bstep (se 1 (by rfl) ⟨799028, by rfl⟩ : syracuseStep 1065371 = 1598057) B1598057
theorem B3293855 : Blo 1064615 3293855 := bstep (se 1 (by rfl) ⟨2470391, by rfl⟩ : syracuseStep 3293855 = 4940783) B4940783
theorem B9716431 : Blo 1064615 9716431 := bstep (se 1 (by rfl) ⟨7287323, by rfl⟩ : syracuseStep 9716431 = 14574647) B14574647
theorem B2704225 : Blo 1064615 2704225 := bstep (se 2 (by rfl) ⟨1014084, by rfl⟩ : syracuseStep 2704225 = 2028169) B2028169
theorem B116835371 : Blo 1064615 116835371 := bstep (se 1 (by rfl) ⟨87626528, by rfl⟩ : syracuseStep 116835371 = 175253057) B175253057
theorem B1066143 : Blo 1064615 1066143 := bstep (se 1 (by rfl) ⟨799607, by rfl⟩ : syracuseStep 1066143 = 1599215) B1599215
theorem B5129405 : Blo 1064615 5129405 := bstep (se 3 (by rfl) ⟨961763, by rfl⟩ : syracuseStep 5129405 = 1923527) B1923527
theorem B1066215 : Blo 1064615 1066215 := bstep (se 1 (by rfl) ⟨799661, by rfl⟩ : syracuseStep 1066215 = 1599323) B1599323
theorem B4867523 : Blo 1064615 4867523 := bstep (se 1 (by rfl) ⟨3650642, by rfl⟩ : syracuseStep 4867523 = 7301285) B7301285
theorem B2278991 : Blo 1064615 2278991 := bstep (se 1 (by rfl) ⟨1709243, by rfl⟩ : syracuseStep 2278991 = 3418487) B3418487
theorem B1066655 : Blo 1064615 1066655 := bstep (se 1 (by rfl) ⟨799991, by rfl⟩ : syracuseStep 1066655 = 1599983) B1599983
theorem B1066863 : Blo 1064615 1066863 := bstep (se 1 (by rfl) ⟨800147, by rfl⟩ : syracuseStep 1066863 = 1600295) B1600295
theorem B5392493 : Blo 1064615 5392493 := bstep (se 3 (by rfl) ⟨1011092, by rfl⟩ : syracuseStep 5392493 = 2022185) B2022185
theorem B20498615 : Blo 1064615 20498615 := bstep (se 1 (by rfl) ⟨15373961, by rfl⟩ : syracuseStep 20498615 = 30747923) B30747923
theorem B1067263 : Blo 1064615 1067263 := bstep (se 1 (by rfl) ⟨800447, by rfl⟩ : syracuseStep 1067263 = 1600895) B1600895
theorem B1067847 : Blo 1064615 1067847 := bstep (se 1 (by rfl) ⟨800885, by rfl⟩ : syracuseStep 1067847 = 1601771) B1601771
theorem B1067887 : Blo 1064615 1067887 := bstep (se 1 (by rfl) ⟨800915, by rfl⟩ : syracuseStep 1067887 = 1601831) B1601831
theorem B1068239 : Blo 1064615 1068239 := bstep (se 1 (by rfl) ⟨801179, by rfl⟩ : syracuseStep 1068239 = 1602359) B1602359
theorem B3034361 : Blo 1064615 3034361 := bstep (se 2 (by rfl) ⟨1137885, by rfl⟩ : syracuseStep 3034361 = 2275771) B2275771
theorem B17288441 : Blo 1064615 17288441 := bstep (se 2 (by rfl) ⟨6483165, by rfl⟩ : syracuseStep 17288441 = 12966331) B12966331
theorem B1068315 : Blo 1064615 1068315 := bstep (se 1 (by rfl) ⟨801236, by rfl⟩ : syracuseStep 1068315 = 1602473) B1602473
theorem B1068359 : Blo 1064615 1068359 := bstep (se 1 (by rfl) ⟨801269, by rfl⟩ : syracuseStep 1068359 = 1602539) B1602539
theorem B1068447 : Blo 1064615 1068447 := bstep (se 1 (by rfl) ⟨801335, by rfl⟩ : syracuseStep 1068447 = 1602671) B1602671
theorem B1232623 : Blo 1064615 1232623 := bstep (se 1 (by rfl) ⟨924467, by rfl⟩ : syracuseStep 1232623 = 1848935) B1848935
theorem B4050719 : Blo 1064615 4050719 := bstep (se 1 (by rfl) ⟨3038039, by rfl⟩ : syracuseStep 4050719 = 6076079) B6076079
theorem B2281451 : Blo 1064615 2281451 := bstep (se 1 (by rfl) ⟨1711088, by rfl⟩ : syracuseStep 2281451 = 3422177) B3422177
theorem B5394923 : Blo 1064615 5394923 := bstep (se 1 (by rfl) ⟨4046192, by rfl⟩ : syracuseStep 5394923 = 8092385) B8092385
theorem B32789495 : Blo 1064615 32789495 := bstep (se 1 (by rfl) ⟨24592121, by rfl⟩ : syracuseStep 32789495 = 49184243) B49184243
theorem B1201243 : Blo 1064615 1201243 := bstep (se 1 (by rfl) ⟨900932, by rfl⟩ : syracuseStep 1201243 = 1801865) B1801865
theorem B7296743 : Blo 1064615 7296743 := bstep (se 1 (by rfl) ⟨5472557, by rfl⟩ : syracuseStep 7296743 = 10945115) B10945115
theorem B237132197 : Blo 1064615 237132197 := bstep (se 4 (by rfl) ⟨22231143, by rfl⟩ : syracuseStep 237132197 = 44462287) B44462287
theorem B8215091 : Blo 1064615 8215091 := bstep (se 1 (by rfl) ⟨6161318, by rfl⟩ : syracuseStep 8215091 = 12322637) B12322637
theorem B4053847 : Blo 1064615 4053847 := bstep (se 1 (by rfl) ⟨3040385, by rfl⟩ : syracuseStep 4053847 = 6080771) B6080771
theorem B1924283 : Blo 1064615 1924283 := bstep (se 1 (by rfl) ⟨1443212, by rfl⟩ : syracuseStep 1924283 = 2886425) B2886425
theorem B1596983 : Blo 1064615 1596983 := bstep (se 1 (by rfl) ⟨1197737, by rfl⟩ : syracuseStep 1596983 = 2395475) B2395475
theorem B3595913 : Blo 1064615 3595913 := bstep (se 2 (by rfl) ⟨1348467, by rfl⟩ : syracuseStep 3595913 = 2696935) B2696935
theorem B3038951 : Blo 1064615 3038951 := bstep (se 1 (by rfl) ⟨2279213, by rfl⟩ : syracuseStep 3038951 = 4558427) B4558427
theorem B1597595 : Blo 1064615 1597595 := bstep (se 1 (by rfl) ⟨1198196, by rfl⟩ : syracuseStep 1597595 = 2396393) B2396393
theorem B3039407 : Blo 1064615 3039407 := bstep (se 1 (by rfl) ⟨2279555, by rfl⟩ : syracuseStep 3039407 = 4559111) B4559111
theorem B3596831 : Blo 1064615 3596831 := bstep (se 1 (by rfl) ⟨2697623, by rfl⟩ : syracuseStep 3596831 = 5395247) B5395247
theorem B1598063 : Blo 1064615 1598063 := bstep (se 1 (by rfl) ⟨1198547, by rfl⟩ : syracuseStep 1598063 = 2397095) B2397095
theorem B1598279 : Blo 1064615 1598279 := bstep (se 1 (by rfl) ⟨1198709, by rfl⟩ : syracuseStep 1598279 = 2397419) B2397419
theorem B3597263 : Blo 1064615 3597263 := bstep (se 1 (by rfl) ⟨2697947, by rfl⟩ : syracuseStep 3597263 = 5395895) B5395895
theorem B5465083 : Blo 1064615 5465083 := bstep (se 1 (by rfl) ⟨4098812, by rfl⟩ : syracuseStep 5465083 = 8197625) B8197625
theorem B13657085 : Blo 1064615 13657085 := bstep (se 3 (by rfl) ⟨2560703, by rfl⟩ : syracuseStep 13657085 = 5121407) B5121407
theorem B3466273 : Blo 1064615 3466273 := bstep (se 2 (by rfl) ⟨1299852, by rfl⟩ : syracuseStep 3466273 = 2599705) B2599705
theorem B1598687 : Blo 1064615 1598687 := bstep (se 1 (by rfl) ⟨1199015, by rfl⟩ : syracuseStep 1598687 = 2398031) B2398031
theorem B2024767 : Blo 1064615 2024767 := bstep (se 1 (by rfl) ⟨1518575, by rfl⟩ : syracuseStep 2024767 = 3037151) B3037151
theorem B1598927 : Blo 1064615 1598927 := bstep (se 1 (by rfl) ⟨1199195, by rfl⟩ : syracuseStep 1598927 = 2398391) B2398391
theorem B1599113 : Blo 1064615 1599113 := bstep (se 2 (by rfl) ⟨599667, by rfl⟩ : syracuseStep 1599113 = 1199335) B1199335
theorem B1599167 : Blo 1064615 1599167 := bstep (se 1 (by rfl) ⟨1199375, by rfl⟩ : syracuseStep 1599167 = 2398751) B2398751
theorem B3598559 : Blo 1064615 3598559 := bstep (se 1 (by rfl) ⟨2698919, by rfl⟩ : syracuseStep 3598559 = 5397839) B5397839
theorem B1600055 : Blo 1064615 1600055 := bstep (se 1 (by rfl) ⟨1200041, by rfl⟩ : syracuseStep 1600055 = 2400083) B2400083
theorem B4549355 : Blo 1064615 4549355 := bstep (se 1 (by rfl) ⟨3412016, by rfl⟩ : syracuseStep 4549355 = 6824033) B6824033
theorem B1600319 : Blo 1064615 1600319 := bstep (se 1 (by rfl) ⟨1200239, by rfl⟩ : syracuseStep 1600319 = 2400479) B2400479
theorem B32828419 : Blo 1064615 32828419 := bstep (se 1 (by rfl) ⟨24621314, by rfl⟩ : syracuseStep 32828419 = 49242629) B49242629
theorem B1600619 : Blo 1064615 1600619 := bstep (se 1 (by rfl) ⟨1200464, by rfl⟩ : syracuseStep 1600619 = 2400929) B2400929
theorem B1797403 : Blo 1064615 1797403 := bstep (se 1 (by rfl) ⟨1348052, by rfl⟩ : syracuseStep 1797403 = 2696105) B2696105
theorem B1600859 : Blo 1064615 1600859 := bstep (se 1 (by rfl) ⟨1200644, by rfl⟩ : syracuseStep 1600859 = 2401289) B2401289
theorem B3042937 : Blo 1064615 3042937 := bstep (se 2 (by rfl) ⟨1141101, by rfl⟩ : syracuseStep 3042937 = 2282203) B2282203
theorem B1601183 : Blo 1064615 1601183 := bstep (se 1 (by rfl) ⟨1200887, by rfl⟩ : syracuseStep 1601183 = 2401775) B2401775
theorem B11530127 : Blo 1064615 11530127 := bstep (se 1 (by rfl) ⟨8647595, by rfl⟩ : syracuseStep 11530127 = 17295191) B17295191
theorem B1601819 : Blo 1064615 1601819 := bstep (se 1 (by rfl) ⟨1201364, by rfl⟩ : syracuseStep 1601819 = 2402729) B2402729
theorem B8221241 : Blo 1064615 8221241 := bstep (se 2 (by rfl) ⟨3082965, by rfl⟩ : syracuseStep 8221241 = 6165931) B6165931
theorem B1602857 : Blo 1064615 1602857 := bstep (se 2 (by rfl) ⟨601071, by rfl⟩ : syracuseStep 1602857 = 1202143) B1202143
theorem B2160335 : Blo 1064615 2160335 := bstep (se 1 (by rfl) ⟨1620251, by rfl⟩ : syracuseStep 2160335 = 3240503) B3240503
theorem B1800299 : Blo 1064615 1800299 := bstep (se 1 (by rfl) ⟨1350224, by rfl⟩ : syracuseStep 1800299 = 2700449) B2700449
theorem B3603689 : Blo 1064615 3603689 := bstep (se 2 (by rfl) ⟨1351383, by rfl⟩ : syracuseStep 3603689 = 2702767) B2702767
theorem B5406587 : Blo 1064615 5406587 := bstep (se 1 (by rfl) ⟨4054940, by rfl⟩ : syracuseStep 5406587 = 8109881) B8109881
theorem B101056571 : Blo 1064615 101056571 := bstep (se 1 (by rfl) ⟨75792428, by rfl⟩ : syracuseStep 101056571 = 151584857) B151584857
theorem B3604607 : Blo 1064615 3604607 := bstep (se 1 (by rfl) ⟨2703455, by rfl⟩ : syracuseStep 3604607 = 5406911) B5406911
theorem B3604715 : Blo 1064615 3604715 := bstep (se 1 (by rfl) ⟨2703536, by rfl⟩ : syracuseStep 3604715 = 5407073) B5407073
theorem B2195903 : Blo 1064615 2195903 := bstep (se 1 (by rfl) ⟨1646927, by rfl⟩ : syracuseStep 2195903 = 3293855) B3293855
theorem B77890247 : Blo 1064615 77890247 := bstep (se 1 (by rfl) ⟨58417685, by rfl⟩ : syracuseStep 77890247 = 116835371) B116835371
theorem B3245015 : Blo 1064615 3245015 := bstep (se 1 (by rfl) ⟨2433761, by rfl⟩ : syracuseStep 3245015 = 4867523) B4867523
theorem B3605471 : Blo 1064615 3605471 := bstep (se 1 (by rfl) ⟨2704103, by rfl⟩ : syracuseStep 3605471 = 5408207) B5408207
theorem B3605633 : Blo 1064615 3605633 := bstep (se 2 (by rfl) ⟨1352112, by rfl⟩ : syracuseStep 3605633 = 2704225) B2704225
theorem B3605687 : Blo 1064615 3605687 := bstep (se 1 (by rfl) ⟨2704265, by rfl⟩ : syracuseStep 3605687 = 5408531) B5408531
theorem B4621697 : Blo 1064615 4621697 := bstep (se 2 (by rfl) ⟨1733136, by rfl⟩ : syracuseStep 4621697 = 3466273) B3466273
theorem B13665743 : Blo 1064615 13665743 := bstep (se 1 (by rfl) ⟨10249307, by rfl⟩ : syracuseStep 13665743 = 20498615) B20498615
theorem B3606335 : Blo 1064615 3606335 := bstep (se 1 (by rfl) ⟨2704751, by rfl⟩ : syracuseStep 3606335 = 5409503) B5409503
theorem B3410695 : Blo 1064615 3410695 := bstep (se 1 (by rfl) ⟨2558021, by rfl⟩ : syracuseStep 3410695 = 5116043) B5116043
theorem B2559167 : Blo 1064615 2559167 := bstep (se 1 (by rfl) ⟨1919375, by rfl⟩ : syracuseStep 2559167 = 3838751) B3838751
theorem B5476727 : Blo 1064615 5476727 := bstep (se 1 (by rfl) ⟨4107545, by rfl⟩ : syracuseStep 5476727 = 8215091) B8215091
theorem B2396537 : Blo 1064615 2396537 := bstep (se 2 (by rfl) ⟨898701, by rfl⟩ : syracuseStep 2396537 = 1797403) B1797403
theorem B1643497 : Blo 1064615 1643497 := bstep (se 2 (by rfl) ⟨616311, by rfl⟩ : syracuseStep 1643497 = 1232623) B1232623
theorem B2397275 : Blo 1064615 2397275 := bstep (se 1 (by rfl) ⟨1797956, by rfl⟩ : syracuseStep 2397275 = 3595913) B3595913
theorem B175084901 : Blo 1064615 175084901 := bstep (se 4 (by rfl) ⟨16414209, by rfl⟩ : syracuseStep 175084901 = 32828419) B32828419
theorem B2561627 : Blo 1064615 2561627 := bstep (se 1 (by rfl) ⟨1921220, by rfl⟩ : syracuseStep 2561627 = 3842441) B3842441
theorem B2397887 : Blo 1064615 2397887 := bstep (se 1 (by rfl) ⟨1798415, by rfl⟩ : syracuseStep 2397887 = 3596831) B3596831
theorem B2398175 : Blo 1064615 2398175 := bstep (se 1 (by rfl) ⟨1798631, by rfl⟩ : syracuseStep 2398175 = 3597263) B3597263
theorem B2399039 : Blo 1064615 2399039 := bstep (se 1 (by rfl) ⟨1799279, by rfl⟩ : syracuseStep 2399039 = 3598559) B3598559
theorem B5119159 : Blo 1064615 5119159 := bstep (se 1 (by rfl) ⟨3839369, by rfl⟩ : syracuseStep 5119159 = 7678739) B7678739
theorem B4562561 : Blo 1064615 4562561 := bstep (se 2 (by rfl) ⟨1710960, by rfl⟩ : syracuseStep 4562561 = 3421921) B3421921
theorem B5480827 : Blo 1064615 5480827 := bstep (se 1 (by rfl) ⟨4110620, by rfl⟩ : syracuseStep 5480827 = 8221241) B8221241
theorem B3417385 : Blo 1064615 3417385 := bstep (se 2 (by rfl) ⟨1281519, by rfl⟩ : syracuseStep 3417385 = 2563039) B2563039
theorem B98674433 : Blo 1064615 98674433 := bstep (se 2 (by rfl) ⟨37002912, by rfl⟩ : syracuseStep 98674433 = 74005825) B74005825
theorem B2402459 : Blo 1064615 2402459 := bstep (se 1 (by rfl) ⟨1801844, by rfl⟩ : syracuseStep 2402459 = 3603689) B3603689
theorem B51915143 : Blo 1064615 51915143 := bstep (se 1 (by rfl) ⟨38936357, by rfl⟩ : syracuseStep 51915143 = 77872715) B77872715
theorem B3419603 : Blo 1064615 3419603 := bstep (se 1 (by rfl) ⟨2564702, by rfl⟩ : syracuseStep 3419603 = 5129405) B5129405
theorem B2403881 : Blo 1064615 2403881 := bstep (se 2 (by rfl) ⟨901455, by rfl⟩ : syracuseStep 2403881 = 1802911) B1802911
theorem B11677265 : Blo 1064615 11677265 := bstep (se 2 (by rfl) ⟨4378974, by rfl⟩ : syracuseStep 11677265 = 8757949) B8757949
theorem B12955241 : Blo 1064615 12955241 := bstep (se 2 (by rfl) ⟨4858215, by rfl⟩ : syracuseStep 12955241 = 9716431) B9716431
theorem B1519327 : Blo 1064615 1519327 := bstep (se 1 (by rfl) ⟨1139495, by rfl⟩ : syracuseStep 1519327 = 2278991) B2278991
theorem B4042655 : Blo 1064615 4042655 := bstep (se 1 (by rfl) ⟨3031991, by rfl⟩ : syracuseStep 4042655 = 6063983) B6063983
theorem B7286777 : Blo 1064615 7286777 := bstep (se 2 (by rfl) ⟨2732541, by rfl⟩ : syracuseStep 7286777 = 5465083) B5465083
theorem B3420281 : Blo 1064615 3420281 := bstep (se 2 (by rfl) ⟨1282605, by rfl⟩ : syracuseStep 3420281 = 2565211) B2565211
theorem B2699689 : Blo 1064615 2699689 := bstep (se 2 (by rfl) ⟨1012383, by rfl⟩ : syracuseStep 2699689 = 2024767) B2024767
theorem B5124961 : Blo 1064615 5124961 := bstep (se 2 (by rfl) ⟨1921860, by rfl⟩ : syracuseStep 5124961 = 3843721) B3843721
theorem B2700479 : Blo 1064615 2700479 := bstep (se 1 (by rfl) ⟨2025359, by rfl⟩ : syracuseStep 2700479 = 4050719) B4050719
theorem B32781617 : Blo 1064615 32781617 := bstep (se 2 (by rfl) ⟨12293106, by rfl⟩ : syracuseStep 32781617 = 24586213) B24586213
theorem B87438653 : Blo 1064615 87438653 := bstep (se 3 (by rfl) ⟨16394747, by rfl⟩ : syracuseStep 87438653 = 32789495) B32789495
theorem B4109635 : Blo 1064615 4109635 := bstep (se 1 (by rfl) ⟨3082226, by rfl⟩ : syracuseStep 4109635 = 6164453) B6164453
theorem B6666259 : Blo 1064615 6666259 := bstep (se 1 (by rfl) ⟨4999694, by rfl⟩ : syracuseStep 6666259 = 9999389) B9999389
theorem B2079359 : Blo 1064615 2079359 := bstep (se 1 (by rfl) ⟨1559519, by rfl⟩ : syracuseStep 2079359 = 3119039) B3119039
theorem B158088131 : Blo 1064615 158088131 := bstep (se 1 (by rfl) ⟨118566098, by rfl⟩ : syracuseStep 158088131 = 237132197) B237132197
theorem B14597633 : Blo 1064615 14597633 := bstep (se 2 (by rfl) ⟨5474112, by rfl⟩ : syracuseStep 14597633 = 10948225) B10948225
theorem B23051951 : Blo 1064615 23051951 := bstep (se 1 (by rfl) ⟨17288963, by rfl⟩ : syracuseStep 23051951 = 34577927) B34577927
theorem B1064655 : Blo 1064615 1064655 := bstep (se 1 (by rfl) ⟨798491, by rfl⟩ : syracuseStep 1064655 = 1596983) B1596983
theorem B1065063 : Blo 1064615 1065063 := bstep (se 1 (by rfl) ⟨798797, by rfl⟩ : syracuseStep 1065063 = 1597595) B1597595
theorem B1065375 : Blo 1064615 1065375 := bstep (se 1 (by rfl) ⟨799031, by rfl⟩ : syracuseStep 1065375 = 1598063) B1598063
theorem B1065519 : Blo 1064615 1065519 := bstep (se 1 (by rfl) ⟨799139, by rfl⟩ : syracuseStep 1065519 = 1598279) B1598279
theorem B1065791 : Blo 1064615 1065791 := bstep (se 1 (by rfl) ⟨799343, by rfl⟩ : syracuseStep 1065791 = 1598687) B1598687
theorem B1065951 : Blo 1064615 1065951 := bstep (se 1 (by rfl) ⟨799463, by rfl⟩ : syracuseStep 1065951 = 1598927) B1598927
theorem B1066075 : Blo 1064615 1066075 := bstep (se 1 (by rfl) ⟨799556, by rfl⟩ : syracuseStep 1066075 = 1599113) B1599113
theorem B1066111 : Blo 1064615 1066111 := bstep (se 1 (by rfl) ⟨799583, by rfl⟩ : syracuseStep 1066111 = 1599167) B1599167
theorem B59229791 : Blo 1064615 59229791 := bstep (se 1 (by rfl) ⟨44422343, by rfl⟩ : syracuseStep 59229791 = 88844687) B88844687
theorem B1066703 : Blo 1064615 1066703 := bstep (se 1 (by rfl) ⟨800027, by rfl⟩ : syracuseStep 1066703 = 1600055) B1600055
theorem B3032903 : Blo 1064615 3032903 := bstep (se 1 (by rfl) ⟨2274677, by rfl⟩ : syracuseStep 3032903 = 4549355) B4549355
theorem B1066879 : Blo 1064615 1066879 := bstep (se 1 (by rfl) ⟨800159, by rfl⟩ : syracuseStep 1066879 = 1600319) B1600319
theorem B13518737 : Blo 1064615 13518737 := bstep (se 2 (by rfl) ⟨5069526, by rfl⟩ : syracuseStep 13518737 = 10139053) B10139053
theorem B1067079 : Blo 1064615 1067079 := bstep (se 1 (by rfl) ⟨800309, by rfl⟩ : syracuseStep 1067079 = 1600619) B1600619
theorem B1067239 : Blo 1064615 1067239 := bstep (se 1 (by rfl) ⟨800429, by rfl⟩ : syracuseStep 1067239 = 1600859) B1600859
theorem B4049291 : Blo 1064615 4049291 := bstep (se 1 (by rfl) ⟨3036968, by rfl⟩ : syracuseStep 4049291 = 6073937) B6073937
theorem B1067455 : Blo 1064615 1067455 := bstep (se 1 (by rfl) ⟨800591, by rfl⟩ : syracuseStep 1067455 = 1601183) B1601183
theorem B7686751 : Blo 1064615 7686751 := bstep (se 1 (by rfl) ⟨5765063, by rfl⟩ : syracuseStep 7686751 = 11530127) B11530127
theorem B1067879 : Blo 1064615 1067879 := bstep (se 1 (by rfl) ⟨800909, by rfl⟩ : syracuseStep 1067879 = 1601819) B1601819
theorem B5131421 : Blo 1064615 5131421 := bstep (se 3 (by rfl) ⟨962141, by rfl⟩ : syracuseStep 5131421 = 1924283) B1924283
theorem B9227591 : Blo 1064615 9227591 := bstep (se 1 (by rfl) ⟨6920693, by rfl⟩ : syracuseStep 9227591 = 13841387) B13841387
theorem B1068571 : Blo 1064615 1068571 := bstep (se 1 (by rfl) ⟨801428, by rfl⟩ : syracuseStep 1068571 = 1602857) B1602857
theorem B1200199 : Blo 1064615 1200199 := bstep (se 1 (by rfl) ⟨900149, by rfl⟩ : syracuseStep 1200199 = 1800299) B1800299
theorem B1823131 : Blo 1064615 1823131 := bstep (se 1 (by rfl) ⟨1367348, by rfl⟩ : syracuseStep 1823131 = 2734697) B2734697
theorem B6083869 : Blo 1064615 6083869 := bstep (se 3 (by rfl) ⟨1140725, by rfl⟩ : syracuseStep 6083869 = 2281451) B2281451
theorem B3593807 : Blo 1064615 3593807 := bstep (se 1 (by rfl) ⟨2695355, by rfl⟩ : syracuseStep 3593807 = 5390711) B5390711
theorem B5396219 : Blo 1064615 5396219 := bstep (se 1 (by rfl) ⟨4047164, by rfl⟩ : syracuseStep 5396219 = 8094329) B8094329
theorem B13326119 : Blo 1064615 13326119 := bstep (se 1 (by rfl) ⟨9994589, by rfl⟩ : syracuseStep 13326119 = 19989179) B19989179
theorem B2021449 : Blo 1064615 2021449 := bstep (se 2 (by rfl) ⟨758043, by rfl⟩ : syracuseStep 2021449 = 1516087) B1516087
theorem B3037459 : Blo 1064615 3037459 := bstep (se 1 (by rfl) ⟨2278094, by rfl⟩ : syracuseStep 3037459 = 4556189) B4556189
theorem B3594995 : Blo 1064615 3594995 := bstep (se 1 (by rfl) ⟨2696246, by rfl⟩ : syracuseStep 3594995 = 5392493) B5392493
theorem B7691111 : Blo 1064615 7691111 := bstep (se 1 (by rfl) ⟨5768333, by rfl⟩ : syracuseStep 7691111 = 11536667) B11536667
theorem B32857483 : Blo 1064615 32857483 := bstep (se 1 (by rfl) ⟨24643112, by rfl⟩ : syracuseStep 32857483 = 49286225) B49286225
theorem B6839741 : Blo 1064615 6839741 := bstep (se 3 (by rfl) ⟨1282451, by rfl⟩ : syracuseStep 6839741 = 2564903) B2564903
theorem B13688297 : Blo 1064615 13688297 := bstep (se 2 (by rfl) ⟨5133111, by rfl⟩ : syracuseStep 13688297 = 10266223) B10266223
theorem B2022907 : Blo 1064615 2022907 := bstep (se 1 (by rfl) ⟨1517180, by rfl⟩ : syracuseStep 2022907 = 3034361) B3034361
theorem B11525627 : Blo 1064615 11525627 := bstep (se 1 (by rfl) ⟨8644220, by rfl⟩ : syracuseStep 11525627 = 17288441) B17288441
theorem B1597031 : Blo 1064615 1597031 := bstep (se 1 (by rfl) ⟨1197773, by rfl⟩ : syracuseStep 1597031 = 2395547) B2395547
theorem B1597343 : Blo 1064615 1597343 := bstep (se 1 (by rfl) ⟨1198007, by rfl⟩ : syracuseStep 1597343 = 2396015) B2396015
theorem B2023393 : Blo 1064615 2023393 := bstep (se 2 (by rfl) ⟨758772, by rfl⟩ : syracuseStep 2023393 = 1517545) B1517545
theorem B1597415 : Blo 1064615 1597415 := bstep (se 1 (by rfl) ⟨1198061, by rfl⟩ : syracuseStep 1597415 = 2396123) B2396123
theorem B3596615 : Blo 1064615 3596615 := bstep (se 1 (by rfl) ⟨2697461, by rfl⟩ : syracuseStep 3596615 = 5394923) B5394923
theorem B1597799 : Blo 1064615 1597799 := bstep (se 1 (by rfl) ⟨1198349, by rfl⟩ : syracuseStep 1597799 = 2396699) B2396699
theorem B3039839 : Blo 1064615 3039839 := bstep (se 1 (by rfl) ⟨2279879, by rfl⟩ : syracuseStep 3039839 = 4559759) B4559759
theorem B12149513 : Blo 1064615 12149513 := bstep (se 2 (by rfl) ⟨4556067, by rfl⟩ : syracuseStep 12149513 = 9112135) B9112135
theorem B19457981 : Blo 1064615 19457981 := bstep (se 3 (by rfl) ⟨3648371, by rfl⟩ : syracuseStep 19457981 = 7296743) B7296743
theorem B8087525 : Blo 1064615 8087525 := bstep (se 4 (by rfl) ⟨758205, by rfl⟩ : syracuseStep 8087525 = 1516411) B1516411
theorem B4057249 : Blo 1064615 4057249 := bstep (se 2 (by rfl) ⟨1521468, by rfl⟩ : syracuseStep 4057249 = 3042937) B3042937
theorem B1599695 : Blo 1064615 1599695 := bstep (se 1 (by rfl) ⟨1199771, by rfl⟩ : syracuseStep 1599695 = 2399543) B2399543
theorem B2025967 : Blo 1064615 2025967 := bstep (se 1 (by rfl) ⟨1519475, by rfl⟩ : syracuseStep 2025967 = 3038951) B3038951
theorem B13134575 : Blo 1064615 13134575 := bstep (se 1 (by rfl) ⟨9850931, by rfl⟩ : syracuseStep 13134575 = 19701863) B19701863
theorem B2026271 : Blo 1064615 2026271 := bstep (se 1 (by rfl) ⟨1519703, by rfl⟩ : syracuseStep 2026271 = 3039407) B3039407
theorem B1600367 : Blo 1064615 1600367 := bstep (se 1 (by rfl) ⟨1200275, by rfl⟩ : syracuseStep 1600367 = 2400551) B2400551
theorem B3337529 : Blo 1064615 3337529 := bstep (se 2 (by rfl) ⟨1251573, by rfl⟩ : syracuseStep 3337529 = 2503147) B2503147
theorem B9104723 : Blo 1064615 9104723 := bstep (se 1 (by rfl) ⟨6828542, by rfl⟩ : syracuseStep 9104723 = 13657085) B13657085
theorem B1601471 : Blo 1064615 1601471 := bstep (se 1 (by rfl) ⟨1201103, by rfl⟩ : syracuseStep 1601471 = 2402207) B2402207
theorem B1601657 : Blo 1064615 1601657 := bstep (se 2 (by rfl) ⟨600621, by rfl⟩ : syracuseStep 1601657 = 1201243) B1201243
theorem B1602203 : Blo 1064615 1602203 := bstep (se 1 (by rfl) ⟨1201652, by rfl⟩ : syracuseStep 1602203 = 2403305) B2403305
theorem B1602239 : Blo 1064615 1602239 := bstep (se 1 (by rfl) ⟨1201679, by rfl⟩ : syracuseStep 1602239 = 2403359) B2403359
theorem B1602791 : Blo 1064615 1602791 := bstep (se 1 (by rfl) ⟨1202093, by rfl⟩ : syracuseStep 1602791 = 2404187) B2404187
theorem B1799887 : Blo 1064615 1799887 := bstep (se 1 (by rfl) ⟨1349915, by rfl⟩ : syracuseStep 1799887 = 2699831) B2699831
theorem B7698401 : Blo 1064615 7698401 := bstep (se 2 (by rfl) ⟨2886900, by rfl⟩ : syracuseStep 7698401 = 5773801) B5773801
theorem B1800265 : Blo 1064615 1800265 := bstep (se 2 (by rfl) ⟨675099, by rfl⟩ : syracuseStep 1800265 = 1350199) B1350199
theorem B5405129 : Blo 1064615 5405129 := bstep (se 2 (by rfl) ⟨2026923, by rfl⟩ : syracuseStep 5405129 = 4053847) B4053847
theorem B1440223 : Blo 1064615 1440223 := bstep (se 1 (by rfl) ⟨1080167, by rfl⟩ : syracuseStep 1440223 = 2160335) B2160335
theorem B1801183 : Blo 1064615 1801183 := bstep (se 1 (by rfl) ⟨1350887, by rfl⟩ : syracuseStep 1801183 = 2701775) B2701775
theorem B3243071 : Blo 1064615 3243071 := bstep (se 1 (by rfl) ⟨2432303, by rfl⟩ : syracuseStep 3243071 = 4864607) B4864607
theorem B19430765 : Blo 1064615 19430765 := bstep (se 3 (by rfl) ⟨3643268, by rfl⟩ : syracuseStep 19430765 = 7286537) B7286537
theorem B5406263 : Blo 1064615 5406263 := bstep (se 1 (by rfl) ⟨4054697, by rfl⟩ : syracuseStep 5406263 = 8109395) B8109395
theorem B1801831 : Blo 1064615 1801831 := bstep (se 1 (by rfl) ⟨1351373, by rfl⟩ : syracuseStep 1801831 = 2702747) B2702747
theorem B3604391 : Blo 1064615 3604391 := bstep (se 1 (by rfl) ⟨2703293, by rfl⟩ : syracuseStep 3604391 = 5406587) B5406587
theorem B67371047 : Blo 1064615 67371047 := bstep (se 1 (by rfl) ⟨50528285, by rfl⟩ : syracuseStep 67371047 = 101056571) B101056571
theorem B2163343 : Blo 1064615 2163343 := bstep (se 1 (by rfl) ⟨1622507, by rfl⟩ : syracuseStep 2163343 = 3245015) B3245015
theorem B3081131 : Blo 1064615 3081131 := bstep (se 1 (by rfl) ⟨2310848, by rfl⟩ : syracuseStep 3081131 = 4621697) B4621697
theorem B9110495 : Blo 1064615 9110495 := bstep (se 1 (by rfl) ⟨6832871, by rfl⟩ : syracuseStep 9110495 = 13665743) B13665743
theorem B39486527 : Blo 1064615 39486527 := bstep (se 1 (by rfl) ⟨29614895, by rfl⟩ : syracuseStep 39486527 = 59229791) B59229791
theorem B9012491 : Blo 1064615 9012491 := bstep (se 1 (by rfl) ⟨6759368, by rfl⟩ : syracuseStep 9012491 = 13518737) B13518737
theorem B4556513 : Blo 1064615 4556513 := bstep (se 2 (by rfl) ⟨1708692, by rfl⟩ : syracuseStep 4556513 = 3417385) B3417385
theorem B29231077 : Blo 1064615 29231077 := bstep (se 4 (by rfl) ⟨2740413, by rfl⟩ : syracuseStep 29231077 = 5480827) B5480827
theorem B1706111 : Blo 1064615 1706111 := bstep (se 1 (by rfl) ⟨1279583, by rfl⟩ : syracuseStep 1706111 = 2559167) B2559167
theorem B5409665 : Blo 1064615 5409665 := bstep (se 2 (by rfl) ⟨2028624, by rfl⟩ : syracuseStep 5409665 = 4057249) B4057249
theorem B116723267 : Blo 1064615 116723267 := bstep (se 1 (by rfl) ⟨87542450, by rfl⟩ : syracuseStep 116723267 = 175084901) B175084901
theorem B2395871 : Blo 1064615 2395871 := bstep (se 1 (by rfl) ⟨1796903, by rfl⟩ : syracuseStep 2395871 = 3593807) B3593807
theorem B1707751 : Blo 1064615 1707751 := bstep (se 1 (by rfl) ⟨1280813, by rfl⟩ : syracuseStep 1707751 = 2561627) B2561627
theorem B8884079 : Blo 1064615 8884079 := bstep (se 1 (by rfl) ⟨6663059, by rfl⟩ : syracuseStep 8884079 = 13326119) B13326119
theorem B2396663 : Blo 1064615 2396663 := bstep (se 1 (by rfl) ⟨1797497, by rfl⟩ : syracuseStep 2396663 = 3594995) B3594995
theorem B27333125 : Blo 1064615 27333125 := bstep (se 4 (by rfl) ⟨2562480, by rfl⟩ : syracuseStep 27333125 = 5124961) B5124961
theorem B4559827 : Blo 1064615 4559827 := bstep (se 1 (by rfl) ⟨3419870, by rfl⟩ : syracuseStep 4559827 = 6839741) B6839741
theorem B2397743 : Blo 1064615 2397743 := bstep (se 1 (by rfl) ⟨1798307, by rfl⟩ : syracuseStep 2397743 = 3596615) B3596615
theorem B8099675 : Blo 1064615 8099675 := bstep (se 1 (by rfl) ⟨6074756, by rfl⟩ : syracuseStep 8099675 = 12149513) B12149513
theorem B34610095 : Blo 1064615 34610095 := bstep (se 1 (by rfl) ⟨25957571, by rfl⟩ : syracuseStep 34610095 = 51915143) B51915143
theorem B8756383 : Blo 1064615 8756383 := bstep (se 1 (by rfl) ⟨6567287, by rfl⟩ : syracuseStep 8756383 = 13134575) B13134575
theorem B1350847 : Blo 1064615 1350847 := bstep (se 1 (by rfl) ⟨1013135, by rfl⟩ : syracuseStep 1350847 = 2026271) B2026271
theorem B6069815 : Blo 1064615 6069815 := bstep (se 1 (by rfl) ⟨4552361, by rfl⟩ : syracuseStep 6069815 = 9104723) B9104723
theorem B2399849 : Blo 1064615 2399849 := bstep (se 2 (by rfl) ⟨899943, by rfl⟩ : syracuseStep 2399849 = 1799887) B1799887
theorem B2695103 : Blo 1064615 2695103 := bstep (se 1 (by rfl) ⟨2021327, by rfl⟩ : syracuseStep 2695103 = 4042655) B4042655
theorem B4857851 : Blo 1064615 4857851 := bstep (se 1 (by rfl) ⟨3643388, by rfl⟩ : syracuseStep 4857851 = 7286777) B7286777
theorem B8888345 : Blo 1064615 8888345 := bstep (se 2 (by rfl) ⟨3333129, by rfl⟩ : syracuseStep 8888345 = 6666259) B6666259
theorem B2695265 : Blo 1064615 2695265 := bstep (se 2 (by rfl) ⟨1010724, by rfl⟩ : syracuseStep 2695265 = 2021449) B2021449
theorem B2400353 : Blo 1064615 2400353 := bstep (se 2 (by rfl) ⟨900132, by rfl⟩ : syracuseStep 2400353 = 1800265) B1800265
theorem B8103077 : Blo 1064615 8103077 := bstep (se 4 (by rfl) ⟨759663, by rfl⟩ : syracuseStep 8103077 = 1519327) B1519327
theorem B2401577 : Blo 1064615 2401577 := bstep (se 2 (by rfl) ⟨900591, by rfl⟩ : syracuseStep 2401577 = 1801183) B1801183
theorem B6825545 : Blo 1064615 6825545 := bstep (se 2 (by rfl) ⟨2559579, by rfl⟩ : syracuseStep 6825545 = 5119159) B5119159
theorem B34547309 : Blo 1064615 34547309 := bstep (se 3 (by rfl) ⟨6477620, by rfl⟩ : syracuseStep 34547309 = 12955241) B12955241
theorem B1386239 : Blo 1064615 1386239 := bstep (se 1 (by rfl) ⟨1039679, by rfl⟩ : syracuseStep 1386239 = 2079359) B2079359
theorem B105392087 : Blo 1064615 105392087 := bstep (se 1 (by rfl) ⟨79044065, by rfl⟩ : syracuseStep 105392087 = 158088131) B158088131
theorem B2697209 : Blo 1064615 2697209 := bstep (se 2 (by rfl) ⟨1011453, by rfl⟩ : syracuseStep 2697209 = 2022907) B2022907
theorem B2402441 : Blo 1064615 2402441 := bstep (se 2 (by rfl) ⟨900915, by rfl⟩ : syracuseStep 2402441 = 1801831) B1801831
theorem B12953843 : Blo 1064615 12953843 := bstep (se 1 (by rfl) ⟨9715382, by rfl⟩ : syracuseStep 12953843 = 19430765) B19430765
theorem B2402927 : Blo 1064615 2402927 := bstep (se 1 (by rfl) ⟨1802195, by rfl⟩ : syracuseStep 2402927 = 3604391) B3604391
theorem B2697857 : Blo 1064615 2697857 := bstep (se 2 (by rfl) ⟨1011696, by rfl⟩ : syracuseStep 2697857 = 2023393) B2023393
theorem B2403071 : Blo 1064615 2403071 := bstep (se 1 (by rfl) ⟨1802303, by rfl⟩ : syracuseStep 2403071 = 3604607) B3604607
theorem B2403143 : Blo 1064615 2403143 := bstep (se 1 (by rfl) ⟨1802357, by rfl⟩ : syracuseStep 2403143 = 3604715) B3604715
theorem B2403647 : Blo 1064615 2403647 := bstep (se 1 (by rfl) ⟨1802735, by rfl⟩ : syracuseStep 2403647 = 3605471) B3605471
theorem B2403755 : Blo 1064615 2403755 := bstep (se 1 (by rfl) ⟨1802816, by rfl⟩ : syracuseStep 2403755 = 3605633) B3605633
theorem B2403791 : Blo 1064615 2403791 := bstep (se 1 (by rfl) ⟨1802843, by rfl⟩ : syracuseStep 2403791 = 3605687) B3605687
theorem B2404223 : Blo 1064615 2404223 := bstep (se 1 (by rfl) ⟨1803167, by rfl⟩ : syracuseStep 2404223 = 3606335) B3606335
theorem B2699527 : Blo 1064615 2699527 := bstep (se 1 (by rfl) ⟨2024645, by rfl⟩ : syracuseStep 2699527 = 4049291) B4049291
theorem B3420947 : Blo 1064615 3420947 := bstep (se 1 (by rfl) ⟨2565710, by rfl⟩ : syracuseStep 3420947 = 5131421) B5131421
theorem B7681189 : Blo 1064615 7681189 := bstep (se 4 (by rfl) ⟨720111, by rfl⟩ : syracuseStep 7681189 = 1440223) B1440223
theorem B3651151 : Blo 1064615 3651151 := bstep (se 1 (by rfl) ⟨2738363, by rfl⟩ : syracuseStep 3651151 = 5476727) B5476727
theorem B2701289 : Blo 1064615 2701289 := bstep (se 2 (by rfl) ⟨1012983, by rfl⟩ : syracuseStep 2701289 = 2025967) B2025967
theorem B5127407 : Blo 1064615 5127407 := bstep (se 1 (by rfl) ⟨3845555, by rfl⟩ : syracuseStep 5127407 = 7691111) B7691111
theorem B9125531 : Blo 1064615 9125531 := bstep (se 1 (by rfl) ⟨6844148, by rfl⟩ : syracuseStep 9125531 = 13688297) B13688297
theorem B7683751 : Blo 1064615 7683751 := bstep (se 1 (by rfl) ⟨5762813, by rfl⟩ : syracuseStep 7683751 = 11525627) B11525627
theorem B1064687 : Blo 1064615 1064687 := bstep (se 1 (by rfl) ⟨798515, by rfl⟩ : syracuseStep 1064687 = 1597031) B1597031
theorem B8765317 : Blo 1064615 8765317 := bstep (se 4 (by rfl) ⟨821748, by rfl⟩ : syracuseStep 8765317 = 1643497) B1643497
theorem B1064895 : Blo 1064615 1064895 := bstep (se 1 (by rfl) ⟨798671, by rfl⟩ : syracuseStep 1064895 = 1597343) B1597343
theorem B1064943 : Blo 1064615 1064943 := bstep (se 1 (by rfl) ⟨798707, by rfl⟩ : syracuseStep 1064943 = 1597415) B1597415
theorem B1065199 : Blo 1064615 1065199 := bstep (se 1 (by rfl) ⟨798899, by rfl⟩ : syracuseStep 1065199 = 1597799) B1597799
theorem B65782955 : Blo 1064615 65782955 := bstep (se 1 (by rfl) ⟨49337216, by rfl⟩ : syracuseStep 65782955 = 98674433) B98674433
theorem B5391683 : Blo 1064615 5391683 := bstep (se 1 (by rfl) ⟨4043762, by rfl⟩ : syracuseStep 5391683 = 8087525) B8087525
theorem B1066463 : Blo 1064615 1066463 := bstep (se 1 (by rfl) ⟨799847, by rfl⟩ : syracuseStep 1066463 = 1599695) B1599695
theorem B8111825 : Blo 1064615 8111825 := bstep (se 2 (by rfl) ⟨3041934, by rfl⟩ : syracuseStep 8111825 = 6083869) B6083869
theorem B1066911 : Blo 1064615 1066911 := bstep (se 1 (by rfl) ⟨800183, by rfl⟩ : syracuseStep 1066911 = 1600367) B1600367
theorem B2279735 : Blo 1064615 2279735 := bstep (se 1 (by rfl) ⟨1709801, by rfl⟩ : syracuseStep 2279735 = 3419603) B3419603
theorem B7784843 : Blo 1064615 7784843 := bstep (se 1 (by rfl) ⟨5838632, by rfl⟩ : syracuseStep 7784843 = 11677265) B11677265
theorem B1067647 : Blo 1064615 1067647 := bstep (se 1 (by rfl) ⟨800735, by rfl⟩ : syracuseStep 1067647 = 1601471) B1601471
theorem B2280187 : Blo 1064615 2280187 := bstep (se 1 (by rfl) ⟨1710140, by rfl⟩ : syracuseStep 2280187 = 3420281) B3420281
theorem B1067771 : Blo 1064615 1067771 := bstep (se 1 (by rfl) ⟨800828, by rfl⟩ : syracuseStep 1067771 = 1601657) B1601657
theorem B4049945 : Blo 1064615 4049945 := bstep (se 2 (by rfl) ⟨1518729, by rfl⟩ : syracuseStep 4049945 = 3037459) B3037459
theorem B1068135 : Blo 1064615 1068135 := bstep (se 1 (by rfl) ⟨801101, by rfl⟩ : syracuseStep 1068135 = 1602203) B1602203
theorem B1068159 : Blo 1064615 1068159 := bstep (se 1 (by rfl) ⟨801119, by rfl⟩ : syracuseStep 1068159 = 1602239) B1602239
theorem B8900077 : Blo 1064615 8900077 := bstep (se 3 (by rfl) ⟨1668764, by rfl⟩ : syracuseStep 8900077 = 3337529) B3337529
theorem B1068527 : Blo 1064615 1068527 := bstep (se 1 (by rfl) ⟨801395, by rfl⟩ : syracuseStep 1068527 = 1602791) B1602791
theorem B5132267 : Blo 1064615 5132267 := bstep (se 1 (by rfl) ⟨3849200, by rfl⟩ : syracuseStep 5132267 = 7698401) B7698401
theorem B1463935 : Blo 1064615 1463935 := bstep (se 1 (by rfl) ⟨1097951, by rfl⟩ : syracuseStep 1463935 = 2195903) B2195903
theorem B51926831 : Blo 1064615 51926831 := bstep (se 1 (by rfl) ⟨38945123, by rfl⟩ : syracuseStep 51926831 = 77890247) B77890247
theorem B2021935 : Blo 1064615 2021935 := bstep (se 1 (by rfl) ⟨1516451, by rfl⟩ : syracuseStep 2021935 = 3032903) B3032903
theorem B9723365 : Blo 1064615 9723365 := bstep (se 4 (by rfl) ⟨911565, by rfl⟩ : syracuseStep 9723365 = 1823131) B1823131
theorem B6151727 : Blo 1064615 6151727 := bstep (se 1 (by rfl) ⟨4613795, by rfl⟩ : syracuseStep 6151727 = 9227591) B9227591
theorem B1597691 : Blo 1064615 1597691 := bstep (se 1 (by rfl) ⟨1198268, by rfl⟩ : syracuseStep 1597691 = 2396537) B2396537
theorem B1598183 : Blo 1064615 1598183 := bstep (se 1 (by rfl) ⟨1198637, by rfl⟩ : syracuseStep 1598183 = 2397275) B2397275
theorem B10249001 : Blo 1064615 10249001 := bstep (se 2 (by rfl) ⟨3843375, by rfl⟩ : syracuseStep 10249001 = 7686751) B7686751
theorem B4547593 : Blo 1064615 4547593 := bstep (se 2 (by rfl) ⟨1705347, by rfl⟩ : syracuseStep 4547593 = 3410695) B3410695
theorem B1598591 : Blo 1064615 1598591 := bstep (se 1 (by rfl) ⟨1198943, by rfl⟩ : syracuseStep 1598591 = 2397887) B2397887
theorem B3597479 : Blo 1064615 3597479 := bstep (se 1 (by rfl) ⟨2698109, by rfl⟩ : syracuseStep 3597479 = 5396219) B5396219
theorem B1598783 : Blo 1064615 1598783 := bstep (se 1 (by rfl) ⟨1199087, by rfl⟩ : syracuseStep 1598783 = 2398175) B2398175
theorem B1599359 : Blo 1064615 1599359 := bstep (se 1 (by rfl) ⟨1199519, by rfl⟩ : syracuseStep 1599359 = 2399039) B2399039
theorem B3041707 : Blo 1064615 3041707 := bstep (se 1 (by rfl) ⟨2281280, by rfl⟩ : syracuseStep 3041707 = 4562561) B4562561
theorem B1600265 : Blo 1064615 1600265 := bstep (se 2 (by rfl) ⟨600099, by rfl⟩ : syracuseStep 1600265 = 1200199) B1200199
theorem B2026559 : Blo 1064615 2026559 := bstep (se 1 (by rfl) ⟨1519919, by rfl⟩ : syracuseStep 2026559 = 3039839) B3039839
theorem B3599585 : Blo 1064615 3599585 := bstep (se 2 (by rfl) ⟨1349844, by rfl⟩ : syracuseStep 3599585 = 2699689) B2699689
theorem B12971987 : Blo 1064615 12971987 := bstep (se 1 (by rfl) ⟨9728990, by rfl⟩ : syracuseStep 12971987 = 19457981) B19457981
theorem B1601639 : Blo 1064615 1601639 := bstep (se 1 (by rfl) ⟨1201229, by rfl⟩ : syracuseStep 1601639 = 2402459) B2402459
theorem B21918053 : Blo 1064615 21918053 := bstep (se 4 (by rfl) ⟨2054817, by rfl⟩ : syracuseStep 21918053 = 4109635) B4109635
theorem B1602587 : Blo 1064615 1602587 := bstep (se 1 (by rfl) ⟨1201940, by rfl⟩ : syracuseStep 1602587 = 2403881) B2403881
theorem B1800319 : Blo 1064615 1800319 := bstep (se 1 (by rfl) ⟨1350239, by rfl⟩ : syracuseStep 1800319 = 2700479) B2700479
theorem B21854411 : Blo 1064615 21854411 := bstep (se 1 (by rfl) ⟨16390808, by rfl⟩ : syracuseStep 21854411 = 32781617) B32781617
theorem B58292435 : Blo 1064615 58292435 := bstep (se 1 (by rfl) ⟨43719326, by rfl⟩ : syracuseStep 58292435 = 87438653) B87438653
theorem B3603419 : Blo 1064615 3603419 := bstep (se 1 (by rfl) ⟨2702564, by rfl⟩ : syracuseStep 3603419 = 5405129) B5405129
theorem B43809977 : Blo 1064615 43809977 := bstep (se 2 (by rfl) ⟨16428741, by rfl⟩ : syracuseStep 43809977 = 32857483) B32857483
theorem B2162047 : Blo 1064615 2162047 := bstep (se 1 (by rfl) ⟨1621535, by rfl⟩ : syracuseStep 2162047 = 3243071) B3243071
theorem B9731755 : Blo 1064615 9731755 := bstep (se 1 (by rfl) ⟨7298816, by rfl⟩ : syracuseStep 9731755 = 14597633) B14597633
theorem B3604175 : Blo 1064615 3604175 := bstep (se 1 (by rfl) ⟨2703131, by rfl⟩ : syracuseStep 3604175 = 5406263) B5406263
theorem B15367967 : Blo 1064615 15367967 := bstep (se 1 (by rfl) ⟨11525975, by rfl⟩ : syracuseStep 15367967 = 23051951) B23051951
theorem B2884457 : Blo 1064615 2884457 := bstep (se 2 (by rfl) ⟨1081671, by rfl⟩ : syracuseStep 2884457 = 2163343) B2163343
theorem B5407883 : Blo 1064615 5407883 := bstep (se 1 (by rfl) ⟨4055912, by rfl⟩ : syracuseStep 5407883 = 8111825) B8111825
theorem B6063457 : Blo 1064615 6063457 := bstep (se 2 (by rfl) ⟨2273796, by rfl⟩ : syracuseStep 6063457 = 4547593) B4547593
theorem B3606443 : Blo 1064615 3606443 := bstep (se 1 (by rfl) ⟨2704832, by rfl⟩ : syracuseStep 3606443 = 5409665) B5409665
theorem B18222083 : Blo 1064615 18222083 := bstep (se 1 (by rfl) ⟨13666562, by rfl⟩ : syracuseStep 18222083 = 27333125) B27333125
theorem B11866769 : Blo 1064615 11866769 := bstep (se 2 (by rfl) ⟨4450038, by rfl⟩ : syracuseStep 11866769 = 8900077) B8900077
theorem B4101151 : Blo 1064615 4101151 := bstep (se 1 (by rfl) ⟨3075863, by rfl⟩ : syracuseStep 4101151 = 6151727) B6151727
theorem B2398319 : Blo 1064615 2398319 := bstep (se 1 (by rfl) ⟨1798739, by rfl⟩ : syracuseStep 2398319 = 3597479) B3597479
theorem B70261391 : Blo 1064615 70261391 := bstep (se 1 (by rfl) ⟨52696043, by rfl⟩ : syracuseStep 70261391 = 105392087) B105392087
theorem B2399723 : Blo 1064615 2399723 := bstep (se 1 (by rfl) ⟨1799792, by rfl⟩ : syracuseStep 2399723 = 3599585) B3599585
theorem B14786549 : Blo 1064615 14786549 := bstep (se 5 (by rfl) ⟨693119, by rfl⟩ : syracuseStep 14786549 = 1386239) B1386239
theorem B2400425 : Blo 1064615 2400425 := bstep (se 2 (by rfl) ⟨900159, by rfl⟩ : syracuseStep 2400425 = 1800319) B1800319
theorem B2695913 : Blo 1064615 2695913 := bstep (se 2 (by rfl) ⟨1010967, by rfl⟩ : syracuseStep 2695913 = 2021935) B2021935
theorem B46146793 : Blo 1064615 46146793 := bstep (se 2 (by rfl) ⟨17305047, by rfl⟩ : syracuseStep 46146793 = 34610095) B34610095
theorem B11675177 : Blo 1064615 11675177 := bstep (se 2 (by rfl) ⟨4378191, by rfl⟩ : syracuseStep 11675177 = 8756383) B8756383
theorem B2402279 : Blo 1064615 2402279 := bstep (se 1 (by rfl) ⟨1801709, by rfl⟩ : syracuseStep 2402279 = 3603419) B3603419
theorem B29206651 : Blo 1064615 29206651 := bstep (se 1 (by rfl) ⟨21904988, by rfl⟩ : syracuseStep 29206651 = 43809977) B43809977
theorem B3418271 : Blo 1064615 3418271 := bstep (se 1 (by rfl) ⟨2563703, by rfl⟩ : syracuseStep 3418271 = 5127407) B5127407
theorem B2402783 : Blo 1064615 2402783 := bstep (se 1 (by rfl) ⟨1802087, by rfl⟩ : syracuseStep 2402783 = 3604175) B3604175
theorem B12954269 : Blo 1064615 12954269 := bstep (se 3 (by rfl) ⟨2428925, by rfl⟩ : syracuseStep 12954269 = 4857851) B4857851
theorem B6073663 : Blo 1064615 6073663 := bstep (se 1 (by rfl) ⟨4555247, by rfl⟩ : syracuseStep 6073663 = 9110495) B9110495
theorem B26324351 : Blo 1064615 26324351 := bstep (se 1 (by rfl) ⟨19743263, by rfl⟩ : syracuseStep 26324351 = 39486527) B39486527
theorem B43855303 : Blo 1064615 43855303 := bstep (se 1 (by rfl) ⟨32891477, by rfl⟩ : syracuseStep 43855303 = 65782955) B65782955
theorem B6008327 : Blo 1064615 6008327 := bstep (se 1 (by rfl) ⟨4506245, by rfl⟩ : syracuseStep 6008327 = 9012491) B9012491
theorem B1519823 : Blo 1064615 1519823 := bstep (se 1 (by rfl) ⟨1139867, by rfl⟩ : syracuseStep 1519823 = 2279735) B2279735
theorem B2699963 : Blo 1064615 2699963 := bstep (se 1 (by rfl) ⟨2024972, by rfl⟩ : syracuseStep 2699963 = 4049945) B4049945
theorem B38974769 : Blo 1064615 38974769 := bstep (se 2 (by rfl) ⟨14615538, by rfl⟩ : syracuseStep 38974769 = 29231077) B29231077
theorem B3421511 : Blo 1064615 3421511 := bstep (se 1 (by rfl) ⟨2566133, by rfl⟩ : syracuseStep 3421511 = 5132267) B5132267
theorem B34617887 : Blo 1064615 34617887 := bstep (se 1 (by rfl) ⟨25963415, by rfl⟩ : syracuseStep 34617887 = 51926831) B51926831
theorem B2277001 : Blo 1064615 2277001 := bstep (se 2 (by rfl) ⟨853875, by rfl⟩ : syracuseStep 2277001 = 1707751) B1707751
theorem B4046543 : Blo 1064615 4046543 := bstep (se 1 (by rfl) ⟨3034907, by rfl⟩ : syracuseStep 4046543 = 6069815) B6069815
theorem B1065127 : Blo 1064615 1065127 := bstep (se 1 (by rfl) ⟨798845, by rfl⟩ : syracuseStep 1065127 = 1597691) B1597691
theorem B1065455 : Blo 1064615 1065455 := bstep (se 1 (by rfl) ⟨799091, by rfl⟩ : syracuseStep 1065455 = 1598183) B1598183
theorem B6832667 : Blo 1064615 6832667 := bstep (se 1 (by rfl) ⟨5124500, by rfl⟩ : syracuseStep 6832667 = 10249001) B10249001
theorem B1065727 : Blo 1064615 1065727 := bstep (se 1 (by rfl) ⟨799295, by rfl⟩ : syracuseStep 1065727 = 1598591) B1598591
theorem B1065855 : Blo 1064615 1065855 := bstep (se 1 (by rfl) ⟨799391, by rfl⟩ : syracuseStep 1065855 = 1598783) B1598783
theorem B20759581 : Blo 1064615 20759581 := bstep (se 3 (by rfl) ⟨3892421, by rfl⟩ : syracuseStep 20759581 = 7784843) B7784843
theorem B1066239 : Blo 1064615 1066239 := bstep (se 1 (by rfl) ⟨799679, by rfl⟩ : syracuseStep 1066239 = 1599359) B1599359
theorem B6079769 : Blo 1064615 6079769 := bstep (se 2 (by rfl) ⟨2279913, by rfl⟩ : syracuseStep 6079769 = 4559827) B4559827
theorem B8635895 : Blo 1064615 8635895 := bstep (se 1 (by rfl) ⟨6476921, by rfl⟩ : syracuseStep 8635895 = 12953843) B12953843
theorem B10241585 : Blo 1064615 10241585 := bstep (se 2 (by rfl) ⟨3840594, by rfl⟩ : syracuseStep 10241585 = 7681189) B7681189
theorem B1066843 : Blo 1064615 1066843 := bstep (se 1 (by rfl) ⟨800132, by rfl⟩ : syracuseStep 1066843 = 1600265) B1600265
theorem B4868201 : Blo 1064615 4868201 := bstep (se 2 (by rfl) ⟨1825575, by rfl⟩ : syracuseStep 4868201 = 3651151) B3651151
theorem B1951913 : Blo 1064615 1951913 := bstep (se 2 (by rfl) ⟨731967, by rfl⟩ : syracuseStep 1951913 = 1463935) B1463935
theorem B1067759 : Blo 1064615 1067759 := bstep (se 1 (by rfl) ⟨800819, by rfl⟩ : syracuseStep 1067759 = 1601639) B1601639
theorem B2280631 : Blo 1064615 2280631 := bstep (se 1 (by rfl) ⟨1710473, by rfl⟩ : syracuseStep 2280631 = 3420947) B3420947
theorem B1068391 : Blo 1064615 1068391 := bstep (se 1 (by rfl) ⟨801293, by rfl⟩ : syracuseStep 1068391 = 1602587) B1602587
theorem B40980005 : Blo 1064615 40980005 := bstep (se 4 (by rfl) ⟨3841875, by rfl⟩ : syracuseStep 40980005 = 7683751) B7683751
theorem B14569607 : Blo 1064615 14569607 := bstep (se 1 (by rfl) ⟨10927205, by rfl⟩ : syracuseStep 14569607 = 21854411) B21854411
theorem B6083687 : Blo 1064615 6083687 := bstep (se 1 (by rfl) ⟨4562765, by rfl⟩ : syracuseStep 6083687 = 9125531) B9125531
theorem B11687089 : Blo 1064615 11687089 := bstep (se 2 (by rfl) ⟨4382658, by rfl⟩ : syracuseStep 11687089 = 8765317) B8765317
theorem B10245311 : Blo 1064615 10245311 := bstep (se 1 (by rfl) ⟨7683983, by rfl⟩ : syracuseStep 10245311 = 15367967) B15367967
theorem B44914031 : Blo 1064615 44914031 := bstep (se 1 (by rfl) ⟨33685523, by rfl⟩ : syracuseStep 44914031 = 67371047) B67371047
theorem B2054087 : Blo 1064615 2054087 := bstep (se 1 (by rfl) ⟨1540565, by rfl⟩ : syracuseStep 2054087 = 3081131) B3081131
theorem B3594455 : Blo 1064615 3594455 := bstep (se 1 (by rfl) ⟨2695841, by rfl⟩ : syracuseStep 3594455 = 5391683) B5391683
theorem B3037675 : Blo 1064615 3037675 := bstep (se 1 (by rfl) ⟨2278256, by rfl⟩ : syracuseStep 3037675 = 4556513) B4556513
theorem B1137407 : Blo 1064615 1137407 := bstep (se 1 (by rfl) ⟨853055, by rfl⟩ : syracuseStep 1137407 = 1706111) B1706111
theorem B77815511 : Blo 1064615 77815511 := bstep (se 1 (by rfl) ⟨58361633, by rfl⟩ : syracuseStep 77815511 = 116723267) B116723267
theorem B1597247 : Blo 1064615 1597247 := bstep (se 1 (by rfl) ⟨1197935, by rfl⟩ : syracuseStep 1597247 = 2395871) B2395871
theorem B5922719 : Blo 1064615 5922719 := bstep (se 1 (by rfl) ⟨4442039, by rfl⟩ : syracuseStep 5922719 = 8884079) B8884079
theorem B1597775 : Blo 1064615 1597775 := bstep (se 1 (by rfl) ⟨1198331, by rfl⟩ : syracuseStep 1597775 = 2396663) B2396663
theorem B4055609 : Blo 1064615 4055609 := bstep (se 2 (by rfl) ⟨1520853, by rfl⟩ : syracuseStep 4055609 = 3041707) B3041707
theorem B3040249 : Blo 1064615 3040249 := bstep (se 2 (by rfl) ⟨1140093, by rfl⟩ : syracuseStep 3040249 = 2280187) B2280187
theorem B1598495 : Blo 1064615 1598495 := bstep (se 1 (by rfl) ⟨1198871, by rfl⟩ : syracuseStep 1598495 = 2397743) B2397743
theorem B5399783 : Blo 1064615 5399783 := bstep (se 1 (by rfl) ⟨4049837, by rfl⟩ : syracuseStep 5399783 = 8099675) B8099675
theorem B6482243 : Blo 1064615 6482243 := bstep (se 1 (by rfl) ⟨4861682, by rfl⟩ : syracuseStep 6482243 = 9723365) B9723365
theorem B1599899 : Blo 1064615 1599899 := bstep (se 1 (by rfl) ⟨1199924, by rfl⟩ : syracuseStep 1599899 = 2399849) B2399849
theorem B1796735 : Blo 1064615 1796735 := bstep (se 1 (by rfl) ⟨1347551, by rfl⟩ : syracuseStep 1796735 = 2695103) B2695103
theorem B5925563 : Blo 1064615 5925563 := bstep (se 1 (by rfl) ⟨4444172, by rfl⟩ : syracuseStep 5925563 = 8888345) B8888345
theorem B1796843 : Blo 1064615 1796843 := bstep (se 1 (by rfl) ⟨1347632, by rfl⟩ : syracuseStep 1796843 = 2695265) B2695265
theorem B1600235 : Blo 1064615 1600235 := bstep (se 1 (by rfl) ⟨1200176, by rfl⟩ : syracuseStep 1600235 = 2400353) B2400353
theorem B3599369 : Blo 1064615 3599369 := bstep (se 2 (by rfl) ⟨1349763, by rfl⟩ : syracuseStep 3599369 = 2699527) B2699527
theorem B5402051 : Blo 1064615 5402051 := bstep (se 1 (by rfl) ⟨4051538, by rfl⟩ : syracuseStep 5402051 = 8103077) B8103077
theorem B1601051 : Blo 1064615 1601051 := bstep (se 1 (by rfl) ⟨1200788, by rfl⟩ : syracuseStep 1601051 = 2401577) B2401577
theorem B4550363 : Blo 1064615 4550363 := bstep (se 1 (by rfl) ⟨3412772, by rfl⟩ : syracuseStep 4550363 = 6825545) B6825545
theorem B23031539 : Blo 1064615 23031539 := bstep (se 1 (by rfl) ⟨17273654, by rfl⟩ : syracuseStep 23031539 = 34547309) B34547309
theorem B1798139 : Blo 1064615 1798139 := bstep (se 1 (by rfl) ⟨1348604, by rfl⟩ : syracuseStep 1798139 = 2697209) B2697209
theorem B1601627 : Blo 1064615 1601627 := bstep (se 1 (by rfl) ⟨1201220, by rfl⟩ : syracuseStep 1601627 = 2402441) B2402441
theorem B1601951 : Blo 1064615 1601951 := bstep (se 1 (by rfl) ⟨1201463, by rfl⟩ : syracuseStep 1601951 = 2402927) B2402927
theorem B1798571 : Blo 1064615 1798571 := bstep (se 1 (by rfl) ⟨1348928, by rfl⟩ : syracuseStep 1798571 = 2697857) B2697857
theorem B1602047 : Blo 1064615 1602047 := bstep (se 1 (by rfl) ⟨1201535, by rfl⟩ : syracuseStep 1602047 = 2403071) B2403071
theorem B1602095 : Blo 1064615 1602095 := bstep (se 1 (by rfl) ⟨1201571, by rfl⟩ : syracuseStep 1602095 = 2403143) B2403143
theorem B1602431 : Blo 1064615 1602431 := bstep (se 1 (by rfl) ⟨1201823, by rfl⟩ : syracuseStep 1602431 = 2403647) B2403647
theorem B1602503 : Blo 1064615 1602503 := bstep (se 1 (by rfl) ⟨1201877, by rfl⟩ : syracuseStep 1602503 = 2403755) B2403755
theorem B1602527 : Blo 1064615 1602527 := bstep (se 1 (by rfl) ⟨1201895, by rfl⟩ : syracuseStep 1602527 = 2403791) B2403791
theorem B1602815 : Blo 1064615 1602815 := bstep (se 1 (by rfl) ⟨1202111, by rfl⟩ : syracuseStep 1602815 = 2404223) B2404223
theorem B8647991 : Blo 1064615 8647991 := bstep (se 1 (by rfl) ⟨6485993, by rfl⟩ : syracuseStep 8647991 = 12971987) B12971987
theorem B5404157 : Blo 1064615 5404157 := bstep (se 3 (by rfl) ⟨1013279, by rfl⟩ : syracuseStep 5404157 = 2026559) B2026559
theorem B14612035 : Blo 1064615 14612035 := bstep (se 1 (by rfl) ⟨10959026, by rfl⟩ : syracuseStep 14612035 = 21918053) B21918053
theorem B1800859 : Blo 1064615 1800859 := bstep (se 1 (by rfl) ⟨1350644, by rfl⟩ : syracuseStep 1800859 = 2701289) B2701289
theorem B38861623 : Blo 1064615 38861623 := bstep (se 1 (by rfl) ⟨29146217, by rfl⟩ : syracuseStep 38861623 = 58292435) B58292435
theorem B1801129 : Blo 1064615 1801129 := bstep (se 2 (by rfl) ⟨675423, by rfl⟩ : syracuseStep 1801129 = 1350847) B1350847
theorem B2882729 : Blo 1064615 2882729 := bstep (se 2 (by rfl) ⟨1081023, by rfl⟩ : syracuseStep 2882729 = 2162047) B2162047
theorem B12975673 : Blo 1064615 12975673 := bstep (se 2 (by rfl) ⟨4865877, by rfl⟩ : syracuseStep 12975673 = 9731755) B9731755
theorem B4555111 : Blo 1064615 4555111 := bstep (se 1 (by rfl) ⟨3416333, by rfl⟩ : syracuseStep 4555111 = 6832667) B6832667
theorem B3605255 : Blo 1064615 3605255 := bstep (se 1 (by rfl) ⟨2703941, by rfl⟩ : syracuseStep 3605255 = 5407883) B5407883
theorem B3245467 : Blo 1064615 3245467 := bstep (se 1 (by rfl) ⟨2434100, by rfl⟩ : syracuseStep 3245467 = 4868201) B4868201
theorem B2396303 : Blo 1064615 2396303 := bstep (se 1 (by rfl) ⟨1797227, by rfl⟩ : syracuseStep 2396303 = 3594455) B3594455
theorem B207261989 : Blo 1064615 207261989 := bstep (se 4 (by rfl) ⟨19430811, by rfl⟩ : syracuseStep 207261989 = 38861623) B38861623
theorem B8098217 : Blo 1064615 8098217 := bstep (se 2 (by rfl) ⟨3036831, by rfl⟩ : syracuseStep 8098217 = 6073663) B6073663
theorem B51877007 : Blo 1064615 51877007 := bstep (se 1 (by rfl) ⟨38907755, by rfl⟩ : syracuseStep 51877007 = 77815511) B77815511
theorem B2399579 : Blo 1064615 2399579 := bstep (se 1 (by rfl) ⟨1799684, by rfl⟩ : syracuseStep 2399579 = 3599369) B3599369
theorem B4005551 : Blo 1064615 4005551 := bstep (se 1 (by rfl) ⟨3004163, by rfl⟩ : syracuseStep 4005551 = 6008327) B6008327
theorem B2401145 : Blo 1064615 2401145 := bstep (se 2 (by rfl) ⟨900429, by rfl⟩ : syracuseStep 2401145 = 1800859) B1800859
theorem B2401505 : Blo 1064615 2401505 := bstep (se 2 (by rfl) ⟨900564, by rfl⟩ : syracuseStep 2401505 = 1801129) B1801129
theorem B23078591 : Blo 1064615 23078591 := bstep (se 1 (by rfl) ⟨17308943, by rfl⟩ : syracuseStep 23078591 = 34617887) B34617887
theorem B2697695 : Blo 1064615 2697695 := bstep (se 1 (by rfl) ⟨2023271, by rfl⟩ : syracuseStep 2697695 = 4046543) B4046543
theorem B6827723 : Blo 1064615 6827723 := bstep (se 1 (by rfl) ⟨5120792, by rfl⟩ : syracuseStep 6827723 = 10241585) B10241585
theorem B2404295 : Blo 1064615 2404295 := bstep (se 1 (by rfl) ⟨1803221, by rfl⟩ : syracuseStep 2404295 = 3606443) B3606443
theorem B9713071 : Blo 1064615 9713071 := bstep (se 1 (by rfl) ⟨7284803, by rfl⟩ : syracuseStep 9713071 = 14569607) B14569607
theorem B38942201 : Blo 1064615 38942201 := bstep (se 2 (by rfl) ⟨14603325, by rfl⟩ : syracuseStep 38942201 = 29206651) B29206651
theorem B7911179 : Blo 1064615 7911179 := bstep (se 1 (by rfl) ⟨5933384, by rfl⟩ : syracuseStep 7911179 = 11866769) B11866769
theorem B6830207 : Blo 1064615 6830207 := bstep (se 1 (by rfl) ⟨5122655, by rfl⟩ : syracuseStep 6830207 = 10245311) B10245311
theorem B46840927 : Blo 1064615 46840927 := bstep (se 1 (by rfl) ⟨35130695, by rfl⟩ : syracuseStep 46840927 = 70261391) B70261391
theorem B58473737 : Blo 1064615 58473737 := bstep (se 2 (by rfl) ⟨21927651, by rfl⟩ : syracuseStep 58473737 = 43855303) B43855303
theorem B1064831 : Blo 1064615 1064831 := bstep (se 1 (by rfl) ⟨798623, by rfl⟩ : syracuseStep 1064831 = 1597247) B1597247
theorem B3948479 : Blo 1064615 3948479 := bstep (se 1 (by rfl) ⟨2961359, by rfl⟩ : syracuseStep 3948479 = 5922719) B5922719
theorem B1065183 : Blo 1064615 1065183 := bstep (se 1 (by rfl) ⟨798887, by rfl⟩ : syracuseStep 1065183 = 1597775) B1597775
theorem B2703739 : Blo 1064615 2703739 := bstep (se 1 (by rfl) ⟨2027804, by rfl⟩ : syracuseStep 2703739 = 4055609) B4055609
theorem B1065663 : Blo 1064615 1065663 := bstep (se 1 (by rfl) ⟨799247, by rfl⟩ : syracuseStep 1065663 = 1598495) B1598495
theorem B7783451 : Blo 1064615 7783451 := bstep (se 1 (by rfl) ⟨5837588, by rfl⟩ : syracuseStep 7783451 = 11675177) B11675177
theorem B2278847 : Blo 1064615 2278847 := bstep (se 1 (by rfl) ⟨1709135, by rfl⟩ : syracuseStep 2278847 = 3418271) B3418271
theorem B15582785 : Blo 1064615 15582785 := bstep (se 2 (by rfl) ⟨5843544, by rfl⟩ : syracuseStep 15582785 = 11687089) B11687089
theorem B1066599 : Blo 1064615 1066599 := bstep (se 1 (by rfl) ⟨799949, by rfl⟩ : syracuseStep 1066599 = 1599899) B1599899
theorem B1197823 : Blo 1064615 1197823 := bstep (se 1 (by rfl) ⟨898367, by rfl⟩ : syracuseStep 1197823 = 1796735) B1796735
theorem B8636179 : Blo 1064615 8636179 := bstep (se 1 (by rfl) ⟨6477134, by rfl⟩ : syracuseStep 8636179 = 12954269) B12954269
theorem B3950375 : Blo 1064615 3950375 := bstep (se 1 (by rfl) ⟨2962781, by rfl⟩ : syracuseStep 3950375 = 5925563) B5925563
theorem B1197895 : Blo 1064615 1197895 := bstep (se 1 (by rfl) ⟨898421, by rfl⟩ : syracuseStep 1197895 = 1796843) B1796843
theorem B1066823 : Blo 1064615 1066823 := bstep (se 1 (by rfl) ⟨800117, by rfl⟩ : syracuseStep 1066823 = 1600235) B1600235
theorem B3033085 : Blo 1064615 3033085 := bstep (se 3 (by rfl) ⟨568703, by rfl⟩ : syracuseStep 3033085 = 1137407) B1137407
theorem B19482713 : Blo 1064615 19482713 := bstep (se 2 (by rfl) ⟨7306017, by rfl⟩ : syracuseStep 19482713 = 14612035) B14612035
theorem B17549567 : Blo 1064615 17549567 := bstep (se 1 (by rfl) ⟨13162175, by rfl⟩ : syracuseStep 17549567 = 26324351) B26324351
theorem B1067367 : Blo 1064615 1067367 := bstep (se 1 (by rfl) ⟨800525, by rfl⟩ : syracuseStep 1067367 = 1601051) B1601051
theorem B3033575 : Blo 1064615 3033575 := bstep (se 1 (by rfl) ⟨2275181, by rfl⟩ : syracuseStep 3033575 = 4550363) B4550363
theorem B15354359 : Blo 1064615 15354359 := bstep (se 1 (by rfl) ⟨11515769, by rfl⟩ : syracuseStep 15354359 = 23031539) B23031539
theorem B1198759 : Blo 1064615 1198759 := bstep (se 1 (by rfl) ⟨899069, by rfl⟩ : syracuseStep 1198759 = 1798139) B1798139
theorem B1067751 : Blo 1064615 1067751 := bstep (se 1 (by rfl) ⟨800813, by rfl⟩ : syracuseStep 1067751 = 1601627) B1601627
theorem B1067967 : Blo 1064615 1067967 := bstep (se 1 (by rfl) ⟨800975, by rfl⟩ : syracuseStep 1067967 = 1601951) B1601951
theorem B1199047 : Blo 1064615 1199047 := bstep (se 1 (by rfl) ⟨899285, by rfl⟩ : syracuseStep 1199047 = 1798571) B1798571
theorem B1068031 : Blo 1064615 1068031 := bstep (se 1 (by rfl) ⟨801023, by rfl⟩ : syracuseStep 1068031 = 1602047) B1602047
theorem B1068063 : Blo 1064615 1068063 := bstep (se 1 (by rfl) ⟨801047, by rfl⟩ : syracuseStep 1068063 = 1602095) B1602095
theorem B1068287 : Blo 1064615 1068287 := bstep (se 1 (by rfl) ⟨801215, by rfl⟩ : syracuseStep 1068287 = 1602431) B1602431
theorem B1068335 : Blo 1064615 1068335 := bstep (se 1 (by rfl) ⟨801251, by rfl⟩ : syracuseStep 1068335 = 1602503) B1602503
theorem B4050233 : Blo 1064615 4050233 := bstep (se 2 (by rfl) ⟨1518837, by rfl⟩ : syracuseStep 4050233 = 3037675) B3037675
theorem B1068351 : Blo 1064615 1068351 := bstep (se 1 (by rfl) ⟨801263, by rfl⟩ : syracuseStep 1068351 = 1602527) B1602527
theorem B1068543 : Blo 1064615 1068543 := bstep (se 1 (by rfl) ⟨801407, by rfl⟩ : syracuseStep 1068543 = 1602815) B1602815
theorem B2281007 : Blo 1064615 2281007 := bstep (se 1 (by rfl) ⟨1710755, by rfl⟩ : syracuseStep 2281007 = 3421511) B3421511
theorem B1921819 : Blo 1064615 1921819 := bstep (se 1 (by rfl) ⟨1441364, by rfl⟩ : syracuseStep 1921819 = 2882729) B2882729
theorem B3036001 : Blo 1064615 3036001 := bstep (se 2 (by rfl) ⟨1138500, by rfl⟩ : syracuseStep 3036001 = 2277001) B2277001
theorem B4052861 : Blo 1064615 4052861 := bstep (se 3 (by rfl) ⟨759911, by rfl⟩ : syracuseStep 4052861 = 1519823) B1519823
theorem B4053179 : Blo 1064615 4053179 := bstep (se 1 (by rfl) ⟨3039884, by rfl⟩ : syracuseStep 4053179 = 6079769) B6079769
theorem B5757263 : Blo 1064615 5757263 := bstep (se 1 (by rfl) ⟨4317947, by rfl⟩ : syracuseStep 5757263 = 8635895) B8635895
theorem B4053665 : Blo 1064615 4053665 := bstep (se 2 (by rfl) ⟨1520124, by rfl⟩ : syracuseStep 4053665 = 3040249) B3040249
theorem B1301275 : Blo 1064615 1301275 := bstep (se 1 (by rfl) ⟨975956, by rfl⟩ : syracuseStep 1301275 = 1951913) B1951913
theorem B61529057 : Blo 1064615 61529057 := bstep (se 2 (by rfl) ⟨23073396, by rfl⟩ : syracuseStep 61529057 = 46146793) B46146793
theorem B8084609 : Blo 1064615 8084609 := bstep (se 2 (by rfl) ⟨3031728, by rfl⟩ : syracuseStep 8084609 = 6063457) B6063457
theorem B12148055 : Blo 1064615 12148055 := bstep (se 1 (by rfl) ⟨9111041, by rfl⟩ : syracuseStep 12148055 = 18222083) B18222083
theorem B7691885 : Blo 1064615 7691885 := bstep (se 3 (by rfl) ⟨1442228, by rfl⟩ : syracuseStep 7691885 = 2884457) B2884457
theorem B27320003 : Blo 1064615 27320003 := bstep (se 1 (by rfl) ⟨20490002, by rfl⟩ : syracuseStep 27320003 = 40980005) B40980005
theorem B4055791 : Blo 1064615 4055791 := bstep (se 1 (by rfl) ⟨3041843, by rfl⟩ : syracuseStep 4055791 = 6083687) B6083687
theorem B29942687 : Blo 1064615 29942687 := bstep (se 1 (by rfl) ⟨22457015, by rfl⟩ : syracuseStep 29942687 = 44914031) B44914031
theorem B1369391 : Blo 1064615 1369391 := bstep (se 1 (by rfl) ⟨1027043, by rfl⟩ : syracuseStep 1369391 = 2054087) B2054087
theorem B1598879 : Blo 1064615 1598879 := bstep (se 1 (by rfl) ⟨1199159, by rfl⟩ : syracuseStep 1598879 = 2398319) B2398319
theorem B3040841 : Blo 1064615 3040841 := bstep (se 2 (by rfl) ⟨1140315, by rfl⟩ : syracuseStep 3040841 = 2280631) B2280631
theorem B1599815 : Blo 1064615 1599815 := bstep (se 1 (by rfl) ⟨1199861, by rfl⟩ : syracuseStep 1599815 = 2399723) B2399723
theorem B9857699 : Blo 1064615 9857699 := bstep (se 1 (by rfl) ⟨7393274, by rfl⟩ : syracuseStep 9857699 = 14786549) B14786549
theorem B1600283 : Blo 1064615 1600283 := bstep (se 1 (by rfl) ⟨1200212, by rfl⟩ : syracuseStep 1600283 = 2400425) B2400425
theorem B110717765 : Blo 1064615 110717765 := bstep (se 4 (by rfl) ⟨10379790, by rfl⟩ : syracuseStep 110717765 = 20759581) B20759581
theorem B1797275 : Blo 1064615 1797275 := bstep (se 1 (by rfl) ⟨1347956, by rfl⟩ : syracuseStep 1797275 = 2695913) B2695913
theorem B3599855 : Blo 1064615 3599855 := bstep (se 1 (by rfl) ⟨2699891, by rfl⟩ : syracuseStep 3599855 = 5399783) B5399783
theorem B1601519 : Blo 1064615 1601519 := bstep (se 1 (by rfl) ⟨1201139, by rfl⟩ : syracuseStep 1601519 = 2402279) B2402279
theorem B5468201 : Blo 1064615 5468201 := bstep (se 2 (by rfl) ⟨2050575, by rfl⟩ : syracuseStep 5468201 = 4101151) B4101151
theorem B4321495 : Blo 1064615 4321495 := bstep (se 1 (by rfl) ⟨3241121, by rfl⟩ : syracuseStep 4321495 = 6482243) B6482243
theorem B1601855 : Blo 1064615 1601855 := bstep (se 1 (by rfl) ⟨1201391, by rfl⟩ : syracuseStep 1601855 = 2402783) B2402783
theorem B3601367 : Blo 1064615 3601367 := bstep (se 1 (by rfl) ⟨2701025, by rfl⟩ : syracuseStep 3601367 = 5402051) B5402051
theorem B1799975 : Blo 1064615 1799975 := bstep (se 1 (by rfl) ⟨1349981, by rfl⟩ : syracuseStep 1799975 = 2699963) B2699963
theorem B25983179 : Blo 1064615 25983179 := bstep (se 1 (by rfl) ⟨19487384, by rfl⟩ : syracuseStep 25983179 = 38974769) B38974769
theorem B5765327 : Blo 1064615 5765327 := bstep (se 1 (by rfl) ⟨4323995, by rfl⟩ : syracuseStep 5765327 = 8647991) B8647991
theorem B3602771 : Blo 1064615 3602771 := bstep (se 1 (by rfl) ⟨2702078, by rfl⟩ : syracuseStep 3602771 = 5404157) B5404157
theorem B17300897 : Blo 1064615 17300897 := bstep (se 2 (by rfl) ⟨6487836, by rfl⟩ : syracuseStep 17300897 = 12975673) B12975673
theorem B3604985 : Blo 1064615 3604985 := bstep (se 2 (by rfl) ⟨1351869, by rfl⟩ : syracuseStep 3604985 = 2703739) B2703739
theorem B5407721 : Blo 1064615 5407721 := bstep (se 2 (by rfl) ⟨2027895, by rfl⟩ : syracuseStep 5407721 = 4055791) B4055791
theorem B11699711 : Blo 1064615 11699711 := bstep (se 1 (by rfl) ⟨8774783, by rfl⟩ : syracuseStep 11699711 = 17549567) B17549567
theorem B4327289 : Blo 1064615 4327289 := bstep (se 2 (by rfl) ⟨1622733, by rfl⟩ : syracuseStep 4327289 = 3245467) B3245467
theorem B3838175 : Blo 1064615 3838175 := bstep (se 1 (by rfl) ⟨2878631, by rfl⟩ : syracuseStep 3838175 = 5757263) B5757263
theorem B8098703 : Blo 1064615 8098703 := bstep (se 1 (by rfl) ⟨6074027, by rfl⟩ : syracuseStep 8098703 = 12148055) B12148055
theorem B2562425 : Blo 1064615 2562425 := bstep (se 2 (by rfl) ⟨960909, by rfl⟩ : syracuseStep 2562425 = 1921819) B1921819
theorem B12950761 : Blo 1064615 12950761 := bstep (se 2 (by rfl) ⟨4856535, by rfl⟩ : syracuseStep 12950761 = 9713071) B9713071
theorem B2399903 : Blo 1064615 2399903 := bstep (se 1 (by rfl) ⟨1799927, by rfl⟩ : syracuseStep 2399903 = 3599855) B3599855
theorem B3645467 : Blo 1064615 3645467 := bstep (se 1 (by rfl) ⟨2734100, by rfl⟩ : syracuseStep 3645467 = 5468201) B5468201
theorem B2400911 : Blo 1064615 2400911 := bstep (se 1 (by rfl) ⟨1800683, by rfl⟩ : syracuseStep 2400911 = 3601367) B3601367
theorem B25961467 : Blo 1064615 25961467 := bstep (se 1 (by rfl) ⟨19471100, by rfl⟩ : syracuseStep 25961467 = 38942201) B38942201
theorem B3843551 : Blo 1064615 3843551 := bstep (se 1 (by rfl) ⟨2882663, by rfl⟩ : syracuseStep 3843551 = 5765327) B5765327
theorem B2401847 : Blo 1064615 2401847 := bstep (se 1 (by rfl) ⟨1801385, by rfl⟩ : syracuseStep 2401847 = 3602771) B3602771
theorem B2632319 : Blo 1064615 2632319 := bstep (se 1 (by rfl) ⟨1974239, by rfl⟩ : syracuseStep 2632319 = 3948479) B3948479
theorem B6073481 : Blo 1064615 6073481 := bstep (se 2 (by rfl) ⟨2277555, by rfl⟩ : syracuseStep 6073481 = 4555111) B4555111
theorem B2403503 : Blo 1064615 2403503 := bstep (se 1 (by rfl) ⟨1802627, by rfl⟩ : syracuseStep 2403503 = 3605255) B3605255
theorem B5188967 : Blo 1064615 5188967 := bstep (se 1 (by rfl) ⟨3891725, by rfl⟩ : syracuseStep 5188967 = 7783451) B7783451
theorem B1519231 : Blo 1064615 1519231 := bstep (se 1 (by rfl) ⟨1139423, by rfl⟩ : syracuseStep 1519231 = 2278847) B2278847
theorem B23047973 : Blo 1064615 23047973 := bstep (se 4 (by rfl) ⟨2160747, by rfl⟩ : syracuseStep 23047973 = 4321495) B4321495
theorem B12988475 : Blo 1064615 12988475 := bstep (se 1 (by rfl) ⟨9741356, by rfl⟩ : syracuseStep 12988475 = 19482713) B19482713
theorem B10236239 : Blo 1064615 10236239 := bstep (se 1 (by rfl) ⟨7677179, by rfl⟩ : syracuseStep 10236239 = 15354359) B15354359
theorem B2700155 : Blo 1064615 2700155 := bstep (se 1 (by rfl) ⟨2025116, by rfl⟩ : syracuseStep 2700155 = 4050233) B4050233
theorem B11514905 : Blo 1064615 11514905 := bstep (se 2 (by rfl) ⟨4318089, by rfl⟩ : syracuseStep 11514905 = 8636179) B8636179
theorem B4044113 : Blo 1064615 4044113 := bstep (se 2 (by rfl) ⟨1516542, by rfl⟩ : syracuseStep 4044113 = 3033085) B3033085
theorem B34584671 : Blo 1064615 34584671 := bstep (se 1 (by rfl) ⟨25938503, by rfl⟩ : syracuseStep 34584671 = 51877007) B51877007
theorem B2701907 : Blo 1064615 2701907 := bstep (se 1 (by rfl) ⟨2026430, by rfl⟩ : syracuseStep 2701907 = 4052861) B4052861
theorem B2702119 : Blo 1064615 2702119 := bstep (se 1 (by rfl) ⟨2026589, by rfl⟩ : syracuseStep 2702119 = 4053179) B4053179
theorem B8108909 : Blo 1064615 8108909 := bstep (se 3 (by rfl) ⟨1520420, by rfl⟩ : syracuseStep 8108909 = 3040841) B3040841
theorem B2702443 : Blo 1064615 2702443 := bstep (se 1 (by rfl) ⟨2026832, by rfl⟩ : syracuseStep 2702443 = 4053665) B4053665
theorem B5389739 : Blo 1064615 5389739 := bstep (se 1 (by rfl) ⟨4042304, by rfl⟩ : syracuseStep 5389739 = 8084609) B8084609
theorem B5127923 : Blo 1064615 5127923 := bstep (se 1 (by rfl) ⟨3845942, by rfl⟩ : syracuseStep 5127923 = 7691885) B7691885
theorem B166216373 : Blo 1064615 166216373 := bstep (se 5 (by rfl) ⟨7791392, by rfl⟩ : syracuseStep 166216373 = 15582785) B15582785
theorem B1065919 : Blo 1064615 1065919 := bstep (se 1 (by rfl) ⟨799439, by rfl⟩ : syracuseStep 1065919 = 1598879) B1598879
theorem B15385727 : Blo 1064615 15385727 := bstep (se 1 (by rfl) ⟨11539295, by rfl⟩ : syracuseStep 15385727 = 23078591) B23078591
theorem B4048001 : Blo 1064615 4048001 := bstep (se 2 (by rfl) ⟨1518000, by rfl⟩ : syracuseStep 4048001 = 3036001) B3036001
theorem B1066543 : Blo 1064615 1066543 := bstep (se 1 (by rfl) ⟨799907, by rfl⟩ : syracuseStep 1066543 = 1599815) B1599815
theorem B6571799 : Blo 1064615 6571799 := bstep (se 1 (by rfl) ⟨4928849, by rfl⟩ : syracuseStep 6571799 = 9857699) B9857699
theorem B1066855 : Blo 1064615 1066855 := bstep (se 1 (by rfl) ⟨800141, by rfl⟩ : syracuseStep 1066855 = 1600283) B1600283
theorem B73811843 : Blo 1064615 73811843 := bstep (se 1 (by rfl) ⟨55358882, by rfl⟩ : syracuseStep 73811843 = 110717765) B110717765
theorem B1198183 : Blo 1064615 1198183 := bstep (se 1 (by rfl) ⟨898637, by rfl⟩ : syracuseStep 1198183 = 1797275) B1797275
theorem B1067679 : Blo 1064615 1067679 := bstep (se 1 (by rfl) ⟨800759, by rfl⟩ : syracuseStep 1067679 = 1601519) B1601519
theorem B1067903 : Blo 1064615 1067903 := bstep (se 1 (by rfl) ⟨800927, by rfl⟩ : syracuseStep 1067903 = 1601855) B1601855
theorem B1199983 : Blo 1064615 1199983 := bstep (se 1 (by rfl) ⟨899987, by rfl⟩ : syracuseStep 1199983 = 1799975) B1799975
theorem B6082685 : Blo 1064615 6082685 := bstep (se 3 (by rfl) ⟨1140503, by rfl⟩ : syracuseStep 6082685 = 2281007) B2281007
theorem B17322119 : Blo 1064615 17322119 := bstep (se 1 (by rfl) ⟨12991589, by rfl⟩ : syracuseStep 17322119 = 25983179) B25983179
theorem B38982491 : Blo 1064615 38982491 := bstep (se 1 (by rfl) ⟨29236868, by rfl⟩ : syracuseStep 38982491 = 58473737) B58473737
theorem B2022383 : Blo 1064615 2022383 := bstep (se 1 (by rfl) ⟨1516787, by rfl⟩ : syracuseStep 2022383 = 3033575) B3033575
theorem B1597097 : Blo 1064615 1597097 := bstep (se 2 (by rfl) ⟨598911, by rfl⟩ : syracuseStep 1597097 = 1197823) B1197823
theorem B79847165 : Blo 1064615 79847165 := bstep (se 3 (by rfl) ⟨14971343, by rfl⟩ : syracuseStep 79847165 = 29942687) B29942687
theorem B1597193 : Blo 1064615 1597193 := bstep (se 2 (by rfl) ⟨598947, by rfl⟩ : syracuseStep 1597193 = 1197895) B1197895
theorem B1597535 : Blo 1064615 1597535 := bstep (se 1 (by rfl) ⟨1198151, by rfl⟩ : syracuseStep 1597535 = 2396303) B2396303
theorem B138174659 : Blo 1064615 138174659 := bstep (se 1 (by rfl) ⟨103630994, by rfl⟩ : syracuseStep 138174659 = 207261989) B207261989
theorem B5398811 : Blo 1064615 5398811 := bstep (se 1 (by rfl) ⟨4049108, by rfl⟩ : syracuseStep 5398811 = 8098217) B8098217
theorem B14606837 : Blo 1064615 14606837 := bstep (se 5 (by rfl) ⟨684695, by rfl⟩ : syracuseStep 14606837 = 1369391) B1369391
theorem B1598345 : Blo 1064615 1598345 := bstep (se 2 (by rfl) ⟨599379, by rfl⟩ : syracuseStep 1598345 = 1198759) B1198759
theorem B1598729 : Blo 1064615 1598729 := bstep (se 2 (by rfl) ⟨599523, by rfl⟩ : syracuseStep 1598729 = 1199047) B1199047
theorem B41019371 : Blo 1064615 41019371 := bstep (se 1 (by rfl) ⟨30764528, by rfl⟩ : syracuseStep 41019371 = 61529057) B61529057
theorem B1599719 : Blo 1064615 1599719 := bstep (se 1 (by rfl) ⟨1199789, by rfl⟩ : syracuseStep 1599719 = 2399579) B2399579
theorem B18213335 : Blo 1064615 18213335 := bstep (se 1 (by rfl) ⟨13660001, by rfl⟩ : syracuseStep 18213335 = 27320003) B27320003
theorem B1600763 : Blo 1064615 1600763 := bstep (se 1 (by rfl) ⟨1200572, by rfl⟩ : syracuseStep 1600763 = 2401145) B2401145
theorem B1601003 : Blo 1064615 1601003 := bstep (se 1 (by rfl) ⟨1200752, by rfl⟩ : syracuseStep 1601003 = 2401505) B2401505
theorem B1798463 : Blo 1064615 1798463 := bstep (se 1 (by rfl) ⟨1348847, by rfl⟩ : syracuseStep 1798463 = 2697695) B2697695
theorem B4551815 : Blo 1064615 4551815 := bstep (se 1 (by rfl) ⟨3413861, by rfl⟩ : syracuseStep 4551815 = 6827723) B6827723
theorem B1602863 : Blo 1064615 1602863 := bstep (se 1 (by rfl) ⟨1202147, by rfl⟩ : syracuseStep 1602863 = 2404295) B2404295
theorem B42137333 : Blo 1064615 42137333 := bstep (se 5 (by rfl) ⟨1975187, by rfl⟩ : syracuseStep 42137333 = 3950375) B3950375
theorem B1735033 : Blo 1064615 1735033 := bstep (se 2 (by rfl) ⟨650637, by rfl⟩ : syracuseStep 1735033 = 1301275) B1301275
theorem B5274119 : Blo 1064615 5274119 := bstep (se 1 (by rfl) ⟨3955589, by rfl⟩ : syracuseStep 5274119 = 7911179) B7911179
theorem B4553471 : Blo 1064615 4553471 := bstep (se 1 (by rfl) ⟨3415103, by rfl⟩ : syracuseStep 4553471 = 6830207) B6830207
theorem B62454569 : Blo 1064615 62454569 := bstep (se 2 (by rfl) ⟨23420463, by rfl⟩ : syracuseStep 62454569 = 46840927) B46840927
theorem B10681469 : Blo 1064615 10681469 := bstep (se 3 (by rfl) ⟨2002775, by rfl⟩ : syracuseStep 10681469 = 4005551) B4005551
theorem B11533931 : Blo 1064615 11533931 := bstep (se 1 (by rfl) ⟨8650448, by rfl⟩ : syracuseStep 11533931 = 17300897) B17300897
theorem B3605147 : Blo 1064615 3605147 := bstep (se 1 (by rfl) ⟨2703860, by rfl⟩ : syracuseStep 3605147 = 5407721) B5407721
theorem B10257151 : Blo 1064615 10257151 := bstep (se 1 (by rfl) ⟨7692863, by rfl⟩ : syracuseStep 10257151 = 15385727) B15385727
theorem B7799807 : Blo 1064615 7799807 := bstep (se 1 (by rfl) ⟨5849855, by rfl⟩ : syracuseStep 7799807 = 11699711) B11699711
theorem B2884859 : Blo 1064615 2884859 := bstep (se 1 (by rfl) ⟨2163644, by rfl⟩ : syracuseStep 2884859 = 4327289) B4327289
theorem B2558783 : Blo 1064615 2558783 := bstep (se 1 (by rfl) ⟨1919087, by rfl⟩ : syracuseStep 2558783 = 3838175) B3838175
theorem B25988327 : Blo 1064615 25988327 := bstep (se 1 (by rfl) ⟨19491245, by rfl⟩ : syracuseStep 25988327 = 38982491) B38982491
theorem B1708283 : Blo 1064615 1708283 := bstep (se 1 (by rfl) ⟨1281212, by rfl⟩ : syracuseStep 1708283 = 2562425) B2562425
theorem B1348255 : Blo 1064615 1348255 := bstep (se 1 (by rfl) ⟨1011191, by rfl⟩ : syracuseStep 1348255 = 2022383) B2022383
theorem B92116439 : Blo 1064615 92116439 := bstep (se 1 (by rfl) ⟨69087329, by rfl⟩ : syracuseStep 92116439 = 138174659) B138174659
theorem B9737891 : Blo 1064615 9737891 := bstep (se 1 (by rfl) ⟨7303418, by rfl⟩ : syracuseStep 9737891 = 14606837) B14606837
theorem B2562367 : Blo 1064615 2562367 := bstep (se 1 (by rfl) ⟨1921775, by rfl⟩ : syracuseStep 2562367 = 3843551) B3843551
theorem B14064317 : Blo 1064615 14064317 := bstep (se 3 (by rfl) ⟨2637059, by rfl⟩ : syracuseStep 14064317 = 5274119) B5274119
theorem B8658983 : Blo 1064615 8658983 := bstep (se 1 (by rfl) ⟨6494237, by rfl⟩ : syracuseStep 8658983 = 12988475) B12988475
theorem B6824159 : Blo 1064615 6824159 := bstep (se 1 (by rfl) ⟨5118119, by rfl⟩ : syracuseStep 6824159 = 10236239) B10236239
theorem B7676603 : Blo 1064615 7676603 := bstep (se 1 (by rfl) ⟨5757452, by rfl⟩ : syracuseStep 7676603 = 11514905) B11514905
theorem B2696075 : Blo 1064615 2696075 := bstep (se 1 (by rfl) ⟨2022056, by rfl⟩ : syracuseStep 2696075 = 4044113) B4044113
theorem B28091555 : Blo 1064615 28091555 := bstep (se 1 (by rfl) ⟨21068666, by rfl⟩ : syracuseStep 28091555 = 42137333) B42137333
theorem B7120979 : Blo 1064615 7120979 := bstep (se 1 (by rfl) ⟨5340734, by rfl⟩ : syracuseStep 7120979 = 10681469) B10681469
theorem B3418615 : Blo 1064615 3418615 := bstep (se 1 (by rfl) ⟨2563961, by rfl⟩ : syracuseStep 3418615 = 5127923) B5127923
theorem B2403323 : Blo 1064615 2403323 := bstep (se 1 (by rfl) ⟨1802492, by rfl⟩ : syracuseStep 2403323 = 3604985) B3604985
theorem B2698667 : Blo 1064615 2698667 := bstep (se 1 (by rfl) ⟨2024000, by rfl⟩ : syracuseStep 2698667 = 4048001) B4048001
theorem B34615289 : Blo 1064615 34615289 := bstep (se 2 (by rfl) ⟨12980733, by rfl⟩ : syracuseStep 34615289 = 25961467) B25961467
theorem B11548079 : Blo 1064615 11548079 := bstep (se 1 (by rfl) ⟨8661059, by rfl⟩ : syracuseStep 11548079 = 17322119) B17322119
theorem B1064731 : Blo 1064615 1064731 := bstep (se 1 (by rfl) ⟨798548, by rfl⟩ : syracuseStep 1064731 = 1597097) B1597097
theorem B1064795 : Blo 1064615 1064795 := bstep (se 1 (by rfl) ⟨798596, by rfl⟩ : syracuseStep 1064795 = 1597193) B1597193
theorem B1065023 : Blo 1064615 1065023 := bstep (se 1 (by rfl) ⟨798767, by rfl⟩ : syracuseStep 1065023 = 1597535) B1597535
theorem B1065563 : Blo 1064615 1065563 := bstep (se 1 (by rfl) ⟨799172, by rfl⟩ : syracuseStep 1065563 = 1598345) B1598345
theorem B1065819 : Blo 1064615 1065819 := bstep (se 1 (by rfl) ⟨799364, by rfl⟩ : syracuseStep 1065819 = 1598729) B1598729
theorem B27346247 : Blo 1064615 27346247 := bstep (se 1 (by rfl) ⟨20509685, by rfl⟩ : syracuseStep 27346247 = 41019371) B41019371
theorem B1066479 : Blo 1064615 1066479 := bstep (se 1 (by rfl) ⟨799859, by rfl⟩ : syracuseStep 1066479 = 1599719) B1599719
theorem B12142223 : Blo 1064615 12142223 := bstep (se 1 (by rfl) ⟨9106667, by rfl⟩ : syracuseStep 12142223 = 18213335) B18213335
theorem B1754879 : Blo 1064615 1754879 := bstep (se 1 (by rfl) ⟨1316159, by rfl⟩ : syracuseStep 1754879 = 2632319) B2632319
theorem B4048987 : Blo 1064615 4048987 := bstep (se 1 (by rfl) ⟨3036740, by rfl⟩ : syracuseStep 4048987 = 6073481) B6073481
theorem B166545517 : Blo 1064615 166545517 := bstep (se 3 (by rfl) ⟨31227284, by rfl⟩ : syracuseStep 166545517 = 62454569) B62454569
theorem B1067175 : Blo 1064615 1067175 := bstep (se 1 (by rfl) ⟨800381, by rfl⟩ : syracuseStep 1067175 = 1600763) B1600763
theorem B3459311 : Blo 1064615 3459311 := bstep (se 1 (by rfl) ⟨2594483, by rfl⟩ : syracuseStep 3459311 = 5188967) B5188967
theorem B1067335 : Blo 1064615 1067335 := bstep (se 1 (by rfl) ⟨800501, by rfl⟩ : syracuseStep 1067335 = 1601003) B1601003
theorem B1198975 : Blo 1064615 1198975 := bstep (se 1 (by rfl) ⟨899231, by rfl⟩ : syracuseStep 1198975 = 1798463) B1798463
theorem B2313377 : Blo 1064615 2313377 := bstep (se 2 (by rfl) ⟨867516, by rfl⟩ : syracuseStep 2313377 = 1735033) B1735033
theorem B3034543 : Blo 1064615 3034543 := bstep (se 1 (by rfl) ⟨2275907, by rfl⟩ : syracuseStep 3034543 = 4551815) B4551815
theorem B1068575 : Blo 1064615 1068575 := bstep (se 1 (by rfl) ⟨801431, by rfl⟩ : syracuseStep 1068575 = 1602863) B1602863
theorem B23056447 : Blo 1064615 23056447 := bstep (se 1 (by rfl) ⟨17292335, by rfl⟩ : syracuseStep 23056447 = 34584671) B34584671
theorem B3035647 : Blo 1064615 3035647 := bstep (se 1 (by rfl) ⟨2276735, by rfl⟩ : syracuseStep 3035647 = 4553471) B4553471
theorem B3593159 : Blo 1064615 3593159 := bstep (se 1 (by rfl) ⟨2694869, by rfl⟩ : syracuseStep 3593159 = 5389739) B5389739
theorem B7689287 : Blo 1064615 7689287 := bstep (se 1 (by rfl) ⟨5766965, by rfl⟩ : syracuseStep 7689287 = 11533931) B11533931
theorem B38884981 : Blo 1064615 38884981 := bstep (se 5 (by rfl) ⟨1822733, by rfl⟩ : syracuseStep 38884981 = 3645467) B3645467
theorem B110810915 : Blo 1064615 110810915 := bstep (se 1 (by rfl) ⟨83108186, by rfl⟩ : syracuseStep 110810915 = 166216373) B166216373
theorem B4381199 : Blo 1064615 4381199 := bstep (se 1 (by rfl) ⟨3285899, by rfl⟩ : syracuseStep 4381199 = 6571799) B6571799
theorem B49207895 : Blo 1064615 49207895 := bstep (se 1 (by rfl) ⟨36905921, by rfl⟩ : syracuseStep 49207895 = 73811843) B73811843
theorem B4055123 : Blo 1064615 4055123 := bstep (se 1 (by rfl) ⟨3041342, by rfl⟩ : syracuseStep 4055123 = 6082685) B6082685
theorem B1597577 : Blo 1064615 1597577 := bstep (se 2 (by rfl) ⟨599091, by rfl⟩ : syracuseStep 1597577 = 1198183) B1198183
theorem B5399135 : Blo 1064615 5399135 := bstep (se 1 (by rfl) ⟨4049351, by rfl⟩ : syracuseStep 5399135 = 8098703) B8098703
theorem B2025641 : Blo 1064615 2025641 := bstep (se 2 (by rfl) ⟨759615, by rfl⟩ : syracuseStep 2025641 = 1519231) B1519231
theorem B1599935 : Blo 1064615 1599935 := bstep (se 1 (by rfl) ⟨1199951, by rfl⟩ : syracuseStep 1599935 = 2399903) B2399903
theorem B1599977 : Blo 1064615 1599977 := bstep (se 2 (by rfl) ⟨599991, by rfl⟩ : syracuseStep 1599977 = 1199983) B1199983
theorem B3599207 : Blo 1064615 3599207 := bstep (se 1 (by rfl) ⟨2699405, by rfl⟩ : syracuseStep 3599207 = 5398811) B5398811
theorem B1600607 : Blo 1064615 1600607 := bstep (se 1 (by rfl) ⟨1200455, by rfl⟩ : syracuseStep 1600607 = 2400911) B2400911
theorem B1601231 : Blo 1064615 1601231 := bstep (se 1 (by rfl) ⟨1200923, by rfl⟩ : syracuseStep 1601231 = 2401847) B2401847
theorem B1602335 : Blo 1064615 1602335 := bstep (se 1 (by rfl) ⟨1201751, by rfl⟩ : syracuseStep 1602335 = 2403503) B2403503
theorem B15365315 : Blo 1064615 15365315 := bstep (se 1 (by rfl) ⟨11523986, by rfl⟩ : syracuseStep 15365315 = 23047973) B23047973
theorem B1800103 : Blo 1064615 1800103 := bstep (se 1 (by rfl) ⟨1350077, by rfl⟩ : syracuseStep 1800103 = 2700155) B2700155
theorem B3602825 : Blo 1064615 3602825 := bstep (se 2 (by rfl) ⟨1351059, by rfl⟩ : syracuseStep 3602825 = 2702119) B2702119
theorem B3603257 : Blo 1064615 3603257 := bstep (se 2 (by rfl) ⟨1351221, by rfl⟩ : syracuseStep 3603257 = 2702443) B2702443
theorem B17267681 : Blo 1064615 17267681 := bstep (se 2 (by rfl) ⟨6475380, by rfl⟩ : syracuseStep 17267681 = 12950761) B12950761
theorem B1801271 : Blo 1064615 1801271 := bstep (se 1 (by rfl) ⟨1350953, by rfl⟩ : syracuseStep 1801271 = 2701907) B2701907
theorem B5405939 : Blo 1064615 5405939 := bstep (se 1 (by rfl) ⟨4054454, by rfl⟩ : syracuseStep 5405939 = 8108909) B8108909
theorem B212925773 : Blo 1064615 212925773 := bstep (se 3 (by rfl) ⟨39923582, by rfl⟩ : syracuseStep 212925773 = 79847165) B79847165
theorem B8094815 : Blo 1064615 8094815 := bstep (se 1 (by rfl) ⟨6071111, by rfl⟩ : syracuseStep 8094815 = 12142223) B12142223
theorem B1705855 : Blo 1064615 1705855 := bstep (se 1 (by rfl) ⟨1279391, by rfl⟩ : syracuseStep 1705855 = 2558783) B2558783
theorem B1542251 : Blo 1064615 1542251 := bstep (se 1 (by rfl) ⟨1156688, by rfl⟩ : syracuseStep 1542251 = 2313377) B2313377
theorem B2395439 : Blo 1064615 2395439 := bstep (se 1 (by rfl) ⟨1796579, by rfl⟩ : syracuseStep 2395439 = 3593159) B3593159
theorem B4558153 : Blo 1064615 4558153 := bstep (se 2 (by rfl) ⟨1709307, by rfl⟩ : syracuseStep 4558153 = 3418615) B3418615
theorem B61410959 : Blo 1064615 61410959 := bstep (se 1 (by rfl) ⟨46058219, by rfl⟩ : syracuseStep 61410959 = 92116439) B92116439
theorem B6491927 : Blo 1064615 6491927 := bstep (se 1 (by rfl) ⟨4868945, by rfl⟩ : syracuseStep 6491927 = 9737891) B9737891
theorem B2920799 : Blo 1064615 2920799 := bstep (se 1 (by rfl) ⟨2190599, by rfl⟩ : syracuseStep 2920799 = 4381199) B4381199
theorem B32805263 : Blo 1064615 32805263 := bstep (se 1 (by rfl) ⟨24603947, by rfl⟩ : syracuseStep 32805263 = 49207895) B49207895
theorem B9376211 : Blo 1064615 9376211 := bstep (se 1 (by rfl) ⟨7032158, by rfl⟩ : syracuseStep 9376211 = 14064317) B14064317
theorem B5772655 : Blo 1064615 5772655 := bstep (se 1 (by rfl) ⟨4329491, by rfl⟩ : syracuseStep 5772655 = 8658983) B8658983
theorem B30741929 : Blo 1064615 30741929 := bstep (se 2 (by rfl) ⟨11528223, by rfl⟩ : syracuseStep 30741929 = 23056447) B23056447
theorem B5117735 : Blo 1064615 5117735 := bstep (se 1 (by rfl) ⟨3838301, by rfl⟩ : syracuseStep 5117735 = 7676603) B7676603
theorem B1350427 : Blo 1064615 1350427 := bstep (se 1 (by rfl) ⟨1012820, by rfl⟩ : syracuseStep 1350427 = 2025641) B2025641
theorem B2399471 : Blo 1064615 2399471 := bstep (se 1 (by rfl) ⟨1799603, by rfl⟩ : syracuseStep 2399471 = 3599207) B3599207
theorem B51846641 : Blo 1064615 51846641 := bstep (se 2 (by rfl) ⟨19442490, by rfl⟩ : syracuseStep 51846641 = 38884981) B38884981
theorem B2400137 : Blo 1064615 2400137 := bstep (se 2 (by rfl) ⟨900051, by rfl⟩ : syracuseStep 2400137 = 1800103) B1800103
theorem B46047149 : Blo 1064615 46047149 := bstep (se 3 (by rfl) ⟨8633840, by rfl⟩ : syracuseStep 46047149 = 17267681) B17267681
theorem B23076859 : Blo 1064615 23076859 := bstep (se 1 (by rfl) ⟨17307644, by rfl⟩ : syracuseStep 23076859 = 34615289) B34615289
theorem B3416489 : Blo 1064615 3416489 := bstep (se 2 (by rfl) ⟨1281183, by rfl⟩ : syracuseStep 3416489 = 2562367) B2562367
theorem B2401883 : Blo 1064615 2401883 := bstep (se 1 (by rfl) ⟨1801412, by rfl⟩ : syracuseStep 2401883 = 3602825) B3602825
theorem B2402171 : Blo 1064615 2402171 := bstep (se 1 (by rfl) ⟨1801628, by rfl⟩ : syracuseStep 2402171 = 3603257) B3603257
theorem B2403431 : Blo 1064615 2403431 := bstep (se 1 (by rfl) ⟨1802573, by rfl⟩ : syracuseStep 2403431 = 3605147) B3605147
theorem B18230831 : Blo 1064615 18230831 := bstep (se 1 (by rfl) ⟨13673123, by rfl⟩ : syracuseStep 18230831 = 27346247) B27346247
theorem B13676201 : Blo 1064615 13676201 := bstep (se 2 (by rfl) ⟨5128575, by rfl⟩ : syracuseStep 13676201 = 10257151) B10257151
theorem B2306207 : Blo 1064615 2306207 := bstep (se 1 (by rfl) ⟨1729655, by rfl⟩ : syracuseStep 2306207 = 3459311) B3459311
theorem B73873943 : Blo 1064615 73873943 := bstep (se 1 (by rfl) ⟨55405457, by rfl⟩ : syracuseStep 73873943 = 110810915) B110810915
theorem B4046057 : Blo 1064615 4046057 := bstep (se 2 (by rfl) ⟨1517271, by rfl⟩ : syracuseStep 4046057 = 3034543) B3034543
theorem B2703415 : Blo 1064615 2703415 := bstep (se 1 (by rfl) ⟨2027561, by rfl⟩ : syracuseStep 2703415 = 4055123) B4055123
theorem B1065051 : Blo 1064615 1065051 := bstep (se 1 (by rfl) ⟨798788, by rfl⟩ : syracuseStep 1065051 = 1597577) B1597577
theorem B4047529 : Blo 1064615 4047529 := bstep (se 2 (by rfl) ⟨1517823, by rfl⟩ : syracuseStep 4047529 = 3035647) B3035647
theorem B18727703 : Blo 1064615 18727703 := bstep (se 1 (by rfl) ⟨14045777, by rfl⟩ : syracuseStep 18727703 = 28091555) B28091555
theorem B1066623 : Blo 1064615 1066623 := bstep (se 1 (by rfl) ⟨799967, by rfl⟩ : syracuseStep 1066623 = 1599935) B1599935
theorem B1066651 : Blo 1064615 1066651 := bstep (se 1 (by rfl) ⟨799988, by rfl⟩ : syracuseStep 1066651 = 1599977) B1599977
theorem B1067071 : Blo 1064615 1067071 := bstep (se 1 (by rfl) ⟨800303, by rfl⟩ : syracuseStep 1067071 = 1600607) B1600607
theorem B1067487 : Blo 1064615 1067487 := bstep (se 1 (by rfl) ⟨800615, by rfl⟩ : syracuseStep 1067487 = 1601231) B1601231
theorem B1068223 : Blo 1064615 1068223 := bstep (se 1 (by rfl) ⟨801167, by rfl⟩ : syracuseStep 1068223 = 1602335) B1602335
theorem B10243543 : Blo 1064615 10243543 := bstep (se 1 (by rfl) ⟨7682657, by rfl⟩ : syracuseStep 10243543 = 15365315) B15365315
theorem B1200847 : Blo 1064615 1200847 := bstep (se 1 (by rfl) ⟨900635, by rfl⟩ : syracuseStep 1200847 = 1801271) B1801271
theorem B5199871 : Blo 1064615 5199871 := bstep (se 1 (by rfl) ⟨3899903, by rfl⟩ : syracuseStep 5199871 = 7799807) B7799807
theorem B1923239 : Blo 1064615 1923239 := bstep (se 1 (by rfl) ⟨1442429, by rfl⟩ : syracuseStep 1923239 = 2884859) B2884859
theorem B17325551 : Blo 1064615 17325551 := bstep (se 1 (by rfl) ⟨12994163, by rfl⟩ : syracuseStep 17325551 = 25988327) B25988327
theorem B5398649 : Blo 1064615 5398649 := bstep (se 2 (by rfl) ⟨2024493, by rfl⟩ : syracuseStep 5398649 = 4048987) B4048987
theorem B222060689 : Blo 1064615 222060689 := bstep (se 2 (by rfl) ⟨83272758, by rfl⟩ : syracuseStep 222060689 = 166545517) B166545517
theorem B1138855 : Blo 1064615 1138855 := bstep (se 1 (by rfl) ⟨854141, by rfl⟩ : syracuseStep 1138855 = 1708283) B1708283
theorem B20504765 : Blo 1064615 20504765 := bstep (se 3 (by rfl) ⟨3844643, by rfl⟩ : syracuseStep 20504765 = 7689287) B7689287
theorem B1598633 : Blo 1064615 1598633 := bstep (se 2 (by rfl) ⟨599487, by rfl⟩ : syracuseStep 1598633 = 1198975) B1198975
theorem B4679677 : Blo 1064615 4679677 := bstep (se 3 (by rfl) ⟨877439, by rfl⟩ : syracuseStep 4679677 = 1754879) B1754879
theorem B4549439 : Blo 1064615 4549439 := bstep (se 1 (by rfl) ⟨3412079, by rfl⟩ : syracuseStep 4549439 = 6824159) B6824159
theorem B3599423 : Blo 1064615 3599423 := bstep (se 1 (by rfl) ⟨2699567, by rfl⟩ : syracuseStep 3599423 = 5399135) B5399135
theorem B1797383 : Blo 1064615 1797383 := bstep (se 1 (by rfl) ⟨1348037, by rfl⟩ : syracuseStep 1797383 = 2696075) B2696075
theorem B1797673 : Blo 1064615 1797673 := bstep (se 2 (by rfl) ⟨674127, by rfl⟩ : syracuseStep 1797673 = 1348255) B1348255
theorem B4747319 : Blo 1064615 4747319 := bstep (se 1 (by rfl) ⟨3560489, by rfl⟩ : syracuseStep 4747319 = 7120979) B7120979
theorem B1602215 : Blo 1064615 1602215 := bstep (se 1 (by rfl) ⟨1201661, by rfl⟩ : syracuseStep 1602215 = 2403323) B2403323
theorem B1799111 : Blo 1064615 1799111 := bstep (se 1 (by rfl) ⟨1349333, by rfl⟩ : syracuseStep 1799111 = 2698667) B2698667
theorem B7698719 : Blo 1064615 7698719 := bstep (se 1 (by rfl) ⟨5774039, by rfl⟩ : syracuseStep 7698719 = 11548079) B11548079
theorem B3603959 : Blo 1064615 3603959 := bstep (se 1 (by rfl) ⟨2702969, by rfl⟩ : syracuseStep 3603959 = 5405939) B5405939
theorem B141950515 : Blo 1064615 141950515 := bstep (se 1 (by rfl) ⟨106462886, by rfl⟩ : syracuseStep 141950515 = 212925773) B212925773
theorem B3604553 : Blo 1064615 3604553 := bstep (se 2 (by rfl) ⟨1351707, by rfl⟩ : syracuseStep 3604553 = 2703415) B2703415
theorem B12485135 : Blo 1064615 12485135 := bstep (se 1 (by rfl) ⟨9363851, by rfl⟩ : syracuseStep 12485135 = 18727703) B18727703
theorem B4327951 : Blo 1064615 4327951 := bstep (se 1 (by rfl) ⟨3245963, by rfl⟩ : syracuseStep 4327951 = 6491927) B6491927
theorem B3411823 : Blo 1064615 3411823 := bstep (se 1 (by rfl) ⟨2558867, by rfl⟩ : syracuseStep 3411823 = 5117735) B5117735
theorem B1282159 : Blo 1064615 1282159 := bstep (se 1 (by rfl) ⟨961619, by rfl⟩ : syracuseStep 1282159 = 1923239) B1923239
theorem B2396897 : Blo 1064615 2396897 := bstep (se 2 (by rfl) ⟨898836, by rfl⟩ : syracuseStep 2396897 = 1797673) B1797673
theorem B13669843 : Blo 1064615 13669843 := bstep (se 1 (by rfl) ⟨10252382, by rfl⟩ : syracuseStep 13669843 = 20504765) B20504765
theorem B2399615 : Blo 1064615 2399615 := bstep (se 1 (by rfl) ⟨1799711, by rfl⟩ : syracuseStep 2399615 = 3599423) B3599423
theorem B9117467 : Blo 1064615 9117467 := bstep (se 1 (by rfl) ⟨6838100, by rfl⟩ : syracuseStep 9117467 = 13676201) B13676201
theorem B2697371 : Blo 1064615 2697371 := bstep (se 1 (by rfl) ⟨2023028, by rfl⟩ : syracuseStep 2697371 = 4046057) B4046057
theorem B2402639 : Blo 1064615 2402639 := bstep (se 1 (by rfl) ⟨1801979, by rfl⟩ : syracuseStep 2402639 = 3603959) B3603959
theorem B1518473 : Blo 1064615 1518473 := bstep (se 2 (by rfl) ⟨569427, by rfl⟩ : syracuseStep 1518473 = 1138855) B1138855
theorem B40940639 : Blo 1064615 40940639 := bstep (se 1 (by rfl) ⟨30705479, by rfl⟩ : syracuseStep 40940639 = 61410959) B61410959
theorem B2274473 : Blo 1064615 2274473 := bstep (se 2 (by rfl) ⟨852927, by rfl⟩ : syracuseStep 2274473 = 1705855) B1705855
theorem B21870175 : Blo 1064615 21870175 := bstep (se 1 (by rfl) ⟨16402631, by rfl⟩ : syracuseStep 21870175 = 32805263) B32805263
theorem B20494619 : Blo 1064615 20494619 := bstep (se 1 (by rfl) ⟨15370964, by rfl⟩ : syracuseStep 20494619 = 30741929) B30741929
theorem B6077537 : Blo 1064615 6077537 := bstep (se 2 (by rfl) ⟨2279076, by rfl⟩ : syracuseStep 6077537 = 4558153) B4558153
theorem B11550367 : Blo 1064615 11550367 := bstep (se 1 (by rfl) ⟨8662775, by rfl⟩ : syracuseStep 11550367 = 17325551) B17325551
theorem B2277659 : Blo 1064615 2277659 := bstep (se 1 (by rfl) ⟨1708244, by rfl⟩ : syracuseStep 2277659 = 3416489) B3416489
theorem B4112669 : Blo 1064615 4112669 := bstep (se 3 (by rfl) ⟨771125, by rfl⟩ : syracuseStep 4112669 = 1542251) B1542251
theorem B1065755 : Blo 1064615 1065755 := bstep (se 1 (by rfl) ⟨799316, by rfl⟩ : syracuseStep 1065755 = 1598633) B1598633
theorem B3032959 : Blo 1064615 3032959 := bstep (se 1 (by rfl) ⟨2274719, by rfl⟩ : syracuseStep 3032959 = 4549439) B4549439
theorem B1198255 : Blo 1064615 1198255 := bstep (se 1 (by rfl) ⟨898691, by rfl⟩ : syracuseStep 1198255 = 1797383) B1797383
theorem B6933161 : Blo 1064615 6933161 := bstep (se 2 (by rfl) ⟨2599935, by rfl⟩ : syracuseStep 6933161 = 5199871) B5199871
theorem B3164879 : Blo 1064615 3164879 := bstep (se 1 (by rfl) ⟨2373659, by rfl⟩ : syracuseStep 3164879 = 4747319) B4747319
theorem B1068143 : Blo 1064615 1068143 := bstep (se 1 (by rfl) ⟨801107, by rfl⟩ : syracuseStep 1068143 = 1602215) B1602215
theorem B1199407 : Blo 1064615 1199407 := bstep (se 1 (by rfl) ⟨899555, by rfl⟩ : syracuseStep 1199407 = 1799111) B1799111
theorem B5132479 : Blo 1064615 5132479 := bstep (se 1 (by rfl) ⟨3849359, by rfl⟩ : syracuseStep 5132479 = 7698719) B7698719
theorem B24958277 : Blo 1064615 24958277 := bstep (se 4 (by rfl) ⟨2339838, by rfl⟩ : syracuseStep 24958277 = 4679677) B4679677
theorem B5396543 : Blo 1064615 5396543 := bstep (se 1 (by rfl) ⟨4047407, by rfl⟩ : syracuseStep 5396543 = 8094815) B8094815
theorem B5396705 : Blo 1064615 5396705 := bstep (se 2 (by rfl) ⟨2023764, by rfl⟩ : syracuseStep 5396705 = 4047529) B4047529
theorem B7788797 : Blo 1064615 7788797 := bstep (se 3 (by rfl) ⟨1460399, by rfl⟩ : syracuseStep 7788797 = 2920799) B2920799
theorem B1596959 : Blo 1064615 1596959 := bstep (se 1 (by rfl) ⟨1197719, by rfl⟩ : syracuseStep 1596959 = 2395439) B2395439
theorem B6250807 : Blo 1064615 6250807 := bstep (se 1 (by rfl) ⟨4688105, by rfl⟩ : syracuseStep 6250807 = 9376211) B9376211
theorem B13658057 : Blo 1064615 13658057 := bstep (se 2 (by rfl) ⟨5121771, by rfl⟩ : syracuseStep 13658057 = 10243543) B10243543
theorem B1599647 : Blo 1064615 1599647 := bstep (se 1 (by rfl) ⟨1199735, by rfl⟩ : syracuseStep 1599647 = 2399471) B2399471
theorem B34564427 : Blo 1064615 34564427 := bstep (se 1 (by rfl) ⟨25923320, by rfl⟩ : syracuseStep 34564427 = 51846641) B51846641
theorem B1600091 : Blo 1064615 1600091 := bstep (se 1 (by rfl) ⟨1200068, by rfl⟩ : syracuseStep 1600091 = 2400137) B2400137
theorem B30698099 : Blo 1064615 30698099 := bstep (se 1 (by rfl) ⟨23023574, by rfl⟩ : syracuseStep 30698099 = 46047149) B46047149
theorem B3599099 : Blo 1064615 3599099 := bstep (se 1 (by rfl) ⟨2699324, by rfl⟩ : syracuseStep 3599099 = 5398649) B5398649
theorem B148040459 : Blo 1064615 148040459 := bstep (se 1 (by rfl) ⟨111030344, by rfl⟩ : syracuseStep 148040459 = 222060689) B222060689
theorem B1601129 : Blo 1064615 1601129 := bstep (se 2 (by rfl) ⟨600423, by rfl⟩ : syracuseStep 1601129 = 1200847) B1200847
theorem B1601255 : Blo 1064615 1601255 := bstep (se 1 (by rfl) ⟨1200941, by rfl⟩ : syracuseStep 1601255 = 2401883) B2401883
theorem B1601447 : Blo 1064615 1601447 := bstep (se 1 (by rfl) ⟨1201085, by rfl⟩ : syracuseStep 1601447 = 2402171) B2402171
theorem B7696873 : Blo 1064615 7696873 := bstep (se 2 (by rfl) ⟨2886327, by rfl⟩ : syracuseStep 7696873 = 5772655) B5772655
theorem B1602287 : Blo 1064615 1602287 := bstep (se 1 (by rfl) ⟨1201715, by rfl⟩ : syracuseStep 1602287 = 2403431) B2403431
theorem B12153887 : Blo 1064615 12153887 := bstep (se 1 (by rfl) ⟨9115415, by rfl⟩ : syracuseStep 12153887 = 18230831) B18230831
theorem B1537471 : Blo 1064615 1537471 := bstep (se 1 (by rfl) ⟨1153103, by rfl⟩ : syracuseStep 1537471 = 2306207) B2306207
theorem B1800569 : Blo 1064615 1800569 := bstep (se 2 (by rfl) ⟨675213, by rfl⟩ : syracuseStep 1800569 = 1350427) B1350427
theorem B49249295 : Blo 1064615 49249295 := bstep (se 1 (by rfl) ⟨36936971, by rfl⟩ : syracuseStep 49249295 = 73873943) B73873943
theorem B189267353 : Blo 1064615 189267353 := bstep (se 2 (by rfl) ⟨70975257, by rfl⟩ : syracuseStep 189267353 = 141950515) B141950515
theorem B30769145 : Blo 1064615 30769145 := bstep (se 2 (by rfl) ⟨11538429, by rfl⟩ : syracuseStep 30769145 = 23076859) B23076859
theorem B33293693 : Blo 1064615 33293693 := bstep (se 3 (by rfl) ⟨6242567, by rfl⟩ : syracuseStep 33293693 = 12485135) B12485135
theorem B5770601 : Blo 1064615 5770601 := bstep (se 2 (by rfl) ⟨2163975, by rfl⟩ : syracuseStep 5770601 = 4327951) B4327951
theorem B10262497 : Blo 1064615 10262497 := bstep (se 2 (by rfl) ⟨3848436, by rfl⟩ : syracuseStep 10262497 = 7696873) B7696873
theorem B23042951 : Blo 1064615 23042951 := bstep (se 1 (by rfl) ⟨17282213, by rfl⟩ : syracuseStep 23042951 = 34564427) B34564427
theorem B18488429 : Blo 1064615 18488429 := bstep (se 3 (by rfl) ⟨3466580, by rfl⟩ : syracuseStep 18488429 = 6933161) B6933161
theorem B2399399 : Blo 1064615 2399399 := bstep (se 1 (by rfl) ⟨1799549, by rfl⟩ : syracuseStep 2399399 = 3599099) B3599099
theorem B18226457 : Blo 1064615 18226457 := bstep (se 2 (by rfl) ⟨6834921, by rfl⟩ : syracuseStep 18226457 = 13669843) B13669843
theorem B8102591 : Blo 1064615 8102591 := bstep (se 1 (by rfl) ⟨6076943, by rfl⟩ : syracuseStep 8102591 = 12153887) B12153887
theorem B1516315 : Blo 1064615 1516315 := bstep (se 1 (by rfl) ⟨1137236, by rfl⟩ : syracuseStep 1516315 = 2274473) B2274473
theorem B2403035 : Blo 1064615 2403035 := bstep (se 1 (by rfl) ⟨1802276, by rfl⟩ : syracuseStep 2403035 = 3604553) B3604553
theorem B1518439 : Blo 1064615 1518439 := bstep (se 1 (by rfl) ⟨1138829, by rfl⟩ : syracuseStep 1518439 = 2277659) B2277659
theorem B8334409 : Blo 1064615 8334409 := bstep (se 2 (by rfl) ⟨3125403, by rfl⟩ : syracuseStep 8334409 = 6250807) B6250807
theorem B4043945 : Blo 1064615 4043945 := bstep (se 2 (by rfl) ⟨1516479, by rfl⟩ : syracuseStep 4043945 = 3032959) B3032959
theorem B5192531 : Blo 1064615 5192531 := bstep (se 1 (by rfl) ⟨3894398, by rfl⟩ : syracuseStep 5192531 = 7788797) B7788797
theorem B1064639 : Blo 1064615 1064639 := bstep (se 1 (by rfl) ⟨798479, by rfl⟩ : syracuseStep 1064639 = 1596959) B1596959
theorem B6078311 : Blo 1064615 6078311 := bstep (se 1 (by rfl) ⟨4558733, by rfl⟩ : syracuseStep 6078311 = 9117467) B9117467
theorem B1066431 : Blo 1064615 1066431 := bstep (se 1 (by rfl) ⟨799823, by rfl⟩ : syracuseStep 1066431 = 1599647) B1599647
theorem B1066727 : Blo 1064615 1066727 := bstep (se 1 (by rfl) ⟨800045, by rfl⟩ : syracuseStep 1066727 = 1600091) B1600091
theorem B20465399 : Blo 1064615 20465399 := bstep (se 1 (by rfl) ⟨15349049, by rfl⟩ : syracuseStep 20465399 = 30698099) B30698099
theorem B8439677 : Blo 1064615 8439677 := bstep (se 3 (by rfl) ⟨1582439, by rfl⟩ : syracuseStep 8439677 = 3164879) B3164879
theorem B2049961 : Blo 1064615 2049961 := bstep (se 2 (by rfl) ⟨768735, by rfl⟩ : syracuseStep 2049961 = 1537471) B1537471
theorem B4049261 : Blo 1064615 4049261 := bstep (se 3 (by rfl) ⟨759236, by rfl⟩ : syracuseStep 4049261 = 1518473) B1518473
theorem B1067419 : Blo 1064615 1067419 := bstep (se 1 (by rfl) ⟨800564, by rfl⟩ : syracuseStep 1067419 = 1601129) B1601129
theorem B1067503 : Blo 1064615 1067503 := bstep (se 1 (by rfl) ⟨800627, by rfl⟩ : syracuseStep 1067503 = 1601255) B1601255
theorem B1067631 : Blo 1064615 1067631 := bstep (se 1 (by rfl) ⟨800723, by rfl⟩ : syracuseStep 1067631 = 1601447) B1601447
theorem B1068191 : Blo 1064615 1068191 := bstep (se 1 (by rfl) ⟨801143, by rfl⟩ : syracuseStep 1068191 = 1602287) B1602287
theorem B1200379 : Blo 1064615 1200379 := bstep (se 1 (by rfl) ⟨900284, by rfl⟩ : syracuseStep 1200379 = 1800569) B1800569
theorem B4051691 : Blo 1064615 4051691 := bstep (se 1 (by rfl) ⟨3038768, by rfl⟩ : syracuseStep 4051691 = 6077537) B6077537
theorem B126178235 : Blo 1064615 126178235 := bstep (se 1 (by rfl) ⟨94633676, by rfl⟩ : syracuseStep 126178235 = 189267353) B189267353
theorem B2741779 : Blo 1064615 2741779 := bstep (se 1 (by rfl) ⟨2056334, by rfl⟩ : syracuseStep 2741779 = 4112669) B4112669
theorem B6838181 : Blo 1064615 6838181 := bstep (se 4 (by rfl) ⟨641079, by rfl⟩ : syracuseStep 6838181 = 1282159) B1282159
theorem B1597673 : Blo 1064615 1597673 := bstep (se 2 (by rfl) ⟨599127, by rfl⟩ : syracuseStep 1597673 = 1198255) B1198255
theorem B1597931 : Blo 1064615 1597931 := bstep (se 1 (by rfl) ⟨1198448, by rfl⟩ : syracuseStep 1597931 = 2396897) B2396897
theorem B16638851 : Blo 1064615 16638851 := bstep (se 1 (by rfl) ⟨12479138, by rfl⟩ : syracuseStep 16638851 = 24958277) B24958277
theorem B3597695 : Blo 1064615 3597695 := bstep (se 1 (by rfl) ⟨2698271, by rfl⟩ : syracuseStep 3597695 = 5396543) B5396543
theorem B3597803 : Blo 1064615 3597803 := bstep (se 1 (by rfl) ⟨2698352, by rfl⟩ : syracuseStep 3597803 = 5396705) B5396705
theorem B1599209 : Blo 1064615 1599209 := bstep (se 2 (by rfl) ⟨599703, by rfl⟩ : syracuseStep 1599209 = 1199407) B1199407
theorem B1599743 : Blo 1064615 1599743 := bstep (se 1 (by rfl) ⟨1199807, by rfl⟩ : syracuseStep 1599743 = 2399615) B2399615
theorem B4549097 : Blo 1064615 4549097 := bstep (se 2 (by rfl) ⟨1705911, by rfl⟩ : syracuseStep 4549097 = 3411823) B3411823
theorem B6843305 : Blo 1064615 6843305 := bstep (se 2 (by rfl) ⟨2566239, by rfl⟩ : syracuseStep 6843305 = 5132479) B5132479
theorem B9105371 : Blo 1064615 9105371 := bstep (se 1 (by rfl) ⟨6829028, by rfl⟩ : syracuseStep 9105371 = 13658057) B13658057
theorem B1798247 : Blo 1064615 1798247 := bstep (se 1 (by rfl) ⟨1348685, by rfl⟩ : syracuseStep 1798247 = 2697371) B2697371
theorem B1601759 : Blo 1064615 1601759 := bstep (se 1 (by rfl) ⟨1201319, by rfl⟩ : syracuseStep 1601759 = 2402639) B2402639
theorem B98693639 : Blo 1064615 98693639 := bstep (se 1 (by rfl) ⟨74020229, by rfl⟩ : syracuseStep 98693639 = 148040459) B148040459
theorem B29160233 : Blo 1064615 29160233 := bstep (se 2 (by rfl) ⟨10935087, by rfl⟩ : syracuseStep 29160233 = 21870175) B21870175
theorem B27293759 : Blo 1064615 27293759 := bstep (se 1 (by rfl) ⟨20470319, by rfl⟩ : syracuseStep 27293759 = 40940639) B40940639
theorem B13663079 : Blo 1064615 13663079 := bstep (se 1 (by rfl) ⟨10247309, by rfl⟩ : syracuseStep 13663079 = 20494619) B20494619
theorem B32832863 : Blo 1064615 32832863 := bstep (se 1 (by rfl) ⟨24624647, by rfl⟩ : syracuseStep 32832863 = 49249295) B49249295
theorem B15400489 : Blo 1064615 15400489 := bstep (se 2 (by rfl) ⟨5775183, by rfl⟩ : syracuseStep 15400489 = 11550367) B11550367
theorem B20512763 : Blo 1064615 20512763 := bstep (se 1 (by rfl) ⟨15384572, by rfl⟩ : syracuseStep 20512763 = 30769145) B30769145
theorem B84118823 : Blo 1064615 84118823 := bstep (se 1 (by rfl) ⟨63089117, by rfl⟩ : syracuseStep 84118823 = 126178235) B126178235
theorem B4558787 : Blo 1064615 4558787 := bstep (se 1 (by rfl) ⟨3419090, by rfl⟩ : syracuseStep 4558787 = 6838181) B6838181
theorem B11112545 : Blo 1064615 11112545 := bstep (se 2 (by rfl) ⟨4167204, by rfl⟩ : syracuseStep 11112545 = 8334409) B8334409
theorem B12325619 : Blo 1064615 12325619 := bstep (se 1 (by rfl) ⟨9244214, by rfl⟩ : syracuseStep 12325619 = 18488429) B18488429
theorem B2398463 : Blo 1064615 2398463 := bstep (se 1 (by rfl) ⟨1798847, by rfl⟩ : syracuseStep 2398463 = 3597695) B3597695
theorem B2398535 : Blo 1064615 2398535 := bstep (se 1 (by rfl) ⟨1798901, by rfl⟩ : syracuseStep 2398535 = 3597803) B3597803
theorem B4562203 : Blo 1064615 4562203 := bstep (se 1 (by rfl) ⟨3421652, by rfl⟩ : syracuseStep 4562203 = 6843305) B6843305
theorem B6070247 : Blo 1064615 6070247 := bstep (se 1 (by rfl) ⟨4552685, by rfl⟩ : syracuseStep 6070247 = 9105371) B9105371
theorem B19440155 : Blo 1064615 19440155 := bstep (se 1 (by rfl) ⟨14580116, by rfl⟩ : syracuseStep 19440155 = 29160233) B29160233
theorem B2695963 : Blo 1064615 2695963 := bstep (se 1 (by rfl) ⟨2021972, by rfl⟩ : syracuseStep 2695963 = 4043945) B4043945
theorem B18195839 : Blo 1064615 18195839 := bstep (se 1 (by rfl) ⟨13646879, by rfl⟩ : syracuseStep 18195839 = 27293759) B27293759
theorem B13675175 : Blo 1064615 13675175 := bstep (se 1 (by rfl) ⟨10256381, by rfl⟩ : syracuseStep 13675175 = 20512763) B20512763
theorem B22195795 : Blo 1064615 22195795 := bstep (se 1 (by rfl) ⟨16646846, by rfl⟩ : syracuseStep 22195795 = 33293693) B33293693
theorem B13643599 : Blo 1064615 13643599 := bstep (se 1 (by rfl) ⟨10232699, by rfl⟩ : syracuseStep 13643599 = 20465399) B20465399
theorem B2699507 : Blo 1064615 2699507 := bstep (se 1 (by rfl) ⟨2024630, by rfl⟩ : syracuseStep 2699507 = 4049261) B4049261
theorem B3847067 : Blo 1064615 3847067 := bstep (se 1 (by rfl) ⟨2885300, by rfl⟩ : syracuseStep 3847067 = 5770601) B5770601
theorem B2733281 : Blo 1064615 2733281 := bstep (se 2 (by rfl) ⟨1024980, by rfl⟩ : syracuseStep 2733281 = 2049961) B2049961
theorem B2701127 : Blo 1064615 2701127 := bstep (se 1 (by rfl) ⟨2025845, by rfl⟩ : syracuseStep 2701127 = 4051691) B4051691
theorem B1065115 : Blo 1064615 1065115 := bstep (se 1 (by rfl) ⟨798836, by rfl⟩ : syracuseStep 1065115 = 1597673) B1597673
theorem B1065287 : Blo 1064615 1065287 := bstep (se 1 (by rfl) ⟨798965, by rfl⟩ : syracuseStep 1065287 = 1597931) B1597931
theorem B11092567 : Blo 1064615 11092567 := bstep (se 1 (by rfl) ⟨8319425, by rfl⟩ : syracuseStep 11092567 = 16638851) B16638851
theorem B1066139 : Blo 1064615 1066139 := bstep (se 1 (by rfl) ⟨799604, by rfl⟩ : syracuseStep 1066139 = 1599209) B1599209
theorem B1066495 : Blo 1064615 1066495 := bstep (se 1 (by rfl) ⟨799871, by rfl⟩ : syracuseStep 1066495 = 1599743) B1599743
theorem B3032731 : Blo 1064615 3032731 := bstep (se 1 (by rfl) ⟨2274548, by rfl⟩ : syracuseStep 3032731 = 4549097) B4549097
theorem B3655705 : Blo 1064615 3655705 := bstep (se 2 (by rfl) ⟨1370889, by rfl⟩ : syracuseStep 3655705 = 2741779) B2741779
theorem B13683329 : Blo 1064615 13683329 := bstep (se 2 (by rfl) ⟨5131248, by rfl⟩ : syracuseStep 13683329 = 10262497) B10262497
theorem B1198831 : Blo 1064615 1198831 := bstep (se 1 (by rfl) ⟨899123, by rfl⟩ : syracuseStep 1198831 = 1798247) B1798247
theorem B1067839 : Blo 1064615 1067839 := bstep (se 1 (by rfl) ⟨800879, by rfl⟩ : syracuseStep 1067839 = 1601759) B1601759
theorem B3461687 : Blo 1064615 3461687 := bstep (se 1 (by rfl) ⟨2596265, by rfl⟩ : syracuseStep 3461687 = 5192531) B5192531
theorem B20533985 : Blo 1064615 20533985 := bstep (se 2 (by rfl) ⟨7700244, by rfl⟩ : syracuseStep 20533985 = 15400489) B15400489
theorem B4052207 : Blo 1064615 4052207 := bstep (se 1 (by rfl) ⟨3039155, by rfl⟩ : syracuseStep 4052207 = 6078311) B6078311
theorem B2021753 : Blo 1064615 2021753 := bstep (se 2 (by rfl) ⟨758157, by rfl⟩ : syracuseStep 2021753 = 1516315) B1516315
theorem B5626451 : Blo 1064615 5626451 := bstep (se 1 (by rfl) ⟨4219838, by rfl⟩ : syracuseStep 5626451 = 8439677) B8439677
theorem B2024585 : Blo 1064615 2024585 := bstep (se 2 (by rfl) ⟨759219, by rfl⟩ : syracuseStep 2024585 = 1518439) B1518439
theorem B15361967 : Blo 1064615 15361967 := bstep (se 1 (by rfl) ⟨11521475, by rfl⟩ : syracuseStep 15361967 = 23042951) B23042951
theorem B1599599 : Blo 1064615 1599599 := bstep (se 1 (by rfl) ⟨1199699, by rfl⟩ : syracuseStep 1599599 = 2399399) B2399399
theorem B12150971 : Blo 1064615 12150971 := bstep (se 1 (by rfl) ⟨9113228, by rfl⟩ : syracuseStep 12150971 = 18226457) B18226457
theorem B1600505 : Blo 1064615 1600505 := bstep (se 2 (by rfl) ⟨600189, by rfl⟩ : syracuseStep 1600505 = 1200379) B1200379
theorem B5401727 : Blo 1064615 5401727 := bstep (se 1 (by rfl) ⟨4051295, by rfl⟩ : syracuseStep 5401727 = 8102591) B8102591
theorem B1602023 : Blo 1064615 1602023 := bstep (se 1 (by rfl) ⟨1201517, by rfl⟩ : syracuseStep 1602023 = 2403035) B2403035
theorem B65795759 : Blo 1064615 65795759 := bstep (se 1 (by rfl) ⟨49346819, by rfl⟩ : syracuseStep 65795759 = 98693639) B98693639
theorem B9108719 : Blo 1064615 9108719 := bstep (se 1 (by rfl) ⟨6831539, by rfl⟩ : syracuseStep 9108719 = 13663079) B13663079
theorem B21888575 : Blo 1064615 21888575 := bstep (se 1 (by rfl) ⟨16416431, by rfl⟩ : syracuseStep 21888575 = 32832863) B32832863
theorem B32868317 : Blo 1064615 32868317 := bstep (se 3 (by rfl) ⟨6162809, by rfl⟩ : syracuseStep 32868317 = 12325619) B12325619
theorem B7408363 : Blo 1064615 7408363 := bstep (se 1 (by rfl) ⟨5556272, by rfl⟩ : syracuseStep 7408363 = 11112545) B11112545
theorem B1347835 : Blo 1064615 1347835 := bstep (se 1 (by rfl) ⟨1010876, by rfl⟩ : syracuseStep 1347835 = 2021753) B2021753
theorem B29594393 : Blo 1064615 29594393 := bstep (se 2 (by rfl) ⟨11097897, by rfl⟩ : syracuseStep 29594393 = 22195795) B22195795
theorem B18191465 : Blo 1064615 18191465 := bstep (se 2 (by rfl) ⟨6821799, by rfl⟩ : syracuseStep 18191465 = 13643599) B13643599
theorem B1349723 : Blo 1064615 1349723 := bstep (se 1 (by rfl) ⟨1012292, by rfl⟩ : syracuseStep 1349723 = 2024585) B2024585
theorem B12130559 : Blo 1064615 12130559 := bstep (se 1 (by rfl) ⟨9097919, by rfl⟩ : syracuseStep 12130559 = 18195839) B18195839
theorem B8100647 : Blo 1064615 8100647 := bstep (se 1 (by rfl) ⟨6075485, by rfl⟩ : syracuseStep 8100647 = 12150971) B12150971
theorem B9116783 : Blo 1064615 9116783 := bstep (se 1 (by rfl) ⟨6837587, by rfl⟩ : syracuseStep 9116783 = 13675175) B13675175
theorem B2564711 : Blo 1064615 2564711 := bstep (se 1 (by rfl) ⟨1923533, by rfl⟩ : syracuseStep 2564711 = 3847067) B3847067
theorem B6072479 : Blo 1064615 6072479 := bstep (se 1 (by rfl) ⟨4554359, by rfl⟩ : syracuseStep 6072479 = 9108719) B9108719
theorem B14592383 : Blo 1064615 14592383 := bstep (se 1 (by rfl) ⟨10944287, by rfl⟩ : syracuseStep 14592383 = 21888575) B21888575
theorem B14790089 : Blo 1064615 14790089 := bstep (se 2 (by rfl) ⟨5546283, by rfl⟩ : syracuseStep 14790089 = 11092567) B11092567
theorem B9122219 : Blo 1064615 9122219 := bstep (se 1 (by rfl) ⟨6841664, by rfl⟩ : syracuseStep 9122219 = 13683329) B13683329
theorem B56079215 : Blo 1064615 56079215 := bstep (se 1 (by rfl) ⟨42059411, by rfl⟩ : syracuseStep 56079215 = 84118823) B84118823
theorem B4043641 : Blo 1064615 4043641 := bstep (se 2 (by rfl) ⟨1516365, by rfl⟩ : syracuseStep 4043641 = 3032731) B3032731
theorem B2307791 : Blo 1064615 2307791 := bstep (se 1 (by rfl) ⟨1730843, by rfl⟩ : syracuseStep 2307791 = 3461687) B3461687
theorem B2701471 : Blo 1064615 2701471 := bstep (se 1 (by rfl) ⟨2026103, by rfl⟩ : syracuseStep 2701471 = 4052207) B4052207
theorem B3750967 : Blo 1064615 3750967 := bstep (se 1 (by rfl) ⟨2813225, by rfl⟩ : syracuseStep 3750967 = 5626451) B5626451
theorem B4046831 : Blo 1064615 4046831 := bstep (se 1 (by rfl) ⟨3035123, by rfl⟩ : syracuseStep 4046831 = 6070247) B6070247
theorem B12960103 : Blo 1064615 12960103 := bstep (se 1 (by rfl) ⟨9720077, by rfl⟩ : syracuseStep 12960103 = 19440155) B19440155
theorem B10241311 : Blo 1064615 10241311 := bstep (se 1 (by rfl) ⟨7680983, by rfl⟩ : syracuseStep 10241311 = 15361967) B15361967
theorem B1066399 : Blo 1064615 1066399 := bstep (se 1 (by rfl) ⟨799799, by rfl⟩ : syracuseStep 1066399 = 1599599) B1599599
theorem B1067003 : Blo 1064615 1067003 := bstep (se 1 (by rfl) ⟨800252, by rfl⟩ : syracuseStep 1067003 = 1600505) B1600505
theorem B1068015 : Blo 1064615 1068015 := bstep (se 1 (by rfl) ⟨801011, by rfl⟩ : syracuseStep 1068015 = 1602023) B1602023
theorem B1822187 : Blo 1064615 1822187 := bstep (se 1 (by rfl) ⟨1366640, by rfl⟩ : syracuseStep 1822187 = 2733281) B2733281
theorem B43863839 : Blo 1064615 43863839 := bstep (se 1 (by rfl) ⟨32897879, by rfl⟩ : syracuseStep 43863839 = 65795759) B65795759
theorem B6082937 : Blo 1064615 6082937 := bstep (se 2 (by rfl) ⟨2281101, by rfl⟩ : syracuseStep 6082937 = 4562203) B4562203
theorem B3594617 : Blo 1064615 3594617 := bstep (se 2 (by rfl) ⟨1347981, by rfl⟩ : syracuseStep 3594617 = 2695963) B2695963
theorem B3039191 : Blo 1064615 3039191 := bstep (se 1 (by rfl) ⟨2279393, by rfl⟩ : syracuseStep 3039191 = 4558787) B4558787
theorem B4874273 : Blo 1064615 4874273 := bstep (se 2 (by rfl) ⟨1827852, by rfl⟩ : syracuseStep 4874273 = 3655705) B3655705
theorem B13689323 : Blo 1064615 13689323 := bstep (se 1 (by rfl) ⟨10266992, by rfl⟩ : syracuseStep 13689323 = 20533985) B20533985
theorem B1598441 : Blo 1064615 1598441 := bstep (se 2 (by rfl) ⟨599415, by rfl⟩ : syracuseStep 1598441 = 1198831) B1198831
theorem B1598975 : Blo 1064615 1598975 := bstep (se 1 (by rfl) ⟨1199231, by rfl⟩ : syracuseStep 1598975 = 2398463) B2398463
theorem B1599023 : Blo 1064615 1599023 := bstep (se 1 (by rfl) ⟨1199267, by rfl⟩ : syracuseStep 1599023 = 2398535) B2398535
theorem B3601151 : Blo 1064615 3601151 := bstep (se 1 (by rfl) ⟨2700863, by rfl⟩ : syracuseStep 3601151 = 5401727) B5401727
theorem B1799671 : Blo 1064615 1799671 := bstep (se 1 (by rfl) ⟨1349753, by rfl⟩ : syracuseStep 1799671 = 2699507) B2699507
theorem B1800751 : Blo 1064615 1800751 := bstep (se 1 (by rfl) ⟨1350563, by rfl⟩ : syracuseStep 1800751 = 2701127) B2701127
theorem B19729595 : Blo 1064615 19729595 := bstep (se 1 (by rfl) ⟨14797196, by rfl⟩ : syracuseStep 19729595 = 29594393) B29594393
theorem B12127643 : Blo 1064615 12127643 := bstep (se 1 (by rfl) ⟨9095732, by rfl⟩ : syracuseStep 12127643 = 18191465) B18191465
theorem B2396411 : Blo 1064615 2396411 := bstep (se 1 (by rfl) ⟨1797308, by rfl⟩ : syracuseStep 2396411 = 3594617) B3594617
theorem B3249515 : Blo 1064615 3249515 := bstep (se 1 (by rfl) ⟨2437136, by rfl⟩ : syracuseStep 3249515 = 4874273) B4874273
theorem B1709807 : Blo 1064615 1709807 := bstep (se 1 (by rfl) ⟨1282355, by rfl⟩ : syracuseStep 1709807 = 2564711) B2564711
theorem B2399561 : Blo 1064615 2399561 := bstep (se 2 (by rfl) ⟨899835, by rfl⟩ : syracuseStep 2399561 = 1799671) B1799671
theorem B2400767 : Blo 1064615 2400767 := bstep (se 1 (by rfl) ⟨1800575, by rfl⟩ : syracuseStep 2400767 = 3601151) B3601151
theorem B2401001 : Blo 1064615 2401001 := bstep (se 2 (by rfl) ⟨900375, by rfl⟩ : syracuseStep 2401001 = 1800751) B1800751
theorem B4859165 : Blo 1064615 4859165 := bstep (se 3 (by rfl) ⟨911093, by rfl⟩ : syracuseStep 4859165 = 1822187) B1822187
theorem B2697887 : Blo 1064615 2697887 := bstep (se 1 (by rfl) ⟨2023415, by rfl⟩ : syracuseStep 2697887 = 4046831) B4046831
theorem B17280137 : Blo 1064615 17280137 := bstep (se 2 (by rfl) ⟨6480051, by rfl⟩ : syracuseStep 17280137 = 12960103) B12960103
theorem B29242559 : Blo 1064615 29242559 := bstep (se 1 (by rfl) ⟨21931919, by rfl⟩ : syracuseStep 29242559 = 43863839) B43863839
theorem B9877817 : Blo 1064615 9877817 := bstep (se 2 (by rfl) ⟨3704181, by rfl⟩ : syracuseStep 9877817 = 7408363) B7408363
theorem B6077855 : Blo 1064615 6077855 := bstep (se 1 (by rfl) ⟨4558391, by rfl⟩ : syracuseStep 6077855 = 9116783) B9116783
theorem B20005157 : Blo 1064615 20005157 := bstep (se 4 (by rfl) ⟨1875483, by rfl⟩ : syracuseStep 20005157 = 3750967) B3750967
theorem B9126215 : Blo 1064615 9126215 := bstep (se 1 (by rfl) ⟨6844661, by rfl⟩ : syracuseStep 9126215 = 13689323) B13689323
theorem B1065627 : Blo 1064615 1065627 := bstep (se 1 (by rfl) ⟨799220, by rfl⟩ : syracuseStep 1065627 = 1598441) B1598441
theorem B1065983 : Blo 1064615 1065983 := bstep (se 1 (by rfl) ⟨799487, by rfl⟩ : syracuseStep 1065983 = 1598975) B1598975
theorem B1066015 : Blo 1064615 1066015 := bstep (se 1 (by rfl) ⟨799511, by rfl⟩ : syracuseStep 1066015 = 1599023) B1599023
theorem B5391521 : Blo 1064615 5391521 := bstep (se 2 (by rfl) ⟨2021820, by rfl⟩ : syracuseStep 5391521 = 4043641) B4043641
theorem B4048319 : Blo 1064615 4048319 := bstep (se 1 (by rfl) ⟨3036239, by rfl⟩ : syracuseStep 4048319 = 6072479) B6072479
theorem B6081479 : Blo 1064615 6081479 := bstep (se 1 (by rfl) ⟨4561109, by rfl⟩ : syracuseStep 6081479 = 9122219) B9122219
theorem B21912211 : Blo 1064615 21912211 := bstep (se 1 (by rfl) ⟨16434158, by rfl⟩ : syracuseStep 21912211 = 32868317) B32868317
theorem B13655081 : Blo 1064615 13655081 := bstep (se 2 (by rfl) ⟨5120655, by rfl⟩ : syracuseStep 13655081 = 10241311) B10241311
theorem B4055291 : Blo 1064615 4055291 := bstep (se 1 (by rfl) ⟨3041468, by rfl⟩ : syracuseStep 4055291 = 6082937) B6082937
theorem B8087039 : Blo 1064615 8087039 := bstep (se 1 (by rfl) ⟨6065279, by rfl⟩ : syracuseStep 8087039 = 12130559) B12130559
theorem B5400431 : Blo 1064615 5400431 := bstep (se 1 (by rfl) ⟨4050323, by rfl⟩ : syracuseStep 5400431 = 8100647) B8100647
theorem B2026127 : Blo 1064615 2026127 := bstep (se 1 (by rfl) ⟨1519595, by rfl⟩ : syracuseStep 2026127 = 3039191) B3039191
theorem B3599261 : Blo 1064615 3599261 := bstep (se 3 (by rfl) ⟨674861, by rfl⟩ : syracuseStep 3599261 = 1349723) B1349723
theorem B1797113 : Blo 1064615 1797113 := bstep (se 2 (by rfl) ⟨673917, by rfl⟩ : syracuseStep 1797113 = 1347835) B1347835
theorem B9728255 : Blo 1064615 9728255 := bstep (se 1 (by rfl) ⟨7296191, by rfl⟩ : syracuseStep 9728255 = 14592383) B14592383
theorem B9860059 : Blo 1064615 9860059 := bstep (se 1 (by rfl) ⟨7395044, by rfl⟩ : syracuseStep 9860059 = 14790089) B14790089
theorem B3601961 : Blo 1064615 3601961 := bstep (se 2 (by rfl) ⟨1350735, by rfl⟩ : syracuseStep 3601961 = 2701471) B2701471
theorem B37386143 : Blo 1064615 37386143 := bstep (se 1 (by rfl) ⟨28039607, by rfl⟩ : syracuseStep 37386143 = 56079215) B56079215
theorem B1538527 : Blo 1064615 1538527 := bstep (se 1 (by rfl) ⟨1153895, by rfl⟩ : syracuseStep 1538527 = 2307791) B2307791
theorem B13336771 : Blo 1064615 13336771 := bstep (se 1 (by rfl) ⟨10002578, by rfl⟩ : syracuseStep 13336771 = 20005157) B20005157
theorem B4559485 : Blo 1064615 4559485 := bstep (se 3 (by rfl) ⟨854903, by rfl⟩ : syracuseStep 4559485 = 1709807) B1709807
theorem B13146745 : Blo 1064615 13146745 := bstep (se 2 (by rfl) ⟨4930029, by rfl⟩ : syracuseStep 13146745 = 9860059) B9860059
theorem B1350751 : Blo 1064615 1350751 := bstep (se 1 (by rfl) ⟨1013063, by rfl⟩ : syracuseStep 1350751 = 2026127) B2026127
theorem B2399507 : Blo 1064615 2399507 := bstep (se 1 (by rfl) ⟨1799630, by rfl⟩ : syracuseStep 2399507 = 3599261) B3599261
theorem B2401307 : Blo 1064615 2401307 := bstep (se 1 (by rfl) ⟨1800980, by rfl⟩ : syracuseStep 2401307 = 3601961) B3601961
theorem B2698879 : Blo 1064615 2698879 := bstep (se 1 (by rfl) ⟨2024159, by rfl⟩ : syracuseStep 2698879 = 4048319) B4048319
theorem B13153063 : Blo 1064615 13153063 := bstep (se 1 (by rfl) ⟨9864797, by rfl⟩ : syracuseStep 13153063 = 19729595) B19729595
theorem B116865125 : Blo 1064615 116865125 := bstep (se 4 (by rfl) ⟨10956105, by rfl⟩ : syracuseStep 116865125 = 21912211) B21912211
theorem B8665373 : Blo 1064615 8665373 := bstep (se 3 (by rfl) ⟨1624757, by rfl⟩ : syracuseStep 8665373 = 3249515) B3249515
theorem B2703527 : Blo 1064615 2703527 := bstep (se 1 (by rfl) ⟨2027645, by rfl⟩ : syracuseStep 2703527 = 4055291) B4055291
theorem B5391359 : Blo 1064615 5391359 := bstep (se 1 (by rfl) ⟨4043519, by rfl⟩ : syracuseStep 5391359 = 8087039) B8087039
theorem B1198075 : Blo 1064615 1198075 := bstep (se 1 (by rfl) ⟨898556, by rfl⟩ : syracuseStep 1198075 = 1797113) B1797113
theorem B11520091 : Blo 1064615 11520091 := bstep (se 1 (by rfl) ⟨8640068, by rfl⟩ : syracuseStep 11520091 = 17280137) B17280137
theorem B2051369 : Blo 1064615 2051369 := bstep (se 2 (by rfl) ⟨769263, by rfl⟩ : syracuseStep 2051369 = 1538527) B1538527
theorem B24924095 : Blo 1064615 24924095 := bstep (se 1 (by rfl) ⟨18693071, by rfl⟩ : syracuseStep 24924095 = 37386143) B37386143
theorem B4051903 : Blo 1064615 4051903 := bstep (se 1 (by rfl) ⟨3038927, by rfl⟩ : syracuseStep 4051903 = 6077855) B6077855
theorem B6084143 : Blo 1064615 6084143 := bstep (se 1 (by rfl) ⟨4563107, by rfl⟩ : syracuseStep 6084143 = 9126215) B9126215
theorem B3594347 : Blo 1064615 3594347 := bstep (se 1 (by rfl) ⟨2695760, by rfl⟩ : syracuseStep 3594347 = 5391521) B5391521
theorem B4054319 : Blo 1064615 4054319 := bstep (se 1 (by rfl) ⟨3040739, by rfl⟩ : syracuseStep 4054319 = 6081479) B6081479
theorem B8085095 : Blo 1064615 8085095 := bstep (se 1 (by rfl) ⟨6063821, by rfl⟩ : syracuseStep 8085095 = 12127643) B12127643
theorem B1597607 : Blo 1064615 1597607 := bstep (se 1 (by rfl) ⟨1198205, by rfl⟩ : syracuseStep 1597607 = 2396411) B2396411
theorem B9103387 : Blo 1064615 9103387 := bstep (se 1 (by rfl) ⟨6827540, by rfl⟩ : syracuseStep 9103387 = 13655081) B13655081
theorem B1599707 : Blo 1064615 1599707 := bstep (se 1 (by rfl) ⟨1199780, by rfl⟩ : syracuseStep 1599707 = 2399561) B2399561
theorem B1600511 : Blo 1064615 1600511 := bstep (se 1 (by rfl) ⟨1200383, by rfl⟩ : syracuseStep 1600511 = 2400767) B2400767
theorem B1600667 : Blo 1064615 1600667 := bstep (se 1 (by rfl) ⟨1200500, by rfl⟩ : syracuseStep 1600667 = 2401001) B2401001
theorem B3239443 : Blo 1064615 3239443 := bstep (se 1 (by rfl) ⟨2429582, by rfl⟩ : syracuseStep 3239443 = 4859165) B4859165
theorem B3600287 : Blo 1064615 3600287 := bstep (se 1 (by rfl) ⟨2700215, by rfl⟩ : syracuseStep 3600287 = 5400431) B5400431
theorem B1798591 : Blo 1064615 1798591 := bstep (se 1 (by rfl) ⟨1348943, by rfl⟩ : syracuseStep 1798591 = 2697887) B2697887
theorem B6485503 : Blo 1064615 6485503 := bstep (se 1 (by rfl) ⟨4864127, by rfl⟩ : syracuseStep 6485503 = 9728255) B9728255
theorem B19495039 : Blo 1064615 19495039 := bstep (se 1 (by rfl) ⟨14621279, by rfl⟩ : syracuseStep 19495039 = 29242559) B29242559
theorem B6585211 : Blo 1064615 6585211 := bstep (se 1 (by rfl) ⟨4938908, by rfl⟩ : syracuseStep 6585211 = 9877817) B9877817
theorem B1802351 : Blo 1064615 1802351 := bstep (se 1 (by rfl) ⟨1351763, by rfl⟩ : syracuseStep 1802351 = 2703527) B2703527
theorem B16616063 : Blo 1064615 16616063 := bstep (se 1 (by rfl) ⟨12462047, by rfl⟩ : syracuseStep 16616063 = 24924095) B24924095
theorem B2396231 : Blo 1064615 2396231 := bstep (se 1 (by rfl) ⟨1797173, by rfl⟩ : syracuseStep 2396231 = 3594347) B3594347
theorem B2398121 : Blo 1064615 2398121 := bstep (se 2 (by rfl) ⟨899295, by rfl⟩ : syracuseStep 2398121 = 1798591) B1798591
theorem B17537417 : Blo 1064615 17537417 := bstep (se 2 (by rfl) ⟨6576531, by rfl⟩ : syracuseStep 17537417 = 13153063) B13153063
theorem B2400191 : Blo 1064615 2400191 := bstep (se 1 (by rfl) ⟨1800143, by rfl⟩ : syracuseStep 2400191 = 3600287) B3600287
theorem B25993385 : Blo 1064615 25993385 := bstep (se 2 (by rfl) ⟨9747519, by rfl⟩ : syracuseStep 25993385 = 19495039) B19495039
theorem B5776915 : Blo 1064615 5776915 := bstep (se 1 (by rfl) ⟨4332686, by rfl⟩ : syracuseStep 5776915 = 8665373) B8665373
theorem B12137849 : Blo 1064615 12137849 := bstep (se 2 (by rfl) ⟨4551693, by rfl⟩ : syracuseStep 12137849 = 9103387) B9103387
theorem B2702879 : Blo 1064615 2702879 := bstep (se 1 (by rfl) ⟨2027159, by rfl⟩ : syracuseStep 2702879 = 4054319) B4054319
theorem B5390063 : Blo 1064615 5390063 := bstep (se 1 (by rfl) ⟨4042547, by rfl⟩ : syracuseStep 5390063 = 8085095) B8085095
theorem B1065071 : Blo 1064615 1065071 := bstep (se 1 (by rfl) ⟨798803, by rfl⟩ : syracuseStep 1065071 = 1597607) B1597607
theorem B6079313 : Blo 1064615 6079313 := bstep (se 2 (by rfl) ⟨2279742, by rfl⟩ : syracuseStep 6079313 = 4559485) B4559485
theorem B1066471 : Blo 1064615 1066471 := bstep (se 1 (by rfl) ⟨799853, by rfl⟩ : syracuseStep 1066471 = 1599707) B1599707
theorem B1067007 : Blo 1064615 1067007 := bstep (se 1 (by rfl) ⟨800255, by rfl⟩ : syracuseStep 1067007 = 1600511) B1600511
theorem B1067111 : Blo 1064615 1067111 := bstep (se 1 (by rfl) ⟨800333, by rfl⟩ : syracuseStep 1067111 = 1600667) B1600667
theorem B77910083 : Blo 1064615 77910083 := bstep (se 1 (by rfl) ⟨58432562, by rfl⟩ : syracuseStep 77910083 = 116865125) B116865125
theorem B17782361 : Blo 1064615 17782361 := bstep (se 2 (by rfl) ⟨6668385, by rfl⟩ : syracuseStep 17782361 = 13336771) B13336771
theorem B3594239 : Blo 1064615 3594239 := bstep (se 1 (by rfl) ⟨2695679, by rfl⟩ : syracuseStep 3594239 = 5391359) B5391359
theorem B1597433 : Blo 1064615 1597433 := bstep (se 2 (by rfl) ⟨599037, by rfl⟩ : syracuseStep 1597433 = 1198075) B1198075
theorem B15360121 : Blo 1064615 15360121 := bstep (se 2 (by rfl) ⟨5760045, by rfl⟩ : syracuseStep 15360121 = 11520091) B11520091
theorem B21881269 : Blo 1064615 21881269 := bstep (se 5 (by rfl) ⟨1025684, by rfl⟩ : syracuseStep 21881269 = 2051369) B2051369
theorem B4056095 : Blo 1064615 4056095 := bstep (se 1 (by rfl) ⟨3042071, by rfl⟩ : syracuseStep 4056095 = 6084143) B6084143
theorem B4319257 : Blo 1064615 4319257 := bstep (se 2 (by rfl) ⟨1619721, by rfl⟩ : syracuseStep 4319257 = 3239443) B3239443
theorem B3598505 : Blo 1064615 3598505 := bstep (se 2 (by rfl) ⟨1349439, by rfl⟩ : syracuseStep 3598505 = 2698879) B2698879
theorem B1599671 : Blo 1064615 1599671 := bstep (se 1 (by rfl) ⟨1199753, by rfl⟩ : syracuseStep 1599671 = 2399507) B2399507
theorem B1600871 : Blo 1064615 1600871 := bstep (se 1 (by rfl) ⟨1200653, by rfl⟩ : syracuseStep 1600871 = 2401307) B2401307
theorem B5402537 : Blo 1064615 5402537 := bstep (se 2 (by rfl) ⟨2025951, by rfl⟩ : syracuseStep 5402537 = 4051903) B4051903
theorem B8647337 : Blo 1064615 8647337 := bstep (se 2 (by rfl) ⟨3242751, by rfl⟩ : syracuseStep 8647337 = 6485503) B6485503
theorem B17528993 : Blo 1064615 17528993 := bstep (se 2 (by rfl) ⟨6573372, by rfl⟩ : syracuseStep 17528993 = 13146745) B13146745
theorem B8780281 : Blo 1064615 8780281 := bstep (se 2 (by rfl) ⟨3292605, by rfl⟩ : syracuseStep 8780281 = 6585211) B6585211
theorem B1801001 : Blo 1064615 1801001 := bstep (se 2 (by rfl) ⟨675375, by rfl⟩ : syracuseStep 1801001 = 1350751) B1350751
theorem B20480161 : Blo 1064615 20480161 := bstep (se 2 (by rfl) ⟨7680060, by rfl⟩ : syracuseStep 20480161 = 15360121) B15360121
theorem B7702553 : Blo 1064615 7702553 := bstep (se 2 (by rfl) ⟨2888457, by rfl⟩ : syracuseStep 7702553 = 5776915) B5776915
theorem B46828165 : Blo 1064615 46828165 := bstep (se 4 (by rfl) ⟨4390140, by rfl⟩ : syracuseStep 46828165 = 8780281) B8780281
theorem B51940055 : Blo 1064615 51940055 := bstep (se 1 (by rfl) ⟨38955041, by rfl⟩ : syracuseStep 51940055 = 77910083) B77910083
theorem B2396159 : Blo 1064615 2396159 := bstep (se 1 (by rfl) ⟨1797119, by rfl⟩ : syracuseStep 2396159 = 3594239) B3594239
theorem B2399003 : Blo 1064615 2399003 := bstep (se 1 (by rfl) ⟨1799252, by rfl⟩ : syracuseStep 2399003 = 3598505) B3598505
theorem B44309501 : Blo 1064615 44309501 := bstep (se 3 (by rfl) ⟨8308031, by rfl⟩ : syracuseStep 44309501 = 16616063) B16616063
theorem B29175025 : Blo 1064615 29175025 := bstep (se 2 (by rfl) ⟨10940634, by rfl⟩ : syracuseStep 29175025 = 21881269) B21881269
theorem B1064955 : Blo 1064615 1064955 := bstep (se 1 (by rfl) ⟨798716, by rfl⟩ : syracuseStep 1064955 = 1597433) B1597433
theorem B2704063 : Blo 1064615 2704063 := bstep (se 1 (by rfl) ⟨2028047, by rfl⟩ : syracuseStep 2704063 = 4056095) B4056095
theorem B1066447 : Blo 1064615 1066447 := bstep (se 1 (by rfl) ⟨799835, by rfl⟩ : syracuseStep 1066447 = 1599671) B1599671
theorem B1067247 : Blo 1064615 1067247 := bstep (se 1 (by rfl) ⟨800435, by rfl⟩ : syracuseStep 1067247 = 1600871) B1600871
theorem B11685995 : Blo 1064615 11685995 := bstep (se 1 (by rfl) ⟨8764496, by rfl⟩ : syracuseStep 11685995 = 17528993) B17528993
theorem B1200667 : Blo 1064615 1200667 := bstep (se 1 (by rfl) ⟨900500, by rfl⟩ : syracuseStep 1200667 = 1801001) B1801001
theorem B3593375 : Blo 1064615 3593375 := bstep (se 1 (by rfl) ⟨2695031, by rfl⟩ : syracuseStep 3593375 = 5390063) B5390063
theorem B1201567 : Blo 1064615 1201567 := bstep (se 1 (by rfl) ⟨901175, by rfl⟩ : syracuseStep 1201567 = 1802351) B1802351
theorem B4052875 : Blo 1064615 4052875 := bstep (se 1 (by rfl) ⟨3039656, by rfl⟩ : syracuseStep 4052875 = 6079313) B6079313
theorem B5759009 : Blo 1064615 5759009 := bstep (se 2 (by rfl) ⟨2159628, by rfl⟩ : syracuseStep 5759009 = 4319257) B4319257
theorem B1597487 : Blo 1064615 1597487 := bstep (se 1 (by rfl) ⟨1198115, by rfl⟩ : syracuseStep 1597487 = 2396231) B2396231
theorem B11854907 : Blo 1064615 11854907 := bstep (se 1 (by rfl) ⟨8891180, by rfl⟩ : syracuseStep 11854907 = 17782361) B17782361
theorem B1598747 : Blo 1064615 1598747 := bstep (se 1 (by rfl) ⟨1199060, by rfl⟩ : syracuseStep 1598747 = 2398121) B2398121
theorem B11691611 : Blo 1064615 11691611 := bstep (se 1 (by rfl) ⟨8768708, by rfl⟩ : syracuseStep 11691611 = 17537417) B17537417
theorem B1600127 : Blo 1064615 1600127 := bstep (se 1 (by rfl) ⟨1200095, by rfl⟩ : syracuseStep 1600127 = 2400191) B2400191
theorem B17328923 : Blo 1064615 17328923 := bstep (se 1 (by rfl) ⟨12996692, by rfl⟩ : syracuseStep 17328923 = 25993385) B25993385
theorem B3601691 : Blo 1064615 3601691 := bstep (se 1 (by rfl) ⟨2701268, by rfl⟩ : syracuseStep 3601691 = 5402537) B5402537
theorem B5764891 : Blo 1064615 5764891 := bstep (se 1 (by rfl) ⟨4323668, by rfl⟩ : syracuseStep 5764891 = 8647337) B8647337
theorem B8091899 : Blo 1064615 8091899 := bstep (se 1 (by rfl) ⟨6068924, by rfl⟩ : syracuseStep 8091899 = 12137849) B12137849
theorem B1801919 : Blo 1064615 1801919 := bstep (se 1 (by rfl) ⟨1351439, by rfl⟩ : syracuseStep 1801919 = 2702879) B2702879
theorem B3605417 : Blo 1064615 3605417 := bstep (se 2 (by rfl) ⟨1352031, by rfl⟩ : syracuseStep 3605417 = 2704063) B2704063
theorem B2395583 : Blo 1064615 2395583 := bstep (se 1 (by rfl) ⟨1796687, by rfl⟩ : syracuseStep 2395583 = 3593375) B3593375
theorem B38900033 : Blo 1064615 38900033 := bstep (se 2 (by rfl) ⟨14587512, by rfl⟩ : syracuseStep 38900033 = 29175025) B29175025
theorem B3839339 : Blo 1064615 3839339 := bstep (se 1 (by rfl) ⟨2879504, by rfl⟩ : syracuseStep 3839339 = 5759009) B5759009
theorem B7903271 : Blo 1064615 7903271 := bstep (se 1 (by rfl) ⟨5927453, by rfl⟩ : syracuseStep 7903271 = 11854907) B11854907
theorem B2401127 : Blo 1064615 2401127 := bstep (se 1 (by rfl) ⟨1800845, by rfl⟩ : syracuseStep 2401127 = 3601691) B3601691
theorem B27306881 : Blo 1064615 27306881 := bstep (se 2 (by rfl) ⟨10240080, by rfl⟩ : syracuseStep 27306881 = 20480161) B20480161
theorem B62437553 : Blo 1064615 62437553 := bstep (se 2 (by rfl) ⟨23414082, by rfl⟩ : syracuseStep 62437553 = 46828165) B46828165
theorem B29539667 : Blo 1064615 29539667 := bstep (se 1 (by rfl) ⟨22154750, by rfl⟩ : syracuseStep 29539667 = 44309501) B44309501
theorem B1064991 : Blo 1064615 1064991 := bstep (se 1 (by rfl) ⟨798743, by rfl⟩ : syracuseStep 1064991 = 1597487) B1597487
theorem B1065831 : Blo 1064615 1065831 := bstep (se 1 (by rfl) ⟨799373, by rfl⟩ : syracuseStep 1065831 = 1598747) B1598747
theorem B1066751 : Blo 1064615 1066751 := bstep (se 1 (by rfl) ⟨800063, by rfl⟩ : syracuseStep 1066751 = 1600127) B1600127
theorem B11552615 : Blo 1064615 11552615 := bstep (se 1 (by rfl) ⟨8664461, by rfl⟩ : syracuseStep 11552615 = 17328923) B17328923
theorem B7686521 : Blo 1064615 7686521 := bstep (se 2 (by rfl) ⟨2882445, by rfl⟩ : syracuseStep 7686521 = 5764891) B5764891
theorem B5394599 : Blo 1064615 5394599 := bstep (se 1 (by rfl) ⟨4045949, by rfl⟩ : syracuseStep 5394599 = 8091899) B8091899
theorem B1201279 : Blo 1064615 1201279 := bstep (se 1 (by rfl) ⟨900959, by rfl⟩ : syracuseStep 1201279 = 1801919) B1801919
theorem B5135035 : Blo 1064615 5135035 := bstep (se 1 (by rfl) ⟨3851276, by rfl⟩ : syracuseStep 5135035 = 7702553) B7702553
theorem B34626703 : Blo 1064615 34626703 := bstep (se 1 (by rfl) ⟨25970027, by rfl⟩ : syracuseStep 34626703 = 51940055) B51940055
theorem B1597439 : Blo 1064615 1597439 := bstep (se 1 (by rfl) ⟨1198079, by rfl⟩ : syracuseStep 1597439 = 2396159) B2396159
theorem B7790663 : Blo 1064615 7790663 := bstep (se 1 (by rfl) ⟨5842997, by rfl⟩ : syracuseStep 7790663 = 11685995) B11685995
theorem B1599335 : Blo 1064615 1599335 := bstep (se 1 (by rfl) ⟨1199501, by rfl⟩ : syracuseStep 1599335 = 2399003) B2399003
theorem B1600889 : Blo 1064615 1600889 := bstep (se 2 (by rfl) ⟨600333, by rfl⟩ : syracuseStep 1600889 = 1200667) B1200667
theorem B7794407 : Blo 1064615 7794407 := bstep (se 1 (by rfl) ⟨5845805, by rfl⟩ : syracuseStep 7794407 = 11691611) B11691611
theorem B1602089 : Blo 1064615 1602089 := bstep (se 2 (by rfl) ⟨600783, by rfl⟩ : syracuseStep 1602089 = 1201567) B1201567
theorem B5403833 : Blo 1064615 5403833 := bstep (se 2 (by rfl) ⟨2026437, by rfl⟩ : syracuseStep 5403833 = 4052875) B4052875
theorem B7701743 : Blo 1064615 7701743 := bstep (se 1 (by rfl) ⟨5776307, by rfl⟩ : syracuseStep 7701743 = 11552615) B11552615
theorem B41625035 : Blo 1064615 41625035 := bstep (se 1 (by rfl) ⟨31218776, by rfl⟩ : syracuseStep 41625035 = 62437553) B62437553
theorem B2403611 : Blo 1064615 2403611 := bstep (se 1 (by rfl) ⟨1802708, by rfl⟩ : syracuseStep 2403611 = 3605417) B3605417
theorem B5124347 : Blo 1064615 5124347 := bstep (se 1 (by rfl) ⟨3843260, by rfl⟩ : syracuseStep 5124347 = 7686521) B7686521
theorem B25933355 : Blo 1064615 25933355 := bstep (se 1 (by rfl) ⟨19450016, by rfl⟩ : syracuseStep 25933355 = 38900033) B38900033
theorem B10238237 : Blo 1064615 10238237 := bstep (se 3 (by rfl) ⟨1919669, by rfl⟩ : syracuseStep 10238237 = 3839339) B3839339
theorem B1064959 : Blo 1064615 1064959 := bstep (se 1 (by rfl) ⟨798719, by rfl⟩ : syracuseStep 1064959 = 1597439) B1597439
theorem B5193775 : Blo 1064615 5193775 := bstep (se 1 (by rfl) ⟨3895331, by rfl⟩ : syracuseStep 5193775 = 7790663) B7790663
theorem B1066223 : Blo 1064615 1066223 := bstep (se 1 (by rfl) ⟨799667, by rfl⟩ : syracuseStep 1066223 = 1599335) B1599335
theorem B18204587 : Blo 1064615 18204587 := bstep (se 1 (by rfl) ⟨13653440, by rfl⟩ : syracuseStep 18204587 = 27306881) B27306881
theorem B1067259 : Blo 1064615 1067259 := bstep (se 1 (by rfl) ⟨800444, by rfl⟩ : syracuseStep 1067259 = 1600889) B1600889
theorem B5196271 : Blo 1064615 5196271 := bstep (se 1 (by rfl) ⟨3897203, by rfl⟩ : syracuseStep 5196271 = 7794407) B7794407
theorem B1068059 : Blo 1064615 1068059 := bstep (se 1 (by rfl) ⟨801044, by rfl⟩ : syracuseStep 1068059 = 1602089) B1602089
theorem B1597055 : Blo 1064615 1597055 := bstep (se 1 (by rfl) ⟨1197791, by rfl⟩ : syracuseStep 1597055 = 2395583) B2395583
theorem B3596399 : Blo 1064615 3596399 := bstep (se 1 (by rfl) ⟨2697299, by rfl⟩ : syracuseStep 3596399 = 5394599) B5394599
theorem B5268847 : Blo 1064615 5268847 := bstep (se 1 (by rfl) ⟨3951635, by rfl⟩ : syracuseStep 5268847 = 7903271) B7903271
theorem B1600751 : Blo 1064615 1600751 := bstep (se 1 (by rfl) ⟨1200563, by rfl⟩ : syracuseStep 1600751 = 2401127) B2401127
theorem B1601705 : Blo 1064615 1601705 := bstep (se 2 (by rfl) ⟨600639, by rfl⟩ : syracuseStep 1601705 = 1201279) B1201279
theorem B3602555 : Blo 1064615 3602555 := bstep (se 1 (by rfl) ⟨2701916, by rfl⟩ : syracuseStep 3602555 = 5403833) B5403833
theorem B78772445 : Blo 1064615 78772445 := bstep (se 3 (by rfl) ⟨14769833, by rfl⟩ : syracuseStep 78772445 = 29539667) B29539667
theorem B6846713 : Blo 1064615 6846713 := bstep (se 2 (by rfl) ⟨2567517, by rfl⟩ : syracuseStep 6846713 = 5135035) B5135035
theorem B46168937 : Blo 1064615 46168937 := bstep (se 2 (by rfl) ⟨17313351, by rfl⟩ : syracuseStep 46168937 = 34626703) B34626703
theorem B2397599 : Blo 1064615 2397599 := bstep (se 1 (by rfl) ⟨1798199, by rfl⟩ : syracuseStep 2397599 = 3596399) B3596399
theorem B3416231 : Blo 1064615 3416231 := bstep (se 1 (by rfl) ⟨2562173, by rfl⟩ : syracuseStep 3416231 = 5124347) B5124347
theorem B2401703 : Blo 1064615 2401703 := bstep (se 1 (by rfl) ⟨1801277, by rfl⟩ : syracuseStep 2401703 = 3602555) B3602555
theorem B4564475 : Blo 1064615 4564475 := bstep (se 1 (by rfl) ⟨3423356, by rfl⟩ : syracuseStep 4564475 = 6846713) B6846713
theorem B6825491 : Blo 1064615 6825491 := bstep (se 1 (by rfl) ⟨5119118, by rfl⟩ : syracuseStep 6825491 = 10238237) B10238237
theorem B30779291 : Blo 1064615 30779291 := bstep (se 1 (by rfl) ⟨23084468, by rfl⟩ : syracuseStep 30779291 = 46168937) B46168937
theorem B6925033 : Blo 1064615 6925033 := bstep (se 2 (by rfl) ⟨2596887, by rfl⟩ : syracuseStep 6925033 = 5193775) B5193775
theorem B12136391 : Blo 1064615 12136391 := bstep (se 1 (by rfl) ⟨9102293, by rfl⟩ : syracuseStep 12136391 = 18204587) B18204587
theorem B7025129 : Blo 1064615 7025129 := bstep (se 2 (by rfl) ⟨2634423, by rfl⟩ : syracuseStep 7025129 = 5268847) B5268847
theorem B6928361 : Blo 1064615 6928361 := bstep (se 2 (by rfl) ⟨2598135, by rfl⟩ : syracuseStep 6928361 = 5196271) B5196271
theorem B1064703 : Blo 1064615 1064703 := bstep (se 1 (by rfl) ⟨798527, by rfl⟩ : syracuseStep 1064703 = 1597055) B1597055
theorem B1067167 : Blo 1064615 1067167 := bstep (se 1 (by rfl) ⟨800375, by rfl⟩ : syracuseStep 1067167 = 1600751) B1600751
theorem B1067803 : Blo 1064615 1067803 := bstep (se 1 (by rfl) ⟨800852, by rfl⟩ : syracuseStep 1067803 = 1601705) B1601705
theorem B17288903 : Blo 1064615 17288903 := bstep (se 1 (by rfl) ⟨12966677, by rfl⟩ : syracuseStep 17288903 = 25933355) B25933355
theorem B52514963 : Blo 1064615 52514963 := bstep (se 1 (by rfl) ⟨39386222, by rfl⟩ : syracuseStep 52514963 = 78772445) B78772445
theorem B20537981 : Blo 1064615 20537981 := bstep (se 3 (by rfl) ⟨3850871, by rfl⟩ : syracuseStep 20537981 = 7701743) B7701743
theorem B27750023 : Blo 1064615 27750023 := bstep (se 1 (by rfl) ⟨20812517, by rfl⟩ : syracuseStep 27750023 = 41625035) B41625035
theorem B1602407 : Blo 1064615 1602407 := bstep (se 1 (by rfl) ⟨1201805, by rfl⟩ : syracuseStep 1602407 = 2403611) B2403611
theorem B36933509 : Blo 1064615 36933509 := bstep (se 4 (by rfl) ⟨3462516, by rfl⟩ : syracuseStep 36933509 = 6925033) B6925033
theorem B20519527 : Blo 1064615 20519527 := bstep (se 1 (by rfl) ⟨15389645, by rfl⟩ : syracuseStep 20519527 = 30779291) B30779291
theorem B35009975 : Blo 1064615 35009975 := bstep (se 1 (by rfl) ⟨26257481, by rfl⟩ : syracuseStep 35009975 = 52514963) B52514963
theorem B2277487 : Blo 1064615 2277487 := bstep (se 1 (by rfl) ⟨1708115, by rfl⟩ : syracuseStep 2277487 = 3416231) B3416231
theorem B18500015 : Blo 1064615 18500015 := bstep (se 1 (by rfl) ⟨13875011, by rfl⟩ : syracuseStep 18500015 = 27750023) B27750023
theorem B1068271 : Blo 1064615 1068271 := bstep (se 1 (by rfl) ⟨801203, by rfl⟩ : syracuseStep 1068271 = 1602407) B1602407
theorem B11525935 : Blo 1064615 11525935 := bstep (se 1 (by rfl) ⟨8644451, by rfl⟩ : syracuseStep 11525935 = 17288903) B17288903
theorem B1598399 : Blo 1064615 1598399 := bstep (se 1 (by rfl) ⟨1198799, by rfl⟩ : syracuseStep 1598399 = 2397599) B2397599
theorem B13691987 : Blo 1064615 13691987 := bstep (se 1 (by rfl) ⟨10268990, by rfl⟩ : syracuseStep 13691987 = 20537981) B20537981
theorem B1601135 : Blo 1064615 1601135 := bstep (se 1 (by rfl) ⟨1200851, by rfl⟩ : syracuseStep 1601135 = 2401703) B2401703
theorem B3042983 : Blo 1064615 3042983 := bstep (se 1 (by rfl) ⟨2282237, by rfl⟩ : syracuseStep 3042983 = 4564475) B4564475
theorem B4550327 : Blo 1064615 4550327 := bstep (se 1 (by rfl) ⟨3412745, by rfl⟩ : syracuseStep 4550327 = 6825491) B6825491
theorem B8090927 : Blo 1064615 8090927 := bstep (se 1 (by rfl) ⟨6068195, by rfl⟩ : syracuseStep 8090927 = 12136391) B12136391
theorem B4683419 : Blo 1064615 4683419 := bstep (se 1 (by rfl) ⟨3512564, by rfl⟩ : syracuseStep 4683419 = 7025129) B7025129
theorem B4618907 : Blo 1064615 4618907 := bstep (se 1 (by rfl) ⟨3464180, by rfl⟩ : syracuseStep 4618907 = 6928361) B6928361
theorem B23339983 : Blo 1064615 23339983 := bstep (se 1 (by rfl) ⟨17504987, by rfl⟩ : syracuseStep 23339983 = 35009975) B35009975
theorem B3122279 : Blo 1064615 3122279 := bstep (se 1 (by rfl) ⟨2341709, by rfl⟩ : syracuseStep 3122279 = 4683419) B4683419
theorem B12333343 : Blo 1064615 12333343 := bstep (se 1 (by rfl) ⟨9250007, by rfl⟩ : syracuseStep 12333343 = 18500015) B18500015
theorem B1065599 : Blo 1064615 1065599 := bstep (se 1 (by rfl) ⟨799199, by rfl⟩ : syracuseStep 1065599 = 1598399) B1598399
theorem B9127991 : Blo 1064615 9127991 := bstep (se 1 (by rfl) ⟨6845993, by rfl⟩ : syracuseStep 9127991 = 13691987) B13691987
theorem B1067423 : Blo 1064615 1067423 := bstep (se 1 (by rfl) ⟨800567, by rfl⟩ : syracuseStep 1067423 = 1601135) B1601135
theorem B3033551 : Blo 1064615 3033551 := bstep (se 1 (by rfl) ⟨2275163, by rfl⟩ : syracuseStep 3033551 = 4550327) B4550327
theorem B5393951 : Blo 1064615 5393951 := bstep (se 1 (by rfl) ⟨4045463, by rfl⟩ : syracuseStep 5393951 = 8090927) B8090927
theorem B98489357 : Blo 1064615 98489357 := bstep (se 3 (by rfl) ⟨18466754, by rfl⟩ : syracuseStep 98489357 = 36933509) B36933509
theorem B12146597 : Blo 1064615 12146597 := bstep (se 4 (by rfl) ⟨1138743, by rfl⟩ : syracuseStep 12146597 = 2277487) B2277487
theorem B2028655 : Blo 1064615 2028655 := bstep (se 1 (by rfl) ⟨1521491, by rfl⟩ : syracuseStep 2028655 = 3042983) B3042983
theorem B27359369 : Blo 1064615 27359369 := bstep (se 2 (by rfl) ⟨10259763, by rfl⟩ : syracuseStep 27359369 = 20519527) B20519527
theorem B3079271 : Blo 1064615 3079271 := bstep (se 1 (by rfl) ⟨2309453, by rfl⟩ : syracuseStep 3079271 = 4618907) B4618907
theorem B15367913 : Blo 1064615 15367913 := bstep (se 2 (by rfl) ⟨5762967, by rfl⟩ : syracuseStep 15367913 = 11525935) B11525935
theorem B8097731 : Blo 1064615 8097731 := bstep (se 1 (by rfl) ⟨6073298, by rfl⟩ : syracuseStep 8097731 = 12146597) B12146597
theorem B2081519 : Blo 1064615 2081519 := bstep (se 1 (by rfl) ⟨1561139, by rfl⟩ : syracuseStep 2081519 = 3122279) B3122279
theorem B2704873 : Blo 1064615 2704873 := bstep (se 2 (by rfl) ⟨1014327, by rfl⟩ : syracuseStep 2704873 = 2028655) B2028655
theorem B18239579 : Blo 1064615 18239579 := bstep (se 1 (by rfl) ⟨13679684, by rfl⟩ : syracuseStep 18239579 = 27359369) B27359369
theorem B2052847 : Blo 1064615 2052847 := bstep (se 1 (by rfl) ⟨1539635, by rfl⟩ : syracuseStep 2052847 = 3079271) B3079271
theorem B10245275 : Blo 1064615 10245275 := bstep (se 1 (by rfl) ⟨7683956, by rfl⟩ : syracuseStep 10245275 = 15367913) B15367913
theorem B31119977 : Blo 1064615 31119977 := bstep (se 2 (by rfl) ⟨11669991, by rfl⟩ : syracuseStep 31119977 = 23339983) B23339983
theorem B6085327 : Blo 1064615 6085327 := bstep (se 1 (by rfl) ⟨4563995, by rfl⟩ : syracuseStep 6085327 = 9127991) B9127991
theorem B3595967 : Blo 1064615 3595967 := bstep (se 1 (by rfl) ⟨2696975, by rfl⟩ : syracuseStep 3595967 = 5393951) B5393951
theorem B65659571 : Blo 1064615 65659571 := bstep (se 1 (by rfl) ⟨49244678, by rfl⟩ : syracuseStep 65659571 = 98489357) B98489357
theorem B16444457 : Blo 1064615 16444457 := bstep (se 2 (by rfl) ⟨6166671, by rfl⟩ : syracuseStep 16444457 = 12333343) B12333343
theorem B8089469 : Blo 1064615 8089469 := bstep (se 3 (by rfl) ⟨1516775, by rfl⟩ : syracuseStep 8089469 = 3033551) B3033551
theorem B3606497 : Blo 1064615 3606497 := bstep (se 2 (by rfl) ⟨1352436, by rfl⟩ : syracuseStep 3606497 = 2704873) B2704873
theorem B12159719 : Blo 1064615 12159719 := bstep (se 1 (by rfl) ⟨9119789, by rfl⟩ : syracuseStep 12159719 = 18239579) B18239579
theorem B2397311 : Blo 1064615 2397311 := bstep (se 1 (by rfl) ⟨1797983, by rfl⟩ : syracuseStep 2397311 = 3595967) B3595967
theorem B6830183 : Blo 1064615 6830183 := bstep (se 1 (by rfl) ⟨5122637, by rfl⟩ : syracuseStep 6830183 = 10245275) B10245275
theorem B2737129 : Blo 1064615 2737129 := bstep (se 2 (by rfl) ⟨1026423, by rfl⟩ : syracuseStep 2737129 = 2052847) B2052847
theorem B82986605 : Blo 1064615 82986605 := bstep (se 3 (by rfl) ⟨15559988, by rfl⟩ : syracuseStep 82986605 = 31119977) B31119977
theorem B10962971 : Blo 1064615 10962971 := bstep (se 1 (by rfl) ⟨8222228, by rfl⟩ : syracuseStep 10962971 = 16444457) B16444457
theorem B22202869 : Blo 1064615 22202869 := bstep (se 5 (by rfl) ⟨1040759, by rfl⟩ : syracuseStep 22202869 = 2081519) B2081519
theorem B5392979 : Blo 1064615 5392979 := bstep (se 1 (by rfl) ⟨4044734, by rfl⟩ : syracuseStep 5392979 = 8089469) B8089469
theorem B8113769 : Blo 1064615 8113769 := bstep (se 2 (by rfl) ⟨3042663, by rfl⟩ : syracuseStep 8113769 = 6085327) B6085327
theorem B5398487 : Blo 1064615 5398487 := bstep (se 1 (by rfl) ⟨4048865, by rfl⟩ : syracuseStep 5398487 = 8097731) B8097731
theorem B43773047 : Blo 1064615 43773047 := bstep (se 1 (by rfl) ⟨32829785, by rfl⟩ : syracuseStep 43773047 = 65659571) B65659571
theorem B7308647 : Blo 1064615 7308647 := bstep (se 1 (by rfl) ⟨5481485, by rfl⟩ : syracuseStep 7308647 = 10962971) B10962971
theorem B5409179 : Blo 1064615 5409179 := bstep (se 1 (by rfl) ⟨4056884, by rfl⟩ : syracuseStep 5409179 = 8113769) B8113769
theorem B55324403 : Blo 1064615 55324403 := bstep (se 1 (by rfl) ⟨41493302, by rfl⟩ : syracuseStep 55324403 = 82986605) B82986605
theorem B3649505 : Blo 1064615 3649505 := bstep (se 2 (by rfl) ⟨1368564, by rfl⟩ : syracuseStep 3649505 = 2737129) B2737129
theorem B2404331 : Blo 1064615 2404331 := bstep (se 1 (by rfl) ⟨1803248, by rfl⟩ : syracuseStep 2404331 = 3606497) B3606497
theorem B8106479 : Blo 1064615 8106479 := bstep (se 1 (by rfl) ⟨6079859, by rfl⟩ : syracuseStep 8106479 = 12159719) B12159719
theorem B29603825 : Blo 1064615 29603825 := bstep (se 2 (by rfl) ⟨11101434, by rfl⟩ : syracuseStep 29603825 = 22202869) B22202869
theorem B29182031 : Blo 1064615 29182031 := bstep (se 1 (by rfl) ⟨21886523, by rfl⟩ : syracuseStep 29182031 = 43773047) B43773047
theorem B3595319 : Blo 1064615 3595319 := bstep (se 1 (by rfl) ⟨2696489, by rfl⟩ : syracuseStep 3595319 = 5392979) B5392979
theorem B1598207 : Blo 1064615 1598207 := bstep (se 1 (by rfl) ⟨1198655, by rfl⟩ : syracuseStep 1598207 = 2397311) B2397311
theorem B3598991 : Blo 1064615 3598991 := bstep (se 1 (by rfl) ⟨2699243, by rfl⟩ : syracuseStep 3598991 = 5398487) B5398487
theorem B4553455 : Blo 1064615 4553455 := bstep (se 1 (by rfl) ⟨3415091, by rfl⟩ : syracuseStep 4553455 = 6830183) B6830183
theorem B3606119 : Blo 1064615 3606119 := bstep (se 1 (by rfl) ⟨2704589, by rfl⟩ : syracuseStep 3606119 = 5409179) B5409179
theorem B2396879 : Blo 1064615 2396879 := bstep (se 1 (by rfl) ⟨1797659, by rfl⟩ : syracuseStep 2396879 = 3595319) B3595319
theorem B2399327 : Blo 1064615 2399327 := bstep (se 1 (by rfl) ⟨1799495, by rfl⟩ : syracuseStep 2399327 = 3598991) B3598991
theorem B6071273 : Blo 1064615 6071273 := bstep (se 2 (by rfl) ⟨2276727, by rfl⟩ : syracuseStep 6071273 = 4553455) B4553455
theorem B19735883 : Blo 1064615 19735883 := bstep (se 1 (by rfl) ⟨14801912, by rfl⟩ : syracuseStep 19735883 = 29603825) B29603825
theorem B1065471 : Blo 1064615 1065471 := bstep (se 1 (by rfl) ⟨799103, by rfl⟩ : syracuseStep 1065471 = 1598207) B1598207
theorem B36882935 : Blo 1064615 36882935 := bstep (se 1 (by rfl) ⟨27662201, by rfl⟩ : syracuseStep 36882935 = 55324403) B55324403
theorem B4872431 : Blo 1064615 4872431 := bstep (se 1 (by rfl) ⟨3654323, by rfl⟩ : syracuseStep 4872431 = 7308647) B7308647
theorem B19454687 : Blo 1064615 19454687 := bstep (se 1 (by rfl) ⟨14591015, by rfl⟩ : syracuseStep 19454687 = 29182031) B29182031
theorem B1602887 : Blo 1064615 1602887 := bstep (se 1 (by rfl) ⟨1202165, by rfl⟩ : syracuseStep 1602887 = 2404331) B2404331
theorem B5404319 : Blo 1064615 5404319 := bstep (se 1 (by rfl) ⟨4053239, by rfl⟩ : syracuseStep 5404319 = 8106479) B8106479
theorem B38928053 : Blo 1064615 38928053 := bstep (se 5 (by rfl) ⟨1824752, by rfl⟩ : syracuseStep 38928053 = 3649505) B3649505
theorem B2404079 : Blo 1064615 2404079 := bstep (se 1 (by rfl) ⟨1803059, by rfl⟩ : syracuseStep 2404079 = 3606119) B3606119
theorem B24588623 : Blo 1064615 24588623 := bstep (se 1 (by rfl) ⟨18441467, by rfl⟩ : syracuseStep 24588623 = 36882935) B36882935
theorem B12993149 : Blo 1064615 12993149 := bstep (se 3 (by rfl) ⟨2436215, by rfl⟩ : syracuseStep 12993149 = 4872431) B4872431
theorem B4047515 : Blo 1064615 4047515 := bstep (se 1 (by rfl) ⟨3035636, by rfl⟩ : syracuseStep 4047515 = 6071273) B6071273
theorem B13157255 : Blo 1064615 13157255 := bstep (se 1 (by rfl) ⟨9867941, by rfl⟩ : syracuseStep 13157255 = 19735883) B19735883
theorem B1068591 : Blo 1064615 1068591 := bstep (se 1 (by rfl) ⟨801443, by rfl⟩ : syracuseStep 1068591 = 1602887) B1602887
theorem B1597919 : Blo 1064615 1597919 := bstep (se 1 (by rfl) ⟨1198439, by rfl⟩ : syracuseStep 1597919 = 2396879) B2396879
theorem B12969791 : Blo 1064615 12969791 := bstep (se 1 (by rfl) ⟨9727343, by rfl⟩ : syracuseStep 12969791 = 19454687) B19454687
theorem B1599551 : Blo 1064615 1599551 := bstep (se 1 (by rfl) ⟨1199663, by rfl⟩ : syracuseStep 1599551 = 2399327) B2399327
theorem B3602879 : Blo 1064615 3602879 := bstep (se 1 (by rfl) ⟨2702159, by rfl⟩ : syracuseStep 3602879 = 5404319) B5404319
theorem B103808141 : Blo 1064615 103808141 := bstep (se 3 (by rfl) ⟨19464026, by rfl⟩ : syracuseStep 103808141 = 38928053) B38928053
theorem B16392415 : Blo 1064615 16392415 := bstep (se 1 (by rfl) ⟨12294311, by rfl⟩ : syracuseStep 16392415 = 24588623) B24588623
theorem B2401919 : Blo 1064615 2401919 := bstep (se 1 (by rfl) ⟨1801439, by rfl⟩ : syracuseStep 2401919 = 3602879) B3602879
theorem B8662099 : Blo 1064615 8662099 := bstep (se 1 (by rfl) ⟨6496574, by rfl⟩ : syracuseStep 8662099 = 12993149) B12993149
theorem B2698343 : Blo 1064615 2698343 := bstep (se 1 (by rfl) ⟨2023757, by rfl⟩ : syracuseStep 2698343 = 4047515) B4047515
theorem B1065279 : Blo 1064615 1065279 := bstep (se 1 (by rfl) ⟨798959, by rfl⟩ : syracuseStep 1065279 = 1597919) B1597919
theorem B1066367 : Blo 1064615 1066367 := bstep (se 1 (by rfl) ⟨799775, by rfl⟩ : syracuseStep 1066367 = 1599551) B1599551
theorem B8771503 : Blo 1064615 8771503 := bstep (se 1 (by rfl) ⟨6578627, by rfl⟩ : syracuseStep 8771503 = 13157255) B13157255
theorem B8646527 : Blo 1064615 8646527 := bstep (se 1 (by rfl) ⟨6484895, by rfl⟩ : syracuseStep 8646527 = 12969791) B12969791
theorem B1602719 : Blo 1064615 1602719 := bstep (se 1 (by rfl) ⟨1202039, by rfl⟩ : syracuseStep 1602719 = 2404079) B2404079
theorem B69205427 : Blo 1064615 69205427 := bstep (se 1 (by rfl) ⟨51904070, by rfl⟩ : syracuseStep 69205427 = 103808141) B103808141
theorem B21856553 : Blo 1064615 21856553 := bstep (se 2 (by rfl) ⟨8196207, by rfl⟩ : syracuseStep 21856553 = 16392415) B16392415
theorem B11549465 : Blo 1064615 11549465 := bstep (se 2 (by rfl) ⟨4331049, by rfl⟩ : syracuseStep 11549465 = 8662099) B8662099
theorem B1068479 : Blo 1064615 1068479 := bstep (se 1 (by rfl) ⟨801359, by rfl⟩ : syracuseStep 1068479 = 1602719) B1602719
theorem B23057405 : Blo 1064615 23057405 := bstep (se 3 (by rfl) ⟨4323263, by rfl⟩ : syracuseStep 23057405 = 8646527) B8646527
theorem B1601279 : Blo 1064615 1601279 := bstep (se 1 (by rfl) ⟨1200959, by rfl⟩ : syracuseStep 1601279 = 2401919) B2401919
theorem B1798895 : Blo 1064615 1798895 := bstep (se 1 (by rfl) ⟨1349171, by rfl⟩ : syracuseStep 1798895 = 2698343) B2698343
theorem B11695337 : Blo 1064615 11695337 := bstep (se 2 (by rfl) ⟨4385751, by rfl⟩ : syracuseStep 11695337 = 8771503) B8771503
theorem B46136951 : Blo 1064615 46136951 := bstep (se 1 (by rfl) ⟨34602713, by rfl⟩ : syracuseStep 46136951 = 69205427) B69205427
theorem B15371603 : Blo 1064615 15371603 := bstep (se 1 (by rfl) ⟨11528702, by rfl⟩ : syracuseStep 15371603 = 23057405) B23057405
theorem B1067519 : Blo 1064615 1067519 := bstep (se 1 (by rfl) ⟨800639, by rfl⟩ : syracuseStep 1067519 = 1601279) B1601279
theorem B1199263 : Blo 1064615 1199263 := bstep (se 1 (by rfl) ⟨899447, by rfl⟩ : syracuseStep 1199263 = 1798895) B1798895
theorem B30757967 : Blo 1064615 30757967 := bstep (se 1 (by rfl) ⟨23068475, by rfl⟩ : syracuseStep 30757967 = 46136951) B46136951
theorem B14571035 : Blo 1064615 14571035 := bstep (se 1 (by rfl) ⟨10928276, by rfl⟩ : syracuseStep 14571035 = 21856553) B21856553
theorem B7796891 : Blo 1064615 7796891 := bstep (se 1 (by rfl) ⟨5847668, by rfl⟩ : syracuseStep 7796891 = 11695337) B11695337
theorem B7699643 : Blo 1064615 7699643 := bstep (se 1 (by rfl) ⟨5774732, by rfl⟩ : syracuseStep 7699643 = 11549465) B11549465
theorem B9714023 : Blo 1064615 9714023 := bstep (se 1 (by rfl) ⟨7285517, by rfl⟩ : syracuseStep 9714023 = 14571035) B14571035
theorem B5197927 : Blo 1064615 5197927 := bstep (se 1 (by rfl) ⟨3898445, by rfl⟩ : syracuseStep 5197927 = 7796891) B7796891
theorem B5133095 : Blo 1064615 5133095 := bstep (se 1 (by rfl) ⟨3849821, by rfl⟩ : syracuseStep 5133095 = 7699643) B7699643
theorem B10247735 : Blo 1064615 10247735 := bstep (se 1 (by rfl) ⟨7685801, by rfl⟩ : syracuseStep 10247735 = 15371603) B15371603
theorem B20505311 : Blo 1064615 20505311 := bstep (se 1 (by rfl) ⟨15378983, by rfl⟩ : syracuseStep 20505311 = 30757967) B30757967
theorem B1599017 : Blo 1064615 1599017 := bstep (se 2 (by rfl) ⟨599631, by rfl⟩ : syracuseStep 1599017 = 1199263) B1199263
theorem B13670207 : Blo 1064615 13670207 := bstep (se 1 (by rfl) ⟨10252655, by rfl⟩ : syracuseStep 13670207 = 20505311) B20505311
theorem B3422063 : Blo 1064615 3422063 := bstep (se 1 (by rfl) ⟨2566547, by rfl⟩ : syracuseStep 3422063 = 5133095) B5133095
theorem B6831823 : Blo 1064615 6831823 := bstep (se 1 (by rfl) ⟨5123867, by rfl⟩ : syracuseStep 6831823 = 10247735) B10247735
theorem B6930569 : Blo 1064615 6930569 := bstep (se 2 (by rfl) ⟨2598963, by rfl⟩ : syracuseStep 6930569 = 5197927) B5197927
theorem B1066011 : Blo 1064615 1066011 := bstep (se 1 (by rfl) ⟨799508, by rfl⟩ : syracuseStep 1066011 = 1599017) B1599017
theorem B6476015 : Blo 1064615 6476015 := bstep (se 1 (by rfl) ⟨4857011, by rfl⟩ : syracuseStep 6476015 = 9714023) B9714023
theorem B18481517 : Blo 1064615 18481517 := bstep (se 3 (by rfl) ⟨3465284, by rfl⟩ : syracuseStep 18481517 = 6930569) B6930569
theorem B9113471 : Blo 1064615 9113471 := bstep (se 1 (by rfl) ⟨6835103, by rfl⟩ : syracuseStep 9113471 = 13670207) B13670207
theorem B2281375 : Blo 1064615 2281375 := bstep (se 1 (by rfl) ⟨1711031, by rfl⟩ : syracuseStep 2281375 = 3422063) B3422063
theorem B4317343 : Blo 1064615 4317343 := bstep (se 1 (by rfl) ⟨3238007, by rfl⟩ : syracuseStep 4317343 = 6476015) B6476015
theorem B9109097 : Blo 1064615 9109097 := bstep (se 2 (by rfl) ⟨3415911, by rfl⟩ : syracuseStep 9109097 = 6831823) B6831823
theorem B12321011 : Blo 1064615 12321011 := bstep (se 1 (by rfl) ⟨9240758, by rfl⟩ : syracuseStep 12321011 = 18481517) B18481517
theorem B6072731 : Blo 1064615 6072731 := bstep (se 1 (by rfl) ⟨4554548, by rfl⟩ : syracuseStep 6072731 = 9109097) B9109097
theorem B6075647 : Blo 1064615 6075647 := bstep (se 1 (by rfl) ⟨4556735, by rfl⟩ : syracuseStep 6075647 = 9113471) B9113471
theorem B23025829 : Blo 1064615 23025829 := bstep (se 4 (by rfl) ⟨2158671, by rfl⟩ : syracuseStep 23025829 = 4317343) B4317343
theorem B3041833 : Blo 1064615 3041833 := bstep (se 2 (by rfl) ⟨1140687, by rfl⟩ : syracuseStep 3041833 = 2281375) B2281375
theorem B4048487 : Blo 1064615 4048487 := bstep (se 1 (by rfl) ⟨3036365, by rfl⟩ : syracuseStep 4048487 = 6072731) B6072731
theorem B4050431 : Blo 1064615 4050431 := bstep (se 1 (by rfl) ⟨3037823, by rfl⟩ : syracuseStep 4050431 = 6075647) B6075647
theorem B8214007 : Blo 1064615 8214007 := bstep (se 1 (by rfl) ⟨6160505, by rfl⟩ : syracuseStep 8214007 = 12321011) B12321011
theorem B4055777 : Blo 1064615 4055777 := bstep (se 2 (by rfl) ⟨1520916, by rfl⟩ : syracuseStep 4055777 = 3041833) B3041833
theorem B30701105 : Blo 1064615 30701105 := bstep (se 2 (by rfl) ⟨11512914, by rfl⟩ : syracuseStep 30701105 = 23025829) B23025829
theorem B10952009 : Blo 1064615 10952009 := bstep (se 2 (by rfl) ⟨4107003, by rfl⟩ : syracuseStep 10952009 = 8214007) B8214007
theorem B2698991 : Blo 1064615 2698991 := bstep (se 1 (by rfl) ⟨2024243, by rfl⟩ : syracuseStep 2698991 = 4048487) B4048487
theorem B2700287 : Blo 1064615 2700287 := bstep (se 1 (by rfl) ⟨2025215, by rfl⟩ : syracuseStep 2700287 = 4050431) B4050431
theorem B2703851 : Blo 1064615 2703851 := bstep (se 1 (by rfl) ⟨2027888, by rfl⟩ : syracuseStep 2703851 = 4055777) B4055777
theorem B20467403 : Blo 1064615 20467403 := bstep (se 1 (by rfl) ⟨15350552, by rfl⟩ : syracuseStep 20467403 = 30701105) B30701105
theorem B1802567 : Blo 1064615 1802567 := bstep (se 1 (by rfl) ⟨1351925, by rfl⟩ : syracuseStep 1802567 = 2703851) B2703851
theorem B13644935 : Blo 1064615 13644935 := bstep (se 1 (by rfl) ⟨10233701, by rfl⟩ : syracuseStep 13644935 = 20467403) B20467403
theorem B7301339 : Blo 1064615 7301339 := bstep (se 1 (by rfl) ⟨5476004, by rfl⟩ : syracuseStep 7301339 = 10952009) B10952009
theorem B1799327 : Blo 1064615 1799327 := bstep (se 1 (by rfl) ⟨1349495, by rfl⟩ : syracuseStep 1799327 = 2698991) B2698991
theorem B1800191 : Blo 1064615 1800191 := bstep (se 1 (by rfl) ⟨1350143, by rfl⟩ : syracuseStep 1800191 = 2700287) B2700287
theorem B4867559 : Blo 1064615 4867559 := bstep (se 1 (by rfl) ⟨3650669, by rfl⟩ : syracuseStep 4867559 = 7301339) B7301339
theorem B9096623 : Blo 1064615 9096623 := bstep (se 1 (by rfl) ⟨6822467, by rfl⟩ : syracuseStep 9096623 = 13644935) B13644935
theorem B1199551 : Blo 1064615 1199551 := bstep (se 1 (by rfl) ⟨899663, by rfl⟩ : syracuseStep 1199551 = 1799327) B1799327
theorem B1200127 : Blo 1064615 1200127 := bstep (se 1 (by rfl) ⟨900095, by rfl⟩ : syracuseStep 1200127 = 1800191) B1800191
theorem B1201711 : Blo 1064615 1201711 := bstep (se 1 (by rfl) ⟨901283, by rfl⟩ : syracuseStep 1201711 = 1802567) B1802567
theorem B3245039 : Blo 1064615 3245039 := bstep (se 1 (by rfl) ⟨2433779, by rfl⟩ : syracuseStep 3245039 = 4867559) B4867559
theorem B6064415 : Blo 1064615 6064415 := bstep (se 1 (by rfl) ⟨4548311, by rfl⟩ : syracuseStep 6064415 = 9096623) B9096623
theorem B1599401 : Blo 1064615 1599401 := bstep (se 2 (by rfl) ⟨599775, by rfl⟩ : syracuseStep 1599401 = 1199551) B1199551
theorem B1600169 : Blo 1064615 1600169 := bstep (se 2 (by rfl) ⟨600063, by rfl⟩ : syracuseStep 1600169 = 1200127) B1200127
theorem B1602281 : Blo 1064615 1602281 := bstep (se 2 (by rfl) ⟨600855, by rfl⟩ : syracuseStep 1602281 = 1201711) B1201711
theorem B2163359 : Blo 1064615 2163359 := bstep (se 1 (by rfl) ⟨1622519, by rfl⟩ : syracuseStep 2163359 = 3245039) B3245039
theorem B4042943 : Blo 1064615 4042943 := bstep (se 1 (by rfl) ⟨3032207, by rfl⟩ : syracuseStep 4042943 = 6064415) B6064415
theorem B1066267 : Blo 1064615 1066267 := bstep (se 1 (by rfl) ⟨799700, by rfl⟩ : syracuseStep 1066267 = 1599401) B1599401
theorem B1066779 : Blo 1064615 1066779 := bstep (se 1 (by rfl) ⟨800084, by rfl⟩ : syracuseStep 1066779 = 1600169) B1600169
theorem B1068187 : Blo 1064615 1068187 := bstep (se 1 (by rfl) ⟨801140, by rfl⟩ : syracuseStep 1068187 = 1602281) B1602281
theorem B5768957 : Blo 1064615 5768957 := bstep (se 3 (by rfl) ⟨1081679, by rfl⟩ : syracuseStep 5768957 = 2163359) B2163359
theorem B2695295 : Blo 1064615 2695295 := bstep (se 1 (by rfl) ⟨2021471, by rfl⟩ : syracuseStep 2695295 = 4042943) B4042943
theorem B3845971 : Blo 1064615 3845971 := bstep (se 1 (by rfl) ⟨2884478, by rfl⟩ : syracuseStep 3845971 = 5768957) B5768957
theorem B1796863 : Blo 1064615 1796863 := bstep (se 1 (by rfl) ⟨1347647, by rfl⟩ : syracuseStep 1796863 = 2695295) B2695295
theorem B2395817 : Blo 1064615 2395817 := bstep (se 2 (by rfl) ⟨898431, by rfl⟩ : syracuseStep 2395817 = 1796863) B1796863
theorem B5127961 : Blo 1064615 5127961 := bstep (se 2 (by rfl) ⟨1922985, by rfl⟩ : syracuseStep 5127961 = 3845971) B3845971
theorem B6837281 : Blo 1064615 6837281 := bstep (se 2 (by rfl) ⟨2563980, by rfl⟩ : syracuseStep 6837281 = 5127961) B5127961
theorem B1597211 : Blo 1064615 1597211 := bstep (se 1 (by rfl) ⟨1197908, by rfl⟩ : syracuseStep 1597211 = 2395817) B2395817
theorem B4558187 : Blo 1064615 4558187 := bstep (se 1 (by rfl) ⟨3418640, by rfl⟩ : syracuseStep 4558187 = 6837281) B6837281
theorem B1064807 : Blo 1064615 1064807 := bstep (se 1 (by rfl) ⟨798605, by rfl⟩ : syracuseStep 1064807 = 1597211) B1597211
theorem B3038791 : Blo 1064615 3038791 := bstep (se 1 (by rfl) ⟨2279093, by rfl⟩ : syracuseStep 3038791 = 4558187) B4558187
theorem B4051721 : Blo 1064615 4051721 := bstep (se 2 (by rfl) ⟨1519395, by rfl⟩ : syracuseStep 4051721 = 3038791) B3038791
theorem B2701147 : Blo 1064615 2701147 := bstep (se 1 (by rfl) ⟨2025860, by rfl⟩ : syracuseStep 2701147 = 4051721) B4051721
theorem B3601529 : Blo 1064615 3601529 := bstep (se 2 (by rfl) ⟨1350573, by rfl⟩ : syracuseStep 3601529 = 2701147) B2701147
theorem B2401019 : Blo 1064615 2401019 := bstep (se 1 (by rfl) ⟨1800764, by rfl⟩ : syracuseStep 2401019 = 3601529) B3601529
theorem B1600679 : Blo 1064615 1600679 := bstep (se 1 (by rfl) ⟨1200509, by rfl⟩ : syracuseStep 1600679 = 2401019) B2401019
theorem B1067119 : Blo 1064615 1067119 := bstep (se 1 (by rfl) ⟨800339, by rfl⟩ : syracuseStep 1067119 = 1600679) B1600679

theorem C0 (j : ℕ) (h1 : 266153 ≤ j) (h2 : j ≤ 266852) : Blo 1064615 (4 * j + 3) := by
  interval_cases j
  · exact B1064615
  · exact B1064619
  · exact B1064623
  · exact B1064627
  · exact B1064631
  · exact B1064635
  · exact B1064639
  · exact B1064643
  · exact B1064647
  · exact B1064651
  · exact B1064655
  · exact B1064659
  · exact B1064663
  · exact B1064667
  · exact B1064671
  · exact B1064675
  · exact B1064679
  · exact B1064683
  · exact B1064687
  · exact B1064691
  · exact B1064695
  · exact B1064699
  · exact B1064703
  · exact B1064707
  · exact B1064711
  · exact B1064715
  · exact B1064719
  · exact B1064723
  · exact B1064727
  · exact B1064731
  · exact B1064735
  · exact B1064739
  · exact B1064743
  · exact B1064747
  · exact B1064751
  · exact B1064755
  · exact B1064759
  · exact B1064763
  · exact B1064767
  · exact B1064771
  · exact B1064775
  · exact B1064779
  · exact B1064783
  · exact B1064787
  · exact B1064791
  · exact B1064795
  · exact B1064799
  · exact B1064803
  · exact B1064807
  · exact B1064811
  · exact B1064815
  · exact B1064819
  · exact B1064823
  · exact B1064827
  · exact B1064831
  · exact B1064835
  · exact B1064839
  · exact B1064843
  · exact B1064847
  · exact B1064851
  · exact B1064855
  · exact B1064859
  · exact B1064863
  · exact B1064867
  · exact B1064871
  · exact B1064875
  · exact B1064879
  · exact B1064883
  · exact B1064887
  · exact B1064891
  · exact B1064895
  · exact B1064899
  · exact B1064903
  · exact B1064907
  · exact B1064911
  · exact B1064915
  · exact B1064919
  · exact B1064923
  · exact B1064927
  · exact B1064931
  · exact B1064935
  · exact B1064939
  · exact B1064943
  · exact B1064947
  · exact B1064951
  · exact B1064955
  · exact B1064959
  · exact B1064963
  · exact B1064967
  · exact B1064971
  · exact B1064975
  · exact B1064979
  · exact B1064983
  · exact B1064987
  · exact B1064991
  · exact B1064995
  · exact B1064999
  · exact B1065003
  · exact B1065007
  · exact B1065011
  · exact B1065015
  · exact B1065019
  · exact B1065023
  · exact B1065027
  · exact B1065031
  · exact B1065035
  · exact B1065039
  · exact B1065043
  · exact B1065047
  · exact B1065051
  · exact B1065055
  · exact B1065059
  · exact B1065063
  · exact B1065067
  · exact B1065071
  · exact B1065075
  · exact B1065079
  · exact B1065083
  · exact B1065087
  · exact B1065091
  · exact B1065095
  · exact B1065099
  · exact B1065103
  · exact B1065107
  · exact B1065111
  · exact B1065115
  · exact B1065119
  · exact B1065123
  · exact B1065127
  · exact B1065131
  · exact B1065135
  · exact B1065139
  · exact B1065143
  · exact B1065147
  · exact B1065151
  · exact B1065155
  · exact B1065159
  · exact B1065163
  · exact B1065167
  · exact B1065171
  · exact B1065175
  · exact B1065179
  · exact B1065183
  · exact B1065187
  · exact B1065191
  · exact B1065195
  · exact B1065199
  · exact B1065203
  · exact B1065207
  · exact B1065211
  · exact B1065215
  · exact B1065219
  · exact B1065223
  · exact B1065227
  · exact B1065231
  · exact B1065235
  · exact B1065239
  · exact B1065243
  · exact B1065247
  · exact B1065251
  · exact B1065255
  · exact B1065259
  · exact B1065263
  · exact B1065267
  · exact B1065271
  · exact B1065275
  · exact B1065279
  · exact B1065283
  · exact B1065287
  · exact B1065291
  · exact B1065295
  · exact B1065299
  · exact B1065303
  · exact B1065307
  · exact B1065311
  · exact B1065315
  · exact B1065319
  · exact B1065323
  · exact B1065327
  · exact B1065331
  · exact B1065335
  · exact B1065339
  · exact B1065343
  · exact B1065347
  · exact B1065351
  · exact B1065355
  · exact B1065359
  · exact B1065363
  · exact B1065367
  · exact B1065371
  · exact B1065375
  · exact B1065379
  · exact B1065383
  · exact B1065387
  · exact B1065391
  · exact B1065395
  · exact B1065399
  · exact B1065403
  · exact B1065407
  · exact B1065411
  · exact B1065415
  · exact B1065419
  · exact B1065423
  · exact B1065427
  · exact B1065431
  · exact B1065435
  · exact B1065439
  · exact B1065443
  · exact B1065447
  · exact B1065451
  · exact B1065455
  · exact B1065459
  · exact B1065463
  · exact B1065467
  · exact B1065471
  · exact B1065475
  · exact B1065479
  · exact B1065483
  · exact B1065487
  · exact B1065491
  · exact B1065495
  · exact B1065499
  · exact B1065503
  · exact B1065507
  · exact B1065511
  · exact B1065515
  · exact B1065519
  · exact B1065523
  · exact B1065527
  · exact B1065531
  · exact B1065535
  · exact B1065539
  · exact B1065543
  · exact B1065547
  · exact B1065551
  · exact B1065555
  · exact B1065559
  · exact B1065563
  · exact B1065567
  · exact B1065571
  · exact B1065575
  · exact B1065579
  · exact B1065583
  · exact B1065587
  · exact B1065591
  · exact B1065595
  · exact B1065599
  · exact B1065603
  · exact B1065607
  · exact B1065611
  · exact B1065615
  · exact B1065619
  · exact B1065623
  · exact B1065627
  · exact B1065631
  · exact B1065635
  · exact B1065639
  · exact B1065643
  · exact B1065647
  · exact B1065651
  · exact B1065655
  · exact B1065659
  · exact B1065663
  · exact B1065667
  · exact B1065671
  · exact B1065675
  · exact B1065679
  · exact B1065683
  · exact B1065687
  · exact B1065691
  · exact B1065695
  · exact B1065699
  · exact B1065703
  · exact B1065707
  · exact B1065711
  · exact B1065715
  · exact B1065719
  · exact B1065723
  · exact B1065727
  · exact B1065731
  · exact B1065735
  · exact B1065739
  · exact B1065743
  · exact B1065747
  · exact B1065751
  · exact B1065755
  · exact B1065759
  · exact B1065763
  · exact B1065767
  · exact B1065771
  · exact B1065775
  · exact B1065779
  · exact B1065783
  · exact B1065787
  · exact B1065791
  · exact B1065795
  · exact B1065799
  · exact B1065803
  · exact B1065807
  · exact B1065811
  · exact B1065815
  · exact B1065819
  · exact B1065823
  · exact B1065827
  · exact B1065831
  · exact B1065835
  · exact B1065839
  · exact B1065843
  · exact B1065847
  · exact B1065851
  · exact B1065855
  · exact B1065859
  · exact B1065863
  · exact B1065867
  · exact B1065871
  · exact B1065875
  · exact B1065879
  · exact B1065883
  · exact B1065887
  · exact B1065891
  · exact B1065895
  · exact B1065899
  · exact B1065903
  · exact B1065907
  · exact B1065911
  · exact B1065915
  · exact B1065919
  · exact B1065923
  · exact B1065927
  · exact B1065931
  · exact B1065935
  · exact B1065939
  · exact B1065943
  · exact B1065947
  · exact B1065951
  · exact B1065955
  · exact B1065959
  · exact B1065963
  · exact B1065967
  · exact B1065971
  · exact B1065975
  · exact B1065979
  · exact B1065983
  · exact B1065987
  · exact B1065991
  · exact B1065995
  · exact B1065999
  · exact B1066003
  · exact B1066007
  · exact B1066011
  · exact B1066015
  · exact B1066019
  · exact B1066023
  · exact B1066027
  · exact B1066031
  · exact B1066035
  · exact B1066039
  · exact B1066043
  · exact B1066047
  · exact B1066051
  · exact B1066055
  · exact B1066059
  · exact B1066063
  · exact B1066067
  · exact B1066071
  · exact B1066075
  · exact B1066079
  · exact B1066083
  · exact B1066087
  · exact B1066091
  · exact B1066095
  · exact B1066099
  · exact B1066103
  · exact B1066107
  · exact B1066111
  · exact B1066115
  · exact B1066119
  · exact B1066123
  · exact B1066127
  · exact B1066131
  · exact B1066135
  · exact B1066139
  · exact B1066143
  · exact B1066147
  · exact B1066151
  · exact B1066155
  · exact B1066159
  · exact B1066163
  · exact B1066167
  · exact B1066171
  · exact B1066175
  · exact B1066179
  · exact B1066183
  · exact B1066187
  · exact B1066191
  · exact B1066195
  · exact B1066199
  · exact B1066203
  · exact B1066207
  · exact B1066211
  · exact B1066215
  · exact B1066219
  · exact B1066223
  · exact B1066227
  · exact B1066231
  · exact B1066235
  · exact B1066239
  · exact B1066243
  · exact B1066247
  · exact B1066251
  · exact B1066255
  · exact B1066259
  · exact B1066263
  · exact B1066267
  · exact B1066271
  · exact B1066275
  · exact B1066279
  · exact B1066283
  · exact B1066287
  · exact B1066291
  · exact B1066295
  · exact B1066299
  · exact B1066303
  · exact B1066307
  · exact B1066311
  · exact B1066315
  · exact B1066319
  · exact B1066323
  · exact B1066327
  · exact B1066331
  · exact B1066335
  · exact B1066339
  · exact B1066343
  · exact B1066347
  · exact B1066351
  · exact B1066355
  · exact B1066359
  · exact B1066363
  · exact B1066367
  · exact B1066371
  · exact B1066375
  · exact B1066379
  · exact B1066383
  · exact B1066387
  · exact B1066391
  · exact B1066395
  · exact B1066399
  · exact B1066403
  · exact B1066407
  · exact B1066411
  · exact B1066415
  · exact B1066419
  · exact B1066423
  · exact B1066427
  · exact B1066431
  · exact B1066435
  · exact B1066439
  · exact B1066443
  · exact B1066447
  · exact B1066451
  · exact B1066455
  · exact B1066459
  · exact B1066463
  · exact B1066467
  · exact B1066471
  · exact B1066475
  · exact B1066479
  · exact B1066483
  · exact B1066487
  · exact B1066491
  · exact B1066495
  · exact B1066499
  · exact B1066503
  · exact B1066507
  · exact B1066511
  · exact B1066515
  · exact B1066519
  · exact B1066523
  · exact B1066527
  · exact B1066531
  · exact B1066535
  · exact B1066539
  · exact B1066543
  · exact B1066547
  · exact B1066551
  · exact B1066555
  · exact B1066559
  · exact B1066563
  · exact B1066567
  · exact B1066571
  · exact B1066575
  · exact B1066579
  · exact B1066583
  · exact B1066587
  · exact B1066591
  · exact B1066595
  · exact B1066599
  · exact B1066603
  · exact B1066607
  · exact B1066611
  · exact B1066615
  · exact B1066619
  · exact B1066623
  · exact B1066627
  · exact B1066631
  · exact B1066635
  · exact B1066639
  · exact B1066643
  · exact B1066647
  · exact B1066651
  · exact B1066655
  · exact B1066659
  · exact B1066663
  · exact B1066667
  · exact B1066671
  · exact B1066675
  · exact B1066679
  · exact B1066683
  · exact B1066687
  · exact B1066691
  · exact B1066695
  · exact B1066699
  · exact B1066703
  · exact B1066707
  · exact B1066711
  · exact B1066715
  · exact B1066719
  · exact B1066723
  · exact B1066727
  · exact B1066731
  · exact B1066735
  · exact B1066739
  · exact B1066743
  · exact B1066747
  · exact B1066751
  · exact B1066755
  · exact B1066759
  · exact B1066763
  · exact B1066767
  · exact B1066771
  · exact B1066775
  · exact B1066779
  · exact B1066783
  · exact B1066787
  · exact B1066791
  · exact B1066795
  · exact B1066799
  · exact B1066803
  · exact B1066807
  · exact B1066811
  · exact B1066815
  · exact B1066819
  · exact B1066823
  · exact B1066827
  · exact B1066831
  · exact B1066835
  · exact B1066839
  · exact B1066843
  · exact B1066847
  · exact B1066851
  · exact B1066855
  · exact B1066859
  · exact B1066863
  · exact B1066867
  · exact B1066871
  · exact B1066875
  · exact B1066879
  · exact B1066883
  · exact B1066887
  · exact B1066891
  · exact B1066895
  · exact B1066899
  · exact B1066903
  · exact B1066907
  · exact B1066911
  · exact B1066915
  · exact B1066919
  · exact B1066923
  · exact B1066927
  · exact B1066931
  · exact B1066935
  · exact B1066939
  · exact B1066943
  · exact B1066947
  · exact B1066951
  · exact B1066955
  · exact B1066959
  · exact B1066963
  · exact B1066967
  · exact B1066971
  · exact B1066975
  · exact B1066979
  · exact B1066983
  · exact B1066987
  · exact B1066991
  · exact B1066995
  · exact B1066999
  · exact B1067003
  · exact B1067007
  · exact B1067011
  · exact B1067015
  · exact B1067019
  · exact B1067023
  · exact B1067027
  · exact B1067031
  · exact B1067035
  · exact B1067039
  · exact B1067043
  · exact B1067047
  · exact B1067051
  · exact B1067055
  · exact B1067059
  · exact B1067063
  · exact B1067067
  · exact B1067071
  · exact B1067075
  · exact B1067079
  · exact B1067083
  · exact B1067087
  · exact B1067091
  · exact B1067095
  · exact B1067099
  · exact B1067103
  · exact B1067107
  · exact B1067111
  · exact B1067115
  · exact B1067119
  · exact B1067123
  · exact B1067127
  · exact B1067131
  · exact B1067135
  · exact B1067139
  · exact B1067143
  · exact B1067147
  · exact B1067151
  · exact B1067155
  · exact B1067159
  · exact B1067163
  · exact B1067167
  · exact B1067171
  · exact B1067175
  · exact B1067179
  · exact B1067183
  · exact B1067187
  · exact B1067191
  · exact B1067195
  · exact B1067199
  · exact B1067203
  · exact B1067207
  · exact B1067211
  · exact B1067215
  · exact B1067219
  · exact B1067223
  · exact B1067227
  · exact B1067231
  · exact B1067235
  · exact B1067239
  · exact B1067243
  · exact B1067247
  · exact B1067251
  · exact B1067255
  · exact B1067259
  · exact B1067263
  · exact B1067267
  · exact B1067271
  · exact B1067275
  · exact B1067279
  · exact B1067283
  · exact B1067287
  · exact B1067291
  · exact B1067295
  · exact B1067299
  · exact B1067303
  · exact B1067307
  · exact B1067311
  · exact B1067315
  · exact B1067319
  · exact B1067323
  · exact B1067327
  · exact B1067331
  · exact B1067335
  · exact B1067339
  · exact B1067343
  · exact B1067347
  · exact B1067351
  · exact B1067355
  · exact B1067359
  · exact B1067363
  · exact B1067367
  · exact B1067371
  · exact B1067375
  · exact B1067379
  · exact B1067383
  · exact B1067387
  · exact B1067391
  · exact B1067395
  · exact B1067399
  · exact B1067403
  · exact B1067407
  · exact B1067411

theorem C1 (j : ℕ) (h1 : 266853 ≤ j) (h2 : j ≤ 267153) : Blo 1064615 (4 * j + 3) := by
  interval_cases j
  · exact B1067415
  · exact B1067419
  · exact B1067423
  · exact B1067427
  · exact B1067431
  · exact B1067435
  · exact B1067439
  · exact B1067443
  · exact B1067447
  · exact B1067451
  · exact B1067455
  · exact B1067459
  · exact B1067463
  · exact B1067467
  · exact B1067471
  · exact B1067475
  · exact B1067479
  · exact B1067483
  · exact B1067487
  · exact B1067491
  · exact B1067495
  · exact B1067499
  · exact B1067503
  · exact B1067507
  · exact B1067511
  · exact B1067515
  · exact B1067519
  · exact B1067523
  · exact B1067527
  · exact B1067531
  · exact B1067535
  · exact B1067539
  · exact B1067543
  · exact B1067547
  · exact B1067551
  · exact B1067555
  · exact B1067559
  · exact B1067563
  · exact B1067567
  · exact B1067571
  · exact B1067575
  · exact B1067579
  · exact B1067583
  · exact B1067587
  · exact B1067591
  · exact B1067595
  · exact B1067599
  · exact B1067603
  · exact B1067607
  · exact B1067611
  · exact B1067615
  · exact B1067619
  · exact B1067623
  · exact B1067627
  · exact B1067631
  · exact B1067635
  · exact B1067639
  · exact B1067643
  · exact B1067647
  · exact B1067651
  · exact B1067655
  · exact B1067659
  · exact B1067663
  · exact B1067667
  · exact B1067671
  · exact B1067675
  · exact B1067679
  · exact B1067683
  · exact B1067687
  · exact B1067691
  · exact B1067695
  · exact B1067699
  · exact B1067703
  · exact B1067707
  · exact B1067711
  · exact B1067715
  · exact B1067719
  · exact B1067723
  · exact B1067727
  · exact B1067731
  · exact B1067735
  · exact B1067739
  · exact B1067743
  · exact B1067747
  · exact B1067751
  · exact B1067755
  · exact B1067759
  · exact B1067763
  · exact B1067767
  · exact B1067771
  · exact B1067775
  · exact B1067779
  · exact B1067783
  · exact B1067787
  · exact B1067791
  · exact B1067795
  · exact B1067799
  · exact B1067803
  · exact B1067807
  · exact B1067811
  · exact B1067815
  · exact B1067819
  · exact B1067823
  · exact B1067827
  · exact B1067831
  · exact B1067835
  · exact B1067839
  · exact B1067843
  · exact B1067847
  · exact B1067851
  · exact B1067855
  · exact B1067859
  · exact B1067863
  · exact B1067867
  · exact B1067871
  · exact B1067875
  · exact B1067879
  · exact B1067883
  · exact B1067887
  · exact B1067891
  · exact B1067895
  · exact B1067899
  · exact B1067903
  · exact B1067907
  · exact B1067911
  · exact B1067915
  · exact B1067919
  · exact B1067923
  · exact B1067927
  · exact B1067931
  · exact B1067935
  · exact B1067939
  · exact B1067943
  · exact B1067947
  · exact B1067951
  · exact B1067955
  · exact B1067959
  · exact B1067963
  · exact B1067967
  · exact B1067971
  · exact B1067975
  · exact B1067979
  · exact B1067983
  · exact B1067987
  · exact B1067991
  · exact B1067995
  · exact B1067999
  · exact B1068003
  · exact B1068007
  · exact B1068011
  · exact B1068015
  · exact B1068019
  · exact B1068023
  · exact B1068027
  · exact B1068031
  · exact B1068035
  · exact B1068039
  · exact B1068043
  · exact B1068047
  · exact B1068051
  · exact B1068055
  · exact B1068059
  · exact B1068063
  · exact B1068067
  · exact B1068071
  · exact B1068075
  · exact B1068079
  · exact B1068083
  · exact B1068087
  · exact B1068091
  · exact B1068095
  · exact B1068099
  · exact B1068103
  · exact B1068107
  · exact B1068111
  · exact B1068115
  · exact B1068119
  · exact B1068123
  · exact B1068127
  · exact B1068131
  · exact B1068135
  · exact B1068139
  · exact B1068143
  · exact B1068147
  · exact B1068151
  · exact B1068155
  · exact B1068159
  · exact B1068163
  · exact B1068167
  · exact B1068171
  · exact B1068175
  · exact B1068179
  · exact B1068183
  · exact B1068187
  · exact B1068191
  · exact B1068195
  · exact B1068199
  · exact B1068203
  · exact B1068207
  · exact B1068211
  · exact B1068215
  · exact B1068219
  · exact B1068223
  · exact B1068227
  · exact B1068231
  · exact B1068235
  · exact B1068239
  · exact B1068243
  · exact B1068247
  · exact B1068251
  · exact B1068255
  · exact B1068259
  · exact B1068263
  · exact B1068267
  · exact B1068271
  · exact B1068275
  · exact B1068279
  · exact B1068283
  · exact B1068287
  · exact B1068291
  · exact B1068295
  · exact B1068299
  · exact B1068303
  · exact B1068307
  · exact B1068311
  · exact B1068315
  · exact B1068319
  · exact B1068323
  · exact B1068327
  · exact B1068331
  · exact B1068335
  · exact B1068339
  · exact B1068343
  · exact B1068347
  · exact B1068351
  · exact B1068355
  · exact B1068359
  · exact B1068363
  · exact B1068367
  · exact B1068371
  · exact B1068375
  · exact B1068379
  · exact B1068383
  · exact B1068387
  · exact B1068391
  · exact B1068395
  · exact B1068399
  · exact B1068403
  · exact B1068407
  · exact B1068411
  · exact B1068415
  · exact B1068419
  · exact B1068423
  · exact B1068427
  · exact B1068431
  · exact B1068435
  · exact B1068439
  · exact B1068443
  · exact B1068447
  · exact B1068451
  · exact B1068455
  · exact B1068459
  · exact B1068463
  · exact B1068467
  · exact B1068471
  · exact B1068475
  · exact B1068479
  · exact B1068483
  · exact B1068487
  · exact B1068491
  · exact B1068495
  · exact B1068499
  · exact B1068503
  · exact B1068507
  · exact B1068511
  · exact B1068515
  · exact B1068519
  · exact B1068523
  · exact B1068527
  · exact B1068531
  · exact B1068535
  · exact B1068539
  · exact B1068543
  · exact B1068547
  · exact B1068551
  · exact B1068555
  · exact B1068559
  · exact B1068563
  · exact B1068567
  · exact B1068571
  · exact B1068575
  · exact B1068579
  · exact B1068583
  · exact B1068587
  · exact B1068591
  · exact B1068595
  · exact B1068599
  · exact B1068603
  · exact B1068607
  · exact B1068611
  · exact B1068615

theorem solution (m : ℕ) (hlo : 1064615 ≤ m) (hhi : m ≤ 1068615) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 266153 ≤ j := by omega
    have hj2 : j ≤ 267153 := by omega
    have hb : Blo 1064615 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 266853 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
