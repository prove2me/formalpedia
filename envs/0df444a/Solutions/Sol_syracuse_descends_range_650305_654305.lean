-- Prove2me | solution 1 for syracuse_descends_range_650305_654305
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T19:04:47.844007+00:00
-- url     : https://prove2.me/submissions/b6c57362-e97f-44de-9c80-5d1f2817ee50

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


theorem B2195477 : Blo 650305 2195477 := bbase (se 6 (by rfl) ⟨51456, by rfl⟩ : syracuseStep 2195477 = 102913) (by norm_num)
theorem B1671293 : Blo 650305 1671293 := bbase (se 3 (by rfl) ⟨313367, by rfl⟩ : syracuseStep 1671293 = 626735) (by norm_num)
theorem B1507621 : Blo 650305 1507621 := bbase (se 4 (by rfl) ⟨141339, by rfl⟩ : syracuseStep 1507621 = 282679) (by norm_num)
theorem B2195909 : Blo 650305 2195909 := bbase (se 4 (by rfl) ⟨205866, by rfl⟩ : syracuseStep 2195909 = 411733) (by norm_num)
theorem B1671653 : Blo 650305 1671653 := bbase (se 4 (by rfl) ⟨156717, by rfl⟩ : syracuseStep 1671653 = 313435) (by norm_num)
theorem B1344365 : Blo 650305 1344365 := bbase (se 3 (by rfl) ⟨252068, by rfl⟩ : syracuseStep 1344365 = 504137) (by norm_num)
theorem B2196341 : Blo 650305 2196341 := bbase (se 5 (by rfl) ⟨102953, by rfl⟩ : syracuseStep 2196341 = 205907) (by norm_num)
theorem B1409909 : Blo 650305 1409909 := bbase (se 5 (by rfl) ⟨66089, by rfl⟩ : syracuseStep 1409909 = 132179) (by norm_num)
theorem B3310469 : Blo 650305 3310469 := bbase (se 4 (by rfl) ⟨310356, by rfl⟩ : syracuseStep 3310469 = 620713) (by norm_num)
theorem B2196773 : Blo 650305 2196773 := bbase (se 4 (by rfl) ⟨205947, by rfl⟩ : syracuseStep 2196773 = 411895) (by norm_num)
theorem B755353 : Blo 650305 755353 := bbase (se 2 (by rfl) ⟨283257, by rfl⟩ : syracuseStep 755353 = 566515) (by norm_num)
theorem B2197205 : Blo 650305 2197205 := bbase (se 7 (by rfl) ⟨25748, by rfl⟩ : syracuseStep 2197205 = 51497) (by norm_num)
theorem B4949909 : Blo 650305 4949909 := bbase (se 6 (by rfl) ⟨116013, by rfl⟩ : syracuseStep 4949909 = 232027) (by norm_num)
theorem B2787317 : Blo 650305 2787317 := bbase (se 5 (by rfl) ⟨130655, by rfl⟩ : syracuseStep 2787317 = 261311) (by norm_num)
theorem B2197637 : Blo 650305 2197637 := bbase (se 4 (by rfl) ⟨206028, by rfl⟩ : syracuseStep 2197637 = 412057) (by norm_num)
theorem B3311765 : Blo 650305 3311765 := bbase (se 6 (by rfl) ⟨77619, by rfl⟩ : syracuseStep 3311765 = 155239) (by norm_num)
theorem B1116317 : Blo 650305 1116317 := bbase (se 3 (by rfl) ⟨209309, by rfl⟩ : syracuseStep 1116317 = 418619) (by norm_num)
theorem B1116413 : Blo 650305 1116413 := bbase (se 3 (by rfl) ⟨209327, by rfl⟩ : syracuseStep 1116413 = 418655) (by norm_num)
theorem B2787605 : Blo 650305 2787605 := bbase (se 6 (by rfl) ⟨65334, by rfl⟩ : syracuseStep 2787605 = 130669) (by norm_num)
theorem B2198069 : Blo 650305 2198069 := bbase (se 5 (by rfl) ⟨103034, by rfl⟩ : syracuseStep 2198069 = 206069) (by norm_num)
theorem B2198501 : Blo 650305 2198501 := bbase (se 4 (by rfl) ⟨206109, by rfl⟩ : syracuseStep 2198501 = 412219) (by norm_num)
theorem B1674229 : Blo 650305 1674229 := bbase (se 5 (by rfl) ⟨78479, by rfl⟩ : syracuseStep 1674229 = 156959) (by norm_num)
theorem B2788357 : Blo 650305 2788357 := bbase (se 4 (by rfl) ⟨261408, by rfl⟩ : syracuseStep 2788357 = 522817) (by norm_num)
theorem B1117261 : Blo 650305 1117261 := bbase (se 3 (by rfl) ⟨209486, by rfl⟩ : syracuseStep 1117261 = 418973) (by norm_num)
theorem B1674557 : Blo 650305 1674557 := bbase (se 3 (by rfl) ⟨313979, by rfl⟩ : syracuseStep 1674557 = 627959) (by norm_num)
theorem B2198933 : Blo 650305 2198933 := bbase (se 6 (by rfl) ⟨51537, by rfl⟩ : syracuseStep 2198933 = 103075) (by norm_num)
theorem B2789093 : Blo 650305 2789093 := bbase (se 4 (by rfl) ⟨261477, by rfl⟩ : syracuseStep 2789093 = 522955) (by norm_num)
theorem B823061 : Blo 650305 823061 := bbase (se 6 (by rfl) ⟨19290, by rfl⟩ : syracuseStep 823061 = 38581) (by norm_num)
theorem B2199365 : Blo 650305 2199365 := bbase (se 4 (by rfl) ⟨206190, by rfl⟩ : syracuseStep 2199365 = 412381) (by norm_num)
theorem B823117 : Blo 650305 823117 := bbase (se 3 (by rfl) ⟨154334, by rfl⟩ : syracuseStep 823117 = 308669) (by norm_num)
theorem B823213 : Blo 650305 823213 := bbase (se 3 (by rfl) ⟨154352, by rfl⟩ : syracuseStep 823213 = 308705) (by norm_num)
theorem B823385 : Blo 650305 823385 := bbase (se 2 (by rfl) ⟨308769, by rfl⟩ : syracuseStep 823385 = 617539) (by norm_num)
theorem B5967989 : Blo 650305 5967989 := bbase (se 5 (by rfl) ⟨279749, by rfl⟩ : syracuseStep 5967989 = 559499) (by norm_num)
theorem B823441 : Blo 650305 823441 := bbase (se 2 (by rfl) ⟨308790, by rfl⟩ : syracuseStep 823441 = 617581) (by norm_num)
theorem B823537 : Blo 650305 823537 := bbase (se 2 (by rfl) ⟨308826, by rfl⟩ : syracuseStep 823537 = 617653) (by norm_num)
theorem B2199797 : Blo 650305 2199797 := bbase (se 5 (by rfl) ⟨103115, by rfl⟩ : syracuseStep 2199797 = 206231) (by norm_num)
theorem B823709 : Blo 650305 823709 := bbase (se 3 (by rfl) ⟨154445, by rfl⟩ : syracuseStep 823709 = 308891) (by norm_num)
theorem B823765 : Blo 650305 823765 := bbase (se 7 (by rfl) ⟨9653, by rfl⟩ : syracuseStep 823765 = 19307) (by norm_num)
theorem B823861 : Blo 650305 823861 := bbase (se 5 (by rfl) ⟨38618, by rfl⟩ : syracuseStep 823861 = 77237) (by norm_num)
theorem B12554837 : Blo 650305 12554837 := bbase (se 8 (by rfl) ⟨73563, by rfl⟩ : syracuseStep 12554837 = 147127) (by norm_num)
theorem B2200229 : Blo 650305 2200229 := bbase (se 4 (by rfl) ⟨206271, by rfl⟩ : syracuseStep 2200229 = 412543) (by norm_num)
theorem B824033 : Blo 650305 824033 := bbase (se 2 (by rfl) ⟨309012, by rfl⟩ : syracuseStep 824033 = 618025) (by norm_num)
theorem B824089 : Blo 650305 824089 := bbase (se 2 (by rfl) ⟨309033, by rfl⟩ : syracuseStep 824089 = 618067) (by norm_num)
theorem B824185 : Blo 650305 824185 := bbase (se 2 (by rfl) ⟨309069, by rfl⟩ : syracuseStep 824185 = 618139) (by norm_num)
theorem B824357 : Blo 650305 824357 := bbase (se 4 (by rfl) ⟨77283, by rfl⟩ : syracuseStep 824357 = 154567) (by norm_num)
theorem B2200661 : Blo 650305 2200661 := bbase (se 8 (by rfl) ⟨12894, by rfl⟩ : syracuseStep 2200661 = 25789) (by norm_num)
theorem B824413 : Blo 650305 824413 := bbase (se 3 (by rfl) ⟨154577, by rfl⟩ : syracuseStep 824413 = 309155) (by norm_num)
theorem B824509 : Blo 650305 824509 := bbase (se 3 (by rfl) ⟨154595, by rfl⟩ : syracuseStep 824509 = 309191) (by norm_num)
theorem B824681 : Blo 650305 824681 := bbase (se 2 (by rfl) ⟨309255, by rfl⟩ : syracuseStep 824681 = 618511) (by norm_num)
theorem B824737 : Blo 650305 824737 := bbase (se 2 (by rfl) ⟨309276, by rfl⟩ : syracuseStep 824737 = 618553) (by norm_num)
theorem B824833 : Blo 650305 824833 := bbase (se 2 (by rfl) ⟨309312, by rfl⟩ : syracuseStep 824833 = 618625) (by norm_num)
theorem B2201093 : Blo 650305 2201093 := bbase (se 4 (by rfl) ⟨206352, by rfl⟩ : syracuseStep 2201093 = 412705) (by norm_num)
theorem B1676837 : Blo 650305 1676837 := bbase (se 4 (by rfl) ⟨157203, by rfl⟩ : syracuseStep 1676837 = 314407) (by norm_num)
theorem B825005 : Blo 650305 825005 := bbase (se 3 (by rfl) ⟨154688, by rfl⟩ : syracuseStep 825005 = 309377) (by norm_num)
theorem B825061 : Blo 650305 825061 := bbase (se 4 (by rfl) ⟨77349, by rfl⟩ : syracuseStep 825061 = 154699) (by norm_num)
theorem B825157 : Blo 650305 825157 := bbase (se 4 (by rfl) ⟨77358, by rfl⟩ : syracuseStep 825157 = 154717) (by norm_num)
theorem B2201525 : Blo 650305 2201525 := bbase (se 5 (by rfl) ⟨103196, by rfl⟩ : syracuseStep 2201525 = 206393) (by norm_num)
theorem B825329 : Blo 650305 825329 := bbase (se 2 (by rfl) ⟨309498, by rfl⟩ : syracuseStep 825329 = 618997) (by norm_num)
theorem B825385 : Blo 650305 825385 := bbase (se 2 (by rfl) ⟨309519, by rfl⟩ : syracuseStep 825385 = 619039) (by norm_num)
theorem B825481 : Blo 650305 825481 := bbase (se 2 (by rfl) ⟨309555, by rfl⟩ : syracuseStep 825481 = 619111) (by norm_num)
theorem B2005301 : Blo 650305 2005301 := bbase (se 5 (by rfl) ⟨93998, by rfl⟩ : syracuseStep 2005301 = 187997) (by norm_num)
theorem B825653 : Blo 650305 825653 := bbase (se 5 (by rfl) ⟨38702, by rfl⟩ : syracuseStep 825653 = 77405) (by norm_num)
theorem B2201957 : Blo 650305 2201957 := bbase (se 4 (by rfl) ⟨206433, by rfl⟩ : syracuseStep 2201957 = 412867) (by norm_num)
theorem B825709 : Blo 650305 825709 := bbase (se 3 (by rfl) ⟨154820, by rfl⟩ : syracuseStep 825709 = 309641) (by norm_num)
theorem B825805 : Blo 650305 825805 := bbase (se 3 (by rfl) ⟨154838, by rfl⟩ : syracuseStep 825805 = 309677) (by norm_num)
theorem B4692437 : Blo 650305 4692437 := bbase (se 7 (by rfl) ⟨54989, by rfl⟩ : syracuseStep 4692437 = 109979) (by norm_num)
theorem B694813 : Blo 650305 694813 := bbase (se 3 (by rfl) ⟨130277, by rfl⟩ : syracuseStep 694813 = 260555) (by norm_num)
theorem B825977 : Blo 650305 825977 := bbase (se 2 (by rfl) ⟨309741, by rfl⟩ : syracuseStep 825977 = 619483) (by norm_num)
theorem B662137 : Blo 650305 662137 := bbase (se 2 (by rfl) ⟨248301, by rfl⟩ : syracuseStep 662137 = 496603) (by norm_num)
theorem B826033 : Blo 650305 826033 := bbase (se 2 (by rfl) ⟨309762, by rfl⟩ : syracuseStep 826033 = 619525) (by norm_num)
theorem B826129 : Blo 650305 826129 := bbase (se 2 (by rfl) ⟨309798, by rfl⟩ : syracuseStep 826129 = 619597) (by norm_num)
theorem B2202389 : Blo 650305 2202389 := bbase (se 6 (by rfl) ⟨51618, by rfl⟩ : syracuseStep 2202389 = 103237) (by norm_num)
theorem B695189 : Blo 650305 695189 := bbase (se 6 (by rfl) ⟨16293, by rfl⟩ : syracuseStep 695189 = 32587) (by norm_num)
theorem B662437 : Blo 650305 662437 := bbase (se 4 (by rfl) ⟨62103, by rfl⟩ : syracuseStep 662437 = 124207) (by norm_num)
theorem B826301 : Blo 650305 826301 := bbase (se 3 (by rfl) ⟨154931, by rfl⟩ : syracuseStep 826301 = 309863) (by norm_num)
theorem B2792389 : Blo 650305 2792389 := bbase (se 4 (by rfl) ⟨261786, by rfl⟩ : syracuseStep 2792389 = 523573) (by norm_num)
theorem B695261 : Blo 650305 695261 := bbase (se 3 (by rfl) ⟨130361, by rfl⟩ : syracuseStep 695261 = 260723) (by norm_num)
theorem B826357 : Blo 650305 826357 := bbase (se 5 (by rfl) ⟨38735, by rfl⟩ : syracuseStep 826357 = 77471) (by norm_num)
theorem B826453 : Blo 650305 826453 := bbase (se 8 (by rfl) ⟨4842, by rfl⟩ : syracuseStep 826453 = 9685) (by norm_num)
theorem B695449 : Blo 650305 695449 := bbase (se 2 (by rfl) ⟨260793, by rfl⟩ : syracuseStep 695449 = 521587) (by norm_num)
theorem B2202821 : Blo 650305 2202821 := bbase (se 4 (by rfl) ⟨206514, by rfl⟩ : syracuseStep 2202821 = 413029) (by norm_num)
theorem B826625 : Blo 650305 826625 := bbase (se 2 (by rfl) ⟨309984, by rfl⟩ : syracuseStep 826625 = 619969) (by norm_num)
theorem B826681 : Blo 650305 826681 := bbase (se 2 (by rfl) ⟨310005, by rfl⟩ : syracuseStep 826681 = 620011) (by norm_num)
theorem B695633 : Blo 650305 695633 := bbase (se 2 (by rfl) ⟨260862, by rfl⟩ : syracuseStep 695633 = 521725) (by norm_num)
theorem B4234613 : Blo 650305 4234613 := bbase (se 5 (by rfl) ⟨198497, by rfl⟩ : syracuseStep 4234613 = 396995) (by norm_num)
theorem B826777 : Blo 650305 826777 := bbase (se 2 (by rfl) ⟨310041, by rfl⟩ : syracuseStep 826777 = 620083) (by norm_num)
theorem B826949 : Blo 650305 826949 := bbase (se 4 (by rfl) ⟨77526, by rfl⟩ : syracuseStep 826949 = 155053) (by norm_num)
theorem B2203253 : Blo 650305 2203253 := bbase (se 5 (by rfl) ⟨103277, by rfl⟩ : syracuseStep 2203253 = 206555) (by norm_num)
theorem B827005 : Blo 650305 827005 := bbase (se 3 (by rfl) ⟨155063, by rfl⟩ : syracuseStep 827005 = 310127) (by norm_num)
theorem B1318565 : Blo 650305 1318565 := bbase (se 4 (by rfl) ⟨123615, by rfl⟩ : syracuseStep 1318565 = 247231) (by norm_num)
theorem B5086901 : Blo 650305 5086901 := bbase (se 5 (by rfl) ⟨238448, by rfl⟩ : syracuseStep 5086901 = 476897) (by norm_num)
theorem B794321 : Blo 650305 794321 := bbase (se 2 (by rfl) ⟨297870, by rfl⟩ : syracuseStep 794321 = 595741) (by norm_num)
theorem B827101 : Blo 650305 827101 := bbase (se 3 (by rfl) ⟨155081, by rfl⟩ : syracuseStep 827101 = 310163) (by norm_num)
theorem B1646365 : Blo 650305 1646365 := bbase (se 3 (by rfl) ⟨308693, by rfl⟩ : syracuseStep 1646365 = 617387) (by norm_num)
theorem B827273 : Blo 650305 827273 := bbase (se 2 (by rfl) ⟨310227, by rfl⟩ : syracuseStep 827273 = 620455) (by norm_num)
theorem B1646477 : Blo 650305 1646477 := bbase (se 3 (by rfl) ⟨308714, by rfl⟩ : syracuseStep 1646477 = 617429) (by norm_num)
theorem B827329 : Blo 650305 827329 := bbase (se 2 (by rfl) ⟨310248, by rfl⟩ : syracuseStep 827329 = 620497) (by norm_num)
theorem B827425 : Blo 650305 827425 := bbase (se 2 (by rfl) ⟨310284, by rfl⟩ : syracuseStep 827425 = 620569) (by norm_num)
theorem B2203685 : Blo 650305 2203685 := bbase (se 4 (by rfl) ⟨206595, by rfl⟩ : syracuseStep 2203685 = 413191) (by norm_num)
theorem B1450037 : Blo 650305 1450037 := bbase (se 5 (by rfl) ⟨67970, by rfl⟩ : syracuseStep 1450037 = 135941) (by norm_num)
theorem B696385 : Blo 650305 696385 := bbase (se 2 (by rfl) ⟨261144, by rfl⟩ : syracuseStep 696385 = 522289) (by norm_num)
theorem B1646669 : Blo 650305 1646669 := bbase (se 3 (by rfl) ⟨308750, by rfl⟩ : syracuseStep 1646669 = 617501) (by norm_num)
theorem B696457 : Blo 650305 696457 := bbase (se 2 (by rfl) ⟨261171, by rfl⟩ : syracuseStep 696457 = 522343) (by norm_num)
theorem B5578901 : Blo 650305 5578901 := bbase (se 6 (by rfl) ⟨130755, by rfl⟩ : syracuseStep 5578901 = 261511) (by norm_num)
theorem B827597 : Blo 650305 827597 := bbase (se 3 (by rfl) ⟨155174, by rfl⟩ : syracuseStep 827597 = 310349) (by norm_num)
theorem B925933 : Blo 650305 925933 := bbase (se 3 (by rfl) ⟨173612, by rfl⟩ : syracuseStep 925933 = 347225) (by norm_num)
theorem B827653 : Blo 650305 827653 := bbase (se 4 (by rfl) ⟨77592, by rfl⟩ : syracuseStep 827653 = 155185) (by norm_num)
theorem B696637 : Blo 650305 696637 := bbase (se 3 (by rfl) ⟨130619, by rfl⟩ : syracuseStep 696637 = 261239) (by norm_num)
theorem B1319261 : Blo 650305 1319261 := bbase (se 3 (by rfl) ⟨247361, by rfl⟩ : syracuseStep 1319261 = 494723) (by norm_num)
theorem B827749 : Blo 650305 827749 := bbase (se 4 (by rfl) ⟨77601, by rfl⟩ : syracuseStep 827749 = 155203) (by norm_num)
theorem B1647013 : Blo 650305 1647013 := bbase (se 4 (by rfl) ⟨154407, by rfl⟩ : syracuseStep 1647013 = 308815) (by norm_num)
theorem B926149 : Blo 650305 926149 := bbase (se 4 (by rfl) ⟨86826, by rfl⟩ : syracuseStep 926149 = 173653) (by norm_num)
theorem B991685 : Blo 650305 991685 := bbase (se 4 (by rfl) ⟨92970, by rfl⟩ : syracuseStep 991685 = 185941) (by norm_num)
theorem B2204117 : Blo 650305 2204117 := bbase (se 7 (by rfl) ⟨25829, by rfl⟩ : syracuseStep 2204117 = 51659) (by norm_num)
theorem B827921 : Blo 650305 827921 := bbase (se 2 (by rfl) ⟨310470, by rfl⟩ : syracuseStep 827921 = 620941) (by norm_num)
theorem B1647125 : Blo 650305 1647125 := bbase (se 6 (by rfl) ⟨38604, by rfl⟩ : syracuseStep 1647125 = 77209) (by norm_num)
theorem B827977 : Blo 650305 827977 := bbase (se 2 (by rfl) ⟨310491, by rfl⟩ : syracuseStep 827977 = 620983) (by norm_num)
theorem B828073 : Blo 650305 828073 := bbase (se 2 (by rfl) ⟨310527, by rfl⟩ : syracuseStep 828073 = 621055) (by norm_num)
theorem B1647317 : Blo 650305 1647317 := bbase (se 7 (by rfl) ⟨19304, by rfl⟩ : syracuseStep 1647317 = 38609) (by norm_num)
theorem B697081 : Blo 650305 697081 := bbase (se 2 (by rfl) ⟨261405, by rfl⟩ : syracuseStep 697081 = 522811) (by norm_num)
theorem B926525 : Blo 650305 926525 := bbase (se 3 (by rfl) ⟨173723, by rfl⟩ : syracuseStep 926525 = 347447) (by norm_num)
theorem B697205 : Blo 650305 697205 := bbase (se 5 (by rfl) ⟨32681, by rfl⟩ : syracuseStep 697205 = 65363) (by norm_num)
theorem B2204549 : Blo 650305 2204549 := bbase (se 4 (by rfl) ⟨206676, by rfl⟩ : syracuseStep 2204549 = 413353) (by norm_num)
theorem B992245 : Blo 650305 992245 := bbase (se 5 (by rfl) ⟨46511, by rfl⟩ : syracuseStep 992245 = 93023) (by norm_num)
theorem B1647661 : Blo 650305 1647661 := bbase (se 3 (by rfl) ⟨308936, by rfl⟩ : syracuseStep 1647661 = 617873) (by norm_num)
theorem B1254485 : Blo 650305 1254485 := bbase (se 8 (by rfl) ⟨7350, by rfl⟩ : syracuseStep 1254485 = 14701) (by norm_num)
theorem B697457 : Blo 650305 697457 := bbase (se 2 (by rfl) ⟨261546, by rfl⟩ : syracuseStep 697457 = 523093) (by norm_num)
theorem B1647773 : Blo 650305 1647773 := bbase (se 3 (by rfl) ⟨308957, by rfl⟩ : syracuseStep 1647773 = 617915) (by norm_num)
theorem B2204981 : Blo 650305 2204981 := bbase (se 5 (by rfl) ⟨103358, by rfl⟩ : syracuseStep 2204981 = 206717) (by norm_num)
theorem B1647965 : Blo 650305 1647965 := bbase (se 3 (by rfl) ⟨308993, by rfl⟩ : syracuseStep 1647965 = 617987) (by norm_num)
theorem B796009 : Blo 650305 796009 := bbase (se 2 (by rfl) ⟨298503, by rfl⟩ : syracuseStep 796009 = 597007) (by norm_num)
theorem B2860469 : Blo 650305 2860469 := bbase (se 5 (by rfl) ⟨134084, by rfl⟩ : syracuseStep 2860469 = 268169) (by norm_num)
theorem B4957685 : Blo 650305 4957685 := bbase (se 5 (by rfl) ⟨232391, by rfl⟩ : syracuseStep 4957685 = 464783) (by norm_num)
theorem B697901 : Blo 650305 697901 := bbase (se 3 (by rfl) ⟨130856, by rfl⟩ : syracuseStep 697901 = 261713) (by norm_num)
theorem B3712661 : Blo 650305 3712661 := bbase (se 6 (by rfl) ⟨87015, by rfl⟩ : syracuseStep 3712661 = 174031) (by norm_num)
theorem B1648309 : Blo 650305 1648309 := bbase (se 5 (by rfl) ⟨77264, by rfl⟩ : syracuseStep 1648309 = 154529) (by norm_num)
theorem B2205413 : Blo 650305 2205413 := bbase (se 4 (by rfl) ⟨206757, by rfl⟩ : syracuseStep 2205413 = 413515) (by norm_num)
theorem B1648421 : Blo 650305 1648421 := bbase (se 4 (by rfl) ⟨154539, by rfl⟩ : syracuseStep 1648421 = 309079) (by norm_num)
theorem B698149 : Blo 650305 698149 := bbase (se 4 (by rfl) ⟨65451, by rfl⟩ : syracuseStep 698149 = 130903) (by norm_num)
theorem B1648613 : Blo 650305 1648613 := bbase (se 4 (by rfl) ⟨154557, by rfl⟩ : syracuseStep 1648613 = 309115) (by norm_num)
theorem B2205845 : Blo 650305 2205845 := bbase (se 6 (by rfl) ⟨51699, by rfl⟩ : syracuseStep 2205845 = 103399) (by norm_num)
theorem B927949 : Blo 650305 927949 := bbase (se 3 (by rfl) ⟨173990, by rfl⟩ : syracuseStep 927949 = 347981) (by norm_num)
theorem B698593 : Blo 650305 698593 := bbase (se 2 (by rfl) ⟨261972, by rfl⟩ : syracuseStep 698593 = 523945) (by norm_num)
theorem B698653 : Blo 650305 698653 := bbase (se 3 (by rfl) ⟨130997, by rfl⟩ : syracuseStep 698653 = 261995) (by norm_num)
theorem B1648957 : Blo 650305 1648957 := bbase (se 3 (by rfl) ⟨309179, by rfl⟩ : syracuseStep 1648957 = 618359) (by norm_num)
theorem B1649069 : Blo 650305 1649069 := bbase (se 3 (by rfl) ⟨309200, by rfl⟩ : syracuseStep 1649069 = 618401) (by norm_num)
theorem B731605 : Blo 650305 731605 := bbase (se 7 (by rfl) ⟨8573, by rfl⟩ : syracuseStep 731605 = 17147) (by norm_num)
theorem B731641 : Blo 650305 731641 := bbase (se 2 (by rfl) ⟨274365, by rfl⟩ : syracuseStep 731641 = 548731) (by norm_num)
theorem B731677 : Blo 650305 731677 := bbase (se 3 (by rfl) ⟨137189, by rfl⟩ : syracuseStep 731677 = 274379) (by norm_num)
theorem B1321525 : Blo 650305 1321525 := bbase (se 5 (by rfl) ⟨61946, by rfl⟩ : syracuseStep 1321525 = 123893) (by norm_num)
theorem B731713 : Blo 650305 731713 := bbase (se 2 (by rfl) ⟨274392, by rfl⟩ : syracuseStep 731713 = 548785) (by norm_num)
theorem B2206277 : Blo 650305 2206277 := bbase (se 4 (by rfl) ⟨206838, by rfl⟩ : syracuseStep 2206277 = 413677) (by norm_num)
theorem B731749 : Blo 650305 731749 := bbase (se 4 (by rfl) ⟨68601, by rfl⟩ : syracuseStep 731749 = 137203) (by norm_num)
theorem B1649261 : Blo 650305 1649261 := bbase (se 3 (by rfl) ⟨309236, by rfl⟩ : syracuseStep 1649261 = 618473) (by norm_num)
theorem B731785 : Blo 650305 731785 := bbase (se 2 (by rfl) ⟨274419, by rfl⟩ : syracuseStep 731785 = 548839) (by norm_num)
theorem B1059485 : Blo 650305 1059485 := bbase (se 3 (by rfl) ⟨198653, by rfl⟩ : syracuseStep 1059485 = 397307) (by norm_num)
theorem B731821 : Blo 650305 731821 := bbase (se 3 (by rfl) ⟨137216, by rfl⟩ : syracuseStep 731821 = 274433) (by norm_num)
theorem B731857 : Blo 650305 731857 := bbase (se 2 (by rfl) ⟨274446, by rfl⟩ : syracuseStep 731857 = 548893) (by norm_num)
theorem B731893 : Blo 650305 731893 := bbase (se 5 (by rfl) ⟨34307, by rfl⟩ : syracuseStep 731893 = 68615) (by norm_num)
theorem B994069 : Blo 650305 994069 := bbase (se 6 (by rfl) ⟨23298, by rfl⟩ : syracuseStep 994069 = 46597) (by norm_num)
theorem B731929 : Blo 650305 731929 := bbase (se 2 (by rfl) ⟨274473, by rfl⟩ : syracuseStep 731929 = 548947) (by norm_num)
theorem B928541 : Blo 650305 928541 := bbase (se 3 (by rfl) ⟨174101, by rfl⟩ : syracuseStep 928541 = 348203) (by norm_num)
theorem B731965 : Blo 650305 731965 := bbase (se 3 (by rfl) ⟨137243, by rfl⟩ : syracuseStep 731965 = 274487) (by norm_num)
theorem B732001 : Blo 650305 732001 := bbase (se 2 (by rfl) ⟨274500, by rfl⟩ : syracuseStep 732001 = 549001) (by norm_num)
theorem B928621 : Blo 650305 928621 := bbase (se 3 (by rfl) ⟨174116, by rfl⟩ : syracuseStep 928621 = 348233) (by norm_num)
theorem B732037 : Blo 650305 732037 := bbase (se 4 (by rfl) ⟨68628, by rfl⟩ : syracuseStep 732037 = 137257) (by norm_num)
theorem B732073 : Blo 650305 732073 := bbase (se 2 (by rfl) ⟨274527, by rfl⟩ : syracuseStep 732073 = 549055) (by norm_num)
theorem B1649605 : Blo 650305 1649605 := bbase (se 4 (by rfl) ⟨154650, by rfl⟩ : syracuseStep 1649605 = 309301) (by norm_num)
theorem B732109 : Blo 650305 732109 := bbase (se 3 (by rfl) ⟨137270, by rfl⟩ : syracuseStep 732109 = 274541) (by norm_num)
theorem B928741 : Blo 650305 928741 := bbase (se 4 (by rfl) ⟨87069, by rfl⟩ : syracuseStep 928741 = 174139) (by norm_num)
theorem B994277 : Blo 650305 994277 := bbase (se 4 (by rfl) ⟨93213, by rfl⟩ : syracuseStep 994277 = 186427) (by norm_num)
theorem B732145 : Blo 650305 732145 := bbase (se 2 (by rfl) ⟨274554, by rfl⟩ : syracuseStep 732145 = 549109) (by norm_num)
theorem B2206709 : Blo 650305 2206709 := bbase (se 5 (by rfl) ⟨103439, by rfl⟩ : syracuseStep 2206709 = 206879) (by norm_num)
theorem B732181 : Blo 650305 732181 := bbase (se 6 (by rfl) ⟨17160, by rfl⟩ : syracuseStep 732181 = 34321) (by norm_num)
theorem B1649717 : Blo 650305 1649717 := bbase (se 5 (by rfl) ⟨77330, by rfl⟩ : syracuseStep 1649717 = 154661) (by norm_num)
theorem B732217 : Blo 650305 732217 := bbase (se 2 (by rfl) ⟨274581, by rfl⟩ : syracuseStep 732217 = 549163) (by norm_num)
theorem B928837 : Blo 650305 928837 := bbase (se 4 (by rfl) ⟨87078, by rfl⟩ : syracuseStep 928837 = 174157) (by norm_num)
theorem B732253 : Blo 650305 732253 := bbase (se 3 (by rfl) ⟨137297, by rfl⟩ : syracuseStep 732253 = 274595) (by norm_num)
theorem B732289 : Blo 650305 732289 := bbase (se 2 (by rfl) ⟨274608, by rfl⟩ : syracuseStep 732289 = 549217) (by norm_num)
theorem B732325 : Blo 650305 732325 := bbase (se 4 (by rfl) ⟨68655, by rfl⟩ : syracuseStep 732325 = 137311) (by norm_num)
theorem B732361 : Blo 650305 732361 := bbase (se 2 (by rfl) ⟨274635, by rfl⟩ : syracuseStep 732361 = 549271) (by norm_num)
theorem B732397 : Blo 650305 732397 := bbase (se 3 (by rfl) ⟨137324, by rfl⟩ : syracuseStep 732397 = 274649) (by norm_num)
theorem B1649909 : Blo 650305 1649909 := bbase (se 5 (by rfl) ⟨77339, by rfl⟩ : syracuseStep 1649909 = 154679) (by norm_num)
theorem B732433 : Blo 650305 732433 := bbase (se 2 (by rfl) ⟨274662, by rfl⟩ : syracuseStep 732433 = 549325) (by norm_num)
theorem B10595605 : Blo 650305 10595605 := bbase (se 6 (by rfl) ⟨248334, by rfl⟩ : syracuseStep 10595605 = 496669) (by norm_num)
theorem B732469 : Blo 650305 732469 := bbase (se 5 (by rfl) ⟨34334, by rfl⟩ : syracuseStep 732469 = 68669) (by norm_num)
theorem B732505 : Blo 650305 732505 := bbase (se 2 (by rfl) ⟨274689, by rfl⟩ : syracuseStep 732505 = 549379) (by norm_num)
theorem B732541 : Blo 650305 732541 := bbase (se 3 (by rfl) ⟨137351, by rfl⟩ : syracuseStep 732541 = 274703) (by norm_num)
theorem B1584533 : Blo 650305 1584533 := bbase (se 6 (by rfl) ⟨37137, by rfl⟩ : syracuseStep 1584533 = 74275) (by norm_num)
theorem B732577 : Blo 650305 732577 := bbase (se 2 (by rfl) ⟨274716, by rfl⟩ : syracuseStep 732577 = 549433) (by norm_num)
theorem B2207141 : Blo 650305 2207141 := bbase (se 4 (by rfl) ⟨206919, by rfl⟩ : syracuseStep 2207141 = 413839) (by norm_num)
theorem B732613 : Blo 650305 732613 := bbase (se 4 (by rfl) ⟨68682, by rfl⟩ : syracuseStep 732613 = 137365) (by norm_num)
theorem B732649 : Blo 650305 732649 := bbase (se 2 (by rfl) ⟨274743, by rfl⟩ : syracuseStep 732649 = 549487) (by norm_num)
theorem B732685 : Blo 650305 732685 := bbase (se 3 (by rfl) ⟨137378, by rfl⟩ : syracuseStep 732685 = 274757) (by norm_num)
theorem B732721 : Blo 650305 732721 := bbase (se 2 (by rfl) ⟨274770, by rfl⟩ : syracuseStep 732721 = 549541) (by norm_num)
theorem B929333 : Blo 650305 929333 := bbase (se 5 (by rfl) ⟨43562, by rfl⟩ : syracuseStep 929333 = 87125) (by norm_num)
theorem B1650253 : Blo 650305 1650253 := bbase (se 3 (by rfl) ⟨309422, by rfl⟩ : syracuseStep 1650253 = 618845) (by norm_num)
theorem B732757 : Blo 650305 732757 := bbase (se 8 (by rfl) ⟨4293, by rfl⟩ : syracuseStep 732757 = 8587) (by norm_num)
theorem B732793 : Blo 650305 732793 := bbase (se 2 (by rfl) ⟨274797, by rfl⟩ : syracuseStep 732793 = 549595) (by norm_num)
theorem B732829 : Blo 650305 732829 := bbase (se 3 (by rfl) ⟨137405, by rfl⟩ : syracuseStep 732829 = 274811) (by norm_num)
theorem B1650365 : Blo 650305 1650365 := bbase (se 3 (by rfl) ⟨309443, by rfl⟩ : syracuseStep 1650365 = 618887) (by norm_num)
theorem B732865 : Blo 650305 732865 := bbase (se 2 (by rfl) ⟨274824, by rfl⟩ : syracuseStep 732865 = 549649) (by norm_num)
theorem B732901 : Blo 650305 732901 := bbase (se 4 (by rfl) ⟨68709, by rfl⟩ : syracuseStep 732901 = 137419) (by norm_num)
theorem B732937 : Blo 650305 732937 := bbase (se 2 (by rfl) ⟨274851, by rfl⟩ : syracuseStep 732937 = 549703) (by norm_num)
theorem B732973 : Blo 650305 732973 := bbase (se 3 (by rfl) ⟨137432, by rfl⟩ : syracuseStep 732973 = 274865) (by norm_num)
theorem B2862917 : Blo 650305 2862917 := bbase (se 4 (by rfl) ⟨268398, by rfl⟩ : syracuseStep 2862917 = 536797) (by norm_num)
theorem B733009 : Blo 650305 733009 := bbase (se 2 (by rfl) ⟨274878, by rfl⟩ : syracuseStep 733009 = 549757) (by norm_num)
theorem B2207573 : Blo 650305 2207573 := bbase (se 9 (by rfl) ⟨6467, by rfl⟩ : syracuseStep 2207573 = 12935) (by norm_num)
theorem B733045 : Blo 650305 733045 := bbase (se 5 (by rfl) ⟨34361, by rfl⟩ : syracuseStep 733045 = 68723) (by norm_num)
theorem B1650557 : Blo 650305 1650557 := bbase (se 3 (by rfl) ⟨309479, by rfl⟩ : syracuseStep 1650557 = 618959) (by norm_num)
theorem B733081 : Blo 650305 733081 := bbase (se 2 (by rfl) ⟨274905, by rfl⟩ : syracuseStep 733081 = 549811) (by norm_num)
theorem B1257373 : Blo 650305 1257373 := bbase (se 3 (by rfl) ⟨235757, by rfl⟩ : syracuseStep 1257373 = 471515) (by norm_num)
theorem B3583925 : Blo 650305 3583925 := bbase (se 5 (by rfl) ⟨167996, by rfl⟩ : syracuseStep 3583925 = 335993) (by norm_num)
theorem B733117 : Blo 650305 733117 := bbase (se 3 (by rfl) ⟨137459, by rfl⟩ : syracuseStep 733117 = 274919) (by norm_num)
theorem B733153 : Blo 650305 733153 := bbase (se 2 (by rfl) ⟨274932, by rfl⟩ : syracuseStep 733153 = 549865) (by norm_num)
theorem B733189 : Blo 650305 733189 := bbase (se 4 (by rfl) ⟨68736, by rfl⟩ : syracuseStep 733189 = 137473) (by norm_num)
theorem B733225 : Blo 650305 733225 := bbase (se 2 (by rfl) ⟨274959, by rfl⟩ : syracuseStep 733225 = 549919) (by norm_num)
theorem B733261 : Blo 650305 733261 := bbase (se 3 (by rfl) ⟨137486, by rfl⟩ : syracuseStep 733261 = 274973) (by norm_num)
theorem B2469973 : Blo 650305 2469973 := bbase (se 8 (by rfl) ⟨14472, by rfl⟩ : syracuseStep 2469973 = 28945) (by norm_num)
theorem B929885 : Blo 650305 929885 := bbase (se 3 (by rfl) ⟨174353, by rfl⟩ : syracuseStep 929885 = 348707) (by norm_num)
theorem B733297 : Blo 650305 733297 := bbase (se 2 (by rfl) ⟨274986, by rfl⟩ : syracuseStep 733297 = 549973) (by norm_num)
theorem B733333 : Blo 650305 733333 := bbase (se 6 (by rfl) ⟨17187, by rfl⟩ : syracuseStep 733333 = 34375) (by norm_num)
theorem B3125429 : Blo 650305 3125429 := bbase (se 5 (by rfl) ⟨146504, by rfl⟩ : syracuseStep 3125429 = 293009) (by norm_num)
theorem B733369 : Blo 650305 733369 := bbase (se 2 (by rfl) ⟨275013, by rfl⟩ : syracuseStep 733369 = 550027) (by norm_num)
theorem B1159373 : Blo 650305 1159373 := bbase (se 3 (by rfl) ⟨217382, by rfl⟩ : syracuseStep 1159373 = 434765) (by norm_num)
theorem B1650901 : Blo 650305 1650901 := bbase (se 7 (by rfl) ⟨19346, by rfl⟩ : syracuseStep 1650901 = 38693) (by norm_num)
theorem B733405 : Blo 650305 733405 := bbase (se 3 (by rfl) ⟨137513, by rfl⟩ : syracuseStep 733405 = 275027) (by norm_num)
theorem B733441 : Blo 650305 733441 := bbase (se 2 (by rfl) ⟨275040, by rfl⟩ : syracuseStep 733441 = 550081) (by norm_num)
theorem B2208005 : Blo 650305 2208005 := bbase (se 4 (by rfl) ⟨207000, by rfl⟩ : syracuseStep 2208005 = 414001) (by norm_num)
theorem B1880341 : Blo 650305 1880341 := bbase (se 6 (by rfl) ⟨44070, by rfl⟩ : syracuseStep 1880341 = 88141) (by norm_num)
theorem B733477 : Blo 650305 733477 := bbase (se 4 (by rfl) ⟨68763, by rfl⟩ : syracuseStep 733477 = 137527) (by norm_num)
theorem B1585469 : Blo 650305 1585469 := bbase (se 3 (by rfl) ⟨297275, by rfl⟩ : syracuseStep 1585469 = 594551) (by norm_num)
theorem B1651013 : Blo 650305 1651013 := bbase (se 4 (by rfl) ⟨154782, by rfl⟩ : syracuseStep 1651013 = 309565) (by norm_num)
theorem B733513 : Blo 650305 733513 := bbase (se 2 (by rfl) ⟨275067, by rfl⟩ : syracuseStep 733513 = 550135) (by norm_num)
theorem B733549 : Blo 650305 733549 := bbase (se 3 (by rfl) ⟨137540, by rfl⟩ : syracuseStep 733549 = 275081) (by norm_num)
theorem B1192301 : Blo 650305 1192301 := bbase (se 3 (by rfl) ⟨223556, by rfl⟩ : syracuseStep 1192301 = 447113) (by norm_num)
theorem B2470277 : Blo 650305 2470277 := bbase (se 4 (by rfl) ⟨231588, by rfl⟩ : syracuseStep 2470277 = 463177) (by norm_num)
theorem B733585 : Blo 650305 733585 := bbase (se 2 (by rfl) ⟨275094, by rfl⟩ : syracuseStep 733585 = 550189) (by norm_num)
theorem B733621 : Blo 650305 733621 := bbase (se 5 (by rfl) ⟨34388, by rfl⟩ : syracuseStep 733621 = 68777) (by norm_num)
theorem B733657 : Blo 650305 733657 := bbase (se 2 (by rfl) ⟨275121, by rfl⟩ : syracuseStep 733657 = 550243) (by norm_num)
theorem B733693 : Blo 650305 733693 := bbase (se 3 (by rfl) ⟨137567, by rfl⟩ : syracuseStep 733693 = 275135) (by norm_num)
theorem B1651205 : Blo 650305 1651205 := bbase (se 4 (by rfl) ⟨154800, by rfl⟩ : syracuseStep 1651205 = 309601) (by norm_num)
theorem B733729 : Blo 650305 733729 := bbase (se 2 (by rfl) ⟨275148, by rfl⟩ : syracuseStep 733729 = 550297) (by norm_num)
theorem B733765 : Blo 650305 733765 := bbase (se 4 (by rfl) ⟨68790, by rfl⟩ : syracuseStep 733765 = 137581) (by norm_num)
theorem B13414997 : Blo 650305 13414997 := bbase (se 8 (by rfl) ⟨78603, by rfl⟩ : syracuseStep 13414997 = 157207) (by norm_num)
theorem B733801 : Blo 650305 733801 := bbase (se 2 (by rfl) ⟨275175, by rfl⟩ : syracuseStep 733801 = 550351) (by norm_num)
theorem B1585781 : Blo 650305 1585781 := bbase (se 5 (by rfl) ⟨74333, by rfl⟩ : syracuseStep 1585781 = 148667) (by norm_num)
theorem B733837 : Blo 650305 733837 := bbase (se 3 (by rfl) ⟨137594, by rfl⟩ : syracuseStep 733837 = 275189) (by norm_num)
theorem B733873 : Blo 650305 733873 := bbase (se 2 (by rfl) ⟨275202, by rfl⟩ : syracuseStep 733873 = 550405) (by norm_num)
theorem B733909 : Blo 650305 733909 := bbase (se 7 (by rfl) ⟨8600, by rfl⟩ : syracuseStep 733909 = 17201) (by norm_num)
theorem B733945 : Blo 650305 733945 := bbase (se 2 (by rfl) ⟨275229, by rfl⟩ : syracuseStep 733945 = 550459) (by norm_num)
theorem B733981 : Blo 650305 733981 := bbase (se 3 (by rfl) ⟨137621, by rfl⟩ : syracuseStep 733981 = 275243) (by norm_num)
theorem B734017 : Blo 650305 734017 := bbase (se 2 (by rfl) ⟨275256, by rfl⟩ : syracuseStep 734017 = 550513) (by norm_num)
theorem B930637 : Blo 650305 930637 := bbase (se 3 (by rfl) ⟨174494, by rfl⟩ : syracuseStep 930637 = 348989) (by norm_num)
theorem B1651549 : Blo 650305 1651549 := bbase (se 3 (by rfl) ⟨309665, by rfl⟩ : syracuseStep 1651549 = 619331) (by norm_num)
theorem B734053 : Blo 650305 734053 := bbase (se 4 (by rfl) ⟨68817, by rfl⟩ : syracuseStep 734053 = 137635) (by norm_num)
theorem B734089 : Blo 650305 734089 := bbase (se 2 (by rfl) ⟨275283, by rfl⟩ : syracuseStep 734089 = 550567) (by norm_num)
theorem B734125 : Blo 650305 734125 := bbase (se 3 (by rfl) ⟨137648, by rfl⟩ : syracuseStep 734125 = 275297) (by norm_num)
theorem B1651661 : Blo 650305 1651661 := bbase (se 3 (by rfl) ⟨309686, by rfl⟩ : syracuseStep 1651661 = 619373) (by norm_num)
theorem B734161 : Blo 650305 734161 := bbase (se 2 (by rfl) ⟨275310, by rfl⟩ : syracuseStep 734161 = 550621) (by norm_num)
theorem B3978197 : Blo 650305 3978197 := bbase (se 7 (by rfl) ⟨46619, by rfl⟩ : syracuseStep 3978197 = 93239) (by norm_num)
theorem B734197 : Blo 650305 734197 := bbase (se 5 (by rfl) ⟨34415, by rfl⟩ : syracuseStep 734197 = 68831) (by norm_num)
theorem B1389565 : Blo 650305 1389565 := bbase (se 3 (by rfl) ⟨260543, by rfl⟩ : syracuseStep 1389565 = 521087) (by norm_num)
theorem B734233 : Blo 650305 734233 := bbase (se 2 (by rfl) ⟨275337, by rfl⟩ : syracuseStep 734233 = 550675) (by norm_num)
theorem B4174901 : Blo 650305 4174901 := bbase (se 5 (by rfl) ⟨195698, by rfl⟩ : syracuseStep 4174901 = 391397) (by norm_num)
theorem B734269 : Blo 650305 734269 := bbase (se 3 (by rfl) ⟨137675, by rfl⟩ : syracuseStep 734269 = 275351) (by norm_num)
theorem B1487965 : Blo 650305 1487965 := bbase (se 3 (by rfl) ⟨278993, by rfl⟩ : syracuseStep 1487965 = 557987) (by norm_num)
theorem B734305 : Blo 650305 734305 := bbase (se 2 (by rfl) ⟨275364, by rfl⟩ : syracuseStep 734305 = 550729) (by norm_num)
theorem B734341 : Blo 650305 734341 := bbase (se 4 (by rfl) ⟨68844, by rfl⟩ : syracuseStep 734341 = 137689) (by norm_num)
theorem B1651853 : Blo 650305 1651853 := bbase (se 3 (by rfl) ⟨309722, by rfl⟩ : syracuseStep 1651853 = 619445) (by norm_num)
theorem B734377 : Blo 650305 734377 := bbase (se 2 (by rfl) ⟨275391, by rfl⟩ : syracuseStep 734377 = 550783) (by norm_num)
theorem B1881269 : Blo 650305 1881269 := bbase (se 5 (by rfl) ⟨88184, by rfl⟩ : syracuseStep 1881269 = 176369) (by norm_num)
theorem B734413 : Blo 650305 734413 := bbase (se 3 (by rfl) ⟨137702, by rfl⟩ : syracuseStep 734413 = 275405) (by norm_num)
theorem B734449 : Blo 650305 734449 := bbase (se 2 (by rfl) ⟨275418, by rfl⟩ : syracuseStep 734449 = 550837) (by norm_num)
theorem B734485 : Blo 650305 734485 := bbase (se 6 (by rfl) ⟨17214, by rfl⟩ : syracuseStep 734485 = 34429) (by norm_num)
theorem B734521 : Blo 650305 734521 := bbase (se 2 (by rfl) ⟨275445, by rfl⟩ : syracuseStep 734521 = 550891) (by norm_num)
theorem B734557 : Blo 650305 734557 := bbase (se 3 (by rfl) ⟨137729, by rfl⟩ : syracuseStep 734557 = 275459) (by norm_num)
theorem B734593 : Blo 650305 734593 := bbase (se 2 (by rfl) ⟨275472, by rfl⟩ : syracuseStep 734593 = 550945) (by norm_num)
theorem B734629 : Blo 650305 734629 := bbase (se 4 (by rfl) ⟨68871, by rfl⟩ : syracuseStep 734629 = 137743) (by norm_num)
theorem B734665 : Blo 650305 734665 := bbase (se 2 (by rfl) ⟨275499, by rfl⟩ : syracuseStep 734665 = 550999) (by norm_num)
theorem B1652197 : Blo 650305 1652197 := bbase (se 4 (by rfl) ⟨154893, by rfl⟩ : syracuseStep 1652197 = 309787) (by norm_num)
theorem B1390061 : Blo 650305 1390061 := bbase (se 3 (by rfl) ⟨260636, by rfl⟩ : syracuseStep 1390061 = 521273) (by norm_num)
theorem B734701 : Blo 650305 734701 := bbase (se 3 (by rfl) ⟨137756, by rfl⟩ : syracuseStep 734701 = 275513) (by norm_num)
theorem B734737 : Blo 650305 734737 := bbase (se 2 (by rfl) ⟨275526, by rfl⟩ : syracuseStep 734737 = 551053) (by norm_num)
theorem B734773 : Blo 650305 734773 := bbase (se 5 (by rfl) ⟨34442, by rfl⟩ : syracuseStep 734773 = 68885) (by norm_num)
theorem B1652309 : Blo 650305 1652309 := bbase (se 8 (by rfl) ⟨9681, by rfl⟩ : syracuseStep 1652309 = 19363) (by norm_num)
theorem B734809 : Blo 650305 734809 := bbase (se 2 (by rfl) ⟨275553, by rfl⟩ : syracuseStep 734809 = 551107) (by norm_num)
theorem B931429 : Blo 650305 931429 := bbase (se 4 (by rfl) ⟨87321, by rfl⟩ : syracuseStep 931429 = 174643) (by norm_num)
theorem B734845 : Blo 650305 734845 := bbase (se 3 (by rfl) ⟨137783, by rfl⟩ : syracuseStep 734845 = 275567) (by norm_num)
theorem B734881 : Blo 650305 734881 := bbase (se 2 (by rfl) ⟨275580, by rfl⟩ : syracuseStep 734881 = 551161) (by norm_num)
theorem B734917 : Blo 650305 734917 := bbase (se 4 (by rfl) ⟨68898, by rfl⟩ : syracuseStep 734917 = 137797) (by norm_num)
theorem B1586893 : Blo 650305 1586893 := bbase (se 3 (by rfl) ⟨297542, by rfl⟩ : syracuseStep 1586893 = 595085) (by norm_num)
theorem B734953 : Blo 650305 734953 := bbase (se 2 (by rfl) ⟨275607, by rfl⟩ : syracuseStep 734953 = 551215) (by norm_num)
theorem B734989 : Blo 650305 734989 := bbase (se 3 (by rfl) ⟨137810, by rfl⟩ : syracuseStep 734989 = 275621) (by norm_num)
theorem B3127061 : Blo 650305 3127061 := bbase (se 6 (by rfl) ⟨73290, by rfl⟩ : syracuseStep 3127061 = 146581) (by norm_num)
theorem B1652501 : Blo 650305 1652501 := bbase (se 6 (by rfl) ⟨38730, by rfl⟩ : syracuseStep 1652501 = 77461) (by norm_num)
theorem B735025 : Blo 650305 735025 := bbase (se 2 (by rfl) ⟨275634, by rfl⟩ : syracuseStep 735025 = 551269) (by norm_num)
theorem B735061 : Blo 650305 735061 := bbase (se 9 (by rfl) ⟨2153, by rfl⟩ : syracuseStep 735061 = 4307) (by norm_num)
theorem B735097 : Blo 650305 735097 := bbase (se 2 (by rfl) ⟨275661, by rfl⟩ : syracuseStep 735097 = 551323) (by norm_num)
theorem B735133 : Blo 650305 735133 := bbase (se 3 (by rfl) ⟨137837, by rfl⟩ : syracuseStep 735133 = 275675) (by norm_num)
theorem B735169 : Blo 650305 735169 := bbase (se 2 (by rfl) ⟨275688, by rfl⟩ : syracuseStep 735169 = 551377) (by norm_num)
theorem B735205 : Blo 650305 735205 := bbase (se 4 (by rfl) ⟨68925, by rfl⟩ : syracuseStep 735205 = 137851) (by norm_num)
theorem B735241 : Blo 650305 735241 := bbase (se 2 (by rfl) ⟨275715, by rfl⟩ : syracuseStep 735241 = 551431) (by norm_num)
theorem B735277 : Blo 650305 735277 := bbase (se 3 (by rfl) ⟨137864, by rfl⟩ : syracuseStep 735277 = 275729) (by norm_num)
theorem B1325117 : Blo 650305 1325117 := bbase (se 3 (by rfl) ⟨248459, by rfl⟩ : syracuseStep 1325117 = 496919) (by norm_num)
theorem B735313 : Blo 650305 735313 := bbase (se 2 (by rfl) ⟨275742, by rfl⟩ : syracuseStep 735313 = 551485) (by norm_num)
theorem B1652845 : Blo 650305 1652845 := bbase (se 3 (by rfl) ⟨309908, by rfl⟩ : syracuseStep 1652845 = 619817) (by norm_num)
theorem B735349 : Blo 650305 735349 := bbase (se 5 (by rfl) ⟨34469, by rfl⟩ : syracuseStep 735349 = 68939) (by norm_num)
theorem B735385 : Blo 650305 735385 := bbase (se 2 (by rfl) ⟨275769, by rfl⟩ : syracuseStep 735385 = 551539) (by norm_num)
theorem B735421 : Blo 650305 735421 := bbase (se 3 (by rfl) ⟨137891, by rfl⟩ : syracuseStep 735421 = 275783) (by norm_num)
theorem B1652957 : Blo 650305 1652957 := bbase (se 3 (by rfl) ⟨309929, by rfl⟩ : syracuseStep 1652957 = 619859) (by norm_num)
theorem B735457 : Blo 650305 735457 := bbase (se 2 (by rfl) ⟨275796, by rfl⟩ : syracuseStep 735457 = 551593) (by norm_num)
theorem B735493 : Blo 650305 735493 := bbase (se 4 (by rfl) ⟨68952, by rfl⟩ : syracuseStep 735493 = 137905) (by norm_num)
theorem B735529 : Blo 650305 735529 := bbase (se 2 (by rfl) ⟨275823, by rfl⟩ : syracuseStep 735529 = 551647) (by norm_num)
theorem B1390925 : Blo 650305 1390925 := bbase (se 3 (by rfl) ⟨260798, by rfl⟩ : syracuseStep 1390925 = 521597) (by norm_num)
theorem B735565 : Blo 650305 735565 := bbase (se 3 (by rfl) ⟨137918, by rfl⟩ : syracuseStep 735565 = 275837) (by norm_num)
theorem B735601 : Blo 650305 735601 := bbase (se 2 (by rfl) ⟨275850, by rfl⟩ : syracuseStep 735601 = 551701) (by norm_num)
theorem B735637 : Blo 650305 735637 := bbase (se 6 (by rfl) ⟨17241, by rfl⟩ : syracuseStep 735637 = 34483) (by norm_num)
theorem B1653149 : Blo 650305 1653149 := bbase (se 3 (by rfl) ⟨309965, by rfl⟩ : syracuseStep 1653149 = 619931) (by norm_num)
theorem B735673 : Blo 650305 735673 := bbase (se 2 (by rfl) ⟨275877, by rfl⟩ : syracuseStep 735673 = 551755) (by norm_num)
theorem B2472389 : Blo 650305 2472389 := bbase (se 4 (by rfl) ⟨231786, by rfl⟩ : syracuseStep 2472389 = 463573) (by norm_num)
theorem B1391069 : Blo 650305 1391069 := bbase (se 3 (by rfl) ⟨260825, by rfl⟩ : syracuseStep 1391069 = 521651) (by norm_num)
theorem B735709 : Blo 650305 735709 := bbase (se 3 (by rfl) ⟨137945, by rfl⟩ : syracuseStep 735709 = 275891) (by norm_num)
theorem B670177 : Blo 650305 670177 := bbase (se 2 (by rfl) ⟨251316, by rfl⟩ : syracuseStep 670177 = 502633) (by norm_num)
theorem B735745 : Blo 650305 735745 := bbase (se 2 (by rfl) ⟨275904, by rfl⟩ : syracuseStep 735745 = 551809) (by norm_num)
theorem B735781 : Blo 650305 735781 := bbase (se 4 (by rfl) ⟨68979, by rfl⟩ : syracuseStep 735781 = 137959) (by norm_num)
theorem B735817 : Blo 650305 735817 := bbase (se 2 (by rfl) ⟨275931, by rfl⟩ : syracuseStep 735817 = 551863) (by norm_num)
theorem B735853 : Blo 650305 735853 := bbase (se 3 (by rfl) ⟨137972, by rfl⟩ : syracuseStep 735853 = 275945) (by norm_num)
theorem B735889 : Blo 650305 735889 := bbase (se 2 (by rfl) ⟨275958, by rfl⟩ : syracuseStep 735889 = 551917) (by norm_num)
theorem B1325749 : Blo 650305 1325749 := bbase (se 5 (by rfl) ⟨62144, by rfl⟩ : syracuseStep 1325749 = 124289) (by norm_num)
theorem B735925 : Blo 650305 735925 := bbase (se 5 (by rfl) ⟨34496, by rfl⟩ : syracuseStep 735925 = 68993) (by norm_num)
theorem B735961 : Blo 650305 735961 := bbase (se 2 (by rfl) ⟨275985, by rfl⟩ : syracuseStep 735961 = 551971) (by norm_num)
theorem B2472677 : Blo 650305 2472677 := bbase (se 4 (by rfl) ⟨231813, by rfl⟩ : syracuseStep 2472677 = 463627) (by norm_num)
theorem B670441 : Blo 650305 670441 := bbase (se 2 (by rfl) ⟨251415, by rfl⟩ : syracuseStep 670441 = 502831) (by norm_num)
theorem B1653493 : Blo 650305 1653493 := bbase (se 5 (by rfl) ⟨77507, by rfl⟩ : syracuseStep 1653493 = 155015) (by norm_num)
theorem B735997 : Blo 650305 735997 := bbase (se 3 (by rfl) ⟨137999, by rfl⟩ : syracuseStep 735997 = 275999) (by norm_num)
theorem B736033 : Blo 650305 736033 := bbase (se 2 (by rfl) ⟨276012, by rfl⟩ : syracuseStep 736033 = 552025) (by norm_num)
theorem B736069 : Blo 650305 736069 := bbase (se 4 (by rfl) ⟨69006, by rfl⟩ : syracuseStep 736069 = 138013) (by norm_num)
theorem B1653605 : Blo 650305 1653605 := bbase (se 4 (by rfl) ⟨155025, by rfl⟩ : syracuseStep 1653605 = 310051) (by norm_num)
theorem B1653797 : Blo 650305 1653797 := bbase (se 4 (by rfl) ⟨155043, by rfl⟩ : syracuseStep 1653797 = 310087) (by norm_num)
theorem B2636869 : Blo 650305 2636869 := bbase (se 4 (by rfl) ⟨247206, by rfl⟩ : syracuseStep 2636869 = 494413) (by norm_num)
theorem B3292325 : Blo 650305 3292325 := bbase (se 4 (by rfl) ⟨308655, by rfl⟩ : syracuseStep 3292325 = 617311) (by norm_num)
theorem B2636965 : Blo 650305 2636965 := bbase (se 4 (by rfl) ⟨247215, by rfl⟩ : syracuseStep 2636965 = 494431) (by norm_num)
theorem B1391813 : Blo 650305 1391813 := bbase (se 4 (by rfl) ⟨130482, by rfl⟩ : syracuseStep 1391813 = 260965) (by norm_num)
theorem B670933 : Blo 650305 670933 := bbase (se 7 (by rfl) ⟨7862, by rfl⟩ : syracuseStep 670933 = 15725) (by norm_num)
theorem B6274421 : Blo 650305 6274421 := bbase (se 5 (by rfl) ⟨294113, by rfl⟩ : syracuseStep 6274421 = 588227) (by norm_num)
theorem B1654141 : Blo 650305 1654141 := bbase (se 3 (by rfl) ⟨310151, by rfl⟩ : syracuseStep 1654141 = 620303) (by norm_num)
theorem B835009 : Blo 650305 835009 := bbase (se 2 (by rfl) ⟨313128, by rfl⟩ : syracuseStep 835009 = 626257) (by norm_num)
theorem B1654253 : Blo 650305 1654253 := bbase (se 3 (by rfl) ⟨310172, by rfl⟩ : syracuseStep 1654253 = 620345) (by norm_num)
theorem B1654445 : Blo 650305 1654445 := bbase (se 3 (by rfl) ⟨310208, by rfl⟩ : syracuseStep 1654445 = 620417) (by norm_num)
theorem B1097509 : Blo 650305 1097509 := bbase (se 4 (by rfl) ⟨102891, by rfl⟩ : syracuseStep 1097509 = 205783) (by norm_num)
theorem B1097597 : Blo 650305 1097597 := bbase (se 3 (by rfl) ⟨205799, by rfl⟩ : syracuseStep 1097597 = 411599) (by norm_num)
theorem B2473861 : Blo 650305 2473861 := bbase (se 4 (by rfl) ⟨231924, by rfl⟩ : syracuseStep 2473861 = 463849) (by norm_num)
theorem B671657 : Blo 650305 671657 := bbase (se 2 (by rfl) ⟨251871, by rfl⟩ : syracuseStep 671657 = 503743) (by norm_num)
theorem B1392565 : Blo 650305 1392565 := bbase (se 5 (by rfl) ⟨65276, by rfl⟩ : syracuseStep 1392565 = 130553) (by norm_num)
theorem B1097725 : Blo 650305 1097725 := bbase (se 3 (by rfl) ⟨205823, by rfl⟩ : syracuseStep 1097725 = 411647) (by norm_num)
theorem B1654789 : Blo 650305 1654789 := bbase (se 4 (by rfl) ⟨155136, by rfl⟩ : syracuseStep 1654789 = 310273) (by norm_num)
theorem B5586965 : Blo 650305 5586965 := bbase (se 6 (by rfl) ⟨130944, by rfl⟩ : syracuseStep 5586965 = 261889) (by norm_num)
theorem B5947445 : Blo 650305 5947445 := bbase (se 5 (by rfl) ⟨278786, by rfl⟩ : syracuseStep 5947445 = 557573) (by norm_num)
theorem B1392709 : Blo 650305 1392709 := bbase (se 4 (by rfl) ⟨130566, by rfl⟩ : syracuseStep 1392709 = 261133) (by norm_num)
theorem B1097813 : Blo 650305 1097813 := bbase (se 8 (by rfl) ⟨6432, by rfl⟩ : syracuseStep 1097813 = 12865) (by norm_num)
theorem B1491029 : Blo 650305 1491029 := bbase (se 8 (by rfl) ⟨8736, by rfl⟩ : syracuseStep 1491029 = 17473) (by norm_num)
theorem B1654901 : Blo 650305 1654901 := bbase (se 5 (by rfl) ⟨77573, by rfl⟩ : syracuseStep 1654901 = 155147) (by norm_num)
theorem B2474165 : Blo 650305 2474165 := bbase (se 5 (by rfl) ⟨115976, by rfl⟩ : syracuseStep 2474165 = 231953) (by norm_num)
theorem B4538549 : Blo 650305 4538549 := bbase (se 5 (by rfl) ⟨212744, by rfl⟩ : syracuseStep 4538549 = 425489) (by norm_num)
theorem B1097941 : Blo 650305 1097941 := bbase (se 7 (by rfl) ⟨12866, by rfl⟩ : syracuseStep 1097941 = 25733) (by norm_num)
theorem B2113829 : Blo 650305 2113829 := bbase (se 4 (by rfl) ⟨198171, by rfl⟩ : syracuseStep 2113829 = 396343) (by norm_num)
theorem B1098029 : Blo 650305 1098029 := bbase (se 3 (by rfl) ⟨205880, by rfl⟩ : syracuseStep 1098029 = 411761) (by norm_num)
theorem B1655093 : Blo 650305 1655093 := bbase (se 5 (by rfl) ⟨77582, by rfl⟩ : syracuseStep 1655093 = 155165) (by norm_num)
theorem B1098157 : Blo 650305 1098157 := bbase (se 3 (by rfl) ⟨205904, by rfl⟩ : syracuseStep 1098157 = 411809) (by norm_num)
theorem B3293621 : Blo 650305 3293621 := bbase (se 5 (by rfl) ⟨154388, by rfl⟩ : syracuseStep 3293621 = 308777) (by norm_num)
theorem B1393085 : Blo 650305 1393085 := bbase (se 3 (by rfl) ⟨261203, by rfl⟩ : syracuseStep 1393085 = 522407) (by norm_num)
theorem B3228149 : Blo 650305 3228149 := bbase (se 5 (by rfl) ⟨151319, by rfl⟩ : syracuseStep 3228149 = 302639) (by norm_num)
theorem B1098245 : Blo 650305 1098245 := bbase (se 4 (by rfl) ⟨102960, by rfl⟩ : syracuseStep 1098245 = 205921) (by norm_num)
theorem B836201 : Blo 650305 836201 := bbase (se 2 (by rfl) ⟨313575, by rfl⟩ : syracuseStep 836201 = 627151) (by norm_num)
theorem B1098373 : Blo 650305 1098373 := bbase (se 4 (by rfl) ⟨102972, by rfl⟩ : syracuseStep 1098373 = 205945) (by norm_num)
theorem B1655437 : Blo 650305 1655437 := bbase (se 3 (by rfl) ⟨310394, by rfl⟩ : syracuseStep 1655437 = 620789) (by norm_num)
theorem B7422677 : Blo 650305 7422677 := bbase (se 7 (by rfl) ⟨86984, by rfl⟩ : syracuseStep 7422677 = 173969) (by norm_num)
theorem B1098461 : Blo 650305 1098461 := bbase (se 3 (by rfl) ⟨205961, by rfl⟩ : syracuseStep 1098461 = 411923) (by norm_num)
theorem B1884917 : Blo 650305 1884917 := bbase (se 5 (by rfl) ⟨88355, by rfl⟩ : syracuseStep 1884917 = 176711) (by norm_num)
theorem B1655549 : Blo 650305 1655549 := bbase (se 3 (by rfl) ⟨310415, by rfl⟩ : syracuseStep 1655549 = 620831) (by norm_num)
theorem B1393453 : Blo 650305 1393453 := bbase (se 3 (by rfl) ⟨261272, by rfl⟩ : syracuseStep 1393453 = 522545) (by norm_num)
theorem B1098589 : Blo 650305 1098589 := bbase (se 3 (by rfl) ⟨205985, by rfl⟩ : syracuseStep 1098589 = 411971) (by norm_num)
theorem B1098677 : Blo 650305 1098677 := bbase (se 5 (by rfl) ⟨51500, by rfl⟩ : syracuseStep 1098677 = 103001) (by norm_num)
theorem B1655741 : Blo 650305 1655741 := bbase (se 3 (by rfl) ⟨310451, by rfl⟩ : syracuseStep 1655741 = 620903) (by norm_num)
theorem B1098805 : Blo 650305 1098805 := bbase (se 5 (by rfl) ⟨51506, by rfl⟩ : syracuseStep 1098805 = 103013) (by norm_num)
theorem B4965461 : Blo 650305 4965461 := bbase (se 8 (by rfl) ⟨29094, by rfl⟩ : syracuseStep 4965461 = 58189) (by norm_num)
theorem B1098893 : Blo 650305 1098893 := bbase (se 3 (by rfl) ⟨206042, by rfl⟩ : syracuseStep 1098893 = 412085) (by norm_num)
theorem B836857 : Blo 650305 836857 := bbase (se 2 (by rfl) ⟨313821, by rfl⟩ : syracuseStep 836857 = 627643) (by norm_num)
theorem B1099021 : Blo 650305 1099021 := bbase (se 3 (by rfl) ⟨206066, by rfl⟩ : syracuseStep 1099021 = 412133) (by norm_num)
theorem B1656085 : Blo 650305 1656085 := bbase (se 6 (by rfl) ⟨38814, by rfl⟩ : syracuseStep 1656085 = 77629) (by norm_num)
theorem B1099109 : Blo 650305 1099109 := bbase (se 4 (by rfl) ⟨103041, by rfl⟩ : syracuseStep 1099109 = 206083) (by norm_num)
theorem B1983845 : Blo 650305 1983845 := bbase (se 4 (by rfl) ⟨185985, by rfl⟩ : syracuseStep 1983845 = 371971) (by norm_num)
theorem B705925 : Blo 650305 705925 := bbase (se 4 (by rfl) ⟨66180, by rfl⟩ : syracuseStep 705925 = 132361) (by norm_num)
theorem B1656197 : Blo 650305 1656197 := bbase (se 4 (by rfl) ⟨155268, by rfl⟩ : syracuseStep 1656197 = 310537) (by norm_num)
theorem B1099237 : Blo 650305 1099237 := bbase (se 4 (by rfl) ⟨103053, by rfl⟩ : syracuseStep 1099237 = 206107) (by norm_num)
theorem B3720725 : Blo 650305 3720725 := bbase (se 6 (by rfl) ⟨87204, by rfl⟩ : syracuseStep 3720725 = 174409) (by norm_num)
theorem B1099325 : Blo 650305 1099325 := bbase (se 3 (by rfl) ⟨206123, by rfl⟩ : syracuseStep 1099325 = 412247) (by norm_num)
theorem B1099453 : Blo 650305 1099453 := bbase (se 3 (by rfl) ⟨206147, by rfl⟩ : syracuseStep 1099453 = 412295) (by norm_num)
theorem B3294917 : Blo 650305 3294917 := bbase (se 4 (by rfl) ⟨308898, by rfl⟩ : syracuseStep 3294917 = 617797) (by norm_num)
theorem B1099541 : Blo 650305 1099541 := bbase (se 6 (by rfl) ⟨25770, by rfl⟩ : syracuseStep 1099541 = 51541) (by norm_num)
theorem B1132309 : Blo 650305 1132309 := bbase (se 6 (by rfl) ⟨26538, by rfl⟩ : syracuseStep 1132309 = 53077) (by norm_num)
theorem B837473 : Blo 650305 837473 := bbase (se 2 (by rfl) ⟨314052, by rfl⟩ : syracuseStep 837473 = 628105) (by norm_num)
theorem B1099669 : Blo 650305 1099669 := bbase (se 6 (by rfl) ⟨25773, by rfl⟩ : syracuseStep 1099669 = 51547) (by norm_num)
theorem B1853381 : Blo 650305 1853381 := bbase (se 4 (by rfl) ⟨173754, by rfl⟩ : syracuseStep 1853381 = 347509) (by norm_num)
theorem B1099757 : Blo 650305 1099757 := bbase (se 3 (by rfl) ⟨206204, by rfl⟩ : syracuseStep 1099757 = 412409) (by norm_num)
theorem B2377765 : Blo 650305 2377765 := bbase (se 4 (by rfl) ⟨222915, by rfl⟩ : syracuseStep 2377765 = 445831) (by norm_num)
theorem B1099885 : Blo 650305 1099885 := bbase (se 3 (by rfl) ⟨206228, by rfl⟩ : syracuseStep 1099885 = 412457) (by norm_num)
theorem B1099973 : Blo 650305 1099973 := bbase (se 4 (by rfl) ⟨103122, by rfl⟩ : syracuseStep 1099973 = 206245) (by norm_num)
theorem B2476277 : Blo 650305 2476277 := bbase (se 5 (by rfl) ⟨116075, by rfl⟩ : syracuseStep 2476277 = 232151) (by norm_num)
theorem B1394957 : Blo 650305 1394957 := bbase (se 3 (by rfl) ⟨261554, by rfl⟩ : syracuseStep 1394957 = 523109) (by norm_num)
theorem B2509093 : Blo 650305 2509093 := bbase (se 4 (by rfl) ⟨235227, by rfl⟩ : syracuseStep 2509093 = 470455) (by norm_num)
theorem B1100101 : Blo 650305 1100101 := bbase (se 4 (by rfl) ⟨103134, by rfl⟩ : syracuseStep 1100101 = 206269) (by norm_num)
theorem B1100189 : Blo 650305 1100189 := bbase (se 3 (by rfl) ⟨206285, by rfl⟩ : syracuseStep 1100189 = 412571) (by norm_num)
theorem B1395101 : Blo 650305 1395101 := bbase (se 3 (by rfl) ⟨261581, by rfl⟩ : syracuseStep 1395101 = 523163) (by norm_num)
theorem B2476565 : Blo 650305 2476565 := bbase (se 6 (by rfl) ⟨58044, by rfl⟩ : syracuseStep 2476565 = 116089) (by norm_num)
theorem B1100317 : Blo 650305 1100317 := bbase (se 3 (by rfl) ⟨206309, by rfl⟩ : syracuseStep 1100317 = 412619) (by norm_num)
theorem B1854053 : Blo 650305 1854053 := bbase (se 4 (by rfl) ⟨173817, by rfl⟩ : syracuseStep 1854053 = 347635) (by norm_num)
theorem B1100405 : Blo 650305 1100405 := bbase (se 5 (by rfl) ⟨51581, by rfl⟩ : syracuseStep 1100405 = 103163) (by norm_num)
theorem B2083477 : Blo 650305 2083477 := bbase (se 6 (by rfl) ⟨48831, by rfl⟩ : syracuseStep 2083477 = 97663) (by norm_num)
theorem B3721909 : Blo 650305 3721909 := bbase (se 5 (by rfl) ⟨174464, by rfl⟩ : syracuseStep 3721909 = 348929) (by norm_num)
theorem B1100533 : Blo 650305 1100533 := bbase (se 5 (by rfl) ⟨51587, by rfl⟩ : syracuseStep 1100533 = 103175) (by norm_num)
theorem B1395461 : Blo 650305 1395461 := bbase (se 4 (by rfl) ⟨130824, by rfl⟩ : syracuseStep 1395461 = 261649) (by norm_num)
theorem B772933 : Blo 650305 772933 := bbase (se 4 (by rfl) ⟨72462, by rfl⟩ : syracuseStep 772933 = 144925) (by norm_num)
theorem B1100621 : Blo 650305 1100621 := bbase (se 3 (by rfl) ⟨206366, by rfl⟩ : syracuseStep 1100621 = 412733) (by norm_num)
theorem B4246357 : Blo 650305 4246357 := bbase (se 9 (by rfl) ⟨12440, by rfl⟩ : syracuseStep 4246357 = 24881) (by norm_num)
theorem B2083733 : Blo 650305 2083733 := bbase (se 6 (by rfl) ⟨48837, by rfl⟩ : syracuseStep 2083733 = 97675) (by norm_num)
theorem B1100749 : Blo 650305 1100749 := bbase (se 3 (by rfl) ⟨206390, by rfl⟩ : syracuseStep 1100749 = 412781) (by norm_num)
theorem B3296213 : Blo 650305 3296213 := bbase (se 7 (by rfl) ⟨38627, by rfl⟩ : syracuseStep 3296213 = 77255) (by norm_num)
theorem B1985509 : Blo 650305 1985509 := bbase (se 4 (by rfl) ⟨186141, by rfl⟩ : syracuseStep 1985509 = 372283) (by norm_num)
theorem B1854485 : Blo 650305 1854485 := bbase (se 6 (by rfl) ⟨43464, by rfl⟩ : syracuseStep 1854485 = 86929) (by norm_num)
theorem B1100837 : Blo 650305 1100837 := bbase (se 4 (by rfl) ⟨103203, by rfl⟩ : syracuseStep 1100837 = 206407) (by norm_num)
theorem B1100965 : Blo 650305 1100965 := bbase (se 4 (by rfl) ⟨103215, by rfl⟩ : syracuseStep 1100965 = 206431) (by norm_num)
theorem B1101053 : Blo 650305 1101053 := bbase (se 3 (by rfl) ⟨206447, by rfl⟩ : syracuseStep 1101053 = 412895) (by norm_num)
theorem B2870549 : Blo 650305 2870549 := bbase (se 6 (by rfl) ⟨67278, by rfl⟩ : syracuseStep 2870549 = 134557) (by norm_num)
theorem B1101181 : Blo 650305 1101181 := bbase (se 3 (by rfl) ⟨206471, by rfl⟩ : syracuseStep 1101181 = 412943) (by norm_num)
theorem B1101269 : Blo 650305 1101269 := bbase (se 7 (by rfl) ⟨12905, by rfl⟩ : syracuseStep 1101269 = 25811) (by norm_num)
theorem B1101397 : Blo 650305 1101397 := bbase (se 8 (by rfl) ⟨6453, by rfl⟩ : syracuseStep 1101397 = 12907) (by norm_num)
theorem B1396349 : Blo 650305 1396349 := bbase (se 3 (by rfl) ⟨261815, by rfl⟩ : syracuseStep 1396349 = 523631) (by norm_num)
theorem B2117285 : Blo 650305 2117285 := bbase (se 4 (by rfl) ⟨198495, by rfl⟩ : syracuseStep 2117285 = 396991) (by norm_num)
theorem B1101485 : Blo 650305 1101485 := bbase (se 3 (by rfl) ⟨206528, by rfl⟩ : syracuseStep 1101485 = 413057) (by norm_num)
theorem B2477749 : Blo 650305 2477749 := bbase (se 5 (by rfl) ⟨116144, by rfl⟩ : syracuseStep 2477749 = 232289) (by norm_num)
theorem B1855237 : Blo 650305 1855237 := bbase (se 4 (by rfl) ⟨173928, by rfl⟩ : syracuseStep 1855237 = 347857) (by norm_num)
theorem B1101613 : Blo 650305 1101613 := bbase (se 3 (by rfl) ⟨206552, by rfl⟩ : syracuseStep 1101613 = 413105) (by norm_num)
theorem B2346853 : Blo 650305 2346853 := bbase (se 4 (by rfl) ⟨220017, by rfl⟩ : syracuseStep 2346853 = 440035) (by norm_num)
theorem B1396597 : Blo 650305 1396597 := bbase (se 5 (by rfl) ⟨65465, by rfl⟩ : syracuseStep 1396597 = 130931) (by norm_num)
theorem B1101701 : Blo 650305 1101701 := bbase (se 4 (by rfl) ⟨103284, by rfl⟩ : syracuseStep 1101701 = 206569) (by norm_num)
theorem B2478053 : Blo 650305 2478053 := bbase (se 4 (by rfl) ⟨232317, by rfl⟩ : syracuseStep 2478053 = 464635) (by norm_num)
theorem B1101829 : Blo 650305 1101829 := bbase (se 4 (by rfl) ⟨103296, by rfl⟩ : syracuseStep 1101829 = 206593) (by norm_num)
theorem B1101917 : Blo 650305 1101917 := bbase (se 3 (by rfl) ⟨206609, by rfl⟩ : syracuseStep 1101917 = 413219) (by norm_num)
theorem B3133637 : Blo 650305 3133637 := bbase (se 4 (by rfl) ⟨293778, by rfl⟩ : syracuseStep 3133637 = 587557) (by norm_num)
theorem B1102045 : Blo 650305 1102045 := bbase (se 3 (by rfl) ⟨206633, by rfl⟩ : syracuseStep 1102045 = 413267) (by norm_num)
theorem B3297509 : Blo 650305 3297509 := bbase (se 4 (by rfl) ⟨309141, by rfl⟩ : syracuseStep 3297509 = 618283) (by norm_num)
theorem B2347301 : Blo 650305 2347301 := bbase (se 4 (by rfl) ⟨220059, by rfl⟩ : syracuseStep 2347301 = 440119) (by norm_num)
theorem B1102133 : Blo 650305 1102133 := bbase (se 5 (by rfl) ⟨51662, by rfl⟩ : syracuseStep 1102133 = 103325) (by norm_num)
theorem B1397101 : Blo 650305 1397101 := bbase (se 3 (by rfl) ⟨261956, by rfl⟩ : syracuseStep 1397101 = 523913) (by norm_num)
theorem B741793 : Blo 650305 741793 := bbase (se 2 (by rfl) ⟨278172, by rfl⟩ : syracuseStep 741793 = 556345) (by norm_num)
theorem B1102261 : Blo 650305 1102261 := bbase (se 5 (by rfl) ⟨51668, by rfl⟩ : syracuseStep 1102261 = 103337) (by norm_num)
theorem B1102349 : Blo 650305 1102349 := bbase (se 3 (by rfl) ⟨206690, by rfl⟩ : syracuseStep 1102349 = 413381) (by norm_num)
theorem B3723893 : Blo 650305 3723893 := bbase (se 5 (by rfl) ⟨174557, by rfl⟩ : syracuseStep 3723893 = 349115) (by norm_num)
theorem B1102477 : Blo 650305 1102477 := bbase (se 3 (by rfl) ⟨206714, by rfl⟩ : syracuseStep 1102477 = 413429) (by norm_num)
theorem B5952149 : Blo 650305 5952149 := bbase (se 6 (by rfl) ⟨139503, by rfl⟩ : syracuseStep 5952149 = 279007) (by norm_num)
theorem B938693 : Blo 650305 938693 := bbase (se 4 (by rfl) ⟨88002, by rfl⟩ : syracuseStep 938693 = 176005) (by norm_num)
theorem B1102565 : Blo 650305 1102565 := bbase (se 4 (by rfl) ⟨103365, by rfl⟩ : syracuseStep 1102565 = 206731) (by norm_num)
theorem B1102693 : Blo 650305 1102693 := bbase (se 4 (by rfl) ⟨103377, by rfl⟩ : syracuseStep 1102693 = 206755) (by norm_num)
theorem B1102781 : Blo 650305 1102781 := bbase (se 3 (by rfl) ⟨206771, by rfl⟩ : syracuseStep 1102781 = 413543) (by norm_num)
theorem B1463237 : Blo 650305 1463237 := bbase (se 4 (by rfl) ⟨137178, by rfl⟩ : syracuseStep 1463237 = 274357) (by norm_num)
theorem B1004525 : Blo 650305 1004525 := bbase (se 3 (by rfl) ⟨188348, by rfl⟩ : syracuseStep 1004525 = 376697) (by norm_num)
theorem B1463309 : Blo 650305 1463309 := bbase (se 3 (by rfl) ⟨274370, by rfl⟩ : syracuseStep 1463309 = 548741) (by norm_num)
theorem B1102909 : Blo 650305 1102909 := bbase (se 3 (by rfl) ⟨206795, by rfl⟩ : syracuseStep 1102909 = 413591) (by norm_num)
theorem B1463381 : Blo 650305 1463381 := bbase (se 8 (by rfl) ⟨8574, by rfl⟩ : syracuseStep 1463381 = 17149) (by norm_num)
theorem B939133 : Blo 650305 939133 := bbase (se 3 (by rfl) ⟨176087, by rfl⟩ : syracuseStep 939133 = 352175) (by norm_num)
theorem B1102997 : Blo 650305 1102997 := bbase (se 6 (by rfl) ⟨25851, by rfl⟩ : syracuseStep 1102997 = 51703) (by norm_num)
theorem B1463453 : Blo 650305 1463453 := bbase (se 3 (by rfl) ⟨274397, by rfl⟩ : syracuseStep 1463453 = 548795) (by norm_num)
theorem B1463525 : Blo 650305 1463525 := bbase (se 4 (by rfl) ⟨137205, by rfl⟩ : syracuseStep 1463525 = 274411) (by norm_num)
theorem B1103125 : Blo 650305 1103125 := bbase (se 6 (by rfl) ⟨25854, by rfl⟩ : syracuseStep 1103125 = 51709) (by norm_num)
theorem B1463597 : Blo 650305 1463597 := bbase (se 3 (by rfl) ⟨274424, by rfl⟩ : syracuseStep 1463597 = 548849) (by norm_num)
theorem B1103213 : Blo 650305 1103213 := bbase (se 3 (by rfl) ⟨206852, by rfl⟩ : syracuseStep 1103213 = 413705) (by norm_num)
theorem B1463669 : Blo 650305 1463669 := bbase (se 5 (by rfl) ⟨68609, by rfl⟩ : syracuseStep 1463669 = 137219) (by norm_num)
theorem B1463741 : Blo 650305 1463741 := bbase (se 3 (by rfl) ⟨274451, by rfl⟩ : syracuseStep 1463741 = 548903) (by norm_num)
theorem B742861 : Blo 650305 742861 := bbase (se 3 (by rfl) ⟨139286, by rfl⟩ : syracuseStep 742861 = 278573) (by norm_num)
theorem B1103341 : Blo 650305 1103341 := bbase (se 3 (by rfl) ⟨206876, by rfl⟩ : syracuseStep 1103341 = 413753) (by norm_num)
theorem B3298805 : Blo 650305 3298805 := bbase (se 5 (by rfl) ⟨154631, by rfl⟩ : syracuseStep 3298805 = 309263) (by norm_num)
theorem B1463813 : Blo 650305 1463813 := bbase (se 4 (by rfl) ⟨137232, by rfl⟩ : syracuseStep 1463813 = 274465) (by norm_num)
theorem B1103429 : Blo 650305 1103429 := bbase (se 4 (by rfl) ⟨103446, by rfl⟩ : syracuseStep 1103429 = 206893) (by norm_num)
theorem B1463885 : Blo 650305 1463885 := bbase (se 3 (by rfl) ⟨274478, by rfl⟩ : syracuseStep 1463885 = 548957) (by norm_num)
theorem B2086501 : Blo 650305 2086501 := bbase (se 4 (by rfl) ⟨195609, by rfl⟩ : syracuseStep 2086501 = 391219) (by norm_num)
theorem B1463957 : Blo 650305 1463957 := bbase (se 6 (by rfl) ⟨34311, by rfl⟩ : syracuseStep 1463957 = 68623) (by norm_num)
theorem B1103557 : Blo 650305 1103557 := bbase (se 4 (by rfl) ⟨103458, by rfl⟩ : syracuseStep 1103557 = 206917) (by norm_num)
theorem B1464029 : Blo 650305 1464029 := bbase (se 3 (by rfl) ⟨274505, by rfl⟩ : syracuseStep 1464029 = 549011) (by norm_num)
theorem B1103645 : Blo 650305 1103645 := bbase (se 3 (by rfl) ⟨206933, by rfl⟩ : syracuseStep 1103645 = 413867) (by norm_num)
theorem B1464101 : Blo 650305 1464101 := bbase (se 4 (by rfl) ⟨137259, by rfl⟩ : syracuseStep 1464101 = 274519) (by norm_num)
theorem B1464173 : Blo 650305 1464173 := bbase (se 3 (by rfl) ⟨274532, by rfl⟩ : syracuseStep 1464173 = 549065) (by norm_num)
theorem B1103773 : Blo 650305 1103773 := bbase (se 3 (by rfl) ⟨206957, by rfl⟩ : syracuseStep 1103773 = 413915) (by norm_num)
theorem B1464245 : Blo 650305 1464245 := bbase (se 5 (by rfl) ⟨68636, by rfl⟩ : syracuseStep 1464245 = 137273) (by norm_num)
theorem B22566869 : Blo 650305 22566869 := bbase (se 7 (by rfl) ⟨264455, by rfl⟩ : syracuseStep 22566869 = 528911) (by norm_num)
theorem B2578405 : Blo 650305 2578405 := bbase (se 4 (by rfl) ⟨241725, by rfl⟩ : syracuseStep 2578405 = 483451) (by norm_num)
theorem B1103861 : Blo 650305 1103861 := bbase (se 5 (by rfl) ⟨51743, by rfl⟩ : syracuseStep 1103861 = 103487) (by norm_num)
theorem B1464317 : Blo 650305 1464317 := bbase (se 3 (by rfl) ⟨274559, by rfl⟩ : syracuseStep 1464317 = 549119) (by norm_num)
theorem B2480165 : Blo 650305 2480165 := bbase (se 4 (by rfl) ⟨232515, by rfl⟩ : syracuseStep 2480165 = 465031) (by norm_num)
theorem B1464389 : Blo 650305 1464389 := bbase (se 4 (by rfl) ⟨137286, by rfl⟩ : syracuseStep 1464389 = 274573) (by norm_num)
theorem B1103989 : Blo 650305 1103989 := bbase (se 5 (by rfl) ⟨51749, by rfl⟩ : syracuseStep 1103989 = 103499) (by norm_num)
theorem B1464461 : Blo 650305 1464461 := bbase (se 3 (by rfl) ⟨274586, by rfl⟩ : syracuseStep 1464461 = 549173) (by norm_num)
theorem B1235101 : Blo 650305 1235101 := bbase (se 3 (by rfl) ⟨231581, by rfl⟩ : syracuseStep 1235101 = 463163) (by norm_num)
theorem B1104077 : Blo 650305 1104077 := bbase (se 3 (by rfl) ⟨207014, by rfl⟩ : syracuseStep 1104077 = 414029) (by norm_num)
theorem B1464533 : Blo 650305 1464533 := bbase (se 7 (by rfl) ⟨17162, by rfl⟩ : syracuseStep 1464533 = 34325) (by norm_num)
theorem B1464605 : Blo 650305 1464605 := bbase (se 3 (by rfl) ⟨274613, by rfl⟩ : syracuseStep 1464605 = 549227) (by norm_num)
theorem B1235245 : Blo 650305 1235245 := bbase (se 3 (by rfl) ⟨231608, by rfl⟩ : syracuseStep 1235245 = 463217) (by norm_num)
theorem B2480453 : Blo 650305 2480453 := bbase (se 4 (by rfl) ⟨232542, by rfl⟩ : syracuseStep 2480453 = 465085) (by norm_num)
theorem B1464677 : Blo 650305 1464677 := bbase (se 4 (by rfl) ⟨137313, by rfl⟩ : syracuseStep 1464677 = 274627) (by norm_num)
theorem B1464749 : Blo 650305 1464749 := bbase (se 3 (by rfl) ⟨274640, by rfl⟩ : syracuseStep 1464749 = 549281) (by norm_num)
theorem B1235405 : Blo 650305 1235405 := bbase (se 3 (by rfl) ⟨231638, by rfl⟩ : syracuseStep 1235405 = 463277) (by norm_num)
theorem B1464821 : Blo 650305 1464821 := bbase (se 5 (by rfl) ⟨68663, by rfl⟩ : syracuseStep 1464821 = 137327) (by norm_num)
theorem B1104389 : Blo 650305 1104389 := bbase (se 4 (by rfl) ⟨103536, by rfl⟩ : syracuseStep 1104389 = 207073) (by norm_num)
theorem B1858085 : Blo 650305 1858085 := bbase (se 4 (by rfl) ⟨174195, by rfl⟩ : syracuseStep 1858085 = 348391) (by norm_num)
theorem B1464893 : Blo 650305 1464893 := bbase (se 3 (by rfl) ⟨274667, by rfl⟩ : syracuseStep 1464893 = 549335) (by norm_num)
theorem B1235549 : Blo 650305 1235549 := bbase (se 3 (by rfl) ⟨231665, by rfl⟩ : syracuseStep 1235549 = 463331) (by norm_num)
theorem B940645 : Blo 650305 940645 := bbase (se 4 (by rfl) ⟨88185, by rfl⟩ : syracuseStep 940645 = 176371) (by norm_num)
theorem B1464965 : Blo 650305 1464965 := bbase (se 4 (by rfl) ⟨137340, by rfl⟩ : syracuseStep 1464965 = 274681) (by norm_num)
theorem B1465037 : Blo 650305 1465037 := bbase (se 3 (by rfl) ⟨274694, by rfl⟩ : syracuseStep 1465037 = 549389) (by norm_num)
theorem B3300101 : Blo 650305 3300101 := bbase (se 4 (by rfl) ⟨309384, by rfl⟩ : syracuseStep 3300101 = 618769) (by norm_num)
theorem B1006349 : Blo 650305 1006349 := bbase (se 3 (by rfl) ⟨188690, by rfl⟩ : syracuseStep 1006349 = 377381) (by norm_num)
theorem B1465109 : Blo 650305 1465109 := bbase (se 6 (by rfl) ⟨34338, by rfl⟩ : syracuseStep 1465109 = 68677) (by norm_num)
theorem B3726101 : Blo 650305 3726101 := bbase (se 6 (by rfl) ⟨87330, by rfl⟩ : syracuseStep 3726101 = 174661) (by norm_num)
theorem B1465181 : Blo 650305 1465181 := bbase (se 3 (by rfl) ⟨274721, by rfl⟩ : syracuseStep 1465181 = 549443) (by norm_num)
theorem B1235837 : Blo 650305 1235837 := bbase (se 3 (by rfl) ⟨231719, by rfl⟩ : syracuseStep 1235837 = 463439) (by norm_num)
theorem B1465253 : Blo 650305 1465253 := bbase (se 4 (by rfl) ⟨137367, by rfl⟩ : syracuseStep 1465253 = 274735) (by norm_num)
theorem B1465325 : Blo 650305 1465325 := bbase (se 3 (by rfl) ⟨274748, by rfl⟩ : syracuseStep 1465325 = 549497) (by norm_num)
theorem B1563637 : Blo 650305 1563637 := bbase (se 5 (by rfl) ⟨73295, by rfl⟩ : syracuseStep 1563637 = 146591) (by norm_num)
theorem B1235989 : Blo 650305 1235989 := bbase (se 6 (by rfl) ⟨28968, by rfl⟩ : syracuseStep 1235989 = 57937) (by norm_num)
theorem B1465397 : Blo 650305 1465397 := bbase (se 5 (by rfl) ⟨68690, by rfl⟩ : syracuseStep 1465397 = 137381) (by norm_num)
theorem B1465469 : Blo 650305 1465469 := bbase (se 3 (by rfl) ⟨274775, by rfl⟩ : syracuseStep 1465469 = 549551) (by norm_num)
theorem B2645173 : Blo 650305 2645173 := bbase (se 5 (by rfl) ⟨123992, by rfl⟩ : syracuseStep 2645173 = 247985) (by norm_num)
theorem B1465541 : Blo 650305 1465541 := bbase (se 4 (by rfl) ⟨137394, by rfl⟩ : syracuseStep 1465541 = 274789) (by norm_num)
theorem B1465613 : Blo 650305 1465613 := bbase (se 3 (by rfl) ⟨274802, by rfl⟩ : syracuseStep 1465613 = 549605) (by norm_num)
theorem B1236293 : Blo 650305 1236293 := bbase (se 4 (by rfl) ⟨115902, by rfl⟩ : syracuseStep 1236293 = 231805) (by norm_num)
theorem B1465685 : Blo 650305 1465685 := bbase (se 11 (by rfl) ⟨1073, by rfl⟩ : syracuseStep 1465685 = 2147) (by norm_num)
theorem B13557077 : Blo 650305 13557077 := bbase (se 11 (by rfl) ⟨9929, by rfl⟩ : syracuseStep 13557077 = 19859) (by norm_num)
theorem B1465757 : Blo 650305 1465757 := bbase (se 3 (by rfl) ⟨274829, by rfl⟩ : syracuseStep 1465757 = 549659) (by norm_num)
theorem B1465829 : Blo 650305 1465829 := bbase (se 4 (by rfl) ⟨137421, by rfl⟩ : syracuseStep 1465829 = 274843) (by norm_num)
theorem B2481637 : Blo 650305 2481637 := bbase (se 4 (by rfl) ⟨232653, by rfl⟩ : syracuseStep 2481637 = 465307) (by norm_num)
theorem B941581 : Blo 650305 941581 := bbase (se 3 (by rfl) ⟨176546, by rfl⟩ : syracuseStep 941581 = 353093) (by norm_num)
theorem B1465901 : Blo 650305 1465901 := bbase (se 3 (by rfl) ⟨274856, by rfl⟩ : syracuseStep 1465901 = 549713) (by norm_num)
theorem B1465973 : Blo 650305 1465973 := bbase (se 5 (by rfl) ⟨68717, by rfl⟩ : syracuseStep 1465973 = 137435) (by norm_num)
theorem B1466045 : Blo 650305 1466045 := bbase (se 3 (by rfl) ⟨274883, by rfl⟩ : syracuseStep 1466045 = 549767) (by norm_num)
theorem B1859269 : Blo 650305 1859269 := bbase (se 4 (by rfl) ⟨174306, by rfl⟩ : syracuseStep 1859269 = 348613) (by norm_num)
theorem B1466117 : Blo 650305 1466117 := bbase (se 4 (by rfl) ⟨137448, by rfl⟩ : syracuseStep 1466117 = 274897) (by norm_num)
theorem B2481941 : Blo 650305 2481941 := bbase (se 6 (by rfl) ⟨58170, by rfl⟩ : syracuseStep 2481941 = 116341) (by norm_num)
theorem B1466189 : Blo 650305 1466189 := bbase (se 3 (by rfl) ⟨274910, by rfl⟩ : syracuseStep 1466189 = 549821) (by norm_num)
theorem B1859429 : Blo 650305 1859429 := bbase (se 4 (by rfl) ⟨174321, by rfl⟩ : syracuseStep 1859429 = 348643) (by norm_num)
theorem B1466261 : Blo 650305 1466261 := bbase (se 6 (by rfl) ⟨34365, by rfl⟩ : syracuseStep 1466261 = 68731) (by norm_num)
theorem B1269661 : Blo 650305 1269661 := bbase (se 3 (by rfl) ⟨238061, by rfl⟩ : syracuseStep 1269661 = 476123) (by norm_num)
theorem B1564589 : Blo 650305 1564589 := bbase (se 3 (by rfl) ⟨293360, by rfl⟩ : syracuseStep 1564589 = 586721) (by norm_num)
theorem B1466333 : Blo 650305 1466333 := bbase (se 3 (by rfl) ⟨274937, by rfl⟩ : syracuseStep 1466333 = 549875) (by norm_num)
theorem B1564645 : Blo 650305 1564645 := bbase (se 4 (by rfl) ⟨146685, by rfl⟩ : syracuseStep 1564645 = 293371) (by norm_num)
theorem B3301397 : Blo 650305 3301397 := bbase (se 6 (by rfl) ⟨77376, by rfl⟩ : syracuseStep 3301397 = 154753) (by norm_num)
theorem B1466405 : Blo 650305 1466405 := bbase (se 4 (by rfl) ⟨137475, by rfl⟩ : syracuseStep 1466405 = 274951) (by norm_num)
theorem B1237045 : Blo 650305 1237045 := bbase (se 5 (by rfl) ⟨57986, by rfl⟩ : syracuseStep 1237045 = 115973) (by norm_num)
theorem B1859669 : Blo 650305 1859669 := bbase (se 8 (by rfl) ⟨10896, by rfl⟩ : syracuseStep 1859669 = 21793) (by norm_num)
theorem B1466477 : Blo 650305 1466477 := bbase (se 3 (by rfl) ⟨274964, by rfl⟩ : syracuseStep 1466477 = 549929) (by norm_num)
theorem B2384005 : Blo 650305 2384005 := bbase (se 4 (by rfl) ⟨223500, by rfl⟩ : syracuseStep 2384005 = 447001) (by norm_num)
theorem B1466549 : Blo 650305 1466549 := bbase (se 5 (by rfl) ⟨68744, by rfl⟩ : syracuseStep 1466549 = 137489) (by norm_num)
theorem B1237189 : Blo 650305 1237189 := bbase (se 4 (by rfl) ⟨115986, by rfl⟩ : syracuseStep 1237189 = 231973) (by norm_num)
theorem B1466621 : Blo 650305 1466621 := bbase (se 3 (by rfl) ⟨274991, by rfl⟩ : syracuseStep 1466621 = 549983) (by norm_num)
theorem B1859861 : Blo 650305 1859861 := bbase (se 6 (by rfl) ⟨43590, by rfl⟩ : syracuseStep 1859861 = 87181) (by norm_num)
theorem B1466693 : Blo 650305 1466693 := bbase (se 4 (by rfl) ⟨137502, by rfl⟩ : syracuseStep 1466693 = 275005) (by norm_num)
theorem B1565021 : Blo 650305 1565021 := bbase (se 3 (by rfl) ⟨293441, by rfl⟩ : syracuseStep 1565021 = 586883) (by norm_num)
theorem B1237349 : Blo 650305 1237349 := bbase (se 4 (by rfl) ⟨116001, by rfl⟩ : syracuseStep 1237349 = 232003) (by norm_num)
theorem B1466765 : Blo 650305 1466765 := bbase (se 3 (by rfl) ⟨275018, by rfl⟩ : syracuseStep 1466765 = 550037) (by norm_num)
theorem B2646437 : Blo 650305 2646437 := bbase (se 4 (by rfl) ⟨248103, by rfl⟩ : syracuseStep 2646437 = 496207) (by norm_num)
theorem B1466837 : Blo 650305 1466837 := bbase (se 7 (by rfl) ⟨17189, by rfl⟩ : syracuseStep 1466837 = 34379) (by norm_num)
theorem B1237493 : Blo 650305 1237493 := bbase (se 5 (by rfl) ⟨58007, by rfl⟩ : syracuseStep 1237493 = 116015) (by norm_num)
theorem B1466909 : Blo 650305 1466909 := bbase (se 3 (by rfl) ⟨275045, by rfl⟩ : syracuseStep 1466909 = 550091) (by norm_num)
theorem B1565261 : Blo 650305 1565261 := bbase (se 3 (by rfl) ⟨293486, by rfl⟩ : syracuseStep 1565261 = 586973) (by norm_num)
theorem B975461 : Blo 650305 975461 := bbase (se 4 (by rfl) ⟨91449, by rfl⟩ : syracuseStep 975461 = 182899) (by norm_num)
theorem B1466981 : Blo 650305 1466981 := bbase (se 4 (by rfl) ⟨137529, by rfl⟩ : syracuseStep 1466981 = 275059) (by norm_num)
theorem B975485 : Blo 650305 975485 := bbase (se 3 (by rfl) ⟨182903, by rfl⟩ : syracuseStep 975485 = 365807) (by norm_num)
theorem B975509 : Blo 650305 975509 := bbase (se 6 (by rfl) ⟨22863, by rfl⟩ : syracuseStep 975509 = 45727) (by norm_num)
theorem B975533 : Blo 650305 975533 := bbase (se 3 (by rfl) ⟨182912, by rfl⟩ : syracuseStep 975533 = 365825) (by norm_num)
theorem B1467053 : Blo 650305 1467053 := bbase (se 3 (by rfl) ⟨275072, by rfl⟩ : syracuseStep 1467053 = 550145) (by norm_num)
theorem B975557 : Blo 650305 975557 := bbase (se 4 (by rfl) ⟨91458, by rfl⟩ : syracuseStep 975557 = 182917) (by norm_num)
theorem B1172173 : Blo 650305 1172173 := bbase (se 3 (by rfl) ⟨219782, by rfl⟩ : syracuseStep 1172173 = 439565) (by norm_num)
theorem B975581 : Blo 650305 975581 := bbase (se 3 (by rfl) ⟨182921, by rfl⟩ : syracuseStep 975581 = 365843) (by norm_num)
theorem B975605 : Blo 650305 975605 := bbase (se 5 (by rfl) ⟨45731, by rfl⟩ : syracuseStep 975605 = 91463) (by norm_num)
theorem B1467125 : Blo 650305 1467125 := bbase (se 5 (by rfl) ⟨68771, by rfl⟩ : syracuseStep 1467125 = 137543) (by norm_num)
theorem B975629 : Blo 650305 975629 := bbase (se 3 (by rfl) ⟨182930, by rfl⟩ : syracuseStep 975629 = 365861) (by norm_num)
theorem B1237781 : Blo 650305 1237781 := bbase (se 6 (by rfl) ⟨29010, by rfl⟩ : syracuseStep 1237781 = 58021) (by norm_num)
theorem B975653 : Blo 650305 975653 := bbase (se 4 (by rfl) ⟨91467, by rfl⟩ : syracuseStep 975653 = 182935) (by norm_num)
theorem B975677 : Blo 650305 975677 := bbase (se 3 (by rfl) ⟨182939, by rfl⟩ : syracuseStep 975677 = 365879) (by norm_num)
theorem B1467197 : Blo 650305 1467197 := bbase (se 3 (by rfl) ⟨275099, by rfl⟩ : syracuseStep 1467197 = 550199) (by norm_num)
theorem B975701 : Blo 650305 975701 := bbase (se 9 (by rfl) ⟨2858, by rfl⟩ : syracuseStep 975701 = 5717) (by norm_num)
theorem B975725 : Blo 650305 975725 := bbase (se 3 (by rfl) ⟨182948, by rfl⟩ : syracuseStep 975725 = 365897) (by norm_num)
theorem B4186997 : Blo 650305 4186997 := bbase (se 5 (by rfl) ⟨196265, by rfl⟩ : syracuseStep 4186997 = 392531) (by norm_num)
theorem B975749 : Blo 650305 975749 := bbase (se 4 (by rfl) ⟨91476, by rfl⟩ : syracuseStep 975749 = 182953) (by norm_num)
theorem B1467269 : Blo 650305 1467269 := bbase (se 4 (by rfl) ⟨137556, by rfl⟩ : syracuseStep 1467269 = 275113) (by norm_num)
theorem B975773 : Blo 650305 975773 := bbase (se 3 (by rfl) ⟨182957, by rfl⟩ : syracuseStep 975773 = 365915) (by norm_num)
theorem B1237933 : Blo 650305 1237933 := bbase (se 3 (by rfl) ⟨232112, by rfl⟩ : syracuseStep 1237933 = 464225) (by norm_num)
theorem B975797 : Blo 650305 975797 := bbase (se 5 (by rfl) ⟨45740, by rfl⟩ : syracuseStep 975797 = 91481) (by norm_num)
theorem B975821 : Blo 650305 975821 := bbase (se 3 (by rfl) ⟨182966, by rfl⟩ : syracuseStep 975821 = 365933) (by norm_num)
theorem B1467341 : Blo 650305 1467341 := bbase (se 3 (by rfl) ⟨275126, by rfl⟩ : syracuseStep 1467341 = 550253) (by norm_num)
theorem B975845 : Blo 650305 975845 := bbase (se 4 (by rfl) ⟨91485, by rfl⟩ : syracuseStep 975845 = 182971) (by norm_num)
theorem B975869 : Blo 650305 975869 := bbase (se 3 (by rfl) ⟨182975, by rfl⟩ : syracuseStep 975869 = 365951) (by norm_num)
theorem B975893 : Blo 650305 975893 := bbase (se 6 (by rfl) ⟨22872, by rfl⟩ : syracuseStep 975893 = 45745) (by norm_num)
theorem B1467413 : Blo 650305 1467413 := bbase (se 6 (by rfl) ⟨34392, by rfl⟩ : syracuseStep 1467413 = 68785) (by norm_num)
theorem B975917 : Blo 650305 975917 := bbase (se 3 (by rfl) ⟨182984, by rfl⟩ : syracuseStep 975917 = 365969) (by norm_num)
theorem B975941 : Blo 650305 975941 := bbase (se 4 (by rfl) ⟨91494, by rfl⟩ : syracuseStep 975941 = 182989) (by norm_num)
theorem B975965 : Blo 650305 975965 := bbase (se 3 (by rfl) ⟨182993, by rfl⟩ : syracuseStep 975965 = 365987) (by norm_num)
theorem B1467485 : Blo 650305 1467485 := bbase (se 3 (by rfl) ⟨275153, by rfl⟩ : syracuseStep 1467485 = 550307) (by norm_num)
theorem B975989 : Blo 650305 975989 := bbase (se 5 (by rfl) ⟨45749, by rfl⟩ : syracuseStep 975989 = 91499) (by norm_num)
theorem B976013 : Blo 650305 976013 := bbase (se 3 (by rfl) ⟨183002, by rfl⟩ : syracuseStep 976013 = 366005) (by norm_num)
theorem B976037 : Blo 650305 976037 := bbase (se 4 (by rfl) ⟨91503, by rfl⟩ : syracuseStep 976037 = 183007) (by norm_num)
theorem B1467557 : Blo 650305 1467557 := bbase (se 4 (by rfl) ⟨137583, by rfl⟩ : syracuseStep 1467557 = 275167) (by norm_num)
theorem B976061 : Blo 650305 976061 := bbase (se 3 (by rfl) ⟨183011, by rfl⟩ : syracuseStep 976061 = 366023) (by norm_num)
theorem B976085 : Blo 650305 976085 := bbase (se 7 (by rfl) ⟨11438, by rfl⟩ : syracuseStep 976085 = 22877) (by norm_num)
theorem B1238237 : Blo 650305 1238237 := bbase (se 3 (by rfl) ⟨232169, by rfl⟩ : syracuseStep 1238237 = 464339) (by norm_num)
theorem B976109 : Blo 650305 976109 := bbase (se 3 (by rfl) ⟨183020, by rfl⟩ : syracuseStep 976109 = 366041) (by norm_num)
theorem B1467629 : Blo 650305 1467629 := bbase (se 3 (by rfl) ⟨275180, by rfl⟩ : syracuseStep 1467629 = 550361) (by norm_num)
theorem B1860853 : Blo 650305 1860853 := bbase (se 5 (by rfl) ⟨87227, by rfl⟩ : syracuseStep 1860853 = 174455) (by norm_num)
theorem B976133 : Blo 650305 976133 := bbase (se 4 (by rfl) ⟨91512, by rfl⟩ : syracuseStep 976133 = 183025) (by norm_num)
theorem B976157 : Blo 650305 976157 := bbase (se 3 (by rfl) ⟨183029, by rfl⟩ : syracuseStep 976157 = 366059) (by norm_num)
theorem B3302693 : Blo 650305 3302693 := bbase (se 4 (by rfl) ⟨309627, by rfl⟩ : syracuseStep 3302693 = 619255) (by norm_num)
theorem B976181 : Blo 650305 976181 := bbase (se 5 (by rfl) ⟨45758, by rfl⟩ : syracuseStep 976181 = 91517) (by norm_num)
theorem B1467701 : Blo 650305 1467701 := bbase (se 5 (by rfl) ⟨68798, by rfl⟩ : syracuseStep 1467701 = 137597) (by norm_num)
theorem B976205 : Blo 650305 976205 := bbase (se 3 (by rfl) ⟨183038, by rfl⟩ : syracuseStep 976205 = 366077) (by norm_num)
theorem B976229 : Blo 650305 976229 := bbase (se 4 (by rfl) ⟨91521, by rfl⟩ : syracuseStep 976229 = 183043) (by norm_num)
theorem B976253 : Blo 650305 976253 := bbase (se 3 (by rfl) ⟨183047, by rfl⟩ : syracuseStep 976253 = 366095) (by norm_num)
theorem B1467773 : Blo 650305 1467773 := bbase (se 3 (by rfl) ⟨275207, by rfl⟩ : syracuseStep 1467773 = 550415) (by norm_num)
theorem B976277 : Blo 650305 976277 := bbase (se 6 (by rfl) ⟨22881, by rfl⟩ : syracuseStep 976277 = 45763) (by norm_num)
theorem B976301 : Blo 650305 976301 := bbase (se 3 (by rfl) ⟨183056, by rfl⟩ : syracuseStep 976301 = 366113) (by norm_num)
theorem B976325 : Blo 650305 976325 := bbase (se 4 (by rfl) ⟨91530, by rfl⟩ : syracuseStep 976325 = 183061) (by norm_num)
theorem B1467845 : Blo 650305 1467845 := bbase (se 4 (by rfl) ⟨137610, by rfl⟩ : syracuseStep 1467845 = 275221) (by norm_num)
theorem B976349 : Blo 650305 976349 := bbase (se 3 (by rfl) ⟨183065, by rfl⟩ : syracuseStep 976349 = 366131) (by norm_num)
theorem B1041893 : Blo 650305 1041893 := bbase (se 4 (by rfl) ⟨97677, by rfl⟩ : syracuseStep 1041893 = 195355) (by norm_num)
theorem B1172965 : Blo 650305 1172965 := bbase (se 4 (by rfl) ⟨109965, by rfl⟩ : syracuseStep 1172965 = 219931) (by norm_num)
theorem B976373 : Blo 650305 976373 := bbase (se 5 (by rfl) ⟨45767, by rfl⟩ : syracuseStep 976373 = 91535) (by norm_num)
theorem B1172981 : Blo 650305 1172981 := bbase (se 5 (by rfl) ⟨54983, by rfl⟩ : syracuseStep 1172981 = 109967) (by norm_num)
theorem B976397 : Blo 650305 976397 := bbase (se 3 (by rfl) ⟨183074, by rfl⟩ : syracuseStep 976397 = 366149) (by norm_num)
theorem B1467917 : Blo 650305 1467917 := bbase (se 3 (by rfl) ⟨275234, by rfl⟩ : syracuseStep 1467917 = 550469) (by norm_num)
theorem B976421 : Blo 650305 976421 := bbase (se 4 (by rfl) ⟨91539, by rfl⟩ : syracuseStep 976421 = 183079) (by norm_num)
theorem B976445 : Blo 650305 976445 := bbase (se 3 (by rfl) ⟨183083, by rfl⟩ : syracuseStep 976445 = 366167) (by norm_num)
theorem B976469 : Blo 650305 976469 := bbase (se 8 (by rfl) ⟨5721, by rfl⟩ : syracuseStep 976469 = 11443) (by norm_num)
theorem B1467989 : Blo 650305 1467989 := bbase (se 8 (by rfl) ⟨8601, by rfl⟩ : syracuseStep 1467989 = 17203) (by norm_num)
theorem B976493 : Blo 650305 976493 := bbase (se 3 (by rfl) ⟨183092, by rfl⟩ : syracuseStep 976493 = 366185) (by norm_num)
theorem B976517 : Blo 650305 976517 := bbase (se 4 (by rfl) ⟨91548, by rfl⟩ : syracuseStep 976517 = 183097) (by norm_num)
theorem B976541 : Blo 650305 976541 := bbase (se 3 (by rfl) ⟨183101, by rfl⟩ : syracuseStep 976541 = 366203) (by norm_num)
theorem B1468061 : Blo 650305 1468061 := bbase (se 3 (by rfl) ⟨275261, by rfl⟩ : syracuseStep 1468061 = 550523) (by norm_num)
theorem B1042085 : Blo 650305 1042085 := bbase (se 4 (by rfl) ⟨97695, by rfl⟩ : syracuseStep 1042085 = 195391) (by norm_num)
theorem B976565 : Blo 650305 976565 := bbase (se 5 (by rfl) ⟨45776, by rfl⟩ : syracuseStep 976565 = 91553) (by norm_num)
theorem B1173197 : Blo 650305 1173197 := bbase (se 3 (by rfl) ⟨219974, by rfl⟩ : syracuseStep 1173197 = 439949) (by norm_num)
theorem B976589 : Blo 650305 976589 := bbase (se 3 (by rfl) ⟨183110, by rfl⟩ : syracuseStep 976589 = 366221) (by norm_num)
theorem B976613 : Blo 650305 976613 := bbase (se 4 (by rfl) ⟨91557, by rfl⟩ : syracuseStep 976613 = 183115) (by norm_num)
theorem B1468133 : Blo 650305 1468133 := bbase (se 4 (by rfl) ⟨137637, by rfl⟩ : syracuseStep 1468133 = 275275) (by norm_num)
theorem B943861 : Blo 650305 943861 := bbase (se 5 (by rfl) ⟨44243, by rfl⟩ : syracuseStep 943861 = 88487) (by norm_num)
theorem B976637 : Blo 650305 976637 := bbase (se 3 (by rfl) ⟨183119, by rfl⟩ : syracuseStep 976637 = 366239) (by norm_num)
theorem B976661 : Blo 650305 976661 := bbase (se 6 (by rfl) ⟨22890, by rfl⟩ : syracuseStep 976661 = 45781) (by norm_num)
theorem B976685 : Blo 650305 976685 := bbase (se 3 (by rfl) ⟨183128, by rfl⟩ : syracuseStep 976685 = 366257) (by norm_num)
theorem B1468205 : Blo 650305 1468205 := bbase (se 3 (by rfl) ⟨275288, by rfl⟩ : syracuseStep 1468205 = 550577) (by norm_num)
theorem B976709 : Blo 650305 976709 := bbase (se 4 (by rfl) ⟨91566, by rfl⟩ : syracuseStep 976709 = 183133) (by norm_num)
theorem B2484053 : Blo 650305 2484053 := bbase (se 9 (by rfl) ⟨7277, by rfl⟩ : syracuseStep 2484053 = 14555) (by norm_num)
theorem B1173341 : Blo 650305 1173341 := bbase (se 3 (by rfl) ⟨220001, by rfl⟩ : syracuseStep 1173341 = 440003) (by norm_num)
theorem B976733 : Blo 650305 976733 := bbase (se 3 (by rfl) ⟨183137, by rfl⟩ : syracuseStep 976733 = 366275) (by norm_num)
theorem B976757 : Blo 650305 976757 := bbase (se 5 (by rfl) ⟨45785, by rfl⟩ : syracuseStep 976757 = 91571) (by norm_num)
theorem B1468277 : Blo 650305 1468277 := bbase (se 5 (by rfl) ⟨68825, by rfl⟩ : syracuseStep 1468277 = 137651) (by norm_num)
theorem B714629 : Blo 650305 714629 := bbase (se 4 (by rfl) ⟨66996, by rfl⟩ : syracuseStep 714629 = 133993) (by norm_num)
theorem B976781 : Blo 650305 976781 := bbase (se 3 (by rfl) ⟨183146, by rfl⟩ : syracuseStep 976781 = 366293) (by norm_num)
theorem B976805 : Blo 650305 976805 := bbase (se 4 (by rfl) ⟨91575, by rfl⟩ : syracuseStep 976805 = 183151) (by norm_num)
theorem B976829 : Blo 650305 976829 := bbase (se 3 (by rfl) ⟨183155, by rfl⟩ : syracuseStep 976829 = 366311) (by norm_num)
theorem B1468349 : Blo 650305 1468349 := bbase (se 3 (by rfl) ⟨275315, by rfl⟩ : syracuseStep 1468349 = 550631) (by norm_num)
theorem B1238989 : Blo 650305 1238989 := bbase (se 3 (by rfl) ⟨232310, by rfl⟩ : syracuseStep 1238989 = 464621) (by norm_num)
theorem B976853 : Blo 650305 976853 := bbase (se 7 (by rfl) ⟨11447, by rfl⟩ : syracuseStep 976853 = 22895) (by norm_num)
theorem B976877 : Blo 650305 976877 := bbase (se 3 (by rfl) ⟨183164, by rfl⟩ : syracuseStep 976877 = 366329) (by norm_num)
theorem B4777973 : Blo 650305 4777973 := bbase (se 5 (by rfl) ⟨223967, by rfl⟩ : syracuseStep 4777973 = 447935) (by norm_num)
theorem B976901 : Blo 650305 976901 := bbase (se 4 (by rfl) ⟨91584, by rfl⟩ : syracuseStep 976901 = 183169) (by norm_num)
theorem B1468421 : Blo 650305 1468421 := bbase (se 4 (by rfl) ⟨137664, by rfl⟩ : syracuseStep 1468421 = 275329) (by norm_num)
theorem B976925 : Blo 650305 976925 := bbase (se 3 (by rfl) ⟨183173, by rfl⟩ : syracuseStep 976925 = 366347) (by norm_num)
theorem B976949 : Blo 650305 976949 := bbase (se 5 (by rfl) ⟨45794, by rfl⟩ : syracuseStep 976949 = 91589) (by norm_num)
theorem B976973 : Blo 650305 976973 := bbase (se 3 (by rfl) ⟨183182, by rfl⟩ : syracuseStep 976973 = 366365) (by norm_num)
theorem B1468493 : Blo 650305 1468493 := bbase (se 3 (by rfl) ⟨275342, by rfl⟩ : syracuseStep 1468493 = 550685) (by norm_num)
theorem B1239133 : Blo 650305 1239133 := bbase (se 3 (by rfl) ⟨232337, by rfl⟩ : syracuseStep 1239133 = 464675) (by norm_num)
theorem B976997 : Blo 650305 976997 := bbase (se 4 (by rfl) ⟨91593, by rfl⟩ : syracuseStep 976997 = 183187) (by norm_num)
theorem B977021 : Blo 650305 977021 := bbase (se 3 (by rfl) ⟨183191, by rfl⟩ : syracuseStep 977021 = 366383) (by norm_num)
theorem B977045 : Blo 650305 977045 := bbase (se 6 (by rfl) ⟨22899, by rfl⟩ : syracuseStep 977045 = 45799) (by norm_num)
theorem B1468565 : Blo 650305 1468565 := bbase (se 6 (by rfl) ⟨34419, by rfl⟩ : syracuseStep 1468565 = 68839) (by norm_num)
theorem B977069 : Blo 650305 977069 := bbase (se 3 (by rfl) ⟨183200, by rfl⟩ : syracuseStep 977069 = 366401) (by norm_num)
theorem B977093 : Blo 650305 977093 := bbase (se 4 (by rfl) ⟨91602, by rfl⟩ : syracuseStep 977093 = 183205) (by norm_num)
theorem B977117 : Blo 650305 977117 := bbase (se 3 (by rfl) ⟨183209, by rfl⟩ : syracuseStep 977117 = 366419) (by norm_num)
theorem B1468637 : Blo 650305 1468637 := bbase (se 3 (by rfl) ⟨275369, by rfl⟩ : syracuseStep 1468637 = 550739) (by norm_num)
theorem B977141 : Blo 650305 977141 := bbase (se 5 (by rfl) ⟨45803, by rfl⟩ : syracuseStep 977141 = 91607) (by norm_num)
theorem B1239293 : Blo 650305 1239293 := bbase (se 3 (by rfl) ⟨232367, by rfl⟩ : syracuseStep 1239293 = 464735) (by norm_num)
theorem B977165 : Blo 650305 977165 := bbase (se 3 (by rfl) ⟨183218, by rfl⟩ : syracuseStep 977165 = 366437) (by norm_num)
theorem B977189 : Blo 650305 977189 := bbase (se 4 (by rfl) ⟨91611, by rfl⟩ : syracuseStep 977189 = 183223) (by norm_num)
theorem B1468709 : Blo 650305 1468709 := bbase (se 4 (by rfl) ⟨137691, by rfl⟩ : syracuseStep 1468709 = 275383) (by norm_num)
theorem B4942133 : Blo 650305 4942133 := bbase (se 5 (by rfl) ⟨231662, by rfl⟩ : syracuseStep 4942133 = 463325) (by norm_num)
theorem B977213 : Blo 650305 977213 := bbase (se 3 (by rfl) ⟨183227, by rfl⟩ : syracuseStep 977213 = 366455) (by norm_num)
theorem B1861957 : Blo 650305 1861957 := bbase (se 4 (by rfl) ⟨174558, by rfl⟩ : syracuseStep 1861957 = 349117) (by norm_num)
theorem B977237 : Blo 650305 977237 := bbase (se 10 (by rfl) ⟨1431, by rfl⟩ : syracuseStep 977237 = 2863) (by norm_num)
theorem B878941 : Blo 650305 878941 := bbase (se 3 (by rfl) ⟨164801, by rfl⟩ : syracuseStep 878941 = 329603) (by norm_num)
theorem B977261 : Blo 650305 977261 := bbase (se 3 (by rfl) ⟨183236, by rfl⟩ : syracuseStep 977261 = 366473) (by norm_num)
theorem B1468781 : Blo 650305 1468781 := bbase (se 3 (by rfl) ⟨275396, by rfl⟩ : syracuseStep 1468781 = 550793) (by norm_num)
theorem B977285 : Blo 650305 977285 := bbase (se 4 (by rfl) ⟨91620, by rfl⟩ : syracuseStep 977285 = 183241) (by norm_num)
theorem B1239437 : Blo 650305 1239437 := bbase (se 3 (by rfl) ⟨232394, by rfl⟩ : syracuseStep 1239437 = 464789) (by norm_num)
theorem B2779541 : Blo 650305 2779541 := bbase (se 6 (by rfl) ⟨65145, by rfl⟩ : syracuseStep 2779541 = 130291) (by norm_num)
theorem B5564821 : Blo 650305 5564821 := bbase (se 6 (by rfl) ⟨130425, by rfl⟩ : syracuseStep 5564821 = 260851) (by norm_num)
theorem B977309 : Blo 650305 977309 := bbase (se 3 (by rfl) ⟨183245, by rfl⟩ : syracuseStep 977309 = 366491) (by norm_num)
theorem B977333 : Blo 650305 977333 := bbase (se 5 (by rfl) ⟨45812, by rfl⟩ : syracuseStep 977333 = 91625) (by norm_num)
theorem B1468853 : Blo 650305 1468853 := bbase (se 5 (by rfl) ⟨68852, by rfl⟩ : syracuseStep 1468853 = 137705) (by norm_num)
theorem B977357 : Blo 650305 977357 := bbase (se 3 (by rfl) ⟨183254, by rfl⟩ : syracuseStep 977357 = 366509) (by norm_num)
theorem B977381 : Blo 650305 977381 := bbase (se 4 (by rfl) ⟨91629, by rfl⟩ : syracuseStep 977381 = 183259) (by norm_num)
theorem B977405 : Blo 650305 977405 := bbase (se 3 (by rfl) ⟨183263, by rfl⟩ : syracuseStep 977405 = 366527) (by norm_num)
theorem B1468925 : Blo 650305 1468925 := bbase (se 3 (by rfl) ⟨275423, by rfl⟩ : syracuseStep 1468925 = 550847) (by norm_num)
theorem B977429 : Blo 650305 977429 := bbase (se 6 (by rfl) ⟨22908, by rfl⟩ : syracuseStep 977429 = 45817) (by norm_num)
theorem B1174061 : Blo 650305 1174061 := bbase (se 3 (by rfl) ⟨220136, by rfl⟩ : syracuseStep 1174061 = 440273) (by norm_num)
theorem B977453 : Blo 650305 977453 := bbase (se 3 (by rfl) ⟨183272, by rfl⟩ : syracuseStep 977453 = 366545) (by norm_num)
theorem B879157 : Blo 650305 879157 := bbase (se 5 (by rfl) ⟨41210, by rfl⟩ : syracuseStep 879157 = 82421) (by norm_num)
theorem B3303989 : Blo 650305 3303989 := bbase (se 5 (by rfl) ⟨154874, by rfl⟩ : syracuseStep 3303989 = 309749) (by norm_num)
theorem B977477 : Blo 650305 977477 := bbase (se 4 (by rfl) ⟨91638, by rfl⟩ : syracuseStep 977477 = 183277) (by norm_num)
theorem B1468997 : Blo 650305 1468997 := bbase (se 4 (by rfl) ⟨137718, by rfl⟩ : syracuseStep 1468997 = 275437) (by norm_num)
theorem B2648645 : Blo 650305 2648645 := bbase (se 4 (by rfl) ⟨248310, by rfl⟩ : syracuseStep 2648645 = 496621) (by norm_num)
theorem B977501 : Blo 650305 977501 := bbase (se 3 (by rfl) ⟨183281, by rfl⟩ : syracuseStep 977501 = 366563) (by norm_num)
theorem B977525 : Blo 650305 977525 := bbase (se 5 (by rfl) ⟨45821, by rfl⟩ : syracuseStep 977525 = 91643) (by norm_num)
theorem B2091653 : Blo 650305 2091653 := bbase (se 4 (by rfl) ⟨196092, by rfl⟩ : syracuseStep 2091653 = 392185) (by norm_num)
theorem B977549 : Blo 650305 977549 := bbase (se 3 (by rfl) ⟨183290, by rfl⟩ : syracuseStep 977549 = 366581) (by norm_num)
theorem B1469069 : Blo 650305 1469069 := bbase (se 3 (by rfl) ⟨275450, by rfl⟩ : syracuseStep 1469069 = 550901) (by norm_num)
theorem B977573 : Blo 650305 977573 := bbase (se 4 (by rfl) ⟨91647, by rfl⟩ : syracuseStep 977573 = 183295) (by norm_num)
theorem B1239725 : Blo 650305 1239725 := bbase (se 3 (by rfl) ⟨232448, by rfl⟩ : syracuseStep 1239725 = 464897) (by norm_num)
theorem B977597 : Blo 650305 977597 := bbase (se 3 (by rfl) ⟨183299, by rfl⟩ : syracuseStep 977597 = 366599) (by norm_num)
theorem B977621 : Blo 650305 977621 := bbase (se 7 (by rfl) ⟨11456, by rfl⟩ : syracuseStep 977621 = 22913) (by norm_num)
theorem B1469141 : Blo 650305 1469141 := bbase (se 7 (by rfl) ⟨17216, by rfl⟩ : syracuseStep 1469141 = 34433) (by norm_num)
theorem B977645 : Blo 650305 977645 := bbase (se 3 (by rfl) ⟨183308, by rfl⟩ : syracuseStep 977645 = 366617) (by norm_num)
theorem B977669 : Blo 650305 977669 := bbase (se 4 (by rfl) ⟨91656, by rfl⟩ : syracuseStep 977669 = 183313) (by norm_num)
theorem B977693 : Blo 650305 977693 := bbase (se 3 (by rfl) ⟨183317, by rfl⟩ : syracuseStep 977693 = 366635) (by norm_num)
theorem B1469213 : Blo 650305 1469213 := bbase (se 3 (by rfl) ⟨275477, by rfl⟩ : syracuseStep 1469213 = 550955) (by norm_num)
theorem B977717 : Blo 650305 977717 := bbase (se 5 (by rfl) ⟨45830, by rfl⟩ : syracuseStep 977717 = 91661) (by norm_num)
theorem B879421 : Blo 650305 879421 := bbase (se 3 (by rfl) ⟨164891, by rfl⟩ : syracuseStep 879421 = 329783) (by norm_num)
theorem B1239877 : Blo 650305 1239877 := bbase (se 4 (by rfl) ⟨116238, by rfl⟩ : syracuseStep 1239877 = 232477) (by norm_num)
theorem B1174349 : Blo 650305 1174349 := bbase (se 3 (by rfl) ⟨220190, by rfl⟩ : syracuseStep 1174349 = 440381) (by norm_num)
theorem B977741 : Blo 650305 977741 := bbase (se 3 (by rfl) ⟨183326, by rfl⟩ : syracuseStep 977741 = 366653) (by norm_num)
theorem B977765 : Blo 650305 977765 := bbase (se 4 (by rfl) ⟨91665, by rfl⟩ : syracuseStep 977765 = 183331) (by norm_num)
theorem B1469285 : Blo 650305 1469285 := bbase (se 4 (by rfl) ⟨137745, by rfl⟩ : syracuseStep 1469285 = 275491) (by norm_num)
theorem B977789 : Blo 650305 977789 := bbase (se 3 (by rfl) ⟨183335, by rfl⟩ : syracuseStep 977789 = 366671) (by norm_num)
theorem B977813 : Blo 650305 977813 := bbase (se 6 (by rfl) ⟨22917, by rfl⟩ : syracuseStep 977813 = 45835) (by norm_num)
theorem B977837 : Blo 650305 977837 := bbase (se 3 (by rfl) ⟨183344, by rfl⟩ : syracuseStep 977837 = 366689) (by norm_num)
theorem B1469357 : Blo 650305 1469357 := bbase (se 3 (by rfl) ⟨275504, by rfl⟩ : syracuseStep 1469357 = 551009) (by norm_num)
theorem B977861 : Blo 650305 977861 := bbase (se 4 (by rfl) ⟨91674, by rfl⟩ : syracuseStep 977861 = 183349) (by norm_num)
theorem B977885 : Blo 650305 977885 := bbase (se 3 (by rfl) ⟨183353, by rfl⟩ : syracuseStep 977885 = 366707) (by norm_num)
theorem B977909 : Blo 650305 977909 := bbase (se 5 (by rfl) ⟨45839, by rfl⟩ : syracuseStep 977909 = 91679) (by norm_num)
theorem B1469429 : Blo 650305 1469429 := bbase (se 5 (by rfl) ⟨68879, by rfl⟩ : syracuseStep 1469429 = 137759) (by norm_num)
theorem B977933 : Blo 650305 977933 := bbase (se 3 (by rfl) ⟨183362, by rfl⟩ : syracuseStep 977933 = 366725) (by norm_num)
theorem B977957 : Blo 650305 977957 := bbase (se 4 (by rfl) ⟨91683, by rfl⟩ : syracuseStep 977957 = 183367) (by norm_num)
theorem B977981 : Blo 650305 977981 := bbase (se 3 (by rfl) ⟨183371, by rfl⟩ : syracuseStep 977981 = 366743) (by norm_num)
theorem B1469501 : Blo 650305 1469501 := bbase (se 3 (by rfl) ⟨275531, by rfl⟩ : syracuseStep 1469501 = 551063) (by norm_num)
theorem B1043533 : Blo 650305 1043533 := bbase (se 3 (by rfl) ⟨195662, by rfl⟩ : syracuseStep 1043533 = 391325) (by norm_num)
theorem B978005 : Blo 650305 978005 := bbase (se 8 (by rfl) ⟨5730, by rfl⟩ : syracuseStep 978005 = 11461) (by norm_num)
theorem B978029 : Blo 650305 978029 := bbase (se 3 (by rfl) ⟨183380, by rfl⟩ : syracuseStep 978029 = 366761) (by norm_num)
theorem B1240181 : Blo 650305 1240181 := bbase (se 5 (by rfl) ⟨58133, by rfl⟩ : syracuseStep 1240181 = 116267) (by norm_num)
theorem B978053 : Blo 650305 978053 := bbase (se 4 (by rfl) ⟨91692, by rfl⟩ : syracuseStep 978053 = 183385) (by norm_num)
theorem B1469573 : Blo 650305 1469573 := bbase (se 4 (by rfl) ⟨137772, by rfl⟩ : syracuseStep 1469573 = 275545) (by norm_num)
theorem B978077 : Blo 650305 978077 := bbase (se 3 (by rfl) ⟨183389, by rfl⟩ : syracuseStep 978077 = 366779) (by norm_num)
theorem B978101 : Blo 650305 978101 := bbase (se 5 (by rfl) ⟨45848, by rfl⟩ : syracuseStep 978101 = 91697) (by norm_num)
theorem B978125 : Blo 650305 978125 := bbase (se 3 (by rfl) ⟨183398, by rfl⟩ : syracuseStep 978125 = 366797) (by norm_num)
theorem B1469645 : Blo 650305 1469645 := bbase (se 3 (by rfl) ⟨275558, by rfl⟩ : syracuseStep 1469645 = 551117) (by norm_num)
theorem B978149 : Blo 650305 978149 := bbase (se 4 (by rfl) ⟨91701, by rfl⟩ : syracuseStep 978149 = 183403) (by norm_num)
theorem B978173 : Blo 650305 978173 := bbase (se 3 (by rfl) ⟨183407, by rfl⟩ : syracuseStep 978173 = 366815) (by norm_num)
theorem B978197 : Blo 650305 978197 := bbase (se 6 (by rfl) ⟨22926, by rfl⟩ : syracuseStep 978197 = 45853) (by norm_num)
theorem B1764629 : Blo 650305 1764629 := bbase (se 6 (by rfl) ⟨41358, by rfl⟩ : syracuseStep 1764629 = 82717) (by norm_num)
theorem B1469717 : Blo 650305 1469717 := bbase (se 6 (by rfl) ⟨34446, by rfl⟩ : syracuseStep 1469717 = 68893) (by norm_num)
theorem B3534101 : Blo 650305 3534101 := bbase (se 6 (by rfl) ⟨82830, by rfl⟩ : syracuseStep 3534101 = 165661) (by norm_num)
theorem B978221 : Blo 650305 978221 := bbase (se 3 (by rfl) ⟨183416, by rfl⟩ : syracuseStep 978221 = 366833) (by norm_num)
theorem B978245 : Blo 650305 978245 := bbase (se 4 (by rfl) ⟨91710, by rfl⟩ : syracuseStep 978245 = 183421) (by norm_num)
theorem B978269 : Blo 650305 978269 := bbase (se 3 (by rfl) ⟨183425, by rfl⟩ : syracuseStep 978269 = 366851) (by norm_num)
theorem B1469789 : Blo 650305 1469789 := bbase (se 3 (by rfl) ⟨275585, by rfl⟩ : syracuseStep 1469789 = 551171) (by norm_num)
theorem B781669 : Blo 650305 781669 := bbase (se 4 (by rfl) ⟨73281, by rfl⟩ : syracuseStep 781669 = 146563) (by norm_num)
theorem B716149 : Blo 650305 716149 := bbase (se 5 (by rfl) ⟨33569, by rfl⟩ : syracuseStep 716149 = 67139) (by norm_num)
theorem B978293 : Blo 650305 978293 := bbase (se 5 (by rfl) ⟨45857, by rfl⟩ : syracuseStep 978293 = 91715) (by norm_num)
theorem B978317 : Blo 650305 978317 := bbase (se 3 (by rfl) ⟨183434, by rfl⟩ : syracuseStep 978317 = 366869) (by norm_num)
theorem B978341 : Blo 650305 978341 := bbase (se 4 (by rfl) ⟨91719, by rfl⟩ : syracuseStep 978341 = 183439) (by norm_num)
theorem B1469861 : Blo 650305 1469861 := bbase (se 4 (by rfl) ⟨137799, by rfl⟩ : syracuseStep 1469861 = 275599) (by norm_num)
theorem B978365 : Blo 650305 978365 := bbase (se 3 (by rfl) ⟨183443, by rfl⟩ : syracuseStep 978365 = 366887) (by norm_num)
theorem B978389 : Blo 650305 978389 := bbase (se 7 (by rfl) ⟨11465, by rfl⟩ : syracuseStep 978389 = 22931) (by norm_num)
theorem B978413 : Blo 650305 978413 := bbase (se 3 (by rfl) ⟨183452, by rfl⟩ : syracuseStep 978413 = 366905) (by norm_num)
theorem B1469933 : Blo 650305 1469933 := bbase (se 3 (by rfl) ⟨275612, by rfl⟩ : syracuseStep 1469933 = 551225) (by norm_num)
theorem B2092549 : Blo 650305 2092549 := bbase (se 4 (by rfl) ⟨196176, by rfl⟩ : syracuseStep 2092549 = 392353) (by norm_num)
theorem B978437 : Blo 650305 978437 := bbase (se 4 (by rfl) ⟨91728, by rfl⟩ : syracuseStep 978437 = 183457) (by norm_num)
theorem B978461 : Blo 650305 978461 := bbase (se 3 (by rfl) ⟨183461, by rfl⟩ : syracuseStep 978461 = 366923) (by norm_num)
theorem B978485 : Blo 650305 978485 := bbase (se 5 (by rfl) ⟨45866, by rfl⟩ : syracuseStep 978485 = 91733) (by norm_num)
theorem B1470005 : Blo 650305 1470005 := bbase (se 5 (by rfl) ⟨68906, by rfl⟩ : syracuseStep 1470005 = 137813) (by norm_num)
theorem B978509 : Blo 650305 978509 := bbase (se 3 (by rfl) ⟨183470, by rfl⟩ : syracuseStep 978509 = 366941) (by norm_num)
theorem B978533 : Blo 650305 978533 := bbase (se 4 (by rfl) ⟨91737, by rfl⟩ : syracuseStep 978533 = 183475) (by norm_num)
theorem B978557 : Blo 650305 978557 := bbase (se 3 (by rfl) ⟨183479, by rfl⟩ : syracuseStep 978557 = 366959) (by norm_num)
theorem B1470077 : Blo 650305 1470077 := bbase (se 3 (by rfl) ⟨275639, by rfl⟩ : syracuseStep 1470077 = 551279) (by norm_num)
theorem B978581 : Blo 650305 978581 := bbase (se 6 (by rfl) ⟨22935, by rfl⟩ : syracuseStep 978581 = 45871) (by norm_num)
theorem B1568413 : Blo 650305 1568413 := bbase (se 3 (by rfl) ⟨294077, by rfl⟩ : syracuseStep 1568413 = 588155) (by norm_num)
theorem B978605 : Blo 650305 978605 := bbase (se 3 (by rfl) ⟨183488, by rfl⟩ : syracuseStep 978605 = 366977) (by norm_num)
theorem B978629 : Blo 650305 978629 := bbase (se 4 (by rfl) ⟨91746, by rfl⟩ : syracuseStep 978629 = 183493) (by norm_num)
theorem B1470149 : Blo 650305 1470149 := bbase (se 4 (by rfl) ⟨137826, by rfl⟩ : syracuseStep 1470149 = 275653) (by norm_num)
theorem B978653 : Blo 650305 978653 := bbase (se 3 (by rfl) ⟨183497, by rfl⟩ : syracuseStep 978653 = 366995) (by norm_num)
theorem B978677 : Blo 650305 978677 := bbase (se 5 (by rfl) ⟨45875, by rfl⟩ : syracuseStep 978677 = 91751) (by norm_num)
theorem B978701 : Blo 650305 978701 := bbase (se 3 (by rfl) ⟨183506, by rfl⟩ : syracuseStep 978701 = 367013) (by norm_num)
theorem B1470221 : Blo 650305 1470221 := bbase (se 3 (by rfl) ⟨275666, by rfl⟩ : syracuseStep 1470221 = 551333) (by norm_num)
theorem B978725 : Blo 650305 978725 := bbase (se 4 (by rfl) ⟨91755, by rfl⟩ : syracuseStep 978725 = 183511) (by norm_num)
theorem B978749 : Blo 650305 978749 := bbase (se 3 (by rfl) ⟨183515, by rfl⟩ : syracuseStep 978749 = 367031) (by norm_num)
theorem B3305285 : Blo 650305 3305285 := bbase (se 4 (by rfl) ⟨309870, by rfl⟩ : syracuseStep 3305285 = 619741) (by norm_num)
theorem B978773 : Blo 650305 978773 := bbase (se 9 (by rfl) ⟨2867, by rfl⟩ : syracuseStep 978773 = 5735) (by norm_num)
theorem B1470293 : Blo 650305 1470293 := bbase (se 9 (by rfl) ⟨4307, by rfl⟩ : syracuseStep 1470293 = 8615) (by norm_num)
theorem B2649941 : Blo 650305 2649941 := bbase (se 9 (by rfl) ⟨7763, by rfl⟩ : syracuseStep 2649941 = 15527) (by norm_num)
theorem B1240933 : Blo 650305 1240933 := bbase (se 4 (by rfl) ⟨116337, by rfl⟩ : syracuseStep 1240933 = 232675) (by norm_num)
theorem B978797 : Blo 650305 978797 := bbase (se 3 (by rfl) ⟨183524, by rfl⟩ : syracuseStep 978797 = 367049) (by norm_num)
theorem B978821 : Blo 650305 978821 := bbase (se 4 (by rfl) ⟨91764, by rfl⟩ : syracuseStep 978821 = 183529) (by norm_num)
theorem B2092949 : Blo 650305 2092949 := bbase (se 6 (by rfl) ⟨49053, by rfl⟩ : syracuseStep 2092949 = 98107) (by norm_num)
theorem B978845 : Blo 650305 978845 := bbase (se 3 (by rfl) ⟨183533, by rfl⟩ : syracuseStep 978845 = 367067) (by norm_num)
theorem B1470365 : Blo 650305 1470365 := bbase (se 3 (by rfl) ⟨275693, by rfl⟩ : syracuseStep 1470365 = 551387) (by norm_num)
theorem B978869 : Blo 650305 978869 := bbase (se 5 (by rfl) ⟨45884, by rfl⟩ : syracuseStep 978869 = 91769) (by norm_num)
theorem B978893 : Blo 650305 978893 := bbase (se 3 (by rfl) ⟨183542, by rfl⟩ : syracuseStep 978893 = 367085) (by norm_num)
theorem B978917 : Blo 650305 978917 := bbase (se 4 (by rfl) ⟨91773, by rfl⟩ : syracuseStep 978917 = 183547) (by norm_num)
theorem B1470437 : Blo 650305 1470437 := bbase (se 4 (by rfl) ⟨137853, by rfl⟩ : syracuseStep 1470437 = 275707) (by norm_num)
theorem B1241077 : Blo 650305 1241077 := bbase (se 5 (by rfl) ⟨58175, by rfl⟩ : syracuseStep 1241077 = 116351) (by norm_num)
theorem B978941 : Blo 650305 978941 := bbase (se 3 (by rfl) ⟨183551, by rfl⟩ : syracuseStep 978941 = 367103) (by norm_num)
theorem B978965 : Blo 650305 978965 := bbase (se 6 (by rfl) ⟨22944, by rfl⟩ : syracuseStep 978965 = 45889) (by norm_num)
theorem B2977829 : Blo 650305 2977829 := bbase (se 4 (by rfl) ⟨279171, by rfl⟩ : syracuseStep 2977829 = 558343) (by norm_num)
theorem B978989 : Blo 650305 978989 := bbase (se 3 (by rfl) ⟨183560, by rfl⟩ : syracuseStep 978989 = 367121) (by norm_num)
theorem B1470509 : Blo 650305 1470509 := bbase (se 3 (by rfl) ⟨275720, by rfl⟩ : syracuseStep 1470509 = 551441) (by norm_num)
theorem B979013 : Blo 650305 979013 := bbase (se 4 (by rfl) ⟨91782, by rfl⟩ : syracuseStep 979013 = 183565) (by norm_num)
theorem B979037 : Blo 650305 979037 := bbase (se 3 (by rfl) ⟨183569, by rfl⟩ : syracuseStep 979037 = 367139) (by norm_num)
theorem B979061 : Blo 650305 979061 := bbase (se 5 (by rfl) ⟨45893, by rfl⟩ : syracuseStep 979061 = 91787) (by norm_num)
theorem B1470581 : Blo 650305 1470581 := bbase (se 5 (by rfl) ⟨68933, by rfl⟩ : syracuseStep 1470581 = 137867) (by norm_num)
theorem B2781317 : Blo 650305 2781317 := bbase (se 4 (by rfl) ⟨260748, by rfl⟩ : syracuseStep 2781317 = 521497) (by norm_num)
theorem B979085 : Blo 650305 979085 := bbase (se 3 (by rfl) ⟨183578, by rfl⟩ : syracuseStep 979085 = 367157) (by norm_num)
theorem B1241237 : Blo 650305 1241237 := bbase (se 6 (by rfl) ⟨29091, by rfl⟩ : syracuseStep 1241237 = 58183) (by norm_num)
theorem B880805 : Blo 650305 880805 := bbase (se 4 (by rfl) ⟨82575, by rfl⟩ : syracuseStep 880805 = 165151) (by norm_num)
theorem B979109 : Blo 650305 979109 := bbase (se 4 (by rfl) ⟨91791, by rfl⟩ : syracuseStep 979109 = 183583) (by norm_num)
theorem B979133 : Blo 650305 979133 := bbase (se 3 (by rfl) ⟨183587, by rfl⟩ : syracuseStep 979133 = 367175) (by norm_num)
theorem B1470653 : Blo 650305 1470653 := bbase (se 3 (by rfl) ⟨275747, by rfl⟩ : syracuseStep 1470653 = 551495) (by norm_num)
theorem B1241285 : Blo 650305 1241285 := bbase (se 4 (by rfl) ⟨116370, by rfl⟩ : syracuseStep 1241285 = 232741) (by norm_num)
theorem B979157 : Blo 650305 979157 := bbase (se 7 (by rfl) ⟨11474, by rfl⟩ : syracuseStep 979157 = 22949) (by norm_num)
theorem B979181 : Blo 650305 979181 := bbase (se 3 (by rfl) ⟨183596, by rfl⟩ : syracuseStep 979181 = 367193) (by norm_num)
theorem B979205 : Blo 650305 979205 := bbase (se 4 (by rfl) ⟨91800, by rfl⟩ : syracuseStep 979205 = 183601) (by norm_num)
theorem B1470725 : Blo 650305 1470725 := bbase (se 4 (by rfl) ⟨137880, by rfl⟩ : syracuseStep 1470725 = 275761) (by norm_num)
theorem B979229 : Blo 650305 979229 := bbase (se 3 (by rfl) ⟨183605, by rfl⟩ : syracuseStep 979229 = 367211) (by norm_num)
theorem B1241381 : Blo 650305 1241381 := bbase (se 4 (by rfl) ⟨116379, by rfl⟩ : syracuseStep 1241381 = 232759) (by norm_num)
theorem B979253 : Blo 650305 979253 := bbase (se 5 (by rfl) ⟨45902, by rfl⟩ : syracuseStep 979253 = 91805) (by norm_num)
theorem B880957 : Blo 650305 880957 := bbase (se 3 (by rfl) ⟨165179, by rfl⟩ : syracuseStep 880957 = 330359) (by norm_num)
theorem B782669 : Blo 650305 782669 := bbase (se 3 (by rfl) ⟨146750, by rfl⟩ : syracuseStep 782669 = 293501) (by norm_num)
theorem B979277 : Blo 650305 979277 := bbase (se 3 (by rfl) ⟨183614, by rfl⟩ : syracuseStep 979277 = 367229) (by norm_num)
theorem B1470797 : Blo 650305 1470797 := bbase (se 3 (by rfl) ⟨275774, by rfl⟩ : syracuseStep 1470797 = 551549) (by norm_num)
theorem B5566805 : Blo 650305 5566805 := bbase (se 10 (by rfl) ⟨8154, by rfl⟩ : syracuseStep 5566805 = 16309) (by norm_num)
theorem B979301 : Blo 650305 979301 := bbase (se 4 (by rfl) ⟨91809, by rfl⟩ : syracuseStep 979301 = 183619) (by norm_num)
theorem B979325 : Blo 650305 979325 := bbase (se 3 (by rfl) ⟨183623, by rfl⟩ : syracuseStep 979325 = 367247) (by norm_num)
theorem B782741 : Blo 650305 782741 := bbase (se 6 (by rfl) ⟨18345, by rfl⟩ : syracuseStep 782741 = 36691) (by norm_num)
theorem B979349 : Blo 650305 979349 := bbase (se 6 (by rfl) ⟨22953, by rfl⟩ : syracuseStep 979349 = 45907) (by norm_num)
theorem B2355605 : Blo 650305 2355605 := bbase (se 6 (by rfl) ⟨55209, by rfl⟩ : syracuseStep 2355605 = 110419) (by norm_num)
theorem B1470869 : Blo 650305 1470869 := bbase (se 6 (by rfl) ⟨34473, by rfl⟩ : syracuseStep 1470869 = 68947) (by norm_num)
theorem B979373 : Blo 650305 979373 := bbase (se 3 (by rfl) ⟨183632, by rfl⟩ : syracuseStep 979373 = 367265) (by norm_num)
theorem B1044917 : Blo 650305 1044917 := bbase (se 5 (by rfl) ⟨48980, by rfl⟩ : syracuseStep 1044917 = 97961) (by norm_num)
theorem B979397 : Blo 650305 979397 := bbase (se 4 (by rfl) ⟨91818, by rfl⟩ : syracuseStep 979397 = 183637) (by norm_num)
theorem B979421 : Blo 650305 979421 := bbase (se 3 (by rfl) ⟨183641, by rfl⟩ : syracuseStep 979421 = 367283) (by norm_num)
theorem B1470941 : Blo 650305 1470941 := bbase (se 3 (by rfl) ⟨275801, by rfl⟩ : syracuseStep 1470941 = 551603) (by norm_num)
theorem B979445 : Blo 650305 979445 := bbase (se 5 (by rfl) ⟨45911, by rfl⟩ : syracuseStep 979445 = 91823) (by norm_num)
theorem B979469 : Blo 650305 979469 := bbase (se 3 (by rfl) ⟨183650, by rfl⟩ : syracuseStep 979469 = 367301) (by norm_num)
theorem B2355733 : Blo 650305 2355733 := bbase (se 6 (by rfl) ⟨55212, by rfl⟩ : syracuseStep 2355733 = 110425) (by norm_num)
theorem B979493 : Blo 650305 979493 := bbase (se 4 (by rfl) ⟨91827, by rfl⟩ : syracuseStep 979493 = 183655) (by norm_num)
theorem B1471013 : Blo 650305 1471013 := bbase (se 4 (by rfl) ⟨137907, by rfl⟩ : syracuseStep 1471013 = 275815) (by norm_num)
theorem B979517 : Blo 650305 979517 := bbase (se 3 (by rfl) ⟨183659, by rfl⟩ : syracuseStep 979517 = 367319) (by norm_num)
theorem B1241669 : Blo 650305 1241669 := bbase (se 4 (by rfl) ⟨116406, by rfl⟩ : syracuseStep 1241669 = 232813) (by norm_num)
theorem B979541 : Blo 650305 979541 := bbase (se 8 (by rfl) ⟨5739, by rfl⟩ : syracuseStep 979541 = 11479) (by norm_num)
theorem B979565 : Blo 650305 979565 := bbase (se 3 (by rfl) ⟨183668, by rfl⟩ : syracuseStep 979565 = 367337) (by norm_num)
theorem B1471085 : Blo 650305 1471085 := bbase (se 3 (by rfl) ⟨275828, by rfl⟩ : syracuseStep 1471085 = 551657) (by norm_num)
theorem B1045109 : Blo 650305 1045109 := bbase (se 5 (by rfl) ⟨48989, by rfl⟩ : syracuseStep 1045109 = 97979) (by norm_num)
theorem B979589 : Blo 650305 979589 := bbase (se 4 (by rfl) ⟨91836, by rfl⟩ : syracuseStep 979589 = 183673) (by norm_num)
theorem B1503893 : Blo 650305 1503893 := bbase (se 6 (by rfl) ⟨35247, by rfl⟩ : syracuseStep 1503893 = 70495) (by norm_num)
theorem B979613 : Blo 650305 979613 := bbase (se 3 (by rfl) ⟨183677, by rfl⟩ : syracuseStep 979613 = 367355) (by norm_num)
theorem B979637 : Blo 650305 979637 := bbase (se 5 (by rfl) ⟨45920, by rfl⟩ : syracuseStep 979637 = 91841) (by norm_num)
theorem B1471157 : Blo 650305 1471157 := bbase (se 5 (by rfl) ⟨68960, by rfl⟩ : syracuseStep 1471157 = 137921) (by norm_num)
theorem B783049 : Blo 650305 783049 := bbase (se 2 (by rfl) ⟨293643, by rfl⟩ : syracuseStep 783049 = 587287) (by norm_num)
theorem B979661 : Blo 650305 979661 := bbase (se 3 (by rfl) ⟨183686, by rfl⟩ : syracuseStep 979661 = 367373) (by norm_num)
theorem B1241821 : Blo 650305 1241821 := bbase (se 3 (by rfl) ⟨232841, by rfl⟩ : syracuseStep 1241821 = 465683) (by norm_num)
theorem B979685 : Blo 650305 979685 := bbase (se 4 (by rfl) ⟨91845, by rfl⟩ : syracuseStep 979685 = 183691) (by norm_num)
theorem B979709 : Blo 650305 979709 := bbase (se 3 (by rfl) ⟨183695, by rfl⟩ : syracuseStep 979709 = 367391) (by norm_num)
theorem B1471229 : Blo 650305 1471229 := bbase (se 3 (by rfl) ⟨275855, by rfl⟩ : syracuseStep 1471229 = 551711) (by norm_num)
theorem B979733 : Blo 650305 979733 := bbase (se 6 (by rfl) ⟨22962, by rfl⟩ : syracuseStep 979733 = 45925) (by norm_num)
theorem B979757 : Blo 650305 979757 := bbase (se 3 (by rfl) ⟨183704, by rfl⟩ : syracuseStep 979757 = 367409) (by norm_num)
theorem B979781 : Blo 650305 979781 := bbase (se 4 (by rfl) ⟨91854, by rfl⟩ : syracuseStep 979781 = 183709) (by norm_num)
theorem B1471301 : Blo 650305 1471301 := bbase (se 4 (by rfl) ⟨137934, by rfl⟩ : syracuseStep 1471301 = 275869) (by norm_num)
theorem B979805 : Blo 650305 979805 := bbase (se 3 (by rfl) ⟨183713, by rfl⟩ : syracuseStep 979805 = 367427) (by norm_num)
theorem B783217 : Blo 650305 783217 := bbase (se 2 (by rfl) ⟨293706, by rfl⟩ : syracuseStep 783217 = 587413) (by norm_num)
theorem B979829 : Blo 650305 979829 := bbase (se 5 (by rfl) ⟨45929, by rfl⟩ : syracuseStep 979829 = 91859) (by norm_num)
theorem B979853 : Blo 650305 979853 := bbase (se 3 (by rfl) ⟨183722, by rfl⟩ : syracuseStep 979853 = 367445) (by norm_num)
theorem B1471373 : Blo 650305 1471373 := bbase (se 3 (by rfl) ⟨275882, by rfl⟩ : syracuseStep 1471373 = 551765) (by norm_num)
theorem B783265 : Blo 650305 783265 := bbase (se 2 (by rfl) ⟨293724, by rfl⟩ : syracuseStep 783265 = 587449) (by norm_num)
theorem B979877 : Blo 650305 979877 := bbase (se 4 (by rfl) ⟨91863, by rfl⟩ : syracuseStep 979877 = 183727) (by norm_num)
theorem B979901 : Blo 650305 979901 := bbase (se 3 (by rfl) ⟨183731, by rfl⟩ : syracuseStep 979901 = 367463) (by norm_num)
theorem B979925 : Blo 650305 979925 := bbase (se 7 (by rfl) ⟨11483, by rfl⟩ : syracuseStep 979925 = 22967) (by norm_num)
theorem B1471445 : Blo 650305 1471445 := bbase (se 7 (by rfl) ⟨17243, by rfl⟩ : syracuseStep 1471445 = 34487) (by norm_num)
theorem B979949 : Blo 650305 979949 := bbase (se 3 (by rfl) ⟨183740, by rfl⟩ : syracuseStep 979949 = 367481) (by norm_num)
theorem B783361 : Blo 650305 783361 := bbase (se 2 (by rfl) ⟨293760, by rfl⟩ : syracuseStep 783361 = 587521) (by norm_num)
theorem B979973 : Blo 650305 979973 := bbase (se 4 (by rfl) ⟨91872, by rfl⟩ : syracuseStep 979973 = 183745) (by norm_num)
theorem B1569797 : Blo 650305 1569797 := bbase (se 4 (by rfl) ⟨147168, by rfl⟩ : syracuseStep 1569797 = 294337) (by norm_num)
theorem B1242125 : Blo 650305 1242125 := bbase (se 3 (by rfl) ⟨232898, by rfl⟩ : syracuseStep 1242125 = 465797) (by norm_num)
theorem B979997 : Blo 650305 979997 := bbase (se 3 (by rfl) ⟨183749, by rfl⟩ : syracuseStep 979997 = 367499) (by norm_num)
theorem B1471517 : Blo 650305 1471517 := bbase (se 3 (by rfl) ⟨275909, by rfl⟩ : syracuseStep 1471517 = 551819) (by norm_num)
theorem B980021 : Blo 650305 980021 := bbase (se 5 (by rfl) ⟨45938, by rfl⟩ : syracuseStep 980021 = 91877) (by norm_num)
theorem B3142709 : Blo 650305 3142709 := bbase (se 5 (by rfl) ⟨147314, by rfl⟩ : syracuseStep 3142709 = 294629) (by norm_num)
theorem B980045 : Blo 650305 980045 := bbase (se 3 (by rfl) ⟨183758, by rfl⟩ : syracuseStep 980045 = 367517) (by norm_num)
theorem B3306581 : Blo 650305 3306581 := bbase (se 8 (by rfl) ⟨19374, by rfl⟩ : syracuseStep 3306581 = 38749) (by norm_num)
theorem B2782309 : Blo 650305 2782309 := bbase (se 4 (by rfl) ⟨260841, by rfl⟩ : syracuseStep 2782309 = 521683) (by norm_num)
theorem B980069 : Blo 650305 980069 := bbase (se 4 (by rfl) ⟨91881, by rfl⟩ : syracuseStep 980069 = 183763) (by norm_num)
theorem B1471589 : Blo 650305 1471589 := bbase (se 4 (by rfl) ⟨137961, by rfl⟩ : syracuseStep 1471589 = 275923) (by norm_num)
theorem B980093 : Blo 650305 980093 := bbase (se 3 (by rfl) ⟨183767, by rfl⟩ : syracuseStep 980093 = 367535) (by norm_num)
theorem B980117 : Blo 650305 980117 := bbase (se 6 (by rfl) ⟨22971, by rfl⟩ : syracuseStep 980117 = 45943) (by norm_num)
theorem B3536021 : Blo 650305 3536021 := bbase (se 6 (by rfl) ⟨82875, by rfl⟩ : syracuseStep 3536021 = 165751) (by norm_num)
theorem B980141 : Blo 650305 980141 := bbase (se 3 (by rfl) ⟨183776, by rfl⟩ : syracuseStep 980141 = 367553) (by norm_num)
theorem B1471661 : Blo 650305 1471661 := bbase (se 3 (by rfl) ⟨275936, by rfl⟩ : syracuseStep 1471661 = 551873) (by norm_num)
theorem B1569989 : Blo 650305 1569989 := bbase (se 4 (by rfl) ⟨147186, by rfl⟩ : syracuseStep 1569989 = 294373) (by norm_num)
theorem B980165 : Blo 650305 980165 := bbase (se 4 (by rfl) ⟨91890, by rfl⟩ : syracuseStep 980165 = 183781) (by norm_num)
theorem B980189 : Blo 650305 980189 := bbase (se 3 (by rfl) ⟨183785, by rfl⟩ : syracuseStep 980189 = 367571) (by norm_num)
theorem B980213 : Blo 650305 980213 := bbase (se 5 (by rfl) ⟨45947, by rfl⟩ : syracuseStep 980213 = 91895) (by norm_num)
theorem B3142901 : Blo 650305 3142901 := bbase (se 5 (by rfl) ⟨147323, by rfl⟩ : syracuseStep 3142901 = 294647) (by norm_num)
theorem B1471733 : Blo 650305 1471733 := bbase (se 5 (by rfl) ⟨68987, by rfl⟩ : syracuseStep 1471733 = 137975) (by norm_num)
theorem B980237 : Blo 650305 980237 := bbase (se 3 (by rfl) ⟨183794, by rfl⟩ : syracuseStep 980237 = 367589) (by norm_num)
theorem B980261 : Blo 650305 980261 := bbase (se 4 (by rfl) ⟨91899, by rfl⟩ : syracuseStep 980261 = 183799) (by norm_num)
theorem B980285 : Blo 650305 980285 := bbase (se 3 (by rfl) ⟨183803, by rfl⟩ : syracuseStep 980285 = 367607) (by norm_num)
theorem B1471805 : Blo 650305 1471805 := bbase (se 3 (by rfl) ⟨275963, by rfl⟩ : syracuseStep 1471805 = 551927) (by norm_num)
theorem B980309 : Blo 650305 980309 := bbase (se 13 (by rfl) ⟨179, by rfl⟩ : syracuseStep 980309 = 359) (by norm_num)
theorem B980333 : Blo 650305 980333 := bbase (se 3 (by rfl) ⟨183812, by rfl⟩ : syracuseStep 980333 = 367625) (by norm_num)
theorem B980357 : Blo 650305 980357 := bbase (se 4 (by rfl) ⟨91908, by rfl⟩ : syracuseStep 980357 = 183817) (by norm_num)
theorem B1471877 : Blo 650305 1471877 := bbase (se 4 (by rfl) ⟨137988, by rfl⟩ : syracuseStep 1471877 = 275977) (by norm_num)
theorem B980381 : Blo 650305 980381 := bbase (se 3 (by rfl) ⟨183821, by rfl⟩ : syracuseStep 980381 = 367643) (by norm_num)
theorem B980405 : Blo 650305 980405 := bbase (se 5 (by rfl) ⟨45956, by rfl⟩ : syracuseStep 980405 = 91913) (by norm_num)
theorem B980429 : Blo 650305 980429 := bbase (se 3 (by rfl) ⟨183830, by rfl⟩ : syracuseStep 980429 = 367661) (by norm_num)
theorem B1471949 : Blo 650305 1471949 := bbase (se 3 (by rfl) ⟨275990, by rfl⟩ : syracuseStep 1471949 = 551981) (by norm_num)
theorem B980453 : Blo 650305 980453 := bbase (se 4 (by rfl) ⟨91917, by rfl⟩ : syracuseStep 980453 = 183835) (by norm_num)
theorem B980477 : Blo 650305 980477 := bbase (se 3 (by rfl) ⟨183839, by rfl⟩ : syracuseStep 980477 = 367679) (by norm_num)
theorem B980501 : Blo 650305 980501 := bbase (se 6 (by rfl) ⟨22980, by rfl⟩ : syracuseStep 980501 = 45961) (by norm_num)
theorem B1472021 : Blo 650305 1472021 := bbase (se 6 (by rfl) ⟨34500, by rfl⟩ : syracuseStep 1472021 = 69001) (by norm_num)
theorem B980525 : Blo 650305 980525 := bbase (se 3 (by rfl) ⟨183848, by rfl⟩ : syracuseStep 980525 = 367697) (by norm_num)
theorem B783937 : Blo 650305 783937 := bbase (se 2 (by rfl) ⟨293976, by rfl⟩ : syracuseStep 783937 = 587953) (by norm_num)
theorem B980549 : Blo 650305 980549 := bbase (se 4 (by rfl) ⟨91926, by rfl⟩ : syracuseStep 980549 = 183853) (by norm_num)
theorem B980573 : Blo 650305 980573 := bbase (se 3 (by rfl) ⟨183857, by rfl⟩ : syracuseStep 980573 = 367715) (by norm_num)
theorem B1472093 : Blo 650305 1472093 := bbase (se 3 (by rfl) ⟨276017, by rfl⟩ : syracuseStep 1472093 = 552035) (by norm_num)
theorem B980597 : Blo 650305 980597 := bbase (se 5 (by rfl) ⟨45965, by rfl⟩ : syracuseStep 980597 = 91931) (by norm_num)
theorem B3143285 : Blo 650305 3143285 := bbase (se 5 (by rfl) ⟨147341, by rfl⟩ : syracuseStep 3143285 = 294683) (by norm_num)
theorem B980621 : Blo 650305 980621 := bbase (se 3 (by rfl) ⟨183866, by rfl⟩ : syracuseStep 980621 = 367733) (by norm_num)
theorem B6256277 : Blo 650305 6256277 := bbase (se 6 (by rfl) ⟨146631, by rfl⟩ : syracuseStep 6256277 = 293263) (by norm_num)
theorem B980645 : Blo 650305 980645 := bbase (se 4 (by rfl) ⟨91935, by rfl⟩ : syracuseStep 980645 = 183871) (by norm_num)
theorem B1472165 : Blo 650305 1472165 := bbase (se 4 (by rfl) ⟨138015, by rfl⟩ : syracuseStep 1472165 = 276031) (by norm_num)
theorem B980669 : Blo 650305 980669 := bbase (se 3 (by rfl) ⟨183875, by rfl⟩ : syracuseStep 980669 = 367751) (by norm_num)
theorem B980693 : Blo 650305 980693 := bbase (se 7 (by rfl) ⟨11492, by rfl⟩ : syracuseStep 980693 = 22985) (by norm_num)
theorem B980717 : Blo 650305 980717 := bbase (se 3 (by rfl) ⟨183884, by rfl⟩ : syracuseStep 980717 = 367769) (by norm_num)
theorem B980741 : Blo 650305 980741 := bbase (se 4 (by rfl) ⟨91944, by rfl⟩ : syracuseStep 980741 = 183889) (by norm_num)
theorem B980765 : Blo 650305 980765 := bbase (se 3 (by rfl) ⟨183893, by rfl⟩ : syracuseStep 980765 = 367787) (by norm_num)
theorem B980789 : Blo 650305 980789 := bbase (se 5 (by rfl) ⟨45974, by rfl⟩ : syracuseStep 980789 = 91949) (by norm_num)
theorem B849733 : Blo 650305 849733 := bbase (se 4 (by rfl) ⟨79662, by rfl⟩ : syracuseStep 849733 = 159325) (by norm_num)
theorem B980813 : Blo 650305 980813 := bbase (se 3 (by rfl) ⟨183902, by rfl⟩ : syracuseStep 980813 = 367805) (by norm_num)
theorem B980837 : Blo 650305 980837 := bbase (se 4 (by rfl) ⟨91953, by rfl⟩ : syracuseStep 980837 = 183907) (by norm_num)
theorem B980861 : Blo 650305 980861 := bbase (se 3 (by rfl) ⟨183911, by rfl⟩ : syracuseStep 980861 = 367823) (by norm_num)
theorem B980885 : Blo 650305 980885 := bbase (se 6 (by rfl) ⟨22989, by rfl⟩ : syracuseStep 980885 = 45979) (by norm_num)
theorem B1046429 : Blo 650305 1046429 := bbase (se 3 (by rfl) ⟨196205, by rfl⟩ : syracuseStep 1046429 = 392411) (by norm_num)
theorem B980909 : Blo 650305 980909 := bbase (se 3 (by rfl) ⟨183920, by rfl⟩ : syracuseStep 980909 = 367841) (by norm_num)
theorem B1341373 : Blo 650305 1341373 := bbase (se 3 (by rfl) ⟨251507, by rfl⟩ : syracuseStep 1341373 = 503015) (by norm_num)
theorem B980933 : Blo 650305 980933 := bbase (se 4 (by rfl) ⟨91962, by rfl⟩ : syracuseStep 980933 = 183925) (by norm_num)
theorem B980957 : Blo 650305 980957 := bbase (se 3 (by rfl) ⟨183929, by rfl⟩ : syracuseStep 980957 = 367859) (by norm_num)
theorem B980981 : Blo 650305 980981 := bbase (se 5 (by rfl) ⟨45983, by rfl⟩ : syracuseStep 980981 = 91967) (by norm_num)
theorem B1046525 : Blo 650305 1046525 := bbase (se 3 (by rfl) ⟨196223, by rfl⟩ : syracuseStep 1046525 = 392447) (by norm_num)
theorem B981005 : Blo 650305 981005 := bbase (se 3 (by rfl) ⟨183938, by rfl⟩ : syracuseStep 981005 = 367877) (by norm_num)
theorem B1046557 : Blo 650305 1046557 := bbase (se 3 (by rfl) ⟨196229, by rfl⟩ : syracuseStep 1046557 = 392459) (by norm_num)
theorem B981029 : Blo 650305 981029 := bbase (se 4 (by rfl) ⟨91971, by rfl⟩ : syracuseStep 981029 = 183943) (by norm_num)
theorem B4454453 : Blo 650305 4454453 := bbase (se 5 (by rfl) ⟨208802, by rfl⟩ : syracuseStep 4454453 = 417605) (by norm_num)
theorem B981053 : Blo 650305 981053 := bbase (se 3 (by rfl) ⟨183947, by rfl⟩ : syracuseStep 981053 = 367895) (by norm_num)
theorem B981077 : Blo 650305 981077 := bbase (se 8 (by rfl) ⟨5748, by rfl⟩ : syracuseStep 981077 = 11497) (by norm_num)
theorem B981101 : Blo 650305 981101 := bbase (se 3 (by rfl) ⟨183956, by rfl⟩ : syracuseStep 981101 = 367913) (by norm_num)
theorem B2652277 : Blo 650305 2652277 := bbase (se 5 (by rfl) ⟨124325, by rfl⟩ : syracuseStep 2652277 = 248651) (by norm_num)
theorem B981125 : Blo 650305 981125 := bbase (se 4 (by rfl) ⟨91980, by rfl⟩ : syracuseStep 981125 = 183961) (by norm_num)
theorem B981149 : Blo 650305 981149 := bbase (se 3 (by rfl) ⟨183965, by rfl⟩ : syracuseStep 981149 = 367931) (by norm_num)
theorem B981173 : Blo 650305 981173 := bbase (se 5 (by rfl) ⟨45992, by rfl⟩ : syracuseStep 981173 = 91985) (by norm_num)
theorem B981197 : Blo 650305 981197 := bbase (se 3 (by rfl) ⟨183974, by rfl⟩ : syracuseStep 981197 = 367949) (by norm_num)
theorem B981221 : Blo 650305 981221 := bbase (se 4 (by rfl) ⟨91989, by rfl⟩ : syracuseStep 981221 = 183979) (by norm_num)
theorem B981245 : Blo 650305 981245 := bbase (se 3 (by rfl) ⟨183983, by rfl⟩ : syracuseStep 981245 = 367967) (by norm_num)
theorem B981269 : Blo 650305 981269 := bbase (se 6 (by rfl) ⟨22998, by rfl⟩ : syracuseStep 981269 = 45997) (by norm_num)
theorem B981293 : Blo 650305 981293 := bbase (se 3 (by rfl) ⟨183992, by rfl⟩ : syracuseStep 981293 = 367985) (by norm_num)
theorem B981317 : Blo 650305 981317 := bbase (se 4 (by rfl) ⟨91998, by rfl⟩ : syracuseStep 981317 = 183997) (by norm_num)
theorem B981341 : Blo 650305 981341 := bbase (se 3 (by rfl) ⟨184001, by rfl⟩ : syracuseStep 981341 = 368003) (by norm_num)
theorem B3307877 : Blo 650305 3307877 := bbase (se 4 (by rfl) ⟨310113, by rfl⟩ : syracuseStep 3307877 = 620227) (by norm_num)
theorem B981365 : Blo 650305 981365 := bbase (se 5 (by rfl) ⟨46001, by rfl⟩ : syracuseStep 981365 = 92003) (by norm_num)
theorem B981389 : Blo 650305 981389 := bbase (se 3 (by rfl) ⟨184010, by rfl⟩ : syracuseStep 981389 = 368021) (by norm_num)
theorem B3340693 : Blo 650305 3340693 := bbase (se 6 (by rfl) ⟨78297, by rfl⟩ : syracuseStep 3340693 = 156595) (by norm_num)
theorem B981413 : Blo 650305 981413 := bbase (se 4 (by rfl) ⟨92007, by rfl⟩ : syracuseStep 981413 = 184015) (by norm_num)
theorem B981437 : Blo 650305 981437 := bbase (se 3 (by rfl) ⟨184019, by rfl⟩ : syracuseStep 981437 = 368039) (by norm_num)
theorem B784937 : Blo 650305 784937 := bbase (se 2 (by rfl) ⟨294351, by rfl⟩ : syracuseStep 784937 = 588703) (by norm_num)
theorem B784985 : Blo 650305 784985 := bbase (se 2 (by rfl) ⟨294369, by rfl⟩ : syracuseStep 784985 = 588739) (by norm_num)
theorem B883309 : Blo 650305 883309 := bbase (se 3 (by rfl) ⟨165620, by rfl⟩ : syracuseStep 883309 = 331241) (by norm_num)
theorem B1112773 : Blo 650305 1112773 := bbase (se 4 (by rfl) ⟨104322, by rfl⟩ : syracuseStep 1112773 = 208645) (by norm_num)
theorem B1571557 : Blo 650305 1571557 := bbase (se 4 (by rfl) ⟨147333, by rfl⟩ : syracuseStep 1571557 = 294667) (by norm_num)
theorem B1178645 : Blo 650305 1178645 := bbase (se 6 (by rfl) ⟨27624, by rfl⟩ : syracuseStep 1178645 = 55249) (by norm_num)
theorem B785533 : Blo 650305 785533 := bbase (se 3 (by rfl) ⟨147287, by rfl⟩ : syracuseStep 785533 = 294575) (by norm_num)
theorem B1408213 : Blo 650305 1408213 := bbase (se 7 (by rfl) ⟨16502, by rfl⟩ : syracuseStep 1408213 = 33005) (by norm_num)
theorem B1048069 : Blo 650305 1048069 := bbase (se 4 (by rfl) ⟨98256, by rfl⟩ : syracuseStep 1048069 = 196513) (by norm_num)
theorem B786013 : Blo 650305 786013 := bbase (se 3 (by rfl) ⟨147377, by rfl⟩ : syracuseStep 786013 = 294755) (by norm_num)
theorem B2195045 : Blo 650305 2195045 := bbase (se 4 (by rfl) ⟨205785, by rfl⟩ : syracuseStep 2195045 = 411571) (by norm_num)
theorem B3309173 : Blo 650305 3309173 := bbase (se 5 (by rfl) ⟨155117, by rfl⟩ : syracuseStep 3309173 = 310235) (by norm_num)
theorem B1113725 : Blo 650305 1113725 := bbase (se 3 (by rfl) ⟨208823, by rfl⟩ : syracuseStep 1113725 = 417647) (by norm_num)
theorem B8355797 : Blo 650305 8355797 := bbase (se 7 (by rfl) ⟨97919, by rfl⟩ : syracuseStep 8355797 = 195839) (by norm_num)
theorem B3964963 : Blo 650305 3964963 := bstep (se 1 (by rfl) ⟨2973722, by rfl⟩ : syracuseStep 3964963 = 5947445) B5947445
theorem B3178673 : Blo 650305 3178673 := bstep (se 2 (by rfl) ⟨1192002, by rfl⟩ : syracuseStep 3178673 = 2384005) B2384005
theorem B1409219 : Blo 650305 1409219 := bstep (se 1 (by rfl) ⟨1056914, by rfl⟩ : syracuseStep 1409219 = 2113829) B2113829
theorem B2195693 : Blo 650305 2195693 := bstep (se 3 (by rfl) ⟨411692, by rfl⟩ : syracuseStep 2195693 = 823385) B823385
theorem B2195747 : Blo 650305 2195747 := bstep (se 1 (by rfl) ⟨1646810, by rfl⟩ : syracuseStep 2195747 = 3293621) B3293621
theorem B1114435 : Blo 650305 1114435 := bstep (se 1 (by rfl) ⟨835826, by rfl⟩ : syracuseStep 1114435 = 1671653) B1671653
theorem B4456781 : Blo 650305 4456781 := bstep (se 3 (by rfl) ⟨835646, by rfl⟩ : syracuseStep 4456781 = 1671293) B1671293
theorem B4948451 : Blo 650305 4948451 := bstep (se 1 (by rfl) ⟨3711338, by rfl⟩ : syracuseStep 4948451 = 7422677) B7422677
theorem B3310093 : Blo 650305 3310093 := bstep (se 3 (by rfl) ⟨620642, by rfl⟩ : syracuseStep 3310093 = 1241285) B1241285
theorem B2196017 : Blo 650305 2196017 := bstep (se 2 (by rfl) ⟨823506, by rfl⟩ : syracuseStep 2196017 = 1647013) B1647013
theorem B3310307 : Blo 650305 3310307 := bstep (se 1 (by rfl) ⟨2482730, by rfl⟩ : syracuseStep 3310307 = 4965461) B4965461
theorem B2196557 : Blo 650305 2196557 := bstep (se 3 (by rfl) ⟨411854, by rfl⟩ : syracuseStep 2196557 = 823709) B823709
theorem B2196611 : Blo 650305 2196611 := bstep (se 1 (by rfl) ⟨1647458, by rfl⟩ : syracuseStep 2196611 = 3294917) B3294917
theorem B2196881 : Blo 650305 2196881 := bstep (se 2 (by rfl) ⟨823830, by rfl⟩ : syracuseStep 2196881 = 1647661) B1647661
theorem B10028485 : Blo 650305 10028485 := bstep (se 4 (by rfl) ⟨940170, by rfl⟩ : syracuseStep 10028485 = 1880341) B1880341
theorem B3311117 : Blo 650305 3311117 := bstep (se 3 (by rfl) ⟨620834, by rfl⟩ : syracuseStep 3311117 = 1241669) B1241669
theorem B2229869 : Blo 650305 2229869 := bstep (se 3 (by rfl) ⟨418100, by rfl⟩ : syracuseStep 2229869 = 836201) B836201
theorem B2786957 : Blo 650305 2786957 := bstep (se 3 (by rfl) ⟨522554, by rfl⟩ : syracuseStep 2786957 = 1045109) B1045109
theorem B2197421 : Blo 650305 2197421 := bstep (se 3 (by rfl) ⟨412016, by rfl⟩ : syracuseStep 2197421 = 824033) B824033
theorem B2197475 : Blo 650305 2197475 := bstep (se 1 (by rfl) ⟨1648106, by rfl⟩ : syracuseStep 2197475 = 3296213) B3296213
theorem B1116371 : Blo 650305 1116371 := bstep (se 1 (by rfl) ⟨837278, by rfl⟩ : syracuseStep 1116371 = 1674557) B1674557
theorem B2197745 : Blo 650305 2197745 := bstep (se 2 (by rfl) ⟨824154, by rfl⟩ : syracuseStep 2197745 = 1648309) B1648309
theorem B1411523 : Blo 650305 1411523 := bstep (se 1 (by rfl) ⟨1058642, by rfl⟩ : syracuseStep 1411523 = 2117285) B2117285
theorem B3574277 : Blo 650305 3574277 := bstep (se 4 (by rfl) ⟨335088, by rfl⟩ : syracuseStep 3574277 = 670177) B670177
theorem B2198285 : Blo 650305 2198285 := bstep (se 3 (by rfl) ⟨412178, by rfl⟩ : syracuseStep 2198285 = 824357) B824357
theorem B2198339 : Blo 650305 2198339 := bstep (se 1 (by rfl) ⟨1648754, by rfl⟩ : syracuseStep 2198339 = 3297509) B3297509
theorem B3345293 : Blo 650305 3345293 := bstep (se 3 (by rfl) ⟨627242, by rfl⟩ : syracuseStep 3345293 = 1254485) B1254485
theorem B4688837 : Blo 650305 4688837 := bstep (se 4 (by rfl) ⟨439578, by rfl⟩ : syracuseStep 4688837 = 879157) B879157
theorem B7048133 : Blo 650305 7048133 := bstep (se 4 (by rfl) ⟨660762, by rfl⟩ : syracuseStep 7048133 = 1321525) B1321525
theorem B3345457 : Blo 650305 3345457 := bstep (se 2 (by rfl) ⟨1254546, by rfl⟩ : syracuseStep 3345457 = 2509093) B2509093
theorem B2198609 : Blo 650305 2198609 := bstep (se 2 (by rfl) ⟨824478, by rfl⟩ : syracuseStep 2198609 = 1648957) B1648957
theorem B3968099 : Blo 650305 3968099 := bstep (se 1 (by rfl) ⟨2976074, by rfl⟩ : syracuseStep 3968099 = 5952149) B5952149
theorem B5016773 : Blo 650305 5016773 := bstep (se 4 (by rfl) ⟨470322, by rfl⟩ : syracuseStep 5016773 = 940645) B940645
theorem B2199149 : Blo 650305 2199149 := bstep (se 3 (by rfl) ⟨412340, by rfl⟩ : syracuseStep 2199149 = 824681) B824681
theorem B2199203 : Blo 650305 2199203 := bstep (se 1 (by rfl) ⟨1649402, by rfl⟩ : syracuseStep 2199203 = 3298805) B3298805
theorem B1117891 : Blo 650305 1117891 := bstep (se 1 (by rfl) ⟨838418, by rfl⟩ : syracuseStep 1117891 = 1676837) B1676837
theorem B2199473 : Blo 650305 2199473 := bstep (se 2 (by rfl) ⟨824802, by rfl⟩ : syracuseStep 2199473 = 1649605) B1649605
theorem B3706829 : Blo 650305 3706829 := bstep (se 3 (by rfl) ⟨695030, by rfl⟩ : syracuseStep 3706829 = 1390061) B1390061
theorem B15044579 : Blo 650305 15044579 := bstep (se 1 (by rfl) ⟨11283434, by rfl⟩ : syracuseStep 15044579 = 22566869) B22566869
theorem B2232305 : Blo 650305 2232305 := bstep (se 2 (by rfl) ⟨837114, by rfl⟩ : syracuseStep 2232305 = 1674229) B1674229
theorem B823603 : Blo 650305 823603 := bstep (se 1 (by rfl) ⟨617702, by rfl⟩ : syracuseStep 823603 = 1235405) B1235405
theorem B14127473 : Blo 650305 14127473 := bstep (se 2 (by rfl) ⟨5297802, by rfl⟩ : syracuseStep 14127473 = 10595605) B10595605
theorem B823699 : Blo 650305 823699 := bstep (se 1 (by rfl) ⟨617774, by rfl⟩ : syracuseStep 823699 = 1235549) B1235549
theorem B2200013 : Blo 650305 2200013 := bstep (se 3 (by rfl) ⟨412502, by rfl⟩ : syracuseStep 2200013 = 825005) B825005
theorem B954865 : Blo 650305 954865 := bstep (se 2 (by rfl) ⟨358074, by rfl⟩ : syracuseStep 954865 = 716149) B716149
theorem B2200067 : Blo 650305 2200067 := bstep (se 1 (by rfl) ⟨1650050, by rfl⟩ : syracuseStep 2200067 = 3300101) B3300101
theorem B30511669 : Blo 650305 30511669 := bstep (se 5 (by rfl) ⟨1430234, by rfl⟩ : syracuseStep 30511669 = 2860469) B2860469
theorem B2790065 : Blo 650305 2790065 := bstep (se 2 (by rfl) ⟨1046274, by rfl⟩ : syracuseStep 2790065 = 2092549) B2092549
theorem B2200337 : Blo 650305 2200337 := bstep (se 2 (by rfl) ⟨825126, by rfl⟩ : syracuseStep 2200337 = 1650253) B1650253
theorem B824195 : Blo 650305 824195 := bstep (se 1 (by rfl) ⟨618146, by rfl⟩ : syracuseStep 824195 = 1236293) B1236293
theorem B2233261 : Blo 650305 2233261 := bstep (se 3 (by rfl) ⟨418736, by rfl⟩ : syracuseStep 2233261 = 837473) B837473
theorem B1905677 : Blo 650305 1905677 := bstep (se 3 (by rfl) ⟨357314, by rfl⟩ : syracuseStep 1905677 = 714629) B714629
theorem B1676497 : Blo 650305 1676497 := bstep (se 2 (by rfl) ⟨628686, by rfl⟩ : syracuseStep 1676497 = 1257373) B1257373
theorem B2200877 : Blo 650305 2200877 := bstep (se 3 (by rfl) ⟨412664, by rfl⟩ : syracuseStep 2200877 = 825329) B825329
theorem B7411013 : Blo 650305 7411013 := bstep (se 4 (by rfl) ⟨694782, by rfl⟩ : syracuseStep 7411013 = 1389565) B1389565
theorem B2790733 : Blo 650305 2790733 := bstep (se 3 (by rfl) ⟨523262, by rfl⟩ : syracuseStep 2790733 = 1046525) B1046525
theorem B2200931 : Blo 650305 2200931 := bstep (se 1 (by rfl) ⟨1650698, by rfl⟩ : syracuseStep 2200931 = 3301397) B3301397
theorem B824899 : Blo 650305 824899 := bstep (se 1 (by rfl) ⟨618674, by rfl⟩ : syracuseStep 824899 = 1237349) B1237349
theorem B2201201 : Blo 650305 2201201 := bstep (se 2 (by rfl) ⟨825450, by rfl⟩ : syracuseStep 2201201 = 1650901) B1650901
theorem B661123 : Blo 650305 661123 := bstep (se 1 (by rfl) ⟨495842, by rfl⟩ : syracuseStep 661123 = 991685) B991685
theorem B824995 : Blo 650305 824995 := bstep (se 1 (by rfl) ⟨618746, by rfl⟩ : syracuseStep 824995 = 1237493) B1237493
theorem B4953797 : Blo 650305 4953797 := bstep (se 4 (by rfl) ⟨464418, by rfl⟩ : syracuseStep 4953797 = 928837) B928837
theorem B989057 : Blo 650305 989057 := bstep (se 2 (by rfl) ⟨370896, by rfl⟩ : syracuseStep 989057 = 741793) B741793
theorem B2791331 : Blo 650305 2791331 := bstep (se 1 (by rfl) ⟨2093498, by rfl⟩ : syracuseStep 2791331 = 4186997) B4186997
theorem B3709061 : Blo 650305 3709061 := bstep (se 4 (by rfl) ⟨347724, by rfl⟩ : syracuseStep 3709061 = 695449) B695449
theorem B2201741 : Blo 650305 2201741 := bstep (se 3 (by rfl) ⟨412826, by rfl⟩ : syracuseStep 2201741 = 825653) B825653
theorem B825491 : Blo 650305 825491 := bstep (se 1 (by rfl) ⟨619118, by rfl⟩ : syracuseStep 825491 = 1238237) B1238237
theorem B2201795 : Blo 650305 2201795 := bstep (se 1 (by rfl) ⟨1651346, by rfl⟩ : syracuseStep 2201795 = 3302693) B3302693
theorem B14063813 : Blo 650305 14063813 := bstep (se 4 (by rfl) ⟨1318482, by rfl⟩ : syracuseStep 14063813 = 2636965) B2636965
theorem B694595 : Blo 650305 694595 := bstep (se 1 (by rfl) ⟨520946, by rfl⟩ : syracuseStep 694595 = 1041893) B1041893
theorem B3578309 : Blo 650305 3578309 := bstep (se 4 (by rfl) ⟨335466, by rfl⟩ : syracuseStep 3578309 = 670933) B670933
theorem B2202065 : Blo 650305 2202065 := bstep (se 2 (by rfl) ⟨825774, by rfl⟩ : syracuseStep 2202065 = 1651549) B1651549
theorem B4463237 : Blo 650305 4463237 := bstep (se 4 (by rfl) ⟨418428, by rfl⟩ : syracuseStep 4463237 = 836857) B836857
theorem B3185315 : Blo 650305 3185315 := bstep (se 1 (by rfl) ⟨2388986, by rfl⟩ : syracuseStep 3185315 = 4777973) B4777973
theorem B3709745 : Blo 650305 3709745 := bstep (se 2 (by rfl) ⟨1391154, by rfl⟩ : syracuseStep 3709745 = 2782309) B2782309
theorem B826195 : Blo 650305 826195 := bstep (se 1 (by rfl) ⟨619646, by rfl⟩ : syracuseStep 826195 = 1239293) B1239293
theorem B826291 : Blo 650305 826291 := bstep (se 1 (by rfl) ⟨619718, by rfl⟩ : syracuseStep 826291 = 1239437) B1239437
theorem B2202605 : Blo 650305 2202605 := bstep (se 3 (by rfl) ⟨412988, by rfl⟩ : syracuseStep 2202605 = 825977) B825977
theorem B2202659 : Blo 650305 2202659 := bstep (se 1 (by rfl) ⟨1651994, by rfl⟩ : syracuseStep 2202659 = 3303989) B3303989
theorem B2825293 : Blo 650305 2825293 := bstep (se 3 (by rfl) ⟨529742, by rfl⟩ : syracuseStep 2825293 = 1059485) B1059485
theorem B4168901 : Blo 650305 4168901 := bstep (se 4 (by rfl) ⟨390834, by rfl⟩ : syracuseStep 4168901 = 781669) B781669
theorem B990481 : Blo 650305 990481 := bstep (se 2 (by rfl) ⟨371430, by rfl⟩ : syracuseStep 990481 = 742861) B742861
theorem B2202929 : Blo 650305 2202929 := bstep (se 2 (by rfl) ⟨826098, by rfl⟩ : syracuseStep 2202929 = 1652197) B1652197
theorem B662851 : Blo 650305 662851 := bstep (se 1 (by rfl) ⟨497138, by rfl⟩ : syracuseStep 662851 = 994277) B994277
theorem B826787 : Blo 650305 826787 := bstep (se 1 (by rfl) ⟨620090, by rfl⟩ : syracuseStep 826787 = 1240181) B1240181
theorem B2203469 : Blo 650305 2203469 := bstep (se 3 (by rfl) ⟨413150, by rfl⟩ : syracuseStep 2203469 = 826301) B826301
theorem B1908611 : Blo 650305 1908611 := bstep (se 1 (by rfl) ⟨1431458, by rfl⟩ : syracuseStep 1908611 = 2862917) B2862917
theorem B2203523 : Blo 650305 2203523 := bstep (se 1 (by rfl) ⟨1652642, by rfl⟩ : syracuseStep 2203523 = 3305285) B3305285
theorem B827491 : Blo 650305 827491 := bstep (se 1 (by rfl) ⟨620618, by rfl⟩ : syracuseStep 827491 = 1241237) B1241237
theorem B2203793 : Blo 650305 2203793 := bstep (se 2 (by rfl) ⟨826422, by rfl⟩ : syracuseStep 2203793 = 1652845) B1652845
theorem B827587 : Blo 650305 827587 := bstep (se 1 (by rfl) ⟨620690, by rfl⟩ : syracuseStep 827587 = 1241381) B1241381
theorem B1646801 : Blo 650305 1646801 := bstep (se 2 (by rfl) ⟨617550, by rfl⟩ : syracuseStep 1646801 = 1235101) B1235101
theorem B1056979 : Blo 650305 1056979 := bstep (se 1 (by rfl) ⟨792734, by rfl⟩ : syracuseStep 1056979 = 1585469) B1585469
theorem B3711203 : Blo 650305 3711203 := bstep (se 1 (by rfl) ⟨2783402, by rfl⟩ : syracuseStep 3711203 = 5566805) B5566805
theorem B794867 : Blo 650305 794867 := bstep (se 1 (by rfl) ⟨596150, by rfl⟩ : syracuseStep 794867 = 1192301) B1192301
theorem B1646851 : Blo 650305 1646851 := bstep (se 1 (by rfl) ⟨1235138, by rfl⟩ : syracuseStep 1646851 = 2470277) B2470277
theorem B696611 : Blo 650305 696611 := bstep (se 1 (by rfl) ⟨522458, by rfl⟩ : syracuseStep 696611 = 1044917) B1044917
theorem B1646993 : Blo 650305 1646993 := bstep (se 2 (by rfl) ⟨617622, by rfl⟩ : syracuseStep 1646993 = 1235245) B1235245
theorem B1057187 : Blo 650305 1057187 := bstep (se 1 (by rfl) ⟨792890, by rfl⟩ : syracuseStep 1057187 = 1585781) B1585781
theorem B2204333 : Blo 650305 2204333 := bstep (se 3 (by rfl) ⟨413312, by rfl⟩ : syracuseStep 2204333 = 826625) B826625
theorem B828083 : Blo 650305 828083 := bstep (se 1 (by rfl) ⟨621062, by rfl⟩ : syracuseStep 828083 = 1242125) B1242125
theorem B926417 : Blo 650305 926417 := bstep (se 2 (by rfl) ⟨347406, by rfl⟩ : syracuseStep 926417 = 694813) B694813
theorem B2204387 : Blo 650305 2204387 := bstep (se 1 (by rfl) ⟨1653290, by rfl⟩ : syracuseStep 2204387 = 3306581) B3306581
theorem B1254179 : Blo 650305 1254179 := bstep (se 1 (by rfl) ⟨940634, by rfl⟩ : syracuseStep 1254179 = 1881269) B1881269
theorem B1483697 : Blo 650305 1483697 := bstep (se 2 (by rfl) ⟨556386, by rfl⟩ : syracuseStep 1483697 = 1112773) B1112773
theorem B893921 : Blo 650305 893921 := bstep (se 2 (by rfl) ⟨335220, by rfl⟩ : syracuseStep 893921 = 670441) B670441
theorem B2204657 : Blo 650305 2204657 := bstep (se 2 (by rfl) ⟨826746, by rfl⟩ : syracuseStep 2204657 = 1653493) B1653493
theorem B4170851 : Blo 650305 4170851 := bstep (se 1 (by rfl) ⟨3128138, by rfl⟩ : syracuseStep 4170851 = 6256277) B6256277
theorem B697619 : Blo 650305 697619 := bstep (se 1 (by rfl) ⟨523214, by rfl⟩ : syracuseStep 697619 = 1046429) B1046429
theorem B1647985 : Blo 650305 1647985 := bstep (se 2 (by rfl) ⟨617994, by rfl⟩ : syracuseStep 1647985 = 1235989) B1235989
theorem B3515825 : Blo 650305 3515825 := bstep (se 2 (by rfl) ⟨1318434, by rfl⟩ : syracuseStep 3515825 = 2636869) B2636869
theorem B6038981 : Blo 650305 6038981 := bstep (se 4 (by rfl) ⟨566154, by rfl⟩ : syracuseStep 6038981 = 1132309) B1132309
theorem B2205197 : Blo 650305 2205197 := bstep (se 3 (by rfl) ⟨413474, by rfl⟩ : syracuseStep 2205197 = 826949) B826949
theorem B927283 : Blo 650305 927283 := bstep (se 1 (by rfl) ⟨695462, by rfl⟩ : syracuseStep 927283 = 1390925) B1390925
theorem B2205251 : Blo 650305 2205251 := bstep (se 1 (by rfl) ⟨1653938, by rfl⟩ : syracuseStep 2205251 = 3307877) B3307877
theorem B1877617 : Blo 650305 1877617 := bstep (se 2 (by rfl) ⟨704106, by rfl⟩ : syracuseStep 1877617 = 1408213) B1408213
theorem B1648259 : Blo 650305 1648259 := bstep (se 1 (by rfl) ⟨1236194, by rfl⟩ : syracuseStep 1648259 = 2472389) B2472389
theorem B927379 : Blo 650305 927379 := bstep (se 1 (by rfl) ⟨695534, by rfl⟩ : syracuseStep 927379 = 1391069) B1391069
theorem B4531909 : Blo 650305 4531909 := bstep (se 4 (by rfl) ⟨424866, by rfl⟩ : syracuseStep 4531909 = 849733) B849733
theorem B3516173 : Blo 650305 3516173 := bstep (se 3 (by rfl) ⟨659282, by rfl⟩ : syracuseStep 3516173 = 1318565) B1318565
theorem B1648451 : Blo 650305 1648451 := bstep (se 1 (by rfl) ⟨1236338, by rfl⟩ : syracuseStep 1648451 = 2472677) B2472677
theorem B2205521 : Blo 650305 2205521 := bstep (se 2 (by rfl) ⟨827070, by rfl⟩ : syracuseStep 2205521 = 1654141) B1654141
theorem B1255441 : Blo 650305 1255441 := bstep (se 2 (by rfl) ⟨470790, by rfl⟩ : syracuseStep 1255441 = 941581) B941581
theorem B927875 : Blo 650305 927875 := bstep (se 1 (by rfl) ⟨695906, by rfl⟩ : syracuseStep 927875 = 1391813) B1391813
theorem B2206061 : Blo 650305 2206061 := bstep (se 3 (by rfl) ⟨413636, by rfl⟩ : syracuseStep 2206061 = 827273) B827273
theorem B2206115 : Blo 650305 2206115 := bstep (se 1 (by rfl) ⟨1654586, by rfl⟩ : syracuseStep 2206115 = 3309173) B3309173
theorem B731731 : Blo 650305 731731 := bstep (se 1 (by rfl) ⟨548798, by rfl⟩ : syracuseStep 731731 = 1097597) B1097597
theorem B2206385 : Blo 650305 2206385 := bstep (se 2 (by rfl) ⟨827394, by rfl⟩ : syracuseStep 2206385 = 1654789) B1654789
theorem B731875 : Blo 650305 731875 := bstep (se 1 (by rfl) ⟨548906, by rfl⟩ : syracuseStep 731875 = 1097813) B1097813
theorem B1649393 : Blo 650305 1649393 := bstep (se 2 (by rfl) ⟨618522, by rfl⟩ : syracuseStep 1649393 = 1237045) B1237045
theorem B928513 : Blo 650305 928513 := bstep (se 2 (by rfl) ⟨348192, by rfl⟩ : syracuseStep 928513 = 696385) B696385
theorem B1649443 : Blo 650305 1649443 := bstep (se 1 (by rfl) ⟨1237082, by rfl⟩ : syracuseStep 1649443 = 2474165) B2474165
theorem B732019 : Blo 650305 732019 := bstep (se 1 (by rfl) ⟨549014, by rfl⟩ : syracuseStep 732019 = 1098029) B1098029
theorem B1649585 : Blo 650305 1649585 := bstep (se 2 (by rfl) ⟨618594, by rfl⟩ : syracuseStep 1649585 = 1237189) B1237189
theorem B732163 : Blo 650305 732163 := bstep (se 1 (by rfl) ⟨549122, by rfl⟩ : syracuseStep 732163 = 1098245) B1098245
theorem B7416845 : Blo 650305 7416845 := bstep (se 3 (by rfl) ⟨1390658, by rfl⟩ : syracuseStep 7416845 = 2781317) B2781317
theorem B2010161 : Blo 650305 2010161 := bstep (se 2 (by rfl) ⟨753810, by rfl⟩ : syracuseStep 2010161 = 1507621) B1507621
theorem B928849 : Blo 650305 928849 := bstep (se 2 (by rfl) ⟨348318, by rfl⟩ : syracuseStep 928849 = 696637) B696637
theorem B12102797 : Blo 650305 12102797 := bstep (se 3 (by rfl) ⟨2269274, by rfl⟩ : syracuseStep 12102797 = 4538549) B4538549
theorem B732307 : Blo 650305 732307 := bstep (se 1 (by rfl) ⟨549230, by rfl⟩ : syracuseStep 732307 = 1098461) B1098461
theorem B2206925 : Blo 650305 2206925 := bstep (se 3 (by rfl) ⟨413798, by rfl⟩ : syracuseStep 2206925 = 827597) B827597
theorem B896243 : Blo 650305 896243 := bstep (se 1 (by rfl) ⟨672182, by rfl⟩ : syracuseStep 896243 = 1344365) B1344365
theorem B2206979 : Blo 650305 2206979 := bstep (se 1 (by rfl) ⟨1655234, by rfl⟩ : syracuseStep 2206979 = 3310469) B3310469
theorem B732451 : Blo 650305 732451 := bstep (se 1 (by rfl) ⟨549338, by rfl⟩ : syracuseStep 732451 = 1098677) B1098677
theorem B3714437 : Blo 650305 3714437 := bstep (se 4 (by rfl) ⟨348228, by rfl⟩ : syracuseStep 3714437 = 696457) B696457
theorem B4959629 : Blo 650305 4959629 := bstep (se 3 (by rfl) ⟨929930, by rfl⟩ : syracuseStep 4959629 = 1859861) B1859861
theorem B732595 : Blo 650305 732595 := bstep (se 1 (by rfl) ⟨549446, by rfl⟩ : syracuseStep 732595 = 1098893) B1098893
theorem B2207249 : Blo 650305 2207249 := bstep (se 2 (by rfl) ⟨827718, by rfl⟩ : syracuseStep 2207249 = 1655437) B1655437
theorem B15904309 : Blo 650305 15904309 := bstep (se 5 (by rfl) ⟨745514, by rfl⟩ : syracuseStep 15904309 = 1491029) B1491029
theorem B732739 : Blo 650305 732739 := bstep (se 1 (by rfl) ⟨549554, by rfl⟩ : syracuseStep 732739 = 1099109) B1099109
theorem B1322563 : Blo 650305 1322563 := bstep (se 1 (by rfl) ⟨991922, by rfl⟩ : syracuseStep 1322563 = 1983845) B1983845
theorem B3518029 : Blo 650305 3518029 := bstep (se 3 (by rfl) ⟨659630, by rfl⟩ : syracuseStep 3518029 = 1319261) B1319261
theorem B4173389 : Blo 650305 4173389 := bstep (se 3 (by rfl) ⟨782510, by rfl⟩ : syracuseStep 4173389 = 1565021) B1565021
theorem B929441 : Blo 650305 929441 := bstep (se 2 (by rfl) ⟨348540, by rfl⟩ : syracuseStep 929441 = 697081) B697081
theorem B732883 : Blo 650305 732883 := bstep (se 1 (by rfl) ⟨549662, by rfl⟩ : syracuseStep 732883 = 1099325) B1099325
theorem B7057165 : Blo 650305 7057165 := bstep (se 3 (by rfl) ⟨1323218, by rfl⟩ : syracuseStep 7057165 = 2646437) B2646437
theorem B3714893 : Blo 650305 3714893 := bstep (se 3 (by rfl) ⟨696542, by rfl⟩ : syracuseStep 3714893 = 1393085) B1393085
theorem B733027 : Blo 650305 733027 := bstep (se 1 (by rfl) ⟨549770, by rfl⟩ : syracuseStep 733027 = 1099541) B1099541
theorem B1650577 : Blo 650305 1650577 := bstep (se 2 (by rfl) ⟨618966, by rfl⟩ : syracuseStep 1650577 = 1237933) B1237933
theorem B1322993 : Blo 650305 1322993 := bstep (se 2 (by rfl) ⟨496122, by rfl⟩ : syracuseStep 1322993 = 992245) B992245
theorem B733171 : Blo 650305 733171 := bstep (se 1 (by rfl) ⟨549878, by rfl⟩ : syracuseStep 733171 = 1099757) B1099757
theorem B2207789 : Blo 650305 2207789 := bstep (se 3 (by rfl) ⟨413960, by rfl⟩ : syracuseStep 2207789 = 827921) B827921
theorem B2207843 : Blo 650305 2207843 := bstep (se 1 (by rfl) ⟨1655882, by rfl⟩ : syracuseStep 2207843 = 3311765) B3311765
theorem B733315 : Blo 650305 733315 := bstep (se 1 (by rfl) ⟨549986, by rfl⟩ : syracuseStep 733315 = 1099973) B1099973
theorem B1650851 : Blo 650305 1650851 := bstep (se 1 (by rfl) ⟨1238138, by rfl⟩ : syracuseStep 1650851 = 2476277) B2476277
theorem B929971 : Blo 650305 929971 := bstep (se 1 (by rfl) ⟨697478, by rfl⟩ : syracuseStep 929971 = 1394957) B1394957
theorem B733459 : Blo 650305 733459 := bstep (se 1 (by rfl) ⟨550094, by rfl⟩ : syracuseStep 733459 = 1100189) B1100189
theorem B1651043 : Blo 650305 1651043 := bstep (se 1 (by rfl) ⟨1238282, by rfl⟩ : syracuseStep 1651043 = 2476565) B2476565
theorem B2208113 : Blo 650305 2208113 := bstep (se 2 (by rfl) ⟨828042, by rfl⟩ : syracuseStep 2208113 = 1656085) B1656085
theorem B4010381 : Blo 650305 4010381 := bstep (se 3 (by rfl) ⟨751946, by rfl⟩ : syracuseStep 4010381 = 1503893) B1503893
theorem B733603 : Blo 650305 733603 := bstep (se 1 (by rfl) ⟨550202, by rfl⟩ : syracuseStep 733603 = 1100405) B1100405
theorem B1061345 : Blo 650305 1061345 := bstep (se 2 (by rfl) ⟨398004, by rfl⟩ : syracuseStep 1061345 = 796009) B796009
theorem B930307 : Blo 650305 930307 := bstep (se 1 (by rfl) ⟨697730, by rfl⟩ : syracuseStep 930307 = 1395461) B1395461
theorem B2503181 : Blo 650305 2503181 := bstep (se 3 (by rfl) ⟨469346, by rfl⟩ : syracuseStep 2503181 = 938693) B938693
theorem B733747 : Blo 650305 733747 := bstep (se 1 (by rfl) ⟨550310, by rfl⟩ : syracuseStep 733747 = 1100621) B1100621
theorem B1389155 : Blo 650305 1389155 := bstep (se 1 (by rfl) ⟨1041866, by rfl⟩ : syracuseStep 1389155 = 2083733) B2083733
theorem B5026445 : Blo 650305 5026445 := bstep (se 3 (by rfl) ⟨942458, by rfl⟩ : syracuseStep 5026445 = 1884917) B1884917
theorem B733891 : Blo 650305 733891 := bstep (se 1 (by rfl) ⟨550418, by rfl⟩ : syracuseStep 733891 = 1100837) B1100837
theorem B2470733 : Blo 650305 2470733 := bstep (se 3 (by rfl) ⟨463262, by rfl⟩ : syracuseStep 2470733 = 926525) B926525
theorem B734035 : Blo 650305 734035 := bstep (se 1 (by rfl) ⟨550526, by rfl⟩ : syracuseStep 734035 = 1101053) B1101053
theorem B1913699 : Blo 650305 1913699 := bstep (se 1 (by rfl) ⟨1435274, by rfl⟩ : syracuseStep 1913699 = 2870549) B2870549
theorem B734179 : Blo 650305 734179 := bstep (se 1 (by rfl) ⟨550634, by rfl⟩ : syracuseStep 734179 = 1101269) B1101269
theorem B1258481 : Blo 650305 1258481 := bstep (se 2 (by rfl) ⟨471930, by rfl⟩ : syracuseStep 1258481 = 943861) B943861
theorem B930865 : Blo 650305 930865 := bstep (se 2 (by rfl) ⟨349074, by rfl⟩ : syracuseStep 930865 = 698149) B698149
theorem B930899 : Blo 650305 930899 := bstep (se 1 (by rfl) ⟨698174, by rfl⟩ : syracuseStep 930899 = 1396349) B1396349
theorem B734323 : Blo 650305 734323 := bstep (se 1 (by rfl) ⟨550742, by rfl⟩ : syracuseStep 734323 = 1101485) B1101485
theorem B734467 : Blo 650305 734467 := bstep (se 1 (by rfl) ⟨550850, by rfl⟩ : syracuseStep 734467 = 1101701) B1101701
theorem B1651985 : Blo 650305 1651985 := bstep (se 2 (by rfl) ⟨619494, by rfl⟩ : syracuseStep 1651985 = 1238989) B1238989
theorem B1652035 : Blo 650305 1652035 := bstep (se 1 (by rfl) ⟨1239026, by rfl⟩ : syracuseStep 1652035 = 2478053) B2478053
theorem B734611 : Blo 650305 734611 := bstep (se 1 (by rfl) ⟨550958, by rfl⟩ : syracuseStep 734611 = 1101917) B1101917
theorem B3978659 : Blo 650305 3978659 := bstep (se 1 (by rfl) ⟨2983994, by rfl⟩ : syracuseStep 3978659 = 5967989) B5967989
theorem B1652177 : Blo 650305 1652177 := bstep (se 2 (by rfl) ⟨619566, by rfl⟩ : syracuseStep 1652177 = 1239133) B1239133
theorem B734755 : Blo 650305 734755 := bstep (se 1 (by rfl) ⟨551066, by rfl⟩ : syracuseStep 734755 = 1102133) B1102133
theorem B931457 : Blo 650305 931457 := bstep (se 2 (by rfl) ⟨349296, by rfl⟩ : syracuseStep 931457 = 698593) B698593
theorem B734899 : Blo 650305 734899 := bstep (se 1 (by rfl) ⟨551174, by rfl⟩ : syracuseStep 734899 = 1102349) B1102349
theorem B931537 : Blo 650305 931537 := bstep (se 2 (by rfl) ⟨349326, by rfl⟩ : syracuseStep 931537 = 698653) B698653
theorem B8369891 : Blo 650305 8369891 := bstep (se 1 (by rfl) ⟨6277418, by rfl⟩ : syracuseStep 8369891 = 12554837) B12554837
theorem B735043 : Blo 650305 735043 := bstep (se 1 (by rfl) ⟨551282, by rfl⟩ : syracuseStep 735043 = 1102565) B1102565
theorem B7419761 : Blo 650305 7419761 := bstep (se 2 (by rfl) ⟨2782410, by rfl⟩ : syracuseStep 7419761 = 5564821) B5564821
theorem B735187 : Blo 650305 735187 := bstep (se 1 (by rfl) ⟨551390, by rfl⟩ : syracuseStep 735187 = 1102781) B1102781
theorem B735331 : Blo 650305 735331 := bstep (se 1 (by rfl) ⟨551498, by rfl⟩ : syracuseStep 735331 = 1102997) B1102997
theorem B4962545 : Blo 650305 4962545 := bstep (se 2 (by rfl) ⟨1860954, by rfl⟩ : syracuseStep 4962545 = 3721909) B3721909
theorem B735475 : Blo 650305 735475 := bstep (se 1 (by rfl) ⟨551606, by rfl⟩ : syracuseStep 735475 = 1103213) B1103213
theorem B1325425 : Blo 650305 1325425 := bstep (se 2 (by rfl) ⟨497034, by rfl⟩ : syracuseStep 1325425 = 994069) B994069
theorem B735619 : Blo 650305 735619 := bstep (se 1 (by rfl) ⟨551714, by rfl⟩ : syracuseStep 735619 = 1103429) B1103429
theorem B1030577 : Blo 650305 1030577 := bstep (se 2 (by rfl) ⟨386466, by rfl⟩ : syracuseStep 1030577 = 772933) B772933
theorem B1653169 : Blo 650305 1653169 := bstep (se 2 (by rfl) ⟨619938, by rfl⟩ : syracuseStep 1653169 = 1239877) B1239877
theorem B735763 : Blo 650305 735763 := bstep (se 1 (by rfl) ⟨551822, by rfl⟩ : syracuseStep 735763 = 1103645) B1103645
theorem B735907 : Blo 650305 735907 := bstep (se 1 (by rfl) ⟨551930, by rfl⟩ : syracuseStep 735907 = 1103861) B1103861
theorem B3717809 : Blo 650305 3717809 := bstep (se 2 (by rfl) ⟨1394178, by rfl⟩ : syracuseStep 3717809 = 2788357) B2788357
theorem B1653443 : Blo 650305 1653443 := bstep (se 1 (by rfl) ⟨1240082, by rfl⟩ : syracuseStep 1653443 = 2480165) B2480165
theorem B1391377 : Blo 650305 1391377 := bstep (se 2 (by rfl) ⟨521766, by rfl⟩ : syracuseStep 1391377 = 1043533) B1043533
theorem B1489681 : Blo 650305 1489681 := bstep (se 2 (by rfl) ⟨558630, by rfl⟩ : syracuseStep 1489681 = 1117261) B1117261
theorem B736051 : Blo 650305 736051 := bstep (se 1 (by rfl) ⟨552038, by rfl⟩ : syracuseStep 736051 = 1104077) B1104077
theorem B1653635 : Blo 650305 1653635 := bstep (se 1 (by rfl) ⟨1240226, by rfl⟩ : syracuseStep 1653635 = 2480453) B2480453
theorem B3128291 : Blo 650305 3128291 := bstep (se 1 (by rfl) ⟨2346218, by rfl⟩ : syracuseStep 3128291 = 4692437) B4692437
theorem B736259 : Blo 650305 736259 := bstep (se 1 (by rfl) ⟨552194, by rfl⟩ : syracuseStep 736259 = 1104389) B1104389
theorem B2473649 : Blo 650305 2473649 := bstep (se 2 (by rfl) ⟨927618, by rfl⟩ : syracuseStep 2473649 = 1855237) B1855237
theorem B1097489 : Blo 650305 1097489 := bstep (se 2 (by rfl) ⟨411558, by rfl⟩ : syracuseStep 1097489 = 823117) B823117
theorem B3129137 : Blo 650305 3129137 := bstep (se 2 (by rfl) ⟨1173426, by rfl⟩ : syracuseStep 3129137 = 2346853) B2346853
theorem B1654577 : Blo 650305 1654577 := bstep (se 2 (by rfl) ⟨620466, by rfl⟩ : syracuseStep 1654577 = 1240933) B1240933
theorem B1654627 : Blo 650305 1654627 := bstep (se 1 (by rfl) ⟨1240970, by rfl⟩ : syracuseStep 1654627 = 2481941) B2481941
theorem B1097617 : Blo 650305 1097617 := bstep (se 2 (by rfl) ⟨411606, by rfl⟩ : syracuseStep 1097617 = 823213) B823213
theorem B1097651 : Blo 650305 1097651 := bstep (se 1 (by rfl) ⟨823238, by rfl⟩ : syracuseStep 1097651 = 1646477) B1646477
theorem B1654769 : Blo 650305 1654769 := bstep (se 2 (by rfl) ⟨620538, by rfl⟩ : syracuseStep 1654769 = 1241077) B1241077
theorem B966691 : Blo 650305 966691 := bstep (se 1 (by rfl) ⟨725018, by rfl⟩ : syracuseStep 966691 = 1450037) B1450037
theorem B1097779 : Blo 650305 1097779 := bstep (se 1 (by rfl) ⟨823334, by rfl⟩ : syracuseStep 1097779 = 1646669) B1646669
theorem B3719267 : Blo 650305 3719267 := bstep (se 1 (by rfl) ⟨2789450, by rfl⟩ : syracuseStep 3719267 = 5578901) B5578901
theorem B3293297 : Blo 650305 3293297 := bstep (se 2 (by rfl) ⟨1234986, by rfl⟩ : syracuseStep 3293297 = 2469973) B2469973
theorem B1097921 : Blo 650305 1097921 := bstep (se 2 (by rfl) ⟨411720, by rfl⟩ : syracuseStep 1097921 = 823441) B823441
theorem B1098049 : Blo 650305 1098049 := bstep (se 2 (by rfl) ⟨411768, by rfl⟩ : syracuseStep 1098049 = 823537) B823537
theorem B1098083 : Blo 650305 1098083 := bstep (se 1 (by rfl) ⟨823562, by rfl⟩ : syracuseStep 1098083 = 1647125) B1647125
theorem B1098211 : Blo 650305 1098211 := bstep (se 1 (by rfl) ⟨823658, by rfl⟩ : syracuseStep 1098211 = 1647317) B1647317
theorem B1098353 : Blo 650305 1098353 := bstep (se 2 (by rfl) ⟨411882, by rfl⟩ : syracuseStep 1098353 = 823765) B823765
theorem B1098481 : Blo 650305 1098481 := bstep (se 2 (by rfl) ⟨411930, by rfl⟩ : syracuseStep 1098481 = 823861) B823861
theorem B1098515 : Blo 650305 1098515 := bstep (se 1 (by rfl) ⟨823886, by rfl⟩ : syracuseStep 1098515 = 1647773) B1647773
theorem B1098643 : Blo 650305 1098643 := bstep (se 1 (by rfl) ⟨823982, by rfl⟩ : syracuseStep 1098643 = 1647965) B1647965
theorem B1655761 : Blo 650305 1655761 := bstep (se 2 (by rfl) ⟨620910, by rfl⟩ : syracuseStep 1655761 = 1241821) B1241821
theorem B1098785 : Blo 650305 1098785 := bstep (se 2 (by rfl) ⟨412044, by rfl⟩ : syracuseStep 1098785 = 824089) B824089
theorem B3720269 : Blo 650305 3720269 := bstep (se 3 (by rfl) ⟨697550, by rfl⟩ : syracuseStep 3720269 = 1395101) B1395101
theorem B2475107 : Blo 650305 2475107 := bstep (se 1 (by rfl) ⟨1856330, by rfl⟩ : syracuseStep 2475107 = 3712661) B3712661
theorem B1098913 : Blo 650305 1098913 := bstep (se 2 (by rfl) ⟨412092, by rfl⟩ : syracuseStep 1098913 = 824185) B824185
theorem B1098947 : Blo 650305 1098947 := bstep (se 1 (by rfl) ⟨824210, by rfl⟩ : syracuseStep 1098947 = 1648421) B1648421
theorem B1656035 : Blo 650305 1656035 := bstep (se 1 (by rfl) ⟨1242026, by rfl⟩ : syracuseStep 1656035 = 2484053) B2484053
theorem B1099075 : Blo 650305 1099075 := bstep (se 1 (by rfl) ⟨824306, by rfl⟩ : syracuseStep 1099075 = 1648613) B1648613
theorem B1099217 : Blo 650305 1099217 := bstep (se 2 (by rfl) ⟨412206, by rfl⟩ : syracuseStep 1099217 = 824413) B824413
theorem B1983953 : Blo 650305 1983953 := bstep (se 2 (by rfl) ⟨743982, by rfl⟩ : syracuseStep 1983953 = 1487965) B1487965
theorem B3294755 : Blo 650305 3294755 := bstep (se 1 (by rfl) ⟨2471066, by rfl⟩ : syracuseStep 3294755 = 4942133) B4942133
theorem B1099345 : Blo 650305 1099345 := bstep (se 2 (by rfl) ⟨412254, by rfl⟩ : syracuseStep 1099345 = 824509) B824509
theorem B1853027 : Blo 650305 1853027 := bstep (se 1 (by rfl) ⟨1389770, by rfl⟩ : syracuseStep 1853027 = 2779541) B2779541
theorem B1099379 : Blo 650305 1099379 := bstep (se 1 (by rfl) ⟨824534, by rfl⟩ : syracuseStep 1099379 = 1649069) B1649069
theorem B1099507 : Blo 650305 1099507 := bstep (se 1 (by rfl) ⟨824630, by rfl⟩ : syracuseStep 1099507 = 1649261) B1649261
theorem B1394435 : Blo 650305 1394435 := bstep (se 1 (by rfl) ⟨1045826, by rfl⟩ : syracuseStep 1394435 = 2091653) B2091653
theorem B1099649 : Blo 650305 1099649 := bstep (se 2 (by rfl) ⟨412368, by rfl⟩ : syracuseStep 1099649 = 824737) B824737
theorem B1099777 : Blo 650305 1099777 := bstep (se 2 (by rfl) ⟨412416, by rfl⟩ : syracuseStep 1099777 = 824833) B824833
theorem B1099811 : Blo 650305 1099811 := bstep (se 1 (by rfl) ⟨824858, by rfl⟩ : syracuseStep 1099811 = 1649717) B1649717
theorem B2476109 : Blo 650305 2476109 := bstep (se 3 (by rfl) ⟨464270, by rfl⟩ : syracuseStep 2476109 = 928541) B928541
theorem B1099939 : Blo 650305 1099939 := bstep (se 1 (by rfl) ⟨824954, by rfl⟩ : syracuseStep 1099939 = 1649909) B1649909
theorem B8472757 : Blo 650305 8472757 := bstep (se 5 (by rfl) ⟨397160, by rfl⟩ : syracuseStep 8472757 = 794321) B794321
theorem B3131597 : Blo 650305 3131597 := bstep (se 3 (by rfl) ⟨587174, by rfl⟩ : syracuseStep 3131597 = 1174349) B1174349
theorem B2115857 : Blo 650305 2115857 := bstep (se 2 (by rfl) ⟨793446, by rfl⟩ : syracuseStep 2115857 = 1586893) B1586893
theorem B1100081 : Blo 650305 1100081 := bstep (se 2 (by rfl) ⟨412530, by rfl⟩ : syracuseStep 1100081 = 825061) B825061
theorem B3295565 : Blo 650305 3295565 := bstep (se 3 (by rfl) ⟨617918, by rfl⟩ : syracuseStep 3295565 = 1235837) B1235837
theorem B1853837 : Blo 650305 1853837 := bstep (se 3 (by rfl) ⟨347594, by rfl⟩ : syracuseStep 1853837 = 695189) B695189
theorem B1100209 : Blo 650305 1100209 := bstep (se 2 (by rfl) ⟨412578, by rfl⟩ : syracuseStep 1100209 = 825157) B825157
theorem B1100243 : Blo 650305 1100243 := bstep (se 1 (by rfl) ⟨825182, by rfl⟩ : syracuseStep 1100243 = 1650365) B1650365
theorem B1854029 : Blo 650305 1854029 := bstep (se 3 (by rfl) ⟨347630, by rfl⟩ : syracuseStep 1854029 = 695261) B695261
theorem B1788497 : Blo 650305 1788497 := bstep (se 2 (by rfl) ⟨670686, by rfl⟩ : syracuseStep 1788497 = 1341373) B1341373
theorem B1100371 : Blo 650305 1100371 := bstep (se 1 (by rfl) ⟨825278, by rfl⟩ : syracuseStep 1100371 = 1650557) B1650557
theorem B1395299 : Blo 650305 1395299 := bstep (se 1 (by rfl) ⟨1046474, by rfl⟩ : syracuseStep 1395299 = 2092949) B2092949
theorem B1985219 : Blo 650305 1985219 := bstep (se 1 (by rfl) ⟨1488914, by rfl⟩ : syracuseStep 1985219 = 2977829) B2977829
theorem B1395409 : Blo 650305 1395409 := bstep (se 2 (by rfl) ⟨523278, by rfl⟩ : syracuseStep 1395409 = 1046557) B1046557
theorem B1100513 : Blo 650305 1100513 := bstep (se 2 (by rfl) ⟨412692, by rfl⟩ : syracuseStep 1100513 = 825385) B825385
theorem B2083619 : Blo 650305 2083619 := bstep (se 1 (by rfl) ⟨1562714, by rfl⟩ : syracuseStep 2083619 = 3125429) B3125429
theorem B772915 : Blo 650305 772915 := bstep (se 1 (by rfl) ⟨579686, by rfl⟩ : syracuseStep 772915 = 1159373) B1159373
theorem B10734389 : Blo 650305 10734389 := bstep (se 5 (by rfl) ⟨503174, by rfl⟩ : syracuseStep 10734389 = 1006349) B1006349
theorem B1100641 : Blo 650305 1100641 := bstep (se 2 (by rfl) ⟨412740, by rfl⟩ : syracuseStep 1100641 = 825481) B825481
theorem B1100675 : Blo 650305 1100675 := bstep (se 1 (by rfl) ⟨825506, by rfl⟩ : syracuseStep 1100675 = 1651013) B1651013
theorem B1100803 : Blo 650305 1100803 := bstep (se 1 (by rfl) ⟨825602, by rfl⟩ : syracuseStep 1100803 = 1651205) B1651205
theorem B4180997 : Blo 650305 4180997 := bstep (se 4 (by rfl) ⟨391968, by rfl⟩ : syracuseStep 4180997 = 783937) B783937
theorem B1100945 : Blo 650305 1100945 := bstep (se 2 (by rfl) ⟨412854, by rfl⟩ : syracuseStep 1100945 = 825709) B825709
theorem B1101073 : Blo 650305 1101073 := bstep (se 2 (by rfl) ⟨412902, by rfl⟩ : syracuseStep 1101073 = 825805) B825805
theorem B1101107 : Blo 650305 1101107 := bstep (se 1 (by rfl) ⟨825830, by rfl⟩ : syracuseStep 1101107 = 1651661) B1651661
theorem B1101235 : Blo 650305 1101235 := bstep (se 1 (by rfl) ⟨825926, by rfl⟩ : syracuseStep 1101235 = 1651853) B1651853
theorem B1855021 : Blo 650305 1855021 := bstep (se 3 (by rfl) ⟨347816, by rfl⟩ : syracuseStep 1855021 = 695633) B695633
theorem B1101377 : Blo 650305 1101377 := bstep (se 2 (by rfl) ⟨413016, by rfl⟩ : syracuseStep 1101377 = 826033) B826033
theorem B11292301 : Blo 650305 11292301 := bstep (se 3 (by rfl) ⟨2117306, by rfl⟩ : syracuseStep 11292301 = 4234613) B4234613
theorem B1101505 : Blo 650305 1101505 := bstep (se 2 (by rfl) ⟨413064, by rfl⟩ : syracuseStep 1101505 = 826129) B826129
theorem B1101539 : Blo 650305 1101539 := bstep (se 1 (by rfl) ⟨826154, by rfl⟩ : syracuseStep 1101539 = 1652309) B1652309
theorem B2084707 : Blo 650305 2084707 := bstep (se 1 (by rfl) ⟨1563530, by rfl⟩ : syracuseStep 2084707 = 3127061) B3127061
theorem B1101667 : Blo 650305 1101667 := bstep (se 1 (by rfl) ⟨826250, by rfl⟩ : syracuseStep 1101667 = 1652501) B1652501
theorem B3723185 : Blo 650305 3723185 := bstep (se 2 (by rfl) ⟨1396194, by rfl⟩ : syracuseStep 3723185 = 2792389) B2792389
theorem B2084849 : Blo 650305 2084849 := bstep (se 2 (by rfl) ⟨781818, by rfl⟩ : syracuseStep 2084849 = 1563637) B1563637
theorem B1101809 : Blo 650305 1101809 := bstep (se 2 (by rfl) ⟨413178, by rfl⟩ : syracuseStep 1101809 = 826357) B826357
theorem B17813525 : Blo 650305 17813525 := bstep (se 6 (by rfl) ⟨417504, by rfl⟩ : syracuseStep 17813525 = 835009) B835009
theorem B2969635 : Blo 650305 2969635 := bstep (se 1 (by rfl) ⟨2227226, by rfl⟩ : syracuseStep 2969635 = 4454453) B4454453
theorem B1101937 : Blo 650305 1101937 := bstep (se 2 (by rfl) ⟨413226, by rfl⟩ : syracuseStep 1101937 = 826453) B826453
theorem B2478221 : Blo 650305 2478221 := bstep (se 3 (by rfl) ⟨464666, by rfl⟩ : syracuseStep 2478221 = 929333) B929333
theorem B1101971 : Blo 650305 1101971 := bstep (se 1 (by rfl) ⟨826478, by rfl⟩ : syracuseStep 1101971 = 1652957) B1652957
theorem B3526897 : Blo 650305 3526897 := bstep (se 2 (by rfl) ⟨1322586, by rfl⟩ : syracuseStep 3526897 = 2645173) B2645173
theorem B1102099 : Blo 650305 1102099 := bstep (se 1 (by rfl) ⟨826574, by rfl⟩ : syracuseStep 1102099 = 1653149) B1653149
theorem B1102241 : Blo 650305 1102241 := bstep (se 2 (by rfl) ⟨413340, by rfl⟩ : syracuseStep 1102241 = 826681) B826681
theorem B1102369 : Blo 650305 1102369 := bstep (se 2 (by rfl) ⟨413388, by rfl⟩ : syracuseStep 1102369 = 826777) B826777
theorem B1102403 : Blo 650305 1102403 := bstep (se 1 (by rfl) ⟨826802, by rfl⟩ : syracuseStep 1102403 = 1653605) B1653605
theorem B1397425 : Blo 650305 1397425 := bstep (se 2 (by rfl) ⟨524034, by rfl⟩ : syracuseStep 1397425 = 1048069) B1048069
theorem B1102531 : Blo 650305 1102531 := bstep (se 1 (by rfl) ⟨826898, by rfl⟩ : syracuseStep 1102531 = 1653797) B1653797
theorem B1102673 : Blo 650305 1102673 := bstep (se 2 (by rfl) ⟨413502, by rfl⟩ : syracuseStep 1102673 = 827005) B827005
theorem B4182947 : Blo 650305 4182947 := bstep (se 1 (by rfl) ⟨3137210, by rfl⟩ : syracuseStep 4182947 = 6274421) B6274421
theorem B2479025 : Blo 650305 2479025 := bstep (se 2 (by rfl) ⟨929634, by rfl⟩ : syracuseStep 2479025 = 1859269) B1859269
theorem B1102801 : Blo 650305 1102801 := bstep (se 2 (by rfl) ⟨413550, by rfl⟩ : syracuseStep 1102801 = 827101) B827101
theorem B1102835 : Blo 650305 1102835 := bstep (se 1 (by rfl) ⟨827126, by rfl⟩ : syracuseStep 1102835 = 1654253) B1654253
theorem B1463345 : Blo 650305 1463345 := bstep (se 2 (by rfl) ⟨548754, by rfl⟩ : syracuseStep 1463345 = 1097509) B1097509
theorem B1463363 : Blo 650305 1463363 := bstep (se 1 (by rfl) ⟨1097522, by rfl⟩ : syracuseStep 1463363 = 2195045) B2195045
theorem B742483 : Blo 650305 742483 := bstep (se 1 (by rfl) ⟨556862, by rfl⟩ : syracuseStep 742483 = 1113725) B1113725
theorem B1791085 : Blo 650305 1791085 := bstep (se 3 (by rfl) ⟨335828, by rfl⟩ : syracuseStep 1791085 = 671657) B671657
theorem B1102963 : Blo 650305 1102963 := bstep (se 1 (by rfl) ⟨827222, by rfl⟩ : syracuseStep 1102963 = 1654445) B1654445
theorem B3298481 : Blo 650305 3298481 := bstep (se 2 (by rfl) ⟨1236930, by rfl⟩ : syracuseStep 3298481 = 2473861) B2473861
theorem B1692881 : Blo 650305 1692881 := bstep (se 2 (by rfl) ⟨634830, by rfl⟩ : syracuseStep 1692881 = 1269661) B1269661
theorem B1856753 : Blo 650305 1856753 := bstep (se 2 (by rfl) ⟨696282, by rfl⟩ : syracuseStep 1856753 = 1392565) B1392565
theorem B1103105 : Blo 650305 1103105 := bstep (se 2 (by rfl) ⟨413664, by rfl⟩ : syracuseStep 1103105 = 827329) B827329
theorem B2086193 : Blo 650305 2086193 := bstep (se 2 (by rfl) ⟨782322, by rfl⟩ : syracuseStep 2086193 = 1564645) B1564645
theorem B1463633 : Blo 650305 1463633 := bstep (se 2 (by rfl) ⟨548862, by rfl⟩ : syracuseStep 1463633 = 1097725) B1097725
theorem B1463651 : Blo 650305 1463651 := bstep (se 1 (by rfl) ⟨1097738, by rfl⟩ : syracuseStep 1463651 = 2195477) B2195477
theorem B3724643 : Blo 650305 3724643 := bstep (se 1 (by rfl) ⟨2793482, by rfl⟩ : syracuseStep 3724643 = 5586965) B5586965
theorem B1103233 : Blo 650305 1103233 := bstep (se 2 (by rfl) ⟨413712, by rfl⟩ : syracuseStep 1103233 = 827425) B827425
theorem B1103267 : Blo 650305 1103267 := bstep (se 1 (by rfl) ⟨827450, by rfl⟩ : syracuseStep 1103267 = 1654901) B1654901
theorem B1856945 : Blo 650305 1856945 := bstep (se 2 (by rfl) ⟨696354, by rfl⟩ : syracuseStep 1856945 = 1392709) B1392709
theorem B1103395 : Blo 650305 1103395 := bstep (se 1 (by rfl) ⟨827546, by rfl⟩ : syracuseStep 1103395 = 1655093) B1655093
theorem B2479693 : Blo 650305 2479693 := bstep (se 3 (by rfl) ⟨464942, by rfl⟩ : syracuseStep 2479693 = 929885) B929885
theorem B1463921 : Blo 650305 1463921 := bstep (se 2 (by rfl) ⟨548970, by rfl⟩ : syracuseStep 1463921 = 1097941) B1097941
theorem B1463939 : Blo 650305 1463939 := bstep (se 1 (by rfl) ⟨1097954, by rfl⟩ : syracuseStep 1463939 = 2195909) B2195909
theorem B1234577 : Blo 650305 1234577 := bstep (se 2 (by rfl) ⟨462966, by rfl⟩ : syracuseStep 1234577 = 925933) B925933
theorem B2152099 : Blo 650305 2152099 := bstep (se 1 (by rfl) ⟨1614074, by rfl⟩ : syracuseStep 2152099 = 3228149) B3228149
theorem B1103537 : Blo 650305 1103537 := bstep (se 2 (by rfl) ⟨413826, by rfl⟩ : syracuseStep 1103537 = 827653) B827653
theorem B2348813 : Blo 650305 2348813 := bstep (se 3 (by rfl) ⟨440402, by rfl⟩ : syracuseStep 2348813 = 880805) B880805
theorem B1103665 : Blo 650305 1103665 := bstep (se 2 (by rfl) ⟨413874, by rfl⟩ : syracuseStep 1103665 = 827749) B827749
theorem B1103699 : Blo 650305 1103699 := bstep (se 1 (by rfl) ⟨827774, by rfl⟩ : syracuseStep 1103699 = 1655549) B1655549
theorem B1464209 : Blo 650305 1464209 := bstep (se 2 (by rfl) ⟨549078, by rfl⟩ : syracuseStep 1464209 = 1098157) B1098157
theorem B1464227 : Blo 650305 1464227 := bstep (se 1 (by rfl) ⟨1098170, by rfl⟩ : syracuseStep 1464227 = 2196341) B2196341
theorem B1234865 : Blo 650305 1234865 := bstep (se 2 (by rfl) ⟨463074, by rfl⟩ : syracuseStep 1234865 = 926149) B926149
theorem B1103827 : Blo 650305 1103827 := bstep (se 1 (by rfl) ⟨827870, by rfl⟩ : syracuseStep 1103827 = 1655741) B1655741
theorem B1103969 : Blo 650305 1103969 := bstep (se 2 (by rfl) ⟨413988, by rfl⟩ : syracuseStep 1103969 = 827977) B827977
theorem B1464497 : Blo 650305 1464497 := bstep (se 2 (by rfl) ⟨549186, by rfl⟩ : syracuseStep 1464497 = 1098373) B1098373
theorem B1464515 : Blo 650305 1464515 := bstep (se 1 (by rfl) ⟨1098386, by rfl⟩ : syracuseStep 1464515 = 2196773) B2196773
theorem B2087117 : Blo 650305 2087117 := bstep (se 3 (by rfl) ⟨391334, by rfl⟩ : syracuseStep 2087117 = 782669) B782669
theorem B1104097 : Blo 650305 1104097 := bstep (se 2 (by rfl) ⟨414036, by rfl⟩ : syracuseStep 1104097 = 828073) B828073
theorem B1104131 : Blo 650305 1104131 := bstep (se 1 (by rfl) ⟨828098, by rfl⟩ : syracuseStep 1104131 = 1656197) B1656197
theorem B1562897 : Blo 650305 1562897 := bstep (se 2 (by rfl) ⟨586086, by rfl⟩ : syracuseStep 1562897 = 1172173) B1172173
theorem B2480483 : Blo 650305 2480483 := bstep (se 1 (by rfl) ⟨1860362, by rfl⟩ : syracuseStep 2480483 = 3720725) B3720725
theorem B2087309 : Blo 650305 2087309 := bstep (se 3 (by rfl) ⟨391370, by rfl⟩ : syracuseStep 2087309 = 782741) B782741
theorem B1857937 : Blo 650305 1857937 := bstep (se 2 (by rfl) ⟨696726, by rfl⟩ : syracuseStep 1857937 = 1393453) B1393453
theorem B1464785 : Blo 650305 1464785 := bstep (se 2 (by rfl) ⟨549294, by rfl⟩ : syracuseStep 1464785 = 1098589) B1098589
theorem B1464803 : Blo 650305 1464803 := bstep (se 1 (by rfl) ⟨1098602, by rfl⟩ : syracuseStep 1464803 = 2197205) B2197205
theorem B3299939 : Blo 650305 3299939 := bstep (se 1 (by rfl) ⟨2474954, by rfl⟩ : syracuseStep 3299939 = 4949909) B4949909
theorem B1235587 : Blo 650305 1235587 := bstep (se 1 (by rfl) ⟨926690, by rfl⟩ : syracuseStep 1235587 = 1853381) B1853381
theorem B1858211 : Blo 650305 1858211 := bstep (se 1 (by rfl) ⟨1393658, by rfl⟩ : syracuseStep 1858211 = 2787317) B2787317
theorem B1465073 : Blo 650305 1465073 := bstep (se 2 (by rfl) ⟨549402, by rfl⟩ : syracuseStep 1465073 = 1098805) B1098805
theorem B1465091 : Blo 650305 1465091 := bstep (se 1 (by rfl) ⟨1098818, by rfl⟩ : syracuseStep 1465091 = 2197637) B2197637
theorem B744211 : Blo 650305 744211 := bstep (se 1 (by rfl) ⟨558158, by rfl⟩ : syracuseStep 744211 = 1116317) B1116317
theorem B744275 : Blo 650305 744275 := bstep (se 1 (by rfl) ⟨558206, by rfl⟩ : syracuseStep 744275 = 1116413) B1116413
theorem B1858403 : Blo 650305 1858403 := bstep (se 1 (by rfl) ⟨1393802, by rfl⟩ : syracuseStep 1858403 = 2787605) B2787605
theorem B2481137 : Blo 650305 2481137 := bstep (se 2 (by rfl) ⟨930426, by rfl⟩ : syracuseStep 2481137 = 1860853) B1860853
theorem B1465361 : Blo 650305 1465361 := bstep (se 2 (by rfl) ⟨549510, by rfl⟩ : syracuseStep 1465361 = 1099021) B1099021
theorem B1465379 : Blo 650305 1465379 := bstep (se 1 (by rfl) ⟨1099034, by rfl⟩ : syracuseStep 1465379 = 2198069) B2198069
theorem B1236035 : Blo 650305 1236035 := bstep (se 1 (by rfl) ⟨927026, by rfl⟩ : syracuseStep 1236035 = 1854053) B1854053
theorem B1563953 : Blo 650305 1563953 := bstep (se 2 (by rfl) ⟨586482, by rfl⟩ : syracuseStep 1563953 = 1172965) B1172965
theorem B1465649 : Blo 650305 1465649 := bstep (se 2 (by rfl) ⟨549618, by rfl⟩ : syracuseStep 1465649 = 1099237) B1099237
theorem B1465667 : Blo 650305 1465667 := bstep (se 1 (by rfl) ⟨1099250, by rfl⟩ : syracuseStep 1465667 = 2198501) B2198501
theorem B1236323 : Blo 650305 1236323 := bstep (se 1 (by rfl) ⟨927242, by rfl⟩ : syracuseStep 1236323 = 1854485) B1854485
theorem B3300749 : Blo 650305 3300749 := bstep (se 3 (by rfl) ⟨618890, by rfl⟩ : syracuseStep 3300749 = 1237781) B1237781
theorem B17817029 : Blo 650305 17817029 := bstep (se 4 (by rfl) ⟨1670346, by rfl⟩ : syracuseStep 17817029 = 3340693) B3340693
theorem B1465937 : Blo 650305 1465937 := bstep (se 2 (by rfl) ⟨549726, by rfl⟩ : syracuseStep 1465937 = 1099453) B1099453
theorem B1465955 : Blo 650305 1465955 := bstep (se 1 (by rfl) ⟨1099466, by rfl⟩ : syracuseStep 1465955 = 2198933) B2198933
theorem B1859213 : Blo 650305 1859213 := bstep (se 3 (by rfl) ⟨348602, by rfl⟩ : syracuseStep 1859213 = 697205) B697205
theorem B1859395 : Blo 650305 1859395 := bstep (se 1 (by rfl) ⟨1394546, by rfl⟩ : syracuseStep 1859395 = 2789093) B2789093
theorem B1466225 : Blo 650305 1466225 := bstep (se 2 (by rfl) ⟨549834, by rfl⟩ : syracuseStep 1466225 = 1099669) B1099669
theorem B1466243 : Blo 650305 1466243 := bstep (se 1 (by rfl) ⟨1099682, by rfl⟩ : syracuseStep 1466243 = 2199365) B2199365
theorem B3170353 : Blo 650305 3170353 := bstep (se 2 (by rfl) ⟨1188882, by rfl⟩ : syracuseStep 3170353 = 2377765) B2377765
theorem B2089091 : Blo 650305 2089091 := bstep (se 1 (by rfl) ⟨1566818, by rfl⟩ : syracuseStep 2089091 = 3133637) B3133637
theorem B1466513 : Blo 650305 1466513 := bstep (se 2 (by rfl) ⟨549942, by rfl⟩ : syracuseStep 1466513 = 1099885) B1099885
theorem B1466531 : Blo 650305 1466531 := bstep (se 1 (by rfl) ⟨1099898, by rfl⟩ : syracuseStep 1466531 = 2199797) B2199797
theorem B1564867 : Blo 650305 1564867 := bstep (se 1 (by rfl) ⟨1173650, by rfl⟩ : syracuseStep 1564867 = 2347301) B2347301
theorem B1237265 : Blo 650305 1237265 := bstep (se 2 (by rfl) ⟨463974, by rfl⟩ : syracuseStep 1237265 = 927949) B927949
theorem B1859885 : Blo 650305 1859885 := bstep (se 3 (by rfl) ⟨348728, by rfl⟩ : syracuseStep 1859885 = 697457) B697457
theorem B2482595 : Blo 650305 2482595 := bstep (se 1 (by rfl) ⟨1861946, by rfl⟩ : syracuseStep 2482595 = 3723893) B3723893
theorem B1466801 : Blo 650305 1466801 := bstep (se 2 (by rfl) ⟨550050, by rfl⟩ : syracuseStep 1466801 = 1100101) B1100101
theorem B2482609 : Blo 650305 2482609 := bstep (se 2 (by rfl) ⟨930978, by rfl⟩ : syracuseStep 2482609 = 1861957) B1861957
theorem B1466819 : Blo 650305 1466819 := bstep (se 1 (by rfl) ⟨1100114, by rfl⟩ : syracuseStep 1466819 = 2200229) B2200229
theorem B1171921 : Blo 650305 1171921 := bstep (se 2 (by rfl) ⟨439470, by rfl⟩ : syracuseStep 1171921 = 878941) B878941
theorem B4186637 : Blo 650305 4186637 := bstep (se 3 (by rfl) ⟨784994, by rfl⟩ : syracuseStep 4186637 = 1569989) B1569989
theorem B975473 : Blo 650305 975473 := bstep (se 2 (by rfl) ⟨365802, by rfl⟩ : syracuseStep 975473 = 731605) B731605
theorem B975491 : Blo 650305 975491 := bstep (se 1 (by rfl) ⟨731618, by rfl⟩ : syracuseStep 975491 = 1463237) B1463237
theorem B3531397 : Blo 650305 3531397 := bstep (se 4 (by rfl) ⟨331068, by rfl⟩ : syracuseStep 3531397 = 662137) B662137
theorem B975521 : Blo 650305 975521 := bstep (se 2 (by rfl) ⟨365820, by rfl⟩ : syracuseStep 975521 = 731641) B731641
theorem B975539 : Blo 650305 975539 := bstep (se 1 (by rfl) ⟨731654, by rfl⟩ : syracuseStep 975539 = 1463309) B1463309
theorem B975569 : Blo 650305 975569 := bstep (se 2 (by rfl) ⟨365838, by rfl⟩ : syracuseStep 975569 = 731677) B731677
theorem B1467089 : Blo 650305 1467089 := bstep (se 2 (by rfl) ⟨550158, by rfl⟩ : syracuseStep 1467089 = 1100317) B1100317
theorem B975587 : Blo 650305 975587 := bstep (se 1 (by rfl) ⟨731690, by rfl⟩ : syracuseStep 975587 = 1463381) B1463381
theorem B1467107 : Blo 650305 1467107 := bstep (se 1 (by rfl) ⟨1100330, by rfl⟩ : syracuseStep 1467107 = 2200661) B2200661
theorem B975617 : Blo 650305 975617 := bstep (se 2 (by rfl) ⟨365856, by rfl⟩ : syracuseStep 975617 = 731713) B731713
theorem B975635 : Blo 650305 975635 := bstep (se 1 (by rfl) ⟨731726, by rfl⟩ : syracuseStep 975635 = 1463453) B1463453
theorem B975665 : Blo 650305 975665 := bstep (se 2 (by rfl) ⟨365874, by rfl⟩ : syracuseStep 975665 = 731749) B731749
theorem B975683 : Blo 650305 975683 := bstep (se 1 (by rfl) ⟨731762, by rfl⟩ : syracuseStep 975683 = 1463525) B1463525
theorem B975713 : Blo 650305 975713 := bstep (se 2 (by rfl) ⟨365892, by rfl⟩ : syracuseStep 975713 = 731785) B731785
theorem B2777969 : Blo 650305 2777969 := bstep (se 2 (by rfl) ⟨1041738, by rfl⟩ : syracuseStep 2777969 = 2083477) B2083477
theorem B975731 : Blo 650305 975731 := bstep (se 1 (by rfl) ⟨731798, by rfl⟩ : syracuseStep 975731 = 1463597) B1463597
theorem B975761 : Blo 650305 975761 := bstep (se 2 (by rfl) ⟨365910, by rfl⟩ : syracuseStep 975761 = 731821) B731821
theorem B975779 : Blo 650305 975779 := bstep (se 1 (by rfl) ⟨731834, by rfl⟩ : syracuseStep 975779 = 1463669) B1463669
theorem B975809 : Blo 650305 975809 := bstep (se 2 (by rfl) ⟨365928, by rfl⟩ : syracuseStep 975809 = 731857) B731857
theorem B975827 : Blo 650305 975827 := bstep (se 1 (by rfl) ⟨731870, by rfl⟩ : syracuseStep 975827 = 1463741) B1463741
theorem B975857 : Blo 650305 975857 := bstep (se 2 (by rfl) ⟨365946, by rfl⟩ : syracuseStep 975857 = 731893) B731893
theorem B1467377 : Blo 650305 1467377 := bstep (se 2 (by rfl) ⟨550266, by rfl⟩ : syracuseStep 1467377 = 1100533) B1100533
theorem B975875 : Blo 650305 975875 := bstep (se 1 (by rfl) ⟨731906, by rfl⟩ : syracuseStep 975875 = 1463813) B1463813
theorem B1467395 : Blo 650305 1467395 := bstep (se 1 (by rfl) ⟨1100546, by rfl⟩ : syracuseStep 1467395 = 2201093) B2201093
theorem B975905 : Blo 650305 975905 := bstep (se 2 (by rfl) ⟨365964, by rfl⟩ : syracuseStep 975905 = 731929) B731929
theorem B975923 : Blo 650305 975923 := bstep (se 1 (by rfl) ⟨731942, by rfl⟩ : syracuseStep 975923 = 1463885) B1463885
theorem B975953 : Blo 650305 975953 := bstep (se 2 (by rfl) ⟨365982, by rfl⟩ : syracuseStep 975953 = 731965) B731965
theorem B1172561 : Blo 650305 1172561 := bstep (se 2 (by rfl) ⟨439710, by rfl⟩ : syracuseStep 1172561 = 879421) B879421
theorem B975971 : Blo 650305 975971 := bstep (se 1 (by rfl) ⟨731978, by rfl⟩ : syracuseStep 975971 = 1463957) B1463957
theorem B5661809 : Blo 650305 5661809 := bstep (se 2 (by rfl) ⟨2123178, by rfl⟩ : syracuseStep 5661809 = 4246357) B4246357
theorem B976001 : Blo 650305 976001 := bstep (se 2 (by rfl) ⟨366000, by rfl⟩ : syracuseStep 976001 = 732001) B732001
theorem B1238161 : Blo 650305 1238161 := bstep (se 2 (by rfl) ⟨464310, by rfl⟩ : syracuseStep 1238161 = 928621) B928621
theorem B976019 : Blo 650305 976019 := bstep (se 1 (by rfl) ⟨732014, by rfl⟩ : syracuseStep 976019 = 1464029) B1464029
theorem B976049 : Blo 650305 976049 := bstep (se 2 (by rfl) ⟨366018, by rfl⟩ : syracuseStep 976049 = 732037) B732037
theorem B976067 : Blo 650305 976067 := bstep (se 1 (by rfl) ⟨732050, by rfl⟩ : syracuseStep 976067 = 1464101) B1464101
theorem B976097 : Blo 650305 976097 := bstep (se 2 (by rfl) ⟨366036, by rfl⟩ : syracuseStep 976097 = 732073) B732073
theorem B976115 : Blo 650305 976115 := bstep (se 1 (by rfl) ⟨732086, by rfl⟩ : syracuseStep 976115 = 1464173) B1464173
theorem B976145 : Blo 650305 976145 := bstep (se 2 (by rfl) ⟨366054, by rfl⟩ : syracuseStep 976145 = 732109) B732109
theorem B1467665 : Blo 650305 1467665 := bstep (se 2 (by rfl) ⟨550374, by rfl⟩ : syracuseStep 1467665 = 1100749) B1100749
theorem B976163 : Blo 650305 976163 := bstep (se 1 (by rfl) ⟨732122, by rfl⟩ : syracuseStep 976163 = 1464245) B1464245
theorem B1467683 : Blo 650305 1467683 := bstep (se 1 (by rfl) ⟨1100762, by rfl⟩ : syracuseStep 1467683 = 2201525) B2201525
theorem B1238321 : Blo 650305 1238321 := bstep (se 2 (by rfl) ⟨464370, by rfl⟩ : syracuseStep 1238321 = 928741) B928741
theorem B2647345 : Blo 650305 2647345 := bstep (se 2 (by rfl) ⟨992754, by rfl⟩ : syracuseStep 2647345 = 1985509) B1985509
theorem B976193 : Blo 650305 976193 := bstep (se 2 (by rfl) ⟨366072, by rfl⟩ : syracuseStep 976193 = 732145) B732145
theorem B976211 : Blo 650305 976211 := bstep (se 1 (by rfl) ⟨732158, by rfl⟩ : syracuseStep 976211 = 1464317) B1464317
theorem B976241 : Blo 650305 976241 := bstep (se 2 (by rfl) ⟨366090, by rfl⟩ : syracuseStep 976241 = 732181) B732181
theorem B976259 : Blo 650305 976259 := bstep (se 1 (by rfl) ⟨732194, by rfl⟩ : syracuseStep 976259 = 1464389) B1464389
theorem B976289 : Blo 650305 976289 := bstep (se 2 (by rfl) ⟨366108, by rfl⟩ : syracuseStep 976289 = 732217) B732217
theorem B976307 : Blo 650305 976307 := bstep (se 1 (by rfl) ⟨732230, by rfl⟩ : syracuseStep 976307 = 1464461) B1464461
theorem B1861069 : Blo 650305 1861069 := bstep (se 3 (by rfl) ⟨348950, by rfl⟩ : syracuseStep 1861069 = 697901) B697901
theorem B976337 : Blo 650305 976337 := bstep (se 2 (by rfl) ⟨366126, by rfl⟩ : syracuseStep 976337 = 732253) B732253
theorem B976355 : Blo 650305 976355 := bstep (se 1 (by rfl) ⟨732266, by rfl⟩ : syracuseStep 976355 = 1464533) B1464533
theorem B976385 : Blo 650305 976385 := bstep (se 2 (by rfl) ⟨366144, by rfl⟩ : syracuseStep 976385 = 732289) B732289
theorem B976403 : Blo 650305 976403 := bstep (se 1 (by rfl) ⟨732302, by rfl⟩ : syracuseStep 976403 = 1464605) B1464605
theorem B1336867 : Blo 650305 1336867 := bstep (se 1 (by rfl) ⟨1002650, by rfl⟩ : syracuseStep 1336867 = 2005301) B2005301
theorem B976433 : Blo 650305 976433 := bstep (se 2 (by rfl) ⟨366162, by rfl⟩ : syracuseStep 976433 = 732325) B732325
theorem B1467953 : Blo 650305 1467953 := bstep (se 2 (by rfl) ⟨550482, by rfl⟩ : syracuseStep 1467953 = 1100965) B1100965
theorem B976451 : Blo 650305 976451 := bstep (se 1 (by rfl) ⟨732338, by rfl⟩ : syracuseStep 976451 = 1464677) B1464677
theorem B1467971 : Blo 650305 1467971 := bstep (se 1 (by rfl) ⟨1100978, by rfl⟩ : syracuseStep 1467971 = 2201957) B2201957
theorem B976481 : Blo 650305 976481 := bstep (se 2 (by rfl) ⟨366180, by rfl⟩ : syracuseStep 976481 = 732361) B732361
theorem B976499 : Blo 650305 976499 := bstep (se 1 (by rfl) ⟨732374, by rfl⟩ : syracuseStep 976499 = 1464749) B1464749
theorem B976529 : Blo 650305 976529 := bstep (se 2 (by rfl) ⟨366198, by rfl⟩ : syracuseStep 976529 = 732397) B732397
theorem B976547 : Blo 650305 976547 := bstep (se 1 (by rfl) ⟨732410, by rfl⟩ : syracuseStep 976547 = 1464821) B1464821
theorem B976577 : Blo 650305 976577 := bstep (se 2 (by rfl) ⟨366216, by rfl⟩ : syracuseStep 976577 = 732433) B732433
theorem B1238723 : Blo 650305 1238723 := bstep (se 1 (by rfl) ⟨929042, by rfl⟩ : syracuseStep 1238723 = 1858085) B1858085
theorem B976595 : Blo 650305 976595 := bstep (se 1 (by rfl) ⟨732446, by rfl⟩ : syracuseStep 976595 = 1464893) B1464893
theorem B976625 : Blo 650305 976625 := bstep (se 2 (by rfl) ⟨366234, by rfl⟩ : syracuseStep 976625 = 732469) B732469
theorem B976643 : Blo 650305 976643 := bstep (se 1 (by rfl) ⟨732482, by rfl⟩ : syracuseStep 976643 = 1464965) B1464965
theorem B2778893 : Blo 650305 2778893 := bstep (se 3 (by rfl) ⟨521042, by rfl⟩ : syracuseStep 2778893 = 1042085) B1042085
theorem B976673 : Blo 650305 976673 := bstep (se 2 (by rfl) ⟨366252, by rfl⟩ : syracuseStep 976673 = 732505) B732505
theorem B976691 : Blo 650305 976691 := bstep (se 1 (by rfl) ⟨732518, by rfl⟩ : syracuseStep 976691 = 1465037) B1465037
theorem B976721 : Blo 650305 976721 := bstep (se 2 (by rfl) ⟨366270, by rfl⟩ : syracuseStep 976721 = 732541) B732541
theorem B1468241 : Blo 650305 1468241 := bstep (se 2 (by rfl) ⟨550590, by rfl⟩ : syracuseStep 1468241 = 1101181) B1101181
theorem B976739 : Blo 650305 976739 := bstep (se 1 (by rfl) ⟨732554, by rfl⟩ : syracuseStep 976739 = 1465109) B1465109
theorem B1468259 : Blo 650305 1468259 := bstep (se 1 (by rfl) ⟨1101194, by rfl⟩ : syracuseStep 1468259 = 2202389) B2202389
theorem B2484067 : Blo 650305 2484067 := bstep (se 1 (by rfl) ⟨1863050, by rfl⟩ : syracuseStep 2484067 = 3726101) B3726101
theorem B976769 : Blo 650305 976769 := bstep (se 2 (by rfl) ⟨366288, by rfl⟩ : syracuseStep 976769 = 732577) B732577
theorem B976787 : Blo 650305 976787 := bstep (se 1 (by rfl) ⟨732590, by rfl⟩ : syracuseStep 976787 = 1465181) B1465181
theorem B976817 : Blo 650305 976817 := bstep (se 2 (by rfl) ⟨366306, by rfl⟩ : syracuseStep 976817 = 732613) B732613
theorem B976835 : Blo 650305 976835 := bstep (se 1 (by rfl) ⟨732626, by rfl⟩ : syracuseStep 976835 = 1465253) B1465253
theorem B976865 : Blo 650305 976865 := bstep (se 2 (by rfl) ⟨366324, by rfl⟩ : syracuseStep 976865 = 732649) B732649
theorem B976883 : Blo 650305 976883 := bstep (se 1 (by rfl) ⟨732662, by rfl⟩ : syracuseStep 976883 = 1465325) B1465325
theorem B976913 : Blo 650305 976913 := bstep (se 2 (by rfl) ⟨366342, by rfl⟩ : syracuseStep 976913 = 732685) B732685
theorem B976931 : Blo 650305 976931 := bstep (se 1 (by rfl) ⟨732698, by rfl⟩ : syracuseStep 976931 = 1465397) B1465397
theorem B976961 : Blo 650305 976961 := bstep (se 2 (by rfl) ⟨366360, by rfl⟩ : syracuseStep 976961 = 732721) B732721
theorem B976979 : Blo 650305 976979 := bstep (se 1 (by rfl) ⟨732734, by rfl⟩ : syracuseStep 976979 = 1465469) B1465469
theorem B977009 : Blo 650305 977009 := bstep (se 2 (by rfl) ⟨366378, by rfl⟩ : syracuseStep 977009 = 732757) B732757
theorem B1468529 : Blo 650305 1468529 := bstep (se 2 (by rfl) ⟨550698, by rfl⟩ : syracuseStep 1468529 = 1101397) B1101397
theorem B977027 : Blo 650305 977027 := bstep (se 1 (by rfl) ⟨732770, by rfl⟩ : syracuseStep 977027 = 1465541) B1465541
theorem B1468547 : Blo 650305 1468547 := bstep (se 1 (by rfl) ⟨1101410, by rfl⟩ : syracuseStep 1468547 = 2202821) B2202821
theorem B977057 : Blo 650305 977057 := bstep (se 2 (by rfl) ⟨366396, by rfl⟩ : syracuseStep 977057 = 732793) B732793
theorem B977075 : Blo 650305 977075 := bstep (se 1 (by rfl) ⟨732806, by rfl⟩ : syracuseStep 977075 = 1465613) B1465613
theorem B3532997 : Blo 650305 3532997 := bstep (se 4 (by rfl) ⟨331218, by rfl⟩ : syracuseStep 3532997 = 662437) B662437
theorem B977105 : Blo 650305 977105 := bstep (se 2 (by rfl) ⟨366414, by rfl⟩ : syracuseStep 977105 = 732829) B732829
theorem B2091217 : Blo 650305 2091217 := bstep (se 2 (by rfl) ⟨784206, by rfl⟩ : syracuseStep 2091217 = 1568413) B1568413
theorem B977123 : Blo 650305 977123 := bstep (se 1 (by rfl) ⟨732842, by rfl⟩ : syracuseStep 977123 = 1465685) B1465685
theorem B9038051 : Blo 650305 9038051 := bstep (se 1 (by rfl) ⟨6778538, by rfl⟩ : syracuseStep 9038051 = 13557077) B13557077
theorem B3303665 : Blo 650305 3303665 := bstep (se 2 (by rfl) ⟨1238874, by rfl⟩ : syracuseStep 3303665 = 2477749) B2477749
theorem B977153 : Blo 650305 977153 := bstep (se 2 (by rfl) ⟨366432, by rfl⟩ : syracuseStep 977153 = 732865) B732865
theorem B977171 : Blo 650305 977171 := bstep (se 1 (by rfl) ⟨732878, by rfl⟩ : syracuseStep 977171 = 1465757) B1465757
theorem B977201 : Blo 650305 977201 := bstep (se 2 (by rfl) ⟨366450, by rfl⟩ : syracuseStep 977201 = 732901) B732901
theorem B977219 : Blo 650305 977219 := bstep (se 1 (by rfl) ⟨732914, by rfl⟩ : syracuseStep 977219 = 1465829) B1465829
theorem B977249 : Blo 650305 977249 := bstep (se 2 (by rfl) ⟨366468, by rfl⟩ : syracuseStep 977249 = 732937) B732937
theorem B977267 : Blo 650305 977267 := bstep (se 1 (by rfl) ⟨732950, by rfl⟩ : syracuseStep 977267 = 1465901) B1465901
theorem B977297 : Blo 650305 977297 := bstep (se 2 (by rfl) ⟨366486, by rfl⟩ : syracuseStep 977297 = 732973) B732973
theorem B1468817 : Blo 650305 1468817 := bstep (se 2 (by rfl) ⟨550806, by rfl⟩ : syracuseStep 1468817 = 1101613) B1101613
theorem B977315 : Blo 650305 977315 := bstep (se 1 (by rfl) ⟨732986, by rfl⟩ : syracuseStep 977315 = 1465973) B1465973
theorem B1468835 : Blo 650305 1468835 := bstep (se 1 (by rfl) ⟨1101626, by rfl⟩ : syracuseStep 1468835 = 2203253) B2203253
theorem B977345 : Blo 650305 977345 := bstep (se 2 (by rfl) ⟨366504, by rfl⟩ : syracuseStep 977345 = 733009) B733009
theorem B977363 : Blo 650305 977363 := bstep (se 1 (by rfl) ⟨733022, by rfl⟩ : syracuseStep 977363 = 1466045) B1466045
theorem B977393 : Blo 650305 977393 := bstep (se 2 (by rfl) ⟨366522, by rfl⟩ : syracuseStep 977393 = 733045) B733045
theorem B1862129 : Blo 650305 1862129 := bstep (se 2 (by rfl) ⟨698298, by rfl⟩ : syracuseStep 1862129 = 1396597) B1396597
theorem B977411 : Blo 650305 977411 := bstep (se 1 (by rfl) ⟨733058, by rfl⟩ : syracuseStep 977411 = 1466117) B1466117
theorem B977441 : Blo 650305 977441 := bstep (se 2 (by rfl) ⟨366540, by rfl⟩ : syracuseStep 977441 = 733081) B733081
theorem B977459 : Blo 650305 977459 := bstep (se 1 (by rfl) ⟨733094, by rfl⟩ : syracuseStep 977459 = 1466189) B1466189
theorem B1239619 : Blo 650305 1239619 := bstep (se 1 (by rfl) ⟨929714, by rfl⟩ : syracuseStep 1239619 = 1859429) B1859429
theorem B977489 : Blo 650305 977489 := bstep (se 2 (by rfl) ⟨366558, by rfl⟩ : syracuseStep 977489 = 733117) B733117
theorem B977507 : Blo 650305 977507 := bstep (se 1 (by rfl) ⟨733130, by rfl⟩ : syracuseStep 977507 = 1466261) B1466261
theorem B1043059 : Blo 650305 1043059 := bstep (se 1 (by rfl) ⟨782294, by rfl⟩ : syracuseStep 1043059 = 1564589) B1564589
theorem B977537 : Blo 650305 977537 := bstep (se 2 (by rfl) ⟨366576, by rfl⟩ : syracuseStep 977537 = 733153) B733153
theorem B977555 : Blo 650305 977555 := bstep (se 1 (by rfl) ⟨733166, by rfl⟩ : syracuseStep 977555 = 1466333) B1466333
theorem B977585 : Blo 650305 977585 := bstep (se 2 (by rfl) ⟨366594, by rfl⟩ : syracuseStep 977585 = 733189) B733189
theorem B1469105 : Blo 650305 1469105 := bstep (se 2 (by rfl) ⟨550914, by rfl⟩ : syracuseStep 1469105 = 1101829) B1101829
theorem B977603 : Blo 650305 977603 := bstep (se 1 (by rfl) ⟨733202, by rfl⟩ : syracuseStep 977603 = 1466405) B1466405
theorem B1469123 : Blo 650305 1469123 := bstep (se 1 (by rfl) ⟨1101842, by rfl⟩ : syracuseStep 1469123 = 2203685) B2203685
theorem B977633 : Blo 650305 977633 := bstep (se 2 (by rfl) ⟨366612, by rfl⟩ : syracuseStep 977633 = 733225) B733225
theorem B1239779 : Blo 650305 1239779 := bstep (se 1 (by rfl) ⟨929834, by rfl⟩ : syracuseStep 1239779 = 1859669) B1859669
theorem B977651 : Blo 650305 977651 := bstep (se 1 (by rfl) ⟨733238, by rfl⟩ : syracuseStep 977651 = 1466477) B1466477
theorem B977681 : Blo 650305 977681 := bstep (se 2 (by rfl) ⟨366630, by rfl⟩ : syracuseStep 977681 = 733261) B733261
theorem B977699 : Blo 650305 977699 := bstep (se 1 (by rfl) ⟨733274, by rfl⟩ : syracuseStep 977699 = 1466549) B1466549
theorem B977729 : Blo 650305 977729 := bstep (se 2 (by rfl) ⟨366648, by rfl⟩ : syracuseStep 977729 = 733297) B733297
theorem B3533645 : Blo 650305 3533645 := bstep (se 3 (by rfl) ⟨662558, by rfl⟩ : syracuseStep 3533645 = 1325117) B1325117
theorem B977747 : Blo 650305 977747 := bstep (se 1 (by rfl) ⟨733310, by rfl⟩ : syracuseStep 977747 = 1466621) B1466621
theorem B977777 : Blo 650305 977777 := bstep (se 2 (by rfl) ⟨366666, by rfl⟩ : syracuseStep 977777 = 733333) B733333
theorem B977795 : Blo 650305 977795 := bstep (se 1 (by rfl) ⟨733346, by rfl⟩ : syracuseStep 977795 = 1466693) B1466693
theorem B977825 : Blo 650305 977825 := bstep (se 2 (by rfl) ⟨366684, by rfl⟩ : syracuseStep 977825 = 733369) B733369
theorem B977843 : Blo 650305 977843 := bstep (se 1 (by rfl) ⟨733382, by rfl⟩ : syracuseStep 977843 = 1466765) B1466765
theorem B977873 : Blo 650305 977873 := bstep (se 2 (by rfl) ⟨366702, by rfl⟩ : syracuseStep 977873 = 733405) B733405
theorem B1469393 : Blo 650305 1469393 := bstep (se 2 (by rfl) ⟨551022, by rfl⟩ : syracuseStep 1469393 = 1102045) B1102045
theorem B977891 : Blo 650305 977891 := bstep (se 1 (by rfl) ⟨733418, by rfl⟩ : syracuseStep 977891 = 1466837) B1466837
theorem B1469411 : Blo 650305 1469411 := bstep (se 1 (by rfl) ⟨1102058, by rfl⟩ : syracuseStep 1469411 = 2204117) B2204117
theorem B977921 : Blo 650305 977921 := bstep (se 2 (by rfl) ⟨366720, by rfl⟩ : syracuseStep 977921 = 733441) B733441
theorem B977939 : Blo 650305 977939 := bstep (se 1 (by rfl) ⟨733454, by rfl⟩ : syracuseStep 977939 = 1466909) B1466909
theorem B977969 : Blo 650305 977969 := bstep (se 2 (by rfl) ⟨366738, by rfl⟩ : syracuseStep 977969 = 733477) B733477
theorem B1043507 : Blo 650305 1043507 := bstep (se 1 (by rfl) ⟨782630, by rfl⟩ : syracuseStep 1043507 = 1565261) B1565261
theorem B650307 : Blo 650305 650307 := bstep (se 1 (by rfl) ⟨487730, by rfl⟩ : syracuseStep 650307 = 975461) B975461
theorem B977987 : Blo 650305 977987 := bstep (se 1 (by rfl) ⟨733490, by rfl⟩ : syracuseStep 977987 = 1466981) B1466981
theorem B1174609 : Blo 650305 1174609 := bstep (se 2 (by rfl) ⟨440478, by rfl⟩ : syracuseStep 1174609 = 880957) B880957
theorem B650323 : Blo 650305 650323 := bstep (se 1 (by rfl) ⟨487742, by rfl⟩ : syracuseStep 650323 = 975485) B975485
theorem B978017 : Blo 650305 978017 := bstep (se 2 (by rfl) ⟨366756, by rfl⟩ : syracuseStep 978017 = 733513) B733513
theorem B650339 : Blo 650305 650339 := bstep (se 1 (by rfl) ⟨487754, by rfl⟩ : syracuseStep 650339 = 975509) B975509
theorem B650355 : Blo 650305 650355 := bstep (se 1 (by rfl) ⟨487766, by rfl⟩ : syracuseStep 650355 = 975533) B975533
theorem B978035 : Blo 650305 978035 := bstep (se 1 (by rfl) ⟨733526, by rfl⟩ : syracuseStep 978035 = 1467053) B1467053
theorem B650371 : Blo 650305 650371 := bstep (se 1 (by rfl) ⟨487778, by rfl⟩ : syracuseStep 650371 = 975557) B975557
theorem B978065 : Blo 650305 978065 := bstep (se 2 (by rfl) ⟨366774, by rfl⟩ : syracuseStep 978065 = 733549) B733549
theorem B1862801 : Blo 650305 1862801 := bstep (se 2 (by rfl) ⟨698550, by rfl⟩ : syracuseStep 1862801 = 1397101) B1397101
theorem B650387 : Blo 650305 650387 := bstep (se 1 (by rfl) ⟨487790, by rfl⟩ : syracuseStep 650387 = 975581) B975581
theorem B650403 : Blo 650305 650403 := bstep (se 1 (by rfl) ⟨487802, by rfl⟩ : syracuseStep 650403 = 975605) B975605
theorem B978083 : Blo 650305 978083 := bstep (se 1 (by rfl) ⟨733562, by rfl⟩ : syracuseStep 978083 = 1467125) B1467125
theorem B650419 : Blo 650305 650419 := bstep (se 1 (by rfl) ⟨487814, by rfl⟩ : syracuseStep 650419 = 975629) B975629
theorem B978113 : Blo 650305 978113 := bstep (se 2 (by rfl) ⟨366792, by rfl⟩ : syracuseStep 978113 = 733585) B733585
theorem B650435 : Blo 650305 650435 := bstep (se 1 (by rfl) ⟨487826, by rfl⟩ : syracuseStep 650435 = 975653) B975653
theorem B650451 : Blo 650305 650451 := bstep (se 1 (by rfl) ⟨487838, by rfl⟩ : syracuseStep 650451 = 975677) B975677
theorem B978131 : Blo 650305 978131 := bstep (se 1 (by rfl) ⟨733598, by rfl⟩ : syracuseStep 978131 = 1467197) B1467197
theorem B650467 : Blo 650305 650467 := bstep (se 1 (by rfl) ⟨487850, by rfl⟩ : syracuseStep 650467 = 975701) B975701
theorem B978161 : Blo 650305 978161 := bstep (se 2 (by rfl) ⟨366810, by rfl⟩ : syracuseStep 978161 = 733621) B733621
theorem B1469681 : Blo 650305 1469681 := bstep (se 2 (by rfl) ⟨551130, by rfl⟩ : syracuseStep 1469681 = 1102261) B1102261
theorem B650483 : Blo 650305 650483 := bstep (se 1 (by rfl) ⟨487862, by rfl⟩ : syracuseStep 650483 = 975725) B975725
theorem B650499 : Blo 650305 650499 := bstep (se 1 (by rfl) ⟨487874, by rfl⟩ : syracuseStep 650499 = 975749) B975749
theorem B978179 : Blo 650305 978179 := bstep (se 1 (by rfl) ⟨733634, by rfl⟩ : syracuseStep 978179 = 1467269) B1467269
theorem B1469699 : Blo 650305 1469699 := bstep (se 1 (by rfl) ⟨1102274, by rfl⟩ : syracuseStep 1469699 = 2204549) B2204549
theorem B650515 : Blo 650305 650515 := bstep (se 1 (by rfl) ⟨487886, by rfl⟩ : syracuseStep 650515 = 975773) B975773
theorem B978209 : Blo 650305 978209 := bstep (se 2 (by rfl) ⟨366828, by rfl⟩ : syracuseStep 978209 = 733657) B733657
theorem B650531 : Blo 650305 650531 := bstep (se 1 (by rfl) ⟨487898, by rfl⟩ : syracuseStep 650531 = 975797) B975797
theorem B650547 : Blo 650305 650547 := bstep (se 1 (by rfl) ⟨487910, by rfl⟩ : syracuseStep 650547 = 975821) B975821
theorem B978227 : Blo 650305 978227 := bstep (se 1 (by rfl) ⟨733670, by rfl⟩ : syracuseStep 978227 = 1467341) B1467341
theorem B650563 : Blo 650305 650563 := bstep (se 1 (by rfl) ⟨487922, by rfl⟩ : syracuseStep 650563 = 975845) B975845
theorem B5008709 : Blo 650305 5008709 := bstep (se 4 (by rfl) ⟨469566, by rfl⟩ : syracuseStep 5008709 = 939133) B939133
theorem B978257 : Blo 650305 978257 := bstep (se 2 (by rfl) ⟨366846, by rfl⟩ : syracuseStep 978257 = 733693) B733693
theorem B650579 : Blo 650305 650579 := bstep (se 1 (by rfl) ⟨487934, by rfl⟩ : syracuseStep 650579 = 975869) B975869
theorem B650595 : Blo 650305 650595 := bstep (se 1 (by rfl) ⟨487946, by rfl⟩ : syracuseStep 650595 = 975893) B975893
theorem B978275 : Blo 650305 978275 := bstep (se 1 (by rfl) ⟨733706, by rfl⟩ : syracuseStep 978275 = 1467413) B1467413
theorem B3140977 : Blo 650305 3140977 := bstep (se 2 (by rfl) ⟨1177866, by rfl⟩ : syracuseStep 3140977 = 2355733) B2355733
theorem B650611 : Blo 650305 650611 := bstep (se 1 (by rfl) ⟨487958, by rfl⟩ : syracuseStep 650611 = 975917) B975917
theorem B978305 : Blo 650305 978305 := bstep (se 2 (by rfl) ⟨366864, by rfl⟩ : syracuseStep 978305 = 733729) B733729
theorem B650627 : Blo 650305 650627 := bstep (se 1 (by rfl) ⟨487970, by rfl⟩ : syracuseStep 650627 = 975941) B975941
theorem B650643 : Blo 650305 650643 := bstep (se 1 (by rfl) ⟨487982, by rfl⟩ : syracuseStep 650643 = 975965) B975965
theorem B978323 : Blo 650305 978323 := bstep (se 1 (by rfl) ⟨733742, by rfl⟩ : syracuseStep 978323 = 1467485) B1467485
theorem B650659 : Blo 650305 650659 := bstep (se 1 (by rfl) ⟨487994, by rfl⟩ : syracuseStep 650659 = 975989) B975989
theorem B978353 : Blo 650305 978353 := bstep (se 2 (by rfl) ⟨366882, by rfl⟩ : syracuseStep 978353 = 733765) B733765
theorem B650675 : Blo 650305 650675 := bstep (se 1 (by rfl) ⟨488006, by rfl⟩ : syracuseStep 650675 = 976013) B976013
theorem B650691 : Blo 650305 650691 := bstep (se 1 (by rfl) ⟨488018, by rfl⟩ : syracuseStep 650691 = 976037) B976037
theorem B978371 : Blo 650305 978371 := bstep (se 1 (by rfl) ⟨733778, by rfl⟩ : syracuseStep 978371 = 1467557) B1467557
theorem B650707 : Blo 650305 650707 := bstep (se 1 (by rfl) ⟨488030, by rfl⟩ : syracuseStep 650707 = 976061) B976061
theorem B978401 : Blo 650305 978401 := bstep (se 2 (by rfl) ⟨366900, by rfl⟩ : syracuseStep 978401 = 733801) B733801
theorem B650723 : Blo 650305 650723 := bstep (se 1 (by rfl) ⟨488042, by rfl⟩ : syracuseStep 650723 = 976085) B976085
theorem B650739 : Blo 650305 650739 := bstep (se 1 (by rfl) ⟨488054, by rfl⟩ : syracuseStep 650739 = 976109) B976109
theorem B978419 : Blo 650305 978419 := bstep (se 1 (by rfl) ⟨733814, by rfl⟩ : syracuseStep 978419 = 1467629) B1467629
theorem B650755 : Blo 650305 650755 := bstep (se 1 (by rfl) ⟨488066, by rfl⟩ : syracuseStep 650755 = 976133) B976133
theorem B978449 : Blo 650305 978449 := bstep (se 2 (by rfl) ⟨366918, by rfl⟩ : syracuseStep 978449 = 733837) B733837
theorem B1469969 : Blo 650305 1469969 := bstep (se 2 (by rfl) ⟨551238, by rfl⟩ : syracuseStep 1469969 = 1102477) B1102477
theorem B650771 : Blo 650305 650771 := bstep (se 1 (by rfl) ⟨488078, by rfl⟩ : syracuseStep 650771 = 976157) B976157
theorem B650787 : Blo 650305 650787 := bstep (se 1 (by rfl) ⟨488090, by rfl⟩ : syracuseStep 650787 = 976181) B976181
theorem B978467 : Blo 650305 978467 := bstep (se 1 (by rfl) ⟨733850, by rfl⟩ : syracuseStep 978467 = 1467701) B1467701
theorem B1469987 : Blo 650305 1469987 := bstep (se 1 (by rfl) ⟨1102490, by rfl⟩ : syracuseStep 1469987 = 2204981) B2204981
theorem B650803 : Blo 650305 650803 := bstep (se 1 (by rfl) ⟨488102, by rfl⟩ : syracuseStep 650803 = 976205) B976205
theorem B978497 : Blo 650305 978497 := bstep (se 2 (by rfl) ⟨366936, by rfl⟩ : syracuseStep 978497 = 733873) B733873
theorem B650819 : Blo 650305 650819 := bstep (se 1 (by rfl) ⟨488114, by rfl⟩ : syracuseStep 650819 = 976229) B976229
theorem B650835 : Blo 650305 650835 := bstep (se 1 (by rfl) ⟨488126, by rfl⟩ : syracuseStep 650835 = 976253) B976253
theorem B978515 : Blo 650305 978515 := bstep (se 1 (by rfl) ⟨733886, by rfl⟩ : syracuseStep 978515 = 1467773) B1467773
theorem B1044065 : Blo 650305 1044065 := bstep (se 2 (by rfl) ⟨391524, by rfl⟩ : syracuseStep 1044065 = 783049) B783049
theorem B650851 : Blo 650305 650851 := bstep (se 1 (by rfl) ⟨488138, by rfl⟩ : syracuseStep 650851 = 976277) B976277
theorem B978545 : Blo 650305 978545 := bstep (se 2 (by rfl) ⟨366954, by rfl⟩ : syracuseStep 978545 = 733909) B733909
theorem B650867 : Blo 650305 650867 := bstep (se 1 (by rfl) ⟨488150, by rfl⟩ : syracuseStep 650867 = 976301) B976301
theorem B650883 : Blo 650305 650883 := bstep (se 1 (by rfl) ⟨488162, by rfl⟩ : syracuseStep 650883 = 976325) B976325
theorem B978563 : Blo 650305 978563 := bstep (se 1 (by rfl) ⟨733922, by rfl⟩ : syracuseStep 978563 = 1467845) B1467845
theorem B650899 : Blo 650305 650899 := bstep (se 1 (by rfl) ⟨488174, by rfl⟩ : syracuseStep 650899 = 976349) B976349
theorem B978593 : Blo 650305 978593 := bstep (se 2 (by rfl) ⟨366972, by rfl⟩ : syracuseStep 978593 = 733945) B733945
theorem B650915 : Blo 650305 650915 := bstep (se 1 (by rfl) ⟨488186, by rfl⟩ : syracuseStep 650915 = 976373) B976373
theorem B781987 : Blo 650305 781987 := bstep (se 1 (by rfl) ⟨586490, by rfl⟩ : syracuseStep 781987 = 1172981) B1172981
theorem B3305123 : Blo 650305 3305123 := bstep (se 1 (by rfl) ⟨2478842, by rfl⟩ : syracuseStep 3305123 = 4957685) B4957685
theorem B650931 : Blo 650305 650931 := bstep (se 1 (by rfl) ⟨488198, by rfl⟩ : syracuseStep 650931 = 976397) B976397
theorem B978611 : Blo 650305 978611 := bstep (se 1 (by rfl) ⟨733958, by rfl⟩ : syracuseStep 978611 = 1467917) B1467917
theorem B650947 : Blo 650305 650947 := bstep (se 1 (by rfl) ⟨488210, by rfl⟩ : syracuseStep 650947 = 976421) B976421
theorem B978641 : Blo 650305 978641 := bstep (se 2 (by rfl) ⟨366990, by rfl⟩ : syracuseStep 978641 = 733981) B733981
theorem B650963 : Blo 650305 650963 := bstep (se 1 (by rfl) ⟨488222, by rfl⟩ : syracuseStep 650963 = 976445) B976445
theorem B650979 : Blo 650305 650979 := bstep (se 1 (by rfl) ⟨488234, by rfl⟩ : syracuseStep 650979 = 976469) B976469
theorem B978659 : Blo 650305 978659 := bstep (se 1 (by rfl) ⟨733994, by rfl⟩ : syracuseStep 978659 = 1467989) B1467989
theorem B650995 : Blo 650305 650995 := bstep (se 1 (by rfl) ⟨488246, by rfl⟩ : syracuseStep 650995 = 976493) B976493
theorem B978689 : Blo 650305 978689 := bstep (se 2 (by rfl) ⟨367008, by rfl⟩ : syracuseStep 978689 = 734017) B734017
theorem B651011 : Blo 650305 651011 := bstep (se 1 (by rfl) ⟨488258, by rfl⟩ : syracuseStep 651011 = 976517) B976517
theorem B1240849 : Blo 650305 1240849 := bstep (se 2 (by rfl) ⟨465318, by rfl⟩ : syracuseStep 1240849 = 930637) B930637
theorem B651027 : Blo 650305 651027 := bstep (se 1 (by rfl) ⟨488270, by rfl⟩ : syracuseStep 651027 = 976541) B976541
theorem B978707 : Blo 650305 978707 := bstep (se 1 (by rfl) ⟨734030, by rfl⟩ : syracuseStep 978707 = 1468061) B1468061
theorem B651043 : Blo 650305 651043 := bstep (se 1 (by rfl) ⟨488282, by rfl⟩ : syracuseStep 651043 = 976565) B976565
theorem B978737 : Blo 650305 978737 := bstep (se 2 (by rfl) ⟨367026, by rfl⟩ : syracuseStep 978737 = 734053) B734053
theorem B1470257 : Blo 650305 1470257 := bstep (se 2 (by rfl) ⟨551346, by rfl⟩ : syracuseStep 1470257 = 1102693) B1102693
theorem B782131 : Blo 650305 782131 := bstep (se 1 (by rfl) ⟨586598, by rfl⟩ : syracuseStep 782131 = 1173197) B1173197
theorem B651059 : Blo 650305 651059 := bstep (se 1 (by rfl) ⟨488294, by rfl⟩ : syracuseStep 651059 = 976589) B976589
theorem B1044289 : Blo 650305 1044289 := bstep (se 2 (by rfl) ⟨391608, by rfl⟩ : syracuseStep 1044289 = 783217) B783217
theorem B651075 : Blo 650305 651075 := bstep (se 1 (by rfl) ⟨488306, by rfl⟩ : syracuseStep 651075 = 976613) B976613
theorem B978755 : Blo 650305 978755 := bstep (se 1 (by rfl) ⟨734066, by rfl⟩ : syracuseStep 978755 = 1468133) B1468133
theorem B1470275 : Blo 650305 1470275 := bstep (se 1 (by rfl) ⟨1102706, by rfl⟩ : syracuseStep 1470275 = 2205413) B2205413
theorem B651091 : Blo 650305 651091 := bstep (se 1 (by rfl) ⟨488318, by rfl⟩ : syracuseStep 651091 = 976637) B976637
theorem B978785 : Blo 650305 978785 := bstep (se 2 (by rfl) ⟨367044, by rfl⟩ : syracuseStep 978785 = 734089) B734089
theorem B651107 : Blo 650305 651107 := bstep (se 1 (by rfl) ⟨488330, by rfl⟩ : syracuseStep 651107 = 976661) B976661
theorem B651123 : Blo 650305 651123 := bstep (se 1 (by rfl) ⟨488342, by rfl⟩ : syracuseStep 651123 = 976685) B976685
theorem B978803 : Blo 650305 978803 := bstep (se 1 (by rfl) ⟨734102, by rfl⟩ : syracuseStep 978803 = 1468205) B1468205
theorem B1044353 : Blo 650305 1044353 := bstep (se 2 (by rfl) ⟨391632, by rfl⟩ : syracuseStep 1044353 = 783265) B783265
theorem B651139 : Blo 650305 651139 := bstep (se 1 (by rfl) ⟨488354, by rfl⟩ : syracuseStep 651139 = 976709) B976709
theorem B978833 : Blo 650305 978833 := bstep (se 2 (by rfl) ⟨367062, by rfl⟩ : syracuseStep 978833 = 734125) B734125
theorem B782227 : Blo 650305 782227 := bstep (se 1 (by rfl) ⟨586670, by rfl⟩ : syracuseStep 782227 = 1173341) B1173341
theorem B651155 : Blo 650305 651155 := bstep (se 1 (by rfl) ⟨488366, by rfl⟩ : syracuseStep 651155 = 976733) B976733
theorem B651171 : Blo 650305 651171 := bstep (se 1 (by rfl) ⟨488378, by rfl⟩ : syracuseStep 651171 = 976757) B976757
theorem B978851 : Blo 650305 978851 := bstep (se 1 (by rfl) ⟨734138, by rfl⟩ : syracuseStep 978851 = 1468277) B1468277
theorem B651187 : Blo 650305 651187 := bstep (se 1 (by rfl) ⟨488390, by rfl⟩ : syracuseStep 651187 = 976781) B976781
theorem B978881 : Blo 650305 978881 := bstep (se 2 (by rfl) ⟨367080, by rfl⟩ : syracuseStep 978881 = 734161) B734161
theorem B651203 : Blo 650305 651203 := bstep (se 1 (by rfl) ⟨488402, by rfl⟩ : syracuseStep 651203 = 976805) B976805
theorem B651219 : Blo 650305 651219 := bstep (se 1 (by rfl) ⟨488414, by rfl⟩ : syracuseStep 651219 = 976829) B976829
theorem B978899 : Blo 650305 978899 := bstep (se 1 (by rfl) ⟨734174, by rfl⟩ : syracuseStep 978899 = 1468349) B1468349
theorem B651235 : Blo 650305 651235 := bstep (se 1 (by rfl) ⟨488426, by rfl⟩ : syracuseStep 651235 = 976853) B976853
theorem B978929 : Blo 650305 978929 := bstep (se 2 (by rfl) ⟨367098, by rfl⟩ : syracuseStep 978929 = 734197) B734197
theorem B651251 : Blo 650305 651251 := bstep (se 1 (by rfl) ⟨488438, by rfl⟩ : syracuseStep 651251 = 976877) B976877
theorem B1044481 : Blo 650305 1044481 := bstep (se 2 (by rfl) ⟨391680, by rfl⟩ : syracuseStep 1044481 = 783361) B783361
theorem B651267 : Blo 650305 651267 := bstep (se 1 (by rfl) ⟨488450, by rfl⟩ : syracuseStep 651267 = 976901) B976901
theorem B978947 : Blo 650305 978947 := bstep (se 1 (by rfl) ⟨734210, by rfl⟩ : syracuseStep 978947 = 1468421) B1468421
theorem B651283 : Blo 650305 651283 := bstep (se 1 (by rfl) ⟨488462, by rfl⟩ : syracuseStep 651283 = 976925) B976925
theorem B978977 : Blo 650305 978977 := bstep (se 2 (by rfl) ⟨367116, by rfl⟩ : syracuseStep 978977 = 734233) B734233
theorem B651299 : Blo 650305 651299 := bstep (se 1 (by rfl) ⟨488474, by rfl⟩ : syracuseStep 651299 = 976949) B976949
theorem B651315 : Blo 650305 651315 := bstep (se 1 (by rfl) ⟨488486, by rfl⟩ : syracuseStep 651315 = 976973) B976973
theorem B978995 : Blo 650305 978995 := bstep (se 1 (by rfl) ⟨734246, by rfl⟩ : syracuseStep 978995 = 1468493) B1468493
theorem B651331 : Blo 650305 651331 := bstep (se 1 (by rfl) ⟨488498, by rfl⟩ : syracuseStep 651331 = 976997) B976997
theorem B979025 : Blo 650305 979025 := bstep (se 2 (by rfl) ⟨367134, by rfl⟩ : syracuseStep 979025 = 734269) B734269
theorem B1470545 : Blo 650305 1470545 := bstep (se 2 (by rfl) ⟨551454, by rfl⟩ : syracuseStep 1470545 = 1102909) B1102909
theorem B651347 : Blo 650305 651347 := bstep (se 1 (by rfl) ⟨488510, by rfl⟩ : syracuseStep 651347 = 977021) B977021
theorem B651363 : Blo 650305 651363 := bstep (se 1 (by rfl) ⟨488522, by rfl⟩ : syracuseStep 651363 = 977045) B977045
theorem B979043 : Blo 650305 979043 := bstep (se 1 (by rfl) ⟨734282, by rfl⟩ : syracuseStep 979043 = 1468565) B1468565
theorem B1470563 : Blo 650305 1470563 := bstep (se 1 (by rfl) ⟨1102922, by rfl⟩ : syracuseStep 1470563 = 2205845) B2205845
theorem B2093165 : Blo 650305 2093165 := bstep (se 3 (by rfl) ⟨392468, by rfl⟩ : syracuseStep 2093165 = 784937) B784937
theorem B651379 : Blo 650305 651379 := bstep (se 1 (by rfl) ⟨488534, by rfl⟩ : syracuseStep 651379 = 977069) B977069
theorem B979073 : Blo 650305 979073 := bstep (se 2 (by rfl) ⟨367152, by rfl⟩ : syracuseStep 979073 = 734305) B734305
theorem B651395 : Blo 650305 651395 := bstep (se 1 (by rfl) ⟨488546, by rfl⟩ : syracuseStep 651395 = 977093) B977093
theorem B651411 : Blo 650305 651411 := bstep (se 1 (by rfl) ⟨488558, by rfl⟩ : syracuseStep 651411 = 977117) B977117
theorem B979091 : Blo 650305 979091 := bstep (se 1 (by rfl) ⟨734318, by rfl⟩ : syracuseStep 979091 = 1468637) B1468637
theorem B651427 : Blo 650305 651427 := bstep (se 1 (by rfl) ⟨488570, by rfl⟩ : syracuseStep 651427 = 977141) B977141
theorem B979121 : Blo 650305 979121 := bstep (se 2 (by rfl) ⟨367170, by rfl⟩ : syracuseStep 979121 = 734341) B734341
theorem B651443 : Blo 650305 651443 := bstep (se 1 (by rfl) ⟨488582, by rfl⟩ : syracuseStep 651443 = 977165) B977165
theorem B651459 : Blo 650305 651459 := bstep (se 1 (by rfl) ⟨488594, by rfl⟩ : syracuseStep 651459 = 977189) B977189
theorem B979139 : Blo 650305 979139 := bstep (se 1 (by rfl) ⟨734354, by rfl⟩ : syracuseStep 979139 = 1468709) B1468709
theorem B651475 : Blo 650305 651475 := bstep (se 1 (by rfl) ⟨488606, by rfl⟩ : syracuseStep 651475 = 977213) B977213
theorem B979169 : Blo 650305 979169 := bstep (se 2 (by rfl) ⟨367188, by rfl⟩ : syracuseStep 979169 = 734377) B734377
theorem B651491 : Blo 650305 651491 := bstep (se 1 (by rfl) ⟨488618, by rfl⟩ : syracuseStep 651491 = 977237) B977237
theorem B2093293 : Blo 650305 2093293 := bstep (se 3 (by rfl) ⟨392492, by rfl⟩ : syracuseStep 2093293 = 784985) B784985
theorem B651507 : Blo 650305 651507 := bstep (se 1 (by rfl) ⟨488630, by rfl⟩ : syracuseStep 651507 = 977261) B977261
theorem B979187 : Blo 650305 979187 := bstep (se 1 (by rfl) ⟨734390, by rfl⟩ : syracuseStep 979187 = 1468781) B1468781
theorem B651523 : Blo 650305 651523 := bstep (se 1 (by rfl) ⟨488642, by rfl⟩ : syracuseStep 651523 = 977285) B977285
theorem B979217 : Blo 650305 979217 := bstep (se 2 (by rfl) ⟨367206, by rfl⟩ : syracuseStep 979217 = 734413) B734413
theorem B651539 : Blo 650305 651539 := bstep (se 1 (by rfl) ⟨488654, by rfl⟩ : syracuseStep 651539 = 977309) B977309
theorem B651555 : Blo 650305 651555 := bstep (se 1 (by rfl) ⟨488666, by rfl⟩ : syracuseStep 651555 = 977333) B977333
theorem B979235 : Blo 650305 979235 := bstep (se 1 (by rfl) ⟨734426, by rfl⟩ : syracuseStep 979235 = 1468853) B1468853
theorem B651571 : Blo 650305 651571 := bstep (se 1 (by rfl) ⟨488678, by rfl⟩ : syracuseStep 651571 = 977357) B977357
theorem B979265 : Blo 650305 979265 := bstep (se 2 (by rfl) ⟨367224, by rfl⟩ : syracuseStep 979265 = 734449) B734449
theorem B651587 : Blo 650305 651587 := bstep (se 1 (by rfl) ⟨488690, by rfl⟩ : syracuseStep 651587 = 977381) B977381
theorem B651603 : Blo 650305 651603 := bstep (se 1 (by rfl) ⟨488702, by rfl⟩ : syracuseStep 651603 = 977405) B977405
theorem B979283 : Blo 650305 979283 := bstep (se 1 (by rfl) ⟨734462, by rfl⟩ : syracuseStep 979283 = 1468925) B1468925
theorem B651619 : Blo 650305 651619 := bstep (se 1 (by rfl) ⟨488714, by rfl⟩ : syracuseStep 651619 = 977429) B977429
theorem B979313 : Blo 650305 979313 := bstep (se 2 (by rfl) ⟨367242, by rfl⟩ : syracuseStep 979313 = 734485) B734485
theorem B1470833 : Blo 650305 1470833 := bstep (se 2 (by rfl) ⟨551562, by rfl⟩ : syracuseStep 1470833 = 1103125) B1103125
theorem B782707 : Blo 650305 782707 := bstep (se 1 (by rfl) ⟨587030, by rfl⟩ : syracuseStep 782707 = 1174061) B1174061
theorem B651635 : Blo 650305 651635 := bstep (se 1 (by rfl) ⟨488726, by rfl⟩ : syracuseStep 651635 = 977453) B977453
theorem B651651 : Blo 650305 651651 := bstep (se 1 (by rfl) ⟨488738, by rfl⟩ : syracuseStep 651651 = 977477) B977477
theorem B979331 : Blo 650305 979331 := bstep (se 1 (by rfl) ⟨734498, by rfl⟩ : syracuseStep 979331 = 1468997) B1468997
theorem B1765763 : Blo 650305 1765763 := bstep (se 1 (by rfl) ⟨1324322, by rfl⟩ : syracuseStep 1765763 = 2648645) B2648645
theorem B1470851 : Blo 650305 1470851 := bstep (se 1 (by rfl) ⟨1103138, by rfl⟩ : syracuseStep 1470851 = 2206277) B2206277
theorem B651667 : Blo 650305 651667 := bstep (se 1 (by rfl) ⟨488750, by rfl⟩ : syracuseStep 651667 = 977501) B977501
theorem B979361 : Blo 650305 979361 := bstep (se 2 (by rfl) ⟨367260, by rfl⟩ : syracuseStep 979361 = 734521) B734521
theorem B651683 : Blo 650305 651683 := bstep (se 1 (by rfl) ⟨488762, by rfl⟩ : syracuseStep 651683 = 977525) B977525
theorem B651699 : Blo 650305 651699 := bstep (se 1 (by rfl) ⟨488774, by rfl⟩ : syracuseStep 651699 = 977549) B977549
theorem B979379 : Blo 650305 979379 := bstep (se 1 (by rfl) ⟨734534, by rfl⟩ : syracuseStep 979379 = 1469069) B1469069
theorem B651715 : Blo 650305 651715 := bstep (se 1 (by rfl) ⟨488786, by rfl⟩ : syracuseStep 651715 = 977573) B977573
theorem B3305933 : Blo 650305 3305933 := bstep (se 3 (by rfl) ⟨619862, by rfl⟩ : syracuseStep 3305933 = 1239725) B1239725
theorem B979409 : Blo 650305 979409 := bstep (se 2 (by rfl) ⟨367278, by rfl⟩ : syracuseStep 979409 = 734557) B734557
theorem B651731 : Blo 650305 651731 := bstep (se 1 (by rfl) ⟨488798, by rfl⟩ : syracuseStep 651731 = 977597) B977597
theorem B651747 : Blo 650305 651747 := bstep (se 1 (by rfl) ⟨488810, by rfl⟩ : syracuseStep 651747 = 977621) B977621
theorem B979427 : Blo 650305 979427 := bstep (se 1 (by rfl) ⟨734570, by rfl⟩ : syracuseStep 979427 = 1469141) B1469141
theorem B651763 : Blo 650305 651763 := bstep (se 1 (by rfl) ⟨488822, by rfl⟩ : syracuseStep 651763 = 977645) B977645
theorem B979457 : Blo 650305 979457 := bstep (se 2 (by rfl) ⟨367296, by rfl⟩ : syracuseStep 979457 = 734593) B734593
theorem B651779 : Blo 650305 651779 := bstep (se 1 (by rfl) ⟨488834, by rfl⟩ : syracuseStep 651779 = 977669) B977669
theorem B651795 : Blo 650305 651795 := bstep (se 1 (by rfl) ⟨488846, by rfl⟩ : syracuseStep 651795 = 977693) B977693
theorem B979475 : Blo 650305 979475 := bstep (se 1 (by rfl) ⟨734606, by rfl⟩ : syracuseStep 979475 = 1469213) B1469213
theorem B651811 : Blo 650305 651811 := bstep (se 1 (by rfl) ⟨488858, by rfl⟩ : syracuseStep 651811 = 977717) B977717
theorem B979505 : Blo 650305 979505 := bstep (se 2 (by rfl) ⟨367314, by rfl⟩ : syracuseStep 979505 = 734629) B734629
theorem B651827 : Blo 650305 651827 := bstep (se 1 (by rfl) ⟨488870, by rfl⟩ : syracuseStep 651827 = 977741) B977741
theorem B651843 : Blo 650305 651843 := bstep (se 1 (by rfl) ⟨488882, by rfl⟩ : syracuseStep 651843 = 977765) B977765
theorem B979523 : Blo 650305 979523 := bstep (se 1 (by rfl) ⟨734642, by rfl⟩ : syracuseStep 979523 = 1469285) B1469285
theorem B651859 : Blo 650305 651859 := bstep (se 1 (by rfl) ⟨488894, by rfl⟩ : syracuseStep 651859 = 977789) B977789
theorem B979553 : Blo 650305 979553 := bstep (se 2 (by rfl) ⟨367332, by rfl⟩ : syracuseStep 979553 = 734665) B734665
theorem B651875 : Blo 650305 651875 := bstep (se 1 (by rfl) ⟨488906, by rfl⟩ : syracuseStep 651875 = 977813) B977813
theorem B651891 : Blo 650305 651891 := bstep (se 1 (by rfl) ⟨488918, by rfl⟩ : syracuseStep 651891 = 977837) B977837
theorem B979571 : Blo 650305 979571 := bstep (se 1 (by rfl) ⟨734678, by rfl⟩ : syracuseStep 979571 = 1469357) B1469357
theorem B651907 : Blo 650305 651907 := bstep (se 1 (by rfl) ⟨488930, by rfl⟩ : syracuseStep 651907 = 977861) B977861
theorem B979601 : Blo 650305 979601 := bstep (se 2 (by rfl) ⟨367350, by rfl⟩ : syracuseStep 979601 = 734701) B734701
theorem B1471121 : Blo 650305 1471121 := bstep (se 2 (by rfl) ⟨551670, by rfl⟩ : syracuseStep 1471121 = 1103341) B1103341
theorem B651923 : Blo 650305 651923 := bstep (se 1 (by rfl) ⟨488942, by rfl⟩ : syracuseStep 651923 = 977885) B977885
theorem B651939 : Blo 650305 651939 := bstep (se 1 (by rfl) ⟨488954, by rfl⟩ : syracuseStep 651939 = 977909) B977909
theorem B979619 : Blo 650305 979619 := bstep (se 1 (by rfl) ⟨734714, by rfl⟩ : syracuseStep 979619 = 1469429) B1469429
theorem B1471139 : Blo 650305 1471139 := bstep (se 1 (by rfl) ⟨1103354, by rfl⟩ : syracuseStep 1471139 = 2206709) B2206709
theorem B651955 : Blo 650305 651955 := bstep (se 1 (by rfl) ⟨488966, by rfl⟩ : syracuseStep 651955 = 977933) B977933
theorem B979649 : Blo 650305 979649 := bstep (se 2 (by rfl) ⟨367368, by rfl⟩ : syracuseStep 979649 = 734737) B734737
theorem B651971 : Blo 650305 651971 := bstep (se 1 (by rfl) ⟨488978, by rfl⟩ : syracuseStep 651971 = 977957) B977957
theorem B3764933 : Blo 650305 3764933 := bstep (se 4 (by rfl) ⟨352962, by rfl⟩ : syracuseStep 3764933 = 705925) B705925
theorem B651987 : Blo 650305 651987 := bstep (se 1 (by rfl) ⟨488990, by rfl⟩ : syracuseStep 651987 = 977981) B977981
theorem B979667 : Blo 650305 979667 := bstep (se 1 (by rfl) ⟨734750, by rfl⟩ : syracuseStep 979667 = 1469501) B1469501
theorem B652003 : Blo 650305 652003 := bstep (se 1 (by rfl) ⟨489002, by rfl⟩ : syracuseStep 652003 = 978005) B978005
theorem B979697 : Blo 650305 979697 := bstep (se 2 (by rfl) ⟨367386, by rfl⟩ : syracuseStep 979697 = 734773) B734773
theorem B652019 : Blo 650305 652019 := bstep (se 1 (by rfl) ⟨489014, by rfl⟩ : syracuseStep 652019 = 978029) B978029
theorem B652035 : Blo 650305 652035 := bstep (se 1 (by rfl) ⟨489026, by rfl⟩ : syracuseStep 652035 = 978053) B978053
theorem B979715 : Blo 650305 979715 := bstep (se 1 (by rfl) ⟨734786, by rfl⟩ : syracuseStep 979715 = 1469573) B1469573
theorem B652051 : Blo 650305 652051 := bstep (se 1 (by rfl) ⟨489038, by rfl⟩ : syracuseStep 652051 = 978077) B978077
theorem B979745 : Blo 650305 979745 := bstep (se 2 (by rfl) ⟨367404, by rfl⟩ : syracuseStep 979745 = 734809) B734809
theorem B652067 : Blo 650305 652067 := bstep (se 1 (by rfl) ⟨489050, by rfl⟩ : syracuseStep 652067 = 978101) B978101
theorem B2782001 : Blo 650305 2782001 := bstep (se 2 (by rfl) ⟨1043250, by rfl⟩ : syracuseStep 2782001 = 2086501) B2086501
theorem B1241905 : Blo 650305 1241905 := bstep (se 2 (by rfl) ⟨465714, by rfl⟩ : syracuseStep 1241905 = 931429) B931429
theorem B652083 : Blo 650305 652083 := bstep (se 1 (by rfl) ⟨489062, by rfl⟩ : syracuseStep 652083 = 978125) B978125
theorem B979763 : Blo 650305 979763 := bstep (se 1 (by rfl) ⟨734822, by rfl⟩ : syracuseStep 979763 = 1469645) B1469645
theorem B652099 : Blo 650305 652099 := bstep (se 1 (by rfl) ⟨489074, by rfl⟩ : syracuseStep 652099 = 978149) B978149
theorem B979793 : Blo 650305 979793 := bstep (se 2 (by rfl) ⟨367422, by rfl⟩ : syracuseStep 979793 = 734845) B734845
theorem B652115 : Blo 650305 652115 := bstep (se 1 (by rfl) ⟨489086, by rfl⟩ : syracuseStep 652115 = 978173) B978173
theorem B652131 : Blo 650305 652131 := bstep (se 1 (by rfl) ⟨489098, by rfl⟩ : syracuseStep 652131 = 978197) B978197
theorem B1176419 : Blo 650305 1176419 := bstep (se 1 (by rfl) ⟨882314, by rfl⟩ : syracuseStep 1176419 = 1764629) B1764629
theorem B979811 : Blo 650305 979811 := bstep (se 1 (by rfl) ⟨734858, by rfl⟩ : syracuseStep 979811 = 1469717) B1469717
theorem B2356067 : Blo 650305 2356067 := bstep (se 1 (by rfl) ⟨1767050, by rfl⟩ : syracuseStep 2356067 = 3534101) B3534101
theorem B652147 : Blo 650305 652147 := bstep (se 1 (by rfl) ⟨489110, by rfl⟩ : syracuseStep 652147 = 978221) B978221
theorem B979841 : Blo 650305 979841 := bstep (se 2 (by rfl) ⟨367440, by rfl⟩ : syracuseStep 979841 = 734881) B734881
theorem B652163 : Blo 650305 652163 := bstep (se 1 (by rfl) ⟨489122, by rfl⟩ : syracuseStep 652163 = 978245) B978245
theorem B652179 : Blo 650305 652179 := bstep (se 1 (by rfl) ⟨489134, by rfl⟩ : syracuseStep 652179 = 978269) B978269
theorem B979859 : Blo 650305 979859 := bstep (se 1 (by rfl) ⟨734894, by rfl⟩ : syracuseStep 979859 = 1469789) B1469789
theorem B652195 : Blo 650305 652195 := bstep (se 1 (by rfl) ⟨489146, by rfl⟩ : syracuseStep 652195 = 978293) B978293
theorem B979889 : Blo 650305 979889 := bstep (se 2 (by rfl) ⟨367458, by rfl⟩ : syracuseStep 979889 = 734917) B734917
theorem B1471409 : Blo 650305 1471409 := bstep (se 2 (by rfl) ⟨551778, by rfl⟩ : syracuseStep 1471409 = 1103557) B1103557
theorem B652211 : Blo 650305 652211 := bstep (se 1 (by rfl) ⟨489158, by rfl⟩ : syracuseStep 652211 = 978317) B978317
theorem B652227 : Blo 650305 652227 := bstep (se 1 (by rfl) ⟨489170, by rfl⟩ : syracuseStep 652227 = 978341) B978341
theorem B979907 : Blo 650305 979907 := bstep (se 1 (by rfl) ⟨734930, by rfl⟩ : syracuseStep 979907 = 1469861) B1469861
theorem B1471427 : Blo 650305 1471427 := bstep (se 1 (by rfl) ⟨1103570, by rfl⟩ : syracuseStep 1471427 = 2207141) B2207141
theorem B652243 : Blo 650305 652243 := bstep (se 1 (by rfl) ⟨489182, by rfl⟩ : syracuseStep 652243 = 978365) B978365
theorem B979937 : Blo 650305 979937 := bstep (se 2 (by rfl) ⟨367476, by rfl⟩ : syracuseStep 979937 = 734953) B734953
theorem B652259 : Blo 650305 652259 := bstep (se 1 (by rfl) ⟨489194, by rfl⟩ : syracuseStep 652259 = 978389) B978389
theorem B652275 : Blo 650305 652275 := bstep (se 1 (by rfl) ⟨489206, by rfl⟩ : syracuseStep 652275 = 978413) B978413
theorem B979955 : Blo 650305 979955 := bstep (se 1 (by rfl) ⟨734966, by rfl⟩ : syracuseStep 979955 = 1469933) B1469933
theorem B652291 : Blo 650305 652291 := bstep (se 1 (by rfl) ⟨489218, by rfl⟩ : syracuseStep 652291 = 978437) B978437
theorem B979985 : Blo 650305 979985 := bstep (se 2 (by rfl) ⟨367494, by rfl⟩ : syracuseStep 979985 = 734989) B734989
theorem B652307 : Blo 650305 652307 := bstep (se 1 (by rfl) ⟨489230, by rfl⟩ : syracuseStep 652307 = 978461) B978461
theorem B652323 : Blo 650305 652323 := bstep (se 1 (by rfl) ⟨489242, by rfl⟩ : syracuseStep 652323 = 978485) B978485
theorem B980003 : Blo 650305 980003 := bstep (se 1 (by rfl) ⟨735002, by rfl⟩ : syracuseStep 980003 = 1470005) B1470005
theorem B652339 : Blo 650305 652339 := bstep (se 1 (by rfl) ⟨489254, by rfl⟩ : syracuseStep 652339 = 978509) B978509
theorem B980033 : Blo 650305 980033 := bstep (se 2 (by rfl) ⟨367512, by rfl⟩ : syracuseStep 980033 = 735025) B735025
theorem B652355 : Blo 650305 652355 := bstep (se 1 (by rfl) ⟨489266, by rfl⟩ : syracuseStep 652355 = 978533) B978533
theorem B652371 : Blo 650305 652371 := bstep (se 1 (by rfl) ⟨489278, by rfl⟩ : syracuseStep 652371 = 978557) B978557
theorem B980051 : Blo 650305 980051 := bstep (se 1 (by rfl) ⟨735038, by rfl⟩ : syracuseStep 980051 = 1470077) B1470077
theorem B652387 : Blo 650305 652387 := bstep (se 1 (by rfl) ⟨489290, by rfl⟩ : syracuseStep 652387 = 978581) B978581
theorem B980081 : Blo 650305 980081 := bstep (se 2 (by rfl) ⟨367530, by rfl⟩ : syracuseStep 980081 = 735061) B735061
theorem B652403 : Blo 650305 652403 := bstep (se 1 (by rfl) ⟨489302, by rfl⟩ : syracuseStep 652403 = 978605) B978605
theorem B652419 : Blo 650305 652419 := bstep (se 1 (by rfl) ⟨489314, by rfl⟩ : syracuseStep 652419 = 978629) B978629
theorem B980099 : Blo 650305 980099 := bstep (se 1 (by rfl) ⟨735074, by rfl⟩ : syracuseStep 980099 = 1470149) B1470149
theorem B652435 : Blo 650305 652435 := bstep (se 1 (by rfl) ⟨489326, by rfl⟩ : syracuseStep 652435 = 978653) B978653
theorem B980129 : Blo 650305 980129 := bstep (se 2 (by rfl) ⟨367548, by rfl⟩ : syracuseStep 980129 = 735097) B735097
theorem B652451 : Blo 650305 652451 := bstep (se 1 (by rfl) ⟨489338, by rfl⟩ : syracuseStep 652451 = 978677) B978677
theorem B652467 : Blo 650305 652467 := bstep (se 1 (by rfl) ⟨489350, by rfl⟩ : syracuseStep 652467 = 978701) B978701
theorem B980147 : Blo 650305 980147 := bstep (se 1 (by rfl) ⟨735110, by rfl⟩ : syracuseStep 980147 = 1470221) B1470221
theorem B652483 : Blo 650305 652483 := bstep (se 1 (by rfl) ⟨489362, by rfl⟩ : syracuseStep 652483 = 978725) B978725
theorem B980177 : Blo 650305 980177 := bstep (se 2 (by rfl) ⟨367566, by rfl⟩ : syracuseStep 980177 = 735133) B735133
theorem B1471697 : Blo 650305 1471697 := bstep (se 2 (by rfl) ⟨551886, by rfl⟩ : syracuseStep 1471697 = 1103773) B1103773
theorem B652499 : Blo 650305 652499 := bstep (se 1 (by rfl) ⟨489374, by rfl⟩ : syracuseStep 652499 = 978749) B978749
theorem B652515 : Blo 650305 652515 := bstep (se 1 (by rfl) ⟨489386, by rfl⟩ : syracuseStep 652515 = 978773) B978773
theorem B980195 : Blo 650305 980195 := bstep (se 1 (by rfl) ⟨735146, by rfl⟩ : syracuseStep 980195 = 1470293) B1470293
theorem B1766627 : Blo 650305 1766627 := bstep (se 1 (by rfl) ⟨1324970, by rfl⟩ : syracuseStep 1766627 = 2649941) B2649941
theorem B1471715 : Blo 650305 1471715 := bstep (se 1 (by rfl) ⟨1103786, by rfl⟩ : syracuseStep 1471715 = 2207573) B2207573
theorem B652531 : Blo 650305 652531 := bstep (se 1 (by rfl) ⟨489398, by rfl⟩ : syracuseStep 652531 = 978797) B978797
theorem B980225 : Blo 650305 980225 := bstep (se 2 (by rfl) ⟨367584, by rfl⟩ : syracuseStep 980225 = 735169) B735169
theorem B652547 : Blo 650305 652547 := bstep (se 1 (by rfl) ⟨489410, by rfl⟩ : syracuseStep 652547 = 978821) B978821
theorem B652563 : Blo 650305 652563 := bstep (se 1 (by rfl) ⟨489422, by rfl⟩ : syracuseStep 652563 = 978845) B978845
theorem B980243 : Blo 650305 980243 := bstep (se 1 (by rfl) ⟨735182, by rfl⟩ : syracuseStep 980243 = 1470365) B1470365
theorem B652579 : Blo 650305 652579 := bstep (se 1 (by rfl) ⟨489434, by rfl⟩ : syracuseStep 652579 = 978869) B978869
theorem B2389283 : Blo 650305 2389283 := bstep (se 1 (by rfl) ⟨1791962, by rfl⟩ : syracuseStep 2389283 = 3583925) B3583925
theorem B3437873 : Blo 650305 3437873 := bstep (se 2 (by rfl) ⟨1289202, by rfl⟩ : syracuseStep 3437873 = 2578405) B2578405
theorem B980273 : Blo 650305 980273 := bstep (se 2 (by rfl) ⟨367602, by rfl⟩ : syracuseStep 980273 = 735205) B735205
theorem B652595 : Blo 650305 652595 := bstep (se 1 (by rfl) ⟨489446, by rfl⟩ : syracuseStep 652595 = 978893) B978893
theorem B652611 : Blo 650305 652611 := bstep (se 1 (by rfl) ⟨489458, by rfl⟩ : syracuseStep 652611 = 978917) B978917
theorem B980291 : Blo 650305 980291 := bstep (se 1 (by rfl) ⟨735218, by rfl⟩ : syracuseStep 980291 = 1470437) B1470437
theorem B652627 : Blo 650305 652627 := bstep (se 1 (by rfl) ⟨489470, by rfl⟩ : syracuseStep 652627 = 978941) B978941
theorem B980321 : Blo 650305 980321 := bstep (se 2 (by rfl) ⟨367620, by rfl⟩ : syracuseStep 980321 = 735241) B735241
theorem B652643 : Blo 650305 652643 := bstep (se 1 (by rfl) ⟨489482, by rfl⟩ : syracuseStep 652643 = 978965) B978965
theorem B652659 : Blo 650305 652659 := bstep (se 1 (by rfl) ⟨489494, by rfl⟩ : syracuseStep 652659 = 978989) B978989
theorem B980339 : Blo 650305 980339 := bstep (se 1 (by rfl) ⟨735254, by rfl⟩ : syracuseStep 980339 = 1470509) B1470509
theorem B652675 : Blo 650305 652675 := bstep (se 1 (by rfl) ⟨489506, by rfl⟩ : syracuseStep 652675 = 979013) B979013
theorem B3143053 : Blo 650305 3143053 := bstep (se 3 (by rfl) ⟨589322, by rfl⟩ : syracuseStep 3143053 = 1178645) B1178645
theorem B980369 : Blo 650305 980369 := bstep (se 2 (by rfl) ⟨367638, by rfl⟩ : syracuseStep 980369 = 735277) B735277
theorem B652691 : Blo 650305 652691 := bstep (se 1 (by rfl) ⟨489518, by rfl⟩ : syracuseStep 652691 = 979037) B979037
theorem B652707 : Blo 650305 652707 := bstep (se 1 (by rfl) ⟨489530, by rfl⟩ : syracuseStep 652707 = 979061) B979061
theorem B980387 : Blo 650305 980387 := bstep (se 1 (by rfl) ⟨735290, by rfl⟩ : syracuseStep 980387 = 1470581) B1470581
theorem B652723 : Blo 650305 652723 := bstep (se 1 (by rfl) ⟨489542, by rfl⟩ : syracuseStep 652723 = 979085) B979085
theorem B980417 : Blo 650305 980417 := bstep (se 2 (by rfl) ⟨367656, by rfl⟩ : syracuseStep 980417 = 735313) B735313
theorem B652739 : Blo 650305 652739 := bstep (se 1 (by rfl) ⟨489554, by rfl⟩ : syracuseStep 652739 = 979109) B979109
theorem B652755 : Blo 650305 652755 := bstep (se 1 (by rfl) ⟨489566, by rfl⟩ : syracuseStep 652755 = 979133) B979133
theorem B980435 : Blo 650305 980435 := bstep (se 1 (by rfl) ⟨735326, by rfl⟩ : syracuseStep 980435 = 1470653) B1470653
theorem B652771 : Blo 650305 652771 := bstep (se 1 (by rfl) ⟨489578, by rfl⟩ : syracuseStep 652771 = 979157) B979157
theorem B980465 : Blo 650305 980465 := bstep (se 2 (by rfl) ⟨367674, by rfl⟩ : syracuseStep 980465 = 735349) B735349
theorem B3536369 : Blo 650305 3536369 := bstep (se 2 (by rfl) ⟨1326138, by rfl⟩ : syracuseStep 3536369 = 2652277) B2652277
theorem B652787 : Blo 650305 652787 := bstep (se 1 (by rfl) ⟨489590, by rfl⟩ : syracuseStep 652787 = 979181) B979181
theorem B1471985 : Blo 650305 1471985 := bstep (se 2 (by rfl) ⟨551994, by rfl⟩ : syracuseStep 1471985 = 1103989) B1103989
theorem B652803 : Blo 650305 652803 := bstep (se 1 (by rfl) ⟨489602, by rfl⟩ : syracuseStep 652803 = 979205) B979205
theorem B980483 : Blo 650305 980483 := bstep (se 1 (by rfl) ⟨735362, by rfl⟩ : syracuseStep 980483 = 1470725) B1470725
theorem B1472003 : Blo 650305 1472003 := bstep (se 1 (by rfl) ⟨1104002, by rfl⟩ : syracuseStep 1472003 = 2208005) B2208005
theorem B652819 : Blo 650305 652819 := bstep (se 1 (by rfl) ⟨489614, by rfl⟩ : syracuseStep 652819 = 979229) B979229
theorem B980513 : Blo 650305 980513 := bstep (se 2 (by rfl) ⟨367692, by rfl⟩ : syracuseStep 980513 = 735385) B735385
theorem B652835 : Blo 650305 652835 := bstep (se 1 (by rfl) ⟨489626, by rfl⟩ : syracuseStep 652835 = 979253) B979253
theorem B652851 : Blo 650305 652851 := bstep (se 1 (by rfl) ⟨489638, by rfl⟩ : syracuseStep 652851 = 979277) B979277
theorem B980531 : Blo 650305 980531 := bstep (se 1 (by rfl) ⟨735398, by rfl⟩ : syracuseStep 980531 = 1470797) B1470797
theorem B652867 : Blo 650305 652867 := bstep (se 1 (by rfl) ⟨489650, by rfl⟩ : syracuseStep 652867 = 979301) B979301
theorem B980561 : Blo 650305 980561 := bstep (se 2 (by rfl) ⟨367710, by rfl⟩ : syracuseStep 980561 = 735421) B735421
theorem B652883 : Blo 650305 652883 := bstep (se 1 (by rfl) ⟨489662, by rfl⟩ : syracuseStep 652883 = 979325) B979325
theorem B652899 : Blo 650305 652899 := bstep (se 1 (by rfl) ⟨489674, by rfl⟩ : syracuseStep 652899 = 979349) B979349
theorem B1570403 : Blo 650305 1570403 := bstep (se 1 (by rfl) ⟨1177802, by rfl⟩ : syracuseStep 1570403 = 2355605) B2355605
theorem B980579 : Blo 650305 980579 := bstep (se 1 (by rfl) ⟨735434, by rfl⟩ : syracuseStep 980579 = 1470869) B1470869
theorem B652915 : Blo 650305 652915 := bstep (se 1 (by rfl) ⟨489686, by rfl⟩ : syracuseStep 652915 = 979373) B979373
theorem B980609 : Blo 650305 980609 := bstep (se 2 (by rfl) ⟨367728, by rfl⟩ : syracuseStep 980609 = 735457) B735457
theorem B652931 : Blo 650305 652931 := bstep (se 1 (by rfl) ⟨489698, by rfl⟩ : syracuseStep 652931 = 979397) B979397
theorem B652947 : Blo 650305 652947 := bstep (se 1 (by rfl) ⟨489710, by rfl⟩ : syracuseStep 652947 = 979421) B979421
theorem B980627 : Blo 650305 980627 := bstep (se 1 (by rfl) ⟨735470, by rfl⟩ : syracuseStep 980627 = 1470941) B1470941
theorem B652963 : Blo 650305 652963 := bstep (se 1 (by rfl) ⟨489722, by rfl⟩ : syracuseStep 652963 = 979445) B979445
theorem B980657 : Blo 650305 980657 := bstep (se 2 (by rfl) ⟨367746, by rfl⟩ : syracuseStep 980657 = 735493) B735493
theorem B652979 : Blo 650305 652979 := bstep (se 1 (by rfl) ⟨489734, by rfl⟩ : syracuseStep 652979 = 979469) B979469
theorem B652995 : Blo 650305 652995 := bstep (se 1 (by rfl) ⟨489746, by rfl⟩ : syracuseStep 652995 = 979493) B979493
theorem B980675 : Blo 650305 980675 := bstep (se 1 (by rfl) ⟨735506, by rfl⟩ : syracuseStep 980675 = 1471013) B1471013
theorem B653011 : Blo 650305 653011 := bstep (se 1 (by rfl) ⟨489758, by rfl⟩ : syracuseStep 653011 = 979517) B979517
theorem B980705 : Blo 650305 980705 := bstep (se 2 (by rfl) ⟨367764, by rfl⟩ : syracuseStep 980705 = 735529) B735529
theorem B653027 : Blo 650305 653027 := bstep (se 1 (by rfl) ⟨489770, by rfl⟩ : syracuseStep 653027 = 979541) B979541
theorem B8943331 : Blo 650305 8943331 := bstep (se 1 (by rfl) ⟨6707498, by rfl⟩ : syracuseStep 8943331 = 13414997) B13414997
theorem B653043 : Blo 650305 653043 := bstep (se 1 (by rfl) ⟨489782, by rfl⟩ : syracuseStep 653043 = 979565) B979565
theorem B980723 : Blo 650305 980723 := bstep (se 1 (by rfl) ⟨735542, by rfl⟩ : syracuseStep 980723 = 1471085) B1471085
theorem B653059 : Blo 650305 653059 := bstep (se 1 (by rfl) ⟨489794, by rfl⟩ : syracuseStep 653059 = 979589) B979589
theorem B980753 : Blo 650305 980753 := bstep (se 2 (by rfl) ⟨367782, by rfl⟩ : syracuseStep 980753 = 735565) B735565
theorem B653075 : Blo 650305 653075 := bstep (se 1 (by rfl) ⟨489806, by rfl⟩ : syracuseStep 653075 = 979613) B979613
theorem B653091 : Blo 650305 653091 := bstep (se 1 (by rfl) ⟨489818, by rfl⟩ : syracuseStep 653091 = 979637) B979637
theorem B980771 : Blo 650305 980771 := bstep (se 1 (by rfl) ⟨735578, by rfl⟩ : syracuseStep 980771 = 1471157) B1471157
theorem B653107 : Blo 650305 653107 := bstep (se 1 (by rfl) ⟨489830, by rfl⟩ : syracuseStep 653107 = 979661) B979661
theorem B980801 : Blo 650305 980801 := bstep (se 2 (by rfl) ⟨367800, by rfl⟩ : syracuseStep 980801 = 735601) B735601
theorem B653123 : Blo 650305 653123 := bstep (se 1 (by rfl) ⟨489842, by rfl⟩ : syracuseStep 653123 = 979685) B979685
theorem B4192069 : Blo 650305 4192069 := bstep (se 4 (by rfl) ⟨393006, by rfl⟩ : syracuseStep 4192069 = 786013) B786013
theorem B653139 : Blo 650305 653139 := bstep (se 1 (by rfl) ⟨489854, by rfl⟩ : syracuseStep 653139 = 979709) B979709
theorem B980819 : Blo 650305 980819 := bstep (se 1 (by rfl) ⟨735614, by rfl⟩ : syracuseStep 980819 = 1471229) B1471229
theorem B653155 : Blo 650305 653155 := bstep (se 1 (by rfl) ⟨489866, by rfl⟩ : syracuseStep 653155 = 979733) B979733
theorem B980849 : Blo 650305 980849 := bstep (se 2 (by rfl) ⟨367818, by rfl⟩ : syracuseStep 980849 = 735637) B735637
theorem B653171 : Blo 650305 653171 := bstep (se 1 (by rfl) ⟨489878, by rfl⟩ : syracuseStep 653171 = 979757) B979757
theorem B653187 : Blo 650305 653187 := bstep (se 1 (by rfl) ⟨489890, by rfl⟩ : syracuseStep 653187 = 979781) B979781
theorem B980867 : Blo 650305 980867 := bstep (se 1 (by rfl) ⟨735650, by rfl⟩ : syracuseStep 980867 = 1471301) B1471301
theorem B653203 : Blo 650305 653203 := bstep (se 1 (by rfl) ⟨489902, by rfl⟩ : syracuseStep 653203 = 979805) B979805
theorem B980897 : Blo 650305 980897 := bstep (se 2 (by rfl) ⟨367836, by rfl⟩ : syracuseStep 980897 = 735673) B735673
theorem B653219 : Blo 650305 653219 := bstep (se 1 (by rfl) ⟨489914, by rfl⟩ : syracuseStep 653219 = 979829) B979829
theorem B653235 : Blo 650305 653235 := bstep (se 1 (by rfl) ⟨489926, by rfl⟩ : syracuseStep 653235 = 979853) B979853
theorem B980915 : Blo 650305 980915 := bstep (se 1 (by rfl) ⟨735686, by rfl⟩ : syracuseStep 980915 = 1471373) B1471373
theorem B653251 : Blo 650305 653251 := bstep (se 1 (by rfl) ⟨489938, by rfl⟩ : syracuseStep 653251 = 979877) B979877
theorem B980945 : Blo 650305 980945 := bstep (se 2 (by rfl) ⟨367854, by rfl⟩ : syracuseStep 980945 = 735709) B735709
theorem B653267 : Blo 650305 653267 := bstep (se 1 (by rfl) ⟨489950, by rfl⟩ : syracuseStep 653267 = 979901) B979901
theorem B653283 : Blo 650305 653283 := bstep (se 1 (by rfl) ⟨489962, by rfl⟩ : syracuseStep 653283 = 979925) B979925
theorem B980963 : Blo 650305 980963 := bstep (se 1 (by rfl) ⟨735722, by rfl⟩ : syracuseStep 980963 = 1471445) B1471445
theorem B2652131 : Blo 650305 2652131 := bstep (se 1 (by rfl) ⟨1989098, by rfl⟩ : syracuseStep 2652131 = 3978197) B3978197
theorem B653299 : Blo 650305 653299 := bstep (se 1 (by rfl) ⟨489974, by rfl⟩ : syracuseStep 653299 = 979949) B979949
theorem B980993 : Blo 650305 980993 := bstep (se 2 (by rfl) ⟨367872, by rfl⟩ : syracuseStep 980993 = 735745) B735745
theorem B653315 : Blo 650305 653315 := bstep (se 1 (by rfl) ⟨489986, by rfl⟩ : syracuseStep 653315 = 979973) B979973
theorem B1046531 : Blo 650305 1046531 := bstep (se 1 (by rfl) ⟨784898, by rfl⟩ : syracuseStep 1046531 = 1569797) B1569797
theorem B653331 : Blo 650305 653331 := bstep (se 1 (by rfl) ⟨489998, by rfl⟩ : syracuseStep 653331 = 979997) B979997
theorem B981011 : Blo 650305 981011 := bstep (se 1 (by rfl) ⟨735758, by rfl⟩ : syracuseStep 981011 = 1471517) B1471517
theorem B2783267 : Blo 650305 2783267 := bstep (se 1 (by rfl) ⟨2087450, by rfl⟩ : syracuseStep 2783267 = 4174901) B4174901
theorem B653347 : Blo 650305 653347 := bstep (se 1 (by rfl) ⟨490010, by rfl⟩ : syracuseStep 653347 = 980021) B980021
theorem B2095139 : Blo 650305 2095139 := bstep (se 1 (by rfl) ⟨1571354, by rfl⟩ : syracuseStep 2095139 = 3142709) B3142709
theorem B981041 : Blo 650305 981041 := bstep (se 2 (by rfl) ⟨367890, by rfl⟩ : syracuseStep 981041 = 735781) B735781
theorem B653363 : Blo 650305 653363 := bstep (se 1 (by rfl) ⟨490022, by rfl⟩ : syracuseStep 653363 = 980045) B980045
theorem B653379 : Blo 650305 653379 := bstep (se 1 (by rfl) ⟨490034, by rfl⟩ : syracuseStep 653379 = 980069) B980069
theorem B981059 : Blo 650305 981059 := bstep (se 1 (by rfl) ⟨735794, by rfl⟩ : syracuseStep 981059 = 1471589) B1471589
theorem B653395 : Blo 650305 653395 := bstep (se 1 (by rfl) ⟨490046, by rfl⟩ : syracuseStep 653395 = 980093) B980093
theorem B981089 : Blo 650305 981089 := bstep (se 2 (by rfl) ⟨367908, by rfl⟩ : syracuseStep 981089 = 735817) B735817
theorem B653411 : Blo 650305 653411 := bstep (se 1 (by rfl) ⟨490058, by rfl⟩ : syracuseStep 653411 = 980117) B980117
theorem B2357347 : Blo 650305 2357347 := bstep (se 1 (by rfl) ⟨1768010, by rfl⟩ : syracuseStep 2357347 = 3536021) B3536021
theorem B653427 : Blo 650305 653427 := bstep (se 1 (by rfl) ⟨490070, by rfl⟩ : syracuseStep 653427 = 980141) B980141
theorem B981107 : Blo 650305 981107 := bstep (se 1 (by rfl) ⟨735830, by rfl⟩ : syracuseStep 981107 = 1471661) B1471661
theorem B653443 : Blo 650305 653443 := bstep (se 1 (by rfl) ⟨490082, by rfl⟩ : syracuseStep 653443 = 980165) B980165
theorem B4028549 : Blo 650305 4028549 := bstep (se 4 (by rfl) ⟨377676, by rfl⟩ : syracuseStep 4028549 = 755353) B755353
theorem B1177745 : Blo 650305 1177745 := bstep (se 2 (by rfl) ⟨441654, by rfl⟩ : syracuseStep 1177745 = 883309) B883309
theorem B981137 : Blo 650305 981137 := bstep (se 2 (by rfl) ⟨367926, by rfl⟩ : syracuseStep 981137 = 735853) B735853
theorem B653459 : Blo 650305 653459 := bstep (se 1 (by rfl) ⟨490094, by rfl⟩ : syracuseStep 653459 = 980189) B980189
theorem B653475 : Blo 650305 653475 := bstep (se 1 (by rfl) ⟨490106, by rfl⟩ : syracuseStep 653475 = 980213) B980213
theorem B2095267 : Blo 650305 2095267 := bstep (se 1 (by rfl) ⟨1571450, by rfl⟩ : syracuseStep 2095267 = 3142901) B3142901
theorem B981155 : Blo 650305 981155 := bstep (se 1 (by rfl) ⟨735866, by rfl⟩ : syracuseStep 981155 = 1471733) B1471733
theorem B653491 : Blo 650305 653491 := bstep (se 1 (by rfl) ⟨490118, by rfl⟩ : syracuseStep 653491 = 980237) B980237
theorem B981185 : Blo 650305 981185 := bstep (se 2 (by rfl) ⟨367944, by rfl⟩ : syracuseStep 981185 = 735889) B735889
theorem B653507 : Blo 650305 653507 := bstep (se 1 (by rfl) ⟨490130, by rfl⟩ : syracuseStep 653507 = 980261) B980261
theorem B653523 : Blo 650305 653523 := bstep (se 1 (by rfl) ⟨490142, by rfl⟩ : syracuseStep 653523 = 980285) B980285
theorem B981203 : Blo 650305 981203 := bstep (se 1 (by rfl) ⟨735902, by rfl⟩ : syracuseStep 981203 = 1471805) B1471805
theorem B653539 : Blo 650305 653539 := bstep (se 1 (by rfl) ⟨490154, by rfl⟩ : syracuseStep 653539 = 980309) B980309
theorem B1767665 : Blo 650305 1767665 := bstep (se 2 (by rfl) ⟨662874, by rfl⟩ : syracuseStep 1767665 = 1325749) B1325749
theorem B981233 : Blo 650305 981233 := bstep (se 2 (by rfl) ⟨367962, by rfl⟩ : syracuseStep 981233 = 735925) B735925
theorem B653555 : Blo 650305 653555 := bstep (se 1 (by rfl) ⟨490166, by rfl⟩ : syracuseStep 653555 = 980333) B980333
theorem B653571 : Blo 650305 653571 := bstep (se 1 (by rfl) ⟨490178, by rfl⟩ : syracuseStep 653571 = 980357) B980357
theorem B981251 : Blo 650305 981251 := bstep (se 1 (by rfl) ⟨735938, by rfl⟩ : syracuseStep 981251 = 1471877) B1471877
theorem B653587 : Blo 650305 653587 := bstep (se 1 (by rfl) ⟨490190, by rfl⟩ : syracuseStep 653587 = 980381) B980381
theorem B981281 : Blo 650305 981281 := bstep (se 2 (by rfl) ⟨367980, by rfl⟩ : syracuseStep 981281 = 735961) B735961
theorem B653603 : Blo 650305 653603 := bstep (se 1 (by rfl) ⟨490202, by rfl⟩ : syracuseStep 653603 = 980405) B980405
theorem B2095409 : Blo 650305 2095409 := bstep (se 2 (by rfl) ⟨785778, by rfl⟩ : syracuseStep 2095409 = 1571557) B1571557
theorem B653619 : Blo 650305 653619 := bstep (se 1 (by rfl) ⟨490214, by rfl⟩ : syracuseStep 653619 = 980429) B980429
theorem B981299 : Blo 650305 981299 := bstep (se 1 (by rfl) ⟨735974, by rfl⟩ : syracuseStep 981299 = 1471949) B1471949
theorem B653635 : Blo 650305 653635 := bstep (se 1 (by rfl) ⟨490226, by rfl⟩ : syracuseStep 653635 = 980453) B980453
theorem B981329 : Blo 650305 981329 := bstep (se 2 (by rfl) ⟨367998, by rfl⟩ : syracuseStep 981329 = 735997) B735997
theorem B653651 : Blo 650305 653651 := bstep (se 1 (by rfl) ⟨490238, by rfl⟩ : syracuseStep 653651 = 980477) B980477
theorem B653667 : Blo 650305 653667 := bstep (se 1 (by rfl) ⟨490250, by rfl⟩ : syracuseStep 653667 = 980501) B980501
theorem B981347 : Blo 650305 981347 := bstep (se 1 (by rfl) ⟨736010, by rfl⟩ : syracuseStep 981347 = 1472021) B1472021
theorem B653683 : Blo 650305 653683 := bstep (se 1 (by rfl) ⟨490262, by rfl⟩ : syracuseStep 653683 = 980525) B980525
theorem B981377 : Blo 650305 981377 := bstep (se 2 (by rfl) ⟨368016, by rfl⟩ : syracuseStep 981377 = 736033) B736033
theorem B653699 : Blo 650305 653699 := bstep (se 1 (by rfl) ⟨490274, by rfl⟩ : syracuseStep 653699 = 980549) B980549
theorem B4225421 : Blo 650305 4225421 := bstep (se 3 (by rfl) ⟨792266, by rfl⟩ : syracuseStep 4225421 = 1584533) B1584533
theorem B653715 : Blo 650305 653715 := bstep (se 1 (by rfl) ⟨490286, by rfl⟩ : syracuseStep 653715 = 980573) B980573
theorem B981395 : Blo 650305 981395 := bstep (se 1 (by rfl) ⟨736046, by rfl⟩ : syracuseStep 981395 = 1472093) B1472093
theorem B653731 : Blo 650305 653731 := bstep (se 1 (by rfl) ⟨490298, by rfl⟩ : syracuseStep 653731 = 980597) B980597
theorem B2095523 : Blo 650305 2095523 := bstep (se 1 (by rfl) ⟨1571642, by rfl⟩ : syracuseStep 2095523 = 3143285) B3143285
theorem B981425 : Blo 650305 981425 := bstep (se 2 (by rfl) ⟨368034, by rfl⟩ : syracuseStep 981425 = 736069) B736069
theorem B653747 : Blo 650305 653747 := bstep (se 1 (by rfl) ⟨490310, by rfl⟩ : syracuseStep 653747 = 980621) B980621
theorem B653763 : Blo 650305 653763 := bstep (se 1 (by rfl) ⟨490322, by rfl⟩ : syracuseStep 653763 = 980645) B980645
theorem B981443 : Blo 650305 981443 := bstep (se 1 (by rfl) ⟨736082, by rfl⟩ : syracuseStep 981443 = 1472165) B1472165
theorem B653779 : Blo 650305 653779 := bstep (se 1 (by rfl) ⟨490334, by rfl⟩ : syracuseStep 653779 = 980669) B980669
theorem B653795 : Blo 650305 653795 := bstep (se 1 (by rfl) ⟨490346, by rfl⟩ : syracuseStep 653795 = 980693) B980693
theorem B653811 : Blo 650305 653811 := bstep (se 1 (by rfl) ⟨490358, by rfl⟩ : syracuseStep 653811 = 980717) B980717
theorem B653827 : Blo 650305 653827 := bstep (se 1 (by rfl) ⟨490370, by rfl⟩ : syracuseStep 653827 = 980741) B980741
theorem B653843 : Blo 650305 653843 := bstep (se 1 (by rfl) ⟨490382, by rfl⟩ : syracuseStep 653843 = 980765) B980765
theorem B653859 : Blo 650305 653859 := bstep (se 1 (by rfl) ⟨490394, by rfl⟩ : syracuseStep 653859 = 980789) B980789
theorem B653875 : Blo 650305 653875 := bstep (se 1 (by rfl) ⟨490406, by rfl⟩ : syracuseStep 653875 = 980813) B980813
theorem B15039029 : Blo 650305 15039029 := bstep (se 5 (by rfl) ⟨704954, by rfl⟩ : syracuseStep 15039029 = 1409909) B1409909
theorem B653891 : Blo 650305 653891 := bstep (se 1 (by rfl) ⟨490418, by rfl⟩ : syracuseStep 653891 = 980837) B980837
theorem B653907 : Blo 650305 653907 := bstep (se 1 (by rfl) ⟨490430, by rfl⟩ : syracuseStep 653907 = 980861) B980861
theorem B653923 : Blo 650305 653923 := bstep (se 1 (by rfl) ⟨490442, by rfl⟩ : syracuseStep 653923 = 980885) B980885
theorem B653939 : Blo 650305 653939 := bstep (se 1 (by rfl) ⟨490454, by rfl⟩ : syracuseStep 653939 = 980909) B980909
theorem B653955 : Blo 650305 653955 := bstep (se 1 (by rfl) ⟨490466, by rfl⟩ : syracuseStep 653955 = 980933) B980933
theorem B653971 : Blo 650305 653971 := bstep (se 1 (by rfl) ⟨490478, by rfl⟩ : syracuseStep 653971 = 980957) B980957
theorem B653987 : Blo 650305 653987 := bstep (se 1 (by rfl) ⟨490490, by rfl⟩ : syracuseStep 653987 = 980981) B980981
theorem B654003 : Blo 650305 654003 := bstep (se 1 (by rfl) ⟨490502, by rfl⟩ : syracuseStep 654003 = 981005) B981005
theorem B654019 : Blo 650305 654019 := bstep (se 1 (by rfl) ⟨490514, by rfl⟩ : syracuseStep 654019 = 981029) B981029
theorem B654035 : Blo 650305 654035 := bstep (se 1 (by rfl) ⟨490526, by rfl⟩ : syracuseStep 654035 = 981053) B981053
theorem B654051 : Blo 650305 654051 := bstep (se 1 (by rfl) ⟨490538, by rfl⟩ : syracuseStep 654051 = 981077) B981077
theorem B654067 : Blo 650305 654067 := bstep (se 1 (by rfl) ⟨490550, by rfl⟩ : syracuseStep 654067 = 981101) B981101
theorem B654083 : Blo 650305 654083 := bstep (se 1 (by rfl) ⟨490562, by rfl⟩ : syracuseStep 654083 = 981125) B981125
theorem B654099 : Blo 650305 654099 := bstep (se 1 (by rfl) ⟨490574, by rfl⟩ : syracuseStep 654099 = 981149) B981149
theorem B654115 : Blo 650305 654115 := bstep (se 1 (by rfl) ⟨490586, by rfl⟩ : syracuseStep 654115 = 981173) B981173
theorem B654131 : Blo 650305 654131 := bstep (se 1 (by rfl) ⟨490598, by rfl⟩ : syracuseStep 654131 = 981197) B981197
theorem B654147 : Blo 650305 654147 := bstep (se 1 (by rfl) ⟨490610, by rfl⟩ : syracuseStep 654147 = 981221) B981221
theorem B1047377 : Blo 650305 1047377 := bstep (se 2 (by rfl) ⟨392766, by rfl⟩ : syracuseStep 1047377 = 785533) B785533
theorem B654163 : Blo 650305 654163 := bstep (se 1 (by rfl) ⟨490622, by rfl⟩ : syracuseStep 654163 = 981245) B981245
theorem B654179 : Blo 650305 654179 := bstep (se 1 (by rfl) ⟨490634, by rfl⟩ : syracuseStep 654179 = 981269) B981269
theorem B654195 : Blo 650305 654195 := bstep (se 1 (by rfl) ⟨490646, by rfl⟩ : syracuseStep 654195 = 981293) B981293
theorem B654211 : Blo 650305 654211 := bstep (se 1 (by rfl) ⟨490658, by rfl⟩ : syracuseStep 654211 = 981317) B981317
theorem B654227 : Blo 650305 654227 := bstep (se 1 (by rfl) ⟨490670, by rfl⟩ : syracuseStep 654227 = 981341) B981341
theorem B654243 : Blo 650305 654243 := bstep (se 1 (by rfl) ⟨490682, by rfl⟩ : syracuseStep 654243 = 981365) B981365
theorem B654259 : Blo 650305 654259 := bstep (se 1 (by rfl) ⟨490694, by rfl⟩ : syracuseStep 654259 = 981389) B981389
theorem B654275 : Blo 650305 654275 := bstep (se 1 (by rfl) ⟨490706, by rfl⟩ : syracuseStep 654275 = 981413) B981413
theorem B654291 : Blo 650305 654291 := bstep (se 1 (by rfl) ⟨490718, by rfl⟩ : syracuseStep 654291 = 981437) B981437
theorem B13565069 : Blo 650305 13565069 := bstep (se 3 (by rfl) ⟨2543450, by rfl⟩ : syracuseStep 13565069 = 5086901) B5086901
theorem B3308849 : Blo 650305 3308849 := bstep (se 2 (by rfl) ⟨1240818, by rfl⟩ : syracuseStep 3308849 = 2481637) B2481637
theorem B2194829 : Blo 650305 2194829 := bstep (se 3 (by rfl) ⟨411530, by rfl⟩ : syracuseStep 2194829 = 823061) B823061
theorem B2194883 : Blo 650305 2194883 := bstep (se 1 (by rfl) ⟨1646162, by rfl⟩ : syracuseStep 2194883 = 3292325) B3292325
theorem B2195153 : Blo 650305 2195153 := bstep (se 2 (by rfl) ⟨823182, by rfl⟩ : syracuseStep 2195153 = 1646365) B1646365
theorem B10714933 : Blo 650305 10714933 := bstep (se 5 (by rfl) ⟨502262, by rfl⟩ : syracuseStep 10714933 = 1004525) B1004525
theorem B5570531 : Blo 650305 5570531 := bstep (se 1 (by rfl) ⟨4177898, by rfl⟩ : syracuseStep 5570531 = 8355797) B8355797
theorem B4227137 : Blo 650305 4227137 := bstep (se 2 (by rfl) ⟨1585176, by rfl⟩ : syracuseStep 4227137 = 3170353) B3170353
theorem B2195531 : Blo 650305 2195531 := bstep (se 1 (by rfl) ⟨1646648, by rfl⟩ : syracuseStep 2195531 = 3293297) B3293297
theorem B2195801 : Blo 650305 2195801 := bstep (se 2 (by rfl) ⟨823425, by rfl⟩ : syracuseStep 2195801 = 1646851) B1646851
theorem B3310145 : Blo 650305 3310145 := bstep (se 2 (by rfl) ⟨1241304, by rfl⟩ : syracuseStep 3310145 = 2482609) B2482609
theorem B2196503 : Blo 650305 2196503 := bstep (se 1 (by rfl) ⟨1647377, by rfl⟩ : syracuseStep 2196503 = 3294755) B3294755
theorem B5637221 : Blo 650305 5637221 := bstep (se 4 (by rfl) ⟨528489, by rfl⟩ : syracuseStep 5637221 = 1056979) B1056979
theorem B1410571 : Blo 650305 1410571 := bstep (se 1 (by rfl) ⟨1057928, by rfl⟩ : syracuseStep 1410571 = 2115857) B2115857
theorem B2197043 : Blo 650305 2197043 := bstep (se 1 (by rfl) ⟨1647782, by rfl⟩ : syracuseStep 2197043 = 3295565) B3295565
theorem B3704413 : Blo 650305 3704413 := bstep (se 3 (by rfl) ⟨694577, by rfl⟩ : syracuseStep 3704413 = 1389155) B1389155
theorem B7440173 : Blo 650305 7440173 := bstep (se 3 (by rfl) ⟨1395032, by rfl⟩ : syracuseStep 7440173 = 2790065) B2790065
theorem B2197313 : Blo 650305 2197313 := bstep (se 2 (by rfl) ⟨823992, by rfl⟩ : syracuseStep 2197313 = 1647985) B1647985
theorem B13371313 : Blo 650305 13371313 := bstep (se 2 (by rfl) ⟨5014242, by rfl⟩ : syracuseStep 13371313 = 10028485) B10028485
theorem B2230195 : Blo 650305 2230195 := bstep (se 1 (by rfl) ⟨1672646, by rfl⟩ : syracuseStep 2230195 = 3345293) B3345293
theorem B2197853 : Blo 650305 2197853 := bstep (se 3 (by rfl) ⟨412097, by rfl⟩ : syracuseStep 2197853 = 824195) B824195
theorem B3312089 : Blo 650305 3312089 := bstep (se 2 (by rfl) ⟨1242033, by rfl⟩ : syracuseStep 3312089 = 2484067) B2484067
theorem B10029719 : Blo 650305 10029719 := bstep (se 1 (by rfl) ⟨7522289, by rfl⟩ : syracuseStep 10029719 = 15044579) B15044579
theorem B1673921 : Blo 650305 1673921 := bstep (se 2 (by rfl) ⟨627720, by rfl⟩ : syracuseStep 1673921 = 1255441) B1255441
theorem B2788289 : Blo 650305 2788289 := bstep (se 2 (by rfl) ⟨1045608, by rfl⟩ : syracuseStep 2788289 = 2091217) B2091217
theorem B2788631 : Blo 650305 2788631 := bstep (se 1 (by rfl) ⟨2091473, by rfl⟩ : syracuseStep 2788631 = 4182947) B4182947
theorem B2198987 : Blo 650305 2198987 := bstep (se 1 (by rfl) ⟨1649240, by rfl⟩ : syracuseStep 2198987 = 3298481) B3298481
theorem B2199257 : Blo 650305 2199257 := bstep (se 2 (by rfl) ⟨824721, by rfl⟩ : syracuseStep 2199257 = 1649443) B1649443
theorem B823051 : Blo 650305 823051 := bstep (se 1 (by rfl) ⟨617288, by rfl⟩ : syracuseStep 823051 = 1234577) B1234577
theorem B9375533 : Blo 650305 9375533 := bstep (se 3 (by rfl) ⟨1757912, by rfl⟩ : syracuseStep 9375533 = 3515825) B3515825
theorem B4951853 : Blo 650305 4951853 := bstep (se 3 (by rfl) ⟨928472, by rfl⟩ : syracuseStep 4951853 = 1856945) B1856945
theorem B4460609 : Blo 650305 4460609 := bstep (se 2 (by rfl) ⟨1672728, by rfl⟩ : syracuseStep 4460609 = 3345457) B3345457
theorem B3969125 : Blo 650305 3969125 := bstep (se 4 (by rfl) ⟨372105, by rfl⟩ : syracuseStep 3969125 = 744211) B744211
theorem B9375875 : Blo 650305 9375875 := bstep (se 1 (by rfl) ⟨7031906, by rfl⟩ : syracuseStep 9375875 = 14063813) B14063813
theorem B2199959 : Blo 650305 2199959 := bstep (se 1 (by rfl) ⟨1649969, by rfl⟩ : syracuseStep 2199959 = 3299939) B3299939
theorem B824023 : Blo 650305 824023 := bstep (se 1 (by rfl) ⟨618017, by rfl⟩ : syracuseStep 824023 = 1236035) B1236035
theorem B21205745 : Blo 650305 21205745 := bstep (se 2 (by rfl) ⟨7952154, by rfl⟩ : syracuseStep 21205745 = 15904309) B15904309
theorem B4690705 : Blo 650305 4690705 := bstep (se 2 (by rfl) ⟨1759014, by rfl⟩ : syracuseStep 4690705 = 3518029) B3518029
theorem B2200499 : Blo 650305 2200499 := bstep (se 1 (by rfl) ⟨1650374, by rfl⟩ : syracuseStep 2200499 = 3300749) B3300749
theorem B9409553 : Blo 650305 9409553 := bstep (se 2 (by rfl) ⟨3528582, by rfl⟩ : syracuseStep 9409553 = 7057165) B7057165
theorem B2200769 : Blo 650305 2200769 := bstep (se 2 (by rfl) ⟨825288, by rfl⟩ : syracuseStep 2200769 = 1650577) B1650577
theorem B2790749 : Blo 650305 2790749 := bstep (se 3 (by rfl) ⟨523265, by rfl⟩ : syracuseStep 2790749 = 1046531) B1046531
theorem B824843 : Blo 650305 824843 := bstep (se 1 (by rfl) ⟨618632, by rfl⟩ : syracuseStep 824843 = 1237265) B1237265
theorem B2791057 : Blo 650305 2791057 := bstep (se 2 (by rfl) ⟨1046646, by rfl⟩ : syracuseStep 2791057 = 2093293) B2093293
theorem B2791091 : Blo 650305 2791091 := bstep (se 1 (by rfl) ⟨2093318, by rfl⟩ : syracuseStep 2791091 = 4186637) B4186637
theorem B2201309 : Blo 650305 2201309 := bstep (se 3 (by rfl) ⟨412745, by rfl⟩ : syracuseStep 2201309 = 825491) B825491
theorem B3774539 : Blo 650305 3774539 := bstep (se 1 (by rfl) ⟨2830904, by rfl⟩ : syracuseStep 3774539 = 5661809) B5661809
theorem B825547 : Blo 650305 825547 := bstep (se 1 (by rfl) ⟨619160, by rfl⟩ : syracuseStep 825547 = 1238321) B1238321
theorem B825815 : Blo 650305 825815 := bstep (se 1 (by rfl) ⟨619361, by rfl⟩ : syracuseStep 825815 = 1238723) B1238723
theorem B989977 : Blo 650305 989977 := bstep (se 2 (by rfl) ⟨371241, by rfl⟩ : syracuseStep 989977 = 742483) B742483
theorem B2202443 : Blo 650305 2202443 := bstep (se 1 (by rfl) ⟨1651832, by rfl⟩ : syracuseStep 2202443 = 3303665) B3303665
theorem B2235329 : Blo 650305 2235329 := bstep (se 2 (by rfl) ⟨838248, by rfl⟩ : syracuseStep 2235329 = 1676497) B1676497
theorem B2202713 : Blo 650305 2202713 := bstep (se 2 (by rfl) ⟨826017, by rfl⟩ : syracuseStep 2202713 = 1652035) B1652035
theorem B826519 : Blo 650305 826519 := bstep (se 1 (by rfl) ⟨619889, by rfl⟩ : syracuseStep 826519 = 1239779) B1239779
theorem B695671 : Blo 650305 695671 := bstep (se 1 (by rfl) ⟨521753, by rfl⟩ : syracuseStep 695671 = 1043507) B1043507
theorem B8068531 : Blo 650305 8068531 := bstep (se 1 (by rfl) ⟨6051398, by rfl⟩ : syracuseStep 8068531 = 12102797) B12102797
theorem B2793005 : Blo 650305 2793005 := bstep (se 3 (by rfl) ⟨523688, by rfl⟩ : syracuseStep 2793005 = 1047377) B1047377
theorem B4955741 : Blo 650305 4955741 := bstep (se 3 (by rfl) ⟨929201, by rfl⟩ : syracuseStep 4955741 = 1858403) B1858403
theorem B696043 : Blo 650305 696043 := bstep (se 1 (by rfl) ⟨522032, by rfl⟩ : syracuseStep 696043 = 1044065) B1044065
theorem B2203415 : Blo 650305 2203415 := bstep (se 1 (by rfl) ⟨1652561, by rfl⟩ : syracuseStep 2203415 = 3305123) B3305123
theorem B11149325 : Blo 650305 11149325 := bstep (se 3 (by rfl) ⟨2090498, by rfl⟩ : syracuseStep 11149325 = 4180997) B4180997
theorem B2793689 : Blo 650305 2793689 := bstep (se 2 (by rfl) ⟨1047633, by rfl⟩ : syracuseStep 2793689 = 2095267) B2095267
theorem B2203955 : Blo 650305 2203955 := bstep (se 1 (by rfl) ⟨1652966, by rfl⟩ : syracuseStep 2203955 = 3305933) B3305933
theorem B3350963 : Blo 650305 3350963 := bstep (se 1 (by rfl) ⟨2513222, by rfl⟩ : syracuseStep 3350963 = 5026445) B5026445
theorem B13378061 : Blo 650305 13378061 := bstep (se 3 (by rfl) ⟨2508386, by rfl⟩ : syracuseStep 13378061 = 5016773) B5016773
theorem B1647155 : Blo 650305 1647155 := bstep (se 1 (by rfl) ⟨1235366, by rfl⟩ : syracuseStep 1647155 = 2470733) B2470733
theorem B2204225 : Blo 650305 2204225 := bstep (se 2 (by rfl) ⟨826584, by rfl⟩ : syracuseStep 2204225 = 1653169) B1653169
theorem B4170541 : Blo 650305 4170541 := bstep (se 3 (by rfl) ⟨781976, by rfl⟩ : syracuseStep 4170541 = 1563953) B1563953
theorem B1647449 : Blo 650305 1647449 := bstep (se 2 (by rfl) ⟨617793, by rfl⟩ : syracuseStep 1647449 = 1235587) B1235587
theorem B2204765 : Blo 650305 2204765 := bstep (se 3 (by rfl) ⟨413393, by rfl⟩ : syracuseStep 2204765 = 826787) B826787
theorem B5579927 : Blo 650305 5579927 := bstep (se 1 (by rfl) ⟨4184945, by rfl⟩ : syracuseStep 5579927 = 8369891) B8369891
theorem B1320641 : Blo 650305 1320641 := bstep (se 2 (by rfl) ⟨495240, by rfl⟩ : syracuseStep 1320641 = 990481) B990481
theorem B2205899 : Blo 650305 2205899 := bstep (se 1 (by rfl) ⟨1654424, by rfl⟩ : syracuseStep 2205899 = 3308849) B3308849
theorem B1649099 : Blo 650305 1649099 := bstep (se 1 (by rfl) ⟨1236824, by rfl⟩ : syracuseStep 1649099 = 2473649) B2473649
theorem B2206169 : Blo 650305 2206169 := bstep (se 2 (by rfl) ⟨827313, by rfl⟩ : syracuseStep 2206169 = 1654627) B1654627
theorem B731659 : Blo 650305 731659 := bstep (se 1 (by rfl) ⟨548744, by rfl⟩ : syracuseStep 731659 = 1097489) B1097489
theorem B731767 : Blo 650305 731767 := bstep (se 1 (by rfl) ⟨548825, by rfl⟩ : syracuseStep 731767 = 1097651) B1097651
theorem B3713687 : Blo 650305 3713687 := bstep (se 1 (by rfl) ⟨2785265, by rfl⟩ : syracuseStep 3713687 = 5570531) B5570531
theorem B1288921 : Blo 650305 1288921 := bstep (se 2 (by rfl) ⟨483345, by rfl⟩ : syracuseStep 1288921 = 966691) B966691
theorem B5286617 : Blo 650305 5286617 := bstep (se 2 (by rfl) ⟨1982481, by rfl⟩ : syracuseStep 5286617 = 3964963) B3964963
theorem B731947 : Blo 650305 731947 := bstep (se 1 (by rfl) ⟨548960, by rfl⟩ : syracuseStep 731947 = 1097921) B1097921
theorem B732055 : Blo 650305 732055 := bstep (se 1 (by rfl) ⟨549041, by rfl⟩ : syracuseStep 732055 = 1098083) B1098083
theorem B732235 : Blo 650305 732235 := bstep (se 1 (by rfl) ⟨549176, by rfl⟩ : syracuseStep 732235 = 1098353) B1098353
theorem B1485913 : Blo 650305 1485913 := bstep (se 2 (by rfl) ⟨557217, by rfl⟩ : syracuseStep 1485913 = 1114435) B1114435
theorem B2206871 : Blo 650305 2206871 := bstep (se 1 (by rfl) ⟨1655153, by rfl⟩ : syracuseStep 2206871 = 3310307) B3310307
theorem B732343 : Blo 650305 732343 := bstep (se 1 (by rfl) ⟨549257, by rfl⟩ : syracuseStep 732343 = 1098515) B1098515
theorem B732523 : Blo 650305 732523 := bstep (se 1 (by rfl) ⟨549392, by rfl⟩ : syracuseStep 732523 = 1098785) B1098785
theorem B1650071 : Blo 650305 1650071 := bstep (se 1 (by rfl) ⟨1237553, by rfl⟩ : syracuseStep 1650071 = 2475107) B2475107
theorem B732631 : Blo 650305 732631 := bstep (se 1 (by rfl) ⟨549473, by rfl⟩ : syracuseStep 732631 = 1098947) B1098947
theorem B732811 : Blo 650305 732811 := bstep (se 1 (by rfl) ⟨549608, by rfl⟩ : syracuseStep 732811 = 1099217) B1099217
theorem B1322635 : Blo 650305 1322635 := bstep (se 1 (by rfl) ⟨991976, by rfl⟩ : syracuseStep 1322635 = 1983953) B1983953
theorem B2207411 : Blo 650305 2207411 := bstep (se 1 (by rfl) ⟨1655558, by rfl⟩ : syracuseStep 2207411 = 3311117) B3311117
theorem B732919 : Blo 650305 732919 := bstep (se 1 (by rfl) ⟨549689, by rfl⟩ : syracuseStep 732919 = 1099379) B1099379
theorem B733099 : Blo 650305 733099 := bstep (se 1 (by rfl) ⟨549824, by rfl⟩ : syracuseStep 733099 = 1099649) B1099649
theorem B2207681 : Blo 650305 2207681 := bstep (se 2 (by rfl) ⟨827880, by rfl⟩ : syracuseStep 2207681 = 1655761) B1655761
theorem B733207 : Blo 650305 733207 := bstep (se 1 (by rfl) ⟨549905, by rfl⟩ : syracuseStep 733207 = 1099811) B1099811
theorem B1650739 : Blo 650305 1650739 := bstep (se 1 (by rfl) ⟨1238054, by rfl⟩ : syracuseStep 1650739 = 2476109) B2476109
theorem B1650881 : Blo 650305 1650881 := bstep (se 2 (by rfl) ⟨619080, by rfl⟩ : syracuseStep 1650881 = 1238161) B1238161
theorem B733387 : Blo 650305 733387 := bstep (se 1 (by rfl) ⟨550040, by rfl⟩ : syracuseStep 733387 = 1100081) B1100081
theorem B733495 : Blo 650305 733495 := bstep (se 1 (by rfl) ⟨550121, by rfl⟩ : syracuseStep 733495 = 1100243) B1100243
theorem B1192331 : Blo 650305 1192331 := bstep (se 1 (by rfl) ⟨894248, by rfl⟩ : syracuseStep 1192331 = 1788497) B1788497
theorem B930199 : Blo 650305 930199 := bstep (se 1 (by rfl) ⟨697649, by rfl⟩ : syracuseStep 930199 = 1395299) B1395299
theorem B1323479 : Blo 650305 1323479 := bstep (se 1 (by rfl) ⟨992609, by rfl⟩ : syracuseStep 1323479 = 1985219) B1985219
theorem B2208221 : Blo 650305 2208221 := bstep (se 3 (by rfl) ⟨414041, by rfl⟩ : syracuseStep 2208221 = 828083) B828083
theorem B733675 : Blo 650305 733675 := bstep (se 1 (by rfl) ⟨550256, by rfl⟩ : syracuseStep 733675 = 1100513) B1100513
theorem B1389079 : Blo 650305 1389079 := bstep (se 1 (by rfl) ⟨1041809, by rfl⟩ : syracuseStep 1389079 = 2083619) B2083619
theorem B7156259 : Blo 650305 7156259 := bstep (se 1 (by rfl) ⟨5367194, by rfl⟩ : syracuseStep 7156259 = 10734389) B10734389
theorem B2470445 : Blo 650305 2470445 := bstep (se 3 (by rfl) ⟨463208, by rfl⟩ : syracuseStep 2470445 = 926417) B926417
theorem B733783 : Blo 650305 733783 := bstep (se 1 (by rfl) ⟨550337, by rfl⟩ : syracuseStep 733783 = 1100675) B1100675
theorem B3125891 : Blo 650305 3125891 := bstep (se 1 (by rfl) ⟨2344418, by rfl⟩ : syracuseStep 3125891 = 4688837) B4688837
theorem B4698755 : Blo 650305 4698755 := bstep (se 1 (by rfl) ⟨3524066, by rfl⟩ : syracuseStep 4698755 = 7048133) B7048133
theorem B733963 : Blo 650305 733963 := bstep (se 1 (by rfl) ⟨550472, by rfl⟩ : syracuseStep 733963 = 1100945) B1100945
theorem B2503489 : Blo 650305 2503489 := bstep (se 2 (by rfl) ⟨938808, by rfl⟩ : syracuseStep 2503489 = 1877617) B1877617
theorem B734071 : Blo 650305 734071 := bstep (se 1 (by rfl) ⟨550553, by rfl⟩ : syracuseStep 734071 = 1101107) B1101107
theorem B6042545 : Blo 650305 6042545 := bstep (se 2 (by rfl) ⟨2265954, by rfl⟩ : syracuseStep 6042545 = 4531909) B4531909
theorem B734251 : Blo 650305 734251 := bstep (se 1 (by rfl) ⟨550688, by rfl⟩ : syracuseStep 734251 = 1101377) B1101377
theorem B734359 : Blo 650305 734359 := bstep (se 1 (by rfl) ⟨550769, by rfl⟩ : syracuseStep 734359 = 1101539) B1101539
theorem B2471219 : Blo 650305 2471219 := bstep (se 1 (by rfl) ⟨1853414, by rfl⟩ : syracuseStep 2471219 = 3706829) B3706829
theorem B1389899 : Blo 650305 1389899 := bstep (se 1 (by rfl) ⟨1042424, by rfl⟩ : syracuseStep 1389899 = 2084849) B2084849
theorem B1488203 : Blo 650305 1488203 := bstep (se 1 (by rfl) ⟨1116152, by rfl⟩ : syracuseStep 1488203 = 2232305) B2232305
theorem B734539 : Blo 650305 734539 := bstep (se 1 (by rfl) ⟨550904, by rfl⟩ : syracuseStep 734539 = 1101809) B1101809
theorem B1652147 : Blo 650305 1652147 := bstep (se 1 (by rfl) ⟨1239110, by rfl⟩ : syracuseStep 1652147 = 2478221) B2478221
theorem B734647 : Blo 650305 734647 := bstep (se 1 (by rfl) ⟨550985, by rfl⟩ : syracuseStep 734647 = 1101971) B1101971
theorem B734827 : Blo 650305 734827 := bstep (se 1 (by rfl) ⟨551120, by rfl⟩ : syracuseStep 734827 = 1102241) B1102241
theorem B734935 : Blo 650305 734935 := bstep (se 1 (by rfl) ⟨551201, by rfl⟩ : syracuseStep 734935 = 1102403) B1102403
theorem B735115 : Blo 650305 735115 := bstep (se 1 (by rfl) ⟨551336, by rfl⟩ : syracuseStep 735115 = 1102673) B1102673
theorem B1652683 : Blo 650305 1652683 := bstep (se 1 (by rfl) ⟨1239512, by rfl⟩ : syracuseStep 1652683 = 2479025) B2479025
theorem B735223 : Blo 650305 735223 := bstep (se 1 (by rfl) ⟨551417, by rfl⟩ : syracuseStep 735223 = 1102835) B1102835
theorem B1652825 : Blo 650305 1652825 := bstep (se 2 (by rfl) ⟨619809, by rfl⟩ : syracuseStep 1652825 = 1239619) B1239619
theorem B1128587 : Blo 650305 1128587 := bstep (se 1 (by rfl) ⟨846440, by rfl⟩ : syracuseStep 1128587 = 1692881) B1692881
theorem B1390745 : Blo 650305 1390745 := bstep (se 2 (by rfl) ⟨521529, by rfl⟩ : syracuseStep 1390745 = 1043059) B1043059
theorem B735403 : Blo 650305 735403 := bstep (se 1 (by rfl) ⟨551552, by rfl⟩ : syracuseStep 735403 = 1103105) B1103105
theorem B735511 : Blo 650305 735511 := bstep (se 1 (by rfl) ⟨551633, by rfl⟩ : syracuseStep 735511 = 1103267) B1103267
theorem B1030553 : Blo 650305 1030553 := bstep (se 2 (by rfl) ⟨386457, by rfl⟩ : syracuseStep 1030553 = 772915) B772915
theorem B735691 : Blo 650305 735691 := bstep (se 1 (by rfl) ⟨551768, by rfl⟩ : syracuseStep 735691 = 1103537) B1103537
theorem B735799 : Blo 650305 735799 := bstep (se 1 (by rfl) ⟨551849, by rfl⟩ : syracuseStep 735799 = 1103699) B1103699
theorem B735979 : Blo 650305 735979 := bstep (se 1 (by rfl) ⟨551984, by rfl⟩ : syracuseStep 735979 = 1103969) B1103969
theorem B2472707 : Blo 650305 2472707 := bstep (se 1 (by rfl) ⟨1854530, by rfl⟩ : syracuseStep 2472707 = 3709061) B3709061
theorem B1391411 : Blo 650305 1391411 := bstep (se 1 (by rfl) ⟨1043558, by rfl⟩ : syracuseStep 1391411 = 2087117) B2087117
theorem B736087 : Blo 650305 736087 := bstep (se 1 (by rfl) ⟨552065, by rfl⟩ : syracuseStep 736087 = 1104131) B1104131
theorem B1653655 : Blo 650305 1653655 := bstep (se 1 (by rfl) ⟨1240241, by rfl⟩ : syracuseStep 1653655 = 2480483) B2480483
theorem B5946317 : Blo 650305 5946317 := bstep (se 3 (by rfl) ⟨1114934, by rfl⟩ : syracuseStep 5946317 = 2229869) B2229869
theorem B2473163 : Blo 650305 2473163 := bstep (se 1 (by rfl) ⟨1854872, by rfl⟩ : syracuseStep 2473163 = 3709745) B3709745
theorem B1654091 : Blo 650305 1654091 := bstep (se 1 (by rfl) ⟨1240568, by rfl⟩ : syracuseStep 1654091 = 2481137) B2481137
theorem B3718493 : Blo 650305 3718493 := bstep (se 3 (by rfl) ⟨697217, by rfl⟩ : syracuseStep 3718493 = 1394435) B1394435
theorem B2473361 : Blo 650305 2473361 := bstep (se 2 (by rfl) ⟨927510, by rfl⟩ : syracuseStep 2473361 = 1855021) B1855021
theorem B1490521 : Blo 650305 1490521 := bstep (se 2 (by rfl) ⟨558945, by rfl⟩ : syracuseStep 1490521 = 1117891) B1117891
theorem B11878019 : Blo 650305 11878019 := bstep (se 1 (by rfl) ⟨8908514, by rfl⟩ : syracuseStep 11878019 = 17817029) B17817029
theorem B2637485 : Blo 650305 2637485 := bstep (se 3 (by rfl) ⟨494528, by rfl⟩ : syracuseStep 2637485 = 989057) B989057
theorem B1654465 : Blo 650305 1654465 := bstep (se 2 (by rfl) ⟨620424, by rfl⟩ : syracuseStep 1654465 = 1240849) B1240849
theorem B1392385 : Blo 650305 1392385 := bstep (se 2 (by rfl) ⟨522144, by rfl⟩ : syracuseStep 1392385 = 1044289) B1044289
theorem B3292973 : Blo 650305 3292973 := bstep (se 3 (by rfl) ⟨617432, by rfl⟩ : syracuseStep 3292973 = 1234865) B1234865
theorem B1392641 : Blo 650305 1392641 := bstep (se 2 (by rfl) ⟨522240, by rfl⟩ : syracuseStep 1392641 = 1044481) B1044481
theorem B1392727 : Blo 650305 1392727 := bstep (se 1 (by rfl) ⟨1044545, by rfl⟩ : syracuseStep 1392727 = 2089091) B2089091
theorem B1097867 : Blo 650305 1097867 := bstep (se 1 (by rfl) ⟨823400, by rfl⟩ : syracuseStep 1097867 = 1646801) B1646801
theorem B2474135 : Blo 650305 2474135 := bstep (se 1 (by rfl) ⟨1855601, by rfl⟩ : syracuseStep 2474135 = 3711203) B3711203
theorem B1097995 : Blo 650305 1097995 := bstep (se 1 (by rfl) ⟨823496, by rfl⟩ : syracuseStep 1097995 = 1646993) B1646993
theorem B704791 : Blo 650305 704791 := bstep (se 1 (by rfl) ⟨528593, by rfl⟩ : syracuseStep 704791 = 1057187) B1057187
theorem B1655063 : Blo 650305 1655063 := bstep (se 1 (by rfl) ⟨1241297, by rfl⟩ : syracuseStep 1655063 = 2482595) B2482595
theorem B4702529 : Blo 650305 4702529 := bstep (se 2 (by rfl) ⟨1763448, by rfl⟩ : syracuseStep 4702529 = 3526897) B3526897
theorem B2474333 : Blo 650305 2474333 := bstep (se 3 (by rfl) ⟨463937, by rfl⟩ : syracuseStep 2474333 = 927875) B927875
theorem B1098137 : Blo 650305 1098137 := bstep (se 2 (by rfl) ⟨411801, by rfl⟩ : syracuseStep 1098137 = 823603) B823603
theorem B836119 : Blo 650305 836119 := bstep (se 1 (by rfl) ⟨627089, by rfl⟩ : syracuseStep 836119 = 1254179) B1254179
theorem B1098265 : Blo 650305 1098265 := bstep (se 2 (by rfl) ⟨411849, by rfl⟩ : syracuseStep 1098265 = 823699) B823699
theorem B1851979 : Blo 650305 1851979 := bstep (se 1 (by rfl) ⟨1388984, by rfl⟩ : syracuseStep 1851979 = 2777969) B2777969
theorem B40682225 : Blo 650305 40682225 := bstep (se 2 (by rfl) ⟨15255834, by rfl⟩ : syracuseStep 40682225 = 30511669) B30511669
theorem B1852253 : Blo 650305 1852253 := bstep (se 3 (by rfl) ⟨347297, by rfl⟩ : syracuseStep 1852253 = 694595) B694595
theorem B1655873 : Blo 650305 1655873 := bstep (se 2 (by rfl) ⟨620952, by rfl⟩ : syracuseStep 1655873 = 1241905) B1241905
theorem B1098839 : Blo 650305 1098839 := bstep (se 1 (by rfl) ⟨824129, by rfl⟩ : syracuseStep 1098839 = 1648259) B1648259
theorem B2344115 : Blo 650305 2344115 := bstep (se 1 (by rfl) ⟨1758086, by rfl⟩ : syracuseStep 2344115 = 3516173) B3516173
theorem B1852595 : Blo 650305 1852595 := bstep (se 1 (by rfl) ⟨1389446, by rfl⟩ : syracuseStep 1852595 = 2778893) B2778893
theorem B1098967 : Blo 650305 1098967 := bstep (se 1 (by rfl) ⟨824225, by rfl⟩ : syracuseStep 1098967 = 1648451) B1648451
theorem B3720977 : Blo 650305 3720977 := bstep (se 2 (by rfl) ⟨1395366, by rfl⟩ : syracuseStep 3720977 = 2790733) B2790733
theorem B1099595 : Blo 650305 1099595 := bstep (se 1 (by rfl) ⟨824696, by rfl⟩ : syracuseStep 1099595 = 1649393) B1649393
theorem B1099723 : Blo 650305 1099723 := bstep (se 1 (by rfl) ⟨824792, by rfl⟩ : syracuseStep 1099723 = 1649585) B1649585
theorem B1099865 : Blo 650305 1099865 := bstep (se 2 (by rfl) ⟨412449, by rfl⟩ : syracuseStep 1099865 = 824899) B824899
theorem B9423053 : Blo 650305 9423053 := bstep (se 3 (by rfl) ⟨1766822, by rfl⟩ : syracuseStep 9423053 = 3533645) B3533645
theorem B1099993 : Blo 650305 1099993 := bstep (se 2 (by rfl) ⟨412497, by rfl⟩ : syracuseStep 1099993 = 824995) B824995
theorem B2869465 : Blo 650305 2869465 := bstep (se 2 (by rfl) ⟨1076049, by rfl⟩ : syracuseStep 2869465 = 2152099) B2152099
theorem B1984733 : Blo 650305 1984733 := bstep (se 3 (by rfl) ⟨372137, by rfl⟩ : syracuseStep 1984733 = 744275) B744275
theorem B2476291 : Blo 650305 2476291 := bstep (se 1 (by rfl) ⟨1857218, by rfl⟩ : syracuseStep 2476291 = 3714437) B3714437
theorem B5589425 : Blo 650305 5589425 := bstep (se 2 (by rfl) ⟨2096034, by rfl⟩ : syracuseStep 5589425 = 4192069) B4192069
theorem B2476595 : Blo 650305 2476595 := bstep (se 1 (by rfl) ⟨1857446, by rfl⟩ : syracuseStep 2476595 = 3714893) B3714893
theorem B1395443 : Blo 650305 1395443 := bstep (se 1 (by rfl) ⟨1046582, by rfl⟩ : syracuseStep 1395443 = 2093165) B2093165
theorem B1100567 : Blo 650305 1100567 := bstep (se 1 (by rfl) ⟨825425, by rfl⟩ : syracuseStep 1100567 = 1650851) B1650851
theorem B7129957 : Blo 650305 7129957 := bstep (se 4 (by rfl) ⟨668433, by rfl⟩ : syracuseStep 7129957 = 1336867) B1336867
theorem B1100695 : Blo 650305 1100695 := bstep (se 1 (by rfl) ⟨825521, by rfl⟩ : syracuseStep 1100695 = 1651043) B1651043
theorem B2673587 : Blo 650305 2673587 := bstep (se 1 (by rfl) ⟨2005190, by rfl⟩ : syracuseStep 2673587 = 4010381) B4010381
theorem B707563 : Blo 650305 707563 := bstep (se 1 (by rfl) ⟨530672, by rfl⟩ : syracuseStep 707563 = 1061345) B1061345
theorem B2509955 : Blo 650305 2509955 := bstep (se 1 (by rfl) ⟨1882466, by rfl⟩ : syracuseStep 2509955 = 3764933) B3764933
theorem B2477249 : Blo 650305 2477249 := bstep (se 2 (by rfl) ⟨928968, by rfl⟩ : syracuseStep 2477249 = 1857937) B1857937
theorem B1854667 : Blo 650305 1854667 := bstep (se 1 (by rfl) ⟨1391000, by rfl⟩ : syracuseStep 1854667 = 2782001) B2782001
theorem B838987 : Blo 650305 838987 := bstep (se 1 (by rfl) ⟨629240, by rfl⟩ : syracuseStep 838987 = 1258481) B1258481
theorem B1101323 : Blo 650305 1101323 := bstep (se 1 (by rfl) ⟨825992, by rfl⟩ : syracuseStep 1101323 = 1651985) B1651985
theorem B1592855 : Blo 650305 1592855 := bstep (se 1 (by rfl) ⟨1194641, by rfl⟩ : syracuseStep 1592855 = 2389283) B2389283
theorem B3296861 : Blo 650305 3296861 := bstep (se 3 (by rfl) ⟨618161, by rfl⟩ : syracuseStep 3296861 = 1236323) B1236323
theorem B1101451 : Blo 650305 1101451 := bstep (se 1 (by rfl) ⟨826088, by rfl⟩ : syracuseStep 1101451 = 1652177) B1652177
theorem B1855169 : Blo 650305 1855169 := bstep (se 2 (by rfl) ⟨695688, by rfl⟩ : syracuseStep 1855169 = 1391377) B1391377
theorem B1986241 : Blo 650305 1986241 := bstep (se 2 (by rfl) ⟨744840, by rfl⟩ : syracuseStep 1986241 = 1489681) B1489681
theorem B1101593 : Blo 650305 1101593 := bstep (se 2 (by rfl) ⟨413097, by rfl⟩ : syracuseStep 1101593 = 826195) B826195
theorem B1101721 : Blo 650305 1101721 := bstep (se 2 (by rfl) ⟨413145, by rfl⟩ : syracuseStep 1101721 = 826291) B826291
theorem B1855511 : Blo 650305 1855511 := bstep (se 1 (by rfl) ⟨1391633, by rfl⟩ : syracuseStep 1855511 = 2783267) B2783267
theorem B1396759 : Blo 650305 1396759 := bstep (se 1 (by rfl) ⟨1047569, by rfl⟩ : syracuseStep 1396759 = 2095139) B2095139
theorem B1396939 : Blo 650305 1396939 := bstep (se 1 (by rfl) ⟨1047704, by rfl⟩ : syracuseStep 1396939 = 2095409) B2095409
theorem B1397015 : Blo 650305 1397015 := bstep (se 1 (by rfl) ⟨1047761, by rfl⟩ : syracuseStep 1397015 = 2095523) B2095523
theorem B2478509 : Blo 650305 2478509 := bstep (se 3 (by rfl) ⟨464720, by rfl⟩ : syracuseStep 2478509 = 929441) B929441
theorem B2478539 : Blo 650305 2478539 := bstep (se 1 (by rfl) ⟨1858904, by rfl⟩ : syracuseStep 2478539 = 3717809) B3717809
theorem B1102295 : Blo 650305 1102295 := bstep (se 1 (by rfl) ⟨826721, by rfl⟩ : syracuseStep 1102295 = 1653443) B1653443
theorem B1102423 : Blo 650305 1102423 := bstep (se 1 (by rfl) ⟨826817, by rfl⟩ : syracuseStep 1102423 = 1653635) B1653635
theorem B2085527 : Blo 650305 2085527 := bstep (se 1 (by rfl) ⟨1564145, by rfl⟩ : syracuseStep 2085527 = 3128291) B3128291
theorem B1463219 : Blo 650305 1463219 := bstep (se 1 (by rfl) ⟨1097414, by rfl⟩ : syracuseStep 1463219 = 2194829) B2194829
theorem B1463255 : Blo 650305 1463255 := bstep (se 1 (by rfl) ⟨1097441, by rfl⟩ : syracuseStep 1463255 = 2194883) B2194883
theorem B2479193 : Blo 650305 2479193 := bstep (se 2 (by rfl) ⟨929697, by rfl⟩ : syracuseStep 2479193 = 1859395) B1859395
theorem B1463435 : Blo 650305 1463435 := bstep (se 1 (by rfl) ⟨1097576, by rfl⟩ : syracuseStep 1463435 = 2195153) B2195153
theorem B1463489 : Blo 650305 1463489 := bstep (se 2 (by rfl) ⟨548808, by rfl⟩ : syracuseStep 1463489 = 1097617) B1097617
theorem B2086091 : Blo 650305 2086091 := bstep (se 1 (by rfl) ⟨1564568, by rfl⟩ : syracuseStep 2086091 = 3129137) B3129137
theorem B1103051 : Blo 650305 1103051 := bstep (se 1 (by rfl) ⟨827288, by rfl⟩ : syracuseStep 1103051 = 1654577) B1654577
theorem B3527981 : Blo 650305 3527981 := bstep (se 3 (by rfl) ⟨661496, by rfl⟩ : syracuseStep 3527981 = 1322993) B1322993
theorem B1103179 : Blo 650305 1103179 := bstep (se 1 (by rfl) ⟨827384, by rfl⟩ : syracuseStep 1103179 = 1654769) B1654769
theorem B7853429 : Blo 650305 7853429 := bstep (se 5 (by rfl) ⟨368129, by rfl⟩ : syracuseStep 7853429 = 736259) B736259
theorem B47502733 : Blo 650305 47502733 := bstep (se 3 (by rfl) ⟨8906762, by rfl⟩ : syracuseStep 47502733 = 17813525) B17813525
theorem B2479511 : Blo 650305 2479511 := bstep (se 1 (by rfl) ⟨1859633, by rfl⟩ : syracuseStep 2479511 = 3719267) B3719267
theorem B1463705 : Blo 650305 1463705 := bstep (se 2 (by rfl) ⟨548889, by rfl⟩ : syracuseStep 1463705 = 1097779) B1097779
theorem B2119115 : Blo 650305 2119115 := bstep (se 1 (by rfl) ⟨1589336, by rfl⟩ : syracuseStep 2119115 = 3178673) B3178673
theorem B939479 : Blo 650305 939479 := bstep (se 1 (by rfl) ⟨704609, by rfl⟩ : syracuseStep 939479 = 1409219) B1409219
theorem B1103321 : Blo 650305 1103321 := bstep (se 2 (by rfl) ⟨413745, by rfl⟩ : syracuseStep 1103321 = 827491) B827491
theorem B1463795 : Blo 650305 1463795 := bstep (se 1 (by rfl) ⟨1097846, by rfl⟩ : syracuseStep 1463795 = 2195693) B2195693
theorem B1463831 : Blo 650305 1463831 := bstep (se 1 (by rfl) ⟨1097873, by rfl⟩ : syracuseStep 1463831 = 2195747) B2195747
theorem B2971187 : Blo 650305 2971187 := bstep (se 1 (by rfl) ⟨2228390, by rfl⟩ : syracuseStep 2971187 = 4456781) B4456781
theorem B2086489 : Blo 650305 2086489 := bstep (se 2 (by rfl) ⟨782433, by rfl⟩ : syracuseStep 2086489 = 1564867) B1564867
theorem B1103449 : Blo 650305 1103449 := bstep (se 2 (by rfl) ⟨413793, by rfl⟩ : syracuseStep 1103449 = 827587) B827587
theorem B3298967 : Blo 650305 3298967 := bstep (se 1 (by rfl) ⟨2474225, by rfl⟩ : syracuseStep 3298967 = 4948451) B4948451
theorem B1464011 : Blo 650305 1464011 := bstep (se 1 (by rfl) ⟨1098008, by rfl⟩ : syracuseStep 1464011 = 2196017) B2196017
theorem B1464065 : Blo 650305 1464065 := bstep (se 2 (by rfl) ⟨549024, by rfl⟩ : syracuseStep 1464065 = 1098049) B1098049
theorem B1562561 : Blo 650305 1562561 := bstep (se 2 (by rfl) ⟨585960, by rfl⟩ : syracuseStep 1562561 = 1171921) B1171921
theorem B1464281 : Blo 650305 1464281 := bstep (se 2 (by rfl) ⟨549105, by rfl⟩ : syracuseStep 1464281 = 1098211) B1098211
theorem B2119645 : Blo 650305 2119645 := bstep (se 3 (by rfl) ⟨397433, by rfl⟩ : syracuseStep 2119645 = 794867) B794867
theorem B4413457 : Blo 650305 4413457 := bstep (se 2 (by rfl) ⟨1655046, by rfl⟩ : syracuseStep 4413457 = 3310093) B3310093
theorem B1464371 : Blo 650305 1464371 := bstep (se 1 (by rfl) ⟨1098278, by rfl⟩ : syracuseStep 1464371 = 2196557) B2196557
theorem B2480179 : Blo 650305 2480179 := bstep (se 1 (by rfl) ⟨1860134, by rfl⟩ : syracuseStep 2480179 = 3720269) B3720269
theorem B1464407 : Blo 650305 1464407 := bstep (se 1 (by rfl) ⟨1098305, by rfl⟩ : syracuseStep 1464407 = 2196611) B2196611
theorem B1857629 : Blo 650305 1857629 := bstep (se 3 (by rfl) ⟨348305, by rfl⟩ : syracuseStep 1857629 = 696611) B696611
theorem B1104023 : Blo 650305 1104023 := bstep (se 1 (by rfl) ⟨828017, by rfl⟩ : syracuseStep 1104023 = 1656035) B1656035
theorem B4708529 : Blo 650305 4708529 := bstep (se 2 (by rfl) ⟨1765698, by rfl⟩ : syracuseStep 4708529 = 3531397) B3531397
theorem B12507317 : Blo 650305 12507317 := bstep (se 5 (by rfl) ⟨586280, by rfl⟩ : syracuseStep 12507317 = 1172561) B1172561
theorem B1464587 : Blo 650305 1464587 := bstep (se 1 (by rfl) ⟨1098440, by rfl⟩ : syracuseStep 1464587 = 2196881) B2196881
theorem B37673261 : Blo 650305 37673261 := bstep (se 3 (by rfl) ⟨7063736, by rfl⟩ : syracuseStep 37673261 = 14127473) B14127473
theorem B1464641 : Blo 650305 1464641 := bstep (se 2 (by rfl) ⟨549240, by rfl⟩ : syracuseStep 1464641 = 1098481) B1098481
theorem B1235351 : Blo 650305 1235351 := bstep (se 1 (by rfl) ⟨926513, by rfl⟩ : syracuseStep 1235351 = 1853027) B1853027
theorem B1857971 : Blo 650305 1857971 := bstep (se 1 (by rfl) ⟨1393478, by rfl⟩ : syracuseStep 1857971 = 2786957) B2786957
theorem B1464857 : Blo 650305 1464857 := bstep (se 2 (by rfl) ⟨549321, by rfl⟩ : syracuseStep 1464857 = 1098643) B1098643
theorem B1464947 : Blo 650305 1464947 := bstep (se 1 (by rfl) ⟨1098710, by rfl⟩ : syracuseStep 1464947 = 2197421) B2197421
theorem B1464983 : Blo 650305 1464983 := bstep (se 1 (by rfl) ⟨1098737, by rfl⟩ : syracuseStep 1464983 = 2197475) B2197475
theorem B6675149 : Blo 650305 6675149 := bstep (se 3 (by rfl) ⟨1251590, by rfl⟩ : syracuseStep 6675149 = 2503181) B2503181
theorem B2087731 : Blo 650305 2087731 := bstep (se 1 (by rfl) ⟨1565798, by rfl⟩ : syracuseStep 2087731 = 3131597) B3131597
theorem B744247 : Blo 650305 744247 := bstep (se 1 (by rfl) ⟨558185, by rfl⟩ : syracuseStep 744247 = 1116371) B1116371
theorem B1465163 : Blo 650305 1465163 := bstep (se 1 (by rfl) ⟨1098872, by rfl⟩ : syracuseStep 1465163 = 2197745) B2197745
theorem B1465217 : Blo 650305 1465217 := bstep (se 2 (by rfl) ⟨549456, by rfl⟩ : syracuseStep 1465217 = 1098913) B1098913
theorem B1235891 : Blo 650305 1235891 := bstep (se 1 (by rfl) ⟨926918, by rfl⟩ : syracuseStep 1235891 = 1853837) B1853837
theorem B941015 : Blo 650305 941015 := bstep (se 1 (by rfl) ⟨705761, by rfl⟩ : syracuseStep 941015 = 1411523) B1411523
theorem B2382851 : Blo 650305 2382851 := bstep (se 1 (by rfl) ⟨1787138, by rfl⟩ : syracuseStep 2382851 = 3574277) B3574277
theorem B3529793 : Blo 650305 3529793 := bstep (se 2 (by rfl) ⟨1323672, by rfl⟩ : syracuseStep 3529793 = 2647345) B2647345
theorem B1465433 : Blo 650305 1465433 := bstep (se 2 (by rfl) ⟨549537, by rfl⟩ : syracuseStep 1465433 = 1099075) B1099075
theorem B1465523 : Blo 650305 1465523 := bstep (se 1 (by rfl) ⟨1099142, by rfl⟩ : syracuseStep 1465523 = 2198285) B2198285
theorem B1465559 : Blo 650305 1465559 := bstep (se 1 (by rfl) ⟨1099169, by rfl⟩ : syracuseStep 1465559 = 2198339) B2198339
theorem B2481425 : Blo 650305 2481425 := bstep (se 2 (by rfl) ⟨930534, by rfl⟩ : syracuseStep 2481425 = 1861069) B1861069
theorem B1465739 : Blo 650305 1465739 := bstep (se 1 (by rfl) ⟨1099304, by rfl⟩ : syracuseStep 1465739 = 2198609) B2198609
theorem B2645399 : Blo 650305 2645399 := bstep (se 1 (by rfl) ⟨1984049, by rfl⟩ : syracuseStep 2645399 = 3968099) B3968099
theorem B1236377 : Blo 650305 1236377 := bstep (se 2 (by rfl) ⟨463641, by rfl⟩ : syracuseStep 1236377 = 927283) B927283
theorem B1465793 : Blo 650305 1465793 := bstep (se 2 (by rfl) ⟨549672, by rfl⟩ : syracuseStep 1465793 = 1099345) B1099345
theorem B1466009 : Blo 650305 1466009 := bstep (se 2 (by rfl) ⟨549753, by rfl⟩ : syracuseStep 1466009 = 1099507) B1099507
theorem B1466099 : Blo 650305 1466099 := bstep (se 1 (by rfl) ⟨1099574, by rfl⟩ : syracuseStep 1466099 = 2199149) B2199149
theorem B1466135 : Blo 650305 1466135 := bstep (se 1 (by rfl) ⟨1099601, by rfl⟩ : syracuseStep 1466135 = 2199203) B2199203
theorem B3956525 : Blo 650305 3956525 := bstep (se 3 (by rfl) ⟨741848, by rfl⟩ : syracuseStep 3956525 = 1483697) B1483697
theorem B2383789 : Blo 650305 2383789 := bstep (se 3 (by rfl) ⟨446960, by rfl⟩ : syracuseStep 2383789 = 893921) B893921
theorem B1466315 : Blo 650305 1466315 := bstep (se 1 (by rfl) ⟨1099736, by rfl⟩ : syracuseStep 1466315 = 2199473) B2199473
theorem B2482123 : Blo 650305 2482123 := bstep (se 1 (by rfl) ⟨1861592, by rfl⟩ : syracuseStep 2482123 = 3723185) B3723185
theorem B1466369 : Blo 650305 1466369 := bstep (se 2 (by rfl) ⟨549888, by rfl⟩ : syracuseStep 1466369 = 1099777) B1099777
theorem B1466585 : Blo 650305 1466585 := bstep (se 2 (by rfl) ⟨549969, by rfl⟩ : syracuseStep 1466585 = 1099939) B1099939
theorem B2482397 : Blo 650305 2482397 := bstep (se 3 (by rfl) ⟨465449, by rfl⟩ : syracuseStep 2482397 = 930899) B930899
theorem B11297009 : Blo 650305 11297009 := bstep (se 2 (by rfl) ⟨4236378, by rfl⟩ : syracuseStep 11297009 = 8472757) B8472757
theorem B1466675 : Blo 650305 1466675 := bstep (se 1 (by rfl) ⟨1100006, by rfl⟩ : syracuseStep 1466675 = 2200013) B2200013
theorem B1466711 : Blo 650305 1466711 := bstep (se 1 (by rfl) ⟨1100033, by rfl⟩ : syracuseStep 1466711 = 2200067) B2200067
theorem B1466891 : Blo 650305 1466891 := bstep (se 1 (by rfl) ⟨1100168, by rfl⟩ : syracuseStep 1466891 = 2200337) B2200337
theorem B1466945 : Blo 650305 1466945 := bstep (se 2 (by rfl) ⟨550104, by rfl⟩ : syracuseStep 1466945 = 1100209) B1100209
theorem B1270451 : Blo 650305 1270451 := bstep (se 1 (by rfl) ⟨952838, by rfl⟩ : syracuseStep 1270451 = 1905677) B1905677
theorem B975563 : Blo 650305 975563 := bstep (se 1 (by rfl) ⟨731672, by rfl⟩ : syracuseStep 975563 = 1463345) B1463345
theorem B975575 : Blo 650305 975575 := bstep (se 1 (by rfl) ⟨731681, by rfl⟩ : syracuseStep 975575 = 1463363) B1463363
theorem B1860317 : Blo 650305 1860317 := bstep (se 3 (by rfl) ⟨348809, by rfl⟩ : syracuseStep 1860317 = 697619) B697619
theorem B975641 : Blo 650305 975641 := bstep (se 2 (by rfl) ⟨365865, by rfl⟩ : syracuseStep 975641 = 731731) B731731
theorem B1467161 : Blo 650305 1467161 := bstep (se 2 (by rfl) ⟨550185, by rfl⟩ : syracuseStep 1467161 = 1100371) B1100371
theorem B5563181 : Blo 650305 5563181 := bstep (se 3 (by rfl) ⟨1043096, by rfl⟩ : syracuseStep 5563181 = 2086193) B2086193
theorem B1237835 : Blo 650305 1237835 := bstep (se 1 (by rfl) ⟨928376, by rfl⟩ : syracuseStep 1237835 = 1856753) B1856753
theorem B1467251 : Blo 650305 1467251 := bstep (se 1 (by rfl) ⟨1100438, by rfl⟩ : syracuseStep 1467251 = 2200877) B2200877
theorem B4940675 : Blo 650305 4940675 := bstep (se 1 (by rfl) ⟨3705506, by rfl⟩ : syracuseStep 4940675 = 7411013) B7411013
theorem B975755 : Blo 650305 975755 := bstep (se 1 (by rfl) ⟨731816, by rfl⟩ : syracuseStep 975755 = 1463633) B1463633
theorem B975767 : Blo 650305 975767 := bstep (se 1 (by rfl) ⟨731825, by rfl⟩ : syracuseStep 975767 = 1463651) B1463651
theorem B1467287 : Blo 650305 1467287 := bstep (se 1 (by rfl) ⟨1100465, by rfl⟩ : syracuseStep 1467287 = 2200931) B2200931
theorem B2483095 : Blo 650305 2483095 := bstep (se 1 (by rfl) ⟨1862321, by rfl⟩ : syracuseStep 2483095 = 3724643) B3724643
theorem B1860545 : Blo 650305 1860545 := bstep (se 2 (by rfl) ⟨697704, by rfl⟩ : syracuseStep 1860545 = 1395409) B1395409
theorem B975833 : Blo 650305 975833 := bstep (se 2 (by rfl) ⟨365937, by rfl⟩ : syracuseStep 975833 = 731875) B731875
theorem B1238017 : Blo 650305 1238017 := bstep (se 2 (by rfl) ⟨464256, by rfl⟩ : syracuseStep 1238017 = 928513) B928513
theorem B975947 : Blo 650305 975947 := bstep (se 1 (by rfl) ⟨731960, by rfl⟩ : syracuseStep 975947 = 1463921) B1463921
theorem B1467467 : Blo 650305 1467467 := bstep (se 1 (by rfl) ⟨1100600, by rfl⟩ : syracuseStep 1467467 = 2201201) B2201201
theorem B975959 : Blo 650305 975959 := bstep (se 1 (by rfl) ⟨731969, by rfl⟩ : syracuseStep 975959 = 1463939) B1463939
theorem B1467521 : Blo 650305 1467521 := bstep (se 2 (by rfl) ⟨550320, by rfl⟩ : syracuseStep 1467521 = 1100641) B1100641
theorem B3302531 : Blo 650305 3302531 := bstep (se 1 (by rfl) ⟨2476898, by rfl⟩ : syracuseStep 3302531 = 4953797) B4953797
theorem B976025 : Blo 650305 976025 := bstep (se 2 (by rfl) ⟨366009, by rfl⟩ : syracuseStep 976025 = 732019) B732019
theorem B1565875 : Blo 650305 1565875 := bstep (se 1 (by rfl) ⟨1174406, by rfl⟩ : syracuseStep 1565875 = 2348813) B2348813
theorem B976139 : Blo 650305 976139 := bstep (se 1 (by rfl) ⟨732104, by rfl⟩ : syracuseStep 976139 = 1464209) B1464209
theorem B976151 : Blo 650305 976151 := bstep (se 1 (by rfl) ⟨732113, by rfl⟩ : syracuseStep 976151 = 1464227) B1464227
theorem B1860887 : Blo 650305 1860887 := bstep (se 1 (by rfl) ⟨1395665, by rfl⟩ : syracuseStep 1860887 = 2791331) B2791331
theorem B976217 : Blo 650305 976217 := bstep (se 2 (by rfl) ⟨366081, by rfl⟩ : syracuseStep 976217 = 732163) B732163
theorem B1467737 : Blo 650305 1467737 := bstep (se 2 (by rfl) ⟨550401, by rfl⟩ : syracuseStep 1467737 = 1100803) B1100803
theorem B1467827 : Blo 650305 1467827 := bstep (se 1 (by rfl) ⟨1100870, by rfl⟩ : syracuseStep 1467827 = 2201741) B2201741
theorem B1566145 : Blo 650305 1566145 := bstep (se 2 (by rfl) ⟨587304, by rfl⟩ : syracuseStep 1566145 = 1174609) B1174609
theorem B1238465 : Blo 650305 1238465 := bstep (se 2 (by rfl) ⟨464424, by rfl⟩ : syracuseStep 1238465 = 928849) B928849
theorem B976331 : Blo 650305 976331 := bstep (se 1 (by rfl) ⟨732248, by rfl⟩ : syracuseStep 976331 = 1464497) B1464497
theorem B976343 : Blo 650305 976343 := bstep (se 1 (by rfl) ⟨732257, by rfl⟩ : syracuseStep 976343 = 1464515) B1464515
theorem B1467863 : Blo 650305 1467863 := bstep (se 1 (by rfl) ⟨1100897, by rfl⟩ : syracuseStep 1467863 = 2201795) B2201795
theorem B1041931 : Blo 650305 1041931 := bstep (se 1 (by rfl) ⟨781448, by rfl⟩ : syracuseStep 1041931 = 1562897) B1562897
theorem B976409 : Blo 650305 976409 := bstep (se 2 (by rfl) ⟨366153, by rfl⟩ : syracuseStep 976409 = 732307) B732307
theorem B2385539 : Blo 650305 2385539 := bstep (se 1 (by rfl) ⟨1789154, by rfl⟩ : syracuseStep 2385539 = 3578309) B3578309
theorem B976523 : Blo 650305 976523 := bstep (se 1 (by rfl) ⟨732392, by rfl⟩ : syracuseStep 976523 = 1464785) B1464785
theorem B1468043 : Blo 650305 1468043 := bstep (se 1 (by rfl) ⟨1101032, by rfl⟩ : syracuseStep 1468043 = 2202065) B2202065
theorem B976535 : Blo 650305 976535 := bstep (se 1 (by rfl) ⟨732401, by rfl⟩ : syracuseStep 976535 = 1464803) B1464803
theorem B2483885 : Blo 650305 2483885 := bstep (se 3 (by rfl) ⟨465728, by rfl⟩ : syracuseStep 2483885 = 931457) B931457
theorem B1468097 : Blo 650305 1468097 := bstep (se 2 (by rfl) ⟨550536, by rfl⟩ : syracuseStep 1468097 = 1101073) B1101073
theorem B976601 : Blo 650305 976601 := bstep (se 2 (by rfl) ⟨366225, by rfl⟩ : syracuseStep 976601 = 732451) B732451
theorem B2975491 : Blo 650305 2975491 := bstep (se 1 (by rfl) ⟨2231618, by rfl⟩ : syracuseStep 2975491 = 4463237) B4463237
theorem B1238807 : Blo 650305 1238807 := bstep (se 1 (by rfl) ⟨929105, by rfl⟩ : syracuseStep 1238807 = 1858211) B1858211
theorem B2123543 : Blo 650305 2123543 := bstep (se 1 (by rfl) ⟨1592657, by rfl⟩ : syracuseStep 2123543 = 3185315) B3185315
theorem B4187969 : Blo 650305 4187969 := bstep (se 2 (by rfl) ⟨1570488, by rfl⟩ : syracuseStep 4187969 = 3140977) B3140977
theorem B976715 : Blo 650305 976715 := bstep (se 1 (by rfl) ⟨732536, by rfl⟩ : syracuseStep 976715 = 1465073) B1465073
theorem B976727 : Blo 650305 976727 := bstep (se 1 (by rfl) ⟨732545, by rfl⟩ : syracuseStep 976727 = 1465091) B1465091
theorem B976793 : Blo 650305 976793 := bstep (se 2 (by rfl) ⟨366297, by rfl⟩ : syracuseStep 976793 = 732595) B732595
theorem B1468313 : Blo 650305 1468313 := bstep (se 2 (by rfl) ⟨550617, by rfl⟩ : syracuseStep 1468313 = 1101235) B1101235
theorem B1468403 : Blo 650305 1468403 := bstep (se 1 (by rfl) ⟨1101302, by rfl⟩ : syracuseStep 1468403 = 2202605) B2202605
theorem B976907 : Blo 650305 976907 := bstep (se 1 (by rfl) ⟨732680, by rfl⟩ : syracuseStep 976907 = 1465361) B1465361
theorem B976919 : Blo 650305 976919 := bstep (se 1 (by rfl) ⟨732689, by rfl⟩ : syracuseStep 976919 = 1465379) B1465379
theorem B1468439 : Blo 650305 1468439 := bstep (se 1 (by rfl) ⟨1101329, by rfl⟩ : syracuseStep 1468439 = 2202659) B2202659
theorem B976985 : Blo 650305 976985 := bstep (se 2 (by rfl) ⟨366369, by rfl⟩ : syracuseStep 976985 = 732739) B732739
theorem B1763417 : Blo 650305 1763417 := bstep (se 2 (by rfl) ⟨661281, by rfl⟩ : syracuseStep 1763417 = 1322563) B1322563
theorem B2779267 : Blo 650305 2779267 := bstep (se 1 (by rfl) ⟨2084450, by rfl⟩ : syracuseStep 2779267 = 4168901) B4168901
theorem B977099 : Blo 650305 977099 := bstep (se 1 (by rfl) ⟨732824, by rfl⟩ : syracuseStep 977099 = 1465649) B1465649
theorem B1468619 : Blo 650305 1468619 := bstep (se 1 (by rfl) ⟨1101464, by rfl⟩ : syracuseStep 1468619 = 2202929) B2202929
theorem B977111 : Blo 650305 977111 := bstep (se 1 (by rfl) ⟨732833, by rfl⟩ : syracuseStep 977111 = 1465667) B1465667
theorem B1042649 : Blo 650305 1042649 := bstep (se 2 (by rfl) ⟨390993, by rfl⟩ : syracuseStep 1042649 = 781987) B781987
theorem B1468673 : Blo 650305 1468673 := bstep (se 2 (by rfl) ⟨550752, by rfl⟩ : syracuseStep 1468673 = 1101505) B1101505
theorem B977177 : Blo 650305 977177 := bstep (se 2 (by rfl) ⟨366441, by rfl⟩ : syracuseStep 977177 = 732883) B732883
theorem B977291 : Blo 650305 977291 := bstep (se 1 (by rfl) ⟨732968, by rfl⟩ : syracuseStep 977291 = 1465937) B1465937
theorem B977303 : Blo 650305 977303 := bstep (se 1 (by rfl) ⟨732977, by rfl⟩ : syracuseStep 977303 = 1465955) B1465955
theorem B1042841 : Blo 650305 1042841 := bstep (se 2 (by rfl) ⟨391065, by rfl⟩ : syracuseStep 1042841 = 782131) B782131
theorem B1239475 : Blo 650305 1239475 := bstep (se 1 (by rfl) ⟨929606, by rfl⟩ : syracuseStep 1239475 = 1859213) B1859213
theorem B2779609 : Blo 650305 2779609 := bstep (se 2 (by rfl) ⟨1042353, by rfl⟩ : syracuseStep 2779609 = 2084707) B2084707
theorem B977369 : Blo 650305 977369 := bstep (se 2 (by rfl) ⟨366513, by rfl⟩ : syracuseStep 977369 = 733027) B733027
theorem B1468889 : Blo 650305 1468889 := bstep (se 2 (by rfl) ⟨550833, by rfl⟩ : syracuseStep 1468889 = 1101667) B1101667
theorem B1042969 : Blo 650305 1042969 := bstep (se 2 (by rfl) ⟨391113, by rfl⟩ : syracuseStep 1042969 = 782227) B782227
theorem B1468979 : Blo 650305 1468979 := bstep (se 1 (by rfl) ⟨1101734, by rfl⟩ : syracuseStep 1468979 = 2203469) B2203469
theorem B977483 : Blo 650305 977483 := bstep (se 1 (by rfl) ⟨733112, by rfl⟩ : syracuseStep 977483 = 1466225) B1466225
theorem B977495 : Blo 650305 977495 := bstep (se 1 (by rfl) ⟨733121, by rfl⟩ : syracuseStep 977495 = 1466243) B1466243
theorem B1272407 : Blo 650305 1272407 := bstep (se 1 (by rfl) ⟨954305, by rfl⟩ : syracuseStep 1272407 = 1908611) B1908611
theorem B1469015 : Blo 650305 1469015 := bstep (se 1 (by rfl) ⟨1101761, by rfl⟩ : syracuseStep 1469015 = 2203523) B2203523
theorem B977561 : Blo 650305 977561 := bstep (se 2 (by rfl) ⟨366585, by rfl⟩ : syracuseStep 977561 = 733171) B733171
theorem B3959513 : Blo 650305 3959513 := bstep (se 2 (by rfl) ⟨1484817, by rfl⟩ : syracuseStep 3959513 = 2969635) B2969635
theorem B977675 : Blo 650305 977675 := bstep (se 1 (by rfl) ⟨733256, by rfl⟩ : syracuseStep 977675 = 1466513) B1466513
theorem B1469195 : Blo 650305 1469195 := bstep (se 1 (by rfl) ⟨1101896, by rfl⟩ : syracuseStep 1469195 = 2203793) B2203793
theorem B977687 : Blo 650305 977687 := bstep (se 1 (by rfl) ⟨733265, by rfl⟩ : syracuseStep 977687 = 1466531) B1466531
theorem B1469249 : Blo 650305 1469249 := bstep (se 2 (by rfl) ⟨550968, by rfl⟩ : syracuseStep 1469249 = 1101937) B1101937
theorem B977753 : Blo 650305 977753 := bstep (se 2 (by rfl) ⟨366657, by rfl⟩ : syracuseStep 977753 = 733315) B733315
theorem B1239923 : Blo 650305 1239923 := bstep (se 1 (by rfl) ⟨929942, by rfl⟩ : syracuseStep 1239923 = 1859885) B1859885
theorem B1239961 : Blo 650305 1239961 := bstep (se 2 (by rfl) ⟨464985, by rfl⟩ : syracuseStep 1239961 = 929971) B929971
theorem B977867 : Blo 650305 977867 := bstep (se 1 (by rfl) ⟨733400, by rfl⟩ : syracuseStep 977867 = 1466801) B1466801
theorem B977879 : Blo 650305 977879 := bstep (se 1 (by rfl) ⟨733409, by rfl⟩ : syracuseStep 977879 = 1466819) B1466819
theorem B10742797 : Blo 650305 10742797 := bstep (se 3 (by rfl) ⟨2014274, by rfl⟩ : syracuseStep 10742797 = 4028549) B4028549
theorem B977945 : Blo 650305 977945 := bstep (se 2 (by rfl) ⟨366729, by rfl⟩ : syracuseStep 977945 = 733459) B733459
theorem B1469465 : Blo 650305 1469465 := bstep (se 2 (by rfl) ⟨551049, by rfl⟩ : syracuseStep 1469465 = 1102099) B1102099
theorem B3140653 : Blo 650305 3140653 := bstep (se 3 (by rfl) ⟨588872, by rfl⟩ : syracuseStep 3140653 = 1177745) B1177745
theorem B650315 : Blo 650305 650315 := bstep (se 1 (by rfl) ⟨487736, by rfl⟩ : syracuseStep 650315 = 975473) B975473
theorem B650327 : Blo 650305 650327 := bstep (se 1 (by rfl) ⟨487745, by rfl⟩ : syracuseStep 650327 = 975491) B975491
theorem B650347 : Blo 650305 650347 := bstep (se 1 (by rfl) ⟨487760, by rfl⟩ : syracuseStep 650347 = 975521) B975521
theorem B1469555 : Blo 650305 1469555 := bstep (se 1 (by rfl) ⟨1102166, by rfl⟩ : syracuseStep 1469555 = 2204333) B2204333
theorem B650359 : Blo 650305 650359 := bstep (se 1 (by rfl) ⟨487769, by rfl⟩ : syracuseStep 650359 = 975539) B975539
theorem B650379 : Blo 650305 650379 := bstep (se 1 (by rfl) ⟨487784, by rfl⟩ : syracuseStep 650379 = 975569) B975569
theorem B978059 : Blo 650305 978059 := bstep (se 1 (by rfl) ⟨733544, by rfl⟩ : syracuseStep 978059 = 1467089) B1467089
theorem B650391 : Blo 650305 650391 := bstep (se 1 (by rfl) ⟨487793, by rfl⟩ : syracuseStep 650391 = 975587) B975587
theorem B978071 : Blo 650305 978071 := bstep (se 1 (by rfl) ⟨733553, by rfl⟩ : syracuseStep 978071 = 1467107) B1467107
theorem B1043609 : Blo 650305 1043609 := bstep (se 2 (by rfl) ⟨391353, by rfl⟩ : syracuseStep 1043609 = 782707) B782707
theorem B1469591 : Blo 650305 1469591 := bstep (se 1 (by rfl) ⟨1102193, by rfl⟩ : syracuseStep 1469591 = 2204387) B2204387
theorem B650411 : Blo 650305 650411 := bstep (se 1 (by rfl) ⟨487808, by rfl⟩ : syracuseStep 650411 = 975617) B975617
theorem B650423 : Blo 650305 650423 := bstep (se 1 (by rfl) ⟨487817, by rfl⟩ : syracuseStep 650423 = 975635) B975635
theorem B650443 : Blo 650305 650443 := bstep (se 1 (by rfl) ⟨487832, by rfl⟩ : syracuseStep 650443 = 975665) B975665
theorem B650455 : Blo 650305 650455 := bstep (se 1 (by rfl) ⟨487841, by rfl⟩ : syracuseStep 650455 = 975683) B975683
theorem B978137 : Blo 650305 978137 := bstep (se 2 (by rfl) ⟨366801, by rfl⟩ : syracuseStep 978137 = 733603) B733603
theorem B650475 : Blo 650305 650475 := bstep (se 1 (by rfl) ⟨487856, by rfl⟩ : syracuseStep 650475 = 975713) B975713
theorem B650487 : Blo 650305 650487 := bstep (se 1 (by rfl) ⟨487865, by rfl⟩ : syracuseStep 650487 = 975731) B975731
theorem B650507 : Blo 650305 650507 := bstep (se 1 (by rfl) ⟨487880, by rfl⟩ : syracuseStep 650507 = 975761) B975761
theorem B650519 : Blo 650305 650519 := bstep (se 1 (by rfl) ⟨487889, by rfl⟩ : syracuseStep 650519 = 975779) B975779
theorem B650539 : Blo 650305 650539 := bstep (se 1 (by rfl) ⟨487904, by rfl⟩ : syracuseStep 650539 = 975809) B975809
theorem B650551 : Blo 650305 650551 := bstep (se 1 (by rfl) ⟨487913, by rfl⟩ : syracuseStep 650551 = 975827) B975827
theorem B1273153 : Blo 650305 1273153 := bstep (se 2 (by rfl) ⟨477432, by rfl⟩ : syracuseStep 1273153 = 954865) B954865
theorem B650571 : Blo 650305 650571 := bstep (se 1 (by rfl) ⟨487928, by rfl⟩ : syracuseStep 650571 = 975857) B975857
theorem B978251 : Blo 650305 978251 := bstep (se 1 (by rfl) ⟨733688, by rfl⟩ : syracuseStep 978251 = 1467377) B1467377
theorem B1469771 : Blo 650305 1469771 := bstep (se 1 (by rfl) ⟨1102328, by rfl⟩ : syracuseStep 1469771 = 2204657) B2204657
theorem B650583 : Blo 650305 650583 := bstep (se 1 (by rfl) ⟨487937, by rfl⟩ : syracuseStep 650583 = 975875) B975875
theorem B978263 : Blo 650305 978263 := bstep (se 1 (by rfl) ⟨733697, by rfl⟩ : syracuseStep 978263 = 1467395) B1467395
theorem B1240409 : Blo 650305 1240409 := bstep (se 2 (by rfl) ⟨465153, by rfl⟩ : syracuseStep 1240409 = 930307) B930307
theorem B650603 : Blo 650305 650603 := bstep (se 1 (by rfl) ⟨487952, by rfl⟩ : syracuseStep 650603 = 975905) B975905
theorem B650615 : Blo 650305 650615 := bstep (se 1 (by rfl) ⟨487961, by rfl⟩ : syracuseStep 650615 = 975923) B975923
theorem B1469825 : Blo 650305 1469825 := bstep (se 2 (by rfl) ⟨551184, by rfl⟩ : syracuseStep 1469825 = 1102369) B1102369
theorem B650635 : Blo 650305 650635 := bstep (se 1 (by rfl) ⟨487976, by rfl⟩ : syracuseStep 650635 = 975953) B975953
theorem B650647 : Blo 650305 650647 := bstep (se 1 (by rfl) ⟨487985, by rfl⟩ : syracuseStep 650647 = 975971) B975971
theorem B2780567 : Blo 650305 2780567 := bstep (se 1 (by rfl) ⟨2085425, by rfl⟩ : syracuseStep 2780567 = 4170851) B4170851
theorem B978329 : Blo 650305 978329 := bstep (se 2 (by rfl) ⟨366873, by rfl⟩ : syracuseStep 978329 = 733747) B733747
theorem B650667 : Blo 650305 650667 := bstep (se 1 (by rfl) ⟨488000, by rfl⟩ : syracuseStep 650667 = 976001) B976001
theorem B650679 : Blo 650305 650679 := bstep (se 1 (by rfl) ⟨488009, by rfl⟩ : syracuseStep 650679 = 976019) B976019
theorem B650699 : Blo 650305 650699 := bstep (se 1 (by rfl) ⟨488024, by rfl⟩ : syracuseStep 650699 = 976049) B976049
theorem B650711 : Blo 650305 650711 := bstep (se 1 (by rfl) ⟨488033, by rfl⟩ : syracuseStep 650711 = 976067) B976067
theorem B650731 : Blo 650305 650731 := bstep (se 1 (by rfl) ⟨488048, by rfl⟩ : syracuseStep 650731 = 976097) B976097
theorem B650743 : Blo 650305 650743 := bstep (se 1 (by rfl) ⟨488057, by rfl⟩ : syracuseStep 650743 = 976115) B976115
theorem B650763 : Blo 650305 650763 := bstep (se 1 (by rfl) ⟨488072, by rfl⟩ : syracuseStep 650763 = 976145) B976145
theorem B978443 : Blo 650305 978443 := bstep (se 1 (by rfl) ⟨733832, by rfl⟩ : syracuseStep 978443 = 1467665) B1467665
theorem B650775 : Blo 650305 650775 := bstep (se 1 (by rfl) ⟨488081, by rfl⟩ : syracuseStep 650775 = 976163) B976163
theorem B978455 : Blo 650305 978455 := bstep (se 1 (by rfl) ⟨733841, by rfl⟩ : syracuseStep 978455 = 1467683) B1467683
theorem B650795 : Blo 650305 650795 := bstep (se 1 (by rfl) ⟨488096, by rfl⟩ : syracuseStep 650795 = 976193) B976193
theorem B650807 : Blo 650305 650807 := bstep (se 1 (by rfl) ⟨488105, by rfl⟩ : syracuseStep 650807 = 976211) B976211
theorem B1863233 : Blo 650305 1863233 := bstep (se 2 (by rfl) ⟨698712, by rfl⟩ : syracuseStep 1863233 = 1397425) B1397425
theorem B650827 : Blo 650305 650827 := bstep (se 1 (by rfl) ⟨488120, by rfl⟩ : syracuseStep 650827 = 976241) B976241
theorem B650839 : Blo 650305 650839 := bstep (se 1 (by rfl) ⟨488129, by rfl⟩ : syracuseStep 650839 = 976259) B976259
theorem B978521 : Blo 650305 978521 := bstep (se 2 (by rfl) ⟨366945, by rfl⟩ : syracuseStep 978521 = 733891) B733891
theorem B1470041 : Blo 650305 1470041 := bstep (se 2 (by rfl) ⟨551265, by rfl⟩ : syracuseStep 1470041 = 1102531) B1102531
theorem B650859 : Blo 650305 650859 := bstep (se 1 (by rfl) ⟨488144, by rfl⟩ : syracuseStep 650859 = 976289) B976289
theorem B650871 : Blo 650305 650871 := bstep (se 1 (by rfl) ⟨488153, by rfl⟩ : syracuseStep 650871 = 976307) B976307
theorem B4025987 : Blo 650305 4025987 := bstep (se 1 (by rfl) ⟨3019490, by rfl⟩ : syracuseStep 4025987 = 6038981) B6038981
theorem B650891 : Blo 650305 650891 := bstep (se 1 (by rfl) ⟨488168, by rfl⟩ : syracuseStep 650891 = 976337) B976337
theorem B650903 : Blo 650305 650903 := bstep (se 1 (by rfl) ⟨488177, by rfl⟩ : syracuseStep 650903 = 976355) B976355
theorem B650923 : Blo 650305 650923 := bstep (se 1 (by rfl) ⟨488192, by rfl⟩ : syracuseStep 650923 = 976385) B976385
theorem B1470131 : Blo 650305 1470131 := bstep (se 1 (by rfl) ⟨1102598, by rfl⟩ : syracuseStep 1470131 = 2205197) B2205197
theorem B650935 : Blo 650305 650935 := bstep (se 1 (by rfl) ⟨488201, by rfl⟩ : syracuseStep 650935 = 976403) B976403
theorem B650955 : Blo 650305 650955 := bstep (se 1 (by rfl) ⟨488216, by rfl⟩ : syracuseStep 650955 = 976433) B976433
theorem B978635 : Blo 650305 978635 := bstep (se 1 (by rfl) ⟨733976, by rfl⟩ : syracuseStep 978635 = 1467953) B1467953
theorem B5566157 : Blo 650305 5566157 := bstep (se 3 (by rfl) ⟨1043654, by rfl⟩ : syracuseStep 5566157 = 2087309) B2087309
theorem B650967 : Blo 650305 650967 := bstep (se 1 (by rfl) ⟨488225, by rfl⟩ : syracuseStep 650967 = 976451) B976451
theorem B978647 : Blo 650305 978647 := bstep (se 1 (by rfl) ⟨733985, by rfl⟩ : syracuseStep 978647 = 1467971) B1467971
theorem B1470167 : Blo 650305 1470167 := bstep (se 1 (by rfl) ⟨1102625, by rfl⟩ : syracuseStep 1470167 = 2205251) B2205251
theorem B650987 : Blo 650305 650987 := bstep (se 1 (by rfl) ⟨488240, by rfl⟩ : syracuseStep 650987 = 976481) B976481
theorem B650999 : Blo 650305 650999 := bstep (se 1 (by rfl) ⟨488249, by rfl⟩ : syracuseStep 650999 = 976499) B976499
theorem B651019 : Blo 650305 651019 := bstep (se 1 (by rfl) ⟨488264, by rfl⟩ : syracuseStep 651019 = 976529) B976529
theorem B651031 : Blo 650305 651031 := bstep (se 1 (by rfl) ⟨488273, by rfl⟩ : syracuseStep 651031 = 976547) B976547
theorem B978713 : Blo 650305 978713 := bstep (se 2 (by rfl) ⟨367017, by rfl⟩ : syracuseStep 978713 = 734035) B734035
theorem B651051 : Blo 650305 651051 := bstep (se 1 (by rfl) ⟨488288, by rfl⟩ : syracuseStep 651051 = 976577) B976577
theorem B2748205 : Blo 650305 2748205 := bstep (se 3 (by rfl) ⟨515288, by rfl⟩ : syracuseStep 2748205 = 1030577) B1030577
theorem B651063 : Blo 650305 651063 := bstep (se 1 (by rfl) ⟨488297, by rfl⟩ : syracuseStep 651063 = 976595) B976595
theorem B651083 : Blo 650305 651083 := bstep (se 1 (by rfl) ⟨488312, by rfl⟩ : syracuseStep 651083 = 976625) B976625
theorem B651095 : Blo 650305 651095 := bstep (se 1 (by rfl) ⟨488321, by rfl⟩ : syracuseStep 651095 = 976643) B976643
theorem B651115 : Blo 650305 651115 := bstep (se 1 (by rfl) ⟨488336, by rfl⟩ : syracuseStep 651115 = 976673) B976673
theorem B651127 : Blo 650305 651127 := bstep (se 1 (by rfl) ⟨488345, by rfl⟩ : syracuseStep 651127 = 976691) B976691
theorem B651147 : Blo 650305 651147 := bstep (se 1 (by rfl) ⟨488360, by rfl⟩ : syracuseStep 651147 = 976721) B976721
theorem B978827 : Blo 650305 978827 := bstep (se 1 (by rfl) ⟨734120, by rfl⟩ : syracuseStep 978827 = 1468241) B1468241
theorem B1470347 : Blo 650305 1470347 := bstep (se 1 (by rfl) ⟨1102760, by rfl⟩ : syracuseStep 1470347 = 2205521) B2205521
theorem B2977681 : Blo 650305 2977681 := bstep (se 2 (by rfl) ⟨1116630, by rfl⟩ : syracuseStep 2977681 = 2233261) B2233261
theorem B651159 : Blo 650305 651159 := bstep (se 1 (by rfl) ⟨488369, by rfl⟩ : syracuseStep 651159 = 976739) B976739
theorem B978839 : Blo 650305 978839 := bstep (se 1 (by rfl) ⟨734129, by rfl⟩ : syracuseStep 978839 = 1468259) B1468259
theorem B651179 : Blo 650305 651179 := bstep (se 1 (by rfl) ⟨488384, by rfl⟩ : syracuseStep 651179 = 976769) B976769
theorem B651191 : Blo 650305 651191 := bstep (se 1 (by rfl) ⟨488393, by rfl⟩ : syracuseStep 651191 = 976787) B976787
theorem B1470401 : Blo 650305 1470401 := bstep (se 2 (by rfl) ⟨551400, by rfl⟩ : syracuseStep 1470401 = 1102801) B1102801
theorem B651211 : Blo 650305 651211 := bstep (se 1 (by rfl) ⟨488408, by rfl⟩ : syracuseStep 651211 = 976817) B976817
theorem B651223 : Blo 650305 651223 := bstep (se 1 (by rfl) ⟨488417, by rfl⟩ : syracuseStep 651223 = 976835) B976835
theorem B978905 : Blo 650305 978905 := bstep (se 2 (by rfl) ⟨367089, by rfl⟩ : syracuseStep 978905 = 734179) B734179
theorem B651243 : Blo 650305 651243 := bstep (se 1 (by rfl) ⟨488432, by rfl⟩ : syracuseStep 651243 = 976865) B976865
theorem B651255 : Blo 650305 651255 := bstep (se 1 (by rfl) ⟨488441, by rfl⟩ : syracuseStep 651255 = 976883) B976883
theorem B651275 : Blo 650305 651275 := bstep (se 1 (by rfl) ⟨488456, by rfl⟩ : syracuseStep 651275 = 976913) B976913
theorem B651287 : Blo 650305 651287 := bstep (se 1 (by rfl) ⟨488465, by rfl⟩ : syracuseStep 651287 = 976931) B976931
theorem B651307 : Blo 650305 651307 := bstep (se 1 (by rfl) ⟨488480, by rfl⟩ : syracuseStep 651307 = 976961) B976961
theorem B651319 : Blo 650305 651319 := bstep (se 1 (by rfl) ⟨488489, by rfl⟩ : syracuseStep 651319 = 976979) B976979
theorem B1241153 : Blo 650305 1241153 := bstep (se 2 (by rfl) ⟨465432, by rfl⟩ : syracuseStep 1241153 = 930865) B930865
theorem B651339 : Blo 650305 651339 := bstep (se 1 (by rfl) ⟨488504, by rfl⟩ : syracuseStep 651339 = 977009) B977009
theorem B979019 : Blo 650305 979019 := bstep (se 1 (by rfl) ⟨734264, by rfl⟩ : syracuseStep 979019 = 1468529) B1468529
theorem B651351 : Blo 650305 651351 := bstep (se 1 (by rfl) ⟨488513, by rfl⟩ : syracuseStep 651351 = 977027) B977027
theorem B979031 : Blo 650305 979031 := bstep (se 1 (by rfl) ⟨734273, by rfl⟩ : syracuseStep 979031 = 1468547) B1468547
theorem B651371 : Blo 650305 651371 := bstep (se 1 (by rfl) ⟨488528, by rfl⟩ : syracuseStep 651371 = 977057) B977057
theorem B651383 : Blo 650305 651383 := bstep (se 1 (by rfl) ⟨488537, by rfl⟩ : syracuseStep 651383 = 977075) B977075
theorem B2355331 : Blo 650305 2355331 := bstep (se 1 (by rfl) ⟨1766498, by rfl⟩ : syracuseStep 2355331 = 3532997) B3532997
theorem B651403 : Blo 650305 651403 := bstep (se 1 (by rfl) ⟨488552, by rfl⟩ : syracuseStep 651403 = 977105) B977105
theorem B2388113 : Blo 650305 2388113 := bstep (se 2 (by rfl) ⟨895542, by rfl⟩ : syracuseStep 2388113 = 1791085) B1791085
theorem B651415 : Blo 650305 651415 := bstep (se 1 (by rfl) ⟨488561, by rfl⟩ : syracuseStep 651415 = 977123) B977123
theorem B6025367 : Blo 650305 6025367 := bstep (se 1 (by rfl) ⟨4519025, by rfl⟩ : syracuseStep 6025367 = 9038051) B9038051
theorem B979097 : Blo 650305 979097 := bstep (se 2 (by rfl) ⟨367161, by rfl⟩ : syracuseStep 979097 = 734323) B734323
theorem B1470617 : Blo 650305 1470617 := bstep (se 2 (by rfl) ⟨551481, by rfl⟩ : syracuseStep 1470617 = 1102963) B1102963
theorem B651435 : Blo 650305 651435 := bstep (se 1 (by rfl) ⟨488576, by rfl⟩ : syracuseStep 651435 = 977153) B977153
theorem B651447 : Blo 650305 651447 := bstep (se 1 (by rfl) ⟨488585, by rfl⟩ : syracuseStep 651447 = 977171) B977171
theorem B651467 : Blo 650305 651467 := bstep (se 1 (by rfl) ⟨488600, by rfl⟩ : syracuseStep 651467 = 977201) B977201
theorem B4944077 : Blo 650305 4944077 := bstep (se 3 (by rfl) ⟨927014, by rfl⟩ : syracuseStep 4944077 = 1854029) B1854029
theorem B651479 : Blo 650305 651479 := bstep (se 1 (by rfl) ⟨488609, by rfl⟩ : syracuseStep 651479 = 977219) B977219
theorem B651499 : Blo 650305 651499 := bstep (se 1 (by rfl) ⟨488624, by rfl⟩ : syracuseStep 651499 = 977249) B977249
theorem B1470707 : Blo 650305 1470707 := bstep (se 1 (by rfl) ⟨1103030, by rfl⟩ : syracuseStep 1470707 = 2206061) B2206061
theorem B651511 : Blo 650305 651511 := bstep (se 1 (by rfl) ⟨488633, by rfl⟩ : syracuseStep 651511 = 977267) B977267
theorem B651531 : Blo 650305 651531 := bstep (se 1 (by rfl) ⟨488648, by rfl⟩ : syracuseStep 651531 = 977297) B977297
theorem B979211 : Blo 650305 979211 := bstep (se 1 (by rfl) ⟨734408, by rfl⟩ : syracuseStep 979211 = 1468817) B1468817
theorem B651543 : Blo 650305 651543 := bstep (se 1 (by rfl) ⟨488657, by rfl⟩ : syracuseStep 651543 = 977315) B977315
theorem B979223 : Blo 650305 979223 := bstep (se 1 (by rfl) ⟨734417, by rfl⟩ : syracuseStep 979223 = 1468835) B1468835
theorem B1470743 : Blo 650305 1470743 := bstep (se 1 (by rfl) ⟨1103057, by rfl⟩ : syracuseStep 1470743 = 2206115) B2206115
theorem B651563 : Blo 650305 651563 := bstep (se 1 (by rfl) ⟨488672, by rfl⟩ : syracuseStep 651563 = 977345) B977345
theorem B651575 : Blo 650305 651575 := bstep (se 1 (by rfl) ⟨488681, by rfl⟩ : syracuseStep 651575 = 977363) B977363
theorem B651595 : Blo 650305 651595 := bstep (se 1 (by rfl) ⟨488696, by rfl⟩ : syracuseStep 651595 = 977393) B977393
theorem B1241419 : Blo 650305 1241419 := bstep (se 1 (by rfl) ⟨931064, by rfl⟩ : syracuseStep 1241419 = 1862129) B1862129
theorem B651607 : Blo 650305 651607 := bstep (se 1 (by rfl) ⟨488705, by rfl⟩ : syracuseStep 651607 = 977411) B977411
theorem B979289 : Blo 650305 979289 := bstep (se 2 (by rfl) ⟨367233, by rfl⟩ : syracuseStep 979289 = 734467) B734467
theorem B651627 : Blo 650305 651627 := bstep (se 1 (by rfl) ⟨488720, by rfl⟩ : syracuseStep 651627 = 977441) B977441
theorem B651639 : Blo 650305 651639 := bstep (se 1 (by rfl) ⟨488729, by rfl⟩ : syracuseStep 651639 = 977459) B977459
theorem B651659 : Blo 650305 651659 := bstep (se 1 (by rfl) ⟨488744, by rfl⟩ : syracuseStep 651659 = 977489) B977489
theorem B651671 : Blo 650305 651671 := bstep (se 1 (by rfl) ⟨488753, by rfl⟩ : syracuseStep 651671 = 977507) B977507
theorem B651691 : Blo 650305 651691 := bstep (se 1 (by rfl) ⟨488768, by rfl⟩ : syracuseStep 651691 = 977537) B977537
theorem B651703 : Blo 650305 651703 := bstep (se 1 (by rfl) ⟨488777, by rfl⟩ : syracuseStep 651703 = 977555) B977555
theorem B651723 : Blo 650305 651723 := bstep (se 1 (by rfl) ⟨488792, by rfl⟩ : syracuseStep 651723 = 977585) B977585
theorem B979403 : Blo 650305 979403 := bstep (se 1 (by rfl) ⟨734552, by rfl⟩ : syracuseStep 979403 = 1469105) B1469105
theorem B1470923 : Blo 650305 1470923 := bstep (se 1 (by rfl) ⟨1103192, by rfl⟩ : syracuseStep 1470923 = 2206385) B2206385
theorem B651735 : Blo 650305 651735 := bstep (se 1 (by rfl) ⟨488801, by rfl⟩ : syracuseStep 651735 = 977603) B977603
theorem B979415 : Blo 650305 979415 := bstep (se 1 (by rfl) ⟨734561, by rfl⟩ : syracuseStep 979415 = 1469123) B1469123
theorem B651755 : Blo 650305 651755 := bstep (se 1 (by rfl) ⟨488816, by rfl⟩ : syracuseStep 651755 = 977633) B977633
theorem B651767 : Blo 650305 651767 := bstep (se 1 (by rfl) ⟨488825, by rfl⟩ : syracuseStep 651767 = 977651) B977651
theorem B1470977 : Blo 650305 1470977 := bstep (se 2 (by rfl) ⟨551616, by rfl⟩ : syracuseStep 1470977 = 1103233) B1103233
theorem B651787 : Blo 650305 651787 := bstep (se 1 (by rfl) ⟨488840, by rfl⟩ : syracuseStep 651787 = 977681) B977681
theorem B4190737 : Blo 650305 4190737 := bstep (se 2 (by rfl) ⟨1571526, by rfl⟩ : syracuseStep 4190737 = 3143053) B3143053
theorem B651799 : Blo 650305 651799 := bstep (se 1 (by rfl) ⟨488849, by rfl⟩ : syracuseStep 651799 = 977699) B977699
theorem B979481 : Blo 650305 979481 := bstep (se 2 (by rfl) ⟨367305, by rfl⟩ : syracuseStep 979481 = 734611) B734611
theorem B651819 : Blo 650305 651819 := bstep (se 1 (by rfl) ⟨488864, by rfl⟩ : syracuseStep 651819 = 977729) B977729
theorem B651831 : Blo 650305 651831 := bstep (se 1 (by rfl) ⟨488873, by rfl⟩ : syracuseStep 651831 = 977747) B977747
theorem B651851 : Blo 650305 651851 := bstep (se 1 (by rfl) ⟨488888, by rfl⟩ : syracuseStep 651851 = 977777) B977777
theorem B651863 : Blo 650305 651863 := bstep (se 1 (by rfl) ⟨488897, by rfl⟩ : syracuseStep 651863 = 977795) B977795
theorem B651883 : Blo 650305 651883 := bstep (se 1 (by rfl) ⟨488912, by rfl⟩ : syracuseStep 651883 = 977825) B977825
theorem B651895 : Blo 650305 651895 := bstep (se 1 (by rfl) ⟨488921, by rfl⟩ : syracuseStep 651895 = 977843) B977843
theorem B651915 : Blo 650305 651915 := bstep (se 1 (by rfl) ⟨488936, by rfl⟩ : syracuseStep 651915 = 977873) B977873
theorem B979595 : Blo 650305 979595 := bstep (se 1 (by rfl) ⟨734696, by rfl⟩ : syracuseStep 979595 = 1469393) B1469393
theorem B651927 : Blo 650305 651927 := bstep (se 1 (by rfl) ⟨488945, by rfl⟩ : syracuseStep 651927 = 977891) B977891
theorem B979607 : Blo 650305 979607 := bstep (se 1 (by rfl) ⟨734705, by rfl⟩ : syracuseStep 979607 = 1469411) B1469411
theorem B651947 : Blo 650305 651947 := bstep (se 1 (by rfl) ⟨488960, by rfl⟩ : syracuseStep 651947 = 977921) B977921
theorem B4944563 : Blo 650305 4944563 := bstep (se 1 (by rfl) ⟨3708422, by rfl⟩ : syracuseStep 4944563 = 7416845) B7416845
theorem B651959 : Blo 650305 651959 := bstep (se 1 (by rfl) ⟨488969, by rfl⟩ : syracuseStep 651959 = 977939) B977939
theorem B651979 : Blo 650305 651979 := bstep (se 1 (by rfl) ⟨488984, by rfl⟩ : syracuseStep 651979 = 977969) B977969
theorem B1340107 : Blo 650305 1340107 := bstep (se 1 (by rfl) ⟨1005080, by rfl⟩ : syracuseStep 1340107 = 2010161) B2010161
theorem B651991 : Blo 650305 651991 := bstep (se 1 (by rfl) ⟨488993, by rfl⟩ : syracuseStep 651991 = 977987) B977987
theorem B979673 : Blo 650305 979673 := bstep (se 2 (by rfl) ⟨367377, by rfl⟩ : syracuseStep 979673 = 734755) B734755
theorem B1471193 : Blo 650305 1471193 := bstep (se 2 (by rfl) ⟨551697, by rfl⟩ : syracuseStep 1471193 = 1103395) B1103395
theorem B652011 : Blo 650305 652011 := bstep (se 1 (by rfl) ⟨489008, by rfl⟩ : syracuseStep 652011 = 978017) B978017
theorem B652023 : Blo 650305 652023 := bstep (se 1 (by rfl) ⟨489017, by rfl⟩ : syracuseStep 652023 = 978035) B978035
theorem B652043 : Blo 650305 652043 := bstep (se 1 (by rfl) ⟨489032, by rfl⟩ : syracuseStep 652043 = 978065) B978065
theorem B1241867 : Blo 650305 1241867 := bstep (se 1 (by rfl) ⟨931400, by rfl⟩ : syracuseStep 1241867 = 1862801) B1862801
theorem B3306257 : Blo 650305 3306257 := bstep (se 2 (by rfl) ⟨1239846, by rfl⟩ : syracuseStep 3306257 = 2479693) B2479693
theorem B652055 : Blo 650305 652055 := bstep (se 1 (by rfl) ⟨489041, by rfl⟩ : syracuseStep 652055 = 978083) B978083
theorem B652075 : Blo 650305 652075 := bstep (se 1 (by rfl) ⟨489056, by rfl⟩ : syracuseStep 652075 = 978113) B978113
theorem B1471283 : Blo 650305 1471283 := bstep (se 1 (by rfl) ⟨1103462, by rfl⟩ : syracuseStep 1471283 = 2206925) B2206925
theorem B652087 : Blo 650305 652087 := bstep (se 1 (by rfl) ⟨489065, by rfl⟩ : syracuseStep 652087 = 978131) B978131
theorem B652107 : Blo 650305 652107 := bstep (se 1 (by rfl) ⟨489080, by rfl⟩ : syracuseStep 652107 = 978161) B978161
theorem B979787 : Blo 650305 979787 := bstep (se 1 (by rfl) ⟨734840, by rfl⟩ : syracuseStep 979787 = 1469681) B1469681
theorem B652119 : Blo 650305 652119 := bstep (se 1 (by rfl) ⟨489089, by rfl⟩ : syracuseStep 652119 = 978179) B978179
theorem B979799 : Blo 650305 979799 := bstep (se 1 (by rfl) ⟨734849, by rfl⟩ : syracuseStep 979799 = 1469699) B1469699
theorem B881497 : Blo 650305 881497 := bstep (se 2 (by rfl) ⟨330561, by rfl⟩ : syracuseStep 881497 = 661123) B661123
theorem B1471319 : Blo 650305 1471319 := bstep (se 1 (by rfl) ⟨1103489, by rfl⟩ : syracuseStep 1471319 = 2206979) B2206979
theorem B652139 : Blo 650305 652139 := bstep (se 1 (by rfl) ⟨489104, by rfl⟩ : syracuseStep 652139 = 978209) B978209
theorem B652151 : Blo 650305 652151 := bstep (se 1 (by rfl) ⟨489113, by rfl⟩ : syracuseStep 652151 = 978227) B978227
theorem B3339139 : Blo 650305 3339139 := bstep (se 1 (by rfl) ⟨2504354, by rfl⟩ : syracuseStep 3339139 = 5008709) B5008709
theorem B652171 : Blo 650305 652171 := bstep (se 1 (by rfl) ⟨489128, by rfl⟩ : syracuseStep 652171 = 978257) B978257
theorem B652183 : Blo 650305 652183 := bstep (se 1 (by rfl) ⟨489137, by rfl⟩ : syracuseStep 652183 = 978275) B978275
theorem B979865 : Blo 650305 979865 := bstep (se 2 (by rfl) ⟨367449, by rfl⟩ : syracuseStep 979865 = 734899) B734899
theorem B652203 : Blo 650305 652203 := bstep (se 1 (by rfl) ⟨489152, by rfl⟩ : syracuseStep 652203 = 978305) B978305
theorem B3306419 : Blo 650305 3306419 := bstep (se 1 (by rfl) ⟨2479814, by rfl⟩ : syracuseStep 3306419 = 4959629) B4959629
theorem B652215 : Blo 650305 652215 := bstep (se 1 (by rfl) ⟨489161, by rfl⟩ : syracuseStep 652215 = 978323) B978323
theorem B1242049 : Blo 650305 1242049 := bstep (se 2 (by rfl) ⟨465768, by rfl⟩ : syracuseStep 1242049 = 931537) B931537
theorem B652235 : Blo 650305 652235 := bstep (se 1 (by rfl) ⟨489176, by rfl⟩ : syracuseStep 652235 = 978353) B978353
theorem B652247 : Blo 650305 652247 := bstep (se 1 (by rfl) ⟨489185, by rfl⟩ : syracuseStep 652247 = 978371) B978371
theorem B11924441 : Blo 650305 11924441 := bstep (se 2 (by rfl) ⟨4471665, by rfl⟩ : syracuseStep 11924441 = 8943331) B8943331
theorem B652267 : Blo 650305 652267 := bstep (se 1 (by rfl) ⟨489200, by rfl⟩ : syracuseStep 652267 = 978401) B978401
theorem B652279 : Blo 650305 652279 := bstep (se 1 (by rfl) ⟨489209, by rfl⟩ : syracuseStep 652279 = 978419) B978419
theorem B652299 : Blo 650305 652299 := bstep (se 1 (by rfl) ⟨489224, by rfl⟩ : syracuseStep 652299 = 978449) B978449
theorem B979979 : Blo 650305 979979 := bstep (se 1 (by rfl) ⟨734984, by rfl⟩ : syracuseStep 979979 = 1469969) B1469969
theorem B1471499 : Blo 650305 1471499 := bstep (se 1 (by rfl) ⟨1103624, by rfl⟩ : syracuseStep 1471499 = 2207249) B2207249
theorem B652311 : Blo 650305 652311 := bstep (se 1 (by rfl) ⟨489233, by rfl⟩ : syracuseStep 652311 = 978467) B978467
theorem B979991 : Blo 650305 979991 := bstep (se 1 (by rfl) ⟨734993, by rfl⟩ : syracuseStep 979991 = 1469987) B1469987
theorem B652331 : Blo 650305 652331 := bstep (se 1 (by rfl) ⟨489248, by rfl⟩ : syracuseStep 652331 = 978497) B978497
theorem B2782259 : Blo 650305 2782259 := bstep (se 1 (by rfl) ⟨2086694, by rfl⟩ : syracuseStep 2782259 = 4173389) B4173389
theorem B652343 : Blo 650305 652343 := bstep (se 1 (by rfl) ⟨489257, by rfl⟩ : syracuseStep 652343 = 978515) B978515
theorem B1471553 : Blo 650305 1471553 := bstep (se 2 (by rfl) ⟨551832, by rfl⟩ : syracuseStep 1471553 = 1103665) B1103665
theorem B652363 : Blo 650305 652363 := bstep (se 1 (by rfl) ⟨489272, by rfl⟩ : syracuseStep 652363 = 978545) B978545
theorem B652375 : Blo 650305 652375 := bstep (se 1 (by rfl) ⟨489281, by rfl⟩ : syracuseStep 652375 = 978563) B978563
theorem B980057 : Blo 650305 980057 := bstep (se 2 (by rfl) ⟨367521, by rfl⟩ : syracuseStep 980057 = 735043) B735043
theorem B652395 : Blo 650305 652395 := bstep (se 1 (by rfl) ⟨489296, by rfl⟩ : syracuseStep 652395 = 978593) B978593
theorem B652407 : Blo 650305 652407 := bstep (se 1 (by rfl) ⟨489305, by rfl⟩ : syracuseStep 652407 = 978611) B978611
theorem B652427 : Blo 650305 652427 := bstep (se 1 (by rfl) ⟨489320, by rfl⟩ : syracuseStep 652427 = 978641) B978641
theorem B652439 : Blo 650305 652439 := bstep (se 1 (by rfl) ⟨489329, by rfl⟩ : syracuseStep 652439 = 978659) B978659
theorem B652459 : Blo 650305 652459 := bstep (se 1 (by rfl) ⟨489344, by rfl⟩ : syracuseStep 652459 = 978689) B978689
theorem B652471 : Blo 650305 652471 := bstep (se 1 (by rfl) ⟨489353, by rfl⟩ : syracuseStep 652471 = 978707) B978707
theorem B652491 : Blo 650305 652491 := bstep (se 1 (by rfl) ⟨489368, by rfl⟩ : syracuseStep 652491 = 978737) B978737
theorem B980171 : Blo 650305 980171 := bstep (se 1 (by rfl) ⟨735128, by rfl⟩ : syracuseStep 980171 = 1470257) B1470257
theorem B652503 : Blo 650305 652503 := bstep (se 1 (by rfl) ⟨489377, by rfl⟩ : syracuseStep 652503 = 978755) B978755
theorem B980183 : Blo 650305 980183 := bstep (se 1 (by rfl) ⟨735137, by rfl⟩ : syracuseStep 980183 = 1470275) B1470275
theorem B652523 : Blo 650305 652523 := bstep (se 1 (by rfl) ⟨489392, by rfl⟩ : syracuseStep 652523 = 978785) B978785
theorem B652535 : Blo 650305 652535 := bstep (se 1 (by rfl) ⟨489401, by rfl⟩ : syracuseStep 652535 = 978803) B978803
theorem B652555 : Blo 650305 652555 := bstep (se 1 (by rfl) ⟨489416, by rfl⟩ : syracuseStep 652555 = 978833) B978833
theorem B652567 : Blo 650305 652567 := bstep (se 1 (by rfl) ⟨489425, by rfl⟩ : syracuseStep 652567 = 978851) B978851
theorem B980249 : Blo 650305 980249 := bstep (se 2 (by rfl) ⟨367593, by rfl⟩ : syracuseStep 980249 = 735187) B735187
theorem B1471769 : Blo 650305 1471769 := bstep (se 2 (by rfl) ⟨551913, by rfl⟩ : syracuseStep 1471769 = 1103827) B1103827
theorem B652587 : Blo 650305 652587 := bstep (se 1 (by rfl) ⟨489440, by rfl⟩ : syracuseStep 652587 = 978881) B978881
theorem B652599 : Blo 650305 652599 := bstep (se 1 (by rfl) ⟨489449, by rfl⟩ : syracuseStep 652599 = 978899) B978899
theorem B652619 : Blo 650305 652619 := bstep (se 1 (by rfl) ⟨489464, by rfl⟩ : syracuseStep 652619 = 978929) B978929
theorem B652631 : Blo 650305 652631 := bstep (se 1 (by rfl) ⟨489473, by rfl⟩ : syracuseStep 652631 = 978947) B978947
theorem B652651 : Blo 650305 652651 := bstep (se 1 (by rfl) ⟨489488, by rfl⟩ : syracuseStep 652651 = 978977) B978977
theorem B1471859 : Blo 650305 1471859 := bstep (se 1 (by rfl) ⟨1103894, by rfl⟩ : syracuseStep 1471859 = 2207789) B2207789
theorem B652663 : Blo 650305 652663 := bstep (se 1 (by rfl) ⟨489497, by rfl⟩ : syracuseStep 652663 = 978995) B978995
theorem B652683 : Blo 650305 652683 := bstep (se 1 (by rfl) ⟨489512, by rfl⟩ : syracuseStep 652683 = 979025) B979025
theorem B980363 : Blo 650305 980363 := bstep (se 1 (by rfl) ⟨735272, by rfl⟩ : syracuseStep 980363 = 1470545) B1470545
theorem B652695 : Blo 650305 652695 := bstep (se 1 (by rfl) ⟨489521, by rfl⟩ : syracuseStep 652695 = 979043) B979043
theorem B980375 : Blo 650305 980375 := bstep (se 1 (by rfl) ⟨735281, by rfl⟩ : syracuseStep 980375 = 1470563) B1470563
theorem B1471895 : Blo 650305 1471895 := bstep (se 1 (by rfl) ⟨1103921, by rfl⟩ : syracuseStep 1471895 = 2207843) B2207843
theorem B652715 : Blo 650305 652715 := bstep (se 1 (by rfl) ⟨489536, by rfl⟩ : syracuseStep 652715 = 979073) B979073
theorem B652727 : Blo 650305 652727 := bstep (se 1 (by rfl) ⟨489545, by rfl⟩ : syracuseStep 652727 = 979091) B979091
theorem B652747 : Blo 650305 652747 := bstep (se 1 (by rfl) ⟨489560, by rfl⟩ : syracuseStep 652747 = 979121) B979121
theorem B652759 : Blo 650305 652759 := bstep (se 1 (by rfl) ⟨489569, by rfl⟩ : syracuseStep 652759 = 979139) B979139
theorem B980441 : Blo 650305 980441 := bstep (se 2 (by rfl) ⟨367665, by rfl⟩ : syracuseStep 980441 = 735331) B735331
theorem B3143129 : Blo 650305 3143129 := bstep (se 2 (by rfl) ⟨1178673, by rfl⟩ : syracuseStep 3143129 = 2357347) B2357347
theorem B652779 : Blo 650305 652779 := bstep (se 1 (by rfl) ⟨489584, by rfl⟩ : syracuseStep 652779 = 979169) B979169
theorem B652791 : Blo 650305 652791 := bstep (se 1 (by rfl) ⟨489593, by rfl⟩ : syracuseStep 652791 = 979187) B979187
theorem B652811 : Blo 650305 652811 := bstep (se 1 (by rfl) ⟨489608, by rfl⟩ : syracuseStep 652811 = 979217) B979217
theorem B652823 : Blo 650305 652823 := bstep (se 1 (by rfl) ⟨489617, by rfl⟩ : syracuseStep 652823 = 979235) B979235
theorem B652843 : Blo 650305 652843 := bstep (se 1 (by rfl) ⟨489632, by rfl⟩ : syracuseStep 652843 = 979265) B979265
theorem B652855 : Blo 650305 652855 := bstep (se 1 (by rfl) ⟨489641, by rfl⟩ : syracuseStep 652855 = 979283) B979283
theorem B652875 : Blo 650305 652875 := bstep (se 1 (by rfl) ⟨489656, by rfl⟩ : syracuseStep 652875 = 979313) B979313
theorem B980555 : Blo 650305 980555 := bstep (se 1 (by rfl) ⟨735416, by rfl⟩ : syracuseStep 980555 = 1470833) B1470833
theorem B1472075 : Blo 650305 1472075 := bstep (se 1 (by rfl) ⟨1104056, by rfl⟩ : syracuseStep 1472075 = 2208113) B2208113
theorem B652887 : Blo 650305 652887 := bstep (se 1 (by rfl) ⟨489665, by rfl⟩ : syracuseStep 652887 = 979331) B979331
theorem B1177175 : Blo 650305 1177175 := bstep (se 1 (by rfl) ⟨882881, by rfl⟩ : syracuseStep 1177175 = 1765763) B1765763
theorem B980567 : Blo 650305 980567 := bstep (se 1 (by rfl) ⟨735425, by rfl⟩ : syracuseStep 980567 = 1470851) B1470851
theorem B652907 : Blo 650305 652907 := bstep (se 1 (by rfl) ⟨489680, by rfl⟩ : syracuseStep 652907 = 979361) B979361
theorem B652919 : Blo 650305 652919 := bstep (se 1 (by rfl) ⟨489689, by rfl⟩ : syracuseStep 652919 = 979379) B979379
theorem B1472129 : Blo 650305 1472129 := bstep (se 2 (by rfl) ⟨552048, by rfl⟩ : syracuseStep 1472129 = 1104097) B1104097
theorem B652939 : Blo 650305 652939 := bstep (se 1 (by rfl) ⟨489704, by rfl⟩ : syracuseStep 652939 = 979409) B979409
theorem B652951 : Blo 650305 652951 := bstep (se 1 (by rfl) ⟨489713, by rfl⟩ : syracuseStep 652951 = 979427) B979427
theorem B980633 : Blo 650305 980633 := bstep (se 2 (by rfl) ⟨367737, by rfl⟩ : syracuseStep 980633 = 735475) B735475
theorem B652971 : Blo 650305 652971 := bstep (se 1 (by rfl) ⟨489728, by rfl⟩ : syracuseStep 652971 = 979457) B979457
theorem B652983 : Blo 650305 652983 := bstep (se 1 (by rfl) ⟨489737, by rfl⟩ : syracuseStep 652983 = 979475) B979475
theorem B653003 : Blo 650305 653003 := bstep (se 1 (by rfl) ⟨489752, by rfl⟩ : syracuseStep 653003 = 979505) B979505
theorem B653015 : Blo 650305 653015 := bstep (se 1 (by rfl) ⟨489761, by rfl⟩ : syracuseStep 653015 = 979523) B979523
theorem B653035 : Blo 650305 653035 := bstep (se 1 (by rfl) ⟨489776, by rfl⟩ : syracuseStep 653035 = 979553) B979553
theorem B653047 : Blo 650305 653047 := bstep (se 1 (by rfl) ⟨489785, by rfl⟩ : syracuseStep 653047 = 979571) B979571
theorem B653067 : Blo 650305 653067 := bstep (se 1 (by rfl) ⟨489800, by rfl⟩ : syracuseStep 653067 = 979601) B979601
theorem B980747 : Blo 650305 980747 := bstep (se 1 (by rfl) ⟨735560, by rfl⟩ : syracuseStep 980747 = 1471121) B1471121
theorem B653079 : Blo 650305 653079 := bstep (se 1 (by rfl) ⟨489809, by rfl⟩ : syracuseStep 653079 = 979619) B979619
theorem B980759 : Blo 650305 980759 := bstep (se 1 (by rfl) ⟨735569, by rfl⟩ : syracuseStep 980759 = 1471139) B1471139
theorem B653099 : Blo 650305 653099 := bstep (se 1 (by rfl) ⟨489824, by rfl⟩ : syracuseStep 653099 = 979649) B979649
theorem B653111 : Blo 650305 653111 := bstep (se 1 (by rfl) ⟨489833, by rfl⟩ : syracuseStep 653111 = 979667) B979667
theorem B1767233 : Blo 650305 1767233 := bstep (se 2 (by rfl) ⟨662712, by rfl⟩ : syracuseStep 1767233 = 1325425) B1325425
theorem B653131 : Blo 650305 653131 := bstep (se 1 (by rfl) ⟨489848, by rfl⟩ : syracuseStep 653131 = 979697) B979697
theorem B653143 : Blo 650305 653143 := bstep (se 1 (by rfl) ⟨489857, by rfl⟩ : syracuseStep 653143 = 979715) B979715
theorem B980825 : Blo 650305 980825 := bstep (se 2 (by rfl) ⟨367809, by rfl⟩ : syracuseStep 980825 = 735619) B735619
theorem B653163 : Blo 650305 653163 := bstep (se 1 (by rfl) ⟨489872, by rfl⟩ : syracuseStep 653163 = 979745) B979745
theorem B653175 : Blo 650305 653175 := bstep (se 1 (by rfl) ⟨489881, by rfl⟩ : syracuseStep 653175 = 979763) B979763
theorem B653195 : Blo 650305 653195 := bstep (se 1 (by rfl) ⟨489896, by rfl⟩ : syracuseStep 653195 = 979793) B979793
theorem B784279 : Blo 650305 784279 := bstep (se 1 (by rfl) ⟨588209, by rfl⟩ : syracuseStep 784279 = 1176419) B1176419
theorem B653207 : Blo 650305 653207 := bstep (se 1 (by rfl) ⟨489905, by rfl⟩ : syracuseStep 653207 = 979811) B979811
theorem B1570711 : Blo 650305 1570711 := bstep (se 1 (by rfl) ⟨1178033, by rfl⟩ : syracuseStep 1570711 = 2356067) B2356067
theorem B1275799 : Blo 650305 1275799 := bstep (se 1 (by rfl) ⟨956849, by rfl⟩ : syracuseStep 1275799 = 1913699) B1913699
theorem B653227 : Blo 650305 653227 := bstep (se 1 (by rfl) ⟨489920, by rfl⟩ : syracuseStep 653227 = 979841) B979841
theorem B653239 : Blo 650305 653239 := bstep (se 1 (by rfl) ⟨489929, by rfl⟩ : syracuseStep 653239 = 979859) B979859
theorem B653259 : Blo 650305 653259 := bstep (se 1 (by rfl) ⟨489944, by rfl⟩ : syracuseStep 653259 = 979889) B979889
theorem B980939 : Blo 650305 980939 := bstep (se 1 (by rfl) ⟨735704, by rfl⟩ : syracuseStep 980939 = 1471409) B1471409
theorem B653271 : Blo 650305 653271 := bstep (se 1 (by rfl) ⟨489953, by rfl⟩ : syracuseStep 653271 = 979907) B979907
theorem B980951 : Blo 650305 980951 := bstep (se 1 (by rfl) ⟨735713, by rfl⟩ : syracuseStep 980951 = 1471427) B1471427
theorem B2389981 : Blo 650305 2389981 := bstep (se 3 (by rfl) ⟨448121, by rfl⟩ : syracuseStep 2389981 = 896243) B896243
theorem B653291 : Blo 650305 653291 := bstep (se 1 (by rfl) ⟨489968, by rfl⟩ : syracuseStep 653291 = 979937) B979937
theorem B653303 : Blo 650305 653303 := bstep (se 1 (by rfl) ⟨489977, by rfl⟩ : syracuseStep 653303 = 979955) B979955
theorem B653323 : Blo 650305 653323 := bstep (se 1 (by rfl) ⟨489992, by rfl⟩ : syracuseStep 653323 = 979985) B979985
theorem B653335 : Blo 650305 653335 := bstep (se 1 (by rfl) ⟨490001, by rfl⟩ : syracuseStep 653335 = 980003) B980003
theorem B981017 : Blo 650305 981017 := bstep (se 2 (by rfl) ⟨367881, by rfl⟩ : syracuseStep 981017 = 735763) B735763
theorem B653355 : Blo 650305 653355 := bstep (se 1 (by rfl) ⟨490016, by rfl⟩ : syracuseStep 653355 = 980033) B980033
theorem B653367 : Blo 650305 653367 := bstep (se 1 (by rfl) ⟨490025, by rfl⟩ : syracuseStep 653367 = 980051) B980051
theorem B60225605 : Blo 650305 60225605 := bstep (se 4 (by rfl) ⟨5646150, by rfl⟩ : syracuseStep 60225605 = 11292301) B11292301
theorem B653387 : Blo 650305 653387 := bstep (se 1 (by rfl) ⟨490040, by rfl⟩ : syracuseStep 653387 = 980081) B980081
theorem B653399 : Blo 650305 653399 := bstep (se 1 (by rfl) ⟨490049, by rfl⟩ : syracuseStep 653399 = 980099) B980099
theorem B4946021 : Blo 650305 4946021 := bstep (se 4 (by rfl) ⟨463689, by rfl⟩ : syracuseStep 4946021 = 927379) B927379
theorem B653419 : Blo 650305 653419 := bstep (se 1 (by rfl) ⟨490064, by rfl⟩ : syracuseStep 653419 = 980129) B980129
theorem B653431 : Blo 650305 653431 := bstep (se 1 (by rfl) ⟨490073, by rfl⟩ : syracuseStep 653431 = 980147) B980147
theorem B653451 : Blo 650305 653451 := bstep (se 1 (by rfl) ⟨490088, by rfl⟩ : syracuseStep 653451 = 980177) B980177
theorem B981131 : Blo 650305 981131 := bstep (se 1 (by rfl) ⟨735848, by rfl⟩ : syracuseStep 981131 = 1471697) B1471697
theorem B653463 : Blo 650305 653463 := bstep (se 1 (by rfl) ⟨490097, by rfl⟩ : syracuseStep 653463 = 980195) B980195
theorem B1177751 : Blo 650305 1177751 := bstep (se 1 (by rfl) ⟨883313, by rfl⟩ : syracuseStep 1177751 = 1766627) B1766627
theorem B981143 : Blo 650305 981143 := bstep (se 1 (by rfl) ⟨735857, by rfl⟩ : syracuseStep 981143 = 1471715) B1471715
theorem B653483 : Blo 650305 653483 := bstep (se 1 (by rfl) ⟨490112, by rfl⟩ : syracuseStep 653483 = 980225) B980225
theorem B653495 : Blo 650305 653495 := bstep (se 1 (by rfl) ⟨490121, by rfl⟩ : syracuseStep 653495 = 980243) B980243
theorem B2291915 : Blo 650305 2291915 := bstep (se 1 (by rfl) ⟨1718936, by rfl⟩ : syracuseStep 2291915 = 3437873) B3437873
theorem B653515 : Blo 650305 653515 := bstep (se 1 (by rfl) ⟨490136, by rfl⟩ : syracuseStep 653515 = 980273) B980273
theorem B653527 : Blo 650305 653527 := bstep (se 1 (by rfl) ⟨490145, by rfl⟩ : syracuseStep 653527 = 980291) B980291
theorem B981209 : Blo 650305 981209 := bstep (se 2 (by rfl) ⟨367953, by rfl⟩ : syracuseStep 981209 = 735907) B735907
theorem B653547 : Blo 650305 653547 := bstep (se 1 (by rfl) ⟨490160, by rfl⟩ : syracuseStep 653547 = 980321) B980321
theorem B653559 : Blo 650305 653559 := bstep (se 1 (by rfl) ⟨490169, by rfl⟩ : syracuseStep 653559 = 980339) B980339
theorem B653579 : Blo 650305 653579 := bstep (se 1 (by rfl) ⟨490184, by rfl⟩ : syracuseStep 653579 = 980369) B980369
theorem B653591 : Blo 650305 653591 := bstep (se 1 (by rfl) ⟨490193, by rfl⟩ : syracuseStep 653591 = 980387) B980387
theorem B2652439 : Blo 650305 2652439 := bstep (se 1 (by rfl) ⟨1989329, by rfl⟩ : syracuseStep 2652439 = 3978659) B3978659
theorem B653611 : Blo 650305 653611 := bstep (se 1 (by rfl) ⟨490208, by rfl⟩ : syracuseStep 653611 = 980417) B980417
theorem B653623 : Blo 650305 653623 := bstep (se 1 (by rfl) ⟨490217, by rfl⟩ : syracuseStep 653623 = 980435) B980435
theorem B653643 : Blo 650305 653643 := bstep (se 1 (by rfl) ⟨490232, by rfl⟩ : syracuseStep 653643 = 980465) B980465
theorem B2357579 : Blo 650305 2357579 := bstep (se 1 (by rfl) ⟨1768184, by rfl⟩ : syracuseStep 2357579 = 3536369) B3536369
theorem B981323 : Blo 650305 981323 := bstep (se 1 (by rfl) ⟨735992, by rfl⟩ : syracuseStep 981323 = 1471985) B1471985
theorem B653655 : Blo 650305 653655 := bstep (se 1 (by rfl) ⟨490241, by rfl⟩ : syracuseStep 653655 = 980483) B980483
theorem B981335 : Blo 650305 981335 := bstep (se 1 (by rfl) ⟨736001, by rfl⟩ : syracuseStep 981335 = 1472003) B1472003
theorem B653675 : Blo 650305 653675 := bstep (se 1 (by rfl) ⟨490256, by rfl⟩ : syracuseStep 653675 = 980513) B980513
theorem B653687 : Blo 650305 653687 := bstep (se 1 (by rfl) ⟨490265, by rfl⟩ : syracuseStep 653687 = 980531) B980531
theorem B653707 : Blo 650305 653707 := bstep (se 1 (by rfl) ⟨490280, by rfl⟩ : syracuseStep 653707 = 980561) B980561
theorem B1046935 : Blo 650305 1046935 := bstep (se 1 (by rfl) ⟨785201, by rfl⟩ : syracuseStep 1046935 = 1570403) B1570403
theorem B653719 : Blo 650305 653719 := bstep (se 1 (by rfl) ⟨490289, by rfl⟩ : syracuseStep 653719 = 980579) B980579
theorem B981401 : Blo 650305 981401 := bstep (se 2 (by rfl) ⟨368025, by rfl⟩ : syracuseStep 981401 = 736051) B736051
theorem B653739 : Blo 650305 653739 := bstep (se 1 (by rfl) ⟨490304, by rfl⟩ : syracuseStep 653739 = 980609) B980609
theorem B653751 : Blo 650305 653751 := bstep (se 1 (by rfl) ⟨490313, by rfl⟩ : syracuseStep 653751 = 980627) B980627
theorem B653771 : Blo 650305 653771 := bstep (se 1 (by rfl) ⟨490328, by rfl⟩ : syracuseStep 653771 = 980657) B980657
theorem B653783 : Blo 650305 653783 := bstep (se 1 (by rfl) ⟨490337, by rfl⟩ : syracuseStep 653783 = 980675) B980675
theorem B653803 : Blo 650305 653803 := bstep (se 1 (by rfl) ⟨490352, by rfl⟩ : syracuseStep 653803 = 980705) B980705
theorem B653815 : Blo 650305 653815 := bstep (se 1 (by rfl) ⟨490361, by rfl⟩ : syracuseStep 653815 = 980723) B980723
theorem B653835 : Blo 650305 653835 := bstep (se 1 (by rfl) ⟨490376, by rfl⟩ : syracuseStep 653835 = 980753) B980753
theorem B653847 : Blo 650305 653847 := bstep (se 1 (by rfl) ⟨490385, by rfl⟩ : syracuseStep 653847 = 980771) B980771
theorem B653867 : Blo 650305 653867 := bstep (se 1 (by rfl) ⟨490400, by rfl⟩ : syracuseStep 653867 = 980801) B980801
theorem B653879 : Blo 650305 653879 := bstep (se 1 (by rfl) ⟨490409, by rfl⟩ : syracuseStep 653879 = 980819) B980819
theorem B4946507 : Blo 650305 4946507 := bstep (se 1 (by rfl) ⟨3709880, by rfl⟩ : syracuseStep 4946507 = 7419761) B7419761
theorem B653899 : Blo 650305 653899 := bstep (se 1 (by rfl) ⟨490424, by rfl⟩ : syracuseStep 653899 = 980849) B980849
theorem B653911 : Blo 650305 653911 := bstep (se 1 (by rfl) ⟨490433, by rfl⟩ : syracuseStep 653911 = 980867) B980867
theorem B653931 : Blo 650305 653931 := bstep (se 1 (by rfl) ⟨490448, by rfl⟩ : syracuseStep 653931 = 980897) B980897
theorem B653943 : Blo 650305 653943 := bstep (se 1 (by rfl) ⟨490457, by rfl⟩ : syracuseStep 653943 = 980915) B980915
theorem B653963 : Blo 650305 653963 := bstep (se 1 (by rfl) ⟨490472, by rfl⟩ : syracuseStep 653963 = 980945) B980945
theorem B653975 : Blo 650305 653975 := bstep (se 1 (by rfl) ⟨490481, by rfl⟩ : syracuseStep 653975 = 980963) B980963
theorem B1768087 : Blo 650305 1768087 := bstep (se 1 (by rfl) ⟨1326065, by rfl⟩ : syracuseStep 1768087 = 2652131) B2652131
theorem B653995 : Blo 650305 653995 := bstep (se 1 (by rfl) ⟨490496, by rfl⟩ : syracuseStep 653995 = 980993) B980993
theorem B654007 : Blo 650305 654007 := bstep (se 1 (by rfl) ⟨490505, by rfl⟩ : syracuseStep 654007 = 981011) B981011
theorem B654027 : Blo 650305 654027 := bstep (se 1 (by rfl) ⟨490520, by rfl⟩ : syracuseStep 654027 = 981041) B981041
theorem B654039 : Blo 650305 654039 := bstep (se 1 (by rfl) ⟨490529, by rfl⟩ : syracuseStep 654039 = 981059) B981059
theorem B654059 : Blo 650305 654059 := bstep (se 1 (by rfl) ⟨490544, by rfl⟩ : syracuseStep 654059 = 981089) B981089
theorem B654071 : Blo 650305 654071 := bstep (se 1 (by rfl) ⟨490553, by rfl⟩ : syracuseStep 654071 = 981107) B981107
theorem B654091 : Blo 650305 654091 := bstep (se 1 (by rfl) ⟨490568, by rfl⟩ : syracuseStep 654091 = 981137) B981137
theorem B3767057 : Blo 650305 3767057 := bstep (se 2 (by rfl) ⟨1412646, by rfl⟩ : syracuseStep 3767057 = 2825293) B2825293
theorem B654103 : Blo 650305 654103 := bstep (se 1 (by rfl) ⟨490577, by rfl⟩ : syracuseStep 654103 = 981155) B981155
theorem B654123 : Blo 650305 654123 := bstep (se 1 (by rfl) ⟨490592, by rfl⟩ : syracuseStep 654123 = 981185) B981185
theorem B654135 : Blo 650305 654135 := bstep (se 1 (by rfl) ⟨490601, by rfl⟩ : syracuseStep 654135 = 981203) B981203
theorem B3308363 : Blo 650305 3308363 := bstep (se 1 (by rfl) ⟨2481272, by rfl⟩ : syracuseStep 3308363 = 4962545) B4962545
theorem B1178443 : Blo 650305 1178443 := bstep (se 1 (by rfl) ⟨883832, by rfl⟩ : syracuseStep 1178443 = 1767665) B1767665
theorem B654155 : Blo 650305 654155 := bstep (se 1 (by rfl) ⟨490616, by rfl⟩ : syracuseStep 654155 = 981233) B981233
theorem B654167 : Blo 650305 654167 := bstep (se 1 (by rfl) ⟨490625, by rfl⟩ : syracuseStep 654167 = 981251) B981251
theorem B654187 : Blo 650305 654187 := bstep (se 1 (by rfl) ⟨490640, by rfl⟩ : syracuseStep 654187 = 981281) B981281
theorem B654199 : Blo 650305 654199 := bstep (se 1 (by rfl) ⟨490649, by rfl⟩ : syracuseStep 654199 = 981299) B981299
theorem B654219 : Blo 650305 654219 := bstep (se 1 (by rfl) ⟨490664, by rfl⟩ : syracuseStep 654219 = 981329) B981329
theorem B654231 : Blo 650305 654231 := bstep (se 1 (by rfl) ⟨490673, by rfl⟩ : syracuseStep 654231 = 981347) B981347
theorem B654251 : Blo 650305 654251 := bstep (se 1 (by rfl) ⟨490688, by rfl⟩ : syracuseStep 654251 = 981377) B981377
theorem B2816947 : Blo 650305 2816947 := bstep (se 1 (by rfl) ⟨2112710, by rfl⟩ : syracuseStep 2816947 = 4225421) B4225421
theorem B654263 : Blo 650305 654263 := bstep (se 1 (by rfl) ⟨490697, by rfl⟩ : syracuseStep 654263 = 981395) B981395
theorem B654283 : Blo 650305 654283 := bstep (se 1 (by rfl) ⟨490712, by rfl⟩ : syracuseStep 654283 = 981425) B981425
theorem B654295 : Blo 650305 654295 := bstep (se 1 (by rfl) ⟨490721, by rfl⟩ : syracuseStep 654295 = 981443) B981443
theorem B10026019 : Blo 650305 10026019 := bstep (se 1 (by rfl) ⟨7519514, by rfl⟩ : syracuseStep 10026019 = 15039029) B15039029
theorem B883801 : Blo 650305 883801 := bstep (se 2 (by rfl) ⟨331425, by rfl⟩ : syracuseStep 883801 = 662851) B662851
theorem B9043379 : Blo 650305 9043379 := bstep (se 1 (by rfl) ⟨6782534, by rfl⟩ : syracuseStep 9043379 = 13565069) B13565069
theorem B2784941 : Blo 650305 2784941 := bstep (se 3 (by rfl) ⟨522176, by rfl⟩ : syracuseStep 2784941 = 1044353) B1044353
theorem B14286577 : Blo 650305 14286577 := bstep (se 2 (by rfl) ⟨5357466, by rfl⟩ : syracuseStep 14286577 = 10714933) B10714933
theorem B2818091 : Blo 650305 2818091 := bstep (se 1 (by rfl) ⟨2113568, by rfl⟩ : syracuseStep 2818091 = 4227137) B4227137
theorem B11894957 : Blo 650305 11894957 := bstep (se 3 (by rfl) ⟨2230304, by rfl⟩ : syracuseStep 11894957 = 4460609) B4460609
theorem B1114825 : Blo 650305 1114825 := bstep (se 2 (by rfl) ⟨418059, by rfl⟩ : syracuseStep 1114825 = 836119) B836119
theorem B3310793 : Blo 650305 3310793 := bstep (se 2 (by rfl) ⟨1241547, by rfl⟩ : syracuseStep 3310793 = 2483095) B2483095
theorem B6686479 : Blo 650305 6686479 := bstep (se 1 (by rfl) ⟨5014859, by rfl⟩ : syracuseStep 6686479 = 10029719) B10029719
theorem B1115947 : Blo 650305 1115947 := bstep (se 1 (by rfl) ⟨836960, by rfl⟩ : syracuseStep 1115947 = 1673921) B1673921
theorem B1673303 : Blo 650305 1673303 := bstep (se 1 (by rfl) ⟨1254977, by rfl⟩ : syracuseStep 1673303 = 2509955) B2509955
theorem B3967321 : Blo 650305 3967321 := bstep (se 2 (by rfl) ⟨1487745, by rfl⟩ : syracuseStep 3967321 = 2975491) B2975491
theorem B2197907 : Blo 650305 2197907 := bstep (se 1 (by rfl) ⟨1648430, by rfl⟩ : syracuseStep 2197907 = 3296861) B3296861
theorem B17828417 : Blo 650305 17828417 := bstep (se 2 (by rfl) ⟨6685656, by rfl⟩ : syracuseStep 17828417 = 13371313) B13371313
theorem B3705689 : Blo 650305 3705689 := bstep (se 2 (by rfl) ⟨1389633, by rfl⟩ : syracuseStep 3705689 = 2779267) B2779267
theorem B3706145 : Blo 650305 3706145 := bstep (se 2 (by rfl) ⟨1389804, by rfl⟩ : syracuseStep 3706145 = 2779609) B2779609
theorem B3706397 : Blo 650305 3706397 := bstep (se 3 (by rfl) ⟨694949, by rfl⟩ : syracuseStep 3706397 = 1389899) B1389899
theorem B1412743 : Blo 650305 1412743 := bstep (se 1 (by rfl) ⟨1059557, by rfl⟩ : syracuseStep 1412743 = 2119115) B2119115
theorem B7147237 : Blo 650305 7147237 := bstep (se 4 (by rfl) ⟨670053, by rfl⟩ : syracuseStep 7147237 = 1340107) B1340107
theorem B2199311 : Blo 650305 2199311 := bstep (se 1 (by rfl) ⟨1649483, by rfl⟩ : syracuseStep 2199311 = 3298967) B3298967
theorem B9506609 : Blo 650305 9506609 := bstep (se 2 (by rfl) ⟨3564978, by rfl⟩ : syracuseStep 9506609 = 7129957) B7129957
theorem B14323729 : Blo 650305 14323729 := bstep (se 2 (by rfl) ⟨5371398, by rfl⟩ : syracuseStep 14323729 = 10742797) B10742797
theorem B2199581 : Blo 650305 2199581 := bstep (se 3 (by rfl) ⟨412421, by rfl⟩ : syracuseStep 2199581 = 824843) B824843
theorem B3969317 : Blo 650305 3969317 := bstep (se 4 (by rfl) ⟨372123, by rfl⟩ : syracuseStep 3969317 = 744247) B744247
theorem B823927 : Blo 650305 823927 := bstep (se 1 (by rfl) ⟨617945, by rfl⟩ : syracuseStep 823927 = 1235891) B1235891
theorem B824251 : Blo 650305 824251 := bstep (se 1 (by rfl) ⟨618188, by rfl⟩ : syracuseStep 824251 = 1236377) B1236377
theorem B3970241 : Blo 650305 3970241 := bstep (se 2 (by rfl) ⟨1488840, by rfl⟩ : syracuseStep 3970241 = 2977681) B2977681
theorem B2200985 : Blo 650305 2200985 := bstep (se 2 (by rfl) ⟨825369, by rfl⟩ : syracuseStep 2200985 = 1650739) B1650739
theorem B2233975 : Blo 650305 2233975 := bstep (se 1 (by rfl) ⟨1675481, by rfl⟩ : syracuseStep 2233975 = 3350963) B3350963
theorem B8918707 : Blo 650305 8918707 := bstep (se 1 (by rfl) ⟨6689030, by rfl⟩ : syracuseStep 8918707 = 13378061) B13378061
theorem B3708787 : Blo 650305 3708787 := bstep (se 1 (by rfl) ⟨2781590, by rfl⟩ : syracuseStep 3708787 = 5563181) B5563181
theorem B825223 : Blo 650305 825223 := bstep (se 1 (by rfl) ⟨618917, by rfl⟩ : syracuseStep 825223 = 1237835) B1237835
theorem B2201687 : Blo 650305 2201687 := bstep (se 1 (by rfl) ⟨1651265, by rfl⟩ : syracuseStep 2201687 = 3302531) B3302531
theorem B825643 : Blo 650305 825643 := bstep (se 1 (by rfl) ⟨619232, by rfl⟩ : syracuseStep 825643 = 1238465) B1238465
theorem B825871 : Blo 650305 825871 := bstep (se 1 (by rfl) ⟨619403, by rfl⟩ : syracuseStep 825871 = 1238807) B1238807
theorem B2791979 : Blo 650305 2791979 := bstep (se 1 (by rfl) ⟨2093984, by rfl⟩ : syracuseStep 2791979 = 4187969) B4187969
theorem B2202173 : Blo 650305 2202173 := bstep (se 3 (by rfl) ⟨412907, by rfl⟩ : syracuseStep 2202173 = 825815) B825815
theorem B695099 : Blo 650305 695099 := bstep (se 1 (by rfl) ⟨521324, by rfl⟩ : syracuseStep 695099 = 1042649) B1042649
theorem B695227 : Blo 650305 695227 := bstep (se 1 (by rfl) ⟨521420, by rfl⟩ : syracuseStep 695227 = 1042841) B1042841
theorem B826615 : Blo 650305 826615 := bstep (se 1 (by rfl) ⟨619961, by rfl⟩ : syracuseStep 826615 = 1239923) B1239923
theorem B3710245 : Blo 650305 3710245 := bstep (se 4 (by rfl) ⟨347835, by rfl⟩ : syracuseStep 3710245 = 695671) B695671
theorem B826939 : Blo 650305 826939 := bstep (se 1 (by rfl) ⟨620204, by rfl⟩ : syracuseStep 826939 = 1240409) B1240409
theorem B3710771 : Blo 650305 3710771 := bstep (se 1 (by rfl) ⟨2783078, by rfl⟩ : syracuseStep 3710771 = 5566157) B5566157
theorem B2203577 : Blo 650305 2203577 := bstep (se 2 (by rfl) ⟨826341, by rfl⟩ : syracuseStep 2203577 = 1652683) B1652683
theorem B2826193 : Blo 650305 2826193 := bstep (se 2 (by rfl) ⟨1059822, by rfl⟩ : syracuseStep 2826193 = 2119645) B2119645
theorem B3186641 : Blo 650305 3186641 := bstep (se 2 (by rfl) ⟨1194990, by rfl⟩ : syracuseStep 3186641 = 2389981) B2389981
theorem B827435 : Blo 650305 827435 := bstep (se 1 (by rfl) ⟨620576, by rfl⟩ : syracuseStep 827435 = 1241153) B1241153
theorem B794887 : Blo 650305 794887 := bstep (se 1 (by rfl) ⟨596165, by rfl⟩ : syracuseStep 794887 = 1192331) B1192331
theorem B1646963 : Blo 650305 1646963 := bstep (se 1 (by rfl) ⟨1235222, by rfl⟩ : syracuseStep 1646963 = 2470445) B2470445
theorem B827911 : Blo 650305 827911 := bstep (se 1 (by rfl) ⟨620933, by rfl⟩ : syracuseStep 827911 = 1241867) B1241867
theorem B2204171 : Blo 650305 2204171 := bstep (se 1 (by rfl) ⟨1653128, by rfl⟩ : syracuseStep 2204171 = 3306257) B3306257
theorem B2204279 : Blo 650305 2204279 := bstep (se 1 (by rfl) ⟨1653209, by rfl⟩ : syracuseStep 2204279 = 3306419) B3306419
theorem B1647479 : Blo 650305 1647479 := bstep (se 1 (by rfl) ⟨1235609, by rfl⟩ : syracuseStep 1647479 = 2471219) B2471219
theorem B992135 : Blo 650305 992135 := bstep (se 1 (by rfl) ⟨744101, by rfl⟩ : syracuseStep 992135 = 1488203) B1488203
theorem B1319969 : Blo 650305 1319969 := bstep (se 2 (by rfl) ⟨494988, by rfl⟩ : syracuseStep 1319969 = 989977) B989977
theorem B7054397 : Blo 650305 7054397 := bstep (se 3 (by rfl) ⟨1322699, by rfl⟩ : syracuseStep 7054397 = 2645399) B2645399
theorem B2204873 : Blo 650305 2204873 := bstep (se 2 (by rfl) ⟨826827, by rfl⟩ : syracuseStep 2204873 = 1653655) B1653655
theorem B3712229 : Blo 650305 3712229 := bstep (se 4 (by rfl) ⟨348021, by rfl⟩ : syracuseStep 3712229 = 696043) B696043
theorem B40150403 : Blo 650305 40150403 := bstep (se 1 (by rfl) ⟨30112802, by rfl⟩ : syracuseStep 40150403 = 60225605) B60225605
theorem B927163 : Blo 650305 927163 := bstep (se 1 (by rfl) ⟨695372, by rfl⟩ : syracuseStep 927163 = 1390745) B1390745
theorem B1648471 : Blo 650305 1648471 := bstep (se 1 (by rfl) ⟨1236353, by rfl⟩ : syracuseStep 1648471 = 2472707) B2472707
theorem B927607 : Blo 650305 927607 := bstep (se 1 (by rfl) ⟨695705, by rfl⟩ : syracuseStep 927607 = 1391411) B1391411
theorem B2205575 : Blo 650305 2205575 := bstep (se 1 (by rfl) ⟨1654181, by rfl⟩ : syracuseStep 2205575 = 3308363) B3308363
theorem B10758041 : Blo 650305 10758041 := bstep (se 2 (by rfl) ⟨4034265, by rfl⟩ : syracuseStep 10758041 = 8068531) B8068531
theorem B1648775 : Blo 650305 1648775 := bstep (se 1 (by rfl) ⟨1236581, by rfl⟩ : syracuseStep 1648775 = 2473163) B2473163
theorem B2205953 : Blo 650305 2205953 := bstep (se 2 (by rfl) ⟨827232, by rfl⟩ : syracuseStep 2205953 = 1654465) B1654465
theorem B1648907 : Blo 650305 1648907 := bstep (se 1 (by rfl) ⟨1236680, by rfl⟩ : syracuseStep 1648907 = 2473361) B2473361
theorem B19048769 : Blo 650305 19048769 := bstep (se 2 (by rfl) ⟨7143288, by rfl⟩ : syracuseStep 19048769 = 14286577) B14286577
theorem B928427 : Blo 650305 928427 := bstep (se 1 (by rfl) ⟨696320, by rfl⟩ : syracuseStep 928427 = 1392641) B1392641
theorem B23538437 : Blo 650305 23538437 := bstep (se 4 (by rfl) ⟨2206728, by rfl⟩ : syracuseStep 23538437 = 4413457) B4413457
theorem B731911 : Blo 650305 731911 := bstep (se 1 (by rfl) ⟨548933, by rfl⟩ : syracuseStep 731911 = 1097867) B1097867
theorem B1649423 : Blo 650305 1649423 := bstep (se 1 (by rfl) ⟨1237067, by rfl⟩ : syracuseStep 1649423 = 2474135) B2474135
theorem B1649555 : Blo 650305 1649555 := bstep (se 1 (by rfl) ⟨1237166, by rfl⟩ : syracuseStep 1649555 = 2474333) B2474333
theorem B732091 : Blo 650305 732091 := bstep (se 1 (by rfl) ⟨549068, by rfl⟩ : syracuseStep 732091 = 1098137) B1098137
theorem B2206763 : Blo 650305 2206763 := bstep (se 1 (by rfl) ⟨1655072, by rfl⟩ : syracuseStep 2206763 = 3310145) B3310145
theorem B16067645 : Blo 650305 16067645 := bstep (se 3 (by rfl) ⟨3012683, by rfl⟩ : syracuseStep 16067645 = 6025367) B6025367
theorem B30125357 : Blo 650305 30125357 := bstep (se 3 (by rfl) ⟨5648504, by rfl⟩ : syracuseStep 30125357 = 11297009) B11297009
theorem B732559 : Blo 650305 732559 := bstep (se 1 (by rfl) ⟨549419, by rfl⟩ : syracuseStep 732559 = 1098839) B1098839
theorem B2469305 : Blo 650305 2469305 := bstep (se 2 (by rfl) ⟨925989, by rfl⟩ : syracuseStep 2469305 = 1851979) B1851979
theorem B4960115 : Blo 650305 4960115 := bstep (se 1 (by rfl) ⟨3720086, by rfl⟩ : syracuseStep 4960115 = 7440173) B7440173
theorem B733063 : Blo 650305 733063 := bstep (se 1 (by rfl) ⟨549797, by rfl⟩ : syracuseStep 733063 = 1099595) B1099595
theorem B1650689 : Blo 650305 1650689 := bstep (se 2 (by rfl) ⟨619008, by rfl⟩ : syracuseStep 1650689 = 1238017) B1238017
theorem B733243 : Blo 650305 733243 := bstep (se 1 (by rfl) ⟨549932, by rfl⟩ : syracuseStep 733243 = 1099865) B1099865
theorem B1323155 : Blo 650305 1323155 := bstep (se 1 (by rfl) ⟨992366, by rfl⟩ : syracuseStep 1323155 = 1984733) B1984733
theorem B2208059 : Blo 650305 2208059 := bstep (se 1 (by rfl) ⟨1656044, by rfl⟩ : syracuseStep 2208059 = 3312089) B3312089
theorem B1651063 : Blo 650305 1651063 := bstep (se 1 (by rfl) ⟨1238297, by rfl⟩ : syracuseStep 1651063 = 2476595) B2476595
theorem B3387869 : Blo 650305 3387869 := bstep (se 3 (by rfl) ⟨635225, by rfl⟩ : syracuseStep 3387869 = 1270451) B1270451
theorem B930295 : Blo 650305 930295 := bstep (se 1 (by rfl) ⟨697721, by rfl⟩ : syracuseStep 930295 = 1395443) B1395443
theorem B733711 : Blo 650305 733711 := bstep (se 1 (by rfl) ⟨550283, by rfl⟩ : syracuseStep 733711 = 1100567) B1100567
theorem B1389241 : Blo 650305 1389241 := bstep (se 2 (by rfl) ⟨520965, by rfl⟩ : syracuseStep 1389241 = 1041931) B1041931
theorem B1880761 : Blo 650305 1880761 := bstep (se 2 (by rfl) ⟨705285, by rfl⟩ : syracuseStep 1880761 = 1410571) B1410571
theorem B5583653 : Blo 650305 5583653 := bstep (se 4 (by rfl) ⟨523467, by rfl⟩ : syracuseStep 5583653 = 1046935) B1046935
theorem B1651499 : Blo 650305 1651499 := bstep (se 1 (by rfl) ⟨1238624, by rfl⟩ : syracuseStep 1651499 = 2477249) B2477249
theorem B734215 : Blo 650305 734215 := bstep (se 1 (by rfl) ⟨550661, by rfl⟩ : syracuseStep 734215 = 1101323) B1101323
theorem B1061903 : Blo 650305 1061903 := bstep (se 1 (by rfl) ⟨796427, by rfl⟩ : syracuseStep 1061903 = 1592855) B1592855
theorem B734395 : Blo 650305 734395 := bstep (se 1 (by rfl) ⟨550796, by rfl⟩ : syracuseStep 734395 = 1101593) B1101593
theorem B931343 : Blo 650305 931343 := bstep (se 1 (by rfl) ⟨698507, by rfl⟩ : syracuseStep 931343 = 1397015) B1397015
theorem B1652339 : Blo 650305 1652339 := bstep (se 1 (by rfl) ⟨1239254, by rfl⟩ : syracuseStep 1652339 = 2478509) B2478509
theorem B1652359 : Blo 650305 1652359 := bstep (se 1 (by rfl) ⟨1239269, by rfl⟩ : syracuseStep 1652359 = 2478539) B2478539
theorem B734863 : Blo 650305 734863 := bstep (se 1 (by rfl) ⟨551147, by rfl⟩ : syracuseStep 734863 = 1102295) B1102295
theorem B14137163 : Blo 650305 14137163 := bstep (se 1 (by rfl) ⟨10602872, by rfl⟩ : syracuseStep 14137163 = 21205745) B21205745
theorem B1652633 : Blo 650305 1652633 := bstep (se 2 (by rfl) ⟨619737, by rfl⟩ : syracuseStep 1652633 = 1239475) B1239475
theorem B6273035 : Blo 650305 6273035 := bstep (se 1 (by rfl) ⟨4704776, by rfl⟩ : syracuseStep 6273035 = 9409553) B9409553
theorem B1390625 : Blo 650305 1390625 := bstep (se 2 (by rfl) ⟨521484, by rfl⟩ : syracuseStep 1390625 = 1042969) B1042969
theorem B1652795 : Blo 650305 1652795 := bstep (se 1 (by rfl) ⟨1239596, by rfl⟩ : syracuseStep 1652795 = 2479193) B2479193
theorem B1390727 : Blo 650305 1390727 := bstep (se 1 (by rfl) ⟨1043045, by rfl⟩ : syracuseStep 1390727 = 2086091) B2086091
theorem B735367 : Blo 650305 735367 := bstep (se 1 (by rfl) ⟨551525, by rfl⟩ : syracuseStep 735367 = 1103051) B1103051
theorem B1653007 : Blo 650305 1653007 := bstep (se 1 (by rfl) ⟨1239755, by rfl⟩ : syracuseStep 1653007 = 2479511) B2479511
theorem B1718561 : Blo 650305 1718561 := bstep (se 2 (by rfl) ⟨644460, by rfl⟩ : syracuseStep 1718561 = 1288921) B1288921
theorem B735547 : Blo 650305 735547 := bstep (se 1 (by rfl) ⟨551660, by rfl⟩ : syracuseStep 735547 = 1103321) B1103321
theorem B1980791 : Blo 650305 1980791 := bstep (se 1 (by rfl) ⟨1485593, by rfl⟩ : syracuseStep 1980791 = 2971187) B2971187
theorem B1653281 : Blo 650305 1653281 := bstep (se 2 (by rfl) ⟨619980, by rfl⟩ : syracuseStep 1653281 = 1239961) B1239961
theorem B2505277 : Blo 650305 2505277 := bstep (se 3 (by rfl) ⟨469739, by rfl⟩ : syracuseStep 2505277 = 939479) B939479
theorem B736015 : Blo 650305 736015 := bstep (se 1 (by rfl) ⟨552011, by rfl⟩ : syracuseStep 736015 = 1104023) B1104023
theorem B1981217 : Blo 650305 1981217 := bstep (se 2 (by rfl) ⟨742956, by rfl⟩ : syracuseStep 1981217 = 1485913) B1485913
theorem B8338211 : Blo 650305 8338211 := bstep (se 1 (by rfl) ⟨6253658, by rfl⟩ : syracuseStep 8338211 = 12507317) B12507317
theorem B25115507 : Blo 650305 25115507 := bstep (se 1 (by rfl) ⟨18836630, by rfl⟩ : syracuseStep 25115507 = 37673261) B37673261
theorem B2472889 : Blo 650305 2472889 := bstep (se 2 (by rfl) ⟨927333, by rfl⟩ : syracuseStep 2472889 = 1854667) B1854667
theorem B1490219 : Blo 650305 1490219 := bstep (se 1 (by rfl) ⟨1117664, by rfl⟩ : syracuseStep 1490219 = 2235329) B2235329
theorem B1588567 : Blo 650305 1588567 := bstep (se 1 (by rfl) ⟨1191425, by rfl⟩ : syracuseStep 1588567 = 2382851) B2382851
theorem B1654283 : Blo 650305 1654283 := bstep (se 1 (by rfl) ⟨1240712, by rfl⟩ : syracuseStep 1654283 = 2481425) B2481425
theorem B1097401 : Blo 650305 1097401 := bstep (se 2 (by rfl) ⟨411525, by rfl⟩ : syracuseStep 1097401 = 823051) B823051
theorem B2637683 : Blo 650305 2637683 := bstep (se 1 (by rfl) ⟨1978262, by rfl⟩ : syracuseStep 2637683 = 3956525) B3956525
theorem B1654931 : Blo 650305 1654931 := bstep (se 1 (by rfl) ⟨1241198, by rfl⟩ : syracuseStep 1654931 = 2482397) B2482397
theorem B4702445 : Blo 650305 4702445 := bstep (se 3 (by rfl) ⟨881708, by rfl⟩ : syracuseStep 4702445 = 1763417) B1763417
theorem B1098103 : Blo 650305 1098103 := bstep (se 1 (by rfl) ⟨823577, by rfl⟩ : syracuseStep 1098103 = 1647155) B1647155
theorem B1655225 : Blo 650305 1655225 := bstep (se 2 (by rfl) ⟨620709, by rfl⟩ : syracuseStep 1655225 = 1241419) B1241419
theorem B6111773 : Blo 650305 6111773 := bstep (se 3 (by rfl) ⟨1145957, by rfl⟩ : syracuseStep 6111773 = 2291915) B2291915
theorem B1098299 : Blo 650305 1098299 := bstep (se 1 (by rfl) ⟨823724, by rfl⟩ : syracuseStep 1098299 = 1647449) B1647449
theorem B3293783 : Blo 650305 3293783 := bstep (se 1 (by rfl) ⟨2470337, by rfl⟩ : syracuseStep 3293783 = 4940675) B4940675
theorem B5587649 : Blo 650305 5587649 := bstep (se 2 (by rfl) ⟨2095368, by rfl⟩ : syracuseStep 5587649 = 4190737) B4190737
theorem B1852105 : Blo 650305 1852105 := bstep (se 2 (by rfl) ⟨694539, by rfl⟩ : syracuseStep 1852105 = 1389079) B1389079
theorem B3719951 : Blo 650305 3719951 := bstep (se 1 (by rfl) ⟨2789963, by rfl⟩ : syracuseStep 3719951 = 5579927) B5579927
theorem B1098697 : Blo 650305 1098697 := bstep (se 2 (by rfl) ⟨412011, by rfl⟩ : syracuseStep 1098697 = 824023) B824023
theorem B3294269 : Blo 650305 3294269 := bstep (se 3 (by rfl) ⟨617675, by rfl⟩ : syracuseStep 3294269 = 1235351) B1235351
theorem B1590359 : Blo 650305 1590359 := bstep (se 1 (by rfl) ⟨1192769, by rfl⟩ : syracuseStep 1590359 = 2385539) B2385539
theorem B1655923 : Blo 650305 1655923 := bstep (se 1 (by rfl) ⟨1241942, by rfl⟩ : syracuseStep 1655923 = 2483885) B2483885
theorem B1656065 : Blo 650305 1656065 := bstep (se 2 (by rfl) ⟨621024, by rfl⟩ : syracuseStep 1656065 = 1242049) B1242049
theorem B3393085 : Blo 650305 3393085 := bstep (se 3 (by rfl) ⟨636203, by rfl⟩ : syracuseStep 3393085 = 1272407) B1272407
theorem B1099399 : Blo 650305 1099399 := bstep (se 1 (by rfl) ⟨824549, by rfl⟩ : syracuseStep 1099399 = 1649099) B1649099
theorem B4474597 : Blo 650305 4474597 := bstep (se 4 (by rfl) ⟨419493, by rfl⟩ : syracuseStep 4474597 = 838987) B838987
theorem B2475791 : Blo 650305 2475791 := bstep (se 1 (by rfl) ⟨1856843, by rfl⟩ : syracuseStep 2475791 = 3713687) B3713687
theorem B2639675 : Blo 650305 2639675 := bstep (se 1 (by rfl) ⟨1979756, by rfl⟩ : syracuseStep 2639675 = 3959513) B3959513
theorem B3524411 : Blo 650305 3524411 := bstep (se 1 (by rfl) ⟨2643308, by rfl⟩ : syracuseStep 3524411 = 5286617) B5286617
theorem B3721409 : Blo 650305 3721409 := bstep (se 2 (by rfl) ⟨1395528, by rfl⟩ : syracuseStep 3721409 = 2791057) B2791057
theorem B1853711 : Blo 650305 1853711 := bstep (se 1 (by rfl) ⟨1390283, by rfl⟩ : syracuseStep 1853711 = 2780567) B2780567
theorem B1100047 : Blo 650305 1100047 := bstep (se 1 (by rfl) ⟨825035, by rfl⟩ : syracuseStep 1100047 = 1650071) B1650071
theorem B7129565 : Blo 650305 7129565 := bstep (se 3 (by rfl) ⟨1336793, by rfl⟩ : syracuseStep 7129565 = 2673587) B2673587
theorem B2509373 : Blo 650305 2509373 := bstep (se 3 (by rfl) ⟨470507, by rfl⟩ : syracuseStep 2509373 = 941015) B941015
theorem B1592075 : Blo 650305 1592075 := bstep (se 1 (by rfl) ⟨1194056, by rfl⟩ : syracuseStep 1592075 = 2388113) B2388113
theorem B1100587 : Blo 650305 1100587 := bstep (se 1 (by rfl) ⟨825440, by rfl⟩ : syracuseStep 1100587 = 1650881) B1650881
theorem B3296051 : Blo 650305 3296051 := bstep (se 1 (by rfl) ⟨2472038, by rfl⟩ : syracuseStep 3296051 = 4944077) B4944077
theorem B1100729 : Blo 650305 1100729 := bstep (se 2 (by rfl) ⟨412773, by rfl⟩ : syracuseStep 1100729 = 825547) B825547
theorem B4770839 : Blo 650305 4770839 := bstep (se 1 (by rfl) ⟨3578129, by rfl⟩ : syracuseStep 4770839 = 7156259) B7156259
theorem B2083927 : Blo 650305 2083927 := bstep (se 1 (by rfl) ⟨1562945, by rfl⟩ : syracuseStep 2083927 = 3125891) B3125891
theorem B3132503 : Blo 650305 3132503 := bstep (se 1 (by rfl) ⟨2349377, by rfl⟩ : syracuseStep 3132503 = 4698755) B4698755
theorem B3296375 : Blo 650305 3296375 := bstep (se 1 (by rfl) ⟨2472281, by rfl⟩ : syracuseStep 3296375 = 4944563) B4944563
theorem B7949627 : Blo 650305 7949627 := bstep (se 1 (by rfl) ⟨5962220, by rfl⟩ : syracuseStep 7949627 = 11924441) B11924441
theorem B1854839 : Blo 650305 1854839 := bstep (se 1 (by rfl) ⟨1391129, by rfl⟩ : syracuseStep 1854839 = 2782259) B2782259
theorem B1101431 : Blo 650305 1101431 := bstep (se 1 (by rfl) ⟨826073, by rfl⟩ : syracuseStep 1101431 = 1652147) B1652147
theorem B3755929 : Blo 650305 3755929 := bstep (se 2 (by rfl) ⟨1408473, by rfl⟩ : syracuseStep 3755929 = 2816947) B2816947
theorem B1101883 : Blo 650305 1101883 := bstep (se 1 (by rfl) ⟨826412, by rfl⟩ : syracuseStep 1101883 = 1652825) B1652825
theorem B3297347 : Blo 650305 3297347 := bstep (se 1 (by rfl) ⟨2473010, by rfl⟩ : syracuseStep 3297347 = 4946021) B4946021
theorem B1102025 : Blo 650305 1102025 := bstep (se 2 (by rfl) ⟨413259, by rfl⟩ : syracuseStep 1102025 = 826519) B826519
theorem B3297671 : Blo 650305 3297671 := bstep (se 1 (by rfl) ⟨2473253, by rfl⟩ : syracuseStep 3297671 = 4946507) B4946507
theorem B2511371 : Blo 650305 2511371 := bstep (se 1 (by rfl) ⟨1883528, by rfl⟩ : syracuseStep 2511371 = 3767057) B3767057
theorem B1987361 : Blo 650305 1987361 := bstep (se 2 (by rfl) ⟨745260, by rfl⟩ : syracuseStep 1987361 = 1490521) B1490521
theorem B1102727 : Blo 650305 1102727 := bstep (se 1 (by rfl) ⟨827045, by rfl⟩ : syracuseStep 1102727 = 1654091) B1654091
theorem B2478995 : Blo 650305 2478995 := bstep (se 1 (by rfl) ⟨1859246, by rfl⟩ : syracuseStep 2478995 = 3718493) B3718493
theorem B1856513 : Blo 650305 1856513 := bstep (se 2 (by rfl) ⟨696192, by rfl⟩ : syracuseStep 1856513 = 1392385) B1392385
theorem B7918679 : Blo 650305 7918679 := bstep (se 1 (by rfl) ⟨5939009, by rfl⟩ : syracuseStep 7918679 = 11878019) B11878019
theorem B1758323 : Blo 650305 1758323 := bstep (se 1 (by rfl) ⟨1318742, by rfl⟩ : syracuseStep 1758323 = 2637485) B2637485
theorem B1856627 : Blo 650305 1856627 := bstep (se 1 (by rfl) ⟨1392470, by rfl⟩ : syracuseStep 1856627 = 2784941) B2784941
theorem B1463687 : Blo 650305 1463687 := bstep (se 1 (by rfl) ⟨1097765, by rfl⟩ : syracuseStep 1463687 = 2195531) B2195531
theorem B1856969 : Blo 650305 1856969 := bstep (se 2 (by rfl) ⟨696363, by rfl⟩ : syracuseStep 1856969 = 1392727) B1392727
theorem B1103375 : Blo 650305 1103375 := bstep (se 1 (by rfl) ⟨827531, by rfl⟩ : syracuseStep 1103375 = 1655063) B1655063
theorem B3135019 : Blo 650305 3135019 := bstep (se 1 (by rfl) ⟨2351264, by rfl⟩ : syracuseStep 3135019 = 4702529) B4702529
theorem B1463867 : Blo 650305 1463867 := bstep (se 1 (by rfl) ⟨1097900, by rfl⟩ : syracuseStep 1463867 = 2195801) B2195801
theorem B1463993 : Blo 650305 1463993 := bstep (se 2 (by rfl) ⟨548997, by rfl⟩ : syracuseStep 1463993 = 1097995) B1097995
theorem B939721 : Blo 650305 939721 := bstep (se 2 (by rfl) ⟨352395, by rfl⟩ : syracuseStep 939721 = 704791) B704791
theorem B27121483 : Blo 650305 27121483 := bstep (se 1 (by rfl) ⟨20341112, by rfl⟩ : syracuseStep 27121483 = 40682225) B40682225
theorem B1234835 : Blo 650305 1234835 := bstep (se 1 (by rfl) ⟨926126, by rfl⟩ : syracuseStep 1234835 = 1852253) B1852253
theorem B1464335 : Blo 650305 1464335 := bstep (se 1 (by rfl) ⟨1098251, by rfl⟩ : syracuseStep 1464335 = 2196503) B2196503
theorem B1464353 : Blo 650305 1464353 := bstep (se 2 (by rfl) ⟨549132, by rfl⟩ : syracuseStep 1464353 = 1098265) B1098265
theorem B1103915 : Blo 650305 1103915 := bstep (se 1 (by rfl) ⟨827936, by rfl⟩ : syracuseStep 1103915 = 1655873) B1655873
theorem B3758147 : Blo 650305 3758147 := bstep (se 1 (by rfl) ⟨2818610, by rfl⟩ : syracuseStep 3758147 = 5637221) B5637221
theorem B1562743 : Blo 650305 1562743 := bstep (se 1 (by rfl) ⟨1172057, by rfl⟩ : syracuseStep 1562743 = 2344115) B2344115
theorem B1235063 : Blo 650305 1235063 := bstep (se 1 (by rfl) ⟨926297, by rfl⟩ : syracuseStep 1235063 = 1852595) B1852595
theorem B1464695 : Blo 650305 1464695 := bstep (se 1 (by rfl) ⟨1098521, by rfl⟩ : syracuseStep 1464695 = 2197043) B2197043
theorem B5560721 : Blo 650305 5560721 := bstep (se 2 (by rfl) ⟨2085270, by rfl⟩ : syracuseStep 5560721 = 4170541) B4170541
theorem B2480651 : Blo 650305 2480651 := bstep (se 1 (by rfl) ⟨1860488, by rfl⟩ : syracuseStep 2480651 = 3720977) B3720977
theorem B1464875 : Blo 650305 1464875 := bstep (se 1 (by rfl) ⟨1098656, by rfl⟩ : syracuseStep 1464875 = 2197313) B2197313
theorem B3529277 : Blo 650305 3529277 := bstep (se 3 (by rfl) ⟨661739, by rfl⟩ : syracuseStep 3529277 = 1323479) B1323479
theorem B6282035 : Blo 650305 6282035 := bstep (se 1 (by rfl) ⟨4711526, by rfl⟩ : syracuseStep 6282035 = 9423053) B9423053
theorem B1465235 : Blo 650305 1465235 := bstep (se 1 (by rfl) ⟨1098926, by rfl⟩ : syracuseStep 1465235 = 2197853) B2197853
theorem B11131829 : Blo 650305 11131829 := bstep (se 5 (by rfl) ⟨521804, by rfl⟩ : syracuseStep 11131829 = 1043609) B1043609
theorem B1465289 : Blo 650305 1465289 := bstep (se 2 (by rfl) ⟨549483, by rfl⟩ : syracuseStep 1465289 = 1098967) B1098967
theorem B3726283 : Blo 650305 3726283 := bstep (se 1 (by rfl) ⟨2794712, by rfl⟩ : syracuseStep 3726283 = 5589425) B5589425
theorem B5561405 : Blo 650305 5561405 := bstep (se 3 (by rfl) ⟨1042763, by rfl⟩ : syracuseStep 5561405 = 2085527) B2085527
theorem B2088193 : Blo 650305 2088193 := bstep (se 2 (by rfl) ⟨783072, by rfl⟩ : syracuseStep 2088193 = 1566145) B1566145
theorem B1858859 : Blo 650305 1858859 := bstep (se 1 (by rfl) ⟨1394144, by rfl⟩ : syracuseStep 1858859 = 2788289) B2788289
theorem B4939217 : Blo 650305 4939217 := bstep (se 2 (by rfl) ⟨1852206, by rfl⟩ : syracuseStep 4939217 = 3704413) B3704413
theorem B1859087 : Blo 650305 1859087 := bstep (se 1 (by rfl) ⟨1394315, by rfl⟩ : syracuseStep 1859087 = 2788631) B2788631
theorem B1465991 : Blo 650305 1465991 := bstep (se 1 (by rfl) ⟨1099493, by rfl⟩ : syracuseStep 1465991 = 2198987) B2198987
theorem B1236779 : Blo 650305 1236779 := bstep (se 1 (by rfl) ⟨927584, by rfl⟩ : syracuseStep 1236779 = 1855169) B1855169
theorem B1466171 : Blo 650305 1466171 := bstep (se 1 (by rfl) ⟨1099628, by rfl⟩ : syracuseStep 1466171 = 2199257) B2199257
theorem B6250355 : Blo 650305 6250355 := bstep (se 1 (by rfl) ⟨4687766, by rfl⟩ : syracuseStep 6250355 = 9375533) B9375533
theorem B3301235 : Blo 650305 3301235 := bstep (se 1 (by rfl) ⟨2475926, by rfl⟩ : syracuseStep 3301235 = 4951853) B4951853
theorem B2973593 : Blo 650305 2973593 := bstep (se 2 (by rfl) ⟨1115097, by rfl⟩ : syracuseStep 2973593 = 2230195) B2230195
theorem B1466297 : Blo 650305 1466297 := bstep (se 2 (by rfl) ⟨549861, by rfl⟩ : syracuseStep 1466297 = 1099723) B1099723
theorem B1237007 : Blo 650305 1237007 := bstep (se 1 (by rfl) ⟨927755, by rfl⟩ : syracuseStep 1237007 = 1855511) B1855511
theorem B2646083 : Blo 650305 2646083 := bstep (se 1 (by rfl) ⟨1984562, by rfl⟩ : syracuseStep 2646083 = 3969125) B3969125
theorem B6250583 : Blo 650305 6250583 := bstep (se 1 (by rfl) ⟨4687937, by rfl⟩ : syracuseStep 6250583 = 9375875) B9375875
theorem B1466639 : Blo 650305 1466639 := bstep (se 1 (by rfl) ⟨1099979, by rfl⟩ : syracuseStep 1466639 = 2199959) B2199959
theorem B1466657 : Blo 650305 1466657 := bstep (se 2 (by rfl) ⟨549996, by rfl⟩ : syracuseStep 1466657 = 1099993) B1099993
theorem B3825953 : Blo 650305 3825953 := bstep (se 2 (by rfl) ⟨1434732, by rfl⟩ : syracuseStep 3825953 = 2869465) B2869465
theorem B3301721 : Blo 650305 3301721 := bstep (se 2 (by rfl) ⟨1238145, by rfl⟩ : syracuseStep 3301721 = 2476291) B2476291
theorem B975479 : Blo 650305 975479 := bstep (se 1 (by rfl) ⟨731609, by rfl⟩ : syracuseStep 975479 = 1463219) B1463219
theorem B1466999 : Blo 650305 1466999 := bstep (se 1 (by rfl) ⟨1100249, by rfl⟩ : syracuseStep 1466999 = 2200499) B2200499
theorem B975503 : Blo 650305 975503 := bstep (se 1 (by rfl) ⟨731627, by rfl⟩ : syracuseStep 975503 = 1463255) B1463255
theorem B975545 : Blo 650305 975545 := bstep (se 2 (by rfl) ⟨365829, by rfl⟩ : syracuseStep 975545 = 731659) B731659
theorem B975623 : Blo 650305 975623 := bstep (se 1 (by rfl) ⟨731717, by rfl⟩ : syracuseStep 975623 = 1463435) B1463435
theorem B9429797 : Blo 650305 9429797 := bstep (se 4 (by rfl) ⟨884043, by rfl⟩ : syracuseStep 9429797 = 1768087) B1768087
theorem B975659 : Blo 650305 975659 := bstep (se 1 (by rfl) ⟨731744, by rfl⟩ : syracuseStep 975659 = 1463489) B1463489
theorem B1467179 : Blo 650305 1467179 := bstep (se 1 (by rfl) ⟨1100384, by rfl⟩ : syracuseStep 1467179 = 2200769) B2200769
theorem B975689 : Blo 650305 975689 := bstep (se 2 (by rfl) ⟨365883, by rfl⟩ : syracuseStep 975689 = 731767) B731767
theorem B2351987 : Blo 650305 2351987 := bstep (se 1 (by rfl) ⟨1763990, by rfl⟩ : syracuseStep 2351987 = 3527981) B3527981
theorem B1860499 : Blo 650305 1860499 := bstep (se 1 (by rfl) ⟨1395374, by rfl⟩ : syracuseStep 1860499 = 2790749) B2790749
theorem B5235619 : Blo 650305 5235619 := bstep (se 1 (by rfl) ⟨3926714, by rfl⟩ : syracuseStep 5235619 = 7853429) B7853429
theorem B975803 : Blo 650305 975803 := bstep (se 1 (by rfl) ⟨731852, by rfl⟩ : syracuseStep 975803 = 1463705) B1463705
theorem B975863 : Blo 650305 975863 := bstep (se 1 (by rfl) ⟨731897, by rfl⟩ : syracuseStep 975863 = 1463795) B1463795
theorem B975887 : Blo 650305 975887 := bstep (se 1 (by rfl) ⟨731915, by rfl⟩ : syracuseStep 975887 = 1463831) B1463831
theorem B975929 : Blo 650305 975929 := bstep (se 2 (by rfl) ⟨365973, by rfl⟩ : syracuseStep 975929 = 731947) B731947
theorem B1860727 : Blo 650305 1860727 := bstep (se 1 (by rfl) ⟨1395545, by rfl⟩ : syracuseStep 1860727 = 2791091) B2791091
theorem B976007 : Blo 650305 976007 := bstep (se 1 (by rfl) ⟨732005, by rfl⟩ : syracuseStep 976007 = 1464011) B1464011
theorem B1467539 : Blo 650305 1467539 := bstep (se 1 (by rfl) ⟨1100654, by rfl⟩ : syracuseStep 1467539 = 2201309) B2201309
theorem B976043 : Blo 650305 976043 := bstep (se 1 (by rfl) ⟨732032, by rfl⟩ : syracuseStep 976043 = 1464065) B1464065
theorem B976073 : Blo 650305 976073 := bstep (se 2 (by rfl) ⟨366027, by rfl⟩ : syracuseStep 976073 = 732055) B732055
theorem B1467593 : Blo 650305 1467593 := bstep (se 2 (by rfl) ⟨550347, by rfl⟩ : syracuseStep 1467593 = 1100695) B1100695
theorem B8381677 : Blo 650305 8381677 := bstep (se 3 (by rfl) ⟨1571564, by rfl⟩ : syracuseStep 8381677 = 3143129) B3143129
theorem B1041707 : Blo 650305 1041707 := bstep (se 1 (by rfl) ⟨781280, by rfl⟩ : syracuseStep 1041707 = 1562561) B1562561
theorem B943417 : Blo 650305 943417 := bstep (se 2 (by rfl) ⟨353781, by rfl⟩ : syracuseStep 943417 = 707563) B707563
theorem B976187 : Blo 650305 976187 := bstep (se 1 (by rfl) ⟨732140, by rfl⟩ : syracuseStep 976187 = 1464281) B1464281
theorem B976247 : Blo 650305 976247 := bstep (se 1 (by rfl) ⟨732185, by rfl⟩ : syracuseStep 976247 = 1464371) B1464371
theorem B2516359 : Blo 650305 2516359 := bstep (se 1 (by rfl) ⟨1887269, by rfl⟩ : syracuseStep 2516359 = 3774539) B3774539
theorem B976271 : Blo 650305 976271 := bstep (se 1 (by rfl) ⟨732203, by rfl⟩ : syracuseStep 976271 = 1464407) B1464407
theorem B4187537 : Blo 650305 4187537 := bstep (se 2 (by rfl) ⟨1570326, by rfl⟩ : syracuseStep 4187537 = 3140653) B3140653
theorem B1238419 : Blo 650305 1238419 := bstep (se 1 (by rfl) ⟨928814, by rfl⟩ : syracuseStep 1238419 = 1857629) B1857629
theorem B976313 : Blo 650305 976313 := bstep (se 2 (by rfl) ⟨366117, by rfl⟩ : syracuseStep 976313 = 732235) B732235
theorem B3139019 : Blo 650305 3139019 := bstep (se 1 (by rfl) ⟨2354264, by rfl⟩ : syracuseStep 3139019 = 4708529) B4708529
theorem B976391 : Blo 650305 976391 := bstep (se 1 (by rfl) ⟨732293, by rfl⟩ : syracuseStep 976391 = 1464587) B1464587
theorem B976427 : Blo 650305 976427 := bstep (se 1 (by rfl) ⟨732320, by rfl⟩ : syracuseStep 976427 = 1464641) B1464641
theorem B976457 : Blo 650305 976457 := bstep (se 2 (by rfl) ⟨366171, by rfl⟩ : syracuseStep 976457 = 732343) B732343
theorem B1238647 : Blo 650305 1238647 := bstep (se 1 (by rfl) ⟨928985, by rfl⟩ : syracuseStep 1238647 = 1857971) B1857971
theorem B976571 : Blo 650305 976571 := bstep (se 1 (by rfl) ⟨732428, by rfl⟩ : syracuseStep 976571 = 1464857) B1464857
theorem B976631 : Blo 650305 976631 := bstep (se 1 (by rfl) ⟨732473, by rfl⟩ : syracuseStep 976631 = 1464947) B1464947
theorem B1697537 : Blo 650305 1697537 := bstep (se 2 (by rfl) ⟨636576, by rfl⟩ : syracuseStep 1697537 = 1273153) B1273153
theorem B976655 : Blo 650305 976655 := bstep (se 1 (by rfl) ⟨732491, by rfl⟩ : syracuseStep 976655 = 1464983) B1464983
theorem B4450099 : Blo 650305 4450099 := bstep (se 1 (by rfl) ⟨3337574, by rfl⟩ : syracuseStep 4450099 = 6675149) B6675149
theorem B976697 : Blo 650305 976697 := bstep (se 2 (by rfl) ⟨366261, by rfl⟩ : syracuseStep 976697 = 732523) B732523
theorem B976775 : Blo 650305 976775 := bstep (se 1 (by rfl) ⟨732581, by rfl⟩ : syracuseStep 976775 = 1465163) B1465163
theorem B1468295 : Blo 650305 1468295 := bstep (se 1 (by rfl) ⟨1101221, by rfl⟩ : syracuseStep 1468295 = 2202443) B2202443
theorem B976811 : Blo 650305 976811 := bstep (se 1 (by rfl) ⟨732608, by rfl⟩ : syracuseStep 976811 = 1465217) B1465217
theorem B976841 : Blo 650305 976841 := bstep (se 2 (by rfl) ⟨366315, by rfl⟩ : syracuseStep 976841 = 732631) B732631
theorem B2353195 : Blo 650305 2353195 := bstep (se 1 (by rfl) ⟨1764896, by rfl⟩ : syracuseStep 2353195 = 3529793) B3529793
theorem B976955 : Blo 650305 976955 := bstep (se 1 (by rfl) ⟨732716, by rfl⟩ : syracuseStep 976955 = 1465433) B1465433
theorem B1468475 : Blo 650305 1468475 := bstep (se 1 (by rfl) ⟨1101356, by rfl⟩ : syracuseStep 1468475 = 2202713) B2202713
theorem B5662781 : Blo 650305 5662781 := bstep (se 3 (by rfl) ⟨1061771, by rfl⟩ : syracuseStep 5662781 = 2123543) B2123543
theorem B977015 : Blo 650305 977015 := bstep (se 1 (by rfl) ⟨732761, by rfl⟩ : syracuseStep 977015 = 1465523) B1465523
theorem B977039 : Blo 650305 977039 := bstep (se 1 (by rfl) ⟨732779, by rfl⟩ : syracuseStep 977039 = 1465559) B1465559
theorem B977081 : Blo 650305 977081 := bstep (se 2 (by rfl) ⟨366405, by rfl⟩ : syracuseStep 977081 = 732811) B732811
theorem B1763513 : Blo 650305 1763513 := bstep (se 2 (by rfl) ⟨661317, by rfl⟩ : syracuseStep 1763513 = 1322635) B1322635
theorem B1468601 : Blo 650305 1468601 := bstep (se 2 (by rfl) ⟨550725, by rfl⟩ : syracuseStep 1468601 = 1101451) B1101451
theorem B2648321 : Blo 650305 2648321 := bstep (se 2 (by rfl) ⟨993120, by rfl⟩ : syracuseStep 2648321 = 1986241) B1986241
theorem B977159 : Blo 650305 977159 := bstep (se 1 (by rfl) ⟨732869, by rfl⟩ : syracuseStep 977159 = 1465739) B1465739
theorem B977195 : Blo 650305 977195 := bstep (se 1 (by rfl) ⟨732896, by rfl⟩ : syracuseStep 977195 = 1465793) B1465793
theorem B977225 : Blo 650305 977225 := bstep (se 2 (by rfl) ⟨366459, by rfl⟩ : syracuseStep 977225 = 732919) B732919
theorem B1862003 : Blo 650305 1862003 := bstep (se 1 (by rfl) ⟨1396502, by rfl⟩ : syracuseStep 1862003 = 2793005) B2793005
theorem B3664273 : Blo 650305 3664273 := bstep (se 2 (by rfl) ⟨1374102, by rfl⟩ : syracuseStep 3664273 = 2748205) B2748205
theorem B3303827 : Blo 650305 3303827 := bstep (se 1 (by rfl) ⟨2477870, by rfl⟩ : syracuseStep 3303827 = 4955741) B4955741
theorem B977339 : Blo 650305 977339 := bstep (se 1 (by rfl) ⟨733004, by rfl⟩ : syracuseStep 977339 = 1466009) B1466009
theorem B977399 : Blo 650305 977399 := bstep (se 1 (by rfl) ⟨733049, by rfl⟩ : syracuseStep 977399 = 1466099) B1466099
theorem B977423 : Blo 650305 977423 := bstep (se 1 (by rfl) ⟨733067, by rfl⟩ : syracuseStep 977423 = 1466135) B1466135
theorem B1468943 : Blo 650305 1468943 := bstep (se 1 (by rfl) ⟨1101707, by rfl⟩ : syracuseStep 1468943 = 2203415) B2203415
theorem B1468961 : Blo 650305 1468961 := bstep (se 2 (by rfl) ⟨550860, by rfl⟩ : syracuseStep 1468961 = 1101721) B1101721
theorem B977465 : Blo 650305 977465 := bstep (se 2 (by rfl) ⟨366549, by rfl⟩ : syracuseStep 977465 = 733099) B733099
theorem B977543 : Blo 650305 977543 := bstep (se 1 (by rfl) ⟨733157, by rfl⟩ : syracuseStep 977543 = 1466315) B1466315
theorem B977579 : Blo 650305 977579 := bstep (se 1 (by rfl) ⟨733184, by rfl⟩ : syracuseStep 977579 = 1466369) B1466369
theorem B7432883 : Blo 650305 7432883 := bstep (se 1 (by rfl) ⟨5574662, by rfl⟩ : syracuseStep 7432883 = 11149325) B11149325
theorem B977609 : Blo 650305 977609 := bstep (se 2 (by rfl) ⟨366603, by rfl⟩ : syracuseStep 977609 = 733207) B733207
theorem B1862345 : Blo 650305 1862345 := bstep (se 2 (by rfl) ⟨698379, by rfl⟩ : syracuseStep 1862345 = 1396759) B1396759
theorem B977723 : Blo 650305 977723 := bstep (se 1 (by rfl) ⟨733292, by rfl⟩ : syracuseStep 977723 = 1466585) B1466585
theorem B1862459 : Blo 650305 1862459 := bstep (se 1 (by rfl) ⟨1396844, by rfl⟩ : syracuseStep 1862459 = 2793689) B2793689
theorem B3140441 : Blo 650305 3140441 := bstep (se 2 (by rfl) ⟨1177665, by rfl⟩ : syracuseStep 3140441 = 2355331) B2355331
theorem B977783 : Blo 650305 977783 := bstep (se 1 (by rfl) ⟨733337, by rfl⟩ : syracuseStep 977783 = 1466675) B1466675
theorem B1469303 : Blo 650305 1469303 := bstep (se 1 (by rfl) ⟨1101977, by rfl⟩ : syracuseStep 1469303 = 2203955) B2203955
theorem B977807 : Blo 650305 977807 := bstep (se 1 (by rfl) ⟨733355, by rfl⟩ : syracuseStep 977807 = 1466711) B1466711
theorem B977849 : Blo 650305 977849 := bstep (se 2 (by rfl) ⟨366693, by rfl⟩ : syracuseStep 977849 = 733387) B733387
theorem B1862585 : Blo 650305 1862585 := bstep (se 2 (by rfl) ⟨698469, by rfl⟩ : syracuseStep 1862585 = 1396939) B1396939
theorem B977927 : Blo 650305 977927 := bstep (se 1 (by rfl) ⟨733445, by rfl⟩ : syracuseStep 977927 = 1466891) B1466891
theorem B3009565 : Blo 650305 3009565 := bstep (se 3 (by rfl) ⟨564293, by rfl⟩ : syracuseStep 3009565 = 1128587) B1128587
theorem B977963 : Blo 650305 977963 := bstep (se 1 (by rfl) ⟨733472, by rfl⟩ : syracuseStep 977963 = 1466945) B1466945
theorem B1469483 : Blo 650305 1469483 := bstep (se 1 (by rfl) ⟨1102112, by rfl⟩ : syracuseStep 1469483 = 2204225) B2204225
theorem B3140669 : Blo 650305 3140669 := bstep (se 3 (by rfl) ⟨588875, by rfl⟩ : syracuseStep 3140669 = 1177751) B1177751
theorem B977993 : Blo 650305 977993 := bstep (se 2 (by rfl) ⟨366747, by rfl⟩ : syracuseStep 977993 = 733495) B733495
theorem B650375 : Blo 650305 650375 := bstep (se 1 (by rfl) ⟨487781, by rfl⟩ : syracuseStep 650375 = 975563) B975563
theorem B650383 : Blo 650305 650383 := bstep (se 1 (by rfl) ⟨487787, by rfl⟩ : syracuseStep 650383 = 975575) B975575
theorem B1240211 : Blo 650305 1240211 := bstep (se 1 (by rfl) ⟨930158, by rfl⟩ : syracuseStep 1240211 = 1860317) B1860317
theorem B650427 : Blo 650305 650427 := bstep (se 1 (by rfl) ⟨487820, by rfl⟩ : syracuseStep 650427 = 975641) B975641
theorem B978107 : Blo 650305 978107 := bstep (se 1 (by rfl) ⟨733580, by rfl⟩ : syracuseStep 978107 = 1467161) B1467161
theorem B1240265 : Blo 650305 1240265 := bstep (se 2 (by rfl) ⟨465099, by rfl⟩ : syracuseStep 1240265 = 930199) B930199
theorem B978167 : Blo 650305 978167 := bstep (se 1 (by rfl) ⟨733625, by rfl⟩ : syracuseStep 978167 = 1467251) B1467251
theorem B650503 : Blo 650305 650503 := bstep (se 1 (by rfl) ⟨487877, by rfl⟩ : syracuseStep 650503 = 975755) B975755
theorem B650511 : Blo 650305 650511 := bstep (se 1 (by rfl) ⟨487883, by rfl⟩ : syracuseStep 650511 = 975767) B975767
theorem B978191 : Blo 650305 978191 := bstep (se 1 (by rfl) ⟨733643, by rfl⟩ : syracuseStep 978191 = 1467287) B1467287
theorem B1240363 : Blo 650305 1240363 := bstep (se 1 (by rfl) ⟨930272, by rfl⟩ : syracuseStep 1240363 = 1860545) B1860545
theorem B978233 : Blo 650305 978233 := bstep (se 2 (by rfl) ⟨366837, by rfl⟩ : syracuseStep 978233 = 733675) B733675
theorem B650555 : Blo 650305 650555 := bstep (se 1 (by rfl) ⟨487916, by rfl⟩ : syracuseStep 650555 = 975833) B975833
theorem B650631 : Blo 650305 650631 := bstep (se 1 (by rfl) ⟨487973, by rfl⟩ : syracuseStep 650631 = 975947) B975947
theorem B978311 : Blo 650305 978311 := bstep (se 1 (by rfl) ⟨733733, by rfl⟩ : syracuseStep 978311 = 1467467) B1467467
theorem B650639 : Blo 650305 650639 := bstep (se 1 (by rfl) ⟨487979, by rfl⟩ : syracuseStep 650639 = 975959) B975959
theorem B1469843 : Blo 650305 1469843 := bstep (se 1 (by rfl) ⟨1102382, by rfl⟩ : syracuseStep 1469843 = 2204765) B2204765
theorem B978347 : Blo 650305 978347 := bstep (se 1 (by rfl) ⟨733760, by rfl⟩ : syracuseStep 978347 = 1467521) B1467521
theorem B650683 : Blo 650305 650683 := bstep (se 1 (by rfl) ⟨488012, by rfl⟩ : syracuseStep 650683 = 976025) B976025
theorem B978377 : Blo 650305 978377 := bstep (se 2 (by rfl) ⟨366891, by rfl⟩ : syracuseStep 978377 = 733783) B733783
theorem B1469897 : Blo 650305 1469897 := bstep (se 2 (by rfl) ⟨551211, by rfl⟩ : syracuseStep 1469897 = 1102423) B1102423
theorem B650759 : Blo 650305 650759 := bstep (se 1 (by rfl) ⟨488069, by rfl⟩ : syracuseStep 650759 = 976139) B976139
theorem B650767 : Blo 650305 650767 := bstep (se 1 (by rfl) ⟨488075, by rfl⟩ : syracuseStep 650767 = 976151) B976151
theorem B1240591 : Blo 650305 1240591 := bstep (se 1 (by rfl) ⟨930443, by rfl⟩ : syracuseStep 1240591 = 1860887) B1860887
theorem B650811 : Blo 650305 650811 := bstep (se 1 (by rfl) ⟨488108, by rfl⟩ : syracuseStep 650811 = 976217) B976217
theorem B978491 : Blo 650305 978491 := bstep (se 1 (by rfl) ⟨733868, by rfl⟩ : syracuseStep 978491 = 1467737) B1467737
theorem B8351333 : Blo 650305 8351333 := bstep (se 4 (by rfl) ⟨782937, by rfl⟩ : syracuseStep 8351333 = 1565875) B1565875
theorem B978551 : Blo 650305 978551 := bstep (se 1 (by rfl) ⟨733913, by rfl⟩ : syracuseStep 978551 = 1467827) B1467827
theorem B650887 : Blo 650305 650887 := bstep (se 1 (by rfl) ⟨488165, by rfl⟩ : syracuseStep 650887 = 976331) B976331
theorem B650895 : Blo 650305 650895 := bstep (se 1 (by rfl) ⟨488171, by rfl⟩ : syracuseStep 650895 = 976343) B976343
theorem B978575 : Blo 650305 978575 := bstep (se 1 (by rfl) ⟨733931, by rfl⟩ : syracuseStep 978575 = 1467863) B1467863
theorem B978617 : Blo 650305 978617 := bstep (se 2 (by rfl) ⟨366981, by rfl⟩ : syracuseStep 978617 = 733963) B733963
theorem B650939 : Blo 650305 650939 := bstep (se 1 (by rfl) ⟨488204, by rfl⟩ : syracuseStep 650939 = 976409) B976409
theorem B6254273 : Blo 650305 6254273 := bstep (se 2 (by rfl) ⟨2345352, by rfl⟩ : syracuseStep 6254273 = 4690705) B4690705
theorem B3337985 : Blo 650305 3337985 := bstep (se 2 (by rfl) ⟨1251744, by rfl⟩ : syracuseStep 3337985 = 2503489) B2503489
theorem B651015 : Blo 650305 651015 := bstep (se 1 (by rfl) ⟨488261, by rfl⟩ : syracuseStep 651015 = 976523) B976523
theorem B978695 : Blo 650305 978695 := bstep (se 1 (by rfl) ⟨734021, by rfl⟩ : syracuseStep 978695 = 1468043) B1468043
theorem B651023 : Blo 650305 651023 := bstep (se 1 (by rfl) ⟨488267, by rfl⟩ : syracuseStep 651023 = 976535) B976535
theorem B1175329 : Blo 650305 1175329 := bstep (se 2 (by rfl) ⟨440748, by rfl⟩ : syracuseStep 1175329 = 881497) B881497
theorem B978731 : Blo 650305 978731 := bstep (se 1 (by rfl) ⟨734048, by rfl⟩ : syracuseStep 978731 = 1468097) B1468097
theorem B880427 : Blo 650305 880427 := bstep (se 1 (by rfl) ⟨660320, by rfl⟩ : syracuseStep 880427 = 1320641) B1320641
theorem B651067 : Blo 650305 651067 := bstep (se 1 (by rfl) ⟨488300, by rfl⟩ : syracuseStep 651067 = 976601) B976601
theorem B978761 : Blo 650305 978761 := bstep (se 2 (by rfl) ⟨367035, by rfl⟩ : syracuseStep 978761 = 734071) B734071
theorem B4452185 : Blo 650305 4452185 := bstep (se 2 (by rfl) ⟨1669569, by rfl⟩ : syracuseStep 4452185 = 3339139) B3339139
theorem B651143 : Blo 650305 651143 := bstep (se 1 (by rfl) ⟨488357, by rfl⟩ : syracuseStep 651143 = 976715) B976715
theorem B651151 : Blo 650305 651151 := bstep (se 1 (by rfl) ⟨488363, by rfl⟩ : syracuseStep 651151 = 976727) B976727
theorem B651195 : Blo 650305 651195 := bstep (se 1 (by rfl) ⟨488396, by rfl⟩ : syracuseStep 651195 = 976793) B976793
theorem B978875 : Blo 650305 978875 := bstep (se 1 (by rfl) ⟨734156, by rfl⟩ : syracuseStep 978875 = 1468313) B1468313
theorem B978935 : Blo 650305 978935 := bstep (se 1 (by rfl) ⟨734201, by rfl⟩ : syracuseStep 978935 = 1468403) B1468403
theorem B651271 : Blo 650305 651271 := bstep (se 1 (by rfl) ⟨488453, by rfl⟩ : syracuseStep 651271 = 976907) B976907
theorem B651279 : Blo 650305 651279 := bstep (se 1 (by rfl) ⟨488459, by rfl⟩ : syracuseStep 651279 = 976919) B976919
theorem B978959 : Blo 650305 978959 := bstep (se 1 (by rfl) ⟨734219, by rfl⟩ : syracuseStep 978959 = 1468439) B1468439
theorem B979001 : Blo 650305 979001 := bstep (se 2 (by rfl) ⟨367125, by rfl⟩ : syracuseStep 979001 = 734251) B734251
theorem B651323 : Blo 650305 651323 := bstep (se 1 (by rfl) ⟨488492, by rfl⟩ : syracuseStep 651323 = 976985) B976985
theorem B651399 : Blo 650305 651399 := bstep (se 1 (by rfl) ⟨488549, by rfl⟩ : syracuseStep 651399 = 977099) B977099
theorem B979079 : Blo 650305 979079 := bstep (se 1 (by rfl) ⟨734309, by rfl⟩ : syracuseStep 979079 = 1468619) B1468619
theorem B1470599 : Blo 650305 1470599 := bstep (se 1 (by rfl) ⟨1102949, by rfl⟩ : syracuseStep 1470599 = 2205899) B2205899
theorem B651407 : Blo 650305 651407 := bstep (se 1 (by rfl) ⟨488555, by rfl⟩ : syracuseStep 651407 = 977111) B977111
theorem B979115 : Blo 650305 979115 := bstep (se 1 (by rfl) ⟨734336, by rfl⟩ : syracuseStep 979115 = 1468673) B1468673
theorem B651451 : Blo 650305 651451 := bstep (se 1 (by rfl) ⟨488588, by rfl⟩ : syracuseStep 651451 = 977177) B977177
theorem B979145 : Blo 650305 979145 := bstep (se 2 (by rfl) ⟨367179, by rfl⟩ : syracuseStep 979145 = 734359) B734359
theorem B651527 : Blo 650305 651527 := bstep (se 1 (by rfl) ⟨488645, by rfl⟩ : syracuseStep 651527 = 977291) B977291
theorem B651535 : Blo 650305 651535 := bstep (se 1 (by rfl) ⟨488651, by rfl⟩ : syracuseStep 651535 = 977303) B977303
theorem B651579 : Blo 650305 651579 := bstep (se 1 (by rfl) ⟨488684, by rfl⟩ : syracuseStep 651579 = 977369) B977369
theorem B979259 : Blo 650305 979259 := bstep (se 1 (by rfl) ⟨734444, by rfl⟩ : syracuseStep 979259 = 1468889) B1468889
theorem B1470779 : Blo 650305 1470779 := bstep (se 1 (by rfl) ⟨1103084, by rfl⟩ : syracuseStep 1470779 = 2206169) B2206169
theorem B979319 : Blo 650305 979319 := bstep (se 1 (by rfl) ⟨734489, by rfl⟩ : syracuseStep 979319 = 1468979) B1468979
theorem B651655 : Blo 650305 651655 := bstep (se 1 (by rfl) ⟨488741, by rfl⟩ : syracuseStep 651655 = 977483) B977483
theorem B651663 : Blo 650305 651663 := bstep (se 1 (by rfl) ⟨488747, by rfl⟩ : syracuseStep 651663 = 977495) B977495
theorem B979343 : Blo 650305 979343 := bstep (se 1 (by rfl) ⟨734507, by rfl⟩ : syracuseStep 979343 = 1469015) B1469015
theorem B979385 : Blo 650305 979385 := bstep (se 2 (by rfl) ⟨367269, by rfl⟩ : syracuseStep 979385 = 734539) B734539
theorem B1470905 : Blo 650305 1470905 := bstep (se 2 (by rfl) ⟨551589, by rfl⟩ : syracuseStep 1470905 = 1103179) B1103179
theorem B651707 : Blo 650305 651707 := bstep (se 1 (by rfl) ⟨488780, by rfl⟩ : syracuseStep 651707 = 977561) B977561
theorem B651783 : Blo 650305 651783 := bstep (se 1 (by rfl) ⟨488837, by rfl⟩ : syracuseStep 651783 = 977675) B977675
theorem B979463 : Blo 650305 979463 := bstep (se 1 (by rfl) ⟨734597, by rfl⟩ : syracuseStep 979463 = 1469195) B1469195
theorem B651791 : Blo 650305 651791 := bstep (se 1 (by rfl) ⟨488843, by rfl⟩ : syracuseStep 651791 = 977687) B977687
theorem B63336977 : Blo 650305 63336977 := bstep (se 2 (by rfl) ⟨23751366, by rfl⟩ : syracuseStep 63336977 = 47502733) B47502733
theorem B979499 : Blo 650305 979499 := bstep (se 1 (by rfl) ⟨734624, by rfl⟩ : syracuseStep 979499 = 1469249) B1469249
theorem B651835 : Blo 650305 651835 := bstep (se 1 (by rfl) ⟨488876, by rfl⟩ : syracuseStep 651835 = 977753) B977753
theorem B979529 : Blo 650305 979529 := bstep (se 2 (by rfl) ⟨367323, by rfl⟩ : syracuseStep 979529 = 734647) B734647
theorem B651911 : Blo 650305 651911 := bstep (se 1 (by rfl) ⟨488933, by rfl⟩ : syracuseStep 651911 = 977867) B977867
theorem B651919 : Blo 650305 651919 := bstep (se 1 (by rfl) ⟨488939, by rfl⟩ : syracuseStep 651919 = 977879) B977879
theorem B651963 : Blo 650305 651963 := bstep (se 1 (by rfl) ⟨488972, by rfl⟩ : syracuseStep 651963 = 977945) B977945
theorem B979643 : Blo 650305 979643 := bstep (se 1 (by rfl) ⟨734732, by rfl⟩ : syracuseStep 979643 = 1469465) B1469465
theorem B979703 : Blo 650305 979703 := bstep (se 1 (by rfl) ⟨734777, by rfl⟩ : syracuseStep 979703 = 1469555) B1469555
theorem B652039 : Blo 650305 652039 := bstep (se 1 (by rfl) ⟨489029, by rfl⟩ : syracuseStep 652039 = 978059) B978059
theorem B652047 : Blo 650305 652047 := bstep (se 1 (by rfl) ⟨489035, by rfl⟩ : syracuseStep 652047 = 978071) B978071
theorem B979727 : Blo 650305 979727 := bstep (se 1 (by rfl) ⟨734795, by rfl⟩ : syracuseStep 979727 = 1469591) B1469591
theorem B1471247 : Blo 650305 1471247 := bstep (se 1 (by rfl) ⟨1103435, by rfl⟩ : syracuseStep 1471247 = 2206871) B2206871
theorem B2781985 : Blo 650305 2781985 := bstep (se 2 (by rfl) ⟨1043244, by rfl⟩ : syracuseStep 2781985 = 2086489) B2086489
theorem B1471265 : Blo 650305 1471265 := bstep (se 2 (by rfl) ⟨551724, by rfl⟩ : syracuseStep 1471265 = 1103449) B1103449
theorem B979769 : Blo 650305 979769 := bstep (se 2 (by rfl) ⟨367413, by rfl⟩ : syracuseStep 979769 = 734827) B734827
theorem B652091 : Blo 650305 652091 := bstep (se 1 (by rfl) ⟨489068, by rfl⟩ : syracuseStep 652091 = 978137) B978137
theorem B652167 : Blo 650305 652167 := bstep (se 1 (by rfl) ⟨489125, by rfl⟩ : syracuseStep 652167 = 978251) B978251
theorem B979847 : Blo 650305 979847 := bstep (se 1 (by rfl) ⟨734885, by rfl⟩ : syracuseStep 979847 = 1469771) B1469771
theorem B652175 : Blo 650305 652175 := bstep (se 1 (by rfl) ⟨489131, by rfl⟩ : syracuseStep 652175 = 978263) B978263
theorem B979883 : Blo 650305 979883 := bstep (se 1 (by rfl) ⟨734912, by rfl⟩ : syracuseStep 979883 = 1469825) B1469825
theorem B652219 : Blo 650305 652219 := bstep (se 1 (by rfl) ⟨489164, by rfl⟩ : syracuseStep 652219 = 978329) B978329
theorem B979913 : Blo 650305 979913 := bstep (se 2 (by rfl) ⟨367467, by rfl⟩ : syracuseStep 979913 = 734935) B734935
theorem B652295 : Blo 650305 652295 := bstep (se 1 (by rfl) ⟨489221, by rfl⟩ : syracuseStep 652295 = 978443) B978443
theorem B652303 : Blo 650305 652303 := bstep (se 1 (by rfl) ⟨489227, by rfl⟩ : syracuseStep 652303 = 978455) B978455
theorem B1242155 : Blo 650305 1242155 := bstep (se 1 (by rfl) ⟨931616, by rfl⟩ : syracuseStep 1242155 = 1863233) B1863233
theorem B652347 : Blo 650305 652347 := bstep (se 1 (by rfl) ⟨489260, by rfl⟩ : syracuseStep 652347 = 978521) B978521
theorem B980027 : Blo 650305 980027 := bstep (se 1 (by rfl) ⟨735020, by rfl⟩ : syracuseStep 980027 = 1470041) B1470041
theorem B2683991 : Blo 650305 2683991 := bstep (se 1 (by rfl) ⟨2012993, by rfl⟩ : syracuseStep 2683991 = 4025987) B4025987
theorem B980087 : Blo 650305 980087 := bstep (se 1 (by rfl) ⟨735065, by rfl⟩ : syracuseStep 980087 = 1470131) B1470131
theorem B1471607 : Blo 650305 1471607 := bstep (se 1 (by rfl) ⟨1103705, by rfl⟩ : syracuseStep 1471607 = 2207411) B2207411
theorem B652423 : Blo 650305 652423 := bstep (se 1 (by rfl) ⟨489317, by rfl⟩ : syracuseStep 652423 = 978635) B978635
theorem B652431 : Blo 650305 652431 := bstep (se 1 (by rfl) ⟨489323, by rfl⟩ : syracuseStep 652431 = 978647) B978647
theorem B980111 : Blo 650305 980111 := bstep (se 1 (by rfl) ⟨735083, by rfl⟩ : syracuseStep 980111 = 1470167) B1470167
theorem B980153 : Blo 650305 980153 := bstep (se 2 (by rfl) ⟨367557, by rfl⟩ : syracuseStep 980153 = 735115) B735115
theorem B652475 : Blo 650305 652475 := bstep (se 1 (by rfl) ⟨489356, by rfl⟩ : syracuseStep 652475 = 978713) B978713
theorem B1045705 : Blo 650305 1045705 := bstep (se 2 (by rfl) ⟨392139, by rfl⟩ : syracuseStep 1045705 = 784279) B784279
theorem B2094281 : Blo 650305 2094281 := bstep (se 2 (by rfl) ⟨785355, by rfl⟩ : syracuseStep 2094281 = 1570711) B1570711
theorem B1701065 : Blo 650305 1701065 := bstep (se 2 (by rfl) ⟨637899, by rfl⟩ : syracuseStep 1701065 = 1275799) B1275799
theorem B652551 : Blo 650305 652551 := bstep (se 1 (by rfl) ⟨489413, by rfl⟩ : syracuseStep 652551 = 978827) B978827
theorem B980231 : Blo 650305 980231 := bstep (se 1 (by rfl) ⟨735173, by rfl⟩ : syracuseStep 980231 = 1470347) B1470347
theorem B652559 : Blo 650305 652559 := bstep (se 1 (by rfl) ⟨489419, by rfl⟩ : syracuseStep 652559 = 978839) B978839
theorem B980267 : Blo 650305 980267 := bstep (se 1 (by rfl) ⟨735200, by rfl⟩ : syracuseStep 980267 = 1470401) B1470401
theorem B1471787 : Blo 650305 1471787 := bstep (se 1 (by rfl) ⟨1103840, by rfl⟩ : syracuseStep 1471787 = 2207681) B2207681
theorem B652603 : Blo 650305 652603 := bstep (se 1 (by rfl) ⟨489452, by rfl⟩ : syracuseStep 652603 = 978905) B978905
theorem B980297 : Blo 650305 980297 := bstep (se 2 (by rfl) ⟨367611, by rfl⟩ : syracuseStep 980297 = 735223) B735223
theorem B652679 : Blo 650305 652679 := bstep (se 1 (by rfl) ⟨489509, by rfl⟩ : syracuseStep 652679 = 979019) B979019
theorem B652687 : Blo 650305 652687 := bstep (se 1 (by rfl) ⟨489515, by rfl⟩ : syracuseStep 652687 = 979031) B979031
theorem B3306905 : Blo 650305 3306905 := bstep (se 2 (by rfl) ⟨1240089, by rfl⟩ : syracuseStep 3306905 = 2480179) B2480179
theorem B652731 : Blo 650305 652731 := bstep (se 1 (by rfl) ⟨489548, by rfl⟩ : syracuseStep 652731 = 979097) B979097
theorem B980411 : Blo 650305 980411 := bstep (se 1 (by rfl) ⟨735308, by rfl⟩ : syracuseStep 980411 = 1470617) B1470617
theorem B980471 : Blo 650305 980471 := bstep (se 1 (by rfl) ⟨735353, by rfl⟩ : syracuseStep 980471 = 1470707) B1470707
theorem B652807 : Blo 650305 652807 := bstep (se 1 (by rfl) ⟨489605, by rfl⟩ : syracuseStep 652807 = 979211) B979211
theorem B652815 : Blo 650305 652815 := bstep (se 1 (by rfl) ⟨489611, by rfl⟩ : syracuseStep 652815 = 979223) B979223
theorem B980495 : Blo 650305 980495 := bstep (se 1 (by rfl) ⟨735371, by rfl⟩ : syracuseStep 980495 = 1470743) B1470743
theorem B980537 : Blo 650305 980537 := bstep (se 2 (by rfl) ⟨367701, by rfl⟩ : syracuseStep 980537 = 735403) B735403
theorem B652859 : Blo 650305 652859 := bstep (se 1 (by rfl) ⟨489644, by rfl⟩ : syracuseStep 652859 = 979289) B979289
theorem B652935 : Blo 650305 652935 := bstep (se 1 (by rfl) ⟨489701, by rfl⟩ : syracuseStep 652935 = 979403) B979403
theorem B980615 : Blo 650305 980615 := bstep (se 1 (by rfl) ⟨735461, by rfl⟩ : syracuseStep 980615 = 1470923) B1470923
theorem B652943 : Blo 650305 652943 := bstep (se 1 (by rfl) ⟨489707, by rfl⟩ : syracuseStep 652943 = 979415) B979415
theorem B1472147 : Blo 650305 1472147 := bstep (se 1 (by rfl) ⟨1104110, by rfl⟩ : syracuseStep 1472147 = 2208221) B2208221
theorem B980651 : Blo 650305 980651 := bstep (se 1 (by rfl) ⟨735488, by rfl⟩ : syracuseStep 980651 = 1470977) B1470977
theorem B652987 : Blo 650305 652987 := bstep (se 1 (by rfl) ⟨489740, by rfl⟩ : syracuseStep 652987 = 979481) B979481
theorem B980681 : Blo 650305 980681 := bstep (se 2 (by rfl) ⟨367755, by rfl⟩ : syracuseStep 980681 = 735511) B735511
theorem B3536585 : Blo 650305 3536585 := bstep (se 2 (by rfl) ⟨1326219, by rfl⟩ : syracuseStep 3536585 = 2652439) B2652439
theorem B653063 : Blo 650305 653063 := bstep (se 1 (by rfl) ⟨489797, by rfl⟩ : syracuseStep 653063 = 979595) B979595
theorem B653071 : Blo 650305 653071 := bstep (se 1 (by rfl) ⟨489803, by rfl⟩ : syracuseStep 653071 = 979607) B979607
theorem B653115 : Blo 650305 653115 := bstep (se 1 (by rfl) ⟨489836, by rfl⟩ : syracuseStep 653115 = 979673) B979673
theorem B980795 : Blo 650305 980795 := bstep (se 1 (by rfl) ⟨735596, by rfl⟩ : syracuseStep 980795 = 1471193) B1471193
theorem B980855 : Blo 650305 980855 := bstep (se 1 (by rfl) ⟨735641, by rfl⟩ : syracuseStep 980855 = 1471283) B1471283
theorem B653191 : Blo 650305 653191 := bstep (se 1 (by rfl) ⟨489893, by rfl⟩ : syracuseStep 653191 = 979787) B979787
theorem B653199 : Blo 650305 653199 := bstep (se 1 (by rfl) ⟨489899, by rfl⟩ : syracuseStep 653199 = 979799) B979799
theorem B980879 : Blo 650305 980879 := bstep (se 1 (by rfl) ⟨735659, by rfl⟩ : syracuseStep 980879 = 1471319) B1471319
theorem B980921 : Blo 650305 980921 := bstep (se 2 (by rfl) ⟨367845, by rfl⟩ : syracuseStep 980921 = 735691) B735691
theorem B653243 : Blo 650305 653243 := bstep (se 1 (by rfl) ⟨489932, by rfl⟩ : syracuseStep 653243 = 979865) B979865
theorem B4028363 : Blo 650305 4028363 := bstep (se 1 (by rfl) ⟨3021272, by rfl⟩ : syracuseStep 4028363 = 6042545) B6042545
theorem B653319 : Blo 650305 653319 := bstep (se 1 (by rfl) ⟨489989, by rfl⟩ : syracuseStep 653319 = 979979) B979979
theorem B980999 : Blo 650305 980999 := bstep (se 1 (by rfl) ⟨735749, by rfl⟩ : syracuseStep 980999 = 1471499) B1471499
theorem B653327 : Blo 650305 653327 := bstep (se 1 (by rfl) ⟨489995, by rfl⟩ : syracuseStep 653327 = 979991) B979991
theorem B981035 : Blo 650305 981035 := bstep (se 1 (by rfl) ⟨735776, by rfl⟩ : syracuseStep 981035 = 1471553) B1471553
theorem B653371 : Blo 650305 653371 := bstep (se 1 (by rfl) ⟨490028, by rfl⟩ : syracuseStep 653371 = 980057) B980057
theorem B981065 : Blo 650305 981065 := bstep (se 2 (by rfl) ⟨367899, by rfl⟩ : syracuseStep 981065 = 735799) B735799
theorem B653447 : Blo 650305 653447 := bstep (se 1 (by rfl) ⟨490085, by rfl⟩ : syracuseStep 653447 = 980171) B980171
theorem B653455 : Blo 650305 653455 := bstep (se 1 (by rfl) ⟨490091, by rfl⟩ : syracuseStep 653455 = 980183) B980183
theorem B653499 : Blo 650305 653499 := bstep (se 1 (by rfl) ⟨490124, by rfl⟩ : syracuseStep 653499 = 980249) B980249
theorem B981179 : Blo 650305 981179 := bstep (se 1 (by rfl) ⟨735884, by rfl⟩ : syracuseStep 981179 = 1471769) B1471769
theorem B981239 : Blo 650305 981239 := bstep (se 1 (by rfl) ⟨735929, by rfl⟩ : syracuseStep 981239 = 1471859) B1471859
theorem B653575 : Blo 650305 653575 := bstep (se 1 (by rfl) ⟨490181, by rfl⟩ : syracuseStep 653575 = 980363) B980363
theorem B653583 : Blo 650305 653583 := bstep (se 1 (by rfl) ⟨490187, by rfl⟩ : syracuseStep 653583 = 980375) B980375
theorem B981263 : Blo 650305 981263 := bstep (se 1 (by rfl) ⟨735947, by rfl⟩ : syracuseStep 981263 = 1471895) B1471895
theorem B981305 : Blo 650305 981305 := bstep (se 2 (by rfl) ⟨367989, by rfl⟩ : syracuseStep 981305 = 735979) B735979
theorem B653627 : Blo 650305 653627 := bstep (se 1 (by rfl) ⟨490220, by rfl⟩ : syracuseStep 653627 = 980441) B980441
theorem B653703 : Blo 650305 653703 := bstep (se 1 (by rfl) ⟨490277, by rfl⟩ : syracuseStep 653703 = 980555) B980555
theorem B981383 : Blo 650305 981383 := bstep (se 1 (by rfl) ⟨736037, by rfl⟩ : syracuseStep 981383 = 1472075) B1472075
theorem B784783 : Blo 650305 784783 := bstep (se 1 (by rfl) ⟨588587, by rfl⟩ : syracuseStep 784783 = 1177175) B1177175
theorem B653711 : Blo 650305 653711 := bstep (se 1 (by rfl) ⟨490283, by rfl⟩ : syracuseStep 653711 = 980567) B980567
theorem B2783641 : Blo 650305 2783641 := bstep (se 2 (by rfl) ⟨1043865, by rfl⟩ : syracuseStep 2783641 = 2087731) B2087731
theorem B981419 : Blo 650305 981419 := bstep (se 1 (by rfl) ⟨736064, by rfl⟩ : syracuseStep 981419 = 1472129) B1472129
theorem B1571257 : Blo 650305 1571257 := bstep (se 2 (by rfl) ⟨589221, by rfl⟩ : syracuseStep 1571257 = 1178443) B1178443
theorem B653755 : Blo 650305 653755 := bstep (se 1 (by rfl) ⟨490316, by rfl⟩ : syracuseStep 653755 = 980633) B980633
theorem B981449 : Blo 650305 981449 := bstep (se 2 (by rfl) ⟨368043, by rfl⟩ : syracuseStep 981449 = 736087) B736087
theorem B653831 : Blo 650305 653831 := bstep (se 1 (by rfl) ⟨490373, by rfl⟩ : syracuseStep 653831 = 980747) B980747
theorem B653839 : Blo 650305 653839 := bstep (se 1 (by rfl) ⟨490379, by rfl⟩ : syracuseStep 653839 = 980759) B980759
theorem B1178155 : Blo 650305 1178155 := bstep (se 1 (by rfl) ⟨883616, by rfl⟩ : syracuseStep 1178155 = 1767233) B1767233
theorem B653883 : Blo 650305 653883 := bstep (se 1 (by rfl) ⟨490412, by rfl⟩ : syracuseStep 653883 = 980825) B980825
theorem B653959 : Blo 650305 653959 := bstep (se 1 (by rfl) ⟨490469, by rfl⟩ : syracuseStep 653959 = 980939) B980939
theorem B653967 : Blo 650305 653967 := bstep (se 1 (by rfl) ⟨490475, by rfl⟩ : syracuseStep 653967 = 980951) B980951
theorem B654011 : Blo 650305 654011 := bstep (se 1 (by rfl) ⟨490508, by rfl⟩ : syracuseStep 654011 = 981017) B981017
theorem B13368025 : Blo 650305 13368025 := bstep (se 2 (by rfl) ⟨5013009, by rfl⟩ : syracuseStep 13368025 = 10026019) B10026019
theorem B654087 : Blo 650305 654087 := bstep (se 1 (by rfl) ⟨490565, by rfl⟩ : syracuseStep 654087 = 981131) B981131
theorem B654095 : Blo 650305 654095 := bstep (se 1 (by rfl) ⟨490571, by rfl⟩ : syracuseStep 654095 = 981143) B981143
theorem B1178401 : Blo 650305 1178401 := bstep (se 2 (by rfl) ⟨441900, by rfl⟩ : syracuseStep 1178401 = 883801) B883801
theorem B654139 : Blo 650305 654139 := bstep (se 1 (by rfl) ⟨490604, by rfl⟩ : syracuseStep 654139 = 981209) B981209
theorem B1571719 : Blo 650305 1571719 := bstep (se 1 (by rfl) ⟨1178789, by rfl⟩ : syracuseStep 1571719 = 2357579) B2357579
theorem B654215 : Blo 650305 654215 := bstep (se 1 (by rfl) ⟨490661, by rfl⟩ : syracuseStep 654215 = 981323) B981323
theorem B654223 : Blo 650305 654223 := bstep (se 1 (by rfl) ⟨490667, by rfl⟩ : syracuseStep 654223 = 981335) B981335
theorem B687035 : Blo 650305 687035 := bstep (se 1 (by rfl) ⟨515276, by rfl⟩ : syracuseStep 687035 = 1030553) B1030553
theorem B654267 : Blo 650305 654267 := bstep (se 1 (by rfl) ⟨490700, by rfl⟩ : syracuseStep 654267 = 981401) B981401
theorem B3964211 : Blo 650305 3964211 := bstep (se 1 (by rfl) ⟨2973158, by rfl⟩ : syracuseStep 3964211 = 5946317) B5946317
theorem B6028919 : Blo 650305 6028919 := bstep (se 1 (by rfl) ⟨4521689, by rfl⟩ : syracuseStep 6028919 = 9043379) B9043379
theorem B2195315 : Blo 650305 2195315 := bstep (se 1 (by rfl) ⟨1646486, by rfl⟩ : syracuseStep 2195315 = 3292973) B3292973
theorem B3178385 : Blo 650305 3178385 := bstep (se 2 (by rfl) ⟨1191894, by rfl⟩ : syracuseStep 3178385 = 2383789) B2383789
theorem B3309497 : Blo 650305 3309497 := bstep (se 2 (by rfl) ⟨1241061, by rfl⟩ : syracuseStep 3309497 = 2482123) B2482123
theorem B7929971 : Blo 650305 7929971 := bstep (se 1 (by rfl) ⟨5947478, by rfl⟩ : syracuseStep 7929971 = 11894957) B11894957
theorem B12550373 : Blo 650305 12550373 := bstep (se 4 (by rfl) ⟨1176597, by rfl⟩ : syracuseStep 12550373 = 2353195) B2353195
theorem B2195855 : Blo 650305 2195855 := bstep (se 1 (by rfl) ⟨1646891, by rfl⟩ : syracuseStep 2195855 = 3293783) B3293783
theorem B2196179 : Blo 650305 2196179 := bstep (se 1 (by rfl) ⟨1647134, by rfl⟩ : syracuseStep 2196179 = 3294269) B3294269
theorem B6980825 : Blo 650305 6980825 := bstep (se 2 (by rfl) ⟨2617809, by rfl⟩ : syracuseStep 6980825 = 5235619) B5235619
theorem B11175569 : Blo 650305 11175569 := bstep (se 2 (by rfl) ⟨4190838, by rfl⟩ : syracuseStep 11175569 = 8381677) B8381677
theorem B4753043 : Blo 650305 4753043 := bstep (se 1 (by rfl) ⟨3564782, by rfl⟩ : syracuseStep 4753043 = 7129565) B7129565
theorem B1672915 : Blo 650305 1672915 := bstep (se 1 (by rfl) ⟨1254686, by rfl⟩ : syracuseStep 1672915 = 2509373) B2509373
theorem B2197367 : Blo 650305 2197367 := bstep (se 1 (by rfl) ⟨1648025, by rfl⟩ : syracuseStep 2197367 = 3296051) B3296051
theorem B3180559 : Blo 650305 3180559 := bstep (se 1 (by rfl) ⟨2385419, by rfl⟩ : syracuseStep 3180559 = 4770839) B4770839
theorem B2197583 : Blo 650305 2197583 := bstep (se 1 (by rfl) ⟨1648187, by rfl⟩ : syracuseStep 2197583 = 3296375) B3296375
theorem B4524113 : Blo 650305 4524113 := bstep (se 2 (by rfl) ⟨1696542, by rfl⟩ : syracuseStep 4524113 = 3393085) B3393085
theorem B5966129 : Blo 650305 5966129 := bstep (se 2 (by rfl) ⟨2237298, by rfl⟩ : syracuseStep 5966129 = 4474597) B4474597
theorem B5933465 : Blo 650305 5933465 := bstep (se 2 (by rfl) ⟨2225049, by rfl⟩ : syracuseStep 5933465 = 4450099) B4450099
theorem B2197961 : Blo 650305 2197961 := bstep (se 2 (by rfl) ⟨824235, by rfl⟩ : syracuseStep 2197961 = 1648471) B1648471
theorem B2198231 : Blo 650305 2198231 := bstep (se 1 (by rfl) ⟨1648673, by rfl⟩ : syracuseStep 2198231 = 3297347) B3297347
theorem B3312413 : Blo 650305 3312413 := bstep (se 3 (by rfl) ⟨621077, by rfl⟩ : syracuseStep 3312413 = 1242155) B1242155
theorem B2198447 : Blo 650305 2198447 := bstep (se 1 (by rfl) ⟨1648835, by rfl⟩ : syracuseStep 2198447 = 3297671) B3297671
theorem B1674247 : Blo 650305 1674247 := bstep (se 1 (by rfl) ⟨1255685, by rfl⟩ : syracuseStep 1674247 = 2511371) B2511371
theorem B4885697 : Blo 650305 4885697 := bstep (se 2 (by rfl) ⟨1832136, by rfl⟩ : syracuseStep 4885697 = 3664273) B3664273
theorem B823223 : Blo 650305 823223 := bstep (se 1 (by rfl) ⟨617417, by rfl⟩ : syracuseStep 823223 = 1234835) B1234835
theorem B823375 : Blo 650305 823375 := bstep (se 1 (by rfl) ⟨617531, by rfl⟩ : syracuseStep 823375 = 1235063) B1235063
theorem B3707147 : Blo 650305 3707147 := bstep (se 1 (by rfl) ⟨2780360, by rfl⟩ : syracuseStep 3707147 = 5560721) B5560721
theorem B4526765 : Blo 650305 4526765 := bstep (se 3 (by rfl) ⟨848768, by rfl⟩ : syracuseStep 4526765 = 1697537) B1697537
theorem B3707603 : Blo 650305 3707603 := bstep (se 1 (by rfl) ⟨2780702, by rfl⟩ : syracuseStep 3707603 = 5561405) B5561405
theorem B824519 : Blo 650305 824519 := bstep (se 1 (by rfl) ⟨618389, by rfl⟩ : syracuseStep 824519 = 1236779) B1236779
theorem B4166903 : Blo 650305 4166903 := bstep (se 1 (by rfl) ⟨3125177, by rfl⟩ : syracuseStep 4166903 = 6250355) B6250355
theorem B2200823 : Blo 650305 2200823 := bstep (se 1 (by rfl) ⟨1650617, by rfl⟩ : syracuseStep 2200823 = 3301235) B3301235
theorem B824671 : Blo 650305 824671 := bstep (se 1 (by rfl) ⟨618503, by rfl⟩ : syracuseStep 824671 = 1237007) B1237007
theorem B4167055 : Blo 650305 4167055 := bstep (se 1 (by rfl) ⟨3125291, by rfl⟩ : syracuseStep 4167055 = 6250583) B6250583
theorem B2201147 : Blo 650305 2201147 := bstep (se 1 (by rfl) ⟨1650860, by rfl⟩ : syracuseStep 2201147 = 3301721) B3301721
theorem B4462141 : Blo 650305 4462141 := bstep (se 3 (by rfl) ⟨836651, by rfl⟩ : syracuseStep 4462141 = 1673303) B1673303
theorem B3708605 : Blo 650305 3708605 := bstep (se 3 (by rfl) ⟨695363, by rfl⟩ : syracuseStep 3708605 = 1390727) B1390727
theorem B2201417 : Blo 650305 2201417 := bstep (se 2 (by rfl) ⟨825531, by rfl⟩ : syracuseStep 2201417 = 1651063) B1651063
theorem B2791691 : Blo 650305 2791691 := bstep (se 1 (by rfl) ⟨2093768, by rfl⟩ : syracuseStep 2791691 = 4187537) B4187537
theorem B3709313 : Blo 650305 3709313 := bstep (se 2 (by rfl) ⟨1390992, by rfl⟩ : syracuseStep 3709313 = 2781985) B2781985
theorem B3775187 : Blo 650305 3775187 := bstep (se 1 (by rfl) ⟨2831390, by rfl⟩ : syracuseStep 3775187 = 5662781) B5662781
theorem B2202551 : Blo 650305 2202551 := bstep (se 1 (by rfl) ⟨1651913, by rfl⟩ : syracuseStep 2202551 = 3303827) B3303827
theorem B4955255 : Blo 650305 4955255 := bstep (se 1 (by rfl) ⟨3716441, by rfl⟩ : syracuseStep 4955255 = 7432883) B7432883
theorem B5283245 : Blo 650305 5283245 := bstep (se 3 (by rfl) ⟨990608, by rfl⟩ : syracuseStep 5283245 = 1981217) B1981217
theorem B826843 : Blo 650305 826843 := bstep (se 1 (by rfl) ⟨620132, by rfl⟩ : syracuseStep 826843 = 1240265) B1240265
theorem B2203145 : Blo 650305 2203145 := bstep (se 2 (by rfl) ⟨826179, by rfl⟩ : syracuseStep 2203145 = 1652359) B1652359
theorem B1252961 : Blo 650305 1252961 := bstep (se 2 (by rfl) ⟨469860, by rfl⟩ : syracuseStep 1252961 = 939721) B939721
theorem B1646203 : Blo 650305 1646203 := bstep (se 1 (by rfl) ⟨1234652, by rfl⟩ : syracuseStep 1646203 = 2469305) B2469305
theorem B2204009 : Blo 650305 2204009 := bstep (se 2 (by rfl) ⟨826503, by rfl⟩ : syracuseStep 2204009 = 1653007) B1653007
theorem B3711521 : Blo 650305 3711521 := bstep (se 2 (by rfl) ⟨1391820, by rfl⟩ : syracuseStep 3711521 = 2783641) B2783641
theorem B2204603 : Blo 650305 2204603 := bstep (se 1 (by rfl) ⟨1653452, by rfl⟩ : syracuseStep 2204603 = 3306905) B3306905
theorem B926969 : Blo 650305 926969 := bstep (se 2 (by rfl) ⟨347613, by rfl⟩ : syracuseStep 926969 = 695227) B695227
theorem B927083 : Blo 650305 927083 := bstep (se 1 (by rfl) ⟨695312, by rfl⟩ : syracuseStep 927083 = 1390625) B1390625
theorem B35661221 : Blo 650305 35661221 := bstep (se 4 (by rfl) ⟨3343239, by rfl⟩ : syracuseStep 35661221 = 6686479) B6686479
theorem B6268421 : Blo 650305 6268421 := bstep (se 4 (by rfl) ⟨587664, by rfl⟩ : syracuseStep 6268421 = 1175329) B1175329
theorem B1320527 : Blo 650305 1320527 := bstep (se 1 (by rfl) ⟨990395, by rfl⟩ : syracuseStep 1320527 = 1980791) B1980791
theorem B117253973 : Blo 650305 117253973 := bstep (se 9 (by rfl) ⟨343517, by rfl⟩ : syracuseStep 117253973 = 687035) B687035
theorem B993479 : Blo 650305 993479 := bstep (se 1 (by rfl) ⟨745109, by rfl⟩ : syracuseStep 993479 = 1490219) B1490219
theorem B11872493 : Blo 650305 11872493 := bstep (se 3 (by rfl) ⟨2226092, by rfl⟩ : syracuseStep 11872493 = 4452185) B4452185
theorem B2206331 : Blo 650305 2206331 := bstep (se 1 (by rfl) ⟨1654748, by rfl⟩ : syracuseStep 2206331 = 3309497) B3309497
theorem B7514909 : Blo 650305 7514909 := bstep (se 3 (by rfl) ⟨1409045, by rfl⟩ : syracuseStep 7514909 = 2818091) B2818091
theorem B2206493 : Blo 650305 2206493 := bstep (se 3 (by rfl) ⟨413717, by rfl⟩ : syracuseStep 2206493 = 827435) B827435
theorem B4074515 : Blo 650305 4074515 := bstep (se 1 (by rfl) ⟨3055886, by rfl⟩ : syracuseStep 4074515 = 6111773) B6111773
theorem B732199 : Blo 650305 732199 := bstep (se 1 (by rfl) ⟨549149, by rfl⟩ : syracuseStep 732199 = 1098299) B1098299
theorem B2207195 : Blo 650305 2207195 := bstep (se 1 (by rfl) ⟨1655396, by rfl⟩ : syracuseStep 2207195 = 3310793) B3310793
theorem B2469473 : Blo 650305 2469473 := bstep (se 2 (by rfl) ⟨926052, by rfl⟩ : syracuseStep 2469473 = 1852105) B1852105
theorem B1486433 : Blo 650305 1486433 := bstep (se 2 (by rfl) ⟨557412, by rfl⟩ : syracuseStep 1486433 = 1114825) B1114825
theorem B1650527 : Blo 650305 1650527 := bstep (se 1 (by rfl) ⟨1237895, by rfl⟩ : syracuseStep 1650527 = 2475791) B2475791
theorem B4239397 : Blo 650305 4239397 := bstep (se 4 (by rfl) ⟨397443, by rfl⟩ : syracuseStep 4239397 = 794887) B794887
theorem B2207897 : Blo 650305 2207897 := bstep (se 2 (by rfl) ⟨827961, by rfl⟩ : syracuseStep 2207897 = 1655923) B1655923
theorem B3355145 : Blo 650305 3355145 := bstep (se 2 (by rfl) ⟨1258179, by rfl⟩ : syracuseStep 3355145 = 2516359) B2516359
theorem B1651225 : Blo 650305 1651225 := bstep (se 2 (by rfl) ⟨619209, by rfl⟩ : syracuseStep 1651225 = 1238419) B1238419
theorem B2470459 : Blo 650305 2470459 := bstep (se 1 (by rfl) ⟨1852844, by rfl⟩ : syracuseStep 2470459 = 3705689) B3705689
theorem B733819 : Blo 650305 733819 := bstep (se 1 (by rfl) ⟨550364, by rfl⟩ : syracuseStep 733819 = 1100729) B1100729
theorem B1651529 : Blo 650305 1651529 := bstep (se 2 (by rfl) ⟨619323, by rfl⟩ : syracuseStep 1651529 = 1238647) B1238647
theorem B2470763 : Blo 650305 2470763 := bstep (se 1 (by rfl) ⟨1853072, by rfl⟩ : syracuseStep 2470763 = 3706145) B3706145
theorem B2470931 : Blo 650305 2470931 := bstep (se 1 (by rfl) ⟨1853198, by rfl⟩ : syracuseStep 2470931 = 3706397) B3706397
theorem B734287 : Blo 650305 734287 := bstep (se 1 (by rfl) ⟨550715, by rfl⟩ : syracuseStep 734287 = 1101431) B1101431
theorem B6337739 : Blo 650305 6337739 := bstep (se 1 (by rfl) ⟨4753304, by rfl⟩ : syracuseStep 6337739 = 9506609) B9506609
theorem B4961573 : Blo 650305 4961573 := bstep (se 4 (by rfl) ⟨465147, by rfl⟩ : syracuseStep 4961573 = 930295) B930295
theorem B734683 : Blo 650305 734683 := bstep (se 1 (by rfl) ⟨551012, by rfl⟩ : syracuseStep 734683 = 1102025) B1102025
theorem B21116477 : Blo 650305 21116477 := bstep (se 3 (by rfl) ⟨3959339, by rfl⟩ : syracuseStep 21116477 = 7918679) B7918679
theorem B5289761 : Blo 650305 5289761 := bstep (se 2 (by rfl) ⟨1983660, by rfl⟩ : syracuseStep 5289761 = 3967321) B3967321
theorem B1324907 : Blo 650305 1324907 := bstep (se 1 (by rfl) ⟨993680, by rfl⟩ : syracuseStep 1324907 = 1987361) B1987361
theorem B735151 : Blo 650305 735151 := bstep (se 1 (by rfl) ⟨551363, by rfl⟩ : syracuseStep 735151 = 1102727) B1102727
theorem B1652663 : Blo 650305 1652663 := bstep (se 1 (by rfl) ⟨1239497, by rfl⟩ : syracuseStep 1652663 = 2478995) B2478995
theorem B735583 : Blo 650305 735583 := bstep (se 1 (by rfl) ⟨551687, by rfl⟩ : syracuseStep 735583 = 1103375) B1103375
theorem B735943 : Blo 650305 735943 := bstep (se 1 (by rfl) ⟨551957, by rfl⟩ : syracuseStep 735943 = 1103915) B1103915
theorem B4012753 : Blo 650305 4012753 := bstep (se 2 (by rfl) ⟨1504782, by rfl⟩ : syracuseStep 4012753 = 3009565) B3009565
theorem B2505431 : Blo 650305 2505431 := bstep (se 1 (by rfl) ⟨1879073, by rfl⟩ : syracuseStep 2505431 = 3758147) B3758147
theorem B1653767 : Blo 650305 1653767 := bstep (se 1 (by rfl) ⟨1240325, by rfl⟩ : syracuseStep 1653767 = 2480651) B2480651
theorem B1653817 : Blo 650305 1653817 := bstep (se 2 (by rfl) ⟨620181, by rfl⟩ : syracuseStep 1653817 = 1240363) B1240363
theorem B7421219 : Blo 650305 7421219 := bstep (se 1 (by rfl) ⟨5565914, by rfl⟩ : syracuseStep 7421219 = 11131829) B11131829
theorem B1654121 : Blo 650305 1654121 := bstep (se 2 (by rfl) ⟨620295, by rfl⟩ : syracuseStep 1654121 = 1240591) B1240591
theorem B1883657 : Blo 650305 1883657 := bstep (se 2 (by rfl) ⟨706371, by rfl⟩ : syracuseStep 1883657 = 1412743) B1412743
theorem B3292811 : Blo 650305 3292811 := bstep (se 1 (by rfl) ⟨2469608, by rfl⟩ : syracuseStep 3292811 = 4939217) B4939217
theorem B2473847 : Blo 650305 2473847 := bstep (se 1 (by rfl) ⟨1855385, by rfl⟩ : syracuseStep 2473847 = 3710771) B3710771
theorem B1982395 : Blo 650305 1982395 := bstep (se 1 (by rfl) ⟨1486796, by rfl⟩ : syracuseStep 1982395 = 2973593) B2973593
theorem B1097975 : Blo 650305 1097975 := bstep (se 1 (by rfl) ⟨823481, by rfl⟩ : syracuseStep 1097975 = 1646963) B1646963
theorem B1098319 : Blo 650305 1098319 := bstep (se 1 (by rfl) ⟨823739, by rfl⟩ : syracuseStep 1098319 = 1647479) B1647479
theorem B4702931 : Blo 650305 4702931 := bstep (se 1 (by rfl) ⟨3527198, by rfl⟩ : syracuseStep 4702931 = 7054397) B7054397
theorem B2474819 : Blo 650305 2474819 := bstep (se 1 (by rfl) ⟨1856114, by rfl⟩ : syracuseStep 2474819 = 3712229) B3712229
theorem B1098569 : Blo 650305 1098569 := bstep (se 2 (by rfl) ⟨411963, by rfl⟩ : syracuseStep 1098569 = 823927) B823927
theorem B1852321 : Blo 650305 1852321 := bstep (se 2 (by rfl) ⟨694620, by rfl⟩ : syracuseStep 1852321 = 1389241) B1389241
theorem B2507681 : Blo 650305 2507681 := bstep (se 2 (by rfl) ⟨940380, by rfl⟩ : syracuseStep 2507681 = 1880761) B1880761
theorem B1099001 : Blo 650305 1099001 := bstep (se 2 (by rfl) ⟨412125, by rfl⟩ : syracuseStep 1099001 = 824251) B824251
theorem B1099183 : Blo 650305 1099183 := bstep (se 1 (by rfl) ⟨824387, by rfl⟩ : syracuseStep 1099183 = 1648775) B1648775
theorem B1099271 : Blo 650305 1099271 := bstep (se 1 (by rfl) ⟨824453, by rfl⟩ : syracuseStep 1099271 = 1648907) B1648907
theorem B12699179 : Blo 650305 12699179 := bstep (se 1 (by rfl) ⟨9524384, by rfl⟩ : syracuseStep 12699179 = 19048769) B19048769
theorem B1394273 : Blo 650305 1394273 := bstep (se 2 (by rfl) ⟨522852, by rfl⟩ : syracuseStep 1394273 = 1045705) B1045705
theorem B5031557 : Blo 650305 5031557 := bstep (se 4 (by rfl) ⟨471708, by rfl⟩ : syracuseStep 5031557 = 943417) B943417
theorem B2475805 : Blo 650305 2475805 := bstep (se 3 (by rfl) ⟨464213, by rfl⟩ : syracuseStep 2475805 = 928427) B928427
theorem B1099615 : Blo 650305 1099615 := bstep (se 1 (by rfl) ⟨824711, by rfl⟩ : syracuseStep 1099615 = 1649423) B1649423
theorem B1099703 : Blo 650305 1099703 := bstep (se 1 (by rfl) ⟨824777, by rfl⟩ : syracuseStep 1099703 = 1649555) B1649555
theorem B4245533 : Blo 650305 4245533 := bstep (se 3 (by rfl) ⟨796037, by rfl⟩ : syracuseStep 4245533 = 1592075) B1592075
theorem B4180025 : Blo 650305 4180025 := bstep (se 2 (by rfl) ⟨1567509, by rfl⟩ : syracuseStep 4180025 = 3135019) B3135019
theorem B1853597 : Blo 650305 1853597 := bstep (se 3 (by rfl) ⟨347549, by rfl⟩ : syracuseStep 1853597 = 695099) B695099
theorem B36161977 : Blo 650305 36161977 := bstep (se 2 (by rfl) ⟨13560741, by rfl⟩ : syracuseStep 36161977 = 27121483) B27121483
theorem B1100297 : Blo 650305 1100297 := bstep (se 2 (by rfl) ⟨412611, by rfl⟩ : syracuseStep 1100297 = 825223) B825223
theorem B1100459 : Blo 650305 1100459 := bstep (se 1 (by rfl) ⟨825344, by rfl⟩ : syracuseStep 1100459 = 1650689) B1650689
theorem B2083657 : Blo 650305 2083657 := bstep (se 2 (by rfl) ⟨781371, by rfl⟩ : syracuseStep 2083657 = 1562743) B1562743
theorem B42224651 : Blo 650305 42224651 := bstep (se 1 (by rfl) ⟨31668488, by rfl⟩ : syracuseStep 42224651 = 63336977) B63336977
theorem B1100857 : Blo 650305 1100857 := bstep (se 2 (by rfl) ⟨412821, by rfl⟩ : syracuseStep 1100857 = 825643) B825643
theorem B3722435 : Blo 650305 3722435 := bstep (se 1 (by rfl) ⟨2791826, by rfl⟩ : syracuseStep 3722435 = 5583653) B5583653
theorem B1100999 : Blo 650305 1100999 := bstep (se 1 (by rfl) ⟨825749, by rfl⟩ : syracuseStep 1100999 = 1651499) B1651499
theorem B707935 : Blo 650305 707935 := bstep (se 1 (by rfl) ⟨530951, by rfl⟩ : syracuseStep 707935 = 1061903) B1061903
theorem B1101161 : Blo 650305 1101161 := bstep (se 2 (by rfl) ⟨412935, by rfl⟩ : syracuseStep 1101161 = 825871) B825871
theorem B1789327 : Blo 650305 1789327 := bstep (se 1 (by rfl) ⟨1341995, by rfl⟩ : syracuseStep 1789327 = 2683991) B2683991
theorem B1396187 : Blo 650305 1396187 := bstep (se 1 (by rfl) ⟨1047140, by rfl⟩ : syracuseStep 1396187 = 2094281) B2094281
theorem B1134043 : Blo 650305 1134043 := bstep (se 1 (by rfl) ⟨850532, by rfl⟩ : syracuseStep 1134043 = 1701065) B1701065
theorem B1101559 : Blo 650305 1101559 := bstep (se 1 (by rfl) ⟨826169, by rfl⟩ : syracuseStep 1101559 = 1652339) B1652339
theorem B9424775 : Blo 650305 9424775 := bstep (se 1 (by rfl) ⟨7068581, by rfl⟩ : syracuseStep 9424775 = 14137163) B14137163
theorem B3297185 : Blo 650305 3297185 := bstep (se 2 (by rfl) ⟨1236444, by rfl⟩ : syracuseStep 3297185 = 2472889) B2472889
theorem B4968377 : Blo 650305 4968377 := bstep (se 2 (by rfl) ⟨1863141, by rfl⟩ : syracuseStep 4968377 = 3726283) B3726283
theorem B1101755 : Blo 650305 1101755 := bstep (se 1 (by rfl) ⟨826316, by rfl⟩ : syracuseStep 1101755 = 1652633) B1652633
theorem B4182023 : Blo 650305 4182023 := bstep (se 1 (by rfl) ⟨3136517, by rfl⟩ : syracuseStep 4182023 = 6273035) B6273035
theorem B1101863 : Blo 650305 1101863 := bstep (se 1 (by rfl) ⟨826397, by rfl⟩ : syracuseStep 1101863 = 1652795) B1652795
theorem B5951717 : Blo 650305 5951717 := bstep (se 4 (by rfl) ⟨557973, by rfl⟩ : syracuseStep 5951717 = 1115947) B1115947
theorem B1102153 : Blo 650305 1102153 := bstep (se 2 (by rfl) ⟨413307, by rfl⟩ : syracuseStep 1102153 = 826615) B826615
theorem B1102187 : Blo 650305 1102187 := bstep (se 1 (by rfl) ⟨826640, by rfl⟩ : syracuseStep 1102187 = 1653281) B1653281
theorem B2118089 : Blo 650305 2118089 := bstep (se 2 (by rfl) ⟨794283, by rfl⟩ : syracuseStep 2118089 = 1588567) B1588567
theorem B5558807 : Blo 650305 5558807 := bstep (se 1 (by rfl) ⟨4169105, by rfl⟩ : syracuseStep 5558807 = 8338211) B8338211
theorem B1102585 : Blo 650305 1102585 := bstep (se 2 (by rfl) ⟨413469, by rfl⟩ : syracuseStep 1102585 = 826939) B826939
theorem B2347805 : Blo 650305 2347805 := bstep (se 3 (by rfl) ⟨440213, by rfl⟩ : syracuseStep 2347805 = 880427) B880427
theorem B2642807 : Blo 650305 2642807 := bstep (se 1 (by rfl) ⟨1982105, by rfl⟩ : syracuseStep 2642807 = 3964211) B3964211
theorem B1463201 : Blo 650305 1463201 := bstep (se 2 (by rfl) ⟨548700, by rfl⟩ : syracuseStep 1463201 = 1097401) B1097401
theorem B1102855 : Blo 650305 1102855 := bstep (se 1 (by rfl) ⟨827141, by rfl⟩ : syracuseStep 1102855 = 1654283) B1654283
theorem B4019279 : Blo 650305 4019279 := bstep (se 1 (by rfl) ⟨3014459, by rfl⟩ : syracuseStep 4019279 = 6028919) B6028919
theorem B1463543 : Blo 650305 1463543 := bstep (se 1 (by rfl) ⟨1097657, by rfl⟩ : syracuseStep 1463543 = 2195315) B2195315
theorem B1758455 : Blo 650305 1758455 := bstep (se 1 (by rfl) ⟨1318841, by rfl⟩ : syracuseStep 1758455 = 2637683) B2637683
theorem B2118923 : Blo 650305 2118923 := bstep (se 1 (by rfl) ⟨1589192, by rfl⟩ : syracuseStep 2118923 = 3178385) B3178385
theorem B1103287 : Blo 650305 1103287 := bstep (se 1 (by rfl) ⟨827465, by rfl⟩ : syracuseStep 1103287 = 1654931) B1654931
theorem B3134963 : Blo 650305 3134963 := bstep (se 1 (by rfl) ⟨2351222, by rfl⟩ : syracuseStep 3134963 = 4702445) B4702445
theorem B1103483 : Blo 650305 1103483 := bstep (se 1 (by rfl) ⟨827612, by rfl⟩ : syracuseStep 1103483 = 1655225) B1655225
theorem B3725099 : Blo 650305 3725099 := bstep (se 1 (by rfl) ⟨2793824, by rfl⟩ : syracuseStep 3725099 = 5587649) B5587649
theorem B1464137 : Blo 650305 1464137 := bstep (se 2 (by rfl) ⟨549051, by rfl⟩ : syracuseStep 1464137 = 1098103) B1098103
theorem B2479967 : Blo 650305 2479967 := bstep (se 1 (by rfl) ⟨1859975, by rfl⟩ : syracuseStep 2479967 = 3719951) B3719951
theorem B1103881 : Blo 650305 1103881 := bstep (se 2 (by rfl) ⟨413955, by rfl⟩ : syracuseStep 1103881 = 827911) B827911
theorem B1104043 : Blo 650305 1104043 := bstep (se 1 (by rfl) ⟨828032, by rfl⟩ : syracuseStep 1104043 = 1656065) B1656065
theorem B16963829 : Blo 650305 16963829 := bstep (se 5 (by rfl) ⟨795179, by rfl⟩ : syracuseStep 16963829 = 1590359) B1590359
theorem B2480665 : Blo 650305 2480665 := bstep (se 2 (by rfl) ⟨930249, by rfl⟩ : syracuseStep 2480665 = 1860499) B1860499
theorem B1464929 : Blo 650305 1464929 := bstep (se 2 (by rfl) ⟨549348, by rfl⟩ : syracuseStep 1464929 = 1098697) B1098697
theorem B2480939 : Blo 650305 2480939 := bstep (se 1 (by rfl) ⟨1860704, by rfl⟩ : syracuseStep 2480939 = 3721409) B3721409
theorem B2480969 : Blo 650305 2480969 := bstep (se 2 (by rfl) ⟨930363, by rfl⟩ : syracuseStep 2480969 = 1860727) B1860727
theorem B1235807 : Blo 650305 1235807 := bstep (se 1 (by rfl) ⟨926855, by rfl⟩ : syracuseStep 1235807 = 1853711) B1853711
theorem B1465271 : Blo 650305 1465271 := bstep (se 1 (by rfl) ⟨1098953, by rfl⟩ : syracuseStep 1465271 = 2197907) B2197907
theorem B11885611 : Blo 650305 11885611 := bstep (se 1 (by rfl) ⟨8914208, by rfl⟩ : syracuseStep 11885611 = 17828417) B17828417
theorem B1236217 : Blo 650305 1236217 := bstep (se 2 (by rfl) ⟨463581, by rfl⟩ : syracuseStep 1236217 = 927163) B927163
theorem B2088335 : Blo 650305 2088335 := bstep (se 1 (by rfl) ⟨1566251, by rfl⟩ : syracuseStep 2088335 = 3132503) B3132503
theorem B1465865 : Blo 650305 1465865 := bstep (se 2 (by rfl) ⟨549699, by rfl⟩ : syracuseStep 1465865 = 1099399) B1099399
theorem B5299751 : Blo 650305 5299751 := bstep (se 1 (by rfl) ⟨3974813, by rfl⟩ : syracuseStep 5299751 = 7949627) B7949627
theorem B1236559 : Blo 650305 1236559 := bstep (se 1 (by rfl) ⟨927419, by rfl⟩ : syracuseStep 1236559 = 1854839) B1854839
theorem B8380037 : Blo 650305 8380037 := bstep (se 4 (by rfl) ⟨785628, by rfl⟩ : syracuseStep 8380037 = 1571257) B1571257
theorem B2645693 : Blo 650305 2645693 := bstep (se 3 (by rfl) ⟨496067, by rfl⟩ : syracuseStep 2645693 = 992135) B992135
theorem B1236809 : Blo 650305 1236809 := bstep (se 2 (by rfl) ⟨463803, by rfl⟩ : syracuseStep 1236809 = 927607) B927607
theorem B1466207 : Blo 650305 1466207 := bstep (se 1 (by rfl) ⟨1099655, by rfl⟩ : syracuseStep 1466207 = 2199311) B2199311
theorem B1466387 : Blo 650305 1466387 := bstep (se 1 (by rfl) ⟨1099790, by rfl⟩ : syracuseStep 1466387 = 2199581) B2199581
theorem B2646211 : Blo 650305 2646211 := bstep (se 1 (by rfl) ⟨1984658, by rfl⟩ : syracuseStep 2646211 = 3969317) B3969317
theorem B6283493 : Blo 650305 6283493 := bstep (se 4 (by rfl) ⟨589077, by rfl⟩ : syracuseStep 6283493 = 1178155) B1178155
theorem B1466729 : Blo 650305 1466729 := bstep (se 2 (by rfl) ⟨550023, by rfl⟩ : syracuseStep 1466729 = 1100047) B1100047
theorem B1237675 : Blo 650305 1237675 := bstep (se 1 (by rfl) ⟨928256, by rfl⟩ : syracuseStep 1237675 = 1856513) B1856513
theorem B1172215 : Blo 650305 1172215 := bstep (se 1 (by rfl) ⟨879161, by rfl⟩ : syracuseStep 1172215 = 1758323) B1758323
theorem B1237751 : Blo 650305 1237751 := bstep (se 1 (by rfl) ⟨928313, by rfl⟩ : syracuseStep 1237751 = 1856627) B1856627
theorem B2777885 : Blo 650305 2777885 := bstep (se 3 (by rfl) ⟨520853, by rfl⟩ : syracuseStep 2777885 = 1041707) B1041707
theorem B2646827 : Blo 650305 2646827 := bstep (se 1 (by rfl) ⟨1985120, by rfl⟩ : syracuseStep 2646827 = 3970241) B3970241
theorem B975791 : Blo 650305 975791 := bstep (se 1 (by rfl) ⟨731843, by rfl⟩ : syracuseStep 975791 = 1463687) B1463687
theorem B1467323 : Blo 650305 1467323 := bstep (se 1 (by rfl) ⟨1100492, by rfl⟩ : syracuseStep 1467323 = 2200985) B2200985
theorem B1237979 : Blo 650305 1237979 := bstep (se 1 (by rfl) ⟨928484, by rfl⟩ : syracuseStep 1237979 = 1856969) B1856969
theorem B975881 : Blo 650305 975881 := bstep (se 2 (by rfl) ⟨365955, by rfl⟩ : syracuseStep 975881 = 731911) B731911
theorem B975911 : Blo 650305 975911 := bstep (se 1 (by rfl) ⟨731933, by rfl⟩ : syracuseStep 975911 = 1463867) B1463867
theorem B1467449 : Blo 650305 1467449 := bstep (se 2 (by rfl) ⟨550293, by rfl⟩ : syracuseStep 1467449 = 1100587) B1100587
theorem B975995 : Blo 650305 975995 := bstep (se 1 (by rfl) ⟨731996, by rfl⟩ : syracuseStep 975995 = 1463993) B1463993
theorem B976121 : Blo 650305 976121 := bstep (se 2 (by rfl) ⟨366045, by rfl⟩ : syracuseStep 976121 = 732091) B732091
theorem B976223 : Blo 650305 976223 := bstep (se 1 (by rfl) ⟨732167, by rfl⟩ : syracuseStep 976223 = 1464335) B1464335
theorem B976235 : Blo 650305 976235 := bstep (se 1 (by rfl) ⟨732176, by rfl⟩ : syracuseStep 976235 = 1464353) B1464353
theorem B2483581 : Blo 650305 2483581 := bstep (se 3 (by rfl) ⟨465671, by rfl⟩ : syracuseStep 2483581 = 931343) B931343
theorem B1467791 : Blo 650305 1467791 := bstep (se 1 (by rfl) ⟨1100843, by rfl⟩ : syracuseStep 1467791 = 2201687) B2201687
theorem B2778569 : Blo 650305 2778569 := bstep (se 2 (by rfl) ⟨1041963, by rfl⟩ : syracuseStep 2778569 = 2083927) B2083927
theorem B976463 : Blo 650305 976463 := bstep (se 1 (by rfl) ⟨732347, by rfl⟩ : syracuseStep 976463 = 1464695) B1464695
theorem B976583 : Blo 650305 976583 := bstep (se 1 (by rfl) ⟨732437, by rfl⟩ : syracuseStep 976583 = 1464875) B1464875
theorem B1861319 : Blo 650305 1861319 := bstep (se 1 (by rfl) ⟨1395989, by rfl⟩ : syracuseStep 1861319 = 2791979) B2791979
theorem B1468115 : Blo 650305 1468115 := bstep (se 1 (by rfl) ⟨1101086, by rfl⟩ : syracuseStep 1468115 = 2202173) B2202173
theorem B2352851 : Blo 650305 2352851 := bstep (se 1 (by rfl) ⟨1764638, by rfl⟩ : syracuseStep 2352851 = 3529277) B3529277
theorem B976745 : Blo 650305 976745 := bstep (se 2 (by rfl) ⟨366279, by rfl⟩ : syracuseStep 976745 = 732559) B732559
theorem B4188023 : Blo 650305 4188023 := bstep (se 1 (by rfl) ⟨3141017, by rfl⟩ : syracuseStep 4188023 = 6282035) B6282035
theorem B976823 : Blo 650305 976823 := bstep (se 1 (by rfl) ⟨732617, by rfl⟩ : syracuseStep 976823 = 1465235) B1465235
theorem B976859 : Blo 650305 976859 := bstep (se 1 (by rfl) ⟨732644, by rfl⟩ : syracuseStep 976859 = 1465289) B1465289
theorem B7039133 : Blo 650305 7039133 := bstep (se 3 (by rfl) ⟨1319837, by rfl⟩ : syracuseStep 7039133 = 2639675) B2639675
theorem B9398429 : Blo 650305 9398429 := bstep (se 3 (by rfl) ⟨1762205, by rfl⟩ : syracuseStep 9398429 = 3524411) B3524411
theorem B1239239 : Blo 650305 1239239 := bstep (se 1 (by rfl) ⟨929429, by rfl⟩ : syracuseStep 1239239 = 1858859) B1858859
theorem B9529649 : Blo 650305 9529649 := bstep (se 2 (by rfl) ⟨3573618, by rfl⟩ : syracuseStep 9529649 = 7147237) B7147237
theorem B1239391 : Blo 650305 1239391 := bstep (se 1 (by rfl) ⟨929543, by rfl⟩ : syracuseStep 1239391 = 1859087) B1859087
theorem B977327 : Blo 650305 977327 := bstep (se 1 (by rfl) ⟨732995, by rfl⟩ : syracuseStep 977327 = 1465991) B1465991
theorem B977417 : Blo 650305 977417 := bstep (se 2 (by rfl) ⟨366531, by rfl⟩ : syracuseStep 977417 = 733063) B733063
theorem B5007905 : Blo 650305 5007905 := bstep (se 2 (by rfl) ⟨1877964, by rfl⟩ : syracuseStep 5007905 = 3755929) B3755929
theorem B977447 : Blo 650305 977447 := bstep (se 1 (by rfl) ⟨733085, by rfl⟩ : syracuseStep 977447 = 1466171) B1466171
theorem B977531 : Blo 650305 977531 := bstep (se 1 (by rfl) ⟨733148, by rfl⟩ : syracuseStep 977531 = 1466297) B1466297
theorem B1469051 : Blo 650305 1469051 := bstep (se 1 (by rfl) ⟨1101788, by rfl⟩ : syracuseStep 1469051 = 2203577) B2203577
theorem B2124427 : Blo 650305 2124427 := bstep (se 1 (by rfl) ⟨1593320, by rfl⟩ : syracuseStep 2124427 = 3186641) B3186641
theorem B19098305 : Blo 650305 19098305 := bstep (se 2 (by rfl) ⟨7161864, by rfl⟩ : syracuseStep 19098305 = 14323729) B14323729
theorem B1764055 : Blo 650305 1764055 := bstep (se 1 (by rfl) ⟨1323041, by rfl⟩ : syracuseStep 1764055 = 2646083) B2646083
theorem B977657 : Blo 650305 977657 := bstep (se 2 (by rfl) ⟨366621, by rfl⟩ : syracuseStep 977657 = 733243) B733243
theorem B1469177 : Blo 650305 1469177 := bstep (se 2 (by rfl) ⟨550941, by rfl⟩ : syracuseStep 1469177 = 1101883) B1101883
theorem B977759 : Blo 650305 977759 := bstep (se 1 (by rfl) ⟨733319, by rfl⟩ : syracuseStep 977759 = 1466639) B1466639
theorem B977771 : Blo 650305 977771 := bstep (se 1 (by rfl) ⟨733328, by rfl⟩ : syracuseStep 977771 = 1466657) B1466657
theorem B2550635 : Blo 650305 2550635 := bstep (se 1 (by rfl) ⟨1912976, by rfl⟩ : syracuseStep 2550635 = 3825953) B3825953
theorem B1469447 : Blo 650305 1469447 := bstep (se 1 (by rfl) ⟨1102085, by rfl⟩ : syracuseStep 1469447 = 2204171) B2204171
theorem B650319 : Blo 650305 650319 := bstep (se 1 (by rfl) ⟨487739, by rfl⟩ : syracuseStep 650319 = 975479) B975479
theorem B977999 : Blo 650305 977999 := bstep (se 1 (by rfl) ⟨733499, by rfl⟩ : syracuseStep 977999 = 1466999) B1466999
theorem B1469519 : Blo 650305 1469519 := bstep (se 1 (by rfl) ⟨1102139, by rfl⟩ : syracuseStep 1469519 = 2204279) B2204279
theorem B650335 : Blo 650305 650335 := bstep (se 1 (by rfl) ⟨487751, by rfl⟩ : syracuseStep 650335 = 975503) B975503
theorem B650363 : Blo 650305 650363 := bstep (se 1 (by rfl) ⟨487772, by rfl⟩ : syracuseStep 650363 = 975545) B975545
theorem B650415 : Blo 650305 650415 := bstep (se 1 (by rfl) ⟨487811, by rfl⟩ : syracuseStep 650415 = 975623) B975623
theorem B6286531 : Blo 650305 6286531 := bstep (se 1 (by rfl) ⟨4714898, by rfl⟩ : syracuseStep 6286531 = 9429797) B9429797
theorem B650439 : Blo 650305 650439 := bstep (se 1 (by rfl) ⟨487829, by rfl⟩ : syracuseStep 650439 = 975659) B975659
theorem B978119 : Blo 650305 978119 := bstep (se 1 (by rfl) ⟨733589, by rfl⟩ : syracuseStep 978119 = 1467179) B1467179
theorem B650459 : Blo 650305 650459 := bstep (se 1 (by rfl) ⟨487844, by rfl⟩ : syracuseStep 650459 = 975689) B975689
theorem B1567991 : Blo 650305 1567991 := bstep (se 1 (by rfl) ⟨1175993, by rfl⟩ : syracuseStep 1567991 = 2351987) B2351987
theorem B650535 : Blo 650305 650535 := bstep (se 1 (by rfl) ⟨487901, by rfl⟩ : syracuseStep 650535 = 975803) B975803
theorem B650575 : Blo 650305 650575 := bstep (se 1 (by rfl) ⟨487931, by rfl⟩ : syracuseStep 650575 = 975863) B975863
theorem B650591 : Blo 650305 650591 := bstep (se 1 (by rfl) ⟨487943, by rfl⟩ : syracuseStep 650591 = 975887) B975887
theorem B978281 : Blo 650305 978281 := bstep (se 2 (by rfl) ⟨366855, by rfl⟩ : syracuseStep 978281 = 733711) B733711
theorem B879979 : Blo 650305 879979 := bstep (se 1 (by rfl) ⟨659984, by rfl⟩ : syracuseStep 879979 = 1319969) B1319969
theorem B650619 : Blo 650305 650619 := bstep (se 1 (by rfl) ⟨487964, by rfl⟩ : syracuseStep 650619 = 975929) B975929
theorem B650671 : Blo 650305 650671 := bstep (se 1 (by rfl) ⟨488003, by rfl⟩ : syracuseStep 650671 = 976007) B976007
theorem B978359 : Blo 650305 978359 := bstep (se 1 (by rfl) ⟨733769, by rfl⟩ : syracuseStep 978359 = 1467539) B1467539
theorem B650695 : Blo 650305 650695 := bstep (se 1 (by rfl) ⟨488021, by rfl⟩ : syracuseStep 650695 = 976043) B976043
theorem B650715 : Blo 650305 650715 := bstep (se 1 (by rfl) ⟨488036, by rfl⟩ : syracuseStep 650715 = 976073) B976073
theorem B978395 : Blo 650305 978395 := bstep (se 1 (by rfl) ⟨733796, by rfl⟩ : syracuseStep 978395 = 1467593) B1467593
theorem B1469915 : Blo 650305 1469915 := bstep (se 1 (by rfl) ⟨1102436, by rfl⟩ : syracuseStep 1469915 = 2204873) B2204873
theorem B650791 : Blo 650305 650791 := bstep (se 1 (by rfl) ⟨488093, by rfl⟩ : syracuseStep 650791 = 976187) B976187
theorem B650831 : Blo 650305 650831 := bstep (se 1 (by rfl) ⟨488123, by rfl⟩ : syracuseStep 650831 = 976247) B976247
theorem B26766935 : Blo 650305 26766935 := bstep (se 1 (by rfl) ⟨20075201, by rfl⟩ : syracuseStep 26766935 = 40150403) B40150403
theorem B650847 : Blo 650305 650847 := bstep (se 1 (by rfl) ⟨488135, by rfl⟩ : syracuseStep 650847 = 976271) B976271
theorem B650875 : Blo 650305 650875 := bstep (se 1 (by rfl) ⟨488156, by rfl⟩ : syracuseStep 650875 = 976313) B976313
theorem B2092679 : Blo 650305 2092679 := bstep (se 1 (by rfl) ⟨1569509, by rfl⟩ : syracuseStep 2092679 = 3139019) B3139019
theorem B650927 : Blo 650305 650927 := bstep (se 1 (by rfl) ⟨488195, by rfl⟩ : syracuseStep 650927 = 976391) B976391
theorem B650951 : Blo 650305 650951 := bstep (se 1 (by rfl) ⟨488213, by rfl⟩ : syracuseStep 650951 = 976427) B976427
theorem B650971 : Blo 650305 650971 := bstep (se 1 (by rfl) ⟨488228, by rfl⟩ : syracuseStep 650971 = 976457) B976457
theorem B651047 : Blo 650305 651047 := bstep (se 1 (by rfl) ⟨488285, by rfl⟩ : syracuseStep 651047 = 976571) B976571
theorem B651087 : Blo 650305 651087 := bstep (se 1 (by rfl) ⟨488315, by rfl⟩ : syracuseStep 651087 = 976631) B976631
theorem B651103 : Blo 650305 651103 := bstep (se 1 (by rfl) ⟨488327, by rfl⟩ : syracuseStep 651103 = 976655) B976655
theorem B651131 : Blo 650305 651131 := bstep (se 1 (by rfl) ⟨488348, by rfl⟩ : syracuseStep 651131 = 976697) B976697
theorem B651183 : Blo 650305 651183 := bstep (se 1 (by rfl) ⟨488387, by rfl⟩ : syracuseStep 651183 = 976775) B976775
theorem B978863 : Blo 650305 978863 := bstep (se 1 (by rfl) ⟨734147, by rfl⟩ : syracuseStep 978863 = 1468295) B1468295
theorem B1470383 : Blo 650305 1470383 := bstep (se 1 (by rfl) ⟨1102787, by rfl⟩ : syracuseStep 1470383 = 2205575) B2205575
theorem B7172027 : Blo 650305 7172027 := bstep (se 1 (by rfl) ⟨5379020, by rfl⟩ : syracuseStep 7172027 = 10758041) B10758041
theorem B651207 : Blo 650305 651207 := bstep (se 1 (by rfl) ⟨488405, by rfl⟩ : syracuseStep 651207 = 976811) B976811
theorem B651227 : Blo 650305 651227 := bstep (se 1 (by rfl) ⟨488420, by rfl⟩ : syracuseStep 651227 = 976841) B976841
theorem B978953 : Blo 650305 978953 := bstep (se 2 (by rfl) ⟨367107, by rfl⟩ : syracuseStep 978953 = 734215) B734215
theorem B651303 : Blo 650305 651303 := bstep (se 1 (by rfl) ⟨488477, by rfl⟩ : syracuseStep 651303 = 976955) B976955
theorem B978983 : Blo 650305 978983 := bstep (se 1 (by rfl) ⟨734237, by rfl⟩ : syracuseStep 978983 = 1468475) B1468475
theorem B651343 : Blo 650305 651343 := bstep (se 1 (by rfl) ⟨488507, by rfl⟩ : syracuseStep 651343 = 977015) B977015
theorem B651359 : Blo 650305 651359 := bstep (se 1 (by rfl) ⟨488519, by rfl⟩ : syracuseStep 651359 = 977039) B977039
theorem B651387 : Blo 650305 651387 := bstep (se 1 (by rfl) ⟨488540, by rfl⟩ : syracuseStep 651387 = 977081) B977081
theorem B1175675 : Blo 650305 1175675 := bstep (se 1 (by rfl) ⟨881756, by rfl⟩ : syracuseStep 1175675 = 1763513) B1763513
theorem B979067 : Blo 650305 979067 := bstep (se 1 (by rfl) ⟨734300, by rfl⟩ : syracuseStep 979067 = 1468601) B1468601
theorem B1765547 : Blo 650305 1765547 := bstep (se 1 (by rfl) ⟨1324160, by rfl⟩ : syracuseStep 1765547 = 2648321) B2648321
theorem B1470635 : Blo 650305 1470635 := bstep (se 1 (by rfl) ⟨1102976, by rfl⟩ : syracuseStep 1470635 = 2205953) B2205953
theorem B651439 : Blo 650305 651439 := bstep (se 1 (by rfl) ⟨488579, by rfl⟩ : syracuseStep 651439 = 977159) B977159
theorem B651463 : Blo 650305 651463 := bstep (se 1 (by rfl) ⟨488597, by rfl⟩ : syracuseStep 651463 = 977195) B977195
theorem B651483 : Blo 650305 651483 := bstep (se 1 (by rfl) ⟨488612, by rfl⟩ : syracuseStep 651483 = 977225) B977225
theorem B979193 : Blo 650305 979193 := bstep (se 2 (by rfl) ⟨367197, by rfl⟩ : syracuseStep 979193 = 734395) B734395
theorem B1241335 : Blo 650305 1241335 := bstep (se 1 (by rfl) ⟨931001, by rfl⟩ : syracuseStep 1241335 = 1862003) B1862003
theorem B651559 : Blo 650305 651559 := bstep (se 1 (by rfl) ⟨488669, by rfl⟩ : syracuseStep 651559 = 977339) B977339
theorem B651599 : Blo 650305 651599 := bstep (se 1 (by rfl) ⟨488699, by rfl⟩ : syracuseStep 651599 = 977399) B977399
theorem B651615 : Blo 650305 651615 := bstep (se 1 (by rfl) ⟨488711, by rfl⟩ : syracuseStep 651615 = 977423) B977423
theorem B979295 : Blo 650305 979295 := bstep (se 1 (by rfl) ⟨734471, by rfl⟩ : syracuseStep 979295 = 1468943) B1468943
theorem B979307 : Blo 650305 979307 := bstep (se 1 (by rfl) ⟨734480, by rfl⟩ : syracuseStep 979307 = 1468961) B1468961
theorem B651643 : Blo 650305 651643 := bstep (se 1 (by rfl) ⟨488732, by rfl⟩ : syracuseStep 651643 = 977465) B977465
theorem B651695 : Blo 650305 651695 := bstep (se 1 (by rfl) ⟨488771, by rfl⟩ : syracuseStep 651695 = 977543) B977543
theorem B651719 : Blo 650305 651719 := bstep (se 1 (by rfl) ⟨488789, by rfl⟩ : syracuseStep 651719 = 977579) B977579
theorem B651739 : Blo 650305 651739 := bstep (se 1 (by rfl) ⟨488804, by rfl⟩ : syracuseStep 651739 = 977609) B977609
theorem B1241563 : Blo 650305 1241563 := bstep (se 1 (by rfl) ⟨931172, by rfl⟩ : syracuseStep 1241563 = 1862345) B1862345
theorem B15692291 : Blo 650305 15692291 := bstep (se 1 (by rfl) ⟨11769218, by rfl⟩ : syracuseStep 15692291 = 23538437) B23538437
theorem B651815 : Blo 650305 651815 := bstep (se 1 (by rfl) ⟨488861, by rfl⟩ : syracuseStep 651815 = 977723) B977723
theorem B1241639 : Blo 650305 1241639 := bstep (se 1 (by rfl) ⟨931229, by rfl⟩ : syracuseStep 1241639 = 1862459) B1862459
theorem B2093627 : Blo 650305 2093627 := bstep (se 1 (by rfl) ⟨1570220, by rfl⟩ : syracuseStep 2093627 = 3140441) B3140441
theorem B651855 : Blo 650305 651855 := bstep (se 1 (by rfl) ⟨488891, by rfl⟩ : syracuseStep 651855 = 977783) B977783
theorem B979535 : Blo 650305 979535 := bstep (se 1 (by rfl) ⟨734651, by rfl⟩ : syracuseStep 979535 = 1469303) B1469303
theorem B651871 : Blo 650305 651871 := bstep (se 1 (by rfl) ⟨488903, by rfl⟩ : syracuseStep 651871 = 977807) B977807
theorem B651899 : Blo 650305 651899 := bstep (se 1 (by rfl) ⟨488924, by rfl⟩ : syracuseStep 651899 = 977849) B977849
theorem B1241723 : Blo 650305 1241723 := bstep (se 1 (by rfl) ⟨931292, by rfl⟩ : syracuseStep 1241723 = 1862585) B1862585
theorem B651951 : Blo 650305 651951 := bstep (se 1 (by rfl) ⟨488963, by rfl⟩ : syracuseStep 651951 = 977927) B977927
theorem B651975 : Blo 650305 651975 := bstep (se 1 (by rfl) ⟨488981, by rfl⟩ : syracuseStep 651975 = 977963) B977963
theorem B979655 : Blo 650305 979655 := bstep (se 1 (by rfl) ⟨734741, by rfl⟩ : syracuseStep 979655 = 1469483) B1469483
theorem B1471175 : Blo 650305 1471175 := bstep (se 1 (by rfl) ⟨1103381, by rfl⟩ : syracuseStep 1471175 = 2206763) B2206763
theorem B10711763 : Blo 650305 10711763 := bstep (se 1 (by rfl) ⟨8033822, by rfl⟩ : syracuseStep 10711763 = 16067645) B16067645
theorem B2093779 : Blo 650305 2093779 := bstep (se 1 (by rfl) ⟨1570334, by rfl⟩ : syracuseStep 2093779 = 3140669) B3140669
theorem B651995 : Blo 650305 651995 := bstep (se 1 (by rfl) ⟨488996, by rfl⟩ : syracuseStep 651995 = 977993) B977993
theorem B652071 : Blo 650305 652071 := bstep (se 1 (by rfl) ⟨489053, by rfl⟩ : syracuseStep 652071 = 978107) B978107
theorem B2978633 : Blo 650305 2978633 := bstep (se 2 (by rfl) ⟨1116987, by rfl⟩ : syracuseStep 2978633 = 2233975) B2233975
theorem B652111 : Blo 650305 652111 := bstep (se 1 (by rfl) ⟨489083, by rfl⟩ : syracuseStep 652111 = 978167) B978167
theorem B652127 : Blo 650305 652127 := bstep (se 1 (by rfl) ⟨489095, by rfl⟩ : syracuseStep 652127 = 978191) B978191
theorem B979817 : Blo 650305 979817 := bstep (se 2 (by rfl) ⟨367431, by rfl⟩ : syracuseStep 979817 = 734863) B734863
theorem B20083571 : Blo 650305 20083571 := bstep (se 1 (by rfl) ⟨15062678, by rfl⟩ : syracuseStep 20083571 = 30125357) B30125357
theorem B652155 : Blo 650305 652155 := bstep (se 1 (by rfl) ⟨489116, by rfl⟩ : syracuseStep 652155 = 978233) B978233
theorem B11891609 : Blo 650305 11891609 := bstep (se 2 (by rfl) ⟨4459353, by rfl⟩ : syracuseStep 11891609 = 8918707) B8918707
theorem B652207 : Blo 650305 652207 := bstep (se 1 (by rfl) ⟨489155, by rfl⟩ : syracuseStep 652207 = 978311) B978311
theorem B979895 : Blo 650305 979895 := bstep (se 1 (by rfl) ⟨734921, by rfl⟩ : syracuseStep 979895 = 1469843) B1469843
theorem B652231 : Blo 650305 652231 := bstep (se 1 (by rfl) ⟨489173, by rfl⟩ : syracuseStep 652231 = 978347) B978347
theorem B652251 : Blo 650305 652251 := bstep (se 1 (by rfl) ⟨489188, by rfl⟩ : syracuseStep 652251 = 978377) B978377
theorem B979931 : Blo 650305 979931 := bstep (se 1 (by rfl) ⟨734948, by rfl⟩ : syracuseStep 979931 = 1469897) B1469897
theorem B652327 : Blo 650305 652327 := bstep (se 1 (by rfl) ⟨489245, by rfl⟩ : syracuseStep 652327 = 978491) B978491
theorem B5567555 : Blo 650305 5567555 := bstep (se 1 (by rfl) ⟨4175666, by rfl⟩ : syracuseStep 5567555 = 8351333) B8351333
theorem B652367 : Blo 650305 652367 := bstep (se 1 (by rfl) ⟨489275, by rfl⟩ : syracuseStep 652367 = 978551) B978551
theorem B652383 : Blo 650305 652383 := bstep (se 1 (by rfl) ⟨489287, by rfl⟩ : syracuseStep 652383 = 978575) B978575
theorem B652411 : Blo 650305 652411 := bstep (se 1 (by rfl) ⟨489308, by rfl⟩ : syracuseStep 652411 = 978617) B978617
theorem B4945049 : Blo 650305 4945049 := bstep (se 2 (by rfl) ⟨1854393, by rfl⟩ : syracuseStep 4945049 = 3708787) B3708787
theorem B2225323 : Blo 650305 2225323 := bstep (se 1 (by rfl) ⟨1668992, by rfl⟩ : syracuseStep 2225323 = 3337985) B3337985
theorem B652463 : Blo 650305 652463 := bstep (se 1 (by rfl) ⟨489347, by rfl⟩ : syracuseStep 652463 = 978695) B978695
theorem B652487 : Blo 650305 652487 := bstep (se 1 (by rfl) ⟨489365, by rfl⟩ : syracuseStep 652487 = 978731) B978731
theorem B652507 : Blo 650305 652507 := bstep (se 1 (by rfl) ⟨489380, by rfl⟩ : syracuseStep 652507 = 978761) B978761
theorem B3306743 : Blo 650305 3306743 := bstep (se 1 (by rfl) ⟨2480057, by rfl⟩ : syracuseStep 3306743 = 4960115) B4960115
theorem B652583 : Blo 650305 652583 := bstep (se 1 (by rfl) ⟨489437, by rfl⟩ : syracuseStep 652583 = 978875) B978875
theorem B652623 : Blo 650305 652623 := bstep (se 1 (by rfl) ⟨489467, by rfl⟩ : syracuseStep 652623 = 978935) B978935
theorem B652639 : Blo 650305 652639 := bstep (se 1 (by rfl) ⟨489479, by rfl⟩ : syracuseStep 652639 = 978959) B978959
theorem B652667 : Blo 650305 652667 := bstep (se 1 (by rfl) ⟨489500, by rfl⟩ : syracuseStep 652667 = 979001) B979001
theorem B652719 : Blo 650305 652719 := bstep (se 1 (by rfl) ⟨489539, by rfl⟩ : syracuseStep 652719 = 979079) B979079
theorem B980399 : Blo 650305 980399 := bstep (se 1 (by rfl) ⟨735299, by rfl⟩ : syracuseStep 980399 = 1470599) B1470599
theorem B882103 : Blo 650305 882103 := bstep (se 1 (by rfl) ⟨661577, by rfl⟩ : syracuseStep 882103 = 1323155) B1323155
theorem B652743 : Blo 650305 652743 := bstep (se 1 (by rfl) ⟨489557, by rfl⟩ : syracuseStep 652743 = 979115) B979115
theorem B652763 : Blo 650305 652763 := bstep (se 1 (by rfl) ⟨489572, by rfl⟩ : syracuseStep 652763 = 979145) B979145
theorem B980489 : Blo 650305 980489 := bstep (se 2 (by rfl) ⟨367683, by rfl⟩ : syracuseStep 980489 = 735367) B735367
theorem B652839 : Blo 650305 652839 := bstep (se 1 (by rfl) ⟨489629, by rfl⟩ : syracuseStep 652839 = 979259) B979259
theorem B980519 : Blo 650305 980519 := bstep (se 1 (by rfl) ⟨735389, by rfl⟩ : syracuseStep 980519 = 1470779) B1470779
theorem B1472039 : Blo 650305 1472039 := bstep (se 1 (by rfl) ⟨1104029, by rfl⟩ : syracuseStep 1472039 = 2208059) B2208059
theorem B652879 : Blo 650305 652879 := bstep (se 1 (by rfl) ⟨489659, by rfl⟩ : syracuseStep 652879 = 979319) B979319
theorem B652895 : Blo 650305 652895 := bstep (se 1 (by rfl) ⟨489671, by rfl⟩ : syracuseStep 652895 = 979343) B979343
theorem B652923 : Blo 650305 652923 := bstep (se 1 (by rfl) ⟨489692, by rfl⟩ : syracuseStep 652923 = 979385) B979385
theorem B980603 : Blo 650305 980603 := bstep (se 1 (by rfl) ⟨735452, by rfl⟩ : syracuseStep 980603 = 1470905) B1470905
theorem B2258579 : Blo 650305 2258579 := bstep (se 1 (by rfl) ⟨1693934, by rfl⟩ : syracuseStep 2258579 = 3387869) B3387869
theorem B652975 : Blo 650305 652975 := bstep (se 1 (by rfl) ⟨489731, by rfl⟩ : syracuseStep 652975 = 979463) B979463
theorem B652999 : Blo 650305 652999 := bstep (se 1 (by rfl) ⟨489749, by rfl⟩ : syracuseStep 652999 = 979499) B979499
theorem B653019 : Blo 650305 653019 := bstep (se 1 (by rfl) ⟨489764, by rfl⟩ : syracuseStep 653019 = 979529) B979529
theorem B3307229 : Blo 650305 3307229 := bstep (se 3 (by rfl) ⟨620105, by rfl⟩ : syracuseStep 3307229 = 1240211) B1240211
theorem B980729 : Blo 650305 980729 := bstep (se 2 (by rfl) ⟨367773, by rfl⟩ : syracuseStep 980729 = 735547) B735547
theorem B653095 : Blo 650305 653095 := bstep (se 1 (by rfl) ⟨489821, by rfl⟩ : syracuseStep 653095 = 979643) B979643
theorem B653135 : Blo 650305 653135 := bstep (se 1 (by rfl) ⟨489851, by rfl⟩ : syracuseStep 653135 = 979703) B979703
theorem B653151 : Blo 650305 653151 := bstep (se 1 (by rfl) ⟨489863, by rfl⟩ : syracuseStep 653151 = 979727) B979727
theorem B980831 : Blo 650305 980831 := bstep (se 1 (by rfl) ⟨735623, by rfl⟩ : syracuseStep 980831 = 1471247) B1471247
theorem B1046377 : Blo 650305 1046377 := bstep (se 2 (by rfl) ⟨392391, by rfl⟩ : syracuseStep 1046377 = 784783) B784783
theorem B980843 : Blo 650305 980843 := bstep (se 1 (by rfl) ⟨735632, by rfl⟩ : syracuseStep 980843 = 1471265) B1471265
theorem B653179 : Blo 650305 653179 := bstep (se 1 (by rfl) ⟨489884, by rfl⟩ : syracuseStep 653179 = 979769) B979769
theorem B653231 : Blo 650305 653231 := bstep (se 1 (by rfl) ⟨489923, by rfl⟩ : syracuseStep 653231 = 979847) B979847
theorem B653255 : Blo 650305 653255 := bstep (se 1 (by rfl) ⟨489941, by rfl⟩ : syracuseStep 653255 = 979883) B979883
theorem B653275 : Blo 650305 653275 := bstep (se 1 (by rfl) ⟨489956, by rfl⟩ : syracuseStep 653275 = 979913) B979913
theorem B653351 : Blo 650305 653351 := bstep (se 1 (by rfl) ⟨490013, by rfl⟩ : syracuseStep 653351 = 980027) B980027
theorem B653391 : Blo 650305 653391 := bstep (se 1 (by rfl) ⟨490043, by rfl⟩ : syracuseStep 653391 = 980087) B980087
theorem B981071 : Blo 650305 981071 := bstep (se 1 (by rfl) ⟨735803, by rfl⟩ : syracuseStep 981071 = 1471607) B1471607
theorem B3340369 : Blo 650305 3340369 := bstep (se 2 (by rfl) ⟨1252638, by rfl⟩ : syracuseStep 3340369 = 2505277) B2505277
theorem B653407 : Blo 650305 653407 := bstep (se 1 (by rfl) ⟨490055, by rfl⟩ : syracuseStep 653407 = 980111) B980111
theorem B653435 : Blo 650305 653435 := bstep (se 1 (by rfl) ⟨490076, by rfl⟩ : syracuseStep 653435 = 980153) B980153
theorem B653487 : Blo 650305 653487 := bstep (se 1 (by rfl) ⟨490115, by rfl⟩ : syracuseStep 653487 = 980231) B980231
theorem B653511 : Blo 650305 653511 := bstep (se 1 (by rfl) ⟨490133, by rfl⟩ : syracuseStep 653511 = 980267) B980267
theorem B981191 : Blo 650305 981191 := bstep (se 1 (by rfl) ⟨735893, by rfl⟩ : syracuseStep 981191 = 1471787) B1471787
theorem B653531 : Blo 650305 653531 := bstep (se 1 (by rfl) ⟨490148, by rfl⟩ : syracuseStep 653531 = 980297) B980297
theorem B17824033 : Blo 650305 17824033 := bstep (se 2 (by rfl) ⟨6684012, by rfl⟩ : syracuseStep 17824033 = 13368025) B13368025
theorem B653607 : Blo 650305 653607 := bstep (se 1 (by rfl) ⟨490205, by rfl⟩ : syracuseStep 653607 = 980411) B980411
theorem B653647 : Blo 650305 653647 := bstep (se 1 (by rfl) ⟨490235, by rfl⟩ : syracuseStep 653647 = 980471) B980471
theorem B653663 : Blo 650305 653663 := bstep (se 1 (by rfl) ⟨490247, by rfl⟩ : syracuseStep 653663 = 980495) B980495
theorem B981353 : Blo 650305 981353 := bstep (se 2 (by rfl) ⟨368007, by rfl⟩ : syracuseStep 981353 = 736015) B736015
theorem B653691 : Blo 650305 653691 := bstep (se 1 (by rfl) ⟨490268, by rfl⟩ : syracuseStep 653691 = 980537) B980537
theorem B1571201 : Blo 650305 1571201 := bstep (se 2 (by rfl) ⟨589200, by rfl⟩ : syracuseStep 1571201 = 1178401) B1178401
theorem B653743 : Blo 650305 653743 := bstep (se 1 (by rfl) ⟨490307, by rfl⟩ : syracuseStep 653743 = 980615) B980615
theorem B981431 : Blo 650305 981431 := bstep (se 1 (by rfl) ⟨736073, by rfl⟩ : syracuseStep 981431 = 1472147) B1472147
theorem B653767 : Blo 650305 653767 := bstep (se 1 (by rfl) ⟨490325, by rfl⟩ : syracuseStep 653767 = 980651) B980651
theorem B653787 : Blo 650305 653787 := bstep (se 1 (by rfl) ⟨490340, by rfl⟩ : syracuseStep 653787 = 980681) B980681
theorem B2357723 : Blo 650305 2357723 := bstep (se 1 (by rfl) ⟨1768292, by rfl⟩ : syracuseStep 2357723 = 3536585) B3536585
theorem B2095625 : Blo 650305 2095625 := bstep (se 2 (by rfl) ⟨785859, by rfl⟩ : syracuseStep 2095625 = 1571719) B1571719
theorem B653863 : Blo 650305 653863 := bstep (se 1 (by rfl) ⟨490397, by rfl⟩ : syracuseStep 653863 = 980795) B980795
theorem B653903 : Blo 650305 653903 := bstep (se 1 (by rfl) ⟨490427, by rfl⟩ : syracuseStep 653903 = 980855) B980855
theorem B653919 : Blo 650305 653919 := bstep (se 1 (by rfl) ⟨490439, by rfl⟩ : syracuseStep 653919 = 980879) B980879
theorem B653947 : Blo 650305 653947 := bstep (se 1 (by rfl) ⟨490460, by rfl⟩ : syracuseStep 653947 = 980921) B980921
theorem B2685575 : Blo 650305 2685575 := bstep (se 1 (by rfl) ⟨2014181, by rfl⟩ : syracuseStep 2685575 = 4028363) B4028363
theorem B653999 : Blo 650305 653999 := bstep (se 1 (by rfl) ⟨490499, by rfl⟩ : syracuseStep 653999 = 980999) B980999
theorem B654023 : Blo 650305 654023 := bstep (se 1 (by rfl) ⟨490517, by rfl⟩ : syracuseStep 654023 = 981035) B981035
theorem B654043 : Blo 650305 654043 := bstep (se 1 (by rfl) ⟨490532, by rfl⟩ : syracuseStep 654043 = 981065) B981065
theorem B654119 : Blo 650305 654119 := bstep (se 1 (by rfl) ⟨490589, by rfl⟩ : syracuseStep 654119 = 981179) B981179
theorem B654159 : Blo 650305 654159 := bstep (se 1 (by rfl) ⟨490619, by rfl⟩ : syracuseStep 654159 = 981239) B981239
theorem B654175 : Blo 650305 654175 := bstep (se 1 (by rfl) ⟨490631, by rfl⟩ : syracuseStep 654175 = 981263) B981263
theorem B1145707 : Blo 650305 1145707 := bstep (se 1 (by rfl) ⟨859280, by rfl⟩ : syracuseStep 1145707 = 1718561) B1718561
theorem B654203 : Blo 650305 654203 := bstep (se 1 (by rfl) ⟨490652, by rfl⟩ : syracuseStep 654203 = 981305) B981305
theorem B654255 : Blo 650305 654255 := bstep (se 1 (by rfl) ⟨490691, by rfl⟩ : syracuseStep 654255 = 981383) B981383
theorem B654279 : Blo 650305 654279 := bstep (se 1 (by rfl) ⟨490709, by rfl⟩ : syracuseStep 654279 = 981419) B981419
theorem B654299 : Blo 650305 654299 := bstep (se 1 (by rfl) ⟨490724, by rfl⟩ : syracuseStep 654299 = 981449) B981449
theorem B2784257 : Blo 650305 2784257 := bstep (se 2 (by rfl) ⟨1044096, by rfl⟩ : syracuseStep 2784257 = 2088193) B2088193
theorem B4946993 : Blo 650305 4946993 := bstep (se 2 (by rfl) ⟨1855122, by rfl⟩ : syracuseStep 4946993 = 3710245) B3710245
theorem B16678061 : Blo 650305 16678061 := bstep (se 3 (by rfl) ⟨3127136, by rfl⟩ : syracuseStep 16678061 = 6254273) B6254273
theorem B16743671 : Blo 650305 16743671 := bstep (se 1 (by rfl) ⟨12557753, by rfl⟩ : syracuseStep 16743671 = 25115507) B25115507
theorem B3768257 : Blo 650305 3768257 := bstep (se 2 (by rfl) ⟨1413096, by rfl⟩ : syracuseStep 3768257 = 2826193) B2826193
theorem B22610117 : Blo 650305 22610117 := bstep (se 4 (by rfl) ⟨2119698, by rfl⟩ : syracuseStep 22610117 = 4239397) B4239397
theorem B1671787 : Blo 650305 1671787 := bstep (se 1 (by rfl) ⟨1253840, by rfl⟩ : syracuseStep 1671787 = 2507681) B2507681
theorem B4653883 : Blo 650305 4653883 := bstep (se 1 (by rfl) ⟨3490412, by rfl⟩ : syracuseStep 4653883 = 6980825) B6980825
theorem B2786683 : Blo 650305 2786683 := bstep (se 1 (by rfl) ⟨2090012, by rfl⟩ : syracuseStep 2786683 = 4180025) B4180025
theorem B3016075 : Blo 650305 3016075 := bstep (se 1 (by rfl) ⟨2262056, by rfl⟩ : syracuseStep 3016075 = 4524113) B4524113
theorem B95061509 : Blo 650305 95061509 := bstep (se 4 (by rfl) ⟨8912016, by rfl⟩ : syracuseStep 95061509 = 17824033) B17824033
theorem B3311441 : Blo 650305 3311441 := bstep (se 2 (by rfl) ⟨1241790, by rfl⟩ : syracuseStep 3311441 = 2483581) B2483581
theorem B28149767 : Blo 650305 28149767 := bstep (se 1 (by rfl) ⟨21112325, by rfl⟩ : syracuseStep 28149767 = 42224651) B42224651
theorem B6260813 : Blo 650305 6260813 := bstep (se 3 (by rfl) ⟨1173902, by rfl⟩ : syracuseStep 6260813 = 2347805) B2347805
theorem B2230553 : Blo 650305 2230553 := bstep (se 2 (by rfl) ⟨836457, by rfl⟩ : syracuseStep 2230553 = 1672915) B1672915
theorem B2198123 : Blo 650305 2198123 := bstep (se 1 (by rfl) ⟨1648592, by rfl⟩ : syracuseStep 2198123 = 3297185) B3297185
theorem B3312251 : Blo 650305 3312251 := bstep (se 1 (by rfl) ⟨2484188, by rfl⟩ : syracuseStep 3312251 = 4968377) B4968377
theorem B2788015 : Blo 650305 2788015 := bstep (se 1 (by rfl) ⟨2091011, by rfl⟩ : syracuseStep 2788015 = 4182023) B4182023
theorem B3967811 : Blo 650305 3967811 := bstep (se 1 (by rfl) ⟨2975858, by rfl⟩ : syracuseStep 3967811 = 5951717) B5951717
theorem B10718077 : Blo 650305 10718077 := bstep (se 3 (by rfl) ⟨2009639, by rfl⟩ : syracuseStep 10718077 = 4019279) B4019279
theorem B3705871 : Blo 650305 3705871 := bstep (se 1 (by rfl) ⟨2779403, by rfl⟩ : syracuseStep 3705871 = 5558807) B5558807
theorem B3017843 : Blo 650305 3017843 := bstep (se 1 (by rfl) ⟨2263382, by rfl⟩ : syracuseStep 3017843 = 4526765) B4526765
theorem B2198717 : Blo 650305 2198717 := bstep (se 3 (by rfl) ⟨412259, by rfl⟩ : syracuseStep 2198717 = 824519) B824519
theorem B1412615 : Blo 650305 1412615 := bstep (se 1 (by rfl) ⟨1059461, by rfl⟩ : syracuseStep 1412615 = 2118923) B2118923
theorem B2232329 : Blo 650305 2232329 := bstep (se 2 (by rfl) ⟨837123, by rfl⟩ : syracuseStep 2232329 = 1674247) B1674247
theorem B11309219 : Blo 650305 11309219 := bstep (se 1 (by rfl) ⟨8481914, by rfl⟩ : syracuseStep 11309219 = 16963829) B16963829
theorem B823871 : Blo 650305 823871 := bstep (se 1 (by rfl) ⟨617903, by rfl⟩ : syracuseStep 823871 = 1235807) B1235807
theorem B825167 : Blo 650305 825167 := bstep (se 1 (by rfl) ⟨618875, by rfl⟩ : syracuseStep 825167 = 1237751) B1237751
theorem B825319 : Blo 650305 825319 := bstep (se 1 (by rfl) ⟨618989, by rfl⟩ : syracuseStep 825319 = 1237979) B1237979
theorem B2201633 : Blo 650305 2201633 := bstep (se 2 (by rfl) ⟨825612, by rfl⟩ : syracuseStep 2201633 = 1651225) B1651225
theorem B11868389 : Blo 650305 11868389 := bstep (se 4 (by rfl) ⟨1112661, by rfl⟩ : syracuseStep 11868389 = 2225323) B2225323
theorem B2792015 : Blo 650305 2792015 := bstep (se 1 (by rfl) ⟨2094011, by rfl⟩ : syracuseStep 2792015 = 4188023) B4188023
theorem B4692755 : Blo 650305 4692755 := bstep (se 1 (by rfl) ⟨3519566, by rfl⟩ : syracuseStep 4692755 = 7039133) B7039133
theorem B6265619 : Blo 650305 6265619 := bstep (se 1 (by rfl) ⟨4699214, by rfl⟩ : syracuseStep 6265619 = 9398429) B9398429
theorem B10067165 : Blo 650305 10067165 := bstep (se 3 (by rfl) ⟨1887593, by rfl⟩ : syracuseStep 10067165 = 3775187) B3775187
theorem B1646315 : Blo 650305 1646315 := bstep (se 1 (by rfl) ⟨1234736, by rfl⟩ : syracuseStep 1646315 = 2469473) B2469473
theorem B990955 : Blo 650305 990955 := bstep (se 1 (by rfl) ⟨743216, by rfl⟩ : syracuseStep 990955 = 1486433) B1486433
theorem B10461527 : Blo 650305 10461527 := bstep (se 1 (by rfl) ⟨7846145, by rfl⟩ : syracuseStep 10461527 = 15692291) B15692291
theorem B2236763 : Blo 650305 2236763 := bstep (se 1 (by rfl) ⟨1677572, by rfl⟩ : syracuseStep 2236763 = 3355145) B3355145
theorem B827759 : Blo 650305 827759 := bstep (se 1 (by rfl) ⟨620819, by rfl⟩ : syracuseStep 827759 = 1241639) B1241639
theorem B827815 : Blo 650305 827815 := bstep (se 1 (by rfl) ⟨620861, by rfl⟩ : syracuseStep 827815 = 1241723) B1241723
theorem B1647175 : Blo 650305 1647175 := bstep (se 1 (by rfl) ⟨1235381, by rfl⟩ : syracuseStep 1647175 = 2470763) B2470763
theorem B1647287 : Blo 650305 1647287 := bstep (se 1 (by rfl) ⟨1235465, by rfl⟩ : syracuseStep 1647287 = 2470931) B2470931
theorem B3711703 : Blo 650305 3711703 := bstep (se 1 (by rfl) ⟨2783777, by rfl⟩ : syracuseStep 3711703 = 5567555) B5567555
theorem B2204495 : Blo 650305 2204495 := bstep (se 1 (by rfl) ⟨1653371, by rfl⟩ : syracuseStep 2204495 = 3306743) B3306743
theorem B5350337 : Blo 650305 5350337 := bstep (se 2 (by rfl) ⟨2006376, by rfl⟩ : syracuseStep 5350337 = 4012753) B4012753
theorem B2204819 : Blo 650305 2204819 := bstep (se 1 (by rfl) ⟨1653614, by rfl⟩ : syracuseStep 2204819 = 3307229) B3307229
theorem B2205089 : Blo 650305 2205089 := bstep (se 2 (by rfl) ⟨826908, by rfl⟩ : syracuseStep 2205089 = 1653817) B1653817
theorem B1648289 : Blo 650305 1648289 := bstep (se 2 (by rfl) ⟨618108, by rfl⟩ : syracuseStep 1648289 = 1236217) B1236217
theorem B5580677 : Blo 650305 5580677 := bstep (se 4 (by rfl) ⟨523188, by rfl⟩ : syracuseStep 5580677 = 1046377) B1046377
theorem B1648745 : Blo 650305 1648745 := bstep (se 2 (by rfl) ⟨618279, by rfl⟩ : syracuseStep 1648745 = 1236559) B1236559
theorem B11118707 : Blo 650305 11118707 := bstep (se 1 (by rfl) ⟨8339030, by rfl⟩ : syracuseStep 11118707 = 16678061) B16678061
theorem B1255771 : Blo 650305 1255771 := bstep (se 1 (by rfl) ⟨941828, by rfl⟩ : syracuseStep 1255771 = 1883657) B1883657
theorem B1649231 : Blo 650305 1649231 := bstep (se 1 (by rfl) ⟨1236923, by rfl⟩ : syracuseStep 1649231 = 2473847) B2473847
theorem B5286647 : Blo 650305 5286647 := bstep (se 1 (by rfl) ⟨3964985, by rfl⟩ : syracuseStep 5286647 = 7929971) B7929971
theorem B8366915 : Blo 650305 8366915 := bstep (se 1 (by rfl) ⟨6275186, by rfl⟩ : syracuseStep 8366915 = 12550373) B12550373
theorem B731983 : Blo 650305 731983 := bstep (se 1 (by rfl) ⟨548987, by rfl⟩ : syracuseStep 731983 = 1097975) B1097975
theorem B1649879 : Blo 650305 1649879 := bstep (se 1 (by rfl) ⟨1237409, by rfl⟩ : syracuseStep 1649879 = 2474819) B2474819
theorem B732379 : Blo 650305 732379 := bstep (se 1 (by rfl) ⟨549284, by rfl⟩ : syracuseStep 732379 = 1098569) B1098569
theorem B732667 : Blo 650305 732667 := bstep (se 1 (by rfl) ⟨549500, by rfl⟩ : syracuseStep 732667 = 1099001) B1099001
theorem B1650233 : Blo 650305 1650233 := bstep (se 2 (by rfl) ⟨618837, by rfl⟩ : syracuseStep 1650233 = 1237675) B1237675
theorem B732847 : Blo 650305 732847 := bstep (se 1 (by rfl) ⟨549635, by rfl⟩ : syracuseStep 732847 = 1099271) B1099271
theorem B8466119 : Blo 650305 8466119 := bstep (se 1 (by rfl) ⟨6349589, by rfl⟩ : syracuseStep 8466119 = 12699179) B12699179
theorem B3354371 : Blo 650305 3354371 := bstep (se 1 (by rfl) ⟨2515778, by rfl⟩ : syracuseStep 3354371 = 5031557) B5031557
theorem B7450379 : Blo 650305 7450379 := bstep (se 1 (by rfl) ⟨5587784, by rfl⟩ : syracuseStep 7450379 = 11175569) B11175569
theorem B5648237 : Blo 650305 5648237 := bstep (se 3 (by rfl) ⟨1059044, by rfl⟩ : syracuseStep 5648237 = 2118089) B2118089
theorem B2469761 : Blo 650305 2469761 := bstep (se 2 (by rfl) ⟨926160, by rfl⟩ : syracuseStep 2469761 = 1852321) B1852321
theorem B733135 : Blo 650305 733135 := bstep (se 1 (by rfl) ⟨549851, by rfl⟩ : syracuseStep 733135 = 1099703) B1099703
theorem B2830355 : Blo 650305 2830355 := bstep (se 1 (by rfl) ⟨2122766, by rfl⟩ : syracuseStep 2830355 = 4245533) B4245533
theorem B3977419 : Blo 650305 3977419 := bstep (se 1 (by rfl) ⟨2983064, by rfl⟩ : syracuseStep 3977419 = 5966129) B5966129
theorem B733531 : Blo 650305 733531 := bstep (se 1 (by rfl) ⟨550148, by rfl⟩ : syracuseStep 733531 = 1100297) B1100297
theorem B733639 : Blo 650305 733639 := bstep (se 1 (by rfl) ⟨550229, by rfl⟩ : syracuseStep 733639 = 1100459) B1100459
theorem B2208275 : Blo 650305 2208275 := bstep (se 1 (by rfl) ⟨1656206, by rfl⟩ : syracuseStep 2208275 = 3312413) B3312413
theorem B733999 : Blo 650305 733999 := bstep (se 1 (by rfl) ⟨550499, by rfl⟩ : syracuseStep 733999 = 1100999) B1100999
theorem B734107 : Blo 650305 734107 := bstep (se 1 (by rfl) ⟨550580, by rfl⟩ : syracuseStep 734107 = 1101161) B1101161
theorem B930791 : Blo 650305 930791 := bstep (se 1 (by rfl) ⟨698093, by rfl⟩ : syracuseStep 930791 = 1396187) B1396187
theorem B734503 : Blo 650305 734503 := bstep (se 1 (by rfl) ⟨550877, by rfl⟩ : syracuseStep 734503 = 1101755) B1101755
theorem B4240745 : Blo 650305 4240745 := bstep (se 2 (by rfl) ⟨1590279, by rfl⟩ : syracuseStep 4240745 = 3180559) B3180559
theorem B734575 : Blo 650305 734575 := bstep (se 1 (by rfl) ⟨550931, by rfl⟩ : syracuseStep 734575 = 1101863) B1101863
theorem B2471431 : Blo 650305 2471431 := bstep (se 1 (by rfl) ⟨1853573, by rfl⟩ : syracuseStep 2471431 = 3707147) B3707147
theorem B734791 : Blo 650305 734791 := bstep (se 1 (by rfl) ⟨551093, by rfl⟩ : syracuseStep 734791 = 1102187) B1102187
theorem B1652521 : Blo 650305 1652521 := bstep (se 2 (by rfl) ⟨619695, by rfl⟩ : syracuseStep 1652521 = 1239391) B1239391
theorem B2471735 : Blo 650305 2471735 := bstep (se 1 (by rfl) ⟨1853801, by rfl⟩ : syracuseStep 2471735 = 3707603) B3707603
theorem B48215969 : Blo 650305 48215969 := bstep (se 2 (by rfl) ⟨18080988, by rfl⟩ : syracuseStep 48215969 = 36161977) B36161977
theorem B2471917 : Blo 650305 2471917 := bstep (se 3 (by rfl) ⟨463484, by rfl⟩ : syracuseStep 2471917 = 926969) B926969
theorem B2832569 : Blo 650305 2832569 := bstep (se 2 (by rfl) ⟨1062213, by rfl⟩ : syracuseStep 2832569 = 2124427) B2124427
theorem B2472221 : Blo 650305 2472221 := bstep (se 3 (by rfl) ⟨463541, by rfl⟩ : syracuseStep 2472221 = 927083) B927083
theorem B735655 : Blo 650305 735655 := bstep (se 1 (by rfl) ⟨551741, by rfl⟩ : syracuseStep 735655 = 1103483) B1103483
theorem B2472403 : Blo 650305 2472403 := bstep (se 1 (by rfl) ⟨1854302, by rfl⟩ : syracuseStep 2472403 = 3708605) B3708605
theorem B1653311 : Blo 650305 1653311 := bstep (se 1 (by rfl) ⟨1239983, by rfl⟩ : syracuseStep 1653311 = 2479967) B2479967
theorem B2472875 : Blo 650305 2472875 := bstep (se 1 (by rfl) ⟨1854656, by rfl⟩ : syracuseStep 2472875 = 3709313) B3709313
theorem B3718061 : Blo 650305 3718061 := bstep (se 3 (by rfl) ⟨697136, by rfl⟩ : syracuseStep 3718061 = 1394273) B1394273
theorem B4963517 : Blo 650305 4963517 := bstep (se 3 (by rfl) ⟨930659, by rfl⟩ : syracuseStep 4963517 = 1861319) B1861319
theorem B1653959 : Blo 650305 1653959 := bstep (se 1 (by rfl) ⟨1240469, by rfl⟩ : syracuseStep 1653959 = 2480939) B2480939
theorem B1653979 : Blo 650305 1653979 := bstep (se 1 (by rfl) ⟨1240484, by rfl⟩ : syracuseStep 1653979 = 2480969) B2480969
theorem B6110437 : Blo 650305 6110437 := bstep (se 4 (by rfl) ⟨572853, by rfl⟩ : syracuseStep 6110437 = 1145707) B1145707
theorem B1392223 : Blo 650305 1392223 := bstep (se 1 (by rfl) ⟨1044167, by rfl⟩ : syracuseStep 1392223 = 2088335) B2088335
theorem B835307 : Blo 650305 835307 := bstep (se 1 (by rfl) ⟨626480, by rfl⟩ : syracuseStep 835307 = 1252961) B1252961
theorem B5586691 : Blo 650305 5586691 := bstep (se 1 (by rfl) ⟨4190018, by rfl⟩ : syracuseStep 5586691 = 8380037) B8380037
theorem B1097833 : Blo 650305 1097833 := bstep (se 2 (by rfl) ⟨411687, by rfl⟩ : syracuseStep 1097833 = 823375) B823375
theorem B1655113 : Blo 650305 1655113 := bstep (se 2 (by rfl) ⟨620667, by rfl⟩ : syracuseStep 1655113 = 1241335) B1241335
theorem B2474347 : Blo 650305 2474347 := bstep (se 1 (by rfl) ⟨1855760, by rfl⟩ : syracuseStep 2474347 = 3711521) B3711521
theorem B1851923 : Blo 650305 1851923 := bstep (se 1 (by rfl) ⟨1388942, by rfl⟩ : syracuseStep 1851923 = 2777885) B2777885
theorem B1655417 : Blo 650305 1655417 := bstep (se 2 (by rfl) ⟨620781, by rfl⟩ : syracuseStep 1655417 = 1241563) B1241563
theorem B3293945 : Blo 650305 3293945 := bstep (se 2 (by rfl) ⟨1235229, by rfl⟩ : syracuseStep 3293945 = 2470459) B2470459
theorem B23774147 : Blo 650305 23774147 := bstep (se 1 (by rfl) ⟨17830610, by rfl⟩ : syracuseStep 23774147 = 35661221) B35661221
theorem B1852379 : Blo 650305 1852379 := bstep (se 1 (by rfl) ⟨1389284, by rfl⟩ : syracuseStep 1852379 = 2778569) B2778569
theorem B4178947 : Blo 650305 4178947 := bstep (se 1 (by rfl) ⟨3134210, by rfl⟩ : syracuseStep 4178947 = 6268421) B6268421
theorem B78169315 : Blo 650305 78169315 := bstep (se 1 (by rfl) ⟨58626986, by rfl⟩ : syracuseStep 78169315 = 117253973) B117253973
theorem B7914995 : Blo 650305 7914995 := bstep (se 1 (by rfl) ⟨5936246, by rfl⟩ : syracuseStep 7914995 = 11872493) B11872493
theorem B1099561 : Blo 650305 1099561 := bstep (se 2 (by rfl) ⟨412335, by rfl⟩ : syracuseStep 1099561 = 824671) B824671
theorem B12732203 : Blo 650305 12732203 := bstep (se 1 (by rfl) ⟨9549152, by rfl⟩ : syracuseStep 12732203 = 19098305) B19098305
theorem B5556073 : Blo 650305 5556073 := bstep (se 2 (by rfl) ⟨2083527, by rfl⟩ : syracuseStep 5556073 = 4167055) B4167055
theorem B5949521 : Blo 650305 5949521 := bstep (se 2 (by rfl) ⟨2231070, by rfl⟩ : syracuseStep 5949521 = 4462141) B4462141
theorem B17844623 : Blo 650305 17844623 := bstep (se 1 (by rfl) ⟨13383467, by rfl⟩ : syracuseStep 17844623 = 26766935) B26766935
theorem B1395119 : Blo 650305 1395119 := bstep (se 1 (by rfl) ⟨1046339, by rfl⟩ : syracuseStep 1395119 = 2092679) B2092679
theorem B6048229 : Blo 650305 6048229 := bstep (se 4 (by rfl) ⟨567021, by rfl⟩ : syracuseStep 6048229 = 1134043) B1134043
theorem B1100351 : Blo 650305 1100351 := bstep (se 1 (by rfl) ⟨825263, by rfl⟩ : syracuseStep 1100351 = 1650527) B1650527
theorem B1395751 : Blo 650305 1395751 := bstep (se 1 (by rfl) ⟨1046813, by rfl⟩ : syracuseStep 1395751 = 2093627) B2093627
theorem B13028525 : Blo 650305 13028525 := bstep (se 3 (by rfl) ⟨2442848, by rfl⟩ : syracuseStep 13028525 = 4885697) B4885697
theorem B1101019 : Blo 650305 1101019 := bstep (se 1 (by rfl) ⟨825764, by rfl⟩ : syracuseStep 1101019 = 1651529) B1651529
theorem B1985755 : Blo 650305 1985755 := bstep (se 1 (by rfl) ⟨1489316, by rfl⟩ : syracuseStep 1985755 = 2978633) B2978633
theorem B13389047 : Blo 650305 13389047 := bstep (se 1 (by rfl) ⟨10041785, by rfl⟩ : syracuseStep 13389047 = 20083571) B20083571
theorem B3296699 : Blo 650305 3296699 := bstep (se 1 (by rfl) ⟨2472524, by rfl⟩ : syracuseStep 3296699 = 4945049) B4945049
theorem B14077651 : Blo 650305 14077651 := bstep (se 1 (by rfl) ⟨10558238, by rfl⟩ : syracuseStep 14077651 = 21116477) B21116477
theorem B3526507 : Blo 650305 3526507 := bstep (se 1 (by rfl) ⟨2644880, by rfl⟩ : syracuseStep 3526507 = 5289761) B5289761
theorem B1101775 : Blo 650305 1101775 := bstep (se 1 (by rfl) ⟨826331, by rfl⟩ : syracuseStep 1101775 = 1652663) B1652663
theorem B15847481 : Blo 650305 15847481 := bstep (se 2 (by rfl) ⟨5942805, by rfl⟩ : syracuseStep 15847481 = 11885611) B11885611
theorem B1397083 : Blo 650305 1397083 := bstep (se 1 (by rfl) ⟨1047812, by rfl⟩ : syracuseStep 1397083 = 2095625) B2095625
theorem B1790383 : Blo 650305 1790383 := bstep (se 1 (by rfl) ⟨1342787, by rfl⟩ : syracuseStep 1790383 = 2685575) B2685575
theorem B1102457 : Blo 650305 1102457 := bstep (se 2 (by rfl) ⟨413421, by rfl⟩ : syracuseStep 1102457 = 826843) B826843
theorem B1856171 : Blo 650305 1856171 := bstep (se 1 (by rfl) ⟨1392128, by rfl⟩ : syracuseStep 1856171 = 2784257) B2784257
theorem B1102511 : Blo 650305 1102511 := bstep (se 1 (by rfl) ⟨826883, by rfl⟩ : syracuseStep 1102511 = 1653767) B1653767
theorem B3297995 : Blo 650305 3297995 := bstep (se 1 (by rfl) ⟨2473496, by rfl⟩ : syracuseStep 3297995 = 4946993) B4946993
theorem B11162447 : Blo 650305 11162447 := bstep (se 1 (by rfl) ⟨8371835, by rfl⟩ : syracuseStep 11162447 = 16743671) B16743671
theorem B3298157 : Blo 650305 3298157 := bstep (se 3 (by rfl) ⟨618404, by rfl⟩ : syracuseStep 3298157 = 1236809) B1236809
theorem B1102747 : Blo 650305 1102747 := bstep (se 1 (by rfl) ⟨827060, by rfl⟩ : syracuseStep 1102747 = 1654121) B1654121
theorem B2643193 : Blo 650305 2643193 := bstep (se 2 (by rfl) ⟨991197, by rfl⟩ : syracuseStep 2643193 = 1982395) B1982395
theorem B2512171 : Blo 650305 2512171 := bstep (se 1 (by rfl) ⟨1884128, by rfl⟩ : syracuseStep 2512171 = 3768257) B3768257
theorem B3528281 : Blo 650305 3528281 := bstep (se 2 (by rfl) ⟨1323105, by rfl⟩ : syracuseStep 3528281 = 2646211) B2646211
theorem B1463903 : Blo 650305 1463903 := bstep (se 1 (by rfl) ⟨1097927, by rfl⟩ : syracuseStep 1463903 = 2195855) B2195855
theorem B3135133 : Blo 650305 3135133 := bstep (se 3 (by rfl) ⟨587837, by rfl⟩ : syracuseStep 3135133 = 1175675) B1175675
theorem B1464119 : Blo 650305 1464119 := bstep (se 1 (by rfl) ⟨1098089, by rfl⟩ : syracuseStep 1464119 = 2196179) B2196179
theorem B3135287 : Blo 650305 3135287 := bstep (se 1 (by rfl) ⟨2351465, by rfl⟩ : syracuseStep 3135287 = 4702931) B4702931
theorem B1464425 : Blo 650305 1464425 := bstep (se 2 (by rfl) ⟨549159, by rfl⟩ : syracuseStep 1464425 = 1098319) B1098319
theorem B3168695 : Blo 650305 3168695 := bstep (se 1 (by rfl) ⟨2376521, by rfl⟩ : syracuseStep 3168695 = 4753043) B4753043
theorem B1464911 : Blo 650305 1464911 := bstep (se 1 (by rfl) ⟨1098683, by rfl⟩ : syracuseStep 1464911 = 2197367) B2197367
theorem B1465055 : Blo 650305 1465055 := bstep (se 1 (by rfl) ⟨1098791, by rfl⟩ : syracuseStep 1465055 = 2197583) B2197583
theorem B1235731 : Blo 650305 1235731 := bstep (se 1 (by rfl) ⟨926798, by rfl⟩ : syracuseStep 1235731 = 1853597) B1853597
theorem B3955643 : Blo 650305 3955643 := bstep (se 1 (by rfl) ⟨2966732, by rfl⟩ : syracuseStep 3955643 = 5933465) B5933465
theorem B1465307 : Blo 650305 1465307 := bstep (se 1 (by rfl) ⟨1098980, by rfl⟩ : syracuseStep 1465307 = 2197961) B2197961
theorem B1465487 : Blo 650305 1465487 := bstep (se 1 (by rfl) ⟨1099115, by rfl⟩ : syracuseStep 1465487 = 2198231) B2198231
theorem B1465577 : Blo 650305 1465577 := bstep (se 2 (by rfl) ⟨549591, by rfl⟩ : syracuseStep 1465577 = 1099183) B1099183
theorem B1465631 : Blo 650305 1465631 := bstep (se 1 (by rfl) ⟨1099223, by rfl⟩ : syracuseStep 1465631 = 2198447) B2198447
theorem B2481623 : Blo 650305 2481623 := bstep (se 1 (by rfl) ⟨1861217, by rfl⟩ : syracuseStep 2481623 = 3722435) B3722435
theorem B3301073 : Blo 650305 3301073 := bstep (se 2 (by rfl) ⟨1237902, by rfl⟩ : syracuseStep 3301073 = 2475805) B2475805
theorem B1466153 : Blo 650305 1466153 := bstep (se 2 (by rfl) ⟨549807, by rfl⟩ : syracuseStep 1466153 = 1099615) B1099615
theorem B6283183 : Blo 650305 6283183 := bstep (se 1 (by rfl) ⟨4712387, by rfl⟩ : syracuseStep 6283183 = 9424775) B9424775
theorem B1761871 : Blo 650305 1761871 := bstep (se 1 (by rfl) ⟨1321403, by rfl⟩ : syracuseStep 1761871 = 2642807) B2642807
theorem B975467 : Blo 650305 975467 := bstep (se 1 (by rfl) ⟨731600, by rfl⟩ : syracuseStep 975467 = 1463201) B1463201
theorem B2777935 : Blo 650305 2777935 := bstep (se 1 (by rfl) ⟨2083451, by rfl⟩ : syracuseStep 2777935 = 4166903) B4166903
theorem B975695 : Blo 650305 975695 := bstep (se 1 (by rfl) ⟨731771, by rfl⟩ : syracuseStep 975695 = 1463543) B1463543
theorem B1172303 : Blo 650305 1172303 := bstep (se 1 (by rfl) ⟨879227, by rfl⟩ : syracuseStep 1172303 = 1758455) B1758455
theorem B1467215 : Blo 650305 1467215 := bstep (se 1 (by rfl) ⟨1100411, by rfl⟩ : syracuseStep 1467215 = 2200823) B2200823
theorem B2352073 : Blo 650305 2352073 := bstep (se 2 (by rfl) ⟨882027, by rfl⟩ : syracuseStep 2352073 = 1764055) B1764055
theorem B2089975 : Blo 650305 2089975 := bstep (se 1 (by rfl) ⟨1567481, by rfl⟩ : syracuseStep 2089975 = 3134963) B3134963
theorem B1467431 : Blo 650305 1467431 := bstep (se 1 (by rfl) ⟨1100573, by rfl⟩ : syracuseStep 1467431 = 2201147) B2201147
theorem B2778209 : Blo 650305 2778209 := bstep (se 2 (by rfl) ⟨1041828, by rfl⟩ : syracuseStep 2778209 = 2083657) B2083657
theorem B11166821 : Blo 650305 11166821 := bstep (se 4 (by rfl) ⟨1046889, by rfl⟩ : syracuseStep 11166821 = 2093779) B2093779
theorem B2483399 : Blo 650305 2483399 := bstep (se 1 (by rfl) ⟨1862549, by rfl⟩ : syracuseStep 2483399 = 3725099) B3725099
theorem B976091 : Blo 650305 976091 := bstep (se 1 (by rfl) ⟨732068, by rfl⟩ : syracuseStep 976091 = 1464137) B1464137
theorem B1467611 : Blo 650305 1467611 := bstep (se 1 (by rfl) ⟨1100708, by rfl⟩ : syracuseStep 1467611 = 2201417) B2201417
theorem B6251813 : Blo 650305 6251813 := bstep (se 4 (by rfl) ⟨586107, by rfl⟩ : syracuseStep 6251813 = 1172215) B1172215
theorem B976265 : Blo 650305 976265 := bstep (se 2 (by rfl) ⟨366099, by rfl⟩ : syracuseStep 976265 = 732199) B732199
theorem B1467809 : Blo 650305 1467809 := bstep (se 2 (by rfl) ⟨550428, by rfl⟩ : syracuseStep 1467809 = 1100857) B1100857
theorem B1861127 : Blo 650305 1861127 := bstep (se 1 (by rfl) ⟨1395845, by rfl⟩ : syracuseStep 1861127 = 2791691) B2791691
theorem B8382041 : Blo 650305 8382041 := bstep (se 2 (by rfl) ⟨3143265, by rfl⟩ : syracuseStep 8382041 = 6286531) B6286531
theorem B976619 : Blo 650305 976619 := bstep (se 1 (by rfl) ⟨732464, by rfl⟩ : syracuseStep 976619 = 1464929) B1464929
theorem B943913 : Blo 650305 943913 := bstep (se 2 (by rfl) ⟨353967, by rfl⟩ : syracuseStep 943913 = 707935) B707935
theorem B1173305 : Blo 650305 1173305 := bstep (se 2 (by rfl) ⟨439989, by rfl⟩ : syracuseStep 1173305 = 879979) B879979
theorem B2385769 : Blo 650305 2385769 := bstep (se 2 (by rfl) ⟨894663, by rfl⟩ : syracuseStep 2385769 = 1789327) B1789327
theorem B976847 : Blo 650305 976847 := bstep (se 1 (by rfl) ⟨732635, by rfl⟩ : syracuseStep 976847 = 1465271) B1465271
theorem B1468367 : Blo 650305 1468367 := bstep (se 1 (by rfl) ⟨1101275, by rfl⟩ : syracuseStep 1468367 = 2202551) B2202551
theorem B3303503 : Blo 650305 3303503 := bstep (se 1 (by rfl) ⟨2477627, by rfl⟩ : syracuseStep 3303503 = 4955255) B4955255
theorem B1468745 : Blo 650305 1468745 := bstep (se 2 (by rfl) ⟨550779, by rfl⟩ : syracuseStep 1468745 = 1101559) B1101559
theorem B977243 : Blo 650305 977243 := bstep (se 1 (by rfl) ⟨732932, by rfl⟩ : syracuseStep 977243 = 1465865) B1465865
theorem B1468763 : Blo 650305 1468763 := bstep (se 1 (by rfl) ⟨1101572, by rfl⟩ : syracuseStep 1468763 = 2203145) B2203145
theorem B3533167 : Blo 650305 3533167 := bstep (se 1 (by rfl) ⟨2649875, by rfl⟩ : syracuseStep 3533167 = 5299751) B5299751
theorem B1763795 : Blo 650305 1763795 := bstep (se 1 (by rfl) ⟨1322846, by rfl⟩ : syracuseStep 1763795 = 2645693) B2645693
theorem B977471 : Blo 650305 977471 := bstep (se 1 (by rfl) ⟨733103, by rfl⟩ : syracuseStep 977471 = 1466207) B1466207
theorem B977591 : Blo 650305 977591 := bstep (se 1 (by rfl) ⟨733193, by rfl⟩ : syracuseStep 977591 = 1466387) B1466387
theorem B4188995 : Blo 650305 4188995 := bstep (se 1 (by rfl) ⟨3141746, by rfl⟩ : syracuseStep 4188995 = 6283493) B6283493
theorem B977819 : Blo 650305 977819 := bstep (se 1 (by rfl) ⟨733364, by rfl⟩ : syracuseStep 977819 = 1466729) B1466729
theorem B1469339 : Blo 650305 1469339 := bstep (se 1 (by rfl) ⟨1102004, by rfl⟩ : syracuseStep 1469339 = 2204009) B2204009
theorem B1469537 : Blo 650305 1469537 := bstep (se 2 (by rfl) ⟨551076, by rfl⟩ : syracuseStep 1469537 = 1102153) B1102153
theorem B2649277 : Blo 650305 2649277 := bstep (se 3 (by rfl) ⟨496739, by rfl⟩ : syracuseStep 2649277 = 993479) B993479
theorem B3304637 : Blo 650305 3304637 := bstep (se 3 (by rfl) ⟨619619, by rfl⟩ : syracuseStep 3304637 = 1239239) B1239239
theorem B1764551 : Blo 650305 1764551 := bstep (se 1 (by rfl) ⟨1323413, by rfl⟩ : syracuseStep 1764551 = 2646827) B2646827
theorem B650527 : Blo 650305 650527 := bstep (se 1 (by rfl) ⟨487895, by rfl⟩ : syracuseStep 650527 = 975791) B975791
theorem B978215 : Blo 650305 978215 := bstep (se 1 (by rfl) ⟨733661, by rfl⟩ : syracuseStep 978215 = 1467323) B1467323
theorem B1469735 : Blo 650305 1469735 := bstep (se 1 (by rfl) ⟨1102301, by rfl⟩ : syracuseStep 1469735 = 2204603) B2204603
theorem B650587 : Blo 650305 650587 := bstep (se 1 (by rfl) ⟨487940, by rfl⟩ : syracuseStep 650587 = 975881) B975881
theorem B650607 : Blo 650305 650607 := bstep (se 1 (by rfl) ⟨487955, by rfl⟩ : syracuseStep 650607 = 975911) B975911
theorem B978299 : Blo 650305 978299 := bstep (se 1 (by rfl) ⟨733724, by rfl⟩ : syracuseStep 978299 = 1467449) B1467449
theorem B650663 : Blo 650305 650663 := bstep (se 1 (by rfl) ⟨487997, by rfl⟩ : syracuseStep 650663 = 975995) B975995
theorem B978425 : Blo 650305 978425 := bstep (se 2 (by rfl) ⟨366909, by rfl⟩ : syracuseStep 978425 = 733819) B733819
theorem B650747 : Blo 650305 650747 := bstep (se 1 (by rfl) ⟨488060, by rfl⟩ : syracuseStep 650747 = 976121) B976121
theorem B650815 : Blo 650305 650815 := bstep (se 1 (by rfl) ⟨488111, by rfl⟩ : syracuseStep 650815 = 976223) B976223
theorem B650823 : Blo 650305 650823 := bstep (se 1 (by rfl) ⟨488117, by rfl⟩ : syracuseStep 650823 = 976235) B976235
theorem B978527 : Blo 650305 978527 := bstep (se 1 (by rfl) ⟨733895, by rfl⟩ : syracuseStep 978527 = 1467791) B1467791
theorem B1470113 : Blo 650305 1470113 := bstep (se 2 (by rfl) ⟨551292, by rfl⟩ : syracuseStep 1470113 = 1102585) B1102585
theorem B650975 : Blo 650305 650975 := bstep (se 1 (by rfl) ⟨488231, by rfl⟩ : syracuseStep 650975 = 976463) B976463
theorem B880351 : Blo 650305 880351 := bstep (se 1 (by rfl) ⟨660263, by rfl⟩ : syracuseStep 880351 = 1320527) B1320527
theorem B651055 : Blo 650305 651055 := bstep (se 1 (by rfl) ⟨488291, by rfl⟩ : syracuseStep 651055 = 976583) B976583
theorem B978743 : Blo 650305 978743 := bstep (se 1 (by rfl) ⟨734057, by rfl⟩ : syracuseStep 978743 = 1468115) B1468115
theorem B1568567 : Blo 650305 1568567 := bstep (se 1 (by rfl) ⟨1176425, by rfl⟩ : syracuseStep 1568567 = 2352851) B2352851
theorem B651163 : Blo 650305 651163 := bstep (se 1 (by rfl) ⟨488372, by rfl⟩ : syracuseStep 651163 = 976745) B976745
theorem B651215 : Blo 650305 651215 := bstep (se 1 (by rfl) ⟨488411, by rfl⟩ : syracuseStep 651215 = 976823) B976823
theorem B651239 : Blo 650305 651239 := bstep (se 1 (by rfl) ⟨488429, by rfl⟩ : syracuseStep 651239 = 976859) B976859
theorem B1470473 : Blo 650305 1470473 := bstep (se 2 (by rfl) ⟨551427, by rfl⟩ : syracuseStep 1470473 = 1102855) B1102855
theorem B979049 : Blo 650305 979049 := bstep (se 2 (by rfl) ⟨367143, by rfl⟩ : syracuseStep 979049 = 734287) B734287
theorem B6353099 : Blo 650305 6353099 := bstep (se 1 (by rfl) ⟨4764824, by rfl⟩ : syracuseStep 6353099 = 9529649) B9529649
theorem B651551 : Blo 650305 651551 := bstep (se 1 (by rfl) ⟨488663, by rfl⟩ : syracuseStep 651551 = 977327) B977327
theorem B651611 : Blo 650305 651611 := bstep (se 1 (by rfl) ⟨488708, by rfl⟩ : syracuseStep 651611 = 977417) B977417
theorem B3338603 : Blo 650305 3338603 := bstep (se 1 (by rfl) ⟨2503952, by rfl⟩ : syracuseStep 3338603 = 5007905) B5007905
theorem B651631 : Blo 650305 651631 := bstep (se 1 (by rfl) ⟨488723, by rfl⟩ : syracuseStep 651631 = 977447) B977447
theorem B651687 : Blo 650305 651687 := bstep (se 1 (by rfl) ⟨488765, by rfl⟩ : syracuseStep 651687 = 977531) B977531
theorem B979367 : Blo 650305 979367 := bstep (se 1 (by rfl) ⟨734525, by rfl⟩ : syracuseStep 979367 = 1469051) B1469051
theorem B1470887 : Blo 650305 1470887 := bstep (se 1 (by rfl) ⟨1103165, by rfl⟩ : syracuseStep 1470887 = 2206331) B2206331
theorem B651771 : Blo 650305 651771 := bstep (se 1 (by rfl) ⟨488828, by rfl⟩ : syracuseStep 651771 = 977657) B977657
theorem B979451 : Blo 650305 979451 := bstep (se 1 (by rfl) ⟨734588, by rfl⟩ : syracuseStep 979451 = 1469177) B1469177
theorem B5009939 : Blo 650305 5009939 := bstep (se 1 (by rfl) ⟨3757454, by rfl⟩ : syracuseStep 5009939 = 7514909) B7514909
theorem B1470995 : Blo 650305 1470995 := bstep (se 1 (by rfl) ⟨1103246, by rfl⟩ : syracuseStep 1470995 = 2206493) B2206493
theorem B6681149 : Blo 650305 6681149 := bstep (se 3 (by rfl) ⟨1252715, by rfl⟩ : syracuseStep 6681149 = 2505431) B2505431
theorem B651839 : Blo 650305 651839 := bstep (se 1 (by rfl) ⟨488879, by rfl⟩ : syracuseStep 651839 = 977759) B977759
theorem B651847 : Blo 650305 651847 := bstep (se 1 (by rfl) ⟨488885, by rfl⟩ : syracuseStep 651847 = 977771) B977771
theorem B1700423 : Blo 650305 1700423 := bstep (se 1 (by rfl) ⟨1275317, by rfl⟩ : syracuseStep 1700423 = 2550635) B2550635
theorem B1176137 : Blo 650305 1176137 := bstep (se 2 (by rfl) ⟨441051, by rfl⟩ : syracuseStep 1176137 = 882103) B882103
theorem B1471049 : Blo 650305 1471049 := bstep (se 2 (by rfl) ⟨551643, by rfl⟩ : syracuseStep 1471049 = 1103287) B1103287
theorem B979577 : Blo 650305 979577 := bstep (se 2 (by rfl) ⟨367341, by rfl⟩ : syracuseStep 979577 = 734683) B734683
theorem B979631 : Blo 650305 979631 := bstep (se 1 (by rfl) ⟨734723, by rfl⟩ : syracuseStep 979631 = 1469447) B1469447
theorem B2716343 : Blo 650305 2716343 := bstep (se 1 (by rfl) ⟨2037257, by rfl⟩ : syracuseStep 2716343 = 4074515) B4074515
theorem B651999 : Blo 650305 651999 := bstep (se 1 (by rfl) ⟨488999, by rfl⟩ : syracuseStep 651999 = 977999) B977999
theorem B979679 : Blo 650305 979679 := bstep (se 1 (by rfl) ⟨734759, by rfl⟩ : syracuseStep 979679 = 1469519) B1469519
theorem B652079 : Blo 650305 652079 := bstep (se 1 (by rfl) ⟨489059, by rfl⟩ : syracuseStep 652079 = 978119) B978119
theorem B1045327 : Blo 650305 1045327 := bstep (se 1 (by rfl) ⟨783995, by rfl⟩ : syracuseStep 1045327 = 1567991) B1567991
theorem B652187 : Blo 650305 652187 := bstep (se 1 (by rfl) ⟨489140, by rfl⟩ : syracuseStep 652187 = 978281) B978281
theorem B652239 : Blo 650305 652239 := bstep (se 1 (by rfl) ⟨489179, by rfl⟩ : syracuseStep 652239 = 978359) B978359
theorem B652263 : Blo 650305 652263 := bstep (se 1 (by rfl) ⟨489197, by rfl⟩ : syracuseStep 652263 = 978395) B978395
theorem B979943 : Blo 650305 979943 := bstep (se 1 (by rfl) ⟨734957, by rfl⟩ : syracuseStep 979943 = 1469915) B1469915
theorem B1471463 : Blo 650305 1471463 := bstep (se 1 (by rfl) ⟨1103597, by rfl⟩ : syracuseStep 1471463 = 2207195) B2207195
theorem B980201 : Blo 650305 980201 := bstep (se 2 (by rfl) ⟨367575, by rfl⟩ : syracuseStep 980201 = 735151) B735151
theorem B652575 : Blo 650305 652575 := bstep (se 1 (by rfl) ⟨489431, by rfl⟩ : syracuseStep 652575 = 978863) B978863
theorem B980255 : Blo 650305 980255 := bstep (se 1 (by rfl) ⟨735191, by rfl⟩ : syracuseStep 980255 = 1470383) B1470383
theorem B4781351 : Blo 650305 4781351 := bstep (se 1 (by rfl) ⟨3586013, by rfl⟩ : syracuseStep 4781351 = 7172027) B7172027
theorem B652635 : Blo 650305 652635 := bstep (se 1 (by rfl) ⟨489476, by rfl⟩ : syracuseStep 652635 = 978953) B978953
theorem B1471841 : Blo 650305 1471841 := bstep (se 2 (by rfl) ⟨551940, by rfl⟩ : syracuseStep 1471841 = 1103881) B1103881
theorem B652655 : Blo 650305 652655 := bstep (se 1 (by rfl) ⟨489491, by rfl⟩ : syracuseStep 652655 = 978983) B978983
theorem B652711 : Blo 650305 652711 := bstep (se 1 (by rfl) ⟨489533, by rfl⟩ : syracuseStep 652711 = 979067) B979067
theorem B1471931 : Blo 650305 1471931 := bstep (se 1 (by rfl) ⟨1103948, by rfl⟩ : syracuseStep 1471931 = 2207897) B2207897
theorem B4453825 : Blo 650305 4453825 := bstep (se 2 (by rfl) ⟨1670184, by rfl⟩ : syracuseStep 4453825 = 3340369) B3340369
theorem B1177031 : Blo 650305 1177031 := bstep (se 1 (by rfl) ⟨882773, by rfl⟩ : syracuseStep 1177031 = 1765547) B1765547
theorem B980423 : Blo 650305 980423 := bstep (se 1 (by rfl) ⟨735317, by rfl⟩ : syracuseStep 980423 = 1470635) B1470635
theorem B652795 : Blo 650305 652795 := bstep (se 1 (by rfl) ⟨489596, by rfl⟩ : syracuseStep 652795 = 979193) B979193
theorem B1472057 : Blo 650305 1472057 := bstep (se 2 (by rfl) ⟨552021, by rfl⟩ : syracuseStep 1472057 = 1104043) B1104043
theorem B652863 : Blo 650305 652863 := bstep (se 1 (by rfl) ⟨489647, by rfl⟩ : syracuseStep 652863 = 979295) B979295
theorem B652871 : Blo 650305 652871 := bstep (se 1 (by rfl) ⟨489653, by rfl⟩ : syracuseStep 652871 = 979307) B979307
theorem B653023 : Blo 650305 653023 := bstep (se 1 (by rfl) ⟨489767, by rfl⟩ : syracuseStep 653023 = 979535) B979535
theorem B980777 : Blo 650305 980777 := bstep (se 2 (by rfl) ⟨367791, by rfl⟩ : syracuseStep 980777 = 735583) B735583
theorem B653103 : Blo 650305 653103 := bstep (se 1 (by rfl) ⟨489827, by rfl⟩ : syracuseStep 653103 = 979655) B979655
theorem B980783 : Blo 650305 980783 := bstep (se 1 (by rfl) ⟨735587, by rfl⟩ : syracuseStep 980783 = 1471175) B1471175
theorem B7141175 : Blo 650305 7141175 := bstep (se 1 (by rfl) ⟨5355881, by rfl⟩ : syracuseStep 7141175 = 10711763) B10711763
theorem B653211 : Blo 650305 653211 := bstep (se 1 (by rfl) ⟨489908, by rfl⟩ : syracuseStep 653211 = 979817) B979817
theorem B7927739 : Blo 650305 7927739 := bstep (se 1 (by rfl) ⟨5945804, by rfl⟩ : syracuseStep 7927739 = 11891609) B11891609
theorem B653263 : Blo 650305 653263 := bstep (se 1 (by rfl) ⟨489947, by rfl⟩ : syracuseStep 653263 = 979895) B979895
theorem B653287 : Blo 650305 653287 := bstep (se 1 (by rfl) ⟨489965, by rfl⟩ : syracuseStep 653287 = 979931) B979931
theorem B3307553 : Blo 650305 3307553 := bstep (se 2 (by rfl) ⟨1240332, by rfl⟩ : syracuseStep 3307553 = 2480665) B2480665
theorem B4225159 : Blo 650305 4225159 := bstep (se 1 (by rfl) ⟨3168869, by rfl⟩ : syracuseStep 4225159 = 6337739) B6337739
theorem B3307715 : Blo 650305 3307715 := bstep (se 1 (by rfl) ⟨2480786, by rfl⟩ : syracuseStep 3307715 = 4961573) B4961573
theorem B981257 : Blo 650305 981257 := bstep (se 2 (by rfl) ⟨367971, by rfl⟩ : syracuseStep 981257 = 735943) B735943
theorem B653599 : Blo 650305 653599 := bstep (se 1 (by rfl) ⟨490199, by rfl⟩ : syracuseStep 653599 = 980399) B980399
theorem B653659 : Blo 650305 653659 := bstep (se 1 (by rfl) ⟨490244, by rfl⟩ : syracuseStep 653659 = 980489) B980489
theorem B653679 : Blo 650305 653679 := bstep (se 1 (by rfl) ⟨490259, by rfl⟩ : syracuseStep 653679 = 980519) B980519
theorem B981359 : Blo 650305 981359 := bstep (se 1 (by rfl) ⟨736019, by rfl⟩ : syracuseStep 981359 = 1472039) B1472039
theorem B653735 : Blo 650305 653735 := bstep (se 1 (by rfl) ⟨490301, by rfl⟩ : syracuseStep 653735 = 980603) B980603
theorem B1505719 : Blo 650305 1505719 := bstep (se 1 (by rfl) ⟨1129289, by rfl⟩ : syracuseStep 1505719 = 2258579) B2258579
theorem B14088653 : Blo 650305 14088653 := bstep (se 3 (by rfl) ⟨2641622, by rfl⟩ : syracuseStep 14088653 = 5283245) B5283245
theorem B653819 : Blo 650305 653819 := bstep (se 1 (by rfl) ⟨490364, by rfl⟩ : syracuseStep 653819 = 980729) B980729
theorem B653887 : Blo 650305 653887 := bstep (se 1 (by rfl) ⟨490415, by rfl⟩ : syracuseStep 653887 = 980831) B980831
theorem B883271 : Blo 650305 883271 := bstep (se 1 (by rfl) ⟨662453, by rfl⟩ : syracuseStep 883271 = 1324907) B1324907
theorem B653895 : Blo 650305 653895 := bstep (se 1 (by rfl) ⟨490421, by rfl⟩ : syracuseStep 653895 = 980843) B980843
theorem B654047 : Blo 650305 654047 := bstep (se 1 (by rfl) ⟨490535, by rfl⟩ : syracuseStep 654047 = 981071) B981071
theorem B654127 : Blo 650305 654127 := bstep (se 1 (by rfl) ⟨490595, by rfl⟩ : syracuseStep 654127 = 981191) B981191
theorem B654235 : Blo 650305 654235 := bstep (se 1 (by rfl) ⟨490676, by rfl⟩ : syracuseStep 654235 = 981353) B981353
theorem B1047467 : Blo 650305 1047467 := bstep (se 1 (by rfl) ⟨785600, by rfl⟩ : syracuseStep 1047467 = 1571201) B1571201
theorem B654287 : Blo 650305 654287 := bstep (se 1 (by rfl) ⟨490715, by rfl⟩ : syracuseStep 654287 = 981431) B981431
theorem B1571815 : Blo 650305 1571815 := bstep (se 1 (by rfl) ⟨1178861, by rfl⟩ : syracuseStep 1571815 = 2357723) B2357723
theorem B2194937 : Blo 650305 2194937 := bstep (se 2 (by rfl) ⟨823101, by rfl⟩ : syracuseStep 2194937 = 1646203) B1646203
theorem B4947479 : Blo 650305 4947479 := bstep (se 1 (by rfl) ⟨3710609, by rfl⟩ : syracuseStep 4947479 = 7421219) B7421219
theorem B2195207 : Blo 650305 2195207 := bstep (se 1 (by rfl) ⟨1646405, by rfl⟩ : syracuseStep 2195207 = 3292811) B3292811
theorem B2195261 : Blo 650305 2195261 := bstep (se 3 (by rfl) ⟨411611, by rfl⟩ : syracuseStep 2195261 = 823223) B823223
theorem B2195963 : Blo 650305 2195963 := bstep (se 1 (by rfl) ⟨1646972, by rfl⟩ : syracuseStep 2195963 = 3293945) B3293945
theorem B60293645 : Blo 650305 60293645 := bstep (se 3 (by rfl) ⟨11305058, by rfl⟩ : syracuseStep 60293645 = 22610117) B22610117
theorem B2196233 : Blo 650305 2196233 := bstep (se 2 (by rfl) ⟨823587, by rfl⟩ : syracuseStep 2196233 = 1647175) B1647175
theorem B2229049 : Blo 650305 2229049 := bstep (se 2 (by rfl) ⟨835893, by rfl⟩ : syracuseStep 2229049 = 1671787) B1671787
theorem B4948937 : Blo 650305 4948937 := bstep (se 2 (by rfl) ⟨1855851, by rfl⟩ : syracuseStep 4948937 = 3711703) B3711703
theorem B5276663 : Blo 650305 5276663 := bstep (se 1 (by rfl) ⟨3957497, by rfl⟩ : syracuseStep 5276663 = 7914995) B7914995
theorem B63374339 : Blo 650305 63374339 := bstep (se 1 (by rfl) ⟨47530754, by rfl⟩ : syracuseStep 63374339 = 95061509) B95061509
theorem B3703913 : Blo 650305 3703913 := bstep (se 2 (by rfl) ⟨1388967, by rfl⟩ : syracuseStep 3703913 = 2777935) B2777935
theorem B2786633 : Blo 650305 2786633 := bstep (se 2 (by rfl) ⟨1044987, by rfl⟩ : syracuseStep 2786633 = 2089975) B2089975
theorem B5571929 : Blo 650305 5571929 := bstep (se 2 (by rfl) ⟨2089473, by rfl⟩ : syracuseStep 5571929 = 4178947) B4178947
theorem B3966347 : Blo 650305 3966347 := bstep (se 1 (by rfl) ⟨2974760, by rfl⟩ : syracuseStep 3966347 = 5949521) B5949521
theorem B2196989 : Blo 650305 2196989 := bstep (se 3 (by rfl) ⟨411935, by rfl⟩ : syracuseStep 2196989 = 823871) B823871
theorem B11896415 : Blo 650305 11896415 := bstep (se 1 (by rfl) ⟨8922311, by rfl⟩ : syracuseStep 11896415 = 17844623) B17844623
theorem B8685683 : Blo 650305 8685683 := bstep (se 1 (by rfl) ⟨6514262, by rfl⟩ : syracuseStep 8685683 = 13028525) B13028525
theorem B2197799 : Blo 650305 2197799 := bstep (se 1 (by rfl) ⟨1648349, by rfl⟩ : syracuseStep 2197799 = 3296699) B3296699
theorem B7408097 : Blo 650305 7408097 := bstep (se 2 (by rfl) ⟨2778036, by rfl⟩ : syracuseStep 7408097 = 5556073) B5556073
theorem B3181025 : Blo 650305 3181025 := bstep (se 2 (by rfl) ⟨1192884, by rfl⟩ : syracuseStep 3181025 = 2385769) B2385769
theorem B7539479 : Blo 650305 7539479 := bstep (se 1 (by rfl) ⟨5654609, by rfl⟩ : syracuseStep 7539479 = 11309219) B11309219
theorem B1674361 : Blo 650305 1674361 := bstep (se 2 (by rfl) ⟨627885, by rfl⟩ : syracuseStep 1674361 = 1255771) B1255771
theorem B2198663 : Blo 650305 2198663 := bstep (se 1 (by rfl) ⟨1648997, by rfl⟩ : syracuseStep 2198663 = 3297995) B3297995
theorem B7441631 : Blo 650305 7441631 := bstep (se 1 (by rfl) ⟨5581223, by rfl⟩ : syracuseStep 7441631 = 11162447) B11162447
theorem B2198771 : Blo 650305 2198771 := bstep (se 1 (by rfl) ⟨1649078, by rfl⟩ : syracuseStep 2198771 = 3298157) B3298157
theorem B8064305 : Blo 650305 8064305 := bstep (se 2 (by rfl) ⟨3024114, by rfl⟩ : syracuseStep 8064305 = 6048229) B6048229
theorem B14290769 : Blo 650305 14290769 := bstep (se 2 (by rfl) ⟨5359038, by rfl⟩ : syracuseStep 14290769 = 10718077) B10718077
theorem B33952541 : Blo 650305 33952541 := bstep (se 3 (by rfl) ⟨6366101, by rfl⟩ : syracuseStep 33952541 = 12732203) B12732203
theorem B8360765 : Blo 650305 8360765 := bstep (se 3 (by rfl) ⟨1567643, by rfl⟩ : syracuseStep 8360765 = 3135287) B3135287
theorem B2200445 : Blo 650305 2200445 := bstep (se 3 (by rfl) ⟨412583, by rfl⟩ : syracuseStep 2200445 = 825167) B825167
theorem B2200715 : Blo 650305 2200715 := bstep (se 1 (by rfl) ⟨1650536, by rfl⟩ : syracuseStep 2200715 = 3301073) B3301073
theorem B7444547 : Blo 650305 7444547 := bstep (se 1 (by rfl) ⟨5583410, by rfl⟩ : syracuseStep 7444547 = 11166821) B11166821
theorem B4167875 : Blo 650305 4167875 := bstep (se 1 (by rfl) ⟨3125906, by rfl⟩ : syracuseStep 4167875 = 6251813) B6251813
theorem B14129477 : Blo 650305 14129477 := bstep (se 4 (by rfl) ⟨1324638, by rfl⟩ : syracuseStep 14129477 = 2649277) B2649277
theorem B2202335 : Blo 650305 2202335 := bstep (se 1 (by rfl) ⟨1651751, by rfl⟩ : syracuseStep 2202335 = 3303503) B3303503
theorem B7412471 : Blo 650305 7412471 := bstep (se 1 (by rfl) ⟨5559353, by rfl⟩ : syracuseStep 7412471 = 11118707) B11118707
theorem B3349561 : Blo 650305 3349561 := bstep (se 2 (by rfl) ⟨1256085, by rfl⟩ : syracuseStep 3349561 = 2512171) B2512171
theorem B5577943 : Blo 650305 5577943 := bstep (se 1 (by rfl) ⟨4183457, by rfl⟩ : syracuseStep 5577943 = 8366915) B8366915
theorem B2792663 : Blo 650305 2792663 := bstep (se 1 (by rfl) ⟨2094497, by rfl⟩ : syracuseStep 2792663 = 4188995) B4188995
theorem B5938433 : Blo 650305 5938433 := bstep (se 2 (by rfl) ⟨2226912, by rfl⟩ : syracuseStep 5938433 = 4453825) B4453825
theorem B2203091 : Blo 650305 2203091 := bstep (se 1 (by rfl) ⟨1652318, by rfl⟩ : syracuseStep 2203091 = 3304637) B3304637
theorem B2203361 : Blo 650305 2203361 := bstep (se 2 (by rfl) ⟨826260, by rfl⟩ : syracuseStep 2203361 = 1652521) B1652521
theorem B5644079 : Blo 650305 5644079 := bstep (se 1 (by rfl) ⟨4233059, by rfl⟩ : syracuseStep 5644079 = 8466119) B8466119
theorem B2236247 : Blo 650305 2236247 := bstep (se 1 (by rfl) ⟨1677185, by rfl⟩ : syracuseStep 2236247 = 3354371) B3354371
theorem B1646507 : Blo 650305 1646507 := bstep (se 1 (by rfl) ⟨1234880, by rfl⟩ : syracuseStep 1646507 = 2469761) B2469761
theorem B4235399 : Blo 650305 4235399 := bstep (se 1 (by rfl) ⟨3176549, by rfl⟩ : syracuseStep 4235399 = 6353099) B6353099
theorem B1810895 : Blo 650305 1810895 := bstep (se 1 (by rfl) ⟨1358171, by rfl⟩ : syracuseStep 1810895 = 2716343) B2716343
theorem B2007625 : Blo 650305 2007625 := bstep (se 2 (by rfl) ⟨752859, by rfl⟩ : syracuseStep 2007625 = 1505719) B1505719
theorem B3187567 : Blo 650305 3187567 := bstep (se 1 (by rfl) ⟨2390675, by rfl⟩ : syracuseStep 3187567 = 4781351) B4781351
theorem B2827163 : Blo 650305 2827163 := bstep (se 1 (by rfl) ⟨2120372, by rfl⟩ : syracuseStep 2827163 = 4240745) B4240745
theorem B1647641 : Blo 650305 1647641 := bstep (se 2 (by rfl) ⟨617865, by rfl⟩ : syracuseStep 1647641 = 1235731) B1235731
theorem B4695205 : Blo 650305 4695205 := bstep (se 4 (by rfl) ⟨440175, by rfl⟩ : syracuseStep 4695205 = 880351) B880351
theorem B1647823 : Blo 650305 1647823 := bstep (se 1 (by rfl) ⟨1235867, by rfl⟩ : syracuseStep 1647823 = 2471735) B2471735
theorem B4760783 : Blo 650305 4760783 := bstep (se 1 (by rfl) ⟨3570587, by rfl⟩ : syracuseStep 4760783 = 7141175) B7141175
theorem B5285159 : Blo 650305 5285159 := bstep (se 1 (by rfl) ⟨3963869, by rfl⟩ : syracuseStep 5285159 = 7927739) B7927739
theorem B2205035 : Blo 650305 2205035 := bstep (se 1 (by rfl) ⟨1653776, by rfl⟩ : syracuseStep 2205035 = 3307553) B3307553
theorem B2205143 : Blo 650305 2205143 := bstep (se 1 (by rfl) ⟨1653857, by rfl⟩ : syracuseStep 2205143 = 3307715) B3307715
theorem B1648147 : Blo 650305 1648147 := bstep (se 1 (by rfl) ⟨1236110, by rfl⟩ : syracuseStep 1648147 = 2472221) B2472221
theorem B2205305 : Blo 650305 2205305 := bstep (se 2 (by rfl) ⟨826989, by rfl⟩ : syracuseStep 2205305 = 1653979) B1653979
theorem B1648583 : Blo 650305 1648583 := bstep (se 1 (by rfl) ⟨1236437, by rfl⟩ : syracuseStep 1648583 = 2472875) B2472875
theorem B698311 : Blo 650305 698311 := bstep (se 1 (by rfl) ⟨523733, by rfl⟩ : syracuseStep 698311 = 1047467) B1047467
theorem B1321273 : Blo 650305 1321273 := bstep (se 2 (by rfl) ⟨495477, by rfl⟩ : syracuseStep 1321273 = 990955) B990955
theorem B7448921 : Blo 650305 7448921 := bstep (se 2 (by rfl) ⟨2793345, by rfl⟩ : syracuseStep 7448921 = 5586691) B5586691
theorem B2206817 : Blo 650305 2206817 := bstep (se 2 (by rfl) ⟨827556, by rfl⟩ : syracuseStep 2206817 = 1655113) B1655113
theorem B2207357 : Blo 650305 2207357 := bstep (se 3 (by rfl) ⟨413879, by rfl⟩ : syracuseStep 2207357 = 827759) B827759
theorem B6205177 : Blo 650305 6205177 := bstep (se 2 (by rfl) ⟨2326941, by rfl⟩ : syracuseStep 6205177 = 4653883) B4653883
theorem B2207627 : Blo 650305 2207627 := bstep (se 1 (by rfl) ⟨1655720, by rfl⟩ : syracuseStep 2207627 = 3311441) B3311441
theorem B4173875 : Blo 650305 4173875 := bstep (se 1 (by rfl) ⟨3130406, by rfl⟩ : syracuseStep 4173875 = 6260813) B6260813
theorem B1487035 : Blo 650305 1487035 := bstep (se 1 (by rfl) ⟨1115276, by rfl⟩ : syracuseStep 1487035 = 2230553) B2230553
theorem B930079 : Blo 650305 930079 := bstep (se 1 (by rfl) ⟨697559, by rfl⟩ : syracuseStep 930079 = 1395119) B1395119
theorem B733567 : Blo 650305 733567 := bstep (se 1 (by rfl) ⟨550175, by rfl⟩ : syracuseStep 733567 = 1100351) B1100351
theorem B2208167 : Blo 650305 2208167 := bstep (se 1 (by rfl) ⟨1656125, by rfl⟩ : syracuseStep 2208167 = 3312251) B3312251
theorem B3715577 : Blo 650305 3715577 := bstep (se 2 (by rfl) ⟨1393341, by rfl⟩ : syracuseStep 3715577 = 2786683) B2786683
theorem B2011895 : Blo 650305 2011895 := bstep (se 1 (by rfl) ⟨1508921, by rfl⟩ : syracuseStep 2011895 = 3017843) B3017843
theorem B8926031 : Blo 650305 8926031 := bstep (se 1 (by rfl) ⟨6694523, by rfl⟩ : syracuseStep 8926031 = 13389047) B13389047
theorem B10564987 : Blo 650305 10564987 := bstep (se 1 (by rfl) ⟨7923740, by rfl⟩ : syracuseStep 10564987 = 15847481) B15847481
theorem B734971 : Blo 650305 734971 := bstep (se 1 (by rfl) ⟨551228, by rfl⟩ : syracuseStep 734971 = 1102457) B1102457
theorem B735007 : Blo 650305 735007 := bstep (se 1 (by rfl) ⟨551255, by rfl⟩ : syracuseStep 735007 = 1102511) B1102511
theorem B3717353 : Blo 650305 3717353 := bstep (se 2 (by rfl) ⟨1394007, by rfl⟩ : syracuseStep 3717353 = 2788015) B2788015
theorem B7912259 : Blo 650305 7912259 := bstep (se 1 (by rfl) ⟨5934194, by rfl⟩ : syracuseStep 7912259 = 11868389) B11868389
theorem B2112463 : Blo 650305 2112463 := bstep (se 1 (by rfl) ⟨1584347, by rfl⟩ : syracuseStep 2112463 = 3168695) B3168695
theorem B4177079 : Blo 650305 4177079 := bstep (se 1 (by rfl) ⟨3132809, by rfl⟩ : syracuseStep 4177079 = 6265619) B6265619
theorem B2637095 : Blo 650305 2637095 := bstep (se 1 (by rfl) ⟨1977821, by rfl⟩ : syracuseStep 2637095 = 3955643) B3955643
theorem B3128813 : Blo 650305 3128813 := bstep (se 3 (by rfl) ⟨586652, by rfl⟩ : syracuseStep 3128813 = 1173305) B1173305
theorem B1654415 : Blo 650305 1654415 := bstep (se 1 (by rfl) ⟨1240811, by rfl⟩ : syracuseStep 1654415 = 2481623) B2481623
theorem B4702009 : Blo 650305 4702009 := bstep (se 2 (by rfl) ⟨1763253, by rfl⟩ : syracuseStep 4702009 = 3526507) B3526507
theorem B1097543 : Blo 650305 1097543 := bstep (se 1 (by rfl) ⟨823157, by rfl⟩ : syracuseStep 1097543 = 1646315) B1646315
theorem B1491175 : Blo 650305 1491175 := bstep (se 1 (by rfl) ⟨1118381, by rfl⟩ : syracuseStep 1491175 = 2236763) B2236763
theorem B1098191 : Blo 650305 1098191 := bstep (se 1 (by rfl) ⟨823643, by rfl⟩ : syracuseStep 1098191 = 1647287) B1647287
theorem B1852139 : Blo 650305 1852139 := bstep (se 1 (by rfl) ⟨1389104, by rfl⟩ : syracuseStep 1852139 = 2778209) B2778209
theorem B1655599 : Blo 650305 1655599 := bstep (se 1 (by rfl) ⟨1241699, by rfl⟩ : syracuseStep 1655599 = 2483399) B2483399
theorem B5588027 : Blo 650305 5588027 := bstep (se 1 (by rfl) ⟨4191020, by rfl⟩ : syracuseStep 5588027 = 8382041) B8382041
theorem B1393769 : Blo 650305 1393769 := bstep (se 2 (by rfl) ⟨522663, by rfl⟩ : syracuseStep 1393769 = 1045327) B1045327
theorem B1098859 : Blo 650305 1098859 := bstep (se 1 (by rfl) ⟨824144, by rfl⟩ : syracuseStep 1098859 = 1648289) B1648289
theorem B4703453 : Blo 650305 4703453 := bstep (se 3 (by rfl) ⟨881897, by rfl⟩ : syracuseStep 4703453 = 1763795) B1763795
theorem B3720451 : Blo 650305 3720451 := bstep (se 1 (by rfl) ⟨2790338, by rfl⟩ : syracuseStep 3720451 = 5580677) B5580677
theorem B1099163 : Blo 650305 1099163 := bstep (se 1 (by rfl) ⟨824372, by rfl⟩ : syracuseStep 1099163 = 1648745) B1648745
theorem B3524257 : Blo 650305 3524257 := bstep (se 2 (by rfl) ⟨1321596, by rfl⟩ : syracuseStep 3524257 = 2643193) B2643193
theorem B1099487 : Blo 650305 1099487 := bstep (se 1 (by rfl) ⟨824615, by rfl⟩ : syracuseStep 1099487 = 1649231) B1649231
theorem B3524431 : Blo 650305 3524431 := bstep (se 1 (by rfl) ⟨2643323, by rfl⟩ : syracuseStep 3524431 = 5286647) B5286647
theorem B3295241 : Blo 650305 3295241 := bstep (se 2 (by rfl) ⟨1235715, by rfl⟩ : syracuseStep 3295241 = 2471431) B2471431
theorem B1099919 : Blo 650305 1099919 := bstep (se 1 (by rfl) ⟨824939, by rfl⟩ : syracuseStep 1099919 = 1649879) B1649879
theorem B4180177 : Blo 650305 4180177 := bstep (se 2 (by rfl) ⟨1567566, by rfl⟩ : syracuseStep 4180177 = 3135133) B3135133
theorem B1100155 : Blo 650305 1100155 := bstep (se 1 (by rfl) ⟨825116, by rfl⟩ : syracuseStep 1100155 = 1650233) B1650233
theorem B4966919 : Blo 650305 4966919 := bstep (se 1 (by rfl) ⟨3725189, by rfl⟩ : syracuseStep 4966919 = 7450379) B7450379
theorem B1100425 : Blo 650305 1100425 := bstep (se 2 (by rfl) ⟨412659, by rfl⟩ : syracuseStep 1100425 = 825319) B825319
theorem B3295889 : Blo 650305 3295889 := bstep (se 2 (by rfl) ⟨1235958, by rfl⟩ : syracuseStep 3295889 = 2471917) B2471917
theorem B1886903 : Blo 650305 1886903 := bstep (se 1 (by rfl) ⟨1415177, by rfl⟩ : syracuseStep 1886903 = 2830355) B2830355
theorem B1133615 : Blo 650305 1133615 := bstep (se 1 (by rfl) ⟨850211, by rfl⟩ : syracuseStep 1133615 = 1700423) B1700423
theorem B3296537 : Blo 650305 3296537 := bstep (se 2 (by rfl) ⟨1236201, by rfl⟩ : syracuseStep 3296537 = 2472403) B2472403
theorem B1888379 : Blo 650305 1888379 := bstep (se 1 (by rfl) ⟨1416284, by rfl⟩ : syracuseStep 1888379 = 2832569) B2832569
theorem B8147249 : Blo 650305 8147249 := bstep (se 2 (by rfl) ⟨3055218, by rfl⟩ : syracuseStep 8147249 = 6110437) B6110437
theorem B9392435 : Blo 650305 9392435 := bstep (se 1 (by rfl) ⟨7044326, by rfl⟩ : syracuseStep 9392435 = 14088653) B14088653
theorem B1102207 : Blo 650305 1102207 := bstep (se 1 (by rfl) ⟨826655, by rfl⟩ : syracuseStep 1102207 = 1653311) B1653311
theorem B2478707 : Blo 650305 2478707 := bstep (se 1 (by rfl) ⟨1859030, by rfl⟩ : syracuseStep 2478707 = 3718061) B3718061
theorem B1856297 : Blo 650305 1856297 := bstep (se 2 (by rfl) ⟨696111, by rfl⟩ : syracuseStep 1856297 = 1392223) B1392223
theorem B1102639 : Blo 650305 1102639 := bstep (se 1 (by rfl) ⟨826979, by rfl⟩ : syracuseStep 1102639 = 1653959) B1653959
theorem B1463291 : Blo 650305 1463291 := bstep (se 1 (by rfl) ⟨1097468, by rfl⟩ : syracuseStep 1463291 = 2194937) B2194937
theorem B3298319 : Blo 650305 3298319 := bstep (se 1 (by rfl) ⟨2473739, by rfl⟩ : syracuseStep 3298319 = 4947479) B4947479
theorem B1463471 : Blo 650305 1463471 := bstep (se 1 (by rfl) ⟨1097603, by rfl⟩ : syracuseStep 1463471 = 2195207) B2195207
theorem B1463507 : Blo 650305 1463507 := bstep (se 1 (by rfl) ⟨1097630, by rfl⟩ : syracuseStep 1463507 = 2195261) B2195261
theorem B8377577 : Blo 650305 8377577 := bstep (se 2 (by rfl) ⟨3141591, by rfl⟩ : syracuseStep 8377577 = 6283183) B6283183
theorem B23811509 : Blo 650305 23811509 := bstep (se 5 (by rfl) ⟨1116164, by rfl⟩ : syracuseStep 23811509 = 2232329) B2232329
theorem B1463777 : Blo 650305 1463777 := bstep (se 2 (by rfl) ⟨548916, by rfl⟩ : syracuseStep 1463777 = 1097833) B1097833
theorem B1234615 : Blo 650305 1234615 := bstep (se 1 (by rfl) ⟨925961, by rfl⟩ : syracuseStep 1234615 = 1851923) B1851923
theorem B1103611 : Blo 650305 1103611 := bstep (se 1 (by rfl) ⟨827708, by rfl⟩ : syracuseStep 1103611 = 1655417) B1655417
theorem B3299129 : Blo 650305 3299129 := bstep (se 2 (by rfl) ⟨1237173, by rfl⟩ : syracuseStep 3299129 = 2474347) B2474347
theorem B1103753 : Blo 650305 1103753 := bstep (se 2 (by rfl) ⟨413907, by rfl⟩ : syracuseStep 1103753 = 827815) B827815
theorem B15849431 : Blo 650305 15849431 := bstep (se 1 (by rfl) ⟨11887073, by rfl⟩ : syracuseStep 15849431 = 23774147) B23774147
theorem B1234919 : Blo 650305 1234919 := bstep (se 1 (by rfl) ⟨926189, by rfl⟩ : syracuseStep 1234919 = 1852379) B1852379
theorem B2349161 : Blo 650305 2349161 := bstep (se 2 (by rfl) ⟨880935, by rfl⟩ : syracuseStep 2349161 = 1761871) B1761871
theorem B3136097 : Blo 650305 3136097 := bstep (se 2 (by rfl) ⟨1176036, by rfl⟩ : syracuseStep 3136097 = 2352073) B2352073
theorem B18766511 : Blo 650305 18766511 := bstep (se 1 (by rfl) ⟨14074883, by rfl⟩ : syracuseStep 18766511 = 28149767) B28149767
theorem B104225753 : Blo 650305 104225753 := bstep (se 2 (by rfl) ⟨39084657, by rfl⟩ : syracuseStep 104225753 = 78169315) B78169315
theorem B1465415 : Blo 650305 1465415 := bstep (se 1 (by rfl) ⟨1099061, by rfl⟩ : syracuseStep 1465415 = 2198123) B2198123
theorem B4021433 : Blo 650305 4021433 := bstep (se 2 (by rfl) ⟨1508037, by rfl⟩ : syracuseStep 4021433 = 3016075) B3016075
theorem B2645207 : Blo 650305 2645207 := bstep (se 1 (by rfl) ⟨1983905, by rfl⟩ : syracuseStep 2645207 = 3967811) B3967811
theorem B1465811 : Blo 650305 1465811 := bstep (se 1 (by rfl) ⟨1099358, by rfl⟩ : syracuseStep 1465811 = 2198717) B2198717
theorem B941743 : Blo 650305 941743 := bstep (se 1 (by rfl) ⟨706307, by rfl⟩ : syracuseStep 941743 = 1412615) B1412615
theorem B1466081 : Blo 650305 1466081 := bstep (se 2 (by rfl) ⟨549780, by rfl⟩ : syracuseStep 1466081 = 1099561) B1099561
theorem B2482109 : Blo 650305 2482109 := bstep (se 3 (by rfl) ⟨465395, by rfl⟩ : syracuseStep 2482109 = 930791) B930791
theorem B1237447 : Blo 650305 1237447 := bstep (se 1 (by rfl) ⟨928085, by rfl⟩ : syracuseStep 1237447 = 1856171) B1856171
theorem B4710889 : Blo 650305 4710889 := bstep (se 2 (by rfl) ⟨1766583, by rfl⟩ : syracuseStep 4710889 = 3533167) B3533167
theorem B2352187 : Blo 650305 2352187 := bstep (se 1 (by rfl) ⟨1764140, by rfl⟩ : syracuseStep 2352187 = 3528281) B3528281
theorem B975935 : Blo 650305 975935 := bstep (se 1 (by rfl) ⟨731951, by rfl⟩ : syracuseStep 975935 = 1463903) B1463903
theorem B975977 : Blo 650305 975977 := bstep (se 2 (by rfl) ⟨365991, by rfl⟩ : syracuseStep 975977 = 731983) B731983
theorem B3138749 : Blo 650305 3138749 := bstep (se 3 (by rfl) ⟨588515, by rfl⟩ : syracuseStep 3138749 = 1177031) B1177031
theorem B976079 : Blo 650305 976079 := bstep (se 1 (by rfl) ⟨732059, by rfl⟩ : syracuseStep 976079 = 1464119) B1464119
theorem B4941161 : Blo 650305 4941161 := bstep (se 2 (by rfl) ⟨1852935, by rfl⟩ : syracuseStep 4941161 = 3705871) B3705871
theorem B1467755 : Blo 650305 1467755 := bstep (se 1 (by rfl) ⟨1100816, by rfl⟩ : syracuseStep 1467755 = 2201633) B2201633
theorem B1861001 : Blo 650305 1861001 := bstep (se 2 (by rfl) ⟨697875, by rfl⟩ : syracuseStep 1861001 = 1395751) B1395751
theorem B976283 : Blo 650305 976283 := bstep (se 1 (by rfl) ⟨732212, by rfl⟩ : syracuseStep 976283 = 1464425) B1464425
theorem B976505 : Blo 650305 976505 := bstep (se 2 (by rfl) ⟨366189, by rfl⟩ : syracuseStep 976505 = 732379) B732379
theorem B1468025 : Blo 650305 1468025 := bstep (se 2 (by rfl) ⟨550509, by rfl⟩ : syracuseStep 1468025 = 1101019) B1101019
theorem B2647673 : Blo 650305 2647673 := bstep (se 2 (by rfl) ⟨992877, by rfl⟩ : syracuseStep 2647673 = 1985755) B1985755
theorem B976607 : Blo 650305 976607 := bstep (se 1 (by rfl) ⟨732455, by rfl⟩ : syracuseStep 976607 = 1464911) B1464911
theorem B1861343 : Blo 650305 1861343 := bstep (se 1 (by rfl) ⟨1396007, by rfl⟩ : syracuseStep 1861343 = 2792015) B2792015
theorem B976703 : Blo 650305 976703 := bstep (se 1 (by rfl) ⟨732527, by rfl⟩ : syracuseStep 976703 = 1465055) B1465055
theorem B976871 : Blo 650305 976871 := bstep (se 1 (by rfl) ⟨732653, by rfl⟩ : syracuseStep 976871 = 1465307) B1465307
theorem B976889 : Blo 650305 976889 := bstep (se 2 (by rfl) ⟨366333, by rfl⟩ : syracuseStep 976889 = 732667) B732667
theorem B976991 : Blo 650305 976991 := bstep (se 1 (by rfl) ⟨732743, by rfl⟩ : syracuseStep 976991 = 1465487) B1465487
theorem B2517101 : Blo 650305 2517101 := bstep (se 3 (by rfl) ⟨471956, by rfl⟩ : syracuseStep 2517101 = 943913) B943913
theorem B6711443 : Blo 650305 6711443 := bstep (se 1 (by rfl) ⟨5033582, by rfl⟩ : syracuseStep 6711443 = 10067165) B10067165
theorem B977051 : Blo 650305 977051 := bstep (se 1 (by rfl) ⟨732788, by rfl⟩ : syracuseStep 977051 = 1465577) B1465577
theorem B977087 : Blo 650305 977087 := bstep (se 1 (by rfl) ⟨732815, by rfl⟩ : syracuseStep 977087 = 1465631) B1465631
theorem B977129 : Blo 650305 977129 := bstep (se 2 (by rfl) ⟨366423, by rfl⟩ : syracuseStep 977129 = 732847) B732847
theorem B18770201 : Blo 650305 18770201 := bstep (se 2 (by rfl) ⟨7038825, by rfl⟩ : syracuseStep 18770201 = 14077651) B14077651
theorem B977435 : Blo 650305 977435 := bstep (se 1 (by rfl) ⟨733076, by rfl⟩ : syracuseStep 977435 = 1466153) B1466153
theorem B8383013 : Blo 650305 8383013 := bstep (se 4 (by rfl) ⟨785907, by rfl⟩ : syracuseStep 8383013 = 1571815) B1571815
theorem B977513 : Blo 650305 977513 := bstep (se 2 (by rfl) ⟨366567, by rfl⟩ : syracuseStep 977513 = 733135) B733135
theorem B1469033 : Blo 650305 1469033 := bstep (se 2 (by rfl) ⟨550887, by rfl⟩ : syracuseStep 1469033 = 1101775) B1101775
theorem B6974351 : Blo 650305 6974351 := bstep (se 1 (by rfl) ⟨5230763, by rfl⟩ : syracuseStep 6974351 = 10461527) B10461527
theorem B5303225 : Blo 650305 5303225 := bstep (se 2 (by rfl) ⟨1988709, by rfl⟩ : syracuseStep 5303225 = 3977419) B3977419
theorem B650311 : Blo 650305 650311 := bstep (se 1 (by rfl) ⟨487733, by rfl⟩ : syracuseStep 650311 = 975467) B975467
theorem B978041 : Blo 650305 978041 := bstep (se 2 (by rfl) ⟨366765, by rfl⟩ : syracuseStep 978041 = 733531) B733531
theorem B1862777 : Blo 650305 1862777 := bstep (se 2 (by rfl) ⟨698541, by rfl⟩ : syracuseStep 1862777 = 1397083) B1397083
theorem B650463 : Blo 650305 650463 := bstep (se 1 (by rfl) ⟨487847, by rfl⟩ : syracuseStep 650463 = 975695) B975695
theorem B781535 : Blo 650305 781535 := bstep (se 1 (by rfl) ⟨586151, by rfl⟩ : syracuseStep 781535 = 1172303) B1172303
theorem B978143 : Blo 650305 978143 := bstep (se 1 (by rfl) ⟨733607, by rfl⟩ : syracuseStep 978143 = 1467215) B1467215
theorem B1469663 : Blo 650305 1469663 := bstep (se 1 (by rfl) ⟨1102247, by rfl⟩ : syracuseStep 1469663 = 2204495) B2204495
theorem B2387177 : Blo 650305 2387177 := bstep (se 2 (by rfl) ⟨895191, by rfl⟩ : syracuseStep 2387177 = 1790383) B1790383
theorem B978185 : Blo 650305 978185 := bstep (se 2 (by rfl) ⟨366819, by rfl⟩ : syracuseStep 978185 = 733639) B733639
theorem B3566891 : Blo 650305 3566891 := bstep (se 1 (by rfl) ⟨2675168, by rfl⟩ : syracuseStep 3566891 = 5350337) B5350337
theorem B978287 : Blo 650305 978287 := bstep (se 1 (by rfl) ⟨733715, by rfl⟩ : syracuseStep 978287 = 1467431) B1467431
theorem B1469879 : Blo 650305 1469879 := bstep (se 1 (by rfl) ⟨1102409, by rfl⟩ : syracuseStep 1469879 = 2204819) B2204819
theorem B650727 : Blo 650305 650727 := bstep (se 1 (by rfl) ⟨488045, by rfl⟩ : syracuseStep 650727 = 976091) B976091
theorem B978407 : Blo 650305 978407 := bstep (se 1 (by rfl) ⟨733805, by rfl⟩ : syracuseStep 978407 = 1467611) B1467611
theorem B650843 : Blo 650305 650843 := bstep (se 1 (by rfl) ⟨488132, by rfl⟩ : syracuseStep 650843 = 976265) B976265
theorem B978539 : Blo 650305 978539 := bstep (se 1 (by rfl) ⟨733904, by rfl⟩ : syracuseStep 978539 = 1467809) B1467809
theorem B1470059 : Blo 650305 1470059 := bstep (se 1 (by rfl) ⟨1102544, by rfl⟩ : syracuseStep 1470059 = 2205089) B2205089
theorem B1240751 : Blo 650305 1240751 := bstep (se 1 (by rfl) ⟨930563, by rfl⟩ : syracuseStep 1240751 = 1861127) B1861127
theorem B978665 : Blo 650305 978665 := bstep (se 2 (by rfl) ⟨366999, by rfl⟩ : syracuseStep 978665 = 733999) B733999
theorem B651079 : Blo 650305 651079 := bstep (se 1 (by rfl) ⟨488309, by rfl⟩ : syracuseStep 651079 = 976619) B976619
theorem B978809 : Blo 650305 978809 := bstep (se 2 (by rfl) ⟨367053, by rfl⟩ : syracuseStep 978809 = 734107) B734107
theorem B1470329 : Blo 650305 1470329 := bstep (se 2 (by rfl) ⟨551373, by rfl⟩ : syracuseStep 1470329 = 1102747) B1102747
theorem B651231 : Blo 650305 651231 := bstep (se 1 (by rfl) ⟨488423, by rfl⟩ : syracuseStep 651231 = 976847) B976847
theorem B978911 : Blo 650305 978911 := bstep (se 1 (by rfl) ⟨734183, by rfl⟩ : syracuseStep 978911 = 1468367) B1468367
theorem B2355389 : Blo 650305 2355389 := bstep (se 3 (by rfl) ⟨441635, by rfl⟩ : syracuseStep 2355389 = 883271) B883271
theorem B979163 : Blo 650305 979163 := bstep (se 1 (by rfl) ⟨734372, by rfl⟩ : syracuseStep 979163 = 1468745) B1468745
theorem B651495 : Blo 650305 651495 := bstep (se 1 (by rfl) ⟨488621, by rfl⟩ : syracuseStep 651495 = 977243) B977243
theorem B979175 : Blo 650305 979175 := bstep (se 1 (by rfl) ⟨734381, by rfl⟩ : syracuseStep 979175 = 1468763) B1468763
theorem B651647 : Blo 650305 651647 := bstep (se 1 (by rfl) ⟨488735, by rfl⟩ : syracuseStep 651647 = 977471) B977471
theorem B979337 : Blo 650305 979337 := bstep (se 2 (by rfl) ⟨367251, by rfl⟩ : syracuseStep 979337 = 734503) B734503
theorem B651727 : Blo 650305 651727 := bstep (se 1 (by rfl) ⟨488795, by rfl⟩ : syracuseStep 651727 = 977591) B977591
theorem B979433 : Blo 650305 979433 := bstep (se 2 (by rfl) ⟨367287, by rfl⟩ : syracuseStep 979433 = 734575) B734575
theorem B651879 : Blo 650305 651879 := bstep (se 1 (by rfl) ⟨488909, by rfl⟩ : syracuseStep 651879 = 977819) B977819
theorem B979559 : Blo 650305 979559 := bstep (se 1 (by rfl) ⟨734669, by rfl⟩ : syracuseStep 979559 = 1469339) B1469339
theorem B12514013 : Blo 650305 12514013 := bstep (se 3 (by rfl) ⟨2346377, by rfl⟩ : syracuseStep 12514013 = 4692755) B4692755
theorem B979691 : Blo 650305 979691 := bstep (se 1 (by rfl) ⟨734768, by rfl⟩ : syracuseStep 979691 = 1469537) B1469537
theorem B979721 : Blo 650305 979721 := bstep (se 2 (by rfl) ⟨367395, by rfl⟩ : syracuseStep 979721 = 734791) B734791
theorem B1176367 : Blo 650305 1176367 := bstep (se 1 (by rfl) ⟨882275, by rfl⟩ : syracuseStep 1176367 = 1764551) B1764551
theorem B652143 : Blo 650305 652143 := bstep (se 1 (by rfl) ⟨489107, by rfl⟩ : syracuseStep 652143 = 978215) B978215
theorem B979823 : Blo 650305 979823 := bstep (se 1 (by rfl) ⟨734867, by rfl⟩ : syracuseStep 979823 = 1469735) B1469735
theorem B652199 : Blo 650305 652199 := bstep (se 1 (by rfl) ⟨489149, by rfl⟩ : syracuseStep 652199 = 978299) B978299
theorem B652283 : Blo 650305 652283 := bstep (se 1 (by rfl) ⟨489212, by rfl⟩ : syracuseStep 652283 = 978425) B978425
theorem B652351 : Blo 650305 652351 := bstep (se 1 (by rfl) ⟨489263, by rfl⟩ : syracuseStep 652351 = 978527) B978527
theorem B980075 : Blo 650305 980075 := bstep (se 1 (by rfl) ⟨735056, by rfl⟩ : syracuseStep 980075 = 1470113) B1470113
theorem B8909941 : Blo 650305 8909941 := bstep (se 5 (by rfl) ⟨417653, by rfl⟩ : syracuseStep 8909941 = 835307) B835307
theorem B652495 : Blo 650305 652495 := bstep (se 1 (by rfl) ⟨489371, by rfl⟩ : syracuseStep 652495 = 978743) B978743
theorem B1045711 : Blo 650305 1045711 := bstep (se 1 (by rfl) ⟨784283, by rfl⟩ : syracuseStep 1045711 = 1568567) B1568567
theorem B3765491 : Blo 650305 3765491 := bstep (se 1 (by rfl) ⟨2824118, by rfl⟩ : syracuseStep 3765491 = 5648237) B5648237
theorem B980315 : Blo 650305 980315 := bstep (se 1 (by rfl) ⟨735236, by rfl⟩ : syracuseStep 980315 = 1470473) B1470473
theorem B652699 : Blo 650305 652699 := bstep (se 1 (by rfl) ⟨489524, by rfl⟩ : syracuseStep 652699 = 979049) B979049
theorem B5633545 : Blo 650305 5633545 := bstep (se 2 (by rfl) ⟨2112579, by rfl⟩ : syracuseStep 5633545 = 4225159) B4225159
theorem B2225735 : Blo 650305 2225735 := bstep (se 1 (by rfl) ⟨1669301, by rfl⟩ : syracuseStep 2225735 = 3338603) B3338603
theorem B652911 : Blo 650305 652911 := bstep (se 1 (by rfl) ⟨489683, by rfl⟩ : syracuseStep 652911 = 979367) B979367
theorem B980591 : Blo 650305 980591 := bstep (se 1 (by rfl) ⟨735443, by rfl⟩ : syracuseStep 980591 = 1470887) B1470887
theorem B652967 : Blo 650305 652967 := bstep (se 1 (by rfl) ⟨489725, by rfl⟩ : syracuseStep 652967 = 979451) B979451
theorem B3339959 : Blo 650305 3339959 := bstep (se 1 (by rfl) ⟨2504969, by rfl⟩ : syracuseStep 3339959 = 5009939) B5009939
theorem B980663 : Blo 650305 980663 := bstep (se 1 (by rfl) ⟨735497, by rfl⟩ : syracuseStep 980663 = 1470995) B1470995
theorem B1472183 : Blo 650305 1472183 := bstep (se 1 (by rfl) ⟨1104137, by rfl⟩ : syracuseStep 1472183 = 2208275) B2208275
theorem B4454099 : Blo 650305 4454099 := bstep (se 1 (by rfl) ⟨3340574, by rfl⟩ : syracuseStep 4454099 = 6681149) B6681149
theorem B784091 : Blo 650305 784091 := bstep (se 1 (by rfl) ⟨588068, by rfl⟩ : syracuseStep 784091 = 1176137) B1176137
theorem B980699 : Blo 650305 980699 := bstep (se 1 (by rfl) ⟨735524, by rfl⟩ : syracuseStep 980699 = 1471049) B1471049
theorem B653051 : Blo 650305 653051 := bstep (se 1 (by rfl) ⟨489788, by rfl⟩ : syracuseStep 653051 = 979577) B979577
theorem B653087 : Blo 650305 653087 := bstep (se 1 (by rfl) ⟨489815, by rfl⟩ : syracuseStep 653087 = 979631) B979631
theorem B653119 : Blo 650305 653119 := bstep (se 1 (by rfl) ⟨489839, by rfl⟩ : syracuseStep 653119 = 979679) B979679
theorem B980873 : Blo 650305 980873 := bstep (se 2 (by rfl) ⟨367827, by rfl⟩ : syracuseStep 980873 = 735655) B735655
theorem B653295 : Blo 650305 653295 := bstep (se 1 (by rfl) ⟨489971, by rfl⟩ : syracuseStep 653295 = 979943) B979943
theorem B980975 : Blo 650305 980975 := bstep (se 1 (by rfl) ⟨735731, by rfl⟩ : syracuseStep 980975 = 1471463) B1471463
theorem B653467 : Blo 650305 653467 := bstep (se 1 (by rfl) ⟨490100, by rfl⟩ : syracuseStep 653467 = 980201) B980201
theorem B653503 : Blo 650305 653503 := bstep (se 1 (by rfl) ⟨490127, by rfl⟩ : syracuseStep 653503 = 980255) B980255
theorem B981227 : Blo 650305 981227 := bstep (se 1 (by rfl) ⟨735920, by rfl⟩ : syracuseStep 981227 = 1471841) B1471841
theorem B981287 : Blo 650305 981287 := bstep (se 1 (by rfl) ⟨735965, by rfl⟩ : syracuseStep 981287 = 1471931) B1471931
theorem B653615 : Blo 650305 653615 := bstep (se 1 (by rfl) ⟨490211, by rfl⟩ : syracuseStep 653615 = 980423) B980423
theorem B981371 : Blo 650305 981371 := bstep (se 1 (by rfl) ⟨736028, by rfl⟩ : syracuseStep 981371 = 1472057) B1472057
theorem B653851 : Blo 650305 653851 := bstep (se 1 (by rfl) ⟨490388, by rfl⟩ : syracuseStep 653851 = 980777) B980777
theorem B653855 : Blo 650305 653855 := bstep (se 1 (by rfl) ⟨490391, by rfl⟩ : syracuseStep 653855 = 980783) B980783
theorem B32143979 : Blo 650305 32143979 := bstep (se 1 (by rfl) ⟨24107984, by rfl⟩ : syracuseStep 32143979 = 48215969) B48215969
theorem B654171 : Blo 650305 654171 := bstep (se 1 (by rfl) ⟨490628, by rfl⟩ : syracuseStep 654171 = 981257) B981257
theorem B654239 : Blo 650305 654239 := bstep (se 1 (by rfl) ⟨490679, by rfl⟩ : syracuseStep 654239 = 981359) B981359
theorem B3309011 : Blo 650305 3309011 := bstep (se 1 (by rfl) ⟨2481758, by rfl⟩ : syracuseStep 3309011 = 4963517) B4963517
theorem B7930943 : Blo 650305 7930943 := bstep (se 1 (by rfl) ⟨5948207, by rfl⟩ : syracuseStep 7930943 = 11896415) B11896415
theorem B2196827 : Blo 650305 2196827 := bstep (se 1 (by rfl) ⟨1647620, by rfl⟩ : syracuseStep 2196827 = 3295241) B3295241
theorem B6260273 : Blo 650305 6260273 := bstep (se 2 (by rfl) ⟨2347602, by rfl⟩ : syracuseStep 6260273 = 4695205) B4695205
theorem B2197097 : Blo 650305 2197097 := bstep (se 2 (by rfl) ⟨823911, by rfl⟩ : syracuseStep 2197097 = 1647823) B1647823
theorem B3311279 : Blo 650305 3311279 := bstep (se 1 (by rfl) ⟨2483459, by rfl⟩ : syracuseStep 3311279 = 4966919) B4966919
theorem B2197259 : Blo 650305 2197259 := bstep (se 1 (by rfl) ⟨1647944, by rfl⟩ : syracuseStep 2197259 = 3295889) B3295889
theorem B2197529 : Blo 650305 2197529 := bstep (se 2 (by rfl) ⟨824073, by rfl⟩ : syracuseStep 2197529 = 1648147) B1648147
theorem B755743 : Blo 650305 755743 := bstep (se 1 (by rfl) ⟨566807, by rfl⟩ : syracuseStep 755743 = 1133615) B1133615
theorem B90540109 : Blo 650305 90540109 := bstep (se 3 (by rfl) ⟨16976270, by rfl⟩ : syracuseStep 90540109 = 33952541) B33952541
theorem B2197691 : Blo 650305 2197691 := bstep (se 1 (by rfl) ⟨1648268, by rfl⟩ : syracuseStep 2197691 = 3296537) B3296537
theorem B5376203 : Blo 650305 5376203 := bstep (se 1 (by rfl) ⟨4032152, by rfl⟩ : syracuseStep 5376203 = 8064305) B8064305
theorem B7539101 : Blo 650305 7539101 := bstep (se 3 (by rfl) ⟨1413581, by rfl⟩ : syracuseStep 7539101 = 2827163) B2827163
theorem B6261623 : Blo 650305 6261623 := bstep (se 1 (by rfl) ⟨4696217, by rfl⟩ : syracuseStep 6261623 = 9392435) B9392435
theorem B5573569 : Blo 650305 5573569 := bstep (se 2 (by rfl) ⟨2090088, by rfl⟩ : syracuseStep 5573569 = 4180177) B4180177
theorem B5573843 : Blo 650305 5573843 := bstep (se 1 (by rfl) ⟨4180382, by rfl⟩ : syracuseStep 5573843 = 8360765) B8360765
theorem B2198879 : Blo 650305 2198879 := bstep (se 1 (by rfl) ⟨1649159, by rfl⟩ : syracuseStep 2198879 = 3298319) B3298319
theorem B2199419 : Blo 650305 2199419 := bstep (se 1 (by rfl) ⟨1649564, by rfl⟩ : syracuseStep 2199419 = 3299129) B3299129
theorem B823279 : Blo 650305 823279 := bstep (se 1 (by rfl) ⟨617459, by rfl⟩ : syracuseStep 823279 = 1234919) B1234919
theorem B2823599 : Blo 650305 2823599 := bstep (se 1 (by rfl) ⟨2117699, by rfl⟩ : syracuseStep 2823599 = 4235399) B4235399
theorem B11114333 : Blo 650305 11114333 := bstep (se 3 (by rfl) ⟨2083937, by rfl⟩ : syracuseStep 11114333 = 4167875) B4167875
theorem B1678067 : Blo 650305 1678067 := bstep (se 1 (by rfl) ⟨1258550, by rfl⟩ : syracuseStep 1678067 = 2517101) B2517101
theorem B7511393 : Blo 650305 7511393 := bstep (se 2 (by rfl) ⟨2816772, by rfl⟩ : syracuseStep 7511393 = 5633545) B5633545
theorem B1646153 : Blo 650305 1646153 := bstep (se 2 (by rfl) ⟨617307, by rfl⟩ : syracuseStep 1646153 = 1234615) B1234615
theorem B827167 : Blo 650305 827167 := bstep (se 1 (by rfl) ⟨620375, by rfl⟩ : syracuseStep 827167 = 1240751) B1240751
theorem B1483823 : Blo 650305 1483823 := bstep (se 1 (by rfl) ⟨1112867, by rfl⟩ : syracuseStep 1483823 = 2225735) B2225735
theorem B4466081 : Blo 650305 4466081 := bstep (se 2 (by rfl) ⟨1674780, by rfl⟩ : syracuseStep 4466081 = 3349561) B3349561
theorem B1255657 : Blo 650305 1255657 := bstep (se 2 (by rfl) ⟨470871, by rfl⟩ : syracuseStep 1255657 = 941743) B941743
theorem B2206007 : Blo 650305 2206007 := bstep (se 1 (by rfl) ⟨1654505, by rfl⟩ : syracuseStep 2206007 = 3309011) B3309011
theorem B6269345 : Blo 650305 6269345 := bstep (se 2 (by rfl) ⟨2351004, by rfl⟩ : syracuseStep 6269345 = 4702009) B4702009
theorem B731695 : Blo 650305 731695 := bstep (se 1 (by rfl) ⟨548771, by rfl⟩ : syracuseStep 731695 = 1097543) B1097543
theorem B732127 : Blo 650305 732127 := bstep (se 1 (by rfl) ⟨549095, by rfl⟩ : syracuseStep 732127 = 1098191) B1098191
theorem B1649929 : Blo 650305 1649929 := bstep (se 2 (by rfl) ⟨618723, by rfl⟩ : syracuseStep 1649929 = 1237447) B1237447
theorem B3517775 : Blo 650305 3517775 := bstep (se 1 (by rfl) ⟨2638331, by rfl⟩ : syracuseStep 3517775 = 5276663) B5276663
theorem B42249559 : Blo 650305 42249559 := bstep (se 1 (by rfl) ⟨31687169, by rfl⟩ : syracuseStep 42249559 = 63374339) B63374339
theorem B2469275 : Blo 650305 2469275 := bstep (se 1 (by rfl) ⟨1851956, by rfl⟩ : syracuseStep 2469275 = 3703913) B3703913
theorem B929179 : Blo 650305 929179 := bstep (se 1 (by rfl) ⟨696884, by rfl⟩ : syracuseStep 929179 = 1393769) B1393769
theorem B3714619 : Blo 650305 3714619 := bstep (se 1 (by rfl) ⟨2785964, by rfl⟩ : syracuseStep 3714619 = 5571929) B5571929
theorem B732775 : Blo 650305 732775 := bstep (se 1 (by rfl) ⟨549581, by rfl⟩ : syracuseStep 732775 = 1099163) B1099163
theorem B2207465 : Blo 650305 2207465 := bstep (se 2 (by rfl) ⟨827799, by rfl⟩ : syracuseStep 2207465 = 1655599) B1655599
theorem B732991 : Blo 650305 732991 := bstep (se 1 (by rfl) ⟨549743, by rfl⟩ : syracuseStep 732991 = 1099487) B1099487
theorem B4829053 : Blo 650305 4829053 := bstep (se 3 (by rfl) ⟨905447, by rfl⟩ : syracuseStep 4829053 = 1810895) B1810895
theorem B733279 : Blo 650305 733279 := bstep (se 1 (by rfl) ⟨549959, by rfl⟩ : syracuseStep 733279 = 1099919) B1099919
theorem B4960601 : Blo 650305 4960601 := bstep (se 2 (by rfl) ⟨1860225, by rfl⟩ : syracuseStep 4960601 = 3720451) B3720451
theorem B1257935 : Blo 650305 1257935 := bstep (se 1 (by rfl) ⟨943451, by rfl⟩ : syracuseStep 1257935 = 1886903) B1886903
theorem B5026319 : Blo 650305 5026319 := bstep (se 1 (by rfl) ⟨3769739, by rfl⟩ : syracuseStep 5026319 = 7539479) B7539479
theorem B4961087 : Blo 650305 4961087 := bstep (se 1 (by rfl) ⟨3720815, by rfl⟩ : syracuseStep 4961087 = 7441631) B7441631
theorem B4699009 : Blo 650305 4699009 := bstep (se 2 (by rfl) ⟨1762128, by rfl⟩ : syracuseStep 4699009 = 3524257) B3524257
theorem B4699241 : Blo 650305 4699241 := bstep (se 2 (by rfl) ⟨1762215, by rfl⟩ : syracuseStep 4699241 = 3524431) B3524431
theorem B1258919 : Blo 650305 1258919 := bstep (se 1 (by rfl) ⟨944189, by rfl⟩ : syracuseStep 1258919 = 1888379) B1888379
theorem B1652471 : Blo 650305 1652471 := bstep (se 1 (by rfl) ⟨1239353, by rfl⟩ : syracuseStep 1652471 = 2478707) B2478707
theorem B5585051 : Blo 650305 5585051 := bstep (se 1 (by rfl) ⟨4188788, by rfl⟩ : syracuseStep 5585051 = 8377577) B8377577
theorem B735835 : Blo 650305 735835 := bstep (se 1 (by rfl) ⟨551876, by rfl⟩ : syracuseStep 735835 = 1103753) B1103753
theorem B10566287 : Blo 650305 10566287 := bstep (se 1 (by rfl) ⟨7924715, by rfl⟩ : syracuseStep 10566287 = 15849431) B15849431
theorem B4963031 : Blo 650305 4963031 := bstep (se 1 (by rfl) ⟨3722273, by rfl⟩ : syracuseStep 4963031 = 7444547) B7444547
theorem B9419651 : Blo 650305 9419651 := bstep (se 1 (by rfl) ⟨7064738, by rfl⟩ : syracuseStep 9419651 = 14129477) B14129477
theorem B69483835 : Blo 650305 69483835 := bstep (se 1 (by rfl) ⟨52112876, by rfl⟩ : syracuseStep 69483835 = 104225753) B104225753
theorem B1490831 : Blo 650305 1490831 := bstep (se 1 (by rfl) ⟨1118123, by rfl⟩ : syracuseStep 1490831 = 2236247) B2236247
theorem B1097671 : Blo 650305 1097671 := bstep (se 1 (by rfl) ⟨823253, by rfl⟩ : syracuseStep 1097671 = 1646507) B1646507
theorem B1654739 : Blo 650305 1654739 := bstep (se 1 (by rfl) ⟨1241054, by rfl⟩ : syracuseStep 1654739 = 2482109) B2482109
theorem B1982713 : Blo 650305 1982713 := bstep (se 2 (by rfl) ⟨743517, by rfl⟩ : syracuseStep 1982713 = 1487035) B1487035
theorem B8929925 : Blo 650305 8929925 := bstep (se 4 (by rfl) ⟨837180, by rfl⟩ : syracuseStep 8929925 = 1674361) B1674361
theorem B1098427 : Blo 650305 1098427 := bstep (se 1 (by rfl) ⟨823820, by rfl⟩ : syracuseStep 1098427 = 1647641) B1647641
theorem B3523439 : Blo 650305 3523439 := bstep (se 1 (by rfl) ⟨2642579, by rfl⟩ : syracuseStep 3523439 = 5285159) B5285159
theorem B3294107 : Blo 650305 3294107 := bstep (se 1 (by rfl) ⟨2470580, by rfl⟩ : syracuseStep 3294107 = 4941161) B4941161
theorem B1099055 : Blo 650305 1099055 := bstep (se 1 (by rfl) ⟨824291, by rfl⟩ : syracuseStep 1099055 = 1648583) B1648583
theorem B4474295 : Blo 650305 4474295 := bstep (se 1 (by rfl) ⟨3355721, by rfl⟩ : syracuseStep 4474295 = 6711443) B6711443
theorem B11879921 : Blo 650305 11879921 := bstep (se 2 (by rfl) ⟨4454970, by rfl⟩ : syracuseStep 11879921 = 8909941) B8909941
theorem B4965947 : Blo 650305 4965947 := bstep (se 1 (by rfl) ⟨3724460, by rfl⟩ : syracuseStep 4965947 = 7448921) B7448921
theorem B1394281 : Blo 650305 1394281 := bstep (se 2 (by rfl) ⟨522855, by rfl⟩ : syracuseStep 1394281 = 1045711) B1045711
theorem B5588675 : Blo 650305 5588675 := bstep (se 1 (by rfl) ⟨4191506, by rfl⟩ : syracuseStep 5588675 = 8383013) B8383013
theorem B1591451 : Blo 650305 1591451 := bstep (se 1 (by rfl) ⟨1193588, by rfl⟩ : syracuseStep 1591451 = 2387177) B2387177
theorem B2377927 : Blo 650305 2377927 := bstep (se 1 (by rfl) ⟨1783445, by rfl⟩ : syracuseStep 2377927 = 3566891) B3566891
theorem B4967405 : Blo 650305 4967405 := bstep (se 3 (by rfl) ⟨931388, by rfl⟩ : syracuseStep 4967405 = 1862777) B1862777
theorem B2477051 : Blo 650305 2477051 := bstep (se 1 (by rfl) ⟨1857788, by rfl⟩ : syracuseStep 2477051 = 3715577) B3715577
theorem B8342675 : Blo 650305 8342675 := bstep (se 1 (by rfl) ⟨6257006, by rfl⟩ : syracuseStep 8342675 = 12514013) B12514013
theorem B5950687 : Blo 650305 5950687 := bstep (se 1 (by rfl) ⟨4463015, by rfl⟩ : syracuseStep 5950687 = 8926031) B8926031
theorem B2084093 : Blo 650305 2084093 := bstep (se 3 (by rfl) ⟨390767, by rfl⟩ : syracuseStep 2084093 = 781535) B781535
theorem B7032253 : Blo 650305 7032253 := bstep (se 3 (by rfl) ⟨1318547, by rfl⟩ : syracuseStep 7032253 = 2637095) B2637095
theorem B2510327 : Blo 650305 2510327 := bstep (se 1 (by rfl) ⟨1882745, by rfl⟩ : syracuseStep 2510327 = 3765491) B3765491
theorem B2969399 : Blo 650305 2969399 := bstep (se 1 (by rfl) ⟨2227049, by rfl⟩ : syracuseStep 2969399 = 4454099) B4454099
theorem B2478235 : Blo 650305 2478235 := bstep (se 1 (by rfl) ⟨1858676, by rfl⟩ : syracuseStep 2478235 = 3717353) B3717353
theorem B2085875 : Blo 650305 2085875 := bstep (se 1 (by rfl) ⟨1564406, by rfl⟩ : syracuseStep 2085875 = 3128813) B3128813
theorem B3724325 : Blo 650305 3724325 := bstep (se 4 (by rfl) ⟨349155, by rfl⟩ : syracuseStep 3724325 = 698311) B698311
theorem B1102943 : Blo 650305 1102943 := bstep (se 1 (by rfl) ⟨827207, by rfl⟩ : syracuseStep 1102943 = 1654415) B1654415
theorem B1988233 : Blo 650305 1988233 := bstep (se 2 (by rfl) ⟨745587, by rfl⟩ : syracuseStep 1988233 = 1491175) B1491175
theorem B1463975 : Blo 650305 1463975 := bstep (se 1 (by rfl) ⟨1097981, by rfl⟩ : syracuseStep 1463975 = 2195963) B2195963
theorem B40195763 : Blo 650305 40195763 := bstep (se 1 (by rfl) ⟨30146822, by rfl⟩ : syracuseStep 40195763 = 60293645) B60293645
theorem B1234759 : Blo 650305 1234759 := bstep (se 1 (by rfl) ⟨926069, by rfl⟩ : syracuseStep 1234759 = 1852139) B1852139
theorem B1464155 : Blo 650305 1464155 := bstep (se 1 (by rfl) ⟨1098116, by rfl⟩ : syracuseStep 1464155 = 2196233) B2196233
theorem B3299291 : Blo 650305 3299291 := bstep (se 1 (by rfl) ⟨2474468, by rfl⟩ : syracuseStep 3299291 = 4948937) B4948937
theorem B6281185 : Blo 650305 6281185 := bstep (se 2 (by rfl) ⟨2355444, by rfl⟩ : syracuseStep 6281185 = 4710889) B4710889
theorem B3725351 : Blo 650305 3725351 := bstep (se 1 (by rfl) ⟨2794013, by rfl⟩ : syracuseStep 3725351 = 5588027) B5588027
theorem B2676833 : Blo 650305 2676833 := bstep (se 2 (by rfl) ⟨1003812, by rfl⟩ : syracuseStep 2676833 = 2007625) B2007625
theorem B3135635 : Blo 650305 3135635 := bstep (se 1 (by rfl) ⟨2351726, by rfl⟩ : syracuseStep 3135635 = 4703453) B4703453
theorem B1857755 : Blo 650305 1857755 := bstep (se 1 (by rfl) ⟨1393316, by rfl⟩ : syracuseStep 1857755 = 2786633) B2786633
theorem B1464659 : Blo 650305 1464659 := bstep (se 1 (by rfl) ⟨1098494, by rfl⟩ : syracuseStep 1464659 = 2196989) B2196989
theorem B2972065 : Blo 650305 2972065 := bstep (se 2 (by rfl) ⟨1114524, by rfl⟩ : syracuseStep 2972065 = 2229049) B2229049
theorem B4250089 : Blo 650305 4250089 := bstep (se 2 (by rfl) ⟨1593783, by rfl⟩ : syracuseStep 4250089 = 3187567) B3187567
theorem B5790455 : Blo 650305 5790455 := bstep (se 1 (by rfl) ⟨4342841, by rfl⟩ : syracuseStep 5790455 = 8685683) B8685683
theorem B3136249 : Blo 650305 3136249 := bstep (se 2 (by rfl) ⟨1176093, by rfl⟩ : syracuseStep 3136249 = 2352187) B2352187
theorem B1465145 : Blo 650305 1465145 := bstep (se 2 (by rfl) ⟨549429, by rfl⟩ : syracuseStep 1465145 = 1098859) B1098859
theorem B1465199 : Blo 650305 1465199 := bstep (se 1 (by rfl) ⟨1098899, by rfl⟩ : syracuseStep 1465199 = 2197799) B2197799
theorem B4938731 : Blo 650305 4938731 := bstep (se 1 (by rfl) ⟨3704048, by rfl⟩ : syracuseStep 4938731 = 7408097) B7408097
theorem B1465775 : Blo 650305 1465775 := bstep (se 1 (by rfl) ⟨1099331, by rfl⟩ : syracuseStep 1465775 = 2198663) B2198663
theorem B1465847 : Blo 650305 1465847 := bstep (se 1 (by rfl) ⟨1099385, by rfl⟩ : syracuseStep 1465847 = 2198771) B2198771
theorem B5431499 : Blo 650305 5431499 := bstep (se 1 (by rfl) ⟨4073624, by rfl⟩ : syracuseStep 5431499 = 8147249) B8147249
theorem B1761697 : Blo 650305 1761697 := bstep (se 2 (by rfl) ⟨660636, by rfl⟩ : syracuseStep 1761697 = 1321273) B1321273
theorem B1466873 : Blo 650305 1466873 := bstep (se 2 (by rfl) ⟨550077, by rfl⟩ : syracuseStep 1466873 = 1100155) B1100155
theorem B1237531 : Blo 650305 1237531 := bstep (se 1 (by rfl) ⟨928148, by rfl⟩ : syracuseStep 1237531 = 1856297) B1856297
theorem B1466963 : Blo 650305 1466963 := bstep (se 1 (by rfl) ⟨1100222, by rfl⟩ : syracuseStep 1466963 = 2200445) B2200445
theorem B975527 : Blo 650305 975527 := bstep (se 1 (by rfl) ⟨731645, by rfl⟩ : syracuseStep 975527 = 1463291) B1463291
theorem B1467143 : Blo 650305 1467143 := bstep (se 1 (by rfl) ⟨1100357, by rfl⟩ : syracuseStep 1467143 = 2200715) B2200715
theorem B975647 : Blo 650305 975647 := bstep (se 1 (by rfl) ⟨731735, by rfl⟩ : syracuseStep 975647 = 1463471) B1463471
theorem B975671 : Blo 650305 975671 := bstep (se 1 (by rfl) ⟨731753, by rfl⟩ : syracuseStep 975671 = 1463507) B1463507
theorem B1467233 : Blo 650305 1467233 := bstep (se 2 (by rfl) ⟨550212, by rfl⟩ : syracuseStep 1467233 = 1100425) B1100425
theorem B975851 : Blo 650305 975851 := bstep (se 1 (by rfl) ⟨731888, by rfl⟩ : syracuseStep 975851 = 1463777) B1463777
theorem B10576925 : Blo 650305 10576925 := bstep (se 3 (by rfl) ⟨1983173, by rfl⟩ : syracuseStep 10576925 = 3966347) B3966347
theorem B63497357 : Blo 650305 63497357 := bstep (se 3 (by rfl) ⟨11905754, by rfl⟩ : syracuseStep 63497357 = 23811509) B23811509
theorem B1566107 : Blo 650305 1566107 := bstep (se 1 (by rfl) ⟨1174580, by rfl⟩ : syracuseStep 1566107 = 2349161) B2349161
theorem B2090731 : Blo 650305 2090731 := bstep (se 1 (by rfl) ⟨1568048, by rfl⟩ : syracuseStep 2090731 = 3136097) B3136097
theorem B12511007 : Blo 650305 12511007 := bstep (se 1 (by rfl) ⟨9383255, by rfl⟩ : syracuseStep 12511007 = 18766511) B18766511
theorem B8906557 : Blo 650305 8906557 := bstep (se 3 (by rfl) ⟨1669979, by rfl⟩ : syracuseStep 8906557 = 3339959) B3339959
theorem B1468223 : Blo 650305 1468223 := bstep (se 1 (by rfl) ⟨1101167, by rfl⟩ : syracuseStep 1468223 = 2202335) B2202335
theorem B4941647 : Blo 650305 4941647 := bstep (se 1 (by rfl) ⟨3706235, by rfl⟩ : syracuseStep 4941647 = 7412471) B7412471
theorem B2090909 : Blo 650305 2090909 := bstep (se 3 (by rfl) ⟨392045, by rfl⟩ : syracuseStep 2090909 = 784091) B784091
theorem B976943 : Blo 650305 976943 := bstep (se 1 (by rfl) ⟨732707, by rfl⟩ : syracuseStep 976943 = 1465415) B1465415
theorem B2680955 : Blo 650305 2680955 := bstep (se 1 (by rfl) ⟨2010716, by rfl⟩ : syracuseStep 2680955 = 4021433) B4021433
theorem B1763471 : Blo 650305 1763471 := bstep (se 1 (by rfl) ⟨1322603, by rfl⟩ : syracuseStep 1763471 = 2645207) B2645207
theorem B1861775 : Blo 650305 1861775 := bstep (se 1 (by rfl) ⟨1396331, by rfl⟩ : syracuseStep 1861775 = 2792663) B2792663
theorem B3958955 : Blo 650305 3958955 := bstep (se 1 (by rfl) ⟨2969216, by rfl⟩ : syracuseStep 3958955 = 5938433) B5938433
theorem B977207 : Blo 650305 977207 := bstep (se 1 (by rfl) ⟨732905, by rfl⟩ : syracuseStep 977207 = 1465811) B1465811
theorem B1468727 : Blo 650305 1468727 := bstep (se 1 (by rfl) ⟨1101545, by rfl⟩ : syracuseStep 1468727 = 2203091) B2203091
theorem B977387 : Blo 650305 977387 := bstep (se 1 (by rfl) ⟨733040, by rfl⟩ : syracuseStep 977387 = 1466081) B1466081
theorem B1468907 : Blo 650305 1468907 := bstep (se 1 (by rfl) ⟨1101680, by rfl⟩ : syracuseStep 1468907 = 2203361) B2203361
theorem B3762719 : Blo 650305 3762719 := bstep (se 1 (by rfl) ⟨2822039, by rfl⟩ : syracuseStep 3762719 = 5644079) B5644079
theorem B1240105 : Blo 650305 1240105 := bstep (se 2 (by rfl) ⟨465039, by rfl⟩ : syracuseStep 1240105 = 930079) B930079
theorem B978089 : Blo 650305 978089 := bstep (se 2 (by rfl) ⟨366783, by rfl⟩ : syracuseStep 978089 = 733567) B733567
theorem B1469609 : Blo 650305 1469609 := bstep (se 2 (by rfl) ⟨551103, by rfl⟩ : syracuseStep 1469609 = 1102207) B1102207
theorem B650623 : Blo 650305 650623 := bstep (se 1 (by rfl) ⟨487967, by rfl⟩ : syracuseStep 650623 = 975935) B975935
theorem B650651 : Blo 650305 650651 := bstep (se 1 (by rfl) ⟨487988, by rfl⟩ : syracuseStep 650651 = 975977) B975977
theorem B2092499 : Blo 650305 2092499 := bstep (se 1 (by rfl) ⟨1569374, by rfl⟩ : syracuseStep 2092499 = 3138749) B3138749
theorem B650719 : Blo 650305 650719 := bstep (se 1 (by rfl) ⟨488039, by rfl⟩ : syracuseStep 650719 = 976079) B976079
theorem B3173855 : Blo 650305 3173855 := bstep (se 1 (by rfl) ⟨2380391, by rfl⟩ : syracuseStep 3173855 = 4760783) B4760783
theorem B978503 : Blo 650305 978503 := bstep (se 1 (by rfl) ⟨733877, by rfl⟩ : syracuseStep 978503 = 1467755) B1467755
theorem B1470023 : Blo 650305 1470023 := bstep (se 1 (by rfl) ⟨1102517, by rfl⟩ : syracuseStep 1470023 = 2205035) B2205035
theorem B1240667 : Blo 650305 1240667 := bstep (se 1 (by rfl) ⟨930500, by rfl⟩ : syracuseStep 1240667 = 1861001) B1861001
theorem B650855 : Blo 650305 650855 := bstep (se 1 (by rfl) ⟨488141, by rfl⟩ : syracuseStep 650855 = 976283) B976283
theorem B1470095 : Blo 650305 1470095 := bstep (se 1 (by rfl) ⟨1102571, by rfl⟩ : syracuseStep 1470095 = 2205143) B2205143
theorem B1568489 : Blo 650305 1568489 := bstep (se 2 (by rfl) ⟨588183, by rfl⟩ : syracuseStep 1568489 = 1176367) B1176367
theorem B1470185 : Blo 650305 1470185 := bstep (se 2 (by rfl) ⟨551319, by rfl⟩ : syracuseStep 1470185 = 1102639) B1102639
theorem B651003 : Blo 650305 651003 := bstep (se 1 (by rfl) ⟨488252, by rfl⟩ : syracuseStep 651003 = 976505) B976505
theorem B978683 : Blo 650305 978683 := bstep (se 1 (by rfl) ⟨734012, by rfl⟩ : syracuseStep 978683 = 1468025) B1468025
theorem B1765115 : Blo 650305 1765115 := bstep (se 1 (by rfl) ⟨1323836, by rfl⟩ : syracuseStep 1765115 = 2647673) B2647673
theorem B1470203 : Blo 650305 1470203 := bstep (se 1 (by rfl) ⟨1102652, by rfl⟩ : syracuseStep 1470203 = 2205305) B2205305
theorem B651071 : Blo 650305 651071 := bstep (se 1 (by rfl) ⟨488303, by rfl⟩ : syracuseStep 651071 = 976607) B976607
theorem B1240895 : Blo 650305 1240895 := bstep (se 1 (by rfl) ⟨930671, by rfl⟩ : syracuseStep 1240895 = 1861343) B1861343
theorem B651135 : Blo 650305 651135 := bstep (se 1 (by rfl) ⟨488351, by rfl⟩ : syracuseStep 651135 = 976703) B976703
theorem B8482733 : Blo 650305 8482733 := bstep (se 3 (by rfl) ⟨1590512, by rfl⟩ : syracuseStep 8482733 = 3181025) B3181025
theorem B651247 : Blo 650305 651247 := bstep (se 1 (by rfl) ⟨488435, by rfl⟩ : syracuseStep 651247 = 976871) B976871
theorem B651259 : Blo 650305 651259 := bstep (se 1 (by rfl) ⟨488444, by rfl⟩ : syracuseStep 651259 = 976889) B976889
theorem B651327 : Blo 650305 651327 := bstep (se 1 (by rfl) ⟨488495, by rfl⟩ : syracuseStep 651327 = 976991) B976991
theorem B651367 : Blo 650305 651367 := bstep (se 1 (by rfl) ⟨488525, by rfl⟩ : syracuseStep 651367 = 977051) B977051
theorem B651391 : Blo 650305 651391 := bstep (se 1 (by rfl) ⟨488543, by rfl⟩ : syracuseStep 651391 = 977087) B977087
theorem B651419 : Blo 650305 651419 := bstep (se 1 (by rfl) ⟨488564, by rfl⟩ : syracuseStep 651419 = 977129) B977129
theorem B12513467 : Blo 650305 12513467 := bstep (se 1 (by rfl) ⟨9385100, by rfl⟩ : syracuseStep 12513467 = 18770201) B18770201
theorem B651623 : Blo 650305 651623 := bstep (se 1 (by rfl) ⟨488717, by rfl⟩ : syracuseStep 651623 = 977435) B977435
theorem B651675 : Blo 650305 651675 := bstep (se 1 (by rfl) ⟨488756, by rfl⟩ : syracuseStep 651675 = 977513) B977513
theorem B979355 : Blo 650305 979355 := bstep (se 1 (by rfl) ⟨734516, by rfl⟩ : syracuseStep 979355 = 1469033) B1469033
theorem B14086649 : Blo 650305 14086649 := bstep (se 2 (by rfl) ⟨5282493, by rfl⟩ : syracuseStep 14086649 = 10564987) B10564987
theorem B4649567 : Blo 650305 4649567 := bstep (se 1 (by rfl) ⟨3487175, by rfl⟩ : syracuseStep 4649567 = 6974351) B6974351
theorem B3535483 : Blo 650305 3535483 := bstep (se 1 (by rfl) ⟨2651612, by rfl⟩ : syracuseStep 3535483 = 5303225) B5303225
theorem B1471211 : Blo 650305 1471211 := bstep (se 1 (by rfl) ⟨1103408, by rfl⟩ : syracuseStep 1471211 = 2206817) B2206817
theorem B652027 : Blo 650305 652027 := bstep (se 1 (by rfl) ⟨489020, by rfl⟩ : syracuseStep 652027 = 978041) B978041
theorem B652095 : Blo 650305 652095 := bstep (se 1 (by rfl) ⟨489071, by rfl⟩ : syracuseStep 652095 = 978143) B978143
theorem B979775 : Blo 650305 979775 := bstep (se 1 (by rfl) ⟨734831, by rfl⟩ : syracuseStep 979775 = 1469663) B1469663
theorem B652123 : Blo 650305 652123 := bstep (se 1 (by rfl) ⟨489092, by rfl⟩ : syracuseStep 652123 = 978185) B978185
theorem B652191 : Blo 650305 652191 := bstep (se 1 (by rfl) ⟨489143, by rfl⟩ : syracuseStep 652191 = 978287) B978287
theorem B979919 : Blo 650305 979919 := bstep (se 1 (by rfl) ⟨734939, by rfl⟩ : syracuseStep 979919 = 1469879) B1469879
theorem B652271 : Blo 650305 652271 := bstep (se 1 (by rfl) ⟨489203, by rfl⟩ : syracuseStep 652271 = 978407) B978407
theorem B979961 : Blo 650305 979961 := bstep (se 2 (by rfl) ⟨367485, by rfl⟩ : syracuseStep 979961 = 734971) B734971
theorem B1471481 : Blo 650305 1471481 := bstep (se 2 (by rfl) ⟨551805, by rfl⟩ : syracuseStep 1471481 = 1103611) B1103611
theorem B980009 : Blo 650305 980009 := bstep (se 2 (by rfl) ⟨367503, by rfl⟩ : syracuseStep 980009 = 735007) B735007
theorem B652359 : Blo 650305 652359 := bstep (se 1 (by rfl) ⟨489269, by rfl⟩ : syracuseStep 652359 = 978539) B978539
theorem B980039 : Blo 650305 980039 := bstep (se 1 (by rfl) ⟨735029, by rfl⟩ : syracuseStep 980039 = 1470059) B1470059
theorem B1471571 : Blo 650305 1471571 := bstep (se 1 (by rfl) ⟨1103678, by rfl⟩ : syracuseStep 1471571 = 2207357) B2207357
theorem B652443 : Blo 650305 652443 := bstep (se 1 (by rfl) ⟨489332, by rfl⟩ : syracuseStep 652443 = 978665) B978665
theorem B652539 : Blo 650305 652539 := bstep (se 1 (by rfl) ⟨489404, by rfl⟩ : syracuseStep 652539 = 978809) B978809
theorem B980219 : Blo 650305 980219 := bstep (se 1 (by rfl) ⟨735164, by rfl⟩ : syracuseStep 980219 = 1470329) B1470329
theorem B1471751 : Blo 650305 1471751 := bstep (se 1 (by rfl) ⟨1103813, by rfl⟩ : syracuseStep 1471751 = 2207627) B2207627
theorem B652607 : Blo 650305 652607 := bstep (se 1 (by rfl) ⟨489455, by rfl⟩ : syracuseStep 652607 = 978911) B978911
theorem B2782583 : Blo 650305 2782583 := bstep (se 1 (by rfl) ⟨2086937, by rfl⟩ : syracuseStep 2782583 = 4173875) B4173875
theorem B1570259 : Blo 650305 1570259 := bstep (se 1 (by rfl) ⟨1177694, by rfl⟩ : syracuseStep 1570259 = 2355389) B2355389
theorem B652775 : Blo 650305 652775 := bstep (se 1 (by rfl) ⟨489581, by rfl⟩ : syracuseStep 652775 = 979163) B979163
theorem B652783 : Blo 650305 652783 := bstep (se 1 (by rfl) ⟨489587, by rfl⟩ : syracuseStep 652783 = 979175) B979175
theorem B652891 : Blo 650305 652891 := bstep (se 1 (by rfl) ⟨489668, by rfl⟩ : syracuseStep 652891 = 979337) B979337
theorem B1472111 : Blo 650305 1472111 := bstep (se 1 (by rfl) ⟨1104083, by rfl⟩ : syracuseStep 1472111 = 2208167) B2208167
theorem B652955 : Blo 650305 652955 := bstep (se 1 (by rfl) ⟨489716, by rfl⟩ : syracuseStep 652955 = 979433) B979433
theorem B653039 : Blo 650305 653039 := bstep (se 1 (by rfl) ⟨489779, by rfl⟩ : syracuseStep 653039 = 979559) B979559
theorem B653127 : Blo 650305 653127 := bstep (se 1 (by rfl) ⟨489845, by rfl⟩ : syracuseStep 653127 = 979691) B979691
theorem B1341263 : Blo 650305 1341263 := bstep (se 1 (by rfl) ⟨1005947, by rfl⟩ : syracuseStep 1341263 = 2011895) B2011895
theorem B653147 : Blo 650305 653147 := bstep (se 1 (by rfl) ⟨489860, by rfl⟩ : syracuseStep 653147 = 979721) B979721
theorem B653215 : Blo 650305 653215 := bstep (se 1 (by rfl) ⟨489911, by rfl⟩ : syracuseStep 653215 = 979823) B979823
theorem B653383 : Blo 650305 653383 := bstep (se 1 (by rfl) ⟨490037, by rfl⟩ : syracuseStep 653383 = 980075) B980075
theorem B653543 : Blo 650305 653543 := bstep (se 1 (by rfl) ⟨490157, by rfl⟩ : syracuseStep 653543 = 980315) B980315
theorem B653727 : Blo 650305 653727 := bstep (se 1 (by rfl) ⟨490295, by rfl⟩ : syracuseStep 653727 = 980591) B980591
theorem B653775 : Blo 650305 653775 := bstep (se 1 (by rfl) ⟨490331, by rfl⟩ : syracuseStep 653775 = 980663) B980663
theorem B981455 : Blo 650305 981455 := bstep (se 1 (by rfl) ⟨736091, by rfl⟩ : syracuseStep 981455 = 1472183) B1472183
theorem B653799 : Blo 650305 653799 := bstep (se 1 (by rfl) ⟨490349, by rfl⟩ : syracuseStep 653799 = 980699) B980699
theorem B653915 : Blo 650305 653915 := bstep (se 1 (by rfl) ⟨490436, by rfl⟩ : syracuseStep 653915 = 980873) B980873
theorem B2816617 : Blo 650305 2816617 := bstep (se 2 (by rfl) ⟨1056231, by rfl⟩ : syracuseStep 2816617 = 2112463) B2112463
theorem B33094277 : Blo 650305 33094277 := bstep (se 4 (by rfl) ⟨3102588, by rfl⟩ : syracuseStep 33094277 = 6205177) B6205177
theorem B653983 : Blo 650305 653983 := bstep (se 1 (by rfl) ⟨490487, by rfl⟩ : syracuseStep 653983 = 980975) B980975
theorem B654151 : Blo 650305 654151 := bstep (se 1 (by rfl) ⟨490613, by rfl⟩ : syracuseStep 654151 = 981227) B981227
theorem B654191 : Blo 650305 654191 := bstep (se 1 (by rfl) ⟨490643, by rfl⟩ : syracuseStep 654191 = 981287) B981287
theorem B654247 : Blo 650305 654247 := bstep (se 1 (by rfl) ⟨490685, by rfl⟩ : syracuseStep 654247 = 981371) B981371
theorem B7437257 : Blo 650305 7437257 := bstep (se 2 (by rfl) ⟨2788971, by rfl⟩ : syracuseStep 7437257 = 5577943) B5577943
theorem B21429319 : Blo 650305 21429319 := bstep (se 1 (by rfl) ⟨16071989, by rfl⟩ : syracuseStep 21429319 = 32143979) B32143979
theorem B5274839 : Blo 650305 5274839 := bstep (se 1 (by rfl) ⟨3956129, by rfl⟩ : syracuseStep 5274839 = 7912259) B7912259
theorem B2784719 : Blo 650305 2784719 := bstep (se 1 (by rfl) ⟨2088539, by rfl⟩ : syracuseStep 2784719 = 4177079) B4177079
theorem B38108717 : Blo 650305 38108717 := bstep (se 3 (by rfl) ⟨7145384, by rfl⟩ : syracuseStep 38108717 = 14290769) B14290769
theorem B2196071 : Blo 650305 2196071 := bstep (se 1 (by rfl) ⟨1647053, by rfl⟩ : syracuseStep 2196071 = 3294107) B3294107
theorem B2982863 : Blo 650305 2982863 := bstep (se 1 (by rfl) ⟨2237147, by rfl⟩ : syracuseStep 2982863 = 4474295) B4474295
theorem B12682277 : Blo 650305 12682277 := bstep (se 4 (by rfl) ⟨1188963, by rfl⟩ : syracuseStep 12682277 = 2377927) B2377927
theorem B3310631 : Blo 650305 3310631 := bstep (se 1 (by rfl) ⟨2482973, by rfl⟩ : syracuseStep 3310631 = 4965947) B4965947
theorem B3311603 : Blo 650305 3311603 := bstep (se 1 (by rfl) ⟨2483702, by rfl⟩ : syracuseStep 3311603 = 4967405) B4967405
theorem B2787641 : Blo 650305 2787641 := bstep (se 2 (by rfl) ⟨1045365, by rfl⟩ : syracuseStep 2787641 = 2090731) B2090731
theorem B1673551 : Blo 650305 1673551 := bstep (se 1 (by rfl) ⟨1255163, by rfl⟩ : syracuseStep 1673551 = 2510327) B2510327
theorem B120720145 : Blo 650305 120720145 := bstep (se 2 (by rfl) ⟨45270054, by rfl⟩ : syracuseStep 120720145 = 90540109) B90540109
theorem B1674209 : Blo 650305 1674209 := bstep (se 2 (by rfl) ⟨627828, by rfl⟩ : syracuseStep 1674209 = 1255657) B1255657
theorem B7409555 : Blo 650305 7409555 := bstep (se 1 (by rfl) ⟨5557166, by rfl⟩ : syracuseStep 7409555 = 11114333) B11114333
theorem B2199527 : Blo 650305 2199527 := bstep (se 1 (by rfl) ⟨1649645, by rfl⟩ : syracuseStep 2199527 = 3299291) B3299291
theorem B7934249 : Blo 650305 7934249 := bstep (se 2 (by rfl) ⟨2975343, by rfl⟩ : syracuseStep 7934249 = 5950687) B5950687
theorem B2199905 : Blo 650305 2199905 := bstep (se 2 (by rfl) ⟨824964, by rfl⟩ : syracuseStep 2199905 = 1649929) B1649929
theorem B56332745 : Blo 650305 56332745 := bstep (se 2 (by rfl) ⟨21124779, by rfl⟩ : syracuseStep 56332745 = 42249559) B42249559
theorem B1118711 : Blo 650305 1118711 := bstep (se 1 (by rfl) ⟨839033, by rfl⟩ : syracuseStep 1118711 = 1678067) B1678067
theorem B9376337 : Blo 650305 9376337 := bstep (se 2 (by rfl) ⟨3516126, by rfl⟩ : syracuseStep 9376337 = 7032253) B7032253
theorem B4952825 : Blo 650305 4952825 := bstep (se 2 (by rfl) ⟨1857309, by rfl⟩ : syracuseStep 4952825 = 3714619) B3714619
theorem B33854453 : Blo 650305 33854453 := bstep (se 5 (by rfl) ⟨1586927, by rfl⟩ : syracuseStep 33854453 = 3173855) B3173855
theorem B7051283 : Blo 650305 7051283 := bstep (se 1 (by rfl) ⟨5288462, by rfl⟩ : syracuseStep 7051283 = 10576925) B10576925
theorem B989215 : Blo 650305 989215 := bstep (se 1 (by rfl) ⟨741911, by rfl⟩ : syracuseStep 989215 = 1483823) B1483823
theorem B6265345 : Blo 650305 6265345 := bstep (se 2 (by rfl) ⟨2349504, by rfl⟩ : syracuseStep 6265345 = 4699009) B4699009
theorem B370580453 : Blo 650305 370580453 := bstep (se 4 (by rfl) ⟨34741917, by rfl⟩ : syracuseStep 370580453 = 69483835) B69483835
theorem B1646183 : Blo 650305 1646183 := bstep (se 1 (by rfl) ⟨1234637, by rfl⟩ : syracuseStep 1646183 = 2469275) B2469275
theorem B827111 : Blo 650305 827111 := bstep (se 1 (by rfl) ⟨620333, by rfl⟩ : syracuseStep 827111 = 1240667) B1240667
theorem B1646345 : Blo 650305 1646345 := bstep (se 2 (by rfl) ⟨617379, by rfl⟩ : syracuseStep 1646345 = 1234759) B1234759
theorem B827263 : Blo 650305 827263 := bstep (se 1 (by rfl) ⟨620447, by rfl⟩ : syracuseStep 827263 = 1240895) B1240895
theorem B3350879 : Blo 650305 3350879 := bstep (se 1 (by rfl) ⟨2513159, by rfl⟩ : syracuseStep 3350879 = 5026319) B5026319
theorem B14066237 : Blo 650305 14066237 := bstep (se 3 (by rfl) ⟨2637419, by rfl⟩ : syracuseStep 14066237 = 5274839) B5274839
theorem B894175 : Blo 650305 894175 := bstep (se 1 (by rfl) ⟨670631, by rfl⟩ : syracuseStep 894175 = 1341263) B1341263
theorem B22062851 : Blo 650305 22062851 := bstep (se 1 (by rfl) ⟨16547138, by rfl⟩ : syracuseStep 22062851 = 33094277) B33094277
theorem B4958171 : Blo 650305 4958171 := bstep (se 1 (by rfl) ⟨3718628, by rfl⟩ : syracuseStep 4958171 = 7437257) B7437257
theorem B25405811 : Blo 650305 25405811 := bstep (se 1 (by rfl) ⟨19054358, by rfl⟩ : syracuseStep 25405811 = 38108717) B38108717
theorem B993887 : Blo 650305 993887 := bstep (se 1 (by rfl) ⟨745415, by rfl⟩ : syracuseStep 993887 = 1490831) B1490831
theorem B1650041 : Blo 650305 1650041 := bstep (se 2 (by rfl) ⟨618765, by rfl⟩ : syracuseStep 1650041 = 1237531) B1237531
theorem B5287295 : Blo 650305 5287295 := bstep (se 1 (by rfl) ⟨3965471, by rfl⟩ : syracuseStep 5287295 = 7930943) B7930943
theorem B732703 : Blo 650305 732703 := bstep (se 1 (by rfl) ⟨549527, by rfl⟩ : syracuseStep 732703 = 1099055) B1099055
theorem B4173515 : Blo 650305 4173515 := bstep (se 1 (by rfl) ⟨3130136, by rfl⟩ : syracuseStep 4173515 = 6260273) B6260273
theorem B2207519 : Blo 650305 2207519 := bstep (se 1 (by rfl) ⟨1655639, by rfl⟩ : syracuseStep 2207519 = 3311279) B3311279
theorem B3354493 : Blo 650305 3354493 := bstep (se 3 (by rfl) ⟨628967, by rfl⟩ : syracuseStep 3354493 = 1257935) B1257935
theorem B1060967 : Blo 650305 1060967 := bstep (se 1 (by rfl) ⟨795725, by rfl⟩ : syracuseStep 1060967 = 1591451) B1591451
theorem B3584135 : Blo 650305 3584135 := bstep (se 1 (by rfl) ⟨2688101, by rfl⟩ : syracuseStep 3584135 = 5376203) B5376203
theorem B12398845 : Blo 650305 12398845 := bstep (se 3 (by rfl) ⟨2324783, by rfl⟩ : syracuseStep 12398845 = 4649567) B4649567
theorem B5026067 : Blo 650305 5026067 := bstep (se 1 (by rfl) ⟨3769550, by rfl⟩ : syracuseStep 5026067 = 7539101) B7539101
theorem B4174415 : Blo 650305 4174415 := bstep (se 1 (by rfl) ⟨3130811, by rfl⟩ : syracuseStep 4174415 = 6261623) B6261623
theorem B1651367 : Blo 650305 1651367 := bstep (se 1 (by rfl) ⟨1238525, by rfl⟩ : syracuseStep 1651367 = 2477051) B2477051
theorem B3715895 : Blo 650305 3715895 := bstep (se 1 (by rfl) ⟨2786921, by rfl⟩ : syracuseStep 3715895 = 5573843) B5573843
theorem B1389395 : Blo 650305 1389395 := bstep (se 1 (by rfl) ⟨1042046, by rfl⟩ : syracuseStep 1389395 = 2084093) B2084093
theorem B11875409 : Blo 650305 11875409 := bstep (se 2 (by rfl) ⟨4453278, by rfl⟩ : syracuseStep 11875409 = 8906557) B8906557
theorem B1390583 : Blo 650305 1390583 := bstep (se 1 (by rfl) ⟨1042937, by rfl⟩ : syracuseStep 1390583 = 2085875) B2085875
theorem B735295 : Blo 650305 735295 := bstep (se 1 (by rfl) ⟨551471, by rfl⟩ : syracuseStep 735295 = 1102943) B1102943
theorem B1882399 : Blo 650305 1882399 := bstep (se 1 (by rfl) ⟨1411799, by rfl⟩ : syracuseStep 1882399 = 2823599) B2823599
theorem B1653473 : Blo 650305 1653473 := bstep (se 2 (by rfl) ⟨620052, by rfl⟩ : syracuseStep 1653473 = 1240105) B1240105
theorem B1784555 : Blo 650305 1784555 := bstep (se 1 (by rfl) ⟨1338416, by rfl⟩ : syracuseStep 1784555 = 2676833) B2676833
theorem B3292487 : Blo 650305 3292487 := bstep (se 1 (by rfl) ⟨2469365, by rfl⟩ : syracuseStep 3292487 = 4938731) B4938731
theorem B1097435 : Blo 650305 1097435 := bstep (se 1 (by rfl) ⟨823076, by rfl⟩ : syracuseStep 1097435 = 1646153) B1646153
theorem B6438737 : Blo 650305 6438737 := bstep (se 2 (by rfl) ⟨2414526, by rfl⟩ : syracuseStep 6438737 = 4829053) B4829053
theorem B1097705 : Blo 650305 1097705 := bstep (se 2 (by rfl) ⟨411639, by rfl⟩ : syracuseStep 1097705 = 823279) B823279
theorem B3620999 : Blo 650305 3620999 := bstep (se 1 (by rfl) ⟨2715749, by rfl⟩ : syracuseStep 3620999 = 5431499) B5431499
theorem B8340671 : Blo 650305 8340671 := bstep (se 1 (by rfl) ⟨6255503, by rfl⟩ : syracuseStep 8340671 = 12511007) B12511007
theorem B3294431 : Blo 650305 3294431 := bstep (se 1 (by rfl) ⟨2470823, by rfl⟩ : syracuseStep 3294431 = 4941647) B4941647
theorem B1393939 : Blo 650305 1393939 := bstep (se 1 (by rfl) ⟨1045454, by rfl⟩ : syracuseStep 1393939 = 2090909) B2090909
theorem B1787303 : Blo 650305 1787303 := bstep (se 1 (by rfl) ⟨1340477, by rfl⟩ : syracuseStep 1787303 = 2680955) B2680955
theorem B2639303 : Blo 650305 2639303 := bstep (se 1 (by rfl) ⟨1979477, by rfl⟩ : syracuseStep 2639303 = 3958955) B3958955
theorem B4179563 : Blo 650305 4179563 := bstep (se 1 (by rfl) ⟨3134672, by rfl⟩ : syracuseStep 4179563 = 6269345) B6269345
theorem B2508479 : Blo 650305 2508479 := bstep (se 1 (by rfl) ⟨1881359, by rfl⟩ : syracuseStep 2508479 = 3762719) B3762719
theorem B2345183 : Blo 650305 2345183 := bstep (se 1 (by rfl) ⟨1758887, by rfl⟩ : syracuseStep 2345183 = 3517775) B3517775
theorem B1394999 : Blo 650305 1394999 := bstep (se 1 (by rfl) ⟨1046249, by rfl⟩ : syracuseStep 1394999 = 2092499) B2092499
theorem B16730549 : Blo 650305 16730549 := bstep (se 5 (by rfl) ⟨784244, by rfl⟩ : syracuseStep 16730549 = 1568489) B1568489
theorem B5655155 : Blo 650305 5655155 := bstep (se 1 (by rfl) ⟨4241366, by rfl⟩ : syracuseStep 5655155 = 8482733) B8482733
theorem B8374913 : Blo 650305 8374913 := bstep (se 2 (by rfl) ⟨3140592, by rfl⟩ : syracuseStep 8374913 = 6281185) B6281185
theorem B8342311 : Blo 650305 8342311 := bstep (se 1 (by rfl) ⟨6256733, by rfl⟩ : syracuseStep 8342311 = 12513467) B12513467
theorem B9391099 : Blo 650305 9391099 := bstep (se 1 (by rfl) ⟨7043324, by rfl⟩ : syracuseStep 9391099 = 14086649) B14086649
theorem B10603909 : Blo 650305 10603909 := bstep (se 4 (by rfl) ⟨994116, by rfl⟩ : syracuseStep 10603909 = 1988233) B1988233
theorem B3132827 : Blo 650305 3132827 := bstep (se 1 (by rfl) ⟨2349620, by rfl⟩ : syracuseStep 3132827 = 4699241) B4699241
theorem B3755489 : Blo 650305 3755489 := bstep (se 2 (by rfl) ⟨1408308, by rfl⟩ : syracuseStep 3755489 = 2816617) B2816617
theorem B1855055 : Blo 650305 1855055 := bstep (se 1 (by rfl) ⟨1391291, by rfl⟩ : syracuseStep 1855055 = 2782583) B2782583
theorem B839279 : Blo 650305 839279 := bstep (se 1 (by rfl) ⟨629459, by rfl⟩ : syracuseStep 839279 = 1258919) B1258919
theorem B4181665 : Blo 650305 4181665 := bstep (se 2 (by rfl) ⟨1568124, by rfl⟩ : syracuseStep 4181665 = 3136249) B3136249
theorem B1101647 : Blo 650305 1101647 := bstep (se 1 (by rfl) ⟨826235, by rfl⟩ : syracuseStep 1101647 = 1652471) B1652471
theorem B3723367 : Blo 650305 3723367 := bstep (se 1 (by rfl) ⟨2792525, by rfl⟩ : syracuseStep 3723367 = 5585051) B5585051
theorem B6279767 : Blo 650305 6279767 := bstep (se 1 (by rfl) ⟨4709825, by rfl⟩ : syracuseStep 6279767 = 9419651) B9419651
theorem B7918397 : Blo 650305 7918397 := bstep (se 3 (by rfl) ⟨1484699, by rfl⟩ : syracuseStep 7918397 = 2969399) B2969399
theorem B1856479 : Blo 650305 1856479 := bstep (se 1 (by rfl) ⟨1392359, by rfl⟩ : syracuseStep 1856479 = 2784719) B2784719
theorem B1102889 : Blo 650305 1102889 := bstep (se 2 (by rfl) ⟨413583, by rfl⟩ : syracuseStep 1102889 = 827167) B827167
theorem B1463561 : Blo 650305 1463561 := bstep (se 2 (by rfl) ⟨548835, by rfl⟩ : syracuseStep 1463561 = 1097671) B1097671
theorem B1103159 : Blo 650305 1103159 := bstep (se 1 (by rfl) ⟨827369, by rfl⟩ : syracuseStep 1103159 = 1654739) B1654739
theorem B2643617 : Blo 650305 2643617 := bstep (se 2 (by rfl) ⟨991356, by rfl⟩ : syracuseStep 2643617 = 1982713) B1982713
theorem B5953283 : Blo 650305 5953283 := bstep (se 1 (by rfl) ⟨4464962, by rfl⟩ : syracuseStep 5953283 = 8929925) B8929925
theorem B2348929 : Blo 650305 2348929 := bstep (se 2 (by rfl) ⟨880848, by rfl⟩ : syracuseStep 2348929 = 1761697) B1761697
theorem B2348959 : Blo 650305 2348959 := bstep (se 1 (by rfl) ⟨1761719, by rfl⟩ : syracuseStep 2348959 = 3523439) B3523439
theorem B1464551 : Blo 650305 1464551 := bstep (se 1 (by rfl) ⟨1098413, by rfl⟩ : syracuseStep 1464551 = 2196827) B2196827
theorem B1464569 : Blo 650305 1464569 := bstep (se 2 (by rfl) ⟨549213, by rfl⟩ : syracuseStep 1464569 = 1098427) B1098427
theorem B7919947 : Blo 650305 7919947 := bstep (se 1 (by rfl) ⟨5939960, by rfl⟩ : syracuseStep 7919947 = 11879921) B11879921
theorem B1464731 : Blo 650305 1464731 := bstep (se 1 (by rfl) ⟨1098548, by rfl⟩ : syracuseStep 1464731 = 2197097) B2197097
theorem B3725783 : Blo 650305 3725783 := bstep (se 1 (by rfl) ⟨2794337, by rfl⟩ : syracuseStep 3725783 = 5588675) B5588675
theorem B1464839 : Blo 650305 1464839 := bstep (se 1 (by rfl) ⟨1098629, by rfl⟩ : syracuseStep 1464839 = 2197259) B2197259
theorem B1465019 : Blo 650305 1465019 := bstep (se 1 (by rfl) ⟨1098764, by rfl⟩ : syracuseStep 1465019 = 2197529) B2197529
theorem B1465127 : Blo 650305 1465127 := bstep (se 1 (by rfl) ⟨1098845, by rfl⟩ : syracuseStep 1465127 = 2197691) B2197691
theorem B5561783 : Blo 650305 5561783 := bstep (se 1 (by rfl) ⟨4171337, by rfl⟩ : syracuseStep 5561783 = 8342675) B8342675
theorem B1859041 : Blo 650305 1859041 := bstep (se 2 (by rfl) ⟨697140, by rfl⟩ : syracuseStep 1859041 = 1394281) B1394281
theorem B1465919 : Blo 650305 1465919 := bstep (se 1 (by rfl) ⟨1099439, by rfl⟩ : syracuseStep 1465919 = 2198879) B2198879
theorem B22667141 : Blo 650305 22667141 := bstep (se 4 (by rfl) ⟨2125044, by rfl⟩ : syracuseStep 22667141 = 4250089) B4250089
theorem B1466279 : Blo 650305 1466279 := bstep (se 1 (by rfl) ⟨1099709, by rfl⟩ : syracuseStep 1466279 = 2199419) B2199419
theorem B1007657 : Blo 650305 1007657 := bstep (se 2 (by rfl) ⟨377871, by rfl⟩ : syracuseStep 1007657 = 755743) B755743
theorem B2482883 : Blo 650305 2482883 := bstep (se 1 (by rfl) ⟨1862162, by rfl⟩ : syracuseStep 2482883 = 3724325) B3724325
theorem B975593 : Blo 650305 975593 := bstep (se 2 (by rfl) ⟨365847, by rfl⟩ : syracuseStep 975593 = 731695) B731695
theorem B975983 : Blo 650305 975983 := bstep (se 1 (by rfl) ⟨731987, by rfl⟩ : syracuseStep 975983 = 1463975) B1463975
theorem B26797175 : Blo 650305 26797175 := bstep (se 1 (by rfl) ⟨20097881, by rfl⟩ : syracuseStep 26797175 = 40195763) B40195763
theorem B976103 : Blo 650305 976103 := bstep (se 1 (by rfl) ⟨732077, by rfl⟩ : syracuseStep 976103 = 1464155) B1464155
theorem B7431425 : Blo 650305 7431425 := bstep (se 2 (by rfl) ⟨2786784, by rfl⟩ : syracuseStep 7431425 = 5573569) B5573569
theorem B976169 : Blo 650305 976169 := bstep (se 2 (by rfl) ⟨366063, by rfl⟩ : syracuseStep 976169 = 732127) B732127
theorem B2483567 : Blo 650305 2483567 := bstep (se 1 (by rfl) ⟨1862675, by rfl⟩ : syracuseStep 2483567 = 3725351) B3725351
theorem B2090423 : Blo 650305 2090423 := bstep (se 1 (by rfl) ⟨1567817, by rfl⟩ : syracuseStep 2090423 = 3135635) B3135635
theorem B1238503 : Blo 650305 1238503 := bstep (se 1 (by rfl) ⟨928877, by rfl⟩ : syracuseStep 1238503 = 1857755) B1857755
theorem B976439 : Blo 650305 976439 := bstep (se 1 (by rfl) ⟨732329, by rfl⟩ : syracuseStep 976439 = 1464659) B1464659
theorem B3860303 : Blo 650305 3860303 := bstep (se 1 (by rfl) ⟨2895227, by rfl⟩ : syracuseStep 3860303 = 5790455) B5790455
theorem B1238905 : Blo 650305 1238905 := bstep (se 2 (by rfl) ⟨464589, by rfl⟩ : syracuseStep 1238905 = 929179) B929179
theorem B976763 : Blo 650305 976763 := bstep (se 1 (by rfl) ⟨732572, by rfl⟩ : syracuseStep 976763 = 1465145) B1465145
theorem B976799 : Blo 650305 976799 := bstep (se 1 (by rfl) ⟨732599, by rfl⟩ : syracuseStep 976799 = 1465199) B1465199
theorem B977033 : Blo 650305 977033 := bstep (se 2 (by rfl) ⟨366387, by rfl⟩ : syracuseStep 977033 = 732775) B732775
theorem B5007595 : Blo 650305 5007595 := bstep (se 1 (by rfl) ⟨3755696, by rfl⟩ : syracuseStep 5007595 = 7511393) B7511393
theorem B977183 : Blo 650305 977183 := bstep (se 1 (by rfl) ⟨732887, by rfl⟩ : syracuseStep 977183 = 1465775) B1465775
theorem B977231 : Blo 650305 977231 := bstep (se 1 (by rfl) ⟨732923, by rfl⟩ : syracuseStep 977231 = 1465847) B1465847
theorem B977321 : Blo 650305 977321 := bstep (se 2 (by rfl) ⟨366495, by rfl⟩ : syracuseStep 977321 = 732991) B732991
theorem B977705 : Blo 650305 977705 := bstep (se 2 (by rfl) ⟨366639, by rfl⟩ : syracuseStep 977705 = 733279) B733279
theorem B3304313 : Blo 650305 3304313 := bstep (se 2 (by rfl) ⟨1239117, by rfl⟩ : syracuseStep 3304313 = 2478235) B2478235
theorem B977915 : Blo 650305 977915 := bstep (se 1 (by rfl) ⟨733436, by rfl⟩ : syracuseStep 977915 = 1466873) B1466873
theorem B977975 : Blo 650305 977975 := bstep (se 1 (by rfl) ⟨733481, by rfl⟩ : syracuseStep 977975 = 1466963) B1466963
theorem B650351 : Blo 650305 650351 := bstep (se 1 (by rfl) ⟨487763, by rfl⟩ : syracuseStep 650351 = 975527) B975527
theorem B978095 : Blo 650305 978095 := bstep (se 1 (by rfl) ⟨733571, by rfl⟩ : syracuseStep 978095 = 1467143) B1467143
theorem B650431 : Blo 650305 650431 := bstep (se 1 (by rfl) ⟨487823, by rfl⟩ : syracuseStep 650431 = 975647) B975647
theorem B650447 : Blo 650305 650447 := bstep (se 1 (by rfl) ⟨487835, by rfl⟩ : syracuseStep 650447 = 975671) B975671
theorem B978155 : Blo 650305 978155 := bstep (se 1 (by rfl) ⟨733616, by rfl⟩ : syracuseStep 978155 = 1467233) B1467233
theorem B650567 : Blo 650305 650567 := bstep (se 1 (by rfl) ⟨487925, by rfl⟩ : syracuseStep 650567 = 975851) B975851
theorem B42331571 : Blo 650305 42331571 := bstep (se 1 (by rfl) ⟨31748678, by rfl⟩ : syracuseStep 42331571 = 63497357) B63497357
theorem B4713977 : Blo 650305 4713977 := bstep (se 2 (by rfl) ⟨1767741, by rfl⟩ : syracuseStep 4713977 = 3535483) B3535483
theorem B1044071 : Blo 650305 1044071 := bstep (se 1 (by rfl) ⟨783053, by rfl⟩ : syracuseStep 1044071 = 1566107) B1566107
theorem B2977387 : Blo 650305 2977387 := bstep (se 1 (by rfl) ⟨2233040, by rfl⟩ : syracuseStep 2977387 = 4466081) B4466081
theorem B978815 : Blo 650305 978815 := bstep (se 1 (by rfl) ⟨734111, by rfl⟩ : syracuseStep 978815 = 1468223) B1468223
theorem B651295 : Blo 650305 651295 := bstep (se 1 (by rfl) ⟨488471, by rfl⟩ : syracuseStep 651295 = 976943) B976943
theorem B1175647 : Blo 650305 1175647 := bstep (se 1 (by rfl) ⟨881735, by rfl⟩ : syracuseStep 1175647 = 1763471) B1763471
theorem B1241183 : Blo 650305 1241183 := bstep (se 1 (by rfl) ⟨930887, by rfl⟩ : syracuseStep 1241183 = 1861775) B1861775
theorem B651471 : Blo 650305 651471 := bstep (se 1 (by rfl) ⟨488603, by rfl⟩ : syracuseStep 651471 = 977207) B977207
theorem B979151 : Blo 650305 979151 := bstep (se 1 (by rfl) ⟨734363, by rfl⟩ : syracuseStep 979151 = 1468727) B1468727
theorem B1470671 : Blo 650305 1470671 := bstep (se 1 (by rfl) ⟨1103003, by rfl⟩ : syracuseStep 1470671 = 2206007) B2206007
theorem B651591 : Blo 650305 651591 := bstep (se 1 (by rfl) ⟨488693, by rfl⟩ : syracuseStep 651591 = 977387) B977387
theorem B979271 : Blo 650305 979271 := bstep (se 1 (by rfl) ⟨734453, by rfl⟩ : syracuseStep 979271 = 1468907) B1468907
theorem B652059 : Blo 650305 652059 := bstep (se 1 (by rfl) ⟨489044, by rfl⟩ : syracuseStep 652059 = 978089) B978089
theorem B979739 : Blo 650305 979739 := bstep (se 1 (by rfl) ⟨734804, by rfl⟩ : syracuseStep 979739 = 1469609) B1469609
theorem B652335 : Blo 650305 652335 := bstep (se 1 (by rfl) ⟨489251, by rfl⟩ : syracuseStep 652335 = 978503) B978503
theorem B980015 : Blo 650305 980015 := bstep (se 1 (by rfl) ⟨735011, by rfl⟩ : syracuseStep 980015 = 1470023) B1470023
theorem B980063 : Blo 650305 980063 := bstep (se 1 (by rfl) ⟨735047, by rfl⟩ : syracuseStep 980063 = 1470095) B1470095
theorem B980123 : Blo 650305 980123 := bstep (se 1 (by rfl) ⟨735092, by rfl⟩ : syracuseStep 980123 = 1470185) B1470185
theorem B1471643 : Blo 650305 1471643 := bstep (se 1 (by rfl) ⟨1103732, by rfl⟩ : syracuseStep 1471643 = 2207465) B2207465
theorem B652455 : Blo 650305 652455 := bstep (se 1 (by rfl) ⟨489341, by rfl⟩ : syracuseStep 652455 = 978683) B978683
theorem B1176743 : Blo 650305 1176743 := bstep (se 1 (by rfl) ⟨882557, by rfl⟩ : syracuseStep 1176743 = 1765115) B1765115
theorem B980135 : Blo 650305 980135 := bstep (se 1 (by rfl) ⟨735101, by rfl⟩ : syracuseStep 980135 = 1470203) B1470203
theorem B3307067 : Blo 650305 3307067 := bstep (se 1 (by rfl) ⟨2480300, by rfl⟩ : syracuseStep 3307067 = 4960601) B4960601
theorem B652903 : Blo 650305 652903 := bstep (se 1 (by rfl) ⟨489677, by rfl⟩ : syracuseStep 652903 = 979355) B979355
theorem B980807 : Blo 650305 980807 := bstep (se 1 (by rfl) ⟨735605, by rfl⟩ : syracuseStep 980807 = 1471211) B1471211
theorem B3307391 : Blo 650305 3307391 := bstep (se 1 (by rfl) ⟨2480543, by rfl⟩ : syracuseStep 3307391 = 4961087) B4961087
theorem B653183 : Blo 650305 653183 := bstep (se 1 (by rfl) ⟨489887, by rfl⟩ : syracuseStep 653183 = 979775) B979775
theorem B3962753 : Blo 650305 3962753 := bstep (se 2 (by rfl) ⟨1486032, by rfl⟩ : syracuseStep 3962753 = 2972065) B2972065
theorem B653279 : Blo 650305 653279 := bstep (se 1 (by rfl) ⟨489959, by rfl⟩ : syracuseStep 653279 = 979919) B979919
theorem B653307 : Blo 650305 653307 := bstep (se 1 (by rfl) ⟨489980, by rfl⟩ : syracuseStep 653307 = 979961) B979961
theorem B980987 : Blo 650305 980987 := bstep (se 1 (by rfl) ⟨735740, by rfl⟩ : syracuseStep 980987 = 1471481) B1471481
theorem B653339 : Blo 650305 653339 := bstep (se 1 (by rfl) ⟨490004, by rfl⟩ : syracuseStep 653339 = 980009) B980009
theorem B653359 : Blo 650305 653359 := bstep (se 1 (by rfl) ⟨490019, by rfl⟩ : syracuseStep 653359 = 980039) B980039
theorem B981047 : Blo 650305 981047 := bstep (se 1 (by rfl) ⟨735785, by rfl⟩ : syracuseStep 981047 = 1471571) B1471571
theorem B981113 : Blo 650305 981113 := bstep (se 2 (by rfl) ⟨367917, by rfl⟩ : syracuseStep 981113 = 735835) B735835
theorem B653479 : Blo 650305 653479 := bstep (se 1 (by rfl) ⟨490109, by rfl⟩ : syracuseStep 653479 = 980219) B980219
theorem B981167 : Blo 650305 981167 := bstep (se 1 (by rfl) ⟨735875, by rfl⟩ : syracuseStep 981167 = 1471751) B1471751
theorem B1046839 : Blo 650305 1046839 := bstep (se 1 (by rfl) ⟨785129, by rfl⟩ : syracuseStep 1046839 = 1570259) B1570259
theorem B981407 : Blo 650305 981407 := bstep (se 1 (by rfl) ⟨736055, by rfl⟩ : syracuseStep 981407 = 1472111) B1472111
theorem B28572425 : Blo 650305 28572425 := bstep (se 2 (by rfl) ⟨10714659, by rfl⟩ : syracuseStep 28572425 = 21429319) B21429319
theorem B654303 : Blo 650305 654303 := bstep (se 1 (by rfl) ⟨490727, by rfl⟩ : syracuseStep 654303 = 981455) B981455
theorem B7044191 : Blo 650305 7044191 := bstep (se 1 (by rfl) ⟨5283143, by rfl⟩ : syracuseStep 7044191 = 10566287) B10566287
theorem B3308687 : Blo 650305 3308687 := bstep (se 1 (by rfl) ⟨2481515, by rfl⟩ : syracuseStep 3308687 = 4963031) B4963031
theorem B3309821 : Blo 650305 3309821 := bstep (se 3 (by rfl) ⟨620591, by rfl⟩ : syracuseStep 3309821 = 1241183) B1241183
theorem B21103253 : Blo 650305 21103253 := bstep (se 6 (by rfl) ⟨494607, by rfl⟩ : syracuseStep 21103253 = 989215) B989215
theorem B8454851 : Blo 650305 8454851 := bstep (se 1 (by rfl) ⟨6341138, by rfl⟩ : syracuseStep 8454851 = 12682277) B12682277
theorem B2196287 : Blo 650305 2196287 := bstep (se 1 (by rfl) ⟨1647215, by rfl⟩ : syracuseStep 2196287 = 3294431) B3294431
theorem B2786375 : Blo 650305 2786375 := bstep (se 1 (by rfl) ⟨2089781, by rfl⟩ : syracuseStep 2786375 = 4179563) B4179563
theorem B1672319 : Blo 650305 1672319 := bstep (se 1 (by rfl) ⟨1254239, by rfl⟩ : syracuseStep 1672319 = 2508479) B2508479
theorem B2983229 : Blo 650305 2983229 := bstep (se 3 (by rfl) ⟨559355, by rfl⟩ : syracuseStep 2983229 = 1118711) B1118711
theorem B42239717 : Blo 650305 42239717 := bstep (se 4 (by rfl) ⟨3959973, by rfl⟩ : syracuseStep 42239717 = 7919947) B7919947
theorem B37555163 : Blo 650305 37555163 := bstep (se 1 (by rfl) ⟨28166372, by rfl⟩ : syracuseStep 37555163 = 56332745) B56332745
theorem B2231401 : Blo 650305 2231401 := bstep (se 2 (by rfl) ⟨836775, by rfl⟩ : syracuseStep 2231401 = 1673551) B1673551
theorem B5278931 : Blo 650305 5278931 := bstep (se 1 (by rfl) ⟨3959198, by rfl⟩ : syracuseStep 5278931 = 7918397) B7918397
theorem B160960193 : Blo 650305 160960193 := bstep (se 2 (by rfl) ⟨60360072, by rfl⟩ : syracuseStep 160960193 = 120720145) B120720145
theorem B3968855 : Blo 650305 3968855 := bstep (se 1 (by rfl) ⟨2976641, by rfl⟩ : syracuseStep 3968855 = 5953283) B5953283
theorem B12521465 : Blo 650305 12521465 := bstep (se 2 (by rfl) ⟨4695549, by rfl⟩ : syracuseStep 12521465 = 9391099) B9391099
theorem B19075733 : Blo 650305 19075733 := bstep (se 6 (by rfl) ⟨447087, by rfl⟩ : syracuseStep 19075733 = 894175) B894175
theorem B10294141 : Blo 650305 10294141 := bstep (se 3 (by rfl) ⟨1930151, by rfl⟩ : syracuseStep 10294141 = 3860303) B3860303
theorem B5575553 : Blo 650305 5575553 := bstep (se 2 (by rfl) ⟨2090832, by rfl⟩ : syracuseStep 5575553 = 4181665) B4181665
theorem B3707855 : Blo 650305 3707855 := bstep (se 1 (by rfl) ⟨2780891, by rfl⟩ : syracuseStep 3707855 = 5561783) B5561783
theorem B2233919 : Blo 650305 2233919 := bstep (se 1 (by rfl) ⟨1675439, by rfl⟩ : syracuseStep 2233919 = 3350879) B3350879
theorem B9377491 : Blo 650305 9377491 := bstep (se 1 (by rfl) ⟨7033118, by rfl⟩ : syracuseStep 9377491 = 14066237) B14066237
theorem B17864783 : Blo 650305 17864783 := bstep (se 1 (by rfl) ⟨13398587, by rfl⟩ : syracuseStep 17864783 = 26797175) B26797175
theorem B4954283 : Blo 650305 4954283 := bstep (se 1 (by rfl) ⟨3715712, by rfl⟩ : syracuseStep 4954283 = 7431425) B7431425
theorem B15080413 : Blo 650305 15080413 := bstep (se 3 (by rfl) ⟨2827577, by rfl⟩ : syracuseStep 15080413 = 5655155) B5655155
theorem B662591 : Blo 650305 662591 := bstep (se 1 (by rfl) ⟨496943, by rfl⟩ : syracuseStep 662591 = 993887) B993887
theorem B2202875 : Blo 650305 2202875 := bstep (se 1 (by rfl) ⟨1652156, by rfl⟩ : syracuseStep 2202875 = 3304313) B3304313
theorem B28221047 : Blo 650305 28221047 := bstep (se 1 (by rfl) ⟨21165785, by rfl⟩ : syracuseStep 28221047 = 42331571) B42331571
theorem B696047 : Blo 650305 696047 := bstep (se 1 (by rfl) ⟨522035, by rfl⟩ : syracuseStep 696047 = 1044071) B1044071
theorem B4464557 : Blo 650305 4464557 := bstep (se 3 (by rfl) ⟨837104, by rfl⟩ : syracuseStep 4464557 = 1674209) B1674209
theorem B3350711 : Blo 650305 3350711 := bstep (se 1 (by rfl) ⟨2513033, by rfl⟩ : syracuseStep 3350711 = 5026067) B5026067
theorem B926263 : Blo 650305 926263 := bstep (se 1 (by rfl) ⟨694697, by rfl⟩ : syracuseStep 926263 = 1389395) B1389395
theorem B14099453 : Blo 650305 14099453 := bstep (se 3 (by rfl) ⟨2643647, by rfl⟩ : syracuseStep 14099453 = 5287295) B5287295
theorem B2204711 : Blo 650305 2204711 := bstep (se 1 (by rfl) ⟨1653533, by rfl⟩ : syracuseStep 2204711 = 3307067) B3307067
theorem B2204927 : Blo 650305 2204927 := bstep (se 1 (by rfl) ⟨1653695, by rfl⟩ : syracuseStep 2204927 = 3307391) B3307391
theorem B927055 : Blo 650305 927055 := bstep (se 1 (by rfl) ⟨695291, by rfl⟩ : syracuseStep 927055 = 1390583) B1390583
theorem B2238077 : Blo 650305 2238077 := bstep (se 3 (by rfl) ⟨419639, by rfl⟩ : syracuseStep 2238077 = 839279) B839279
theorem B1189703 : Blo 650305 1189703 := bstep (se 1 (by rfl) ⟨892277, by rfl⟩ : syracuseStep 1189703 = 1784555) B1784555
theorem B19048283 : Blo 650305 19048283 := bstep (se 1 (by rfl) ⟨14286212, by rfl⟩ : syracuseStep 19048283 = 28572425) B28572425
theorem B2205629 : Blo 650305 2205629 := bstep (se 3 (by rfl) ⟨413555, by rfl⟩ : syracuseStep 2205629 = 827111) B827111
theorem B4696127 : Blo 650305 4696127 := bstep (se 1 (by rfl) ⟨3522095, by rfl⟩ : syracuseStep 4696127 = 7044191) B7044191
theorem B2205791 : Blo 650305 2205791 := bstep (se 1 (by rfl) ⟨1654343, by rfl⟩ : syracuseStep 2205791 = 3308687) B3308687
theorem B731623 : Blo 650305 731623 := bstep (se 1 (by rfl) ⟨548717, by rfl⟩ : syracuseStep 731623 = 1097435) B1097435
theorem B731803 : Blo 650305 731803 := bstep (se 1 (by rfl) ⟨548852, by rfl⟩ : syracuseStep 731803 = 1097705) B1097705
theorem B2207087 : Blo 650305 2207087 := bstep (se 1 (by rfl) ⟨1655315, by rfl⟩ : syracuseStep 2207087 = 3310631) B3310631
theorem B2207735 : Blo 650305 2207735 := bstep (se 1 (by rfl) ⟨1655801, by rfl⟩ : syracuseStep 2207735 = 3311603) B3311603
theorem B929999 : Blo 650305 929999 := bstep (se 1 (by rfl) ⟨697499, by rfl⟩ : syracuseStep 929999 = 1394999) B1394999
theorem B11153699 : Blo 650305 11153699 := bstep (se 1 (by rfl) ⟨8365274, by rfl⟩ : syracuseStep 11153699 = 16730549) B16730549
theorem B5583275 : Blo 650305 5583275 := bstep (se 1 (by rfl) ⟨4187456, by rfl⟩ : syracuseStep 5583275 = 8374913) B8374913
theorem B1651337 : Blo 650305 1651337 := bstep (se 2 (by rfl) ⟨619251, by rfl⟩ : syracuseStep 1651337 = 1238503) B1238503
theorem B1651873 : Blo 650305 1651873 := bstep (se 2 (by rfl) ⟨619452, by rfl⟩ : syracuseStep 1651873 = 1238905) B1238905
theorem B734431 : Blo 650305 734431 := bstep (se 1 (by rfl) ⟨550823, by rfl⟩ : syracuseStep 734431 = 1101647) B1101647
theorem B5289499 : Blo 650305 5289499 := bstep (se 1 (by rfl) ⟨3967124, by rfl⟩ : syracuseStep 5289499 = 7934249) B7934249
theorem B735259 : Blo 650305 735259 := bstep (se 1 (by rfl) ⟨551444, by rfl⟩ : syracuseStep 735259 = 1102889) B1102889
theorem B735439 : Blo 650305 735439 := bstep (se 1 (by rfl) ⟨551579, by rfl⟩ : syracuseStep 735439 = 1103159) B1103159
theorem B11123081 : Blo 650305 11123081 := bstep (se 2 (by rfl) ⟨4171155, by rfl⟩ : syracuseStep 11123081 = 8342311) B8342311
theorem B4766141 : Blo 650305 4766141 := bstep (se 3 (by rfl) ⟨893651, by rfl⟩ : syracuseStep 4766141 = 1787303) B1787303
theorem B4700855 : Blo 650305 4700855 := bstep (se 1 (by rfl) ⟨3525641, by rfl⟩ : syracuseStep 4700855 = 7051283) B7051283
theorem B14138545 : Blo 650305 14138545 := bstep (se 2 (by rfl) ⟨5301954, by rfl⟩ : syracuseStep 14138545 = 10603909) B10603909
theorem B247053635 : Blo 650305 247053635 := bstep (se 1 (by rfl) ⟨185290226, by rfl⟩ : syracuseStep 247053635 = 370580453) B370580453
theorem B40058549 : Blo 650305 40058549 := bstep (se 5 (by rfl) ⟨1877744, by rfl⟩ : syracuseStep 40058549 = 3755489) B3755489
theorem B1097455 : Blo 650305 1097455 := bstep (se 1 (by rfl) ⟨823091, by rfl⟩ : syracuseStep 1097455 = 1646183) B1646183
theorem B4472657 : Blo 650305 4472657 := bstep (se 2 (by rfl) ⟨1677246, by rfl⟩ : syracuseStep 4472657 = 3354493) B3354493
theorem B1097563 : Blo 650305 1097563 := bstep (se 1 (by rfl) ⟨823172, by rfl⟩ : syracuseStep 1097563 = 1646345) B1646345
theorem B671771 : Blo 650305 671771 := bstep (se 1 (by rfl) ⟨503828, by rfl⟩ : syracuseStep 671771 = 1007657) B1007657
theorem B4964489 : Blo 650305 4964489 := bstep (se 2 (by rfl) ⟨1861683, by rfl⟩ : syracuseStep 4964489 = 3723367) B3723367
theorem B16531793 : Blo 650305 16531793 := bstep (se 2 (by rfl) ⟨6199422, by rfl⟩ : syracuseStep 16531793 = 12398845) B12398845
theorem B1655255 : Blo 650305 1655255 := bstep (se 1 (by rfl) ⟨1241441, by rfl⟩ : syracuseStep 1655255 = 2482883) B2482883
theorem B1655711 : Blo 650305 1655711 := bstep (se 1 (by rfl) ⟨1241783, by rfl⟩ : syracuseStep 1655711 = 2483567) B2483567
theorem B1393615 : Blo 650305 1393615 := bstep (se 1 (by rfl) ⟨1045211, by rfl⟩ : syracuseStep 1393615 = 2090423) B2090423
theorem B2475305 : Blo 650305 2475305 := bstep (se 2 (by rfl) ⟨928239, by rfl⟩ : syracuseStep 2475305 = 1856479) B1856479
theorem B1100027 : Blo 650305 1100027 := bstep (se 1 (by rfl) ⟨825020, by rfl⟩ : syracuseStep 1100027 = 1650041) B1650041
theorem B3131905 : Blo 650305 3131905 := bstep (se 2 (by rfl) ⟨1174464, by rfl⟩ : syracuseStep 3131905 = 2348929) B2348929
theorem B3131945 : Blo 650305 3131945 := bstep (se 2 (by rfl) ⟨1174479, by rfl⟩ : syracuseStep 3131945 = 2348959) B2348959
theorem B707311 : Blo 650305 707311 := bstep (se 1 (by rfl) ⟨530483, by rfl⟩ : syracuseStep 707311 = 1060967) B1060967
theorem B2509865 : Blo 650305 2509865 := bstep (se 2 (by rfl) ⟨941199, by rfl⟩ : syracuseStep 2509865 = 1882399) B1882399
theorem B1395785 : Blo 650305 1395785 := bstep (se 2 (by rfl) ⟨523419, by rfl⟩ : syracuseStep 1395785 = 1046839) B1046839
theorem B1100911 : Blo 650305 1100911 := bstep (se 1 (by rfl) ⟨825683, by rfl⟩ : syracuseStep 1100911 = 1651367) B1651367
theorem B2477263 : Blo 650305 2477263 := bstep (se 1 (by rfl) ⟨1857947, by rfl⟩ : syracuseStep 2477263 = 3715895) B3715895
theorem B15879397 : Blo 650305 15879397 := bstep (se 4 (by rfl) ⟨1488693, by rfl⟩ : syracuseStep 15879397 = 2977387) B2977387
theorem B7916939 : Blo 650305 7916939 := bstep (se 1 (by rfl) ⟨5937704, by rfl⟩ : syracuseStep 7916939 = 11875409) B11875409
theorem B2641835 : Blo 650305 2641835 := bstep (se 1 (by rfl) ⟨1981376, by rfl⟩ : syracuseStep 2641835 = 3962753) B3962753
theorem B1102315 : Blo 650305 1102315 := bstep (se 1 (by rfl) ⟨826736, by rfl⟩ : syracuseStep 1102315 = 1653473) B1653473
theorem B2478721 : Blo 650305 2478721 := bstep (se 2 (by rfl) ⟨929520, by rfl⟩ : syracuseStep 2478721 = 1859041) B1859041
theorem B60445709 : Blo 650305 60445709 := bstep (se 3 (by rfl) ⟨11333570, by rfl⟩ : syracuseStep 60445709 = 22667141) B22667141
theorem B1103017 : Blo 650305 1103017 := bstep (se 2 (by rfl) ⟨413631, by rfl⟩ : syracuseStep 1103017 = 827263) B827263
theorem B2413999 : Blo 650305 2413999 := bstep (se 1 (by rfl) ⟨1810499, by rfl⟩ : syracuseStep 2413999 = 3620999) B3620999
theorem B9557693 : Blo 650305 9557693 := bstep (se 3 (by rfl) ⟨1792067, by rfl⟩ : syracuseStep 9557693 = 3584135) B3584135
theorem B1464047 : Blo 650305 1464047 := bstep (se 1 (by rfl) ⟨1098035, by rfl⟩ : syracuseStep 1464047 = 2196071) B2196071
theorem B5560447 : Blo 650305 5560447 := bstep (se 1 (by rfl) ⟨4170335, by rfl⟩ : syracuseStep 5560447 = 8340671) B8340671
theorem B1759535 : Blo 650305 1759535 := bstep (se 1 (by rfl) ⟨1319651, by rfl⟩ : syracuseStep 1759535 = 2639303) B2639303
theorem B1563455 : Blo 650305 1563455 := bstep (se 1 (by rfl) ⟨1172591, by rfl⟩ : syracuseStep 1563455 = 2345183) B2345183
theorem B1858427 : Blo 650305 1858427 := bstep (se 1 (by rfl) ⟨1393820, by rfl⟩ : syracuseStep 1858427 = 2787641) B2787641
theorem B2088551 : Blo 650305 2088551 := bstep (se 1 (by rfl) ⟨1566413, by rfl⟩ : syracuseStep 2088551 = 3132827) B3132827
theorem B1236703 : Blo 650305 1236703 := bstep (se 1 (by rfl) ⟨927527, by rfl⟩ : syracuseStep 1236703 = 1855055) B1855055
theorem B7954301 : Blo 650305 7954301 := bstep (se 3 (by rfl) ⟨1491431, by rfl⟩ : syracuseStep 7954301 = 2982863) B2982863
theorem B4939703 : Blo 650305 4939703 := bstep (se 1 (by rfl) ⟨3704777, by rfl⟩ : syracuseStep 4939703 = 7409555) B7409555
theorem B1466351 : Blo 650305 1466351 := bstep (se 1 (by rfl) ⟨1099763, by rfl⟩ : syracuseStep 1466351 = 2199527) B2199527
theorem B1466603 : Blo 650305 1466603 := bstep (se 1 (by rfl) ⟨1099952, by rfl⟩ : syracuseStep 1466603 = 2199905) B2199905
theorem B6676793 : Blo 650305 6676793 := bstep (se 2 (by rfl) ⟨2503797, by rfl⟩ : syracuseStep 6676793 = 5007595) B5007595
theorem B6250891 : Blo 650305 6250891 := bstep (se 1 (by rfl) ⟨4688168, by rfl⟩ : syracuseStep 6250891 = 9376337) B9376337
theorem B4186511 : Blo 650305 4186511 := bstep (se 1 (by rfl) ⟨3139883, by rfl⟩ : syracuseStep 4186511 = 6279767) B6279767
theorem B3301883 : Blo 650305 3301883 := bstep (se 1 (by rfl) ⟨2476412, by rfl⟩ : syracuseStep 3301883 = 4952825) B4952825
theorem B22569635 : Blo 650305 22569635 := bstep (se 1 (by rfl) ⟨16927226, by rfl⟩ : syracuseStep 22569635 = 33854453) B33854453
theorem B975707 : Blo 650305 975707 := bstep (se 1 (by rfl) ⟨731780, by rfl⟩ : syracuseStep 975707 = 1463561) B1463561
theorem B1762411 : Blo 650305 1762411 := bstep (se 1 (by rfl) ⟨1321808, by rfl⟩ : syracuseStep 1762411 = 2643617) B2643617
theorem B976367 : Blo 650305 976367 := bstep (se 1 (by rfl) ⟨732275, by rfl⟩ : syracuseStep 976367 = 1464551) B1464551
theorem B976379 : Blo 650305 976379 := bstep (se 1 (by rfl) ⟨732284, by rfl⟩ : syracuseStep 976379 = 1464569) B1464569
theorem B976487 : Blo 650305 976487 := bstep (se 1 (by rfl) ⟨732365, by rfl⟩ : syracuseStep 976487 = 1464731) B1464731
theorem B2483855 : Blo 650305 2483855 := bstep (se 1 (by rfl) ⟨1862891, by rfl⟩ : syracuseStep 2483855 = 3725783) B3725783
theorem B976559 : Blo 650305 976559 := bstep (se 1 (by rfl) ⟨732419, by rfl⟩ : syracuseStep 976559 = 1464839) B1464839
theorem B976679 : Blo 650305 976679 := bstep (se 1 (by rfl) ⟨732509, by rfl⟩ : syracuseStep 976679 = 1465019) B1465019
theorem B976751 : Blo 650305 976751 := bstep (se 1 (by rfl) ⟨732563, by rfl⟩ : syracuseStep 976751 = 1465127) B1465127
theorem B976937 : Blo 650305 976937 := bstep (se 2 (by rfl) ⟨366351, by rfl⟩ : syracuseStep 976937 = 732703) B732703
theorem B977279 : Blo 650305 977279 := bstep (se 1 (by rfl) ⟨732959, by rfl⟩ : syracuseStep 977279 = 1465919) B1465919
theorem B977519 : Blo 650305 977519 := bstep (se 1 (by rfl) ⟨733139, by rfl⟩ : syracuseStep 977519 = 1466279) B1466279
theorem B1567529 : Blo 650305 1567529 := bstep (se 2 (by rfl) ⟨587823, by rfl⟩ : syracuseStep 1567529 = 1175647) B1175647
theorem B650395 : Blo 650305 650395 := bstep (se 1 (by rfl) ⟨487796, by rfl⟩ : syracuseStep 650395 = 975593) B975593
theorem B650655 : Blo 650305 650655 := bstep (se 1 (by rfl) ⟨487991, by rfl⟩ : syracuseStep 650655 = 975983) B975983
theorem B650735 : Blo 650305 650735 := bstep (se 1 (by rfl) ⟨488051, by rfl⟩ : syracuseStep 650735 = 976103) B976103
theorem B650779 : Blo 650305 650779 := bstep (se 1 (by rfl) ⟨488084, by rfl⟩ : syracuseStep 650779 = 976169) B976169
theorem B650959 : Blo 650305 650959 := bstep (se 1 (by rfl) ⟨488219, by rfl⟩ : syracuseStep 650959 = 976439) B976439
theorem B14708567 : Blo 650305 14708567 := bstep (se 1 (by rfl) ⟨11031425, by rfl⟩ : syracuseStep 14708567 = 22062851) B22062851
theorem B651175 : Blo 650305 651175 := bstep (se 1 (by rfl) ⟨488381, by rfl⟩ : syracuseStep 651175 = 976763) B976763
theorem B651199 : Blo 650305 651199 := bstep (se 1 (by rfl) ⟨488399, by rfl⟩ : syracuseStep 651199 = 976799) B976799
theorem B3305447 : Blo 650305 3305447 := bstep (se 1 (by rfl) ⟨2479085, by rfl⟩ : syracuseStep 3305447 = 4958171) B4958171
theorem B651355 : Blo 650305 651355 := bstep (se 1 (by rfl) ⟨488516, by rfl⟩ : syracuseStep 651355 = 977033) B977033
theorem B7434341 : Blo 650305 7434341 := bstep (se 4 (by rfl) ⟨696969, by rfl⟩ : syracuseStep 7434341 = 1393939) B1393939
theorem B651455 : Blo 650305 651455 := bstep (se 1 (by rfl) ⟨488591, by rfl⟩ : syracuseStep 651455 = 977183) B977183
theorem B651487 : Blo 650305 651487 := bstep (se 1 (by rfl) ⟨488615, by rfl⟩ : syracuseStep 651487 = 977231) B977231
theorem B16937207 : Blo 650305 16937207 := bstep (se 1 (by rfl) ⟨12702905, by rfl⟩ : syracuseStep 16937207 = 25405811) B25405811
theorem B651547 : Blo 650305 651547 := bstep (se 1 (by rfl) ⟨488660, by rfl⟩ : syracuseStep 651547 = 977321) B977321
theorem B651803 : Blo 650305 651803 := bstep (se 1 (by rfl) ⟨488852, by rfl⟩ : syracuseStep 651803 = 977705) B977705
theorem B651943 : Blo 650305 651943 := bstep (se 1 (by rfl) ⟨488957, by rfl⟩ : syracuseStep 651943 = 977915) B977915
theorem B651983 : Blo 650305 651983 := bstep (se 1 (by rfl) ⟨488987, by rfl⟩ : syracuseStep 651983 = 977975) B977975
theorem B652063 : Blo 650305 652063 := bstep (se 1 (by rfl) ⟨489047, by rfl⟩ : syracuseStep 652063 = 978095) B978095
theorem B652103 : Blo 650305 652103 := bstep (se 1 (by rfl) ⟨489077, by rfl⟩ : syracuseStep 652103 = 978155) B978155
theorem B3142651 : Blo 650305 3142651 := bstep (se 1 (by rfl) ⟨2356988, by rfl⟩ : syracuseStep 3142651 = 4713977) B4713977
theorem B2782343 : Blo 650305 2782343 := bstep (se 1 (by rfl) ⟨2086757, by rfl⟩ : syracuseStep 2782343 = 4173515) B4173515
theorem B1471679 : Blo 650305 1471679 := bstep (se 1 (by rfl) ⟨1103759, by rfl⟩ : syracuseStep 1471679 = 2207519) B2207519
theorem B652543 : Blo 650305 652543 := bstep (se 1 (by rfl) ⟨489407, by rfl⟩ : syracuseStep 652543 = 978815) B978815
theorem B980393 : Blo 650305 980393 := bstep (se 2 (by rfl) ⟨367647, by rfl⟩ : syracuseStep 980393 = 735295) B735295
theorem B652767 : Blo 650305 652767 := bstep (se 1 (by rfl) ⟨489575, by rfl⟩ : syracuseStep 652767 = 979151) B979151
theorem B980447 : Blo 650305 980447 := bstep (se 1 (by rfl) ⟨735335, by rfl⟩ : syracuseStep 980447 = 1470671) B1470671
theorem B652847 : Blo 650305 652847 := bstep (se 1 (by rfl) ⟨489635, by rfl⟩ : syracuseStep 652847 = 979271) B979271
theorem B2782943 : Blo 650305 2782943 := bstep (se 1 (by rfl) ⟨2087207, by rfl⟩ : syracuseStep 2782943 = 4174415) B4174415
theorem B653159 : Blo 650305 653159 := bstep (se 1 (by rfl) ⟨489869, by rfl⟩ : syracuseStep 653159 = 979739) B979739
theorem B8353793 : Blo 650305 8353793 := bstep (se 2 (by rfl) ⟨3132672, by rfl⟩ : syracuseStep 8353793 = 6265345) B6265345
theorem B653343 : Blo 650305 653343 := bstep (se 1 (by rfl) ⟨490007, by rfl⟩ : syracuseStep 653343 = 980015) B980015
theorem B653375 : Blo 650305 653375 := bstep (se 1 (by rfl) ⟨490031, by rfl⟩ : syracuseStep 653375 = 980063) B980063
theorem B653415 : Blo 650305 653415 := bstep (se 1 (by rfl) ⟨490061, by rfl⟩ : syracuseStep 653415 = 980123) B980123
theorem B981095 : Blo 650305 981095 := bstep (se 1 (by rfl) ⟨735821, by rfl⟩ : syracuseStep 981095 = 1471643) B1471643
theorem B784495 : Blo 650305 784495 := bstep (se 1 (by rfl) ⟨588371, by rfl⟩ : syracuseStep 784495 = 1176743) B1176743
theorem B653423 : Blo 650305 653423 := bstep (se 1 (by rfl) ⟨490067, by rfl⟩ : syracuseStep 653423 = 980135) B980135
theorem B653871 : Blo 650305 653871 := bstep (se 1 (by rfl) ⟨490403, by rfl⟩ : syracuseStep 653871 = 980807) B980807
theorem B653991 : Blo 650305 653991 := bstep (se 1 (by rfl) ⟨490493, by rfl⟩ : syracuseStep 653991 = 980987) B980987
theorem B654031 : Blo 650305 654031 := bstep (se 1 (by rfl) ⟨490523, by rfl⟩ : syracuseStep 654031 = 981047) B981047
theorem B654075 : Blo 650305 654075 := bstep (se 1 (by rfl) ⟨490556, by rfl⟩ : syracuseStep 654075 = 981113) B981113
theorem B654111 : Blo 650305 654111 := bstep (se 1 (by rfl) ⟨490583, by rfl⟩ : syracuseStep 654111 = 981167) B981167
theorem B654271 : Blo 650305 654271 := bstep (se 1 (by rfl) ⟨490703, by rfl⟩ : syracuseStep 654271 = 981407) B981407
theorem B17169965 : Blo 650305 17169965 := bstep (se 3 (by rfl) ⟨3219368, by rfl⟩ : syracuseStep 17169965 = 6438737) B6438737
theorem B2194991 : Blo 650305 2194991 := bstep (se 1 (by rfl) ⟨1646243, by rfl⟩ : syracuseStep 2194991 = 3292487) B3292487
theorem B3309659 : Blo 650305 3309659 := bstep (se 1 (by rfl) ⟨2482244, by rfl⟩ : syracuseStep 3309659 = 4964489) B4964489
theorem B5636567 : Blo 650305 5636567 := bstep (se 1 (by rfl) ⟨4227425, by rfl⟩ : syracuseStep 5636567 = 8454851) B8454851
theorem B1114879 : Blo 650305 1114879 := bstep (se 1 (by rfl) ⟨836159, by rfl⟩ : syracuseStep 1114879 = 1672319) B1672319
theorem B25036775 : Blo 650305 25036775 := bstep (se 1 (by rfl) ⟨18777581, by rfl⟩ : syracuseStep 25036775 = 37555163) B37555163
theorem B1673243 : Blo 650305 1673243 := bstep (se 1 (by rfl) ⟨1254932, by rfl⟩ : syracuseStep 1673243 = 2509865) B2509865
theorem B5277959 : Blo 650305 5277959 := bstep (se 1 (by rfl) ⟨3958469, by rfl⟩ : syracuseStep 5277959 = 7916939) B7916939
theorem B12717155 : Blo 650305 12717155 := bstep (se 1 (by rfl) ⟨9537866, by rfl⟩ : syracuseStep 12717155 = 19075733) B19075733
theorem B3772325 : Blo 650305 3772325 := bstep (se 4 (by rfl) ⟨353655, by rfl⟩ : syracuseStep 3772325 = 707311) B707311
theorem B21172529 : Blo 650305 21172529 := bstep (se 2 (by rfl) ⟨7939698, by rfl⟩ : syracuseStep 21172529 = 15879397) B15879397
theorem B5968205 : Blo 650305 5968205 := bstep (se 3 (by rfl) ⟨1119038, by rfl⟩ : syracuseStep 5968205 = 2238077) B2238077
theorem B18814031 : Blo 650305 18814031 := bstep (se 1 (by rfl) ⟨14110523, by rfl⟩ : syracuseStep 18814031 = 28221047) B28221047
theorem B2233807 : Blo 650305 2233807 := bstep (se 1 (by rfl) ⟨1675355, by rfl⟩ : syracuseStep 2233807 = 3350711) B3350711
theorem B2791007 : Blo 650305 2791007 := bstep (se 1 (by rfl) ⟨2093255, by rfl⟩ : syracuseStep 2791007 = 4186511) B4186511
theorem B2201255 : Blo 650305 2201255 := bstep (se 1 (by rfl) ⟨1650941, by rfl⟩ : syracuseStep 2201255 = 3301883) B3301883
theorem B793135 : Blo 650305 793135 := bstep (se 1 (by rfl) ⟨594851, by rfl⟩ : syracuseStep 793135 = 1189703) B1189703
theorem B2202497 : Blo 650305 2202497 := bstep (se 2 (by rfl) ⟨825936, by rfl⟩ : syracuseStep 2202497 = 1651873) B1651873
theorem B3218665 : Blo 650305 3218665 := bstep (se 2 (by rfl) ⟨1206999, by rfl⟩ : syracuseStep 3218665 = 2413999) B2413999
theorem B7052665 : Blo 650305 7052665 := bstep (se 2 (by rfl) ⟨2644749, by rfl⟩ : syracuseStep 7052665 = 5289499) B5289499
theorem B9805711 : Blo 650305 9805711 := bstep (se 1 (by rfl) ⟨7354283, by rfl⟩ : syracuseStep 9805711 = 14708567) B14708567
theorem B2203631 : Blo 650305 2203631 := bstep (se 1 (by rfl) ⟨1652723, by rfl⟩ : syracuseStep 2203631 = 3305447) B3305447
theorem B4956227 : Blo 650305 4956227 := bstep (se 1 (by rfl) ⟨3717170, by rfl⟩ : syracuseStep 4956227 = 7434341) B7434341
theorem B7413929 : Blo 650305 7413929 := bstep (se 2 (by rfl) ⟨2780223, by rfl⟩ : syracuseStep 7413929 = 5560447) B5560447
theorem B18851393 : Blo 650305 18851393 := bstep (se 2 (by rfl) ⟨7069272, by rfl⟩ : syracuseStep 18851393 = 14138545) B14138545
theorem B7415387 : Blo 650305 7415387 := bstep (se 1 (by rfl) ⟨5561540, by rfl⟩ : syracuseStep 7415387 = 11123081) B11123081
theorem B164702423 : Blo 650305 164702423 := bstep (se 1 (by rfl) ⟨123526817, by rfl⟩ : syracuseStep 164702423 = 247053635) B247053635
theorem B1648937 : Blo 650305 1648937 := bstep (se 2 (by rfl) ⟨618351, by rfl⟩ : syracuseStep 1648937 = 1236703) B1236703
theorem B11446643 : Blo 650305 11446643 := bstep (se 1 (by rfl) ⟨8584982, by rfl⟩ : syracuseStep 11446643 = 17169965) B17169965
theorem B2206547 : Blo 650305 2206547 := bstep (se 1 (by rfl) ⟨1654910, by rfl⟩ : syracuseStep 2206547 = 3309821) B3309821
theorem B11021195 : Blo 650305 11021195 := bstep (se 1 (by rfl) ⟨8265896, by rfl⟩ : syracuseStep 11021195 = 16531793) B16531793
theorem B14068835 : Blo 650305 14068835 := bstep (se 1 (by rfl) ⟨10551626, by rfl⟩ : syracuseStep 14068835 = 21103253) B21103253
theorem B8334521 : Blo 650305 8334521 := bstep (se 2 (by rfl) ⟨3125445, by rfl⟩ : syracuseStep 8334521 = 6250891) B6250891
theorem B1650203 : Blo 650305 1650203 := bstep (se 1 (by rfl) ⟨1237652, by rfl⟩ : syracuseStep 1650203 = 2475305) B2475305
theorem B28159811 : Blo 650305 28159811 := bstep (se 1 (by rfl) ⟨21119858, by rfl⟩ : syracuseStep 28159811 = 42239717) B42239717
theorem B733351 : Blo 650305 733351 := bstep (se 1 (by rfl) ⟨550013, by rfl⟩ : syracuseStep 733351 = 1100027) B1100027
theorem B930523 : Blo 650305 930523 := bstep (se 1 (by rfl) ⟨697892, by rfl⟩ : syracuseStep 930523 = 1395785) B1395785
theorem B3519287 : Blo 650305 3519287 := bstep (se 1 (by rfl) ⟨2639465, by rfl⟩ : syracuseStep 3519287 = 5278931) B5278931
theorem B3717035 : Blo 650305 3717035 := bstep (se 1 (by rfl) ⟨2787776, by rfl⟩ : syracuseStep 3717035 = 5575553) B5575553
theorem B2471903 : Blo 650305 2471903 := bstep (se 1 (by rfl) ⟨1853927, by rfl⟩ : syracuseStep 2471903 = 3707855) B3707855
theorem B4175873 : Blo 650305 4175873 := bstep (se 2 (by rfl) ⟨1565952, by rfl⟩ : syracuseStep 4175873 = 3131905) B3131905
theorem B1489279 : Blo 650305 1489279 := bstep (se 1 (by rfl) ⟨1116959, by rfl⟩ : syracuseStep 1489279 = 2233919) B2233919
theorem B6371795 : Blo 650305 6371795 := bstep (se 1 (by rfl) ⟨4778846, by rfl⟩ : syracuseStep 6371795 = 9557693) B9557693
theorem B11909855 : Blo 650305 11909855 := bstep (se 1 (by rfl) ⟨8932391, by rfl⟩ : syracuseStep 11909855 = 17864783) B17864783
theorem B3293135 : Blo 650305 3293135 := bstep (se 1 (by rfl) ⟨2469851, by rfl⟩ : syracuseStep 3293135 = 4939703) B4939703
theorem B1655903 : Blo 650305 1655903 := bstep (se 1 (by rfl) ⟨1241927, by rfl⟩ : syracuseStep 1655903 = 2483855) B2483855
theorem B12698855 : Blo 650305 12698855 := bstep (se 1 (by rfl) ⟨9524141, by rfl⟩ : syracuseStep 12698855 = 19048283) B19048283
theorem B3130751 : Blo 650305 3130751 := bstep (se 1 (by rfl) ⟨2348063, by rfl⟩ : syracuseStep 3130751 = 4696127) B4696127
theorem B12503321 : Blo 650305 12503321 := bstep (se 2 (by rfl) ⟨4688745, by rfl⟩ : syracuseStep 12503321 = 9377491) B9377491
theorem B11291471 : Blo 650305 11291471 := bstep (se 1 (by rfl) ⟨8468603, by rfl⟩ : syracuseStep 11291471 = 16937207) B16937207
theorem B3722183 : Blo 650305 3722183 := bstep (se 1 (by rfl) ⟨2791637, by rfl⟩ : syracuseStep 3722183 = 5583275) B5583275
theorem B1100891 : Blo 650305 1100891 := bstep (se 1 (by rfl) ⟨825668, by rfl⟩ : syracuseStep 1100891 = 1651337) B1651337
theorem B1854895 : Blo 650305 1854895 := bstep (se 1 (by rfl) ⟨1391171, by rfl⟩ : syracuseStep 1854895 = 2782343) B2782343
theorem B1855295 : Blo 650305 1855295 := bstep (se 1 (by rfl) ⟨1391471, by rfl⟩ : syracuseStep 1855295 = 2782943) B2782943
theorem B20107217 : Blo 650305 20107217 := bstep (se 2 (by rfl) ⟨7540206, by rfl⟩ : syracuseStep 20107217 = 15080413) B15080413
theorem B3133903 : Blo 650305 3133903 := bstep (se 1 (by rfl) ⟨2350427, by rfl⟩ : syracuseStep 3133903 = 4700855) B4700855
theorem B1856125 : Blo 650305 1856125 := bstep (se 3 (by rfl) ⟨348023, by rfl⟩ : syracuseStep 1856125 = 696047) B696047
theorem B1463273 : Blo 650305 1463273 := bstep (se 2 (by rfl) ⟨548727, by rfl⟩ : syracuseStep 1463273 = 1097455) B1097455
theorem B1463327 : Blo 650305 1463327 := bstep (se 1 (by rfl) ⟨1097495, by rfl⟩ : syracuseStep 1463327 = 2194991) B2194991
theorem B1463417 : Blo 650305 1463417 := bstep (se 2 (by rfl) ⟨548781, by rfl⟩ : syracuseStep 1463417 = 1097563) B1097563
theorem B1791389 : Blo 650305 1791389 := bstep (se 3 (by rfl) ⟨335885, by rfl⟩ : syracuseStep 1791389 = 671771) B671771
theorem B1103503 : Blo 650305 1103503 := bstep (se 1 (by rfl) ⟨827627, by rfl⟩ : syracuseStep 1103503 = 1655255) B1655255
theorem B2479997 : Blo 650305 2479997 := bstep (se 3 (by rfl) ⟨464999, by rfl⟩ : syracuseStep 2479997 = 929999) B929999
theorem B1464191 : Blo 650305 1464191 := bstep (se 1 (by rfl) ⟨1098143, by rfl⟩ : syracuseStep 1464191 = 2196287) B2196287
theorem B4183973 : Blo 650305 4183973 := bstep (se 4 (by rfl) ⟨392247, by rfl⟩ : syracuseStep 4183973 = 784495) B784495
theorem B1103807 : Blo 650305 1103807 := bstep (se 1 (by rfl) ⟨827855, by rfl⟩ : syracuseStep 1103807 = 1655711) B1655711
theorem B1857583 : Blo 650305 1857583 := bstep (se 1 (by rfl) ⟨1393187, by rfl⟩ : syracuseStep 1857583 = 2786375) B2786375
theorem B1235017 : Blo 650305 1235017 := bstep (se 2 (by rfl) ⟨463131, by rfl⟩ : syracuseStep 1235017 = 926263) B926263
theorem B1988819 : Blo 650305 1988819 := bstep (se 1 (by rfl) ⟨1491614, by rfl⟩ : syracuseStep 1988819 = 2983229) B2983229
theorem B1858153 : Blo 650305 1858153 := bstep (se 2 (by rfl) ⟨696807, by rfl⟩ : syracuseStep 1858153 = 1393615) B1393615
theorem B2349881 : Blo 650305 2349881 := bstep (se 2 (by rfl) ⟨881205, by rfl⟩ : syracuseStep 2349881 = 1762411) B1762411
theorem B2087963 : Blo 650305 2087963 := bstep (se 1 (by rfl) ⟨1565972, by rfl⟩ : syracuseStep 2087963 = 3131945) B3131945
theorem B60185693 : Blo 650305 60185693 := bstep (se 3 (by rfl) ⟨11284817, by rfl⟩ : syracuseStep 60185693 = 22569635) B22569635
theorem B1236073 : Blo 650305 1236073 := bstep (se 2 (by rfl) ⟨463527, by rfl⟩ : syracuseStep 1236073 = 927055) B927055
theorem B107306795 : Blo 650305 107306795 := bstep (se 1 (by rfl) ⟨80480096, by rfl⟩ : syracuseStep 107306795 = 160960193) B160960193
theorem B2645903 : Blo 650305 2645903 := bstep (se 1 (by rfl) ⟨1984427, by rfl⟩ : syracuseStep 2645903 = 3968855) B3968855
theorem B1761223 : Blo 650305 1761223 := bstep (se 1 (by rfl) ⟨1320917, by rfl⟩ : syracuseStep 1761223 = 2641835) B2641835
theorem B8347643 : Blo 650305 8347643 := bstep (se 1 (by rfl) ⟨6260732, by rfl⟩ : syracuseStep 8347643 = 12521465) B12521465
theorem B975497 : Blo 650305 975497 := bstep (se 2 (by rfl) ⟨365811, by rfl⟩ : syracuseStep 975497 = 731623) B731623
theorem B40297139 : Blo 650305 40297139 := bstep (se 1 (by rfl) ⟨30222854, by rfl⟩ : syracuseStep 40297139 = 60445709) B60445709
theorem B975737 : Blo 650305 975737 := bstep (se 2 (by rfl) ⟨365901, by rfl⟩ : syracuseStep 975737 = 731803) B731803
theorem B976031 : Blo 650305 976031 := bstep (se 1 (by rfl) ⟨732023, by rfl⟩ : syracuseStep 976031 = 1464047) B1464047
theorem B3302855 : Blo 650305 3302855 := bstep (se 1 (by rfl) ⟨2477141, by rfl⟩ : syracuseStep 3302855 = 4954283) B4954283
theorem B2975201 : Blo 650305 2975201 := bstep (se 2 (by rfl) ⟨1115700, by rfl⟩ : syracuseStep 2975201 = 2231401) B2231401
theorem B1467881 : Blo 650305 1467881 := bstep (se 2 (by rfl) ⟨550455, by rfl⟩ : syracuseStep 1467881 = 1100911) B1100911
theorem B1173023 : Blo 650305 1173023 := bstep (se 1 (by rfl) ⟨879767, by rfl⟩ : syracuseStep 1173023 = 1759535) B1759535
theorem B3303017 : Blo 650305 3303017 := bstep (se 2 (by rfl) ⟨1238631, by rfl⟩ : syracuseStep 3303017 = 2477263) B2477263
theorem B1042303 : Blo 650305 1042303 := bstep (se 1 (by rfl) ⟨781727, by rfl⟩ : syracuseStep 1042303 = 1563455) B1563455
theorem B1238951 : Blo 650305 1238951 := bstep (se 1 (by rfl) ⟨929213, by rfl⟩ : syracuseStep 1238951 = 1858427) B1858427
theorem B1468583 : Blo 650305 1468583 := bstep (se 1 (by rfl) ⟨1101437, by rfl⟩ : syracuseStep 1468583 = 2202875) B2202875
theorem B5302867 : Blo 650305 5302867 := bstep (se 1 (by rfl) ⟨3977150, by rfl⟩ : syracuseStep 5302867 = 7954301) B7954301
theorem B2976371 : Blo 650305 2976371 := bstep (se 1 (by rfl) ⟨2232278, by rfl⟩ : syracuseStep 2976371 = 4464557) B4464557
theorem B977567 : Blo 650305 977567 := bstep (se 1 (by rfl) ⟨733175, by rfl⟩ : syracuseStep 977567 = 1466351) B1466351
theorem B977735 : Blo 650305 977735 := bstep (se 1 (by rfl) ⟨733301, by rfl⟩ : syracuseStep 977735 = 1466603) B1466603
theorem B4451195 : Blo 650305 4451195 := bstep (se 1 (by rfl) ⟨3338396, by rfl⟩ : syracuseStep 4451195 = 6676793) B6676793
theorem B650471 : Blo 650305 650471 := bstep (se 1 (by rfl) ⟨487853, by rfl⟩ : syracuseStep 650471 = 975707) B975707
theorem B1469753 : Blo 650305 1469753 := bstep (se 2 (by rfl) ⟨551157, by rfl⟩ : syracuseStep 1469753 = 1102315) B1102315
theorem B9399635 : Blo 650305 9399635 := bstep (se 1 (by rfl) ⟨7049726, by rfl⟩ : syracuseStep 9399635 = 14099453) B14099453
theorem B1469807 : Blo 650305 1469807 := bstep (se 1 (by rfl) ⟨1102355, by rfl⟩ : syracuseStep 1469807 = 2204711) B2204711
theorem B3304961 : Blo 650305 3304961 := bstep (se 2 (by rfl) ⟨1239360, by rfl⟩ : syracuseStep 3304961 = 2478721) B2478721
theorem B1469951 : Blo 650305 1469951 := bstep (se 1 (by rfl) ⟨1102463, by rfl⟩ : syracuseStep 1469951 = 2204927) B2204927
theorem B650911 : Blo 650305 650911 := bstep (se 1 (by rfl) ⟨488183, by rfl⟩ : syracuseStep 650911 = 976367) B976367
theorem B650919 : Blo 650305 650919 := bstep (se 1 (by rfl) ⟨488189, by rfl⟩ : syracuseStep 650919 = 976379) B976379
theorem B650991 : Blo 650305 650991 := bstep (se 1 (by rfl) ⟨488243, by rfl⟩ : syracuseStep 650991 = 976487) B976487
theorem B651039 : Blo 650305 651039 := bstep (se 1 (by rfl) ⟨488279, by rfl⟩ : syracuseStep 651039 = 976559) B976559
theorem B13725521 : Blo 650305 13725521 := bstep (se 2 (by rfl) ⟨5147070, by rfl⟩ : syracuseStep 13725521 = 10294141) B10294141
theorem B651119 : Blo 650305 651119 := bstep (se 1 (by rfl) ⟨488339, by rfl⟩ : syracuseStep 651119 = 976679) B976679
theorem B651167 : Blo 650305 651167 := bstep (se 1 (by rfl) ⟨488375, by rfl⟩ : syracuseStep 651167 = 976751) B976751
theorem B1470419 : Blo 650305 1470419 := bstep (se 1 (by rfl) ⟨1102814, by rfl⟩ : syracuseStep 1470419 = 2205629) B2205629
theorem B4190201 : Blo 650305 4190201 := bstep (se 2 (by rfl) ⟨1571325, by rfl⟩ : syracuseStep 4190201 = 3142651) B3142651
theorem B651291 : Blo 650305 651291 := bstep (se 1 (by rfl) ⟨488468, by rfl⟩ : syracuseStep 651291 = 976937) B976937
theorem B1470527 : Blo 650305 1470527 := bstep (se 1 (by rfl) ⟨1102895, by rfl⟩ : syracuseStep 1470527 = 2205791) B2205791
theorem B1470689 : Blo 650305 1470689 := bstep (se 2 (by rfl) ⟨551508, by rfl⟩ : syracuseStep 1470689 = 1103017) B1103017
theorem B651519 : Blo 650305 651519 := bstep (se 1 (by rfl) ⟨488639, by rfl⟩ : syracuseStep 651519 = 977279) B977279
theorem B979241 : Blo 650305 979241 := bstep (se 2 (by rfl) ⟨367215, by rfl⟩ : syracuseStep 979241 = 734431) B734431
theorem B651679 : Blo 650305 651679 := bstep (se 1 (by rfl) ⟨488759, by rfl⟩ : syracuseStep 651679 = 977519) B977519
theorem B1045019 : Blo 650305 1045019 := bstep (se 1 (by rfl) ⟨783764, by rfl⟩ : syracuseStep 1045019 = 1567529) B1567529
theorem B1471391 : Blo 650305 1471391 := bstep (se 1 (by rfl) ⟨1103543, by rfl⟩ : syracuseStep 1471391 = 2207087) B2207087
theorem B1471823 : Blo 650305 1471823 := bstep (se 1 (by rfl) ⟨1103867, by rfl⟩ : syracuseStep 1471823 = 2207735) B2207735
theorem B980345 : Blo 650305 980345 := bstep (se 2 (by rfl) ⟨367629, by rfl⟩ : syracuseStep 980345 = 735259) B735259
theorem B1766909 : Blo 650305 1766909 := bstep (se 3 (by rfl) ⟨331295, by rfl⟩ : syracuseStep 1766909 = 662591) B662591
theorem B7435799 : Blo 650305 7435799 := bstep (se 1 (by rfl) ⟨5576849, by rfl⟩ : syracuseStep 7435799 = 11153699) B11153699
theorem B980585 : Blo 650305 980585 := bstep (se 2 (by rfl) ⟨367719, by rfl⟩ : syracuseStep 980585 = 735439) B735439
theorem B981119 : Blo 650305 981119 := bstep (se 1 (by rfl) ⟨735839, by rfl⟩ : syracuseStep 981119 = 1471679) B1471679
theorem B653595 : Blo 650305 653595 := bstep (se 1 (by rfl) ⟨490196, by rfl⟩ : syracuseStep 653595 = 980393) B980393
theorem B653631 : Blo 650305 653631 := bstep (se 1 (by rfl) ⟨490223, by rfl⟩ : syracuseStep 653631 = 980447) B980447
theorem B5569195 : Blo 650305 5569195 := bstep (se 1 (by rfl) ⟨4176896, by rfl⟩ : syracuseStep 5569195 = 8353793) B8353793
theorem B654063 : Blo 650305 654063 := bstep (se 1 (by rfl) ⟨490547, by rfl⟩ : syracuseStep 654063 = 981095) B981095
theorem B5569469 : Blo 650305 5569469 := bstep (se 3 (by rfl) ⟨1044275, by rfl⟩ : syracuseStep 5569469 = 2088551) B2088551
theorem B3177427 : Blo 650305 3177427 := bstep (se 1 (by rfl) ⟨2383070, by rfl⟩ : syracuseStep 3177427 = 4766141) B4766141
theorem B26705699 : Blo 650305 26705699 := bstep (se 1 (by rfl) ⟨20029274, by rfl⟩ : syracuseStep 26705699 = 40058549) B40058549
theorem B2981771 : Blo 650305 2981771 := bstep (se 1 (by rfl) ⟨2236328, by rfl⟩ : syracuseStep 2981771 = 4472657) B4472657
theorem B1115495 : Blo 650305 1115495 := bstep (se 1 (by rfl) ⟨836621, by rfl⟩ : syracuseStep 1115495 = 1673243) B1673243
theorem B2786717 : Blo 650305 2786717 := bstep (se 3 (by rfl) ⟨522509, by rfl⟩ : syracuseStep 2786717 = 1045019) B1045019
theorem B13404811 : Blo 650305 13404811 := bstep (se 1 (by rfl) ⟨10053608, by rfl⟩ : syracuseStep 13404811 = 20107217) B20107217
theorem B4230053 : Blo 650305 4230053 := bstep (se 4 (by rfl) ⟨396567, by rfl⟩ : syracuseStep 4230053 = 793135) B793135
theorem B2789315 : Blo 650305 2789315 := bstep (se 1 (by rfl) ⟨2091986, by rfl⟩ : syracuseStep 2789315 = 4183973) B4183973
theorem B71537863 : Blo 650305 71537863 := bstep (se 1 (by rfl) ⟨53653397, by rfl⟩ : syracuseStep 71537863 = 107306795) B107306795
theorem B2201903 : Blo 650305 2201903 := bstep (se 1 (by rfl) ⟨1651427, by rfl⟩ : syracuseStep 2201903 = 3302855) B3302855
theorem B2202011 : Blo 650305 2202011 := bstep (se 1 (by rfl) ⟨1651508, by rfl⟩ : syracuseStep 2202011 = 3303017) B3303017
theorem B825967 : Blo 650305 825967 := bstep (se 1 (by rfl) ⟨619475, by rfl⟩ : syracuseStep 825967 = 1238951) B1238951
theorem B9379223 : Blo 650305 9379223 := bstep (se 1 (by rfl) ⟨7034417, by rfl⟩ : syracuseStep 9379223 = 14068835) B14068835
theorem B6266423 : Blo 650305 6266423 := bstep (se 1 (by rfl) ⟨4699817, by rfl⟩ : syracuseStep 6266423 = 9399635) B9399635
theorem B2203307 : Blo 650305 2203307 := bstep (se 1 (by rfl) ⟨1652480, by rfl⟩ : syracuseStep 2203307 = 3304961) B3304961
theorem B9150347 : Blo 650305 9150347 := bstep (se 1 (by rfl) ⟨6862760, by rfl⟩ : syracuseStep 9150347 = 13725521) B13725521
theorem B2793467 : Blo 650305 2793467 := bstep (se 1 (by rfl) ⟨2095100, by rfl⟩ : syracuseStep 2793467 = 4190201) B4190201
theorem B1646689 : Blo 650305 1646689 := bstep (se 2 (by rfl) ⟨617508, by rfl⟩ : syracuseStep 1646689 = 1235017) B1235017
theorem B4957199 : Blo 650305 4957199 := bstep (se 1 (by rfl) ⟨3717899, by rfl⟩ : syracuseStep 4957199 = 7435799) B7435799
theorem B4236569 : Blo 650305 4236569 := bstep (se 2 (by rfl) ⟨1588713, by rfl⟩ : syracuseStep 4236569 = 3177427) B3177427
theorem B1647935 : Blo 650305 1647935 := bstep (se 1 (by rfl) ⟨1235951, by rfl⟩ : syracuseStep 1647935 = 2471903) B2471903
theorem B1648097 : Blo 650305 1648097 := bstep (se 2 (by rfl) ⟨618036, by rfl⟩ : syracuseStep 1648097 = 1236073) B1236073
theorem B7939903 : Blo 650305 7939903 := bstep (se 1 (by rfl) ⟨5954927, by rfl⟩ : syracuseStep 7939903 = 11909855) B11909855
theorem B3712979 : Blo 650305 3712979 := bstep (se 1 (by rfl) ⟨2784734, by rfl⟩ : syracuseStep 3712979 = 5569469) B5569469
theorem B7055741 : Blo 650305 7055741 := bstep (se 3 (by rfl) ⟨1322951, by rfl⟩ : syracuseStep 7055741 = 2645903) B2645903
theorem B17803799 : Blo 650305 17803799 := bstep (se 1 (by rfl) ⟨13352849, by rfl⟩ : syracuseStep 17803799 = 26705699) B26705699
theorem B2206439 : Blo 650305 2206439 := bstep (se 1 (by rfl) ⟨1654829, by rfl⟩ : syracuseStep 2206439 = 3309659) B3309659
theorem B8465903 : Blo 650305 8465903 := bstep (se 1 (by rfl) ⟨6349427, by rfl⟩ : syracuseStep 8465903 = 12698855) B12698855
theorem B1486505 : Blo 650305 1486505 := bstep (se 2 (by rfl) ⟨557439, by rfl⟩ : syracuseStep 1486505 = 1114879) B1114879
theorem B16691183 : Blo 650305 16691183 := bstep (se 1 (by rfl) ⟨12518387, by rfl⟩ : syracuseStep 16691183 = 25036775) B25036775
theorem B3518639 : Blo 650305 3518639 := bstep (se 1 (by rfl) ⟨2638979, by rfl⟩ : syracuseStep 3518639 = 5277959) B5277959
theorem B8335547 : Blo 650305 8335547 := bstep (se 1 (by rfl) ⟨6251660, by rfl⟩ : syracuseStep 8335547 = 12503321) B12503321
theorem B733927 : Blo 650305 733927 := bstep (se 1 (by rfl) ⟨550445, by rfl⟩ : syracuseStep 733927 = 1100891) B1100891
theorem B1389737 : Blo 650305 1389737 := bstep (se 2 (by rfl) ⟨521151, by rfl⟩ : syracuseStep 1389737 = 1042303) B1042303
theorem B3978803 : Blo 650305 3978803 := bstep (se 1 (by rfl) ⟨2984102, by rfl⟩ : syracuseStep 3978803 = 5968205) B5968205
theorem B1194259 : Blo 650305 1194259 := bstep (se 1 (by rfl) ⟨895694, by rfl⟩ : syracuseStep 1194259 = 1791389) B1791389
theorem B1653331 : Blo 650305 1653331 := bstep (se 1 (by rfl) ⟨1239998, by rfl⟩ : syracuseStep 1653331 = 2479997) B2479997
theorem B735871 : Blo 650305 735871 := bstep (se 1 (by rfl) ⟨551903, by rfl⟩ : syracuseStep 735871 = 1103807) B1103807
theorem B1325879 : Blo 650305 1325879 := bstep (se 1 (by rfl) ⟨994409, by rfl⟩ : syracuseStep 1325879 = 1988819) B1988819
theorem B2473193 : Blo 650305 2473193 := bstep (se 2 (by rfl) ⟨927447, by rfl⟩ : syracuseStep 2473193 = 1854895) B1854895
theorem B1391975 : Blo 650305 1391975 := bstep (se 1 (by rfl) ⟨1043981, by rfl⟩ : syracuseStep 1391975 = 2087963) B2087963
theorem B4178537 : Blo 650305 4178537 := bstep (se 2 (by rfl) ⟨1566951, by rfl⟩ : syracuseStep 4178537 = 3133903) B3133903
theorem B2474833 : Blo 650305 2474833 := bstep (se 2 (by rfl) ⟨928062, by rfl⟩ : syracuseStep 2474833 = 1856125) B1856125
theorem B30524381 : Blo 650305 30524381 := bstep (se 3 (by rfl) ⟨5723321, by rfl⟩ : syracuseStep 30524381 = 11446643) B11446643
theorem B1983467 : Blo 650305 1983467 := bstep (se 1 (by rfl) ⟨1487600, by rfl⟩ : syracuseStep 1983467 = 2975201) B2975201
theorem B12567595 : Blo 650305 12567595 := bstep (se 1 (by rfl) ⟨9425696, by rfl⟩ : syracuseStep 12567595 = 18851393) B18851393
theorem B16991453 : Blo 650305 16991453 := bstep (se 3 (by rfl) ⟨3185897, by rfl⟩ : syracuseStep 16991453 = 6371795) B6371795
theorem B1099291 : Blo 650305 1099291 := bstep (se 1 (by rfl) ⟨824468, by rfl⟩ : syracuseStep 1099291 = 1648937) B1648937
theorem B1984247 : Blo 650305 1984247 := bstep (se 1 (by rfl) ⟨1488185, by rfl⟩ : syracuseStep 1984247 = 2976371) B2976371
theorem B2967463 : Blo 650305 2967463 := bstep (se 1 (by rfl) ⟨2225597, by rfl⟩ : syracuseStep 2967463 = 4451195) B4451195
theorem B5556347 : Blo 650305 5556347 := bstep (se 1 (by rfl) ⟨4167260, by rfl⟩ : syracuseStep 5556347 = 8334521) B8334521
theorem B1100135 : Blo 650305 1100135 := bstep (se 1 (by rfl) ⟨825101, by rfl⟩ : syracuseStep 1100135 = 1650203) B1650203
theorem B11913637 : Blo 650305 11913637 := bstep (se 4 (by rfl) ⟨1116903, by rfl⟩ : syracuseStep 11913637 = 2233807) B2233807
theorem B2476777 : Blo 650305 2476777 := bstep (se 2 (by rfl) ⟨928791, by rfl⟩ : syracuseStep 2476777 = 1857583) B1857583
theorem B1985705 : Blo 650305 1985705 := bstep (se 2 (by rfl) ⟨744639, by rfl⟩ : syracuseStep 1985705 = 1489279) B1489279
theorem B2346191 : Blo 650305 2346191 := bstep (se 1 (by rfl) ⟨1759643, by rfl⟩ : syracuseStep 2346191 = 3519287) B3519287
theorem B2477537 : Blo 650305 2477537 := bstep (se 2 (by rfl) ⟨929076, by rfl⟩ : syracuseStep 2477537 = 1858153) B1858153
theorem B7425593 : Blo 650305 7425593 := bstep (se 2 (by rfl) ⟨2784597, by rfl⟩ : syracuseStep 7425593 = 5569195) B5569195
theorem B2478023 : Blo 650305 2478023 := bstep (se 1 (by rfl) ⟨1858517, by rfl⟩ : syracuseStep 2478023 = 3717035) B3717035
theorem B1987847 : Blo 650305 1987847 := bstep (se 1 (by rfl) ⟨1490885, by rfl⟩ : syracuseStep 1987847 = 2981771) B2981771
theorem B2348297 : Blo 650305 2348297 := bstep (se 2 (by rfl) ⟨880611, by rfl⟩ : syracuseStep 2348297 = 1761223) B1761223
theorem B3757711 : Blo 650305 3757711 := bstep (se 1 (by rfl) ⟨2818283, by rfl⟩ : syracuseStep 3757711 = 5636567) B5636567
theorem B1103935 : Blo 650305 1103935 := bstep (se 1 (by rfl) ⟨827951, by rfl⟩ : syracuseStep 1103935 = 1655903) B1655903
theorem B7527647 : Blo 650305 7527647 := bstep (se 1 (by rfl) ⟨5645735, by rfl⟩ : syracuseStep 7527647 = 11291471) B11291471
theorem B2481455 : Blo 650305 2481455 := bstep (se 1 (by rfl) ⟨1861091, by rfl⟩ : syracuseStep 2481455 = 3722183) B3722183
theorem B8478103 : Blo 650305 8478103 := bstep (se 1 (by rfl) ⟨6358577, by rfl⟩ : syracuseStep 8478103 = 12717155) B12717155
theorem B1236863 : Blo 650305 1236863 := bstep (se 1 (by rfl) ⟨927647, by rfl⟩ : syracuseStep 1236863 = 1855295) B1855295
theorem B2514883 : Blo 650305 2514883 := bstep (se 1 (by rfl) ⟨1886162, by rfl⟩ : syracuseStep 2514883 = 3772325) B3772325
theorem B14115019 : Blo 650305 14115019 := bstep (se 1 (by rfl) ⟨10586264, by rfl⟩ : syracuseStep 14115019 = 21172529) B21172529
theorem B975515 : Blo 650305 975515 := bstep (se 1 (by rfl) ⟨731636, by rfl⟩ : syracuseStep 975515 = 1463273) B1463273
theorem B975551 : Blo 650305 975551 := bstep (se 1 (by rfl) ⟨731663, by rfl⟩ : syracuseStep 975551 = 1463327) B1463327
theorem B12542687 : Blo 650305 12542687 := bstep (se 1 (by rfl) ⟨9407015, by rfl⟩ : syracuseStep 12542687 = 18814031) B18814031
theorem B975611 : Blo 650305 975611 := bstep (se 1 (by rfl) ⟨731708, by rfl⟩ : syracuseStep 975611 = 1463417) B1463417
theorem B7070489 : Blo 650305 7070489 := bstep (se 2 (by rfl) ⟨2651433, by rfl⟩ : syracuseStep 7070489 = 5302867) B5302867
theorem B8348669 : Blo 650305 8348669 := bstep (se 3 (by rfl) ⟨1565375, by rfl⟩ : syracuseStep 8348669 = 3130751) B3130751
theorem B1860671 : Blo 650305 1860671 := bstep (se 1 (by rfl) ⟨1395503, by rfl⟩ : syracuseStep 1860671 = 2791007) B2791007
theorem B1467503 : Blo 650305 1467503 := bstep (se 1 (by rfl) ⟨1100627, by rfl⟩ : syracuseStep 1467503 = 2201255) B2201255
theorem B976127 : Blo 650305 976127 := bstep (se 1 (by rfl) ⟨732095, by rfl⟩ : syracuseStep 976127 = 1464191) B1464191
theorem B1566587 : Blo 650305 1566587 := bstep (se 1 (by rfl) ⟨1174940, by rfl⟩ : syracuseStep 1566587 = 2349881) B2349881
theorem B1468331 : Blo 650305 1468331 := bstep (se 1 (by rfl) ⟨1101248, by rfl⟩ : syracuseStep 1468331 = 2202497) B2202497
theorem B1469087 : Blo 650305 1469087 := bstep (se 1 (by rfl) ⟨1101815, by rfl⟩ : syracuseStep 1469087 = 2203631) B2203631
theorem B5565095 : Blo 650305 5565095 := bstep (se 1 (by rfl) ⟨4173821, by rfl⟩ : syracuseStep 5565095 = 8347643) B8347643
theorem B3304151 : Blo 650305 3304151 := bstep (se 1 (by rfl) ⟨2478113, by rfl⟩ : syracuseStep 3304151 = 4956227) B4956227
theorem B4942619 : Blo 650305 4942619 := bstep (se 1 (by rfl) ⟨3706964, by rfl⟩ : syracuseStep 4942619 = 7413929) B7413929
theorem B977801 : Blo 650305 977801 := bstep (se 2 (by rfl) ⟨366675, by rfl⟩ : syracuseStep 977801 = 733351) B733351
theorem B650331 : Blo 650305 650331 := bstep (se 1 (by rfl) ⟨487748, by rfl⟩ : syracuseStep 650331 = 975497) B975497
theorem B26864759 : Blo 650305 26864759 := bstep (se 1 (by rfl) ⟨20148569, by rfl⟩ : syracuseStep 26864759 = 40297139) B40297139
theorem B650491 : Blo 650305 650491 := bstep (se 1 (by rfl) ⟨487868, by rfl⟩ : syracuseStep 650491 = 975737) B975737
theorem B650687 : Blo 650305 650687 := bstep (se 1 (by rfl) ⟨488015, by rfl⟩ : syracuseStep 650687 = 976031) B976031
theorem B1240697 : Blo 650305 1240697 := bstep (se 2 (by rfl) ⟨465261, by rfl⟩ : syracuseStep 1240697 = 930523) B930523
theorem B978587 : Blo 650305 978587 := bstep (se 1 (by rfl) ⟨733940, by rfl⟩ : syracuseStep 978587 = 1467881) B1467881
theorem B782015 : Blo 650305 782015 := bstep (se 1 (by rfl) ⟨586511, by rfl⟩ : syracuseStep 782015 = 1173023) B1173023
theorem B4943591 : Blo 650305 4943591 := bstep (se 1 (by rfl) ⟨3707693, by rfl⟩ : syracuseStep 4943591 = 7415387) B7415387
theorem B979055 : Blo 650305 979055 := bstep (se 1 (by rfl) ⟨734291, by rfl⟩ : syracuseStep 979055 = 1468583) B1468583
theorem B109801615 : Blo 650305 109801615 := bstep (se 1 (by rfl) ⟨82351211, by rfl⟩ : syracuseStep 109801615 = 164702423) B164702423
theorem B651711 : Blo 650305 651711 := bstep (se 1 (by rfl) ⟨488783, by rfl⟩ : syracuseStep 651711 = 977567) B977567
theorem B651823 : Blo 650305 651823 := bstep (se 1 (by rfl) ⟨488867, by rfl⟩ : syracuseStep 651823 = 977735) B977735
theorem B1471031 : Blo 650305 1471031 := bstep (se 1 (by rfl) ⟨1103273, by rfl⟩ : syracuseStep 1471031 = 2206547) B2206547
theorem B1471337 : Blo 650305 1471337 := bstep (se 2 (by rfl) ⟨551751, by rfl⟩ : syracuseStep 1471337 = 1103503) B1103503
theorem B979835 : Blo 650305 979835 := bstep (se 1 (by rfl) ⟨734876, by rfl⟩ : syracuseStep 979835 = 1469753) B1469753
theorem B979871 : Blo 650305 979871 := bstep (se 1 (by rfl) ⟨734903, by rfl⟩ : syracuseStep 979871 = 1469807) B1469807
theorem B979967 : Blo 650305 979967 := bstep (se 1 (by rfl) ⟨734975, by rfl⟩ : syracuseStep 979967 = 1469951) B1469951
theorem B29389853 : Blo 650305 29389853 := bstep (se 3 (by rfl) ⟨5510597, by rfl⟩ : syracuseStep 29389853 = 11021195) B11021195
theorem B18773207 : Blo 650305 18773207 := bstep (se 1 (by rfl) ⟨14079905, by rfl⟩ : syracuseStep 18773207 = 28159811) B28159811
theorem B980279 : Blo 650305 980279 := bstep (se 1 (by rfl) ⟨735209, by rfl⟩ : syracuseStep 980279 = 1470419) B1470419
theorem B980351 : Blo 650305 980351 := bstep (se 1 (by rfl) ⟨735263, by rfl⟩ : syracuseStep 980351 = 1470527) B1470527
theorem B980459 : Blo 650305 980459 := bstep (se 1 (by rfl) ⟨735344, by rfl⟩ : syracuseStep 980459 = 1470689) B1470689
theorem B652827 : Blo 650305 652827 := bstep (se 1 (by rfl) ⟨489620, by rfl⟩ : syracuseStep 652827 = 979241) B979241
theorem B160495181 : Blo 650305 160495181 := bstep (se 3 (by rfl) ⟨30092846, by rfl⟩ : syracuseStep 160495181 = 60185693) B60185693
theorem B980927 : Blo 650305 980927 := bstep (se 1 (by rfl) ⟨735695, by rfl⟩ : syracuseStep 980927 = 1471391) B1471391
theorem B981215 : Blo 650305 981215 := bstep (se 1 (by rfl) ⟨735911, by rfl⟩ : syracuseStep 981215 = 1471823) B1471823
theorem B653563 : Blo 650305 653563 := bstep (se 1 (by rfl) ⟨490172, by rfl⟩ : syracuseStep 653563 = 980345) B980345
theorem B1177939 : Blo 650305 1177939 := bstep (se 1 (by rfl) ⟨883454, by rfl⟩ : syracuseStep 1177939 = 1766909) B1766909
theorem B653723 : Blo 650305 653723 := bstep (se 1 (by rfl) ⟨490292, by rfl⟩ : syracuseStep 653723 = 980585) B980585
theorem B2783915 : Blo 650305 2783915 := bstep (se 1 (by rfl) ⟨2087936, by rfl⟩ : syracuseStep 2783915 = 4175873) B4175873
theorem B654079 : Blo 650305 654079 := bstep (se 1 (by rfl) ⟨490559, by rfl⟩ : syracuseStep 654079 = 981119) B981119
theorem B4291553 : Blo 650305 4291553 := bstep (se 2 (by rfl) ⟨1609332, by rfl⟩ : syracuseStep 4291553 = 3218665) B3218665
theorem B9403553 : Blo 650305 9403553 := bstep (se 2 (by rfl) ⟨3526332, by rfl⟩ : syracuseStep 9403553 = 7052665) B7052665
theorem B13074281 : Blo 650305 13074281 := bstep (se 2 (by rfl) ⟨4902855, by rfl⟩ : syracuseStep 13074281 = 9805711) B9805711
theorem B2195423 : Blo 650305 2195423 := bstep (se 1 (by rfl) ⟨1646567, by rfl⟩ : syracuseStep 2195423 = 3293135) B3293135
theorem B2195585 : Blo 650305 2195585 := bstep (se 2 (by rfl) ⟨823344, by rfl⟩ : syracuseStep 2195585 = 1646689) B1646689
theorem B2785691 : Blo 650305 2785691 := bstep (se 1 (by rfl) ⟨2089268, by rfl⟩ : syracuseStep 2785691 = 4178537) B4178537
theorem B20349587 : Blo 650305 20349587 := bstep (se 1 (by rfl) ⟨15262190, by rfl⟩ : syracuseStep 20349587 = 30524381) B30524381
theorem B3704231 : Blo 650305 3704231 := bstep (se 1 (by rfl) ⟨2778173, by rfl⟩ : syracuseStep 3704231 = 5556347) B5556347
theorem B2820035 : Blo 650305 2820035 := bstep (se 1 (by rfl) ⟨2115026, by rfl⟩ : syracuseStep 2820035 = 4230053) B4230053
theorem B4950395 : Blo 650305 4950395 := bstep (se 1 (by rfl) ⟨3712796, by rfl⟩ : syracuseStep 4950395 = 7425593) B7425593
theorem B10586537 : Blo 650305 10586537 := bstep (se 2 (by rfl) ⟨3969951, by rfl⟩ : syracuseStep 10586537 = 7939903) B7939903
theorem B5018431 : Blo 650305 5018431 := bstep (se 1 (by rfl) ⟨3763823, by rfl⟩ : syracuseStep 5018431 = 7527647) B7527647
theorem B824575 : Blo 650305 824575 := bstep (se 1 (by rfl) ⟨618431, by rfl⟩ : syracuseStep 824575 = 1236863) B1236863
theorem B8361791 : Blo 650305 8361791 := bstep (se 1 (by rfl) ⟨6271343, by rfl⟩ : syracuseStep 8361791 = 12542687) B12542687
theorem B2824379 : Blo 650305 2824379 := bstep (se 1 (by rfl) ⟨2118284, by rfl⟩ : syracuseStep 2824379 = 4236569) B4236569
theorem B11869199 : Blo 650305 11869199 := bstep (se 1 (by rfl) ⟨8901899, by rfl⟩ : syracuseStep 11869199 = 17803799) B17803799
theorem B3710063 : Blo 650305 3710063 := bstep (se 1 (by rfl) ⟨2782547, by rfl⟩ : syracuseStep 3710063 = 5565095) B5565095
theorem B2202767 : Blo 650305 2202767 := bstep (se 1 (by rfl) ⟨1652075, by rfl⟩ : syracuseStep 2202767 = 3304151) B3304151
theorem B5643935 : Blo 650305 5643935 := bstep (se 1 (by rfl) ⟨4232951, by rfl⟩ : syracuseStep 5643935 = 8465903) B8465903
theorem B991003 : Blo 650305 991003 := bstep (se 1 (by rfl) ⟨743252, by rfl⟩ : syracuseStep 991003 = 1486505) B1486505
theorem B11444141 : Blo 650305 11444141 := bstep (se 3 (by rfl) ⟨2145776, by rfl⟩ : syracuseStep 11444141 = 4291553) B4291553
theorem B25076141 : Blo 650305 25076141 := bstep (se 3 (by rfl) ⟨4701776, by rfl⟩ : syracuseStep 25076141 = 9403553) B9403553
theorem B2204441 : Blo 650305 2204441 := bstep (se 2 (by rfl) ⟨826665, by rfl⟩ : syracuseStep 2204441 = 1653331) B1653331
theorem B926491 : Blo 650305 926491 := bstep (se 1 (by rfl) ⟨694868, by rfl⟩ : syracuseStep 926491 = 1389737) B1389737
theorem B106996787 : Blo 650305 106996787 := bstep (se 1 (by rfl) ⟨80247590, by rfl⟩ : syracuseStep 106996787 = 160495181) B160495181
theorem B1648795 : Blo 650305 1648795 := bstep (se 1 (by rfl) ⟨1236596, by rfl⟩ : syracuseStep 1648795 = 2473193) B2473193
theorem B927983 : Blo 650305 927983 := bstep (se 1 (by rfl) ⟨695987, by rfl⟩ : syracuseStep 927983 = 1391975) B1391975
theorem B3353177 : Blo 650305 3353177 := bstep (se 2 (by rfl) ⟨1257441, by rfl⟩ : syracuseStep 3353177 = 2514883) B2514883
theorem B18820025 : Blo 650305 18820025 := bstep (se 2 (by rfl) ⟨7057509, by rfl⟩ : syracuseStep 18820025 = 14115019) B14115019
theorem B1322831 : Blo 650305 1322831 := bstep (se 1 (by rfl) ⟨992123, by rfl⟩ : syracuseStep 1322831 = 1984247) B1984247
theorem B16756793 : Blo 650305 16756793 := bstep (se 2 (by rfl) ⟨6283797, by rfl⟩ : syracuseStep 16756793 = 12567595) B12567595
theorem B733423 : Blo 650305 733423 := bstep (se 1 (by rfl) ⟨550067, by rfl⟩ : syracuseStep 733423 = 1100135) B1100135
theorem B1323803 : Blo 650305 1323803 := bstep (se 1 (by rfl) ⟨992852, by rfl⟩ : syracuseStep 1323803 = 1985705) B1985705
theorem B1651691 : Blo 650305 1651691 := bstep (se 1 (by rfl) ⟨1238768, by rfl⟩ : syracuseStep 1651691 = 2477537) B2477537
theorem B5289245 : Blo 650305 5289245 := bstep (se 3 (by rfl) ⟨991733, by rfl⟩ : syracuseStep 5289245 = 1983467) B1983467
theorem B1652015 : Blo 650305 1652015 := bstep (se 1 (by rfl) ⟨1239011, by rfl⟩ : syracuseStep 1652015 = 2478023) B2478023
theorem B1325231 : Blo 650305 1325231 := bstep (se 1 (by rfl) ⟨993923, by rfl⟩ : syracuseStep 1325231 = 1987847) B1987847
theorem B17873081 : Blo 650305 17873081 := bstep (se 2 (by rfl) ⟨6702405, by rfl⟩ : syracuseStep 17873081 = 13404811) B13404811
theorem B1654303 : Blo 650305 1654303 := bstep (se 1 (by rfl) ⟨1240727, by rfl⟩ : syracuseStep 1654303 = 2481455) B2481455
theorem B4177565 : Blo 650305 4177565 := bstep (se 3 (by rfl) ⟨783293, by rfl⟩ : syracuseStep 4177565 = 1566587) B1566587
theorem B4177615 : Blo 650305 4177615 := bstep (se 1 (by rfl) ⟨3133211, by rfl⟩ : syracuseStep 4177615 = 6266423) B6266423
theorem B1098623 : Blo 650305 1098623 := bstep (se 1 (by rfl) ⟨823967, by rfl⟩ : syracuseStep 1098623 = 1647935) B1647935
theorem B1098731 : Blo 650305 1098731 := bstep (se 1 (by rfl) ⟨824048, by rfl⟩ : syracuseStep 1098731 = 1648097) B1648097
theorem B2475319 : Blo 650305 2475319 := bstep (se 1 (by rfl) ⟨1856489, by rfl⟩ : syracuseStep 2475319 = 3712979) B3712979
theorem B4703827 : Blo 650305 4703827 := bstep (se 1 (by rfl) ⟨3527870, by rfl⟩ : syracuseStep 4703827 = 7055741) B7055741
theorem B3295079 : Blo 650305 3295079 := bstep (se 1 (by rfl) ⟨2471309, by rfl⟩ : syracuseStep 3295079 = 4942619) B4942619
theorem B17909839 : Blo 650305 17909839 := bstep (se 1 (by rfl) ⟨13432379, by rfl⟩ : syracuseStep 17909839 = 26864759) B26864759
theorem B3295727 : Blo 650305 3295727 := bstep (se 1 (by rfl) ⟨2471795, by rfl⟩ : syracuseStep 3295727 = 4943591) B4943591
theorem B11127455 : Blo 650305 11127455 := bstep (se 1 (by rfl) ⟨8345591, by rfl⟩ : syracuseStep 11127455 = 16691183) B16691183
theorem B2345759 : Blo 650305 2345759 := bstep (se 1 (by rfl) ⟨1759319, by rfl⟩ : syracuseStep 2345759 = 3518639) B3518639
theorem B5557031 : Blo 650305 5557031 := bstep (se 1 (by rfl) ⟨4167773, by rfl⟩ : syracuseStep 5557031 = 8335547) B8335547
theorem B1592345 : Blo 650305 1592345 := bstep (se 2 (by rfl) ⟨597129, by rfl⟩ : syracuseStep 1592345 = 1194259) B1194259
theorem B1101289 : Blo 650305 1101289 := bstep (se 2 (by rfl) ⟨412983, by rfl⟩ : syracuseStep 1101289 = 825967) B825967
theorem B1855943 : Blo 650305 1855943 := bstep (se 1 (by rfl) ⟨1391957, by rfl⟩ : syracuseStep 1855943 = 2783915) B2783915
theorem B2085373 : Blo 650305 2085373 := bstep (se 3 (by rfl) ⟨391007, by rfl⟩ : syracuseStep 2085373 = 782015) B782015
theorem B24400925 : Blo 650305 24400925 := bstep (se 3 (by rfl) ⟨4575173, by rfl⟩ : syracuseStep 24400925 = 9150347) B9150347
theorem B1463615 : Blo 650305 1463615 := bstep (se 1 (by rfl) ⟨1097711, by rfl⟩ : syracuseStep 1463615 = 2195423) B2195423
theorem B11327635 : Blo 650305 11327635 := bstep (se 1 (by rfl) ⟨8495726, by rfl⟩ : syracuseStep 11327635 = 16991453) B16991453
theorem B743663 : Blo 650305 743663 := bstep (se 1 (by rfl) ⟨557747, by rfl⟩ : syracuseStep 743663 = 1115495) B1115495
theorem B1857811 : Blo 650305 1857811 := bstep (se 1 (by rfl) ⟨1393358, by rfl⟩ : syracuseStep 1857811 = 2786717) B2786717
theorem B3299777 : Blo 650305 3299777 := bstep (se 2 (by rfl) ⟨1237416, by rfl⟩ : syracuseStep 3299777 = 2474833) B2474833
theorem B1465721 : Blo 650305 1465721 := bstep (se 2 (by rfl) ⟨549645, by rfl⟩ : syracuseStep 1465721 = 1099291) B1099291
theorem B1564127 : Blo 650305 1564127 := bstep (se 1 (by rfl) ⟨1173095, by rfl⟩ : syracuseStep 1564127 = 2346191) B2346191
theorem B3956617 : Blo 650305 3956617 := bstep (se 2 (by rfl) ⟨1483731, by rfl⟩ : syracuseStep 3956617 = 2967463) B2967463
theorem B1859543 : Blo 650305 1859543 := bstep (se 1 (by rfl) ⟨1394657, by rfl⟩ : syracuseStep 1859543 = 2789315) B2789315
theorem B15884849 : Blo 650305 15884849 := bstep (se 2 (by rfl) ⟨5956818, by rfl⟩ : syracuseStep 15884849 = 11913637) B11913637
theorem B1565531 : Blo 650305 1565531 := bstep (se 1 (by rfl) ⟨1174148, by rfl⟩ : syracuseStep 1565531 = 2348297) B2348297
theorem B3302369 : Blo 650305 3302369 := bstep (se 2 (by rfl) ⟨1238388, by rfl⟩ : syracuseStep 3302369 = 2476777) B2476777
theorem B1467935 : Blo 650305 1467935 := bstep (se 1 (by rfl) ⟨1100951, by rfl⟩ : syracuseStep 1467935 = 2201903) B2201903
theorem B1468007 : Blo 650305 1468007 := bstep (se 1 (by rfl) ⟨1101005, by rfl⟩ : syracuseStep 1468007 = 2202011) B2202011
theorem B6252815 : Blo 650305 6252815 := bstep (se 1 (by rfl) ⟨4689611, by rfl⟩ : syracuseStep 6252815 = 9379223) B9379223
theorem B1468871 : Blo 650305 1468871 := bstep (se 1 (by rfl) ⟨1101653, by rfl⟩ : syracuseStep 1468871 = 2203307) B2203307
theorem B1862311 : Blo 650305 1862311 := bstep (se 1 (by rfl) ⟨1396733, by rfl⟩ : syracuseStep 1862311 = 2793467) B2793467
theorem B146402153 : Blo 650305 146402153 := bstep (se 2 (by rfl) ⟨54900807, by rfl⟩ : syracuseStep 146402153 = 109801615) B109801615
theorem B650343 : Blo 650305 650343 := bstep (se 1 (by rfl) ⟨487757, by rfl⟩ : syracuseStep 650343 = 975515) B975515
theorem B650367 : Blo 650305 650367 := bstep (se 1 (by rfl) ⟨487775, by rfl⟩ : syracuseStep 650367 = 975551) B975551
theorem B650407 : Blo 650305 650407 := bstep (se 1 (by rfl) ⟨487805, by rfl⟩ : syracuseStep 650407 = 975611) B975611
theorem B4713659 : Blo 650305 4713659 := bstep (se 1 (by rfl) ⟨3535244, by rfl⟩ : syracuseStep 4713659 = 7070489) B7070489
theorem B5565779 : Blo 650305 5565779 := bstep (se 1 (by rfl) ⟨4174334, by rfl⟩ : syracuseStep 5565779 = 8348669) B8348669
theorem B3304799 : Blo 650305 3304799 := bstep (se 1 (by rfl) ⟨2478599, by rfl⟩ : syracuseStep 3304799 = 4957199) B4957199
theorem B1240447 : Blo 650305 1240447 := bstep (se 1 (by rfl) ⟨930335, by rfl⟩ : syracuseStep 1240447 = 1860671) B1860671
theorem B978335 : Blo 650305 978335 := bstep (se 1 (by rfl) ⟨733751, by rfl⟩ : syracuseStep 978335 = 1467503) B1467503
theorem B650751 : Blo 650305 650751 := bstep (se 1 (by rfl) ⟨488063, by rfl⟩ : syracuseStep 650751 = 976127) B976127
theorem B978569 : Blo 650305 978569 := bstep (se 2 (by rfl) ⟨366963, by rfl⟩ : syracuseStep 978569 = 733927) B733927
theorem B978887 : Blo 650305 978887 := bstep (se 1 (by rfl) ⟨734165, by rfl⟩ : syracuseStep 978887 = 1468331) B1468331
theorem B95383817 : Blo 650305 95383817 := bstep (se 2 (by rfl) ⟨35768931, by rfl⟩ : syracuseStep 95383817 = 71537863) B71537863
theorem B979391 : Blo 650305 979391 := bstep (se 1 (by rfl) ⟨734543, by rfl⟩ : syracuseStep 979391 = 1469087) B1469087
theorem B1470959 : Blo 650305 1470959 := bstep (se 1 (by rfl) ⟨1103219, by rfl⟩ : syracuseStep 1470959 = 2206439) B2206439
theorem B651867 : Blo 650305 651867 := bstep (se 1 (by rfl) ⟨488900, by rfl⟩ : syracuseStep 651867 = 977801) B977801
theorem B5010281 : Blo 650305 5010281 := bstep (se 2 (by rfl) ⟨1878855, by rfl⟩ : syracuseStep 5010281 = 3757711) B3757711
theorem B652391 : Blo 650305 652391 := bstep (se 1 (by rfl) ⟨489293, by rfl⟩ : syracuseStep 652391 = 978587) B978587
theorem B652703 : Blo 650305 652703 := bstep (se 1 (by rfl) ⟨489527, by rfl⟩ : syracuseStep 652703 = 979055) B979055
theorem B1471913 : Blo 650305 1471913 := bstep (se 2 (by rfl) ⟨551967, by rfl⟩ : syracuseStep 1471913 = 1103935) B1103935
theorem B980687 : Blo 650305 980687 := bstep (se 1 (by rfl) ⟨735515, by rfl⟩ : syracuseStep 980687 = 1471031) B1471031
theorem B1570585 : Blo 650305 1570585 := bstep (se 2 (by rfl) ⟨588969, by rfl⟩ : syracuseStep 1570585 = 1177939) B1177939
theorem B980891 : Blo 650305 980891 := bstep (se 1 (by rfl) ⟨735668, by rfl⟩ : syracuseStep 980891 = 1471337) B1471337
theorem B653223 : Blo 650305 653223 := bstep (se 1 (by rfl) ⟨489917, by rfl⟩ : syracuseStep 653223 = 979835) B979835
theorem B653247 : Blo 650305 653247 := bstep (se 1 (by rfl) ⟨489935, by rfl⟩ : syracuseStep 653247 = 979871) B979871
theorem B653311 : Blo 650305 653311 := bstep (se 1 (by rfl) ⟨489983, by rfl⟩ : syracuseStep 653311 = 979967) B979967
theorem B19593235 : Blo 650305 19593235 := bstep (se 1 (by rfl) ⟨14694926, by rfl⟩ : syracuseStep 19593235 = 29389853) B29389853
theorem B12515471 : Blo 650305 12515471 := bstep (se 1 (by rfl) ⟨9386603, by rfl⟩ : syracuseStep 12515471 = 18773207) B18773207
theorem B981161 : Blo 650305 981161 := bstep (se 2 (by rfl) ⟨367935, by rfl⟩ : syracuseStep 981161 = 735871) B735871
theorem B653519 : Blo 650305 653519 := bstep (se 1 (by rfl) ⟨490139, by rfl⟩ : syracuseStep 653519 = 980279) B980279
theorem B653567 : Blo 650305 653567 := bstep (se 1 (by rfl) ⟨490175, by rfl⟩ : syracuseStep 653567 = 980351) B980351
theorem B653639 : Blo 650305 653639 := bstep (se 1 (by rfl) ⟨490229, by rfl⟩ : syracuseStep 653639 = 980459) B980459
theorem B2652535 : Blo 650305 2652535 := bstep (se 1 (by rfl) ⟨1989401, by rfl⟩ : syracuseStep 2652535 = 3978803) B3978803
theorem B653951 : Blo 650305 653951 := bstep (se 1 (by rfl) ⟨490463, by rfl⟩ : syracuseStep 653951 = 980927) B980927
theorem B654143 : Blo 650305 654143 := bstep (se 1 (by rfl) ⟨490607, by rfl⟩ : syracuseStep 654143 = 981215) B981215
theorem B3308525 : Blo 650305 3308525 := bstep (se 3 (by rfl) ⟨620348, by rfl⟩ : syracuseStep 3308525 = 1240697) B1240697
theorem B11304137 : Blo 650305 11304137 := bstep (se 2 (by rfl) ⟨4239051, by rfl⟩ : syracuseStep 11304137 = 8478103) B8478103
theorem B883919 : Blo 650305 883919 := bstep (se 1 (by rfl) ⟨662939, by rfl⟩ : syracuseStep 883919 = 1325879) B1325879
theorem B8716187 : Blo 650305 8716187 := bstep (se 1 (by rfl) ⟨6537140, by rfl⟩ : syracuseStep 8716187 = 13074281) B13074281
theorem B104497253 : Blo 650305 104497253 := bstep (se 4 (by rfl) ⟨9796617, by rfl⟩ : syracuseStep 104497253 = 19593235) B19593235
theorem B2196719 : Blo 650305 2196719 := bstep (se 1 (by rfl) ⟨1647539, by rfl⟩ : syracuseStep 2196719 = 3295079) B3295079
theorem B2197151 : Blo 650305 2197151 := bstep (se 1 (by rfl) ⟨1647863, by rfl⟩ : syracuseStep 2197151 = 3295727) B3295727
theorem B54265565 : Blo 650305 54265565 := bstep (se 3 (by rfl) ⟨10174793, by rfl⟩ : syracuseStep 54265565 = 20349587) B20349587
theorem B3704687 : Blo 650305 3704687 := bstep (se 1 (by rfl) ⟨2778515, by rfl⟩ : syracuseStep 3704687 = 5557031) B5557031
theorem B2198393 : Blo 650305 2198393 := bstep (se 2 (by rfl) ⟨824397, by rfl⟩ : syracuseStep 2198393 = 1648795) B1648795
theorem B5574527 : Blo 650305 5574527 := bstep (se 1 (by rfl) ⟨4180895, by rfl⟩ : syracuseStep 5574527 = 8361791) B8361791
theorem B2199851 : Blo 650305 2199851 := bstep (se 1 (by rfl) ⟨1649888, by rfl⟩ : syracuseStep 2199851 = 3299777) B3299777
theorem B16717427 : Blo 650305 16717427 := bstep (se 1 (by rfl) ⟨12538070, by rfl⟩ : syracuseStep 16717427 = 25076141) B25076141
theorem B10589899 : Blo 650305 10589899 := bstep (se 1 (by rfl) ⟨7942424, by rfl⟩ : syracuseStep 10589899 = 15884849) B15884849
theorem B2201579 : Blo 650305 2201579 := bstep (se 1 (by rfl) ⟨1651184, by rfl⟩ : syracuseStep 2201579 = 3302369) B3302369
theorem B6691241 : Blo 650305 6691241 := bstep (se 2 (by rfl) ⟨2509215, by rfl⟩ : syracuseStep 6691241 = 5018431) B5018431
theorem B4168543 : Blo 650305 4168543 := bstep (se 1 (by rfl) ⟨3126407, by rfl⟩ : syracuseStep 4168543 = 6252815) B6252815
theorem B2235451 : Blo 650305 2235451 := bstep (se 1 (by rfl) ⟨1676588, by rfl⟩ : syracuseStep 2235451 = 3353177) B3353177
theorem B3710519 : Blo 650305 3710519 := bstep (se 1 (by rfl) ⟨2782889, by rfl⟩ : syracuseStep 3710519 = 5565779) B5565779
theorem B2203199 : Blo 650305 2203199 := bstep (se 1 (by rfl) ⟨1652399, by rfl⟩ : syracuseStep 2203199 = 3304799) B3304799
theorem B2205683 : Blo 650305 2205683 := bstep (se 1 (by rfl) ⟨1654262, by rfl⟩ : syracuseStep 2205683 = 3308525) B3308525
theorem B2205737 : Blo 650305 2205737 := bstep (se 2 (by rfl) ⟨827151, by rfl⟩ : syracuseStep 2205737 = 1654303) B1654303
theorem B1321337 : Blo 650305 1321337 := bstep (se 2 (by rfl) ⟨495501, by rfl⟩ : syracuseStep 1321337 = 991003) B991003
theorem B5810791 : Blo 650305 5810791 := bstep (se 1 (by rfl) ⟨4358093, by rfl⟩ : syracuseStep 5810791 = 8716187) B8716187
theorem B732415 : Blo 650305 732415 := bstep (se 1 (by rfl) ⟨549311, by rfl⟩ : syracuseStep 732415 = 1098623) B1098623
theorem B732487 : Blo 650305 732487 := bstep (se 1 (by rfl) ⟨549365, by rfl⟩ : syracuseStep 732487 = 1098731) B1098731
theorem B2469487 : Blo 650305 2469487 := bstep (se 1 (by rfl) ⟨1852115, by rfl⟩ : syracuseStep 2469487 = 3704231) B3704231
theorem B1880023 : Blo 650305 1880023 := bstep (se 1 (by rfl) ⟨1410017, by rfl⟩ : syracuseStep 1880023 = 2820035) B2820035
theorem B7057691 : Blo 650305 7057691 := bstep (se 1 (by rfl) ⟨5293268, by rfl⟩ : syracuseStep 7057691 = 10586537) B10586537
theorem B7418303 : Blo 650305 7418303 := bstep (se 1 (by rfl) ⟨5563727, by rfl⟩ : syracuseStep 7418303 = 11127455) B11127455
theorem B6271769 : Blo 650305 6271769 := bstep (se 2 (by rfl) ⟨2351913, by rfl⟩ : syracuseStep 6271769 = 4703827) B4703827
theorem B16267283 : Blo 650305 16267283 := bstep (se 1 (by rfl) ⟨12200462, by rfl⟩ : syracuseStep 16267283 = 24400925) B24400925
theorem B1882919 : Blo 650305 1882919 := bstep (se 1 (by rfl) ⟨1412189, by rfl⟩ : syracuseStep 1882919 = 2824379) B2824379
theorem B1653929 : Blo 650305 1653929 := bstep (se 2 (by rfl) ⟨620223, by rfl⟩ : syracuseStep 1653929 = 1240447) B1240447
theorem B7912799 : Blo 650305 7912799 := bstep (se 1 (by rfl) ⟨5934599, by rfl⟩ : syracuseStep 7912799 = 11869199) B11869199
theorem B2473375 : Blo 650305 2473375 := bstep (se 1 (by rfl) ⟨1855031, by rfl⟩ : syracuseStep 2473375 = 3710063) B3710063
theorem B2474621 : Blo 650305 2474621 := bstep (se 3 (by rfl) ⟨463991, by rfl⟩ : syracuseStep 2474621 = 927983) B927983
theorem B1983101 : Blo 650305 1983101 := bstep (se 3 (by rfl) ⟨371831, by rfl⟩ : syracuseStep 1983101 = 743663) B743663
theorem B1099433 : Blo 650305 1099433 := bstep (se 2 (by rfl) ⟨412287, by rfl⟩ : syracuseStep 1099433 = 824575) B824575
theorem B97601435 : Blo 650305 97601435 := bstep (se 1 (by rfl) ⟨73201076, by rfl⟩ : syracuseStep 97601435 = 146402153) B146402153
theorem B4246253 : Blo 650305 4246253 := bstep (se 3 (by rfl) ⟨796172, by rfl⟩ : syracuseStep 4246253 = 1592345) B1592345
theorem B63589211 : Blo 650305 63589211 := bstep (se 1 (by rfl) ⟨47691908, by rfl⟩ : syracuseStep 63589211 = 95383817) B95383817
theorem B2477081 : Blo 650305 2477081 := bstep (se 2 (by rfl) ⟨928905, by rfl⟩ : syracuseStep 2477081 = 1857811) B1857811
theorem B1101127 : Blo 650305 1101127 := bstep (se 1 (by rfl) ⟨825845, by rfl⟩ : syracuseStep 1101127 = 1651691) B1651691
theorem B3526163 : Blo 650305 3526163 := bstep (se 1 (by rfl) ⟨2644622, by rfl⟩ : syracuseStep 3526163 = 5289245) B5289245
theorem B1101343 : Blo 650305 1101343 := bstep (se 1 (by rfl) ⟨826007, by rfl⟩ : syracuseStep 1101343 = 1652015) B1652015
theorem B8343647 : Blo 650305 8343647 := bstep (se 1 (by rfl) ⟨6257735, by rfl⟩ : syracuseStep 8343647 = 12515471) B12515471
theorem B11915387 : Blo 650305 11915387 := bstep (se 1 (by rfl) ⟨8936540, by rfl⟩ : syracuseStep 11915387 = 17873081) B17873081
theorem B3527549 : Blo 650305 3527549 := bstep (se 3 (by rfl) ⟨661415, by rfl⟩ : syracuseStep 3527549 = 1322831) B1322831
theorem B1463723 : Blo 650305 1463723 := bstep (se 1 (by rfl) ⟨1097792, by rfl⟩ : syracuseStep 1463723 = 2195585) B2195585
theorem B1235321 : Blo 650305 1235321 := bstep (se 2 (by rfl) ⟨463245, by rfl⟩ : syracuseStep 1235321 = 926491) B926491
theorem B7428509 : Blo 650305 7428509 := bstep (se 3 (by rfl) ⟨1392845, by rfl⟩ : syracuseStep 7428509 = 2785691) B2785691
theorem B3300263 : Blo 650305 3300263 := bstep (se 1 (by rfl) ⟨2475197, by rfl⟩ : syracuseStep 3300263 = 4950395) B4950395
theorem B3300425 : Blo 650305 3300425 := bstep (se 2 (by rfl) ⟨1237659, by rfl⟩ : syracuseStep 3300425 = 2475319) B2475319
theorem B1563839 : Blo 650305 1563839 := bstep (se 1 (by rfl) ⟨1172879, by rfl⟩ : syracuseStep 1563839 = 2345759) B2345759
theorem B3530141 : Blo 650305 3530141 := bstep (se 3 (by rfl) ⟨661901, by rfl⟩ : syracuseStep 3530141 = 1323803) B1323803
theorem B23879785 : Blo 650305 23879785 := bstep (se 2 (by rfl) ⟨8954919, by rfl⟩ : syracuseStep 23879785 = 17909839) B17909839
theorem B1237295 : Blo 650305 1237295 := bstep (se 1 (by rfl) ⟨927971, by rfl⟩ : syracuseStep 1237295 = 1855943) B1855943
theorem B975743 : Blo 650305 975743 := bstep (se 1 (by rfl) ⟨731807, by rfl⟩ : syracuseStep 975743 = 1463615) B1463615
theorem B2483081 : Blo 650305 2483081 := bstep (se 2 (by rfl) ⟨931155, by rfl⟩ : syracuseStep 2483081 = 1862311) B1862311
theorem B1468385 : Blo 650305 1468385 := bstep (se 2 (by rfl) ⟨550644, by rfl⟩ : syracuseStep 1468385 = 1101289) B1101289
theorem B1468511 : Blo 650305 1468511 := bstep (se 1 (by rfl) ⟨1101383, by rfl⟩ : syracuseStep 1468511 = 2202767) B2202767
theorem B977147 : Blo 650305 977147 := bstep (se 1 (by rfl) ⟨732860, by rfl⟩ : syracuseStep 977147 = 1465721) B1465721
theorem B1042751 : Blo 650305 1042751 := bstep (se 1 (by rfl) ⟨782063, by rfl⟩ : syracuseStep 1042751 = 1564127) B1564127
theorem B3762623 : Blo 650305 3762623 := bstep (se 1 (by rfl) ⟨2821967, by rfl⟩ : syracuseStep 3762623 = 5643935) B5643935
theorem B7629427 : Blo 650305 7629427 := bstep (se 1 (by rfl) ⟨5722070, by rfl⟩ : syracuseStep 7629427 = 11444141) B11444141
theorem B1239695 : Blo 650305 1239695 := bstep (se 1 (by rfl) ⟨929771, by rfl⟩ : syracuseStep 1239695 = 1859543) B1859543
theorem B977897 : Blo 650305 977897 := bstep (se 2 (by rfl) ⟨366711, by rfl⟩ : syracuseStep 977897 = 733423) B733423
theorem B1469627 : Blo 650305 1469627 := bstep (se 1 (by rfl) ⟨1102220, by rfl⟩ : syracuseStep 1469627 = 2204441) B2204441
theorem B1043687 : Blo 650305 1043687 := bstep (se 1 (by rfl) ⟨782765, by rfl⟩ : syracuseStep 1043687 = 1565531) B1565531
theorem B2780497 : Blo 650305 2780497 := bstep (se 2 (by rfl) ⟨1042686, by rfl⟩ : syracuseStep 2780497 = 2085373) B2085373
theorem B71331191 : Blo 650305 71331191 := bstep (se 1 (by rfl) ⟨53498393, by rfl⟩ : syracuseStep 71331191 = 106996787) B106996787
theorem B978623 : Blo 650305 978623 := bstep (se 1 (by rfl) ⟨733967, by rfl⟩ : syracuseStep 978623 = 1467935) B1467935
theorem B978671 : Blo 650305 978671 := bstep (se 1 (by rfl) ⟨734003, by rfl⟩ : syracuseStep 978671 = 1468007) B1468007
theorem B979247 : Blo 650305 979247 := bstep (se 1 (by rfl) ⟨734435, by rfl⟩ : syracuseStep 979247 = 1468871) B1468871
theorem B12546683 : Blo 650305 12546683 := bstep (se 1 (by rfl) ⟨9410012, by rfl⟩ : syracuseStep 12546683 = 18820025) B18820025
theorem B3142439 : Blo 650305 3142439 := bstep (se 1 (by rfl) ⟨2356829, by rfl⟩ : syracuseStep 3142439 = 4713659) B4713659
theorem B652223 : Blo 650305 652223 := bstep (se 1 (by rfl) ⟨489167, by rfl⟩ : syracuseStep 652223 = 978335) B978335
theorem B2094113 : Blo 650305 2094113 := bstep (se 2 (by rfl) ⟨785292, by rfl⟩ : syracuseStep 2094113 = 1570585) B1570585
theorem B652379 : Blo 650305 652379 := bstep (se 1 (by rfl) ⟨489284, by rfl⟩ : syracuseStep 652379 = 978569) B978569
theorem B652591 : Blo 650305 652591 := bstep (se 1 (by rfl) ⟨489443, by rfl⟩ : syracuseStep 652591 = 978887) B978887
theorem B11171195 : Blo 650305 11171195 := bstep (se 1 (by rfl) ⟨8378396, by rfl⟩ : syracuseStep 11171195 = 16756793) B16756793
theorem B15103513 : Blo 650305 15103513 := bstep (se 2 (by rfl) ⟨5663817, by rfl⟩ : syracuseStep 15103513 = 11327635) B11327635
theorem B652927 : Blo 650305 652927 := bstep (se 1 (by rfl) ⟨489695, by rfl⟩ : syracuseStep 652927 = 979391) B979391
theorem B980639 : Blo 650305 980639 := bstep (se 1 (by rfl) ⟨735479, by rfl⟩ : syracuseStep 980639 = 1470959) B1470959
theorem B3536713 : Blo 650305 3536713 := bstep (se 2 (by rfl) ⟨1326267, by rfl⟩ : syracuseStep 3536713 = 2652535) B2652535
theorem B2357117 : Blo 650305 2357117 := bstep (se 3 (by rfl) ⟨441959, by rfl⟩ : syracuseStep 2357117 = 883919) B883919
theorem B3340187 : Blo 650305 3340187 := bstep (se 1 (by rfl) ⟨2505140, by rfl⟩ : syracuseStep 3340187 = 5010281) B5010281
theorem B981275 : Blo 650305 981275 := bstep (se 1 (by rfl) ⟨735956, by rfl⟩ : syracuseStep 981275 = 1471913) B1471913
theorem B653791 : Blo 650305 653791 := bstep (se 1 (by rfl) ⟨490343, by rfl⟩ : syracuseStep 653791 = 980687) B980687
theorem B653927 : Blo 650305 653927 := bstep (se 1 (by rfl) ⟨490445, by rfl⟩ : syracuseStep 653927 = 980891) B980891
theorem B654107 : Blo 650305 654107 := bstep (se 1 (by rfl) ⟨490580, by rfl⟩ : syracuseStep 654107 = 981161) B981161
theorem B883487 : Blo 650305 883487 := bstep (se 1 (by rfl) ⟨662615, by rfl⟩ : syracuseStep 883487 = 1325231) B1325231
theorem B7536091 : Blo 650305 7536091 := bstep (se 1 (by rfl) ⟨5652068, by rfl⟩ : syracuseStep 7536091 = 11304137) B11304137
theorem B5570153 : Blo 650305 5570153 := bstep (se 2 (by rfl) ⟨2088807, by rfl⟩ : syracuseStep 5570153 = 4177615) B4177615
theorem B2785043 : Blo 650305 2785043 := bstep (se 1 (by rfl) ⟨2088782, by rfl⟩ : syracuseStep 2785043 = 4177565) B4177565
theorem B5275489 : Blo 650305 5275489 := bstep (se 2 (by rfl) ⟨1978308, by rfl⟩ : syracuseStep 5275489 = 3956617) B3956617
theorem B69664835 : Blo 650305 69664835 := bstep (se 1 (by rfl) ⟨52248626, by rfl⟩ : syracuseStep 69664835 = 104497253) B104497253
theorem B36177043 : Blo 650305 36177043 := bstep (se 1 (by rfl) ⟨27132782, by rfl⟩ : syracuseStep 36177043 = 54265565) B54265565
theorem B11144951 : Blo 650305 11144951 := bstep (se 1 (by rfl) ⟨8358713, by rfl⟩ : syracuseStep 11144951 = 16717427) B16717427
theorem B823547 : Blo 650305 823547 := bstep (se 1 (by rfl) ⟨617660, by rfl⟩ : syracuseStep 823547 = 1235321) B1235321
theorem B4952339 : Blo 650305 4952339 := bstep (se 1 (by rfl) ⟨3714254, by rfl⟩ : syracuseStep 4952339 = 7428509) B7428509
theorem B4460827 : Blo 650305 4460827 := bstep (se 1 (by rfl) ⟨3345620, by rfl⟩ : syracuseStep 4460827 = 6691241) B6691241
theorem B3707329 : Blo 650305 3707329 := bstep (se 2 (by rfl) ⟨1390248, by rfl⟩ : syracuseStep 3707329 = 2780497) B2780497
theorem B2200175 : Blo 650305 2200175 := bstep (se 1 (by rfl) ⟨1650131, by rfl⟩ : syracuseStep 2200175 = 3300263) B3300263
theorem B2200283 : Blo 650305 2200283 := bstep (se 1 (by rfl) ⟨1650212, by rfl⟩ : syracuseStep 2200283 = 3300425) B3300425
theorem B826463 : Blo 650305 826463 := bstep (se 1 (by rfl) ⟨619847, by rfl⟩ : syracuseStep 826463 = 1239695) B1239695
theorem B695791 : Blo 650305 695791 := bstep (se 1 (by rfl) ⟨521843, by rfl⟩ : syracuseStep 695791 = 1043687) B1043687
theorem B47554127 : Blo 650305 47554127 := bstep (se 1 (by rfl) ⟨35665595, by rfl⟩ : syracuseStep 47554127 = 71331191) B71331191
theorem B8364455 : Blo 650305 8364455 := bstep (se 1 (by rfl) ⟨6273341, by rfl⟩ : syracuseStep 8364455 = 12546683) B12546683
theorem B7447463 : Blo 650305 7447463 := bstep (se 1 (by rfl) ⟨5585597, by rfl⟩ : syracuseStep 7447463 = 11171195) B11171195
theorem B1255279 : Blo 650305 1255279 := bstep (se 1 (by rfl) ⟨941459, by rfl⟩ : syracuseStep 1255279 = 1882919) B1882919
theorem B3713435 : Blo 650305 3713435 := bstep (se 1 (by rfl) ⟨2785076, by rfl⟩ : syracuseStep 3713435 = 5570153) B5570153
theorem B1649747 : Blo 650305 1649747 := bstep (se 1 (by rfl) ⟨1237310, by rfl⟩ : syracuseStep 1649747 = 2474621) B2474621
theorem B732955 : Blo 650305 732955 := bstep (se 1 (by rfl) ⟨549716, by rfl⟩ : syracuseStep 732955 = 1099433) B1099433
theorem B2469791 : Blo 650305 2469791 := bstep (se 1 (by rfl) ⟨1852343, by rfl⟩ : syracuseStep 2469791 = 3704687) B3704687
theorem B5288269 : Blo 650305 5288269 := bstep (se 3 (by rfl) ⟨991550, by rfl⟩ : syracuseStep 5288269 = 1983101) B1983101
theorem B2830835 : Blo 650305 2830835 := bstep (se 1 (by rfl) ⟨2123126, by rfl⟩ : syracuseStep 2830835 = 4246253) B4246253
theorem B1651387 : Blo 650305 1651387 := bstep (se 1 (by rfl) ⟨1238540, by rfl⟩ : syracuseStep 1651387 = 2477081) B2477081
theorem B3716351 : Blo 650305 3716351 := bstep (se 1 (by rfl) ⟨2787263, by rfl⟩ : syracuseStep 3716351 = 5574527) B5574527
theorem B7943591 : Blo 650305 7943591 := bstep (se 1 (by rfl) ⟨5957693, by rfl⟩ : syracuseStep 7943591 = 11915387) B11915387
theorem B5584301 : Blo 650305 5584301 := bstep (se 3 (by rfl) ⟨1047056, by rfl⟩ : syracuseStep 5584301 = 2094113) B2094113
theorem B7747721 : Blo 650305 7747721 := bstep (se 2 (by rfl) ⟨2905395, by rfl⟩ : syracuseStep 7747721 = 5810791) B5810791
theorem B10172569 : Blo 650305 10172569 := bstep (se 2 (by rfl) ⟨3814713, by rfl⟩ : syracuseStep 10172569 = 7629427) B7629427
theorem B3292649 : Blo 650305 3292649 := bstep (se 2 (by rfl) ⟨1234743, by rfl⟩ : syracuseStep 3292649 = 2469487) B2469487
theorem B2473679 : Blo 650305 2473679 := bstep (se 1 (by rfl) ⟨1855259, by rfl⟩ : syracuseStep 2473679 = 3710519) B3710519
theorem B2506697 : Blo 650305 2506697 := bstep (se 2 (by rfl) ⟨940011, by rfl⟩ : syracuseStep 2506697 = 1880023) B1880023
theorem B1655387 : Blo 650305 1655387 := bstep (se 1 (by rfl) ⟨1241540, by rfl⟩ : syracuseStep 1655387 = 2483081) B2483081
theorem B3523565 : Blo 650305 3523565 := bstep (se 3 (by rfl) ⟨660668, by rfl⟩ : syracuseStep 3523565 = 1321337) B1321337
theorem B2508415 : Blo 650305 2508415 := bstep (se 1 (by rfl) ⟨1881311, by rfl⟩ : syracuseStep 2508415 = 3762623) B3762623
theorem B20138017 : Blo 650305 20138017 := bstep (se 2 (by rfl) ⟨7551756, by rfl⟩ : syracuseStep 20138017 = 15103513) B15103513
theorem B4705127 : Blo 650305 4705127 := bstep (se 1 (by rfl) ⟨3528845, by rfl⟩ : syracuseStep 4705127 = 7057691) B7057691
theorem B4181179 : Blo 650305 4181179 := bstep (se 1 (by rfl) ⟨3135884, by rfl⟩ : syracuseStep 4181179 = 6271769) B6271769
theorem B5558057 : Blo 650305 5558057 := bstep (se 2 (by rfl) ⟨2084271, by rfl⟩ : syracuseStep 5558057 = 4168543) B4168543
theorem B3297833 : Blo 650305 3297833 := bstep (se 2 (by rfl) ⟨1236687, by rfl⟩ : syracuseStep 3297833 = 2473375) B2473375
theorem B10048121 : Blo 650305 10048121 := bstep (se 2 (by rfl) ⟨3768045, by rfl⟩ : syracuseStep 10048121 = 7536091) B7536091
theorem B1102619 : Blo 650305 1102619 := bstep (se 1 (by rfl) ⟨826964, by rfl⟩ : syracuseStep 1102619 = 1653929) B1653929
theorem B7033985 : Blo 650305 7033985 := bstep (se 2 (by rfl) ⟨2637744, by rfl⟩ : syracuseStep 7033985 = 5275489) B5275489
theorem B1856695 : Blo 650305 1856695 := bstep (se 1 (by rfl) ⟨1392521, by rfl⟩ : syracuseStep 1856695 = 2785043) B2785043
theorem B31839713 : Blo 650305 31839713 := bstep (se 2 (by rfl) ⟨11939892, by rfl⟩ : syracuseStep 31839713 = 23879785) B23879785
theorem B3299453 : Blo 650305 3299453 := bstep (se 3 (by rfl) ⟨618647, by rfl⟩ : syracuseStep 3299453 = 1237295) B1237295
theorem B1464479 : Blo 650305 1464479 := bstep (se 1 (by rfl) ⟨1098359, by rfl⟩ : syracuseStep 1464479 = 2196719) B2196719
theorem B1464767 : Blo 650305 1464767 := bstep (se 1 (by rfl) ⟨1098575, by rfl⟩ : syracuseStep 1464767 = 2197151) B2197151
theorem B65067623 : Blo 650305 65067623 := bstep (se 1 (by rfl) ⟨48800717, by rfl⟩ : syracuseStep 65067623 = 97601435) B97601435
theorem B42392807 : Blo 650305 42392807 := bstep (se 1 (by rfl) ⟨31794605, by rfl⟩ : syracuseStep 42392807 = 63589211) B63589211
theorem B1465595 : Blo 650305 1465595 := bstep (se 1 (by rfl) ⟨1099196, by rfl⟩ : syracuseStep 1465595 = 2198393) B2198393
theorem B2350775 : Blo 650305 2350775 := bstep (se 1 (by rfl) ⟨1763081, by rfl⟩ : syracuseStep 2350775 = 3526163) B3526163
theorem B5562431 : Blo 650305 5562431 := bstep (se 1 (by rfl) ⟨4171823, by rfl⟩ : syracuseStep 5562431 = 8343647) B8343647
theorem B1466567 : Blo 650305 1466567 := bstep (se 1 (by rfl) ⟨1099925, by rfl⟩ : syracuseStep 1466567 = 2199851) B2199851
theorem B2351699 : Blo 650305 2351699 := bstep (se 1 (by rfl) ⟨1763774, by rfl⟩ : syracuseStep 2351699 = 3527549) B3527549
theorem B975815 : Blo 650305 975815 := bstep (se 1 (by rfl) ⟨731861, by rfl⟩ : syracuseStep 975815 = 1463723) B1463723
theorem B1467719 : Blo 650305 1467719 := bstep (se 1 (by rfl) ⟨1100789, by rfl⟩ : syracuseStep 1467719 = 2201579) B2201579
theorem B976553 : Blo 650305 976553 := bstep (se 2 (by rfl) ⟨366207, by rfl⟩ : syracuseStep 976553 = 732415) B732415
theorem B976649 : Blo 650305 976649 := bstep (se 2 (by rfl) ⟨366243, by rfl⟩ : syracuseStep 976649 = 732487) B732487
theorem B1468169 : Blo 650305 1468169 := bstep (se 2 (by rfl) ⟨550563, by rfl⟩ : syracuseStep 1468169 = 1101127) B1101127
theorem B1468457 : Blo 650305 1468457 := bstep (se 2 (by rfl) ⟨550671, by rfl⟩ : syracuseStep 1468457 = 1101343) B1101343
theorem B1042559 : Blo 650305 1042559 := bstep (se 1 (by rfl) ⟨781919, by rfl⟩ : syracuseStep 1042559 = 1563839) B1563839
theorem B2353427 : Blo 650305 2353427 := bstep (se 1 (by rfl) ⟨1765070, by rfl⟩ : syracuseStep 2353427 = 3530141) B3530141
theorem B1468799 : Blo 650305 1468799 := bstep (se 1 (by rfl) ⟨1101599, by rfl⟩ : syracuseStep 1468799 = 2203199) B2203199
theorem B650495 : Blo 650305 650495 := bstep (se 1 (by rfl) ⟨487871, by rfl⟩ : syracuseStep 650495 = 975743) B975743
theorem B2780669 : Blo 650305 2780669 := bstep (se 3 (by rfl) ⟨521375, by rfl⟩ : syracuseStep 2780669 = 1042751) B1042751
theorem B978923 : Blo 650305 978923 := bstep (se 1 (by rfl) ⟨734192, by rfl⟩ : syracuseStep 978923 = 1468385) B1468385
theorem B1470455 : Blo 650305 1470455 := bstep (se 1 (by rfl) ⟨1102841, by rfl⟩ : syracuseStep 1470455 = 2205683) B2205683
theorem B1470491 : Blo 650305 1470491 := bstep (se 1 (by rfl) ⟨1102868, by rfl⟩ : syracuseStep 1470491 = 2205737) B2205737
theorem B979007 : Blo 650305 979007 := bstep (se 1 (by rfl) ⟨734255, by rfl⟩ : syracuseStep 979007 = 1468511) B1468511
theorem B651431 : Blo 650305 651431 := bstep (se 1 (by rfl) ⟨488573, by rfl⟩ : syracuseStep 651431 = 977147) B977147
theorem B651931 : Blo 650305 651931 := bstep (se 1 (by rfl) ⟨488948, by rfl⟩ : syracuseStep 651931 = 977897) B977897
theorem B2355965 : Blo 650305 2355965 := bstep (se 3 (by rfl) ⟨441743, by rfl⟩ : syracuseStep 2355965 = 883487) B883487
theorem B979751 : Blo 650305 979751 := bstep (se 1 (by rfl) ⟨734813, by rfl⟩ : syracuseStep 979751 = 1469627) B1469627
theorem B14119865 : Blo 650305 14119865 := bstep (se 2 (by rfl) ⟨5294949, by rfl⟩ : syracuseStep 14119865 = 10589899) B10589899
theorem B4715617 : Blo 650305 4715617 := bstep (se 2 (by rfl) ⟨1768356, by rfl⟩ : syracuseStep 4715617 = 3536713) B3536713
theorem B652415 : Blo 650305 652415 := bstep (se 1 (by rfl) ⟨489311, by rfl⟩ : syracuseStep 652415 = 978623) B978623
theorem B652447 : Blo 650305 652447 := bstep (se 1 (by rfl) ⟨489335, by rfl⟩ : syracuseStep 652447 = 978671) B978671
theorem B652831 : Blo 650305 652831 := bstep (se 1 (by rfl) ⟨489623, by rfl⟩ : syracuseStep 652831 = 979247) B979247
theorem B4945535 : Blo 650305 4945535 := bstep (se 1 (by rfl) ⟨3709151, by rfl⟩ : syracuseStep 4945535 = 7418303) B7418303
theorem B2094959 : Blo 650305 2094959 := bstep (se 1 (by rfl) ⟨1571219, by rfl⟩ : syracuseStep 2094959 = 3142439) B3142439
theorem B653759 : Blo 650305 653759 := bstep (se 1 (by rfl) ⟨490319, by rfl⟩ : syracuseStep 653759 = 980639) B980639
theorem B1571411 : Blo 650305 1571411 := bstep (se 1 (by rfl) ⟨1178558, by rfl⟩ : syracuseStep 1571411 = 2357117) B2357117
theorem B2226791 : Blo 650305 2226791 := bstep (se 1 (by rfl) ⟨1670093, by rfl⟩ : syracuseStep 2226791 = 3340187) B3340187
theorem B10844855 : Blo 650305 10844855 := bstep (se 1 (by rfl) ⟨8133641, by rfl⟩ : syracuseStep 10844855 = 16267283) B16267283
theorem B2980601 : Blo 650305 2980601 := bstep (se 2 (by rfl) ⟨1117725, by rfl⟩ : syracuseStep 2980601 = 2235451) B2235451
theorem B654183 : Blo 650305 654183 := bstep (se 1 (by rfl) ⟨490637, by rfl⟩ : syracuseStep 654183 = 981275) B981275
theorem B5275199 : Blo 650305 5275199 := bstep (se 1 (by rfl) ⟨3956399, by rfl⟩ : syracuseStep 5275199 = 7912799) B7912799
theorem B2196125 : Blo 650305 2196125 := bstep (se 3 (by rfl) ⟨411773, by rfl⟩ : syracuseStep 2196125 = 823547) B823547
theorem B48236057 : Blo 650305 48236057 := bstep (se 2 (by rfl) ⟨18088521, by rfl⟩ : syracuseStep 48236057 = 36177043) B36177043
theorem B1673705 : Blo 650305 1673705 := bstep (se 2 (by rfl) ⟨627639, by rfl⟩ : syracuseStep 1673705 = 1255279) B1255279
theorem B3705371 : Blo 650305 3705371 := bstep (se 1 (by rfl) ⟨2779028, by rfl⟩ : syracuseStep 3705371 = 5558057) B5558057
theorem B2198555 : Blo 650305 2198555 := bstep (se 1 (by rfl) ⟨1648916, by rfl⟩ : syracuseStep 2198555 = 3297833) B3297833
theorem B4689323 : Blo 650305 4689323 := bstep (se 1 (by rfl) ⟨3516992, by rfl⟩ : syracuseStep 4689323 = 7033985) B7033985
theorem B2199635 : Blo 650305 2199635 := bstep (se 1 (by rfl) ⟨1649726, by rfl⟩ : syracuseStep 2199635 = 3299453) B3299453
theorem B5574905 : Blo 650305 5574905 := bstep (se 2 (by rfl) ⟨2090589, by rfl⟩ : syracuseStep 5574905 = 4181179) B4181179
theorem B3708287 : Blo 650305 3708287 := bstep (se 1 (by rfl) ⟨2781215, by rfl⟩ : syracuseStep 3708287 = 5562431) B5562431
theorem B5576303 : Blo 650305 5576303 := bstep (se 1 (by rfl) ⟨4182227, by rfl⟩ : syracuseStep 5576303 = 8364455) B8364455
theorem B7051025 : Blo 650305 7051025 := bstep (se 2 (by rfl) ⟨2644134, by rfl⟩ : syracuseStep 7051025 = 5288269) B5288269
theorem B2201849 : Blo 650305 2201849 := bstep (se 2 (by rfl) ⟨825693, by rfl⟩ : syracuseStep 2201849 = 1651387) B1651387
theorem B695039 : Blo 650305 695039 := bstep (se 1 (by rfl) ⟨521279, by rfl⟩ : syracuseStep 695039 = 1042559) B1042559
theorem B1646527 : Blo 650305 1646527 := bstep (se 1 (by rfl) ⟨1234895, by rfl⟩ : syracuseStep 1646527 = 2469791) B2469791
theorem B2203901 : Blo 650305 2203901 := bstep (se 3 (by rfl) ⟨413231, by rfl⟩ : syracuseStep 2203901 = 826463) B826463
theorem B9413243 : Blo 650305 9413243 := bstep (se 1 (by rfl) ⟨7059932, by rfl⟩ : syracuseStep 9413243 = 14119865) B14119865
theorem B13378213 : Blo 650305 13378213 := bstep (se 4 (by rfl) ⟨1254207, by rfl⟩ : syracuseStep 13378213 = 2508415) B2508415
theorem B1484527 : Blo 650305 1484527 := bstep (se 1 (by rfl) ⟨1113395, by rfl⟩ : syracuseStep 1484527 = 2226791) B2226791
theorem B927721 : Blo 650305 927721 := bstep (se 2 (by rfl) ⟨347895, by rfl⟩ : syracuseStep 927721 = 695791) B695791
theorem B3516799 : Blo 650305 3516799 := bstep (se 1 (by rfl) ⟨2637599, by rfl⟩ : syracuseStep 3516799 = 5275199) B5275199
theorem B1649119 : Blo 650305 1649119 := bstep (se 1 (by rfl) ⟨1236839, by rfl⟩ : syracuseStep 1649119 = 2473679) B2473679
theorem B46443223 : Blo 650305 46443223 := bstep (se 1 (by rfl) ⟨34832417, by rfl⟩ : syracuseStep 46443223 = 69664835) B69664835
theorem B7548893 : Blo 650305 7548893 := bstep (se 3 (by rfl) ⟨1415417, by rfl⟩ : syracuseStep 7548893 = 2830835) B2830835
theorem B26850689 : Blo 650305 26850689 := bstep (se 2 (by rfl) ⟨10069008, by rfl⟩ : syracuseStep 26850689 = 20138017) B20138017
theorem B6698747 : Blo 650305 6698747 := bstep (se 1 (by rfl) ⟨5024060, by rfl⟩ : syracuseStep 6698747 = 10048121) B10048121
theorem B735079 : Blo 650305 735079 := bstep (se 1 (by rfl) ⟨551309, by rfl⟩ : syracuseStep 735079 = 1102619) B1102619
theorem B28261871 : Blo 650305 28261871 := bstep (se 1 (by rfl) ⟨21196403, by rfl⟩ : syracuseStep 28261871 = 42392807) B42392807
theorem B31702751 : Blo 650305 31702751 := bstep (se 1 (by rfl) ⟨23777063, by rfl⟩ : syracuseStep 31702751 = 47554127) B47554127
theorem B5947769 : Blo 650305 5947769 := bstep (se 2 (by rfl) ⟨2230413, by rfl⟩ : syracuseStep 5947769 = 4460827) B4460827
theorem B4964975 : Blo 650305 4964975 := bstep (se 1 (by rfl) ⟨3723731, by rfl⟩ : syracuseStep 4964975 = 7447463) B7447463
theorem B2475593 : Blo 650305 2475593 := bstep (se 2 (by rfl) ⟨928347, by rfl⟩ : syracuseStep 2475593 = 1856695) B1856695
theorem B2475623 : Blo 650305 2475623 := bstep (se 1 (by rfl) ⟨1856717, by rfl⟩ : syracuseStep 2475623 = 3713435) B3713435
theorem B1099831 : Blo 650305 1099831 := bstep (se 1 (by rfl) ⟨824873, by rfl⟩ : syracuseStep 1099831 = 1649747) B1649747
theorem B1853779 : Blo 650305 1853779 := bstep (se 1 (by rfl) ⟨1390334, by rfl⟩ : syracuseStep 1853779 = 2780669) B2780669
theorem B2477567 : Blo 650305 2477567 := bstep (se 1 (by rfl) ⟨1858175, by rfl⟩ : syracuseStep 2477567 = 3716351) B3716351
theorem B5295727 : Blo 650305 5295727 := bstep (se 1 (by rfl) ⟨3971795, by rfl⟩ : syracuseStep 5295727 = 7943591) B7943591
theorem B3722867 : Blo 650305 3722867 := bstep (se 1 (by rfl) ⟨2792150, by rfl⟩ : syracuseStep 3722867 = 5584301) B5584301
theorem B3297023 : Blo 650305 3297023 := bstep (se 1 (by rfl) ⟨2472767, by rfl⟩ : syracuseStep 3297023 = 4945535) B4945535
theorem B1396639 : Blo 650305 1396639 := bstep (se 1 (by rfl) ⟨1047479, by rfl⟩ : syracuseStep 1396639 = 2094959) B2094959
theorem B5165147 : Blo 650305 5165147 := bstep (se 1 (by rfl) ⟨3873860, by rfl⟩ : syracuseStep 5165147 = 7747721) B7747721
theorem B7229903 : Blo 650305 7229903 := bstep (se 1 (by rfl) ⟨5422427, by rfl⟩ : syracuseStep 7229903 = 10844855) B10844855
theorem B1987067 : Blo 650305 1987067 := bstep (se 1 (by rfl) ⟨1490300, by rfl⟩ : syracuseStep 1987067 = 2980601) B2980601
theorem B1103591 : Blo 650305 1103591 := bstep (se 1 (by rfl) ⟨827693, by rfl⟩ : syracuseStep 1103591 = 1655387) B1655387
theorem B2349043 : Blo 650305 2349043 := bstep (se 1 (by rfl) ⟨1761782, by rfl⟩ : syracuseStep 2349043 = 3523565) B3523565
theorem B3136751 : Blo 650305 3136751 := bstep (se 1 (by rfl) ⟨2352563, by rfl⟩ : syracuseStep 3136751 = 4705127) B4705127
theorem B7429967 : Blo 650305 7429967 := bstep (se 1 (by rfl) ⟨5572475, by rfl⟩ : syracuseStep 7429967 = 11144951) B11144951
theorem B3301559 : Blo 650305 3301559 := bstep (se 1 (by rfl) ⟨2476169, by rfl⟩ : syracuseStep 3301559 = 4952339) B4952339
theorem B1466783 : Blo 650305 1466783 := bstep (se 1 (by rfl) ⟨1100087, by rfl⟩ : syracuseStep 1466783 = 2200175) B2200175
theorem B1466855 : Blo 650305 1466855 := bstep (se 1 (by rfl) ⟨1100141, by rfl⟩ : syracuseStep 1466855 = 2200283) B2200283
theorem B21226475 : Blo 650305 21226475 := bstep (se 1 (by rfl) ⟨15919856, by rfl⟩ : syracuseStep 21226475 = 31839713) B31839713
theorem B976319 : Blo 650305 976319 := bstep (se 1 (by rfl) ⟨732239, by rfl⟩ : syracuseStep 976319 = 1464479) B1464479
theorem B976511 : Blo 650305 976511 := bstep (se 1 (by rfl) ⟨732383, by rfl⟩ : syracuseStep 976511 = 1464767) B1464767
theorem B43378415 : Blo 650305 43378415 := bstep (se 1 (by rfl) ⟨32533811, by rfl⟩ : syracuseStep 43378415 = 65067623) B65067623
theorem B977063 : Blo 650305 977063 := bstep (se 1 (by rfl) ⟨732797, by rfl⟩ : syracuseStep 977063 = 1465595) B1465595
theorem B977273 : Blo 650305 977273 := bstep (se 2 (by rfl) ⟨366477, by rfl⟩ : syracuseStep 977273 = 732955) B732955
theorem B1567183 : Blo 650305 1567183 := bstep (se 1 (by rfl) ⟨1175387, by rfl⟩ : syracuseStep 1567183 = 2350775) B2350775
theorem B977711 : Blo 650305 977711 := bstep (se 1 (by rfl) ⟨733283, by rfl⟩ : syracuseStep 977711 = 1466567) B1466567
theorem B1567799 : Blo 650305 1567799 := bstep (se 1 (by rfl) ⟨1175849, by rfl⟩ : syracuseStep 1567799 = 2351699) B2351699
theorem B4943105 : Blo 650305 4943105 := bstep (se 2 (by rfl) ⟨1853664, by rfl⟩ : syracuseStep 4943105 = 3707329) B3707329
theorem B650543 : Blo 650305 650543 := bstep (se 1 (by rfl) ⟨487907, by rfl⟩ : syracuseStep 650543 = 975815) B975815
theorem B978479 : Blo 650305 978479 := bstep (se 1 (by rfl) ⟨733859, by rfl⟩ : syracuseStep 978479 = 1467719) B1467719
theorem B651035 : Blo 650305 651035 := bstep (se 1 (by rfl) ⟨488276, by rfl⟩ : syracuseStep 651035 = 976553) B976553
theorem B651099 : Blo 650305 651099 := bstep (se 1 (by rfl) ⟨488324, by rfl⟩ : syracuseStep 651099 = 976649) B976649
theorem B978779 : Blo 650305 978779 := bstep (se 1 (by rfl) ⟨734084, by rfl⟩ : syracuseStep 978779 = 1468169) B1468169
theorem B978971 : Blo 650305 978971 := bstep (se 1 (by rfl) ⟨734228, by rfl⟩ : syracuseStep 978971 = 1468457) B1468457
theorem B6287489 : Blo 650305 6287489 := bstep (se 2 (by rfl) ⟨2357808, by rfl⟩ : syracuseStep 6287489 = 4715617) B4715617
theorem B1568951 : Blo 650305 1568951 := bstep (se 1 (by rfl) ⟨1176713, by rfl⟩ : syracuseStep 1568951 = 2353427) B2353427
theorem B4190429 : Blo 650305 4190429 := bstep (se 3 (by rfl) ⟨785705, by rfl⟩ : syracuseStep 4190429 = 1571411) B1571411
theorem B979199 : Blo 650305 979199 := bstep (se 1 (by rfl) ⟨734399, by rfl⟩ : syracuseStep 979199 = 1468799) B1468799
theorem B652615 : Blo 650305 652615 := bstep (se 1 (by rfl) ⟨489461, by rfl⟩ : syracuseStep 652615 = 978923) B978923
theorem B980303 : Blo 650305 980303 := bstep (se 1 (by rfl) ⟨735227, by rfl⟩ : syracuseStep 980303 = 1470455) B1470455
theorem B980327 : Blo 650305 980327 := bstep (se 1 (by rfl) ⟨735245, by rfl⟩ : syracuseStep 980327 = 1470491) B1470491
theorem B652671 : Blo 650305 652671 := bstep (se 1 (by rfl) ⟨489503, by rfl⟩ : syracuseStep 652671 = 979007) B979007
theorem B13563425 : Blo 650305 13563425 := bstep (se 2 (by rfl) ⟨5086284, by rfl⟩ : syracuseStep 13563425 = 10172569) B10172569
theorem B1570643 : Blo 650305 1570643 := bstep (se 1 (by rfl) ⟨1177982, by rfl⟩ : syracuseStep 1570643 = 2355965) B2355965
theorem B653167 : Blo 650305 653167 := bstep (se 1 (by rfl) ⟨489875, by rfl⟩ : syracuseStep 653167 = 979751) B979751
theorem B2195099 : Blo 650305 2195099 := bstep (se 1 (by rfl) ⟨1646324, by rfl⟩ : syracuseStep 2195099 = 3292649) B3292649
theorem B1671131 : Blo 650305 1671131 := bstep (se 1 (by rfl) ⟨1253348, by rfl⟩ : syracuseStep 1671131 = 2506697) B2506697
theorem B3309983 : Blo 650305 3309983 := bstep (se 1 (by rfl) ⟨2482487, by rfl⟩ : syracuseStep 3309983 = 4964975) B4964975
theorem B15860717 : Blo 650305 15860717 := bstep (se 3 (by rfl) ⟨2973884, by rfl⟩ : syracuseStep 15860717 = 5947769) B5947769
theorem B1115803 : Blo 650305 1115803 := bstep (se 1 (by rfl) ⟨836852, by rfl⟩ : syracuseStep 1115803 = 1673705) B1673705
theorem B2198015 : Blo 650305 2198015 := bstep (se 1 (by rfl) ⟨1648511, by rfl⟩ : syracuseStep 2198015 = 3297023) B3297023
theorem B4689065 : Blo 650305 4689065 := bstep (se 2 (by rfl) ⟨1758399, by rfl⟩ : syracuseStep 4689065 = 3516799) B3516799
theorem B2198825 : Blo 650305 2198825 := bstep (se 2 (by rfl) ⟨824559, by rfl⟩ : syracuseStep 2198825 = 1649119) B1649119
theorem B17863325 : Blo 650305 17863325 := bstep (se 3 (by rfl) ⟨3349373, by rfl⟩ : syracuseStep 17863325 = 6698747) B6698747
theorem B4953311 : Blo 650305 4953311 := bstep (se 1 (by rfl) ⟨3714983, by rfl⟩ : syracuseStep 4953311 = 7429967) B7429967
theorem B2201039 : Blo 650305 2201039 := bstep (se 1 (by rfl) ⟨1650779, by rfl⟩ : syracuseStep 2201039 = 3301559) B3301559
theorem B2793619 : Blo 650305 2793619 := bstep (se 1 (by rfl) ⟨2095214, by rfl⟩ : syracuseStep 2793619 = 4190429) B4190429
theorem B17900459 : Blo 650305 17900459 := bstep (se 1 (by rfl) ⟨13425344, by rfl⟩ : syracuseStep 17900459 = 26850689) B26850689
theorem B12528229 : Blo 650305 12528229 := bstep (se 4 (by rfl) ⟨1174521, by rfl⟩ : syracuseStep 12528229 = 2349043) B2349043
theorem B13773725 : Blo 650305 13773725 := bstep (se 3 (by rfl) ⟨2582573, by rfl⟩ : syracuseStep 13773725 = 5165147) B5165147
theorem B17837617 : Blo 650305 17837617 := bstep (se 2 (by rfl) ⟨6689106, by rfl⟩ : syracuseStep 17837617 = 13378213) B13378213
theorem B32157371 : Blo 650305 32157371 := bstep (se 1 (by rfl) ⟨24118028, by rfl⟩ : syracuseStep 32157371 = 48236057) B48236057
theorem B1650395 : Blo 650305 1650395 := bstep (se 1 (by rfl) ⟨1237796, by rfl⟩ : syracuseStep 1650395 = 2475593) B2475593
theorem B1650415 : Blo 650305 1650415 := bstep (se 1 (by rfl) ⟨1237811, by rfl⟩ : syracuseStep 1650415 = 2475623) B2475623
theorem B19279741 : Blo 650305 19279741 := bstep (se 3 (by rfl) ⟨3614951, by rfl⟩ : syracuseStep 19279741 = 7229903) B7229903
theorem B2470247 : Blo 650305 2470247 := bstep (se 1 (by rfl) ⟨1852685, by rfl⟩ : syracuseStep 2470247 = 3705371) B3705371
theorem B3126215 : Blo 650305 3126215 := bstep (se 1 (by rfl) ⟨2344661, by rfl⟩ : syracuseStep 3126215 = 4689323) B4689323
theorem B1979369 : Blo 650305 1979369 := bstep (se 2 (by rfl) ⟨742263, by rfl⟩ : syracuseStep 1979369 = 1484527) B1484527
theorem B1651711 : Blo 650305 1651711 := bstep (se 1 (by rfl) ⟨1238783, by rfl⟩ : syracuseStep 1651711 = 2477567) B2477567
theorem B56603933 : Blo 650305 56603933 := bstep (se 3 (by rfl) ⟨10613237, by rfl⟩ : syracuseStep 56603933 = 21226475) B21226475
theorem B3716603 : Blo 650305 3716603 := bstep (se 1 (by rfl) ⟨2787452, by rfl⟩ : syracuseStep 3716603 = 5574905) B5574905
theorem B1324711 : Blo 650305 1324711 := bstep (se 1 (by rfl) ⟨993533, by rfl⟩ : syracuseStep 1324711 = 1987067) B1987067
theorem B2471705 : Blo 650305 2471705 := bstep (se 2 (by rfl) ⟨926889, by rfl⟩ : syracuseStep 2471705 = 1853779) B1853779
theorem B2472191 : Blo 650305 2472191 := bstep (se 1 (by rfl) ⟨1854143, by rfl⟩ : syracuseStep 2472191 = 3708287) B3708287
theorem B3717535 : Blo 650305 3717535 := bstep (se 1 (by rfl) ⟨2788151, by rfl⟩ : syracuseStep 3717535 = 5576303) B5576303
theorem B735727 : Blo 650305 735727 := bstep (se 1 (by rfl) ⟨551795, by rfl⟩ : syracuseStep 735727 = 1103591) B1103591
theorem B4700683 : Blo 650305 4700683 := bstep (se 1 (by rfl) ⟨3525512, by rfl⟩ : syracuseStep 4700683 = 7051025) B7051025
theorem B7060969 : Blo 650305 7060969 := bstep (se 2 (by rfl) ⟨2647863, by rfl⟩ : syracuseStep 7060969 = 5295727) B5295727
theorem B6275495 : Blo 650305 6275495 := bstep (se 1 (by rfl) ⟨4706621, by rfl⟩ : syracuseStep 6275495 = 9413243) B9413243
theorem B28918943 : Blo 650305 28918943 := bstep (se 1 (by rfl) ⟨21689207, by rfl⟩ : syracuseStep 28918943 = 43378415) B43378415
theorem B1853437 : Blo 650305 1853437 := bstep (se 3 (by rfl) ⟨347519, by rfl⟩ : syracuseStep 1853437 = 695039) B695039
theorem B3295403 : Blo 650305 3295403 := bstep (se 1 (by rfl) ⟨2471552, by rfl⟩ : syracuseStep 3295403 = 4943105) B4943105
theorem B5032595 : Blo 650305 5032595 := bstep (se 1 (by rfl) ⟨3774446, by rfl⟩ : syracuseStep 5032595 = 7548893) B7548893
theorem B1463399 : Blo 650305 1463399 := bstep (se 1 (by rfl) ⟨1097549, by rfl⟩ : syracuseStep 1463399 = 2195099) B2195099
theorem B1464083 : Blo 650305 1464083 := bstep (se 1 (by rfl) ⟨1098062, by rfl⟩ : syracuseStep 1464083 = 2196125) B2196125
theorem B1465703 : Blo 650305 1465703 := bstep (se 1 (by rfl) ⟨1099277, by rfl⟩ : syracuseStep 1465703 = 2198555) B2198555
theorem B2481911 : Blo 650305 2481911 := bstep (se 1 (by rfl) ⟨1861433, by rfl⟩ : syracuseStep 2481911 = 3722867) B3722867
theorem B1236961 : Blo 650305 1236961 := bstep (se 2 (by rfl) ⟨463860, by rfl⟩ : syracuseStep 1236961 = 927721) B927721
theorem B1466423 : Blo 650305 1466423 := bstep (se 1 (by rfl) ⟨1099817, by rfl⟩ : syracuseStep 1466423 = 2199635) B2199635
theorem B1466441 : Blo 650305 1466441 := bstep (se 2 (by rfl) ⟨549915, by rfl⟩ : syracuseStep 1466441 = 1099831) B1099831
theorem B2089577 : Blo 650305 2089577 := bstep (se 2 (by rfl) ⟨783591, by rfl⟩ : syracuseStep 2089577 = 1567183) B1567183
theorem B61924297 : Blo 650305 61924297 := bstep (se 2 (by rfl) ⟨23221611, by rfl⟩ : syracuseStep 61924297 = 46443223) B46443223
theorem B1467899 : Blo 650305 1467899 := bstep (se 1 (by rfl) ⟨1100924, by rfl⟩ : syracuseStep 1467899 = 2201849) B2201849
theorem B2091167 : Blo 650305 2091167 := bstep (se 1 (by rfl) ⟨1568375, by rfl⟩ : syracuseStep 2091167 = 3136751) B3136751
theorem B1862185 : Blo 650305 1862185 := bstep (se 2 (by rfl) ⟨698319, by rfl⟩ : syracuseStep 1862185 = 1396639) B1396639
theorem B1469267 : Blo 650305 1469267 := bstep (se 1 (by rfl) ⟨1101950, by rfl⟩ : syracuseStep 1469267 = 2203901) B2203901
theorem B977855 : Blo 650305 977855 := bstep (se 1 (by rfl) ⟨733391, by rfl⟩ : syracuseStep 977855 = 1466783) B1466783
theorem B977903 : Blo 650305 977903 := bstep (se 1 (by rfl) ⟨733427, by rfl⟩ : syracuseStep 977903 = 1466855) B1466855
theorem B650879 : Blo 650305 650879 := bstep (se 1 (by rfl) ⟨488159, by rfl⟩ : syracuseStep 650879 = 976319) B976319
theorem B651007 : Blo 650305 651007 := bstep (se 1 (by rfl) ⟨488255, by rfl⟩ : syracuseStep 651007 = 976511) B976511
theorem B651375 : Blo 650305 651375 := bstep (se 1 (by rfl) ⟨488531, by rfl⟩ : syracuseStep 651375 = 977063) B977063
theorem B651515 : Blo 650305 651515 := bstep (se 1 (by rfl) ⟨488636, by rfl⟩ : syracuseStep 651515 = 977273) B977273
theorem B651807 : Blo 650305 651807 := bstep (se 1 (by rfl) ⟨488855, by rfl⟩ : syracuseStep 651807 = 977711) B977711
theorem B1045199 : Blo 650305 1045199 := bstep (se 1 (by rfl) ⟨783899, by rfl⟩ : syracuseStep 1045199 = 1567799) B1567799
theorem B652319 : Blo 650305 652319 := bstep (se 1 (by rfl) ⟨489239, by rfl⟩ : syracuseStep 652319 = 978479) B978479
theorem B980105 : Blo 650305 980105 := bstep (se 2 (by rfl) ⟨367539, by rfl⟩ : syracuseStep 980105 = 735079) B735079
theorem B652519 : Blo 650305 652519 := bstep (se 1 (by rfl) ⟨489389, by rfl⟩ : syracuseStep 652519 = 978779) B978779
theorem B652647 : Blo 650305 652647 := bstep (se 1 (by rfl) ⟨489485, by rfl⟩ : syracuseStep 652647 = 978971) B978971
theorem B4191659 : Blo 650305 4191659 := bstep (se 1 (by rfl) ⟨3143744, by rfl⟩ : syracuseStep 4191659 = 6287489) B6287489
theorem B1045967 : Blo 650305 1045967 := bstep (se 1 (by rfl) ⟨784475, by rfl⟩ : syracuseStep 1045967 = 1568951) B1568951
theorem B652799 : Blo 650305 652799 := bstep (se 1 (by rfl) ⟨489599, by rfl⟩ : syracuseStep 652799 = 979199) B979199
theorem B653535 : Blo 650305 653535 := bstep (se 1 (by rfl) ⟨490151, by rfl⟩ : syracuseStep 653535 = 980303) B980303
theorem B653551 : Blo 650305 653551 := bstep (se 1 (by rfl) ⟨490163, by rfl⟩ : syracuseStep 653551 = 980327) B980327
theorem B9042283 : Blo 650305 9042283 := bstep (se 1 (by rfl) ⟨6781712, by rfl⟩ : syracuseStep 9042283 = 13563425) B13563425
theorem B1047095 : Blo 650305 1047095 := bstep (se 1 (by rfl) ⟨785321, by rfl⟩ : syracuseStep 1047095 = 1570643) B1570643
theorem B18841247 : Blo 650305 18841247 := bstep (se 1 (by rfl) ⟨14130935, by rfl⟩ : syracuseStep 18841247 = 28261871) B28261871
theorem B21135167 : Blo 650305 21135167 := bstep (se 1 (by rfl) ⟨15851375, by rfl⟩ : syracuseStep 21135167 = 31702751) B31702751
theorem B2195369 : Blo 650305 2195369 := bstep (se 2 (by rfl) ⟨823263, by rfl⟩ : syracuseStep 2195369 = 1646527) B1646527
theorem B1114087 : Blo 650305 1114087 := bstep (se 1 (by rfl) ⟨835565, by rfl⟩ : syracuseStep 1114087 = 1671131) B1671131
theorem B2196935 : Blo 650305 2196935 := bstep (se 1 (by rfl) ⟨1647701, by rfl⟩ : syracuseStep 2196935 = 3295403) B3295403
theorem B2789245 : Blo 650305 2789245 := bstep (se 3 (by rfl) ⟨522983, by rfl⟩ : syracuseStep 2789245 = 1045967) B1045967
theorem B2200553 : Blo 650305 2200553 := bstep (se 2 (by rfl) ⟨825207, by rfl⟩ : syracuseStep 2200553 = 1650415) B1650415
theorem B11933639 : Blo 650305 11933639 := bstep (se 1 (by rfl) ⟨8950229, by rfl⟩ : syracuseStep 11933639 = 17900459) B17900459
theorem B2202281 : Blo 650305 2202281 := bstep (se 2 (by rfl) ⟨825855, by rfl⟩ : syracuseStep 2202281 = 1651711) B1651711
theorem B9182483 : Blo 650305 9182483 := bstep (se 1 (by rfl) ⟨6886862, by rfl⟩ : syracuseStep 9182483 = 13773725) B13773725
theorem B1646831 : Blo 650305 1646831 := bstep (se 1 (by rfl) ⟨1235123, by rfl⟩ : syracuseStep 1646831 = 2470247) B2470247
theorem B696799 : Blo 650305 696799 := bstep (se 1 (by rfl) ⟨522599, by rfl⟩ : syracuseStep 696799 = 1045199) B1045199
theorem B4956713 : Blo 650305 4956713 := bstep (se 2 (by rfl) ⟨1858767, by rfl⟩ : syracuseStep 4956713 = 3717535) B3717535
theorem B1319579 : Blo 650305 1319579 := bstep (se 1 (by rfl) ⟨989684, by rfl⟩ : syracuseStep 1319579 = 1979369) B1979369
theorem B6267577 : Blo 650305 6267577 := bstep (se 2 (by rfl) ⟨2350341, by rfl⟩ : syracuseStep 6267577 = 4700683) B4700683
theorem B2794439 : Blo 650305 2794439 := bstep (se 1 (by rfl) ⟨2095829, by rfl⟩ : syracuseStep 2794439 = 4191659) B4191659
theorem B1647803 : Blo 650305 1647803 := bstep (se 1 (by rfl) ⟨1235852, by rfl⟩ : syracuseStep 1647803 = 2471705) B2471705
theorem B1648127 : Blo 650305 1648127 := bstep (se 1 (by rfl) ⟨1236095, by rfl⟩ : syracuseStep 1648127 = 2472191) B2472191
theorem B698063 : Blo 650305 698063 := bstep (se 1 (by rfl) ⟨523547, by rfl⟩ : syracuseStep 698063 = 1047095) B1047095
theorem B9414625 : Blo 650305 9414625 := bstep (se 2 (by rfl) ⟨3530484, by rfl⟩ : syracuseStep 9414625 = 7060969) B7060969
theorem B12560831 : Blo 650305 12560831 := bstep (se 1 (by rfl) ⟨9420623, by rfl⟩ : syracuseStep 12560831 = 18841247) B18841247
theorem B1649281 : Blo 650305 1649281 := bstep (se 2 (by rfl) ⟨618480, by rfl⟩ : syracuseStep 1649281 = 1236961) B1236961
theorem B1485449 : Blo 650305 1485449 := bstep (se 2 (by rfl) ⟨557043, by rfl⟩ : syracuseStep 1485449 = 1114087) B1114087
theorem B2206655 : Blo 650305 2206655 := bstep (se 1 (by rfl) ⟨1654991, by rfl⟩ : syracuseStep 2206655 = 3309983) B3309983
theorem B19279295 : Blo 650305 19279295 := bstep (se 1 (by rfl) ⟨14459471, by rfl⟩ : syracuseStep 19279295 = 28918943) B28918943
theorem B3355063 : Blo 650305 3355063 := bstep (se 1 (by rfl) ⟨2516297, by rfl⟩ : syracuseStep 3355063 = 5032595) B5032595
theorem B3126043 : Blo 650305 3126043 := bstep (se 1 (by rfl) ⟨2344532, by rfl⟩ : syracuseStep 3126043 = 4689065) B4689065
theorem B1487737 : Blo 650305 1487737 := bstep (se 2 (by rfl) ⟨557901, by rfl⟩ : syracuseStep 1487737 = 1115803) B1115803
theorem B2471249 : Blo 650305 2471249 := bstep (se 2 (by rfl) ⟨926718, by rfl⟩ : syracuseStep 2471249 = 1853437) B1853437
theorem B11908883 : Blo 650305 11908883 := bstep (se 1 (by rfl) ⟨8931662, by rfl⟩ : syracuseStep 11908883 = 17863325) B17863325
theorem B1654607 : Blo 650305 1654607 := bstep (se 1 (by rfl) ⟨1240955, by rfl⟩ : syracuseStep 1654607 = 2481911) B2481911
theorem B25706321 : Blo 650305 25706321 := bstep (se 2 (by rfl) ⟨9639870, by rfl⟩ : syracuseStep 25706321 = 19279741) B19279741
theorem B1393051 : Blo 650305 1393051 := bstep (se 1 (by rfl) ⟨1044788, by rfl⟩ : syracuseStep 1393051 = 2089577) B2089577
theorem B1394111 : Blo 650305 1394111 := bstep (se 1 (by rfl) ⟨1045583, by rfl⟩ : syracuseStep 1394111 = 2091167) B2091167
theorem B1100263 : Blo 650305 1100263 := bstep (se 1 (by rfl) ⟨825197, by rfl⟩ : syracuseStep 1100263 = 1650395) B1650395
theorem B2084143 : Blo 650305 2084143 := bstep (se 1 (by rfl) ⟨1563107, by rfl⟩ : syracuseStep 2084143 = 3126215) B3126215
theorem B37735955 : Blo 650305 37735955 := bstep (se 1 (by rfl) ⟨28301966, by rfl⟩ : syracuseStep 37735955 = 56603933) B56603933
theorem B2477735 : Blo 650305 2477735 := bstep (se 1 (by rfl) ⟨1858301, by rfl⟩ : syracuseStep 2477735 = 3716603) B3716603
theorem B1463579 : Blo 650305 1463579 := bstep (se 1 (by rfl) ⟨1097684, by rfl⟩ : syracuseStep 1463579 = 2195369) B2195369
theorem B3724825 : Blo 650305 3724825 := bstep (se 2 (by rfl) ⟨1396809, by rfl⟩ : syracuseStep 3724825 = 2793619) B2793619
theorem B4183663 : Blo 650305 4183663 := bstep (se 1 (by rfl) ⟨3137747, by rfl⟩ : syracuseStep 4183663 = 6275495) B6275495
theorem B10573811 : Blo 650305 10573811 := bstep (se 1 (by rfl) ⟨7930358, by rfl⟩ : syracuseStep 10573811 = 15860717) B15860717
theorem B82565729 : Blo 650305 82565729 := bstep (se 2 (by rfl) ⟨30962148, by rfl⟩ : syracuseStep 82565729 = 61924297) B61924297
theorem B1465343 : Blo 650305 1465343 := bstep (se 1 (by rfl) ⟨1099007, by rfl⟩ : syracuseStep 1465343 = 2198015) B2198015
theorem B1465883 : Blo 650305 1465883 := bstep (se 1 (by rfl) ⟨1099412, by rfl⟩ : syracuseStep 1465883 = 2198825) B2198825
theorem B2482913 : Blo 650305 2482913 := bstep (se 2 (by rfl) ⟨931092, by rfl⟩ : syracuseStep 2482913 = 1862185) B1862185
theorem B975599 : Blo 650305 975599 := bstep (se 1 (by rfl) ⟨731699, by rfl⟩ : syracuseStep 975599 = 1463399) B1463399
theorem B16704305 : Blo 650305 16704305 := bstep (se 2 (by rfl) ⟨6264114, by rfl⟩ : syracuseStep 16704305 = 12528229) B12528229
theorem B3302207 : Blo 650305 3302207 := bstep (se 1 (by rfl) ⟨2476655, by rfl⟩ : syracuseStep 3302207 = 4953311) B4953311
theorem B1467359 : Blo 650305 1467359 := bstep (se 1 (by rfl) ⟨1100519, by rfl⟩ : syracuseStep 1467359 = 2201039) B2201039
theorem B976055 : Blo 650305 976055 := bstep (se 1 (by rfl) ⟨732041, by rfl⟩ : syracuseStep 976055 = 1464083) B1464083
theorem B23783489 : Blo 650305 23783489 := bstep (se 2 (by rfl) ⟨8918808, by rfl⟩ : syracuseStep 23783489 = 17837617) B17837617
theorem B977135 : Blo 650305 977135 := bstep (se 1 (by rfl) ⟨732851, by rfl⟩ : syracuseStep 977135 = 1465703) B1465703
theorem B977615 : Blo 650305 977615 := bstep (se 1 (by rfl) ⟨733211, by rfl⟩ : syracuseStep 977615 = 1466423) B1466423
theorem B977627 : Blo 650305 977627 := bstep (se 1 (by rfl) ⟨733220, by rfl⟩ : syracuseStep 977627 = 1466441) B1466441
theorem B978599 : Blo 650305 978599 := bstep (se 1 (by rfl) ⟨733949, by rfl⟩ : syracuseStep 978599 = 1467899) B1467899
theorem B979511 : Blo 650305 979511 := bstep (se 1 (by rfl) ⟨734633, by rfl⟩ : syracuseStep 979511 = 1469267) B1469267
theorem B651903 : Blo 650305 651903 := bstep (se 1 (by rfl) ⟨488927, by rfl⟩ : syracuseStep 651903 = 977855) B977855
theorem B651935 : Blo 650305 651935 := bstep (se 1 (by rfl) ⟨488951, by rfl⟩ : syracuseStep 651935 = 977903) B977903
theorem B1766281 : Blo 650305 1766281 := bstep (se 2 (by rfl) ⟨662355, by rfl⟩ : syracuseStep 1766281 = 1324711) B1324711
theorem B12056377 : Blo 650305 12056377 := bstep (se 2 (by rfl) ⟨4521141, by rfl⟩ : syracuseStep 12056377 = 9042283) B9042283
theorem B980969 : Blo 650305 980969 := bstep (se 2 (by rfl) ⟨367863, by rfl⟩ : syracuseStep 980969 = 735727) B735727
theorem B653403 : Blo 650305 653403 := bstep (se 1 (by rfl) ⟨490052, by rfl⟩ : syracuseStep 653403 = 980105) B980105
theorem B85752989 : Blo 650305 85752989 := bstep (se 3 (by rfl) ⟨16078685, by rfl⟩ : syracuseStep 85752989 = 32157371) B32157371
theorem B14090111 : Blo 650305 14090111 := bstep (se 1 (by rfl) ⟨10567583, by rfl⟩ : syracuseStep 14090111 = 21135167) B21135167
theorem B8356769 : Blo 650305 8356769 := bstep (se 2 (by rfl) ⟨3133788, by rfl⟩ : syracuseStep 8356769 = 6267577) B6267577
theorem B17893669 : Blo 650305 17893669 := bstep (se 4 (by rfl) ⟨1677531, by rfl⟩ : syracuseStep 17893669 = 3355063) B3355063
theorem B12552833 : Blo 650305 12552833 := bstep (se 2 (by rfl) ⟨4707312, by rfl⟩ : syracuseStep 12552833 = 9414625) B9414625
theorem B2199041 : Blo 650305 2199041 := bstep (se 2 (by rfl) ⟨824640, by rfl⟩ : syracuseStep 2199041 = 1649281) B1649281
theorem B7049207 : Blo 650305 7049207 := bstep (se 1 (by rfl) ⟨5286905, by rfl⟩ : syracuseStep 7049207 = 10573811) B10573811
theorem B7934597 : Blo 650305 7934597 := bstep (se 4 (by rfl) ⟨743868, by rfl⟩ : syracuseStep 7934597 = 1487737) B1487737
theorem B2201471 : Blo 650305 2201471 := bstep (se 1 (by rfl) ⟨1651103, by rfl⟩ : syracuseStep 2201471 = 3302207) B3302207
theorem B4168057 : Blo 650305 4168057 := bstep (se 2 (by rfl) ⟨1563021, by rfl⟩ : syracuseStep 4168057 = 3126043) B3126043
theorem B990299 : Blo 650305 990299 := bstep (se 1 (by rfl) ⟨742724, by rfl⟩ : syracuseStep 990299 = 1485449) B1485449
theorem B5578217 : Blo 650305 5578217 := bstep (se 2 (by rfl) ⟨2091831, by rfl⟩ : syracuseStep 5578217 = 4183663) B4183663
theorem B7446005 : Blo 650305 7446005 := bstep (se 5 (by rfl) ⟨349031, by rfl⟩ : syracuseStep 7446005 = 698063) B698063
theorem B12852863 : Blo 650305 12852863 := bstep (se 1 (by rfl) ⟨9639647, by rfl⟩ : syracuseStep 12852863 = 19279295) B19279295
theorem B1647499 : Blo 650305 1647499 := bstep (se 1 (by rfl) ⟨1235624, by rfl⟩ : syracuseStep 1647499 = 2471249) B2471249
theorem B7939255 : Blo 650305 7939255 := bstep (se 1 (by rfl) ⟨5954441, by rfl⟩ : syracuseStep 7939255 = 11908883) B11908883
theorem B929065 : Blo 650305 929065 := bstep (se 2 (by rfl) ⟨348399, by rfl⟩ : syracuseStep 929065 = 696799) B696799
theorem B929407 : Blo 650305 929407 := bstep (se 1 (by rfl) ⟨697055, by rfl⟩ : syracuseStep 929407 = 1394111) B1394111
theorem B1651823 : Blo 650305 1651823 := bstep (se 1 (by rfl) ⟨1238867, by rfl⟩ : syracuseStep 1651823 = 2477735) B2477735
theorem B7451837 : Blo 650305 7451837 := bstep (se 3 (by rfl) ⟨1397219, by rfl⟩ : syracuseStep 7451837 = 2794439) B2794439
theorem B3718993 : Blo 650305 3718993 := bstep (se 2 (by rfl) ⟨1394622, by rfl⟩ : syracuseStep 3718993 = 2789245) B2789245
theorem B1097887 : Blo 650305 1097887 := bstep (se 1 (by rfl) ⟨823415, by rfl⟩ : syracuseStep 1097887 = 1646831) B1646831
theorem B1655275 : Blo 650305 1655275 := bstep (se 1 (by rfl) ⟨1241456, by rfl⟩ : syracuseStep 1655275 = 2482913) B2482913
theorem B1098535 : Blo 650305 1098535 := bstep (se 1 (by rfl) ⟨823901, by rfl⟩ : syracuseStep 1098535 = 1647803) B1647803
theorem B1098751 : Blo 650305 1098751 := bstep (se 1 (by rfl) ⟨824063, by rfl⟩ : syracuseStep 1098751 = 1648127) B1648127
theorem B8373887 : Blo 650305 8373887 := bstep (se 1 (by rfl) ⟨6280415, by rfl⟩ : syracuseStep 8373887 = 12560831) B12560831
theorem B4966433 : Blo 650305 4966433 := bstep (se 2 (by rfl) ⟨1862412, by rfl⟩ : syracuseStep 4966433 = 3724825) B3724825
theorem B16075169 : Blo 650305 16075169 := bstep (se 2 (by rfl) ⟨6028188, by rfl⟩ : syracuseStep 16075169 = 12056377) B12056377
theorem B57168659 : Blo 650305 57168659 := bstep (se 1 (by rfl) ⟨42876494, by rfl⟩ : syracuseStep 57168659 = 85752989) B85752989
theorem B1103071 : Blo 650305 1103071 := bstep (se 1 (by rfl) ⟨827303, by rfl⟩ : syracuseStep 1103071 = 1654607) B1654607
theorem B9393407 : Blo 650305 9393407 := bstep (se 1 (by rfl) ⟨7045055, by rfl⟩ : syracuseStep 9393407 = 14090111) B14090111
theorem B1857401 : Blo 650305 1857401 := bstep (se 2 (by rfl) ⟨696525, by rfl⟩ : syracuseStep 1857401 = 1393051) B1393051
theorem B1464623 : Blo 650305 1464623 := bstep (se 1 (by rfl) ⟨1098467, by rfl⟩ : syracuseStep 1464623 = 2196935) B2196935
theorem B25157303 : Blo 650305 25157303 := bstep (se 1 (by rfl) ⟨18867977, by rfl⟩ : syracuseStep 25157303 = 37735955) B37735955
theorem B1467017 : Blo 650305 1467017 := bstep (se 2 (by rfl) ⟨550131, by rfl⟩ : syracuseStep 1467017 = 1100263) B1100263
theorem B1467035 : Blo 650305 1467035 := bstep (se 1 (by rfl) ⟨1100276, by rfl⟩ : syracuseStep 1467035 = 2200553) B2200553
theorem B975719 : Blo 650305 975719 := bstep (se 1 (by rfl) ⟨731789, by rfl⟩ : syracuseStep 975719 = 1463579) B1463579
theorem B7955759 : Blo 650305 7955759 := bstep (se 1 (by rfl) ⟨5966819, by rfl⟩ : syracuseStep 7955759 = 11933639) B11933639
theorem B2778857 : Blo 650305 2778857 := bstep (se 2 (by rfl) ⟨1042071, by rfl⟩ : syracuseStep 2778857 = 2084143) B2084143
theorem B55043819 : Blo 650305 55043819 := bstep (se 1 (by rfl) ⟨41282864, by rfl⟩ : syracuseStep 55043819 = 82565729) B82565729
theorem B1468187 : Blo 650305 1468187 := bstep (se 1 (by rfl) ⟨1101140, by rfl⟩ : syracuseStep 1468187 = 2202281) B2202281
theorem B976895 : Blo 650305 976895 := bstep (se 1 (by rfl) ⟨732671, by rfl⟩ : syracuseStep 976895 = 1465343) B1465343
theorem B6121655 : Blo 650305 6121655 := bstep (se 1 (by rfl) ⟨4591241, by rfl⟩ : syracuseStep 6121655 = 9182483) B9182483
theorem B977255 : Blo 650305 977255 := bstep (se 1 (by rfl) ⟨732941, by rfl⟩ : syracuseStep 977255 = 1465883) B1465883
theorem B3304475 : Blo 650305 3304475 := bstep (se 1 (by rfl) ⟨2478356, by rfl⟩ : syracuseStep 3304475 = 4956713) B4956713
theorem B879719 : Blo 650305 879719 := bstep (se 1 (by rfl) ⟨659789, by rfl⟩ : syracuseStep 879719 = 1319579) B1319579
theorem B650399 : Blo 650305 650399 := bstep (se 1 (by rfl) ⟨487799, by rfl⟩ : syracuseStep 650399 = 975599) B975599
theorem B11136203 : Blo 650305 11136203 := bstep (se 1 (by rfl) ⟨8352152, by rfl⟩ : syracuseStep 11136203 = 16704305) B16704305
theorem B978239 : Blo 650305 978239 := bstep (se 1 (by rfl) ⟨733679, by rfl⟩ : syracuseStep 978239 = 1467359) B1467359
theorem B650703 : Blo 650305 650703 := bstep (se 1 (by rfl) ⟨488027, by rfl⟩ : syracuseStep 650703 = 976055) B976055
theorem B2355041 : Blo 650305 2355041 := bstep (se 2 (by rfl) ⟨883140, by rfl⟩ : syracuseStep 2355041 = 1766281) B1766281
theorem B15855659 : Blo 650305 15855659 := bstep (se 1 (by rfl) ⟨11891744, by rfl⟩ : syracuseStep 15855659 = 23783489) B23783489
theorem B651423 : Blo 650305 651423 := bstep (se 1 (by rfl) ⟨488567, by rfl⟩ : syracuseStep 651423 = 977135) B977135
theorem B651743 : Blo 650305 651743 := bstep (se 1 (by rfl) ⟨488807, by rfl⟩ : syracuseStep 651743 = 977615) B977615
theorem B651751 : Blo 650305 651751 := bstep (se 1 (by rfl) ⟨488813, by rfl⟩ : syracuseStep 651751 = 977627) B977627
theorem B1471103 : Blo 650305 1471103 := bstep (se 1 (by rfl) ⟨1103327, by rfl⟩ : syracuseStep 1471103 = 2206655) B2206655
theorem B652399 : Blo 650305 652399 := bstep (se 1 (by rfl) ⟨489299, by rfl⟩ : syracuseStep 652399 = 978599) B978599
theorem B653007 : Blo 650305 653007 := bstep (se 1 (by rfl) ⟨489755, by rfl⟩ : syracuseStep 653007 = 979511) B979511
theorem B653979 : Blo 650305 653979 := bstep (se 1 (by rfl) ⟨490484, by rfl⟩ : syracuseStep 653979 = 980969) B980969
theorem B17137547 : Blo 650305 17137547 := bstep (se 1 (by rfl) ⟨12853160, by rfl⟩ : syracuseStep 17137547 = 25706321) B25706321
theorem B5571179 : Blo 650305 5571179 := bstep (se 1 (by rfl) ⟨4178384, by rfl⟩ : syracuseStep 5571179 = 8356769) B8356769
theorem B2196665 : Blo 650305 2196665 := bstep (se 2 (by rfl) ⟨823749, by rfl⟩ : syracuseStep 2196665 = 1647499) B1647499
theorem B3310955 : Blo 650305 3310955 := bstep (se 1 (by rfl) ⟨2483216, by rfl⟩ : syracuseStep 3310955 = 4966433) B4966433
theorem B10585673 : Blo 650305 10585673 := bstep (se 2 (by rfl) ⟨3969627, by rfl⟩ : syracuseStep 10585673 = 7939255) B7939255
theorem B10716779 : Blo 650305 10716779 := bstep (se 1 (by rfl) ⟨8037584, by rfl⟩ : syracuseStep 10716779 = 16075169) B16075169
theorem B23858225 : Blo 650305 23858225 := bstep (se 2 (by rfl) ⟨8946834, by rfl⟩ : syracuseStep 23858225 = 17893669) B17893669
theorem B38112439 : Blo 650305 38112439 := bstep (se 1 (by rfl) ⟨28584329, by rfl⟩ : syracuseStep 38112439 = 57168659) B57168659
theorem B6262271 : Blo 650305 6262271 := bstep (se 1 (by rfl) ⟨4696703, by rfl⟩ : syracuseStep 6262271 = 9393407) B9393407
theorem B660199 : Blo 650305 660199 := bstep (se 1 (by rfl) ⟨495149, by rfl⟩ : syracuseStep 660199 = 990299) B990299
theorem B2202983 : Blo 650305 2202983 := bstep (se 1 (by rfl) ⟨1652237, by rfl⟩ : syracuseStep 2202983 = 3304475) B3304475
theorem B4958657 : Blo 650305 4958657 := bstep (se 2 (by rfl) ⟨1859496, by rfl⟩ : syracuseStep 4958657 = 3718993) B3718993
theorem B2207033 : Blo 650305 2207033 := bstep (se 2 (by rfl) ⟨827637, by rfl⟩ : syracuseStep 2207033 = 1655275) B1655275
theorem B5582591 : Blo 650305 5582591 := bstep (se 1 (by rfl) ⟨4186943, by rfl⟩ : syracuseStep 5582591 = 8373887) B8373887
theorem B8368555 : Blo 650305 8368555 := bstep (se 1 (by rfl) ⟨6276416, by rfl⟩ : syracuseStep 8368555 = 12552833) B12552833
theorem B4699471 : Blo 650305 4699471 := bstep (se 1 (by rfl) ⟨3524603, by rfl⟩ : syracuseStep 4699471 = 7049207) B7049207
theorem B5289731 : Blo 650305 5289731 := bstep (se 1 (by rfl) ⟨3967298, by rfl⟩ : syracuseStep 5289731 = 7934597) B7934597
theorem B21215357 : Blo 650305 21215357 := bstep (se 3 (by rfl) ⟨3977879, by rfl⟩ : syracuseStep 21215357 = 7955759) B7955759
theorem B3718811 : Blo 650305 3718811 := bstep (se 1 (by rfl) ⟨2789108, by rfl⟩ : syracuseStep 3718811 = 5578217) B5578217
theorem B4964003 : Blo 650305 4964003 := bstep (se 1 (by rfl) ⟨3723002, by rfl⟩ : syracuseStep 4964003 = 7446005) B7446005
theorem B8568575 : Blo 650305 8568575 := bstep (se 1 (by rfl) ⟨6426431, by rfl⟩ : syracuseStep 8568575 = 12852863) B12852863
theorem B1852571 : Blo 650305 1852571 := bstep (se 1 (by rfl) ⟨1389428, by rfl⟩ : syracuseStep 1852571 = 2778857) B2778857
theorem B4081103 : Blo 650305 4081103 := bstep (se 1 (by rfl) ⟨3060827, by rfl⟩ : syracuseStep 4081103 = 6121655) B6121655
theorem B7424135 : Blo 650305 7424135 := bstep (se 1 (by rfl) ⟨5568101, by rfl⟩ : syracuseStep 7424135 = 11136203) B11136203
theorem B10570439 : Blo 650305 10570439 := bstep (se 1 (by rfl) ⟨7927829, by rfl⟩ : syracuseStep 10570439 = 15855659) B15855659
theorem B2345917 : Blo 650305 2345917 := bstep (se 3 (by rfl) ⟨439859, by rfl⟩ : syracuseStep 2345917 = 879719) B879719
theorem B5557409 : Blo 650305 5557409 := bstep (se 2 (by rfl) ⟨2084028, by rfl⟩ : syracuseStep 5557409 = 4168057) B4168057
theorem B1101215 : Blo 650305 1101215 := bstep (se 1 (by rfl) ⟨825911, by rfl⟩ : syracuseStep 1101215 = 1651823) B1651823
theorem B4967891 : Blo 650305 4967891 := bstep (se 1 (by rfl) ⟨3725918, by rfl⟩ : syracuseStep 4967891 = 7451837) B7451837
theorem B11425031 : Blo 650305 11425031 := bstep (se 1 (by rfl) ⟨8568773, by rfl⟩ : syracuseStep 11425031 = 17137547) B17137547
theorem B1463849 : Blo 650305 1463849 := bstep (se 2 (by rfl) ⟨548943, by rfl⟩ : syracuseStep 1463849 = 1097887) B1097887
theorem B1464713 : Blo 650305 1464713 := bstep (se 2 (by rfl) ⟨549267, by rfl⟩ : syracuseStep 1464713 = 1098535) B1098535
theorem B1465001 : Blo 650305 1465001 := bstep (se 2 (by rfl) ⟨549375, by rfl⟩ : syracuseStep 1465001 = 1098751) B1098751
theorem B1466027 : Blo 650305 1466027 := bstep (se 1 (by rfl) ⟨1099520, by rfl⟩ : syracuseStep 1466027 = 2199041) B2199041
theorem B1238267 : Blo 650305 1238267 := bstep (se 1 (by rfl) ⟨928700, by rfl⟩ : syracuseStep 1238267 = 1857401) B1857401
theorem B1467647 : Blo 650305 1467647 := bstep (se 1 (by rfl) ⟨1100735, by rfl⟩ : syracuseStep 1467647 = 2201471) B2201471
theorem B976415 : Blo 650305 976415 := bstep (se 1 (by rfl) ⟨732311, by rfl⟩ : syracuseStep 976415 = 1464623) B1464623
theorem B1238753 : Blo 650305 1238753 := bstep (se 2 (by rfl) ⟨464532, by rfl⟩ : syracuseStep 1238753 = 929065) B929065
theorem B1239209 : Blo 650305 1239209 := bstep (se 2 (by rfl) ⟨464703, by rfl⟩ : syracuseStep 1239209 = 929407) B929407
theorem B16771535 : Blo 650305 16771535 := bstep (se 1 (by rfl) ⟨12578651, by rfl⟩ : syracuseStep 16771535 = 25157303) B25157303
theorem B978011 : Blo 650305 978011 := bstep (se 1 (by rfl) ⟨733508, by rfl⟩ : syracuseStep 978011 = 1467017) B1467017
theorem B978023 : Blo 650305 978023 := bstep (se 1 (by rfl) ⟨733517, by rfl⟩ : syracuseStep 978023 = 1467035) B1467035
theorem B650479 : Blo 650305 650479 := bstep (se 1 (by rfl) ⟨487859, by rfl⟩ : syracuseStep 650479 = 975719) B975719
theorem B36695879 : Blo 650305 36695879 := bstep (se 1 (by rfl) ⟨27521909, by rfl⟩ : syracuseStep 36695879 = 55043819) B55043819
theorem B978791 : Blo 650305 978791 := bstep (se 1 (by rfl) ⟨734093, by rfl⟩ : syracuseStep 978791 = 1468187) B1468187
theorem B651263 : Blo 650305 651263 := bstep (se 1 (by rfl) ⟨488447, by rfl⟩ : syracuseStep 651263 = 976895) B976895
theorem B651503 : Blo 650305 651503 := bstep (se 1 (by rfl) ⟨488627, by rfl⟩ : syracuseStep 651503 = 977255) B977255
theorem B1470761 : Blo 650305 1470761 := bstep (se 2 (by rfl) ⟨551535, by rfl⟩ : syracuseStep 1470761 = 1103071) B1103071
theorem B652159 : Blo 650305 652159 := bstep (se 1 (by rfl) ⟨489119, by rfl⟩ : syracuseStep 652159 = 978239) B978239
theorem B1570027 : Blo 650305 1570027 := bstep (se 1 (by rfl) ⟨1177520, by rfl⟩ : syracuseStep 1570027 = 2355041) B2355041
theorem B980735 : Blo 650305 980735 := bstep (se 1 (by rfl) ⟨735551, by rfl⟩ : syracuseStep 980735 = 1471103) B1471103
theorem B2720735 : Blo 650305 2720735 := bstep (se 1 (by rfl) ⟨2040551, by rfl⟩ : syracuseStep 2720735 = 4081103) B4081103
theorem B7144519 : Blo 650305 7144519 := bstep (se 1 (by rfl) ⟨5358389, by rfl⟩ : syracuseStep 7144519 = 10716779) B10716779
theorem B4949423 : Blo 650305 4949423 := bstep (se 1 (by rfl) ⟨3712067, by rfl⟩ : syracuseStep 4949423 = 7424135) B7424135
theorem B7046959 : Blo 650305 7046959 := bstep (se 1 (by rfl) ⟨5285219, by rfl⟩ : syracuseStep 7046959 = 10570439) B10570439
theorem B3704939 : Blo 650305 3704939 := bstep (se 1 (by rfl) ⟨2778704, by rfl⟩ : syracuseStep 3704939 = 5557409) B5557409
theorem B3311927 : Blo 650305 3311927 := bstep (se 1 (by rfl) ⟨2483945, by rfl⟩ : syracuseStep 3311927 = 4967891) B4967891
theorem B826139 : Blo 650305 826139 := bstep (se 1 (by rfl) ⟨619604, by rfl⟩ : syracuseStep 826139 = 1239209) B1239209
theorem B11181023 : Blo 650305 11181023 := bstep (se 1 (by rfl) ⟨8385767, by rfl⟩ : syracuseStep 11181023 = 16771535) B16771535
theorem B6265961 : Blo 650305 6265961 := bstep (se 2 (by rfl) ⟨2349735, by rfl⟩ : syracuseStep 6265961 = 4699471) B4699471
theorem B5712383 : Blo 650305 5712383 := bstep (se 1 (by rfl) ⟨4284287, by rfl⟩ : syracuseStep 5712383 = 8568575) B8568575
theorem B3714119 : Blo 650305 3714119 := bstep (se 1 (by rfl) ⟨2785589, by rfl⟩ : syracuseStep 3714119 = 5571179) B5571179
theorem B2207303 : Blo 650305 2207303 := bstep (se 1 (by rfl) ⟨1655477, by rfl⟩ : syracuseStep 2207303 = 3310955) B3310955
theorem B7057115 : Blo 650305 7057115 := bstep (se 1 (by rfl) ⟨5292836, by rfl⟩ : syracuseStep 7057115 = 10585673) B10585673
theorem B15905483 : Blo 650305 15905483 := bstep (se 1 (by rfl) ⟨11929112, by rfl⟩ : syracuseStep 15905483 = 23858225) B23858225
theorem B734143 : Blo 650305 734143 := bstep (se 1 (by rfl) ⟨550607, by rfl⟩ : syracuseStep 734143 = 1101215) B1101215
theorem B4174847 : Blo 650305 4174847 := bstep (se 1 (by rfl) ⟨3131135, by rfl⟩ : syracuseStep 4174847 = 6262271) B6262271
theorem B7616687 : Blo 650305 7616687 := bstep (se 1 (by rfl) ⟨5712515, by rfl⟩ : syracuseStep 7616687 = 11425031) B11425031
theorem B3127889 : Blo 650305 3127889 := bstep (se 2 (by rfl) ⟨1172958, by rfl⟩ : syracuseStep 3127889 = 2345917) B2345917
theorem B11158073 : Blo 650305 11158073 := bstep (se 2 (by rfl) ⟨4184277, by rfl⟩ : syracuseStep 11158073 = 8368555) B8368555
theorem B3721727 : Blo 650305 3721727 := bstep (se 1 (by rfl) ⟨2791295, by rfl⟩ : syracuseStep 3721727 = 5582591) B5582591
theorem B24463919 : Blo 650305 24463919 := bstep (se 1 (by rfl) ⟨18347939, by rfl⟩ : syracuseStep 24463919 = 36695879) B36695879
theorem B3526487 : Blo 650305 3526487 := bstep (se 1 (by rfl) ⟨2644865, by rfl⟩ : syracuseStep 3526487 = 5289731) B5289731
theorem B14143571 : Blo 650305 14143571 := bstep (se 1 (by rfl) ⟨10607678, by rfl⟩ : syracuseStep 14143571 = 21215357) B21215357
theorem B2479207 : Blo 650305 2479207 := bstep (se 1 (by rfl) ⟨1859405, by rfl⟩ : syracuseStep 2479207 = 3718811) B3718811
theorem B1464443 : Blo 650305 1464443 := bstep (se 1 (by rfl) ⟨1098332, by rfl⟩ : syracuseStep 1464443 = 2196665) B2196665
theorem B4940189 : Blo 650305 4940189 := bstep (se 3 (by rfl) ⟨926285, by rfl⟩ : syracuseStep 4940189 = 1852571) B1852571
theorem B3302045 : Blo 650305 3302045 := bstep (se 3 (by rfl) ⟨619133, by rfl⟩ : syracuseStep 3302045 = 1238267) B1238267
theorem B975899 : Blo 650305 975899 := bstep (se 1 (by rfl) ⟨731924, by rfl⟩ : syracuseStep 975899 = 1463849) B1463849
theorem B50816585 : Blo 650305 50816585 := bstep (se 2 (by rfl) ⟨19056219, by rfl⟩ : syracuseStep 50816585 = 38112439) B38112439
theorem B976475 : Blo 650305 976475 := bstep (se 1 (by rfl) ⟨732356, by rfl⟩ : syracuseStep 976475 = 1464713) B1464713
theorem B976667 : Blo 650305 976667 := bstep (se 1 (by rfl) ⟨732500, by rfl⟩ : syracuseStep 976667 = 1465001) B1465001
theorem B3303341 : Blo 650305 3303341 := bstep (se 3 (by rfl) ⟨619376, by rfl⟩ : syracuseStep 3303341 = 1238753) B1238753
theorem B1468655 : Blo 650305 1468655 := bstep (se 1 (by rfl) ⟨1101491, by rfl⟩ : syracuseStep 1468655 = 2202983) B2202983
theorem B977351 : Blo 650305 977351 := bstep (se 1 (by rfl) ⟨733013, by rfl⟩ : syracuseStep 977351 = 1466027) B1466027
theorem B978431 : Blo 650305 978431 := bstep (se 1 (by rfl) ⟨733823, by rfl⟩ : syracuseStep 978431 = 1467647) B1467647
theorem B880265 : Blo 650305 880265 := bstep (se 2 (by rfl) ⟨330099, by rfl⟩ : syracuseStep 880265 = 660199) B660199
theorem B650943 : Blo 650305 650943 := bstep (se 1 (by rfl) ⟨488207, by rfl⟩ : syracuseStep 650943 = 976415) B976415
theorem B3305771 : Blo 650305 3305771 := bstep (se 1 (by rfl) ⟨2479328, by rfl⟩ : syracuseStep 3305771 = 4958657) B4958657
theorem B2093369 : Blo 650305 2093369 := bstep (se 2 (by rfl) ⟨785013, by rfl⟩ : syracuseStep 2093369 = 1570027) B1570027
theorem B652007 : Blo 650305 652007 := bstep (se 1 (by rfl) ⟨489005, by rfl⟩ : syracuseStep 652007 = 978011) B978011
theorem B652015 : Blo 650305 652015 := bstep (se 1 (by rfl) ⟨489011, by rfl⟩ : syracuseStep 652015 = 978023) B978023
theorem B1471355 : Blo 650305 1471355 := bstep (se 1 (by rfl) ⟨1103516, by rfl⟩ : syracuseStep 1471355 = 2207033) B2207033
theorem B652527 : Blo 650305 652527 := bstep (se 1 (by rfl) ⟨489395, by rfl⟩ : syracuseStep 652527 = 978791) B978791
theorem B980507 : Blo 650305 980507 := bstep (se 1 (by rfl) ⟨735380, by rfl⟩ : syracuseStep 980507 = 1470761) B1470761
theorem B653823 : Blo 650305 653823 := bstep (se 1 (by rfl) ⟨490367, by rfl⟩ : syracuseStep 653823 = 980735) B980735
theorem B3309335 : Blo 650305 3309335 := bstep (se 1 (by rfl) ⟨2482001, by rfl⟩ : syracuseStep 3309335 = 4964003) B4964003
theorem B7438715 : Blo 650305 7438715 := bstep (se 1 (by rfl) ⟨5579036, by rfl⟩ : syracuseStep 7438715 = 11158073) B11158073
theorem B2201363 : Blo 650305 2201363 := bstep (se 1 (by rfl) ⟨1651022, by rfl⟩ : syracuseStep 2201363 = 3302045) B3302045
theorem B2202227 : Blo 650305 2202227 := bstep (se 1 (by rfl) ⟨1651670, by rfl⟩ : syracuseStep 2202227 = 3303341) B3303341
theorem B3808255 : Blo 650305 3808255 := bstep (se 1 (by rfl) ⟨2856191, by rfl⟩ : syracuseStep 3808255 = 5712383) B5712383
theorem B2203037 : Blo 650305 2203037 := bstep (se 3 (by rfl) ⟨413069, by rfl⟩ : syracuseStep 2203037 = 826139) B826139
theorem B2203847 : Blo 650305 2203847 := bstep (se 1 (by rfl) ⟨1652885, by rfl⟩ : syracuseStep 2203847 = 3305771) B3305771
theorem B2206223 : Blo 650305 2206223 := bstep (se 1 (by rfl) ⟨1654667, by rfl⟩ : syracuseStep 2206223 = 3309335) B3309335
theorem B1813823 : Blo 650305 1813823 := bstep (se 1 (by rfl) ⟨1360367, by rfl⟩ : syracuseStep 1813823 = 2720735) B2720735
theorem B5582317 : Blo 650305 5582317 := bstep (se 3 (by rfl) ⟨1046684, by rfl⟩ : syracuseStep 5582317 = 2093369) B2093369
theorem B2469959 : Blo 650305 2469959 := bstep (se 1 (by rfl) ⟨1852469, by rfl⟩ : syracuseStep 2469959 = 3704939) B3704939
theorem B2207951 : Blo 650305 2207951 := bstep (se 1 (by rfl) ⟨1655963, by rfl⟩ : syracuseStep 2207951 = 3311927) B3311927
theorem B135510893 : Blo 650305 135510893 := bstep (se 3 (by rfl) ⟨25408292, by rfl⟩ : syracuseStep 135510893 = 50816585) B50816585
theorem B7454015 : Blo 650305 7454015 := bstep (se 1 (by rfl) ⟨5590511, by rfl⟩ : syracuseStep 7454015 = 11181023) B11181023
theorem B4177307 : Blo 650305 4177307 := bstep (se 1 (by rfl) ⟨3132980, by rfl⟩ : syracuseStep 4177307 = 6265961) B6265961
theorem B3293459 : Blo 650305 3293459 := bstep (se 1 (by rfl) ⟨2470094, by rfl⟩ : syracuseStep 3293459 = 4940189) B4940189
theorem B2476079 : Blo 650305 2476079 := bstep (se 1 (by rfl) ⟨1857059, by rfl⟩ : syracuseStep 2476079 = 3714119) B3714119
theorem B4704743 : Blo 650305 4704743 := bstep (se 1 (by rfl) ⟨3528557, by rfl⟩ : syracuseStep 4704743 = 7057115) B7057115
theorem B10603655 : Blo 650305 10603655 := bstep (se 1 (by rfl) ⟨7952741, by rfl⟩ : syracuseStep 10603655 = 15905483) B15905483
theorem B2347373 : Blo 650305 2347373 := bstep (se 3 (by rfl) ⟨440132, by rfl⟩ : syracuseStep 2347373 = 880265) B880265
theorem B2085259 : Blo 650305 2085259 := bstep (se 1 (by rfl) ⟨1563944, by rfl⟩ : syracuseStep 2085259 = 3127889) B3127889
theorem B3299615 : Blo 650305 3299615 := bstep (se 1 (by rfl) ⟨2474711, by rfl⟩ : syracuseStep 3299615 = 4949423) B4949423
theorem B9526025 : Blo 650305 9526025 := bstep (se 2 (by rfl) ⟨3572259, by rfl⟩ : syracuseStep 9526025 = 7144519) B7144519
theorem B2481151 : Blo 650305 2481151 := bstep (se 1 (by rfl) ⟨1860863, by rfl⟩ : syracuseStep 2481151 = 3721727) B3721727
theorem B16309279 : Blo 650305 16309279 := bstep (se 1 (by rfl) ⟨12231959, by rfl⟩ : syracuseStep 16309279 = 24463919) B24463919
theorem B9395945 : Blo 650305 9395945 := bstep (se 2 (by rfl) ⟨3523479, by rfl⟩ : syracuseStep 9395945 = 7046959) B7046959
theorem B2350991 : Blo 650305 2350991 := bstep (se 1 (by rfl) ⟨1763243, by rfl⟩ : syracuseStep 2350991 = 3526487) B3526487
theorem B9429047 : Blo 650305 9429047 := bstep (se 1 (by rfl) ⟨7071785, by rfl⟩ : syracuseStep 9429047 = 14143571) B14143571
theorem B976295 : Blo 650305 976295 := bstep (se 1 (by rfl) ⟨732221, by rfl⟩ : syracuseStep 976295 = 1464443) B1464443
theorem B20311165 : Blo 650305 20311165 := bstep (se 3 (by rfl) ⟨3808343, by rfl⟩ : syracuseStep 20311165 = 7616687) B7616687
theorem B650599 : Blo 650305 650599 := bstep (se 1 (by rfl) ⟨487949, by rfl⟩ : syracuseStep 650599 = 975899) B975899
theorem B650983 : Blo 650305 650983 := bstep (se 1 (by rfl) ⟨488237, by rfl⟩ : syracuseStep 650983 = 976475) B976475
theorem B651111 : Blo 650305 651111 := bstep (se 1 (by rfl) ⟨488333, by rfl⟩ : syracuseStep 651111 = 976667) B976667
theorem B978857 : Blo 650305 978857 := bstep (se 2 (by rfl) ⟨367071, by rfl⟩ : syracuseStep 978857 = 734143) B734143
theorem B3305609 : Blo 650305 3305609 := bstep (se 2 (by rfl) ⟨1239603, by rfl⟩ : syracuseStep 3305609 = 2479207) B2479207
theorem B979103 : Blo 650305 979103 := bstep (se 1 (by rfl) ⟨734327, by rfl⟩ : syracuseStep 979103 = 1468655) B1468655
theorem B651567 : Blo 650305 651567 := bstep (se 1 (by rfl) ⟨488675, by rfl⟩ : syracuseStep 651567 = 977351) B977351
theorem B652287 : Blo 650305 652287 := bstep (se 1 (by rfl) ⟨489215, by rfl⟩ : syracuseStep 652287 = 978431) B978431
theorem B1471535 : Blo 650305 1471535 := bstep (se 1 (by rfl) ⟨1103651, by rfl⟩ : syracuseStep 1471535 = 2207303) B2207303
theorem B980903 : Blo 650305 980903 := bstep (se 1 (by rfl) ⟨735677, by rfl⟩ : syracuseStep 980903 = 1471355) B1471355
theorem B2783231 : Blo 650305 2783231 := bstep (se 1 (by rfl) ⟨2087423, by rfl⟩ : syracuseStep 2783231 = 4174847) B4174847
theorem B653671 : Blo 650305 653671 := bstep (se 1 (by rfl) ⟨490253, by rfl⟩ : syracuseStep 653671 = 980507) B980507
theorem B2195639 : Blo 650305 2195639 := bstep (se 1 (by rfl) ⟨1646729, by rfl⟩ : syracuseStep 2195639 = 3293459) B3293459
theorem B2199743 : Blo 650305 2199743 := bstep (se 1 (by rfl) ⟨1649807, by rfl⟩ : syracuseStep 2199743 = 3299615) B3299615
theorem B7443089 : Blo 650305 7443089 := bstep (se 2 (by rfl) ⟨2791158, by rfl⟩ : syracuseStep 7443089 = 5582317) B5582317
theorem B6263963 : Blo 650305 6263963 := bstep (se 1 (by rfl) ⟨4697972, by rfl⟩ : syracuseStep 6263963 = 9395945) B9395945
theorem B1646639 : Blo 650305 1646639 := bstep (se 1 (by rfl) ⟨1234979, by rfl⟩ : syracuseStep 1646639 = 2469959) B2469959
theorem B2203739 : Blo 650305 2203739 := bstep (se 1 (by rfl) ⟨1652804, by rfl⟩ : syracuseStep 2203739 = 3305609) B3305609
theorem B6269309 : Blo 650305 6269309 := bstep (se 3 (by rfl) ⟨1175495, by rfl⟩ : syracuseStep 6269309 = 2350991) B2350991
theorem B4959143 : Blo 650305 4959143 := bstep (se 1 (by rfl) ⟨3719357, by rfl⟩ : syracuseStep 4959143 = 7438715) B7438715
theorem B1650719 : Blo 650305 1650719 := bstep (se 1 (by rfl) ⟨1238039, by rfl⟩ : syracuseStep 1650719 = 2476079) B2476079
theorem B27081553 : Blo 650305 27081553 := bstep (se 2 (by rfl) ⟨10155582, by rfl⟩ : syracuseStep 27081553 = 20311165) B20311165
theorem B1855487 : Blo 650305 1855487 := bstep (se 1 (by rfl) ⟨1391615, by rfl⟩ : syracuseStep 1855487 = 2783231) B2783231
theorem B21745705 : Blo 650305 21745705 := bstep (se 2 (by rfl) ⟨8154639, by rfl⟩ : syracuseStep 21745705 = 16309279) B16309279
theorem B4969343 : Blo 650305 4969343 := bstep (se 1 (by rfl) ⟨3727007, by rfl⟩ : syracuseStep 4969343 = 7454015) B7454015
theorem B3136495 : Blo 650305 3136495 := bstep (se 1 (by rfl) ⟨2352371, by rfl⟩ : syracuseStep 3136495 = 4704743) B4704743
theorem B7069103 : Blo 650305 7069103 := bstep (se 1 (by rfl) ⟨5301827, by rfl⟩ : syracuseStep 7069103 = 10603655) B10603655
theorem B1564915 : Blo 650305 1564915 := bstep (se 1 (by rfl) ⟨1173686, by rfl⟩ : syracuseStep 1564915 = 2347373) B2347373
theorem B1467575 : Blo 650305 1467575 := bstep (se 1 (by rfl) ⟨1100681, by rfl⟩ : syracuseStep 1467575 = 2201363) B2201363
theorem B1468151 : Blo 650305 1468151 := bstep (se 1 (by rfl) ⟨1101113, by rfl⟩ : syracuseStep 1468151 = 2202227) B2202227
theorem B6350683 : Blo 650305 6350683 := bstep (se 1 (by rfl) ⟨4763012, by rfl⟩ : syracuseStep 6350683 = 9526025) B9526025
theorem B1468691 : Blo 650305 1468691 := bstep (se 1 (by rfl) ⟨1101518, by rfl⟩ : syracuseStep 1468691 = 2203037) B2203037
theorem B6286031 : Blo 650305 6286031 := bstep (se 1 (by rfl) ⟨4714523, by rfl⟩ : syracuseStep 6286031 = 9429047) B9429047
theorem B1469231 : Blo 650305 1469231 := bstep (se 1 (by rfl) ⟨1101923, by rfl⟩ : syracuseStep 1469231 = 2203847) B2203847
theorem B2780345 : Blo 650305 2780345 := bstep (se 2 (by rfl) ⟨1042629, by rfl⟩ : syracuseStep 2780345 = 2085259) B2085259
theorem B650863 : Blo 650305 650863 := bstep (se 1 (by rfl) ⟨488147, by rfl⟩ : syracuseStep 650863 = 976295) B976295
theorem B1470815 : Blo 650305 1470815 := bstep (se 1 (by rfl) ⟨1103111, by rfl⟩ : syracuseStep 1470815 = 2206223) B2206223
theorem B1209215 : Blo 650305 1209215 := bstep (se 1 (by rfl) ⟨906911, by rfl⟩ : syracuseStep 1209215 = 1813823) B1813823
theorem B652571 : Blo 650305 652571 := bstep (se 1 (by rfl) ⟨489428, by rfl⟩ : syracuseStep 652571 = 978857) B978857
theorem B652735 : Blo 650305 652735 := bstep (se 1 (by rfl) ⟨489551, by rfl⟩ : syracuseStep 652735 = 979103) B979103
theorem B1471967 : Blo 650305 1471967 := bstep (se 1 (by rfl) ⟨1103975, by rfl⟩ : syracuseStep 1471967 = 2207951) B2207951
theorem B981023 : Blo 650305 981023 := bstep (se 1 (by rfl) ⟨735767, by rfl⟩ : syracuseStep 981023 = 1471535) B1471535
theorem B653935 : Blo 650305 653935 := bstep (se 1 (by rfl) ⟨490451, by rfl⟩ : syracuseStep 653935 = 980903) B980903
theorem B5077673 : Blo 650305 5077673 := bstep (se 2 (by rfl) ⟨1904127, by rfl⟩ : syracuseStep 5077673 = 3808255) B3808255
theorem B3308201 : Blo 650305 3308201 := bstep (se 2 (by rfl) ⟨1240575, by rfl⟩ : syracuseStep 3308201 = 2481151) B2481151
theorem B90340595 : Blo 650305 90340595 := bstep (se 1 (by rfl) ⟨67755446, by rfl⟩ : syracuseStep 90340595 = 135510893) B135510893
theorem B2784871 : Blo 650305 2784871 := bstep (se 1 (by rfl) ⟨2088653, by rfl⟩ : syracuseStep 2784871 = 4177307) B4177307
theorem B3312895 : Blo 650305 3312895 := bstep (se 1 (by rfl) ⟨2484671, by rfl⟩ : syracuseStep 3312895 = 4969343) B4969343
theorem B3385115 : Blo 650305 3385115 := bstep (se 1 (by rfl) ⟨2538836, by rfl⟩ : syracuseStep 3385115 = 5077673) B5077673
theorem B2205467 : Blo 650305 2205467 := bstep (se 1 (by rfl) ⟨1654100, by rfl⟩ : syracuseStep 2205467 = 3308201) B3308201
theorem B3713161 : Blo 650305 3713161 := bstep (se 2 (by rfl) ⟨1392435, by rfl⟩ : syracuseStep 3713161 = 2784871) B2784871
theorem B3224573 : Blo 650305 3224573 := bstep (se 3 (by rfl) ⟨604607, by rfl⟩ : syracuseStep 3224573 = 1209215) B1209215
theorem B8467577 : Blo 650305 8467577 := bstep (se 2 (by rfl) ⟨3175341, by rfl⟩ : syracuseStep 8467577 = 6350683) B6350683
theorem B4962059 : Blo 650305 4962059 := bstep (se 1 (by rfl) ⟨3721544, by rfl⟩ : syracuseStep 4962059 = 7443089) B7443089
theorem B4175975 : Blo 650305 4175975 := bstep (se 1 (by rfl) ⟨3131981, by rfl⟩ : syracuseStep 4175975 = 6263963) B6263963
theorem B1097759 : Blo 650305 1097759 := bstep (se 1 (by rfl) ⟨823319, by rfl⟩ : syracuseStep 1097759 = 1646639) B1646639
theorem B4179539 : Blo 650305 4179539 := bstep (se 1 (by rfl) ⟨3134654, by rfl⟩ : syracuseStep 4179539 = 6269309) B6269309
theorem B1853563 : Blo 650305 1853563 := bstep (se 1 (by rfl) ⟨1390172, by rfl⟩ : syracuseStep 1853563 = 2780345) B2780345
theorem B1100479 : Blo 650305 1100479 := bstep (se 1 (by rfl) ⟨825359, by rfl⟩ : syracuseStep 1100479 = 1650719) B1650719
theorem B4181993 : Blo 650305 4181993 := bstep (se 2 (by rfl) ⟨1568247, by rfl⟩ : syracuseStep 4181993 = 3136495) B3136495
theorem B1463759 : Blo 650305 1463759 := bstep (se 1 (by rfl) ⟨1097819, by rfl⟩ : syracuseStep 1463759 = 2195639) B2195639
theorem B2086553 : Blo 650305 2086553 := bstep (se 2 (by rfl) ⟨782457, by rfl⟩ : syracuseStep 2086553 = 1564915) B1564915
theorem B1466495 : Blo 650305 1466495 := bstep (se 1 (by rfl) ⟨1099871, by rfl⟩ : syracuseStep 1466495 = 2199743) B2199743
theorem B4712735 : Blo 650305 4712735 := bstep (se 1 (by rfl) ⟨3534551, by rfl⟩ : syracuseStep 4712735 = 7069103) B7069103
theorem B28994273 : Blo 650305 28994273 := bstep (se 2 (by rfl) ⟨10872852, by rfl⟩ : syracuseStep 28994273 = 21745705) B21745705
theorem B1469159 : Blo 650305 1469159 := bstep (se 1 (by rfl) ⟨1101869, by rfl⟩ : syracuseStep 1469159 = 2203739) B2203739
theorem B978383 : Blo 650305 978383 := bstep (se 1 (by rfl) ⟨733787, by rfl⟩ : syracuseStep 978383 = 1467575) B1467575
theorem B978767 : Blo 650305 978767 := bstep (se 1 (by rfl) ⟨734075, by rfl⟩ : syracuseStep 978767 = 1468151) B1468151
theorem B979127 : Blo 650305 979127 := bstep (se 1 (by rfl) ⟨734345, by rfl⟩ : syracuseStep 979127 = 1468691) B1468691
theorem B4190687 : Blo 650305 4190687 := bstep (se 1 (by rfl) ⟨3143015, by rfl⟩ : syracuseStep 4190687 = 6286031) B6286031
theorem B979487 : Blo 650305 979487 := bstep (se 1 (by rfl) ⟨734615, by rfl⟩ : syracuseStep 979487 = 1469231) B1469231
theorem B3306095 : Blo 650305 3306095 := bstep (se 1 (by rfl) ⟨2479571, by rfl⟩ : syracuseStep 3306095 = 4959143) B4959143
theorem B980543 : Blo 650305 980543 := bstep (se 1 (by rfl) ⟨735407, by rfl⟩ : syracuseStep 980543 = 1470815) B1470815
theorem B981311 : Blo 650305 981311 := bstep (se 1 (by rfl) ⟨735983, by rfl⟩ : syracuseStep 981311 = 1471967) B1471967
theorem B36108737 : Blo 650305 36108737 := bstep (se 2 (by rfl) ⟨13540776, by rfl⟩ : syracuseStep 36108737 = 27081553) B27081553
theorem B654015 : Blo 650305 654015 := bstep (se 1 (by rfl) ⟨490511, by rfl⟩ : syracuseStep 654015 = 981023) B981023
theorem B60227063 : Blo 650305 60227063 := bstep (se 1 (by rfl) ⟨45170297, by rfl⟩ : syracuseStep 60227063 = 90340595) B90340595
theorem B4947965 : Blo 650305 4947965 := bstep (se 3 (by rfl) ⟨927743, by rfl⟩ : syracuseStep 4947965 = 1855487) B1855487
theorem B2786359 : Blo 650305 2786359 := bstep (se 1 (by rfl) ⟨2089769, by rfl⟩ : syracuseStep 2786359 = 4179539) B4179539
theorem B2787995 : Blo 650305 2787995 := bstep (se 1 (by rfl) ⟨2090996, by rfl⟩ : syracuseStep 2787995 = 4181993) B4181993
theorem B4950881 : Blo 650305 4950881 := bstep (se 2 (by rfl) ⟨1856580, by rfl⟩ : syracuseStep 4950881 = 3713161) B3713161
theorem B2793791 : Blo 650305 2793791 := bstep (se 1 (by rfl) ⟨2095343, by rfl⟩ : syracuseStep 2793791 = 4190687) B4190687
theorem B2204063 : Blo 650305 2204063 := bstep (se 1 (by rfl) ⟨1653047, by rfl⟩ : syracuseStep 2204063 = 3306095) B3306095
theorem B5645051 : Blo 650305 5645051 := bstep (se 1 (by rfl) ⟨4233788, by rfl⟩ : syracuseStep 5645051 = 8467577) B8467577
theorem B40151375 : Blo 650305 40151375 := bstep (se 1 (by rfl) ⟨30113531, by rfl⟩ : syracuseStep 40151375 = 60227063) B60227063
theorem B731839 : Blo 650305 731839 := bstep (se 1 (by rfl) ⟨548879, by rfl⟩ : syracuseStep 731839 = 1097759) B1097759
theorem B2471417 : Blo 650305 2471417 := bstep (se 2 (by rfl) ⟨926781, by rfl⟩ : syracuseStep 2471417 = 1853563) B1853563
theorem B1391035 : Blo 650305 1391035 := bstep (se 1 (by rfl) ⟨1043276, by rfl⟩ : syracuseStep 1391035 = 2086553) B2086553
theorem B2149715 : Blo 650305 2149715 := bstep (se 1 (by rfl) ⟨1612286, by rfl⟩ : syracuseStep 2149715 = 3224573) B3224573
theorem B24072491 : Blo 650305 24072491 := bstep (se 1 (by rfl) ⟨18054368, by rfl⟩ : syracuseStep 24072491 = 36108737) B36108737
theorem B3298643 : Blo 650305 3298643 := bstep (se 1 (by rfl) ⟨2473982, by rfl⟩ : syracuseStep 3298643 = 4947965) B4947965
theorem B1467305 : Blo 650305 1467305 := bstep (se 2 (by rfl) ⟨550239, by rfl⟩ : syracuseStep 1467305 = 1100479) B1100479
theorem B975839 : Blo 650305 975839 := bstep (se 1 (by rfl) ⟨731879, by rfl⟩ : syracuseStep 975839 = 1463759) B1463759
theorem B4417193 : Blo 650305 4417193 := bstep (se 2 (by rfl) ⟨1656447, by rfl⟩ : syracuseStep 4417193 = 3312895) B3312895
theorem B977663 : Blo 650305 977663 := bstep (se 1 (by rfl) ⟨733247, by rfl⟩ : syracuseStep 977663 = 1466495) B1466495
theorem B2256743 : Blo 650305 2256743 := bstep (se 1 (by rfl) ⟨1692557, by rfl⟩ : syracuseStep 2256743 = 3385115) B3385115
theorem B1470311 : Blo 650305 1470311 := bstep (se 1 (by rfl) ⟨1102733, by rfl⟩ : syracuseStep 1470311 = 2205467) B2205467
theorem B3141823 : Blo 650305 3141823 := bstep (se 1 (by rfl) ⟨2356367, by rfl⟩ : syracuseStep 3141823 = 4712735) B4712735
theorem B19329515 : Blo 650305 19329515 := bstep (se 1 (by rfl) ⟨14497136, by rfl⟩ : syracuseStep 19329515 = 28994273) B28994273
theorem B979439 : Blo 650305 979439 := bstep (se 1 (by rfl) ⟨734579, by rfl⟩ : syracuseStep 979439 = 1469159) B1469159
theorem B652255 : Blo 650305 652255 := bstep (se 1 (by rfl) ⟨489191, by rfl⟩ : syracuseStep 652255 = 978383) B978383
theorem B652511 : Blo 650305 652511 := bstep (se 1 (by rfl) ⟨489383, by rfl⟩ : syracuseStep 652511 = 978767) B978767
theorem B652751 : Blo 650305 652751 := bstep (se 1 (by rfl) ⟨489563, by rfl⟩ : syracuseStep 652751 = 979127) B979127
theorem B652991 : Blo 650305 652991 := bstep (se 1 (by rfl) ⟨489743, by rfl⟩ : syracuseStep 652991 = 979487) B979487
theorem B653695 : Blo 650305 653695 := bstep (se 1 (by rfl) ⟨490271, by rfl⟩ : syracuseStep 653695 = 980543) B980543
theorem B3308039 : Blo 650305 3308039 := bstep (se 1 (by rfl) ⟨2481029, by rfl⟩ : syracuseStep 3308039 = 4962059) B4962059
theorem B2783983 : Blo 650305 2783983 := bstep (se 1 (by rfl) ⟨2087987, by rfl⟩ : syracuseStep 2783983 = 4175975) B4175975
theorem B654207 : Blo 650305 654207 := bstep (se 1 (by rfl) ⟨490655, by rfl⟩ : syracuseStep 654207 = 981311) B981311
theorem B2199095 : Blo 650305 2199095 := bstep (se 1 (by rfl) ⟨1649321, by rfl⟩ : syracuseStep 2199095 = 3298643) B3298643
theorem B12886343 : Blo 650305 12886343 := bstep (se 1 (by rfl) ⟨9664757, by rfl⟩ : syracuseStep 12886343 = 19329515) B19329515
theorem B3711977 : Blo 650305 3711977 := bstep (se 2 (by rfl) ⟨1391991, by rfl⟩ : syracuseStep 3711977 = 2783983) B2783983
theorem B1647611 : Blo 650305 1647611 := bstep (se 1 (by rfl) ⟨1235708, by rfl⟩ : syracuseStep 1647611 = 2471417) B2471417
theorem B2205359 : Blo 650305 2205359 := bstep (se 1 (by rfl) ⟨1654019, by rfl⟩ : syracuseStep 2205359 = 3308039) B3308039
theorem B3715145 : Blo 650305 3715145 := bstep (se 2 (by rfl) ⟨1393179, by rfl⟩ : syracuseStep 3715145 = 2786359) B2786359
theorem B11779181 : Blo 650305 11779181 := bstep (se 3 (by rfl) ⟨2208596, by rfl⟩ : syracuseStep 11779181 = 4417193) B4417193
theorem B1854713 : Blo 650305 1854713 := bstep (se 2 (by rfl) ⟨695517, by rfl⟩ : syracuseStep 1854713 = 1391035) B1391035
theorem B1858663 : Blo 650305 1858663 := bstep (se 1 (by rfl) ⟨1393997, by rfl⟩ : syracuseStep 1858663 = 2787995) B2787995
theorem B3300587 : Blo 650305 3300587 := bstep (se 1 (by rfl) ⟨2475440, by rfl⟩ : syracuseStep 3300587 = 4950881) B4950881
theorem B1433143 : Blo 650305 1433143 := bstep (se 1 (by rfl) ⟨1074857, by rfl⟩ : syracuseStep 1433143 = 2149715) B2149715
theorem B16048327 : Blo 650305 16048327 := bstep (se 1 (by rfl) ⟨12036245, by rfl⟩ : syracuseStep 16048327 = 24072491) B24072491
theorem B975785 : Blo 650305 975785 := bstep (se 2 (by rfl) ⟨365919, by rfl⟩ : syracuseStep 975785 = 731839) B731839
theorem B1862527 : Blo 650305 1862527 := bstep (se 1 (by rfl) ⟨1396895, by rfl⟩ : syracuseStep 1862527 = 2793791) B2793791
theorem B4189097 : Blo 650305 4189097 := bstep (se 2 (by rfl) ⟨1570911, by rfl⟩ : syracuseStep 4189097 = 3141823) B3141823
theorem B1469375 : Blo 650305 1469375 := bstep (se 1 (by rfl) ⟨1102031, by rfl⟩ : syracuseStep 1469375 = 2204063) B2204063
theorem B3763367 : Blo 650305 3763367 := bstep (se 1 (by rfl) ⟨2822525, by rfl⟩ : syracuseStep 3763367 = 5645051) B5645051
theorem B978203 : Blo 650305 978203 := bstep (se 1 (by rfl) ⟨733652, by rfl⟩ : syracuseStep 978203 = 1467305) B1467305
theorem B650559 : Blo 650305 650559 := bstep (se 1 (by rfl) ⟨487919, by rfl⟩ : syracuseStep 650559 = 975839) B975839
theorem B26767583 : Blo 650305 26767583 := bstep (se 1 (by rfl) ⟨20075687, by rfl⟩ : syracuseStep 26767583 = 40151375) B40151375
theorem B651775 : Blo 650305 651775 := bstep (se 1 (by rfl) ⟨488831, by rfl⟩ : syracuseStep 651775 = 977663) B977663
theorem B1504495 : Blo 650305 1504495 := bstep (se 1 (by rfl) ⟨1128371, by rfl⟩ : syracuseStep 1504495 = 2256743) B2256743
theorem B980207 : Blo 650305 980207 := bstep (se 1 (by rfl) ⟨735155, by rfl⟩ : syracuseStep 980207 = 1470311) B1470311
theorem B652959 : Blo 650305 652959 := bstep (se 1 (by rfl) ⟨489719, by rfl⟩ : syracuseStep 652959 = 979439) B979439
theorem B21397769 : Blo 650305 21397769 := bstep (se 2 (by rfl) ⟨8024163, by rfl⟩ : syracuseStep 21397769 = 16048327) B16048327
theorem B2200391 : Blo 650305 2200391 := bstep (se 1 (by rfl) ⟨1650293, by rfl⟩ : syracuseStep 2200391 = 3300587) B3300587
theorem B8590895 : Blo 650305 8590895 := bstep (se 1 (by rfl) ⟨6443171, by rfl⟩ : syracuseStep 8590895 = 12886343) B12886343
theorem B2005993 : Blo 650305 2005993 := bstep (se 2 (by rfl) ⟨752247, by rfl⟩ : syracuseStep 2005993 = 1504495) B1504495
theorem B2792731 : Blo 650305 2792731 := bstep (se 1 (by rfl) ⟨2094548, by rfl⟩ : syracuseStep 2792731 = 4189097) B4189097
theorem B7643429 : Blo 650305 7643429 := bstep (se 4 (by rfl) ⟨716571, by rfl⟩ : syracuseStep 7643429 = 1433143) B1433143
theorem B2474651 : Blo 650305 2474651 := bstep (se 1 (by rfl) ⟨1855988, by rfl⟩ : syracuseStep 2474651 = 3711977) B3711977
theorem B1098407 : Blo 650305 1098407 := bstep (se 1 (by rfl) ⟨823805, by rfl⟩ : syracuseStep 1098407 = 1647611) B1647611
theorem B2508911 : Blo 650305 2508911 := bstep (se 1 (by rfl) ⟨1881683, by rfl⟩ : syracuseStep 2508911 = 3763367) B3763367
theorem B2476763 : Blo 650305 2476763 := bstep (se 1 (by rfl) ⟨1857572, by rfl⟩ : syracuseStep 2476763 = 3715145) B3715145
theorem B17845055 : Blo 650305 17845055 := bstep (se 1 (by rfl) ⟨13383791, by rfl⟩ : syracuseStep 17845055 = 26767583) B26767583
theorem B2478217 : Blo 650305 2478217 := bstep (se 2 (by rfl) ⟨929331, by rfl⟩ : syracuseStep 2478217 = 1858663) B1858663
theorem B7852787 : Blo 650305 7852787 := bstep (se 1 (by rfl) ⟨5889590, by rfl⟩ : syracuseStep 7852787 = 11779181) B11779181
theorem B1236475 : Blo 650305 1236475 := bstep (se 1 (by rfl) ⟨927356, by rfl⟩ : syracuseStep 1236475 = 1854713) B1854713
theorem B1466063 : Blo 650305 1466063 := bstep (se 1 (by rfl) ⟨1099547, by rfl⟩ : syracuseStep 1466063 = 2199095) B2199095
theorem B2483369 : Blo 650305 2483369 := bstep (se 2 (by rfl) ⟨931263, by rfl⟩ : syracuseStep 2483369 = 1862527) B1862527
theorem B650523 : Blo 650305 650523 := bstep (se 1 (by rfl) ⟨487892, by rfl⟩ : syracuseStep 650523 = 975785) B975785
theorem B1470239 : Blo 650305 1470239 := bstep (se 1 (by rfl) ⟨1102679, by rfl⟩ : syracuseStep 1470239 = 2205359) B2205359
theorem B979583 : Blo 650305 979583 := bstep (se 1 (by rfl) ⟨734687, by rfl⟩ : syracuseStep 979583 = 1469375) B1469375
theorem B652135 : Blo 650305 652135 := bstep (se 1 (by rfl) ⟨489101, by rfl⟩ : syracuseStep 652135 = 978203) B978203
theorem B653471 : Blo 650305 653471 := bstep (se 1 (by rfl) ⟨490103, by rfl⟩ : syracuseStep 653471 = 980207) B980207
theorem B1672607 : Blo 650305 1672607 := bstep (se 1 (by rfl) ⟨1254455, by rfl⟩ : syracuseStep 1672607 = 2508911) B2508911
theorem B11896703 : Blo 650305 11896703 := bstep (se 1 (by rfl) ⟨8922527, by rfl⟩ : syracuseStep 11896703 = 17845055) B17845055
theorem B1648633 : Blo 650305 1648633 := bstep (se 2 (by rfl) ⟨618237, by rfl⟩ : syracuseStep 1648633 = 1236475) B1236475
theorem B14265179 : Blo 650305 14265179 := bstep (se 1 (by rfl) ⟨10698884, by rfl⟩ : syracuseStep 14265179 = 21397769) B21397769
theorem B1649767 : Blo 650305 1649767 := bstep (se 1 (by rfl) ⟨1237325, by rfl⟩ : syracuseStep 1649767 = 2474651) B2474651
theorem B732271 : Blo 650305 732271 := bstep (se 1 (by rfl) ⟨549203, by rfl⟩ : syracuseStep 732271 = 1098407) B1098407
theorem B1651175 : Blo 650305 1651175 := bstep (se 1 (by rfl) ⟨1238381, by rfl⟩ : syracuseStep 1651175 = 2476763) B2476763
theorem B52868629 : Blo 650305 52868629 := bstep (se 6 (by rfl) ⟨1239108, by rfl⟩ : syracuseStep 52868629 = 2478217) B2478217
theorem B5095619 : Blo 650305 5095619 := bstep (se 1 (by rfl) ⟨3821714, by rfl⟩ : syracuseStep 5095619 = 7643429) B7643429
theorem B1655579 : Blo 650305 1655579 := bstep (se 1 (by rfl) ⟨1241684, by rfl⟩ : syracuseStep 1655579 = 2483369) B2483369
theorem B2674657 : Blo 650305 2674657 := bstep (se 2 (by rfl) ⟨1002996, by rfl⟩ : syracuseStep 2674657 = 2005993) B2005993
theorem B3723641 : Blo 650305 3723641 := bstep (se 2 (by rfl) ⟨1396365, by rfl⟩ : syracuseStep 3723641 = 2792731) B2792731
theorem B5235191 : Blo 650305 5235191 := bstep (se 1 (by rfl) ⟨3926393, by rfl⟩ : syracuseStep 5235191 = 7852787) B7852787
theorem B1466927 : Blo 650305 1466927 := bstep (se 1 (by rfl) ⟨1100195, by rfl⟩ : syracuseStep 1466927 = 2200391) B2200391
theorem B5727263 : Blo 650305 5727263 := bstep (se 1 (by rfl) ⟨4295447, by rfl⟩ : syracuseStep 5727263 = 8590895) B8590895
theorem B977375 : Blo 650305 977375 := bstep (se 1 (by rfl) ⟨733031, by rfl⟩ : syracuseStep 977375 = 1466063) B1466063
theorem B980159 : Blo 650305 980159 := bstep (se 1 (by rfl) ⟨735119, by rfl⟩ : syracuseStep 980159 = 1470239) B1470239
theorem B653055 : Blo 650305 653055 := bstep (se 1 (by rfl) ⟨489791, by rfl⟩ : syracuseStep 653055 = 979583) B979583
theorem B7931135 : Blo 650305 7931135 := bstep (se 1 (by rfl) ⟨5948351, by rfl⟩ : syracuseStep 7931135 = 11896703) B11896703
theorem B2198177 : Blo 650305 2198177 := bstep (se 2 (by rfl) ⟨824316, by rfl⟩ : syracuseStep 2198177 = 1648633) B1648633
theorem B15272701 : Blo 650305 15272701 := bstep (se 3 (by rfl) ⟨2863631, by rfl⟩ : syracuseStep 15272701 = 5727263) B5727263
theorem B4460285 : Blo 650305 4460285 := bstep (se 3 (by rfl) ⟨836303, by rfl⟩ : syracuseStep 4460285 = 1672607) B1672607
theorem B2199689 : Blo 650305 2199689 := bstep (se 2 (by rfl) ⟨824883, by rfl⟩ : syracuseStep 2199689 = 1649767) B1649767
theorem B9510119 : Blo 650305 9510119 := bstep (se 1 (by rfl) ⟨7132589, by rfl⟩ : syracuseStep 9510119 = 14265179) B14265179
theorem B70491505 : Blo 650305 70491505 := bstep (se 2 (by rfl) ⟨26434314, by rfl⟩ : syracuseStep 70491505 = 52868629) B52868629
theorem B3490127 : Blo 650305 3490127 := bstep (se 1 (by rfl) ⟨2617595, by rfl⟩ : syracuseStep 3490127 = 5235191) B5235191
theorem B1100783 : Blo 650305 1100783 := bstep (se 1 (by rfl) ⟨825587, by rfl⟩ : syracuseStep 1100783 = 1651175) B1651175
theorem B3397079 : Blo 650305 3397079 := bstep (se 1 (by rfl) ⟨2547809, by rfl⟩ : syracuseStep 3397079 = 5095619) B5095619
theorem B1103719 : Blo 650305 1103719 := bstep (se 1 (by rfl) ⟨827789, by rfl⟩ : syracuseStep 1103719 = 1655579) B1655579
theorem B2482427 : Blo 650305 2482427 := bstep (se 1 (by rfl) ⟨1861820, by rfl⟩ : syracuseStep 2482427 = 3723641) B3723641
theorem B976361 : Blo 650305 976361 := bstep (se 2 (by rfl) ⟨366135, by rfl⟩ : syracuseStep 976361 = 732271) B732271
theorem B3566209 : Blo 650305 3566209 := bstep (se 2 (by rfl) ⟨1337328, by rfl⟩ : syracuseStep 3566209 = 2674657) B2674657
theorem B977951 : Blo 650305 977951 := bstep (se 1 (by rfl) ⟨733463, by rfl⟩ : syracuseStep 977951 = 1466927) B1466927
theorem B651583 : Blo 650305 651583 := bstep (se 1 (by rfl) ⟨488687, by rfl⟩ : syracuseStep 651583 = 977375) B977375
theorem B653439 : Blo 650305 653439 := bstep (se 1 (by rfl) ⟨490079, by rfl⟩ : syracuseStep 653439 = 980159) B980159
theorem B2326751 : Blo 650305 2326751 := bstep (se 1 (by rfl) ⟨1745063, by rfl⟩ : syracuseStep 2326751 = 3490127) B3490127
theorem B4754945 : Blo 650305 4754945 := bstep (se 2 (by rfl) ⟨1783104, by rfl⟩ : syracuseStep 4754945 = 3566209) B3566209
theorem B2264719 : Blo 650305 2264719 := bstep (se 1 (by rfl) ⟨1698539, by rfl⟩ : syracuseStep 2264719 = 3397079) B3397079
theorem B93988673 : Blo 650305 93988673 := bstep (se 2 (by rfl) ⟨35245752, by rfl⟩ : syracuseStep 93988673 = 70491505) B70491505
theorem B733855 : Blo 650305 733855 := bstep (se 1 (by rfl) ⟨550391, by rfl⟩ : syracuseStep 733855 = 1100783) B1100783
theorem B21149693 : Blo 650305 21149693 := bstep (se 3 (by rfl) ⟨3965567, by rfl⟩ : syracuseStep 21149693 = 7931135) B7931135
theorem B6340079 : Blo 650305 6340079 := bstep (se 1 (by rfl) ⟨4755059, by rfl⟩ : syracuseStep 6340079 = 9510119) B9510119
theorem B1654951 : Blo 650305 1654951 := bstep (se 1 (by rfl) ⟨1241213, by rfl⟩ : syracuseStep 1654951 = 2482427) B2482427
theorem B1465451 : Blo 650305 1465451 := bstep (se 1 (by rfl) ⟨1099088, by rfl⟩ : syracuseStep 1465451 = 2198177) B2198177
theorem B2973523 : Blo 650305 2973523 := bstep (se 1 (by rfl) ⟨2230142, by rfl⟩ : syracuseStep 2973523 = 4460285) B4460285
theorem B1466459 : Blo 650305 1466459 := bstep (se 1 (by rfl) ⟨1099844, by rfl⟩ : syracuseStep 1466459 = 2199689) B2199689
theorem B81454405 : Blo 650305 81454405 := bstep (se 4 (by rfl) ⟨7636350, by rfl⟩ : syracuseStep 81454405 = 15272701) B15272701
theorem B650907 : Blo 650305 650907 := bstep (se 1 (by rfl) ⟨488180, by rfl⟩ : syracuseStep 650907 = 976361) B976361
theorem B651967 : Blo 650305 651967 := bstep (se 1 (by rfl) ⟨488975, by rfl⟩ : syracuseStep 651967 = 977951) B977951
theorem B1471625 : Blo 650305 1471625 := bstep (se 2 (by rfl) ⟨551859, by rfl⟩ : syracuseStep 1471625 = 1103719) B1103719
theorem B3019625 : Blo 650305 3019625 := bstep (se 2 (by rfl) ⟨1132359, by rfl⟩ : syracuseStep 3019625 = 2264719) B2264719
theorem B62659115 : Blo 650305 62659115 := bstep (se 1 (by rfl) ⟨46994336, by rfl⟩ : syracuseStep 62659115 = 93988673) B93988673
theorem B14099795 : Blo 650305 14099795 := bstep (se 1 (by rfl) ⟨10574846, by rfl⟩ : syracuseStep 14099795 = 21149693) B21149693
theorem B1551167 : Blo 650305 1551167 := bstep (se 1 (by rfl) ⟨1163375, by rfl⟩ : syracuseStep 1551167 = 2326751) B2326751
theorem B2206601 : Blo 650305 2206601 := bstep (se 2 (by rfl) ⟨827475, by rfl⟩ : syracuseStep 2206601 = 1654951) B1654951
theorem B108605873 : Blo 650305 108605873 := bstep (se 2 (by rfl) ⟨40727202, by rfl⟩ : syracuseStep 108605873 = 81454405) B81454405
theorem B3169963 : Blo 650305 3169963 := bstep (se 1 (by rfl) ⟨2377472, by rfl⟩ : syracuseStep 3169963 = 4754945) B4754945
theorem B976967 : Blo 650305 976967 := bstep (se 1 (by rfl) ⟨732725, by rfl⟩ : syracuseStep 976967 = 1465451) B1465451
theorem B977639 : Blo 650305 977639 := bstep (se 1 (by rfl) ⟨733229, by rfl⟩ : syracuseStep 977639 = 1466459) B1466459
theorem B978473 : Blo 650305 978473 := bstep (se 2 (by rfl) ⟨366927, by rfl⟩ : syracuseStep 978473 = 733855) B733855
theorem B981083 : Blo 650305 981083 := bstep (se 1 (by rfl) ⟨735812, by rfl⟩ : syracuseStep 981083 = 1471625) B1471625
theorem B16906877 : Blo 650305 16906877 := bstep (se 3 (by rfl) ⟨3170039, by rfl⟩ : syracuseStep 16906877 = 6340079) B6340079
theorem B3964697 : Blo 650305 3964697 := bstep (se 2 (by rfl) ⟨1486761, by rfl⟩ : syracuseStep 3964697 = 2973523) B2973523
theorem B2013083 : Blo 650305 2013083 := bstep (se 1 (by rfl) ⟨1509812, by rfl⟩ : syracuseStep 2013083 = 3019625) B3019625
theorem B1034111 : Blo 650305 1034111 := bstep (se 1 (by rfl) ⟨775583, by rfl⟩ : syracuseStep 1034111 = 1551167) B1551167
theorem B72403915 : Blo 650305 72403915 := bstep (se 1 (by rfl) ⟨54302936, by rfl⟩ : syracuseStep 72403915 = 108605873) B108605873
theorem B2643131 : Blo 650305 2643131 := bstep (se 1 (by rfl) ⟨1982348, by rfl⟩ : syracuseStep 2643131 = 3964697) B3964697
theorem B41772743 : Blo 650305 41772743 := bstep (se 1 (by rfl) ⟨31329557, by rfl⟩ : syracuseStep 41772743 = 62659115) B62659115
theorem B9399863 : Blo 650305 9399863 := bstep (se 1 (by rfl) ⟨7049897, by rfl⟩ : syracuseStep 9399863 = 14099795) B14099795
theorem B651311 : Blo 650305 651311 := bstep (se 1 (by rfl) ⟨488483, by rfl⟩ : syracuseStep 651311 = 976967) B976967
theorem B651759 : Blo 650305 651759 := bstep (se 1 (by rfl) ⟨488819, by rfl⟩ : syracuseStep 651759 = 977639) B977639
theorem B1471067 : Blo 650305 1471067 := bstep (se 1 (by rfl) ⟨1103300, by rfl⟩ : syracuseStep 1471067 = 2206601) B2206601
theorem B652315 : Blo 650305 652315 := bstep (se 1 (by rfl) ⟨489236, by rfl⟩ : syracuseStep 652315 = 978473) B978473
theorem B654055 : Blo 650305 654055 := bstep (se 1 (by rfl) ⟨490541, by rfl⟩ : syracuseStep 654055 = 981083) B981083
theorem B11271251 : Blo 650305 11271251 := bstep (se 1 (by rfl) ⟨8453438, by rfl⟩ : syracuseStep 11271251 = 16906877) B16906877
theorem B4226617 : Blo 650305 4226617 := bstep (se 2 (by rfl) ⟨1584981, by rfl⟩ : syracuseStep 4226617 = 3169963) B3169963
theorem B689407 : Blo 650305 689407 := bstep (se 1 (by rfl) ⟨517055, by rfl⟩ : syracuseStep 689407 = 1034111) B1034111
theorem B96538553 : Blo 650305 96538553 := bstep (se 2 (by rfl) ⟨36201957, by rfl⟩ : syracuseStep 96538553 = 72403915) B72403915
theorem B6266575 : Blo 650305 6266575 := bstep (se 1 (by rfl) ⟨4699931, by rfl⟩ : syracuseStep 6266575 = 9399863) B9399863
theorem B7514167 : Blo 650305 7514167 := bstep (se 1 (by rfl) ⟨5635625, by rfl⟩ : syracuseStep 7514167 = 11271251) B11271251
theorem B1762087 : Blo 650305 1762087 := bstep (se 1 (by rfl) ⟨1321565, by rfl⟩ : syracuseStep 1762087 = 2643131) B2643131
theorem B27848495 : Blo 650305 27848495 := bstep (se 1 (by rfl) ⟨20886371, by rfl⟩ : syracuseStep 27848495 = 41772743) B41772743
theorem B980711 : Blo 650305 980711 := bstep (se 1 (by rfl) ⟨735533, by rfl⟩ : syracuseStep 980711 = 1471067) B1471067
theorem B1342055 : Blo 650305 1342055 := bstep (se 1 (by rfl) ⟨1006541, by rfl⟩ : syracuseStep 1342055 = 2013083) B2013083
theorem B5635489 : Blo 650305 5635489 := bstep (se 2 (by rfl) ⟨2113308, by rfl⟩ : syracuseStep 5635489 = 4226617) B4226617
theorem B64359035 : Blo 650305 64359035 := bstep (se 1 (by rfl) ⟨48269276, by rfl⟩ : syracuseStep 64359035 = 96538553) B96538553
theorem B3676837 : Blo 650305 3676837 := bstep (se 4 (by rfl) ⟨344703, by rfl⟩ : syracuseStep 3676837 = 689407) B689407
theorem B3578813 : Blo 650305 3578813 := bstep (se 3 (by rfl) ⟨671027, by rfl⟩ : syracuseStep 3578813 = 1342055) B1342055
theorem B7513985 : Blo 650305 7513985 := bstep (se 2 (by rfl) ⟨2817744, by rfl⟩ : syracuseStep 7513985 = 5635489) B5635489
theorem B74262653 : Blo 650305 74262653 := bstep (se 3 (by rfl) ⟨13924247, by rfl⟩ : syracuseStep 74262653 = 27848495) B27848495
theorem B2349449 : Blo 650305 2349449 := bstep (se 2 (by rfl) ⟨881043, by rfl⟩ : syracuseStep 2349449 = 1762087) B1762087
theorem B10018889 : Blo 650305 10018889 := bstep (se 2 (by rfl) ⟨3757083, by rfl⟩ : syracuseStep 10018889 = 7514167) B7514167
theorem B653807 : Blo 650305 653807 := bstep (se 1 (by rfl) ⟨490355, by rfl⟩ : syracuseStep 653807 = 980711) B980711
theorem B8355433 : Blo 650305 8355433 := bstep (se 2 (by rfl) ⟨3133287, by rfl⟩ : syracuseStep 8355433 = 6266575) B6266575
theorem B42906023 : Blo 650305 42906023 := bstep (se 1 (by rfl) ⟨32179517, by rfl⟩ : syracuseStep 42906023 = 64359035) B64359035
theorem B20037293 : Blo 650305 20037293 := bstep (se 3 (by rfl) ⟨3756992, by rfl⟩ : syracuseStep 20037293 = 7513985) B7513985
theorem B4902449 : Blo 650305 4902449 := bstep (se 2 (by rfl) ⟨1838418, by rfl⟩ : syracuseStep 4902449 = 3676837) B3676837
theorem B1566299 : Blo 650305 1566299 := bstep (se 1 (by rfl) ⟨1174724, by rfl⟩ : syracuseStep 1566299 = 2349449) B2349449
theorem B2385875 : Blo 650305 2385875 := bstep (se 1 (by rfl) ⟨1789406, by rfl⟩ : syracuseStep 2385875 = 3578813) B3578813
theorem B6679259 : Blo 650305 6679259 := bstep (se 1 (by rfl) ⟨5009444, by rfl⟩ : syracuseStep 6679259 = 10018889) B10018889
theorem B49508435 : Blo 650305 49508435 := bstep (se 1 (by rfl) ⟨37131326, by rfl⟩ : syracuseStep 49508435 = 74262653) B74262653
theorem B11140577 : Blo 650305 11140577 := bstep (se 2 (by rfl) ⟨4177716, by rfl⟩ : syracuseStep 11140577 = 8355433) B8355433
theorem B132022493 : Blo 650305 132022493 := bstep (se 3 (by rfl) ⟨24754217, by rfl⟩ : syracuseStep 132022493 = 49508435) B49508435
theorem B6362333 : Blo 650305 6362333 := bstep (se 3 (by rfl) ⟨1192937, by rfl⟩ : syracuseStep 6362333 = 2385875) B2385875
theorem B7427051 : Blo 650305 7427051 := bstep (se 1 (by rfl) ⟨5570288, by rfl⟩ : syracuseStep 7427051 = 11140577) B11140577
theorem B13358195 : Blo 650305 13358195 := bstep (se 1 (by rfl) ⟨10018646, by rfl⟩ : syracuseStep 13358195 = 20037293) B20037293
theorem B52292789 : Blo 650305 52292789 := bstep (se 5 (by rfl) ⟨2451224, by rfl⟩ : syracuseStep 52292789 = 4902449) B4902449
theorem B1044199 : Blo 650305 1044199 := bstep (se 1 (by rfl) ⟨783149, by rfl⟩ : syracuseStep 1044199 = 1566299) B1566299
theorem B4452839 : Blo 650305 4452839 := bstep (se 1 (by rfl) ⟨3339629, by rfl⟩ : syracuseStep 4452839 = 6679259) B6679259
theorem B28604015 : Blo 650305 28604015 := bstep (se 1 (by rfl) ⟨21453011, by rfl⟩ : syracuseStep 28604015 = 42906023) B42906023
theorem B88014995 : Blo 650305 88014995 := bstep (se 1 (by rfl) ⟨66011246, by rfl⟩ : syracuseStep 88014995 = 132022493) B132022493
theorem B4951367 : Blo 650305 4951367 := bstep (se 1 (by rfl) ⟨3713525, by rfl⟩ : syracuseStep 4951367 = 7427051) B7427051
theorem B4241555 : Blo 650305 4241555 := bstep (se 1 (by rfl) ⟨3181166, by rfl⟩ : syracuseStep 4241555 = 6362333) B6362333
theorem B1392265 : Blo 650305 1392265 := bstep (se 2 (by rfl) ⟨522099, by rfl⟩ : syracuseStep 1392265 = 1044199) B1044199
theorem B2968559 : Blo 650305 2968559 := bstep (se 1 (by rfl) ⟨2226419, by rfl⟩ : syracuseStep 2968559 = 4452839) B4452839
theorem B8905463 : Blo 650305 8905463 := bstep (se 1 (by rfl) ⟨6679097, by rfl⟩ : syracuseStep 8905463 = 13358195) B13358195
theorem B34861859 : Blo 650305 34861859 := bstep (se 1 (by rfl) ⟨26146394, by rfl⟩ : syracuseStep 34861859 = 52292789) B52292789
theorem B19069343 : Blo 650305 19069343 := bstep (se 1 (by rfl) ⟨14302007, by rfl⟩ : syracuseStep 19069343 = 28604015) B28604015
theorem B5936975 : Blo 650305 5936975 := bstep (se 1 (by rfl) ⟨4452731, by rfl⟩ : syracuseStep 5936975 = 8905463) B8905463
theorem B23241239 : Blo 650305 23241239 := bstep (se 1 (by rfl) ⟨17430929, by rfl⟩ : syracuseStep 23241239 = 34861859) B34861859
theorem B2827703 : Blo 650305 2827703 := bstep (se 1 (by rfl) ⟨2120777, by rfl⟩ : syracuseStep 2827703 = 4241555) B4241555
theorem B1979039 : Blo 650305 1979039 := bstep (se 1 (by rfl) ⟨1484279, by rfl⟩ : syracuseStep 1979039 = 2968559) B2968559
theorem B1856353 : Blo 650305 1856353 := bstep (se 2 (by rfl) ⟨696132, by rfl⟩ : syracuseStep 1856353 = 1392265) B1392265
theorem B58676663 : Blo 650305 58676663 := bstep (se 1 (by rfl) ⟨44007497, by rfl⟩ : syracuseStep 58676663 = 88014995) B88014995
theorem B3300911 : Blo 650305 3300911 := bstep (se 1 (by rfl) ⟨2475683, by rfl⟩ : syracuseStep 3300911 = 4951367) B4951367
theorem B12712895 : Blo 650305 12712895 := bstep (se 1 (by rfl) ⟨9534671, by rfl⟩ : syracuseStep 12712895 = 19069343) B19069343
theorem B5277437 : Blo 650305 5277437 := bstep (se 3 (by rfl) ⟨989519, by rfl⟩ : syracuseStep 5277437 = 1979039) B1979039
theorem B2200607 : Blo 650305 2200607 := bstep (se 1 (by rfl) ⟨1650455, by rfl⟩ : syracuseStep 2200607 = 3300911) B3300911
theorem B1885135 : Blo 650305 1885135 := bstep (se 1 (by rfl) ⟨1413851, by rfl⟩ : syracuseStep 1885135 = 2827703) B2827703
theorem B2475137 : Blo 650305 2475137 := bstep (se 2 (by rfl) ⟨928176, by rfl⟩ : syracuseStep 2475137 = 1856353) B1856353
theorem B8475263 : Blo 650305 8475263 := bstep (se 1 (by rfl) ⟨6356447, by rfl⟩ : syracuseStep 8475263 = 12712895) B12712895
theorem B39117775 : Blo 650305 39117775 := bstep (se 1 (by rfl) ⟨29338331, by rfl⟩ : syracuseStep 39117775 = 58676663) B58676663
theorem B3957983 : Blo 650305 3957983 := bstep (se 1 (by rfl) ⟨2968487, by rfl⟩ : syracuseStep 3957983 = 5936975) B5936975
theorem B15494159 : Blo 650305 15494159 := bstep (se 1 (by rfl) ⟨11620619, by rfl⟩ : syracuseStep 15494159 = 23241239) B23241239
theorem B10329439 : Blo 650305 10329439 := bstep (se 1 (by rfl) ⟨7747079, by rfl⟩ : syracuseStep 10329439 = 15494159) B15494159
theorem B1650091 : Blo 650305 1650091 := bstep (se 1 (by rfl) ⟨1237568, by rfl⟩ : syracuseStep 1650091 = 2475137) B2475137
theorem B3518291 : Blo 650305 3518291 := bstep (se 1 (by rfl) ⟨2638718, by rfl⟩ : syracuseStep 3518291 = 5277437) B5277437
theorem B5650175 : Blo 650305 5650175 := bstep (se 1 (by rfl) ⟨4237631, by rfl⟩ : syracuseStep 5650175 = 8475263) B8475263
theorem B2638655 : Blo 650305 2638655 := bstep (se 1 (by rfl) ⟨1978991, by rfl⟩ : syracuseStep 2638655 = 3957983) B3957983
theorem B52157033 : Blo 650305 52157033 := bstep (se 2 (by rfl) ⟨19558887, by rfl⟩ : syracuseStep 52157033 = 39117775) B39117775
theorem B2513513 : Blo 650305 2513513 := bstep (se 2 (by rfl) ⟨942567, by rfl⟩ : syracuseStep 2513513 = 1885135) B1885135
theorem B1467071 : Blo 650305 1467071 := bstep (se 1 (by rfl) ⟨1100303, by rfl⟩ : syracuseStep 1467071 = 2200607) B2200607
theorem B34771355 : Blo 650305 34771355 := bstep (se 1 (by rfl) ⟨26078516, by rfl⟩ : syracuseStep 34771355 = 52157033) B52157033
theorem B1675675 : Blo 650305 1675675 := bstep (se 1 (by rfl) ⟨1256756, by rfl⟩ : syracuseStep 1675675 = 2513513) B2513513
theorem B2200121 : Blo 650305 2200121 := bstep (se 2 (by rfl) ⟨825045, by rfl⟩ : syracuseStep 2200121 = 1650091) B1650091
theorem B13772585 : Blo 650305 13772585 := bstep (se 2 (by rfl) ⟨5164719, by rfl⟩ : syracuseStep 13772585 = 10329439) B10329439
theorem B2345527 : Blo 650305 2345527 := bstep (se 1 (by rfl) ⟨1759145, by rfl⟩ : syracuseStep 2345527 = 3518291) B3518291
theorem B1759103 : Blo 650305 1759103 := bstep (se 1 (by rfl) ⟨1319327, by rfl⟩ : syracuseStep 1759103 = 2638655) B2638655
theorem B15067133 : Blo 650305 15067133 := bstep (se 3 (by rfl) ⟨2825087, by rfl⟩ : syracuseStep 15067133 = 5650175) B5650175
theorem B978047 : Blo 650305 978047 := bstep (se 1 (by rfl) ⟨733535, by rfl⟩ : syracuseStep 978047 = 1467071) B1467071
theorem B2234233 : Blo 650305 2234233 := bstep (se 2 (by rfl) ⟨837837, by rfl⟩ : syracuseStep 2234233 = 1675675) B1675675
theorem B9181723 : Blo 650305 9181723 := bstep (se 1 (by rfl) ⟨6886292, by rfl⟩ : syracuseStep 9181723 = 13772585) B13772585
theorem B23180903 : Blo 650305 23180903 := bstep (se 1 (by rfl) ⟨17385677, by rfl⟩ : syracuseStep 23180903 = 34771355) B34771355
theorem B3127369 : Blo 650305 3127369 := bstep (se 2 (by rfl) ⟨1172763, by rfl⟩ : syracuseStep 3127369 = 2345527) B2345527
theorem B10044755 : Blo 650305 10044755 := bstep (se 1 (by rfl) ⟨7533566, by rfl⟩ : syracuseStep 10044755 = 15067133) B15067133
theorem B1466747 : Blo 650305 1466747 := bstep (se 1 (by rfl) ⟨1100060, by rfl⟩ : syracuseStep 1466747 = 2200121) B2200121
theorem B1172735 : Blo 650305 1172735 := bstep (se 1 (by rfl) ⟨879551, by rfl⟩ : syracuseStep 1172735 = 1759103) B1759103
theorem B652031 : Blo 650305 652031 := bstep (se 1 (by rfl) ⟨489023, by rfl⟩ : syracuseStep 652031 = 978047) B978047
theorem B4169825 : Blo 650305 4169825 := bstep (se 2 (by rfl) ⟨1563684, by rfl⟩ : syracuseStep 4169825 = 3127369) B3127369
theorem B6696503 : Blo 650305 6696503 := bstep (se 1 (by rfl) ⟨5022377, by rfl⟩ : syracuseStep 6696503 = 10044755) B10044755
theorem B12242297 : Blo 650305 12242297 := bstep (se 2 (by rfl) ⟨4590861, by rfl⟩ : syracuseStep 12242297 = 9181723) B9181723
theorem B15453935 : Blo 650305 15453935 := bstep (se 1 (by rfl) ⟨11590451, by rfl⟩ : syracuseStep 15453935 = 23180903) B23180903
theorem B977831 : Blo 650305 977831 := bstep (se 1 (by rfl) ⟨733373, by rfl⟩ : syracuseStep 977831 = 1466747) B1466747
theorem B781823 : Blo 650305 781823 := bstep (se 1 (by rfl) ⟨586367, by rfl⟩ : syracuseStep 781823 = 1172735) B1172735
theorem B2978977 : Blo 650305 2978977 := bstep (se 2 (by rfl) ⟨1117116, by rfl⟩ : syracuseStep 2978977 = 2234233) B2234233
theorem B3971969 : Blo 650305 3971969 := bstep (se 2 (by rfl) ⟨1489488, by rfl⟩ : syracuseStep 3971969 = 2978977) B2978977
theorem B4464335 : Blo 650305 4464335 := bstep (se 1 (by rfl) ⟨3348251, by rfl⟩ : syracuseStep 4464335 = 6696503) B6696503
theorem B32646125 : Blo 650305 32646125 := bstep (se 3 (by rfl) ⟨6121148, by rfl⟩ : syracuseStep 32646125 = 12242297) B12242297
theorem B10302623 : Blo 650305 10302623 := bstep (se 1 (by rfl) ⟨7726967, by rfl⟩ : syracuseStep 10302623 = 15453935) B15453935
theorem B2084861 : Blo 650305 2084861 := bstep (se 3 (by rfl) ⟨390911, by rfl⟩ : syracuseStep 2084861 = 781823) B781823
theorem B2779883 : Blo 650305 2779883 := bstep (se 1 (by rfl) ⟨2084912, by rfl⟩ : syracuseStep 2779883 = 4169825) B4169825
theorem B651887 : Blo 650305 651887 := bstep (se 1 (by rfl) ⟨488915, by rfl⟩ : syracuseStep 651887 = 977831) B977831
theorem B1389907 : Blo 650305 1389907 := bstep (se 1 (by rfl) ⟨1042430, by rfl⟩ : syracuseStep 1389907 = 2084861) B2084861
theorem B1853255 : Blo 650305 1853255 := bstep (se 1 (by rfl) ⟨1389941, by rfl⟩ : syracuseStep 1853255 = 2779883) B2779883
theorem B6868415 : Blo 650305 6868415 := bstep (se 1 (by rfl) ⟨5151311, by rfl⟩ : syracuseStep 6868415 = 10302623) B10302623
theorem B87056333 : Blo 650305 87056333 := bstep (se 3 (by rfl) ⟨16323062, by rfl⟩ : syracuseStep 87056333 = 32646125) B32646125
theorem B2647979 : Blo 650305 2647979 := bstep (se 1 (by rfl) ⟨1985984, by rfl⟩ : syracuseStep 2647979 = 3971969) B3971969
theorem B2976223 : Blo 650305 2976223 := bstep (se 1 (by rfl) ⟨2232167, by rfl⟩ : syracuseStep 2976223 = 4464335) B4464335
theorem B3968297 : Blo 650305 3968297 := bstep (se 2 (by rfl) ⟨1488111, by rfl⟩ : syracuseStep 3968297 = 2976223) B2976223
theorem B58037555 : Blo 650305 58037555 := bstep (se 1 (by rfl) ⟨43528166, by rfl⟩ : syracuseStep 58037555 = 87056333) B87056333
theorem B1853209 : Blo 650305 1853209 := bstep (se 2 (by rfl) ⟨694953, by rfl⟩ : syracuseStep 1853209 = 1389907) B1389907
theorem B1235503 : Blo 650305 1235503 := bstep (se 1 (by rfl) ⟨926627, by rfl⟩ : syracuseStep 1235503 = 1853255) B1853255
theorem B1765319 : Blo 650305 1765319 := bstep (se 1 (by rfl) ⟨1323989, by rfl⟩ : syracuseStep 1765319 = 2647979) B2647979
theorem B18315773 : Blo 650305 18315773 := bstep (se 3 (by rfl) ⟨3434207, by rfl⟩ : syracuseStep 18315773 = 6868415) B6868415
theorem B1647337 : Blo 650305 1647337 := bstep (se 2 (by rfl) ⟨617751, by rfl⟩ : syracuseStep 1647337 = 1235503) B1235503
theorem B2470945 : Blo 650305 2470945 := bstep (se 2 (by rfl) ⟨926604, by rfl⟩ : syracuseStep 2470945 = 1853209) B1853209
theorem B12210515 : Blo 650305 12210515 := bstep (se 1 (by rfl) ⟨9157886, by rfl⟩ : syracuseStep 12210515 = 18315773) B18315773
theorem B18830069 : Blo 650305 18830069 := bstep (se 5 (by rfl) ⟨882659, by rfl⟩ : syracuseStep 18830069 = 1765319) B1765319
theorem B2645531 : Blo 650305 2645531 := bstep (se 1 (by rfl) ⟨1984148, by rfl⟩ : syracuseStep 2645531 = 3968297) B3968297
theorem B38691703 : Blo 650305 38691703 := bstep (se 1 (by rfl) ⟨29018777, by rfl⟩ : syracuseStep 38691703 = 58037555) B58037555
theorem B2196449 : Blo 650305 2196449 := bstep (se 2 (by rfl) ⟨823668, by rfl⟩ : syracuseStep 2196449 = 1647337) B1647337
theorem B12553379 : Blo 650305 12553379 := bstep (se 1 (by rfl) ⟨9415034, by rfl⟩ : syracuseStep 12553379 = 18830069) B18830069
theorem B51588937 : Blo 650305 51588937 := bstep (se 2 (by rfl) ⟨19345851, by rfl⟩ : syracuseStep 51588937 = 38691703) B38691703
theorem B8140343 : Blo 650305 8140343 := bstep (se 1 (by rfl) ⟨6105257, by rfl⟩ : syracuseStep 8140343 = 12210515) B12210515
theorem B3294593 : Blo 650305 3294593 := bstep (se 2 (by rfl) ⟨1235472, by rfl⟩ : syracuseStep 3294593 = 2470945) B2470945
theorem B1763687 : Blo 650305 1763687 := bstep (se 1 (by rfl) ⟨1322765, by rfl⟩ : syracuseStep 1763687 = 2645531) B2645531
theorem B2196395 : Blo 650305 2196395 := bstep (se 1 (by rfl) ⟨1647296, by rfl⟩ : syracuseStep 2196395 = 3294593) B3294593
theorem B68785249 : Blo 650305 68785249 := bstep (se 2 (by rfl) ⟨25794468, by rfl⟩ : syracuseStep 68785249 = 51588937) B51588937
theorem B8368919 : Blo 650305 8368919 := bstep (se 1 (by rfl) ⟨6276689, by rfl⟩ : syracuseStep 8368919 = 12553379) B12553379
theorem B1464299 : Blo 650305 1464299 := bstep (se 1 (by rfl) ⟨1098224, by rfl⟩ : syracuseStep 1464299 = 2196449) B2196449
theorem B86830325 : Blo 650305 86830325 := bstep (se 5 (by rfl) ⟨4070171, by rfl⟩ : syracuseStep 86830325 = 8140343) B8140343
theorem B1175791 : Blo 650305 1175791 := bstep (se 1 (by rfl) ⟨881843, by rfl⟩ : syracuseStep 1175791 = 1763687) B1763687
theorem B5579279 : Blo 650305 5579279 := bstep (se 1 (by rfl) ⟨4184459, by rfl⟩ : syracuseStep 5579279 = 8368919) B8368919
theorem B57886883 : Blo 650305 57886883 := bstep (se 1 (by rfl) ⟨43415162, by rfl⟩ : syracuseStep 57886883 = 86830325) B86830325
theorem B1464263 : Blo 650305 1464263 := bstep (se 1 (by rfl) ⟨1098197, by rfl⟩ : syracuseStep 1464263 = 2196395) B2196395
theorem B976199 : Blo 650305 976199 := bstep (se 1 (by rfl) ⟨732149, by rfl⟩ : syracuseStep 976199 = 1464299) B1464299
theorem B1567721 : Blo 650305 1567721 := bstep (se 2 (by rfl) ⟨587895, by rfl⟩ : syracuseStep 1567721 = 1175791) B1175791
theorem B91713665 : Blo 650305 91713665 := bstep (se 2 (by rfl) ⟨34392624, by rfl⟩ : syracuseStep 91713665 = 68785249) B68785249
theorem B3719519 : Blo 650305 3719519 := bstep (se 1 (by rfl) ⟨2789639, by rfl⟩ : syracuseStep 3719519 = 5579279) B5579279
theorem B244569773 : Blo 650305 244569773 := bstep (se 3 (by rfl) ⟨45856832, by rfl⟩ : syracuseStep 244569773 = 91713665) B91713665
theorem B38591255 : Blo 650305 38591255 := bstep (se 1 (by rfl) ⟨28943441, by rfl⟩ : syracuseStep 38591255 = 57886883) B57886883
theorem B976175 : Blo 650305 976175 := bstep (se 1 (by rfl) ⟨732131, by rfl⟩ : syracuseStep 976175 = 1464263) B1464263
theorem B650799 : Blo 650305 650799 := bstep (se 1 (by rfl) ⟨488099, by rfl⟩ : syracuseStep 650799 = 976199) B976199
theorem B1045147 : Blo 650305 1045147 := bstep (se 1 (by rfl) ⟨783860, by rfl⟩ : syracuseStep 1045147 = 1567721) B1567721
theorem B25727503 : Blo 650305 25727503 := bstep (se 1 (by rfl) ⟨19295627, by rfl⟩ : syracuseStep 25727503 = 38591255) B38591255
theorem B1393529 : Blo 650305 1393529 := bstep (se 2 (by rfl) ⟨522573, by rfl⟩ : syracuseStep 1393529 = 1045147) B1045147
theorem B2479679 : Blo 650305 2479679 := bstep (se 1 (by rfl) ⟨1859759, by rfl⟩ : syracuseStep 2479679 = 3719519) B3719519
theorem B163046515 : Blo 650305 163046515 := bstep (se 1 (by rfl) ⟨122284886, by rfl⟩ : syracuseStep 163046515 = 244569773) B244569773
theorem B650783 : Blo 650305 650783 := bstep (se 1 (by rfl) ⟨488087, by rfl⟩ : syracuseStep 650783 = 976175) B976175
theorem B217395353 : Blo 650305 217395353 := bstep (se 2 (by rfl) ⟨81523257, by rfl⟩ : syracuseStep 217395353 = 163046515) B163046515
theorem B3716077 : Blo 650305 3716077 := bstep (se 3 (by rfl) ⟨696764, by rfl⟩ : syracuseStep 3716077 = 1393529) B1393529
theorem B1653119 : Blo 650305 1653119 := bstep (se 1 (by rfl) ⟨1239839, by rfl⟩ : syracuseStep 1653119 = 2479679) B2479679
theorem B34303337 : Blo 650305 34303337 := bstep (se 2 (by rfl) ⟨12863751, by rfl⟩ : syracuseStep 34303337 = 25727503) B25727503
theorem B4954769 : Blo 650305 4954769 := bstep (se 2 (by rfl) ⟨1858038, by rfl⟩ : syracuseStep 4954769 = 3716077) B3716077
theorem B1102079 : Blo 650305 1102079 := bstep (se 1 (by rfl) ⟨826559, by rfl⟩ : syracuseStep 1102079 = 1653119) B1653119
theorem B22868891 : Blo 650305 22868891 := bstep (se 1 (by rfl) ⟨17151668, by rfl⟩ : syracuseStep 22868891 = 34303337) B34303337
theorem B144930235 : Blo 650305 144930235 := bstep (se 1 (by rfl) ⟨108697676, by rfl⟩ : syracuseStep 144930235 = 217395353) B217395353
theorem B193240313 : Blo 650305 193240313 := bstep (se 2 (by rfl) ⟨72465117, by rfl⟩ : syracuseStep 193240313 = 144930235) B144930235
theorem B15245927 : Blo 650305 15245927 := bstep (se 1 (by rfl) ⟨11434445, by rfl⟩ : syracuseStep 15245927 = 22868891) B22868891
theorem B734719 : Blo 650305 734719 := bstep (se 1 (by rfl) ⟨551039, by rfl⟩ : syracuseStep 734719 = 1102079) B1102079
theorem B3303179 : Blo 650305 3303179 := bstep (se 1 (by rfl) ⟨2477384, by rfl⟩ : syracuseStep 3303179 = 4954769) B4954769
theorem B10163951 : Blo 650305 10163951 := bstep (se 1 (by rfl) ⟨7622963, by rfl⟩ : syracuseStep 10163951 = 15245927) B15245927
theorem B2202119 : Blo 650305 2202119 := bstep (se 1 (by rfl) ⟨1651589, by rfl⟩ : syracuseStep 2202119 = 3303179) B3303179
theorem B128826875 : Blo 650305 128826875 := bstep (se 1 (by rfl) ⟨96620156, by rfl⟩ : syracuseStep 128826875 = 193240313) B193240313
theorem B979625 : Blo 650305 979625 := bstep (se 2 (by rfl) ⟨367359, by rfl⟩ : syracuseStep 979625 = 734719) B734719
theorem B6775967 : Blo 650305 6775967 := bstep (se 1 (by rfl) ⟨5081975, by rfl⟩ : syracuseStep 6775967 = 10163951) B10163951
theorem B1468079 : Blo 650305 1468079 := bstep (se 1 (by rfl) ⟨1101059, by rfl⟩ : syracuseStep 1468079 = 2202119) B2202119
theorem B653083 : Blo 650305 653083 := bstep (se 1 (by rfl) ⟨489812, by rfl⟩ : syracuseStep 653083 = 979625) B979625
theorem B85884583 : Blo 650305 85884583 := bstep (se 1 (by rfl) ⟨64413437, by rfl⟩ : syracuseStep 85884583 = 128826875) B128826875
theorem B18069245 : Blo 650305 18069245 := bstep (se 3 (by rfl) ⟨3387983, by rfl⟩ : syracuseStep 18069245 = 6775967) B6775967
theorem B114512777 : Blo 650305 114512777 := bstep (se 2 (by rfl) ⟨42942291, by rfl⟩ : syracuseStep 114512777 = 85884583) B85884583
theorem B978719 : Blo 650305 978719 := bstep (se 1 (by rfl) ⟨734039, by rfl⟩ : syracuseStep 978719 = 1468079) B1468079
theorem B12046163 : Blo 650305 12046163 := bstep (se 1 (by rfl) ⟨9034622, by rfl⟩ : syracuseStep 12046163 = 18069245) B18069245
theorem B76341851 : Blo 650305 76341851 := bstep (se 1 (by rfl) ⟨57256388, by rfl⟩ : syracuseStep 76341851 = 114512777) B114512777
theorem B652479 : Blo 650305 652479 := bstep (se 1 (by rfl) ⟨489359, by rfl⟩ : syracuseStep 652479 = 978719) B978719
theorem B50894567 : Blo 650305 50894567 := bstep (se 1 (by rfl) ⟨38170925, by rfl⟩ : syracuseStep 50894567 = 76341851) B76341851
theorem B32123101 : Blo 650305 32123101 := bstep (se 3 (by rfl) ⟨6023081, by rfl⟩ : syracuseStep 32123101 = 12046163) B12046163
theorem B42830801 : Blo 650305 42830801 := bstep (se 2 (by rfl) ⟨16061550, by rfl⟩ : syracuseStep 42830801 = 32123101) B32123101
theorem B33929711 : Blo 650305 33929711 := bstep (se 1 (by rfl) ⟨25447283, by rfl⟩ : syracuseStep 33929711 = 50894567) B50894567
theorem B22619807 : Blo 650305 22619807 := bstep (se 1 (by rfl) ⟨16964855, by rfl⟩ : syracuseStep 22619807 = 33929711) B33929711
theorem B28553867 : Blo 650305 28553867 := bstep (se 1 (by rfl) ⟨21415400, by rfl⟩ : syracuseStep 28553867 = 42830801) B42830801
theorem B15079871 : Blo 650305 15079871 := bstep (se 1 (by rfl) ⟨11309903, by rfl⟩ : syracuseStep 15079871 = 22619807) B22619807
theorem B19035911 : Blo 650305 19035911 := bstep (se 1 (by rfl) ⟨14276933, by rfl⟩ : syracuseStep 19035911 = 28553867) B28553867
theorem B12690607 : Blo 650305 12690607 := bstep (se 1 (by rfl) ⟨9517955, by rfl⟩ : syracuseStep 12690607 = 19035911) B19035911
theorem B10053247 : Blo 650305 10053247 := bstep (se 1 (by rfl) ⟨7539935, by rfl⟩ : syracuseStep 10053247 = 15079871) B15079871
theorem B13404329 : Blo 650305 13404329 := bstep (se 2 (by rfl) ⟨5026623, by rfl⟩ : syracuseStep 13404329 = 10053247) B10053247
theorem B16920809 : Blo 650305 16920809 := bstep (se 2 (by rfl) ⟨6345303, by rfl⟩ : syracuseStep 16920809 = 12690607) B12690607
theorem B11280539 : Blo 650305 11280539 := bstep (se 1 (by rfl) ⟨8460404, by rfl⟩ : syracuseStep 11280539 = 16920809) B16920809
theorem B8936219 : Blo 650305 8936219 := bstep (se 1 (by rfl) ⟨6702164, by rfl⟩ : syracuseStep 8936219 = 13404329) B13404329
theorem B7520359 : Blo 650305 7520359 := bstep (se 1 (by rfl) ⟨5640269, by rfl⟩ : syracuseStep 7520359 = 11280539) B11280539
theorem B5957479 : Blo 650305 5957479 := bstep (se 1 (by rfl) ⟨4468109, by rfl⟩ : syracuseStep 5957479 = 8936219) B8936219
theorem B10027145 : Blo 650305 10027145 := bstep (se 2 (by rfl) ⟨3760179, by rfl⟩ : syracuseStep 10027145 = 7520359) B7520359
theorem B7943305 : Blo 650305 7943305 := bstep (se 2 (by rfl) ⟨2978739, by rfl⟩ : syracuseStep 7943305 = 5957479) B5957479
theorem B6684763 : Blo 650305 6684763 := bstep (se 1 (by rfl) ⟨5013572, by rfl⟩ : syracuseStep 6684763 = 10027145) B10027145
theorem B10591073 : Blo 650305 10591073 := bstep (se 2 (by rfl) ⟨3971652, by rfl⟩ : syracuseStep 10591073 = 7943305) B7943305
theorem B8913017 : Blo 650305 8913017 := bstep (se 2 (by rfl) ⟨3342381, by rfl⟩ : syracuseStep 8913017 = 6684763) B6684763
theorem B7060715 : Blo 650305 7060715 := bstep (se 1 (by rfl) ⟨5295536, by rfl⟩ : syracuseStep 7060715 = 10591073) B10591073
theorem B5942011 : Blo 650305 5942011 := bstep (se 1 (by rfl) ⟨4456508, by rfl⟩ : syracuseStep 5942011 = 8913017) B8913017
theorem B4707143 : Blo 650305 4707143 := bstep (se 1 (by rfl) ⟨3530357, by rfl⟩ : syracuseStep 4707143 = 7060715) B7060715
theorem B3138095 : Blo 650305 3138095 := bstep (se 1 (by rfl) ⟨2353571, by rfl⟩ : syracuseStep 3138095 = 4707143) B4707143
theorem B7922681 : Blo 650305 7922681 := bstep (se 2 (by rfl) ⟨2971005, by rfl⟩ : syracuseStep 7922681 = 5942011) B5942011
theorem B5281787 : Blo 650305 5281787 := bstep (se 1 (by rfl) ⟨3961340, by rfl⟩ : syracuseStep 5281787 = 7922681) B7922681
theorem B2092063 : Blo 650305 2092063 := bstep (se 1 (by rfl) ⟨1569047, by rfl⟩ : syracuseStep 2092063 = 3138095) B3138095
theorem B2789417 : Blo 650305 2789417 := bstep (se 2 (by rfl) ⟨1046031, by rfl⟩ : syracuseStep 2789417 = 2092063) B2092063
theorem B3521191 : Blo 650305 3521191 := bstep (se 1 (by rfl) ⟨2640893, by rfl⟩ : syracuseStep 3521191 = 5281787) B5281787
theorem B4694921 : Blo 650305 4694921 := bstep (se 2 (by rfl) ⟨1760595, by rfl⟩ : syracuseStep 4694921 = 3521191) B3521191
theorem B1859611 : Blo 650305 1859611 := bstep (se 1 (by rfl) ⟨1394708, by rfl⟩ : syracuseStep 1859611 = 2789417) B2789417
theorem B3129947 : Blo 650305 3129947 := bstep (se 1 (by rfl) ⟨2347460, by rfl⟩ : syracuseStep 3129947 = 4694921) B4694921
theorem B2479481 : Blo 650305 2479481 := bstep (se 2 (by rfl) ⟨929805, by rfl⟩ : syracuseStep 2479481 = 1859611) B1859611
theorem B1652987 : Blo 650305 1652987 := bstep (se 1 (by rfl) ⟨1239740, by rfl⟩ : syracuseStep 1652987 = 2479481) B2479481
theorem B2086631 : Blo 650305 2086631 := bstep (se 1 (by rfl) ⟨1564973, by rfl⟩ : syracuseStep 2086631 = 3129947) B3129947
theorem B1391087 : Blo 650305 1391087 := bstep (se 1 (by rfl) ⟨1043315, by rfl⟩ : syracuseStep 1391087 = 2086631) B2086631
theorem B1101991 : Blo 650305 1101991 := bstep (se 1 (by rfl) ⟨826493, by rfl⟩ : syracuseStep 1101991 = 1652987) B1652987
theorem B927391 : Blo 650305 927391 := bstep (se 1 (by rfl) ⟨695543, by rfl⟩ : syracuseStep 927391 = 1391087) B1391087
theorem B1469321 : Blo 650305 1469321 := bstep (se 2 (by rfl) ⟨550995, by rfl⟩ : syracuseStep 1469321 = 1101991) B1101991
theorem B1236521 : Blo 650305 1236521 := bstep (se 2 (by rfl) ⟨463695, by rfl⟩ : syracuseStep 1236521 = 927391) B927391
theorem B979547 : Blo 650305 979547 := bstep (se 1 (by rfl) ⟨734660, by rfl⟩ : syracuseStep 979547 = 1469321) B1469321
theorem B824347 : Blo 650305 824347 := bstep (se 1 (by rfl) ⟨618260, by rfl⟩ : syracuseStep 824347 = 1236521) B1236521
theorem B653031 : Blo 650305 653031 := bstep (se 1 (by rfl) ⟨489773, by rfl⟩ : syracuseStep 653031 = 979547) B979547
theorem B1099129 : Blo 650305 1099129 := bstep (se 2 (by rfl) ⟨412173, by rfl⟩ : syracuseStep 1099129 = 824347) B824347
theorem B1465505 : Blo 650305 1465505 := bstep (se 2 (by rfl) ⟨549564, by rfl⟩ : syracuseStep 1465505 = 1099129) B1099129
theorem B977003 : Blo 650305 977003 := bstep (se 1 (by rfl) ⟨732752, by rfl⟩ : syracuseStep 977003 = 1465505) B1465505
theorem B651335 : Blo 650305 651335 := bstep (se 1 (by rfl) ⟨488501, by rfl⟩ : syracuseStep 651335 = 977003) B977003

theorem C0 (j : ℕ) (h1 : 162576 ≤ j) (h2 : j ≤ 163275) : Blo 650305 (4 * j + 3) := by
  interval_cases j
  · exact B650307
  · exact B650311
  · exact B650315
  · exact B650319
  · exact B650323
  · exact B650327
  · exact B650331
  · exact B650335
  · exact B650339
  · exact B650343
  · exact B650347
  · exact B650351
  · exact B650355
  · exact B650359
  · exact B650363
  · exact B650367
  · exact B650371
  · exact B650375
  · exact B650379
  · exact B650383
  · exact B650387
  · exact B650391
  · exact B650395
  · exact B650399
  · exact B650403
  · exact B650407
  · exact B650411
  · exact B650415
  · exact B650419
  · exact B650423
  · exact B650427
  · exact B650431
  · exact B650435
  · exact B650439
  · exact B650443
  · exact B650447
  · exact B650451
  · exact B650455
  · exact B650459
  · exact B650463
  · exact B650467
  · exact B650471
  · exact B650475
  · exact B650479
  · exact B650483
  · exact B650487
  · exact B650491
  · exact B650495
  · exact B650499
  · exact B650503
  · exact B650507
  · exact B650511
  · exact B650515
  · exact B650519
  · exact B650523
  · exact B650527
  · exact B650531
  · exact B650535
  · exact B650539
  · exact B650543
  · exact B650547
  · exact B650551
  · exact B650555
  · exact B650559
  · exact B650563
  · exact B650567
  · exact B650571
  · exact B650575
  · exact B650579
  · exact B650583
  · exact B650587
  · exact B650591
  · exact B650595
  · exact B650599
  · exact B650603
  · exact B650607
  · exact B650611
  · exact B650615
  · exact B650619
  · exact B650623
  · exact B650627
  · exact B650631
  · exact B650635
  · exact B650639
  · exact B650643
  · exact B650647
  · exact B650651
  · exact B650655
  · exact B650659
  · exact B650663
  · exact B650667
  · exact B650671
  · exact B650675
  · exact B650679
  · exact B650683
  · exact B650687
  · exact B650691
  · exact B650695
  · exact B650699
  · exact B650703
  · exact B650707
  · exact B650711
  · exact B650715
  · exact B650719
  · exact B650723
  · exact B650727
  · exact B650731
  · exact B650735
  · exact B650739
  · exact B650743
  · exact B650747
  · exact B650751
  · exact B650755
  · exact B650759
  · exact B650763
  · exact B650767
  · exact B650771
  · exact B650775
  · exact B650779
  · exact B650783
  · exact B650787
  · exact B650791
  · exact B650795
  · exact B650799
  · exact B650803
  · exact B650807
  · exact B650811
  · exact B650815
  · exact B650819
  · exact B650823
  · exact B650827
  · exact B650831
  · exact B650835
  · exact B650839
  · exact B650843
  · exact B650847
  · exact B650851
  · exact B650855
  · exact B650859
  · exact B650863
  · exact B650867
  · exact B650871
  · exact B650875
  · exact B650879
  · exact B650883
  · exact B650887
  · exact B650891
  · exact B650895
  · exact B650899
  · exact B650903
  · exact B650907
  · exact B650911
  · exact B650915
  · exact B650919
  · exact B650923
  · exact B650927
  · exact B650931
  · exact B650935
  · exact B650939
  · exact B650943
  · exact B650947
  · exact B650951
  · exact B650955
  · exact B650959
  · exact B650963
  · exact B650967
  · exact B650971
  · exact B650975
  · exact B650979
  · exact B650983
  · exact B650987
  · exact B650991
  · exact B650995
  · exact B650999
  · exact B651003
  · exact B651007
  · exact B651011
  · exact B651015
  · exact B651019
  · exact B651023
  · exact B651027
  · exact B651031
  · exact B651035
  · exact B651039
  · exact B651043
  · exact B651047
  · exact B651051
  · exact B651055
  · exact B651059
  · exact B651063
  · exact B651067
  · exact B651071
  · exact B651075
  · exact B651079
  · exact B651083
  · exact B651087
  · exact B651091
  · exact B651095
  · exact B651099
  · exact B651103
  · exact B651107
  · exact B651111
  · exact B651115
  · exact B651119
  · exact B651123
  · exact B651127
  · exact B651131
  · exact B651135
  · exact B651139
  · exact B651143
  · exact B651147
  · exact B651151
  · exact B651155
  · exact B651159
  · exact B651163
  · exact B651167
  · exact B651171
  · exact B651175
  · exact B651179
  · exact B651183
  · exact B651187
  · exact B651191
  · exact B651195
  · exact B651199
  · exact B651203
  · exact B651207
  · exact B651211
  · exact B651215
  · exact B651219
  · exact B651223
  · exact B651227
  · exact B651231
  · exact B651235
  · exact B651239
  · exact B651243
  · exact B651247
  · exact B651251
  · exact B651255
  · exact B651259
  · exact B651263
  · exact B651267
  · exact B651271
  · exact B651275
  · exact B651279
  · exact B651283
  · exact B651287
  · exact B651291
  · exact B651295
  · exact B651299
  · exact B651303
  · exact B651307
  · exact B651311
  · exact B651315
  · exact B651319
  · exact B651323
  · exact B651327
  · exact B651331
  · exact B651335
  · exact B651339
  · exact B651343
  · exact B651347
  · exact B651351
  · exact B651355
  · exact B651359
  · exact B651363
  · exact B651367
  · exact B651371
  · exact B651375
  · exact B651379
  · exact B651383
  · exact B651387
  · exact B651391
  · exact B651395
  · exact B651399
  · exact B651403
  · exact B651407
  · exact B651411
  · exact B651415
  · exact B651419
  · exact B651423
  · exact B651427
  · exact B651431
  · exact B651435
  · exact B651439
  · exact B651443
  · exact B651447
  · exact B651451
  · exact B651455
  · exact B651459
  · exact B651463
  · exact B651467
  · exact B651471
  · exact B651475
  · exact B651479
  · exact B651483
  · exact B651487
  · exact B651491
  · exact B651495
  · exact B651499
  · exact B651503
  · exact B651507
  · exact B651511
  · exact B651515
  · exact B651519
  · exact B651523
  · exact B651527
  · exact B651531
  · exact B651535
  · exact B651539
  · exact B651543
  · exact B651547
  · exact B651551
  · exact B651555
  · exact B651559
  · exact B651563
  · exact B651567
  · exact B651571
  · exact B651575
  · exact B651579
  · exact B651583
  · exact B651587
  · exact B651591
  · exact B651595
  · exact B651599
  · exact B651603
  · exact B651607
  · exact B651611
  · exact B651615
  · exact B651619
  · exact B651623
  · exact B651627
  · exact B651631
  · exact B651635
  · exact B651639
  · exact B651643
  · exact B651647
  · exact B651651
  · exact B651655
  · exact B651659
  · exact B651663
  · exact B651667
  · exact B651671
  · exact B651675
  · exact B651679
  · exact B651683
  · exact B651687
  · exact B651691
  · exact B651695
  · exact B651699
  · exact B651703
  · exact B651707
  · exact B651711
  · exact B651715
  · exact B651719
  · exact B651723
  · exact B651727
  · exact B651731
  · exact B651735
  · exact B651739
  · exact B651743
  · exact B651747
  · exact B651751
  · exact B651755
  · exact B651759
  · exact B651763
  · exact B651767
  · exact B651771
  · exact B651775
  · exact B651779
  · exact B651783
  · exact B651787
  · exact B651791
  · exact B651795
  · exact B651799
  · exact B651803
  · exact B651807
  · exact B651811
  · exact B651815
  · exact B651819
  · exact B651823
  · exact B651827
  · exact B651831
  · exact B651835
  · exact B651839
  · exact B651843
  · exact B651847
  · exact B651851
  · exact B651855
  · exact B651859
  · exact B651863
  · exact B651867
  · exact B651871
  · exact B651875
  · exact B651879
  · exact B651883
  · exact B651887
  · exact B651891
  · exact B651895
  · exact B651899
  · exact B651903
  · exact B651907
  · exact B651911
  · exact B651915
  · exact B651919
  · exact B651923
  · exact B651927
  · exact B651931
  · exact B651935
  · exact B651939
  · exact B651943
  · exact B651947
  · exact B651951
  · exact B651955
  · exact B651959
  · exact B651963
  · exact B651967
  · exact B651971
  · exact B651975
  · exact B651979
  · exact B651983
  · exact B651987
  · exact B651991
  · exact B651995
  · exact B651999
  · exact B652003
  · exact B652007
  · exact B652011
  · exact B652015
  · exact B652019
  · exact B652023
  · exact B652027
  · exact B652031
  · exact B652035
  · exact B652039
  · exact B652043
  · exact B652047
  · exact B652051
  · exact B652055
  · exact B652059
  · exact B652063
  · exact B652067
  · exact B652071
  · exact B652075
  · exact B652079
  · exact B652083
  · exact B652087
  · exact B652091
  · exact B652095
  · exact B652099
  · exact B652103
  · exact B652107
  · exact B652111
  · exact B652115
  · exact B652119
  · exact B652123
  · exact B652127
  · exact B652131
  · exact B652135
  · exact B652139
  · exact B652143
  · exact B652147
  · exact B652151
  · exact B652155
  · exact B652159
  · exact B652163
  · exact B652167
  · exact B652171
  · exact B652175
  · exact B652179
  · exact B652183
  · exact B652187
  · exact B652191
  · exact B652195
  · exact B652199
  · exact B652203
  · exact B652207
  · exact B652211
  · exact B652215
  · exact B652219
  · exact B652223
  · exact B652227
  · exact B652231
  · exact B652235
  · exact B652239
  · exact B652243
  · exact B652247
  · exact B652251
  · exact B652255
  · exact B652259
  · exact B652263
  · exact B652267
  · exact B652271
  · exact B652275
  · exact B652279
  · exact B652283
  · exact B652287
  · exact B652291
  · exact B652295
  · exact B652299
  · exact B652303
  · exact B652307
  · exact B652311
  · exact B652315
  · exact B652319
  · exact B652323
  · exact B652327
  · exact B652331
  · exact B652335
  · exact B652339
  · exact B652343
  · exact B652347
  · exact B652351
  · exact B652355
  · exact B652359
  · exact B652363
  · exact B652367
  · exact B652371
  · exact B652375
  · exact B652379
  · exact B652383
  · exact B652387
  · exact B652391
  · exact B652395
  · exact B652399
  · exact B652403
  · exact B652407
  · exact B652411
  · exact B652415
  · exact B652419
  · exact B652423
  · exact B652427
  · exact B652431
  · exact B652435
  · exact B652439
  · exact B652443
  · exact B652447
  · exact B652451
  · exact B652455
  · exact B652459
  · exact B652463
  · exact B652467
  · exact B652471
  · exact B652475
  · exact B652479
  · exact B652483
  · exact B652487
  · exact B652491
  · exact B652495
  · exact B652499
  · exact B652503
  · exact B652507
  · exact B652511
  · exact B652515
  · exact B652519
  · exact B652523
  · exact B652527
  · exact B652531
  · exact B652535
  · exact B652539
  · exact B652543
  · exact B652547
  · exact B652551
  · exact B652555
  · exact B652559
  · exact B652563
  · exact B652567
  · exact B652571
  · exact B652575
  · exact B652579
  · exact B652583
  · exact B652587
  · exact B652591
  · exact B652595
  · exact B652599
  · exact B652603
  · exact B652607
  · exact B652611
  · exact B652615
  · exact B652619
  · exact B652623
  · exact B652627
  · exact B652631
  · exact B652635
  · exact B652639
  · exact B652643
  · exact B652647
  · exact B652651
  · exact B652655
  · exact B652659
  · exact B652663
  · exact B652667
  · exact B652671
  · exact B652675
  · exact B652679
  · exact B652683
  · exact B652687
  · exact B652691
  · exact B652695
  · exact B652699
  · exact B652703
  · exact B652707
  · exact B652711
  · exact B652715
  · exact B652719
  · exact B652723
  · exact B652727
  · exact B652731
  · exact B652735
  · exact B652739
  · exact B652743
  · exact B652747
  · exact B652751
  · exact B652755
  · exact B652759
  · exact B652763
  · exact B652767
  · exact B652771
  · exact B652775
  · exact B652779
  · exact B652783
  · exact B652787
  · exact B652791
  · exact B652795
  · exact B652799
  · exact B652803
  · exact B652807
  · exact B652811
  · exact B652815
  · exact B652819
  · exact B652823
  · exact B652827
  · exact B652831
  · exact B652835
  · exact B652839
  · exact B652843
  · exact B652847
  · exact B652851
  · exact B652855
  · exact B652859
  · exact B652863
  · exact B652867
  · exact B652871
  · exact B652875
  · exact B652879
  · exact B652883
  · exact B652887
  · exact B652891
  · exact B652895
  · exact B652899
  · exact B652903
  · exact B652907
  · exact B652911
  · exact B652915
  · exact B652919
  · exact B652923
  · exact B652927
  · exact B652931
  · exact B652935
  · exact B652939
  · exact B652943
  · exact B652947
  · exact B652951
  · exact B652955
  · exact B652959
  · exact B652963
  · exact B652967
  · exact B652971
  · exact B652975
  · exact B652979
  · exact B652983
  · exact B652987
  · exact B652991
  · exact B652995
  · exact B652999
  · exact B653003
  · exact B653007
  · exact B653011
  · exact B653015
  · exact B653019
  · exact B653023
  · exact B653027
  · exact B653031
  · exact B653035
  · exact B653039
  · exact B653043
  · exact B653047
  · exact B653051
  · exact B653055
  · exact B653059
  · exact B653063
  · exact B653067
  · exact B653071
  · exact B653075
  · exact B653079
  · exact B653083
  · exact B653087
  · exact B653091
  · exact B653095
  · exact B653099
  · exact B653103

theorem C1 (j : ℕ) (h1 : 163276 ≤ j) (h2 : j ≤ 163575) : Blo 650305 (4 * j + 3) := by
  interval_cases j
  · exact B653107
  · exact B653111
  · exact B653115
  · exact B653119
  · exact B653123
  · exact B653127
  · exact B653131
  · exact B653135
  · exact B653139
  · exact B653143
  · exact B653147
  · exact B653151
  · exact B653155
  · exact B653159
  · exact B653163
  · exact B653167
  · exact B653171
  · exact B653175
  · exact B653179
  · exact B653183
  · exact B653187
  · exact B653191
  · exact B653195
  · exact B653199
  · exact B653203
  · exact B653207
  · exact B653211
  · exact B653215
  · exact B653219
  · exact B653223
  · exact B653227
  · exact B653231
  · exact B653235
  · exact B653239
  · exact B653243
  · exact B653247
  · exact B653251
  · exact B653255
  · exact B653259
  · exact B653263
  · exact B653267
  · exact B653271
  · exact B653275
  · exact B653279
  · exact B653283
  · exact B653287
  · exact B653291
  · exact B653295
  · exact B653299
  · exact B653303
  · exact B653307
  · exact B653311
  · exact B653315
  · exact B653319
  · exact B653323
  · exact B653327
  · exact B653331
  · exact B653335
  · exact B653339
  · exact B653343
  · exact B653347
  · exact B653351
  · exact B653355
  · exact B653359
  · exact B653363
  · exact B653367
  · exact B653371
  · exact B653375
  · exact B653379
  · exact B653383
  · exact B653387
  · exact B653391
  · exact B653395
  · exact B653399
  · exact B653403
  · exact B653407
  · exact B653411
  · exact B653415
  · exact B653419
  · exact B653423
  · exact B653427
  · exact B653431
  · exact B653435
  · exact B653439
  · exact B653443
  · exact B653447
  · exact B653451
  · exact B653455
  · exact B653459
  · exact B653463
  · exact B653467
  · exact B653471
  · exact B653475
  · exact B653479
  · exact B653483
  · exact B653487
  · exact B653491
  · exact B653495
  · exact B653499
  · exact B653503
  · exact B653507
  · exact B653511
  · exact B653515
  · exact B653519
  · exact B653523
  · exact B653527
  · exact B653531
  · exact B653535
  · exact B653539
  · exact B653543
  · exact B653547
  · exact B653551
  · exact B653555
  · exact B653559
  · exact B653563
  · exact B653567
  · exact B653571
  · exact B653575
  · exact B653579
  · exact B653583
  · exact B653587
  · exact B653591
  · exact B653595
  · exact B653599
  · exact B653603
  · exact B653607
  · exact B653611
  · exact B653615
  · exact B653619
  · exact B653623
  · exact B653627
  · exact B653631
  · exact B653635
  · exact B653639
  · exact B653643
  · exact B653647
  · exact B653651
  · exact B653655
  · exact B653659
  · exact B653663
  · exact B653667
  · exact B653671
  · exact B653675
  · exact B653679
  · exact B653683
  · exact B653687
  · exact B653691
  · exact B653695
  · exact B653699
  · exact B653703
  · exact B653707
  · exact B653711
  · exact B653715
  · exact B653719
  · exact B653723
  · exact B653727
  · exact B653731
  · exact B653735
  · exact B653739
  · exact B653743
  · exact B653747
  · exact B653751
  · exact B653755
  · exact B653759
  · exact B653763
  · exact B653767
  · exact B653771
  · exact B653775
  · exact B653779
  · exact B653783
  · exact B653787
  · exact B653791
  · exact B653795
  · exact B653799
  · exact B653803
  · exact B653807
  · exact B653811
  · exact B653815
  · exact B653819
  · exact B653823
  · exact B653827
  · exact B653831
  · exact B653835
  · exact B653839
  · exact B653843
  · exact B653847
  · exact B653851
  · exact B653855
  · exact B653859
  · exact B653863
  · exact B653867
  · exact B653871
  · exact B653875
  · exact B653879
  · exact B653883
  · exact B653887
  · exact B653891
  · exact B653895
  · exact B653899
  · exact B653903
  · exact B653907
  · exact B653911
  · exact B653915
  · exact B653919
  · exact B653923
  · exact B653927
  · exact B653931
  · exact B653935
  · exact B653939
  · exact B653943
  · exact B653947
  · exact B653951
  · exact B653955
  · exact B653959
  · exact B653963
  · exact B653967
  · exact B653971
  · exact B653975
  · exact B653979
  · exact B653983
  · exact B653987
  · exact B653991
  · exact B653995
  · exact B653999
  · exact B654003
  · exact B654007
  · exact B654011
  · exact B654015
  · exact B654019
  · exact B654023
  · exact B654027
  · exact B654031
  · exact B654035
  · exact B654039
  · exact B654043
  · exact B654047
  · exact B654051
  · exact B654055
  · exact B654059
  · exact B654063
  · exact B654067
  · exact B654071
  · exact B654075
  · exact B654079
  · exact B654083
  · exact B654087
  · exact B654091
  · exact B654095
  · exact B654099
  · exact B654103
  · exact B654107
  · exact B654111
  · exact B654115
  · exact B654119
  · exact B654123
  · exact B654127
  · exact B654131
  · exact B654135
  · exact B654139
  · exact B654143
  · exact B654147
  · exact B654151
  · exact B654155
  · exact B654159
  · exact B654163
  · exact B654167
  · exact B654171
  · exact B654175
  · exact B654179
  · exact B654183
  · exact B654187
  · exact B654191
  · exact B654195
  · exact B654199
  · exact B654203
  · exact B654207
  · exact B654211
  · exact B654215
  · exact B654219
  · exact B654223
  · exact B654227
  · exact B654231
  · exact B654235
  · exact B654239
  · exact B654243
  · exact B654247
  · exact B654251
  · exact B654255
  · exact B654259
  · exact B654263
  · exact B654267
  · exact B654271
  · exact B654275
  · exact B654279
  · exact B654283
  · exact B654287
  · exact B654291
  · exact B654295
  · exact B654299
  · exact B654303

theorem solution (m : ℕ) (hlo : 650305 ≤ m) (hhi : m ≤ 654305) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 162576 ≤ j := by omega
    have hj2 : j ≤ 163575 := by omega
    have hb : Blo 650305 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 163276 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
