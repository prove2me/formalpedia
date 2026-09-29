-- Prove2me | solution 1 for syracuse_descends_range_255820_259820
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T16:44:04.487449+00:00
-- url     : https://prove2.me/submissions/ff57a364-c512-4897-8058-362ff1d58360

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


theorem B1310741 : Blo 255820 1310741 := bbase (se 6 (by rfl) ⟨30720, by rfl⟩ : syracuseStep 1310741 = 61441) (by norm_num)
theorem B327721 : Blo 255820 327721 := bbase (se 2 (by rfl) ⟨122895, by rfl⟩ : syracuseStep 327721 = 245791) (by norm_num)
theorem B327817 : Blo 255820 327817 := bbase (se 2 (by rfl) ⟨122931, by rfl⟩ : syracuseStep 327817 = 245863) (by norm_num)
theorem B655573 : Blo 255820 655573 := bbase (se 7 (by rfl) ⟨7682, by rfl⟩ : syracuseStep 655573 = 15365) (by norm_num)
theorem B491741 : Blo 255820 491741 := bbase (se 3 (by rfl) ⟨92201, by rfl⟩ : syracuseStep 491741 = 184403) (by norm_num)
theorem B983285 : Blo 255820 983285 := bbase (se 5 (by rfl) ⟨46091, by rfl⟩ : syracuseStep 983285 = 92183) (by norm_num)
theorem B327989 : Blo 255820 327989 := bbase (se 5 (by rfl) ⟨15374, by rfl⟩ : syracuseStep 327989 = 30749) (by norm_num)
theorem B655685 : Blo 255820 655685 := bbase (se 4 (by rfl) ⟨61470, by rfl⟩ : syracuseStep 655685 = 122941) (by norm_num)
theorem B2359637 : Blo 255820 2359637 := bbase (se 10 (by rfl) ⟨3456, by rfl⟩ : syracuseStep 2359637 = 6913) (by norm_num)
theorem B328045 : Blo 255820 328045 := bbase (se 3 (by rfl) ⟨61508, by rfl⟩ : syracuseStep 328045 = 123017) (by norm_num)
theorem B328141 : Blo 255820 328141 := bbase (se 3 (by rfl) ⟨61526, by rfl⟩ : syracuseStep 328141 = 123053) (by norm_num)
theorem B655877 : Blo 255820 655877 := bbase (se 4 (by rfl) ⟨61488, by rfl⟩ : syracuseStep 655877 = 122977) (by norm_num)
theorem B983573 : Blo 255820 983573 := bbase (se 6 (by rfl) ⟨23052, by rfl⟩ : syracuseStep 983573 = 46105) (by norm_num)
theorem B262721 : Blo 255820 262721 := bbase (se 2 (by rfl) ⟨98520, by rfl⟩ : syracuseStep 262721 = 197041) (by norm_num)
theorem B262769 : Blo 255820 262769 := bbase (se 2 (by rfl) ⟨98538, by rfl⟩ : syracuseStep 262769 = 197077) (by norm_num)
theorem B328313 : Blo 255820 328313 := bbase (se 2 (by rfl) ⟨123117, by rfl⟩ : syracuseStep 328313 = 246235) (by norm_num)
theorem B819845 : Blo 255820 819845 := bbase (se 4 (by rfl) ⟨76860, by rfl⟩ : syracuseStep 819845 = 153721) (by norm_num)
theorem B328369 : Blo 255820 328369 := bbase (se 2 (by rfl) ⟨123138, by rfl⟩ : syracuseStep 328369 = 246277) (by norm_num)
theorem B328465 : Blo 255820 328465 := bbase (se 2 (by rfl) ⟨123174, by rfl⟩ : syracuseStep 328465 = 246349) (by norm_num)
theorem B394069 : Blo 255820 394069 := bbase (se 9 (by rfl) ⟨1154, by rfl⟩ : syracuseStep 394069 = 2309) (by norm_num)
theorem B656221 : Blo 255820 656221 := bbase (se 3 (by rfl) ⟨123041, by rfl⟩ : syracuseStep 656221 = 246083) (by norm_num)
theorem B328637 : Blo 255820 328637 := bbase (se 3 (by rfl) ⟨61619, by rfl⟩ : syracuseStep 328637 = 123239) (by norm_num)
theorem B656333 : Blo 255820 656333 := bbase (se 3 (by rfl) ⟨123062, by rfl⟩ : syracuseStep 656333 = 246125) (by norm_num)
theorem B492493 : Blo 255820 492493 := bbase (se 3 (by rfl) ⟨92342, by rfl⟩ : syracuseStep 492493 = 184685) (by norm_num)
theorem B328693 : Blo 255820 328693 := bbase (se 5 (by rfl) ⟨15407, by rfl⟩ : syracuseStep 328693 = 30815) (by norm_num)
theorem B623629 : Blo 255820 623629 := bbase (se 3 (by rfl) ⟨116930, by rfl⟩ : syracuseStep 623629 = 233861) (by norm_num)
theorem B328729 : Blo 255820 328729 := bbase (se 2 (by rfl) ⟨123273, by rfl⟩ : syracuseStep 328729 = 246547) (by norm_num)
theorem B328789 : Blo 255820 328789 := bbase (se 8 (by rfl) ⟨1926, by rfl⟩ : syracuseStep 328789 = 3853) (by norm_num)
theorem B492637 : Blo 255820 492637 := bbase (se 3 (by rfl) ⟨92369, by rfl⟩ : syracuseStep 492637 = 184739) (by norm_num)
theorem B656525 : Blo 255820 656525 := bbase (se 3 (by rfl) ⟨123098, by rfl⟩ : syracuseStep 656525 = 246197) (by norm_num)
theorem B591077 : Blo 255820 591077 := bbase (se 4 (by rfl) ⟨55413, by rfl⟩ : syracuseStep 591077 = 110827) (by norm_num)
theorem B492797 : Blo 255820 492797 := bbase (se 3 (by rfl) ⟨92399, by rfl⟩ : syracuseStep 492797 = 184799) (by norm_num)
theorem B1312037 : Blo 255820 1312037 := bbase (se 4 (by rfl) ⟨123003, by rfl⟩ : syracuseStep 1312037 = 246007) (by norm_num)
theorem B525685 : Blo 255820 525685 := bbase (se 5 (by rfl) ⟨24641, by rfl⟩ : syracuseStep 525685 = 49283) (by norm_num)
theorem B492941 : Blo 255820 492941 := bbase (se 3 (by rfl) ⟨92426, by rfl⟩ : syracuseStep 492941 = 184853) (by norm_num)
theorem B656869 : Blo 255820 656869 := bbase (se 4 (by rfl) ⟨61581, by rfl⟩ : syracuseStep 656869 = 123163) (by norm_num)
theorem B394733 : Blo 255820 394733 := bbase (se 3 (by rfl) ⟨74012, by rfl⟩ : syracuseStep 394733 = 148025) (by norm_num)
theorem B656981 : Blo 255820 656981 := bbase (se 8 (by rfl) ⟨3849, by rfl⟩ : syracuseStep 656981 = 7699) (by norm_num)
theorem B2360981 : Blo 255820 2360981 := bbase (se 6 (by rfl) ⟨55335, by rfl⟩ : syracuseStep 2360981 = 110671) (by norm_num)
theorem B493229 : Blo 255820 493229 := bbase (se 3 (by rfl) ⟨92480, by rfl⟩ : syracuseStep 493229 = 184961) (by norm_num)
theorem B984757 : Blo 255820 984757 := bbase (se 5 (by rfl) ⟨46160, by rfl⟩ : syracuseStep 984757 = 92321) (by norm_num)
theorem B329449 : Blo 255820 329449 := bbase (se 2 (by rfl) ⟨123543, by rfl⟩ : syracuseStep 329449 = 247087) (by norm_num)
theorem B493325 : Blo 255820 493325 := bbase (se 3 (by rfl) ⟨92498, by rfl⟩ : syracuseStep 493325 = 184997) (by norm_num)
theorem B657173 : Blo 255820 657173 := bbase (se 6 (by rfl) ⟨15402, by rfl⟩ : syracuseStep 657173 = 30805) (by norm_num)
theorem B985061 : Blo 255820 985061 := bbase (se 4 (by rfl) ⟨92349, by rfl⟩ : syracuseStep 985061 = 184699) (by norm_num)
theorem B657517 : Blo 255820 657517 := bbase (se 3 (by rfl) ⟨123284, by rfl⟩ : syracuseStep 657517 = 246569) (by norm_num)
theorem B329869 : Blo 255820 329869 := bbase (se 3 (by rfl) ⟨61850, by rfl⟩ : syracuseStep 329869 = 123701) (by norm_num)
theorem B1181861 : Blo 255820 1181861 := bbase (se 4 (by rfl) ⟨110799, by rfl⟩ : syracuseStep 1181861 = 221599) (by norm_num)
theorem B657629 : Blo 255820 657629 := bbase (se 3 (by rfl) ⟨123305, by rfl⟩ : syracuseStep 657629 = 246611) (by norm_num)
theorem B2787605 : Blo 255820 2787605 := bbase (se 6 (by rfl) ⟨65334, by rfl⟩ : syracuseStep 2787605 = 130669) (by norm_num)
theorem B1313333 : Blo 255820 1313333 := bbase (se 5 (by rfl) ⟨61562, by rfl⟩ : syracuseStep 1313333 = 123125) (by norm_num)
theorem B658037 : Blo 255820 658037 := bbase (se 5 (by rfl) ⟨30845, by rfl⟩ : syracuseStep 658037 = 61691) (by norm_num)
theorem B494437 : Blo 255820 494437 := bbase (se 4 (by rfl) ⟨46353, by rfl⟩ : syracuseStep 494437 = 92707) (by norm_num)
theorem B592861 : Blo 255820 592861 := bbase (se 3 (by rfl) ⟨111161, by rfl⟩ : syracuseStep 592861 = 222323) (by norm_num)
theorem B1182757 : Blo 255820 1182757 := bbase (se 4 (by rfl) ⟨110883, by rfl⟩ : syracuseStep 1182757 = 221767) (by norm_num)
theorem B691541 : Blo 255820 691541 := bbase (se 11 (by rfl) ⟨506, by rfl⟩ : syracuseStep 691541 = 1013) (by norm_num)
theorem B2100853 : Blo 255820 2100853 := bbase (se 5 (by rfl) ⟨98477, by rfl⟩ : syracuseStep 2100853 = 196955) (by norm_num)
theorem B659141 : Blo 255820 659141 := bbase (se 4 (by rfl) ⟨61794, by rfl⟩ : syracuseStep 659141 = 123589) (by norm_num)
theorem B691973 : Blo 255820 691973 := bbase (se 4 (by rfl) ⟨64872, by rfl⟩ : syracuseStep 691973 = 129745) (by norm_num)
theorem B1314629 : Blo 255820 1314629 := bbase (se 4 (by rfl) ⟨123246, by rfl⟩ : syracuseStep 1314629 = 246493) (by norm_num)
theorem B266437 : Blo 255820 266437 := bbase (se 4 (by rfl) ⟨24978, by rfl⟩ : syracuseStep 266437 = 49957) (by norm_num)
theorem B364933 : Blo 255820 364933 := bbase (se 4 (by rfl) ⟨34212, by rfl⟩ : syracuseStep 364933 = 68425) (by norm_num)
theorem B823765 : Blo 255820 823765 := bbase (se 7 (by rfl) ⟨9653, by rfl⟩ : syracuseStep 823765 = 19307) (by norm_num)
theorem B463333 : Blo 255820 463333 := bbase (se 4 (by rfl) ⟨43437, by rfl⟩ : syracuseStep 463333 = 86875) (by norm_num)
theorem B692869 : Blo 255820 692869 := bbase (se 4 (by rfl) ⟨64956, by rfl⟩ : syracuseStep 692869 = 129913) (by norm_num)
theorem B824021 : Blo 255820 824021 := bbase (se 7 (by rfl) ⟨9656, by rfl⟩ : syracuseStep 824021 = 19313) (by norm_num)
theorem B2495285 : Blo 255820 2495285 := bbase (se 5 (by rfl) ⟨116966, by rfl⟩ : syracuseStep 2495285 = 233933) (by norm_num)
theorem B529325 : Blo 255820 529325 := bbase (se 3 (by rfl) ⟨99248, by rfl⟩ : syracuseStep 529325 = 198497) (by norm_num)
theorem B332753 : Blo 255820 332753 := bbase (se 2 (by rfl) ⟨124782, by rfl⟩ : syracuseStep 332753 = 249565) (by norm_num)
theorem B463973 : Blo 255820 463973 := bbase (se 4 (by rfl) ⟨43497, by rfl⟩ : syracuseStep 463973 = 86995) (by norm_num)
theorem B365725 : Blo 255820 365725 := bbase (se 3 (by rfl) ⟨68573, by rfl⟩ : syracuseStep 365725 = 137147) (by norm_num)
theorem B988469 : Blo 255820 988469 := bbase (se 5 (by rfl) ⟨46334, by rfl⟩ : syracuseStep 988469 = 92669) (by norm_num)
theorem B660869 : Blo 255820 660869 := bbase (se 4 (by rfl) ⟨61956, by rfl⟩ : syracuseStep 660869 = 123913) (by norm_num)
theorem B366061 : Blo 255820 366061 := bbase (se 3 (by rfl) ⟨68636, by rfl⟩ : syracuseStep 366061 = 137273) (by norm_num)
theorem B1971701 : Blo 255820 1971701 := bbase (se 5 (by rfl) ⟨92423, by rfl⟩ : syracuseStep 1971701 = 184847) (by norm_num)
theorem B431797 : Blo 255820 431797 := bbase (se 5 (by rfl) ⟨20240, by rfl⟩ : syracuseStep 431797 = 40481) (by norm_num)
theorem B366277 : Blo 255820 366277 := bbase (se 4 (by rfl) ⟨34338, by rfl⟩ : syracuseStep 366277 = 68677) (by norm_num)
theorem B431885 : Blo 255820 431885 := bbase (se 3 (by rfl) ⟨80978, by rfl⟩ : syracuseStep 431885 = 161957) (by norm_num)
theorem B464717 : Blo 255820 464717 := bbase (se 3 (by rfl) ⟨87134, by rfl⟩ : syracuseStep 464717 = 174269) (by norm_num)
theorem B432013 : Blo 255820 432013 := bbase (se 3 (by rfl) ⟨81002, by rfl⟩ : syracuseStep 432013 = 162005) (by norm_num)
theorem B432101 : Blo 255820 432101 := bbase (se 4 (by rfl) ⟨40509, by rfl⟩ : syracuseStep 432101 = 81019) (by norm_num)
theorem B1644533 : Blo 255820 1644533 := bbase (se 5 (by rfl) ⟨77087, by rfl⟩ : syracuseStep 1644533 = 154175) (by norm_num)
theorem B366653 : Blo 255820 366653 := bbase (se 3 (by rfl) ⟨68747, by rfl⟩ : syracuseStep 366653 = 137495) (by norm_num)
theorem B432229 : Blo 255820 432229 := bbase (se 4 (by rfl) ⟨40521, by rfl⟩ : syracuseStep 432229 = 81043) (by norm_num)
theorem B432317 : Blo 255820 432317 := bbase (se 3 (by rfl) ⟨81059, by rfl⟩ : syracuseStep 432317 = 162119) (by norm_num)
theorem B432445 : Blo 255820 432445 := bbase (se 3 (by rfl) ⟨81083, by rfl⟩ : syracuseStep 432445 = 162167) (by norm_num)
theorem B432533 : Blo 255820 432533 := bbase (se 6 (by rfl) ⟨10137, by rfl⟩ : syracuseStep 432533 = 20275) (by norm_num)
theorem B432661 : Blo 255820 432661 := bbase (se 6 (by rfl) ⟨10140, by rfl⟩ : syracuseStep 432661 = 20281) (by norm_num)
theorem B432749 : Blo 255820 432749 := bbase (se 3 (by rfl) ⟨81140, by rfl⟩ : syracuseStep 432749 = 162281) (by norm_num)
theorem B432877 : Blo 255820 432877 := bbase (se 3 (by rfl) ⟨81164, by rfl⟩ : syracuseStep 432877 = 162329) (by norm_num)
theorem B432965 : Blo 255820 432965 := bbase (se 4 (by rfl) ⟨40590, by rfl⟩ : syracuseStep 432965 = 81181) (by norm_num)
theorem B1579925 : Blo 255820 1579925 := bbase (se 6 (by rfl) ⟨37029, by rfl⟩ : syracuseStep 1579925 = 74059) (by norm_num)
theorem B433093 : Blo 255820 433093 := bbase (se 4 (by rfl) ⟨40602, by rfl⟩ : syracuseStep 433093 = 81205) (by norm_num)
theorem B433181 : Blo 255820 433181 := bbase (se 3 (by rfl) ⟨81221, by rfl⟩ : syracuseStep 433181 = 162443) (by norm_num)
theorem B466021 : Blo 255820 466021 := bbase (se 4 (by rfl) ⟨43689, by rfl⟩ : syracuseStep 466021 = 87379) (by norm_num)
theorem B924821 : Blo 255820 924821 := bbase (se 6 (by rfl) ⟨21675, by rfl⟩ : syracuseStep 924821 = 43351) (by norm_num)
theorem B433309 : Blo 255820 433309 := bbase (se 3 (by rfl) ⟨81245, by rfl⟩ : syracuseStep 433309 = 162491) (by norm_num)
theorem B3316949 : Blo 255820 3316949 := bbase (se 7 (by rfl) ⟨38870, by rfl⟩ : syracuseStep 3316949 = 77741) (by norm_num)
theorem B433397 : Blo 255820 433397 := bbase (se 5 (by rfl) ⟨20315, by rfl⟩ : syracuseStep 433397 = 40631) (by norm_num)
theorem B695573 : Blo 255820 695573 := bbase (se 6 (by rfl) ⟨16302, by rfl⟩ : syracuseStep 695573 = 32605) (by norm_num)
theorem B433525 : Blo 255820 433525 := bbase (se 5 (by rfl) ⟨20321, by rfl⟩ : syracuseStep 433525 = 40643) (by norm_num)
theorem B826789 : Blo 255820 826789 := bbase (se 4 (by rfl) ⟨77511, by rfl⟩ : syracuseStep 826789 = 155023) (by norm_num)
theorem B433613 : Blo 255820 433613 := bbase (se 3 (by rfl) ⟨81302, by rfl⟩ : syracuseStep 433613 = 162605) (by norm_num)
theorem B368077 : Blo 255820 368077 := bbase (se 3 (by rfl) ⟨69014, by rfl⟩ : syracuseStep 368077 = 138029) (by norm_num)
theorem B1121861 : Blo 255820 1121861 := bbase (se 4 (by rfl) ⟨105174, by rfl⟩ : syracuseStep 1121861 = 210349) (by norm_num)
theorem B433741 : Blo 255820 433741 := bbase (se 3 (by rfl) ⟨81326, by rfl⟩ : syracuseStep 433741 = 162653) (by norm_num)
theorem B433829 : Blo 255820 433829 := bbase (se 4 (by rfl) ⟨40671, by rfl⟩ : syracuseStep 433829 = 81343) (by norm_num)
theorem B2989781 : Blo 255820 2989781 := bbase (se 7 (by rfl) ⟨35036, by rfl⟩ : syracuseStep 2989781 = 70073) (by norm_num)
theorem B433957 : Blo 255820 433957 := bbase (se 4 (by rfl) ⟨40683, by rfl⟩ : syracuseStep 433957 = 81367) (by norm_num)
theorem B466741 : Blo 255820 466741 := bbase (se 5 (by rfl) ⟨21878, by rfl⟩ : syracuseStep 466741 = 43757) (by norm_num)
theorem B434045 : Blo 255820 434045 := bbase (se 3 (by rfl) ⟨81383, by rfl⟩ : syracuseStep 434045 = 162767) (by norm_num)
theorem B2957269 : Blo 255820 2957269 := bbase (se 7 (by rfl) ⟨34655, by rfl⟩ : syracuseStep 2957269 = 69311) (by norm_num)
theorem B434173 : Blo 255820 434173 := bbase (se 3 (by rfl) ⟨81407, by rfl⟩ : syracuseStep 434173 = 162815) (by norm_num)
theorem B368669 : Blo 255820 368669 := bbase (se 3 (by rfl) ⟨69125, by rfl⟩ : syracuseStep 368669 = 138251) (by norm_num)
theorem B1450037 : Blo 255820 1450037 := bbase (se 5 (by rfl) ⟨67970, by rfl⟩ : syracuseStep 1450037 = 135941) (by norm_num)
theorem B434261 : Blo 255820 434261 := bbase (se 8 (by rfl) ⟨2544, by rfl⟩ : syracuseStep 434261 = 5089) (by norm_num)
theorem B368749 : Blo 255820 368749 := bbase (se 3 (by rfl) ⟨69140, by rfl⟩ : syracuseStep 368749 = 138281) (by norm_num)
theorem B434389 : Blo 255820 434389 := bbase (se 7 (by rfl) ⟨5090, by rfl⟩ : syracuseStep 434389 = 10181) (by norm_num)
theorem B2367701 : Blo 255820 2367701 := bbase (se 7 (by rfl) ⟨27746, by rfl⟩ : syracuseStep 2367701 = 55493) (by norm_num)
theorem B368869 : Blo 255820 368869 := bbase (se 4 (by rfl) ⟨34581, by rfl⟩ : syracuseStep 368869 = 69163) (by norm_num)
theorem B434477 : Blo 255820 434477 := bbase (se 3 (by rfl) ⟨81464, by rfl⟩ : syracuseStep 434477 = 162929) (by norm_num)
theorem B368965 : Blo 255820 368965 := bbase (se 4 (by rfl) ⟨34590, by rfl⟩ : syracuseStep 368965 = 69181) (by norm_num)
theorem B729445 : Blo 255820 729445 := bbase (se 4 (by rfl) ⟨68385, by rfl⟩ : syracuseStep 729445 = 136771) (by norm_num)
theorem B926101 : Blo 255820 926101 := bbase (se 6 (by rfl) ⟨21705, by rfl⟩ : syracuseStep 926101 = 43411) (by norm_num)
theorem B434605 : Blo 255820 434605 := bbase (se 3 (by rfl) ⟨81488, by rfl⟩ : syracuseStep 434605 = 162977) (by norm_num)
theorem B434693 : Blo 255820 434693 := bbase (se 4 (by rfl) ⟨40752, by rfl⟩ : syracuseStep 434693 = 81505) (by norm_num)
theorem B467549 : Blo 255820 467549 := bbase (se 3 (by rfl) ⟨87665, by rfl⟩ : syracuseStep 467549 = 175331) (by norm_num)
theorem B434821 : Blo 255820 434821 := bbase (se 4 (by rfl) ⟨40764, by rfl⟩ : syracuseStep 434821 = 81529) (by norm_num)
theorem B434909 : Blo 255820 434909 := bbase (se 3 (by rfl) ⟨81545, by rfl⟩ : syracuseStep 434909 = 163091) (by norm_num)
theorem B795413 : Blo 255820 795413 := bbase (se 6 (by rfl) ⟨18642, by rfl⟩ : syracuseStep 795413 = 37285) (by norm_num)
theorem B369461 : Blo 255820 369461 := bbase (se 5 (by rfl) ⟨17318, by rfl⟩ : syracuseStep 369461 = 34637) (by norm_num)
theorem B435037 : Blo 255820 435037 := bbase (se 3 (by rfl) ⟨81569, by rfl⟩ : syracuseStep 435037 = 163139) (by norm_num)
theorem B992101 : Blo 255820 992101 := bbase (se 4 (by rfl) ⟨93009, by rfl⟩ : syracuseStep 992101 = 186019) (by norm_num)
theorem B435125 : Blo 255820 435125 := bbase (se 5 (by rfl) ⟨20396, by rfl⟩ : syracuseStep 435125 = 40793) (by norm_num)
theorem B435253 : Blo 255820 435253 := bbase (se 5 (by rfl) ⟨20402, by rfl⟩ : syracuseStep 435253 = 40805) (by norm_num)
theorem B5022805 : Blo 255820 5022805 := bbase (se 8 (by rfl) ⟨29430, by rfl⟩ : syracuseStep 5022805 = 58861) (by norm_num)
theorem B435341 : Blo 255820 435341 := bbase (se 3 (by rfl) ⟨81626, by rfl⟩ : syracuseStep 435341 = 163253) (by norm_num)
theorem B435469 : Blo 255820 435469 := bbase (se 3 (by rfl) ⟨81650, by rfl⟩ : syracuseStep 435469 = 163301) (by norm_num)
theorem B435557 : Blo 255820 435557 := bbase (se 4 (by rfl) ⟨40833, by rfl⟩ : syracuseStep 435557 = 81667) (by norm_num)
theorem B730549 : Blo 255820 730549 := bbase (se 5 (by rfl) ⟨34244, by rfl⟩ : syracuseStep 730549 = 68489) (by norm_num)
theorem B4793813 : Blo 255820 4793813 := bbase (se 7 (by rfl) ⟨56177, by rfl⟩ : syracuseStep 4793813 = 112355) (by norm_num)
theorem B435685 : Blo 255820 435685 := bbase (se 4 (by rfl) ⟨40845, by rfl⟩ : syracuseStep 435685 = 81691) (by norm_num)
theorem B435773 : Blo 255820 435773 := bbase (se 3 (by rfl) ⟨81707, by rfl⟩ : syracuseStep 435773 = 163415) (by norm_num)
theorem B1320581 : Blo 255820 1320581 := bbase (se 4 (by rfl) ⟨123804, by rfl⟩ : syracuseStep 1320581 = 247609) (by norm_num)
theorem B435901 : Blo 255820 435901 := bbase (se 3 (by rfl) ⟨81731, by rfl⟩ : syracuseStep 435901 = 163463) (by norm_num)
theorem B435989 : Blo 255820 435989 := bbase (se 6 (by rfl) ⟨10218, by rfl⟩ : syracuseStep 435989 = 20437) (by norm_num)
theorem B2205589 : Blo 255820 2205589 := bbase (se 6 (by rfl) ⟨51693, by rfl⟩ : syracuseStep 2205589 = 103387) (by norm_num)
theorem B436117 : Blo 255820 436117 := bbase (se 6 (by rfl) ⟨10221, by rfl⟩ : syracuseStep 436117 = 20443) (by norm_num)
theorem B698341 : Blo 255820 698341 := bbase (se 4 (by rfl) ⟨65469, by rfl⟩ : syracuseStep 698341 = 130939) (by norm_num)
theorem B436205 : Blo 255820 436205 := bbase (se 3 (by rfl) ⟨81788, by rfl⟩ : syracuseStep 436205 = 163577) (by norm_num)
theorem B436333 : Blo 255820 436333 := bbase (se 3 (by rfl) ⟨81812, by rfl⟩ : syracuseStep 436333 = 163625) (by norm_num)
theorem B436421 : Blo 255820 436421 := bbase (se 4 (by rfl) ⟨40914, by rfl⟩ : syracuseStep 436421 = 81829) (by norm_num)
theorem B436549 : Blo 255820 436549 := bbase (se 4 (by rfl) ⟨40926, by rfl⟩ : syracuseStep 436549 = 81853) (by norm_num)
theorem B436637 : Blo 255820 436637 := bbase (se 3 (by rfl) ⟨81869, by rfl⟩ : syracuseStep 436637 = 163739) (by norm_num)
theorem B436765 : Blo 255820 436765 := bbase (se 3 (by rfl) ⟨81893, by rfl⟩ : syracuseStep 436765 = 163787) (by norm_num)
theorem B436853 : Blo 255820 436853 := bbase (se 5 (by rfl) ⟨20477, by rfl⟩ : syracuseStep 436853 = 40955) (by norm_num)
theorem B436981 : Blo 255820 436981 := bbase (se 5 (by rfl) ⟨20483, by rfl⟩ : syracuseStep 436981 = 40967) (by norm_num)
theorem B994069 : Blo 255820 994069 := bbase (se 6 (by rfl) ⟨23298, by rfl⟩ : syracuseStep 994069 = 46597) (by norm_num)
theorem B994117 : Blo 255820 994117 := bbase (se 4 (by rfl) ⟨93198, by rfl⟩ : syracuseStep 994117 = 186397) (by norm_num)
theorem B699205 : Blo 255820 699205 := bbase (se 4 (by rfl) ⟨65550, by rfl⟩ : syracuseStep 699205 = 131101) (by norm_num)
theorem B437069 : Blo 255820 437069 := bbase (se 3 (by rfl) ⟨81950, by rfl⟩ : syracuseStep 437069 = 163901) (by norm_num)
theorem B338837 : Blo 255820 338837 := bbase (se 6 (by rfl) ⟨7941, by rfl⟩ : syracuseStep 338837 = 15883) (by norm_num)
theorem B732053 : Blo 255820 732053 := bbase (se 6 (by rfl) ⟨17157, by rfl⟩ : syracuseStep 732053 = 34315) (by norm_num)
theorem B273341 : Blo 255820 273341 := bbase (se 3 (by rfl) ⟨51251, by rfl⟩ : syracuseStep 273341 = 102503) (by norm_num)
theorem B437197 : Blo 255820 437197 := bbase (se 3 (by rfl) ⟨81974, by rfl⟩ : syracuseStep 437197 = 163949) (by norm_num)
theorem B928741 : Blo 255820 928741 := bbase (se 4 (by rfl) ⟨87069, by rfl⟩ : syracuseStep 928741 = 174139) (by norm_num)
theorem B437285 : Blo 255820 437285 := bbase (se 4 (by rfl) ⟨40995, by rfl⟩ : syracuseStep 437285 = 81991) (by norm_num)
theorem B437413 : Blo 255820 437413 := bbase (se 4 (by rfl) ⟨41007, by rfl⟩ : syracuseStep 437413 = 82015) (by norm_num)
theorem B437501 : Blo 255820 437501 := bbase (se 3 (by rfl) ⟨82031, by rfl⟩ : syracuseStep 437501 = 164063) (by norm_num)
theorem B273785 : Blo 255820 273785 := bbase (se 2 (by rfl) ⟨102669, by rfl⟩ : syracuseStep 273785 = 205339) (by norm_num)
theorem B437629 : Blo 255820 437629 := bbase (se 3 (by rfl) ⟨82055, by rfl⟩ : syracuseStep 437629 = 164111) (by norm_num)
theorem B863621 : Blo 255820 863621 := bbase (se 4 (by rfl) ⟨80964, by rfl⟩ : syracuseStep 863621 = 161929) (by norm_num)
theorem B372109 : Blo 255820 372109 := bbase (se 3 (by rfl) ⟨69770, by rfl⟩ : syracuseStep 372109 = 139541) (by norm_num)
theorem B437717 : Blo 255820 437717 := bbase (se 7 (by rfl) ⟨5129, by rfl⟩ : syracuseStep 437717 = 10259) (by norm_num)
theorem B437845 : Blo 255820 437845 := bbase (se 8 (by rfl) ⟨2565, by rfl⟩ : syracuseStep 437845 = 5131) (by norm_num)
theorem B274033 : Blo 255820 274033 := bbase (se 2 (by rfl) ⟨102762, by rfl⟩ : syracuseStep 274033 = 205525) (by norm_num)
theorem B437933 : Blo 255820 437933 := bbase (se 3 (by rfl) ⟨82112, by rfl⟩ : syracuseStep 437933 = 164225) (by norm_num)
theorem B438005 : Blo 255820 438005 := bbase (se 5 (by rfl) ⟨20531, by rfl⟩ : syracuseStep 438005 = 41063) (by norm_num)
theorem B438053 : Blo 255820 438053 := bbase (se 4 (by rfl) ⟨41067, by rfl⟩ : syracuseStep 438053 = 82135) (by norm_num)
theorem B438061 : Blo 255820 438061 := bbase (se 3 (by rfl) ⟨82136, by rfl⟩ : syracuseStep 438061 = 164273) (by norm_num)
theorem B864053 : Blo 255820 864053 := bbase (se 5 (by rfl) ⟨40502, by rfl⟩ : syracuseStep 864053 = 81005) (by norm_num)
theorem B2207573 : Blo 255820 2207573 := bbase (se 9 (by rfl) ⟨6467, by rfl⟩ : syracuseStep 2207573 = 12935) (by norm_num)
theorem B438149 : Blo 255820 438149 := bbase (se 4 (by rfl) ⟨41076, by rfl⟩ : syracuseStep 438149 = 82153) (by norm_num)
theorem B1093621 : Blo 255820 1093621 := bbase (se 5 (by rfl) ⟨51263, by rfl⟩ : syracuseStep 1093621 = 102527) (by norm_num)
theorem B1093637 : Blo 255820 1093637 := bbase (se 4 (by rfl) ⟨102528, by rfl⟩ : syracuseStep 1093637 = 205057) (by norm_num)
theorem B438277 : Blo 255820 438277 := bbase (se 4 (by rfl) ⟨41088, by rfl⟩ : syracuseStep 438277 = 82177) (by norm_num)
theorem B274465 : Blo 255820 274465 := bbase (se 2 (by rfl) ⟨102924, by rfl⟩ : syracuseStep 274465 = 205849) (by norm_num)
theorem B438365 : Blo 255820 438365 := bbase (se 3 (by rfl) ⟨82193, by rfl⟩ : syracuseStep 438365 = 164387) (by norm_num)
theorem B274537 : Blo 255820 274537 := bbase (se 2 (by rfl) ⟨102951, by rfl⟩ : syracuseStep 274537 = 205903) (by norm_num)
theorem B897173 : Blo 255820 897173 := bbase (se 6 (by rfl) ⟨21027, by rfl⟩ : syracuseStep 897173 = 42055) (by norm_num)
theorem B2076853 : Blo 255820 2076853 := bbase (se 5 (by rfl) ⟨97352, by rfl⟩ : syracuseStep 2076853 = 194705) (by norm_num)
theorem B864485 : Blo 255820 864485 := bbase (se 4 (by rfl) ⟨81045, by rfl⟩ : syracuseStep 864485 = 162091) (by norm_num)
theorem B700805 : Blo 255820 700805 := bbase (se 4 (by rfl) ⟨65700, by rfl⟩ : syracuseStep 700805 = 131401) (by norm_num)
theorem B930197 : Blo 255820 930197 := bbase (se 6 (by rfl) ⟨21801, by rfl⟩ : syracuseStep 930197 = 43603) (by norm_num)
theorem B733637 : Blo 255820 733637 := bbase (se 4 (by rfl) ⟨68778, by rfl⟩ : syracuseStep 733637 = 137557) (by norm_num)
theorem B831941 : Blo 255820 831941 := bbase (se 4 (by rfl) ⟨77994, by rfl⟩ : syracuseStep 831941 = 155989) (by norm_num)
theorem B274909 : Blo 255820 274909 := bbase (se 3 (by rfl) ⟨51545, by rfl⟩ : syracuseStep 274909 = 103091) (by norm_num)
theorem B1192421 : Blo 255820 1192421 := bbase (se 4 (by rfl) ⟨111789, by rfl⟩ : syracuseStep 1192421 = 223579) (by norm_num)
theorem B1487413 : Blo 255820 1487413 := bbase (se 5 (by rfl) ⟨69722, by rfl⟩ : syracuseStep 1487413 = 139445) (by norm_num)
theorem B864917 : Blo 255820 864917 := bbase (se 6 (by rfl) ⟨20271, by rfl⟩ : syracuseStep 864917 = 40543) (by norm_num)
theorem B438989 : Blo 255820 438989 := bbase (se 3 (by rfl) ⟨82310, by rfl⟩ : syracuseStep 438989 = 164621) (by norm_num)
theorem B701173 : Blo 255820 701173 := bbase (se 5 (by rfl) ⟨32867, by rfl⟩ : syracuseStep 701173 = 65735) (by norm_num)
theorem B996101 : Blo 255820 996101 := bbase (se 4 (by rfl) ⟨93384, by rfl⟩ : syracuseStep 996101 = 186769) (by norm_num)
theorem B930629 : Blo 255820 930629 := bbase (se 4 (by rfl) ⟨87246, by rfl⟩ : syracuseStep 930629 = 174493) (by norm_num)
theorem B275285 : Blo 255820 275285 := bbase (se 9 (by rfl) ⟨806, by rfl⟩ : syracuseStep 275285 = 1613) (by norm_num)
theorem B275357 : Blo 255820 275357 := bbase (se 3 (by rfl) ⟨51629, by rfl⟩ : syracuseStep 275357 = 103259) (by norm_num)
theorem B865349 : Blo 255820 865349 := bbase (se 4 (by rfl) ⟨81126, by rfl⟩ : syracuseStep 865349 = 162253) (by norm_num)
theorem B308297 : Blo 255820 308297 := bbase (se 2 (by rfl) ⟨115611, by rfl⟩ : syracuseStep 308297 = 231223) (by norm_num)
theorem B275545 : Blo 255820 275545 := bbase (se 2 (by rfl) ⟨103329, by rfl⟩ : syracuseStep 275545 = 206659) (by norm_num)
theorem B734309 : Blo 255820 734309 := bbase (se 4 (by rfl) ⟨68841, by rfl⟩ : syracuseStep 734309 = 137683) (by norm_num)
theorem B701669 : Blo 255820 701669 := bbase (se 4 (by rfl) ⟨65781, by rfl⟩ : syracuseStep 701669 = 131563) (by norm_num)
theorem B275729 : Blo 255820 275729 := bbase (se 2 (by rfl) ⟨103398, by rfl⟩ : syracuseStep 275729 = 206797) (by norm_num)
theorem B308557 : Blo 255820 308557 := bbase (se 3 (by rfl) ⟨57854, by rfl⟩ : syracuseStep 308557 = 115709) (by norm_num)
theorem B308605 : Blo 255820 308605 := bbase (se 3 (by rfl) ⟨57863, by rfl⟩ : syracuseStep 308605 = 115727) (by norm_num)
theorem B865781 : Blo 255820 865781 := bbase (se 5 (by rfl) ⟨40583, by rfl⟩ : syracuseStep 865781 = 81167) (by norm_num)
theorem B2635253 : Blo 255820 2635253 := bbase (se 5 (by rfl) ⟨123527, by rfl⟩ : syracuseStep 2635253 = 247055) (by norm_num)
theorem B734741 : Blo 255820 734741 := bbase (se 6 (by rfl) ⟨17220, by rfl⟩ : syracuseStep 734741 = 34441) (by norm_num)
theorem B8336981 : Blo 255820 8336981 := bbase (se 8 (by rfl) ⟨48849, by rfl⟩ : syracuseStep 8336981 = 97699) (by norm_num)
theorem B996965 : Blo 255820 996965 := bbase (se 4 (by rfl) ⟨93465, by rfl⟩ : syracuseStep 996965 = 186931) (by norm_num)
theorem B472717 : Blo 255820 472717 := bbase (se 3 (by rfl) ⟨88634, by rfl⟩ : syracuseStep 472717 = 177269) (by norm_num)
theorem B2635541 : Blo 255820 2635541 := bbase (se 6 (by rfl) ⟨61770, by rfl⟩ : syracuseStep 2635541 = 123541) (by norm_num)
theorem B931637 : Blo 255820 931637 := bbase (se 5 (by rfl) ⟨43670, by rfl⟩ : syracuseStep 931637 = 87341) (by norm_num)
theorem B1259333 : Blo 255820 1259333 := bbase (se 4 (by rfl) ⟨118062, by rfl⟩ : syracuseStep 1259333 = 236125) (by norm_num)
theorem B866213 : Blo 255820 866213 := bbase (se 4 (by rfl) ⟨81207, by rfl⟩ : syracuseStep 866213 = 162415) (by norm_num)
theorem B1718261 : Blo 255820 1718261 := bbase (se 5 (by rfl) ⟨80543, by rfl⟩ : syracuseStep 1718261 = 161087) (by norm_num)
theorem B276481 : Blo 255820 276481 := bbase (se 2 (by rfl) ⟨103680, by rfl⟩ : syracuseStep 276481 = 207361) (by norm_num)
theorem B309277 : Blo 255820 309277 := bbase (se 3 (by rfl) ⟨57989, by rfl⟩ : syracuseStep 309277 = 115979) (by norm_num)
theorem B276553 : Blo 255820 276553 := bbase (se 2 (by rfl) ⟨103707, by rfl⟩ : syracuseStep 276553 = 207415) (by norm_num)
theorem B1095893 : Blo 255820 1095893 := bbase (se 7 (by rfl) ⟨12842, by rfl⟩ : syracuseStep 1095893 = 25685) (by norm_num)
theorem B276733 : Blo 255820 276733 := bbase (se 3 (by rfl) ⟨51887, by rfl⟩ : syracuseStep 276733 = 103775) (by norm_num)
theorem B735493 : Blo 255820 735493 := bbase (se 4 (by rfl) ⟨68952, by rfl⟩ : syracuseStep 735493 = 137905) (by norm_num)
theorem B899381 : Blo 255820 899381 := bbase (se 5 (by rfl) ⟨42158, by rfl⟩ : syracuseStep 899381 = 84317) (by norm_num)
theorem B866645 : Blo 255820 866645 := bbase (se 10 (by rfl) ⟨1269, by rfl⟩ : syracuseStep 866645 = 2539) (by norm_num)
theorem B440797 : Blo 255820 440797 := bbase (se 3 (by rfl) ⟨82649, by rfl⟩ : syracuseStep 440797 = 165299) (by norm_num)
theorem B277177 : Blo 255820 277177 := bbase (se 2 (by rfl) ⟨103941, by rfl⟩ : syracuseStep 277177 = 207883) (by norm_num)
theorem B1948373 : Blo 255820 1948373 := bbase (se 7 (by rfl) ⟨22832, by rfl⟩ : syracuseStep 1948373 = 45665) (by norm_num)
theorem B867077 : Blo 255820 867077 := bbase (se 4 (by rfl) ⟨81288, by rfl⟩ : syracuseStep 867077 = 162577) (by norm_num)
theorem B277301 : Blo 255820 277301 := bbase (se 5 (by rfl) ⟨12998, by rfl⟩ : syracuseStep 277301 = 25997) (by norm_num)
theorem B277453 : Blo 255820 277453 := bbase (se 3 (by rfl) ⟨52022, by rfl⟩ : syracuseStep 277453 = 104045) (by norm_num)
theorem B1850357 : Blo 255820 1850357 := bbase (se 5 (by rfl) ⟨86735, by rfl⟩ : syracuseStep 1850357 = 173471) (by norm_num)
theorem B310277 : Blo 255820 310277 := bbase (se 4 (by rfl) ⟨29088, by rfl⟩ : syracuseStep 310277 = 58177) (by norm_num)
theorem B277553 : Blo 255820 277553 := bbase (se 2 (by rfl) ⟨104082, by rfl⟩ : syracuseStep 277553 = 208165) (by norm_num)
theorem B310349 : Blo 255820 310349 := bbase (se 3 (by rfl) ⟨58190, by rfl⟩ : syracuseStep 310349 = 116381) (by norm_num)
theorem B1719413 : Blo 255820 1719413 := bbase (se 5 (by rfl) ⟨80597, by rfl⟩ : syracuseStep 1719413 = 161195) (by norm_num)
theorem B277625 : Blo 255820 277625 := bbase (se 2 (by rfl) ⟨104109, by rfl⟩ : syracuseStep 277625 = 208219) (by norm_num)
theorem B867509 : Blo 255820 867509 := bbase (se 5 (by rfl) ⟨40664, by rfl⟩ : syracuseStep 867509 = 81329) (by norm_num)
theorem B1785077 : Blo 255820 1785077 := bbase (se 5 (by rfl) ⟨83675, by rfl⟩ : syracuseStep 1785077 = 167351) (by norm_num)
theorem B933125 : Blo 255820 933125 := bbase (se 4 (by rfl) ⟨87480, by rfl⟩ : syracuseStep 933125 = 174961) (by norm_num)
theorem B638237 : Blo 255820 638237 := bbase (se 3 (by rfl) ⟨119669, by rfl⟩ : syracuseStep 638237 = 239339) (by norm_num)
theorem B310657 : Blo 255820 310657 := bbase (se 2 (by rfl) ⟨116496, by rfl⟩ : syracuseStep 310657 = 232993) (by norm_num)
theorem B310825 : Blo 255820 310825 := bbase (se 2 (by rfl) ⟨116559, by rfl⟩ : syracuseStep 310825 = 233119) (by norm_num)
theorem B310873 : Blo 255820 310873 := bbase (se 2 (by rfl) ⟨116577, by rfl⟩ : syracuseStep 310873 = 233155) (by norm_num)
theorem B867941 : Blo 255820 867941 := bbase (se 4 (by rfl) ⟨81369, by rfl⟩ : syracuseStep 867941 = 162739) (by norm_num)
theorem B310969 : Blo 255820 310969 := bbase (se 2 (by rfl) ⟨116613, by rfl⟩ : syracuseStep 310969 = 233227) (by norm_num)
theorem B1457909 : Blo 255820 1457909 := bbase (se 5 (by rfl) ⟨68339, by rfl⟩ : syracuseStep 1457909 = 136679) (by norm_num)
theorem B278353 : Blo 255820 278353 := bbase (se 2 (by rfl) ⟨104382, by rfl⟩ : syracuseStep 278353 = 208765) (by norm_num)
theorem B868373 : Blo 255820 868373 := bbase (se 6 (by rfl) ⟨20352, by rfl⟩ : syracuseStep 868373 = 40705) (by norm_num)
theorem B442493 : Blo 255820 442493 := bbase (se 3 (by rfl) ⟨82967, by rfl⟩ : syracuseStep 442493 = 165935) (by norm_num)
theorem B442541 : Blo 255820 442541 := bbase (se 3 (by rfl) ⟨82976, by rfl⟩ : syracuseStep 442541 = 165953) (by norm_num)
theorem B704693 : Blo 255820 704693 := bbase (se 5 (by rfl) ⟨33032, by rfl⟩ : syracuseStep 704693 = 66065) (by norm_num)
theorem B442597 : Blo 255820 442597 := bbase (se 4 (by rfl) ⟨41493, by rfl⟩ : syracuseStep 442597 = 82987) (by norm_num)
theorem B311545 : Blo 255820 311545 := bbase (se 2 (by rfl) ⟨116829, by rfl⟩ : syracuseStep 311545 = 233659) (by norm_num)
theorem B409909 : Blo 255820 409909 := bbase (se 5 (by rfl) ⟨19214, by rfl⟩ : syracuseStep 409909 = 38429) (by norm_num)
theorem B868805 : Blo 255820 868805 := bbase (se 4 (by rfl) ⟨81450, by rfl⟩ : syracuseStep 868805 = 162901) (by norm_num)
theorem B1655477 : Blo 255820 1655477 := bbase (se 5 (by rfl) ⟨77600, by rfl⟩ : syracuseStep 1655477 = 155201) (by norm_num)
theorem B1229573 : Blo 255820 1229573 := bbase (se 4 (by rfl) ⟨115272, by rfl⟩ : syracuseStep 1229573 = 230545) (by norm_num)
theorem B1295189 : Blo 255820 1295189 := bbase (se 9 (by rfl) ⟨3794, by rfl⟩ : syracuseStep 1295189 = 7589) (by norm_num)
theorem B869237 : Blo 255820 869237 := bbase (se 5 (by rfl) ⟨40745, by rfl⟩ : syracuseStep 869237 = 81491) (by norm_num)
theorem B1459093 : Blo 255820 1459093 := bbase (se 6 (by rfl) ⟨34197, by rfl⟩ : syracuseStep 1459093 = 68395) (by norm_num)
theorem B738341 : Blo 255820 738341 := bbase (se 4 (by rfl) ⟨69219, by rfl⟩ : syracuseStep 738341 = 138439) (by norm_num)
theorem B410845 : Blo 255820 410845 := bbase (se 3 (by rfl) ⟨77033, by rfl⟩ : syracuseStep 410845 = 154067) (by norm_num)
theorem B869669 : Blo 255820 869669 := bbase (se 4 (by rfl) ⟨81531, by rfl⟩ : syracuseStep 869669 = 163063) (by norm_num)
theorem B870101 : Blo 255820 870101 := bbase (se 7 (by rfl) ⟨10196, by rfl⟩ : syracuseStep 870101 = 20393) (by norm_num)
theorem B1296485 : Blo 255820 1296485 := bbase (se 4 (by rfl) ⟨121545, by rfl⟩ : syracuseStep 1296485 = 243091) (by norm_num)
theorem B575621 : Blo 255820 575621 := bbase (se 4 (by rfl) ⟨53964, by rfl⟩ : syracuseStep 575621 = 107929) (by norm_num)
theorem B870533 : Blo 255820 870533 := bbase (se 4 (by rfl) ⟨81612, by rfl⟩ : syracuseStep 870533 = 163225) (by norm_num)
theorem B1230997 : Blo 255820 1230997 := bbase (se 6 (by rfl) ⟨28851, by rfl⟩ : syracuseStep 1230997 = 57703) (by norm_num)
theorem B1099925 : Blo 255820 1099925 := bbase (se 6 (by rfl) ⟨25779, by rfl⟩ : syracuseStep 1099925 = 51559) (by norm_num)
theorem B739525 : Blo 255820 739525 := bbase (se 4 (by rfl) ⟨69330, by rfl⟩ : syracuseStep 739525 = 138661) (by norm_num)
theorem B575693 : Blo 255820 575693 := bbase (se 3 (by rfl) ⟨107942, by rfl⟩ : syracuseStep 575693 = 215885) (by norm_num)
theorem B575765 : Blo 255820 575765 := bbase (se 6 (by rfl) ⟨13494, by rfl⟩ : syracuseStep 575765 = 26989) (by norm_num)
theorem B575837 : Blo 255820 575837 := bbase (se 3 (by rfl) ⟨107969, by rfl⟩ : syracuseStep 575837 = 215939) (by norm_num)
theorem B739685 : Blo 255820 739685 := bbase (se 4 (by rfl) ⟨69345, by rfl⟩ : syracuseStep 739685 = 138691) (by norm_num)
theorem B412037 : Blo 255820 412037 := bbase (se 4 (by rfl) ⟨38628, by rfl⟩ : syracuseStep 412037 = 77257) (by norm_num)
theorem B575909 : Blo 255820 575909 := bbase (se 4 (by rfl) ⟨53991, by rfl⟩ : syracuseStep 575909 = 107983) (by norm_num)
theorem B575981 : Blo 255820 575981 := bbase (se 3 (by rfl) ⟨107996, by rfl⟩ : syracuseStep 575981 = 215993) (by norm_num)
theorem B576053 : Blo 255820 576053 := bbase (se 5 (by rfl) ⟨27002, by rfl⟩ : syracuseStep 576053 = 54005) (by norm_num)
theorem B870965 : Blo 255820 870965 := bbase (se 5 (by rfl) ⟨40826, by rfl⟩ : syracuseStep 870965 = 81653) (by norm_num)
theorem B412229 : Blo 255820 412229 := bbase (se 4 (by rfl) ⟨38646, by rfl⟩ : syracuseStep 412229 = 77293) (by norm_num)
theorem B576125 : Blo 255820 576125 := bbase (se 3 (by rfl) ⟨108023, by rfl⟩ : syracuseStep 576125 = 216047) (by norm_num)
theorem B576197 : Blo 255820 576197 := bbase (se 4 (by rfl) ⟨54018, by rfl⟩ : syracuseStep 576197 = 108037) (by norm_num)
theorem B576269 : Blo 255820 576269 := bbase (se 3 (by rfl) ⟨108050, by rfl⟩ : syracuseStep 576269 = 216101) (by norm_num)
theorem B576341 : Blo 255820 576341 := bbase (se 9 (by rfl) ⟨1688, by rfl⟩ : syracuseStep 576341 = 3377) (by norm_num)
theorem B1461077 : Blo 255820 1461077 := bbase (se 9 (by rfl) ⟨4280, by rfl⟩ : syracuseStep 1461077 = 8561) (by norm_num)
theorem B576413 : Blo 255820 576413 := bbase (se 3 (by rfl) ⟨108077, by rfl⟩ : syracuseStep 576413 = 216155) (by norm_num)
theorem B576485 : Blo 255820 576485 := bbase (se 4 (by rfl) ⟨54045, by rfl⟩ : syracuseStep 576485 = 108091) (by norm_num)
theorem B871397 : Blo 255820 871397 := bbase (se 4 (by rfl) ⟨81693, by rfl⟩ : syracuseStep 871397 = 163387) (by norm_num)
theorem B1854485 : Blo 255820 1854485 := bbase (se 6 (by rfl) ⟨43464, by rfl⟩ : syracuseStep 1854485 = 86929) (by norm_num)
theorem B4213781 : Blo 255820 4213781 := bbase (se 6 (by rfl) ⟨98760, by rfl⟩ : syracuseStep 4213781 = 197521) (by norm_num)
theorem B576557 : Blo 255820 576557 := bbase (se 3 (by rfl) ⟨108104, by rfl⟩ : syracuseStep 576557 = 216209) (by norm_num)
theorem B2477141 : Blo 255820 2477141 := bbase (se 8 (by rfl) ⟨14514, by rfl⟩ : syracuseStep 2477141 = 29029) (by norm_num)
theorem B576629 : Blo 255820 576629 := bbase (se 5 (by rfl) ⟨27029, by rfl⟩ : syracuseStep 576629 = 54059) (by norm_num)
theorem B576701 : Blo 255820 576701 := bbase (se 3 (by rfl) ⟨108131, by rfl⟩ : syracuseStep 576701 = 216263) (by norm_num)
theorem B576773 : Blo 255820 576773 := bbase (se 4 (by rfl) ⟨54072, by rfl⟩ : syracuseStep 576773 = 108145) (by norm_num)
theorem B347413 : Blo 255820 347413 := bbase (se 6 (by rfl) ⟨8142, by rfl⟩ : syracuseStep 347413 = 16285) (by norm_num)
theorem B576845 : Blo 255820 576845 := bbase (se 3 (by rfl) ⟨108158, by rfl⟩ : syracuseStep 576845 = 216317) (by norm_num)
theorem B1297781 : Blo 255820 1297781 := bbase (se 5 (by rfl) ⟨60833, by rfl⟩ : syracuseStep 1297781 = 121667) (by norm_num)
theorem B576917 : Blo 255820 576917 := bbase (se 6 (by rfl) ⟨13521, by rfl⟩ : syracuseStep 576917 = 27043) (by norm_num)
theorem B871829 : Blo 255820 871829 := bbase (se 6 (by rfl) ⟨20433, by rfl⟩ : syracuseStep 871829 = 40867) (by norm_num)
theorem B970181 : Blo 255820 970181 := bbase (se 4 (by rfl) ⟨90954, by rfl⟩ : syracuseStep 970181 = 181909) (by norm_num)
theorem B576989 : Blo 255820 576989 := bbase (se 3 (by rfl) ⟨108185, by rfl⟩ : syracuseStep 576989 = 216371) (by norm_num)
theorem B314861 : Blo 255820 314861 := bbase (se 3 (by rfl) ⟨59036, by rfl⟩ : syracuseStep 314861 = 118073) (by norm_num)
theorem B577061 : Blo 255820 577061 := bbase (se 4 (by rfl) ⟨54099, by rfl⟩ : syracuseStep 577061 = 108199) (by norm_num)
theorem B577133 : Blo 255820 577133 := bbase (se 3 (by rfl) ⟨108212, by rfl⟩ : syracuseStep 577133 = 216425) (by norm_num)
theorem B675461 : Blo 255820 675461 := bbase (se 4 (by rfl) ⟨63324, by rfl⟩ : syracuseStep 675461 = 126649) (by norm_num)
theorem B577205 : Blo 255820 577205 := bbase (se 5 (by rfl) ⟨27056, by rfl⟩ : syracuseStep 577205 = 54113) (by norm_num)
theorem B675541 : Blo 255820 675541 := bbase (se 7 (by rfl) ⟨7916, by rfl⟩ : syracuseStep 675541 = 15833) (by norm_num)
theorem B577277 : Blo 255820 577277 := bbase (se 3 (by rfl) ⟨108239, by rfl⟩ : syracuseStep 577277 = 216479) (by norm_num)
theorem B577349 : Blo 255820 577349 := bbase (se 4 (by rfl) ⟨54126, by rfl⟩ : syracuseStep 577349 = 108253) (by norm_num)
theorem B872261 : Blo 255820 872261 := bbase (se 4 (by rfl) ⟨81774, by rfl⟩ : syracuseStep 872261 = 163549) (by norm_num)
theorem B1101701 : Blo 255820 1101701 := bbase (se 4 (by rfl) ⟨103284, by rfl⟩ : syracuseStep 1101701 = 206569) (by norm_num)
theorem B577421 : Blo 255820 577421 := bbase (se 3 (by rfl) ⟨108266, by rfl⟩ : syracuseStep 577421 = 216533) (by norm_num)
theorem B577493 : Blo 255820 577493 := bbase (se 7 (by rfl) ⟨6767, by rfl⟩ : syracuseStep 577493 = 13535) (by norm_num)
theorem B413677 : Blo 255820 413677 := bbase (se 3 (by rfl) ⟨77564, by rfl⟩ : syracuseStep 413677 = 155129) (by norm_num)
theorem B577565 : Blo 255820 577565 := bbase (se 3 (by rfl) ⟨108293, by rfl⟩ : syracuseStep 577565 = 216587) (by norm_num)
theorem B577637 : Blo 255820 577637 := bbase (se 4 (by rfl) ⟨54153, by rfl⟩ : syracuseStep 577637 = 108307) (by norm_num)
theorem B577709 : Blo 255820 577709 := bbase (se 3 (by rfl) ⟨108320, by rfl⟩ : syracuseStep 577709 = 216641) (by norm_num)
theorem B577781 : Blo 255820 577781 := bbase (se 5 (by rfl) ⟨27083, by rfl⟩ : syracuseStep 577781 = 54167) (by norm_num)
theorem B872693 : Blo 255820 872693 := bbase (se 5 (by rfl) ⟨40907, by rfl⟩ : syracuseStep 872693 = 81815) (by norm_num)
theorem B577853 : Blo 255820 577853 := bbase (se 3 (by rfl) ⟨108347, by rfl⟩ : syracuseStep 577853 = 216695) (by norm_num)
theorem B577925 : Blo 255820 577925 := bbase (se 4 (by rfl) ⟨54180, by rfl⟩ : syracuseStep 577925 = 108361) (by norm_num)
theorem B348565 : Blo 255820 348565 := bbase (se 6 (by rfl) ⟨8169, by rfl⟩ : syracuseStep 348565 = 16339) (by norm_num)
theorem B577997 : Blo 255820 577997 := bbase (se 3 (by rfl) ⟨108374, by rfl⟩ : syracuseStep 577997 = 216749) (by norm_num)
theorem B348629 : Blo 255820 348629 := bbase (se 7 (by rfl) ⟨4085, by rfl⟩ : syracuseStep 348629 = 8171) (by norm_num)
theorem B578069 : Blo 255820 578069 := bbase (se 6 (by rfl) ⟨13548, by rfl⟩ : syracuseStep 578069 = 27097) (by norm_num)
theorem B3986005 : Blo 255820 3986005 := bbase (se 8 (by rfl) ⟨23355, by rfl⟩ : syracuseStep 3986005 = 46711) (by norm_num)
theorem B578141 : Blo 255820 578141 := bbase (se 3 (by rfl) ⟨108401, by rfl⟩ : syracuseStep 578141 = 216803) (by norm_num)
theorem B348797 : Blo 255820 348797 := bbase (se 3 (by rfl) ⟨65399, by rfl⟩ : syracuseStep 348797 = 130799) (by norm_num)
theorem B1299077 : Blo 255820 1299077 := bbase (se 4 (by rfl) ⟨121788, by rfl⟩ : syracuseStep 1299077 = 243577) (by norm_num)
theorem B578213 : Blo 255820 578213 := bbase (se 4 (by rfl) ⟨54207, by rfl⟩ : syracuseStep 578213 = 108415) (by norm_num)
theorem B873125 : Blo 255820 873125 := bbase (se 4 (by rfl) ⟨81855, by rfl⟩ : syracuseStep 873125 = 163711) (by norm_num)
theorem B578285 : Blo 255820 578285 := bbase (se 3 (by rfl) ⟨108428, by rfl⟩ : syracuseStep 578285 = 216857) (by norm_num)
theorem B578357 : Blo 255820 578357 := bbase (se 5 (by rfl) ⟨27110, by rfl⟩ : syracuseStep 578357 = 54221) (by norm_num)
theorem B971621 : Blo 255820 971621 := bbase (se 4 (by rfl) ⟨91089, by rfl⟩ : syracuseStep 971621 = 182179) (by norm_num)
theorem B1102693 : Blo 255820 1102693 := bbase (se 4 (by rfl) ⟨103377, by rfl⟩ : syracuseStep 1102693 = 206755) (by norm_num)
theorem B578429 : Blo 255820 578429 := bbase (se 3 (by rfl) ⟨108455, by rfl⟩ : syracuseStep 578429 = 216911) (by norm_num)
theorem B578501 : Blo 255820 578501 := bbase (se 4 (by rfl) ⟨54234, by rfl⟩ : syracuseStep 578501 = 108469) (by norm_num)
theorem B1463285 : Blo 255820 1463285 := bbase (se 5 (by rfl) ⟨68591, by rfl⟩ : syracuseStep 1463285 = 137183) (by norm_num)
theorem B578573 : Blo 255820 578573 := bbase (se 3 (by rfl) ⟨108482, by rfl⟩ : syracuseStep 578573 = 216965) (by norm_num)
theorem B578645 : Blo 255820 578645 := bbase (se 8 (by rfl) ⟨3390, by rfl⟩ : syracuseStep 578645 = 6781) (by norm_num)
theorem B873557 : Blo 255820 873557 := bbase (se 8 (by rfl) ⟨5118, by rfl⟩ : syracuseStep 873557 = 10237) (by norm_num)
theorem B971909 : Blo 255820 971909 := bbase (se 4 (by rfl) ⟨91116, by rfl⟩ : syracuseStep 971909 = 182233) (by norm_num)
theorem B578717 : Blo 255820 578717 := bbase (se 3 (by rfl) ⟨108509, by rfl⟩ : syracuseStep 578717 = 217019) (by norm_num)
theorem B578789 : Blo 255820 578789 := bbase (se 4 (by rfl) ⟨54261, by rfl⟩ : syracuseStep 578789 = 108523) (by norm_num)
theorem B578861 : Blo 255820 578861 := bbase (se 3 (by rfl) ⟨108536, by rfl⟩ : syracuseStep 578861 = 217073) (by norm_num)
theorem B415061 : Blo 255820 415061 := bbase (se 16 (by rfl) ⟨9, by rfl⟩ : syracuseStep 415061 = 19) (by norm_num)
theorem B578933 : Blo 255820 578933 := bbase (se 5 (by rfl) ⟨27137, by rfl⟩ : syracuseStep 578933 = 54275) (by norm_num)
theorem B579005 : Blo 255820 579005 := bbase (se 3 (by rfl) ⟨108563, by rfl⟩ : syracuseStep 579005 = 217127) (by norm_num)
theorem B579077 : Blo 255820 579077 := bbase (se 4 (by rfl) ⟨54288, by rfl⟩ : syracuseStep 579077 = 108577) (by norm_num)
theorem B873989 : Blo 255820 873989 := bbase (se 4 (by rfl) ⟨81936, by rfl⟩ : syracuseStep 873989 = 163873) (by norm_num)
theorem B415253 : Blo 255820 415253 := bbase (se 6 (by rfl) ⟨9732, by rfl⟩ : syracuseStep 415253 = 19465) (by norm_num)
theorem B579149 : Blo 255820 579149 := bbase (se 3 (by rfl) ⟨108590, by rfl⟩ : syracuseStep 579149 = 217181) (by norm_num)
theorem B579221 : Blo 255820 579221 := bbase (se 6 (by rfl) ⟨13575, by rfl⟩ : syracuseStep 579221 = 27151) (by norm_num)
theorem B579293 : Blo 255820 579293 := bbase (se 3 (by rfl) ⟨108617, by rfl⟩ : syracuseStep 579293 = 217235) (by norm_num)
theorem B579365 : Blo 255820 579365 := bbase (se 4 (by rfl) ⟨54315, by rfl⟩ : syracuseStep 579365 = 108631) (by norm_num)
theorem B579437 : Blo 255820 579437 := bbase (se 3 (by rfl) ⟨108644, by rfl⟩ : syracuseStep 579437 = 217289) (by norm_num)
theorem B1300373 : Blo 255820 1300373 := bbase (se 6 (by rfl) ⟨30477, by rfl⟩ : syracuseStep 1300373 = 60955) (by norm_num)
theorem B579509 : Blo 255820 579509 := bbase (se 5 (by rfl) ⟨27164, by rfl⟩ : syracuseStep 579509 = 54329) (by norm_num)
theorem B874421 : Blo 255820 874421 := bbase (se 5 (by rfl) ⟨40988, by rfl⟩ : syracuseStep 874421 = 81977) (by norm_num)
theorem B579581 : Blo 255820 579581 := bbase (se 3 (by rfl) ⟨108671, by rfl⟩ : syracuseStep 579581 = 217343) (by norm_num)
theorem B546853 : Blo 255820 546853 := bbase (se 4 (by rfl) ⟨51267, by rfl⟩ : syracuseStep 546853 = 102535) (by norm_num)
theorem B579653 : Blo 255820 579653 := bbase (se 4 (by rfl) ⟨54342, by rfl⟩ : syracuseStep 579653 = 108685) (by norm_num)
theorem B415829 : Blo 255820 415829 := bbase (se 8 (by rfl) ⟨2436, by rfl⟩ : syracuseStep 415829 = 4873) (by norm_num)
theorem B579725 : Blo 255820 579725 := bbase (se 3 (by rfl) ⟨108698, by rfl⟩ : syracuseStep 579725 = 217397) (by norm_num)
theorem B579797 : Blo 255820 579797 := bbase (se 7 (by rfl) ⟨6794, by rfl⟩ : syracuseStep 579797 = 13589) (by norm_num)
theorem B579869 : Blo 255820 579869 := bbase (se 3 (by rfl) ⟨108725, by rfl⟩ : syracuseStep 579869 = 217451) (by norm_num)
theorem B973093 : Blo 255820 973093 := bbase (se 4 (by rfl) ⟨91227, by rfl⟩ : syracuseStep 973093 = 182455) (by norm_num)
theorem B1956149 : Blo 255820 1956149 := bbase (se 5 (by rfl) ⟨91694, by rfl⟩ : syracuseStep 1956149 = 183389) (by norm_num)
theorem B579941 : Blo 255820 579941 := bbase (se 4 (by rfl) ⟨54369, by rfl⟩ : syracuseStep 579941 = 108739) (by norm_num)
theorem B874853 : Blo 255820 874853 := bbase (se 4 (by rfl) ⟨82017, by rfl⟩ : syracuseStep 874853 = 164035) (by norm_num)
theorem B547229 : Blo 255820 547229 := bbase (se 3 (by rfl) ⟨102605, by rfl⟩ : syracuseStep 547229 = 205211) (by norm_num)
theorem B580013 : Blo 255820 580013 := bbase (se 3 (by rfl) ⟨108752, by rfl⟩ : syracuseStep 580013 = 217505) (by norm_num)
theorem B580085 : Blo 255820 580085 := bbase (se 5 (by rfl) ⟨27191, by rfl⟩ : syracuseStep 580085 = 54383) (by norm_num)
theorem B580157 : Blo 255820 580157 := bbase (se 3 (by rfl) ⟨108779, by rfl⟩ : syracuseStep 580157 = 217559) (by norm_num)
theorem B973397 : Blo 255820 973397 := bbase (se 8 (by rfl) ⟨5703, by rfl⟩ : syracuseStep 973397 = 11407) (by norm_num)
theorem B580229 : Blo 255820 580229 := bbase (se 4 (by rfl) ⟨54396, by rfl⟩ : syracuseStep 580229 = 108793) (by norm_num)
theorem B580301 : Blo 255820 580301 := bbase (se 3 (by rfl) ⟨108806, by rfl⟩ : syracuseStep 580301 = 217613) (by norm_num)
theorem B383741 : Blo 255820 383741 := bbase (se 3 (by rfl) ⟨71951, by rfl⟩ : syracuseStep 383741 = 143903) (by norm_num)
theorem B875269 : Blo 255820 875269 := bbase (se 4 (by rfl) ⟨82056, by rfl⟩ : syracuseStep 875269 = 164113) (by norm_num)
theorem B383765 : Blo 255820 383765 := bbase (se 6 (by rfl) ⟨8994, by rfl⟩ : syracuseStep 383765 = 17989) (by norm_num)
theorem B580373 : Blo 255820 580373 := bbase (se 6 (by rfl) ⟨13602, by rfl⟩ : syracuseStep 580373 = 27205) (by norm_num)
theorem B875285 : Blo 255820 875285 := bbase (se 6 (by rfl) ⟨20514, by rfl⟩ : syracuseStep 875285 = 41029) (by norm_num)
theorem B383789 : Blo 255820 383789 := bbase (se 3 (by rfl) ⟨71960, by rfl⟩ : syracuseStep 383789 = 143921) (by norm_num)
theorem B383813 : Blo 255820 383813 := bbase (se 4 (by rfl) ⟨35982, by rfl⟩ : syracuseStep 383813 = 71965) (by norm_num)
theorem B383837 : Blo 255820 383837 := bbase (se 3 (by rfl) ⟨71969, by rfl⟩ : syracuseStep 383837 = 143939) (by norm_num)
theorem B580445 : Blo 255820 580445 := bbase (se 3 (by rfl) ⟨108833, by rfl⟩ : syracuseStep 580445 = 217667) (by norm_num)
theorem B383861 : Blo 255820 383861 := bbase (se 5 (by rfl) ⟨17993, by rfl⟩ : syracuseStep 383861 = 35987) (by norm_num)
theorem B383885 : Blo 255820 383885 := bbase (se 3 (by rfl) ⟨71978, by rfl⟩ : syracuseStep 383885 = 143957) (by norm_num)
theorem B1235861 : Blo 255820 1235861 := bbase (se 6 (by rfl) ⟨28965, by rfl⟩ : syracuseStep 1235861 = 57931) (by norm_num)
theorem B842645 : Blo 255820 842645 := bbase (se 6 (by rfl) ⟨19749, by rfl⟩ : syracuseStep 842645 = 39499) (by norm_num)
theorem B383909 : Blo 255820 383909 := bbase (se 4 (by rfl) ⟨35991, by rfl⟩ : syracuseStep 383909 = 71983) (by norm_num)
theorem B580517 : Blo 255820 580517 := bbase (se 4 (by rfl) ⟨54423, by rfl⟩ : syracuseStep 580517 = 108847) (by norm_num)
theorem B383933 : Blo 255820 383933 := bbase (se 3 (by rfl) ⟨71987, by rfl⟩ : syracuseStep 383933 = 143975) (by norm_num)
theorem B383957 : Blo 255820 383957 := bbase (se 7 (by rfl) ⟨4499, by rfl⟩ : syracuseStep 383957 = 8999) (by norm_num)
theorem B383981 : Blo 255820 383981 := bbase (se 3 (by rfl) ⟨71996, by rfl⟩ : syracuseStep 383981 = 143993) (by norm_num)
theorem B580589 : Blo 255820 580589 := bbase (se 3 (by rfl) ⟨108860, by rfl⟩ : syracuseStep 580589 = 217721) (by norm_num)
theorem B384005 : Blo 255820 384005 := bbase (se 4 (by rfl) ⟨36000, by rfl⟩ : syracuseStep 384005 = 72001) (by norm_num)
theorem B384029 : Blo 255820 384029 := bbase (se 3 (by rfl) ⟨72005, by rfl⟩ : syracuseStep 384029 = 144011) (by norm_num)
theorem B384053 : Blo 255820 384053 := bbase (se 5 (by rfl) ⟨18002, by rfl⟩ : syracuseStep 384053 = 36005) (by norm_num)
theorem B580661 : Blo 255820 580661 := bbase (se 5 (by rfl) ⟨27218, by rfl⟩ : syracuseStep 580661 = 54437) (by norm_num)
theorem B384077 : Blo 255820 384077 := bbase (se 3 (by rfl) ⟨72014, by rfl⟩ : syracuseStep 384077 = 144029) (by norm_num)
theorem B384101 : Blo 255820 384101 := bbase (se 4 (by rfl) ⟨36009, by rfl⟩ : syracuseStep 384101 = 72019) (by norm_num)
theorem B384125 : Blo 255820 384125 := bbase (se 3 (by rfl) ⟨72023, by rfl⟩ : syracuseStep 384125 = 144047) (by norm_num)
theorem B580733 : Blo 255820 580733 := bbase (se 3 (by rfl) ⟨108887, by rfl⟩ : syracuseStep 580733 = 217775) (by norm_num)
theorem B384149 : Blo 255820 384149 := bbase (se 6 (by rfl) ⟨9003, by rfl⟩ : syracuseStep 384149 = 18007) (by norm_num)
theorem B1301669 : Blo 255820 1301669 := bbase (se 4 (by rfl) ⟨122031, by rfl⟩ : syracuseStep 1301669 = 244063) (by norm_num)
theorem B384173 : Blo 255820 384173 := bbase (se 3 (by rfl) ⟨72032, by rfl⟩ : syracuseStep 384173 = 144065) (by norm_num)
theorem B384197 : Blo 255820 384197 := bbase (se 4 (by rfl) ⟨36018, by rfl⟩ : syracuseStep 384197 = 72037) (by norm_num)
theorem B580805 : Blo 255820 580805 := bbase (se 4 (by rfl) ⟨54450, by rfl⟩ : syracuseStep 580805 = 108901) (by norm_num)
theorem B875717 : Blo 255820 875717 := bbase (se 4 (by rfl) ⟨82098, by rfl⟩ : syracuseStep 875717 = 164197) (by norm_num)
theorem B2186453 : Blo 255820 2186453 := bbase (se 7 (by rfl) ⟨25622, by rfl⟩ : syracuseStep 2186453 = 51245) (by norm_num)
theorem B384221 : Blo 255820 384221 := bbase (se 3 (by rfl) ⟨72041, by rfl⟩ : syracuseStep 384221 = 144083) (by norm_num)
theorem B384245 : Blo 255820 384245 := bbase (se 5 (by rfl) ⟨18011, by rfl⟩ : syracuseStep 384245 = 36023) (by norm_num)
theorem B384269 : Blo 255820 384269 := bbase (se 3 (by rfl) ⟨72050, by rfl⟩ : syracuseStep 384269 = 144101) (by norm_num)
theorem B580877 : Blo 255820 580877 := bbase (se 3 (by rfl) ⟨108914, by rfl⟩ : syracuseStep 580877 = 217829) (by norm_num)
theorem B384293 : Blo 255820 384293 := bbase (se 4 (by rfl) ⟨36027, by rfl⟩ : syracuseStep 384293 = 72055) (by norm_num)
theorem B843061 : Blo 255820 843061 := bbase (se 5 (by rfl) ⟨39518, by rfl⟩ : syracuseStep 843061 = 79037) (by norm_num)
theorem B384317 : Blo 255820 384317 := bbase (se 3 (by rfl) ⟨72059, by rfl⟩ : syracuseStep 384317 = 144119) (by norm_num)
theorem B384341 : Blo 255820 384341 := bbase (se 11 (by rfl) ⟨281, by rfl⟩ : syracuseStep 384341 = 563) (by norm_num)
theorem B580949 : Blo 255820 580949 := bbase (se 11 (by rfl) ⟨425, by rfl⟩ : syracuseStep 580949 = 851) (by norm_num)
theorem B384365 : Blo 255820 384365 := bbase (se 3 (by rfl) ⟨72068, by rfl⟩ : syracuseStep 384365 = 144137) (by norm_num)
theorem B384389 : Blo 255820 384389 := bbase (se 4 (by rfl) ⟨36036, by rfl⟩ : syracuseStep 384389 = 72073) (by norm_num)
theorem B5037461 : Blo 255820 5037461 := bbase (se 6 (by rfl) ⟨118065, by rfl⟩ : syracuseStep 5037461 = 236131) (by norm_num)
theorem B384413 : Blo 255820 384413 := bbase (se 3 (by rfl) ⟨72077, by rfl⟩ : syracuseStep 384413 = 144155) (by norm_num)
theorem B581021 : Blo 255820 581021 := bbase (se 3 (by rfl) ⟨108941, by rfl⟩ : syracuseStep 581021 = 217883) (by norm_num)
theorem B384437 : Blo 255820 384437 := bbase (se 5 (by rfl) ⟨18020, by rfl⟩ : syracuseStep 384437 = 36041) (by norm_num)
theorem B384461 : Blo 255820 384461 := bbase (se 3 (by rfl) ⟨72086, by rfl⟩ : syracuseStep 384461 = 144173) (by norm_num)
theorem B384485 : Blo 255820 384485 := bbase (se 4 (by rfl) ⟨36045, by rfl⟩ : syracuseStep 384485 = 72091) (by norm_num)
theorem B581093 : Blo 255820 581093 := bbase (se 4 (by rfl) ⟨54477, by rfl⟩ : syracuseStep 581093 = 108955) (by norm_num)
theorem B384509 : Blo 255820 384509 := bbase (se 3 (by rfl) ⟨72095, by rfl⟩ : syracuseStep 384509 = 144191) (by norm_num)
theorem B384533 : Blo 255820 384533 := bbase (se 6 (by rfl) ⟨9012, by rfl⟩ : syracuseStep 384533 = 18025) (by norm_num)
theorem B384557 : Blo 255820 384557 := bbase (se 3 (by rfl) ⟨72104, by rfl⟩ : syracuseStep 384557 = 144209) (by norm_num)
theorem B581165 : Blo 255820 581165 := bbase (se 3 (by rfl) ⟨108968, by rfl⟩ : syracuseStep 581165 = 217937) (by norm_num)
theorem B384581 : Blo 255820 384581 := bbase (se 4 (by rfl) ⟨36054, by rfl⟩ : syracuseStep 384581 = 72109) (by norm_num)
theorem B384605 : Blo 255820 384605 := bbase (se 3 (by rfl) ⟨72113, by rfl⟩ : syracuseStep 384605 = 144227) (by norm_num)
theorem B384629 : Blo 255820 384629 := bbase (se 5 (by rfl) ⟨18029, by rfl⟩ : syracuseStep 384629 = 36059) (by norm_num)
theorem B581237 : Blo 255820 581237 := bbase (se 5 (by rfl) ⟨27245, by rfl⟩ : syracuseStep 581237 = 54491) (by norm_num)
theorem B876149 : Blo 255820 876149 := bbase (se 5 (by rfl) ⟨41069, by rfl⟩ : syracuseStep 876149 = 82139) (by norm_num)
theorem B384653 : Blo 255820 384653 := bbase (se 3 (by rfl) ⟨72122, by rfl⟩ : syracuseStep 384653 = 144245) (by norm_num)
theorem B384677 : Blo 255820 384677 := bbase (se 4 (by rfl) ⟨36063, by rfl⟩ : syracuseStep 384677 = 72127) (by norm_num)
theorem B384701 : Blo 255820 384701 := bbase (se 3 (by rfl) ⟨72131, by rfl⟩ : syracuseStep 384701 = 144263) (by norm_num)
theorem B581309 : Blo 255820 581309 := bbase (se 3 (by rfl) ⟨108995, by rfl⟩ : syracuseStep 581309 = 217991) (by norm_num)
theorem B384725 : Blo 255820 384725 := bbase (se 7 (by rfl) ⟨4508, by rfl⟩ : syracuseStep 384725 = 9017) (by norm_num)
theorem B384749 : Blo 255820 384749 := bbase (se 3 (by rfl) ⟨72140, by rfl⟩ : syracuseStep 384749 = 144281) (by norm_num)
theorem B384773 : Blo 255820 384773 := bbase (se 4 (by rfl) ⟨36072, by rfl⟩ : syracuseStep 384773 = 72145) (by norm_num)
theorem B581381 : Blo 255820 581381 := bbase (se 4 (by rfl) ⟨54504, by rfl⟩ : syracuseStep 581381 = 109009) (by norm_num)
theorem B384797 : Blo 255820 384797 := bbase (se 3 (by rfl) ⟨72149, by rfl⟩ : syracuseStep 384797 = 144299) (by norm_num)
theorem B384821 : Blo 255820 384821 := bbase (se 5 (by rfl) ⟨18038, by rfl⟩ : syracuseStep 384821 = 36077) (by norm_num)
theorem B384845 : Blo 255820 384845 := bbase (se 3 (by rfl) ⟨72158, by rfl⟩ : syracuseStep 384845 = 144317) (by norm_num)
theorem B581453 : Blo 255820 581453 := bbase (se 3 (by rfl) ⟨109022, by rfl⟩ : syracuseStep 581453 = 218045) (by norm_num)
theorem B384869 : Blo 255820 384869 := bbase (se 4 (by rfl) ⟨36081, by rfl⟩ : syracuseStep 384869 = 72163) (by norm_num)
theorem B384893 : Blo 255820 384893 := bbase (se 3 (by rfl) ⟨72167, by rfl⟩ : syracuseStep 384893 = 144335) (by norm_num)
theorem B384917 : Blo 255820 384917 := bbase (se 6 (by rfl) ⟨9021, by rfl⟩ : syracuseStep 384917 = 18043) (by norm_num)
theorem B581525 : Blo 255820 581525 := bbase (se 6 (by rfl) ⟨13629, by rfl⟩ : syracuseStep 581525 = 27259) (by norm_num)
theorem B384941 : Blo 255820 384941 := bbase (se 3 (by rfl) ⟨72176, by rfl⟩ : syracuseStep 384941 = 144353) (by norm_num)
theorem B384965 : Blo 255820 384965 := bbase (se 4 (by rfl) ⟨36090, by rfl⟩ : syracuseStep 384965 = 72181) (by norm_num)
theorem B384989 : Blo 255820 384989 := bbase (se 3 (by rfl) ⟨72185, by rfl⟩ : syracuseStep 384989 = 144371) (by norm_num)
theorem B581597 : Blo 255820 581597 := bbase (se 3 (by rfl) ⟨109049, by rfl⟩ : syracuseStep 581597 = 218099) (by norm_num)
theorem B385013 : Blo 255820 385013 := bbase (se 5 (by rfl) ⟨18047, by rfl⟩ : syracuseStep 385013 = 36095) (by norm_num)
theorem B548869 : Blo 255820 548869 := bbase (se 4 (by rfl) ⟨51456, by rfl⟩ : syracuseStep 548869 = 102913) (by norm_num)
theorem B385037 : Blo 255820 385037 := bbase (se 3 (by rfl) ⟨72194, by rfl⟩ : syracuseStep 385037 = 144389) (by norm_num)
theorem B385061 : Blo 255820 385061 := bbase (se 4 (by rfl) ⟨36099, by rfl⟩ : syracuseStep 385061 = 72199) (by norm_num)
theorem B581669 : Blo 255820 581669 := bbase (se 4 (by rfl) ⟨54531, by rfl⟩ : syracuseStep 581669 = 109063) (by norm_num)
theorem B876581 : Blo 255820 876581 := bbase (se 4 (by rfl) ⟨82179, by rfl⟩ : syracuseStep 876581 = 164359) (by norm_num)
theorem B385085 : Blo 255820 385085 := bbase (se 3 (by rfl) ⟨72203, by rfl⟩ : syracuseStep 385085 = 144407) (by norm_num)
theorem B385109 : Blo 255820 385109 := bbase (se 8 (by rfl) ⟨2256, by rfl⟩ : syracuseStep 385109 = 4513) (by norm_num)
theorem B385133 : Blo 255820 385133 := bbase (se 3 (by rfl) ⟨72212, by rfl⟩ : syracuseStep 385133 = 144425) (by norm_num)
theorem B581741 : Blo 255820 581741 := bbase (se 3 (by rfl) ⟨109076, by rfl⟩ : syracuseStep 581741 = 218153) (by norm_num)
theorem B385157 : Blo 255820 385157 := bbase (se 4 (by rfl) ⟨36108, by rfl⟩ : syracuseStep 385157 = 72217) (by norm_num)
theorem B385181 : Blo 255820 385181 := bbase (se 3 (by rfl) ⟨72221, by rfl⟩ : syracuseStep 385181 = 144443) (by norm_num)
theorem B385205 : Blo 255820 385205 := bbase (se 5 (by rfl) ⟨18056, by rfl⟩ : syracuseStep 385205 = 36113) (by norm_num)
theorem B581813 : Blo 255820 581813 := bbase (se 5 (by rfl) ⟨27272, by rfl⟩ : syracuseStep 581813 = 54545) (by norm_num)
theorem B385229 : Blo 255820 385229 := bbase (se 3 (by rfl) ⟨72230, by rfl⟩ : syracuseStep 385229 = 144461) (by norm_num)
theorem B385253 : Blo 255820 385253 := bbase (se 4 (by rfl) ⟨36117, by rfl⟩ : syracuseStep 385253 = 72235) (by norm_num)
theorem B385277 : Blo 255820 385277 := bbase (se 3 (by rfl) ⟨72239, by rfl⟩ : syracuseStep 385277 = 144479) (by norm_num)
theorem B581885 : Blo 255820 581885 := bbase (se 3 (by rfl) ⟨109103, by rfl⟩ : syracuseStep 581885 = 218207) (by norm_num)
theorem B385301 : Blo 255820 385301 := bbase (se 6 (by rfl) ⟨9030, by rfl⟩ : syracuseStep 385301 = 18061) (by norm_num)
theorem B385325 : Blo 255820 385325 := bbase (se 3 (by rfl) ⟨72248, by rfl⟩ : syracuseStep 385325 = 144497) (by norm_num)
theorem B385349 : Blo 255820 385349 := bbase (se 4 (by rfl) ⟨36126, by rfl⟩ : syracuseStep 385349 = 72253) (by norm_num)
theorem B581957 : Blo 255820 581957 := bbase (se 4 (by rfl) ⟨54558, by rfl⟩ : syracuseStep 581957 = 109117) (by norm_num)
theorem B614749 : Blo 255820 614749 := bbase (se 3 (by rfl) ⟨115265, by rfl⟩ : syracuseStep 614749 = 230531) (by norm_num)
theorem B385373 : Blo 255820 385373 := bbase (se 3 (by rfl) ⟨72257, by rfl⟩ : syracuseStep 385373 = 144515) (by norm_num)
theorem B385397 : Blo 255820 385397 := bbase (se 5 (by rfl) ⟨18065, by rfl⟩ : syracuseStep 385397 = 36131) (by norm_num)
theorem B385421 : Blo 255820 385421 := bbase (se 3 (by rfl) ⟨72266, by rfl⟩ : syracuseStep 385421 = 144533) (by norm_num)
theorem B582029 : Blo 255820 582029 := bbase (se 3 (by rfl) ⟨109130, by rfl⟩ : syracuseStep 582029 = 218261) (by norm_num)
theorem B385445 : Blo 255820 385445 := bbase (se 4 (by rfl) ⟨36135, by rfl⟩ : syracuseStep 385445 = 72271) (by norm_num)
theorem B1302965 : Blo 255820 1302965 := bbase (se 5 (by rfl) ⟨61076, by rfl⟩ : syracuseStep 1302965 = 122153) (by norm_num)
theorem B385469 : Blo 255820 385469 := bbase (se 3 (by rfl) ⟨72275, by rfl⟩ : syracuseStep 385469 = 144551) (by norm_num)
theorem B385493 : Blo 255820 385493 := bbase (se 7 (by rfl) ⟨4517, by rfl⟩ : syracuseStep 385493 = 9035) (by norm_num)
theorem B582101 : Blo 255820 582101 := bbase (se 7 (by rfl) ⟨6821, by rfl⟩ : syracuseStep 582101 = 13643) (by norm_num)
theorem B385517 : Blo 255820 385517 := bbase (se 3 (by rfl) ⟨72284, by rfl⟩ : syracuseStep 385517 = 144569) (by norm_num)
theorem B1237493 : Blo 255820 1237493 := bbase (se 5 (by rfl) ⟨58007, by rfl⟩ : syracuseStep 1237493 = 116015) (by norm_num)
theorem B385541 : Blo 255820 385541 := bbase (se 4 (by rfl) ⟨36144, by rfl⟩ : syracuseStep 385541 = 72289) (by norm_num)
theorem B385565 : Blo 255820 385565 := bbase (se 3 (by rfl) ⟨72293, by rfl⟩ : syracuseStep 385565 = 144587) (by norm_num)
theorem B582173 : Blo 255820 582173 := bbase (se 3 (by rfl) ⟨109157, by rfl⟩ : syracuseStep 582173 = 218315) (by norm_num)
theorem B385589 : Blo 255820 385589 := bbase (se 5 (by rfl) ⟨18074, by rfl⟩ : syracuseStep 385589 = 36149) (by norm_num)
theorem B385613 : Blo 255820 385613 := bbase (se 3 (by rfl) ⟨72302, by rfl⟩ : syracuseStep 385613 = 144605) (by norm_num)
theorem B385637 : Blo 255820 385637 := bbase (se 4 (by rfl) ⟨36153, by rfl⟩ : syracuseStep 385637 = 72307) (by norm_num)
theorem B582245 : Blo 255820 582245 := bbase (se 4 (by rfl) ⟨54585, by rfl⟩ : syracuseStep 582245 = 109171) (by norm_num)
theorem B647797 : Blo 255820 647797 := bbase (se 5 (by rfl) ⟨30365, by rfl⟩ : syracuseStep 647797 = 60731) (by norm_num)
theorem B385661 : Blo 255820 385661 := bbase (se 3 (by rfl) ⟨72311, by rfl⟩ : syracuseStep 385661 = 144623) (by norm_num)
theorem B975509 : Blo 255820 975509 := bbase (se 6 (by rfl) ⟨22863, by rfl⟩ : syracuseStep 975509 = 45727) (by norm_num)
theorem B385685 : Blo 255820 385685 := bbase (se 6 (by rfl) ⟨9039, by rfl⟩ : syracuseStep 385685 = 18079) (by norm_num)
theorem B385709 : Blo 255820 385709 := bbase (se 3 (by rfl) ⟨72320, by rfl⟩ : syracuseStep 385709 = 144641) (by norm_num)
theorem B582317 : Blo 255820 582317 := bbase (se 3 (by rfl) ⟨109184, by rfl⟩ : syracuseStep 582317 = 218369) (by norm_num)
theorem B385733 : Blo 255820 385733 := bbase (se 4 (by rfl) ⟨36162, by rfl⟩ : syracuseStep 385733 = 72325) (by norm_num)
theorem B385757 : Blo 255820 385757 := bbase (se 3 (by rfl) ⟨72329, by rfl⟩ : syracuseStep 385757 = 144659) (by norm_num)
theorem B647909 : Blo 255820 647909 := bbase (se 4 (by rfl) ⟨60741, by rfl⟩ : syracuseStep 647909 = 121483) (by norm_num)
theorem B385781 : Blo 255820 385781 := bbase (se 5 (by rfl) ⟨18083, by rfl⟩ : syracuseStep 385781 = 36167) (by norm_num)
theorem B582389 : Blo 255820 582389 := bbase (se 5 (by rfl) ⟨27299, by rfl⟩ : syracuseStep 582389 = 54599) (by norm_num)
theorem B385805 : Blo 255820 385805 := bbase (se 3 (by rfl) ⟨72338, by rfl⟩ : syracuseStep 385805 = 144677) (by norm_num)
theorem B385829 : Blo 255820 385829 := bbase (se 4 (by rfl) ⟨36171, by rfl⟩ : syracuseStep 385829 = 72343) (by norm_num)
theorem B385853 : Blo 255820 385853 := bbase (se 3 (by rfl) ⟨72347, by rfl⟩ : syracuseStep 385853 = 144695) (by norm_num)
theorem B582461 : Blo 255820 582461 := bbase (se 3 (by rfl) ⟨109211, by rfl⟩ : syracuseStep 582461 = 218423) (by norm_num)
theorem B385877 : Blo 255820 385877 := bbase (se 9 (by rfl) ⟨1130, by rfl⟩ : syracuseStep 385877 = 2261) (by norm_num)
theorem B615269 : Blo 255820 615269 := bbase (se 4 (by rfl) ⟨57681, by rfl⟩ : syracuseStep 615269 = 115363) (by norm_num)
theorem B385901 : Blo 255820 385901 := bbase (se 3 (by rfl) ⟨72356, by rfl⟩ : syracuseStep 385901 = 144713) (by norm_num)
theorem B549757 : Blo 255820 549757 := bbase (se 3 (by rfl) ⟨103079, by rfl⟩ : syracuseStep 549757 = 206159) (by norm_num)
theorem B385925 : Blo 255820 385925 := bbase (se 4 (by rfl) ⟨36180, by rfl⟩ : syracuseStep 385925 = 72361) (by norm_num)
theorem B582533 : Blo 255820 582533 := bbase (se 4 (by rfl) ⟨54612, by rfl⟩ : syracuseStep 582533 = 109225) (by norm_num)
theorem B385949 : Blo 255820 385949 := bbase (se 3 (by rfl) ⟨72365, by rfl⟩ : syracuseStep 385949 = 144731) (by norm_num)
theorem B648101 : Blo 255820 648101 := bbase (se 4 (by rfl) ⟨60759, by rfl⟩ : syracuseStep 648101 = 121519) (by norm_num)
theorem B975797 : Blo 255820 975797 := bbase (se 5 (by rfl) ⟨45740, by rfl⟩ : syracuseStep 975797 = 91481) (by norm_num)
theorem B385973 : Blo 255820 385973 := bbase (se 5 (by rfl) ⟨18092, by rfl⟩ : syracuseStep 385973 = 36185) (by norm_num)
theorem B385997 : Blo 255820 385997 := bbase (se 3 (by rfl) ⟨72374, by rfl⟩ : syracuseStep 385997 = 144749) (by norm_num)
theorem B582605 : Blo 255820 582605 := bbase (se 3 (by rfl) ⟨109238, by rfl⟩ : syracuseStep 582605 = 218477) (by norm_num)
theorem B386021 : Blo 255820 386021 := bbase (se 4 (by rfl) ⟨36189, by rfl⟩ : syracuseStep 386021 = 72379) (by norm_num)
theorem B386045 : Blo 255820 386045 := bbase (se 3 (by rfl) ⟨72383, by rfl⟩ : syracuseStep 386045 = 144767) (by norm_num)
theorem B386069 : Blo 255820 386069 := bbase (se 6 (by rfl) ⟨9048, by rfl⟩ : syracuseStep 386069 = 18097) (by norm_num)
theorem B582677 : Blo 255820 582677 := bbase (se 6 (by rfl) ⟨13656, by rfl⟩ : syracuseStep 582677 = 27313) (by norm_num)
theorem B386093 : Blo 255820 386093 := bbase (se 3 (by rfl) ⟨72392, by rfl⟩ : syracuseStep 386093 = 144785) (by norm_num)
theorem B386117 : Blo 255820 386117 := bbase (se 4 (by rfl) ⟨36198, by rfl⟩ : syracuseStep 386117 = 72397) (by norm_num)
theorem B287833 : Blo 255820 287833 := bbase (se 2 (by rfl) ⟨107937, by rfl⟩ : syracuseStep 287833 = 215875) (by norm_num)
theorem B386141 : Blo 255820 386141 := bbase (se 3 (by rfl) ⟨72401, by rfl⟩ : syracuseStep 386141 = 144803) (by norm_num)
theorem B582749 : Blo 255820 582749 := bbase (se 3 (by rfl) ⟨109265, by rfl⟩ : syracuseStep 582749 = 218531) (by norm_num)
theorem B386165 : Blo 255820 386165 := bbase (se 5 (by rfl) ⟨18101, by rfl⟩ : syracuseStep 386165 = 36203) (by norm_num)
theorem B287869 : Blo 255820 287869 := bbase (se 3 (by rfl) ⟨53975, by rfl⟩ : syracuseStep 287869 = 107951) (by norm_num)
theorem B386189 : Blo 255820 386189 := bbase (se 3 (by rfl) ⟨72410, by rfl⟩ : syracuseStep 386189 = 144821) (by norm_num)
theorem B287905 : Blo 255820 287905 := bbase (se 2 (by rfl) ⟨107964, by rfl⟩ : syracuseStep 287905 = 215929) (by norm_num)
theorem B386213 : Blo 255820 386213 := bbase (se 4 (by rfl) ⟨36207, by rfl⟩ : syracuseStep 386213 = 72415) (by norm_num)
theorem B582821 : Blo 255820 582821 := bbase (se 4 (by rfl) ⟨54639, by rfl⟩ : syracuseStep 582821 = 109279) (by norm_num)
theorem B386237 : Blo 255820 386237 := bbase (se 3 (by rfl) ⟨72419, by rfl⟩ : syracuseStep 386237 = 144839) (by norm_num)
theorem B287941 : Blo 255820 287941 := bbase (se 4 (by rfl) ⟨26994, by rfl⟩ : syracuseStep 287941 = 53989) (by norm_num)
theorem B386261 : Blo 255820 386261 := bbase (se 7 (by rfl) ⟨4526, by rfl⟩ : syracuseStep 386261 = 9053) (by norm_num)
theorem B615653 : Blo 255820 615653 := bbase (se 4 (by rfl) ⟨57717, by rfl⟩ : syracuseStep 615653 = 115435) (by norm_num)
theorem B287977 : Blo 255820 287977 := bbase (se 2 (by rfl) ⟨107991, by rfl⟩ : syracuseStep 287977 = 215983) (by norm_num)
theorem B386285 : Blo 255820 386285 := bbase (se 3 (by rfl) ⟨72428, by rfl⟩ : syracuseStep 386285 = 144857) (by norm_num)
theorem B582893 : Blo 255820 582893 := bbase (se 3 (by rfl) ⟨109292, by rfl⟩ : syracuseStep 582893 = 218585) (by norm_num)
theorem B1860853 : Blo 255820 1860853 := bbase (se 5 (by rfl) ⟨87227, by rfl⟩ : syracuseStep 1860853 = 174455) (by norm_num)
theorem B648445 : Blo 255820 648445 := bbase (se 3 (by rfl) ⟨121583, by rfl⟩ : syracuseStep 648445 = 243167) (by norm_num)
theorem B386309 : Blo 255820 386309 := bbase (se 4 (by rfl) ⟨36216, by rfl⟩ : syracuseStep 386309 = 72433) (by norm_num)
theorem B288013 : Blo 255820 288013 := bbase (se 3 (by rfl) ⟨54002, by rfl⟩ : syracuseStep 288013 = 108005) (by norm_num)
theorem B615701 : Blo 255820 615701 := bbase (se 6 (by rfl) ⟨14430, by rfl⟩ : syracuseStep 615701 = 28861) (by norm_num)
theorem B615709 : Blo 255820 615709 := bbase (se 3 (by rfl) ⟨115445, by rfl⟩ : syracuseStep 615709 = 230891) (by norm_num)
theorem B386333 : Blo 255820 386333 := bbase (se 3 (by rfl) ⟨72437, by rfl⟩ : syracuseStep 386333 = 144875) (by norm_num)
theorem B288049 : Blo 255820 288049 := bbase (se 2 (by rfl) ⟨108018, by rfl⟩ : syracuseStep 288049 = 216037) (by norm_num)
theorem B386357 : Blo 255820 386357 := bbase (se 5 (by rfl) ⟨18110, by rfl⟩ : syracuseStep 386357 = 36221) (by norm_num)
theorem B582965 : Blo 255820 582965 := bbase (se 5 (by rfl) ⟨27326, by rfl⟩ : syracuseStep 582965 = 54653) (by norm_num)
theorem B386381 : Blo 255820 386381 := bbase (se 3 (by rfl) ⟨72446, by rfl⟩ : syracuseStep 386381 = 144893) (by norm_num)
theorem B288085 : Blo 255820 288085 := bbase (se 12 (by rfl) ⟨105, by rfl⟩ : syracuseStep 288085 = 211) (by norm_num)
theorem B386405 : Blo 255820 386405 := bbase (se 4 (by rfl) ⟨36225, by rfl⟩ : syracuseStep 386405 = 72451) (by norm_num)
theorem B648557 : Blo 255820 648557 := bbase (se 3 (by rfl) ⟨121604, by rfl⟩ : syracuseStep 648557 = 243209) (by norm_num)
theorem B550253 : Blo 255820 550253 := bbase (se 3 (by rfl) ⟨103172, by rfl⟩ : syracuseStep 550253 = 206345) (by norm_num)
theorem B288121 : Blo 255820 288121 := bbase (se 2 (by rfl) ⟨108045, by rfl⟩ : syracuseStep 288121 = 216091) (by norm_num)
theorem B386429 : Blo 255820 386429 := bbase (se 3 (by rfl) ⟨72455, by rfl⟩ : syracuseStep 386429 = 144911) (by norm_num)
theorem B583037 : Blo 255820 583037 := bbase (se 3 (by rfl) ⟨109319, by rfl⟩ : syracuseStep 583037 = 218639) (by norm_num)
theorem B386453 : Blo 255820 386453 := bbase (se 6 (by rfl) ⟨9057, by rfl⟩ : syracuseStep 386453 = 18115) (by norm_num)
theorem B288157 : Blo 255820 288157 := bbase (se 3 (by rfl) ⟨54029, by rfl⟩ : syracuseStep 288157 = 108059) (by norm_num)
theorem B386477 : Blo 255820 386477 := bbase (se 3 (by rfl) ⟨72464, by rfl⟩ : syracuseStep 386477 = 144929) (by norm_num)
theorem B288193 : Blo 255820 288193 := bbase (se 2 (by rfl) ⟨108072, by rfl⟩ : syracuseStep 288193 = 216145) (by norm_num)
theorem B386501 : Blo 255820 386501 := bbase (se 4 (by rfl) ⟨36234, by rfl⟩ : syracuseStep 386501 = 72469) (by norm_num)
theorem B583109 : Blo 255820 583109 := bbase (se 4 (by rfl) ⟨54666, by rfl⟩ : syracuseStep 583109 = 109333) (by norm_num)
theorem B386525 : Blo 255820 386525 := bbase (se 3 (by rfl) ⟨72473, by rfl⟩ : syracuseStep 386525 = 144947) (by norm_num)
theorem B288229 : Blo 255820 288229 := bbase (se 4 (by rfl) ⟨27021, by rfl⟩ : syracuseStep 288229 = 54043) (by norm_num)
theorem B386549 : Blo 255820 386549 := bbase (se 5 (by rfl) ⟨18119, by rfl⟩ : syracuseStep 386549 = 36239) (by norm_num)
theorem B288265 : Blo 255820 288265 := bbase (se 2 (by rfl) ⟨108099, by rfl⟩ : syracuseStep 288265 = 216199) (by norm_num)
theorem B386573 : Blo 255820 386573 := bbase (se 3 (by rfl) ⟨72482, by rfl⟩ : syracuseStep 386573 = 144965) (by norm_num)
theorem B583181 : Blo 255820 583181 := bbase (se 3 (by rfl) ⟨109346, by rfl⟩ : syracuseStep 583181 = 218693) (by norm_num)
theorem B386597 : Blo 255820 386597 := bbase (se 4 (by rfl) ⟨36243, by rfl⟩ : syracuseStep 386597 = 72487) (by norm_num)
theorem B288301 : Blo 255820 288301 := bbase (se 3 (by rfl) ⟨54056, by rfl⟩ : syracuseStep 288301 = 108113) (by norm_num)
theorem B648749 : Blo 255820 648749 := bbase (se 3 (by rfl) ⟨121640, by rfl⟩ : syracuseStep 648749 = 243281) (by norm_num)
theorem B386621 : Blo 255820 386621 := bbase (se 3 (by rfl) ⟨72491, by rfl⟩ : syracuseStep 386621 = 144983) (by norm_num)
theorem B288337 : Blo 255820 288337 := bbase (se 2 (by rfl) ⟨108126, by rfl⟩ : syracuseStep 288337 = 216253) (by norm_num)
theorem B386645 : Blo 255820 386645 := bbase (se 8 (by rfl) ⟨2265, by rfl⟩ : syracuseStep 386645 = 4531) (by norm_num)
theorem B583253 : Blo 255820 583253 := bbase (se 8 (by rfl) ⟨3417, by rfl⟩ : syracuseStep 583253 = 6835) (by norm_num)
theorem B386669 : Blo 255820 386669 := bbase (se 3 (by rfl) ⟨72500, by rfl⟩ : syracuseStep 386669 = 145001) (by norm_num)
theorem B288373 : Blo 255820 288373 := bbase (se 5 (by rfl) ⟨13517, by rfl⟩ : syracuseStep 288373 = 27035) (by norm_num)
theorem B386693 : Blo 255820 386693 := bbase (se 4 (by rfl) ⟨36252, by rfl⟩ : syracuseStep 386693 = 72505) (by norm_num)
theorem B1402517 : Blo 255820 1402517 := bbase (se 6 (by rfl) ⟨32871, by rfl⟩ : syracuseStep 1402517 = 65743) (by norm_num)
theorem B288409 : Blo 255820 288409 := bbase (se 2 (by rfl) ⟨108153, by rfl⟩ : syracuseStep 288409 = 216307) (by norm_num)
theorem B386717 : Blo 255820 386717 := bbase (se 3 (by rfl) ⟨72509, by rfl⟩ : syracuseStep 386717 = 145019) (by norm_num)
theorem B583325 : Blo 255820 583325 := bbase (se 3 (by rfl) ⟨109373, by rfl⟩ : syracuseStep 583325 = 218747) (by norm_num)
theorem B386741 : Blo 255820 386741 := bbase (se 5 (by rfl) ⟨18128, by rfl⟩ : syracuseStep 386741 = 36257) (by norm_num)
theorem B288445 : Blo 255820 288445 := bbase (se 3 (by rfl) ⟨54083, by rfl⟩ : syracuseStep 288445 = 108167) (by norm_num)
theorem B1304261 : Blo 255820 1304261 := bbase (se 4 (by rfl) ⟨122274, by rfl⟩ : syracuseStep 1304261 = 244549) (by norm_num)
theorem B386765 : Blo 255820 386765 := bbase (se 3 (by rfl) ⟨72518, by rfl⟩ : syracuseStep 386765 = 145037) (by norm_num)
theorem B779989 : Blo 255820 779989 := bbase (se 7 (by rfl) ⟨9140, by rfl⟩ : syracuseStep 779989 = 18281) (by norm_num)
theorem B288481 : Blo 255820 288481 := bbase (se 2 (by rfl) ⟨108180, by rfl⟩ : syracuseStep 288481 = 216361) (by norm_num)
theorem B386789 : Blo 255820 386789 := bbase (se 4 (by rfl) ⟨36261, by rfl⟩ : syracuseStep 386789 = 72523) (by norm_num)
theorem B583397 : Blo 255820 583397 := bbase (se 4 (by rfl) ⟨54693, by rfl⟩ : syracuseStep 583397 = 109387) (by norm_num)
theorem B1107701 : Blo 255820 1107701 := bbase (se 5 (by rfl) ⟨51923, by rfl⟩ : syracuseStep 1107701 = 103847) (by norm_num)
theorem B386813 : Blo 255820 386813 := bbase (se 3 (by rfl) ⟨72527, by rfl⟩ : syracuseStep 386813 = 145055) (by norm_num)
theorem B288517 : Blo 255820 288517 := bbase (se 4 (by rfl) ⟨27048, by rfl⟩ : syracuseStep 288517 = 54097) (by norm_num)
theorem B386837 : Blo 255820 386837 := bbase (se 6 (by rfl) ⟨9066, by rfl⟩ : syracuseStep 386837 = 18133) (by norm_num)
theorem B288553 : Blo 255820 288553 := bbase (se 2 (by rfl) ⟨108207, by rfl⟩ : syracuseStep 288553 = 216415) (by norm_num)
theorem B386861 : Blo 255820 386861 := bbase (se 3 (by rfl) ⟨72536, by rfl⟩ : syracuseStep 386861 = 145073) (by norm_num)
theorem B583469 : Blo 255820 583469 := bbase (se 3 (by rfl) ⟨109400, by rfl⟩ : syracuseStep 583469 = 218801) (by norm_num)
theorem B386885 : Blo 255820 386885 := bbase (se 4 (by rfl) ⟨36270, by rfl⟩ : syracuseStep 386885 = 72541) (by norm_num)
theorem B288589 : Blo 255820 288589 := bbase (se 3 (by rfl) ⟨54110, by rfl⟩ : syracuseStep 288589 = 108221) (by norm_num)
theorem B386909 : Blo 255820 386909 := bbase (se 3 (by rfl) ⟨72545, by rfl⟩ : syracuseStep 386909 = 145091) (by norm_num)
theorem B288625 : Blo 255820 288625 := bbase (se 2 (by rfl) ⟨108234, by rfl⟩ : syracuseStep 288625 = 216469) (by norm_num)
theorem B386933 : Blo 255820 386933 := bbase (se 5 (by rfl) ⟨18137, by rfl⟩ : syracuseStep 386933 = 36275) (by norm_num)
theorem B583541 : Blo 255820 583541 := bbase (se 5 (by rfl) ⟨27353, by rfl⟩ : syracuseStep 583541 = 54707) (by norm_num)
theorem B649093 : Blo 255820 649093 := bbase (se 4 (by rfl) ⟨60852, by rfl⟩ : syracuseStep 649093 = 121705) (by norm_num)
theorem B714629 : Blo 255820 714629 := bbase (se 4 (by rfl) ⟨66996, by rfl⟩ : syracuseStep 714629 = 133993) (by norm_num)
theorem B386957 : Blo 255820 386957 := bbase (se 3 (by rfl) ⟨72554, by rfl⟩ : syracuseStep 386957 = 145109) (by norm_num)
theorem B288661 : Blo 255820 288661 := bbase (se 6 (by rfl) ⟨6765, by rfl⟩ : syracuseStep 288661 = 13531) (by norm_num)
theorem B386981 : Blo 255820 386981 := bbase (se 4 (by rfl) ⟨36279, by rfl⟩ : syracuseStep 386981 = 72559) (by norm_num)
theorem B288697 : Blo 255820 288697 := bbase (se 2 (by rfl) ⟨108261, by rfl⟩ : syracuseStep 288697 = 216523) (by norm_num)
theorem B387005 : Blo 255820 387005 := bbase (se 3 (by rfl) ⟨72563, by rfl⟩ : syracuseStep 387005 = 145127) (by norm_num)
theorem B583613 : Blo 255820 583613 := bbase (se 3 (by rfl) ⟨109427, by rfl⟩ : syracuseStep 583613 = 218855) (by norm_num)
theorem B387029 : Blo 255820 387029 := bbase (se 7 (by rfl) ⟨4535, by rfl⟩ : syracuseStep 387029 = 9071) (by norm_num)
theorem B288733 : Blo 255820 288733 := bbase (se 3 (by rfl) ⟨54137, by rfl⟩ : syracuseStep 288733 = 108275) (by norm_num)
theorem B387053 : Blo 255820 387053 := bbase (se 3 (by rfl) ⟨72572, by rfl⟩ : syracuseStep 387053 = 145145) (by norm_num)
theorem B649205 : Blo 255820 649205 := bbase (se 5 (by rfl) ⟨30431, by rfl⟩ : syracuseStep 649205 = 60863) (by norm_num)
theorem B288769 : Blo 255820 288769 := bbase (se 2 (by rfl) ⟨108288, by rfl⟩ : syracuseStep 288769 = 216577) (by norm_num)
theorem B387077 : Blo 255820 387077 := bbase (se 4 (by rfl) ⟨36288, by rfl⟩ : syracuseStep 387077 = 72577) (by norm_num)
theorem B583685 : Blo 255820 583685 := bbase (se 4 (by rfl) ⟨54720, by rfl⟩ : syracuseStep 583685 = 109441) (by norm_num)
theorem B1107989 : Blo 255820 1107989 := bbase (se 6 (by rfl) ⟨25968, by rfl⟩ : syracuseStep 1107989 = 51937) (by norm_num)
theorem B387101 : Blo 255820 387101 := bbase (se 3 (by rfl) ⟨72581, by rfl⟩ : syracuseStep 387101 = 145163) (by norm_num)
theorem B288805 : Blo 255820 288805 := bbase (se 4 (by rfl) ⟨27075, by rfl⟩ : syracuseStep 288805 = 54151) (by norm_num)
theorem B387125 : Blo 255820 387125 := bbase (se 5 (by rfl) ⟨18146, by rfl⟩ : syracuseStep 387125 = 36293) (by norm_num)
theorem B288841 : Blo 255820 288841 := bbase (se 2 (by rfl) ⟨108315, by rfl⟩ : syracuseStep 288841 = 216631) (by norm_num)
theorem B387149 : Blo 255820 387149 := bbase (se 3 (by rfl) ⟨72590, by rfl⟩ : syracuseStep 387149 = 145181) (by norm_num)
theorem B583757 : Blo 255820 583757 := bbase (se 3 (by rfl) ⟨109454, by rfl⟩ : syracuseStep 583757 = 218909) (by norm_num)
theorem B976981 : Blo 255820 976981 := bbase (se 8 (by rfl) ⟨5724, by rfl⟩ : syracuseStep 976981 = 11449) (by norm_num)
theorem B387173 : Blo 255820 387173 := bbase (se 4 (by rfl) ⟨36297, by rfl⟩ : syracuseStep 387173 = 72595) (by norm_num)
theorem B288877 : Blo 255820 288877 := bbase (se 3 (by rfl) ⟨54164, by rfl⟩ : syracuseStep 288877 = 108329) (by norm_num)
theorem B2189429 : Blo 255820 2189429 := bbase (se 5 (by rfl) ⟨102629, by rfl⟩ : syracuseStep 2189429 = 205259) (by norm_num)
theorem B387197 : Blo 255820 387197 := bbase (se 3 (by rfl) ⟨72599, by rfl⟩ : syracuseStep 387197 = 145199) (by norm_num)
theorem B288913 : Blo 255820 288913 := bbase (se 2 (by rfl) ⟨108342, by rfl⟩ : syracuseStep 288913 = 216685) (by norm_num)
theorem B387221 : Blo 255820 387221 := bbase (se 6 (by rfl) ⟨9075, by rfl⟩ : syracuseStep 387221 = 18151) (by norm_num)
theorem B583829 : Blo 255820 583829 := bbase (se 6 (by rfl) ⟨13683, by rfl⟩ : syracuseStep 583829 = 27367) (by norm_num)
theorem B387245 : Blo 255820 387245 := bbase (se 3 (by rfl) ⟨72608, by rfl⟩ : syracuseStep 387245 = 145217) (by norm_num)
theorem B649397 : Blo 255820 649397 := bbase (se 5 (by rfl) ⟨30440, by rfl⟩ : syracuseStep 649397 = 60881) (by norm_num)
theorem B288949 : Blo 255820 288949 := bbase (se 5 (by rfl) ⟨13544, by rfl⟩ : syracuseStep 288949 = 27089) (by norm_num)
theorem B387269 : Blo 255820 387269 := bbase (se 4 (by rfl) ⟨36306, by rfl⟩ : syracuseStep 387269 = 72613) (by norm_num)
theorem B551117 : Blo 255820 551117 := bbase (se 3 (by rfl) ⟨103334, by rfl⟩ : syracuseStep 551117 = 206669) (by norm_num)
theorem B288985 : Blo 255820 288985 := bbase (se 2 (by rfl) ⟨108369, by rfl⟩ : syracuseStep 288985 = 216739) (by norm_num)
theorem B387293 : Blo 255820 387293 := bbase (se 3 (by rfl) ⟨72617, by rfl⟩ : syracuseStep 387293 = 145235) (by norm_num)
theorem B583901 : Blo 255820 583901 := bbase (se 3 (by rfl) ⟨109481, by rfl⟩ : syracuseStep 583901 = 218963) (by norm_num)
theorem B387317 : Blo 255820 387317 := bbase (se 5 (by rfl) ⟨18155, by rfl⟩ : syracuseStep 387317 = 36311) (by norm_num)
theorem B289021 : Blo 255820 289021 := bbase (se 3 (by rfl) ⟨54191, by rfl⟩ : syracuseStep 289021 = 108383) (by norm_num)
theorem B616709 : Blo 255820 616709 := bbase (se 4 (by rfl) ⟨57816, by rfl⟩ : syracuseStep 616709 = 115633) (by norm_num)
theorem B387341 : Blo 255820 387341 := bbase (se 3 (by rfl) ⟨72626, by rfl⟩ : syracuseStep 387341 = 145253) (by norm_num)
theorem B289057 : Blo 255820 289057 := bbase (se 2 (by rfl) ⟨108396, by rfl⟩ : syracuseStep 289057 = 216793) (by norm_num)
theorem B387365 : Blo 255820 387365 := bbase (se 4 (by rfl) ⟨36315, by rfl⟩ : syracuseStep 387365 = 72631) (by norm_num)
theorem B583973 : Blo 255820 583973 := bbase (se 4 (by rfl) ⟨54747, by rfl⟩ : syracuseStep 583973 = 109495) (by norm_num)
theorem B387389 : Blo 255820 387389 := bbase (se 3 (by rfl) ⟨72635, by rfl⟩ : syracuseStep 387389 = 145271) (by norm_num)
theorem B289093 : Blo 255820 289093 := bbase (se 4 (by rfl) ⟨27102, by rfl⟩ : syracuseStep 289093 = 54205) (by norm_num)
theorem B387413 : Blo 255820 387413 := bbase (se 10 (by rfl) ⟨567, by rfl⟩ : syracuseStep 387413 = 1135) (by norm_num)
theorem B551261 : Blo 255820 551261 := bbase (se 3 (by rfl) ⟨103361, by rfl⟩ : syracuseStep 551261 = 206723) (by norm_num)
theorem B289129 : Blo 255820 289129 := bbase (se 2 (by rfl) ⟨108423, by rfl⟩ : syracuseStep 289129 = 216847) (by norm_num)
theorem B387437 : Blo 255820 387437 := bbase (se 3 (by rfl) ⟨72644, by rfl⟩ : syracuseStep 387437 = 145289) (by norm_num)
theorem B584045 : Blo 255820 584045 := bbase (se 3 (by rfl) ⟨109508, by rfl⟩ : syracuseStep 584045 = 219017) (by norm_num)
theorem B977285 : Blo 255820 977285 := bbase (se 4 (by rfl) ⟨91620, by rfl⟩ : syracuseStep 977285 = 183241) (by norm_num)
theorem B387461 : Blo 255820 387461 := bbase (se 4 (by rfl) ⟨36324, by rfl⟩ : syracuseStep 387461 = 72649) (by norm_num)
theorem B289165 : Blo 255820 289165 := bbase (se 3 (by rfl) ⟨54218, by rfl⟩ : syracuseStep 289165 = 108437) (by norm_num)
theorem B387485 : Blo 255820 387485 := bbase (se 3 (by rfl) ⟨72653, by rfl⟩ : syracuseStep 387485 = 145307) (by norm_num)
theorem B289201 : Blo 255820 289201 := bbase (se 2 (by rfl) ⟨108450, by rfl⟩ : syracuseStep 289201 = 216901) (by norm_num)
theorem B387509 : Blo 255820 387509 := bbase (se 5 (by rfl) ⟨18164, by rfl⟩ : syracuseStep 387509 = 36329) (by norm_num)
theorem B584117 : Blo 255820 584117 := bbase (se 5 (by rfl) ⟨27380, by rfl⟩ : syracuseStep 584117 = 54761) (by norm_num)
theorem B616901 : Blo 255820 616901 := bbase (se 4 (by rfl) ⟨57834, by rfl⟩ : syracuseStep 616901 = 115669) (by norm_num)
theorem B387533 : Blo 255820 387533 := bbase (se 3 (by rfl) ⟨72662, by rfl⟩ : syracuseStep 387533 = 145325) (by norm_num)
theorem B289237 : Blo 255820 289237 := bbase (se 7 (by rfl) ⟨3389, by rfl⟩ : syracuseStep 289237 = 6779) (by norm_num)
theorem B387557 : Blo 255820 387557 := bbase (se 4 (by rfl) ⟨36333, by rfl⟩ : syracuseStep 387557 = 72667) (by norm_num)
theorem B289273 : Blo 255820 289273 := bbase (se 2 (by rfl) ⟨108477, by rfl⟩ : syracuseStep 289273 = 216955) (by norm_num)
theorem B387581 : Blo 255820 387581 := bbase (se 3 (by rfl) ⟨72671, by rfl⟩ : syracuseStep 387581 = 145343) (by norm_num)
theorem B584189 : Blo 255820 584189 := bbase (se 3 (by rfl) ⟨109535, by rfl⟩ : syracuseStep 584189 = 219071) (by norm_num)
theorem B649741 : Blo 255820 649741 := bbase (se 3 (by rfl) ⟨121826, by rfl⟩ : syracuseStep 649741 = 243653) (by norm_num)
theorem B485909 : Blo 255820 485909 := bbase (se 6 (by rfl) ⟨11388, by rfl⟩ : syracuseStep 485909 = 22777) (by norm_num)
theorem B387605 : Blo 255820 387605 := bbase (se 6 (by rfl) ⟨9084, by rfl⟩ : syracuseStep 387605 = 18169) (by norm_num)
theorem B289309 : Blo 255820 289309 := bbase (se 3 (by rfl) ⟨54245, by rfl⟩ : syracuseStep 289309 = 108491) (by norm_num)
theorem B387629 : Blo 255820 387629 := bbase (se 3 (by rfl) ⟨72680, by rfl⟩ : syracuseStep 387629 = 145361) (by norm_num)
theorem B289345 : Blo 255820 289345 := bbase (se 2 (by rfl) ⟨108504, by rfl⟩ : syracuseStep 289345 = 217009) (by norm_num)
theorem B387653 : Blo 255820 387653 := bbase (se 4 (by rfl) ⟨36342, by rfl⟩ : syracuseStep 387653 = 72685) (by norm_num)
theorem B584261 : Blo 255820 584261 := bbase (se 4 (by rfl) ⟨54774, by rfl⟩ : syracuseStep 584261 = 109549) (by norm_num)
theorem B387677 : Blo 255820 387677 := bbase (se 3 (by rfl) ⟨72689, by rfl⟩ : syracuseStep 387677 = 145379) (by norm_num)
theorem B289381 : Blo 255820 289381 := bbase (se 4 (by rfl) ⟨27129, by rfl⟩ : syracuseStep 289381 = 54259) (by norm_num)
theorem B387701 : Blo 255820 387701 := bbase (se 5 (by rfl) ⟨18173, by rfl⟩ : syracuseStep 387701 = 36347) (by norm_num)
theorem B649853 : Blo 255820 649853 := bbase (se 3 (by rfl) ⟨121847, by rfl⟩ : syracuseStep 649853 = 243695) (by norm_num)
theorem B289417 : Blo 255820 289417 := bbase (se 2 (by rfl) ⟨108531, by rfl⟩ : syracuseStep 289417 = 217063) (by norm_num)
theorem B387725 : Blo 255820 387725 := bbase (se 3 (by rfl) ⟨72698, by rfl⟩ : syracuseStep 387725 = 145397) (by norm_num)
theorem B584333 : Blo 255820 584333 := bbase (se 3 (by rfl) ⟨109562, by rfl⟩ : syracuseStep 584333 = 219125) (by norm_num)
theorem B387749 : Blo 255820 387749 := bbase (se 4 (by rfl) ⟨36351, by rfl⟩ : syracuseStep 387749 = 72703) (by norm_num)
theorem B289453 : Blo 255820 289453 := bbase (se 3 (by rfl) ⟨54272, by rfl⟩ : syracuseStep 289453 = 108545) (by norm_num)
theorem B387773 : Blo 255820 387773 := bbase (se 3 (by rfl) ⟨72707, by rfl⟩ : syracuseStep 387773 = 145415) (by norm_num)
theorem B289489 : Blo 255820 289489 := bbase (se 2 (by rfl) ⟨108558, by rfl⟩ : syracuseStep 289489 = 217117) (by norm_num)
theorem B2943701 : Blo 255820 2943701 := bbase (se 7 (by rfl) ⟨34496, by rfl⟩ : syracuseStep 2943701 = 68993) (by norm_num)
theorem B387797 : Blo 255820 387797 := bbase (se 7 (by rfl) ⟨4544, by rfl⟩ : syracuseStep 387797 = 9089) (by norm_num)
theorem B584405 : Blo 255820 584405 := bbase (se 7 (by rfl) ⟨6848, by rfl⟩ : syracuseStep 584405 = 13697) (by norm_num)
theorem B387821 : Blo 255820 387821 := bbase (se 3 (by rfl) ⟨72716, by rfl⟩ : syracuseStep 387821 = 145433) (by norm_num)
theorem B289525 : Blo 255820 289525 := bbase (se 5 (by rfl) ⟨13571, by rfl⟩ : syracuseStep 289525 = 27143) (by norm_num)
theorem B387845 : Blo 255820 387845 := bbase (se 4 (by rfl) ⟨36360, by rfl⟩ : syracuseStep 387845 = 72721) (by norm_num)
theorem B1108741 : Blo 255820 1108741 := bbase (se 4 (by rfl) ⟨103944, by rfl⟩ : syracuseStep 1108741 = 207889) (by norm_num)
theorem B289561 : Blo 255820 289561 := bbase (se 2 (by rfl) ⟨108585, by rfl⟩ : syracuseStep 289561 = 217171) (by norm_num)
theorem B387869 : Blo 255820 387869 := bbase (se 3 (by rfl) ⟨72725, by rfl⟩ : syracuseStep 387869 = 145451) (by norm_num)
theorem B584477 : Blo 255820 584477 := bbase (se 3 (by rfl) ⟨109589, by rfl⟩ : syracuseStep 584477 = 219179) (by norm_num)
theorem B387893 : Blo 255820 387893 := bbase (se 5 (by rfl) ⟨18182, by rfl⟩ : syracuseStep 387893 = 36365) (by norm_num)
theorem B650045 : Blo 255820 650045 := bbase (se 3 (by rfl) ⟨121883, by rfl⟩ : syracuseStep 650045 = 243767) (by norm_num)
theorem B289597 : Blo 255820 289597 := bbase (se 3 (by rfl) ⟨54299, by rfl⟩ : syracuseStep 289597 = 108599) (by norm_num)
theorem B387917 : Blo 255820 387917 := bbase (se 3 (by rfl) ⟨72734, by rfl⟩ : syracuseStep 387917 = 145469) (by norm_num)
theorem B289633 : Blo 255820 289633 := bbase (se 2 (by rfl) ⟨108612, by rfl⟩ : syracuseStep 289633 = 217225) (by norm_num)
theorem B387941 : Blo 255820 387941 := bbase (se 4 (by rfl) ⟨36369, by rfl⟩ : syracuseStep 387941 = 72739) (by norm_num)
theorem B584549 : Blo 255820 584549 := bbase (se 4 (by rfl) ⟨54801, by rfl⟩ : syracuseStep 584549 = 109603) (by norm_num)
theorem B387965 : Blo 255820 387965 := bbase (se 3 (by rfl) ⟨72743, by rfl⟩ : syracuseStep 387965 = 145487) (by norm_num)
theorem B289669 : Blo 255820 289669 := bbase (se 4 (by rfl) ⟨27156, by rfl⟩ : syracuseStep 289669 = 54313) (by norm_num)
theorem B387989 : Blo 255820 387989 := bbase (se 6 (by rfl) ⟨9093, by rfl⟩ : syracuseStep 387989 = 18187) (by norm_num)
theorem B289705 : Blo 255820 289705 := bbase (se 2 (by rfl) ⟨108639, by rfl⟩ : syracuseStep 289705 = 217279) (by norm_num)
theorem B388013 : Blo 255820 388013 := bbase (se 3 (by rfl) ⟨72752, by rfl⟩ : syracuseStep 388013 = 145505) (by norm_num)
theorem B388037 : Blo 255820 388037 := bbase (se 4 (by rfl) ⟨36378, by rfl⟩ : syracuseStep 388037 = 72757) (by norm_num)
theorem B289741 : Blo 255820 289741 := bbase (se 3 (by rfl) ⟨54326, by rfl⟩ : syracuseStep 289741 = 108653) (by norm_num)
theorem B1305557 : Blo 255820 1305557 := bbase (se 7 (by rfl) ⟨15299, by rfl⟩ : syracuseStep 1305557 = 30599) (by norm_num)
theorem B388061 : Blo 255820 388061 := bbase (se 3 (by rfl) ⟨72761, by rfl⟩ : syracuseStep 388061 = 145523) (by norm_num)
theorem B289777 : Blo 255820 289777 := bbase (se 2 (by rfl) ⟨108666, by rfl⟩ : syracuseStep 289777 = 217333) (by norm_num)
theorem B388085 : Blo 255820 388085 := bbase (se 5 (by rfl) ⟨18191, by rfl⟩ : syracuseStep 388085 = 36383) (by norm_num)
theorem B388109 : Blo 255820 388109 := bbase (se 3 (by rfl) ⟨72770, by rfl⟩ : syracuseStep 388109 = 145541) (by norm_num)
theorem B289813 : Blo 255820 289813 := bbase (se 6 (by rfl) ⟨6792, by rfl⟩ : syracuseStep 289813 = 13585) (by norm_num)
theorem B388133 : Blo 255820 388133 := bbase (se 4 (by rfl) ⟨36387, by rfl⟩ : syracuseStep 388133 = 72775) (by norm_num)
theorem B289849 : Blo 255820 289849 := bbase (se 2 (by rfl) ⟨108693, by rfl⟩ : syracuseStep 289849 = 217387) (by norm_num)
theorem B388157 : Blo 255820 388157 := bbase (se 3 (by rfl) ⟨72779, by rfl⟩ : syracuseStep 388157 = 145559) (by norm_num)
theorem B552005 : Blo 255820 552005 := bbase (se 4 (by rfl) ⟨51750, by rfl⟩ : syracuseStep 552005 = 103501) (by norm_num)
theorem B388181 : Blo 255820 388181 := bbase (se 8 (by rfl) ⟨2274, by rfl⟩ : syracuseStep 388181 = 4549) (by norm_num)
theorem B289885 : Blo 255820 289885 := bbase (se 3 (by rfl) ⟨54353, by rfl⟩ : syracuseStep 289885 = 108707) (by norm_num)
theorem B388205 : Blo 255820 388205 := bbase (se 3 (by rfl) ⟨72788, by rfl⟩ : syracuseStep 388205 = 145577) (by norm_num)
theorem B289921 : Blo 255820 289921 := bbase (se 2 (by rfl) ⟨108720, by rfl⟩ : syracuseStep 289921 = 217441) (by norm_num)
theorem B388229 : Blo 255820 388229 := bbase (se 4 (by rfl) ⟨36396, by rfl⟩ : syracuseStep 388229 = 72793) (by norm_num)
theorem B650389 : Blo 255820 650389 := bbase (se 6 (by rfl) ⟨15243, by rfl⟩ : syracuseStep 650389 = 30487) (by norm_num)
theorem B388253 : Blo 255820 388253 := bbase (se 3 (by rfl) ⟨72797, by rfl⟩ : syracuseStep 388253 = 145595) (by norm_num)
theorem B289957 : Blo 255820 289957 := bbase (se 4 (by rfl) ⟨27183, by rfl⟩ : syracuseStep 289957 = 54367) (by norm_num)
theorem B388277 : Blo 255820 388277 := bbase (se 5 (by rfl) ⟨18200, by rfl⟩ : syracuseStep 388277 = 36401) (by norm_num)
theorem B289993 : Blo 255820 289993 := bbase (se 2 (by rfl) ⟨108747, by rfl⟩ : syracuseStep 289993 = 217495) (by norm_num)
theorem B388301 : Blo 255820 388301 := bbase (se 3 (by rfl) ⟨72806, by rfl⟩ : syracuseStep 388301 = 145613) (by norm_num)
theorem B388325 : Blo 255820 388325 := bbase (se 4 (by rfl) ⟨36405, by rfl⟩ : syracuseStep 388325 = 72811) (by norm_num)
theorem B290029 : Blo 255820 290029 := bbase (se 3 (by rfl) ⟨54380, by rfl⟩ : syracuseStep 290029 = 108761) (by norm_num)
theorem B388349 : Blo 255820 388349 := bbase (se 3 (by rfl) ⟨72815, by rfl⟩ : syracuseStep 388349 = 145631) (by norm_num)
theorem B486661 : Blo 255820 486661 := bbase (se 4 (by rfl) ⟨45624, by rfl⟩ : syracuseStep 486661 = 91249) (by norm_num)
theorem B650501 : Blo 255820 650501 := bbase (se 4 (by rfl) ⟨60984, by rfl⟩ : syracuseStep 650501 = 121969) (by norm_num)
theorem B290065 : Blo 255820 290065 := bbase (se 2 (by rfl) ⟨108774, by rfl⟩ : syracuseStep 290065 = 217549) (by norm_num)
theorem B388373 : Blo 255820 388373 := bbase (se 6 (by rfl) ⟨9102, by rfl⟩ : syracuseStep 388373 = 18205) (by norm_num)
theorem B388397 : Blo 255820 388397 := bbase (se 3 (by rfl) ⟨72824, by rfl⟩ : syracuseStep 388397 = 145649) (by norm_num)
theorem B290101 : Blo 255820 290101 := bbase (se 5 (by rfl) ⟨13598, by rfl⟩ : syracuseStep 290101 = 27197) (by norm_num)
theorem B388421 : Blo 255820 388421 := bbase (se 4 (by rfl) ⟨36414, by rfl⟩ : syracuseStep 388421 = 72829) (by norm_num)
theorem B290137 : Blo 255820 290137 := bbase (se 2 (by rfl) ⟨108801, by rfl⟩ : syracuseStep 290137 = 217603) (by norm_num)
theorem B388445 : Blo 255820 388445 := bbase (se 3 (by rfl) ⟨72833, by rfl⟩ : syracuseStep 388445 = 145667) (by norm_num)
theorem B781669 : Blo 255820 781669 := bbase (se 4 (by rfl) ⟨73281, by rfl⟩ : syracuseStep 781669 = 146563) (by norm_num)
theorem B388469 : Blo 255820 388469 := bbase (se 5 (by rfl) ⟨18209, by rfl⟩ : syracuseStep 388469 = 36419) (by norm_num)
theorem B290173 : Blo 255820 290173 := bbase (se 3 (by rfl) ⟨54407, by rfl⟩ : syracuseStep 290173 = 108815) (by norm_num)
theorem B388493 : Blo 255820 388493 := bbase (se 3 (by rfl) ⟨72842, by rfl⟩ : syracuseStep 388493 = 145685) (by norm_num)
theorem B486805 : Blo 255820 486805 := bbase (se 6 (by rfl) ⟨11409, by rfl⟩ : syracuseStep 486805 = 22819) (by norm_num)
theorem B290209 : Blo 255820 290209 := bbase (se 2 (by rfl) ⟨108828, by rfl⟩ : syracuseStep 290209 = 217657) (by norm_num)
theorem B388517 : Blo 255820 388517 := bbase (se 4 (by rfl) ⟨36423, by rfl⟩ : syracuseStep 388517 = 72847) (by norm_num)
theorem B388541 : Blo 255820 388541 := bbase (se 3 (by rfl) ⟨72851, by rfl⟩ : syracuseStep 388541 = 145703) (by norm_num)
theorem B650693 : Blo 255820 650693 := bbase (se 4 (by rfl) ⟨61002, by rfl⟩ : syracuseStep 650693 = 122005) (by norm_num)
theorem B290245 : Blo 255820 290245 := bbase (se 4 (by rfl) ⟨27210, by rfl⟩ : syracuseStep 290245 = 54421) (by norm_num)
theorem B388565 : Blo 255820 388565 := bbase (se 7 (by rfl) ⟨4553, by rfl⟩ : syracuseStep 388565 = 9107) (by norm_num)
theorem B749029 : Blo 255820 749029 := bbase (se 4 (by rfl) ⟨70221, by rfl⟩ : syracuseStep 749029 = 140443) (by norm_num)
theorem B1109477 : Blo 255820 1109477 := bbase (se 4 (by rfl) ⟨104013, by rfl⟩ : syracuseStep 1109477 = 208027) (by norm_num)
theorem B290281 : Blo 255820 290281 := bbase (se 2 (by rfl) ⟨108855, by rfl⟩ : syracuseStep 290281 = 217711) (by norm_num)
theorem B388589 : Blo 255820 388589 := bbase (se 3 (by rfl) ⟨72860, by rfl⟩ : syracuseStep 388589 = 145721) (by norm_num)
theorem B421373 : Blo 255820 421373 := bbase (se 3 (by rfl) ⟨79007, by rfl⟩ : syracuseStep 421373 = 158015) (by norm_num)
theorem B388613 : Blo 255820 388613 := bbase (se 4 (by rfl) ⟨36432, by rfl⟩ : syracuseStep 388613 = 72865) (by norm_num)
theorem B290317 : Blo 255820 290317 := bbase (se 3 (by rfl) ⟨54434, by rfl⟩ : syracuseStep 290317 = 108869) (by norm_num)
theorem B388637 : Blo 255820 388637 := bbase (se 3 (by rfl) ⟨72869, by rfl⟩ : syracuseStep 388637 = 145739) (by norm_num)
theorem B290353 : Blo 255820 290353 := bbase (se 2 (by rfl) ⟨108882, by rfl⟩ : syracuseStep 290353 = 217765) (by norm_num)
theorem B486965 : Blo 255820 486965 := bbase (se 5 (by rfl) ⟨22826, by rfl⟩ : syracuseStep 486965 = 45653) (by norm_num)
theorem B388661 : Blo 255820 388661 := bbase (se 5 (by rfl) ⟨18218, by rfl⟩ : syracuseStep 388661 = 36437) (by norm_num)
theorem B355909 : Blo 255820 355909 := bbase (se 4 (by rfl) ⟨33366, by rfl⟩ : syracuseStep 355909 = 66733) (by norm_num)
theorem B388685 : Blo 255820 388685 := bbase (se 3 (by rfl) ⟨72878, by rfl⟩ : syracuseStep 388685 = 145757) (by norm_num)
theorem B290389 : Blo 255820 290389 := bbase (se 8 (by rfl) ⟨1701, by rfl⟩ : syracuseStep 290389 = 3403) (by norm_num)
theorem B388709 : Blo 255820 388709 := bbase (se 4 (by rfl) ⟨36441, by rfl⟩ : syracuseStep 388709 = 72883) (by norm_num)
theorem B290425 : Blo 255820 290425 := bbase (se 2 (by rfl) ⟨108909, by rfl⟩ : syracuseStep 290425 = 217819) (by norm_num)
theorem B388733 : Blo 255820 388733 := bbase (se 3 (by rfl) ⟨72887, by rfl⟩ : syracuseStep 388733 = 145775) (by norm_num)
theorem B388757 : Blo 255820 388757 := bbase (se 6 (by rfl) ⟨9111, by rfl⟩ : syracuseStep 388757 = 18223) (by norm_num)
theorem B290461 : Blo 255820 290461 := bbase (se 3 (by rfl) ⟨54461, by rfl⟩ : syracuseStep 290461 = 108923) (by norm_num)
theorem B388781 : Blo 255820 388781 := bbase (se 3 (by rfl) ⟨72896, by rfl⟩ : syracuseStep 388781 = 145793) (by norm_num)
theorem B290497 : Blo 255820 290497 := bbase (se 2 (by rfl) ⟨108936, by rfl⟩ : syracuseStep 290497 = 217873) (by norm_num)
theorem B487109 : Blo 255820 487109 := bbase (se 4 (by rfl) ⟨45666, by rfl⟩ : syracuseStep 487109 = 91333) (by norm_num)
theorem B585413 : Blo 255820 585413 := bbase (se 4 (by rfl) ⟨54882, by rfl⟩ : syracuseStep 585413 = 109765) (by norm_num)
theorem B388805 : Blo 255820 388805 := bbase (se 4 (by rfl) ⟨36450, by rfl⟩ : syracuseStep 388805 = 72901) (by norm_num)
theorem B388829 : Blo 255820 388829 := bbase (se 3 (by rfl) ⟨72905, by rfl⟩ : syracuseStep 388829 = 145811) (by norm_num)
theorem B290533 : Blo 255820 290533 := bbase (se 4 (by rfl) ⟨27237, by rfl⟩ : syracuseStep 290533 = 54475) (by norm_num)
theorem B388853 : Blo 255820 388853 := bbase (se 5 (by rfl) ⟨18227, by rfl⟩ : syracuseStep 388853 = 36455) (by norm_num)
theorem B290569 : Blo 255820 290569 := bbase (se 2 (by rfl) ⟨108963, by rfl⟩ : syracuseStep 290569 = 217927) (by norm_num)
theorem B388877 : Blo 255820 388877 := bbase (se 3 (by rfl) ⟨72914, by rfl⟩ : syracuseStep 388877 = 145829) (by norm_num)
theorem B651037 : Blo 255820 651037 := bbase (se 3 (by rfl) ⟨122069, by rfl⟩ : syracuseStep 651037 = 244139) (by norm_num)
theorem B388901 : Blo 255820 388901 := bbase (se 4 (by rfl) ⟨36459, by rfl⟩ : syracuseStep 388901 = 72919) (by norm_num)
theorem B290605 : Blo 255820 290605 := bbase (se 3 (by rfl) ⟨54488, by rfl⟩ : syracuseStep 290605 = 108977) (by norm_num)
theorem B552757 : Blo 255820 552757 := bbase (se 5 (by rfl) ⟨25910, by rfl⟩ : syracuseStep 552757 = 51821) (by norm_num)
theorem B388925 : Blo 255820 388925 := bbase (se 3 (by rfl) ⟨72923, by rfl⟩ : syracuseStep 388925 = 145847) (by norm_num)
theorem B290641 : Blo 255820 290641 := bbase (se 2 (by rfl) ⟨108990, by rfl⟩ : syracuseStep 290641 = 217981) (by norm_num)
theorem B585557 : Blo 255820 585557 := bbase (se 9 (by rfl) ⟨1715, by rfl⟩ : syracuseStep 585557 = 3431) (by norm_num)
theorem B388949 : Blo 255820 388949 := bbase (se 9 (by rfl) ⟨1139, by rfl⟩ : syracuseStep 388949 = 2279) (by norm_num)
theorem B388973 : Blo 255820 388973 := bbase (se 3 (by rfl) ⟨72932, by rfl⟩ : syracuseStep 388973 = 145865) (by norm_num)
theorem B290677 : Blo 255820 290677 := bbase (se 5 (by rfl) ⟨13625, by rfl⟩ : syracuseStep 290677 = 27251) (by norm_num)
theorem B388997 : Blo 255820 388997 := bbase (se 4 (by rfl) ⟨36468, by rfl⟩ : syracuseStep 388997 = 72937) (by norm_num)
theorem B651149 : Blo 255820 651149 := bbase (se 3 (by rfl) ⟨122090, by rfl⟩ : syracuseStep 651149 = 244181) (by norm_num)
theorem B290713 : Blo 255820 290713 := bbase (se 2 (by rfl) ⟨109017, by rfl⟩ : syracuseStep 290713 = 218035) (by norm_num)
theorem B389021 : Blo 255820 389021 := bbase (se 3 (by rfl) ⟨72941, by rfl⟩ : syracuseStep 389021 = 145883) (by norm_num)
theorem B389045 : Blo 255820 389045 := bbase (se 5 (by rfl) ⟨18236, by rfl⟩ : syracuseStep 389045 = 36473) (by norm_num)
theorem B290749 : Blo 255820 290749 := bbase (se 3 (by rfl) ⟨54515, by rfl⟩ : syracuseStep 290749 = 109031) (by norm_num)
theorem B552901 : Blo 255820 552901 := bbase (se 4 (by rfl) ⟨51834, by rfl⟩ : syracuseStep 552901 = 103669) (by norm_num)
theorem B389069 : Blo 255820 389069 := bbase (se 3 (by rfl) ⟨72950, by rfl⟩ : syracuseStep 389069 = 145901) (by norm_num)
theorem B290785 : Blo 255820 290785 := bbase (se 2 (by rfl) ⟨109044, by rfl⟩ : syracuseStep 290785 = 218089) (by norm_num)
theorem B487397 : Blo 255820 487397 := bbase (se 4 (by rfl) ⟨45693, by rfl⟩ : syracuseStep 487397 = 91387) (by norm_num)
theorem B389093 : Blo 255820 389093 := bbase (se 4 (by rfl) ⟨36477, by rfl⟩ : syracuseStep 389093 = 72955) (by norm_num)
theorem B389117 : Blo 255820 389117 := bbase (se 3 (by rfl) ⟨72959, by rfl⟩ : syracuseStep 389117 = 145919) (by norm_num)
theorem B290821 : Blo 255820 290821 := bbase (se 4 (by rfl) ⟨27264, by rfl⟩ : syracuseStep 290821 = 54529) (by norm_num)
theorem B389141 : Blo 255820 389141 := bbase (se 6 (by rfl) ⟨9120, by rfl⟩ : syracuseStep 389141 = 18241) (by norm_num)
theorem B290857 : Blo 255820 290857 := bbase (se 2 (by rfl) ⟨109071, by rfl⟩ : syracuseStep 290857 = 218143) (by norm_num)
theorem B389165 : Blo 255820 389165 := bbase (se 3 (by rfl) ⟨72968, by rfl⟩ : syracuseStep 389165 = 145937) (by norm_num)
theorem B389189 : Blo 255820 389189 := bbase (se 4 (by rfl) ⟨36486, by rfl⟩ : syracuseStep 389189 = 72973) (by norm_num)
theorem B651341 : Blo 255820 651341 := bbase (se 3 (by rfl) ⟨122126, by rfl⟩ : syracuseStep 651341 = 244253) (by norm_num)
theorem B290893 : Blo 255820 290893 := bbase (se 3 (by rfl) ⟨54542, by rfl⟩ : syracuseStep 290893 = 109085) (by norm_num)
theorem B2093141 : Blo 255820 2093141 := bbase (se 8 (by rfl) ⟨12264, by rfl⟩ : syracuseStep 2093141 = 24529) (by norm_num)
theorem B389213 : Blo 255820 389213 := bbase (se 3 (by rfl) ⟨72977, by rfl⟩ : syracuseStep 389213 = 145955) (by norm_num)
theorem B290929 : Blo 255820 290929 := bbase (se 2 (by rfl) ⟨109098, by rfl⟩ : syracuseStep 290929 = 218197) (by norm_num)
theorem B389237 : Blo 255820 389237 := bbase (se 5 (by rfl) ⟨18245, by rfl⟩ : syracuseStep 389237 = 36491) (by norm_num)
theorem B487549 : Blo 255820 487549 := bbase (se 3 (by rfl) ⟨91415, by rfl⟩ : syracuseStep 487549 = 182831) (by norm_num)
theorem B389261 : Blo 255820 389261 := bbase (se 3 (by rfl) ⟨72986, by rfl⟩ : syracuseStep 389261 = 145973) (by norm_num)
theorem B290965 : Blo 255820 290965 := bbase (se 6 (by rfl) ⟨6819, by rfl⟩ : syracuseStep 290965 = 13639) (by norm_num)
theorem B389285 : Blo 255820 389285 := bbase (se 4 (by rfl) ⟨36495, by rfl⟩ : syracuseStep 389285 = 72991) (by norm_num)
theorem B291001 : Blo 255820 291001 := bbase (se 2 (by rfl) ⟨109125, by rfl⟩ : syracuseStep 291001 = 218251) (by norm_num)
theorem B389309 : Blo 255820 389309 := bbase (se 3 (by rfl) ⟨72995, by rfl⟩ : syracuseStep 389309 = 145991) (by norm_num)
theorem B323777 : Blo 255820 323777 := bbase (se 2 (by rfl) ⟨121416, by rfl⟩ : syracuseStep 323777 = 242833) (by norm_num)
theorem B389333 : Blo 255820 389333 := bbase (se 7 (by rfl) ⟨4562, by rfl⟩ : syracuseStep 389333 = 9125) (by norm_num)
theorem B291037 : Blo 255820 291037 := bbase (se 3 (by rfl) ⟨54569, by rfl⟩ : syracuseStep 291037 = 109139) (by norm_num)
theorem B1306853 : Blo 255820 1306853 := bbase (se 4 (by rfl) ⟨122517, by rfl⟩ : syracuseStep 1306853 = 245035) (by norm_num)
theorem B389357 : Blo 255820 389357 := bbase (se 3 (by rfl) ⟨73004, by rfl⟩ : syracuseStep 389357 = 146009) (by norm_num)
theorem B323833 : Blo 255820 323833 := bbase (se 2 (by rfl) ⟨121437, by rfl⟩ : syracuseStep 323833 = 242875) (by norm_num)
theorem B291073 : Blo 255820 291073 := bbase (se 2 (by rfl) ⟨109152, by rfl⟩ : syracuseStep 291073 = 218305) (by norm_num)
theorem B389381 : Blo 255820 389381 := bbase (se 4 (by rfl) ⟨36504, by rfl⟩ : syracuseStep 389381 = 73009) (by norm_num)
theorem B389405 : Blo 255820 389405 := bbase (se 3 (by rfl) ⟨73013, by rfl⟩ : syracuseStep 389405 = 146027) (by norm_num)
theorem B291109 : Blo 255820 291109 := bbase (se 4 (by rfl) ⟨27291, by rfl⟩ : syracuseStep 291109 = 54583) (by norm_num)
theorem B389429 : Blo 255820 389429 := bbase (se 5 (by rfl) ⟨18254, by rfl⟩ : syracuseStep 389429 = 36509) (by norm_num)
theorem B553277 : Blo 255820 553277 := bbase (se 3 (by rfl) ⟨103739, by rfl⟩ : syracuseStep 553277 = 207479) (by norm_num)
theorem B291145 : Blo 255820 291145 := bbase (se 2 (by rfl) ⟨109179, by rfl⟩ : syracuseStep 291145 = 218359) (by norm_num)
theorem B389453 : Blo 255820 389453 := bbase (se 3 (by rfl) ⟨73022, by rfl⟩ : syracuseStep 389453 = 146045) (by norm_num)
theorem B323929 : Blo 255820 323929 := bbase (se 2 (by rfl) ⟨121473, by rfl⟩ : syracuseStep 323929 = 242947) (by norm_num)
theorem B618853 : Blo 255820 618853 := bbase (se 4 (by rfl) ⟨58017, by rfl⟩ : syracuseStep 618853 = 116035) (by norm_num)
theorem B389477 : Blo 255820 389477 := bbase (se 4 (by rfl) ⟨36513, by rfl⟩ : syracuseStep 389477 = 73027) (by norm_num)
theorem B291181 : Blo 255820 291181 := bbase (se 3 (by rfl) ⟨54596, by rfl⟩ : syracuseStep 291181 = 109193) (by norm_num)
theorem B389501 : Blo 255820 389501 := bbase (se 3 (by rfl) ⟨73031, by rfl⟩ : syracuseStep 389501 = 146063) (by norm_num)
theorem B291217 : Blo 255820 291217 := bbase (se 2 (by rfl) ⟨109206, by rfl⟩ : syracuseStep 291217 = 218413) (by norm_num)
theorem B389525 : Blo 255820 389525 := bbase (se 6 (by rfl) ⟨9129, by rfl⟩ : syracuseStep 389525 = 18259) (by norm_num)
theorem B651685 : Blo 255820 651685 := bbase (se 4 (by rfl) ⟨61095, by rfl⟩ : syracuseStep 651685 = 122191) (by norm_num)
theorem B487853 : Blo 255820 487853 := bbase (se 3 (by rfl) ⟨91472, by rfl⟩ : syracuseStep 487853 = 182945) (by norm_num)
theorem B389549 : Blo 255820 389549 := bbase (se 3 (by rfl) ⟨73040, by rfl⟩ : syracuseStep 389549 = 146081) (by norm_num)
theorem B389557 : Blo 255820 389557 := bbase (se 5 (by rfl) ⟨18260, by rfl⟩ : syracuseStep 389557 = 36521) (by norm_num)
theorem B291253 : Blo 255820 291253 := bbase (se 5 (by rfl) ⟨13652, by rfl⟩ : syracuseStep 291253 = 27305) (by norm_num)
theorem B979397 : Blo 255820 979397 := bbase (se 4 (by rfl) ⟨91818, by rfl⟩ : syracuseStep 979397 = 183637) (by norm_num)
theorem B389573 : Blo 255820 389573 := bbase (se 4 (by rfl) ⟨36522, by rfl⟩ : syracuseStep 389573 = 73045) (by norm_num)
theorem B291289 : Blo 255820 291289 := bbase (se 2 (by rfl) ⟨109233, by rfl⟩ : syracuseStep 291289 = 218467) (by norm_num)
theorem B389597 : Blo 255820 389597 := bbase (se 3 (by rfl) ⟨73049, by rfl⟩ : syracuseStep 389597 = 146099) (by norm_num)
theorem B389621 : Blo 255820 389621 := bbase (se 5 (by rfl) ⟨18263, by rfl⟩ : syracuseStep 389621 = 36527) (by norm_num)
theorem B291325 : Blo 255820 291325 := bbase (se 3 (by rfl) ⟨54623, by rfl⟩ : syracuseStep 291325 = 109247) (by norm_num)
theorem B324101 : Blo 255820 324101 := bbase (se 4 (by rfl) ⟨30384, by rfl⟩ : syracuseStep 324101 = 60769) (by norm_num)
theorem B389645 : Blo 255820 389645 := bbase (se 3 (by rfl) ⟨73058, by rfl⟩ : syracuseStep 389645 = 146117) (by norm_num)
theorem B651797 : Blo 255820 651797 := bbase (se 6 (by rfl) ⟨15276, by rfl⟩ : syracuseStep 651797 = 30553) (by norm_num)
theorem B291361 : Blo 255820 291361 := bbase (se 2 (by rfl) ⟨109260, by rfl⟩ : syracuseStep 291361 = 218521) (by norm_num)
theorem B389669 : Blo 255820 389669 := bbase (se 4 (by rfl) ⟨36531, by rfl⟩ : syracuseStep 389669 = 73063) (by norm_num)
theorem B324157 : Blo 255820 324157 := bbase (se 3 (by rfl) ⟨60779, by rfl⟩ : syracuseStep 324157 = 121559) (by norm_num)
theorem B389693 : Blo 255820 389693 := bbase (se 3 (by rfl) ⟨73067, by rfl⟩ : syracuseStep 389693 = 146135) (by norm_num)
theorem B291397 : Blo 255820 291397 := bbase (se 4 (by rfl) ⟨27318, by rfl⟩ : syracuseStep 291397 = 54637) (by norm_num)
theorem B389717 : Blo 255820 389717 := bbase (se 8 (by rfl) ⟨2283, by rfl⟩ : syracuseStep 389717 = 4567) (by norm_num)
theorem B291433 : Blo 255820 291433 := bbase (se 2 (by rfl) ⟨109287, by rfl⟩ : syracuseStep 291433 = 218575) (by norm_num)
theorem B291469 : Blo 255820 291469 := bbase (se 3 (by rfl) ⟨54650, by rfl⟩ : syracuseStep 291469 = 109301) (by norm_num)
theorem B324253 : Blo 255820 324253 := bbase (se 3 (by rfl) ⟨60797, by rfl⟩ : syracuseStep 324253 = 121595) (by norm_num)
theorem B553645 : Blo 255820 553645 := bbase (se 3 (by rfl) ⟨103808, by rfl⟩ : syracuseStep 553645 = 207617) (by norm_num)
theorem B291505 : Blo 255820 291505 := bbase (se 2 (by rfl) ⟨109314, by rfl⟩ : syracuseStep 291505 = 218629) (by norm_num)
theorem B651989 : Blo 255820 651989 := bbase (se 7 (by rfl) ⟨7640, by rfl⟩ : syracuseStep 651989 = 15281) (by norm_num)
theorem B291541 : Blo 255820 291541 := bbase (se 7 (by rfl) ⟨3416, by rfl⟩ : syracuseStep 291541 = 6833) (by norm_num)
theorem B979685 : Blo 255820 979685 := bbase (se 4 (by rfl) ⟨91845, by rfl⟩ : syracuseStep 979685 = 183691) (by norm_num)
theorem B291577 : Blo 255820 291577 := bbase (se 2 (by rfl) ⟨109341, by rfl⟩ : syracuseStep 291577 = 218683) (by norm_num)
theorem B291613 : Blo 255820 291613 := bbase (se 3 (by rfl) ⟨54677, by rfl⟩ : syracuseStep 291613 = 109355) (by norm_num)
theorem B291649 : Blo 255820 291649 := bbase (se 2 (by rfl) ⟨109368, by rfl⟩ : syracuseStep 291649 = 218737) (by norm_num)
theorem B324425 : Blo 255820 324425 := bbase (se 2 (by rfl) ⟨121659, by rfl⟩ : syracuseStep 324425 = 243319) (by norm_num)
theorem B291685 : Blo 255820 291685 := bbase (se 4 (by rfl) ⟨27345, by rfl⟩ : syracuseStep 291685 = 54691) (by norm_num)
theorem B324481 : Blo 255820 324481 := bbase (se 2 (by rfl) ⟨121680, by rfl⟩ : syracuseStep 324481 = 243361) (by norm_num)
theorem B291721 : Blo 255820 291721 := bbase (se 2 (by rfl) ⟨109395, by rfl⟩ : syracuseStep 291721 = 218791) (by norm_num)
theorem B291757 : Blo 255820 291757 := bbase (se 3 (by rfl) ⟨54704, by rfl⟩ : syracuseStep 291757 = 109409) (by norm_num)
theorem B291793 : Blo 255820 291793 := bbase (se 2 (by rfl) ⟨109422, by rfl⟩ : syracuseStep 291793 = 218845) (by norm_num)
theorem B324577 : Blo 255820 324577 := bbase (se 2 (by rfl) ⟨121716, by rfl⟩ : syracuseStep 324577 = 243433) (by norm_num)
theorem B291829 : Blo 255820 291829 := bbase (se 5 (by rfl) ⟨13679, by rfl⟩ : syracuseStep 291829 = 27359) (by norm_num)
theorem B291865 : Blo 255820 291865 := bbase (se 2 (by rfl) ⟨109449, by rfl⟩ : syracuseStep 291865 = 218899) (by norm_num)
theorem B652333 : Blo 255820 652333 := bbase (se 3 (by rfl) ⟨122312, by rfl⟩ : syracuseStep 652333 = 244625) (by norm_num)
theorem B291901 : Blo 255820 291901 := bbase (se 3 (by rfl) ⟨54731, by rfl⟩ : syracuseStep 291901 = 109463) (by norm_num)
theorem B291937 : Blo 255820 291937 := bbase (se 2 (by rfl) ⟨109476, by rfl⟩ : syracuseStep 291937 = 218953) (by norm_num)
theorem B291973 : Blo 255820 291973 := bbase (se 4 (by rfl) ⟨27372, by rfl⟩ : syracuseStep 291973 = 54745) (by norm_num)
theorem B324749 : Blo 255820 324749 := bbase (se 3 (by rfl) ⟨60890, by rfl⟩ : syracuseStep 324749 = 121781) (by norm_num)
theorem B488605 : Blo 255820 488605 := bbase (se 3 (by rfl) ⟨91613, by rfl⟩ : syracuseStep 488605 = 183227) (by norm_num)
theorem B652445 : Blo 255820 652445 := bbase (se 3 (by rfl) ⟨122333, by rfl⟩ : syracuseStep 652445 = 244667) (by norm_num)
theorem B292009 : Blo 255820 292009 := bbase (se 2 (by rfl) ⟨109503, by rfl⟩ : syracuseStep 292009 = 219007) (by norm_num)
theorem B324805 : Blo 255820 324805 := bbase (se 4 (by rfl) ⟨30450, by rfl⟩ : syracuseStep 324805 = 60901) (by norm_num)
theorem B292045 : Blo 255820 292045 := bbase (se 3 (by rfl) ⟨54758, by rfl⟩ : syracuseStep 292045 = 109517) (by norm_num)
theorem B292081 : Blo 255820 292081 := bbase (se 2 (by rfl) ⟨109530, by rfl⟩ : syracuseStep 292081 = 219061) (by norm_num)
theorem B292117 : Blo 255820 292117 := bbase (se 6 (by rfl) ⟨6846, by rfl⟩ : syracuseStep 292117 = 13693) (by norm_num)
theorem B619805 : Blo 255820 619805 := bbase (se 3 (by rfl) ⟨116213, by rfl⟩ : syracuseStep 619805 = 232427) (by norm_num)
theorem B324901 : Blo 255820 324901 := bbase (se 4 (by rfl) ⟨30459, by rfl⟩ : syracuseStep 324901 = 60919) (by norm_num)
theorem B488749 : Blo 255820 488749 := bbase (se 3 (by rfl) ⟨91640, by rfl⟩ : syracuseStep 488749 = 183281) (by norm_num)
theorem B292153 : Blo 255820 292153 := bbase (se 2 (by rfl) ⟨109557, by rfl⟩ : syracuseStep 292153 = 219115) (by norm_num)
theorem B619861 : Blo 255820 619861 := bbase (se 13 (by rfl) ⟨113, by rfl⟩ : syracuseStep 619861 = 227) (by norm_num)
theorem B652637 : Blo 255820 652637 := bbase (se 3 (by rfl) ⟨122369, by rfl⟩ : syracuseStep 652637 = 244739) (by norm_num)
theorem B292189 : Blo 255820 292189 := bbase (se 3 (by rfl) ⟨54785, by rfl⟩ : syracuseStep 292189 = 109571) (by norm_num)
theorem B521581 : Blo 255820 521581 := bbase (se 3 (by rfl) ⟨97796, by rfl⟩ : syracuseStep 521581 = 195593) (by norm_num)
theorem B292225 : Blo 255820 292225 := bbase (se 2 (by rfl) ⟨109584, by rfl⟩ : syracuseStep 292225 = 219169) (by norm_num)
theorem B292261 : Blo 255820 292261 := bbase (se 4 (by rfl) ⟨27399, by rfl⟩ : syracuseStep 292261 = 54799) (by norm_num)
theorem B292297 : Blo 255820 292297 := bbase (se 2 (by rfl) ⟨109611, by rfl⟩ : syracuseStep 292297 = 219223) (by norm_num)
theorem B488909 : Blo 255820 488909 := bbase (se 3 (by rfl) ⟨91670, by rfl⟩ : syracuseStep 488909 = 183341) (by norm_num)
theorem B325073 : Blo 255820 325073 := bbase (se 2 (by rfl) ⟨121902, by rfl⟩ : syracuseStep 325073 = 243805) (by norm_num)
theorem B1308149 : Blo 255820 1308149 := bbase (se 5 (by rfl) ⟨61319, by rfl⟩ : syracuseStep 1308149 = 122639) (by norm_num)
theorem B325129 : Blo 255820 325129 := bbase (se 2 (by rfl) ⟨121923, by rfl⟩ : syracuseStep 325129 = 243847) (by norm_num)
theorem B751141 : Blo 255820 751141 := bbase (se 4 (by rfl) ⟨70419, by rfl⟩ : syracuseStep 751141 = 140839) (by norm_num)
theorem B292405 : Blo 255820 292405 := bbase (se 5 (by rfl) ⟨13706, by rfl⟩ : syracuseStep 292405 = 27413) (by norm_num)
theorem B489053 : Blo 255820 489053 := bbase (se 3 (by rfl) ⟨91697, by rfl⟩ : syracuseStep 489053 = 183395) (by norm_num)
theorem B325225 : Blo 255820 325225 := bbase (se 2 (by rfl) ⟨121959, by rfl⟩ : syracuseStep 325225 = 243919) (by norm_num)
theorem B390773 : Blo 255820 390773 := bbase (se 5 (by rfl) ⟨18317, by rfl⟩ : syracuseStep 390773 = 36635) (by norm_num)
theorem B1111733 : Blo 255820 1111733 := bbase (se 5 (by rfl) ⟨52112, by rfl⟩ : syracuseStep 1111733 = 104225) (by norm_num)
theorem B652981 : Blo 255820 652981 := bbase (se 5 (by rfl) ⟨30608, by rfl⟩ : syracuseStep 652981 = 61217) (by norm_num)
theorem B620237 : Blo 255820 620237 := bbase (se 3 (by rfl) ⟨116294, by rfl⟩ : syracuseStep 620237 = 232589) (by norm_num)
theorem B325397 : Blo 255820 325397 := bbase (se 6 (by rfl) ⟨7626, by rfl⟩ : syracuseStep 325397 = 15253) (by norm_num)
theorem B653093 : Blo 255820 653093 := bbase (se 4 (by rfl) ⟨61227, by rfl⟩ : syracuseStep 653093 = 122455) (by norm_num)
theorem B325453 : Blo 255820 325453 := bbase (se 3 (by rfl) ⟨61022, by rfl⟩ : syracuseStep 325453 = 122045) (by norm_num)
theorem B489341 : Blo 255820 489341 := bbase (se 3 (by rfl) ⟨91751, by rfl⟩ : syracuseStep 489341 = 183503) (by norm_num)
theorem B980869 : Blo 255820 980869 := bbase (se 4 (by rfl) ⟨91956, by rfl⟩ : syracuseStep 980869 = 183913) (by norm_num)
theorem B1963925 : Blo 255820 1963925 := bbase (se 6 (by rfl) ⟨46029, by rfl⟩ : syracuseStep 1963925 = 92059) (by norm_num)
theorem B325549 : Blo 255820 325549 := bbase (se 3 (by rfl) ⟨61040, by rfl⟩ : syracuseStep 325549 = 122081) (by norm_num)
theorem B620477 : Blo 255820 620477 := bbase (se 3 (by rfl) ⟨116339, by rfl⟩ : syracuseStep 620477 = 232679) (by norm_num)
theorem B587749 : Blo 255820 587749 := bbase (se 4 (by rfl) ⟨55101, by rfl⟩ : syracuseStep 587749 = 110203) (by norm_num)
theorem B653285 : Blo 255820 653285 := bbase (se 4 (by rfl) ⟨61245, by rfl⟩ : syracuseStep 653285 = 122491) (by norm_num)
theorem B489493 : Blo 255820 489493 := bbase (se 6 (by rfl) ⟨11472, by rfl⟩ : syracuseStep 489493 = 22945) (by norm_num)
theorem B325721 : Blo 255820 325721 := bbase (se 2 (by rfl) ⟨122145, by rfl⟩ : syracuseStep 325721 = 244291) (by norm_num)
theorem B587893 : Blo 255820 587893 := bbase (se 5 (by rfl) ⟨27557, by rfl⟩ : syracuseStep 587893 = 55115) (by norm_num)
theorem B325777 : Blo 255820 325777 := bbase (se 2 (by rfl) ⟨122166, by rfl⟩ : syracuseStep 325777 = 244333) (by norm_num)
theorem B981173 : Blo 255820 981173 := bbase (se 5 (by rfl) ⟨45992, by rfl⟩ : syracuseStep 981173 = 91985) (by norm_num)
theorem B325873 : Blo 255820 325873 := bbase (se 2 (by rfl) ⟨122202, by rfl⟩ : syracuseStep 325873 = 244405) (by norm_num)
theorem B260377 : Blo 255820 260377 := bbase (se 2 (by rfl) ⟨97641, by rfl⟩ : syracuseStep 260377 = 195283) (by norm_num)
theorem B653629 : Blo 255820 653629 := bbase (se 3 (by rfl) ⟨122555, by rfl⟩ : syracuseStep 653629 = 245111) (by norm_num)
theorem B489797 : Blo 255820 489797 := bbase (se 4 (by rfl) ⟨45918, by rfl⟩ : syracuseStep 489797 = 91837) (by norm_num)
theorem B326045 : Blo 255820 326045 := bbase (se 3 (by rfl) ⟨61133, by rfl⟩ : syracuseStep 326045 = 122267) (by norm_num)
theorem B653741 : Blo 255820 653741 := bbase (se 3 (by rfl) ⟨122576, by rfl⟩ : syracuseStep 653741 = 245153) (by norm_num)
theorem B326101 : Blo 255820 326101 := bbase (se 7 (by rfl) ⟨3821, by rfl⟩ : syracuseStep 326101 = 7643) (by norm_num)
theorem B326197 : Blo 255820 326197 := bbase (se 5 (by rfl) ⟨15290, by rfl⟩ : syracuseStep 326197 = 30581) (by norm_num)
theorem B260693 : Blo 255820 260693 := bbase (se 8 (by rfl) ⟨1527, by rfl⟩ : syracuseStep 260693 = 3055) (by norm_num)
theorem B653933 : Blo 255820 653933 := bbase (se 3 (by rfl) ⟨122612, by rfl⟩ : syracuseStep 653933 = 245225) (by norm_num)
theorem B1473173 : Blo 255820 1473173 := bbase (se 6 (by rfl) ⟨34527, by rfl⟩ : syracuseStep 1473173 = 69055) (by norm_num)
theorem B326369 : Blo 255820 326369 := bbase (se 2 (by rfl) ⟨122388, by rfl⟩ : syracuseStep 326369 = 244777) (by norm_num)
theorem B1309445 : Blo 255820 1309445 := bbase (se 4 (by rfl) ⟨122760, by rfl⟩ : syracuseStep 1309445 = 245521) (by norm_num)
theorem B326425 : Blo 255820 326425 := bbase (se 2 (by rfl) ⟨122409, by rfl⟩ : syracuseStep 326425 = 244819) (by norm_num)
theorem B326521 : Blo 255820 326521 := bbase (se 2 (by rfl) ⟨122445, by rfl⟩ : syracuseStep 326521 = 244891) (by norm_num)
theorem B1244069 : Blo 255820 1244069 := bbase (se 4 (by rfl) ⟨116631, by rfl⟩ : syracuseStep 1244069 = 233263) (by norm_num)
theorem B654277 : Blo 255820 654277 := bbase (se 4 (by rfl) ⟨61338, by rfl⟩ : syracuseStep 654277 = 122677) (by norm_num)
theorem B326693 : Blo 255820 326693 := bbase (se 4 (by rfl) ⟨30627, by rfl⟩ : syracuseStep 326693 = 61255) (by norm_num)
theorem B490549 : Blo 255820 490549 := bbase (se 5 (by rfl) ⟨22994, by rfl⟩ : syracuseStep 490549 = 45989) (by norm_num)
theorem B654389 : Blo 255820 654389 := bbase (se 5 (by rfl) ⟨30674, by rfl⟩ : syracuseStep 654389 = 61349) (by norm_num)
theorem B326749 : Blo 255820 326749 := bbase (se 3 (by rfl) ⟨61265, by rfl⟩ : syracuseStep 326749 = 122531) (by norm_num)
theorem B261245 : Blo 255820 261245 := bbase (se 3 (by rfl) ⟨48983, by rfl⟩ : syracuseStep 261245 = 97967) (by norm_num)
theorem B326845 : Blo 255820 326845 := bbase (se 3 (by rfl) ⟨61283, by rfl⟩ : syracuseStep 326845 = 122567) (by norm_num)
theorem B490693 : Blo 255820 490693 := bbase (se 4 (by rfl) ⟨46002, by rfl⟩ : syracuseStep 490693 = 92005) (by norm_num)
theorem B654581 : Blo 255820 654581 := bbase (se 5 (by rfl) ⟨30683, by rfl⟩ : syracuseStep 654581 = 61367) (by norm_num)
theorem B490853 : Blo 255820 490853 := bbase (se 4 (by rfl) ⟨46017, by rfl⟩ : syracuseStep 490853 = 92035) (by norm_num)
theorem B327017 : Blo 255820 327017 := bbase (se 2 (by rfl) ⟨122631, by rfl⟩ : syracuseStep 327017 = 245263) (by norm_num)
theorem B327073 : Blo 255820 327073 := bbase (se 2 (by rfl) ⟨122652, by rfl⟩ : syracuseStep 327073 = 245305) (by norm_num)
theorem B490997 : Blo 255820 490997 := bbase (se 5 (by rfl) ⟨23015, by rfl⟩ : syracuseStep 490997 = 46031) (by norm_num)
theorem B327169 : Blo 255820 327169 := bbase (se 2 (by rfl) ⟨122688, by rfl⟩ : syracuseStep 327169 = 245377) (by norm_num)
theorem B2227733 : Blo 255820 2227733 := bbase (se 6 (by rfl) ⟨52212, by rfl⟩ : syracuseStep 2227733 = 104425) (by norm_num)
theorem B654925 : Blo 255820 654925 := bbase (se 3 (by rfl) ⟨122798, by rfl⟩ : syracuseStep 654925 = 245597) (by norm_num)
theorem B327341 : Blo 255820 327341 := bbase (se 3 (by rfl) ⟨61376, by rfl⟩ : syracuseStep 327341 = 122753) (by norm_num)
theorem B655037 : Blo 255820 655037 := bbase (se 3 (by rfl) ⟨122819, by rfl⟩ : syracuseStep 655037 = 245639) (by norm_num)
theorem B261829 : Blo 255820 261829 := bbase (se 4 (by rfl) ⟨24546, by rfl⟩ : syracuseStep 261829 = 49093) (by norm_num)
theorem B327397 : Blo 255820 327397 := bbase (se 4 (by rfl) ⟨30693, by rfl⟩ : syracuseStep 327397 = 61387) (by norm_num)
theorem B851717 : Blo 255820 851717 := bbase (se 4 (by rfl) ⟨79848, by rfl⟩ : syracuseStep 851717 = 159697) (by norm_num)
theorem B491285 : Blo 255820 491285 := bbase (se 6 (by rfl) ⟨11514, by rfl⟩ : syracuseStep 491285 = 23029) (by norm_num)
theorem B327493 : Blo 255820 327493 := bbase (se 4 (by rfl) ⟨30702, by rfl⟩ : syracuseStep 327493 = 61405) (by norm_num)
theorem B655229 : Blo 255820 655229 := bbase (se 3 (by rfl) ⟨122855, by rfl⟩ : syracuseStep 655229 = 245711) (by norm_num)
theorem B556949 : Blo 255820 556949 := bbase (se 6 (by rfl) ⟨13053, by rfl⟩ : syracuseStep 556949 = 26107) (by norm_num)
theorem B491437 : Blo 255820 491437 := bbase (se 3 (by rfl) ⟨92144, by rfl⟩ : syracuseStep 491437 = 184289) (by norm_num)
theorem B262121 : Blo 255820 262121 := bbase (se 2 (by rfl) ⟨98295, by rfl⟩ : syracuseStep 262121 = 196591) (by norm_num)
theorem B327665 : Blo 255820 327665 := bbase (se 2 (by rfl) ⟨122874, by rfl⟩ : syracuseStep 327665 = 245749) (by norm_num)
theorem B983117 : Blo 255820 983117 := bstep (se 3 (by rfl) ⟨184334, by rfl⟩ : syracuseStep 983117 = 368669) B368669
theorem B294995 : Blo 255820 294995 := bstep (se 1 (by rfl) ⟨221246, by rfl⟩ : syracuseStep 294995 = 442493) B442493
theorem B491665 : Blo 255820 491665 := bstep (se 2 (by rfl) ⟨184374, by rfl⟩ : syracuseStep 491665 = 368749) B368749
theorem B327827 : Blo 255820 327827 := bstep (se 1 (by rfl) ⟨245870, by rfl⟩ : syracuseStep 327827 = 491741) B491741
theorem B655523 : Blo 255820 655523 := bstep (se 1 (by rfl) ⟨491642, by rfl⟩ : syracuseStep 655523 = 983285) B983285
theorem B1573091 : Blo 255820 1573091 := bstep (se 1 (by rfl) ⟨1179818, by rfl⟩ : syracuseStep 1573091 = 2359637) B2359637
theorem B590129 : Blo 255820 590129 := bstep (se 2 (by rfl) ⟨221298, by rfl⟩ : syracuseStep 590129 = 442597) B442597
theorem B491825 : Blo 255820 491825 := bstep (se 2 (by rfl) ⟨184434, by rfl⟩ : syracuseStep 491825 = 368869) B368869
theorem B655715 : Blo 255820 655715 := bstep (se 1 (by rfl) ⟨491786, by rfl⟩ : syracuseStep 655715 = 983573) B983573
theorem B1474949 : Blo 255820 1474949 := bstep (se 4 (by rfl) ⟨138276, by rfl⟩ : syracuseStep 1474949 = 276553) B276553
theorem B1180109 : Blo 255820 1180109 := bstep (se 3 (by rfl) ⟨221270, by rfl⟩ : syracuseStep 1180109 = 442541) B442541
theorem B819665 : Blo 255820 819665 := bstep (se 2 (by rfl) ⟨307374, by rfl⟩ : syracuseStep 819665 = 614749) B614749
theorem B819715 : Blo 255820 819715 := bstep (se 1 (by rfl) ⟨614786, by rfl⟩ : syracuseStep 819715 = 1229573) B1229573
theorem B492227 : Blo 255820 492227 := bstep (se 1 (by rfl) ⟨369170, by rfl⟩ : syracuseStep 492227 = 738341) B738341
theorem B1475405 : Blo 255820 1475405 := bstep (se 3 (by rfl) ⟨276638, by rfl⟩ : syracuseStep 1475405 = 553277) B553277
theorem B328531 : Blo 255820 328531 := bstep (se 1 (by rfl) ⟨246398, by rfl⟩ : syracuseStep 328531 = 492797) B492797
theorem B328627 : Blo 255820 328627 := bstep (se 1 (by rfl) ⟨246470, by rfl⟩ : syracuseStep 328627 = 492941) B492941
theorem B4949045 : Blo 255820 4949045 := bstep (se 5 (by rfl) ⟨231986, by rfl⟩ : syracuseStep 4949045 = 463973) B463973
theorem B1573987 : Blo 255820 1573987 := bstep (se 1 (by rfl) ⟨1180490, by rfl⟩ : syracuseStep 1573987 = 2360981) B2360981
theorem B525425 : Blo 255820 525425 := bstep (se 2 (by rfl) ⟨197034, by rfl⟩ : syracuseStep 525425 = 394069) B394069
theorem B328883 : Blo 255820 328883 := bstep (se 1 (by rfl) ⟨246662, by rfl⟩ : syracuseStep 328883 = 493325) B493325
theorem B656657 : Blo 255820 656657 := bstep (se 2 (by rfl) ⟨246246, by rfl⟩ : syracuseStep 656657 = 492493) B492493
theorem B656707 : Blo 255820 656707 := bstep (se 1 (by rfl) ⟨492530, by rfl⟩ : syracuseStep 656707 = 985061) B985061
theorem B787907 : Blo 255820 787907 := bstep (se 1 (by rfl) ⟨590930, by rfl⟩ : syracuseStep 787907 = 1181861) B1181861
theorem B656849 : Blo 255820 656849 := bstep (se 2 (by rfl) ⟨246318, by rfl⟩ : syracuseStep 656849 = 492637) B492637
theorem B493123 : Blo 255820 493123 := bstep (se 1 (by rfl) ⟨369842, by rfl⟩ : syracuseStep 493123 = 739685) B739685
theorem B1967813 : Blo 255820 1967813 := bstep (se 4 (by rfl) ⟨184482, by rfl⟩ : syracuseStep 1967813 = 368965) B368965
theorem B820945 : Blo 255820 820945 := bstep (se 2 (by rfl) ⟨307854, by rfl⟩ : syracuseStep 820945 = 615709) B615709
theorem B985229 : Blo 255820 985229 := bstep (se 3 (by rfl) ⟨184730, by rfl⟩ : syracuseStep 985229 = 369461) B369461
theorem B461027 : Blo 255820 461027 := bstep (se 1 (by rfl) ⟨345770, by rfl⟩ : syracuseStep 461027 = 691541) B691541
theorem B1313009 : Blo 255820 1313009 := bstep (se 2 (by rfl) ⟨492378, by rfl⟩ : syracuseStep 1313009 = 984757) B984757
theorem B461315 : Blo 255820 461315 := bstep (se 1 (by rfl) ⟨345986, by rfl⟩ : syracuseStep 461315 = 691973) B691973
theorem B822125 : Blo 255820 822125 := bstep (se 3 (by rfl) ⟨154148, by rfl⟩ : syracuseStep 822125 = 308297) B308297
theorem B1641329 : Blo 255820 1641329 := bstep (se 2 (by rfl) ⟨615498, by rfl⟩ : syracuseStep 1641329 = 1230997) B1230997
theorem B986033 : Blo 255820 986033 := bstep (se 2 (by rfl) ⟨369762, by rfl⟩ : syracuseStep 986033 = 739525) B739525
theorem B1576205 : Blo 255820 1576205 := bstep (se 3 (by rfl) ⟨295538, by rfl⟩ : syracuseStep 1576205 = 591077) B591077
theorem B1641869 : Blo 255820 1641869 := bstep (se 3 (by rfl) ⟨307850, by rfl⟩ : syracuseStep 1641869 = 615701) B615701
theorem B658979 : Blo 255820 658979 := bstep (se 1 (by rfl) ⟨494234, by rfl⟩ : syracuseStep 658979 = 988469) B988469
theorem B1314467 : Blo 255820 1314467 := bstep (se 1 (by rfl) ⟨985850, by rfl⟩ : syracuseStep 1314467 = 1971701) B1971701
theorem B1478321 : Blo 255820 1478321 := bstep (se 2 (by rfl) ⟨554370, by rfl⟩ : syracuseStep 1478321 = 1108741) B1108741
theorem B659249 : Blo 255820 659249 := bstep (se 2 (by rfl) ⟨247218, by rfl⟩ : syracuseStep 659249 = 494437) B494437
theorem B2920373 : Blo 255820 2920373 := bstep (se 5 (by rfl) ⟨136892, by rfl⟩ : syracuseStep 2920373 = 273785) B273785
theorem B1052621 : Blo 255820 1052621 := bstep (se 3 (by rfl) ⟨197366, by rfl⟩ : syracuseStep 1052621 = 394733) B394733
theorem B790481 : Blo 255820 790481 := bstep (se 2 (by rfl) ⟨296430, by rfl⟩ : syracuseStep 790481 = 592861) B592861
theorem B1577009 : Blo 255820 1577009 := bstep (se 2 (by rfl) ⟨591378, by rfl⟩ : syracuseStep 1577009 = 1182757) B1182757
theorem B364819 : Blo 255820 364819 := bstep (se 1 (by rfl) ⟨273614, by rfl⟩ : syracuseStep 364819 = 547229) B547229
theorem B463217 : Blo 255820 463217 := bstep (se 2 (by rfl) ⟨173706, by rfl⟩ : syracuseStep 463217 = 347413) B347413
theorem B1315277 : Blo 255820 1315277 := bstep (se 3 (by rfl) ⟨246614, by rfl⟩ : syracuseStep 1315277 = 493229) B493229
theorem B496145 : Blo 255820 496145 := bstep (se 2 (by rfl) ⟨186054, by rfl⟩ : syracuseStep 496145 = 372109) B372109
theorem B823907 : Blo 255820 823907 := bstep (se 1 (by rfl) ⟨617930, by rfl⟩ : syracuseStep 823907 = 1235861) B1235861
theorem B561763 : Blo 255820 561763 := bstep (se 1 (by rfl) ⟨421322, by rfl⟩ : syracuseStep 561763 = 842645) B842645
theorem B1053283 : Blo 255820 1053283 := bstep (se 1 (by rfl) ⟨789962, by rfl⟩ : syracuseStep 1053283 = 1579925) B1579925
theorem B463715 : Blo 255820 463715 := bstep (se 1 (by rfl) ⟨347786, by rfl⟩ : syracuseStep 463715 = 695573) B695573
theorem B1905677 : Blo 255820 1905677 := bstep (se 3 (by rfl) ⟨357314, by rfl⟩ : syracuseStep 1905677 = 714629) B714629
theorem B365953 : Blo 255820 365953 := bstep (se 2 (by rfl) ⟨137232, by rfl⟩ : syracuseStep 365953 = 274465) B274465
theorem B366049 : Blo 255820 366049 := bstep (se 2 (by rfl) ⟨137268, by rfl⟩ : syracuseStep 366049 = 274537) B274537
theorem B1578467 : Blo 255820 1578467 := bstep (se 1 (by rfl) ⟨1183850, by rfl⟩ : syracuseStep 1578467 = 2367701) B2367701
theorem B431777 : Blo 255820 431777 := bstep (se 2 (by rfl) ⟨161916, by rfl⟩ : syracuseStep 431777 = 323833) B323833
theorem B824995 : Blo 255820 824995 := bstep (se 1 (by rfl) ⟨618746, by rfl⟩ : syracuseStep 824995 = 1237493) B1237493
theorem B431905 : Blo 255820 431905 := bstep (se 2 (by rfl) ⟨161964, by rfl⟩ : syracuseStep 431905 = 323929) B323929
theorem B825137 : Blo 255820 825137 := bstep (se 2 (by rfl) ⟨309426, by rfl⟩ : syracuseStep 825137 = 618853) B618853
theorem B431939 : Blo 255820 431939 := bstep (se 1 (by rfl) ⟨323954, by rfl⟩ : syracuseStep 431939 = 647909) B647909
theorem B530275 : Blo 255820 530275 := bstep (se 1 (by rfl) ⟨397706, by rfl⟩ : syracuseStep 530275 = 795413) B795413
theorem B464753 : Blo 255820 464753 := bstep (se 2 (by rfl) ⟨174282, by rfl⟩ : syracuseStep 464753 = 348565) B348565
theorem B432067 : Blo 255820 432067 := bstep (se 1 (by rfl) ⟨324050, by rfl⟩ : syracuseStep 432067 = 648101) B648101
theorem B366545 : Blo 255820 366545 := bstep (se 2 (by rfl) ⟨137454, by rfl⟩ : syracuseStep 366545 = 274909) B274909
theorem B432209 : Blo 255820 432209 := bstep (se 2 (by rfl) ⟨162078, by rfl⟩ : syracuseStep 432209 = 324157) B324157
theorem B5314673 : Blo 255820 5314673 := bstep (se 2 (by rfl) ⟨1993002, by rfl⟩ : syracuseStep 5314673 = 3986005) B3986005
theorem B2398349 : Blo 255820 2398349 := bstep (se 3 (by rfl) ⟨449690, by rfl⟩ : syracuseStep 2398349 = 899381) B899381
theorem B923825 : Blo 255820 923825 := bstep (se 2 (by rfl) ⟨346434, by rfl⟩ : syracuseStep 923825 = 692869) B692869
theorem B432337 : Blo 255820 432337 := bstep (se 2 (by rfl) ⟨162126, by rfl⟩ : syracuseStep 432337 = 324253) B324253
theorem B432371 : Blo 255820 432371 := bstep (se 1 (by rfl) ⟨324278, by rfl⟩ : syracuseStep 432371 = 648557) B648557
theorem B432499 : Blo 255820 432499 := bstep (se 1 (by rfl) ⟨324374, by rfl⟩ : syracuseStep 432499 = 648749) B648749
theorem B432641 : Blo 255820 432641 := bstep (se 2 (by rfl) ⟨162240, by rfl⟩ : syracuseStep 432641 = 324481) B324481
theorem B1645069 : Blo 255820 1645069 := bstep (se 3 (by rfl) ⟨308450, by rfl⟩ : syracuseStep 1645069 = 616901) B616901
theorem B432769 : Blo 255820 432769 := bstep (se 2 (by rfl) ⟨162288, by rfl⟩ : syracuseStep 432769 = 324577) B324577
theorem B432803 : Blo 255820 432803 := bstep (se 1 (by rfl) ⟨324602, by rfl⟩ : syracuseStep 432803 = 649205) B649205
theorem B432931 : Blo 255820 432931 := bstep (se 1 (by rfl) ⟨324698, by rfl⟩ : syracuseStep 432931 = 649397) B649397
theorem B367411 : Blo 255820 367411 := bstep (se 1 (by rfl) ⟨275558, by rfl⟩ : syracuseStep 367411 = 551117) B551117
theorem B367507 : Blo 255820 367507 := bstep (se 1 (by rfl) ⟨275630, by rfl⟩ : syracuseStep 367507 = 551261) B551261
theorem B433073 : Blo 255820 433073 := bstep (se 2 (by rfl) ⟨162402, by rfl⟩ : syracuseStep 433073 = 324805) B324805
theorem B433201 : Blo 255820 433201 := bstep (se 2 (by rfl) ⟨162450, by rfl⟩ : syracuseStep 433201 = 324901) B324901
theorem B433235 : Blo 255820 433235 := bstep (se 1 (by rfl) ⟨324926, by rfl⟩ : syracuseStep 433235 = 649853) B649853
theorem B826481 : Blo 255820 826481 := bstep (se 2 (by rfl) ⟨309930, by rfl⟩ : syracuseStep 826481 = 619861) B619861
theorem B695441 : Blo 255820 695441 := bstep (se 2 (by rfl) ⟨260790, by rfl⟩ : syracuseStep 695441 = 521581) B521581
theorem B4168901 : Blo 255820 4168901 := bstep (se 4 (by rfl) ⟨390834, by rfl⟩ : syracuseStep 4168901 = 781669) B781669
theorem B433363 : Blo 255820 433363 := bstep (se 1 (by rfl) ⟨325022, by rfl⟩ : syracuseStep 433363 = 650045) B650045
theorem B433505 : Blo 255820 433505 := bstep (se 2 (by rfl) ⟨162564, by rfl⟩ : syracuseStep 433505 = 325129) B325129
theorem B368003 : Blo 255820 368003 := bstep (se 1 (by rfl) ⟨276002, by rfl⟩ : syracuseStep 368003 = 552005) B552005
theorem B433633 : Blo 255820 433633 := bstep (se 2 (by rfl) ⟨162612, by rfl⟩ : syracuseStep 433633 = 325225) B325225
theorem B433667 : Blo 255820 433667 := bstep (se 1 (by rfl) ⟨325250, by rfl⟩ : syracuseStep 433667 = 650501) B650501
theorem B630289 : Blo 255820 630289 := bstep (se 2 (by rfl) ⟨236358, by rfl⟩ : syracuseStep 630289 = 472717) B472717
theorem B433795 : Blo 255820 433795 := bstep (se 1 (by rfl) ⟨325346, by rfl⟩ : syracuseStep 433795 = 650693) B650693
theorem B433937 : Blo 255820 433937 := bstep (se 2 (by rfl) ⟨162726, by rfl⟩ : syracuseStep 433937 = 325453) B325453
theorem B728909 : Blo 255820 728909 := bstep (se 3 (by rfl) ⟨136670, by rfl⟩ : syracuseStep 728909 = 273341) B273341
theorem B434065 : Blo 255820 434065 := bstep (se 2 (by rfl) ⟨162774, by rfl⟩ : syracuseStep 434065 = 325549) B325549
theorem B434099 : Blo 255820 434099 := bstep (se 1 (by rfl) ⟨325574, by rfl⟩ : syracuseStep 434099 = 651149) B651149
theorem B368641 : Blo 255820 368641 := bstep (se 2 (by rfl) ⟨138240, by rfl⟩ : syracuseStep 368641 = 276481) B276481
theorem B729091 : Blo 255820 729091 := bstep (se 1 (by rfl) ⟨546818, by rfl⟩ : syracuseStep 729091 = 1093637) B1093637
theorem B827405 : Blo 255820 827405 := bstep (se 3 (by rfl) ⟨155138, by rfl⟩ : syracuseStep 827405 = 310277) B310277
theorem B729137 : Blo 255820 729137 := bstep (se 2 (by rfl) ⟨273426, by rfl⟩ : syracuseStep 729137 = 546853) B546853
theorem B434227 : Blo 255820 434227 := bstep (se 1 (by rfl) ⟨325670, by rfl⟩ : syracuseStep 434227 = 651341) B651341
theorem B598115 : Blo 255820 598115 := bstep (se 1 (by rfl) ⟨448586, by rfl⟩ : syracuseStep 598115 = 897173) B897173
theorem B434369 : Blo 255820 434369 := bstep (se 2 (by rfl) ⟨162888, by rfl⟩ : syracuseStep 434369 = 325777) B325777
theorem B827597 : Blo 255820 827597 := bstep (se 3 (by rfl) ⟨155174, by rfl⟩ : syracuseStep 827597 = 310349) B310349
theorem B467203 : Blo 255820 467203 := bstep (se 1 (by rfl) ⟨350402, by rfl⟩ : syracuseStep 467203 = 700805) B700805
theorem B434497 : Blo 255820 434497 := bstep (se 2 (by rfl) ⟨162936, by rfl⟩ : syracuseStep 434497 = 325873) B325873
theorem B794947 : Blo 255820 794947 := bstep (se 1 (by rfl) ⟨596210, by rfl⟩ : syracuseStep 794947 = 1192421) B1192421
theorem B696653 : Blo 255820 696653 := bstep (se 3 (by rfl) ⟨130622, by rfl⟩ : syracuseStep 696653 = 261245) B261245
theorem B368977 : Blo 255820 368977 := bstep (se 2 (by rfl) ⟨138366, by rfl⟩ : syracuseStep 368977 = 276733) B276733
theorem B434531 : Blo 255820 434531 := bstep (se 1 (by rfl) ⟨325898, by rfl⟩ : syracuseStep 434531 = 651797) B651797
theorem B434659 : Blo 255820 434659 := bstep (se 1 (by rfl) ⟨325994, by rfl⟩ : syracuseStep 434659 = 651989) B651989
theorem B664067 : Blo 255820 664067 := bstep (se 1 (by rfl) ⟨498050, by rfl⟩ : syracuseStep 664067 = 996101) B996101
theorem B434801 : Blo 255820 434801 := bstep (se 2 (by rfl) ⟨163050, by rfl⟩ : syracuseStep 434801 = 326101) B326101
theorem B434929 : Blo 255820 434929 := bstep (se 2 (by rfl) ⟨163098, by rfl⟩ : syracuseStep 434929 = 326197) B326197
theorem B434963 : Blo 255820 434963 := bstep (se 1 (by rfl) ⟨326222, by rfl⟩ : syracuseStep 434963 = 652445) B652445
theorem B467779 : Blo 255820 467779 := bstep (se 1 (by rfl) ⟨350834, by rfl⟩ : syracuseStep 467779 = 701669) B701669
theorem B435091 : Blo 255820 435091 := bstep (se 1 (by rfl) ⟨326318, by rfl⟩ : syracuseStep 435091 = 652637) B652637
theorem B369569 : Blo 255820 369569 := bstep (se 2 (by rfl) ⟨138588, by rfl⟩ : syracuseStep 369569 = 277177) B277177
theorem B435233 : Blo 255820 435233 := bstep (se 2 (by rfl) ⟨163212, by rfl⟩ : syracuseStep 435233 = 326425) B326425
theorem B664643 : Blo 255820 664643 := bstep (se 1 (by rfl) ⟨498482, by rfl⟩ : syracuseStep 664643 = 996965) B996965
theorem B435361 : Blo 255820 435361 := bstep (se 2 (by rfl) ⟨163260, by rfl⟩ : syracuseStep 435361 = 326521) B326521
theorem B435395 : Blo 255820 435395 := bstep (se 1 (by rfl) ⟨326546, by rfl⟩ : syracuseStep 435395 = 653093) B653093
theorem B369937 : Blo 255820 369937 := bstep (se 2 (by rfl) ⟨138726, by rfl⟩ : syracuseStep 369937 = 277453) B277453
theorem B435523 : Blo 255820 435523 := bstep (se 1 (by rfl) ⟨326642, by rfl⟩ : syracuseStep 435523 = 653285) B653285
theorem B1123661 : Blo 255820 1123661 := bstep (se 3 (by rfl) ⟨210686, by rfl⟩ : syracuseStep 1123661 = 421373) B421373
theorem B435665 : Blo 255820 435665 := bstep (se 2 (by rfl) ⟨163374, by rfl⟩ : syracuseStep 435665 = 326749) B326749
theorem B730595 : Blo 255820 730595 := bstep (se 1 (by rfl) ⟨547946, by rfl⟩ : syracuseStep 730595 = 1095893) B1095893
theorem B2991629 : Blo 255820 2991629 := bstep (se 3 (by rfl) ⟨560930, by rfl⟩ : syracuseStep 2991629 = 1121861) B1121861
theorem B435793 : Blo 255820 435793 := bstep (se 2 (by rfl) ⟨163422, by rfl⟩ : syracuseStep 435793 = 326845) B326845
theorem B435827 : Blo 255820 435827 := bstep (se 1 (by rfl) ⟨326870, by rfl⟩ : syracuseStep 435827 = 653741) B653741
theorem B1124081 : Blo 255820 1124081 := bstep (se 2 (by rfl) ⟨421530, by rfl⟩ : syracuseStep 1124081 = 843061) B843061
theorem B435955 : Blo 255820 435955 := bstep (se 1 (by rfl) ⟨326966, by rfl⟩ : syracuseStep 435955 = 653933) B653933
theorem B436097 : Blo 255820 436097 := bstep (se 2 (by rfl) ⟨163536, by rfl⟩ : syracuseStep 436097 = 327073) B327073
theorem B829379 : Blo 255820 829379 := bstep (se 1 (by rfl) ⟨622034, by rfl⟩ : syracuseStep 829379 = 1244069) B1244069
theorem B436225 : Blo 255820 436225 := bstep (se 2 (by rfl) ⟨163584, by rfl⟩ : syracuseStep 436225 = 327169) B327169
theorem B436259 : Blo 255820 436259 := bstep (se 1 (by rfl) ⟨327194, by rfl⟩ : syracuseStep 436259 = 654389) B654389
theorem B1190051 : Blo 255820 1190051 := bstep (se 1 (by rfl) ⟨892538, by rfl⟩ : syracuseStep 1190051 = 1785077) B1785077
theorem B436387 : Blo 255820 436387 := bstep (se 1 (by rfl) ⟨327290, by rfl⟩ : syracuseStep 436387 = 654581) B654581
theorem B3549365 : Blo 255820 3549365 := bstep (se 5 (by rfl) ⟨166376, by rfl⟩ : syracuseStep 3549365 = 332753) B332753
theorem B436529 : Blo 255820 436529 := bstep (se 2 (by rfl) ⟨163698, by rfl⟩ : syracuseStep 436529 = 327397) B327397
theorem B1485155 : Blo 255820 1485155 := bstep (se 1 (by rfl) ⟨1113866, by rfl⟩ : syracuseStep 1485155 = 2227733) B2227733
theorem B436657 : Blo 255820 436657 := bstep (se 2 (by rfl) ⟨163746, by rfl⟩ : syracuseStep 436657 = 327493) B327493
theorem B371137 : Blo 255820 371137 := bstep (se 2 (by rfl) ⟨139176, by rfl⟩ : syracuseStep 371137 = 278353) B278353
theorem B436691 : Blo 255820 436691 := bstep (se 1 (by rfl) ⟨327518, by rfl⟩ : syracuseStep 436691 = 655037) B655037
theorem B567811 : Blo 255820 567811 := bstep (se 1 (by rfl) ⟨425858, by rfl⟩ : syracuseStep 567811 = 851717) B851717
theorem B436819 : Blo 255820 436819 := bstep (se 1 (by rfl) ⟨327614, by rfl⟩ : syracuseStep 436819 = 655229) B655229
theorem B371299 : Blo 255820 371299 := bstep (se 1 (by rfl) ⟨278474, by rfl⟩ : syracuseStep 371299 = 556949) B556949
theorem B698989 : Blo 255820 698989 := bstep (se 3 (by rfl) ⟨131060, by rfl⟩ : syracuseStep 698989 = 262121) B262121
theorem B3943025 : Blo 255820 3943025 := bstep (se 2 (by rfl) ⟨1478634, by rfl⟩ : syracuseStep 3943025 = 2957269) B2957269
theorem B731825 : Blo 255820 731825 := bstep (se 2 (by rfl) ⟨274434, by rfl⟩ : syracuseStep 731825 = 548869) B548869
theorem B436961 : Blo 255820 436961 := bstep (se 2 (by rfl) ⟨163860, by rfl⟩ : syracuseStep 436961 = 327721) B327721
theorem B469795 : Blo 255820 469795 := bstep (se 1 (by rfl) ⟨352346, by rfl⟩ : syracuseStep 469795 = 704693) B704693
theorem B1649477 : Blo 255820 1649477 := bstep (se 4 (by rfl) ⟨154638, by rfl⟩ : syracuseStep 1649477 = 309277) B309277
theorem B437089 : Blo 255820 437089 := bstep (se 2 (by rfl) ⟨163908, by rfl⟩ : syracuseStep 437089 = 327817) B327817
theorem B437123 : Blo 255820 437123 := bstep (se 1 (by rfl) ⟨327842, by rfl⟩ : syracuseStep 437123 = 655685) B655685
theorem B437251 : Blo 255820 437251 := bstep (se 1 (by rfl) ⟨327938, by rfl⟩ : syracuseStep 437251 = 655877) B655877
theorem B437393 : Blo 255820 437393 := bstep (se 2 (by rfl) ⟨164022, by rfl⟩ : syracuseStep 437393 = 328045) B328045
theorem B863405 : Blo 255820 863405 := bstep (se 3 (by rfl) ⟨161888, by rfl⟩ : syracuseStep 863405 = 323777) B323777
theorem B863459 : Blo 255820 863459 := bstep (se 1 (by rfl) ⟨647594, by rfl⟩ : syracuseStep 863459 = 1295189) B1295189
theorem B437521 : Blo 255820 437521 := bstep (se 2 (by rfl) ⟨164070, by rfl⟩ : syracuseStep 437521 = 328141) B328141
theorem B437555 : Blo 255820 437555 := bstep (se 1 (by rfl) ⟨328166, by rfl⟩ : syracuseStep 437555 = 656333) B656333
theorem B437683 : Blo 255820 437683 := bstep (se 1 (by rfl) ⟨328262, by rfl⟩ : syracuseStep 437683 = 656525) B656525
theorem B863729 : Blo 255820 863729 := bstep (se 2 (by rfl) ⟨323898, by rfl⟩ : syracuseStep 863729 = 647797) B647797
theorem B437825 : Blo 255820 437825 := bstep (se 2 (by rfl) ⟨164184, by rfl⟩ : syracuseStep 437825 = 328369) B328369
theorem B437953 : Blo 255820 437953 := bstep (se 2 (by rfl) ⟨164232, by rfl⟩ : syracuseStep 437953 = 328465) B328465
theorem B437987 : Blo 255820 437987 := bstep (se 1 (by rfl) ⟨328490, by rfl⟩ : syracuseStep 437987 = 656981) B656981
theorem B1322801 : Blo 255820 1322801 := bstep (se 2 (by rfl) ⟨496050, by rfl⟩ : syracuseStep 1322801 = 992101) B992101
theorem B438115 : Blo 255820 438115 := bstep (se 1 (by rfl) ⟨328586, by rfl⟩ : syracuseStep 438115 = 657173) B657173
theorem B1945457 : Blo 255820 1945457 := bstep (se 2 (by rfl) ⟨729546, by rfl⟩ : syracuseStep 1945457 = 1459093) B1459093
theorem B929677 : Blo 255820 929677 := bstep (se 3 (by rfl) ⟨174314, by rfl⟩ : syracuseStep 929677 = 348629) B348629
theorem B438257 : Blo 255820 438257 := bstep (se 2 (by rfl) ⟨164346, by rfl⟩ : syracuseStep 438257 = 328693) B328693
theorem B864269 : Blo 255820 864269 := bstep (se 3 (by rfl) ⟨162050, by rfl⟩ : syracuseStep 864269 = 324101) B324101
theorem B831505 : Blo 255820 831505 := bstep (se 2 (by rfl) ⟨311814, by rfl⟩ : syracuseStep 831505 = 623629) B623629
theorem B438305 : Blo 255820 438305 := bstep (se 2 (by rfl) ⟨164364, by rfl⟩ : syracuseStep 438305 = 328729) B328729
theorem B864323 : Blo 255820 864323 := bstep (se 1 (by rfl) ⟨648242, by rfl⟩ : syracuseStep 864323 = 1296485) B1296485
theorem B733283 : Blo 255820 733283 := bstep (se 1 (by rfl) ⟨549962, by rfl⟩ : syracuseStep 733283 = 1099925) B1099925
theorem B6697073 : Blo 255820 6697073 := bstep (se 2 (by rfl) ⟨2511402, by rfl⟩ : syracuseStep 6697073 = 5022805) B5022805
theorem B438385 : Blo 255820 438385 := bstep (se 2 (by rfl) ⟨164394, by rfl⟩ : syracuseStep 438385 = 328789) B328789
theorem B1388677 : Blo 255820 1388677 := bstep (se 4 (by rfl) ⟨130188, by rfl⟩ : syracuseStep 1388677 = 260377) B260377
theorem B438419 : Blo 255820 438419 := bstep (se 1 (by rfl) ⟨328814, by rfl⟩ : syracuseStep 438419 = 657629) B657629
theorem B700589 : Blo 255820 700589 := bstep (se 3 (by rfl) ⟨131360, by rfl⟩ : syracuseStep 700589 = 262721) B262721
theorem B274691 : Blo 255820 274691 := bstep (se 1 (by rfl) ⟨206018, by rfl⟩ : syracuseStep 274691 = 412037) B412037
theorem B930125 : Blo 255820 930125 := bstep (se 3 (by rfl) ⟨174398, by rfl⟩ : syracuseStep 930125 = 348797) B348797
theorem B864593 : Blo 255820 864593 := bstep (se 2 (by rfl) ⟨324222, by rfl⟩ : syracuseStep 864593 = 648445) B648445
theorem B438691 : Blo 255820 438691 := bstep (se 1 (by rfl) ⟨329018, by rfl⟩ : syracuseStep 438691 = 658037) B658037
theorem B700913 : Blo 255820 700913 := bstep (se 2 (by rfl) ⟨262842, by rfl⟩ : syracuseStep 700913 = 525685) B525685
theorem B1651427 : Blo 255820 1651427 := bstep (se 1 (by rfl) ⟨1238570, by rfl⟩ : syracuseStep 1651427 = 2477141) B2477141
theorem B865133 : Blo 255820 865133 := bstep (se 3 (by rfl) ⟨162212, by rfl⟩ : syracuseStep 865133 = 324425) B324425
theorem B734093 : Blo 255820 734093 := bstep (se 3 (by rfl) ⟨137642, by rfl⟩ : syracuseStep 734093 = 275285) B275285
theorem B865187 : Blo 255820 865187 := bstep (se 1 (by rfl) ⟨648890, by rfl⟩ : syracuseStep 865187 = 1297781) B1297781
theorem B439265 : Blo 255820 439265 := bstep (se 2 (by rfl) ⟨164724, by rfl⟩ : syracuseStep 439265 = 329449) B329449
theorem B734285 : Blo 255820 734285 := bstep (se 3 (by rfl) ⟨137678, by rfl⟩ : syracuseStep 734285 = 275357) B275357
theorem B439427 : Blo 255820 439427 := bstep (se 1 (by rfl) ⟨329570, by rfl⟩ : syracuseStep 439427 = 659141) B659141
theorem B865457 : Blo 255820 865457 := bstep (se 2 (by rfl) ⟨324546, by rfl⟩ : syracuseStep 865457 = 649093) B649093
theorem B931121 : Blo 255820 931121 := bstep (se 2 (by rfl) ⟨349170, by rfl⟩ : syracuseStep 931121 = 698341) B698341
theorem B439825 : Blo 255820 439825 := bstep (se 2 (by rfl) ⟨164934, by rfl⟩ : syracuseStep 439825 = 329869) B329869
theorem B865997 : Blo 255820 865997 := bstep (se 3 (by rfl) ⟨162374, by rfl⟩ : syracuseStep 865997 = 324749) B324749
theorem B866051 : Blo 255820 866051 := bstep (se 1 (by rfl) ⟨649538, by rfl⟩ : syracuseStep 866051 = 1299077) B1299077
theorem B866321 : Blo 255820 866321 := bstep (se 2 (by rfl) ⟨324870, by rfl⟩ : syracuseStep 866321 = 649741) B649741
theorem B735277 : Blo 255820 735277 := bstep (se 3 (by rfl) ⟨137864, by rfl⟩ : syracuseStep 735277 = 275729) B275729
theorem B276707 : Blo 255820 276707 := bstep (se 1 (by rfl) ⟨207530, by rfl⟩ : syracuseStep 276707 = 415061) B415061
theorem B440579 : Blo 255820 440579 := bstep (se 1 (by rfl) ⟨330434, by rfl⟩ : syracuseStep 440579 = 660869) B660869
theorem B1325425 : Blo 255820 1325425 := bstep (se 2 (by rfl) ⟨497034, by rfl⟩ : syracuseStep 1325425 = 994069) B994069
theorem B1325489 : Blo 255820 1325489 := bstep (se 2 (by rfl) ⟨497058, by rfl⟩ : syracuseStep 1325489 = 994117) B994117
theorem B932273 : Blo 255820 932273 := bstep (se 2 (by rfl) ⟨349602, by rfl⟩ : syracuseStep 932273 = 699205) B699205
theorem B866861 : Blo 255820 866861 := bstep (se 3 (by rfl) ⟨162536, by rfl⟩ : syracuseStep 866861 = 325073) B325073
theorem B866915 : Blo 255820 866915 := bstep (se 1 (by rfl) ⟨650186, by rfl⟩ : syracuseStep 866915 = 1300373) B1300373
theorem B1096355 : Blo 255820 1096355 := bstep (se 1 (by rfl) ⟨822266, by rfl⟩ : syracuseStep 1096355 = 1644533) B1644533
theorem B4668101 : Blo 255820 4668101 := bstep (se 4 (by rfl) ⟨437634, by rfl⟩ : syracuseStep 4668101 = 875269) B875269
theorem B277219 : Blo 255820 277219 := bstep (se 1 (by rfl) ⟨207914, by rfl⟩ : syracuseStep 277219 = 415829) B415829
theorem B867185 : Blo 255820 867185 := bstep (se 2 (by rfl) ⟨325194, by rfl⟩ : syracuseStep 867185 = 650389) B650389
theorem B3521549 : Blo 255820 3521549 := bstep (se 3 (by rfl) ⟨660290, by rfl⟩ : syracuseStep 3521549 = 1320581) B1320581
theorem B1653965 : Blo 255820 1653965 := bstep (se 3 (by rfl) ⟨310118, by rfl⟩ : syracuseStep 1653965 = 620237) B620237
theorem B998705 : Blo 255820 998705 := bstep (se 2 (by rfl) ⟨374514, by rfl⟩ : syracuseStep 998705 = 749029) B749029
theorem B2932037 : Blo 255820 2932037 := bstep (se 4 (by rfl) ⟨274878, by rfl⟩ : syracuseStep 2932037 = 549757) B549757
theorem B867725 : Blo 255820 867725 := bstep (se 3 (by rfl) ⟨162698, by rfl⟩ : syracuseStep 867725 = 325397) B325397
theorem B474545 : Blo 255820 474545 := bstep (se 2 (by rfl) ⟨177954, by rfl⟩ : syracuseStep 474545 = 355909) B355909
theorem B867779 : Blo 255820 867779 := bstep (se 1 (by rfl) ⟨650834, by rfl⟩ : syracuseStep 867779 = 1301669) B1301669
theorem B1457635 : Blo 255820 1457635 := bstep (se 1 (by rfl) ⟨1093226, by rfl⟩ : syracuseStep 1457635 = 2186453) B2186453
theorem B2211299 : Blo 255820 2211299 := bstep (se 1 (by rfl) ⟨1658474, by rfl⟩ : syracuseStep 2211299 = 3316949) B3316949
theorem B2801137 : Blo 255820 2801137 := bstep (se 2 (by rfl) ⟨1050426, by rfl⟩ : syracuseStep 2801137 = 2100853) B2100853
theorem B3358307 : Blo 255820 3358307 := bstep (se 1 (by rfl) ⟨2518730, by rfl⟩ : syracuseStep 3358307 = 5037461) B5037461
theorem B900721 : Blo 255820 900721 := bstep (se 2 (by rfl) ⟨337770, by rfl⟩ : syracuseStep 900721 = 675541) B675541
theorem B868049 : Blo 255820 868049 := bstep (se 2 (by rfl) ⟨325518, by rfl⟩ : syracuseStep 868049 = 651037) B651037
theorem B737009 : Blo 255820 737009 := bstep (se 2 (by rfl) ⟨276378, by rfl⟩ : syracuseStep 737009 = 552757) B552757
theorem B737201 : Blo 255820 737201 := bstep (se 2 (by rfl) ⟨276450, by rfl⟩ : syracuseStep 737201 = 552901) B552901
theorem B1458161 : Blo 255820 1458161 := bstep (se 2 (by rfl) ⟨546810, by rfl⟩ : syracuseStep 1458161 = 1093621) B1093621
theorem B966691 : Blo 255820 966691 := bstep (se 1 (by rfl) ⟨725018, by rfl⟩ : syracuseStep 966691 = 1450037) B1450037
theorem B868589 : Blo 255820 868589 := bstep (se 3 (by rfl) ⟨162860, by rfl⟩ : syracuseStep 868589 = 325721) B325721
theorem B2769137 : Blo 255820 2769137 := bstep (se 2 (by rfl) ⟨1038426, by rfl⟩ : syracuseStep 2769137 = 2076853) B2076853
theorem B868643 : Blo 255820 868643 := bstep (se 1 (by rfl) ⟨651482, by rfl⟩ : syracuseStep 868643 = 1302965) B1302965
theorem B311699 : Blo 255820 311699 := bstep (se 1 (by rfl) ⟨233774, by rfl⟩ : syracuseStep 311699 = 467549) B467549
theorem B868913 : Blo 255820 868913 := bstep (se 2 (by rfl) ⟨325842, by rfl⟩ : syracuseStep 868913 = 651685) B651685
theorem B410179 : Blo 255820 410179 := bstep (se 1 (by rfl) ⟨307634, by rfl⟩ : syracuseStep 410179 = 615269) B615269
theorem B1098353 : Blo 255820 1098353 := bstep (se 2 (by rfl) ⟨411882, by rfl⟩ : syracuseStep 1098353 = 823765) B823765
theorem B1983217 : Blo 255820 1983217 := bstep (se 2 (by rfl) ⟨743706, by rfl⟩ : syracuseStep 1983217 = 1487413) B1487413
theorem B410435 : Blo 255820 410435 := bstep (se 1 (by rfl) ⟨307826, by rfl⟩ : syracuseStep 410435 = 615653) B615653
theorem B738193 : Blo 255820 738193 := bstep (se 2 (by rfl) ⟨276822, by rfl⟩ : syracuseStep 738193 = 553645) B553645
theorem B3195875 : Blo 255820 3195875 := bstep (se 1 (by rfl) ⟨2396906, by rfl⟩ : syracuseStep 3195875 = 4793813) B4793813
theorem B934897 : Blo 255820 934897 := bstep (se 2 (by rfl) ⟨350586, by rfl⟩ : syracuseStep 934897 = 701173) B701173
theorem B869453 : Blo 255820 869453 := bstep (se 3 (by rfl) ⟨163022, by rfl⟩ : syracuseStep 869453 = 326045) B326045
theorem B935011 : Blo 255820 935011 := bstep (se 1 (by rfl) ⟨701258, by rfl⟩ : syracuseStep 935011 = 1402517) B1402517
theorem B869507 : Blo 255820 869507 := bstep (se 1 (by rfl) ⟨652130, by rfl⟩ : syracuseStep 869507 = 1304261) B1304261
theorem B738467 : Blo 255820 738467 := bstep (se 1 (by rfl) ⟨553850, by rfl⟩ : syracuseStep 738467 = 1107701) B1107701
theorem B2802869 : Blo 255820 2802869 := bstep (se 5 (by rfl) ⟨131384, by rfl⟩ : syracuseStep 2802869 = 262769) B262769
theorem B738659 : Blo 255820 738659 := bstep (se 1 (by rfl) ⟨553994, by rfl⟩ : syracuseStep 738659 = 1107989) B1107989
theorem B869777 : Blo 255820 869777 := bstep (se 2 (by rfl) ⟨326166, by rfl⟩ : syracuseStep 869777 = 652333) B652333
theorem B1459619 : Blo 255820 1459619 := bstep (se 1 (by rfl) ⟨1094714, by rfl⟩ : syracuseStep 1459619 = 2189429) B2189429
theorem B411139 : Blo 255820 411139 := bstep (se 1 (by rfl) ⟨308354, by rfl⟩ : syracuseStep 411139 = 616709) B616709
theorem B1099277 : Blo 255820 1099277 := bstep (se 3 (by rfl) ⟨206114, by rfl⟩ : syracuseStep 1099277 = 412229) B412229
theorem B411409 : Blo 255820 411409 := bstep (se 2 (by rfl) ⟨154278, by rfl⟩ : syracuseStep 411409 = 308557) B308557
theorem B411473 : Blo 255820 411473 := bstep (se 2 (by rfl) ⟨154302, by rfl⟩ : syracuseStep 411473 = 308605) B308605
theorem B870317 : Blo 255820 870317 := bstep (se 3 (by rfl) ⟨163184, by rfl⟩ : syracuseStep 870317 = 326369) B326369
theorem B870371 : Blo 255820 870371 := bstep (se 1 (by rfl) ⟨652778, by rfl⟩ : syracuseStep 870371 = 1305557) B1305557
theorem B1001521 : Blo 255820 1001521 := bstep (se 2 (by rfl) ⟨375570, by rfl⟩ : syracuseStep 1001521 = 751141) B751141
theorem B739469 : Blo 255820 739469 := bstep (se 3 (by rfl) ⟨138650, by rfl⟩ : syracuseStep 739469 = 277301) B277301
theorem B575729 : Blo 255820 575729 := bstep (se 2 (by rfl) ⟨215898, by rfl⟩ : syracuseStep 575729 = 431797) B431797
theorem B870641 : Blo 255820 870641 := bstep (se 2 (by rfl) ⟨326490, by rfl⟩ : syracuseStep 870641 = 652981) B652981
theorem B575747 : Blo 255820 575747 := bstep (se 1 (by rfl) ⟨431810, by rfl⟩ : syracuseStep 575747 = 863621) B863621
theorem B739651 : Blo 255820 739651 := bstep (se 1 (by rfl) ⟨554738, by rfl⟩ : syracuseStep 739651 = 1109477) B1109477
theorem B903565 : Blo 255820 903565 := bstep (se 3 (by rfl) ⟨169418, by rfl⟩ : syracuseStep 903565 = 338837) B338837
theorem B576017 : Blo 255820 576017 := bstep (se 2 (by rfl) ⟨216006, by rfl⟩ : syracuseStep 576017 = 432013) B432013
theorem B576035 : Blo 255820 576035 := bstep (se 1 (by rfl) ⟨432026, by rfl⟩ : syracuseStep 576035 = 864053) B864053
theorem B1395427 : Blo 255820 1395427 := bstep (se 1 (by rfl) ⟨1046570, by rfl⟩ : syracuseStep 1395427 = 2093141) B2093141
theorem B871181 : Blo 255820 871181 := bstep (se 3 (by rfl) ⟨163346, by rfl⟩ : syracuseStep 871181 = 326693) B326693
theorem B740141 : Blo 255820 740141 := bstep (se 3 (by rfl) ⟨138776, by rfl⟩ : syracuseStep 740141 = 277553) B277553
theorem B576305 : Blo 255820 576305 := bstep (se 2 (by rfl) ⟨216114, by rfl⟩ : syracuseStep 576305 = 432229) B432229
theorem B576323 : Blo 255820 576323 := bstep (se 1 (by rfl) ⟨432242, by rfl⟩ : syracuseStep 576323 = 864485) B864485
theorem B871235 : Blo 255820 871235 := bstep (se 1 (by rfl) ⟨653426, by rfl⟩ : syracuseStep 871235 = 1306853) B1306853
theorem B740333 : Blo 255820 740333 := bstep (se 3 (by rfl) ⟨138812, by rfl⟩ : syracuseStep 740333 = 277625) B277625
theorem B1297457 : Blo 255820 1297457 := bstep (se 2 (by rfl) ⟨486546, by rfl⟩ : syracuseStep 1297457 = 973093) B973093
theorem B576593 : Blo 255820 576593 := bstep (se 2 (by rfl) ⟨216222, by rfl⟩ : syracuseStep 576593 = 432445) B432445
theorem B871505 : Blo 255820 871505 := bstep (se 2 (by rfl) ⟨326814, by rfl⟩ : syracuseStep 871505 = 653629) B653629
theorem B576611 : Blo 255820 576611 := bstep (se 1 (by rfl) ⟨432458, by rfl⟩ : syracuseStep 576611 = 864917) B864917
theorem B1461509 : Blo 255820 1461509 := bstep (se 4 (by rfl) ⟨137016, by rfl⟩ : syracuseStep 1461509 = 274033) B274033
theorem B576881 : Blo 255820 576881 := bstep (se 2 (by rfl) ⟨216330, by rfl⟩ : syracuseStep 576881 = 432661) B432661
theorem B576899 : Blo 255820 576899 := bstep (se 1 (by rfl) ⟨432674, by rfl⟩ : syracuseStep 576899 = 865349) B865349
theorem B413203 : Blo 255820 413203 := bstep (se 1 (by rfl) ⟨309902, by rfl⟩ : syracuseStep 413203 = 619805) B619805
theorem B872045 : Blo 255820 872045 := bstep (se 3 (by rfl) ⟨163508, by rfl⟩ : syracuseStep 872045 = 327017) B327017
theorem B577169 : Blo 255820 577169 := bstep (se 2 (by rfl) ⟨216438, by rfl⟩ : syracuseStep 577169 = 432877) B432877
theorem B577187 : Blo 255820 577187 := bstep (se 1 (by rfl) ⟨432890, by rfl⟩ : syracuseStep 577187 = 865781) B865781
theorem B1756835 : Blo 255820 1756835 := bstep (se 1 (by rfl) ⟨1317626, by rfl⟩ : syracuseStep 1756835 = 2635253) B2635253
theorem B872099 : Blo 255820 872099 := bstep (se 1 (by rfl) ⟨654074, by rfl⟩ : syracuseStep 872099 = 1308149) B1308149
theorem B5557987 : Blo 255820 5557987 := bstep (se 1 (by rfl) ⟨4168490, by rfl⟩ : syracuseStep 5557987 = 8336981) B8336981
theorem B741155 : Blo 255820 741155 := bstep (se 1 (by rfl) ⟨555866, by rfl⟩ : syracuseStep 741155 = 1111733) B1111733
theorem B1757027 : Blo 255820 1757027 := bstep (se 1 (by rfl) ⟨1317770, by rfl⟩ : syracuseStep 1757027 = 2635541) B2635541
theorem B839555 : Blo 255820 839555 := bstep (se 1 (by rfl) ⟨629666, by rfl⟩ : syracuseStep 839555 = 1259333) B1259333
theorem B577457 : Blo 255820 577457 := bstep (se 2 (by rfl) ⟨216546, by rfl⟩ : syracuseStep 577457 = 433093) B433093
theorem B872369 : Blo 255820 872369 := bstep (se 2 (by rfl) ⟨327138, by rfl⟩ : syracuseStep 872369 = 654277) B654277
theorem B577475 : Blo 255820 577475 := bstep (se 1 (by rfl) ⟨433106, by rfl⟩ : syracuseStep 577475 = 866213) B866213
theorem B839629 : Blo 255820 839629 := bstep (se 3 (by rfl) ⟨157430, by rfl⟩ : syracuseStep 839629 = 314861) B314861
theorem B413651 : Blo 255820 413651 := bstep (se 1 (by rfl) ⟨310238, by rfl⟩ : syracuseStep 413651 = 620477) B620477
theorem B577745 : Blo 255820 577745 := bstep (se 2 (by rfl) ⟨216654, by rfl⟩ : syracuseStep 577745 = 433309) B433309
theorem B577763 : Blo 255820 577763 := bstep (se 1 (by rfl) ⟨433322, by rfl⟩ : syracuseStep 577763 = 866645) B866645
theorem B872909 : Blo 255820 872909 := bstep (se 3 (by rfl) ⟨163670, by rfl⟩ : syracuseStep 872909 = 327341) B327341
theorem B1298915 : Blo 255820 1298915 := bstep (se 1 (by rfl) ⟨974186, by rfl⟩ : syracuseStep 1298915 = 1948373) B1948373
theorem B578033 : Blo 255820 578033 := bstep (se 2 (by rfl) ⟨216762, by rfl⟩ : syracuseStep 578033 = 433525) B433525
theorem B414209 : Blo 255820 414209 := bstep (se 2 (by rfl) ⟨155328, by rfl⟩ : syracuseStep 414209 = 310657) B310657
theorem B578051 : Blo 255820 578051 := bstep (se 1 (by rfl) ⟨433538, by rfl⟩ : syracuseStep 578051 = 867077) B867077
theorem B872963 : Blo 255820 872963 := bstep (se 1 (by rfl) ⟨654722, by rfl⟩ : syracuseStep 872963 = 1309445) B1309445
theorem B1102385 : Blo 255820 1102385 := bstep (se 2 (by rfl) ⟨413394, by rfl⟩ : syracuseStep 1102385 = 826789) B826789
theorem B1168013 : Blo 255820 1168013 := bstep (se 3 (by rfl) ⟨219002, by rfl⟩ : syracuseStep 1168013 = 438005) B438005
theorem B1233571 : Blo 255820 1233571 := bstep (se 1 (by rfl) ⟨925178, by rfl⟩ : syracuseStep 1233571 = 1850357) B1850357
theorem B414433 : Blo 255820 414433 := bstep (se 2 (by rfl) ⟨155412, by rfl⟩ : syracuseStep 414433 = 310825) B310825
theorem B1168141 : Blo 255820 1168141 := bstep (se 3 (by rfl) ⟨219026, by rfl⟩ : syracuseStep 1168141 = 438053) B438053
theorem B578321 : Blo 255820 578321 := bstep (se 2 (by rfl) ⟨216870, by rfl⟩ : syracuseStep 578321 = 433741) B433741
theorem B873233 : Blo 255820 873233 := bstep (se 2 (by rfl) ⟨327462, by rfl⟩ : syracuseStep 873233 = 654925) B654925
theorem B414497 : Blo 255820 414497 := bstep (se 2 (by rfl) ⟨155436, by rfl⟩ : syracuseStep 414497 = 310873) B310873
theorem B578339 : Blo 255820 578339 := bstep (se 1 (by rfl) ⟨433754, by rfl⟩ : syracuseStep 578339 = 867509) B867509
theorem B414625 : Blo 255820 414625 := bstep (se 2 (by rfl) ⟨155484, by rfl⟩ : syracuseStep 414625 = 310969) B310969
theorem B349105 : Blo 255820 349105 := bstep (se 2 (by rfl) ⟨130914, by rfl⟩ : syracuseStep 349105 = 261829) B261829
theorem B2937869 : Blo 255820 2937869 := bstep (se 3 (by rfl) ⟨550850, by rfl⟩ : syracuseStep 2937869 = 1101701) B1101701
theorem B578609 : Blo 255820 578609 := bstep (se 2 (by rfl) ⟨216978, by rfl⟩ : syracuseStep 578609 = 433957) B433957
theorem B578627 : Blo 255820 578627 := bstep (se 1 (by rfl) ⟨433970, by rfl⟩ : syracuseStep 578627 = 867941) B867941
theorem B971939 : Blo 255820 971939 := bstep (se 1 (by rfl) ⟨728954, by rfl⟩ : syracuseStep 971939 = 1457909) B1457909
theorem B1299725 : Blo 255820 1299725 := bstep (se 3 (by rfl) ⟨243698, by rfl⟩ : syracuseStep 1299725 = 487397) B487397
theorem B873773 : Blo 255820 873773 := bstep (se 3 (by rfl) ⟨163832, by rfl⟩ : syracuseStep 873773 = 327665) B327665
theorem B578897 : Blo 255820 578897 := bstep (se 2 (by rfl) ⟨217086, by rfl⟩ : syracuseStep 578897 = 434173) B434173
theorem B578915 : Blo 255820 578915 := bstep (se 1 (by rfl) ⟨434186, by rfl⟩ : syracuseStep 578915 = 868373) B868373
theorem B873827 : Blo 255820 873827 := bstep (se 1 (by rfl) ⟨655370, by rfl⟩ : syracuseStep 873827 = 1310741) B1310741
theorem B579185 : Blo 255820 579185 := bstep (se 2 (by rfl) ⟨217194, by rfl⟩ : syracuseStep 579185 = 434389) B434389
theorem B874097 : Blo 255820 874097 := bstep (se 2 (by rfl) ⟨327786, by rfl⟩ : syracuseStep 874097 = 655573) B655573
theorem B579203 : Blo 255820 579203 := bstep (se 1 (by rfl) ⟨434402, by rfl⟩ : syracuseStep 579203 = 868805) B868805
theorem B546545 : Blo 255820 546545 := bstep (se 2 (by rfl) ⟨204954, by rfl⟩ : syracuseStep 546545 = 409909) B409909
theorem B546563 : Blo 255820 546563 := bstep (se 1 (by rfl) ⟨409922, by rfl⟩ : syracuseStep 546563 = 819845) B819845
theorem B1103651 : Blo 255820 1103651 := bstep (se 1 (by rfl) ⟨827738, by rfl⟩ : syracuseStep 1103651 = 1655477) B1655477
theorem B972593 : Blo 255820 972593 := bstep (se 2 (by rfl) ⟨364722, by rfl⟩ : syracuseStep 972593 = 729445) B729445
theorem B1234801 : Blo 255820 1234801 := bstep (se 2 (by rfl) ⟨463050, by rfl⟩ : syracuseStep 1234801 = 926101) B926101
theorem B579473 : Blo 255820 579473 := bstep (se 2 (by rfl) ⟨217302, by rfl⟩ : syracuseStep 579473 = 434605) B434605
theorem B579491 : Blo 255820 579491 := bstep (se 1 (by rfl) ⟨434618, by rfl⟩ : syracuseStep 579491 = 869237) B869237
theorem B874637 : Blo 255820 874637 := bstep (se 3 (by rfl) ⟨163994, by rfl⟩ : syracuseStep 874637 = 327989) B327989
theorem B579761 : Blo 255820 579761 := bstep (se 2 (by rfl) ⟨217410, by rfl⟩ : syracuseStep 579761 = 434821) B434821
theorem B579779 : Blo 255820 579779 := bstep (se 1 (by rfl) ⟨434834, by rfl⟩ : syracuseStep 579779 = 869669) B869669
theorem B874691 : Blo 255820 874691 := bstep (se 1 (by rfl) ⟨656018, by rfl⟩ : syracuseStep 874691 = 1312037) B1312037
theorem B580049 : Blo 255820 580049 := bstep (se 2 (by rfl) ⟨217518, by rfl⟩ : syracuseStep 580049 = 435037) B435037
theorem B874961 : Blo 255820 874961 := bstep (se 2 (by rfl) ⟨328110, by rfl⟩ : syracuseStep 874961 = 656221) B656221
theorem B580067 : Blo 255820 580067 := bstep (se 1 (by rfl) ⟨435050, by rfl⟩ : syracuseStep 580067 = 870101) B870101
theorem B1661573 : Blo 255820 1661573 := bstep (se 4 (by rfl) ⟨155772, by rfl⟩ : syracuseStep 1661573 = 311545) B311545
theorem B580337 : Blo 255820 580337 := bstep (se 2 (by rfl) ⟨217626, by rfl⟩ : syracuseStep 580337 = 435253) B435253
theorem B383747 : Blo 255820 383747 := bstep (se 1 (by rfl) ⟨287810, by rfl⟩ : syracuseStep 383747 = 575621) B575621
theorem B580355 : Blo 255820 580355 := bstep (se 1 (by rfl) ⟨435266, by rfl⟩ : syracuseStep 580355 = 870533) B870533
theorem B383777 : Blo 255820 383777 := bstep (se 2 (by rfl) ⟨143916, by rfl⟩ : syracuseStep 383777 = 287833) B287833
theorem B383795 : Blo 255820 383795 := bstep (se 1 (by rfl) ⟨287846, by rfl⟩ : syracuseStep 383795 = 575693) B575693
theorem B383825 : Blo 255820 383825 := bstep (se 2 (by rfl) ⟨143934, by rfl⟩ : syracuseStep 383825 = 287869) B287869
theorem B383843 : Blo 255820 383843 := bstep (se 1 (by rfl) ⟨287882, by rfl⟩ : syracuseStep 383843 = 575765) B575765
theorem B1858403 : Blo 255820 1858403 := bstep (se 1 (by rfl) ⟨1393802, by rfl⟩ : syracuseStep 1858403 = 2787605) B2787605
theorem B383873 : Blo 255820 383873 := bstep (se 2 (by rfl) ⟨143952, by rfl⟩ : syracuseStep 383873 = 287905) B287905
theorem B383891 : Blo 255820 383891 := bstep (se 1 (by rfl) ⟨287918, by rfl⟩ : syracuseStep 383891 = 575837) B575837
theorem B383921 : Blo 255820 383921 := bstep (se 2 (by rfl) ⟨143970, by rfl⟩ : syracuseStep 383921 = 287941) B287941
theorem B383939 : Blo 255820 383939 := bstep (se 1 (by rfl) ⟨287954, by rfl⟩ : syracuseStep 383939 = 575909) B575909
theorem B547793 : Blo 255820 547793 := bstep (se 2 (by rfl) ⟨205422, by rfl⟩ : syracuseStep 547793 = 410845) B410845
theorem B383969 : Blo 255820 383969 := bstep (se 2 (by rfl) ⟨143988, by rfl⟩ : syracuseStep 383969 = 287977) B287977
theorem B875501 : Blo 255820 875501 := bstep (se 3 (by rfl) ⟨164156, by rfl⟩ : syracuseStep 875501 = 328313) B328313
theorem B2481137 : Blo 255820 2481137 := bstep (se 2 (by rfl) ⟨930426, by rfl⟩ : syracuseStep 2481137 = 1860853) B1860853
theorem B383987 : Blo 255820 383987 := bstep (se 1 (by rfl) ⟨287990, by rfl⟩ : syracuseStep 383987 = 575981) B575981
theorem B384017 : Blo 255820 384017 := bstep (se 2 (by rfl) ⟨144006, by rfl⟩ : syracuseStep 384017 = 288013) B288013
theorem B580625 : Blo 255820 580625 := bstep (se 2 (by rfl) ⟨217734, by rfl⟩ : syracuseStep 580625 = 435469) B435469
theorem B384035 : Blo 255820 384035 := bstep (se 1 (by rfl) ⟨288026, by rfl⟩ : syracuseStep 384035 = 576053) B576053
theorem B580643 : Blo 255820 580643 := bstep (se 1 (by rfl) ⟨435482, by rfl⟩ : syracuseStep 580643 = 870965) B870965
theorem B875555 : Blo 255820 875555 := bstep (se 1 (by rfl) ⟨656666, by rfl⟩ : syracuseStep 875555 = 1313333) B1313333
theorem B384065 : Blo 255820 384065 := bstep (se 2 (by rfl) ⟨144024, by rfl⟩ : syracuseStep 384065 = 288049) B288049
theorem B384083 : Blo 255820 384083 := bstep (se 1 (by rfl) ⟨288062, by rfl⟩ : syracuseStep 384083 = 576125) B576125
theorem B384113 : Blo 255820 384113 := bstep (se 2 (by rfl) ⟨144042, by rfl⟩ : syracuseStep 384113 = 288085) B288085
theorem B384131 : Blo 255820 384131 := bstep (se 1 (by rfl) ⟨288098, by rfl⟩ : syracuseStep 384131 = 576197) B576197
theorem B384161 : Blo 255820 384161 := bstep (se 2 (by rfl) ⟨144060, by rfl⟩ : syracuseStep 384161 = 288121) B288121
theorem B384179 : Blo 255820 384179 := bstep (se 1 (by rfl) ⟨288134, by rfl⟩ : syracuseStep 384179 = 576269) B576269
theorem B384209 : Blo 255820 384209 := bstep (se 2 (by rfl) ⟨144078, by rfl⟩ : syracuseStep 384209 = 288157) B288157
theorem B384227 : Blo 255820 384227 := bstep (se 1 (by rfl) ⟨288170, by rfl⟩ : syracuseStep 384227 = 576341) B576341
theorem B974051 : Blo 255820 974051 := bstep (se 1 (by rfl) ⟨730538, by rfl⟩ : syracuseStep 974051 = 1461077) B1461077
theorem B974065 : Blo 255820 974065 := bstep (se 2 (by rfl) ⟨365274, by rfl⟩ : syracuseStep 974065 = 730549) B730549
theorem B384257 : Blo 255820 384257 := bstep (se 2 (by rfl) ⟨144096, by rfl⟩ : syracuseStep 384257 = 288193) B288193
theorem B384275 : Blo 255820 384275 := bstep (se 1 (by rfl) ⟨288206, by rfl⟩ : syracuseStep 384275 = 576413) B576413
theorem B384305 : Blo 255820 384305 := bstep (se 2 (by rfl) ⟨144114, by rfl⟩ : syracuseStep 384305 = 288229) B288229
theorem B580913 : Blo 255820 580913 := bstep (se 2 (by rfl) ⟨217842, by rfl⟩ : syracuseStep 580913 = 435685) B435685
theorem B875825 : Blo 255820 875825 := bstep (se 2 (by rfl) ⟨328434, by rfl⟩ : syracuseStep 875825 = 656869) B656869
theorem B384323 : Blo 255820 384323 := bstep (se 1 (by rfl) ⟨288242, by rfl⟩ : syracuseStep 384323 = 576485) B576485
theorem B580931 : Blo 255820 580931 := bstep (se 1 (by rfl) ⟨435698, by rfl⟩ : syracuseStep 580931 = 871397) B871397
theorem B384353 : Blo 255820 384353 := bstep (se 2 (by rfl) ⟨144132, by rfl⟩ : syracuseStep 384353 = 288265) B288265
theorem B1236323 : Blo 255820 1236323 := bstep (se 1 (by rfl) ⟨927242, by rfl⟩ : syracuseStep 1236323 = 1854485) B1854485
theorem B2809187 : Blo 255820 2809187 := bstep (se 1 (by rfl) ⟨2106890, by rfl⟩ : syracuseStep 2809187 = 4213781) B4213781
theorem B384371 : Blo 255820 384371 := bstep (se 1 (by rfl) ⟨288278, by rfl⟩ : syracuseStep 384371 = 576557) B576557
theorem B384401 : Blo 255820 384401 := bstep (se 2 (by rfl) ⟨144150, by rfl⟩ : syracuseStep 384401 = 288301) B288301
theorem B384419 : Blo 255820 384419 := bstep (se 1 (by rfl) ⟨288314, by rfl⟩ : syracuseStep 384419 = 576629) B576629
theorem B384449 : Blo 255820 384449 := bstep (se 2 (by rfl) ⟨144168, by rfl⟩ : syracuseStep 384449 = 288337) B288337
theorem B384467 : Blo 255820 384467 := bstep (se 1 (by rfl) ⟨288350, by rfl⟩ : syracuseStep 384467 = 576701) B576701
theorem B384497 : Blo 255820 384497 := bstep (se 2 (by rfl) ⟨144186, by rfl⟩ : syracuseStep 384497 = 288373) B288373
theorem B384515 : Blo 255820 384515 := bstep (se 1 (by rfl) ⟨288386, by rfl⟩ : syracuseStep 384515 = 576773) B576773
theorem B2481677 : Blo 255820 2481677 := bstep (se 3 (by rfl) ⟨465314, by rfl⟩ : syracuseStep 2481677 = 930629) B930629
theorem B384545 : Blo 255820 384545 := bstep (se 2 (by rfl) ⟨144204, by rfl⟩ : syracuseStep 384545 = 288409) B288409
theorem B384563 : Blo 255820 384563 := bstep (se 1 (by rfl) ⟨288422, by rfl⟩ : syracuseStep 384563 = 576845) B576845
theorem B384593 : Blo 255820 384593 := bstep (se 2 (by rfl) ⟨144222, by rfl⟩ : syracuseStep 384593 = 288445) B288445
theorem B581201 : Blo 255820 581201 := bstep (se 2 (by rfl) ⟨217950, by rfl⟩ : syracuseStep 581201 = 435901) B435901
theorem B384611 : Blo 255820 384611 := bstep (se 1 (by rfl) ⟨288458, by rfl⟩ : syracuseStep 384611 = 576917) B576917
theorem B581219 : Blo 255820 581219 := bstep (se 1 (by rfl) ⟨435914, by rfl⟩ : syracuseStep 581219 = 871829) B871829
theorem B1039985 : Blo 255820 1039985 := bstep (se 2 (by rfl) ⟨389994, by rfl⟩ : syracuseStep 1039985 = 779989) B779989
theorem B384641 : Blo 255820 384641 := bstep (se 2 (by rfl) ⟨144240, by rfl⟩ : syracuseStep 384641 = 288481) B288481
theorem B646787 : Blo 255820 646787 := bstep (se 1 (by rfl) ⟨485090, by rfl⟩ : syracuseStep 646787 = 970181) B970181
theorem B384659 : Blo 255820 384659 := bstep (se 1 (by rfl) ⟨288494, by rfl⟩ : syracuseStep 384659 = 576989) B576989
theorem B384689 : Blo 255820 384689 := bstep (se 2 (by rfl) ⟨144258, by rfl⟩ : syracuseStep 384689 = 288517) B288517
theorem B384707 : Blo 255820 384707 := bstep (se 1 (by rfl) ⟨288530, by rfl⟩ : syracuseStep 384707 = 577061) B577061
theorem B384737 : Blo 255820 384737 := bstep (se 2 (by rfl) ⟨144276, by rfl⟩ : syracuseStep 384737 = 288553) B288553
theorem B384755 : Blo 255820 384755 := bstep (se 1 (by rfl) ⟨288566, by rfl⟩ : syracuseStep 384755 = 577133) B577133
theorem B450307 : Blo 255820 450307 := bstep (se 1 (by rfl) ⟨337730, by rfl⟩ : syracuseStep 450307 = 675461) B675461
theorem B384785 : Blo 255820 384785 := bstep (se 2 (by rfl) ⟨144294, by rfl⟩ : syracuseStep 384785 = 288589) B288589
theorem B384803 : Blo 255820 384803 := bstep (se 1 (by rfl) ⟨288602, by rfl⟩ : syracuseStep 384803 = 577205) B577205
theorem B384833 : Blo 255820 384833 := bstep (se 2 (by rfl) ⟨144312, by rfl⟩ : syracuseStep 384833 = 288625) B288625
theorem B876365 : Blo 255820 876365 := bstep (se 3 (by rfl) ⟨164318, by rfl⟩ : syracuseStep 876365 = 328637) B328637
theorem B384851 : Blo 255820 384851 := bstep (se 1 (by rfl) ⟨288638, by rfl⟩ : syracuseStep 384851 = 577277) B577277
theorem B384881 : Blo 255820 384881 := bstep (se 2 (by rfl) ⟨144330, by rfl⟩ : syracuseStep 384881 = 288661) B288661
theorem B2940785 : Blo 255820 2940785 := bstep (se 2 (by rfl) ⟨1102794, by rfl⟩ : syracuseStep 2940785 = 2205589) B2205589
theorem B581489 : Blo 255820 581489 := bstep (se 2 (by rfl) ⟨218058, by rfl⟩ : syracuseStep 581489 = 436117) B436117
theorem B384899 : Blo 255820 384899 := bstep (se 1 (by rfl) ⟨288674, by rfl⟩ : syracuseStep 384899 = 577349) B577349
theorem B581507 : Blo 255820 581507 := bstep (se 1 (by rfl) ⟨436130, by rfl⟩ : syracuseStep 581507 = 872261) B872261
theorem B876419 : Blo 255820 876419 := bstep (se 1 (by rfl) ⟨657314, by rfl⟩ : syracuseStep 876419 = 1314629) B1314629
theorem B384929 : Blo 255820 384929 := bstep (se 2 (by rfl) ⟨144348, by rfl⟩ : syracuseStep 384929 = 288697) B288697
theorem B384947 : Blo 255820 384947 := bstep (se 1 (by rfl) ⟨288710, by rfl⟩ : syracuseStep 384947 = 577421) B577421
theorem B384977 : Blo 255820 384977 := bstep (se 2 (by rfl) ⟨144366, by rfl⟩ : syracuseStep 384977 = 288733) B288733
theorem B384995 : Blo 255820 384995 := bstep (se 1 (by rfl) ⟨288746, by rfl⟩ : syracuseStep 384995 = 577493) B577493
theorem B385025 : Blo 255820 385025 := bstep (se 2 (by rfl) ⟨144384, by rfl⟩ : syracuseStep 385025 = 288769) B288769
theorem B385043 : Blo 255820 385043 := bstep (se 1 (by rfl) ⟨288782, by rfl⟩ : syracuseStep 385043 = 577565) B577565
theorem B385073 : Blo 255820 385073 := bstep (se 2 (by rfl) ⟨144402, by rfl⟩ : syracuseStep 385073 = 288805) B288805
theorem B385091 : Blo 255820 385091 := bstep (se 1 (by rfl) ⟨288818, by rfl⟩ : syracuseStep 385091 = 577637) B577637
theorem B385121 : Blo 255820 385121 := bstep (se 2 (by rfl) ⟨144420, by rfl⟩ : syracuseStep 385121 = 288841) B288841
theorem B1302641 : Blo 255820 1302641 := bstep (se 2 (by rfl) ⟨488490, by rfl⟩ : syracuseStep 1302641 = 976981) B976981
theorem B385139 : Blo 255820 385139 := bstep (se 1 (by rfl) ⟨288854, by rfl⟩ : syracuseStep 385139 = 577709) B577709
theorem B385169 : Blo 255820 385169 := bstep (se 2 (by rfl) ⟨144438, by rfl⟩ : syracuseStep 385169 = 288877) B288877
theorem B581777 : Blo 255820 581777 := bstep (se 2 (by rfl) ⟨218166, by rfl⟩ : syracuseStep 581777 = 436333) B436333
theorem B876689 : Blo 255820 876689 := bstep (se 2 (by rfl) ⟨328758, by rfl⟩ : syracuseStep 876689 = 657517) B657517
theorem B385187 : Blo 255820 385187 := bstep (se 1 (by rfl) ⟨288890, by rfl⟩ : syracuseStep 385187 = 577781) B577781
theorem B581795 : Blo 255820 581795 := bstep (se 1 (by rfl) ⟨436346, by rfl⟩ : syracuseStep 581795 = 872693) B872693
theorem B385217 : Blo 255820 385217 := bstep (se 2 (by rfl) ⟨144456, by rfl⟩ : syracuseStep 385217 = 288913) B288913
theorem B385235 : Blo 255820 385235 := bstep (se 1 (by rfl) ⟨288926, by rfl⟩ : syracuseStep 385235 = 577853) B577853
theorem B385265 : Blo 255820 385265 := bstep (se 2 (by rfl) ⟨144474, by rfl⟩ : syracuseStep 385265 = 288949) B288949
theorem B385283 : Blo 255820 385283 := bstep (se 1 (by rfl) ⟨288962, by rfl⟩ : syracuseStep 385283 = 577925) B577925
theorem B385313 : Blo 255820 385313 := bstep (se 2 (by rfl) ⟨144492, by rfl⟩ : syracuseStep 385313 = 288985) B288985
theorem B385331 : Blo 255820 385331 := bstep (se 1 (by rfl) ⟨288998, by rfl⟩ : syracuseStep 385331 = 577997) B577997
theorem B385361 : Blo 255820 385361 := bstep (se 2 (by rfl) ⟨144510, by rfl⟩ : syracuseStep 385361 = 289021) B289021
theorem B385379 : Blo 255820 385379 := bstep (se 1 (by rfl) ⟨289034, by rfl⟩ : syracuseStep 385379 = 578069) B578069
theorem B385409 : Blo 255820 385409 := bstep (se 2 (by rfl) ⟨144528, by rfl⟩ : syracuseStep 385409 = 289057) B289057
theorem B385427 : Blo 255820 385427 := bstep (se 1 (by rfl) ⟨289070, by rfl⟩ : syracuseStep 385427 = 578141) B578141
theorem B385457 : Blo 255820 385457 := bstep (se 2 (by rfl) ⟨144546, by rfl⟩ : syracuseStep 385457 = 289093) B289093
theorem B582065 : Blo 255820 582065 := bstep (se 2 (by rfl) ⟨218274, by rfl⟩ : syracuseStep 582065 = 436549) B436549
theorem B385475 : Blo 255820 385475 := bstep (se 1 (by rfl) ⟨289106, by rfl⟩ : syracuseStep 385475 = 578213) B578213
theorem B582083 : Blo 255820 582083 := bstep (se 1 (by rfl) ⟨436562, by rfl⟩ : syracuseStep 582083 = 873125) B873125
theorem B385505 : Blo 255820 385505 := bstep (se 2 (by rfl) ⟨144564, by rfl⟩ : syracuseStep 385505 = 289129) B289129
theorem B549347 : Blo 255820 549347 := bstep (se 1 (by rfl) ⟨412010, by rfl⟩ : syracuseStep 549347 = 824021) B824021
theorem B385523 : Blo 255820 385523 := bstep (se 1 (by rfl) ⟨289142, by rfl⟩ : syracuseStep 385523 = 578285) B578285
theorem B385553 : Blo 255820 385553 := bstep (se 2 (by rfl) ⟨144582, by rfl⟩ : syracuseStep 385553 = 289165) B289165
theorem B385571 : Blo 255820 385571 := bstep (se 1 (by rfl) ⟨289178, by rfl⟩ : syracuseStep 385571 = 578357) B578357
theorem B1663523 : Blo 255820 1663523 := bstep (se 1 (by rfl) ⟨1247642, by rfl⟩ : syracuseStep 1663523 = 2495285) B2495285
theorem B385601 : Blo 255820 385601 := bstep (se 2 (by rfl) ⟨144600, by rfl⟩ : syracuseStep 385601 = 289201) B289201
theorem B647747 : Blo 255820 647747 := bstep (se 1 (by rfl) ⟨485810, by rfl⟩ : syracuseStep 647747 = 971621) B971621
theorem B385619 : Blo 255820 385619 := bstep (se 1 (by rfl) ⟨289214, by rfl⟩ : syracuseStep 385619 = 578429) B578429
theorem B385649 : Blo 255820 385649 := bstep (se 2 (by rfl) ⟨144618, by rfl⟩ : syracuseStep 385649 = 289237) B289237
theorem B352883 : Blo 255820 352883 := bstep (se 1 (by rfl) ⟨264662, by rfl⟩ : syracuseStep 352883 = 529325) B529325
theorem B385667 : Blo 255820 385667 := bstep (se 1 (by rfl) ⟨289250, by rfl⟩ : syracuseStep 385667 = 578501) B578501
theorem B385697 : Blo 255820 385697 := bstep (se 2 (by rfl) ⟨144636, by rfl⟩ : syracuseStep 385697 = 289273) B289273
theorem B975523 : Blo 255820 975523 := bstep (se 1 (by rfl) ⟨731642, by rfl⟩ : syracuseStep 975523 = 1463285) B1463285
theorem B385715 : Blo 255820 385715 := bstep (se 1 (by rfl) ⟨289286, by rfl⟩ : syracuseStep 385715 = 578573) B578573
theorem B385745 : Blo 255820 385745 := bstep (se 2 (by rfl) ⟨144654, by rfl⟩ : syracuseStep 385745 = 289309) B289309
theorem B582353 : Blo 255820 582353 := bstep (se 2 (by rfl) ⟨218382, by rfl⟩ : syracuseStep 582353 = 436765) B436765
theorem B385763 : Blo 255820 385763 := bstep (se 1 (by rfl) ⟨289322, by rfl⟩ : syracuseStep 385763 = 578645) B578645
theorem B582371 : Blo 255820 582371 := bstep (se 1 (by rfl) ⟨436778, by rfl⟩ : syracuseStep 582371 = 873557) B873557
theorem B385793 : Blo 255820 385793 := bstep (se 2 (by rfl) ⟨144672, by rfl⟩ : syracuseStep 385793 = 289345) B289345
theorem B647939 : Blo 255820 647939 := bstep (se 1 (by rfl) ⟨485954, by rfl⟩ : syracuseStep 647939 = 971909) B971909
theorem B385811 : Blo 255820 385811 := bstep (se 1 (by rfl) ⟨289358, by rfl⟩ : syracuseStep 385811 = 578717) B578717
theorem B385841 : Blo 255820 385841 := bstep (se 2 (by rfl) ⟨144690, by rfl⟩ : syracuseStep 385841 = 289381) B289381
theorem B385859 : Blo 255820 385859 := bstep (se 1 (by rfl) ⟨289394, by rfl⟩ : syracuseStep 385859 = 578789) B578789
theorem B385889 : Blo 255820 385889 := bstep (se 2 (by rfl) ⟨144708, by rfl⟩ : syracuseStep 385889 = 289417) B289417
theorem B385907 : Blo 255820 385907 := bstep (se 1 (by rfl) ⟨289430, by rfl⟩ : syracuseStep 385907 = 578861) B578861
theorem B385937 : Blo 255820 385937 := bstep (se 2 (by rfl) ⟨144726, by rfl⟩ : syracuseStep 385937 = 289453) B289453
theorem B385955 : Blo 255820 385955 := bstep (se 1 (by rfl) ⟨289466, by rfl⟩ : syracuseStep 385955 = 578933) B578933
theorem B385985 : Blo 255820 385985 := bstep (se 2 (by rfl) ⟨144744, by rfl⟩ : syracuseStep 385985 = 289489) B289489
theorem B1467341 : Blo 255820 1467341 := bstep (se 3 (by rfl) ⟨275126, by rfl⟩ : syracuseStep 1467341 = 550253) B550253
theorem B386003 : Blo 255820 386003 := bstep (se 1 (by rfl) ⟨289502, by rfl⟩ : syracuseStep 386003 = 579005) B579005
theorem B386033 : Blo 255820 386033 := bstep (se 2 (by rfl) ⟨144762, by rfl⟩ : syracuseStep 386033 = 289525) B289525
theorem B582641 : Blo 255820 582641 := bstep (se 2 (by rfl) ⟨218490, by rfl⟩ : syracuseStep 582641 = 436981) B436981
theorem B386051 : Blo 255820 386051 := bstep (se 1 (by rfl) ⟨289538, by rfl⟩ : syracuseStep 386051 = 579077) B579077
theorem B582659 : Blo 255820 582659 := bstep (se 1 (by rfl) ⟨436994, by rfl⟩ : syracuseStep 582659 = 873989) B873989
theorem B386081 : Blo 255820 386081 := bstep (se 2 (by rfl) ⟨144780, by rfl⟩ : syracuseStep 386081 = 289561) B289561
theorem B386099 : Blo 255820 386099 := bstep (se 1 (by rfl) ⟨289574, by rfl⟩ : syracuseStep 386099 = 579149) B579149
theorem B386129 : Blo 255820 386129 := bstep (se 2 (by rfl) ⟨144798, by rfl⟩ : syracuseStep 386129 = 289597) B289597
theorem B386147 : Blo 255820 386147 := bstep (se 1 (by rfl) ⟨289610, by rfl⟩ : syracuseStep 386147 = 579221) B579221
theorem B386177 : Blo 255820 386177 := bstep (se 2 (by rfl) ⟨144816, by rfl⟩ : syracuseStep 386177 = 289633) B289633
theorem B386195 : Blo 255820 386195 := bstep (se 1 (by rfl) ⟨289646, by rfl⟩ : syracuseStep 386195 = 579293) B579293
theorem B386225 : Blo 255820 386225 := bstep (se 2 (by rfl) ⟨144834, by rfl⟩ : syracuseStep 386225 = 289669) B289669
theorem B287923 : Blo 255820 287923 := bstep (se 1 (by rfl) ⟨215942, by rfl⟩ : syracuseStep 287923 = 431885) B431885
theorem B386243 : Blo 255820 386243 := bstep (se 1 (by rfl) ⟨289682, by rfl⟩ : syracuseStep 386243 = 579365) B579365
theorem B386273 : Blo 255820 386273 := bstep (se 2 (by rfl) ⟨144852, by rfl⟩ : syracuseStep 386273 = 289705) B289705
theorem B386291 : Blo 255820 386291 := bstep (se 1 (by rfl) ⟨289718, by rfl⟩ : syracuseStep 386291 = 579437) B579437
theorem B386321 : Blo 255820 386321 := bstep (se 2 (by rfl) ⟨144870, by rfl⟩ : syracuseStep 386321 = 289741) B289741
theorem B582929 : Blo 255820 582929 := bstep (se 2 (by rfl) ⟨218598, by rfl⟩ : syracuseStep 582929 = 437197) B437197
theorem B386339 : Blo 255820 386339 := bstep (se 1 (by rfl) ⟨289754, by rfl⟩ : syracuseStep 386339 = 579509) B579509
theorem B582947 : Blo 255820 582947 := bstep (se 1 (by rfl) ⟨437210, by rfl⟩ : syracuseStep 582947 = 874421) B874421
theorem B1238321 : Blo 255820 1238321 := bstep (se 2 (by rfl) ⟨464370, by rfl⟩ : syracuseStep 1238321 = 928741) B928741
theorem B386369 : Blo 255820 386369 := bstep (se 2 (by rfl) ⟨144888, by rfl⟩ : syracuseStep 386369 = 289777) B289777
theorem B288067 : Blo 255820 288067 := bstep (se 1 (by rfl) ⟨216050, by rfl⟩ : syracuseStep 288067 = 432101) B432101
theorem B386387 : Blo 255820 386387 := bstep (se 1 (by rfl) ⟨289790, by rfl⟩ : syracuseStep 386387 = 579581) B579581
theorem B386417 : Blo 255820 386417 := bstep (se 2 (by rfl) ⟨144906, by rfl⟩ : syracuseStep 386417 = 289813) B289813
theorem B386435 : Blo 255820 386435 := bstep (se 1 (by rfl) ⟨289826, by rfl⟩ : syracuseStep 386435 = 579653) B579653
theorem B1107341 : Blo 255820 1107341 := bstep (se 3 (by rfl) ⟨207626, by rfl⟩ : syracuseStep 1107341 = 415253) B415253
theorem B386465 : Blo 255820 386465 := bstep (se 2 (by rfl) ⟨144924, by rfl⟩ : syracuseStep 386465 = 289849) B289849
theorem B386483 : Blo 255820 386483 := bstep (se 1 (by rfl) ⟨289862, by rfl⟩ : syracuseStep 386483 = 579725) B579725
theorem B386513 : Blo 255820 386513 := bstep (se 2 (by rfl) ⟨144942, by rfl⟩ : syracuseStep 386513 = 289885) B289885
theorem B288211 : Blo 255820 288211 := bstep (se 1 (by rfl) ⟨216158, by rfl⟩ : syracuseStep 288211 = 432317) B432317
theorem B386531 : Blo 255820 386531 := bstep (se 1 (by rfl) ⟨289898, by rfl⟩ : syracuseStep 386531 = 579797) B579797
theorem B386561 : Blo 255820 386561 := bstep (se 2 (by rfl) ⟨144960, by rfl⟩ : syracuseStep 386561 = 289921) B289921
theorem B386579 : Blo 255820 386579 := bstep (se 1 (by rfl) ⟨289934, by rfl⟩ : syracuseStep 386579 = 579869) B579869
theorem B1304099 : Blo 255820 1304099 := bstep (se 1 (by rfl) ⟨978074, by rfl⟩ : syracuseStep 1304099 = 1956149) B1956149
theorem B386609 : Blo 255820 386609 := bstep (se 2 (by rfl) ⟨144978, by rfl⟩ : syracuseStep 386609 = 289957) B289957
theorem B583217 : Blo 255820 583217 := bstep (se 2 (by rfl) ⟨218706, by rfl⟩ : syracuseStep 583217 = 437413) B437413
theorem B386627 : Blo 255820 386627 := bstep (se 1 (by rfl) ⟨289970, by rfl⟩ : syracuseStep 386627 = 579941) B579941
theorem B583235 : Blo 255820 583235 := bstep (se 1 (by rfl) ⟨437426, by rfl⟩ : syracuseStep 583235 = 874853) B874853
theorem B386657 : Blo 255820 386657 := bstep (se 2 (by rfl) ⟨144996, by rfl⟩ : syracuseStep 386657 = 289993) B289993
theorem B288355 : Blo 255820 288355 := bstep (se 1 (by rfl) ⟨216266, by rfl⟩ : syracuseStep 288355 = 432533) B432533
theorem B386675 : Blo 255820 386675 := bstep (se 1 (by rfl) ⟨290006, by rfl⟩ : syracuseStep 386675 = 580013) B580013
theorem B386705 : Blo 255820 386705 := bstep (se 2 (by rfl) ⟨145014, by rfl⟩ : syracuseStep 386705 = 290029) B290029
theorem B386723 : Blo 255820 386723 := bstep (se 1 (by rfl) ⟨290042, by rfl⟩ : syracuseStep 386723 = 580085) B580085
theorem B648881 : Blo 255820 648881 := bstep (se 2 (by rfl) ⟨243330, by rfl⟩ : syracuseStep 648881 = 486661) B486661
theorem B386753 : Blo 255820 386753 := bstep (se 2 (by rfl) ⟨145032, by rfl⟩ : syracuseStep 386753 = 290065) B290065
theorem B386771 : Blo 255820 386771 := bstep (se 1 (by rfl) ⟨290078, by rfl⟩ : syracuseStep 386771 = 580157) B580157
theorem B648931 : Blo 255820 648931 := bstep (se 1 (by rfl) ⟨486698, by rfl⟩ : syracuseStep 648931 = 973397) B973397
theorem B386801 : Blo 255820 386801 := bstep (se 2 (by rfl) ⟨145050, by rfl⟩ : syracuseStep 386801 = 290101) B290101
theorem B288499 : Blo 255820 288499 := bstep (se 1 (by rfl) ⟨216374, by rfl⟩ : syracuseStep 288499 = 432749) B432749
theorem B386819 : Blo 255820 386819 := bstep (se 1 (by rfl) ⟨290114, by rfl⟩ : syracuseStep 386819 = 580229) B580229
theorem B386849 : Blo 255820 386849 := bstep (se 2 (by rfl) ⟨145068, by rfl⟩ : syracuseStep 386849 = 290137) B290137
theorem B386867 : Blo 255820 386867 := bstep (se 1 (by rfl) ⟨290150, by rfl⟩ : syracuseStep 386867 = 580301) B580301
theorem B386897 : Blo 255820 386897 := bstep (se 2 (by rfl) ⟨145086, by rfl⟩ : syracuseStep 386897 = 290173) B290173
theorem B583505 : Blo 255820 583505 := bstep (se 2 (by rfl) ⟨218814, by rfl⟩ : syracuseStep 583505 = 437629) B437629
theorem B255827 : Blo 255820 255827 := bstep (se 1 (by rfl) ⟨191870, by rfl⟩ : syracuseStep 255827 = 383741) B383741
theorem B255843 : Blo 255820 255843 := bstep (se 1 (by rfl) ⟨191882, by rfl⟩ : syracuseStep 255843 = 383765) B383765
theorem B386915 : Blo 255820 386915 := bstep (se 1 (by rfl) ⟨290186, by rfl⟩ : syracuseStep 386915 = 580373) B580373
theorem B583523 : Blo 255820 583523 := bstep (se 1 (by rfl) ⟨437642, by rfl⟩ : syracuseStep 583523 = 875285) B875285
theorem B649073 : Blo 255820 649073 := bstep (se 2 (by rfl) ⟨243402, by rfl⟩ : syracuseStep 649073 = 486805) B486805
theorem B255859 : Blo 255820 255859 := bstep (se 1 (by rfl) ⟨191894, by rfl⟩ : syracuseStep 255859 = 383789) B383789
theorem B386945 : Blo 255820 386945 := bstep (se 2 (by rfl) ⟨145104, by rfl⟩ : syracuseStep 386945 = 290209) B290209
theorem B255875 : Blo 255820 255875 := bstep (se 1 (by rfl) ⟨191906, by rfl⟩ : syracuseStep 255875 = 383813) B383813
theorem B288643 : Blo 255820 288643 := bstep (se 1 (by rfl) ⟨216482, by rfl⟩ : syracuseStep 288643 = 432965) B432965
theorem B255891 : Blo 255820 255891 := bstep (se 1 (by rfl) ⟨191918, by rfl⟩ : syracuseStep 255891 = 383837) B383837
theorem B386963 : Blo 255820 386963 := bstep (se 1 (by rfl) ⟨290222, by rfl⟩ : syracuseStep 386963 = 580445) B580445
theorem B255907 : Blo 255820 255907 := bstep (se 1 (by rfl) ⟨191930, by rfl⟩ : syracuseStep 255907 = 383861) B383861
theorem B386993 : Blo 255820 386993 := bstep (se 2 (by rfl) ⟨145122, by rfl⟩ : syracuseStep 386993 = 290245) B290245
theorem B255923 : Blo 255820 255923 := bstep (se 1 (by rfl) ⟨191942, by rfl⟩ : syracuseStep 255923 = 383885) B383885
theorem B255939 : Blo 255820 255939 := bstep (se 1 (by rfl) ⟨191954, by rfl⟩ : syracuseStep 255939 = 383909) B383909
theorem B387011 : Blo 255820 387011 := bstep (se 1 (by rfl) ⟨290258, by rfl⟩ : syracuseStep 387011 = 580517) B580517
theorem B255955 : Blo 255820 255955 := bstep (se 1 (by rfl) ⟨191966, by rfl⟩ : syracuseStep 255955 = 383933) B383933
theorem B387041 : Blo 255820 387041 := bstep (se 2 (by rfl) ⟨145140, by rfl⟩ : syracuseStep 387041 = 290281) B290281
theorem B255971 : Blo 255820 255971 := bstep (se 1 (by rfl) ⟨191978, by rfl⟩ : syracuseStep 255971 = 383957) B383957
theorem B255987 : Blo 255820 255987 := bstep (se 1 (by rfl) ⟨191990, by rfl⟩ : syracuseStep 255987 = 383981) B383981
theorem B387059 : Blo 255820 387059 := bstep (se 1 (by rfl) ⟨290294, by rfl⟩ : syracuseStep 387059 = 580589) B580589
theorem B256003 : Blo 255820 256003 := bstep (se 1 (by rfl) ⟨192002, by rfl⟩ : syracuseStep 256003 = 384005) B384005
theorem B387089 : Blo 255820 387089 := bstep (se 2 (by rfl) ⟨145158, by rfl⟩ : syracuseStep 387089 = 290317) B290317
theorem B256019 : Blo 255820 256019 := bstep (se 1 (by rfl) ⟨192014, by rfl⟩ : syracuseStep 256019 = 384029) B384029
theorem B288787 : Blo 255820 288787 := bstep (se 1 (by rfl) ⟨216590, by rfl⟩ : syracuseStep 288787 = 433181) B433181
theorem B256035 : Blo 255820 256035 := bstep (se 1 (by rfl) ⟨192026, by rfl⟩ : syracuseStep 256035 = 384053) B384053
theorem B387107 : Blo 255820 387107 := bstep (se 1 (by rfl) ⟨290330, by rfl⟩ : syracuseStep 387107 = 580661) B580661
theorem B256051 : Blo 255820 256051 := bstep (se 1 (by rfl) ⟨192038, by rfl⟩ : syracuseStep 256051 = 384077) B384077
theorem B387137 : Blo 255820 387137 := bstep (se 2 (by rfl) ⟨145176, by rfl⟩ : syracuseStep 387137 = 290353) B290353
theorem B256067 : Blo 255820 256067 := bstep (se 1 (by rfl) ⟨192050, by rfl⟩ : syracuseStep 256067 = 384101) B384101
theorem B256083 : Blo 255820 256083 := bstep (se 1 (by rfl) ⟨192062, by rfl⟩ : syracuseStep 256083 = 384125) B384125
theorem B387155 : Blo 255820 387155 := bstep (se 1 (by rfl) ⟨290366, by rfl⟩ : syracuseStep 387155 = 580733) B580733
theorem B256099 : Blo 255820 256099 := bstep (se 1 (by rfl) ⟨192074, by rfl⟩ : syracuseStep 256099 = 384149) B384149
theorem B616547 : Blo 255820 616547 := bstep (se 1 (by rfl) ⟨462410, by rfl⟩ : syracuseStep 616547 = 924821) B924821
theorem B387185 : Blo 255820 387185 := bstep (se 2 (by rfl) ⟨145194, by rfl⟩ : syracuseStep 387185 = 290389) B290389
theorem B583793 : Blo 255820 583793 := bstep (se 2 (by rfl) ⟨218922, by rfl⟩ : syracuseStep 583793 = 437845) B437845
theorem B256115 : Blo 255820 256115 := bstep (se 1 (by rfl) ⟨192086, by rfl⟩ : syracuseStep 256115 = 384173) B384173
theorem B256131 : Blo 255820 256131 := bstep (se 1 (by rfl) ⟨192098, by rfl⟩ : syracuseStep 256131 = 384197) B384197
theorem B387203 : Blo 255820 387203 := bstep (se 1 (by rfl) ⟨290402, by rfl⟩ : syracuseStep 387203 = 580805) B580805
theorem B583811 : Blo 255820 583811 := bstep (se 1 (by rfl) ⟨437858, by rfl⟩ : syracuseStep 583811 = 875717) B875717
theorem B256147 : Blo 255820 256147 := bstep (se 1 (by rfl) ⟨192110, by rfl⟩ : syracuseStep 256147 = 384221) B384221
theorem B387233 : Blo 255820 387233 := bstep (se 2 (by rfl) ⟨145212, by rfl⟩ : syracuseStep 387233 = 290425) B290425
theorem B256163 : Blo 255820 256163 := bstep (se 1 (by rfl) ⟨192122, by rfl⟩ : syracuseStep 256163 = 384245) B384245
theorem B288931 : Blo 255820 288931 := bstep (se 1 (by rfl) ⟨216698, by rfl⟩ : syracuseStep 288931 = 433397) B433397
theorem B256179 : Blo 255820 256179 := bstep (se 1 (by rfl) ⟨192134, by rfl⟩ : syracuseStep 256179 = 384269) B384269
theorem B387251 : Blo 255820 387251 := bstep (se 1 (by rfl) ⟨290438, by rfl⟩ : syracuseStep 387251 = 580877) B580877
theorem B256195 : Blo 255820 256195 := bstep (se 1 (by rfl) ⟨192146, by rfl⟩ : syracuseStep 256195 = 384293) B384293
theorem B1239245 : Blo 255820 1239245 := bstep (se 3 (by rfl) ⟨232358, by rfl⟩ : syracuseStep 1239245 = 464717) B464717
theorem B387281 : Blo 255820 387281 := bstep (se 2 (by rfl) ⟨145230, by rfl⟩ : syracuseStep 387281 = 290461) B290461
theorem B256211 : Blo 255820 256211 := bstep (se 1 (by rfl) ⟨192158, by rfl⟩ : syracuseStep 256211 = 384317) B384317
theorem B256227 : Blo 255820 256227 := bstep (se 1 (by rfl) ⟨192170, by rfl⟩ : syracuseStep 256227 = 384341) B384341
theorem B387299 : Blo 255820 387299 := bstep (se 1 (by rfl) ⟨290474, by rfl⟩ : syracuseStep 387299 = 580949) B580949
theorem B256243 : Blo 255820 256243 := bstep (se 1 (by rfl) ⟨192182, by rfl⟩ : syracuseStep 256243 = 384365) B384365
theorem B387329 : Blo 255820 387329 := bstep (se 2 (by rfl) ⟨145248, by rfl⟩ : syracuseStep 387329 = 290497) B290497
theorem B256259 : Blo 255820 256259 := bstep (se 1 (by rfl) ⟨192194, by rfl⟩ : syracuseStep 256259 = 384389) B384389
theorem B256275 : Blo 255820 256275 := bstep (se 1 (by rfl) ⟨192206, by rfl⟩ : syracuseStep 256275 = 384413) B384413
theorem B387347 : Blo 255820 387347 := bstep (se 1 (by rfl) ⟨290510, by rfl⟩ : syracuseStep 387347 = 581021) B581021
theorem B256291 : Blo 255820 256291 := bstep (se 1 (by rfl) ⟨192218, by rfl⟩ : syracuseStep 256291 = 384437) B384437
theorem B387377 : Blo 255820 387377 := bstep (se 2 (by rfl) ⟨145266, by rfl⟩ : syracuseStep 387377 = 290533) B290533
theorem B256307 : Blo 255820 256307 := bstep (se 1 (by rfl) ⟨192230, by rfl⟩ : syracuseStep 256307 = 384461) B384461
theorem B289075 : Blo 255820 289075 := bstep (se 1 (by rfl) ⟨216806, by rfl⟩ : syracuseStep 289075 = 433613) B433613
theorem B256323 : Blo 255820 256323 := bstep (se 1 (by rfl) ⟨192242, by rfl⟩ : syracuseStep 256323 = 384485) B384485
theorem B387395 : Blo 255820 387395 := bstep (se 1 (by rfl) ⟨290546, by rfl⟩ : syracuseStep 387395 = 581093) B581093
theorem B1304909 : Blo 255820 1304909 := bstep (se 3 (by rfl) ⟨244670, by rfl⟩ : syracuseStep 1304909 = 489341) B489341
theorem B256339 : Blo 255820 256339 := bstep (se 1 (by rfl) ⟨192254, by rfl⟩ : syracuseStep 256339 = 384509) B384509
theorem B387425 : Blo 255820 387425 := bstep (se 2 (by rfl) ⟨145284, by rfl⟩ : syracuseStep 387425 = 290569) B290569
theorem B256355 : Blo 255820 256355 := bstep (se 1 (by rfl) ⟨192266, by rfl⟩ : syracuseStep 256355 = 384533) B384533
theorem B256371 : Blo 255820 256371 := bstep (se 1 (by rfl) ⟨192278, by rfl⟩ : syracuseStep 256371 = 384557) B384557
theorem B387443 : Blo 255820 387443 := bstep (se 1 (by rfl) ⟨290582, by rfl⟩ : syracuseStep 387443 = 581165) B581165
theorem B256387 : Blo 255820 256387 := bstep (se 1 (by rfl) ⟨192290, by rfl⟩ : syracuseStep 256387 = 384581) B384581
theorem B387473 : Blo 255820 387473 := bstep (se 2 (by rfl) ⟨145302, by rfl⟩ : syracuseStep 387473 = 290605) B290605
theorem B256403 : Blo 255820 256403 := bstep (se 1 (by rfl) ⟨192302, by rfl⟩ : syracuseStep 256403 = 384605) B384605
theorem B584081 : Blo 255820 584081 := bstep (se 2 (by rfl) ⟨219030, by rfl⟩ : syracuseStep 584081 = 438061) B438061
theorem B256419 : Blo 255820 256419 := bstep (se 1 (by rfl) ⟨192314, by rfl⟩ : syracuseStep 256419 = 384629) B384629
theorem B387491 : Blo 255820 387491 := bstep (se 1 (by rfl) ⟨290618, by rfl⟩ : syracuseStep 387491 = 581237) B581237
theorem B584099 : Blo 255820 584099 := bstep (se 1 (by rfl) ⟨438074, by rfl⟩ : syracuseStep 584099 = 876149) B876149
theorem B256435 : Blo 255820 256435 := bstep (se 1 (by rfl) ⟨192326, by rfl⟩ : syracuseStep 256435 = 384653) B384653
theorem B387521 : Blo 255820 387521 := bstep (se 2 (by rfl) ⟨145320, by rfl⟩ : syracuseStep 387521 = 290641) B290641
theorem B256451 : Blo 255820 256451 := bstep (se 1 (by rfl) ⟨192338, by rfl⟩ : syracuseStep 256451 = 384677) B384677
theorem B289219 : Blo 255820 289219 := bstep (se 1 (by rfl) ⟨216914, by rfl⟩ : syracuseStep 289219 = 433829) B433829
theorem B256467 : Blo 255820 256467 := bstep (se 1 (by rfl) ⟨192350, by rfl⟩ : syracuseStep 256467 = 384701) B384701
theorem B387539 : Blo 255820 387539 := bstep (se 1 (by rfl) ⟨290654, by rfl⟩ : syracuseStep 387539 = 581309) B581309
theorem B256483 : Blo 255820 256483 := bstep (se 1 (by rfl) ⟨192362, by rfl⟩ : syracuseStep 256483 = 384725) B384725
theorem B1993187 : Blo 255820 1993187 := bstep (se 1 (by rfl) ⟨1494890, by rfl⟩ : syracuseStep 1993187 = 2989781) B2989781
theorem B387569 : Blo 255820 387569 := bstep (se 2 (by rfl) ⟨145338, by rfl⟩ : syracuseStep 387569 = 290677) B290677
theorem B256499 : Blo 255820 256499 := bstep (se 1 (by rfl) ⟨192374, by rfl⟩ : syracuseStep 256499 = 384749) B384749
theorem B256515 : Blo 255820 256515 := bstep (se 1 (by rfl) ⟨192386, by rfl⟩ : syracuseStep 256515 = 384773) B384773
theorem B387587 : Blo 255820 387587 := bstep (se 1 (by rfl) ⟨290690, by rfl⟩ : syracuseStep 387587 = 581381) B581381
theorem B256531 : Blo 255820 256531 := bstep (se 1 (by rfl) ⟨192398, by rfl⟩ : syracuseStep 256531 = 384797) B384797
theorem B387617 : Blo 255820 387617 := bstep (se 2 (by rfl) ⟨145356, by rfl⟩ : syracuseStep 387617 = 290713) B290713
theorem B256547 : Blo 255820 256547 := bstep (se 1 (by rfl) ⟨192410, by rfl⟩ : syracuseStep 256547 = 384821) B384821
theorem B256563 : Blo 255820 256563 := bstep (se 1 (by rfl) ⟨192422, by rfl⟩ : syracuseStep 256563 = 384845) B384845
theorem B387635 : Blo 255820 387635 := bstep (se 1 (by rfl) ⟨290726, by rfl⟩ : syracuseStep 387635 = 581453) B581453
theorem B256579 : Blo 255820 256579 := bstep (se 1 (by rfl) ⟨192434, by rfl⟩ : syracuseStep 256579 = 384869) B384869
theorem B387665 : Blo 255820 387665 := bstep (se 2 (by rfl) ⟨145374, by rfl⟩ : syracuseStep 387665 = 290749) B290749
theorem B256595 : Blo 255820 256595 := bstep (se 1 (by rfl) ⟨192446, by rfl⟩ : syracuseStep 256595 = 384893) B384893
theorem B289363 : Blo 255820 289363 := bstep (se 1 (by rfl) ⟨217022, by rfl⟩ : syracuseStep 289363 = 434045) B434045
theorem B256611 : Blo 255820 256611 := bstep (se 1 (by rfl) ⟨192458, by rfl⟩ : syracuseStep 256611 = 384917) B384917
theorem B387683 : Blo 255820 387683 := bstep (se 1 (by rfl) ⟨290762, by rfl⟩ : syracuseStep 387683 = 581525) B581525
theorem B256627 : Blo 255820 256627 := bstep (se 1 (by rfl) ⟨192470, by rfl⟩ : syracuseStep 256627 = 384941) B384941
theorem B387713 : Blo 255820 387713 := bstep (se 2 (by rfl) ⟨145392, by rfl⟩ : syracuseStep 387713 = 290785) B290785
theorem B256643 : Blo 255820 256643 := bstep (se 1 (by rfl) ⟨192482, by rfl⟩ : syracuseStep 256643 = 384965) B384965
theorem B551569 : Blo 255820 551569 := bstep (se 2 (by rfl) ⟨206838, by rfl⟩ : syracuseStep 551569 = 413677) B413677
theorem B256659 : Blo 255820 256659 := bstep (se 1 (by rfl) ⟨192494, by rfl⟩ : syracuseStep 256659 = 384989) B384989
theorem B387731 : Blo 255820 387731 := bstep (se 1 (by rfl) ⟨290798, by rfl⟩ : syracuseStep 387731 = 581597) B581597
theorem B256675 : Blo 255820 256675 := bstep (se 1 (by rfl) ⟨192506, by rfl⟩ : syracuseStep 256675 = 385013) B385013
theorem B387761 : Blo 255820 387761 := bstep (se 2 (by rfl) ⟨145410, by rfl⟩ : syracuseStep 387761 = 290821) B290821
theorem B584369 : Blo 255820 584369 := bstep (se 2 (by rfl) ⟨219138, by rfl⟩ : syracuseStep 584369 = 438277) B438277
theorem B256691 : Blo 255820 256691 := bstep (se 1 (by rfl) ⟨192518, by rfl⟩ : syracuseStep 256691 = 385037) B385037
theorem B256707 : Blo 255820 256707 := bstep (se 1 (by rfl) ⟨192530, by rfl⟩ : syracuseStep 256707 = 385061) B385061
theorem B387779 : Blo 255820 387779 := bstep (se 1 (by rfl) ⟨290834, by rfl⟩ : syracuseStep 387779 = 581669) B581669
theorem B584387 : Blo 255820 584387 := bstep (se 1 (by rfl) ⟨438290, by rfl⟩ : syracuseStep 584387 = 876581) B876581
theorem B256723 : Blo 255820 256723 := bstep (se 1 (by rfl) ⟨192542, by rfl⟩ : syracuseStep 256723 = 385085) B385085
theorem B387809 : Blo 255820 387809 := bstep (se 2 (by rfl) ⟨145428, by rfl⟩ : syracuseStep 387809 = 290857) B290857
theorem B256739 : Blo 255820 256739 := bstep (se 1 (by rfl) ⟨192554, by rfl⟩ : syracuseStep 256739 = 385109) B385109
theorem B289507 : Blo 255820 289507 := bstep (se 1 (by rfl) ⟨217130, by rfl⟩ : syracuseStep 289507 = 434261) B434261
theorem B256755 : Blo 255820 256755 := bstep (se 1 (by rfl) ⟨192566, by rfl⟩ : syracuseStep 256755 = 385133) B385133
theorem B387827 : Blo 255820 387827 := bstep (se 1 (by rfl) ⟨290870, by rfl⟩ : syracuseStep 387827 = 581741) B581741
theorem B256771 : Blo 255820 256771 := bstep (se 1 (by rfl) ⟨192578, by rfl⟩ : syracuseStep 256771 = 385157) B385157
theorem B387857 : Blo 255820 387857 := bstep (se 2 (by rfl) ⟨145446, by rfl⟩ : syracuseStep 387857 = 290893) B290893
theorem B256787 : Blo 255820 256787 := bstep (se 1 (by rfl) ⟨192590, by rfl⟩ : syracuseStep 256787 = 385181) B385181
theorem B256803 : Blo 255820 256803 := bstep (se 1 (by rfl) ⟨192602, by rfl⟩ : syracuseStep 256803 = 385205) B385205
theorem B387875 : Blo 255820 387875 := bstep (se 1 (by rfl) ⟨290906, by rfl⟩ : syracuseStep 387875 = 581813) B581813
theorem B256819 : Blo 255820 256819 := bstep (se 1 (by rfl) ⟨192614, by rfl⟩ : syracuseStep 256819 = 385229) B385229
theorem B387905 : Blo 255820 387905 := bstep (se 2 (by rfl) ⟨145464, by rfl⟩ : syracuseStep 387905 = 290929) B290929
theorem B256835 : Blo 255820 256835 := bstep (se 1 (by rfl) ⟨192626, by rfl⟩ : syracuseStep 256835 = 385253) B385253
theorem B977741 : Blo 255820 977741 := bstep (se 3 (by rfl) ⟨183326, by rfl⟩ : syracuseStep 977741 = 366653) B366653
theorem B650065 : Blo 255820 650065 := bstep (se 2 (by rfl) ⟨243774, by rfl⟩ : syracuseStep 650065 = 487549) B487549
theorem B256851 : Blo 255820 256851 := bstep (se 1 (by rfl) ⟨192638, by rfl⟩ : syracuseStep 256851 = 385277) B385277
theorem B387923 : Blo 255820 387923 := bstep (se 1 (by rfl) ⟨290942, by rfl⟩ : syracuseStep 387923 = 581885) B581885
theorem B256867 : Blo 255820 256867 := bstep (se 1 (by rfl) ⟨192650, by rfl⟩ : syracuseStep 256867 = 385301) B385301
theorem B387953 : Blo 255820 387953 := bstep (se 2 (by rfl) ⟨145482, by rfl⟩ : syracuseStep 387953 = 290965) B290965
theorem B256883 : Blo 255820 256883 := bstep (se 1 (by rfl) ⟨192662, by rfl⟩ : syracuseStep 256883 = 385325) B385325
theorem B289651 : Blo 255820 289651 := bstep (se 1 (by rfl) ⟨217238, by rfl⟩ : syracuseStep 289651 = 434477) B434477
theorem B256899 : Blo 255820 256899 := bstep (se 1 (by rfl) ⟨192674, by rfl⟩ : syracuseStep 256899 = 385349) B385349
theorem B387971 : Blo 255820 387971 := bstep (se 1 (by rfl) ⟨290978, by rfl⟩ : syracuseStep 387971 = 581957) B581957
theorem B256915 : Blo 255820 256915 := bstep (se 1 (by rfl) ⟨192686, by rfl⟩ : syracuseStep 256915 = 385373) B385373
theorem B388001 : Blo 255820 388001 := bstep (se 2 (by rfl) ⟨145500, by rfl⟩ : syracuseStep 388001 = 291001) B291001
theorem B256931 : Blo 255820 256931 := bstep (se 1 (by rfl) ⟨192698, by rfl⟩ : syracuseStep 256931 = 385397) B385397
theorem B355249 : Blo 255820 355249 := bstep (se 2 (by rfl) ⟨133218, by rfl⟩ : syracuseStep 355249 = 266437) B266437
theorem B256947 : Blo 255820 256947 := bstep (se 1 (by rfl) ⟨192710, by rfl⟩ : syracuseStep 256947 = 385421) B385421
theorem B388019 : Blo 255820 388019 := bstep (se 1 (by rfl) ⟨291014, by rfl⟩ : syracuseStep 388019 = 582029) B582029
theorem B256963 : Blo 255820 256963 := bstep (se 1 (by rfl) ⟨192722, by rfl⟩ : syracuseStep 256963 = 385445) B385445
theorem B388049 : Blo 255820 388049 := bstep (se 2 (by rfl) ⟨145518, by rfl⟩ : syracuseStep 388049 = 291037) B291037
theorem B256979 : Blo 255820 256979 := bstep (se 1 (by rfl) ⟨192734, by rfl⟩ : syracuseStep 256979 = 385469) B385469
theorem B256995 : Blo 255820 256995 := bstep (se 1 (by rfl) ⟨192746, by rfl⟩ : syracuseStep 256995 = 385493) B385493
theorem B388067 : Blo 255820 388067 := bstep (se 1 (by rfl) ⟨291050, by rfl⟩ : syracuseStep 388067 = 582101) B582101
theorem B257011 : Blo 255820 257011 := bstep (se 1 (by rfl) ⟨192758, by rfl⟩ : syracuseStep 257011 = 385517) B385517
theorem B388097 : Blo 255820 388097 := bstep (se 2 (by rfl) ⟨145536, by rfl⟩ : syracuseStep 388097 = 291073) B291073
theorem B257027 : Blo 255820 257027 := bstep (se 1 (by rfl) ⟨192770, by rfl⟩ : syracuseStep 257027 = 385541) B385541
theorem B289795 : Blo 255820 289795 := bstep (se 1 (by rfl) ⟨217346, by rfl⟩ : syracuseStep 289795 = 434693) B434693
theorem B257043 : Blo 255820 257043 := bstep (se 1 (by rfl) ⟨192782, by rfl⟩ : syracuseStep 257043 = 385565) B385565
theorem B388115 : Blo 255820 388115 := bstep (se 1 (by rfl) ⟨291086, by rfl⟩ : syracuseStep 388115 = 582173) B582173
theorem B257059 : Blo 255820 257059 := bstep (se 1 (by rfl) ⟨192794, by rfl⟩ : syracuseStep 257059 = 385589) B385589
theorem B388145 : Blo 255820 388145 := bstep (se 2 (by rfl) ⟨145554, by rfl⟩ : syracuseStep 388145 = 291109) B291109
theorem B257075 : Blo 255820 257075 := bstep (se 1 (by rfl) ⟨192806, by rfl⟩ : syracuseStep 257075 = 385613) B385613
theorem B257091 : Blo 255820 257091 := bstep (se 1 (by rfl) ⟨192818, by rfl⟩ : syracuseStep 257091 = 385637) B385637
theorem B388163 : Blo 255820 388163 := bstep (se 1 (by rfl) ⟨291122, by rfl⟩ : syracuseStep 388163 = 582245) B582245
theorem B257107 : Blo 255820 257107 := bstep (se 1 (by rfl) ⟨192830, by rfl⟩ : syracuseStep 257107 = 385661) B385661
theorem B388193 : Blo 255820 388193 := bstep (se 2 (by rfl) ⟨145572, by rfl⟩ : syracuseStep 388193 = 291145) B291145
theorem B650339 : Blo 255820 650339 := bstep (se 1 (by rfl) ⟨487754, by rfl⟩ : syracuseStep 650339 = 975509) B975509
theorem B257123 : Blo 255820 257123 := bstep (se 1 (by rfl) ⟨192842, by rfl⟩ : syracuseStep 257123 = 385685) B385685
theorem B257139 : Blo 255820 257139 := bstep (se 1 (by rfl) ⟨192854, by rfl⟩ : syracuseStep 257139 = 385709) B385709
theorem B388211 : Blo 255820 388211 := bstep (se 1 (by rfl) ⟨291158, by rfl⟩ : syracuseStep 388211 = 582317) B582317
theorem B257155 : Blo 255820 257155 := bstep (se 1 (by rfl) ⟨192866, by rfl⟩ : syracuseStep 257155 = 385733) B385733
theorem B1469573 : Blo 255820 1469573 := bstep (se 4 (by rfl) ⟨137772, by rfl⟩ : syracuseStep 1469573 = 275545) B275545
theorem B388241 : Blo 255820 388241 := bstep (se 2 (by rfl) ⟨145590, by rfl⟩ : syracuseStep 388241 = 291181) B291181
theorem B257171 : Blo 255820 257171 := bstep (se 1 (by rfl) ⟨192878, by rfl⟩ : syracuseStep 257171 = 385757) B385757
theorem B289939 : Blo 255820 289939 := bstep (se 1 (by rfl) ⟨217454, by rfl⟩ : syracuseStep 289939 = 434909) B434909
theorem B257187 : Blo 255820 257187 := bstep (se 1 (by rfl) ⟨192890, by rfl⟩ : syracuseStep 257187 = 385781) B385781
theorem B388259 : Blo 255820 388259 := bstep (se 1 (by rfl) ⟨291194, by rfl⟩ : syracuseStep 388259 = 582389) B582389
theorem B486577 : Blo 255820 486577 := bstep (se 2 (by rfl) ⟨182466, by rfl⟩ : syracuseStep 486577 = 364933) B364933
theorem B257203 : Blo 255820 257203 := bstep (se 1 (by rfl) ⟨192902, by rfl⟩ : syracuseStep 257203 = 385805) B385805
theorem B388289 : Blo 255820 388289 := bstep (se 2 (by rfl) ⟨145608, by rfl⟩ : syracuseStep 388289 = 291217) B291217
theorem B257219 : Blo 255820 257219 := bstep (se 1 (by rfl) ⟨192914, by rfl⟩ : syracuseStep 257219 = 385829) B385829
theorem B257235 : Blo 255820 257235 := bstep (se 1 (by rfl) ⟨192926, by rfl⟩ : syracuseStep 257235 = 385853) B385853
theorem B388307 : Blo 255820 388307 := bstep (se 1 (by rfl) ⟨291230, by rfl⟩ : syracuseStep 388307 = 582461) B582461
theorem B257251 : Blo 255820 257251 := bstep (se 1 (by rfl) ⟨192938, by rfl⟩ : syracuseStep 257251 = 385877) B385877
theorem B519409 : Blo 255820 519409 := bstep (se 2 (by rfl) ⟨194778, by rfl⟩ : syracuseStep 519409 = 389557) B389557
theorem B388337 : Blo 255820 388337 := bstep (se 2 (by rfl) ⟨145626, by rfl⟩ : syracuseStep 388337 = 291253) B291253
theorem B257267 : Blo 255820 257267 := bstep (se 1 (by rfl) ⟨192950, by rfl⟩ : syracuseStep 257267 = 385901) B385901
theorem B257283 : Blo 255820 257283 := bstep (se 1 (by rfl) ⟨192962, by rfl⟩ : syracuseStep 257283 = 385925) B385925
theorem B388355 : Blo 255820 388355 := bstep (se 1 (by rfl) ⟨291266, by rfl⟩ : syracuseStep 388355 = 582533) B582533
theorem B257299 : Blo 255820 257299 := bstep (se 1 (by rfl) ⟨192974, by rfl⟩ : syracuseStep 257299 = 385949) B385949
theorem B388385 : Blo 255820 388385 := bstep (se 2 (by rfl) ⟨145644, by rfl⟩ : syracuseStep 388385 = 291289) B291289
theorem B650531 : Blo 255820 650531 := bstep (se 1 (by rfl) ⟨487898, by rfl⟩ : syracuseStep 650531 = 975797) B975797
theorem B257315 : Blo 255820 257315 := bstep (se 1 (by rfl) ⟨192986, by rfl⟩ : syracuseStep 257315 = 385973) B385973
theorem B290083 : Blo 255820 290083 := bstep (se 1 (by rfl) ⟨217562, by rfl⟩ : syracuseStep 290083 = 435125) B435125
theorem B617777 : Blo 255820 617777 := bstep (se 2 (by rfl) ⟨231666, by rfl⟩ : syracuseStep 617777 = 463333) B463333
theorem B257331 : Blo 255820 257331 := bstep (se 1 (by rfl) ⟨192998, by rfl⟩ : syracuseStep 257331 = 385997) B385997
theorem B388403 : Blo 255820 388403 := bstep (se 1 (by rfl) ⟨291302, by rfl⟩ : syracuseStep 388403 = 582605) B582605
theorem B257347 : Blo 255820 257347 := bstep (se 1 (by rfl) ⟨193010, by rfl⟩ : syracuseStep 257347 = 386021) B386021
theorem B388433 : Blo 255820 388433 := bstep (se 2 (by rfl) ⟨145662, by rfl⟩ : syracuseStep 388433 = 291325) B291325
theorem B257363 : Blo 255820 257363 := bstep (se 1 (by rfl) ⟨193022, by rfl⟩ : syracuseStep 257363 = 386045) B386045
theorem B257379 : Blo 255820 257379 := bstep (se 1 (by rfl) ⟨193034, by rfl⟩ : syracuseStep 257379 = 386069) B386069
theorem B388451 : Blo 255820 388451 := bstep (se 1 (by rfl) ⟨291338, by rfl⟩ : syracuseStep 388451 = 582677) B582677
theorem B257395 : Blo 255820 257395 := bstep (se 1 (by rfl) ⟨193046, by rfl⟩ : syracuseStep 257395 = 386093) B386093
theorem B388481 : Blo 255820 388481 := bstep (se 2 (by rfl) ⟨145680, by rfl⟩ : syracuseStep 388481 = 291361) B291361
theorem B257411 : Blo 255820 257411 := bstep (se 1 (by rfl) ⟨193058, by rfl⟩ : syracuseStep 257411 = 386117) B386117
theorem B257427 : Blo 255820 257427 := bstep (se 1 (by rfl) ⟨193070, by rfl⟩ : syracuseStep 257427 = 386141) B386141
theorem B388499 : Blo 255820 388499 := bstep (se 1 (by rfl) ⟨291374, by rfl⟩ : syracuseStep 388499 = 582749) B582749
theorem B257443 : Blo 255820 257443 := bstep (se 1 (by rfl) ⟨193082, by rfl⟩ : syracuseStep 257443 = 386165) B386165
theorem B388529 : Blo 255820 388529 := bstep (se 2 (by rfl) ⟨145698, by rfl⟩ : syracuseStep 388529 = 291397) B291397
theorem B257459 : Blo 255820 257459 := bstep (se 1 (by rfl) ⟨193094, by rfl⟩ : syracuseStep 257459 = 386189) B386189
theorem B290227 : Blo 255820 290227 := bstep (se 1 (by rfl) ⟨217670, by rfl⟩ : syracuseStep 290227 = 435341) B435341
theorem B257475 : Blo 255820 257475 := bstep (se 1 (by rfl) ⟨193106, by rfl⟩ : syracuseStep 257475 = 386213) B386213
theorem B388547 : Blo 255820 388547 := bstep (se 1 (by rfl) ⟨291410, by rfl⟩ : syracuseStep 388547 = 582821) B582821
theorem B257491 : Blo 255820 257491 := bstep (se 1 (by rfl) ⟨193118, by rfl⟩ : syracuseStep 257491 = 386237) B386237
theorem B388577 : Blo 255820 388577 := bstep (se 2 (by rfl) ⟨145716, by rfl⟩ : syracuseStep 388577 = 291433) B291433
theorem B257507 : Blo 255820 257507 := bstep (se 1 (by rfl) ⟨193130, by rfl⟩ : syracuseStep 257507 = 386261) B386261
theorem B257523 : Blo 255820 257523 := bstep (se 1 (by rfl) ⟨193142, by rfl⟩ : syracuseStep 257523 = 386285) B386285
theorem B388595 : Blo 255820 388595 := bstep (se 1 (by rfl) ⟨291446, by rfl⟩ : syracuseStep 388595 = 582893) B582893
theorem B257539 : Blo 255820 257539 := bstep (se 1 (by rfl) ⟨193154, by rfl⟩ : syracuseStep 257539 = 386309) B386309
theorem B388625 : Blo 255820 388625 := bstep (se 2 (by rfl) ⟨145734, by rfl⟩ : syracuseStep 388625 = 291469) B291469
theorem B257555 : Blo 255820 257555 := bstep (se 1 (by rfl) ⟨193166, by rfl⟩ : syracuseStep 257555 = 386333) B386333
theorem B257571 : Blo 255820 257571 := bstep (se 1 (by rfl) ⟨193178, by rfl⟩ : syracuseStep 257571 = 386357) B386357
theorem B388643 : Blo 255820 388643 := bstep (se 1 (by rfl) ⟨291482, by rfl⟩ : syracuseStep 388643 = 582965) B582965
theorem B257587 : Blo 255820 257587 := bstep (se 1 (by rfl) ⟨193190, by rfl⟩ : syracuseStep 257587 = 386381) B386381
theorem B2780725 : Blo 255820 2780725 := bstep (se 5 (by rfl) ⟨130346, by rfl⟩ : syracuseStep 2780725 = 260693) B260693
theorem B388673 : Blo 255820 388673 := bstep (se 2 (by rfl) ⟨145752, by rfl⟩ : syracuseStep 388673 = 291505) B291505
theorem B257603 : Blo 255820 257603 := bstep (se 1 (by rfl) ⟨193202, by rfl⟩ : syracuseStep 257603 = 386405) B386405
theorem B290371 : Blo 255820 290371 := bstep (se 1 (by rfl) ⟨217778, by rfl⟩ : syracuseStep 290371 = 435557) B435557
theorem B257619 : Blo 255820 257619 := bstep (se 1 (by rfl) ⟨193214, by rfl⟩ : syracuseStep 257619 = 386429) B386429
theorem B388691 : Blo 255820 388691 := bstep (se 1 (by rfl) ⟨291518, by rfl⟩ : syracuseStep 388691 = 583037) B583037
theorem B257635 : Blo 255820 257635 := bstep (se 1 (by rfl) ⟨193226, by rfl⟩ : syracuseStep 257635 = 386453) B386453
theorem B388721 : Blo 255820 388721 := bstep (se 2 (by rfl) ⟨145770, by rfl⟩ : syracuseStep 388721 = 291541) B291541
theorem B257651 : Blo 255820 257651 := bstep (se 1 (by rfl) ⟨193238, by rfl⟩ : syracuseStep 257651 = 386477) B386477
theorem B257667 : Blo 255820 257667 := bstep (se 1 (by rfl) ⟨193250, by rfl⟩ : syracuseStep 257667 = 386501) B386501
theorem B388739 : Blo 255820 388739 := bstep (se 1 (by rfl) ⟨291554, by rfl⟩ : syracuseStep 388739 = 583109) B583109
theorem B257683 : Blo 255820 257683 := bstep (se 1 (by rfl) ⟨193262, by rfl⟩ : syracuseStep 257683 = 386525) B386525
theorem B388769 : Blo 255820 388769 := bstep (se 2 (by rfl) ⟨145788, by rfl⟩ : syracuseStep 388769 = 291577) B291577
theorem B257699 : Blo 255820 257699 := bstep (se 1 (by rfl) ⟨193274, by rfl⟩ : syracuseStep 257699 = 386549) B386549
theorem B257715 : Blo 255820 257715 := bstep (se 1 (by rfl) ⟨193286, by rfl⟩ : syracuseStep 257715 = 386573) B386573
theorem B388787 : Blo 255820 388787 := bstep (se 1 (by rfl) ⟨291590, by rfl⟩ : syracuseStep 388787 = 583181) B583181
theorem B257731 : Blo 255820 257731 := bstep (se 1 (by rfl) ⟨193298, by rfl⟩ : syracuseStep 257731 = 386597) B386597
theorem B388817 : Blo 255820 388817 := bstep (se 2 (by rfl) ⟨145806, by rfl⟩ : syracuseStep 388817 = 291613) B291613
theorem B257747 : Blo 255820 257747 := bstep (se 1 (by rfl) ⟨193310, by rfl⟩ : syracuseStep 257747 = 386621) B386621
theorem B290515 : Blo 255820 290515 := bstep (se 1 (by rfl) ⟨217886, by rfl⟩ : syracuseStep 290515 = 435773) B435773
theorem B257763 : Blo 255820 257763 := bstep (se 1 (by rfl) ⟨193322, by rfl⟩ : syracuseStep 257763 = 386645) B386645
theorem B388835 : Blo 255820 388835 := bstep (se 1 (by rfl) ⟨291626, by rfl⟩ : syracuseStep 388835 = 583253) B583253
theorem B257779 : Blo 255820 257779 := bstep (se 1 (by rfl) ⟨193334, by rfl⟩ : syracuseStep 257779 = 386669) B386669
theorem B388865 : Blo 255820 388865 := bstep (se 2 (by rfl) ⟨145824, by rfl⟩ : syracuseStep 388865 = 291649) B291649
theorem B257795 : Blo 255820 257795 := bstep (se 1 (by rfl) ⟨193346, by rfl⟩ : syracuseStep 257795 = 386693) B386693
theorem B257811 : Blo 255820 257811 := bstep (se 1 (by rfl) ⟨193358, by rfl⟩ : syracuseStep 257811 = 386717) B386717
theorem B388883 : Blo 255820 388883 := bstep (se 1 (by rfl) ⟨291662, by rfl⟩ : syracuseStep 388883 = 583325) B583325
theorem B257827 : Blo 255820 257827 := bstep (se 1 (by rfl) ⟨193370, by rfl⟩ : syracuseStep 257827 = 386741) B386741
theorem B1470257 : Blo 255820 1470257 := bstep (se 2 (by rfl) ⟨551346, by rfl⟩ : syracuseStep 1470257 = 1102693) B1102693
theorem B388913 : Blo 255820 388913 := bstep (se 2 (by rfl) ⟨145842, by rfl⟩ : syracuseStep 388913 = 291685) B291685
theorem B257843 : Blo 255820 257843 := bstep (se 1 (by rfl) ⟨193382, by rfl⟩ : syracuseStep 257843 = 386765) B386765
theorem B257859 : Blo 255820 257859 := bstep (se 1 (by rfl) ⟨193394, by rfl⟩ : syracuseStep 257859 = 386789) B386789
theorem B388931 : Blo 255820 388931 := bstep (se 1 (by rfl) ⟨291698, by rfl⟩ : syracuseStep 388931 = 583397) B583397
theorem B257875 : Blo 255820 257875 := bstep (se 1 (by rfl) ⟨193406, by rfl⟩ : syracuseStep 257875 = 386813) B386813
theorem B388961 : Blo 255820 388961 := bstep (se 2 (by rfl) ⟨145860, by rfl⟩ : syracuseStep 388961 = 291721) B291721
theorem B257891 : Blo 255820 257891 := bstep (se 1 (by rfl) ⟨193418, by rfl⟩ : syracuseStep 257891 = 386837) B386837
theorem B290659 : Blo 255820 290659 := bstep (se 1 (by rfl) ⟨217994, by rfl⟩ : syracuseStep 290659 = 435989) B435989
theorem B257907 : Blo 255820 257907 := bstep (se 1 (by rfl) ⟨193430, by rfl⟩ : syracuseStep 257907 = 386861) B386861
theorem B388979 : Blo 255820 388979 := bstep (se 1 (by rfl) ⟨291734, by rfl⟩ : syracuseStep 388979 = 583469) B583469
theorem B257923 : Blo 255820 257923 := bstep (se 1 (by rfl) ⟨193442, by rfl⟩ : syracuseStep 257923 = 386885) B386885
theorem B389009 : Blo 255820 389009 := bstep (se 2 (by rfl) ⟨145878, by rfl⟩ : syracuseStep 389009 = 291757) B291757
theorem B257939 : Blo 255820 257939 := bstep (se 1 (by rfl) ⟨193454, by rfl⟩ : syracuseStep 257939 = 386909) B386909
theorem B257955 : Blo 255820 257955 := bstep (se 1 (by rfl) ⟨193466, by rfl⟩ : syracuseStep 257955 = 386933) B386933
theorem B389027 : Blo 255820 389027 := bstep (se 1 (by rfl) ⟨291770, by rfl⟩ : syracuseStep 389027 = 583541) B583541
theorem B257971 : Blo 255820 257971 := bstep (se 1 (by rfl) ⟨193478, by rfl⟩ : syracuseStep 257971 = 386957) B386957
theorem B389057 : Blo 255820 389057 := bstep (se 2 (by rfl) ⟨145896, by rfl⟩ : syracuseStep 389057 = 291793) B291793
theorem B257987 : Blo 255820 257987 := bstep (se 1 (by rfl) ⟨193490, by rfl⟩ : syracuseStep 257987 = 386981) B386981
theorem B258003 : Blo 255820 258003 := bstep (se 1 (by rfl) ⟨193502, by rfl⟩ : syracuseStep 258003 = 387005) B387005
theorem B389075 : Blo 255820 389075 := bstep (se 1 (by rfl) ⟨291806, by rfl⟩ : syracuseStep 389075 = 583613) B583613
theorem B258019 : Blo 255820 258019 := bstep (se 1 (by rfl) ⟨193514, by rfl⟩ : syracuseStep 258019 = 387029) B387029
theorem B389105 : Blo 255820 389105 := bstep (se 2 (by rfl) ⟨145914, by rfl⟩ : syracuseStep 389105 = 291829) B291829
theorem B258035 : Blo 255820 258035 := bstep (se 1 (by rfl) ⟨193526, by rfl⟩ : syracuseStep 258035 = 387053) B387053
theorem B290803 : Blo 255820 290803 := bstep (se 1 (by rfl) ⟨218102, by rfl⟩ : syracuseStep 290803 = 436205) B436205
theorem B258051 : Blo 255820 258051 := bstep (se 1 (by rfl) ⟨193538, by rfl⟩ : syracuseStep 258051 = 387077) B387077
theorem B389123 : Blo 255820 389123 := bstep (se 1 (by rfl) ⟨291842, by rfl⟩ : syracuseStep 389123 = 583685) B583685
theorem B258067 : Blo 255820 258067 := bstep (se 1 (by rfl) ⟨193550, by rfl⟩ : syracuseStep 258067 = 387101) B387101
theorem B389153 : Blo 255820 389153 := bstep (se 2 (by rfl) ⟨145932, by rfl⟩ : syracuseStep 389153 = 291865) B291865
theorem B258083 : Blo 255820 258083 := bstep (se 1 (by rfl) ⟨193562, by rfl⟩ : syracuseStep 258083 = 387125) B387125
theorem B258099 : Blo 255820 258099 := bstep (se 1 (by rfl) ⟨193574, by rfl⟩ : syracuseStep 258099 = 387149) B387149
theorem B389171 : Blo 255820 389171 := bstep (se 1 (by rfl) ⟨291878, by rfl⟩ : syracuseStep 389171 = 583757) B583757
theorem B258115 : Blo 255820 258115 := bstep (se 1 (by rfl) ⟨193586, by rfl⟩ : syracuseStep 258115 = 387173) B387173
theorem B389201 : Blo 255820 389201 := bstep (se 2 (by rfl) ⟨145950, by rfl⟩ : syracuseStep 389201 = 291901) B291901
theorem B258131 : Blo 255820 258131 := bstep (se 1 (by rfl) ⟨193598, by rfl⟩ : syracuseStep 258131 = 387197) B387197
theorem B258147 : Blo 255820 258147 := bstep (se 1 (by rfl) ⟨193610, by rfl⟩ : syracuseStep 258147 = 387221) B387221
theorem B389219 : Blo 255820 389219 := bstep (se 1 (by rfl) ⟨291914, by rfl⟩ : syracuseStep 389219 = 583829) B583829
theorem B258163 : Blo 255820 258163 := bstep (se 1 (by rfl) ⟨193622, by rfl⟩ : syracuseStep 258163 = 387245) B387245
theorem B389249 : Blo 255820 389249 := bstep (se 2 (by rfl) ⟨145968, by rfl⟩ : syracuseStep 389249 = 291937) B291937
theorem B258179 : Blo 255820 258179 := bstep (se 1 (by rfl) ⟨193634, by rfl⟩ : syracuseStep 258179 = 387269) B387269
theorem B290947 : Blo 255820 290947 := bstep (se 1 (by rfl) ⟨218210, by rfl⟩ : syracuseStep 290947 = 436421) B436421
theorem B258195 : Blo 255820 258195 := bstep (se 1 (by rfl) ⟨193646, by rfl⟩ : syracuseStep 258195 = 387293) B387293
theorem B389267 : Blo 255820 389267 := bstep (se 1 (by rfl) ⟨291950, by rfl⟩ : syracuseStep 389267 = 583901) B583901
theorem B258211 : Blo 255820 258211 := bstep (se 1 (by rfl) ⟨193658, by rfl⟩ : syracuseStep 258211 = 387317) B387317
theorem B389297 : Blo 255820 389297 := bstep (se 2 (by rfl) ⟨145986, by rfl⟩ : syracuseStep 389297 = 291973) B291973
theorem B258227 : Blo 255820 258227 := bstep (se 1 (by rfl) ⟨193670, by rfl⟩ : syracuseStep 258227 = 387341) B387341
theorem B258243 : Blo 255820 258243 := bstep (se 1 (by rfl) ⟨193682, by rfl⟩ : syracuseStep 258243 = 387365) B387365
theorem B389315 : Blo 255820 389315 := bstep (se 1 (by rfl) ⟨291986, by rfl⟩ : syracuseStep 389315 = 583973) B583973
theorem B487633 : Blo 255820 487633 := bstep (se 2 (by rfl) ⟨182862, by rfl⟩ : syracuseStep 487633 = 365725) B365725
theorem B651473 : Blo 255820 651473 := bstep (se 2 (by rfl) ⟨244302, by rfl⟩ : syracuseStep 651473 = 488605) B488605
theorem B258259 : Blo 255820 258259 := bstep (se 1 (by rfl) ⟨193694, by rfl⟩ : syracuseStep 258259 = 387389) B387389
theorem B389345 : Blo 255820 389345 := bstep (se 2 (by rfl) ⟨146004, by rfl⟩ : syracuseStep 389345 = 292009) B292009
theorem B258275 : Blo 255820 258275 := bstep (se 1 (by rfl) ⟨193706, by rfl⟩ : syracuseStep 258275 = 387413) B387413
theorem B258291 : Blo 255820 258291 := bstep (se 1 (by rfl) ⟨193718, by rfl⟩ : syracuseStep 258291 = 387437) B387437
theorem B389363 : Blo 255820 389363 := bstep (se 1 (by rfl) ⟨292022, by rfl⟩ : syracuseStep 389363 = 584045) B584045
theorem B651523 : Blo 255820 651523 := bstep (se 1 (by rfl) ⟨488642, by rfl⟩ : syracuseStep 651523 = 977285) B977285
theorem B258307 : Blo 255820 258307 := bstep (se 1 (by rfl) ⟨193730, by rfl⟩ : syracuseStep 258307 = 387461) B387461
theorem B389393 : Blo 255820 389393 := bstep (se 2 (by rfl) ⟨146022, by rfl⟩ : syracuseStep 389393 = 292045) B292045
theorem B258323 : Blo 255820 258323 := bstep (se 1 (by rfl) ⟨193742, by rfl⟩ : syracuseStep 258323 = 387485) B387485
theorem B291091 : Blo 255820 291091 := bstep (se 1 (by rfl) ⟨218318, by rfl⟩ : syracuseStep 291091 = 436637) B436637
theorem B258339 : Blo 255820 258339 := bstep (se 1 (by rfl) ⟨193754, by rfl⟩ : syracuseStep 258339 = 387509) B387509
theorem B389411 : Blo 255820 389411 := bstep (se 1 (by rfl) ⟨292058, by rfl⟩ : syracuseStep 389411 = 584117) B584117
theorem B258355 : Blo 255820 258355 := bstep (se 1 (by rfl) ⟨193766, by rfl⟩ : syracuseStep 258355 = 387533) B387533
theorem B389441 : Blo 255820 389441 := bstep (se 2 (by rfl) ⟨146040, by rfl⟩ : syracuseStep 389441 = 292081) B292081
theorem B258371 : Blo 255820 258371 := bstep (se 1 (by rfl) ⟨193778, by rfl⟩ : syracuseStep 258371 = 387557) B387557
theorem B258387 : Blo 255820 258387 := bstep (se 1 (by rfl) ⟨193790, by rfl⟩ : syracuseStep 258387 = 387581) B387581
theorem B389459 : Blo 255820 389459 := bstep (se 1 (by rfl) ⟨292094, by rfl⟩ : syracuseStep 389459 = 584189) B584189
theorem B323939 : Blo 255820 323939 := bstep (se 1 (by rfl) ⟨242954, by rfl⟩ : syracuseStep 323939 = 485909) B485909
theorem B258403 : Blo 255820 258403 := bstep (se 1 (by rfl) ⟨193802, by rfl⟩ : syracuseStep 258403 = 387605) B387605
theorem B389489 : Blo 255820 389489 := bstep (se 2 (by rfl) ⟨146058, by rfl⟩ : syracuseStep 389489 = 292117) B292117
theorem B258419 : Blo 255820 258419 := bstep (se 1 (by rfl) ⟨193814, by rfl⟩ : syracuseStep 258419 = 387629) B387629
theorem B258435 : Blo 255820 258435 := bstep (se 1 (by rfl) ⟨193826, by rfl⟩ : syracuseStep 258435 = 387653) B387653
theorem B389507 : Blo 255820 389507 := bstep (se 1 (by rfl) ⟨292130, by rfl⟩ : syracuseStep 389507 = 584261) B584261
theorem B651665 : Blo 255820 651665 := bstep (se 2 (by rfl) ⟨244374, by rfl⟩ : syracuseStep 651665 = 488749) B488749
theorem B258451 : Blo 255820 258451 := bstep (se 1 (by rfl) ⟨193838, by rfl⟩ : syracuseStep 258451 = 387677) B387677
theorem B389537 : Blo 255820 389537 := bstep (se 2 (by rfl) ⟨146076, by rfl⟩ : syracuseStep 389537 = 292153) B292153
theorem B258467 : Blo 255820 258467 := bstep (se 1 (by rfl) ⟨193850, by rfl⟩ : syracuseStep 258467 = 387701) B387701
theorem B291235 : Blo 255820 291235 := bstep (se 1 (by rfl) ⟨218426, by rfl⟩ : syracuseStep 291235 = 436853) B436853
theorem B258483 : Blo 255820 258483 := bstep (se 1 (by rfl) ⟨193862, by rfl⟩ : syracuseStep 258483 = 387725) B387725
theorem B389555 : Blo 255820 389555 := bstep (se 1 (by rfl) ⟨292166, by rfl⟩ : syracuseStep 389555 = 584333) B584333
theorem B258499 : Blo 255820 258499 := bstep (se 1 (by rfl) ⟨193874, by rfl⟩ : syracuseStep 258499 = 387749) B387749
theorem B389585 : Blo 255820 389585 := bstep (se 2 (by rfl) ⟨146094, by rfl⟩ : syracuseStep 389585 = 292189) B292189
theorem B258515 : Blo 255820 258515 := bstep (se 1 (by rfl) ⟨193886, by rfl⟩ : syracuseStep 258515 = 387773) B387773
theorem B1962467 : Blo 255820 1962467 := bstep (se 1 (by rfl) ⟨1471850, by rfl⟩ : syracuseStep 1962467 = 2943701) B2943701
theorem B258531 : Blo 255820 258531 := bstep (se 1 (by rfl) ⟨193898, by rfl⟩ : syracuseStep 258531 = 387797) B387797
theorem B389603 : Blo 255820 389603 := bstep (se 1 (by rfl) ⟨292202, by rfl⟩ : syracuseStep 389603 = 584405) B584405
theorem B258547 : Blo 255820 258547 := bstep (se 1 (by rfl) ⟨193910, by rfl⟩ : syracuseStep 258547 = 387821) B387821
theorem B389633 : Blo 255820 389633 := bstep (se 2 (by rfl) ⟨146112, by rfl⟩ : syracuseStep 389633 = 292225) B292225
theorem B258563 : Blo 255820 258563 := bstep (se 1 (by rfl) ⟨193922, by rfl⟩ : syracuseStep 258563 = 387845) B387845
theorem B258579 : Blo 255820 258579 := bstep (se 1 (by rfl) ⟨193934, by rfl⟩ : syracuseStep 258579 = 387869) B387869
theorem B389651 : Blo 255820 389651 := bstep (se 1 (by rfl) ⟨292238, by rfl⟩ : syracuseStep 389651 = 584477) B584477
theorem B258595 : Blo 255820 258595 := bstep (se 1 (by rfl) ⟨193946, by rfl⟩ : syracuseStep 258595 = 387893) B387893
theorem B389681 : Blo 255820 389681 := bstep (se 2 (by rfl) ⟨146130, by rfl⟩ : syracuseStep 389681 = 292261) B292261
theorem B258611 : Blo 255820 258611 := bstep (se 1 (by rfl) ⟨193958, by rfl⟩ : syracuseStep 258611 = 387917) B387917
theorem B291379 : Blo 255820 291379 := bstep (se 1 (by rfl) ⟨218534, by rfl⟩ : syracuseStep 291379 = 437069) B437069
theorem B258627 : Blo 255820 258627 := bstep (se 1 (by rfl) ⟨193970, by rfl⟩ : syracuseStep 258627 = 387941) B387941
theorem B389699 : Blo 255820 389699 := bstep (se 1 (by rfl) ⟨292274, by rfl⟩ : syracuseStep 389699 = 584549) B584549
theorem B258643 : Blo 255820 258643 := bstep (se 1 (by rfl) ⟨193982, by rfl⟩ : syracuseStep 258643 = 387965) B387965
theorem B389729 : Blo 255820 389729 := bstep (se 2 (by rfl) ⟨146148, by rfl⟩ : syracuseStep 389729 = 292297) B292297
theorem B488035 : Blo 255820 488035 := bstep (se 1 (by rfl) ⟨366026, by rfl⟩ : syracuseStep 488035 = 732053) B732053
theorem B258659 : Blo 255820 258659 := bstep (se 1 (by rfl) ⟨193994, by rfl⟩ : syracuseStep 258659 = 387989) B387989
theorem B258675 : Blo 255820 258675 := bstep (se 1 (by rfl) ⟨194006, by rfl⟩ : syracuseStep 258675 = 388013) B388013
theorem B258691 : Blo 255820 258691 := bstep (se 1 (by rfl) ⟨194018, by rfl⟩ : syracuseStep 258691 = 388037) B388037
theorem B488081 : Blo 255820 488081 := bstep (se 2 (by rfl) ⟨183030, by rfl⟩ : syracuseStep 488081 = 366061) B366061
theorem B258707 : Blo 255820 258707 := bstep (se 1 (by rfl) ⟨194030, by rfl⟩ : syracuseStep 258707 = 388061) B388061
theorem B258723 : Blo 255820 258723 := bstep (se 1 (by rfl) ⟨194042, by rfl⟩ : syracuseStep 258723 = 388085) B388085
theorem B258739 : Blo 255820 258739 := bstep (se 1 (by rfl) ⟨194054, by rfl⟩ : syracuseStep 258739 = 388109) B388109
theorem B258755 : Blo 255820 258755 := bstep (se 1 (by rfl) ⟨194066, by rfl⟩ : syracuseStep 258755 = 388133) B388133
theorem B291523 : Blo 255820 291523 := bstep (se 1 (by rfl) ⟨218642, by rfl⟩ : syracuseStep 291523 = 437285) B437285
theorem B258771 : Blo 255820 258771 := bstep (se 1 (by rfl) ⟨194078, by rfl⟩ : syracuseStep 258771 = 388157) B388157
theorem B258787 : Blo 255820 258787 := bstep (se 1 (by rfl) ⟨194090, by rfl⟩ : syracuseStep 258787 = 388181) B388181
theorem B389873 : Blo 255820 389873 := bstep (se 2 (by rfl) ⟨146202, by rfl⟩ : syracuseStep 389873 = 292405) B292405
theorem B258803 : Blo 255820 258803 := bstep (se 1 (by rfl) ⟨194102, by rfl⟩ : syracuseStep 258803 = 388205) B388205
theorem B258819 : Blo 255820 258819 := bstep (se 1 (by rfl) ⟨194114, by rfl⟩ : syracuseStep 258819 = 388229) B388229
theorem B258835 : Blo 255820 258835 := bstep (se 1 (by rfl) ⟨194126, by rfl⟩ : syracuseStep 258835 = 388253) B388253
theorem B258851 : Blo 255820 258851 := bstep (se 1 (by rfl) ⟨194138, by rfl⟩ : syracuseStep 258851 = 388277) B388277
theorem B258867 : Blo 255820 258867 := bstep (se 1 (by rfl) ⟨194150, by rfl⟩ : syracuseStep 258867 = 388301) B388301
theorem B4682549 : Blo 255820 4682549 := bstep (se 5 (by rfl) ⟨219494, by rfl⟩ : syracuseStep 4682549 = 438989) B438989
theorem B258883 : Blo 255820 258883 := bstep (se 1 (by rfl) ⟨194162, by rfl⟩ : syracuseStep 258883 = 388325) B388325
theorem B258899 : Blo 255820 258899 := bstep (se 1 (by rfl) ⟨194174, by rfl⟩ : syracuseStep 258899 = 388349) B388349
theorem B291667 : Blo 255820 291667 := bstep (se 1 (by rfl) ⟨218750, by rfl⟩ : syracuseStep 291667 = 437501) B437501
theorem B258915 : Blo 255820 258915 := bstep (se 1 (by rfl) ⟨194186, by rfl⟩ : syracuseStep 258915 = 388373) B388373
theorem B258931 : Blo 255820 258931 := bstep (se 1 (by rfl) ⟨194198, by rfl⟩ : syracuseStep 258931 = 388397) B388397
theorem B258947 : Blo 255820 258947 := bstep (se 1 (by rfl) ⟨194210, by rfl⟩ : syracuseStep 258947 = 388421) B388421
theorem B258963 : Blo 255820 258963 := bstep (se 1 (by rfl) ⟨194222, by rfl⟩ : syracuseStep 258963 = 388445) B388445
theorem B258979 : Blo 255820 258979 := bstep (se 1 (by rfl) ⟨194234, by rfl⟩ : syracuseStep 258979 = 388469) B388469
theorem B488369 : Blo 255820 488369 := bstep (se 2 (by rfl) ⟨183138, by rfl⟩ : syracuseStep 488369 = 366277) B366277
theorem B258995 : Blo 255820 258995 := bstep (se 1 (by rfl) ⟨194246, by rfl⟩ : syracuseStep 258995 = 388493) B388493
theorem B259011 : Blo 255820 259011 := bstep (se 1 (by rfl) ⟨194258, by rfl⟩ : syracuseStep 259011 = 388517) B388517
theorem B259027 : Blo 255820 259027 := bstep (se 1 (by rfl) ⟨194270, by rfl⟩ : syracuseStep 259027 = 388541) B388541
theorem B259043 : Blo 255820 259043 := bstep (se 1 (by rfl) ⟨194282, by rfl⟩ : syracuseStep 259043 = 388565) B388565
theorem B291811 : Blo 255820 291811 := bstep (se 1 (by rfl) ⟨218858, by rfl⟩ : syracuseStep 291811 = 437717) B437717
theorem B259059 : Blo 255820 259059 := bstep (se 1 (by rfl) ⟨194294, by rfl⟩ : syracuseStep 259059 = 388589) B388589
theorem B259075 : Blo 255820 259075 := bstep (se 1 (by rfl) ⟨194306, by rfl⟩ : syracuseStep 259075 = 388613) B388613
theorem B259091 : Blo 255820 259091 := bstep (se 1 (by rfl) ⟨194318, by rfl⟩ : syracuseStep 259091 = 388637) B388637
theorem B324643 : Blo 255820 324643 := bstep (se 1 (by rfl) ⟨243482, by rfl⟩ : syracuseStep 324643 = 486965) B486965
theorem B259107 : Blo 255820 259107 := bstep (se 1 (by rfl) ⟨194330, by rfl⟩ : syracuseStep 259107 = 388661) B388661
theorem B259123 : Blo 255820 259123 := bstep (se 1 (by rfl) ⟨194342, by rfl⟩ : syracuseStep 259123 = 388685) B388685
theorem B259139 : Blo 255820 259139 := bstep (se 1 (by rfl) ⟨194354, by rfl⟩ : syracuseStep 259139 = 388709) B388709
theorem B259155 : Blo 255820 259155 := bstep (se 1 (by rfl) ⟨194366, by rfl⟩ : syracuseStep 259155 = 388733) B388733
theorem B259171 : Blo 255820 259171 := bstep (se 1 (by rfl) ⟨194378, by rfl⟩ : syracuseStep 259171 = 388757) B388757
theorem B259187 : Blo 255820 259187 := bstep (se 1 (by rfl) ⟨194390, by rfl⟩ : syracuseStep 259187 = 388781) B388781
theorem B291955 : Blo 255820 291955 := bstep (se 1 (by rfl) ⟨218966, by rfl⟩ : syracuseStep 291955 = 437933) B437933
theorem B324739 : Blo 255820 324739 := bstep (se 1 (by rfl) ⟨243554, by rfl⟩ : syracuseStep 324739 = 487109) B487109
theorem B390275 : Blo 255820 390275 := bstep (se 1 (by rfl) ⟨292706, by rfl⟩ : syracuseStep 390275 = 585413) B585413
theorem B259203 : Blo 255820 259203 := bstep (se 1 (by rfl) ⟨194402, by rfl⟩ : syracuseStep 259203 = 388805) B388805
theorem B259219 : Blo 255820 259219 := bstep (se 1 (by rfl) ⟨194414, by rfl⟩ : syracuseStep 259219 = 388829) B388829
theorem B259235 : Blo 255820 259235 := bstep (se 1 (by rfl) ⟨194426, by rfl⟩ : syracuseStep 259235 = 388853) B388853
theorem B1307825 : Blo 255820 1307825 := bstep (se 2 (by rfl) ⟨490434, by rfl⟩ : syracuseStep 1307825 = 980869) B980869
theorem B259251 : Blo 255820 259251 := bstep (se 1 (by rfl) ⟨194438, by rfl⟩ : syracuseStep 259251 = 388877) B388877
theorem B259267 : Blo 255820 259267 := bstep (se 1 (by rfl) ⟨194450, by rfl⟩ : syracuseStep 259267 = 388901) B388901
theorem B259283 : Blo 255820 259283 := bstep (se 1 (by rfl) ⟨194462, by rfl⟩ : syracuseStep 259283 = 388925) B388925
theorem B390371 : Blo 255820 390371 := bstep (se 1 (by rfl) ⟨292778, by rfl⟩ : syracuseStep 390371 = 585557) B585557
theorem B1471715 : Blo 255820 1471715 := bstep (se 1 (by rfl) ⟨1103786, by rfl⟩ : syracuseStep 1471715 = 2207573) B2207573
theorem B259299 : Blo 255820 259299 := bstep (se 1 (by rfl) ⟨194474, by rfl⟩ : syracuseStep 259299 = 388949) B388949
theorem B259315 : Blo 255820 259315 := bstep (se 1 (by rfl) ⟨194486, by rfl⟩ : syracuseStep 259315 = 388973) B388973
theorem B259331 : Blo 255820 259331 := bstep (se 1 (by rfl) ⟨194498, by rfl⟩ : syracuseStep 259331 = 388997) B388997
theorem B292099 : Blo 255820 292099 := bstep (se 1 (by rfl) ⟨219074, by rfl⟩ : syracuseStep 292099 = 438149) B438149
theorem B259347 : Blo 255820 259347 := bstep (se 1 (by rfl) ⟨194510, by rfl⟩ : syracuseStep 259347 = 389021) B389021
theorem B259363 : Blo 255820 259363 := bstep (se 1 (by rfl) ⟨194522, by rfl⟩ : syracuseStep 259363 = 389045) B389045
theorem B783665 : Blo 255820 783665 := bstep (se 2 (by rfl) ⟨293874, by rfl⟩ : syracuseStep 783665 = 587749) B587749
theorem B259379 : Blo 255820 259379 := bstep (se 1 (by rfl) ⟨194534, by rfl⟩ : syracuseStep 259379 = 389069) B389069
theorem B259395 : Blo 255820 259395 := bstep (se 1 (by rfl) ⟨194546, by rfl⟩ : syracuseStep 259395 = 389093) B389093
theorem B259411 : Blo 255820 259411 := bstep (se 1 (by rfl) ⟨194558, by rfl⟩ : syracuseStep 259411 = 389117) B389117
theorem B259427 : Blo 255820 259427 := bstep (se 1 (by rfl) ⟨194570, by rfl⟩ : syracuseStep 259427 = 389141) B389141
theorem B652657 : Blo 255820 652657 := bstep (se 2 (by rfl) ⟨244746, by rfl⟩ : syracuseStep 652657 = 489493) B489493
theorem B259443 : Blo 255820 259443 := bstep (se 1 (by rfl) ⟨194582, by rfl⟩ : syracuseStep 259443 = 389165) B389165
theorem B259459 : Blo 255820 259459 := bstep (se 1 (by rfl) ⟨194594, by rfl⟩ : syracuseStep 259459 = 389189) B389189
theorem B259475 : Blo 255820 259475 := bstep (se 1 (by rfl) ⟨194606, by rfl⟩ : syracuseStep 259475 = 389213) B389213
theorem B292243 : Blo 255820 292243 := bstep (se 1 (by rfl) ⟨219182, by rfl⟩ : syracuseStep 292243 = 438365) B438365
theorem B259491 : Blo 255820 259491 := bstep (se 1 (by rfl) ⟨194618, by rfl⟩ : syracuseStep 259491 = 389237) B389237
theorem B259507 : Blo 255820 259507 := bstep (se 1 (by rfl) ⟨194630, by rfl⟩ : syracuseStep 259507 = 389261) B389261
theorem B259523 : Blo 255820 259523 := bstep (se 1 (by rfl) ⟨194642, by rfl⟩ : syracuseStep 259523 = 389285) B389285
theorem B259539 : Blo 255820 259539 := bstep (se 1 (by rfl) ⟨194654, by rfl⟩ : syracuseStep 259539 = 389309) B389309
theorem B259555 : Blo 255820 259555 := bstep (se 1 (by rfl) ⟨194666, by rfl⟩ : syracuseStep 259555 = 389333) B389333
theorem B783857 : Blo 255820 783857 := bstep (se 2 (by rfl) ⟨293946, by rfl⟩ : syracuseStep 783857 = 587893) B587893
theorem B259571 : Blo 255820 259571 := bstep (se 1 (by rfl) ⟨194678, by rfl⟩ : syracuseStep 259571 = 389357) B389357
theorem B259587 : Blo 255820 259587 := bstep (se 1 (by rfl) ⟨194690, by rfl⟩ : syracuseStep 259587 = 389381) B389381
theorem B259603 : Blo 255820 259603 := bstep (se 1 (by rfl) ⟨194702, by rfl⟩ : syracuseStep 259603 = 389405) B389405
theorem B259619 : Blo 255820 259619 := bstep (se 1 (by rfl) ⟨194714, by rfl⟩ : syracuseStep 259619 = 389429) B389429
theorem B259635 : Blo 255820 259635 := bstep (se 1 (by rfl) ⟨194726, by rfl⟩ : syracuseStep 259635 = 389453) B389453
theorem B259651 : Blo 255820 259651 := bstep (se 1 (by rfl) ⟨194738, by rfl⟩ : syracuseStep 259651 = 389477) B389477
theorem B259667 : Blo 255820 259667 := bstep (se 1 (by rfl) ⟨194750, by rfl⟩ : syracuseStep 259667 = 389501) B389501
theorem B620131 : Blo 255820 620131 := bstep (se 1 (by rfl) ⟨465098, by rfl⟩ : syracuseStep 620131 = 930197) B930197
theorem B259683 : Blo 255820 259683 := bstep (se 1 (by rfl) ⟨194762, by rfl⟩ : syracuseStep 259683 = 389525) B389525
theorem B325235 : Blo 255820 325235 := bstep (se 1 (by rfl) ⟨243926, by rfl⟩ : syracuseStep 325235 = 487853) B487853
theorem B259699 : Blo 255820 259699 := bstep (se 1 (by rfl) ⟨194774, by rfl⟩ : syracuseStep 259699 = 389549) B389549
theorem B489091 : Blo 255820 489091 := bstep (se 1 (by rfl) ⟨366818, by rfl⟩ : syracuseStep 489091 = 733637) B733637
theorem B652931 : Blo 255820 652931 := bstep (se 1 (by rfl) ⟨489698, by rfl⟩ : syracuseStep 652931 = 979397) B979397
theorem B554627 : Blo 255820 554627 := bstep (se 1 (by rfl) ⟨415970, by rfl⟩ : syracuseStep 554627 = 831941) B831941
theorem B259715 : Blo 255820 259715 := bstep (se 1 (by rfl) ⟨194786, by rfl⟩ : syracuseStep 259715 = 389573) B389573
theorem B259731 : Blo 255820 259731 := bstep (se 1 (by rfl) ⟨194798, by rfl⟩ : syracuseStep 259731 = 389597) B389597
theorem B259747 : Blo 255820 259747 := bstep (se 1 (by rfl) ⟨194810, by rfl⟩ : syracuseStep 259747 = 389621) B389621
theorem B980657 : Blo 255820 980657 := bstep (se 2 (by rfl) ⟨367746, by rfl⟩ : syracuseStep 980657 = 735493) B735493
theorem B259763 : Blo 255820 259763 := bstep (se 1 (by rfl) ⟨194822, by rfl⟩ : syracuseStep 259763 = 389645) B389645
theorem B259779 : Blo 255820 259779 := bstep (se 1 (by rfl) ⟨194834, by rfl⟩ : syracuseStep 259779 = 389669) B389669
theorem B259795 : Blo 255820 259795 := bstep (se 1 (by rfl) ⟨194846, by rfl⟩ : syracuseStep 259795 = 389693) B389693
theorem B259811 : Blo 255820 259811 := bstep (se 1 (by rfl) ⟨194858, by rfl⟩ : syracuseStep 259811 = 389717) B389717
theorem B653123 : Blo 255820 653123 := bstep (se 1 (by rfl) ⟨489842, by rfl⟩ : syracuseStep 653123 = 979685) B979685
theorem B587729 : Blo 255820 587729 := bstep (se 2 (by rfl) ⟨220398, by rfl⟩ : syracuseStep 587729 = 440797) B440797
theorem B2488333 : Blo 255820 2488333 := bstep (se 3 (by rfl) ⟨466562, by rfl⟩ : syracuseStep 2488333 = 933125) B933125
theorem B489539 : Blo 255820 489539 := bstep (se 1 (by rfl) ⟨367154, by rfl⟩ : syracuseStep 489539 = 734309) B734309
theorem B1701965 : Blo 255820 1701965 := bstep (se 3 (by rfl) ⟨319118, by rfl⟩ : syracuseStep 1701965 = 638237) B638237
theorem B325939 : Blo 255820 325939 := bstep (se 1 (by rfl) ⟨244454, by rfl⟩ : syracuseStep 325939 = 488909) B488909
theorem B489827 : Blo 255820 489827 := bstep (se 1 (by rfl) ⟨367370, by rfl⟩ : syracuseStep 489827 = 734741) B734741
theorem B326035 : Blo 255820 326035 := bstep (se 1 (by rfl) ⟨244526, by rfl⟩ : syracuseStep 326035 = 489053) B489053
theorem B260515 : Blo 255820 260515 := bstep (se 1 (by rfl) ⟨195386, by rfl⟩ : syracuseStep 260515 = 390773) B390773
theorem B621091 : Blo 255820 621091 := bstep (se 1 (by rfl) ⟨465818, by rfl⟩ : syracuseStep 621091 = 931637) B931637
theorem B1309283 : Blo 255820 1309283 := bstep (se 1 (by rfl) ⟨981962, by rfl⟩ : syracuseStep 1309283 = 1963925) B1963925
theorem B1145507 : Blo 255820 1145507 := bstep (se 1 (by rfl) ⟨859130, by rfl⟩ : syracuseStep 1145507 = 1718261) B1718261
theorem B654065 : Blo 255820 654065 := bstep (se 2 (by rfl) ⟨245274, by rfl⟩ : syracuseStep 654065 = 490549) B490549
theorem B654115 : Blo 255820 654115 := bstep (se 1 (by rfl) ⟨490586, by rfl⟩ : syracuseStep 654115 = 981173) B981173
theorem B621361 : Blo 255820 621361 := bstep (se 2 (by rfl) ⟨233010, by rfl⟩ : syracuseStep 621361 = 466021) B466021
theorem B326531 : Blo 255820 326531 := bstep (se 1 (by rfl) ⟨244898, by rfl⟩ : syracuseStep 326531 = 489797) B489797
theorem B654257 : Blo 255820 654257 := bstep (se 2 (by rfl) ⟨245346, by rfl⟩ : syracuseStep 654257 = 490693) B490693
theorem B2489285 : Blo 255820 2489285 := bstep (se 4 (by rfl) ⟨233370, by rfl⟩ : syracuseStep 2489285 = 466741) B466741
theorem B982115 : Blo 255820 982115 := bstep (se 1 (by rfl) ⟨736586, by rfl⟩ : syracuseStep 982115 = 1473173) B1473173
theorem B490769 : Blo 255820 490769 := bstep (se 2 (by rfl) ⟨184038, by rfl⟩ : syracuseStep 490769 = 368077) B368077
theorem B1310093 : Blo 255820 1310093 := bstep (se 3 (by rfl) ⟨245642, by rfl⟩ : syracuseStep 1310093 = 491285) B491285
theorem B1146275 : Blo 255820 1146275 := bstep (se 1 (by rfl) ⟨859706, by rfl⟩ : syracuseStep 1146275 = 1719413) B1719413
theorem B327235 : Blo 255820 327235 := bstep (se 1 (by rfl) ⟨245426, by rfl⟩ : syracuseStep 327235 = 490853) B490853
theorem B327331 : Blo 255820 327331 := bstep (se 1 (by rfl) ⟨245498, by rfl⟩ : syracuseStep 327331 = 490997) B490997
theorem B655249 : Blo 255820 655249 := bstep (se 2 (by rfl) ⟨245718, by rfl⟩ : syracuseStep 655249 = 491437) B491437
theorem B491521 : Blo 255820 491521 := bstep (se 2 (by rfl) ⟨184320, by rfl⟩ : syracuseStep 491521 = 368641) B368641
theorem B655411 : Blo 255820 655411 := bstep (se 1 (by rfl) ⟨491558, by rfl⟩ : syracuseStep 655411 = 983117) B983117
theorem B1048727 : Blo 255820 1048727 := bstep (se 1 (by rfl) ⟨786545, by rfl⟩ : syracuseStep 1048727 = 1573091) B1573091
theorem B655553 : Blo 255820 655553 := bstep (se 2 (by rfl) ⟨245832, by rfl⟩ : syracuseStep 655553 = 491665) B491665
theorem B393419 : Blo 255820 393419 := bstep (se 1 (by rfl) ⟨295064, by rfl⟩ : syracuseStep 393419 = 590129) B590129
theorem B327883 : Blo 255820 327883 := bstep (se 1 (by rfl) ⟨245912, by rfl⟩ : syracuseStep 327883 = 491825) B491825
theorem B786653 : Blo 255820 786653 := bstep (se 3 (by rfl) ⟨147497, by rfl⟩ : syracuseStep 786653 = 294995) B294995
theorem B983299 : Blo 255820 983299 := bstep (se 1 (by rfl) ⟨737474, by rfl⟩ : syracuseStep 983299 = 1474949) B1474949
theorem B622937 : Blo 255820 622937 := bstep (se 2 (by rfl) ⟨233601, by rfl⟩ : syracuseStep 622937 = 467203) B467203
theorem B491969 : Blo 255820 491969 := bstep (se 2 (by rfl) ⟨184488, by rfl⟩ : syracuseStep 491969 = 368977) B368977
theorem B328151 : Blo 255820 328151 := bstep (se 1 (by rfl) ⟨246113, by rfl⟩ : syracuseStep 328151 = 492227) B492227
theorem B983603 : Blo 255820 983603 := bstep (se 1 (by rfl) ⟨737702, by rfl⟩ : syracuseStep 983603 = 1475405) B1475405
theorem B2130583 : Blo 255820 2130583 := bstep (se 1 (by rfl) ⟨1597937, by rfl⟩ : syracuseStep 2130583 = 3195875) B3195875
theorem B492311 : Blo 255820 492311 := bstep (se 1 (by rfl) ⟨369233, by rfl⟩ : syracuseStep 492311 = 738467) B738467
theorem B1868579 : Blo 255820 1868579 := bstep (se 1 (by rfl) ⟨1401434, by rfl⟩ : syracuseStep 1868579 = 2802869) B2802869
theorem B623705 : Blo 255820 623705 := bstep (se 2 (by rfl) ⟨233889, by rfl⟩ : syracuseStep 623705 = 467779) B467779
theorem B1311875 : Blo 255820 1311875 := bstep (se 1 (by rfl) ⟨983906, by rfl⟩ : syracuseStep 1311875 = 1967813) B1967813
theorem B984257 : Blo 255820 984257 := bstep (se 2 (by rfl) ⟨369096, by rfl⟩ : syracuseStep 984257 = 738193) B738193
theorem B3146957 : Blo 255820 3146957 := bstep (se 3 (by rfl) ⟨590054, by rfl⟩ : syracuseStep 3146957 = 1180109) B1180109
theorem B1869101 : Blo 255820 1869101 := bstep (se 3 (by rfl) ⟨350456, by rfl⟩ : syracuseStep 1869101 = 700913) B700913
theorem B1246529 : Blo 255820 1246529 := bstep (se 2 (by rfl) ⟨467448, by rfl⟩ : syracuseStep 1246529 = 934897) B934897
theorem B656819 : Blo 255820 656819 := bstep (se 1 (by rfl) ⟨492614, by rfl⟩ : syracuseStep 656819 = 985229) B985229
theorem B492979 : Blo 255820 492979 := bstep (se 1 (by rfl) ⟨369734, by rfl⟩ : syracuseStep 492979 = 739469) B739469
theorem B2098649 : Blo 255820 2098649 := bstep (se 2 (by rfl) ⟨786993, by rfl⟩ : syracuseStep 2098649 = 1573987) B1573987
theorem B1246681 : Blo 255820 1246681 := bstep (se 2 (by rfl) ⟨467505, by rfl⟩ : syracuseStep 1246681 = 935011) B935011
theorem B493249 : Blo 255820 493249 := bstep (se 2 (by rfl) ⟨184968, by rfl⟩ : syracuseStep 493249 = 369937) B369937
theorem B493427 : Blo 255820 493427 := bstep (se 1 (by rfl) ⟨370070, by rfl⟩ : syracuseStep 493427 = 740141) B740141
theorem B3508085 : Blo 255820 3508085 := bstep (se 5 (by rfl) ⟨164441, by rfl⟩ : syracuseStep 3508085 = 328883) B328883
theorem B657355 : Blo 255820 657355 := bstep (se 1 (by rfl) ⟨493016, by rfl⟩ : syracuseStep 657355 = 986033) B986033
theorem B657497 : Blo 255820 657497 := bstep (se 2 (by rfl) ⟨246561, by rfl⟩ : syracuseStep 657497 = 493123) B493123
theorem B1050803 : Blo 255820 1050803 := bstep (se 1 (by rfl) ⟨788102, by rfl⟩ : syracuseStep 1050803 = 1576205) B1576205
theorem B4163957 : Blo 255820 4163957 := bstep (se 5 (by rfl) ⟨195185, by rfl⟩ : syracuseStep 4163957 = 390371) B390371
theorem B985517 : Blo 255820 985517 := bstep (se 3 (by rfl) ⟨184784, by rfl⟩ : syracuseStep 985517 = 369569) B369569
theorem B985547 : Blo 255820 985547 := bstep (se 1 (by rfl) ⟨739160, by rfl⟩ : syracuseStep 985547 = 1478321) B1478321
theorem B559703 : Blo 255820 559703 := bstep (se 1 (by rfl) ⟨419777, by rfl⟩ : syracuseStep 559703 = 839555) B839555
theorem B1051339 : Blo 255820 1051339 := bstep (se 1 (by rfl) ⟨788504, by rfl⟩ : syracuseStep 1051339 = 1577009) B1577009
theorem B1772381 : Blo 255820 1772381 := bstep (se 3 (by rfl) ⟨332321, by rfl⟩ : syracuseStep 1772381 = 664643) B664643
theorem B3312485 : Blo 255820 3312485 := bstep (se 4 (by rfl) ⟨310545, by rfl⟩ : syracuseStep 3312485 = 621091) B621091
theorem B986201 : Blo 255820 986201 := bstep (se 2 (by rfl) ⟨369825, by rfl⟩ : syracuseStep 986201 = 739651) B739651
theorem B494849 : Blo 255820 494849 := bstep (se 2 (by rfl) ⟨185568, by rfl⟩ : syracuseStep 494849 = 371137) B371137
theorem B757081 : Blo 255820 757081 := bstep (se 2 (by rfl) ⟨283905, by rfl⟩ : syracuseStep 757081 = 567811) B567811
theorem B495065 : Blo 255820 495065 := bstep (se 2 (by rfl) ⟨185649, by rfl⟩ : syracuseStep 495065 = 371299) B371299
theorem B1969757 : Blo 255820 1969757 := bstep (se 3 (by rfl) ⟨369329, by rfl⟩ : syracuseStep 1969757 = 738659) B738659
theorem B626393 : Blo 255820 626393 := bstep (se 2 (by rfl) ⟨234897, by rfl⟩ : syracuseStep 626393 = 469795) B469795
theorem B364375 : Blo 255820 364375 := bstep (se 1 (by rfl) ⟨273281, by rfl⟩ : syracuseStep 364375 = 546563) B546563
theorem B2101085 : Blo 255820 2101085 := bstep (se 3 (by rfl) ⟨393953, by rfl⟩ : syracuseStep 2101085 = 787907) B787907
theorem B3543115 : Blo 255820 3543115 := bstep (se 1 (by rfl) ⟨2657336, by rfl⟩ : syracuseStep 3543115 = 5314673) B5314673
theorem B692545 : Blo 255820 692545 := bstep (se 2 (by rfl) ⟨259704, by rfl⟩ : syracuseStep 692545 = 519409) B519409
theorem B1479005 : Blo 255820 1479005 := bstep (se 3 (by rfl) ⟨277313, by rfl⟩ : syracuseStep 1479005 = 554627) B554627
theorem B365195 : Blo 255820 365195 := bstep (se 1 (by rfl) ⟨273896, by rfl⟩ : syracuseStep 365195 = 547793) B547793
theorem B3707633 : Blo 255820 3707633 := bstep (se 2 (by rfl) ⟨1390362, by rfl⟩ : syracuseStep 3707633 = 2780725) B2780725
theorem B463627 : Blo 255820 463627 := bstep (se 1 (by rfl) ⟨347720, by rfl⟩ : syracuseStep 463627 = 695441) B695441
theorem B824215 : Blo 255820 824215 := bstep (se 1 (by rfl) ⟨618161, by rfl⟩ : syracuseStep 824215 = 1236323) B1236323
theorem B1872791 : Blo 255820 1872791 := bstep (se 1 (by rfl) ⟨1404593, by rfl⟩ : syracuseStep 1872791 = 2809187) B2809187
theorem B7410649 : Blo 255820 7410649 := bstep (se 2 (by rfl) ⟨2778993, by rfl⟩ : syracuseStep 7410649 = 5557987) B5557987
theorem B693323 : Blo 255820 693323 := bstep (se 1 (by rfl) ⟨519992, by rfl⟩ : syracuseStep 693323 = 1039985) B1039985
theorem B431191 : Blo 255820 431191 := bstep (se 1 (by rfl) ⟨323393, by rfl⟩ : syracuseStep 431191 = 646787) B646787
theorem B1119505 : Blo 255820 1119505 := bstep (se 2 (by rfl) ⟨419814, by rfl⟩ : syracuseStep 1119505 = 839629) B839629
theorem B464435 : Blo 255820 464435 := bstep (se 1 (by rfl) ⟨348326, by rfl⟩ : syracuseStep 464435 = 696653) B696653
theorem B431831 : Blo 255820 431831 := bstep (se 1 (by rfl) ⟨323873, by rfl⟩ : syracuseStep 431831 = 647747) B647747
theorem B2463533 : Blo 255820 2463533 := bstep (se 3 (by rfl) ⟨461912, by rfl⟩ : syracuseStep 2463533 = 923825) B923825
theorem B431959 : Blo 255820 431959 := bstep (se 1 (by rfl) ⟨323969, by rfl⟩ : syracuseStep 431959 = 647939) B647939
theorem B825547 : Blo 255820 825547 := bstep (se 1 (by rfl) ⟨619160, by rfl⟩ : syracuseStep 825547 = 1238321) B1238321
theorem B1644761 : Blo 255820 1644761 := bstep (se 2 (by rfl) ⟨616785, by rfl⟩ : syracuseStep 1644761 = 1233571) B1233571
theorem B432587 : Blo 255820 432587 := bstep (se 1 (by rfl) ⟨324440, by rfl⟩ : syracuseStep 432587 = 648881) B648881
theorem B465473 : Blo 255820 465473 := bstep (se 2 (by rfl) ⟨174552, by rfl⟩ : syracuseStep 465473 = 349105) B349105
theorem B432715 : Blo 255820 432715 := bstep (se 1 (by rfl) ⟨324536, by rfl⟩ : syracuseStep 432715 = 649073) B649073
theorem B432857 : Blo 255820 432857 := bstep (se 2 (by rfl) ⟨162321, by rfl⟩ : syracuseStep 432857 = 324643) B324643
theorem B793367 : Blo 255820 793367 := bstep (se 1 (by rfl) ⟨595025, by rfl⟩ : syracuseStep 793367 = 1190051) B1190051
theorem B2366243 : Blo 255820 2366243 := bstep (se 1 (by rfl) ⟨1774682, by rfl⟩ : syracuseStep 2366243 = 3549365) B3549365
theorem B826163 : Blo 255820 826163 := bstep (se 1 (by rfl) ⟨619622, by rfl⟩ : syracuseStep 826163 = 1239245) B1239245
theorem B432985 : Blo 255820 432985 := bstep (se 2 (by rfl) ⟨162369, by rfl⟩ : syracuseStep 432985 = 324739) B324739
theorem B990103 : Blo 255820 990103 := bstep (se 1 (by rfl) ⟨742577, by rfl⟩ : syracuseStep 990103 = 1485155) B1485155
theorem B4430861 : Blo 255820 4430861 := bstep (se 3 (by rfl) ⟨830786, by rfl⟩ : syracuseStep 4430861 = 1661573) B1661573
theorem B2628683 : Blo 255820 2628683 := bstep (se 1 (by rfl) ⟨1971512, by rfl⟩ : syracuseStep 2628683 = 3943025) B3943025
theorem B3054685 : Blo 255820 3054685 := bstep (se 3 (by rfl) ⟨572753, by rfl⟩ : syracuseStep 3054685 = 1145507) B1145507
theorem B433559 : Blo 255820 433559 := bstep (se 1 (by rfl) ⟨325169, by rfl⟩ : syracuseStep 433559 = 650339) B650339
theorem B826841 : Blo 255820 826841 := bstep (se 2 (by rfl) ⟨310065, by rfl⟩ : syracuseStep 826841 = 620131) B620131
theorem B433687 : Blo 255820 433687 := bstep (se 1 (by rfl) ⟨325265, by rfl⟩ : syracuseStep 433687 = 650531) B650531
theorem B4955741 : Blo 255820 4955741 := bstep (se 3 (by rfl) ⟨929201, by rfl⟩ : syracuseStep 4955741 = 1858403) B1858403
theorem B1646401 : Blo 255820 1646401 := bstep (se 2 (by rfl) ⟨617400, by rfl⟩ : syracuseStep 1646401 = 1234801) B1234801
theorem B1974221 : Blo 255820 1974221 := bstep (se 3 (by rfl) ⟨370166, by rfl⟩ : syracuseStep 1974221 = 740333) B740333
theorem B3317777 : Blo 255820 3317777 := bstep (se 2 (by rfl) ⟨1244166, by rfl⟩ : syracuseStep 3317777 = 2488333) B2488333
theorem B4464715 : Blo 255820 4464715 := bstep (se 1 (by rfl) ⟨3348536, by rfl⟩ : syracuseStep 4464715 = 6697073) B6697073
theorem B467059 : Blo 255820 467059 := bstep (se 1 (by rfl) ⟨350294, by rfl⟩ : syracuseStep 467059 = 700589) B700589
theorem B434315 : Blo 255820 434315 := bstep (se 1 (by rfl) ⟨325736, by rfl⟩ : syracuseStep 434315 = 651473) B651473
theorem B434443 : Blo 255820 434443 := bstep (se 1 (by rfl) ⟨325832, by rfl⟩ : syracuseStep 434443 = 651665) B651665
theorem B2203949 : Blo 255820 2203949 := bstep (se 3 (by rfl) ⟨413240, by rfl⟩ : syracuseStep 2203949 = 826481) B826481
theorem B434585 : Blo 255820 434585 := bstep (se 2 (by rfl) ⟨162969, by rfl⟩ : syracuseStep 434585 = 325939) B325939
theorem B434713 : Blo 255820 434713 := bstep (se 2 (by rfl) ⟨163017, by rfl⟩ : syracuseStep 434713 = 326035) B326035
theorem B3121699 : Blo 255820 3121699 := bstep (se 1 (by rfl) ⟨2341274, by rfl⟩ : syracuseStep 3121699 = 4682549) B4682549
theorem B369625 : Blo 255820 369625 := bstep (se 2 (by rfl) ⟨138609, by rfl⟩ : syracuseStep 369625 = 277219) B277219
theorem B828481 : Blo 255820 828481 := bstep (se 2 (by rfl) ⟨310680, by rfl⟩ : syracuseStep 828481 = 621361) B621361
theorem B435287 : Blo 255820 435287 := bstep (se 1 (by rfl) ⟨326465, by rfl⟩ : syracuseStep 435287 = 652931) B652931
theorem B435415 : Blo 255820 435415 := bstep (se 1 (by rfl) ⟨326561, by rfl⟩ : syracuseStep 435415 = 653123) B653123
theorem B8955485 : Blo 255820 8955485 := bstep (se 3 (by rfl) ⟨1679153, by rfl⟩ : syracuseStep 8955485 = 3358307) B3358307
theorem B730903 : Blo 255820 730903 := bstep (se 1 (by rfl) ⟨548177, by rfl⟩ : syracuseStep 730903 = 1096355) B1096355
theorem B436043 : Blo 255820 436043 := bstep (se 1 (by rfl) ⟨327032, by rfl⟩ : syracuseStep 436043 = 654065) B654065
theorem B436171 : Blo 255820 436171 := bstep (se 1 (by rfl) ⟨327128, by rfl⟩ : syracuseStep 436171 = 654257) B654257
theorem B1943513 : Blo 255820 1943513 := bstep (se 2 (by rfl) ⟨728817, by rfl⟩ : syracuseStep 1943513 = 1457635) B1457635
theorem B436313 : Blo 255820 436313 := bstep (se 2 (by rfl) ⟨163617, by rfl⟩ : syracuseStep 436313 = 327235) B327235
theorem B1976413 : Blo 255820 1976413 := bstep (se 3 (by rfl) ⟨370577, by rfl⟩ : syracuseStep 1976413 = 741155) B741155
theorem B665803 : Blo 255820 665803 := bstep (se 1 (by rfl) ⟨499352, by rfl⟩ : syracuseStep 665803 = 998705) B998705
theorem B436441 : Blo 255820 436441 := bstep (se 2 (by rfl) ⟨163665, by rfl⟩ : syracuseStep 436441 = 327331) B327331
theorem B764183 : Blo 255820 764183 := bstep (se 1 (by rfl) ⟨573137, by rfl⟩ : syracuseStep 764183 = 1146275) B1146275
theorem B600409 : Blo 255820 600409 := bstep (se 2 (by rfl) ⟨225153, by rfl⟩ : syracuseStep 600409 = 450307) B450307
theorem B2107949 : Blo 255820 2107949 := bstep (se 3 (by rfl) ⟨395240, by rfl⟩ : syracuseStep 2107949 = 790481) B790481
theorem B1288921 : Blo 255820 1288921 := bstep (se 2 (by rfl) ⟨483345, by rfl⟩ : syracuseStep 1288921 = 966691) B966691
theorem B437015 : Blo 255820 437015 := bstep (se 1 (by rfl) ⟨327761, by rfl⟩ : syracuseStep 437015 = 655523) B655523
theorem B1846091 : Blo 255820 1846091 := bstep (se 1 (by rfl) ⟨1384568, by rfl⟩ : syracuseStep 1846091 = 2769137) B2769137
theorem B437143 : Blo 255820 437143 := bstep (se 1 (by rfl) ⟨327857, by rfl⟩ : syracuseStep 437143 = 655715) B655715
theorem B732235 : Blo 255820 732235 := bstep (se 1 (by rfl) ⟨549176, by rfl⟩ : syracuseStep 732235 = 1098353) B1098353
theorem B1059929 : Blo 255820 1059929 := bstep (se 2 (by rfl) ⟨397473, by rfl⟩ : syracuseStep 1059929 = 794947) B794947
theorem B2206925 : Blo 255820 2206925 := bstep (se 3 (by rfl) ⟨413798, by rfl⟩ : syracuseStep 2206925 = 827597) B827597
theorem B273623 : Blo 255820 273623 := bstep (se 1 (by rfl) ⟨205217, by rfl⟩ : syracuseStep 273623 = 410435) B410435
theorem B1092953 : Blo 255820 1092953 := bstep (se 2 (by rfl) ⟨409857, by rfl⟩ : syracuseStep 1092953 = 819715) B819715
theorem B732509 : Blo 255820 732509 := bstep (se 3 (by rfl) ⟨137345, by rfl⟩ : syracuseStep 732509 = 274691) B274691
theorem B437771 : Blo 255820 437771 := bstep (se 1 (by rfl) ⟨328328, by rfl⟩ : syracuseStep 437771 = 656657) B656657
theorem B863837 : Blo 255820 863837 := bstep (se 3 (by rfl) ⟨161969, by rfl⟩ : syracuseStep 863837 = 323939) B323939
theorem B437899 : Blo 255820 437899 := bstep (se 1 (by rfl) ⟨328424, by rfl⟩ : syracuseStep 437899 = 656849) B656849
theorem B732851 : Blo 255820 732851 := bstep (se 1 (by rfl) ⟨549638, by rfl⟩ : syracuseStep 732851 = 1099277) B1099277
theorem B831197 : Blo 255820 831197 := bstep (se 3 (by rfl) ⟨155849, by rfl⟩ : syracuseStep 831197 = 311699) B311699
theorem B438041 : Blo 255820 438041 := bstep (se 2 (by rfl) ⟨164265, by rfl⟩ : syracuseStep 438041 = 328531) B328531
theorem B274315 : Blo 255820 274315 := bstep (se 1 (by rfl) ⟨205736, by rfl⟩ : syracuseStep 274315 = 411473) B411473
theorem B438169 : Blo 255820 438169 := bstep (se 2 (by rfl) ⟨164313, by rfl⟩ : syracuseStep 438169 = 328627) B328627
theorem B1323053 : Blo 255820 1323053 := bstep (se 3 (by rfl) ⟨248072, by rfl⟩ : syracuseStep 1323053 = 496145) B496145
theorem B307351 : Blo 255820 307351 := bstep (se 1 (by rfl) ⟨230513, by rfl⟩ : syracuseStep 307351 = 461027) B461027
theorem B1094219 : Blo 255820 1094219 := bstep (se 1 (by rfl) ⟨820664, by rfl⟩ : syracuseStep 1094219 = 1641329) B1641329
theorem B864971 : Blo 255820 864971 := bstep (se 1 (by rfl) ⟨648728, by rfl⟩ : syracuseStep 864971 = 1297457) B1297457
theorem B1389413 : Blo 255820 1389413 := bstep (se 4 (by rfl) ⟨130257, by rfl⟩ : syracuseStep 1389413 = 260515) B260515
theorem B1094579 : Blo 255820 1094579 := bstep (se 1 (by rfl) ⟨820934, by rfl⟩ : syracuseStep 1094579 = 1641869) B1641869
theorem B865241 : Blo 255820 865241 := bstep (se 2 (by rfl) ⟨324465, by rfl⟩ : syracuseStep 865241 = 648931) B648931
theorem B439319 : Blo 255820 439319 := bstep (se 1 (by rfl) ⟨329489, by rfl⟩ : syracuseStep 439319 = 658979) B658979
theorem B439499 : Blo 255820 439499 := bstep (se 1 (by rfl) ⟨329624, by rfl⟩ : syracuseStep 439499 = 659249) B659249
theorem B1946915 : Blo 255820 1946915 := bstep (se 1 (by rfl) ⟨1460186, by rfl⟩ : syracuseStep 1946915 = 2920373) B2920373
theorem B701747 : Blo 255820 701747 := bstep (se 1 (by rfl) ⟨526310, by rfl⟩ : syracuseStep 701747 = 1052621) B1052621
theorem B275767 : Blo 255820 275767 := bstep (se 1 (by rfl) ⟨206825, by rfl⟩ : syracuseStep 275767 = 413651) B413651
theorem B865943 : Blo 255820 865943 := bstep (se 1 (by rfl) ⟨649457, by rfl⟩ : syracuseStep 865943 = 1298915) B1298915
theorem B276139 : Blo 255820 276139 := bstep (se 1 (by rfl) ⟨207104, by rfl⟩ : syracuseStep 276139 = 414209) B414209
theorem B734923 : Blo 255820 734923 := bstep (se 1 (by rfl) ⟨551192, by rfl⟩ : syracuseStep 734923 = 1102385) B1102385
theorem B309143 : Blo 255820 309143 := bstep (se 1 (by rfl) ⟨231857, by rfl⟩ : syracuseStep 309143 = 463715) B463715
theorem B931985 : Blo 255820 931985 := bstep (se 2 (by rfl) ⟨349494, by rfl⟩ : syracuseStep 931985 = 698989) B698989
theorem B866483 : Blo 255820 866483 := bstep (se 1 (by rfl) ⟨649862, by rfl⟩ : syracuseStep 866483 = 1299725) B1299725
theorem B735425 : Blo 255820 735425 := bstep (se 2 (by rfl) ⟨275784, by rfl⟩ : syracuseStep 735425 = 551569) B551569
theorem B866753 : Blo 255820 866753 := bstep (se 2 (by rfl) ⟨325032, by rfl⟩ : syracuseStep 866753 = 650065) B650065
theorem B735767 : Blo 255820 735767 := bstep (se 1 (by rfl) ⟨551825, by rfl⟩ : syracuseStep 735767 = 1103651) B1103651
theorem B309835 : Blo 255820 309835 := bstep (se 1 (by rfl) ⟨232376, by rfl⟩ : syracuseStep 309835 = 464753) B464753
theorem B4209245 : Blo 255820 4209245 := bstep (se 3 (by rfl) ⟨789233, by rfl⟩ : syracuseStep 4209245 = 1578467) B1578467
theorem B867293 : Blo 255820 867293 := bstep (se 3 (by rfl) ⟨162617, by rfl⟩ : syracuseStep 867293 = 325235) B325235
theorem B1457453 : Blo 255820 1457453 := bstep (se 3 (by rfl) ⟨273272, by rfl⟩ : syracuseStep 1457453 = 546545) B546545
theorem B1654091 : Blo 255820 1654091 := bstep (se 1 (by rfl) ⟨1240568, by rfl⟩ : syracuseStep 1654091 = 2481137) B2481137
theorem B1654451 : Blo 255820 1654451 := bstep (se 1 (by rfl) ⟨1240838, by rfl⟩ : syracuseStep 1654451 = 2481677) B2481677
theorem B868427 : Blo 255820 868427 := bstep (se 1 (by rfl) ⟨651320, by rfl⟩ : syracuseStep 868427 = 1302641) B1302641
theorem B1851569 : Blo 255820 1851569 := bstep (se 2 (by rfl) ⟨694338, by rfl⟩ : syracuseStep 1851569 = 1388677) B1388677
theorem B442711 : Blo 255820 442711 := bstep (se 1 (by rfl) ⟨332033, by rfl⟩ : syracuseStep 442711 = 664067) B664067
theorem B868697 : Blo 255820 868697 := bstep (se 2 (by rfl) ⟨325761, by rfl⟩ : syracuseStep 868697 = 651523) B651523
theorem B737885 : Blo 255820 737885 := bstep (se 3 (by rfl) ⟨138353, by rfl⟩ : syracuseStep 737885 = 276707) B276707
theorem B738227 : Blo 255820 738227 := bstep (se 1 (by rfl) ⟨553670, by rfl⟩ : syracuseStep 738227 = 1107341) B1107341
theorem B1557521 : Blo 255820 1557521 := bstep (se 2 (by rfl) ⟨584070, by rfl⟩ : syracuseStep 1557521 = 1168141) B1168141
theorem B869399 : Blo 255820 869399 := bstep (se 1 (by rfl) ⟨652049, by rfl⟩ : syracuseStep 869399 = 1304099) B1304099
theorem B1230173 : Blo 255820 1230173 := bstep (se 3 (by rfl) ⟨230657, by rfl⟩ : syracuseStep 1230173 = 461315) B461315
theorem B411031 : Blo 255820 411031 := bstep (se 1 (by rfl) ⟨308273, by rfl⟩ : syracuseStep 411031 = 616547) B616547
theorem B869939 : Blo 255820 869939 := bstep (se 1 (by rfl) ⟨652454, by rfl⟩ : syracuseStep 869939 = 1304909) B1304909
theorem B1328791 : Blo 255820 1328791 := bstep (se 1 (by rfl) ⟨996593, by rfl⟩ : syracuseStep 1328791 = 1993187) B1993187
theorem B870209 : Blo 255820 870209 := bstep (se 2 (by rfl) ⟨326328, by rfl⟩ : syracuseStep 870209 = 652657) B652657
theorem B1099651 : Blo 255820 1099651 := bstep (se 1 (by rfl) ⟨824738, by rfl⟩ : syracuseStep 1099651 = 1649477) B1649477
theorem B575603 : Blo 255820 575603 := bstep (se 1 (by rfl) ⟨431702, by rfl⟩ : syracuseStep 575603 = 863405) B863405
theorem B575639 : Blo 255820 575639 := bstep (se 1 (by rfl) ⟨431729, by rfl⟩ : syracuseStep 575639 = 863459) B863459
theorem B411851 : Blo 255820 411851 := bstep (se 1 (by rfl) ⟨308888, by rfl⟩ : syracuseStep 411851 = 617777) B617777
theorem B1099993 : Blo 255820 1099993 := bstep (se 2 (by rfl) ⟨412497, by rfl⟩ : syracuseStep 1099993 = 824995) B824995
theorem B575819 : Blo 255820 575819 := bstep (se 1 (by rfl) ⟨431864, by rfl⟩ : syracuseStep 575819 = 863729) B863729
theorem B870749 : Blo 255820 870749 := bstep (se 3 (by rfl) ⟨163265, by rfl⟩ : syracuseStep 870749 = 326531) B326531
theorem B575873 : Blo 255820 575873 := bstep (se 2 (by rfl) ⟨215952, by rfl⟩ : syracuseStep 575873 = 431905) B431905
theorem B707033 : Blo 255820 707033 := bstep (se 2 (by rfl) ⟨265137, by rfl⟩ : syracuseStep 707033 = 530275) B530275
theorem B1952261 : Blo 255820 1952261 := bstep (se 4 (by rfl) ⟨183024, by rfl⟩ : syracuseStep 1952261 = 366049) B366049
theorem B1296971 : Blo 255820 1296971 := bstep (se 1 (by rfl) ⟨972728, by rfl⟩ : syracuseStep 1296971 = 1945457) B1945457
theorem B576089 : Blo 255820 576089 := bstep (se 2 (by rfl) ⟨216033, by rfl⟩ : syracuseStep 576089 = 432067) B432067
theorem B576179 : Blo 255820 576179 := bstep (se 1 (by rfl) ⟨432134, by rfl⟩ : syracuseStep 576179 = 864269) B864269
theorem B576215 : Blo 255820 576215 := bstep (se 1 (by rfl) ⟨432161, by rfl⟩ : syracuseStep 576215 = 864323) B864323
theorem B576395 : Blo 255820 576395 := bstep (se 1 (by rfl) ⟨432296, by rfl⟩ : syracuseStep 576395 = 864593) B864593
theorem B576449 : Blo 255820 576449 := bstep (se 2 (by rfl) ⟨216168, by rfl⟩ : syracuseStep 576449 = 432337) B432337
theorem B1100951 : Blo 255820 1100951 := bstep (se 1 (by rfl) ⟨825713, by rfl⟩ : syracuseStep 1100951 = 1651427) B1651427
theorem B576665 : Blo 255820 576665 := bstep (se 2 (by rfl) ⟨216249, by rfl⟩ : syracuseStep 576665 = 432499) B432499
theorem B576755 : Blo 255820 576755 := bstep (se 1 (by rfl) ⟨432566, by rfl⟩ : syracuseStep 576755 = 865133) B865133
theorem B576791 : Blo 255820 576791 := bstep (se 1 (by rfl) ⟨432593, by rfl⟩ : syracuseStep 576791 = 865187) B865187
theorem B576971 : Blo 255820 576971 := bstep (se 1 (by rfl) ⟨432728, by rfl⟩ : syracuseStep 576971 = 865457) B865457
theorem B871883 : Blo 255820 871883 := bstep (se 1 (by rfl) ⟨653912, by rfl⟩ : syracuseStep 871883 = 1307825) B1307825
theorem B577025 : Blo 255820 577025 := bstep (se 2 (by rfl) ⟨216384, by rfl⟩ : syracuseStep 577025 = 432769) B432769
theorem B577241 : Blo 255820 577241 := bstep (se 2 (by rfl) ⟨216465, by rfl⟩ : syracuseStep 577241 = 432931) B432931
theorem B872153 : Blo 255820 872153 := bstep (se 2 (by rfl) ⟨327057, by rfl⟩ : syracuseStep 872153 = 654115) B654115
theorem B4378373 : Blo 255820 4378373 := bstep (se 4 (by rfl) ⟨410472, by rfl⟩ : syracuseStep 4378373 = 820945) B820945
theorem B1265453 : Blo 255820 1265453 := bstep (se 3 (by rfl) ⟨237272, by rfl⟩ : syracuseStep 1265453 = 474545) B474545
theorem B577331 : Blo 255820 577331 := bstep (se 1 (by rfl) ⟨432998, by rfl⟩ : syracuseStep 577331 = 865997) B865997
theorem B577367 : Blo 255820 577367 := bstep (se 1 (by rfl) ⟨433025, by rfl⟩ : syracuseStep 577367 = 866051) B866051
theorem B577547 : Blo 255820 577547 := bstep (se 1 (by rfl) ⟨433160, by rfl⟩ : syracuseStep 577547 = 866321) B866321
theorem B1134643 : Blo 255820 1134643 := bstep (se 1 (by rfl) ⟨850982, by rfl⟩ : syracuseStep 1134643 = 1701965) B1701965
theorem B577601 : Blo 255820 577601 := bstep (se 2 (by rfl) ⟨216600, by rfl⟩ : syracuseStep 577601 = 433201) B433201
theorem B577817 : Blo 255820 577817 := bstep (se 2 (by rfl) ⟨216681, by rfl⟩ : syracuseStep 577817 = 433363) B433363
theorem B1298753 : Blo 255820 1298753 := bstep (se 2 (by rfl) ⟨487032, by rfl⟩ : syracuseStep 1298753 = 974065) B974065
theorem B577907 : Blo 255820 577907 := bstep (se 1 (by rfl) ⟨433430, by rfl⟩ : syracuseStep 577907 = 866861) B866861
theorem B577943 : Blo 255820 577943 := bstep (se 1 (by rfl) ⟨433457, by rfl⟩ : syracuseStep 577943 = 866915) B866915
theorem B872855 : Blo 255820 872855 := bstep (se 1 (by rfl) ⟨654641, by rfl⟩ : syracuseStep 872855 = 1309283) B1309283
theorem B578123 : Blo 255820 578123 := bstep (se 1 (by rfl) ⟨433592, by rfl⟩ : syracuseStep 578123 = 867185) B867185
theorem B578177 : Blo 255820 578177 := bstep (se 2 (by rfl) ⟨216816, by rfl⟩ : syracuseStep 578177 = 433633) B433633
theorem B1659523 : Blo 255820 1659523 := bstep (se 1 (by rfl) ⟨1244642, by rfl⟩ : syracuseStep 1659523 = 2489285) B2489285
theorem B2347699 : Blo 255820 2347699 := bstep (se 1 (by rfl) ⟨1760774, by rfl⟩ : syracuseStep 2347699 = 3521549) B3521549
theorem B840385 : Blo 255820 840385 := bstep (se 2 (by rfl) ⟨315144, by rfl⟩ : syracuseStep 840385 = 630289) B630289
theorem B1102643 : Blo 255820 1102643 := bstep (se 1 (by rfl) ⟨826982, by rfl⟩ : syracuseStep 1102643 = 1653965) B1653965
theorem B1200961 : Blo 255820 1200961 := bstep (se 2 (by rfl) ⟨450360, by rfl⟩ : syracuseStep 1200961 = 900721) B900721
theorem B578393 : Blo 255820 578393 := bstep (se 2 (by rfl) ⟨216897, by rfl⟩ : syracuseStep 578393 = 433795) B433795
theorem B1954691 : Blo 255820 1954691 := bstep (se 1 (by rfl) ⟨1466018, by rfl⟩ : syracuseStep 1954691 = 2932037) B2932037
theorem B578483 : Blo 255820 578483 := bstep (se 1 (by rfl) ⟨433862, by rfl⟩ : syracuseStep 578483 = 867725) B867725
theorem B873395 : Blo 255820 873395 := bstep (se 1 (by rfl) ⟨655046, by rfl⟩ : syracuseStep 873395 = 1310093) B1310093
theorem B578519 : Blo 255820 578519 := bstep (se 1 (by rfl) ⟨433889, by rfl⟩ : syracuseStep 578519 = 867779) B867779
theorem B578699 : Blo 255820 578699 := bstep (se 1 (by rfl) ⟨434024, by rfl⟩ : syracuseStep 578699 = 868049) B868049
theorem B578753 : Blo 255820 578753 := bstep (se 2 (by rfl) ⟨217032, by rfl⟩ : syracuseStep 578753 = 434065) B434065
theorem B873665 : Blo 255820 873665 := bstep (se 2 (by rfl) ⟨327624, by rfl⟩ : syracuseStep 873665 = 655249) B655249
theorem B972107 : Blo 255820 972107 := bstep (se 1 (by rfl) ⟨729080, by rfl⟩ : syracuseStep 972107 = 1458161) B1458161
theorem B972121 : Blo 255820 972121 := bstep (se 2 (by rfl) ⟨364545, by rfl⟩ : syracuseStep 972121 = 729091) B729091
theorem B578969 : Blo 255820 578969 := bstep (se 2 (by rfl) ⟨217113, by rfl⟩ : syracuseStep 578969 = 434227) B434227
theorem B1168813 : Blo 255820 1168813 := bstep (se 3 (by rfl) ⟨219152, by rfl⟩ : syracuseStep 1168813 = 438305) B438305
theorem B579059 : Blo 255820 579059 := bstep (se 1 (by rfl) ⟨434294, by rfl⟩ : syracuseStep 579059 = 868589) B868589
theorem B579095 : Blo 255820 579095 := bstep (se 1 (by rfl) ⟨434321, by rfl⟩ : syracuseStep 579095 = 868643) B868643
theorem B1594973 : Blo 255820 1594973 := bstep (se 3 (by rfl) ⟨299057, by rfl⟩ : syracuseStep 1594973 = 598115) B598115
theorem B546443 : Blo 255820 546443 := bstep (se 1 (by rfl) ⟨409832, by rfl⟩ : syracuseStep 546443 = 819665) B819665
theorem B579275 : Blo 255820 579275 := bstep (se 1 (by rfl) ⟨434456, by rfl⟩ : syracuseStep 579275 = 868913) B868913
theorem B874205 : Blo 255820 874205 := bstep (se 3 (by rfl) ⟨163913, by rfl⟩ : syracuseStep 874205 = 327827) B327827
theorem B579329 : Blo 255820 579329 := bstep (se 2 (by rfl) ⟨217248, by rfl⟩ : syracuseStep 579329 = 434497) B434497
theorem B579545 : Blo 255820 579545 := bstep (se 2 (by rfl) ⟨217329, by rfl⟩ : syracuseStep 579545 = 434659) B434659
theorem B3299363 : Blo 255820 3299363 := bstep (se 1 (by rfl) ⟨2474522, by rfl⟩ : syracuseStep 3299363 = 4949045) B4949045
theorem B579635 : Blo 255820 579635 := bstep (se 1 (by rfl) ⟨434726, by rfl⟩ : syracuseStep 579635 = 869453) B869453
theorem B579671 : Blo 255820 579671 := bstep (se 1 (by rfl) ⟨434753, by rfl⟩ : syracuseStep 579671 = 869507) B869507
theorem B546905 : Blo 255820 546905 := bstep (se 2 (by rfl) ⟨205089, by rfl⟩ : syracuseStep 546905 = 410179) B410179
theorem B1300697 : Blo 255820 1300697 := bstep (se 2 (by rfl) ⟨487761, by rfl⟩ : syracuseStep 1300697 = 975523) B975523
theorem B579851 : Blo 255820 579851 := bstep (se 1 (by rfl) ⟨434888, by rfl⟩ : syracuseStep 579851 = 869777) B869777
theorem B973079 : Blo 255820 973079 := bstep (se 1 (by rfl) ⟨729809, by rfl⟩ : syracuseStep 973079 = 1459619) B1459619
theorem B1235245 : Blo 255820 1235245 := bstep (se 3 (by rfl) ⟨231608, by rfl⟩ : syracuseStep 1235245 = 463217) B463217
theorem B2644289 : Blo 255820 2644289 := bstep (se 2 (by rfl) ⟨991608, by rfl⟩ : syracuseStep 2644289 = 1983217) B1983217
theorem B579905 : Blo 255820 579905 := bstep (se 2 (by rfl) ⟨217464, by rfl⟩ : syracuseStep 579905 = 434929) B434929
theorem B580121 : Blo 255820 580121 := bstep (se 2 (by rfl) ⟨217545, by rfl⟩ : syracuseStep 580121 = 435091) B435091
theorem B1464925 : Blo 255820 1464925 := bstep (se 3 (by rfl) ⟨274673, by rfl⟩ : syracuseStep 1464925 = 549347) B549347
theorem B580211 : Blo 255820 580211 := bstep (se 1 (by rfl) ⟨435158, by rfl⟩ : syracuseStep 580211 = 870317) B870317
theorem B580247 : Blo 255820 580247 := bstep (se 1 (by rfl) ⟨435185, by rfl⟩ : syracuseStep 580247 = 870371) B870371
theorem B383819 : Blo 255820 383819 := bstep (se 1 (by rfl) ⟨287864, by rfl⟩ : syracuseStep 383819 = 575729) B575729
theorem B580427 : Blo 255820 580427 := bstep (se 1 (by rfl) ⟨435320, by rfl⟩ : syracuseStep 580427 = 870641) B870641
theorem B875339 : Blo 255820 875339 := bstep (se 1 (by rfl) ⟨656504, by rfl⟩ : syracuseStep 875339 = 1313009) B1313009
theorem B383831 : Blo 255820 383831 := bstep (se 1 (by rfl) ⟨287873, by rfl⟩ : syracuseStep 383831 = 575747) B575747
theorem B580481 : Blo 255820 580481 := bstep (se 2 (by rfl) ⟨217680, by rfl⟩ : syracuseStep 580481 = 435361) B435361
theorem B383897 : Blo 255820 383897 := bstep (se 2 (by rfl) ⟨143961, by rfl⟩ : syracuseStep 383897 = 287923) B287923
theorem B941021 : Blo 255820 941021 := bstep (se 3 (by rfl) ⟨176441, by rfl⟩ : syracuseStep 941021 = 352883) B352883
theorem B384011 : Blo 255820 384011 := bstep (se 1 (by rfl) ⟨288008, by rfl⟩ : syracuseStep 384011 = 576017) B576017
theorem B384023 : Blo 255820 384023 := bstep (se 1 (by rfl) ⟨288017, by rfl⟩ : syracuseStep 384023 = 576035) B576035
theorem B384089 : Blo 255820 384089 := bstep (se 2 (by rfl) ⟨144033, by rfl⟩ : syracuseStep 384089 = 288067) B288067
theorem B580697 : Blo 255820 580697 := bstep (se 2 (by rfl) ⟨217761, by rfl⟩ : syracuseStep 580697 = 435523) B435523
theorem B875609 : Blo 255820 875609 := bstep (se 2 (by rfl) ⟨328353, by rfl⟩ : syracuseStep 875609 = 656707) B656707
theorem B580787 : Blo 255820 580787 := bstep (se 1 (by rfl) ⟨435590, by rfl⟩ : syracuseStep 580787 = 871181) B871181
theorem B384203 : Blo 255820 384203 := bstep (se 1 (by rfl) ⟨288152, by rfl⟩ : syracuseStep 384203 = 576305) B576305
theorem B384215 : Blo 255820 384215 := bstep (se 1 (by rfl) ⟨288161, by rfl⟩ : syracuseStep 384215 = 576323) B576323
theorem B580823 : Blo 255820 580823 := bstep (se 1 (by rfl) ⟨435617, by rfl⟩ : syracuseStep 580823 = 871235) B871235
theorem B548083 : Blo 255820 548083 := bstep (se 1 (by rfl) ⟨411062, by rfl⟩ : syracuseStep 548083 = 822125) B822125
theorem B384281 : Blo 255820 384281 := bstep (se 2 (by rfl) ⟨144105, by rfl⟩ : syracuseStep 384281 = 288211) B288211
theorem B1039661 : Blo 255820 1039661 := bstep (se 3 (by rfl) ⟨194936, by rfl⟩ : syracuseStep 1039661 = 389873) B389873
theorem B384395 : Blo 255820 384395 := bstep (se 1 (by rfl) ⟨288296, by rfl⟩ : syracuseStep 384395 = 576593) B576593
theorem B581003 : Blo 255820 581003 := bstep (se 1 (by rfl) ⟨435752, by rfl⟩ : syracuseStep 581003 = 871505) B871505
theorem B384407 : Blo 255820 384407 := bstep (se 1 (by rfl) ⟨288305, by rfl⟩ : syracuseStep 384407 = 576611) B576611
theorem B1105325 : Blo 255820 1105325 := bstep (se 3 (by rfl) ⟨207248, by rfl⟩ : syracuseStep 1105325 = 414497) B414497
theorem B581057 : Blo 255820 581057 := bstep (se 2 (by rfl) ⟨217896, by rfl⟩ : syracuseStep 581057 = 435793) B435793
theorem B384473 : Blo 255820 384473 := bstep (se 2 (by rfl) ⟨144177, by rfl⟩ : syracuseStep 384473 = 288355) B288355
theorem B974339 : Blo 255820 974339 := bstep (se 1 (by rfl) ⟨730754, by rfl⟩ : syracuseStep 974339 = 1461509) B1461509
theorem B384587 : Blo 255820 384587 := bstep (se 1 (by rfl) ⟨288440, by rfl⟩ : syracuseStep 384587 = 576881) B576881
theorem B384599 : Blo 255820 384599 := bstep (se 1 (by rfl) ⟨288449, by rfl⟩ : syracuseStep 384599 = 576899) B576899
theorem B384665 : Blo 255820 384665 := bstep (se 2 (by rfl) ⟨144249, by rfl⟩ : syracuseStep 384665 = 288499) B288499
theorem B581273 : Blo 255820 581273 := bstep (se 2 (by rfl) ⟨217977, by rfl⟩ : syracuseStep 581273 = 435955) B435955
theorem B548545 : Blo 255820 548545 := bstep (se 2 (by rfl) ⟨205704, by rfl⟩ : syracuseStep 548545 = 411409) B411409
theorem B581363 : Blo 255820 581363 := bstep (se 1 (by rfl) ⟨436022, by rfl⟩ : syracuseStep 581363 = 872045) B872045
theorem B384779 : Blo 255820 384779 := bstep (se 1 (by rfl) ⟨288584, by rfl⟩ : syracuseStep 384779 = 577169) B577169
theorem B384791 : Blo 255820 384791 := bstep (se 1 (by rfl) ⟨288593, by rfl⟩ : syracuseStep 384791 = 577187) B577187
theorem B1171223 : Blo 255820 1171223 := bstep (se 1 (by rfl) ⟨878417, by rfl⟩ : syracuseStep 1171223 = 1756835) B1756835
theorem B581399 : Blo 255820 581399 := bstep (se 1 (by rfl) ⟨436049, by rfl⟩ : syracuseStep 581399 = 872099) B872099
theorem B876311 : Blo 255820 876311 := bstep (se 1 (by rfl) ⟨657233, by rfl⟩ : syracuseStep 876311 = 1314467) B1314467
theorem B1302317 : Blo 255820 1302317 := bstep (se 3 (by rfl) ⟨244184, by rfl⟩ : syracuseStep 1302317 = 488369) B488369
theorem B384857 : Blo 255820 384857 := bstep (se 2 (by rfl) ⟨144321, by rfl⟩ : syracuseStep 384857 = 288643) B288643
theorem B1171351 : Blo 255820 1171351 := bstep (se 1 (by rfl) ⟨878513, by rfl⟩ : syracuseStep 1171351 = 1757027) B1757027
theorem B384971 : Blo 255820 384971 := bstep (se 1 (by rfl) ⟨288728, by rfl⟩ : syracuseStep 384971 = 577457) B577457
theorem B581579 : Blo 255820 581579 := bstep (se 1 (by rfl) ⟨436184, by rfl⟩ : syracuseStep 581579 = 872369) B872369
theorem B384983 : Blo 255820 384983 := bstep (se 1 (by rfl) ⟨288737, by rfl⟩ : syracuseStep 384983 = 577475) B577475
theorem B581633 : Blo 255820 581633 := bstep (se 2 (by rfl) ⟨218112, by rfl⟩ : syracuseStep 581633 = 436225) B436225
theorem B385049 : Blo 255820 385049 := bstep (se 2 (by rfl) ⟨144393, by rfl⟩ : syracuseStep 385049 = 288787) B288787
theorem B1335361 : Blo 255820 1335361 := bstep (se 2 (by rfl) ⟨500760, by rfl⟩ : syracuseStep 1335361 = 1001521) B1001521
theorem B385163 : Blo 255820 385163 := bstep (se 1 (by rfl) ⟨288872, by rfl⟩ : syracuseStep 385163 = 577745) B577745
theorem B385175 : Blo 255820 385175 := bstep (se 1 (by rfl) ⟨288881, by rfl⟩ : syracuseStep 385175 = 577763) B577763
theorem B1958093 : Blo 255820 1958093 := bstep (se 3 (by rfl) ⟨367142, by rfl⟩ : syracuseStep 1958093 = 734285) B734285
theorem B385241 : Blo 255820 385241 := bstep (se 2 (by rfl) ⟨144465, by rfl⟩ : syracuseStep 385241 = 288931) B288931
theorem B581849 : Blo 255820 581849 := bstep (se 2 (by rfl) ⟨218193, by rfl⟩ : syracuseStep 581849 = 436387) B436387
theorem B1401133 : Blo 255820 1401133 := bstep (se 3 (by rfl) ⟨262712, by rfl⟩ : syracuseStep 1401133 = 525425) B525425
theorem B581939 : Blo 255820 581939 := bstep (se 1 (by rfl) ⟨436454, by rfl⟩ : syracuseStep 581939 = 872909) B872909
theorem B876851 : Blo 255820 876851 := bstep (se 1 (by rfl) ⟨657638, by rfl⟩ : syracuseStep 876851 = 1315277) B1315277
theorem B385355 : Blo 255820 385355 := bstep (se 1 (by rfl) ⟨289016, by rfl⟩ : syracuseStep 385355 = 578033) B578033
theorem B385367 : Blo 255820 385367 := bstep (se 1 (by rfl) ⟨289025, by rfl⟩ : syracuseStep 385367 = 578051) B578051
theorem B581975 : Blo 255820 581975 := bstep (se 1 (by rfl) ⟨436481, by rfl⟩ : syracuseStep 581975 = 872963) B872963
theorem B1171805 : Blo 255820 1171805 := bstep (se 3 (by rfl) ⟨219713, by rfl⟩ : syracuseStep 1171805 = 439427) B439427
theorem B549271 : Blo 255820 549271 := bstep (se 1 (by rfl) ⟨411953, by rfl⟩ : syracuseStep 549271 = 823907) B823907
theorem B385433 : Blo 255820 385433 := bstep (se 2 (by rfl) ⟨144537, by rfl⟩ : syracuseStep 385433 = 289075) B289075
theorem B778675 : Blo 255820 778675 := bstep (se 1 (by rfl) ⟨584006, by rfl⟩ : syracuseStep 778675 = 1168013) B1168013
theorem B385547 : Blo 255820 385547 := bstep (se 1 (by rfl) ⟨289160, by rfl⟩ : syracuseStep 385547 = 578321) B578321
theorem B582155 : Blo 255820 582155 := bstep (se 1 (by rfl) ⟨436616, by rfl⟩ : syracuseStep 582155 = 873233) B873233
theorem B1204753 : Blo 255820 1204753 := bstep (se 2 (by rfl) ⟨451782, by rfl⟩ : syracuseStep 1204753 = 903565) B903565
theorem B385559 : Blo 255820 385559 := bstep (se 1 (by rfl) ⟨289169, by rfl⟩ : syracuseStep 385559 = 578339) B578339
theorem B582209 : Blo 255820 582209 := bstep (se 2 (by rfl) ⟨218328, by rfl⟩ : syracuseStep 582209 = 436657) B436657
theorem B385625 : Blo 255820 385625 := bstep (se 2 (by rfl) ⟨144609, by rfl⟩ : syracuseStep 385625 = 289219) B289219
theorem B1270451 : Blo 255820 1270451 := bstep (se 1 (by rfl) ⟨952838, by rfl⟩ : syracuseStep 1270451 = 1905677) B1905677
theorem B1958579 : Blo 255820 1958579 := bstep (se 1 (by rfl) ⟨1468934, by rfl⟩ : syracuseStep 1958579 = 2937869) B2937869
theorem B385739 : Blo 255820 385739 := bstep (se 1 (by rfl) ⟨289304, by rfl⟩ : syracuseStep 385739 = 578609) B578609
theorem B385751 : Blo 255820 385751 := bstep (se 1 (by rfl) ⟨289313, by rfl⟩ : syracuseStep 385751 = 578627) B578627
theorem B647959 : Blo 255820 647959 := bstep (se 1 (by rfl) ⟨485969, by rfl⟩ : syracuseStep 647959 = 971939) B971939
theorem B385817 : Blo 255820 385817 := bstep (se 2 (by rfl) ⟨144681, by rfl⟩ : syracuseStep 385817 = 289363) B289363
theorem B582425 : Blo 255820 582425 := bstep (se 2 (by rfl) ⟨218409, by rfl⟩ : syracuseStep 582425 = 436819) B436819
theorem B582515 : Blo 255820 582515 := bstep (se 1 (by rfl) ⟨436886, by rfl⟩ : syracuseStep 582515 = 873773) B873773
theorem B385931 : Blo 255820 385931 := bstep (se 1 (by rfl) ⟨289448, by rfl⟩ : syracuseStep 385931 = 578897) B578897
theorem B385943 : Blo 255820 385943 := bstep (se 1 (by rfl) ⟨289457, by rfl⟩ : syracuseStep 385943 = 578915) B578915
theorem B582551 : Blo 255820 582551 := bstep (se 1 (by rfl) ⟨436913, by rfl⟩ : syracuseStep 582551 = 873827) B873827
theorem B386009 : Blo 255820 386009 := bstep (se 2 (by rfl) ⟨144753, by rfl⟩ : syracuseStep 386009 = 289507) B289507
theorem B1860569 : Blo 255820 1860569 := bstep (se 2 (by rfl) ⟨697713, by rfl⟩ : syracuseStep 1860569 = 1395427) B1395427
theorem B386123 : Blo 255820 386123 := bstep (se 1 (by rfl) ⟨289592, by rfl⟩ : syracuseStep 386123 = 579185) B579185
theorem B582731 : Blo 255820 582731 := bstep (se 1 (by rfl) ⟨437048, by rfl⟩ : syracuseStep 582731 = 874097) B874097
theorem B386135 : Blo 255820 386135 := bstep (se 1 (by rfl) ⟨289601, by rfl⟩ : syracuseStep 386135 = 579203) B579203
theorem B287851 : Blo 255820 287851 := bstep (se 1 (by rfl) ⟨215888, by rfl⟩ : syracuseStep 287851 = 431777) B431777
theorem B582785 : Blo 255820 582785 := bstep (se 2 (by rfl) ⟨218544, by rfl⟩ : syracuseStep 582785 = 437089) B437089
theorem B386201 : Blo 255820 386201 := bstep (se 2 (by rfl) ⟨144825, by rfl⟩ : syracuseStep 386201 = 289651) B289651
theorem B648395 : Blo 255820 648395 := bstep (se 1 (by rfl) ⟨486296, by rfl⟩ : syracuseStep 648395 = 972593) B972593
theorem B550091 : Blo 255820 550091 := bstep (se 1 (by rfl) ⟨412568, by rfl⟩ : syracuseStep 550091 = 825137) B825137
theorem B287959 : Blo 255820 287959 := bstep (se 1 (by rfl) ⟨215969, by rfl⟩ : syracuseStep 287959 = 431939) B431939
theorem B386315 : Blo 255820 386315 := bstep (se 1 (by rfl) ⟨289736, by rfl⟩ : syracuseStep 386315 = 579473) B579473
theorem B386327 : Blo 255820 386327 := bstep (se 1 (by rfl) ⟨289745, by rfl⟩ : syracuseStep 386327 = 579491) B579491
theorem B2090285 : Blo 255820 2090285 := bstep (se 3 (by rfl) ⟨391928, by rfl⟩ : syracuseStep 2090285 = 783857) B783857
theorem B386393 : Blo 255820 386393 := bstep (se 2 (by rfl) ⟨144897, by rfl⟩ : syracuseStep 386393 = 289795) B289795
theorem B583001 : Blo 255820 583001 := bstep (se 2 (by rfl) ⟨218625, by rfl⟩ : syracuseStep 583001 = 437251) B437251
theorem B288139 : Blo 255820 288139 := bstep (se 1 (by rfl) ⟨216104, by rfl⟩ : syracuseStep 288139 = 432209) B432209
theorem B583091 : Blo 255820 583091 := bstep (se 1 (by rfl) ⟨437318, by rfl⟩ : syracuseStep 583091 = 874637) B874637
theorem B1598899 : Blo 255820 1598899 := bstep (se 1 (by rfl) ⟨1199174, by rfl⟩ : syracuseStep 1598899 = 2398349) B2398349
theorem B386507 : Blo 255820 386507 := bstep (se 1 (by rfl) ⟨289880, by rfl⟩ : syracuseStep 386507 = 579761) B579761
theorem B386519 : Blo 255820 386519 := bstep (se 1 (by rfl) ⟨289889, by rfl⟩ : syracuseStep 386519 = 579779) B579779
theorem B583127 : Blo 255820 583127 := bstep (se 1 (by rfl) ⟨437345, by rfl⟩ : syracuseStep 583127 = 874691) B874691
theorem B288247 : Blo 255820 288247 := bstep (se 1 (by rfl) ⟨216185, by rfl⟩ : syracuseStep 288247 = 432371) B432371
theorem B386585 : Blo 255820 386585 := bstep (se 2 (by rfl) ⟨144969, by rfl⟩ : syracuseStep 386585 = 289939) B289939
theorem B648769 : Blo 255820 648769 := bstep (se 2 (by rfl) ⟨243288, by rfl⟩ : syracuseStep 648769 = 486577) B486577
theorem B386699 : Blo 255820 386699 := bstep (se 1 (by rfl) ⟨290024, by rfl⟩ : syracuseStep 386699 = 580049) B580049
theorem B583307 : Blo 255820 583307 := bstep (se 1 (by rfl) ⟨437480, by rfl⟩ : syracuseStep 583307 = 874961) B874961
theorem B386711 : Blo 255820 386711 := bstep (se 1 (by rfl) ⟨290033, by rfl⟩ : syracuseStep 386711 = 580067) B580067
theorem B288427 : Blo 255820 288427 := bstep (se 1 (by rfl) ⟨216320, by rfl⟩ : syracuseStep 288427 = 432641) B432641
theorem B583361 : Blo 255820 583361 := bstep (se 2 (by rfl) ⟨218760, by rfl⟩ : syracuseStep 583361 = 437521) B437521
theorem B386777 : Blo 255820 386777 := bstep (se 2 (by rfl) ⟨145041, by rfl⟩ : syracuseStep 386777 = 290083) B290083
theorem B288535 : Blo 255820 288535 := bstep (se 1 (by rfl) ⟨216401, by rfl⟩ : syracuseStep 288535 = 432803) B432803
theorem B386891 : Blo 255820 386891 := bstep (se 1 (by rfl) ⟨290168, by rfl⟩ : syracuseStep 386891 = 580337) B580337
theorem B255831 : Blo 255820 255831 := bstep (se 1 (by rfl) ⟨191873, by rfl⟩ : syracuseStep 255831 = 383747) B383747
theorem B386903 : Blo 255820 386903 := bstep (se 1 (by rfl) ⟨290177, by rfl⟩ : syracuseStep 386903 = 580355) B580355
theorem B255851 : Blo 255820 255851 := bstep (se 1 (by rfl) ⟨191888, by rfl⟩ : syracuseStep 255851 = 383777) B383777
theorem B255863 : Blo 255820 255863 := bstep (se 1 (by rfl) ⟨191897, by rfl⟩ : syracuseStep 255863 = 383795) B383795
theorem B255883 : Blo 255820 255883 := bstep (se 1 (by rfl) ⟨191912, by rfl⟩ : syracuseStep 255883 = 383825) B383825
theorem B255895 : Blo 255820 255895 := bstep (se 1 (by rfl) ⟨191921, by rfl⟩ : syracuseStep 255895 = 383843) B383843
theorem B386969 : Blo 255820 386969 := bstep (se 2 (by rfl) ⟨145113, by rfl⟩ : syracuseStep 386969 = 290227) B290227
theorem B583577 : Blo 255820 583577 := bstep (se 2 (by rfl) ⟨218841, by rfl⟩ : syracuseStep 583577 = 437683) B437683
theorem B255915 : Blo 255820 255915 := bstep (se 1 (by rfl) ⟨191936, by rfl⟩ : syracuseStep 255915 = 383873) B383873
theorem B255927 : Blo 255820 255927 := bstep (se 1 (by rfl) ⟨191945, by rfl⟩ : syracuseStep 255927 = 383891) B383891
theorem B255947 : Blo 255820 255947 := bstep (se 1 (by rfl) ⟨191960, by rfl⟩ : syracuseStep 255947 = 383921) B383921
theorem B288715 : Blo 255820 288715 := bstep (se 1 (by rfl) ⟨216536, by rfl⟩ : syracuseStep 288715 = 433073) B433073
theorem B255959 : Blo 255820 255959 := bstep (se 1 (by rfl) ⟨191969, by rfl⟩ : syracuseStep 255959 = 383939) B383939
theorem B255979 : Blo 255820 255979 := bstep (se 1 (by rfl) ⟨191984, by rfl⟩ : syracuseStep 255979 = 383969) B383969
theorem B583667 : Blo 255820 583667 := bstep (se 1 (by rfl) ⟨437750, by rfl⟩ : syracuseStep 583667 = 875501) B875501
theorem B255991 : Blo 255820 255991 := bstep (se 1 (by rfl) ⟨191993, by rfl⟩ : syracuseStep 255991 = 383987) B383987
theorem B256011 : Blo 255820 256011 := bstep (se 1 (by rfl) ⟨192008, by rfl⟩ : syracuseStep 256011 = 384017) B384017
theorem B387083 : Blo 255820 387083 := bstep (se 1 (by rfl) ⟨290312, by rfl⟩ : syracuseStep 387083 = 580625) B580625
theorem B256023 : Blo 255820 256023 := bstep (se 1 (by rfl) ⟨192017, by rfl⟩ : syracuseStep 256023 = 384035) B384035
theorem B387095 : Blo 255820 387095 := bstep (se 1 (by rfl) ⟨290321, by rfl⟩ : syracuseStep 387095 = 580643) B580643
theorem B550937 : Blo 255820 550937 := bstep (se 2 (by rfl) ⟨206601, by rfl⟩ : syracuseStep 550937 = 413203) B413203
theorem B583703 : Blo 255820 583703 := bstep (se 1 (by rfl) ⟨437777, by rfl⟩ : syracuseStep 583703 = 875555) B875555
theorem B256043 : Blo 255820 256043 := bstep (se 1 (by rfl) ⟨192032, by rfl⟩ : syracuseStep 256043 = 384065) B384065
theorem B256055 : Blo 255820 256055 := bstep (se 1 (by rfl) ⟨192041, by rfl⟩ : syracuseStep 256055 = 384083) B384083
theorem B288823 : Blo 255820 288823 := bstep (se 1 (by rfl) ⟨216617, by rfl⟩ : syracuseStep 288823 = 433235) B433235
theorem B256075 : Blo 255820 256075 := bstep (se 1 (by rfl) ⟨192056, by rfl⟩ : syracuseStep 256075 = 384113) B384113
theorem B256087 : Blo 255820 256087 := bstep (se 1 (by rfl) ⟨192065, by rfl⟩ : syracuseStep 256087 = 384131) B384131
theorem B387161 : Blo 255820 387161 := bstep (se 2 (by rfl) ⟨145185, by rfl⟩ : syracuseStep 387161 = 290371) B290371
theorem B1960037 : Blo 255820 1960037 := bstep (se 4 (by rfl) ⟨183753, by rfl⟩ : syracuseStep 1960037 = 367507) B367507
theorem B256107 : Blo 255820 256107 := bstep (se 1 (by rfl) ⟨192080, by rfl⟩ : syracuseStep 256107 = 384161) B384161
theorem B256119 : Blo 255820 256119 := bstep (se 1 (by rfl) ⟨192089, by rfl⟩ : syracuseStep 256119 = 384179) B384179
theorem B2779267 : Blo 255820 2779267 := bstep (se 1 (by rfl) ⟨2084450, by rfl⟩ : syracuseStep 2779267 = 4168901) B4168901
theorem B256139 : Blo 255820 256139 := bstep (se 1 (by rfl) ⟨192104, by rfl⟩ : syracuseStep 256139 = 384209) B384209
theorem B256151 : Blo 255820 256151 := bstep (se 1 (by rfl) ⟨192113, by rfl⟩ : syracuseStep 256151 = 384227) B384227
theorem B649367 : Blo 255820 649367 := bstep (se 1 (by rfl) ⟨487025, by rfl⟩ : syracuseStep 649367 = 974051) B974051
theorem B256171 : Blo 255820 256171 := bstep (se 1 (by rfl) ⟨192128, by rfl⟩ : syracuseStep 256171 = 384257) B384257
theorem B256183 : Blo 255820 256183 := bstep (se 1 (by rfl) ⟨192137, by rfl⟩ : syracuseStep 256183 = 384275) B384275
theorem B256203 : Blo 255820 256203 := bstep (se 1 (by rfl) ⟨192152, by rfl⟩ : syracuseStep 256203 = 384305) B384305
theorem B387275 : Blo 255820 387275 := bstep (se 1 (by rfl) ⟨290456, by rfl⟩ : syracuseStep 387275 = 580913) B580913
theorem B583883 : Blo 255820 583883 := bstep (se 1 (by rfl) ⟨437912, by rfl⟩ : syracuseStep 583883 = 875825) B875825
theorem B256215 : Blo 255820 256215 := bstep (se 1 (by rfl) ⟨192161, by rfl⟩ : syracuseStep 256215 = 384323) B384323
theorem B387287 : Blo 255820 387287 := bstep (se 1 (by rfl) ⟨290465, by rfl⟩ : syracuseStep 387287 = 580931) B580931
theorem B256235 : Blo 255820 256235 := bstep (se 1 (by rfl) ⟨192176, by rfl⟩ : syracuseStep 256235 = 384353) B384353
theorem B289003 : Blo 255820 289003 := bstep (se 1 (by rfl) ⟨216752, by rfl⟩ : syracuseStep 289003 = 433505) B433505
theorem B256247 : Blo 255820 256247 := bstep (se 1 (by rfl) ⟨192185, by rfl⟩ : syracuseStep 256247 = 384371) B384371
theorem B583937 : Blo 255820 583937 := bstep (se 2 (by rfl) ⟨218976, by rfl⟩ : syracuseStep 583937 = 437953) B437953
theorem B1894661 : Blo 255820 1894661 := bstep (se 4 (by rfl) ⟨177624, by rfl⟩ : syracuseStep 1894661 = 355249) B355249
theorem B256267 : Blo 255820 256267 := bstep (se 1 (by rfl) ⟨192200, by rfl⟩ : syracuseStep 256267 = 384401) B384401
theorem B256279 : Blo 255820 256279 := bstep (se 1 (by rfl) ⟨192209, by rfl⟩ : syracuseStep 256279 = 384419) B384419
theorem B387353 : Blo 255820 387353 := bstep (se 2 (by rfl) ⟨145257, by rfl⟩ : syracuseStep 387353 = 290515) B290515
theorem B256299 : Blo 255820 256299 := bstep (se 1 (by rfl) ⟨192224, by rfl⟩ : syracuseStep 256299 = 384449) B384449
theorem B256311 : Blo 255820 256311 := bstep (se 1 (by rfl) ⟨192233, by rfl⟩ : syracuseStep 256311 = 384467) B384467
theorem B256331 : Blo 255820 256331 := bstep (se 1 (by rfl) ⟨192248, by rfl⟩ : syracuseStep 256331 = 384497) B384497
theorem B256343 : Blo 255820 256343 := bstep (se 1 (by rfl) ⟨192257, by rfl⟩ : syracuseStep 256343 = 384515) B384515
theorem B289111 : Blo 255820 289111 := bstep (se 1 (by rfl) ⟨216833, by rfl⟩ : syracuseStep 289111 = 433667) B433667
theorem B256363 : Blo 255820 256363 := bstep (se 1 (by rfl) ⟨192272, by rfl⟩ : syracuseStep 256363 = 384545) B384545
theorem B256375 : Blo 255820 256375 := bstep (se 1 (by rfl) ⟨192281, by rfl⟩ : syracuseStep 256375 = 384563) B384563
theorem B256395 : Blo 255820 256395 := bstep (se 1 (by rfl) ⟨192296, by rfl⟩ : syracuseStep 256395 = 384593) B384593
theorem B387467 : Blo 255820 387467 := bstep (se 1 (by rfl) ⟨290600, by rfl⟩ : syracuseStep 387467 = 581201) B581201
theorem B256407 : Blo 255820 256407 := bstep (se 1 (by rfl) ⟨192305, by rfl⟩ : syracuseStep 256407 = 384611) B384611
theorem B387479 : Blo 255820 387479 := bstep (se 1 (by rfl) ⟨290609, by rfl⟩ : syracuseStep 387479 = 581219) B581219
theorem B256427 : Blo 255820 256427 := bstep (se 1 (by rfl) ⟨192320, by rfl⟩ : syracuseStep 256427 = 384641) B384641
theorem B256439 : Blo 255820 256439 := bstep (se 1 (by rfl) ⟨192329, by rfl⟩ : syracuseStep 256439 = 384659) B384659
theorem B256459 : Blo 255820 256459 := bstep (se 1 (by rfl) ⟨192344, by rfl⟩ : syracuseStep 256459 = 384689) B384689
theorem B256471 : Blo 255820 256471 := bstep (se 1 (by rfl) ⟨192353, by rfl⟩ : syracuseStep 256471 = 384707) B384707
theorem B387545 : Blo 255820 387545 := bstep (se 2 (by rfl) ⟨145329, by rfl⟩ : syracuseStep 387545 = 290659) B290659
theorem B584153 : Blo 255820 584153 := bstep (se 2 (by rfl) ⟨219057, by rfl⟩ : syracuseStep 584153 = 438115) B438115
theorem B256491 : Blo 255820 256491 := bstep (se 1 (by rfl) ⟨192368, by rfl⟩ : syracuseStep 256491 = 384737) B384737
theorem B256503 : Blo 255820 256503 := bstep (se 1 (by rfl) ⟨192377, by rfl⟩ : syracuseStep 256503 = 384755) B384755
theorem B256523 : Blo 255820 256523 := bstep (se 1 (by rfl) ⟨192392, by rfl⟩ : syracuseStep 256523 = 384785) B384785
theorem B289291 : Blo 255820 289291 := bstep (se 1 (by rfl) ⟨216968, by rfl⟩ : syracuseStep 289291 = 433937) B433937
theorem B1239569 : Blo 255820 1239569 := bstep (se 2 (by rfl) ⟨464838, by rfl⟩ : syracuseStep 1239569 = 929677) B929677
theorem B256535 : Blo 255820 256535 := bstep (se 1 (by rfl) ⟨192401, by rfl⟩ : syracuseStep 256535 = 384803) B384803
theorem B256555 : Blo 255820 256555 := bstep (se 1 (by rfl) ⟨192416, by rfl⟩ : syracuseStep 256555 = 384833) B384833
theorem B977453 : Blo 255820 977453 := bstep (se 3 (by rfl) ⟨183272, by rfl⟩ : syracuseStep 977453 = 366545) B366545
theorem B485939 : Blo 255820 485939 := bstep (se 1 (by rfl) ⟨364454, by rfl⟩ : syracuseStep 485939 = 728909) B728909
theorem B584243 : Blo 255820 584243 := bstep (se 1 (by rfl) ⟨438182, by rfl⟩ : syracuseStep 584243 = 876365) B876365
theorem B256567 : Blo 255820 256567 := bstep (se 1 (by rfl) ⟨192425, by rfl⟩ : syracuseStep 256567 = 384851) B384851
theorem B256587 : Blo 255820 256587 := bstep (se 1 (by rfl) ⟨192440, by rfl⟩ : syracuseStep 256587 = 384881) B384881
theorem B1960523 : Blo 255820 1960523 := bstep (se 1 (by rfl) ⟨1470392, by rfl⟩ : syracuseStep 1960523 = 2940785) B2940785
theorem B387659 : Blo 255820 387659 := bstep (se 1 (by rfl) ⟨290744, by rfl⟩ : syracuseStep 387659 = 581489) B581489
theorem B256599 : Blo 255820 256599 := bstep (se 1 (by rfl) ⟨192449, by rfl⟩ : syracuseStep 256599 = 384899) B384899
theorem B387671 : Blo 255820 387671 := bstep (se 1 (by rfl) ⟨290753, by rfl⟩ : syracuseStep 387671 = 581507) B581507
theorem B584279 : Blo 255820 584279 := bstep (se 1 (by rfl) ⟨438209, by rfl⟩ : syracuseStep 584279 = 876419) B876419
theorem B256619 : Blo 255820 256619 := bstep (se 1 (by rfl) ⟨192464, by rfl⟩ : syracuseStep 256619 = 384929) B384929
theorem B256631 : Blo 255820 256631 := bstep (se 1 (by rfl) ⟨192473, by rfl⟩ : syracuseStep 256631 = 384947) B384947
theorem B289399 : Blo 255820 289399 := bstep (se 1 (by rfl) ⟨217049, by rfl⟩ : syracuseStep 289399 = 434099) B434099
theorem B256651 : Blo 255820 256651 := bstep (se 1 (by rfl) ⟨192488, by rfl⟩ : syracuseStep 256651 = 384977) B384977
theorem B256663 : Blo 255820 256663 := bstep (se 1 (by rfl) ⟨192497, by rfl⟩ : syracuseStep 256663 = 384995) B384995
theorem B387737 : Blo 255820 387737 := bstep (se 2 (by rfl) ⟨145401, by rfl⟩ : syracuseStep 387737 = 290803) B290803
theorem B256683 : Blo 255820 256683 := bstep (se 1 (by rfl) ⟨192512, by rfl⟩ : syracuseStep 256683 = 385025) B385025
theorem B551603 : Blo 255820 551603 := bstep (se 1 (by rfl) ⟨413702, by rfl⟩ : syracuseStep 551603 = 827405) B827405
theorem B256695 : Blo 255820 256695 := bstep (se 1 (by rfl) ⟨192521, by rfl⟩ : syracuseStep 256695 = 385043) B385043
theorem B1108673 : Blo 255820 1108673 := bstep (se 2 (by rfl) ⟨415752, by rfl⟩ : syracuseStep 1108673 = 831505) B831505
theorem B486091 : Blo 255820 486091 := bstep (se 1 (by rfl) ⟨364568, by rfl⟩ : syracuseStep 486091 = 729137) B729137
theorem B256715 : Blo 255820 256715 := bstep (se 1 (by rfl) ⟨192536, by rfl⟩ : syracuseStep 256715 = 385073) B385073
theorem B256727 : Blo 255820 256727 := bstep (se 1 (by rfl) ⟨192545, by rfl⟩ : syracuseStep 256727 = 385091) B385091
theorem B256747 : Blo 255820 256747 := bstep (se 1 (by rfl) ⟨192560, by rfl⟩ : syracuseStep 256747 = 385121) B385121
theorem B256759 : Blo 255820 256759 := bstep (se 1 (by rfl) ⟨192569, by rfl⟩ : syracuseStep 256759 = 385139) B385139
theorem B256779 : Blo 255820 256779 := bstep (se 1 (by rfl) ⟨192584, by rfl⟩ : syracuseStep 256779 = 385169) B385169
theorem B387851 : Blo 255820 387851 := bstep (se 1 (by rfl) ⟨290888, by rfl⟩ : syracuseStep 387851 = 581777) B581777
theorem B584459 : Blo 255820 584459 := bstep (se 1 (by rfl) ⟨438344, by rfl⟩ : syracuseStep 584459 = 876689) B876689
theorem B256791 : Blo 255820 256791 := bstep (se 1 (by rfl) ⟨192593, by rfl⟩ : syracuseStep 256791 = 385187) B385187
theorem B387863 : Blo 255820 387863 := bstep (se 1 (by rfl) ⟨290897, by rfl⟩ : syracuseStep 387863 = 581795) B581795
theorem B256811 : Blo 255820 256811 := bstep (se 1 (by rfl) ⟨192608, by rfl⟩ : syracuseStep 256811 = 385217) B385217
theorem B289579 : Blo 255820 289579 := bstep (se 1 (by rfl) ⟨217184, by rfl⟩ : syracuseStep 289579 = 434369) B434369
theorem B256823 : Blo 255820 256823 := bstep (se 1 (by rfl) ⟨192617, by rfl⟩ : syracuseStep 256823 = 385235) B385235
theorem B584513 : Blo 255820 584513 := bstep (se 2 (by rfl) ⟨219192, by rfl⟩ : syracuseStep 584513 = 438385) B438385
theorem B256843 : Blo 255820 256843 := bstep (se 1 (by rfl) ⟨192632, by rfl⟩ : syracuseStep 256843 = 385265) B385265
theorem B256855 : Blo 255820 256855 := bstep (se 1 (by rfl) ⟨192641, by rfl⟩ : syracuseStep 256855 = 385283) B385283
theorem B387929 : Blo 255820 387929 := bstep (se 2 (by rfl) ⟨145473, by rfl⟩ : syracuseStep 387929 = 290947) B290947
theorem B256875 : Blo 255820 256875 := bstep (se 1 (by rfl) ⟨192656, by rfl⟩ : syracuseStep 256875 = 385313) B385313
theorem B256887 : Blo 255820 256887 := bstep (se 1 (by rfl) ⟨192665, by rfl⟩ : syracuseStep 256887 = 385331) B385331
theorem B256907 : Blo 255820 256907 := bstep (se 1 (by rfl) ⟨192680, by rfl⟩ : syracuseStep 256907 = 385361) B385361
theorem B256919 : Blo 255820 256919 := bstep (se 1 (by rfl) ⟨192689, by rfl⟩ : syracuseStep 256919 = 385379) B385379
theorem B289687 : Blo 255820 289687 := bstep (se 1 (by rfl) ⟨217265, by rfl⟩ : syracuseStep 289687 = 434531) B434531
theorem B256939 : Blo 255820 256939 := bstep (se 1 (by rfl) ⟨192704, by rfl⟩ : syracuseStep 256939 = 385409) B385409
theorem B256951 : Blo 255820 256951 := bstep (se 1 (by rfl) ⟨192713, by rfl⟩ : syracuseStep 256951 = 385427) B385427
theorem B650177 : Blo 255820 650177 := bstep (se 2 (by rfl) ⟨243816, by rfl⟩ : syracuseStep 650177 = 487633) B487633
theorem B256971 : Blo 255820 256971 := bstep (se 1 (by rfl) ⟨192728, by rfl⟩ : syracuseStep 256971 = 385457) B385457
theorem B388043 : Blo 255820 388043 := bstep (se 1 (by rfl) ⟨291032, by rfl⟩ : syracuseStep 388043 = 582065) B582065
theorem B256983 : Blo 255820 256983 := bstep (se 1 (by rfl) ⟨192737, by rfl⟩ : syracuseStep 256983 = 385475) B385475
theorem B388055 : Blo 255820 388055 := bstep (se 1 (by rfl) ⟨291041, by rfl⟩ : syracuseStep 388055 = 582083) B582083
theorem B257003 : Blo 255820 257003 := bstep (se 1 (by rfl) ⟨192752, by rfl⟩ : syracuseStep 257003 = 385505) B385505
theorem B257015 : Blo 255820 257015 := bstep (se 1 (by rfl) ⟨192761, by rfl⟩ : syracuseStep 257015 = 385523) B385523
theorem B257035 : Blo 255820 257035 := bstep (se 1 (by rfl) ⟨192776, by rfl⟩ : syracuseStep 257035 = 385553) B385553
theorem B257047 : Blo 255820 257047 := bstep (se 1 (by rfl) ⟨192785, by rfl⟩ : syracuseStep 257047 = 385571) B385571
theorem B1109015 : Blo 255820 1109015 := bstep (se 1 (by rfl) ⟨831761, by rfl⟩ : syracuseStep 1109015 = 1663523) B1663523
theorem B486425 : Blo 255820 486425 := bstep (se 2 (by rfl) ⟨182409, by rfl⟩ : syracuseStep 486425 = 364819) B364819
theorem B388121 : Blo 255820 388121 := bstep (se 2 (by rfl) ⟨145545, by rfl⟩ : syracuseStep 388121 = 291091) B291091
theorem B257067 : Blo 255820 257067 := bstep (se 1 (by rfl) ⟨192800, by rfl⟩ : syracuseStep 257067 = 385601) B385601
theorem B257079 : Blo 255820 257079 := bstep (se 1 (by rfl) ⟨192809, by rfl⟩ : syracuseStep 257079 = 385619) B385619
theorem B257099 : Blo 255820 257099 := bstep (se 1 (by rfl) ⟨192824, by rfl⟩ : syracuseStep 257099 = 385649) B385649
theorem B289867 : Blo 255820 289867 := bstep (se 1 (by rfl) ⟨217400, by rfl⟩ : syracuseStep 289867 = 434801) B434801
theorem B257111 : Blo 255820 257111 := bstep (se 1 (by rfl) ⟨192833, by rfl⟩ : syracuseStep 257111 = 385667) B385667
theorem B257131 : Blo 255820 257131 := bstep (se 1 (by rfl) ⟨192848, by rfl⟩ : syracuseStep 257131 = 385697) B385697
theorem B257143 : Blo 255820 257143 := bstep (se 1 (by rfl) ⟨192857, by rfl⟩ : syracuseStep 257143 = 385715) B385715
theorem B257163 : Blo 255820 257163 := bstep (se 1 (by rfl) ⟨192872, by rfl⟩ : syracuseStep 257163 = 385745) B385745
theorem B388235 : Blo 255820 388235 := bstep (se 1 (by rfl) ⟨291176, by rfl⟩ : syracuseStep 388235 = 582353) B582353
theorem B257175 : Blo 255820 257175 := bstep (se 1 (by rfl) ⟨192881, by rfl⟩ : syracuseStep 257175 = 385763) B385763
theorem B388247 : Blo 255820 388247 := bstep (se 1 (by rfl) ⟨291185, by rfl⟩ : syracuseStep 388247 = 582371) B582371
theorem B257195 : Blo 255820 257195 := bstep (se 1 (by rfl) ⟨192896, by rfl⟩ : syracuseStep 257195 = 385793) B385793
theorem B257207 : Blo 255820 257207 := bstep (se 1 (by rfl) ⟨192905, by rfl⟩ : syracuseStep 257207 = 385811) B385811
theorem B289975 : Blo 255820 289975 := bstep (se 1 (by rfl) ⟨217481, by rfl⟩ : syracuseStep 289975 = 434963) B434963
theorem B257227 : Blo 255820 257227 := bstep (se 1 (by rfl) ⟨192920, by rfl⟩ : syracuseStep 257227 = 385841) B385841
theorem B257239 : Blo 255820 257239 := bstep (se 1 (by rfl) ⟨192929, by rfl⟩ : syracuseStep 257239 = 385859) B385859
theorem B584921 : Blo 255820 584921 := bstep (se 2 (by rfl) ⟨219345, by rfl⟩ : syracuseStep 584921 = 438691) B438691
theorem B388313 : Blo 255820 388313 := bstep (se 2 (by rfl) ⟨145617, by rfl⟩ : syracuseStep 388313 = 291235) B291235
theorem B257259 : Blo 255820 257259 := bstep (se 1 (by rfl) ⟨192944, by rfl⟩ : syracuseStep 257259 = 385889) B385889
theorem B257271 : Blo 255820 257271 := bstep (se 1 (by rfl) ⟨192953, by rfl⟩ : syracuseStep 257271 = 385907) B385907
theorem B257291 : Blo 255820 257291 := bstep (se 1 (by rfl) ⟨192968, by rfl⟩ : syracuseStep 257291 = 385937) B385937
theorem B257303 : Blo 255820 257303 := bstep (se 1 (by rfl) ⟨192977, by rfl⟩ : syracuseStep 257303 = 385955) B385955
theorem B257323 : Blo 255820 257323 := bstep (se 1 (by rfl) ⟨192992, by rfl⟩ : syracuseStep 257323 = 385985) B385985
theorem B978227 : Blo 255820 978227 := bstep (se 1 (by rfl) ⟨733670, by rfl⟩ : syracuseStep 978227 = 1467341) B1467341
theorem B257335 : Blo 255820 257335 := bstep (se 1 (by rfl) ⟨193001, by rfl⟩ : syracuseStep 257335 = 386003) B386003
theorem B257355 : Blo 255820 257355 := bstep (se 1 (by rfl) ⟨193016, by rfl⟩ : syracuseStep 257355 = 386033) B386033
theorem B388427 : Blo 255820 388427 := bstep (se 1 (by rfl) ⟨291320, by rfl⟩ : syracuseStep 388427 = 582641) B582641
theorem B257367 : Blo 255820 257367 := bstep (se 1 (by rfl) ⟨193025, by rfl⟩ : syracuseStep 257367 = 386051) B386051
theorem B388439 : Blo 255820 388439 := bstep (se 1 (by rfl) ⟨291329, by rfl⟩ : syracuseStep 388439 = 582659) B582659
theorem B257387 : Blo 255820 257387 := bstep (se 1 (by rfl) ⟨193040, by rfl⟩ : syracuseStep 257387 = 386081) B386081
theorem B290155 : Blo 255820 290155 := bstep (se 1 (by rfl) ⟨217616, by rfl⟩ : syracuseStep 290155 = 435233) B435233
theorem B257399 : Blo 255820 257399 := bstep (se 1 (by rfl) ⟨193049, by rfl⟩ : syracuseStep 257399 = 386099) B386099
theorem B257419 : Blo 255820 257419 := bstep (se 1 (by rfl) ⟨193064, by rfl⟩ : syracuseStep 257419 = 386129) B386129
theorem B257431 : Blo 255820 257431 := bstep (se 1 (by rfl) ⟨193073, by rfl⟩ : syracuseStep 257431 = 386147) B386147
theorem B388505 : Blo 255820 388505 := bstep (se 2 (by rfl) ⟨145689, by rfl⟩ : syracuseStep 388505 = 291379) B291379
theorem B257451 : Blo 255820 257451 := bstep (se 1 (by rfl) ⟨193088, by rfl⟩ : syracuseStep 257451 = 386177) B386177
theorem B257463 : Blo 255820 257463 := bstep (se 1 (by rfl) ⟨193097, by rfl⟩ : syracuseStep 257463 = 386195) B386195
theorem B257483 : Blo 255820 257483 := bstep (se 1 (by rfl) ⟨193112, by rfl⟩ : syracuseStep 257483 = 386225) B386225
theorem B257495 : Blo 255820 257495 := bstep (se 1 (by rfl) ⟨193121, by rfl⟩ : syracuseStep 257495 = 386243) B386243
theorem B290263 : Blo 255820 290263 := bstep (se 1 (by rfl) ⟨217697, by rfl⟩ : syracuseStep 290263 = 435395) B435395
theorem B650713 : Blo 255820 650713 := bstep (se 2 (by rfl) ⟨244017, by rfl⟩ : syracuseStep 650713 = 488035) B488035
theorem B749017 : Blo 255820 749017 := bstep (se 2 (by rfl) ⟨280881, by rfl⟩ : syracuseStep 749017 = 561763) B561763
theorem B1404377 : Blo 255820 1404377 := bstep (se 2 (by rfl) ⟨526641, by rfl⟩ : syracuseStep 1404377 = 1053283) B1053283
theorem B257515 : Blo 255820 257515 := bstep (se 1 (by rfl) ⟨193136, by rfl⟩ : syracuseStep 257515 = 386273) B386273
theorem B257527 : Blo 255820 257527 := bstep (se 1 (by rfl) ⟨193145, by rfl⟩ : syracuseStep 257527 = 386291) B386291
theorem B257547 : Blo 255820 257547 := bstep (se 1 (by rfl) ⟨193160, by rfl⟩ : syracuseStep 257547 = 386321) B386321
theorem B388619 : Blo 255820 388619 := bstep (se 1 (by rfl) ⟨291464, by rfl⟩ : syracuseStep 388619 = 582929) B582929
theorem B257559 : Blo 255820 257559 := bstep (se 1 (by rfl) ⟨193169, by rfl⟩ : syracuseStep 257559 = 386339) B386339
theorem B388631 : Blo 255820 388631 := bstep (se 1 (by rfl) ⟨291473, by rfl⟩ : syracuseStep 388631 = 582947) B582947
theorem B257579 : Blo 255820 257579 := bstep (se 1 (by rfl) ⟨193184, by rfl⟩ : syracuseStep 257579 = 386369) B386369
theorem B749107 : Blo 255820 749107 := bstep (se 1 (by rfl) ⟨561830, by rfl⟩ : syracuseStep 749107 = 1123661) B1123661
theorem B257591 : Blo 255820 257591 := bstep (se 1 (by rfl) ⟨193193, by rfl⟩ : syracuseStep 257591 = 386387) B386387
theorem B257611 : Blo 255820 257611 := bstep (se 1 (by rfl) ⟨193208, by rfl⟩ : syracuseStep 257611 = 386417) B386417
theorem B257623 : Blo 255820 257623 := bstep (se 1 (by rfl) ⟨193217, by rfl⟩ : syracuseStep 257623 = 386435) B386435
theorem B388697 : Blo 255820 388697 := bstep (se 2 (by rfl) ⟨145761, by rfl⟩ : syracuseStep 388697 = 291523) B291523
theorem B1306205 : Blo 255820 1306205 := bstep (se 3 (by rfl) ⟨244913, by rfl⟩ : syracuseStep 1306205 = 489827) B489827
theorem B257643 : Blo 255820 257643 := bstep (se 1 (by rfl) ⟨193232, by rfl⟩ : syracuseStep 257643 = 386465) B386465
theorem B257655 : Blo 255820 257655 := bstep (se 1 (by rfl) ⟨193241, by rfl⟩ : syracuseStep 257655 = 386483) B386483
theorem B552577 : Blo 255820 552577 := bstep (se 2 (by rfl) ⟨207216, by rfl⟩ : syracuseStep 552577 = 414433) B414433
theorem B257675 : Blo 255820 257675 := bstep (se 1 (by rfl) ⟨193256, by rfl⟩ : syracuseStep 257675 = 386513) B386513
theorem B290443 : Blo 255820 290443 := bstep (se 1 (by rfl) ⟨217832, by rfl⟩ : syracuseStep 290443 = 435665) B435665
theorem B487063 : Blo 255820 487063 := bstep (se 1 (by rfl) ⟨365297, by rfl⟩ : syracuseStep 487063 = 730595) B730595
theorem B257687 : Blo 255820 257687 := bstep (se 1 (by rfl) ⟨193265, by rfl⟩ : syracuseStep 257687 = 386531) B386531
theorem B257707 : Blo 255820 257707 := bstep (se 1 (by rfl) ⟨193280, by rfl⟩ : syracuseStep 257707 = 386561) B386561
theorem B1994419 : Blo 255820 1994419 := bstep (se 1 (by rfl) ⟨1495814, by rfl⟩ : syracuseStep 1994419 = 2991629) B2991629
theorem B257719 : Blo 255820 257719 := bstep (se 1 (by rfl) ⟨193289, by rfl⟩ : syracuseStep 257719 = 386579) B386579
theorem B257739 : Blo 255820 257739 := bstep (se 1 (by rfl) ⟨193304, by rfl⟩ : syracuseStep 257739 = 386609) B386609
theorem B388811 : Blo 255820 388811 := bstep (se 1 (by rfl) ⟨291608, by rfl⟩ : syracuseStep 388811 = 583217) B583217
theorem B257751 : Blo 255820 257751 := bstep (se 1 (by rfl) ⟨193313, by rfl⟩ : syracuseStep 257751 = 386627) B386627
theorem B388823 : Blo 255820 388823 := bstep (se 1 (by rfl) ⟨291617, by rfl⟩ : syracuseStep 388823 = 583235) B583235
theorem B257771 : Blo 255820 257771 := bstep (se 1 (by rfl) ⟨193328, by rfl⟩ : syracuseStep 257771 = 386657) B386657
theorem B257783 : Blo 255820 257783 := bstep (se 1 (by rfl) ⟨193337, by rfl⟩ : syracuseStep 257783 = 386675) B386675
theorem B290551 : Blo 255820 290551 := bstep (se 1 (by rfl) ⟨217913, by rfl⟩ : syracuseStep 290551 = 435827) B435827
theorem B257803 : Blo 255820 257803 := bstep (se 1 (by rfl) ⟨193352, by rfl⟩ : syracuseStep 257803 = 386705) B386705
theorem B257815 : Blo 255820 257815 := bstep (se 1 (by rfl) ⟨193361, by rfl⟩ : syracuseStep 257815 = 386723) B386723
theorem B388889 : Blo 255820 388889 := bstep (se 2 (by rfl) ⟨145833, by rfl⟩ : syracuseStep 388889 = 291667) B291667
theorem B257835 : Blo 255820 257835 := bstep (se 1 (by rfl) ⟨193376, by rfl⟩ : syracuseStep 257835 = 386753) B386753
theorem B3534637 : Blo 255820 3534637 := bstep (se 3 (by rfl) ⟨662744, by rfl⟩ : syracuseStep 3534637 = 1325489) B1325489
theorem B257847 : Blo 255820 257847 := bstep (se 1 (by rfl) ⟨193385, by rfl⟩ : syracuseStep 257847 = 386771) B386771
theorem B257867 : Blo 255820 257867 := bstep (se 1 (by rfl) ⟨193400, by rfl⟩ : syracuseStep 257867 = 386801) B386801
theorem B749387 : Blo 255820 749387 := bstep (se 1 (by rfl) ⟨562040, by rfl⟩ : syracuseStep 749387 = 1124081) B1124081
theorem B257879 : Blo 255820 257879 := bstep (se 1 (by rfl) ⟨193409, by rfl⟩ : syracuseStep 257879 = 386819) B386819
theorem B257899 : Blo 255820 257899 := bstep (se 1 (by rfl) ⟨193424, by rfl⟩ : syracuseStep 257899 = 386849) B386849
theorem B257911 : Blo 255820 257911 := bstep (se 1 (by rfl) ⟨193433, by rfl⟩ : syracuseStep 257911 = 386867) B386867
theorem B552833 : Blo 255820 552833 := bstep (se 2 (by rfl) ⟨207312, by rfl⟩ : syracuseStep 552833 = 414625) B414625
theorem B257931 : Blo 255820 257931 := bstep (se 1 (by rfl) ⟨193448, by rfl⟩ : syracuseStep 257931 = 386897) B386897
theorem B389003 : Blo 255820 389003 := bstep (se 1 (by rfl) ⟨291752, by rfl⟩ : syracuseStep 389003 = 583505) B583505
theorem B257943 : Blo 255820 257943 := bstep (se 1 (by rfl) ⟨193457, by rfl⟩ : syracuseStep 257943 = 386915) B386915
theorem B389015 : Blo 255820 389015 := bstep (se 1 (by rfl) ⟨291761, by rfl⟩ : syracuseStep 389015 = 583523) B583523
theorem B257963 : Blo 255820 257963 := bstep (se 1 (by rfl) ⟨193472, by rfl⟩ : syracuseStep 257963 = 386945) B386945
theorem B290731 : Blo 255820 290731 := bstep (se 1 (by rfl) ⟨218048, by rfl⟩ : syracuseStep 290731 = 436097) B436097
theorem B257975 : Blo 255820 257975 := bstep (se 1 (by rfl) ⟨193481, by rfl⟩ : syracuseStep 257975 = 386963) B386963
theorem B257995 : Blo 255820 257995 := bstep (se 1 (by rfl) ⟨193496, by rfl⟩ : syracuseStep 257995 = 386993) B386993
theorem B258007 : Blo 255820 258007 := bstep (se 1 (by rfl) ⟨193505, by rfl⟩ : syracuseStep 258007 = 387011) B387011
theorem B552919 : Blo 255820 552919 := bstep (se 1 (by rfl) ⟨414689, by rfl⟩ : syracuseStep 552919 = 829379) B829379
theorem B389081 : Blo 255820 389081 := bstep (se 2 (by rfl) ⟨145905, by rfl⟩ : syracuseStep 389081 = 291811) B291811
theorem B258027 : Blo 255820 258027 := bstep (se 1 (by rfl) ⟨193520, by rfl⟩ : syracuseStep 258027 = 387041) B387041
theorem B258039 : Blo 255820 258039 := bstep (se 1 (by rfl) ⟨193529, by rfl⟩ : syracuseStep 258039 = 387059) B387059
theorem B258059 : Blo 255820 258059 := bstep (se 1 (by rfl) ⟨193544, by rfl⟩ : syracuseStep 258059 = 387089) B387089
theorem B258071 : Blo 255820 258071 := bstep (se 1 (by rfl) ⟨193553, by rfl⟩ : syracuseStep 258071 = 387107) B387107
theorem B290839 : Blo 255820 290839 := bstep (se 1 (by rfl) ⟨218129, by rfl⟩ : syracuseStep 290839 = 436259) B436259
theorem B258091 : Blo 255820 258091 := bstep (se 1 (by rfl) ⟨193568, by rfl⟩ : syracuseStep 258091 = 387137) B387137
theorem B258103 : Blo 255820 258103 := bstep (se 1 (by rfl) ⟨193577, by rfl⟩ : syracuseStep 258103 = 387155) B387155
theorem B258123 : Blo 255820 258123 := bstep (se 1 (by rfl) ⟨193592, by rfl⟩ : syracuseStep 258123 = 387185) B387185
theorem B389195 : Blo 255820 389195 := bstep (se 1 (by rfl) ⟨291896, by rfl⟩ : syracuseStep 389195 = 583793) B583793
theorem B258135 : Blo 255820 258135 := bstep (se 1 (by rfl) ⟨193601, by rfl⟩ : syracuseStep 258135 = 387203) B387203
theorem B389207 : Blo 255820 389207 := bstep (se 1 (by rfl) ⟨291905, by rfl⟩ : syracuseStep 389207 = 583811) B583811
theorem B258155 : Blo 255820 258155 := bstep (se 1 (by rfl) ⟨193616, by rfl⟩ : syracuseStep 258155 = 387233) B387233
theorem B258167 : Blo 255820 258167 := bstep (se 1 (by rfl) ⟨193625, by rfl⟩ : syracuseStep 258167 = 387251) B387251
theorem B258187 : Blo 255820 258187 := bstep (se 1 (by rfl) ⟨193640, by rfl⟩ : syracuseStep 258187 = 387281) B387281
theorem B258199 : Blo 255820 258199 := bstep (se 1 (by rfl) ⟨193649, by rfl⟩ : syracuseStep 258199 = 387299) B387299
theorem B389273 : Blo 255820 389273 := bstep (se 2 (by rfl) ⟨145977, by rfl⟩ : syracuseStep 389273 = 291955) B291955
theorem B258219 : Blo 255820 258219 := bstep (se 1 (by rfl) ⟨193664, by rfl⟩ : syracuseStep 258219 = 387329) B387329
theorem B258231 : Blo 255820 258231 := bstep (se 1 (by rfl) ⟨193673, by rfl⟩ : syracuseStep 258231 = 387347) B387347
theorem B258251 : Blo 255820 258251 := bstep (se 1 (by rfl) ⟨193688, by rfl⟩ : syracuseStep 258251 = 387377) B387377
theorem B291019 : Blo 255820 291019 := bstep (se 1 (by rfl) ⟨218264, by rfl⟩ : syracuseStep 291019 = 436529) B436529
theorem B258263 : Blo 255820 258263 := bstep (se 1 (by rfl) ⟨193697, by rfl⟩ : syracuseStep 258263 = 387395) B387395
theorem B258283 : Blo 255820 258283 := bstep (se 1 (by rfl) ⟨193712, by rfl⟩ : syracuseStep 258283 = 387425) B387425
theorem B258295 : Blo 255820 258295 := bstep (se 1 (by rfl) ⟨193721, by rfl⟩ : syracuseStep 258295 = 387443) B387443
theorem B258315 : Blo 255820 258315 := bstep (se 1 (by rfl) ⟨193736, by rfl⟩ : syracuseStep 258315 = 387473) B387473
theorem B389387 : Blo 255820 389387 := bstep (se 1 (by rfl) ⟨292040, by rfl⟩ : syracuseStep 389387 = 584081) B584081
theorem B258327 : Blo 255820 258327 := bstep (se 1 (by rfl) ⟨193745, by rfl⟩ : syracuseStep 258327 = 387491) B387491
theorem B389399 : Blo 255820 389399 := bstep (se 1 (by rfl) ⟨292049, by rfl⟩ : syracuseStep 389399 = 584099) B584099
theorem B258347 : Blo 255820 258347 := bstep (se 1 (by rfl) ⟨193760, by rfl⟩ : syracuseStep 258347 = 387521) B387521
theorem B258359 : Blo 255820 258359 := bstep (se 1 (by rfl) ⟨193769, by rfl⟩ : syracuseStep 258359 = 387539) B387539
theorem B291127 : Blo 255820 291127 := bstep (se 1 (by rfl) ⟨218345, by rfl⟩ : syracuseStep 291127 = 436691) B436691
theorem B258379 : Blo 255820 258379 := bstep (se 1 (by rfl) ⟨193784, by rfl⟩ : syracuseStep 258379 = 387569) B387569
theorem B258391 : Blo 255820 258391 := bstep (se 1 (by rfl) ⟨193793, by rfl⟩ : syracuseStep 258391 = 387587) B387587
theorem B389465 : Blo 255820 389465 := bstep (se 2 (by rfl) ⟨146049, by rfl⟩ : syracuseStep 389465 = 292099) B292099
theorem B258411 : Blo 255820 258411 := bstep (se 1 (by rfl) ⟨193808, by rfl⟩ : syracuseStep 258411 = 387617) B387617
theorem B258423 : Blo 255820 258423 := bstep (se 1 (by rfl) ⟨193817, by rfl⟩ : syracuseStep 258423 = 387635) B387635
theorem B258443 : Blo 255820 258443 := bstep (se 1 (by rfl) ⟨193832, by rfl⟩ : syracuseStep 258443 = 387665) B387665
theorem B258455 : Blo 255820 258455 := bstep (se 1 (by rfl) ⟨193841, by rfl⟩ : syracuseStep 258455 = 387683) B387683
theorem B258475 : Blo 255820 258475 := bstep (se 1 (by rfl) ⟨193856, by rfl⟩ : syracuseStep 258475 = 387713) B387713
theorem B258487 : Blo 255820 258487 := bstep (se 1 (by rfl) ⟨193865, by rfl⟩ : syracuseStep 258487 = 387731) B387731
theorem B487883 : Blo 255820 487883 := bstep (se 1 (by rfl) ⟨365912, by rfl⟩ : syracuseStep 487883 = 731825) B731825
theorem B258507 : Blo 255820 258507 := bstep (se 1 (by rfl) ⟨193880, by rfl⟩ : syracuseStep 258507 = 387761) B387761
theorem B389579 : Blo 255820 389579 := bstep (se 1 (by rfl) ⟨292184, by rfl⟩ : syracuseStep 389579 = 584369) B584369
theorem B258519 : Blo 255820 258519 := bstep (se 1 (by rfl) ⟨193889, by rfl⟩ : syracuseStep 258519 = 387779) B387779
theorem B389591 : Blo 255820 389591 := bstep (se 1 (by rfl) ⟨292193, by rfl⟩ : syracuseStep 389591 = 584387) B584387
theorem B258539 : Blo 255820 258539 := bstep (se 1 (by rfl) ⟨193904, by rfl⟩ : syracuseStep 258539 = 387809) B387809
theorem B291307 : Blo 255820 291307 := bstep (se 1 (by rfl) ⟨218480, by rfl⟩ : syracuseStep 291307 = 436961) B436961
theorem B258551 : Blo 255820 258551 := bstep (se 1 (by rfl) ⟨193913, by rfl⟩ : syracuseStep 258551 = 387827) B387827
theorem B487937 : Blo 255820 487937 := bstep (se 2 (by rfl) ⟨182976, by rfl⟩ : syracuseStep 487937 = 365953) B365953
theorem B258571 : Blo 255820 258571 := bstep (se 1 (by rfl) ⟨193928, by rfl⟩ : syracuseStep 258571 = 387857) B387857
theorem B258583 : Blo 255820 258583 := bstep (se 1 (by rfl) ⟨193937, by rfl⟩ : syracuseStep 258583 = 387875) B387875
theorem B389657 : Blo 255820 389657 := bstep (se 2 (by rfl) ⟨146121, by rfl⟩ : syracuseStep 389657 = 292243) B292243
theorem B258603 : Blo 255820 258603 := bstep (se 1 (by rfl) ⟨193952, by rfl⟩ : syracuseStep 258603 = 387905) B387905
theorem B651827 : Blo 255820 651827 := bstep (se 1 (by rfl) ⟨488870, by rfl⟩ : syracuseStep 651827 = 977741) B977741
theorem B258615 : Blo 255820 258615 := bstep (se 1 (by rfl) ⟨193961, by rfl⟩ : syracuseStep 258615 = 387923) B387923
theorem B258635 : Blo 255820 258635 := bstep (se 1 (by rfl) ⟨193976, by rfl⟩ : syracuseStep 258635 = 387953) B387953
theorem B258647 : Blo 255820 258647 := bstep (se 1 (by rfl) ⟨193985, by rfl⟩ : syracuseStep 258647 = 387971) B387971
theorem B291415 : Blo 255820 291415 := bstep (se 1 (by rfl) ⟨218561, by rfl⟩ : syracuseStep 291415 = 437123) B437123
theorem B258667 : Blo 255820 258667 := bstep (se 1 (by rfl) ⟨194000, by rfl⟩ : syracuseStep 258667 = 388001) B388001
theorem B258679 : Blo 255820 258679 := bstep (se 1 (by rfl) ⟨194009, by rfl⟩ : syracuseStep 258679 = 388019) B388019
theorem B258699 : Blo 255820 258699 := bstep (se 1 (by rfl) ⟨194024, by rfl⟩ : syracuseStep 258699 = 388049) B388049
theorem B258711 : Blo 255820 258711 := bstep (se 1 (by rfl) ⟨194033, by rfl⟩ : syracuseStep 258711 = 388067) B388067
theorem B258731 : Blo 255820 258731 := bstep (se 1 (by rfl) ⟨194048, by rfl⟩ : syracuseStep 258731 = 388097) B388097
theorem B258743 : Blo 255820 258743 := bstep (se 1 (by rfl) ⟨194057, by rfl⟩ : syracuseStep 258743 = 388115) B388115
theorem B586433 : Blo 255820 586433 := bstep (se 2 (by rfl) ⟨219912, by rfl⟩ : syracuseStep 586433 = 439825) B439825
theorem B258763 : Blo 255820 258763 := bstep (se 1 (by rfl) ⟨194072, by rfl⟩ : syracuseStep 258763 = 388145) B388145
theorem B258775 : Blo 255820 258775 := bstep (se 1 (by rfl) ⟨194081, by rfl⟩ : syracuseStep 258775 = 388163) B388163
theorem B258795 : Blo 255820 258795 := bstep (se 1 (by rfl) ⟨194096, by rfl⟩ : syracuseStep 258795 = 388193) B388193
theorem B258807 : Blo 255820 258807 := bstep (se 1 (by rfl) ⟨194105, by rfl⟩ : syracuseStep 258807 = 388211) B388211
theorem B979715 : Blo 255820 979715 := bstep (se 1 (by rfl) ⟨734786, by rfl⟩ : syracuseStep 979715 = 1469573) B1469573
theorem B258827 : Blo 255820 258827 := bstep (se 1 (by rfl) ⟨194120, by rfl⟩ : syracuseStep 258827 = 388241) B388241
theorem B291595 : Blo 255820 291595 := bstep (se 1 (by rfl) ⟨218696, by rfl⟩ : syracuseStep 291595 = 437393) B437393
theorem B258839 : Blo 255820 258839 := bstep (se 1 (by rfl) ⟨194129, by rfl⟩ : syracuseStep 258839 = 388259) B388259
theorem B258859 : Blo 255820 258859 := bstep (se 1 (by rfl) ⟨194144, by rfl⟩ : syracuseStep 258859 = 388289) B388289
theorem B258871 : Blo 255820 258871 := bstep (se 1 (by rfl) ⟨194153, by rfl⟩ : syracuseStep 258871 = 388307) B388307
theorem B258891 : Blo 255820 258891 := bstep (se 1 (by rfl) ⟨194168, by rfl⟩ : syracuseStep 258891 = 388337) B388337
theorem B258903 : Blo 255820 258903 := bstep (se 1 (by rfl) ⟨194177, by rfl⟩ : syracuseStep 258903 = 388355) B388355
theorem B652121 : Blo 255820 652121 := bstep (se 2 (by rfl) ⟨244545, by rfl⟩ : syracuseStep 652121 = 489091) B489091
theorem B258923 : Blo 255820 258923 := bstep (se 1 (by rfl) ⟨194192, by rfl⟩ : syracuseStep 258923 = 388385) B388385
theorem B258935 : Blo 255820 258935 := bstep (se 1 (by rfl) ⟨194201, by rfl⟩ : syracuseStep 258935 = 388403) B388403
theorem B291703 : Blo 255820 291703 := bstep (se 1 (by rfl) ⟨218777, by rfl⟩ : syracuseStep 291703 = 437555) B437555
theorem B258955 : Blo 255820 258955 := bstep (se 1 (by rfl) ⟨194216, by rfl⟩ : syracuseStep 258955 = 388433) B388433
theorem B258967 : Blo 255820 258967 := bstep (se 1 (by rfl) ⟨194225, by rfl⟩ : syracuseStep 258967 = 388451) B388451
theorem B258987 : Blo 255820 258987 := bstep (se 1 (by rfl) ⟨194240, by rfl⟩ : syracuseStep 258987 = 388481) B388481
theorem B258999 : Blo 255820 258999 := bstep (se 1 (by rfl) ⟨194249, by rfl⟩ : syracuseStep 258999 = 388499) B388499
theorem B259019 : Blo 255820 259019 := bstep (se 1 (by rfl) ⟨194264, by rfl⟩ : syracuseStep 259019 = 388529) B388529
theorem B259031 : Blo 255820 259031 := bstep (se 1 (by rfl) ⟨194273, by rfl⟩ : syracuseStep 259031 = 388547) B388547
theorem B259051 : Blo 255820 259051 := bstep (se 1 (by rfl) ⟨194288, by rfl⟩ : syracuseStep 259051 = 388577) B388577
theorem B259063 : Blo 255820 259063 := bstep (se 1 (by rfl) ⟨194297, by rfl⟩ : syracuseStep 259063 = 388595) B388595
theorem B259083 : Blo 255820 259083 := bstep (se 1 (by rfl) ⟨194312, by rfl⟩ : syracuseStep 259083 = 388625) B388625
theorem B259095 : Blo 255820 259095 := bstep (se 1 (by rfl) ⟨194321, by rfl⟩ : syracuseStep 259095 = 388643) B388643
theorem B259115 : Blo 255820 259115 := bstep (se 1 (by rfl) ⟨194336, by rfl⟩ : syracuseStep 259115 = 388673) B388673
theorem B291883 : Blo 255820 291883 := bstep (se 1 (by rfl) ⟨218912, by rfl⟩ : syracuseStep 291883 = 437825) B437825
theorem B259127 : Blo 255820 259127 := bstep (se 1 (by rfl) ⟨194345, by rfl⟩ : syracuseStep 259127 = 388691) B388691
theorem B259147 : Blo 255820 259147 := bstep (se 1 (by rfl) ⟨194360, by rfl⟩ : syracuseStep 259147 = 388721) B388721
theorem B259159 : Blo 255820 259159 := bstep (se 1 (by rfl) ⟨194369, by rfl⟩ : syracuseStep 259159 = 388739) B388739
theorem B259179 : Blo 255820 259179 := bstep (se 1 (by rfl) ⟨194384, by rfl⟩ : syracuseStep 259179 = 388769) B388769
theorem B259191 : Blo 255820 259191 := bstep (se 1 (by rfl) ⟨194393, by rfl⟩ : syracuseStep 259191 = 388787) B388787
theorem B259211 : Blo 255820 259211 := bstep (se 1 (by rfl) ⟨194408, by rfl⟩ : syracuseStep 259211 = 388817) B388817
theorem B259223 : Blo 255820 259223 := bstep (se 1 (by rfl) ⟨194417, by rfl⟩ : syracuseStep 259223 = 388835) B388835
theorem B291991 : Blo 255820 291991 := bstep (se 1 (by rfl) ⟨218993, by rfl⟩ : syracuseStep 291991 = 437987) B437987
theorem B259243 : Blo 255820 259243 := bstep (se 1 (by rfl) ⟨194432, by rfl⟩ : syracuseStep 259243 = 388865) B388865
theorem B259255 : Blo 255820 259255 := bstep (se 1 (by rfl) ⟨194441, by rfl⟩ : syracuseStep 259255 = 388883) B388883
theorem B881867 : Blo 255820 881867 := bstep (se 1 (by rfl) ⟨661400, by rfl⟩ : syracuseStep 881867 = 1322801) B1322801
theorem B980171 : Blo 255820 980171 := bstep (se 1 (by rfl) ⟨735128, by rfl⟩ : syracuseStep 980171 = 1470257) B1470257
theorem B259275 : Blo 255820 259275 := bstep (se 1 (by rfl) ⟨194456, by rfl⟩ : syracuseStep 259275 = 388913) B388913
theorem B259287 : Blo 255820 259287 := bstep (se 1 (by rfl) ⟨194465, by rfl⟩ : syracuseStep 259287 = 388931) B388931
theorem B259307 : Blo 255820 259307 := bstep (se 1 (by rfl) ⟨194480, by rfl⟩ : syracuseStep 259307 = 388961) B388961
theorem B259319 : Blo 255820 259319 := bstep (se 1 (by rfl) ⟨194489, by rfl⟩ : syracuseStep 259319 = 388979) B388979
theorem B259339 : Blo 255820 259339 := bstep (se 1 (by rfl) ⟨194504, by rfl⟩ : syracuseStep 259339 = 389009) B389009
theorem B259351 : Blo 255820 259351 := bstep (se 1 (by rfl) ⟨194513, by rfl⟩ : syracuseStep 259351 = 389027) B389027
theorem B259371 : Blo 255820 259371 := bstep (se 1 (by rfl) ⟨194528, by rfl⟩ : syracuseStep 259371 = 389057) B389057
theorem B259383 : Blo 255820 259383 := bstep (se 1 (by rfl) ⟨194537, by rfl⟩ : syracuseStep 259383 = 389075) B389075
theorem B259403 : Blo 255820 259403 := bstep (se 1 (by rfl) ⟨194552, by rfl⟩ : syracuseStep 259403 = 389105) B389105
theorem B292171 : Blo 255820 292171 := bstep (se 1 (by rfl) ⟨219128, by rfl⟩ : syracuseStep 292171 = 438257) B438257
theorem B259415 : Blo 255820 259415 := bstep (se 1 (by rfl) ⟨194561, by rfl⟩ : syracuseStep 259415 = 389123) B389123
theorem B2192741 : Blo 255820 2192741 := bstep (se 4 (by rfl) ⟨205569, by rfl⟩ : syracuseStep 2192741 = 411139) B411139
theorem B259435 : Blo 255820 259435 := bstep (se 1 (by rfl) ⟨194576, by rfl⟩ : syracuseStep 259435 = 389153) B389153
theorem B259447 : Blo 255820 259447 := bstep (se 1 (by rfl) ⟨194585, by rfl⟩ : syracuseStep 259447 = 389171) B389171
theorem B259467 : Blo 255820 259467 := bstep (se 1 (by rfl) ⟨194600, by rfl⟩ : syracuseStep 259467 = 389201) B389201
theorem B980369 : Blo 255820 980369 := bstep (se 2 (by rfl) ⟨367638, by rfl⟩ : syracuseStep 980369 = 735277) B735277
theorem B488855 : Blo 255820 488855 := bstep (se 1 (by rfl) ⟨366641, by rfl⟩ : syracuseStep 488855 = 733283) B733283
theorem B259479 : Blo 255820 259479 := bstep (se 1 (by rfl) ⟨194609, by rfl⟩ : syracuseStep 259479 = 389219) B389219
theorem B259499 : Blo 255820 259499 := bstep (se 1 (by rfl) ⟨194624, by rfl⟩ : syracuseStep 259499 = 389249) B389249
theorem B259511 : Blo 255820 259511 := bstep (se 1 (by rfl) ⟨194633, by rfl⟩ : syracuseStep 259511 = 389267) B389267
theorem B292279 : Blo 255820 292279 := bstep (se 1 (by rfl) ⟨219209, by rfl⟩ : syracuseStep 292279 = 438419) B438419
theorem B259531 : Blo 255820 259531 := bstep (se 1 (by rfl) ⟨194648, by rfl⟩ : syracuseStep 259531 = 389297) B389297
theorem B259543 : Blo 255820 259543 := bstep (se 1 (by rfl) ⟨194657, by rfl⟩ : syracuseStep 259543 = 389315) B389315
theorem B259563 : Blo 255820 259563 := bstep (se 1 (by rfl) ⟨194672, by rfl⟩ : syracuseStep 259563 = 389345) B389345
theorem B259575 : Blo 255820 259575 := bstep (se 1 (by rfl) ⟨194681, by rfl⟩ : syracuseStep 259575 = 389363) B389363
theorem B259595 : Blo 255820 259595 := bstep (se 1 (by rfl) ⟨194696, by rfl⟩ : syracuseStep 259595 = 389393) B389393
theorem B259607 : Blo 255820 259607 := bstep (se 1 (by rfl) ⟨194705, by rfl⟩ : syracuseStep 259607 = 389411) B389411
theorem B259627 : Blo 255820 259627 := bstep (se 1 (by rfl) ⟨194720, by rfl⟩ : syracuseStep 259627 = 389441) B389441
theorem B620083 : Blo 255820 620083 := bstep (se 1 (by rfl) ⟨465062, by rfl⟩ : syracuseStep 620083 = 930125) B930125
theorem B259639 : Blo 255820 259639 := bstep (se 1 (by rfl) ⟨194729, by rfl⟩ : syracuseStep 259639 = 389459) B389459
theorem B259659 : Blo 255820 259659 := bstep (se 1 (by rfl) ⟨194744, by rfl⟩ : syracuseStep 259659 = 389489) B389489
theorem B259671 : Blo 255820 259671 := bstep (se 1 (by rfl) ⟨194753, by rfl⟩ : syracuseStep 259671 = 389507) B389507
theorem B259691 : Blo 255820 259691 := bstep (se 1 (by rfl) ⟨194768, by rfl⟩ : syracuseStep 259691 = 389537) B389537
theorem B259703 : Blo 255820 259703 := bstep (se 1 (by rfl) ⟨194777, by rfl⟩ : syracuseStep 259703 = 389555) B389555
theorem B259723 : Blo 255820 259723 := bstep (se 1 (by rfl) ⟨194792, by rfl⟩ : syracuseStep 259723 = 389585) B389585
theorem B1308311 : Blo 255820 1308311 := bstep (se 1 (by rfl) ⟨981233, by rfl⟩ : syracuseStep 1308311 = 1962467) B1962467
theorem B259735 : Blo 255820 259735 := bstep (se 1 (by rfl) ⟨194801, by rfl⟩ : syracuseStep 259735 = 389603) B389603
theorem B259755 : Blo 255820 259755 := bstep (se 1 (by rfl) ⟨194816, by rfl⟩ : syracuseStep 259755 = 389633) B389633
theorem B259767 : Blo 255820 259767 := bstep (se 1 (by rfl) ⟨194825, by rfl⟩ : syracuseStep 259767 = 389651) B389651
theorem B259787 : Blo 255820 259787 := bstep (se 1 (by rfl) ⟨194840, by rfl⟩ : syracuseStep 259787 = 389681) B389681
theorem B259799 : Blo 255820 259799 := bstep (se 1 (by rfl) ⟨194849, by rfl⟩ : syracuseStep 259799 = 389699) B389699
theorem B259819 : Blo 255820 259819 := bstep (se 1 (by rfl) ⟨194864, by rfl⟩ : syracuseStep 259819 = 389729) B389729
theorem B325387 : Blo 255820 325387 := bstep (se 1 (by rfl) ⟨244040, by rfl⟩ : syracuseStep 325387 = 488081) B488081
theorem B1767233 : Blo 255820 1767233 := bstep (se 2 (by rfl) ⟨662712, by rfl⟩ : syracuseStep 1767233 = 1325425) B1325425
theorem B489395 : Blo 255820 489395 := bstep (se 1 (by rfl) ⟨367046, by rfl⟩ : syracuseStep 489395 = 734093) B734093
theorem B292843 : Blo 255820 292843 := bstep (se 1 (by rfl) ⟨219632, by rfl⟩ : syracuseStep 292843 = 439265) B439265
theorem B2193425 : Blo 255820 2193425 := bstep (se 2 (by rfl) ⟨822534, by rfl⟩ : syracuseStep 2193425 = 1645069) B1645069
theorem B260183 : Blo 255820 260183 := bstep (se 1 (by rfl) ⟨195137, by rfl⟩ : syracuseStep 260183 = 390275) B390275
theorem B981143 : Blo 255820 981143 := bstep (se 1 (by rfl) ⟨735857, by rfl⟩ : syracuseStep 981143 = 1471715) B1471715
theorem B522443 : Blo 255820 522443 := bstep (se 1 (by rfl) ⟨391832, by rfl⟩ : syracuseStep 522443 = 783665) B783665
theorem B620747 : Blo 255820 620747 := bstep (se 1 (by rfl) ⟨465560, by rfl⟩ : syracuseStep 620747 = 931121) B931121
theorem B981341 : Blo 255820 981341 := bstep (se 3 (by rfl) ⟨184001, by rfl⟩ : syracuseStep 981341 = 368003) B368003
theorem B489881 : Blo 255820 489881 := bstep (se 2 (by rfl) ⟨183705, by rfl⟩ : syracuseStep 489881 = 367411) B367411
theorem B653771 : Blo 255820 653771 := bstep (se 1 (by rfl) ⟨490328, by rfl⟩ : syracuseStep 653771 = 980657) B980657
theorem B391819 : Blo 255820 391819 := bstep (se 1 (by rfl) ⟨293864, by rfl⟩ : syracuseStep 391819 = 587729) B587729
theorem B326359 : Blo 255820 326359 := bstep (se 1 (by rfl) ⟨244769, by rfl⟩ : syracuseStep 326359 = 489539) B489539
theorem B293719 : Blo 255820 293719 := bstep (se 1 (by rfl) ⟨220289, by rfl⟩ : syracuseStep 293719 = 440579) B440579
theorem B621515 : Blo 255820 621515 := bstep (se 1 (by rfl) ⟨466136, by rfl⟩ : syracuseStep 621515 = 932273) B932273
theorem B3112067 : Blo 255820 3112067 := bstep (se 1 (by rfl) ⟨2334050, by rfl⟩ : syracuseStep 3112067 = 4668101) B4668101
theorem B3734849 : Blo 255820 3734849 := bstep (se 2 (by rfl) ⟨1400568, by rfl⟩ : syracuseStep 3734849 = 2801137) B2801137
theorem B654743 : Blo 255820 654743 := bstep (se 1 (by rfl) ⟨491057, by rfl⟩ : syracuseStep 654743 = 982115) B982115
theorem B327179 : Blo 255820 327179 := bstep (se 1 (by rfl) ⟨245384, by rfl⟩ : syracuseStep 327179 = 490769) B490769
theorem B1474199 : Blo 255820 1474199 := bstep (se 1 (by rfl) ⟨1105649, by rfl⟩ : syracuseStep 1474199 = 2211299) B2211299
theorem B1965869 : Blo 255820 1965869 := bstep (se 3 (by rfl) ⟨368600, by rfl⟩ : syracuseStep 1965869 = 737201) B737201
theorem B491339 : Blo 255820 491339 := bstep (se 1 (by rfl) ⟨368504, by rfl⟩ : syracuseStep 491339 = 737009) B737009
theorem B655361 : Blo 255820 655361 := bstep (se 2 (by rfl) ⟨245760, by rfl⟩ : syracuseStep 655361 = 491521) B491521
theorem B262279 : Blo 255820 262279 := bstep (se 1 (by rfl) ⟨196709, by rfl⟩ : syracuseStep 262279 = 393419) B393419
theorem B524435 : Blo 255820 524435 := bstep (se 1 (by rfl) ⟨393326, by rfl⟩ : syracuseStep 524435 = 786653) B786653
theorem B622745 : Blo 255820 622745 := bstep (se 2 (by rfl) ⟨233529, by rfl⟩ : syracuseStep 622745 = 467059) B467059
theorem B327979 : Blo 255820 327979 := bstep (se 1 (by rfl) ⟨245984, by rfl⟩ : syracuseStep 327979 = 491969) B491969
theorem B1311065 : Blo 255820 1311065 := bstep (se 2 (by rfl) ⟨491649, by rfl⟩ : syracuseStep 1311065 = 983299) B983299
theorem B655735 : Blo 255820 655735 := bstep (se 1 (by rfl) ⟨491801, by rfl⟩ : syracuseStep 655735 = 983603) B983603
theorem B1868177 : Blo 255820 1868177 := bstep (se 2 (by rfl) ⟨700566, by rfl⟩ : syracuseStep 1868177 = 1401133) B1401133
theorem B491923 : Blo 255820 491923 := bstep (se 1 (by rfl) ⟨368942, by rfl⟩ : syracuseStep 491923 = 737885) B737885
theorem B328207 : Blo 255820 328207 := bstep (se 1 (by rfl) ⟨246155, by rfl⟩ : syracuseStep 328207 = 492311) B492311
theorem B1245719 : Blo 255820 1245719 := bstep (se 1 (by rfl) ⟨934289, by rfl⟩ : syracuseStep 1245719 = 1868579) B1868579
theorem B492151 : Blo 255820 492151 := bstep (se 1 (by rfl) ⟨369113, by rfl⟩ : syracuseStep 492151 = 738227) B738227
theorem B1606337 : Blo 255820 1606337 := bstep (se 2 (by rfl) ⟨602376, by rfl⟩ : syracuseStep 1606337 = 1204753) B1204753
theorem B4162265 : Blo 255820 4162265 := bstep (se 2 (by rfl) ⟨1560849, by rfl⟩ : syracuseStep 4162265 = 3121699) B3121699
theorem B656171 : Blo 255820 656171 := bstep (se 1 (by rfl) ⟨492128, by rfl⟩ : syracuseStep 656171 = 984257) B984257
theorem B2097971 : Blo 255820 2097971 := bstep (se 1 (by rfl) ⟨1573478, by rfl⟩ : syracuseStep 2097971 = 3146957) B3146957
theorem B1246067 : Blo 255820 1246067 := bstep (se 1 (by rfl) ⟨934550, by rfl⟩ : syracuseStep 1246067 = 1869101) B1869101
theorem B820115 : Blo 255820 820115 := bstep (se 1 (by rfl) ⟨615086, by rfl⟩ : syracuseStep 820115 = 1230173) B1230173
theorem B6652853 : Blo 255820 6652853 := bstep (se 5 (by rfl) ⟨311852, by rfl⟩ : syracuseStep 6652853 = 623705) B623705
theorem B328951 : Blo 255820 328951 := bstep (se 1 (by rfl) ⟨246713, by rfl⟩ : syracuseStep 328951 = 493427) B493427
theorem B492833 : Blo 255820 492833 := bstep (se 2 (by rfl) ⟨184812, by rfl⟩ : syracuseStep 492833 = 369625) B369625
theorem B657011 : Blo 255820 657011 := bstep (se 1 (by rfl) ⟨492758, by rfl⟩ : syracuseStep 657011 = 985517) B985517
theorem B657031 : Blo 255820 657031 := bstep (se 1 (by rfl) ⟨492773, by rfl⟩ : syracuseStep 657031 = 985547) B985547
theorem B2361125 : Blo 255820 2361125 := bstep (se 4 (by rfl) ⟨221355, by rfl⟩ : syracuseStep 2361125 = 442711) B442711
theorem B2131865 : Blo 255820 2131865 := bstep (se 2 (by rfl) ⟨799449, by rfl⟩ : syracuseStep 2131865 = 1598899) B1598899
theorem B657305 : Blo 255820 657305 := bstep (se 2 (by rfl) ⟨246489, by rfl⟩ : syracuseStep 657305 = 492979) B492979
theorem B657467 : Blo 255820 657467 := bstep (se 1 (by rfl) ⟨493100, by rfl⟩ : syracuseStep 657467 = 986201) B986201
theorem B1771721 : Blo 255820 1771721 := bstep (se 2 (by rfl) ⟨664395, by rfl⟩ : syracuseStep 1771721 = 1328791) B1328791
theorem B657665 : Blo 255820 657665 := bstep (se 2 (by rfl) ⟨246624, by rfl⟩ : syracuseStep 657665 = 493249) B493249
theorem B330043 : Blo 255820 330043 := bstep (se 1 (by rfl) ⟨247532, by rfl⟩ : syracuseStep 330043 = 495065) B495065
theorem B1313171 : Blo 255820 1313171 := bstep (se 1 (by rfl) ⟨984878, by rfl⟩ : syracuseStep 1313171 = 1969757) B1969757
theorem B2918915 : Blo 255820 2918915 := bstep (se 1 (by rfl) ⟨2189186, by rfl⟩ : syracuseStep 2918915 = 4378373) B4378373
theorem B3705689 : Blo 255820 3705689 := bstep (se 2 (by rfl) ⟨1389633, by rfl⟩ : syracuseStep 3705689 = 2779267) B2779267
theorem B986003 : Blo 255820 986003 := bstep (se 1 (by rfl) ⟨739502, by rfl⟩ : syracuseStep 986003 = 1479005) B1479005
theorem B1248527 : Blo 255820 1248527 := bstep (se 1 (by rfl) ⟨936395, by rfl⟩ : syracuseStep 1248527 = 1872791) B1872791
theorem B462215 : Blo 255820 462215 := bstep (se 1 (by rfl) ⟨346661, by rfl⟩ : syracuseStep 462215 = 693323) B693323
theorem B364295 : Blo 255820 364295 := bstep (se 1 (by rfl) ⟨273221, by rfl⟩ : syracuseStep 364295 = 546443) B546443
theorem B1642355 : Blo 255820 1642355 := bstep (se 1 (by rfl) ⟨1231766, by rfl⟩ : syracuseStep 1642355 = 2463533) B2463533
theorem B2199575 : Blo 255820 2199575 := bstep (se 1 (by rfl) ⟨1649681, by rfl⟩ : syracuseStep 2199575 = 3299363) B3299363
theorem B364603 : Blo 255820 364603 := bstep (se 1 (by rfl) ⟨273452, by rfl⟩ : syracuseStep 364603 = 546905) B546905
theorem B528911 : Blo 255820 528911 := bstep (se 1 (by rfl) ⟨396683, by rfl⟩ : syracuseStep 528911 = 793367) B793367
theorem B1577495 : Blo 255820 1577495 := bstep (se 1 (by rfl) ⟨1183121, by rfl⟩ : syracuseStep 1577495 = 2366243) B2366243
theorem B627347 : Blo 255820 627347 := bstep (se 1 (by rfl) ⟨470510, by rfl⟩ : syracuseStep 627347 = 941021) B941021
theorem B2953907 : Blo 255820 2953907 := bstep (se 1 (by rfl) ⟨2215430, by rfl⟩ : syracuseStep 2953907 = 4430861) B4430861
theorem B693107 : Blo 255820 693107 := bstep (se 1 (by rfl) ⟨519830, by rfl⟩ : syracuseStep 693107 = 1039661) B1039661
theorem B2659225 : Blo 255820 2659225 := bstep (se 2 (by rfl) ⟨997209, by rfl⟩ : syracuseStep 2659225 = 1994419) B1994419
theorem B824381 : Blo 255820 824381 := bstep (se 3 (by rfl) ⟨154571, by rfl⟩ : syracuseStep 824381 = 309143) B309143
theorem B365753 : Blo 255820 365753 := bstep (se 2 (by rfl) ⟨137157, by rfl⟩ : syracuseStep 365753 = 274315) B274315
theorem B1316147 : Blo 255820 1316147 := bstep (se 1 (by rfl) ⟨987110, by rfl⟩ : syracuseStep 1316147 = 1974221) B1974221
theorem B1512857 : Blo 255820 1512857 := bstep (se 2 (by rfl) ⟨567321, by rfl⟩ : syracuseStep 1512857 = 1134643) B1134643
theorem B4724153 : Blo 255820 4724153 := bstep (se 2 (by rfl) ⟨1771557, by rfl⟩ : syracuseStep 4724153 = 3543115) B3543115
theorem B693821 : Blo 255820 693821 := bstep (se 3 (by rfl) ⟨130091, by rfl⟩ : syracuseStep 693821 = 260183) B260183
theorem B923393 : Blo 255820 923393 := bstep (se 2 (by rfl) ⟨346272, by rfl⟩ : syracuseStep 923393 = 692545) B692545
theorem B22484789 : Blo 255820 22484789 := bstep (se 5 (by rfl) ⟨1053974, by rfl⟩ : syracuseStep 22484789 = 2107949) B2107949
theorem B432263 : Blo 255820 432263 := bstep (se 1 (by rfl) ⟨324197, by rfl⟩ : syracuseStep 432263 = 648395) B648395
theorem B5970323 : Blo 255820 5970323 := bstep (se 1 (by rfl) ⟨4477742, by rfl⟩ : syracuseStep 5970323 = 8955485) B8955485
theorem B367291 : Blo 255820 367291 := bstep (se 1 (by rfl) ⟨275468, by rfl⟩ : syracuseStep 367291 = 550937) B550937
theorem B432911 : Blo 255820 432911 := bstep (se 1 (by rfl) ⟨324683, by rfl⟩ : syracuseStep 432911 = 649367) B649367
theorem B826379 : Blo 255820 826379 := bstep (se 1 (by rfl) ⟨619784, by rfl⟩ : syracuseStep 826379 = 1239569) B1239569
theorem B367735 : Blo 255820 367735 := bstep (se 1 (by rfl) ⟨275801, by rfl⟩ : syracuseStep 367735 = 551603) B551603
theorem B433451 : Blo 255820 433451 := bstep (se 1 (by rfl) ⟨325088, by rfl⟩ : syracuseStep 433451 = 650177) B650177
theorem B826777 : Blo 255820 826777 := bstep (se 2 (by rfl) ⟨310041, by rfl⟩ : syracuseStep 826777 = 620083) B620083
theorem B6233669 : Blo 255820 6233669 := bstep (se 4 (by rfl) ⟨584406, by rfl⟩ : syracuseStep 6233669 = 1168813) B1168813
theorem B4726349 : Blo 255820 4726349 := bstep (se 3 (by rfl) ⟨886190, by rfl⟩ : syracuseStep 4726349 = 1772381) B1772381
theorem B433849 : Blo 255820 433849 := bstep (se 2 (by rfl) ⟨162693, by rfl⟩ : syracuseStep 433849 = 325387) B325387
theorem B499591 : Blo 255820 499591 := bstep (se 1 (by rfl) ⟨374693, by rfl⟩ : syracuseStep 499591 = 749387) B749387
theorem B368555 : Blo 255820 368555 := bstep (se 1 (by rfl) ⟨276416, by rfl⟩ : syracuseStep 368555 = 552833) B552833
theorem B8298845 : Blo 255820 8298845 := bstep (se 3 (by rfl) ⟨1556033, by rfl⟩ : syracuseStep 8298845 = 3112067) B3112067
theorem B434551 : Blo 255820 434551 := bstep (se 1 (by rfl) ⟨325913, by rfl⟩ : syracuseStep 434551 = 651827) B651827
theorem B729479 : Blo 255820 729479 := bstep (se 1 (by rfl) ⟨547109, by rfl⟩ : syracuseStep 729479 = 1094219) B1094219
theorem B1646993 : Blo 255820 1646993 := bstep (se 2 (by rfl) ⟨617622, by rfl⟩ : syracuseStep 1646993 = 1235245) B1235245
theorem B434747 : Blo 255820 434747 := bstep (se 1 (by rfl) ⟨326060, by rfl⟩ : syracuseStep 434747 = 652121) B652121
theorem B729661 : Blo 255820 729661 := bstep (se 3 (by rfl) ⟨136811, by rfl⟩ : syracuseStep 729661 = 273623) B273623
theorem B926275 : Blo 255820 926275 := bstep (se 1 (by rfl) ⟨694706, by rfl⟩ : syracuseStep 926275 = 1389413) B1389413
theorem B729719 : Blo 255820 729719 := bstep (se 1 (by rfl) ⟨547289, by rfl⟩ : syracuseStep 729719 = 1094579) B1094579
theorem B1319597 : Blo 255820 1319597 := bstep (se 3 (by rfl) ⟨247424, by rfl⟩ : syracuseStep 1319597 = 494849) B494849
theorem B467831 : Blo 255820 467831 := bstep (se 1 (by rfl) ⟨350873, by rfl⟩ : syracuseStep 467831 = 701747) B701747
theorem B435145 : Blo 255820 435145 := bstep (se 2 (by rfl) ⟨163179, by rfl⟩ : syracuseStep 435145 = 326359) B326359
theorem B1320137 : Blo 255820 1320137 := bstep (se 2 (by rfl) ⟨495051, by rfl⟩ : syracuseStep 1320137 = 990103) B990103
theorem B4072913 : Blo 255820 4072913 := bstep (se 2 (by rfl) ⟨1527342, by rfl⟩ : syracuseStep 4072913 = 3054685) B3054685
theorem B435847 : Blo 255820 435847 := bstep (se 1 (by rfl) ⟨326885, by rfl⟩ : syracuseStep 435847 = 653771) B653771
theorem B730777 : Blo 255820 730777 := bstep (se 2 (by rfl) ⟨274041, by rfl⟩ : syracuseStep 730777 = 548083) B548083
theorem B731393 : Blo 255820 731393 := bstep (se 2 (by rfl) ⟨274272, by rfl⟩ : syracuseStep 731393 = 548545) B548545
theorem B436495 : Blo 255820 436495 := bstep (se 1 (by rfl) ⟨327371, by rfl⟩ : syracuseStep 436495 = 654743) B654743
theorem B1780481 : Blo 255820 1780481 := bstep (se 2 (by rfl) ⟨667680, by rfl⟩ : syracuseStep 1780481 = 1335361) B1335361
theorem B437035 : Blo 255820 437035 := bstep (se 1 (by rfl) ⟨327776, by rfl⟩ : syracuseStep 437035 = 655553) B655553
theorem B437177 : Blo 255820 437177 := bstep (se 2 (by rfl) ⟨163941, by rfl⟩ : syracuseStep 437177 = 327883) B327883
theorem B2796605 : Blo 255820 2796605 := bstep (se 3 (by rfl) ⟨524363, by rfl⟩ : syracuseStep 2796605 = 1048727) B1048727
theorem B732361 : Blo 255820 732361 := bstep (se 2 (by rfl) ⟨274635, by rfl⟩ : syracuseStep 732361 = 549271) B549271
theorem B831019 : Blo 255820 831019 := bstep (se 1 (by rfl) ⟨623264, by rfl⟩ : syracuseStep 831019 = 1246529) B1246529
theorem B3124813 : Blo 255820 3124813 := bstep (se 3 (by rfl) ⟨585902, by rfl⟩ : syracuseStep 3124813 = 1171805) B1171805
theorem B437879 : Blo 255820 437879 := bstep (se 1 (by rfl) ⟨328409, by rfl⟩ : syracuseStep 437879 = 656819) B656819
theorem B863945 : Blo 255820 863945 := bstep (se 2 (by rfl) ⟨323979, by rfl⟩ : syracuseStep 863945 = 647959) B647959
theorem B3550949 : Blo 255820 3550949 := bstep (se 4 (by rfl) ⟨332901, by rfl⟩ : syracuseStep 3550949 = 665803) B665803
theorem B2338723 : Blo 255820 2338723 := bstep (se 1 (by rfl) ⟨1754042, by rfl⟩ : syracuseStep 2338723 = 3508085) B3508085
theorem B438331 : Blo 255820 438331 := bstep (se 1 (by rfl) ⟨328748, by rfl⟩ : syracuseStep 438331 = 657497) B657497
theorem B700535 : Blo 255820 700535 := bstep (se 1 (by rfl) ⟨525401, by rfl⟩ : syracuseStep 700535 = 1050803) B1050803
theorem B864647 : Blo 255820 864647 := bstep (se 1 (by rfl) ⟨648485, by rfl⟩ : syracuseStep 864647 = 1296971) B1296971
theorem B373135 : Blo 255820 373135 := bstep (se 1 (by rfl) ⟨279851, by rfl⟩ : syracuseStep 373135 = 559703) B559703
theorem B3387869 : Blo 255820 3387869 := bstep (se 3 (by rfl) ⟨635225, by rfl⟩ : syracuseStep 3387869 = 1270451) B1270451
theorem B2208323 : Blo 255820 2208323 := bstep (se 1 (by rfl) ⟨1656242, by rfl⟩ : syracuseStep 2208323 = 3312485) B3312485
theorem B865025 : Blo 255820 865025 := bstep (se 2 (by rfl) ⟨324384, by rfl⟩ : syracuseStep 865025 = 648769) B648769
theorem B733967 : Blo 255820 733967 := bstep (se 1 (by rfl) ⟨550475, by rfl⟩ : syracuseStep 733967 = 1100951) B1100951
theorem B2635217 : Blo 255820 2635217 := bstep (se 2 (by rfl) ⟨988206, by rfl⟩ : syracuseStep 2635217 = 1976413) B1976413
theorem B865835 : Blo 255820 865835 := bstep (se 1 (by rfl) ⟨649376, by rfl⟩ : syracuseStep 865835 = 1298753) B1298753
theorem B800545 : Blo 255820 800545 := bstep (se 2 (by rfl) ⟨300204, by rfl⟩ : syracuseStep 800545 = 600409) B600409
theorem B2471755 : Blo 255820 2471755 := bstep (se 1 (by rfl) ⟨1853816, by rfl⟩ : syracuseStep 2471755 = 3707633) B3707633
theorem B735095 : Blo 255820 735095 := bstep (se 1 (by rfl) ⟨551321, by rfl⟩ : syracuseStep 735095 = 1102643) B1102643
theorem B1718561 : Blo 255820 1718561 := bstep (se 2 (by rfl) ⟨644460, by rfl⟩ : syracuseStep 1718561 = 1288921) B1288921
theorem B309623 : Blo 255820 309623 := bstep (se 1 (by rfl) ⟨232217, by rfl⟩ : syracuseStep 309623 = 464435) B464435
theorem B1063315 : Blo 255820 1063315 := bstep (se 1 (by rfl) ⟨797486, by rfl⟩ : syracuseStep 1063315 = 1594973) B1594973
theorem B2472677 : Blo 255820 2472677 := bstep (se 4 (by rfl) ⟨231813, by rfl⟩ : syracuseStep 2472677 = 463627) B463627
theorem B1096507 : Blo 255820 1096507 := bstep (se 1 (by rfl) ⟨822380, by rfl⟩ : syracuseStep 1096507 = 1644761) B1644761
theorem B867131 : Blo 255820 867131 := bstep (se 1 (by rfl) ⟨650348, by rfl⟩ : syracuseStep 867131 = 1300697) B1300697
theorem B310315 : Blo 255820 310315 := bstep (se 1 (by rfl) ⟨232736, by rfl⟩ : syracuseStep 310315 = 465473) B465473
theorem B867617 : Blo 255820 867617 := bstep (se 2 (by rfl) ⟨325356, by rfl⟩ : syracuseStep 867617 = 650713) B650713
theorem B998689 : Blo 255820 998689 := bstep (se 2 (by rfl) ⟨374508, by rfl⟩ : syracuseStep 998689 = 749017) B749017
theorem B1752455 : Blo 255820 1752455 := bstep (se 1 (by rfl) ⟨1314341, by rfl⟩ : syracuseStep 1752455 = 2628683) B2628683
theorem B736769 : Blo 255820 736769 := bstep (se 2 (by rfl) ⟨276288, by rfl⟩ : syracuseStep 736769 = 552577) B552577
theorem B736883 : Blo 255820 736883 := bstep (se 1 (by rfl) ⟨552662, by rfl⟩ : syracuseStep 736883 = 1105325) B1105325
theorem B868211 : Blo 255820 868211 := bstep (se 1 (by rfl) ⟨651158, by rfl⟩ : syracuseStep 868211 = 1302317) B1302317
theorem B737225 : Blo 255820 737225 := bstep (se 2 (by rfl) ⟨276459, by rfl⟩ : syracuseStep 737225 = 552919) B552919
theorem B2211851 : Blo 255820 2211851 := bstep (se 1 (by rfl) ⟨1658888, by rfl⟩ : syracuseStep 2211851 = 3317777) B3317777
theorem B409801 : Blo 255820 409801 := bstep (se 2 (by rfl) ⟨153675, by rfl⟩ : syracuseStep 409801 = 307351) B307351
theorem B1098269 : Blo 255820 1098269 := bstep (se 3 (by rfl) ⟨205925, by rfl⟩ : syracuseStep 1098269 = 411851) B411851
theorem B2212697 : Blo 255820 2212697 := bstep (se 2 (by rfl) ⟨829761, by rfl⟩ : syracuseStep 2212697 = 1659523) B1659523
theorem B1393523 : Blo 255820 1393523 := bstep (se 1 (by rfl) ⟨1045142, by rfl⟩ : syracuseStep 1393523 = 2090285) B2090285
theorem B3130265 : Blo 255820 3130265 := bstep (se 2 (by rfl) ⟨1173849, by rfl⟩ : syracuseStep 3130265 = 2347699) B2347699
theorem B1098953 : Blo 255820 1098953 := bstep (se 2 (by rfl) ⟨412107, by rfl⟩ : syracuseStep 1098953 = 824215) B824215
theorem B1885421 : Blo 255820 1885421 := bstep (se 3 (by rfl) ⟨353516, by rfl⟩ : syracuseStep 1885421 = 707033) B707033
theorem B9880865 : Blo 255820 9880865 := bstep (se 2 (by rfl) ⟨3705324, by rfl⟩ : syracuseStep 9880865 = 7410649) B7410649
theorem B1295675 : Blo 255820 1295675 := bstep (se 1 (by rfl) ⟨971756, by rfl⟩ : syracuseStep 1295675 = 1943513) B1943513
theorem B574921 : Blo 255820 574921 := bstep (se 2 (by rfl) ⟨215595, by rfl⟩ : syracuseStep 574921 = 431191) B431191
theorem B1295837 : Blo 255820 1295837 := bstep (se 3 (by rfl) ⟨242969, by rfl⟩ : syracuseStep 1295837 = 485939) B485939
theorem B1263107 : Blo 255820 1263107 := bstep (se 1 (by rfl) ⟨947330, by rfl⟩ : syracuseStep 1263107 = 1894661) B1894661
theorem B509455 : Blo 255820 509455 := bstep (se 1 (by rfl) ⟨382091, by rfl⟩ : syracuseStep 509455 = 764183) B764183
theorem B1492673 : Blo 255820 1492673 := bstep (se 2 (by rfl) ⟨559752, by rfl⟩ : syracuseStep 1492673 = 1119505) B1119505
theorem B1296161 : Blo 255820 1296161 := bstep (se 2 (by rfl) ⟨486060, by rfl⟩ : syracuseStep 1296161 = 972121) B972121
theorem B739115 : Blo 255820 739115 := bstep (se 1 (by rfl) ⟨554336, by rfl⟩ : syracuseStep 739115 = 1108673) B1108673
theorem B1230727 : Blo 255820 1230727 := bstep (se 1 (by rfl) ⟨923045, by rfl⟩ : syracuseStep 1230727 = 1846091) B1846091
theorem B739343 : Blo 255820 739343 := bstep (se 1 (by rfl) ⟨554507, by rfl⟩ : syracuseStep 739343 = 1109015) B1109015
theorem B706619 : Blo 255820 706619 := bstep (se 1 (by rfl) ⟨529964, by rfl⟩ : syracuseStep 706619 = 1059929) B1059929
theorem B936251 : Blo 255820 936251 := bstep (se 1 (by rfl) ⟨702188, by rfl⟩ : syracuseStep 936251 = 1404377) B1404377
theorem B575891 : Blo 255820 575891 := bstep (se 1 (by rfl) ⟨431918, by rfl⟩ : syracuseStep 575891 = 863837) B863837
theorem B870803 : Blo 255820 870803 := bstep (se 1 (by rfl) ⟨653102, by rfl⟩ : syracuseStep 870803 = 1306205) B1306205
theorem B575945 : Blo 255820 575945 := bstep (se 2 (by rfl) ⟨215979, by rfl⟩ : syracuseStep 575945 = 431959) B431959
theorem B1297133 : Blo 255820 1297133 := bstep (se 3 (by rfl) ⟨243212, by rfl⟩ : syracuseStep 1297133 = 486425) B486425
theorem B1100729 : Blo 255820 1100729 := bstep (se 2 (by rfl) ⟨412773, by rfl⟩ : syracuseStep 1100729 = 825547) B825547
theorem B576647 : Blo 255820 576647 := bstep (se 1 (by rfl) ⟨432485, by rfl⟩ : syracuseStep 576647 = 864971) B864971
theorem B576827 : Blo 255820 576827 := bstep (se 1 (by rfl) ⟨432620, by rfl⟩ : syracuseStep 576827 = 865241) B865241
theorem B576953 : Blo 255820 576953 := bstep (se 2 (by rfl) ⟨216357, by rfl⟩ : syracuseStep 576953 = 432715) B432715
theorem B413113 : Blo 255820 413113 := bstep (se 2 (by rfl) ⟨154917, by rfl⟩ : syracuseStep 413113 = 309835) B309835
theorem B1953233 : Blo 255820 1953233 := bstep (se 2 (by rfl) ⟨732462, by rfl⟩ : syracuseStep 1953233 = 1464925) B1464925
theorem B1297943 : Blo 255820 1297943 := bstep (se 1 (by rfl) ⟨973457, by rfl⟩ : syracuseStep 1297943 = 1946915) B1946915
theorem B1461827 : Blo 255820 1461827 := bstep (se 1 (by rfl) ⟨1096370, by rfl⟩ : syracuseStep 1461827 = 2192741) B2192741
theorem B577295 : Blo 255820 577295 := bstep (se 1 (by rfl) ⟨432971, by rfl⟩ : syracuseStep 577295 = 865943) B865943
theorem B872207 : Blo 255820 872207 := bstep (se 1 (by rfl) ⟨654155, by rfl⟩ : syracuseStep 872207 = 1308311) B1308311
theorem B577313 : Blo 255820 577313 := bstep (se 2 (by rfl) ⟨216492, by rfl⟩ : syracuseStep 577313 = 432985) B432985
theorem B1462283 : Blo 255820 1462283 := bstep (se 1 (by rfl) ⟨1096712, by rfl⟩ : syracuseStep 1462283 = 2193425) B2193425
theorem B872477 : Blo 255820 872477 := bstep (se 3 (by rfl) ⟨163589, by rfl⟩ : syracuseStep 872477 = 327179) B327179
theorem B577655 : Blo 255820 577655 := bstep (se 1 (by rfl) ⟨433241, by rfl⟩ : syracuseStep 577655 = 866483) B866483
theorem B348295 : Blo 255820 348295 := bstep (se 1 (by rfl) ⟨261221, by rfl⟩ : syracuseStep 348295 = 522443) B522443
theorem B413831 : Blo 255820 413831 := bstep (se 1 (by rfl) ⟨310373, by rfl⟩ : syracuseStep 413831 = 620747) B620747
theorem B577835 : Blo 255820 577835 := bstep (se 1 (by rfl) ⟨433376, by rfl⟩ : syracuseStep 577835 = 866753) B866753
theorem B2806163 : Blo 255820 2806163 := bstep (se 1 (by rfl) ⟨2104622, by rfl⟩ : syracuseStep 2806163 = 4209245) B4209245
theorem B414343 : Blo 255820 414343 := bstep (se 1 (by rfl) ⟨310757, by rfl⟩ : syracuseStep 414343 = 621515) B621515
theorem B578195 : Blo 255820 578195 := bstep (se 1 (by rfl) ⟨433646, by rfl⟩ : syracuseStep 578195 = 867293) B867293
theorem B578249 : Blo 255820 578249 := bstep (se 2 (by rfl) ⟨216843, by rfl⟩ : syracuseStep 578249 = 433687) B433687
theorem B971635 : Blo 255820 971635 := bstep (se 1 (by rfl) ⟨728726, by rfl⟩ : syracuseStep 971635 = 1457453) B1457453
theorem B1102727 : Blo 255820 1102727 := bstep (se 1 (by rfl) ⟨827045, by rfl⟩ : syracuseStep 1102727 = 1654091) B1654091
theorem B1102967 : Blo 255820 1102967 := bstep (se 1 (by rfl) ⟨827225, by rfl⟩ : syracuseStep 1102967 = 1654451) B1654451
theorem B1561801 : Blo 255820 1561801 := bstep (se 2 (by rfl) ⟨585675, by rfl⟩ : syracuseStep 1561801 = 1171351) B1171351
theorem B578951 : Blo 255820 578951 := bstep (se 1 (by rfl) ⟨434213, by rfl⟩ : syracuseStep 578951 = 868427) B868427
theorem B873881 : Blo 255820 873881 := bstep (se 2 (by rfl) ⟨327705, by rfl⟩ : syracuseStep 873881 = 655411) B655411
theorem B5952953 : Blo 255820 5952953 := bstep (se 2 (by rfl) ⟨2232357, by rfl⟩ : syracuseStep 5952953 = 4464715) B4464715
theorem B1234379 : Blo 255820 1234379 := bstep (se 1 (by rfl) ⟨925784, by rfl⟩ : syracuseStep 1234379 = 1851569) B1851569
theorem B579131 : Blo 255820 579131 := bstep (se 1 (by rfl) ⟨434348, by rfl⟩ : syracuseStep 579131 = 868697) B868697
theorem B415291 : Blo 255820 415291 := bstep (se 1 (by rfl) ⟨311468, by rfl⟩ : syracuseStep 415291 = 622937) B622937
theorem B579257 : Blo 255820 579257 := bstep (se 2 (by rfl) ⟨217221, by rfl⟩ : syracuseStep 579257 = 434443) B434443
theorem B1038233 : Blo 255820 1038233 := bstep (se 2 (by rfl) ⟨389337, by rfl⟩ : syracuseStep 1038233 = 778675) B778675
theorem B1038347 : Blo 255820 1038347 := bstep (se 1 (by rfl) ⟨778760, by rfl⟩ : syracuseStep 1038347 = 1557521) B1557521
theorem B579599 : Blo 255820 579599 := bstep (se 1 (by rfl) ⟨434699, by rfl⟩ : syracuseStep 579599 = 869399) B869399
theorem B579617 : Blo 255820 579617 := bstep (se 2 (by rfl) ⟨217356, by rfl⟩ : syracuseStep 579617 = 434713) B434713
theorem B874583 : Blo 255820 874583 := bstep (se 1 (by rfl) ⟨655937, by rfl⟩ : syracuseStep 874583 = 1311875) B1311875
theorem B2840777 : Blo 255820 2840777 := bstep (se 2 (by rfl) ⟨1065291, by rfl⟩ : syracuseStep 2840777 = 2130583) B2130583
theorem B579959 : Blo 255820 579959 := bstep (se 1 (by rfl) ⟨434969, by rfl⟩ : syracuseStep 579959 = 869939) B869939
theorem B1301021 : Blo 255820 1301021 := bstep (se 3 (by rfl) ⟨243941, by rfl⟩ : syracuseStep 1301021 = 487883) B487883
theorem B580139 : Blo 255820 580139 := bstep (se 1 (by rfl) ⟨435104, by rfl⟩ : syracuseStep 580139 = 870209) B870209
theorem B875069 : Blo 255820 875069 := bstep (se 3 (by rfl) ⟨164075, by rfl⟩ : syracuseStep 875069 = 328151) B328151
theorem B383735 : Blo 255820 383735 := bstep (se 1 (by rfl) ⟨287801, by rfl⟩ : syracuseStep 383735 = 575603) B575603
theorem B1104641 : Blo 255820 1104641 := bstep (se 2 (by rfl) ⟨414240, by rfl⟩ : syracuseStep 1104641 = 828481) B828481
theorem B383759 : Blo 255820 383759 := bstep (se 1 (by rfl) ⟨287819, by rfl⟩ : syracuseStep 383759 = 575639) B575639
theorem B383801 : Blo 255820 383801 := bstep (se 2 (by rfl) ⟨143925, by rfl⟩ : syracuseStep 383801 = 287851) B287851
theorem B383879 : Blo 255820 383879 := bstep (se 1 (by rfl) ⟨287909, by rfl⟩ : syracuseStep 383879 = 575819) B575819
theorem B580499 : Blo 255820 580499 := bstep (se 1 (by rfl) ⟨435374, by rfl⟩ : syracuseStep 580499 = 870749) B870749
theorem B2775971 : Blo 255820 2775971 := bstep (se 1 (by rfl) ⟨2081978, by rfl⟩ : syracuseStep 2775971 = 4163957) B4163957
theorem B383915 : Blo 255820 383915 := bstep (se 1 (by rfl) ⟨287936, by rfl⟩ : syracuseStep 383915 = 575873) B575873
theorem B383945 : Blo 255820 383945 := bstep (se 2 (by rfl) ⟨143979, by rfl⟩ : syracuseStep 383945 = 287959) B287959
theorem B580553 : Blo 255820 580553 := bstep (se 2 (by rfl) ⟨217707, by rfl⟩ : syracuseStep 580553 = 435415) B435415
theorem B1301507 : Blo 255820 1301507 := bstep (se 1 (by rfl) ⟨976130, by rfl⟩ : syracuseStep 1301507 = 1952261) B1952261
theorem B973853 : Blo 255820 973853 := bstep (se 3 (by rfl) ⟨182597, by rfl⟩ : syracuseStep 973853 = 365195) B365195
theorem B384059 : Blo 255820 384059 := bstep (se 1 (by rfl) ⟨288044, by rfl⟩ : syracuseStep 384059 = 576089) B576089
theorem B384119 : Blo 255820 384119 := bstep (se 1 (by rfl) ⟨288089, by rfl⟩ : syracuseStep 384119 = 576179) B576179
theorem B384143 : Blo 255820 384143 := bstep (se 1 (by rfl) ⟨288107, by rfl⟩ : syracuseStep 384143 = 576215) B576215
theorem B384185 : Blo 255820 384185 := bstep (se 2 (by rfl) ⟨144069, by rfl⟩ : syracuseStep 384185 = 288139) B288139
theorem B548041 : Blo 255820 548041 := bstep (se 2 (by rfl) ⟨205515, by rfl⟩ : syracuseStep 548041 = 411031) B411031
theorem B384263 : Blo 255820 384263 := bstep (se 1 (by rfl) ⟨288197, by rfl⟩ : syracuseStep 384263 = 576395) B576395
theorem B1662241 : Blo 255820 1662241 := bstep (se 2 (by rfl) ⟨623340, by rfl⟩ : syracuseStep 1662241 = 1246681) B1246681
theorem B384299 : Blo 255820 384299 := bstep (se 1 (by rfl) ⟨288224, by rfl⟩ : syracuseStep 384299 = 576449) B576449
theorem B384329 : Blo 255820 384329 := bstep (se 2 (by rfl) ⟨144123, by rfl⟩ : syracuseStep 384329 = 288247) B288247
theorem B384443 : Blo 255820 384443 := bstep (se 1 (by rfl) ⟨288332, by rfl⟩ : syracuseStep 384443 = 576665) B576665
theorem B384503 : Blo 255820 384503 := bstep (se 1 (by rfl) ⟨288377, by rfl⟩ : syracuseStep 384503 = 576755) B576755
theorem B384527 : Blo 255820 384527 := bstep (se 1 (by rfl) ⟨288395, by rfl⟩ : syracuseStep 384527 = 576791) B576791
theorem B384569 : Blo 255820 384569 := bstep (se 2 (by rfl) ⟨144213, by rfl⟩ : syracuseStep 384569 = 288427) B288427
theorem B384647 : Blo 255820 384647 := bstep (se 1 (by rfl) ⟨288485, by rfl⟩ : syracuseStep 384647 = 576971) B576971
theorem B581255 : Blo 255820 581255 := bstep (se 1 (by rfl) ⟨435941, by rfl⟩ : syracuseStep 581255 = 871883) B871883
theorem B384683 : Blo 255820 384683 := bstep (se 1 (by rfl) ⟨288512, by rfl⟩ : syracuseStep 384683 = 577025) B577025
theorem B384713 : Blo 255820 384713 := bstep (se 2 (by rfl) ⟨144267, by rfl⟩ : syracuseStep 384713 = 288535) B288535
theorem B974537 : Blo 255820 974537 := bstep (se 2 (by rfl) ⟨365451, by rfl⟩ : syracuseStep 974537 = 730903) B730903
theorem B384827 : Blo 255820 384827 := bstep (se 1 (by rfl) ⟨288620, by rfl⟩ : syracuseStep 384827 = 577241) B577241
theorem B581435 : Blo 255820 581435 := bstep (se 1 (by rfl) ⟨436076, by rfl⟩ : syracuseStep 581435 = 872153) B872153
theorem B1466201 : Blo 255820 1466201 := bstep (se 2 (by rfl) ⟨549825, by rfl⟩ : syracuseStep 1466201 = 1099651) B1099651
theorem B843635 : Blo 255820 843635 := bstep (se 1 (by rfl) ⟨632726, by rfl⟩ : syracuseStep 843635 = 1265453) B1265453
theorem B384887 : Blo 255820 384887 := bstep (se 1 (by rfl) ⟨288665, by rfl⟩ : syracuseStep 384887 = 577331) B577331
theorem B384911 : Blo 255820 384911 := bstep (se 1 (by rfl) ⟨288683, by rfl⟩ : syracuseStep 384911 = 577367) B577367
theorem B1400723 : Blo 255820 1400723 := bstep (se 1 (by rfl) ⟨1050542, by rfl⟩ : syracuseStep 1400723 = 2101085) B2101085
theorem B384953 : Blo 255820 384953 := bstep (se 2 (by rfl) ⟨144357, by rfl⟩ : syracuseStep 384953 = 288715) B288715
theorem B581561 : Blo 255820 581561 := bstep (se 2 (by rfl) ⟨218085, by rfl⟩ : syracuseStep 581561 = 436171) B436171
theorem B876473 : Blo 255820 876473 := bstep (se 2 (by rfl) ⟨328677, by rfl⟩ : syracuseStep 876473 = 657355) B657355
theorem B385031 : Blo 255820 385031 := bstep (se 1 (by rfl) ⟨288773, by rfl⟩ : syracuseStep 385031 = 577547) B577547
theorem B385067 : Blo 255820 385067 := bstep (se 1 (by rfl) ⟨288800, by rfl⟩ : syracuseStep 385067 = 577601) B577601
theorem B385097 : Blo 255820 385097 := bstep (se 2 (by rfl) ⟨144411, by rfl⟩ : syracuseStep 385097 = 288823) B288823
theorem B385211 : Blo 255820 385211 := bstep (se 1 (by rfl) ⟨288908, by rfl⟩ : syracuseStep 385211 = 577817) B577817
theorem B385271 : Blo 255820 385271 := bstep (se 1 (by rfl) ⟨288953, by rfl⟩ : syracuseStep 385271 = 577907) B577907
theorem B385295 : Blo 255820 385295 := bstep (se 1 (by rfl) ⟨288971, by rfl⟩ : syracuseStep 385295 = 577943) B577943
theorem B581903 : Blo 255820 581903 := bstep (se 1 (by rfl) ⟨436427, by rfl⟩ : syracuseStep 581903 = 872855) B872855
theorem B1466657 : Blo 255820 1466657 := bstep (se 2 (by rfl) ⟨549996, by rfl⟩ : syracuseStep 1466657 = 1099993) B1099993
theorem B581921 : Blo 255820 581921 := bstep (se 2 (by rfl) ⟨218220, by rfl⟩ : syracuseStep 581921 = 436441) B436441
theorem B385337 : Blo 255820 385337 := bstep (se 2 (by rfl) ⟨144501, by rfl⟩ : syracuseStep 385337 = 289003) B289003
theorem B385415 : Blo 255820 385415 := bstep (se 1 (by rfl) ⟨289061, by rfl⟩ : syracuseStep 385415 = 578123) B578123
theorem B385451 : Blo 255820 385451 := bstep (se 1 (by rfl) ⟨289088, by rfl⟩ : syracuseStep 385451 = 578177) B578177
theorem B385481 : Blo 255820 385481 := bstep (se 2 (by rfl) ⟨144555, by rfl⟩ : syracuseStep 385481 = 289111) B289111
theorem B1466909 : Blo 255820 1466909 := bstep (se 3 (by rfl) ⟨275045, by rfl⟩ : syracuseStep 1466909 = 550091) B550091
theorem B385595 : Blo 255820 385595 := bstep (se 1 (by rfl) ⟨289196, by rfl⟩ : syracuseStep 385595 = 578393) B578393
theorem B1303127 : Blo 255820 1303127 := bstep (se 1 (by rfl) ⟨977345, by rfl⟩ : syracuseStep 1303127 = 1954691) B1954691
theorem B385655 : Blo 255820 385655 := bstep (se 1 (by rfl) ⟨289241, by rfl⟩ : syracuseStep 385655 = 578483) B578483
theorem B582263 : Blo 255820 582263 := bstep (se 1 (by rfl) ⟨436697, by rfl⟩ : syracuseStep 582263 = 873395) B873395
theorem B385679 : Blo 255820 385679 := bstep (se 1 (by rfl) ⟨289259, by rfl⟩ : syracuseStep 385679 = 578519) B578519
theorem B385721 : Blo 255820 385721 := bstep (se 2 (by rfl) ⟨144645, by rfl⟩ : syracuseStep 385721 = 289291) B289291
theorem B385799 : Blo 255820 385799 := bstep (se 1 (by rfl) ⟨289349, by rfl⟩ : syracuseStep 385799 = 578699) B578699
theorem B385835 : Blo 255820 385835 := bstep (se 1 (by rfl) ⟨289376, by rfl⟩ : syracuseStep 385835 = 578753) B578753
theorem B582443 : Blo 255820 582443 := bstep (se 1 (by rfl) ⟨436832, by rfl⟩ : syracuseStep 582443 = 873665) B873665
theorem B385865 : Blo 255820 385865 := bstep (se 2 (by rfl) ⟨144699, by rfl⟩ : syracuseStep 385865 = 289399) B289399
theorem B648071 : Blo 255820 648071 := bstep (se 1 (by rfl) ⟨486053, by rfl⟩ : syracuseStep 648071 = 972107) B972107
theorem B648121 : Blo 255820 648121 := bstep (se 2 (by rfl) ⟨243045, by rfl⟩ : syracuseStep 648121 = 486091) B486091
theorem B1401785 : Blo 255820 1401785 := bstep (se 2 (by rfl) ⟨525669, by rfl⟩ : syracuseStep 1401785 = 1051339) B1051339
theorem B385979 : Blo 255820 385979 := bstep (se 1 (by rfl) ⟨289484, by rfl⟩ : syracuseStep 385979 = 578969) B578969
theorem B386039 : Blo 255820 386039 := bstep (se 1 (by rfl) ⟨289529, by rfl⟩ : syracuseStep 386039 = 579059) B579059
theorem B4482053 : Blo 255820 4482053 := bstep (se 4 (by rfl) ⟨420192, by rfl⟩ : syracuseStep 4482053 = 840385) B840385
theorem B386063 : Blo 255820 386063 := bstep (se 1 (by rfl) ⟨289547, by rfl⟩ : syracuseStep 386063 = 579095) B579095
theorem B386105 : Blo 255820 386105 := bstep (se 2 (by rfl) ⟨144789, by rfl⟩ : syracuseStep 386105 = 289579) B289579
theorem B1303613 : Blo 255820 1303613 := bstep (se 3 (by rfl) ⟨244427, by rfl⟩ : syracuseStep 1303613 = 488855) B488855
theorem B386183 : Blo 255820 386183 := bstep (se 1 (by rfl) ⟨289637, by rfl⟩ : syracuseStep 386183 = 579275) B579275
theorem B287887 : Blo 255820 287887 := bstep (se 1 (by rfl) ⟨215915, by rfl⟩ : syracuseStep 287887 = 431831) B431831
theorem B582803 : Blo 255820 582803 := bstep (se 1 (by rfl) ⟨437102, by rfl⟩ : syracuseStep 582803 = 874205) B874205
theorem B386219 : Blo 255820 386219 := bstep (se 1 (by rfl) ⟨289664, by rfl⟩ : syracuseStep 386219 = 579329) B579329
theorem B386249 : Blo 255820 386249 := bstep (se 2 (by rfl) ⟨144843, by rfl⟩ : syracuseStep 386249 = 289687) B289687
theorem B582857 : Blo 255820 582857 := bstep (se 2 (by rfl) ⟨218571, by rfl⟩ : syracuseStep 582857 = 437143) B437143
theorem B5596397 : Blo 255820 5596397 := bstep (se 3 (by rfl) ⟨1049324, by rfl⟩ : syracuseStep 5596397 = 2098649) B2098649
theorem B386363 : Blo 255820 386363 := bstep (se 1 (by rfl) ⟨289772, by rfl⟩ : syracuseStep 386363 = 579545) B579545
theorem B386423 : Blo 255820 386423 := bstep (se 1 (by rfl) ⟨289817, by rfl⟩ : syracuseStep 386423 = 579635) B579635
theorem B386447 : Blo 255820 386447 := bstep (se 1 (by rfl) ⟨289835, by rfl⟩ : syracuseStep 386447 = 579671) B579671
theorem B976313 : Blo 255820 976313 := bstep (se 2 (by rfl) ⟨366117, by rfl⟩ : syracuseStep 976313 = 732235) B732235
theorem B386489 : Blo 255820 386489 := bstep (se 2 (by rfl) ⟨144933, by rfl⟩ : syracuseStep 386489 = 289867) B289867
theorem B386567 : Blo 255820 386567 := bstep (se 1 (by rfl) ⟨289925, by rfl⟩ : syracuseStep 386567 = 579851) B579851
theorem B648719 : Blo 255820 648719 := bstep (se 1 (by rfl) ⟨486539, by rfl⟩ : syracuseStep 648719 = 973079) B973079
theorem B1762859 : Blo 255820 1762859 := bstep (se 1 (by rfl) ⟨1322144, by rfl⟩ : syracuseStep 1762859 = 2644289) B2644289
theorem B386603 : Blo 255820 386603 := bstep (se 1 (by rfl) ⟨289952, by rfl⟩ : syracuseStep 386603 = 579905) B579905
theorem B386633 : Blo 255820 386633 := bstep (se 2 (by rfl) ⟨144987, by rfl⟩ : syracuseStep 386633 = 289975) B289975
theorem B288391 : Blo 255820 288391 := bstep (se 1 (by rfl) ⟨216293, by rfl⟩ : syracuseStep 288391 = 432587) B432587
theorem B386747 : Blo 255820 386747 := bstep (se 1 (by rfl) ⟨290060, by rfl⟩ : syracuseStep 386747 = 580121) B580121
theorem B386807 : Blo 255820 386807 := bstep (se 1 (by rfl) ⟨290105, by rfl⟩ : syracuseStep 386807 = 580211) B580211
theorem B386831 : Blo 255820 386831 := bstep (se 1 (by rfl) ⟨290123, by rfl⟩ : syracuseStep 386831 = 580247) B580247
theorem B1009441 : Blo 255820 1009441 := bstep (se 2 (by rfl) ⟨378540, by rfl⟩ : syracuseStep 1009441 = 757081) B757081
theorem B386873 : Blo 255820 386873 := bstep (se 2 (by rfl) ⟨145077, by rfl⟩ : syracuseStep 386873 = 290155) B290155
theorem B288571 : Blo 255820 288571 := bstep (se 1 (by rfl) ⟨216428, by rfl⟩ : syracuseStep 288571 = 432857) B432857
theorem B550775 : Blo 255820 550775 := bstep (se 1 (by rfl) ⟨413081, by rfl⟩ : syracuseStep 550775 = 826163) B826163
theorem B255879 : Blo 255820 255879 := bstep (se 1 (by rfl) ⟨191909, by rfl⟩ : syracuseStep 255879 = 383819) B383819
theorem B386951 : Blo 255820 386951 := bstep (se 1 (by rfl) ⟨290213, by rfl⟩ : syracuseStep 386951 = 580427) B580427
theorem B583559 : Blo 255820 583559 := bstep (se 1 (by rfl) ⟨437669, by rfl⟩ : syracuseStep 583559 = 875339) B875339
theorem B255887 : Blo 255820 255887 := bstep (se 1 (by rfl) ⟨191915, by rfl⟩ : syracuseStep 255887 = 383831) B383831
theorem B386987 : Blo 255820 386987 := bstep (se 1 (by rfl) ⟨290240, by rfl⟩ : syracuseStep 386987 = 580481) B580481
theorem B255931 : Blo 255820 255931 := bstep (se 1 (by rfl) ⟨191948, by rfl⟩ : syracuseStep 255931 = 383897) B383897
theorem B387017 : Blo 255820 387017 := bstep (se 2 (by rfl) ⟨145131, by rfl⟩ : syracuseStep 387017 = 290263) B290263
theorem B256007 : Blo 255820 256007 := bstep (se 1 (by rfl) ⟨192005, by rfl⟩ : syracuseStep 256007 = 384011) B384011
theorem B256015 : Blo 255820 256015 := bstep (se 1 (by rfl) ⟨192011, by rfl⟩ : syracuseStep 256015 = 384023) B384023
theorem B256059 : Blo 255820 256059 := bstep (se 1 (by rfl) ⟨192044, by rfl⟩ : syracuseStep 256059 = 384089) B384089
theorem B387131 : Blo 255820 387131 := bstep (se 1 (by rfl) ⟨290348, by rfl⟩ : syracuseStep 387131 = 580697) B580697
theorem B583739 : Blo 255820 583739 := bstep (se 1 (by rfl) ⟨437804, by rfl⟩ : syracuseStep 583739 = 875609) B875609
theorem B387191 : Blo 255820 387191 := bstep (se 1 (by rfl) ⟨290393, by rfl⟩ : syracuseStep 387191 = 580787) B580787
theorem B256135 : Blo 255820 256135 := bstep (se 1 (by rfl) ⟨192101, by rfl⟩ : syracuseStep 256135 = 384203) B384203
theorem B256143 : Blo 255820 256143 := bstep (se 1 (by rfl) ⟨192107, by rfl⟩ : syracuseStep 256143 = 384215) B384215
theorem B387215 : Blo 255820 387215 := bstep (se 1 (by rfl) ⟨290411, by rfl⟩ : syracuseStep 387215 = 580823) B580823
theorem B387257 : Blo 255820 387257 := bstep (se 2 (by rfl) ⟨145221, by rfl⟩ : syracuseStep 387257 = 290443) B290443
theorem B583865 : Blo 255820 583865 := bstep (se 2 (by rfl) ⟨218949, by rfl⟩ : syracuseStep 583865 = 437899) B437899
theorem B256187 : Blo 255820 256187 := bstep (se 1 (by rfl) ⟨192140, by rfl⟩ : syracuseStep 256187 = 384281) B384281
theorem B649417 : Blo 255820 649417 := bstep (se 2 (by rfl) ⟨243531, by rfl⟩ : syracuseStep 649417 = 487063) B487063
theorem B256263 : Blo 255820 256263 := bstep (se 1 (by rfl) ⟨192197, by rfl⟩ : syracuseStep 256263 = 384395) B384395
theorem B387335 : Blo 255820 387335 := bstep (se 1 (by rfl) ⟨290501, by rfl⟩ : syracuseStep 387335 = 581003) B581003
theorem B256271 : Blo 255820 256271 := bstep (se 1 (by rfl) ⟨192203, by rfl⟩ : syracuseStep 256271 = 384407) B384407
theorem B289039 : Blo 255820 289039 := bstep (se 1 (by rfl) ⟨216779, by rfl⟩ : syracuseStep 289039 = 433559) B433559
theorem B387371 : Blo 255820 387371 := bstep (se 1 (by rfl) ⟨290528, by rfl⟩ : syracuseStep 387371 = 581057) B581057
theorem B256315 : Blo 255820 256315 := bstep (se 1 (by rfl) ⟨192236, by rfl⟩ : syracuseStep 256315 = 384473) B384473
theorem B551227 : Blo 255820 551227 := bstep (se 1 (by rfl) ⟨413420, by rfl⟩ : syracuseStep 551227 = 826841) B826841
theorem B387401 : Blo 255820 387401 := bstep (se 2 (by rfl) ⟨145275, by rfl⟩ : syracuseStep 387401 = 290551) B290551
theorem B649559 : Blo 255820 649559 := bstep (se 1 (by rfl) ⟨487169, by rfl⟩ : syracuseStep 649559 = 974339) B974339
theorem B256391 : Blo 255820 256391 := bstep (se 1 (by rfl) ⟨192293, by rfl⟩ : syracuseStep 256391 = 384587) B384587
theorem B256399 : Blo 255820 256399 := bstep (se 1 (by rfl) ⟨192299, by rfl⟩ : syracuseStep 256399 = 384599) B384599
theorem B4712849 : Blo 255820 4712849 := bstep (se 2 (by rfl) ⟨1767318, by rfl⟩ : syracuseStep 4712849 = 3534637) B3534637
theorem B3303827 : Blo 255820 3303827 := bstep (se 1 (by rfl) ⟨2477870, by rfl⟩ : syracuseStep 3303827 = 4955741) B4955741
theorem B256443 : Blo 255820 256443 := bstep (se 1 (by rfl) ⟨192332, by rfl⟩ : syracuseStep 256443 = 384665) B384665
theorem B387515 : Blo 255820 387515 := bstep (se 1 (by rfl) ⟨290636, by rfl⟩ : syracuseStep 387515 = 581273) B581273
theorem B485833 : Blo 255820 485833 := bstep (se 2 (by rfl) ⟨182187, by rfl⟩ : syracuseStep 485833 = 364375) B364375
theorem B387575 : Blo 255820 387575 := bstep (se 1 (by rfl) ⟨290681, by rfl⟩ : syracuseStep 387575 = 581363) B581363
theorem B256519 : Blo 255820 256519 := bstep (se 1 (by rfl) ⟨192389, by rfl⟩ : syracuseStep 256519 = 384779) B384779
theorem B256527 : Blo 255820 256527 := bstep (se 1 (by rfl) ⟨192395, by rfl⟩ : syracuseStep 256527 = 384791) B384791
theorem B780815 : Blo 255820 780815 := bstep (se 1 (by rfl) ⟨585611, by rfl⟩ : syracuseStep 780815 = 1171223) B1171223
theorem B387599 : Blo 255820 387599 := bstep (se 1 (by rfl) ⟨290699, by rfl⟩ : syracuseStep 387599 = 581399) B581399
theorem B584207 : Blo 255820 584207 := bstep (se 1 (by rfl) ⟨438155, by rfl⟩ : syracuseStep 584207 = 876311) B876311
theorem B584225 : Blo 255820 584225 := bstep (se 2 (by rfl) ⟨219084, by rfl⟩ : syracuseStep 584225 = 438169) B438169
theorem B387641 : Blo 255820 387641 := bstep (se 2 (by rfl) ⟨145365, by rfl⟩ : syracuseStep 387641 = 290731) B290731
theorem B256571 : Blo 255820 256571 := bstep (se 1 (by rfl) ⟨192428, by rfl⟩ : syracuseStep 256571 = 384857) B384857
theorem B256647 : Blo 255820 256647 := bstep (se 1 (by rfl) ⟨192485, by rfl⟩ : syracuseStep 256647 = 384971) B384971
theorem B387719 : Blo 255820 387719 := bstep (se 1 (by rfl) ⟨290789, by rfl⟩ : syracuseStep 387719 = 581579) B581579
theorem B256655 : Blo 255820 256655 := bstep (se 1 (by rfl) ⟨192491, by rfl⟩ : syracuseStep 256655 = 384983) B384983
theorem B387755 : Blo 255820 387755 := bstep (se 1 (by rfl) ⟨290816, by rfl⟩ : syracuseStep 387755 = 581633) B581633
theorem B256699 : Blo 255820 256699 := bstep (se 1 (by rfl) ⟨192524, by rfl⟩ : syracuseStep 256699 = 385049) B385049
theorem B387785 : Blo 255820 387785 := bstep (se 2 (by rfl) ⟨145419, by rfl⟩ : syracuseStep 387785 = 290839) B290839
theorem B256775 : Blo 255820 256775 := bstep (se 1 (by rfl) ⟨192581, by rfl⟩ : syracuseStep 256775 = 385163) B385163
theorem B289543 : Blo 255820 289543 := bstep (se 1 (by rfl) ⟨217157, by rfl⟩ : syracuseStep 289543 = 434315) B434315
theorem B256783 : Blo 255820 256783 := bstep (se 1 (by rfl) ⟨192587, by rfl⟩ : syracuseStep 256783 = 385175) B385175
theorem B1305395 : Blo 255820 1305395 := bstep (se 1 (by rfl) ⟨979046, by rfl⟩ : syracuseStep 1305395 = 1958093) B1958093
theorem B256827 : Blo 255820 256827 := bstep (se 1 (by rfl) ⟨192620, by rfl⟩ : syracuseStep 256827 = 385241) B385241
theorem B387899 : Blo 255820 387899 := bstep (se 1 (by rfl) ⟨290924, by rfl⟩ : syracuseStep 387899 = 581849) B581849
theorem B1469299 : Blo 255820 1469299 := bstep (se 1 (by rfl) ⟨1101974, by rfl⟩ : syracuseStep 1469299 = 2203949) B2203949
theorem B387959 : Blo 255820 387959 := bstep (se 1 (by rfl) ⟨290969, by rfl⟩ : syracuseStep 387959 = 581939) B581939
theorem B584567 : Blo 255820 584567 := bstep (se 1 (by rfl) ⟨438425, by rfl⟩ : syracuseStep 584567 = 876851) B876851
theorem B256903 : Blo 255820 256903 := bstep (se 1 (by rfl) ⟨192677, by rfl⟩ : syracuseStep 256903 = 385355) B385355
theorem B256911 : Blo 255820 256911 := bstep (se 1 (by rfl) ⟨192683, by rfl⟩ : syracuseStep 256911 = 385367) B385367
theorem B387983 : Blo 255820 387983 := bstep (se 1 (by rfl) ⟨290987, by rfl⟩ : syracuseStep 387983 = 581975) B581975
theorem B388025 : Blo 255820 388025 := bstep (se 2 (by rfl) ⟨145509, by rfl⟩ : syracuseStep 388025 = 291019) B291019
theorem B256955 : Blo 255820 256955 := bstep (se 1 (by rfl) ⟨192716, by rfl⟩ : syracuseStep 256955 = 385433) B385433
theorem B289723 : Blo 255820 289723 := bstep (se 1 (by rfl) ⟨217292, by rfl⟩ : syracuseStep 289723 = 434585) B434585
theorem B257031 : Blo 255820 257031 := bstep (se 1 (by rfl) ⟨192773, by rfl⟩ : syracuseStep 257031 = 385547) B385547
theorem B388103 : Blo 255820 388103 := bstep (se 1 (by rfl) ⟨291077, by rfl⟩ : syracuseStep 388103 = 582155) B582155
theorem B257039 : Blo 255820 257039 := bstep (se 1 (by rfl) ⟨192779, by rfl⟩ : syracuseStep 257039 = 385559) B385559
theorem B388139 : Blo 255820 388139 := bstep (se 1 (by rfl) ⟨291104, by rfl⟩ : syracuseStep 388139 = 582209) B582209
theorem B257083 : Blo 255820 257083 := bstep (se 1 (by rfl) ⟨192812, by rfl⟩ : syracuseStep 257083 = 385625) B385625
theorem B388169 : Blo 255820 388169 := bstep (se 2 (by rfl) ⟨145563, by rfl⟩ : syracuseStep 388169 = 291127) B291127
theorem B1305719 : Blo 255820 1305719 := bstep (se 1 (by rfl) ⟨979289, by rfl⟩ : syracuseStep 1305719 = 1958579) B1958579
theorem B257159 : Blo 255820 257159 := bstep (se 1 (by rfl) ⟨192869, by rfl⟩ : syracuseStep 257159 = 385739) B385739
theorem B257167 : Blo 255820 257167 := bstep (se 1 (by rfl) ⟨192875, by rfl⟩ : syracuseStep 257167 = 385751) B385751
theorem B257211 : Blo 255820 257211 := bstep (se 1 (by rfl) ⟨192908, by rfl⟩ : syracuseStep 257211 = 385817) B385817
theorem B388283 : Blo 255820 388283 := bstep (se 1 (by rfl) ⟨291212, by rfl⟩ : syracuseStep 388283 = 582425) B582425
theorem B388343 : Blo 255820 388343 := bstep (se 1 (by rfl) ⟨291257, by rfl⟩ : syracuseStep 388343 = 582515) B582515
theorem B257287 : Blo 255820 257287 := bstep (se 1 (by rfl) ⟨192965, by rfl⟩ : syracuseStep 257287 = 385931) B385931
theorem B257295 : Blo 255820 257295 := bstep (se 1 (by rfl) ⟨192971, by rfl⟩ : syracuseStep 257295 = 385943) B385943
theorem B388367 : Blo 255820 388367 := bstep (se 1 (by rfl) ⟨291275, by rfl⟩ : syracuseStep 388367 = 582551) B582551
theorem B388409 : Blo 255820 388409 := bstep (se 2 (by rfl) ⟨145653, by rfl⟩ : syracuseStep 388409 = 291307) B291307
theorem B257339 : Blo 255820 257339 := bstep (se 1 (by rfl) ⟨193004, by rfl⟩ : syracuseStep 257339 = 386009) B386009
theorem B1240379 : Blo 255820 1240379 := bstep (se 1 (by rfl) ⟨930284, by rfl⟩ : syracuseStep 1240379 = 1860569) B1860569
theorem B257415 : Blo 255820 257415 := bstep (se 1 (by rfl) ⟨193061, by rfl⟩ : syracuseStep 257415 = 386123) B386123
theorem B388487 : Blo 255820 388487 := bstep (se 1 (by rfl) ⟨291365, by rfl⟩ : syracuseStep 388487 = 582731) B582731
theorem B257423 : Blo 255820 257423 := bstep (se 1 (by rfl) ⟨193067, by rfl⟩ : syracuseStep 257423 = 386135) B386135
theorem B290191 : Blo 255820 290191 := bstep (se 1 (by rfl) ⟨217643, by rfl⟩ : syracuseStep 290191 = 435287) B435287
theorem B388523 : Blo 255820 388523 := bstep (se 1 (by rfl) ⟨291392, by rfl⟩ : syracuseStep 388523 = 582785) B582785
theorem B257467 : Blo 255820 257467 := bstep (se 1 (by rfl) ⟨193100, by rfl⟩ : syracuseStep 257467 = 386201) B386201
theorem B388553 : Blo 255820 388553 := bstep (se 2 (by rfl) ⟨145707, by rfl⟩ : syracuseStep 388553 = 291415) B291415
theorem B257543 : Blo 255820 257543 := bstep (se 1 (by rfl) ⟨193157, by rfl⟩ : syracuseStep 257543 = 386315) B386315
theorem B257551 : Blo 255820 257551 := bstep (se 1 (by rfl) ⟨193163, by rfl⟩ : syracuseStep 257551 = 386327) B386327
theorem B257595 : Blo 255820 257595 := bstep (se 1 (by rfl) ⟨193196, by rfl⟩ : syracuseStep 257595 = 386393) B386393
theorem B388667 : Blo 255820 388667 := bstep (se 1 (by rfl) ⟨291500, by rfl⟩ : syracuseStep 388667 = 583001) B583001
theorem B388727 : Blo 255820 388727 := bstep (se 1 (by rfl) ⟨291545, by rfl⟩ : syracuseStep 388727 = 583091) B583091
theorem B257671 : Blo 255820 257671 := bstep (se 1 (by rfl) ⟨193253, by rfl⟩ : syracuseStep 257671 = 386507) B386507
theorem B257679 : Blo 255820 257679 := bstep (se 1 (by rfl) ⟨193259, by rfl⟩ : syracuseStep 257679 = 386519) B386519
theorem B388751 : Blo 255820 388751 := bstep (se 1 (by rfl) ⟨291563, by rfl⟩ : syracuseStep 388751 = 583127) B583127
theorem B388793 : Blo 255820 388793 := bstep (se 2 (by rfl) ⟨145797, by rfl⟩ : syracuseStep 388793 = 291595) B291595
theorem B257723 : Blo 255820 257723 := bstep (se 1 (by rfl) ⟨193292, by rfl⟩ : syracuseStep 257723 = 386585) B386585
theorem B1601281 : Blo 255820 1601281 := bstep (se 2 (by rfl) ⟨600480, by rfl⟩ : syracuseStep 1601281 = 1200961) B1200961
theorem B257799 : Blo 255820 257799 := bstep (se 1 (by rfl) ⟨193349, by rfl⟩ : syracuseStep 257799 = 386699) B386699
theorem B388871 : Blo 255820 388871 := bstep (se 1 (by rfl) ⟨291653, by rfl⟩ : syracuseStep 388871 = 583307) B583307
theorem B257807 : Blo 255820 257807 := bstep (se 1 (by rfl) ⟨193355, by rfl⟩ : syracuseStep 257807 = 386711) B386711
theorem B388907 : Blo 255820 388907 := bstep (se 1 (by rfl) ⟨291680, by rfl⟩ : syracuseStep 388907 = 583361) B583361
theorem B257851 : Blo 255820 257851 := bstep (se 1 (by rfl) ⟨193388, by rfl⟩ : syracuseStep 257851 = 386777) B386777
theorem B388937 : Blo 255820 388937 := bstep (se 2 (by rfl) ⟨145851, by rfl⟩ : syracuseStep 388937 = 291703) B291703
theorem B257927 : Blo 255820 257927 := bstep (se 1 (by rfl) ⟨193445, by rfl⟩ : syracuseStep 257927 = 386891) B386891
theorem B290695 : Blo 255820 290695 := bstep (se 1 (by rfl) ⟨218021, by rfl⟩ : syracuseStep 290695 = 436043) B436043
theorem B257935 : Blo 255820 257935 := bstep (se 1 (by rfl) ⟨193451, by rfl⟩ : syracuseStep 257935 = 386903) B386903
theorem B257979 : Blo 255820 257979 := bstep (se 1 (by rfl) ⟨193484, by rfl⟩ : syracuseStep 257979 = 386969) B386969
theorem B389051 : Blo 255820 389051 := bstep (se 1 (by rfl) ⟨291788, by rfl⟩ : syracuseStep 389051 = 583577) B583577
theorem B389111 : Blo 255820 389111 := bstep (se 1 (by rfl) ⟨291833, by rfl⟩ : syracuseStep 389111 = 583667) B583667
theorem B258055 : Blo 255820 258055 := bstep (se 1 (by rfl) ⟨193541, by rfl⟩ : syracuseStep 258055 = 387083) B387083
theorem B258063 : Blo 255820 258063 := bstep (se 1 (by rfl) ⟨193547, by rfl⟩ : syracuseStep 258063 = 387095) B387095
theorem B389135 : Blo 255820 389135 := bstep (se 1 (by rfl) ⟨291851, by rfl⟩ : syracuseStep 389135 = 583703) B583703
theorem B389177 : Blo 255820 389177 := bstep (se 2 (by rfl) ⟨145941, by rfl⟩ : syracuseStep 389177 = 291883) B291883
theorem B258107 : Blo 255820 258107 := bstep (se 1 (by rfl) ⟨193580, by rfl⟩ : syracuseStep 258107 = 387161) B387161
theorem B290875 : Blo 255820 290875 := bstep (se 1 (by rfl) ⟨218156, by rfl⟩ : syracuseStep 290875 = 436313) B436313
theorem B1306691 : Blo 255820 1306691 := bstep (se 1 (by rfl) ⟨980018, by rfl⟩ : syracuseStep 1306691 = 1960037) B1960037
theorem B258183 : Blo 255820 258183 := bstep (se 1 (by rfl) ⟨193637, by rfl⟩ : syracuseStep 258183 = 387275) B387275
theorem B389255 : Blo 255820 389255 := bstep (se 1 (by rfl) ⟨291941, by rfl⟩ : syracuseStep 389255 = 583883) B583883
theorem B258191 : Blo 255820 258191 := bstep (se 1 (by rfl) ⟨193643, by rfl⟩ : syracuseStep 258191 = 387287) B387287
theorem B389291 : Blo 255820 389291 := bstep (se 1 (by rfl) ⟨291968, by rfl⟩ : syracuseStep 389291 = 583937) B583937
theorem B258235 : Blo 255820 258235 := bstep (se 1 (by rfl) ⟨193676, by rfl⟩ : syracuseStep 258235 = 387353) B387353
theorem B389321 : Blo 255820 389321 := bstep (se 2 (by rfl) ⟨145995, by rfl⟩ : syracuseStep 389321 = 291991) B291991
theorem B258311 : Blo 255820 258311 := bstep (se 1 (by rfl) ⟨193733, by rfl⟩ : syracuseStep 258311 = 387467) B387467
theorem B258319 : Blo 255820 258319 := bstep (se 1 (by rfl) ⟨193739, by rfl⟩ : syracuseStep 258319 = 387479) B387479
theorem B1470757 : Blo 255820 1470757 := bstep (se 4 (by rfl) ⟨137883, by rfl⟩ : syracuseStep 1470757 = 275767) B275767
theorem B258363 : Blo 255820 258363 := bstep (se 1 (by rfl) ⟨193772, by rfl⟩ : syracuseStep 258363 = 387545) B387545
theorem B389435 : Blo 255820 389435 := bstep (se 1 (by rfl) ⟨292076, by rfl⟩ : syracuseStep 389435 = 584153) B584153
theorem B651635 : Blo 255820 651635 := bstep (se 1 (by rfl) ⟨488726, by rfl⟩ : syracuseStep 651635 = 977453) B977453
theorem B389495 : Blo 255820 389495 := bstep (se 1 (by rfl) ⟨292121, by rfl⟩ : syracuseStep 389495 = 584243) B584243
theorem B1307015 : Blo 255820 1307015 := bstep (se 1 (by rfl) ⟨980261, by rfl⟩ : syracuseStep 1307015 = 1960523) B1960523
theorem B258439 : Blo 255820 258439 := bstep (se 1 (by rfl) ⟨193829, by rfl⟩ : syracuseStep 258439 = 387659) B387659
theorem B258447 : Blo 255820 258447 := bstep (se 1 (by rfl) ⟨193835, by rfl⟩ : syracuseStep 258447 = 387671) B387671
theorem B389519 : Blo 255820 389519 := bstep (se 1 (by rfl) ⟨292139, by rfl⟩ : syracuseStep 389519 = 584279) B584279
theorem B389561 : Blo 255820 389561 := bstep (se 2 (by rfl) ⟨146085, by rfl⟩ : syracuseStep 389561 = 292171) B292171
theorem B258491 : Blo 255820 258491 := bstep (se 1 (by rfl) ⟨193868, by rfl⟩ : syracuseStep 258491 = 387737) B387737
theorem B258567 : Blo 255820 258567 := bstep (se 1 (by rfl) ⟨193925, by rfl⟩ : syracuseStep 258567 = 387851) B387851
theorem B389639 : Blo 255820 389639 := bstep (se 1 (by rfl) ⟨292229, by rfl⟩ : syracuseStep 389639 = 584459) B584459
theorem B258575 : Blo 255820 258575 := bstep (se 1 (by rfl) ⟨193931, by rfl⟩ : syracuseStep 258575 = 387863) B387863
theorem B291343 : Blo 255820 291343 := bstep (se 1 (by rfl) ⟨218507, by rfl⟩ : syracuseStep 291343 = 437015) B437015
theorem B389675 : Blo 255820 389675 := bstep (se 1 (by rfl) ⟨292256, by rfl⟩ : syracuseStep 389675 = 584513) B584513
theorem B258619 : Blo 255820 258619 := bstep (se 1 (by rfl) ⟨193964, by rfl⟩ : syracuseStep 258619 = 387929) B387929
theorem B389705 : Blo 255820 389705 := bstep (se 2 (by rfl) ⟨146139, by rfl⟩ : syracuseStep 389705 = 292279) B292279
theorem B258695 : Blo 255820 258695 := bstep (se 1 (by rfl) ⟨194021, by rfl⟩ : syracuseStep 258695 = 388043) B388043
theorem B258703 : Blo 255820 258703 := bstep (se 1 (by rfl) ⟨194027, by rfl⟩ : syracuseStep 258703 = 388055) B388055
theorem B258747 : Blo 255820 258747 := bstep (se 1 (by rfl) ⟨194060, by rfl⟩ : syracuseStep 258747 = 388121) B388121
theorem B258823 : Blo 255820 258823 := bstep (se 1 (by rfl) ⟨194117, by rfl⟩ : syracuseStep 258823 = 388235) B388235
theorem B258831 : Blo 255820 258831 := bstep (se 1 (by rfl) ⟨194123, by rfl⟩ : syracuseStep 258831 = 388247) B388247
theorem B1471283 : Blo 255820 1471283 := bstep (se 1 (by rfl) ⟨1103462, by rfl⟩ : syracuseStep 1471283 = 2206925) B2206925
theorem B389947 : Blo 255820 389947 := bstep (se 1 (by rfl) ⟨292460, by rfl⟩ : syracuseStep 389947 = 584921) B584921
theorem B258875 : Blo 255820 258875 := bstep (se 1 (by rfl) ⟨194156, by rfl⟩ : syracuseStep 258875 = 388313) B388313
theorem B652151 : Blo 255820 652151 := bstep (se 1 (by rfl) ⟨489113, by rfl⟩ : syracuseStep 652151 = 978227) B978227
theorem B258951 : Blo 255820 258951 := bstep (se 1 (by rfl) ⟨194213, by rfl⟩ : syracuseStep 258951 = 388427) B388427
theorem B258959 : Blo 255820 258959 := bstep (se 1 (by rfl) ⟨194219, by rfl⟩ : syracuseStep 258959 = 388439) B388439
theorem B488339 : Blo 255820 488339 := bstep (se 1 (by rfl) ⟨366254, by rfl⟩ : syracuseStep 488339 = 732509) B732509
theorem B979897 : Blo 255820 979897 := bstep (se 2 (by rfl) ⟨367461, by rfl⟩ : syracuseStep 979897 = 734923) B734923
theorem B259003 : Blo 255820 259003 := bstep (se 1 (by rfl) ⟨194252, by rfl⟩ : syracuseStep 259003 = 388505) B388505
theorem B259079 : Blo 255820 259079 := bstep (se 1 (by rfl) ⟨194309, by rfl⟩ : syracuseStep 259079 = 388619) B388619
theorem B291847 : Blo 255820 291847 := bstep (se 1 (by rfl) ⟨218885, by rfl⟩ : syracuseStep 291847 = 437771) B437771
theorem B259087 : Blo 255820 259087 := bstep (se 1 (by rfl) ⟨194315, by rfl⟩ : syracuseStep 259087 = 388631) B388631
theorem B259131 : Blo 255820 259131 := bstep (se 1 (by rfl) ⟨194348, by rfl⟩ : syracuseStep 259131 = 388697) B388697
theorem B488567 : Blo 255820 488567 := bstep (se 1 (by rfl) ⟨366425, by rfl⟩ : syracuseStep 488567 = 732851) B732851
theorem B259207 : Blo 255820 259207 := bstep (se 1 (by rfl) ⟨194405, by rfl⟩ : syracuseStep 259207 = 388811) B388811
theorem B259215 : Blo 255820 259215 := bstep (se 1 (by rfl) ⟨194411, by rfl⟩ : syracuseStep 259215 = 388823) B388823
theorem B554131 : Blo 255820 554131 := bstep (se 1 (by rfl) ⟨415598, by rfl⟩ : syracuseStep 554131 = 831197) B831197
theorem B259259 : Blo 255820 259259 := bstep (se 1 (by rfl) ⟨194444, by rfl⟩ : syracuseStep 259259 = 388889) B388889
theorem B292027 : Blo 255820 292027 := bstep (se 1 (by rfl) ⟨219020, by rfl⟩ : syracuseStep 292027 = 438041) B438041
theorem B259335 : Blo 255820 259335 := bstep (se 1 (by rfl) ⟨194501, by rfl⟩ : syracuseStep 259335 = 389003) B389003
theorem B259343 : Blo 255820 259343 := bstep (se 1 (by rfl) ⟨194507, by rfl⟩ : syracuseStep 259343 = 389015) B389015
theorem B390457 : Blo 255820 390457 := bstep (se 2 (by rfl) ⟨146421, by rfl⟩ : syracuseStep 390457 = 292843) B292843
theorem B259387 : Blo 255820 259387 := bstep (se 1 (by rfl) ⟨194540, by rfl⟩ : syracuseStep 259387 = 389081) B389081
theorem B882035 : Blo 255820 882035 := bstep (se 1 (by rfl) ⟨661526, by rfl⟩ : syracuseStep 882035 = 1323053) B1323053
theorem B259463 : Blo 255820 259463 := bstep (se 1 (by rfl) ⟨194597, by rfl⟩ : syracuseStep 259463 = 389195) B389195
theorem B259471 : Blo 255820 259471 := bstep (se 1 (by rfl) ⟨194603, by rfl⟩ : syracuseStep 259471 = 389207) B389207
theorem B259515 : Blo 255820 259515 := bstep (se 1 (by rfl) ⟨194636, by rfl⟩ : syracuseStep 259515 = 389273) B389273
theorem B259591 : Blo 255820 259591 := bstep (se 1 (by rfl) ⟨194693, by rfl⟩ : syracuseStep 259591 = 389387) B389387
theorem B259599 : Blo 255820 259599 := bstep (se 1 (by rfl) ⟨194699, by rfl⟩ : syracuseStep 259599 = 389399) B389399
theorem B259643 : Blo 255820 259643 := bstep (se 1 (by rfl) ⟨194732, by rfl⟩ : syracuseStep 259643 = 389465) B389465
theorem B3995237 : Blo 255820 3995237 := bstep (se 4 (by rfl) ⟨374553, by rfl⟩ : syracuseStep 3995237 = 749107) B749107
theorem B259719 : Blo 255820 259719 := bstep (se 1 (by rfl) ⟨194789, by rfl⟩ : syracuseStep 259719 = 389579) B389579
theorem B259727 : Blo 255820 259727 := bstep (se 1 (by rfl) ⟨194795, by rfl⟩ : syracuseStep 259727 = 389591) B389591
theorem B325291 : Blo 255820 325291 := bstep (se 1 (by rfl) ⟨243968, by rfl⟩ : syracuseStep 325291 = 487937) B487937
theorem B259771 : Blo 255820 259771 := bstep (se 1 (by rfl) ⟨194828, by rfl⟩ : syracuseStep 259771 = 389657) B389657
theorem B390955 : Blo 255820 390955 := bstep (se 1 (by rfl) ⟨293216, by rfl⟩ : syracuseStep 390955 = 586433) B586433
theorem B653143 : Blo 255820 653143 := bstep (se 1 (by rfl) ⟨489857, by rfl⟩ : syracuseStep 653143 = 979715) B979715
theorem B292879 : Blo 255820 292879 := bstep (se 1 (by rfl) ⟨219659, by rfl⟩ : syracuseStep 292879 = 439319) B439319
theorem B292999 : Blo 255820 292999 := bstep (se 1 (by rfl) ⟨219749, by rfl⟩ : syracuseStep 292999 = 439499) B439499
theorem B587911 : Blo 255820 587911 := bstep (se 1 (by rfl) ⟨440933, by rfl⟩ : syracuseStep 587911 = 881867) B881867
theorem B653447 : Blo 255820 653447 := bstep (se 1 (by rfl) ⟨490085, by rfl⟩ : syracuseStep 653447 = 980171) B980171
theorem B9959597 : Blo 255820 9959597 := bstep (se 3 (by rfl) ⟨1867424, by rfl⟩ : syracuseStep 9959597 = 3734849) B3734849
theorem B522425 : Blo 255820 522425 := bstep (se 2 (by rfl) ⟨195909, by rfl⟩ : syracuseStep 522425 = 391819) B391819
theorem B1472741 : Blo 255820 1472741 := bstep (se 4 (by rfl) ⟨138069, by rfl⟩ : syracuseStep 1472741 = 276139) B276139
theorem B2914541 : Blo 255820 2914541 := bstep (se 3 (by rfl) ⟨546476, by rfl⟩ : syracuseStep 2914541 = 1092953) B1092953
theorem B653579 : Blo 255820 653579 := bstep (se 1 (by rfl) ⟨490184, by rfl⟩ : syracuseStep 653579 = 980369) B980369
theorem B391625 : Blo 255820 391625 := bstep (se 2 (by rfl) ⟨146859, by rfl⟩ : syracuseStep 391625 = 293719) B293719
theorem B1178155 : Blo 255820 1178155 := bstep (se 1 (by rfl) ⟨883616, by rfl⟩ : syracuseStep 1178155 = 1767233) B1767233
theorem B326263 : Blo 255820 326263 := bstep (se 1 (by rfl) ⟨244697, by rfl⟩ : syracuseStep 326263 = 489395) B489395
theorem B621323 : Blo 255820 621323 := bstep (se 1 (by rfl) ⟨465992, by rfl⟩ : syracuseStep 621323 = 931985) B931985
theorem B654095 : Blo 255820 654095 := bstep (se 1 (by rfl) ⟨490571, by rfl⟩ : syracuseStep 654095 = 981143) B981143
theorem B490283 : Blo 255820 490283 := bstep (se 1 (by rfl) ⟨367712, by rfl⟩ : syracuseStep 490283 = 735425) B735425
theorem B654227 : Blo 255820 654227 := bstep (se 1 (by rfl) ⟨490670, by rfl⟩ : syracuseStep 654227 = 981341) B981341
theorem B326587 : Blo 255820 326587 := bstep (se 1 (by rfl) ⟨244940, by rfl⟩ : syracuseStep 326587 = 489881) B489881
theorem B490511 : Blo 255820 490511 := bstep (se 1 (by rfl) ⟨367883, by rfl⟩ : syracuseStep 490511 = 735767) B735767
theorem B1670381 : Blo 255820 1670381 := bstep (se 3 (by rfl) ⟨313196, by rfl⟩ : syracuseStep 1670381 = 626393) B626393
theorem B2195201 : Blo 255820 2195201 := bstep (se 2 (by rfl) ⟨823200, by rfl⟩ : syracuseStep 2195201 = 1646401) B1646401
theorem B982799 : Blo 255820 982799 := bstep (se 1 (by rfl) ⟨737099, by rfl⟩ : syracuseStep 982799 = 1474199) B1474199
theorem B1310579 : Blo 255820 1310579 := bstep (se 1 (by rfl) ⟨982934, by rfl⟩ : syracuseStep 1310579 = 1965869) B1965869
theorem B327559 : Blo 255820 327559 := bstep (se 1 (by rfl) ⟨245669, by rfl⟩ : syracuseStep 327559 = 491339) B491339
theorem B5898269 : Blo 255820 5898269 := bstep (se 3 (by rfl) ⟨1105925, by rfl⟩ : syracuseStep 5898269 = 2211851) B2211851
theorem B1245451 : Blo 255820 1245451 := bstep (se 1 (by rfl) ⟨934088, by rfl⟩ : syracuseStep 1245451 = 1868177) B1868177
theorem B1868093 : Blo 255820 1868093 := bstep (se 3 (by rfl) ⟨350267, by rfl⟩ : syracuseStep 1868093 = 700535) B700535
theorem B655897 : Blo 255820 655897 := bstep (se 2 (by rfl) ⟨245961, by rfl⟩ : syracuseStep 655897 = 491923) B491923
theorem B1475131 : Blo 255820 1475131 := bstep (se 1 (by rfl) ⟨1106348, by rfl⟩ : syracuseStep 1475131 = 2212697) B2212697
theorem B656201 : Blo 255820 656201 := bstep (se 2 (by rfl) ⟨246075, by rfl⟩ : syracuseStep 656201 = 492151) B492151
theorem B328555 : Blo 255820 328555 := bstep (se 1 (by rfl) ⟨246416, by rfl⟩ : syracuseStep 328555 = 492833) B492833
theorem B6587243 : Blo 255820 6587243 := bstep (se 1 (by rfl) ⟨4940432, by rfl⟩ : syracuseStep 6587243 = 9880865) B9880865
theorem B1574083 : Blo 255820 1574083 := bstep (se 1 (by rfl) ⟨1180562, by rfl⟩ : syracuseStep 1574083 = 2361125) B2361125
theorem B492743 : Blo 255820 492743 := bstep (se 1 (by rfl) ⟨369557, by rfl⟩ : syracuseStep 492743 = 739115) B739115
theorem B492895 : Blo 255820 492895 := bstep (se 1 (by rfl) ⟨369671, by rfl⟩ : syracuseStep 492895 = 739343) B739343
theorem B1181147 : Blo 255820 1181147 := bstep (se 1 (by rfl) ⟨885860, by rfl⟩ : syracuseStep 1181147 = 1771721) B1771721
theorem B624167 : Blo 255820 624167 := bstep (se 1 (by rfl) ⟨468125, by rfl⟩ : syracuseStep 624167 = 936251) B936251
theorem B657335 : Blo 255820 657335 := bstep (se 1 (by rfl) ⟨493001, by rfl⟩ : syracuseStep 657335 = 986003) B986003
theorem B1345921 : Blo 255820 1345921 := bstep (se 2 (by rfl) ⟨504720, by rfl⟩ : syracuseStep 1345921 = 1009441) B1009441
theorem B1640969 : Blo 255820 1640969 := bstep (se 2 (by rfl) ⟨615363, by rfl⟩ : syracuseStep 1640969 = 1230727) B1230727
theorem B1870775 : Blo 255820 1870775 := bstep (se 1 (by rfl) ⟨1403081, by rfl⟩ : syracuseStep 1870775 = 2806163) B2806163
theorem B1051663 : Blo 255820 1051663 := bstep (se 1 (by rfl) ⟨788747, by rfl⟩ : syracuseStep 1051663 = 1577495) B1577495
theorem B1969271 : Blo 255820 1969271 := bstep (se 1 (by rfl) ⟨1476953, by rfl⟩ : syracuseStep 1969271 = 2953907) B2953907
theorem B462071 : Blo 255820 462071 := bstep (se 1 (by rfl) ⟨346553, by rfl⟩ : syracuseStep 462071 = 693107) B693107
theorem B3509725 : Blo 255820 3509725 := bstep (se 3 (by rfl) ⟨658073, by rfl⟩ : syracuseStep 3509725 = 1316147) B1316147
theorem B3149435 : Blo 255820 3149435 := bstep (se 1 (by rfl) ⟨2362076, by rfl⟩ : syracuseStep 3149435 = 4724153) B4724153
theorem B3968635 : Blo 255820 3968635 := bstep (se 1 (by rfl) ⟨2976476, by rfl⟩ : syracuseStep 3968635 = 5952953) B5952953
theorem B462547 : Blo 255820 462547 := bstep (se 1 (by rfl) ⟨346910, by rfl⟩ : syracuseStep 462547 = 693821) B693821
theorem B4034285 : Blo 255820 4034285 := bstep (se 3 (by rfl) ⟨756428, by rfl⟩ : syracuseStep 4034285 = 1512857) B1512857
theorem B692155 : Blo 255820 692155 := bstep (se 1 (by rfl) ⟨519116, by rfl⟩ : syracuseStep 692155 = 1038233) B1038233
theorem B692231 : Blo 255820 692231 := bstep (se 1 (by rfl) ⟨519173, by rfl⟩ : syracuseStep 692231 = 1038347) B1038347
theorem B4166417 : Blo 255820 4166417 := bstep (se 2 (by rfl) ⟨1562406, by rfl⟩ : syracuseStep 4166417 = 3124813) B3124813
theorem B2135041 : Blo 255820 2135041 := bstep (se 2 (by rfl) ⟨800640, by rfl⟩ : syracuseStep 2135041 = 1601281) B1601281
theorem B3150899 : Blo 255820 3150899 := bstep (se 1 (by rfl) ⟨2363174, by rfl⟩ : syracuseStep 3150899 = 4726349) B4726349
theorem B3118297 : Blo 255820 3118297 := bstep (se 2 (by rfl) ⟨1169361, by rfl⟩ : syracuseStep 3118297 = 2338723) B2338723
theorem B464393 : Blo 255820 464393 := bstep (se 2 (by rfl) ⟨174147, by rfl⟩ : syracuseStep 464393 = 348295) B348295
theorem B497513 : Blo 255820 497513 := bstep (se 2 (by rfl) ⟨186567, by rfl⟩ : syracuseStep 497513 = 373135) B373135
theorem B432047 : Blo 255820 432047 := bstep (se 1 (by rfl) ⟨324035, by rfl⟩ : syracuseStep 432047 = 648071) B648071
theorem B2988035 : Blo 255820 2988035 := bstep (se 1 (by rfl) ⟨2241026, by rfl⟩ : syracuseStep 2988035 = 4482053) B4482053
theorem B2955365 : Blo 255820 2955365 := bstep (se 4 (by rfl) ⟨277065, by rfl⟩ : syracuseStep 2955365 = 554131) B554131
theorem B825661 : Blo 255820 825661 := bstep (se 3 (by rfl) ⟨154811, by rfl⟩ : syracuseStep 825661 = 309623) B309623
theorem B432479 : Blo 255820 432479 := bstep (se 1 (by rfl) ⟨324359, by rfl⟩ : syracuseStep 432479 = 648719) B648719
theorem B3545633 : Blo 255820 3545633 := bstep (se 2 (by rfl) ⟨1329612, by rfl⟩ : syracuseStep 3545633 = 2659225) B2659225
theorem B367183 : Blo 255820 367183 := bstep (se 1 (by rfl) ⟨275387, by rfl⟩ : syracuseStep 367183 = 550775) B550775
theorem B433039 : Blo 255820 433039 := bstep (se 1 (by rfl) ⟨324779, by rfl⟩ : syracuseStep 433039 = 649559) B649559
theorem B2202551 : Blo 255820 2202551 := bstep (se 1 (by rfl) ⟨1651913, by rfl⟩ : syracuseStep 2202551 = 3303827) B3303827
theorem B1186987 : Blo 255820 1186987 := bstep (se 1 (by rfl) ⟨890240, by rfl⟩ : syracuseStep 1186987 = 1780481) B1780481
theorem B826919 : Blo 255820 826919 := bstep (se 1 (by rfl) ⟨620189, by rfl⟩ : syracuseStep 826919 = 1240379) B1240379
theorem B433721 : Blo 255820 433721 := bstep (se 2 (by rfl) ⟨162645, by rfl⟩ : syracuseStep 433721 = 325291) B325291
theorem B2367299 : Blo 255820 2367299 := bstep (se 1 (by rfl) ⟨1775474, by rfl⟩ : syracuseStep 2367299 = 3550949) B3550949
theorem B434423 : Blo 255820 434423 := bstep (se 1 (by rfl) ⟨325817, by rfl⟩ : syracuseStep 434423 = 651635) B651635
theorem B1417753 : Blo 255820 1417753 := bstep (se 2 (by rfl) ⟨531657, by rfl⟩ : syracuseStep 1417753 = 1063315) B1063315
theorem B434767 : Blo 255820 434767 := bstep (se 1 (by rfl) ⟨326075, by rfl⟩ : syracuseStep 434767 = 652151) B652151
theorem B435017 : Blo 255820 435017 := bstep (se 2 (by rfl) ⟨163131, by rfl⟩ : syracuseStep 435017 = 326263) B326263
theorem B2663491 : Blo 255820 2663491 := bstep (se 1 (by rfl) ⟨1997618, by rfl⟩ : syracuseStep 2663491 = 3995237) B3995237
theorem B435449 : Blo 255820 435449 := bstep (se 2 (by rfl) ⟨163293, by rfl⟩ : syracuseStep 435449 = 326587) B326587
theorem B435631 : Blo 255820 435631 := bstep (se 1 (by rfl) ⟨326723, by rfl⟩ : syracuseStep 435631 = 653447) B653447
theorem B1943027 : Blo 255820 1943027 := bstep (se 1 (by rfl) ⟨1457270, by rfl⟩ : syracuseStep 1943027 = 2914541) B2914541
theorem B435719 : Blo 255820 435719 := bstep (se 1 (by rfl) ⟨326789, by rfl⟩ : syracuseStep 435719 = 653579) B653579
theorem B730721 : Blo 255820 730721 := bstep (se 2 (by rfl) ⟨274020, by rfl⟩ : syracuseStep 730721 = 548041) B548041
theorem B1648451 : Blo 255820 1648451 := bstep (se 1 (by rfl) ⟨1236338, by rfl⟩ : syracuseStep 1648451 = 2472677) B2472677
theorem B436063 : Blo 255820 436063 := bstep (se 1 (by rfl) ⟨327047, by rfl⟩ : syracuseStep 436063 = 654095) B654095
theorem B436151 : Blo 255820 436151 := bstep (se 1 (by rfl) ⟨327113, by rfl⟩ : syracuseStep 436151 = 654227) B654227
theorem B2664485 : Blo 255820 2664485 := bstep (se 4 (by rfl) ⟨249795, by rfl⟩ : syracuseStep 2664485 = 499591) B499591
theorem B436745 : Blo 255820 436745 := bstep (se 2 (by rfl) ⟨163779, by rfl⟩ : syracuseStep 436745 = 327559) B327559
theorem B436907 : Blo 255820 436907 := bstep (se 1 (by rfl) ⟨327680, by rfl⟩ : syracuseStep 436907 = 655361) B655361
theorem B732179 : Blo 255820 732179 := bstep (se 1 (by rfl) ⟨549134, by rfl⟩ : syracuseStep 732179 = 1098269) B1098269
theorem B437305 : Blo 255820 437305 := bstep (se 2 (by rfl) ⟨163989, by rfl⟩ : syracuseStep 437305 = 327979) B327979
theorem B437447 : Blo 255820 437447 := bstep (se 1 (by rfl) ⟨328085, by rfl⟩ : syracuseStep 437447 = 656171) B656171
theorem B929015 : Blo 255820 929015 := bstep (se 1 (by rfl) ⟨696761, by rfl⟩ : syracuseStep 929015 = 1393523) B1393523
theorem B830711 : Blo 255820 830711 := bstep (se 1 (by rfl) ⟨623033, by rfl⟩ : syracuseStep 830711 = 1246067) B1246067
theorem B4435235 : Blo 255820 4435235 := bstep (se 1 (by rfl) ⟨3326426, by rfl⟩ : syracuseStep 4435235 = 6652853) B6652853
theorem B437609 : Blo 255820 437609 := bstep (se 2 (by rfl) ⟨164103, by rfl⟩ : syracuseStep 437609 = 328207) B328207
theorem B732635 : Blo 255820 732635 := bstep (se 1 (by rfl) ⟨549476, by rfl⟩ : syracuseStep 732635 = 1098953) B1098953
theorem B863783 : Blo 255820 863783 := bstep (se 1 (by rfl) ⟨647837, by rfl⟩ : syracuseStep 863783 = 1295675) B1295675
theorem B863891 : Blo 255820 863891 := bstep (se 1 (by rfl) ⟨647918, by rfl⟩ : syracuseStep 863891 = 1295837) B1295837
theorem B438007 : Blo 255820 438007 := bstep (se 1 (by rfl) ⟨328505, by rfl⟩ : syracuseStep 438007 = 657011) B657011
theorem B864107 : Blo 255820 864107 := bstep (se 1 (by rfl) ⟨648080, by rfl⟩ : syracuseStep 864107 = 1296161) B1296161
theorem B864161 : Blo 255820 864161 := bstep (se 2 (by rfl) ⟨324060, by rfl⟩ : syracuseStep 864161 = 648121) B648121
theorem B1421243 : Blo 255820 1421243 := bstep (se 1 (by rfl) ⟨1065932, by rfl⟩ : syracuseStep 1421243 = 2131865) B2131865
theorem B438203 : Blo 255820 438203 := bstep (se 1 (by rfl) ⟨328652, by rfl⟩ : syracuseStep 438203 = 657305) B657305
theorem B471079 : Blo 255820 471079 := bstep (se 1 (by rfl) ⟨353309, by rfl⟩ : syracuseStep 471079 = 706619) B706619
theorem B438311 : Blo 255820 438311 := bstep (se 1 (by rfl) ⟨328733, by rfl⟩ : syracuseStep 438311 = 657467) B657467
theorem B3321917 : Blo 255820 3321917 := bstep (se 3 (by rfl) ⟨622859, by rfl⟩ : syracuseStep 3321917 = 1245719) B1245719
theorem B438443 : Blo 255820 438443 := bstep (se 1 (by rfl) ⟨328832, by rfl⟩ : syracuseStep 438443 = 657665) B657665
theorem B438601 : Blo 255820 438601 := bstep (se 2 (by rfl) ⟨164475, by rfl⟩ : syracuseStep 438601 = 328951) B328951
theorem B1945943 : Blo 255820 1945943 := bstep (se 1 (by rfl) ⟨1459457, by rfl⟩ : syracuseStep 1945943 = 2918915) B2918915
theorem B864755 : Blo 255820 864755 := bstep (se 1 (by rfl) ⟨648566, by rfl⟩ : syracuseStep 864755 = 1297133) B1297133
theorem B2470459 : Blo 255820 2470459 := bstep (se 1 (by rfl) ⟨1852844, by rfl⟩ : syracuseStep 2470459 = 3705689) B3705689
theorem B766561 : Blo 255820 766561 := bstep (se 2 (by rfl) ⟨287460, by rfl⟩ : syracuseStep 766561 = 574921) B574921
theorem B733819 : Blo 255820 733819 := bstep (se 1 (by rfl) ⟨550364, by rfl⟩ : syracuseStep 733819 = 1100729) B1100729
theorem B832351 : Blo 255820 832351 := bstep (se 1 (by rfl) ⟨624263, by rfl⟩ : syracuseStep 832351 = 1248527) B1248527
theorem B308143 : Blo 255820 308143 := bstep (se 1 (by rfl) ⟨231107, by rfl⟩ : syracuseStep 308143 = 462215) B462215
theorem B865295 : Blo 255820 865295 := bstep (se 1 (by rfl) ⟨648971, by rfl⟩ : syracuseStep 865295 = 1297943) B1297943
theorem B1094903 : Blo 255820 1094903 := bstep (se 1 (by rfl) ⟨821177, by rfl⟩ : syracuseStep 1094903 = 1642355) B1642355
theorem B275887 : Blo 255820 275887 := bstep (se 1 (by rfl) ⟨206915, by rfl⟩ : syracuseStep 275887 = 413831) B413831
theorem B865889 : Blo 255820 865889 := bstep (se 2 (by rfl) ⟨324708, by rfl⟩ : syracuseStep 865889 = 649417) B649417
theorem B440057 : Blo 255820 440057 := bstep (se 2 (by rfl) ⟨165021, by rfl⟩ : syracuseStep 440057 = 330043) B330043
theorem B734969 : Blo 255820 734969 := bstep (se 2 (by rfl) ⟨275613, by rfl⟩ : syracuseStep 734969 = 551227) B551227
theorem B735151 : Blo 255820 735151 := bstep (se 1 (by rfl) ⟨551363, by rfl⟩ : syracuseStep 735151 = 1102727) B1102727
theorem B5027789 : Blo 255820 5027789 := bstep (se 3 (by rfl) ⟨942710, by rfl⟩ : syracuseStep 5027789 = 1885421) B1885421
theorem B735311 : Blo 255820 735311 := bstep (se 1 (by rfl) ⟨551483, by rfl⟩ : syracuseStep 735311 = 1102967) B1102967
theorem B3291677 : Blo 255820 3291677 := bstep (se 3 (by rfl) ⟨617189, by rfl⟩ : syracuseStep 3291677 = 1234379) B1234379
theorem B14989859 : Blo 255820 14989859 := bstep (se 1 (by rfl) ⟨11242394, by rfl⟩ : syracuseStep 14989859 = 22484789) B22484789
theorem B3980215 : Blo 255820 3980215 := bstep (se 1 (by rfl) ⟨2985161, by rfl⟩ : syracuseStep 3980215 = 5970323) B5970323
theorem B867347 : Blo 255820 867347 := bstep (se 1 (by rfl) ⟨650510, by rfl⟩ : syracuseStep 867347 = 1301021) B1301021
theorem B736427 : Blo 255820 736427 := bstep (se 1 (by rfl) ⟨552320, by rfl⟩ : syracuseStep 736427 = 1104641) B1104641
theorem B3980461 : Blo 255820 3980461 := bstep (se 3 (by rfl) ⟨746336, by rfl⟩ : syracuseStep 3980461 = 1492673) B1492673
theorem B1850647 : Blo 255820 1850647 := bstep (se 1 (by rfl) ⟨1387985, by rfl⟩ : syracuseStep 1850647 = 2775971) B2775971
theorem B867671 : Blo 255820 867671 := bstep (se 1 (by rfl) ⟨650753, by rfl⟩ : syracuseStep 867671 = 1301507) B1301507
theorem B933815 : Blo 255820 933815 := bstep (se 1 (by rfl) ⟨700361, by rfl⟩ : syracuseStep 933815 = 1400723) B1400723
theorem B1097995 : Blo 255820 1097995 := bstep (se 1 (by rfl) ⟨823496, by rfl⟩ : syracuseStep 1097995 = 1646993) B1646993
theorem B868751 : Blo 255820 868751 := bstep (se 1 (by rfl) ⟨651563, by rfl⟩ : syracuseStep 868751 = 1303127) B1303127
theorem B311887 : Blo 255820 311887 := bstep (se 1 (by rfl) ⟨233915, by rfl⟩ : syracuseStep 311887 = 467831) B467831
theorem B934523 : Blo 255820 934523 := bstep (se 1 (by rfl) ⟨700892, by rfl⟩ : syracuseStep 934523 = 1401785) B1401785
theorem B869075 : Blo 255820 869075 := bstep (se 1 (by rfl) ⟨651806, by rfl⟩ : syracuseStep 869075 = 1303613) B1303613
theorem B1295513 : Blo 255820 1295513 := bstep (se 2 (by rfl) ⟨485817, by rfl⟩ : syracuseStep 1295513 = 971635) B971635
theorem B2082401 : Blo 255820 2082401 := bstep (se 2 (by rfl) ⟨780900, by rfl⟩ : syracuseStep 2082401 = 1561801) B1561801
theorem B870263 : Blo 255820 870263 := bstep (se 1 (by rfl) ⟨652697, by rfl⟩ : syracuseStep 870263 = 1305395) B1305395
theorem B870479 : Blo 255820 870479 := bstep (se 1 (by rfl) ⟨652859, by rfl⟩ : syracuseStep 870479 = 1305719) B1305719
theorem B1067393 : Blo 255820 1067393 := bstep (se 2 (by rfl) ⟨400272, by rfl⟩ : syracuseStep 1067393 = 800545) B800545
theorem B3295673 : Blo 255820 3295673 := bstep (se 2 (by rfl) ⟨1235877, by rfl⟩ : syracuseStep 3295673 = 2471755) B2471755
theorem B870857 : Blo 255820 870857 := bstep (se 2 (by rfl) ⟨326571, by rfl⟩ : syracuseStep 870857 = 653143) B653143
theorem B575963 : Blo 255820 575963 := bstep (se 1 (by rfl) ⟨431972, by rfl⟩ : syracuseStep 575963 = 863945) B863945
theorem B871127 : Blo 255820 871127 := bstep (se 1 (by rfl) ⟨653345, by rfl⟩ : syracuseStep 871127 = 1306691) B1306691
theorem B576431 : Blo 255820 576431 := bstep (se 1 (by rfl) ⟨432323, by rfl⟩ : syracuseStep 576431 = 864647) B864647
theorem B871343 : Blo 255820 871343 := bstep (se 1 (by rfl) ⟨653507, by rfl⟩ : syracuseStep 871343 = 1307015) B1307015
theorem B576683 : Blo 255820 576683 := bstep (se 1 (by rfl) ⟨432512, by rfl⟩ : syracuseStep 576683 = 865025) B865025
theorem B1756811 : Blo 255820 1756811 := bstep (se 1 (by rfl) ⟨1317608, by rfl⟩ : syracuseStep 1756811 = 2635217) B2635217
theorem B577223 : Blo 255820 577223 := bstep (se 1 (by rfl) ⟨432917, by rfl⟩ : syracuseStep 577223 = 865835) B865835
theorem B1462009 : Blo 255820 1462009 := bstep (se 2 (by rfl) ⟨548253, by rfl⟩ : syracuseStep 1462009 = 1096507) B1096507
theorem B413753 : Blo 255820 413753 := bstep (se 2 (by rfl) ⟨155157, by rfl⟩ : syracuseStep 413753 = 310315) B310315
theorem B6639731 : Blo 255820 6639731 := bstep (se 1 (by rfl) ⟨4979798, by rfl⟩ : syracuseStep 6639731 = 9959597) B9959597
theorem B348283 : Blo 255820 348283 := bstep (se 1 (by rfl) ⟨261212, by rfl⟩ : syracuseStep 348283 = 522425) B522425
theorem B2216321 : Blo 255820 2216321 := bstep (se 2 (by rfl) ⟨831120, by rfl⟩ : syracuseStep 2216321 = 1662241) B1662241
theorem B1331585 : Blo 255820 1331585 := bstep (se 2 (by rfl) ⟨499344, by rfl⟩ : syracuseStep 1331585 = 998689) B998689
theorem B414215 : Blo 255820 414215 := bstep (se 1 (by rfl) ⟨310661, by rfl⟩ : syracuseStep 414215 = 621323) B621323
theorem B1102369 : Blo 255820 1102369 := bstep (se 2 (by rfl) ⟨413388, by rfl⟩ : syracuseStep 1102369 = 826777) B826777
theorem B578087 : Blo 255820 578087 := bstep (se 1 (by rfl) ⟨433565, by rfl⟩ : syracuseStep 578087 = 867131) B867131
theorem B971453 : Blo 255820 971453 := bstep (se 3 (by rfl) ⟨182147, by rfl⟩ : syracuseStep 971453 = 364295) B364295
theorem B578411 : Blo 255820 578411 := bstep (se 1 (by rfl) ⟨433808, by rfl⟩ : syracuseStep 578411 = 867617) B867617
theorem B578465 : Blo 255820 578465 := bstep (se 2 (by rfl) ⟨216924, by rfl⟩ : syracuseStep 578465 = 433849) B433849
theorem B1168303 : Blo 255820 1168303 := bstep (se 1 (by rfl) ⟨876227, by rfl⟩ : syracuseStep 1168303 = 1752455) B1752455
theorem B2249693 : Blo 255820 2249693 := bstep (se 3 (by rfl) ⟨421817, by rfl⟩ : syracuseStep 2249693 = 843635) B843635
theorem B1463467 : Blo 255820 1463467 := bstep (se 1 (by rfl) ⟨1097600, by rfl⟩ : syracuseStep 1463467 = 2195201) B2195201
theorem B578807 : Blo 255820 578807 := bstep (se 1 (by rfl) ⟨434105, by rfl⟩ : syracuseStep 578807 = 868211) B868211
theorem B873719 : Blo 255820 873719 := bstep (se 1 (by rfl) ⟨655289, by rfl⟩ : syracuseStep 873719 = 1310579) B1310579
theorem B415163 : Blo 255820 415163 := bstep (se 1 (by rfl) ⟨311372, by rfl⟩ : syracuseStep 415163 = 622745) B622745
theorem B349705 : Blo 255820 349705 := bstep (se 2 (by rfl) ⟨131139, by rfl⟩ : syracuseStep 349705 = 262279) B262279
theorem B874043 : Blo 255820 874043 := bstep (se 1 (by rfl) ⟨655532, by rfl⟩ : syracuseStep 874043 = 1311065) B1311065
theorem B546401 : Blo 255820 546401 := bstep (se 2 (by rfl) ⟨204900, by rfl⟩ : syracuseStep 546401 = 409801) B409801
theorem B1398493 : Blo 255820 1398493 := bstep (se 3 (by rfl) ⟨262217, by rfl⟩ : syracuseStep 1398493 = 524435) B524435
theorem B1070891 : Blo 255820 1070891 := bstep (se 1 (by rfl) ⟨803168, by rfl⟩ : syracuseStep 1070891 = 1606337) B1606337
theorem B2774843 : Blo 255820 2774843 := bstep (se 1 (by rfl) ⟨2081132, by rfl⟩ : syracuseStep 2774843 = 4162265) B4162265
theorem B579401 : Blo 255820 579401 := bstep (se 2 (by rfl) ⟨217275, by rfl⟩ : syracuseStep 579401 = 434551) B434551
theorem B874313 : Blo 255820 874313 := bstep (se 2 (by rfl) ⟨327867, by rfl⟩ : syracuseStep 874313 = 655735) B655735
theorem B1398647 : Blo 255820 1398647 := bstep (se 1 (by rfl) ⟨1048985, by rfl⟩ : syracuseStep 1398647 = 2097971) B2097971
theorem B546743 : Blo 255820 546743 := bstep (se 1 (by rfl) ⟨410057, by rfl⟩ : syracuseStep 546743 = 820115) B820115
theorem B2086843 : Blo 255820 2086843 := bstep (se 1 (by rfl) ⟨1565132, by rfl⟩ : syracuseStep 2086843 = 3130265) B3130265
theorem B22566869 : Blo 255820 22566869 := bstep (se 7 (by rfl) ⟨264455, by rfl⟩ : syracuseStep 22566869 = 528911) B528911
theorem B972881 : Blo 255820 972881 := bstep (se 2 (by rfl) ⟨364830, by rfl⟩ : syracuseStep 972881 = 729661) B729661
theorem B1235033 : Blo 255820 1235033 := bstep (se 2 (by rfl) ⟨463137, by rfl⟩ : syracuseStep 1235033 = 926275) B926275
theorem B842071 : Blo 255820 842071 := bstep (se 1 (by rfl) ⟨631553, by rfl⟩ : syracuseStep 842071 = 1263107) B1263107
theorem B580193 : Blo 255820 580193 := bstep (se 2 (by rfl) ⟨217572, by rfl⟩ : syracuseStep 580193 = 435145) B435145
theorem B383849 : Blo 255820 383849 := bstep (se 2 (by rfl) ⟨143943, by rfl⟩ : syracuseStep 383849 = 287887) B287887
theorem B383927 : Blo 255820 383927 := bstep (se 1 (by rfl) ⟨287945, by rfl⟩ : syracuseStep 383927 = 575891) B575891
theorem B580535 : Blo 255820 580535 := bstep (se 1 (by rfl) ⟨435401, by rfl⟩ : syracuseStep 580535 = 870803) B870803
theorem B875447 : Blo 255820 875447 := bstep (se 1 (by rfl) ⟨656585, by rfl⟩ : syracuseStep 875447 = 1313171) B1313171
theorem B383963 : Blo 255820 383963 := bstep (se 1 (by rfl) ⟨287972, by rfl⟩ : syracuseStep 383963 = 575945) B575945
theorem B384431 : Blo 255820 384431 := bstep (se 1 (by rfl) ⟨288323, by rfl⟩ : syracuseStep 384431 = 576647) B576647
theorem B384521 : Blo 255820 384521 := bstep (se 2 (by rfl) ⟨144195, by rfl⟩ : syracuseStep 384521 = 288391) B288391
theorem B581129 : Blo 255820 581129 := bstep (se 2 (by rfl) ⟨217923, by rfl⟩ : syracuseStep 581129 = 435847) B435847
theorem B876041 : Blo 255820 876041 := bstep (se 2 (by rfl) ⟨328515, by rfl⟩ : syracuseStep 876041 = 657031) B657031
theorem B974369 : Blo 255820 974369 := bstep (se 2 (by rfl) ⟨365388, by rfl⟩ : syracuseStep 974369 = 730777) B730777
theorem B384551 : Blo 255820 384551 := bstep (se 1 (by rfl) ⟨288413, by rfl⟩ : syracuseStep 384551 = 576827) B576827
theorem B384635 : Blo 255820 384635 := bstep (se 1 (by rfl) ⟨288476, by rfl⟩ : syracuseStep 384635 = 576953) B576953
theorem B1302155 : Blo 255820 1302155 := bstep (se 1 (by rfl) ⟨976616, by rfl⟩ : syracuseStep 1302155 = 1953233) B1953233
theorem B974551 : Blo 255820 974551 := bstep (se 1 (by rfl) ⟨730913, by rfl⟩ : syracuseStep 974551 = 1461827) B1461827
theorem B384761 : Blo 255820 384761 := bstep (se 2 (by rfl) ⟨144285, by rfl⟩ : syracuseStep 384761 = 288571) B288571
theorem B384863 : Blo 255820 384863 := bstep (se 1 (by rfl) ⟨288647, by rfl⟩ : syracuseStep 384863 = 577295) B577295
theorem B581471 : Blo 255820 581471 := bstep (se 1 (by rfl) ⟨436103, by rfl⟩ : syracuseStep 581471 = 872207) B872207
theorem B384875 : Blo 255820 384875 := bstep (se 1 (by rfl) ⟨288656, by rfl⟩ : syracuseStep 384875 = 577313) B577313
theorem B974855 : Blo 255820 974855 := bstep (se 1 (by rfl) ⟨731141, by rfl⟩ : syracuseStep 974855 = 1462283) B1462283
theorem B1466383 : Blo 255820 1466383 := bstep (se 1 (by rfl) ⟨1099787, by rfl⟩ : syracuseStep 1466383 = 2199575) B2199575
theorem B581651 : Blo 255820 581651 := bstep (se 1 (by rfl) ⟨436238, by rfl⟩ : syracuseStep 581651 = 872477) B872477
theorem B385103 : Blo 255820 385103 := bstep (se 1 (by rfl) ⟨288827, by rfl⟩ : syracuseStep 385103 = 577655) B577655
theorem B385223 : Blo 255820 385223 := bstep (se 1 (by rfl) ⟨288917, by rfl⟩ : syracuseStep 385223 = 577835) B577835
theorem B6283493 : Blo 255820 6283493 := bstep (se 4 (by rfl) ⟨589077, by rfl⟩ : syracuseStep 6283493 = 1178155) B1178155
theorem B385385 : Blo 255820 385385 := bstep (se 2 (by rfl) ⟨144519, by rfl⟩ : syracuseStep 385385 = 289039) B289039
theorem B581993 : Blo 255820 581993 := bstep (se 2 (by rfl) ⟨218247, by rfl⟩ : syracuseStep 581993 = 436495) B436495
theorem B385463 : Blo 255820 385463 := bstep (se 1 (by rfl) ⟨289097, by rfl⟩ : syracuseStep 385463 = 578195) B578195
theorem B418231 : Blo 255820 418231 := bstep (se 1 (by rfl) ⟨313673, by rfl⟩ : syracuseStep 418231 = 627347) B627347
theorem B385499 : Blo 255820 385499 := bstep (se 1 (by rfl) ⟨289124, by rfl⟩ : syracuseStep 385499 = 578249) B578249
theorem B975341 : Blo 255820 975341 := bstep (se 3 (by rfl) ⟨182876, by rfl⟩ : syracuseStep 975341 = 365753) B365753
theorem B647777 : Blo 255820 647777 := bstep (se 2 (by rfl) ⟨242916, by rfl⟩ : syracuseStep 647777 = 485833) B485833
theorem B549587 : Blo 255820 549587 := bstep (se 1 (by rfl) ⟨412190, by rfl⟩ : syracuseStep 549587 = 824381) B824381
theorem B385967 : Blo 255820 385967 := bstep (se 1 (by rfl) ⟨289475, by rfl⟩ : syracuseStep 385967 = 578951) B578951
theorem B582587 : Blo 255820 582587 := bstep (se 1 (by rfl) ⟨436940, by rfl⟩ : syracuseStep 582587 = 873881) B873881
theorem B386057 : Blo 255820 386057 := bstep (se 2 (by rfl) ⟨144771, by rfl⟩ : syracuseStep 386057 = 289543) B289543
theorem B386087 : Blo 255820 386087 := bstep (se 1 (by rfl) ⟨289565, by rfl⟩ : syracuseStep 386087 = 579131) B579131
theorem B582713 : Blo 255820 582713 := bstep (se 2 (by rfl) ⟨218517, by rfl⟩ : syracuseStep 582713 = 437035) B437035
theorem B386171 : Blo 255820 386171 := bstep (se 1 (by rfl) ⟨289628, by rfl⟩ : syracuseStep 386171 = 579257) B579257
theorem B1959065 : Blo 255820 1959065 := bstep (se 2 (by rfl) ⟨734649, by rfl⟩ : syracuseStep 1959065 = 1469299) B1469299
theorem B615595 : Blo 255820 615595 := bstep (se 1 (by rfl) ⟨461696, by rfl⟩ : syracuseStep 615595 = 923393) B923393
theorem B386297 : Blo 255820 386297 := bstep (se 2 (by rfl) ⟨144861, by rfl⟩ : syracuseStep 386297 = 289723) B289723
theorem B386399 : Blo 255820 386399 := bstep (se 1 (by rfl) ⟨289799, by rfl⟩ : syracuseStep 386399 = 579599) B579599
theorem B386411 : Blo 255820 386411 := bstep (se 1 (by rfl) ⟨289808, by rfl⟩ : syracuseStep 386411 = 579617) B579617
theorem B583055 : Blo 255820 583055 := bstep (se 1 (by rfl) ⟨437291, by rfl⟩ : syracuseStep 583055 = 874583) B874583
theorem B288175 : Blo 255820 288175 := bstep (se 1 (by rfl) ⟨216131, by rfl⟩ : syracuseStep 288175 = 432263) B432263
theorem B1893851 : Blo 255820 1893851 := bstep (se 1 (by rfl) ⟨1420388, by rfl⟩ : syracuseStep 1893851 = 2840777) B2840777
theorem B386639 : Blo 255820 386639 := bstep (se 1 (by rfl) ⟨289979, by rfl⟩ : syracuseStep 386639 = 579959) B579959
theorem B976481 : Blo 255820 976481 := bstep (se 2 (by rfl) ⟨366180, by rfl⟩ : syracuseStep 976481 = 732361) B732361
theorem B386759 : Blo 255820 386759 := bstep (se 1 (by rfl) ⟨290069, by rfl⟩ : syracuseStep 386759 = 580139) B580139
theorem B583379 : Blo 255820 583379 := bstep (se 1 (by rfl) ⟨437534, by rfl⟩ : syracuseStep 583379 = 875069) B875069
theorem B255823 : Blo 255820 255823 := bstep (se 1 (by rfl) ⟨191867, by rfl⟩ : syracuseStep 255823 = 383735) B383735
theorem B255839 : Blo 255820 255839 := bstep (se 1 (by rfl) ⟨191879, by rfl⟩ : syracuseStep 255839 = 383759) B383759
theorem B288607 : Blo 255820 288607 := bstep (se 1 (by rfl) ⟨216455, by rfl⟩ : syracuseStep 288607 = 432911) B432911
theorem B386921 : Blo 255820 386921 := bstep (se 2 (by rfl) ⟨145095, by rfl⟩ : syracuseStep 386921 = 290191) B290191
theorem B255867 : Blo 255820 255867 := bstep (se 1 (by rfl) ⟨191900, by rfl⟩ : syracuseStep 255867 = 383801) B383801
theorem B550817 : Blo 255820 550817 := bstep (se 2 (by rfl) ⟨206556, by rfl⟩ : syracuseStep 550817 = 413113) B413113
theorem B255919 : Blo 255820 255919 := bstep (se 1 (by rfl) ⟨191939, by rfl⟩ : syracuseStep 255919 = 383879) B383879
theorem B386999 : Blo 255820 386999 := bstep (se 1 (by rfl) ⟨290249, by rfl⟩ : syracuseStep 386999 = 580499) B580499
theorem B255943 : Blo 255820 255943 := bstep (se 1 (by rfl) ⟨191957, by rfl⟩ : syracuseStep 255943 = 383915) B383915
theorem B255963 : Blo 255820 255963 := bstep (se 1 (by rfl) ⟨191972, by rfl⟩ : syracuseStep 255963 = 383945) B383945
theorem B387035 : Blo 255820 387035 := bstep (se 1 (by rfl) ⟨290276, by rfl⟩ : syracuseStep 387035 = 580553) B580553
theorem B550919 : Blo 255820 550919 := bstep (se 1 (by rfl) ⟨413189, by rfl⟩ : syracuseStep 550919 = 826379) B826379
theorem B649235 : Blo 255820 649235 := bstep (se 1 (by rfl) ⟨486926, by rfl⟩ : syracuseStep 649235 = 973853) B973853
theorem B256039 : Blo 255820 256039 := bstep (se 1 (by rfl) ⟨192029, by rfl⟩ : syracuseStep 256039 = 384059) B384059
theorem B1108025 : Blo 255820 1108025 := bstep (se 2 (by rfl) ⟨415509, by rfl⟩ : syracuseStep 1108025 = 831019) B831019
theorem B256079 : Blo 255820 256079 := bstep (se 1 (by rfl) ⟨192059, by rfl⟩ : syracuseStep 256079 = 384119) B384119
theorem B256095 : Blo 255820 256095 := bstep (se 1 (by rfl) ⟨192071, by rfl⟩ : syracuseStep 256095 = 384143) B384143
theorem B256123 : Blo 255820 256123 := bstep (se 1 (by rfl) ⟨192092, by rfl⟩ : syracuseStep 256123 = 384185) B384185
theorem B256175 : Blo 255820 256175 := bstep (se 1 (by rfl) ⟨192131, by rfl⟩ : syracuseStep 256175 = 384263) B384263
theorem B256199 : Blo 255820 256199 := bstep (se 1 (by rfl) ⟨192149, by rfl⟩ : syracuseStep 256199 = 384299) B384299
theorem B288967 : Blo 255820 288967 := bstep (se 1 (by rfl) ⟨216725, by rfl⟩ : syracuseStep 288967 = 433451) B433451
theorem B256219 : Blo 255820 256219 := bstep (se 1 (by rfl) ⟨192164, by rfl⟩ : syracuseStep 256219 = 384329) B384329
theorem B256295 : Blo 255820 256295 := bstep (se 1 (by rfl) ⟨192221, by rfl⟩ : syracuseStep 256295 = 384443) B384443
theorem B256335 : Blo 255820 256335 := bstep (se 1 (by rfl) ⟨192251, by rfl⟩ : syracuseStep 256335 = 384503) B384503
theorem B256351 : Blo 255820 256351 := bstep (se 1 (by rfl) ⟨192263, by rfl⟩ : syracuseStep 256351 = 384527) B384527
theorem B256379 : Blo 255820 256379 := bstep (se 1 (by rfl) ⟨192284, by rfl⟩ : syracuseStep 256379 = 384569) B384569
theorem B4155779 : Blo 255820 4155779 := bstep (se 1 (by rfl) ⟨3116834, by rfl⟩ : syracuseStep 4155779 = 6233669) B6233669
theorem B256431 : Blo 255820 256431 := bstep (se 1 (by rfl) ⟨192323, by rfl⟩ : syracuseStep 256431 = 384647) B384647
theorem B387503 : Blo 255820 387503 := bstep (se 1 (by rfl) ⟨290627, by rfl⟩ : syracuseStep 387503 = 581255) B581255
theorem B256455 : Blo 255820 256455 := bstep (se 1 (by rfl) ⟨192341, by rfl⟩ : syracuseStep 256455 = 384683) B384683
theorem B256475 : Blo 255820 256475 := bstep (se 1 (by rfl) ⟨192356, by rfl⟩ : syracuseStep 256475 = 384713) B384713
theorem B649691 : Blo 255820 649691 := bstep (se 1 (by rfl) ⟨487268, by rfl⟩ : syracuseStep 649691 = 974537) B974537
theorem B387593 : Blo 255820 387593 := bstep (se 2 (by rfl) ⟨145347, by rfl⟩ : syracuseStep 387593 = 290695) B290695
theorem B256551 : Blo 255820 256551 := bstep (se 1 (by rfl) ⟨192413, by rfl⟩ : syracuseStep 256551 = 384827) B384827
theorem B387623 : Blo 255820 387623 := bstep (se 1 (by rfl) ⟨290717, by rfl⟩ : syracuseStep 387623 = 581435) B581435
theorem B977467 : Blo 255820 977467 := bstep (se 1 (by rfl) ⟨733100, by rfl⟩ : syracuseStep 977467 = 1466201) B1466201
theorem B256591 : Blo 255820 256591 := bstep (se 1 (by rfl) ⟨192443, by rfl⟩ : syracuseStep 256591 = 384887) B384887
theorem B256607 : Blo 255820 256607 := bstep (se 1 (by rfl) ⟨192455, by rfl⟩ : syracuseStep 256607 = 384911) B384911
theorem B256635 : Blo 255820 256635 := bstep (se 1 (by rfl) ⟨192476, by rfl⟩ : syracuseStep 256635 = 384953) B384953
theorem B387707 : Blo 255820 387707 := bstep (se 1 (by rfl) ⟨290780, by rfl⟩ : syracuseStep 387707 = 581561) B581561
theorem B584315 : Blo 255820 584315 := bstep (se 1 (by rfl) ⟨438236, by rfl⟩ : syracuseStep 584315 = 876473) B876473
theorem B256687 : Blo 255820 256687 := bstep (se 1 (by rfl) ⟨192515, by rfl⟩ : syracuseStep 256687 = 385031) B385031
theorem B256711 : Blo 255820 256711 := bstep (se 1 (by rfl) ⟨192533, by rfl⟩ : syracuseStep 256711 = 385067) B385067
theorem B256731 : Blo 255820 256731 := bstep (se 1 (by rfl) ⟨192548, by rfl⟩ : syracuseStep 256731 = 385097) B385097
theorem B486137 : Blo 255820 486137 := bstep (se 2 (by rfl) ⟨182301, by rfl⟩ : syracuseStep 486137 = 364603) B364603
theorem B387833 : Blo 255820 387833 := bstep (se 2 (by rfl) ⟨145437, by rfl⟩ : syracuseStep 387833 = 290875) B290875
theorem B584441 : Blo 255820 584441 := bstep (se 2 (by rfl) ⟨219165, by rfl⟩ : syracuseStep 584441 = 438331) B438331
theorem B256807 : Blo 255820 256807 := bstep (se 1 (by rfl) ⟨192605, by rfl⟩ : syracuseStep 256807 = 385211) B385211
theorem B256847 : Blo 255820 256847 := bstep (se 1 (by rfl) ⟨192635, by rfl⟩ : syracuseStep 256847 = 385271) B385271
theorem B256863 : Blo 255820 256863 := bstep (se 1 (by rfl) ⟨192647, by rfl⟩ : syracuseStep 256863 = 385295) B385295
theorem B387935 : Blo 255820 387935 := bstep (se 1 (by rfl) ⟨290951, by rfl⟩ : syracuseStep 387935 = 581903) B581903
theorem B977771 : Blo 255820 977771 := bstep (se 1 (by rfl) ⟨733328, by rfl⟩ : syracuseStep 977771 = 1466657) B1466657
theorem B387947 : Blo 255820 387947 := bstep (se 1 (by rfl) ⟨290960, by rfl⟩ : syracuseStep 387947 = 581921) B581921
theorem B256891 : Blo 255820 256891 := bstep (se 1 (by rfl) ⟨192668, by rfl⟩ : syracuseStep 256891 = 385337) B385337
theorem B5532563 : Blo 255820 5532563 := bstep (se 1 (by rfl) ⟨4149422, by rfl⟩ : syracuseStep 5532563 = 8298845) B8298845
theorem B486319 : Blo 255820 486319 := bstep (se 1 (by rfl) ⟨364739, by rfl⟩ : syracuseStep 486319 = 729479) B729479
theorem B256943 : Blo 255820 256943 := bstep (se 1 (by rfl) ⟨192707, by rfl⟩ : syracuseStep 256943 = 385415) B385415
theorem B256967 : Blo 255820 256967 := bstep (se 1 (by rfl) ⟨192725, by rfl⟩ : syracuseStep 256967 = 385451) B385451
theorem B256987 : Blo 255820 256987 := bstep (se 1 (by rfl) ⟨192740, by rfl⟩ : syracuseStep 256987 = 385481) B385481
theorem B977939 : Blo 255820 977939 := bstep (se 1 (by rfl) ⟨733454, by rfl⟩ : syracuseStep 977939 = 1466909) B1466909
theorem B257063 : Blo 255820 257063 := bstep (se 1 (by rfl) ⟨192797, by rfl⟩ : syracuseStep 257063 = 385595) B385595
theorem B289831 : Blo 255820 289831 := bstep (se 1 (by rfl) ⟨217373, by rfl⟩ : syracuseStep 289831 = 434747) B434747
theorem B1961009 : Blo 255820 1961009 := bstep (se 2 (by rfl) ⟨735378, by rfl⟩ : syracuseStep 1961009 = 1470757) B1470757
theorem B486479 : Blo 255820 486479 := bstep (se 1 (by rfl) ⟨364859, by rfl⟩ : syracuseStep 486479 = 729719) B729719
theorem B257103 : Blo 255820 257103 := bstep (se 1 (by rfl) ⟨192827, by rfl⟩ : syracuseStep 257103 = 385655) B385655
theorem B388175 : Blo 255820 388175 := bstep (se 1 (by rfl) ⟨291131, by rfl⟩ : syracuseStep 388175 = 582263) B582263
theorem B257119 : Blo 255820 257119 := bstep (se 1 (by rfl) ⟨192839, by rfl⟩ : syracuseStep 257119 = 385679) B385679
theorem B879731 : Blo 255820 879731 := bstep (se 1 (by rfl) ⟨659798, by rfl⟩ : syracuseStep 879731 = 1319597) B1319597
theorem B257147 : Blo 255820 257147 := bstep (se 1 (by rfl) ⟨192860, by rfl⟩ : syracuseStep 257147 = 385721) B385721
theorem B257199 : Blo 255820 257199 := bstep (se 1 (by rfl) ⟨192899, by rfl⟩ : syracuseStep 257199 = 385799) B385799
theorem B257223 : Blo 255820 257223 := bstep (se 1 (by rfl) ⟨192917, by rfl⟩ : syracuseStep 257223 = 385835) B385835
theorem B388295 : Blo 255820 388295 := bstep (se 1 (by rfl) ⟨291221, by rfl⟩ : syracuseStep 388295 = 582443) B582443
theorem B257243 : Blo 255820 257243 := bstep (se 1 (by rfl) ⟨192932, by rfl⟩ : syracuseStep 257243 = 385865) B385865
theorem B257319 : Blo 255820 257319 := bstep (se 1 (by rfl) ⟨192989, by rfl⟩ : syracuseStep 257319 = 385979) B385979
theorem B257359 : Blo 255820 257359 := bstep (se 1 (by rfl) ⟨193019, by rfl⟩ : syracuseStep 257359 = 386039) B386039
theorem B257375 : Blo 255820 257375 := bstep (se 1 (by rfl) ⟨193031, by rfl⟩ : syracuseStep 257375 = 386063) B386063
theorem B388457 : Blo 255820 388457 := bstep (se 2 (by rfl) ⟨145671, by rfl⟩ : syracuseStep 388457 = 291343) B291343
theorem B257403 : Blo 255820 257403 := bstep (se 1 (by rfl) ⟨193052, by rfl⟩ : syracuseStep 257403 = 386105) B386105
theorem B257455 : Blo 255820 257455 := bstep (se 1 (by rfl) ⟨193091, by rfl⟩ : syracuseStep 257455 = 386183) B386183
theorem B388535 : Blo 255820 388535 := bstep (se 1 (by rfl) ⟨291401, by rfl⟩ : syracuseStep 388535 = 582803) B582803
theorem B257479 : Blo 255820 257479 := bstep (se 1 (by rfl) ⟨193109, by rfl⟩ : syracuseStep 257479 = 386219) B386219
theorem B880091 : Blo 255820 880091 := bstep (se 1 (by rfl) ⟨660068, by rfl⟩ : syracuseStep 880091 = 1320137) B1320137
theorem B257499 : Blo 255820 257499 := bstep (se 1 (by rfl) ⟨193124, by rfl⟩ : syracuseStep 257499 = 386249) B386249
theorem B388571 : Blo 255820 388571 := bstep (se 1 (by rfl) ⟨291428, by rfl⟩ : syracuseStep 388571 = 582857) B582857
theorem B3730931 : Blo 255820 3730931 := bstep (se 1 (by rfl) ⟨2798198, by rfl⟩ : syracuseStep 3730931 = 5596397) B5596397
theorem B552457 : Blo 255820 552457 := bstep (se 2 (by rfl) ⟨207171, by rfl⟩ : syracuseStep 552457 = 414343) B414343
theorem B257575 : Blo 255820 257575 := bstep (se 1 (by rfl) ⟨193181, by rfl⟩ : syracuseStep 257575 = 386363) B386363
theorem B257615 : Blo 255820 257615 := bstep (se 1 (by rfl) ⟨193211, by rfl⟩ : syracuseStep 257615 = 386423) B386423
theorem B257631 : Blo 255820 257631 := bstep (se 1 (by rfl) ⟨193223, by rfl⟩ : syracuseStep 257631 = 386447) B386447
theorem B650875 : Blo 255820 650875 := bstep (se 1 (by rfl) ⟨488156, by rfl⟩ : syracuseStep 650875 = 976313) B976313
theorem B257659 : Blo 255820 257659 := bstep (se 1 (by rfl) ⟨193244, by rfl⟩ : syracuseStep 257659 = 386489) B386489
theorem B2715275 : Blo 255820 2715275 := bstep (se 1 (by rfl) ⟨2036456, by rfl⟩ : syracuseStep 2715275 = 4072913) B4072913
theorem B257711 : Blo 255820 257711 := bstep (se 1 (by rfl) ⟨193283, by rfl⟩ : syracuseStep 257711 = 386567) B386567
theorem B1175239 : Blo 255820 1175239 := bstep (se 1 (by rfl) ⟨881429, by rfl⟩ : syracuseStep 1175239 = 1762859) B1762859
theorem B257735 : Blo 255820 257735 := bstep (se 1 (by rfl) ⟨193301, by rfl⟩ : syracuseStep 257735 = 386603) B386603
theorem B257755 : Blo 255820 257755 := bstep (se 1 (by rfl) ⟨193316, by rfl⟩ : syracuseStep 257755 = 386633) B386633
theorem B519929 : Blo 255820 519929 := bstep (se 2 (by rfl) ⟨194973, by rfl⟩ : syracuseStep 519929 = 389947) B389947
theorem B257831 : Blo 255820 257831 := bstep (se 1 (by rfl) ⟨193373, by rfl⟩ : syracuseStep 257831 = 386747) B386747
theorem B257871 : Blo 255820 257871 := bstep (se 1 (by rfl) ⟨193403, by rfl⟩ : syracuseStep 257871 = 386807) B386807
theorem B257887 : Blo 255820 257887 := bstep (se 1 (by rfl) ⟨193415, by rfl⟩ : syracuseStep 257887 = 386831) B386831
theorem B257915 : Blo 255820 257915 := bstep (se 1 (by rfl) ⟨193436, by rfl⟩ : syracuseStep 257915 = 386873) B386873
theorem B1306529 : Blo 255820 1306529 := bstep (se 2 (by rfl) ⟨489948, by rfl⟩ : syracuseStep 1306529 = 979897) B979897
theorem B257967 : Blo 255820 257967 := bstep (se 1 (by rfl) ⟨193475, by rfl⟩ : syracuseStep 257967 = 386951) B386951
theorem B389039 : Blo 255820 389039 := bstep (se 1 (by rfl) ⟨291779, by rfl⟩ : syracuseStep 389039 = 583559) B583559
theorem B257991 : Blo 255820 257991 := bstep (se 1 (by rfl) ⟨193493, by rfl⟩ : syracuseStep 257991 = 386987) B386987
theorem B258011 : Blo 255820 258011 := bstep (se 1 (by rfl) ⟨193508, by rfl⟩ : syracuseStep 258011 = 387017) B387017
theorem B389129 : Blo 255820 389129 := bstep (se 2 (by rfl) ⟨145923, by rfl⟩ : syracuseStep 389129 = 291847) B291847
theorem B258087 : Blo 255820 258087 := bstep (se 1 (by rfl) ⟨193565, by rfl⟩ : syracuseStep 258087 = 387131) B387131
theorem B389159 : Blo 255820 389159 := bstep (se 1 (by rfl) ⟨291869, by rfl⟩ : syracuseStep 389159 = 583739) B583739
theorem B258127 : Blo 255820 258127 := bstep (se 1 (by rfl) ⟨193595, by rfl⟩ : syracuseStep 258127 = 387191) B387191
theorem B258143 : Blo 255820 258143 := bstep (se 1 (by rfl) ⟨193607, by rfl⟩ : syracuseStep 258143 = 387215) B387215
theorem B258171 : Blo 255820 258171 := bstep (se 1 (by rfl) ⟨193628, by rfl⟩ : syracuseStep 258171 = 387257) B387257
theorem B389243 : Blo 255820 389243 := bstep (se 1 (by rfl) ⟨291932, by rfl⟩ : syracuseStep 389243 = 583865) B583865
theorem B487595 : Blo 255820 487595 := bstep (se 1 (by rfl) ⟨365696, by rfl⟩ : syracuseStep 487595 = 731393) B731393
theorem B258223 : Blo 255820 258223 := bstep (se 1 (by rfl) ⟨193667, by rfl⟩ : syracuseStep 258223 = 387335) B387335
theorem B258247 : Blo 255820 258247 := bstep (se 1 (by rfl) ⟨193685, by rfl⟩ : syracuseStep 258247 = 387371) B387371
theorem B258267 : Blo 255820 258267 := bstep (se 1 (by rfl) ⟨193700, by rfl⟩ : syracuseStep 258267 = 387401) B387401
theorem B389369 : Blo 255820 389369 := bstep (se 2 (by rfl) ⟨146013, by rfl⟩ : syracuseStep 389369 = 292027) B292027
theorem B3141899 : Blo 255820 3141899 := bstep (se 1 (by rfl) ⟨2356424, by rfl⟩ : syracuseStep 3141899 = 4712849) B4712849
theorem B258343 : Blo 255820 258343 := bstep (se 1 (by rfl) ⟨193757, by rfl⟩ : syracuseStep 258343 = 387515) B387515
theorem B258383 : Blo 255820 258383 := bstep (se 1 (by rfl) ⟨193787, by rfl⟩ : syracuseStep 258383 = 387575) B387575
theorem B520543 : Blo 255820 520543 := bstep (se 1 (by rfl) ⟨390407, by rfl⟩ : syracuseStep 520543 = 780815) B780815
theorem B258399 : Blo 255820 258399 := bstep (se 1 (by rfl) ⟨193799, by rfl⟩ : syracuseStep 258399 = 387599) B387599
theorem B389471 : Blo 255820 389471 := bstep (se 1 (by rfl) ⟨292103, by rfl⟩ : syracuseStep 389471 = 584207) B584207
theorem B389483 : Blo 255820 389483 := bstep (se 1 (by rfl) ⟨292112, by rfl⟩ : syracuseStep 389483 = 584225) B584225
theorem B258427 : Blo 255820 258427 := bstep (se 1 (by rfl) ⟨193820, by rfl⟩ : syracuseStep 258427 = 387641) B387641
theorem B520609 : Blo 255820 520609 := bstep (se 2 (by rfl) ⟨195228, by rfl⟩ : syracuseStep 520609 = 390457) B390457
theorem B258479 : Blo 255820 258479 := bstep (se 1 (by rfl) ⟨193859, by rfl⟩ : syracuseStep 258479 = 387719) B387719
theorem B258503 : Blo 255820 258503 := bstep (se 1 (by rfl) ⟨193877, by rfl⟩ : syracuseStep 258503 = 387755) B387755
theorem B258523 : Blo 255820 258523 := bstep (se 1 (by rfl) ⟨193892, by rfl⟩ : syracuseStep 258523 = 387785) B387785
theorem B258599 : Blo 255820 258599 := bstep (se 1 (by rfl) ⟨193949, by rfl⟩ : syracuseStep 258599 = 387899) B387899
theorem B258639 : Blo 255820 258639 := bstep (se 1 (by rfl) ⟨193979, by rfl⟩ : syracuseStep 258639 = 387959) B387959
theorem B389711 : Blo 255820 389711 := bstep (se 1 (by rfl) ⟨292283, by rfl⟩ : syracuseStep 389711 = 584567) B584567
theorem B258655 : Blo 255820 258655 := bstep (se 1 (by rfl) ⟨193991, by rfl⟩ : syracuseStep 258655 = 387983) B387983
theorem B258683 : Blo 255820 258683 := bstep (se 1 (by rfl) ⟨194012, by rfl⟩ : syracuseStep 258683 = 388025) B388025
theorem B291451 : Blo 255820 291451 := bstep (se 1 (by rfl) ⟨218588, by rfl⟩ : syracuseStep 291451 = 437177) B437177
theorem B258735 : Blo 255820 258735 := bstep (se 1 (by rfl) ⟨194051, by rfl⟩ : syracuseStep 258735 = 388103) B388103
theorem B258759 : Blo 255820 258759 := bstep (se 1 (by rfl) ⟨194069, by rfl⟩ : syracuseStep 258759 = 388139) B388139
theorem B1864403 : Blo 255820 1864403 := bstep (se 1 (by rfl) ⟨1398302, by rfl⟩ : syracuseStep 1864403 = 2796605) B2796605
theorem B258779 : Blo 255820 258779 := bstep (se 1 (by rfl) ⟨194084, by rfl⟩ : syracuseStep 258779 = 388169) B388169
theorem B553721 : Blo 255820 553721 := bstep (se 2 (by rfl) ⟨207645, by rfl⟩ : syracuseStep 553721 = 415291) B415291
theorem B258855 : Blo 255820 258855 := bstep (se 1 (by rfl) ⟨194141, by rfl⟩ : syracuseStep 258855 = 388283) B388283
theorem B258895 : Blo 255820 258895 := bstep (se 1 (by rfl) ⟨194171, by rfl⟩ : syracuseStep 258895 = 388343) B388343
theorem B258911 : Blo 255820 258911 := bstep (se 1 (by rfl) ⟨194183, by rfl⟩ : syracuseStep 258911 = 388367) B388367
theorem B258939 : Blo 255820 258939 := bstep (se 1 (by rfl) ⟨194204, by rfl⟩ : syracuseStep 258939 = 388409) B388409
theorem B258991 : Blo 255820 258991 := bstep (se 1 (by rfl) ⟨194243, by rfl⟩ : syracuseStep 258991 = 388487) B388487
theorem B259015 : Blo 255820 259015 := bstep (se 1 (by rfl) ⟨194261, by rfl⟩ : syracuseStep 259015 = 388523) B388523
theorem B259035 : Blo 255820 259035 := bstep (se 1 (by rfl) ⟨194276, by rfl⟩ : syracuseStep 259035 = 388553) B388553
theorem B259111 : Blo 255820 259111 := bstep (se 1 (by rfl) ⟨194333, by rfl⟩ : syracuseStep 259111 = 388667) B388667
theorem B521273 : Blo 255820 521273 := bstep (se 2 (by rfl) ⟨195477, by rfl⟩ : syracuseStep 521273 = 390955) B390955
theorem B259151 : Blo 255820 259151 := bstep (se 1 (by rfl) ⟨194363, by rfl⟩ : syracuseStep 259151 = 388727) B388727
theorem B291919 : Blo 255820 291919 := bstep (se 1 (by rfl) ⟨218939, by rfl⟩ : syracuseStep 291919 = 437879) B437879
theorem B259167 : Blo 255820 259167 := bstep (se 1 (by rfl) ⟨194375, by rfl⟩ : syracuseStep 259167 = 388751) B388751
theorem B259195 : Blo 255820 259195 := bstep (se 1 (by rfl) ⟨194396, by rfl⟩ : syracuseStep 259195 = 388793) B388793
theorem B259247 : Blo 255820 259247 := bstep (se 1 (by rfl) ⟨194435, by rfl⟩ : syracuseStep 259247 = 388871) B388871
theorem B259271 : Blo 255820 259271 := bstep (se 1 (by rfl) ⟨194453, by rfl⟩ : syracuseStep 259271 = 388907) B388907
theorem B259291 : Blo 255820 259291 := bstep (se 1 (by rfl) ⟨194468, by rfl⟩ : syracuseStep 259291 = 388937) B388937
theorem B259367 : Blo 255820 259367 := bstep (se 1 (by rfl) ⟨194525, by rfl⟩ : syracuseStep 259367 = 389051) B389051
theorem B259407 : Blo 255820 259407 := bstep (se 1 (by rfl) ⟨194555, by rfl⟩ : syracuseStep 259407 = 389111) B389111
theorem B259423 : Blo 255820 259423 := bstep (se 1 (by rfl) ⟨194567, by rfl⟩ : syracuseStep 259423 = 389135) B389135
theorem B390505 : Blo 255820 390505 := bstep (se 2 (by rfl) ⟨146439, by rfl⟩ : syracuseStep 390505 = 292879) B292879
theorem B259451 : Blo 255820 259451 := bstep (se 1 (by rfl) ⟨194588, by rfl⟩ : syracuseStep 259451 = 389177) B389177
theorem B2717093 : Blo 255820 2717093 := bstep (se 4 (by rfl) ⟨254727, by rfl⟩ : syracuseStep 2717093 = 509455) B509455
theorem B259503 : Blo 255820 259503 := bstep (se 1 (by rfl) ⟨194627, by rfl⟩ : syracuseStep 259503 = 389255) B389255
theorem B259527 : Blo 255820 259527 := bstep (se 1 (by rfl) ⟨194645, by rfl⟩ : syracuseStep 259527 = 389291) B389291
theorem B259547 : Blo 255820 259547 := bstep (se 1 (by rfl) ⟨194660, by rfl⟩ : syracuseStep 259547 = 389321) B389321
theorem B390665 : Blo 255820 390665 := bstep (se 2 (by rfl) ⟨146499, by rfl⟩ : syracuseStep 390665 = 292999) B292999
theorem B783881 : Blo 255820 783881 := bstep (se 2 (by rfl) ⟨293955, by rfl⟩ : syracuseStep 783881 = 587911) B587911
theorem B259623 : Blo 255820 259623 := bstep (se 1 (by rfl) ⟨194717, by rfl⟩ : syracuseStep 259623 = 389435) B389435
theorem B259663 : Blo 255820 259663 := bstep (se 1 (by rfl) ⟨194747, by rfl⟩ : syracuseStep 259663 = 389495) B389495
theorem B259679 : Blo 255820 259679 := bstep (se 1 (by rfl) ⟨194759, by rfl⟩ : syracuseStep 259679 = 389519) B389519
theorem B259707 : Blo 255820 259707 := bstep (se 1 (by rfl) ⟨194780, by rfl⟩ : syracuseStep 259707 = 389561) B389561
theorem B2258579 : Blo 255820 2258579 := bstep (se 1 (by rfl) ⟨1693934, by rfl⟩ : syracuseStep 2258579 = 3387869) B3387869
theorem B259759 : Blo 255820 259759 := bstep (se 1 (by rfl) ⟨194819, by rfl⟩ : syracuseStep 259759 = 389639) B389639
theorem B259783 : Blo 255820 259783 := bstep (se 1 (by rfl) ⟨194837, by rfl⟩ : syracuseStep 259783 = 389675) B389675
theorem B1472215 : Blo 255820 1472215 := bstep (se 1 (by rfl) ⟨1104161, by rfl⟩ : syracuseStep 1472215 = 2208323) B2208323
theorem B259803 : Blo 255820 259803 := bstep (se 1 (by rfl) ⟨194852, by rfl⟩ : syracuseStep 259803 = 389705) B389705
theorem B489311 : Blo 255820 489311 := bstep (se 1 (by rfl) ⟨366983, by rfl⟩ : syracuseStep 489311 = 733967) B733967
theorem B980855 : Blo 255820 980855 := bstep (se 1 (by rfl) ⟨735641, by rfl⟩ : syracuseStep 980855 = 1471283) B1471283
theorem B325559 : Blo 255820 325559 := bstep (se 1 (by rfl) ⟨244169, by rfl⟩ : syracuseStep 325559 = 488339) B488339
theorem B325711 : Blo 255820 325711 := bstep (se 1 (by rfl) ⟨244283, by rfl⟩ : syracuseStep 325711 = 488567) B488567
theorem B588023 : Blo 255820 588023 := bstep (se 1 (by rfl) ⟨441017, by rfl⟩ : syracuseStep 588023 = 882035) B882035
theorem B489721 : Blo 255820 489721 := bstep (se 2 (by rfl) ⟨183645, by rfl⟩ : syracuseStep 489721 = 367291) B367291
theorem B490063 : Blo 255820 490063 := bstep (se 1 (by rfl) ⟨367547, by rfl⟩ : syracuseStep 490063 = 735095) B735095
theorem B981827 : Blo 255820 981827 := bstep (se 1 (by rfl) ⟨736370, by rfl⟩ : syracuseStep 981827 = 1472741) B1472741
theorem B490313 : Blo 255820 490313 := bstep (se 2 (by rfl) ⟨183867, by rfl⟩ : syracuseStep 490313 = 367735) B367735
theorem B1145707 : Blo 255820 1145707 := bstep (se 1 (by rfl) ⟨859280, by rfl⟩ : syracuseStep 1145707 = 1718561) B1718561
theorem B261083 : Blo 255820 261083 := bstep (se 1 (by rfl) ⟨195812, by rfl⟩ : syracuseStep 261083 = 391625) B391625
theorem B326855 : Blo 255820 326855 := bstep (se 1 (by rfl) ⟨245141, by rfl⟩ : syracuseStep 326855 = 490283) B490283
theorem B327007 : Blo 255820 327007 := bstep (se 1 (by rfl) ⟨245255, by rfl⟩ : syracuseStep 327007 = 490511) B490511
theorem B1113587 : Blo 255820 1113587 := bstep (se 1 (by rfl) ⟨835190, by rfl⟩ : syracuseStep 1113587 = 1670381) B1670381
theorem B491179 : Blo 255820 491179 := bstep (se 1 (by rfl) ⟨368384, by rfl⟩ : syracuseStep 491179 = 736769) B736769
theorem B491255 : Blo 255820 491255 := bstep (se 1 (by rfl) ⟨368441, by rfl⟩ : syracuseStep 491255 = 736883) B736883
theorem B982813 : Blo 255820 982813 := bstep (se 3 (by rfl) ⟨184277, by rfl⟩ : syracuseStep 982813 = 368555) B368555
theorem B655199 : Blo 255820 655199 := bstep (se 1 (by rfl) ⟨491399, by rfl⟩ : syracuseStep 655199 = 982799) B982799
theorem B491483 : Blo 255820 491483 := bstep (se 1 (by rfl) ⟨368612, by rfl⟩ : syracuseStep 491483 = 737225) B737225
theorem B45547541 : Blo 255820 45547541 := bstep (se 6 (by rfl) ⟨1067520, by rfl⟩ : syracuseStep 45547541 = 2135041) B2135041
theorem B15728717 : Blo 255820 15728717 := bstep (se 3 (by rfl) ⟨2949134, by rfl⟩ : syracuseStep 15728717 = 5898269) B5898269
theorem B1245395 : Blo 255820 1245395 := bstep (se 1 (by rfl) ⟨934046, by rfl⟩ : syracuseStep 1245395 = 1868093) B1868093
theorem B623015 : Blo 255820 623015 := bstep (se 1 (by rfl) ⟨467261, by rfl⟩ : syracuseStep 623015 = 934523) B934523
theorem B4391495 : Blo 255820 4391495 := bstep (se 1 (by rfl) ⟨3293621, by rfl⟩ : syracuseStep 4391495 = 6587243) B6587243
theorem B557641 : Blo 255820 557641 := bstep (se 2 (by rfl) ⟨209115, by rfl⟩ : syracuseStep 557641 = 418231) B418231
theorem B1966841 : Blo 255820 1966841 := bstep (se 2 (by rfl) ⟨737565, by rfl⟩ : syracuseStep 1966841 = 1475131) B1475131
theorem B820793 : Blo 255820 820793 := bstep (se 2 (by rfl) ⟨307797, by rfl⟩ : syracuseStep 820793 = 615595) B615595
theorem B2197115 : Blo 255820 2197115 := bstep (se 1 (by rfl) ⟨1647836, by rfl⟩ : syracuseStep 2197115 = 3295673) B3295673
theorem B657193 : Blo 255820 657193 := bstep (se 2 (by rfl) ⟨246447, by rfl⟩ : syracuseStep 657193 = 492895) B492895
theorem B1247183 : Blo 255820 1247183 := bstep (se 1 (by rfl) ⟨935387, by rfl⟩ : syracuseStep 1247183 = 1870775) B1870775
theorem B1476589 : Blo 255820 1476589 := bstep (se 3 (by rfl) ⟨276860, by rfl⟩ : syracuseStep 1476589 = 553721) B553721
theorem B1312847 : Blo 255820 1312847 := bstep (se 1 (by rfl) ⟨984635, by rfl⟩ : syracuseStep 1312847 = 1969271) B1969271
theorem B2099623 : Blo 255820 2099623 := bstep (se 1 (by rfl) ⟨1574717, by rfl⟩ : syracuseStep 2099623 = 3149435) B3149435
theorem B2689523 : Blo 255820 2689523 := bstep (se 1 (by rfl) ⟨2017142, by rfl⟩ : syracuseStep 2689523 = 4034285) B4034285
theorem B4426487 : Blo 255820 4426487 := bstep (se 1 (by rfl) ⟨3319865, by rfl⟩ : syracuseStep 4426487 = 6639731) B6639731
theorem B1477547 : Blo 255820 1477547 := bstep (se 1 (by rfl) ⟨1108160, by rfl⟩ : syracuseStep 1477547 = 2216321) B2216321
theorem B887723 : Blo 255820 887723 := bstep (se 1 (by rfl) ⟨665792, by rfl⟩ : syracuseStep 887723 = 1331585) B1331585
theorem B1313981 : Blo 255820 1313981 := bstep (se 3 (by rfl) ⟨246371, by rfl⟩ : syracuseStep 1313981 = 492743) B492743
theorem B2100599 : Blo 255820 2100599 := bstep (se 1 (by rfl) ⟨1575449, by rfl⟩ : syracuseStep 2100599 = 3150899) B3150899
theorem B364267 : Blo 255820 364267 := bstep (se 1 (by rfl) ⟨273200, by rfl⟩ : syracuseStep 364267 = 546401) B546401
theorem B3149725 : Blo 255820 3149725 := bstep (se 3 (by rfl) ⟨590573, by rfl⟩ : syracuseStep 3149725 = 1181147) B1181147
theorem B364495 : Blo 255820 364495 := bstep (se 1 (by rfl) ⟨273371, by rfl⟩ : syracuseStep 364495 = 546743) B546743
theorem B15044579 : Blo 255820 15044579 := bstep (se 1 (by rfl) ⟨11283434, by rfl⟩ : syracuseStep 15044579 = 22566869) B22566869
theorem B823355 : Blo 255820 823355 := bstep (se 1 (by rfl) ⟨617516, by rfl⟩ : syracuseStep 823355 = 1235033) B1235033
theorem B1970243 : Blo 255820 1970243 := bstep (se 1 (by rfl) ⟨1477682, by rfl⟩ : syracuseStep 1970243 = 2955365) B2955365
theorem B2363755 : Blo 255820 2363755 := bstep (se 1 (by rfl) ⟨1772816, by rfl⟩ : syracuseStep 2363755 = 3545633) B3545633
theorem B4395869 : Blo 255820 4395869 := bstep (se 3 (by rfl) ⟨824225, by rfl⟩ : syracuseStep 4395869 = 1648451) B1648451
theorem B1643429 : Blo 255820 1643429 := bstep (se 4 (by rfl) ⟨154071, by rfl⟩ : syracuseStep 1643429 = 308143) B308143
theorem B13407437 : Blo 255820 13407437 := bstep (se 3 (by rfl) ⟨2513894, by rfl⟩ : syracuseStep 13407437 = 5027789) B5027789
theorem B1578199 : Blo 255820 1578199 := bstep (se 1 (by rfl) ⟨1183649, by rfl⟩ : syracuseStep 1578199 = 2367299) B2367299
theorem B922873 : Blo 255820 922873 := bstep (se 2 (by rfl) ⟨346077, by rfl⟩ : syracuseStep 922873 = 692155) B692155
theorem B628105 : Blo 255820 628105 := bstep (se 2 (by rfl) ⟨235539, by rfl⟩ : syracuseStep 628105 = 471079) B471079
theorem B464377 : Blo 255820 464377 := bstep (se 2 (by rfl) ⟨174141, by rfl⟩ : syracuseStep 464377 = 348283) B348283
theorem B431851 : Blo 255820 431851 := bstep (se 1 (by rfl) ⟨323888, by rfl⟩ : syracuseStep 431851 = 647777) B647777
theorem B694057 : Blo 255820 694057 := bstep (se 2 (by rfl) ⟨260271, by rfl⟩ : syracuseStep 694057 = 520543) B520543
theorem B366391 : Blo 255820 366391 := bstep (se 1 (by rfl) ⟨274793, by rfl⟩ : syracuseStep 366391 = 549587) B549587
theorem B694145 : Blo 255820 694145 := bstep (se 2 (by rfl) ⟨260304, by rfl⟩ : syracuseStep 694145 = 520609) B520609
theorem B1022081 : Blo 255820 1022081 := bstep (se 2 (by rfl) ⟨383280, by rfl⟩ : syracuseStep 1022081 = 766561) B766561
theorem B8395109 : Blo 255820 8395109 := bstep (se 4 (by rfl) ⟨787041, by rfl⟩ : syracuseStep 8395109 = 1574083) B1574083
theorem B367211 : Blo 255820 367211 := bstep (se 1 (by rfl) ⟨275408, by rfl⟩ : syracuseStep 367211 = 550817) B550817
theorem B432823 : Blo 255820 432823 := bstep (se 1 (by rfl) ⟨324617, by rfl⟩ : syracuseStep 432823 = 649235) B649235
theorem B1776323 : Blo 255820 1776323 := bstep (se 1 (by rfl) ⟨1332242, by rfl⟩ : syracuseStep 1776323 = 2664485) B2664485
theorem B433127 : Blo 255820 433127 := bstep (se 1 (by rfl) ⟨324845, by rfl⟩ : syracuseStep 433127 = 649691) B649691
theorem B367849 : Blo 255820 367849 := bstep (se 2 (by rfl) ⟨137943, by rfl⟩ : syracuseStep 367849 = 275887) B275887
theorem B466273 : Blo 255820 466273 := bstep (se 2 (by rfl) ⟨174852, by rfl⟩ : syracuseStep 466273 = 349705) B349705
theorem B2956823 : Blo 255820 2956823 := bstep (se 1 (by rfl) ⟨2217617, by rfl⟩ : syracuseStep 2956823 = 4435235) B4435235
theorem B1810183 : Blo 255820 1810183 := bstep (se 1 (by rfl) ⟨1357637, by rfl⟩ : syracuseStep 1810183 = 2715275) B2715275
theorem B696221 : Blo 255820 696221 := bstep (se 3 (by rfl) ⟨130541, by rfl⟩ : syracuseStep 696221 = 261083) B261083
theorem B28712981 : Blo 255820 28712981 := bstep (se 6 (by rfl) ⟨672960, by rfl⟩ : syracuseStep 28712981 = 1345921) B1345921
theorem B434281 : Blo 255820 434281 := bstep (se 2 (by rfl) ⟨162855, by rfl⟩ : syracuseStep 434281 = 325711) B325711
theorem B1122761 : Blo 255820 1122761 := bstep (se 2 (by rfl) ⟨421035, by rfl⟩ : syracuseStep 1122761 = 842071) B842071
theorem B729935 : Blo 255820 729935 := bstep (se 1 (by rfl) ⟨547451, by rfl⟩ : syracuseStep 729935 = 1094903) B1094903
theorem B1811395 : Blo 255820 1811395 := bstep (se 1 (by rfl) ⟨1358546, by rfl⟩ : syracuseStep 1811395 = 2717093) B2717093
theorem B1582649 : Blo 255820 1582649 := bstep (se 2 (by rfl) ⟨593493, by rfl⟩ : syracuseStep 1582649 = 1186987) B1186987
theorem B2467529 : Blo 255820 2467529 := bstep (se 2 (by rfl) ⟨925323, by rfl⟩ : syracuseStep 2467529 = 1850647) B1850647
theorem B436009 : Blo 255820 436009 := bstep (se 2 (by rfl) ⟨163503, by rfl⟩ : syracuseStep 436009 = 327007) B327007
theorem B436799 : Blo 255820 436799 := bstep (se 1 (by rfl) ⟨327599, by rfl⟩ : syracuseStep 436799 = 655199) B655199
theorem B1845949 : Blo 255820 1845949 := bstep (se 3 (by rfl) ⟨346115, by rfl⟩ : syracuseStep 1845949 = 692231) B692231
theorem B437467 : Blo 255820 437467 := bstep (se 1 (by rfl) ⟨328100, by rfl⟩ : syracuseStep 437467 = 656201) B656201
theorem B863675 : Blo 255820 863675 := bstep (se 1 (by rfl) ⟨647756, by rfl⟩ : syracuseStep 863675 = 1295513) B1295513
theorem B1388267 : Blo 255820 1388267 := bstep (se 1 (by rfl) ⟨1041200, by rfl⟩ : syracuseStep 1388267 = 2082401) B2082401
theorem B438223 : Blo 255820 438223 := bstep (se 1 (by rfl) ⟨328667, by rfl⟩ : syracuseStep 438223 = 657335) B657335
theorem B3551321 : Blo 255820 3551321 := bstep (se 2 (by rfl) ⟨1331745, by rfl⟩ : syracuseStep 3551321 = 2663491) B2663491
theorem B1093979 : Blo 255820 1093979 := bstep (se 1 (by rfl) ⟨820484, by rfl⟩ : syracuseStep 1093979 = 1640969) B1640969
theorem B308047 : Blo 255820 308047 := bstep (se 1 (by rfl) ⟨231035, by rfl⟩ : syracuseStep 308047 = 462071) B462071
theorem B1390061 : Blo 255820 1390061 := bstep (se 3 (by rfl) ⟨260636, by rfl⟩ : syracuseStep 1390061 = 521273) B521273
theorem B276143 : Blo 255820 276143 := bstep (se 1 (by rfl) ⟨207107, by rfl⟩ : syracuseStep 276143 = 414215) B414215
theorem B309595 : Blo 255820 309595 := bstep (se 1 (by rfl) ⟨232196, by rfl⟩ : syracuseStep 309595 = 464393) B464393
theorem B1849895 : Blo 255820 1849895 := bstep (se 1 (by rfl) ⟨1387421, by rfl⟩ : syracuseStep 1849895 = 2774843) B2774843
theorem B1752293 : Blo 255820 1752293 := bstep (se 4 (by rfl) ⟨164277, by rfl⟩ : syracuseStep 1752293 = 328555) B328555
theorem B6110437 : Blo 255820 6110437 := bstep (se 4 (by rfl) ⟨572853, by rfl⟩ : syracuseStep 6110437 = 1145707) B1145707
theorem B736609 : Blo 255820 736609 := bstep (se 2 (by rfl) ⟨276228, by rfl⟩ : syracuseStep 736609 = 552457) B552457
theorem B867833 : Blo 255820 867833 := bstep (se 2 (by rfl) ⟨325437, by rfl⟩ : syracuseStep 867833 = 650875) B650875
theorem B5291513 : Blo 255820 5291513 := bstep (se 2 (by rfl) ⟨1984317, by rfl⟩ : syracuseStep 5291513 = 3968635) B3968635
theorem B1326701 : Blo 255820 1326701 := bstep (se 3 (by rfl) ⟨248756, by rfl⟩ : syracuseStep 1326701 = 497513) B497513
theorem B1949345 : Blo 255820 1949345 := bstep (se 2 (by rfl) ⟨731004, by rfl⟩ : syracuseStep 1949345 = 1462009) B1462009
theorem B868103 : Blo 255820 868103 := bstep (se 1 (by rfl) ⟨651077, by rfl⟩ : syracuseStep 868103 = 1302155) B1302155
theorem B868157 : Blo 255820 868157 := bstep (se 3 (by rfl) ⟨162779, by rfl⟩ : syracuseStep 868157 = 325559) B325559
theorem B3293945 : Blo 255820 3293945 := bstep (se 2 (by rfl) ⟨1235229, by rfl⟩ : syracuseStep 3293945 = 2470459) B2470459
theorem B1262567 : Blo 255820 1262567 := bstep (se 1 (by rfl) ⟨946925, by rfl⟩ : syracuseStep 1262567 = 1893851) B1893851
theorem B1295351 : Blo 255820 1295351 := bstep (se 1 (by rfl) ⟨971513, by rfl⟩ : syracuseStep 1295351 = 1943027) B1943027
theorem B1557737 : Blo 255820 1557737 := bstep (se 2 (by rfl) ⟨584151, by rfl⟩ : syracuseStep 1557737 = 1168303) B1168303
theorem B738683 : Blo 255820 738683 := bstep (se 1 (by rfl) ⟨554012, by rfl⟩ : syracuseStep 738683 = 1108025) B1108025
theorem B1951289 : Blo 255820 1951289 := bstep (se 2 (by rfl) ⟨731733, by rfl⟩ : syracuseStep 1951289 = 1463467) B1463467
theorem B2770519 : Blo 255820 2770519 := bstep (se 1 (by rfl) ⟨2077889, by rfl⟩ : syracuseStep 2770519 = 4155779) B4155779
theorem B3688375 : Blo 255820 3688375 := bstep (se 1 (by rfl) ⟨2766281, by rfl⟩ : syracuseStep 3688375 = 5532563) B5532563
theorem B575855 : Blo 255820 575855 := bstep (se 1 (by rfl) ⟨431891, by rfl⟩ : syracuseStep 575855 = 863783) B863783
theorem B575927 : Blo 255820 575927 := bstep (se 1 (by rfl) ⟨431945, by rfl⟩ : syracuseStep 575927 = 863891) B863891
theorem B346619 : Blo 255820 346619 := bstep (se 1 (by rfl) ⟨259964, by rfl⟩ : syracuseStep 346619 = 519929) B519929
theorem B576071 : Blo 255820 576071 := bstep (se 1 (by rfl) ⟨432053, by rfl⟩ : syracuseStep 576071 = 864107) B864107
theorem B576107 : Blo 255820 576107 := bstep (se 1 (by rfl) ⟨432080, by rfl⟩ : syracuseStep 576107 = 864161) B864161
theorem B871019 : Blo 255820 871019 := bstep (se 1 (by rfl) ⟨653264, by rfl⟩ : syracuseStep 871019 = 1306529) B1306529
theorem B2214611 : Blo 255820 2214611 := bstep (se 1 (by rfl) ⟨1660958, by rfl⟩ : syracuseStep 2214611 = 3321917) B3321917
theorem B1297295 : Blo 255820 1297295 := bstep (se 1 (by rfl) ⟨972971, by rfl⟩ : syracuseStep 1297295 = 1945943) B1945943
theorem B576503 : Blo 255820 576503 := bstep (se 1 (by rfl) ⟨432377, by rfl⟩ : syracuseStep 576503 = 864755) B864755
theorem B1100881 : Blo 255820 1100881 := bstep (se 2 (by rfl) ⟨412830, by rfl⟩ : syracuseStep 1100881 = 825661) B825661
theorem B871613 : Blo 255820 871613 := bstep (se 3 (by rfl) ⟨163427, by rfl⟩ : syracuseStep 871613 = 326855) B326855
theorem B576863 : Blo 255820 576863 := bstep (se 1 (by rfl) ⟨432647, by rfl⟩ : syracuseStep 576863 = 865295) B865295
theorem B577259 : Blo 255820 577259 := bstep (se 1 (by rfl) ⟨432944, by rfl⟩ : syracuseStep 577259 = 865889) B865889
theorem B577385 : Blo 255820 577385 := bstep (se 2 (by rfl) ⟨216519, by rfl⟩ : syracuseStep 577385 = 433039) B433039
theorem B578231 : Blo 255820 578231 := bstep (se 1 (by rfl) ⟨433673, by rfl⟩ : syracuseStep 578231 = 867347) B867347
theorem B578447 : Blo 255820 578447 := bstep (se 1 (by rfl) ⟨433835, by rfl⟩ : syracuseStep 578447 = 867671) B867671
theorem B1299401 : Blo 255820 1299401 := bstep (se 2 (by rfl) ⟨487275, by rfl⟩ : syracuseStep 1299401 = 974551) B974551
theorem B742391 : Blo 255820 742391 := bstep (se 1 (by rfl) ⟨556793, by rfl⟩ : syracuseStep 742391 = 1113587) B1113587
theorem B1955177 : Blo 255820 1955177 := bstep (se 2 (by rfl) ⟨733191, by rfl⟩ : syracuseStep 1955177 = 1466383) B1466383
theorem B579167 : Blo 255820 579167 := bstep (se 1 (by rfl) ⟨434375, by rfl⟩ : syracuseStep 579167 = 868751) B868751
theorem B1463993 : Blo 255820 1463993 := bstep (se 2 (by rfl) ⟨548997, by rfl⟩ : syracuseStep 1463993 = 1097995) B1097995
theorem B1660601 : Blo 255820 1660601 := bstep (se 2 (by rfl) ⟨622725, by rfl⟩ : syracuseStep 1660601 = 1245451) B1245451
theorem B579383 : Blo 255820 579383 := bstep (se 1 (by rfl) ⟨434537, by rfl⟩ : syracuseStep 579383 = 869075) B869075
theorem B4413365 : Blo 255820 4413365 := bstep (se 5 (by rfl) ⟨206876, by rfl⟩ : syracuseStep 4413365 = 413753) B413753
theorem B874529 : Blo 255820 874529 := bstep (se 2 (by rfl) ⟨327948, by rfl⟩ : syracuseStep 874529 = 655897) B655897
theorem B579689 : Blo 255820 579689 := bstep (se 2 (by rfl) ⟨217383, by rfl⟩ : syracuseStep 579689 = 434767) B434767
theorem B415849 : Blo 255820 415849 := bstep (se 2 (by rfl) ⟨155943, by rfl⟩ : syracuseStep 415849 = 311887) B311887
theorem B416111 : Blo 255820 416111 := bstep (se 1 (by rfl) ⟨312083, by rfl⟩ : syracuseStep 416111 = 624167) B624167
theorem B580175 : Blo 255820 580175 := bstep (se 1 (by rfl) ⟨435131, by rfl⟩ : syracuseStep 580175 = 870263) B870263
theorem B580319 : Blo 255820 580319 := bstep (se 1 (by rfl) ⟨435239, by rfl⟩ : syracuseStep 580319 = 870479) B870479
theorem B711595 : Blo 255820 711595 := bstep (se 1 (by rfl) ⟨533696, by rfl⟩ : syracuseStep 711595 = 1067393) B1067393
theorem B580571 : Blo 255820 580571 := bstep (se 1 (by rfl) ⟨435428, by rfl⟩ : syracuseStep 580571 = 870857) B870857
theorem B383975 : Blo 255820 383975 := bstep (se 1 (by rfl) ⟨287981, by rfl⟩ : syracuseStep 383975 = 575963) B575963
theorem B580751 : Blo 255820 580751 := bstep (se 1 (by rfl) ⟨435563, by rfl⟩ : syracuseStep 580751 = 871127) B871127
theorem B384233 : Blo 255820 384233 := bstep (se 2 (by rfl) ⟨144087, by rfl⟩ : syracuseStep 384233 = 288175) B288175
theorem B580841 : Blo 255820 580841 := bstep (se 2 (by rfl) ⟨217815, by rfl⟩ : syracuseStep 580841 = 435631) B435631
theorem B384287 : Blo 255820 384287 := bstep (se 1 (by rfl) ⟨288215, by rfl⟩ : syracuseStep 384287 = 576431) B576431
theorem B580895 : Blo 255820 580895 := bstep (se 1 (by rfl) ⟨435671, by rfl⟩ : syracuseStep 580895 = 871343) B871343
theorem B384455 : Blo 255820 384455 := bstep (se 1 (by rfl) ⟨288341, by rfl⟩ : syracuseStep 384455 = 576683) B576683
theorem B1171207 : Blo 255820 1171207 := bstep (se 1 (by rfl) ⟨878405, by rfl⟩ : syracuseStep 1171207 = 1756811) B1756811
theorem B384809 : Blo 255820 384809 := bstep (se 2 (by rfl) ⟨144303, by rfl⟩ : syracuseStep 384809 = 288607) B288607
theorem B581417 : Blo 255820 581417 := bstep (se 2 (by rfl) ⟨218031, by rfl⟩ : syracuseStep 581417 = 436063) B436063
theorem B384815 : Blo 255820 384815 := bstep (se 1 (by rfl) ⟨288611, by rfl⟩ : syracuseStep 384815 = 577223) B577223
theorem B7561349 : Blo 255820 7561349 := bstep (se 4 (by rfl) ⟨708876, by rfl⟩ : syracuseStep 7561349 = 1417753) B1417753
theorem B385289 : Blo 255820 385289 := bstep (se 2 (by rfl) ⟨144483, by rfl⟩ : syracuseStep 385289 = 288967) B288967
theorem B385391 : Blo 255820 385391 := bstep (se 1 (by rfl) ⟨289043, by rfl⟩ : syracuseStep 385391 = 578087) B578087
theorem B647635 : Blo 255820 647635 := bstep (se 1 (by rfl) ⟨485726, by rfl⟩ : syracuseStep 647635 = 971453) B971453
theorem B2777611 : Blo 255820 2777611 := bstep (se 1 (by rfl) ⟨2083208, by rfl⟩ : syracuseStep 2777611 = 4166417) B4166417
theorem B385607 : Blo 255820 385607 := bstep (se 1 (by rfl) ⟨289205, by rfl⟩ : syracuseStep 385607 = 578411) B578411
theorem B385643 : Blo 255820 385643 := bstep (se 1 (by rfl) ⟨289232, by rfl⟩ : syracuseStep 385643 = 578465) B578465
theorem B1499795 : Blo 255820 1499795 := bstep (se 1 (by rfl) ⟨1124846, by rfl⟩ : syracuseStep 1499795 = 2249693) B2249693
theorem B1303289 : Blo 255820 1303289 := bstep (se 2 (by rfl) ⟨488733, by rfl⟩ : syracuseStep 1303289 = 977467) B977467
theorem B385871 : Blo 255820 385871 := bstep (se 1 (by rfl) ⟨289403, by rfl⟩ : syracuseStep 385871 = 578807) B578807
theorem B582479 : Blo 255820 582479 := bstep (se 1 (by rfl) ⟨436859, by rfl⟩ : syracuseStep 582479 = 873719) B873719
theorem B582695 : Blo 255820 582695 := bstep (se 1 (by rfl) ⟨437021, by rfl⟩ : syracuseStep 582695 = 874043) B874043
theorem B1107101 : Blo 255820 1107101 := bstep (se 3 (by rfl) ⟨207581, by rfl⟩ : syracuseStep 1107101 = 415163) B415163
theorem B713927 : Blo 255820 713927 := bstep (se 1 (by rfl) ⟨535445, by rfl⟩ : syracuseStep 713927 = 1070891) B1070891
theorem B386267 : Blo 255820 386267 := bstep (se 1 (by rfl) ⟨289700, by rfl⟩ : syracuseStep 386267 = 579401) B579401
theorem B582875 : Blo 255820 582875 := bstep (se 1 (by rfl) ⟨437156, by rfl⟩ : syracuseStep 582875 = 874313) B874313
theorem B648425 : Blo 255820 648425 := bstep (se 2 (by rfl) ⟨243159, by rfl⟩ : syracuseStep 648425 = 486319) B486319
theorem B288031 : Blo 255820 288031 := bstep (se 1 (by rfl) ⟨216023, by rfl⟩ : syracuseStep 288031 = 432047) B432047
theorem B1992023 : Blo 255820 1992023 := bstep (se 1 (by rfl) ⟨1494017, by rfl⟩ : syracuseStep 1992023 = 2988035) B2988035
theorem B1402217 : Blo 255820 1402217 := bstep (se 2 (by rfl) ⟨525831, by rfl⟩ : syracuseStep 1402217 = 1051663) B1051663
theorem B386441 : Blo 255820 386441 := bstep (se 2 (by rfl) ⟨144915, by rfl⟩ : syracuseStep 386441 = 289831) B289831
theorem B648587 : Blo 255820 648587 := bstep (se 1 (by rfl) ⟨486440, by rfl⟩ : syracuseStep 648587 = 972881) B972881
theorem B583073 : Blo 255820 583073 := bstep (se 2 (by rfl) ⟨218652, by rfl⟩ : syracuseStep 583073 = 437305) B437305
theorem B288319 : Blo 255820 288319 := bstep (se 1 (by rfl) ⟨216239, by rfl⟩ : syracuseStep 288319 = 432479) B432479
theorem B386795 : Blo 255820 386795 := bstep (se 1 (by rfl) ⟨290096, by rfl⟩ : syracuseStep 386795 = 580193) B580193
theorem B255899 : Blo 255820 255899 := bstep (se 1 (by rfl) ⟨191924, by rfl⟩ : syracuseStep 255899 = 383849) B383849
theorem B255951 : Blo 255820 255951 := bstep (se 1 (by rfl) ⟨191963, by rfl⟩ : syracuseStep 255951 = 383927) B383927
theorem B1468367 : Blo 255820 1468367 := bstep (se 1 (by rfl) ⟨1101275, by rfl⟩ : syracuseStep 1468367 = 2202551) B2202551
theorem B4679633 : Blo 255820 4679633 := bstep (se 2 (by rfl) ⟨1754862, by rfl⟩ : syracuseStep 4679633 = 3509725) B3509725
theorem B387023 : Blo 255820 387023 := bstep (se 1 (by rfl) ⟨290267, by rfl⟩ : syracuseStep 387023 = 580535) B580535
theorem B583631 : Blo 255820 583631 := bstep (se 1 (by rfl) ⟨437723, by rfl⟩ : syracuseStep 583631 = 875447) B875447
theorem B255975 : Blo 255820 255975 := bstep (se 1 (by rfl) ⟨191981, by rfl⟩ : syracuseStep 255975 = 383963) B383963
theorem B1566985 : Blo 255820 1566985 := bstep (se 2 (by rfl) ⟨587619, by rfl⟩ : syracuseStep 1566985 = 1175239) B1175239
theorem B616729 : Blo 255820 616729 := bstep (se 2 (by rfl) ⟨231273, by rfl⟩ : syracuseStep 616729 = 462547) B462547
theorem B256287 : Blo 255820 256287 := bstep (se 1 (by rfl) ⟨192215, by rfl⟩ : syracuseStep 256287 = 384431) B384431
theorem B3729725 : Blo 255820 3729725 := bstep (se 3 (by rfl) ⟨699323, by rfl⟩ : syracuseStep 3729725 = 1398647) B1398647
theorem B584009 : Blo 255820 584009 := bstep (se 2 (by rfl) ⟨219003, by rfl⟩ : syracuseStep 584009 = 438007) B438007
theorem B256347 : Blo 255820 256347 := bstep (se 1 (by rfl) ⟨192260, by rfl⟩ : syracuseStep 256347 = 384521) B384521
theorem B387419 : Blo 255820 387419 := bstep (se 1 (by rfl) ⟨290564, by rfl⟩ : syracuseStep 387419 = 581129) B581129
theorem B584027 : Blo 255820 584027 := bstep (se 1 (by rfl) ⟨438020, by rfl⟩ : syracuseStep 584027 = 876041) B876041
theorem B649579 : Blo 255820 649579 := bstep (se 1 (by rfl) ⟨487184, by rfl⟩ : syracuseStep 649579 = 974369) B974369
theorem B256367 : Blo 255820 256367 := bstep (se 1 (by rfl) ⟨192275, by rfl⟩ : syracuseStep 256367 = 384551) B384551
theorem B551279 : Blo 255820 551279 := bstep (se 1 (by rfl) ⟨413459, by rfl⟩ : syracuseStep 551279 = 826919) B826919
theorem B289147 : Blo 255820 289147 := bstep (se 1 (by rfl) ⟨216860, by rfl⟩ : syracuseStep 289147 = 433721) B433721
theorem B256423 : Blo 255820 256423 := bstep (se 1 (by rfl) ⟨192317, by rfl⟩ : syracuseStep 256423 = 384635) B384635
theorem B256507 : Blo 255820 256507 := bstep (se 1 (by rfl) ⟨192380, by rfl⟩ : syracuseStep 256507 = 384761) B384761
theorem B256575 : Blo 255820 256575 := bstep (se 1 (by rfl) ⟨192431, by rfl⟩ : syracuseStep 256575 = 384863) B384863
theorem B387647 : Blo 255820 387647 := bstep (se 1 (by rfl) ⟨290735, by rfl⟩ : syracuseStep 387647 = 581471) B581471
theorem B256583 : Blo 255820 256583 := bstep (se 1 (by rfl) ⟨192437, by rfl⟩ : syracuseStep 256583 = 384875) B384875
theorem B649903 : Blo 255820 649903 := bstep (se 1 (by rfl) ⟨487427, by rfl⟩ : syracuseStep 649903 = 974855) B974855
theorem B387767 : Blo 255820 387767 := bstep (se 1 (by rfl) ⟨290825, by rfl⟩ : syracuseStep 387767 = 581651) B581651
theorem B1469117 : Blo 255820 1469117 := bstep (se 3 (by rfl) ⟨275459, by rfl⟩ : syracuseStep 1469117 = 550919) B550919
theorem B256735 : Blo 255820 256735 := bstep (se 1 (by rfl) ⟨192551, by rfl⟩ : syracuseStep 256735 = 385103) B385103
theorem B256815 : Blo 255820 256815 := bstep (se 1 (by rfl) ⟨192611, by rfl⟩ : syracuseStep 256815 = 385223) B385223
theorem B4188995 : Blo 255820 4188995 := bstep (se 1 (by rfl) ⟨3141746, by rfl⟩ : syracuseStep 4188995 = 6283493) B6283493
theorem B289615 : Blo 255820 289615 := bstep (se 1 (by rfl) ⟨217211, by rfl⟩ : syracuseStep 289615 = 434423) B434423
theorem B256923 : Blo 255820 256923 := bstep (se 1 (by rfl) ⟨192692, by rfl⟩ : syracuseStep 256923 = 385385) B385385
theorem B387995 : Blo 255820 387995 := bstep (se 1 (by rfl) ⟨290996, by rfl⟩ : syracuseStep 387995 = 581993) B581993
theorem B256975 : Blo 255820 256975 := bstep (se 1 (by rfl) ⟨192731, by rfl⟩ : syracuseStep 256975 = 385463) B385463
theorem B256999 : Blo 255820 256999 := bstep (se 1 (by rfl) ⟨192749, by rfl⟩ : syracuseStep 256999 = 385499) B385499
theorem B650227 : Blo 255820 650227 := bstep (se 1 (by rfl) ⟨487670, by rfl⟩ : syracuseStep 650227 = 975341) B975341
theorem B584801 : Blo 255820 584801 := bstep (se 2 (by rfl) ⟨219300, by rfl⟩ : syracuseStep 584801 = 438601) B438601
theorem B290011 : Blo 255820 290011 := bstep (se 1 (by rfl) ⟨217508, by rfl⟩ : syracuseStep 290011 = 435017) B435017
theorem B257311 : Blo 255820 257311 := bstep (se 1 (by rfl) ⟨192983, by rfl⟩ : syracuseStep 257311 = 385967) B385967
theorem B388391 : Blo 255820 388391 := bstep (se 1 (by rfl) ⟨291293, by rfl⟩ : syracuseStep 388391 = 582587) B582587
theorem B257371 : Blo 255820 257371 := bstep (se 1 (by rfl) ⟨193028, by rfl⟩ : syracuseStep 257371 = 386057) B386057
theorem B257391 : Blo 255820 257391 := bstep (se 1 (by rfl) ⟨193043, by rfl⟩ : syracuseStep 257391 = 386087) B386087
theorem B388475 : Blo 255820 388475 := bstep (se 1 (by rfl) ⟨291356, by rfl⟩ : syracuseStep 388475 = 582713) B582713
theorem B1469825 : Blo 255820 1469825 := bstep (se 2 (by rfl) ⟨551184, by rfl⟩ : syracuseStep 1469825 = 1102369) B1102369
theorem B257447 : Blo 255820 257447 := bstep (se 1 (by rfl) ⟨193085, by rfl⟩ : syracuseStep 257447 = 386171) B386171
theorem B1306043 : Blo 255820 1306043 := bstep (se 1 (by rfl) ⟨979532, by rfl⟩ : syracuseStep 1306043 = 1959065) B1959065
theorem B978425 : Blo 255820 978425 := bstep (se 2 (by rfl) ⟨366909, by rfl⟩ : syracuseStep 978425 = 733819) B733819
theorem B388601 : Blo 255820 388601 := bstep (se 2 (by rfl) ⟨145725, by rfl⟩ : syracuseStep 388601 = 291451) B291451
theorem B257531 : Blo 255820 257531 := bstep (se 1 (by rfl) ⟨193148, by rfl⟩ : syracuseStep 257531 = 386297) B386297
theorem B290299 : Blo 255820 290299 := bstep (se 1 (by rfl) ⟨217724, by rfl⟩ : syracuseStep 290299 = 435449) B435449
theorem B257599 : Blo 255820 257599 := bstep (se 1 (by rfl) ⟨193199, by rfl⟩ : syracuseStep 257599 = 386399) B386399
theorem B257607 : Blo 255820 257607 := bstep (se 1 (by rfl) ⟨193205, by rfl⟩ : syracuseStep 257607 = 386411) B386411
theorem B388703 : Blo 255820 388703 := bstep (se 1 (by rfl) ⟨291527, by rfl⟩ : syracuseStep 388703 = 583055) B583055
theorem B290479 : Blo 255820 290479 := bstep (se 1 (by rfl) ⟨217859, by rfl⟩ : syracuseStep 290479 = 435719) B435719
theorem B257759 : Blo 255820 257759 := bstep (se 1 (by rfl) ⟨193319, by rfl⟩ : syracuseStep 257759 = 386639) B386639
theorem B487147 : Blo 255820 487147 := bstep (se 1 (by rfl) ⟨365360, by rfl⟩ : syracuseStep 487147 = 730721) B730721
theorem B650987 : Blo 255820 650987 := bstep (se 1 (by rfl) ⟨488240, by rfl⟩ : syracuseStep 650987 = 976481) B976481
theorem B1109801 : Blo 255820 1109801 := bstep (se 2 (by rfl) ⟨416175, by rfl⟩ : syracuseStep 1109801 = 832351) B832351
theorem B257839 : Blo 255820 257839 := bstep (se 1 (by rfl) ⟨193379, by rfl⟩ : syracuseStep 257839 = 386759) B386759
theorem B388919 : Blo 255820 388919 := bstep (se 1 (by rfl) ⟨291689, by rfl⟩ : syracuseStep 388919 = 583379) B583379
theorem B257947 : Blo 255820 257947 := bstep (se 1 (by rfl) ⟨193460, by rfl⟩ : syracuseStep 257947 = 386921) B386921
theorem B257999 : Blo 255820 257999 := bstep (se 1 (by rfl) ⟨193499, by rfl⟩ : syracuseStep 257999 = 386999) B386999
theorem B290767 : Blo 255820 290767 := bstep (se 1 (by rfl) ⟨218075, by rfl⟩ : syracuseStep 290767 = 436151) B436151
theorem B258023 : Blo 255820 258023 := bstep (se 1 (by rfl) ⟨193517, by rfl⟩ : syracuseStep 258023 = 387035) B387035
theorem B389225 : Blo 255820 389225 := bstep (se 2 (by rfl) ⟨145959, by rfl⟩ : syracuseStep 389225 = 291919) B291919
theorem B258335 : Blo 255820 258335 := bstep (se 1 (by rfl) ⟨193751, by rfl⟩ : syracuseStep 258335 = 387503) B387503
theorem B4157729 : Blo 255820 4157729 := bstep (se 2 (by rfl) ⟨1559148, by rfl⟩ : syracuseStep 4157729 = 3118297) B3118297
theorem B258395 : Blo 255820 258395 := bstep (se 1 (by rfl) ⟨193796, by rfl⟩ : syracuseStep 258395 = 387593) B387593
theorem B291163 : Blo 255820 291163 := bstep (se 1 (by rfl) ⟨218372, by rfl⟩ : syracuseStep 291163 = 436745) B436745
theorem B258415 : Blo 255820 258415 := bstep (se 1 (by rfl) ⟨193811, by rfl⟩ : syracuseStep 258415 = 387623) B387623
theorem B258471 : Blo 255820 258471 := bstep (se 1 (by rfl) ⟨193853, by rfl⟩ : syracuseStep 258471 = 387707) B387707
theorem B389543 : Blo 255820 389543 := bstep (se 1 (by rfl) ⟨292157, by rfl⟩ : syracuseStep 389543 = 584315) B584315
theorem B291271 : Blo 255820 291271 := bstep (se 1 (by rfl) ⟨218453, by rfl⟩ : syracuseStep 291271 = 436907) B436907
theorem B520673 : Blo 255820 520673 := bstep (se 2 (by rfl) ⟨195252, by rfl⟩ : syracuseStep 520673 = 390505) B390505
theorem B324091 : Blo 255820 324091 := bstep (se 1 (by rfl) ⟨243068, by rfl⟩ : syracuseStep 324091 = 486137) B486137
theorem B258555 : Blo 255820 258555 := bstep (se 1 (by rfl) ⟨193916, by rfl⟩ : syracuseStep 258555 = 387833) B387833
theorem B389627 : Blo 255820 389627 := bstep (se 1 (by rfl) ⟨292220, by rfl⟩ : syracuseStep 389627 = 584441) B584441
theorem B258623 : Blo 255820 258623 := bstep (se 1 (by rfl) ⟨193967, by rfl⟩ : syracuseStep 258623 = 387935) B387935
theorem B651847 : Blo 255820 651847 := bstep (se 1 (by rfl) ⟨488885, by rfl⟩ : syracuseStep 651847 = 977771) B977771
theorem B258631 : Blo 255820 258631 := bstep (se 1 (by rfl) ⟨193973, by rfl⟩ : syracuseStep 258631 = 387947) B387947
theorem B488119 : Blo 255820 488119 := bstep (se 1 (by rfl) ⟨366089, by rfl⟩ : syracuseStep 488119 = 732179) B732179
theorem B651959 : Blo 255820 651959 := bstep (se 1 (by rfl) ⟨488969, by rfl⟩ : syracuseStep 651959 = 977939) B977939
theorem B1307339 : Blo 255820 1307339 := bstep (se 1 (by rfl) ⟨980504, by rfl⟩ : syracuseStep 1307339 = 1961009) B1961009
theorem B324319 : Blo 255820 324319 := bstep (se 1 (by rfl) ⟨243239, by rfl⟩ : syracuseStep 324319 = 486479) B486479
theorem B258783 : Blo 255820 258783 := bstep (se 1 (by rfl) ⟨194087, by rfl⟩ : syracuseStep 258783 = 388175) B388175
theorem B586487 : Blo 255820 586487 := bstep (se 1 (by rfl) ⟨439865, by rfl⟩ : syracuseStep 586487 = 879731) B879731
theorem B258863 : Blo 255820 258863 := bstep (se 1 (by rfl) ⟨194147, by rfl⟩ : syracuseStep 258863 = 388295) B388295
theorem B291631 : Blo 255820 291631 := bstep (se 1 (by rfl) ⟨218723, by rfl⟩ : syracuseStep 291631 = 437447) B437447
theorem B619343 : Blo 255820 619343 := bstep (se 1 (by rfl) ⟨464507, by rfl⟩ : syracuseStep 619343 = 929015) B929015
theorem B553807 : Blo 255820 553807 := bstep (se 1 (by rfl) ⟨415355, by rfl⟩ : syracuseStep 553807 = 830711) B830711
theorem B1307501 : Blo 255820 1307501 := bstep (se 3 (by rfl) ⟨245156, by rfl⟩ : syracuseStep 1307501 = 490313) B490313
theorem B258971 : Blo 255820 258971 := bstep (se 1 (by rfl) ⟨194228, by rfl⟩ : syracuseStep 258971 = 388457) B388457
theorem B291739 : Blo 255820 291739 := bstep (se 1 (by rfl) ⟨218804, by rfl⟩ : syracuseStep 291739 = 437609) B437609
theorem B1962953 : Blo 255820 1962953 := bstep (se 2 (by rfl) ⟨736107, by rfl⟩ : syracuseStep 1962953 = 1472215) B1472215
theorem B259023 : Blo 255820 259023 := bstep (se 1 (by rfl) ⟨194267, by rfl⟩ : syracuseStep 259023 = 388535) B388535
theorem B1864657 : Blo 255820 1864657 := bstep (se 2 (by rfl) ⟨699246, by rfl⟩ : syracuseStep 1864657 = 1398493) B1398493
theorem B586727 : Blo 255820 586727 := bstep (se 1 (by rfl) ⟨440045, by rfl⟩ : syracuseStep 586727 = 880091) B880091
theorem B488423 : Blo 255820 488423 := bstep (se 1 (by rfl) ⟨366317, by rfl⟩ : syracuseStep 488423 = 732635) B732635
theorem B259047 : Blo 255820 259047 := bstep (se 1 (by rfl) ⟨194285, by rfl⟩ : syracuseStep 259047 = 388571) B388571
theorem B2487287 : Blo 255820 2487287 := bstep (se 1 (by rfl) ⟨1865465, by rfl⟩ : syracuseStep 2487287 = 3730931) B3730931
theorem B980201 : Blo 255820 980201 := bstep (se 2 (by rfl) ⟨367575, by rfl⟩ : syracuseStep 980201 = 735151) B735151
theorem B2782457 : Blo 255820 2782457 := bstep (se 2 (by rfl) ⟨1043421, by rfl⟩ : syracuseStep 2782457 = 2086843) B2086843
theorem B259359 : Blo 255820 259359 := bstep (se 1 (by rfl) ⟨194519, by rfl⟩ : syracuseStep 259359 = 389039) B389039
theorem B947495 : Blo 255820 947495 := bstep (se 1 (by rfl) ⟨710621, by rfl⟩ : syracuseStep 947495 = 1421243) B1421243
theorem B292135 : Blo 255820 292135 := bstep (se 1 (by rfl) ⟨219101, by rfl⟩ : syracuseStep 292135 = 438203) B438203
theorem B259419 : Blo 255820 259419 := bstep (se 1 (by rfl) ⟨194564, by rfl⟩ : syracuseStep 259419 = 389129) B389129
theorem B259439 : Blo 255820 259439 := bstep (se 1 (by rfl) ⟨194579, by rfl⟩ : syracuseStep 259439 = 389159) B389159
theorem B292207 : Blo 255820 292207 := bstep (se 1 (by rfl) ⟨219155, by rfl⟩ : syracuseStep 292207 = 438311) B438311
theorem B259495 : Blo 255820 259495 := bstep (se 1 (by rfl) ⟨194621, by rfl⟩ : syracuseStep 259495 = 389243) B389243
theorem B292295 : Blo 255820 292295 := bstep (se 1 (by rfl) ⟨219221, by rfl⟩ : syracuseStep 292295 = 438443) B438443
theorem B325063 : Blo 255820 325063 := bstep (se 1 (by rfl) ⟨243797, by rfl⟩ : syracuseStep 325063 = 487595) B487595
theorem B259579 : Blo 255820 259579 := bstep (se 1 (by rfl) ⟨194684, by rfl⟩ : syracuseStep 259579 = 389369) B389369
theorem B2094599 : Blo 255820 2094599 := bstep (se 1 (by rfl) ⟨1570949, by rfl⟩ : syracuseStep 2094599 = 3141899) B3141899
theorem B259647 : Blo 255820 259647 := bstep (se 1 (by rfl) ⟨194735, by rfl⟩ : syracuseStep 259647 = 389471) B389471
theorem B259655 : Blo 255820 259655 := bstep (se 1 (by rfl) ⟨194741, by rfl⟩ : syracuseStep 259655 = 389483) B389483
theorem B652961 : Blo 255820 652961 := bstep (se 2 (by rfl) ⟨244860, by rfl⟩ : syracuseStep 652961 = 489721) B489721
theorem B259807 : Blo 255820 259807 := bstep (se 1 (by rfl) ⟨194855, by rfl⟩ : syracuseStep 259807 = 389711) B389711
theorem B1242935 : Blo 255820 1242935 := bstep (se 1 (by rfl) ⟨932201, by rfl⟩ : syracuseStep 1242935 = 1864403) B1864403
theorem B489577 : Blo 255820 489577 := bstep (se 2 (by rfl) ⟨183591, by rfl⟩ : syracuseStep 489577 = 367183) B367183
theorem B653417 : Blo 255820 653417 := bstep (se 2 (by rfl) ⟨245031, by rfl⟩ : syracuseStep 653417 = 490063) B490063
theorem B260443 : Blo 255820 260443 := bstep (se 1 (by rfl) ⟨195332, by rfl⟩ : syracuseStep 260443 = 390665) B390665
theorem B522587 : Blo 255820 522587 := bstep (se 1 (by rfl) ⟨391940, by rfl⟩ : syracuseStep 522587 = 783881) B783881
theorem B1505719 : Blo 255820 1505719 := bstep (se 1 (by rfl) ⟨1129289, by rfl⟩ : syracuseStep 1505719 = 2258579) B2258579
theorem B293371 : Blo 255820 293371 := bstep (se 1 (by rfl) ⟨220028, by rfl⟩ : syracuseStep 293371 = 440057) B440057
theorem B489979 : Blo 255820 489979 := bstep (se 1 (by rfl) ⟨367484, by rfl⟩ : syracuseStep 489979 = 734969) B734969
theorem B326207 : Blo 255820 326207 := bstep (se 1 (by rfl) ⟨244655, by rfl⟩ : syracuseStep 326207 = 489311) B489311
theorem B5306953 : Blo 255820 5306953 := bstep (se 2 (by rfl) ⟨1990107, by rfl⟩ : syracuseStep 5306953 = 3980215) B3980215
theorem B653903 : Blo 255820 653903 := bstep (se 1 (by rfl) ⟨490427, by rfl⟩ : syracuseStep 653903 = 980855) B980855
theorem B490207 : Blo 255820 490207 := bstep (se 1 (by rfl) ⟨367655, by rfl⟩ : syracuseStep 490207 = 735311) B735311
theorem B392015 : Blo 255820 392015 := bstep (se 1 (by rfl) ⟨294011, by rfl⟩ : syracuseStep 392015 = 588023) B588023
theorem B5307281 : Blo 255820 5307281 := bstep (se 2 (by rfl) ⟨1990230, by rfl⟩ : syracuseStep 5307281 = 3980461) B3980461
theorem B2194451 : Blo 255820 2194451 := bstep (se 1 (by rfl) ⟨1645838, by rfl⟩ : syracuseStep 2194451 = 3291677) B3291677
theorem B9993239 : Blo 255820 9993239 := bstep (se 1 (by rfl) ⟨7494929, by rfl⟩ : syracuseStep 9993239 = 14989859) B14989859
theorem B654551 : Blo 255820 654551 := bstep (se 1 (by rfl) ⟨490913, by rfl⟩ : syracuseStep 654551 = 981827) B981827
theorem B490951 : Blo 255820 490951 := bstep (se 1 (by rfl) ⟨368213, by rfl⟩ : syracuseStep 490951 = 736427) B736427
theorem B654905 : Blo 255820 654905 := bstep (se 2 (by rfl) ⟨245589, by rfl⟩ : syracuseStep 654905 = 491179) B491179
theorem B1310417 : Blo 255820 1310417 := bstep (se 2 (by rfl) ⟨491406, by rfl⟩ : syracuseStep 1310417 = 982813) B982813
theorem B2490173 : Blo 255820 2490173 := bstep (se 3 (by rfl) ⟨466907, by rfl⟩ : syracuseStep 2490173 = 933815) B933815
theorem B327503 : Blo 255820 327503 := bstep (se 1 (by rfl) ⟨245627, by rfl⟩ : syracuseStep 327503 = 491255) B491255
theorem B327655 : Blo 255820 327655 := bstep (se 1 (by rfl) ⟨245741, by rfl⟩ : syracuseStep 327655 = 491483) B491483
theorem B10485811 : Blo 255820 10485811 := bstep (se 1 (by rfl) ⟨7864358, by rfl⟩ : syracuseStep 10485811 = 15728717) B15728717
theorem B9470189 : Blo 255820 9470189 := bstep (se 3 (by rfl) ⟨1775660, by rfl⟩ : syracuseStep 9470189 = 3551321) B3551321
theorem B2195963 : Blo 255820 2195963 := bstep (se 1 (by rfl) ⟨1646972, by rfl⟩ : syracuseStep 2195963 = 3293945) B3293945
theorem B1311227 : Blo 255820 1311227 := bstep (se 1 (by rfl) ⟨983420, by rfl⟩ : syracuseStep 1311227 = 1966841) B1966841
theorem B3703481 : Blo 255820 3703481 := bstep (se 2 (by rfl) ⟨1388805, by rfl⟩ : syracuseStep 3703481 = 2777611) B2777611
theorem B492455 : Blo 255820 492455 := bstep (se 1 (by rfl) ⟨369341, by rfl⟩ : syracuseStep 492455 = 738683) B738683
theorem B1476407 : Blo 255820 1476407 := bstep (se 1 (by rfl) ⟨1107305, by rfl⟩ : syracuseStep 1476407 = 2214611) B2214611
theorem B2950991 : Blo 255820 2950991 := bstep (se 1 (by rfl) ⟨2213243, by rfl⟩ : syracuseStep 2950991 = 4426487) B4426487
theorem B985031 : Blo 255820 985031 := bstep (se 1 (by rfl) ⟨738773, by rfl⟩ : syracuseStep 985031 = 1477547) B1477547
theorem B591815 : Blo 255820 591815 := bstep (se 1 (by rfl) ⟨443861, by rfl⟩ : syracuseStep 591815 = 887723) B887723
theorem B4917833 : Blo 255820 4917833 := bstep (se 2 (by rfl) ⟨1844187, by rfl⟩ : syracuseStep 4917833 = 3688375) B3688375
theorem B1968785 : Blo 255820 1968785 := bstep (se 2 (by rfl) ⟨738294, by rfl⟩ : syracuseStep 1968785 = 1476589) B1476589
theorem B10029719 : Blo 255820 10029719 := bstep (se 1 (by rfl) ⟨7522289, by rfl⟩ : syracuseStep 10029719 = 15044579) B15044579
theorem B1313495 : Blo 255820 1313495 := bstep (se 1 (by rfl) ⟨985121, by rfl⟩ : syracuseStep 1313495 = 1970243) B1970243
theorem B822305 : Blo 255820 822305 := bstep (se 2 (by rfl) ⟨308364, by rfl⟩ : syracuseStep 822305 = 616729) B616729
theorem B494927 : Blo 255820 494927 := bstep (se 1 (by rfl) ⟨371195, by rfl⟩ : syracuseStep 494927 = 742391) B742391
theorem B2526653 : Blo 255820 2526653 := bstep (se 3 (by rfl) ⟨473747, by rfl⟩ : syracuseStep 2526653 = 947495) B947495
theorem B2461265 : Blo 255820 2461265 := bstep (se 2 (by rfl) ⟨922974, by rfl⟩ : syracuseStep 2461265 = 1845949) B1845949
theorem B462763 : Blo 255820 462763 := bstep (se 1 (by rfl) ⟨347072, by rfl⟩ : syracuseStep 462763 = 694145) B694145
theorem B3706829 : Blo 255820 3706829 := bstep (se 3 (by rfl) ⟨695030, by rfl⟩ : syracuseStep 3706829 = 1390061) B1390061
theorem B1184215 : Blo 255820 1184215 := bstep (se 1 (by rfl) ⟨888161, by rfl⟩ : syracuseStep 1184215 = 1776323) B1776323
theorem B1971215 : Blo 255820 1971215 := bstep (se 1 (by rfl) ⟨1478411, by rfl⟩ : syracuseStep 1971215 = 2956823) B2956823
theorem B4199633 : Blo 255820 4199633 := bstep (se 2 (by rfl) ⟨1574862, by rfl⟩ : syracuseStep 4199633 = 3149725) B3149725
theorem B464147 : Blo 255820 464147 := bstep (se 1 (by rfl) ⟨348110, by rfl⟩ : syracuseStep 464147 = 696221) B696221
theorem B3151673 : Blo 255820 3151673 := bstep (se 2 (by rfl) ⟨1181877, by rfl⟩ : syracuseStep 3151673 = 2363755) B2363755
theorem B432121 : Blo 255820 432121 := bstep (se 2 (by rfl) ⟨162045, by rfl⟩ : syracuseStep 432121 = 324091) B324091
theorem B432283 : Blo 255820 432283 := bstep (se 1 (by rfl) ⟨324212, by rfl⟩ : syracuseStep 432283 = 648425) B648425
theorem B432391 : Blo 255820 432391 := bstep (se 1 (by rfl) ⟨324293, by rfl⟩ : syracuseStep 432391 = 648587) B648587
theorem B432425 : Blo 255820 432425 := bstep (se 2 (by rfl) ⟨162159, by rfl⟩ : syracuseStep 432425 = 324319) B324319
theorem B1055099 : Blo 255820 1055099 := bstep (se 1 (by rfl) ⟨791324, by rfl⟩ : syracuseStep 1055099 = 1582649) B1582649
theorem B1645019 : Blo 255820 1645019 := bstep (se 1 (by rfl) ⟨1233764, by rfl⟩ : syracuseStep 1645019 = 2467529) B2467529
theorem B924317 : Blo 255820 924317 := bstep (se 3 (by rfl) ⟨173309, by rfl⟩ : syracuseStep 924317 = 346619) B346619
theorem B367519 : Blo 255820 367519 := bstep (se 1 (by rfl) ⟨275639, by rfl⟩ : syracuseStep 367519 = 551279) B551279
theorem B2104265 : Blo 255820 2104265 := bstep (se 2 (by rfl) ⟨789099, by rfl⟩ : syracuseStep 2104265 = 1578199) B1578199
theorem B2792663 : Blo 255820 2792663 := bstep (se 1 (by rfl) ⟨2094497, by rfl⟩ : syracuseStep 2792663 = 4188995) B4188995
theorem B433417 : Blo 255820 433417 := bstep (se 2 (by rfl) ⟨162531, by rfl⟩ : syracuseStep 433417 = 325063) B325063
theorem B925409 : Blo 255820 925409 := bstep (se 2 (by rfl) ⟨347028, by rfl⟩ : syracuseStep 925409 = 694057) B694057
theorem B925511 : Blo 255820 925511 := bstep (se 1 (by rfl) ⟨694133, by rfl⟩ : syracuseStep 925511 = 1388267) B1388267
theorem B433991 : Blo 255820 433991 := bstep (se 1 (by rfl) ⟨325493, by rfl⟩ : syracuseStep 433991 = 650987) B650987
theorem B729319 : Blo 255820 729319 := bstep (se 1 (by rfl) ⟨546989, by rfl⟩ : syracuseStep 729319 = 1093979) B1093979
theorem B434639 : Blo 255820 434639 := bstep (se 1 (by rfl) ⟨325979, by rfl⟩ : syracuseStep 434639 = 651959) B651959
theorem B2007625 : Blo 255820 2007625 := bstep (se 2 (by rfl) ⟨752859, by rfl⟩ : syracuseStep 2007625 = 1505719) B1505719
theorem B435307 : Blo 255820 435307 := bstep (se 1 (by rfl) ⟨326480, by rfl⟩ : syracuseStep 435307 = 652961) B652961
theorem B828623 : Blo 255820 828623 := bstep (se 1 (by rfl) ⟨621467, by rfl⟩ : syracuseStep 828623 = 1242935) B1242935
theorem B435611 : Blo 255820 435611 := bstep (se 1 (by rfl) ⟨326708, by rfl⟩ : syracuseStep 435611 = 653417) B653417
theorem B435935 : Blo 255820 435935 := bstep (se 1 (by rfl) ⟨326951, by rfl⟩ : syracuseStep 435935 = 653903) B653903
theorem B6662159 : Blo 255820 6662159 := bstep (se 1 (by rfl) ⟨4996619, by rfl⟩ : syracuseStep 6662159 = 9993239) B9993239
theorem B436367 : Blo 255820 436367 := bstep (se 1 (by rfl) ⟨327275, by rfl⟩ : syracuseStep 436367 = 654551) B654551
theorem B436603 : Blo 255820 436603 := bstep (se 1 (by rfl) ⟨327452, by rfl⟩ : syracuseStep 436603 = 654905) B654905
theorem B436873 : Blo 255820 436873 := bstep (se 2 (by rfl) ⟨163827, by rfl⟩ : syracuseStep 436873 = 327655) B327655
theorem B830263 : Blo 255820 830263 := bstep (se 1 (by rfl) ⟨622697, by rfl⟩ : syracuseStep 830263 = 1245395) B1245395
theorem B2927663 : Blo 255820 2927663 := bstep (se 1 (by rfl) ⟨2195747, by rfl⟩ : syracuseStep 2927663 = 4391495) B4391495
theorem B863513 : Blo 255820 863513 := bstep (se 2 (by rfl) ⟨323817, by rfl⟩ : syracuseStep 863513 = 647635) B647635
theorem B863567 : Blo 255820 863567 := bstep (se 1 (by rfl) ⟨647675, by rfl⟩ : syracuseStep 863567 = 1295351) B1295351
theorem B2994029 : Blo 255820 2994029 := bstep (se 3 (by rfl) ⟨561380, by rfl⟩ : syracuseStep 2994029 = 1122761) B1122761
theorem B1388461 : Blo 255820 1388461 := bstep (se 3 (by rfl) ⟨260336, by rfl⟩ : syracuseStep 1388461 = 520673) B520673
theorem B831455 : Blo 255820 831455 := bstep (se 1 (by rfl) ⟨623591, by rfl⟩ : syracuseStep 831455 = 1247183) B1247183
theorem B864863 : Blo 255820 864863 := bstep (se 1 (by rfl) ⟨648647, by rfl⟩ : syracuseStep 864863 = 1297295) B1297295
theorem B866105 : Blo 255820 866105 := bstep (se 2 (by rfl) ⟨324789, by rfl⟩ : syracuseStep 866105 = 649579) B649579
theorem B2799497 : Blo 255820 2799497 := bstep (se 2 (by rfl) ⟨1049811, by rfl⟩ : syracuseStep 2799497 = 2099623) B2099623
theorem B2930579 : Blo 255820 2930579 := bstep (se 1 (by rfl) ⟨2197934, by rfl⟩ : syracuseStep 2930579 = 4395869) B4395869
theorem B1095619 : Blo 255820 1095619 := bstep (se 1 (by rfl) ⟨821714, by rfl⟩ : syracuseStep 1095619 = 1643429) B1643429
theorem B866267 : Blo 255820 866267 := bstep (se 1 (by rfl) ⟨649700, by rfl⟩ : syracuseStep 866267 = 1299401) B1299401
theorem B866537 : Blo 255820 866537 := bstep (se 2 (by rfl) ⟨324951, by rfl⟩ : syracuseStep 866537 = 649903) B649903
theorem B866969 : Blo 255820 866969 := bstep (se 2 (by rfl) ⟨325113, by rfl⟩ : syracuseStep 866969 = 650227) B650227
theorem B5585597 : Blo 255820 5585597 := bstep (se 3 (by rfl) ⟨1047299, by rfl⟩ : syracuseStep 5585597 = 2094599) B2094599
theorem B736381 : Blo 255820 736381 := bstep (se 3 (by rfl) ⟨138071, by rfl⟩ : syracuseStep 736381 = 276143) B276143
theorem B999863 : Blo 255820 999863 := bstep (se 1 (by rfl) ⟨749897, by rfl⟩ : syracuseStep 999863 = 1499795) B1499795
theorem B868859 : Blo 255820 868859 := bstep (se 1 (by rfl) ⟨651644, by rfl⟩ : syracuseStep 868859 = 1303289) B1303289
theorem B2769653 : Blo 255820 2769653 := bstep (se 5 (by rfl) ⟨129827, by rfl⟩ : syracuseStep 2769653 = 259655) B259655
theorem B869129 : Blo 255820 869129 := bstep (se 2 (by rfl) ⟨325923, by rfl⟩ : syracuseStep 869129 = 651847) B651847
theorem B738067 : Blo 255820 738067 := bstep (se 1 (by rfl) ⟨553550, by rfl⟩ : syracuseStep 738067 = 1107101) B1107101
theorem B475951 : Blo 255820 475951 := bstep (se 1 (by rfl) ⟨356963, by rfl⟩ : syracuseStep 475951 = 713927) B713927
theorem B1328015 : Blo 255820 1328015 := bstep (se 1 (by rfl) ⟨996011, by rfl⟩ : syracuseStep 1328015 = 1992023) B1992023
theorem B934811 : Blo 255820 934811 := bstep (se 1 (by rfl) ⟨701108, by rfl⟩ : syracuseStep 934811 = 1402217) B1402217
theorem B410729 : Blo 255820 410729 := bstep (se 2 (by rfl) ⟨154023, by rfl⟩ : syracuseStep 410729 = 308047) B308047
theorem B738409 : Blo 255820 738409 := bstep (se 2 (by rfl) ⟨276903, by rfl⟩ : syracuseStep 738409 = 553807) B553807
theorem B869885 : Blo 255820 869885 := bstep (se 3 (by rfl) ⟨163103, by rfl⟩ : syracuseStep 869885 = 326207) B326207
theorem B1230497 : Blo 255820 1230497 := bstep (se 2 (by rfl) ⟨461436, by rfl⟩ : syracuseStep 1230497 = 922873) B922873
theorem B837473 : Blo 255820 837473 := bstep (se 2 (by rfl) ⟨314052, by rfl⟩ : syracuseStep 837473 = 628105) B628105
theorem B575783 : Blo 255820 575783 := bstep (se 1 (by rfl) ⟨431837, by rfl⟩ : syracuseStep 575783 = 863675) B863675
theorem B870695 : Blo 255820 870695 := bstep (se 1 (by rfl) ⟨653021, by rfl⟩ : syracuseStep 870695 = 1306043) B1306043
theorem B575801 : Blo 255820 575801 := bstep (se 2 (by rfl) ⟨215925, by rfl⟩ : syracuseStep 575801 = 431851) B431851
theorem B739867 : Blo 255820 739867 := bstep (se 1 (by rfl) ⟨554900, by rfl⟩ : syracuseStep 739867 = 1109801) B1109801
theorem B2771819 : Blo 255820 2771819 := bstep (se 1 (by rfl) ⟨2078864, by rfl⟩ : syracuseStep 2771819 = 4157729) B4157729
theorem B347257 : Blo 255820 347257 := bstep (se 2 (by rfl) ⟨130221, by rfl⟩ : syracuseStep 347257 = 260443) B260443
theorem B412793 : Blo 255820 412793 := bstep (se 2 (by rfl) ⟨154797, by rfl⟩ : syracuseStep 412793 = 309595) B309595
theorem B871559 : Blo 255820 871559 := bstep (se 1 (by rfl) ⟨653669, by rfl⟩ : syracuseStep 871559 = 1307339) B1307339
theorem B412895 : Blo 255820 412895 := bstep (se 1 (by rfl) ⟨309671, by rfl⟩ : syracuseStep 412895 = 619343) B619343
theorem B871667 : Blo 255820 871667 := bstep (se 1 (by rfl) ⟨653750, by rfl⟩ : syracuseStep 871667 = 1307501) B1307501
theorem B1658191 : Blo 255820 1658191 := bstep (se 1 (by rfl) ⟨1243643, by rfl⟩ : syracuseStep 1658191 = 2487287) B2487287
theorem B1854971 : Blo 255820 1854971 := bstep (se 1 (by rfl) ⟨1391228, by rfl⟩ : syracuseStep 1854971 = 2782457) B2782457
theorem B577097 : Blo 255820 577097 := bstep (se 2 (by rfl) ⟨216411, by rfl⟩ : syracuseStep 577097 = 432823) B432823
theorem B348391 : Blo 255820 348391 := bstep (se 1 (by rfl) ⟨261293, by rfl⟩ : syracuseStep 348391 = 522587) B522587
theorem B8147249 : Blo 255820 8147249 := bstep (se 2 (by rfl) ⟨3055218, by rfl⟩ : syracuseStep 8147249 = 6110437) B6110437
theorem B1233263 : Blo 255820 1233263 := bstep (se 1 (by rfl) ⟨924947, by rfl⟩ : syracuseStep 1233263 = 1849895) B1849895
theorem B1462967 : Blo 255820 1462967 := bstep (se 1 (by rfl) ⟨1097225, by rfl⟩ : syracuseStep 1462967 = 2194451) B2194451
theorem B1168195 : Blo 255820 1168195 := bstep (se 1 (by rfl) ⟨876146, by rfl⟩ : syracuseStep 1168195 = 1752293) B1752293
theorem B873341 : Blo 255820 873341 := bstep (se 3 (by rfl) ⟨163751, by rfl⟩ : syracuseStep 873341 = 327503) B327503
theorem B578555 : Blo 255820 578555 := bstep (se 1 (by rfl) ⟨433916, by rfl⟩ : syracuseStep 578555 = 867833) B867833
theorem B3527675 : Blo 255820 3527675 := bstep (se 1 (by rfl) ⟨2645756, by rfl⟩ : syracuseStep 3527675 = 5291513) B5291513
theorem B1561609 : Blo 255820 1561609 := bstep (se 2 (by rfl) ⟨585603, by rfl⟩ : syracuseStep 1561609 = 1171207) B1171207
theorem B2413577 : Blo 255820 2413577 := bstep (se 2 (by rfl) ⟨905091, by rfl⟩ : syracuseStep 2413577 = 1810183) B1810183
theorem B1299563 : Blo 255820 1299563 := bstep (se 1 (by rfl) ⟨974672, by rfl⟩ : syracuseStep 1299563 = 1949345) B1949345
theorem B873611 : Blo 255820 873611 := bstep (se 1 (by rfl) ⟨655208, by rfl⟩ : syracuseStep 873611 = 1310417) B1310417
theorem B578735 : Blo 255820 578735 := bstep (se 1 (by rfl) ⟨434051, by rfl⟩ : syracuseStep 578735 = 868103) B868103
theorem B578771 : Blo 255820 578771 := bstep (se 1 (by rfl) ⟨434078, by rfl⟩ : syracuseStep 578771 = 868157) B868157
theorem B1660115 : Blo 255820 1660115 := bstep (se 1 (by rfl) ⟨1245086, by rfl⟩ : syracuseStep 1660115 = 2490173) B2490173
theorem B30365027 : Blo 255820 30365027 := bstep (se 1 (by rfl) ⟨22773770, by rfl⟩ : syracuseStep 30365027 = 45547541) B45547541
theorem B76567949 : Blo 255820 76567949 := bstep (se 3 (by rfl) ⟨14356490, by rfl⟩ : syracuseStep 76567949 = 28712981) B28712981
theorem B579041 : Blo 255820 579041 := bstep (se 2 (by rfl) ⟨217140, by rfl⟩ : syracuseStep 579041 = 434281) B434281
theorem B415343 : Blo 255820 415343 := bstep (se 1 (by rfl) ⟨311507, by rfl⟩ : syracuseStep 415343 = 623015) B623015
theorem B841711 : Blo 255820 841711 := bstep (se 1 (by rfl) ⟨631283, by rfl⟩ : syracuseStep 841711 = 1262567) B1262567
theorem B743521 : Blo 255820 743521 := bstep (se 2 (by rfl) ⟨278820, by rfl⟩ : syracuseStep 743521 = 557641) B557641
theorem B1038491 : Blo 255820 1038491 := bstep (se 1 (by rfl) ⟨778868, by rfl⟩ : syracuseStep 1038491 = 1557737) B1557737
theorem B547195 : Blo 255820 547195 := bstep (se 1 (by rfl) ⟨410396, by rfl⟩ : syracuseStep 547195 = 820793) B820793
theorem B1300859 : Blo 255820 1300859 := bstep (se 1 (by rfl) ⟨975644, by rfl⟩ : syracuseStep 1300859 = 1951289) B1951289
theorem B1464743 : Blo 255820 1464743 := bstep (se 1 (by rfl) ⟨1098557, by rfl⟩ : syracuseStep 1464743 = 2197115) B2197115
theorem B2415193 : Blo 255820 2415193 := bstep (se 2 (by rfl) ⟨905697, by rfl⟩ : syracuseStep 2415193 = 1811395) B1811395
theorem B10902197 : Blo 255820 10902197 := bstep (se 5 (by rfl) ⟨511040, by rfl⟩ : syracuseStep 10902197 = 1022081) B1022081
theorem B875231 : Blo 255820 875231 := bstep (se 1 (by rfl) ⟨656423, by rfl⟩ : syracuseStep 875231 = 1312847) B1312847
theorem B383903 : Blo 255820 383903 := bstep (se 1 (by rfl) ⟨287927, by rfl⟩ : syracuseStep 383903 = 575855) B575855
theorem B383951 : Blo 255820 383951 := bstep (se 1 (by rfl) ⟨287963, by rfl⟩ : syracuseStep 383951 = 575927) B575927
theorem B1793015 : Blo 255820 1793015 := bstep (se 1 (by rfl) ⟨1344761, by rfl⟩ : syracuseStep 1793015 = 2689523) B2689523
theorem B384041 : Blo 255820 384041 := bstep (se 2 (by rfl) ⟨144015, by rfl⟩ : syracuseStep 384041 = 288031) B288031
theorem B384047 : Blo 255820 384047 := bstep (se 1 (by rfl) ⟨288035, by rfl⟩ : syracuseStep 384047 = 576071) B576071
theorem B384071 : Blo 255820 384071 := bstep (se 1 (by rfl) ⟨288053, by rfl⟩ : syracuseStep 384071 = 576107) B576107
theorem B580679 : Blo 255820 580679 := bstep (se 1 (by rfl) ⟨435509, by rfl⟩ : syracuseStep 580679 = 871019) B871019
theorem B384335 : Blo 255820 384335 := bstep (se 1 (by rfl) ⟨288251, by rfl⟩ : syracuseStep 384335 = 576503) B576503
theorem B384425 : Blo 255820 384425 := bstep (se 2 (by rfl) ⟨144159, by rfl⟩ : syracuseStep 384425 = 288319) B288319
theorem B3694025 : Blo 255820 3694025 := bstep (se 2 (by rfl) ⟨1385259, by rfl⟩ : syracuseStep 3694025 = 2770519) B2770519
theorem B581075 : Blo 255820 581075 := bstep (se 1 (by rfl) ⟨435806, by rfl⟩ : syracuseStep 581075 = 871613) B871613
theorem B875987 : Blo 255820 875987 := bstep (se 1 (by rfl) ⟨656990, by rfl⟩ : syracuseStep 875987 = 1313981) B1313981
theorem B384575 : Blo 255820 384575 := bstep (se 1 (by rfl) ⟨288431, by rfl⟩ : syracuseStep 384575 = 576863) B576863
theorem B1400399 : Blo 255820 1400399 := bstep (se 1 (by rfl) ⟨1050299, by rfl⟩ : syracuseStep 1400399 = 2100599) B2100599
theorem B581345 : Blo 255820 581345 := bstep (se 2 (by rfl) ⟨218004, by rfl⟩ : syracuseStep 581345 = 436009) B436009
theorem B876257 : Blo 255820 876257 := bstep (se 2 (by rfl) ⟨328596, by rfl⟩ : syracuseStep 876257 = 657193) B657193
theorem B384839 : Blo 255820 384839 := bstep (se 1 (by rfl) ⟨288629, by rfl⟩ : syracuseStep 384839 = 577259) B577259
theorem B384923 : Blo 255820 384923 := bstep (se 1 (by rfl) ⟨288692, by rfl⟩ : syracuseStep 384923 = 577385) B577385
theorem B1564645 : Blo 255820 1564645 := bstep (se 4 (by rfl) ⟨146685, by rfl⟩ : syracuseStep 1564645 = 293371) B293371
theorem B548903 : Blo 255820 548903 := bstep (se 1 (by rfl) ⟨411677, by rfl⟩ : syracuseStep 548903 = 823355) B823355
theorem B2089313 : Blo 255820 2089313 := bstep (se 2 (by rfl) ⟨783492, by rfl⟩ : syracuseStep 2089313 = 1566985) B1566985
theorem B385487 : Blo 255820 385487 := bstep (se 1 (by rfl) ⟨289115, by rfl⟩ : syracuseStep 385487 = 578231) B578231
theorem B385529 : Blo 255820 385529 := bstep (se 2 (by rfl) ⟨144573, by rfl⟩ : syracuseStep 385529 = 289147) B289147
theorem B385631 : Blo 255820 385631 := bstep (se 1 (by rfl) ⟨289223, by rfl⟩ : syracuseStep 385631 = 578447) B578447
theorem B8938291 : Blo 255820 8938291 := bstep (se 1 (by rfl) ⟨6703718, by rfl⟩ : syracuseStep 8938291 = 13407437) B13407437
theorem B1303451 : Blo 255820 1303451 := bstep (se 1 (by rfl) ⟨977588, by rfl⟩ : syracuseStep 1303451 = 1955177) B1955177
theorem B386111 : Blo 255820 386111 := bstep (se 1 (by rfl) ⟨289583, by rfl⟩ : syracuseStep 386111 = 579167) B579167
theorem B386153 : Blo 255820 386153 := bstep (se 2 (by rfl) ⟨144807, by rfl⟩ : syracuseStep 386153 = 289615) B289615
theorem B975995 : Blo 255820 975995 := bstep (se 1 (by rfl) ⟨731996, by rfl⟩ : syracuseStep 975995 = 1463993) B1463993
theorem B1107067 : Blo 255820 1107067 := bstep (se 1 (by rfl) ⟨830300, by rfl⟩ : syracuseStep 1107067 = 1660601) B1660601
theorem B779453 : Blo 255820 779453 := bstep (se 3 (by rfl) ⟨146147, by rfl⟩ : syracuseStep 779453 = 292295) B292295
theorem B386255 : Blo 255820 386255 := bstep (se 1 (by rfl) ⟨289691, by rfl⟩ : syracuseStep 386255 = 579383) B579383
theorem B2942243 : Blo 255820 2942243 := bstep (se 1 (by rfl) ⟨2206682, by rfl⟩ : syracuseStep 2942243 = 4413365) B4413365
theorem B583019 : Blo 255820 583019 := bstep (se 1 (by rfl) ⟨437264, by rfl⟩ : syracuseStep 583019 = 874529) B874529
theorem B386459 : Blo 255820 386459 := bstep (se 1 (by rfl) ⟨289844, by rfl⟩ : syracuseStep 386459 = 579689) B579689
theorem B1467841 : Blo 255820 1467841 := bstep (se 2 (by rfl) ⟨550440, by rfl⟩ : syracuseStep 1467841 = 1100881) B1100881
theorem B5596739 : Blo 255820 5596739 := bstep (se 1 (by rfl) ⟨4197554, by rfl⟩ : syracuseStep 5596739 = 8395109) B8395109
theorem B386681 : Blo 255820 386681 := bstep (se 2 (by rfl) ⟨145005, by rfl⟩ : syracuseStep 386681 = 290011) B290011
theorem B583289 : Blo 255820 583289 := bstep (se 2 (by rfl) ⟨218733, by rfl⟩ : syracuseStep 583289 = 437467) B437467
theorem B386783 : Blo 255820 386783 := bstep (se 1 (by rfl) ⟨290087, by rfl⟩ : syracuseStep 386783 = 580175) B580175
theorem B386879 : Blo 255820 386879 := bstep (se 1 (by rfl) ⟨290159, by rfl⟩ : syracuseStep 386879 = 580319) B580319
theorem B387047 : Blo 255820 387047 := bstep (se 1 (by rfl) ⟨290285, by rfl⟩ : syracuseStep 387047 = 580571) B580571
theorem B255983 : Blo 255820 255983 := bstep (se 1 (by rfl) ⟨191987, by rfl⟩ : syracuseStep 255983 = 383975) B383975
theorem B288751 : Blo 255820 288751 := bstep (se 1 (by rfl) ⟨216563, by rfl⟩ : syracuseStep 288751 = 433127) B433127
theorem B387065 : Blo 255820 387065 := bstep (se 2 (by rfl) ⟨145149, by rfl⟩ : syracuseStep 387065 = 290299) B290299
theorem B387167 : Blo 255820 387167 := bstep (se 1 (by rfl) ⟨290375, by rfl⟩ : syracuseStep 387167 = 580751) B580751
theorem B256155 : Blo 255820 256155 := bstep (se 1 (by rfl) ⟨192116, by rfl⟩ : syracuseStep 256155 = 384233) B384233
theorem B387227 : Blo 255820 387227 := bstep (se 1 (by rfl) ⟨290420, by rfl⟩ : syracuseStep 387227 = 580841) B580841
theorem B256191 : Blo 255820 256191 := bstep (se 1 (by rfl) ⟨192143, by rfl⟩ : syracuseStep 256191 = 384287) B384287
theorem B387263 : Blo 255820 387263 := bstep (se 1 (by rfl) ⟨290447, by rfl⟩ : syracuseStep 387263 = 580895) B580895
theorem B3795173 : Blo 255820 3795173 := bstep (se 4 (by rfl) ⟨355797, by rfl⟩ : syracuseStep 3795173 = 711595) B711595
theorem B387305 : Blo 255820 387305 := bstep (se 2 (by rfl) ⟨145239, by rfl⟩ : syracuseStep 387305 = 290479) B290479
theorem B256303 : Blo 255820 256303 := bstep (se 1 (by rfl) ⟨192227, by rfl⟩ : syracuseStep 256303 = 384455) B384455
theorem B485689 : Blo 255820 485689 := bstep (se 2 (by rfl) ⟨182133, by rfl⟩ : syracuseStep 485689 = 364267) B364267
theorem B649529 : Blo 255820 649529 := bstep (se 2 (by rfl) ⟨243573, by rfl⟩ : syracuseStep 649529 = 487147) B487147
theorem B256539 : Blo 255820 256539 := bstep (se 1 (by rfl) ⟨192404, by rfl⟩ : syracuseStep 256539 = 384809) B384809
theorem B387611 : Blo 255820 387611 := bstep (se 1 (by rfl) ⟨290708, by rfl⟩ : syracuseStep 387611 = 581417) B581417
theorem B256543 : Blo 255820 256543 := bstep (se 1 (by rfl) ⟨192407, by rfl⟩ : syracuseStep 256543 = 384815) B384815
theorem B12479021 : Blo 255820 12479021 := bstep (se 3 (by rfl) ⟨2339816, by rfl⟩ : syracuseStep 12479021 = 4679633) B4679633
theorem B485993 : Blo 255820 485993 := bstep (se 2 (by rfl) ⟨182247, by rfl⟩ : syracuseStep 485993 = 364495) B364495
theorem B387689 : Blo 255820 387689 := bstep (se 2 (by rfl) ⟨145383, by rfl⟩ : syracuseStep 387689 = 290767) B290767
theorem B584297 : Blo 255820 584297 := bstep (se 2 (by rfl) ⟨219111, by rfl⟩ : syracuseStep 584297 = 438223) B438223
theorem B5040899 : Blo 255820 5040899 := bstep (se 1 (by rfl) ⟨3780674, by rfl⟩ : syracuseStep 5040899 = 7561349) B7561349
theorem B256859 : Blo 255820 256859 := bstep (se 1 (by rfl) ⟨192644, by rfl⟩ : syracuseStep 256859 = 385289) B385289
theorem B256927 : Blo 255820 256927 := bstep (se 1 (by rfl) ⟨192695, by rfl⟩ : syracuseStep 256927 = 385391) B385391
theorem B257071 : Blo 255820 257071 := bstep (se 1 (by rfl) ⟨192803, by rfl⟩ : syracuseStep 257071 = 385607) B385607
theorem B257095 : Blo 255820 257095 := bstep (se 1 (by rfl) ⟨192821, by rfl⟩ : syracuseStep 257095 = 385643) B385643
theorem B388217 : Blo 255820 388217 := bstep (se 2 (by rfl) ⟨145581, by rfl⟩ : syracuseStep 388217 = 291163) B291163
theorem B486623 : Blo 255820 486623 := bstep (se 1 (by rfl) ⟨364967, by rfl⟩ : syracuseStep 486623 = 729935) B729935
theorem B257247 : Blo 255820 257247 := bstep (se 1 (by rfl) ⟨192935, by rfl⟩ : syracuseStep 257247 = 385871) B385871
theorem B388319 : Blo 255820 388319 := bstep (se 1 (by rfl) ⟨291239, by rfl⟩ : syracuseStep 388319 = 582479) B582479
theorem B388361 : Blo 255820 388361 := bstep (se 2 (by rfl) ⟨145635, by rfl⟩ : syracuseStep 388361 = 291271) B291271
theorem B388463 : Blo 255820 388463 := bstep (se 1 (by rfl) ⟨291347, by rfl⟩ : syracuseStep 388463 = 582695) B582695
theorem B257511 : Blo 255820 257511 := bstep (se 1 (by rfl) ⟨193133, by rfl⟩ : syracuseStep 257511 = 386267) B386267
theorem B388583 : Blo 255820 388583 := bstep (se 1 (by rfl) ⟨291437, by rfl⟩ : syracuseStep 388583 = 582875) B582875
theorem B650825 : Blo 255820 650825 := bstep (se 2 (by rfl) ⟨244059, by rfl⟩ : syracuseStep 650825 = 488119) B488119
theorem B257627 : Blo 255820 257627 := bstep (se 1 (by rfl) ⟨193220, by rfl⟩ : syracuseStep 257627 = 386441) B386441
theorem B388715 : Blo 255820 388715 := bstep (se 1 (by rfl) ⟨291536, by rfl⟩ : syracuseStep 388715 = 583073) B583073
theorem B1109629 : Blo 255820 1109629 := bstep (se 3 (by rfl) ⟨208055, by rfl⟩ : syracuseStep 1109629 = 416111) B416111
theorem B388841 : Blo 255820 388841 := bstep (se 2 (by rfl) ⟨145815, by rfl⟩ : syracuseStep 388841 = 291631) B291631
theorem B257863 : Blo 255820 257863 := bstep (se 1 (by rfl) ⟨193397, by rfl⟩ : syracuseStep 257863 = 386795) B386795
theorem B388985 : Blo 255820 388985 := bstep (se 2 (by rfl) ⟨145869, by rfl⟩ : syracuseStep 388985 = 291739) B291739
theorem B2486209 : Blo 255820 2486209 := bstep (se 2 (by rfl) ⟨932328, by rfl⟩ : syracuseStep 2486209 = 1864657) B1864657
theorem B978911 : Blo 255820 978911 := bstep (se 1 (by rfl) ⟨734183, by rfl⟩ : syracuseStep 978911 = 1468367) B1468367
theorem B258015 : Blo 255820 258015 := bstep (se 1 (by rfl) ⟨193511, by rfl⟩ : syracuseStep 258015 = 387023) B387023
theorem B389087 : Blo 255820 389087 := bstep (se 1 (by rfl) ⟨291815, by rfl⟩ : syracuseStep 389087 = 583631) B583631
theorem B2486483 : Blo 255820 2486483 := bstep (se 1 (by rfl) ⟨1864862, by rfl⟩ : syracuseStep 2486483 = 3729725) B3729725
theorem B389339 : Blo 255820 389339 := bstep (se 1 (by rfl) ⟨292004, by rfl⟩ : syracuseStep 389339 = 584009) B584009
theorem B258279 : Blo 255820 258279 := bstep (se 1 (by rfl) ⟨193709, by rfl⟩ : syracuseStep 258279 = 387419) B387419
theorem B389351 : Blo 255820 389351 := bstep (se 1 (by rfl) ⟨292013, by rfl⟩ : syracuseStep 389351 = 584027) B584027
theorem B979229 : Blo 255820 979229 := bstep (se 3 (by rfl) ⟨183605, by rfl⟩ : syracuseStep 979229 = 367211) B367211
theorem B258431 : Blo 255820 258431 := bstep (se 1 (by rfl) ⟨193823, by rfl⟩ : syracuseStep 258431 = 387647) B387647
theorem B291199 : Blo 255820 291199 := bstep (se 1 (by rfl) ⟨218399, by rfl⟩ : syracuseStep 291199 = 436799) B436799
theorem B389513 : Blo 255820 389513 := bstep (se 2 (by rfl) ⟨146067, by rfl⟩ : syracuseStep 389513 = 292135) B292135
theorem B258511 : Blo 255820 258511 := bstep (se 1 (by rfl) ⟨193883, by rfl⟩ : syracuseStep 258511 = 387767) B387767
theorem B979411 : Blo 255820 979411 := bstep (se 1 (by rfl) ⟨734558, by rfl⟩ : syracuseStep 979411 = 1469117) B1469117
theorem B389609 : Blo 255820 389609 := bstep (se 2 (by rfl) ⟨146103, by rfl⟩ : syracuseStep 389609 = 292207) B292207
theorem B258663 : Blo 255820 258663 := bstep (se 1 (by rfl) ⟨193997, by rfl⟩ : syracuseStep 258663 = 387995) B387995
theorem B619169 : Blo 255820 619169 := bstep (se 2 (by rfl) ⟨232188, by rfl⟩ : syracuseStep 619169 = 464377) B464377
theorem B389867 : Blo 255820 389867 := bstep (se 1 (by rfl) ⟨292400, by rfl⟩ : syracuseStep 389867 = 584801) B584801
theorem B258927 : Blo 255820 258927 := bstep (se 1 (by rfl) ⟨194195, by rfl⟩ : syracuseStep 258927 = 388391) B388391
theorem B258983 : Blo 255820 258983 := bstep (se 1 (by rfl) ⟨194237, by rfl⟩ : syracuseStep 258983 = 388475) B388475
theorem B979883 : Blo 255820 979883 := bstep (se 1 (by rfl) ⟨734912, by rfl⟩ : syracuseStep 979883 = 1469825) B1469825
theorem B652283 : Blo 255820 652283 := bstep (se 1 (by rfl) ⟨489212, by rfl⟩ : syracuseStep 652283 = 978425) B978425
theorem B259067 : Blo 255820 259067 := bstep (se 1 (by rfl) ⟨194300, by rfl⟩ : syracuseStep 259067 = 388601) B388601
theorem B259135 : Blo 255820 259135 := bstep (se 1 (by rfl) ⟨194351, by rfl⟩ : syracuseStep 259135 = 388703) B388703
theorem B488521 : Blo 255820 488521 := bstep (se 2 (by rfl) ⟨183195, by rfl⟩ : syracuseStep 488521 = 366391) B366391
theorem B259279 : Blo 255820 259279 := bstep (se 1 (by rfl) ⟨194459, by rfl⟩ : syracuseStep 259279 = 388919) B388919
theorem B259483 : Blo 255820 259483 := bstep (se 1 (by rfl) ⟨194612, by rfl⟩ : syracuseStep 259483 = 389225) B389225
theorem B652769 : Blo 255820 652769 := bstep (se 2 (by rfl) ⟨244788, by rfl⟩ : syracuseStep 652769 = 489577) B489577
theorem B554465 : Blo 255820 554465 := bstep (se 2 (by rfl) ⟨207924, by rfl⟩ : syracuseStep 554465 = 415849) B415849
theorem B259695 : Blo 255820 259695 := bstep (se 1 (by rfl) ⟨194771, by rfl⟩ : syracuseStep 259695 = 389543) B389543
theorem B259751 : Blo 255820 259751 := bstep (se 1 (by rfl) ⟨194813, by rfl⟩ : syracuseStep 259751 = 389627) B389627
theorem B390991 : Blo 255820 390991 := bstep (se 1 (by rfl) ⟨293243, by rfl⟩ : syracuseStep 390991 = 586487) B586487
theorem B1308635 : Blo 255820 1308635 := bstep (se 1 (by rfl) ⟨981476, by rfl⟩ : syracuseStep 1308635 = 1962953) B1962953
theorem B391151 : Blo 255820 391151 := bstep (se 1 (by rfl) ⟨293363, by rfl⟩ : syracuseStep 391151 = 586727) B586727
theorem B325615 : Blo 255820 325615 := bstep (se 1 (by rfl) ⟨244211, by rfl⟩ : syracuseStep 325615 = 488423) B488423
theorem B653305 : Blo 255820 653305 := bstep (se 2 (by rfl) ⟨244989, by rfl⟩ : syracuseStep 653305 = 489979) B489979
theorem B7075937 : Blo 255820 7075937 := bstep (se 2 (by rfl) ⟨2653476, by rfl⟩ : syracuseStep 7075937 = 5306953) B5306953
theorem B653467 : Blo 255820 653467 := bstep (se 1 (by rfl) ⟨490100, by rfl⟩ : syracuseStep 653467 = 980201) B980201
theorem B653609 : Blo 255820 653609 := bstep (se 2 (by rfl) ⟨245103, by rfl⟩ : syracuseStep 653609 = 490207) B490207
theorem B490465 : Blo 255820 490465 := bstep (se 2 (by rfl) ⟨183924, by rfl⟩ : syracuseStep 490465 = 367849) B367849
theorem B621697 : Blo 255820 621697 := bstep (se 2 (by rfl) ⟨233136, by rfl⟩ : syracuseStep 621697 = 466273) B466273
theorem B982145 : Blo 255820 982145 := bstep (se 2 (by rfl) ⟨368304, by rfl⟩ : syracuseStep 982145 = 736609) B736609
theorem B261343 : Blo 255820 261343 := bstep (se 1 (by rfl) ⟨196007, by rfl⟩ : syracuseStep 261343 = 392015) B392015
theorem B654601 : Blo 255820 654601 := bstep (se 2 (by rfl) ⟨245475, by rfl⟩ : syracuseStep 654601 = 490951) B490951
theorem B3538187 : Blo 255820 3538187 := bstep (se 1 (by rfl) ⟨2653640, by rfl⟩ : syracuseStep 3538187 = 5307281) B5307281
theorem B884467 : Blo 255820 884467 := bstep (se 1 (by rfl) ⟨663350, by rfl⟩ : syracuseStep 884467 = 1326701) B1326701
theorem B885343 : Blo 255820 885343 := bstep (se 1 (by rfl) ⟨664007, by rfl⟩ : syracuseStep 885343 = 1328015) B1328015
theorem B623207 : Blo 255820 623207 := bstep (se 1 (by rfl) ⟨467405, by rfl⟩ : syracuseStep 623207 = 934811) B934811
theorem B328303 : Blo 255820 328303 := bstep (se 1 (by rfl) ⟨246227, by rfl⟩ : syracuseStep 328303 = 492455) B492455
theorem B984089 : Blo 255820 984089 := bstep (se 2 (by rfl) ⟨369033, by rfl⟩ : syracuseStep 984089 = 738067) B738067
theorem B820331 : Blo 255820 820331 := bstep (se 1 (by rfl) ⟨615248, by rfl⟩ : syracuseStep 820331 = 1230497) B1230497
theorem B984271 : Blo 255820 984271 := bstep (se 1 (by rfl) ⟨738203, by rfl⟩ : syracuseStep 984271 = 1476407) B1476407
theorem B1967327 : Blo 255820 1967327 := bstep (se 1 (by rfl) ⟨1475495, by rfl⟩ : syracuseStep 1967327 = 2950991) B2950991
theorem B656687 : Blo 255820 656687 := bstep (se 1 (by rfl) ⟨492515, by rfl⟩ : syracuseStep 656687 = 985031) B985031
theorem B394543 : Blo 255820 394543 := bstep (se 1 (by rfl) ⟨295907, by rfl⟩ : syracuseStep 394543 = 591815) B591815
theorem B984545 : Blo 255820 984545 := bstep (se 2 (by rfl) ⟨369204, by rfl⟩ : syracuseStep 984545 = 738409) B738409
theorem B1476089 : Blo 255820 1476089 := bstep (se 2 (by rfl) ⟨553533, by rfl⟩ : syracuseStep 1476089 = 1107067) B1107067
theorem B3278555 : Blo 255820 3278555 := bstep (se 1 (by rfl) ⟨2458916, by rfl⟩ : syracuseStep 3278555 = 4917833) B4917833
theorem B1312523 : Blo 255820 1312523 := bstep (se 1 (by rfl) ⟨984392, by rfl⟩ : syracuseStep 1312523 = 1968785) B1968785
theorem B6686479 : Blo 255820 6686479 := bstep (se 1 (by rfl) ⟨5014859, by rfl⟩ : syracuseStep 6686479 = 10029719) B10029719
theorem B329951 : Blo 255820 329951 := bstep (se 1 (by rfl) ⟨247463, by rfl⟩ : syracuseStep 329951 = 494927) B494927
theorem B1640843 : Blo 255820 1640843 := bstep (se 1 (by rfl) ⟨1230632, by rfl⟩ : syracuseStep 1640843 = 2461265) B2461265
theorem B12881029 : Blo 255820 12881029 := bstep (se 4 (by rfl) ⟨1207596, by rfl⟩ : syracuseStep 12881029 = 2415193) B2415193
theorem B1314143 : Blo 255820 1314143 := bstep (se 1 (by rfl) ⟨985607, by rfl⟩ : syracuseStep 1314143 = 1971215) B1971215
theorem B986489 : Blo 255820 986489 := bstep (se 2 (by rfl) ⟨369933, by rfl⟩ : syracuseStep 986489 = 739867) B739867
theorem B2101115 : Blo 255820 2101115 := bstep (se 1 (by rfl) ⟨1575836, by rfl⟩ : syracuseStep 2101115 = 3151673) B3151673
theorem B1478573 : Blo 255820 1478573 := bstep (se 3 (by rfl) ⟨277232, by rfl⟩ : syracuseStep 1478573 = 554465) B554465
theorem B692327 : Blo 255820 692327 := bstep (se 1 (by rfl) ⟨519245, by rfl⟩ : syracuseStep 692327 = 1038491) B1038491
theorem B463009 : Blo 255820 463009 := bstep (se 2 (by rfl) ⟨173628, by rfl⟩ : syracuseStep 463009 = 347257) B347257
theorem B1479505 : Blo 255820 1479505 := bstep (se 2 (by rfl) ⟨554814, by rfl⟩ : syracuseStep 1479505 = 1109629) B1109629
theorem B2233261 : Blo 255820 2233261 := bstep (se 3 (by rfl) ⟨418736, by rfl⟩ : syracuseStep 2233261 = 837473) B837473
theorem B2462683 : Blo 255820 2462683 := bstep (se 1 (by rfl) ⟨1847012, by rfl⟩ : syracuseStep 2462683 = 3694025) B3694025
theorem B3314945 : Blo 255820 3314945 := bstep (se 2 (by rfl) ⟨1243104, by rfl⟩ : syracuseStep 3314945 = 2486209) B2486209
theorem B1578953 : Blo 255820 1578953 := bstep (se 2 (by rfl) ⟨592107, by rfl⟩ : syracuseStep 1578953 = 1184215) B1184215
theorem B2530115 : Blo 255820 2530115 := bstep (se 1 (by rfl) ⟨1897586, by rfl⟩ : syracuseStep 2530115 = 3795173) B3795173
theorem B433019 : Blo 255820 433019 := bstep (se 1 (by rfl) ⟨324764, by rfl⟩ : syracuseStep 433019 = 649529) B649529
theorem B433883 : Blo 255820 433883 := bstep (se 1 (by rfl) ⟨325412, by rfl⟩ : syracuseStep 433883 = 650825) B650825
theorem B5611373 : Blo 255820 5611373 := bstep (se 3 (by rfl) ⟨1052132, by rfl⟩ : syracuseStep 5611373 = 2104265) B2104265
theorem B434153 : Blo 255820 434153 := bstep (se 2 (by rfl) ⟨162807, by rfl⟩ : syracuseStep 434153 = 325615) B325615
theorem B1122281 : Blo 255820 1122281 := bstep (se 2 (by rfl) ⟨420855, by rfl⟩ : syracuseStep 1122281 = 841711) B841711
theorem B991361 : Blo 255820 991361 := bstep (se 2 (by rfl) ⟨371760, by rfl⟩ : syracuseStep 991361 = 743521) B743521
theorem B729593 : Blo 255820 729593 := bstep (se 2 (by rfl) ⟨273597, by rfl⟩ : syracuseStep 729593 = 547195) B547195
theorem B434855 : Blo 255820 434855 := bstep (se 1 (by rfl) ⟨326141, by rfl⟩ : syracuseStep 434855 = 652283) B652283
theorem B435179 : Blo 255820 435179 := bstep (se 1 (by rfl) ⟨326384, by rfl⟩ : syracuseStep 435179 = 652769) B652769
theorem B828929 : Blo 255820 828929 := bstep (se 2 (by rfl) ⟨310848, by rfl⟩ : syracuseStep 828929 = 621697) B621697
theorem B435739 : Blo 255820 435739 := bstep (se 1 (by rfl) ⟨326804, by rfl⟩ : syracuseStep 435739 = 653609) B653609
theorem B2468029 : Blo 255820 2468029 := bstep (se 3 (by rfl) ⟨462755, by rfl⟩ : syracuseStep 2468029 = 925511) B925511
theorem B666575 : Blo 255820 666575 := bstep (se 1 (by rfl) ⟨499931, by rfl⟩ : syracuseStep 666575 = 999863) B999863
theorem B2468987 : Blo 255820 2468987 := bstep (se 1 (by rfl) ⟨1851740, by rfl⟩ : syracuseStep 2468987 = 3703481) B3703481
theorem B3288701 : Blo 255820 3288701 := bstep (se 3 (by rfl) ⟨616631, by rfl⟩ : syracuseStep 3288701 = 1233263) B1233263
theorem B634601 : Blo 255820 634601 := bstep (se 2 (by rfl) ⟨237975, by rfl⟩ : syracuseStep 634601 = 475951) B475951
theorem B1651117 : Blo 255820 1651117 := bstep (se 3 (by rfl) ⟨309584, by rfl⟩ : syracuseStep 1651117 = 619169) B619169
theorem B1847879 : Blo 255820 1847879 := bstep (se 1 (by rfl) ⟨1385909, by rfl⟩ : syracuseStep 1847879 = 2771819) B2771819
theorem B7385741 : Blo 255820 7385741 := bstep (se 3 (by rfl) ⟨1384826, by rfl⟩ : syracuseStep 7385741 = 2769653) B2769653
theorem B275195 : Blo 255820 275195 := bstep (se 1 (by rfl) ⟨206396, by rfl⟩ : syracuseStep 275195 = 412793) B412793
theorem B1684435 : Blo 255820 1684435 := bstep (se 1 (by rfl) ⟨1263326, by rfl⟩ : syracuseStep 1684435 = 2526653) B2526653
theorem B2471219 : Blo 255820 2471219 := bstep (se 1 (by rfl) ⟨1853414, by rfl⟩ : syracuseStep 2471219 = 3706829) B3706829
theorem B6436205 : Blo 255820 6436205 := bstep (se 3 (by rfl) ⟨1206788, by rfl⟩ : syracuseStep 6436205 = 2413577) B2413577
theorem B1095277 : Blo 255820 1095277 := bstep (se 3 (by rfl) ⟨205364, by rfl⟩ : syracuseStep 1095277 = 410729) B410729
theorem B866375 : Blo 255820 866375 := bstep (se 1 (by rfl) ⟨649781, by rfl⟩ : syracuseStep 866375 = 1299563) B1299563
theorem B2799755 : Blo 255820 2799755 := bstep (se 1 (by rfl) ⟨2099816, by rfl⟩ : syracuseStep 2799755 = 4199633) B4199633
theorem B309431 : Blo 255820 309431 := bstep (se 1 (by rfl) ⟨232073, by rfl⟩ : syracuseStep 309431 = 464147) B464147
theorem B276895 : Blo 255820 276895 := bstep (se 1 (by rfl) ⟨207671, by rfl⟩ : syracuseStep 276895 = 415343) B415343
theorem B703399 : Blo 255820 703399 := bstep (se 1 (by rfl) ⟨527549, by rfl⟩ : syracuseStep 703399 = 1055099) B1055099
theorem B867239 : Blo 255820 867239 := bstep (se 1 (by rfl) ⟨650429, by rfl⟩ : syracuseStep 867239 = 1300859) B1300859
theorem B1096679 : Blo 255820 1096679 := bstep (se 1 (by rfl) ⟨822509, by rfl⟩ : syracuseStep 1096679 = 1645019) B1645019
theorem B2210921 : Blo 255820 2210921 := bstep (se 2 (by rfl) ⟨829095, by rfl⟩ : syracuseStep 2210921 = 1658191) B1658191
theorem B1195343 : Blo 255820 1195343 := bstep (se 1 (by rfl) ⟨896507, by rfl⟩ : syracuseStep 1195343 = 1793015) B1793015
theorem B933599 : Blo 255820 933599 := bstep (se 1 (by rfl) ⟨700199, by rfl⟩ : syracuseStep 933599 = 1400399) B1400399
theorem B1851281 : Blo 255820 1851281 := bstep (se 2 (by rfl) ⟨694230, by rfl⟩ : syracuseStep 1851281 = 1388461) B1388461
theorem B1392875 : Blo 255820 1392875 := bstep (se 1 (by rfl) ⟨1044656, by rfl⟩ : syracuseStep 1392875 = 2089313) B2089313
theorem B868967 : Blo 255820 868967 := bstep (se 1 (by rfl) ⟨651725, by rfl⟩ : syracuseStep 868967 = 1303451) B1303451
theorem B1557593 : Blo 255820 1557593 := bstep (se 2 (by rfl) ⟨584097, by rfl⟩ : syracuseStep 1557593 = 1168195) B1168195
theorem B4441439 : Blo 255820 4441439 := bstep (se 1 (by rfl) ⟨3331079, by rfl⟩ : syracuseStep 4441439 = 6662159) B6662159
theorem B2082145 : Blo 255820 2082145 := bstep (se 2 (by rfl) ⟨780804, by rfl⟩ : syracuseStep 2082145 = 1561609) B1561609
theorem B3360599 : Blo 255820 3360599 := bstep (se 1 (by rfl) ⟨2520449, by rfl⟩ : syracuseStep 3360599 = 5040899) B5040899
theorem B1951775 : Blo 255820 1951775 := bstep (se 1 (by rfl) ⟨1463831, by rfl⟩ : syracuseStep 1951775 = 2927663) B2927663
theorem B575675 : Blo 255820 575675 := bstep (se 1 (by rfl) ⟨431756, by rfl⟩ : syracuseStep 575675 = 863513) B863513
theorem B575711 : Blo 255820 575711 := bstep (se 1 (by rfl) ⟨431783, by rfl⟩ : syracuseStep 575711 = 863567) B863567
theorem B1460825 : Blo 255820 1460825 := bstep (se 2 (by rfl) ⟨547809, by rfl⟩ : syracuseStep 1460825 = 1095619) B1095619
theorem B576161 : Blo 255820 576161 := bstep (se 2 (by rfl) ⟨216060, by rfl⟩ : syracuseStep 576161 = 432121) B432121
theorem B871073 : Blo 255820 871073 := bstep (se 2 (by rfl) ⟨326652, by rfl⟩ : syracuseStep 871073 = 653305) B653305
theorem B1657655 : Blo 255820 1657655 := bstep (se 1 (by rfl) ⟨1243241, by rfl⟩ : syracuseStep 1657655 = 2486483) B2486483
theorem B576377 : Blo 255820 576377 := bstep (se 2 (by rfl) ⟨216141, by rfl⟩ : syracuseStep 576377 = 432283) B432283
theorem B871289 : Blo 255820 871289 := bstep (se 2 (by rfl) ⟨326733, by rfl⟩ : syracuseStep 871289 = 653467) B653467
theorem B576521 : Blo 255820 576521 := bstep (se 2 (by rfl) ⟨216195, by rfl⟩ : syracuseStep 576521 = 432391) B432391
theorem B576575 : Blo 255820 576575 := bstep (se 1 (by rfl) ⟨432431, by rfl⟩ : syracuseStep 576575 = 864863) B864863
theorem B1101053 : Blo 255820 1101053 := bstep (se 3 (by rfl) ⟨206447, by rfl⟩ : syracuseStep 1101053 = 412895) B412895
theorem B577403 : Blo 255820 577403 := bstep (se 1 (by rfl) ⟨433052, by rfl⟩ : syracuseStep 577403 = 866105) B866105
theorem B1953719 : Blo 255820 1953719 := bstep (se 1 (by rfl) ⟨1465289, by rfl⟩ : syracuseStep 1953719 = 2930579) B2930579
theorem B577511 : Blo 255820 577511 := bstep (se 1 (by rfl) ⟨433133, by rfl⟩ : syracuseStep 577511 = 866267) B866267
theorem B872423 : Blo 255820 872423 := bstep (se 1 (by rfl) ⟨654317, by rfl⟩ : syracuseStep 872423 = 1308635) B1308635
theorem B577691 : Blo 255820 577691 := bstep (se 1 (by rfl) ⟨433268, by rfl⟩ : syracuseStep 577691 = 866537) B866537
theorem B348457 : Blo 255820 348457 := bstep (se 2 (by rfl) ⟨130671, by rfl⟩ : syracuseStep 348457 = 261343) B261343
theorem B577889 : Blo 255820 577889 := bstep (se 2 (by rfl) ⟨216708, by rfl⟩ : syracuseStep 577889 = 433417) B433417
theorem B872801 : Blo 255820 872801 := bstep (se 2 (by rfl) ⟨327300, by rfl⟩ : syracuseStep 872801 = 654601) B654601
theorem B577979 : Blo 255820 577979 := bstep (se 1 (by rfl) ⟨433484, by rfl⟩ : syracuseStep 577979 = 866969) B866969
theorem B3723731 : Blo 255820 3723731 := bstep (se 1 (by rfl) ⟨2792798, by rfl⟩ : syracuseStep 3723731 = 5585597) B5585597
theorem B2086193 : Blo 255820 2086193 := bstep (se 2 (by rfl) ⟨782322, by rfl⟩ : syracuseStep 2086193 = 1564645) B1564645
theorem B13981081 : Blo 255820 13981081 := bstep (se 2 (by rfl) ⟨5242905, by rfl⟩ : syracuseStep 13981081 = 10485811) B10485811
theorem B1463741 : Blo 255820 1463741 := bstep (se 3 (by rfl) ⟨274451, by rfl⟩ : syracuseStep 1463741 = 548903) B548903
theorem B6313459 : Blo 255820 6313459 := bstep (se 1 (by rfl) ⟨4735094, by rfl⟩ : syracuseStep 6313459 = 9470189) B9470189
theorem B972425 : Blo 255820 972425 := bstep (se 2 (by rfl) ⟨364659, by rfl⟩ : syracuseStep 972425 = 729319) B729319
theorem B1463975 : Blo 255820 1463975 := bstep (se 1 (by rfl) ⟨1097981, by rfl⟩ : syracuseStep 1463975 = 2195963) B2195963
theorem B579239 : Blo 255820 579239 := bstep (se 1 (by rfl) ⟨434429, by rfl⟩ : syracuseStep 579239 = 868859) B868859
theorem B874151 : Blo 255820 874151 := bstep (se 1 (by rfl) ⟨655613, by rfl⟩ : syracuseStep 874151 = 1311227) B1311227
theorem B579419 : Blo 255820 579419 := bstep (se 1 (by rfl) ⟨434564, by rfl⟩ : syracuseStep 579419 = 869129) B869129
theorem B2676833 : Blo 255820 2676833 := bstep (se 2 (by rfl) ⟨1003812, by rfl⟩ : syracuseStep 2676833 = 2007625) B2007625
theorem B579923 : Blo 255820 579923 := bstep (se 1 (by rfl) ⟨434942, by rfl⟩ : syracuseStep 579923 = 869885) B869885
theorem B11917721 : Blo 255820 11917721 := bstep (se 2 (by rfl) ⟨4469145, by rfl⟩ : syracuseStep 11917721 = 8938291) B8938291
theorem B1858085 : Blo 255820 1858085 := bstep (se 4 (by rfl) ⟨174195, by rfl⟩ : syracuseStep 1858085 = 348391) B348391
theorem B580409 : Blo 255820 580409 := bstep (se 2 (by rfl) ⟨217653, by rfl⟩ : syracuseStep 580409 = 435307) B435307
theorem B383855 : Blo 255820 383855 := bstep (se 1 (by rfl) ⟨287891, by rfl⟩ : syracuseStep 383855 = 575783) B575783
theorem B580463 : Blo 255820 580463 := bstep (se 1 (by rfl) ⟨435347, by rfl⟩ : syracuseStep 580463 = 870695) B870695
theorem B383867 : Blo 255820 383867 := bstep (se 1 (by rfl) ⟨287900, by rfl⟩ : syracuseStep 383867 = 575801) B575801
theorem B875663 : Blo 255820 875663 := bstep (se 1 (by rfl) ⟨656747, by rfl⟩ : syracuseStep 875663 = 1313495) B1313495
theorem B1957121 : Blo 255820 1957121 := bstep (se 2 (by rfl) ⟨733920, by rfl⟩ : syracuseStep 1957121 = 1467841) B1467841
theorem B1039645 : Blo 255820 1039645 := bstep (se 3 (by rfl) ⟨194933, by rfl⟩ : syracuseStep 1039645 = 389867) B389867
theorem B548203 : Blo 255820 548203 := bstep (se 1 (by rfl) ⟨411152, by rfl⟩ : syracuseStep 548203 = 822305) B822305
theorem B581039 : Blo 255820 581039 := bstep (se 1 (by rfl) ⟨435779, by rfl⟩ : syracuseStep 581039 = 871559) B871559
theorem B581111 : Blo 255820 581111 := bstep (se 1 (by rfl) ⟨435833, by rfl⟩ : syracuseStep 581111 = 871667) B871667
theorem B1236647 : Blo 255820 1236647 := bstep (se 1 (by rfl) ⟨927485, by rfl⟩ : syracuseStep 1236647 = 1854971) B1854971
theorem B384731 : Blo 255820 384731 := bstep (se 1 (by rfl) ⟨288548, by rfl⟩ : syracuseStep 384731 = 577097) B577097
theorem B385001 : Blo 255820 385001 := bstep (se 2 (by rfl) ⟨144375, by rfl⟩ : syracuseStep 385001 = 288751) B288751
theorem B5431499 : Blo 255820 5431499 := bstep (se 1 (by rfl) ⟨4073624, by rfl⟩ : syracuseStep 5431499 = 8147249) B8147249
theorem B647585 : Blo 255820 647585 := bstep (se 2 (by rfl) ⟨242844, by rfl⟩ : syracuseStep 647585 = 485689) B485689
theorem B975311 : Blo 255820 975311 := bstep (se 1 (by rfl) ⟨731483, by rfl⟩ : syracuseStep 975311 = 1462967) B1462967
theorem B582137 : Blo 255820 582137 := bstep (se 2 (by rfl) ⟨218301, by rfl⟩ : syracuseStep 582137 = 436603) B436603
theorem B582227 : Blo 255820 582227 := bstep (se 1 (by rfl) ⟨436670, by rfl⟩ : syracuseStep 582227 = 873341) B873341
theorem B385703 : Blo 255820 385703 := bstep (se 1 (by rfl) ⟨289277, by rfl⟩ : syracuseStep 385703 = 578555) B578555
theorem B2351783 : Blo 255820 2351783 := bstep (se 1 (by rfl) ⟨1763837, by rfl⟩ : syracuseStep 2351783 = 3527675) B3527675
theorem B582407 : Blo 255820 582407 := bstep (se 1 (by rfl) ⟨436805, by rfl⟩ : syracuseStep 582407 = 873611) B873611
theorem B385823 : Blo 255820 385823 := bstep (se 1 (by rfl) ⟨289367, by rfl⟩ : syracuseStep 385823 = 578735) B578735
theorem B385847 : Blo 255820 385847 := bstep (se 1 (by rfl) ⟨289385, by rfl⟩ : syracuseStep 385847 = 578771) B578771
theorem B1106743 : Blo 255820 1106743 := bstep (se 1 (by rfl) ⟨830057, by rfl⟩ : syracuseStep 1106743 = 1660115) B1660115
theorem B582497 : Blo 255820 582497 := bstep (se 2 (by rfl) ⟨218436, by rfl⟩ : syracuseStep 582497 = 436873) B436873
theorem B20243351 : Blo 255820 20243351 := bstep (se 1 (by rfl) ⟨15182513, by rfl⟩ : syracuseStep 20243351 = 30365027) B30365027
theorem B51045299 : Blo 255820 51045299 := bstep (se 1 (by rfl) ⟨38283974, by rfl⟩ : syracuseStep 51045299 = 76567949) B76567949
theorem B386027 : Blo 255820 386027 := bstep (se 1 (by rfl) ⟨289520, by rfl⟩ : syracuseStep 386027 = 579041) B579041
theorem B1107017 : Blo 255820 1107017 := bstep (se 2 (by rfl) ⟨415131, by rfl⟩ : syracuseStep 1107017 = 830263) B830263
theorem B288283 : Blo 255820 288283 := bstep (se 1 (by rfl) ⟨216212, by rfl⟩ : syracuseStep 288283 = 432425) B432425
theorem B976495 : Blo 255820 976495 := bstep (se 1 (by rfl) ⟨732371, by rfl⟩ : syracuseStep 976495 = 1464743) B1464743
theorem B616211 : Blo 255820 616211 := bstep (se 1 (by rfl) ⟨462158, by rfl⟩ : syracuseStep 616211 = 924317) B924317
theorem B7268131 : Blo 255820 7268131 := bstep (se 1 (by rfl) ⟨5451098, by rfl⟩ : syracuseStep 7268131 = 10902197) B10902197
theorem B583487 : Blo 255820 583487 := bstep (se 1 (by rfl) ⟨437615, by rfl⟩ : syracuseStep 583487 = 875231) B875231
theorem B255935 : Blo 255820 255935 := bstep (se 1 (by rfl) ⟨191951, by rfl⟩ : syracuseStep 255935 = 383903) B383903
theorem B255967 : Blo 255820 255967 := bstep (se 1 (by rfl) ⟨191975, by rfl⟩ : syracuseStep 255967 = 383951) B383951
theorem B256027 : Blo 255820 256027 := bstep (se 1 (by rfl) ⟨192020, by rfl⟩ : syracuseStep 256027 = 384041) B384041
theorem B256031 : Blo 255820 256031 := bstep (se 1 (by rfl) ⟨192023, by rfl⟩ : syracuseStep 256031 = 384047) B384047
theorem B256047 : Blo 255820 256047 := bstep (se 1 (by rfl) ⟨192035, by rfl⟩ : syracuseStep 256047 = 384071) B384071
theorem B387119 : Blo 255820 387119 := bstep (se 1 (by rfl) ⟨290339, by rfl⟩ : syracuseStep 387119 = 580679) B580679
theorem B1861775 : Blo 255820 1861775 := bstep (se 1 (by rfl) ⟨1396331, by rfl⟩ : syracuseStep 1861775 = 2792663) B2792663
theorem B256223 : Blo 255820 256223 := bstep (se 1 (by rfl) ⟨192167, by rfl⟩ : syracuseStep 256223 = 384335) B384335
theorem B256283 : Blo 255820 256283 := bstep (se 1 (by rfl) ⟨192212, by rfl⟩ : syracuseStep 256283 = 384425) B384425
theorem B387383 : Blo 255820 387383 := bstep (se 1 (by rfl) ⟨290537, by rfl⟩ : syracuseStep 387383 = 581075) B581075
theorem B583991 : Blo 255820 583991 := bstep (se 1 (by rfl) ⟨437993, by rfl⟩ : syracuseStep 583991 = 875987) B875987
theorem B256383 : Blo 255820 256383 := bstep (se 1 (by rfl) ⟨192287, by rfl⟩ : syracuseStep 256383 = 384575) B384575
theorem B616939 : Blo 255820 616939 := bstep (se 1 (by rfl) ⟨462704, by rfl⟩ : syracuseStep 616939 = 925409) B925409
theorem B387563 : Blo 255820 387563 := bstep (se 1 (by rfl) ⟨290672, by rfl⟩ : syracuseStep 387563 = 581345) B581345
theorem B584171 : Blo 255820 584171 := bstep (se 1 (by rfl) ⟨438128, by rfl⟩ : syracuseStep 584171 = 876257) B876257
theorem B256559 : Blo 255820 256559 := bstep (se 1 (by rfl) ⟨192419, by rfl⟩ : syracuseStep 256559 = 384839) B384839
theorem B289327 : Blo 255820 289327 := bstep (se 1 (by rfl) ⟨216995, by rfl⟩ : syracuseStep 289327 = 433991) B433991
theorem B617017 : Blo 255820 617017 := bstep (se 2 (by rfl) ⟨231381, by rfl⟩ : syracuseStep 617017 = 462763) B462763
theorem B256615 : Blo 255820 256615 := bstep (se 1 (by rfl) ⟨192461, by rfl⟩ : syracuseStep 256615 = 384923) B384923
theorem B256991 : Blo 255820 256991 := bstep (se 1 (by rfl) ⟨192743, by rfl⟩ : syracuseStep 256991 = 385487) B385487
theorem B289759 : Blo 255820 289759 := bstep (se 1 (by rfl) ⟨217319, by rfl⟩ : syracuseStep 289759 = 434639) B434639
theorem B257019 : Blo 255820 257019 := bstep (se 1 (by rfl) ⟨192764, by rfl⟩ : syracuseStep 257019 = 385529) B385529
theorem B257087 : Blo 255820 257087 := bstep (se 1 (by rfl) ⟨192815, by rfl⟩ : syracuseStep 257087 = 385631) B385631
theorem B388265 : Blo 255820 388265 := bstep (se 2 (by rfl) ⟨145599, by rfl⟩ : syracuseStep 388265 = 291199) B291199
theorem B1305881 : Blo 255820 1305881 := bstep (se 2 (by rfl) ⟨489705, by rfl⟩ : syracuseStep 1305881 = 979411) B979411
theorem B257407 : Blo 255820 257407 := bstep (se 1 (by rfl) ⟨193055, by rfl⟩ : syracuseStep 257407 = 386111) B386111
theorem B257435 : Blo 255820 257435 := bstep (se 1 (by rfl) ⟨193076, by rfl⟩ : syracuseStep 257435 = 386153) B386153
theorem B650663 : Blo 255820 650663 := bstep (se 1 (by rfl) ⟨487997, by rfl⟩ : syracuseStep 650663 = 975995) B975995
theorem B519635 : Blo 255820 519635 := bstep (se 1 (by rfl) ⟨389726, by rfl⟩ : syracuseStep 519635 = 779453) B779453
theorem B257503 : Blo 255820 257503 := bstep (se 1 (by rfl) ⟨193127, by rfl⟩ : syracuseStep 257503 = 386255) B386255
theorem B552415 : Blo 255820 552415 := bstep (se 1 (by rfl) ⟨414311, by rfl⟩ : syracuseStep 552415 = 828623) B828623
theorem B1961495 : Blo 255820 1961495 := bstep (se 1 (by rfl) ⟨1471121, by rfl⟩ : syracuseStep 1961495 = 2942243) B2942243
theorem B388679 : Blo 255820 388679 := bstep (se 1 (by rfl) ⟨291509, by rfl⟩ : syracuseStep 388679 = 583019) B583019
theorem B257639 : Blo 255820 257639 := bstep (se 1 (by rfl) ⟨193229, by rfl⟩ : syracuseStep 257639 = 386459) B386459
theorem B290407 : Blo 255820 290407 := bstep (se 1 (by rfl) ⟨217805, by rfl⟩ : syracuseStep 290407 = 435611) B435611
theorem B3731159 : Blo 255820 3731159 := bstep (se 1 (by rfl) ⟨2798369, by rfl⟩ : syracuseStep 3731159 = 5596739) B5596739
theorem B257787 : Blo 255820 257787 := bstep (se 1 (by rfl) ⟨193340, by rfl⟩ : syracuseStep 257787 = 386681) B386681
theorem B388859 : Blo 255820 388859 := bstep (se 1 (by rfl) ⟨291644, by rfl⟩ : syracuseStep 388859 = 583289) B583289
theorem B257855 : Blo 255820 257855 := bstep (se 1 (by rfl) ⟨193391, by rfl⟩ : syracuseStep 257855 = 386783) B386783
theorem B290623 : Blo 255820 290623 := bstep (se 1 (by rfl) ⟨217967, by rfl⟩ : syracuseStep 290623 = 435935) B435935
theorem B257919 : Blo 255820 257919 := bstep (se 1 (by rfl) ⟨193439, by rfl⟩ : syracuseStep 257919 = 386879) B386879
theorem B258031 : Blo 255820 258031 := bstep (se 1 (by rfl) ⟨193523, by rfl⟩ : syracuseStep 258031 = 387047) B387047
theorem B258043 : Blo 255820 258043 := bstep (se 1 (by rfl) ⟨193532, by rfl⟩ : syracuseStep 258043 = 387065) B387065
theorem B258111 : Blo 255820 258111 := bstep (se 1 (by rfl) ⟨193583, by rfl⟩ : syracuseStep 258111 = 387167) B387167
theorem B651361 : Blo 255820 651361 := bstep (se 2 (by rfl) ⟨244260, by rfl⟩ : syracuseStep 651361 = 488521) B488521
theorem B290911 : Blo 255820 290911 := bstep (se 1 (by rfl) ⟨218183, by rfl⟩ : syracuseStep 290911 = 436367) B436367
theorem B258151 : Blo 255820 258151 := bstep (se 1 (by rfl) ⟨193613, by rfl⟩ : syracuseStep 258151 = 387227) B387227
theorem B258175 : Blo 255820 258175 := bstep (se 1 (by rfl) ⟨193631, by rfl⟩ : syracuseStep 258175 = 387263) B387263
theorem B258203 : Blo 255820 258203 := bstep (se 1 (by rfl) ⟨193652, by rfl⟩ : syracuseStep 258203 = 387305) B387305
theorem B258407 : Blo 255820 258407 := bstep (se 1 (by rfl) ⟨193805, by rfl⟩ : syracuseStep 258407 = 387611) B387611
theorem B8319347 : Blo 255820 8319347 := bstep (se 1 (by rfl) ⟨6239510, by rfl⟩ : syracuseStep 8319347 = 12479021) B12479021
theorem B323995 : Blo 255820 323995 := bstep (se 1 (by rfl) ⟨242996, by rfl⟩ : syracuseStep 323995 = 485993) B485993
theorem B258459 : Blo 255820 258459 := bstep (se 1 (by rfl) ⟨193844, by rfl⟩ : syracuseStep 258459 = 387689) B387689
theorem B389531 : Blo 255820 389531 := bstep (se 1 (by rfl) ⟨292148, by rfl⟩ : syracuseStep 389531 = 584297) B584297
theorem B258811 : Blo 255820 258811 := bstep (se 1 (by rfl) ⟨194108, by rfl⟩ : syracuseStep 258811 = 388217) B388217
theorem B324415 : Blo 255820 324415 := bstep (se 1 (by rfl) ⟨243311, by rfl⟩ : syracuseStep 324415 = 486623) B486623
theorem B258879 : Blo 255820 258879 := bstep (se 1 (by rfl) ⟨194159, by rfl⟩ : syracuseStep 258879 = 388319) B388319
theorem B258907 : Blo 255820 258907 := bstep (se 1 (by rfl) ⟨194180, by rfl⟩ : syracuseStep 258907 = 388361) B388361
theorem B258975 : Blo 255820 258975 := bstep (se 1 (by rfl) ⟨194231, by rfl⟩ : syracuseStep 258975 = 388463) B388463
theorem B259055 : Blo 255820 259055 := bstep (se 1 (by rfl) ⟨194291, by rfl⟩ : syracuseStep 259055 = 388583) B388583
theorem B259143 : Blo 255820 259143 := bstep (se 1 (by rfl) ⟨194357, by rfl⟩ : syracuseStep 259143 = 388715) B388715
theorem B521321 : Blo 255820 521321 := bstep (se 2 (by rfl) ⟨195495, by rfl⟩ : syracuseStep 521321 = 390991) B390991
theorem B259227 : Blo 255820 259227 := bstep (se 1 (by rfl) ⟨194420, by rfl⟩ : syracuseStep 259227 = 388841) B388841
theorem B1996019 : Blo 255820 1996019 := bstep (se 1 (by rfl) ⟨1497014, by rfl⟩ : syracuseStep 1996019 = 2994029) B2994029
theorem B259323 : Blo 255820 259323 := bstep (se 1 (by rfl) ⟨194492, by rfl⟩ : syracuseStep 259323 = 388985) B388985
theorem B652607 : Blo 255820 652607 := bstep (se 1 (by rfl) ⟨489455, by rfl⟩ : syracuseStep 652607 = 978911) B978911
theorem B259391 : Blo 255820 259391 := bstep (se 1 (by rfl) ⟨194543, by rfl⟩ : syracuseStep 259391 = 389087) B389087
theorem B554303 : Blo 255820 554303 := bstep (se 1 (by rfl) ⟨415727, by rfl⟩ : syracuseStep 554303 = 831455) B831455
theorem B259559 : Blo 255820 259559 := bstep (se 1 (by rfl) ⟨194669, by rfl⟩ : syracuseStep 259559 = 389339) B389339
theorem B259567 : Blo 255820 259567 := bstep (se 1 (by rfl) ⟨194675, by rfl⟩ : syracuseStep 259567 = 389351) B389351
theorem B652819 : Blo 255820 652819 := bstep (se 1 (by rfl) ⟨489614, by rfl⟩ : syracuseStep 652819 = 979229) B979229
theorem B259675 : Blo 255820 259675 := bstep (se 1 (by rfl) ⟨194756, by rfl⟩ : syracuseStep 259675 = 389513) B389513
theorem B259739 : Blo 255820 259739 := bstep (se 1 (by rfl) ⟨194804, by rfl⟩ : syracuseStep 259739 = 389609) B389609
theorem B653255 : Blo 255820 653255 := bstep (se 1 (by rfl) ⟨489941, by rfl⟩ : syracuseStep 653255 = 979883) B979883
theorem B490025 : Blo 255820 490025 := bstep (se 2 (by rfl) ⟨183759, by rfl⟩ : syracuseStep 490025 = 367519) B367519
theorem B1866331 : Blo 255820 1866331 := bstep (se 1 (by rfl) ⟨1399748, by rfl⟩ : syracuseStep 1866331 = 2799497) B2799497
theorem B653953 : Blo 255820 653953 := bstep (se 2 (by rfl) ⟨245232, by rfl⟩ : syracuseStep 653953 = 490465) B490465
theorem B260767 : Blo 255820 260767 := bstep (se 1 (by rfl) ⟨195575, by rfl⟩ : syracuseStep 260767 = 391151) B391151
theorem B4717291 : Blo 255820 4717291 := bstep (se 1 (by rfl) ⟨3537968, by rfl⟩ : syracuseStep 4717291 = 7075937) B7075937
theorem B981841 : Blo 255820 981841 := bstep (se 2 (by rfl) ⟨368190, by rfl⟩ : syracuseStep 981841 = 736381) B736381
theorem B654763 : Blo 255820 654763 := bstep (se 1 (by rfl) ⟨491072, by rfl⟩ : syracuseStep 654763 = 982145) B982145
theorem B2358791 : Blo 255820 2358791 := bstep (se 1 (by rfl) ⟨1769093, by rfl⟩ : syracuseStep 2358791 = 3538187) B3538187
theorem B1179289 : Blo 255820 1179289 := bstep (se 2 (by rfl) ⟨442233, by rfl⟩ : syracuseStep 1179289 = 884467) B884467
theorem B656059 : Blo 255820 656059 := bstep (se 1 (by rfl) ⟨492044, by rfl⟩ : syracuseStep 656059 = 984089) B984089
theorem B1180457 : Blo 255820 1180457 := bstep (se 2 (by rfl) ⟨442671, by rfl⟩ : syracuseStep 1180457 = 885343) B885343
theorem B1311551 : Blo 255820 1311551 := bstep (se 1 (by rfl) ⟨983663, by rfl⟩ : syracuseStep 1311551 = 1967327) B1967327
theorem B656363 : Blo 255820 656363 := bstep (se 1 (by rfl) ⟨492272, by rfl⟩ : syracuseStep 656363 = 984545) B984545
theorem B984059 : Blo 255820 984059 := bstep (se 1 (by rfl) ⟨738044, by rfl⟩ : syracuseStep 984059 = 1476089) B1476089
theorem B1475657 : Blo 255820 1475657 := bstep (se 2 (by rfl) ⟨553371, by rfl⟩ : syracuseStep 1475657 = 1106743) B1106743
theorem B1312361 : Blo 255820 1312361 := bstep (se 2 (by rfl) ⟨492135, by rfl⟩ : syracuseStep 1312361 = 984271) B984271
theorem B526057 : Blo 255820 526057 := bstep (se 2 (by rfl) ⟨197271, by rfl⟩ : syracuseStep 526057 = 394543) B394543
theorem B657659 : Blo 255820 657659 := bstep (se 1 (by rfl) ⟨493244, by rfl⟩ : syracuseStep 657659 = 986489) B986489
theorem B985715 : Blo 255820 985715 := bstep (se 1 (by rfl) ⟨739286, by rfl⟩ : syracuseStep 985715 = 1478573) B1478573
theorem B822689 : Blo 255820 822689 := bstep (se 2 (by rfl) ⟨308508, by rfl⟩ : syracuseStep 822689 = 617017) B617017
theorem B1052635 : Blo 255820 1052635 := bstep (se 1 (by rfl) ⟨789476, by rfl⟩ : syracuseStep 1052635 = 1578953) B1578953
theorem B17174705 : Blo 255820 17174705 := bstep (se 2 (by rfl) ⟨6440514, by rfl⟩ : syracuseStep 17174705 = 12881029) B12881029
theorem B824431 : Blo 255820 824431 := bstep (se 1 (by rfl) ⟨618323, by rfl⟩ : syracuseStep 824431 = 1236647) B1236647
theorem B3740915 : Blo 255820 3740915 := bstep (se 1 (by rfl) ⟨2805686, by rfl⟩ : syracuseStep 3740915 = 5611373) B5611373
theorem B660907 : Blo 255820 660907 := bstep (se 1 (by rfl) ⟨495680, by rfl⟩ : syracuseStep 660907 = 991361) B991361
theorem B431723 : Blo 255820 431723 := bstep (se 1 (by rfl) ⟨323792, by rfl⟩ : syracuseStep 431723 = 647585) B647585
theorem B464609 : Blo 255820 464609 := bstep (se 2 (by rfl) ⟨174228, by rfl⟩ : syracuseStep 464609 = 348457) B348457
theorem B825149 : Blo 255820 825149 := bstep (se 3 (by rfl) ⟨154715, by rfl⟩ : syracuseStep 825149 = 309431) B309431
theorem B431993 : Blo 255820 431993 := bstep (se 2 (by rfl) ⟨161997, by rfl⟩ : syracuseStep 431993 = 323995) B323995
theorem B2201489 : Blo 255820 2201489 := bstep (se 2 (by rfl) ⟨825558, by rfl⟩ : syracuseStep 2201489 = 1651117) B1651117
theorem B432553 : Blo 255820 432553 := bstep (se 2 (by rfl) ⟨162207, by rfl⟩ : syracuseStep 432553 = 324415) B324415
theorem B1972673 : Blo 255820 1972673 := bstep (se 2 (by rfl) ⟨739752, by rfl⟩ : syracuseStep 1972673 = 1479505) B1479505
theorem B3283577 : Blo 255820 3283577 := bstep (se 2 (by rfl) ⟨1231341, by rfl⟩ : syracuseStep 3283577 = 2462683) B2462683
theorem B1645991 : Blo 255820 1645991 := bstep (se 1 (by rfl) ⟨1234493, by rfl⟩ : syracuseStep 1645991 = 2468987) B2468987
theorem B433775 : Blo 255820 433775 := bstep (se 1 (by rfl) ⟨325331, by rfl⟩ : syracuseStep 433775 = 650663) B650663
theorem B5546231 : Blo 255820 5546231 := bstep (se 1 (by rfl) ⟨4159673, by rfl⟩ : syracuseStep 5546231 = 8319347) B8319347
theorem B4923827 : Blo 255820 4923827 := bstep (se 1 (by rfl) ⟨3692870, by rfl⟩ : syracuseStep 4923827 = 7385741) B7385741
theorem B369193 : Blo 255820 369193 := bstep (se 2 (by rfl) ⟨138447, by rfl⟩ : syracuseStep 369193 = 276895) B276895
theorem B1647479 : Blo 255820 1647479 := bstep (se 1 (by rfl) ⟨1235609, by rfl⟩ : syracuseStep 1647479 = 2471219) B2471219
theorem B435071 : Blo 255820 435071 := bstep (se 1 (by rfl) ⟨326303, by rfl⟩ : syracuseStep 435071 = 652607) B652607
theorem B369535 : Blo 255820 369535 := bstep (se 1 (by rfl) ⟨277151, by rfl⟩ : syracuseStep 369535 = 554303) B554303
theorem B1385693 : Blo 255820 1385693 := bstep (se 3 (by rfl) ⟨259817, by rfl⟩ : syracuseStep 1385693 = 519635) B519635
theorem B435503 : Blo 255820 435503 := bstep (se 1 (by rfl) ⟨326627, by rfl⟩ : syracuseStep 435503 = 653255) B653255
theorem B35661221 : Blo 255820 35661221 := bstep (se 4 (by rfl) ⟨3343239, by rfl⟩ : syracuseStep 35661221 = 6686479) B6686479
theorem B1386193 : Blo 255820 1386193 := bstep (se 2 (by rfl) ⟨519822, by rfl⟩ : syracuseStep 1386193 = 1039645) B1039645
theorem B730937 : Blo 255820 730937 := bstep (se 2 (by rfl) ⟨274101, by rfl⟩ : syracuseStep 730937 = 548203) B548203
theorem B731119 : Blo 255820 731119 := bstep (se 1 (by rfl) ⟨548339, by rfl⟩ : syracuseStep 731119 = 1096679) B1096679
theorem B796895 : Blo 255820 796895 := bstep (se 1 (by rfl) ⟨597671, by rfl⟩ : syracuseStep 796895 = 1195343) B1195343
theorem B928583 : Blo 255820 928583 := bstep (se 1 (by rfl) ⟨696437, by rfl⟩ : syracuseStep 928583 = 1392875) B1392875
theorem B1846205 : Blo 255820 1846205 := bstep (se 3 (by rfl) ⟨346163, by rfl⟩ : syracuseStep 1846205 = 692327) B692327
theorem B437737 : Blo 255820 437737 := bstep (se 2 (by rfl) ⟨164151, by rfl⟩ : syracuseStep 437737 = 328303) B328303
theorem B437791 : Blo 255820 437791 := bstep (se 1 (by rfl) ⟨328343, by rfl⟩ : syracuseStep 437791 = 656687) B656687
theorem B2960959 : Blo 255820 2960959 := bstep (se 1 (by rfl) ⟨2220719, by rfl⟩ : syracuseStep 2960959 = 4441439) B4441439
theorem B2240399 : Blo 255820 2240399 := bstep (se 1 (by rfl) ⟨1680299, by rfl⟩ : syracuseStep 2240399 = 3360599) B3360599
theorem B1093895 : Blo 255820 1093895 := bstep (se 1 (by rfl) ⟨820421, by rfl⟩ : syracuseStep 1093895 = 1640843) B1640843
theorem B733853 : Blo 255820 733853 := bstep (se 3 (by rfl) ⟨137597, by rfl⟩ : syracuseStep 733853 = 275195) B275195
theorem B734035 : Blo 255820 734035 := bstep (se 1 (by rfl) ⟨550526, by rfl⟩ : syracuseStep 734035 = 1101053) B1101053
theorem B3290341 : Blo 255820 3290341 := bstep (se 4 (by rfl) ⟨308469, by rfl⟩ : syracuseStep 3290341 = 616939) B616939
theorem B3290705 : Blo 255820 3290705 := bstep (se 2 (by rfl) ⟨1234014, by rfl⟩ : syracuseStep 3290705 = 2468029) B2468029
theorem B2209963 : Blo 255820 2209963 := bstep (se 1 (by rfl) ⟨1657472, by rfl⟩ : syracuseStep 2209963 = 3314945) B3314945
theorem B1784555 : Blo 255820 1784555 := bstep (se 1 (by rfl) ⟨1338416, by rfl⟩ : syracuseStep 1784555 = 2676833) B2676833
theorem B7945147 : Blo 255820 7945147 := bstep (se 1 (by rfl) ⟨5958860, by rfl⟩ : syracuseStep 7945147 = 11917721) B11917721
theorem B1686743 : Blo 255820 1686743 := bstep (se 1 (by rfl) ⟨1265057, by rfl⟩ : syracuseStep 1686743 = 2530115) B2530115
theorem B736553 : Blo 255820 736553 := bstep (se 2 (by rfl) ⟨276207, by rfl⟩ : syracuseStep 736553 = 552415) B552415
theorem B868481 : Blo 255820 868481 := bstep (se 2 (by rfl) ⟨325680, by rfl⟩ : syracuseStep 868481 = 651361) B651361
theorem B3620999 : Blo 255820 3620999 := bstep (se 1 (by rfl) ⟨2715749, by rfl⟩ : syracuseStep 3620999 = 5431499) B5431499
theorem B34030199 : Blo 255820 34030199 := bstep (se 1 (by rfl) ⟨25522649, by rfl⟩ : syracuseStep 34030199 = 51045299) B51045299
theorem B738011 : Blo 255820 738011 := bstep (se 1 (by rfl) ⟨553508, by rfl⟩ : syracuseStep 738011 = 1107017) B1107017
theorem B410807 : Blo 255820 410807 := bstep (se 1 (by rfl) ⟨308105, by rfl⟩ : syracuseStep 410807 = 616211) B616211
theorem B2245913 : Blo 255820 2245913 := bstep (se 2 (by rfl) ⟨842217, by rfl⟩ : syracuseStep 2245913 = 1684435) B1684435
theorem B444383 : Blo 255820 444383 := bstep (se 1 (by rfl) ⟨333287, by rfl⟩ : syracuseStep 444383 = 666575) B666575
theorem B870425 : Blo 255820 870425 := bstep (se 2 (by rfl) ⟨326409, by rfl⟩ : syracuseStep 870425 = 652819) B652819
theorem B1460369 : Blo 255820 1460369 := bstep (se 2 (by rfl) ⟨547638, by rfl⟩ : syracuseStep 1460369 = 1095277) B1095277
theorem B870587 : Blo 255820 870587 := bstep (se 1 (by rfl) ⟨652940, by rfl⟩ : syracuseStep 870587 = 1305881) B1305881
theorem B1231919 : Blo 255820 1231919 := bstep (se 1 (by rfl) ⟨923939, by rfl⟩ : syracuseStep 1231919 = 1847879) B1847879
theorem B1330679 : Blo 255820 1330679 := bstep (se 1 (by rfl) ⟨998009, by rfl⟩ : syracuseStep 1330679 = 1996019) B1996019
theorem B871937 : Blo 255820 871937 := bstep (se 2 (by rfl) ⟨326976, by rfl⟩ : syracuseStep 871937 = 653953) B653953
theorem B347689 : Blo 255820 347689 := bstep (se 2 (by rfl) ⟨130383, by rfl⟩ : syracuseStep 347689 = 260767) B260767
theorem B937865 : Blo 255820 937865 := bstep (se 2 (by rfl) ⟨351699, by rfl⟩ : syracuseStep 937865 = 703399) B703399
theorem B577583 : Blo 255820 577583 := bstep (se 1 (by rfl) ⟨433187, by rfl⟩ : syracuseStep 577583 = 866375) B866375
theorem B873017 : Blo 255820 873017 := bstep (se 2 (by rfl) ⟨327381, by rfl⟩ : syracuseStep 873017 = 654763) B654763
theorem B1692269 : Blo 255820 1692269 := bstep (se 3 (by rfl) ⟨317300, by rfl⟩ : syracuseStep 1692269 = 634601) B634601
theorem B578159 : Blo 255820 578159 := bstep (se 1 (by rfl) ⟨433619, by rfl⟩ : syracuseStep 578159 = 867239) B867239
theorem B1234187 : Blo 255820 1234187 := bstep (se 1 (by rfl) ⟨925640, by rfl⟩ : syracuseStep 1234187 = 1851281) B1851281
theorem B579311 : Blo 255820 579311 := bstep (se 1 (by rfl) ⟨434483, by rfl⟩ : syracuseStep 579311 = 868967) B868967
theorem B415471 : Blo 255820 415471 := bstep (se 1 (by rfl) ⟨311603, by rfl⟩ : syracuseStep 415471 = 623207) B623207
theorem B1038395 : Blo 255820 1038395 := bstep (se 1 (by rfl) ⟨778796, by rfl⟩ : syracuseStep 1038395 = 1557593) B1557593
theorem B546887 : Blo 255820 546887 := bstep (se 1 (by rfl) ⟨410165, by rfl⟩ : syracuseStep 546887 = 820331) B820331
theorem B5560757 : Blo 255820 5560757 := bstep (se 5 (by rfl) ⟨260660, by rfl⟩ : syracuseStep 5560757 = 521321) B521321
theorem B2185703 : Blo 255820 2185703 := bstep (se 1 (by rfl) ⟨1639277, by rfl⟩ : syracuseStep 2185703 = 3278555) B3278555
theorem B875015 : Blo 255820 875015 := bstep (se 1 (by rfl) ⟨656261, by rfl⟩ : syracuseStep 875015 = 1312523) B1312523
theorem B1301183 : Blo 255820 1301183 := bstep (se 1 (by rfl) ⟨975887, by rfl⟩ : syracuseStep 1301183 = 1951775) B1951775
theorem B383783 : Blo 255820 383783 := bstep (se 1 (by rfl) ⟨287837, by rfl⟩ : syracuseStep 383783 = 575675) B575675
theorem B383807 : Blo 255820 383807 := bstep (se 1 (by rfl) ⟨287855, by rfl⟩ : syracuseStep 383807 = 575711) B575711
theorem B973883 : Blo 255820 973883 := bstep (se 1 (by rfl) ⟨730412, by rfl⟩ : syracuseStep 973883 = 1460825) B1460825
theorem B384107 : Blo 255820 384107 := bstep (se 1 (by rfl) ⟨288080, by rfl⟩ : syracuseStep 384107 = 576161) B576161
theorem B580715 : Blo 255820 580715 := bstep (se 1 (by rfl) ⟨435536, by rfl⟩ : syracuseStep 580715 = 871073) B871073
theorem B2776193 : Blo 255820 2776193 := bstep (se 2 (by rfl) ⟨1041072, by rfl⟩ : syracuseStep 2776193 = 2082145) B2082145
theorem B1105103 : Blo 255820 1105103 := bstep (se 1 (by rfl) ⟨828827, by rfl⟩ : syracuseStep 1105103 = 1657655) B1657655
theorem B384251 : Blo 255820 384251 := bstep (se 1 (by rfl) ⟨288188, by rfl⟩ : syracuseStep 384251 = 576377) B576377
theorem B580859 : Blo 255820 580859 := bstep (se 1 (by rfl) ⟨435644, by rfl⟩ : syracuseStep 580859 = 871289) B871289
theorem B384347 : Blo 255820 384347 := bstep (se 1 (by rfl) ⟨288260, by rfl⟩ : syracuseStep 384347 = 576521) B576521
theorem B384377 : Blo 255820 384377 := bstep (se 2 (by rfl) ⟨144141, by rfl⟩ : syracuseStep 384377 = 288283) B288283
theorem B580985 : Blo 255820 580985 := bstep (se 2 (by rfl) ⟨217869, by rfl⟩ : syracuseStep 580985 = 435739) B435739
theorem B384383 : Blo 255820 384383 := bstep (se 1 (by rfl) ⟨288287, by rfl⟩ : syracuseStep 384383 = 576575) B576575
theorem B1301993 : Blo 255820 1301993 := bstep (se 2 (by rfl) ⟨488247, by rfl⟩ : syracuseStep 1301993 = 976495) B976495
theorem B876095 : Blo 255820 876095 := bstep (se 1 (by rfl) ⟨657071, by rfl⟩ : syracuseStep 876095 = 1314143) B1314143
theorem B9690841 : Blo 255820 9690841 := bstep (se 2 (by rfl) ⟨3634065, by rfl⟩ : syracuseStep 9690841 = 7268131) B7268131
theorem B384935 : Blo 255820 384935 := bstep (se 1 (by rfl) ⟨288701, by rfl⟩ : syracuseStep 384935 = 577403) B577403
theorem B1400743 : Blo 255820 1400743 := bstep (se 1 (by rfl) ⟨1050557, by rfl⟩ : syracuseStep 1400743 = 2101115) B2101115
theorem B1302479 : Blo 255820 1302479 := bstep (se 1 (by rfl) ⟨976859, by rfl⟩ : syracuseStep 1302479 = 1953719) B1953719
theorem B385007 : Blo 255820 385007 := bstep (se 1 (by rfl) ⟨288755, by rfl⟩ : syracuseStep 385007 = 577511) B577511
theorem B581615 : Blo 255820 581615 := bstep (se 1 (by rfl) ⟨436211, by rfl⟩ : syracuseStep 581615 = 872423) B872423
theorem B385127 : Blo 255820 385127 := bstep (se 1 (by rfl) ⟨288845, by rfl⟩ : syracuseStep 385127 = 577691) B577691
theorem B385259 : Blo 255820 385259 := bstep (se 1 (by rfl) ⟨288944, by rfl⟩ : syracuseStep 385259 = 577889) B577889
theorem B581867 : Blo 255820 581867 := bstep (se 1 (by rfl) ⟨436400, by rfl⟩ : syracuseStep 581867 = 872801) B872801
theorem B385319 : Blo 255820 385319 := bstep (se 1 (by rfl) ⟨288989, by rfl⟩ : syracuseStep 385319 = 577979) B577979
theorem B2482487 : Blo 255820 2482487 := bstep (se 1 (by rfl) ⟨1861865, by rfl⟩ : syracuseStep 2482487 = 3723731) B3723731
theorem B385769 : Blo 255820 385769 := bstep (se 2 (by rfl) ⟨144663, by rfl⟩ : syracuseStep 385769 = 289327) B289327
theorem B5563181 : Blo 255820 5563181 := bstep (se 3 (by rfl) ⟨1043096, by rfl⟩ : syracuseStep 5563181 = 2086193) B2086193
theorem B975827 : Blo 255820 975827 := bstep (se 1 (by rfl) ⟨731870, by rfl⟩ : syracuseStep 975827 = 1463741) B1463741
theorem B648283 : Blo 255820 648283 := bstep (se 1 (by rfl) ⟨486212, by rfl⟩ : syracuseStep 648283 = 972425) B972425
theorem B975983 : Blo 255820 975983 := bstep (se 1 (by rfl) ⟨731987, by rfl⟩ : syracuseStep 975983 = 1463975) B1463975
theorem B386159 : Blo 255820 386159 := bstep (se 1 (by rfl) ⟨289619, by rfl⟩ : syracuseStep 386159 = 579239) B579239
theorem B582767 : Blo 255820 582767 := bstep (se 1 (by rfl) ⟨437075, by rfl⟩ : syracuseStep 582767 = 874151) B874151
theorem B386279 : Blo 255820 386279 := bstep (se 1 (by rfl) ⟨289709, by rfl⟩ : syracuseStep 386279 = 579419) B579419
theorem B386345 : Blo 255820 386345 := bstep (se 2 (by rfl) ⟨144879, by rfl⟩ : syracuseStep 386345 = 289759) B289759
theorem B386615 : Blo 255820 386615 := bstep (se 1 (by rfl) ⟨289961, by rfl⟩ : syracuseStep 386615 = 579923) B579923
theorem B1238723 : Blo 255820 1238723 := bstep (se 1 (by rfl) ⟨929042, by rfl⟩ : syracuseStep 1238723 = 1858085) B1858085
theorem B386939 : Blo 255820 386939 := bstep (se 1 (by rfl) ⟨290204, by rfl⟩ : syracuseStep 386939 = 580409) B580409
theorem B255903 : Blo 255820 255903 := bstep (se 1 (by rfl) ⟨191927, by rfl⟩ : syracuseStep 255903 = 383855) B383855
theorem B386975 : Blo 255820 386975 := bstep (se 1 (by rfl) ⟨290231, by rfl⟩ : syracuseStep 386975 = 580463) B580463
theorem B255911 : Blo 255820 255911 := bstep (se 1 (by rfl) ⟨191933, by rfl⟩ : syracuseStep 255911 = 383867) B383867
theorem B288679 : Blo 255820 288679 := bstep (se 1 (by rfl) ⟨216509, by rfl⟩ : syracuseStep 288679 = 433019) B433019
theorem B583775 : Blo 255820 583775 := bstep (se 1 (by rfl) ⟨437831, by rfl⟩ : syracuseStep 583775 = 875663) B875663
theorem B387209 : Blo 255820 387209 := bstep (se 2 (by rfl) ⟨145203, by rfl⟩ : syracuseStep 387209 = 290407) B290407
theorem B1304747 : Blo 255820 1304747 := bstep (se 1 (by rfl) ⟨978560, by rfl⟩ : syracuseStep 1304747 = 1957121) B1957121
theorem B387359 : Blo 255820 387359 := bstep (se 1 (by rfl) ⟨290519, by rfl⟩ : syracuseStep 387359 = 581039) B581039
theorem B387407 : Blo 255820 387407 := bstep (se 1 (by rfl) ⟨290555, by rfl⟩ : syracuseStep 387407 = 581111) B581111
theorem B387497 : Blo 255820 387497 := bstep (se 2 (by rfl) ⟨145311, by rfl⟩ : syracuseStep 387497 = 290623) B290623
theorem B256487 : Blo 255820 256487 := bstep (se 1 (by rfl) ⟨192365, by rfl⟩ : syracuseStep 256487 = 384731) B384731
theorem B289255 : Blo 255820 289255 := bstep (se 1 (by rfl) ⟨216941, by rfl⟩ : syracuseStep 289255 = 433883) B433883
theorem B256667 : Blo 255820 256667 := bstep (se 1 (by rfl) ⟨192500, by rfl⟩ : syracuseStep 256667 = 385001) B385001
theorem B289435 : Blo 255820 289435 := bstep (se 1 (by rfl) ⟨217076, by rfl⟩ : syracuseStep 289435 = 434153) B434153
theorem B748187 : Blo 255820 748187 := bstep (se 1 (by rfl) ⟨561140, by rfl⟩ : syracuseStep 748187 = 1122281) B1122281
theorem B387881 : Blo 255820 387881 := bstep (se 2 (by rfl) ⟨145455, by rfl⟩ : syracuseStep 387881 = 290911) B290911
theorem B617345 : Blo 255820 617345 := bstep (se 2 (by rfl) ⟨231504, by rfl⟩ : syracuseStep 617345 = 463009) B463009
theorem B650207 : Blo 255820 650207 := bstep (se 1 (by rfl) ⟨487655, by rfl⟩ : syracuseStep 650207 = 975311) B975311
theorem B486395 : Blo 255820 486395 := bstep (se 1 (by rfl) ⟨364796, by rfl⟩ : syracuseStep 486395 = 729593) B729593
theorem B388091 : Blo 255820 388091 := bstep (se 1 (by rfl) ⟨291068, by rfl⟩ : syracuseStep 388091 = 582137) B582137
theorem B388151 : Blo 255820 388151 := bstep (se 1 (by rfl) ⟨291113, by rfl⟩ : syracuseStep 388151 = 582227) B582227
theorem B257135 : Blo 255820 257135 := bstep (se 1 (by rfl) ⟨192851, by rfl⟩ : syracuseStep 257135 = 385703) B385703
theorem B289903 : Blo 255820 289903 := bstep (se 1 (by rfl) ⟨217427, by rfl⟩ : syracuseStep 289903 = 434855) B434855
theorem B1567855 : Blo 255820 1567855 := bstep (se 1 (by rfl) ⟨1175891, by rfl⟩ : syracuseStep 1567855 = 2351783) B2351783
theorem B388271 : Blo 255820 388271 := bstep (se 1 (by rfl) ⟨291203, by rfl⟩ : syracuseStep 388271 = 582407) B582407
theorem B257215 : Blo 255820 257215 := bstep (se 1 (by rfl) ⟨192911, by rfl⟩ : syracuseStep 257215 = 385823) B385823
theorem B257231 : Blo 255820 257231 := bstep (se 1 (by rfl) ⟨192923, by rfl⟩ : syracuseStep 257231 = 385847) B385847
theorem B388331 : Blo 255820 388331 := bstep (se 1 (by rfl) ⟨291248, by rfl⟩ : syracuseStep 388331 = 582497) B582497
theorem B879869 : Blo 255820 879869 := bstep (se 3 (by rfl) ⟨164975, by rfl⟩ : syracuseStep 879869 = 329951) B329951
theorem B13495567 : Blo 255820 13495567 := bstep (se 1 (by rfl) ⟨10121675, by rfl⟩ : syracuseStep 13495567 = 20243351) B20243351
theorem B257351 : Blo 255820 257351 := bstep (se 1 (by rfl) ⟨193013, by rfl⟩ : syracuseStep 257351 = 386027) B386027
theorem B290119 : Blo 255820 290119 := bstep (se 1 (by rfl) ⟨217589, by rfl⟩ : syracuseStep 290119 = 435179) B435179
theorem B552619 : Blo 255820 552619 := bstep (se 1 (by rfl) ⟨414464, by rfl⟩ : syracuseStep 552619 = 828929) B828929
theorem B388991 : Blo 255820 388991 := bstep (se 1 (by rfl) ⟨291743, by rfl⟩ : syracuseStep 388991 = 583487) B583487
theorem B2977681 : Blo 255820 2977681 := bstep (se 2 (by rfl) ⟨1116630, by rfl⟩ : syracuseStep 2977681 = 2233261) B2233261
theorem B258079 : Blo 255820 258079 := bstep (se 1 (by rfl) ⟨193559, by rfl⟩ : syracuseStep 258079 = 387119) B387119
theorem B1241183 : Blo 255820 1241183 := bstep (se 1 (by rfl) ⟨930887, by rfl⟩ : syracuseStep 1241183 = 1861775) B1861775
theorem B258255 : Blo 255820 258255 := bstep (se 1 (by rfl) ⟨193691, by rfl⟩ : syracuseStep 258255 = 387383) B387383
theorem B389327 : Blo 255820 389327 := bstep (se 1 (by rfl) ⟨291995, by rfl⟩ : syracuseStep 389327 = 583991) B583991
theorem B258375 : Blo 255820 258375 := bstep (se 1 (by rfl) ⟨193781, by rfl⟩ : syracuseStep 258375 = 387563) B387563
theorem B389447 : Blo 255820 389447 := bstep (se 1 (by rfl) ⟨292085, by rfl⟩ : syracuseStep 389447 = 584171) B584171
theorem B18641441 : Blo 255820 18641441 := bstep (se 2 (by rfl) ⟨6990540, by rfl⟩ : syracuseStep 18641441 = 13981081) B13981081
theorem B8417945 : Blo 255820 8417945 := bstep (se 2 (by rfl) ⟨3156729, by rfl⟩ : syracuseStep 8417945 = 6313459) B6313459
theorem B258843 : Blo 255820 258843 := bstep (se 1 (by rfl) ⟨194132, by rfl⟩ : syracuseStep 258843 = 388265) B388265
theorem B1307663 : Blo 255820 1307663 := bstep (se 1 (by rfl) ⟨980747, by rfl⟩ : syracuseStep 1307663 = 1961495) B1961495
theorem B259119 : Blo 255820 259119 := bstep (se 1 (by rfl) ⟨194339, by rfl⟩ : syracuseStep 259119 = 388679) B388679
theorem B2192467 : Blo 255820 2192467 := bstep (se 1 (by rfl) ⟨1644350, by rfl⟩ : syracuseStep 2192467 = 3288701) B3288701
theorem B2487439 : Blo 255820 2487439 := bstep (se 1 (by rfl) ⟨1865579, by rfl⟩ : syracuseStep 2487439 = 3731159) B3731159
theorem B259239 : Blo 255820 259239 := bstep (se 1 (by rfl) ⟨194429, by rfl⟩ : syracuseStep 259239 = 388859) B388859
theorem B259687 : Blo 255820 259687 := bstep (se 1 (by rfl) ⟨194765, by rfl⟩ : syracuseStep 259687 = 389531) B389531
theorem B2488441 : Blo 255820 2488441 := bstep (se 2 (by rfl) ⟨933165, by rfl⟩ : syracuseStep 2488441 = 1866331) B1866331
theorem B4290803 : Blo 255820 4290803 := bstep (se 1 (by rfl) ⟨3218102, by rfl⟩ : syracuseStep 4290803 = 6436205) B6436205
theorem B6289721 : Blo 255820 6289721 := bstep (se 2 (by rfl) ⟨2358645, by rfl⟩ : syracuseStep 6289721 = 4717291) B4717291
theorem B1309121 : Blo 255820 1309121 := bstep (se 2 (by rfl) ⟨490920, by rfl⟩ : syracuseStep 1309121 = 981841) B981841
theorem B1866503 : Blo 255820 1866503 := bstep (se 1 (by rfl) ⟨1399877, by rfl⟩ : syracuseStep 1866503 = 2799755) B2799755
theorem B326683 : Blo 255820 326683 := bstep (se 1 (by rfl) ⟨245012, by rfl⟩ : syracuseStep 326683 = 490025) B490025
theorem B1473947 : Blo 255820 1473947 := bstep (se 1 (by rfl) ⟨1105460, by rfl⟩ : syracuseStep 1473947 = 2210921) B2210921
theorem B1572385 : Blo 255820 1572385 := bstep (se 2 (by rfl) ⟨589644, by rfl⟩ : syracuseStep 1572385 = 1179289) B1179289
theorem B1572527 : Blo 255820 1572527 := bstep (se 1 (by rfl) ⟨1179395, by rfl⟩ : syracuseStep 1572527 = 2358791) B2358791
theorem B622399 : Blo 255820 622399 := bstep (se 1 (by rfl) ⟨466799, by rfl⟩ : syracuseStep 622399 = 933599) B933599
theorem B3309821 : Blo 255820 3309821 := bstep (se 3 (by rfl) ⟨620591, by rfl⟩ : syracuseStep 3309821 = 1241183) B1241183
theorem B492007 : Blo 255820 492007 := bstep (se 1 (by rfl) ⟨369005, by rfl⟩ : syracuseStep 492007 = 738011) B738011
theorem B786971 : Blo 255820 786971 := bstep (se 1 (by rfl) ⟨590228, by rfl⟩ : syracuseStep 786971 = 1180457) B1180457
theorem B656039 : Blo 255820 656039 := bstep (se 1 (by rfl) ⟨492029, by rfl⟩ : syracuseStep 656039 = 984059) B984059
theorem B983771 : Blo 255820 983771 := bstep (se 1 (by rfl) ⟨737828, by rfl⟩ : syracuseStep 983771 = 1475657) B1475657
theorem B492257 : Blo 255820 492257 := bstep (se 2 (by rfl) ⟨184596, by rfl⟩ : syracuseStep 492257 = 369193) B369193
theorem B492713 : Blo 255820 492713 := bstep (se 2 (by rfl) ⟨184767, by rfl⟩ : syracuseStep 492713 = 369535) B369535
theorem B296255 : Blo 255820 296255 := bstep (se 1 (by rfl) ⟨222191, by rfl⟩ : syracuseStep 296255 = 444383) B444383
theorem B657143 : Blo 255820 657143 := bstep (se 1 (by rfl) ⟨492857, by rfl⟩ : syracuseStep 657143 = 985715) B985715
theorem B821279 : Blo 255820 821279 := bstep (se 1 (by rfl) ⟨615959, by rfl⟩ : syracuseStep 821279 = 1231919) B1231919
theorem B887119 : Blo 255820 887119 := bstep (se 1 (by rfl) ⟨665339, by rfl⟩ : syracuseStep 887119 = 1330679) B1330679
theorem B625243 : Blo 255820 625243 := bstep (se 1 (by rfl) ⟨468932, by rfl⟩ : syracuseStep 625243 = 937865) B937865
theorem B822791 : Blo 255820 822791 := bstep (se 1 (by rfl) ⟨617093, by rfl⟩ : syracuseStep 822791 = 1234187) B1234187
theorem B692263 : Blo 255820 692263 := bstep (se 1 (by rfl) ⟨519197, by rfl⟩ : syracuseStep 692263 = 1038395) B1038395
theorem B364591 : Blo 255820 364591 := bstep (se 1 (by rfl) ⟨273443, by rfl⟩ : syracuseStep 364591 = 546887) B546887
theorem B3707171 : Blo 255820 3707171 := bstep (se 1 (by rfl) ⟨2780378, by rfl⟩ : syracuseStep 3707171 = 5560757) B5560757
theorem B1315115 : Blo 255820 1315115 := bstep (se 1 (by rfl) ⟨986336, by rfl⟩ : syracuseStep 1315115 = 1972673) B1972673
theorem B17994089 : Blo 255820 17994089 := bstep (se 2 (by rfl) ⟨6747783, by rfl⟩ : syracuseStep 17994089 = 13495567) B13495567
theorem B463585 : Blo 255820 463585 := bstep (se 2 (by rfl) ⟨173844, by rfl⟩ : syracuseStep 463585 = 347689) B347689
theorem B42374117 : Blo 255820 42374117 := bstep (se 4 (by rfl) ⟨3972573, by rfl⟩ : syracuseStep 42374117 = 7945147) B7945147
theorem B3970241 : Blo 255820 3970241 := bstep (se 2 (by rfl) ⟨1488840, by rfl⟩ : syracuseStep 3970241 = 2977681) B2977681
theorem B3282551 : Blo 255820 3282551 := bstep (se 1 (by rfl) ⟨2461913, by rfl⟩ : syracuseStep 3282551 = 4923827) B4923827
theorem B3708787 : Blo 255820 3708787 := bstep (se 1 (by rfl) ⟨2781590, by rfl⟩ : syracuseStep 3708787 = 5563181) B5563181
theorem B8361893 : Blo 255820 8361893 := bstep (se 4 (by rfl) ⟨783927, by rfl⟩ : syracuseStep 8361893 = 1567855) B1567855
theorem B923795 : Blo 255820 923795 := bstep (se 1 (by rfl) ⟨692846, by rfl⟩ : syracuseStep 923795 = 1385693) B1385693
theorem B825815 : Blo 255820 825815 := bstep (se 1 (by rfl) ⟨619361, by rfl⟩ : syracuseStep 825815 = 1238723) B1238723
theorem B2923289 : Blo 255820 2923289 := bstep (se 2 (by rfl) ⟨1096233, by rfl⟩ : syracuseStep 2923289 = 2192467) B2192467
theorem B531263 : Blo 255820 531263 := bstep (se 1 (by rfl) ⟨398447, by rfl⟩ : syracuseStep 531263 = 796895) B796895
theorem B3316585 : Blo 255820 3316585 := bstep (se 2 (by rfl) ⟨1243719, by rfl⟩ : syracuseStep 3316585 = 2487439) B2487439
theorem B498791 : Blo 255820 498791 := bstep (se 1 (by rfl) ⟨374093, by rfl⟩ : syracuseStep 498791 = 748187) B748187
theorem B433471 : Blo 255820 433471 := bstep (se 1 (by rfl) ⟨325103, by rfl⟩ : syracuseStep 433471 = 650207) B650207
theorem B3317921 : Blo 255820 3317921 := bstep (se 2 (by rfl) ⟨1244220, by rfl⟩ : syracuseStep 3317921 = 2488441) B2488441
theorem B729263 : Blo 255820 729263 := bstep (se 1 (by rfl) ⟨546947, by rfl⟩ : syracuseStep 729263 = 1093895) B1093895
theorem B12427627 : Blo 255820 12427627 := bstep (se 1 (by rfl) ⟨9320720, by rfl⟩ : syracuseStep 12427627 = 18641441) B18641441
theorem B5611963 : Blo 255820 5611963 := bstep (se 1 (by rfl) ⟨4208972, by rfl⟩ : syracuseStep 5611963 = 8417945) B8417945
theorem B435577 : Blo 255820 435577 := bstep (se 2 (by rfl) ⟨163341, by rfl⟩ : syracuseStep 435577 = 326683) B326683
theorem B2860535 : Blo 255820 2860535 := bstep (se 1 (by rfl) ⟨2145401, by rfl⟩ : syracuseStep 2860535 = 4290803) B4290803
theorem B1189703 : Blo 255820 1189703 := bstep (se 1 (by rfl) ⟨892277, by rfl⟩ : syracuseStep 1189703 = 1784555) B1784555
theorem B1124495 : Blo 255820 1124495 := bstep (se 1 (by rfl) ⟨843371, by rfl⟩ : syracuseStep 1124495 = 1686743) B1686743
theorem B12921121 : Blo 255820 12921121 := bstep (se 2 (by rfl) ⟨4845420, by rfl⟩ : syracuseStep 12921121 = 9690841) B9690841
theorem B829865 : Blo 255820 829865 := bstep (se 2 (by rfl) ⟨311199, by rfl⟩ : syracuseStep 829865 = 622399) B622399
theorem B22686799 : Blo 255820 22686799 := bstep (se 1 (by rfl) ⟨17015099, by rfl⟩ : syracuseStep 22686799 = 34030199) B34030199
theorem B437575 : Blo 255820 437575 := bstep (se 1 (by rfl) ⟨328181, by rfl⟩ : syracuseStep 437575 = 656363) B656363
theorem B273871 : Blo 255820 273871 := bstep (se 1 (by rfl) ⟨205403, by rfl⟩ : syracuseStep 273871 = 410807) B410807
theorem B864377 : Blo 255820 864377 := bstep (se 2 (by rfl) ⟨324141, by rfl⟩ : syracuseStep 864377 = 648283) B648283
theorem B438439 : Blo 255820 438439 := bstep (se 1 (by rfl) ⟨328829, by rfl⟩ : syracuseStep 438439 = 657659) B657659
theorem B1848257 : Blo 255820 1848257 := bstep (se 2 (by rfl) ⟨693096, by rfl⟩ : syracuseStep 1848257 = 1386193) B1386193
theorem B2602621 : Blo 255820 2602621 := bstep (se 3 (by rfl) ⟨487991, by rfl⟩ : syracuseStep 2602621 = 975983) B975983
theorem B1128179 : Blo 255820 1128179 := bstep (se 1 (by rfl) ⟨846134, by rfl⟩ : syracuseStep 1128179 = 1692269) B1692269
theorem B9975773 : Blo 255820 9975773 := bstep (se 3 (by rfl) ⟨1870457, by rfl⟩ : syracuseStep 9975773 = 3740915) B3740915
theorem B188627285 : Blo 255820 188627285 := bstep (se 10 (by rfl) ⟨276309, by rfl⟩ : syracuseStep 188627285 = 552619) B552619
theorem B309739 : Blo 255820 309739 := bstep (se 1 (by rfl) ⟨232304, by rfl⟩ : syracuseStep 309739 = 464609) B464609
theorem B1457135 : Blo 255820 1457135 := bstep (se 1 (by rfl) ⟨1092851, by rfl⟩ : syracuseStep 1457135 = 2185703) B2185703
theorem B867455 : Blo 255820 867455 := bstep (se 1 (by rfl) ⟨650591, by rfl⟩ : syracuseStep 867455 = 1301183) B1301183
theorem B3947945 : Blo 255820 3947945 := bstep (se 2 (by rfl) ⟨1480479, by rfl⟩ : syracuseStep 3947945 = 2960959) B2960959
theorem B1850795 : Blo 255820 1850795 := bstep (se 1 (by rfl) ⟨1388096, by rfl⟩ : syracuseStep 1850795 = 2776193) B2776193
theorem B736735 : Blo 255820 736735 := bstep (se 1 (by rfl) ⟨552551, by rfl⟩ : syracuseStep 736735 = 1105103) B1105103
theorem B1097327 : Blo 255820 1097327 := bstep (se 1 (by rfl) ⟨822995, by rfl⟩ : syracuseStep 1097327 = 1645991) B1645991
theorem B867995 : Blo 255820 867995 := bstep (se 1 (by rfl) ⟨650996, by rfl⟩ : syracuseStep 867995 = 1301993) B1301993
theorem B868319 : Blo 255820 868319 := bstep (se 1 (by rfl) ⟨651239, by rfl⟩ : syracuseStep 868319 = 1302479) B1302479
theorem B1654991 : Blo 255820 1654991 := bstep (se 1 (by rfl) ⟨1241243, by rfl⟩ : syracuseStep 1654991 = 2482487) B2482487
theorem B1098319 : Blo 255820 1098319 := bstep (se 1 (by rfl) ⟨823739, by rfl⟩ : syracuseStep 1098319 = 1647479) B1647479
theorem B23774147 : Blo 255820 23774147 := bstep (se 1 (by rfl) ⟨17830610, by rfl⟩ : syracuseStep 23774147 = 35661221) B35661221
theorem B869831 : Blo 255820 869831 := bstep (se 1 (by rfl) ⟨652373, by rfl⟩ : syracuseStep 869831 = 1304747) B1304747
theorem B1099241 : Blo 255820 1099241 := bstep (se 2 (by rfl) ⟨412215, by rfl⟩ : syracuseStep 1099241 = 824431) B824431
theorem B411563 : Blo 255820 411563 := bstep (se 1 (by rfl) ⟨308672, by rfl⟩ : syracuseStep 411563 = 617345) B617345
theorem B1230803 : Blo 255820 1230803 := bstep (se 1 (by rfl) ⟨923102, by rfl⟩ : syracuseStep 1230803 = 1846205) B1846205
theorem B1493599 : Blo 255820 1493599 := bstep (se 1 (by rfl) ⟨1120199, by rfl⟩ : syracuseStep 1493599 = 2240399) B2240399
theorem B576737 : Blo 255820 576737 := bstep (se 2 (by rfl) ⟨216276, by rfl⟩ : syracuseStep 576737 = 432553) B432553
theorem B2346317 : Blo 255820 2346317 := bstep (se 3 (by rfl) ⟨439934, by rfl⟩ : syracuseStep 2346317 = 879869) B879869
theorem B871775 : Blo 255820 871775 := bstep (se 1 (by rfl) ⟨653831, by rfl⟩ : syracuseStep 871775 = 1307663) B1307663
theorem B2805637 : Blo 255820 2805637 := bstep (se 4 (by rfl) ⟨263028, by rfl⟩ : syracuseStep 2805637 = 526057) B526057
theorem B872747 : Blo 255820 872747 := bstep (se 1 (by rfl) ⟨654560, by rfl⟩ : syracuseStep 872747 = 1309121) B1309121
theorem B578987 : Blo 255820 578987 := bstep (se 1 (by rfl) ⟨434240, by rfl⟩ : syracuseStep 578987 = 868481) B868481
theorem B2413999 : Blo 255820 2413999 := bstep (se 1 (by rfl) ⟨1810499, by rfl⟩ : syracuseStep 2413999 = 3620999) B3620999
theorem B874367 : Blo 255820 874367 := bstep (se 1 (by rfl) ⟨655775, by rfl⟩ : syracuseStep 874367 = 1311551) B1311551
theorem B1497275 : Blo 255820 1497275 := bstep (se 1 (by rfl) ⟨1122956, by rfl⟩ : syracuseStep 1497275 = 2245913) B2245913
theorem B874745 : Blo 255820 874745 := bstep (se 2 (by rfl) ⟨328029, by rfl⟩ : syracuseStep 874745 = 656059) B656059
theorem B874907 : Blo 255820 874907 := bstep (se 1 (by rfl) ⟨656180, by rfl⟩ : syracuseStep 874907 = 1312361) B1312361
theorem B580283 : Blo 255820 580283 := bstep (se 1 (by rfl) ⟨435212, by rfl⟩ : syracuseStep 580283 = 870425) B870425
theorem B973579 : Blo 255820 973579 := bstep (se 1 (by rfl) ⟨730184, by rfl⟩ : syracuseStep 973579 = 1460369) B1460369
theorem B580391 : Blo 255820 580391 := bstep (se 1 (by rfl) ⟨435293, by rfl⟩ : syracuseStep 580391 = 870587) B870587
theorem B183196853 : Blo 255820 183196853 := bstep (se 5 (by rfl) ⟨8587352, by rfl⟩ : syracuseStep 183196853 = 17174705) B17174705
theorem B548459 : Blo 255820 548459 := bstep (se 1 (by rfl) ⟨411344, by rfl⟩ : syracuseStep 548459 = 822689) B822689
theorem B581291 : Blo 255820 581291 := bstep (se 1 (by rfl) ⟨435968, by rfl⟩ : syracuseStep 581291 = 871937) B871937
theorem B384905 : Blo 255820 384905 := bstep (se 2 (by rfl) ⟨144339, by rfl⟩ : syracuseStep 384905 = 288679) B288679
theorem B974825 : Blo 255820 974825 := bstep (se 2 (by rfl) ⟨365559, by rfl⟩ : syracuseStep 974825 = 731119) B731119
theorem B385055 : Blo 255820 385055 := bstep (se 1 (by rfl) ⟨288791, by rfl⟩ : syracuseStep 385055 = 577583) B577583
theorem B582011 : Blo 255820 582011 := bstep (se 1 (by rfl) ⟨436508, by rfl⟩ : syracuseStep 582011 = 873017) B873017
theorem B385439 : Blo 255820 385439 := bstep (se 1 (by rfl) ⟨289079, by rfl⟩ : syracuseStep 385439 = 578159) B578159
theorem B385673 : Blo 255820 385673 := bstep (se 2 (by rfl) ⟨144627, by rfl⟩ : syracuseStep 385673 = 289255) B289255
theorem B385913 : Blo 255820 385913 := bstep (se 2 (by rfl) ⟨144717, by rfl⟩ : syracuseStep 385913 = 289435) B289435
theorem B287815 : Blo 255820 287815 := bstep (se 1 (by rfl) ⟨215861, by rfl⟩ : syracuseStep 287815 = 431723) B431723
theorem B386207 : Blo 255820 386207 := bstep (se 1 (by rfl) ⟨289655, by rfl⟩ : syracuseStep 386207 = 579311) B579311
theorem B550099 : Blo 255820 550099 := bstep (se 1 (by rfl) ⟨412574, by rfl⟩ : syracuseStep 550099 = 825149) B825149
theorem B287995 : Blo 255820 287995 := bstep (se 1 (by rfl) ⟨215996, by rfl⟩ : syracuseStep 287995 = 431993) B431993
theorem B1467659 : Blo 255820 1467659 := bstep (se 1 (by rfl) ⟨1100744, by rfl⟩ : syracuseStep 1467659 = 2201489) B2201489
theorem B386537 : Blo 255820 386537 := bstep (se 2 (by rfl) ⟨144951, by rfl⟩ : syracuseStep 386537 = 289903) B289903
theorem B583343 : Blo 255820 583343 := bstep (se 1 (by rfl) ⟨437507, by rfl⟩ : syracuseStep 583343 = 875015) B875015
theorem B2189051 : Blo 255820 2189051 := bstep (se 1 (by rfl) ⟨1641788, by rfl⟩ : syracuseStep 2189051 = 3283577) B3283577
theorem B386825 : Blo 255820 386825 := bstep (se 2 (by rfl) ⟨145059, by rfl⟩ : syracuseStep 386825 = 290119) B290119
theorem B255855 : Blo 255820 255855 := bstep (se 1 (by rfl) ⟨191891, by rfl⟩ : syracuseStep 255855 = 383783) B383783
theorem B255871 : Blo 255820 255871 := bstep (se 1 (by rfl) ⟨191903, by rfl⟩ : syracuseStep 255871 = 383807) B383807
theorem B583649 : Blo 255820 583649 := bstep (se 2 (by rfl) ⟨218868, by rfl⟩ : syracuseStep 583649 = 437737) B437737
theorem B649255 : Blo 255820 649255 := bstep (se 1 (by rfl) ⟨486941, by rfl⟩ : syracuseStep 649255 = 973883) B973883
theorem B583721 : Blo 255820 583721 := bstep (se 2 (by rfl) ⟨218895, by rfl⟩ : syracuseStep 583721 = 437791) B437791
theorem B256071 : Blo 255820 256071 := bstep (se 1 (by rfl) ⟨192053, by rfl⟩ : syracuseStep 256071 = 384107) B384107
theorem B387143 : Blo 255820 387143 := bstep (se 1 (by rfl) ⟨290357, by rfl⟩ : syracuseStep 387143 = 580715) B580715
theorem B256167 : Blo 255820 256167 := bstep (se 1 (by rfl) ⟨192125, by rfl⟩ : syracuseStep 256167 = 384251) B384251
theorem B387239 : Blo 255820 387239 := bstep (se 1 (by rfl) ⟨290429, by rfl⟩ : syracuseStep 387239 = 580859) B580859
theorem B256231 : Blo 255820 256231 := bstep (se 1 (by rfl) ⟨192173, by rfl⟩ : syracuseStep 256231 = 384347) B384347
theorem B256251 : Blo 255820 256251 := bstep (se 1 (by rfl) ⟨192188, by rfl⟩ : syracuseStep 256251 = 384377) B384377
theorem B387323 : Blo 255820 387323 := bstep (se 1 (by rfl) ⟨290492, by rfl⟩ : syracuseStep 387323 = 580985) B580985
theorem B256255 : Blo 255820 256255 := bstep (se 1 (by rfl) ⟨192191, by rfl⟩ : syracuseStep 256255 = 384383) B384383
theorem B584063 : Blo 255820 584063 := bstep (se 1 (by rfl) ⟨438047, by rfl⟩ : syracuseStep 584063 = 876095) B876095
theorem B289183 : Blo 255820 289183 := bstep (se 1 (by rfl) ⟨216887, by rfl⟩ : syracuseStep 289183 = 433775) B433775
theorem B256623 : Blo 255820 256623 := bstep (se 1 (by rfl) ⟨192467, by rfl⟩ : syracuseStep 256623 = 384935) B384935
theorem B1403513 : Blo 255820 1403513 := bstep (se 2 (by rfl) ⟨526317, by rfl⟩ : syracuseStep 1403513 = 1052635) B1052635
theorem B256671 : Blo 255820 256671 := bstep (se 1 (by rfl) ⟨192503, by rfl⟩ : syracuseStep 256671 = 385007) B385007
theorem B387743 : Blo 255820 387743 := bstep (se 1 (by rfl) ⟨290807, by rfl⟩ : syracuseStep 387743 = 581615) B581615
theorem B256751 : Blo 255820 256751 := bstep (se 1 (by rfl) ⟨192563, by rfl⟩ : syracuseStep 256751 = 385127) B385127
theorem B256839 : Blo 255820 256839 := bstep (se 1 (by rfl) ⟨192629, by rfl⟩ : syracuseStep 256839 = 385259) B385259
theorem B387911 : Blo 255820 387911 := bstep (se 1 (by rfl) ⟨290933, by rfl⟩ : syracuseStep 387911 = 581867) B581867
theorem B3697487 : Blo 255820 3697487 := bstep (se 1 (by rfl) ⟨2773115, by rfl⟩ : syracuseStep 3697487 = 5546231) B5546231
theorem B256879 : Blo 255820 256879 := bstep (se 1 (by rfl) ⟨192659, by rfl⟩ : syracuseStep 256879 = 385319) B385319
theorem B257179 : Blo 255820 257179 := bstep (se 1 (by rfl) ⟨192884, by rfl⟩ : syracuseStep 257179 = 385769) B385769
theorem B290047 : Blo 255820 290047 := bstep (se 1 (by rfl) ⟨217535, by rfl⟩ : syracuseStep 290047 = 435071) B435071
theorem B650551 : Blo 255820 650551 := bstep (se 1 (by rfl) ⟨487913, by rfl⟩ : syracuseStep 650551 = 975827) B975827
theorem B257439 : Blo 255820 257439 := bstep (se 1 (by rfl) ⟨193079, by rfl⟩ : syracuseStep 257439 = 386159) B386159
theorem B388511 : Blo 255820 388511 := bstep (se 1 (by rfl) ⟨291383, by rfl⟩ : syracuseStep 388511 = 582767) B582767
theorem B257519 : Blo 255820 257519 := bstep (se 1 (by rfl) ⟨193139, by rfl⟩ : syracuseStep 257519 = 386279) B386279
theorem B257563 : Blo 255820 257563 := bstep (se 1 (by rfl) ⟨193172, by rfl⟩ : syracuseStep 257563 = 386345) B386345
theorem B290335 : Blo 255820 290335 := bstep (se 1 (by rfl) ⟨217751, by rfl⟩ : syracuseStep 290335 = 435503) B435503
theorem B257743 : Blo 255820 257743 := bstep (se 1 (by rfl) ⟨193307, by rfl⟩ : syracuseStep 257743 = 386615) B386615
theorem B978713 : Blo 255820 978713 := bstep (se 2 (by rfl) ⟨367017, by rfl⟩ : syracuseStep 978713 = 734035) B734035
theorem B487291 : Blo 255820 487291 := bstep (se 1 (by rfl) ⟨365468, by rfl⟩ : syracuseStep 487291 = 730937) B730937
theorem B257959 : Blo 255820 257959 := bstep (se 1 (by rfl) ⟨193469, by rfl⟩ : syracuseStep 257959 = 386939) B386939
theorem B257983 : Blo 255820 257983 := bstep (se 1 (by rfl) ⟨193487, by rfl⟩ : syracuseStep 257983 = 386975) B386975
theorem B389183 : Blo 255820 389183 := bstep (se 1 (by rfl) ⟨291887, by rfl⟩ : syracuseStep 389183 = 583775) B583775
theorem B258139 : Blo 255820 258139 := bstep (se 1 (by rfl) ⟨193604, by rfl⟩ : syracuseStep 258139 = 387209) B387209
theorem B258239 : Blo 255820 258239 := bstep (se 1 (by rfl) ⟨193679, by rfl⟩ : syracuseStep 258239 = 387359) B387359
theorem B258271 : Blo 255820 258271 := bstep (se 1 (by rfl) ⟨193703, by rfl⟩ : syracuseStep 258271 = 387407) B387407
theorem B258331 : Blo 255820 258331 := bstep (se 1 (by rfl) ⟨193748, by rfl⟩ : syracuseStep 258331 = 387497) B387497
theorem B4387121 : Blo 255820 4387121 := bstep (se 2 (by rfl) ⟨1645170, by rfl⟩ : syracuseStep 4387121 = 3290341) B3290341
theorem B258587 : Blo 255820 258587 := bstep (se 1 (by rfl) ⟨193940, by rfl⟩ : syracuseStep 258587 = 387881) B387881
theorem B619055 : Blo 255820 619055 := bstep (se 1 (by rfl) ⟨464291, by rfl⟩ : syracuseStep 619055 = 928583) B928583
theorem B881209 : Blo 255820 881209 := bstep (se 2 (by rfl) ⟨330453, by rfl⟩ : syracuseStep 881209 = 660907) B660907
theorem B324263 : Blo 255820 324263 := bstep (se 1 (by rfl) ⟨243197, by rfl⟩ : syracuseStep 324263 = 486395) B486395
theorem B258727 : Blo 255820 258727 := bstep (se 1 (by rfl) ⟨194045, by rfl⟩ : syracuseStep 258727 = 388091) B388091
theorem B258767 : Blo 255820 258767 := bstep (se 1 (by rfl) ⟨194075, by rfl⟩ : syracuseStep 258767 = 388151) B388151
theorem B258847 : Blo 255820 258847 := bstep (se 1 (by rfl) ⟨194135, by rfl⟩ : syracuseStep 258847 = 388271) B388271
theorem B258887 : Blo 255820 258887 := bstep (se 1 (by rfl) ⟨194165, by rfl⟩ : syracuseStep 258887 = 388331) B388331
theorem B553961 : Blo 255820 553961 := bstep (se 2 (by rfl) ⟨207735, by rfl⟩ : syracuseStep 553961 = 415471) B415471
theorem B259327 : Blo 255820 259327 := bstep (se 1 (by rfl) ⟨194495, by rfl⟩ : syracuseStep 259327 = 388991) B388991
theorem B259551 : Blo 255820 259551 := bstep (se 1 (by rfl) ⟨194663, by rfl⟩ : syracuseStep 259551 = 389327) B389327
theorem B259631 : Blo 255820 259631 := bstep (se 1 (by rfl) ⟨194723, by rfl⟩ : syracuseStep 259631 = 389447) B389447
theorem B2946617 : Blo 255820 2946617 := bstep (se 2 (by rfl) ⟨1104981, by rfl⟩ : syracuseStep 2946617 = 2209963) B2209963
theorem B489235 : Blo 255820 489235 := bstep (se 1 (by rfl) ⟨366926, by rfl⟩ : syracuseStep 489235 = 733853) B733853
theorem B2193803 : Blo 255820 2193803 := bstep (se 1 (by rfl) ⟨1645352, by rfl⟩ : syracuseStep 2193803 = 3290705) B3290705
theorem B4193147 : Blo 255820 4193147 := bstep (se 1 (by rfl) ⟨3144860, by rfl⟩ : syracuseStep 4193147 = 6289721) B6289721
theorem B1244335 : Blo 255820 1244335 := bstep (se 1 (by rfl) ⟨933251, by rfl⟩ : syracuseStep 1244335 = 1866503) B1866503
theorem B2096513 : Blo 255820 2096513 := bstep (se 2 (by rfl) ⟨786192, by rfl⟩ : syracuseStep 2096513 = 1572385) B1572385
theorem B491035 : Blo 255820 491035 := bstep (se 1 (by rfl) ⟨368276, by rfl⟩ : syracuseStep 491035 = 736553) B736553
theorem B982631 : Blo 255820 982631 := bstep (se 1 (by rfl) ⟨736973, by rfl⟩ : syracuseStep 982631 = 1473947) B1473947
theorem B1048351 : Blo 255820 1048351 := bstep (se 1 (by rfl) ⟨786263, by rfl⟩ : syracuseStep 1048351 = 1572527) B1572527
theorem B1867657 : Blo 255820 1867657 := bstep (se 2 (by rfl) ⟨700371, by rfl⟩ : syracuseStep 1867657 = 1400743) B1400743
theorem B524647 : Blo 255820 524647 := bstep (se 1 (by rfl) ⟨393485, by rfl⟩ : syracuseStep 524647 = 786971) B786971
theorem B655847 : Blo 255820 655847 := bstep (se 1 (by rfl) ⟨491885, by rfl⟩ : syracuseStep 655847 = 983771) B983771
theorem B656009 : Blo 255820 656009 := bstep (se 2 (by rfl) ⟨246003, by rfl⟩ : syracuseStep 656009 = 492007) B492007
theorem B328475 : Blo 255820 328475 := bstep (se 1 (by rfl) ⟨246356, by rfl⟩ : syracuseStep 328475 = 492713) B492713
theorem B820535 : Blo 255820 820535 := bstep (se 1 (by rfl) ⟨615401, by rfl⟩ : syracuseStep 820535 = 1230803) B1230803
theorem B1312685 : Blo 255820 1312685 := bstep (se 3 (by rfl) ⟨246128, by rfl⟩ : syracuseStep 1312685 = 492257) B492257
theorem B28249411 : Blo 255820 28249411 := bstep (se 1 (by rfl) ⟨21187058, by rfl⟩ : syracuseStep 28249411 = 42374117) B42374117
theorem B790013 : Blo 255820 790013 := bstep (se 3 (by rfl) ⟨148127, by rfl⟩ : syracuseStep 790013 = 296255) B296255
theorem B5574595 : Blo 255820 5574595 := bstep (se 1 (by rfl) ⟨4180946, by rfl⟩ : syracuseStep 5574595 = 8361893) B8361893
theorem B30249065 : Blo 255820 30249065 := bstep (se 2 (by rfl) ⟨11343399, by rfl⟩ : syracuseStep 30249065 = 22686799) B22686799
theorem B365161 : Blo 255820 365161 := bstep (se 2 (by rfl) ⟨136935, by rfl⟩ : syracuseStep 365161 = 273871) B273871
theorem B332527 : Blo 255820 332527 := bstep (se 1 (by rfl) ⟨249395, by rfl⟩ : syracuseStep 332527 = 498791) B498791
theorem B122131235 : Blo 255820 122131235 := bstep (se 1 (by rfl) ⟨91598426, by rfl⟩ : syracuseStep 122131235 = 183196853) B183196853
theorem B365639 : Blo 255820 365639 := bstep (se 1 (by rfl) ⟨274229, by rfl⟩ : syracuseStep 365639 = 548459) B548459
theorem B3740849 : Blo 255820 3740849 := bstep (se 2 (by rfl) ⟨1402818, by rfl⟩ : syracuseStep 3740849 = 2805637) B2805637
theorem B923017 : Blo 255820 923017 := bstep (se 2 (by rfl) ⟨346131, by rfl⟩ : syracuseStep 923017 = 692263) B692263
theorem B1907023 : Blo 255820 1907023 := bstep (se 1 (by rfl) ⟨1430267, by rfl⟩ : syracuseStep 1907023 = 2860535) B2860535
theorem B793135 : Blo 255820 793135 := bstep (se 1 (by rfl) ⟨594851, by rfl⟩ : syracuseStep 793135 = 1189703) B1189703
theorem B2202173 : Blo 255820 2202173 := bstep (se 3 (by rfl) ⟨412907, by rfl⟩ : syracuseStep 2202173 = 825815) B825815
theorem B2464991 : Blo 255820 2464991 := bstep (se 1 (by rfl) ⟨1848743, by rfl⟩ : syracuseStep 2464991 = 3697487) B3697487
theorem B3218665 : Blo 255820 3218665 := bstep (se 2 (by rfl) ⟨1206999, by rfl⟩ : syracuseStep 3218665 = 2413999) B2413999
theorem B1416701 : Blo 255820 1416701 := bstep (se 3 (by rfl) ⟨265631, by rfl⟩ : syracuseStep 1416701 = 531263) B531263
theorem B2924747 : Blo 255820 2924747 := bstep (se 1 (by rfl) ⟨2193560, by rfl⟩ : syracuseStep 2924747 = 4387121) B4387121
theorem B369307 : Blo 255820 369307 := bstep (se 1 (by rfl) ⟨276980, by rfl⟩ : syracuseStep 369307 = 553961) B553961
theorem B10527853 : Blo 255820 10527853 := bstep (se 3 (by rfl) ⟨1973972, by rfl⟩ : syracuseStep 10527853 = 3947945) B3947945
theorem B2926205 : Blo 255820 2926205 := bstep (se 3 (by rfl) ⟨548663, by rfl⟩ : syracuseStep 2926205 = 1097327) B1097327
theorem B2795431 : Blo 255820 2795431 := bstep (se 1 (by rfl) ⟨2096573, by rfl⟩ : syracuseStep 2795431 = 4193147) B4193147
theorem B2206547 : Blo 255820 2206547 := bstep (se 1 (by rfl) ⟨1654910, by rfl⟩ : syracuseStep 2206547 = 3309821) B3309821
theorem B1944485 : Blo 255820 1944485 := bstep (se 4 (by rfl) ⟨182295, by rfl⟩ : syracuseStep 1944485 = 364591) B364591
theorem B437359 : Blo 255820 437359 := bstep (se 1 (by rfl) ⟨328019, by rfl⟩ : syracuseStep 437359 = 656039) B656039
theorem B7482617 : Blo 255820 7482617 := bstep (se 2 (by rfl) ⟨2805981, by rfl⟩ : syracuseStep 7482617 = 5611963) B5611963
theorem B47984237 : Blo 255820 47984237 := bstep (se 3 (by rfl) ⟨8997044, by rfl⟩ : syracuseStep 47984237 = 17994089) B17994089
theorem B732827 : Blo 255820 732827 := bstep (se 1 (by rfl) ⟨549620, by rfl⟩ : syracuseStep 732827 = 1099241) B1099241
theorem B438095 : Blo 255820 438095 := bstep (se 1 (by rfl) ⟨328571, by rfl⟩ : syracuseStep 438095 = 657143) B657143
theorem B274375 : Blo 255820 274375 := bstep (se 1 (by rfl) ⟨205781, by rfl⟩ : syracuseStep 274375 = 411563) B411563
theorem B733465 : Blo 255820 733465 := bstep (se 2 (by rfl) ⟨275049, by rfl⟩ : syracuseStep 733465 = 550099) B550099
theorem B4731301 : Blo 255820 4731301 := bstep (se 4 (by rfl) ⟨443559, by rfl⟩ : syracuseStep 4731301 = 887119) B887119
theorem B864701 : Blo 255820 864701 := bstep (se 3 (by rfl) ⟨162131, by rfl⟩ : syracuseStep 864701 = 324263) B324263
theorem B865673 : Blo 255820 865673 := bstep (se 2 (by rfl) ⟨324627, by rfl⟩ : syracuseStep 865673 = 649255) B649255
theorem B2471447 : Blo 255820 2471447 := bstep (se 1 (by rfl) ⟨1853585, by rfl⟩ : syracuseStep 2471447 = 3707171) B3707171
theorem B4699781 : Blo 255820 4699781 := bstep (se 4 (by rfl) ⟨440604, by rfl⟩ : syracuseStep 4699781 = 881209) B881209
theorem B833657 : Blo 255820 833657 := bstep (se 2 (by rfl) ⟨312621, by rfl⟩ : syracuseStep 833657 = 625243) B625243
theorem B998183 : Blo 255820 998183 := bstep (se 1 (by rfl) ⟨748637, by rfl⟩ : syracuseStep 998183 = 1497275) B1497275
theorem B867401 : Blo 255820 867401 := bstep (se 2 (by rfl) ⟨325275, by rfl⟩ : syracuseStep 867401 = 650551) B650551
theorem B1948859 : Blo 255820 1948859 := bstep (se 1 (by rfl) ⟨1461644, by rfl⟩ : syracuseStep 1948859 = 2923289) B2923289
theorem B2211947 : Blo 255820 2211947 := bstep (se 1 (by rfl) ⟨1658960, by rfl⟩ : syracuseStep 2211947 = 3317921) B3317921
theorem B1459367 : Blo 255820 1459367 := bstep (se 1 (by rfl) ⟨1094525, by rfl⟩ : syracuseStep 1459367 = 2189051) B2189051
theorem B935675 : Blo 255820 935675 := bstep (se 1 (by rfl) ⟨701756, by rfl⟩ : syracuseStep 935675 = 1403513) B1403513
theorem B576251 : Blo 255820 576251 := bstep (se 1 (by rfl) ⟨432188, by rfl⟩ : syracuseStep 576251 = 864377) B864377
theorem B412703 : Blo 255820 412703 := bstep (se 1 (by rfl) ⟨309527, by rfl⟩ : syracuseStep 412703 = 619055) B619055
theorem B1232171 : Blo 255820 1232171 := bstep (se 1 (by rfl) ⟨924128, by rfl⟩ : syracuseStep 1232171 = 1848257) B1848257
theorem B412985 : Blo 255820 412985 := bstep (se 2 (by rfl) ⟨154869, by rfl⟩ : syracuseStep 412985 = 309739) B309739
theorem B1298105 : Blo 255820 1298105 := bstep (se 2 (by rfl) ⟨486789, by rfl⟩ : syracuseStep 1298105 = 973579) B973579
theorem B125751523 : Blo 255820 125751523 := bstep (se 1 (by rfl) ⟨94313642, by rfl⟩ : syracuseStep 125751523 = 188627285) B188627285
theorem B1659113 : Blo 255820 1659113 := bstep (se 2 (by rfl) ⟨622167, by rfl⟩ : syracuseStep 1659113 = 1244335) B1244335
theorem B1462535 : Blo 255820 1462535 := bstep (se 1 (by rfl) ⟨1096901, by rfl⟩ : syracuseStep 1462535 = 2193803) B2193803
theorem B577961 : Blo 255820 577961 := bstep (se 2 (by rfl) ⟨216735, by rfl⟩ : syracuseStep 577961 = 433471) B433471
theorem B971423 : Blo 255820 971423 := bstep (se 1 (by rfl) ⟨728567, by rfl⟩ : syracuseStep 971423 = 1457135) B1457135
theorem B578303 : Blo 255820 578303 := bstep (se 1 (by rfl) ⟨433727, by rfl⟩ : syracuseStep 578303 = 867455) B867455
theorem B1397675 : Blo 255820 1397675 := bstep (se 1 (by rfl) ⟨1048256, by rfl⟩ : syracuseStep 1397675 = 2096513) B2096513
theorem B1233863 : Blo 255820 1233863 := bstep (se 1 (by rfl) ⟨925397, by rfl⟩ : syracuseStep 1233863 = 1850795) B1850795
theorem B1397801 : Blo 255820 1397801 := bstep (se 2 (by rfl) ⟨524175, by rfl⟩ : syracuseStep 1397801 = 1048351) B1048351
theorem B578663 : Blo 255820 578663 := bstep (se 1 (by rfl) ⟨433997, by rfl⟩ : syracuseStep 578663 = 867995) B867995
theorem B578879 : Blo 255820 578879 := bstep (se 1 (by rfl) ⟨434159, by rfl⟩ : syracuseStep 578879 = 868319) B868319
theorem B1103327 : Blo 255820 1103327 := bstep (se 1 (by rfl) ⟨827495, by rfl⟩ : syracuseStep 1103327 = 1654991) B1654991
theorem B16570169 : Blo 255820 16570169 := bstep (se 2 (by rfl) ⟨6213813, by rfl⟩ : syracuseStep 16570169 = 12427627) B12427627
theorem B15849431 : Blo 255820 15849431 := bstep (se 1 (by rfl) ⟨11887073, by rfl⟩ : syracuseStep 15849431 = 23774147) B23774147
theorem B1464425 : Blo 255820 1464425 := bstep (se 2 (by rfl) ⟨549159, by rfl⟩ : syracuseStep 1464425 = 1098319) B1098319
theorem B579887 : Blo 255820 579887 := bstep (se 1 (by rfl) ⟨434915, by rfl⟩ : syracuseStep 579887 = 869831) B869831
theorem B383753 : Blo 255820 383753 := bstep (se 2 (by rfl) ⟨143907, by rfl⟩ : syracuseStep 383753 = 287815) B287815
theorem B383993 : Blo 255820 383993 := bstep (se 2 (by rfl) ⟨143997, by rfl⟩ : syracuseStep 383993 = 287995) B287995
theorem B580769 : Blo 255820 580769 := bstep (se 2 (by rfl) ⟨217788, by rfl⟩ : syracuseStep 580769 = 435577) B435577
theorem B384491 : Blo 255820 384491 := bstep (se 1 (by rfl) ⟨288368, by rfl⟩ : syracuseStep 384491 = 576737) B576737
theorem B1564211 : Blo 255820 1564211 := bstep (se 1 (by rfl) ⟨1173158, by rfl⟩ : syracuseStep 1564211 = 2346317) B2346317
theorem B581183 : Blo 255820 581183 := bstep (se 1 (by rfl) ⟨435887, by rfl⟩ : syracuseStep 581183 = 871775) B871775
theorem B548527 : Blo 255820 548527 := bstep (se 1 (by rfl) ⟨411395, by rfl⟩ : syracuseStep 548527 = 822791) B822791
theorem B581831 : Blo 255820 581831 := bstep (se 1 (by rfl) ⟨436373, by rfl⟩ : syracuseStep 581831 = 872747) B872747
theorem B876743 : Blo 255820 876743 := bstep (se 1 (by rfl) ⟨657557, by rfl⟩ : syracuseStep 876743 = 1315115) B1315115
theorem B17228161 : Blo 255820 17228161 := bstep (se 2 (by rfl) ⟨6460560, by rfl⟩ : syracuseStep 17228161 = 12921121) B12921121
theorem B385577 : Blo 255820 385577 := bstep (se 2 (by rfl) ⟨144591, by rfl⟩ : syracuseStep 385577 = 289183) B289183
theorem B1991465 : Blo 255820 1991465 := bstep (se 2 (by rfl) ⟨746799, by rfl⟩ : syracuseStep 1991465 = 1493599) B1493599
theorem B2646827 : Blo 255820 2646827 := bstep (se 1 (by rfl) ⟨1985120, by rfl⟩ : syracuseStep 2646827 = 3970241) B3970241
theorem B385991 : Blo 255820 385991 := bstep (se 1 (by rfl) ⟨289493, by rfl⟩ : syracuseStep 385991 = 578987) B578987
theorem B2188367 : Blo 255820 2188367 := bstep (se 1 (by rfl) ⟨1641275, by rfl⟩ : syracuseStep 2188367 = 3282551) B3282551
theorem B582911 : Blo 255820 582911 := bstep (se 1 (by rfl) ⟨437183, by rfl⟩ : syracuseStep 582911 = 874367) B874367
theorem B615863 : Blo 255820 615863 := bstep (se 1 (by rfl) ⟨461897, by rfl⟩ : syracuseStep 615863 = 923795) B923795
theorem B583163 : Blo 255820 583163 := bstep (se 1 (by rfl) ⟨437372, by rfl⟩ : syracuseStep 583163 = 874745) B874745
theorem B583271 : Blo 255820 583271 := bstep (se 1 (by rfl) ⟨437453, by rfl⟩ : syracuseStep 583271 = 874907) B874907
theorem B386729 : Blo 255820 386729 := bstep (se 2 (by rfl) ⟨145023, by rfl⟩ : syracuseStep 386729 = 290047) B290047
theorem B583433 : Blo 255820 583433 := bstep (se 2 (by rfl) ⟨218787, by rfl⟩ : syracuseStep 583433 = 437575) B437575
theorem B386855 : Blo 255820 386855 := bstep (se 1 (by rfl) ⟨290141, by rfl⟩ : syracuseStep 386855 = 580283) B580283
theorem B386927 : Blo 255820 386927 := bstep (se 1 (by rfl) ⟨290195, by rfl⟩ : syracuseStep 386927 = 580391) B580391
theorem B3008477 : Blo 255820 3008477 := bstep (se 3 (by rfl) ⟨564089, by rfl⟩ : syracuseStep 3008477 = 1128179) B1128179
theorem B387113 : Blo 255820 387113 := bstep (se 2 (by rfl) ⟨145167, by rfl⟩ : syracuseStep 387113 = 290335) B290335
theorem B387527 : Blo 255820 387527 := bstep (se 1 (by rfl) ⟨290645, by rfl⟩ : syracuseStep 387527 = 581291) B581291
theorem B649721 : Blo 255820 649721 := bstep (se 2 (by rfl) ⟨243645, by rfl⟩ : syracuseStep 649721 = 487291) B487291
theorem B256603 : Blo 255820 256603 := bstep (se 1 (by rfl) ⟨192452, by rfl⟩ : syracuseStep 256603 = 384905) B384905
theorem B649883 : Blo 255820 649883 := bstep (se 1 (by rfl) ⟨487412, by rfl⟩ : syracuseStep 649883 = 974825) B974825
theorem B256703 : Blo 255820 256703 := bstep (se 1 (by rfl) ⟨192527, by rfl⟩ : syracuseStep 256703 = 385055) B385055
theorem B2190077 : Blo 255820 2190077 := bstep (se 3 (by rfl) ⟨410639, by rfl⟩ : syracuseStep 2190077 = 821279) B821279
theorem B486175 : Blo 255820 486175 := bstep (se 1 (by rfl) ⟨364631, by rfl⟩ : syracuseStep 486175 = 729263) B729263
theorem B584585 : Blo 255820 584585 := bstep (se 2 (by rfl) ⟨219219, by rfl⟩ : syracuseStep 584585 = 438439) B438439
theorem B388007 : Blo 255820 388007 := bstep (se 1 (by rfl) ⟨291005, by rfl⟩ : syracuseStep 388007 = 582011) B582011
theorem B256959 : Blo 255820 256959 := bstep (se 1 (by rfl) ⟨192719, by rfl⟩ : syracuseStep 256959 = 385439) B385439
theorem B257115 : Blo 255820 257115 := bstep (se 1 (by rfl) ⟨192836, by rfl⟩ : syracuseStep 257115 = 385673) B385673
theorem B257275 : Blo 255820 257275 := bstep (se 1 (by rfl) ⟨192956, by rfl⟩ : syracuseStep 257275 = 385913) B385913
theorem B257471 : Blo 255820 257471 := bstep (se 1 (by rfl) ⟨193103, by rfl⟩ : syracuseStep 257471 = 386207) B386207
theorem B978439 : Blo 255820 978439 := bstep (se 1 (by rfl) ⟨733829, by rfl⟩ : syracuseStep 978439 = 1467659) B1467659
theorem B618113 : Blo 255820 618113 := bstep (se 2 (by rfl) ⟨231792, by rfl⟩ : syracuseStep 618113 = 463585) B463585
theorem B257691 : Blo 255820 257691 := bstep (se 1 (by rfl) ⟨193268, by rfl⟩ : syracuseStep 257691 = 386537) B386537
theorem B388895 : Blo 255820 388895 := bstep (se 1 (by rfl) ⟨291671, by rfl⟩ : syracuseStep 388895 = 583343) B583343
theorem B257883 : Blo 255820 257883 := bstep (se 1 (by rfl) ⟨193412, by rfl⟩ : syracuseStep 257883 = 386825) B386825
theorem B389099 : Blo 255820 389099 := bstep (se 1 (by rfl) ⟨291824, by rfl⟩ : syracuseStep 389099 = 583649) B583649
theorem B389147 : Blo 255820 389147 := bstep (se 1 (by rfl) ⟨291860, by rfl⟩ : syracuseStep 389147 = 583721) B583721
theorem B258095 : Blo 255820 258095 := bstep (se 1 (by rfl) ⟨193571, by rfl⟩ : syracuseStep 258095 = 387143) B387143
theorem B749663 : Blo 255820 749663 := bstep (se 1 (by rfl) ⟨562247, by rfl⟩ : syracuseStep 749663 = 1124495) B1124495
theorem B258159 : Blo 255820 258159 := bstep (se 1 (by rfl) ⟨193619, by rfl⟩ : syracuseStep 258159 = 387239) B387239
theorem B258215 : Blo 255820 258215 := bstep (se 1 (by rfl) ⟨193661, by rfl⟩ : syracuseStep 258215 = 387323) B387323
theorem B389375 : Blo 255820 389375 := bstep (se 1 (by rfl) ⟨292031, by rfl⟩ : syracuseStep 389375 = 584063) B584063
theorem B553243 : Blo 255820 553243 := bstep (se 1 (by rfl) ⟨414932, by rfl⟩ : syracuseStep 553243 = 829865) B829865
theorem B258495 : Blo 255820 258495 := bstep (se 1 (by rfl) ⟨193871, by rfl⟩ : syracuseStep 258495 = 387743) B387743
theorem B258607 : Blo 255820 258607 := bstep (se 1 (by rfl) ⟨193955, by rfl⟩ : syracuseStep 258607 = 387911) B387911
theorem B3470161 : Blo 255820 3470161 := bstep (se 2 (by rfl) ⟨1301310, by rfl⟩ : syracuseStep 3470161 = 2602621) B2602621
theorem B259007 : Blo 255820 259007 := bstep (se 1 (by rfl) ⟨194255, by rfl⟩ : syracuseStep 259007 = 388511) B388511
theorem B652313 : Blo 255820 652313 := bstep (se 2 (by rfl) ⟨244617, by rfl⟩ : syracuseStep 652313 = 489235) B489235
theorem B4945049 : Blo 255820 4945049 := bstep (se 2 (by rfl) ⟨1854393, by rfl⟩ : syracuseStep 4945049 = 3708787) B3708787
theorem B652475 : Blo 255820 652475 := bstep (se 1 (by rfl) ⟨489356, by rfl⟩ : syracuseStep 652475 = 978713) B978713
theorem B259455 : Blo 255820 259455 := bstep (se 1 (by rfl) ⟨194591, by rfl⟩ : syracuseStep 259455 = 389183) B389183
theorem B1964411 : Blo 255820 1964411 := bstep (se 1 (by rfl) ⟨1473308, by rfl⟩ : syracuseStep 1964411 = 2946617) B2946617
theorem B4422113 : Blo 255820 4422113 := bstep (se 2 (by rfl) ⟨1658292, by rfl⟩ : syracuseStep 4422113 = 3316585) B3316585
theorem B6650515 : Blo 255820 6650515 := bstep (se 1 (by rfl) ⟨4987886, by rfl⟩ : syracuseStep 6650515 = 9975773) B9975773
theorem B982313 : Blo 255820 982313 := bstep (se 2 (by rfl) ⟨368367, by rfl⟩ : syracuseStep 982313 = 736735) B736735
theorem B654713 : Blo 255820 654713 := bstep (se 2 (by rfl) ⟨245517, by rfl⟩ : syracuseStep 654713 = 491035) B491035
theorem B655087 : Blo 255820 655087 := bstep (se 1 (by rfl) ⟨491315, by rfl⟩ : syracuseStep 655087 = 982631) B982631
theorem B2490209 : Blo 255820 2490209 := bstep (se 2 (by rfl) ⟨933828, by rfl⟩ : syracuseStep 2490209 = 1867657) B1867657
theorem B1474631 : Blo 255820 1474631 := bstep (se 1 (by rfl) ⟨1105973, by rfl⟩ : syracuseStep 1474631 = 2211947) B2211947
theorem B22970881 : Blo 255820 22970881 := bstep (se 2 (by rfl) ⟨8614080, by rfl⟩ : syracuseStep 22970881 = 17228161) B17228161
theorem B492409 : Blo 255820 492409 := bstep (se 2 (by rfl) ⟨184653, by rfl⟩ : syracuseStep 492409 = 369307) B369307
theorem B623783 : Blo 255820 623783 := bstep (se 1 (by rfl) ⟨467837, by rfl⟩ : syracuseStep 623783 = 935675) B935675
theorem B25233605 : Blo 255820 25233605 := bstep (se 4 (by rfl) ⟨2365650, by rfl⟩ : syracuseStep 25233605 = 4731301) B4731301
theorem B821447 : Blo 255820 821447 := bstep (se 1 (by rfl) ⟨616085, by rfl⟩ : syracuseStep 821447 = 1232171) B1232171
theorem B526675 : Blo 255820 526675 := bstep (se 1 (by rfl) ⟨395006, by rfl⟩ : syracuseStep 526675 = 790013) B790013
theorem B4230053 : Blo 255820 4230053 := bstep (se 4 (by rfl) ⟨396567, by rfl⟩ : syracuseStep 4230053 = 793135) B793135
theorem B822575 : Blo 255820 822575 := bstep (se 1 (by rfl) ⟨616931, by rfl⟩ : syracuseStep 822575 = 1233863) B1233863
theorem B2493899 : Blo 255820 2493899 := bstep (se 1 (by rfl) ⟨1870424, by rfl⟩ : syracuseStep 2493899 = 3740849) B3740849
theorem B1642301 : Blo 255820 1642301 := bstep (se 3 (by rfl) ⟨307931, by rfl⟩ : syracuseStep 1642301 = 615863) B615863
theorem B11046779 : Blo 255820 11046779 := bstep (se 1 (by rfl) ⟨8285084, by rfl⟩ : syracuseStep 11046779 = 16570169) B16570169
theorem B1643327 : Blo 255820 1643327 := bstep (se 1 (by rfl) ⟨1232495, by rfl⟩ : syracuseStep 1643327 = 2464991) B2464991
theorem B365833 : Blo 255820 365833 := bstep (se 2 (by rfl) ⟨137187, by rfl⟩ : syracuseStep 365833 = 274375) B274375
theorem B4626881 : Blo 255820 4626881 := bstep (se 2 (by rfl) ⟨1735080, by rfl⟩ : syracuseStep 4626881 = 3470161) B3470161
theorem B2005651 : Blo 255820 2005651 := bstep (se 1 (by rfl) ⟨1504238, by rfl⟩ : syracuseStep 2005651 = 3008477) B3008477
theorem B433147 : Blo 255820 433147 := bstep (se 1 (by rfl) ⟨324860, by rfl⟩ : syracuseStep 433147 = 649721) B649721
theorem B433255 : Blo 255820 433255 := bstep (se 1 (by rfl) ⟨324941, by rfl⟩ : syracuseStep 433255 = 649883) B649883
theorem B4988411 : Blo 255820 4988411 := bstep (se 1 (by rfl) ⟨3741308, by rfl⟩ : syracuseStep 4988411 = 7482617) B7482617
theorem B31989491 : Blo 255820 31989491 := bstep (se 1 (by rfl) ⟨23992118, by rfl⟩ : syracuseStep 31989491 = 47984237) B47984237
theorem B499775 : Blo 255820 499775 := bstep (se 1 (by rfl) ⟨374831, by rfl⟩ : syracuseStep 499775 = 749663) B749663
theorem B434875 : Blo 255820 434875 := bstep (se 1 (by rfl) ⟨326156, by rfl⟩ : syracuseStep 434875 = 652313) B652313
theorem B434983 : Blo 255820 434983 := bstep (se 1 (by rfl) ⟨326237, by rfl⟩ : syracuseStep 434983 = 652475) B652475
theorem B1647631 : Blo 255820 1647631 := bstep (se 1 (by rfl) ⟨1235723, by rfl⟩ : syracuseStep 1647631 = 2471447) B2471447
theorem B665455 : Blo 255820 665455 := bstep (se 1 (by rfl) ⟨499091, by rfl⟩ : syracuseStep 665455 = 998183) B998183
theorem B731369 : Blo 255820 731369 := bstep (se 2 (by rfl) ⟨274263, by rfl⟩ : syracuseStep 731369 = 548527) B548527
theorem B436475 : Blo 255820 436475 := bstep (se 1 (by rfl) ⟨327356, by rfl⟩ : syracuseStep 436475 = 654713) B654713
theorem B437231 : Blo 255820 437231 := bstep (se 1 (by rfl) ⟨327923, by rfl⟩ : syracuseStep 437231 = 655847) B655847
theorem B437339 : Blo 255820 437339 := bstep (se 1 (by rfl) ⟨328004, by rfl⟩ : syracuseStep 437339 = 656009) B656009
theorem B699529 : Blo 255820 699529 := bstep (se 2 (by rfl) ⟨262323, by rfl⟩ : syracuseStep 699529 = 524647) B524647
theorem B8892341 : Blo 255820 8892341 := bstep (se 5 (by rfl) ⟨416828, by rfl⟩ : syracuseStep 8892341 = 833657) B833657
theorem B14037137 : Blo 255820 14037137 := bstep (se 2 (by rfl) ⟨5263926, by rfl⟩ : syracuseStep 14037137 = 10527853) B10527853
theorem B275135 : Blo 255820 275135 := bstep (se 1 (by rfl) ⟨206351, by rfl⟩ : syracuseStep 275135 = 412703) B412703
theorem B275323 : Blo 255820 275323 := bstep (se 1 (by rfl) ⟨206492, by rfl⟩ : syracuseStep 275323 = 412985) B412985
theorem B865403 : Blo 255820 865403 := bstep (se 1 (by rfl) ⟨649052, by rfl⟩ : syracuseStep 865403 = 1298105) B1298105
theorem B20166043 : Blo 255820 20166043 := bstep (se 1 (by rfl) ⟨15124532, by rfl⟩ : syracuseStep 20166043 = 30249065) B30249065
theorem B931783 : Blo 255820 931783 := bstep (se 1 (by rfl) ⟨698837, by rfl⟩ : syracuseStep 931783 = 1397675) B1397675
theorem B931867 : Blo 255820 931867 := bstep (se 1 (by rfl) ⟨698900, by rfl⟩ : syracuseStep 931867 = 1397801) B1397801
theorem B735551 : Blo 255820 735551 := bstep (se 1 (by rfl) ⟨551663, by rfl⟩ : syracuseStep 735551 = 1103327) B1103327
theorem B10566287 : Blo 255820 10566287 := bstep (se 1 (by rfl) ⟨7924715, by rfl⟩ : syracuseStep 10566287 = 15849431) B15849431
theorem B37665881 : Blo 255820 37665881 := bstep (se 2 (by rfl) ⟨14124705, by rfl⟩ : syracuseStep 37665881 = 28249411) B28249411
theorem B1949831 : Blo 255820 1949831 := bstep (se 1 (by rfl) ⟨1462373, by rfl⟩ : syracuseStep 1949831 = 2924747) B2924747
theorem B737657 : Blo 255820 737657 := bstep (se 2 (by rfl) ⟨276621, by rfl⟩ : syracuseStep 737657 = 553243) B553243
theorem B1327643 : Blo 255820 1327643 := bstep (se 1 (by rfl) ⟨995732, by rfl⟩ : syracuseStep 1327643 = 1991465) B1991465
theorem B1458911 : Blo 255820 1458911 := bstep (se 1 (by rfl) ⟨1094183, by rfl⟩ : syracuseStep 1458911 = 2188367) B2188367
theorem B443369 : Blo 255820 443369 := bstep (se 2 (by rfl) ⟨166263, by rfl⟩ : syracuseStep 443369 = 332527) B332527
theorem B1950803 : Blo 255820 1950803 := bstep (se 1 (by rfl) ⟨1463102, by rfl⟩ : syracuseStep 1950803 = 2926205) B2926205
theorem B1460051 : Blo 255820 1460051 := bstep (se 1 (by rfl) ⟨1095038, by rfl⟩ : syracuseStep 1460051 = 2190077) B2190077
theorem B1230689 : Blo 255820 1230689 := bstep (se 2 (by rfl) ⟨461508, by rfl⟩ : syracuseStep 1230689 = 923017) B923017
theorem B1296323 : Blo 255820 1296323 := bstep (se 1 (by rfl) ⟨972242, by rfl⟩ : syracuseStep 1296323 = 1944485) B1944485
theorem B412075 : Blo 255820 412075 := bstep (se 1 (by rfl) ⟨309056, by rfl⟩ : syracuseStep 412075 = 618113) B618113
theorem B576467 : Blo 255820 576467 := bstep (se 1 (by rfl) ⟨432350, by rfl⟩ : syracuseStep 576467 = 864701) B864701
theorem B2542697 : Blo 255820 2542697 := bstep (se 2 (by rfl) ⟨953511, by rfl⟩ : syracuseStep 2542697 = 1907023) B1907023
theorem B3296699 : Blo 255820 3296699 := bstep (se 1 (by rfl) ⟨2472524, by rfl⟩ : syracuseStep 3296699 = 4945049) B4945049
theorem B8867353 : Blo 255820 8867353 := bstep (se 2 (by rfl) ⟨3325257, by rfl⟩ : syracuseStep 8867353 = 6650515) B6650515
theorem B577115 : Blo 255820 577115 := bstep (se 1 (by rfl) ⟨432836, by rfl⟩ : syracuseStep 577115 = 865673) B865673
theorem B3133187 : Blo 255820 3133187 := bstep (se 1 (by rfl) ⟨2349890, by rfl⟩ : syracuseStep 3133187 = 4699781) B4699781
theorem B1954205 : Blo 255820 1954205 := bstep (se 3 (by rfl) ⟨366413, by rfl⟩ : syracuseStep 1954205 = 732827) B732827
theorem B578267 : Blo 255820 578267 := bstep (se 1 (by rfl) ⟨433700, by rfl⟩ : syracuseStep 578267 = 867401) B867401
theorem B1299239 : Blo 255820 1299239 := bstep (se 1 (by rfl) ⟨974429, by rfl⟩ : syracuseStep 1299239 = 1948859) B1948859
theorem B873449 : Blo 255820 873449 := bstep (se 2 (by rfl) ⟨327543, by rfl⟩ : syracuseStep 873449 = 655087) B655087
theorem B1660139 : Blo 255820 1660139 := bstep (se 1 (by rfl) ⟨1245104, by rfl⟩ : syracuseStep 1660139 = 2490209) B2490209
theorem B972911 : Blo 255820 972911 := bstep (se 1 (by rfl) ⟨729683, by rfl⟩ : syracuseStep 972911 = 1459367) B1459367
theorem B875123 : Blo 255820 875123 := bstep (se 1 (by rfl) ⟨656342, by rfl⟩ : syracuseStep 875123 = 1312685) B1312685
theorem B384167 : Blo 255820 384167 := bstep (se 1 (by rfl) ⟨288125, by rfl⟩ : syracuseStep 384167 = 576251) B576251
theorem B875933 : Blo 255820 875933 := bstep (se 3 (by rfl) ⟨164237, by rfl⟩ : syracuseStep 875933 = 328475) B328475
theorem B3727241 : Blo 255820 3727241 := bstep (se 2 (by rfl) ⟨1397715, by rfl⟩ : syracuseStep 3727241 = 2795431) B2795431
theorem B1106075 : Blo 255820 1106075 := bstep (se 1 (by rfl) ⟨829556, by rfl⟩ : syracuseStep 1106075 = 1659113) B1659113
theorem B975023 : Blo 255820 975023 := bstep (se 1 (by rfl) ⟨731267, by rfl⟩ : syracuseStep 975023 = 1462535) B1462535
theorem B975037 : Blo 255820 975037 := bstep (se 3 (by rfl) ⟨182819, by rfl⟩ : syracuseStep 975037 = 365639) B365639
theorem B385307 : Blo 255820 385307 := bstep (se 1 (by rfl) ⟨288980, by rfl⟩ : syracuseStep 385307 = 577961) B577961
theorem B647615 : Blo 255820 647615 := bstep (se 1 (by rfl) ⟨485711, by rfl⟩ : syracuseStep 647615 = 971423) B971423
theorem B385535 : Blo 255820 385535 := bstep (se 1 (by rfl) ⟨289151, by rfl⟩ : syracuseStep 385535 = 578303) B578303
theorem B81420823 : Blo 255820 81420823 := bstep (se 1 (by rfl) ⟨61065617, by rfl⟩ : syracuseStep 81420823 = 122131235) B122131235
theorem B385775 : Blo 255820 385775 := bstep (se 1 (by rfl) ⟨289331, by rfl⟩ : syracuseStep 385775 = 578663) B578663
theorem B2188093 : Blo 255820 2188093 := bstep (se 3 (by rfl) ⟨410267, by rfl⟩ : syracuseStep 2188093 = 820535) B820535
theorem B385919 : Blo 255820 385919 := bstep (se 1 (by rfl) ⟨289439, by rfl⟩ : syracuseStep 385919 = 578879) B578879
theorem B648233 : Blo 255820 648233 := bstep (se 2 (by rfl) ⟨243087, by rfl⟩ : syracuseStep 648233 = 486175) B486175
theorem B976283 : Blo 255820 976283 := bstep (se 1 (by rfl) ⟨732212, by rfl⟩ : syracuseStep 976283 = 1464425) B1464425
theorem B583145 : Blo 255820 583145 := bstep (se 2 (by rfl) ⟨218679, by rfl⟩ : syracuseStep 583145 = 437359) B437359
theorem B386591 : Blo 255820 386591 := bstep (se 1 (by rfl) ⟨289943, by rfl⟩ : syracuseStep 386591 = 579887) B579887
theorem B1468115 : Blo 255820 1468115 := bstep (se 1 (by rfl) ⟨1101086, by rfl⟩ : syracuseStep 1468115 = 2202173) B2202173
theorem B255835 : Blo 255820 255835 := bstep (se 1 (by rfl) ⟨191876, by rfl⟩ : syracuseStep 255835 = 383753) B383753
theorem B255995 : Blo 255820 255995 := bstep (se 1 (by rfl) ⟨191996, by rfl⟩ : syracuseStep 255995 = 383993) B383993
theorem B1304585 : Blo 255820 1304585 := bstep (se 2 (by rfl) ⟨489219, by rfl⟩ : syracuseStep 1304585 = 978439) B978439
theorem B387179 : Blo 255820 387179 := bstep (se 1 (by rfl) ⟨290384, by rfl⟩ : syracuseStep 387179 = 580769) B580769
theorem B256327 : Blo 255820 256327 := bstep (se 1 (by rfl) ⟨192245, by rfl⟩ : syracuseStep 256327 = 384491) B384491
theorem B944467 : Blo 255820 944467 := bstep (se 1 (by rfl) ⟨708350, by rfl⟩ : syracuseStep 944467 = 1416701) B1416701
theorem B1042807 : Blo 255820 1042807 := bstep (se 1 (by rfl) ⟨782105, by rfl⟩ : syracuseStep 1042807 = 1564211) B1564211
theorem B387455 : Blo 255820 387455 := bstep (se 1 (by rfl) ⟨290591, by rfl⟩ : syracuseStep 387455 = 581183) B581183
theorem B7432793 : Blo 255820 7432793 := bstep (se 2 (by rfl) ⟨2787297, by rfl⟩ : syracuseStep 7432793 = 5574595) B5574595
theorem B387887 : Blo 255820 387887 := bstep (se 1 (by rfl) ⟨290915, by rfl⟩ : syracuseStep 387887 = 581831) B581831
theorem B584495 : Blo 255820 584495 := bstep (se 1 (by rfl) ⟨438371, by rfl⟩ : syracuseStep 584495 = 876743) B876743
theorem B167668697 : Blo 255820 167668697 := bstep (se 2 (by rfl) ⟨62875761, by rfl⟩ : syracuseStep 167668697 = 125751523) B125751523
theorem B257051 : Blo 255820 257051 := bstep (se 1 (by rfl) ⟨192788, by rfl⟩ : syracuseStep 257051 = 385577) B385577
theorem B977953 : Blo 255820 977953 := bstep (se 2 (by rfl) ⟨366732, by rfl⟩ : syracuseStep 977953 = 733465) B733465
theorem B1764551 : Blo 255820 1764551 := bstep (se 1 (by rfl) ⟨1323413, by rfl⟩ : syracuseStep 1764551 = 2646827) B2646827
theorem B257327 : Blo 255820 257327 := bstep (se 1 (by rfl) ⟨192995, by rfl⟩ : syracuseStep 257327 = 385991) B385991
theorem B486881 : Blo 255820 486881 := bstep (se 2 (by rfl) ⟨182580, by rfl⟩ : syracuseStep 486881 = 365161) B365161
theorem B388607 : Blo 255820 388607 := bstep (se 1 (by rfl) ⟨291455, by rfl⟩ : syracuseStep 388607 = 582911) B582911
theorem B388775 : Blo 255820 388775 := bstep (se 1 (by rfl) ⟨291581, by rfl⟩ : syracuseStep 388775 = 583163) B583163
theorem B388847 : Blo 255820 388847 := bstep (se 1 (by rfl) ⟨291635, by rfl⟩ : syracuseStep 388847 = 583271) B583271
theorem B257819 : Blo 255820 257819 := bstep (se 1 (by rfl) ⟨193364, by rfl⟩ : syracuseStep 257819 = 386729) B386729
theorem B388955 : Blo 255820 388955 := bstep (se 1 (by rfl) ⟨291716, by rfl⟩ : syracuseStep 388955 = 583433) B583433
theorem B257903 : Blo 255820 257903 := bstep (se 1 (by rfl) ⟨193427, by rfl⟩ : syracuseStep 257903 = 386855) B386855
theorem B257951 : Blo 255820 257951 := bstep (se 1 (by rfl) ⟨193463, by rfl⟩ : syracuseStep 257951 = 386927) B386927
theorem B258075 : Blo 255820 258075 := bstep (se 1 (by rfl) ⟨193556, by rfl⟩ : syracuseStep 258075 = 387113) B387113
theorem B258351 : Blo 255820 258351 := bstep (se 1 (by rfl) ⟨193763, by rfl⟩ : syracuseStep 258351 = 387527) B387527
theorem B1471031 : Blo 255820 1471031 := bstep (se 1 (by rfl) ⟨1103273, by rfl⟩ : syracuseStep 1471031 = 2206547) B2206547
theorem B389723 : Blo 255820 389723 := bstep (se 1 (by rfl) ⟨292292, by rfl⟩ : syracuseStep 389723 = 584585) B584585
theorem B258671 : Blo 255820 258671 := bstep (se 1 (by rfl) ⟨194003, by rfl⟩ : syracuseStep 258671 = 388007) B388007
theorem B259263 : Blo 255820 259263 := bstep (se 1 (by rfl) ⟨194447, by rfl⟩ : syracuseStep 259263 = 388895) B388895
theorem B292063 : Blo 255820 292063 := bstep (se 1 (by rfl) ⟨219047, by rfl⟩ : syracuseStep 292063 = 438095) B438095
theorem B259399 : Blo 255820 259399 := bstep (se 1 (by rfl) ⟨194549, by rfl⟩ : syracuseStep 259399 = 389099) B389099
theorem B259431 : Blo 255820 259431 := bstep (se 1 (by rfl) ⟨194573, by rfl⟩ : syracuseStep 259431 = 389147) B389147
theorem B259583 : Blo 255820 259583 := bstep (se 1 (by rfl) ⟨194687, by rfl⟩ : syracuseStep 259583 = 389375) B389375
theorem B1309607 : Blo 255820 1309607 := bstep (se 1 (by rfl) ⟨982205, by rfl⟩ : syracuseStep 1309607 = 1964411) B1964411
theorem B4291553 : Blo 255820 4291553 := bstep (se 2 (by rfl) ⟨1609332, by rfl⟩ : syracuseStep 4291553 = 3218665) B3218665
theorem B2948075 : Blo 255820 2948075 := bstep (se 1 (by rfl) ⟨2211056, by rfl⟩ : syracuseStep 2948075 = 4422113) B4422113
theorem B654875 : Blo 255820 654875 := bstep (se 1 (by rfl) ⟨491156, by rfl⟩ : syracuseStep 654875 = 982313) B982313
theorem B983087 : Blo 255820 983087 := bstep (se 1 (by rfl) ⟨737315, by rfl⟩ : syracuseStep 983087 = 1474631) B1474631
theorem B491771 : Blo 255820 491771 := bstep (se 1 (by rfl) ⟨368828, by rfl⟩ : syracuseStep 491771 = 737657) B737657
theorem B885095 : Blo 255820 885095 := bstep (se 1 (by rfl) ⟨663821, by rfl⟩ : syracuseStep 885095 = 1327643) B1327643
theorem B2949533 : Blo 255820 2949533 := bstep (se 3 (by rfl) ⟨553037, by rfl⟩ : syracuseStep 2949533 = 1106075) B1106075
theorem B295579 : Blo 255820 295579 := bstep (se 1 (by rfl) ⟨221684, by rfl⟩ : syracuseStep 295579 = 443369) B443369
theorem B108561097 : Blo 255820 108561097 := bstep (se 2 (by rfl) ⟨40710411, by rfl⟩ : syracuseStep 108561097 = 81420823) B81420823
theorem B2917457 : Blo 255820 2917457 := bstep (se 2 (by rfl) ⟨1094046, by rfl⟩ : syracuseStep 2917457 = 2188093) B2188093
theorem B656545 : Blo 255820 656545 := bstep (se 2 (by rfl) ⟨246204, by rfl⟩ : syracuseStep 656545 = 492409) B492409
theorem B820459 : Blo 255820 820459 := bstep (se 1 (by rfl) ⟨615344, by rfl⟩ : syracuseStep 820459 = 1230689) B1230689
theorem B2196841 : Blo 255820 2196841 := bstep (se 2 (by rfl) ⟨823815, by rfl⟩ : syracuseStep 2196841 = 1647631) B1647631
theorem B2820035 : Blo 255820 2820035 := bstep (se 1 (by rfl) ⟨2115026, by rfl⟩ : syracuseStep 2820035 = 4230053) B4230053
theorem B2197799 : Blo 255820 2197799 := bstep (se 1 (by rfl) ⟨1648349, by rfl⟩ : syracuseStep 2197799 = 3296699) B3296699
theorem B887273 : Blo 255820 887273 := bstep (se 2 (by rfl) ⟨332727, by rfl⟩ : syracuseStep 887273 = 665455) B665455
theorem B3084587 : Blo 255820 3084587 := bstep (se 1 (by rfl) ⟨2313440, by rfl⟩ : syracuseStep 3084587 = 4626881) B4626881
theorem B431743 : Blo 255820 431743 := bstep (se 1 (by rfl) ⟨323807, by rfl⟩ : syracuseStep 431743 = 647615) B647615
theorem B432155 : Blo 255820 432155 := bstep (se 1 (by rfl) ⟨324116, by rfl⟩ : syracuseStep 432155 = 648233) B648233
theorem B367097 : Blo 255820 367097 := bstep (se 2 (by rfl) ⟨137661, by rfl⟩ : syracuseStep 367097 = 275323) B275323
theorem B4955195 : Blo 255820 4955195 := bstep (se 1 (by rfl) ⟨3716396, by rfl⟩ : syracuseStep 4955195 = 7432793) B7432793
theorem B111779131 : Blo 255820 111779131 := bstep (se 1 (by rfl) ⟨83834348, by rfl⟩ : syracuseStep 111779131 = 167668697) B167668697
theorem B11444141 : Blo 255820 11444141 := bstep (se 3 (by rfl) ⟨2145776, by rfl⟩ : syracuseStep 11444141 = 4291553) B4291553
theorem B25110587 : Blo 255820 25110587 := bstep (se 1 (by rfl) ⟨18832940, by rfl⟩ : syracuseStep 25110587 = 37665881) B37665881
theorem B436583 : Blo 255820 436583 := bstep (se 1 (by rfl) ⟨327437, by rfl⟩ : syracuseStep 436583 = 654875) B654875
theorem B864215 : Blo 255820 864215 := bstep (se 1 (by rfl) ⟨648161, by rfl⟩ : syracuseStep 864215 = 1296323) B1296323
theorem B16822403 : Blo 255820 16822403 := bstep (se 1 (by rfl) ⟨12616802, by rfl⟩ : syracuseStep 16822403 = 25233605) B25233605
theorem B733693 : Blo 255820 733693 := bstep (se 3 (by rfl) ⟨137567, by rfl⟩ : syracuseStep 733693 = 275135) B275135
theorem B1094867 : Blo 255820 1094867 := bstep (se 1 (by rfl) ⟨821150, by rfl⟩ : syracuseStep 1094867 = 1642301) B1642301
theorem B702233 : Blo 255820 702233 := bstep (se 2 (by rfl) ⟨263337, by rfl⟩ : syracuseStep 702233 = 526675) B526675
theorem B1390409 : Blo 255820 1390409 := bstep (se 2 (by rfl) ⟨521403, by rfl⟩ : syracuseStep 1390409 = 1042807) B1042807
theorem B866159 : Blo 255820 866159 := bstep (se 1 (by rfl) ⟨649619, by rfl⟩ : syracuseStep 866159 = 1299239) B1299239
theorem B1095551 : Blo 255820 1095551 := bstep (se 1 (by rfl) ⟨821663, by rfl⟩ : syracuseStep 1095551 = 1643327) B1643327
theorem B932705 : Blo 255820 932705 := bstep (se 2 (by rfl) ⟨349764, by rfl⟩ : syracuseStep 932705 = 699529) B699529
theorem B3325607 : Blo 255820 3325607 := bstep (se 1 (by rfl) ⟨2494205, by rfl⟩ : syracuseStep 3325607 = 4988411) B4988411
theorem B1950317 : Blo 255820 1950317 := bstep (se 3 (by rfl) ⟨365684, by rfl⟩ : syracuseStep 1950317 = 731369) B731369
theorem B869723 : Blo 255820 869723 := bstep (se 1 (by rfl) ⟨652292, by rfl⟩ : syracuseStep 869723 = 1304585) B1304585
theorem B26888057 : Blo 255820 26888057 := bstep (se 2 (by rfl) ⟨10083021, by rfl⟩ : syracuseStep 26888057 = 20166043) B20166043
theorem B9358091 : Blo 255820 9358091 := bstep (se 1 (by rfl) ⟨7018568, by rfl⟩ : syracuseStep 9358091 = 14037137) B14037137
theorem B576935 : Blo 255820 576935 := bstep (se 1 (by rfl) ⟨432701, by rfl⟩ : syracuseStep 576935 = 865403) B865403
theorem B2674201 : Blo 255820 2674201 := bstep (se 2 (by rfl) ⟨1002825, by rfl⟩ : syracuseStep 2674201 = 2005651) B2005651
theorem B577529 : Blo 255820 577529 := bstep (se 2 (by rfl) ⟨216573, by rfl⟩ : syracuseStep 577529 = 433147) B433147
theorem B577673 : Blo 255820 577673 := bstep (se 2 (by rfl) ⟨216627, by rfl⟩ : syracuseStep 577673 = 433255) B433255
theorem B873071 : Blo 255820 873071 := bstep (se 1 (by rfl) ⟨654803, by rfl⟩ : syracuseStep 873071 = 1309607) B1309607
theorem B1299887 : Blo 255820 1299887 := bstep (se 1 (by rfl) ⟨974915, by rfl⟩ : syracuseStep 1299887 = 1949831) B1949831
theorem B4969957 : Blo 255820 4969957 := bstep (se 4 (by rfl) ⟨465933, by rfl⟩ : syracuseStep 4969957 = 931867) B931867
theorem B1332733 : Blo 255820 1332733 := bstep (se 3 (by rfl) ⟨249887, by rfl⟩ : syracuseStep 1332733 = 499775) B499775
theorem B1300049 : Blo 255820 1300049 := bstep (se 2 (by rfl) ⟨487518, by rfl⟩ : syracuseStep 1300049 = 975037) B975037
theorem B972607 : Blo 255820 972607 := bstep (se 1 (by rfl) ⟨729455, by rfl⟩ : syracuseStep 972607 = 1458911) B1458911
theorem B30627841 : Blo 255820 30627841 := bstep (se 2 (by rfl) ⟨11485440, by rfl⟩ : syracuseStep 30627841 = 22970881) B22970881
theorem B1300535 : Blo 255820 1300535 := bstep (se 1 (by rfl) ⟨975401, by rfl⟩ : syracuseStep 1300535 = 1950803) B1950803
theorem B415855 : Blo 255820 415855 := bstep (se 1 (by rfl) ⟨311891, by rfl⟩ : syracuseStep 415855 = 623783) B623783
theorem B579833 : Blo 255820 579833 := bstep (se 2 (by rfl) ⟨217437, by rfl⟩ : syracuseStep 579833 = 434875) B434875
theorem B579977 : Blo 255820 579977 := bstep (se 2 (by rfl) ⟨217491, by rfl⟩ : syracuseStep 579977 = 434983) B434983
theorem B973367 : Blo 255820 973367 := bstep (se 1 (by rfl) ⟨730025, by rfl⟩ : syracuseStep 973367 = 1460051) B1460051
theorem B547631 : Blo 255820 547631 := bstep (se 1 (by rfl) ⟨410723, by rfl⟩ : syracuseStep 547631 = 821447) B821447
theorem B5037157 : Blo 255820 5037157 := bstep (se 4 (by rfl) ⟨472233, by rfl⟩ : syracuseStep 5037157 = 944467) B944467
theorem B384311 : Blo 255820 384311 := bstep (se 1 (by rfl) ⟨288233, by rfl⟩ : syracuseStep 384311 = 576467) B576467
theorem B1695131 : Blo 255820 1695131 := bstep (se 1 (by rfl) ⟨1271348, by rfl⟩ : syracuseStep 1695131 = 2542697) B2542697
theorem B548383 : Blo 255820 548383 := bstep (se 1 (by rfl) ⟨411287, by rfl⟩ : syracuseStep 548383 = 822575) B822575
theorem B1662599 : Blo 255820 1662599 := bstep (se 1 (by rfl) ⟨1246949, by rfl⟩ : syracuseStep 1662599 = 2493899) B2493899
theorem B384743 : Blo 255820 384743 := bstep (se 1 (by rfl) ⟨288557, by rfl⟩ : syracuseStep 384743 = 577115) B577115
theorem B2088791 : Blo 255820 2088791 := bstep (se 1 (by rfl) ⟨1566593, by rfl⟩ : syracuseStep 2088791 = 3133187) B3133187
theorem B7364519 : Blo 255820 7364519 := bstep (se 1 (by rfl) ⟨5523389, by rfl⟩ : syracuseStep 7364519 = 11046779) B11046779
theorem B1302803 : Blo 255820 1302803 := bstep (se 1 (by rfl) ⟨977102, by rfl⟩ : syracuseStep 1302803 = 1954205) B1954205
theorem B385511 : Blo 255820 385511 := bstep (se 1 (by rfl) ⟨289133, by rfl⟩ : syracuseStep 385511 = 578267) B578267
theorem B549433 : Blo 255820 549433 := bstep (se 2 (by rfl) ⟨206037, by rfl⟩ : syracuseStep 549433 = 412075) B412075
theorem B582299 : Blo 255820 582299 := bstep (se 1 (by rfl) ⟨436724, by rfl⟩ : syracuseStep 582299 = 873449) B873449
theorem B1106759 : Blo 255820 1106759 := bstep (se 1 (by rfl) ⟨830069, by rfl⟩ : syracuseStep 1106759 = 1660139) B1660139
theorem B1303937 : Blo 255820 1303937 := bstep (se 2 (by rfl) ⟨488976, by rfl⟩ : syracuseStep 1303937 = 977953) B977953
theorem B648607 : Blo 255820 648607 := bstep (se 1 (by rfl) ⟨486455, by rfl⟩ : syracuseStep 648607 = 972911) B972911
theorem B583415 : Blo 255820 583415 := bstep (se 1 (by rfl) ⟨437561, by rfl⟩ : syracuseStep 583415 = 875123) B875123
theorem B11823137 : Blo 255820 11823137 := bstep (se 2 (by rfl) ⟨4433676, by rfl⟩ : syracuseStep 11823137 = 8867353) B8867353
theorem B256111 : Blo 255820 256111 := bstep (se 1 (by rfl) ⟨192083, by rfl⟩ : syracuseStep 256111 = 384167) B384167
theorem B583955 : Blo 255820 583955 := bstep (se 1 (by rfl) ⟨437966, by rfl⟩ : syracuseStep 583955 = 875933) B875933
theorem B21326327 : Blo 255820 21326327 := bstep (se 1 (by rfl) ⟨15994745, by rfl⟩ : syracuseStep 21326327 = 31989491) B31989491
theorem B2484827 : Blo 255820 2484827 := bstep (se 1 (by rfl) ⟨1863620, by rfl⟩ : syracuseStep 2484827 = 3727241) B3727241
theorem B650015 : Blo 255820 650015 := bstep (se 1 (by rfl) ⟨487511, by rfl⟩ : syracuseStep 650015 = 975023) B975023
theorem B256871 : Blo 255820 256871 := bstep (se 1 (by rfl) ⟨192653, by rfl⟩ : syracuseStep 256871 = 385307) B385307
theorem B257023 : Blo 255820 257023 := bstep (se 1 (by rfl) ⟨192767, by rfl⟩ : syracuseStep 257023 = 385535) B385535
theorem B257183 : Blo 255820 257183 := bstep (se 1 (by rfl) ⟨192887, by rfl⟩ : syracuseStep 257183 = 385775) B385775
theorem B257279 : Blo 255820 257279 := bstep (se 1 (by rfl) ⟨192959, by rfl⟩ : syracuseStep 257279 = 385919) B385919
theorem B650855 : Blo 255820 650855 := bstep (se 1 (by rfl) ⟨488141, by rfl⟩ : syracuseStep 650855 = 976283) B976283
theorem B388763 : Blo 255820 388763 := bstep (se 1 (by rfl) ⟨291572, by rfl⟩ : syracuseStep 388763 = 583145) B583145
theorem B257727 : Blo 255820 257727 := bstep (se 1 (by rfl) ⟨193295, by rfl⟩ : syracuseStep 257727 = 386591) B386591
theorem B978743 : Blo 255820 978743 := bstep (se 1 (by rfl) ⟨734057, by rfl⟩ : syracuseStep 978743 = 1468115) B1468115
theorem B258119 : Blo 255820 258119 := bstep (se 1 (by rfl) ⟨193589, by rfl⟩ : syracuseStep 258119 = 387179) B387179
theorem B290983 : Blo 255820 290983 := bstep (se 1 (by rfl) ⟨218237, by rfl⟩ : syracuseStep 290983 = 436475) B436475
theorem B258303 : Blo 255820 258303 := bstep (se 1 (by rfl) ⟨193727, by rfl⟩ : syracuseStep 258303 = 387455) B387455
theorem B389417 : Blo 255820 389417 := bstep (se 2 (by rfl) ⟨146031, by rfl⟩ : syracuseStep 389417 = 292063) B292063
theorem B487777 : Blo 255820 487777 := bstep (se 2 (by rfl) ⟨182916, by rfl⟩ : syracuseStep 487777 = 365833) B365833
theorem B258591 : Blo 255820 258591 := bstep (se 1 (by rfl) ⟨193943, by rfl⟩ : syracuseStep 258591 = 387887) B387887
theorem B389663 : Blo 255820 389663 := bstep (se 1 (by rfl) ⟨292247, by rfl⟩ : syracuseStep 389663 = 584495) B584495
theorem B291487 : Blo 255820 291487 := bstep (se 1 (by rfl) ⟨218615, by rfl⟩ : syracuseStep 291487 = 437231) B437231
theorem B291559 : Blo 255820 291559 := bstep (se 1 (by rfl) ⟨218669, by rfl⟩ : syracuseStep 291559 = 437339) B437339
theorem B1176367 : Blo 255820 1176367 := bstep (se 1 (by rfl) ⟨882275, by rfl⟩ : syracuseStep 1176367 = 1764551) B1764551
theorem B324587 : Blo 255820 324587 := bstep (se 1 (by rfl) ⟨243440, by rfl⟩ : syracuseStep 324587 = 486881) B486881
theorem B259071 : Blo 255820 259071 := bstep (se 1 (by rfl) ⟨194303, by rfl⟩ : syracuseStep 259071 = 388607) B388607
theorem B259183 : Blo 255820 259183 := bstep (se 1 (by rfl) ⟨194387, by rfl⟩ : syracuseStep 259183 = 388775) B388775
theorem B259231 : Blo 255820 259231 := bstep (se 1 (by rfl) ⟨194423, by rfl⟩ : syracuseStep 259231 = 388847) B388847
theorem B259303 : Blo 255820 259303 := bstep (se 1 (by rfl) ⟨194477, by rfl⟩ : syracuseStep 259303 = 388955) B388955
theorem B1242377 : Blo 255820 1242377 := bstep (se 2 (by rfl) ⟨465891, by rfl⟩ : syracuseStep 1242377 = 931783) B931783
theorem B5928227 : Blo 255820 5928227 := bstep (se 1 (by rfl) ⟨4446170, by rfl⟩ : syracuseStep 5928227 = 8892341) B8892341
theorem B980687 : Blo 255820 980687 := bstep (se 1 (by rfl) ⟨735515, by rfl⟩ : syracuseStep 980687 = 1471031) B1471031
theorem B259815 : Blo 255820 259815 := bstep (se 1 (by rfl) ⟨194861, by rfl⟩ : syracuseStep 259815 = 389723) B389723
theorem B490367 : Blo 255820 490367 := bstep (se 1 (by rfl) ⟨367775, by rfl⟩ : syracuseStep 490367 = 735551) B735551
theorem B7044191 : Blo 255820 7044191 := bstep (se 1 (by rfl) ⟨5283143, by rfl⟩ : syracuseStep 7044191 = 10566287) B10566287
theorem B1965383 : Blo 255820 1965383 := bstep (se 1 (by rfl) ⟨1474037, by rfl⟩ : syracuseStep 1965383 = 2948075) B2948075
theorem B655391 : Blo 255820 655391 := bstep (se 1 (by rfl) ⟨491543, by rfl⟩ : syracuseStep 655391 = 983087) B983087
theorem B590063 : Blo 255820 590063 := bstep (se 1 (by rfl) ⟨442547, by rfl⟩ : syracuseStep 590063 = 885095) B885095
theorem B1966355 : Blo 255820 1966355 := bstep (se 1 (by rfl) ⟨1474766, by rfl⟩ : syracuseStep 1966355 = 2949533) B2949533
theorem B1311389 : Blo 255820 1311389 := bstep (se 3 (by rfl) ⟨245885, by rfl⟩ : syracuseStep 1311389 = 491771) B491771
theorem B17925371 : Blo 255820 17925371 := bstep (se 1 (by rfl) ⟨13444028, by rfl⟩ : syracuseStep 17925371 = 26888057) B26888057
theorem B591515 : Blo 255820 591515 := bstep (se 1 (by rfl) ⟨443636, by rfl⟩ : syracuseStep 591515 = 887273) B887273
theorem B1576421 : Blo 255820 1576421 := bstep (se 4 (by rfl) ⟨147789, by rfl⟩ : syracuseStep 1576421 = 295579) B295579
theorem B365087 : Blo 255820 365087 := bstep (se 1 (by rfl) ⟨273815, by rfl⟩ : syracuseStep 365087 = 547631) B547631
theorem B433343 : Blo 255820 433343 := bstep (se 1 (by rfl) ⟨325007, by rfl⟩ : syracuseStep 433343 = 650015) B650015
theorem B6626609 : Blo 255820 6626609 := bstep (se 2 (by rfl) ⟨2484978, by rfl⟩ : syracuseStep 6626609 = 4969957) B4969957
theorem B1776977 : Blo 255820 1776977 := bstep (se 2 (by rfl) ⟨666366, by rfl⟩ : syracuseStep 1776977 = 1332733) B1332733
theorem B433903 : Blo 255820 433903 := bstep (se 1 (by rfl) ⟨325427, by rfl⟩ : syracuseStep 433903 = 650855) B650855
theorem B40837121 : Blo 255820 40837121 := bstep (se 2 (by rfl) ⟨15313920, by rfl⟩ : syracuseStep 40837121 = 30627841) B30627841
theorem B11214935 : Blo 255820 11214935 := bstep (se 1 (by rfl) ⟨8411201, by rfl⟩ : syracuseStep 11214935 = 16822403) B16822403
theorem B729911 : Blo 255820 729911 := bstep (se 1 (by rfl) ⟨547433, by rfl⟩ : syracuseStep 729911 = 1094867) B1094867
theorem B828251 : Blo 255820 828251 := bstep (se 1 (by rfl) ⟨621188, by rfl⟩ : syracuseStep 828251 = 1242377) B1242377
theorem B468155 : Blo 255820 468155 := bstep (se 1 (by rfl) ⟨351116, by rfl⟩ : syracuseStep 468155 = 702233) B702233
theorem B926939 : Blo 255820 926939 := bstep (se 1 (by rfl) ⟨695204, by rfl⟩ : syracuseStep 926939 = 1390409) B1390409
theorem B730367 : Blo 255820 730367 := bstep (se 1 (by rfl) ⟨547775, by rfl⟩ : syracuseStep 730367 = 1095551) B1095551
theorem B149038841 : Blo 255820 149038841 := bstep (se 2 (by rfl) ⟨55889565, by rfl⟩ : syracuseStep 149038841 = 111779131) B111779131
theorem B731177 : Blo 255820 731177 := bstep (se 2 (by rfl) ⟨274191, by rfl⟩ : syracuseStep 731177 = 548383) B548383
theorem B4696127 : Blo 255820 4696127 := bstep (se 1 (by rfl) ⟨3522095, by rfl⟩ : syracuseStep 4696127 = 7044191) B7044191
theorem B1944971 : Blo 255820 1944971 := bstep (se 1 (by rfl) ⟨1458728, by rfl⟩ : syracuseStep 1944971 = 2917457) B2917457
theorem B732577 : Blo 255820 732577 := bstep (se 2 (by rfl) ⟨274716, by rfl⟩ : syracuseStep 732577 = 549433) B549433
theorem B144748129 : Blo 255820 144748129 := bstep (se 2 (by rfl) ⟨54280548, by rfl⟩ : syracuseStep 144748129 = 108561097) B108561097
theorem B1880023 : Blo 255820 1880023 := bstep (se 1 (by rfl) ⟨1410017, by rfl⟩ : syracuseStep 1880023 = 2820035) B2820035
theorem B1093945 : Blo 255820 1093945 := bstep (se 2 (by rfl) ⟨410229, by rfl⟩ : syracuseStep 1093945 = 820459) B820459
theorem B2929121 : Blo 255820 2929121 := bstep (se 2 (by rfl) ⟨1098420, by rfl⟩ : syracuseStep 2929121 = 2196841) B2196841
theorem B6238727 : Blo 255820 6238727 := bstep (se 1 (by rfl) ⟨4679045, by rfl⟩ : syracuseStep 6238727 = 9358091) B9358091
theorem B864809 : Blo 255820 864809 := bstep (se 2 (by rfl) ⟨324303, by rfl⟩ : syracuseStep 864809 = 648607) B648607
theorem B865565 : Blo 255820 865565 := bstep (se 3 (by rfl) ⟨162293, by rfl⟩ : syracuseStep 865565 = 324587) B324587
theorem B866591 : Blo 255820 866591 := bstep (se 1 (by rfl) ⟨649943, by rfl⟩ : syracuseStep 866591 = 1299887) B1299887
theorem B866699 : Blo 255820 866699 := bstep (se 1 (by rfl) ⟨650024, by rfl⟩ : syracuseStep 866699 = 1300049) B1300049
theorem B867023 : Blo 255820 867023 := bstep (se 1 (by rfl) ⟨650267, by rfl⟩ : syracuseStep 867023 = 1300535) B1300535
theorem B1130087 : Blo 255820 1130087 := bstep (se 1 (by rfl) ⟨847565, by rfl⟩ : syracuseStep 1130087 = 1695131) B1695131
theorem B1392527 : Blo 255820 1392527 := bstep (se 1 (by rfl) ⟨1044395, by rfl⟩ : syracuseStep 1392527 = 2088791) B2088791
theorem B868535 : Blo 255820 868535 := bstep (se 1 (by rfl) ⟨651401, by rfl⟩ : syracuseStep 868535 = 1302803) B1302803
theorem B737839 : Blo 255820 737839 := bstep (se 1 (by rfl) ⟨553379, by rfl⟩ : syracuseStep 737839 = 1106759) B1106759
theorem B869291 : Blo 255820 869291 := bstep (se 1 (by rfl) ⟨651968, by rfl⟩ : syracuseStep 869291 = 1303937) B1303937
theorem B7882091 : Blo 255820 7882091 := bstep (se 1 (by rfl) ⟨5911568, by rfl⟩ : syracuseStep 7882091 = 11823137) B11823137
theorem B1656551 : Blo 255820 1656551 := bstep (se 1 (by rfl) ⟨1242413, by rfl⟩ : syracuseStep 1656551 = 2484827) B2484827
theorem B575657 : Blo 255820 575657 := bstep (se 2 (by rfl) ⟨215871, by rfl⟩ : syracuseStep 575657 = 431743) B431743
theorem B1296809 : Blo 255820 1296809 := bstep (se 2 (by rfl) ⟨486303, by rfl⟩ : syracuseStep 1296809 = 972607) B972607
theorem B576143 : Blo 255820 576143 := bstep (se 1 (by rfl) ⟨432107, by rfl⟩ : syracuseStep 576143 = 864215) B864215
theorem B3952151 : Blo 255820 3952151 := bstep (se 1 (by rfl) ⟨2964113, by rfl⟩ : syracuseStep 3952151 = 5928227) B5928227
theorem B577439 : Blo 255820 577439 := bstep (se 1 (by rfl) ⟨433079, by rfl⟩ : syracuseStep 577439 = 866159) B866159
theorem B2217071 : Blo 255820 2217071 := bstep (se 1 (by rfl) ⟨1662803, by rfl⟩ : syracuseStep 2217071 = 3325607) B3325607
theorem B1300211 : Blo 255820 1300211 := bstep (se 1 (by rfl) ⟨975158, by rfl⟩ : syracuseStep 1300211 = 1950317) B1950317
theorem B579815 : Blo 255820 579815 := bstep (se 1 (by rfl) ⟨434861, by rfl⟩ : syracuseStep 579815 = 869723) B869723
theorem B1465199 : Blo 255820 1465199 := bstep (se 1 (by rfl) ⟨1098899, by rfl⟩ : syracuseStep 1465199 = 2197799) B2197799
theorem B875393 : Blo 255820 875393 := bstep (se 2 (by rfl) ⟨328272, by rfl⟩ : syracuseStep 875393 = 656545) B656545
theorem B384623 : Blo 255820 384623 := bstep (se 1 (by rfl) ⟨288467, by rfl⟩ : syracuseStep 384623 = 576935) B576935
theorem B385019 : Blo 255820 385019 := bstep (se 1 (by rfl) ⟨288764, by rfl⟩ : syracuseStep 385019 = 577529) B577529
theorem B385115 : Blo 255820 385115 := bstep (se 1 (by rfl) ⟨288836, by rfl⟩ : syracuseStep 385115 = 577673) B577673
theorem B2056391 : Blo 255820 2056391 := bstep (se 1 (by rfl) ⟨1542293, by rfl⟩ : syracuseStep 2056391 = 3084587) B3084587
theorem B582047 : Blo 255820 582047 := bstep (se 1 (by rfl) ⟨436535, by rfl⟩ : syracuseStep 582047 = 873071) B873071
theorem B288103 : Blo 255820 288103 := bstep (se 1 (by rfl) ⟨216077, by rfl⟩ : syracuseStep 288103 = 432155) B432155
theorem B386555 : Blo 255820 386555 := bstep (se 1 (by rfl) ⟨289916, by rfl⟩ : syracuseStep 386555 = 579833) B579833
theorem B386651 : Blo 255820 386651 := bstep (se 1 (by rfl) ⟨289988, by rfl⟩ : syracuseStep 386651 = 579977) B579977
theorem B648911 : Blo 255820 648911 := bstep (se 1 (by rfl) ⟨486683, by rfl⟩ : syracuseStep 648911 = 973367) B973367
theorem B3565601 : Blo 255820 3565601 := bstep (se 2 (by rfl) ⟨1337100, by rfl⟩ : syracuseStep 3565601 = 2674201) B2674201
theorem B3303463 : Blo 255820 3303463 := bstep (se 1 (by rfl) ⟨2477597, by rfl⟩ : syracuseStep 3303463 = 4955195) B4955195
theorem B256207 : Blo 255820 256207 := bstep (se 1 (by rfl) ⟨192155, by rfl⟩ : syracuseStep 256207 = 384311) B384311
theorem B1108399 : Blo 255820 1108399 := bstep (se 1 (by rfl) ⟨831299, by rfl⟩ : syracuseStep 1108399 = 1662599) B1662599
theorem B256495 : Blo 255820 256495 := bstep (se 1 (by rfl) ⟨192371, by rfl⟩ : syracuseStep 256495 = 384743) B384743
theorem B4909679 : Blo 255820 4909679 := bstep (se 1 (by rfl) ⟨3682259, by rfl⟩ : syracuseStep 4909679 = 7364519) B7364519
theorem B7629427 : Blo 255820 7629427 := bstep (se 1 (by rfl) ⟨5722070, by rfl⟩ : syracuseStep 7629427 = 11444141) B11444141
theorem B387977 : Blo 255820 387977 := bstep (se 2 (by rfl) ⟨145491, by rfl⟩ : syracuseStep 387977 = 290983) B290983
theorem B257007 : Blo 255820 257007 := bstep (se 1 (by rfl) ⟨192755, by rfl⟩ : syracuseStep 257007 = 385511) B385511
theorem B388199 : Blo 255820 388199 := bstep (se 1 (by rfl) ⟨291149, by rfl⟩ : syracuseStep 388199 = 582299) B582299
theorem B650369 : Blo 255820 650369 := bstep (se 2 (by rfl) ⟨243888, by rfl⟩ : syracuseStep 650369 = 487777) B487777
theorem B978257 : Blo 255820 978257 := bstep (se 2 (by rfl) ⟨366846, by rfl⟩ : syracuseStep 978257 = 733693) B733693
theorem B388649 : Blo 255820 388649 := bstep (se 2 (by rfl) ⟨145743, by rfl⟩ : syracuseStep 388649 = 291487) B291487
theorem B388745 : Blo 255820 388745 := bstep (se 2 (by rfl) ⟨145779, by rfl⟩ : syracuseStep 388745 = 291559) B291559
theorem B1568489 : Blo 255820 1568489 := bstep (se 2 (by rfl) ⟨588183, by rfl⟩ : syracuseStep 1568489 = 1176367) B1176367
theorem B388943 : Blo 255820 388943 := bstep (se 1 (by rfl) ⟨291707, by rfl⟩ : syracuseStep 388943 = 583415) B583415
theorem B978925 : Blo 255820 978925 := bstep (se 3 (by rfl) ⟨183548, by rfl⟩ : syracuseStep 978925 = 367097) B367097
theorem B16740391 : Blo 255820 16740391 := bstep (se 1 (by rfl) ⟨12555293, by rfl⟩ : syracuseStep 16740391 = 25110587) B25110587
theorem B389303 : Blo 255820 389303 := bstep (se 1 (by rfl) ⟨291977, by rfl⟩ : syracuseStep 389303 = 583955) B583955
theorem B291055 : Blo 255820 291055 := bstep (se 1 (by rfl) ⟨218291, by rfl⟩ : syracuseStep 291055 = 436583) B436583
theorem B14217551 : Blo 255820 14217551 := bstep (se 1 (by rfl) ⟨10663163, by rfl⟩ : syracuseStep 14217551 = 21326327) B21326327
theorem B259175 : Blo 255820 259175 := bstep (se 1 (by rfl) ⟨194381, by rfl⟩ : syracuseStep 259175 = 388763) B388763
theorem B652495 : Blo 255820 652495 := bstep (se 1 (by rfl) ⟨489371, by rfl⟩ : syracuseStep 652495 = 978743) B978743
theorem B554473 : Blo 255820 554473 := bstep (se 2 (by rfl) ⟨207927, by rfl⟩ : syracuseStep 554473 = 415855) B415855
theorem B259611 : Blo 255820 259611 := bstep (se 1 (by rfl) ⟨194708, by rfl⟩ : syracuseStep 259611 = 389417) B389417
theorem B259775 : Blo 255820 259775 := bstep (se 1 (by rfl) ⟨194831, by rfl⟩ : syracuseStep 259775 = 389663) B389663
theorem B653791 : Blo 255820 653791 := bstep (se 1 (by rfl) ⟨490343, by rfl⟩ : syracuseStep 653791 = 980687) B980687
theorem B6716209 : Blo 255820 6716209 := bstep (se 2 (by rfl) ⟨2518578, by rfl⟩ : syracuseStep 6716209 = 5037157) B5037157
theorem B621803 : Blo 255820 621803 := bstep (se 1 (by rfl) ⟨466352, by rfl⟩ : syracuseStep 621803 = 932705) B932705
theorem B326911 : Blo 255820 326911 := bstep (se 1 (by rfl) ⟨245183, by rfl⟩ : syracuseStep 326911 = 490367) B490367
theorem B1310255 : Blo 255820 1310255 := bstep (se 1 (by rfl) ⟨982691, by rfl⟩ : syracuseStep 1310255 = 1965383) B1965383
theorem B1310903 : Blo 255820 1310903 := bstep (se 1 (by rfl) ⟨983177, by rfl⟩ : syracuseStep 1310903 = 1966355) B1966355
theorem B1573501 : Blo 255820 1573501 := bstep (se 3 (by rfl) ⟨295031, by rfl⟩ : syracuseStep 1573501 = 590063) B590063
theorem B983785 : Blo 255820 983785 := bstep (se 2 (by rfl) ⟨368919, by rfl⟩ : syracuseStep 983785 = 737839) B737839
theorem B394343 : Blo 255820 394343 := bstep (se 1 (by rfl) ⟨295757, by rfl⟩ : syracuseStep 394343 = 591515) B591515
theorem B1050947 : Blo 255820 1050947 := bstep (se 1 (by rfl) ⟨788210, by rfl⟩ : syracuseStep 1050947 = 1576421) B1576421
theorem B1477865 : Blo 255820 1477865 := bstep (se 2 (by rfl) ⟨554199, by rfl⟩ : syracuseStep 1477865 = 1108399) B1108399
theorem B1478047 : Blo 255820 1478047 := bstep (se 1 (by rfl) ⟨1108535, by rfl⟩ : syracuseStep 1478047 = 2217071) B2217071
theorem B1184651 : Blo 255820 1184651 := bstep (se 1 (by rfl) ⟨888488, by rfl⟩ : syracuseStep 1184651 = 1776977) B1776977
theorem B22320521 : Blo 255820 22320521 := bstep (se 2 (by rfl) ⟨8370195, by rfl⟩ : syracuseStep 22320521 = 16740391) B16740391
theorem B7476623 : Blo 255820 7476623 := bstep (se 1 (by rfl) ⟨5607467, by rfl⟩ : syracuseStep 7476623 = 11214935) B11214935
theorem B432607 : Blo 255820 432607 := bstep (se 1 (by rfl) ⟨324455, by rfl⟩ : syracuseStep 432607 = 648911) B648911
theorem B99359227 : Blo 255820 99359227 := bstep (se 1 (by rfl) ⟨74519420, by rfl⟩ : syracuseStep 99359227 = 149038841) B149038841
theorem B433579 : Blo 255820 433579 := bstep (se 1 (by rfl) ⟨325184, by rfl⟩ : syracuseStep 433579 = 650369) B650369
theorem B9478367 : Blo 255820 9478367 := bstep (se 1 (by rfl) ⟨7108775, by rfl⟩ : syracuseStep 9478367 = 14217551) B14217551
theorem B8954945 : Blo 255820 8954945 := bstep (se 2 (by rfl) ⟨3358104, by rfl⟩ : syracuseStep 8954945 = 6716209) B6716209
theorem B435881 : Blo 255820 435881 := bstep (se 2 (by rfl) ⟨163455, by rfl⟩ : syracuseStep 435881 = 326911) B326911
theorem B928351 : Blo 255820 928351 := bstep (se 1 (by rfl) ⟨696263, by rfl⟩ : syracuseStep 928351 = 1392527) B1392527
theorem B436927 : Blo 255820 436927 := bstep (se 1 (by rfl) ⟨327695, by rfl⟩ : syracuseStep 436927 = 655391) B655391
theorem B5254727 : Blo 255820 5254727 := bstep (se 1 (by rfl) ⟨3941045, by rfl⟩ : syracuseStep 5254727 = 7882091) B7882091
theorem B864539 : Blo 255820 864539 := bstep (se 1 (by rfl) ⟨648404, by rfl⟩ : syracuseStep 864539 = 1296809) B1296809
theorem B1946429 : Blo 255820 1946429 := bstep (se 3 (by rfl) ⟨364955, by rfl⟩ : syracuseStep 1946429 = 729911) B729911
theorem B2634767 : Blo 255820 2634767 := bstep (se 1 (by rfl) ⟨1976075, by rfl⟩ : syracuseStep 2634767 = 3952151) B3952151
theorem B4404617 : Blo 255820 4404617 := bstep (se 2 (by rfl) ⟨1651731, by rfl⟩ : syracuseStep 4404617 = 3303463) B3303463
theorem B10172569 : Blo 255820 10172569 := bstep (se 2 (by rfl) ⟨3814713, by rfl⟩ : syracuseStep 10172569 = 7629427) B7629427
theorem B866807 : Blo 255820 866807 := bstep (se 1 (by rfl) ⟨650105, by rfl⟩ : syracuseStep 866807 = 1300211) B1300211
theorem B2506697 : Blo 255820 2506697 := bstep (se 2 (by rfl) ⟨940011, by rfl⟩ : syracuseStep 2506697 = 1880023) B1880023
theorem B1458593 : Blo 255820 1458593 := bstep (se 2 (by rfl) ⟨546972, by rfl⟩ : syracuseStep 1458593 = 1093945) B1093945
theorem B312103 : Blo 255820 312103 := bstep (se 1 (by rfl) ⟨234077, by rfl⟩ : syracuseStep 312103 = 468155) B468155
theorem B2377067 : Blo 255820 2377067 := bstep (se 1 (by rfl) ⟨1782800, by rfl⟩ : syracuseStep 2377067 = 3565601) B3565601
theorem B3130751 : Blo 255820 3130751 := bstep (se 1 (by rfl) ⟨2348063, by rfl⟩ : syracuseStep 3130751 = 4696127) B4696127
theorem B869993 : Blo 255820 869993 := bstep (se 2 (by rfl) ⟨326247, by rfl⟩ : syracuseStep 869993 = 652495) B652495
theorem B739297 : Blo 255820 739297 := bstep (se 2 (by rfl) ⟨277236, by rfl⟩ : syracuseStep 739297 = 554473) B554473
theorem B1296647 : Blo 255820 1296647 := bstep (se 1 (by rfl) ⟨972485, by rfl⟩ : syracuseStep 1296647 = 1944971) B1944971
theorem B16730549 : Blo 255820 16730549 := bstep (se 5 (by rfl) ⟨784244, by rfl⟩ : syracuseStep 16730549 = 1568489) B1568489
theorem B1952747 : Blo 255820 1952747 := bstep (se 1 (by rfl) ⟨1464560, by rfl⟩ : syracuseStep 1952747 = 2929121) B2929121
theorem B576539 : Blo 255820 576539 := bstep (se 1 (by rfl) ⟨432404, by rfl⟩ : syracuseStep 576539 = 864809) B864809
theorem B1658141 : Blo 255820 1658141 := bstep (se 3 (by rfl) ⟨310901, by rfl⟩ : syracuseStep 1658141 = 621803) B621803
theorem B871721 : Blo 255820 871721 := bstep (se 2 (by rfl) ⟨326895, by rfl⟩ : syracuseStep 871721 = 653791) B653791
theorem B577043 : Blo 255820 577043 := bstep (se 1 (by rfl) ⟨432782, by rfl⟩ : syracuseStep 577043 = 865565) B865565
theorem B577727 : Blo 255820 577727 := bstep (se 1 (by rfl) ⟨433295, by rfl⟩ : syracuseStep 577727 = 866591) B866591
theorem B577799 : Blo 255820 577799 := bstep (se 1 (by rfl) ⟨433349, by rfl⟩ : syracuseStep 577799 = 866699) B866699
theorem B578015 : Blo 255820 578015 := bstep (se 1 (by rfl) ⟨433511, by rfl⟩ : syracuseStep 578015 = 867023) B867023
theorem B578537 : Blo 255820 578537 := bstep (se 2 (by rfl) ⟨216951, by rfl⟩ : syracuseStep 578537 = 433903) B433903
theorem B873503 : Blo 255820 873503 := bstep (se 1 (by rfl) ⟨655127, by rfl⟩ : syracuseStep 873503 = 1310255) B1310255
theorem B579023 : Blo 255820 579023 := bstep (se 1 (by rfl) ⟨434267, by rfl⟩ : syracuseStep 579023 = 868535) B868535
theorem B874259 : Blo 255820 874259 := bstep (se 1 (by rfl) ⟨655694, by rfl⟩ : syracuseStep 874259 = 1311389) B1311389
theorem B579527 : Blo 255820 579527 := bstep (se 1 (by rfl) ⟨434645, by rfl⟩ : syracuseStep 579527 = 869291) B869291
theorem B11950247 : Blo 255820 11950247 := bstep (se 1 (by rfl) ⟨8962685, by rfl⟩ : syracuseStep 11950247 = 17925371) B17925371
theorem B1104367 : Blo 255820 1104367 := bstep (se 1 (by rfl) ⟨828275, by rfl⟩ : syracuseStep 1104367 = 1656551) B1656551
theorem B973565 : Blo 255820 973565 := bstep (se 3 (by rfl) ⟨182543, by rfl⟩ : syracuseStep 973565 = 365087) B365087
theorem B383771 : Blo 255820 383771 := bstep (se 1 (by rfl) ⟨287828, by rfl⟩ : syracuseStep 383771 = 575657) B575657
theorem B384095 : Blo 255820 384095 := bstep (se 1 (by rfl) ⟨288071, by rfl⟩ : syracuseStep 384095 = 576143) B576143
theorem B384137 : Blo 255820 384137 := bstep (se 2 (by rfl) ⟨144051, by rfl⟩ : syracuseStep 384137 = 288103) B288103
theorem B384959 : Blo 255820 384959 := bstep (se 1 (by rfl) ⟨288719, by rfl⟩ : syracuseStep 384959 = 577439) B577439
theorem B386543 : Blo 255820 386543 := bstep (se 1 (by rfl) ⟨289907, by rfl⟩ : syracuseStep 386543 = 579815) B579815
theorem B976769 : Blo 255820 976769 := bstep (se 2 (by rfl) ⟨366288, by rfl⟩ : syracuseStep 976769 = 732577) B732577
theorem B976799 : Blo 255820 976799 := bstep (se 1 (by rfl) ⟨732599, by rfl⟩ : syracuseStep 976799 = 1465199) B1465199
theorem B583595 : Blo 255820 583595 := bstep (se 1 (by rfl) ⟨437696, by rfl⟩ : syracuseStep 583595 = 875393) B875393
theorem B288895 : Blo 255820 288895 := bstep (se 1 (by rfl) ⟨216671, by rfl⟩ : syracuseStep 288895 = 433343) B433343
theorem B192997505 : Blo 255820 192997505 := bstep (se 2 (by rfl) ⟨72374064, by rfl⟩ : syracuseStep 192997505 = 144748129) B144748129
theorem B4417739 : Blo 255820 4417739 := bstep (se 1 (by rfl) ⟨3313304, by rfl⟩ : syracuseStep 4417739 = 6626609) B6626609
theorem B256415 : Blo 255820 256415 := bstep (se 1 (by rfl) ⟨192311, by rfl⟩ : syracuseStep 256415 = 384623) B384623
theorem B1305233 : Blo 255820 1305233 := bstep (se 2 (by rfl) ⟨489462, by rfl⟩ : syracuseStep 1305233 = 978925) B978925
theorem B256679 : Blo 255820 256679 := bstep (se 1 (by rfl) ⟨192509, by rfl⟩ : syracuseStep 256679 = 385019) B385019
theorem B27224747 : Blo 255820 27224747 := bstep (se 1 (by rfl) ⟨20418560, by rfl⟩ : syracuseStep 27224747 = 40837121) B40837121
theorem B256743 : Blo 255820 256743 := bstep (se 1 (by rfl) ⟨192557, by rfl⟩ : syracuseStep 256743 = 385115) B385115
theorem B1370927 : Blo 255820 1370927 := bstep (se 1 (by rfl) ⟨1028195, by rfl⟩ : syracuseStep 1370927 = 2056391) B2056391
theorem B388031 : Blo 255820 388031 := bstep (se 1 (by rfl) ⟨291023, by rfl⟩ : syracuseStep 388031 = 582047) B582047
theorem B388073 : Blo 255820 388073 := bstep (se 2 (by rfl) ⟨145527, by rfl⟩ : syracuseStep 388073 = 291055) B291055
theorem B552167 : Blo 255820 552167 := bstep (se 1 (by rfl) ⟨414125, by rfl⟩ : syracuseStep 552167 = 828251) B828251
theorem B617959 : Blo 255820 617959 := bstep (se 1 (by rfl) ⟨463469, by rfl⟩ : syracuseStep 617959 = 926939) B926939
theorem B486911 : Blo 255820 486911 := bstep (se 1 (by rfl) ⟨365183, by rfl⟩ : syracuseStep 486911 = 730367) B730367
theorem B257703 : Blo 255820 257703 := bstep (se 1 (by rfl) ⟨193277, by rfl⟩ : syracuseStep 257703 = 386555) B386555
theorem B257767 : Blo 255820 257767 := bstep (se 1 (by rfl) ⟨193325, by rfl⟩ : syracuseStep 257767 = 386651) B386651
theorem B487451 : Blo 255820 487451 := bstep (se 1 (by rfl) ⟨365588, by rfl⟩ : syracuseStep 487451 = 731177) B731177
theorem B3273119 : Blo 255820 3273119 := bstep (se 1 (by rfl) ⟨2454839, by rfl⟩ : syracuseStep 3273119 = 4909679) B4909679
theorem B258651 : Blo 255820 258651 := bstep (se 1 (by rfl) ⟨193988, by rfl⟩ : syracuseStep 258651 = 387977) B387977
theorem B258799 : Blo 255820 258799 := bstep (se 1 (by rfl) ⟨194099, by rfl⟩ : syracuseStep 258799 = 388199) B388199
theorem B652171 : Blo 255820 652171 := bstep (se 1 (by rfl) ⟨489128, by rfl⟩ : syracuseStep 652171 = 978257) B978257
theorem B259099 : Blo 255820 259099 := bstep (se 1 (by rfl) ⟨194324, by rfl⟩ : syracuseStep 259099 = 388649) B388649
theorem B259163 : Blo 255820 259163 := bstep (se 1 (by rfl) ⟨194372, by rfl⟩ : syracuseStep 259163 = 388745) B388745
theorem B259295 : Blo 255820 259295 := bstep (se 1 (by rfl) ⟨194471, by rfl⟩ : syracuseStep 259295 = 388943) B388943
theorem B259535 : Blo 255820 259535 := bstep (se 1 (by rfl) ⟨194651, by rfl⟩ : syracuseStep 259535 = 389303) B389303
theorem B4159151 : Blo 255820 4159151 := bstep (se 1 (by rfl) ⟨3119363, by rfl⟩ : syracuseStep 4159151 = 6238727) B6238727
theorem B753391 : Blo 255820 753391 := bstep (se 1 (by rfl) ⟨565043, by rfl⟩ : syracuseStep 753391 = 1130087) B1130087
theorem B262895 : Blo 255820 262895 := bstep (se 1 (by rfl) ⟨197171, by rfl⟩ : syracuseStep 262895 = 394343) B394343
theorem B2098001 : Blo 255820 2098001 := bstep (se 2 (by rfl) ⟨786750, by rfl⟩ : syracuseStep 2098001 = 1573501) B1573501
theorem B1311713 : Blo 255820 1311713 := bstep (se 2 (by rfl) ⟨491892, by rfl⟩ : syracuseStep 1311713 = 983785) B983785
theorem B985243 : Blo 255820 985243 := bstep (se 1 (by rfl) ⟨738932, by rfl⟩ : syracuseStep 985243 = 1477865) B1477865
theorem B985729 : Blo 255820 985729 := bstep (se 2 (by rfl) ⟨369648, by rfl⟩ : syracuseStep 985729 = 739297) B739297
theorem B789767 : Blo 255820 789767 := bstep (se 1 (by rfl) ⟨592325, by rfl⟩ : syracuseStep 789767 = 1184651) B1184651
theorem B14880347 : Blo 255820 14880347 := bstep (se 1 (by rfl) ⟨11160260, by rfl⟩ : syracuseStep 14880347 = 22320521) B22320521
theorem B4984415 : Blo 255820 4984415 := bstep (se 1 (by rfl) ⟨3738311, by rfl⟩ : syracuseStep 4984415 = 7476623) B7476623
theorem B7966831 : Blo 255820 7966831 := bstep (se 1 (by rfl) ⟨5975123, by rfl⟩ : syracuseStep 7966831 = 11950247) B11950247
theorem B1970729 : Blo 255820 1970729 := bstep (se 2 (by rfl) ⟨739023, by rfl⟩ : syracuseStep 1970729 = 1478047) B1478047
theorem B823945 : Blo 255820 823945 := bstep (se 2 (by rfl) ⟨308979, by rfl⟩ : syracuseStep 823945 = 617959) B617959
theorem B514660013 : Blo 255820 514660013 := bstep (se 3 (by rfl) ⟨96498752, by rfl⟩ : syracuseStep 514660013 = 192997505) B192997505
theorem B5969963 : Blo 255820 5969963 := bstep (se 1 (by rfl) ⟨4477472, by rfl⟩ : syracuseStep 5969963 = 8954945) B8954945
theorem B368111 : Blo 255820 368111 := bstep (se 1 (by rfl) ⟨276083, by rfl⟩ : syracuseStep 368111 = 552167) B552167
theorem B864431 : Blo 255820 864431 := bstep (se 1 (by rfl) ⟨648323, by rfl⟩ : syracuseStep 864431 = 1296647) B1296647
theorem B700631 : Blo 255820 700631 := bstep (se 1 (by rfl) ⟨525473, by rfl⟩ : syracuseStep 700631 = 1050947) B1050947
theorem B11153699 : Blo 255820 11153699 := bstep (se 1 (by rfl) ⟨8365274, by rfl⟩ : syracuseStep 11153699 = 16730549) B16730549
theorem B6338845 : Blo 255820 6338845 := bstep (se 3 (by rfl) ⟨1188533, by rfl⟩ : syracuseStep 6338845 = 2377067) B2377067
theorem B869561 : Blo 255820 869561 := bstep (se 2 (by rfl) ⟨326085, by rfl⟩ : syracuseStep 869561 = 652171) B652171
theorem B870155 : Blo 255820 870155 := bstep (se 1 (by rfl) ⟨652616, by rfl⟩ : syracuseStep 870155 = 1305233) B1305233
theorem B576359 : Blo 255820 576359 := bstep (se 1 (by rfl) ⟨432269, by rfl⟩ : syracuseStep 576359 = 864539) B864539
theorem B2182079 : Blo 255820 2182079 := bstep (se 1 (by rfl) ⟨1636559, by rfl⟩ : syracuseStep 2182079 = 3273119) B3273119
theorem B1297619 : Blo 255820 1297619 := bstep (se 1 (by rfl) ⟨973214, by rfl⟩ : syracuseStep 1297619 = 1946429) B1946429
theorem B576809 : Blo 255820 576809 := bstep (se 2 (by rfl) ⟨216303, by rfl⟩ : syracuseStep 576809 = 432607) B432607
theorem B1756511 : Blo 255820 1756511 := bstep (se 1 (by rfl) ⟨1317383, by rfl⟩ : syracuseStep 1756511 = 2634767) B2634767
theorem B2936411 : Blo 255820 2936411 := bstep (se 1 (by rfl) ⟨2202308, by rfl⟩ : syracuseStep 2936411 = 4404617) B4404617
theorem B2772767 : Blo 255820 2772767 := bstep (se 1 (by rfl) ⟨2079575, by rfl⟩ : syracuseStep 2772767 = 4159151) B4159151
theorem B1298429 : Blo 255820 1298429 := bstep (se 3 (by rfl) ⟨243455, by rfl⟩ : syracuseStep 1298429 = 486911) B486911
theorem B14012605 : Blo 255820 14012605 := bstep (se 3 (by rfl) ⟨2627363, by rfl⟩ : syracuseStep 14012605 = 5254727) B5254727
theorem B577871 : Blo 255820 577871 := bstep (se 1 (by rfl) ⟨433403, by rfl⟩ : syracuseStep 577871 = 866807) B866807
theorem B578105 : Blo 255820 578105 := bstep (se 2 (by rfl) ⟨216789, by rfl⟩ : syracuseStep 578105 = 433579) B433579
theorem B1004521 : Blo 255820 1004521 := bstep (se 2 (by rfl) ⟨376695, by rfl⟩ : syracuseStep 1004521 = 753391) B753391
theorem B873935 : Blo 255820 873935 := bstep (se 1 (by rfl) ⟨655451, by rfl⟩ : syracuseStep 873935 = 1310903) B1310903
theorem B972395 : Blo 255820 972395 := bstep (se 1 (by rfl) ⟨729296, by rfl⟩ : syracuseStep 972395 = 1458593) B1458593
theorem B579995 : Blo 255820 579995 := bstep (se 1 (by rfl) ⟨434996, by rfl⟩ : syracuseStep 579995 = 869993) B869993
theorem B1301831 : Blo 255820 1301831 := bstep (se 1 (by rfl) ⟨976373, by rfl⟩ : syracuseStep 1301831 = 1952747) B1952747
theorem B384359 : Blo 255820 384359 := bstep (se 1 (by rfl) ⟨288269, by rfl⟩ : syracuseStep 384359 = 576539) B576539
theorem B1105427 : Blo 255820 1105427 := bstep (se 1 (by rfl) ⟨829070, by rfl⟩ : syracuseStep 1105427 = 1658141) B1658141
theorem B581147 : Blo 255820 581147 := bstep (se 1 (by rfl) ⟨435860, by rfl⟩ : syracuseStep 581147 = 871721) B871721
theorem B384695 : Blo 255820 384695 := bstep (se 1 (by rfl) ⟨288521, by rfl⟩ : syracuseStep 384695 = 577043) B577043
theorem B529915877 : Blo 255820 529915877 := bstep (se 4 (by rfl) ⟨49679613, by rfl⟩ : syracuseStep 529915877 = 99359227) B99359227
theorem B385151 : Blo 255820 385151 := bstep (se 1 (by rfl) ⟨288863, by rfl⟩ : syracuseStep 385151 = 577727) B577727
theorem B385193 : Blo 255820 385193 := bstep (se 2 (by rfl) ⟨144447, by rfl⟩ : syracuseStep 385193 = 288895) B288895
theorem B385199 : Blo 255820 385199 := bstep (se 1 (by rfl) ⟨288899, by rfl⟩ : syracuseStep 385199 = 577799) B577799
theorem B385343 : Blo 255820 385343 := bstep (se 1 (by rfl) ⟨289007, by rfl⟩ : syracuseStep 385343 = 578015) B578015
theorem B385691 : Blo 255820 385691 := bstep (se 1 (by rfl) ⟨289268, by rfl⟩ : syracuseStep 385691 = 578537) B578537
theorem B582335 : Blo 255820 582335 := bstep (se 1 (by rfl) ⟨436751, by rfl⟩ : syracuseStep 582335 = 873503) B873503
theorem B1237801 : Blo 255820 1237801 := bstep (se 2 (by rfl) ⟨464175, by rfl⟩ : syracuseStep 1237801 = 928351) B928351
theorem B582569 : Blo 255820 582569 := bstep (se 2 (by rfl) ⟨218463, by rfl⟩ : syracuseStep 582569 = 436927) B436927
theorem B386015 : Blo 255820 386015 := bstep (se 1 (by rfl) ⟨289511, by rfl⟩ : syracuseStep 386015 = 579023) B579023
theorem B8348669 : Blo 255820 8348669 := bstep (se 3 (by rfl) ⟨1565375, by rfl⟩ : syracuseStep 8348669 = 3130751) B3130751
theorem B582839 : Blo 255820 582839 := bstep (se 1 (by rfl) ⟨437129, by rfl⟩ : syracuseStep 582839 = 874259) B874259
theorem B386351 : Blo 255820 386351 := bstep (se 1 (by rfl) ⟨289763, by rfl⟩ : syracuseStep 386351 = 579527) B579527
theorem B1664549 : Blo 255820 1664549 := bstep (se 4 (by rfl) ⟨156051, by rfl⟩ : syracuseStep 1664549 = 312103) B312103
theorem B649043 : Blo 255820 649043 := bstep (se 1 (by rfl) ⟨486782, by rfl⟩ : syracuseStep 649043 = 973565) B973565
theorem B255847 : Blo 255820 255847 := bstep (se 1 (by rfl) ⟨191885, by rfl⟩ : syracuseStep 255847 = 383771) B383771
theorem B256063 : Blo 255820 256063 := bstep (se 1 (by rfl) ⟨192047, by rfl⟩ : syracuseStep 256063 = 384095) B384095
theorem B256091 : Blo 255820 256091 := bstep (se 1 (by rfl) ⟨192068, by rfl⟩ : syracuseStep 256091 = 384137) B384137
theorem B256639 : Blo 255820 256639 := bstep (se 1 (by rfl) ⟨192479, by rfl⟩ : syracuseStep 256639 = 384959) B384959
theorem B6318911 : Blo 255820 6318911 := bstep (se 1 (by rfl) ⟨4739183, by rfl⟩ : syracuseStep 6318911 = 9478367) B9478367
theorem B257695 : Blo 255820 257695 := bstep (se 1 (by rfl) ⟨193271, by rfl⟩ : syracuseStep 257695 = 386543) B386543
theorem B290587 : Blo 255820 290587 := bstep (se 1 (by rfl) ⟨217940, by rfl⟩ : syracuseStep 290587 = 435881) B435881
theorem B651179 : Blo 255820 651179 := bstep (se 1 (by rfl) ⟨488384, by rfl⟩ : syracuseStep 651179 = 976769) B976769
theorem B651199 : Blo 255820 651199 := bstep (se 1 (by rfl) ⟨488399, by rfl⟩ : syracuseStep 651199 = 976799) B976799
theorem B389063 : Blo 255820 389063 := bstep (se 1 (by rfl) ⟨291797, by rfl⟩ : syracuseStep 389063 = 583595) B583595
theorem B2945159 : Blo 255820 2945159 := bstep (se 1 (by rfl) ⟨2208869, by rfl⟩ : syracuseStep 2945159 = 4417739) B4417739
theorem B18149831 : Blo 255820 18149831 := bstep (se 1 (by rfl) ⟨13612373, by rfl⟩ : syracuseStep 18149831 = 27224747) B27224747
theorem B913951 : Blo 255820 913951 := bstep (se 1 (by rfl) ⟨685463, by rfl⟩ : syracuseStep 913951 = 1370927) B1370927
theorem B258687 : Blo 255820 258687 := bstep (se 1 (by rfl) ⟨194015, by rfl⟩ : syracuseStep 258687 = 388031) B388031
theorem B258715 : Blo 255820 258715 := bstep (se 1 (by rfl) ⟨194036, by rfl⟩ : syracuseStep 258715 = 388073) B388073
theorem B324967 : Blo 255820 324967 := bstep (se 1 (by rfl) ⟨243725, by rfl⟩ : syracuseStep 324967 = 487451) B487451
theorem B13563425 : Blo 255820 13563425 := bstep (se 2 (by rfl) ⟨5086284, by rfl⟩ : syracuseStep 13563425 = 10172569) B10172569
theorem B1472489 : Blo 255820 1472489 := bstep (se 2 (by rfl) ⟨552183, by rfl⟩ : syracuseStep 1472489 = 1104367) B1104367
theorem B1671131 : Blo 255820 1671131 := bstep (se 1 (by rfl) ⟨1253348, by rfl⟩ : syracuseStep 1671131 = 2506697) B2506697
theorem B526511 : Blo 255820 526511 := bstep (se 1 (by rfl) ⟨394883, by rfl⟩ : syracuseStep 526511 = 789767) B789767
theorem B1313657 : Blo 255820 1313657 := bstep (se 2 (by rfl) ⟨492621, by rfl⟩ : syracuseStep 1313657 = 985243) B985243
theorem B1313819 : Blo 255820 1313819 := bstep (se 1 (by rfl) ⟨985364, by rfl⟩ : syracuseStep 1313819 = 1970729) B1970729
theorem B1314305 : Blo 255820 1314305 := bstep (se 2 (by rfl) ⟨492864, by rfl⟩ : syracuseStep 1314305 = 985729) B985729
theorem B353277251 : Blo 255820 353277251 := bstep (se 1 (by rfl) ⟨264957938, by rfl⟩ : syracuseStep 353277251 = 529915877) B529915877
theorem B10622441 : Blo 255820 10622441 := bstep (se 2 (by rfl) ⟨3983415, by rfl⟩ : syracuseStep 10622441 = 7966831) B7966831
theorem B18683473 : Blo 255820 18683473 := bstep (se 2 (by rfl) ⟨7006302, by rfl⟩ : syracuseStep 18683473 = 14012605) B14012605
theorem B1218601 : Blo 255820 1218601 := bstep (se 2 (by rfl) ⟨456975, by rfl⟩ : syracuseStep 1218601 = 913951) B913951
theorem B432695 : Blo 255820 432695 := bstep (se 1 (by rfl) ⟨324521, by rfl⟩ : syracuseStep 432695 = 649043) B649043
theorem B433289 : Blo 255820 433289 := bstep (se 2 (by rfl) ⟨162483, by rfl⟩ : syracuseStep 433289 = 324967) B324967
theorem B434119 : Blo 255820 434119 := bstep (se 1 (by rfl) ⟨325589, by rfl⟩ : syracuseStep 434119 = 651179) B651179
theorem B467087 : Blo 255820 467087 := bstep (se 1 (by rfl) ⟨350315, by rfl⟩ : syracuseStep 467087 = 700631) B700631
theorem B12099887 : Blo 255820 12099887 := bstep (se 1 (by rfl) ⟨9074915, by rfl⟩ : syracuseStep 12099887 = 18149831) B18149831
theorem B1650401 : Blo 255820 1650401 := bstep (se 2 (by rfl) ⟨618900, by rfl⟩ : syracuseStep 1650401 = 1237801) B1237801
theorem B865079 : Blo 255820 865079 := bstep (se 1 (by rfl) ⟨648809, by rfl⟩ : syracuseStep 865079 = 1297619) B1297619
theorem B3322943 : Blo 255820 3322943 := bstep (se 1 (by rfl) ⟨2492207, by rfl⟩ : syracuseStep 3322943 = 4984415) B4984415
theorem B1848511 : Blo 255820 1848511 := bstep (se 1 (by rfl) ⟨1386383, by rfl⟩ : syracuseStep 1848511 = 2772767) B2772767
theorem B865619 : Blo 255820 865619 := bstep (se 1 (by rfl) ⟨649214, by rfl⟩ : syracuseStep 865619 = 1298429) B1298429
theorem B3979975 : Blo 255820 3979975 := bstep (se 1 (by rfl) ⟨2984981, by rfl⟩ : syracuseStep 3979975 = 5969963) B5969963
theorem B867887 : Blo 255820 867887 := bstep (se 1 (by rfl) ⟨650915, by rfl⟩ : syracuseStep 867887 = 1301831) B1301831
theorem B736951 : Blo 255820 736951 := bstep (se 1 (by rfl) ⟨552713, by rfl⟩ : syracuseStep 736951 = 1105427) B1105427
theorem B868265 : Blo 255820 868265 := bstep (se 2 (by rfl) ⟨325599, by rfl⟩ : syracuseStep 868265 = 651199) B651199
theorem B1098593 : Blo 255820 1098593 := bstep (se 2 (by rfl) ⟨411972, by rfl⟩ : syracuseStep 1098593 = 823945) B823945
theorem B4212607 : Blo 255820 4212607 := bstep (se 1 (by rfl) ⟨3159455, by rfl⟩ : syracuseStep 4212607 = 6318911) B6318911
theorem B2804213 : Blo 255820 2804213 := bstep (se 5 (by rfl) ⟨131447, by rfl⟩ : syracuseStep 2804213 = 262895) B262895
theorem B5818877 : Blo 255820 5818877 := bstep (se 3 (by rfl) ⟨1091039, by rfl⟩ : syracuseStep 5818877 = 2182079) B2182079
theorem B576287 : Blo 255820 576287 := bstep (se 1 (by rfl) ⟨432215, by rfl⟩ : syracuseStep 576287 = 864431) B864431
theorem B1398667 : Blo 255820 1398667 := bstep (se 1 (by rfl) ⟨1049000, by rfl⟩ : syracuseStep 1398667 = 2098001) B2098001
theorem B874475 : Blo 255820 874475 := bstep (se 1 (by rfl) ⟨655856, by rfl⟩ : syracuseStep 874475 = 1311713) B1311713
theorem B579707 : Blo 255820 579707 := bstep (se 1 (by rfl) ⟨434780, by rfl⟩ : syracuseStep 579707 = 869561) B869561
theorem B580103 : Blo 255820 580103 := bstep (se 1 (by rfl) ⟨435077, by rfl⟩ : syracuseStep 580103 = 870155) B870155
theorem B384239 : Blo 255820 384239 := bstep (se 1 (by rfl) ⟨288179, by rfl⟩ : syracuseStep 384239 = 576359) B576359
theorem B384539 : Blo 255820 384539 := bstep (se 1 (by rfl) ⟨288404, by rfl⟩ : syracuseStep 384539 = 576809) B576809
theorem B1171007 : Blo 255820 1171007 := bstep (se 1 (by rfl) ⟨878255, by rfl⟩ : syracuseStep 1171007 = 1756511) B1756511
theorem B1957607 : Blo 255820 1957607 := bstep (se 1 (by rfl) ⟨1468205, by rfl⟩ : syracuseStep 1957607 = 2936411) B2936411
theorem B9920231 : Blo 255820 9920231 := bstep (se 1 (by rfl) ⟨7440173, by rfl⟩ : syracuseStep 9920231 = 14880347) B14880347
theorem B385247 : Blo 255820 385247 := bstep (se 1 (by rfl) ⟨288935, by rfl⟩ : syracuseStep 385247 = 577871) B577871
theorem B385403 : Blo 255820 385403 := bstep (se 1 (by rfl) ⟨289052, by rfl⟩ : syracuseStep 385403 = 578105) B578105
theorem B582623 : Blo 255820 582623 := bstep (se 1 (by rfl) ⟨436967, by rfl⟩ : syracuseStep 582623 = 873935) B873935
theorem B648263 : Blo 255820 648263 := bstep (se 1 (by rfl) ⟨486197, by rfl⟩ : syracuseStep 648263 = 972395) B972395
theorem B343106675 : Blo 255820 343106675 := bstep (se 1 (by rfl) ⟨257330006, by rfl⟩ : syracuseStep 343106675 = 514660013) B514660013
theorem B386663 : Blo 255820 386663 := bstep (se 1 (by rfl) ⟨289997, by rfl⟩ : syracuseStep 386663 = 579995) B579995
theorem B256239 : Blo 255820 256239 := bstep (se 1 (by rfl) ⟨192179, by rfl⟩ : syracuseStep 256239 = 384359) B384359
theorem B387431 : Blo 255820 387431 := bstep (se 1 (by rfl) ⟨290573, by rfl⟩ : syracuseStep 387431 = 581147) B581147
theorem B387449 : Blo 255820 387449 := bstep (se 2 (by rfl) ⟨145293, by rfl⟩ : syracuseStep 387449 = 290587) B290587
theorem B256463 : Blo 255820 256463 := bstep (se 1 (by rfl) ⟨192347, by rfl⟩ : syracuseStep 256463 = 384695) B384695
theorem B256767 : Blo 255820 256767 := bstep (se 1 (by rfl) ⟨192575, by rfl⟩ : syracuseStep 256767 = 385151) B385151
theorem B256795 : Blo 255820 256795 := bstep (se 1 (by rfl) ⟨192596, by rfl⟩ : syracuseStep 256795 = 385193) B385193
theorem B256799 : Blo 255820 256799 := bstep (se 1 (by rfl) ⟨192599, by rfl⟩ : syracuseStep 256799 = 385199) B385199
theorem B256895 : Blo 255820 256895 := bstep (se 1 (by rfl) ⟨192671, by rfl⟩ : syracuseStep 256895 = 385343) B385343
theorem B257127 : Blo 255820 257127 := bstep (se 1 (by rfl) ⟨192845, by rfl⟩ : syracuseStep 257127 = 385691) B385691
theorem B388223 : Blo 255820 388223 := bstep (se 1 (by rfl) ⟨291167, by rfl⟩ : syracuseStep 388223 = 582335) B582335
theorem B388379 : Blo 255820 388379 := bstep (se 1 (by rfl) ⟨291284, by rfl⟩ : syracuseStep 388379 = 582569) B582569
theorem B257343 : Blo 255820 257343 := bstep (se 1 (by rfl) ⟨193007, by rfl⟩ : syracuseStep 257343 = 386015) B386015
theorem B5565779 : Blo 255820 5565779 := bstep (se 1 (by rfl) ⟨4174334, by rfl⟩ : syracuseStep 5565779 = 8348669) B8348669
theorem B388559 : Blo 255820 388559 := bstep (se 1 (by rfl) ⟨291419, by rfl⟩ : syracuseStep 388559 = 582839) B582839
theorem B257567 : Blo 255820 257567 := bstep (se 1 (by rfl) ⟨193175, by rfl⟩ : syracuseStep 257567 = 386351) B386351
theorem B1109699 : Blo 255820 1109699 := bstep (se 1 (by rfl) ⟨832274, by rfl⟩ : syracuseStep 1109699 = 1664549) B1664549
theorem B1339361 : Blo 255820 1339361 := bstep (se 2 (by rfl) ⟨502260, by rfl⟩ : syracuseStep 1339361 = 1004521) B1004521
theorem B259375 : Blo 255820 259375 := bstep (se 1 (by rfl) ⟨194531, by rfl⟩ : syracuseStep 259375 = 389063) B389063
theorem B1963439 : Blo 255820 1963439 := bstep (se 1 (by rfl) ⟨1472579, by rfl⟩ : syracuseStep 1963439 = 2945159) B2945159
theorem B7435799 : Blo 255820 7435799 := bstep (se 1 (by rfl) ⟨5576849, by rfl⟩ : syracuseStep 7435799 = 11153699) B11153699
theorem B8451793 : Blo 255820 8451793 := bstep (se 2 (by rfl) ⟨3169422, by rfl⟩ : syracuseStep 8451793 = 6338845) B6338845
theorem B9042283 : Blo 255820 9042283 := bstep (se 1 (by rfl) ⟨6781712, by rfl⟩ : syracuseStep 9042283 = 13563425) B13563425
theorem B981629 : Blo 255820 981629 := bstep (se 3 (by rfl) ⟨184055, by rfl⟩ : syracuseStep 981629 = 368111) B368111
theorem B981659 : Blo 255820 981659 := bstep (se 1 (by rfl) ⟨736244, by rfl⟩ : syracuseStep 981659 = 1472489) B1472489
theorem B1114087 : Blo 255820 1114087 := bstep (se 1 (by rfl) ⟨835565, by rfl⟩ : syracuseStep 1114087 = 1671131) B1671131
theorem B1245565 : Blo 255820 1245565 := bstep (se 3 (by rfl) ⟨233543, by rfl⟩ : syracuseStep 1245565 = 467087) B467087
theorem B1869475 : Blo 255820 1869475 := bstep (se 1 (by rfl) ⟨1402106, by rfl⟩ : syracuseStep 1869475 = 2804213) B2804213
theorem B7081627 : Blo 255820 7081627 := bstep (se 1 (by rfl) ⟨5311220, by rfl⟩ : syracuseStep 7081627 = 10622441) B10622441
theorem B8066591 : Blo 255820 8066591 := bstep (se 1 (by rfl) ⟨6049943, by rfl⟩ : syracuseStep 8066591 = 12099887) B12099887
theorem B432175 : Blo 255820 432175 := bstep (se 1 (by rfl) ⟨324131, by rfl⟩ : syracuseStep 432175 = 648263) B648263
theorem B2464681 : Blo 255820 2464681 := bstep (se 2 (by rfl) ⟨924255, by rfl⟩ : syracuseStep 2464681 = 1848511) B1848511
theorem B24911297 : Blo 255820 24911297 := bstep (se 2 (by rfl) ⟨9341736, by rfl⟩ : syracuseStep 24911297 = 18683473) B18683473
theorem B3710519 : Blo 255820 3710519 := bstep (se 1 (by rfl) ⟨2782889, by rfl⟩ : syracuseStep 3710519 = 5565779) B5565779
theorem B892907 : Blo 255820 892907 := bstep (se 1 (by rfl) ⟨669680, by rfl⟩ : syracuseStep 892907 = 1339361) B1339361
theorem B4957199 : Blo 255820 4957199 := bstep (se 1 (by rfl) ⟨3717899, by rfl⟩ : syracuseStep 4957199 = 7435799) B7435799
theorem B1485449 : Blo 255820 1485449 := bstep (se 2 (by rfl) ⟨557043, by rfl⟩ : syracuseStep 1485449 = 1114087) B1114087
theorem B732395 : Blo 255820 732395 := bstep (se 1 (by rfl) ⟨549296, by rfl⟩ : syracuseStep 732395 = 1098593) B1098593
theorem B3879251 : Blo 255820 3879251 := bstep (se 1 (by rfl) ⟨2909438, by rfl⟩ : syracuseStep 3879251 = 5818877) B5818877
theorem B5616809 : Blo 255820 5616809 := bstep (se 2 (by rfl) ⟨2106303, by rfl⟩ : syracuseStep 5616809 = 4212607) B4212607
theorem B235518167 : Blo 255820 235518167 := bstep (se 1 (by rfl) ⟨176638625, by rfl⟩ : syracuseStep 235518167 = 353277251) B353277251
theorem B228737783 : Blo 255820 228737783 := bstep (se 1 (by rfl) ⟨171553337, by rfl⟩ : syracuseStep 228737783 = 343106675) B343106675
theorem B739799 : Blo 255820 739799 := bstep (se 1 (by rfl) ⟨554849, by rfl⟩ : syracuseStep 739799 = 1109699) B1109699
theorem B1100267 : Blo 255820 1100267 := bstep (se 1 (by rfl) ⟨825200, by rfl⟩ : syracuseStep 1100267 = 1650401) B1650401
theorem B1624801 : Blo 255820 1624801 := bstep (se 2 (by rfl) ⟨609300, by rfl⟩ : syracuseStep 1624801 = 1218601) B1218601
theorem B576719 : Blo 255820 576719 := bstep (se 1 (by rfl) ⟨432539, by rfl⟩ : syracuseStep 576719 = 865079) B865079
theorem B2215295 : Blo 255820 2215295 := bstep (se 1 (by rfl) ⟨1661471, by rfl⟩ : syracuseStep 2215295 = 3322943) B3322943
theorem B577079 : Blo 255820 577079 := bstep (se 1 (by rfl) ⟨432809, by rfl⟩ : syracuseStep 577079 = 865619) B865619
theorem B578591 : Blo 255820 578591 := bstep (se 1 (by rfl) ⟨433943, by rfl⟩ : syracuseStep 578591 = 867887) B867887
theorem B578825 : Blo 255820 578825 := bstep (se 2 (by rfl) ⟨217059, by rfl⟩ : syracuseStep 578825 = 434119) B434119
theorem B578843 : Blo 255820 578843 := bstep (se 1 (by rfl) ⟨434132, by rfl⟩ : syracuseStep 578843 = 868265) B868265
theorem B384191 : Blo 255820 384191 := bstep (se 1 (by rfl) ⟨288143, by rfl⟩ : syracuseStep 384191 = 576287) B576287
theorem B875771 : Blo 255820 875771 := bstep (se 1 (by rfl) ⟨656828, by rfl⟩ : syracuseStep 875771 = 1313657) B1313657
theorem B875879 : Blo 255820 875879 := bstep (se 1 (by rfl) ⟨656909, by rfl⟩ : syracuseStep 875879 = 1313819) B1313819
theorem B876203 : Blo 255820 876203 := bstep (se 1 (by rfl) ⟨657152, by rfl⟩ : syracuseStep 876203 = 1314305) B1314305
theorem B582983 : Blo 255820 582983 := bstep (se 1 (by rfl) ⟨437237, by rfl⟩ : syracuseStep 582983 = 874475) B874475
theorem B386471 : Blo 255820 386471 := bstep (se 1 (by rfl) ⟨289853, by rfl⟩ : syracuseStep 386471 = 579707) B579707
theorem B386735 : Blo 255820 386735 := bstep (se 1 (by rfl) ⟨290051, by rfl⟩ : syracuseStep 386735 = 580103) B580103
theorem B288463 : Blo 255820 288463 := bstep (se 1 (by rfl) ⟨216347, by rfl⟩ : syracuseStep 288463 = 432695) B432695
theorem B288859 : Blo 255820 288859 := bstep (se 1 (by rfl) ⟨216644, by rfl⟩ : syracuseStep 288859 = 433289) B433289
theorem B256159 : Blo 255820 256159 := bstep (se 1 (by rfl) ⟨192119, by rfl⟩ : syracuseStep 256159 = 384239) B384239
theorem B256359 : Blo 255820 256359 := bstep (se 1 (by rfl) ⟨192269, by rfl⟩ : syracuseStep 256359 = 384539) B384539
theorem B780671 : Blo 255820 780671 := bstep (se 1 (by rfl) ⟨585503, by rfl⟩ : syracuseStep 780671 = 1171007) B1171007
theorem B1305071 : Blo 255820 1305071 := bstep (se 1 (by rfl) ⟨978803, by rfl⟩ : syracuseStep 1305071 = 1957607) B1957607
theorem B6613487 : Blo 255820 6613487 := bstep (se 1 (by rfl) ⟨4960115, by rfl⟩ : syracuseStep 6613487 = 9920231) B9920231
theorem B256831 : Blo 255820 256831 := bstep (se 1 (by rfl) ⟨192623, by rfl⟩ : syracuseStep 256831 = 385247) B385247
theorem B256935 : Blo 255820 256935 := bstep (se 1 (by rfl) ⟨192701, by rfl⟩ : syracuseStep 256935 = 385403) B385403
theorem B1404029 : Blo 255820 1404029 := bstep (se 3 (by rfl) ⟨263255, by rfl⟩ : syracuseStep 1404029 = 526511) B526511
theorem B388415 : Blo 255820 388415 := bstep (se 1 (by rfl) ⟨291311, by rfl⟩ : syracuseStep 388415 = 582623) B582623
theorem B257775 : Blo 255820 257775 := bstep (se 1 (by rfl) ⟨193331, by rfl⟩ : syracuseStep 257775 = 386663) B386663
theorem B258287 : Blo 255820 258287 := bstep (se 1 (by rfl) ⟨193715, by rfl⟩ : syracuseStep 258287 = 387431) B387431
theorem B258299 : Blo 255820 258299 := bstep (se 1 (by rfl) ⟨193724, by rfl⟩ : syracuseStep 258299 = 387449) B387449
theorem B258815 : Blo 255820 258815 := bstep (se 1 (by rfl) ⟨194111, by rfl⟩ : syracuseStep 258815 = 388223) B388223
theorem B258919 : Blo 255820 258919 := bstep (se 1 (by rfl) ⟨194189, by rfl⟩ : syracuseStep 258919 = 388379) B388379
theorem B11269057 : Blo 255820 11269057 := bstep (se 2 (by rfl) ⟨4225896, by rfl⟩ : syracuseStep 11269057 = 8451793) B8451793
theorem B259039 : Blo 255820 259039 := bstep (se 1 (by rfl) ⟨194279, by rfl⟩ : syracuseStep 259039 = 388559) B388559
theorem B1864889 : Blo 255820 1864889 := bstep (se 2 (by rfl) ⟨699333, by rfl⟩ : syracuseStep 1864889 = 1398667) B1398667
theorem B12056377 : Blo 255820 12056377 := bstep (se 2 (by rfl) ⟨4521141, by rfl⟩ : syracuseStep 12056377 = 9042283) B9042283
theorem B5306633 : Blo 255820 5306633 := bstep (se 2 (by rfl) ⟨1989987, by rfl⟩ : syracuseStep 5306633 = 3979975) B3979975
theorem B1308959 : Blo 255820 1308959 := bstep (se 1 (by rfl) ⟨981719, by rfl⟩ : syracuseStep 1308959 = 1963439) B1963439
theorem B654419 : Blo 255820 654419 := bstep (se 1 (by rfl) ⟨490814, by rfl⟩ : syracuseStep 654419 = 981629) B981629
theorem B654439 : Blo 255820 654439 := bstep (se 1 (by rfl) ⟨490829, by rfl⟩ : syracuseStep 654439 = 981659) B981659
theorem B982601 : Blo 255820 982601 := bstep (se 2 (by rfl) ⟨368475, by rfl⟩ : syracuseStep 982601 = 736951) B736951
theorem B493199 : Blo 255820 493199 := bstep (se 1 (by rfl) ⟨369899, by rfl⟩ : syracuseStep 493199 = 739799) B739799
theorem B2492633 : Blo 255820 2492633 := bstep (se 2 (by rfl) ⟨934737, by rfl⟩ : syracuseStep 2492633 = 1869475) B1869475
theorem B1476863 : Blo 255820 1476863 := bstep (se 1 (by rfl) ⟨1107647, by rfl⟩ : syracuseStep 1476863 = 2215295) B2215295
theorem B2166401 : Blo 255820 2166401 := bstep (se 2 (by rfl) ⟨812400, by rfl⟩ : syracuseStep 2166401 = 1624801) B1624801
theorem B5377727 : Blo 255820 5377727 := bstep (se 1 (by rfl) ⟨4033295, by rfl⟩ : syracuseStep 5377727 = 8066591) B8066591
theorem B9442169 : Blo 255820 9442169 := bstep (se 2 (by rfl) ⟨3540813, by rfl⟩ : syracuseStep 9442169 = 7081627) B7081627
theorem B595271 : Blo 255820 595271 := bstep (se 1 (by rfl) ⟨446453, by rfl⟩ : syracuseStep 595271 = 892907) B892907
theorem B990299 : Blo 255820 990299 := bstep (se 1 (by rfl) ⟨742724, by rfl⟩ : syracuseStep 990299 = 1485449) B1485449
theorem B3744539 : Blo 255820 3744539 := bstep (se 1 (by rfl) ⟨2808404, by rfl⟩ : syracuseStep 3744539 = 5616809) B5616809
theorem B3286241 : Blo 255820 3286241 := bstep (se 2 (by rfl) ⟨1232340, by rfl⟩ : syracuseStep 3286241 = 2464681) B2464681
theorem B436279 : Blo 255820 436279 := bstep (se 1 (by rfl) ⟨327209, by rfl⟩ : syracuseStep 436279 = 654419) B654419
theorem B733511 : Blo 255820 733511 := bstep (se 1 (by rfl) ⟨550133, by rfl⟩ : syracuseStep 733511 = 1100267) B1100267
theorem B2473679 : Blo 255820 2473679 := bstep (se 1 (by rfl) ⟨1855259, by rfl⟩ : syracuseStep 2473679 = 3710519) B3710519
theorem B15025409 : Blo 255820 15025409 := bstep (se 2 (by rfl) ⟨5634528, by rfl⟩ : syracuseStep 15025409 = 11269057) B11269057
theorem B870047 : Blo 255820 870047 := bstep (se 1 (by rfl) ⟨652535, by rfl⟩ : syracuseStep 870047 = 1305071) B1305071
theorem B4408991 : Blo 255820 4408991 := bstep (se 1 (by rfl) ⟨3306743, by rfl⟩ : syracuseStep 4408991 = 6613487) B6613487
theorem B936019 : Blo 255820 936019 := bstep (se 1 (by rfl) ⟨702014, by rfl⟩ : syracuseStep 936019 = 1404029) B1404029
theorem B16075169 : Blo 255820 16075169 := bstep (se 2 (by rfl) ⟨6028188, by rfl⟩ : syracuseStep 16075169 = 12056377) B12056377
theorem B576233 : Blo 255820 576233 := bstep (se 2 (by rfl) ⟨216087, by rfl⟩ : syracuseStep 576233 = 432175) B432175
theorem B872585 : Blo 255820 872585 := bstep (se 2 (by rfl) ⟨327219, by rfl⟩ : syracuseStep 872585 = 654439) B654439
theorem B157012111 : Blo 255820 157012111 := bstep (se 1 (by rfl) ⟨117759083, by rfl⟩ : syracuseStep 157012111 = 235518167) B235518167
theorem B872639 : Blo 255820 872639 := bstep (se 1 (by rfl) ⟨654479, by rfl⟩ : syracuseStep 872639 = 1308959) B1308959
theorem B152491855 : Blo 255820 152491855 := bstep (se 1 (by rfl) ⟨114368891, by rfl⟩ : syracuseStep 152491855 = 228737783) B228737783
theorem B1660753 : Blo 255820 1660753 := bstep (se 2 (by rfl) ⟨622782, by rfl⟩ : syracuseStep 1660753 = 1245565) B1245565
theorem B384479 : Blo 255820 384479 := bstep (se 1 (by rfl) ⟨288359, by rfl⟩ : syracuseStep 384479 = 576719) B576719
theorem B384617 : Blo 255820 384617 := bstep (se 2 (by rfl) ⟨144231, by rfl⟩ : syracuseStep 384617 = 288463) B288463
theorem B384719 : Blo 255820 384719 := bstep (se 1 (by rfl) ⟨288539, by rfl⟩ : syracuseStep 384719 = 577079) B577079
theorem B385145 : Blo 255820 385145 := bstep (se 2 (by rfl) ⟨144429, by rfl⟩ : syracuseStep 385145 = 288859) B288859
theorem B385727 : Blo 255820 385727 := bstep (se 1 (by rfl) ⟨289295, by rfl⟩ : syracuseStep 385727 = 578591) B578591
theorem B385883 : Blo 255820 385883 := bstep (se 1 (by rfl) ⟨289412, by rfl⟩ : syracuseStep 385883 = 578825) B578825
theorem B385895 : Blo 255820 385895 := bstep (se 1 (by rfl) ⟨289421, by rfl⟩ : syracuseStep 385895 = 578843) B578843
theorem B256127 : Blo 255820 256127 := bstep (se 1 (by rfl) ⟨192095, by rfl⟩ : syracuseStep 256127 = 384191) B384191
theorem B583847 : Blo 255820 583847 := bstep (se 1 (by rfl) ⟨437885, by rfl⟩ : syracuseStep 583847 = 875771) B875771
theorem B583919 : Blo 255820 583919 := bstep (se 1 (by rfl) ⟨437939, by rfl⟩ : syracuseStep 583919 = 875879) B875879
theorem B16607531 : Blo 255820 16607531 := bstep (se 1 (by rfl) ⟨12455648, by rfl⟩ : syracuseStep 16607531 = 24911297) B24911297
theorem B584135 : Blo 255820 584135 := bstep (se 1 (by rfl) ⟨438101, by rfl⟩ : syracuseStep 584135 = 876203) B876203
theorem B3304799 : Blo 255820 3304799 := bstep (se 1 (by rfl) ⟨2478599, by rfl⟩ : syracuseStep 3304799 = 4957199) B4957199
theorem B388655 : Blo 255820 388655 := bstep (se 1 (by rfl) ⟨291491, by rfl⟩ : syracuseStep 388655 = 582983) B582983
theorem B257647 : Blo 255820 257647 := bstep (se 1 (by rfl) ⟨193235, by rfl⟩ : syracuseStep 257647 = 386471) B386471
theorem B257823 : Blo 255820 257823 := bstep (se 1 (by rfl) ⟨193367, by rfl⟩ : syracuseStep 257823 = 386735) B386735
theorem B520447 : Blo 255820 520447 := bstep (se 1 (by rfl) ⟨390335, by rfl⟩ : syracuseStep 520447 = 780671) B780671
theorem B488263 : Blo 255820 488263 := bstep (se 1 (by rfl) ⟨366197, by rfl⟩ : syracuseStep 488263 = 732395) B732395
theorem B258943 : Blo 255820 258943 := bstep (se 1 (by rfl) ⟨194207, by rfl⟩ : syracuseStep 258943 = 388415) B388415
theorem B2586167 : Blo 255820 2586167 := bstep (se 1 (by rfl) ⟨1939625, by rfl⟩ : syracuseStep 2586167 = 3879251) B3879251
theorem B1243259 : Blo 255820 1243259 := bstep (se 1 (by rfl) ⟨932444, by rfl⟩ : syracuseStep 1243259 = 1864889) B1864889
theorem B3537755 : Blo 255820 3537755 := bstep (se 1 (by rfl) ⟨2653316, by rfl⟩ : syracuseStep 3537755 = 5306633) B5306633
theorem B655067 : Blo 255820 655067 := bstep (se 1 (by rfl) ⟨491300, by rfl⟩ : syracuseStep 655067 = 982601) B982601
theorem B328799 : Blo 255820 328799 := bstep (se 1 (by rfl) ⟨246599, by rfl⟩ : syracuseStep 328799 = 493199) B493199
theorem B984575 : Blo 255820 984575 := bstep (se 1 (by rfl) ⟨738431, by rfl⟩ : syracuseStep 984575 = 1476863) B1476863
theorem B10716779 : Blo 255820 10716779 := bstep (se 1 (by rfl) ⟨8037584, by rfl⟩ : syracuseStep 10716779 = 16075169) B16075169
theorem B1444267 : Blo 255820 1444267 := bstep (se 1 (by rfl) ⟨1083200, by rfl⟩ : syracuseStep 1444267 = 2166401) B2166401
theorem B6294779 : Blo 255820 6294779 := bstep (se 1 (by rfl) ⟨4721084, by rfl⟩ : syracuseStep 6294779 = 9442169) B9442169
theorem B396847 : Blo 255820 396847 := bstep (se 1 (by rfl) ⟨297635, by rfl⟩ : syracuseStep 396847 = 595271) B595271
theorem B660199 : Blo 255820 660199 := bstep (se 1 (by rfl) ⟨495149, by rfl⟩ : syracuseStep 660199 = 990299) B990299
theorem B693929 : Blo 255820 693929 := bstep (se 2 (by rfl) ⟨260223, by rfl⟩ : syracuseStep 693929 = 520447) B520447
theorem B2496359 : Blo 255820 2496359 := bstep (se 1 (by rfl) ⟨1872269, by rfl⟩ : syracuseStep 2496359 = 3744539) B3744539
theorem B2203199 : Blo 255820 2203199 := bstep (se 1 (by rfl) ⟨1652399, by rfl⟩ : syracuseStep 2203199 = 3304799) B3304799
theorem B828839 : Blo 255820 828839 := bstep (se 1 (by rfl) ⟨621629, by rfl⟩ : syracuseStep 828839 = 1243259) B1243259
theorem B1649119 : Blo 255820 1649119 := bstep (se 1 (by rfl) ⟨1236839, by rfl⟩ : syracuseStep 1649119 = 2473679) B2473679
theorem B436711 : Blo 255820 436711 := bstep (se 1 (by rfl) ⟨327533, by rfl⟩ : syracuseStep 436711 = 655067) B655067
theorem B4992101 : Blo 255820 4992101 := bstep (se 4 (by rfl) ⟨468009, by rfl⟩ : syracuseStep 4992101 = 936019) B936019
theorem B837397925 : Blo 255820 837397925 := bstep (se 4 (by rfl) ⟨78506055, by rfl⟩ : syracuseStep 837397925 = 157012111) B157012111
theorem B3585151 : Blo 255820 3585151 := bstep (se 1 (by rfl) ⟨2688863, by rfl⟩ : syracuseStep 3585151 = 5377727) B5377727
theorem B2214337 : Blo 255820 2214337 := bstep (se 2 (by rfl) ⟨830376, by rfl⟩ : syracuseStep 2214337 = 1660753) B1660753
theorem B1724111 : Blo 255820 1724111 := bstep (se 1 (by rfl) ⟨1293083, by rfl⟩ : syracuseStep 1724111 = 2586167) B2586167
theorem B10016939 : Blo 255820 10016939 := bstep (se 1 (by rfl) ⟨7512704, by rfl⟩ : syracuseStep 10016939 = 15025409) B15025409
theorem B580031 : Blo 255820 580031 := bstep (se 1 (by rfl) ⟨435023, by rfl⟩ : syracuseStep 580031 = 870047) B870047
theorem B2939327 : Blo 255820 2939327 := bstep (se 1 (by rfl) ⟨2204495, by rfl⟩ : syracuseStep 2939327 = 4408991) B4408991
theorem B1661755 : Blo 255820 1661755 := bstep (se 1 (by rfl) ⟨1246316, by rfl⟩ : syracuseStep 1661755 = 2492633) B2492633
theorem B384155 : Blo 255820 384155 := bstep (se 1 (by rfl) ⟨288116, by rfl⟩ : syracuseStep 384155 = 576233) B576233
theorem B581705 : Blo 255820 581705 := bstep (se 2 (by rfl) ⟨218139, by rfl⟩ : syracuseStep 581705 = 436279) B436279
theorem B581723 : Blo 255820 581723 := bstep (se 1 (by rfl) ⟨436292, by rfl⟩ : syracuseStep 581723 = 872585) B872585
theorem B581759 : Blo 255820 581759 := bstep (se 1 (by rfl) ⟨436319, by rfl⟩ : syracuseStep 581759 = 872639) B872639
theorem B256319 : Blo 255820 256319 := bstep (se 1 (by rfl) ⟨192239, by rfl⟩ : syracuseStep 256319 = 384479) B384479
theorem B256411 : Blo 255820 256411 := bstep (se 1 (by rfl) ⟨192308, by rfl⟩ : syracuseStep 256411 = 384617) B384617
theorem B256479 : Blo 255820 256479 := bstep (se 1 (by rfl) ⟨192359, by rfl⟩ : syracuseStep 256479 = 384719) B384719
theorem B256763 : Blo 255820 256763 := bstep (se 1 (by rfl) ⟨192572, by rfl⟩ : syracuseStep 256763 = 385145) B385145
theorem B257151 : Blo 255820 257151 := bstep (se 1 (by rfl) ⟨192863, by rfl⟩ : syracuseStep 257151 = 385727) B385727
theorem B257255 : Blo 255820 257255 := bstep (se 1 (by rfl) ⟨192941, by rfl⟩ : syracuseStep 257255 = 385883) B385883
theorem B257263 : Blo 255820 257263 := bstep (se 1 (by rfl) ⟨192947, by rfl⟩ : syracuseStep 257263 = 385895) B385895
theorem B2190827 : Blo 255820 2190827 := bstep (se 1 (by rfl) ⟨1643120, by rfl⟩ : syracuseStep 2190827 = 3286241) B3286241
theorem B651017 : Blo 255820 651017 := bstep (se 2 (by rfl) ⟨244131, by rfl⟩ : syracuseStep 651017 = 488263) B488263
theorem B389231 : Blo 255820 389231 := bstep (se 1 (by rfl) ⟨291923, by rfl⟩ : syracuseStep 389231 = 583847) B583847
theorem B389279 : Blo 255820 389279 := bstep (se 1 (by rfl) ⟨291959, by rfl⟩ : syracuseStep 389279 = 583919) B583919
theorem B11071687 : Blo 255820 11071687 := bstep (se 1 (by rfl) ⟨8303765, by rfl⟩ : syracuseStep 11071687 = 16607531) B16607531
theorem B389423 : Blo 255820 389423 := bstep (se 1 (by rfl) ⟨292067, by rfl⟩ : syracuseStep 389423 = 584135) B584135
theorem B259103 : Blo 255820 259103 := bstep (se 1 (by rfl) ⟨194327, by rfl⟩ : syracuseStep 259103 = 388655) B388655
theorem B203322473 : Blo 255820 203322473 := bstep (se 2 (by rfl) ⟨76245927, by rfl⟩ : syracuseStep 203322473 = 152491855) B152491855
theorem B489007 : Blo 255820 489007 := bstep (se 1 (by rfl) ⟨366755, by rfl⟩ : syracuseStep 489007 = 733511) B733511
theorem B2358503 : Blo 255820 2358503 := bstep (se 1 (by rfl) ⟨1768877, by rfl⟩ : syracuseStep 2358503 = 3537755) B3537755
theorem B656383 : Blo 255820 656383 := bstep (se 1 (by rfl) ⟨492287, by rfl⟩ : syracuseStep 656383 = 984575) B984575
theorem B7144519 : Blo 255820 7144519 := bstep (se 1 (by rfl) ⟨5358389, by rfl⟩ : syracuseStep 7144519 = 10716779) B10716779
theorem B4196519 : Blo 255820 4196519 := bstep (se 1 (by rfl) ⟨3147389, by rfl⟩ : syracuseStep 4196519 = 6294779) B6294779
theorem B1149407 : Blo 255820 1149407 := bstep (se 1 (by rfl) ⟨862055, by rfl⟩ : syracuseStep 1149407 = 1724111) B1724111
theorem B2952449 : Blo 255820 2952449 := bstep (se 2 (by rfl) ⟨1107168, by rfl⟩ : syracuseStep 2952449 = 2214337) B2214337
theorem B2198825 : Blo 255820 2198825 := bstep (se 2 (by rfl) ⟨824559, by rfl⟩ : syracuseStep 2198825 = 1649119) B1649119
theorem B462619 : Blo 255820 462619 := bstep (se 1 (by rfl) ⟨346964, by rfl⟩ : syracuseStep 462619 = 693929) B693929
theorem B529129 : Blo 255820 529129 := bstep (se 2 (by rfl) ⟨198423, by rfl⟩ : syracuseStep 529129 = 396847) B396847
theorem B434011 : Blo 255820 434011 := bstep (se 1 (by rfl) ⟨325508, by rfl⟩ : syracuseStep 434011 = 651017) B651017
theorem B2210237 : Blo 255820 2210237 := bstep (se 3 (by rfl) ⟨414419, by rfl⟩ : syracuseStep 2210237 = 828839) B828839
theorem B14762249 : Blo 255820 14762249 := bstep (se 2 (by rfl) ⟨5535843, by rfl⟩ : syracuseStep 14762249 = 11071687) B11071687
theorem B19120805 : Blo 255820 19120805 := bstep (se 4 (by rfl) ⟨1792575, by rfl⟩ : syracuseStep 19120805 = 3585151) B3585151
theorem B3328067 : Blo 255820 3328067 := bstep (se 1 (by rfl) ⟨2496050, by rfl⟩ : syracuseStep 3328067 = 4992101) B4992101
theorem B1460551 : Blo 255820 1460551 := bstep (se 1 (by rfl) ⟨1095413, by rfl⟩ : syracuseStep 1460551 = 2190827) B2190827
theorem B135548315 : Blo 255820 135548315 := bstep (se 1 (by rfl) ⟨101661236, by rfl⟩ : syracuseStep 135548315 = 203322473) B203322473
theorem B2215673 : Blo 255820 2215673 := bstep (se 2 (by rfl) ⟨830877, by rfl⟩ : syracuseStep 2215673 = 1661755) B1661755
theorem B876797 : Blo 255820 876797 := bstep (se 3 (by rfl) ⟨164399, by rfl⟩ : syracuseStep 876797 = 328799) B328799
theorem B1925689 : Blo 255820 1925689 := bstep (se 2 (by rfl) ⟨722133, by rfl⟩ : syracuseStep 1925689 = 1444267) B1444267
theorem B582281 : Blo 255820 582281 := bstep (se 2 (by rfl) ⟨218355, by rfl⟩ : syracuseStep 582281 = 436711) B436711
theorem B1664239 : Blo 255820 1664239 := bstep (se 1 (by rfl) ⟨1248179, by rfl⟩ : syracuseStep 1664239 = 2496359) B2496359
theorem B6677959 : Blo 255820 6677959 := bstep (se 1 (by rfl) ⟨5008469, by rfl⟩ : syracuseStep 6677959 = 10016939) B10016939
theorem B386687 : Blo 255820 386687 := bstep (se 1 (by rfl) ⟨290015, by rfl⟩ : syracuseStep 386687 = 580031) B580031
theorem B1959551 : Blo 255820 1959551 := bstep (se 1 (by rfl) ⟨1469663, by rfl⟩ : syracuseStep 1959551 = 2939327) B2939327
theorem B256103 : Blo 255820 256103 := bstep (se 1 (by rfl) ⟨192077, by rfl⟩ : syracuseStep 256103 = 384155) B384155
theorem B1468799 : Blo 255820 1468799 := bstep (se 1 (by rfl) ⟨1101599, by rfl⟩ : syracuseStep 1468799 = 2203199) B2203199
theorem B387803 : Blo 255820 387803 := bstep (se 1 (by rfl) ⟨290852, by rfl⟩ : syracuseStep 387803 = 581705) B581705
theorem B387815 : Blo 255820 387815 := bstep (se 1 (by rfl) ⟨290861, by rfl⟩ : syracuseStep 387815 = 581723) B581723
theorem B387839 : Blo 255820 387839 := bstep (se 1 (by rfl) ⟨290879, by rfl⟩ : syracuseStep 387839 = 581759) B581759
theorem B880265 : Blo 255820 880265 := bstep (se 2 (by rfl) ⟨330099, by rfl⟩ : syracuseStep 880265 = 660199) B660199
theorem B652009 : Blo 255820 652009 := bstep (se 2 (by rfl) ⟨244503, by rfl⟩ : syracuseStep 652009 = 489007) B489007
theorem B558265283 : Blo 255820 558265283 := bstep (se 1 (by rfl) ⟨418698962, by rfl⟩ : syracuseStep 558265283 = 837397925) B837397925
theorem B259487 : Blo 255820 259487 := bstep (se 1 (by rfl) ⟨194615, by rfl⟩ : syracuseStep 259487 = 389231) B389231
theorem B259519 : Blo 255820 259519 := bstep (se 1 (by rfl) ⟨194639, by rfl⟩ : syracuseStep 259519 = 389279) B389279
theorem B259615 : Blo 255820 259615 := bstep (se 1 (by rfl) ⟨194711, by rfl⟩ : syracuseStep 259615 = 389423) B389423
theorem B1572335 : Blo 255820 1572335 := bstep (se 1 (by rfl) ⟨1179251, by rfl⟩ : syracuseStep 1572335 = 2358503) B2358503
theorem B12747203 : Blo 255820 12747203 := bstep (se 1 (by rfl) ⟨9560402, by rfl⟩ : syracuseStep 12747203 = 19120805) B19120805
theorem B1968299 : Blo 255820 1968299 := bstep (se 1 (by rfl) ⟨1476224, by rfl⟩ : syracuseStep 1968299 = 2952449) B2952449
theorem B1477115 : Blo 255820 1477115 := bstep (se 1 (by rfl) ⟨1107836, by rfl⟩ : syracuseStep 1477115 = 2215673) B2215673
theorem B9841499 : Blo 255820 9841499 := bstep (se 1 (by rfl) ⟨7381124, by rfl⟩ : syracuseStep 9841499 = 14762249) B14762249
theorem B2567585 : Blo 255820 2567585 := bstep (se 2 (by rfl) ⟨962844, by rfl⟩ : syracuseStep 2567585 = 1925689) B1925689
theorem B2797679 : Blo 255820 2797679 := bstep (se 1 (by rfl) ⟨2098259, by rfl⟩ : syracuseStep 2797679 = 4196519) B4196519
theorem B766271 : Blo 255820 766271 := bstep (se 1 (by rfl) ⟨574703, by rfl⟩ : syracuseStep 766271 = 1149407) B1149407
theorem B1947401 : Blo 255820 1947401 := bstep (se 2 (by rfl) ⟨730275, by rfl⟩ : syracuseStep 1947401 = 1460551) B1460551
theorem B705505 : Blo 255820 705505 := bstep (se 2 (by rfl) ⟨264564, by rfl⟩ : syracuseStep 705505 = 529129) B529129
theorem B869345 : Blo 255820 869345 := bstep (se 2 (by rfl) ⟨326004, by rfl⟩ : syracuseStep 869345 = 652009) B652009
theorem B2347373 : Blo 255820 2347373 := bstep (se 3 (by rfl) ⟨440132, by rfl⟩ : syracuseStep 2347373 = 880265) B880265
theorem B578681 : Blo 255820 578681 := bstep (se 2 (by rfl) ⟨217005, by rfl⟩ : syracuseStep 578681 = 434011) B434011
theorem B875177 : Blo 255820 875177 := bstep (se 2 (by rfl) ⟨328191, by rfl⟩ : syracuseStep 875177 = 656383) B656383
theorem B2218711 : Blo 255820 2218711 := bstep (se 1 (by rfl) ⟨1664033, by rfl⟩ : syracuseStep 2218711 = 3328067) B3328067
theorem B9526025 : Blo 255820 9526025 := bstep (se 2 (by rfl) ⟨3572259, by rfl⟩ : syracuseStep 9526025 = 7144519) B7144519
theorem B2218985 : Blo 255820 2218985 := bstep (se 2 (by rfl) ⟨832119, by rfl⟩ : syracuseStep 2218985 = 1664239) B1664239
theorem B8903945 : Blo 255820 8903945 := bstep (se 2 (by rfl) ⟨3338979, by rfl⟩ : syracuseStep 8903945 = 6677959) B6677959
theorem B1465883 : Blo 255820 1465883 := bstep (se 1 (by rfl) ⟨1099412, by rfl⟩ : syracuseStep 1465883 = 2198825) B2198825
theorem B90365543 : Blo 255820 90365543 := bstep (se 1 (by rfl) ⟨67774157, by rfl⟩ : syracuseStep 90365543 = 135548315) B135548315
theorem B616825 : Blo 255820 616825 := bstep (se 2 (by rfl) ⟨231309, by rfl⟩ : syracuseStep 616825 = 462619) B462619
theorem B584531 : Blo 255820 584531 := bstep (se 1 (by rfl) ⟨438398, by rfl⟩ : syracuseStep 584531 = 876797) B876797
theorem B388187 : Blo 255820 388187 := bstep (se 1 (by rfl) ⟨291140, by rfl⟩ : syracuseStep 388187 = 582281) B582281
theorem B257791 : Blo 255820 257791 := bstep (se 1 (by rfl) ⟨193343, by rfl⟩ : syracuseStep 257791 = 386687) B386687
theorem B1306367 : Blo 255820 1306367 := bstep (se 1 (by rfl) ⟨979775, by rfl⟩ : syracuseStep 1306367 = 1959551) B1959551
theorem B979199 : Blo 255820 979199 := bstep (se 1 (by rfl) ⟨734399, by rfl⟩ : syracuseStep 979199 = 1468799) B1468799
theorem B258535 : Blo 255820 258535 := bstep (se 1 (by rfl) ⟨193901, by rfl⟩ : syracuseStep 258535 = 387803) B387803
theorem B258543 : Blo 255820 258543 := bstep (se 1 (by rfl) ⟨193907, by rfl⟩ : syracuseStep 258543 = 387815) B387815
theorem B258559 : Blo 255820 258559 := bstep (se 1 (by rfl) ⟨193919, by rfl⟩ : syracuseStep 258559 = 387839) B387839
theorem B372176855 : Blo 255820 372176855 := bstep (se 1 (by rfl) ⟨279132641, by rfl⟩ : syracuseStep 372176855 = 558265283) B558265283
theorem B1473491 : Blo 255820 1473491 := bstep (se 1 (by rfl) ⟨1105118, by rfl⟩ : syracuseStep 1473491 = 2210237) B2210237
theorem B1048223 : Blo 255820 1048223 := bstep (se 1 (by rfl) ⟨786167, by rfl⟩ : syracuseStep 1048223 = 1572335) B1572335
theorem B1312199 : Blo 255820 1312199 := bstep (se 1 (by rfl) ⟨984149, by rfl⟩ : syracuseStep 1312199 = 1968299) B1968299
theorem B984743 : Blo 255820 984743 := bstep (se 1 (by rfl) ⟨738557, by rfl⟩ : syracuseStep 984743 = 1477115) B1477115
theorem B822433 : Blo 255820 822433 := bstep (se 2 (by rfl) ⟨308412, by rfl⟩ : syracuseStep 822433 = 616825) B616825
theorem B1479323 : Blo 255820 1479323 := bstep (se 1 (by rfl) ⟨1109492, by rfl⟩ : syracuseStep 1479323 = 2218985) B2218985
theorem B5935963 : Blo 255820 5935963 := bstep (se 1 (by rfl) ⟨4451972, by rfl⟩ : syracuseStep 5935963 = 8903945) B8903945
theorem B6560999 : Blo 255820 6560999 := bstep (se 1 (by rfl) ⟨4920749, by rfl⟩ : syracuseStep 6560999 = 9841499) B9841499
theorem B2958281 : Blo 255820 2958281 := bstep (se 2 (by rfl) ⟨1109355, by rfl⟩ : syracuseStep 2958281 = 2218711) B2218711
theorem B698815 : Blo 255820 698815 := bstep (se 1 (by rfl) ⟨524111, by rfl⟩ : syracuseStep 698815 = 1048223) B1048223
theorem B8498135 : Blo 255820 8498135 := bstep (se 1 (by rfl) ⟨6373601, by rfl⟩ : syracuseStep 8498135 = 12747203) B12747203
theorem B2043389 : Blo 255820 2043389 := bstep (se 3 (by rfl) ⟨383135, by rfl⟩ : syracuseStep 2043389 = 766271) B766271
theorem B60243695 : Blo 255820 60243695 := bstep (se 1 (by rfl) ⟨45182771, by rfl⟩ : syracuseStep 60243695 = 90365543) B90365543
theorem B870911 : Blo 255820 870911 := bstep (se 1 (by rfl) ⟨653183, by rfl⟩ : syracuseStep 870911 = 1306367) B1306367
theorem B1298267 : Blo 255820 1298267 := bstep (se 1 (by rfl) ⟨973700, by rfl⟩ : syracuseStep 1298267 = 1947401) B1947401
theorem B579563 : Blo 255820 579563 := bstep (se 1 (by rfl) ⟨434672, by rfl⟩ : syracuseStep 579563 = 869345) B869345
theorem B940673 : Blo 255820 940673 := bstep (se 2 (by rfl) ⟨352752, by rfl⟩ : syracuseStep 940673 = 705505) B705505
theorem B1564915 : Blo 255820 1564915 := bstep (se 1 (by rfl) ⟨1173686, by rfl⟩ : syracuseStep 1564915 = 2347373) B2347373
theorem B385787 : Blo 255820 385787 := bstep (se 1 (by rfl) ⟨289340, by rfl⟩ : syracuseStep 385787 = 578681) B578681
theorem B583451 : Blo 255820 583451 := bstep (se 1 (by rfl) ⟨437588, by rfl⟩ : syracuseStep 583451 = 875177) B875177
theorem B6350683 : Blo 255820 6350683 := bstep (se 1 (by rfl) ⟨4763012, by rfl⟩ : syracuseStep 6350683 = 9526025) B9526025
theorem B977255 : Blo 255820 977255 := bstep (se 1 (by rfl) ⟨732941, by rfl⟩ : syracuseStep 977255 = 1465883) B1465883
theorem B389687 : Blo 255820 389687 := bstep (se 1 (by rfl) ⟨292265, by rfl⟩ : syracuseStep 389687 = 584531) B584531
theorem B258791 : Blo 255820 258791 := bstep (se 1 (by rfl) ⟨194093, by rfl⟩ : syracuseStep 258791 = 388187) B388187
theorem B1865119 : Blo 255820 1865119 := bstep (se 1 (by rfl) ⟨1398839, by rfl⟩ : syracuseStep 1865119 = 2797679) B2797679
theorem B652799 : Blo 255820 652799 := bstep (se 1 (by rfl) ⟨489599, by rfl⟩ : syracuseStep 652799 = 979199) B979199
theorem B6846893 : Blo 255820 6846893 := bstep (se 3 (by rfl) ⟨1283792, by rfl⟩ : syracuseStep 6846893 = 2567585) B2567585
theorem B248117903 : Blo 255820 248117903 := bstep (se 1 (by rfl) ⟨186088427, by rfl⟩ : syracuseStep 248117903 = 372176855) B372176855
theorem B982327 : Blo 255820 982327 := bstep (se 1 (by rfl) ⟨736745, by rfl⟩ : syracuseStep 982327 = 1473491) B1473491
theorem B656495 : Blo 255820 656495 := bstep (se 1 (by rfl) ⟨492371, by rfl⟩ : syracuseStep 656495 = 984743) B984743
theorem B986215 : Blo 255820 986215 := bstep (se 1 (by rfl) ⟨739661, by rfl⟩ : syracuseStep 986215 = 1479323) B1479323
theorem B627115 : Blo 255820 627115 := bstep (se 1 (by rfl) ⟨470336, by rfl⟩ : syracuseStep 627115 = 940673) B940673
theorem B1972187 : Blo 255820 1972187 := bstep (se 1 (by rfl) ⟨1479140, by rfl⟩ : syracuseStep 1972187 = 2958281) B2958281
theorem B435199 : Blo 255820 435199 := bstep (se 1 (by rfl) ⟨326399, by rfl⟩ : syracuseStep 435199 = 652799) B652799
theorem B5449037 : Blo 255820 5449037 := bstep (se 3 (by rfl) ⟨1021694, by rfl⟩ : syracuseStep 5449037 = 2043389) B2043389
theorem B4564595 : Blo 255820 4564595 := bstep (se 1 (by rfl) ⟨3423446, by rfl⟩ : syracuseStep 4564595 = 6846893) B6846893
theorem B8467577 : Blo 255820 8467577 := bstep (se 2 (by rfl) ⟨3175341, by rfl⟩ : syracuseStep 8467577 = 6350683) B6350683
theorem B865511 : Blo 255820 865511 := bstep (se 1 (by rfl) ⟨649133, by rfl⟩ : syracuseStep 865511 = 1298267) B1298267
theorem B931753 : Blo 255820 931753 := bstep (se 2 (by rfl) ⟨349407, by rfl⟩ : syracuseStep 931753 = 698815) B698815
theorem B1096577 : Blo 255820 1096577 := bstep (se 2 (by rfl) ⟨411216, by rfl⟩ : syracuseStep 1096577 = 822433) B822433
theorem B4373999 : Blo 255820 4373999 := bstep (se 1 (by rfl) ⟨3280499, by rfl⟩ : syracuseStep 4373999 = 6560999) B6560999
theorem B7914617 : Blo 255820 7914617 := bstep (se 2 (by rfl) ⟨2967981, by rfl⟩ : syracuseStep 7914617 = 5935963) B5935963
theorem B40162463 : Blo 255820 40162463 := bstep (se 1 (by rfl) ⟨30121847, by rfl⟩ : syracuseStep 40162463 = 60243695) B60243695
theorem B2086553 : Blo 255820 2086553 := bstep (se 2 (by rfl) ⟨782457, by rfl⟩ : syracuseStep 2086553 = 1564915) B1564915
theorem B874799 : Blo 255820 874799 := bstep (se 1 (by rfl) ⟨656099, by rfl⟩ : syracuseStep 874799 = 1312199) B1312199
theorem B580607 : Blo 255820 580607 := bstep (se 1 (by rfl) ⟨435455, by rfl⟩ : syracuseStep 580607 = 870911) B870911
theorem B386375 : Blo 255820 386375 := bstep (se 1 (by rfl) ⟨289781, by rfl⟩ : syracuseStep 386375 = 579563) B579563
theorem B257191 : Blo 255820 257191 := bstep (se 1 (by rfl) ⟨192893, by rfl⟩ : syracuseStep 257191 = 385787) B385787
theorem B388967 : Blo 255820 388967 := bstep (se 1 (by rfl) ⟨291725, by rfl⟩ : syracuseStep 388967 = 583451) B583451
theorem B651503 : Blo 255820 651503 := bstep (se 1 (by rfl) ⟨488627, by rfl⟩ : syracuseStep 651503 = 977255) B977255
theorem B2486825 : Blo 255820 2486825 := bstep (se 2 (by rfl) ⟨932559, by rfl⟩ : syracuseStep 2486825 = 1865119) B1865119
theorem B5665423 : Blo 255820 5665423 := bstep (se 1 (by rfl) ⟨4249067, by rfl⟩ : syracuseStep 5665423 = 8498135) B8498135
theorem B259791 : Blo 255820 259791 := bstep (se 1 (by rfl) ⟨194843, by rfl⟩ : syracuseStep 259791 = 389687) B389687
theorem B1309769 : Blo 255820 1309769 := bstep (se 2 (by rfl) ⟨491163, by rfl⟩ : syracuseStep 1309769 = 982327) B982327
theorem B165411935 : Blo 255820 165411935 := bstep (se 1 (by rfl) ⟨124058951, by rfl⟩ : syracuseStep 165411935 = 248117903) B248117903
theorem B5276411 : Blo 255820 5276411 := bstep (se 1 (by rfl) ⟨3957308, by rfl⟩ : syracuseStep 5276411 = 7914617) B7914617
theorem B26774975 : Blo 255820 26774975 := bstep (se 1 (by rfl) ⟨20081231, by rfl⟩ : syracuseStep 26774975 = 40162463) B40162463
theorem B1314791 : Blo 255820 1314791 := bstep (se 1 (by rfl) ⟨986093, by rfl⟩ : syracuseStep 1314791 = 1972187) B1972187
theorem B1314953 : Blo 255820 1314953 := bstep (se 2 (by rfl) ⟨493107, by rfl⟩ : syracuseStep 1314953 = 986215) B986215
theorem B434335 : Blo 255820 434335 := bstep (se 1 (by rfl) ⟨325751, by rfl⟩ : syracuseStep 434335 = 651503) B651503
theorem B5645051 : Blo 255820 5645051 := bstep (se 1 (by rfl) ⟨4233788, by rfl⟩ : syracuseStep 5645051 = 8467577) B8467577
theorem B731051 : Blo 255820 731051 := bstep (se 1 (by rfl) ⟨548288, by rfl⟩ : syracuseStep 731051 = 1096577) B1096577
theorem B110274623 : Blo 255820 110274623 := bstep (se 1 (by rfl) ⟨82705967, by rfl⟩ : syracuseStep 110274623 = 165411935) B165411935
theorem B437663 : Blo 255820 437663 := bstep (se 1 (by rfl) ⟨328247, by rfl⟩ : syracuseStep 437663 = 656495) B656495
theorem B14530765 : Blo 255820 14530765 := bstep (se 3 (by rfl) ⟨2724518, by rfl⟩ : syracuseStep 14530765 = 5449037) B5449037
theorem B1391035 : Blo 255820 1391035 := bstep (se 1 (by rfl) ⟨1043276, by rfl⟩ : syracuseStep 1391035 = 2086553) B2086553
theorem B836153 : Blo 255820 836153 := bstep (se 2 (by rfl) ⟨313557, by rfl⟩ : syracuseStep 836153 = 627115) B627115
theorem B7553897 : Blo 255820 7553897 := bstep (se 2 (by rfl) ⟨2832711, by rfl⟩ : syracuseStep 7553897 = 5665423) B5665423
theorem B1657883 : Blo 255820 1657883 := bstep (se 1 (by rfl) ⟨1243412, by rfl⟩ : syracuseStep 1657883 = 2486825) B2486825
theorem B577007 : Blo 255820 577007 := bstep (se 1 (by rfl) ⟨432755, by rfl⟩ : syracuseStep 577007 = 865511) B865511
theorem B873179 : Blo 255820 873179 := bstep (se 1 (by rfl) ⟨654884, by rfl⟩ : syracuseStep 873179 = 1309769) B1309769
theorem B580265 : Blo 255820 580265 := bstep (se 2 (by rfl) ⟨217599, by rfl⟩ : syracuseStep 580265 = 435199) B435199
theorem B583199 : Blo 255820 583199 := bstep (se 1 (by rfl) ⟨437399, by rfl⟩ : syracuseStep 583199 = 874799) B874799
theorem B387071 : Blo 255820 387071 := bstep (se 1 (by rfl) ⟨290303, by rfl⟩ : syracuseStep 387071 = 580607) B580607
theorem B257583 : Blo 255820 257583 := bstep (se 1 (by rfl) ⟨193187, by rfl⟩ : syracuseStep 257583 = 386375) B386375
theorem B3043063 : Blo 255820 3043063 := bstep (se 1 (by rfl) ⟨2282297, by rfl⟩ : syracuseStep 3043063 = 4564595) B4564595
theorem B1242337 : Blo 255820 1242337 := bstep (se 2 (by rfl) ⟨465876, by rfl⟩ : syracuseStep 1242337 = 931753) B931753
theorem B259311 : Blo 255820 259311 := bstep (se 1 (by rfl) ⟨194483, by rfl⟩ : syracuseStep 259311 = 388967) B388967
theorem B2915999 : Blo 255820 2915999 := bstep (se 1 (by rfl) ⟨2186999, by rfl⟩ : syracuseStep 2915999 = 4373999) B4373999
theorem B557435 : Blo 255820 557435 := bstep (se 1 (by rfl) ⟨418076, by rfl⟩ : syracuseStep 557435 = 836153) B836153
theorem B19374353 : Blo 255820 19374353 := bstep (se 2 (by rfl) ⟨7265382, by rfl⟩ : syracuseStep 19374353 = 14530765) B14530765
theorem B1943999 : Blo 255820 1943999 := bstep (se 1 (by rfl) ⟨1457999, by rfl⟩ : syracuseStep 1943999 = 2915999) B2915999
theorem B3517607 : Blo 255820 3517607 := bstep (se 1 (by rfl) ⟨2638205, by rfl⟩ : syracuseStep 3517607 = 5276411) B5276411
theorem B73516415 : Blo 255820 73516415 := bstep (se 1 (by rfl) ⟨55137311, by rfl⟩ : syracuseStep 73516415 = 110274623) B110274623
theorem B1656449 : Blo 255820 1656449 := bstep (se 2 (by rfl) ⟨621168, by rfl⟩ : syracuseStep 1656449 = 1242337) B1242337
theorem B1854713 : Blo 255820 1854713 := bstep (se 2 (by rfl) ⟨695517, by rfl⟩ : syracuseStep 1854713 = 1391035) B1391035
theorem B579113 : Blo 255820 579113 := bstep (se 2 (by rfl) ⟨217167, by rfl⟩ : syracuseStep 579113 = 434335) B434335
theorem B5035931 : Blo 255820 5035931 := bstep (se 1 (by rfl) ⟨3776948, by rfl⟩ : syracuseStep 5035931 = 7553897) B7553897
theorem B1105255 : Blo 255820 1105255 := bstep (se 1 (by rfl) ⟨828941, by rfl⟩ : syracuseStep 1105255 = 1657883) B1657883
theorem B17849983 : Blo 255820 17849983 := bstep (se 1 (by rfl) ⟨13387487, by rfl⟩ : syracuseStep 17849983 = 26774975) B26774975
theorem B384671 : Blo 255820 384671 := bstep (se 1 (by rfl) ⟨288503, by rfl⟩ : syracuseStep 384671 = 577007) B577007
theorem B876527 : Blo 255820 876527 := bstep (se 1 (by rfl) ⟨657395, by rfl⟩ : syracuseStep 876527 = 1314791) B1314791
theorem B876635 : Blo 255820 876635 := bstep (se 1 (by rfl) ⟨657476, by rfl⟩ : syracuseStep 876635 = 1314953) B1314953
theorem B582119 : Blo 255820 582119 := bstep (se 1 (by rfl) ⟨436589, by rfl⟩ : syracuseStep 582119 = 873179) B873179
theorem B386843 : Blo 255820 386843 := bstep (se 1 (by rfl) ⟨290132, by rfl⟩ : syracuseStep 386843 = 580265) B580265
theorem B4057417 : Blo 255820 4057417 := bstep (se 2 (by rfl) ⟨1521531, by rfl⟩ : syracuseStep 4057417 = 3043063) B3043063
theorem B3763367 : Blo 255820 3763367 := bstep (se 1 (by rfl) ⟨2822525, by rfl⟩ : syracuseStep 3763367 = 5645051) B5645051
theorem B388799 : Blo 255820 388799 := bstep (se 1 (by rfl) ⟨291599, by rfl⟩ : syracuseStep 388799 = 583199) B583199
theorem B487367 : Blo 255820 487367 := bstep (se 1 (by rfl) ⟨365525, by rfl⟩ : syracuseStep 487367 = 731051) B731051
theorem B258047 : Blo 255820 258047 := bstep (se 1 (by rfl) ⟨193535, by rfl⟩ : syracuseStep 258047 = 387071) B387071
theorem B291775 : Blo 255820 291775 := bstep (se 1 (by rfl) ⟨218831, by rfl⟩ : syracuseStep 291775 = 437663) B437663
theorem B12916235 : Blo 255820 12916235 := bstep (se 1 (by rfl) ⟨9687176, by rfl⟩ : syracuseStep 12916235 = 19374353) B19374353
theorem B9380285 : Blo 255820 9380285 := bstep (se 3 (by rfl) ⟨1758803, by rfl⟩ : syracuseStep 9380285 = 3517607) B3517607
theorem B23799977 : Blo 255820 23799977 := bstep (se 2 (by rfl) ⟨8924991, by rfl⟩ : syracuseStep 23799977 = 17849983) B17849983
theorem B371623 : Blo 255820 371623 := bstep (se 1 (by rfl) ⟨278717, by rfl⟩ : syracuseStep 371623 = 557435) B557435
theorem B21639557 : Blo 255820 21639557 := bstep (se 4 (by rfl) ⟨2028708, by rfl⟩ : syracuseStep 21639557 = 4057417) B4057417
theorem B3357287 : Blo 255820 3357287 := bstep (se 1 (by rfl) ⟨2517965, by rfl⟩ : syracuseStep 3357287 = 5035931) B5035931
theorem B1295999 : Blo 255820 1295999 := bstep (se 1 (by rfl) ⟨971999, by rfl⟩ : syracuseStep 1295999 = 1943999) B1943999
theorem B2508911 : Blo 255820 2508911 := bstep (se 1 (by rfl) ⟨1881683, by rfl⟩ : syracuseStep 2508911 = 3763367) B3763367
theorem B1104299 : Blo 255820 1104299 := bstep (se 1 (by rfl) ⟨828224, by rfl⟩ : syracuseStep 1104299 = 1656449) B1656449
theorem B1236475 : Blo 255820 1236475 := bstep (se 1 (by rfl) ⟨927356, by rfl⟩ : syracuseStep 1236475 = 1854713) B1854713
theorem B196043773 : Blo 255820 196043773 := bstep (se 3 (by rfl) ⟨36758207, by rfl⟩ : syracuseStep 196043773 = 73516415) B73516415
theorem B386075 : Blo 255820 386075 := bstep (se 1 (by rfl) ⟨289556, by rfl⟩ : syracuseStep 386075 = 579113) B579113
theorem B256447 : Blo 255820 256447 := bstep (se 1 (by rfl) ⟨192335, by rfl⟩ : syracuseStep 256447 = 384671) B384671
theorem B584351 : Blo 255820 584351 := bstep (se 1 (by rfl) ⟨438263, by rfl⟩ : syracuseStep 584351 = 876527) B876527
theorem B584423 : Blo 255820 584423 := bstep (se 1 (by rfl) ⟨438317, by rfl⟩ : syracuseStep 584423 = 876635) B876635
theorem B388079 : Blo 255820 388079 := bstep (se 1 (by rfl) ⟨291059, by rfl⟩ : syracuseStep 388079 = 582119) B582119
theorem B257895 : Blo 255820 257895 := bstep (se 1 (by rfl) ⟨193421, by rfl⟩ : syracuseStep 257895 = 386843) B386843
theorem B389033 : Blo 255820 389033 := bstep (se 2 (by rfl) ⟨145887, by rfl⟩ : syracuseStep 389033 = 291775) B291775
theorem B259199 : Blo 255820 259199 := bstep (se 1 (by rfl) ⟨194399, by rfl⟩ : syracuseStep 259199 = 388799) B388799
theorem B324911 : Blo 255820 324911 := bstep (se 1 (by rfl) ⟨243683, by rfl⟩ : syracuseStep 324911 = 487367) B487367
theorem B1473673 : Blo 255820 1473673 := bstep (se 2 (by rfl) ⟨552627, by rfl⟩ : syracuseStep 1473673 = 1105255) B1105255
theorem B261391697 : Blo 255820 261391697 := bstep (se 2 (by rfl) ⟨98021886, by rfl⟩ : syracuseStep 261391697 = 196043773) B196043773
theorem B1672607 : Blo 255820 1672607 := bstep (se 1 (by rfl) ⟨1254455, by rfl⟩ : syracuseStep 1672607 = 2508911) B2508911
theorem B495497 : Blo 255820 495497 := bstep (se 2 (by rfl) ⟨185811, by rfl⟩ : syracuseStep 495497 = 371623) B371623
theorem B15866651 : Blo 255820 15866651 := bstep (se 1 (by rfl) ⟨11899988, by rfl⟩ : syracuseStep 15866651 = 23799977) B23799977
theorem B14426371 : Blo 255820 14426371 := bstep (se 1 (by rfl) ⟨10819778, by rfl⟩ : syracuseStep 14426371 = 21639557) B21639557
theorem B2238191 : Blo 255820 2238191 := bstep (se 1 (by rfl) ⟨1678643, by rfl⟩ : syracuseStep 2238191 = 3357287) B3357287
theorem B1648633 : Blo 255820 1648633 := bstep (se 2 (by rfl) ⟨618237, by rfl⟩ : syracuseStep 1648633 = 1236475) B1236475
theorem B863999 : Blo 255820 863999 := bstep (se 1 (by rfl) ⟨647999, by rfl⟩ : syracuseStep 863999 = 1295999) B1295999
theorem B866429 : Blo 255820 866429 := bstep (se 3 (by rfl) ⟨162455, by rfl⟩ : syracuseStep 866429 = 324911) B324911
theorem B736199 : Blo 255820 736199 := bstep (se 1 (by rfl) ⟨552149, by rfl⟩ : syracuseStep 736199 = 1104299) B1104299
theorem B8610823 : Blo 255820 8610823 := bstep (se 1 (by rfl) ⟨6458117, by rfl⟩ : syracuseStep 8610823 = 12916235) B12916235
theorem B6253523 : Blo 255820 6253523 := bstep (se 1 (by rfl) ⟨4690142, by rfl⟩ : syracuseStep 6253523 = 9380285) B9380285
theorem B257383 : Blo 255820 257383 := bstep (se 1 (by rfl) ⟨193037, by rfl⟩ : syracuseStep 257383 = 386075) B386075
theorem B389567 : Blo 255820 389567 := bstep (se 1 (by rfl) ⟨292175, by rfl⟩ : syracuseStep 389567 = 584351) B584351
theorem B389615 : Blo 255820 389615 := bstep (se 1 (by rfl) ⟨292211, by rfl⟩ : syracuseStep 389615 = 584423) B584423
theorem B258719 : Blo 255820 258719 := bstep (se 1 (by rfl) ⟨194039, by rfl⟩ : syracuseStep 258719 = 388079) B388079
theorem B259355 : Blo 255820 259355 := bstep (se 1 (by rfl) ⟨194516, by rfl⟩ : syracuseStep 259355 = 389033) B389033
theorem B1964897 : Blo 255820 1964897 := bstep (se 2 (by rfl) ⟨736836, by rfl⟩ : syracuseStep 1964897 = 1473673) B1473673
theorem B19235161 : Blo 255820 19235161 := bstep (se 2 (by rfl) ⟨7213185, by rfl⟩ : syracuseStep 19235161 = 14426371) B14426371
theorem B174261131 : Blo 255820 174261131 := bstep (se 1 (by rfl) ⟨130695848, by rfl⟩ : syracuseStep 174261131 = 261391697) B261391697
theorem B2198177 : Blo 255820 2198177 := bstep (se 2 (by rfl) ⟨824316, by rfl⟩ : syracuseStep 2198177 = 1648633) B1648633
theorem B4460285 : Blo 255820 4460285 := bstep (se 3 (by rfl) ⟨836303, by rfl⟩ : syracuseStep 4460285 = 1672607) B1672607
theorem B4169015 : Blo 255820 4169015 := bstep (se 1 (by rfl) ⟨3126761, by rfl⟩ : syracuseStep 4169015 = 6253523) B6253523
theorem B42311069 : Blo 255820 42311069 := bstep (se 3 (by rfl) ⟨7933325, by rfl⟩ : syracuseStep 42311069 = 15866651) B15866651
theorem B1321325 : Blo 255820 1321325 := bstep (se 3 (by rfl) ⟨247748, by rfl⟩ : syracuseStep 1321325 = 495497) B495497
theorem B11481097 : Blo 255820 11481097 := bstep (se 2 (by rfl) ⟨4305411, by rfl⟩ : syracuseStep 11481097 = 8610823) B8610823
theorem B1492127 : Blo 255820 1492127 := bstep (se 1 (by rfl) ⟨1119095, by rfl⟩ : syracuseStep 1492127 = 2238191) B2238191
theorem B575999 : Blo 255820 575999 := bstep (se 1 (by rfl) ⟨431999, by rfl⟩ : syracuseStep 575999 = 863999) B863999
theorem B577619 : Blo 255820 577619 := bstep (se 1 (by rfl) ⟨433214, by rfl⟩ : syracuseStep 577619 = 866429) B866429
theorem B259711 : Blo 255820 259711 := bstep (se 1 (by rfl) ⟨194783, by rfl⟩ : syracuseStep 259711 = 389567) B389567
theorem B259743 : Blo 255820 259743 := bstep (se 1 (by rfl) ⟨194807, by rfl⟩ : syracuseStep 259743 = 389615) B389615
theorem B1309931 : Blo 255820 1309931 := bstep (se 1 (by rfl) ⟨982448, by rfl⟩ : syracuseStep 1309931 = 1964897) B1964897
theorem B490799 : Blo 255820 490799 := bstep (se 1 (by rfl) ⟨368099, by rfl⟩ : syracuseStep 490799 = 736199) B736199
theorem B15308129 : Blo 255820 15308129 := bstep (se 2 (by rfl) ⟨5740548, by rfl⟩ : syracuseStep 15308129 = 11481097) B11481097
theorem B116174087 : Blo 255820 116174087 := bstep (se 1 (by rfl) ⟨87130565, by rfl⟩ : syracuseStep 116174087 = 174261131) B174261131
theorem B994751 : Blo 255820 994751 := bstep (se 1 (by rfl) ⟨746063, by rfl⟩ : syracuseStep 994751 = 1492127) B1492127
theorem B873287 : Blo 255820 873287 := bstep (se 1 (by rfl) ⟨654965, by rfl⟩ : syracuseStep 873287 = 1309931) B1309931
theorem B25646881 : Blo 255820 25646881 := bstep (se 2 (by rfl) ⟨9617580, by rfl⟩ : syracuseStep 25646881 = 19235161) B19235161
theorem B383999 : Blo 255820 383999 := bstep (se 1 (by rfl) ⟨287999, by rfl⟩ : syracuseStep 383999 = 575999) B575999
theorem B1465451 : Blo 255820 1465451 := bstep (se 1 (by rfl) ⟨1099088, by rfl⟩ : syracuseStep 1465451 = 2198177) B2198177
theorem B2973523 : Blo 255820 2973523 := bstep (se 1 (by rfl) ⟨2230142, by rfl⟩ : syracuseStep 2973523 = 4460285) B4460285
theorem B385079 : Blo 255820 385079 := bstep (se 1 (by rfl) ⟨288809, by rfl⟩ : syracuseStep 385079 = 577619) B577619
theorem B2779343 : Blo 255820 2779343 := bstep (se 1 (by rfl) ⟨2084507, by rfl⟩ : syracuseStep 2779343 = 4169015) B4169015
theorem B28207379 : Blo 255820 28207379 := bstep (se 1 (by rfl) ⟨21155534, by rfl⟩ : syracuseStep 28207379 = 42311069) B42311069
theorem B880883 : Blo 255820 880883 := bstep (se 1 (by rfl) ⟨660662, by rfl⟩ : syracuseStep 880883 = 1321325) B1321325
theorem B1308797 : Blo 255820 1308797 := bstep (se 3 (by rfl) ⟨245399, by rfl⟩ : syracuseStep 1308797 = 490799) B490799
theorem B663167 : Blo 255820 663167 := bstep (se 1 (by rfl) ⟨497375, by rfl⟩ : syracuseStep 663167 = 994751) B994751
theorem B1852895 : Blo 255820 1852895 := bstep (se 1 (by rfl) ⟨1389671, by rfl⟩ : syracuseStep 1852895 = 2779343) B2779343
theorem B77449391 : Blo 255820 77449391 := bstep (se 1 (by rfl) ⟨58087043, by rfl⟩ : syracuseStep 77449391 = 116174087) B116174087
theorem B34195841 : Blo 255820 34195841 := bstep (se 2 (by rfl) ⟨12823440, by rfl⟩ : syracuseStep 34195841 = 25646881) B25646881
theorem B872531 : Blo 255820 872531 := bstep (se 1 (by rfl) ⟨654398, by rfl⟩ : syracuseStep 872531 = 1308797) B1308797
theorem B582191 : Blo 255820 582191 := bstep (se 1 (by rfl) ⟨436643, by rfl⟩ : syracuseStep 582191 = 873287) B873287
theorem B40821677 : Blo 255820 40821677 := bstep (se 3 (by rfl) ⟨7654064, by rfl⟩ : syracuseStep 40821677 = 15308129) B15308129
theorem B255999 : Blo 255820 255999 := bstep (se 1 (by rfl) ⟨191999, by rfl⟩ : syracuseStep 255999 = 383999) B383999
theorem B976967 : Blo 255820 976967 := bstep (se 1 (by rfl) ⟨732725, by rfl⟩ : syracuseStep 976967 = 1465451) B1465451
theorem B256719 : Blo 255820 256719 := bstep (se 1 (by rfl) ⟨192539, by rfl⟩ : syracuseStep 256719 = 385079) B385079
theorem B18804919 : Blo 255820 18804919 := bstep (se 1 (by rfl) ⟨14103689, by rfl⟩ : syracuseStep 18804919 = 28207379) B28207379
theorem B587255 : Blo 255820 587255 := bstep (se 1 (by rfl) ⟨440441, by rfl⟩ : syracuseStep 587255 = 880883) B880883
theorem B3964697 : Blo 255820 3964697 := bstep (se 2 (by rfl) ⟨1486761, by rfl⟩ : syracuseStep 3964697 = 2973523) B2973523
theorem B25073225 : Blo 255820 25073225 := bstep (se 2 (by rfl) ⟨9402459, by rfl⟩ : syracuseStep 25073225 = 18804919) B18804919
theorem B442111 : Blo 255820 442111 := bstep (se 1 (by rfl) ⟨331583, by rfl⟩ : syracuseStep 442111 = 663167) B663167
theorem B27214451 : Blo 255820 27214451 := bstep (se 1 (by rfl) ⟨20410838, by rfl⟩ : syracuseStep 27214451 = 40821677) B40821677
theorem B2643131 : Blo 255820 2643131 := bstep (se 1 (by rfl) ⟨1982348, by rfl⟩ : syracuseStep 2643131 = 3964697) B3964697
theorem B1235263 : Blo 255820 1235263 := bstep (se 1 (by rfl) ⟨926447, by rfl⟩ : syracuseStep 1235263 = 1852895) B1852895
theorem B51632927 : Blo 255820 51632927 := bstep (se 1 (by rfl) ⟨38724695, by rfl⟩ : syracuseStep 51632927 = 77449391) B77449391
theorem B22797227 : Blo 255820 22797227 := bstep (se 1 (by rfl) ⟨17097920, by rfl⟩ : syracuseStep 22797227 = 34195841) B34195841
theorem B581687 : Blo 255820 581687 := bstep (se 1 (by rfl) ⟨436265, by rfl⟩ : syracuseStep 581687 = 872531) B872531
theorem B1566013 : Blo 255820 1566013 := bstep (se 3 (by rfl) ⟨293627, by rfl⟩ : syracuseStep 1566013 = 587255) B587255
theorem B388127 : Blo 255820 388127 := bstep (se 1 (by rfl) ⟨291095, by rfl⟩ : syracuseStep 388127 = 582191) B582191
theorem B651311 : Blo 255820 651311 := bstep (se 1 (by rfl) ⟨488483, by rfl⟩ : syracuseStep 651311 = 976967) B976967
theorem B16715483 : Blo 255820 16715483 := bstep (se 1 (by rfl) ⟨12536612, by rfl⟩ : syracuseStep 16715483 = 25073225) B25073225
theorem B434207 : Blo 255820 434207 := bstep (se 1 (by rfl) ⟨325655, by rfl⟩ : syracuseStep 434207 = 651311) B651311
theorem B1647017 : Blo 255820 1647017 := bstep (se 2 (by rfl) ⟨617631, by rfl⟩ : syracuseStep 1647017 = 1235263) B1235263
theorem B34421951 : Blo 255820 34421951 := bstep (se 1 (by rfl) ⟨25816463, by rfl⟩ : syracuseStep 34421951 = 51632927) B51632927
theorem B18142967 : Blo 255820 18142967 := bstep (se 1 (by rfl) ⟨13607225, by rfl⟩ : syracuseStep 18142967 = 27214451) B27214451
theorem B2088017 : Blo 255820 2088017 := bstep (se 2 (by rfl) ⟨783006, by rfl⟩ : syracuseStep 2088017 = 1566013) B1566013
theorem B1762087 : Blo 255820 1762087 := bstep (se 1 (by rfl) ⟨1321565, by rfl⟩ : syracuseStep 1762087 = 2643131) B2643131
theorem B15198151 : Blo 255820 15198151 := bstep (se 1 (by rfl) ⟨11398613, by rfl⟩ : syracuseStep 15198151 = 22797227) B22797227
theorem B387791 : Blo 255820 387791 := bstep (se 1 (by rfl) ⟨290843, by rfl⟩ : syracuseStep 387791 = 581687) B581687
theorem B258751 : Blo 255820 258751 := bstep (se 1 (by rfl) ⟨194063, by rfl⟩ : syracuseStep 258751 = 388127) B388127
theorem B589481 : Blo 255820 589481 := bstep (se 2 (by rfl) ⟨221055, by rfl⟩ : syracuseStep 589481 = 442111) B442111
theorem B11143655 : Blo 255820 11143655 := bstep (se 1 (by rfl) ⟨8357741, by rfl⟩ : syracuseStep 11143655 = 16715483) B16715483
theorem B22947967 : Blo 255820 22947967 := bstep (se 1 (by rfl) ⟨17210975, by rfl⟩ : syracuseStep 22947967 = 34421951) B34421951
theorem B20264201 : Blo 255820 20264201 := bstep (se 2 (by rfl) ⟨7599075, by rfl⟩ : syracuseStep 20264201 = 15198151) B15198151
theorem B48381245 : Blo 255820 48381245 := bstep (se 3 (by rfl) ⟨9071483, by rfl⟩ : syracuseStep 48381245 = 18142967) B18142967
theorem B1392011 : Blo 255820 1392011 := bstep (se 1 (by rfl) ⟨1044008, by rfl⟩ : syracuseStep 1392011 = 2088017) B2088017
theorem B1098011 : Blo 255820 1098011 := bstep (se 1 (by rfl) ⟨823508, by rfl⟩ : syracuseStep 1098011 = 1647017) B1647017
theorem B2349449 : Blo 255820 2349449 := bstep (se 2 (by rfl) ⟨881043, by rfl⟩ : syracuseStep 2349449 = 1762087) B1762087
theorem B289471 : Blo 255820 289471 := bstep (se 1 (by rfl) ⟨217103, by rfl⟩ : syracuseStep 289471 = 434207) B434207
theorem B258527 : Blo 255820 258527 := bstep (se 1 (by rfl) ⟨193895, by rfl⟩ : syracuseStep 258527 = 387791) B387791
theorem B392987 : Blo 255820 392987 := bstep (se 1 (by rfl) ⟨294740, by rfl⟩ : syracuseStep 392987 = 589481) B589481
theorem B122389157 : Blo 255820 122389157 := bstep (se 4 (by rfl) ⟨11473983, by rfl⟩ : syracuseStep 122389157 = 22947967) B22947967
theorem B13509467 : Blo 255820 13509467 := bstep (se 1 (by rfl) ⟨10132100, by rfl⟩ : syracuseStep 13509467 = 20264201) B20264201
theorem B32254163 : Blo 255820 32254163 := bstep (se 1 (by rfl) ⟨24190622, by rfl⟩ : syracuseStep 32254163 = 48381245) B48381245
theorem B928007 : Blo 255820 928007 := bstep (se 1 (by rfl) ⟨696005, by rfl⟩ : syracuseStep 928007 = 1392011) B1392011
theorem B732007 : Blo 255820 732007 := bstep (se 1 (by rfl) ⟨549005, by rfl⟩ : syracuseStep 732007 = 1098011) B1098011
theorem B7429103 : Blo 255820 7429103 := bstep (se 1 (by rfl) ⟨5571827, by rfl⟩ : syracuseStep 7429103 = 11143655) B11143655
theorem B385961 : Blo 255820 385961 := bstep (se 2 (by rfl) ⟨144735, by rfl⟩ : syracuseStep 385961 = 289471) B289471
theorem B1566299 : Blo 255820 1566299 := bstep (se 1 (by rfl) ⟨1174724, by rfl⟩ : syracuseStep 1566299 = 2349449) B2349449
theorem B261991 : Blo 255820 261991 := bstep (se 1 (by rfl) ⟨196493, by rfl⟩ : syracuseStep 261991 = 392987) B392987
theorem B81592771 : Blo 255820 81592771 := bstep (se 1 (by rfl) ⟨61194578, by rfl⟩ : syracuseStep 81592771 = 122389157) B122389157
theorem B4952735 : Blo 255820 4952735 := bstep (se 1 (by rfl) ⟨3714551, by rfl⟩ : syracuseStep 4952735 = 7429103) B7429103
theorem B21502775 : Blo 255820 21502775 := bstep (se 1 (by rfl) ⟨16127081, by rfl⟩ : syracuseStep 21502775 = 32254163) B32254163
theorem B349321 : Blo 255820 349321 := bstep (se 2 (by rfl) ⟨130995, by rfl⟩ : syracuseStep 349321 = 261991) B261991
theorem B976009 : Blo 255820 976009 := bstep (se 2 (by rfl) ⟨366003, by rfl⟩ : syracuseStep 976009 = 732007) B732007
theorem B9006311 : Blo 255820 9006311 := bstep (se 1 (by rfl) ⟨6754733, by rfl⟩ : syracuseStep 9006311 = 13509467) B13509467
theorem B257307 : Blo 255820 257307 := bstep (se 1 (by rfl) ⟨192980, by rfl⟩ : syracuseStep 257307 = 385961) B385961
theorem B1044199 : Blo 255820 1044199 := bstep (se 1 (by rfl) ⟨783149, by rfl⟩ : syracuseStep 1044199 = 1566299) B1566299
theorem B618671 : Blo 255820 618671 := bstep (se 1 (by rfl) ⟨464003, by rfl⟩ : syracuseStep 618671 = 928007) B928007
theorem B108790361 : Blo 255820 108790361 := bstep (se 2 (by rfl) ⟨40796385, by rfl⟩ : syracuseStep 108790361 = 81592771) B81592771
theorem B465761 : Blo 255820 465761 := bstep (se 2 (by rfl) ⟨174660, by rfl⟩ : syracuseStep 465761 = 349321) B349321
theorem B6004207 : Blo 255820 6004207 := bstep (se 1 (by rfl) ⟨4503155, by rfl⟩ : syracuseStep 6004207 = 9006311) B9006311
theorem B14335183 : Blo 255820 14335183 := bstep (se 1 (by rfl) ⟨10751387, by rfl⟩ : syracuseStep 14335183 = 21502775) B21502775
theorem B1392265 : Blo 255820 1392265 := bstep (se 2 (by rfl) ⟨522099, by rfl⟩ : syracuseStep 1392265 = 1044199) B1044199
theorem B412447 : Blo 255820 412447 := bstep (se 1 (by rfl) ⟨309335, by rfl⟩ : syracuseStep 412447 = 618671) B618671
theorem B1301345 : Blo 255820 1301345 := bstep (se 2 (by rfl) ⟨488004, by rfl⟩ : syracuseStep 1301345 = 976009) B976009
theorem B3301823 : Blo 255820 3301823 := bstep (se 1 (by rfl) ⟨2476367, by rfl⟩ : syracuseStep 3301823 = 4952735) B4952735
theorem B2201215 : Blo 255820 2201215 := bstep (se 1 (by rfl) ⟨1650911, by rfl⟩ : syracuseStep 2201215 = 3301823) B3301823
theorem B19113577 : Blo 255820 19113577 := bstep (se 2 (by rfl) ⟨7167591, by rfl⟩ : syracuseStep 19113577 = 14335183) B14335183
theorem B8005609 : Blo 255820 8005609 := bstep (se 2 (by rfl) ⟨3002103, by rfl⟩ : syracuseStep 8005609 = 6004207) B6004207
theorem B72526907 : Blo 255820 72526907 := bstep (se 1 (by rfl) ⟨54395180, by rfl⟩ : syracuseStep 72526907 = 108790361) B108790361
theorem B867563 : Blo 255820 867563 := bstep (se 1 (by rfl) ⟨650672, by rfl⟩ : syracuseStep 867563 = 1301345) B1301345
theorem B1856353 : Blo 255820 1856353 := bstep (se 2 (by rfl) ⟨696132, by rfl⟩ : syracuseStep 1856353 = 1392265) B1392265
theorem B549929 : Blo 255820 549929 := bstep (se 2 (by rfl) ⟨206223, by rfl⟩ : syracuseStep 549929 = 412447) B412447
theorem B1242029 : Blo 255820 1242029 := bstep (se 3 (by rfl) ⟨232880, by rfl⟩ : syracuseStep 1242029 = 465761) B465761
theorem B366619 : Blo 255820 366619 := bstep (se 1 (by rfl) ⟨274964, by rfl⟩ : syracuseStep 366619 = 549929) B549929
theorem B828019 : Blo 255820 828019 := bstep (se 1 (by rfl) ⟨621014, by rfl⟩ : syracuseStep 828019 = 1242029) B1242029
theorem B2475137 : Blo 255820 2475137 := bstep (se 2 (by rfl) ⟨928176, by rfl⟩ : syracuseStep 2475137 = 1856353) B1856353
theorem B48351271 : Blo 255820 48351271 := bstep (se 1 (by rfl) ⟨36263453, by rfl⟩ : syracuseStep 48351271 = 72526907) B72526907
theorem B2934953 : Blo 255820 2934953 := bstep (se 2 (by rfl) ⟨1100607, by rfl⟩ : syracuseStep 2934953 = 2201215) B2201215
theorem B578375 : Blo 255820 578375 := bstep (se 1 (by rfl) ⟨433781, by rfl⟩ : syracuseStep 578375 = 867563) B867563
theorem B10674145 : Blo 255820 10674145 := bstep (se 2 (by rfl) ⟨4002804, by rfl⟩ : syracuseStep 10674145 = 8005609) B8005609
theorem B101939077 : Blo 255820 101939077 := bstep (se 4 (by rfl) ⟨9556788, by rfl⟩ : syracuseStep 101939077 = 19113577) B19113577
theorem B14232193 : Blo 255820 14232193 := bstep (se 2 (by rfl) ⟨5337072, by rfl⟩ : syracuseStep 14232193 = 10674145) B10674145
theorem B64468361 : Blo 255820 64468361 := bstep (se 2 (by rfl) ⟨24175635, by rfl⟩ : syracuseStep 64468361 = 48351271) B48351271
theorem B6600365 : Blo 255820 6600365 := bstep (se 3 (by rfl) ⟨1237568, by rfl⟩ : syracuseStep 6600365 = 2475137) B2475137
theorem B1104025 : Blo 255820 1104025 := bstep (se 2 (by rfl) ⟨414009, by rfl⟩ : syracuseStep 1104025 = 828019) B828019
theorem B1956635 : Blo 255820 1956635 := bstep (se 1 (by rfl) ⟨1467476, by rfl⟩ : syracuseStep 1956635 = 2934953) B2934953
theorem B385583 : Blo 255820 385583 := bstep (se 1 (by rfl) ⟨289187, by rfl⟩ : syracuseStep 385583 = 578375) B578375
theorem B135918769 : Blo 255820 135918769 := bstep (se 2 (by rfl) ⟨50969538, by rfl⟩ : syracuseStep 135918769 = 101939077) B101939077
theorem B488825 : Blo 255820 488825 := bstep (se 2 (by rfl) ⟨183309, by rfl⟩ : syracuseStep 488825 = 366619) B366619
theorem B4400243 : Blo 255820 4400243 := bstep (se 1 (by rfl) ⟨3300182, by rfl⟩ : syracuseStep 4400243 = 6600365) B6600365
theorem B75905029 : Blo 255820 75905029 := bstep (se 4 (by rfl) ⟨7116096, by rfl⟩ : syracuseStep 75905029 = 14232193) B14232193
theorem B181225025 : Blo 255820 181225025 := bstep (se 2 (by rfl) ⟨67959384, by rfl⟩ : syracuseStep 181225025 = 135918769) B135918769
theorem B42978907 : Blo 255820 42978907 := bstep (se 1 (by rfl) ⟨32234180, by rfl⟩ : syracuseStep 42978907 = 64468361) B64468361
theorem B1304423 : Blo 255820 1304423 := bstep (se 1 (by rfl) ⟨978317, by rfl⟩ : syracuseStep 1304423 = 1956635) B1956635
theorem B257055 : Blo 255820 257055 := bstep (se 1 (by rfl) ⟨192791, by rfl⟩ : syracuseStep 257055 = 385583) B385583
theorem B1472033 : Blo 255820 1472033 := bstep (se 2 (by rfl) ⟨552012, by rfl⟩ : syracuseStep 1472033 = 1104025) B1104025
theorem B325883 : Blo 255820 325883 := bstep (se 1 (by rfl) ⟨244412, by rfl⟩ : syracuseStep 325883 = 488825) B488825
theorem B120816683 : Blo 255820 120816683 := bstep (se 1 (by rfl) ⟨90612512, by rfl⟩ : syracuseStep 120816683 = 181225025) B181225025
theorem B229220837 : Blo 255820 229220837 := bstep (se 4 (by rfl) ⟨21489453, by rfl⟩ : syracuseStep 229220837 = 42978907) B42978907
theorem B869021 : Blo 255820 869021 := bstep (se 3 (by rfl) ⟨162941, by rfl⟩ : syracuseStep 869021 = 325883) B325883
theorem B2933495 : Blo 255820 2933495 := bstep (se 1 (by rfl) ⟨2200121, by rfl⟩ : syracuseStep 2933495 = 4400243) B4400243
theorem B869615 : Blo 255820 869615 := bstep (se 1 (by rfl) ⟨652211, by rfl⟩ : syracuseStep 869615 = 1304423) B1304423
theorem B101206705 : Blo 255820 101206705 := bstep (se 2 (by rfl) ⟨37952514, by rfl⟩ : syracuseStep 101206705 = 75905029) B75905029
theorem B981355 : Blo 255820 981355 := bstep (se 1 (by rfl) ⟨736016, by rfl⟩ : syracuseStep 981355 = 1472033) B1472033
theorem B80544455 : Blo 255820 80544455 := bstep (se 1 (by rfl) ⟨60408341, by rfl⟩ : syracuseStep 80544455 = 120816683) B120816683
theorem B134942273 : Blo 255820 134942273 := bstep (se 2 (by rfl) ⟨50603352, by rfl⟩ : syracuseStep 134942273 = 101206705) B101206705
theorem B152813891 : Blo 255820 152813891 := bstep (se 1 (by rfl) ⟨114610418, by rfl⟩ : syracuseStep 152813891 = 229220837) B229220837
theorem B579347 : Blo 255820 579347 := bstep (se 1 (by rfl) ⟨434510, by rfl⟩ : syracuseStep 579347 = 869021) B869021
theorem B1955663 : Blo 255820 1955663 := bstep (se 1 (by rfl) ⟨1466747, by rfl⟩ : syracuseStep 1955663 = 2933495) B2933495
theorem B579743 : Blo 255820 579743 := bstep (se 1 (by rfl) ⟨434807, by rfl⟩ : syracuseStep 579743 = 869615) B869615
theorem B1308473 : Blo 255820 1308473 := bstep (se 2 (by rfl) ⟨490677, by rfl⟩ : syracuseStep 1308473 = 981355) B981355
theorem B101875927 : Blo 255820 101875927 := bstep (se 1 (by rfl) ⟨76406945, by rfl⟩ : syracuseStep 101875927 = 152813891) B152813891
theorem B89961515 : Blo 255820 89961515 := bstep (se 1 (by rfl) ⟨67471136, by rfl⟩ : syracuseStep 89961515 = 134942273) B134942273
theorem B872315 : Blo 255820 872315 := bstep (se 1 (by rfl) ⟨654236, by rfl⟩ : syracuseStep 872315 = 1308473) B1308473
theorem B53696303 : Blo 255820 53696303 := bstep (se 1 (by rfl) ⟨40272227, by rfl⟩ : syracuseStep 53696303 = 80544455) B80544455
theorem B386231 : Blo 255820 386231 := bstep (se 1 (by rfl) ⟨289673, by rfl⟩ : syracuseStep 386231 = 579347) B579347
theorem B1303775 : Blo 255820 1303775 := bstep (se 1 (by rfl) ⟨977831, by rfl⟩ : syracuseStep 1303775 = 1955663) B1955663
theorem B386495 : Blo 255820 386495 := bstep (se 1 (by rfl) ⟨289871, by rfl⟩ : syracuseStep 386495 = 579743) B579743
theorem B59974343 : Blo 255820 59974343 := bstep (se 1 (by rfl) ⟨44980757, by rfl⟩ : syracuseStep 59974343 = 89961515) B89961515
theorem B135834569 : Blo 255820 135834569 := bstep (se 2 (by rfl) ⟨50937963, by rfl⟩ : syracuseStep 135834569 = 101875927) B101875927
theorem B35797535 : Blo 255820 35797535 := bstep (se 1 (by rfl) ⟨26848151, by rfl⟩ : syracuseStep 35797535 = 53696303) B53696303
theorem B869183 : Blo 255820 869183 := bstep (se 1 (by rfl) ⟨651887, by rfl⟩ : syracuseStep 869183 = 1303775) B1303775
theorem B581543 : Blo 255820 581543 := bstep (se 1 (by rfl) ⟨436157, by rfl⟩ : syracuseStep 581543 = 872315) B872315
theorem B257487 : Blo 255820 257487 := bstep (se 1 (by rfl) ⟨193115, by rfl⟩ : syracuseStep 257487 = 386231) B386231
theorem B257663 : Blo 255820 257663 := bstep (se 1 (by rfl) ⟨193247, by rfl⟩ : syracuseStep 257663 = 386495) B386495
theorem B39982895 : Blo 255820 39982895 := bstep (se 1 (by rfl) ⟨29987171, by rfl⟩ : syracuseStep 39982895 = 59974343) B59974343
theorem B23865023 : Blo 255820 23865023 := bstep (se 1 (by rfl) ⟨17898767, by rfl⟩ : syracuseStep 23865023 = 35797535) B35797535
theorem B90556379 : Blo 255820 90556379 := bstep (se 1 (by rfl) ⟨67917284, by rfl⟩ : syracuseStep 90556379 = 135834569) B135834569
theorem B579455 : Blo 255820 579455 := bstep (se 1 (by rfl) ⟨434591, by rfl⟩ : syracuseStep 579455 = 869183) B869183
theorem B387695 : Blo 255820 387695 := bstep (se 1 (by rfl) ⟨290771, by rfl⟩ : syracuseStep 387695 = 581543) B581543
theorem B60370919 : Blo 255820 60370919 := bstep (se 1 (by rfl) ⟨45278189, by rfl⟩ : syracuseStep 60370919 = 90556379) B90556379
theorem B26655263 : Blo 255820 26655263 := bstep (se 1 (by rfl) ⟨19991447, by rfl⟩ : syracuseStep 26655263 = 39982895) B39982895
theorem B15910015 : Blo 255820 15910015 := bstep (se 1 (by rfl) ⟨11932511, by rfl⟩ : syracuseStep 15910015 = 23865023) B23865023
theorem B386303 : Blo 255820 386303 := bstep (se 1 (by rfl) ⟨289727, by rfl⟩ : syracuseStep 386303 = 579455) B579455
theorem B258463 : Blo 255820 258463 := bstep (se 1 (by rfl) ⟨193847, by rfl⟩ : syracuseStep 258463 = 387695) B387695
theorem B40247279 : Blo 255820 40247279 := bstep (se 1 (by rfl) ⟨30185459, by rfl⟩ : syracuseStep 40247279 = 60370919) B60370919
theorem B17770175 : Blo 255820 17770175 := bstep (se 1 (by rfl) ⟨13327631, by rfl⟩ : syracuseStep 17770175 = 26655263) B26655263
theorem B21213353 : Blo 255820 21213353 := bstep (se 2 (by rfl) ⟨7955007, by rfl⟩ : syracuseStep 21213353 = 15910015) B15910015
theorem B257535 : Blo 255820 257535 := bstep (se 1 (by rfl) ⟨193151, by rfl⟩ : syracuseStep 257535 = 386303) B386303
theorem B11846783 : Blo 255820 11846783 := bstep (se 1 (by rfl) ⟨8885087, by rfl⟩ : syracuseStep 11846783 = 17770175) B17770175
theorem B14142235 : Blo 255820 14142235 := bstep (se 1 (by rfl) ⟨10606676, by rfl⟩ : syracuseStep 14142235 = 21213353) B21213353
theorem B26831519 : Blo 255820 26831519 := bstep (se 1 (by rfl) ⟨20123639, by rfl⟩ : syracuseStep 26831519 = 40247279) B40247279
theorem B31591421 : Blo 255820 31591421 := bstep (se 3 (by rfl) ⟨5923391, by rfl⟩ : syracuseStep 31591421 = 11846783) B11846783
theorem B18856313 : Blo 255820 18856313 := bstep (se 2 (by rfl) ⟨7071117, by rfl⟩ : syracuseStep 18856313 = 14142235) B14142235
theorem B17887679 : Blo 255820 17887679 := bstep (se 1 (by rfl) ⟨13415759, by rfl⟩ : syracuseStep 17887679 = 26831519) B26831519
theorem B12570875 : Blo 255820 12570875 := bstep (se 1 (by rfl) ⟨9428156, by rfl⟩ : syracuseStep 12570875 = 18856313) B18856313
theorem B21060947 : Blo 255820 21060947 := bstep (se 1 (by rfl) ⟨15795710, by rfl⟩ : syracuseStep 21060947 = 31591421) B31591421
theorem B11925119 : Blo 255820 11925119 := bstep (se 1 (by rfl) ⟨8943839, by rfl⟩ : syracuseStep 11925119 = 17887679) B17887679
theorem B14040631 : Blo 255820 14040631 := bstep (se 1 (by rfl) ⟨10530473, by rfl⟩ : syracuseStep 14040631 = 21060947) B21060947
theorem B7950079 : Blo 255820 7950079 := bstep (se 1 (by rfl) ⟨5962559, by rfl⟩ : syracuseStep 7950079 = 11925119) B11925119
theorem B8380583 : Blo 255820 8380583 := bstep (se 1 (by rfl) ⟨6285437, by rfl⟩ : syracuseStep 8380583 = 12570875) B12570875
theorem B18720841 : Blo 255820 18720841 := bstep (se 2 (by rfl) ⟨7020315, by rfl⟩ : syracuseStep 18720841 = 14040631) B14040631
theorem B10600105 : Blo 255820 10600105 := bstep (se 2 (by rfl) ⟨3975039, by rfl⟩ : syracuseStep 10600105 = 7950079) B7950079
theorem B5587055 : Blo 255820 5587055 := bstep (se 1 (by rfl) ⟨4190291, by rfl⟩ : syracuseStep 5587055 = 8380583) B8380583
theorem B14133473 : Blo 255820 14133473 := bstep (se 2 (by rfl) ⟨5300052, by rfl⟩ : syracuseStep 14133473 = 10600105) B10600105
theorem B3724703 : Blo 255820 3724703 := bstep (se 1 (by rfl) ⟨2793527, by rfl⟩ : syracuseStep 3724703 = 5587055) B5587055
theorem B24961121 : Blo 255820 24961121 := bstep (se 2 (by rfl) ⟨9360420, by rfl⟩ : syracuseStep 24961121 = 18720841) B18720841
theorem B9422315 : Blo 255820 9422315 := bstep (se 1 (by rfl) ⟨7066736, by rfl⟩ : syracuseStep 9422315 = 14133473) B14133473
theorem B2483135 : Blo 255820 2483135 := bstep (se 1 (by rfl) ⟨1862351, by rfl⟩ : syracuseStep 2483135 = 3724703) B3724703
theorem B16640747 : Blo 255820 16640747 := bstep (se 1 (by rfl) ⟨12480560, by rfl⟩ : syracuseStep 16640747 = 24961121) B24961121
theorem B1655423 : Blo 255820 1655423 := bstep (se 1 (by rfl) ⟨1241567, by rfl⟩ : syracuseStep 1655423 = 2483135) B2483135
theorem B11093831 : Blo 255820 11093831 := bstep (se 1 (by rfl) ⟨8320373, by rfl⟩ : syracuseStep 11093831 = 16640747) B16640747
theorem B6281543 : Blo 255820 6281543 := bstep (se 1 (by rfl) ⟨4711157, by rfl⟩ : syracuseStep 6281543 = 9422315) B9422315
theorem B1103615 : Blo 255820 1103615 := bstep (se 1 (by rfl) ⟨827711, by rfl⟩ : syracuseStep 1103615 = 1655423) B1655423
theorem B7395887 : Blo 255820 7395887 := bstep (se 1 (by rfl) ⟨5546915, by rfl⟩ : syracuseStep 7395887 = 11093831) B11093831
theorem B4187695 : Blo 255820 4187695 := bstep (se 1 (by rfl) ⟨3140771, by rfl⟩ : syracuseStep 4187695 = 6281543) B6281543
theorem B5583593 : Blo 255820 5583593 := bstep (se 2 (by rfl) ⟨2093847, by rfl⟩ : syracuseStep 5583593 = 4187695) B4187695
theorem B735743 : Blo 255820 735743 := bstep (se 1 (by rfl) ⟨551807, by rfl⟩ : syracuseStep 735743 = 1103615) B1103615
theorem B4930591 : Blo 255820 4930591 := bstep (se 1 (by rfl) ⟨3697943, by rfl⟩ : syracuseStep 4930591 = 7395887) B7395887
theorem B3722395 : Blo 255820 3722395 := bstep (se 1 (by rfl) ⟨2791796, by rfl⟩ : syracuseStep 3722395 = 5583593) B5583593
theorem B6574121 : Blo 255820 6574121 := bstep (se 2 (by rfl) ⟨2465295, by rfl⟩ : syracuseStep 6574121 = 4930591) B4930591
theorem B1961981 : Blo 255820 1961981 := bstep (se 3 (by rfl) ⟨367871, by rfl⟩ : syracuseStep 1961981 = 735743) B735743
theorem B4963193 : Blo 255820 4963193 := bstep (se 2 (by rfl) ⟨1861197, by rfl⟩ : syracuseStep 4963193 = 3722395) B3722395
theorem B4382747 : Blo 255820 4382747 := bstep (se 1 (by rfl) ⟨3287060, by rfl⟩ : syracuseStep 4382747 = 6574121) B6574121
theorem B1307987 : Blo 255820 1307987 := bstep (se 1 (by rfl) ⟨980990, by rfl⟩ : syracuseStep 1307987 = 1961981) B1961981
theorem B2921831 : Blo 255820 2921831 := bstep (se 1 (by rfl) ⟨2191373, by rfl⟩ : syracuseStep 2921831 = 4382747) B4382747
theorem B871991 : Blo 255820 871991 := bstep (se 1 (by rfl) ⟨653993, by rfl⟩ : syracuseStep 871991 = 1307987) B1307987
theorem B3308795 : Blo 255820 3308795 := bstep (se 1 (by rfl) ⟨2481596, by rfl⟩ : syracuseStep 3308795 = 4963193) B4963193
theorem B2205863 : Blo 255820 2205863 := bstep (se 1 (by rfl) ⟨1654397, by rfl⟩ : syracuseStep 2205863 = 3308795) B3308795
theorem B1947887 : Blo 255820 1947887 := bstep (se 1 (by rfl) ⟨1460915, by rfl⟩ : syracuseStep 1947887 = 2921831) B2921831
theorem B581327 : Blo 255820 581327 := bstep (se 1 (by rfl) ⟨435995, by rfl⟩ : syracuseStep 581327 = 871991) B871991
theorem B1298591 : Blo 255820 1298591 := bstep (se 1 (by rfl) ⟨973943, by rfl⟩ : syracuseStep 1298591 = 1947887) B1947887
theorem B387551 : Blo 255820 387551 := bstep (se 1 (by rfl) ⟨290663, by rfl⟩ : syracuseStep 387551 = 581327) B581327
theorem B1470575 : Blo 255820 1470575 := bstep (se 1 (by rfl) ⟨1102931, by rfl⟩ : syracuseStep 1470575 = 2205863) B2205863
theorem B865727 : Blo 255820 865727 := bstep (se 1 (by rfl) ⟨649295, by rfl⟩ : syracuseStep 865727 = 1298591) B1298591
theorem B258367 : Blo 255820 258367 := bstep (se 1 (by rfl) ⟨193775, by rfl⟩ : syracuseStep 258367 = 387551) B387551
theorem B980383 : Blo 255820 980383 := bstep (se 1 (by rfl) ⟨735287, by rfl⟩ : syracuseStep 980383 = 1470575) B1470575
theorem B577151 : Blo 255820 577151 := bstep (se 1 (by rfl) ⟨432863, by rfl⟩ : syracuseStep 577151 = 865727) B865727
theorem B1307177 : Blo 255820 1307177 := bstep (se 2 (by rfl) ⟨490191, by rfl⟩ : syracuseStep 1307177 = 980383) B980383
theorem B871451 : Blo 255820 871451 := bstep (se 1 (by rfl) ⟨653588, by rfl⟩ : syracuseStep 871451 = 1307177) B1307177
theorem B384767 : Blo 255820 384767 := bstep (se 1 (by rfl) ⟨288575, by rfl⟩ : syracuseStep 384767 = 577151) B577151
theorem B580967 : Blo 255820 580967 := bstep (se 1 (by rfl) ⟨435725, by rfl⟩ : syracuseStep 580967 = 871451) B871451
theorem B256511 : Blo 255820 256511 := bstep (se 1 (by rfl) ⟨192383, by rfl⟩ : syracuseStep 256511 = 384767) B384767
theorem B387311 : Blo 255820 387311 := bstep (se 1 (by rfl) ⟨290483, by rfl⟩ : syracuseStep 387311 = 580967) B580967
theorem B258207 : Blo 255820 258207 := bstep (se 1 (by rfl) ⟨193655, by rfl⟩ : syracuseStep 258207 = 387311) B387311

theorem C0 (j : ℕ) (h1 : 63955 ≤ j) (h2 : j ≤ 64654) : Blo 255820 (4 * j + 3) := by
  interval_cases j
  · exact B255823
  · exact B255827
  · exact B255831
  · exact B255835
  · exact B255839
  · exact B255843
  · exact B255847
  · exact B255851
  · exact B255855
  · exact B255859
  · exact B255863
  · exact B255867
  · exact B255871
  · exact B255875
  · exact B255879
  · exact B255883
  · exact B255887
  · exact B255891
  · exact B255895
  · exact B255899
  · exact B255903
  · exact B255907
  · exact B255911
  · exact B255915
  · exact B255919
  · exact B255923
  · exact B255927
  · exact B255931
  · exact B255935
  · exact B255939
  · exact B255943
  · exact B255947
  · exact B255951
  · exact B255955
  · exact B255959
  · exact B255963
  · exact B255967
  · exact B255971
  · exact B255975
  · exact B255979
  · exact B255983
  · exact B255987
  · exact B255991
  · exact B255995
  · exact B255999
  · exact B256003
  · exact B256007
  · exact B256011
  · exact B256015
  · exact B256019
  · exact B256023
  · exact B256027
  · exact B256031
  · exact B256035
  · exact B256039
  · exact B256043
  · exact B256047
  · exact B256051
  · exact B256055
  · exact B256059
  · exact B256063
  · exact B256067
  · exact B256071
  · exact B256075
  · exact B256079
  · exact B256083
  · exact B256087
  · exact B256091
  · exact B256095
  · exact B256099
  · exact B256103
  · exact B256107
  · exact B256111
  · exact B256115
  · exact B256119
  · exact B256123
  · exact B256127
  · exact B256131
  · exact B256135
  · exact B256139
  · exact B256143
  · exact B256147
  · exact B256151
  · exact B256155
  · exact B256159
  · exact B256163
  · exact B256167
  · exact B256171
  · exact B256175
  · exact B256179
  · exact B256183
  · exact B256187
  · exact B256191
  · exact B256195
  · exact B256199
  · exact B256203
  · exact B256207
  · exact B256211
  · exact B256215
  · exact B256219
  · exact B256223
  · exact B256227
  · exact B256231
  · exact B256235
  · exact B256239
  · exact B256243
  · exact B256247
  · exact B256251
  · exact B256255
  · exact B256259
  · exact B256263
  · exact B256267
  · exact B256271
  · exact B256275
  · exact B256279
  · exact B256283
  · exact B256287
  · exact B256291
  · exact B256295
  · exact B256299
  · exact B256303
  · exact B256307
  · exact B256311
  · exact B256315
  · exact B256319
  · exact B256323
  · exact B256327
  · exact B256331
  · exact B256335
  · exact B256339
  · exact B256343
  · exact B256347
  · exact B256351
  · exact B256355
  · exact B256359
  · exact B256363
  · exact B256367
  · exact B256371
  · exact B256375
  · exact B256379
  · exact B256383
  · exact B256387
  · exact B256391
  · exact B256395
  · exact B256399
  · exact B256403
  · exact B256407
  · exact B256411
  · exact B256415
  · exact B256419
  · exact B256423
  · exact B256427
  · exact B256431
  · exact B256435
  · exact B256439
  · exact B256443
  · exact B256447
  · exact B256451
  · exact B256455
  · exact B256459
  · exact B256463
  · exact B256467
  · exact B256471
  · exact B256475
  · exact B256479
  · exact B256483
  · exact B256487
  · exact B256491
  · exact B256495
  · exact B256499
  · exact B256503
  · exact B256507
  · exact B256511
  · exact B256515
  · exact B256519
  · exact B256523
  · exact B256527
  · exact B256531
  · exact B256535
  · exact B256539
  · exact B256543
  · exact B256547
  · exact B256551
  · exact B256555
  · exact B256559
  · exact B256563
  · exact B256567
  · exact B256571
  · exact B256575
  · exact B256579
  · exact B256583
  · exact B256587
  · exact B256591
  · exact B256595
  · exact B256599
  · exact B256603
  · exact B256607
  · exact B256611
  · exact B256615
  · exact B256619
  · exact B256623
  · exact B256627
  · exact B256631
  · exact B256635
  · exact B256639
  · exact B256643
  · exact B256647
  · exact B256651
  · exact B256655
  · exact B256659
  · exact B256663
  · exact B256667
  · exact B256671
  · exact B256675
  · exact B256679
  · exact B256683
  · exact B256687
  · exact B256691
  · exact B256695
  · exact B256699
  · exact B256703
  · exact B256707
  · exact B256711
  · exact B256715
  · exact B256719
  · exact B256723
  · exact B256727
  · exact B256731
  · exact B256735
  · exact B256739
  · exact B256743
  · exact B256747
  · exact B256751
  · exact B256755
  · exact B256759
  · exact B256763
  · exact B256767
  · exact B256771
  · exact B256775
  · exact B256779
  · exact B256783
  · exact B256787
  · exact B256791
  · exact B256795
  · exact B256799
  · exact B256803
  · exact B256807
  · exact B256811
  · exact B256815
  · exact B256819
  · exact B256823
  · exact B256827
  · exact B256831
  · exact B256835
  · exact B256839
  · exact B256843
  · exact B256847
  · exact B256851
  · exact B256855
  · exact B256859
  · exact B256863
  · exact B256867
  · exact B256871
  · exact B256875
  · exact B256879
  · exact B256883
  · exact B256887
  · exact B256891
  · exact B256895
  · exact B256899
  · exact B256903
  · exact B256907
  · exact B256911
  · exact B256915
  · exact B256919
  · exact B256923
  · exact B256927
  · exact B256931
  · exact B256935
  · exact B256939
  · exact B256943
  · exact B256947
  · exact B256951
  · exact B256955
  · exact B256959
  · exact B256963
  · exact B256967
  · exact B256971
  · exact B256975
  · exact B256979
  · exact B256983
  · exact B256987
  · exact B256991
  · exact B256995
  · exact B256999
  · exact B257003
  · exact B257007
  · exact B257011
  · exact B257015
  · exact B257019
  · exact B257023
  · exact B257027
  · exact B257031
  · exact B257035
  · exact B257039
  · exact B257043
  · exact B257047
  · exact B257051
  · exact B257055
  · exact B257059
  · exact B257063
  · exact B257067
  · exact B257071
  · exact B257075
  · exact B257079
  · exact B257083
  · exact B257087
  · exact B257091
  · exact B257095
  · exact B257099
  · exact B257103
  · exact B257107
  · exact B257111
  · exact B257115
  · exact B257119
  · exact B257123
  · exact B257127
  · exact B257131
  · exact B257135
  · exact B257139
  · exact B257143
  · exact B257147
  · exact B257151
  · exact B257155
  · exact B257159
  · exact B257163
  · exact B257167
  · exact B257171
  · exact B257175
  · exact B257179
  · exact B257183
  · exact B257187
  · exact B257191
  · exact B257195
  · exact B257199
  · exact B257203
  · exact B257207
  · exact B257211
  · exact B257215
  · exact B257219
  · exact B257223
  · exact B257227
  · exact B257231
  · exact B257235
  · exact B257239
  · exact B257243
  · exact B257247
  · exact B257251
  · exact B257255
  · exact B257259
  · exact B257263
  · exact B257267
  · exact B257271
  · exact B257275
  · exact B257279
  · exact B257283
  · exact B257287
  · exact B257291
  · exact B257295
  · exact B257299
  · exact B257303
  · exact B257307
  · exact B257311
  · exact B257315
  · exact B257319
  · exact B257323
  · exact B257327
  · exact B257331
  · exact B257335
  · exact B257339
  · exact B257343
  · exact B257347
  · exact B257351
  · exact B257355
  · exact B257359
  · exact B257363
  · exact B257367
  · exact B257371
  · exact B257375
  · exact B257379
  · exact B257383
  · exact B257387
  · exact B257391
  · exact B257395
  · exact B257399
  · exact B257403
  · exact B257407
  · exact B257411
  · exact B257415
  · exact B257419
  · exact B257423
  · exact B257427
  · exact B257431
  · exact B257435
  · exact B257439
  · exact B257443
  · exact B257447
  · exact B257451
  · exact B257455
  · exact B257459
  · exact B257463
  · exact B257467
  · exact B257471
  · exact B257475
  · exact B257479
  · exact B257483
  · exact B257487
  · exact B257491
  · exact B257495
  · exact B257499
  · exact B257503
  · exact B257507
  · exact B257511
  · exact B257515
  · exact B257519
  · exact B257523
  · exact B257527
  · exact B257531
  · exact B257535
  · exact B257539
  · exact B257543
  · exact B257547
  · exact B257551
  · exact B257555
  · exact B257559
  · exact B257563
  · exact B257567
  · exact B257571
  · exact B257575
  · exact B257579
  · exact B257583
  · exact B257587
  · exact B257591
  · exact B257595
  · exact B257599
  · exact B257603
  · exact B257607
  · exact B257611
  · exact B257615
  · exact B257619
  · exact B257623
  · exact B257627
  · exact B257631
  · exact B257635
  · exact B257639
  · exact B257643
  · exact B257647
  · exact B257651
  · exact B257655
  · exact B257659
  · exact B257663
  · exact B257667
  · exact B257671
  · exact B257675
  · exact B257679
  · exact B257683
  · exact B257687
  · exact B257691
  · exact B257695
  · exact B257699
  · exact B257703
  · exact B257707
  · exact B257711
  · exact B257715
  · exact B257719
  · exact B257723
  · exact B257727
  · exact B257731
  · exact B257735
  · exact B257739
  · exact B257743
  · exact B257747
  · exact B257751
  · exact B257755
  · exact B257759
  · exact B257763
  · exact B257767
  · exact B257771
  · exact B257775
  · exact B257779
  · exact B257783
  · exact B257787
  · exact B257791
  · exact B257795
  · exact B257799
  · exact B257803
  · exact B257807
  · exact B257811
  · exact B257815
  · exact B257819
  · exact B257823
  · exact B257827
  · exact B257831
  · exact B257835
  · exact B257839
  · exact B257843
  · exact B257847
  · exact B257851
  · exact B257855
  · exact B257859
  · exact B257863
  · exact B257867
  · exact B257871
  · exact B257875
  · exact B257879
  · exact B257883
  · exact B257887
  · exact B257891
  · exact B257895
  · exact B257899
  · exact B257903
  · exact B257907
  · exact B257911
  · exact B257915
  · exact B257919
  · exact B257923
  · exact B257927
  · exact B257931
  · exact B257935
  · exact B257939
  · exact B257943
  · exact B257947
  · exact B257951
  · exact B257955
  · exact B257959
  · exact B257963
  · exact B257967
  · exact B257971
  · exact B257975
  · exact B257979
  · exact B257983
  · exact B257987
  · exact B257991
  · exact B257995
  · exact B257999
  · exact B258003
  · exact B258007
  · exact B258011
  · exact B258015
  · exact B258019
  · exact B258023
  · exact B258027
  · exact B258031
  · exact B258035
  · exact B258039
  · exact B258043
  · exact B258047
  · exact B258051
  · exact B258055
  · exact B258059
  · exact B258063
  · exact B258067
  · exact B258071
  · exact B258075
  · exact B258079
  · exact B258083
  · exact B258087
  · exact B258091
  · exact B258095
  · exact B258099
  · exact B258103
  · exact B258107
  · exact B258111
  · exact B258115
  · exact B258119
  · exact B258123
  · exact B258127
  · exact B258131
  · exact B258135
  · exact B258139
  · exact B258143
  · exact B258147
  · exact B258151
  · exact B258155
  · exact B258159
  · exact B258163
  · exact B258167
  · exact B258171
  · exact B258175
  · exact B258179
  · exact B258183
  · exact B258187
  · exact B258191
  · exact B258195
  · exact B258199
  · exact B258203
  · exact B258207
  · exact B258211
  · exact B258215
  · exact B258219
  · exact B258223
  · exact B258227
  · exact B258231
  · exact B258235
  · exact B258239
  · exact B258243
  · exact B258247
  · exact B258251
  · exact B258255
  · exact B258259
  · exact B258263
  · exact B258267
  · exact B258271
  · exact B258275
  · exact B258279
  · exact B258283
  · exact B258287
  · exact B258291
  · exact B258295
  · exact B258299
  · exact B258303
  · exact B258307
  · exact B258311
  · exact B258315
  · exact B258319
  · exact B258323
  · exact B258327
  · exact B258331
  · exact B258335
  · exact B258339
  · exact B258343
  · exact B258347
  · exact B258351
  · exact B258355
  · exact B258359
  · exact B258363
  · exact B258367
  · exact B258371
  · exact B258375
  · exact B258379
  · exact B258383
  · exact B258387
  · exact B258391
  · exact B258395
  · exact B258399
  · exact B258403
  · exact B258407
  · exact B258411
  · exact B258415
  · exact B258419
  · exact B258423
  · exact B258427
  · exact B258431
  · exact B258435
  · exact B258439
  · exact B258443
  · exact B258447
  · exact B258451
  · exact B258455
  · exact B258459
  · exact B258463
  · exact B258467
  · exact B258471
  · exact B258475
  · exact B258479
  · exact B258483
  · exact B258487
  · exact B258491
  · exact B258495
  · exact B258499
  · exact B258503
  · exact B258507
  · exact B258511
  · exact B258515
  · exact B258519
  · exact B258523
  · exact B258527
  · exact B258531
  · exact B258535
  · exact B258539
  · exact B258543
  · exact B258547
  · exact B258551
  · exact B258555
  · exact B258559
  · exact B258563
  · exact B258567
  · exact B258571
  · exact B258575
  · exact B258579
  · exact B258583
  · exact B258587
  · exact B258591
  · exact B258595
  · exact B258599
  · exact B258603
  · exact B258607
  · exact B258611
  · exact B258615
  · exact B258619

theorem C1 (j : ℕ) (h1 : 64655 ≤ j) (h2 : j ≤ 64954) : Blo 255820 (4 * j + 3) := by
  interval_cases j
  · exact B258623
  · exact B258627
  · exact B258631
  · exact B258635
  · exact B258639
  · exact B258643
  · exact B258647
  · exact B258651
  · exact B258655
  · exact B258659
  · exact B258663
  · exact B258667
  · exact B258671
  · exact B258675
  · exact B258679
  · exact B258683
  · exact B258687
  · exact B258691
  · exact B258695
  · exact B258699
  · exact B258703
  · exact B258707
  · exact B258711
  · exact B258715
  · exact B258719
  · exact B258723
  · exact B258727
  · exact B258731
  · exact B258735
  · exact B258739
  · exact B258743
  · exact B258747
  · exact B258751
  · exact B258755
  · exact B258759
  · exact B258763
  · exact B258767
  · exact B258771
  · exact B258775
  · exact B258779
  · exact B258783
  · exact B258787
  · exact B258791
  · exact B258795
  · exact B258799
  · exact B258803
  · exact B258807
  · exact B258811
  · exact B258815
  · exact B258819
  · exact B258823
  · exact B258827
  · exact B258831
  · exact B258835
  · exact B258839
  · exact B258843
  · exact B258847
  · exact B258851
  · exact B258855
  · exact B258859
  · exact B258863
  · exact B258867
  · exact B258871
  · exact B258875
  · exact B258879
  · exact B258883
  · exact B258887
  · exact B258891
  · exact B258895
  · exact B258899
  · exact B258903
  · exact B258907
  · exact B258911
  · exact B258915
  · exact B258919
  · exact B258923
  · exact B258927
  · exact B258931
  · exact B258935
  · exact B258939
  · exact B258943
  · exact B258947
  · exact B258951
  · exact B258955
  · exact B258959
  · exact B258963
  · exact B258967
  · exact B258971
  · exact B258975
  · exact B258979
  · exact B258983
  · exact B258987
  · exact B258991
  · exact B258995
  · exact B258999
  · exact B259003
  · exact B259007
  · exact B259011
  · exact B259015
  · exact B259019
  · exact B259023
  · exact B259027
  · exact B259031
  · exact B259035
  · exact B259039
  · exact B259043
  · exact B259047
  · exact B259051
  · exact B259055
  · exact B259059
  · exact B259063
  · exact B259067
  · exact B259071
  · exact B259075
  · exact B259079
  · exact B259083
  · exact B259087
  · exact B259091
  · exact B259095
  · exact B259099
  · exact B259103
  · exact B259107
  · exact B259111
  · exact B259115
  · exact B259119
  · exact B259123
  · exact B259127
  · exact B259131
  · exact B259135
  · exact B259139
  · exact B259143
  · exact B259147
  · exact B259151
  · exact B259155
  · exact B259159
  · exact B259163
  · exact B259167
  · exact B259171
  · exact B259175
  · exact B259179
  · exact B259183
  · exact B259187
  · exact B259191
  · exact B259195
  · exact B259199
  · exact B259203
  · exact B259207
  · exact B259211
  · exact B259215
  · exact B259219
  · exact B259223
  · exact B259227
  · exact B259231
  · exact B259235
  · exact B259239
  · exact B259243
  · exact B259247
  · exact B259251
  · exact B259255
  · exact B259259
  · exact B259263
  · exact B259267
  · exact B259271
  · exact B259275
  · exact B259279
  · exact B259283
  · exact B259287
  · exact B259291
  · exact B259295
  · exact B259299
  · exact B259303
  · exact B259307
  · exact B259311
  · exact B259315
  · exact B259319
  · exact B259323
  · exact B259327
  · exact B259331
  · exact B259335
  · exact B259339
  · exact B259343
  · exact B259347
  · exact B259351
  · exact B259355
  · exact B259359
  · exact B259363
  · exact B259367
  · exact B259371
  · exact B259375
  · exact B259379
  · exact B259383
  · exact B259387
  · exact B259391
  · exact B259395
  · exact B259399
  · exact B259403
  · exact B259407
  · exact B259411
  · exact B259415
  · exact B259419
  · exact B259423
  · exact B259427
  · exact B259431
  · exact B259435
  · exact B259439
  · exact B259443
  · exact B259447
  · exact B259451
  · exact B259455
  · exact B259459
  · exact B259463
  · exact B259467
  · exact B259471
  · exact B259475
  · exact B259479
  · exact B259483
  · exact B259487
  · exact B259491
  · exact B259495
  · exact B259499
  · exact B259503
  · exact B259507
  · exact B259511
  · exact B259515
  · exact B259519
  · exact B259523
  · exact B259527
  · exact B259531
  · exact B259535
  · exact B259539
  · exact B259543
  · exact B259547
  · exact B259551
  · exact B259555
  · exact B259559
  · exact B259563
  · exact B259567
  · exact B259571
  · exact B259575
  · exact B259579
  · exact B259583
  · exact B259587
  · exact B259591
  · exact B259595
  · exact B259599
  · exact B259603
  · exact B259607
  · exact B259611
  · exact B259615
  · exact B259619
  · exact B259623
  · exact B259627
  · exact B259631
  · exact B259635
  · exact B259639
  · exact B259643
  · exact B259647
  · exact B259651
  · exact B259655
  · exact B259659
  · exact B259663
  · exact B259667
  · exact B259671
  · exact B259675
  · exact B259679
  · exact B259683
  · exact B259687
  · exact B259691
  · exact B259695
  · exact B259699
  · exact B259703
  · exact B259707
  · exact B259711
  · exact B259715
  · exact B259719
  · exact B259723
  · exact B259727
  · exact B259731
  · exact B259735
  · exact B259739
  · exact B259743
  · exact B259747
  · exact B259751
  · exact B259755
  · exact B259759
  · exact B259763
  · exact B259767
  · exact B259771
  · exact B259775
  · exact B259779
  · exact B259783
  · exact B259787
  · exact B259791
  · exact B259795
  · exact B259799
  · exact B259803
  · exact B259807
  · exact B259811
  · exact B259815
  · exact B259819

theorem solution (m : ℕ) (hlo : 255820 ≤ m) (hhi : m ≤ 259820) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 63955 ≤ j := by omega
    have hj2 : j ≤ 64954 := by omega
    have hb : Blo 255820 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 64655 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
