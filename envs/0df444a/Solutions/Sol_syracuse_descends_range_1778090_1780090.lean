-- Prove2me | solution 1 for syracuse_descends_range_1778090_1780090
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:43:50.928369+00:00
-- url     : https://prove2.me/submissions/3f91e150-859d-45f3-9409-d0280517221d

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


theorem B3424277 : Blo 1778090 3424277 := bbase (se 6 (by rfl) ⟨80256, by rfl⟩ : syracuseStep 3424277 = 160513) (by norm_num)
theorem B3801109 : Blo 1778090 3801109 := bbase (se 6 (by rfl) ⟨89088, by rfl⟩ : syracuseStep 3801109 = 178177) (by norm_num)
theorem B6758437 : Blo 1778090 6758437 := bbase (se 4 (by rfl) ⟨633603, by rfl⟩ : syracuseStep 6758437 = 1267207) (by norm_num)
theorem B4505645 : Blo 1778090 4505645 := bbase (se 3 (by rfl) ⟨844808, by rfl⟩ : syracuseStep 4505645 = 1689617) (by norm_num)
theorem B2252873 : Blo 1778090 2252873 := bbase (se 2 (by rfl) ⟨844827, by rfl⟩ : syracuseStep 2252873 = 1689655) (by norm_num)
theorem B6004853 : Blo 1778090 6004853 := bbase (se 5 (by rfl) ⟨281477, by rfl⟩ : syracuseStep 6004853 = 562955) (by norm_num)
theorem B1802413 : Blo 1778090 1802413 := bbase (se 3 (by rfl) ⟨337952, by rfl⟩ : syracuseStep 1802413 = 675905) (by norm_num)
theorem B6758741 : Blo 1778090 6758741 := bbase (se 10 (by rfl) ⟨9900, by rfl⟩ : syracuseStep 6758741 = 19801) (by norm_num)
theorem B9011573 : Blo 1778090 9011573 := bbase (se 5 (by rfl) ⟨422417, by rfl⟩ : syracuseStep 9011573 = 844835) (by norm_num)
theorem B3801485 : Blo 1778090 3801485 := bbase (se 3 (by rfl) ⟨712778, by rfl⟩ : syracuseStep 3801485 = 1425557) (by norm_num)
theorem B2531749 : Blo 1778090 2531749 := bbase (se 4 (by rfl) ⟨237351, by rfl⟩ : syracuseStep 2531749 = 474703) (by norm_num)
theorem B1802693 : Blo 1778090 1802693 := bbase (se 4 (by rfl) ⟨169002, by rfl⟩ : syracuseStep 1802693 = 338005) (by norm_num)
theorem B6414805 : Blo 1778090 6414805 := bbase (se 7 (by rfl) ⟨75173, by rfl⟩ : syracuseStep 6414805 = 150347) (by norm_num)
theorem B12829205 : Blo 1778090 12829205 := bbase (se 6 (by rfl) ⟨300684, by rfl⟩ : syracuseStep 12829205 = 601369) (by norm_num)
theorem B6005285 : Blo 1778090 6005285 := bbase (se 4 (by rfl) ⟨562995, by rfl⟩ : syracuseStep 6005285 = 1125991) (by norm_num)
theorem B11395637 : Blo 1778090 11395637 := bbase (se 5 (by rfl) ⟨534170, by rfl⟩ : syracuseStep 11395637 = 1068341) (by norm_num)
theorem B3375749 : Blo 1778090 3375749 := bbase (se 4 (by rfl) ⟨316476, by rfl⟩ : syracuseStep 3375749 = 632953) (by norm_num)
theorem B4276901 : Blo 1778090 4276901 := bbase (se 4 (by rfl) ⟨400959, by rfl⟩ : syracuseStep 4276901 = 801919) (by norm_num)
theorem B4875013 : Blo 1778090 4875013 := bbase (se 4 (by rfl) ⟨457032, by rfl⟩ : syracuseStep 4875013 = 914065) (by norm_num)
theorem B6415109 : Blo 1778090 6415109 := bbase (se 4 (by rfl) ⟨601416, by rfl⟩ : syracuseStep 6415109 = 1202833) (by norm_num)
theorem B3375893 : Blo 1778090 3375893 := bbase (se 6 (by rfl) ⟨79122, by rfl⟩ : syracuseStep 3375893 = 158245) (by norm_num)
theorem B9003797 : Blo 1778090 9003797 := bbase (se 6 (by rfl) ⟨211026, by rfl⟩ : syracuseStep 9003797 = 422053) (by norm_num)
theorem B13697909 : Blo 1778090 13697909 := bbase (se 5 (by rfl) ⟨642089, by rfl⟩ : syracuseStep 13697909 = 1284179) (by norm_num)
theorem B6005717 : Blo 1778090 6005717 := bbase (se 7 (by rfl) ⟨70379, by rfl⟩ : syracuseStep 6005717 = 140759) (by norm_num)
theorem B2532341 : Blo 1778090 2532341 := bbase (se 5 (by rfl) ⟨118703, by rfl⟩ : syracuseStep 2532341 = 237407) (by norm_num)
theorem B2057257 : Blo 1778090 2057257 := bbase (se 2 (by rfl) ⟨771471, by rfl⟩ : syracuseStep 2057257 = 1542943) (by norm_num)
theorem B3376181 : Blo 1778090 3376181 := bbase (se 5 (by rfl) ⟨158258, by rfl⟩ : syracuseStep 3376181 = 316517) (by norm_num)
theorem B2532421 : Blo 1778090 2532421 := bbase (se 4 (by rfl) ⟨237414, by rfl⟩ : syracuseStep 2532421 = 474829) (by norm_num)
theorem B2532541 : Blo 1778090 2532541 := bbase (se 3 (by rfl) ⟨474851, by rfl⟩ : syracuseStep 2532541 = 949703) (by norm_num)
theorem B3376333 : Blo 1778090 3376333 := bbase (se 3 (by rfl) ⟨633062, by rfl⟩ : syracuseStep 3376333 = 1266125) (by norm_num)
theorem B2532637 : Blo 1778090 2532637 := bbase (se 3 (by rfl) ⟨474869, by rfl⟩ : syracuseStep 2532637 = 949739) (by norm_num)
theorem B1926433 : Blo 1778090 1926433 := bbase (se 2 (by rfl) ⟨722412, by rfl⟩ : syracuseStep 1926433 = 1444825) (by norm_num)
theorem B4941125 : Blo 1778090 4941125 := bbase (se 4 (by rfl) ⟨463230, by rfl⟩ : syracuseStep 4941125 = 926461) (by norm_num)
theorem B6006149 : Blo 1778090 6006149 := bbase (se 4 (by rfl) ⟨563076, by rfl⟩ : syracuseStep 6006149 = 1126153) (by norm_num)
theorem B2000353 : Blo 1778090 2000353 := bbase (se 2 (by rfl) ⟨750132, by rfl⟩ : syracuseStep 2000353 = 1500265) (by norm_num)
theorem B3376637 : Blo 1778090 3376637 := bbase (se 3 (by rfl) ⟨633119, by rfl⟩ : syracuseStep 3376637 = 1266239) (by norm_num)
theorem B2000389 : Blo 1778090 2000389 := bbase (se 4 (by rfl) ⟨187536, by rfl⟩ : syracuseStep 2000389 = 375073) (by norm_num)
theorem B3204613 : Blo 1778090 3204613 := bbase (se 4 (by rfl) ⟨300432, by rfl⟩ : syracuseStep 3204613 = 600865) (by norm_num)
theorem B1951241 : Blo 1778090 1951241 := bbase (se 2 (by rfl) ⟨731715, by rfl⟩ : syracuseStep 1951241 = 1463431) (by norm_num)
theorem B4810261 : Blo 1778090 4810261 := bbase (se 6 (by rfl) ⟨112740, by rfl⟩ : syracuseStep 4810261 = 225481) (by norm_num)
theorem B2000425 : Blo 1778090 2000425 := bbase (se 2 (by rfl) ⟨750159, by rfl⟩ : syracuseStep 2000425 = 1500319) (by norm_num)
theorem B5408309 : Blo 1778090 5408309 := bbase (se 5 (by rfl) ⟨253514, by rfl⟩ : syracuseStep 5408309 = 507029) (by norm_num)
theorem B2000461 : Blo 1778090 2000461 := bbase (se 3 (by rfl) ⟨375086, by rfl⟩ : syracuseStep 2000461 = 750173) (by norm_num)
theorem B6170213 : Blo 1778090 6170213 := bbase (se 4 (by rfl) ⟨578457, by rfl⟩ : syracuseStep 6170213 = 1156915) (by norm_num)
theorem B2000497 : Blo 1778090 2000497 := bbase (se 2 (by rfl) ⟨750186, by rfl⟩ : syracuseStep 2000497 = 1500373) (by norm_num)
theorem B2000533 : Blo 1778090 2000533 := bbase (se 6 (by rfl) ⟨46887, by rfl⟩ : syracuseStep 2000533 = 93775) (by norm_num)
theorem B2000569 : Blo 1778090 2000569 := bbase (se 2 (by rfl) ⟨750213, by rfl⟩ : syracuseStep 2000569 = 1500427) (by norm_num)
theorem B10823381 : Blo 1778090 10823381 := bbase (se 7 (by rfl) ⟨126836, by rfl⟩ : syracuseStep 10823381 = 253673) (by norm_num)
theorem B2000605 : Blo 1778090 2000605 := bbase (se 3 (by rfl) ⟨375113, by rfl⟩ : syracuseStep 2000605 = 750227) (by norm_num)
theorem B2000641 : Blo 1778090 2000641 := bbase (se 2 (by rfl) ⟨750240, by rfl⟩ : syracuseStep 2000641 = 1500481) (by norm_num)
theorem B2533133 : Blo 1778090 2533133 := bbase (se 3 (by rfl) ⟨474962, by rfl⟩ : syracuseStep 2533133 = 949925) (by norm_num)
theorem B2000677 : Blo 1778090 2000677 := bbase (se 4 (by rfl) ⟨187563, by rfl⟩ : syracuseStep 2000677 = 375127) (by norm_num)
theorem B6006581 : Blo 1778090 6006581 := bbase (se 5 (by rfl) ⟨281558, by rfl⟩ : syracuseStep 6006581 = 563117) (by norm_num)
theorem B2000713 : Blo 1778090 2000713 := bbase (se 2 (by rfl) ⟨750267, by rfl⟩ : syracuseStep 2000713 = 1500535) (by norm_num)
theorem B2000749 : Blo 1778090 2000749 := bbase (se 3 (by rfl) ⟨375140, by rfl⟩ : syracuseStep 2000749 = 750281) (by norm_num)
theorem B2000785 : Blo 1778090 2000785 := bbase (se 2 (by rfl) ⟨750294, by rfl⟩ : syracuseStep 2000785 = 1500589) (by norm_num)
theorem B1804205 : Blo 1778090 1804205 := bbase (se 3 (by rfl) ⟨338288, by rfl⟩ : syracuseStep 1804205 = 676577) (by norm_num)
theorem B2000821 : Blo 1778090 2000821 := bbase (se 5 (by rfl) ⟨93788, by rfl⟩ : syracuseStep 2000821 = 187577) (by norm_num)
theorem B2000857 : Blo 1778090 2000857 := bbase (se 2 (by rfl) ⟨750321, by rfl⟩ : syracuseStep 2000857 = 1500643) (by norm_num)
theorem B1804253 : Blo 1778090 1804253 := bbase (se 3 (by rfl) ⟨338297, by rfl⟩ : syracuseStep 1804253 = 676595) (by norm_num)
theorem B2000893 : Blo 1778090 2000893 := bbase (se 3 (by rfl) ⟨375167, by rfl⟩ : syracuseStep 2000893 = 750335) (by norm_num)
theorem B2000929 : Blo 1778090 2000929 := bbase (se 2 (by rfl) ⟨750348, by rfl⟩ : syracuseStep 2000929 = 1500697) (by norm_num)
theorem B7211045 : Blo 1778090 7211045 := bbase (se 4 (by rfl) ⟨676035, by rfl⟩ : syracuseStep 7211045 = 1352071) (by norm_num)
theorem B9005093 : Blo 1778090 9005093 := bbase (se 4 (by rfl) ⟨844227, by rfl⟩ : syracuseStep 9005093 = 1688455) (by norm_num)
theorem B4565045 : Blo 1778090 4565045 := bbase (se 5 (by rfl) ⟨213986, by rfl⟩ : syracuseStep 4565045 = 427973) (by norm_num)
theorem B15206453 : Blo 1778090 15206453 := bbase (se 5 (by rfl) ⟨712802, by rfl⟩ : syracuseStep 15206453 = 1425605) (by norm_num)
theorem B2000965 : Blo 1778090 2000965 := bbase (se 4 (by rfl) ⟨187590, by rfl⟩ : syracuseStep 2000965 = 375181) (by norm_num)
theorem B6940741 : Blo 1778090 6940741 := bbase (se 4 (by rfl) ⟨650694, by rfl⟩ : syracuseStep 6940741 = 1301389) (by norm_num)
theorem B3852373 : Blo 1778090 3852373 := bbase (se 8 (by rfl) ⟨22572, by rfl⟩ : syracuseStep 3852373 = 45145) (by norm_num)
theorem B2001001 : Blo 1778090 2001001 := bbase (se 2 (by rfl) ⟨750375, by rfl⟩ : syracuseStep 2001001 = 1500751) (by norm_num)
theorem B2001037 : Blo 1778090 2001037 := bbase (se 3 (by rfl) ⟨375194, by rfl⟩ : syracuseStep 2001037 = 750389) (by norm_num)
theorem B2001073 : Blo 1778090 2001073 := bbase (se 2 (by rfl) ⟨750402, by rfl⟩ : syracuseStep 2001073 = 1500805) (by norm_num)
theorem B2001109 : Blo 1778090 2001109 := bbase (se 7 (by rfl) ⟨23450, by rfl⟩ : syracuseStep 2001109 = 46901) (by norm_num)
theorem B6007013 : Blo 1778090 6007013 := bbase (se 4 (by rfl) ⟨563157, by rfl⟩ : syracuseStep 6007013 = 1126315) (by norm_num)
theorem B3000557 : Blo 1778090 3000557 := bbase (se 3 (by rfl) ⟨562604, by rfl⟩ : syracuseStep 3000557 = 1125209) (by norm_num)
theorem B3377389 : Blo 1778090 3377389 := bbase (se 3 (by rfl) ⟨633260, by rfl⟩ : syracuseStep 3377389 = 1266521) (by norm_num)
theorem B2001145 : Blo 1778090 2001145 := bbase (se 2 (by rfl) ⟨750429, by rfl⟩ : syracuseStep 2001145 = 1500859) (by norm_num)
theorem B2001181 : Blo 1778090 2001181 := bbase (se 3 (by rfl) ⟨375221, by rfl⟩ : syracuseStep 2001181 = 750443) (by norm_num)
theorem B4057381 : Blo 1778090 4057381 := bbase (se 4 (by rfl) ⟨380379, by rfl⟩ : syracuseStep 4057381 = 760759) (by norm_num)
theorem B3205421 : Blo 1778090 3205421 := bbase (se 3 (by rfl) ⟨601016, by rfl⟩ : syracuseStep 3205421 = 1202033) (by norm_num)
theorem B3852589 : Blo 1778090 3852589 := bbase (se 3 (by rfl) ⟨722360, by rfl⟩ : syracuseStep 3852589 = 1444721) (by norm_num)
theorem B7596341 : Blo 1778090 7596341 := bbase (se 5 (by rfl) ⟨356078, by rfl⟩ : syracuseStep 7596341 = 712157) (by norm_num)
theorem B2533685 : Blo 1778090 2533685 := bbase (se 5 (by rfl) ⟨118766, by rfl⟩ : syracuseStep 2533685 = 237533) (by norm_num)
theorem B2001217 : Blo 1778090 2001217 := bbase (se 2 (by rfl) ⟨750456, by rfl⟩ : syracuseStep 2001217 = 1500913) (by norm_num)
theorem B2001253 : Blo 1778090 2001253 := bbase (se 4 (by rfl) ⟨187617, by rfl⟩ : syracuseStep 2001253 = 375235) (by norm_num)
theorem B3000685 : Blo 1778090 3000685 := bbase (se 3 (by rfl) ⟨562628, by rfl⟩ : syracuseStep 3000685 = 1125257) (by norm_num)
theorem B9619829 : Blo 1778090 9619829 := bbase (se 5 (by rfl) ⟨450929, by rfl⟩ : syracuseStep 9619829 = 901859) (by norm_num)
theorem B10135925 : Blo 1778090 10135925 := bbase (se 5 (by rfl) ⟨475121, by rfl⟩ : syracuseStep 10135925 = 950243) (by norm_num)
theorem B3377533 : Blo 1778090 3377533 := bbase (se 3 (by rfl) ⟨633287, by rfl⟩ : syracuseStep 3377533 = 1266575) (by norm_num)
theorem B2001289 : Blo 1778090 2001289 := bbase (se 2 (by rfl) ⟨750483, by rfl⟩ : syracuseStep 2001289 = 1500967) (by norm_num)
theorem B2001325 : Blo 1778090 2001325 := bbase (se 3 (by rfl) ⟨375248, by rfl⟩ : syracuseStep 2001325 = 750497) (by norm_num)
theorem B3000773 : Blo 1778090 3000773 := bbase (se 4 (by rfl) ⟨281322, by rfl⟩ : syracuseStep 3000773 = 562645) (by norm_num)
theorem B2001361 : Blo 1778090 2001361 := bbase (se 2 (by rfl) ⟨750510, by rfl⟩ : syracuseStep 2001361 = 1501021) (by norm_num)
theorem B10127861 : Blo 1778090 10127861 := bbase (se 5 (by rfl) ⟨474743, by rfl⟩ : syracuseStep 10127861 = 949487) (by norm_num)
theorem B2001397 : Blo 1778090 2001397 := bbase (se 5 (by rfl) ⟨93815, by rfl⟩ : syracuseStep 2001397 = 187631) (by norm_num)
theorem B2001433 : Blo 1778090 2001433 := bbase (se 2 (by rfl) ⟨750537, by rfl⟩ : syracuseStep 2001433 = 1501075) (by norm_num)
theorem B3377693 : Blo 1778090 3377693 := bbase (se 3 (by rfl) ⟨633317, by rfl⟩ : syracuseStep 3377693 = 1266635) (by norm_num)
theorem B2001469 : Blo 1778090 2001469 := bbase (se 3 (by rfl) ⟨375275, by rfl⟩ : syracuseStep 2001469 = 750551) (by norm_num)
theorem B3000901 : Blo 1778090 3000901 := bbase (se 4 (by rfl) ⟨281334, by rfl⟩ : syracuseStep 3000901 = 562669) (by norm_num)
theorem B2001505 : Blo 1778090 2001505 := bbase (se 2 (by rfl) ⟨750564, by rfl⟩ : syracuseStep 2001505 = 1501129) (by norm_num)
theorem B13511285 : Blo 1778090 13511285 := bbase (se 5 (by rfl) ⟨633341, by rfl⟩ : syracuseStep 13511285 = 1266683) (by norm_num)
theorem B2001541 : Blo 1778090 2001541 := bbase (se 4 (by rfl) ⟨187644, by rfl⟩ : syracuseStep 2001541 = 375289) (by norm_num)
theorem B6007445 : Blo 1778090 6007445 := bbase (se 6 (by rfl) ⟨140799, by rfl⟩ : syracuseStep 6007445 = 281599) (by norm_num)
theorem B3000989 : Blo 1778090 3000989 := bbase (se 3 (by rfl) ⟨562685, by rfl⟩ : syracuseStep 3000989 = 1125371) (by norm_num)
theorem B2001577 : Blo 1778090 2001577 := bbase (se 2 (by rfl) ⟨750591, by rfl⟩ : syracuseStep 2001577 = 1501183) (by norm_num)
theorem B3377837 : Blo 1778090 3377837 := bbase (se 3 (by rfl) ⟨633344, by rfl⟩ : syracuseStep 3377837 = 1266689) (by norm_num)
theorem B11553461 : Blo 1778090 11553461 := bbase (se 5 (by rfl) ⟨541568, by rfl⟩ : syracuseStep 11553461 = 1083137) (by norm_num)
theorem B8661701 : Blo 1778090 8661701 := bbase (se 4 (by rfl) ⟨812034, by rfl⟩ : syracuseStep 8661701 = 1624069) (by norm_num)
theorem B2001613 : Blo 1778090 2001613 := bbase (se 3 (by rfl) ⟨375302, by rfl⟩ : syracuseStep 2001613 = 750605) (by norm_num)
theorem B2706149 : Blo 1778090 2706149 := bbase (se 4 (by rfl) ⟨253701, by rfl⟩ : syracuseStep 2706149 = 507403) (by norm_num)
theorem B2001649 : Blo 1778090 2001649 := bbase (se 2 (by rfl) ⟨750618, by rfl⟩ : syracuseStep 2001649 = 1501237) (by norm_num)
theorem B2001685 : Blo 1778090 2001685 := bbase (se 6 (by rfl) ⟨46914, by rfl⟩ : syracuseStep 2001685 = 93829) (by norm_num)
theorem B3001117 : Blo 1778090 3001117 := bbase (se 3 (by rfl) ⟨562709, by rfl⟩ : syracuseStep 3001117 = 1125419) (by norm_num)
theorem B6753077 : Blo 1778090 6753077 := bbase (se 5 (by rfl) ⟨316550, by rfl⟩ : syracuseStep 6753077 = 633101) (by norm_num)
theorem B2001721 : Blo 1778090 2001721 := bbase (se 2 (by rfl) ⟨750645, by rfl⟩ : syracuseStep 2001721 = 1501291) (by norm_num)
theorem B2001757 : Blo 1778090 2001757 := bbase (se 3 (by rfl) ⟨375329, by rfl⟩ : syracuseStep 2001757 = 750659) (by norm_num)
theorem B3001205 : Blo 1778090 3001205 := bbase (se 5 (by rfl) ⟨140681, by rfl⟩ : syracuseStep 3001205 = 281363) (by norm_num)
theorem B2001793 : Blo 1778090 2001793 := bbase (se 2 (by rfl) ⟨750672, by rfl⟩ : syracuseStep 2001793 = 1501345) (by norm_num)
theorem B2001829 : Blo 1778090 2001829 := bbase (se 4 (by rfl) ⟨187671, by rfl⟩ : syracuseStep 2001829 = 375343) (by norm_num)
theorem B2001865 : Blo 1778090 2001865 := bbase (se 2 (by rfl) ⟨750699, by rfl⟩ : syracuseStep 2001865 = 1501399) (by norm_num)
theorem B3378125 : Blo 1778090 3378125 := bbase (se 3 (by rfl) ⟨633398, by rfl⟩ : syracuseStep 3378125 = 1266797) (by norm_num)
theorem B5065685 : Blo 1778090 5065685 := bbase (se 7 (by rfl) ⟨59363, by rfl⟩ : syracuseStep 5065685 = 118727) (by norm_num)
theorem B4000733 : Blo 1778090 4000733 := bbase (se 3 (by rfl) ⟨750137, by rfl⟩ : syracuseStep 4000733 = 1500275) (by norm_num)
theorem B2001901 : Blo 1778090 2001901 := bbase (se 3 (by rfl) ⟨375356, by rfl⟩ : syracuseStep 2001901 = 750713) (by norm_num)
theorem B3001333 : Blo 1778090 3001333 := bbase (se 5 (by rfl) ⟨140687, by rfl⟩ : syracuseStep 3001333 = 281375) (by norm_num)
theorem B2001937 : Blo 1778090 2001937 := bbase (se 2 (by rfl) ⟨750726, by rfl⟩ : syracuseStep 2001937 = 1501453) (by norm_num)
theorem B13503509 : Blo 1778090 13503509 := bbase (se 6 (by rfl) ⟨316488, by rfl⟩ : syracuseStep 13503509 = 632977) (by norm_num)
theorem B4000805 : Blo 1778090 4000805 := bbase (se 4 (by rfl) ⟨375075, by rfl⟩ : syracuseStep 4000805 = 750151) (by norm_num)
theorem B2534437 : Blo 1778090 2534437 := bbase (se 4 (by rfl) ⟨237603, by rfl⟩ : syracuseStep 2534437 = 475207) (by norm_num)
theorem B2001973 : Blo 1778090 2001973 := bbase (se 5 (by rfl) ⟨93842, by rfl⟩ : syracuseStep 2001973 = 187685) (by norm_num)
theorem B3001421 : Blo 1778090 3001421 := bbase (se 3 (by rfl) ⟨562766, by rfl⟩ : syracuseStep 3001421 = 1125533) (by norm_num)
theorem B6753365 : Blo 1778090 6753365 := bbase (se 8 (by rfl) ⟨39570, by rfl⟩ : syracuseStep 6753365 = 79141) (by norm_num)
theorem B2002009 : Blo 1778090 2002009 := bbase (se 2 (by rfl) ⟨750753, by rfl⟩ : syracuseStep 2002009 = 1501507) (by norm_num)
theorem B3378277 : Blo 1778090 3378277 := bbase (se 4 (by rfl) ⟨316713, by rfl⟩ : syracuseStep 3378277 = 633427) (by norm_num)
theorem B4000877 : Blo 1778090 4000877 := bbase (se 3 (by rfl) ⟨750164, by rfl⟩ : syracuseStep 4000877 = 1500329) (by norm_num)
theorem B2002045 : Blo 1778090 2002045 := bbase (se 3 (by rfl) ⟨375383, by rfl⟩ : syracuseStep 2002045 = 750767) (by norm_num)
theorem B2002081 : Blo 1778090 2002081 := bbase (se 2 (by rfl) ⟨750780, by rfl⟩ : syracuseStep 2002081 = 1501561) (by norm_num)
theorem B4000949 : Blo 1778090 4000949 := bbase (se 5 (by rfl) ⟨187544, by rfl⟩ : syracuseStep 4000949 = 375089) (by norm_num)
theorem B2002117 : Blo 1778090 2002117 := bbase (se 4 (by rfl) ⟨187698, by rfl⟩ : syracuseStep 2002117 = 375397) (by norm_num)
theorem B3001549 : Blo 1778090 3001549 := bbase (se 3 (by rfl) ⟨562790, by rfl⟩ : syracuseStep 3001549 = 1125581) (by norm_num)
theorem B2002153 : Blo 1778090 2002153 := bbase (se 2 (by rfl) ⟨750807, by rfl⟩ : syracuseStep 2002153 = 1501615) (by norm_num)
theorem B4001021 : Blo 1778090 4001021 := bbase (se 3 (by rfl) ⟨750191, by rfl⟩ : syracuseStep 4001021 = 1500383) (by norm_num)
theorem B2002189 : Blo 1778090 2002189 := bbase (se 3 (by rfl) ⟨375410, by rfl⟩ : syracuseStep 2002189 = 750821) (by norm_num)
theorem B3001637 : Blo 1778090 3001637 := bbase (se 4 (by rfl) ⟨281403, by rfl⟩ : syracuseStep 3001637 = 562807) (by norm_num)
theorem B2002225 : Blo 1778090 2002225 := bbase (se 2 (by rfl) ⟨750834, by rfl⟩ : syracuseStep 2002225 = 1501669) (by norm_num)
theorem B3042613 : Blo 1778090 3042613 := bbase (se 5 (by rfl) ⟨142622, by rfl⟩ : syracuseStep 3042613 = 285245) (by norm_num)
theorem B7212341 : Blo 1778090 7212341 := bbase (se 5 (by rfl) ⟨338078, by rfl⟩ : syracuseStep 7212341 = 676157) (by norm_num)
theorem B9006389 : Blo 1778090 9006389 := bbase (se 5 (by rfl) ⟨422174, by rfl⟩ : syracuseStep 9006389 = 844349) (by norm_num)
theorem B4500805 : Blo 1778090 4500805 := bbase (se 4 (by rfl) ⟨421950, by rfl⟩ : syracuseStep 4500805 = 843901) (by norm_num)
theorem B4001093 : Blo 1778090 4001093 := bbase (se 4 (by rfl) ⟨375102, by rfl⟩ : syracuseStep 4001093 = 750205) (by norm_num)
theorem B2002261 : Blo 1778090 2002261 := bbase (se 11 (by rfl) ⟨1466, by rfl⟩ : syracuseStep 2002261 = 2933) (by norm_num)
theorem B5696885 : Blo 1778090 5696885 := bbase (se 5 (by rfl) ⟨267041, by rfl⟩ : syracuseStep 5696885 = 534083) (by norm_num)
theorem B2002297 : Blo 1778090 2002297 := bbase (se 2 (by rfl) ⟨750861, by rfl⟩ : syracuseStep 2002297 = 1501723) (by norm_num)
theorem B4001165 : Blo 1778090 4001165 := bbase (se 3 (by rfl) ⟨750218, by rfl⟩ : syracuseStep 4001165 = 1500437) (by norm_num)
theorem B3378581 : Blo 1778090 3378581 := bbase (se 6 (by rfl) ⟨79185, by rfl⟩ : syracuseStep 3378581 = 158371) (by norm_num)
theorem B2002333 : Blo 1778090 2002333 := bbase (se 3 (by rfl) ⟨375437, by rfl⟩ : syracuseStep 2002333 = 750875) (by norm_num)
theorem B3001765 : Blo 1778090 3001765 := bbase (se 4 (by rfl) ⟨281415, by rfl⟩ : syracuseStep 3001765 = 562831) (by norm_num)
theorem B4500917 : Blo 1778090 4500917 := bbase (se 5 (by rfl) ⟨210980, by rfl⟩ : syracuseStep 4500917 = 421961) (by norm_num)
theorem B2002369 : Blo 1778090 2002369 := bbase (se 2 (by rfl) ⟨750888, by rfl⟩ : syracuseStep 2002369 = 1501777) (by norm_num)
theorem B4001237 : Blo 1778090 4001237 := bbase (se 7 (by rfl) ⟨46889, by rfl⟩ : syracuseStep 4001237 = 93779) (by norm_num)
theorem B2002405 : Blo 1778090 2002405 := bbase (se 4 (by rfl) ⟨187725, by rfl⟩ : syracuseStep 2002405 = 375451) (by norm_num)
theorem B3001853 : Blo 1778090 3001853 := bbase (se 3 (by rfl) ⟨562847, by rfl⟩ : syracuseStep 3001853 = 1125695) (by norm_num)
theorem B2002441 : Blo 1778090 2002441 := bbase (se 2 (by rfl) ⟨750915, by rfl⟩ : syracuseStep 2002441 = 1501831) (by norm_num)
theorem B10137109 : Blo 1778090 10137109 := bbase (se 6 (by rfl) ⟨237588, by rfl⟩ : syracuseStep 10137109 = 475177) (by norm_num)
theorem B4001309 : Blo 1778090 4001309 := bbase (se 3 (by rfl) ⟨750245, by rfl⟩ : syracuseStep 4001309 = 1500491) (by norm_num)
theorem B2002477 : Blo 1778090 2002477 := bbase (se 3 (by rfl) ⟨375464, by rfl⟩ : syracuseStep 2002477 = 750929) (by norm_num)
theorem B2002513 : Blo 1778090 2002513 := bbase (se 2 (by rfl) ⟨750942, by rfl⟩ : syracuseStep 2002513 = 1501885) (by norm_num)
theorem B4001381 : Blo 1778090 4001381 := bbase (se 4 (by rfl) ⟨375129, by rfl⟩ : syracuseStep 4001381 = 750259) (by norm_num)
theorem B4501109 : Blo 1778090 4501109 := bbase (se 5 (by rfl) ⟨210989, by rfl⟩ : syracuseStep 4501109 = 421979) (by norm_num)
theorem B2002549 : Blo 1778090 2002549 := bbase (se 5 (by rfl) ⟨93869, by rfl⟩ : syracuseStep 2002549 = 187739) (by norm_num)
theorem B3001981 : Blo 1778090 3001981 := bbase (se 3 (by rfl) ⟨562871, by rfl⟩ : syracuseStep 3001981 = 1125743) (by norm_num)
theorem B2002585 : Blo 1778090 2002585 := bbase (se 2 (by rfl) ⟨750969, by rfl⟩ : syracuseStep 2002585 = 1501939) (by norm_num)
theorem B4001453 : Blo 1778090 4001453 := bbase (se 3 (by rfl) ⟨750272, by rfl⟩ : syracuseStep 4001453 = 1500545) (by norm_num)
theorem B3002069 : Blo 1778090 3002069 := bbase (se 7 (by rfl) ⟨35180, by rfl⟩ : syracuseStep 3002069 = 70361) (by norm_num)
theorem B4001525 : Blo 1778090 4001525 := bbase (se 5 (by rfl) ⟨187571, by rfl⟩ : syracuseStep 4001525 = 375143) (by norm_num)
theorem B4001597 : Blo 1778090 4001597 := bbase (se 3 (by rfl) ⟨750299, by rfl⟩ : syracuseStep 4001597 = 1500599) (by norm_num)
theorem B3002197 : Blo 1778090 3002197 := bbase (se 9 (by rfl) ⟨8795, by rfl⟩ : syracuseStep 3002197 = 17591) (by norm_num)
theorem B4001669 : Blo 1778090 4001669 := bbase (se 4 (by rfl) ⟨375156, by rfl⟩ : syracuseStep 4001669 = 750313) (by norm_num)
theorem B3002285 : Blo 1778090 3002285 := bbase (se 3 (by rfl) ⟨562928, by rfl⟩ : syracuseStep 3002285 = 1125857) (by norm_num)
theorem B5410741 : Blo 1778090 5410741 := bbase (se 5 (by rfl) ⟨253628, by rfl⟩ : syracuseStep 5410741 = 507257) (by norm_num)
theorem B4501453 : Blo 1778090 4501453 := bbase (se 3 (by rfl) ⟨844022, by rfl⟩ : syracuseStep 4501453 = 1688045) (by norm_num)
theorem B4001741 : Blo 1778090 4001741 := bbase (se 3 (by rfl) ⟨750326, by rfl⟩ : syracuseStep 4001741 = 1500653) (by norm_num)
theorem B3043325 : Blo 1778090 3043325 := bbase (se 3 (by rfl) ⟨570623, by rfl⟩ : syracuseStep 3043325 = 1141247) (by norm_num)
theorem B4001813 : Blo 1778090 4001813 := bbase (se 6 (by rfl) ⟨93792, by rfl⟩ : syracuseStep 4001813 = 187585) (by norm_num)
theorem B2166809 : Blo 1778090 2166809 := bbase (se 2 (by rfl) ⟨812553, by rfl⟩ : syracuseStep 2166809 = 1625107) (by norm_num)
theorem B7598117 : Blo 1778090 7598117 := bbase (se 4 (by rfl) ⟨712323, by rfl⟩ : syracuseStep 7598117 = 1424647) (by norm_num)
theorem B3002413 : Blo 1778090 3002413 := bbase (se 3 (by rfl) ⟨562952, by rfl⟩ : syracuseStep 3002413 = 1125905) (by norm_num)
theorem B4501565 : Blo 1778090 4501565 := bbase (se 3 (by rfl) ⟨844043, by rfl⟩ : syracuseStep 4501565 = 1688087) (by norm_num)
theorem B3469373 : Blo 1778090 3469373 := bbase (se 3 (by rfl) ⟨650507, by rfl⟩ : syracuseStep 3469373 = 1301015) (by norm_num)
theorem B3608653 : Blo 1778090 3608653 := bbase (se 3 (by rfl) ⟨676622, by rfl⟩ : syracuseStep 3608653 = 1353245) (by norm_num)
theorem B5410901 : Blo 1778090 5410901 := bbase (se 8 (by rfl) ⟨31704, by rfl⟩ : syracuseStep 5410901 = 63409) (by norm_num)
theorem B4001885 : Blo 1778090 4001885 := bbase (se 3 (by rfl) ⟨750353, by rfl⟩ : syracuseStep 4001885 = 1500707) (by norm_num)
theorem B5066869 : Blo 1778090 5066869 := bbase (se 5 (by rfl) ⟨237509, by rfl⟩ : syracuseStep 5066869 = 475019) (by norm_num)
theorem B3002501 : Blo 1778090 3002501 := bbase (se 4 (by rfl) ⟨281484, by rfl⟩ : syracuseStep 3002501 = 562969) (by norm_num)
theorem B3379333 : Blo 1778090 3379333 := bbase (se 4 (by rfl) ⟨316812, by rfl⟩ : syracuseStep 3379333 = 633625) (by norm_num)
theorem B4059277 : Blo 1778090 4059277 := bbase (se 3 (by rfl) ⟨761114, by rfl⟩ : syracuseStep 4059277 = 1522229) (by norm_num)
theorem B3608717 : Blo 1778090 3608717 := bbase (se 3 (by rfl) ⟨676634, by rfl⟩ : syracuseStep 3608717 = 1353269) (by norm_num)
theorem B4001957 : Blo 1778090 4001957 := bbase (se 4 (by rfl) ⟨375183, by rfl⟩ : syracuseStep 4001957 = 750367) (by norm_num)
theorem B13693141 : Blo 1778090 13693141 := bbase (se 7 (by rfl) ⟨160466, by rfl⟩ : syracuseStep 13693141 = 320933) (by norm_num)
theorem B4272365 : Blo 1778090 4272365 := bbase (se 3 (by rfl) ⟨801068, by rfl⟩ : syracuseStep 4272365 = 1602137) (by norm_num)
theorem B4002029 : Blo 1778090 4002029 := bbase (se 3 (by rfl) ⟨750380, by rfl⟩ : syracuseStep 4002029 = 1500761) (by norm_num)
theorem B6754549 : Blo 1778090 6754549 := bbase (se 5 (by rfl) ⟨316619, by rfl⟩ : syracuseStep 6754549 = 633239) (by norm_num)
theorem B4501757 : Blo 1778090 4501757 := bbase (se 3 (by rfl) ⟨844079, by rfl⟩ : syracuseStep 4501757 = 1688159) (by norm_num)
theorem B3002629 : Blo 1778090 3002629 := bbase (se 4 (by rfl) ⟨281496, by rfl⟩ : syracuseStep 3002629 = 562993) (by norm_num)
theorem B7598357 : Blo 1778090 7598357 := bbase (se 6 (by rfl) ⟨178086, by rfl⟩ : syracuseStep 7598357 = 356173) (by norm_num)
theorem B5067029 : Blo 1778090 5067029 := bbase (se 6 (by rfl) ⟨118758, by rfl⟩ : syracuseStep 5067029 = 237517) (by norm_num)
theorem B4002101 : Blo 1778090 4002101 := bbase (se 5 (by rfl) ⟨187598, by rfl⟩ : syracuseStep 4002101 = 375197) (by norm_num)
theorem B13873493 : Blo 1778090 13873493 := bbase (se 10 (by rfl) ⟨20322, by rfl⟩ : syracuseStep 13873493 = 40645) (by norm_num)
theorem B3002717 : Blo 1778090 3002717 := bbase (se 3 (by rfl) ⟨563009, by rfl⟩ : syracuseStep 3002717 = 1126019) (by norm_num)
theorem B9613685 : Blo 1778090 9613685 := bbase (se 5 (by rfl) ⟨450641, by rfl⟩ : syracuseStep 9613685 = 901283) (by norm_num)
theorem B4002173 : Blo 1778090 4002173 := bbase (se 3 (by rfl) ⟨750407, by rfl⟩ : syracuseStep 4002173 = 1500815) (by norm_num)
theorem B4059517 : Blo 1778090 4059517 := bbase (se 3 (by rfl) ⟨761159, by rfl⟩ : syracuseStep 4059517 = 1522319) (by norm_num)
theorem B4059533 : Blo 1778090 4059533 := bbase (se 3 (by rfl) ⟨761162, by rfl⟩ : syracuseStep 4059533 = 1522325) (by norm_num)
theorem B8114597 : Blo 1778090 8114597 := bbase (se 4 (by rfl) ⟨760743, by rfl⟩ : syracuseStep 8114597 = 1521487) (by norm_num)
theorem B4002245 : Blo 1778090 4002245 := bbase (se 4 (by rfl) ⟨375210, by rfl⟩ : syracuseStep 4002245 = 750421) (by norm_num)
theorem B3002845 : Blo 1778090 3002845 := bbase (se 3 (by rfl) ⟨563033, by rfl⟩ : syracuseStep 3002845 = 1126067) (by norm_num)
theorem B5067269 : Blo 1778090 5067269 := bbase (se 4 (by rfl) ⟨475056, by rfl⟩ : syracuseStep 5067269 = 950113) (by norm_num)
theorem B4002317 : Blo 1778090 4002317 := bbase (se 3 (by rfl) ⟨750434, by rfl⟩ : syracuseStep 4002317 = 1500869) (by norm_num)
theorem B6754853 : Blo 1778090 6754853 := bbase (se 4 (by rfl) ⟨633267, by rfl⟩ : syracuseStep 6754853 = 1266535) (by norm_num)
theorem B3002933 : Blo 1778090 3002933 := bbase (se 5 (by rfl) ⟨140762, by rfl⟩ : syracuseStep 3002933 = 281525) (by norm_num)
theorem B9007685 : Blo 1778090 9007685 := bbase (se 4 (by rfl) ⟨844470, by rfl⟩ : syracuseStep 9007685 = 1688941) (by norm_num)
theorem B4502101 : Blo 1778090 4502101 := bbase (se 8 (by rfl) ⟨26379, by rfl⟩ : syracuseStep 4502101 = 52759) (by norm_num)
theorem B4002389 : Blo 1778090 4002389 := bbase (se 8 (by rfl) ⟨23451, by rfl⟩ : syracuseStep 4002389 = 46903) (by norm_num)
theorem B2667149 : Blo 1778090 2667149 := bbase (se 3 (by rfl) ⟨500090, by rfl⟩ : syracuseStep 2667149 = 1000181) (by norm_num)
theorem B4002461 : Blo 1778090 4002461 := bbase (se 3 (by rfl) ⟨750461, by rfl⟩ : syracuseStep 4002461 = 1500923) (by norm_num)
theorem B2667173 : Blo 1778090 2667173 := bbase (se 4 (by rfl) ⟨250047, by rfl⟩ : syracuseStep 2667173 = 500095) (by norm_num)
theorem B3003061 : Blo 1778090 3003061 := bbase (se 5 (by rfl) ⟨140768, by rfl⟩ : syracuseStep 3003061 = 281537) (by norm_num)
theorem B2667197 : Blo 1778090 2667197 := bbase (se 3 (by rfl) ⟨500099, by rfl⟩ : syracuseStep 2667197 = 1000199) (by norm_num)
theorem B4502213 : Blo 1778090 4502213 := bbase (se 4 (by rfl) ⟨422082, by rfl⟩ : syracuseStep 4502213 = 844165) (by norm_num)
theorem B5067461 : Blo 1778090 5067461 := bbase (se 4 (by rfl) ⟨475074, by rfl⟩ : syracuseStep 5067461 = 950149) (by norm_num)
theorem B2667221 : Blo 1778090 2667221 := bbase (se 7 (by rfl) ⟨31256, by rfl⟩ : syracuseStep 2667221 = 62513) (by norm_num)
theorem B22794965 : Blo 1778090 22794965 := bbase (se 7 (by rfl) ⟨267128, by rfl⟩ : syracuseStep 22794965 = 534257) (by norm_num)
theorem B4002533 : Blo 1778090 4002533 := bbase (se 4 (by rfl) ⟨375237, by rfl⟩ : syracuseStep 4002533 = 750475) (by norm_num)
theorem B2667245 : Blo 1778090 2667245 := bbase (se 3 (by rfl) ⟨500108, by rfl⟩ : syracuseStep 2667245 = 1000217) (by norm_num)
theorem B6001397 : Blo 1778090 6001397 := bbase (se 5 (by rfl) ⟨281315, by rfl⟩ : syracuseStep 6001397 = 562631) (by norm_num)
theorem B2028289 : Blo 1778090 2028289 := bbase (se 2 (by rfl) ⟨760608, by rfl⟩ : syracuseStep 2028289 = 1521217) (by norm_num)
theorem B2667269 : Blo 1778090 2667269 := bbase (se 4 (by rfl) ⟨250056, by rfl⟩ : syracuseStep 2667269 = 500113) (by norm_num)
theorem B3003149 : Blo 1778090 3003149 := bbase (se 3 (by rfl) ⟨563090, by rfl⟩ : syracuseStep 3003149 = 1126181) (by norm_num)
theorem B2667293 : Blo 1778090 2667293 := bbase (se 3 (by rfl) ⟨500117, by rfl⟩ : syracuseStep 2667293 = 1000235) (by norm_num)
theorem B2028325 : Blo 1778090 2028325 := bbase (se 4 (by rfl) ⟨190155, by rfl⟩ : syracuseStep 2028325 = 380311) (by norm_num)
theorem B4002605 : Blo 1778090 4002605 := bbase (se 3 (by rfl) ⟨750488, by rfl⟩ : syracuseStep 4002605 = 1500977) (by norm_num)
theorem B2667317 : Blo 1778090 2667317 := bbase (se 5 (by rfl) ⟨125030, by rfl⟩ : syracuseStep 2667317 = 250061) (by norm_num)
theorem B8549189 : Blo 1778090 8549189 := bbase (se 4 (by rfl) ⟨801486, by rfl⟩ : syracuseStep 8549189 = 1602973) (by norm_num)
theorem B2667341 : Blo 1778090 2667341 := bbase (se 3 (by rfl) ⟨500126, by rfl⟩ : syracuseStep 2667341 = 1000253) (by norm_num)
theorem B2667365 : Blo 1778090 2667365 := bbase (se 4 (by rfl) ⟨250065, by rfl⟩ : syracuseStep 2667365 = 500131) (by norm_num)
theorem B3126125 : Blo 1778090 3126125 := bbase (se 3 (by rfl) ⟨586148, by rfl⟩ : syracuseStep 3126125 = 1172297) (by norm_num)
theorem B4002677 : Blo 1778090 4002677 := bbase (se 5 (by rfl) ⟨187625, by rfl⟩ : syracuseStep 4002677 = 375251) (by norm_num)
theorem B2667389 : Blo 1778090 2667389 := bbase (se 3 (by rfl) ⟨500135, by rfl⟩ : syracuseStep 2667389 = 1000271) (by norm_num)
theorem B4502405 : Blo 1778090 4502405 := bbase (se 4 (by rfl) ⟨422100, by rfl⟩ : syracuseStep 4502405 = 844201) (by norm_num)
theorem B3003277 : Blo 1778090 3003277 := bbase (se 3 (by rfl) ⟨563114, by rfl⟩ : syracuseStep 3003277 = 1126229) (by norm_num)
theorem B2667413 : Blo 1778090 2667413 := bbase (se 6 (by rfl) ⟨62517, by rfl⟩ : syracuseStep 2667413 = 125035) (by norm_num)
theorem B2667437 : Blo 1778090 2667437 := bbase (se 3 (by rfl) ⟨500144, by rfl⟩ : syracuseStep 2667437 = 1000289) (by norm_num)
theorem B4002749 : Blo 1778090 4002749 := bbase (se 3 (by rfl) ⟨750515, by rfl⟩ : syracuseStep 4002749 = 1501031) (by norm_num)
theorem B2667461 : Blo 1778090 2667461 := bbase (se 4 (by rfl) ⟨250074, by rfl⟩ : syracuseStep 2667461 = 500149) (by norm_num)
theorem B3797965 : Blo 1778090 3797965 := bbase (se 3 (by rfl) ⟨712118, by rfl⟩ : syracuseStep 3797965 = 1424237) (by norm_num)
theorem B2667485 : Blo 1778090 2667485 := bbase (se 3 (by rfl) ⟨500153, by rfl⟩ : syracuseStep 2667485 = 1000307) (by norm_num)
theorem B3003365 : Blo 1778090 3003365 := bbase (se 4 (by rfl) ⟨281565, by rfl⟩ : syracuseStep 3003365 = 563131) (by norm_num)
theorem B2667509 : Blo 1778090 2667509 := bbase (se 5 (by rfl) ⟨125039, by rfl⟩ : syracuseStep 2667509 = 250079) (by norm_num)
theorem B4002821 : Blo 1778090 4002821 := bbase (se 4 (by rfl) ⟨375264, by rfl⟩ : syracuseStep 4002821 = 750529) (by norm_num)
theorem B2667533 : Blo 1778090 2667533 := bbase (se 3 (by rfl) ⟨500162, by rfl⟩ : syracuseStep 2667533 = 1000325) (by norm_num)
theorem B2667557 : Blo 1778090 2667557 := bbase (se 4 (by rfl) ⟨250083, by rfl⟩ : syracuseStep 2667557 = 500167) (by norm_num)
theorem B2667581 : Blo 1778090 2667581 := bbase (se 3 (by rfl) ⟨500171, by rfl⟩ : syracuseStep 2667581 = 1000343) (by norm_num)
theorem B3798085 : Blo 1778090 3798085 := bbase (se 4 (by rfl) ⟨356070, by rfl⟩ : syracuseStep 3798085 = 712141) (by norm_num)
theorem B4002893 : Blo 1778090 4002893 := bbase (se 3 (by rfl) ⟨750542, by rfl⟩ : syracuseStep 4002893 = 1501085) (by norm_num)
theorem B2667605 : Blo 1778090 2667605 := bbase (se 8 (by rfl) ⟨15630, by rfl⟩ : syracuseStep 2667605 = 31261) (by norm_num)
theorem B3003493 : Blo 1778090 3003493 := bbase (se 4 (by rfl) ⟨281577, by rfl⟩ : syracuseStep 3003493 = 563155) (by norm_num)
theorem B2667629 : Blo 1778090 2667629 := bbase (se 3 (by rfl) ⟨500180, by rfl⟩ : syracuseStep 2667629 = 1000361) (by norm_num)
theorem B2667653 : Blo 1778090 2667653 := bbase (se 4 (by rfl) ⟨250092, by rfl⟩ : syracuseStep 2667653 = 500185) (by norm_num)
theorem B4002965 : Blo 1778090 4002965 := bbase (se 6 (by rfl) ⟨93819, by rfl⟩ : syracuseStep 4002965 = 187639) (by norm_num)
theorem B2667677 : Blo 1778090 2667677 := bbase (se 3 (by rfl) ⟨500189, by rfl⟩ : syracuseStep 2667677 = 1000379) (by norm_num)
theorem B6001829 : Blo 1778090 6001829 := bbase (se 4 (by rfl) ⟨562671, by rfl⟩ : syracuseStep 6001829 = 1125343) (by norm_num)
theorem B2667701 : Blo 1778090 2667701 := bbase (se 5 (by rfl) ⟨125048, by rfl⟩ : syracuseStep 2667701 = 250097) (by norm_num)
theorem B3003581 : Blo 1778090 3003581 := bbase (se 3 (by rfl) ⟨563171, by rfl⟩ : syracuseStep 3003581 = 1126343) (by norm_num)
theorem B2667725 : Blo 1778090 2667725 := bbase (se 3 (by rfl) ⟨500198, by rfl⟩ : syracuseStep 2667725 = 1000397) (by norm_num)
theorem B4502749 : Blo 1778090 4502749 := bbase (se 3 (by rfl) ⟨844265, by rfl⟩ : syracuseStep 4502749 = 1688531) (by norm_num)
theorem B4003037 : Blo 1778090 4003037 := bbase (se 3 (by rfl) ⟨750569, by rfl⟩ : syracuseStep 4003037 = 1501139) (by norm_num)
theorem B2667749 : Blo 1778090 2667749 := bbase (se 4 (by rfl) ⟨250101, by rfl⟩ : syracuseStep 2667749 = 500203) (by norm_num)
theorem B2667773 : Blo 1778090 2667773 := bbase (se 3 (by rfl) ⟨500207, by rfl⟩ : syracuseStep 2667773 = 1000415) (by norm_num)
theorem B2667797 : Blo 1778090 2667797 := bbase (se 6 (by rfl) ⟨62526, by rfl⟩ : syracuseStep 2667797 = 125053) (by norm_num)
theorem B4003109 : Blo 1778090 4003109 := bbase (se 4 (by rfl) ⟨375291, by rfl⟩ : syracuseStep 4003109 = 750583) (by norm_num)
theorem B2667821 : Blo 1778090 2667821 := bbase (se 3 (by rfl) ⟨500216, by rfl⟩ : syracuseStep 2667821 = 1000433) (by norm_num)
theorem B3003709 : Blo 1778090 3003709 := bbase (se 3 (by rfl) ⟨563195, by rfl⟩ : syracuseStep 3003709 = 1126391) (by norm_num)
theorem B3798341 : Blo 1778090 3798341 := bbase (se 4 (by rfl) ⟨356094, by rfl⟩ : syracuseStep 3798341 = 712189) (by norm_num)
theorem B2667845 : Blo 1778090 2667845 := bbase (se 4 (by rfl) ⟨250110, by rfl⟩ : syracuseStep 2667845 = 500221) (by norm_num)
theorem B4502861 : Blo 1778090 4502861 := bbase (se 3 (by rfl) ⟨844286, by rfl⟩ : syracuseStep 4502861 = 1688573) (by norm_num)
theorem B2667869 : Blo 1778090 2667869 := bbase (se 3 (by rfl) ⟨500225, by rfl⟩ : syracuseStep 2667869 = 1000451) (by norm_num)
theorem B4003181 : Blo 1778090 4003181 := bbase (se 3 (by rfl) ⟨750596, by rfl⟩ : syracuseStep 4003181 = 1501193) (by norm_num)
theorem B2667893 : Blo 1778090 2667893 := bbase (se 5 (by rfl) ⟨125057, by rfl⟩ : syracuseStep 2667893 = 250115) (by norm_num)
theorem B2667917 : Blo 1778090 2667917 := bbase (se 3 (by rfl) ⟨500234, by rfl⟩ : syracuseStep 2667917 = 1000469) (by norm_num)
theorem B3003797 : Blo 1778090 3003797 := bbase (se 6 (by rfl) ⟨70401, by rfl⟩ : syracuseStep 3003797 = 140803) (by norm_num)
theorem B2667941 : Blo 1778090 2667941 := bbase (se 4 (by rfl) ⟨250119, by rfl⟩ : syracuseStep 2667941 = 500239) (by norm_num)
theorem B4003253 : Blo 1778090 4003253 := bbase (se 5 (by rfl) ⟨187652, by rfl⟩ : syracuseStep 4003253 = 375305) (by norm_num)
theorem B2667965 : Blo 1778090 2667965 := bbase (se 3 (by rfl) ⟨500243, by rfl⟩ : syracuseStep 2667965 = 1000487) (by norm_num)
theorem B2667989 : Blo 1778090 2667989 := bbase (se 7 (by rfl) ⟨31265, by rfl⟩ : syracuseStep 2667989 = 62531) (by norm_num)
theorem B2668013 : Blo 1778090 2668013 := bbase (se 3 (by rfl) ⟨500252, by rfl⟩ : syracuseStep 2668013 = 1000505) (by norm_num)
theorem B4003325 : Blo 1778090 4003325 := bbase (se 3 (by rfl) ⟨750623, by rfl⟩ : syracuseStep 4003325 = 1501247) (by norm_num)
theorem B2668037 : Blo 1778090 2668037 := bbase (se 4 (by rfl) ⟨250128, by rfl⟩ : syracuseStep 2668037 = 500257) (by norm_num)
theorem B4503053 : Blo 1778090 4503053 := bbase (se 3 (by rfl) ⟨844322, by rfl⟩ : syracuseStep 4503053 = 1688645) (by norm_num)
theorem B2668061 : Blo 1778090 2668061 := bbase (se 3 (by rfl) ⟨500261, by rfl⟩ : syracuseStep 2668061 = 1000523) (by norm_num)
theorem B2668085 : Blo 1778090 2668085 := bbase (se 5 (by rfl) ⟨125066, by rfl⟩ : syracuseStep 2668085 = 250133) (by norm_num)
theorem B4003397 : Blo 1778090 4003397 := bbase (se 4 (by rfl) ⟨375318, by rfl⟩ : syracuseStep 4003397 = 750637) (by norm_num)
theorem B2668109 : Blo 1778090 2668109 := bbase (se 3 (by rfl) ⟨500270, by rfl⟩ : syracuseStep 2668109 = 1000541) (by norm_num)
theorem B6002261 : Blo 1778090 6002261 := bbase (se 8 (by rfl) ⟨35169, by rfl⟩ : syracuseStep 6002261 = 70339) (by norm_num)
theorem B73021013 : Blo 1778090 73021013 := bbase (se 8 (by rfl) ⟨427857, by rfl⟩ : syracuseStep 73021013 = 855715) (by norm_num)
theorem B6084197 : Blo 1778090 6084197 := bbase (se 4 (by rfl) ⟨570393, by rfl⟩ : syracuseStep 6084197 = 1140787) (by norm_num)
theorem B2668133 : Blo 1778090 2668133 := bbase (se 4 (by rfl) ⟨250137, by rfl⟩ : syracuseStep 2668133 = 500275) (by norm_num)
theorem B3421813 : Blo 1778090 3421813 := bbase (se 5 (by rfl) ⟨160397, by rfl⟩ : syracuseStep 3421813 = 320795) (by norm_num)
theorem B2668157 : Blo 1778090 2668157 := bbase (se 3 (by rfl) ⟨500279, by rfl⟩ : syracuseStep 2668157 = 1000559) (by norm_num)
theorem B4003469 : Blo 1778090 4003469 := bbase (se 3 (by rfl) ⟨750650, by rfl⟩ : syracuseStep 4003469 = 1501301) (by norm_num)
theorem B2668181 : Blo 1778090 2668181 := bbase (se 6 (by rfl) ⟨62535, by rfl⟩ : syracuseStep 2668181 = 125071) (by norm_num)
theorem B21649045 : Blo 1778090 21649045 := bbase (se 6 (by rfl) ⟨507399, by rfl⟩ : syracuseStep 21649045 = 1014799) (by norm_num)
theorem B5068453 : Blo 1778090 5068453 := bbase (se 4 (by rfl) ⟨475167, by rfl⟩ : syracuseStep 5068453 = 950335) (by norm_num)
theorem B2668205 : Blo 1778090 2668205 := bbase (se 3 (by rfl) ⟨500288, by rfl⟩ : syracuseStep 2668205 = 1000577) (by norm_num)
theorem B2250433 : Blo 1778090 2250433 := bbase (se 2 (by rfl) ⟨843912, by rfl⟩ : syracuseStep 2250433 = 1687825) (by norm_num)
theorem B2668229 : Blo 1778090 2668229 := bbase (se 4 (by rfl) ⟨250146, by rfl⟩ : syracuseStep 2668229 = 500293) (by norm_num)
theorem B4003541 : Blo 1778090 4003541 := bbase (se 7 (by rfl) ⟨46916, by rfl⟩ : syracuseStep 4003541 = 93833) (by norm_num)
theorem B2668253 : Blo 1778090 2668253 := bbase (se 3 (by rfl) ⟨500297, by rfl⟩ : syracuseStep 2668253 = 1000595) (by norm_num)
theorem B2668277 : Blo 1778090 2668277 := bbase (se 5 (by rfl) ⟨125075, by rfl⟩ : syracuseStep 2668277 = 250151) (by norm_num)
theorem B2668301 : Blo 1778090 2668301 := bbase (se 3 (by rfl) ⟨500306, by rfl⟩ : syracuseStep 2668301 = 1000613) (by norm_num)
theorem B4003613 : Blo 1778090 4003613 := bbase (se 3 (by rfl) ⟨750677, by rfl⟩ : syracuseStep 4003613 = 1501355) (by norm_num)
theorem B2668325 : Blo 1778090 2668325 := bbase (se 4 (by rfl) ⟨250155, by rfl⟩ : syracuseStep 2668325 = 500311) (by norm_num)
theorem B4331317 : Blo 1778090 4331317 := bbase (se 5 (by rfl) ⟨203030, by rfl⟩ : syracuseStep 4331317 = 406061) (by norm_num)
theorem B2668349 : Blo 1778090 2668349 := bbase (se 3 (by rfl) ⟨500315, by rfl⟩ : syracuseStep 2668349 = 1000631) (by norm_num)
theorem B2668373 : Blo 1778090 2668373 := bbase (se 9 (by rfl) ⟨7817, by rfl⟩ : syracuseStep 2668373 = 15635) (by norm_num)
theorem B9008981 : Blo 1778090 9008981 := bbase (se 9 (by rfl) ⟨26393, by rfl⟩ : syracuseStep 9008981 = 52787) (by norm_num)
theorem B4331357 : Blo 1778090 4331357 := bbase (se 3 (by rfl) ⟨812129, by rfl⟩ : syracuseStep 4331357 = 1624259) (by norm_num)
theorem B4503397 : Blo 1778090 4503397 := bbase (se 4 (by rfl) ⟨422193, by rfl⟩ : syracuseStep 4503397 = 844387) (by norm_num)
theorem B4003685 : Blo 1778090 4003685 := bbase (se 4 (by rfl) ⟨375345, by rfl⟩ : syracuseStep 4003685 = 750691) (by norm_num)
theorem B2250605 : Blo 1778090 2250605 := bbase (se 3 (by rfl) ⟨421988, by rfl⟩ : syracuseStep 2250605 = 843977) (by norm_num)
theorem B2668397 : Blo 1778090 2668397 := bbase (se 3 (by rfl) ⟨500324, by rfl⟩ : syracuseStep 2668397 = 1000649) (by norm_num)
theorem B2283385 : Blo 1778090 2283385 := bbase (se 2 (by rfl) ⟨856269, by rfl⟩ : syracuseStep 2283385 = 1712539) (by norm_num)
theorem B2668421 : Blo 1778090 2668421 := bbase (se 4 (by rfl) ⟨250164, by rfl⟩ : syracuseStep 2668421 = 500329) (by norm_num)
theorem B2668445 : Blo 1778090 2668445 := bbase (se 3 (by rfl) ⟨500333, by rfl⟩ : syracuseStep 2668445 = 1000667) (by norm_num)
theorem B2250661 : Blo 1778090 2250661 := bbase (se 4 (by rfl) ⟨210999, by rfl⟩ : syracuseStep 2250661 = 421999) (by norm_num)
theorem B4003757 : Blo 1778090 4003757 := bbase (se 3 (by rfl) ⟨750704, by rfl⟩ : syracuseStep 4003757 = 1501409) (by norm_num)
theorem B2668469 : Blo 1778090 2668469 := bbase (se 5 (by rfl) ⟨125084, by rfl⟩ : syracuseStep 2668469 = 250169) (by norm_num)
theorem B2668493 : Blo 1778090 2668493 := bbase (se 3 (by rfl) ⟨500342, by rfl⟩ : syracuseStep 2668493 = 1000685) (by norm_num)
theorem B4503509 : Blo 1778090 4503509 := bbase (se 7 (by rfl) ⟨52775, by rfl⟩ : syracuseStep 4503509 = 105551) (by norm_num)
theorem B2668517 : Blo 1778090 2668517 := bbase (se 4 (by rfl) ⟨250173, by rfl⟩ : syracuseStep 2668517 = 500347) (by norm_num)
theorem B4003829 : Blo 1778090 4003829 := bbase (se 5 (by rfl) ⟨187679, by rfl⟩ : syracuseStep 4003829 = 375359) (by norm_num)
theorem B2668541 : Blo 1778090 2668541 := bbase (se 3 (by rfl) ⟨500351, by rfl⟩ : syracuseStep 2668541 = 1000703) (by norm_num)
theorem B2250757 : Blo 1778090 2250757 := bbase (se 4 (by rfl) ⟨211008, by rfl⟩ : syracuseStep 2250757 = 422017) (by norm_num)
theorem B6002693 : Blo 1778090 6002693 := bbase (se 4 (by rfl) ⟨562752, by rfl⟩ : syracuseStep 6002693 = 1125505) (by norm_num)
theorem B2668565 : Blo 1778090 2668565 := bbase (se 6 (by rfl) ⟨62544, by rfl⟩ : syracuseStep 2668565 = 125089) (by norm_num)
theorem B2668589 : Blo 1778090 2668589 := bbase (se 3 (by rfl) ⟨500360, by rfl⟩ : syracuseStep 2668589 = 1000721) (by norm_num)
theorem B4003901 : Blo 1778090 4003901 := bbase (se 3 (by rfl) ⟨750731, by rfl⟩ : syracuseStep 4003901 = 1501463) (by norm_num)
theorem B3905597 : Blo 1778090 3905597 := bbase (se 3 (by rfl) ⟨732299, by rfl⟩ : syracuseStep 3905597 = 1464599) (by norm_num)
theorem B2668613 : Blo 1778090 2668613 := bbase (se 4 (by rfl) ⟨250182, by rfl⟩ : syracuseStep 2668613 = 500365) (by norm_num)
theorem B2848853 : Blo 1778090 2848853 := bbase (se 8 (by rfl) ⟨16692, by rfl⟩ : syracuseStep 2848853 = 33385) (by norm_num)
theorem B2668637 : Blo 1778090 2668637 := bbase (se 3 (by rfl) ⟨500369, by rfl⟩ : syracuseStep 2668637 = 1000739) (by norm_num)
theorem B2668661 : Blo 1778090 2668661 := bbase (se 5 (by rfl) ⟨125093, by rfl⟩ : syracuseStep 2668661 = 250187) (by norm_num)
theorem B5699717 : Blo 1778090 5699717 := bbase (se 4 (by rfl) ⟨534348, by rfl⟩ : syracuseStep 5699717 = 1068697) (by norm_num)
theorem B4003973 : Blo 1778090 4003973 := bbase (se 4 (by rfl) ⟨375372, by rfl⟩ : syracuseStep 4003973 = 750745) (by norm_num)
theorem B2668685 : Blo 1778090 2668685 := bbase (se 3 (by rfl) ⟨500378, by rfl⟩ : syracuseStep 2668685 = 1000757) (by norm_num)
theorem B4503701 : Blo 1778090 4503701 := bbase (se 6 (by rfl) ⟨105555, by rfl⟩ : syracuseStep 4503701 = 211111) (by norm_num)
theorem B2668709 : Blo 1778090 2668709 := bbase (se 4 (by rfl) ⟨250191, by rfl⟩ : syracuseStep 2668709 = 500383) (by norm_num)
theorem B2250929 : Blo 1778090 2250929 := bbase (se 2 (by rfl) ⟨844098, by rfl⟩ : syracuseStep 2250929 = 1688197) (by norm_num)
theorem B3799229 : Blo 1778090 3799229 := bbase (se 3 (by rfl) ⟨712355, by rfl⟩ : syracuseStep 3799229 = 1424711) (by norm_num)
theorem B2668733 : Blo 1778090 2668733 := bbase (se 3 (by rfl) ⟨500387, by rfl⟩ : syracuseStep 2668733 = 1000775) (by norm_num)
theorem B4004045 : Blo 1778090 4004045 := bbase (se 3 (by rfl) ⟨750758, by rfl⟩ : syracuseStep 4004045 = 1501517) (by norm_num)
theorem B2668757 : Blo 1778090 2668757 := bbase (se 7 (by rfl) ⟨31274, by rfl⟩ : syracuseStep 2668757 = 62549) (by norm_num)
theorem B2250985 : Blo 1778090 2250985 := bbase (se 2 (by rfl) ⟨844119, by rfl⟩ : syracuseStep 2250985 = 1688239) (by norm_num)
theorem B2668781 : Blo 1778090 2668781 := bbase (se 3 (by rfl) ⟨500396, by rfl⟩ : syracuseStep 2668781 = 1000793) (by norm_num)
theorem B2668805 : Blo 1778090 2668805 := bbase (se 4 (by rfl) ⟨250200, by rfl⟩ : syracuseStep 2668805 = 500401) (by norm_num)
theorem B4004117 : Blo 1778090 4004117 := bbase (se 6 (by rfl) ⟨93846, by rfl⟩ : syracuseStep 4004117 = 187693) (by norm_num)
theorem B4274461 : Blo 1778090 4274461 := bbase (se 3 (by rfl) ⟨801461, by rfl⟩ : syracuseStep 4274461 = 1602923) (by norm_num)
theorem B2668829 : Blo 1778090 2668829 := bbase (se 3 (by rfl) ⟨500405, by rfl⟩ : syracuseStep 2668829 = 1000811) (by norm_num)
theorem B2668853 : Blo 1778090 2668853 := bbase (se 5 (by rfl) ⟨125102, by rfl⟩ : syracuseStep 2668853 = 250205) (by norm_num)
theorem B2251081 : Blo 1778090 2251081 := bbase (se 2 (by rfl) ⟨844155, by rfl⟩ : syracuseStep 2251081 = 1688311) (by norm_num)
theorem B2668877 : Blo 1778090 2668877 := bbase (se 3 (by rfl) ⟨500414, by rfl⟩ : syracuseStep 2668877 = 1000829) (by norm_num)
theorem B10819925 : Blo 1778090 10819925 := bbase (se 10 (by rfl) ⟨15849, by rfl⟩ : syracuseStep 10819925 = 31699) (by norm_num)
theorem B2136413 : Blo 1778090 2136413 := bbase (se 3 (by rfl) ⟨400577, by rfl⟩ : syracuseStep 2136413 = 801155) (by norm_num)
theorem B4004189 : Blo 1778090 4004189 := bbase (se 3 (by rfl) ⟨750785, by rfl⟩ : syracuseStep 4004189 = 1501571) (by norm_num)
theorem B2668901 : Blo 1778090 2668901 := bbase (se 4 (by rfl) ⟨250209, by rfl⟩ : syracuseStep 2668901 = 500419) (by norm_num)
theorem B2668925 : Blo 1778090 2668925 := bbase (se 3 (by rfl) ⟨500423, by rfl⟩ : syracuseStep 2668925 = 1000847) (by norm_num)
theorem B1898893 : Blo 1778090 1898893 := bbase (se 3 (by rfl) ⟨356042, by rfl⟩ : syracuseStep 1898893 = 712085) (by norm_num)
theorem B1898897 : Blo 1778090 1898897 := bbase (se 2 (by rfl) ⟨712086, by rfl⟩ : syracuseStep 1898897 = 1424173) (by norm_num)
theorem B2668949 : Blo 1778090 2668949 := bbase (se 6 (by rfl) ⟨62553, by rfl⟩ : syracuseStep 2668949 = 125107) (by norm_num)
theorem B8550805 : Blo 1778090 8550805 := bbase (se 6 (by rfl) ⟨200409, by rfl⟩ : syracuseStep 8550805 = 400819) (by norm_num)
theorem B4004261 : Blo 1778090 4004261 := bbase (se 4 (by rfl) ⟨375399, by rfl⟩ : syracuseStep 4004261 = 750799) (by norm_num)
theorem B3799469 : Blo 1778090 3799469 := bbase (se 3 (by rfl) ⟨712400, by rfl⟩ : syracuseStep 3799469 = 1424801) (by norm_num)
theorem B2668973 : Blo 1778090 2668973 := bbase (se 3 (by rfl) ⟨500432, by rfl⟩ : syracuseStep 2668973 = 1000865) (by norm_num)
theorem B6003125 : Blo 1778090 6003125 := bbase (se 5 (by rfl) ⟨281396, by rfl⟩ : syracuseStep 6003125 = 562793) (by norm_num)
theorem B2668997 : Blo 1778090 2668997 := bbase (se 4 (by rfl) ⟨250218, by rfl⟩ : syracuseStep 2668997 = 500437) (by norm_num)
theorem B30800341 : Blo 1778090 30800341 := bbase (se 7 (by rfl) ⟨360941, by rfl⟩ : syracuseStep 30800341 = 721883) (by norm_num)
theorem B2669021 : Blo 1778090 2669021 := bbase (se 3 (by rfl) ⟨500441, by rfl⟩ : syracuseStep 2669021 = 1000883) (by norm_num)
theorem B4504045 : Blo 1778090 4504045 := bbase (se 3 (by rfl) ⟨844508, by rfl⟩ : syracuseStep 4504045 = 1689017) (by norm_num)
theorem B4004333 : Blo 1778090 4004333 := bbase (se 3 (by rfl) ⟨750812, by rfl⟩ : syracuseStep 4004333 = 1501625) (by norm_num)
theorem B2251253 : Blo 1778090 2251253 := bbase (se 5 (by rfl) ⟨105527, by rfl⟩ : syracuseStep 2251253 = 211055) (by norm_num)
theorem B2669045 : Blo 1778090 2669045 := bbase (se 5 (by rfl) ⟨125111, by rfl⟩ : syracuseStep 2669045 = 250223) (by norm_num)
theorem B7600645 : Blo 1778090 7600645 := bbase (se 4 (by rfl) ⟨712560, by rfl⟩ : syracuseStep 7600645 = 1425121) (by norm_num)
theorem B2669069 : Blo 1778090 2669069 := bbase (se 3 (by rfl) ⟨500450, by rfl⟩ : syracuseStep 2669069 = 1000901) (by norm_num)
theorem B2669093 : Blo 1778090 2669093 := bbase (se 4 (by rfl) ⟨250227, by rfl⟩ : syracuseStep 2669093 = 500455) (by norm_num)
theorem B2251309 : Blo 1778090 2251309 := bbase (se 3 (by rfl) ⟨422120, by rfl⟩ : syracuseStep 2251309 = 844241) (by norm_num)
theorem B4004405 : Blo 1778090 4004405 := bbase (se 5 (by rfl) ⟨187706, by rfl⟩ : syracuseStep 4004405 = 375413) (by norm_num)
theorem B2669117 : Blo 1778090 2669117 := bbase (se 3 (by rfl) ⟨500459, by rfl⟩ : syracuseStep 2669117 = 1000919) (by norm_num)
theorem B2849365 : Blo 1778090 2849365 := bbase (se 8 (by rfl) ⟨16695, by rfl⟩ : syracuseStep 2849365 = 33391) (by norm_num)
theorem B2669141 : Blo 1778090 2669141 := bbase (se 8 (by rfl) ⟨15639, by rfl⟩ : syracuseStep 2669141 = 31279) (by norm_num)
theorem B4504157 : Blo 1778090 4504157 := bbase (se 3 (by rfl) ⟨844529, by rfl⟩ : syracuseStep 4504157 = 1689059) (by norm_num)
theorem B6756965 : Blo 1778090 6756965 := bbase (se 4 (by rfl) ⟨633465, by rfl⟩ : syracuseStep 6756965 = 1266931) (by norm_num)
theorem B2669165 : Blo 1778090 2669165 := bbase (se 3 (by rfl) ⟨500468, by rfl⟩ : syracuseStep 2669165 = 1000937) (by norm_num)
theorem B4004477 : Blo 1778090 4004477 := bbase (se 3 (by rfl) ⟨750839, by rfl⟩ : syracuseStep 4004477 = 1501679) (by norm_num)
theorem B2669189 : Blo 1778090 2669189 := bbase (se 4 (by rfl) ⟨250236, by rfl⟩ : syracuseStep 2669189 = 500473) (by norm_num)
theorem B2251405 : Blo 1778090 2251405 := bbase (se 3 (by rfl) ⟨422138, by rfl⟩ : syracuseStep 2251405 = 844277) (by norm_num)
theorem B2136721 : Blo 1778090 2136721 := bbase (se 2 (by rfl) ⟨801270, by rfl⟩ : syracuseStep 2136721 = 1602541) (by norm_num)
theorem B2669213 : Blo 1778090 2669213 := bbase (se 3 (by rfl) ⟨500477, by rfl⟩ : syracuseStep 2669213 = 1000955) (by norm_num)
theorem B2669237 : Blo 1778090 2669237 := bbase (se 5 (by rfl) ⟨125120, by rfl⟩ : syracuseStep 2669237 = 250241) (by norm_num)
theorem B4004549 : Blo 1778090 4004549 := bbase (se 4 (by rfl) ⟨375426, by rfl⟩ : syracuseStep 4004549 = 750853) (by norm_num)
theorem B2669261 : Blo 1778090 2669261 := bbase (se 3 (by rfl) ⟨500486, by rfl⟩ : syracuseStep 2669261 = 1000973) (by norm_num)
theorem B2669285 : Blo 1778090 2669285 := bbase (se 4 (by rfl) ⟨250245, by rfl⟩ : syracuseStep 2669285 = 500491) (by norm_num)
theorem B2136817 : Blo 1778090 2136817 := bbase (se 2 (by rfl) ⟨801306, by rfl⟩ : syracuseStep 2136817 = 1602613) (by norm_num)
theorem B2669309 : Blo 1778090 2669309 := bbase (se 3 (by rfl) ⟨500495, by rfl⟩ : syracuseStep 2669309 = 1000991) (by norm_num)
theorem B4004621 : Blo 1778090 4004621 := bbase (se 3 (by rfl) ⟨750866, by rfl⟩ : syracuseStep 4004621 = 1501733) (by norm_num)
theorem B2669333 : Blo 1778090 2669333 := bbase (se 6 (by rfl) ⟨62562, by rfl⟩ : syracuseStep 2669333 = 125125) (by norm_num)
theorem B4504349 : Blo 1778090 4504349 := bbase (se 3 (by rfl) ⟨844565, by rfl⟩ : syracuseStep 4504349 = 1689131) (by norm_num)
theorem B2669357 : Blo 1778090 2669357 := bbase (se 3 (by rfl) ⟨500504, by rfl⟩ : syracuseStep 2669357 = 1001009) (by norm_num)
theorem B2251577 : Blo 1778090 2251577 := bbase (se 2 (by rfl) ⟨844341, by rfl⟩ : syracuseStep 2251577 = 1688683) (by norm_num)
theorem B2669381 : Blo 1778090 2669381 := bbase (se 4 (by rfl) ⟨250254, by rfl⟩ : syracuseStep 2669381 = 500509) (by norm_num)
theorem B4004693 : Blo 1778090 4004693 := bbase (se 9 (by rfl) ⟨11732, by rfl⟩ : syracuseStep 4004693 = 23465) (by norm_num)
theorem B2669405 : Blo 1778090 2669405 := bbase (se 3 (by rfl) ⟨500513, by rfl⟩ : syracuseStep 2669405 = 1001027) (by norm_num)
theorem B6003557 : Blo 1778090 6003557 := bbase (se 4 (by rfl) ⟨562833, by rfl⟩ : syracuseStep 6003557 = 1125667) (by norm_num)
theorem B2251633 : Blo 1778090 2251633 := bbase (se 2 (by rfl) ⟨844362, by rfl⟩ : syracuseStep 2251633 = 1688725) (by norm_num)
theorem B2669429 : Blo 1778090 2669429 := bbase (se 5 (by rfl) ⟨125129, by rfl⟩ : syracuseStep 2669429 = 250259) (by norm_num)
theorem B2136961 : Blo 1778090 2136961 := bbase (se 2 (by rfl) ⟨801360, by rfl⟩ : syracuseStep 2136961 = 1602721) (by norm_num)
theorem B6757253 : Blo 1778090 6757253 := bbase (se 4 (by rfl) ⟨633492, by rfl⟩ : syracuseStep 6757253 = 1266985) (by norm_num)
theorem B2669453 : Blo 1778090 2669453 := bbase (se 3 (by rfl) ⟨500522, by rfl⟩ : syracuseStep 2669453 = 1001045) (by norm_num)
theorem B9124757 : Blo 1778090 9124757 := bbase (se 6 (by rfl) ⟨213861, by rfl⟩ : syracuseStep 9124757 = 427723) (by norm_num)
theorem B4004765 : Blo 1778090 4004765 := bbase (se 3 (by rfl) ⟨750893, by rfl⟩ : syracuseStep 4004765 = 1501787) (by norm_num)
theorem B3799973 : Blo 1778090 3799973 := bbase (se 4 (by rfl) ⟨356247, by rfl⟩ : syracuseStep 3799973 = 712495) (by norm_num)
theorem B2669477 : Blo 1778090 2669477 := bbase (se 4 (by rfl) ⟨250263, by rfl⟩ : syracuseStep 2669477 = 500527) (by norm_num)
theorem B3799981 : Blo 1778090 3799981 := bbase (se 3 (by rfl) ⟨712496, by rfl⟩ : syracuseStep 3799981 = 1424993) (by norm_num)
theorem B4275125 : Blo 1778090 4275125 := bbase (se 5 (by rfl) ⟨200396, by rfl⟩ : syracuseStep 4275125 = 400793) (by norm_num)
theorem B2669501 : Blo 1778090 2669501 := bbase (se 3 (by rfl) ⟨500531, by rfl⟩ : syracuseStep 2669501 = 1001063) (by norm_num)
theorem B1899461 : Blo 1778090 1899461 := bbase (se 4 (by rfl) ⟨178074, by rfl⟩ : syracuseStep 1899461 = 356149) (by norm_num)
theorem B2251729 : Blo 1778090 2251729 := bbase (se 2 (by rfl) ⟨844398, by rfl⟩ : syracuseStep 2251729 = 1688797) (by norm_num)
theorem B2669525 : Blo 1778090 2669525 := bbase (se 7 (by rfl) ⟨31283, by rfl⟩ : syracuseStep 2669525 = 62567) (by norm_num)
theorem B4004837 : Blo 1778090 4004837 := bbase (se 4 (by rfl) ⟨375453, by rfl⟩ : syracuseStep 4004837 = 750907) (by norm_num)
theorem B2669549 : Blo 1778090 2669549 := bbase (se 3 (by rfl) ⟨500540, by rfl⟩ : syracuseStep 2669549 = 1001081) (by norm_num)
theorem B5700613 : Blo 1778090 5700613 := bbase (se 4 (by rfl) ⟨534432, by rfl⟩ : syracuseStep 5700613 = 1068865) (by norm_num)
theorem B2669573 : Blo 1778090 2669573 := bbase (se 4 (by rfl) ⟨250272, by rfl⟩ : syracuseStep 2669573 = 500545) (by norm_num)
theorem B2669597 : Blo 1778090 2669597 := bbase (se 3 (by rfl) ⟨500549, by rfl⟩ : syracuseStep 2669597 = 1001099) (by norm_num)
theorem B4004909 : Blo 1778090 4004909 := bbase (se 3 (by rfl) ⟨750920, by rfl⟩ : syracuseStep 4004909 = 1501841) (by norm_num)
theorem B2669621 : Blo 1778090 2669621 := bbase (se 5 (by rfl) ⟨125138, by rfl⟩ : syracuseStep 2669621 = 250277) (by norm_num)
theorem B3423293 : Blo 1778090 3423293 := bbase (se 3 (by rfl) ⟨641867, by rfl⟩ : syracuseStep 3423293 = 1283735) (by norm_num)
theorem B2669645 : Blo 1778090 2669645 := bbase (se 3 (by rfl) ⟨500558, by rfl⟩ : syracuseStep 2669645 = 1001117) (by norm_num)
theorem B2669669 : Blo 1778090 2669669 := bbase (se 4 (by rfl) ⟨250281, by rfl⟩ : syracuseStep 2669669 = 500563) (by norm_num)
theorem B9010277 : Blo 1778090 9010277 := bbase (se 4 (by rfl) ⟨844713, by rfl⟩ : syracuseStep 9010277 = 1689427) (by norm_num)
theorem B2849909 : Blo 1778090 2849909 := bbase (se 5 (by rfl) ⟨133589, by rfl⟩ : syracuseStep 2849909 = 267179) (by norm_num)
theorem B4504693 : Blo 1778090 4504693 := bbase (se 5 (by rfl) ⟨211157, by rfl⟩ : syracuseStep 4504693 = 422315) (by norm_num)
theorem B4004981 : Blo 1778090 4004981 := bbase (se 5 (by rfl) ⟨187733, by rfl⟩ : syracuseStep 4004981 = 375467) (by norm_num)
theorem B2251901 : Blo 1778090 2251901 := bbase (se 3 (by rfl) ⟨422231, by rfl⟩ : syracuseStep 2251901 = 844463) (by norm_num)
theorem B2669693 : Blo 1778090 2669693 := bbase (se 3 (by rfl) ⟨500567, by rfl⟩ : syracuseStep 2669693 = 1001135) (by norm_num)
theorem B1899649 : Blo 1778090 1899649 := bbase (se 2 (by rfl) ⟨712368, by rfl⟩ : syracuseStep 1899649 = 1424737) (by norm_num)
theorem B15203477 : Blo 1778090 15203477 := bbase (se 6 (by rfl) ⟨356331, by rfl⟩ : syracuseStep 15203477 = 712663) (by norm_num)
theorem B2669717 : Blo 1778090 2669717 := bbase (se 6 (by rfl) ⟨62571, by rfl⟩ : syracuseStep 2669717 = 125143) (by norm_num)
theorem B2669741 : Blo 1778090 2669741 := bbase (se 3 (by rfl) ⟨500576, by rfl⟩ : syracuseStep 2669741 = 1001153) (by norm_num)
theorem B2251957 : Blo 1778090 2251957 := bbase (se 5 (by rfl) ⟨105560, by rfl⟩ : syracuseStep 2251957 = 211121) (by norm_num)
theorem B4005053 : Blo 1778090 4005053 := bbase (se 3 (by rfl) ⟨750947, by rfl⟩ : syracuseStep 4005053 = 1501895) (by norm_num)
theorem B2669765 : Blo 1778090 2669765 := bbase (se 4 (by rfl) ⟨250290, by rfl⟩ : syracuseStep 2669765 = 500581) (by norm_num)
theorem B2669789 : Blo 1778090 2669789 := bbase (se 3 (by rfl) ⟨500585, by rfl⟩ : syracuseStep 2669789 = 1001171) (by norm_num)
theorem B4504805 : Blo 1778090 4504805 := bbase (se 4 (by rfl) ⟨422325, by rfl⟩ : syracuseStep 4504805 = 844651) (by norm_num)
theorem B2669813 : Blo 1778090 2669813 := bbase (se 5 (by rfl) ⟨125147, by rfl⟩ : syracuseStep 2669813 = 250295) (by norm_num)
theorem B4005125 : Blo 1778090 4005125 := bbase (se 4 (by rfl) ⟨375480, by rfl⟩ : syracuseStep 4005125 = 750961) (by norm_num)
theorem B2669837 : Blo 1778090 2669837 := bbase (se 3 (by rfl) ⟨500594, by rfl⟩ : syracuseStep 2669837 = 1001189) (by norm_num)
theorem B6003989 : Blo 1778090 6003989 := bbase (se 6 (by rfl) ⟨140718, by rfl⟩ : syracuseStep 6003989 = 281437) (by norm_num)
theorem B2252053 : Blo 1778090 2252053 := bbase (se 6 (by rfl) ⟨52782, by rfl⟩ : syracuseStep 2252053 = 105565) (by norm_num)
theorem B2669861 : Blo 1778090 2669861 := bbase (se 4 (by rfl) ⟨250299, by rfl⟩ : syracuseStep 2669861 = 500599) (by norm_num)
theorem B2669885 : Blo 1778090 2669885 := bbase (se 3 (by rfl) ⟨500603, by rfl⟩ : syracuseStep 2669885 = 1001207) (by norm_num)
theorem B4005197 : Blo 1778090 4005197 := bbase (se 3 (by rfl) ⟨750974, by rfl⟩ : syracuseStep 4005197 = 1501949) (by norm_num)
theorem B2669909 : Blo 1778090 2669909 := bbase (se 11 (by rfl) ⟨1955, by rfl⟩ : syracuseStep 2669909 = 3911) (by norm_num)
theorem B2669933 : Blo 1778090 2669933 := bbase (se 3 (by rfl) ⟨500612, by rfl⟩ : syracuseStep 2669933 = 1001225) (by norm_num)
theorem B2669957 : Blo 1778090 2669957 := bbase (se 4 (by rfl) ⟨250308, by rfl⟩ : syracuseStep 2669957 = 500617) (by norm_num)
theorem B2669981 : Blo 1778090 2669981 := bbase (se 3 (by rfl) ⟨500621, by rfl⟩ : syracuseStep 2669981 = 1001243) (by norm_num)
theorem B4504997 : Blo 1778090 4504997 := bbase (se 4 (by rfl) ⟨422343, by rfl⟩ : syracuseStep 4504997 = 844687) (by norm_num)
theorem B2670005 : Blo 1778090 2670005 := bbase (se 5 (by rfl) ⟨125156, by rfl⟩ : syracuseStep 2670005 = 250313) (by norm_num)
theorem B2252225 : Blo 1778090 2252225 := bbase (se 2 (by rfl) ⟨844584, by rfl⟩ : syracuseStep 2252225 = 1689169) (by norm_num)
theorem B2670029 : Blo 1778090 2670029 := bbase (se 3 (by rfl) ⟨500630, by rfl⟩ : syracuseStep 2670029 = 1001261) (by norm_num)
theorem B2670053 : Blo 1778090 2670053 := bbase (se 4 (by rfl) ⟨250317, by rfl⟩ : syracuseStep 2670053 = 500635) (by norm_num)
theorem B14425589 : Blo 1778090 14425589 := bbase (se 5 (by rfl) ⟨676199, by rfl⟩ : syracuseStep 14425589 = 1352399) (by norm_num)
theorem B2252281 : Blo 1778090 2252281 := bbase (se 2 (by rfl) ⟨844605, by rfl⟩ : syracuseStep 2252281 = 1689211) (by norm_num)
theorem B2670077 : Blo 1778090 2670077 := bbase (se 3 (by rfl) ⟨500639, by rfl⟩ : syracuseStep 2670077 = 1001279) (by norm_num)
theorem B9002501 : Blo 1778090 9002501 := bbase (se 4 (by rfl) ⟨843984, by rfl⟩ : syracuseStep 9002501 = 1687969) (by norm_num)
theorem B2670101 : Blo 1778090 2670101 := bbase (se 6 (by rfl) ⟨62580, by rfl⟩ : syracuseStep 2670101 = 125161) (by norm_num)
theorem B2670125 : Blo 1778090 2670125 := bbase (se 3 (by rfl) ⟨500648, by rfl⟩ : syracuseStep 2670125 = 1001297) (by norm_num)
theorem B2252377 : Blo 1778090 2252377 := bbase (se 2 (by rfl) ⟨844641, by rfl⟩ : syracuseStep 2252377 = 1689283) (by norm_num)
theorem B2850461 : Blo 1778090 2850461 := bbase (se 3 (by rfl) ⟨534461, by rfl⟩ : syracuseStep 2850461 = 1068923) (by norm_num)
theorem B2850493 : Blo 1778090 2850493 := bbase (se 3 (by rfl) ⟨534467, by rfl⟩ : syracuseStep 2850493 = 1068935) (by norm_num)
theorem B6004421 : Blo 1778090 6004421 := bbase (se 4 (by rfl) ⟨562914, by rfl⟩ : syracuseStep 6004421 = 1125829) (by norm_num)
theorem B8117957 : Blo 1778090 8117957 := bbase (se 4 (by rfl) ⟨761058, by rfl⟩ : syracuseStep 8117957 = 1522117) (by norm_num)
theorem B4505341 : Blo 1778090 4505341 := bbase (se 3 (by rfl) ⟨844751, by rfl⟩ : syracuseStep 4505341 = 1689503) (by norm_num)
theorem B2252549 : Blo 1778090 2252549 := bbase (se 4 (by rfl) ⟨211176, by rfl⟩ : syracuseStep 2252549 = 422353) (by norm_num)
theorem B2252605 : Blo 1778090 2252605 := bbase (se 3 (by rfl) ⟨422363, by rfl⟩ : syracuseStep 2252605 = 844727) (by norm_num)
theorem B2137961 : Blo 1778090 2137961 := bbase (se 2 (by rfl) ⟨801735, by rfl⟩ : syracuseStep 2137961 = 1603471) (by norm_num)
theorem B4505453 : Blo 1778090 4505453 := bbase (se 3 (by rfl) ⟨844772, by rfl⟩ : syracuseStep 4505453 = 1689545) (by norm_num)
theorem B2252701 : Blo 1778090 2252701 := bbase (se 3 (by rfl) ⟨422381, by rfl⟩ : syracuseStep 2252701 = 844763) (by norm_num)
theorem B12173237 : Blo 1778090 12173237 := bbase (se 5 (by rfl) ⟨570620, by rfl⟩ : syracuseStep 12173237 = 1141241) (by norm_num)
theorem B1900469 : Blo 1778090 1900469 := bbase (se 5 (by rfl) ⟨89084, by rfl⟩ : syracuseStep 1900469 = 178169) (by norm_num)
theorem B3858373 : Blo 1778090 3858373 := bbase (se 4 (by rfl) ⟨361722, by rfl⟩ : syracuseStep 3858373 = 723445) (by norm_num)
theorem B7602133 : Blo 1778090 7602133 := bbase (se 7 (by rfl) ⟨89087, by rfl⟩ : syracuseStep 7602133 = 178175) (by norm_num)
theorem B7602149 : Blo 1778090 7602149 := bbase (se 4 (by rfl) ⟨712701, by rfl⟩ : syracuseStep 7602149 = 1425403) (by norm_num)
theorem B9011249 : Blo 1778090 9011249 := bstep (se 2 (by rfl) ⟨3379218, by rfl⟩ : syracuseStep 9011249 = 6758437) B6758437
theorem B5136497 : Blo 1778090 5136497 := bstep (se 2 (by rfl) ⟨1926186, by rfl⟩ : syracuseStep 5136497 = 3852373) B3852373
theorem B9003149 : Blo 1778090 9003149 := bstep (se 3 (by rfl) ⟨1688090, by rfl⟩ : syracuseStep 9003149 = 3376181) B3376181
theorem B12173453 : Blo 1778090 12173453 := bstep (se 3 (by rfl) ⟨2282522, by rfl⟩ : syracuseStep 12173453 = 4565045) B4565045
theorem B4505777 : Blo 1778090 4505777 := bstep (se 2 (by rfl) ⟨1689666, by rfl⟩ : syracuseStep 4505777 = 3379333) B3379333
theorem B9248995 : Blo 1778090 9248995 := bstep (se 1 (by rfl) ⟨6936746, by rfl⟩ : syracuseStep 9248995 = 13873493) B13873493
theorem B4505827 : Blo 1778090 4505827 := bstep (se 1 (by rfl) ⟨3379370, by rfl⟩ : syracuseStep 4505827 = 6758741) B6758741
theorem B6005069 : Blo 1778090 6005069 := bstep (se 3 (by rfl) ⟨1125950, by rfl⟩ : syracuseStep 6005069 = 2251901) B2251901
theorem B8552803 : Blo 1778090 8552803 := bstep (se 1 (by rfl) ⟨6414602, by rfl⟩ : syracuseStep 8552803 = 12829205) B12829205
theorem B6005123 : Blo 1778090 6005123 := bstep (se 1 (by rfl) ⟨4503842, by rfl⟩ : syracuseStep 6005123 = 9007685) B9007685
theorem B5136785 : Blo 1778090 5136785 := bstep (se 2 (by rfl) ⟨1926294, by rfl⟩ : syracuseStep 5136785 = 3852589) B3852589
theorem B1778099 : Blo 1778090 1778099 := bstep (se 1 (by rfl) ⟨1333574, by rfl⟩ : syracuseStep 1778099 = 2667149) B2667149
theorem B1778115 : Blo 1778090 1778115 := bstep (se 1 (by rfl) ⟨1333586, by rfl⟩ : syracuseStep 1778115 = 2667173) B2667173
theorem B1778131 : Blo 1778090 1778131 := bstep (se 1 (by rfl) ⟨1333598, by rfl⟩ : syracuseStep 1778131 = 2667197) B2667197
theorem B1778147 : Blo 1778090 1778147 := bstep (se 1 (by rfl) ⟨1333610, by rfl⟩ : syracuseStep 1778147 = 2667221) B2667221
theorem B15196643 : Blo 1778090 15196643 := bstep (se 1 (by rfl) ⟨11397482, by rfl⟩ : syracuseStep 15196643 = 22794965) B22794965
theorem B1778163 : Blo 1778090 1778163 := bstep (se 1 (by rfl) ⟨1333622, by rfl⟩ : syracuseStep 1778163 = 2667245) B2667245
theorem B1778179 : Blo 1778090 1778179 := bstep (se 1 (by rfl) ⟨1333634, by rfl⟩ : syracuseStep 1778179 = 2667269) B2667269
theorem B4276739 : Blo 1778090 4276739 := bstep (se 1 (by rfl) ⟨3207554, by rfl⟩ : syracuseStep 4276739 = 6415109) B6415109
theorem B1778195 : Blo 1778090 1778195 := bstep (se 1 (by rfl) ⟨1333646, by rfl⟩ : syracuseStep 1778195 = 2667293) B2667293
theorem B1778211 : Blo 1778090 1778211 := bstep (se 1 (by rfl) ⟨1333658, by rfl⟩ : syracuseStep 1778211 = 2667317) B2667317
theorem B3375665 : Blo 1778090 3375665 := bstep (se 2 (by rfl) ⟨1265874, by rfl⟩ : syracuseStep 3375665 = 2531749) B2531749
theorem B1778227 : Blo 1778090 1778227 := bstep (se 1 (by rfl) ⟨1333670, by rfl⟩ : syracuseStep 1778227 = 2667341) B2667341
theorem B1778243 : Blo 1778090 1778243 := bstep (se 1 (by rfl) ⟨1333682, by rfl⟩ : syracuseStep 1778243 = 2667365) B2667365
theorem B1778259 : Blo 1778090 1778259 := bstep (se 1 (by rfl) ⟨1333694, by rfl⟩ : syracuseStep 1778259 = 2667389) B2667389
theorem B1778275 : Blo 1778090 1778275 := bstep (se 1 (by rfl) ⟨1333706, by rfl⟩ : syracuseStep 1778275 = 2667413) B2667413
theorem B41067121 : Blo 1778090 41067121 := bstep (se 2 (by rfl) ⟨15400170, by rfl⟩ : syracuseStep 41067121 = 30800341) B30800341
theorem B8553073 : Blo 1778090 8553073 := bstep (se 2 (by rfl) ⟨3207402, by rfl⟩ : syracuseStep 8553073 = 6414805) B6414805
theorem B1778291 : Blo 1778090 1778291 := bstep (se 1 (by rfl) ⟨1333718, by rfl⟩ : syracuseStep 1778291 = 2667437) B2667437
theorem B1778307 : Blo 1778090 1778307 := bstep (se 1 (by rfl) ⟨1333730, by rfl⟩ : syracuseStep 1778307 = 2667461) B2667461
theorem B6005393 : Blo 1778090 6005393 := bstep (se 2 (by rfl) ⟨2252022, by rfl⟩ : syracuseStep 6005393 = 4504045) B4504045
theorem B1778323 : Blo 1778090 1778323 := bstep (se 1 (by rfl) ⟨1333742, by rfl⟩ : syracuseStep 1778323 = 2667485) B2667485
theorem B1778339 : Blo 1778090 1778339 := bstep (se 1 (by rfl) ⟨1333754, by rfl⟩ : syracuseStep 1778339 = 2667509) B2667509
theorem B10134193 : Blo 1778090 10134193 := bstep (se 2 (by rfl) ⟨3800322, by rfl⟩ : syracuseStep 10134193 = 7600645) B7600645
theorem B1778355 : Blo 1778090 1778355 := bstep (se 1 (by rfl) ⟨1333766, by rfl⟩ : syracuseStep 1778355 = 2667533) B2667533
theorem B1778371 : Blo 1778090 1778371 := bstep (se 1 (by rfl) ⟨1333778, by rfl⟩ : syracuseStep 1778371 = 2667557) B2667557
theorem B1778387 : Blo 1778090 1778387 := bstep (se 1 (by rfl) ⟨1333790, by rfl⟩ : syracuseStep 1778387 = 2667581) B2667581
theorem B1778403 : Blo 1778090 1778403 := bstep (se 1 (by rfl) ⟨1333802, by rfl⟩ : syracuseStep 1778403 = 2667605) B2667605
theorem B1778419 : Blo 1778090 1778419 := bstep (se 1 (by rfl) ⟨1333814, by rfl⟩ : syracuseStep 1778419 = 2667629) B2667629
theorem B1778435 : Blo 1778090 1778435 := bstep (se 1 (by rfl) ⟨1333826, by rfl⟩ : syracuseStep 1778435 = 2667653) B2667653
theorem B1778451 : Blo 1778090 1778451 := bstep (se 1 (by rfl) ⟨1333838, by rfl⟩ : syracuseStep 1778451 = 2667677) B2667677
theorem B1778467 : Blo 1778090 1778467 := bstep (se 1 (by rfl) ⟨1333850, by rfl⟩ : syracuseStep 1778467 = 2667701) B2667701
theorem B1778483 : Blo 1778090 1778483 := bstep (se 1 (by rfl) ⟨1333862, by rfl⟩ : syracuseStep 1778483 = 2667725) B2667725
theorem B1778499 : Blo 1778090 1778499 := bstep (se 1 (by rfl) ⟨1333874, by rfl⟩ : syracuseStep 1778499 = 2667749) B2667749
theorem B1778515 : Blo 1778090 1778515 := bstep (se 1 (by rfl) ⟨1333886, by rfl⟩ : syracuseStep 1778515 = 2667773) B2667773
theorem B1778531 : Blo 1778090 1778531 := bstep (se 1 (by rfl) ⟨1333898, by rfl⟩ : syracuseStep 1778531 = 2667797) B2667797
theorem B1778547 : Blo 1778090 1778547 := bstep (se 1 (by rfl) ⟨1333910, by rfl⟩ : syracuseStep 1778547 = 2667821) B2667821
theorem B2532227 : Blo 1778090 2532227 := bstep (se 1 (by rfl) ⟨1899170, by rfl⟩ : syracuseStep 2532227 = 3798341) B3798341
theorem B1778563 : Blo 1778090 1778563 := bstep (se 1 (by rfl) ⟨1333922, by rfl⟩ : syracuseStep 1778563 = 2667845) B2667845
theorem B3294083 : Blo 1778090 3294083 := bstep (se 1 (by rfl) ⟨2470562, by rfl⟩ : syracuseStep 3294083 = 4941125) B4941125
theorem B1778579 : Blo 1778090 1778579 := bstep (se 1 (by rfl) ⟨1333934, by rfl⟩ : syracuseStep 1778579 = 2667869) B2667869
theorem B1778595 : Blo 1778090 1778595 := bstep (se 1 (by rfl) ⟨1333946, by rfl⟩ : syracuseStep 1778595 = 2667893) B2667893
theorem B1778611 : Blo 1778090 1778611 := bstep (se 1 (by rfl) ⟨1333958, by rfl⟩ : syracuseStep 1778611 = 2667917) B2667917
theorem B1778627 : Blo 1778090 1778627 := bstep (se 1 (by rfl) ⟨1333970, by rfl⟩ : syracuseStep 1778627 = 2667941) B2667941
theorem B1778643 : Blo 1778090 1778643 := bstep (se 1 (by rfl) ⟨1333982, by rfl⟩ : syracuseStep 1778643 = 2667965) B2667965
theorem B1778659 : Blo 1778090 1778659 := bstep (se 1 (by rfl) ⟨1333994, by rfl⟩ : syracuseStep 1778659 = 2667989) B2667989
theorem B1778675 : Blo 1778090 1778675 := bstep (se 1 (by rfl) ⟨1334006, by rfl⟩ : syracuseStep 1778675 = 2668013) B2668013
theorem B2704385 : Blo 1778090 2704385 := bstep (se 2 (by rfl) ⟨1014144, by rfl⟩ : syracuseStep 2704385 = 2028289) B2028289
theorem B1778691 : Blo 1778090 1778691 := bstep (se 1 (by rfl) ⟨1334018, by rfl⟩ : syracuseStep 1778691 = 2668037) B2668037
theorem B1778707 : Blo 1778090 1778707 := bstep (se 1 (by rfl) ⟨1334030, by rfl⟩ : syracuseStep 1778707 = 2668061) B2668061
theorem B1778723 : Blo 1778090 1778723 := bstep (se 1 (by rfl) ⟨1334042, by rfl⟩ : syracuseStep 1778723 = 2668085) B2668085
theorem B5063725 : Blo 1778090 5063725 := bstep (se 3 (by rfl) ⟨949448, by rfl⟩ : syracuseStep 5063725 = 1898897) B1898897
theorem B2704433 : Blo 1778090 2704433 := bstep (se 2 (by rfl) ⟨1014162, by rfl⟩ : syracuseStep 2704433 = 2028325) B2028325
theorem B1778739 : Blo 1778090 1778739 := bstep (se 1 (by rfl) ⟨1334054, by rfl⟩ : syracuseStep 1778739 = 2668109) B2668109
theorem B4056131 : Blo 1778090 4056131 := bstep (se 1 (by rfl) ⟨3042098, by rfl⟩ : syracuseStep 4056131 = 6084197) B6084197
theorem B1778755 : Blo 1778090 1778755 := bstep (se 1 (by rfl) ⟨1334066, by rfl⟩ : syracuseStep 1778755 = 2668133) B2668133
theorem B1778771 : Blo 1778090 1778771 := bstep (se 1 (by rfl) ⟨1334078, by rfl⟩ : syracuseStep 1778771 = 2668157) B2668157
theorem B1778787 : Blo 1778090 1778787 := bstep (se 1 (by rfl) ⟨1334090, by rfl⟩ : syracuseStep 1778787 = 2668181) B2668181
theorem B1778803 : Blo 1778090 1778803 := bstep (se 1 (by rfl) ⟨1334102, by rfl⟩ : syracuseStep 1778803 = 2668205) B2668205
theorem B1778819 : Blo 1778090 1778819 := bstep (se 1 (by rfl) ⟨1334114, by rfl⟩ : syracuseStep 1778819 = 2668229) B2668229
theorem B1778835 : Blo 1778090 1778835 := bstep (se 1 (by rfl) ⟨1334126, by rfl⟩ : syracuseStep 1778835 = 2668253) B2668253
theorem B1778851 : Blo 1778090 1778851 := bstep (se 1 (by rfl) ⟨1334138, by rfl⟩ : syracuseStep 1778851 = 2668277) B2668277
theorem B6005933 : Blo 1778090 6005933 := bstep (se 3 (by rfl) ⟨1126112, by rfl⟩ : syracuseStep 6005933 = 2252225) B2252225
theorem B1778867 : Blo 1778090 1778867 := bstep (se 1 (by rfl) ⟨1334150, by rfl⟩ : syracuseStep 1778867 = 2668301) B2668301
theorem B1778883 : Blo 1778090 1778883 := bstep (se 1 (by rfl) ⟨1334162, by rfl⟩ : syracuseStep 1778883 = 2668325) B2668325
theorem B1778899 : Blo 1778090 1778899 := bstep (se 1 (by rfl) ⟨1334174, by rfl⟩ : syracuseStep 1778899 = 2668349) B2668349
theorem B1778915 : Blo 1778090 1778915 := bstep (se 1 (by rfl) ⟨1334186, by rfl⟩ : syracuseStep 1778915 = 2668373) B2668373
theorem B6005987 : Blo 1778090 6005987 := bstep (se 1 (by rfl) ⟨4504490, by rfl⟩ : syracuseStep 6005987 = 9008981) B9008981
theorem B1778931 : Blo 1778090 1778931 := bstep (se 1 (by rfl) ⟨1334198, by rfl⟩ : syracuseStep 1778931 = 2668397) B2668397
theorem B1778947 : Blo 1778090 1778947 := bstep (se 1 (by rfl) ⟨1334210, by rfl⟩ : syracuseStep 1778947 = 2668421) B2668421
theorem B5063953 : Blo 1778090 5063953 := bstep (se 2 (by rfl) ⟨1898982, by rfl⟩ : syracuseStep 5063953 = 3797965) B3797965
theorem B1778963 : Blo 1778090 1778963 := bstep (se 1 (by rfl) ⟨1334222, by rfl⟩ : syracuseStep 1778963 = 2668445) B2668445
theorem B1778979 : Blo 1778090 1778979 := bstep (se 1 (by rfl) ⟨1334234, by rfl⟩ : syracuseStep 1778979 = 2668469) B2668469
theorem B1778995 : Blo 1778090 1778995 := bstep (se 1 (by rfl) ⟨1334246, by rfl⟩ : syracuseStep 1778995 = 2668493) B2668493
theorem B1779011 : Blo 1778090 1779011 := bstep (se 1 (by rfl) ⟨1334258, by rfl⟩ : syracuseStep 1779011 = 2668517) B2668517
theorem B1779027 : Blo 1778090 1779027 := bstep (se 1 (by rfl) ⟨1334270, by rfl⟩ : syracuseStep 1779027 = 2668541) B2668541
theorem B1779043 : Blo 1778090 1779043 := bstep (se 1 (by rfl) ⟨1334282, by rfl⟩ : syracuseStep 1779043 = 2668565) B2668565
theorem B5203309 : Blo 1778090 5203309 := bstep (se 3 (by rfl) ⟨975620, by rfl⟩ : syracuseStep 5203309 = 1951241) B1951241
theorem B1779059 : Blo 1778090 1779059 := bstep (se 1 (by rfl) ⟨1334294, by rfl⟩ : syracuseStep 1779059 = 2668589) B2668589
theorem B1779075 : Blo 1778090 1779075 := bstep (se 1 (by rfl) ⟨1334306, by rfl⟩ : syracuseStep 1779075 = 2668613) B2668613
theorem B1779091 : Blo 1778090 1779091 := bstep (se 1 (by rfl) ⟨1334318, by rfl⟩ : syracuseStep 1779091 = 2668637) B2668637
theorem B1779107 : Blo 1778090 1779107 := bstep (se 1 (by rfl) ⟨1334330, by rfl⟩ : syracuseStep 1779107 = 2668661) B2668661
theorem B5064113 : Blo 1778090 5064113 := bstep (se 2 (by rfl) ⟨1899042, by rfl⟩ : syracuseStep 5064113 = 3798085) B3798085
theorem B3376561 : Blo 1778090 3376561 := bstep (se 2 (by rfl) ⟨1266210, by rfl⟩ : syracuseStep 3376561 = 2532421) B2532421
theorem B1779123 : Blo 1778090 1779123 := bstep (se 1 (by rfl) ⟨1334342, by rfl⟩ : syracuseStep 1779123 = 2668685) B2668685
theorem B1779139 : Blo 1778090 1779139 := bstep (se 1 (by rfl) ⟨1334354, by rfl⟩ : syracuseStep 1779139 = 2668709) B2668709
theorem B1779155 : Blo 1778090 1779155 := bstep (se 1 (by rfl) ⟨1334366, by rfl⟩ : syracuseStep 1779155 = 2668733) B2668733
theorem B1779171 : Blo 1778090 1779171 := bstep (se 1 (by rfl) ⟨1334378, by rfl⟩ : syracuseStep 1779171 = 2668757) B2668757
theorem B6006257 : Blo 1778090 6006257 := bstep (se 2 (by rfl) ⟨2252346, by rfl⟩ : syracuseStep 6006257 = 4504693) B4504693
theorem B2000371 : Blo 1778090 2000371 := bstep (se 1 (by rfl) ⟨1500278, by rfl⟩ : syracuseStep 2000371 = 3000557) B3000557
theorem B1779187 : Blo 1778090 1779187 := bstep (se 1 (by rfl) ⟨1334390, by rfl⟩ : syracuseStep 1779187 = 2668781) B2668781
theorem B2532865 : Blo 1778090 2532865 := bstep (se 2 (by rfl) ⟨949824, by rfl⟩ : syracuseStep 2532865 = 1899649) B1899649
theorem B1779203 : Blo 1778090 1779203 := bstep (se 1 (by rfl) ⟨1334402, by rfl⟩ : syracuseStep 1779203 = 2668805) B2668805
theorem B1779219 : Blo 1778090 1779219 := bstep (se 1 (by rfl) ⟨1334414, by rfl⟩ : syracuseStep 1779219 = 2668829) B2668829
theorem B5064227 : Blo 1778090 5064227 := bstep (se 1 (by rfl) ⟨3798170, by rfl⟩ : syracuseStep 5064227 = 7596341) B7596341
theorem B1779235 : Blo 1778090 1779235 := bstep (se 1 (by rfl) ⟨1334426, by rfl⟩ : syracuseStep 1779235 = 2668853) B2668853
theorem B1779251 : Blo 1778090 1779251 := bstep (se 1 (by rfl) ⟨1334438, by rfl⟩ : syracuseStep 1779251 = 2668877) B2668877
theorem B1779267 : Blo 1778090 1779267 := bstep (se 1 (by rfl) ⟨1334450, by rfl⟩ : syracuseStep 1779267 = 2668901) B2668901
theorem B3376721 : Blo 1778090 3376721 := bstep (se 2 (by rfl) ⟨1266270, by rfl⟩ : syracuseStep 3376721 = 2532541) B2532541
theorem B1779283 : Blo 1778090 1779283 := bstep (se 1 (by rfl) ⟨1334462, by rfl⟩ : syracuseStep 1779283 = 2668925) B2668925
theorem B1779299 : Blo 1778090 1779299 := bstep (se 1 (by rfl) ⟨1334474, by rfl⟩ : syracuseStep 1779299 = 2668949) B2668949
theorem B2532979 : Blo 1778090 2532979 := bstep (se 1 (by rfl) ⟨1899734, by rfl⟩ : syracuseStep 2532979 = 3799469) B3799469
theorem B1779315 : Blo 1778090 1779315 := bstep (se 1 (by rfl) ⟨1334486, by rfl⟩ : syracuseStep 1779315 = 2668973) B2668973
theorem B2000515 : Blo 1778090 2000515 := bstep (se 1 (by rfl) ⟨1500386, by rfl⟩ : syracuseStep 2000515 = 3000773) B3000773
theorem B1779331 : Blo 1778090 1779331 := bstep (se 1 (by rfl) ⟨1334498, by rfl⟩ : syracuseStep 1779331 = 2668997) B2668997
theorem B1779347 : Blo 1778090 1779347 := bstep (se 1 (by rfl) ⟨1334510, by rfl⟩ : syracuseStep 1779347 = 2669021) B2669021
theorem B6751907 : Blo 1778090 6751907 := bstep (se 1 (by rfl) ⟨5063930, by rfl⟩ : syracuseStep 6751907 = 10127861) B10127861
theorem B1779363 : Blo 1778090 1779363 := bstep (se 1 (by rfl) ⟨1334522, by rfl⟩ : syracuseStep 1779363 = 2669045) B2669045
theorem B1779379 : Blo 1778090 1779379 := bstep (se 1 (by rfl) ⟨1334534, by rfl⟩ : syracuseStep 1779379 = 2669069) B2669069
theorem B1779395 : Blo 1778090 1779395 := bstep (se 1 (by rfl) ⟨1334546, by rfl⟩ : syracuseStep 1779395 = 2669093) B2669093
theorem B1779411 : Blo 1778090 1779411 := bstep (se 1 (by rfl) ⟨1334558, by rfl⟩ : syracuseStep 1779411 = 2669117) B2669117
theorem B1779427 : Blo 1778090 1779427 := bstep (se 1 (by rfl) ⟨1334570, by rfl⟩ : syracuseStep 1779427 = 2669141) B2669141
theorem B4056817 : Blo 1778090 4056817 := bstep (se 2 (by rfl) ⟨1521306, by rfl⟩ : syracuseStep 4056817 = 3042613) B3042613
theorem B1779443 : Blo 1778090 1779443 := bstep (se 1 (by rfl) ⟨1334582, by rfl⟩ : syracuseStep 1779443 = 2669165) B2669165
theorem B1779459 : Blo 1778090 1779459 := bstep (se 1 (by rfl) ⟨1334594, by rfl⟩ : syracuseStep 1779459 = 2669189) B2669189
theorem B11405069 : Blo 1778090 11405069 := bstep (se 3 (by rfl) ⟨2138450, by rfl⟩ : syracuseStep 11405069 = 4276901) B4276901
theorem B2000659 : Blo 1778090 2000659 := bstep (se 1 (by rfl) ⟨1500494, by rfl⟩ : syracuseStep 2000659 = 3000989) B3000989
theorem B1779475 : Blo 1778090 1779475 := bstep (se 1 (by rfl) ⟨1334606, by rfl⟩ : syracuseStep 1779475 = 2669213) B2669213
theorem B7702307 : Blo 1778090 7702307 := bstep (se 1 (by rfl) ⟨5776730, by rfl⟩ : syracuseStep 7702307 = 11553461) B11553461
theorem B1779491 : Blo 1778090 1779491 := bstep (se 1 (by rfl) ⟨1334618, by rfl⟩ : syracuseStep 1779491 = 2669237) B2669237
theorem B1779507 : Blo 1778090 1779507 := bstep (se 1 (by rfl) ⟨1334630, by rfl⟩ : syracuseStep 1779507 = 2669261) B2669261
theorem B1779523 : Blo 1778090 1779523 := bstep (se 1 (by rfl) ⟨1334642, by rfl⟩ : syracuseStep 1779523 = 2669285) B2669285
theorem B1779539 : Blo 1778090 1779539 := bstep (se 1 (by rfl) ⟨1334654, by rfl⟩ : syracuseStep 1779539 = 2669309) B2669309
theorem B1779555 : Blo 1778090 1779555 := bstep (se 1 (by rfl) ⟨1334666, by rfl⟩ : syracuseStep 1779555 = 2669333) B2669333
theorem B1779571 : Blo 1778090 1779571 := bstep (se 1 (by rfl) ⟨1334678, by rfl⟩ : syracuseStep 1779571 = 2669357) B2669357
theorem B1779587 : Blo 1778090 1779587 := bstep (se 1 (by rfl) ⟨1334690, by rfl⟩ : syracuseStep 1779587 = 2669381) B2669381
theorem B1779603 : Blo 1778090 1779603 := bstep (se 1 (by rfl) ⟨1334702, by rfl⟩ : syracuseStep 1779603 = 2669405) B2669405
theorem B2000803 : Blo 1778090 2000803 := bstep (se 1 (by rfl) ⟨1500602, by rfl⟩ : syracuseStep 2000803 = 3001205) B3001205
theorem B1779619 : Blo 1778090 1779619 := bstep (se 1 (by rfl) ⟨1334714, by rfl⟩ : syracuseStep 1779619 = 2669429) B2669429
theorem B1779635 : Blo 1778090 1779635 := bstep (se 1 (by rfl) ⟨1334726, by rfl⟩ : syracuseStep 1779635 = 2669453) B2669453
theorem B1779651 : Blo 1778090 1779651 := bstep (se 1 (by rfl) ⟨1334738, by rfl⟩ : syracuseStep 1779651 = 2669477) B2669477
theorem B1779667 : Blo 1778090 1779667 := bstep (se 1 (by rfl) ⟨1334750, by rfl⟩ : syracuseStep 1779667 = 2669501) B2669501
theorem B3377123 : Blo 1778090 3377123 := bstep (se 1 (by rfl) ⟨2532842, by rfl⟩ : syracuseStep 3377123 = 5065685) B5065685
theorem B1779683 : Blo 1778090 1779683 := bstep (se 1 (by rfl) ⟨1334762, by rfl⟩ : syracuseStep 1779683 = 2669525) B2669525
theorem B1779699 : Blo 1778090 1779699 := bstep (se 1 (by rfl) ⟨1334774, by rfl⟩ : syracuseStep 1779699 = 2669549) B2669549
theorem B1779715 : Blo 1778090 1779715 := bstep (se 1 (by rfl) ⟨1334786, by rfl⟩ : syracuseStep 1779715 = 2669573) B2669573
theorem B11397125 : Blo 1778090 11397125 := bstep (se 4 (by rfl) ⟨1068480, by rfl⟩ : syracuseStep 11397125 = 2136961) B2136961
theorem B6006797 : Blo 1778090 6006797 := bstep (se 3 (by rfl) ⟨1126274, by rfl⟩ : syracuseStep 6006797 = 2252549) B2252549
theorem B1779731 : Blo 1778090 1779731 := bstep (se 1 (by rfl) ⟨1334798, by rfl⟩ : syracuseStep 1779731 = 2669597) B2669597
theorem B1779747 : Blo 1778090 1779747 := bstep (se 1 (by rfl) ⟨1334810, by rfl⟩ : syracuseStep 1779747 = 2669621) B2669621
theorem B2000947 : Blo 1778090 2000947 := bstep (se 1 (by rfl) ⟨1500710, by rfl⟩ : syracuseStep 2000947 = 3001421) B3001421
theorem B1779763 : Blo 1778090 1779763 := bstep (se 1 (by rfl) ⟨1334822, by rfl⟩ : syracuseStep 1779763 = 2669645) B2669645
theorem B1779779 : Blo 1778090 1779779 := bstep (se 1 (by rfl) ⟨1334834, by rfl⟩ : syracuseStep 1779779 = 2669669) B2669669
theorem B6006851 : Blo 1778090 6006851 := bstep (se 1 (by rfl) ⟨4505138, by rfl⟩ : syracuseStep 6006851 = 9010277) B9010277
theorem B10127429 : Blo 1778090 10127429 := bstep (se 4 (by rfl) ⟨949446, by rfl⟩ : syracuseStep 10127429 = 1898893) B1898893
theorem B1779795 : Blo 1778090 1779795 := bstep (se 1 (by rfl) ⟨1334846, by rfl⟩ : syracuseStep 1779795 = 2669693) B2669693
theorem B10135651 : Blo 1778090 10135651 := bstep (se 1 (by rfl) ⟨7601738, by rfl⟩ : syracuseStep 10135651 = 15203477) B15203477
theorem B1779811 : Blo 1778090 1779811 := bstep (se 1 (by rfl) ⟨1334858, by rfl⟩ : syracuseStep 1779811 = 2669717) B2669717
theorem B1779827 : Blo 1778090 1779827 := bstep (se 1 (by rfl) ⟨1334870, by rfl⟩ : syracuseStep 1779827 = 2669741) B2669741
theorem B1779843 : Blo 1778090 1779843 := bstep (se 1 (by rfl) ⟨1334882, by rfl⟩ : syracuseStep 1779843 = 2669765) B2669765
theorem B1779859 : Blo 1778090 1779859 := bstep (se 1 (by rfl) ⟨1334894, by rfl⟩ : syracuseStep 1779859 = 2669789) B2669789
theorem B1779875 : Blo 1778090 1779875 := bstep (se 1 (by rfl) ⟨1334906, by rfl⟩ : syracuseStep 1779875 = 2669813) B2669813
theorem B1779891 : Blo 1778090 1779891 := bstep (se 1 (by rfl) ⟨1334918, by rfl⟩ : syracuseStep 1779891 = 2669837) B2669837
theorem B2001091 : Blo 1778090 2001091 := bstep (se 1 (by rfl) ⟨1500818, by rfl⟩ : syracuseStep 2001091 = 3001637) B3001637
theorem B1779907 : Blo 1778090 1779907 := bstep (se 1 (by rfl) ⟨1334930, by rfl⟩ : syracuseStep 1779907 = 2669861) B2669861
theorem B1779923 : Blo 1778090 1779923 := bstep (se 1 (by rfl) ⟨1334942, by rfl⟩ : syracuseStep 1779923 = 2669885) B2669885
theorem B1779939 : Blo 1778090 1779939 := bstep (se 1 (by rfl) ⟨1334954, by rfl⟩ : syracuseStep 1779939 = 2669909) B2669909
theorem B1779955 : Blo 1778090 1779955 := bstep (se 1 (by rfl) ⟨1334966, by rfl⟩ : syracuseStep 1779955 = 2669933) B2669933
theorem B3000577 : Blo 1778090 3000577 := bstep (se 2 (by rfl) ⟨1125216, by rfl⟩ : syracuseStep 3000577 = 2250433) B2250433
theorem B1779971 : Blo 1778090 1779971 := bstep (se 1 (by rfl) ⟨1334978, by rfl⟩ : syracuseStep 1779971 = 2669957) B2669957
theorem B1779987 : Blo 1778090 1779987 := bstep (se 1 (by rfl) ⟨1334990, by rfl⟩ : syracuseStep 1779987 = 2669981) B2669981
theorem B3000611 : Blo 1778090 3000611 := bstep (se 1 (by rfl) ⟨2250458, by rfl⟩ : syracuseStep 3000611 = 4500917) B4500917
theorem B1780003 : Blo 1778090 1780003 := bstep (se 1 (by rfl) ⟨1335002, by rfl⟩ : syracuseStep 1780003 = 2670005) B2670005
theorem B1780019 : Blo 1778090 1780019 := bstep (se 1 (by rfl) ⟨1335014, by rfl⟩ : syracuseStep 1780019 = 2670029) B2670029
theorem B1780035 : Blo 1778090 1780035 := bstep (se 1 (by rfl) ⟨1335026, by rfl⟩ : syracuseStep 1780035 = 2670053) B2670053
theorem B6007121 : Blo 1778090 6007121 := bstep (se 2 (by rfl) ⟨2252670, by rfl⟩ : syracuseStep 6007121 = 4505341) B4505341
theorem B2001235 : Blo 1778090 2001235 := bstep (se 1 (by rfl) ⟨1500926, by rfl⟩ : syracuseStep 2001235 = 3001853) B3001853
theorem B1780051 : Blo 1778090 1780051 := bstep (se 1 (by rfl) ⟨1335038, by rfl⟩ : syracuseStep 1780051 = 2670077) B2670077
theorem B1780067 : Blo 1778090 1780067 := bstep (se 1 (by rfl) ⟨1335050, by rfl⟩ : syracuseStep 1780067 = 2670101) B2670101
theorem B1780083 : Blo 1778090 1780083 := bstep (se 1 (by rfl) ⟨1335062, by rfl⟩ : syracuseStep 1780083 = 2670125) B2670125
theorem B3000739 : Blo 1778090 3000739 := bstep (se 1 (by rfl) ⟨2250554, by rfl⟩ : syracuseStep 3000739 = 4501109) B4501109
theorem B4811213 : Blo 1778090 4811213 := bstep (se 3 (by rfl) ⟨902102, by rfl⟩ : syracuseStep 4811213 = 1804205) B1804205
theorem B2001379 : Blo 1778090 2001379 := bstep (se 1 (by rfl) ⟨1501034, by rfl⟩ : syracuseStep 2001379 = 3002069) B3002069
theorem B5065229 : Blo 1778090 5065229 := bstep (se 3 (by rfl) ⟨949730, by rfl⟩ : syracuseStep 5065229 = 1899461) B1899461
theorem B3000881 : Blo 1778090 3000881 := bstep (se 2 (by rfl) ⟨1125330, by rfl⟩ : syracuseStep 3000881 = 2250661) B2250661
theorem B4811341 : Blo 1778090 4811341 := bstep (se 3 (by rfl) ⟨902126, by rfl⟩ : syracuseStep 4811341 = 1804253) B1804253
theorem B10136177 : Blo 1778090 10136177 := bstep (se 2 (by rfl) ⟨3801066, by rfl⟩ : syracuseStep 10136177 = 7602133) B7602133
theorem B2001523 : Blo 1778090 2001523 := bstep (se 1 (by rfl) ⟨1501142, by rfl⟩ : syracuseStep 2001523 = 3002285) B3002285
theorem B6752909 : Blo 1778090 6752909 := bstep (se 3 (by rfl) ⟨1266170, by rfl⟩ : syracuseStep 6752909 = 2532341) B2532341
theorem B3001009 : Blo 1778090 3001009 := bstep (se 2 (by rfl) ⟨1125378, by rfl⟩ : syracuseStep 3001009 = 2250757) B2250757
theorem B5065411 : Blo 1778090 5065411 := bstep (se 1 (by rfl) ⟨3799058, by rfl⟩ : syracuseStep 5065411 = 7598117) B7598117
theorem B17091269 : Blo 1778090 17091269 := bstep (se 4 (by rfl) ⟨1602306, by rfl⟩ : syracuseStep 17091269 = 3204613) B3204613
theorem B3001043 : Blo 1778090 3001043 := bstep (se 1 (by rfl) ⟨2250782, by rfl⟩ : syracuseStep 3001043 = 4501565) B4501565
theorem B2312915 : Blo 1778090 2312915 := bstep (se 1 (by rfl) ⟨1734686, by rfl⟩ : syracuseStep 2312915 = 3469373) B3469373
theorem B3607267 : Blo 1778090 3607267 := bstep (se 1 (by rfl) ⟨2705450, by rfl⟩ : syracuseStep 3607267 = 5410901) B5410901
theorem B5778157 : Blo 1778090 5778157 := bstep (se 3 (by rfl) ⟨1083404, by rfl⟩ : syracuseStep 5778157 = 2166809) B2166809
theorem B2001667 : Blo 1778090 2001667 := bstep (se 1 (by rfl) ⟨1501250, by rfl⟩ : syracuseStep 2001667 = 3002501) B3002501
theorem B4811537 : Blo 1778090 4811537 := bstep (se 2 (by rfl) ⟨1804326, by rfl⟩ : syracuseStep 4811537 = 3608653) B3608653
theorem B3001171 : Blo 1778090 3001171 := bstep (se 1 (by rfl) ⟨2250878, by rfl⟩ : syracuseStep 3001171 = 4501757) B4501757
theorem B5065571 : Blo 1778090 5065571 := bstep (se 1 (by rfl) ⟨3799178, by rfl⟩ : syracuseStep 5065571 = 7598357) B7598357
theorem B3378019 : Blo 1778090 3378019 := bstep (se 1 (by rfl) ⟨2533514, by rfl⟩ : syracuseStep 3378019 = 5067029) B5067029
theorem B6007661 : Blo 1778090 6007661 := bstep (se 3 (by rfl) ⟨1126436, by rfl⟩ : syracuseStep 6007661 = 2252873) B2252873
theorem B10972037 : Blo 1778090 10972037 := bstep (se 4 (by rfl) ⟨1028628, by rfl⟩ : syracuseStep 10972037 = 2057257) B2057257
theorem B2403217 : Blo 1778090 2403217 := bstep (se 2 (by rfl) ⟨901206, by rfl⟩ : syracuseStep 2403217 = 1802413) B1802413
theorem B2001811 : Blo 1778090 2001811 := bstep (se 1 (by rfl) ⟨1501358, by rfl⟩ : syracuseStep 2001811 = 3002717) B3002717
theorem B6007715 : Blo 1778090 6007715 := bstep (se 1 (by rfl) ⟨4505786, by rfl⟩ : syracuseStep 6007715 = 9011573) B9011573
theorem B2534323 : Blo 1778090 2534323 := bstep (se 1 (by rfl) ⟨1900742, by rfl⟩ : syracuseStep 2534323 = 3801485) B3801485
theorem B2706355 : Blo 1778090 2706355 := bstep (se 1 (by rfl) ⟨2029766, by rfl⟩ : syracuseStep 2706355 = 4059533) B4059533
theorem B5409731 : Blo 1778090 5409731 := bstep (se 1 (by rfl) ⟨4057298, by rfl⟩ : syracuseStep 5409731 = 8114597) B8114597
theorem B3001313 : Blo 1778090 3001313 := bstep (se 2 (by rfl) ⟨1125492, by rfl⟩ : syracuseStep 3001313 = 2250985) B2250985
theorem B9006065 : Blo 1778090 9006065 := bstep (se 2 (by rfl) ⟨3377274, by rfl⟩ : syracuseStep 9006065 = 6754549) B6754549
theorem B3378179 : Blo 1778090 3378179 := bstep (se 1 (by rfl) ⟨2533634, by rfl⟩ : syracuseStep 3378179 = 5067269) B5067269
theorem B7597091 : Blo 1778090 7597091 := bstep (se 1 (by rfl) ⟨5697818, by rfl⟩ : syracuseStep 7597091 = 11395637) B11395637
theorem B2001955 : Blo 1778090 2001955 := bstep (se 1 (by rfl) ⟨1501466, by rfl⟩ : syracuseStep 2001955 = 3002933) B3002933
theorem B5409841 : Blo 1778090 5409841 := bstep (se 2 (by rfl) ⟨2028690, by rfl⟩ : syracuseStep 5409841 = 4057381) B4057381
theorem B3001441 : Blo 1778090 3001441 := bstep (se 2 (by rfl) ⟨1125540, by rfl⟩ : syracuseStep 3001441 = 2251081) B2251081
theorem B3001475 : Blo 1778090 3001475 := bstep (se 1 (by rfl) ⟨2251106, by rfl⟩ : syracuseStep 3001475 = 4502213) B4502213
theorem B4000913 : Blo 1778090 4000913 := bstep (se 2 (by rfl) ⟨1500342, by rfl⟩ : syracuseStep 4000913 = 3000685) B3000685
theorem B4000931 : Blo 1778090 4000931 := bstep (se 1 (by rfl) ⟨3000698, by rfl⟩ : syracuseStep 4000931 = 6001397) B6001397
theorem B2002099 : Blo 1778090 2002099 := bstep (se 1 (by rfl) ⟨1501574, by rfl⟩ : syracuseStep 2002099 = 3003149) B3003149
theorem B3001603 : Blo 1778090 3001603 := bstep (se 1 (by rfl) ⟨2251202, by rfl⟩ : syracuseStep 3001603 = 4502405) B4502405
theorem B2002243 : Blo 1778090 2002243 := bstep (se 1 (by rfl) ⟨1501682, by rfl⟩ : syracuseStep 2002243 = 3003365) B3003365
theorem B3001745 : Blo 1778090 3001745 := bstep (se 2 (by rfl) ⟨1125654, by rfl⟩ : syracuseStep 3001745 = 2251309) B2251309
theorem B4001201 : Blo 1778090 4001201 := bstep (se 2 (by rfl) ⟨1500450, by rfl⟩ : syracuseStep 4001201 = 3000901) B3000901
theorem B4001219 : Blo 1778090 4001219 := bstep (se 1 (by rfl) ⟨3000914, by rfl⟩ : syracuseStep 4001219 = 6001829) B6001829
theorem B2002387 : Blo 1778090 2002387 := bstep (se 1 (by rfl) ⟨1501790, by rfl⟩ : syracuseStep 2002387 = 3003581) B3003581
theorem B3001873 : Blo 1778090 3001873 := bstep (se 2 (by rfl) ⟨1125702, by rfl⟩ : syracuseStep 3001873 = 2251405) B2251405
theorem B3001907 : Blo 1778090 3001907 := bstep (se 1 (by rfl) ⟨2251430, by rfl⟩ : syracuseStep 3001907 = 4502861) B4502861
theorem B5697101 : Blo 1778090 5697101 := bstep (se 3 (by rfl) ⟨1068206, by rfl⟩ : syracuseStep 5697101 = 2136413) B2136413
theorem B2002531 : Blo 1778090 2002531 := bstep (se 1 (by rfl) ⟨1501898, by rfl⟩ : syracuseStep 2002531 = 3003797) B3003797
theorem B25636493 : Blo 1778090 25636493 := bstep (se 3 (by rfl) ⟨4806842, by rfl⟩ : syracuseStep 25636493 = 9613685) B9613685
theorem B6500017 : Blo 1778090 6500017 := bstep (se 2 (by rfl) ⟨2437506, by rfl⟩ : syracuseStep 6500017 = 4875013) B4875013
theorem B3002035 : Blo 1778090 3002035 := bstep (se 1 (by rfl) ⟨2251526, by rfl⟩ : syracuseStep 3002035 = 4503053) B4503053
theorem B4001489 : Blo 1778090 4001489 := bstep (se 2 (by rfl) ⟨1500558, by rfl⟩ : syracuseStep 4001489 = 3001117) B3001117
theorem B4001507 : Blo 1778090 4001507 := bstep (se 1 (by rfl) ⟨3001130, by rfl⟩ : syracuseStep 4001507 = 6002261) B6002261
theorem B48680675 : Blo 1778090 48680675 := bstep (se 1 (by rfl) ⟨36510506, by rfl⟩ : syracuseStep 48680675 = 73021013) B73021013
theorem B3002177 : Blo 1778090 3002177 := bstep (se 2 (by rfl) ⟨1125816, by rfl⟩ : syracuseStep 3002177 = 2251633) B2251633
theorem B5066641 : Blo 1778090 5066641 := bstep (se 2 (by rfl) ⟨1899990, by rfl⟩ : syracuseStep 5066641 = 3799981) B3799981
theorem B2887571 : Blo 1778090 2887571 := bstep (se 1 (by rfl) ⟨2165678, by rfl⟩ : syracuseStep 2887571 = 4331357) B4331357
theorem B3002305 : Blo 1778090 3002305 := bstep (se 2 (by rfl) ⟨1125864, by rfl⟩ : syracuseStep 3002305 = 2251729) B2251729
theorem B3002339 : Blo 1778090 3002339 := bstep (se 1 (by rfl) ⟨2251754, by rfl⟩ : syracuseStep 3002339 = 4503509) B4503509
theorem B4001777 : Blo 1778090 4001777 := bstep (se 2 (by rfl) ⟨1500666, by rfl⟩ : syracuseStep 4001777 = 3001333) B3001333
theorem B4001795 : Blo 1778090 4001795 := bstep (se 1 (by rfl) ⟨3001346, by rfl⟩ : syracuseStep 4001795 = 6002693) B6002693
theorem B10137635 : Blo 1778090 10137635 := bstep (se 1 (by rfl) ⟨7603226, by rfl⟩ : syracuseStep 10137635 = 15206453) B15206453
theorem B3379249 : Blo 1778090 3379249 := bstep (se 2 (by rfl) ⟨1267218, by rfl⟩ : syracuseStep 3379249 = 2534437) B2534437
theorem B3002467 : Blo 1778090 3002467 := bstep (se 1 (by rfl) ⟨2251850, by rfl⟩ : syracuseStep 3002467 = 4503701) B4503701
theorem B14422157 : Blo 1778090 14422157 := bstep (se 3 (by rfl) ⟨2704154, by rfl⟩ : syracuseStep 14422157 = 5408309) B5408309
theorem B7213283 : Blo 1778090 7213283 := bstep (se 1 (by rfl) ⟨5409962, by rfl⟩ : syracuseStep 7213283 = 10819925) B10819925
theorem B3002609 : Blo 1778090 3002609 := bstep (se 2 (by rfl) ⟨1125978, by rfl⟩ : syracuseStep 3002609 = 2251957) B2251957
theorem B16453901 : Blo 1778090 16453901 := bstep (se 3 (by rfl) ⟨3085106, by rfl⟩ : syracuseStep 16453901 = 6170213) B6170213
theorem B4501777 : Blo 1778090 4501777 := bstep (se 2 (by rfl) ⟨1688166, by rfl⟩ : syracuseStep 4501777 = 3376333) B3376333
theorem B4002065 : Blo 1778090 4002065 := bstep (se 2 (by rfl) ⟨1500774, by rfl⟩ : syracuseStep 4002065 = 3001549) B3001549
theorem B4002083 : Blo 1778090 4002083 := bstep (se 1 (by rfl) ⟨3001562, by rfl⟩ : syracuseStep 4002083 = 6003125) B6003125
theorem B3002737 : Blo 1778090 3002737 := bstep (se 2 (by rfl) ⟨1126026, by rfl⟩ : syracuseStep 3002737 = 2252053) B2252053
theorem B2568577 : Blo 1778090 2568577 := bstep (se 2 (by rfl) ⟨963216, by rfl⟩ : syracuseStep 2568577 = 1926433) B1926433
theorem B3002771 : Blo 1778090 3002771 := bstep (se 1 (by rfl) ⟨2252078, by rfl⟩ : syracuseStep 3002771 = 4504157) B4504157
theorem B9007523 : Blo 1778090 9007523 := bstep (se 1 (by rfl) ⟨6755642, by rfl⟩ : syracuseStep 9007523 = 13511285) B13511285
theorem B6001073 : Blo 1778090 6001073 := bstep (se 2 (by rfl) ⟨2250402, by rfl⟩ : syracuseStep 6001073 = 4500805) B4500805
theorem B23097869 : Blo 1778090 23097869 := bstep (se 3 (by rfl) ⟨4330850, by rfl⟩ : syracuseStep 23097869 = 8661701) B8661701
theorem B13513229 : Blo 1778090 13513229 := bstep (se 3 (by rfl) ⟨2533730, by rfl⟩ : syracuseStep 13513229 = 5067461) B5067461
theorem B3002899 : Blo 1778090 3002899 := bstep (se 1 (by rfl) ⟨2252174, by rfl⟩ : syracuseStep 3002899 = 4504349) B4504349
theorem B4502051 : Blo 1778090 4502051 := bstep (se 1 (by rfl) ⟨3376538, by rfl⟩ : syracuseStep 4502051 = 6753077) B6753077
theorem B4002353 : Blo 1778090 4002353 := bstep (se 2 (by rfl) ⟨1500882, by rfl⟩ : syracuseStep 4002353 = 3001765) B3001765
theorem B4002371 : Blo 1778090 4002371 := bstep (se 1 (by rfl) ⟨3001778, by rfl⟩ : syracuseStep 4002371 = 6003557) B6003557
theorem B6083171 : Blo 1778090 6083171 := bstep (se 1 (by rfl) ⟨4562378, by rfl⟩ : syracuseStep 6083171 = 9124757) B9124757
theorem B2667137 : Blo 1778090 2667137 := bstep (se 2 (by rfl) ⟨1000176, by rfl⟩ : syracuseStep 2667137 = 2000353) B2000353
theorem B2667155 : Blo 1778090 2667155 := bstep (se 1 (by rfl) ⟨2000366, by rfl⟩ : syracuseStep 2667155 = 4000733) B4000733
theorem B3003041 : Blo 1778090 3003041 := bstep (se 2 (by rfl) ⟨1126140, by rfl⟩ : syracuseStep 3003041 = 2252281) B2252281
theorem B2667185 : Blo 1778090 2667185 := bstep (se 2 (by rfl) ⟨1000194, by rfl⟩ : syracuseStep 2667185 = 2000389) B2000389
theorem B2667203 : Blo 1778090 2667203 := bstep (se 1 (by rfl) ⟨2000402, by rfl⟩ : syracuseStep 2667203 = 4000805) B4000805
theorem B6755021 : Blo 1778090 6755021 := bstep (se 3 (by rfl) ⟨1266566, by rfl⟩ : syracuseStep 6755021 = 2533133) B2533133
theorem B2282195 : Blo 1778090 2282195 := bstep (se 1 (by rfl) ⟨1711646, by rfl⟩ : syracuseStep 2282195 = 3423293) B3423293
theorem B2667233 : Blo 1778090 2667233 := bstep (se 2 (by rfl) ⟨1000212, by rfl⟩ : syracuseStep 2667233 = 2000425) B2000425
theorem B4502243 : Blo 1778090 4502243 := bstep (se 1 (by rfl) ⟨3376682, by rfl⟩ : syracuseStep 4502243 = 6753365) B6753365
theorem B2667251 : Blo 1778090 2667251 := bstep (se 1 (by rfl) ⟨2000438, by rfl⟩ : syracuseStep 2667251 = 4000877) B4000877
theorem B2667281 : Blo 1778090 2667281 := bstep (se 2 (by rfl) ⟨1000230, by rfl⟩ : syracuseStep 2667281 = 2000461) B2000461
theorem B3003169 : Blo 1778090 3003169 := bstep (se 2 (by rfl) ⟨1126188, by rfl⟩ : syracuseStep 3003169 = 2252377) B2252377
theorem B2667299 : Blo 1778090 2667299 := bstep (se 1 (by rfl) ⟨2000474, by rfl⟩ : syracuseStep 2667299 = 4000949) B4000949
theorem B2667329 : Blo 1778090 2667329 := bstep (se 2 (by rfl) ⟨1000248, by rfl⟩ : syracuseStep 2667329 = 2000497) B2000497
theorem B3003203 : Blo 1778090 3003203 := bstep (se 1 (by rfl) ⟨2252402, by rfl⟩ : syracuseStep 3003203 = 4504805) B4504805
theorem B4002641 : Blo 1778090 4002641 := bstep (se 2 (by rfl) ⟨1500990, by rfl⟩ : syracuseStep 4002641 = 3001981) B3001981
theorem B2667347 : Blo 1778090 2667347 := bstep (se 1 (by rfl) ⟨2000510, by rfl⟩ : syracuseStep 2667347 = 4001021) B4001021
theorem B4002659 : Blo 1778090 4002659 := bstep (se 1 (by rfl) ⟨3001994, by rfl⟩ : syracuseStep 4002659 = 6003989) B6003989
theorem B2667377 : Blo 1778090 2667377 := bstep (se 2 (by rfl) ⟨1000266, by rfl⟩ : syracuseStep 2667377 = 2000533) B2000533
theorem B28865393 : Blo 1778090 28865393 := bstep (se 2 (by rfl) ⟨10824522, by rfl⟩ : syracuseStep 28865393 = 21649045) B21649045
theorem B2667395 : Blo 1778090 2667395 := bstep (se 1 (by rfl) ⟨2000546, by rfl⟩ : syracuseStep 2667395 = 4001093) B4001093
theorem B2667425 : Blo 1778090 2667425 := bstep (se 2 (by rfl) ⟨1000284, by rfl⟩ : syracuseStep 2667425 = 2000569) B2000569
theorem B3797923 : Blo 1778090 3797923 := bstep (se 1 (by rfl) ⟨2848442, by rfl⟩ : syracuseStep 3797923 = 5696885) B5696885
theorem B2667443 : Blo 1778090 2667443 := bstep (se 1 (by rfl) ⟨2000582, by rfl⟩ : syracuseStep 2667443 = 4001165) B4001165
theorem B3003331 : Blo 1778090 3003331 := bstep (se 1 (by rfl) ⟨2252498, by rfl⟩ : syracuseStep 3003331 = 4504997) B4504997
theorem B6001613 : Blo 1778090 6001613 := bstep (se 3 (by rfl) ⟨1125302, by rfl⟩ : syracuseStep 6001613 = 2250605) B2250605
theorem B8336333 : Blo 1778090 8336333 := bstep (se 3 (by rfl) ⟨1563062, by rfl⟩ : syracuseStep 8336333 = 3126125) B3126125
theorem B2667473 : Blo 1778090 2667473 := bstep (se 2 (by rfl) ⟨1000302, by rfl⟩ : syracuseStep 2667473 = 2000605) B2000605
theorem B2667491 : Blo 1778090 2667491 := bstep (se 1 (by rfl) ⟨2000618, by rfl⟩ : syracuseStep 2667491 = 4001237) B4001237
theorem B2667521 : Blo 1778090 2667521 := bstep (se 2 (by rfl) ⟨1000320, by rfl⟩ : syracuseStep 2667521 = 2000641) B2000641
theorem B6001667 : Blo 1778090 6001667 := bstep (se 1 (by rfl) ⟨4501250, by rfl⟩ : syracuseStep 6001667 = 9002501) B9002501
theorem B2667539 : Blo 1778090 2667539 := bstep (se 1 (by rfl) ⟨2000654, by rfl⟩ : syracuseStep 2667539 = 4001309) B4001309
theorem B2667569 : Blo 1778090 2667569 := bstep (se 2 (by rfl) ⟨1000338, by rfl⟩ : syracuseStep 2667569 = 2000677) B2000677
theorem B2667587 : Blo 1778090 2667587 := bstep (se 1 (by rfl) ⟨2000690, by rfl⟩ : syracuseStep 2667587 = 4001381) B4001381
theorem B3003473 : Blo 1778090 3003473 := bstep (se 2 (by rfl) ⟨1126302, by rfl⟩ : syracuseStep 3003473 = 2252605) B2252605
theorem B2667617 : Blo 1778090 2667617 := bstep (se 2 (by rfl) ⟨1000356, by rfl⟩ : syracuseStep 2667617 = 2000713) B2000713
theorem B4002929 : Blo 1778090 4002929 := bstep (se 2 (by rfl) ⟨1501098, by rfl⟩ : syracuseStep 4002929 = 3002197) B3002197
theorem B2667635 : Blo 1778090 2667635 := bstep (se 1 (by rfl) ⟨2000726, by rfl⟩ : syracuseStep 2667635 = 4001453) B4001453
theorem B4002947 : Blo 1778090 4002947 := bstep (se 1 (by rfl) ⟨3002210, by rfl⟩ : syracuseStep 4002947 = 6004421) B6004421
theorem B5411971 : Blo 1778090 5411971 := bstep (se 1 (by rfl) ⟨4058978, by rfl⟩ : syracuseStep 5411971 = 8117957) B8117957
theorem B5067917 : Blo 1778090 5067917 := bstep (se 3 (by rfl) ⟨950234, by rfl⟩ : syracuseStep 5067917 = 1900469) B1900469
theorem B2667665 : Blo 1778090 2667665 := bstep (se 2 (by rfl) ⟨1000374, by rfl⟩ : syracuseStep 2667665 = 2000749) B2000749
theorem B3044513 : Blo 1778090 3044513 := bstep (se 2 (by rfl) ⟨1141692, by rfl⟩ : syracuseStep 3044513 = 2283385) B2283385
theorem B2667683 : Blo 1778090 2667683 := bstep (se 1 (by rfl) ⟨2000762, by rfl⟩ : syracuseStep 2667683 = 4001525) B4001525
theorem B2667713 : Blo 1778090 2667713 := bstep (se 2 (by rfl) ⟨1000392, by rfl⟩ : syracuseStep 2667713 = 2000785) B2000785
theorem B9008333 : Blo 1778090 9008333 := bstep (se 3 (by rfl) ⟨1689062, by rfl⟩ : syracuseStep 9008333 = 3378125) B3378125
theorem B3003601 : Blo 1778090 3003601 := bstep (se 2 (by rfl) ⟨1126350, by rfl⟩ : syracuseStep 3003601 = 2252701) B2252701
theorem B2667731 : Blo 1778090 2667731 := bstep (se 1 (by rfl) ⟨2000798, by rfl⟩ : syracuseStep 2667731 = 4001597) B4001597
theorem B2667761 : Blo 1778090 2667761 := bstep (se 2 (by rfl) ⟨1000410, by rfl⟩ : syracuseStep 2667761 = 2000821) B2000821
theorem B7214321 : Blo 1778090 7214321 := bstep (se 2 (by rfl) ⟨2705370, by rfl⟩ : syracuseStep 7214321 = 5410741) B5410741
theorem B3003635 : Blo 1778090 3003635 := bstep (se 1 (by rfl) ⟨2252726, by rfl⟩ : syracuseStep 3003635 = 4505453) B4505453
theorem B2667779 : Blo 1778090 2667779 := bstep (se 1 (by rfl) ⟨2000834, by rfl⟩ : syracuseStep 2667779 = 4001669) B4001669
theorem B6001937 : Blo 1778090 6001937 := bstep (se 2 (by rfl) ⟨2250726, by rfl⟩ : syracuseStep 6001937 = 4501453) B4501453
theorem B2667809 : Blo 1778090 2667809 := bstep (se 2 (by rfl) ⟨1000428, by rfl⟩ : syracuseStep 2667809 = 2000857) B2000857
theorem B8115491 : Blo 1778090 8115491 := bstep (se 1 (by rfl) ⟨6086618, by rfl⟩ : syracuseStep 8115491 = 12173237) B12173237
theorem B2667827 : Blo 1778090 2667827 := bstep (se 1 (by rfl) ⟨2000870, by rfl⟩ : syracuseStep 2667827 = 4001741) B4001741
theorem B5068099 : Blo 1778090 5068099 := bstep (se 1 (by rfl) ⟨3801074, by rfl⟩ : syracuseStep 5068099 = 7602149) B7602149
theorem B2667857 : Blo 1778090 2667857 := bstep (se 2 (by rfl) ⟨1000446, by rfl⟩ : syracuseStep 2667857 = 2000893) B2000893
theorem B2028883 : Blo 1778090 2028883 := bstep (se 1 (by rfl) ⟨1521662, by rfl⟩ : syracuseStep 2028883 = 3043325) B3043325
theorem B2667875 : Blo 1778090 2667875 := bstep (se 1 (by rfl) ⟨2000906, by rfl⟩ : syracuseStep 2667875 = 4001813) B4001813
theorem B2282851 : Blo 1778090 2282851 := bstep (se 1 (by rfl) ⟨1712138, by rfl⟩ : syracuseStep 2282851 = 3424277) B3424277
theorem B5068145 : Blo 1778090 5068145 := bstep (se 2 (by rfl) ⟨1900554, by rfl⟩ : syracuseStep 5068145 = 3801109) B3801109
theorem B3003763 : Blo 1778090 3003763 := bstep (se 1 (by rfl) ⟨2252822, by rfl⟩ : syracuseStep 3003763 = 4505645) B4505645
theorem B2667905 : Blo 1778090 2667905 := bstep (se 2 (by rfl) ⟨1000464, by rfl⟩ : syracuseStep 2667905 = 2000929) B2000929
theorem B4003217 : Blo 1778090 4003217 := bstep (se 2 (by rfl) ⟨1501206, by rfl⟩ : syracuseStep 4003217 = 3002413) B3002413
theorem B2667923 : Blo 1778090 2667923 := bstep (se 1 (by rfl) ⟨2000942, by rfl⟩ : syracuseStep 2667923 = 4001885) B4001885
theorem B4003235 : Blo 1778090 4003235 := bstep (se 1 (by rfl) ⟨3002426, by rfl⟩ : syracuseStep 4003235 = 6004853) B6004853
theorem B2667953 : Blo 1778090 2667953 := bstep (se 2 (by rfl) ⟨1000482, by rfl⟩ : syracuseStep 2667953 = 2000965) B2000965
theorem B9254321 : Blo 1778090 9254321 := bstep (se 2 (by rfl) ⟨3470370, by rfl⟩ : syracuseStep 9254321 = 6940741) B6940741
theorem B2667971 : Blo 1778090 2667971 := bstep (se 1 (by rfl) ⟨2000978, by rfl⟩ : syracuseStep 2667971 = 4001957) B4001957
theorem B2668001 : Blo 1778090 2668001 := bstep (se 2 (by rfl) ⟨1000500, by rfl⟩ : syracuseStep 2668001 = 2001001) B2001001
theorem B6755825 : Blo 1778090 6755825 := bstep (se 2 (by rfl) ⟨2533434, by rfl⟩ : syracuseStep 6755825 = 5066869) B5066869
theorem B2668019 : Blo 1778090 2668019 := bstep (se 1 (by rfl) ⟨2001014, by rfl⟩ : syracuseStep 2668019 = 4002029) B4002029
theorem B2668049 : Blo 1778090 2668049 := bstep (se 2 (by rfl) ⟨1000518, by rfl⟩ : syracuseStep 2668049 = 2001037) B2001037
theorem B2668067 : Blo 1778090 2668067 := bstep (se 1 (by rfl) ⟨2001050, by rfl⟩ : syracuseStep 2668067 = 4002101) B4002101
theorem B2668097 : Blo 1778090 2668097 := bstep (se 2 (by rfl) ⟨1000536, by rfl⟩ : syracuseStep 2668097 = 2001073) B2001073
theorem B2668115 : Blo 1778090 2668115 := bstep (se 1 (by rfl) ⟨2001086, by rfl⟩ : syracuseStep 2668115 = 4002173) B4002173
theorem B2668145 : Blo 1778090 2668145 := bstep (se 2 (by rfl) ⟨1000554, by rfl⟩ : syracuseStep 2668145 = 2001109) B2001109
theorem B18257521 : Blo 1778090 18257521 := bstep (se 2 (by rfl) ⟨6846570, by rfl⟩ : syracuseStep 18257521 = 13693141) B13693141
theorem B2668163 : Blo 1778090 2668163 := bstep (se 1 (by rfl) ⟨2001122, by rfl⟩ : syracuseStep 2668163 = 4002245) B4002245
theorem B7599757 : Blo 1778090 7599757 := bstep (se 3 (by rfl) ⟨1424954, by rfl⟩ : syracuseStep 7599757 = 2849909) B2849909
theorem B4503185 : Blo 1778090 4503185 := bstep (se 2 (by rfl) ⟨1688694, by rfl⟩ : syracuseStep 4503185 = 3377389) B3377389
theorem B2668193 : Blo 1778090 2668193 := bstep (se 2 (by rfl) ⟨1000572, by rfl⟩ : syracuseStep 2668193 = 2001145) B2001145
theorem B4003505 : Blo 1778090 4003505 := bstep (se 2 (by rfl) ⟨1501314, by rfl⟩ : syracuseStep 4003505 = 3002629) B3002629
theorem B2668211 : Blo 1778090 2668211 := bstep (se 1 (by rfl) ⟨2001158, by rfl⟩ : syracuseStep 2668211 = 4002317) B4002317
theorem B4503235 : Blo 1778090 4503235 := bstep (se 1 (by rfl) ⟨3377426, by rfl⟩ : syracuseStep 4503235 = 6754853) B6754853
theorem B4003523 : Blo 1778090 4003523 := bstep (se 1 (by rfl) ⟨3002642, by rfl⟩ : syracuseStep 4003523 = 6005285) B6005285
theorem B9623245 : Blo 1778090 9623245 := bstep (se 3 (by rfl) ⟨1804358, by rfl⟩ : syracuseStep 9623245 = 3608717) B3608717
theorem B2668241 : Blo 1778090 2668241 := bstep (se 2 (by rfl) ⟨1000590, by rfl⟩ : syracuseStep 2668241 = 2001181) B2001181
theorem B5699281 : Blo 1778090 5699281 := bstep (se 2 (by rfl) ⟨2137230, by rfl⟩ : syracuseStep 5699281 = 4274461) B4274461
theorem B2668259 : Blo 1778090 2668259 := bstep (se 1 (by rfl) ⟨2001194, by rfl⟩ : syracuseStep 2668259 = 4002389) B4002389
theorem B2668289 : Blo 1778090 2668289 := bstep (se 2 (by rfl) ⟨1000608, by rfl⟩ : syracuseStep 2668289 = 2001217) B2001217
theorem B2250499 : Blo 1778090 2250499 := bstep (se 1 (by rfl) ⟨1687874, by rfl⟩ : syracuseStep 2250499 = 3375749) B3375749
theorem B2668307 : Blo 1778090 2668307 := bstep (se 1 (by rfl) ⟨2001230, by rfl⟩ : syracuseStep 2668307 = 4002461) B4002461
theorem B6002477 : Blo 1778090 6002477 := bstep (se 3 (by rfl) ⟨1125464, by rfl⟩ : syracuseStep 6002477 = 2250929) B2250929
theorem B2668337 : Blo 1778090 2668337 := bstep (se 2 (by rfl) ⟨1000626, by rfl⟩ : syracuseStep 2668337 = 2001253) B2001253
theorem B2668355 : Blo 1778090 2668355 := bstep (se 1 (by rfl) ⟨2001266, by rfl⟩ : syracuseStep 2668355 = 4002533) B4002533
theorem B10131277 : Blo 1778090 10131277 := bstep (se 3 (by rfl) ⟨1899614, by rfl⟩ : syracuseStep 10131277 = 3799229) B3799229
theorem B4503377 : Blo 1778090 4503377 := bstep (se 2 (by rfl) ⟨1688766, by rfl⟩ : syracuseStep 4503377 = 3377533) B3377533
theorem B5412689 : Blo 1778090 5412689 := bstep (se 2 (by rfl) ⟨2029758, by rfl⟩ : syracuseStep 5412689 = 4059517) B4059517
theorem B2668385 : Blo 1778090 2668385 := bstep (se 2 (by rfl) ⟨1000644, by rfl⟩ : syracuseStep 2668385 = 2001289) B2001289
theorem B2250595 : Blo 1778090 2250595 := bstep (se 1 (by rfl) ⟨1687946, by rfl⟩ : syracuseStep 2250595 = 3375893) B3375893
theorem B6002531 : Blo 1778090 6002531 := bstep (se 1 (by rfl) ⟨4501898, by rfl⟩ : syracuseStep 6002531 = 9003797) B9003797
theorem B11401073 : Blo 1778090 11401073 := bstep (se 2 (by rfl) ⟨4275402, by rfl⟩ : syracuseStep 11401073 = 8550805) B8550805
theorem B2668403 : Blo 1778090 2668403 := bstep (se 1 (by rfl) ⟨2001302, by rfl⟩ : syracuseStep 2668403 = 4002605) B4002605
theorem B5699459 : Blo 1778090 5699459 := bstep (se 1 (by rfl) ⟨4274594, by rfl⟩ : syracuseStep 5699459 = 8549189) B8549189
theorem B2668433 : Blo 1778090 2668433 := bstep (se 2 (by rfl) ⟨1000662, by rfl⟩ : syracuseStep 2668433 = 2001325) B2001325
theorem B2668451 : Blo 1778090 2668451 := bstep (se 1 (by rfl) ⟨2001338, by rfl⟩ : syracuseStep 2668451 = 4002677) B4002677
theorem B9131939 : Blo 1778090 9131939 := bstep (se 1 (by rfl) ⟨6848954, by rfl⟩ : syracuseStep 9131939 = 13697909) B13697909
theorem B2668481 : Blo 1778090 2668481 := bstep (se 2 (by rfl) ⟨1000680, by rfl⟩ : syracuseStep 2668481 = 2001361) B2001361
theorem B11392973 : Blo 1778090 11392973 := bstep (se 3 (by rfl) ⟨2136182, by rfl⟩ : syracuseStep 11392973 = 4272365) B4272365
theorem B4003793 : Blo 1778090 4003793 := bstep (se 2 (by rfl) ⟨1501422, by rfl⟩ : syracuseStep 4003793 = 3002845) B3002845
theorem B2668499 : Blo 1778090 2668499 := bstep (se 1 (by rfl) ⟨2001374, by rfl⟩ : syracuseStep 2668499 = 4002749) B4002749
theorem B4003811 : Blo 1778090 4003811 := bstep (se 1 (by rfl) ⟨3002858, by rfl⟩ : syracuseStep 4003811 = 6005717) B6005717
theorem B2668529 : Blo 1778090 2668529 := bstep (se 2 (by rfl) ⟨1000698, by rfl⟩ : syracuseStep 2668529 = 2001397) B2001397
theorem B2668547 : Blo 1778090 2668547 := bstep (se 1 (by rfl) ⟨2001410, by rfl⟩ : syracuseStep 2668547 = 4002821) B4002821
theorem B2668577 : Blo 1778090 2668577 := bstep (se 2 (by rfl) ⟨1000716, by rfl⟩ : syracuseStep 2668577 = 2001433) B2001433
theorem B2668595 : Blo 1778090 2668595 := bstep (se 1 (by rfl) ⟨2001446, by rfl⟩ : syracuseStep 2668595 = 4002893) B4002893
theorem B21649477 : Blo 1778090 21649477 := bstep (se 4 (by rfl) ⟨2029638, by rfl⟩ : syracuseStep 21649477 = 4059277) B4059277
theorem B2668625 : Blo 1778090 2668625 := bstep (se 2 (by rfl) ⟨1000734, by rfl⟩ : syracuseStep 2668625 = 2001469) B2001469
theorem B2668643 : Blo 1778090 2668643 := bstep (se 1 (by rfl) ⟨2001482, by rfl⟩ : syracuseStep 2668643 = 4002965) B4002965
theorem B6002801 : Blo 1778090 6002801 := bstep (se 2 (by rfl) ⟨2251050, by rfl⟩ : syracuseStep 6002801 = 4502101) B4502101
theorem B3799153 : Blo 1778090 3799153 := bstep (se 2 (by rfl) ⟨1424682, by rfl⟩ : syracuseStep 3799153 = 2849365) B2849365
theorem B2668673 : Blo 1778090 2668673 := bstep (se 2 (by rfl) ⟨1000752, by rfl⟩ : syracuseStep 2668673 = 2001505) B2001505
theorem B6756493 : Blo 1778090 6756493 := bstep (se 3 (by rfl) ⟨1266842, by rfl⟩ : syracuseStep 6756493 = 2533685) B2533685
theorem B2668691 : Blo 1778090 2668691 := bstep (se 1 (by rfl) ⟨2001518, by rfl⟩ : syracuseStep 2668691 = 4003037) B4003037
theorem B2668721 : Blo 1778090 2668721 := bstep (se 2 (by rfl) ⟨1000770, by rfl⟩ : syracuseStep 2668721 = 2001541) B2001541
theorem B2848961 : Blo 1778090 2848961 := bstep (se 2 (by rfl) ⟨1068360, by rfl⟩ : syracuseStep 2848961 = 2136721) B2136721
theorem B2668739 : Blo 1778090 2668739 := bstep (se 1 (by rfl) ⟨2001554, by rfl⟩ : syracuseStep 2668739 = 4003109) B4003109
theorem B2668769 : Blo 1778090 2668769 := bstep (se 2 (by rfl) ⟨1000788, by rfl⟩ : syracuseStep 2668769 = 2001577) B2001577
theorem B4004081 : Blo 1778090 4004081 := bstep (se 2 (by rfl) ⟨1501530, by rfl⟩ : syracuseStep 4004081 = 3003061) B3003061
theorem B2668787 : Blo 1778090 2668787 := bstep (se 1 (by rfl) ⟨2001590, by rfl⟩ : syracuseStep 2668787 = 4003181) B4003181
theorem B4004099 : Blo 1778090 4004099 := bstep (se 1 (by rfl) ⟨3003074, by rfl⟩ : syracuseStep 4004099 = 6006149) B6006149
theorem B2668817 : Blo 1778090 2668817 := bstep (se 2 (by rfl) ⟨1000806, by rfl⟩ : syracuseStep 2668817 = 2001613) B2001613
theorem B2668835 : Blo 1778090 2668835 := bstep (se 1 (by rfl) ⟨2001626, by rfl⟩ : syracuseStep 2668835 = 4003253) B4003253
theorem B2849089 : Blo 1778090 2849089 := bstep (se 2 (by rfl) ⟨1068408, by rfl⟩ : syracuseStep 2849089 = 2136817) B2136817
theorem B2668865 : Blo 1778090 2668865 := bstep (se 2 (by rfl) ⟨1000824, by rfl⟩ : syracuseStep 2668865 = 2001649) B2001649
theorem B2251091 : Blo 1778090 2251091 := bstep (se 1 (by rfl) ⟨1688318, by rfl⟩ : syracuseStep 2251091 = 3376637) B3376637
theorem B2668883 : Blo 1778090 2668883 := bstep (se 1 (by rfl) ⟨2001662, by rfl⟩ : syracuseStep 2668883 = 4003325) B4003325
theorem B2668913 : Blo 1778090 2668913 := bstep (se 2 (by rfl) ⟨1000842, by rfl⟩ : syracuseStep 2668913 = 2001685) B2001685
theorem B2668931 : Blo 1778090 2668931 := bstep (se 1 (by rfl) ⟨2001698, by rfl⟩ : syracuseStep 2668931 = 4003397) B4003397
theorem B2668961 : Blo 1778090 2668961 := bstep (se 2 (by rfl) ⟨1000860, by rfl⟩ : syracuseStep 2668961 = 2001721) B2001721
theorem B2668979 : Blo 1778090 2668979 := bstep (se 1 (by rfl) ⟨2001734, by rfl⟩ : syracuseStep 2668979 = 4003469) B4003469
theorem B2669009 : Blo 1778090 2669009 := bstep (se 2 (by rfl) ⟨1000878, by rfl⟩ : syracuseStep 2669009 = 2001757) B2001757
theorem B2669027 : Blo 1778090 2669027 := bstep (se 1 (by rfl) ⟨2001770, by rfl⟩ : syracuseStep 2669027 = 4003541) B4003541
theorem B7215587 : Blo 1778090 7215587 := bstep (se 1 (by rfl) ⟨5411690, by rfl⟩ : syracuseStep 7215587 = 10823381) B10823381
theorem B2669057 : Blo 1778090 2669057 := bstep (se 2 (by rfl) ⟨1000896, by rfl⟩ : syracuseStep 2669057 = 2001793) B2001793
theorem B4807181 : Blo 1778090 4807181 := bstep (se 3 (by rfl) ⟨901346, by rfl⟩ : syracuseStep 4807181 = 1802693) B1802693
theorem B4004369 : Blo 1778090 4004369 := bstep (se 2 (by rfl) ⟨1501638, by rfl⟩ : syracuseStep 4004369 = 3003277) B3003277
theorem B2669075 : Blo 1778090 2669075 := bstep (se 1 (by rfl) ⟨2001806, by rfl⟩ : syracuseStep 2669075 = 4003613) B4003613
theorem B4004387 : Blo 1778090 4004387 := bstep (se 1 (by rfl) ⟨3003290, by rfl⟩ : syracuseStep 4004387 = 6006581) B6006581
theorem B2669105 : Blo 1778090 2669105 := bstep (se 2 (by rfl) ⟨1000914, by rfl⟩ : syracuseStep 2669105 = 2001829) B2001829
theorem B2669123 : Blo 1778090 2669123 := bstep (se 1 (by rfl) ⟨2001842, by rfl⟩ : syracuseStep 2669123 = 4003685) B4003685
theorem B2669153 : Blo 1778090 2669153 := bstep (se 2 (by rfl) ⟨1000932, by rfl⟩ : syracuseStep 2669153 = 2001865) B2001865
theorem B2669171 : Blo 1778090 2669171 := bstep (se 1 (by rfl) ⟨2001878, by rfl⟩ : syracuseStep 2669171 = 4003757) B4003757
theorem B6003341 : Blo 1778090 6003341 := bstep (se 3 (by rfl) ⟨1125626, by rfl⟩ : syracuseStep 6003341 = 2251253) B2251253
theorem B2669201 : Blo 1778090 2669201 := bstep (se 2 (by rfl) ⟨1000950, by rfl⟩ : syracuseStep 2669201 = 2001901) B2001901
theorem B2669219 : Blo 1778090 2669219 := bstep (se 1 (by rfl) ⟨2001914, by rfl⟩ : syracuseStep 2669219 = 4003829) B4003829
theorem B7600817 : Blo 1778090 7600817 := bstep (se 2 (by rfl) ⟨2850306, by rfl⟩ : syracuseStep 7600817 = 5700613) B5700613
theorem B2669249 : Blo 1778090 2669249 := bstep (se 2 (by rfl) ⟨1000968, by rfl⟩ : syracuseStep 2669249 = 2001937) B2001937
theorem B6003395 : Blo 1778090 6003395 := bstep (se 1 (by rfl) ⟨4502546, by rfl⟩ : syracuseStep 6003395 = 9005093) B9005093
theorem B4807363 : Blo 1778090 4807363 := bstep (se 1 (by rfl) ⟨3605522, by rfl⟩ : syracuseStep 4807363 = 7211045) B7211045
theorem B2669267 : Blo 1778090 2669267 := bstep (se 1 (by rfl) ⟨2001950, by rfl⟩ : syracuseStep 2669267 = 4003901) B4003901
theorem B2603731 : Blo 1778090 2603731 := bstep (se 1 (by rfl) ⟨1952798, by rfl⟩ : syracuseStep 2603731 = 3905597) B3905597
theorem B1899235 : Blo 1778090 1899235 := bstep (se 1 (by rfl) ⟨1424426, by rfl⟩ : syracuseStep 1899235 = 2848853) B2848853
theorem B2669297 : Blo 1778090 2669297 := bstep (se 2 (by rfl) ⟨1000986, by rfl⟩ : syracuseStep 2669297 = 2001973) B2001973
theorem B3799811 : Blo 1778090 3799811 := bstep (se 1 (by rfl) ⟨2849858, by rfl⟩ : syracuseStep 3799811 = 5699717) B5699717
theorem B2669315 : Blo 1778090 2669315 := bstep (se 1 (by rfl) ⟨2001986, by rfl⟩ : syracuseStep 2669315 = 4003973) B4003973
theorem B2669345 : Blo 1778090 2669345 := bstep (se 2 (by rfl) ⟨1001004, by rfl⟩ : syracuseStep 2669345 = 2002009) B2002009
theorem B4504369 : Blo 1778090 4504369 := bstep (se 2 (by rfl) ⟨1689138, by rfl⟩ : syracuseStep 4504369 = 3378277) B3378277
theorem B2669363 : Blo 1778090 2669363 := bstep (se 1 (by rfl) ⟨2002022, by rfl⟩ : syracuseStep 2669363 = 4004045) B4004045
theorem B4004657 : Blo 1778090 4004657 := bstep (se 2 (by rfl) ⟨1501746, by rfl⟩ : syracuseStep 4004657 = 3003493) B3003493
theorem B4004675 : Blo 1778090 4004675 := bstep (se 1 (by rfl) ⟨3003506, by rfl⟩ : syracuseStep 4004675 = 6007013) B6007013
theorem B13507397 : Blo 1778090 13507397 := bstep (se 4 (by rfl) ⟨1266318, by rfl⟩ : syracuseStep 13507397 = 2532637) B2532637
theorem B2669393 : Blo 1778090 2669393 := bstep (se 2 (by rfl) ⟨1001022, by rfl⟩ : syracuseStep 2669393 = 2002045) B2002045
theorem B2669411 : Blo 1778090 2669411 := bstep (se 1 (by rfl) ⟨2002058, by rfl⟩ : syracuseStep 2669411 = 4004117) B4004117
theorem B2136947 : Blo 1778090 2136947 := bstep (se 1 (by rfl) ⟨1602710, by rfl⟩ : syracuseStep 2136947 = 3205421) B3205421
theorem B2669441 : Blo 1778090 2669441 := bstep (se 2 (by rfl) ⟨1001040, by rfl⟩ : syracuseStep 2669441 = 2002081) B2002081
theorem B2669459 : Blo 1778090 2669459 := bstep (se 1 (by rfl) ⟨2002094, by rfl⟩ : syracuseStep 2669459 = 4004189) B4004189
theorem B6413219 : Blo 1778090 6413219 := bstep (se 1 (by rfl) ⟨4809914, by rfl⟩ : syracuseStep 6413219 = 9619829) B9619829
theorem B6757283 : Blo 1778090 6757283 := bstep (se 1 (by rfl) ⟨5067962, by rfl⟩ : syracuseStep 6757283 = 10135925) B10135925
theorem B2669489 : Blo 1778090 2669489 := bstep (se 2 (by rfl) ⟨1001058, by rfl⟩ : syracuseStep 2669489 = 2002117) B2002117
theorem B2669507 : Blo 1778090 2669507 := bstep (se 1 (by rfl) ⟨2002130, by rfl⟩ : syracuseStep 2669507 = 4004261) B4004261
theorem B6003665 : Blo 1778090 6003665 := bstep (se 2 (by rfl) ⟨2251374, by rfl⟩ : syracuseStep 6003665 = 4502749) B4502749
theorem B2669537 : Blo 1778090 2669537 := bstep (se 2 (by rfl) ⟨1001076, by rfl⟩ : syracuseStep 2669537 = 2002153) B2002153
theorem B2669555 : Blo 1778090 2669555 := bstep (se 1 (by rfl) ⟨2002166, by rfl⟩ : syracuseStep 2669555 = 4004333) B4004333
theorem B2669585 : Blo 1778090 2669585 := bstep (se 2 (by rfl) ⟨1001094, by rfl⟩ : syracuseStep 2669585 = 2002189) B2002189
theorem B2251795 : Blo 1778090 2251795 := bstep (se 1 (by rfl) ⟨1688846, by rfl⟩ : syracuseStep 2251795 = 3377693) B3377693
theorem B2669603 : Blo 1778090 2669603 := bstep (se 1 (by rfl) ⟨2002202, by rfl⟩ : syracuseStep 2669603 = 4004405) B4004405
theorem B2669633 : Blo 1778090 2669633 := bstep (se 2 (by rfl) ⟨1001112, by rfl⟩ : syracuseStep 2669633 = 2002225) B2002225
theorem B4504643 : Blo 1778090 4504643 := bstep (se 1 (by rfl) ⟨3378482, by rfl⟩ : syracuseStep 4504643 = 6756965) B6756965
theorem B4004945 : Blo 1778090 4004945 := bstep (se 2 (by rfl) ⟨1501854, by rfl⟩ : syracuseStep 4004945 = 3003709) B3003709
theorem B2669651 : Blo 1778090 2669651 := bstep (se 1 (by rfl) ⟨2002238, by rfl⟩ : syracuseStep 2669651 = 4004477) B4004477
theorem B4004963 : Blo 1778090 4004963 := bstep (se 1 (by rfl) ⟨3003722, by rfl⟩ : syracuseStep 4004963 = 6007445) B6007445
theorem B2669681 : Blo 1778090 2669681 := bstep (se 2 (by rfl) ⟨1001130, by rfl⟩ : syracuseStep 2669681 = 2002261) B2002261
theorem B2251891 : Blo 1778090 2251891 := bstep (se 1 (by rfl) ⟨1688918, by rfl⟩ : syracuseStep 2251891 = 3377837) B3377837
theorem B2669699 : Blo 1778090 2669699 := bstep (se 1 (by rfl) ⟨2002274, by rfl⟩ : syracuseStep 2669699 = 4004549) B4004549
theorem B2669729 : Blo 1778090 2669729 := bstep (se 2 (by rfl) ⟨1001148, by rfl⟩ : syracuseStep 2669729 = 2002297) B2002297
theorem B2669747 : Blo 1778090 2669747 := bstep (se 1 (by rfl) ⟨2002310, by rfl⟩ : syracuseStep 2669747 = 4004621) B4004621
theorem B2669777 : Blo 1778090 2669777 := bstep (se 2 (by rfl) ⟨1001166, by rfl⟩ : syracuseStep 2669777 = 2002333) B2002333
theorem B2669795 : Blo 1778090 2669795 := bstep (se 1 (by rfl) ⟨2002346, by rfl⟩ : syracuseStep 2669795 = 4004693) B4004693
theorem B2669825 : Blo 1778090 2669825 := bstep (se 2 (by rfl) ⟨1001184, by rfl⟩ : syracuseStep 2669825 = 2002369) B2002369
theorem B4504835 : Blo 1778090 4504835 := bstep (se 1 (by rfl) ⟨3378626, by rfl⟩ : syracuseStep 4504835 = 6757253) B6757253
theorem B7216397 : Blo 1778090 7216397 := bstep (se 3 (by rfl) ⟨1353074, by rfl⟩ : syracuseStep 7216397 = 2706149) B2706149
theorem B2669843 : Blo 1778090 2669843 := bstep (se 1 (by rfl) ⟨2002382, by rfl⟩ : syracuseStep 2669843 = 4004765) B4004765
theorem B2850083 : Blo 1778090 2850083 := bstep (se 1 (by rfl) ⟨2137562, by rfl⟩ : syracuseStep 2850083 = 4275125) B4275125
theorem B2669873 : Blo 1778090 2669873 := bstep (se 2 (by rfl) ⟨1001202, by rfl⟩ : syracuseStep 2669873 = 2002405) B2002405
theorem B2669891 : Blo 1778090 2669891 := bstep (se 1 (by rfl) ⟨2002418, by rfl⟩ : syracuseStep 2669891 = 4004837) B4004837
theorem B2669921 : Blo 1778090 2669921 := bstep (se 2 (by rfl) ⟨1001220, by rfl⟩ : syracuseStep 2669921 = 2002441) B2002441
theorem B9002339 : Blo 1778090 9002339 := bstep (se 1 (by rfl) ⟨6751754, by rfl⟩ : syracuseStep 9002339 = 13503509) B13503509
theorem B6413681 : Blo 1778090 6413681 := bstep (se 2 (by rfl) ⟨2405130, by rfl⟩ : syracuseStep 6413681 = 4810261) B4810261
theorem B13516145 : Blo 1778090 13516145 := bstep (se 2 (by rfl) ⟨5068554, by rfl⟩ : syracuseStep 13516145 = 10137109) B10137109
theorem B2669939 : Blo 1778090 2669939 := bstep (se 1 (by rfl) ⟨2002454, by rfl⟩ : syracuseStep 2669939 = 4004909) B4004909
theorem B2669969 : Blo 1778090 2669969 := bstep (se 2 (by rfl) ⟨1001238, by rfl⟩ : syracuseStep 2669969 = 2002477) B2002477
theorem B2669987 : Blo 1778090 2669987 := bstep (se 1 (by rfl) ⟨2002490, by rfl⟩ : syracuseStep 2669987 = 4004981) B4004981
theorem B2670017 : Blo 1778090 2670017 := bstep (se 2 (by rfl) ⟨1001256, by rfl⟩ : syracuseStep 2670017 = 2002513) B2002513
theorem B2670035 : Blo 1778090 2670035 := bstep (se 1 (by rfl) ⟨2002526, by rfl⟩ : syracuseStep 2670035 = 4005053) B4005053
theorem B6004205 : Blo 1778090 6004205 := bstep (se 3 (by rfl) ⟨1125788, by rfl⟩ : syracuseStep 6004205 = 2251577) B2251577
theorem B4562417 : Blo 1778090 4562417 := bstep (se 2 (by rfl) ⟨1710906, by rfl⟩ : syracuseStep 4562417 = 3421813) B3421813
theorem B2670065 : Blo 1778090 2670065 := bstep (se 2 (by rfl) ⟨1001274, by rfl⟩ : syracuseStep 2670065 = 2002549) B2002549
theorem B2670083 : Blo 1778090 2670083 := bstep (se 1 (by rfl) ⟨2002562, by rfl⟩ : syracuseStep 2670083 = 4005125) B4005125
theorem B2670113 : Blo 1778090 2670113 := bstep (se 2 (by rfl) ⟨1001292, by rfl⟩ : syracuseStep 2670113 = 2002585) B2002585
theorem B4808227 : Blo 1778090 4808227 := bstep (se 1 (by rfl) ⟨3606170, by rfl⟩ : syracuseStep 4808227 = 7212341) B7212341
theorem B6004259 : Blo 1778090 6004259 := bstep (se 1 (by rfl) ⟨4503194, by rfl⟩ : syracuseStep 6004259 = 9006389) B9006389
theorem B6757937 : Blo 1778090 6757937 := bstep (se 2 (by rfl) ⟨2534226, by rfl⟩ : syracuseStep 6757937 = 5068453) B5068453
theorem B2670131 : Blo 1778090 2670131 := bstep (se 1 (by rfl) ⟨2002598, by rfl⟩ : syracuseStep 2670131 = 4005197) B4005197
theorem B3800657 : Blo 1778090 3800657 := bstep (se 2 (by rfl) ⟨1425246, by rfl⟩ : syracuseStep 3800657 = 2850493) B2850493
theorem B2252387 : Blo 1778090 2252387 := bstep (se 1 (by rfl) ⟨1689290, by rfl⟩ : syracuseStep 2252387 = 3378581) B3378581
theorem B5701229 : Blo 1778090 5701229 := bstep (se 3 (by rfl) ⟨1068980, by rfl⟩ : syracuseStep 5701229 = 2137961) B2137961
theorem B9617059 : Blo 1778090 9617059 := bstep (se 1 (by rfl) ⟨7212794, by rfl⟩ : syracuseStep 9617059 = 14425589) B14425589
theorem B20577989 : Blo 1778090 20577989 := bstep (se 4 (by rfl) ⟨1929186, by rfl⟩ : syracuseStep 20577989 = 3858373) B3858373
theorem B5775089 : Blo 1778090 5775089 := bstep (se 2 (by rfl) ⟨2165658, by rfl⟩ : syracuseStep 5775089 = 4331317) B4331317
theorem B10133261 : Blo 1778090 10133261 := bstep (se 3 (by rfl) ⟨1899986, by rfl⟩ : syracuseStep 10133261 = 3799973) B3799973
theorem B1900307 : Blo 1778090 1900307 := bstep (se 1 (by rfl) ⟨1425230, by rfl⟩ : syracuseStep 1900307 = 2850461) B2850461
theorem B6004529 : Blo 1778090 6004529 := bstep (se 2 (by rfl) ⟨2251698, by rfl⟩ : syracuseStep 6004529 = 4503397) B4503397
theorem B6758423 : Blo 1778090 6758423 := bstep (se 1 (by rfl) ⟨5068817, by rfl⟩ : syracuseStep 6758423 = 10137635) B10137635
theorem B4505665 : Blo 1778090 4505665 := bstep (se 2 (by rfl) ⟨1689624, by rfl⟩ : syracuseStep 4505665 = 3379249) B3379249
theorem B3424331 : Blo 1778090 3424331 := bstep (se 1 (by rfl) ⟨2568248, by rfl⟩ : syracuseStep 3424331 = 5136497) B5136497
theorem B20258909 : Blo 1778090 20258909 := bstep (se 3 (by rfl) ⟨3798545, by rfl⟩ : syracuseStep 20258909 = 7597091) B7597091
theorem B4808855 : Blo 1778090 4808855 := bstep (se 1 (by rfl) ⟨3606641, by rfl⟩ : syracuseStep 4808855 = 7213283) B7213283
theorem B10969267 : Blo 1778090 10969267 := bstep (se 1 (by rfl) ⟨8226950, by rfl⟩ : syracuseStep 10969267 = 16453901) B16453901
theorem B3424523 : Blo 1778090 3424523 := bstep (se 1 (by rfl) ⟨2568392, by rfl⟩ : syracuseStep 3424523 = 5136785) B5136785
theorem B6005015 : Blo 1778090 6005015 := bstep (se 1 (by rfl) ⟨4503761, by rfl⟩ : syracuseStep 6005015 = 9007523) B9007523
theorem B4055447 : Blo 1778090 4055447 := bstep (se 1 (by rfl) ⟨3041585, by rfl⟩ : syracuseStep 4055447 = 6083171) B6083171
theorem B1778091 : Blo 1778090 1778091 := bstep (se 1 (by rfl) ⟨1333568, by rfl⟩ : syracuseStep 1778091 = 2667137) B2667137
theorem B8118701 : Blo 1778090 8118701 := bstep (se 3 (by rfl) ⟨1522256, by rfl⟩ : syracuseStep 8118701 = 3044513) B3044513
theorem B1778103 : Blo 1778090 1778103 := bstep (se 1 (by rfl) ⟨1333577, by rfl⟩ : syracuseStep 1778103 = 2667155) B2667155
theorem B1778123 : Blo 1778090 1778123 := bstep (se 1 (by rfl) ⟨1333592, by rfl⟩ : syracuseStep 1778123 = 2667185) B2667185
theorem B1778135 : Blo 1778090 1778135 := bstep (se 1 (by rfl) ⟨1333601, by rfl⟩ : syracuseStep 1778135 = 2667203) B2667203
theorem B11403737 : Blo 1778090 11403737 := bstep (se 2 (by rfl) ⟨4276401, by rfl⟩ : syracuseStep 11403737 = 8552803) B8552803
theorem B1778155 : Blo 1778090 1778155 := bstep (se 1 (by rfl) ⟨1333616, by rfl⟩ : syracuseStep 1778155 = 2667233) B2667233
theorem B1778167 : Blo 1778090 1778167 := bstep (se 1 (by rfl) ⟨1333625, by rfl⟩ : syracuseStep 1778167 = 2667251) B2667251
theorem B3424769 : Blo 1778090 3424769 := bstep (se 2 (by rfl) ⟨1284288, by rfl⟩ : syracuseStep 3424769 = 2568577) B2568577
theorem B1778187 : Blo 1778090 1778187 := bstep (se 1 (by rfl) ⟨1333640, by rfl⟩ : syracuseStep 1778187 = 2667281) B2667281
theorem B1778199 : Blo 1778090 1778199 := bstep (se 1 (by rfl) ⟨1333649, by rfl⟩ : syracuseStep 1778199 = 2667299) B2667299
theorem B1778219 : Blo 1778090 1778219 := bstep (se 1 (by rfl) ⟨1333664, by rfl⟩ : syracuseStep 1778219 = 2667329) B2667329
theorem B1778231 : Blo 1778090 1778231 := bstep (se 1 (by rfl) ⟨1333673, by rfl⟩ : syracuseStep 1778231 = 2667347) B2667347
theorem B1778251 : Blo 1778090 1778251 := bstep (se 1 (by rfl) ⟨1333688, by rfl⟩ : syracuseStep 1778251 = 2667377) B2667377
theorem B19243595 : Blo 1778090 19243595 := bstep (se 1 (by rfl) ⟨14432696, by rfl⟩ : syracuseStep 19243595 = 28865393) B28865393
theorem B1778263 : Blo 1778090 1778263 := bstep (se 1 (by rfl) ⟨1333697, by rfl⟩ : syracuseStep 1778263 = 2667395) B2667395
theorem B2196055 : Blo 1778090 2196055 := bstep (se 1 (by rfl) ⟨1647041, by rfl⟩ : syracuseStep 2196055 = 3294083) B3294083
theorem B1778283 : Blo 1778090 1778283 := bstep (se 1 (by rfl) ⟨1333712, by rfl⟩ : syracuseStep 1778283 = 2667425) B2667425
theorem B1778295 : Blo 1778090 1778295 := bstep (se 1 (by rfl) ⟨1333721, by rfl⟩ : syracuseStep 1778295 = 2667443) B2667443
theorem B1778315 : Blo 1778090 1778315 := bstep (se 1 (by rfl) ⟨1333736, by rfl⟩ : syracuseStep 1778315 = 2667473) B2667473
theorem B1778327 : Blo 1778090 1778327 := bstep (se 1 (by rfl) ⟨1333745, by rfl⟩ : syracuseStep 1778327 = 2667491) B2667491
theorem B1778347 : Blo 1778090 1778347 := bstep (se 1 (by rfl) ⟨1333760, by rfl⟩ : syracuseStep 1778347 = 2667521) B2667521
theorem B1778359 : Blo 1778090 1778359 := bstep (se 1 (by rfl) ⟨1333769, by rfl⟩ : syracuseStep 1778359 = 2667539) B2667539
theorem B1778379 : Blo 1778090 1778379 := bstep (se 1 (by rfl) ⟨1333784, by rfl⟩ : syracuseStep 1778379 = 2667569) B2667569
theorem B1778391 : Blo 1778090 1778391 := bstep (se 1 (by rfl) ⟨1333793, by rfl⟩ : syracuseStep 1778391 = 2667587) B2667587
theorem B2704087 : Blo 1778090 2704087 := bstep (se 1 (by rfl) ⟨2028065, by rfl⟩ : syracuseStep 2704087 = 4056131) B4056131
theorem B1778411 : Blo 1778090 1778411 := bstep (se 1 (by rfl) ⟨1333808, by rfl⟩ : syracuseStep 1778411 = 2667617) B2667617
theorem B1778423 : Blo 1778090 1778423 := bstep (se 1 (by rfl) ⟨1333817, by rfl⟩ : syracuseStep 1778423 = 2667635) B2667635
theorem B1778443 : Blo 1778090 1778443 := bstep (se 1 (by rfl) ⟨1333832, by rfl⟩ : syracuseStep 1778443 = 2667665) B2667665
theorem B6415121 : Blo 1778090 6415121 := bstep (se 2 (by rfl) ⟨2405670, by rfl⟩ : syracuseStep 6415121 = 4811341) B4811341
theorem B1778455 : Blo 1778090 1778455 := bstep (se 1 (by rfl) ⟨1333841, by rfl⟩ : syracuseStep 1778455 = 2667683) B2667683
theorem B1778475 : Blo 1778090 1778475 := bstep (se 1 (by rfl) ⟨1333856, by rfl⟩ : syracuseStep 1778475 = 2667713) B2667713
theorem B6005555 : Blo 1778090 6005555 := bstep (se 1 (by rfl) ⟨4504166, by rfl⟩ : syracuseStep 6005555 = 9008333) B9008333
theorem B1778487 : Blo 1778090 1778487 := bstep (se 1 (by rfl) ⟨1333865, by rfl⟩ : syracuseStep 1778487 = 2667731) B2667731
theorem B54756161 : Blo 1778090 54756161 := bstep (se 2 (by rfl) ⟨20533560, by rfl⟩ : syracuseStep 54756161 = 41067121) B41067121
theorem B11404097 : Blo 1778090 11404097 := bstep (se 2 (by rfl) ⟨4276536, by rfl⟩ : syracuseStep 11404097 = 8553073) B8553073
theorem B1778507 : Blo 1778090 1778507 := bstep (se 1 (by rfl) ⟨1333880, by rfl⟩ : syracuseStep 1778507 = 2667761) B2667761
theorem B4809547 : Blo 1778090 4809547 := bstep (se 1 (by rfl) ⟨3607160, by rfl⟩ : syracuseStep 4809547 = 7214321) B7214321
theorem B1778519 : Blo 1778090 1778519 := bstep (se 1 (by rfl) ⟨1333889, by rfl⟩ : syracuseStep 1778519 = 2667779) B2667779
theorem B51290981 : Blo 1778090 51290981 := bstep (se 4 (by rfl) ⟨4808529, by rfl⟩ : syracuseStep 51290981 = 9617059) B9617059
theorem B1778539 : Blo 1778090 1778539 := bstep (se 1 (by rfl) ⟨1333904, by rfl⟩ : syracuseStep 1778539 = 2667809) B2667809
theorem B1778551 : Blo 1778090 1778551 := bstep (se 1 (by rfl) ⟨1333913, by rfl⟩ : syracuseStep 1778551 = 2667827) B2667827
theorem B1778571 : Blo 1778090 1778571 := bstep (se 1 (by rfl) ⟨1333928, by rfl⟩ : syracuseStep 1778571 = 2667857) B2667857
theorem B1778583 : Blo 1778090 1778583 := bstep (se 1 (by rfl) ⟨1333937, by rfl⟩ : syracuseStep 1778583 = 2667875) B2667875
theorem B1778603 : Blo 1778090 1778603 := bstep (se 1 (by rfl) ⟨1333952, by rfl⟩ : syracuseStep 1778603 = 2667905) B2667905
theorem B1778615 : Blo 1778090 1778615 := bstep (se 1 (by rfl) ⟨1333961, by rfl⟩ : syracuseStep 1778615 = 2667923) B2667923
theorem B3376075 : Blo 1778090 3376075 := bstep (se 1 (by rfl) ⟨2532056, by rfl⟩ : syracuseStep 3376075 = 5064113) B5064113
theorem B1778635 : Blo 1778090 1778635 := bstep (se 1 (by rfl) ⟨1333976, by rfl⟩ : syracuseStep 1778635 = 2667953) B2667953
theorem B6169547 : Blo 1778090 6169547 := bstep (se 1 (by rfl) ⟨4627160, by rfl⟩ : syracuseStep 6169547 = 9254321) B9254321
theorem B1778647 : Blo 1778090 1778647 := bstep (se 1 (by rfl) ⟨1333985, by rfl⟩ : syracuseStep 1778647 = 2667971) B2667971
theorem B2532313 : Blo 1778090 2532313 := bstep (se 2 (by rfl) ⟨949617, by rfl⟩ : syracuseStep 2532313 = 1899235) B1899235
theorem B4809689 : Blo 1778090 4809689 := bstep (se 2 (by rfl) ⟨1803633, by rfl⟩ : syracuseStep 4809689 = 3607267) B3607267
theorem B1778667 : Blo 1778090 1778667 := bstep (se 1 (by rfl) ⟨1334000, by rfl⟩ : syracuseStep 1778667 = 2668001) B2668001
theorem B1778679 : Blo 1778090 1778679 := bstep (se 1 (by rfl) ⟨1334009, by rfl⟩ : syracuseStep 1778679 = 2668019) B2668019
theorem B1778699 : Blo 1778090 1778699 := bstep (se 1 (by rfl) ⟨1334024, by rfl⟩ : syracuseStep 1778699 = 2668049) B2668049
theorem B3376151 : Blo 1778090 3376151 := bstep (se 1 (by rfl) ⟨2532113, by rfl⟩ : syracuseStep 3376151 = 5064227) B5064227
theorem B1778711 : Blo 1778090 1778711 := bstep (se 1 (by rfl) ⟨1334033, by rfl⟩ : syracuseStep 1778711 = 2668067) B2668067
theorem B1778731 : Blo 1778090 1778731 := bstep (se 1 (by rfl) ⟨1334048, by rfl⟩ : syracuseStep 1778731 = 2668097) B2668097
theorem B1778743 : Blo 1778090 1778743 := bstep (se 1 (by rfl) ⟨1334057, by rfl⟩ : syracuseStep 1778743 = 2668115) B2668115
theorem B6005825 : Blo 1778090 6005825 := bstep (se 2 (by rfl) ⟨2252184, by rfl⟩ : syracuseStep 6005825 = 4504369) B4504369
theorem B1778763 : Blo 1778090 1778763 := bstep (se 1 (by rfl) ⟨1334072, by rfl⟩ : syracuseStep 1778763 = 2668145) B2668145
theorem B1778775 : Blo 1778090 1778775 := bstep (se 1 (by rfl) ⟨1334081, by rfl⟩ : syracuseStep 1778775 = 2668163) B2668163
theorem B1778795 : Blo 1778090 1778795 := bstep (se 1 (by rfl) ⟨1334096, by rfl⟩ : syracuseStep 1778795 = 2668193) B2668193
theorem B1778807 : Blo 1778090 1778807 := bstep (se 1 (by rfl) ⟨1334105, by rfl⟩ : syracuseStep 1778807 = 2668211) B2668211
theorem B1778827 : Blo 1778090 1778827 := bstep (se 1 (by rfl) ⟨1334120, by rfl⟩ : syracuseStep 1778827 = 2668241) B2668241
theorem B1778839 : Blo 1778090 1778839 := bstep (se 1 (by rfl) ⟨1334129, by rfl⟩ : syracuseStep 1778839 = 2668259) B2668259
theorem B1778859 : Blo 1778090 1778859 := bstep (se 1 (by rfl) ⟨1334144, by rfl⟩ : syracuseStep 1778859 = 2668289) B2668289
theorem B7603379 : Blo 1778090 7603379 := bstep (se 1 (by rfl) ⟨5702534, by rfl⟩ : syracuseStep 7603379 = 11405069) B11405069
theorem B1778871 : Blo 1778090 1778871 := bstep (se 1 (by rfl) ⟨1334153, by rfl⟩ : syracuseStep 1778871 = 2668307) B2668307
theorem B3204289 : Blo 1778090 3204289 := bstep (se 2 (by rfl) ⟨1201608, by rfl⟩ : syracuseStep 3204289 = 2403217) B2403217
theorem B1778891 : Blo 1778090 1778891 := bstep (se 1 (by rfl) ⟨1334168, by rfl⟩ : syracuseStep 1778891 = 2668337) B2668337
theorem B1778903 : Blo 1778090 1778903 := bstep (se 1 (by rfl) ⟨1334177, by rfl⟩ : syracuseStep 1778903 = 2668355) B2668355
theorem B5063897 : Blo 1778090 5063897 := bstep (se 2 (by rfl) ⟨1898961, by rfl⟩ : syracuseStep 5063897 = 3797923) B3797923
theorem B1778923 : Blo 1778090 1778923 := bstep (se 1 (by rfl) ⟨1334192, by rfl⟩ : syracuseStep 1778923 = 2668385) B2668385
theorem B1778935 : Blo 1778090 1778935 := bstep (se 1 (by rfl) ⟨1334201, by rfl⟩ : syracuseStep 1778935 = 2668403) B2668403
theorem B1778955 : Blo 1778090 1778955 := bstep (se 1 (by rfl) ⟨1334216, by rfl⟩ : syracuseStep 1778955 = 2668433) B2668433
theorem B1778967 : Blo 1778090 1778967 := bstep (se 1 (by rfl) ⟨1334225, by rfl⟩ : syracuseStep 1778967 = 2668451) B2668451
theorem B6087959 : Blo 1778090 6087959 := bstep (se 1 (by rfl) ⟨4565969, by rfl⟩ : syracuseStep 6087959 = 9131939) B9131939
theorem B1778987 : Blo 1778090 1778987 := bstep (se 1 (by rfl) ⟨1334240, by rfl⟩ : syracuseStep 1778987 = 2668481) B2668481
theorem B12166445 : Blo 1778090 12166445 := bstep (se 3 (by rfl) ⟨2281208, by rfl⟩ : syracuseStep 12166445 = 4562417) B4562417
theorem B7595315 : Blo 1778090 7595315 := bstep (se 1 (by rfl) ⟨5696486, by rfl⟩ : syracuseStep 7595315 = 11392973) B11392973
theorem B1778999 : Blo 1778090 1778999 := bstep (se 1 (by rfl) ⟨1334249, by rfl⟩ : syracuseStep 1778999 = 2668499) B2668499
theorem B1779019 : Blo 1778090 1779019 := bstep (se 1 (by rfl) ⟨1334264, by rfl⟩ : syracuseStep 1779019 = 2668529) B2668529
theorem B1779031 : Blo 1778090 1779031 := bstep (se 1 (by rfl) ⟨1334273, by rfl⟩ : syracuseStep 1779031 = 2668547) B2668547
theorem B11404637 : Blo 1778090 11404637 := bstep (se 3 (by rfl) ⟨2138369, by rfl⟩ : syracuseStep 11404637 = 4276739) B4276739
theorem B1779051 : Blo 1778090 1779051 := bstep (se 1 (by rfl) ⟨1334288, by rfl⟩ : syracuseStep 1779051 = 2668577) B2668577
theorem B1779063 : Blo 1778090 1779063 := bstep (se 1 (by rfl) ⟨1334297, by rfl⟩ : syracuseStep 1779063 = 2668595) B2668595
theorem B6751619 : Blo 1778090 6751619 := bstep (se 1 (by rfl) ⟨5063714, by rfl⟩ : syracuseStep 6751619 = 10127429) B10127429
theorem B1779083 : Blo 1778090 1779083 := bstep (se 1 (by rfl) ⟨1334312, by rfl⟩ : syracuseStep 1779083 = 2668625) B2668625
theorem B6751633 : Blo 1778090 6751633 := bstep (se 2 (by rfl) ⟨2531862, by rfl⟩ : syracuseStep 6751633 = 5063725) B5063725
theorem B1779095 : Blo 1778090 1779095 := bstep (se 1 (by rfl) ⟨1334321, by rfl⟩ : syracuseStep 1779095 = 2668643) B2668643
theorem B1779115 : Blo 1778090 1779115 := bstep (se 1 (by rfl) ⟨1334336, by rfl⟩ : syracuseStep 1779115 = 2668673) B2668673
theorem B1779127 : Blo 1778090 1779127 := bstep (se 1 (by rfl) ⟨1334345, by rfl⟩ : syracuseStep 1779127 = 2668691) B2668691
theorem B1779147 : Blo 1778090 1779147 := bstep (se 1 (by rfl) ⟨1334360, by rfl⟩ : syracuseStep 1779147 = 2668721) B2668721
theorem B1779159 : Blo 1778090 1779159 := bstep (se 1 (by rfl) ⟨1334369, by rfl⟩ : syracuseStep 1779159 = 2668739) B2668739
theorem B1779179 : Blo 1778090 1779179 := bstep (se 1 (by rfl) ⟨1334384, by rfl⟩ : syracuseStep 1779179 = 2668769) B2668769
theorem B1779191 : Blo 1778090 1779191 := bstep (se 1 (by rfl) ⟨1334393, by rfl⟩ : syracuseStep 1779191 = 2668787) B2668787
theorem B1779211 : Blo 1778090 1779211 := bstep (se 1 (by rfl) ⟨1334408, by rfl⟩ : syracuseStep 1779211 = 2668817) B2668817
theorem B2000407 : Blo 1778090 2000407 := bstep (se 1 (by rfl) ⟨1500305, by rfl⟩ : syracuseStep 2000407 = 3000611) B3000611
theorem B1779223 : Blo 1778090 1779223 := bstep (se 1 (by rfl) ⟨1334417, by rfl⟩ : syracuseStep 1779223 = 2668835) B2668835
theorem B1779243 : Blo 1778090 1779243 := bstep (se 1 (by rfl) ⟨1334432, by rfl⟩ : syracuseStep 1779243 = 2668865) B2668865
theorem B1779255 : Blo 1778090 1779255 := bstep (se 1 (by rfl) ⟨1334441, by rfl⟩ : syracuseStep 1779255 = 2668883) B2668883
theorem B1779275 : Blo 1778090 1779275 := bstep (se 1 (by rfl) ⟨1334456, by rfl⟩ : syracuseStep 1779275 = 2668913) B2668913
theorem B1779287 : Blo 1778090 1779287 := bstep (se 1 (by rfl) ⟨1334465, by rfl⟩ : syracuseStep 1779287 = 2668931) B2668931
theorem B6006365 : Blo 1778090 6006365 := bstep (se 3 (by rfl) ⟨1126193, by rfl⟩ : syracuseStep 6006365 = 2252387) B2252387
theorem B1779307 : Blo 1778090 1779307 := bstep (se 1 (by rfl) ⟨1334480, by rfl⟩ : syracuseStep 1779307 = 2668961) B2668961
theorem B1779319 : Blo 1778090 1779319 := bstep (se 1 (by rfl) ⟨1334489, by rfl⟩ : syracuseStep 1779319 = 2668979) B2668979
theorem B1779339 : Blo 1778090 1779339 := bstep (se 1 (by rfl) ⟨1334504, by rfl⟩ : syracuseStep 1779339 = 2669009) B2669009
theorem B1779351 : Blo 1778090 1779351 := bstep (se 1 (by rfl) ⟨1334513, by rfl⟩ : syracuseStep 1779351 = 2669027) B2669027
theorem B4810391 : Blo 1778090 4810391 := bstep (se 1 (by rfl) ⟨3607793, by rfl⟩ : syracuseStep 4810391 = 7215587) B7215587
theorem B1779371 : Blo 1778090 1779371 := bstep (se 1 (by rfl) ⟨1334528, by rfl⟩ : syracuseStep 1779371 = 2669057) B2669057
theorem B3204787 : Blo 1778090 3204787 := bstep (se 1 (by rfl) ⟨2403590, by rfl⟩ : syracuseStep 3204787 = 4807181) B4807181
theorem B3376819 : Blo 1778090 3376819 := bstep (se 1 (by rfl) ⟨2532614, by rfl⟩ : syracuseStep 3376819 = 5065229) B5065229
theorem B1779383 : Blo 1778090 1779383 := bstep (se 1 (by rfl) ⟨1334537, by rfl⟩ : syracuseStep 1779383 = 2669075) B2669075
theorem B6751937 : Blo 1778090 6751937 := bstep (se 2 (by rfl) ⟨2531976, by rfl⟩ : syracuseStep 6751937 = 5063953) B5063953
theorem B2000587 : Blo 1778090 2000587 := bstep (se 1 (by rfl) ⟨1500440, by rfl⟩ : syracuseStep 2000587 = 3000881) B3000881
theorem B1779403 : Blo 1778090 1779403 := bstep (se 1 (by rfl) ⟨1334552, by rfl⟩ : syracuseStep 1779403 = 2669105) B2669105
theorem B1779415 : Blo 1778090 1779415 := bstep (se 1 (by rfl) ⟨1334561, by rfl⟩ : syracuseStep 1779415 = 2669123) B2669123
theorem B1779435 : Blo 1778090 1779435 := bstep (se 1 (by rfl) ⟨1334576, by rfl⟩ : syracuseStep 1779435 = 2669153) B2669153
theorem B1779447 : Blo 1778090 1779447 := bstep (se 1 (by rfl) ⟨1334585, by rfl⟩ : syracuseStep 1779447 = 2669171) B2669171
theorem B1779467 : Blo 1778090 1779467 := bstep (se 1 (by rfl) ⟨1334600, by rfl⟩ : syracuseStep 1779467 = 2669201) B2669201
theorem B1779479 : Blo 1778090 1779479 := bstep (se 1 (by rfl) ⟨1334609, by rfl⟩ : syracuseStep 1779479 = 2669219) B2669219
theorem B2705177 : Blo 1778090 2705177 := bstep (se 2 (by rfl) ⟨1014441, by rfl⟩ : syracuseStep 2705177 = 2028883) B2028883
theorem B1779499 : Blo 1778090 1779499 := bstep (se 1 (by rfl) ⟨1334624, by rfl⟩ : syracuseStep 1779499 = 2669249) B2669249
theorem B2000695 : Blo 1778090 2000695 := bstep (se 1 (by rfl) ⟨1500521, by rfl⟩ : syracuseStep 2000695 = 3001043) B3001043
theorem B1779511 : Blo 1778090 1779511 := bstep (se 1 (by rfl) ⟨1334633, by rfl⟩ : syracuseStep 1779511 = 2669267) B2669267
theorem B1779531 : Blo 1778090 1779531 := bstep (se 1 (by rfl) ⟨1334648, by rfl⟩ : syracuseStep 1779531 = 2669297) B2669297
theorem B2533207 : Blo 1778090 2533207 := bstep (se 1 (by rfl) ⟨1899905, by rfl⟩ : syracuseStep 2533207 = 3799811) B3799811
theorem B1779543 : Blo 1778090 1779543 := bstep (se 1 (by rfl) ⟨1334657, by rfl⟩ : syracuseStep 1779543 = 2669315) B2669315
theorem B1779563 : Blo 1778090 1779563 := bstep (se 1 (by rfl) ⟨1334672, by rfl⟩ : syracuseStep 1779563 = 2669345) B2669345
theorem B1779575 : Blo 1778090 1779575 := bstep (se 1 (by rfl) ⟨1334681, by rfl⟩ : syracuseStep 1779575 = 2669363) B2669363
theorem B9004931 : Blo 1778090 9004931 := bstep (se 1 (by rfl) ⟨6753698, by rfl⟩ : syracuseStep 9004931 = 13507397) B13507397
theorem B1779595 : Blo 1778090 1779595 := bstep (se 1 (by rfl) ⟨1334696, by rfl⟩ : syracuseStep 1779595 = 2669393) B2669393
theorem B3377047 : Blo 1778090 3377047 := bstep (se 1 (by rfl) ⟨2532785, by rfl⟩ : syracuseStep 3377047 = 5065571) B5065571
theorem B1779607 : Blo 1778090 1779607 := bstep (se 1 (by rfl) ⟨1334705, by rfl⟩ : syracuseStep 1779607 = 2669411) B2669411
theorem B1779627 : Blo 1778090 1779627 := bstep (se 1 (by rfl) ⟨1334720, by rfl⟩ : syracuseStep 1779627 = 2669441) B2669441
theorem B1779639 : Blo 1778090 1779639 := bstep (se 1 (by rfl) ⟨1334729, by rfl⟩ : syracuseStep 1779639 = 2669459) B2669459
theorem B1779659 : Blo 1778090 1779659 := bstep (se 1 (by rfl) ⟨1334744, by rfl⟩ : syracuseStep 1779659 = 2669489) B2669489
theorem B3606487 : Blo 1778090 3606487 := bstep (se 1 (by rfl) ⟨2704865, by rfl⟩ : syracuseStep 3606487 = 5409731) B5409731
theorem B1779671 : Blo 1778090 1779671 := bstep (se 1 (by rfl) ⟨1334753, by rfl⟩ : syracuseStep 1779671 = 2669507) B2669507
theorem B2000875 : Blo 1778090 2000875 := bstep (se 1 (by rfl) ⟨1500656, by rfl⟩ : syracuseStep 2000875 = 3001313) B3001313
theorem B1779691 : Blo 1778090 1779691 := bstep (se 1 (by rfl) ⟨1334768, by rfl⟩ : syracuseStep 1779691 = 2669537) B2669537
theorem B1779703 : Blo 1778090 1779703 := bstep (se 1 (by rfl) ⟨1334777, by rfl⟩ : syracuseStep 1779703 = 2669555) B2669555
theorem B3377153 : Blo 1778090 3377153 := bstep (se 2 (by rfl) ⟨1266432, by rfl⟩ : syracuseStep 3377153 = 2532865) B2532865
theorem B1779723 : Blo 1778090 1779723 := bstep (se 1 (by rfl) ⟨1334792, by rfl⟩ : syracuseStep 1779723 = 2669585) B2669585
theorem B1779735 : Blo 1778090 1779735 := bstep (se 1 (by rfl) ⟨1334801, by rfl⟩ : syracuseStep 1779735 = 2669603) B2669603
theorem B1779755 : Blo 1778090 1779755 := bstep (se 1 (by rfl) ⟨1334816, by rfl⟩ : syracuseStep 1779755 = 2669633) B2669633
theorem B1779767 : Blo 1778090 1779767 := bstep (se 1 (by rfl) ⟨1334825, by rfl⟩ : syracuseStep 1779767 = 2669651) B2669651
theorem B1779787 : Blo 1778090 1779787 := bstep (se 1 (by rfl) ⟨1334840, by rfl⟩ : syracuseStep 1779787 = 2669681) B2669681
theorem B2000983 : Blo 1778090 2000983 := bstep (se 1 (by rfl) ⟨1500737, by rfl⟩ : syracuseStep 2000983 = 3001475) B3001475
theorem B1779799 : Blo 1778090 1779799 := bstep (se 1 (by rfl) ⟨1334849, by rfl⟩ : syracuseStep 1779799 = 2669699) B2669699
theorem B1779819 : Blo 1778090 1779819 := bstep (se 1 (by rfl) ⟨1334864, by rfl⟩ : syracuseStep 1779819 = 2669729) B2669729
theorem B1779831 : Blo 1778090 1779831 := bstep (se 1 (by rfl) ⟨1334873, by rfl⟩ : syracuseStep 1779831 = 2669747) B2669747
theorem B1779851 : Blo 1778090 1779851 := bstep (se 1 (by rfl) ⟨1334888, by rfl⟩ : syracuseStep 1779851 = 2669777) B2669777
theorem B1779863 : Blo 1778090 1779863 := bstep (se 1 (by rfl) ⟨1334897, by rfl⟩ : syracuseStep 1779863 = 2669795) B2669795
theorem B3377305 : Blo 1778090 3377305 := bstep (se 2 (by rfl) ⟨1266489, by rfl⟩ : syracuseStep 3377305 = 2532979) B2532979
theorem B1779883 : Blo 1778090 1779883 := bstep (se 1 (by rfl) ⟨1334912, by rfl⟩ : syracuseStep 1779883 = 2669825) B2669825
theorem B4810931 : Blo 1778090 4810931 := bstep (se 1 (by rfl) ⟨3608198, by rfl⟩ : syracuseStep 4810931 = 7216397) B7216397
theorem B1779895 : Blo 1778090 1779895 := bstep (se 1 (by rfl) ⟨1334921, by rfl⟩ : syracuseStep 1779895 = 2669843) B2669843
theorem B1779915 : Blo 1778090 1779915 := bstep (se 1 (by rfl) ⟨1334936, by rfl⟩ : syracuseStep 1779915 = 2669873) B2669873
theorem B1779927 : Blo 1778090 1779927 := bstep (se 1 (by rfl) ⟨1334945, by rfl⟩ : syracuseStep 1779927 = 2669891) B2669891
theorem B1779947 : Blo 1778090 1779947 := bstep (se 1 (by rfl) ⟨1334960, by rfl⟩ : syracuseStep 1779947 = 2669921) B2669921
theorem B1779959 : Blo 1778090 1779959 := bstep (se 1 (by rfl) ⟨1334969, by rfl⟩ : syracuseStep 1779959 = 2669939) B2669939
theorem B2001163 : Blo 1778090 2001163 := bstep (se 1 (by rfl) ⟨1500872, by rfl⟩ : syracuseStep 2001163 = 3001745) B3001745
theorem B1779979 : Blo 1778090 1779979 := bstep (se 1 (by rfl) ⟨1334984, by rfl⟩ : syracuseStep 1779979 = 2669969) B2669969
theorem B12830993 : Blo 1778090 12830993 := bstep (se 2 (by rfl) ⟨4811622, by rfl⟩ : syracuseStep 12830993 = 9623245) B9623245
theorem B1779991 : Blo 1778090 1779991 := bstep (se 1 (by rfl) ⟨1334993, by rfl⟩ : syracuseStep 1779991 = 2669987) B2669987
theorem B1780011 : Blo 1778090 1780011 := bstep (se 1 (by rfl) ⟨1335008, by rfl⟩ : syracuseStep 1780011 = 2670017) B2670017
theorem B1780023 : Blo 1778090 1780023 := bstep (se 1 (by rfl) ⟨1335017, by rfl⟩ : syracuseStep 1780023 = 2670035) B2670035
theorem B5409089 : Blo 1778090 5409089 := bstep (se 2 (by rfl) ⟨2028408, by rfl⟩ : syracuseStep 5409089 = 4056817) B4056817
theorem B1780043 : Blo 1778090 1780043 := bstep (se 1 (by rfl) ⟨1335032, by rfl⟩ : syracuseStep 1780043 = 2670065) B2670065
theorem B1780055 : Blo 1778090 1780055 := bstep (se 1 (by rfl) ⟨1335041, by rfl⟩ : syracuseStep 1780055 = 2670083) B2670083
theorem B3000665 : Blo 1778090 3000665 := bstep (se 2 (by rfl) ⟨1125249, by rfl⟩ : syracuseStep 3000665 = 2250499) B2250499
theorem B6752605 : Blo 1778090 6752605 := bstep (se 3 (by rfl) ⟨1266113, by rfl⟩ : syracuseStep 6752605 = 2532227) B2532227
theorem B1780075 : Blo 1778090 1780075 := bstep (se 1 (by rfl) ⟨1335056, by rfl⟩ : syracuseStep 1780075 = 2670113) B2670113
theorem B2001271 : Blo 1778090 2001271 := bstep (se 1 (by rfl) ⟨1500953, by rfl⟩ : syracuseStep 2001271 = 3001907) B3001907
theorem B1780087 : Blo 1778090 1780087 := bstep (se 1 (by rfl) ⟨1335065, by rfl⟩ : syracuseStep 1780087 = 2670131) B2670131
theorem B2533771 : Blo 1778090 2533771 := bstep (se 1 (by rfl) ⟨1900328, by rfl⟩ : syracuseStep 2533771 = 3800657) B3800657
theorem B17090995 : Blo 1778090 17090995 := bstep (se 1 (by rfl) ⟨12818246, by rfl⟩ : syracuseStep 17090995 = 25636493) B25636493
theorem B3000793 : Blo 1778090 3000793 := bstep (se 2 (by rfl) ⟨1125297, by rfl⟩ : syracuseStep 3000793 = 2250595) B2250595
theorem B2001451 : Blo 1778090 2001451 := bstep (se 1 (by rfl) ⟨1501088, by rfl⟩ : syracuseStep 2001451 = 3002177) B3002177
theorem B2001559 : Blo 1778090 2001559 := bstep (se 1 (by rfl) ⟨1501169, by rfl⟩ : syracuseStep 2001559 = 3002339) B3002339
theorem B7211693 : Blo 1778090 7211693 := bstep (se 3 (by rfl) ⟨1352192, by rfl⟩ : syracuseStep 7211693 = 2704385) B2704385
theorem B6007499 : Blo 1778090 6007499 := bstep (se 1 (by rfl) ⟨4505624, by rfl⟩ : syracuseStep 6007499 = 9011249) B9011249
theorem B7211821 : Blo 1778090 7211821 := bstep (se 3 (by rfl) ⟨1352216, by rfl⟩ : syracuseStep 7211821 = 2704433) B2704433
theorem B5065537 : Blo 1778090 5065537 := bstep (se 2 (by rfl) ⟨1899576, by rfl⟩ : syracuseStep 5065537 = 3799153) B3799153
theorem B2001739 : Blo 1778090 2001739 := bstep (se 1 (by rfl) ⟨1501304, by rfl⟩ : syracuseStep 2001739 = 3002609) B3002609
theorem B2001847 : Blo 1778090 2001847 := bstep (se 1 (by rfl) ⟨1501385, by rfl⟩ : syracuseStep 2001847 = 3002771) B3002771
theorem B4000715 : Blo 1778090 4000715 := bstep (se 1 (by rfl) ⟨3000536, by rfl⟩ : syracuseStep 4000715 = 6001073) B6001073
theorem B12331993 : Blo 1778090 12331993 := bstep (se 2 (by rfl) ⟨4624497, by rfl⟩ : syracuseStep 12331993 = 9248995) B9248995
theorem B6007769 : Blo 1778090 6007769 := bstep (se 2 (by rfl) ⟨2252913, by rfl⟩ : syracuseStep 6007769 = 4505827) B4505827
theorem B4000769 : Blo 1778090 4000769 := bstep (se 2 (by rfl) ⟨1500288, by rfl⟩ : syracuseStep 4000769 = 3000577) B3000577
theorem B3001367 : Blo 1778090 3001367 := bstep (se 1 (by rfl) ⟨2251025, by rfl⟩ : syracuseStep 3001367 = 4502051) B4502051
theorem B2002027 : Blo 1778090 2002027 := bstep (se 1 (by rfl) ⟨1501520, by rfl⟩ : syracuseStep 2002027 = 3003041) B3003041
theorem B3001495 : Blo 1778090 3001495 := bstep (se 1 (by rfl) ⟨2251121, by rfl⟩ : syracuseStep 3001495 = 4502243) B4502243
theorem B2002135 : Blo 1778090 2002135 := bstep (se 1 (by rfl) ⟨1501601, by rfl⟩ : syracuseStep 2002135 = 3003203) B3003203
theorem B4000985 : Blo 1778090 4000985 := bstep (se 2 (by rfl) ⟨1500369, by rfl⟩ : syracuseStep 4000985 = 3000739) B3000739
theorem B4001075 : Blo 1778090 4001075 := bstep (se 1 (by rfl) ⟨3000806, by rfl⟩ : syracuseStep 4001075 = 6001613) B6001613
theorem B5557555 : Blo 1778090 5557555 := bstep (se 1 (by rfl) ⟨4168166, by rfl⟩ : syracuseStep 5557555 = 8336333) B8336333
theorem B4001111 : Blo 1778090 4001111 := bstep (se 1 (by rfl) ⟨3000833, by rfl⟩ : syracuseStep 4001111 = 6001667) B6001667
theorem B2002315 : Blo 1778090 2002315 := bstep (se 1 (by rfl) ⟨1501736, by rfl⟩ : syracuseStep 2002315 = 3003473) B3003473
theorem B3378611 : Blo 1778090 3378611 := bstep (se 1 (by rfl) ⟨2533958, by rfl⟩ : syracuseStep 3378611 = 5067917) B5067917
theorem B2002423 : Blo 1778090 2002423 := bstep (se 1 (by rfl) ⟨1501817, by rfl⟩ : syracuseStep 2002423 = 3003635) B3003635
theorem B4001291 : Blo 1778090 4001291 := bstep (se 1 (by rfl) ⟨3000968, by rfl⟩ : syracuseStep 4001291 = 6001937) B6001937
theorem B5410327 : Blo 1778090 5410327 := bstep (se 1 (by rfl) ⟨4057745, by rfl⟩ : syracuseStep 5410327 = 8115491) B8115491
theorem B4001345 : Blo 1778090 4001345 := bstep (se 2 (by rfl) ⟨1500504, by rfl⟩ : syracuseStep 4001345 = 3001009) B3001009
theorem B13512257 : Blo 1778090 13512257 := bstep (se 2 (by rfl) ⟨5067096, by rfl⟩ : syracuseStep 13512257 = 10134193) B10134193
theorem B3378763 : Blo 1778090 3378763 := bstep (se 1 (by rfl) ⟨2534072, by rfl⟩ : syracuseStep 3378763 = 5068145) B5068145
theorem B6409817 : Blo 1778090 6409817 := bstep (se 2 (by rfl) ⟨2403681, by rfl⟩ : syracuseStep 6409817 = 4807363) B4807363
theorem B6753881 : Blo 1778090 6753881 := bstep (se 2 (by rfl) ⟨2532705, by rfl⟩ : syracuseStep 6753881 = 5065411) B5065411
theorem B7704209 : Blo 1778090 7704209 := bstep (se 2 (by rfl) ⟨2889078, by rfl⟩ : syracuseStep 7704209 = 5778157) B5778157
theorem B3002123 : Blo 1778090 3002123 := bstep (se 1 (by rfl) ⟨2251592, by rfl⟩ : syracuseStep 3002123 = 4503185) B4503185
theorem B4501271 : Blo 1778090 4501271 := bstep (se 1 (by rfl) ⟨3375953, by rfl⟩ : syracuseStep 4501271 = 6751907) B6751907
theorem B4001561 : Blo 1778090 4001561 := bstep (se 2 (by rfl) ⟨1500585, by rfl⟩ : syracuseStep 4001561 = 3001171) B3001171
theorem B4001651 : Blo 1778090 4001651 := bstep (se 1 (by rfl) ⟨3001238, by rfl⟩ : syracuseStep 4001651 = 6002477) B6002477
theorem B3002251 : Blo 1778090 3002251 := bstep (se 1 (by rfl) ⟨2251688, by rfl⟩ : syracuseStep 3002251 = 4503377) B4503377
theorem B3608459 : Blo 1778090 3608459 := bstep (se 1 (by rfl) ⟨2706344, by rfl⟩ : syracuseStep 3608459 = 5412689) B5412689
theorem B4001687 : Blo 1778090 4001687 := bstep (se 1 (by rfl) ⟨3001265, by rfl⟩ : syracuseStep 4001687 = 6002531) B6002531
theorem B3379097 : Blo 1778090 3379097 := bstep (se 2 (by rfl) ⟨1267161, by rfl⟩ : syracuseStep 3379097 = 2534323) B2534323
theorem B7598083 : Blo 1778090 7598083 := bstep (se 1 (by rfl) ⟨5698562, by rfl⟩ : syracuseStep 7598083 = 11397125) B11397125
theorem B3002393 : Blo 1778090 3002393 := bstep (se 2 (by rfl) ⟨1125897, by rfl⟩ : syracuseStep 3002393 = 2251795) B2251795
theorem B7213121 : Blo 1778090 7213121 := bstep (se 2 (by rfl) ⟨2704920, by rfl⟩ : syracuseStep 7213121 = 5409841) B5409841
theorem B4001867 : Blo 1778090 4001867 := bstep (se 1 (by rfl) ⟨3001400, by rfl⟩ : syracuseStep 4001867 = 6002801) B6002801
theorem B4001921 : Blo 1778090 4001921 := bstep (se 2 (by rfl) ⟨1500720, by rfl⟩ : syracuseStep 4001921 = 3001441) B3001441
theorem B3002521 : Blo 1778090 3002521 := bstep (se 2 (by rfl) ⟨1125945, by rfl⟩ : syracuseStep 3002521 = 2251891) B2251891
theorem B15192269 : Blo 1778090 15192269 := bstep (se 3 (by rfl) ⟨2848550, by rfl⟩ : syracuseStep 15192269 = 5697101) B5697101
theorem B3207475 : Blo 1778090 3207475 := bstep (se 1 (by rfl) ⟨2405606, by rfl⟩ : syracuseStep 3207475 = 4811213) B4811213
theorem B4002137 : Blo 1778090 4002137 := bstep (se 2 (by rfl) ⟨1500801, by rfl⟩ : syracuseStep 4002137 = 3001603) B3001603
theorem B4501939 : Blo 1778090 4501939 := bstep (se 1 (by rfl) ⟨3376454, by rfl⟩ : syracuseStep 4501939 = 6752909) B6752909
theorem B4002227 : Blo 1778090 4002227 := bstep (se 1 (by rfl) ⟨3001670, by rfl⟩ : syracuseStep 4002227 = 6003341) B6003341
theorem B5067211 : Blo 1778090 5067211 := bstep (se 1 (by rfl) ⟨3800408, by rfl⟩ : syracuseStep 5067211 = 7600817) B7600817
theorem B4002263 : Blo 1778090 4002263 := bstep (se 1 (by rfl) ⟨3001697, by rfl⟩ : syracuseStep 4002263 = 6003395) B6003395
theorem B3043801 : Blo 1778090 3043801 := bstep (se 2 (by rfl) ⟨1141425, by rfl⟩ : syracuseStep 3043801 = 2282851) B2282851
theorem B3207691 : Blo 1778090 3207691 := bstep (se 1 (by rfl) ⟨2405768, by rfl⟩ : syracuseStep 3207691 = 4811537) B4811537
theorem B4502081 : Blo 1778090 4502081 := bstep (se 2 (by rfl) ⟨1688280, by rfl⟩ : syracuseStep 4502081 = 3376561) B3376561
theorem B4002443 : Blo 1778090 4002443 := bstep (se 1 (by rfl) ⟨3001832, by rfl⟩ : syracuseStep 4002443 = 6003665) B6003665
theorem B2667161 : Blo 1778090 2667161 := bstep (se 2 (by rfl) ⟨1000185, by rfl⟩ : syracuseStep 2667161 = 2000371) B2000371
theorem B4002497 : Blo 1778090 4002497 := bstep (se 2 (by rfl) ⟨1500936, by rfl⟩ : syracuseStep 4002497 = 3001873) B3001873
theorem B3003095 : Blo 1778090 3003095 := bstep (se 1 (by rfl) ⟨2252321, by rfl⟩ : syracuseStep 3003095 = 4504643) B4504643
theorem B6410969 : Blo 1778090 6410969 := bstep (se 2 (by rfl) ⟨2404113, by rfl⟩ : syracuseStep 6410969 = 4808227) B4808227
theorem B5067485 : Blo 1778090 5067485 := bstep (se 3 (by rfl) ⟨950153, by rfl⟩ : syracuseStep 5067485 = 1900307) B1900307
theorem B2667275 : Blo 1778090 2667275 := bstep (se 1 (by rfl) ⟨2000456, by rfl⟩ : syracuseStep 2667275 = 4000913) B4000913
theorem B2667287 : Blo 1778090 2667287 := bstep (se 1 (by rfl) ⟨2000465, by rfl⟩ : syracuseStep 2667287 = 4000931) B4000931
theorem B24343361 : Blo 1778090 24343361 := bstep (se 2 (by rfl) ⟨9128760, by rfl⟩ : syracuseStep 24343361 = 18257521) B18257521
theorem B3003223 : Blo 1778090 3003223 := bstep (se 1 (by rfl) ⟨2252417, by rfl⟩ : syracuseStep 3003223 = 4504835) B4504835
theorem B2667353 : Blo 1778090 2667353 := bstep (se 2 (by rfl) ⟨1000257, by rfl⟩ : syracuseStep 2667353 = 2000515) B2000515
theorem B6001559 : Blo 1778090 6001559 := bstep (se 1 (by rfl) ⟨4501169, by rfl⟩ : syracuseStep 6001559 = 9002339) B9002339
theorem B4002713 : Blo 1778090 4002713 := bstep (se 2 (by rfl) ⟨1501017, by rfl⟩ : syracuseStep 4002713 = 3002035) B3002035
theorem B7599041 : Blo 1778090 7599041 := bstep (se 2 (by rfl) ⟨2849640, by rfl⟩ : syracuseStep 7599041 = 5699281) B5699281
theorem B2667467 : Blo 1778090 2667467 := bstep (se 1 (by rfl) ⟨2000600, by rfl⟩ : syracuseStep 2667467 = 4001201) B4001201
theorem B2667479 : Blo 1778090 2667479 := bstep (se 1 (by rfl) ⟨2000609, by rfl⟩ : syracuseStep 2667479 = 4001219) B4001219
theorem B5698525 : Blo 1778090 5698525 := bstep (se 3 (by rfl) ⟨1068473, by rfl⟩ : syracuseStep 5698525 = 2136947) B2136947
theorem B4002803 : Blo 1778090 4002803 := bstep (se 1 (by rfl) ⟨3002102, by rfl⟩ : syracuseStep 4002803 = 6004205) B6004205
theorem B29258765 : Blo 1778090 29258765 := bstep (se 3 (by rfl) ⟨5486018, by rfl⟩ : syracuseStep 29258765 = 10972037) B10972037
theorem B4002839 : Blo 1778090 4002839 := bstep (se 1 (by rfl) ⟨3002129, by rfl⟩ : syracuseStep 4002839 = 6004259) B6004259
theorem B2667545 : Blo 1778090 2667545 := bstep (se 2 (by rfl) ⟨1000329, by rfl⟩ : syracuseStep 2667545 = 2000659) B2000659
theorem B13718659 : Blo 1778090 13718659 := bstep (se 1 (by rfl) ⟨10288994, by rfl⟩ : syracuseStep 13718659 = 20577989) B20577989
theorem B2667659 : Blo 1778090 2667659 := bstep (se 1 (by rfl) ⟨2000744, by rfl⟩ : syracuseStep 2667659 = 4001489) B4001489
theorem B2667671 : Blo 1778090 2667671 := bstep (se 1 (by rfl) ⟨2000753, by rfl⟩ : syracuseStep 2667671 = 4001507) B4001507
theorem B32453783 : Blo 1778090 32453783 := bstep (se 1 (by rfl) ⟨24340337, by rfl⟩ : syracuseStep 32453783 = 48680675) B48680675
theorem B6755507 : Blo 1778090 6755507 := bstep (se 1 (by rfl) ⟨5066630, by rfl⟩ : syracuseStep 6755507 = 10133261) B10133261
theorem B61600949 : Blo 1778090 61600949 := bstep (se 5 (by rfl) ⟨2887544, by rfl⟩ : syracuseStep 61600949 = 5775089) B5775089
theorem B6755521 : Blo 1778090 6755521 := bstep (se 2 (by rfl) ⟨2533320, by rfl⟩ : syracuseStep 6755521 = 5066641) B5066641
theorem B4003019 : Blo 1778090 4003019 := bstep (se 1 (by rfl) ⟨3002264, by rfl⟩ : syracuseStep 4003019 = 6004529) B6004529
theorem B2667737 : Blo 1778090 2667737 := bstep (se 2 (by rfl) ⟨1000401, by rfl⟩ : syracuseStep 2667737 = 2000803) B2000803
theorem B4003073 : Blo 1778090 4003073 := bstep (se 2 (by rfl) ⟨1501152, by rfl⟩ : syracuseStep 4003073 = 3002305) B3002305
theorem B2667851 : Blo 1778090 2667851 := bstep (se 1 (by rfl) ⟨2000888, by rfl⟩ : syracuseStep 2667851 = 4001777) B4001777
theorem B2667863 : Blo 1778090 2667863 := bstep (se 1 (by rfl) ⟨2000897, by rfl⟩ : syracuseStep 2667863 = 4001795) B4001795
theorem B2667929 : Blo 1778090 2667929 := bstep (se 2 (by rfl) ⟨1000473, by rfl⟩ : syracuseStep 2667929 = 2000947) B2000947
theorem B6002099 : Blo 1778090 6002099 := bstep (se 1 (by rfl) ⟨4501574, by rfl⟩ : syracuseStep 6002099 = 9003149) B9003149
theorem B9614771 : Blo 1778090 9614771 := bstep (se 1 (by rfl) ⟨7211078, by rfl⟩ : syracuseStep 9614771 = 14422157) B14422157
theorem B8115635 : Blo 1778090 8115635 := bstep (se 1 (by rfl) ⟨6086726, by rfl⟩ : syracuseStep 8115635 = 12173453) B12173453
theorem B28865969 : Blo 1778090 28865969 := bstep (se 2 (by rfl) ⟨10824738, by rfl⟩ : syracuseStep 28865969 = 21649477) B21649477
theorem B3003851 : Blo 1778090 3003851 := bstep (se 1 (by rfl) ⟨2252888, by rfl⟩ : syracuseStep 3003851 = 4505777) B4505777
theorem B4003289 : Blo 1778090 4003289 := bstep (se 2 (by rfl) ⟨1501233, by rfl⟩ : syracuseStep 4003289 = 3002467) B3002467
theorem B13514201 : Blo 1778090 13514201 := bstep (se 2 (by rfl) ⟨5067825, by rfl⟩ : syracuseStep 13514201 = 10135651) B10135651
theorem B2668043 : Blo 1778090 2668043 := bstep (se 1 (by rfl) ⟨2001032, by rfl⟩ : syracuseStep 2668043 = 4002065) B4002065
theorem B9008657 : Blo 1778090 9008657 := bstep (se 2 (by rfl) ⟨3378246, by rfl⟩ : syracuseStep 9008657 = 6756493) B6756493
theorem B2668055 : Blo 1778090 2668055 := bstep (se 1 (by rfl) ⟨2001041, by rfl⟩ : syracuseStep 2668055 = 4002083) B4002083
theorem B4003379 : Blo 1778090 4003379 := bstep (se 1 (by rfl) ⟨3002534, by rfl⟩ : syracuseStep 4003379 = 6005069) B6005069
theorem B4003415 : Blo 1778090 4003415 := bstep (se 1 (by rfl) ⟨3002561, by rfl⟩ : syracuseStep 4003415 = 6005123) B6005123
theorem B2668121 : Blo 1778090 2668121 := bstep (se 2 (by rfl) ⟨1000545, by rfl⟩ : syracuseStep 2668121 = 2001091) B2001091
theorem B10131095 : Blo 1778090 10131095 := bstep (se 1 (by rfl) ⟨7598321, by rfl⟩ : syracuseStep 10131095 = 15196643) B15196643
theorem B15398579 : Blo 1778090 15398579 := bstep (se 1 (by rfl) ⟨11548934, by rfl⟩ : syracuseStep 15398579 = 23097869) B23097869
theorem B9008819 : Blo 1778090 9008819 := bstep (se 1 (by rfl) ⟨6756614, by rfl⟩ : syracuseStep 9008819 = 13513229) B13513229
theorem B6002369 : Blo 1778090 6002369 := bstep (se 2 (by rfl) ⟨2250888, by rfl⟩ : syracuseStep 6002369 = 4501777) B4501777
theorem B2250443 : Blo 1778090 2250443 := bstep (se 1 (by rfl) ⟨1687832, by rfl⟩ : syracuseStep 2250443 = 3375665) B3375665
theorem B2668235 : Blo 1778090 2668235 := bstep (se 1 (by rfl) ⟨2001176, by rfl⟩ : syracuseStep 2668235 = 4002353) B4002353
theorem B2668247 : Blo 1778090 2668247 := bstep (se 1 (by rfl) ⟨2001185, by rfl⟩ : syracuseStep 2668247 = 4002371) B4002371
theorem B3798785 : Blo 1778090 3798785 := bstep (se 2 (by rfl) ⟨1424544, by rfl⟩ : syracuseStep 3798785 = 2849089) B2849089
theorem B4003595 : Blo 1778090 4003595 := bstep (se 1 (by rfl) ⟨3002696, by rfl⟩ : syracuseStep 4003595 = 6005393) B6005393
theorem B2668313 : Blo 1778090 2668313 := bstep (se 2 (by rfl) ⟨1000617, by rfl⟩ : syracuseStep 2668313 = 2001235) B2001235
theorem B4503347 : Blo 1778090 4503347 := bstep (se 1 (by rfl) ⟨3377510, by rfl⟩ : syracuseStep 4503347 = 6755021) B6755021
theorem B4003649 : Blo 1778090 4003649 := bstep (se 2 (by rfl) ⟨1501368, by rfl⟩ : syracuseStep 4003649 = 3002737) B3002737
theorem B2668427 : Blo 1778090 2668427 := bstep (se 1 (by rfl) ⟨2001320, by rfl⟩ : syracuseStep 2668427 = 4002641) B4002641
theorem B2668439 : Blo 1778090 2668439 := bstep (se 1 (by rfl) ⟨2001329, by rfl⟩ : syracuseStep 2668439 = 4002659) B4002659
theorem B2668505 : Blo 1778090 2668505 := bstep (se 2 (by rfl) ⟨1000689, by rfl⟩ : syracuseStep 2668505 = 2001379) B2001379
theorem B4003865 : Blo 1778090 4003865 := bstep (se 2 (by rfl) ⟨1501449, by rfl⟩ : syracuseStep 4003865 = 3002899) B3002899
theorem B2668619 : Blo 1778090 2668619 := bstep (se 1 (by rfl) ⟨2001464, by rfl⟩ : syracuseStep 2668619 = 4002929) B4002929
theorem B2668631 : Blo 1778090 2668631 := bstep (se 1 (by rfl) ⟨2001473, by rfl⟩ : syracuseStep 2668631 = 4002947) B4002947
theorem B4003955 : Blo 1778090 4003955 := bstep (se 1 (by rfl) ⟨3002966, by rfl⟩ : syracuseStep 4003955 = 6005933) B6005933
theorem B4003991 : Blo 1778090 4003991 := bstep (se 1 (by rfl) ⟨3002993, by rfl⟩ : syracuseStep 4003991 = 6005987) B6005987
theorem B2668697 : Blo 1778090 2668697 := bstep (se 2 (by rfl) ⟨1000761, by rfl⟩ : syracuseStep 2668697 = 2001523) B2001523
theorem B6002909 : Blo 1778090 6002909 := bstep (se 3 (by rfl) ⟨1125545, by rfl⟩ : syracuseStep 6002909 = 2251091) B2251091
theorem B2668811 : Blo 1778090 2668811 := bstep (se 1 (by rfl) ⟨2001608, by rfl⟩ : syracuseStep 2668811 = 4003217) B4003217
theorem B2668823 : Blo 1778090 2668823 := bstep (se 1 (by rfl) ⟨2001617, by rfl⟩ : syracuseStep 2668823 = 4003235) B4003235
theorem B3471641 : Blo 1778090 3471641 := bstep (se 2 (by rfl) ⟨1301865, by rfl⟩ : syracuseStep 3471641 = 2603731) B2603731
theorem B4503883 : Blo 1778090 4503883 := bstep (se 1 (by rfl) ⟨3377912, by rfl⟩ : syracuseStep 4503883 = 6755825) B6755825
theorem B4004171 : Blo 1778090 4004171 := bstep (se 1 (by rfl) ⟨3003128, by rfl⟩ : syracuseStep 4004171 = 6006257) B6006257
theorem B2668889 : Blo 1778090 2668889 := bstep (se 2 (by rfl) ⟨1000833, by rfl⟩ : syracuseStep 2668889 = 2001667) B2001667
theorem B4004225 : Blo 1778090 4004225 := bstep (se 2 (by rfl) ⟨1501584, by rfl⟩ : syracuseStep 4004225 = 3003169) B3003169
theorem B2251147 : Blo 1778090 2251147 := bstep (se 1 (by rfl) ⟨1688360, by rfl⟩ : syracuseStep 2251147 = 3376721) B3376721
theorem B2669003 : Blo 1778090 2669003 := bstep (se 1 (by rfl) ⟨2001752, by rfl⟩ : syracuseStep 2669003 = 4003505) B4003505
theorem B2669015 : Blo 1778090 2669015 := bstep (se 1 (by rfl) ⟨2001761, by rfl⟩ : syracuseStep 2669015 = 4003523) B4003523
theorem B4504025 : Blo 1778090 4504025 := bstep (se 2 (by rfl) ⟨1689009, by rfl⟩ : syracuseStep 4504025 = 3378019) B3378019
theorem B5134871 : Blo 1778090 5134871 := bstep (se 1 (by rfl) ⟨3851153, by rfl⟩ : syracuseStep 5134871 = 7702307) B7702307
theorem B2669081 : Blo 1778090 2669081 := bstep (se 2 (by rfl) ⟨1000905, by rfl⟩ : syracuseStep 2669081 = 2001811) B2001811
theorem B7600715 : Blo 1778090 7600715 := bstep (se 1 (by rfl) ⟨5700536, by rfl⟩ : syracuseStep 7600715 = 11401073) B11401073
theorem B3799639 : Blo 1778090 3799639 := bstep (se 1 (by rfl) ⟨2849729, by rfl⟩ : syracuseStep 3799639 = 5699459) B5699459
theorem B4004441 : Blo 1778090 4004441 := bstep (se 2 (by rfl) ⟨1501665, by rfl⟩ : syracuseStep 4004441 = 3003331) B3003331
theorem B2669195 : Blo 1778090 2669195 := bstep (se 1 (by rfl) ⟨2001896, by rfl⟩ : syracuseStep 2669195 = 4003793) B4003793
theorem B2251415 : Blo 1778090 2251415 := bstep (se 1 (by rfl) ⟨1688561, by rfl⟩ : syracuseStep 2251415 = 3377123) B3377123
theorem B2669207 : Blo 1778090 2669207 := bstep (se 1 (by rfl) ⟨2001905, by rfl⟩ : syracuseStep 2669207 = 4003811) B4003811
theorem B4004531 : Blo 1778090 4004531 := bstep (se 1 (by rfl) ⟨3003398, by rfl⟩ : syracuseStep 4004531 = 6006797) B6006797
theorem B4004567 : Blo 1778090 4004567 := bstep (se 1 (by rfl) ⟨3003425, by rfl⟩ : syracuseStep 4004567 = 6006851) B6006851
theorem B2669273 : Blo 1778090 2669273 := bstep (se 2 (by rfl) ⟨1000977, by rfl⟩ : syracuseStep 2669273 = 2001955) B2001955
theorem B1899307 : Blo 1778090 1899307 := bstep (se 1 (by rfl) ⟨1424480, by rfl⟩ : syracuseStep 1899307 = 2848961) B2848961
theorem B2669387 : Blo 1778090 2669387 := bstep (se 1 (by rfl) ⟨2002040, by rfl⟩ : syracuseStep 2669387 = 4004081) B4004081
theorem B2669399 : Blo 1778090 2669399 := bstep (se 1 (by rfl) ⟨2002049, by rfl⟩ : syracuseStep 2669399 = 4004099) B4004099
theorem B7215961 : Blo 1778090 7215961 := bstep (se 2 (by rfl) ⟨2705985, by rfl⟩ : syracuseStep 7215961 = 5411971) B5411971
theorem B4004747 : Blo 1778090 4004747 := bstep (se 1 (by rfl) ⟨3003560, by rfl⟩ : syracuseStep 4004747 = 6007121) B6007121
theorem B2669465 : Blo 1778090 2669465 := bstep (se 2 (by rfl) ⟨1001049, by rfl⟩ : syracuseStep 2669465 = 2002099) B2002099
theorem B4004801 : Blo 1778090 4004801 := bstep (se 2 (by rfl) ⟨1501800, by rfl⟩ : syracuseStep 4004801 = 3003601) B3003601
theorem B2669579 : Blo 1778090 2669579 := bstep (se 1 (by rfl) ⟨2002184, by rfl⟩ : syracuseStep 2669579 = 4004369) B4004369
theorem B2669591 : Blo 1778090 2669591 := bstep (se 1 (by rfl) ⟨2002193, by rfl⟩ : syracuseStep 2669591 = 4004387) B4004387
theorem B6757451 : Blo 1778090 6757451 := bstep (se 1 (by rfl) ⟨5068088, by rfl⟩ : syracuseStep 6757451 = 10136177) B10136177
theorem B6757465 : Blo 1778090 6757465 := bstep (se 2 (by rfl) ⟨2534049, by rfl⟩ : syracuseStep 6757465 = 5068099) B5068099
theorem B2669657 : Blo 1778090 2669657 := bstep (se 2 (by rfl) ⟨1001121, by rfl⟩ : syracuseStep 2669657 = 2002243) B2002243
theorem B11394179 : Blo 1778090 11394179 := bstep (se 1 (by rfl) ⟨8545634, by rfl⟩ : syracuseStep 11394179 = 17091269) B17091269
theorem B6937745 : Blo 1778090 6937745 := bstep (se 2 (by rfl) ⟨2601654, by rfl⟩ : syracuseStep 6937745 = 5203309) B5203309
theorem B4005017 : Blo 1778090 4005017 := bstep (se 2 (by rfl) ⟨1501881, by rfl⟩ : syracuseStep 4005017 = 3003763) B3003763
theorem B2669771 : Blo 1778090 2669771 := bstep (se 1 (by rfl) ⟨2002328, by rfl⟩ : syracuseStep 2669771 = 4004657) B4004657
theorem B2669783 : Blo 1778090 2669783 := bstep (se 1 (by rfl) ⟨2002337, by rfl⟩ : syracuseStep 2669783 = 4004675) B4004675
theorem B6167773 : Blo 1778090 6167773 := bstep (se 3 (by rfl) ⟨1156457, by rfl⟩ : syracuseStep 6167773 = 2312915) B2312915
theorem B6085853 : Blo 1778090 6085853 := bstep (se 3 (by rfl) ⟨1141097, by rfl⟩ : syracuseStep 6085853 = 2282195) B2282195
theorem B4005107 : Blo 1778090 4005107 := bstep (se 1 (by rfl) ⟨3003830, by rfl⟩ : syracuseStep 4005107 = 6007661) B6007661
theorem B4275479 : Blo 1778090 4275479 := bstep (se 1 (by rfl) ⟨3206609, by rfl⟩ : syracuseStep 4275479 = 6413219) B6413219
theorem B4504855 : Blo 1778090 4504855 := bstep (se 1 (by rfl) ⟨3378641, by rfl⟩ : syracuseStep 4504855 = 6757283) B6757283
theorem B2669849 : Blo 1778090 2669849 := bstep (se 2 (by rfl) ⟨1001193, by rfl⟩ : syracuseStep 2669849 = 2002387) B2002387
theorem B4005143 : Blo 1778090 4005143 := bstep (se 1 (by rfl) ⟨3003857, by rfl⟩ : syracuseStep 4005143 = 6007715) B6007715
theorem B6004043 : Blo 1778090 6004043 := bstep (se 1 (by rfl) ⟨4503032, by rfl⟩ : syracuseStep 6004043 = 9006065) B9006065
theorem B2252119 : Blo 1778090 2252119 := bstep (se 1 (by rfl) ⟨1689089, by rfl⟩ : syracuseStep 2252119 = 3378179) B3378179
theorem B2669963 : Blo 1778090 2669963 := bstep (se 1 (by rfl) ⟨2002472, by rfl⟩ : syracuseStep 2669963 = 4004945) B4004945
theorem B2669975 : Blo 1778090 2669975 := bstep (se 1 (by rfl) ⟨2002481, by rfl⟩ : syracuseStep 2669975 = 4004963) B4004963
theorem B2670041 : Blo 1778090 2670041 := bstep (se 2 (by rfl) ⟨1001265, by rfl⟩ : syracuseStep 2670041 = 2002531) B2002531
theorem B10133009 : Blo 1778090 10133009 := bstep (se 2 (by rfl) ⟨3799878, by rfl⟩ : syracuseStep 10133009 = 7599757) B7599757
theorem B1900055 : Blo 1778090 1900055 := bstep (se 1 (by rfl) ⟨1425041, by rfl⟩ : syracuseStep 1900055 = 2850083) B2850083
theorem B8666689 : Blo 1778090 8666689 := bstep (se 2 (by rfl) ⟨3250008, by rfl⟩ : syracuseStep 8666689 = 6500017) B6500017
theorem B4275787 : Blo 1778090 4275787 := bstep (se 1 (by rfl) ⟨3206840, by rfl⟩ : syracuseStep 4275787 = 6413681) B6413681
theorem B9010763 : Blo 1778090 9010763 := bstep (se 1 (by rfl) ⟨6758072, by rfl⟩ : syracuseStep 9010763 = 13516145) B13516145
theorem B6004313 : Blo 1778090 6004313 := bstep (se 2 (by rfl) ⟨2251617, by rfl⟩ : syracuseStep 6004313 = 4503235) B4503235
theorem B14433893 : Blo 1778090 14433893 := bstep (se 4 (by rfl) ⟨1353177, by rfl⟩ : syracuseStep 14433893 = 2706355) B2706355
theorem B4505291 : Blo 1778090 4505291 := bstep (se 1 (by rfl) ⟨3378968, by rfl⟩ : syracuseStep 4505291 = 6757937) B6757937
theorem B3800819 : Blo 1778090 3800819 := bstep (se 1 (by rfl) ⟨2850614, by rfl⟩ : syracuseStep 3800819 = 5701229) B5701229
theorem B13508369 : Blo 1778090 13508369 := bstep (se 2 (by rfl) ⟨5065638, by rfl⟩ : syracuseStep 13508369 = 10131277) B10131277
theorem B1925047 : Blo 1778090 1925047 := bstep (se 1 (by rfl) ⟨1443785, by rfl⟩ : syracuseStep 1925047 = 2887571) B2887571
theorem B4505615 : Blo 1778090 4505615 := bstep (se 1 (by rfl) ⟨3379211, by rfl⟩ : syracuseStep 4505615 = 6758423) B6758423
theorem B4808747 : Blo 1778090 4808747 := bstep (se 1 (by rfl) ⟨3606560, by rfl⟩ : syracuseStep 4808747 = 7213121) B7213121
theorem B36528245 : Blo 1778090 36528245 := bstep (se 5 (by rfl) ⟨1712261, by rfl⟩ : syracuseStep 36528245 = 3424523) B3424523
theorem B2703631 : Blo 1778090 2703631 := bstep (se 1 (by rfl) ⟨2027723, by rfl⟩ : syracuseStep 2703631 = 4055447) B4055447
theorem B7602491 : Blo 1778090 7602491 := bstep (se 1 (by rfl) ⟨5701868, by rfl⟩ : syracuseStep 7602491 = 11403737) B11403737
theorem B12829063 : Blo 1778090 12829063 := bstep (se 1 (by rfl) ⟨9621797, by rfl⟩ : syracuseStep 12829063 = 19243595) B19243595
theorem B4276633 : Blo 1778090 4276633 := bstep (se 2 (by rfl) ⟨1603737, by rfl⟩ : syracuseStep 4276633 = 3207475) B3207475
theorem B6005177 : Blo 1778090 6005177 := bstep (se 2 (by rfl) ⟨2251941, by rfl⟩ : syracuseStep 6005177 = 4503883) B4503883
theorem B1778107 : Blo 1778090 1778107 := bstep (se 1 (by rfl) ⟨1333580, by rfl⟩ : syracuseStep 1778107 = 2667161) B2667161
theorem B9003473 : Blo 1778090 9003473 := bstep (se 2 (by rfl) ⟨3376302, by rfl⟩ : syracuseStep 9003473 = 6752605) B6752605
theorem B1778183 : Blo 1778090 1778183 := bstep (se 1 (by rfl) ⟨1333637, by rfl⟩ : syracuseStep 1778183 = 2667275) B2667275
theorem B4276747 : Blo 1778090 4276747 := bstep (se 1 (by rfl) ⟨3207560, by rfl⟩ : syracuseStep 4276747 = 6415121) B6415121
theorem B1778191 : Blo 1778090 1778191 := bstep (se 1 (by rfl) ⟨1333643, by rfl⟩ : syracuseStep 1778191 = 2667287) B2667287
theorem B36504107 : Blo 1778090 36504107 := bstep (se 1 (by rfl) ⟨27378080, by rfl⟩ : syracuseStep 36504107 = 54756161) B54756161
theorem B16228907 : Blo 1778090 16228907 := bstep (se 1 (by rfl) ⟨12171680, by rfl⟩ : syracuseStep 16228907 = 24343361) B24343361
theorem B7602731 : Blo 1778090 7602731 := bstep (se 1 (by rfl) ⟨5702048, by rfl⟩ : syracuseStep 7602731 = 11404097) B11404097
theorem B1778235 : Blo 1778090 1778235 := bstep (se 1 (by rfl) ⟨1333676, by rfl⟩ : syracuseStep 1778235 = 2667353) B2667353
theorem B34193987 : Blo 1778090 34193987 := bstep (se 1 (by rfl) ⟨25645490, by rfl⟩ : syracuseStep 34193987 = 51290981) B51290981
theorem B1778311 : Blo 1778090 1778311 := bstep (se 1 (by rfl) ⟨1333733, by rfl⟩ : syracuseStep 1778311 = 2667467) B2667467
theorem B1778319 : Blo 1778090 1778319 := bstep (se 1 (by rfl) ⟨1333739, by rfl⟩ : syracuseStep 1778319 = 2667479) B2667479
theorem B19505843 : Blo 1778090 19505843 := bstep (se 1 (by rfl) ⟨14629382, by rfl⟩ : syracuseStep 19505843 = 29258765) B29258765
theorem B1778363 : Blo 1778090 1778363 := bstep (se 1 (by rfl) ⟨1333772, by rfl⟩ : syracuseStep 1778363 = 2667545) B2667545
theorem B1778439 : Blo 1778090 1778439 := bstep (se 1 (by rfl) ⟨1333829, by rfl⟩ : syracuseStep 1778439 = 2667659) B2667659
theorem B1778447 : Blo 1778090 1778447 := bstep (se 1 (by rfl) ⟨1333835, by rfl⟩ : syracuseStep 1778447 = 2667671) B2667671
theorem B21635855 : Blo 1778090 21635855 := bstep (se 1 (by rfl) ⟨16226891, by rfl⟩ : syracuseStep 21635855 = 32453783) B32453783
theorem B41067299 : Blo 1778090 41067299 := bstep (se 1 (by rfl) ⟨30800474, by rfl⟩ : syracuseStep 41067299 = 61600949) B61600949
theorem B3375931 : Blo 1778090 3375931 := bstep (se 1 (by rfl) ⟨2531948, by rfl⟩ : syracuseStep 3375931 = 5063897) B5063897
theorem B1778491 : Blo 1778090 1778491 := bstep (se 1 (by rfl) ⟨1333868, by rfl⟩ : syracuseStep 1778491 = 2667737) B2667737
theorem B8110963 : Blo 1778090 8110963 := bstep (se 1 (by rfl) ⟨6083222, by rfl⟩ : syracuseStep 8110963 = 12166445) B12166445
theorem B5063543 : Blo 1778090 5063543 := bstep (se 1 (by rfl) ⟨3797657, by rfl⟩ : syracuseStep 5063543 = 7595315) B7595315
theorem B1778567 : Blo 1778090 1778567 := bstep (se 1 (by rfl) ⟨1333925, by rfl⟩ : syracuseStep 1778567 = 2667851) B2667851
theorem B1778575 : Blo 1778090 1778575 := bstep (se 1 (by rfl) ⟨1333931, by rfl⟩ : syracuseStep 1778575 = 2667863) B2667863
theorem B7603091 : Blo 1778090 7603091 := bstep (se 1 (by rfl) ⟨5702318, by rfl⟩ : syracuseStep 7603091 = 11404637) B11404637
theorem B1778619 : Blo 1778090 1778619 := bstep (se 1 (by rfl) ⟨1333964, by rfl⟩ : syracuseStep 1778619 = 2667929) B2667929
theorem B19243979 : Blo 1778090 19243979 := bstep (se 1 (by rfl) ⟨14432984, by rfl⟩ : syracuseStep 19243979 = 28865969) B28865969
theorem B1778695 : Blo 1778090 1778695 := bstep (se 1 (by rfl) ⟨1334021, by rfl⟩ : syracuseStep 1778695 = 2668043) B2668043
theorem B6005771 : Blo 1778090 6005771 := bstep (se 1 (by rfl) ⟨4504328, by rfl⟩ : syracuseStep 6005771 = 9008657) B9008657
theorem B1778703 : Blo 1778090 1778703 := bstep (se 1 (by rfl) ⟨1334027, by rfl⟩ : syracuseStep 1778703 = 2668055) B2668055
theorem B1778747 : Blo 1778090 1778747 := bstep (se 1 (by rfl) ⟨1334060, by rfl⟩ : syracuseStep 1778747 = 2668121) B2668121
theorem B10265719 : Blo 1778090 10265719 := bstep (se 1 (by rfl) ⟨7699289, by rfl⟩ : syracuseStep 10265719 = 15398579) B15398579
theorem B6005879 : Blo 1778090 6005879 := bstep (se 1 (by rfl) ⟨4504409, by rfl⟩ : syracuseStep 6005879 = 9008819) B9008819
theorem B1778823 : Blo 1778090 1778823 := bstep (se 1 (by rfl) ⟨1334117, by rfl⟩ : syracuseStep 1778823 = 2668235) B2668235
theorem B1778831 : Blo 1778090 1778831 := bstep (se 1 (by rfl) ⟨1334123, by rfl⟩ : syracuseStep 1778831 = 2668247) B2668247
theorem B1778875 : Blo 1778090 1778875 := bstep (se 1 (by rfl) ⟨1334156, by rfl⟩ : syracuseStep 1778875 = 2668313) B2668313
theorem B1778951 : Blo 1778090 1778951 := bstep (se 1 (by rfl) ⟨1334213, by rfl⟩ : syracuseStep 1778951 = 2668427) B2668427
theorem B1778959 : Blo 1778090 1778959 := bstep (se 1 (by rfl) ⟨1334219, by rfl⟩ : syracuseStep 1778959 = 2668439) B2668439
theorem B16442657 : Blo 1778090 16442657 := bstep (se 2 (by rfl) ⟨6165996, by rfl⟩ : syracuseStep 16442657 = 12331993) B12331993
theorem B3376417 : Blo 1778090 3376417 := bstep (se 2 (by rfl) ⟨1266156, by rfl⟩ : syracuseStep 3376417 = 2532313) B2532313
theorem B1779003 : Blo 1778090 1779003 := bstep (se 1 (by rfl) ⟨1334252, by rfl⟩ : syracuseStep 1779003 = 2668505) B2668505
theorem B1779079 : Blo 1778090 1779079 := bstep (se 1 (by rfl) ⟨1334309, by rfl⟩ : syracuseStep 1779079 = 2668619) B2668619
theorem B1779087 : Blo 1778090 1779087 := bstep (se 1 (by rfl) ⟨1334315, by rfl⟩ : syracuseStep 1779087 = 2668631) B2668631
theorem B1779131 : Blo 1778090 1779131 := bstep (se 1 (by rfl) ⟨1334348, by rfl⟩ : syracuseStep 1779131 = 2668697) B2668697
theorem B1779207 : Blo 1778090 1779207 := bstep (se 1 (by rfl) ⟨1334405, by rfl⟩ : syracuseStep 1779207 = 2668811) B2668811
theorem B8553995 : Blo 1778090 8553995 := bstep (se 1 (by rfl) ⟨6415496, by rfl⟩ : syracuseStep 8553995 = 12830993) B12830993
theorem B1779215 : Blo 1778090 1779215 := bstep (se 1 (by rfl) ⟨1334411, by rfl⟩ : syracuseStep 1779215 = 2668823) B2668823
theorem B3606059 : Blo 1778090 3606059 := bstep (se 1 (by rfl) ⟨2704544, by rfl⟩ : syracuseStep 3606059 = 5409089) B5409089
theorem B2000443 : Blo 1778090 2000443 := bstep (se 1 (by rfl) ⟨1500332, by rfl⟩ : syracuseStep 2000443 = 3000665) B3000665
theorem B1779259 : Blo 1778090 1779259 := bstep (se 1 (by rfl) ⟨1334444, by rfl⟩ : syracuseStep 1779259 = 2668889) B2668889
theorem B29640293 : Blo 1778090 29640293 := bstep (se 4 (by rfl) ⟨2778777, by rfl⟩ : syracuseStep 29640293 = 5557555) B5557555
theorem B1779335 : Blo 1778090 1779335 := bstep (se 1 (by rfl) ⟨1334501, by rfl⟩ : syracuseStep 1779335 = 2669003) B2669003
theorem B1779343 : Blo 1778090 1779343 := bstep (se 1 (by rfl) ⟨1334507, by rfl⟩ : syracuseStep 1779343 = 2669015) B2669015
theorem B1779387 : Blo 1778090 1779387 := bstep (se 1 (by rfl) ⟨1334540, by rfl⟩ : syracuseStep 1779387 = 2669081) B2669081
theorem B6006473 : Blo 1778090 6006473 := bstep (se 2 (by rfl) ⟨2252427, by rfl⟩ : syracuseStep 6006473 = 4504855) B4504855
theorem B1779463 : Blo 1778090 1779463 := bstep (se 1 (by rfl) ⟨1334597, by rfl⟩ : syracuseStep 1779463 = 2669195) B2669195
theorem B1779471 : Blo 1778090 1779471 := bstep (se 1 (by rfl) ⟨1334603, by rfl⟩ : syracuseStep 1779471 = 2669207) B2669207
theorem B1779515 : Blo 1778090 1779515 := bstep (se 1 (by rfl) ⟨1334636, by rfl⟩ : syracuseStep 1779515 = 2669273) B2669273
theorem B1779591 : Blo 1778090 1779591 := bstep (se 1 (by rfl) ⟨1334693, by rfl⟩ : syracuseStep 1779591 = 2669387) B2669387
theorem B1779599 : Blo 1778090 1779599 := bstep (se 1 (by rfl) ⟨1334699, by rfl⟩ : syracuseStep 1779599 = 2669399) B2669399
theorem B1779643 : Blo 1778090 1779643 := bstep (se 1 (by rfl) ⟨1334732, by rfl⟩ : syracuseStep 1779643 = 2669465) B2669465
theorem B1779719 : Blo 1778090 1779719 := bstep (se 1 (by rfl) ⟨1334789, by rfl⟩ : syracuseStep 1779719 = 2669579) B2669579
theorem B2000911 : Blo 1778090 2000911 := bstep (se 1 (by rfl) ⟨1500683, by rfl⟩ : syracuseStep 2000911 = 3001367) B3001367
theorem B1779727 : Blo 1778090 1779727 := bstep (se 1 (by rfl) ⟨1334795, by rfl⟩ : syracuseStep 1779727 = 2669591) B2669591
theorem B1779771 : Blo 1778090 1779771 := bstep (se 1 (by rfl) ⟨1334828, by rfl⟩ : syracuseStep 1779771 = 2669657) B2669657
theorem B7596119 : Blo 1778090 7596119 := bstep (se 1 (by rfl) ⟨5697089, by rfl⟩ : syracuseStep 7596119 = 11394179) B11394179
theorem B1779847 : Blo 1778090 1779847 := bstep (se 1 (by rfl) ⟨1334885, by rfl⟩ : syracuseStep 1779847 = 2669771) B2669771
theorem B1779855 : Blo 1778090 1779855 := bstep (se 1 (by rfl) ⟨1334891, by rfl⟩ : syracuseStep 1779855 = 2669783) B2669783
theorem B4057235 : Blo 1778090 4057235 := bstep (se 1 (by rfl) ⟨3042926, by rfl⟩ : syracuseStep 4057235 = 6085853) B6085853
theorem B1779899 : Blo 1778090 1779899 := bstep (se 1 (by rfl) ⟨1334924, by rfl⟩ : syracuseStep 1779899 = 2669849) B2669849
theorem B1779975 : Blo 1778090 1779975 := bstep (se 1 (by rfl) ⟨1334981, by rfl⟩ : syracuseStep 1779975 = 2669963) B2669963
theorem B1779983 : Blo 1778090 1779983 := bstep (se 1 (by rfl) ⟨1334987, by rfl⟩ : syracuseStep 1779983 = 2669975) B2669975
theorem B10266917 : Blo 1778090 10266917 := bstep (se 4 (by rfl) ⟨962523, by rfl⟩ : syracuseStep 10266917 = 1925047) B1925047
theorem B1780027 : Blo 1778090 1780027 := bstep (se 1 (by rfl) ⟨1335020, by rfl⟩ : syracuseStep 1780027 = 2670041) B2670041
theorem B6007175 : Blo 1778090 6007175 := bstep (se 1 (by rfl) ⟨4505381, by rfl⟩ : syracuseStep 6007175 = 9010763) B9010763
theorem B3377609 : Blo 1778090 3377609 := bstep (se 2 (by rfl) ⟨1266603, by rfl⟩ : syracuseStep 3377609 = 2533207) B2533207
theorem B2533879 : Blo 1778090 2533879 := bstep (se 1 (by rfl) ⟨1900409, by rfl⟩ : syracuseStep 2533879 = 3800819) B3800819
theorem B2001415 : Blo 1778090 2001415 := bstep (se 1 (by rfl) ⟨1501061, by rfl⟩ : syracuseStep 2001415 = 3002123) B3002123
theorem B9005579 : Blo 1778090 9005579 := bstep (se 1 (by rfl) ⟨6754184, by rfl⟩ : syracuseStep 9005579 = 13508369) B13508369
theorem B3000847 : Blo 1778090 3000847 := bstep (se 1 (by rfl) ⟨2250635, by rfl⟩ : syracuseStep 3000847 = 4501271) B4501271
theorem B16452125 : Blo 1778090 16452125 := bstep (se 3 (by rfl) ⟨3084773, by rfl⟩ : syracuseStep 16452125 = 6169547) B6169547
theorem B9005741 : Blo 1778090 9005741 := bstep (se 3 (by rfl) ⟨1688576, by rfl⟩ : syracuseStep 9005741 = 3377153) B3377153
theorem B2001595 : Blo 1778090 2001595 := bstep (se 1 (by rfl) ⟨1501196, by rfl⟩ : syracuseStep 2001595 = 3002393) B3002393
theorem B17107685 : Blo 1778090 17107685 := bstep (se 4 (by rfl) ⟨1603845, by rfl⟩ : syracuseStep 17107685 = 3207691) B3207691
theorem B6007553 : Blo 1778090 6007553 := bstep (se 2 (by rfl) ⟨2252832, by rfl⟩ : syracuseStep 6007553 = 4505665) B4505665
theorem B3205903 : Blo 1778090 3205903 := bstep (se 1 (by rfl) ⟨2404427, by rfl⟩ : syracuseStep 3205903 = 4808855) B4808855
theorem B10128179 : Blo 1778090 10128179 := bstep (se 1 (by rfl) ⟨7596134, by rfl⟩ : syracuseStep 10128179 = 15192269) B15192269
theorem B14625689 : Blo 1778090 14625689 := bstep (se 2 (by rfl) ⟨5484633, by rfl⟩ : syracuseStep 14625689 = 10969267) B10969267
theorem B3001387 : Blo 1778090 3001387 := bstep (se 1 (by rfl) ⟨2251040, by rfl⟩ : syracuseStep 3001387 = 4502081) B4502081
theorem B18500653 : Blo 1778090 18500653 := bstep (se 3 (by rfl) ⟨3468872, by rfl⟩ : syracuseStep 18500653 = 6937745) B6937745
theorem B2002063 : Blo 1778090 2002063 := bstep (se 1 (by rfl) ⟨1501547, by rfl⟩ : syracuseStep 2002063 = 3003095) B3003095
theorem B3378323 : Blo 1778090 3378323 := bstep (se 1 (by rfl) ⟨2533742, by rfl⟩ : syracuseStep 3378323 = 5067485) B5067485
theorem B3001529 : Blo 1778090 3001529 := bstep (se 2 (by rfl) ⟨1125573, by rfl⟩ : syracuseStep 3001529 = 2251147) B2251147
theorem B3378361 : Blo 1778090 3378361 := bstep (se 2 (by rfl) ⟨1266885, by rfl⟩ : syracuseStep 3378361 = 2533771) B2533771
theorem B4001039 : Blo 1778090 4001039 := bstep (se 1 (by rfl) ⟨3000779, by rfl⟩ : syracuseStep 4001039 = 6001559) B6001559
theorem B4001057 : Blo 1778090 4001057 := bstep (se 2 (by rfl) ⟨1500396, by rfl⟩ : syracuseStep 4001057 = 3000793) B3000793
theorem B5066027 : Blo 1778090 5066027 := bstep (se 1 (by rfl) ⟨3799520, by rfl⟩ : syracuseStep 5066027 = 7599041) B7599041
theorem B3206459 : Blo 1778090 3206459 := bstep (se 1 (by rfl) ⟨2404844, by rfl⟩ : syracuseStep 3206459 = 4809689) B4809689
theorem B4058639 : Blo 1778090 4058639 := bstep (se 1 (by rfl) ⟨3043979, by rfl⟩ : syracuseStep 4058639 = 6087959) B6087959
theorem B4501079 : Blo 1778090 4501079 := bstep (se 1 (by rfl) ⟨3375809, by rfl⟩ : syracuseStep 4501079 = 6751619) B6751619
theorem B4001399 : Blo 1778090 4001399 := bstep (se 1 (by rfl) ⟨3001049, by rfl⟩ : syracuseStep 4001399 = 6002099) B6002099
theorem B6409847 : Blo 1778090 6409847 := bstep (se 1 (by rfl) ⟨4807385, by rfl⟩ : syracuseStep 6409847 = 9614771) B9614771
theorem B5410423 : Blo 1778090 5410423 := bstep (se 1 (by rfl) ⟨4057817, by rfl⟩ : syracuseStep 5410423 = 8115635) B8115635
theorem B2002567 : Blo 1778090 2002567 := bstep (se 1 (by rfl) ⟨1501925, by rfl⟩ : syracuseStep 2002567 = 3003851) B3003851
theorem B6754049 : Blo 1778090 6754049 := bstep (se 2 (by rfl) ⟨2532768, by rfl⟩ : syracuseStep 6754049 = 5065537) B5065537
theorem B6754063 : Blo 1778090 6754063 := bstep (se 1 (by rfl) ⟨5065547, by rfl⟩ : syracuseStep 6754063 = 10131095) B10131095
theorem B3206927 : Blo 1778090 3206927 := bstep (se 1 (by rfl) ⟨2405195, by rfl⟩ : syracuseStep 3206927 = 4810391) B4810391
theorem B9621281 : Blo 1778090 9621281 := bstep (se 2 (by rfl) ⟨3607980, by rfl⟩ : syracuseStep 9621281 = 7215961) B7215961
theorem B14421797 : Blo 1778090 14421797 := bstep (se 4 (by rfl) ⟨1352043, by rfl⟩ : syracuseStep 14421797 = 2704087) B2704087
theorem B4501291 : Blo 1778090 4501291 := bstep (se 1 (by rfl) ⟨3375968, by rfl⟩ : syracuseStep 4501291 = 6751937) B6751937
theorem B4001579 : Blo 1778090 4001579 := bstep (se 1 (by rfl) ⟨3001184, by rfl⟩ : syracuseStep 4001579 = 6002369) B6002369
theorem B3002231 : Blo 1778090 3002231 := bstep (se 1 (by rfl) ⟨2251673, by rfl⟩ : syracuseStep 3002231 = 4503347) B4503347
theorem B4501433 : Blo 1778090 4501433 := bstep (se 2 (by rfl) ⟨1688037, by rfl⟩ : syracuseStep 4501433 = 3376075) B3376075
theorem B7598033 : Blo 1778090 7598033 := bstep (se 2 (by rfl) ⟨2849262, by rfl⟩ : syracuseStep 7598033 = 5698525) B5698525
theorem B13692989 : Blo 1778090 13692989 := bstep (se 3 (by rfl) ⟨2567435, by rfl⟩ : syracuseStep 13692989 = 5134871) B5134871
theorem B5066813 : Blo 1778090 5066813 := bstep (se 3 (by rfl) ⟨950027, by rfl⟩ : syracuseStep 5066813 = 1900055) B1900055
theorem B3207287 : Blo 1778090 3207287 := bstep (se 1 (by rfl) ⟨2405465, by rfl⟩ : syracuseStep 3207287 = 4810931) B4810931
theorem B4001939 : Blo 1778090 4001939 := bstep (se 1 (by rfl) ⟨3001454, by rfl⟩ : syracuseStep 4001939 = 6002909) B6002909
theorem B2314427 : Blo 1778090 2314427 := bstep (se 1 (by rfl) ⟨1735820, by rfl⟩ : syracuseStep 2314427 = 3471641) B3471641
theorem B4001993 : Blo 1778090 4001993 := bstep (se 2 (by rfl) ⟨1500747, by rfl⟩ : syracuseStep 4001993 = 3001495) B3001495
theorem B10129637 : Blo 1778090 10129637 := bstep (se 4 (by rfl) ⟨949653, by rfl⟩ : syracuseStep 10129637 = 1899307) B1899307
theorem B4272385 : Blo 1778090 4272385 := bstep (se 2 (by rfl) ⟨1602144, by rfl⟩ : syracuseStep 4272385 = 3204289) B3204289
theorem B9007361 : Blo 1778090 9007361 := bstep (se 2 (by rfl) ⟨3377760, by rfl⟩ : syracuseStep 9007361 = 6755521) B6755521
theorem B3002683 : Blo 1778090 3002683 := bstep (se 1 (by rfl) ⟨2252012, by rfl⟩ : syracuseStep 3002683 = 4504025) B4504025
theorem B5067143 : Blo 1778090 5067143 := bstep (se 1 (by rfl) ⟨3800357, by rfl⟩ : syracuseStep 5067143 = 7600715) B7600715
theorem B3002825 : Blo 1778090 3002825 := bstep (se 2 (by rfl) ⟨1126059, by rfl⟩ : syracuseStep 3002825 = 2252119) B2252119
theorem B19231181 : Blo 1778090 19231181 := bstep (se 3 (by rfl) ⟨3605846, by rfl⟩ : syracuseStep 19231181 = 7211693) B7211693
theorem B6001181 : Blo 1778090 6001181 := bstep (se 3 (by rfl) ⟨1125221, by rfl⟩ : syracuseStep 6001181 = 2250443) B2250443
theorem B2667143 : Blo 1778090 2667143 := bstep (se 1 (by rfl) ⟨2000357, by rfl⟩ : syracuseStep 2667143 = 4000715) B4000715
theorem B2667179 : Blo 1778090 2667179 := bstep (se 1 (by rfl) ⟨2000384, by rfl⟩ : syracuseStep 2667179 = 4000769) B4000769
theorem B10130093 : Blo 1778090 10130093 := bstep (se 3 (by rfl) ⟨1899392, by rfl⟩ : syracuseStep 10130093 = 3798785) B3798785
theorem B2667209 : Blo 1778090 2667209 := bstep (se 2 (by rfl) ⟨1000203, by rfl⟩ : syracuseStep 2667209 = 2000407) B2000407
theorem B7213769 : Blo 1778090 7213769 := bstep (se 2 (by rfl) ⟨2705163, by rfl⟩ : syracuseStep 7213769 = 5410327) B5410327
theorem B7213805 : Blo 1778090 7213805 := bstep (se 3 (by rfl) ⟨1352588, by rfl⟩ : syracuseStep 7213805 = 2705177) B2705177
theorem B11555585 : Blo 1778090 11555585 := bstep (se 2 (by rfl) ⟨4333344, by rfl⟩ : syracuseStep 11555585 = 8666689) B8666689
theorem B2667323 : Blo 1778090 2667323 := bstep (se 1 (by rfl) ⟨2000492, by rfl⟩ : syracuseStep 2667323 = 4000985) B4000985
theorem B2667383 : Blo 1778090 2667383 := bstep (se 1 (by rfl) ⟨2000537, by rfl⟩ : syracuseStep 2667383 = 4001075) B4001075
theorem B4002695 : Blo 1778090 4002695 := bstep (se 1 (by rfl) ⟨3002021, by rfl⟩ : syracuseStep 4002695 = 6004043) B6004043
theorem B2667407 : Blo 1778090 2667407 := bstep (se 1 (by rfl) ⟨2000555, by rfl⟩ : syracuseStep 2667407 = 4001111) B4001111
theorem B4273049 : Blo 1778090 4273049 := bstep (se 2 (by rfl) ⟨1602393, by rfl⟩ : syracuseStep 4273049 = 3204787) B3204787
theorem B4502425 : Blo 1778090 4502425 := bstep (se 2 (by rfl) ⟨1688409, by rfl⟩ : syracuseStep 4502425 = 3376819) B3376819
theorem B2667449 : Blo 1778090 2667449 := bstep (se 2 (by rfl) ⟨1000293, by rfl⟩ : syracuseStep 2667449 = 2000587) B2000587
theorem B2667527 : Blo 1778090 2667527 := bstep (se 1 (by rfl) ⟨2000645, by rfl⟩ : syracuseStep 2667527 = 4001291) B4001291
theorem B6755339 : Blo 1778090 6755339 := bstep (se 1 (by rfl) ⟨5066504, by rfl⟩ : syracuseStep 6755339 = 10133009) B10133009
theorem B2667563 : Blo 1778090 2667563 := bstep (se 1 (by rfl) ⟨2000672, by rfl⟩ : syracuseStep 2667563 = 4001345) B4001345
theorem B9008171 : Blo 1778090 9008171 := bstep (se 1 (by rfl) ⟨6756128, by rfl⟩ : syracuseStep 9008171 = 13512257) B13512257
theorem B4273211 : Blo 1778090 4273211 := bstep (se 1 (by rfl) ⟨3204908, by rfl⟩ : syracuseStep 4273211 = 6409817) B6409817
theorem B4502587 : Blo 1778090 4502587 := bstep (se 1 (by rfl) ⟨3376940, by rfl⟩ : syracuseStep 4502587 = 6753881) B6753881
theorem B4002875 : Blo 1778090 4002875 := bstep (se 1 (by rfl) ⟨3002156, by rfl⟩ : syracuseStep 4002875 = 6004313) B6004313
theorem B9622595 : Blo 1778090 9622595 := bstep (se 1 (by rfl) ⟨7216946, by rfl⟩ : syracuseStep 9622595 = 14433893) B14433893
theorem B2667593 : Blo 1778090 2667593 := bstep (se 2 (by rfl) ⟨1000347, by rfl⟩ : syracuseStep 2667593 = 2000695) B2000695
theorem B16233605 : Blo 1778090 16233605 := bstep (se 4 (by rfl) ⟨1521900, by rfl⟩ : syracuseStep 16233605 = 3043801) B3043801
theorem B3003527 : Blo 1778090 3003527 := bstep (se 1 (by rfl) ⟨2252645, by rfl⟩ : syracuseStep 3003527 = 4505291) B4505291
theorem B4003001 : Blo 1778090 4003001 := bstep (se 2 (by rfl) ⟨1501125, by rfl⟩ : syracuseStep 4003001 = 3002251) B3002251
theorem B2667707 : Blo 1778090 2667707 := bstep (se 1 (by rfl) ⟨2000780, by rfl⟩ : syracuseStep 2667707 = 4001561) B4001561
theorem B4502729 : Blo 1778090 4502729 := bstep (se 2 (by rfl) ⟨1688523, by rfl⟩ : syracuseStep 4502729 = 3377047) B3377047
theorem B2667767 : Blo 1778090 2667767 := bstep (se 1 (by rfl) ⟨2000825, by rfl⟩ : syracuseStep 2667767 = 4001651) B4001651
theorem B2405639 : Blo 1778090 2405639 := bstep (se 1 (by rfl) ⟨1804229, by rfl⟩ : syracuseStep 2405639 = 3608459) B3608459
theorem B2667791 : Blo 1778090 2667791 := bstep (se 1 (by rfl) ⟨2000843, by rfl⟩ : syracuseStep 2667791 = 4001687) B4001687
theorem B2667833 : Blo 1778090 2667833 := bstep (se 2 (by rfl) ⟨1000437, by rfl⟩ : syracuseStep 2667833 = 2000875) B2000875
theorem B10130777 : Blo 1778090 10130777 := bstep (se 2 (by rfl) ⟨3799041, by rfl⟩ : syracuseStep 10130777 = 7598083) B7598083
theorem B2667911 : Blo 1778090 2667911 := bstep (se 1 (by rfl) ⟨2000933, by rfl⟩ : syracuseStep 2667911 = 4001867) B4001867
theorem B2282887 : Blo 1778090 2282887 := bstep (se 1 (by rfl) ⟨1712165, by rfl⟩ : syracuseStep 2282887 = 3424331) B3424331
theorem B13505939 : Blo 1778090 13505939 := bstep (se 1 (by rfl) ⟨10129454, by rfl⟩ : syracuseStep 13505939 = 20258909) B20258909
theorem B2667947 : Blo 1778090 2667947 := bstep (se 1 (by rfl) ⟨2000960, by rfl⟩ : syracuseStep 2667947 = 4001921) B4001921
theorem B2667977 : Blo 1778090 2667977 := bstep (se 2 (by rfl) ⟨1000491, by rfl⟩ : syracuseStep 2667977 = 2000983) B2000983
theorem B4003343 : Blo 1778090 4003343 := bstep (se 1 (by rfl) ⟨3002507, by rfl⟩ : syracuseStep 4003343 = 6005015) B6005015
theorem B4503073 : Blo 1778090 4503073 := bstep (se 2 (by rfl) ⟨1688652, by rfl⟩ : syracuseStep 4503073 = 3377305) B3377305
theorem B4003361 : Blo 1778090 4003361 := bstep (se 2 (by rfl) ⟨1501260, by rfl⟩ : syracuseStep 4003361 = 3002521) B3002521
theorem B2668091 : Blo 1778090 2668091 := bstep (se 1 (by rfl) ⟨2001068, by rfl⟩ : syracuseStep 2668091 = 4002137) B4002137
theorem B5412467 : Blo 1778090 5412467 := bstep (se 1 (by rfl) ⟨4059350, by rfl⟩ : syracuseStep 5412467 = 8118701) B8118701
theorem B2668151 : Blo 1778090 2668151 := bstep (se 1 (by rfl) ⟨2001113, by rfl⟩ : syracuseStep 2668151 = 4002227) B4002227
theorem B2668175 : Blo 1778090 2668175 := bstep (se 1 (by rfl) ⟨2001131, by rfl⟩ : syracuseStep 2668175 = 4002263) B4002263
theorem B2283179 : Blo 1778090 2283179 := bstep (se 1 (by rfl) ⟨1712384, by rfl⟩ : syracuseStep 2283179 = 3424769) B3424769
theorem B2668217 : Blo 1778090 2668217 := bstep (se 2 (by rfl) ⟨1000581, by rfl⟩ : syracuseStep 2668217 = 2001163) B2001163
theorem B2668295 : Blo 1778090 2668295 := bstep (se 1 (by rfl) ⟨2001221, by rfl⟩ : syracuseStep 2668295 = 4002443) B4002443
theorem B20264741 : Blo 1778090 20264741 := bstep (se 4 (by rfl) ⟨1899819, by rfl⟩ : syracuseStep 20264741 = 3799639) B3799639
theorem B11712293 : Blo 1778090 11712293 := bstep (se 4 (by rfl) ⟨1098027, by rfl⟩ : syracuseStep 11712293 = 2196055) B2196055
theorem B2668331 : Blo 1778090 2668331 := bstep (se 1 (by rfl) ⟨2001248, by rfl⟩ : syracuseStep 2668331 = 4002497) B4002497
theorem B4273979 : Blo 1778090 4273979 := bstep (se 1 (by rfl) ⟨3205484, by rfl⟩ : syracuseStep 4273979 = 6410969) B6410969
theorem B2668361 : Blo 1778090 2668361 := bstep (se 2 (by rfl) ⟨1000635, by rfl⟩ : syracuseStep 2668361 = 2001271) B2001271
theorem B4003703 : Blo 1778090 4003703 := bstep (se 1 (by rfl) ⟨3002777, by rfl⟩ : syracuseStep 4003703 = 6005555) B6005555
theorem B22787993 : Blo 1778090 22787993 := bstep (se 2 (by rfl) ⟨8545497, by rfl⟩ : syracuseStep 22787993 = 17090995) B17090995
theorem B6002585 : Blo 1778090 6002585 := bstep (se 2 (by rfl) ⟨2250969, by rfl⟩ : syracuseStep 6002585 = 4501939) B4501939
theorem B6756281 : Blo 1778090 6756281 := bstep (se 2 (by rfl) ⟨2533605, by rfl⟩ : syracuseStep 6756281 = 5067211) B5067211
theorem B2668475 : Blo 1778090 2668475 := bstep (se 1 (by rfl) ⟨2001356, by rfl⟩ : syracuseStep 2668475 = 4002713) B4002713
theorem B2668535 : Blo 1778090 2668535 := bstep (se 1 (by rfl) ⟨2001401, by rfl⟩ : syracuseStep 2668535 = 4002803) B4002803
theorem B2250767 : Blo 1778090 2250767 := bstep (se 1 (by rfl) ⟨1688075, by rfl⟩ : syracuseStep 2250767 = 3376151) B3376151
theorem B2668559 : Blo 1778090 2668559 := bstep (se 1 (by rfl) ⟨2001419, by rfl⟩ : syracuseStep 2668559 = 4002839) B4002839
theorem B4003883 : Blo 1778090 4003883 := bstep (se 1 (by rfl) ⟨3002912, by rfl⟩ : syracuseStep 4003883 = 6005825) B6005825
theorem B2668601 : Blo 1778090 2668601 := bstep (se 2 (by rfl) ⟨1000725, by rfl⟩ : syracuseStep 2668601 = 2001451) B2001451
theorem B4503671 : Blo 1778090 4503671 := bstep (se 1 (by rfl) ⟨3377753, by rfl⟩ : syracuseStep 4503671 = 6755507) B6755507
theorem B5068919 : Blo 1778090 5068919 := bstep (se 1 (by rfl) ⟨3801689, by rfl⟩ : syracuseStep 5068919 = 7603379) B7603379
theorem B2668679 : Blo 1778090 2668679 := bstep (se 1 (by rfl) ⟨2001509, by rfl⟩ : syracuseStep 2668679 = 4003019) B4003019
theorem B2668715 : Blo 1778090 2668715 := bstep (se 1 (by rfl) ⟨2001536, by rfl⟩ : syracuseStep 2668715 = 4003073) B4003073
theorem B2668745 : Blo 1778090 2668745 := bstep (se 2 (by rfl) ⟨1000779, by rfl⟩ : syracuseStep 2668745 = 2001559) B2001559
theorem B2668859 : Blo 1778090 2668859 := bstep (se 1 (by rfl) ⟨2001644, by rfl⟩ : syracuseStep 2668859 = 4003289) B4003289
theorem B9009467 : Blo 1778090 9009467 := bstep (se 1 (by rfl) ⟨6757100, by rfl⟩ : syracuseStep 9009467 = 13514201) B13514201
theorem B2668919 : Blo 1778090 2668919 := bstep (se 1 (by rfl) ⟨2001689, by rfl⟩ : syracuseStep 2668919 = 4003379) B4003379
theorem B2668943 : Blo 1778090 2668943 := bstep (se 1 (by rfl) ⟨2001707, by rfl⟩ : syracuseStep 2668943 = 4003415) B4003415
theorem B9615761 : Blo 1778090 9615761 := bstep (se 2 (by rfl) ⟨3605910, by rfl⟩ : syracuseStep 9615761 = 7211821) B7211821
theorem B4004243 : Blo 1778090 4004243 := bstep (se 1 (by rfl) ⟨3003182, by rfl⟩ : syracuseStep 4004243 = 6006365) B6006365
theorem B6412729 : Blo 1778090 6412729 := bstep (se 2 (by rfl) ⟨2404773, by rfl⟩ : syracuseStep 6412729 = 4809547) B4809547
theorem B2668985 : Blo 1778090 2668985 := bstep (se 2 (by rfl) ⟨1000869, by rfl⟩ : syracuseStep 2668985 = 2001739) B2001739
theorem B4004297 : Blo 1778090 4004297 := bstep (se 2 (by rfl) ⟨1501611, by rfl⟩ : syracuseStep 4004297 = 3003223) B3003223
theorem B9009629 : Blo 1778090 9009629 := bstep (se 3 (by rfl) ⟨1689305, by rfl⟩ : syracuseStep 9009629 = 3378611) B3378611
theorem B2669063 : Blo 1778090 2669063 := bstep (se 1 (by rfl) ⟨2001797, by rfl⟩ : syracuseStep 2669063 = 4003595) B4003595
theorem B2669099 : Blo 1778090 2669099 := bstep (se 1 (by rfl) ⟨2001824, by rfl⟩ : syracuseStep 2669099 = 4003649) B4003649
theorem B2669129 : Blo 1778090 2669129 := bstep (se 2 (by rfl) ⟨1000923, by rfl⟩ : syracuseStep 2669129 = 2001847) B2001847
theorem B6003287 : Blo 1778090 6003287 := bstep (se 1 (by rfl) ⟨4502465, by rfl⟩ : syracuseStep 6003287 = 9004931) B9004931
theorem B2669243 : Blo 1778090 2669243 := bstep (se 1 (by rfl) ⟨2001932, by rfl⟩ : syracuseStep 2669243 = 4003865) B4003865
theorem B2669303 : Blo 1778090 2669303 := bstep (se 1 (by rfl) ⟨2001977, by rfl⟩ : syracuseStep 2669303 = 4003955) B4003955
theorem B2669327 : Blo 1778090 2669327 := bstep (se 1 (by rfl) ⟨2001995, by rfl⟩ : syracuseStep 2669327 = 4003991) B4003991
theorem B9009953 : Blo 1778090 9009953 := bstep (se 2 (by rfl) ⟨3378732, by rfl⟩ : syracuseStep 9009953 = 6757465) B6757465
theorem B2669369 : Blo 1778090 2669369 := bstep (se 2 (by rfl) ⟨1001013, by rfl⟩ : syracuseStep 2669369 = 2002027) B2002027
theorem B18291545 : Blo 1778090 18291545 := bstep (se 2 (by rfl) ⟨6859329, by rfl⟩ : syracuseStep 18291545 = 13718659) B13718659
theorem B2669447 : Blo 1778090 2669447 := bstep (se 1 (by rfl) ⟨2002085, by rfl⟩ : syracuseStep 2669447 = 4004171) B4004171
theorem B2669483 : Blo 1778090 2669483 := bstep (se 1 (by rfl) ⟨2002112, by rfl⟩ : syracuseStep 2669483 = 4004225) B4004225
theorem B2669513 : Blo 1778090 2669513 := bstep (se 2 (by rfl) ⟨1001067, by rfl⟩ : syracuseStep 2669513 = 2002135) B2002135
theorem B8223697 : Blo 1778090 8223697 := bstep (se 2 (by rfl) ⟨3083886, by rfl⟩ : syracuseStep 8223697 = 6167773) B6167773
theorem B2669627 : Blo 1778090 2669627 := bstep (se 1 (by rfl) ⟨2002220, by rfl⟩ : syracuseStep 2669627 = 4004441) B4004441
theorem B6003773 : Blo 1778090 6003773 := bstep (se 3 (by rfl) ⟨1125707, by rfl⟩ : syracuseStep 6003773 = 2251415) B2251415
theorem B2669687 : Blo 1778090 2669687 := bstep (se 1 (by rfl) ⟨2002265, by rfl⟩ : syracuseStep 2669687 = 4004531) B4004531
theorem B4004999 : Blo 1778090 4004999 := bstep (se 1 (by rfl) ⟨3003749, by rfl⟩ : syracuseStep 4004999 = 6007499) B6007499
theorem B2669711 : Blo 1778090 2669711 := bstep (se 1 (by rfl) ⟨2002283, by rfl⟩ : syracuseStep 2669711 = 4004567) B4004567
theorem B2669753 : Blo 1778090 2669753 := bstep (se 2 (by rfl) ⟨1001157, by rfl⟩ : syracuseStep 2669753 = 2002315) B2002315
theorem B9002177 : Blo 1778090 9002177 := bstep (se 2 (by rfl) ⟨3375816, by rfl⟩ : syracuseStep 9002177 = 6751633) B6751633
theorem B2669831 : Blo 1778090 2669831 := bstep (se 1 (by rfl) ⟨2002373, by rfl⟩ : syracuseStep 2669831 = 4004747) B4004747
theorem B2669867 : Blo 1778090 2669867 := bstep (se 1 (by rfl) ⟨2002400, by rfl⟩ : syracuseStep 2669867 = 4004801) B4004801
theorem B4005179 : Blo 1778090 4005179 := bstep (se 1 (by rfl) ⟨3003884, by rfl⟩ : syracuseStep 4005179 = 6007769) B6007769
theorem B2669897 : Blo 1778090 2669897 := bstep (se 2 (by rfl) ⟨1001211, by rfl⟩ : syracuseStep 2669897 = 2002423) B2002423
theorem B4504967 : Blo 1778090 4504967 := bstep (se 1 (by rfl) ⟨3378725, by rfl⟩ : syracuseStep 4504967 = 6757451) B6757451
theorem B5701049 : Blo 1778090 5701049 := bstep (se 2 (by rfl) ⟨2137893, by rfl⟩ : syracuseStep 5701049 = 4275787) B4275787
theorem B4505017 : Blo 1778090 4505017 := bstep (se 2 (by rfl) ⟨1689381, by rfl⟩ : syracuseStep 4505017 = 3378763) B3378763
theorem B2670011 : Blo 1778090 2670011 := bstep (se 1 (by rfl) ⟨2002508, by rfl⟩ : syracuseStep 2670011 = 4005017) B4005017
theorem B2670071 : Blo 1778090 2670071 := bstep (se 1 (by rfl) ⟨2002553, by rfl⟩ : syracuseStep 2670071 = 4005107) B4005107
theorem B2850319 : Blo 1778090 2850319 := bstep (se 1 (by rfl) ⟨2137739, by rfl⟩ : syracuseStep 2850319 = 4275479) B4275479
theorem B2670095 : Blo 1778090 2670095 := bstep (se 1 (by rfl) ⟨2002571, by rfl⟩ : syracuseStep 2670095 = 4005143) B4005143
theorem B9010925 : Blo 1778090 9010925 := bstep (se 3 (by rfl) ⟨1689548, by rfl⟩ : syracuseStep 9010925 = 3379097) B3379097
theorem B5136139 : Blo 1778090 5136139 := bstep (se 1 (by rfl) ⟨3852104, by rfl⟩ : syracuseStep 5136139 = 7704209) B7704209
theorem B19234597 : Blo 1778090 19234597 := bstep (se 4 (by rfl) ⟨1803243, by rfl⟩ : syracuseStep 19234597 = 3606487) B3606487
theorem B6004907 : Blo 1778090 6004907 := bstep (se 1 (by rfl) ⟨4503680, by rfl⟩ : syracuseStep 6004907 = 9007361) B9007361
theorem B12820787 : Blo 1778090 12820787 := bstep (se 1 (by rfl) ⟨9615590, by rfl⟩ : syracuseStep 12820787 = 19231181) B19231181
theorem B8552765 : Blo 1778090 8552765 := bstep (se 3 (by rfl) ⟨1603643, by rfl⟩ : syracuseStep 8552765 = 3207287) B3207287
theorem B13517117 : Blo 1778090 13517117 := bstep (se 3 (by rfl) ⟨2534459, by rfl⟩ : syracuseStep 13517117 = 5068919) B5068919
theorem B3604841 : Blo 1778090 3604841 := bstep (se 2 (by rfl) ⟨1351815, by rfl⟩ : syracuseStep 3604841 = 2703631) B2703631
theorem B1778095 : Blo 1778090 1778095 := bstep (se 1 (by rfl) ⟨1333571, by rfl⟩ : syracuseStep 1778095 = 2667143) B2667143
theorem B1778119 : Blo 1778090 1778119 := bstep (se 1 (by rfl) ⟨1333589, by rfl⟩ : syracuseStep 1778119 = 2667179) B2667179
theorem B1778139 : Blo 1778090 1778139 := bstep (se 1 (by rfl) ⟨1333604, by rfl⟩ : syracuseStep 1778139 = 2667209) B2667209
theorem B4809179 : Blo 1778090 4809179 := bstep (se 1 (by rfl) ⟨3606884, by rfl⟩ : syracuseStep 4809179 = 7213769) B7213769
theorem B4809203 : Blo 1778090 4809203 := bstep (se 1 (by rfl) ⟨3606902, by rfl⟩ : syracuseStep 4809203 = 7213805) B7213805
theorem B17105417 : Blo 1778090 17105417 := bstep (se 2 (by rfl) ⟨6414531, by rfl⟩ : syracuseStep 17105417 = 12829063) B12829063
theorem B27378199 : Blo 1778090 27378199 := bstep (se 1 (by rfl) ⟨20533649, by rfl⟩ : syracuseStep 27378199 = 41067299) B41067299
theorem B5702177 : Blo 1778090 5702177 := bstep (se 2 (by rfl) ⟨2138316, by rfl⟩ : syracuseStep 5702177 = 4276633) B4276633
theorem B1778215 : Blo 1778090 1778215 := bstep (se 1 (by rfl) ⟨1333661, by rfl⟩ : syracuseStep 1778215 = 2667323) B2667323
theorem B3375695 : Blo 1778090 3375695 := bstep (se 1 (by rfl) ⟨2531771, by rfl⟩ : syracuseStep 3375695 = 5063543) B5063543
theorem B1778255 : Blo 1778090 1778255 := bstep (se 1 (by rfl) ⟨1333691, by rfl⟩ : syracuseStep 1778255 = 2667383) B2667383
theorem B1778271 : Blo 1778090 1778271 := bstep (se 1 (by rfl) ⟨1333703, by rfl⟩ : syracuseStep 1778271 = 2667407) B2667407
theorem B1778299 : Blo 1778090 1778299 := bstep (se 1 (by rfl) ⟨1333724, by rfl⟩ : syracuseStep 1778299 = 2667449) B2667449
theorem B12829319 : Blo 1778090 12829319 := bstep (se 1 (by rfl) ⟨9621989, by rfl⟩ : syracuseStep 12829319 = 19243979) B19243979
theorem B1778351 : Blo 1778090 1778351 := bstep (se 1 (by rfl) ⟨1333763, by rfl⟩ : syracuseStep 1778351 = 2667527) B2667527
theorem B5702329 : Blo 1778090 5702329 := bstep (se 2 (by rfl) ⟨2138373, by rfl⟩ : syracuseStep 5702329 = 4276747) B4276747
theorem B6415037 : Blo 1778090 6415037 := bstep (se 3 (by rfl) ⟨1202819, by rfl⟩ : syracuseStep 6415037 = 2405639) B2405639
theorem B1778375 : Blo 1778090 1778375 := bstep (se 1 (by rfl) ⟨1333781, by rfl⟩ : syracuseStep 1778375 = 2667563) B2667563
theorem B6005447 : Blo 1778090 6005447 := bstep (se 1 (by rfl) ⟨4504085, by rfl⟩ : syracuseStep 6005447 = 9008171) B9008171
theorem B1778395 : Blo 1778090 1778395 := bstep (se 1 (by rfl) ⟨1333796, by rfl⟩ : syracuseStep 1778395 = 2667593) B2667593
theorem B10822403 : Blo 1778090 10822403 := bstep (se 1 (by rfl) ⟨8116802, by rfl⟩ : syracuseStep 10822403 = 16233605) B16233605
theorem B27378445 : Blo 1778090 27378445 := bstep (se 3 (by rfl) ⟨5133458, by rfl⟩ : syracuseStep 27378445 = 10266917) B10266917
theorem B1778471 : Blo 1778090 1778471 := bstep (se 1 (by rfl) ⟨1333853, by rfl⟩ : syracuseStep 1778471 = 2667707) B2667707
theorem B1778511 : Blo 1778090 1778511 := bstep (se 1 (by rfl) ⟨1333883, by rfl⟩ : syracuseStep 1778511 = 2667767) B2667767
theorem B1778527 : Blo 1778090 1778527 := bstep (se 1 (by rfl) ⟨1333895, by rfl⟩ : syracuseStep 1778527 = 2667791) B2667791
theorem B10961771 : Blo 1778090 10961771 := bstep (se 1 (by rfl) ⟨8221328, by rfl⟩ : syracuseStep 10961771 = 16442657) B16442657
theorem B1778555 : Blo 1778090 1778555 := bstep (se 1 (by rfl) ⟨1333916, by rfl⟩ : syracuseStep 1778555 = 2667833) B2667833
theorem B1778607 : Blo 1778090 1778607 := bstep (se 1 (by rfl) ⟨1333955, by rfl⟩ : syracuseStep 1778607 = 2667911) B2667911
theorem B9003959 : Blo 1778090 9003959 := bstep (se 1 (by rfl) ⟨6752969, by rfl⟩ : syracuseStep 9003959 = 13505939) B13505939
theorem B1778631 : Blo 1778090 1778631 := bstep (se 1 (by rfl) ⟨1333973, by rfl⟩ : syracuseStep 1778631 = 2667947) B2667947
theorem B1778651 : Blo 1778090 1778651 := bstep (se 1 (by rfl) ⟨1333988, by rfl⟩ : syracuseStep 1778651 = 2667977) B2667977
theorem B5702663 : Blo 1778090 5702663 := bstep (se 1 (by rfl) ⟨4276997, by rfl⟩ : syracuseStep 5702663 = 8553995) B8553995
theorem B1778727 : Blo 1778090 1778727 := bstep (se 1 (by rfl) ⟨1334045, by rfl⟩ : syracuseStep 1778727 = 2668091) B2668091
theorem B19760195 : Blo 1778090 19760195 := bstep (se 1 (by rfl) ⟨14820146, by rfl⟩ : syracuseStep 19760195 = 29640293) B29640293
theorem B1778767 : Blo 1778090 1778767 := bstep (se 1 (by rfl) ⟨1334075, by rfl⟩ : syracuseStep 1778767 = 2668151) B2668151
theorem B1778783 : Blo 1778090 1778783 := bstep (se 1 (by rfl) ⟨1334087, by rfl⟩ : syracuseStep 1778783 = 2668175) B2668175
theorem B1778811 : Blo 1778090 1778811 := bstep (se 1 (by rfl) ⟨1334108, by rfl⟩ : syracuseStep 1778811 = 2668217) B2668217
theorem B10814617 : Blo 1778090 10814617 := bstep (se 2 (by rfl) ⟨4055481, by rfl⟩ : syracuseStep 10814617 = 8110963) B8110963
theorem B1778863 : Blo 1778090 1778863 := bstep (se 1 (by rfl) ⟨1334147, by rfl⟩ : syracuseStep 1778863 = 2668295) B2668295
theorem B13509827 : Blo 1778090 13509827 := bstep (se 1 (by rfl) ⟨10132370, by rfl⟩ : syracuseStep 13509827 = 20264741) B20264741
theorem B7808195 : Blo 1778090 7808195 := bstep (se 1 (by rfl) ⟨5856146, by rfl⟩ : syracuseStep 7808195 = 11712293) B11712293
theorem B1778887 : Blo 1778090 1778887 := bstep (se 1 (by rfl) ⟨1334165, by rfl⟩ : syracuseStep 1778887 = 2668331) B2668331
theorem B1778907 : Blo 1778090 1778907 := bstep (se 1 (by rfl) ⟨1334180, by rfl⟩ : syracuseStep 1778907 = 2668361) B2668361
theorem B1778983 : Blo 1778090 1778983 := bstep (se 1 (by rfl) ⟨1334237, by rfl⟩ : syracuseStep 1778983 = 2668475) B2668475
theorem B1779023 : Blo 1778090 1779023 := bstep (se 1 (by rfl) ⟨1334267, by rfl⟩ : syracuseStep 1779023 = 2668535) B2668535
theorem B1779039 : Blo 1778090 1779039 := bstep (se 1 (by rfl) ⟨1334279, by rfl⟩ : syracuseStep 1779039 = 2668559) B2668559
theorem B1779067 : Blo 1778090 1779067 := bstep (se 1 (by rfl) ⟨1334300, by rfl⟩ : syracuseStep 1779067 = 2668601) B2668601
theorem B5064079 : Blo 1778090 5064079 := bstep (se 1 (by rfl) ⟨3798059, by rfl⟩ : syracuseStep 5064079 = 7596119) B7596119
theorem B1779119 : Blo 1778090 1779119 := bstep (se 1 (by rfl) ⟨1334339, by rfl⟩ : syracuseStep 1779119 = 2668679) B2668679
theorem B2704823 : Blo 1778090 2704823 := bstep (se 1 (by rfl) ⟨2028617, by rfl⟩ : syracuseStep 2704823 = 4057235) B4057235
theorem B1779143 : Blo 1778090 1779143 := bstep (se 1 (by rfl) ⟨1334357, by rfl⟩ : syracuseStep 1779143 = 2668715) B2668715
theorem B1779163 : Blo 1778090 1779163 := bstep (se 1 (by rfl) ⟨1334372, by rfl⟩ : syracuseStep 1779163 = 2668745) B2668745
theorem B1779239 : Blo 1778090 1779239 := bstep (se 1 (by rfl) ⟨1334429, by rfl⟩ : syracuseStep 1779239 = 2668859) B2668859
theorem B6006311 : Blo 1778090 6006311 := bstep (se 1 (by rfl) ⟨4504733, by rfl⟩ : syracuseStep 6006311 = 9009467) B9009467
theorem B1779279 : Blo 1778090 1779279 := bstep (se 1 (by rfl) ⟨1334459, by rfl⟩ : syracuseStep 1779279 = 2668919) B2668919
theorem B1779295 : Blo 1778090 1779295 := bstep (se 1 (by rfl) ⟨1334471, by rfl⟩ : syracuseStep 1779295 = 2668943) B2668943
theorem B1779323 : Blo 1778090 1779323 := bstep (se 1 (by rfl) ⟨1334492, by rfl⟩ : syracuseStep 1779323 = 2668985) B2668985
theorem B6006419 : Blo 1778090 6006419 := bstep (se 1 (by rfl) ⟨4504814, by rfl⟩ : syracuseStep 6006419 = 9009629) B9009629
theorem B1779375 : Blo 1778090 1779375 := bstep (se 1 (by rfl) ⟨1334531, by rfl⟩ : syracuseStep 1779375 = 2669063) B2669063
theorem B1779399 : Blo 1778090 1779399 := bstep (se 1 (by rfl) ⟨1334549, by rfl⟩ : syracuseStep 1779399 = 2669099) B2669099
theorem B1779419 : Blo 1778090 1779419 := bstep (se 1 (by rfl) ⟨1334564, by rfl⟩ : syracuseStep 1779419 = 2669129) B2669129
theorem B6088477 : Blo 1778090 6088477 := bstep (se 3 (by rfl) ⟨1141589, by rfl⟩ : syracuseStep 6088477 = 2283179) B2283179
theorem B1779495 : Blo 1778090 1779495 := bstep (se 1 (by rfl) ⟨1334621, by rfl⟩ : syracuseStep 1779495 = 2669243) B2669243
theorem B11405123 : Blo 1778090 11405123 := bstep (se 1 (by rfl) ⟨8553842, by rfl⟩ : syracuseStep 11405123 = 17107685) B17107685
theorem B1779535 : Blo 1778090 1779535 := bstep (se 1 (by rfl) ⟨1334651, by rfl⟩ : syracuseStep 1779535 = 2669303) B2669303
theorem B1779551 : Blo 1778090 1779551 := bstep (se 1 (by rfl) ⟨1334663, by rfl⟩ : syracuseStep 1779551 = 2669327) B2669327
theorem B6006635 : Blo 1778090 6006635 := bstep (se 1 (by rfl) ⟨4504976, by rfl⟩ : syracuseStep 6006635 = 9009953) B9009953
theorem B6752119 : Blo 1778090 6752119 := bstep (se 1 (by rfl) ⟨5064089, by rfl⟩ : syracuseStep 6752119 = 10128179) B10128179
theorem B1779579 : Blo 1778090 1779579 := bstep (se 1 (by rfl) ⟨1334684, by rfl⟩ : syracuseStep 1779579 = 2669369) B2669369
theorem B6006689 : Blo 1778090 6006689 := bstep (se 2 (by rfl) ⟨2252508, by rfl⟩ : syracuseStep 6006689 = 4505017) B4505017
theorem B1779631 : Blo 1778090 1779631 := bstep (se 1 (by rfl) ⟨1334723, by rfl⟩ : syracuseStep 1779631 = 2669447) B2669447
theorem B1779655 : Blo 1778090 1779655 := bstep (se 1 (by rfl) ⟨1334741, by rfl⟩ : syracuseStep 1779655 = 2669483) B2669483
theorem B1779675 : Blo 1778090 1779675 := bstep (se 1 (by rfl) ⟨1334756, by rfl⟩ : syracuseStep 1779675 = 2669513) B2669513
theorem B12175397 : Blo 1778090 12175397 := bstep (se 4 (by rfl) ⟨1141443, by rfl⟩ : syracuseStep 12175397 = 2282887) B2282887
theorem B1779751 : Blo 1778090 1779751 := bstep (se 1 (by rfl) ⟨1334813, by rfl⟩ : syracuseStep 1779751 = 2669627) B2669627
theorem B1779791 : Blo 1778090 1779791 := bstep (se 1 (by rfl) ⟨1334843, by rfl⟩ : syracuseStep 1779791 = 2669687) B2669687
theorem B1779807 : Blo 1778090 1779807 := bstep (se 1 (by rfl) ⟨1334855, by rfl⟩ : syracuseStep 1779807 = 2669711) B2669711
theorem B2001019 : Blo 1778090 2001019 := bstep (se 1 (by rfl) ⟨1500764, by rfl⟩ : syracuseStep 2001019 = 3001529) B3001529
theorem B1779835 : Blo 1778090 1779835 := bstep (se 1 (by rfl) ⟨1334876, by rfl⟩ : syracuseStep 1779835 = 2669753) B2669753
theorem B11397277 : Blo 1778090 11397277 := bstep (se 3 (by rfl) ⟨2136989, by rfl⟩ : syracuseStep 11397277 = 4273979) B4273979
theorem B1779887 : Blo 1778090 1779887 := bstep (se 1 (by rfl) ⟨1334915, by rfl⟩ : syracuseStep 1779887 = 2669831) B2669831
theorem B3377351 : Blo 1778090 3377351 := bstep (se 1 (by rfl) ⟨2533013, by rfl⟩ : syracuseStep 3377351 = 5066027) B5066027
theorem B1779911 : Blo 1778090 1779911 := bstep (se 1 (by rfl) ⟨1334933, by rfl⟩ : syracuseStep 1779911 = 2669867) B2669867
theorem B1779931 : Blo 1778090 1779931 := bstep (se 1 (by rfl) ⟨1334948, by rfl⟩ : syracuseStep 1779931 = 2669897) B2669897
theorem B1780007 : Blo 1778090 1780007 := bstep (se 1 (by rfl) ⟨1335005, by rfl⟩ : syracuseStep 1780007 = 2670011) B2670011
theorem B1780047 : Blo 1778090 1780047 := bstep (se 1 (by rfl) ⟨1335035, by rfl⟩ : syracuseStep 1780047 = 2670071) B2670071
theorem B2705759 : Blo 1778090 2705759 := bstep (se 1 (by rfl) ⟨2029319, by rfl⟩ : syracuseStep 2705759 = 4058639) B4058639
theorem B1780063 : Blo 1778090 1780063 := bstep (se 1 (by rfl) ⟨1335047, by rfl⟩ : syracuseStep 1780063 = 2670095) B2670095
theorem B9005417 : Blo 1778090 9005417 := bstep (se 2 (by rfl) ⟨3377031, by rfl⟩ : syracuseStep 9005417 = 6754063) B6754063
theorem B3000719 : Blo 1778090 3000719 := bstep (se 1 (by rfl) ⟨2250539, by rfl⟩ : syracuseStep 3000719 = 4501079) B4501079
theorem B6007283 : Blo 1778090 6007283 := bstep (se 1 (by rfl) ⟨4505462, by rfl⟩ : syracuseStep 6007283 = 9010925) B9010925
theorem B2001487 : Blo 1778090 2001487 := bstep (se 1 (by rfl) ⟨1501115, by rfl⟩ : syracuseStep 2001487 = 3002231) B3002231
theorem B3000955 : Blo 1778090 3000955 := bstep (se 1 (by rfl) ⟨2250716, by rfl⟩ : syracuseStep 3000955 = 4501433) B4501433
theorem B5065355 : Blo 1778090 5065355 := bstep (se 1 (by rfl) ⟨3799016, by rfl⟩ : syracuseStep 5065355 = 7598033) B7598033
theorem B3205831 : Blo 1778090 3205831 := bstep (se 1 (by rfl) ⟨2404373, by rfl⟩ : syracuseStep 3205831 = 4808747) B4808747
theorem B9128659 : Blo 1778090 9128659 := bstep (se 1 (by rfl) ⟨6846494, by rfl⟩ : syracuseStep 9128659 = 13692989) B13692989
theorem B3377875 : Blo 1778090 3377875 := bstep (se 1 (by rfl) ⟨2533406, by rfl⟩ : syracuseStep 3377875 = 5066813) B5066813
theorem B6753091 : Blo 1778090 6753091 := bstep (se 1 (by rfl) ⟨5064818, by rfl⟩ : syracuseStep 6753091 = 10129637) B10129637
theorem B25660253 : Blo 1778090 25660253 := bstep (se 3 (by rfl) ⟨4811297, by rfl⟩ : syracuseStep 25660253 = 9622595) B9622595
theorem B3378095 : Blo 1778090 3378095 := bstep (se 1 (by rfl) ⟨2533571, by rfl⟩ : syracuseStep 3378095 = 5067143) B5067143
theorem B2001883 : Blo 1778090 2001883 := bstep (se 1 (by rfl) ⟨1501412, by rfl⟩ : syracuseStep 2001883 = 3002825) B3002825
theorem B5696513 : Blo 1778090 5696513 := bstep (se 2 (by rfl) ⟨2136192, by rfl⟩ : syracuseStep 5696513 = 4272385) B4272385
theorem B4000787 : Blo 1778090 4000787 := bstep (se 1 (by rfl) ⟨3000590, by rfl⟩ : syracuseStep 4000787 = 6001181) B6001181
theorem B6753395 : Blo 1778090 6753395 := bstep (se 1 (by rfl) ⟨5065046, by rfl⟩ : syracuseStep 6753395 = 10130093) B10130093
theorem B13003895 : Blo 1778090 13003895 := bstep (se 1 (by rfl) ⟨9752921, by rfl⟩ : syracuseStep 13003895 = 19505843) B19505843
theorem B6171805 : Blo 1778090 6171805 := bstep (se 3 (by rfl) ⟨1157213, by rfl⟩ : syracuseStep 6171805 = 2314427) B2314427
theorem B7703723 : Blo 1778090 7703723 := bstep (se 1 (by rfl) ⟨5777792, by rfl⟩ : syracuseStep 7703723 = 11555585) B11555585
theorem B3378505 : Blo 1778090 3378505 := bstep (se 2 (by rfl) ⟨1266939, by rfl⟩ : syracuseStep 3378505 = 2533879) B2533879
theorem B4001129 : Blo 1778090 4001129 := bstep (se 2 (by rfl) ⟨1500423, by rfl⟩ : syracuseStep 4001129 = 3000847) B3000847
theorem B2002351 : Blo 1778090 2002351 := bstep (se 1 (by rfl) ⟨1501763, by rfl⟩ : syracuseStep 2002351 = 3003527) B3003527
theorem B3001819 : Blo 1778090 3001819 := bstep (se 1 (by rfl) ⟨2251364, by rfl⟩ : syracuseStep 3001819 = 4502729) B4502729
theorem B6753851 : Blo 1778090 6753851 := bstep (se 1 (by rfl) ⟨5065388, by rfl⟩ : syracuseStep 6753851 = 10130777) B10130777
theorem B3608311 : Blo 1778090 3608311 := bstep (se 1 (by rfl) ⟨2706233, by rfl⟩ : syracuseStep 3608311 = 5412467) B5412467
theorem B4501241 : Blo 1778090 4501241 := bstep (se 2 (by rfl) ⟨1687965, by rfl⟩ : syracuseStep 4501241 = 3375931) B3375931
theorem B15191995 : Blo 1778090 15191995 := bstep (se 1 (by rfl) ⟨11393996, by rfl⟩ : syracuseStep 15191995 = 22787993) B22787993
theorem B4001723 : Blo 1778090 4001723 := bstep (se 1 (by rfl) ⟨3001292, by rfl⟩ : syracuseStep 4001723 = 6002585) B6002585
theorem B4001849 : Blo 1778090 4001849 := bstep (se 2 (by rfl) ⟨1500693, by rfl⟩ : syracuseStep 4001849 = 3001387) B3001387
theorem B3002447 : Blo 1778090 3002447 := bstep (se 1 (by rfl) ⟨2251835, by rfl⟩ : syracuseStep 3002447 = 4503671) B4503671
theorem B6410507 : Blo 1778090 6410507 := bstep (se 1 (by rfl) ⟨4807880, by rfl⟩ : syracuseStep 6410507 = 9615761) B9615761
theorem B4501889 : Blo 1778090 4501889 := bstep (se 2 (by rfl) ⟨1688208, by rfl⟩ : syracuseStep 4501889 = 3376417) B3376417
theorem B4002191 : Blo 1778090 4002191 := bstep (se 1 (by rfl) ⟨3001643, by rfl⟩ : syracuseStep 4002191 = 6003287) B6003287
theorem B12194363 : Blo 1778090 12194363 := bstep (se 1 (by rfl) ⟨9145772, by rfl⟩ : syracuseStep 12194363 = 18291545) B18291545
theorem B4002515 : Blo 1778090 4002515 := bstep (se 1 (by rfl) ⟨3001886, by rfl⟩ : syracuseStep 4002515 = 6003773) B6003773
theorem B2667257 : Blo 1778090 2667257 := bstep (se 2 (by rfl) ⟨1000221, by rfl⟩ : syracuseStep 2667257 = 2000443) B2000443
theorem B6001451 : Blo 1778090 6001451 := bstep (se 1 (by rfl) ⟨4501088, by rfl⟩ : syracuseStep 6001451 = 9002177) B9002177
theorem B7213897 : Blo 1778090 7213897 := bstep (se 2 (by rfl) ⟨2705211, by rfl⟩ : syracuseStep 7213897 = 5410423) B5410423
theorem B2667359 : Blo 1778090 2667359 := bstep (se 1 (by rfl) ⟨2000519, by rfl⟩ : syracuseStep 2667359 = 4001039) B4001039
theorem B2667371 : Blo 1778090 2667371 := bstep (se 1 (by rfl) ⟨2000528, by rfl⟩ : syracuseStep 2667371 = 4001057) B4001057
theorem B3003311 : Blo 1778090 3003311 := bstep (se 1 (by rfl) ⟨2252483, by rfl⟩ : syracuseStep 3003311 = 4504967) B4504967
theorem B25646129 : Blo 1778090 25646129 := bstep (se 2 (by rfl) ⟨9617298, by rfl⟩ : syracuseStep 25646129 = 19234597) B19234597
theorem B6001721 : Blo 1778090 6001721 := bstep (se 2 (by rfl) ⟨2250645, by rfl⟩ : syracuseStep 6001721 = 4501291) B4501291
theorem B2667599 : Blo 1778090 2667599 := bstep (se 1 (by rfl) ⟨2000699, by rfl⟩ : syracuseStep 2667599 = 4001399) B4001399
theorem B4273231 : Blo 1778090 4273231 := bstep (se 1 (by rfl) ⟨3204923, by rfl⟩ : syracuseStep 4273231 = 6409847) B6409847
theorem B4502699 : Blo 1778090 4502699 := bstep (se 1 (by rfl) ⟨3377024, by rfl⟩ : syracuseStep 4502699 = 6754049) B6754049
theorem B9614531 : Blo 1778090 9614531 := bstep (se 1 (by rfl) ⟨7210898, by rfl⟩ : syracuseStep 9614531 = 14421797) B14421797
theorem B2667719 : Blo 1778090 2667719 := bstep (se 1 (by rfl) ⟨2000789, by rfl⟩ : syracuseStep 2667719 = 4001579) B4001579
theorem B3003743 : Blo 1778090 3003743 := bstep (se 1 (by rfl) ⟨2252807, by rfl⟩ : syracuseStep 3003743 = 4505615) B4505615
theorem B2667881 : Blo 1778090 2667881 := bstep (se 2 (by rfl) ⟨1000455, by rfl⟩ : syracuseStep 2667881 = 2000911) B2000911
theorem B6002045 : Blo 1778090 6002045 := bstep (se 3 (by rfl) ⟨1125383, by rfl⟩ : syracuseStep 6002045 = 2250767) B2250767
theorem B15201701 : Blo 1778090 15201701 := bstep (se 4 (by rfl) ⟨1425159, by rfl⟩ : syracuseStep 15201701 = 2850319) B2850319
theorem B24352163 : Blo 1778090 24352163 := bstep (se 1 (by rfl) ⟨18264122, by rfl⟩ : syracuseStep 24352163 = 36528245) B36528245
theorem B2667959 : Blo 1778090 2667959 := bstep (se 1 (by rfl) ⟨2000969, by rfl⟩ : syracuseStep 2667959 = 4001939) B4001939
theorem B2667995 : Blo 1778090 2667995 := bstep (se 1 (by rfl) ⟨2000996, by rfl⟩ : syracuseStep 2667995 = 4001993) B4001993
theorem B5068327 : Blo 1778090 5068327 := bstep (se 1 (by rfl) ⟨3801245, by rfl⟩ : syracuseStep 5068327 = 7602491) B7602491
theorem B98670149 : Blo 1778090 98670149 := bstep (se 4 (by rfl) ⟨9250326, by rfl⟩ : syracuseStep 98670149 = 18500653) B18500653
theorem B4003451 : Blo 1778090 4003451 := bstep (se 1 (by rfl) ⟨3002588, by rfl⟩ : syracuseStep 4003451 = 6005177) B6005177
theorem B6002315 : Blo 1778090 6002315 := bstep (se 1 (by rfl) ⟨4501736, by rfl⟩ : syracuseStep 6002315 = 9003473) B9003473
theorem B24336071 : Blo 1778090 24336071 := bstep (se 1 (by rfl) ⟨18252053, by rfl⟩ : syracuseStep 24336071 = 36504107) B36504107
theorem B10819271 : Blo 1778090 10819271 := bstep (se 1 (by rfl) ⟨8114453, by rfl⟩ : syracuseStep 10819271 = 16228907) B16228907
theorem B5068487 : Blo 1778090 5068487 := bstep (se 1 (by rfl) ⟨3801365, by rfl⟩ : syracuseStep 5068487 = 7602731) B7602731
theorem B22795991 : Blo 1778090 22795991 := bstep (se 1 (by rfl) ⟨17096993, by rfl⟩ : syracuseStep 22795991 = 34193987) B34193987
theorem B4003577 : Blo 1778090 4003577 := bstep (se 2 (by rfl) ⟨1501341, by rfl⟩ : syracuseStep 4003577 = 3002683) B3002683
theorem B14423903 : Blo 1778090 14423903 := bstep (se 1 (by rfl) ⟨10817927, by rfl⟩ : syracuseStep 14423903 = 21635855) B21635855
theorem B8550305 : Blo 1778090 8550305 := bstep (se 2 (by rfl) ⟨3206364, by rfl⟩ : syracuseStep 8550305 = 6412729) B6412729
theorem B2668463 : Blo 1778090 2668463 := bstep (se 1 (by rfl) ⟨2001347, by rfl⟩ : syracuseStep 2668463 = 4002695) B4002695
theorem B5068727 : Blo 1778090 5068727 := bstep (se 1 (by rfl) ⟨3801545, by rfl⟩ : syracuseStep 5068727 = 7603091) B7603091
theorem B2848699 : Blo 1778090 2848699 := bstep (se 1 (by rfl) ⟨2136524, by rfl⟩ : syracuseStep 2848699 = 4273049) B4273049
theorem B4503559 : Blo 1778090 4503559 := bstep (se 1 (by rfl) ⟨3377669, by rfl⟩ : syracuseStep 4503559 = 6755339) B6755339
theorem B4003847 : Blo 1778090 4003847 := bstep (se 1 (by rfl) ⟨3002885, by rfl⟩ : syracuseStep 4003847 = 6005771) B6005771
theorem B2668553 : Blo 1778090 2668553 := bstep (se 2 (by rfl) ⟨1000707, by rfl⟩ : syracuseStep 2668553 = 2001415) B2001415
theorem B2848807 : Blo 1778090 2848807 := bstep (se 1 (by rfl) ⟨2136605, by rfl⟩ : syracuseStep 2848807 = 4273211) B4273211
theorem B2668583 : Blo 1778090 2668583 := bstep (se 1 (by rfl) ⟨2001437, by rfl⟩ : syracuseStep 2668583 = 4002875) B4002875
theorem B4003919 : Blo 1778090 4003919 := bstep (se 1 (by rfl) ⟨3002939, by rfl⟩ : syracuseStep 4003919 = 6005879) B6005879
theorem B2668667 : Blo 1778090 2668667 := bstep (se 1 (by rfl) ⟨2001500, by rfl⟩ : syracuseStep 2668667 = 4003001) B4003001
theorem B2668793 : Blo 1778090 2668793 := bstep (se 2 (by rfl) ⟨1000797, by rfl⟩ : syracuseStep 2668793 = 2001595) B2001595
theorem B2668895 : Blo 1778090 2668895 := bstep (se 1 (by rfl) ⟨2001671, by rfl⟩ : syracuseStep 2668895 = 4003343) B4003343
theorem B4274537 : Blo 1778090 4274537 := bstep (se 2 (by rfl) ⟨1602951, by rfl⟩ : syracuseStep 4274537 = 3205903) B3205903
theorem B2668907 : Blo 1778090 2668907 := bstep (se 1 (by rfl) ⟨2001680, by rfl⟩ : syracuseStep 2668907 = 4003361) B4003361
theorem B4004315 : Blo 1778090 4004315 := bstep (se 1 (by rfl) ⟨3003236, by rfl⟩ : syracuseStep 4004315 = 6006473) B6006473
theorem B6003233 : Blo 1778090 6003233 := bstep (se 2 (by rfl) ⟨2251212, by rfl⟩ : syracuseStep 6003233 = 4502425) B4502425
theorem B2669135 : Blo 1778090 2669135 := bstep (se 1 (by rfl) ⟨2001851, by rfl⟩ : syracuseStep 2669135 = 4003703) B4003703
theorem B4504187 : Blo 1778090 4504187 := bstep (se 1 (by rfl) ⟨3378140, by rfl⟩ : syracuseStep 4504187 = 6756281) B6756281
theorem B2669255 : Blo 1778090 2669255 := bstep (se 1 (by rfl) ⟨2001941, by rfl⟩ : syracuseStep 2669255 = 4003883) B4003883
theorem B6003449 : Blo 1778090 6003449 := bstep (se 2 (by rfl) ⟨2251293, by rfl⟩ : syracuseStep 6003449 = 4502587) B4502587
theorem B9616157 : Blo 1778090 9616157 := bstep (se 3 (by rfl) ⟨1803029, by rfl⟩ : syracuseStep 9616157 = 3606059) B3606059
theorem B13687625 : Blo 1778090 13687625 := bstep (se 2 (by rfl) ⟨5132859, by rfl⟩ : syracuseStep 13687625 = 10265719) B10265719
theorem B2669417 : Blo 1778090 2669417 := bstep (se 2 (by rfl) ⟨1001031, by rfl⟩ : syracuseStep 2669417 = 2002063) B2002063
theorem B4504481 : Blo 1778090 4504481 := bstep (se 2 (by rfl) ⟨1689180, by rfl⟩ : syracuseStep 4504481 = 3378361) B3378361
theorem B4004783 : Blo 1778090 4004783 := bstep (se 1 (by rfl) ⟨3003587, by rfl⟩ : syracuseStep 4004783 = 6007175) B6007175
theorem B2669495 : Blo 1778090 2669495 := bstep (se 1 (by rfl) ⟨2002121, by rfl⟩ : syracuseStep 2669495 = 4004243) B4004243
theorem B2251739 : Blo 1778090 2251739 := bstep (se 1 (by rfl) ⟨1688804, by rfl⟩ : syracuseStep 2251739 = 3377609) B3377609
theorem B2669531 : Blo 1778090 2669531 := bstep (se 1 (by rfl) ⟨2002148, by rfl⟩ : syracuseStep 2669531 = 4004297) B4004297
theorem B6003719 : Blo 1778090 6003719 := bstep (se 1 (by rfl) ⟨4502789, by rfl⟩ : syracuseStep 6003719 = 9005579) B9005579
theorem B10968083 : Blo 1778090 10968083 := bstep (se 1 (by rfl) ⟨8226062, by rfl⟩ : syracuseStep 10968083 = 16452125) B16452125
theorem B6003827 : Blo 1778090 6003827 := bstep (se 1 (by rfl) ⟨4502870, by rfl⟩ : syracuseStep 6003827 = 9005741) B9005741
theorem B4005035 : Blo 1778090 4005035 := bstep (se 1 (by rfl) ⟨3003776, by rfl⟩ : syracuseStep 4005035 = 6007553) B6007553
theorem B6004097 : Blo 1778090 6004097 := bstep (se 2 (by rfl) ⟨2251536, by rfl⟩ : syracuseStep 6004097 = 4503073) B4503073
theorem B2669999 : Blo 1778090 2669999 := bstep (se 1 (by rfl) ⟨2002499, by rfl⟩ : syracuseStep 2669999 = 4004999) B4004999
theorem B2252215 : Blo 1778090 2252215 := bstep (se 1 (by rfl) ⟨1689161, by rfl⟩ : syracuseStep 2252215 = 3378323) B3378323
theorem B2670089 : Blo 1778090 2670089 := bstep (se 2 (by rfl) ⟨1001283, by rfl⟩ : syracuseStep 2670089 = 2002567) B2002567
theorem B2137639 : Blo 1778090 2137639 := bstep (se 1 (by rfl) ⟨1603229, by rfl⟩ : syracuseStep 2137639 = 3206459) B3206459
theorem B2670119 : Blo 1778090 2670119 := bstep (se 1 (by rfl) ⟨2002589, by rfl⟩ : syracuseStep 2670119 = 4005179) B4005179
theorem B3800699 : Blo 1778090 3800699 := bstep (se 1 (by rfl) ⟨2850524, by rfl⟩ : syracuseStep 3800699 = 5701049) B5701049
theorem B6848185 : Blo 1778090 6848185 := bstep (se 2 (by rfl) ⟨2568069, by rfl⟩ : syracuseStep 6848185 = 5136139) B5136139
theorem B39001837 : Blo 1778090 39001837 := bstep (se 3 (by rfl) ⟨7312844, by rfl⟩ : syracuseStep 39001837 = 14625689) B14625689
theorem B43859717 : Blo 1778090 43859717 := bstep (se 4 (by rfl) ⟨4111848, by rfl⟩ : syracuseStep 43859717 = 8223697) B8223697
theorem B2137951 : Blo 1778090 2137951 := bstep (se 1 (by rfl) ⟨1603463, by rfl⟩ : syracuseStep 2137951 = 3206927) B3206927
theorem B6414187 : Blo 1778090 6414187 := bstep (se 1 (by rfl) ⟨4810640, by rfl⟩ : syracuseStep 6414187 = 9621281) B9621281
theorem B6004745 : Blo 1778090 6004745 := bstep (se 2 (by rfl) ⟨2251779, by rfl⟩ : syracuseStep 6004745 = 4503559) B4503559
theorem B68378741 : Blo 1778090 68378741 := bstep (se 5 (by rfl) ⟨3205253, by rfl⟩ : syracuseStep 68378741 = 6410507) B6410507
theorem B15196369 : Blo 1778090 15196369 := bstep (se 2 (by rfl) ⟨5698638, by rfl⟩ : syracuseStep 15196369 = 11397277) B11397277
theorem B5701843 : Blo 1778090 5701843 := bstep (se 1 (by rfl) ⟨4276382, by rfl⟩ : syracuseStep 5701843 = 8552765) B8552765
theorem B9011411 : Blo 1778090 9011411 := bstep (se 1 (by rfl) ⟨6758558, by rfl⟩ : syracuseStep 9011411 = 13517117) B13517117
theorem B11403611 : Blo 1778090 11403611 := bstep (se 1 (by rfl) ⟨8552708, by rfl⟩ : syracuseStep 11403611 = 17105417) B17105417
theorem B3801451 : Blo 1778090 3801451 := bstep (se 1 (by rfl) ⟨2851088, by rfl⟩ : syracuseStep 3801451 = 5702177) B5702177
theorem B8552879 : Blo 1778090 8552879 := bstep (se 1 (by rfl) ⟨6414659, by rfl⟩ : syracuseStep 8552879 = 12829319) B12829319
theorem B4276691 : Blo 1778090 4276691 := bstep (se 1 (by rfl) ⟨3207518, by rfl⟩ : syracuseStep 4276691 = 6415037) B6415037
theorem B1778171 : Blo 1778090 1778171 := bstep (se 1 (by rfl) ⟨1333628, by rfl⟩ : syracuseStep 1778171 = 2667257) B2667257
theorem B1778239 : Blo 1778090 1778239 := bstep (se 1 (by rfl) ⟨1333679, by rfl⟩ : syracuseStep 1778239 = 2667359) B2667359
theorem B1778247 : Blo 1778090 1778247 := bstep (se 1 (by rfl) ⟨1333685, by rfl⟩ : syracuseStep 1778247 = 2667371) B2667371
theorem B36504265 : Blo 1778090 36504265 := bstep (se 2 (by rfl) ⟨13689099, by rfl⟩ : syracuseStep 36504265 = 27378199) B27378199
theorem B17097419 : Blo 1778090 17097419 := bstep (se 1 (by rfl) ⟨12823064, by rfl⟩ : syracuseStep 17097419 = 25646129) B25646129
theorem B13173463 : Blo 1778090 13173463 := bstep (se 1 (by rfl) ⟨9880097, by rfl⟩ : syracuseStep 13173463 = 19760195) B19760195
theorem B1778399 : Blo 1778090 1778399 := bstep (se 1 (by rfl) ⟨1333799, by rfl⟩ : syracuseStep 1778399 = 2667599) B2667599
theorem B1778479 : Blo 1778090 1778479 := bstep (se 1 (by rfl) ⟨1333859, by rfl⟩ : syracuseStep 1778479 = 2667719) B2667719
theorem B1778587 : Blo 1778090 1778587 := bstep (se 1 (by rfl) ⟨1333940, by rfl⟩ : syracuseStep 1778587 = 2667881) B2667881
theorem B10134467 : Blo 1778090 10134467 := bstep (se 1 (by rfl) ⟨7600850, by rfl⟩ : syracuseStep 10134467 = 15201701) B15201701
theorem B1778639 : Blo 1778090 1778639 := bstep (se 1 (by rfl) ⟨1333979, by rfl⟩ : syracuseStep 1778639 = 2667959) B2667959
theorem B1803215 : Blo 1778090 1803215 := bstep (se 1 (by rfl) ⟨1352411, by rfl⟩ : syracuseStep 1803215 = 2704823) B2704823
theorem B1778663 : Blo 1778090 1778663 := bstep (se 1 (by rfl) ⟨1333997, by rfl⟩ : syracuseStep 1778663 = 2667995) B2667995
theorem B28861429 : Blo 1778090 28861429 := bstep (se 5 (by rfl) ⟨1352879, by rfl⟩ : syracuseStep 28861429 = 2705759) B2705759
theorem B36504593 : Blo 1778090 36504593 := bstep (se 2 (by rfl) ⟨13689222, by rfl⟩ : syracuseStep 36504593 = 27378445) B27378445
theorem B9004121 : Blo 1778090 9004121 := bstep (se 2 (by rfl) ⟨3376545, by rfl⟩ : syracuseStep 9004121 = 6753091) B6753091
theorem B9618529 : Blo 1778090 9618529 := bstep (se 2 (by rfl) ⟨3606948, by rfl⟩ : syracuseStep 9618529 = 7213897) B7213897
theorem B15197327 : Blo 1778090 15197327 := bstep (se 1 (by rfl) ⟨11397995, by rfl⟩ : syracuseStep 15197327 = 22795991) B22795991
theorem B7603415 : Blo 1778090 7603415 := bstep (se 1 (by rfl) ⟨5702561, by rfl⟩ : syracuseStep 7603415 = 11405123) B11405123
theorem B1778975 : Blo 1778090 1778975 := bstep (se 1 (by rfl) ⟨1334231, by rfl⟩ : syracuseStep 1778975 = 2668463) B2668463
theorem B1779035 : Blo 1778090 1779035 := bstep (se 1 (by rfl) ⟨1334276, by rfl⟩ : syracuseStep 1779035 = 2668553) B2668553
theorem B1779055 : Blo 1778090 1779055 := bstep (se 1 (by rfl) ⟨1334291, by rfl⟩ : syracuseStep 1779055 = 2668583) B2668583
theorem B1779111 : Blo 1778090 1779111 := bstep (se 1 (by rfl) ⟨1334333, by rfl⟩ : syracuseStep 1779111 = 2668667) B2668667
theorem B1779195 : Blo 1778090 1779195 := bstep (se 1 (by rfl) ⟨1334396, by rfl⟩ : syracuseStep 1779195 = 2668793) B2668793
theorem B1779263 : Blo 1778090 1779263 := bstep (se 1 (by rfl) ⟨1334447, by rfl⟩ : syracuseStep 1779263 = 2668895) B2668895
theorem B1779271 : Blo 1778090 1779271 := bstep (se 1 (by rfl) ⟨1334453, by rfl⟩ : syracuseStep 1779271 = 2668907) B2668907
theorem B2000479 : Blo 1778090 2000479 := bstep (se 1 (by rfl) ⟨1500359, by rfl⟩ : syracuseStep 2000479 = 3000719) B3000719
theorem B1779423 : Blo 1778090 1779423 := bstep (se 1 (by rfl) ⟨1334567, by rfl⟩ : syracuseStep 1779423 = 2669135) B2669135
theorem B3376903 : Blo 1778090 3376903 := bstep (se 1 (by rfl) ⟨2532677, by rfl⟩ : syracuseStep 3376903 = 5065355) B5065355
theorem B1779503 : Blo 1778090 1779503 := bstep (se 1 (by rfl) ⟨1334627, by rfl⟩ : syracuseStep 1779503 = 2669255) B2669255
theorem B6752105 : Blo 1778090 6752105 := bstep (se 2 (by rfl) ⟨2532039, by rfl⟩ : syracuseStep 6752105 = 5064079) B5064079
theorem B17106835 : Blo 1778090 17106835 := bstep (se 1 (by rfl) ⟨12830126, by rfl⟩ : syracuseStep 17106835 = 25660253) B25660253
theorem B1779611 : Blo 1778090 1779611 := bstep (se 1 (by rfl) ⟨1334708, by rfl⟩ : syracuseStep 1779611 = 2669417) B2669417
theorem B1779663 : Blo 1778090 1779663 := bstep (se 1 (by rfl) ⟨1334747, by rfl⟩ : syracuseStep 1779663 = 2669495) B2669495
theorem B1779687 : Blo 1778090 1779687 := bstep (se 1 (by rfl) ⟨1334765, by rfl⟩ : syracuseStep 1779687 = 2669531) B2669531
theorem B8669263 : Blo 1778090 8669263 := bstep (se 1 (by rfl) ⟨6501947, by rfl⟩ : syracuseStep 8669263 = 13003895) B13003895
theorem B29231389 : Blo 1778090 29231389 := bstep (se 3 (by rfl) ⟨5480885, by rfl⟩ : syracuseStep 29231389 = 10961771) B10961771
theorem B1779999 : Blo 1778090 1779999 := bstep (se 1 (by rfl) ⟨1334999, by rfl⟩ : syracuseStep 1779999 = 2669999) B2669999
theorem B4811081 : Blo 1778090 4811081 := bstep (se 2 (by rfl) ⟨1804155, by rfl⟩ : syracuseStep 4811081 = 3608311) B3608311
theorem B1780059 : Blo 1778090 1780059 := bstep (se 1 (by rfl) ⟨1335044, by rfl⟩ : syracuseStep 1780059 = 2670089) B2670089
theorem B1780079 : Blo 1778090 1780079 := bstep (se 1 (by rfl) ⟨1335059, by rfl⟩ : syracuseStep 1780079 = 2670119) B2670119
theorem B2533799 : Blo 1778090 2533799 := bstep (se 1 (by rfl) ⟨1900349, by rfl⟩ : syracuseStep 2533799 = 3800699) B3800699
theorem B3000827 : Blo 1778090 3000827 := bstep (se 1 (by rfl) ⟨2250620, by rfl⟩ : syracuseStep 3000827 = 4501241) B4501241
theorem B29239811 : Blo 1778090 29239811 := bstep (se 1 (by rfl) ⟨21929858, by rfl⟩ : syracuseStep 29239811 = 43859717) B43859717
theorem B15207101 : Blo 1778090 15207101 := bstep (se 3 (by rfl) ⟨2851331, by rfl⟩ : syracuseStep 15207101 = 5702663) B5702663
theorem B2001631 : Blo 1778090 2001631 := bstep (se 1 (by rfl) ⟨1501223, by rfl⟩ : syracuseStep 2001631 = 3002447) B3002447
theorem B8547191 : Blo 1778090 8547191 := bstep (se 1 (by rfl) ⟨6410393, by rfl⟩ : syracuseStep 8547191 = 12820787) B12820787
theorem B2403227 : Blo 1778090 2403227 := bstep (se 1 (by rfl) ⟨1802420, by rfl⟩ : syracuseStep 2403227 = 3604841) B3604841
theorem B3001259 : Blo 1778090 3001259 := bstep (se 1 (by rfl) ⟨2250944, by rfl⟩ : syracuseStep 3001259 = 4501889) B4501889
theorem B3206135 : Blo 1778090 3206135 := bstep (se 1 (by rfl) ⟨2404601, by rfl⟩ : syracuseStep 3206135 = 4809203) B4809203
theorem B8129575 : Blo 1778090 8129575 := bstep (se 1 (by rfl) ⟨6097181, by rfl⟩ : syracuseStep 8129575 = 12194363) B12194363
theorem B4000967 : Blo 1778090 4000967 := bstep (se 1 (by rfl) ⟨3000725, by rfl⟩ : syracuseStep 4000967 = 6001451) B6001451
theorem B2002207 : Blo 1778090 2002207 := bstep (se 1 (by rfl) ⟨1501655, by rfl⟩ : syracuseStep 2002207 = 3003311) B3003311
theorem B4001147 : Blo 1778090 4001147 := bstep (se 1 (by rfl) ⟨3000860, by rfl⟩ : syracuseStep 4001147 = 6001721) B6001721
theorem B3001799 : Blo 1778090 3001799 := bstep (se 1 (by rfl) ⟨2251349, by rfl⟩ : syracuseStep 3001799 = 4502699) B4502699
theorem B6409687 : Blo 1778090 6409687 := bstep (se 1 (by rfl) ⟨4807265, by rfl⟩ : syracuseStep 6409687 = 9614531) B9614531
theorem B9006551 : Blo 1778090 9006551 := bstep (se 1 (by rfl) ⟨6754913, by rfl⟩ : syracuseStep 9006551 = 13509827) B13509827
theorem B4001273 : Blo 1778090 4001273 := bstep (se 2 (by rfl) ⟨1500477, by rfl⟩ : syracuseStep 4001273 = 3000955) B3000955
theorem B2002495 : Blo 1778090 2002495 := bstep (se 1 (by rfl) ⟨1501871, by rfl⟩ : syracuseStep 2002495 = 3003743) B3003743
theorem B4001363 : Blo 1778090 4001363 := bstep (se 1 (by rfl) ⟨3001022, by rfl⟩ : syracuseStep 4001363 = 6002045) B6002045
theorem B11398765 : Blo 1778090 11398765 := bstep (se 3 (by rfl) ⟨2137268, by rfl⟩ : syracuseStep 11398765 = 4274537) B4274537
theorem B30412421 : Blo 1778090 30412421 := bstep (se 4 (by rfl) ⟨2851164, by rfl⟩ : syracuseStep 30412421 = 5702329) B5702329
theorem B4001543 : Blo 1778090 4001543 := bstep (se 1 (by rfl) ⟨3001157, by rfl⟩ : syracuseStep 4001543 = 6002315) B6002315
theorem B16224047 : Blo 1778090 16224047 := bstep (se 1 (by rfl) ⟨12168035, by rfl⟩ : syracuseStep 16224047 = 24336071) B24336071
theorem B7212847 : Blo 1778090 7212847 := bstep (se 1 (by rfl) ⟨5409635, by rfl⟩ : syracuseStep 7212847 = 10819271) B10819271
theorem B3378991 : Blo 1778090 3378991 := bstep (se 1 (by rfl) ⟨2534243, by rfl⟩ : syracuseStep 3378991 = 5068487) B5068487
theorem B12824477 : Blo 1778090 12824477 := bstep (se 3 (by rfl) ⟨2404589, by rfl⟩ : syracuseStep 12824477 = 4809179) B4809179
theorem B3379151 : Blo 1778090 3379151 := bstep (se 1 (by rfl) ⟨2534363, by rfl⟩ : syracuseStep 3379151 = 5068727) B5068727
theorem B5697641 : Blo 1778090 5697641 := bstep (se 2 (by rfl) ⟨2136615, by rfl⟩ : syracuseStep 5697641 = 4273231) B4273231
theorem B8229073 : Blo 1778090 8229073 := bstep (se 2 (by rfl) ⟨3085902, by rfl⟩ : syracuseStep 8229073 = 6171805) B6171805
theorem B4002155 : Blo 1778090 4002155 := bstep (se 1 (by rfl) ⟨3001616, by rfl⟩ : syracuseStep 4002155 = 6003233) B6003233
theorem B3002791 : Blo 1778090 3002791 := bstep (se 1 (by rfl) ⟨2252093, by rfl⟩ : syracuseStep 3002791 = 4504187) B4504187
theorem B4002299 : Blo 1778090 4002299 := bstep (se 1 (by rfl) ⟨3001724, by rfl⟩ : syracuseStep 4002299 = 6003449) B6003449
theorem B6410771 : Blo 1778090 6410771 := bstep (se 1 (by rfl) ⟨4808078, by rfl⟩ : syracuseStep 6410771 = 9616157) B9616157
theorem B3002953 : Blo 1778090 3002953 := bstep (se 2 (by rfl) ⟨1126107, by rfl⟩ : syracuseStep 3002953 = 2252215) B2252215
theorem B3002987 : Blo 1778090 3002987 := bstep (se 1 (by rfl) ⟨2252240, by rfl⟩ : syracuseStep 3002987 = 4504481) B4504481
theorem B4002425 : Blo 1778090 4002425 := bstep (se 2 (by rfl) ⟨1500909, by rfl⟩ : syracuseStep 4002425 = 3001819) B3001819
theorem B3797675 : Blo 1778090 3797675 := bstep (se 1 (by rfl) ⟨2848256, by rfl⟩ : syracuseStep 3797675 = 5696513) B5696513
theorem B4002479 : Blo 1778090 4002479 := bstep (se 1 (by rfl) ⟨3001859, by rfl⟩ : syracuseStep 4002479 = 6003719) B6003719
theorem B2667191 : Blo 1778090 2667191 := bstep (se 1 (by rfl) ⟨2000393, by rfl⟩ : syracuseStep 2667191 = 4000787) B4000787
theorem B7312055 : Blo 1778090 7312055 := bstep (se 1 (by rfl) ⟨5484041, by rfl⟩ : syracuseStep 7312055 = 10968083) B10968083
theorem B4502263 : Blo 1778090 4502263 := bstep (se 1 (by rfl) ⟨3376697, by rfl⟩ : syracuseStep 4502263 = 6753395) B6753395
theorem B4002551 : Blo 1778090 4002551 := bstep (se 1 (by rfl) ⟨3001913, by rfl⟩ : syracuseStep 4002551 = 6003827) B6003827
theorem B2667419 : Blo 1778090 2667419 := bstep (se 1 (by rfl) ⟨2000564, by rfl⟩ : syracuseStep 2667419 = 4001129) B4001129
theorem B9130913 : Blo 1778090 9130913 := bstep (se 2 (by rfl) ⟨3424092, by rfl⟩ : syracuseStep 9130913 = 6848185) B6848185
theorem B4002731 : Blo 1778090 4002731 := bstep (se 1 (by rfl) ⟨3002048, by rfl⟩ : syracuseStep 4002731 = 6004097) B6004097
theorem B4502567 : Blo 1778090 4502567 := bstep (se 1 (by rfl) ⟨3376925, by rfl⟩ : syracuseStep 4502567 = 6753851) B6753851
theorem B20255993 : Blo 1778090 20255993 := bstep (se 2 (by rfl) ⟨7595997, by rfl⟩ : syracuseStep 20255993 = 15191995) B15191995
theorem B3798265 : Blo 1778090 3798265 := bstep (se 2 (by rfl) ⟨1424349, by rfl⟩ : syracuseStep 3798265 = 2848699) B2848699
theorem B2667815 : Blo 1778090 2667815 := bstep (se 1 (by rfl) ⟨2000861, by rfl⟩ : syracuseStep 2667815 = 4001723) B4001723
theorem B2667899 : Blo 1778090 2667899 := bstep (se 1 (by rfl) ⟨2000924, by rfl⟩ : syracuseStep 2667899 = 4001849) B4001849
theorem B3798409 : Blo 1778090 3798409 := bstep (se 2 (by rfl) ⟨1424403, by rfl⟩ : syracuseStep 3798409 = 2848807) B2848807
theorem B4003271 : Blo 1778090 4003271 := bstep (se 1 (by rfl) ⟨3002453, by rfl⟩ : syracuseStep 4003271 = 6004907) B6004907
theorem B2668025 : Blo 1778090 2668025 := bstep (se 2 (by rfl) ⟨1000509, by rfl⟩ : syracuseStep 2668025 = 2001019) B2001019
theorem B2668127 : Blo 1778090 2668127 := bstep (se 1 (by rfl) ⟨2001095, by rfl⟩ : syracuseStep 2668127 = 4002191) B4002191
theorem B4003631 : Blo 1778090 4003631 := bstep (se 1 (by rfl) ⟨3002723, by rfl⟩ : syracuseStep 4003631 = 6005447) B6005447
theorem B2668343 : Blo 1778090 2668343 := bstep (se 1 (by rfl) ⟨2001257, by rfl⟩ : syracuseStep 2668343 = 4002515) B4002515
theorem B7214935 : Blo 1778090 7214935 := bstep (se 1 (by rfl) ⟨5411201, by rfl⟩ : syracuseStep 7214935 = 10822403) B10822403
theorem B20821853 : Blo 1778090 20821853 := bstep (se 3 (by rfl) ⟨3904097, by rfl⟩ : syracuseStep 20821853 = 7808195) B7808195
theorem B6002639 : Blo 1778090 6002639 := bstep (se 1 (by rfl) ⟨4501979, by rfl⟩ : syracuseStep 6002639 = 9003959) B9003959
theorem B2668649 : Blo 1778090 2668649 := bstep (se 2 (by rfl) ⟨1000743, by rfl⟩ : syracuseStep 2668649 = 2001487) B2001487
theorem B57677957 : Blo 1778090 57677957 := bstep (se 4 (by rfl) ⟨5407308, by rfl⟩ : syracuseStep 57677957 = 10814617) B10814617
theorem B4274441 : Blo 1778090 4274441 := bstep (se 2 (by rfl) ⟨1602915, by rfl⟩ : syracuseStep 4274441 = 3205831) B3205831
theorem B12171545 : Blo 1778090 12171545 := bstep (se 2 (by rfl) ⟨4564329, by rfl⟩ : syracuseStep 12171545 = 9128659) B9128659
theorem B4503833 : Blo 1778090 4503833 := bstep (se 2 (by rfl) ⟨1688937, by rfl⟩ : syracuseStep 4503833 = 3377875) B3377875
theorem B16234775 : Blo 1778090 16234775 := bstep (se 1 (by rfl) ⟨12176081, by rfl⟩ : syracuseStep 16234775 = 24352163) B24352163
theorem B4004207 : Blo 1778090 4004207 := bstep (se 1 (by rfl) ⟨3003155, by rfl⟩ : syracuseStep 4004207 = 6006311) B6006311
theorem B65780099 : Blo 1778090 65780099 := bstep (se 1 (by rfl) ⟨49335074, by rfl⟩ : syracuseStep 65780099 = 98670149) B98670149
theorem B2668967 : Blo 1778090 2668967 := bstep (se 1 (by rfl) ⟨2001725, by rfl⟩ : syracuseStep 2668967 = 4003451) B4003451
theorem B4004279 : Blo 1778090 4004279 := bstep (se 1 (by rfl) ⟨3003209, by rfl⟩ : syracuseStep 4004279 = 6006419) B6006419
theorem B2669051 : Blo 1778090 2669051 := bstep (se 1 (by rfl) ⟨2001788, by rfl⟩ : syracuseStep 2669051 = 4003577) B4003577
theorem B9615935 : Blo 1778090 9615935 := bstep (se 1 (by rfl) ⟨7211951, by rfl⟩ : syracuseStep 9615935 = 14423903) B14423903
theorem B4004423 : Blo 1778090 4004423 := bstep (se 1 (by rfl) ⟨3003317, by rfl⟩ : syracuseStep 4004423 = 6006635) B6006635
theorem B5700203 : Blo 1778090 5700203 := bstep (se 1 (by rfl) ⟨4275152, by rfl⟩ : syracuseStep 5700203 = 8550305) B8550305
theorem B4004459 : Blo 1778090 4004459 := bstep (se 1 (by rfl) ⟨3003344, by rfl⟩ : syracuseStep 4004459 = 6006689) B6006689
theorem B2669177 : Blo 1778090 2669177 := bstep (se 2 (by rfl) ⟨1000941, by rfl⟩ : syracuseStep 2669177 = 2001883) B2001883
theorem B2669231 : Blo 1778090 2669231 := bstep (se 1 (by rfl) ⟨2001923, by rfl⟩ : syracuseStep 2669231 = 4003847) B4003847
theorem B8116931 : Blo 1778090 8116931 := bstep (se 1 (by rfl) ⟨6087698, by rfl⟩ : syracuseStep 8116931 = 12175397) B12175397
theorem B2669279 : Blo 1778090 2669279 := bstep (se 1 (by rfl) ⟨2001959, by rfl⟩ : syracuseStep 2669279 = 4003919) B4003919
theorem B2251567 : Blo 1778090 2251567 := bstep (se 1 (by rfl) ⟨1688675, by rfl⟩ : syracuseStep 2251567 = 3377351) B3377351
theorem B9001853 : Blo 1778090 9001853 := bstep (se 3 (by rfl) ⟨1687847, by rfl⟩ : syracuseStep 9001853 = 3375695) B3375695
theorem B6003611 : Blo 1778090 6003611 := bstep (se 1 (by rfl) ⟨4502708, by rfl⟩ : syracuseStep 6003611 = 9005417) B9005417
theorem B2669543 : Blo 1778090 2669543 := bstep (se 1 (by rfl) ⟨2002157, by rfl⟩ : syracuseStep 2669543 = 4004315) B4004315
theorem B4004855 : Blo 1778090 4004855 := bstep (se 1 (by rfl) ⟨3003641, by rfl⟩ : syracuseStep 4004855 = 6007283) B6007283
theorem B4504673 : Blo 1778090 4504673 := bstep (se 2 (by rfl) ⟨1689252, by rfl⟩ : syracuseStep 4504673 = 3378505) B3378505
theorem B9125083 : Blo 1778090 9125083 := bstep (se 1 (by rfl) ⟨6843812, by rfl⟩ : syracuseStep 9125083 = 13687625) B13687625
theorem B2669801 : Blo 1778090 2669801 := bstep (se 2 (by rfl) ⟨1001175, by rfl⟩ : syracuseStep 2669801 = 2002351) B2002351
theorem B2252063 : Blo 1778090 2252063 := bstep (se 1 (by rfl) ⟨1689047, by rfl⟩ : syracuseStep 2252063 = 3378095) B3378095
theorem B2669855 : Blo 1778090 2669855 := bstep (se 1 (by rfl) ⟨2002391, by rfl⟩ : syracuseStep 2669855 = 4004783) B4004783
theorem B2850185 : Blo 1778090 2850185 := bstep (se 2 (by rfl) ⟨1068819, by rfl⟩ : syracuseStep 2850185 = 2137639) B2137639
theorem B6757769 : Blo 1778090 6757769 := bstep (se 2 (by rfl) ⟨2534163, by rfl⟩ : syracuseStep 6757769 = 5068327) B5068327
theorem B5135815 : Blo 1778090 5135815 := bstep (se 1 (by rfl) ⟨3851861, by rfl⟩ : syracuseStep 5135815 = 7703723) B7703723
theorem B2670023 : Blo 1778090 2670023 := bstep (se 1 (by rfl) ⟨2002517, by rfl⟩ : syracuseStep 2670023 = 4005035) B4005035
theorem B52002449 : Blo 1778090 52002449 := bstep (se 2 (by rfl) ⟨19500918, by rfl⟩ : syracuseStep 52002449 = 39001837) B39001837
theorem B8117969 : Blo 1778090 8117969 := bstep (se 2 (by rfl) ⟨3044238, by rfl⟩ : syracuseStep 8117969 = 6088477) B6088477
theorem B2850601 : Blo 1778090 2850601 := bstep (se 2 (by rfl) ⟨1068975, by rfl⟩ : syracuseStep 2850601 = 2137951) B2137951
theorem B8552249 : Blo 1778090 8552249 := bstep (se 2 (by rfl) ⟨3207093, by rfl⟩ : syracuseStep 8552249 = 6414187) B6414187
theorem B9002825 : Blo 1778090 9002825 := bstep (se 2 (by rfl) ⟨3376059, by rfl⟩ : syracuseStep 9002825 = 6752119) B6752119
theorem B6004637 : Blo 1778090 6004637 := bstep (se 3 (by rfl) ⟨1125869, by rfl⟩ : syracuseStep 6004637 = 2251739) B2251739
theorem B11559017 : Blo 1778090 11559017 := bstep (se 2 (by rfl) ⟨4334631, by rfl⟩ : syracuseStep 11559017 = 8669263) B8669263
theorem B7602407 : Blo 1778090 7602407 := bstep (se 1 (by rfl) ⟨5701805, by rfl⟩ : syracuseStep 7602407 = 11403611) B11403611
theorem B7602457 : Blo 1778090 7602457 := bstep (se 2 (by rfl) ⟨2850921, by rfl⟩ : syracuseStep 7602457 = 5701843) B5701843
theorem B5701919 : Blo 1778090 5701919 := bstep (se 1 (by rfl) ⟨4276439, by rfl⟩ : syracuseStep 5701919 = 8552879) B8552879
theorem B2851127 : Blo 1778090 2851127 := bstep (se 1 (by rfl) ⟨2138345, by rfl⟩ : syracuseStep 2851127 = 4276691) B4276691
theorem B2531783 : Blo 1778090 2531783 := bstep (se 1 (by rfl) ⟨1898837, by rfl⟩ : syracuseStep 2531783 = 3797675) B3797675
theorem B1778127 : Blo 1778090 1778127 := bstep (se 1 (by rfl) ⟨1333595, by rfl⟩ : syracuseStep 1778127 = 2667191) B2667191
theorem B1778279 : Blo 1778090 1778279 := bstep (se 1 (by rfl) ⟨1333709, by rfl⟩ : syracuseStep 1778279 = 2667419) B2667419
theorem B6087275 : Blo 1778090 6087275 := bstep (se 1 (by rfl) ⟨4565456, by rfl⟩ : syracuseStep 6087275 = 9130913) B9130913
theorem B6005501 : Blo 1778090 6005501 := bstep (se 3 (by rfl) ⟨1126031, by rfl⟩ : syracuseStep 6005501 = 2252063) B2252063
theorem B1778543 : Blo 1778090 1778543 := bstep (se 1 (by rfl) ⟨1333907, by rfl⟩ : syracuseStep 1778543 = 2667815) B2667815
theorem B1778599 : Blo 1778090 1778599 := bstep (se 1 (by rfl) ⟨1333949, by rfl⟩ : syracuseStep 1778599 = 2667899) B2667899
theorem B17564617 : Blo 1778090 17564617 := bstep (se 2 (by rfl) ⟨6586731, by rfl⟩ : syracuseStep 17564617 = 13173463) B13173463
theorem B1778683 : Blo 1778090 1778683 := bstep (se 1 (by rfl) ⟨1334012, by rfl⟩ : syracuseStep 1778683 = 2668025) B2668025
theorem B1778751 : Blo 1778090 1778751 := bstep (se 1 (by rfl) ⟨1334063, by rfl⟩ : syracuseStep 1778751 = 2668127) B2668127
theorem B1778895 : Blo 1778090 1778895 := bstep (se 1 (by rfl) ⟨1334171, by rfl⟩ : syracuseStep 1778895 = 2668343) B2668343
theorem B10839433 : Blo 1778090 10839433 := bstep (se 2 (by rfl) ⟨4064787, by rfl⟩ : syracuseStep 10839433 = 8129575) B8129575
theorem B1779099 : Blo 1778090 1779099 := bstep (se 1 (by rfl) ⟨1334324, by rfl⟩ : syracuseStep 1779099 = 2668649) B2668649
theorem B25642493 : Blo 1778090 25642493 := bstep (se 3 (by rfl) ⟨4807967, by rfl⟩ : syracuseStep 25642493 = 9615935) B9615935
theorem B10823183 : Blo 1778090 10823183 := bstep (se 1 (by rfl) ⟨8117387, by rfl⟩ : syracuseStep 10823183 = 16234775) B16234775
theorem B43853399 : Blo 1778090 43853399 := bstep (se 1 (by rfl) ⟨32890049, by rfl⟩ : syracuseStep 43853399 = 65780099) B65780099
theorem B1779311 : Blo 1778090 1779311 := bstep (se 1 (by rfl) ⟨1334483, by rfl⟩ : syracuseStep 1779311 = 2668967) B2668967
theorem B12166777 : Blo 1778090 12166777 := bstep (se 2 (by rfl) ⟨4562541, by rfl⟩ : syracuseStep 12166777 = 9125083) B9125083
theorem B5064353 : Blo 1778090 5064353 := bstep (se 2 (by rfl) ⟨1899132, by rfl⟩ : syracuseStep 5064353 = 3798265) B3798265
theorem B2000551 : Blo 1778090 2000551 := bstep (se 1 (by rfl) ⟨1500413, by rfl⟩ : syracuseStep 2000551 = 3000827) B3000827
theorem B1779367 : Blo 1778090 1779367 := bstep (se 1 (by rfl) ⟨1334525, by rfl⟩ : syracuseStep 1779367 = 2669051) B2669051
theorem B1779451 : Blo 1778090 1779451 := bstep (se 1 (by rfl) ⟨1334588, by rfl⟩ : syracuseStep 1779451 = 2669177) B2669177
theorem B1779487 : Blo 1778090 1779487 := bstep (se 1 (by rfl) ⟨1334615, by rfl⟩ : syracuseStep 1779487 = 2669231) B2669231
theorem B1779519 : Blo 1778090 1779519 := bstep (se 1 (by rfl) ⟨1334639, by rfl⟩ : syracuseStep 1779519 = 2669279) B2669279
theorem B21645149 : Blo 1778090 21645149 := bstep (se 3 (by rfl) ⟨4058465, by rfl⟩ : syracuseStep 21645149 = 8116931) B8116931
theorem B5064545 : Blo 1778090 5064545 := bstep (se 2 (by rfl) ⟨1899204, by rfl⟩ : syracuseStep 5064545 = 3798409) B3798409
theorem B2000839 : Blo 1778090 2000839 := bstep (se 1 (by rfl) ⟨1500629, by rfl⟩ : syracuseStep 2000839 = 3001259) B3001259
theorem B8546249 : Blo 1778090 8546249 := bstep (se 2 (by rfl) ⟨3204843, by rfl⟩ : syracuseStep 8546249 = 6409687) B6409687
theorem B1779695 : Blo 1778090 1779695 := bstep (se 1 (by rfl) ⟨1334771, by rfl⟩ : syracuseStep 1779695 = 2669543) B2669543
theorem B15198353 : Blo 1778090 15198353 := bstep (se 2 (by rfl) ⟨5699382, by rfl⟩ : syracuseStep 15198353 = 11398765) B11398765
theorem B1779867 : Blo 1778090 1779867 := bstep (se 1 (by rfl) ⟨1334900, by rfl⟩ : syracuseStep 1779867 = 2669801) B2669801
theorem B1779903 : Blo 1778090 1779903 := bstep (se 1 (by rfl) ⟨1334927, by rfl⟩ : syracuseStep 1779903 = 2669855) B2669855
theorem B2001199 : Blo 1778090 2001199 := bstep (se 1 (by rfl) ⟨1500899, by rfl⟩ : syracuseStep 2001199 = 3001799) B3001799
theorem B1780015 : Blo 1778090 1780015 := bstep (se 1 (by rfl) ⟨1335011, by rfl⟩ : syracuseStep 1780015 = 2670023) B2670023
theorem B6408605 : Blo 1778090 6408605 := bstep (se 3 (by rfl) ⟨1201613, by rfl⟩ : syracuseStep 6408605 = 2403227) B2403227
theorem B9619913 : Blo 1778090 9619913 := bstep (se 2 (by rfl) ⟨3607467, by rfl⟩ : syracuseStep 9619913 = 7214935) B7214935
theorem B22809113 : Blo 1778090 22809113 := bstep (se 2 (by rfl) ⟨8553417, by rfl⟩ : syracuseStep 22809113 = 17106835) B17106835
theorem B10816031 : Blo 1778090 10816031 := bstep (se 1 (by rfl) ⟨8112023, by rfl⟩ : syracuseStep 10816031 = 16224047) B16224047
theorem B6007607 : Blo 1778090 6007607 := bstep (se 1 (by rfl) ⟨4505705, by rfl⟩ : syracuseStep 6007607 = 9011411) B9011411
theorem B20261825 : Blo 1778090 20261825 := bstep (se 2 (by rfl) ⟨7598184, by rfl⟩ : syracuseStep 20261825 = 15196369) B15196369
theorem B10972097 : Blo 1778090 10972097 := bstep (se 2 (by rfl) ⟨4114536, by rfl⟩ : syracuseStep 10972097 = 8229073) B8229073
theorem B2001991 : Blo 1778090 2001991 := bstep (se 1 (by rfl) ⟨1501493, by rfl⟩ : syracuseStep 2001991 = 3002987) B3002987
theorem B11398279 : Blo 1778090 11398279 := bstep (se 1 (by rfl) ⟨8548709, by rfl⟩ : syracuseStep 11398279 = 17097419) B17097419
theorem B3001711 : Blo 1778090 3001711 := bstep (se 1 (by rfl) ⟨2251283, by rfl⟩ : syracuseStep 3001711 = 4502567) B4502567
theorem B51318197 : Blo 1778090 51318197 := bstep (se 5 (by rfl) ⟨2405540, by rfl⟩ : syracuseStep 51318197 = 4811081) B4811081
theorem B13503995 : Blo 1778090 13503995 := bstep (se 1 (by rfl) ⟨10127996, by rfl⟩ : syracuseStep 13503995 = 20255993) B20255993
theorem B48672353 : Blo 1778090 48672353 := bstep (se 2 (by rfl) ⟨18252132, by rfl⟩ : syracuseStep 48672353 = 36504265) B36504265
theorem B3002089 : Blo 1778090 3002089 := bstep (se 2 (by rfl) ⟨1125783, by rfl⟩ : syracuseStep 3002089 = 2251567) B2251567
theorem B13881235 : Blo 1778090 13881235 := bstep (se 1 (by rfl) ⟨10410926, by rfl⟩ : syracuseStep 13881235 = 20821853) B20821853
theorem B4501403 : Blo 1778090 4501403 := bstep (se 1 (by rfl) ⟨3376052, by rfl⟩ : syracuseStep 4501403 = 6752105) B6752105
theorem B4001759 : Blo 1778090 4001759 := bstep (se 1 (by rfl) ⟨3001319, by rfl⟩ : syracuseStep 4001759 = 6002639) B6002639
theorem B38481905 : Blo 1778090 38481905 := bstep (se 2 (by rfl) ⟨14430714, by rfl⟩ : syracuseStep 38481905 = 28861429) B28861429
theorem B12824705 : Blo 1778090 12824705 := bstep (se 2 (by rfl) ⟨4809264, by rfl⟩ : syracuseStep 12824705 = 9618529) B9618529
theorem B8114363 : Blo 1778090 8114363 := bstep (se 1 (by rfl) ⟨6085772, by rfl⟩ : syracuseStep 8114363 = 12171545) B12171545
theorem B3002555 : Blo 1778090 3002555 := bstep (se 1 (by rfl) ⟨2251916, by rfl⟩ : syracuseStep 3002555 = 4503833) B4503833
theorem B19493207 : Blo 1778090 19493207 := bstep (se 1 (by rfl) ⟨14619905, by rfl⟩ : syracuseStep 19493207 = 29239811) B29239811
theorem B10138067 : Blo 1778090 10138067 := bstep (se 1 (by rfl) ⟨7603550, by rfl⟩ : syracuseStep 10138067 = 15207101) B15207101
theorem B21647917 : Blo 1778090 21647917 := bstep (se 3 (by rfl) ⟨4058984, by rfl⟩ : syracuseStep 21647917 = 8117969) B8117969
theorem B5698127 : Blo 1778090 5698127 := bstep (se 1 (by rfl) ⟨4273595, by rfl⟩ : syracuseStep 5698127 = 8547191) B8547191
theorem B6001235 : Blo 1778090 6001235 := bstep (se 1 (by rfl) ⟨4500926, by rfl⟩ : syracuseStep 6001235 = 9001853) B9001853
theorem B4002407 : Blo 1778090 4002407 := bstep (se 1 (by rfl) ⟨3001805, by rfl⟩ : syracuseStep 4002407 = 6003611) B6003611
theorem B3003115 : Blo 1778090 3003115 := bstep (se 1 (by rfl) ⟨2252336, by rfl⟩ : syracuseStep 3003115 = 4504673) B4504673
theorem B2667305 : Blo 1778090 2667305 := bstep (se 2 (by rfl) ⟨1000239, by rfl⟩ : syracuseStep 2667305 = 2000479) B2000479
theorem B2667311 : Blo 1778090 2667311 := bstep (se 1 (by rfl) ⟨2000483, by rfl⟩ : syracuseStep 2667311 = 4000967) B4000967
theorem B2667431 : Blo 1778090 2667431 := bstep (se 1 (by rfl) ⟨2000573, by rfl⟩ : syracuseStep 2667431 = 4001147) B4001147
theorem B2667515 : Blo 1778090 2667515 := bstep (se 1 (by rfl) ⟨2000636, by rfl⟩ : syracuseStep 2667515 = 4001273) B4001273
theorem B4502537 : Blo 1778090 4502537 := bstep (se 2 (by rfl) ⟨1688451, by rfl⟩ : syracuseStep 4502537 = 3376903) B3376903
theorem B2667575 : Blo 1778090 2667575 := bstep (se 1 (by rfl) ⟨2000681, by rfl⟩ : syracuseStep 2667575 = 4001363) B4001363
theorem B2667695 : Blo 1778090 2667695 := bstep (se 1 (by rfl) ⟨2000771, by rfl⟩ : syracuseStep 2667695 = 4001543) B4001543
theorem B6001883 : Blo 1778090 6001883 := bstep (se 1 (by rfl) ⟨4501412, by rfl⟩ : syracuseStep 6001883 = 9002825) B9002825
theorem B4003091 : Blo 1778090 4003091 := bstep (se 1 (by rfl) ⟨3002318, by rfl⟩ : syracuseStep 4003091 = 6004637) B6004637
theorem B8549651 : Blo 1778090 8549651 := bstep (se 1 (by rfl) ⟨6412238, by rfl⟩ : syracuseStep 8549651 = 12824477) B12824477
theorem B4003163 : Blo 1778090 4003163 := bstep (se 1 (by rfl) ⟨3002372, by rfl⟩ : syracuseStep 4003163 = 6004745) B6004745
theorem B3798427 : Blo 1778090 3798427 := bstep (se 1 (by rfl) ⟨2848820, by rfl⟩ : syracuseStep 3798427 = 5697641) B5697641
theorem B45585827 : Blo 1778090 45585827 := bstep (se 1 (by rfl) ⟨34189370, by rfl⟩ : syracuseStep 45585827 = 68378741) B68378741
theorem B2668103 : Blo 1778090 2668103 := bstep (se 1 (by rfl) ⟨2001077, by rfl⟩ : syracuseStep 2668103 = 4002155) B4002155
theorem B2668199 : Blo 1778090 2668199 := bstep (se 1 (by rfl) ⟨2001149, by rfl⟩ : syracuseStep 2668199 = 4002299) B4002299
theorem B4273847 : Blo 1778090 4273847 := bstep (se 1 (by rfl) ⟨3205385, by rfl⟩ : syracuseStep 4273847 = 6410771) B6410771
theorem B38975185 : Blo 1778090 38975185 := bstep (se 2 (by rfl) ⟨14615694, by rfl⟩ : syracuseStep 38975185 = 29231389) B29231389
theorem B2668283 : Blo 1778090 2668283 := bstep (se 1 (by rfl) ⟨2001212, by rfl⟩ : syracuseStep 2668283 = 4002425) B4002425
theorem B2668319 : Blo 1778090 2668319 := bstep (se 1 (by rfl) ⟨2001239, by rfl⟩ : syracuseStep 2668319 = 4002479) B4002479
theorem B5068601 : Blo 1778090 5068601 := bstep (se 2 (by rfl) ⟨1900725, by rfl⟩ : syracuseStep 5068601 = 3801451) B3801451
theorem B2668367 : Blo 1778090 2668367 := bstep (se 1 (by rfl) ⟨2001275, by rfl⟩ : syracuseStep 2668367 = 4002551) B4002551
theorem B4003721 : Blo 1778090 4003721 := bstep (se 2 (by rfl) ⟨1501395, by rfl⟩ : syracuseStep 4003721 = 3002791) B3002791
theorem B2668487 : Blo 1778090 2668487 := bstep (se 1 (by rfl) ⟨2001365, by rfl⟩ : syracuseStep 2668487 = 4002731) B4002731
theorem B6756311 : Blo 1778090 6756311 := bstep (se 1 (by rfl) ⟨5067233, by rfl⟩ : syracuseStep 6756311 = 10134467) B10134467
theorem B24336395 : Blo 1778090 24336395 := bstep (se 1 (by rfl) ⟨18252296, by rfl⟩ : syracuseStep 24336395 = 36504593) B36504593
theorem B6002747 : Blo 1778090 6002747 := bstep (se 1 (by rfl) ⟨4502060, by rfl⟩ : syracuseStep 6002747 = 9004121) B9004121
theorem B10131551 : Blo 1778090 10131551 := bstep (se 1 (by rfl) ⟨7598663, by rfl⟩ : syracuseStep 10131551 = 15197327) B15197327
theorem B4003937 : Blo 1778090 4003937 := bstep (se 2 (by rfl) ⟨1501476, by rfl⟩ : syracuseStep 4003937 = 3002953) B3002953
theorem B5068943 : Blo 1778090 5068943 := bstep (se 1 (by rfl) ⟨3801707, by rfl⟩ : syracuseStep 5068943 = 7603415) B7603415
theorem B2668841 : Blo 1778090 2668841 := bstep (se 2 (by rfl) ⟨1000815, by rfl⟩ : syracuseStep 2668841 = 2001631) B2001631
theorem B2668847 : Blo 1778090 2668847 := bstep (se 1 (by rfl) ⟨2001635, by rfl⟩ : syracuseStep 2668847 = 4003271) B4003271
theorem B6003017 : Blo 1778090 6003017 := bstep (se 2 (by rfl) ⟨2251131, by rfl⟩ : syracuseStep 6003017 = 4502263) B4502263
theorem B7600493 : Blo 1778090 7600493 := bstep (se 3 (by rfl) ⟨1425092, by rfl⟩ : syracuseStep 7600493 = 2850185) B2850185
theorem B6756797 : Blo 1778090 6756797 := bstep (se 3 (by rfl) ⟨1266899, by rfl⟩ : syracuseStep 6756797 = 2533799) B2533799
theorem B2669087 : Blo 1778090 2669087 := bstep (se 1 (by rfl) ⟨2001815, by rfl⟩ : syracuseStep 2669087 = 4003631) B4003631
theorem B38451971 : Blo 1778090 38451971 := bstep (se 1 (by rfl) ⟨28838978, by rfl⟩ : syracuseStep 38451971 = 57677957) B57677957
theorem B2849627 : Blo 1778090 2849627 := bstep (se 1 (by rfl) ⟨2137220, by rfl⟩ : syracuseStep 2849627 = 4274441) B4274441
theorem B2669471 : Blo 1778090 2669471 := bstep (se 1 (by rfl) ⟨2002103, by rfl⟩ : syracuseStep 2669471 = 4004207) B4004207
theorem B2669519 : Blo 1778090 2669519 := bstep (se 1 (by rfl) ⟨2002139, by rfl⟩ : syracuseStep 2669519 = 4004279) B4004279
theorem B2669609 : Blo 1778090 2669609 := bstep (se 2 (by rfl) ⟨1001103, by rfl⟩ : syracuseStep 2669609 = 2002207) B2002207
theorem B2669615 : Blo 1778090 2669615 := bstep (se 1 (by rfl) ⟨2002211, by rfl⟩ : syracuseStep 2669615 = 4004423) B4004423
theorem B3800135 : Blo 1778090 3800135 := bstep (se 1 (by rfl) ⟨2850101, by rfl⟩ : syracuseStep 3800135 = 5700203) B5700203
theorem B2669639 : Blo 1778090 2669639 := bstep (se 1 (by rfl) ⟨2002229, by rfl⟩ : syracuseStep 2669639 = 4004459) B4004459
theorem B77995253 : Blo 1778090 77995253 := bstep (se 5 (by rfl) ⟨3656027, by rfl⟩ : syracuseStep 77995253 = 7312055) B7312055
theorem B6847753 : Blo 1778090 6847753 := bstep (se 2 (by rfl) ⟨2567907, by rfl⟩ : syracuseStep 6847753 = 5135815) B5135815
theorem B2137423 : Blo 1778090 2137423 := bstep (se 1 (by rfl) ⟨1603067, by rfl⟩ : syracuseStep 2137423 = 3206135) B3206135
theorem B2669903 : Blo 1778090 2669903 := bstep (se 1 (by rfl) ⟨2002427, by rfl⟩ : syracuseStep 2669903 = 4004855) B4004855
theorem B2669993 : Blo 1778090 2669993 := bstep (se 2 (by rfl) ⟨1001247, by rfl⟩ : syracuseStep 2669993 = 2002495) B2002495
theorem B4505179 : Blo 1778090 4505179 := bstep (se 1 (by rfl) ⟨3378884, by rfl⟩ : syracuseStep 4505179 = 6757769) B6757769
theorem B6004367 : Blo 1778090 6004367 := bstep (se 1 (by rfl) ⟨4503275, by rfl⟩ : syracuseStep 6004367 = 9006551) B9006551
theorem B3800801 : Blo 1778090 3800801 := bstep (se 2 (by rfl) ⟨1425300, by rfl⟩ : syracuseStep 3800801 = 2850601) B2850601
theorem B9617129 : Blo 1778090 9617129 := bstep (se 2 (by rfl) ⟨3606423, by rfl⟩ : syracuseStep 9617129 = 7212847) B7212847
theorem B4505321 : Blo 1778090 4505321 := bstep (se 2 (by rfl) ⟨1689495, by rfl⟩ : syracuseStep 4505321 = 3378991) B3378991
theorem B20274947 : Blo 1778090 20274947 := bstep (se 1 (by rfl) ⟨15206210, by rfl⟩ : syracuseStep 20274947 = 30412421) B30412421
theorem B34668299 : Blo 1778090 34668299 := bstep (se 1 (by rfl) ⟨26001224, by rfl⟩ : syracuseStep 34668299 = 52002449) B52002449
theorem B5701499 : Blo 1778090 5701499 := bstep (se 1 (by rfl) ⟨4276124, by rfl⟩ : syracuseStep 5701499 = 8552249) B8552249
theorem B4808573 : Blo 1778090 4808573 := bstep (se 3 (by rfl) ⟨901607, by rfl⟩ : syracuseStep 4808573 = 1803215) B1803215
theorem B2252767 : Blo 1778090 2252767 := bstep (se 1 (by rfl) ⟨1689575, by rfl⟩ : syracuseStep 2252767 = 3379151) B3379151
theorem B10133693 : Blo 1778090 10133693 := bstep (se 3 (by rfl) ⟨1900067, by rfl⟩ : syracuseStep 10133693 = 3800135) B3800135
theorem B1900751 : Blo 1778090 1900751 := bstep (se 1 (by rfl) ⟨1425563, by rfl⟩ : syracuseStep 1900751 = 2851127) B2851127
theorem B6758711 : Blo 1778090 6758711 := bstep (se 1 (by rfl) ⟨5069033, by rfl⟩ : syracuseStep 6758711 = 10138067) B10138067
theorem B1778203 : Blo 1778090 1778203 := bstep (se 1 (by rfl) ⟨1333652, by rfl⟩ : syracuseStep 1778203 = 2667305) B2667305
theorem B1778207 : Blo 1778090 1778207 := bstep (se 1 (by rfl) ⟨1333655, by rfl⟩ : syracuseStep 1778207 = 2667311) B2667311
theorem B1778287 : Blo 1778090 1778287 := bstep (se 1 (by rfl) ⟨1333715, by rfl⟩ : syracuseStep 1778287 = 2667431) B2667431
theorem B1778343 : Blo 1778090 1778343 := bstep (se 1 (by rfl) ⟨1333757, by rfl⟩ : syracuseStep 1778343 = 2667515) B2667515
theorem B1778383 : Blo 1778090 1778383 := bstep (se 1 (by rfl) ⟨1333787, by rfl⟩ : syracuseStep 1778383 = 2667575) B2667575
theorem B15205117 : Blo 1778090 15205117 := bstep (se 3 (by rfl) ⟨2850959, by rfl⟩ : syracuseStep 15205117 = 5701919) B5701919
theorem B1778463 : Blo 1778090 1778463 := bstep (se 1 (by rfl) ⟨1333847, by rfl⟩ : syracuseStep 1778463 = 2667695) B2667695
theorem B1778735 : Blo 1778090 1778735 := bstep (se 1 (by rfl) ⟨1334051, by rfl⟩ : syracuseStep 1778735 = 2668103) B2668103
theorem B17089613 : Blo 1778090 17089613 := bstep (se 3 (by rfl) ⟨3204302, by rfl⟩ : syracuseStep 17089613 = 6408605) B6408605
theorem B3376235 : Blo 1778090 3376235 := bstep (se 1 (by rfl) ⟨2532176, by rfl⟩ : syracuseStep 3376235 = 5064353) B5064353
theorem B1778799 : Blo 1778090 1778799 := bstep (se 1 (by rfl) ⟨1334099, by rfl⟩ : syracuseStep 1778799 = 2668199) B2668199
theorem B1778855 : Blo 1778090 1778855 := bstep (se 1 (by rfl) ⟨1334141, by rfl⟩ : syracuseStep 1778855 = 2668283) B2668283
theorem B6751421 : Blo 1778090 6751421 := bstep (se 3 (by rfl) ⟨1265891, by rfl⟩ : syracuseStep 6751421 = 2531783) B2531783
theorem B1778879 : Blo 1778090 1778879 := bstep (se 1 (by rfl) ⟨1334159, by rfl⟩ : syracuseStep 1778879 = 2668319) B2668319
theorem B1778911 : Blo 1778090 1778911 := bstep (se 1 (by rfl) ⟨1334183, by rfl⟩ : syracuseStep 1778911 = 2668367) B2668367
theorem B1778991 : Blo 1778090 1778991 := bstep (se 1 (by rfl) ⟨1334243, by rfl⟩ : syracuseStep 1778991 = 2668487) B2668487
theorem B15197705 : Blo 1778090 15197705 := bstep (se 2 (by rfl) ⟨5699139, by rfl⟩ : syracuseStep 15197705 = 11398279) B11398279
theorem B1779227 : Blo 1778090 1779227 := bstep (se 1 (by rfl) ⟨1334420, by rfl⟩ : syracuseStep 1779227 = 2668841) B2668841
theorem B1779231 : Blo 1778090 1779231 := bstep (se 1 (by rfl) ⟨1334423, by rfl⟩ : syracuseStep 1779231 = 2668847) B2668847
theorem B15206075 : Blo 1778090 15206075 := bstep (se 1 (by rfl) ⟨11404556, by rfl⟩ : syracuseStep 15206075 = 22809113) B22809113
theorem B1779391 : Blo 1778090 1779391 := bstep (se 1 (by rfl) ⟨1334543, by rfl⟩ : syracuseStep 1779391 = 2669087) B2669087
theorem B25634647 : Blo 1778090 25634647 := bstep (se 1 (by rfl) ⟨19225985, by rfl⟩ : syracuseStep 25634647 = 38451971) B38451971
theorem B14452577 : Blo 1778090 14452577 := bstep (se 2 (by rfl) ⟨5419716, by rfl⟩ : syracuseStep 14452577 = 10839433) B10839433
theorem B5064569 : Blo 1778090 5064569 := bstep (se 2 (by rfl) ⟨1899213, by rfl⟩ : syracuseStep 5064569 = 3798427) B3798427
theorem B10135469 : Blo 1778090 10135469 := bstep (se 3 (by rfl) ⟨1900400, by rfl⟩ : syracuseStep 10135469 = 3800801) B3800801
theorem B1779647 : Blo 1778090 1779647 := bstep (se 1 (by rfl) ⟨1334735, by rfl⟩ : syracuseStep 1779647 = 2669471) B2669471
theorem B1779679 : Blo 1778090 1779679 := bstep (se 1 (by rfl) ⟨1334759, by rfl⟩ : syracuseStep 1779679 = 2669519) B2669519
theorem B1779739 : Blo 1778090 1779739 := bstep (se 1 (by rfl) ⟨1334804, by rfl⟩ : syracuseStep 1779739 = 2669609) B2669609
theorem B1779743 : Blo 1778090 1779743 := bstep (se 1 (by rfl) ⟨1334807, by rfl⟩ : syracuseStep 1779743 = 2669615) B2669615
theorem B1779759 : Blo 1778090 1779759 := bstep (se 1 (by rfl) ⟨1334819, by rfl⟩ : syracuseStep 1779759 = 2669639) B2669639
theorem B6006905 : Blo 1778090 6006905 := bstep (se 2 (by rfl) ⟨2252589, by rfl⟩ : syracuseStep 6006905 = 4505179) B4505179
theorem B16222369 : Blo 1778090 16222369 := bstep (se 2 (by rfl) ⟨6083388, by rfl⟩ : syracuseStep 16222369 = 12166777) B12166777
theorem B51996835 : Blo 1778090 51996835 := bstep (se 1 (by rfl) ⟨38997626, by rfl⟩ : syracuseStep 51996835 = 77995253) B77995253
theorem B1779935 : Blo 1778090 1779935 := bstep (se 1 (by rfl) ⟨1334951, by rfl⟩ : syracuseStep 1779935 = 2669903) B2669903
theorem B1779995 : Blo 1778090 1779995 := bstep (se 1 (by rfl) ⟨1334996, by rfl⟩ : syracuseStep 1779995 = 2669993) B2669993
theorem B34212131 : Blo 1778090 34212131 := bstep (se 1 (by rfl) ⟨25659098, by rfl⟩ : syracuseStep 34212131 = 51318197) B51318197
theorem B23112199 : Blo 1778090 23112199 := bstep (se 1 (by rfl) ⟨17334149, by rfl⟩ : syracuseStep 23112199 = 34668299) B34668299
theorem B18508313 : Blo 1778090 18508313 := bstep (se 2 (by rfl) ⟨6940617, by rfl⟩ : syracuseStep 18508313 = 13881235) B13881235
theorem B3205715 : Blo 1778090 3205715 := bstep (se 1 (by rfl) ⟨2404286, by rfl⟩ : syracuseStep 3205715 = 4808573) B4808573
theorem B3000935 : Blo 1778090 3000935 := bstep (se 1 (by rfl) ⟨2250701, by rfl⟩ : syracuseStep 3000935 = 4501403) B4501403
theorem B5409575 : Blo 1778090 5409575 := bstep (se 1 (by rfl) ⟨4057181, by rfl⟩ : syracuseStep 5409575 = 8114363) B8114363
theorem B2001703 : Blo 1778090 2001703 := bstep (se 1 (by rfl) ⟨1501277, by rfl⟩ : syracuseStep 2001703 = 3002555) B3002555
theorem B12995471 : Blo 1778090 12995471 := bstep (se 1 (by rfl) ⟨9746603, by rfl⟩ : syracuseStep 12995471 = 19493207) B19493207
theorem B10136609 : Blo 1778090 10136609 := bstep (se 2 (by rfl) ⟨3801228, by rfl⟩ : syracuseStep 10136609 = 7602457) B7602457
theorem B4000823 : Blo 1778090 4000823 := bstep (se 1 (by rfl) ⟨3000617, by rfl⟩ : syracuseStep 4000823 = 6001235) B6001235
theorem B4058183 : Blo 1778090 4058183 := bstep (se 1 (by rfl) ⟨3043637, by rfl⟩ : syracuseStep 4058183 = 6087275) B6087275
theorem B3001691 : Blo 1778090 3001691 := bstep (se 1 (by rfl) ⟨2251268, by rfl⟩ : syracuseStep 3001691 = 4502537) B4502537
theorem B4001255 : Blo 1778090 4001255 := bstep (se 1 (by rfl) ⟨3000941, by rfl⟩ : syracuseStep 4001255 = 6001883) B6001883
theorem B207867653 : Blo 1778090 207867653 := bstep (se 4 (by rfl) ⟨19487592, by rfl⟩ : syracuseStep 207867653 = 38975185) B38975185
theorem B3379067 : Blo 1778090 3379067 := bstep (se 1 (by rfl) ⟨2534300, by rfl⟩ : syracuseStep 3379067 = 5068601) B5068601
theorem B16224263 : Blo 1778090 16224263 := bstep (se 1 (by rfl) ⟨12168197, by rfl⟩ : syracuseStep 16224263 = 24336395) B24336395
theorem B4001831 : Blo 1778090 4001831 := bstep (se 1 (by rfl) ⟨3001373, by rfl⟩ : syracuseStep 4001831 = 6002747) B6002747
theorem B6754367 : Blo 1778090 6754367 := bstep (se 1 (by rfl) ⟨5065775, by rfl⟩ : syracuseStep 6754367 = 10131551) B10131551
theorem B3379295 : Blo 1778090 3379295 := bstep (se 1 (by rfl) ⟨2534471, by rfl⟩ : syracuseStep 3379295 = 5068943) B5068943
theorem B4002011 : Blo 1778090 4002011 := bstep (se 1 (by rfl) ⟨3001508, by rfl⟩ : syracuseStep 4002011 = 6003017) B6003017
theorem B5066995 : Blo 1778090 5066995 := bstep (se 1 (by rfl) ⟨3800246, by rfl⟩ : syracuseStep 5066995 = 7600493) B7600493
theorem B9130337 : Blo 1778090 9130337 := bstep (se 2 (by rfl) ⟨3423876, by rfl⟩ : syracuseStep 9130337 = 6847753) B6847753
theorem B4002281 : Blo 1778090 4002281 := bstep (se 2 (by rfl) ⟨1500855, by rfl⟩ : syracuseStep 4002281 = 3001711) B3001711
theorem B2667401 : Blo 1778090 2667401 := bstep (se 2 (by rfl) ⟨1000275, by rfl⟩ : syracuseStep 2667401 = 2000551) B2000551
theorem B7599005 : Blo 1778090 7599005 := bstep (se 3 (by rfl) ⟨1424813, by rfl⟩ : syracuseStep 7599005 = 2849627) B2849627
theorem B13505453 : Blo 1778090 13505453 := bstep (se 3 (by rfl) ⟨2532272, by rfl⟩ : syracuseStep 13505453 = 5064545) B5064545
theorem B4002785 : Blo 1778090 4002785 := bstep (se 2 (by rfl) ⟨1501044, by rfl⟩ : syracuseStep 4002785 = 3002089) B3002089
theorem B4002911 : Blo 1778090 4002911 := bstep (se 1 (by rfl) ⟨3002183, by rfl⟩ : syracuseStep 4002911 = 6004367) B6004367
theorem B6411419 : Blo 1778090 6411419 := bstep (se 1 (by rfl) ⟨4808564, by rfl⟩ : syracuseStep 6411419 = 9617129) B9617129
theorem B3003547 : Blo 1778090 3003547 := bstep (se 1 (by rfl) ⟨2252660, by rfl⟩ : syracuseStep 3003547 = 4505321) B4505321
theorem B2667785 : Blo 1778090 2667785 := bstep (se 2 (by rfl) ⟨1000419, by rfl⟩ : syracuseStep 2667785 = 2000839) B2000839
theorem B3003689 : Blo 1778090 3003689 := bstep (se 2 (by rfl) ⟨1126383, by rfl⟩ : syracuseStep 3003689 = 2252767) B2252767
theorem B2667839 : Blo 1778090 2667839 := bstep (se 1 (by rfl) ⟨2000879, by rfl⟩ : syracuseStep 2667839 = 4001759) B4001759
theorem B25654603 : Blo 1778090 25654603 := bstep (se 1 (by rfl) ⟨19240952, by rfl⟩ : syracuseStep 25654603 = 38481905) B38481905
theorem B7706011 : Blo 1778090 7706011 := bstep (se 1 (by rfl) ⟨5779508, by rfl⟩ : syracuseStep 7706011 = 11559017) B11559017
theorem B8549803 : Blo 1778090 8549803 := bstep (se 1 (by rfl) ⟨6412352, by rfl⟩ : syracuseStep 8549803 = 12824705) B12824705
theorem B5068271 : Blo 1778090 5068271 := bstep (se 1 (by rfl) ⟨3801203, by rfl⟩ : syracuseStep 5068271 = 7602407) B7602407
theorem B115455557 : Blo 1778090 115455557 := bstep (se 4 (by rfl) ⟨10823958, by rfl⟩ : syracuseStep 115455557 = 21647917) B21647917
theorem B3798751 : Blo 1778090 3798751 := bstep (se 1 (by rfl) ⟨2849063, by rfl⟩ : syracuseStep 3798751 = 5698127) B5698127
theorem B2668265 : Blo 1778090 2668265 := bstep (se 2 (by rfl) ⟨1000599, by rfl⟩ : syracuseStep 2668265 = 2001199) B2001199
theorem B2668271 : Blo 1778090 2668271 := bstep (se 1 (by rfl) ⟨2001203, by rfl⟩ : syracuseStep 2668271 = 4002407) B4002407
theorem B4003667 : Blo 1778090 4003667 := bstep (se 1 (by rfl) ⟨3002750, by rfl⟩ : syracuseStep 4003667 = 6005501) B6005501
theorem B2668727 : Blo 1778090 2668727 := bstep (se 1 (by rfl) ⟨2001545, by rfl⟩ : syracuseStep 2668727 = 4003091) B4003091
theorem B5699767 : Blo 1778090 5699767 := bstep (se 1 (by rfl) ⟨4274825, by rfl⟩ : syracuseStep 5699767 = 8549651) B8549651
theorem B2668775 : Blo 1778090 2668775 := bstep (se 1 (by rfl) ⟨2001581, by rfl⟩ : syracuseStep 2668775 = 4003163) B4003163
theorem B30390551 : Blo 1778090 30390551 := bstep (se 1 (by rfl) ⟨22792913, by rfl⟩ : syracuseStep 30390551 = 45585827) B45585827
theorem B4004153 : Blo 1778090 4004153 := bstep (se 2 (by rfl) ⟨1501557, by rfl⟩ : syracuseStep 4004153 = 3003115) B3003115
theorem B17094995 : Blo 1778090 17094995 := bstep (se 1 (by rfl) ⟨12821246, by rfl⟩ : syracuseStep 17094995 = 25642493) B25642493
theorem B7215455 : Blo 1778090 7215455 := bstep (se 1 (by rfl) ⟨5411591, by rfl⟩ : syracuseStep 7215455 = 10823183) B10823183
theorem B29235599 : Blo 1778090 29235599 := bstep (se 1 (by rfl) ⟨21926699, by rfl⟩ : syracuseStep 29235599 = 43853399) B43853399
theorem B2849231 : Blo 1778090 2849231 := bstep (se 1 (by rfl) ⟨2136923, by rfl⟩ : syracuseStep 2849231 = 4273847) B4273847
theorem B2669147 : Blo 1778090 2669147 := bstep (se 1 (by rfl) ⟨2001860, by rfl⟩ : syracuseStep 2669147 = 4003721) B4003721
theorem B23419489 : Blo 1778090 23419489 := bstep (se 2 (by rfl) ⟨8782308, by rfl⟩ : syracuseStep 23419489 = 17564617) B17564617
theorem B4504207 : Blo 1778090 4504207 := bstep (se 1 (by rfl) ⟨3378155, by rfl⟩ : syracuseStep 4504207 = 6756311) B6756311
theorem B2669291 : Blo 1778090 2669291 := bstep (se 1 (by rfl) ⟨2001968, by rfl⟩ : syracuseStep 2669291 = 4003937) B4003937
theorem B28842749 : Blo 1778090 28842749 := bstep (se 3 (by rfl) ⟨5408015, by rfl⟩ : syracuseStep 28842749 = 10816031) B10816031
theorem B2669321 : Blo 1778090 2669321 := bstep (se 2 (by rfl) ⟨1000995, by rfl⟩ : syracuseStep 2669321 = 2001991) B2001991
theorem B10132235 : Blo 1778090 10132235 := bstep (se 1 (by rfl) ⟨7599176, by rfl⟩ : syracuseStep 10132235 = 15198353) B15198353
theorem B4504531 : Blo 1778090 4504531 := bstep (se 1 (by rfl) ⟨3378398, by rfl⟩ : syracuseStep 4504531 = 6756797) B6756797
theorem B6413275 : Blo 1778090 6413275 := bstep (se 1 (by rfl) ⟨4809956, by rfl⟩ : syracuseStep 6413275 = 9619913) B9619913
theorem B2849897 : Blo 1778090 2849897 := bstep (se 2 (by rfl) ⟨1068711, by rfl⟩ : syracuseStep 2849897 = 2137423) B2137423
theorem B4005071 : Blo 1778090 4005071 := bstep (se 1 (by rfl) ⟨3003803, by rfl⟩ : syracuseStep 4005071 = 6007607) B6007607
theorem B13507883 : Blo 1778090 13507883 := bstep (se 1 (by rfl) ⟨10130912, by rfl⟩ : syracuseStep 13507883 = 20261825) B20261825
theorem B7314731 : Blo 1778090 7314731 := bstep (se 1 (by rfl) ⟨5486048, by rfl⟩ : syracuseStep 7314731 = 10972097) B10972097
theorem B57720397 : Blo 1778090 57720397 := bstep (se 3 (by rfl) ⟨10822574, by rfl⟩ : syracuseStep 57720397 = 21645149) B21645149
theorem B9002663 : Blo 1778090 9002663 := bstep (se 1 (by rfl) ⟨6751997, by rfl⟩ : syracuseStep 9002663 = 13503995) B13503995
theorem B32448235 : Blo 1778090 32448235 := bstep (se 1 (by rfl) ⟨24336176, by rfl⟩ : syracuseStep 32448235 = 48672353) B48672353
theorem B13516631 : Blo 1778090 13516631 := bstep (se 1 (by rfl) ⟨10137473, by rfl⟩ : syracuseStep 13516631 = 20274947) B20274947
theorem B22789997 : Blo 1778090 22789997 := bstep (se 3 (by rfl) ⟨4273124, by rfl⟩ : syracuseStep 22789997 = 8546249) B8546249
theorem B3800999 : Blo 1778090 3800999 := bstep (se 1 (by rfl) ⟨2850749, by rfl⟩ : syracuseStep 3800999 = 5701499) B5701499
theorem B123265061 : Blo 1778090 123265061 := bstep (se 4 (by rfl) ⟨11556099, by rfl⟩ : syracuseStep 123265061 = 23112199) B23112199
theorem B2252863 : Blo 1778090 2252863 := bstep (se 1 (by rfl) ⟨1689647, by rfl⟩ : syracuseStep 2252863 = 3379295) B3379295
theorem B4505807 : Blo 1778090 4505807 := bstep (se 1 (by rfl) ⟨3379355, by rfl⟩ : syracuseStep 4505807 = 6758711) B6758711
theorem B6086891 : Blo 1778090 6086891 := bstep (se 1 (by rfl) ⟨4565168, by rfl⟩ : syracuseStep 6086891 = 9130337) B9130337
theorem B1778267 : Blo 1778090 1778267 := bstep (se 1 (by rfl) ⟨1333700, by rfl⟩ : syracuseStep 1778267 = 2667401) B2667401
theorem B9003635 : Blo 1778090 9003635 := bstep (se 1 (by rfl) ⟨6752726, by rfl⟩ : syracuseStep 9003635 = 13505453) B13505453
theorem B1778523 : Blo 1778090 1778523 := bstep (se 1 (by rfl) ⟨1333892, by rfl⟩ : syracuseStep 1778523 = 2667785) B2667785
theorem B277316453 : Blo 1778090 277316453 := bstep (se 4 (by rfl) ⟨25998417, by rfl⟩ : syracuseStep 277316453 = 51996835) B51996835
theorem B6005609 : Blo 1778090 6005609 := bstep (se 2 (by rfl) ⟨2252103, by rfl⟩ : syracuseStep 6005609 = 4504207) B4504207
theorem B1778559 : Blo 1778090 1778559 := bstep (se 1 (by rfl) ⟨1333919, by rfl⟩ : syracuseStep 1778559 = 2667839) B2667839
theorem B1778843 : Blo 1778090 1778843 := bstep (se 1 (by rfl) ⟨1334132, by rfl⟩ : syracuseStep 1778843 = 2668265) B2668265
theorem B1778847 : Blo 1778090 1778847 := bstep (se 1 (by rfl) ⟨1334135, by rfl⟩ : syracuseStep 1778847 = 2668271) B2668271
theorem B9635051 : Blo 1778090 9635051 := bstep (se 1 (by rfl) ⟨7226288, by rfl⟩ : syracuseStep 9635051 = 14452577) B14452577
theorem B3376379 : Blo 1778090 3376379 := bstep (se 1 (by rfl) ⟨2532284, by rfl⟩ : syracuseStep 3376379 = 5064569) B5064569
theorem B6006041 : Blo 1778090 6006041 := bstep (se 2 (by rfl) ⟨2252265, by rfl⟩ : syracuseStep 6006041 = 4504531) B4504531
theorem B1779151 : Blo 1778090 1779151 := bstep (se 1 (by rfl) ⟨1334363, by rfl⟩ : syracuseStep 1779151 = 2668727) B2668727
theorem B1779183 : Blo 1778090 1779183 := bstep (se 1 (by rfl) ⟨1334387, by rfl⟩ : syracuseStep 1779183 = 2668775) B2668775
theorem B20260367 : Blo 1778090 20260367 := bstep (se 1 (by rfl) ⟨15195275, by rfl⟩ : syracuseStep 20260367 = 30390551) B30390551
theorem B22808087 : Blo 1778090 22808087 := bstep (se 1 (by rfl) ⟨17106065, by rfl⟩ : syracuseStep 22808087 = 34212131) B34212131
theorem B11396663 : Blo 1778090 11396663 := bstep (se 1 (by rfl) ⟨8547497, by rfl⟩ : syracuseStep 11396663 = 17094995) B17094995
theorem B4810303 : Blo 1778090 4810303 := bstep (se 1 (by rfl) ⟨3607727, by rfl⟩ : syracuseStep 4810303 = 7215455) B7215455
theorem B19490399 : Blo 1778090 19490399 := bstep (se 1 (by rfl) ⟨14617799, by rfl⟩ : syracuseStep 19490399 = 29235599) B29235599
theorem B12338875 : Blo 1778090 12338875 := bstep (se 1 (by rfl) ⟨9254156, by rfl⟩ : syracuseStep 12338875 = 18508313) B18508313
theorem B1779431 : Blo 1778090 1779431 := bstep (se 1 (by rfl) ⟨1334573, by rfl⟩ : syracuseStep 1779431 = 2669147) B2669147
theorem B2000623 : Blo 1778090 2000623 := bstep (se 1 (by rfl) ⟨1500467, by rfl⟩ : syracuseStep 2000623 = 3000935) B3000935
theorem B1779527 : Blo 1778090 1779527 := bstep (se 1 (by rfl) ⟨1334645, by rfl⟩ : syracuseStep 1779527 = 2669291) B2669291
theorem B19228499 : Blo 1778090 19228499 := bstep (se 1 (by rfl) ⟨14421374, by rfl⟩ : syracuseStep 19228499 = 28842749) B28842749
theorem B1779547 : Blo 1778090 1779547 := bstep (se 1 (by rfl) ⟨1334660, by rfl⟩ : syracuseStep 1779547 = 2669321) B2669321
theorem B3606383 : Blo 1778090 3606383 := bstep (se 1 (by rfl) ⟨2704787, by rfl⟩ : syracuseStep 3606383 = 5409575) B5409575
theorem B10274681 : Blo 1778090 10274681 := bstep (se 2 (by rfl) ⟨3853005, by rfl⟩ : syracuseStep 10274681 = 7706011) B7706011
theorem B2705455 : Blo 1778090 2705455 := bstep (se 1 (by rfl) ⟨2029091, by rfl⟩ : syracuseStep 2705455 = 4058183) B4058183
theorem B9005255 : Blo 1778090 9005255 := bstep (se 1 (by rfl) ⟨6753941, by rfl⟩ : syracuseStep 9005255 = 13507883) B13507883
theorem B4876487 : Blo 1778090 4876487 := bstep (se 1 (by rfl) ⟨3657365, by rfl⟩ : syracuseStep 4876487 = 7314731) B7314731
theorem B45598949 : Blo 1778090 45598949 := bstep (se 4 (by rfl) ⟨4274901, by rfl⟩ : syracuseStep 45598949 = 8549803) B8549803
theorem B2001127 : Blo 1778090 2001127 := bstep (se 1 (by rfl) ⟨1500845, by rfl⟩ : syracuseStep 2001127 = 3001691) B3001691
theorem B5065001 : Blo 1778090 5065001 := bstep (se 2 (by rfl) ⟨1899375, by rfl⟩ : syracuseStep 5065001 = 3798751) B3798751
theorem B43264313 : Blo 1778090 43264313 := bstep (se 2 (by rfl) ⟨16224117, by rfl⟩ : syracuseStep 43264313 = 32448235) B32448235
theorem B34179529 : Blo 1778090 34179529 := bstep (se 2 (by rfl) ⟨12817323, by rfl⟩ : syracuseStep 34179529 = 25634647) B25634647
theorem B34204133 : Blo 1778090 34204133 := bstep (se 4 (by rfl) ⟨3206637, by rfl⟩ : syracuseStep 34204133 = 6413275) B6413275
theorem B138578435 : Blo 1778090 138578435 := bstep (se 1 (by rfl) ⟨103933826, by rfl⟩ : syracuseStep 138578435 = 207867653) B207867653
theorem B2533999 : Blo 1778090 2533999 := bstep (se 1 (by rfl) ⟨1900499, by rfl⟩ : syracuseStep 2533999 = 3800999) B3800999
theorem B10816175 : Blo 1778090 10816175 := bstep (se 1 (by rfl) ⟨8112131, by rfl⟩ : syracuseStep 10816175 = 16224263) B16224263
theorem B21629825 : Blo 1778090 21629825 := bstep (se 2 (by rfl) ⟨8111184, by rfl⟩ : syracuseStep 21629825 = 16222369) B16222369
theorem B5066003 : Blo 1778090 5066003 := bstep (se 1 (by rfl) ⟨3799502, by rfl⟩ : syracuseStep 5066003 = 7599005) B7599005
theorem B4500947 : Blo 1778090 4500947 := bstep (se 1 (by rfl) ⟨3375710, by rfl⟩ : syracuseStep 4500947 = 6751421) B6751421
theorem B2002459 : Blo 1778090 2002459 := bstep (se 1 (by rfl) ⟨1501844, by rfl⟩ : syracuseStep 2002459 = 3003689) B3003689
theorem B3378847 : Blo 1778090 3378847 := bstep (se 1 (by rfl) ⟨2534135, by rfl⟩ : syracuseStep 3378847 = 5068271) B5068271
theorem B10137383 : Blo 1778090 10137383 := bstep (se 1 (by rfl) ⟨7603037, by rfl⟩ : syracuseStep 10137383 = 15206075) B15206075
theorem B8548573 : Blo 1778090 8548573 := bstep (se 3 (by rfl) ⟨1602857, by rfl⟩ : syracuseStep 8548573 = 3205715) B3205715
theorem B34206137 : Blo 1778090 34206137 := bstep (se 2 (by rfl) ⟨12827301, by rfl⟩ : syracuseStep 34206137 = 25654603) B25654603
theorem B6754823 : Blo 1778090 6754823 := bstep (se 1 (by rfl) ⟨5066117, by rfl⟩ : syracuseStep 6754823 = 10132235) B10132235
theorem B8663647 : Blo 1778090 8663647 := bstep (se 1 (by rfl) ⟨6497735, by rfl⟩ : syracuseStep 8663647 = 12995471) B12995471
theorem B2667215 : Blo 1778090 2667215 := bstep (se 1 (by rfl) ⟨2000411, by rfl⟩ : syracuseStep 2667215 = 4000823) B4000823
theorem B76960529 : Blo 1778090 76960529 := bstep (se 2 (by rfl) ⟨28860198, by rfl⟩ : syracuseStep 76960529 = 57720397) B57720397
theorem B2667503 : Blo 1778090 2667503 := bstep (se 1 (by rfl) ⟨2000627, by rfl⟩ : syracuseStep 2667503 = 4001255) B4001255
theorem B6001775 : Blo 1778090 6001775 := bstep (se 1 (by rfl) ⟨4501331, by rfl⟩ : syracuseStep 6001775 = 9002663) B9002663
theorem B15193331 : Blo 1778090 15193331 := bstep (se 1 (by rfl) ⟨11394998, by rfl⟩ : syracuseStep 15193331 = 22789997) B22789997
theorem B2667887 : Blo 1778090 2667887 := bstep (se 1 (by rfl) ⟨2000915, by rfl⟩ : syracuseStep 2667887 = 4001831) B4001831
theorem B4502911 : Blo 1778090 4502911 := bstep (se 1 (by rfl) ⟨3377183, by rfl⟩ : syracuseStep 4502911 = 6754367) B6754367
theorem B6755795 : Blo 1778090 6755795 := bstep (se 1 (by rfl) ⟨5066846, by rfl⟩ : syracuseStep 6755795 = 10133693) B10133693
theorem B2668007 : Blo 1778090 2668007 := bstep (se 1 (by rfl) ⟨2001005, by rfl⟩ : syracuseStep 2668007 = 4002011) B4002011
theorem B7599689 : Blo 1778090 7599689 := bstep (se 2 (by rfl) ⟨2849883, by rfl⟩ : syracuseStep 7599689 = 5699767) B5699767
theorem B6755993 : Blo 1778090 6755993 := bstep (se 2 (by rfl) ⟨2533497, by rfl⟩ : syracuseStep 6755993 = 5066995) B5066995
theorem B2668187 : Blo 1778090 2668187 := bstep (se 1 (by rfl) ⟨2001140, by rfl⟩ : syracuseStep 2668187 = 4002281) B4002281
theorem B5068669 : Blo 1778090 5068669 := bstep (se 3 (by rfl) ⟨950375, by rfl⟩ : syracuseStep 5068669 = 1900751) B1900751
theorem B2668523 : Blo 1778090 2668523 := bstep (se 1 (by rfl) ⟨2001392, by rfl⟩ : syracuseStep 2668523 = 4002785) B4002785
theorem B11393075 : Blo 1778090 11393075 := bstep (se 1 (by rfl) ⟨8544806, by rfl⟩ : syracuseStep 11393075 = 17089613) B17089613
theorem B2668607 : Blo 1778090 2668607 := bstep (se 1 (by rfl) ⟨2001455, by rfl⟩ : syracuseStep 2668607 = 4002911) B4002911
theorem B2250823 : Blo 1778090 2250823 := bstep (se 1 (by rfl) ⟨1688117, by rfl⟩ : syracuseStep 2250823 = 3376235) B3376235
theorem B4274279 : Blo 1778090 4274279 := bstep (se 1 (by rfl) ⟨3205709, by rfl⟩ : syracuseStep 4274279 = 6411419) B6411419
theorem B31225985 : Blo 1778090 31225985 := bstep (se 2 (by rfl) ⟨11709744, by rfl⟩ : syracuseStep 31225985 = 23419489) B23419489
theorem B20273489 : Blo 1778090 20273489 := bstep (se 2 (by rfl) ⟨7602558, by rfl⟩ : syracuseStep 20273489 = 15205117) B15205117
theorem B10131803 : Blo 1778090 10131803 := bstep (se 1 (by rfl) ⟨7598852, by rfl⟩ : syracuseStep 10131803 = 15197705) B15197705
theorem B76970371 : Blo 1778090 76970371 := bstep (se 1 (by rfl) ⟨57727778, by rfl⟩ : syracuseStep 76970371 = 115455557) B115455557
theorem B2668937 : Blo 1778090 2668937 := bstep (se 2 (by rfl) ⟨1000851, by rfl⟩ : syracuseStep 2668937 = 2001703) B2001703
theorem B2669111 : Blo 1778090 2669111 := bstep (se 1 (by rfl) ⟨2001833, by rfl⟩ : syracuseStep 2669111 = 4003667) B4003667
theorem B6756979 : Blo 1778090 6756979 := bstep (se 1 (by rfl) ⟨5067734, by rfl⟩ : syracuseStep 6756979 = 10135469) B10135469
theorem B4004603 : Blo 1778090 4004603 := bstep (se 1 (by rfl) ⟨3003452, by rfl⟩ : syracuseStep 4004603 = 6006905) B6006905
theorem B4004729 : Blo 1778090 4004729 := bstep (se 2 (by rfl) ⟨1501773, by rfl⟩ : syracuseStep 4004729 = 3003547) B3003547
theorem B2669435 : Blo 1778090 2669435 := bstep (se 1 (by rfl) ⟨2002076, by rfl⟩ : syracuseStep 2669435 = 4004153) B4004153
theorem B1899487 : Blo 1778090 1899487 := bstep (se 1 (by rfl) ⟨1424615, by rfl⟩ : syracuseStep 1899487 = 2849231) B2849231
theorem B6757739 : Blo 1778090 6757739 := bstep (se 1 (by rfl) ⟨5068304, by rfl⟩ : syracuseStep 6757739 = 10136609) B10136609
theorem B1899931 : Blo 1778090 1899931 := bstep (se 1 (by rfl) ⟨1424948, by rfl⟩ : syracuseStep 1899931 = 2849897) B2849897
theorem B2670047 : Blo 1778090 2670047 := bstep (se 1 (by rfl) ⟨2002535, by rfl⟩ : syracuseStep 2670047 = 4005071) B4005071
theorem B9011087 : Blo 1778090 9011087 := bstep (se 1 (by rfl) ⟨6758315, by rfl⟩ : syracuseStep 9011087 = 13516631) B13516631
theorem B2252711 : Blo 1778090 2252711 := bstep (se 1 (by rfl) ⟨1689533, by rfl⟩ : syracuseStep 2252711 = 3379067) B3379067
theorem B1778143 : Blo 1778090 1778143 := bstep (se 1 (by rfl) ⟨1333607, by rfl⟩ : syracuseStep 1778143 = 2667215) B2667215
theorem B51307019 : Blo 1778090 51307019 := bstep (se 1 (by rfl) ⟨38480264, by rfl⟩ : syracuseStep 51307019 = 76960529) B76960529
theorem B184877635 : Blo 1778090 184877635 := bstep (se 1 (by rfl) ⟨138658226, by rfl⟩ : syracuseStep 184877635 = 277316453) B277316453
theorem B45572705 : Blo 1778090 45572705 := bstep (se 2 (by rfl) ⟨17089764, by rfl⟩ : syracuseStep 45572705 = 34179529) B34179529
theorem B1778335 : Blo 1778090 1778335 := bstep (se 1 (by rfl) ⟨1333751, by rfl⟩ : syracuseStep 1778335 = 2667503) B2667503
theorem B13509341 : Blo 1778090 13509341 := bstep (se 3 (by rfl) ⟨2533001, by rfl⟩ : syracuseStep 13509341 = 5066003) B5066003
theorem B11551529 : Blo 1778090 11551529 := bstep (se 2 (by rfl) ⟨4331823, by rfl⟩ : syracuseStep 11551529 = 8663647) B8663647
theorem B1778591 : Blo 1778090 1778591 := bstep (se 1 (by rfl) ⟨1333943, by rfl⟩ : syracuseStep 1778591 = 2667887) B2667887
theorem B1778671 : Blo 1778090 1778671 := bstep (se 1 (by rfl) ⟨1334003, by rfl⟩ : syracuseStep 1778671 = 2668007) B2668007
theorem B15205391 : Blo 1778090 15205391 := bstep (se 1 (by rfl) ⟨11404043, by rfl⟩ : syracuseStep 15205391 = 22808087) B22808087
theorem B12993599 : Blo 1778090 12993599 := bstep (se 1 (by rfl) ⟨9745199, by rfl⟩ : syracuseStep 12993599 = 19490399) B19490399
theorem B1778791 : Blo 1778090 1778791 := bstep (se 1 (by rfl) ⟨1334093, by rfl⟩ : syracuseStep 1778791 = 2668187) B2668187
theorem B6849787 : Blo 1778090 6849787 := bstep (se 1 (by rfl) ⟨5137340, by rfl⟩ : syracuseStep 6849787 = 10274681) B10274681
theorem B2532649 : Blo 1778090 2532649 := bstep (se 2 (by rfl) ⟨949743, by rfl⟩ : syracuseStep 2532649 = 1899487) B1899487
theorem B1779015 : Blo 1778090 1779015 := bstep (se 1 (by rfl) ⟨1334261, by rfl⟩ : syracuseStep 1779015 = 2668523) B2668523
theorem B7595383 : Blo 1778090 7595383 := bstep (se 1 (by rfl) ⟨5696537, by rfl⟩ : syracuseStep 7595383 = 11393075) B11393075
theorem B1779071 : Blo 1778090 1779071 := bstep (se 1 (by rfl) ⟨1334303, by rfl⟩ : syracuseStep 1779071 = 2668607) B2668607
theorem B20817323 : Blo 1778090 20817323 := bstep (se 1 (by rfl) ⟨15612992, by rfl⟩ : syracuseStep 20817323 = 31225985) B31225985
theorem B3376667 : Blo 1778090 3376667 := bstep (se 1 (by rfl) ⟨2532500, by rfl⟩ : syracuseStep 3376667 = 5065001) B5065001
theorem B1779291 : Blo 1778090 1779291 := bstep (se 1 (by rfl) ⟨1334468, by rfl⟩ : syracuseStep 1779291 = 2668937) B2668937
theorem B1779407 : Blo 1778090 1779407 := bstep (se 1 (by rfl) ⟨1334555, by rfl⟩ : syracuseStep 1779407 = 2669111) B2669111
theorem B7210783 : Blo 1778090 7210783 := bstep (se 1 (by rfl) ⟨5408087, by rfl⟩ : syracuseStep 7210783 = 10816175) B10816175
theorem B2533241 : Blo 1778090 2533241 := bstep (se 2 (by rfl) ⟨949965, by rfl⟩ : syracuseStep 2533241 = 1899931) B1899931
theorem B1779623 : Blo 1778090 1779623 := bstep (se 1 (by rfl) ⟨1334717, by rfl⟩ : syracuseStep 1779623 = 2669435) B2669435
theorem B14419883 : Blo 1778090 14419883 := bstep (se 1 (by rfl) ⟨10814912, by rfl⟩ : syracuseStep 14419883 = 21629825) B21629825
theorem B16451833 : Blo 1778090 16451833 := bstep (se 2 (by rfl) ⟨6169437, by rfl⟩ : syracuseStep 16451833 = 12338875) B12338875
theorem B3000631 : Blo 1778090 3000631 := bstep (se 1 (by rfl) ⟨2250473, by rfl⟩ : syracuseStep 3000631 = 4500947) B4500947
theorem B1780031 : Blo 1778090 1780031 := bstep (se 1 (by rfl) ⟨1335023, by rfl⟩ : syracuseStep 1780031 = 2670047) B2670047
theorem B6007229 : Blo 1778090 6007229 := bstep (se 3 (by rfl) ⟨1126355, by rfl⟩ : syracuseStep 6007229 = 2252711) B2252711
theorem B6007391 : Blo 1778090 6007391 := bstep (se 1 (by rfl) ⟨4505543, by rfl⟩ : syracuseStep 6007391 = 9011087) B9011087
theorem B82176707 : Blo 1778090 82176707 := bstep (se 1 (by rfl) ⟨61632530, by rfl⟩ : syracuseStep 82176707 = 123265061) B123265061
theorem B3607273 : Blo 1778090 3607273 := bstep (se 2 (by rfl) ⟨1352727, by rfl⟩ : syracuseStep 3607273 = 2705455) B2705455
theorem B3001097 : Blo 1778090 3001097 := bstep (se 2 (by rfl) ⟨1125411, by rfl⟩ : syracuseStep 3001097 = 2250823) B2250823
theorem B11398097 : Blo 1778090 11398097 := bstep (se 2 (by rfl) ⟨4274286, by rfl⟩ : syracuseStep 11398097 = 8548573) B8548573
theorem B25693469 : Blo 1778090 25693469 := bstep (se 3 (by rfl) ⟨4817525, by rfl⟩ : syracuseStep 25693469 = 9635051) B9635051
theorem B16231709 : Blo 1778090 16231709 := bstep (se 3 (by rfl) ⟨3043445, by rfl⟩ : syracuseStep 16231709 = 6086891) B6086891
theorem B4001183 : Blo 1778090 4001183 := bstep (se 1 (by rfl) ⟨3000887, by rfl⟩ : syracuseStep 4001183 = 6001775) B6001775
theorem B3378665 : Blo 1778090 3378665 := bstep (se 2 (by rfl) ⟨1266999, by rfl⟩ : syracuseStep 3378665 = 2533999) B2533999
theorem B10128887 : Blo 1778090 10128887 := bstep (se 1 (by rfl) ⟨7596665, by rfl⟩ : syracuseStep 10128887 = 15193331) B15193331
theorem B7597775 : Blo 1778090 7597775 := bstep (se 1 (by rfl) ⟨5698331, by rfl⟩ : syracuseStep 7597775 = 11396663) B11396663
theorem B5066459 : Blo 1778090 5066459 := bstep (se 1 (by rfl) ⟨3799844, by rfl⟩ : syracuseStep 5066459 = 7599689) B7599689
theorem B2404255 : Blo 1778090 2404255 := bstep (se 1 (by rfl) ⟨1803191, by rfl⟩ : syracuseStep 2404255 = 3606383) B3606383
theorem B6754535 : Blo 1778090 6754535 := bstep (se 1 (by rfl) ⟨5065901, by rfl⟩ : syracuseStep 6754535 = 10131803) B10131803
theorem B22802755 : Blo 1778090 22802755 := bstep (se 1 (by rfl) ⟨17102066, by rfl⟩ : syracuseStep 22802755 = 34204133) B34204133
theorem B92385623 : Blo 1778090 92385623 := bstep (se 1 (by rfl) ⟨69289217, by rfl⟩ : syracuseStep 92385623 = 138578435) B138578435
theorem B2667497 : Blo 1778090 2667497 := bstep (se 2 (by rfl) ⟨1000311, by rfl⟩ : syracuseStep 2667497 = 2000623) B2000623
theorem B3003817 : Blo 1778090 3003817 := bstep (se 2 (by rfl) ⟨1126431, by rfl⟩ : syracuseStep 3003817 = 2252863) B2252863
theorem B3003871 : Blo 1778090 3003871 := bstep (se 1 (by rfl) ⟨2252903, by rfl⟩ : syracuseStep 3003871 = 4505807) B4505807
theorem B22804091 : Blo 1778090 22804091 := bstep (se 1 (by rfl) ⟨17103068, by rfl⟩ : syracuseStep 22804091 = 34206137) B34206137
theorem B2668169 : Blo 1778090 2668169 := bstep (se 2 (by rfl) ⟨1000563, by rfl⟩ : syracuseStep 2668169 = 2001127) B2001127
theorem B4503215 : Blo 1778090 4503215 := bstep (se 1 (by rfl) ⟨3377411, by rfl⟩ : syracuseStep 4503215 = 6754823) B6754823
theorem B6002423 : Blo 1778090 6002423 := bstep (se 1 (by rfl) ⟨4501817, by rfl⟩ : syracuseStep 6002423 = 9003635) B9003635
theorem B102627161 : Blo 1778090 102627161 := bstep (se 2 (by rfl) ⟨38485185, by rfl⟩ : syracuseStep 102627161 = 76970371) B76970371
theorem B4003739 : Blo 1778090 4003739 := bstep (se 1 (by rfl) ⟨3002804, by rfl⟩ : syracuseStep 4003739 = 6005609) B6005609
theorem B9009305 : Blo 1778090 9009305 := bstep (se 2 (by rfl) ⟨3378489, by rfl⟩ : syracuseStep 9009305 = 6756979) B6756979
theorem B2250919 : Blo 1778090 2250919 := bstep (se 1 (by rfl) ⟨1688189, by rfl⟩ : syracuseStep 2250919 = 3376379) B3376379
theorem B4004027 : Blo 1778090 4004027 := bstep (se 1 (by rfl) ⟨3003020, by rfl⟩ : syracuseStep 4004027 = 6006041) B6006041
theorem B4503863 : Blo 1778090 4503863 := bstep (se 1 (by rfl) ⟨3377897, by rfl⟩ : syracuseStep 4503863 = 6755795) B6755795
theorem B13506911 : Blo 1778090 13506911 := bstep (se 1 (by rfl) ⟨10130183, by rfl⟩ : syracuseStep 13506911 = 20260367) B20260367
theorem B4503995 : Blo 1778090 4503995 := bstep (se 1 (by rfl) ⟨3377996, by rfl⟩ : syracuseStep 4503995 = 6755993) B6755993
theorem B12818999 : Blo 1778090 12818999 := bstep (se 1 (by rfl) ⟨9614249, by rfl⟩ : syracuseStep 12818999 = 19228499) B19228499
theorem B2849519 : Blo 1778090 2849519 := bstep (se 1 (by rfl) ⟨2137139, by rfl⟩ : syracuseStep 2849519 = 4274279) B4274279
theorem B6003503 : Blo 1778090 6003503 := bstep (se 1 (by rfl) ⟨4502627, by rfl⟩ : syracuseStep 6003503 = 9005255) B9005255
theorem B3250991 : Blo 1778090 3250991 := bstep (se 1 (by rfl) ⟨2438243, by rfl⟩ : syracuseStep 3250991 = 4876487) B4876487
theorem B30399299 : Blo 1778090 30399299 := bstep (se 1 (by rfl) ⟨22799474, by rfl⟩ : syracuseStep 30399299 = 45598949) B45598949
theorem B28842875 : Blo 1778090 28842875 := bstep (se 1 (by rfl) ⟨21632156, by rfl⟩ : syracuseStep 28842875 = 43264313) B43264313
theorem B13515659 : Blo 1778090 13515659 := bstep (se 1 (by rfl) ⟨10136744, by rfl⟩ : syracuseStep 13515659 = 20273489) B20273489
theorem B2669735 : Blo 1778090 2669735 := bstep (se 1 (by rfl) ⟨2002301, by rfl⟩ : syracuseStep 2669735 = 4004603) B4004603
theorem B6003881 : Blo 1778090 6003881 := bstep (se 2 (by rfl) ⟨2251455, by rfl⟩ : syracuseStep 6003881 = 4502911) B4502911
theorem B2669819 : Blo 1778090 2669819 := bstep (se 1 (by rfl) ⟨2002364, by rfl⟩ : syracuseStep 2669819 = 4004729) B4004729
theorem B2669945 : Blo 1778090 2669945 := bstep (se 2 (by rfl) ⟨1001229, by rfl⟩ : syracuseStep 2669945 = 2002459) B2002459
theorem B6413737 : Blo 1778090 6413737 := bstep (se 2 (by rfl) ⟨2405151, by rfl⟩ : syracuseStep 6413737 = 4810303) B4810303
theorem B4505129 : Blo 1778090 4505129 := bstep (se 2 (by rfl) ⟨1689423, by rfl⟩ : syracuseStep 4505129 = 3378847) B3378847
theorem B4505159 : Blo 1778090 4505159 := bstep (se 1 (by rfl) ⟨3378869, by rfl⟩ : syracuseStep 4505159 = 6757739) B6757739
theorem B6758225 : Blo 1778090 6758225 := bstep (se 2 (by rfl) ⟨2534334, by rfl⟩ : syracuseStep 6758225 = 5068669) B5068669
theorem B6758255 : Blo 1778090 6758255 := bstep (se 1 (by rfl) ⟨5068691, by rfl⟩ : syracuseStep 6758255 = 10137383) B10137383
theorem B1778331 : Blo 1778090 1778331 := bstep (se 1 (by rfl) ⟨1333748, by rfl⟩ : syracuseStep 1778331 = 2667497) B2667497
theorem B13878215 : Blo 1778090 13878215 := bstep (se 1 (by rfl) ⟨10408661, by rfl⟩ : syracuseStep 13878215 = 20817323) B20817323
theorem B1778779 : Blo 1778090 1778779 := bstep (se 1 (by rfl) ⟨1334084, by rfl⟩ : syracuseStep 1778779 = 2668169) B2668169
theorem B9004445 : Blo 1778090 9004445 := bstep (se 3 (by rfl) ⟨1688333, by rfl⟩ : syracuseStep 9004445 = 3376667) B3376667
theorem B6006203 : Blo 1778090 6006203 := bstep (se 1 (by rfl) ⟨4504652, by rfl⟩ : syracuseStep 6006203 = 9009305) B9009305
theorem B9004607 : Blo 1778090 9004607 := bstep (se 1 (by rfl) ⟨6753455, by rfl⟩ : syracuseStep 9004607 = 13506911) B13506911
theorem B8545999 : Blo 1778090 8545999 := bstep (se 1 (by rfl) ⟨6409499, by rfl⟩ : syracuseStep 8545999 = 12818999) B12818999
theorem B3376865 : Blo 1778090 3376865 := bstep (se 2 (by rfl) ⟨1266324, by rfl⟩ : syracuseStep 3376865 = 2532649) B2532649
theorem B10127177 : Blo 1778090 10127177 := bstep (se 2 (by rfl) ⟨3797691, by rfl⟩ : syracuseStep 10127177 = 7595383) B7595383
theorem B2000731 : Blo 1778090 2000731 := bstep (se 1 (by rfl) ⟨1500548, by rfl⟩ : syracuseStep 2000731 = 3001097) B3001097
theorem B19228583 : Blo 1778090 19228583 := bstep (se 1 (by rfl) ⟨14421437, by rfl⟩ : syracuseStep 19228583 = 28842875) B28842875
theorem B30804077 : Blo 1778090 30804077 := bstep (se 3 (by rfl) ⟨5775764, by rfl⟩ : syracuseStep 30804077 = 11551529) B11551529
theorem B1779823 : Blo 1778090 1779823 := bstep (se 1 (by rfl) ⟨1334867, by rfl⟩ : syracuseStep 1779823 = 2669735) B2669735
theorem B1779879 : Blo 1778090 1779879 := bstep (se 1 (by rfl) ⟨1334909, by rfl⟩ : syracuseStep 1779879 = 2669819) B2669819
theorem B1779963 : Blo 1778090 1779963 := bstep (se 1 (by rfl) ⟨1334972, by rfl⟩ : syracuseStep 1779963 = 2669945) B2669945
theorem B6752591 : Blo 1778090 6752591 := bstep (se 1 (by rfl) ⟨5064443, by rfl⟩ : syracuseStep 6752591 = 10128887) B10128887
theorem B5065183 : Blo 1778090 5065183 := bstep (se 1 (by rfl) ⟨3798887, by rfl⟩ : syracuseStep 5065183 = 7597775) B7597775
theorem B3377639 : Blo 1778090 3377639 := bstep (se 1 (by rfl) ⟨2533229, by rfl⟩ : syracuseStep 3377639 = 5066459) B5066459
theorem B3205673 : Blo 1778090 3205673 := bstep (se 2 (by rfl) ⟨1202127, by rfl⟩ : syracuseStep 3205673 = 2404255) B2404255
theorem B30394925 : Blo 1778090 30394925 := bstep (se 3 (by rfl) ⟨5699048, by rfl⟩ : syracuseStep 30394925 = 11398097) B11398097
theorem B3001225 : Blo 1778090 3001225 := bstep (se 2 (by rfl) ⟨1125459, by rfl⟩ : syracuseStep 3001225 = 2250919) B2250919
theorem B61590415 : Blo 1778090 61590415 := bstep (se 1 (by rfl) ⟨46192811, by rfl⟩ : syracuseStep 61590415 = 92385623) B92385623
theorem B34204679 : Blo 1778090 34204679 := bstep (se 1 (by rfl) ⟨25653509, by rfl⟩ : syracuseStep 34204679 = 51307019) B51307019
theorem B4000841 : Blo 1778090 4000841 := bstep (se 2 (by rfl) ⟨1500315, by rfl⟩ : syracuseStep 4000841 = 3000631) B3000631
theorem B30403673 : Blo 1778090 30403673 := bstep (se 2 (by rfl) ⟨11401377, by rfl⟩ : syracuseStep 30403673 = 22802755) B22802755
theorem B9006227 : Blo 1778090 9006227 := bstep (se 1 (by rfl) ⟨6754670, by rfl⟩ : syracuseStep 9006227 = 13509341) B13509341
theorem B10136927 : Blo 1778090 10136927 := bstep (se 1 (by rfl) ⟨7602695, by rfl⟩ : syracuseStep 10136927 = 15205391) B15205391
theorem B8662399 : Blo 1778090 8662399 := bstep (se 1 (by rfl) ⟨6496799, by rfl⟩ : syracuseStep 8662399 = 12993599) B12993599
theorem B3002143 : Blo 1778090 3002143 := bstep (se 1 (by rfl) ⟨2251607, by rfl⟩ : syracuseStep 3002143 = 4503215) B4503215
theorem B4001615 : Blo 1778090 4001615 := bstep (se 1 (by rfl) ⟨3001211, by rfl⟩ : syracuseStep 4001615 = 6002423) B6002423
theorem B19238789 : Blo 1778090 19238789 := bstep (se 4 (by rfl) ⟨1803636, by rfl⟩ : syracuseStep 19238789 = 3607273) B3607273
theorem B9613255 : Blo 1778090 9613255 := bstep (se 1 (by rfl) ⟨7209941, by rfl⟩ : syracuseStep 9613255 = 14419883) B14419883
theorem B3002575 : Blo 1778090 3002575 := bstep (se 1 (by rfl) ⟨2251931, by rfl⟩ : syracuseStep 3002575 = 4503863) B4503863
theorem B3002663 : Blo 1778090 3002663 := bstep (se 1 (by rfl) ⟨2251997, by rfl⟩ : syracuseStep 3002663 = 4503995) B4503995
theorem B54784471 : Blo 1778090 54784471 := bstep (se 1 (by rfl) ⟨41088353, by rfl⟩ : syracuseStep 54784471 = 82176707) B82176707
theorem B4002335 : Blo 1778090 4002335 := bstep (se 1 (by rfl) ⟨3001751, by rfl⟩ : syracuseStep 4002335 = 6003503) B6003503
theorem B2167327 : Blo 1778090 2167327 := bstep (se 1 (by rfl) ⟨1625495, by rfl⟩ : syracuseStep 2167327 = 3250991) B3250991
theorem B7598717 : Blo 1778090 7598717 := bstep (se 3 (by rfl) ⟨1424759, by rfl⟩ : syracuseStep 7598717 = 2849519) B2849519
theorem B4002587 : Blo 1778090 4002587 := bstep (se 1 (by rfl) ⟨3001940, by rfl⟩ : syracuseStep 4002587 = 6003881) B6003881
theorem B2667455 : Blo 1778090 2667455 := bstep (se 1 (by rfl) ⟨2000591, by rfl⟩ : syracuseStep 2667455 = 4001183) B4001183
theorem B6755309 : Blo 1778090 6755309 := bstep (se 3 (by rfl) ⟨1266620, by rfl⟩ : syracuseStep 6755309 = 2533241) B2533241
theorem B3003419 : Blo 1778090 3003419 := bstep (se 1 (by rfl) ⟨2252564, by rfl⟩ : syracuseStep 3003419 = 4505129) B4505129
theorem B9614377 : Blo 1778090 9614377 := bstep (se 2 (by rfl) ⟨3605391, by rfl⟩ : syracuseStep 9614377 = 7210783) B7210783
theorem B3003439 : Blo 1778090 3003439 := bstep (se 1 (by rfl) ⟨2252579, by rfl⟩ : syracuseStep 3003439 = 4505159) B4505159
theorem B4503023 : Blo 1778090 4503023 := bstep (se 1 (by rfl) ⟨3377267, by rfl⟩ : syracuseStep 4503023 = 6754535) B6754535
theorem B21935777 : Blo 1778090 21935777 := bstep (se 2 (by rfl) ⟨8225916, by rfl⟩ : syracuseStep 21935777 = 16451833) B16451833
theorem B30381803 : Blo 1778090 30381803 := bstep (se 1 (by rfl) ⟨22786352, by rfl⟩ : syracuseStep 30381803 = 45572705) B45572705
theorem B43284557 : Blo 1778090 43284557 := bstep (se 3 (by rfl) ⟨8115854, by rfl⟩ : syracuseStep 43284557 = 16231709) B16231709
theorem B246503513 : Blo 1778090 246503513 := bstep (se 2 (by rfl) ⟨92438817, by rfl⟩ : syracuseStep 246503513 = 184877635) B184877635
theorem B15202727 : Blo 1778090 15202727 := bstep (se 1 (by rfl) ⟨11402045, by rfl⟩ : syracuseStep 15202727 = 22804091) B22804091
theorem B68418107 : Blo 1778090 68418107 := bstep (se 1 (by rfl) ⟨51313580, by rfl⟩ : syracuseStep 68418107 = 102627161) B102627161
theorem B2669159 : Blo 1778090 2669159 := bstep (se 1 (by rfl) ⟨2001869, by rfl⟩ : syracuseStep 2669159 = 4003739) B4003739
theorem B2669351 : Blo 1778090 2669351 := bstep (se 1 (by rfl) ⟨2002013, by rfl⟩ : syracuseStep 2669351 = 4004027) B4004027
theorem B4004819 : Blo 1778090 4004819 := bstep (se 1 (by rfl) ⟨3003614, by rfl⟩ : syracuseStep 4004819 = 6007229) B6007229
theorem B9133049 : Blo 1778090 9133049 := bstep (se 2 (by rfl) ⟨3424893, by rfl⟩ : syracuseStep 9133049 = 6849787) B6849787
theorem B4004927 : Blo 1778090 4004927 := bstep (se 1 (by rfl) ⟨3003695, by rfl⟩ : syracuseStep 4004927 = 6007391) B6007391
theorem B20266199 : Blo 1778090 20266199 := bstep (se 1 (by rfl) ⟨15199649, by rfl⟩ : syracuseStep 20266199 = 30399299) B30399299
theorem B8551649 : Blo 1778090 8551649 := bstep (se 2 (by rfl) ⟨3206868, by rfl⟩ : syracuseStep 8551649 = 6413737) B6413737
theorem B4005089 : Blo 1778090 4005089 := bstep (se 2 (by rfl) ⟨1501908, by rfl⟩ : syracuseStep 4005089 = 3003817) B3003817
theorem B9010439 : Blo 1778090 9010439 := bstep (se 1 (by rfl) ⟨6757829, by rfl⟩ : syracuseStep 9010439 = 13515659) B13515659
theorem B4005161 : Blo 1778090 4005161 := bstep (se 2 (by rfl) ⟨1501935, by rfl⟩ : syracuseStep 4005161 = 3003871) B3003871
theorem B17128979 : Blo 1778090 17128979 := bstep (se 1 (by rfl) ⟨12846734, by rfl⟩ : syracuseStep 17128979 = 25693469) B25693469
theorem B2252443 : Blo 1778090 2252443 := bstep (se 1 (by rfl) ⟨1689332, by rfl⟩ : syracuseStep 2252443 = 3378665) B3378665
theorem B4505483 : Blo 1778090 4505483 := bstep (se 1 (by rfl) ⟨3379112, by rfl⟩ : syracuseStep 4505483 = 6758225) B6758225
theorem B4505503 : Blo 1778090 4505503 := bstep (se 1 (by rfl) ⟨3379127, by rfl⟩ : syracuseStep 4505503 = 6758255) B6758255
theorem B1778303 : Blo 1778090 1778303 := bstep (se 1 (by rfl) ⟨1333727, by rfl⟩ : syracuseStep 1778303 = 2667455) B2667455
theorem B6751451 : Blo 1778090 6751451 := bstep (se 1 (by rfl) ⟨5063588, by rfl⟩ : syracuseStep 6751451 = 10127177) B10127177
theorem B10135151 : Blo 1778090 10135151 := bstep (se 1 (by rfl) ⟨7601363, by rfl⟩ : syracuseStep 10135151 = 15202727) B15202727
theorem B1779439 : Blo 1778090 1779439 := bstep (se 1 (by rfl) ⟨1334579, by rfl⟩ : syracuseStep 1779439 = 2669159) B2669159
theorem B1779567 : Blo 1778090 1779567 := bstep (se 1 (by rfl) ⟨1334675, by rfl⟩ : syracuseStep 1779567 = 2669351) B2669351
theorem B6088699 : Blo 1778090 6088699 := bstep (se 1 (by rfl) ⟨4566524, by rfl⟩ : syracuseStep 6088699 = 9133049) B9133049
theorem B20269115 : Blo 1778090 20269115 := bstep (se 1 (by rfl) ⟨15201836, by rfl⟩ : syracuseStep 20269115 = 30403673) B30403673
theorem B13510799 : Blo 1778090 13510799 := bstep (se 1 (by rfl) ⟨10133099, by rfl⟩ : syracuseStep 13510799 = 20266199) B20266199
theorem B6006959 : Blo 1778090 6006959 := bstep (se 1 (by rfl) ⟨4505219, by rfl⟩ : syracuseStep 6006959 = 9010439) B9010439
theorem B6007337 : Blo 1778090 6007337 := bstep (se 2 (by rfl) ⟨2252751, by rfl⟩ : syracuseStep 6007337 = 4505503) B4505503
theorem B184797845 : Blo 1778090 184797845 := bstep (se 6 (by rfl) ⟨4331199, by rfl⟩ : syracuseStep 184797845 = 8662399) B8662399
theorem B2001775 : Blo 1778090 2001775 := bstep (se 1 (by rfl) ⟨1501331, by rfl⟩ : syracuseStep 2001775 = 3002663) B3002663
theorem B5065811 : Blo 1778090 5065811 := bstep (se 1 (by rfl) ⟨3799358, by rfl⟩ : syracuseStep 5065811 = 7598717) B7598717
theorem B6753577 : Blo 1778090 6753577 := bstep (se 2 (by rfl) ⟨2532591, by rfl⟩ : syracuseStep 6753577 = 5065183) B5065183
theorem B9252143 : Blo 1778090 9252143 := bstep (se 1 (by rfl) ⟨6939107, by rfl⟩ : syracuseStep 9252143 = 13878215) B13878215
theorem B2002279 : Blo 1778090 2002279 := bstep (se 1 (by rfl) ⟨1501709, by rfl⟩ : syracuseStep 2002279 = 3003419) B3003419
theorem B3002015 : Blo 1778090 3002015 := bstep (se 1 (by rfl) ⟨2251511, by rfl⟩ : syracuseStep 3002015 = 4503023) B4503023
theorem B20254535 : Blo 1778090 20254535 := bstep (se 1 (by rfl) ⟨15190901, by rfl⟩ : syracuseStep 20254535 = 30381803) B30381803
theorem B4001633 : Blo 1778090 4001633 := bstep (se 2 (by rfl) ⟨1500612, by rfl⟩ : syracuseStep 4001633 = 3001225) B3001225
theorem B82120553 : Blo 1778090 82120553 := bstep (se 2 (by rfl) ⟨30795207, by rfl⟩ : syracuseStep 82120553 = 61590415) B61590415
theorem B9007037 : Blo 1778090 9007037 := bstep (se 3 (by rfl) ⟨1688819, by rfl⟩ : syracuseStep 9007037 = 3377639) B3377639
theorem B28856371 : Blo 1778090 28856371 := bstep (se 1 (by rfl) ⟨21642278, by rfl⟩ : syracuseStep 28856371 = 43284557) B43284557
theorem B164335675 : Blo 1778090 164335675 := bstep (se 1 (by rfl) ⟨123251756, by rfl⟩ : syracuseStep 164335675 = 246503513) B246503513
theorem B4501727 : Blo 1778090 4501727 := bstep (se 1 (by rfl) ⟨3376295, by rfl⟩ : syracuseStep 4501727 = 6752591) B6752591
theorem B20263283 : Blo 1778090 20263283 := bstep (se 1 (by rfl) ⟨15197462, by rfl⟩ : syracuseStep 20263283 = 30394925) B30394925
theorem B58495405 : Blo 1778090 58495405 := bstep (se 3 (by rfl) ⟨10967888, by rfl⟩ : syracuseStep 58495405 = 21935777) B21935777
theorem B22803119 : Blo 1778090 22803119 := bstep (se 1 (by rfl) ⟨17102339, by rfl⟩ : syracuseStep 22803119 = 34204679) B34204679
theorem B2667227 : Blo 1778090 2667227 := bstep (se 1 (by rfl) ⟨2000420, by rfl⟩ : syracuseStep 2667227 = 4000841) B4000841
theorem B3003257 : Blo 1778090 3003257 := bstep (se 2 (by rfl) ⟨1126221, by rfl⟩ : syracuseStep 3003257 = 2252443) B2252443
theorem B4002857 : Blo 1778090 4002857 := bstep (se 2 (by rfl) ⟨1501071, by rfl⟩ : syracuseStep 4002857 = 3002143) B3002143
theorem B2667641 : Blo 1778090 2667641 := bstep (se 2 (by rfl) ⟨1000365, by rfl⟩ : syracuseStep 2667641 = 2000731) B2000731
theorem B2667743 : Blo 1778090 2667743 := bstep (se 1 (by rfl) ⟨2000807, by rfl⟩ : syracuseStep 2667743 = 4001615) B4001615
theorem B12825859 : Blo 1778090 12825859 := bstep (se 1 (by rfl) ⟨9619394, by rfl⟩ : syracuseStep 12825859 = 19238789) B19238789
theorem B3003655 : Blo 1778090 3003655 := bstep (se 1 (by rfl) ⟨2252741, by rfl⟩ : syracuseStep 3003655 = 4505483) B4505483
theorem B12817673 : Blo 1778090 12817673 := bstep (se 2 (by rfl) ⟨4806627, by rfl⟩ : syracuseStep 12817673 = 9613255) B9613255
theorem B4003433 : Blo 1778090 4003433 := bstep (se 2 (by rfl) ⟨1501287, by rfl⟩ : syracuseStep 4003433 = 3002575) B3002575
theorem B2668223 : Blo 1778090 2668223 := bstep (se 1 (by rfl) ⟨2001167, by rfl⟩ : syracuseStep 2668223 = 4002335) B4002335
theorem B2668391 : Blo 1778090 2668391 := bstep (se 1 (by rfl) ⟨2001293, by rfl⟩ : syracuseStep 2668391 = 4002587) B4002587
theorem B73045961 : Blo 1778090 73045961 := bstep (se 2 (by rfl) ⟨27392235, by rfl⟩ : syracuseStep 73045961 = 54784471) B54784471
theorem B4503539 : Blo 1778090 4503539 := bstep (se 1 (by rfl) ⟨3377654, by rfl⟩ : syracuseStep 4503539 = 6755309) B6755309
theorem B2889769 : Blo 1778090 2889769 := bstep (se 2 (by rfl) ⟨1083663, by rfl⟩ : syracuseStep 2889769 = 2167327) B2167327
theorem B6002963 : Blo 1778090 6002963 := bstep (se 1 (by rfl) ⟨4502222, by rfl⟩ : syracuseStep 6002963 = 9004445) B9004445
theorem B4004135 : Blo 1778090 4004135 := bstep (se 1 (by rfl) ⟨3003101, by rfl⟩ : syracuseStep 4004135 = 6006203) B6006203
theorem B6003071 : Blo 1778090 6003071 := bstep (se 1 (by rfl) ⟨4502303, by rfl⟩ : syracuseStep 6003071 = 9004607) B9004607
theorem B2251243 : Blo 1778090 2251243 := bstep (se 1 (by rfl) ⟨1688432, by rfl⟩ : syracuseStep 2251243 = 3376865) B3376865
theorem B12819055 : Blo 1778090 12819055 := bstep (se 1 (by rfl) ⟨9614291, by rfl⟩ : syracuseStep 12819055 = 19228583) B19228583
theorem B12819169 : Blo 1778090 12819169 := bstep (se 2 (by rfl) ⟨4807188, by rfl⟩ : syracuseStep 12819169 = 9614377) B9614377
theorem B4004585 : Blo 1778090 4004585 := bstep (se 2 (by rfl) ⟨1501719, by rfl⟩ : syracuseStep 4004585 = 3003439) B3003439
theorem B20536051 : Blo 1778090 20536051 := bstep (se 1 (by rfl) ⟨15402038, by rfl⟩ : syracuseStep 20536051 = 30804077) B30804077
theorem B2137115 : Blo 1778090 2137115 := bstep (se 1 (by rfl) ⟨1602836, by rfl⟩ : syracuseStep 2137115 = 3205673) B3205673
theorem B45612071 : Blo 1778090 45612071 := bstep (se 1 (by rfl) ⟨34209053, by rfl⟩ : syracuseStep 45612071 = 68418107) B68418107
theorem B2669879 : Blo 1778090 2669879 := bstep (se 1 (by rfl) ⟨2002409, by rfl⟩ : syracuseStep 2669879 = 4004819) B4004819
theorem B2669951 : Blo 1778090 2669951 := bstep (se 1 (by rfl) ⟨2002463, by rfl⟩ : syracuseStep 2669951 = 4004927) B4004927
theorem B6004151 : Blo 1778090 6004151 := bstep (se 1 (by rfl) ⟨4503113, by rfl⟩ : syracuseStep 6004151 = 9006227) B9006227
theorem B5701099 : Blo 1778090 5701099 := bstep (se 1 (by rfl) ⟨4275824, by rfl⟩ : syracuseStep 5701099 = 8551649) B8551649
theorem B2670059 : Blo 1778090 2670059 := bstep (se 1 (by rfl) ⟨2002544, by rfl⟩ : syracuseStep 2670059 = 4005089) B4005089
theorem B2670107 : Blo 1778090 2670107 := bstep (se 1 (by rfl) ⟨2002580, by rfl⟩ : syracuseStep 2670107 = 4005161) B4005161
theorem B6757951 : Blo 1778090 6757951 := bstep (se 1 (by rfl) ⟨5068463, by rfl⟩ : syracuseStep 6757951 = 10136927) B10136927
theorem B11394665 : Blo 1778090 11394665 := bstep (se 2 (by rfl) ⟨4272999, by rfl⟩ : syracuseStep 11394665 = 8545999) B8545999
theorem B11419319 : Blo 1778090 11419319 := bstep (se 1 (by rfl) ⟨8564489, by rfl⟩ : syracuseStep 11419319 = 17128979) B17128979
theorem B13508855 : Blo 1778090 13508855 := bstep (se 1 (by rfl) ⟨10131641, by rfl⟩ : syracuseStep 13508855 = 20263283) B20263283
theorem B1778151 : Blo 1778090 1778151 := bstep (se 1 (by rfl) ⟨1333613, by rfl⟩ : syracuseStep 1778151 = 2667227) B2667227
theorem B1778427 : Blo 1778090 1778427 := bstep (se 1 (by rfl) ⟨1333820, by rfl⟩ : syracuseStep 1778427 = 2667641) B2667641
theorem B1778495 : Blo 1778090 1778495 := bstep (se 1 (by rfl) ⟨1333871, by rfl⟩ : syracuseStep 1778495 = 2667743) B2667743
theorem B8545115 : Blo 1778090 8545115 := bstep (se 1 (by rfl) ⟨6408836, by rfl⟩ : syracuseStep 8545115 = 12817673) B12817673
theorem B1778815 : Blo 1778090 1778815 := bstep (se 1 (by rfl) ⟨1334111, by rfl⟩ : syracuseStep 1778815 = 2668223) B2668223
theorem B1778927 : Blo 1778090 1778927 := bstep (se 1 (by rfl) ⟨1334195, by rfl⟩ : syracuseStep 1778927 = 2668391) B2668391
theorem B9004769 : Blo 1778090 9004769 := bstep (se 2 (by rfl) ⟨3376788, by rfl⟩ : syracuseStep 9004769 = 6753577) B6753577
theorem B3377207 : Blo 1778090 3377207 := bstep (se 1 (by rfl) ⟨2532905, by rfl⟩ : syracuseStep 3377207 = 5065811) B5065811
theorem B1779919 : Blo 1778090 1779919 := bstep (se 1 (by rfl) ⟨1334939, by rfl⟩ : syracuseStep 1779919 = 2669879) B2669879
theorem B1779967 : Blo 1778090 1779967 := bstep (se 1 (by rfl) ⟨1334975, by rfl⟩ : syracuseStep 1779967 = 2669951) B2669951
theorem B1780039 : Blo 1778090 1780039 := bstep (se 1 (by rfl) ⟨1335029, by rfl⟩ : syracuseStep 1780039 = 2670059) B2670059
theorem B1780071 : Blo 1778090 1780071 := bstep (se 1 (by rfl) ⟨1335053, by rfl⟩ : syracuseStep 1780071 = 2670107) B2670107
theorem B7596443 : Blo 1778090 7596443 := bstep (se 1 (by rfl) ⟨5697332, by rfl⟩ : syracuseStep 7596443 = 11394665) B11394665
theorem B2001343 : Blo 1778090 2001343 := bstep (se 1 (by rfl) ⟨1501007, by rfl⟩ : syracuseStep 2001343 = 3002015) B3002015
theorem B7612879 : Blo 1778090 7612879 := bstep (se 1 (by rfl) ⟨5709659, by rfl⟩ : syracuseStep 7612879 = 11419319) B11419319
theorem B13503023 : Blo 1778090 13503023 := bstep (se 1 (by rfl) ⟨10127267, by rfl⟩ : syracuseStep 13503023 = 20254535) B20254535
theorem B3853025 : Blo 1778090 3853025 := bstep (se 2 (by rfl) ⟨1444884, by rfl⟩ : syracuseStep 3853025 = 2889769) B2889769
theorem B219114233 : Blo 1778090 219114233 := bstep (se 2 (by rfl) ⟨82167837, by rfl⟩ : syracuseStep 219114233 = 164335675) B164335675
theorem B3001151 : Blo 1778090 3001151 := bstep (se 1 (by rfl) ⟨2250863, by rfl⟩ : syracuseStep 3001151 = 4501727) B4501727
theorem B2002171 : Blo 1778090 2002171 := bstep (se 1 (by rfl) ⟨1501628, by rfl⟩ : syracuseStep 2002171 = 3003257) B3003257
theorem B3001657 : Blo 1778090 3001657 := bstep (se 2 (by rfl) ⟨1125621, by rfl⟩ : syracuseStep 3001657 = 2251243) B2251243
theorem B4500967 : Blo 1778090 4500967 := bstep (se 1 (by rfl) ⟨3375725, by rfl⟩ : syracuseStep 4500967 = 6751451) B6751451
theorem B17092073 : Blo 1778090 17092073 := bstep (se 2 (by rfl) ⟨6409527, by rfl⟩ : syracuseStep 17092073 = 12819055) B12819055
theorem B17092225 : Blo 1778090 17092225 := bstep (se 2 (by rfl) ⟨6409584, by rfl⟩ : syracuseStep 17092225 = 12819169) B12819169
theorem B27381401 : Blo 1778090 27381401 := bstep (se 2 (by rfl) ⟨10268025, by rfl⟩ : syracuseStep 27381401 = 20536051) B20536051
theorem B48697307 : Blo 1778090 48697307 := bstep (se 1 (by rfl) ⟨36522980, by rfl⟩ : syracuseStep 48697307 = 73045961) B73045961
theorem B3002359 : Blo 1778090 3002359 := bstep (se 1 (by rfl) ⟨2251769, by rfl⟩ : syracuseStep 3002359 = 4503539) B4503539
theorem B13512743 : Blo 1778090 13512743 := bstep (se 1 (by rfl) ⟨10134557, by rfl⟩ : syracuseStep 13512743 = 20269115) B20269115
theorem B9007199 : Blo 1778090 9007199 := bstep (se 1 (by rfl) ⟨6755399, by rfl⟩ : syracuseStep 9007199 = 13510799) B13510799
theorem B4001975 : Blo 1778090 4001975 := bstep (se 1 (by rfl) ⟨3001481, by rfl⟩ : syracuseStep 4001975 = 6002963) B6002963
theorem B4002047 : Blo 1778090 4002047 := bstep (se 1 (by rfl) ⟨3001535, by rfl⟩ : syracuseStep 4002047 = 6003071) B6003071
theorem B17101145 : Blo 1778090 17101145 := bstep (se 2 (by rfl) ⟨6412929, by rfl⟩ : syracuseStep 17101145 = 12825859) B12825859
theorem B4002767 : Blo 1778090 4002767 := bstep (se 1 (by rfl) ⟨3002075, by rfl⟩ : syracuseStep 4002767 = 6004151) B6004151
theorem B2667755 : Blo 1778090 2667755 := bstep (se 1 (by rfl) ⟨2000816, by rfl⟩ : syracuseStep 2667755 = 4001633) B4001633
theorem B38475161 : Blo 1778090 38475161 := bstep (se 2 (by rfl) ⟨14428185, by rfl⟩ : syracuseStep 38475161 = 28856371) B28856371
theorem B5698973 : Blo 1778090 5698973 := bstep (se 3 (by rfl) ⟨1068557, by rfl⟩ : syracuseStep 5698973 = 2137115) B2137115
theorem B15202079 : Blo 1778090 15202079 := bstep (se 1 (by rfl) ⟨11401559, by rfl⟩ : syracuseStep 15202079 = 22803119) B22803119
theorem B77993873 : Blo 1778090 77993873 := bstep (se 2 (by rfl) ⟨29247702, by rfl⟩ : syracuseStep 77993873 = 58495405) B58495405
theorem B2668571 : Blo 1778090 2668571 := bstep (se 1 (by rfl) ⟨2001428, by rfl⟩ : syracuseStep 2668571 = 4002857) B4002857
theorem B2668955 : Blo 1778090 2668955 := bstep (se 1 (by rfl) ⟨2001716, by rfl⟩ : syracuseStep 2668955 = 4003433) B4003433
theorem B6756767 : Blo 1778090 6756767 := bstep (se 1 (by rfl) ⟨5067575, by rfl⟩ : syracuseStep 6756767 = 10135151) B10135151
theorem B2669033 : Blo 1778090 2669033 := bstep (se 2 (by rfl) ⟨1000887, by rfl⟩ : syracuseStep 2669033 = 2001775) B2001775
theorem B4004639 : Blo 1778090 4004639 := bstep (se 1 (by rfl) ⟨3003479, by rfl⟩ : syracuseStep 4004639 = 6006959) B6006959
theorem B2669423 : Blo 1778090 2669423 := bstep (se 1 (by rfl) ⟨2002067, by rfl⟩ : syracuseStep 2669423 = 4004135) B4004135
theorem B4004873 : Blo 1778090 4004873 := bstep (se 2 (by rfl) ⟨1501827, by rfl⟩ : syracuseStep 4004873 = 3003655) B3003655
theorem B4004891 : Blo 1778090 4004891 := bstep (se 1 (by rfl) ⟨3003668, by rfl⟩ : syracuseStep 4004891 = 6007337) B6007337
theorem B123198563 : Blo 1778090 123198563 := bstep (se 1 (by rfl) ⟨92398922, by rfl⟩ : syracuseStep 123198563 = 184797845) B184797845
theorem B2669705 : Blo 1778090 2669705 := bstep (se 2 (by rfl) ⟨1001139, by rfl⟩ : syracuseStep 2669705 = 2002279) B2002279
theorem B2669723 : Blo 1778090 2669723 := bstep (se 1 (by rfl) ⟨2002292, by rfl⟩ : syracuseStep 2669723 = 4004585) B4004585
theorem B7601465 : Blo 1778090 7601465 := bstep (se 2 (by rfl) ⟨2850549, by rfl⟩ : syracuseStep 7601465 = 5701099) B5701099
theorem B30408047 : Blo 1778090 30408047 := bstep (se 1 (by rfl) ⟨22806035, by rfl⟩ : syracuseStep 30408047 = 45612071) B45612071
theorem B9010601 : Blo 1778090 9010601 := bstep (se 2 (by rfl) ⟨3378975, by rfl⟩ : syracuseStep 9010601 = 6757951) B6757951
theorem B6168095 : Blo 1778090 6168095 := bstep (se 1 (by rfl) ⟨4626071, by rfl⟩ : syracuseStep 6168095 = 9252143) B9252143
theorem B54747035 : Blo 1778090 54747035 := bstep (se 1 (by rfl) ⟨41060276, by rfl⟩ : syracuseStep 54747035 = 82120553) B82120553
theorem B6004691 : Blo 1778090 6004691 := bstep (se 1 (by rfl) ⟨4503518, by rfl⟩ : syracuseStep 6004691 = 9007037) B9007037
theorem B8118265 : Blo 1778090 8118265 := bstep (se 2 (by rfl) ⟨3044349, by rfl⟩ : syracuseStep 8118265 = 6088699) B6088699
theorem B6004799 : Blo 1778090 6004799 := bstep (se 1 (by rfl) ⟨4503599, by rfl⟩ : syracuseStep 6004799 = 9007199) B9007199
theorem B10150505 : Blo 1778090 10150505 := bstep (se 2 (by rfl) ⟨3806439, by rfl⟩ : syracuseStep 10150505 = 7612879) B7612879
theorem B1778503 : Blo 1778090 1778503 := bstep (se 1 (by rfl) ⟨1333877, by rfl⟩ : syracuseStep 1778503 = 2667755) B2667755
theorem B25650107 : Blo 1778090 25650107 := bstep (se 1 (by rfl) ⟨19237580, by rfl⟩ : syracuseStep 25650107 = 38475161) B38475161
theorem B10134719 : Blo 1778090 10134719 := bstep (se 1 (by rfl) ⟨7601039, by rfl⟩ : syracuseStep 10134719 = 15202079) B15202079
theorem B51995915 : Blo 1778090 51995915 := bstep (se 1 (by rfl) ⟨38996936, by rfl⟩ : syracuseStep 51995915 = 77993873) B77993873
theorem B1779047 : Blo 1778090 1779047 := bstep (se 1 (by rfl) ⟨1334285, by rfl⟩ : syracuseStep 1779047 = 2668571) B2668571
theorem B5064295 : Blo 1778090 5064295 := bstep (se 1 (by rfl) ⟨3798221, by rfl⟩ : syracuseStep 5064295 = 7596443) B7596443
theorem B1779303 : Blo 1778090 1779303 := bstep (se 1 (by rfl) ⟨1334477, by rfl⟩ : syracuseStep 1779303 = 2668955) B2668955
theorem B1779355 : Blo 1778090 1779355 := bstep (se 1 (by rfl) ⟨1334516, by rfl⟩ : syracuseStep 1779355 = 2669033) B2669033
theorem B2000767 : Blo 1778090 2000767 := bstep (se 1 (by rfl) ⟨1500575, by rfl⟩ : syracuseStep 2000767 = 3001151) B3001151
theorem B1779615 : Blo 1778090 1779615 := bstep (se 1 (by rfl) ⟨1334711, by rfl⟩ : syracuseStep 1779615 = 2669423) B2669423
theorem B1779803 : Blo 1778090 1779803 := bstep (se 1 (by rfl) ⟨1334852, by rfl⟩ : syracuseStep 1779803 = 2669705) B2669705
theorem B1779815 : Blo 1778090 1779815 := bstep (se 1 (by rfl) ⟨1334861, by rfl⟩ : syracuseStep 1779815 = 2669723) B2669723
theorem B6007067 : Blo 1778090 6007067 := bstep (se 1 (by rfl) ⟨4505300, by rfl⟩ : syracuseStep 6007067 = 9010601) B9010601
theorem B18254267 : Blo 1778090 18254267 := bstep (se 1 (by rfl) ⟨13690700, by rfl⟩ : syracuseStep 18254267 = 27381401) B27381401
theorem B36498023 : Blo 1778090 36498023 := bstep (se 1 (by rfl) ⟨27373517, by rfl⟩ : syracuseStep 36498023 = 54747035) B54747035
theorem B10824353 : Blo 1778090 10824353 := bstep (se 2 (by rfl) ⟨4059132, by rfl⟩ : syracuseStep 10824353 = 8118265) B8118265
theorem B9005903 : Blo 1778090 9005903 := bstep (se 1 (by rfl) ⟨6754427, by rfl⟩ : syracuseStep 9005903 = 13508855) B13508855
theorem B5696743 : Blo 1778090 5696743 := bstep (se 1 (by rfl) ⟨4272557, by rfl⟩ : syracuseStep 5696743 = 8545115) B8545115
theorem B20270573 : Blo 1778090 20270573 := bstep (se 3 (by rfl) ⟨3800732, by rfl⟩ : syracuseStep 20270573 = 7601465) B7601465
theorem B4002209 : Blo 1778090 4002209 := bstep (se 2 (by rfl) ⟨1500828, by rfl⟩ : syracuseStep 4002209 = 3001657) B3001657
theorem B2568683 : Blo 1778090 2568683 := bstep (se 1 (by rfl) ⟨1926512, by rfl⟩ : syracuseStep 2568683 = 3853025) B3853025
theorem B146076155 : Blo 1778090 146076155 := bstep (se 1 (by rfl) ⟨109557116, by rfl⟩ : syracuseStep 146076155 = 219114233) B219114233
theorem B6001289 : Blo 1778090 6001289 := bstep (se 2 (by rfl) ⟨2250483, by rfl⟩ : syracuseStep 6001289 = 4500967) B4500967
theorem B20272031 : Blo 1778090 20272031 := bstep (se 1 (by rfl) ⟨15204023, by rfl⟩ : syracuseStep 20272031 = 30408047) B30408047
theorem B4003127 : Blo 1778090 4003127 := bstep (se 1 (by rfl) ⟨3002345, by rfl⟩ : syracuseStep 4003127 = 6004691) B6004691
theorem B4003145 : Blo 1778090 4003145 := bstep (se 2 (by rfl) ⟨1501179, by rfl⟩ : syracuseStep 4003145 = 3002359) B3002359
theorem B9008495 : Blo 1778090 9008495 := bstep (se 1 (by rfl) ⟨6756371, by rfl⟩ : syracuseStep 9008495 = 13512743) B13512743
theorem B2667983 : Blo 1778090 2667983 := bstep (se 1 (by rfl) ⟨2000987, by rfl⟩ : syracuseStep 2667983 = 4001975) B4001975
theorem B2668031 : Blo 1778090 2668031 := bstep (se 1 (by rfl) ⟨2001023, by rfl⟩ : syracuseStep 2668031 = 4002047) B4002047
theorem B11400763 : Blo 1778090 11400763 := bstep (se 1 (by rfl) ⟨8550572, by rfl⟩ : syracuseStep 11400763 = 17101145) B17101145
theorem B2668457 : Blo 1778090 2668457 := bstep (se 2 (by rfl) ⟨1000671, by rfl⟩ : syracuseStep 2668457 = 2001343) B2001343
theorem B2668511 : Blo 1778090 2668511 := bstep (se 1 (by rfl) ⟨2001383, by rfl⟩ : syracuseStep 2668511 = 4002767) B4002767
theorem B3799315 : Blo 1778090 3799315 := bstep (se 1 (by rfl) ⟨2849486, by rfl⟩ : syracuseStep 3799315 = 5698973) B5698973
theorem B6003179 : Blo 1778090 6003179 := bstep (se 1 (by rfl) ⟨4502384, by rfl⟩ : syracuseStep 6003179 = 9004769) B9004769
theorem B2251471 : Blo 1778090 2251471 := bstep (se 1 (by rfl) ⟨1688603, by rfl⟩ : syracuseStep 2251471 = 3377207) B3377207
theorem B4504511 : Blo 1778090 4504511 := bstep (se 1 (by rfl) ⟨3378383, by rfl⟩ : syracuseStep 4504511 = 6756767) B6756767
theorem B2669561 : Blo 1778090 2669561 := bstep (se 2 (by rfl) ⟨1001085, by rfl⟩ : syracuseStep 2669561 = 2002171) B2002171
theorem B9002015 : Blo 1778090 9002015 := bstep (se 1 (by rfl) ⟨6751511, by rfl⟩ : syracuseStep 9002015 = 13503023) B13503023
theorem B2669759 : Blo 1778090 2669759 := bstep (se 1 (by rfl) ⟨2002319, by rfl⟩ : syracuseStep 2669759 = 4004639) B4004639
theorem B2669915 : Blo 1778090 2669915 := bstep (se 1 (by rfl) ⟨2002436, by rfl⟩ : syracuseStep 2669915 = 4004873) B4004873
theorem B2669927 : Blo 1778090 2669927 := bstep (se 1 (by rfl) ⟨2002445, by rfl⟩ : syracuseStep 2669927 = 4004891) B4004891
theorem B82132375 : Blo 1778090 82132375 := bstep (se 1 (by rfl) ⟨61599281, by rfl⟩ : syracuseStep 82132375 = 123198563) B123198563
theorem B22789633 : Blo 1778090 22789633 := bstep (se 2 (by rfl) ⟨8546112, by rfl⟩ : syracuseStep 22789633 = 17092225) B17092225
theorem B11394715 : Blo 1778090 11394715 := bstep (se 1 (by rfl) ⟨8546036, by rfl⟩ : syracuseStep 11394715 = 17092073) B17092073
theorem B4112063 : Blo 1778090 4112063 := bstep (se 1 (by rfl) ⟨3084047, by rfl⟩ : syracuseStep 4112063 = 6168095) B6168095
theorem B32464871 : Blo 1778090 32464871 := bstep (se 1 (by rfl) ⟨24348653, by rfl⟩ : syracuseStep 32464871 = 48697307) B48697307
theorem B6767003 : Blo 1778090 6767003 := bstep (se 1 (by rfl) ⟨5075252, by rfl⟩ : syracuseStep 6767003 = 10150505) B10150505
theorem B6005663 : Blo 1778090 6005663 := bstep (se 1 (by rfl) ⟨4504247, by rfl⟩ : syracuseStep 6005663 = 9008495) B9008495
theorem B1778655 : Blo 1778090 1778655 := bstep (se 1 (by rfl) ⟨1333991, by rfl⟩ : syracuseStep 1778655 = 2667983) B2667983
theorem B1778687 : Blo 1778090 1778687 := bstep (se 1 (by rfl) ⟨1334015, by rfl⟩ : syracuseStep 1778687 = 2668031) B2668031
theorem B1778971 : Blo 1778090 1778971 := bstep (se 1 (by rfl) ⟨1334228, by rfl⟩ : syracuseStep 1778971 = 2668457) B2668457
theorem B6849821 : Blo 1778090 6849821 := bstep (se 3 (by rfl) ⟨1284341, by rfl⟩ : syracuseStep 6849821 = 2568683) B2568683
theorem B1779007 : Blo 1778090 1779007 := bstep (se 1 (by rfl) ⟨1334255, by rfl⟩ : syracuseStep 1779007 = 2668511) B2668511
theorem B7595657 : Blo 1778090 7595657 := bstep (se 2 (by rfl) ⟨2848371, by rfl⟩ : syracuseStep 7595657 = 5696743) B5696743
theorem B24332015 : Blo 1778090 24332015 := bstep (se 1 (by rfl) ⟨18249011, by rfl⟩ : syracuseStep 24332015 = 36498023) B36498023
theorem B1779707 : Blo 1778090 1779707 := bstep (se 1 (by rfl) ⟨1334780, by rfl⟩ : syracuseStep 1779707 = 2669561) B2669561
theorem B30386177 : Blo 1778090 30386177 := bstep (se 2 (by rfl) ⟨11394816, by rfl⟩ : syracuseStep 30386177 = 22789633) B22789633
theorem B1779839 : Blo 1778090 1779839 := bstep (se 1 (by rfl) ⟨1334879, by rfl⟩ : syracuseStep 1779839 = 2669759) B2669759
theorem B6752393 : Blo 1778090 6752393 := bstep (se 2 (by rfl) ⟨2532147, by rfl⟩ : syracuseStep 6752393 = 5064295) B5064295
theorem B1779943 : Blo 1778090 1779943 := bstep (se 1 (by rfl) ⟨1334957, by rfl⟩ : syracuseStep 1779943 = 2669915) B2669915
theorem B1779951 : Blo 1778090 1779951 := bstep (se 1 (by rfl) ⟨1334963, by rfl⟩ : syracuseStep 1779951 = 2669927) B2669927
theorem B5065753 : Blo 1778090 5065753 := bstep (se 2 (by rfl) ⟨1899657, by rfl⟩ : syracuseStep 5065753 = 3799315) B3799315
theorem B4000859 : Blo 1778090 4000859 := bstep (se 1 (by rfl) ⟨3000644, by rfl⟩ : syracuseStep 4000859 = 6001289) B6001289
theorem B17100071 : Blo 1778090 17100071 := bstep (se 1 (by rfl) ⟨12825053, by rfl⟩ : syracuseStep 17100071 = 25650107) B25650107
theorem B34663943 : Blo 1778090 34663943 := bstep (se 1 (by rfl) ⟨25997957, by rfl⟩ : syracuseStep 34663943 = 51995915) B51995915
theorem B3001961 : Blo 1778090 3001961 := bstep (se 2 (by rfl) ⟨1125735, by rfl⟩ : syracuseStep 3001961 = 2251471) B2251471
theorem B12169511 : Blo 1778090 12169511 := bstep (se 1 (by rfl) ⟨9127133, by rfl⟩ : syracuseStep 12169511 = 18254267) B18254267
theorem B4002119 : Blo 1778090 4002119 := bstep (se 1 (by rfl) ⟨3001589, by rfl⟩ : syracuseStep 4002119 = 6003179) B6003179
theorem B3003007 : Blo 1778090 3003007 := bstep (se 1 (by rfl) ⟨2252255, by rfl⟩ : syracuseStep 3003007 = 4504511) B4504511
theorem B6001343 : Blo 1778090 6001343 := bstep (se 1 (by rfl) ⟨4501007, by rfl⟩ : syracuseStep 6001343 = 9002015) B9002015
theorem B15201017 : Blo 1778090 15201017 := bstep (se 2 (by rfl) ⟨5700381, by rfl⟩ : syracuseStep 15201017 = 11400763) B11400763
theorem B15192953 : Blo 1778090 15192953 := bstep (se 2 (by rfl) ⟨5697357, by rfl⟩ : syracuseStep 15192953 = 11394715) B11394715
theorem B13513715 : Blo 1778090 13513715 := bstep (se 1 (by rfl) ⟨10135286, by rfl⟩ : syracuseStep 13513715 = 20270573) B20270573
theorem B2741375 : Blo 1778090 2741375 := bstep (se 1 (by rfl) ⟨2056031, by rfl⟩ : syracuseStep 2741375 = 4112063) B4112063
theorem B2667689 : Blo 1778090 2667689 := bstep (se 2 (by rfl) ⟨1000383, by rfl⟩ : syracuseStep 2667689 = 2000767) B2000767
theorem B4003199 : Blo 1778090 4003199 := bstep (se 1 (by rfl) ⟨3002399, by rfl⟩ : syracuseStep 4003199 = 6004799) B6004799
theorem B2668139 : Blo 1778090 2668139 := bstep (se 1 (by rfl) ⟨2001104, by rfl⟩ : syracuseStep 2668139 = 4002209) B4002209
theorem B97384103 : Blo 1778090 97384103 := bstep (se 1 (by rfl) ⟨73038077, by rfl⟩ : syracuseStep 97384103 = 146076155) B146076155
theorem B13514687 : Blo 1778090 13514687 := bstep (se 1 (by rfl) ⟨10136015, by rfl⟩ : syracuseStep 13514687 = 20272031) B20272031
theorem B6756479 : Blo 1778090 6756479 := bstep (se 1 (by rfl) ⟨5067359, by rfl⟩ : syracuseStep 6756479 = 10134719) B10134719
theorem B2668751 : Blo 1778090 2668751 := bstep (se 1 (by rfl) ⟨2001563, by rfl⟩ : syracuseStep 2668751 = 4003127) B4003127
theorem B2668763 : Blo 1778090 2668763 := bstep (se 1 (by rfl) ⟨2001572, by rfl⟩ : syracuseStep 2668763 = 4003145) B4003145
theorem B4004711 : Blo 1778090 4004711 := bstep (se 1 (by rfl) ⟨3003533, by rfl⟩ : syracuseStep 4004711 = 6007067) B6007067
theorem B7216235 : Blo 1778090 7216235 := bstep (se 1 (by rfl) ⟨5412176, by rfl⟩ : syracuseStep 7216235 = 10824353) B10824353
theorem B109509833 : Blo 1778090 109509833 := bstep (se 2 (by rfl) ⟨41066187, by rfl⟩ : syracuseStep 109509833 = 82132375) B82132375
theorem B6003935 : Blo 1778090 6003935 := bstep (se 1 (by rfl) ⟨4502951, by rfl⟩ : syracuseStep 6003935 = 9005903) B9005903
theorem B21643247 : Blo 1778090 21643247 := bstep (se 1 (by rfl) ⟨16232435, by rfl⟩ : syracuseStep 21643247 = 32464871) B32464871
theorem B10134011 : Blo 1778090 10134011 := bstep (se 1 (by rfl) ⟨7600508, by rfl⟩ : syracuseStep 10134011 = 15201017) B15201017
theorem B1778459 : Blo 1778090 1778459 := bstep (se 1 (by rfl) ⟨1333844, by rfl⟩ : syracuseStep 1778459 = 2667689) B2667689
theorem B1778759 : Blo 1778090 1778759 := bstep (se 1 (by rfl) ⟨1334069, by rfl⟩ : syracuseStep 1778759 = 2668139) B2668139
theorem B5063771 : Blo 1778090 5063771 := bstep (se 1 (by rfl) ⟨3797828, by rfl⟩ : syracuseStep 5063771 = 7595657) B7595657
theorem B64922735 : Blo 1778090 64922735 := bstep (se 1 (by rfl) ⟨48692051, by rfl⟩ : syracuseStep 64922735 = 97384103) B97384103
theorem B1779167 : Blo 1778090 1779167 := bstep (se 1 (by rfl) ⟨1334375, by rfl⟩ : syracuseStep 1779167 = 2668751) B2668751
theorem B1779175 : Blo 1778090 1779175 := bstep (se 1 (by rfl) ⟨1334381, by rfl⟩ : syracuseStep 1779175 = 2668763) B2668763
theorem B4810823 : Blo 1778090 4810823 := bstep (se 1 (by rfl) ⟨3608117, by rfl⟩ : syracuseStep 4810823 = 7216235) B7216235
theorem B2001307 : Blo 1778090 2001307 := bstep (se 1 (by rfl) ⟨1500980, by rfl⟩ : syracuseStep 2001307 = 3001961) B3001961
theorem B57715325 : Blo 1778090 57715325 := bstep (se 3 (by rfl) ⟨10821623, by rfl⟩ : syracuseStep 57715325 = 21643247) B21643247
theorem B8113007 : Blo 1778090 8113007 := bstep (se 1 (by rfl) ⟨6084755, by rfl⟩ : syracuseStep 8113007 = 12169511) B12169511
theorem B7310333 : Blo 1778090 7310333 := bstep (se 3 (by rfl) ⟨1370687, by rfl⟩ : syracuseStep 7310333 = 2741375) B2741375
theorem B4000895 : Blo 1778090 4000895 := bstep (se 1 (by rfl) ⟨3000671, by rfl⟩ : syracuseStep 4000895 = 6001343) B6001343
theorem B10128635 : Blo 1778090 10128635 := bstep (se 1 (by rfl) ⟨7596476, by rfl⟩ : syracuseStep 10128635 = 15192953) B15192953
theorem B4566547 : Blo 1778090 4566547 := bstep (se 1 (by rfl) ⟨3424910, by rfl⟩ : syracuseStep 4566547 = 6849821) B6849821
theorem B6754337 : Blo 1778090 6754337 := bstep (se 2 (by rfl) ⟨2532876, by rfl⟩ : syracuseStep 6754337 = 5065753) B5065753
theorem B4501595 : Blo 1778090 4501595 := bstep (se 1 (by rfl) ⟨3376196, by rfl⟩ : syracuseStep 4501595 = 6752393) B6752393
theorem B64885373 : Blo 1778090 64885373 := bstep (se 3 (by rfl) ⟨12166007, by rfl⟩ : syracuseStep 64885373 = 24332015) B24332015
theorem B2667239 : Blo 1778090 2667239 := bstep (se 1 (by rfl) ⟨2000429, by rfl⟩ : syracuseStep 2667239 = 4000859) B4000859
theorem B4002623 : Blo 1778090 4002623 := bstep (se 1 (by rfl) ⟨3001967, by rfl⟩ : syracuseStep 4002623 = 6003935) B6003935
theorem B11400047 : Blo 1778090 11400047 := bstep (se 1 (by rfl) ⟨8550035, by rfl⟩ : syracuseStep 11400047 = 17100071) B17100071
theorem B2668079 : Blo 1778090 2668079 := bstep (se 1 (by rfl) ⟨2001059, by rfl⟩ : syracuseStep 2668079 = 4002119) B4002119
theorem B4003775 : Blo 1778090 4003775 := bstep (se 1 (by rfl) ⟨3002831, by rfl⟩ : syracuseStep 4003775 = 6005663) B6005663
theorem B9009143 : Blo 1778090 9009143 := bstep (se 1 (by rfl) ⟨6756857, by rfl⟩ : syracuseStep 9009143 = 13513715) B13513715
theorem B4004009 : Blo 1778090 4004009 := bstep (se 2 (by rfl) ⟨1501503, by rfl⟩ : syracuseStep 4004009 = 3003007) B3003007
theorem B2668799 : Blo 1778090 2668799 := bstep (se 1 (by rfl) ⟨2001599, by rfl⟩ : syracuseStep 2668799 = 4003199) B4003199
theorem B18045341 : Blo 1778090 18045341 := bstep (se 3 (by rfl) ⟨3383501, by rfl⟩ : syracuseStep 18045341 = 6767003) B6767003
theorem B9009791 : Blo 1778090 9009791 := bstep (se 1 (by rfl) ⟨6757343, by rfl⟩ : syracuseStep 9009791 = 13514687) B13514687
theorem B20257451 : Blo 1778090 20257451 := bstep (se 1 (by rfl) ⟨15193088, by rfl⟩ : syracuseStep 20257451 = 30386177) B30386177
theorem B4504319 : Blo 1778090 4504319 := bstep (se 1 (by rfl) ⟨3378239, by rfl⟩ : syracuseStep 4504319 = 6756479) B6756479
theorem B2669807 : Blo 1778090 2669807 := bstep (se 1 (by rfl) ⟨2002355, by rfl⟩ : syracuseStep 2669807 = 4004711) B4004711
theorem B73006555 : Blo 1778090 73006555 := bstep (se 1 (by rfl) ⟨54754916, by rfl⟩ : syracuseStep 73006555 = 109509833) B109509833
theorem B23109295 : Blo 1778090 23109295 := bstep (se 1 (by rfl) ⟨17331971, by rfl⟩ : syracuseStep 23109295 = 34663943) B34663943
theorem B1778159 : Blo 1778090 1778159 := bstep (se 1 (by rfl) ⟨1333619, by rfl⟩ : syracuseStep 1778159 = 2667239) B2667239
theorem B3375847 : Blo 1778090 3375847 := bstep (se 1 (by rfl) ⟨2531885, by rfl⟩ : syracuseStep 3375847 = 5063771) B5063771
theorem B1778719 : Blo 1778090 1778719 := bstep (se 1 (by rfl) ⟨1334039, by rfl⟩ : syracuseStep 1778719 = 2668079) B2668079
theorem B6006095 : Blo 1778090 6006095 := bstep (se 1 (by rfl) ⟨4504571, by rfl⟩ : syracuseStep 6006095 = 9009143) B9009143
theorem B1779199 : Blo 1778090 1779199 := bstep (se 1 (by rfl) ⟨1334399, by rfl⟩ : syracuseStep 1779199 = 2668799) B2668799
theorem B6006527 : Blo 1778090 6006527 := bstep (se 1 (by rfl) ⟨4504895, by rfl⟩ : syracuseStep 6006527 = 9009791) B9009791
theorem B6088729 : Blo 1778090 6088729 := bstep (se 2 (by rfl) ⟨2283273, by rfl⟩ : syracuseStep 6088729 = 4566547) B4566547
theorem B1779871 : Blo 1778090 1779871 := bstep (se 1 (by rfl) ⟨1334903, by rfl⟩ : syracuseStep 1779871 = 2669807) B2669807
theorem B6752423 : Blo 1778090 6752423 := bstep (se 1 (by rfl) ⟨5064317, by rfl⟩ : syracuseStep 6752423 = 10128635) B10128635
theorem B30812393 : Blo 1778090 30812393 := bstep (se 2 (by rfl) ⟨11554647, by rfl⟩ : syracuseStep 30812393 = 23109295) B23109295
theorem B3001063 : Blo 1778090 3001063 := bstep (se 1 (by rfl) ⟨2250797, by rfl⟩ : syracuseStep 3001063 = 4501595) B4501595
theorem B43256915 : Blo 1778090 43256915 := bstep (se 1 (by rfl) ⟨32442686, by rfl⟩ : syracuseStep 43256915 = 64885373) B64885373
theorem B3207215 : Blo 1778090 3207215 := bstep (se 1 (by rfl) ⟨2405411, by rfl⟩ : syracuseStep 3207215 = 4810823) B4810823
theorem B12030227 : Blo 1778090 12030227 := bstep (se 1 (by rfl) ⟨9022670, by rfl⟩ : syracuseStep 12030227 = 18045341) B18045341
theorem B13504967 : Blo 1778090 13504967 := bstep (se 1 (by rfl) ⟨10128725, by rfl⟩ : syracuseStep 13504967 = 20257451) B20257451
theorem B3002879 : Blo 1778090 3002879 := bstep (se 1 (by rfl) ⟨2252159, by rfl⟩ : syracuseStep 3002879 = 4504319) B4504319
theorem B97342073 : Blo 1778090 97342073 := bstep (se 2 (by rfl) ⟨36503277, by rfl⟩ : syracuseStep 97342073 = 73006555) B73006555
theorem B2667263 : Blo 1778090 2667263 := bstep (se 1 (by rfl) ⟨2000447, by rfl⟩ : syracuseStep 2667263 = 4000895) B4000895
theorem B4502891 : Blo 1778090 4502891 := bstep (se 1 (by rfl) ⟨3377168, by rfl⟩ : syracuseStep 4502891 = 6754337) B6754337
theorem B173127293 : Blo 1778090 173127293 := bstep (se 3 (by rfl) ⟨32461367, by rfl⟩ : syracuseStep 173127293 = 64922735) B64922735
theorem B6756007 : Blo 1778090 6756007 := bstep (se 1 (by rfl) ⟨5067005, by rfl⟩ : syracuseStep 6756007 = 10134011) B10134011
theorem B2668409 : Blo 1778090 2668409 := bstep (se 2 (by rfl) ⟨1000653, by rfl⟩ : syracuseStep 2668409 = 2001307) B2001307
theorem B2668415 : Blo 1778090 2668415 := bstep (se 1 (by rfl) ⟨2001311, by rfl⟩ : syracuseStep 2668415 = 4002623) B4002623
theorem B7600031 : Blo 1778090 7600031 := bstep (se 1 (by rfl) ⟨5700023, by rfl⟩ : syracuseStep 7600031 = 11400047) B11400047
theorem B2669183 : Blo 1778090 2669183 := bstep (se 1 (by rfl) ⟨2001887, by rfl⟩ : syracuseStep 2669183 = 4003775) B4003775
theorem B2669339 : Blo 1778090 2669339 := bstep (se 1 (by rfl) ⟨2002004, by rfl⟩ : syracuseStep 2669339 = 4004009) B4004009
theorem B38476883 : Blo 1778090 38476883 := bstep (se 1 (by rfl) ⟨28857662, by rfl⟩ : syracuseStep 38476883 = 57715325) B57715325
theorem B4873555 : Blo 1778090 4873555 := bstep (se 1 (by rfl) ⟨3655166, by rfl⟩ : syracuseStep 4873555 = 7310333) B7310333
theorem B21634685 : Blo 1778090 21634685 := bstep (se 3 (by rfl) ⟨4056503, by rfl⟩ : syracuseStep 21634685 = 8113007) B8113007
theorem B8118305 : Blo 1778090 8118305 := bstep (se 2 (by rfl) ⟨3044364, by rfl⟩ : syracuseStep 8118305 = 6088729) B6088729
theorem B8552573 : Blo 1778090 8552573 := bstep (se 3 (by rfl) ⟨1603607, by rfl⟩ : syracuseStep 8552573 = 3207215) B3207215
theorem B8020151 : Blo 1778090 8020151 := bstep (se 1 (by rfl) ⟨6015113, by rfl⟩ : syracuseStep 8020151 = 12030227) B12030227
theorem B9003311 : Blo 1778090 9003311 := bstep (se 1 (by rfl) ⟨6752483, by rfl⟩ : syracuseStep 9003311 = 13504967) B13504967
theorem B1778175 : Blo 1778090 1778175 := bstep (se 1 (by rfl) ⟨1333631, by rfl⟩ : syracuseStep 1778175 = 2667263) B2667263
theorem B115418195 : Blo 1778090 115418195 := bstep (se 1 (by rfl) ⟨86563646, by rfl⟩ : syracuseStep 115418195 = 173127293) B173127293
theorem B1778939 : Blo 1778090 1778939 := bstep (se 1 (by rfl) ⟨1334204, by rfl⟩ : syracuseStep 1778939 = 2668409) B2668409
theorem B1778943 : Blo 1778090 1778943 := bstep (se 1 (by rfl) ⟨1334207, by rfl⟩ : syracuseStep 1778943 = 2668415) B2668415
theorem B1779455 : Blo 1778090 1779455 := bstep (se 1 (by rfl) ⟨1334591, by rfl⟩ : syracuseStep 1779455 = 2669183) B2669183
theorem B6498073 : Blo 1778090 6498073 := bstep (se 2 (by rfl) ⟨2436777, by rfl⟩ : syracuseStep 6498073 = 4873555) B4873555
theorem B1779559 : Blo 1778090 1779559 := bstep (se 1 (by rfl) ⟨1334669, by rfl⟩ : syracuseStep 1779559 = 2669339) B2669339
theorem B28837943 : Blo 1778090 28837943 := bstep (se 1 (by rfl) ⟨21628457, by rfl⟩ : syracuseStep 28837943 = 43256915) B43256915
theorem B25651255 : Blo 1778090 25651255 := bstep (se 1 (by rfl) ⟨19238441, by rfl⟩ : syracuseStep 25651255 = 38476883) B38476883
theorem B2001919 : Blo 1778090 2001919 := bstep (se 1 (by rfl) ⟨1501439, by rfl⟩ : syracuseStep 2001919 = 3002879) B3002879
theorem B3001927 : Blo 1778090 3001927 := bstep (se 1 (by rfl) ⟨2251445, by rfl⟩ : syracuseStep 3001927 = 4502891) B4502891
theorem B4501129 : Blo 1778090 4501129 := bstep (se 2 (by rfl) ⟨1687923, by rfl⟩ : syracuseStep 4501129 = 3375847) B3375847
theorem B4001417 : Blo 1778090 4001417 := bstep (se 2 (by rfl) ⟨1500531, by rfl⟩ : syracuseStep 4001417 = 3001063) B3001063
theorem B5066687 : Blo 1778090 5066687 := bstep (se 1 (by rfl) ⟨3800015, by rfl⟩ : syracuseStep 5066687 = 7600031) B7600031
theorem B4501615 : Blo 1778090 4501615 := bstep (se 1 (by rfl) ⟨3376211, by rfl⟩ : syracuseStep 4501615 = 6752423) B6752423
theorem B20541595 : Blo 1778090 20541595 := bstep (se 1 (by rfl) ⟨15406196, by rfl⟩ : syracuseStep 20541595 = 30812393) B30812393
theorem B9008009 : Blo 1778090 9008009 := bstep (se 2 (by rfl) ⟨3378003, by rfl⟩ : syracuseStep 9008009 = 6756007) B6756007
theorem B14423123 : Blo 1778090 14423123 := bstep (se 1 (by rfl) ⟨10817342, by rfl⟩ : syracuseStep 14423123 = 21634685) B21634685
theorem B64894715 : Blo 1778090 64894715 := bstep (se 1 (by rfl) ⟨48671036, by rfl⟩ : syracuseStep 64894715 = 97342073) B97342073
theorem B4004063 : Blo 1778090 4004063 := bstep (se 1 (by rfl) ⟨3003047, by rfl⟩ : syracuseStep 4004063 = 6006095) B6006095
theorem B4004351 : Blo 1778090 4004351 := bstep (se 1 (by rfl) ⟨3003263, by rfl⟩ : syracuseStep 4004351 = 6006527) B6006527
theorem B34201673 : Blo 1778090 34201673 := bstep (se 2 (by rfl) ⟨12825627, by rfl⟩ : syracuseStep 34201673 = 25651255) B25651255
theorem B5701715 : Blo 1778090 5701715 := bstep (se 1 (by rfl) ⟨4276286, by rfl⟩ : syracuseStep 5701715 = 8552573) B8552573
theorem B38461661 : Blo 1778090 38461661 := bstep (se 3 (by rfl) ⟨7211561, by rfl⟩ : syracuseStep 38461661 = 14423123) B14423123
theorem B6005339 : Blo 1778090 6005339 := bstep (se 1 (by rfl) ⟨4504004, by rfl⟩ : syracuseStep 6005339 = 9008009) B9008009
theorem B43263143 : Blo 1778090 43263143 := bstep (se 1 (by rfl) ⟨32447357, by rfl⟩ : syracuseStep 43263143 = 64894715) B64894715
theorem B3377791 : Blo 1778090 3377791 := bstep (se 1 (by rfl) ⟨2533343, by rfl⟩ : syracuseStep 3377791 = 5066687) B5066687
theorem B27388793 : Blo 1778090 27388793 := bstep (se 2 (by rfl) ⟨10270797, by rfl⟩ : syracuseStep 27388793 = 20541595) B20541595
theorem B4002569 : Blo 1778090 4002569 := bstep (se 2 (by rfl) ⟨1500963, by rfl⟩ : syracuseStep 4002569 = 3001927) B3001927
theorem B6001505 : Blo 1778090 6001505 := bstep (se 2 (by rfl) ⟨2250564, by rfl⟩ : syracuseStep 6001505 = 4501129) B4501129
theorem B8664097 : Blo 1778090 8664097 := bstep (se 2 (by rfl) ⟨3249036, by rfl⟩ : syracuseStep 8664097 = 6498073) B6498073
theorem B2667611 : Blo 1778090 2667611 := bstep (se 1 (by rfl) ⟨2000708, by rfl⟩ : syracuseStep 2667611 = 4001417) B4001417
theorem B5412203 : Blo 1778090 5412203 := bstep (se 1 (by rfl) ⟨4059152, by rfl⟩ : syracuseStep 5412203 = 8118305) B8118305
theorem B5346767 : Blo 1778090 5346767 := bstep (se 1 (by rfl) ⟨4010075, by rfl⟩ : syracuseStep 5346767 = 8020151) B8020151
theorem B6002153 : Blo 1778090 6002153 := bstep (se 2 (by rfl) ⟨2250807, by rfl⟩ : syracuseStep 6002153 = 4501615) B4501615
theorem B6002207 : Blo 1778090 6002207 := bstep (se 1 (by rfl) ⟨4501655, by rfl⟩ : syracuseStep 6002207 = 9003311) B9003311
theorem B76945463 : Blo 1778090 76945463 := bstep (se 1 (by rfl) ⟨57709097, by rfl⟩ : syracuseStep 76945463 = 115418195) B115418195
theorem B2669225 : Blo 1778090 2669225 := bstep (se 2 (by rfl) ⟨1000959, by rfl⟩ : syracuseStep 2669225 = 2001919) B2001919
theorem B19225295 : Blo 1778090 19225295 := bstep (se 1 (by rfl) ⟨14418971, by rfl⟩ : syracuseStep 19225295 = 28837943) B28837943
theorem B2669375 : Blo 1778090 2669375 := bstep (se 1 (by rfl) ⟨2002031, by rfl⟩ : syracuseStep 2669375 = 4004063) B4004063
theorem B2669567 : Blo 1778090 2669567 := bstep (se 1 (by rfl) ⟨2002175, by rfl⟩ : syracuseStep 2669567 = 4004351) B4004351
theorem B3801143 : Blo 1778090 3801143 := bstep (se 1 (by rfl) ⟨2850857, by rfl⟩ : syracuseStep 3801143 = 5701715) B5701715
theorem B25641107 : Blo 1778090 25641107 := bstep (se 1 (by rfl) ⟨19230830, by rfl⟩ : syracuseStep 25641107 = 38461661) B38461661
theorem B1778407 : Blo 1778090 1778407 := bstep (se 1 (by rfl) ⟨1333805, by rfl⟩ : syracuseStep 1778407 = 2667611) B2667611
theorem B11552129 : Blo 1778090 11552129 := bstep (se 2 (by rfl) ⟨4332048, by rfl⟩ : syracuseStep 11552129 = 8664097) B8664097
theorem B1779483 : Blo 1778090 1779483 := bstep (se 1 (by rfl) ⟨1334612, by rfl⟩ : syracuseStep 1779483 = 2669225) B2669225
theorem B1779583 : Blo 1778090 1779583 := bstep (se 1 (by rfl) ⟨1334687, by rfl⟩ : syracuseStep 1779583 = 2669375) B2669375
theorem B1779711 : Blo 1778090 1779711 := bstep (se 1 (by rfl) ⟨1334783, by rfl⟩ : syracuseStep 1779711 = 2669567) B2669567
theorem B22801115 : Blo 1778090 22801115 := bstep (se 1 (by rfl) ⟨17100836, by rfl⟩ : syracuseStep 22801115 = 34201673) B34201673
theorem B4001003 : Blo 1778090 4001003 := bstep (se 1 (by rfl) ⟨3000752, by rfl⟩ : syracuseStep 4001003 = 6001505) B6001505
theorem B3608135 : Blo 1778090 3608135 := bstep (se 1 (by rfl) ⟨2706101, by rfl⟩ : syracuseStep 3608135 = 5412203) B5412203
theorem B4001435 : Blo 1778090 4001435 := bstep (se 1 (by rfl) ⟨3001076, by rfl⟩ : syracuseStep 4001435 = 6002153) B6002153
theorem B4001471 : Blo 1778090 4001471 := bstep (se 1 (by rfl) ⟨3001103, by rfl⟩ : syracuseStep 4001471 = 6002207) B6002207
theorem B14258045 : Blo 1778090 14258045 := bstep (se 3 (by rfl) ⟨2673383, by rfl⟩ : syracuseStep 14258045 = 5346767) B5346767
theorem B12816863 : Blo 1778090 12816863 := bstep (se 1 (by rfl) ⟨9612647, by rfl⟩ : syracuseStep 12816863 = 19225295) B19225295
theorem B4003559 : Blo 1778090 4003559 := bstep (se 1 (by rfl) ⟨3002669, by rfl⟩ : syracuseStep 4003559 = 6005339) B6005339
theorem B2668379 : Blo 1778090 2668379 := bstep (se 1 (by rfl) ⟨2001284, by rfl⟩ : syracuseStep 2668379 = 4002569) B4002569
theorem B28842095 : Blo 1778090 28842095 := bstep (se 1 (by rfl) ⟨21631571, by rfl⟩ : syracuseStep 28842095 = 43263143) B43263143
theorem B4503721 : Blo 1778090 4503721 := bstep (se 2 (by rfl) ⟨1688895, by rfl⟩ : syracuseStep 4503721 = 3377791) B3377791
theorem B51296975 : Blo 1778090 51296975 := bstep (se 1 (by rfl) ⟨38472731, by rfl⟩ : syracuseStep 51296975 = 76945463) B76945463
theorem B18259195 : Blo 1778090 18259195 := bstep (se 1 (by rfl) ⟨13694396, by rfl⟩ : syracuseStep 18259195 = 27388793) B27388793
theorem B6004961 : Blo 1778090 6004961 := bstep (se 2 (by rfl) ⟨2251860, by rfl⟩ : syracuseStep 6004961 = 4503721) B4503721
theorem B8544575 : Blo 1778090 8544575 := bstep (se 1 (by rfl) ⟨6408431, by rfl⟩ : syracuseStep 8544575 = 12816863) B12816863
theorem B7701419 : Blo 1778090 7701419 := bstep (se 1 (by rfl) ⟨5776064, by rfl⟩ : syracuseStep 7701419 = 11552129) B11552129
theorem B1778919 : Blo 1778090 1778919 := bstep (se 1 (by rfl) ⟨1334189, by rfl⟩ : syracuseStep 1778919 = 2668379) B2668379
theorem B19228063 : Blo 1778090 19228063 := bstep (se 1 (by rfl) ⟨14421047, by rfl⟩ : syracuseStep 19228063 = 28842095) B28842095
theorem B9505363 : Blo 1778090 9505363 := bstep (se 1 (by rfl) ⟨7129022, by rfl⟩ : syracuseStep 9505363 = 14258045) B14258045
theorem B2534095 : Blo 1778090 2534095 := bstep (se 1 (by rfl) ⟨1900571, by rfl⟩ : syracuseStep 2534095 = 3801143) B3801143
theorem B34197983 : Blo 1778090 34197983 := bstep (se 1 (by rfl) ⟨25648487, by rfl⟩ : syracuseStep 34197983 = 51296975) B51296975
theorem B15200743 : Blo 1778090 15200743 := bstep (se 1 (by rfl) ⟨11400557, by rfl⟩ : syracuseStep 15200743 = 22801115) B22801115
theorem B2667335 : Blo 1778090 2667335 := bstep (se 1 (by rfl) ⟨2000501, by rfl⟩ : syracuseStep 2667335 = 4001003) B4001003
theorem B2405423 : Blo 1778090 2405423 := bstep (se 1 (by rfl) ⟨1804067, by rfl⟩ : syracuseStep 2405423 = 3608135) B3608135
theorem B2667623 : Blo 1778090 2667623 := bstep (se 1 (by rfl) ⟨2000717, by rfl⟩ : syracuseStep 2667623 = 4001435) B4001435
theorem B2667647 : Blo 1778090 2667647 := bstep (se 1 (by rfl) ⟨2000735, by rfl⟩ : syracuseStep 2667647 = 4001471) B4001471
theorem B17094071 : Blo 1778090 17094071 := bstep (se 1 (by rfl) ⟨12820553, by rfl⟩ : syracuseStep 17094071 = 25641107) B25641107
theorem B2669039 : Blo 1778090 2669039 := bstep (se 1 (by rfl) ⟨2001779, by rfl⟩ : syracuseStep 2669039 = 4003559) B4003559
theorem B24345593 : Blo 1778090 24345593 := bstep (se 2 (by rfl) ⟨9129597, by rfl⟩ : syracuseStep 24345593 = 18259195) B18259195
theorem B6414461 : Blo 1778090 6414461 := bstep (se 3 (by rfl) ⟨1202711, by rfl⟩ : syracuseStep 6414461 = 2405423) B2405423
theorem B22798655 : Blo 1778090 22798655 := bstep (se 1 (by rfl) ⟨17098991, by rfl⟩ : syracuseStep 22798655 = 34197983) B34197983
theorem B1778223 : Blo 1778090 1778223 := bstep (se 1 (by rfl) ⟨1333667, by rfl⟩ : syracuseStep 1778223 = 2667335) B2667335
theorem B20267657 : Blo 1778090 20267657 := bstep (se 2 (by rfl) ⟨7600371, by rfl⟩ : syracuseStep 20267657 = 15200743) B15200743
theorem B1778415 : Blo 1778090 1778415 := bstep (se 1 (by rfl) ⟨1333811, by rfl⟩ : syracuseStep 1778415 = 2667623) B2667623
theorem B1778431 : Blo 1778090 1778431 := bstep (se 1 (by rfl) ⟨1333823, by rfl⟩ : syracuseStep 1778431 = 2667647) B2667647
theorem B12673817 : Blo 1778090 12673817 := bstep (se 2 (by rfl) ⟨4752681, by rfl⟩ : syracuseStep 12673817 = 9505363) B9505363
theorem B11396047 : Blo 1778090 11396047 := bstep (se 1 (by rfl) ⟨8547035, by rfl⟩ : syracuseStep 11396047 = 17094071) B17094071
theorem B1779359 : Blo 1778090 1779359 := bstep (se 1 (by rfl) ⟨1334519, by rfl⟩ : syracuseStep 1779359 = 2669039) B2669039
theorem B16230395 : Blo 1778090 16230395 := bstep (se 1 (by rfl) ⟨12172796, by rfl⟩ : syracuseStep 16230395 = 24345593) B24345593
theorem B22785533 : Blo 1778090 22785533 := bstep (se 3 (by rfl) ⟨4272287, by rfl⟩ : syracuseStep 22785533 = 8544575) B8544575
theorem B25637417 : Blo 1778090 25637417 := bstep (se 2 (by rfl) ⟨9614031, by rfl⟩ : syracuseStep 25637417 = 19228063) B19228063
theorem B4003307 : Blo 1778090 4003307 := bstep (se 1 (by rfl) ⟨3002480, by rfl⟩ : syracuseStep 4003307 = 6004961) B6004961
theorem B13515173 : Blo 1778090 13515173 := bstep (se 4 (by rfl) ⟨1267047, by rfl⟩ : syracuseStep 13515173 = 2534095) B2534095
theorem B20537117 : Blo 1778090 20537117 := bstep (se 3 (by rfl) ⟨3850709, by rfl⟩ : syracuseStep 20537117 = 7701419) B7701419
theorem B4276307 : Blo 1778090 4276307 := bstep (se 1 (by rfl) ⟨3207230, by rfl⟩ : syracuseStep 4276307 = 6414461) B6414461
theorem B15190355 : Blo 1778090 15190355 := bstep (se 1 (by rfl) ⟨11392766, by rfl⟩ : syracuseStep 15190355 = 22785533) B22785533
theorem B13691411 : Blo 1778090 13691411 := bstep (se 1 (by rfl) ⟨10268558, by rfl⟩ : syracuseStep 13691411 = 20537117) B20537117
theorem B15199103 : Blo 1778090 15199103 := bstep (se 1 (by rfl) ⟨11399327, by rfl⟩ : syracuseStep 15199103 = 22798655) B22798655
theorem B17091611 : Blo 1778090 17091611 := bstep (se 1 (by rfl) ⟨12818708, by rfl⟩ : syracuseStep 17091611 = 25637417) B25637417
theorem B13511771 : Blo 1778090 13511771 := bstep (se 1 (by rfl) ⟨10133828, by rfl⟩ : syracuseStep 13511771 = 20267657) B20267657
theorem B8449211 : Blo 1778090 8449211 := bstep (se 1 (by rfl) ⟨6336908, by rfl⟩ : syracuseStep 8449211 = 12673817) B12673817
theorem B2668871 : Blo 1778090 2668871 := bstep (se 1 (by rfl) ⟨2001653, by rfl⟩ : syracuseStep 2668871 = 4003307) B4003307
theorem B15194729 : Blo 1778090 15194729 := bstep (se 2 (by rfl) ⟨5698023, by rfl⟩ : syracuseStep 15194729 = 11396047) B11396047
theorem B10820263 : Blo 1778090 10820263 := bstep (se 1 (by rfl) ⟨8115197, by rfl⟩ : syracuseStep 10820263 = 16230395) B16230395
theorem B9010115 : Blo 1778090 9010115 := bstep (se 1 (by rfl) ⟨6757586, by rfl⟩ : syracuseStep 9010115 = 13515173) B13515173
theorem B2850871 : Blo 1778090 2850871 := bstep (se 1 (by rfl) ⟨2138153, by rfl⟩ : syracuseStep 2850871 = 4276307) B4276307
theorem B14427017 : Blo 1778090 14427017 := bstep (se 2 (by rfl) ⟨5410131, by rfl⟩ : syracuseStep 14427017 = 10820263) B10820263
theorem B1779247 : Blo 1778090 1779247 := bstep (se 1 (by rfl) ⟨1334435, by rfl⟩ : syracuseStep 1779247 = 2668871) B2668871
theorem B10126903 : Blo 1778090 10126903 := bstep (se 1 (by rfl) ⟨7595177, by rfl⟩ : syracuseStep 10126903 = 15190355) B15190355
theorem B9127607 : Blo 1778090 9127607 := bstep (se 1 (by rfl) ⟨6845705, by rfl⟩ : syracuseStep 9127607 = 13691411) B13691411
theorem B6006743 : Blo 1778090 6006743 := bstep (se 1 (by rfl) ⟨4505057, by rfl⟩ : syracuseStep 6006743 = 9010115) B9010115
theorem B10129819 : Blo 1778090 10129819 := bstep (se 1 (by rfl) ⟨7597364, by rfl⟩ : syracuseStep 10129819 = 15194729) B15194729
theorem B9007847 : Blo 1778090 9007847 := bstep (se 1 (by rfl) ⟨6755885, by rfl⟩ : syracuseStep 9007847 = 13511771) B13511771
theorem B5632807 : Blo 1778090 5632807 := bstep (se 1 (by rfl) ⟨4224605, by rfl⟩ : syracuseStep 5632807 = 8449211) B8449211
theorem B10132735 : Blo 1778090 10132735 := bstep (se 1 (by rfl) ⟨7599551, by rfl⟩ : syracuseStep 10132735 = 15199103) B15199103
theorem B11394407 : Blo 1778090 11394407 := bstep (se 1 (by rfl) ⟨8545805, by rfl⟩ : syracuseStep 11394407 = 17091611) B17091611
theorem B3801161 : Blo 1778090 3801161 := bstep (se 2 (by rfl) ⟨1425435, by rfl⟩ : syracuseStep 3801161 = 2850871) B2850871
theorem B6005231 : Blo 1778090 6005231 := bstep (se 1 (by rfl) ⟨4503923, by rfl⟩ : syracuseStep 6005231 = 9007847) B9007847
theorem B9618011 : Blo 1778090 9618011 := bstep (se 1 (by rfl) ⟨7213508, by rfl⟩ : syracuseStep 9618011 = 14427017) B14427017
theorem B13510313 : Blo 1778090 13510313 := bstep (se 2 (by rfl) ⟨5066367, by rfl⟩ : syracuseStep 13510313 = 10132735) B10132735
theorem B24340285 : Blo 1778090 24340285 := bstep (se 3 (by rfl) ⟨4563803, by rfl⟩ : syracuseStep 24340285 = 9127607) B9127607
theorem B13502537 : Blo 1778090 13502537 := bstep (se 2 (by rfl) ⟨5063451, by rfl⟩ : syracuseStep 13502537 = 10126903) B10126903
theorem B7596271 : Blo 1778090 7596271 := bstep (se 1 (by rfl) ⟨5697203, by rfl⟩ : syracuseStep 7596271 = 11394407) B11394407
theorem B13506425 : Blo 1778090 13506425 := bstep (se 2 (by rfl) ⟨5064909, by rfl⟩ : syracuseStep 13506425 = 10129819) B10129819
theorem B7510409 : Blo 1778090 7510409 := bstep (se 2 (by rfl) ⟨2816403, by rfl⟩ : syracuseStep 7510409 = 5632807) B5632807
theorem B4004495 : Blo 1778090 4004495 := bstep (se 1 (by rfl) ⟨3003371, by rfl⟩ : syracuseStep 4004495 = 6006743) B6006743
theorem B9004283 : Blo 1778090 9004283 := bstep (se 1 (by rfl) ⟨6753212, by rfl⟩ : syracuseStep 9004283 = 13506425) B13506425
theorem B5006939 : Blo 1778090 5006939 := bstep (se 1 (by rfl) ⟨3755204, by rfl⟩ : syracuseStep 5006939 = 7510409) B7510409
theorem B2534107 : Blo 1778090 2534107 := bstep (se 1 (by rfl) ⟨1900580, by rfl⟩ : syracuseStep 2534107 = 3801161) B3801161
theorem B10128361 : Blo 1778090 10128361 := bstep (se 2 (by rfl) ⟨3798135, by rfl⟩ : syracuseStep 10128361 = 7596271) B7596271
theorem B9006875 : Blo 1778090 9006875 := bstep (se 1 (by rfl) ⟨6755156, by rfl⟩ : syracuseStep 9006875 = 13510313) B13510313
theorem B32453713 : Blo 1778090 32453713 := bstep (se 2 (by rfl) ⟨12170142, by rfl⟩ : syracuseStep 32453713 = 24340285) B24340285
theorem B4003487 : Blo 1778090 4003487 := bstep (se 1 (by rfl) ⟨3002615, by rfl⟩ : syracuseStep 4003487 = 6005231) B6005231
theorem B6412007 : Blo 1778090 6412007 := bstep (se 1 (by rfl) ⟨4809005, by rfl⟩ : syracuseStep 6412007 = 9618011) B9618011
theorem B9001691 : Blo 1778090 9001691 := bstep (se 1 (by rfl) ⟨6751268, by rfl⟩ : syracuseStep 9001691 = 13502537) B13502537
theorem B2669663 : Blo 1778090 2669663 := bstep (se 1 (by rfl) ⟨2002247, by rfl⟩ : syracuseStep 2669663 = 4004495) B4004495
theorem B43271617 : Blo 1778090 43271617 := bstep (se 2 (by rfl) ⟨16226856, by rfl⟩ : syracuseStep 43271617 = 32453713) B32453713
theorem B17098685 : Blo 1778090 17098685 := bstep (se 3 (by rfl) ⟨3206003, by rfl⟩ : syracuseStep 17098685 = 6412007) B6412007
theorem B1779775 : Blo 1778090 1779775 := bstep (se 1 (by rfl) ⟨1334831, by rfl⟩ : syracuseStep 1779775 = 2669663) B2669663
theorem B3378809 : Blo 1778090 3378809 := bstep (se 2 (by rfl) ⟨1267053, by rfl⟩ : syracuseStep 3378809 = 2534107) B2534107
theorem B13504481 : Blo 1778090 13504481 := bstep (se 2 (by rfl) ⟨5064180, by rfl⟩ : syracuseStep 13504481 = 10128361) B10128361
theorem B6001127 : Blo 1778090 6001127 := bstep (se 1 (by rfl) ⟨4500845, by rfl⟩ : syracuseStep 6001127 = 9001691) B9001691
theorem B6002855 : Blo 1778090 6002855 := bstep (se 1 (by rfl) ⟨4502141, by rfl⟩ : syracuseStep 6002855 = 9004283) B9004283
theorem B2668991 : Blo 1778090 2668991 := bstep (se 1 (by rfl) ⟨2001743, by rfl⟩ : syracuseStep 2668991 = 4003487) B4003487
theorem B13351837 : Blo 1778090 13351837 := bstep (se 3 (by rfl) ⟨2503469, by rfl⟩ : syracuseStep 13351837 = 5006939) B5006939
theorem B6004583 : Blo 1778090 6004583 := bstep (se 1 (by rfl) ⟨4503437, by rfl⟩ : syracuseStep 6004583 = 9006875) B9006875
theorem B17802449 : Blo 1778090 17802449 := bstep (se 2 (by rfl) ⟨6675918, by rfl⟩ : syracuseStep 17802449 = 13351837) B13351837
theorem B1779327 : Blo 1778090 1779327 := bstep (se 1 (by rfl) ⟨1334495, by rfl⟩ : syracuseStep 1779327 = 2668991) B2668991
theorem B4000751 : Blo 1778090 4000751 := bstep (se 1 (by rfl) ⟨3000563, by rfl⟩ : syracuseStep 4000751 = 6001127) B6001127
theorem B11399123 : Blo 1778090 11399123 := bstep (se 1 (by rfl) ⟨8549342, by rfl⟩ : syracuseStep 11399123 = 17098685) B17098685
theorem B4001903 : Blo 1778090 4001903 := bstep (se 1 (by rfl) ⟨3001427, by rfl⟩ : syracuseStep 4001903 = 6002855) B6002855
theorem B4003055 : Blo 1778090 4003055 := bstep (se 1 (by rfl) ⟨3002291, by rfl⟩ : syracuseStep 4003055 = 6004583) B6004583
theorem B57695489 : Blo 1778090 57695489 := bstep (se 2 (by rfl) ⟨21635808, by rfl⟩ : syracuseStep 57695489 = 43271617) B43271617
theorem B2252539 : Blo 1778090 2252539 := bstep (se 1 (by rfl) ⟨1689404, by rfl⟩ : syracuseStep 2252539 = 3378809) B3378809
theorem B9002987 : Blo 1778090 9002987 := bstep (se 1 (by rfl) ⟨6752240, by rfl⟩ : syracuseStep 9002987 = 13504481) B13504481
theorem B38463659 : Blo 1778090 38463659 := bstep (se 1 (by rfl) ⟨28847744, by rfl⟩ : syracuseStep 38463659 = 57695489) B57695489
theorem B2667167 : Blo 1778090 2667167 := bstep (se 1 (by rfl) ⟨2000375, by rfl⟩ : syracuseStep 2667167 = 4000751) B4000751
theorem B3003385 : Blo 1778090 3003385 := bstep (se 2 (by rfl) ⟨1126269, by rfl⟩ : syracuseStep 3003385 = 2252539) B2252539
theorem B7599415 : Blo 1778090 7599415 := bstep (se 1 (by rfl) ⟨5699561, by rfl⟩ : syracuseStep 7599415 = 11399123) B11399123
theorem B6001991 : Blo 1778090 6001991 := bstep (se 1 (by rfl) ⟨4501493, by rfl⟩ : syracuseStep 6001991 = 9002987) B9002987
theorem B2667935 : Blo 1778090 2667935 := bstep (se 1 (by rfl) ⟨2000951, by rfl⟩ : syracuseStep 2667935 = 4001903) B4001903
theorem B11868299 : Blo 1778090 11868299 := bstep (se 1 (by rfl) ⟨8901224, by rfl⟩ : syracuseStep 11868299 = 17802449) B17802449
theorem B2668703 : Blo 1778090 2668703 := bstep (se 1 (by rfl) ⟨2001527, by rfl⟩ : syracuseStep 2668703 = 4003055) B4003055
theorem B1778111 : Blo 1778090 1778111 := bstep (se 1 (by rfl) ⟨1333583, by rfl⟩ : syracuseStep 1778111 = 2667167) B2667167
theorem B1778623 : Blo 1778090 1778623 := bstep (se 1 (by rfl) ⟨1333967, by rfl⟩ : syracuseStep 1778623 = 2667935) B2667935
theorem B1779135 : Blo 1778090 1779135 := bstep (se 1 (by rfl) ⟨1334351, by rfl⟩ : syracuseStep 1779135 = 2668703) B2668703
theorem B25642439 : Blo 1778090 25642439 := bstep (se 1 (by rfl) ⟨19231829, by rfl⟩ : syracuseStep 25642439 = 38463659) B38463659
theorem B4001327 : Blo 1778090 4001327 := bstep (se 1 (by rfl) ⟨3000995, by rfl⟩ : syracuseStep 4001327 = 6001991) B6001991
theorem B4004513 : Blo 1778090 4004513 := bstep (se 2 (by rfl) ⟨1501692, by rfl⟩ : syracuseStep 4004513 = 3003385) B3003385
theorem B7912199 : Blo 1778090 7912199 := bstep (se 1 (by rfl) ⟨5934149, by rfl⟩ : syracuseStep 7912199 = 11868299) B11868299
theorem B10132553 : Blo 1778090 10132553 := bstep (se 2 (by rfl) ⟨3799707, by rfl⟩ : syracuseStep 10132553 = 7599415) B7599415
theorem B21099197 : Blo 1778090 21099197 := bstep (se 3 (by rfl) ⟨3956099, by rfl⟩ : syracuseStep 21099197 = 7912199) B7912199
theorem B6755035 : Blo 1778090 6755035 := bstep (se 1 (by rfl) ⟨5066276, by rfl⟩ : syracuseStep 6755035 = 10132553) B10132553
theorem B2667551 : Blo 1778090 2667551 := bstep (se 1 (by rfl) ⟨2000663, by rfl⟩ : syracuseStep 2667551 = 4001327) B4001327
theorem B17094959 : Blo 1778090 17094959 := bstep (se 1 (by rfl) ⟨12821219, by rfl⟩ : syracuseStep 17094959 = 25642439) B25642439
theorem B2669675 : Blo 1778090 2669675 := bstep (se 1 (by rfl) ⟨2002256, by rfl⟩ : syracuseStep 2669675 = 4004513) B4004513
theorem B14066131 : Blo 1778090 14066131 := bstep (se 1 (by rfl) ⟨10549598, by rfl⟩ : syracuseStep 14066131 = 21099197) B21099197
theorem B1778367 : Blo 1778090 1778367 := bstep (se 1 (by rfl) ⟨1333775, by rfl⟩ : syracuseStep 1778367 = 2667551) B2667551
theorem B11396639 : Blo 1778090 11396639 := bstep (se 1 (by rfl) ⟨8547479, by rfl⟩ : syracuseStep 11396639 = 17094959) B17094959
theorem B1779783 : Blo 1778090 1779783 := bstep (se 1 (by rfl) ⟨1334837, by rfl⟩ : syracuseStep 1779783 = 2669675) B2669675
theorem B9006713 : Blo 1778090 9006713 := bstep (se 2 (by rfl) ⟨3377517, by rfl⟩ : syracuseStep 9006713 = 6755035) B6755035
theorem B18754841 : Blo 1778090 18754841 := bstep (se 2 (by rfl) ⟨7033065, by rfl⟩ : syracuseStep 18754841 = 14066131) B14066131
theorem B7597759 : Blo 1778090 7597759 := bstep (se 1 (by rfl) ⟨5698319, by rfl⟩ : syracuseStep 7597759 = 11396639) B11396639
theorem B6004475 : Blo 1778090 6004475 := bstep (se 1 (by rfl) ⟨4503356, by rfl⟩ : syracuseStep 6004475 = 9006713) B9006713
theorem B50012909 : Blo 1778090 50012909 := bstep (se 3 (by rfl) ⟨9377420, by rfl⟩ : syracuseStep 50012909 = 18754841) B18754841
theorem B10130345 : Blo 1778090 10130345 := bstep (se 2 (by rfl) ⟨3798879, by rfl⟩ : syracuseStep 10130345 = 7597759) B7597759
theorem B4002983 : Blo 1778090 4002983 := bstep (se 1 (by rfl) ⟨3002237, by rfl⟩ : syracuseStep 4002983 = 6004475) B6004475
theorem B33341939 : Blo 1778090 33341939 := bstep (se 1 (by rfl) ⟨25006454, by rfl⟩ : syracuseStep 33341939 = 50012909) B50012909
theorem B6753563 : Blo 1778090 6753563 := bstep (se 1 (by rfl) ⟨5065172, by rfl⟩ : syracuseStep 6753563 = 10130345) B10130345
theorem B2668655 : Blo 1778090 2668655 := bstep (se 1 (by rfl) ⟨2001491, by rfl⟩ : syracuseStep 2668655 = 4002983) B4002983
theorem B1779103 : Blo 1778090 1779103 := bstep (se 1 (by rfl) ⟨1334327, by rfl⟩ : syracuseStep 1779103 = 2668655) B2668655
theorem B22227959 : Blo 1778090 22227959 := bstep (se 1 (by rfl) ⟨16670969, by rfl⟩ : syracuseStep 22227959 = 33341939) B33341939
theorem B4502375 : Blo 1778090 4502375 := bstep (se 1 (by rfl) ⟨3376781, by rfl⟩ : syracuseStep 4502375 = 6753563) B6753563
theorem B3001583 : Blo 1778090 3001583 := bstep (se 1 (by rfl) ⟨2251187, by rfl⟩ : syracuseStep 3001583 = 4502375) B4502375
theorem B14818639 : Blo 1778090 14818639 := bstep (se 1 (by rfl) ⟨11113979, by rfl⟩ : syracuseStep 14818639 = 22227959) B22227959
theorem B2001055 : Blo 1778090 2001055 := bstep (se 1 (by rfl) ⟨1500791, by rfl⟩ : syracuseStep 2001055 = 3001583) B3001583
theorem B19758185 : Blo 1778090 19758185 := bstep (se 2 (by rfl) ⟨7409319, by rfl⟩ : syracuseStep 19758185 = 14818639) B14818639
theorem B2668073 : Blo 1778090 2668073 := bstep (se 2 (by rfl) ⟨1000527, by rfl⟩ : syracuseStep 2668073 = 2001055) B2001055
theorem B13172123 : Blo 1778090 13172123 := bstep (se 1 (by rfl) ⟨9879092, by rfl⟩ : syracuseStep 13172123 = 19758185) B19758185
theorem B1778715 : Blo 1778090 1778715 := bstep (se 1 (by rfl) ⟨1334036, by rfl⟩ : syracuseStep 1778715 = 2668073) B2668073
theorem B8781415 : Blo 1778090 8781415 := bstep (se 1 (by rfl) ⟨6586061, by rfl⟩ : syracuseStep 8781415 = 13172123) B13172123
theorem B46834213 : Blo 1778090 46834213 := bstep (se 4 (by rfl) ⟨4390707, by rfl⟩ : syracuseStep 46834213 = 8781415) B8781415
theorem B62445617 : Blo 1778090 62445617 := bstep (se 2 (by rfl) ⟨23417106, by rfl⟩ : syracuseStep 62445617 = 46834213) B46834213
theorem B41630411 : Blo 1778090 41630411 := bstep (se 1 (by rfl) ⟨31222808, by rfl⟩ : syracuseStep 41630411 = 62445617) B62445617
theorem B27753607 : Blo 1778090 27753607 := bstep (se 1 (by rfl) ⟨20815205, by rfl⟩ : syracuseStep 27753607 = 41630411) B41630411
theorem B148019237 : Blo 1778090 148019237 := bstep (se 4 (by rfl) ⟨13876803, by rfl⟩ : syracuseStep 148019237 = 27753607) B27753607
theorem B98679491 : Blo 1778090 98679491 := bstep (se 1 (by rfl) ⟨74009618, by rfl⟩ : syracuseStep 98679491 = 148019237) B148019237
theorem B65786327 : Blo 1778090 65786327 := bstep (se 1 (by rfl) ⟨49339745, by rfl⟩ : syracuseStep 65786327 = 98679491) B98679491
theorem B43857551 : Blo 1778090 43857551 := bstep (se 1 (by rfl) ⟨32893163, by rfl⟩ : syracuseStep 43857551 = 65786327) B65786327
theorem B116953469 : Blo 1778090 116953469 := bstep (se 3 (by rfl) ⟨21928775, by rfl⟩ : syracuseStep 116953469 = 43857551) B43857551
theorem B77968979 : Blo 1778090 77968979 := bstep (se 1 (by rfl) ⟨58476734, by rfl⟩ : syracuseStep 77968979 = 116953469) B116953469
theorem B51979319 : Blo 1778090 51979319 := bstep (se 1 (by rfl) ⟨38984489, by rfl⟩ : syracuseStep 51979319 = 77968979) B77968979
theorem B34652879 : Blo 1778090 34652879 := bstep (se 1 (by rfl) ⟨25989659, by rfl⟩ : syracuseStep 34652879 = 51979319) B51979319
theorem B23101919 : Blo 1778090 23101919 := bstep (se 1 (by rfl) ⟨17326439, by rfl⟩ : syracuseStep 23101919 = 34652879) B34652879
theorem B15401279 : Blo 1778090 15401279 := bstep (se 1 (by rfl) ⟨11550959, by rfl⟩ : syracuseStep 15401279 = 23101919) B23101919
theorem B10267519 : Blo 1778090 10267519 := bstep (se 1 (by rfl) ⟨7700639, by rfl⟩ : syracuseStep 10267519 = 15401279) B15401279
theorem B13690025 : Blo 1778090 13690025 := bstep (se 2 (by rfl) ⟨5133759, by rfl⟩ : syracuseStep 13690025 = 10267519) B10267519
theorem B9126683 : Blo 1778090 9126683 := bstep (se 1 (by rfl) ⟨6845012, by rfl⟩ : syracuseStep 9126683 = 13690025) B13690025
theorem B6084455 : Blo 1778090 6084455 := bstep (se 1 (by rfl) ⟨4563341, by rfl⟩ : syracuseStep 6084455 = 9126683) B9126683
theorem B16225213 : Blo 1778090 16225213 := bstep (se 3 (by rfl) ⟨3042227, by rfl⟩ : syracuseStep 16225213 = 6084455) B6084455
theorem B21633617 : Blo 1778090 21633617 := bstep (se 2 (by rfl) ⟨8112606, by rfl⟩ : syracuseStep 21633617 = 16225213) B16225213
theorem B14422411 : Blo 1778090 14422411 := bstep (se 1 (by rfl) ⟨10816808, by rfl⟩ : syracuseStep 14422411 = 21633617) B21633617
theorem B19229881 : Blo 1778090 19229881 := bstep (se 2 (by rfl) ⟨7211205, by rfl⟩ : syracuseStep 19229881 = 14422411) B14422411
theorem B25639841 : Blo 1778090 25639841 := bstep (se 2 (by rfl) ⟨9614940, by rfl⟩ : syracuseStep 25639841 = 19229881) B19229881
theorem B17093227 : Blo 1778090 17093227 := bstep (se 1 (by rfl) ⟨12819920, by rfl⟩ : syracuseStep 17093227 = 25639841) B25639841
theorem B22790969 : Blo 1778090 22790969 := bstep (se 2 (by rfl) ⟨8546613, by rfl⟩ : syracuseStep 22790969 = 17093227) B17093227
theorem B15193979 : Blo 1778090 15193979 := bstep (se 1 (by rfl) ⟨11395484, by rfl⟩ : syracuseStep 15193979 = 22790969) B22790969
theorem B10129319 : Blo 1778090 10129319 := bstep (se 1 (by rfl) ⟨7596989, by rfl⟩ : syracuseStep 10129319 = 15193979) B15193979
theorem B6752879 : Blo 1778090 6752879 := bstep (se 1 (by rfl) ⟨5064659, by rfl⟩ : syracuseStep 6752879 = 10129319) B10129319
theorem B4501919 : Blo 1778090 4501919 := bstep (se 1 (by rfl) ⟨3376439, by rfl⟩ : syracuseStep 4501919 = 6752879) B6752879
theorem B3001279 : Blo 1778090 3001279 := bstep (se 1 (by rfl) ⟨2250959, by rfl⟩ : syracuseStep 3001279 = 4501919) B4501919
theorem B4001705 : Blo 1778090 4001705 := bstep (se 2 (by rfl) ⟨1500639, by rfl⟩ : syracuseStep 4001705 = 3001279) B3001279
theorem B2667803 : Blo 1778090 2667803 := bstep (se 1 (by rfl) ⟨2000852, by rfl⟩ : syracuseStep 2667803 = 4001705) B4001705
theorem B1778535 : Blo 1778090 1778535 := bstep (se 1 (by rfl) ⟨1333901, by rfl⟩ : syracuseStep 1778535 = 2667803) B2667803

theorem C0 (j : ℕ) (h1 : 444522 ≤ j) (h2 : j ≤ 445021) : Blo 1778090 (4 * j + 3) := by
  interval_cases j
  · exact B1778091
  · exact B1778095
  · exact B1778099
  · exact B1778103
  · exact B1778107
  · exact B1778111
  · exact B1778115
  · exact B1778119
  · exact B1778123
  · exact B1778127
  · exact B1778131
  · exact B1778135
  · exact B1778139
  · exact B1778143
  · exact B1778147
  · exact B1778151
  · exact B1778155
  · exact B1778159
  · exact B1778163
  · exact B1778167
  · exact B1778171
  · exact B1778175
  · exact B1778179
  · exact B1778183
  · exact B1778187
  · exact B1778191
  · exact B1778195
  · exact B1778199
  · exact B1778203
  · exact B1778207
  · exact B1778211
  · exact B1778215
  · exact B1778219
  · exact B1778223
  · exact B1778227
  · exact B1778231
  · exact B1778235
  · exact B1778239
  · exact B1778243
  · exact B1778247
  · exact B1778251
  · exact B1778255
  · exact B1778259
  · exact B1778263
  · exact B1778267
  · exact B1778271
  · exact B1778275
  · exact B1778279
  · exact B1778283
  · exact B1778287
  · exact B1778291
  · exact B1778295
  · exact B1778299
  · exact B1778303
  · exact B1778307
  · exact B1778311
  · exact B1778315
  · exact B1778319
  · exact B1778323
  · exact B1778327
  · exact B1778331
  · exact B1778335
  · exact B1778339
  · exact B1778343
  · exact B1778347
  · exact B1778351
  · exact B1778355
  · exact B1778359
  · exact B1778363
  · exact B1778367
  · exact B1778371
  · exact B1778375
  · exact B1778379
  · exact B1778383
  · exact B1778387
  · exact B1778391
  · exact B1778395
  · exact B1778399
  · exact B1778403
  · exact B1778407
  · exact B1778411
  · exact B1778415
  · exact B1778419
  · exact B1778423
  · exact B1778427
  · exact B1778431
  · exact B1778435
  · exact B1778439
  · exact B1778443
  · exact B1778447
  · exact B1778451
  · exact B1778455
  · exact B1778459
  · exact B1778463
  · exact B1778467
  · exact B1778471
  · exact B1778475
  · exact B1778479
  · exact B1778483
  · exact B1778487
  · exact B1778491
  · exact B1778495
  · exact B1778499
  · exact B1778503
  · exact B1778507
  · exact B1778511
  · exact B1778515
  · exact B1778519
  · exact B1778523
  · exact B1778527
  · exact B1778531
  · exact B1778535
  · exact B1778539
  · exact B1778543
  · exact B1778547
  · exact B1778551
  · exact B1778555
  · exact B1778559
  · exact B1778563
  · exact B1778567
  · exact B1778571
  · exact B1778575
  · exact B1778579
  · exact B1778583
  · exact B1778587
  · exact B1778591
  · exact B1778595
  · exact B1778599
  · exact B1778603
  · exact B1778607
  · exact B1778611
  · exact B1778615
  · exact B1778619
  · exact B1778623
  · exact B1778627
  · exact B1778631
  · exact B1778635
  · exact B1778639
  · exact B1778643
  · exact B1778647
  · exact B1778651
  · exact B1778655
  · exact B1778659
  · exact B1778663
  · exact B1778667
  · exact B1778671
  · exact B1778675
  · exact B1778679
  · exact B1778683
  · exact B1778687
  · exact B1778691
  · exact B1778695
  · exact B1778699
  · exact B1778703
  · exact B1778707
  · exact B1778711
  · exact B1778715
  · exact B1778719
  · exact B1778723
  · exact B1778727
  · exact B1778731
  · exact B1778735
  · exact B1778739
  · exact B1778743
  · exact B1778747
  · exact B1778751
  · exact B1778755
  · exact B1778759
  · exact B1778763
  · exact B1778767
  · exact B1778771
  · exact B1778775
  · exact B1778779
  · exact B1778783
  · exact B1778787
  · exact B1778791
  · exact B1778795
  · exact B1778799
  · exact B1778803
  · exact B1778807
  · exact B1778811
  · exact B1778815
  · exact B1778819
  · exact B1778823
  · exact B1778827
  · exact B1778831
  · exact B1778835
  · exact B1778839
  · exact B1778843
  · exact B1778847
  · exact B1778851
  · exact B1778855
  · exact B1778859
  · exact B1778863
  · exact B1778867
  · exact B1778871
  · exact B1778875
  · exact B1778879
  · exact B1778883
  · exact B1778887
  · exact B1778891
  · exact B1778895
  · exact B1778899
  · exact B1778903
  · exact B1778907
  · exact B1778911
  · exact B1778915
  · exact B1778919
  · exact B1778923
  · exact B1778927
  · exact B1778931
  · exact B1778935
  · exact B1778939
  · exact B1778943
  · exact B1778947
  · exact B1778951
  · exact B1778955
  · exact B1778959
  · exact B1778963
  · exact B1778967
  · exact B1778971
  · exact B1778975
  · exact B1778979
  · exact B1778983
  · exact B1778987
  · exact B1778991
  · exact B1778995
  · exact B1778999
  · exact B1779003
  · exact B1779007
  · exact B1779011
  · exact B1779015
  · exact B1779019
  · exact B1779023
  · exact B1779027
  · exact B1779031
  · exact B1779035
  · exact B1779039
  · exact B1779043
  · exact B1779047
  · exact B1779051
  · exact B1779055
  · exact B1779059
  · exact B1779063
  · exact B1779067
  · exact B1779071
  · exact B1779075
  · exact B1779079
  · exact B1779083
  · exact B1779087
  · exact B1779091
  · exact B1779095
  · exact B1779099
  · exact B1779103
  · exact B1779107
  · exact B1779111
  · exact B1779115
  · exact B1779119
  · exact B1779123
  · exact B1779127
  · exact B1779131
  · exact B1779135
  · exact B1779139
  · exact B1779143
  · exact B1779147
  · exact B1779151
  · exact B1779155
  · exact B1779159
  · exact B1779163
  · exact B1779167
  · exact B1779171
  · exact B1779175
  · exact B1779179
  · exact B1779183
  · exact B1779187
  · exact B1779191
  · exact B1779195
  · exact B1779199
  · exact B1779203
  · exact B1779207
  · exact B1779211
  · exact B1779215
  · exact B1779219
  · exact B1779223
  · exact B1779227
  · exact B1779231
  · exact B1779235
  · exact B1779239
  · exact B1779243
  · exact B1779247
  · exact B1779251
  · exact B1779255
  · exact B1779259
  · exact B1779263
  · exact B1779267
  · exact B1779271
  · exact B1779275
  · exact B1779279
  · exact B1779283
  · exact B1779287
  · exact B1779291
  · exact B1779295
  · exact B1779299
  · exact B1779303
  · exact B1779307
  · exact B1779311
  · exact B1779315
  · exact B1779319
  · exact B1779323
  · exact B1779327
  · exact B1779331
  · exact B1779335
  · exact B1779339
  · exact B1779343
  · exact B1779347
  · exact B1779351
  · exact B1779355
  · exact B1779359
  · exact B1779363
  · exact B1779367
  · exact B1779371
  · exact B1779375
  · exact B1779379
  · exact B1779383
  · exact B1779387
  · exact B1779391
  · exact B1779395
  · exact B1779399
  · exact B1779403
  · exact B1779407
  · exact B1779411
  · exact B1779415
  · exact B1779419
  · exact B1779423
  · exact B1779427
  · exact B1779431
  · exact B1779435
  · exact B1779439
  · exact B1779443
  · exact B1779447
  · exact B1779451
  · exact B1779455
  · exact B1779459
  · exact B1779463
  · exact B1779467
  · exact B1779471
  · exact B1779475
  · exact B1779479
  · exact B1779483
  · exact B1779487
  · exact B1779491
  · exact B1779495
  · exact B1779499
  · exact B1779503
  · exact B1779507
  · exact B1779511
  · exact B1779515
  · exact B1779519
  · exact B1779523
  · exact B1779527
  · exact B1779531
  · exact B1779535
  · exact B1779539
  · exact B1779543
  · exact B1779547
  · exact B1779551
  · exact B1779555
  · exact B1779559
  · exact B1779563
  · exact B1779567
  · exact B1779571
  · exact B1779575
  · exact B1779579
  · exact B1779583
  · exact B1779587
  · exact B1779591
  · exact B1779595
  · exact B1779599
  · exact B1779603
  · exact B1779607
  · exact B1779611
  · exact B1779615
  · exact B1779619
  · exact B1779623
  · exact B1779627
  · exact B1779631
  · exact B1779635
  · exact B1779639
  · exact B1779643
  · exact B1779647
  · exact B1779651
  · exact B1779655
  · exact B1779659
  · exact B1779663
  · exact B1779667
  · exact B1779671
  · exact B1779675
  · exact B1779679
  · exact B1779683
  · exact B1779687
  · exact B1779691
  · exact B1779695
  · exact B1779699
  · exact B1779703
  · exact B1779707
  · exact B1779711
  · exact B1779715
  · exact B1779719
  · exact B1779723
  · exact B1779727
  · exact B1779731
  · exact B1779735
  · exact B1779739
  · exact B1779743
  · exact B1779747
  · exact B1779751
  · exact B1779755
  · exact B1779759
  · exact B1779763
  · exact B1779767
  · exact B1779771
  · exact B1779775
  · exact B1779779
  · exact B1779783
  · exact B1779787
  · exact B1779791
  · exact B1779795
  · exact B1779799
  · exact B1779803
  · exact B1779807
  · exact B1779811
  · exact B1779815
  · exact B1779819
  · exact B1779823
  · exact B1779827
  · exact B1779831
  · exact B1779835
  · exact B1779839
  · exact B1779843
  · exact B1779847
  · exact B1779851
  · exact B1779855
  · exact B1779859
  · exact B1779863
  · exact B1779867
  · exact B1779871
  · exact B1779875
  · exact B1779879
  · exact B1779883
  · exact B1779887
  · exact B1779891
  · exact B1779895
  · exact B1779899
  · exact B1779903
  · exact B1779907
  · exact B1779911
  · exact B1779915
  · exact B1779919
  · exact B1779923
  · exact B1779927
  · exact B1779931
  · exact B1779935
  · exact B1779939
  · exact B1779943
  · exact B1779947
  · exact B1779951
  · exact B1779955
  · exact B1779959
  · exact B1779963
  · exact B1779967
  · exact B1779971
  · exact B1779975
  · exact B1779979
  · exact B1779983
  · exact B1779987
  · exact B1779991
  · exact B1779995
  · exact B1779999
  · exact B1780003
  · exact B1780007
  · exact B1780011
  · exact B1780015
  · exact B1780019
  · exact B1780023
  · exact B1780027
  · exact B1780031
  · exact B1780035
  · exact B1780039
  · exact B1780043
  · exact B1780047
  · exact B1780051
  · exact B1780055
  · exact B1780059
  · exact B1780063
  · exact B1780067
  · exact B1780071
  · exact B1780075
  · exact B1780079
  · exact B1780083
  · exact B1780087

theorem solution (m : ℕ) (hlo : 1778090 ≤ m) (hhi : m ≤ 1780090) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 444522 ≤ j := by omega
    have hj2 : j ≤ 445021 := by omega
    have hb : Blo 1778090 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
