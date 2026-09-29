-- Prove2me | solution 1 for syracuse_descends_range_1271954_1273954
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:11:29.183974+00:00
-- url     : https://prove2.me/submissions/2afe9dea-1028-48fa-8f40-488be9607f5b

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


theorem B1908749 : Blo 1271954 1908749 := bbase (se 3 (by rfl) ⟨357890, by rfl⟩ : syracuseStep 1908749 = 715781) (by norm_num)
theorem B2719757 : Blo 1271954 2719757 := bbase (se 3 (by rfl) ⟨509954, by rfl⟩ : syracuseStep 2719757 = 1019909) (by norm_num)
theorem B1908773 : Blo 1271954 1908773 := bbase (se 4 (by rfl) ⟨178947, by rfl⟩ : syracuseStep 1908773 = 357895) (by norm_num)
theorem B1908797 : Blo 1271954 1908797 := bbase (se 3 (by rfl) ⟨357899, by rfl⟩ : syracuseStep 1908797 = 715799) (by norm_num)
theorem B1908821 : Blo 1271954 1908821 := bbase (se 8 (by rfl) ⟨11184, by rfl⟩ : syracuseStep 1908821 = 22369) (by norm_num)
theorem B1908845 : Blo 1271954 1908845 := bbase (se 3 (by rfl) ⟨357908, by rfl⟩ : syracuseStep 1908845 = 715817) (by norm_num)
theorem B1908869 : Blo 1271954 1908869 := bbase (se 4 (by rfl) ⟨178956, by rfl⟩ : syracuseStep 1908869 = 357913) (by norm_num)
theorem B1908893 : Blo 1271954 1908893 := bbase (se 3 (by rfl) ⟨357917, by rfl⟩ : syracuseStep 1908893 = 715835) (by norm_num)
theorem B1360037 : Blo 1271954 1360037 := bbase (se 4 (by rfl) ⟨127503, by rfl⟩ : syracuseStep 1360037 = 255007) (by norm_num)
theorem B1908917 : Blo 1271954 1908917 := bbase (se 5 (by rfl) ⟨89480, by rfl⟩ : syracuseStep 1908917 = 178961) (by norm_num)
theorem B2146493 : Blo 1271954 2146493 := bbase (se 3 (by rfl) ⟨402467, by rfl⟩ : syracuseStep 2146493 = 804935) (by norm_num)
theorem B1908941 : Blo 1271954 1908941 := bbase (se 3 (by rfl) ⟨357926, by rfl⟩ : syracuseStep 1908941 = 715853) (by norm_num)
theorem B1908965 : Blo 1271954 1908965 := bbase (se 4 (by rfl) ⟨178965, by rfl⟩ : syracuseStep 1908965 = 357931) (by norm_num)
theorem B1360109 : Blo 1271954 1360109 := bbase (se 3 (by rfl) ⟨255020, by rfl⟩ : syracuseStep 1360109 = 510041) (by norm_num)
theorem B3219709 : Blo 1271954 3219709 := bbase (se 3 (by rfl) ⟨603695, by rfl⟩ : syracuseStep 3219709 = 1207391) (by norm_num)
theorem B1908989 : Blo 1271954 1908989 := bbase (se 3 (by rfl) ⟨357935, by rfl⟩ : syracuseStep 1908989 = 715871) (by norm_num)
theorem B1909013 : Blo 1271954 1909013 := bbase (se 6 (by rfl) ⟨44742, by rfl⟩ : syracuseStep 1909013 = 89485) (by norm_num)
theorem B1909037 : Blo 1271954 1909037 := bbase (se 3 (by rfl) ⟨357944, by rfl⟩ : syracuseStep 1909037 = 715889) (by norm_num)
theorem B2146621 : Blo 1271954 2146621 := bbase (se 3 (by rfl) ⟨402491, by rfl⟩ : syracuseStep 2146621 = 804983) (by norm_num)
theorem B1909061 : Blo 1271954 1909061 := bbase (se 4 (by rfl) ⟨178974, by rfl⟩ : syracuseStep 1909061 = 357949) (by norm_num)
theorem B1909085 : Blo 1271954 1909085 := bbase (se 3 (by rfl) ⟨357953, by rfl⟩ : syracuseStep 1909085 = 715907) (by norm_num)
theorem B3219821 : Blo 1271954 3219821 := bbase (se 3 (by rfl) ⟨603716, by rfl⟩ : syracuseStep 3219821 = 1207433) (by norm_num)
theorem B1909109 : Blo 1271954 1909109 := bbase (se 5 (by rfl) ⟨89489, by rfl⟩ : syracuseStep 1909109 = 178979) (by norm_num)
theorem B1909133 : Blo 1271954 1909133 := bbase (se 3 (by rfl) ⟨357962, by rfl⟩ : syracuseStep 1909133 = 715925) (by norm_num)
theorem B2146709 : Blo 1271954 2146709 := bbase (se 6 (by rfl) ⟨50313, by rfl⟩ : syracuseStep 2146709 = 100627) (by norm_num)
theorem B2417053 : Blo 1271954 2417053 := bbase (se 3 (by rfl) ⟨453197, by rfl⟩ : syracuseStep 2417053 = 906395) (by norm_num)
theorem B1909157 : Blo 1271954 1909157 := bbase (se 4 (by rfl) ⟨178983, by rfl⟩ : syracuseStep 1909157 = 357967) (by norm_num)
theorem B1360297 : Blo 1271954 1360297 := bbase (se 2 (by rfl) ⟨510111, by rfl⟩ : syracuseStep 1360297 = 1020223) (by norm_num)
theorem B1909181 : Blo 1271954 1909181 := bbase (se 3 (by rfl) ⟨357971, by rfl⟩ : syracuseStep 1909181 = 715943) (by norm_num)
theorem B1909205 : Blo 1271954 1909205 := bbase (se 7 (by rfl) ⟨22373, by rfl⟩ : syracuseStep 1909205 = 44747) (by norm_num)
theorem B1909229 : Blo 1271954 1909229 := bbase (se 3 (by rfl) ⟨357980, by rfl⟩ : syracuseStep 1909229 = 715961) (by norm_num)
theorem B1909253 : Blo 1271954 1909253 := bbase (se 4 (by rfl) ⟨178992, by rfl⟩ : syracuseStep 1909253 = 357985) (by norm_num)
theorem B2146837 : Blo 1271954 2146837 := bbase (se 6 (by rfl) ⟨50316, by rfl⟩ : syracuseStep 2146837 = 100633) (by norm_num)
theorem B1909277 : Blo 1271954 1909277 := bbase (se 3 (by rfl) ⟨357989, by rfl⟩ : syracuseStep 1909277 = 715979) (by norm_num)
theorem B3220013 : Blo 1271954 3220013 := bbase (se 3 (by rfl) ⟨603752, by rfl⟩ : syracuseStep 3220013 = 1207505) (by norm_num)
theorem B2417197 : Blo 1271954 2417197 := bbase (se 3 (by rfl) ⟨453224, by rfl⟩ : syracuseStep 2417197 = 906449) (by norm_num)
theorem B1909301 : Blo 1271954 1909301 := bbase (se 5 (by rfl) ⟨89498, by rfl⟩ : syracuseStep 1909301 = 178997) (by norm_num)
theorem B1909325 : Blo 1271954 1909325 := bbase (se 3 (by rfl) ⟨357998, by rfl⟩ : syracuseStep 1909325 = 715997) (by norm_num)
theorem B4833877 : Blo 1271954 4833877 := bbase (se 8 (by rfl) ⟨28323, by rfl⟩ : syracuseStep 4833877 = 56647) (by norm_num)
theorem B1909349 : Blo 1271954 1909349 := bbase (se 4 (by rfl) ⟨179001, by rfl⟩ : syracuseStep 1909349 = 358003) (by norm_num)
theorem B2146925 : Blo 1271954 2146925 := bbase (se 3 (by rfl) ⟨402548, by rfl⟩ : syracuseStep 2146925 = 805097) (by norm_num)
theorem B1909373 : Blo 1271954 1909373 := bbase (se 3 (by rfl) ⟨358007, by rfl⟩ : syracuseStep 1909373 = 716015) (by norm_num)
theorem B4293269 : Blo 1271954 4293269 := bbase (se 6 (by rfl) ⟨100623, by rfl⟩ : syracuseStep 4293269 = 201247) (by norm_num)
theorem B1909397 : Blo 1271954 1909397 := bbase (se 6 (by rfl) ⟨44751, by rfl⟩ : syracuseStep 1909397 = 89503) (by norm_num)
theorem B1909421 : Blo 1271954 1909421 := bbase (se 3 (by rfl) ⟨358016, by rfl⟩ : syracuseStep 1909421 = 716033) (by norm_num)
theorem B1721021 : Blo 1271954 1721021 := bbase (se 3 (by rfl) ⟨322691, by rfl⟩ : syracuseStep 1721021 = 645383) (by norm_num)
theorem B1909445 : Blo 1271954 1909445 := bbase (se 4 (by rfl) ⟨179010, by rfl⟩ : syracuseStep 1909445 = 358021) (by norm_num)
theorem B2417357 : Blo 1271954 2417357 := bbase (se 3 (by rfl) ⟨453254, by rfl⟩ : syracuseStep 2417357 = 906509) (by norm_num)
theorem B1909469 : Blo 1271954 1909469 := bbase (se 3 (by rfl) ⟨358025, by rfl⟩ : syracuseStep 1909469 = 716051) (by norm_num)
theorem B2147053 : Blo 1271954 2147053 := bbase (se 3 (by rfl) ⟨402572, by rfl⟩ : syracuseStep 2147053 = 805145) (by norm_num)
theorem B5300981 : Blo 1271954 5300981 := bbase (se 5 (by rfl) ⟨248483, by rfl⟩ : syracuseStep 5300981 = 496967) (by norm_num)
theorem B1909493 : Blo 1271954 1909493 := bbase (se 5 (by rfl) ⟨89507, by rfl⟩ : syracuseStep 1909493 = 179015) (by norm_num)
theorem B1909517 : Blo 1271954 1909517 := bbase (se 3 (by rfl) ⟨358034, by rfl⟩ : syracuseStep 1909517 = 716069) (by norm_num)
theorem B1909541 : Blo 1271954 1909541 := bbase (se 4 (by rfl) ⟨179019, by rfl⟩ : syracuseStep 1909541 = 358039) (by norm_num)
theorem B1909565 : Blo 1271954 1909565 := bbase (se 3 (by rfl) ⟨358043, by rfl⟩ : syracuseStep 1909565 = 716087) (by norm_num)
theorem B1811269 : Blo 1271954 1811269 := bbase (se 4 (by rfl) ⟨169806, by rfl⟩ : syracuseStep 1811269 = 339613) (by norm_num)
theorem B2147141 : Blo 1271954 2147141 := bbase (se 4 (by rfl) ⟨201294, by rfl⟩ : syracuseStep 2147141 = 402589) (by norm_num)
theorem B1909589 : Blo 1271954 1909589 := bbase (se 9 (by rfl) ⟨5594, by rfl⟩ : syracuseStep 1909589 = 11189) (by norm_num)
theorem B2417501 : Blo 1271954 2417501 := bbase (se 3 (by rfl) ⟨453281, by rfl⟩ : syracuseStep 2417501 = 906563) (by norm_num)
theorem B1909613 : Blo 1271954 1909613 := bbase (se 3 (by rfl) ⟨358052, by rfl⟩ : syracuseStep 1909613 = 716105) (by norm_num)
theorem B2720621 : Blo 1271954 2720621 := bbase (se 3 (by rfl) ⟨510116, by rfl⟩ : syracuseStep 2720621 = 1020233) (by norm_num)
theorem B3220357 : Blo 1271954 3220357 := bbase (se 4 (by rfl) ⟨301908, by rfl⟩ : syracuseStep 3220357 = 603817) (by norm_num)
theorem B1909637 : Blo 1271954 1909637 := bbase (se 4 (by rfl) ⟨179028, by rfl⟩ : syracuseStep 1909637 = 358057) (by norm_num)
theorem B4834181 : Blo 1271954 4834181 := bbase (se 4 (by rfl) ⟨453204, by rfl⟩ : syracuseStep 4834181 = 906409) (by norm_num)
theorem B1909661 : Blo 1271954 1909661 := bbase (se 3 (by rfl) ⟨358061, by rfl⟩ : syracuseStep 1909661 = 716123) (by norm_num)
theorem B1909685 : Blo 1271954 1909685 := bbase (se 5 (by rfl) ⟨89516, by rfl⟩ : syracuseStep 1909685 = 179033) (by norm_num)
theorem B2147269 : Blo 1271954 2147269 := bbase (se 4 (by rfl) ⟨201306, by rfl⟩ : syracuseStep 2147269 = 402613) (by norm_num)
theorem B1909709 : Blo 1271954 1909709 := bbase (se 3 (by rfl) ⟨358070, by rfl⟩ : syracuseStep 1909709 = 716141) (by norm_num)
theorem B6448085 : Blo 1271954 6448085 := bbase (se 7 (by rfl) ⟨75563, by rfl⟩ : syracuseStep 6448085 = 151127) (by norm_num)
theorem B1909733 : Blo 1271954 1909733 := bbase (se 4 (by rfl) ⟨179037, by rfl⟩ : syracuseStep 1909733 = 358075) (by norm_num)
theorem B3220469 : Blo 1271954 3220469 := bbase (se 5 (by rfl) ⟨150959, by rfl⟩ : syracuseStep 3220469 = 301919) (by norm_num)
theorem B3441653 : Blo 1271954 3441653 := bbase (se 5 (by rfl) ⟨161327, by rfl⟩ : syracuseStep 3441653 = 322655) (by norm_num)
theorem B1909757 : Blo 1271954 1909757 := bbase (se 3 (by rfl) ⟨358079, by rfl⟩ : syracuseStep 1909757 = 716159) (by norm_num)
theorem B2720765 : Blo 1271954 2720765 := bbase (se 3 (by rfl) ⟨510143, by rfl⟩ : syracuseStep 2720765 = 1020287) (by norm_num)
theorem B1909781 : Blo 1271954 1909781 := bbase (se 6 (by rfl) ⟨44760, by rfl⟩ : syracuseStep 1909781 = 89521) (by norm_num)
theorem B2147357 : Blo 1271954 2147357 := bbase (se 3 (by rfl) ⟨402629, by rfl⟩ : syracuseStep 2147357 = 805259) (by norm_num)
theorem B1909805 : Blo 1271954 1909805 := bbase (se 3 (by rfl) ⟨358088, by rfl⟩ : syracuseStep 1909805 = 716177) (by norm_num)
theorem B4293701 : Blo 1271954 4293701 := bbase (se 4 (by rfl) ⟨402534, by rfl⟩ : syracuseStep 4293701 = 805069) (by norm_num)
theorem B1909829 : Blo 1271954 1909829 := bbase (se 4 (by rfl) ⟨179046, by rfl⟩ : syracuseStep 1909829 = 358093) (by norm_num)
theorem B1909853 : Blo 1271954 1909853 := bbase (se 3 (by rfl) ⟨358097, by rfl⟩ : syracuseStep 1909853 = 716195) (by norm_num)
theorem B6882421 : Blo 1271954 6882421 := bbase (se 5 (by rfl) ⟨322613, by rfl⟩ : syracuseStep 6882421 = 645227) (by norm_num)
theorem B1909877 : Blo 1271954 1909877 := bbase (se 5 (by rfl) ⟨89525, by rfl⟩ : syracuseStep 1909877 = 179051) (by norm_num)
theorem B2417789 : Blo 1271954 2417789 := bbase (se 3 (by rfl) ⟨453335, by rfl⟩ : syracuseStep 2417789 = 906671) (by norm_num)
theorem B1909901 : Blo 1271954 1909901 := bbase (se 3 (by rfl) ⟨358106, by rfl⟩ : syracuseStep 1909901 = 716213) (by norm_num)
theorem B2147485 : Blo 1271954 2147485 := bbase (se 3 (by rfl) ⟨402653, by rfl⟩ : syracuseStep 2147485 = 805307) (by norm_num)
theorem B1909925 : Blo 1271954 1909925 := bbase (se 4 (by rfl) ⟨179055, by rfl⟩ : syracuseStep 1909925 = 358111) (by norm_num)
theorem B1451177 : Blo 1271954 1451177 := bbase (se 2 (by rfl) ⟨544191, by rfl⟩ : syracuseStep 1451177 = 1088383) (by norm_num)
theorem B3220661 : Blo 1271954 3220661 := bbase (se 5 (by rfl) ⟨150968, by rfl⟩ : syracuseStep 3220661 = 301937) (by norm_num)
theorem B6120629 : Blo 1271954 6120629 := bbase (se 5 (by rfl) ⟨286904, by rfl⟩ : syracuseStep 6120629 = 573809) (by norm_num)
theorem B1909949 : Blo 1271954 1909949 := bbase (se 3 (by rfl) ⟨358115, by rfl⟩ : syracuseStep 1909949 = 716231) (by norm_num)
theorem B5440709 : Blo 1271954 5440709 := bbase (se 4 (by rfl) ⟨510066, by rfl⟩ : syracuseStep 5440709 = 1020133) (by norm_num)
theorem B1909973 : Blo 1271954 1909973 := bbase (se 7 (by rfl) ⟨22382, by rfl⟩ : syracuseStep 1909973 = 44765) (by norm_num)
theorem B3622117 : Blo 1271954 3622117 := bbase (se 4 (by rfl) ⟨339573, by rfl⟩ : syracuseStep 3622117 = 679147) (by norm_num)
theorem B1909997 : Blo 1271954 1909997 := bbase (se 3 (by rfl) ⟨358124, by rfl⟩ : syracuseStep 1909997 = 716249) (by norm_num)
theorem B2147573 : Blo 1271954 2147573 := bbase (se 5 (by rfl) ⟨100667, by rfl⟩ : syracuseStep 2147573 = 201335) (by norm_num)
theorem B1910021 : Blo 1271954 1910021 := bbase (se 4 (by rfl) ⟨179064, by rfl⟩ : syracuseStep 1910021 = 358129) (by norm_num)
theorem B2417941 : Blo 1271954 2417941 := bbase (se 6 (by rfl) ⟨56670, by rfl⟩ : syracuseStep 2417941 = 113341) (by norm_num)
theorem B1910045 : Blo 1271954 1910045 := bbase (se 3 (by rfl) ⟨358133, by rfl⟩ : syracuseStep 1910045 = 716267) (by norm_num)
theorem B1910069 : Blo 1271954 1910069 := bbase (se 5 (by rfl) ⟨89534, by rfl⟩ : syracuseStep 1910069 = 179069) (by norm_num)
theorem B3441989 : Blo 1271954 3441989 := bbase (se 4 (by rfl) ⟨322686, by rfl⟩ : syracuseStep 3441989 = 645373) (by norm_num)
theorem B1910093 : Blo 1271954 1910093 := bbase (se 3 (by rfl) ⟨358142, by rfl⟩ : syracuseStep 1910093 = 716285) (by norm_num)
theorem B2901341 : Blo 1271954 2901341 := bbase (se 3 (by rfl) ⟨544001, by rfl⟩ : syracuseStep 2901341 = 1088003) (by norm_num)
theorem B1910117 : Blo 1271954 1910117 := bbase (se 4 (by rfl) ⟨179073, by rfl⟩ : syracuseStep 1910117 = 358147) (by norm_num)
theorem B6440309 : Blo 1271954 6440309 := bbase (se 5 (by rfl) ⟨301889, by rfl⟩ : syracuseStep 6440309 = 603779) (by norm_num)
theorem B2147701 : Blo 1271954 2147701 := bbase (se 5 (by rfl) ⟨100673, by rfl⟩ : syracuseStep 2147701 = 201347) (by norm_num)
theorem B1910141 : Blo 1271954 1910141 := bbase (se 3 (by rfl) ⟨358151, by rfl⟩ : syracuseStep 1910141 = 716303) (by norm_num)
theorem B1910165 : Blo 1271954 1910165 := bbase (se 6 (by rfl) ⟨44769, by rfl⟩ : syracuseStep 1910165 = 89539) (by norm_num)
theorem B4081045 : Blo 1271954 4081045 := bbase (se 6 (by rfl) ⟨95649, by rfl⟩ : syracuseStep 4081045 = 191299) (by norm_num)
theorem B1910189 : Blo 1271954 1910189 := bbase (se 3 (by rfl) ⟨358160, by rfl⟩ : syracuseStep 1910189 = 716321) (by norm_num)
theorem B1721773 : Blo 1271954 1721773 := bbase (se 3 (by rfl) ⟨322832, by rfl⟩ : syracuseStep 1721773 = 645665) (by norm_num)
theorem B11019701 : Blo 1271954 11019701 := bbase (se 5 (by rfl) ⟨516548, by rfl⟩ : syracuseStep 11019701 = 1033097) (by norm_num)
theorem B1910213 : Blo 1271954 1910213 := bbase (se 4 (by rfl) ⟨179082, by rfl⟩ : syracuseStep 1910213 = 358165) (by norm_num)
theorem B2147789 : Blo 1271954 2147789 := bbase (se 3 (by rfl) ⟨402710, by rfl⟩ : syracuseStep 2147789 = 805421) (by norm_num)
theorem B1910237 : Blo 1271954 1910237 := bbase (se 3 (by rfl) ⟨358169, by rfl⟩ : syracuseStep 1910237 = 716339) (by norm_num)
theorem B4294133 : Blo 1271954 4294133 := bbase (se 5 (by rfl) ⟨201287, by rfl⟩ : syracuseStep 4294133 = 402575) (by norm_num)
theorem B4589045 : Blo 1271954 4589045 := bbase (se 5 (by rfl) ⟨215111, by rfl⟩ : syracuseStep 4589045 = 430223) (by norm_num)
theorem B1910261 : Blo 1271954 1910261 := bbase (se 5 (by rfl) ⟨89543, by rfl⟩ : syracuseStep 1910261 = 179087) (by norm_num)
theorem B3221005 : Blo 1271954 3221005 := bbase (se 3 (by rfl) ⟨603938, by rfl⟩ : syracuseStep 3221005 = 1207877) (by norm_num)
theorem B1910285 : Blo 1271954 1910285 := bbase (se 3 (by rfl) ⟨358178, by rfl⟩ : syracuseStep 1910285 = 716357) (by norm_num)
theorem B1910309 : Blo 1271954 1910309 := bbase (se 4 (by rfl) ⟨179091, by rfl⟩ : syracuseStep 1910309 = 358183) (by norm_num)
theorem B1910333 : Blo 1271954 1910333 := bbase (se 3 (by rfl) ⟨358187, by rfl⟩ : syracuseStep 1910333 = 716375) (by norm_num)
theorem B2418245 : Blo 1271954 2418245 := bbase (se 4 (by rfl) ⟨226710, by rfl⟩ : syracuseStep 2418245 = 453421) (by norm_num)
theorem B2147917 : Blo 1271954 2147917 := bbase (se 3 (by rfl) ⟨402734, by rfl⟩ : syracuseStep 2147917 = 805469) (by norm_num)
theorem B2295373 : Blo 1271954 2295373 := bbase (se 3 (by rfl) ⟨430382, by rfl⟩ : syracuseStep 2295373 = 860765) (by norm_num)
theorem B6530645 : Blo 1271954 6530645 := bbase (se 8 (by rfl) ⟨38265, by rfl⟩ : syracuseStep 6530645 = 76531) (by norm_num)
theorem B1910357 : Blo 1271954 1910357 := bbase (se 8 (by rfl) ⟨11193, by rfl⟩ : syracuseStep 1910357 = 22387) (by norm_num)
theorem B1812061 : Blo 1271954 1812061 := bbase (se 3 (by rfl) ⟨339761, by rfl⟩ : syracuseStep 1812061 = 679523) (by norm_num)
theorem B1910381 : Blo 1271954 1910381 := bbase (se 3 (by rfl) ⟨358196, by rfl⟩ : syracuseStep 1910381 = 716393) (by norm_num)
theorem B2983541 : Blo 1271954 2983541 := bbase (se 5 (by rfl) ⟨139853, by rfl⟩ : syracuseStep 2983541 = 279707) (by norm_num)
theorem B3221117 : Blo 1271954 3221117 := bbase (se 3 (by rfl) ⟨603959, by rfl⟩ : syracuseStep 3221117 = 1207919) (by norm_num)
theorem B1910405 : Blo 1271954 1910405 := bbase (se 4 (by rfl) ⟨179100, by rfl⟩ : syracuseStep 1910405 = 358201) (by norm_num)
theorem B1451665 : Blo 1271954 1451665 := bbase (se 2 (by rfl) ⟨544374, by rfl⟩ : syracuseStep 1451665 = 1088749) (by norm_num)
theorem B1910429 : Blo 1271954 1910429 := bbase (se 3 (by rfl) ⟨358205, by rfl⟩ : syracuseStep 1910429 = 716411) (by norm_num)
theorem B2148005 : Blo 1271954 2148005 := bbase (se 4 (by rfl) ⟨201375, by rfl⟩ : syracuseStep 2148005 = 402751) (by norm_num)
theorem B1910453 : Blo 1271954 1910453 := bbase (se 5 (by rfl) ⟨89552, by rfl⟩ : syracuseStep 1910453 = 179105) (by norm_num)
theorem B1910477 : Blo 1271954 1910477 := bbase (se 3 (by rfl) ⟨358214, by rfl⟩ : syracuseStep 1910477 = 716429) (by norm_num)
theorem B9176789 : Blo 1271954 9176789 := bbase (se 7 (by rfl) ⟨107540, by rfl⟩ : syracuseStep 9176789 = 215081) (by norm_num)
theorem B1910501 : Blo 1271954 1910501 := bbase (se 4 (by rfl) ⟨179109, by rfl⟩ : syracuseStep 1910501 = 358219) (by norm_num)
theorem B1910525 : Blo 1271954 1910525 := bbase (se 3 (by rfl) ⟨358223, by rfl⟩ : syracuseStep 1910525 = 716447) (by norm_num)
theorem B3057421 : Blo 1271954 3057421 := bbase (se 3 (by rfl) ⟨573266, by rfl⟩ : syracuseStep 3057421 = 1146533) (by norm_num)
theorem B1910549 : Blo 1271954 1910549 := bbase (se 6 (by rfl) ⟨44778, by rfl⟩ : syracuseStep 1910549 = 89557) (by norm_num)
theorem B4351781 : Blo 1271954 4351781 := bbase (se 4 (by rfl) ⟨407979, by rfl⟩ : syracuseStep 4351781 = 815959) (by norm_num)
theorem B2148133 : Blo 1271954 2148133 := bbase (se 4 (by rfl) ⟨201387, by rfl⟩ : syracuseStep 2148133 = 402775) (by norm_num)
theorem B1910573 : Blo 1271954 1910573 := bbase (se 3 (by rfl) ⟨358232, by rfl⟩ : syracuseStep 1910573 = 716465) (by norm_num)
theorem B3221309 : Blo 1271954 3221309 := bbase (se 3 (by rfl) ⟨603995, by rfl⟩ : syracuseStep 3221309 = 1207991) (by norm_num)
theorem B1910597 : Blo 1271954 1910597 := bbase (se 4 (by rfl) ⟨179118, by rfl⟩ : syracuseStep 1910597 = 358237) (by norm_num)
theorem B1910621 : Blo 1271954 1910621 := bbase (se 3 (by rfl) ⟨358241, by rfl⟩ : syracuseStep 1910621 = 716483) (by norm_num)
theorem B3057517 : Blo 1271954 3057517 := bbase (se 3 (by rfl) ⟨573284, by rfl⟩ : syracuseStep 3057517 = 1146569) (by norm_num)
theorem B1910645 : Blo 1271954 1910645 := bbase (se 5 (by rfl) ⟨89561, by rfl⟩ : syracuseStep 1910645 = 179123) (by norm_num)
theorem B2148221 : Blo 1271954 2148221 := bbase (se 3 (by rfl) ⟨402791, by rfl⟩ : syracuseStep 2148221 = 805583) (by norm_num)
theorem B1910669 : Blo 1271954 1910669 := bbase (se 3 (by rfl) ⟨358250, by rfl⟩ : syracuseStep 1910669 = 716501) (by norm_num)
theorem B4294565 : Blo 1271954 4294565 := bbase (se 4 (by rfl) ⟨402615, by rfl⟩ : syracuseStep 4294565 = 805231) (by norm_num)
theorem B1910693 : Blo 1271954 1910693 := bbase (se 4 (by rfl) ⟨179127, by rfl⟩ : syracuseStep 1910693 = 358255) (by norm_num)
theorem B1812397 : Blo 1271954 1812397 := bbase (se 3 (by rfl) ⟨339824, by rfl⟩ : syracuseStep 1812397 = 679649) (by norm_num)
theorem B1910717 : Blo 1271954 1910717 := bbase (se 3 (by rfl) ⟨358259, by rfl⟩ : syracuseStep 1910717 = 716519) (by norm_num)
theorem B1632209 : Blo 1271954 1632209 := bbase (se 2 (by rfl) ⟨612078, by rfl⟩ : syracuseStep 1632209 = 1224157) (by norm_num)
theorem B8153045 : Blo 1271954 8153045 := bbase (se 7 (by rfl) ⟨95543, by rfl⟩ : syracuseStep 8153045 = 191087) (by norm_num)
theorem B1910741 : Blo 1271954 1910741 := bbase (se 7 (by rfl) ⟨22391, by rfl⟩ : syracuseStep 1910741 = 44783) (by norm_num)
theorem B1910765 : Blo 1271954 1910765 := bbase (se 3 (by rfl) ⟨358268, by rfl⟩ : syracuseStep 1910765 = 716537) (by norm_num)
theorem B2148349 : Blo 1271954 2148349 := bbase (se 3 (by rfl) ⟨402815, by rfl⟩ : syracuseStep 2148349 = 805631) (by norm_num)
theorem B5801989 : Blo 1271954 5801989 := bbase (se 4 (by rfl) ⟨543936, by rfl⟩ : syracuseStep 5801989 = 1087873) (by norm_num)
theorem B1910789 : Blo 1271954 1910789 := bbase (se 4 (by rfl) ⟨179136, by rfl⟩ : syracuseStep 1910789 = 358273) (by norm_num)
theorem B1910813 : Blo 1271954 1910813 := bbase (se 3 (by rfl) ⟨358277, by rfl⟩ : syracuseStep 1910813 = 716555) (by norm_num)
theorem B3057709 : Blo 1271954 3057709 := bbase (se 3 (by rfl) ⟨573320, by rfl⟩ : syracuseStep 3057709 = 1146641) (by norm_num)
theorem B4589621 : Blo 1271954 4589621 := bbase (se 5 (by rfl) ⟨215138, by rfl⟩ : syracuseStep 4589621 = 430277) (by norm_num)
theorem B1910837 : Blo 1271954 1910837 := bbase (se 5 (by rfl) ⟨89570, by rfl⟩ : syracuseStep 1910837 = 179141) (by norm_num)
theorem B1910861 : Blo 1271954 1910861 := bbase (se 3 (by rfl) ⟨358286, by rfl⟩ : syracuseStep 1910861 = 716573) (by norm_num)
theorem B2148437 : Blo 1271954 2148437 := bbase (se 8 (by rfl) ⟨12588, by rfl⟩ : syracuseStep 2148437 = 25177) (by norm_num)
theorem B1910885 : Blo 1271954 1910885 := bbase (se 4 (by rfl) ⟨179145, by rfl⟩ : syracuseStep 1910885 = 358291) (by norm_num)
theorem B1910909 : Blo 1271954 1910909 := bbase (se 3 (by rfl) ⟨358295, by rfl⟩ : syracuseStep 1910909 = 716591) (by norm_num)
theorem B1812613 : Blo 1271954 1812613 := bbase (se 4 (by rfl) ⟨169932, by rfl⟩ : syracuseStep 1812613 = 339865) (by norm_num)
theorem B3221653 : Blo 1271954 3221653 := bbase (se 6 (by rfl) ⟨75507, by rfl⟩ : syracuseStep 3221653 = 151015) (by norm_num)
theorem B2148565 : Blo 1271954 2148565 := bbase (se 7 (by rfl) ⟨25178, by rfl⟩ : syracuseStep 2148565 = 50357) (by norm_num)
theorem B6449381 : Blo 1271954 6449381 := bbase (se 4 (by rfl) ⟨604629, by rfl⟩ : syracuseStep 6449381 = 1209259) (by norm_num)
theorem B3221765 : Blo 1271954 3221765 := bbase (se 4 (by rfl) ⟨302040, by rfl⟩ : syracuseStep 3221765 = 604081) (by norm_num)
theorem B2148653 : Blo 1271954 2148653 := bbase (se 3 (by rfl) ⟨402872, by rfl⟩ : syracuseStep 2148653 = 805745) (by norm_num)
theorem B3623221 : Blo 1271954 3623221 := bbase (se 5 (by rfl) ⟨169838, by rfl⟩ : syracuseStep 3623221 = 339677) (by norm_num)
theorem B4294997 : Blo 1271954 4294997 := bbase (se 10 (by rfl) ⟨6291, by rfl⟩ : syracuseStep 4294997 = 12583) (by norm_num)
theorem B3058037 : Blo 1271954 3058037 := bbase (se 5 (by rfl) ⟨143345, by rfl⟩ : syracuseStep 3058037 = 286691) (by norm_num)
theorem B1632673 : Blo 1271954 1632673 := bbase (se 2 (by rfl) ⟨612252, by rfl⟩ : syracuseStep 1632673 = 1224505) (by norm_num)
theorem B2148781 : Blo 1271954 2148781 := bbase (se 3 (by rfl) ⟨402896, by rfl⟩ : syracuseStep 2148781 = 805793) (by norm_num)
theorem B3221957 : Blo 1271954 3221957 := bbase (se 4 (by rfl) ⟨302058, by rfl⟩ : syracuseStep 3221957 = 604117) (by norm_num)
theorem B10463701 : Blo 1271954 10463701 := bbase (se 7 (by rfl) ⟨122621, by rfl⟩ : syracuseStep 10463701 = 245243) (by norm_num)
theorem B4590053 : Blo 1271954 4590053 := bbase (se 4 (by rfl) ⟨430317, by rfl⟩ : syracuseStep 4590053 = 860635) (by norm_num)
theorem B1812989 : Blo 1271954 1812989 := bbase (se 3 (by rfl) ⟨339935, by rfl⟩ : syracuseStep 1812989 = 679871) (by norm_num)
theorem B2148869 : Blo 1271954 2148869 := bbase (se 4 (by rfl) ⟨201456, by rfl⟩ : syracuseStep 2148869 = 402913) (by norm_num)
theorem B1550921 : Blo 1271954 1550921 := bbase (se 2 (by rfl) ⟨581595, by rfl⟩ : syracuseStep 1550921 = 1163191) (by norm_num)
theorem B1452673 : Blo 1271954 1452673 := bbase (se 2 (by rfl) ⟨544752, by rfl⟩ : syracuseStep 1452673 = 1089505) (by norm_num)
theorem B6441605 : Blo 1271954 6441605 := bbase (se 4 (by rfl) ⟨603900, by rfl⟩ : syracuseStep 6441605 = 1207801) (by norm_num)
theorem B2148997 : Blo 1271954 2148997 := bbase (se 4 (by rfl) ⟨201468, by rfl⟩ : syracuseStep 2148997 = 402937) (by norm_num)
theorem B7244437 : Blo 1271954 7244437 := bbase (se 6 (by rfl) ⟨169791, by rfl⟩ : syracuseStep 7244437 = 339583) (by norm_num)
theorem B1862317 : Blo 1271954 1862317 := bbase (se 3 (by rfl) ⟨349184, by rfl⟩ : syracuseStep 1862317 = 698369) (by norm_num)
theorem B2124493 : Blo 1271954 2124493 := bbase (se 3 (by rfl) ⟨398342, by rfl⟩ : syracuseStep 2124493 = 796685) (by norm_num)
theorem B2149085 : Blo 1271954 2149085 := bbase (se 3 (by rfl) ⟨402953, by rfl⟩ : syracuseStep 2149085 = 805907) (by norm_num)
theorem B6195973 : Blo 1271954 6195973 := bbase (se 4 (by rfl) ⟨580872, by rfl⟩ : syracuseStep 6195973 = 1161745) (by norm_num)
theorem B4295429 : Blo 1271954 4295429 := bbase (se 4 (by rfl) ⟨402696, by rfl⟩ : syracuseStep 4295429 = 805393) (by norm_num)
theorem B3222301 : Blo 1271954 3222301 := bbase (se 3 (by rfl) ⟨604181, by rfl⟩ : syracuseStep 3222301 = 1208363) (by norm_num)
theorem B3058469 : Blo 1271954 3058469 := bbase (se 4 (by rfl) ⟨286731, by rfl⟩ : syracuseStep 3058469 = 573463) (by norm_num)
theorem B2861909 : Blo 1271954 2861909 := bbase (se 9 (by rfl) ⟨8384, by rfl⟩ : syracuseStep 2861909 = 16769) (by norm_num)
theorem B3869525 : Blo 1271954 3869525 := bbase (se 9 (by rfl) ⟨11336, by rfl⟩ : syracuseStep 3869525 = 22673) (by norm_num)
theorem B2149213 : Blo 1271954 2149213 := bbase (se 3 (by rfl) ⟨402977, by rfl⟩ : syracuseStep 2149213 = 805955) (by norm_num)
theorem B3222413 : Blo 1271954 3222413 := bbase (se 3 (by rfl) ⟨604202, by rfl⟩ : syracuseStep 3222413 = 1208405) (by norm_num)
theorem B2861981 : Blo 1271954 2861981 := bbase (se 3 (by rfl) ⟨536621, by rfl⟩ : syracuseStep 2861981 = 1073243) (by norm_num)
theorem B3869621 : Blo 1271954 3869621 := bbase (se 5 (by rfl) ⟨181388, by rfl⟩ : syracuseStep 3869621 = 362777) (by norm_num)
theorem B2149301 : Blo 1271954 2149301 := bbase (se 5 (by rfl) ⟨100748, by rfl⟩ : syracuseStep 2149301 = 201497) (by norm_num)
theorem B4836293 : Blo 1271954 4836293 := bbase (se 4 (by rfl) ⟨453402, by rfl⟩ : syracuseStep 4836293 = 906805) (by norm_num)
theorem B2862053 : Blo 1271954 2862053 := bbase (se 4 (by rfl) ⟨268317, by rfl⟩ : syracuseStep 2862053 = 536635) (by norm_num)
theorem B2862125 : Blo 1271954 2862125 := bbase (se 3 (by rfl) ⟨536648, by rfl⟩ : syracuseStep 2862125 = 1073297) (by norm_num)
theorem B2149429 : Blo 1271954 2149429 := bbase (se 5 (by rfl) ⟨100754, by rfl⟩ : syracuseStep 2149429 = 201509) (by norm_num)
theorem B3222605 : Blo 1271954 3222605 := bbase (se 3 (by rfl) ⟨604238, by rfl⟩ : syracuseStep 3222605 = 1208477) (by norm_num)
theorem B2862197 : Blo 1271954 2862197 := bbase (se 5 (by rfl) ⟨134165, by rfl⟩ : syracuseStep 2862197 = 268331) (by norm_num)
theorem B3058805 : Blo 1271954 3058805 := bbase (se 5 (by rfl) ⟨143381, by rfl⟩ : syracuseStep 3058805 = 286763) (by norm_num)
theorem B2149517 : Blo 1271954 2149517 := bbase (se 3 (by rfl) ⟨403034, by rfl⟩ : syracuseStep 2149517 = 806069) (by norm_num)
theorem B4295861 : Blo 1271954 4295861 := bbase (se 5 (by rfl) ⟨201368, by rfl⟩ : syracuseStep 4295861 = 402737) (by norm_num)
theorem B2862269 : Blo 1271954 2862269 := bbase (se 3 (by rfl) ⟨536675, by rfl⟩ : syracuseStep 2862269 = 1073351) (by norm_num)
theorem B4836581 : Blo 1271954 4836581 := bbase (se 4 (by rfl) ⟨453429, by rfl⟩ : syracuseStep 4836581 = 906859) (by norm_num)
theorem B2862341 : Blo 1271954 2862341 := bbase (se 4 (by rfl) ⟨268344, by rfl⟩ : syracuseStep 2862341 = 536689) (by norm_num)
theorem B2149645 : Blo 1271954 2149645 := bbase (se 3 (by rfl) ⟨403058, by rfl⟩ : syracuseStep 2149645 = 806117) (by norm_num)
theorem B1396001 : Blo 1271954 1396001 := bbase (se 2 (by rfl) ⟨523500, by rfl⟩ : syracuseStep 1396001 = 1047001) (by norm_num)
theorem B1289525 : Blo 1271954 1289525 := bbase (se 5 (by rfl) ⟨60446, by rfl⟩ : syracuseStep 1289525 = 120893) (by norm_num)
theorem B9669941 : Blo 1271954 9669941 := bbase (se 5 (by rfl) ⟨453278, by rfl⟩ : syracuseStep 9669941 = 906557) (by norm_num)
theorem B2862413 : Blo 1271954 2862413 := bbase (se 3 (by rfl) ⟨536702, by rfl⟩ : syracuseStep 2862413 = 1073405) (by norm_num)
theorem B2149733 : Blo 1271954 2149733 := bbase (se 4 (by rfl) ⟨201537, by rfl⟩ : syracuseStep 2149733 = 403075) (by norm_num)
theorem B1936757 : Blo 1271954 1936757 := bbase (se 5 (by rfl) ⟨90785, by rfl⟩ : syracuseStep 1936757 = 181571) (by norm_num)
theorem B2862485 : Blo 1271954 2862485 := bbase (se 6 (by rfl) ⟨67089, by rfl⟩ : syracuseStep 2862485 = 134179) (by norm_num)
theorem B3222949 : Blo 1271954 3222949 := bbase (se 4 (by rfl) ⟨302151, by rfl⟩ : syracuseStep 3222949 = 604303) (by norm_num)
theorem B2862557 : Blo 1271954 2862557 := bbase (se 3 (by rfl) ⟨536729, by rfl⟩ : syracuseStep 2862557 = 1073459) (by norm_num)
theorem B1633765 : Blo 1271954 1633765 := bbase (se 4 (by rfl) ⟨153165, by rfl⟩ : syracuseStep 1633765 = 306331) (by norm_num)
theorem B2067941 : Blo 1271954 2067941 := bbase (se 4 (by rfl) ⟨193869, by rfl⟩ : syracuseStep 2067941 = 387739) (by norm_num)
theorem B5434901 : Blo 1271954 5434901 := bbase (se 6 (by rfl) ⟨127380, by rfl⟩ : syracuseStep 5434901 = 254761) (by norm_num)
theorem B3223061 : Blo 1271954 3223061 := bbase (se 6 (by rfl) ⟨75540, by rfl⟩ : syracuseStep 3223061 = 151081) (by norm_num)
theorem B2862629 : Blo 1271954 2862629 := bbase (se 4 (by rfl) ⟨268371, by rfl⟩ : syracuseStep 2862629 = 536743) (by norm_num)
theorem B1289773 : Blo 1271954 1289773 := bbase (se 3 (by rfl) ⟨241832, by rfl⟩ : syracuseStep 1289773 = 483665) (by norm_num)
theorem B4296293 : Blo 1271954 4296293 := bbase (se 4 (by rfl) ⟨402777, by rfl⟩ : syracuseStep 4296293 = 805555) (by norm_num)
theorem B2862701 : Blo 1271954 2862701 := bbase (se 3 (by rfl) ⟨536756, by rfl⟩ : syracuseStep 2862701 = 1073513) (by norm_num)
theorem B2862773 : Blo 1271954 2862773 := bbase (se 5 (by rfl) ⟨134192, by rfl⟩ : syracuseStep 2862773 = 268385) (by norm_num)
theorem B9662165 : Blo 1271954 9662165 := bbase (se 7 (by rfl) ⟨113228, by rfl⟩ : syracuseStep 9662165 = 226457) (by norm_num)
theorem B3223253 : Blo 1271954 3223253 := bbase (se 7 (by rfl) ⟨37772, by rfl⟩ : syracuseStep 3223253 = 75545) (by norm_num)
theorem B2862845 : Blo 1271954 2862845 := bbase (se 3 (by rfl) ⟨536783, by rfl⟩ : syracuseStep 2862845 = 1073567) (by norm_num)
theorem B3624725 : Blo 1271954 3624725 := bbase (se 6 (by rfl) ⟨84954, by rfl⟩ : syracuseStep 3624725 = 169909) (by norm_num)
theorem B1470277 : Blo 1271954 1470277 := bbase (se 4 (by rfl) ⟨137838, by rfl⟩ : syracuseStep 1470277 = 275677) (by norm_num)
theorem B2862917 : Blo 1271954 2862917 := bbase (se 4 (by rfl) ⟨268398, by rfl⟩ : syracuseStep 2862917 = 536797) (by norm_num)
theorem B1290053 : Blo 1271954 1290053 := bbase (se 4 (by rfl) ⟨120942, by rfl⟩ : syracuseStep 1290053 = 241885) (by norm_num)
theorem B2862989 : Blo 1271954 2862989 := bbase (se 3 (by rfl) ⟨536810, by rfl⟩ : syracuseStep 2862989 = 1073621) (by norm_num)
theorem B6442901 : Blo 1271954 6442901 := bbase (se 6 (by rfl) ⟨151005, by rfl⟩ : syracuseStep 6442901 = 302011) (by norm_num)
theorem B1290133 : Blo 1271954 1290133 := bbase (se 6 (by rfl) ⟨30237, by rfl⟩ : syracuseStep 1290133 = 60475) (by norm_num)
theorem B2863061 : Blo 1271954 2863061 := bbase (se 7 (by rfl) ⟨33551, by rfl⟩ : syracuseStep 2863061 = 67103) (by norm_num)
theorem B4296725 : Blo 1271954 4296725 := bbase (se 6 (by rfl) ⟨100704, by rfl⟩ : syracuseStep 4296725 = 201409) (by norm_num)
theorem B2863133 : Blo 1271954 2863133 := bbase (se 3 (by rfl) ⟨536837, by rfl⟩ : syracuseStep 2863133 = 1073675) (by norm_num)
theorem B3223597 : Blo 1271954 3223597 := bbase (se 3 (by rfl) ⟨604424, by rfl⟩ : syracuseStep 3223597 = 1208849) (by norm_num)
theorem B2863205 : Blo 1271954 2863205 := bbase (se 4 (by rfl) ⟨268425, by rfl⟩ : syracuseStep 2863205 = 536851) (by norm_num)
theorem B3059861 : Blo 1271954 3059861 := bbase (se 6 (by rfl) ⟨71715, by rfl⟩ : syracuseStep 3059861 = 143431) (by norm_num)
theorem B1609885 : Blo 1271954 1609885 := bbase (se 3 (by rfl) ⟨301853, by rfl⟩ : syracuseStep 1609885 = 603707) (by norm_num)
theorem B3223709 : Blo 1271954 3223709 := bbase (se 3 (by rfl) ⟨604445, by rfl⟩ : syracuseStep 3223709 = 1208891) (by norm_num)
theorem B2863277 : Blo 1271954 2863277 := bbase (se 3 (by rfl) ⟨536864, by rfl⟩ : syracuseStep 2863277 = 1073729) (by norm_num)
theorem B2863349 : Blo 1271954 2863349 := bbase (se 5 (by rfl) ⟨134219, by rfl⟩ : syracuseStep 2863349 = 268439) (by norm_num)
theorem B2863421 : Blo 1271954 2863421 := bbase (se 3 (by rfl) ⟨536891, by rfl⟩ : syracuseStep 2863421 = 1073783) (by norm_num)
theorem B1610057 : Blo 1271954 1610057 := bbase (se 2 (by rfl) ⟨603771, by rfl⟩ : syracuseStep 1610057 = 1207543) (by norm_num)
theorem B3223901 : Blo 1271954 3223901 := bbase (se 3 (by rfl) ⟨604481, by rfl⟩ : syracuseStep 3223901 = 1208963) (by norm_num)
theorem B1610113 : Blo 1271954 1610113 := bbase (se 2 (by rfl) ⟨603792, by rfl⟩ : syracuseStep 1610113 = 1207585) (by norm_num)
theorem B2863493 : Blo 1271954 2863493 := bbase (se 4 (by rfl) ⟨268452, by rfl⟩ : syracuseStep 2863493 = 536905) (by norm_num)
theorem B4297157 : Blo 1271954 4297157 := bbase (se 4 (by rfl) ⟨402858, by rfl⟩ : syracuseStep 4297157 = 805717) (by norm_num)
theorem B2863565 : Blo 1271954 2863565 := bbase (se 3 (by rfl) ⟨536918, by rfl⟩ : syracuseStep 2863565 = 1073837) (by norm_num)
theorem B1290701 : Blo 1271954 1290701 := bbase (se 3 (by rfl) ⟨242006, by rfl⟩ : syracuseStep 1290701 = 484013) (by norm_num)
theorem B1610209 : Blo 1271954 1610209 := bbase (se 2 (by rfl) ⟨603828, by rfl⟩ : syracuseStep 1610209 = 1207657) (by norm_num)
theorem B2904589 : Blo 1271954 2904589 := bbase (se 3 (by rfl) ⟨544610, by rfl⟩ : syracuseStep 2904589 = 1089221) (by norm_num)
theorem B2863637 : Blo 1271954 2863637 := bbase (se 6 (by rfl) ⟨67116, by rfl⟩ : syracuseStep 2863637 = 134233) (by norm_num)
theorem B1528393 : Blo 1271954 1528393 := bbase (se 2 (by rfl) ⟨573147, by rfl⟩ : syracuseStep 1528393 = 1146295) (by norm_num)
theorem B1307209 : Blo 1271954 1307209 := bbase (se 2 (by rfl) ⟨490203, by rfl⟩ : syracuseStep 1307209 = 980407) (by norm_num)
theorem B7246421 : Blo 1271954 7246421 := bbase (se 8 (by rfl) ⟨42459, by rfl⟩ : syracuseStep 7246421 = 84919) (by norm_num)
theorem B2904661 : Blo 1271954 2904661 := bbase (se 8 (by rfl) ⟨17019, by rfl⟩ : syracuseStep 2904661 = 34039) (by norm_num)
theorem B2863709 : Blo 1271954 2863709 := bbase (se 3 (by rfl) ⟨536945, by rfl⟩ : syracuseStep 2863709 = 1073891) (by norm_num)
theorem B3265157 : Blo 1271954 3265157 := bbase (se 4 (by rfl) ⟨306108, by rfl⟩ : syracuseStep 3265157 = 612217) (by norm_num)
theorem B1610381 : Blo 1271954 1610381 := bbase (se 3 (by rfl) ⟨301946, by rfl⟩ : syracuseStep 1610381 = 603893) (by norm_num)
theorem B11604629 : Blo 1271954 11604629 := bbase (se 6 (by rfl) ⟨271983, by rfl⟩ : syracuseStep 11604629 = 543967) (by norm_num)
theorem B2863781 : Blo 1271954 2863781 := bbase (se 4 (by rfl) ⟨268479, by rfl⟩ : syracuseStep 2863781 = 536959) (by norm_num)
theorem B1528489 : Blo 1271954 1528489 := bbase (se 2 (by rfl) ⟨573183, by rfl⟩ : syracuseStep 1528489 = 1146367) (by norm_num)
theorem B12235445 : Blo 1271954 12235445 := bbase (se 5 (by rfl) ⟨573536, by rfl⟩ : syracuseStep 12235445 = 1147073) (by norm_num)
theorem B3224245 : Blo 1271954 3224245 := bbase (se 5 (by rfl) ⟨151136, by rfl⟩ : syracuseStep 3224245 = 302273) (by norm_num)
theorem B1610437 : Blo 1271954 1610437 := bbase (se 4 (by rfl) ⟨150978, by rfl⟩ : syracuseStep 1610437 = 301957) (by norm_num)
theorem B2863853 : Blo 1271954 2863853 := bbase (se 3 (by rfl) ⟨536972, by rfl⟩ : syracuseStep 2863853 = 1073945) (by norm_num)
theorem B10867445 : Blo 1271954 10867445 := bbase (se 5 (by rfl) ⟨509411, by rfl⟩ : syracuseStep 10867445 = 1018823) (by norm_num)
theorem B4829989 : Blo 1271954 4829989 := bbase (se 4 (by rfl) ⟨452811, by rfl⟩ : syracuseStep 4829989 = 905623) (by norm_num)
theorem B1610533 : Blo 1271954 1610533 := bbase (se 4 (by rfl) ⟨150987, by rfl⟩ : syracuseStep 1610533 = 301975) (by norm_num)
theorem B3224357 : Blo 1271954 3224357 := bbase (se 4 (by rfl) ⟨302283, by rfl⟩ : syracuseStep 3224357 = 604567) (by norm_num)
theorem B2863925 : Blo 1271954 2863925 := bbase (se 5 (by rfl) ⟨134246, by rfl⟩ : syracuseStep 2863925 = 268493) (by norm_num)
theorem B3674965 : Blo 1271954 3674965 := bbase (se 9 (by rfl) ⟨10766, by rfl⟩ : syracuseStep 3674965 = 21533) (by norm_num)
theorem B4297589 : Blo 1271954 4297589 := bbase (se 5 (by rfl) ⟨201449, by rfl⟩ : syracuseStep 4297589 = 402899) (by norm_num)
theorem B2863997 : Blo 1271954 2863997 := bbase (se 3 (by rfl) ⟨536999, by rfl⟩ : syracuseStep 2863997 = 1073999) (by norm_num)
theorem B2864069 : Blo 1271954 2864069 := bbase (se 4 (by rfl) ⟨268506, by rfl⟩ : syracuseStep 2864069 = 537013) (by norm_num)
theorem B1610705 : Blo 1271954 1610705 := bbase (se 2 (by rfl) ⟨604014, by rfl⟩ : syracuseStep 1610705 = 1208029) (by norm_num)
theorem B24474581 : Blo 1271954 24474581 := bbase (se 7 (by rfl) ⟨286811, by rfl⟩ : syracuseStep 24474581 = 573623) (by norm_num)
theorem B3224549 : Blo 1271954 3224549 := bbase (se 4 (by rfl) ⟨302301, by rfl⟩ : syracuseStep 3224549 = 604603) (by norm_num)
theorem B1610761 : Blo 1271954 1610761 := bbase (se 2 (by rfl) ⟨604035, by rfl⟩ : syracuseStep 1610761 = 1208071) (by norm_num)
theorem B2864141 : Blo 1271954 2864141 := bbase (se 3 (by rfl) ⟨537026, by rfl⟩ : syracuseStep 2864141 = 1074053) (by norm_num)
theorem B1291285 : Blo 1271954 1291285 := bbase (se 6 (by rfl) ⟨30264, by rfl⟩ : syracuseStep 1291285 = 60529) (by norm_num)
theorem B2716733 : Blo 1271954 2716733 := bbase (se 3 (by rfl) ⟨509387, by rfl⟩ : syracuseStep 2716733 = 1018775) (by norm_num)
theorem B4830293 : Blo 1271954 4830293 := bbase (se 8 (by rfl) ⟨28302, by rfl⟩ : syracuseStep 4830293 = 56605) (by norm_num)
theorem B2864213 : Blo 1271954 2864213 := bbase (se 8 (by rfl) ⟨16782, by rfl⟩ : syracuseStep 2864213 = 33565) (by norm_num)
theorem B1610857 : Blo 1271954 1610857 := bbase (se 2 (by rfl) ⟨604071, by rfl⟩ : syracuseStep 1610857 = 1208143) (by norm_num)
theorem B2864285 : Blo 1271954 2864285 := bbase (se 3 (by rfl) ⟨537053, by rfl⟩ : syracuseStep 2864285 = 1074107) (by norm_num)
theorem B6444197 : Blo 1271954 6444197 := bbase (se 4 (by rfl) ⟨604143, by rfl⟩ : syracuseStep 6444197 = 1208287) (by norm_num)
theorem B2864357 : Blo 1271954 2864357 := bbase (se 4 (by rfl) ⟨268533, by rfl⟩ : syracuseStep 2864357 = 537067) (by norm_num)
theorem B1766677 : Blo 1271954 1766677 := bbase (se 6 (by rfl) ⟨41406, by rfl⟩ : syracuseStep 1766677 = 82813) (by norm_num)
theorem B3265813 : Blo 1271954 3265813 := bbase (se 6 (by rfl) ⟨76542, by rfl⟩ : syracuseStep 3265813 = 153085) (by norm_num)
theorem B6116629 : Blo 1271954 6116629 := bbase (se 6 (by rfl) ⟨143358, by rfl⟩ : syracuseStep 6116629 = 286717) (by norm_num)
theorem B1611029 : Blo 1271954 1611029 := bbase (se 6 (by rfl) ⟨37758, by rfl⟩ : syracuseStep 1611029 = 75517) (by norm_num)
theorem B4298021 : Blo 1271954 4298021 := bbase (se 4 (by rfl) ⟨402939, by rfl⟩ : syracuseStep 4298021 = 805879) (by norm_num)
theorem B2864429 : Blo 1271954 2864429 := bbase (se 3 (by rfl) ⟨537080, by rfl⟩ : syracuseStep 2864429 = 1074161) (by norm_num)
theorem B8262965 : Blo 1271954 8262965 := bbase (se 5 (by rfl) ⟨387326, by rfl⟩ : syracuseStep 8262965 = 774653) (by norm_num)
theorem B3626309 : Blo 1271954 3626309 := bbase (se 4 (by rfl) ⟨339966, by rfl⟩ : syracuseStep 3626309 = 679933) (by norm_num)
theorem B1611085 : Blo 1271954 1611085 := bbase (se 3 (by rfl) ⟨302078, by rfl⟩ : syracuseStep 1611085 = 604157) (by norm_num)
theorem B123958613 : Blo 1271954 123958613 := bbase (se 13 (by rfl) ⟨22697, by rfl⟩ : syracuseStep 123958613 = 45395) (by norm_num)
theorem B2864501 : Blo 1271954 2864501 := bbase (se 5 (by rfl) ⟨134273, by rfl⟩ : syracuseStep 2864501 = 268547) (by norm_num)
theorem B1611181 : Blo 1271954 1611181 := bbase (se 3 (by rfl) ⟨302096, by rfl⟩ : syracuseStep 1611181 = 604193) (by norm_num)
theorem B2864573 : Blo 1271954 2864573 := bbase (se 3 (by rfl) ⟨537107, by rfl⟩ : syracuseStep 2864573 = 1074215) (by norm_num)
theorem B1430977 : Blo 1271954 1430977 := bbase (se 2 (by rfl) ⟨536616, by rfl⟩ : syracuseStep 1430977 = 1073233) (by norm_num)
theorem B1431013 : Blo 1271954 1431013 := bbase (se 4 (by rfl) ⟨134157, by rfl⟩ : syracuseStep 1431013 = 268315) (by norm_num)
theorem B2864645 : Blo 1271954 2864645 := bbase (se 4 (by rfl) ⟨268560, by rfl⟩ : syracuseStep 2864645 = 537121) (by norm_num)
theorem B1431049 : Blo 1271954 1431049 := bbase (se 2 (by rfl) ⟨536643, by rfl⟩ : syracuseStep 1431049 = 1073287) (by norm_num)
theorem B1431085 : Blo 1271954 1431085 := bbase (se 3 (by rfl) ⟨268328, by rfl⟩ : syracuseStep 1431085 = 536657) (by norm_num)
theorem B2864717 : Blo 1271954 2864717 := bbase (se 3 (by rfl) ⟨537134, by rfl⟩ : syracuseStep 2864717 = 1074269) (by norm_num)
theorem B1431121 : Blo 1271954 1431121 := bbase (se 2 (by rfl) ⟨536670, by rfl⟩ : syracuseStep 1431121 = 1073341) (by norm_num)
theorem B1611353 : Blo 1271954 1611353 := bbase (se 2 (by rfl) ⟨604257, by rfl⟩ : syracuseStep 1611353 = 1208515) (by norm_num)
theorem B1431157 : Blo 1271954 1431157 := bbase (se 5 (by rfl) ⟨67085, by rfl⟩ : syracuseStep 1431157 = 134171) (by norm_num)
theorem B2651789 : Blo 1271954 2651789 := bbase (se 3 (by rfl) ⟨497210, by rfl⟩ : syracuseStep 2651789 = 994421) (by norm_num)
theorem B1529489 : Blo 1271954 1529489 := bbase (se 2 (by rfl) ⟨573558, by rfl⟩ : syracuseStep 1529489 = 1147117) (by norm_num)
theorem B1611409 : Blo 1271954 1611409 := bbase (se 2 (by rfl) ⟨604278, by rfl⟩ : syracuseStep 1611409 = 1208557) (by norm_num)
theorem B2864789 : Blo 1271954 2864789 := bbase (se 6 (by rfl) ⟨67143, by rfl⟩ : syracuseStep 2864789 = 134287) (by norm_num)
theorem B1431193 : Blo 1271954 1431193 := bbase (se 2 (by rfl) ⟨536697, by rfl⟩ : syracuseStep 1431193 = 1073395) (by norm_num)
theorem B1431229 : Blo 1271954 1431229 := bbase (se 3 (by rfl) ⟨268355, by rfl⟩ : syracuseStep 1431229 = 536711) (by norm_num)
theorem B4298453 : Blo 1271954 4298453 := bbase (se 7 (by rfl) ⟨50372, by rfl⟩ : syracuseStep 4298453 = 100745) (by norm_num)
theorem B2864861 : Blo 1271954 2864861 := bbase (se 3 (by rfl) ⟨537161, by rfl⟩ : syracuseStep 2864861 = 1074323) (by norm_num)
theorem B1431265 : Blo 1271954 1431265 := bbase (se 2 (by rfl) ⟨536724, by rfl⟩ : syracuseStep 1431265 = 1073449) (by norm_num)
theorem B1611505 : Blo 1271954 1611505 := bbase (se 2 (by rfl) ⟨604314, by rfl⟩ : syracuseStep 1611505 = 1208629) (by norm_num)
theorem B1431301 : Blo 1271954 1431301 := bbase (se 4 (by rfl) ⟨134184, by rfl⟩ : syracuseStep 1431301 = 268369) (by norm_num)
theorem B2864933 : Blo 1271954 2864933 := bbase (se 4 (by rfl) ⟨268587, by rfl⟩ : syracuseStep 2864933 = 537175) (by norm_num)
theorem B1431337 : Blo 1271954 1431337 := bbase (se 2 (by rfl) ⟨536751, by rfl⟩ : syracuseStep 1431337 = 1073503) (by norm_num)
theorem B3438389 : Blo 1271954 3438389 := bbase (se 5 (by rfl) ⟨161174, by rfl⟩ : syracuseStep 3438389 = 322349) (by norm_num)
theorem B1431373 : Blo 1271954 1431373 := bbase (se 3 (by rfl) ⟨268382, by rfl⟩ : syracuseStep 1431373 = 536765) (by norm_num)
theorem B2865005 : Blo 1271954 2865005 := bbase (se 3 (by rfl) ⟨537188, by rfl⟩ : syracuseStep 2865005 = 1074377) (by norm_num)
theorem B1431409 : Blo 1271954 1431409 := bbase (se 2 (by rfl) ⟨536778, by rfl⟩ : syracuseStep 1431409 = 1073557) (by norm_num)
theorem B1431445 : Blo 1271954 1431445 := bbase (se 6 (by rfl) ⟨33549, by rfl⟩ : syracuseStep 1431445 = 67099) (by norm_num)
theorem B1611677 : Blo 1271954 1611677 := bbase (se 3 (by rfl) ⟨302189, by rfl⟩ : syracuseStep 1611677 = 604379) (by norm_num)
theorem B1529777 : Blo 1271954 1529777 := bbase (se 2 (by rfl) ⟨573666, by rfl⟩ : syracuseStep 1529777 = 1147333) (by norm_num)
theorem B2865077 : Blo 1271954 2865077 := bbase (se 5 (by rfl) ⟨134300, by rfl⟩ : syracuseStep 2865077 = 268601) (by norm_num)
theorem B1431481 : Blo 1271954 1431481 := bbase (se 2 (by rfl) ⟨536805, by rfl⟩ : syracuseStep 1431481 = 1073611) (by norm_num)
theorem B5806037 : Blo 1271954 5806037 := bbase (se 7 (by rfl) ⟨68039, by rfl⟩ : syracuseStep 5806037 = 136079) (by norm_num)
theorem B1611733 : Blo 1271954 1611733 := bbase (se 7 (by rfl) ⟨18887, by rfl⟩ : syracuseStep 1611733 = 37775) (by norm_num)
theorem B1431517 : Blo 1271954 1431517 := bbase (se 3 (by rfl) ⟨268409, by rfl⟩ : syracuseStep 1431517 = 536819) (by norm_num)
theorem B3626981 : Blo 1271954 3626981 := bbase (se 4 (by rfl) ⟨340029, by rfl⟩ : syracuseStep 3626981 = 680059) (by norm_num)
theorem B2865149 : Blo 1271954 2865149 := bbase (se 3 (by rfl) ⟨537215, by rfl⟩ : syracuseStep 2865149 = 1074431) (by norm_num)
theorem B1431553 : Blo 1271954 1431553 := bbase (se 2 (by rfl) ⟨536832, by rfl⟩ : syracuseStep 1431553 = 1073665) (by norm_num)
theorem B1431589 : Blo 1271954 1431589 := bbase (se 4 (by rfl) ⟨134211, by rfl⟩ : syracuseStep 1431589 = 268423) (by norm_num)
theorem B1611829 : Blo 1271954 1611829 := bbase (se 5 (by rfl) ⟨75554, by rfl⟩ : syracuseStep 1611829 = 151109) (by norm_num)
theorem B2865221 : Blo 1271954 2865221 := bbase (se 4 (by rfl) ⟨268614, by rfl⟩ : syracuseStep 2865221 = 537229) (by norm_num)
theorem B1431625 : Blo 1271954 1431625 := bbase (se 2 (by rfl) ⟨536859, by rfl⟩ : syracuseStep 1431625 = 1073719) (by norm_num)
theorem B1529941 : Blo 1271954 1529941 := bbase (se 8 (by rfl) ⟨8964, by rfl⟩ : syracuseStep 1529941 = 17929) (by norm_num)
theorem B1431661 : Blo 1271954 1431661 := bbase (se 3 (by rfl) ⟨268436, by rfl⟩ : syracuseStep 1431661 = 536873) (by norm_num)
theorem B1529969 : Blo 1271954 1529969 := bbase (se 2 (by rfl) ⟨573738, by rfl⟩ : syracuseStep 1529969 = 1147477) (by norm_num)
theorem B4298885 : Blo 1271954 4298885 := bbase (se 4 (by rfl) ⟨403020, by rfl⟩ : syracuseStep 4298885 = 806041) (by norm_num)
theorem B2865293 : Blo 1271954 2865293 := bbase (se 3 (by rfl) ⟨537242, by rfl⟩ : syracuseStep 2865293 = 1074485) (by norm_num)
theorem B1431697 : Blo 1271954 1431697 := bbase (se 2 (by rfl) ⟨536886, by rfl⟩ : syracuseStep 1431697 = 1073773) (by norm_num)
theorem B1431733 : Blo 1271954 1431733 := bbase (se 5 (by rfl) ⟨67112, by rfl⟩ : syracuseStep 1431733 = 134225) (by norm_num)
theorem B2037973 : Blo 1271954 2037973 := bbase (se 7 (by rfl) ⟨23882, by rfl⟩ : syracuseStep 2037973 = 47765) (by norm_num)
theorem B13760725 : Blo 1271954 13760725 := bbase (se 7 (by rfl) ⟨161258, by rfl⟩ : syracuseStep 13760725 = 322517) (by norm_num)
theorem B2865365 : Blo 1271954 2865365 := bbase (se 7 (by rfl) ⟨33578, by rfl⟩ : syracuseStep 2865365 = 67157) (by norm_num)
theorem B1431769 : Blo 1271954 1431769 := bbase (se 2 (by rfl) ⟨536913, by rfl⟩ : syracuseStep 1431769 = 1073827) (by norm_num)
theorem B1612001 : Blo 1271954 1612001 := bbase (se 2 (by rfl) ⟨604500, by rfl⟩ : syracuseStep 1612001 = 1209001) (by norm_num)
theorem B1530085 : Blo 1271954 1530085 := bbase (se 4 (by rfl) ⟨143445, by rfl⟩ : syracuseStep 1530085 = 286891) (by norm_num)
theorem B1431805 : Blo 1271954 1431805 := bbase (se 3 (by rfl) ⟨268463, by rfl⟩ : syracuseStep 1431805 = 536927) (by norm_num)
theorem B1612057 : Blo 1271954 1612057 := bbase (se 2 (by rfl) ⟨604521, by rfl⟩ : syracuseStep 1612057 = 1209043) (by norm_num)
theorem B2865437 : Blo 1271954 2865437 := bbase (se 3 (by rfl) ⟨537269, by rfl⟩ : syracuseStep 2865437 = 1074539) (by norm_num)
theorem B1431841 : Blo 1271954 1431841 := bbase (se 2 (by rfl) ⟨536940, by rfl⟩ : syracuseStep 1431841 = 1073881) (by norm_num)
theorem B1431877 : Blo 1271954 1431877 := bbase (se 4 (by rfl) ⟨134238, by rfl⟩ : syracuseStep 1431877 = 268477) (by norm_num)
theorem B1530181 : Blo 1271954 1530181 := bbase (se 4 (by rfl) ⟨143454, by rfl⟩ : syracuseStep 1530181 = 286909) (by norm_num)
theorem B2865509 : Blo 1271954 2865509 := bbase (se 4 (by rfl) ⟨268641, by rfl⟩ : syracuseStep 2865509 = 537283) (by norm_num)
theorem B1431913 : Blo 1271954 1431913 := bbase (se 2 (by rfl) ⟨536967, by rfl⟩ : syracuseStep 1431913 = 1073935) (by norm_num)
theorem B1612153 : Blo 1271954 1612153 := bbase (se 2 (by rfl) ⟨604557, by rfl⟩ : syracuseStep 1612153 = 1209115) (by norm_num)
theorem B1431949 : Blo 1271954 1431949 := bbase (se 3 (by rfl) ⟨268490, by rfl⟩ : syracuseStep 1431949 = 536981) (by norm_num)
theorem B3627413 : Blo 1271954 3627413 := bbase (se 6 (by rfl) ⟨85017, by rfl⟩ : syracuseStep 3627413 = 170035) (by norm_num)
theorem B2865581 : Blo 1271954 2865581 := bbase (se 3 (by rfl) ⟨537296, by rfl⟩ : syracuseStep 2865581 = 1074593) (by norm_num)
theorem B1431985 : Blo 1271954 1431985 := bbase (se 2 (by rfl) ⟨536994, by rfl⟩ : syracuseStep 1431985 = 1073989) (by norm_num)
theorem B6445493 : Blo 1271954 6445493 := bbase (se 5 (by rfl) ⟨302132, by rfl⟩ : syracuseStep 6445493 = 604265) (by norm_num)
theorem B4078021 : Blo 1271954 4078021 := bbase (se 4 (by rfl) ⟨382314, by rfl⟩ : syracuseStep 4078021 = 764629) (by norm_num)
theorem B1432021 : Blo 1271954 1432021 := bbase (se 7 (by rfl) ⟨16781, by rfl⟩ : syracuseStep 1432021 = 33563) (by norm_num)
theorem B2865653 : Blo 1271954 2865653 := bbase (se 5 (by rfl) ⟨134327, by rfl⟩ : syracuseStep 2865653 = 268655) (by norm_num)
theorem B1432057 : Blo 1271954 1432057 := bbase (se 2 (by rfl) ⟨537021, by rfl⟩ : syracuseStep 1432057 = 1074043) (by norm_num)
theorem B2415109 : Blo 1271954 2415109 := bbase (se 4 (by rfl) ⟨226416, by rfl⟩ : syracuseStep 2415109 = 452833) (by norm_num)
theorem B1432093 : Blo 1271954 1432093 := bbase (se 3 (by rfl) ⟨268517, by rfl⟩ : syracuseStep 1432093 = 537035) (by norm_num)
theorem B1612325 : Blo 1271954 1612325 := bbase (se 4 (by rfl) ⟨151155, by rfl⟩ : syracuseStep 1612325 = 302311) (by norm_num)
theorem B4299317 : Blo 1271954 4299317 := bbase (se 5 (by rfl) ⟨201530, by rfl⟩ : syracuseStep 4299317 = 403061) (by norm_num)
theorem B2865725 : Blo 1271954 2865725 := bbase (se 3 (by rfl) ⟨537323, by rfl⟩ : syracuseStep 2865725 = 1074647) (by norm_num)
theorem B1432129 : Blo 1271954 1432129 := bbase (se 2 (by rfl) ⟨537048, by rfl⟩ : syracuseStep 1432129 = 1074097) (by norm_num)
theorem B2292301 : Blo 1271954 2292301 := bbase (se 3 (by rfl) ⟨429806, by rfl⟩ : syracuseStep 2292301 = 859613) (by norm_num)
theorem B1432165 : Blo 1271954 1432165 := bbase (se 4 (by rfl) ⟨134265, by rfl⟩ : syracuseStep 1432165 = 268531) (by norm_num)
theorem B2865797 : Blo 1271954 2865797 := bbase (se 4 (by rfl) ⟨268668, by rfl⟩ : syracuseStep 2865797 = 537337) (by norm_num)
theorem B1432201 : Blo 1271954 1432201 := bbase (se 2 (by rfl) ⟨537075, by rfl⟩ : syracuseStep 1432201 = 1074151) (by norm_num)
theorem B2415253 : Blo 1271954 2415253 := bbase (se 6 (by rfl) ⟨56607, by rfl⟩ : syracuseStep 2415253 = 113215) (by norm_num)
theorem B2718373 : Blo 1271954 2718373 := bbase (se 4 (by rfl) ⟨254847, by rfl⟩ : syracuseStep 2718373 = 509695) (by norm_num)
theorem B1432237 : Blo 1271954 1432237 := bbase (se 3 (by rfl) ⟨268544, by rfl⟩ : syracuseStep 1432237 = 537089) (by norm_num)
theorem B4078277 : Blo 1271954 4078277 := bbase (se 4 (by rfl) ⟨382338, by rfl⟩ : syracuseStep 4078277 = 764677) (by norm_num)
theorem B1358537 : Blo 1271954 1358537 := bbase (se 2 (by rfl) ⟨509451, by rfl⟩ : syracuseStep 1358537 = 1018903) (by norm_num)
theorem B2865869 : Blo 1271954 2865869 := bbase (se 3 (by rfl) ⟨537350, by rfl⟩ : syracuseStep 2865869 = 1074701) (by norm_num)
theorem B1432273 : Blo 1271954 1432273 := bbase (se 2 (by rfl) ⟨537102, by rfl⟩ : syracuseStep 1432273 = 1074205) (by norm_num)
theorem B7248629 : Blo 1271954 7248629 := bbase (se 5 (by rfl) ⟨339779, by rfl⟩ : syracuseStep 7248629 = 679559) (by norm_num)
theorem B1432309 : Blo 1271954 1432309 := bbase (se 5 (by rfl) ⟨67139, by rfl⟩ : syracuseStep 1432309 = 134279) (by norm_num)
theorem B2865941 : Blo 1271954 2865941 := bbase (se 6 (by rfl) ⟨67170, by rfl⟩ : syracuseStep 2865941 = 134341) (by norm_num)
theorem B1432345 : Blo 1271954 1432345 := bbase (se 2 (by rfl) ⟨537129, by rfl⟩ : syracuseStep 1432345 = 1074259) (by norm_num)
theorem B2415413 : Blo 1271954 2415413 := bbase (se 5 (by rfl) ⟨113222, by rfl⟩ : syracuseStep 2415413 = 226445) (by norm_num)
theorem B1432381 : Blo 1271954 1432381 := bbase (se 3 (by rfl) ⟨268571, by rfl⟩ : syracuseStep 1432381 = 537143) (by norm_num)
theorem B2866013 : Blo 1271954 2866013 := bbase (se 3 (by rfl) ⟨537377, by rfl⟩ : syracuseStep 2866013 = 1074755) (by norm_num)
theorem B1432417 : Blo 1271954 1432417 := bbase (se 2 (by rfl) ⟨537156, by rfl⟩ : syracuseStep 1432417 = 1074313) (by norm_num)
theorem B1432453 : Blo 1271954 1432453 := bbase (se 4 (by rfl) ⟨134292, by rfl⟩ : syracuseStep 1432453 = 268585) (by norm_num)
theorem B2866085 : Blo 1271954 2866085 := bbase (se 4 (by rfl) ⟨268695, by rfl⟩ : syracuseStep 2866085 = 537391) (by norm_num)
theorem B1432489 : Blo 1271954 1432489 := bbase (se 2 (by rfl) ⟨537183, by rfl⟩ : syracuseStep 1432489 = 1074367) (by norm_num)
theorem B1358785 : Blo 1271954 1358785 := bbase (se 2 (by rfl) ⟨509544, by rfl⟩ : syracuseStep 1358785 = 1019089) (by norm_num)
theorem B2415557 : Blo 1271954 2415557 := bbase (se 4 (by rfl) ⟨226458, by rfl⟩ : syracuseStep 2415557 = 452917) (by norm_num)
theorem B1432525 : Blo 1271954 1432525 := bbase (se 3 (by rfl) ⟨268598, by rfl⟩ : syracuseStep 1432525 = 537197) (by norm_num)
theorem B27884501 : Blo 1271954 27884501 := bbase (se 7 (by rfl) ⟨326771, by rfl⟩ : syracuseStep 27884501 = 653543) (by norm_num)
theorem B2866157 : Blo 1271954 2866157 := bbase (se 3 (by rfl) ⟨537404, by rfl⟩ : syracuseStep 2866157 = 1074809) (by norm_num)
theorem B1432561 : Blo 1271954 1432561 := bbase (se 2 (by rfl) ⟨537210, by rfl⟩ : syracuseStep 1432561 = 1074421) (by norm_num)
theorem B1432597 : Blo 1271954 1432597 := bbase (se 6 (by rfl) ⟨33576, by rfl⟩ : syracuseStep 1432597 = 67153) (by norm_num)
theorem B2178085 : Blo 1271954 2178085 := bbase (se 4 (by rfl) ⟨204195, by rfl⟩ : syracuseStep 2178085 = 408391) (by norm_num)
theorem B4586549 : Blo 1271954 4586549 := bbase (se 5 (by rfl) ⟨214994, by rfl⟩ : syracuseStep 4586549 = 429989) (by norm_num)
theorem B2866229 : Blo 1271954 2866229 := bbase (se 5 (by rfl) ⟨134354, by rfl⟩ : syracuseStep 2866229 = 268709) (by norm_num)
theorem B1432633 : Blo 1271954 1432633 := bbase (se 2 (by rfl) ⟨537237, by rfl⟩ : syracuseStep 1432633 = 1074475) (by norm_num)
theorem B1432669 : Blo 1271954 1432669 := bbase (se 3 (by rfl) ⟨268625, by rfl⟩ : syracuseStep 1432669 = 537251) (by norm_num)
theorem B2866301 : Blo 1271954 2866301 := bbase (se 3 (by rfl) ⟨537431, by rfl⟩ : syracuseStep 2866301 = 1074863) (by norm_num)
theorem B1432705 : Blo 1271954 1432705 := bbase (se 2 (by rfl) ⟨537264, by rfl⟩ : syracuseStep 1432705 = 1074529) (by norm_num)
theorem B6200453 : Blo 1271954 6200453 := bbase (se 4 (by rfl) ⟨581292, by rfl⟩ : syracuseStep 6200453 = 1162585) (by norm_num)
theorem B4832405 : Blo 1271954 4832405 := bbase (se 6 (by rfl) ⟨113259, by rfl⟩ : syracuseStep 4832405 = 226519) (by norm_num)
theorem B1432741 : Blo 1271954 1432741 := bbase (se 4 (by rfl) ⟨134319, by rfl⟩ : syracuseStep 1432741 = 268639) (by norm_num)
theorem B2866373 : Blo 1271954 2866373 := bbase (se 4 (by rfl) ⟨268722, by rfl⟩ : syracuseStep 2866373 = 537445) (by norm_num)
theorem B1432777 : Blo 1271954 1432777 := bbase (se 2 (by rfl) ⟨537291, by rfl⟩ : syracuseStep 1432777 = 1074583) (by norm_num)
theorem B1907933 : Blo 1271954 1907933 := bbase (se 3 (by rfl) ⟨357737, by rfl⟩ : syracuseStep 1907933 = 715475) (by norm_num)
theorem B2292965 : Blo 1271954 2292965 := bbase (se 4 (by rfl) ⟨214965, by rfl⟩ : syracuseStep 2292965 = 429931) (by norm_num)
theorem B2415845 : Blo 1271954 2415845 := bbase (se 4 (by rfl) ⟨226485, by rfl⟩ : syracuseStep 2415845 = 452971) (by norm_num)
theorem B1432813 : Blo 1271954 1432813 := bbase (se 3 (by rfl) ⟨268652, by rfl⟩ : syracuseStep 1432813 = 537305) (by norm_num)
theorem B1907957 : Blo 1271954 1907957 := bbase (se 5 (by rfl) ⟨89435, by rfl⟩ : syracuseStep 1907957 = 178871) (by norm_num)
theorem B1907981 : Blo 1271954 1907981 := bbase (se 3 (by rfl) ⟨357746, by rfl⟩ : syracuseStep 1907981 = 715493) (by norm_num)
theorem B1432849 : Blo 1271954 1432849 := bbase (se 2 (by rfl) ⟨537318, by rfl⟩ : syracuseStep 1432849 = 1074637) (by norm_num)
theorem B1908005 : Blo 1271954 1908005 := bbase (se 4 (by rfl) ⟨178875, by rfl⟩ : syracuseStep 1908005 = 357751) (by norm_num)
theorem B1432885 : Blo 1271954 1432885 := bbase (se 5 (by rfl) ⟨67166, by rfl⟩ : syracuseStep 1432885 = 134333) (by norm_num)
theorem B1908029 : Blo 1271954 1908029 := bbase (se 3 (by rfl) ⟨357755, by rfl⟩ : syracuseStep 1908029 = 715511) (by norm_num)
theorem B1908053 : Blo 1271954 1908053 := bbase (se 11 (by rfl) ⟨1397, by rfl⟩ : syracuseStep 1908053 = 2795) (by norm_num)
theorem B1432921 : Blo 1271954 1432921 := bbase (se 2 (by rfl) ⟨537345, by rfl⟩ : syracuseStep 1432921 = 1074691) (by norm_num)
theorem B1908077 : Blo 1271954 1908077 := bbase (se 3 (by rfl) ⟨357764, by rfl⟩ : syracuseStep 1908077 = 715529) (by norm_num)
theorem B1359217 : Blo 1271954 1359217 := bbase (se 2 (by rfl) ⟨509706, by rfl⟩ : syracuseStep 1359217 = 1019413) (by norm_num)
theorem B2415997 : Blo 1271954 2415997 := bbase (se 3 (by rfl) ⟨452999, by rfl⟩ : syracuseStep 2415997 = 905999) (by norm_num)
theorem B2039165 : Blo 1271954 2039165 := bbase (se 3 (by rfl) ⟨382343, by rfl⟩ : syracuseStep 2039165 = 764687) (by norm_num)
theorem B1432957 : Blo 1271954 1432957 := bbase (se 3 (by rfl) ⟨268679, by rfl⟩ : syracuseStep 1432957 = 537359) (by norm_num)
theorem B1908101 : Blo 1271954 1908101 := bbase (se 4 (by rfl) ⟨178884, by rfl⟩ : syracuseStep 1908101 = 357769) (by norm_num)
theorem B2579845 : Blo 1271954 2579845 := bbase (se 4 (by rfl) ⟨241860, by rfl⟩ : syracuseStep 2579845 = 483721) (by norm_num)
theorem B1908125 : Blo 1271954 1908125 := bbase (se 3 (by rfl) ⟨357773, by rfl⟩ : syracuseStep 1908125 = 715547) (by norm_num)
theorem B1432993 : Blo 1271954 1432993 := bbase (se 2 (by rfl) ⟨537372, by rfl⟩ : syracuseStep 1432993 = 1074745) (by norm_num)
theorem B1908149 : Blo 1271954 1908149 := bbase (se 5 (by rfl) ⟨89444, by rfl⟩ : syracuseStep 1908149 = 178889) (by norm_num)
theorem B4832693 : Blo 1271954 4832693 := bbase (se 5 (by rfl) ⟨226532, by rfl⟩ : syracuseStep 4832693 = 453065) (by norm_num)
theorem B9182645 : Blo 1271954 9182645 := bbase (se 5 (by rfl) ⟨430436, by rfl⟩ : syracuseStep 9182645 = 860873) (by norm_num)
theorem B1359289 : Blo 1271954 1359289 := bbase (se 2 (by rfl) ⟨509733, by rfl⟩ : syracuseStep 1359289 = 1019467) (by norm_num)
theorem B1433029 : Blo 1271954 1433029 := bbase (se 4 (by rfl) ⟨134346, by rfl⟩ : syracuseStep 1433029 = 268693) (by norm_num)
theorem B1908173 : Blo 1271954 1908173 := bbase (se 3 (by rfl) ⟨357782, by rfl⟩ : syracuseStep 1908173 = 715565) (by norm_num)
theorem B5438933 : Blo 1271954 5438933 := bbase (se 7 (by rfl) ⟨63737, by rfl⟩ : syracuseStep 5438933 = 127475) (by norm_num)
theorem B1908197 : Blo 1271954 1908197 := bbase (se 4 (by rfl) ⟨178893, by rfl⟩ : syracuseStep 1908197 = 357787) (by norm_num)
theorem B1433065 : Blo 1271954 1433065 := bbase (se 2 (by rfl) ⟨537399, by rfl⟩ : syracuseStep 1433065 = 1074799) (by norm_num)
theorem B3440117 : Blo 1271954 3440117 := bbase (se 5 (by rfl) ⟨161255, by rfl⟩ : syracuseStep 3440117 = 322511) (by norm_num)
theorem B1908221 : Blo 1271954 1908221 := bbase (se 3 (by rfl) ⟨357791, by rfl⟩ : syracuseStep 1908221 = 715583) (by norm_num)
theorem B1433101 : Blo 1271954 1433101 := bbase (se 3 (by rfl) ⟨268706, by rfl⟩ : syracuseStep 1433101 = 537413) (by norm_num)
theorem B1908245 : Blo 1271954 1908245 := bbase (se 6 (by rfl) ⟨44724, by rfl⟩ : syracuseStep 1908245 = 89449) (by norm_num)
theorem B2719261 : Blo 1271954 2719261 := bbase (se 3 (by rfl) ⟨509861, by rfl⟩ : syracuseStep 2719261 = 1019723) (by norm_num)
theorem B1908269 : Blo 1271954 1908269 := bbase (se 3 (by rfl) ⟨357800, by rfl⟩ : syracuseStep 1908269 = 715601) (by norm_num)
theorem B1433137 : Blo 1271954 1433137 := bbase (se 2 (by rfl) ⟨537426, by rfl⟩ : syracuseStep 1433137 = 1074853) (by norm_num)
theorem B2039357 : Blo 1271954 2039357 := bbase (se 3 (by rfl) ⟨382379, by rfl⟩ : syracuseStep 2039357 = 764759) (by norm_num)
theorem B1908293 : Blo 1271954 1908293 := bbase (se 4 (by rfl) ⟨178902, by rfl⟩ : syracuseStep 1908293 = 357805) (by norm_num)
theorem B1433173 : Blo 1271954 1433173 := bbase (se 8 (by rfl) ⟨8397, by rfl⟩ : syracuseStep 1433173 = 16795) (by norm_num)
theorem B1908317 : Blo 1271954 1908317 := bbase (se 3 (by rfl) ⟨357809, by rfl⟩ : syracuseStep 1908317 = 715619) (by norm_num)
theorem B1908341 : Blo 1271954 1908341 := bbase (se 5 (by rfl) ⟨89453, by rfl⟩ : syracuseStep 1908341 = 178907) (by norm_num)
theorem B1908365 : Blo 1271954 1908365 := bbase (se 3 (by rfl) ⟨357818, by rfl⟩ : syracuseStep 1908365 = 715637) (by norm_num)
theorem B2178701 : Blo 1271954 2178701 := bbase (se 3 (by rfl) ⟨408506, by rfl⟩ : syracuseStep 2178701 = 817013) (by norm_num)
theorem B1908389 : Blo 1271954 1908389 := bbase (se 4 (by rfl) ⟨178911, by rfl⟩ : syracuseStep 1908389 = 357823) (by norm_num)
theorem B2416301 : Blo 1271954 2416301 := bbase (se 3 (by rfl) ⟨453056, by rfl⟩ : syracuseStep 2416301 = 906113) (by norm_num)
theorem B1908413 : Blo 1271954 1908413 := bbase (se 3 (by rfl) ⟨357827, by rfl⟩ : syracuseStep 1908413 = 715655) (by norm_num)
theorem B6446789 : Blo 1271954 6446789 := bbase (se 4 (by rfl) ⟨604386, by rfl⟩ : syracuseStep 6446789 = 1208773) (by norm_num)
theorem B1908437 : Blo 1271954 1908437 := bbase (se 7 (by rfl) ⟨22364, by rfl⟩ : syracuseStep 1908437 = 44729) (by norm_num)
theorem B1908461 : Blo 1271954 1908461 := bbase (se 3 (by rfl) ⟨357836, by rfl⟩ : syracuseStep 1908461 = 715673) (by norm_num)
theorem B2178797 : Blo 1271954 2178797 := bbase (se 3 (by rfl) ⟨408524, by rfl⟩ : syracuseStep 2178797 = 817049) (by norm_num)
theorem B1908485 : Blo 1271954 1908485 := bbase (se 4 (by rfl) ⟨178920, by rfl⟩ : syracuseStep 1908485 = 357841) (by norm_num)
theorem B1908509 : Blo 1271954 1908509 := bbase (se 3 (by rfl) ⟨357845, by rfl⟩ : syracuseStep 1908509 = 715691) (by norm_num)
theorem B1359661 : Blo 1271954 1359661 := bbase (se 3 (by rfl) ⟨254936, by rfl⟩ : syracuseStep 1359661 = 509873) (by norm_num)
theorem B1908533 : Blo 1271954 1908533 := bbase (se 5 (by rfl) ⟨89462, by rfl⟩ : syracuseStep 1908533 = 178925) (by norm_num)
theorem B1908557 : Blo 1271954 1908557 := bbase (se 3 (by rfl) ⟨357854, by rfl⟩ : syracuseStep 1908557 = 715709) (by norm_num)
theorem B3923797 : Blo 1271954 3923797 := bbase (se 9 (by rfl) ⟨11495, by rfl⟩ : syracuseStep 3923797 = 22991) (by norm_num)
theorem B1908581 : Blo 1271954 1908581 := bbase (se 4 (by rfl) ⟨178929, by rfl⟩ : syracuseStep 1908581 = 357859) (by norm_num)
theorem B3440485 : Blo 1271954 3440485 := bbase (se 4 (by rfl) ⟨322545, by rfl⟩ : syracuseStep 3440485 = 645091) (by norm_num)
theorem B1908605 : Blo 1271954 1908605 := bbase (se 3 (by rfl) ⟨357863, by rfl⟩ : syracuseStep 1908605 = 715727) (by norm_num)
theorem B1908629 : Blo 1271954 1908629 := bbase (se 6 (by rfl) ⟨44733, by rfl⟩ : syracuseStep 1908629 = 89467) (by norm_num)
theorem B1908653 : Blo 1271954 1908653 := bbase (se 3 (by rfl) ⟨357872, by rfl⟩ : syracuseStep 1908653 = 715745) (by norm_num)
theorem B1908677 : Blo 1271954 1908677 := bbase (se 4 (by rfl) ⟨178938, by rfl⟩ : syracuseStep 1908677 = 357877) (by norm_num)
theorem B1908701 : Blo 1271954 1908701 := bbase (se 3 (by rfl) ⟨357881, by rfl⟩ : syracuseStep 1908701 = 715763) (by norm_num)
theorem B1908725 : Blo 1271954 1908725 := bbase (se 5 (by rfl) ⟨89471, by rfl⟩ : syracuseStep 1908725 = 178943) (by norm_num)
theorem B1908737 : Blo 1271954 1908737 := bstep (se 2 (by rfl) ⟨715776, by rfl⟩ : syracuseStep 1908737 = 1431553) B1431553
theorem B1908755 : Blo 1271954 1908755 := bstep (se 1 (by rfl) ⟨1431566, by rfl⟩ : syracuseStep 1908755 = 2863133) B2863133
theorem B1908785 : Blo 1271954 1908785 := bstep (se 2 (by rfl) ⟨715794, by rfl⟩ : syracuseStep 1908785 = 1431589) B1431589
theorem B1908803 : Blo 1271954 1908803 := bstep (se 1 (by rfl) ⟨1431602, by rfl⟩ : syracuseStep 1908803 = 2863205) B2863205
theorem B1908833 : Blo 1271954 1908833 := bstep (se 2 (by rfl) ⟨715812, by rfl⟩ : syracuseStep 1908833 = 1431625) B1431625
theorem B2039921 : Blo 1271954 2039921 := bstep (se 2 (by rfl) ⟨764970, by rfl⟩ : syracuseStep 2039921 = 1529941) B1529941
theorem B1908851 : Blo 1271954 1908851 := bstep (se 1 (by rfl) ⟨1431638, by rfl⟩ : syracuseStep 1908851 = 2863277) B2863277
theorem B12230797 : Blo 1271954 12230797 := bstep (se 3 (by rfl) ⟨2293274, by rfl⟩ : syracuseStep 12230797 = 4586549) B4586549
theorem B1908881 : Blo 1271954 1908881 := bstep (se 2 (by rfl) ⟨715830, by rfl⟩ : syracuseStep 1908881 = 1431661) B1431661
theorem B1908899 : Blo 1271954 1908899 := bstep (se 1 (by rfl) ⟨1431674, by rfl⟩ : syracuseStep 1908899 = 2863349) B2863349
theorem B2416817 : Blo 1271954 2416817 := bstep (se 2 (by rfl) ⟨906306, by rfl⟩ : syracuseStep 2416817 = 1812613) B1812613
theorem B1908929 : Blo 1271954 1908929 := bstep (se 2 (by rfl) ⟨715848, by rfl⟩ : syracuseStep 1908929 = 1431697) B1431697
theorem B2146513 : Blo 1271954 2146513 := bstep (se 2 (by rfl) ⟨804942, by rfl⟩ : syracuseStep 2146513 = 1609885) B1609885
theorem B1908947 : Blo 1271954 1908947 := bstep (se 1 (by rfl) ⟨1431710, by rfl⟩ : syracuseStep 1908947 = 2863421) B2863421
theorem B1908977 : Blo 1271954 1908977 := bstep (se 2 (by rfl) ⟨715866, by rfl⟩ : syracuseStep 1908977 = 1431733) B1431733
theorem B2146547 : Blo 1271954 2146547 := bstep (se 1 (by rfl) ⟨1609910, by rfl⟩ : syracuseStep 2146547 = 3219821) B3219821
theorem B1908995 : Blo 1271954 1908995 := bstep (se 1 (by rfl) ⟨1431746, by rfl⟩ : syracuseStep 1908995 = 2863493) B2863493
theorem B1909025 : Blo 1271954 1909025 := bstep (se 2 (by rfl) ⟨715884, by rfl⟩ : syracuseStep 1909025 = 1431769) B1431769
theorem B4079917 : Blo 1271954 4079917 := bstep (se 3 (by rfl) ⟨764984, by rfl⟩ : syracuseStep 4079917 = 1529969) B1529969
theorem B2040113 : Blo 1271954 2040113 := bstep (se 2 (by rfl) ⟨765042, by rfl⟩ : syracuseStep 2040113 = 1530085) B1530085
theorem B1909043 : Blo 1271954 1909043 := bstep (se 1 (by rfl) ⟨1431782, by rfl⟩ : syracuseStep 1909043 = 2863565) B2863565
theorem B6447437 : Blo 1271954 6447437 := bstep (se 3 (by rfl) ⟨1208894, by rfl⟩ : syracuseStep 6447437 = 2417789) B2417789
theorem B4292945 : Blo 1271954 4292945 := bstep (se 2 (by rfl) ⟨1609854, by rfl⟩ : syracuseStep 4292945 = 3219709) B3219709
theorem B1909073 : Blo 1271954 1909073 := bstep (se 2 (by rfl) ⟨715902, by rfl⟩ : syracuseStep 1909073 = 1431805) B1431805
theorem B1909091 : Blo 1271954 1909091 := bstep (se 1 (by rfl) ⟨1431818, by rfl⟩ : syracuseStep 1909091 = 2863637) B2863637
theorem B2146675 : Blo 1271954 2146675 := bstep (se 1 (by rfl) ⟨1610006, by rfl⟩ : syracuseStep 2146675 = 3220013) B3220013
theorem B1909121 : Blo 1271954 1909121 := bstep (se 2 (by rfl) ⟨715920, by rfl⟩ : syracuseStep 1909121 = 1431841) B1431841
theorem B8159629 : Blo 1271954 8159629 := bstep (se 3 (by rfl) ⟨1529930, by rfl⟩ : syracuseStep 8159629 = 3059861) B3059861
theorem B1909139 : Blo 1271954 1909139 := bstep (se 1 (by rfl) ⟨1431854, by rfl⟩ : syracuseStep 1909139 = 2863709) B2863709
theorem B1909169 : Blo 1271954 1909169 := bstep (se 2 (by rfl) ⟨715938, by rfl⟩ : syracuseStep 1909169 = 1431877) B1431877
theorem B2040241 : Blo 1271954 2040241 := bstep (se 2 (by rfl) ⟨765090, by rfl⟩ : syracuseStep 2040241 = 1530181) B1530181
theorem B1909187 : Blo 1271954 1909187 := bstep (se 1 (by rfl) ⟨1431890, by rfl⟩ : syracuseStep 1909187 = 2863781) B2863781
theorem B1909217 : Blo 1271954 1909217 := bstep (se 2 (by rfl) ⟨715956, by rfl⟩ : syracuseStep 1909217 = 1431913) B1431913
theorem B1909235 : Blo 1271954 1909235 := bstep (se 1 (by rfl) ⟨1431926, by rfl⟩ : syracuseStep 1909235 = 2863853) B2863853
theorem B2146817 : Blo 1271954 2146817 := bstep (se 2 (by rfl) ⟨805056, by rfl⟩ : syracuseStep 2146817 = 1610113) B1610113
theorem B14508557 : Blo 1271954 14508557 := bstep (se 3 (by rfl) ⟨2720354, by rfl⟩ : syracuseStep 14508557 = 5440709) B5440709
theorem B1909265 : Blo 1271954 1909265 := bstep (se 2 (by rfl) ⟨715974, by rfl⟩ : syracuseStep 1909265 = 1431949) B1431949
theorem B1909283 : Blo 1271954 1909283 := bstep (se 1 (by rfl) ⟨1431962, by rfl⟩ : syracuseStep 1909283 = 2863925) B2863925
theorem B13754933 : Blo 1271954 13754933 := bstep (se 5 (by rfl) ⟨644762, by rfl⟩ : syracuseStep 13754933 = 1289525) B1289525
theorem B1909313 : Blo 1271954 1909313 := bstep (se 2 (by rfl) ⟨715992, by rfl⟩ : syracuseStep 1909313 = 1431985) B1431985
theorem B1909331 : Blo 1271954 1909331 := bstep (se 1 (by rfl) ⟨1431998, by rfl⟩ : syracuseStep 1909331 = 2863997) B2863997
theorem B1909361 : Blo 1271954 1909361 := bstep (se 2 (by rfl) ⟨716010, by rfl⟩ : syracuseStep 1909361 = 1432021) B1432021
theorem B13951601 : Blo 1271954 13951601 := bstep (se 2 (by rfl) ⟨5231850, by rfl⟩ : syracuseStep 13951601 = 10463701) B10463701
theorem B2146945 : Blo 1271954 2146945 := bstep (se 2 (by rfl) ⟨805104, by rfl⟩ : syracuseStep 2146945 = 1610209) B1610209
theorem B1909379 : Blo 1271954 1909379 := bstep (se 1 (by rfl) ⟨1432034, by rfl⟩ : syracuseStep 1909379 = 2864069) B2864069
theorem B1909409 : Blo 1271954 1909409 := bstep (se 2 (by rfl) ⟨716028, by rfl⟩ : syracuseStep 1909409 = 1432057) B1432057
theorem B2146979 : Blo 1271954 2146979 := bstep (se 1 (by rfl) ⟨1610234, by rfl⟩ : syracuseStep 2146979 = 3220469) B3220469
theorem B2294435 : Blo 1271954 2294435 := bstep (se 1 (by rfl) ⟨1720826, by rfl⟩ : syracuseStep 2294435 = 3441653) B3441653
theorem B3220145 : Blo 1271954 3220145 := bstep (se 2 (by rfl) ⟨1207554, by rfl⟩ : syracuseStep 3220145 = 2415109) B2415109
theorem B1909427 : Blo 1271954 1909427 := bstep (se 1 (by rfl) ⟨1432070, by rfl⟩ : syracuseStep 1909427 = 2864141) B2864141
theorem B1909457 : Blo 1271954 1909457 := bstep (se 2 (by rfl) ⟨716046, by rfl⟩ : syracuseStep 1909457 = 1432093) B1432093
theorem B1811155 : Blo 1271954 1811155 := bstep (se 1 (by rfl) ⟨1358366, by rfl⟩ : syracuseStep 1811155 = 2716733) B2716733
theorem B3220195 : Blo 1271954 3220195 := bstep (se 1 (by rfl) ⟨2415146, by rfl⟩ : syracuseStep 3220195 = 4830293) B4830293
theorem B1909475 : Blo 1271954 1909475 := bstep (se 1 (by rfl) ⟨1432106, by rfl⟩ : syracuseStep 1909475 = 2864213) B2864213
theorem B1909505 : Blo 1271954 1909505 := bstep (se 2 (by rfl) ⟨716064, by rfl⟩ : syracuseStep 1909505 = 1432129) B1432129
theorem B7742213 : Blo 1271954 7742213 := bstep (se 4 (by rfl) ⟨725832, by rfl⟩ : syracuseStep 7742213 = 1451665) B1451665
theorem B3056401 : Blo 1271954 3056401 := bstep (se 2 (by rfl) ⟨1146150, by rfl⟩ : syracuseStep 3056401 = 2292301) B2292301
theorem B1909523 : Blo 1271954 1909523 := bstep (se 1 (by rfl) ⟨1432142, by rfl⟩ : syracuseStep 1909523 = 2864285) B2864285
theorem B2147107 : Blo 1271954 2147107 := bstep (se 1 (by rfl) ⟨1610330, by rfl⟩ : syracuseStep 2147107 = 3220661) B3220661
theorem B4080419 : Blo 1271954 4080419 := bstep (se 1 (by rfl) ⟨3060314, by rfl⟩ : syracuseStep 4080419 = 6120629) B6120629
theorem B1909553 : Blo 1271954 1909553 := bstep (se 2 (by rfl) ⟨716082, by rfl⟩ : syracuseStep 1909553 = 1432165) B1432165
theorem B1909571 : Blo 1271954 1909571 := bstep (se 1 (by rfl) ⟨1432178, by rfl⟩ : syracuseStep 1909571 = 2864357) B2864357
theorem B1909601 : Blo 1271954 1909601 := bstep (se 2 (by rfl) ⟨716100, by rfl⟩ : syracuseStep 1909601 = 1432201) B1432201
theorem B4293485 : Blo 1271954 4293485 := bstep (se 3 (by rfl) ⟨805028, by rfl⟩ : syracuseStep 4293485 = 1610057) B1610057
theorem B9659249 : Blo 1271954 9659249 := bstep (se 2 (by rfl) ⟨3622218, by rfl⟩ : syracuseStep 9659249 = 7244437) B7244437
theorem B3220337 : Blo 1271954 3220337 := bstep (se 2 (by rfl) ⟨1207626, by rfl⟩ : syracuseStep 3220337 = 2415253) B2415253
theorem B1909619 : Blo 1271954 1909619 := bstep (se 1 (by rfl) ⟨1432214, by rfl⟩ : syracuseStep 1909619 = 2864429) B2864429
theorem B2294659 : Blo 1271954 2294659 := bstep (se 1 (by rfl) ⟨1720994, by rfl⟩ : syracuseStep 2294659 = 3441989) B3441989
theorem B2417539 : Blo 1271954 2417539 := bstep (se 1 (by rfl) ⟨1813154, by rfl⟩ : syracuseStep 2417539 = 3626309) B3626309
theorem B8151941 : Blo 1271954 8151941 := bstep (se 4 (by rfl) ⟨764244, by rfl⟩ : syracuseStep 8151941 = 1528489) B1528489
theorem B1909649 : Blo 1271954 1909649 := bstep (se 2 (by rfl) ⟨716118, by rfl⟩ : syracuseStep 1909649 = 1432237) B1432237
theorem B1934227 : Blo 1271954 1934227 := bstep (se 1 (by rfl) ⟨1450670, by rfl⟩ : syracuseStep 1934227 = 2901341) B2901341
theorem B4293539 : Blo 1271954 4293539 := bstep (se 1 (by rfl) ⟨3220154, by rfl⟩ : syracuseStep 4293539 = 6440309) B6440309
theorem B1909667 : Blo 1271954 1909667 := bstep (se 1 (by rfl) ⟨1432250, by rfl⟩ : syracuseStep 1909667 = 2864501) B2864501
theorem B2147249 : Blo 1271954 2147249 := bstep (se 2 (by rfl) ⟨805218, by rfl⟩ : syracuseStep 2147249 = 1610437) B1610437
theorem B1909697 : Blo 1271954 1909697 := bstep (se 2 (by rfl) ⟨716136, by rfl⟩ : syracuseStep 1909697 = 1432273) B1432273
theorem B1909715 : Blo 1271954 1909715 := bstep (se 1 (by rfl) ⟨1432286, by rfl⟩ : syracuseStep 1909715 = 2864573) B2864573
theorem B1909745 : Blo 1271954 1909745 := bstep (se 2 (by rfl) ⟨716154, by rfl⟩ : syracuseStep 1909745 = 1432309) B1432309
theorem B1909763 : Blo 1271954 1909763 := bstep (se 1 (by rfl) ⟨1432322, by rfl⟩ : syracuseStep 1909763 = 2864645) B2864645
theorem B1909793 : Blo 1271954 1909793 := bstep (se 2 (by rfl) ⟨716172, by rfl⟩ : syracuseStep 1909793 = 1432345) B1432345
theorem B6439985 : Blo 1271954 6439985 := bstep (se 2 (by rfl) ⟨2414994, by rfl⟩ : syracuseStep 6439985 = 4829989) B4829989
theorem B2147377 : Blo 1271954 2147377 := bstep (se 2 (by rfl) ⟨805266, by rfl⟩ : syracuseStep 2147377 = 1610533) B1610533
theorem B1909811 : Blo 1271954 1909811 := bstep (se 1 (by rfl) ⟨1432358, by rfl⟩ : syracuseStep 1909811 = 2864717) B2864717
theorem B1909841 : Blo 1271954 1909841 := bstep (se 2 (by rfl) ⟨716190, by rfl⟩ : syracuseStep 1909841 = 1432381) B1432381
theorem B2147411 : Blo 1271954 2147411 := bstep (se 1 (by rfl) ⟨1610558, by rfl⟩ : syracuseStep 2147411 = 3221117) B3221117
theorem B158917717 : Blo 1271954 158917717 := bstep (se 8 (by rfl) ⟨931158, by rfl⟩ : syracuseStep 158917717 = 1862317) B1862317
theorem B1909859 : Blo 1271954 1909859 := bstep (se 1 (by rfl) ⟨1432394, by rfl⟩ : syracuseStep 1909859 = 2864789) B2864789
theorem B4899953 : Blo 1271954 4899953 := bstep (se 2 (by rfl) ⟨1837482, by rfl⟩ : syracuseStep 4899953 = 3674965) B3674965
theorem B1909889 : Blo 1271954 1909889 := bstep (se 2 (by rfl) ⟨716208, by rfl⟩ : syracuseStep 1909889 = 1432417) B1432417
theorem B1909907 : Blo 1271954 1909907 := bstep (se 1 (by rfl) ⟨1432430, by rfl⟩ : syracuseStep 1909907 = 2864861) B2864861
theorem B4293809 : Blo 1271954 4293809 := bstep (se 2 (by rfl) ⟨1610178, by rfl⟩ : syracuseStep 4293809 = 3220357) B3220357
theorem B1909937 : Blo 1271954 1909937 := bstep (se 2 (by rfl) ⟨716226, by rfl⟩ : syracuseStep 1909937 = 1432453) B1432453
theorem B2901187 : Blo 1271954 2901187 := bstep (se 1 (by rfl) ⟨2175890, by rfl⟩ : syracuseStep 2901187 = 4351781) B4351781
theorem B1909955 : Blo 1271954 1909955 := bstep (se 1 (by rfl) ⟨1432466, by rfl⟩ : syracuseStep 1909955 = 2864933) B2864933
theorem B3441869 : Blo 1271954 3441869 := bstep (se 3 (by rfl) ⟨645350, by rfl⟩ : syracuseStep 3441869 = 1290701) B1290701
theorem B2147539 : Blo 1271954 2147539 := bstep (se 1 (by rfl) ⟨1610654, by rfl⟩ : syracuseStep 2147539 = 3221309) B3221309
theorem B1909985 : Blo 1271954 1909985 := bstep (se 2 (by rfl) ⟨716244, by rfl⟩ : syracuseStep 1909985 = 1432489) B1432489
theorem B1910003 : Blo 1271954 1910003 := bstep (se 1 (by rfl) ⟨1432502, by rfl⟩ : syracuseStep 1910003 = 2865005) B2865005
theorem B1910033 : Blo 1271954 1910033 := bstep (se 2 (by rfl) ⟨716262, by rfl⟩ : syracuseStep 1910033 = 1432525) B1432525
theorem B1910051 : Blo 1271954 1910051 := bstep (se 1 (by rfl) ⟨1432538, by rfl⟩ : syracuseStep 1910051 = 2865077) B2865077
theorem B1910081 : Blo 1271954 1910081 := bstep (se 2 (by rfl) ⟨716280, by rfl⟩ : syracuseStep 1910081 = 1432561) B1432561
theorem B2417987 : Blo 1271954 2417987 := bstep (se 1 (by rfl) ⟨1813490, by rfl⟩ : syracuseStep 2417987 = 3626981) B3626981
theorem B4834637 : Blo 1271954 4834637 := bstep (se 3 (by rfl) ⟨906494, by rfl⟩ : syracuseStep 4834637 = 1812989) B1812989
theorem B1910099 : Blo 1271954 1910099 := bstep (se 1 (by rfl) ⟨1432574, by rfl⟩ : syracuseStep 1910099 = 2865149) B2865149
theorem B2147681 : Blo 1271954 2147681 := bstep (se 2 (by rfl) ⟨805380, by rfl⟩ : syracuseStep 2147681 = 1610761) B1610761
theorem B1910129 : Blo 1271954 1910129 := bstep (se 2 (by rfl) ⟨716298, by rfl⟩ : syracuseStep 1910129 = 1432597) B1432597
theorem B1910147 : Blo 1271954 1910147 := bstep (se 1 (by rfl) ⟨1432610, by rfl⟩ : syracuseStep 1910147 = 2865221) B2865221
theorem B1910177 : Blo 1271954 1910177 := bstep (se 2 (by rfl) ⟨716316, by rfl⟩ : syracuseStep 1910177 = 1432633) B1432633
theorem B1910195 : Blo 1271954 1910195 := bstep (se 1 (by rfl) ⟨1432646, by rfl⟩ : syracuseStep 1910195 = 2865293) B2865293
theorem B1910225 : Blo 1271954 1910225 := bstep (se 2 (by rfl) ⟨716334, by rfl⟩ : syracuseStep 1910225 = 1432669) B1432669
theorem B2147809 : Blo 1271954 2147809 := bstep (se 2 (by rfl) ⟨805428, by rfl⟩ : syracuseStep 2147809 = 1610857) B1610857
theorem B1910243 : Blo 1271954 1910243 := bstep (se 1 (by rfl) ⟨1432682, by rfl⟩ : syracuseStep 1910243 = 2865365) B2865365
theorem B9176561 : Blo 1271954 9176561 := bstep (se 2 (by rfl) ⟨3441210, by rfl⟩ : syracuseStep 9176561 = 6882421) B6882421
theorem B1910273 : Blo 1271954 1910273 := bstep (se 2 (by rfl) ⟨716352, by rfl⟩ : syracuseStep 1910273 = 1432705) B1432705
theorem B2147843 : Blo 1271954 2147843 := bstep (se 1 (by rfl) ⟨1610882, by rfl⟩ : syracuseStep 2147843 = 3221765) B3221765
theorem B1910291 : Blo 1271954 1910291 := bstep (se 1 (by rfl) ⟨1432718, by rfl⟩ : syracuseStep 1910291 = 2865437) B2865437
theorem B1910321 : Blo 1271954 1910321 := bstep (se 2 (by rfl) ⟨716370, by rfl⟩ : syracuseStep 1910321 = 1432741) B1432741
theorem B1910339 : Blo 1271954 1910339 := bstep (se 1 (by rfl) ⟨1432754, by rfl⟩ : syracuseStep 1910339 = 2865509) B2865509
theorem B1910369 : Blo 1271954 1910369 := bstep (se 2 (by rfl) ⟨716388, by rfl⟩ : syracuseStep 1910369 = 1432777) B1432777
theorem B2418275 : Blo 1271954 2418275 := bstep (se 1 (by rfl) ⟨1813706, by rfl⟩ : syracuseStep 2418275 = 3627413) B3627413
theorem B1910387 : Blo 1271954 1910387 := bstep (se 1 (by rfl) ⟨1432790, by rfl⟩ : syracuseStep 1910387 = 2865581) B2865581
theorem B2147971 : Blo 1271954 2147971 := bstep (se 1 (by rfl) ⟨1610978, by rfl⟩ : syracuseStep 2147971 = 3221957) B3221957
theorem B7956109 : Blo 1271954 7956109 := bstep (se 3 (by rfl) ⟨1491770, by rfl⟩ : syracuseStep 7956109 = 2983541) B2983541
theorem B1910417 : Blo 1271954 1910417 := bstep (se 2 (by rfl) ⟨716406, by rfl⟩ : syracuseStep 1910417 = 1432813) B1432813
theorem B1910435 : Blo 1271954 1910435 := bstep (se 1 (by rfl) ⟨1432826, by rfl⟩ : syracuseStep 1910435 = 2865653) B2865653
theorem B1910465 : Blo 1271954 1910465 := bstep (se 2 (by rfl) ⟨716424, by rfl⟩ : syracuseStep 1910465 = 1432849) B1432849
theorem B4294349 : Blo 1271954 4294349 := bstep (se 3 (by rfl) ⟨805190, by rfl⟩ : syracuseStep 4294349 = 1610381) B1610381
theorem B7071437 : Blo 1271954 7071437 := bstep (se 3 (by rfl) ⟨1325894, by rfl⟩ : syracuseStep 7071437 = 2651789) B2651789
theorem B1910483 : Blo 1271954 1910483 := bstep (se 1 (by rfl) ⟨1432862, by rfl⟩ : syracuseStep 1910483 = 2865725) B2865725
theorem B1910513 : Blo 1271954 1910513 := bstep (se 2 (by rfl) ⟨716442, by rfl⟩ : syracuseStep 1910513 = 1432885) B1432885
theorem B4294403 : Blo 1271954 4294403 := bstep (se 1 (by rfl) ⟨3220802, by rfl⟩ : syracuseStep 4294403 = 6441605) B6441605
theorem B1910531 : Blo 1271954 1910531 := bstep (se 1 (by rfl) ⟨1432898, by rfl⟩ : syracuseStep 1910531 = 2865797) B2865797
theorem B2148113 : Blo 1271954 2148113 := bstep (se 2 (by rfl) ⟨805542, by rfl⟩ : syracuseStep 2148113 = 1611085) B1611085
theorem B1910561 : Blo 1271954 1910561 := bstep (se 2 (by rfl) ⟨716460, by rfl⟩ : syracuseStep 1910561 = 1432921) B1432921
theorem B1910579 : Blo 1271954 1910579 := bstep (se 1 (by rfl) ⟨1432934, by rfl⟩ : syracuseStep 1910579 = 2865869) B2865869
theorem B1812289 : Blo 1271954 1812289 := bstep (se 2 (by rfl) ⟨679608, by rfl⟩ : syracuseStep 1812289 = 1359217) B1359217
theorem B4589389 : Blo 1271954 4589389 := bstep (se 3 (by rfl) ⟨860510, by rfl⟩ : syracuseStep 4589389 = 1721021) B1721021
theorem B3221329 : Blo 1271954 3221329 := bstep (se 2 (by rfl) ⟨1207998, by rfl⟩ : syracuseStep 3221329 = 2415997) B2415997
theorem B1910609 : Blo 1271954 1910609 := bstep (se 2 (by rfl) ⟨716478, by rfl⟩ : syracuseStep 1910609 = 1432957) B1432957
theorem B1910627 : Blo 1271954 1910627 := bstep (se 1 (by rfl) ⟨1432970, by rfl⟩ : syracuseStep 1910627 = 2865941) B2865941
theorem B5441393 : Blo 1271954 5441393 := bstep (se 2 (by rfl) ⟨2040522, by rfl⟩ : syracuseStep 5441393 = 4081045) B4081045
theorem B1910657 : Blo 1271954 1910657 := bstep (se 2 (by rfl) ⟨716496, by rfl⟩ : syracuseStep 1910657 = 1432993) B1432993
theorem B2148241 : Blo 1271954 2148241 := bstep (se 2 (by rfl) ⟨805590, by rfl⟩ : syracuseStep 2148241 = 1611181) B1611181
theorem B2295697 : Blo 1271954 2295697 := bstep (se 2 (by rfl) ⟨860886, by rfl⟩ : syracuseStep 2295697 = 1721773) B1721773
theorem B1910675 : Blo 1271954 1910675 := bstep (se 1 (by rfl) ⟨1433006, by rfl⟩ : syracuseStep 1910675 = 2866013) B2866013
theorem B1812385 : Blo 1271954 1812385 := bstep (se 2 (by rfl) ⟨679644, by rfl⟩ : syracuseStep 1812385 = 1359289) B1359289
theorem B1910705 : Blo 1271954 1910705 := bstep (se 2 (by rfl) ⟨716514, by rfl⟩ : syracuseStep 1910705 = 1433029) B1433029
theorem B2148275 : Blo 1271954 2148275 := bstep (se 1 (by rfl) ⟨1611206, by rfl⟩ : syracuseStep 2148275 = 3222413) B3222413
theorem B1910723 : Blo 1271954 1910723 := bstep (se 1 (by rfl) ⟨1433042, by rfl⟩ : syracuseStep 1910723 = 2866085) B2866085
theorem B5810125 : Blo 1271954 5810125 := bstep (se 3 (by rfl) ⟨1089398, by rfl⟩ : syracuseStep 5810125 = 2178797) B2178797
theorem B1910753 : Blo 1271954 1910753 := bstep (se 2 (by rfl) ⟨716532, by rfl⟩ : syracuseStep 1910753 = 1433065) B1433065
theorem B18589667 : Blo 1271954 18589667 := bstep (se 1 (by rfl) ⟨13942250, by rfl⟩ : syracuseStep 18589667 = 27884501) B27884501
theorem B1910771 : Blo 1271954 1910771 := bstep (se 1 (by rfl) ⟨1433078, by rfl⟩ : syracuseStep 1910771 = 2866157) B2866157
theorem B4294673 : Blo 1271954 4294673 := bstep (se 2 (by rfl) ⟨1610502, by rfl⟩ : syracuseStep 4294673 = 3221005) B3221005
theorem B1910801 : Blo 1271954 1910801 := bstep (se 2 (by rfl) ⟨716550, by rfl⟩ : syracuseStep 1910801 = 1433101) B1433101
theorem B1910819 : Blo 1271954 1910819 := bstep (se 1 (by rfl) ⟨1433114, by rfl⟩ : syracuseStep 1910819 = 2866229) B2866229
theorem B2148403 : Blo 1271954 2148403 := bstep (se 1 (by rfl) ⟨1611302, by rfl⟩ : syracuseStep 2148403 = 3222605) B3222605
theorem B1910849 : Blo 1271954 1910849 := bstep (se 2 (by rfl) ⟨716568, by rfl⟩ : syracuseStep 1910849 = 1433137) B1433137
theorem B1910867 : Blo 1271954 1910867 := bstep (se 1 (by rfl) ⟨1433150, by rfl⟩ : syracuseStep 1910867 = 2866301) B2866301
theorem B3221603 : Blo 1271954 3221603 := bstep (se 1 (by rfl) ⟨2416202, by rfl⟩ : syracuseStep 3221603 = 4832405) B4832405
theorem B1910897 : Blo 1271954 1910897 := bstep (se 2 (by rfl) ⟨716586, by rfl⟩ : syracuseStep 1910897 = 1433173) B1433173
theorem B1910915 : Blo 1271954 1910915 := bstep (se 1 (by rfl) ⟨1433186, by rfl⟩ : syracuseStep 1910915 = 2866373) B2866373
theorem B1271955 : Blo 1271954 1271955 := bstep (se 1 (by rfl) ⟨953966, by rfl⟩ : syracuseStep 1271955 = 1907933) B1907933
theorem B1271971 : Blo 1271954 1271971 := bstep (se 1 (by rfl) ⟨953978, by rfl⟩ : syracuseStep 1271971 = 1907957) B1907957
theorem B1271987 : Blo 1271954 1271987 := bstep (se 1 (by rfl) ⟨953990, by rfl⟩ : syracuseStep 1271987 = 1907981) B1907981
theorem B17410229 : Blo 1271954 17410229 := bstep (se 5 (by rfl) ⟨816104, by rfl⟩ : syracuseStep 17410229 = 1632209) B1632209
theorem B2148545 : Blo 1271954 2148545 := bstep (se 2 (by rfl) ⟨805704, by rfl⟩ : syracuseStep 2148545 = 1611409) B1611409
theorem B1272003 : Blo 1271954 1272003 := bstep (se 1 (by rfl) ⟨954002, by rfl⟩ : syracuseStep 1272003 = 1908005) B1908005
theorem B1272019 : Blo 1271954 1272019 := bstep (se 1 (by rfl) ⟨954014, by rfl⟩ : syracuseStep 1272019 = 1908029) B1908029
theorem B1272035 : Blo 1271954 1272035 := bstep (se 1 (by rfl) ⟨954026, by rfl⟩ : syracuseStep 1272035 = 1908053) B1908053
theorem B1272051 : Blo 1271954 1272051 := bstep (se 1 (by rfl) ⟨954038, by rfl⟩ : syracuseStep 1272051 = 1908077) B1908077
theorem B1272067 : Blo 1271954 1272067 := bstep (se 1 (by rfl) ⟨954050, by rfl⟩ : syracuseStep 1272067 = 1908101) B1908101
theorem B1272083 : Blo 1271954 1272083 := bstep (se 1 (by rfl) ⟨954062, by rfl⟩ : syracuseStep 1272083 = 1908125) B1908125
theorem B1272099 : Blo 1271954 1272099 := bstep (se 1 (by rfl) ⟨954074, by rfl⟩ : syracuseStep 1272099 = 1908149) B1908149
theorem B3221795 : Blo 1271954 3221795 := bstep (se 1 (by rfl) ⟨2416346, by rfl⟩ : syracuseStep 3221795 = 4832693) B4832693
theorem B6121763 : Blo 1271954 6121763 := bstep (se 1 (by rfl) ⟨4591322, by rfl⟩ : syracuseStep 6121763 = 9182645) B9182645
theorem B1272115 : Blo 1271954 1272115 := bstep (se 1 (by rfl) ⟨954086, by rfl⟩ : syracuseStep 1272115 = 1908173) B1908173
theorem B2148673 : Blo 1271954 2148673 := bstep (se 2 (by rfl) ⟨805752, by rfl⟩ : syracuseStep 2148673 = 1611505) B1611505
theorem B1272131 : Blo 1271954 1272131 := bstep (se 1 (by rfl) ⟨954098, by rfl⟩ : syracuseStep 1272131 = 1908197) B1908197
theorem B1378627 : Blo 1271954 1378627 := bstep (se 1 (by rfl) ⟨1033970, by rfl⟩ : syracuseStep 1378627 = 2067941) B2067941
theorem B1272147 : Blo 1271954 1272147 := bstep (se 1 (by rfl) ⟨954110, by rfl⟩ : syracuseStep 1272147 = 1908221) B1908221
theorem B1272163 : Blo 1271954 1272163 := bstep (se 1 (by rfl) ⟨954122, by rfl⟩ : syracuseStep 1272163 = 1908245) B1908245
theorem B3623267 : Blo 1271954 3623267 := bstep (se 1 (by rfl) ⟨2717450, by rfl⟩ : syracuseStep 3623267 = 5434901) B5434901
theorem B2148707 : Blo 1271954 2148707 := bstep (se 1 (by rfl) ⟨1611530, by rfl⟩ : syracuseStep 2148707 = 3223061) B3223061
theorem B1272179 : Blo 1271954 1272179 := bstep (se 1 (by rfl) ⟨954134, by rfl⟩ : syracuseStep 1272179 = 1908269) B1908269
theorem B1272195 : Blo 1271954 1272195 := bstep (se 1 (by rfl) ⟨954146, by rfl⟩ : syracuseStep 1272195 = 1908293) B1908293
theorem B1812881 : Blo 1271954 1812881 := bstep (se 2 (by rfl) ⟨679830, by rfl⟩ : syracuseStep 1812881 = 1359661) B1359661
theorem B1272211 : Blo 1271954 1272211 := bstep (se 1 (by rfl) ⟨954158, by rfl⟩ : syracuseStep 1272211 = 1908317) B1908317
theorem B1272227 : Blo 1271954 1272227 := bstep (se 1 (by rfl) ⟨954170, by rfl⟩ : syracuseStep 1272227 = 1908341) B1908341
theorem B1960369 : Blo 1271954 1960369 := bstep (se 2 (by rfl) ⟨735138, by rfl⟩ : syracuseStep 1960369 = 1470277) B1470277
theorem B1272243 : Blo 1271954 1272243 := bstep (se 1 (by rfl) ⟨954182, by rfl⟩ : syracuseStep 1272243 = 1908365) B1908365
theorem B1452467 : Blo 1271954 1452467 := bstep (se 1 (by rfl) ⟨1089350, by rfl⟩ : syracuseStep 1452467 = 2178701) B2178701
theorem B1272259 : Blo 1271954 1272259 := bstep (se 1 (by rfl) ⟨954194, by rfl⟩ : syracuseStep 1272259 = 1908389) B1908389
theorem B1272275 : Blo 1271954 1272275 := bstep (se 1 (by rfl) ⟨954206, by rfl⟩ : syracuseStep 1272275 = 1908413) B1908413
theorem B1272291 : Blo 1271954 1272291 := bstep (se 1 (by rfl) ⟨954218, by rfl⟩ : syracuseStep 1272291 = 1908437) B1908437
theorem B6441443 : Blo 1271954 6441443 := bstep (se 1 (by rfl) ⟨4831082, by rfl⟩ : syracuseStep 6441443 = 9662165) B9662165
theorem B2148835 : Blo 1271954 2148835 := bstep (se 1 (by rfl) ⟨1611626, by rfl⟩ : syracuseStep 2148835 = 3223253) B3223253
theorem B1272307 : Blo 1271954 1272307 := bstep (se 1 (by rfl) ⟨954230, by rfl⟩ : syracuseStep 1272307 = 1908461) B1908461
theorem B1272323 : Blo 1271954 1272323 := bstep (se 1 (by rfl) ⟨954242, by rfl⟩ : syracuseStep 1272323 = 1908485) B1908485
theorem B1272339 : Blo 1271954 1272339 := bstep (se 1 (by rfl) ⟨954254, by rfl⟩ : syracuseStep 1272339 = 1908509) B1908509
theorem B1272355 : Blo 1271954 1272355 := bstep (se 1 (by rfl) ⟨954266, by rfl⟩ : syracuseStep 1272355 = 1908533) B1908533
theorem B4295213 : Blo 1271954 4295213 := bstep (se 3 (by rfl) ⟨805352, by rfl⟩ : syracuseStep 4295213 = 1610705) B1610705
theorem B1272371 : Blo 1271954 1272371 := bstep (se 1 (by rfl) ⟨954278, by rfl⟩ : syracuseStep 1272371 = 1908557) B1908557
theorem B1272387 : Blo 1271954 1272387 := bstep (se 1 (by rfl) ⟨954290, by rfl⟩ : syracuseStep 1272387 = 1908581) B1908581
theorem B1272403 : Blo 1271954 1272403 := bstep (se 1 (by rfl) ⟨954302, by rfl⟩ : syracuseStep 1272403 = 1908605) B1908605
theorem B1272419 : Blo 1271954 1272419 := bstep (se 1 (by rfl) ⟨954314, by rfl⟩ : syracuseStep 1272419 = 1908629) B1908629
theorem B4295267 : Blo 1271954 4295267 := bstep (se 1 (by rfl) ⟨3221450, by rfl⟩ : syracuseStep 4295267 = 6442901) B6442901
theorem B2148977 : Blo 1271954 2148977 := bstep (se 2 (by rfl) ⟨805866, by rfl⟩ : syracuseStep 2148977 = 1611733) B1611733
theorem B1272435 : Blo 1271954 1272435 := bstep (se 1 (by rfl) ⟨954326, by rfl⟩ : syracuseStep 1272435 = 1908653) B1908653
theorem B1272451 : Blo 1271954 1272451 := bstep (se 1 (by rfl) ⟨954338, by rfl⟩ : syracuseStep 1272451 = 1908677) B1908677
theorem B1272467 : Blo 1271954 1272467 := bstep (se 1 (by rfl) ⟨954350, by rfl⟩ : syracuseStep 1272467 = 1908701) B1908701
theorem B1272483 : Blo 1271954 1272483 := bstep (se 1 (by rfl) ⟨954362, by rfl⟩ : syracuseStep 1272483 = 1908725) B1908725
theorem B7735985 : Blo 1271954 7735985 := bstep (se 2 (by rfl) ⟨2900994, by rfl⟩ : syracuseStep 7735985 = 5801989) B5801989
theorem B1272499 : Blo 1271954 1272499 := bstep (se 1 (by rfl) ⟨954374, by rfl⟩ : syracuseStep 1272499 = 1908749) B1908749
theorem B1272515 : Blo 1271954 1272515 := bstep (se 1 (by rfl) ⟨954386, by rfl⟩ : syracuseStep 1272515 = 1908773) B1908773
theorem B7252685 : Blo 1271954 7252685 := bstep (se 3 (by rfl) ⟨1359878, by rfl⟩ : syracuseStep 7252685 = 2719757) B2719757
theorem B1272531 : Blo 1271954 1272531 := bstep (se 1 (by rfl) ⟨954398, by rfl⟩ : syracuseStep 1272531 = 1908797) B1908797
theorem B1272547 : Blo 1271954 1272547 := bstep (se 1 (by rfl) ⟨954410, by rfl⟩ : syracuseStep 1272547 = 1908821) B1908821
theorem B2149105 : Blo 1271954 2149105 := bstep (se 2 (by rfl) ⟨805914, by rfl⟩ : syracuseStep 2149105 = 1611829) B1611829
theorem B1272563 : Blo 1271954 1272563 := bstep (se 1 (by rfl) ⟨954422, by rfl⟩ : syracuseStep 1272563 = 1908845) B1908845
theorem B1272579 : Blo 1271954 1272579 := bstep (se 1 (by rfl) ⟨954434, by rfl⟩ : syracuseStep 1272579 = 1908869) B1908869
theorem B1272595 : Blo 1271954 1272595 := bstep (se 1 (by rfl) ⟨954446, by rfl⟩ : syracuseStep 1272595 = 1908893) B1908893
theorem B2149139 : Blo 1271954 2149139 := bstep (se 1 (by rfl) ⟨1611854, by rfl⟩ : syracuseStep 2149139 = 3223709) B3223709
theorem B1272611 : Blo 1271954 1272611 := bstep (se 1 (by rfl) ⟨954458, by rfl⟩ : syracuseStep 1272611 = 1908917) B1908917
theorem B1272627 : Blo 1271954 1272627 := bstep (se 1 (by rfl) ⟨954470, by rfl⟩ : syracuseStep 1272627 = 1908941) B1908941
theorem B1272643 : Blo 1271954 1272643 := bstep (se 1 (by rfl) ⟨954482, by rfl⟩ : syracuseStep 1272643 = 1908965) B1908965
theorem B14502725 : Blo 1271954 14502725 := bstep (se 4 (by rfl) ⟨1359630, by rfl⟩ : syracuseStep 14502725 = 2719261) B2719261
theorem B1272659 : Blo 1271954 1272659 := bstep (se 1 (by rfl) ⟨954494, by rfl⟩ : syracuseStep 1272659 = 1908989) B1908989
theorem B1272675 : Blo 1271954 1272675 := bstep (se 1 (by rfl) ⟨954506, by rfl⟩ : syracuseStep 1272675 = 1909013) B1909013
theorem B4295537 : Blo 1271954 4295537 := bstep (se 2 (by rfl) ⟨1610826, by rfl⟩ : syracuseStep 4295537 = 3221653) B3221653
theorem B1272691 : Blo 1271954 1272691 := bstep (se 1 (by rfl) ⟨954518, by rfl⟩ : syracuseStep 1272691 = 1909037) B1909037
theorem B1272707 : Blo 1271954 1272707 := bstep (se 1 (by rfl) ⟨954530, by rfl⟩ : syracuseStep 1272707 = 1909061) B1909061
theorem B1272723 : Blo 1271954 1272723 := bstep (se 1 (by rfl) ⟨954542, by rfl⟩ : syracuseStep 1272723 = 1909085) B1909085
theorem B2149267 : Blo 1271954 2149267 := bstep (se 1 (by rfl) ⟨1611950, by rfl⟩ : syracuseStep 2149267 = 3223901) B3223901
theorem B1272739 : Blo 1271954 1272739 := bstep (se 1 (by rfl) ⟨954554, by rfl⟩ : syracuseStep 1272739 = 1909109) B1909109
theorem B1272755 : Blo 1271954 1272755 := bstep (se 1 (by rfl) ⟨954566, by rfl⟩ : syracuseStep 1272755 = 1909133) B1909133
theorem B1272771 : Blo 1271954 1272771 := bstep (se 1 (by rfl) ⟨954578, by rfl⟩ : syracuseStep 1272771 = 1909157) B1909157
theorem B1272787 : Blo 1271954 1272787 := bstep (se 1 (by rfl) ⟨954590, by rfl⟩ : syracuseStep 1272787 = 1909181) B1909181
theorem B1272803 : Blo 1271954 1272803 := bstep (se 1 (by rfl) ⟨954602, by rfl⟩ : syracuseStep 1272803 = 1909205) B1909205
theorem B1272819 : Blo 1271954 1272819 := bstep (se 1 (by rfl) ⟨954614, by rfl⟩ : syracuseStep 1272819 = 1909229) B1909229
theorem B1272835 : Blo 1271954 1272835 := bstep (se 1 (by rfl) ⟨954626, by rfl⟩ : syracuseStep 1272835 = 1909253) B1909253
theorem B1272851 : Blo 1271954 1272851 := bstep (se 1 (by rfl) ⟨954638, by rfl⟩ : syracuseStep 1272851 = 1909277) B1909277
theorem B2149409 : Blo 1271954 2149409 := bstep (se 2 (by rfl) ⟨806028, by rfl⟩ : syracuseStep 2149409 = 1612057) B1612057
theorem B1272867 : Blo 1271954 1272867 := bstep (se 1 (by rfl) ⟨954650, by rfl⟩ : syracuseStep 1272867 = 1909301) B1909301
theorem B1272883 : Blo 1271954 1272883 := bstep (se 1 (by rfl) ⟨954662, by rfl⟩ : syracuseStep 1272883 = 1909325) B1909325
theorem B1272899 : Blo 1271954 1272899 := bstep (se 1 (by rfl) ⟨954674, by rfl⟩ : syracuseStep 1272899 = 1909349) B1909349
theorem B2862161 : Blo 1271954 2862161 := bstep (se 2 (by rfl) ⟨1073310, by rfl⟩ : syracuseStep 2862161 = 2146621) B2146621
theorem B1272915 : Blo 1271954 1272915 := bstep (se 1 (by rfl) ⟨954686, by rfl⟩ : syracuseStep 1272915 = 1909373) B1909373
theorem B7736419 : Blo 1271954 7736419 := bstep (se 1 (by rfl) ⟨5802314, by rfl⟩ : syracuseStep 7736419 = 11604629) B11604629
theorem B2862179 : Blo 1271954 2862179 := bstep (se 1 (by rfl) ⟨2146634, by rfl⟩ : syracuseStep 2862179 = 4293269) B4293269
theorem B1272931 : Blo 1271954 1272931 := bstep (se 1 (by rfl) ⟨954698, by rfl⟩ : syracuseStep 1272931 = 1909397) B1909397
theorem B1272947 : Blo 1271954 1272947 := bstep (se 1 (by rfl) ⟨954710, by rfl⟩ : syracuseStep 1272947 = 1909421) B1909421
theorem B1272963 : Blo 1271954 1272963 := bstep (se 1 (by rfl) ⟨954722, by rfl⟩ : syracuseStep 1272963 = 1909445) B1909445
theorem B1272979 : Blo 1271954 1272979 := bstep (se 1 (by rfl) ⟨954734, by rfl⟩ : syracuseStep 1272979 = 1909469) B1909469
theorem B2149537 : Blo 1271954 2149537 := bstep (se 2 (by rfl) ⟨806076, by rfl⟩ : syracuseStep 2149537 = 1612153) B1612153
theorem B7244963 : Blo 1271954 7244963 := bstep (se 1 (by rfl) ⟨5433722, by rfl⟩ : syracuseStep 7244963 = 10867445) B10867445
theorem B3533987 : Blo 1271954 3533987 := bstep (se 1 (by rfl) ⟨2650490, by rfl⟩ : syracuseStep 3533987 = 5300981) B5300981
theorem B1272995 : Blo 1271954 1272995 := bstep (se 1 (by rfl) ⟨954746, by rfl⟩ : syracuseStep 1272995 = 1909493) B1909493
theorem B1273011 : Blo 1271954 1273011 := bstep (se 1 (by rfl) ⟨954758, by rfl⟩ : syracuseStep 1273011 = 1909517) B1909517
theorem B1273027 : Blo 1271954 1273027 := bstep (se 1 (by rfl) ⟨954770, by rfl⟩ : syracuseStep 1273027 = 1909541) B1909541
theorem B2149571 : Blo 1271954 2149571 := bstep (se 1 (by rfl) ⟨1612178, by rfl⟩ : syracuseStep 2149571 = 3224357) B3224357
theorem B3222737 : Blo 1271954 3222737 := bstep (se 2 (by rfl) ⟨1208526, by rfl⟩ : syracuseStep 3222737 = 2417053) B2417053
theorem B1273043 : Blo 1271954 1273043 := bstep (se 1 (by rfl) ⟨954782, by rfl⟩ : syracuseStep 1273043 = 1909565) B1909565
theorem B1273059 : Blo 1271954 1273059 := bstep (se 1 (by rfl) ⟨954794, by rfl⟩ : syracuseStep 1273059 = 1909589) B1909589
theorem B1273075 : Blo 1271954 1273075 := bstep (se 1 (by rfl) ⟨954806, by rfl⟩ : syracuseStep 1273075 = 1909613) B1909613
theorem B1813747 : Blo 1271954 1813747 := bstep (se 1 (by rfl) ⟨1360310, by rfl⟩ : syracuseStep 1813747 = 2720621) B2720621
theorem B1273091 : Blo 1271954 1273091 := bstep (se 1 (by rfl) ⟨954818, by rfl⟩ : syracuseStep 1273091 = 1909637) B1909637
theorem B3222787 : Blo 1271954 3222787 := bstep (se 1 (by rfl) ⟨2417090, by rfl⟩ : syracuseStep 3222787 = 4834181) B4834181
theorem B6442253 : Blo 1271954 6442253 := bstep (se 3 (by rfl) ⟨1207922, by rfl⟩ : syracuseStep 6442253 = 2415845) B2415845
theorem B1273107 : Blo 1271954 1273107 := bstep (se 1 (by rfl) ⟨954830, by rfl⟩ : syracuseStep 1273107 = 1909661) B1909661
theorem B1273123 : Blo 1271954 1273123 := bstep (se 1 (by rfl) ⟨954842, by rfl⟩ : syracuseStep 1273123 = 1909685) B1909685
theorem B1273139 : Blo 1271954 1273139 := bstep (se 1 (by rfl) ⟨954854, by rfl⟩ : syracuseStep 1273139 = 1909709) B1909709
theorem B1273155 : Blo 1271954 1273155 := bstep (se 1 (by rfl) ⟨954866, by rfl⟩ : syracuseStep 1273155 = 1909733) B1909733
theorem B2149699 : Blo 1271954 2149699 := bstep (se 1 (by rfl) ⟨1612274, by rfl⟩ : syracuseStep 2149699 = 3224549) B3224549
theorem B1273171 : Blo 1271954 1273171 := bstep (se 1 (by rfl) ⟨954878, by rfl⟩ : syracuseStep 1273171 = 1909757) B1909757
theorem B1813843 : Blo 1271954 1813843 := bstep (se 1 (by rfl) ⟨1360382, by rfl⟩ : syracuseStep 1813843 = 2720765) B2720765
theorem B1273187 : Blo 1271954 1273187 := bstep (se 1 (by rfl) ⟨954890, by rfl⟩ : syracuseStep 1273187 = 1909781) B1909781
theorem B2862449 : Blo 1271954 2862449 := bstep (se 2 (by rfl) ⟨1073418, by rfl⟩ : syracuseStep 2862449 = 2146837) B2146837
theorem B1273203 : Blo 1271954 1273203 := bstep (se 1 (by rfl) ⟨954902, by rfl⟩ : syracuseStep 1273203 = 1909805) B1909805
theorem B2862467 : Blo 1271954 2862467 := bstep (se 1 (by rfl) ⟨2146850, by rfl⟩ : syracuseStep 2862467 = 4293701) B4293701
theorem B1273219 : Blo 1271954 1273219 := bstep (se 1 (by rfl) ⟨954914, by rfl⟩ : syracuseStep 1273219 = 1909829) B1909829
theorem B4296077 : Blo 1271954 4296077 := bstep (se 3 (by rfl) ⟨805514, by rfl⟩ : syracuseStep 4296077 = 1611029) B1611029
theorem B3222929 : Blo 1271954 3222929 := bstep (se 2 (by rfl) ⟨1208598, by rfl⟩ : syracuseStep 3222929 = 2417197) B2417197
theorem B1273235 : Blo 1271954 1273235 := bstep (se 1 (by rfl) ⟨954926, by rfl⟩ : syracuseStep 1273235 = 1909853) B1909853
theorem B1273251 : Blo 1271954 1273251 := bstep (se 1 (by rfl) ⟨954938, by rfl⟩ : syracuseStep 1273251 = 1909877) B1909877
theorem B3722669 : Blo 1271954 3722669 := bstep (se 3 (by rfl) ⟨698000, by rfl⟩ : syracuseStep 3722669 = 1396001) B1396001
theorem B1273267 : Blo 1271954 1273267 := bstep (se 1 (by rfl) ⟨954950, by rfl⟩ : syracuseStep 1273267 = 1909901) B1909901
theorem B4296131 : Blo 1271954 4296131 := bstep (se 1 (by rfl) ⟨3222098, by rfl⟩ : syracuseStep 4296131 = 6444197) B6444197
theorem B1273283 : Blo 1271954 1273283 := bstep (se 1 (by rfl) ⟨954962, by rfl⟩ : syracuseStep 1273283 = 1909925) B1909925
theorem B1273299 : Blo 1271954 1273299 := bstep (se 1 (by rfl) ⟨954974, by rfl⟩ : syracuseStep 1273299 = 1909949) B1909949
theorem B1273315 : Blo 1271954 1273315 := bstep (se 1 (by rfl) ⟨954986, by rfl⟩ : syracuseStep 1273315 = 1909973) B1909973
theorem B1273331 : Blo 1271954 1273331 := bstep (se 1 (by rfl) ⟨954998, by rfl⟩ : syracuseStep 1273331 = 1909997) B1909997
theorem B1273347 : Blo 1271954 1273347 := bstep (se 1 (by rfl) ⟨955010, by rfl⟩ : syracuseStep 1273347 = 1910021) B1910021
theorem B1273363 : Blo 1271954 1273363 := bstep (se 1 (by rfl) ⟨955022, by rfl⟩ : syracuseStep 1273363 = 1910045) B1910045
theorem B5508643 : Blo 1271954 5508643 := bstep (se 1 (by rfl) ⟨4131482, by rfl⟩ : syracuseStep 5508643 = 8262965) B8262965
theorem B1273379 : Blo 1271954 1273379 := bstep (se 1 (by rfl) ⟨955034, by rfl⟩ : syracuseStep 1273379 = 1910069) B1910069
theorem B3624497 : Blo 1271954 3624497 := bstep (se 2 (by rfl) ⟨1359186, by rfl⟩ : syracuseStep 3624497 = 2718373) B2718373
theorem B1273395 : Blo 1271954 1273395 := bstep (se 1 (by rfl) ⟨955046, by rfl⟩ : syracuseStep 1273395 = 1910093) B1910093
theorem B1273411 : Blo 1271954 1273411 := bstep (se 1 (by rfl) ⟨955058, by rfl⟩ : syracuseStep 1273411 = 1910117) B1910117
theorem B1273427 : Blo 1271954 1273427 := bstep (se 1 (by rfl) ⟨955070, by rfl⟩ : syracuseStep 1273427 = 1910141) B1910141
theorem B1273443 : Blo 1271954 1273443 := bstep (se 1 (by rfl) ⟨955082, by rfl⟩ : syracuseStep 1273443 = 1910165) B1910165
theorem B1273459 : Blo 1271954 1273459 := bstep (se 1 (by rfl) ⟨955094, by rfl⟩ : syracuseStep 1273459 = 1910189) B1910189
theorem B1273475 : Blo 1271954 1273475 := bstep (se 1 (by rfl) ⟨955106, by rfl⟩ : syracuseStep 1273475 = 1910213) B1910213
theorem B5164685 : Blo 1271954 5164685 := bstep (se 3 (by rfl) ⟨968378, by rfl⟩ : syracuseStep 5164685 = 1936757) B1936757
theorem B2862737 : Blo 1271954 2862737 := bstep (se 2 (by rfl) ⟨1073526, by rfl⟩ : syracuseStep 2862737 = 2147053) B2147053
theorem B1273491 : Blo 1271954 1273491 := bstep (se 1 (by rfl) ⟨955118, by rfl⟩ : syracuseStep 1273491 = 1910237) B1910237
theorem B2862755 : Blo 1271954 2862755 := bstep (se 1 (by rfl) ⟨2147066, by rfl⟩ : syracuseStep 2862755 = 4294133) B4294133
theorem B3059363 : Blo 1271954 3059363 := bstep (se 1 (by rfl) ⟨2294522, by rfl⟩ : syracuseStep 3059363 = 4589045) B4589045
theorem B1273507 : Blo 1271954 1273507 := bstep (se 1 (by rfl) ⟨955130, by rfl⟩ : syracuseStep 1273507 = 1910261) B1910261
theorem B8261297 : Blo 1271954 8261297 := bstep (se 2 (by rfl) ⟨3097986, by rfl⟩ : syracuseStep 8261297 = 6195973) B6195973
theorem B1273523 : Blo 1271954 1273523 := bstep (se 1 (by rfl) ⟨955142, by rfl⟩ : syracuseStep 1273523 = 1910285) B1910285
theorem B1273539 : Blo 1271954 1273539 := bstep (se 1 (by rfl) ⟨955154, by rfl⟩ : syracuseStep 1273539 = 1910309) B1910309
theorem B4296401 : Blo 1271954 4296401 := bstep (se 2 (by rfl) ⟨1611150, by rfl⟩ : syracuseStep 4296401 = 3222301) B3222301
theorem B1273555 : Blo 1271954 1273555 := bstep (se 1 (by rfl) ⟨955166, by rfl⟩ : syracuseStep 1273555 = 1910333) B1910333
theorem B4353763 : Blo 1271954 4353763 := bstep (se 1 (by rfl) ⟨3265322, by rfl⟩ : syracuseStep 4353763 = 6530645) B6530645
theorem B1273571 : Blo 1271954 1273571 := bstep (se 1 (by rfl) ⟨955178, by rfl⟩ : syracuseStep 1273571 = 1910357) B1910357
theorem B1273587 : Blo 1271954 1273587 := bstep (se 1 (by rfl) ⟨955190, by rfl⟩ : syracuseStep 1273587 = 1910381) B1910381
theorem B1273603 : Blo 1271954 1273603 := bstep (se 1 (by rfl) ⟨955202, by rfl⟩ : syracuseStep 1273603 = 1910405) B1910405
theorem B1273619 : Blo 1271954 1273619 := bstep (se 1 (by rfl) ⟨955214, by rfl⟩ : syracuseStep 1273619 = 1910429) B1910429
theorem B1273635 : Blo 1271954 1273635 := bstep (se 1 (by rfl) ⟨955226, by rfl⟩ : syracuseStep 1273635 = 1910453) B1910453
theorem B1273651 : Blo 1271954 1273651 := bstep (se 1 (by rfl) ⟨955238, by rfl⟩ : syracuseStep 1273651 = 1910477) B1910477
theorem B1273667 : Blo 1271954 1273667 := bstep (se 1 (by rfl) ⟨955250, by rfl⟩ : syracuseStep 1273667 = 1910501) B1910501
theorem B1273683 : Blo 1271954 1273683 := bstep (se 1 (by rfl) ⟨955262, by rfl⟩ : syracuseStep 1273683 = 1910525) B1910525
theorem B1273699 : Blo 1271954 1273699 := bstep (se 1 (by rfl) ⟨955274, by rfl⟩ : syracuseStep 1273699 = 1910549) B1910549
theorem B1273715 : Blo 1271954 1273715 := bstep (se 1 (by rfl) ⟨955286, by rfl⟩ : syracuseStep 1273715 = 1910573) B1910573
theorem B1273731 : Blo 1271954 1273731 := bstep (se 1 (by rfl) ⟨955298, by rfl⟩ : syracuseStep 1273731 = 1910597) B1910597
theorem B1273747 : Blo 1271954 1273747 := bstep (se 1 (by rfl) ⟨955310, by rfl⟩ : syracuseStep 1273747 = 1910621) B1910621
theorem B1273763 : Blo 1271954 1273763 := bstep (se 1 (by rfl) ⟨955322, by rfl⟩ : syracuseStep 1273763 = 1910645) B1910645
theorem B2863025 : Blo 1271954 2863025 := bstep (se 2 (by rfl) ⟨1073634, by rfl⟩ : syracuseStep 2863025 = 2147269) B2147269
theorem B1273779 : Blo 1271954 1273779 := bstep (se 1 (by rfl) ⟨955334, by rfl⟩ : syracuseStep 1273779 = 1910669) B1910669
theorem B2863043 : Blo 1271954 2863043 := bstep (se 1 (by rfl) ⟨2147282, by rfl⟩ : syracuseStep 2863043 = 4294565) B4294565
theorem B1273795 : Blo 1271954 1273795 := bstep (se 1 (by rfl) ⟨955346, by rfl⟩ : syracuseStep 1273795 = 1910693) B1910693
theorem B1273811 : Blo 1271954 1273811 := bstep (se 1 (by rfl) ⟨955358, by rfl⟩ : syracuseStep 1273811 = 1910717) B1910717
theorem B5435363 : Blo 1271954 5435363 := bstep (se 1 (by rfl) ⟨4076522, by rfl⟩ : syracuseStep 5435363 = 8153045) B8153045
theorem B1273827 : Blo 1271954 1273827 := bstep (se 1 (by rfl) ⟨955370, by rfl⟩ : syracuseStep 1273827 = 1910741) B1910741
theorem B1273843 : Blo 1271954 1273843 := bstep (se 1 (by rfl) ⟨955382, by rfl⟩ : syracuseStep 1273843 = 1910765) B1910765
theorem B1273859 : Blo 1271954 1273859 := bstep (se 1 (by rfl) ⟨955394, by rfl⟩ : syracuseStep 1273859 = 1910789) B1910789
theorem B1273875 : Blo 1271954 1273875 := bstep (se 1 (by rfl) ⟨955406, by rfl⟩ : syracuseStep 1273875 = 1910813) B1910813
theorem B3059747 : Blo 1271954 3059747 := bstep (se 1 (by rfl) ⟨2294810, by rfl⟩ : syracuseStep 3059747 = 4589621) B4589621
theorem B1273891 : Blo 1271954 1273891 := bstep (se 1 (by rfl) ⟨955418, by rfl⟩ : syracuseStep 1273891 = 1910837) B1910837
theorem B2904113 : Blo 1271954 2904113 := bstep (se 2 (by rfl) ⟨1089042, by rfl⟩ : syracuseStep 2904113 = 2178085) B2178085
theorem B1273907 : Blo 1271954 1273907 := bstep (se 1 (by rfl) ⟨955430, by rfl⟩ : syracuseStep 1273907 = 1910861) B1910861
theorem B1273923 : Blo 1271954 1273923 := bstep (se 1 (by rfl) ⟨955442, by rfl⟩ : syracuseStep 1273923 = 1910885) B1910885
theorem B1273939 : Blo 1271954 1273939 := bstep (se 1 (by rfl) ⟨955454, by rfl⟩ : syracuseStep 1273939 = 1910909) B1910909
theorem B2863313 : Blo 1271954 2863313 := bstep (se 2 (by rfl) ⟨1073742, by rfl⟩ : syracuseStep 2863313 = 2147485) B2147485
theorem B2863331 : Blo 1271954 2863331 := bstep (se 1 (by rfl) ⟨2147498, by rfl⟩ : syracuseStep 2863331 = 4294997) B4294997
theorem B4296941 : Blo 1271954 4296941 := bstep (se 3 (by rfl) ⟨805676, by rfl⟩ : syracuseStep 4296941 = 1611353) B1611353
theorem B45322517 : Blo 1271954 45322517 := bstep (se 6 (by rfl) ⟨1062246, by rfl⟩ : syracuseStep 45322517 = 2124493) B2124493
theorem B4296995 : Blo 1271954 4296995 := bstep (se 1 (by rfl) ⟨3222746, by rfl⟩ : syracuseStep 4296995 = 6445493) B6445493
theorem B4829489 : Blo 1271954 4829489 := bstep (se 2 (by rfl) ⟨1811058, by rfl⟩ : syracuseStep 4829489 = 3622117) B3622117
theorem B3060035 : Blo 1271954 3060035 := bstep (se 1 (by rfl) ⟨2295026, by rfl⟩ : syracuseStep 3060035 = 4590053) B4590053
theorem B2355569 : Blo 1271954 2355569 := bstep (se 2 (by rfl) ⟨883338, by rfl⟩ : syracuseStep 2355569 = 1766677) B1766677
theorem B4354417 : Blo 1271954 4354417 := bstep (se 2 (by rfl) ⟨1632906, by rfl⟩ : syracuseStep 4354417 = 3265813) B3265813
theorem B8155505 : Blo 1271954 8155505 := bstep (se 2 (by rfl) ⟨3058314, by rfl⟩ : syracuseStep 8155505 = 6116629) B6116629
theorem B3223921 : Blo 1271954 3223921 := bstep (se 2 (by rfl) ⟨1208970, by rfl⟩ : syracuseStep 3223921 = 2417941) B2417941
theorem B15479221 : Blo 1271954 15479221 := bstep (se 5 (by rfl) ⟨725588, by rfl⟩ : syracuseStep 15479221 = 1451177) B1451177
theorem B2863601 : Blo 1271954 2863601 := bstep (se 2 (by rfl) ⟨1073850, by rfl⟩ : syracuseStep 2863601 = 2147701) B2147701
theorem B2863619 : Blo 1271954 2863619 := bstep (se 1 (by rfl) ⟨2147714, by rfl⟩ : syracuseStep 2863619 = 4295429) B4295429
theorem B1610275 : Blo 1271954 1610275 := bstep (se 1 (by rfl) ⟨1207706, by rfl⟩ : syracuseStep 1610275 = 2415413) B2415413
theorem B4297265 : Blo 1271954 4297265 := bstep (se 2 (by rfl) ⟨1611474, by rfl⟩ : syracuseStep 4297265 = 3222949) B3222949
theorem B1610371 : Blo 1271954 1610371 := bstep (se 1 (by rfl) ⟨1207778, by rfl⟩ : syracuseStep 1610371 = 2415557) B2415557
theorem B3224195 : Blo 1271954 3224195 := bstep (se 1 (by rfl) ⟨2418146, by rfl⟩ : syracuseStep 3224195 = 4836293) B4836293
theorem B4133635 : Blo 1271954 4133635 := bstep (se 1 (by rfl) ⟨3100226, by rfl⟩ : syracuseStep 4133635 = 6200453) B6200453
theorem B2863889 : Blo 1271954 2863889 := bstep (se 2 (by rfl) ⟨1073958, by rfl⟩ : syracuseStep 2863889 = 2147917) B2147917
theorem B3060497 : Blo 1271954 3060497 := bstep (se 2 (by rfl) ⟨1147686, by rfl⟩ : syracuseStep 3060497 = 2295373) B2295373
theorem B2863907 : Blo 1271954 2863907 := bstep (se 1 (by rfl) ⟨2147930, by rfl⟩ : syracuseStep 2863907 = 4295861) B4295861
theorem B1528643 : Blo 1271954 1528643 := bstep (se 1 (by rfl) ⟨1146482, by rfl⟩ : syracuseStep 1528643 = 2292965) B2292965
theorem B3224387 : Blo 1271954 3224387 := bstep (se 1 (by rfl) ⟨2418290, by rfl⟩ : syracuseStep 3224387 = 4836581) B4836581
theorem B7254917 : Blo 1271954 7254917 := bstep (se 4 (by rfl) ⟨680148, by rfl⟩ : syracuseStep 7254917 = 1360297) B1360297
theorem B3625955 : Blo 1271954 3625955 := bstep (se 1 (by rfl) ⟨2719466, by rfl⟩ : syracuseStep 3625955 = 5438933) B5438933
theorem B7246853 : Blo 1271954 7246853 := bstep (se 4 (by rfl) ⟨679392, by rfl⟩ : syracuseStep 7246853 = 1358785) B1358785
theorem B4076561 : Blo 1271954 4076561 := bstep (se 2 (by rfl) ⟨1528710, by rfl⟩ : syracuseStep 4076561 = 3057421) B3057421
theorem B2864177 : Blo 1271954 2864177 := bstep (se 2 (by rfl) ⟨1074066, by rfl⟩ : syracuseStep 2864177 = 2148133) B2148133
theorem B2864195 : Blo 1271954 2864195 := bstep (se 1 (by rfl) ⟨2148146, by rfl⟩ : syracuseStep 2864195 = 4296293) B4296293
theorem B4297805 : Blo 1271954 4297805 := bstep (se 3 (by rfl) ⟨805838, by rfl⟩ : syracuseStep 4297805 = 1611677) B1611677
theorem B5231729 : Blo 1271954 5231729 := bstep (se 2 (by rfl) ⟨1961898, by rfl⟩ : syracuseStep 5231729 = 3923797) B3923797
theorem B1610867 : Blo 1271954 1610867 := bstep (se 1 (by rfl) ⟨1208150, by rfl⟩ : syracuseStep 1610867 = 2416301) B2416301
theorem B4297859 : Blo 1271954 4297859 := bstep (se 1 (by rfl) ⟨3223394, by rfl⟩ : syracuseStep 4297859 = 6446789) B6446789
theorem B4076689 : Blo 1271954 4076689 := bstep (se 2 (by rfl) ⟨1528758, by rfl⟩ : syracuseStep 4076689 = 3057517) B3057517
theorem B2864465 : Blo 1271954 2864465 := bstep (se 2 (by rfl) ⟨1074174, by rfl⟩ : syracuseStep 2864465 = 2148349) B2148349
theorem B2864483 : Blo 1271954 2864483 := bstep (se 1 (by rfl) ⟨2148362, by rfl⟩ : syracuseStep 2864483 = 4296725) B4296725
theorem B4076945 : Blo 1271954 4076945 := bstep (se 2 (by rfl) ⟨1528854, by rfl⟩ : syracuseStep 4076945 = 3057709) B3057709
theorem B4298129 : Blo 1271954 4298129 := bstep (se 2 (by rfl) ⟨1611798, by rfl⟩ : syracuseStep 4298129 = 3223597) B3223597
theorem B6886853 : Blo 1271954 6886853 := bstep (se 4 (by rfl) ⟨645642, by rfl⟩ : syracuseStep 6886853 = 1291285) B1291285
theorem B1430995 : Blo 1271954 1430995 := bstep (se 1 (by rfl) ⟨1073246, by rfl⟩ : syracuseStep 1430995 = 2146493) B2146493
theorem B6878789 : Blo 1271954 6878789 := bstep (se 4 (by rfl) ⟨644886, by rfl⟩ : syracuseStep 6878789 = 1289773) B1289773
theorem B1431139 : Blo 1271954 1431139 := bstep (se 1 (by rfl) ⟨1073354, by rfl⟩ : syracuseStep 1431139 = 2146709) B2146709
theorem B2717297 : Blo 1271954 2717297 := bstep (se 2 (by rfl) ⟨1018986, by rfl⟩ : syracuseStep 2717297 = 2037973) B2037973
theorem B18347633 : Blo 1271954 18347633 := bstep (se 2 (by rfl) ⟨6880362, by rfl⟩ : syracuseStep 18347633 = 13760725) B13760725
theorem B2864753 : Blo 1271954 2864753 := bstep (se 2 (by rfl) ⟨1074282, by rfl⟩ : syracuseStep 2864753 = 2148565) B2148565
theorem B2864771 : Blo 1271954 2864771 := bstep (se 1 (by rfl) ⟨2148578, by rfl⟩ : syracuseStep 2864771 = 4297157) B4297157
theorem B4830947 : Blo 1271954 4830947 := bstep (se 1 (by rfl) ⟨3623210, by rfl⟩ : syracuseStep 4830947 = 7246421) B7246421
theorem B4830961 : Blo 1271954 4830961 := bstep (se 2 (by rfl) ⟨1811610, by rfl⟩ : syracuseStep 4830961 = 3623221) B3623221
theorem B1431283 : Blo 1271954 1431283 := bstep (se 1 (by rfl) ⟨1073462, by rfl⟩ : syracuseStep 1431283 = 2146925) B2146925
theorem B3626765 : Blo 1271954 3626765 := bstep (se 3 (by rfl) ⟨680018, by rfl⟩ : syracuseStep 3626765 = 1360037) B1360037
theorem B8156963 : Blo 1271954 8156963 := bstep (se 1 (by rfl) ⟨6117722, by rfl⟩ : syracuseStep 8156963 = 12235445) B12235445
theorem B1611571 : Blo 1271954 1611571 := bstep (se 1 (by rfl) ⟨1208678, by rfl⟩ : syracuseStep 1611571 = 2417357) B2417357
theorem B2176897 : Blo 1271954 2176897 := bstep (se 2 (by rfl) ⟨816336, by rfl⟩ : syracuseStep 2176897 = 1632673) B1632673
theorem B1431427 : Blo 1271954 1431427 := bstep (se 1 (by rfl) ⟨1073570, by rfl⟩ : syracuseStep 1431427 = 2147141) B2147141
theorem B2865041 : Blo 1271954 2865041 := bstep (se 2 (by rfl) ⟨1074390, by rfl⟩ : syracuseStep 2865041 = 2148781) B2148781
theorem B1611667 : Blo 1271954 1611667 := bstep (se 1 (by rfl) ⟨1208750, by rfl⟩ : syracuseStep 1611667 = 2417501) B2417501
theorem B2865059 : Blo 1271954 2865059 := bstep (se 1 (by rfl) ⟨2148794, by rfl⟩ : syracuseStep 2865059 = 4297589) B4297589
theorem B4298669 : Blo 1271954 4298669 := bstep (se 3 (by rfl) ⟨806000, by rfl⟩ : syracuseStep 4298669 = 1612001) B1612001
theorem B5437361 : Blo 1271954 5437361 := bstep (se 2 (by rfl) ⟨2039010, by rfl⟩ : syracuseStep 5437361 = 4078021) B4078021
theorem B3626957 : Blo 1271954 3626957 := bstep (se 3 (by rfl) ⟨680054, by rfl⟩ : syracuseStep 3626957 = 1360109) B1360109
theorem B16316387 : Blo 1271954 16316387 := bstep (se 1 (by rfl) ⟨12237290, by rfl⟩ : syracuseStep 16316387 = 24474581) B24474581
theorem B4298723 : Blo 1271954 4298723 := bstep (se 1 (by rfl) ⟨3224042, by rfl⟩ : syracuseStep 4298723 = 6448085) B6448085
theorem B7747589 : Blo 1271954 7747589 := bstep (se 4 (by rfl) ⟨726336, by rfl⟩ : syracuseStep 7747589 = 1452673) B1452673
theorem B3872785 : Blo 1271954 3872785 := bstep (se 2 (by rfl) ⟨1452294, by rfl⟩ : syracuseStep 3872785 = 2904589) B2904589
theorem B1431571 : Blo 1271954 1431571 := bstep (se 1 (by rfl) ⟨1073678, by rfl⟩ : syracuseStep 1431571 = 2147357) B2147357
theorem B2037857 : Blo 1271954 2037857 := bstep (se 2 (by rfl) ⟨764196, by rfl⟩ : syracuseStep 2037857 = 1528393) B1528393
theorem B1742945 : Blo 1271954 1742945 := bstep (se 2 (by rfl) ⟨653604, by rfl⟩ : syracuseStep 1742945 = 1307209) B1307209
theorem B6445169 : Blo 1271954 6445169 := bstep (se 2 (by rfl) ⟨2416938, by rfl⟩ : syracuseStep 6445169 = 4833877) B4833877
theorem B3872881 : Blo 1271954 3872881 := bstep (se 2 (by rfl) ⟨1452330, by rfl⟩ : syracuseStep 3872881 = 2904661) B2904661
theorem B1431715 : Blo 1271954 1431715 := bstep (se 1 (by rfl) ⟨1073786, by rfl⟩ : syracuseStep 1431715 = 2147573) B2147573
theorem B2865329 : Blo 1271954 2865329 := bstep (se 2 (by rfl) ⟨1074498, by rfl⟩ : syracuseStep 2865329 = 2148997) B2148997
theorem B2865347 : Blo 1271954 2865347 := bstep (se 1 (by rfl) ⟨2149010, by rfl⟩ : syracuseStep 2865347 = 4298021) B4298021
theorem B82639075 : Blo 1271954 82639075 := bstep (se 1 (by rfl) ⟨61979306, by rfl⟩ : syracuseStep 82639075 = 123958613) B123958613
theorem B4298993 : Blo 1271954 4298993 := bstep (se 2 (by rfl) ⟨1612122, by rfl⟩ : syracuseStep 4298993 = 3224245) B3224245
theorem B7346467 : Blo 1271954 7346467 := bstep (se 1 (by rfl) ⟨5509850, by rfl⟩ : syracuseStep 7346467 = 11019701) B11019701
theorem B1431859 : Blo 1271954 1431859 := bstep (se 1 (by rfl) ⟨1073894, by rfl⟩ : syracuseStep 1431859 = 2147789) B2147789
theorem B1612163 : Blo 1271954 1612163 := bstep (se 1 (by rfl) ⟨1209122, by rfl⟩ : syracuseStep 1612163 = 2418245) B2418245
theorem B2415025 : Blo 1271954 2415025 := bstep (se 2 (by rfl) ⟨905634, by rfl⟩ : syracuseStep 2415025 = 1811269) B1811269
theorem B1432003 : Blo 1271954 1432003 := bstep (se 1 (by rfl) ⟨1074002, by rfl⟩ : syracuseStep 1432003 = 2148005) B2148005
theorem B2865617 : Blo 1271954 2865617 := bstep (se 2 (by rfl) ⟨1074606, by rfl⟩ : syracuseStep 2865617 = 2149213) B2149213
theorem B6117859 : Blo 1271954 6117859 := bstep (se 1 (by rfl) ⟨4588394, by rfl⟩ : syracuseStep 6117859 = 9176789) B9176789
theorem B2865635 : Blo 1271954 2865635 := bstep (se 1 (by rfl) ⟨2149226, by rfl⟩ : syracuseStep 2865635 = 4298453) B4298453
theorem B2292259 : Blo 1271954 2292259 := bstep (se 1 (by rfl) ⟨1719194, by rfl⟩ : syracuseStep 2292259 = 3438389) B3438389
theorem B1432147 : Blo 1271954 1432147 := bstep (se 1 (by rfl) ⟨1074110, by rfl⟩ : syracuseStep 1432147 = 2148221) B2148221
theorem B9173645 : Blo 1271954 9173645 := bstep (se 3 (by rfl) ⟨1720058, by rfl⟩ : syracuseStep 9173645 = 3440117) B3440117
theorem B1432291 : Blo 1271954 1432291 := bstep (se 1 (by rfl) ⟨1074218, by rfl⟩ : syracuseStep 1432291 = 2148437) B2148437
theorem B2865905 : Blo 1271954 2865905 := bstep (se 2 (by rfl) ⟨1074714, by rfl⟩ : syracuseStep 2865905 = 2149429) B2149429
theorem B2865923 : Blo 1271954 2865923 := bstep (se 1 (by rfl) ⟨2149442, by rfl⟩ : syracuseStep 2865923 = 4298885) B4298885
theorem B4299533 : Blo 1271954 4299533 := bstep (se 3 (by rfl) ⟨806162, by rfl⟩ : syracuseStep 4299533 = 1612325) B1612325
theorem B4299587 : Blo 1271954 4299587 := bstep (se 1 (by rfl) ⟨3224690, by rfl⟩ : syracuseStep 4299587 = 6449381) B6449381
theorem B5438285 : Blo 1271954 5438285 := bstep (se 3 (by rfl) ⟨1019678, by rfl⟩ : syracuseStep 5438285 = 2039357) B2039357
theorem B4135789 : Blo 1271954 4135789 := bstep (se 3 (by rfl) ⟨775460, by rfl⟩ : syracuseStep 4135789 = 1550921) B1550921
theorem B1432435 : Blo 1271954 1432435 := bstep (se 1 (by rfl) ⟨1074326, by rfl⟩ : syracuseStep 1432435 = 2148653) B2148653
theorem B2038691 : Blo 1271954 2038691 := bstep (se 1 (by rfl) ⟨1529018, by rfl⟩ : syracuseStep 2038691 = 3058037) B3058037
theorem B1432579 : Blo 1271954 1432579 := bstep (se 1 (by rfl) ⟨1074434, by rfl⟩ : syracuseStep 1432579 = 2148869) B2148869
theorem B8707085 : Blo 1271954 8707085 := bstep (se 3 (by rfl) ⟨1632578, by rfl⟩ : syracuseStep 8707085 = 3265157) B3265157
theorem B2866193 : Blo 1271954 2866193 := bstep (se 2 (by rfl) ⟨1074822, by rfl⟩ : syracuseStep 2866193 = 2149645) B2149645
theorem B2866211 : Blo 1271954 2866211 := bstep (se 1 (by rfl) ⟨2149658, by rfl⟩ : syracuseStep 2866211 = 4299317) B4299317
theorem B4078637 : Blo 1271954 4078637 := bstep (se 3 (by rfl) ⟨764744, by rfl⟩ : syracuseStep 4078637 = 1529489) B1529489
theorem B2718851 : Blo 1271954 2718851 := bstep (se 1 (by rfl) ⟨2039138, by rfl⟩ : syracuseStep 2718851 = 4078277) B4078277
theorem B1432723 : Blo 1271954 1432723 := bstep (se 1 (by rfl) ⟨1074542, by rfl⟩ : syracuseStep 1432723 = 2149085) B2149085
theorem B4832419 : Blo 1271954 4832419 := bstep (se 1 (by rfl) ⟨3624314, by rfl⟩ : syracuseStep 4832419 = 7248629) B7248629
theorem B3439793 : Blo 1271954 3439793 := bstep (se 2 (by rfl) ⟨1289922, by rfl⟩ : syracuseStep 3439793 = 2579845) B2579845
theorem B2038979 : Blo 1271954 2038979 := bstep (se 1 (by rfl) ⟨1529234, by rfl⟩ : syracuseStep 2038979 = 3058469) B3058469
theorem B1907939 : Blo 1271954 1907939 := bstep (se 1 (by rfl) ⟨1430954, by rfl⟩ : syracuseStep 1907939 = 2861909) B2861909
theorem B2579683 : Blo 1271954 2579683 := bstep (se 1 (by rfl) ⟨1934762, by rfl⟩ : syracuseStep 2579683 = 3869525) B3869525
theorem B1907969 : Blo 1271954 1907969 := bstep (se 2 (by rfl) ⟨715488, by rfl⟩ : syracuseStep 1907969 = 1430977) B1430977
theorem B1907987 : Blo 1271954 1907987 := bstep (se 1 (by rfl) ⟨1430990, by rfl⟩ : syracuseStep 1907987 = 2861981) B2861981
theorem B2579747 : Blo 1271954 2579747 := bstep (se 1 (by rfl) ⟨1934810, by rfl⟩ : syracuseStep 2579747 = 3869621) B3869621
theorem B1432867 : Blo 1271954 1432867 := bstep (se 1 (by rfl) ⟨1074650, by rfl⟩ : syracuseStep 1432867 = 2149301) B2149301
theorem B1908017 : Blo 1271954 1908017 := bstep (se 2 (by rfl) ⟨715506, by rfl⟩ : syracuseStep 1908017 = 1431013) B1431013
theorem B2178353 : Blo 1271954 2178353 := bstep (se 2 (by rfl) ⟨816882, by rfl⟩ : syracuseStep 2178353 = 1633765) B1633765
theorem B1908035 : Blo 1271954 1908035 := bstep (se 1 (by rfl) ⟨1431026, by rfl⟩ : syracuseStep 1908035 = 2862053) B2862053
theorem B1908065 : Blo 1271954 1908065 := bstep (se 2 (by rfl) ⟨715524, by rfl⟩ : syracuseStep 1908065 = 1431049) B1431049
theorem B1908083 : Blo 1271954 1908083 := bstep (se 1 (by rfl) ⟨1431062, by rfl⟩ : syracuseStep 1908083 = 2862125) B2862125
theorem B1908113 : Blo 1271954 1908113 := bstep (se 2 (by rfl) ⟨715542, by rfl⟩ : syracuseStep 1908113 = 1431085) B1431085
theorem B1908131 : Blo 1271954 1908131 := bstep (se 1 (by rfl) ⟨1431098, by rfl⟩ : syracuseStep 1908131 = 2862197) B2862197
theorem B2039203 : Blo 1271954 2039203 := bstep (se 1 (by rfl) ⟨1529402, by rfl⟩ : syracuseStep 2039203 = 3058805) B3058805
theorem B1433011 : Blo 1271954 1433011 := bstep (se 1 (by rfl) ⟨1074758, by rfl⟩ : syracuseStep 1433011 = 2149517) B2149517
theorem B14491061 : Blo 1271954 14491061 := bstep (se 5 (by rfl) ⟨679268, by rfl⟩ : syracuseStep 14491061 = 1358537) B1358537
theorem B1908161 : Blo 1271954 1908161 := bstep (se 2 (by rfl) ⟨715560, by rfl⟩ : syracuseStep 1908161 = 1431121) B1431121
theorem B6880709 : Blo 1271954 6880709 := bstep (se 4 (by rfl) ⟨645066, by rfl⟩ : syracuseStep 6880709 = 1290133) B1290133
theorem B2416081 : Blo 1271954 2416081 := bstep (se 2 (by rfl) ⟨906030, by rfl⟩ : syracuseStep 2416081 = 1812061) B1812061
theorem B1908179 : Blo 1271954 1908179 := bstep (se 1 (by rfl) ⟨1431134, by rfl⟩ : syracuseStep 1908179 = 2862269) B2862269
theorem B1908209 : Blo 1271954 1908209 := bstep (se 2 (by rfl) ⟨715578, by rfl⟩ : syracuseStep 1908209 = 1431157) B1431157
theorem B1908227 : Blo 1271954 1908227 := bstep (se 1 (by rfl) ⟨1431170, by rfl⟩ : syracuseStep 1908227 = 2862341) B2862341
theorem B3440141 : Blo 1271954 3440141 := bstep (se 3 (by rfl) ⟨645026, by rfl⟩ : syracuseStep 3440141 = 1290053) B1290053
theorem B1908257 : Blo 1271954 1908257 := bstep (se 2 (by rfl) ⟨715596, by rfl⟩ : syracuseStep 1908257 = 1431193) B1431193
theorem B6446627 : Blo 1271954 6446627 := bstep (se 1 (by rfl) ⟨4834970, by rfl⟩ : syracuseStep 6446627 = 9669941) B9669941
theorem B1908275 : Blo 1271954 1908275 := bstep (se 1 (by rfl) ⟨1431206, by rfl⟩ : syracuseStep 1908275 = 2862413) B2862413
theorem B1433155 : Blo 1271954 1433155 := bstep (se 1 (by rfl) ⟨1074866, by rfl⟩ : syracuseStep 1433155 = 2149733) B2149733
theorem B1908305 : Blo 1271954 1908305 := bstep (se 2 (by rfl) ⟨715614, by rfl⟩ : syracuseStep 1908305 = 1431229) B1431229
theorem B1359443 : Blo 1271954 1359443 := bstep (se 1 (by rfl) ⟨1019582, by rfl⟩ : syracuseStep 1359443 = 2039165) B2039165
theorem B1908323 : Blo 1271954 1908323 := bstep (se 1 (by rfl) ⟨1431242, by rfl⟩ : syracuseStep 1908323 = 2862485) B2862485
theorem B1908353 : Blo 1271954 1908353 := bstep (se 2 (by rfl) ⟨715632, by rfl⟩ : syracuseStep 1908353 = 1431265) B1431265
theorem B1908371 : Blo 1271954 1908371 := bstep (se 1 (by rfl) ⟨1431278, by rfl⟩ : syracuseStep 1908371 = 2862557) B2862557
theorem B1908401 : Blo 1271954 1908401 := bstep (se 2 (by rfl) ⟨715650, by rfl⟩ : syracuseStep 1908401 = 1431301) B1431301
theorem B1908419 : Blo 1271954 1908419 := bstep (se 1 (by rfl) ⟨1431314, by rfl⟩ : syracuseStep 1908419 = 2862629) B2862629
theorem B1908449 : Blo 1271954 1908449 := bstep (se 2 (by rfl) ⟨715668, by rfl⟩ : syracuseStep 1908449 = 1431337) B1431337
theorem B1908467 : Blo 1271954 1908467 := bstep (se 1 (by rfl) ⟨1431350, by rfl⟩ : syracuseStep 1908467 = 2862701) B2862701
theorem B1908497 : Blo 1271954 1908497 := bstep (se 2 (by rfl) ⟨715686, by rfl⟩ : syracuseStep 1908497 = 1431373) B1431373
theorem B1908515 : Blo 1271954 1908515 := bstep (se 1 (by rfl) ⟨1431386, by rfl⟩ : syracuseStep 1908515 = 2862773) B2862773
theorem B4079405 : Blo 1271954 4079405 := bstep (se 3 (by rfl) ⟨764888, by rfl⟩ : syracuseStep 4079405 = 1529777) B1529777
theorem B4587313 : Blo 1271954 4587313 := bstep (se 2 (by rfl) ⟨1720242, by rfl⟩ : syracuseStep 4587313 = 3440485) B3440485
theorem B1908545 : Blo 1271954 1908545 := bstep (se 2 (by rfl) ⟨715704, by rfl⟩ : syracuseStep 1908545 = 1431409) B1431409
theorem B1908563 : Blo 1271954 1908563 := bstep (se 1 (by rfl) ⟨1431422, by rfl⟩ : syracuseStep 1908563 = 2862845) B2862845
theorem B2416483 : Blo 1271954 2416483 := bstep (se 1 (by rfl) ⟨1812362, by rfl⟩ : syracuseStep 2416483 = 3624725) B3624725
theorem B1908593 : Blo 1271954 1908593 := bstep (se 2 (by rfl) ⟨715722, by rfl⟩ : syracuseStep 1908593 = 1431445) B1431445
theorem B1908611 : Blo 1271954 1908611 := bstep (se 1 (by rfl) ⟨1431458, by rfl⟩ : syracuseStep 1908611 = 2862917) B2862917
theorem B15482765 : Blo 1271954 15482765 := bstep (se 3 (by rfl) ⟨2903018, by rfl⟩ : syracuseStep 15482765 = 5806037) B5806037
theorem B2416529 : Blo 1271954 2416529 := bstep (se 2 (by rfl) ⟨906198, by rfl⟩ : syracuseStep 2416529 = 1812397) B1812397
theorem B1908641 : Blo 1271954 1908641 := bstep (se 2 (by rfl) ⟨715740, by rfl⟩ : syracuseStep 1908641 = 1431481) B1431481
theorem B1908659 : Blo 1271954 1908659 := bstep (se 1 (by rfl) ⟨1431494, by rfl⟩ : syracuseStep 1908659 = 2862989) B2862989
theorem B1908689 : Blo 1271954 1908689 := bstep (se 2 (by rfl) ⟨715758, by rfl⟩ : syracuseStep 1908689 = 1431517) B1431517
theorem B1908707 : Blo 1271954 1908707 := bstep (se 1 (by rfl) ⟨1431530, by rfl⟩ : syracuseStep 1908707 = 2863061) B2863061
theorem B2039831 : Blo 1271954 2039831 := bstep (se 1 (by rfl) ⟨1529873, by rfl⟩ : syracuseStep 2039831 = 3059747) B3059747
theorem B1908761 : Blo 1271954 1908761 := bstep (se 2 (by rfl) ⟨715785, by rfl⟩ : syracuseStep 1908761 = 1431571) B1431571
theorem B1359947 : Blo 1271954 1359947 := bstep (se 1 (by rfl) ⟨1019960, by rfl⟩ : syracuseStep 1359947 = 2039921) B2039921
theorem B1908875 : Blo 1271954 1908875 := bstep (se 1 (by rfl) ⟨1431656, by rfl⟩ : syracuseStep 1908875 = 2863313) B2863313
theorem B1908887 : Blo 1271954 1908887 := bstep (se 1 (by rfl) ⟨1431665, by rfl⟩ : syracuseStep 1908887 = 2863331) B2863331
theorem B3219659 : Blo 1271954 3219659 := bstep (se 1 (by rfl) ⟨2414744, by rfl⟩ : syracuseStep 3219659 = 4829489) B4829489
theorem B1360075 : Blo 1271954 1360075 := bstep (se 1 (by rfl) ⟨1020056, by rfl⟩ : syracuseStep 1360075 = 2040113) B2040113
theorem B2040023 : Blo 1271954 2040023 := bstep (se 1 (by rfl) ⟨1530017, by rfl⟩ : syracuseStep 2040023 = 3060035) B3060035
theorem B1908953 : Blo 1271954 1908953 := bstep (se 2 (by rfl) ⟨715857, by rfl⟩ : syracuseStep 1908953 = 1431715) B1431715
theorem B13951277 : Blo 1271954 13951277 := bstep (se 3 (by rfl) ⟨2615864, by rfl⟩ : syracuseStep 13951277 = 5231729) B5231729
theorem B13066541 : Blo 1271954 13066541 := bstep (se 3 (by rfl) ⟨2449976, by rfl⟩ : syracuseStep 13066541 = 4899953) B4899953
theorem B1909067 : Blo 1271954 1909067 := bstep (se 1 (by rfl) ⟨1431800, by rfl⟩ : syracuseStep 1909067 = 2863601) B2863601
theorem B1909079 : Blo 1271954 1909079 := bstep (se 1 (by rfl) ⟨1431809, by rfl⟩ : syracuseStep 1909079 = 2863619) B2863619
theorem B7250269 : Blo 1271954 7250269 := bstep (se 3 (by rfl) ⟨1359425, by rfl⟩ : syracuseStep 7250269 = 2718851) B2718851
theorem B5439889 : Blo 1271954 5439889 := bstep (se 2 (by rfl) ⟨2039958, by rfl⟩ : syracuseStep 5439889 = 4079917) B4079917
theorem B1909145 : Blo 1271954 1909145 := bstep (se 2 (by rfl) ⟨715929, by rfl⟩ : syracuseStep 1909145 = 1431859) B1431859
theorem B847561157 : Blo 1271954 847561157 := bstep (se 4 (by rfl) ⟨79458858, by rfl⟩ : syracuseStep 847561157 = 158917717) B158917717
theorem B2146763 : Blo 1271954 2146763 := bstep (se 1 (by rfl) ⟨1610072, by rfl⟩ : syracuseStep 2146763 = 3220145) B3220145
theorem B5161475 : Blo 1271954 5161475 := bstep (se 1 (by rfl) ⟨3871106, by rfl⟩ : syracuseStep 5161475 = 7742213) B7742213
theorem B1909259 : Blo 1271954 1909259 := bstep (se 1 (by rfl) ⟨1431944, by rfl⟩ : syracuseStep 1909259 = 2863889) B2863889
theorem B2040331 : Blo 1271954 2040331 := bstep (se 1 (by rfl) ⟨1530248, by rfl⟩ : syracuseStep 2040331 = 3060497) B3060497
theorem B10879505 : Blo 1271954 10879505 := bstep (se 2 (by rfl) ⟨4079814, by rfl⟩ : syracuseStep 10879505 = 8159629) B8159629
theorem B1909271 : Blo 1271954 1909271 := bstep (se 1 (by rfl) ⟨1431953, by rfl⟩ : syracuseStep 1909271 = 2863907) B2863907
theorem B2720279 : Blo 1271954 2720279 := bstep (se 1 (by rfl) ⟨2040209, by rfl⟩ : syracuseStep 2720279 = 4080419) B4080419
theorem B3220033 : Blo 1271954 3220033 := bstep (se 2 (by rfl) ⟨1207512, by rfl⟩ : syracuseStep 3220033 = 2415025) B2415025
theorem B2720321 : Blo 1271954 2720321 := bstep (se 2 (by rfl) ⟨1020120, by rfl⟩ : syracuseStep 2720321 = 2040241) B2040241
theorem B6439499 : Blo 1271954 6439499 := bstep (se 1 (by rfl) ⟨4829624, by rfl⟩ : syracuseStep 6439499 = 9659249) B9659249
theorem B2146891 : Blo 1271954 2146891 := bstep (se 1 (by rfl) ⟨1610168, by rfl⟩ : syracuseStep 2146891 = 3220337) B3220337
theorem B1909337 : Blo 1271954 1909337 := bstep (se 2 (by rfl) ⟨716001, by rfl⟩ : syracuseStep 1909337 = 1432003) B1432003
theorem B2417303 : Blo 1271954 2417303 := bstep (se 1 (by rfl) ⟨1812977, by rfl⟩ : syracuseStep 2417303 = 3625955) B3625955
theorem B4293323 : Blo 1271954 4293323 := bstep (se 1 (by rfl) ⟨3219992, by rfl⟩ : syracuseStep 4293323 = 6439985) B6439985
theorem B1909451 : Blo 1271954 1909451 := bstep (se 1 (by rfl) ⟨1432088, by rfl⟩ : syracuseStep 1909451 = 2864177) B2864177
theorem B1909463 : Blo 1271954 1909463 := bstep (se 1 (by rfl) ⟨1432097, by rfl⟩ : syracuseStep 1909463 = 2864195) B2864195
theorem B3056345 : Blo 1271954 3056345 := bstep (se 2 (by rfl) ⟨1146129, by rfl⟩ : syracuseStep 3056345 = 2292259) B2292259
theorem B2147033 : Blo 1271954 2147033 := bstep (se 2 (by rfl) ⟨805137, by rfl⟩ : syracuseStep 2147033 = 1610275) B1610275
theorem B1909529 : Blo 1271954 1909529 := bstep (se 2 (by rfl) ⟨716073, by rfl⟩ : syracuseStep 1909529 = 1432147) B1432147
theorem B5808941 : Blo 1271954 5808941 := bstep (se 3 (by rfl) ⟨1089176, by rfl⟩ : syracuseStep 5808941 = 2178353) B2178353
theorem B2294579 : Blo 1271954 2294579 := bstep (se 1 (by rfl) ⟨1720934, by rfl⟩ : syracuseStep 2294579 = 3441869) B3441869
theorem B2147161 : Blo 1271954 2147161 := bstep (se 2 (by rfl) ⟨805185, by rfl⟩ : syracuseStep 2147161 = 1610371) B1610371
theorem B1909643 : Blo 1271954 1909643 := bstep (se 1 (by rfl) ⟨1432232, by rfl⟩ : syracuseStep 1909643 = 2864465) B2864465
theorem B1909655 : Blo 1271954 1909655 := bstep (se 1 (by rfl) ⟨1432241, by rfl⟩ : syracuseStep 1909655 = 2864483) B2864483
theorem B4293593 : Blo 1271954 4293593 := bstep (se 2 (by rfl) ⟨1610097, by rfl⟩ : syracuseStep 4293593 = 3220195) B3220195
theorem B1909721 : Blo 1271954 1909721 := bstep (se 2 (by rfl) ⟨716145, by rfl⟩ : syracuseStep 1909721 = 1432291) B1432291
theorem B4834349 : Blo 1271954 4834349 := bstep (se 3 (by rfl) ⟨906440, by rfl⟩ : syracuseStep 4834349 = 1812881) B1812881
theorem B1811531 : Blo 1271954 1811531 := bstep (se 1 (by rfl) ⟨1358648, by rfl⟩ : syracuseStep 1811531 = 2717297) B2717297
theorem B12231755 : Blo 1271954 12231755 := bstep (se 1 (by rfl) ⟨9173816, by rfl⟩ : syracuseStep 12231755 = 18347633) B18347633
theorem B1909835 : Blo 1271954 1909835 := bstep (se 1 (by rfl) ⟨1432376, by rfl⟩ : syracuseStep 1909835 = 2864753) B2864753
theorem B1909847 : Blo 1271954 1909847 := bstep (se 1 (by rfl) ⟨1432385, by rfl⟩ : syracuseStep 1909847 = 2864771) B2864771
theorem B3220631 : Blo 1271954 3220631 := bstep (se 1 (by rfl) ⟨2415473, by rfl⟩ : syracuseStep 3220631 = 4830947) B4830947
theorem B1909913 : Blo 1271954 1909913 := bstep (se 2 (by rfl) ⟨716217, by rfl⟩ : syracuseStep 1909913 = 1432435) B1432435
theorem B2417843 : Blo 1271954 2417843 := bstep (se 1 (by rfl) ⟨1813382, by rfl⟩ : syracuseStep 2417843 = 3626765) B3626765
theorem B1910027 : Blo 1271954 1910027 := bstep (se 1 (by rfl) ⟨1432520, by rfl⟩ : syracuseStep 1910027 = 2865041) B2865041
theorem B1910039 : Blo 1271954 1910039 := bstep (se 1 (by rfl) ⟨1432529, by rfl⟩ : syracuseStep 1910039 = 2865059) B2865059
theorem B1910105 : Blo 1271954 1910105 := bstep (se 2 (by rfl) ⟨716289, by rfl⟩ : syracuseStep 1910105 = 1432579) B1432579
theorem B22046053 : Blo 1271954 22046053 := bstep (se 4 (by rfl) ⟨2066817, by rfl⟩ : syracuseStep 22046053 = 4133635) B4133635
theorem B2147735 : Blo 1271954 2147735 := bstep (se 1 (by rfl) ⟨1610801, by rfl⟩ : syracuseStep 2147735 = 3221603) B3221603
theorem B1910219 : Blo 1271954 1910219 := bstep (se 1 (by rfl) ⟨1432664, by rfl⟩ : syracuseStep 1910219 = 2865329) B2865329
theorem B1910231 : Blo 1271954 1910231 := bstep (se 1 (by rfl) ⟨1432673, by rfl⟩ : syracuseStep 1910231 = 2865347) B2865347
theorem B10315225 : Blo 1271954 10315225 := bstep (se 2 (by rfl) ⟨3868209, by rfl⟩ : syracuseStep 10315225 = 7736419) B7736419
theorem B2147863 : Blo 1271954 2147863 := bstep (se 1 (by rfl) ⟨1610897, by rfl⟩ : syracuseStep 2147863 = 3221795) B3221795
theorem B1910297 : Blo 1271954 1910297 := bstep (se 2 (by rfl) ⟨716361, by rfl⟩ : syracuseStep 1910297 = 1432723) B1432723
theorem B4081175 : Blo 1271954 4081175 := bstep (se 1 (by rfl) ⟨3060881, by rfl⟩ : syracuseStep 4081175 = 6121763) B6121763
theorem B3868249 : Blo 1271954 3868249 := bstep (se 2 (by rfl) ⟨1450593, by rfl⟩ : syracuseStep 3868249 = 2901187) B2901187
theorem B6448733 : Blo 1271954 6448733 := bstep (se 3 (by rfl) ⟨1209137, by rfl⟩ : syracuseStep 6448733 = 2418275) B2418275
theorem B1910411 : Blo 1271954 1910411 := bstep (se 1 (by rfl) ⟨1432808, by rfl⟩ : syracuseStep 1910411 = 2865617) B2865617
theorem B4294295 : Blo 1271954 4294295 := bstep (se 1 (by rfl) ⟨3220721, by rfl⟩ : syracuseStep 4294295 = 6441443) B6441443
theorem B1910423 : Blo 1271954 1910423 := bstep (se 1 (by rfl) ⟨1432817, by rfl⟩ : syracuseStep 1910423 = 2865635) B2865635
theorem B2418329 : Blo 1271954 2418329 := bstep (se 2 (by rfl) ⟨906873, by rfl⟩ : syracuseStep 2418329 = 1813747) B1813747
theorem B1910489 : Blo 1271954 1910489 := bstep (se 2 (by rfl) ⟨716433, by rfl⟩ : syracuseStep 1910489 = 1432867) B1432867
theorem B4835123 : Blo 1271954 4835123 := bstep (se 1 (by rfl) ⟨3626342, by rfl⟩ : syracuseStep 4835123 = 7252685) B7252685
theorem B1910603 : Blo 1271954 1910603 := bstep (se 1 (by rfl) ⟨1432952, by rfl⟩ : syracuseStep 1910603 = 2865905) B2865905
theorem B1910615 : Blo 1271954 1910615 := bstep (se 1 (by rfl) ⟨1432961, by rfl⟩ : syracuseStep 1910615 = 2865923) B2865923
theorem B9668483 : Blo 1271954 9668483 := bstep (se 1 (by rfl) ⟨7251362, by rfl⟩ : syracuseStep 9668483 = 14502725) B14502725
theorem B1910681 : Blo 1271954 1910681 := bstep (se 2 (by rfl) ⟨716505, by rfl⟩ : syracuseStep 1910681 = 1433011) B1433011
theorem B3221441 : Blo 1271954 3221441 := bstep (se 2 (by rfl) ⟨1208040, by rfl⟩ : syracuseStep 3221441 = 2416081) B2416081
theorem B1910795 : Blo 1271954 1910795 := bstep (se 1 (by rfl) ⟨1433096, by rfl⟩ : syracuseStep 1910795 = 2866193) B2866193
theorem B1910807 : Blo 1271954 1910807 := bstep (se 1 (by rfl) ⟨1433105, by rfl⟩ : syracuseStep 1910807 = 2866211) B2866211
theorem B1910873 : Blo 1271954 1910873 := bstep (se 2 (by rfl) ⟨716577, by rfl⟩ : syracuseStep 1910873 = 1433155) B1433155
theorem B21751901 : Blo 1271954 21751901 := bstep (se 3 (by rfl) ⟨4078481, by rfl⟩ : syracuseStep 21751901 = 8156963) B8156963
theorem B2148491 : Blo 1271954 2148491 := bstep (se 1 (by rfl) ⟨1611368, by rfl⟩ : syracuseStep 2148491 = 3222737) B3222737
theorem B1271959 : Blo 1271954 1271959 := bstep (se 1 (by rfl) ⟨953969, by rfl⟩ : syracuseStep 1271959 = 1907939) B1907939
theorem B1271979 : Blo 1271954 1271979 := bstep (se 1 (by rfl) ⟨953984, by rfl⟩ : syracuseStep 1271979 = 1907969) B1907969
theorem B4294835 : Blo 1271954 4294835 := bstep (se 1 (by rfl) ⟨3221126, by rfl⟩ : syracuseStep 4294835 = 6442253) B6442253
theorem B1271991 : Blo 1271954 1271991 := bstep (se 1 (by rfl) ⟨953993, by rfl⟩ : syracuseStep 1271991 = 1907987) B1907987
theorem B1272011 : Blo 1271954 1272011 := bstep (se 1 (by rfl) ⟨954008, by rfl⟩ : syracuseStep 1272011 = 1908017) B1908017
theorem B1272023 : Blo 1271954 1272023 := bstep (se 1 (by rfl) ⟨954017, by rfl⟩ : syracuseStep 1272023 = 1908035) B1908035
theorem B1272043 : Blo 1271954 1272043 := bstep (se 1 (by rfl) ⟨954032, by rfl⟩ : syracuseStep 1272043 = 1908065) B1908065
theorem B1272055 : Blo 1271954 1272055 := bstep (se 1 (by rfl) ⟨954041, by rfl⟩ : syracuseStep 1272055 = 1908083) B1908083
theorem B10455301 : Blo 1271954 10455301 := bstep (se 4 (by rfl) ⟨980184, by rfl⟩ : syracuseStep 10455301 = 1960369) B1960369
theorem B1272075 : Blo 1271954 1272075 := bstep (se 1 (by rfl) ⟨954056, by rfl⟩ : syracuseStep 1272075 = 1908113) B1908113
theorem B2148619 : Blo 1271954 2148619 := bstep (se 1 (by rfl) ⟨1611464, by rfl⟩ : syracuseStep 2148619 = 3222929) B3222929
theorem B1272087 : Blo 1271954 1272087 := bstep (se 1 (by rfl) ⟨954065, by rfl⟩ : syracuseStep 1272087 = 1908131) B1908131
theorem B9660707 : Blo 1271954 9660707 := bstep (se 1 (by rfl) ⟨7245530, by rfl⟩ : syracuseStep 9660707 = 14491061) B14491061
theorem B1272107 : Blo 1271954 1272107 := bstep (se 1 (by rfl) ⟨954080, by rfl⟩ : syracuseStep 1272107 = 1908161) B1908161
theorem B1272119 : Blo 1271954 1272119 := bstep (se 1 (by rfl) ⟨954089, by rfl⟩ : syracuseStep 1272119 = 1908179) B1908179
theorem B6441281 : Blo 1271954 6441281 := bstep (se 2 (by rfl) ⟨2415480, by rfl⟩ : syracuseStep 6441281 = 4830961) B4830961
theorem B1272139 : Blo 1271954 1272139 := bstep (se 1 (by rfl) ⟨954104, by rfl⟩ : syracuseStep 1272139 = 1908209) B1908209
theorem B1272151 : Blo 1271954 1272151 := bstep (se 1 (by rfl) ⟨954113, by rfl⟩ : syracuseStep 1272151 = 1908227) B1908227
theorem B1272171 : Blo 1271954 1272171 := bstep (se 1 (by rfl) ⟨954128, by rfl⟩ : syracuseStep 1272171 = 1908257) B1908257
theorem B1272183 : Blo 1271954 1272183 := bstep (se 1 (by rfl) ⟨954137, by rfl⟩ : syracuseStep 1272183 = 1908275) B1908275
theorem B1272203 : Blo 1271954 1272203 := bstep (se 1 (by rfl) ⟨954152, by rfl⟩ : syracuseStep 1272203 = 1908305) B1908305
theorem B1272215 : Blo 1271954 1272215 := bstep (se 1 (by rfl) ⟨954161, by rfl⟩ : syracuseStep 1272215 = 1908323) B1908323
theorem B2148761 : Blo 1271954 2148761 := bstep (se 2 (by rfl) ⟨805785, by rfl⟩ : syracuseStep 2148761 = 1611571) B1611571
theorem B1272235 : Blo 1271954 1272235 := bstep (se 1 (by rfl) ⟨954176, by rfl⟩ : syracuseStep 1272235 = 1908353) B1908353
theorem B3443123 : Blo 1271954 3443123 := bstep (se 1 (by rfl) ⟨2582342, by rfl⟩ : syracuseStep 3443123 = 5164685) B5164685
theorem B1272247 : Blo 1271954 1272247 := bstep (se 1 (by rfl) ⟨954185, by rfl⟩ : syracuseStep 1272247 = 1908371) B1908371
theorem B4295105 : Blo 1271954 4295105 := bstep (se 2 (by rfl) ⟨1610664, by rfl⟩ : syracuseStep 4295105 = 3221329) B3221329
theorem B5507531 : Blo 1271954 5507531 := bstep (se 1 (by rfl) ⟨4130648, by rfl⟩ : syracuseStep 5507531 = 8261297) B8261297
theorem B1272267 : Blo 1271954 1272267 := bstep (se 1 (by rfl) ⟨954200, by rfl⟩ : syracuseStep 1272267 = 1908401) B1908401
theorem B1272279 : Blo 1271954 1272279 := bstep (se 1 (by rfl) ⟨954209, by rfl⟩ : syracuseStep 1272279 = 1908419) B1908419
theorem B3221977 : Blo 1271954 3221977 := bstep (se 2 (by rfl) ⟨1208241, by rfl⟩ : syracuseStep 3221977 = 2416483) B2416483
theorem B1272299 : Blo 1271954 1272299 := bstep (se 1 (by rfl) ⟨954224, by rfl⟩ : syracuseStep 1272299 = 1908449) B1908449
theorem B1272311 : Blo 1271954 1272311 := bstep (se 1 (by rfl) ⟨954233, by rfl⟩ : syracuseStep 1272311 = 1908467) B1908467
theorem B2902529 : Blo 1271954 2902529 := bstep (se 2 (by rfl) ⟨1088448, by rfl⟩ : syracuseStep 2902529 = 2176897) B2176897
theorem B1272331 : Blo 1271954 1272331 := bstep (se 1 (by rfl) ⟨954248, by rfl⟩ : syracuseStep 1272331 = 1908497) B1908497
theorem B1272343 : Blo 1271954 1272343 := bstep (se 1 (by rfl) ⟨954257, by rfl⟩ : syracuseStep 1272343 = 1908515) B1908515
theorem B2148889 : Blo 1271954 2148889 := bstep (se 2 (by rfl) ⟨805833, by rfl⟩ : syracuseStep 2148889 = 1611667) B1611667
theorem B1272363 : Blo 1271954 1272363 := bstep (se 1 (by rfl) ⟨954272, by rfl⟩ : syracuseStep 1272363 = 1908545) B1908545
theorem B1272375 : Blo 1271954 1272375 := bstep (se 1 (by rfl) ⟨954281, by rfl⟩ : syracuseStep 1272375 = 1908563) B1908563
theorem B1272395 : Blo 1271954 1272395 := bstep (se 1 (by rfl) ⟨954296, by rfl⟩ : syracuseStep 1272395 = 1908593) B1908593
theorem B1272407 : Blo 1271954 1272407 := bstep (se 1 (by rfl) ⟨954305, by rfl⟩ : syracuseStep 1272407 = 1908611) B1908611
theorem B49572445 : Blo 1271954 49572445 := bstep (se 3 (by rfl) ⟨9294833, by rfl⟩ : syracuseStep 49572445 = 18589667) B18589667
theorem B1272427 : Blo 1271954 1272427 := bstep (se 1 (by rfl) ⟨954320, by rfl⟩ : syracuseStep 1272427 = 1908641) B1908641
theorem B1272439 : Blo 1271954 1272439 := bstep (se 1 (by rfl) ⟨954329, by rfl⟩ : syracuseStep 1272439 = 1908659) B1908659
theorem B1272459 : Blo 1271954 1272459 := bstep (se 1 (by rfl) ⟨954344, by rfl⟩ : syracuseStep 1272459 = 1908689) B1908689
theorem B1272471 : Blo 1271954 1272471 := bstep (se 1 (by rfl) ⟨954353, by rfl⟩ : syracuseStep 1272471 = 1908707) B1908707
theorem B3623575 : Blo 1271954 3623575 := bstep (se 1 (by rfl) ⟨2717681, by rfl⟩ : syracuseStep 3623575 = 5435363) B5435363
theorem B1272491 : Blo 1271954 1272491 := bstep (se 1 (by rfl) ⟨954368, by rfl⟩ : syracuseStep 1272491 = 1908737) B1908737
theorem B1272503 : Blo 1271954 1272503 := bstep (se 1 (by rfl) ⟨954377, by rfl⟩ : syracuseStep 1272503 = 1908755) B1908755
theorem B5163713 : Blo 1271954 5163713 := bstep (se 2 (by rfl) ⟨1936392, by rfl⟩ : syracuseStep 5163713 = 3872785) B3872785
theorem B1272523 : Blo 1271954 1272523 := bstep (se 1 (by rfl) ⟨954392, by rfl⟩ : syracuseStep 1272523 = 1908785) B1908785
theorem B1272535 : Blo 1271954 1272535 := bstep (se 1 (by rfl) ⟨954401, by rfl⟩ : syracuseStep 1272535 = 1908803) B1908803
theorem B1272555 : Blo 1271954 1272555 := bstep (se 1 (by rfl) ⟨954416, by rfl⟩ : syracuseStep 1272555 = 1908833) B1908833
theorem B1272567 : Blo 1271954 1272567 := bstep (se 1 (by rfl) ⟨954425, by rfl⟩ : syracuseStep 1272567 = 1908851) B1908851
theorem B1272587 : Blo 1271954 1272587 := bstep (se 1 (by rfl) ⟨954440, by rfl⟩ : syracuseStep 1272587 = 1908881) B1908881
theorem B1272599 : Blo 1271954 1272599 := bstep (se 1 (by rfl) ⟨954449, by rfl⟩ : syracuseStep 1272599 = 1908899) B1908899
theorem B1272619 : Blo 1271954 1272619 := bstep (se 1 (by rfl) ⟨954464, by rfl⟩ : syracuseStep 1272619 = 1908929) B1908929
theorem B7744301 : Blo 1271954 7744301 := bstep (se 3 (by rfl) ⟨1452056, by rfl⟩ : syracuseStep 7744301 = 2904113) B2904113
theorem B1272631 : Blo 1271954 1272631 := bstep (se 1 (by rfl) ⟨954473, by rfl⟩ : syracuseStep 1272631 = 1908947) B1908947
theorem B5163841 : Blo 1271954 5163841 := bstep (se 2 (by rfl) ⟨1936440, by rfl⟩ : syracuseStep 5163841 = 3872881) B3872881
theorem B1272651 : Blo 1271954 1272651 := bstep (se 1 (by rfl) ⟨954488, by rfl⟩ : syracuseStep 1272651 = 1908977) B1908977
theorem B1272663 : Blo 1271954 1272663 := bstep (se 1 (by rfl) ⟨954497, by rfl⟩ : syracuseStep 1272663 = 1908995) B1908995
theorem B1272683 : Blo 1271954 1272683 := bstep (se 1 (by rfl) ⟨954512, by rfl⟩ : syracuseStep 1272683 = 1909025) B1909025
theorem B1272695 : Blo 1271954 1272695 := bstep (se 1 (by rfl) ⟨954521, by rfl⟩ : syracuseStep 1272695 = 1909043) B1909043
theorem B2861963 : Blo 1271954 2861963 := bstep (se 1 (by rfl) ⟨2146472, by rfl⟩ : syracuseStep 2861963 = 4292945) B4292945
theorem B1272715 : Blo 1271954 1272715 := bstep (se 1 (by rfl) ⟨954536, by rfl⟩ : syracuseStep 1272715 = 1909073) B1909073
theorem B1272727 : Blo 1271954 1272727 := bstep (se 1 (by rfl) ⟨954545, by rfl⟩ : syracuseStep 1272727 = 1909091) B1909091
theorem B1272747 : Blo 1271954 1272747 := bstep (se 1 (by rfl) ⟨954560, by rfl⟩ : syracuseStep 1272747 = 1909121) B1909121
theorem B5434285 : Blo 1271954 5434285 := bstep (se 3 (by rfl) ⟨1018928, by rfl⟩ : syracuseStep 5434285 = 2037857) B2037857
theorem B4647853 : Blo 1271954 4647853 := bstep (se 3 (by rfl) ⟨871472, by rfl⟩ : syracuseStep 4647853 = 1742945) B1742945
theorem B1272759 : Blo 1271954 1272759 := bstep (se 1 (by rfl) ⟨954569, by rfl⟩ : syracuseStep 1272759 = 1909139) B1909139
theorem B2862017 : Blo 1271954 2862017 := bstep (se 2 (by rfl) ⟨1073256, by rfl⟩ : syracuseStep 2862017 = 2146513) B2146513
theorem B1272779 : Blo 1271954 1272779 := bstep (se 1 (by rfl) ⟨954584, by rfl⟩ : syracuseStep 1272779 = 1909169) B1909169
theorem B1272791 : Blo 1271954 1272791 := bstep (se 1 (by rfl) ⟨954593, by rfl⟩ : syracuseStep 1272791 = 1909187) B1909187
theorem B110185433 : Blo 1271954 110185433 := bstep (se 2 (by rfl) ⟨41319537, by rfl⟩ : syracuseStep 110185433 = 82639075) B82639075
theorem B4295645 : Blo 1271954 4295645 := bstep (se 3 (by rfl) ⟨805433, by rfl⟩ : syracuseStep 4295645 = 1610867) B1610867
theorem B1272811 : Blo 1271954 1272811 := bstep (se 1 (by rfl) ⟨954608, by rfl⟩ : syracuseStep 1272811 = 1909217) B1909217
theorem B1272823 : Blo 1271954 1272823 := bstep (se 1 (by rfl) ⟨954617, by rfl⟩ : syracuseStep 1272823 = 1909235) B1909235
theorem B1272843 : Blo 1271954 1272843 := bstep (se 1 (by rfl) ⟨954632, by rfl⟩ : syracuseStep 1272843 = 1909265) B1909265
theorem B1272855 : Blo 1271954 1272855 := bstep (se 1 (by rfl) ⟨954641, by rfl⟩ : syracuseStep 1272855 = 1909283) B1909283
theorem B9169955 : Blo 1271954 9169955 := bstep (se 1 (by rfl) ⟨6877466, by rfl⟩ : syracuseStep 9169955 = 13754933) B13754933
theorem B1272875 : Blo 1271954 1272875 := bstep (se 1 (by rfl) ⟨954656, by rfl⟩ : syracuseStep 1272875 = 1909313) B1909313
theorem B1272887 : Blo 1271954 1272887 := bstep (se 1 (by rfl) ⟨954665, by rfl⟩ : syracuseStep 1272887 = 1909331) B1909331
theorem B1272907 : Blo 1271954 1272907 := bstep (se 1 (by rfl) ⟨954680, by rfl⟩ : syracuseStep 1272907 = 1909361) B1909361
theorem B9301067 : Blo 1271954 9301067 := bstep (se 1 (by rfl) ⟨6975800, by rfl⟩ : syracuseStep 9301067 = 13951601) B13951601
theorem B1272919 : Blo 1271954 1272919 := bstep (se 1 (by rfl) ⟨954689, by rfl⟩ : syracuseStep 1272919 = 1909379) B1909379
theorem B2149463 : Blo 1271954 2149463 := bstep (se 1 (by rfl) ⟨1612097, by rfl⟩ : syracuseStep 2149463 = 3224195) B3224195
theorem B9423965 : Blo 1271954 9423965 := bstep (se 3 (by rfl) ⟨1766993, by rfl⟩ : syracuseStep 9423965 = 3533987) B3533987
theorem B1272939 : Blo 1271954 1272939 := bstep (se 1 (by rfl) ⟨954704, by rfl⟩ : syracuseStep 1272939 = 1909409) B1909409
theorem B1272951 : Blo 1271954 1272951 := bstep (se 1 (by rfl) ⟨954713, by rfl⟩ : syracuseStep 1272951 = 1909427) B1909427
theorem B1272971 : Blo 1271954 1272971 := bstep (se 1 (by rfl) ⟨954728, by rfl⟩ : syracuseStep 1272971 = 1909457) B1909457
theorem B1272983 : Blo 1271954 1272983 := bstep (se 1 (by rfl) ⟨954737, by rfl⟩ : syracuseStep 1272983 = 1909475) B1909475
theorem B2862233 : Blo 1271954 2862233 := bstep (se 2 (by rfl) ⟨1073337, by rfl⟩ : syracuseStep 2862233 = 2146675) B2146675
theorem B1273003 : Blo 1271954 1273003 := bstep (se 1 (by rfl) ⟨954752, by rfl⟩ : syracuseStep 1273003 = 1909505) B1909505
theorem B1273015 : Blo 1271954 1273015 := bstep (se 1 (by rfl) ⟨954761, by rfl⟩ : syracuseStep 1273015 = 1909523) B1909523
theorem B1273035 : Blo 1271954 1273035 := bstep (se 1 (by rfl) ⟨954776, by rfl⟩ : syracuseStep 1273035 = 1909553) B1909553
theorem B1273047 : Blo 1271954 1273047 := bstep (se 1 (by rfl) ⟨954785, by rfl⟩ : syracuseStep 1273047 = 1909571) B1909571
theorem B2149591 : Blo 1271954 2149591 := bstep (se 1 (by rfl) ⟨1612193, by rfl⟩ : syracuseStep 2149591 = 3224387) B3224387
theorem B1273067 : Blo 1271954 1273067 := bstep (se 1 (by rfl) ⟨954800, by rfl⟩ : syracuseStep 1273067 = 1909601) B1909601
theorem B20638961 : Blo 1271954 20638961 := bstep (se 2 (by rfl) ⟨7739610, by rfl⟩ : syracuseStep 20638961 = 15479221) B15479221
theorem B2862323 : Blo 1271954 2862323 := bstep (se 1 (by rfl) ⟨2146742, by rfl⟩ : syracuseStep 2862323 = 4293485) B4293485
theorem B1273079 : Blo 1271954 1273079 := bstep (se 1 (by rfl) ⟨954809, by rfl⟩ : syracuseStep 1273079 = 1909619) B1909619
theorem B5434627 : Blo 1271954 5434627 := bstep (se 1 (by rfl) ⟨4075970, by rfl⟩ : syracuseStep 5434627 = 8151941) B8151941
theorem B4836611 : Blo 1271954 4836611 := bstep (se 1 (by rfl) ⟨3627458, by rfl⟩ : syracuseStep 4836611 = 7254917) B7254917
theorem B1273099 : Blo 1271954 1273099 := bstep (se 1 (by rfl) ⟨954824, by rfl⟩ : syracuseStep 1273099 = 1909649) B1909649
theorem B2862359 : Blo 1271954 2862359 := bstep (se 1 (by rfl) ⟨2146769, by rfl⟩ : syracuseStep 2862359 = 4293539) B4293539
theorem B1273111 : Blo 1271954 1273111 := bstep (se 1 (by rfl) ⟨954833, by rfl⟩ : syracuseStep 1273111 = 1909667) B1909667
theorem B1273131 : Blo 1271954 1273131 := bstep (se 1 (by rfl) ⟨954848, by rfl⟩ : syracuseStep 1273131 = 1909697) B1909697
theorem B1273143 : Blo 1271954 1273143 := bstep (se 1 (by rfl) ⟨954857, by rfl⟩ : syracuseStep 1273143 = 1909715) B1909715
theorem B1273163 : Blo 1271954 1273163 := bstep (se 1 (by rfl) ⟨954872, by rfl⟩ : syracuseStep 1273163 = 1909745) B1909745
theorem B1273175 : Blo 1271954 1273175 := bstep (se 1 (by rfl) ⟨954881, by rfl⟩ : syracuseStep 1273175 = 1909763) B1909763
theorem B1273195 : Blo 1271954 1273195 := bstep (se 1 (by rfl) ⟨954896, by rfl⟩ : syracuseStep 1273195 = 1909793) B1909793
theorem B1273207 : Blo 1271954 1273207 := bstep (se 1 (by rfl) ⟨954905, by rfl⟩ : syracuseStep 1273207 = 1909811) B1909811
theorem B1273227 : Blo 1271954 1273227 := bstep (se 1 (by rfl) ⟨954920, by rfl⟩ : syracuseStep 1273227 = 1909841) B1909841
theorem B120860045 : Blo 1271954 120860045 := bstep (se 3 (by rfl) ⟨22661258, by rfl⟩ : syracuseStep 120860045 = 45322517) B45322517
theorem B1273239 : Blo 1271954 1273239 := bstep (se 1 (by rfl) ⟨954929, by rfl⟩ : syracuseStep 1273239 = 1909859) B1909859
theorem B1273259 : Blo 1271954 1273259 := bstep (se 1 (by rfl) ⟨954944, by rfl⟩ : syracuseStep 1273259 = 1909889) B1909889
theorem B1273271 : Blo 1271954 1273271 := bstep (se 1 (by rfl) ⟨954953, by rfl⟩ : syracuseStep 1273271 = 1909907) B1909907
theorem B2862539 : Blo 1271954 2862539 := bstep (se 1 (by rfl) ⟨2146904, by rfl⟩ : syracuseStep 2862539 = 4293809) B4293809
theorem B1273291 : Blo 1271954 1273291 := bstep (se 1 (by rfl) ⟨954968, by rfl⟩ : syracuseStep 1273291 = 1909937) B1909937
theorem B1273303 : Blo 1271954 1273303 := bstep (se 1 (by rfl) ⟨954977, by rfl⟩ : syracuseStep 1273303 = 1909955) B1909955
theorem B1273323 : Blo 1271954 1273323 := bstep (se 1 (by rfl) ⟨954992, by rfl⟩ : syracuseStep 1273323 = 1909985) B1909985
theorem B1273335 : Blo 1271954 1273335 := bstep (se 1 (by rfl) ⟨955001, by rfl⟩ : syracuseStep 1273335 = 1910003) B1910003
theorem B2862593 : Blo 1271954 2862593 := bstep (se 2 (by rfl) ⟨1073472, by rfl⟩ : syracuseStep 2862593 = 2146945) B2146945
theorem B1273355 : Blo 1271954 1273355 := bstep (se 1 (by rfl) ⟨955016, by rfl⟩ : syracuseStep 1273355 = 1910033) B1910033
theorem B1273367 : Blo 1271954 1273367 := bstep (se 1 (by rfl) ⟨955025, by rfl⟩ : syracuseStep 1273367 = 1910051) B1910051
theorem B1273387 : Blo 1271954 1273387 := bstep (se 1 (by rfl) ⟨955040, by rfl⟩ : syracuseStep 1273387 = 1910081) B1910081
theorem B3223091 : Blo 1271954 3223091 := bstep (se 1 (by rfl) ⟨2417318, by rfl⟩ : syracuseStep 3223091 = 4834637) B4834637
theorem B1273399 : Blo 1271954 1273399 := bstep (se 1 (by rfl) ⟨955049, by rfl⟩ : syracuseStep 1273399 = 1910099) B1910099
theorem B1273419 : Blo 1271954 1273419 := bstep (se 1 (by rfl) ⟨955064, by rfl⟩ : syracuseStep 1273419 = 1910129) B1910129
theorem B1273431 : Blo 1271954 1273431 := bstep (se 1 (by rfl) ⟨955073, by rfl⟩ : syracuseStep 1273431 = 1910147) B1910147
theorem B1273451 : Blo 1271954 1273451 := bstep (se 1 (by rfl) ⟨955088, by rfl⟩ : syracuseStep 1273451 = 1910177) B1910177
theorem B1273463 : Blo 1271954 1273463 := bstep (se 1 (by rfl) ⟨955097, by rfl⟩ : syracuseStep 1273463 = 1910195) B1910195
theorem B4591235 : Blo 1271954 4591235 := bstep (se 1 (by rfl) ⟨3443426, by rfl⟩ : syracuseStep 4591235 = 6886853) B6886853
theorem B1273483 : Blo 1271954 1273483 := bstep (se 1 (by rfl) ⟨955112, by rfl⟩ : syracuseStep 1273483 = 1910225) B1910225
theorem B1273495 : Blo 1271954 1273495 := bstep (se 1 (by rfl) ⟨955121, by rfl⟩ : syracuseStep 1273495 = 1910243) B1910243
theorem B1273515 : Blo 1271954 1273515 := bstep (se 1 (by rfl) ⟨955136, by rfl⟩ : syracuseStep 1273515 = 1910273) B1910273
theorem B1273527 : Blo 1271954 1273527 := bstep (se 1 (by rfl) ⟨955145, by rfl⟩ : syracuseStep 1273527 = 1910291) B1910291
theorem B4075201 : Blo 1271954 4075201 := bstep (se 2 (by rfl) ⟨1528200, by rfl⟩ : syracuseStep 4075201 = 3056401) B3056401
theorem B1273547 : Blo 1271954 1273547 := bstep (se 1 (by rfl) ⟨955160, by rfl⟩ : syracuseStep 1273547 = 1910321) B1910321
theorem B1273559 : Blo 1271954 1273559 := bstep (se 1 (by rfl) ⟨955169, by rfl⟩ : syracuseStep 1273559 = 1910339) B1910339
theorem B2862809 : Blo 1271954 2862809 := bstep (se 2 (by rfl) ⟨1073553, by rfl⟩ : syracuseStep 2862809 = 2147107) B2147107
theorem B1273579 : Blo 1271954 1273579 := bstep (se 1 (by rfl) ⟨955184, by rfl⟩ : syracuseStep 1273579 = 1910369) B1910369
theorem B1273591 : Blo 1271954 1273591 := bstep (se 1 (by rfl) ⟨955193, by rfl⟩ : syracuseStep 1273591 = 1910387) B1910387
theorem B1273611 : Blo 1271954 1273611 := bstep (se 1 (by rfl) ⟨955208, by rfl⟩ : syracuseStep 1273611 = 1910417) B1910417
theorem B1273623 : Blo 1271954 1273623 := bstep (se 1 (by rfl) ⟨955217, by rfl⟩ : syracuseStep 1273623 = 1910435) B1910435
theorem B1273643 : Blo 1271954 1273643 := bstep (se 1 (by rfl) ⟨955232, by rfl⟩ : syracuseStep 1273643 = 1910465) B1910465
theorem B2862899 : Blo 1271954 2862899 := bstep (se 1 (by rfl) ⟨2147174, by rfl⟩ : syracuseStep 2862899 = 4294349) B4294349
theorem B4714291 : Blo 1271954 4714291 := bstep (se 1 (by rfl) ⟨3535718, by rfl⟩ : syracuseStep 4714291 = 7071437) B7071437
theorem B1273655 : Blo 1271954 1273655 := bstep (se 1 (by rfl) ⟨955241, by rfl⟩ : syracuseStep 1273655 = 1910483) B1910483
theorem B1273675 : Blo 1271954 1273675 := bstep (se 1 (by rfl) ⟨955256, by rfl⟩ : syracuseStep 1273675 = 1910513) B1910513
theorem B2862935 : Blo 1271954 2862935 := bstep (se 1 (by rfl) ⟨2147201, by rfl⟩ : syracuseStep 2862935 = 4294403) B4294403
theorem B1273687 : Blo 1271954 1273687 := bstep (se 1 (by rfl) ⟨955265, by rfl⟩ : syracuseStep 1273687 = 1910531) B1910531
theorem B3059545 : Blo 1271954 3059545 := bstep (se 2 (by rfl) ⟨1147329, by rfl⟩ : syracuseStep 3059545 = 2294659) B2294659
theorem B3223385 : Blo 1271954 3223385 := bstep (se 2 (by rfl) ⟨1208769, by rfl⟩ : syracuseStep 3223385 = 2417539) B2417539
theorem B1273707 : Blo 1271954 1273707 := bstep (se 1 (by rfl) ⟨955280, by rfl⟩ : syracuseStep 1273707 = 1910561) B1910561
theorem B1273719 : Blo 1271954 1273719 := bstep (se 1 (by rfl) ⟨955289, by rfl⟩ : syracuseStep 1273719 = 1910579) B1910579
theorem B1273739 : Blo 1271954 1273739 := bstep (se 1 (by rfl) ⟨955304, by rfl⟩ : syracuseStep 1273739 = 1910609) B1910609
theorem B1273751 : Blo 1271954 1273751 := bstep (se 1 (by rfl) ⟨955313, by rfl⟩ : syracuseStep 1273751 = 1910627) B1910627
theorem B1273771 : Blo 1271954 1273771 := bstep (se 1 (by rfl) ⟨955328, by rfl⟩ : syracuseStep 1273771 = 1910657) B1910657
theorem B1273783 : Blo 1271954 1273783 := bstep (se 1 (by rfl) ⟨955337, by rfl⟩ : syracuseStep 1273783 = 1910675) B1910675
theorem B3624907 : Blo 1271954 3624907 := bstep (se 1 (by rfl) ⟨2718680, by rfl⟩ : syracuseStep 3624907 = 5437361) B5437361
theorem B1273803 : Blo 1271954 1273803 := bstep (se 1 (by rfl) ⟨955352, by rfl⟩ : syracuseStep 1273803 = 1910705) B1910705
theorem B1273815 : Blo 1271954 1273815 := bstep (se 1 (by rfl) ⟨955361, by rfl⟩ : syracuseStep 1273815 = 1910723) B1910723
theorem B1273835 : Blo 1271954 1273835 := bstep (se 1 (by rfl) ⟨955376, by rfl⟩ : syracuseStep 1273835 = 1910753) B1910753
theorem B1273847 : Blo 1271954 1273847 := bstep (se 1 (by rfl) ⟨955385, by rfl⟩ : syracuseStep 1273847 = 1910771) B1910771
theorem B5165059 : Blo 1271954 5165059 := bstep (se 1 (by rfl) ⟨3873794, by rfl⟩ : syracuseStep 5165059 = 7747589) B7747589
theorem B2863115 : Blo 1271954 2863115 := bstep (se 1 (by rfl) ⟨2147336, by rfl⟩ : syracuseStep 2863115 = 4294673) B4294673
theorem B1273867 : Blo 1271954 1273867 := bstep (se 1 (by rfl) ⟨955400, by rfl⟩ : syracuseStep 1273867 = 1910801) B1910801
theorem B1273879 : Blo 1271954 1273879 := bstep (se 1 (by rfl) ⟨955409, by rfl⟩ : syracuseStep 1273879 = 1910819) B1910819
theorem B1273899 : Blo 1271954 1273899 := bstep (se 1 (by rfl) ⟨955424, by rfl⟩ : syracuseStep 1273899 = 1910849) B1910849
theorem B1273911 : Blo 1271954 1273911 := bstep (se 1 (by rfl) ⟨955433, by rfl⟩ : syracuseStep 1273911 = 1910867) B1910867
theorem B2863169 : Blo 1271954 2863169 := bstep (se 2 (by rfl) ⟨1073688, by rfl⟩ : syracuseStep 2863169 = 2147377) B2147377
theorem B4296779 : Blo 1271954 4296779 := bstep (se 1 (by rfl) ⟨3222584, by rfl⟩ : syracuseStep 4296779 = 6445169) B6445169
theorem B1273931 : Blo 1271954 1273931 := bstep (se 1 (by rfl) ⟨955448, by rfl⟩ : syracuseStep 1273931 = 1910897) B1910897
theorem B1273943 : Blo 1271954 1273943 := bstep (se 1 (by rfl) ⟨955457, by rfl⟩ : syracuseStep 1273943 = 1910915) B1910915
theorem B5435585 : Blo 1271954 5435585 := bstep (se 2 (by rfl) ⟨2038344, by rfl⟩ : syracuseStep 5435585 = 4076689) B4076689
theorem B6443225 : Blo 1271954 6443225 := bstep (se 2 (by rfl) ⟨2416209, by rfl⟩ : syracuseStep 6443225 = 4832419) B4832419
theorem B3625181 : Blo 1271954 3625181 := bstep (se 3 (by rfl) ⟨679721, by rfl⟩ : syracuseStep 3625181 = 1359443) B1359443
theorem B2863385 : Blo 1271954 2863385 := bstep (se 2 (by rfl) ⟨1073769, by rfl⟩ : syracuseStep 2863385 = 2147539) B2147539
theorem B4297049 : Blo 1271954 4297049 := bstep (se 2 (by rfl) ⟨1611393, by rfl⟩ : syracuseStep 4297049 = 3222787) B3222787
theorem B7352677 : Blo 1271954 7352677 := bstep (se 4 (by rfl) ⟨689313, by rfl⟩ : syracuseStep 7352677 = 1378627) B1378627
theorem B2863475 : Blo 1271954 2863475 := bstep (se 1 (by rfl) ⟨2147606, by rfl⟩ : syracuseStep 2863475 = 4295213) B4295213
theorem B2863511 : Blo 1271954 2863511 := bstep (se 1 (by rfl) ⟨2147633, by rfl⟩ : syracuseStep 2863511 = 4295267) B4295267
theorem B6115763 : Blo 1271954 6115763 := bstep (se 1 (by rfl) ⟨4586822, by rfl⟩ : syracuseStep 6115763 = 9173645) B9173645
theorem B5157323 : Blo 1271954 5157323 := bstep (se 1 (by rfl) ⟨3867992, by rfl⟩ : syracuseStep 5157323 = 7735985) B7735985
theorem B3625523 : Blo 1271954 3625523 := bstep (se 1 (by rfl) ⟨2719142, by rfl⟩ : syracuseStep 3625523 = 5438285) B5438285
theorem B22057541 : Blo 1271954 22057541 := bstep (se 4 (by rfl) ⟨2067894, by rfl⟩ : syracuseStep 22057541 = 4135789) B4135789
theorem B2863691 : Blo 1271954 2863691 := bstep (se 1 (by rfl) ⟨2147768, by rfl⟩ : syracuseStep 2863691 = 4295537) B4295537
theorem B2863745 : Blo 1271954 2863745 := bstep (se 2 (by rfl) ⟨1073904, by rfl⟩ : syracuseStep 2863745 = 2147809) B2147809
theorem B5804723 : Blo 1271954 5804723 := bstep (se 1 (by rfl) ⟨4353542, by rfl⟩ : syracuseStep 5804723 = 8707085) B8707085
theorem B7344857 : Blo 1271954 7344857 := bstep (se 2 (by rfl) ⟨2754321, by rfl⟩ : syracuseStep 7344857 = 5508643) B5508643
theorem B4829975 : Blo 1271954 4829975 := bstep (se 1 (by rfl) ⟨3622481, by rfl⟩ : syracuseStep 4829975 = 7244963) B7244963
theorem B2863961 : Blo 1271954 2863961 := bstep (se 2 (by rfl) ⟨1073985, by rfl⟩ : syracuseStep 2863961 = 2147971) B2147971
theorem B4076381 : Blo 1271954 4076381 := bstep (se 3 (by rfl) ⟨764321, by rfl⟩ : syracuseStep 4076381 = 1528643) B1528643
theorem B2864051 : Blo 1271954 2864051 := bstep (se 1 (by rfl) ⟨2148038, by rfl⟩ : syracuseStep 2864051 = 4296077) B4296077
theorem B2864087 : Blo 1271954 2864087 := bstep (se 1 (by rfl) ⟨2148065, by rfl⟩ : syracuseStep 2864087 = 4296131) B4296131
theorem B5805017 : Blo 1271954 5805017 := bstep (se 2 (by rfl) ⟨2176881, by rfl⟩ : syracuseStep 5805017 = 4353763) B4353763
theorem B4297751 : Blo 1271954 4297751 := bstep (se 1 (by rfl) ⟨3223313, by rfl⟩ : syracuseStep 4297751 = 6446627) B6446627
theorem B6116417 : Blo 1271954 6116417 := bstep (se 2 (by rfl) ⟨2293656, by rfl⟩ : syracuseStep 6116417 = 4587313) B4587313
theorem B2864267 : Blo 1271954 2864267 := bstep (se 1 (by rfl) ⟨2148200, by rfl⟩ : syracuseStep 2864267 = 4296401) B4296401
theorem B2864321 : Blo 1271954 2864321 := bstep (se 2 (by rfl) ⟨1074120, by rfl⟩ : syracuseStep 2864321 = 2148241) B2148241
theorem B3060929 : Blo 1271954 3060929 := bstep (se 2 (by rfl) ⟨1147848, by rfl⟩ : syracuseStep 3060929 = 2295697) B2295697
theorem B9671885 : Blo 1271954 9671885 := bstep (se 3 (by rfl) ⟨1813478, by rfl⟩ : syracuseStep 9671885 = 3626957) B3626957
theorem B1611019 : Blo 1271954 1611019 := bstep (se 1 (by rfl) ⟨1208264, by rfl⟩ : syracuseStep 1611019 = 2416529) B2416529
theorem B7746833 : Blo 1271954 7746833 := bstep (se 2 (by rfl) ⟨2905062, by rfl⟩ : syracuseStep 7746833 = 5810125) B5810125
theorem B2864537 : Blo 1271954 2864537 := bstep (se 2 (by rfl) ⟨1074201, by rfl⟩ : syracuseStep 2864537 = 2148403) B2148403
theorem B2864627 : Blo 1271954 2864627 := bstep (se 1 (by rfl) ⟨2148470, by rfl⟩ : syracuseStep 2864627 = 4296941) B4296941
theorem B1431031 : Blo 1271954 1431031 := bstep (se 1 (by rfl) ⟨1073273, by rfl⟩ : syracuseStep 1431031 = 2146547) B2146547
theorem B16307729 : Blo 1271954 16307729 := bstep (se 2 (by rfl) ⟨6115398, by rfl⟩ : syracuseStep 16307729 = 12230797) B12230797
theorem B2864663 : Blo 1271954 2864663 := bstep (se 1 (by rfl) ⟨2148497, by rfl⟩ : syracuseStep 2864663 = 4296995) B4296995
theorem B4298291 : Blo 1271954 4298291 := bstep (se 1 (by rfl) ⟨3223718, by rfl⟩ : syracuseStep 4298291 = 6447437) B6447437
theorem B1570379 : Blo 1271954 1570379 := bstep (se 1 (by rfl) ⟨1177784, by rfl⟩ : syracuseStep 1570379 = 2355569) B2355569
theorem B5437003 : Blo 1271954 5437003 := bstep (se 1 (by rfl) ⟨4077752, by rfl⟩ : syracuseStep 5437003 = 8155505) B8155505
theorem B1431211 : Blo 1271954 1431211 := bstep (se 1 (by rfl) ⟨1073408, by rfl⟩ : syracuseStep 1431211 = 2146817) B2146817
theorem B9672371 : Blo 1271954 9672371 := bstep (se 1 (by rfl) ⟨7254278, by rfl⟩ : syracuseStep 9672371 = 14508557) B14508557
theorem B2864843 : Blo 1271954 2864843 := bstep (se 1 (by rfl) ⟨2148632, by rfl⟩ : syracuseStep 2864843 = 4297265) B4297265
theorem B9795289 : Blo 1271954 9795289 := bstep (se 2 (by rfl) ⟨3673233, by rfl⟩ : syracuseStep 9795289 = 7346467) B7346467
theorem B2864897 : Blo 1271954 2864897 := bstep (se 2 (by rfl) ⟨1074336, by rfl⟩ : syracuseStep 2864897 = 2148673) B2148673
theorem B1431319 : Blo 1271954 1431319 := bstep (se 1 (by rfl) ⟨1073489, by rfl⟩ : syracuseStep 1431319 = 2146979) B2146979
theorem B1529623 : Blo 1271954 1529623 := bstep (se 1 (by rfl) ⟨1147217, by rfl⟩ : syracuseStep 1529623 = 2294435) B2294435
theorem B6444845 : Blo 1271954 6444845 := bstep (se 3 (by rfl) ⟨1208408, by rfl⟩ : syracuseStep 6444845 = 2416817) B2416817
theorem B4298561 : Blo 1271954 4298561 := bstep (se 2 (by rfl) ⟨1611960, by rfl⟩ : syracuseStep 4298561 = 3223921) B3223921
theorem B5437277 : Blo 1271954 5437277 := bstep (se 3 (by rfl) ⟨1019489, by rfl⟩ : syracuseStep 5437277 = 2038979) B2038979
theorem B1431499 : Blo 1271954 1431499 := bstep (se 1 (by rfl) ⟨1073624, by rfl⟩ : syracuseStep 1431499 = 2147249) B2147249
theorem B8157145 : Blo 1271954 8157145 := bstep (se 2 (by rfl) ⟨3058929, by rfl⟩ : syracuseStep 8157145 = 6117859) B6117859
theorem B2865113 : Blo 1271954 2865113 := bstep (se 2 (by rfl) ⟨1074417, by rfl⟩ : syracuseStep 2865113 = 2148835) B2148835
theorem B4831235 : Blo 1271954 4831235 := bstep (se 1 (by rfl) ⟨3623426, by rfl⟩ : syracuseStep 4831235 = 7246853) B7246853
theorem B2717707 : Blo 1271954 2717707 := bstep (se 1 (by rfl) ⟨2038280, by rfl⟩ : syracuseStep 2717707 = 4076561) B4076561
theorem B2865203 : Blo 1271954 2865203 := bstep (se 1 (by rfl) ⟨2148902, by rfl⟩ : syracuseStep 2865203 = 4297805) B4297805
theorem B1431607 : Blo 1271954 1431607 := bstep (se 1 (by rfl) ⟨1073705, by rfl⟩ : syracuseStep 1431607 = 2147411) B2147411
theorem B42432581 : Blo 1271954 42432581 := bstep (se 4 (by rfl) ⟨3978054, by rfl⟩ : syracuseStep 42432581 = 7956109) B7956109
theorem B2865239 : Blo 1271954 2865239 := bstep (se 1 (by rfl) ⟨2148929, by rfl⟩ : syracuseStep 2865239 = 4297859) B4297859
theorem B6879325 : Blo 1271954 6879325 := bstep (se 3 (by rfl) ⟨1289873, by rfl⟩ : syracuseStep 6879325 = 2579747) B2579747
theorem B1611991 : Blo 1271954 1611991 := bstep (se 1 (by rfl) ⟨1208993, by rfl⟩ : syracuseStep 1611991 = 2417987) B2417987
theorem B1431787 : Blo 1271954 1431787 := bstep (se 1 (by rfl) ⟨1073840, by rfl⟩ : syracuseStep 1431787 = 2147681) B2147681
theorem B2717963 : Blo 1271954 2717963 := bstep (se 1 (by rfl) ⟨2038472, by rfl⟩ : syracuseStep 2717963 = 4076945) B4076945
theorem B2865419 : Blo 1271954 2865419 := bstep (se 1 (by rfl) ⟨2149064, by rfl⟩ : syracuseStep 2865419 = 4298129) B4298129
theorem B2414873 : Blo 1271954 2414873 := bstep (se 2 (by rfl) ⟨905577, by rfl⟩ : syracuseStep 2414873 = 1811155) B1811155
theorem B2865473 : Blo 1271954 2865473 := bstep (se 2 (by rfl) ⟨1074552, by rfl⟩ : syracuseStep 2865473 = 2149105) B2149105
theorem B6117707 : Blo 1271954 6117707 := bstep (se 1 (by rfl) ⟨4588280, by rfl⟩ : syracuseStep 6117707 = 9176561) B9176561
theorem B1431895 : Blo 1271954 1431895 := bstep (se 1 (by rfl) ⟨1073921, by rfl⟩ : syracuseStep 1431895 = 2147843) B2147843
theorem B4299101 : Blo 1271954 4299101 := bstep (se 3 (by rfl) ⟨806081, by rfl⟩ : syracuseStep 4299101 = 1612163) B1612163
theorem B4585859 : Blo 1271954 4585859 := bstep (se 1 (by rfl) ⟨3439394, by rfl⟩ : syracuseStep 4585859 = 6878789) B6878789
theorem B1432075 : Blo 1271954 1432075 := bstep (se 1 (by rfl) ⟨1074056, by rfl⟩ : syracuseStep 1432075 = 2148113) B2148113
theorem B2578969 : Blo 1271954 2578969 := bstep (se 2 (by rfl) ⟨967113, by rfl⟩ : syracuseStep 2578969 = 1934227) B1934227
theorem B2865689 : Blo 1271954 2865689 := bstep (se 2 (by rfl) ⟨1074633, by rfl⟩ : syracuseStep 2865689 = 2149267) B2149267
theorem B3627595 : Blo 1271954 3627595 := bstep (se 1 (by rfl) ⟨2720696, by rfl⟩ : syracuseStep 3627595 = 5441393) B5441393
theorem B2865779 : Blo 1271954 2865779 := bstep (se 1 (by rfl) ⟨2149334, by rfl⟩ : syracuseStep 2865779 = 4298669) B4298669
theorem B1432183 : Blo 1271954 1432183 := bstep (se 1 (by rfl) ⟨1074137, by rfl⟩ : syracuseStep 1432183 = 2148275) B2148275
theorem B10877591 : Blo 1271954 10877591 := bstep (se 1 (by rfl) ⟨8158193, by rfl⟩ : syracuseStep 10877591 = 16316387) B16316387
theorem B2865815 : Blo 1271954 2865815 := bstep (se 1 (by rfl) ⟨2149361, by rfl⟩ : syracuseStep 2865815 = 4298723) B4298723
theorem B11606819 : Blo 1271954 11606819 := bstep (se 1 (by rfl) ⟨8705114, by rfl⟩ : syracuseStep 11606819 = 17410229) B17410229
theorem B1432363 : Blo 1271954 1432363 := bstep (se 1 (by rfl) ⟨1074272, by rfl⟩ : syracuseStep 1432363 = 2148545) B2148545
theorem B2865995 : Blo 1271954 2865995 := bstep (se 1 (by rfl) ⟨2149496, by rfl⟩ : syracuseStep 2865995 = 4298993) B4298993
theorem B2866049 : Blo 1271954 2866049 := bstep (se 2 (by rfl) ⟨1074768, by rfl⟩ : syracuseStep 2866049 = 2149537) B2149537
theorem B2415511 : Blo 1271954 2415511 := bstep (se 1 (by rfl) ⟨1811633, by rfl⟩ : syracuseStep 2415511 = 3623267) B3623267
theorem B1432471 : Blo 1271954 1432471 := bstep (se 1 (by rfl) ⟨1074353, by rfl⟩ : syracuseStep 1432471 = 2148707) B2148707
theorem B3439577 : Blo 1271954 3439577 := bstep (se 2 (by rfl) ⟨1289841, by rfl⟩ : syracuseStep 3439577 = 2579683) B2579683
theorem B1432651 : Blo 1271954 1432651 := bstep (se 1 (by rfl) ⟨1074488, by rfl⟩ : syracuseStep 1432651 = 2148977) B2148977
theorem B2866265 : Blo 1271954 2866265 := bstep (se 2 (by rfl) ⟨1074849, by rfl⟩ : syracuseStep 2866265 = 2149699) B2149699
theorem B9673829 : Blo 1271954 9673829 := bstep (se 4 (by rfl) ⟨906921, by rfl⟩ : syracuseStep 9673829 = 1813843) B1813843
theorem B2866355 : Blo 1271954 2866355 := bstep (se 1 (by rfl) ⟨2149766, by rfl⟩ : syracuseStep 2866355 = 4299533) B4299533
theorem B1432759 : Blo 1271954 1432759 := bstep (se 1 (by rfl) ⟨1074569, by rfl⟩ : syracuseStep 1432759 = 2149139) B2149139
theorem B2866391 : Blo 1271954 2866391 := bstep (se 1 (by rfl) ⟨2149793, by rfl⟩ : syracuseStep 2866391 = 4299587) B4299587
theorem B2718937 : Blo 1271954 2718937 := bstep (se 2 (by rfl) ⟨1019601, by rfl⟩ : syracuseStep 2718937 = 2039203) B2039203
theorem B23223557 : Blo 1271954 23223557 := bstep (se 4 (by rfl) ⟨2177208, by rfl⟩ : syracuseStep 23223557 = 4354417) B4354417
theorem B1359127 : Blo 1271954 1359127 := bstep (se 1 (by rfl) ⟨1019345, by rfl⟩ : syracuseStep 1359127 = 2038691) B2038691
theorem B1907993 : Blo 1271954 1907993 := bstep (se 2 (by rfl) ⟨715497, by rfl⟩ : syracuseStep 1907993 = 1430995) B1430995
theorem B1432939 : Blo 1271954 1432939 := bstep (se 1 (by rfl) ⟨1074704, by rfl⟩ : syracuseStep 1432939 = 2149409) B2149409
theorem B2719091 : Blo 1271954 2719091 := bstep (se 1 (by rfl) ⟨2039318, by rfl⟩ : syracuseStep 2719091 = 4078637) B4078637
theorem B1908107 : Blo 1271954 1908107 := bstep (se 1 (by rfl) ⟨1431080, by rfl⟩ : syracuseStep 1908107 = 2862161) B2862161
theorem B1908119 : Blo 1271954 1908119 := bstep (se 1 (by rfl) ⟨1431089, by rfl⟩ : syracuseStep 1908119 = 2862179) B2862179
theorem B2293195 : Blo 1271954 2293195 := bstep (se 1 (by rfl) ⟨1719896, by rfl⟩ : syracuseStep 2293195 = 3439793) B3439793
theorem B61971925 : Blo 1271954 61971925 := bstep (se 7 (by rfl) ⟨726233, by rfl⟩ : syracuseStep 61971925 = 1452467) B1452467
theorem B1433047 : Blo 1271954 1433047 := bstep (se 1 (by rfl) ⟨1074785, by rfl⟩ : syracuseStep 1433047 = 2149571) B2149571
theorem B1908185 : Blo 1271954 1908185 := bstep (se 2 (by rfl) ⟨715569, by rfl⟩ : syracuseStep 1908185 = 1431139) B1431139
theorem B9666053 : Blo 1271954 9666053 := bstep (se 4 (by rfl) ⟨906192, by rfl⟩ : syracuseStep 9666053 = 1812385) B1812385
theorem B1908299 : Blo 1271954 1908299 := bstep (se 1 (by rfl) ⟨1431224, by rfl⟩ : syracuseStep 1908299 = 2862449) B2862449
theorem B1908311 : Blo 1271954 1908311 := bstep (se 1 (by rfl) ⟨1431233, by rfl⟩ : syracuseStep 1908311 = 2862467) B2862467
theorem B2481779 : Blo 1271954 2481779 := bstep (se 1 (by rfl) ⟨1861334, by rfl⟩ : syracuseStep 2481779 = 3722669) B3722669
theorem B4587139 : Blo 1271954 4587139 := bstep (se 1 (by rfl) ⟨3440354, by rfl⟩ : syracuseStep 4587139 = 6880709) B6880709
theorem B1908377 : Blo 1271954 1908377 := bstep (se 2 (by rfl) ⟨715641, by rfl⟩ : syracuseStep 1908377 = 1431283) B1431283
theorem B2293427 : Blo 1271954 2293427 := bstep (se 1 (by rfl) ⟨1720070, by rfl⟩ : syracuseStep 2293427 = 3440141) B3440141
theorem B2416331 : Blo 1271954 2416331 := bstep (se 1 (by rfl) ⟨1812248, by rfl⟩ : syracuseStep 2416331 = 3624497) B3624497
theorem B2416385 : Blo 1271954 2416385 := bstep (se 2 (by rfl) ⟨906144, by rfl⟩ : syracuseStep 2416385 = 1812289) B1812289
theorem B1908491 : Blo 1271954 1908491 := bstep (se 1 (by rfl) ⟨1431368, by rfl⟩ : syracuseStep 1908491 = 2862737) B2862737
theorem B6119185 : Blo 1271954 6119185 := bstep (se 2 (by rfl) ⟨2294694, by rfl⟩ : syracuseStep 6119185 = 4589389) B4589389
theorem B1908503 : Blo 1271954 1908503 := bstep (se 1 (by rfl) ⟨1431377, by rfl⟩ : syracuseStep 1908503 = 2862755) B2862755
theorem B2039575 : Blo 1271954 2039575 := bstep (se 1 (by rfl) ⟨1529681, by rfl⟩ : syracuseStep 2039575 = 3059363) B3059363
theorem B1908569 : Blo 1271954 1908569 := bstep (se 2 (by rfl) ⟨715713, by rfl⟩ : syracuseStep 1908569 = 1431427) B1431427
theorem B2719603 : Blo 1271954 2719603 := bstep (se 1 (by rfl) ⟨2039702, by rfl⟩ : syracuseStep 2719603 = 4079405) B4079405
theorem B10321843 : Blo 1271954 10321843 := bstep (se 1 (by rfl) ⟨7741382, by rfl⟩ : syracuseStep 10321843 = 15482765) B15482765
theorem B1908683 : Blo 1271954 1908683 := bstep (se 1 (by rfl) ⟨1431512, by rfl⟩ : syracuseStep 1908683 = 2863025) B2863025
theorem B1908695 : Blo 1271954 1908695 := bstep (se 1 (by rfl) ⟨1431521, by rfl⟩ : syracuseStep 1908695 = 2863043) B2863043
theorem B1908743 : Blo 1271954 1908743 := bstep (se 1 (by rfl) ⟨1431557, by rfl⟩ : syracuseStep 1908743 = 2863115) B2863115
theorem B1359887 : Blo 1271954 1359887 := bstep (se 1 (by rfl) ⟨1019915, by rfl⟩ : syracuseStep 1359887 = 2039831) B2039831
theorem B1908779 : Blo 1271954 1908779 := bstep (se 1 (by rfl) ⟨1431584, by rfl⟩ : syracuseStep 1908779 = 2863169) B2863169
theorem B1908809 : Blo 1271954 1908809 := bstep (se 2 (by rfl) ⟨715803, by rfl⟩ : syracuseStep 1908809 = 1431607) B1431607
theorem B2146439 : Blo 1271954 2146439 := bstep (se 1 (by rfl) ⟨1609829, by rfl⟩ : syracuseStep 2146439 = 3219659) B3219659
theorem B2416787 : Blo 1271954 2416787 := bstep (se 1 (by rfl) ⟨1812590, by rfl⟩ : syracuseStep 2416787 = 3625181) B3625181
theorem B1908923 : Blo 1271954 1908923 := bstep (se 1 (by rfl) ⟨1431692, by rfl⟩ : syracuseStep 1908923 = 2863385) B2863385
theorem B1908983 : Blo 1271954 1908983 := bstep (se 1 (by rfl) ⟨1431737, by rfl⟩ : syracuseStep 1908983 = 2863475) B2863475
theorem B1909007 : Blo 1271954 1909007 := bstep (se 1 (by rfl) ⟨1431755, by rfl⟩ : syracuseStep 1909007 = 2863511) B2863511
theorem B1909049 : Blo 1271954 1909049 := bstep (se 2 (by rfl) ⟨715893, by rfl⟩ : syracuseStep 1909049 = 1431787) B1431787
theorem B3440983 : Blo 1271954 3440983 := bstep (se 1 (by rfl) ⟨2580737, by rfl⟩ : syracuseStep 3440983 = 5161475) B5161475
theorem B2417015 : Blo 1271954 2417015 := bstep (se 1 (by rfl) ⟨1812761, by rfl⟩ : syracuseStep 2417015 = 3625523) B3625523
theorem B14705027 : Blo 1271954 14705027 := bstep (se 1 (by rfl) ⟨11028770, by rfl⟩ : syracuseStep 14705027 = 22057541) B22057541
theorem B4292999 : Blo 1271954 4292999 := bstep (se 1 (by rfl) ⟨3219749, by rfl⟩ : syracuseStep 4292999 = 6439499) B6439499
theorem B1909127 : Blo 1271954 1909127 := bstep (se 1 (by rfl) ⟨1431845, by rfl⟩ : syracuseStep 1909127 = 2863691) B2863691
theorem B1909163 : Blo 1271954 1909163 := bstep (se 1 (by rfl) ⟨1431872, by rfl⟩ : syracuseStep 1909163 = 2863745) B2863745
theorem B1909193 : Blo 1271954 1909193 := bstep (se 2 (by rfl) ⟨715947, by rfl⟩ : syracuseStep 1909193 = 1431895) B1431895
theorem B9667025 : Blo 1271954 9667025 := bstep (se 2 (by rfl) ⟨3625134, by rfl⟩ : syracuseStep 9667025 = 7250269) B7250269
theorem B3219983 : Blo 1271954 3219983 := bstep (se 1 (by rfl) ⟨2414987, by rfl⟩ : syracuseStep 3219983 = 4829975) B4829975
theorem B1909307 : Blo 1271954 1909307 := bstep (se 1 (by rfl) ⟨1431980, by rfl⟩ : syracuseStep 1909307 = 2863961) B2863961
theorem B5440061 : Blo 1271954 5440061 := bstep (se 3 (by rfl) ⟨1020011, by rfl⟩ : syracuseStep 5440061 = 2040023) B2040023
theorem B1909367 : Blo 1271954 1909367 := bstep (se 1 (by rfl) ⟨1432025, by rfl⟩ : syracuseStep 1909367 = 2864051) B2864051
theorem B1909391 : Blo 1271954 1909391 := bstep (se 1 (by rfl) ⟨1432043, by rfl⟩ : syracuseStep 1909391 = 2864087) B2864087
theorem B1909433 : Blo 1271954 1909433 := bstep (se 2 (by rfl) ⟨716037, by rfl⟩ : syracuseStep 1909433 = 1432075) B1432075
theorem B2720441 : Blo 1271954 2720441 := bstep (se 2 (by rfl) ⟨1020165, by rfl⟩ : syracuseStep 2720441 = 2040331) B2040331
theorem B6439661 : Blo 1271954 6439661 := bstep (se 3 (by rfl) ⟨1207436, by rfl⟩ : syracuseStep 6439661 = 2414873) B2414873
theorem B4293377 : Blo 1271954 4293377 := bstep (se 2 (by rfl) ⟨1610016, by rfl⟩ : syracuseStep 4293377 = 3220033) B3220033
theorem B1909511 : Blo 1271954 1909511 := bstep (se 1 (by rfl) ⟨1432133, by rfl⟩ : syracuseStep 1909511 = 2864267) B2864267
theorem B2147087 : Blo 1271954 2147087 := bstep (se 1 (by rfl) ⟨1610315, by rfl⟩ : syracuseStep 2147087 = 3220631) B3220631
theorem B1909547 : Blo 1271954 1909547 := bstep (se 1 (by rfl) ⟨1432160, by rfl⟩ : syracuseStep 1909547 = 2864321) B2864321
theorem B6447923 : Blo 1271954 6447923 := bstep (se 1 (by rfl) ⟨4835942, by rfl⟩ : syracuseStep 6447923 = 9671885) B9671885
theorem B1909577 : Blo 1271954 1909577 := bstep (se 2 (by rfl) ⟨716091, by rfl⟩ : syracuseStep 1909577 = 1432183) B1432183
theorem B1909691 : Blo 1271954 1909691 := bstep (se 1 (by rfl) ⟨1432268, by rfl⟩ : syracuseStep 1909691 = 2864537) B2864537
theorem B1909751 : Blo 1271954 1909751 := bstep (se 1 (by rfl) ⟨1432313, by rfl⟩ : syracuseStep 1909751 = 2864627) B2864627
theorem B21734405 : Blo 1271954 21734405 := bstep (se 4 (by rfl) ⟨2037600, by rfl⟩ : syracuseStep 21734405 = 4075201) B4075201
theorem B10871819 : Blo 1271954 10871819 := bstep (se 1 (by rfl) ⟨8153864, by rfl⟩ : syracuseStep 10871819 = 16307729) B16307729
theorem B1909775 : Blo 1271954 1909775 := bstep (se 1 (by rfl) ⟨1432331, by rfl⟩ : syracuseStep 1909775 = 2864663) B2864663
theorem B2720783 : Blo 1271954 2720783 := bstep (se 1 (by rfl) ⟨2040587, by rfl⟩ : syracuseStep 2720783 = 4081175) B4081175
theorem B1909817 : Blo 1271954 1909817 := bstep (se 2 (by rfl) ⟨716181, by rfl⟩ : syracuseStep 1909817 = 1432363) B1432363
theorem B6448247 : Blo 1271954 6448247 := bstep (se 1 (by rfl) ⟨4836185, by rfl⟩ : syracuseStep 6448247 = 9672371) B9672371
theorem B1909895 : Blo 1271954 1909895 := bstep (se 1 (by rfl) ⟨1432421, by rfl⟩ : syracuseStep 1909895 = 2864843) B2864843
theorem B1909931 : Blo 1271954 1909931 := bstep (se 1 (by rfl) ⟨1432448, by rfl⟩ : syracuseStep 1909931 = 2864897) B2864897
theorem B3220681 : Blo 1271954 3220681 := bstep (se 2 (by rfl) ⟨1207755, by rfl⟩ : syracuseStep 3220681 = 2415511) B2415511
theorem B1909961 : Blo 1271954 1909961 := bstep (se 2 (by rfl) ⟨716235, by rfl⟩ : syracuseStep 1909961 = 1432471) B1432471
theorem B2147627 : Blo 1271954 2147627 := bstep (se 1 (by rfl) ⟨1610720, by rfl⟩ : syracuseStep 2147627 = 3221441) B3221441
theorem B1910075 : Blo 1271954 1910075 := bstep (se 1 (by rfl) ⟨1432556, by rfl⟩ : syracuseStep 1910075 = 2865113) B2865113
theorem B3220823 : Blo 1271954 3220823 := bstep (se 1 (by rfl) ⟨2415617, by rfl⟩ : syracuseStep 3220823 = 4831235) B4831235
theorem B1910135 : Blo 1271954 1910135 := bstep (se 1 (by rfl) ⟨1432601, by rfl⟩ : syracuseStep 1910135 = 2865203) B2865203
theorem B28288387 : Blo 1271954 28288387 := bstep (se 1 (by rfl) ⟨21216290, by rfl⟩ : syracuseStep 28288387 = 42432581) B42432581
theorem B1910159 : Blo 1271954 1910159 := bstep (se 1 (by rfl) ⟨1432619, by rfl⟩ : syracuseStep 1910159 = 2865239) B2865239
theorem B14501267 : Blo 1271954 14501267 := bstep (se 1 (by rfl) ⟨10875950, by rfl⟩ : syracuseStep 14501267 = 21751901) B21751901
theorem B1910201 : Blo 1271954 1910201 := bstep (se 2 (by rfl) ⟨716325, by rfl⟩ : syracuseStep 1910201 = 1432651) B1432651
theorem B1811975 : Blo 1271954 1811975 := bstep (se 1 (by rfl) ⟨1358981, by rfl⟩ : syracuseStep 1811975 = 2717963) B2717963
theorem B1910279 : Blo 1271954 1910279 := bstep (se 1 (by rfl) ⟨1432709, by rfl⟩ : syracuseStep 1910279 = 2865419) B2865419
theorem B6440471 : Blo 1271954 6440471 := bstep (se 1 (by rfl) ⟨4830353, by rfl⟩ : syracuseStep 6440471 = 9660707) B9660707
theorem B4294187 : Blo 1271954 4294187 := bstep (se 1 (by rfl) ⟨3220640, by rfl⟩ : syracuseStep 4294187 = 6441281) B6441281
theorem B1910315 : Blo 1271954 1910315 := bstep (se 1 (by rfl) ⟨1432736, by rfl⟩ : syracuseStep 1910315 = 2865473) B2865473
theorem B1910345 : Blo 1271954 1910345 := bstep (se 2 (by rfl) ⟨716379, by rfl⟩ : syracuseStep 1910345 = 1432759) B1432759
theorem B3057239 : Blo 1271954 3057239 := bstep (se 1 (by rfl) ⟨2292929, by rfl⟩ : syracuseStep 3057239 = 4585859) B4585859
theorem B2295415 : Blo 1271954 2295415 := bstep (se 1 (by rfl) ⟨1721561, by rfl⟩ : syracuseStep 2295415 = 3443123) B3443123
theorem B3671687 : Blo 1271954 3671687 := bstep (se 1 (by rfl) ⟨2753765, by rfl⟩ : syracuseStep 3671687 = 5507531) B5507531
theorem B1935019 : Blo 1271954 1935019 := bstep (se 1 (by rfl) ⟨1451264, by rfl⟩ : syracuseStep 1935019 = 2902529) B2902529
theorem B2148025 : Blo 1271954 2148025 := bstep (se 2 (by rfl) ⟨805509, by rfl⟩ : syracuseStep 2148025 = 1611019) B1611019
theorem B1910459 : Blo 1271954 1910459 := bstep (se 1 (by rfl) ⟨1432844, by rfl⟩ : syracuseStep 1910459 = 2865689) B2865689
theorem B1812169 : Blo 1271954 1812169 := bstep (se 2 (by rfl) ⟨679563, by rfl⟩ : syracuseStep 1812169 = 1359127) B1359127
theorem B1910519 : Blo 1271954 1910519 := bstep (se 1 (by rfl) ⟨1432889, by rfl⟩ : syracuseStep 1910519 = 2865779) B2865779
theorem B7251727 : Blo 1271954 7251727 := bstep (se 1 (by rfl) ⟨5438795, by rfl⟩ : syracuseStep 7251727 = 10877591) B10877591
theorem B1910543 : Blo 1271954 1910543 := bstep (se 1 (by rfl) ⟨1432907, by rfl⟩ : syracuseStep 1910543 = 2865815) B2865815
theorem B3442475 : Blo 1271954 3442475 := bstep (se 1 (by rfl) ⟨2581856, by rfl⟩ : syracuseStep 3442475 = 5163713) B5163713
theorem B29394737 : Blo 1271954 29394737 := bstep (se 2 (by rfl) ⟨11023026, by rfl⟩ : syracuseStep 29394737 = 22046053) B22046053
theorem B1910585 : Blo 1271954 1910585 := bstep (se 2 (by rfl) ⟨716469, by rfl⟩ : syracuseStep 1910585 = 1432939) B1432939
theorem B5162867 : Blo 1271954 5162867 := bstep (se 1 (by rfl) ⟨3872150, by rfl⟩ : syracuseStep 5162867 = 7744301) B7744301
theorem B1910663 : Blo 1271954 1910663 := bstep (se 1 (by rfl) ⟨1432997, by rfl⟩ : syracuseStep 1910663 = 2865995) B2865995
theorem B1910699 : Blo 1271954 1910699 := bstep (se 1 (by rfl) ⟨1433024, by rfl⟩ : syracuseStep 1910699 = 2866049) B2866049
theorem B3057593 : Blo 1271954 3057593 := bstep (se 2 (by rfl) ⟨1146597, by rfl⟩ : syracuseStep 3057593 = 2293195) B2293195
theorem B1910729 : Blo 1271954 1910729 := bstep (se 2 (by rfl) ⟨716523, by rfl⟩ : syracuseStep 1910729 = 1433047) B1433047
theorem B6113303 : Blo 1271954 6113303 := bstep (se 1 (by rfl) ⟨4584977, by rfl⟩ : syracuseStep 6113303 = 9169955) B9169955
theorem B1910843 : Blo 1271954 1910843 := bstep (se 1 (by rfl) ⟨1433132, by rfl⟩ : syracuseStep 1910843 = 2866265) B2866265
theorem B6449219 : Blo 1271954 6449219 := bstep (se 1 (by rfl) ⟨4836914, by rfl⟩ : syracuseStep 6449219 = 9673829) B9673829
theorem B30951517 : Blo 1271954 30951517 := bstep (se 3 (by rfl) ⟨5803409, by rfl⟩ : syracuseStep 30951517 = 11606819) B11606819
theorem B1910903 : Blo 1271954 1910903 := bstep (se 1 (by rfl) ⟨1433177, by rfl⟩ : syracuseStep 1910903 = 2866355) B2866355
theorem B1910927 : Blo 1271954 1910927 := bstep (se 1 (by rfl) ⟨1433195, by rfl⟩ : syracuseStep 1910927 = 2866391) B2866391
theorem B1271995 : Blo 1271954 1271995 := bstep (se 1 (by rfl) ⟨953996, by rfl⟩ : syracuseStep 1271995 = 1907993) B1907993
theorem B1812727 : Blo 1271954 1812727 := bstep (se 1 (by rfl) ⟨1359545, by rfl⟩ : syracuseStep 1812727 = 2719091) B2719091
theorem B1272071 : Blo 1271954 1272071 := bstep (se 1 (by rfl) ⟨954053, by rfl⟩ : syracuseStep 1272071 = 1908107) B1908107
theorem B1272079 : Blo 1271954 1272079 := bstep (se 1 (by rfl) ⟨954059, by rfl⟩ : syracuseStep 1272079 = 1908119) B1908119
theorem B13060385 : Blo 1271954 13060385 := bstep (se 2 (by rfl) ⟨4897644, by rfl⟩ : syracuseStep 13060385 = 9795289) B9795289
theorem B1272123 : Blo 1271954 1272123 := bstep (se 1 (by rfl) ⟨954092, by rfl⟩ : syracuseStep 1272123 = 1908185) B1908185
theorem B2148727 : Blo 1271954 2148727 := bstep (se 1 (by rfl) ⟨1611545, by rfl⟩ : syracuseStep 2148727 = 3223091) B3223091
theorem B1272199 : Blo 1271954 1272199 := bstep (se 1 (by rfl) ⟨954149, by rfl⟩ : syracuseStep 1272199 = 1908299) B1908299
theorem B1272207 : Blo 1271954 1272207 := bstep (se 1 (by rfl) ⟨954155, by rfl⟩ : syracuseStep 1272207 = 1908311) B1908311
theorem B6285721 : Blo 1271954 6285721 := bstep (se 2 (by rfl) ⟨2357145, by rfl⟩ : syracuseStep 6285721 = 4714291) B4714291
theorem B1272251 : Blo 1271954 1272251 := bstep (se 1 (by rfl) ⟨954188, by rfl⟩ : syracuseStep 1272251 = 1908377) B1908377
theorem B1272327 : Blo 1271954 1272327 := bstep (se 1 (by rfl) ⟨954245, by rfl⟩ : syracuseStep 1272327 = 1908491) B1908491
theorem B1272335 : Blo 1271954 1272335 := bstep (se 1 (by rfl) ⟨954251, by rfl⟩ : syracuseStep 1272335 = 1908503) B1908503
theorem B1272379 : Blo 1271954 1272379 := bstep (se 1 (by rfl) ⟨954284, by rfl⟩ : syracuseStep 1272379 = 1908569) B1908569
theorem B2148923 : Blo 1271954 2148923 := bstep (se 1 (by rfl) ⟨1611692, by rfl⟩ : syracuseStep 2148923 = 3223385) B3223385
theorem B1272455 : Blo 1271954 1272455 := bstep (se 1 (by rfl) ⟨954341, by rfl⟩ : syracuseStep 1272455 = 1908683) B1908683
theorem B1272463 : Blo 1271954 1272463 := bstep (se 1 (by rfl) ⟨954347, by rfl⟩ : syracuseStep 1272463 = 1908695) B1908695
theorem B3623609 : Blo 1271954 3623609 := bstep (se 2 (by rfl) ⟨1358853, by rfl⟩ : syracuseStep 3623609 = 2717707) B2717707
theorem B1272507 : Blo 1271954 1272507 := bstep (se 1 (by rfl) ⟨954380, by rfl⟩ : syracuseStep 1272507 = 1908761) B1908761
theorem B1272583 : Blo 1271954 1272583 := bstep (se 1 (by rfl) ⟨954437, by rfl⟩ : syracuseStep 1272583 = 1908875) B1908875
theorem B1272591 : Blo 1271954 1272591 := bstep (se 1 (by rfl) ⟨954443, by rfl⟩ : syracuseStep 1272591 = 1908887) B1908887
theorem B3623723 : Blo 1271954 3623723 := bstep (se 1 (by rfl) ⟨2717792, by rfl⟩ : syracuseStep 3623723 = 5435585) B5435585
theorem B1272635 : Blo 1271954 1272635 := bstep (se 1 (by rfl) ⟨954476, by rfl⟩ : syracuseStep 1272635 = 1908953) B1908953
theorem B4295483 : Blo 1271954 4295483 := bstep (se 1 (by rfl) ⟨3221612, by rfl⟩ : syracuseStep 4295483 = 6443225) B6443225
theorem B9300851 : Blo 1271954 9300851 := bstep (se 1 (by rfl) ⟨6975638, by rfl⟩ : syracuseStep 9300851 = 13951277) B13951277
theorem B8711027 : Blo 1271954 8711027 := bstep (se 1 (by rfl) ⟨6533270, by rfl⟩ : syracuseStep 8711027 = 13066541) B13066541
theorem B1272711 : Blo 1271954 1272711 := bstep (se 1 (by rfl) ⟨954533, by rfl⟩ : syracuseStep 1272711 = 1909067) B1909067
theorem B1272719 : Blo 1271954 1272719 := bstep (se 1 (by rfl) ⟨954539, by rfl⟩ : syracuseStep 1272719 = 1909079) B1909079
theorem B1813433 : Blo 1271954 1813433 := bstep (se 2 (by rfl) ⟨680037, by rfl⟩ : syracuseStep 1813433 = 1360075) B1360075
theorem B1272763 : Blo 1271954 1272763 := bstep (se 1 (by rfl) ⟨954572, by rfl⟩ : syracuseStep 1272763 = 1909145) B1909145
theorem B2149321 : Blo 1271954 2149321 := bstep (se 2 (by rfl) ⟨805995, by rfl⟩ : syracuseStep 2149321 = 1611991) B1611991
theorem B1272839 : Blo 1271954 1272839 := bstep (se 1 (by rfl) ⟨954629, by rfl⟩ : syracuseStep 1272839 = 1909259) B1909259
theorem B7253003 : Blo 1271954 7253003 := bstep (se 1 (by rfl) ⟨5439752, by rfl⟩ : syracuseStep 7253003 = 10879505) B10879505
theorem B1272847 : Blo 1271954 1272847 := bstep (se 1 (by rfl) ⟨954635, by rfl⟩ : syracuseStep 1272847 = 1909271) B1909271
theorem B1813519 : Blo 1271954 1813519 := bstep (se 1 (by rfl) ⟨1360139, by rfl⟩ : syracuseStep 1813519 = 2720279) B2720279
theorem B1813547 : Blo 1271954 1813547 := bstep (se 1 (by rfl) ⟨1360160, by rfl⟩ : syracuseStep 1813547 = 2720321) B2720321
theorem B1272891 : Blo 1271954 1272891 := bstep (se 1 (by rfl) ⟨954668, by rfl⟩ : syracuseStep 1272891 = 1909337) B1909337
theorem B2862215 : Blo 1271954 2862215 := bstep (se 1 (by rfl) ⟨2146661, by rfl⟩ : syracuseStep 2862215 = 4293323) B4293323
theorem B1272967 : Blo 1271954 1272967 := bstep (se 1 (by rfl) ⟨954725, by rfl⟩ : syracuseStep 1272967 = 1909451) B1909451
theorem B1272975 : Blo 1271954 1272975 := bstep (se 1 (by rfl) ⟨954731, by rfl⟩ : syracuseStep 1272975 = 1909463) B1909463
theorem B8162477 : Blo 1271954 8162477 := bstep (se 3 (by rfl) ⟨1530464, by rfl⟩ : syracuseStep 8162477 = 3060929) B3060929
theorem B1273019 : Blo 1271954 1273019 := bstep (se 1 (by rfl) ⟨954764, by rfl⟩ : syracuseStep 1273019 = 1909529) B1909529
theorem B7253185 : Blo 1271954 7253185 := bstep (se 2 (by rfl) ⟨2719944, by rfl⟩ : syracuseStep 7253185 = 5439889) B5439889
theorem B1273095 : Blo 1271954 1273095 := bstep (se 1 (by rfl) ⟨954821, by rfl⟩ : syracuseStep 1273095 = 1909643) B1909643
theorem B1273103 : Blo 1271954 1273103 := bstep (se 1 (by rfl) ⟨954827, by rfl⟩ : syracuseStep 1273103 = 1909655) B1909655
theorem B4295969 : Blo 1271954 4295969 := bstep (se 2 (by rfl) ⟨1610988, by rfl⟩ : syracuseStep 4295969 = 3221977) B3221977
theorem B2862395 : Blo 1271954 2862395 := bstep (se 1 (by rfl) ⟨2146796, by rfl⟩ : syracuseStep 2862395 = 4293593) B4293593
theorem B3870011 : Blo 1271954 3870011 := bstep (se 1 (by rfl) ⟨2902508, by rfl⟩ : syracuseStep 3870011 = 5805017) B5805017
theorem B1273147 : Blo 1271954 1273147 := bstep (se 1 (by rfl) ⟨954860, by rfl⟩ : syracuseStep 1273147 = 1909721) B1909721
theorem B3222899 : Blo 1271954 3222899 := bstep (se 1 (by rfl) ⟨2417174, by rfl⟩ : syracuseStep 3222899 = 4834349) B4834349
theorem B8154503 : Blo 1271954 8154503 := bstep (se 1 (by rfl) ⟨6115877, by rfl⟩ : syracuseStep 8154503 = 12231755) B12231755
theorem B1273223 : Blo 1271954 1273223 := bstep (se 1 (by rfl) ⟨954917, by rfl⟩ : syracuseStep 1273223 = 1909835) B1909835
theorem B1273231 : Blo 1271954 1273231 := bstep (se 1 (by rfl) ⟨954923, by rfl⟩ : syracuseStep 1273231 = 1909847) B1909847
theorem B2862521 : Blo 1271954 2862521 := bstep (se 2 (by rfl) ⟨1073445, by rfl⟩ : syracuseStep 2862521 = 2146891) B2146891
theorem B4836793 : Blo 1271954 4836793 := bstep (se 2 (by rfl) ⟨1813797, by rfl⟩ : syracuseStep 4836793 = 3627595) B3627595
theorem B1273275 : Blo 1271954 1273275 := bstep (se 1 (by rfl) ⟨954956, by rfl⟩ : syracuseStep 1273275 = 1909913) B1909913
theorem B66096593 : Blo 1271954 66096593 := bstep (se 2 (by rfl) ⟨24786222, by rfl⟩ : syracuseStep 66096593 = 49572445) B49572445
theorem B1273351 : Blo 1271954 1273351 := bstep (se 1 (by rfl) ⟨955013, by rfl⟩ : syracuseStep 1273351 = 1910027) B1910027
theorem B5164555 : Blo 1271954 5164555 := bstep (se 1 (by rfl) ⟨3873416, by rfl⟩ : syracuseStep 5164555 = 7746833) B7746833
theorem B1273359 : Blo 1271954 1273359 := bstep (se 1 (by rfl) ⟨955019, by rfl⟩ : syracuseStep 1273359 = 1910039) B1910039
theorem B1273403 : Blo 1271954 1273403 := bstep (se 1 (by rfl) ⟨955052, by rfl⟩ : syracuseStep 1273403 = 1910105) B1910105
theorem B1273479 : Blo 1271954 1273479 := bstep (se 1 (by rfl) ⟨955109, by rfl⟩ : syracuseStep 1273479 = 1910219) B1910219
theorem B1273487 : Blo 1271954 1273487 := bstep (se 1 (by rfl) ⟨955115, by rfl⟩ : syracuseStep 1273487 = 1910231) B1910231
theorem B1273531 : Blo 1271954 1273531 := bstep (se 1 (by rfl) ⟨955148, by rfl⟩ : syracuseStep 1273531 = 1910297) B1910297
theorem B6885121 : Blo 1271954 6885121 := bstep (se 2 (by rfl) ⟨2581920, by rfl⟩ : syracuseStep 6885121 = 5163841) B5163841
theorem B1273607 : Blo 1271954 1273607 := bstep (se 1 (by rfl) ⟨955205, by rfl⟩ : syracuseStep 1273607 = 1910411) B1910411
theorem B2862863 : Blo 1271954 2862863 := bstep (se 1 (by rfl) ⟨2147147, by rfl⟩ : syracuseStep 2862863 = 4294295) B4294295
theorem B1273615 : Blo 1271954 1273615 := bstep (se 1 (by rfl) ⟨955211, by rfl⟩ : syracuseStep 1273615 = 1910423) B1910423
theorem B2862881 : Blo 1271954 2862881 := bstep (se 2 (by rfl) ⟨1073580, by rfl⟩ : syracuseStep 2862881 = 2147161) B2147161
theorem B1273659 : Blo 1271954 1273659 := bstep (se 1 (by rfl) ⟨955244, by rfl⟩ : syracuseStep 1273659 = 1910489) B1910489
theorem B4296563 : Blo 1271954 4296563 := bstep (se 1 (by rfl) ⟨3222422, by rfl⟩ : syracuseStep 4296563 = 6444845) B6444845
theorem B3223415 : Blo 1271954 3223415 := bstep (se 1 (by rfl) ⟨2417561, by rfl⟩ : syracuseStep 3223415 = 4835123) B4835123
theorem B1273735 : Blo 1271954 1273735 := bstep (se 1 (by rfl) ⟨955301, by rfl⟩ : syracuseStep 1273735 = 1910603) B1910603
theorem B1273743 : Blo 1271954 1273743 := bstep (se 1 (by rfl) ⟨955307, by rfl⟩ : syracuseStep 1273743 = 1910615) B1910615
theorem B7245713 : Blo 1271954 7245713 := bstep (se 2 (by rfl) ⟨2717142, by rfl⟩ : syracuseStep 7245713 = 5434285) B5434285
theorem B6197137 : Blo 1271954 6197137 := bstep (se 2 (by rfl) ⟨2323926, by rfl⟩ : syracuseStep 6197137 = 4647853) B4647853
theorem B3624851 : Blo 1271954 3624851 := bstep (se 1 (by rfl) ⟨2718638, by rfl⟩ : syracuseStep 3624851 = 5437277) B5437277
theorem B1273787 : Blo 1271954 1273787 := bstep (se 1 (by rfl) ⟨955340, by rfl⟩ : syracuseStep 1273787 = 1910681) B1910681
theorem B1273863 : Blo 1271954 1273863 := bstep (se 1 (by rfl) ⟨955397, by rfl⟩ : syracuseStep 1273863 = 1910795) B1910795
theorem B1273871 : Blo 1271954 1273871 := bstep (se 1 (by rfl) ⟨955403, by rfl⟩ : syracuseStep 1273871 = 1910807) B1910807
theorem B1273915 : Blo 1271954 1273915 := bstep (se 1 (by rfl) ⟨955436, by rfl⟩ : syracuseStep 1273915 = 1910873) B1910873
theorem B2863223 : Blo 1271954 2863223 := bstep (se 1 (by rfl) ⟨2147417, by rfl⟩ : syracuseStep 2863223 = 4294835) B4294835
theorem B3625249 : Blo 1271954 3625249 := bstep (se 2 (by rfl) ⟨1359468, by rfl⟩ : syracuseStep 3625249 = 2718937) B2718937
theorem B2863403 : Blo 1271954 2863403 := bstep (se 1 (by rfl) ⟨2147552, by rfl⟩ : syracuseStep 2863403 = 4295105) B4295105
theorem B7246169 : Blo 1271954 7246169 := bstep (se 2 (by rfl) ⟨2717313, by rfl⟩ : syracuseStep 7246169 = 5434627) B5434627
theorem B15479261 : Blo 1271954 15479261 := bstep (se 3 (by rfl) ⟨2902361, by rfl⟩ : syracuseStep 15479261 = 5804723) B5804723
theorem B6443549 : Blo 1271954 6443549 := bstep (se 3 (by rfl) ⟨1208165, by rfl⟩ : syracuseStep 6443549 = 2416331) B2416331
theorem B82629233 : Blo 1271954 82629233 := bstep (se 2 (by rfl) ⟨30985962, by rfl⟩ : syracuseStep 82629233 = 61971925) B61971925
theorem B2863763 : Blo 1271954 2863763 := bstep (se 1 (by rfl) ⟨2147822, by rfl⟩ : syracuseStep 2863763 = 4295645) B4295645
theorem B2863817 : Blo 1271954 2863817 := bstep (se 2 (by rfl) ⟨1073931, by rfl⟩ : syracuseStep 2863817 = 2147863) B2147863
theorem B5157665 : Blo 1271954 5157665 := bstep (se 2 (by rfl) ⟨1934124, by rfl⟩ : syracuseStep 5157665 = 3868249) B3868249
theorem B13759307 : Blo 1271954 13759307 := bstep (se 1 (by rfl) ⟨10319480, by rfl⟩ : syracuseStep 13759307 = 20638961) B20638961
theorem B3224407 : Blo 1271954 3224407 := bstep (se 1 (by rfl) ⟨2418305, by rfl⟩ : syracuseStep 3224407 = 4836611) B4836611
theorem B6116185 : Blo 1271954 6116185 := bstep (se 2 (by rfl) ⟨2293569, by rfl⟩ : syracuseStep 6116185 = 4587139) B4587139
theorem B80573363 : Blo 1271954 80573363 := bstep (se 1 (by rfl) ⟨60430022, by rfl⟩ : syracuseStep 80573363 = 120860045) B120860045
theorem B6444035 : Blo 1271954 6444035 := bstep (se 1 (by rfl) ⟨4833026, by rfl⟩ : syracuseStep 6444035 = 9666053) B9666053
theorem B3060823 : Blo 1271954 3060823 := bstep (se 1 (by rfl) ⟨2295617, by rfl⟩ : syracuseStep 3060823 = 4591235) B4591235
theorem B1528951 : Blo 1271954 1528951 := bstep (se 1 (by rfl) ⟨1146713, by rfl⟩ : syracuseStep 1528951 = 2293427) B2293427
theorem B3626137 : Blo 1271954 3626137 := bstep (se 2 (by rfl) ⟨1359801, by rfl⟩ : syracuseStep 3626137 = 2719603) B2719603
theorem B1610923 : Blo 1271954 1610923 := bstep (se 1 (by rfl) ⟨1208192, by rfl⟩ : syracuseStep 1610923 = 2416385) B2416385
theorem B10876193 : Blo 1271954 10876193 := bstep (se 2 (by rfl) ⟨4078572, by rfl⟩ : syracuseStep 10876193 = 8157145) B8157145
theorem B6886745 : Blo 1271954 6886745 := bstep (se 2 (by rfl) ⟨2582529, by rfl⟩ : syracuseStep 6886745 = 5165059) B5165059
theorem B2864519 : Blo 1271954 2864519 := bstep (se 1 (by rfl) ⟨2148389, by rfl⟩ : syracuseStep 2864519 = 4296779) B4296779
theorem B9172433 : Blo 1271954 9172433 := bstep (se 2 (by rfl) ⟨3439662, by rfl⟩ : syracuseStep 9172433 = 6879325) B6879325
theorem B4830749 : Blo 1271954 4830749 := bstep (se 3 (by rfl) ⟨905765, by rfl⟩ : syracuseStep 4830749 = 1811531) B1811531
theorem B3626525 : Blo 1271954 3626525 := bstep (se 3 (by rfl) ⟨679973, by rfl⟩ : syracuseStep 3626525 = 1359947) B1359947
theorem B2864699 : Blo 1271954 2864699 := bstep (se 1 (by rfl) ⟨2148524, by rfl⟩ : syracuseStep 2864699 = 4297049) B4297049
theorem B25130573 : Blo 1271954 25130573 := bstep (se 3 (by rfl) ⟨4711982, by rfl⟩ : syracuseStep 25130573 = 9423965) B9423965
theorem B565040771 : Blo 1271954 565040771 := bstep (se 1 (by rfl) ⟨423780578, by rfl⟩ : syracuseStep 565040771 = 847561157) B847561157
theorem B3438215 : Blo 1271954 3438215 := bstep (se 1 (by rfl) ⟨2578661, by rfl⟩ : syracuseStep 3438215 = 5157323) B5157323
theorem B1431175 : Blo 1271954 1431175 := bstep (se 1 (by rfl) ⟨1073381, by rfl⟩ : syracuseStep 1431175 = 2146763) B2146763
theorem B13940401 : Blo 1271954 13940401 := bstep (se 2 (by rfl) ⟨5227650, by rfl⟩ : syracuseStep 13940401 = 10455301) B10455301
theorem B2864825 : Blo 1271954 2864825 := bstep (se 2 (by rfl) ⟨1074309, by rfl⟩ : syracuseStep 2864825 = 2148619) B2148619
theorem B2037563 : Blo 1271954 2037563 := bstep (se 1 (by rfl) ⟨1528172, by rfl⟩ : syracuseStep 2037563 = 3056345) B3056345
theorem B4896571 : Blo 1271954 4896571 := bstep (se 1 (by rfl) ⟨3672428, by rfl⟩ : syracuseStep 4896571 = 7344857) B7344857
theorem B1431355 : Blo 1271954 1431355 := bstep (se 1 (by rfl) ⟨1073516, by rfl⟩ : syracuseStep 1431355 = 2147033) B2147033
theorem B3872627 : Blo 1271954 3872627 := bstep (se 1 (by rfl) ⟨2904470, by rfl⟩ : syracuseStep 3872627 = 5808941) B5808941
theorem B2717587 : Blo 1271954 2717587 := bstep (se 1 (by rfl) ⟨2038190, by rfl⟩ : syracuseStep 2717587 = 4076381) B4076381
theorem B61929485 : Blo 1271954 61929485 := bstep (se 3 (by rfl) ⟨11611778, by rfl⟩ : syracuseStep 61929485 = 23223557) B23223557
theorem B2865167 : Blo 1271954 2865167 := bstep (se 1 (by rfl) ⟨2148875, by rfl⟩ : syracuseStep 2865167 = 4297751) B4297751
theorem B3438625 : Blo 1271954 3438625 := bstep (se 2 (by rfl) ⟨1289484, by rfl⟩ : syracuseStep 3438625 = 2578969) B2578969
theorem B2865185 : Blo 1271954 2865185 := bstep (se 2 (by rfl) ⟨1074444, by rfl⟩ : syracuseStep 2865185 = 2148889) B2148889
theorem B4077611 : Blo 1271954 4077611 := bstep (se 1 (by rfl) ⟨3058208, by rfl⟩ : syracuseStep 4077611 = 6116417) B6116417
theorem B16750709 : Blo 1271954 16750709 := bstep (se 5 (by rfl) ⟨785189, by rfl⟩ : syracuseStep 16750709 = 1570379) B1570379
theorem B1611895 : Blo 1271954 1611895 := bstep (se 1 (by rfl) ⟨1208921, by rfl⟩ : syracuseStep 1611895 = 2417843) B2417843
theorem B4831433 : Blo 1271954 4831433 := bstep (se 2 (by rfl) ⟨1811787, by rfl⟩ : syracuseStep 4831433 = 3623575) B3623575
theorem B1431823 : Blo 1271954 1431823 := bstep (se 1 (by rfl) ⟨1073867, by rfl⟩ : syracuseStep 1431823 = 2147735) B2147735
theorem B2865527 : Blo 1271954 2865527 := bstep (se 1 (by rfl) ⟨2149145, by rfl⟩ : syracuseStep 2865527 = 4298291) B4298291
theorem B4299155 : Blo 1271954 4299155 := bstep (se 1 (by rfl) ⟨3224366, by rfl⟩ : syracuseStep 4299155 = 6448733) B6448733
theorem B1612219 : Blo 1271954 1612219 := bstep (se 1 (by rfl) ⟨1209164, by rfl⟩ : syracuseStep 1612219 = 2418329) B2418329
theorem B16308701 : Blo 1271954 16308701 := bstep (se 3 (by rfl) ⟨3057881, by rfl⟩ : syracuseStep 16308701 = 6115763) B6115763
theorem B2865707 : Blo 1271954 2865707 := bstep (se 1 (by rfl) ⟨2149280, by rfl⟩ : syracuseStep 2865707 = 4298561) B4298561
theorem B6445655 : Blo 1271954 6445655 := bstep (se 1 (by rfl) ⟨4834241, by rfl⟩ : syracuseStep 6445655 = 9668483) B9668483
theorem B1432327 : Blo 1271954 1432327 := bstep (se 1 (by rfl) ⟨1074245, by rfl⟩ : syracuseStep 1432327 = 2148491) B2148491
theorem B8157989 : Blo 1271954 8157989 := bstep (se 4 (by rfl) ⟨764811, by rfl⟩ : syracuseStep 8157989 = 1529623) B1529623
theorem B4078471 : Blo 1271954 4078471 := bstep (se 1 (by rfl) ⟨3058853, by rfl⟩ : syracuseStep 4078471 = 6117707) B6117707
theorem B2866067 : Blo 1271954 2866067 := bstep (se 1 (by rfl) ⟨2149550, by rfl⟩ : syracuseStep 2866067 = 4299101) B4299101
theorem B1432507 : Blo 1271954 1432507 := bstep (se 1 (by rfl) ⟨1074380, by rfl⟩ : syracuseStep 1432507 = 2148761) B2148761
theorem B2866121 : Blo 1271954 2866121 := bstep (se 2 (by rfl) ⟨1074795, by rfl⟩ : syracuseStep 2866121 = 2149591) B2149591
theorem B6618077 : Blo 1271954 6618077 := bstep (se 3 (by rfl) ⟨1240889, by rfl⟩ : syracuseStep 6618077 = 2481779) B2481779
theorem B6446141 : Blo 1271954 6446141 := bstep (se 3 (by rfl) ⟨1208651, by rfl⟩ : syracuseStep 6446141 = 2417303) B2417303
theorem B39214277 : Blo 1271954 39214277 := bstep (se 4 (by rfl) ⟨3676338, by rfl⟩ : syracuseStep 39214277 = 7352677) B7352677
theorem B1907975 : Blo 1271954 1907975 := bstep (se 1 (by rfl) ⟨1430981, by rfl⟩ : syracuseStep 1907975 = 2861963) B2861963
theorem B13753633 : Blo 1271954 13753633 := bstep (se 2 (by rfl) ⟨5157612, by rfl⟩ : syracuseStep 13753633 = 10315225) B10315225
theorem B1908011 : Blo 1271954 1908011 := bstep (se 1 (by rfl) ⟨1431008, by rfl⟩ : syracuseStep 1908011 = 2862017) B2862017
theorem B2293051 : Blo 1271954 2293051 := bstep (se 1 (by rfl) ⟨1719788, by rfl⟩ : syracuseStep 2293051 = 3439577) B3439577
theorem B73456955 : Blo 1271954 73456955 := bstep (se 1 (by rfl) ⟨55092716, by rfl⟩ : syracuseStep 73456955 = 110185433) B110185433
theorem B1908041 : Blo 1271954 1908041 := bstep (se 2 (by rfl) ⟨715515, by rfl⟩ : syracuseStep 1908041 = 1431031) B1431031
theorem B6200711 : Blo 1271954 6200711 := bstep (se 1 (by rfl) ⟨4650533, by rfl⟩ : syracuseStep 6200711 = 9301067) B9301067
theorem B1432975 : Blo 1271954 1432975 := bstep (se 1 (by rfl) ⟨1074731, by rfl⟩ : syracuseStep 1432975 = 2149463) B2149463
theorem B7249337 : Blo 1271954 7249337 := bstep (se 2 (by rfl) ⟨2718501, by rfl⟩ : syracuseStep 7249337 = 5437003) B5437003
theorem B1908155 : Blo 1271954 1908155 := bstep (se 1 (by rfl) ⟨1431116, by rfl⟩ : syracuseStep 1908155 = 2862233) B2862233
theorem B6118877 : Blo 1271954 6118877 := bstep (se 3 (by rfl) ⟨1147289, by rfl⟩ : syracuseStep 6118877 = 2294579) B2294579
theorem B1908215 : Blo 1271954 1908215 := bstep (se 1 (by rfl) ⟨1431161, by rfl⟩ : syracuseStep 1908215 = 2862323) B2862323
theorem B1908239 : Blo 1271954 1908239 := bstep (se 1 (by rfl) ⟨1431179, by rfl⟩ : syracuseStep 1908239 = 2862359) B2862359
theorem B1908281 : Blo 1271954 1908281 := bstep (se 2 (by rfl) ⟨715605, by rfl⟩ : syracuseStep 1908281 = 1431211) B1431211
theorem B1908359 : Blo 1271954 1908359 := bstep (se 1 (by rfl) ⟨1431269, by rfl⟩ : syracuseStep 1908359 = 2862539) B2862539
theorem B1908395 : Blo 1271954 1908395 := bstep (se 1 (by rfl) ⟨1431296, by rfl⟩ : syracuseStep 1908395 = 2862593) B2862593
theorem B8158913 : Blo 1271954 8158913 := bstep (se 2 (by rfl) ⟨3059592, by rfl⟩ : syracuseStep 8158913 = 6119185) B6119185
theorem B1908425 : Blo 1271954 1908425 := bstep (se 2 (by rfl) ⟨715659, by rfl⟩ : syracuseStep 1908425 = 1431319) B1431319
theorem B2719433 : Blo 1271954 2719433 := bstep (se 2 (by rfl) ⟨1019787, by rfl⟩ : syracuseStep 2719433 = 2039575) B2039575
theorem B4079393 : Blo 1271954 4079393 := bstep (se 2 (by rfl) ⟨1529772, by rfl⟩ : syracuseStep 4079393 = 3059545) B3059545
theorem B1908539 : Blo 1271954 1908539 := bstep (se 1 (by rfl) ⟨1431404, by rfl⟩ : syracuseStep 1908539 = 2862809) B2862809
theorem B1908599 : Blo 1271954 1908599 := bstep (se 1 (by rfl) ⟨1431449, by rfl⟩ : syracuseStep 1908599 = 2862899) B2862899
theorem B1908623 : Blo 1271954 1908623 := bstep (se 1 (by rfl) ⟨1431467, by rfl⟩ : syracuseStep 1908623 = 2862935) B2862935
theorem B13762457 : Blo 1271954 13762457 := bstep (se 2 (by rfl) ⟨5160921, by rfl⟩ : syracuseStep 13762457 = 10321843) B10321843
theorem B1908665 : Blo 1271954 1908665 := bstep (se 2 (by rfl) ⟨715749, by rfl⟩ : syracuseStep 1908665 = 1431499) B1431499
theorem B4833209 : Blo 1271954 4833209 := bstep (se 2 (by rfl) ⟨1812453, by rfl⟩ : syracuseStep 4833209 = 3624907) B3624907
theorem B1908815 : Blo 1271954 1908815 := bstep (se 1 (by rfl) ⟨1431611, by rfl⟩ : syracuseStep 1908815 = 2863223) B2863223
theorem B1908935 : Blo 1271954 1908935 := bstep (se 1 (by rfl) ⟨1431701, by rfl⟩ : syracuseStep 1908935 = 2863403) B2863403
theorem B2416969 : Blo 1271954 2416969 := bstep (se 2 (by rfl) ⟨906363, by rfl⟩ : syracuseStep 2416969 = 1812727) B1812727
theorem B2146655 : Blo 1271954 2146655 := bstep (se 1 (by rfl) ⟨1609991, by rfl⟩ : syracuseStep 2146655 = 3219983) B3219983
theorem B1909097 : Blo 1271954 1909097 := bstep (se 2 (by rfl) ⟨715911, by rfl⟩ : syracuseStep 1909097 = 1431823) B1431823
theorem B4833665 : Blo 1271954 4833665 := bstep (se 2 (by rfl) ⟨1812624, by rfl⟩ : syracuseStep 4833665 = 3625249) B3625249
theorem B1909175 : Blo 1271954 1909175 := bstep (se 1 (by rfl) ⟨1431881, by rfl⟩ : syracuseStep 1909175 = 2863763) B2863763
theorem B4587977 : Blo 1271954 4587977 := bstep (se 2 (by rfl) ⟨1720491, by rfl⟩ : syracuseStep 4587977 = 3440983) B3440983
theorem B1909211 : Blo 1271954 1909211 := bstep (se 1 (by rfl) ⟨1431908, by rfl⟩ : syracuseStep 1909211 = 2863817) B2863817
theorem B4293107 : Blo 1271954 4293107 := bstep (se 1 (by rfl) ⟨3219830, by rfl⟩ : syracuseStep 4293107 = 6439661) B6439661
theorem B8380961 : Blo 1271954 8380961 := bstep (se 2 (by rfl) ⟨3142860, by rfl⟩ : syracuseStep 8380961 = 6285721) B6285721
theorem B53715575 : Blo 1271954 53715575 := bstep (se 1 (by rfl) ⟨40286681, by rfl⟩ : syracuseStep 53715575 = 80573363) B80573363
theorem B7250795 : Blo 1271954 7250795 := bstep (se 1 (by rfl) ⟨5438096, by rfl⟩ : syracuseStep 7250795 = 10876193) B10876193
theorem B2147215 : Blo 1271954 2147215 := bstep (se 1 (by rfl) ⟨1610411, by rfl⟩ : syracuseStep 2147215 = 3220823) B3220823
theorem B1909679 : Blo 1271954 1909679 := bstep (se 1 (by rfl) ⟨1432259, by rfl⟩ : syracuseStep 1909679 = 2864519) B2864519
theorem B9667511 : Blo 1271954 9667511 := bstep (se 1 (by rfl) ⟨7250633, by rfl⟩ : syracuseStep 9667511 = 14501267) B14501267
theorem B1909769 : Blo 1271954 1909769 := bstep (se 2 (by rfl) ⟨716163, by rfl⟩ : syracuseStep 1909769 = 1432327) B1432327
theorem B4293647 : Blo 1271954 4293647 := bstep (se 1 (by rfl) ⟨3220235, by rfl⟩ : syracuseStep 4293647 = 6440471) B6440471
theorem B3220499 : Blo 1271954 3220499 := bstep (se 1 (by rfl) ⟨2415374, by rfl⟩ : syracuseStep 3220499 = 4830749) B4830749
theorem B2417683 : Blo 1271954 2417683 := bstep (se 1 (by rfl) ⟨1813262, by rfl⟩ : syracuseStep 2417683 = 3626525) B3626525
theorem B1909799 : Blo 1271954 1909799 := bstep (se 1 (by rfl) ⟨1432349, by rfl⟩ : syracuseStep 1909799 = 2864699) B2864699
theorem B16753715 : Blo 1271954 16753715 := bstep (se 1 (by rfl) ⟨12565286, by rfl⟩ : syracuseStep 16753715 = 25130573) B25130573
theorem B376693847 : Blo 1271954 376693847 := bstep (se 1 (by rfl) ⟨282520385, by rfl⟩ : syracuseStep 376693847 = 565040771) B565040771
theorem B1909883 : Blo 1271954 1909883 := bstep (se 1 (by rfl) ⟨1432412, by rfl⟩ : syracuseStep 1909883 = 2864825) B2864825
theorem B2294983 : Blo 1271954 2294983 := bstep (se 1 (by rfl) ⟨1721237, by rfl⟩ : syracuseStep 2294983 = 3442475) B3442475
theorem B19596491 : Blo 1271954 19596491 := bstep (se 1 (by rfl) ⟨14697368, by rfl⟩ : syracuseStep 19596491 = 29394737) B29394737
theorem B3441911 : Blo 1271954 3441911 := bstep (se 1 (by rfl) ⟨2581433, by rfl⟩ : syracuseStep 3441911 = 5162867) B5162867
theorem B2581751 : Blo 1271954 2581751 := bstep (se 1 (by rfl) ⟨1936313, by rfl⟩ : syracuseStep 2581751 = 3872627) B3872627
theorem B1910009 : Blo 1271954 1910009 := bstep (se 2 (by rfl) ⟨716253, by rfl⟩ : syracuseStep 1910009 = 1432507) B1432507
theorem B1910111 : Blo 1271954 1910111 := bstep (se 1 (by rfl) ⟨1432583, by rfl⟩ : syracuseStep 1910111 = 2865167) B2865167
theorem B2418025 : Blo 1271954 2418025 := bstep (se 2 (by rfl) ⟨906759, by rfl⟩ : syracuseStep 2418025 = 1813519) B1813519
theorem B1910123 : Blo 1271954 1910123 := bstep (se 1 (by rfl) ⟨1432592, by rfl⟩ : syracuseStep 1910123 = 2865185) B2865185
theorem B11167139 : Blo 1271954 11167139 := bstep (se 1 (by rfl) ⟨8375354, by rfl⟩ : syracuseStep 11167139 = 16750709) B16750709
theorem B4081097 : Blo 1271954 4081097 := bstep (se 2 (by rfl) ⟨1530411, by rfl⟩ : syracuseStep 4081097 = 3060823) B3060823
theorem B3220955 : Blo 1271954 3220955 := bstep (se 1 (by rfl) ⟨2415716, by rfl⟩ : syracuseStep 3220955 = 4831433) B4831433
theorem B4834849 : Blo 1271954 4834849 := bstep (se 2 (by rfl) ⟨1813068, by rfl⟩ : syracuseStep 4834849 = 3626137) B3626137
theorem B2147897 : Blo 1271954 2147897 := bstep (se 2 (by rfl) ⟨805461, by rfl⟩ : syracuseStep 2147897 = 1610923) B1610923
theorem B1910351 : Blo 1271954 1910351 := bstep (se 1 (by rfl) ⟨1432763, by rfl⟩ : syracuseStep 1910351 = 2865527) B2865527
theorem B4294241 : Blo 1271954 4294241 := bstep (se 2 (by rfl) ⟨1610340, by rfl⟩ : syracuseStep 4294241 = 3220681) B3220681
theorem B10872467 : Blo 1271954 10872467 := bstep (se 1 (by rfl) ⟨8154350, by rfl⟩ : syracuseStep 10872467 = 16308701) B16308701
theorem B9791165 : Blo 1271954 9791165 := bstep (se 3 (by rfl) ⟨1835843, by rfl⟩ : syracuseStep 9791165 = 3671687) B3671687
theorem B1910471 : Blo 1271954 1910471 := bstep (se 1 (by rfl) ⟨1432853, by rfl⟩ : syracuseStep 1910471 = 2865707) B2865707
theorem B3057401 : Blo 1271954 3057401 := bstep (se 2 (by rfl) ⟨1146525, by rfl⟩ : syracuseStep 3057401 = 2293051) B2293051
theorem B37717849 : Blo 1271954 37717849 := bstep (se 2 (by rfl) ⟨14144193, by rfl⟩ : syracuseStep 37717849 = 28288387) B28288387
theorem B1910633 : Blo 1271954 1910633 := bstep (se 2 (by rfl) ⟨716487, by rfl⟩ : syracuseStep 1910633 = 1432975) B1432975
theorem B6449057 : Blo 1271954 6449057 := bstep (se 2 (by rfl) ⟨2418396, by rfl⟩ : syracuseStep 6449057 = 4836793) B4836793
theorem B1910711 : Blo 1271954 1910711 := bstep (se 1 (by rfl) ⟨1433033, by rfl⟩ : syracuseStep 1910711 = 2866067) B2866067
theorem B1910747 : Blo 1271954 1910747 := bstep (se 1 (by rfl) ⟨1433060, by rfl⟩ : syracuseStep 1910747 = 2866121) B2866121
theorem B4835335 : Blo 1271954 4835335 := bstep (se 1 (by rfl) ⟨3626501, by rfl⟩ : syracuseStep 4835335 = 7253003) B7253003
theorem B5441651 : Blo 1271954 5441651 := bstep (se 1 (by rfl) ⟨4081238, by rfl⟩ : syracuseStep 5441651 = 8162477) B8162477
theorem B26142851 : Blo 1271954 26142851 := bstep (se 1 (by rfl) ⟨19607138, by rfl⟩ : syracuseStep 26142851 = 39214277) B39214277
theorem B1271983 : Blo 1271954 1271983 := bstep (se 1 (by rfl) ⟨953987, by rfl⟩ : syracuseStep 1271983 = 1907975) B1907975
theorem B1272007 : Blo 1271954 1272007 := bstep (se 1 (by rfl) ⟨954005, by rfl⟩ : syracuseStep 1272007 = 1908011) B1908011
theorem B1272027 : Blo 1271954 1272027 := bstep (se 1 (by rfl) ⟨954020, by rfl⟩ : syracuseStep 1272027 = 1908041) B1908041
theorem B2148599 : Blo 1271954 2148599 := bstep (se 1 (by rfl) ⟨1611449, by rfl⟩ : syracuseStep 2148599 = 3222899) B3222899
theorem B1272103 : Blo 1271954 1272103 := bstep (se 1 (by rfl) ⟨954077, by rfl⟩ : syracuseStep 1272103 = 1908155) B1908155
theorem B1272143 : Blo 1271954 1272143 := bstep (se 1 (by rfl) ⟨954107, by rfl⟩ : syracuseStep 1272143 = 1908215) B1908215
theorem B1272159 : Blo 1271954 1272159 := bstep (se 1 (by rfl) ⟨954119, by rfl⟩ : syracuseStep 1272159 = 1908239) B1908239
theorem B9668969 : Blo 1271954 9668969 := bstep (se 2 (by rfl) ⟨3625863, by rfl⟩ : syracuseStep 9668969 = 7251727) B7251727
theorem B1272187 : Blo 1271954 1272187 := bstep (se 1 (by rfl) ⟨954140, by rfl⟩ : syracuseStep 1272187 = 1908281) B1908281
theorem B1272239 : Blo 1271954 1272239 := bstep (se 1 (by rfl) ⟨954179, by rfl⟩ : syracuseStep 1272239 = 1908359) B1908359
theorem B1272263 : Blo 1271954 1272263 := bstep (se 1 (by rfl) ⟨954197, by rfl⟩ : syracuseStep 1272263 = 1908395) B1908395
theorem B1272283 : Blo 1271954 1272283 := bstep (se 1 (by rfl) ⟨954212, by rfl⟩ : syracuseStep 1272283 = 1908425) B1908425
theorem B1812955 : Blo 1271954 1812955 := bstep (se 1 (by rfl) ⟨1359716, by rfl⟩ : syracuseStep 1812955 = 2719433) B2719433
theorem B8153581 : Blo 1271954 8153581 := bstep (se 3 (by rfl) ⟨1528796, by rfl⟩ : syracuseStep 8153581 = 3057593) B3057593
theorem B4835821 : Blo 1271954 4835821 := bstep (se 3 (by rfl) ⟨906716, by rfl⟩ : syracuseStep 4835821 = 1813433) B1813433
theorem B3623449 : Blo 1271954 3623449 := bstep (se 2 (by rfl) ⟨1358793, by rfl⟩ : syracuseStep 3623449 = 2717587) B2717587
theorem B1272359 : Blo 1271954 1272359 := bstep (se 1 (by rfl) ⟨954269, by rfl⟩ : syracuseStep 1272359 = 1908539) B1908539
theorem B1272399 : Blo 1271954 1272399 := bstep (se 1 (by rfl) ⟨954299, by rfl⟩ : syracuseStep 1272399 = 1908599) B1908599
theorem B2148943 : Blo 1271954 2148943 := bstep (se 1 (by rfl) ⟨1611707, by rfl⟩ : syracuseStep 2148943 = 3223415) B3223415
theorem B1272415 : Blo 1271954 1272415 := bstep (se 1 (by rfl) ⟨954311, by rfl⟩ : syracuseStep 1272415 = 1908623) B1908623
theorem B1272443 : Blo 1271954 1272443 := bstep (se 1 (by rfl) ⟨954332, by rfl⟩ : syracuseStep 1272443 = 1908665) B1908665
theorem B3222139 : Blo 1271954 3222139 := bstep (se 1 (by rfl) ⟨2416604, by rfl⟩ : syracuseStep 3222139 = 4833209) B4833209
theorem B1272495 : Blo 1271954 1272495 := bstep (se 1 (by rfl) ⟨954371, by rfl⟩ : syracuseStep 1272495 = 1908743) B1908743
theorem B1272519 : Blo 1271954 1272519 := bstep (se 1 (by rfl) ⟨954389, by rfl⟩ : syracuseStep 1272519 = 1908779) B1908779
theorem B1272539 : Blo 1271954 1272539 := bstep (se 1 (by rfl) ⟨954404, by rfl⟩ : syracuseStep 1272539 = 1908809) B1908809
theorem B4836125 : Blo 1271954 4836125 := bstep (se 3 (by rfl) ⟨906773, by rfl⟩ : syracuseStep 4836125 = 1813547) B1813547
theorem B1272615 : Blo 1271954 1272615 := bstep (se 1 (by rfl) ⟨954461, by rfl⟩ : syracuseStep 1272615 = 1908923) B1908923
theorem B2149193 : Blo 1271954 2149193 := bstep (se 2 (by rfl) ⟨805947, by rfl⟩ : syracuseStep 2149193 = 1611895) B1611895
theorem B1272655 : Blo 1271954 1272655 := bstep (se 1 (by rfl) ⟨954491, by rfl⟩ : syracuseStep 1272655 = 1908983) B1908983
theorem B1272671 : Blo 1271954 1272671 := bstep (se 1 (by rfl) ⟨954503, by rfl⟩ : syracuseStep 1272671 = 1909007) B1909007
theorem B1272699 : Blo 1271954 1272699 := bstep (se 1 (by rfl) ⟨954524, by rfl⟩ : syracuseStep 1272699 = 1909049) B1909049
theorem B2861999 : Blo 1271954 2861999 := bstep (se 1 (by rfl) ⟨2146499, by rfl⟩ : syracuseStep 2861999 = 4292999) B4292999
theorem B1272751 : Blo 1271954 1272751 := bstep (se 1 (by rfl) ⟨954563, by rfl⟩ : syracuseStep 1272751 = 1909127) B1909127
theorem B1272775 : Blo 1271954 1272775 := bstep (se 1 (by rfl) ⟨954581, by rfl⟩ : syracuseStep 1272775 = 1909163) B1909163
theorem B1272795 : Blo 1271954 1272795 := bstep (se 1 (by rfl) ⟨954596, by rfl⟩ : syracuseStep 1272795 = 1909193) B1909193
theorem B4295699 : Blo 1271954 4295699 := bstep (se 1 (by rfl) ⟨3221774, by rfl⟩ : syracuseStep 4295699 = 6443549) B6443549
theorem B1272871 : Blo 1271954 1272871 := bstep (se 1 (by rfl) ⟨954653, by rfl⟩ : syracuseStep 1272871 = 1909307) B1909307
theorem B1272911 : Blo 1271954 1272911 := bstep (se 1 (by rfl) ⟨954683, by rfl⟩ : syracuseStep 1272911 = 1909367) B1909367
theorem B55086155 : Blo 1271954 55086155 := bstep (se 1 (by rfl) ⟨41314616, by rfl⟩ : syracuseStep 55086155 = 82629233) B82629233
theorem B1272927 : Blo 1271954 1272927 := bstep (se 1 (by rfl) ⟨954695, by rfl⟩ : syracuseStep 1272927 = 1909391) B1909391
theorem B1272955 : Blo 1271954 1272955 := bstep (se 1 (by rfl) ⟨954716, by rfl⟩ : syracuseStep 1272955 = 1909433) B1909433
theorem B1813627 : Blo 1271954 1813627 := bstep (se 1 (by rfl) ⟨1360220, by rfl⟩ : syracuseStep 1813627 = 2720441) B2720441
theorem B2862251 : Blo 1271954 2862251 := bstep (se 1 (by rfl) ⟨2146688, by rfl⟩ : syracuseStep 2862251 = 4293377) B4293377
theorem B1273007 : Blo 1271954 1273007 := bstep (se 1 (by rfl) ⟨954755, by rfl⟩ : syracuseStep 1273007 = 1909511) B1909511
theorem B1273031 : Blo 1271954 1273031 := bstep (se 1 (by rfl) ⟨954773, by rfl⟩ : syracuseStep 1273031 = 1909547) B1909547
theorem B1273051 : Blo 1271954 1273051 := bstep (se 1 (by rfl) ⟨954788, by rfl⟩ : syracuseStep 1273051 = 1909577) B1909577
theorem B2149625 : Blo 1271954 2149625 := bstep (se 2 (by rfl) ⟨806109, by rfl⟩ : syracuseStep 2149625 = 1612219) B1612219
theorem B1273127 : Blo 1271954 1273127 := bstep (se 1 (by rfl) ⟨954845, by rfl⟩ : syracuseStep 1273127 = 1909691) B1909691
theorem B1273167 : Blo 1271954 1273167 := bstep (se 1 (by rfl) ⟨954875, by rfl⟩ : syracuseStep 1273167 = 1909751) B1909751
theorem B4296023 : Blo 1271954 4296023 := bstep (se 1 (by rfl) ⟨3222017, by rfl⟩ : syracuseStep 4296023 = 6444035) B6444035
theorem B1273183 : Blo 1271954 1273183 := bstep (se 1 (by rfl) ⟨954887, by rfl⟩ : syracuseStep 1273183 = 1909775) B1909775
theorem B1813855 : Blo 1271954 1813855 := bstep (se 1 (by rfl) ⟨1360391, by rfl⟩ : syracuseStep 1813855 = 2720783) B2720783
theorem B1273211 : Blo 1271954 1273211 := bstep (se 1 (by rfl) ⟨954908, by rfl⟩ : syracuseStep 1273211 = 1909817) B1909817
theorem B1273263 : Blo 1271954 1273263 := bstep (se 1 (by rfl) ⟨954947, by rfl⟩ : syracuseStep 1273263 = 1909895) B1909895
theorem B1273287 : Blo 1271954 1273287 := bstep (se 1 (by rfl) ⟨954965, by rfl⟩ : syracuseStep 1273287 = 1909931) B1909931
theorem B1273307 : Blo 1271954 1273307 := bstep (se 1 (by rfl) ⟨954980, by rfl⟩ : syracuseStep 1273307 = 1909961) B1909961
theorem B1273383 : Blo 1271954 1273383 := bstep (se 1 (by rfl) ⟨955037, by rfl⟩ : syracuseStep 1273383 = 1910075) B1910075
theorem B4591163 : Blo 1271954 4591163 := bstep (se 1 (by rfl) ⟨3443372, by rfl⟩ : syracuseStep 4591163 = 6886745) B6886745
theorem B1273423 : Blo 1271954 1273423 := bstep (se 1 (by rfl) ⟨955067, by rfl⟩ : syracuseStep 1273423 = 1910135) B1910135
theorem B1273439 : Blo 1271954 1273439 := bstep (se 1 (by rfl) ⟨955079, by rfl⟩ : syracuseStep 1273439 = 1910159) B1910159
theorem B1273467 : Blo 1271954 1273467 := bstep (se 1 (by rfl) ⟨955100, by rfl⟩ : syracuseStep 1273467 = 1910201) B1910201
theorem B6114955 : Blo 1271954 6114955 := bstep (se 1 (by rfl) ⟨4586216, by rfl⟩ : syracuseStep 6114955 = 9172433) B9172433
theorem B1273519 : Blo 1271954 1273519 := bstep (se 1 (by rfl) ⟨955139, by rfl⟩ : syracuseStep 1273519 = 1910279) B1910279
theorem B2862791 : Blo 1271954 2862791 := bstep (se 1 (by rfl) ⟨2147093, by rfl⟩ : syracuseStep 2862791 = 4294187) B4294187
theorem B1273543 : Blo 1271954 1273543 := bstep (se 1 (by rfl) ⟨955157, by rfl⟩ : syracuseStep 1273543 = 1910315) B1910315
theorem B1273563 : Blo 1271954 1273563 := bstep (se 1 (by rfl) ⟨955172, by rfl⟩ : syracuseStep 1273563 = 1910345) B1910345
theorem B8154913 : Blo 1271954 8154913 := bstep (se 2 (by rfl) ⟨3058092, by rfl⟩ : syracuseStep 8154913 = 6116185) B6116185
theorem B1273639 : Blo 1271954 1273639 := bstep (se 1 (by rfl) ⟨955229, by rfl⟩ : syracuseStep 1273639 = 1910459) B1910459
theorem B1273679 : Blo 1271954 1273679 := bstep (se 1 (by rfl) ⟨955259, by rfl⟩ : syracuseStep 1273679 = 1910519) B1910519
theorem B1273695 : Blo 1271954 1273695 := bstep (se 1 (by rfl) ⟨955271, by rfl⟩ : syracuseStep 1273695 = 1910543) B1910543
theorem B1273723 : Blo 1271954 1273723 := bstep (se 1 (by rfl) ⟨955292, by rfl⟩ : syracuseStep 1273723 = 1910585) B1910585
theorem B1273775 : Blo 1271954 1273775 := bstep (se 1 (by rfl) ⟨955331, by rfl⟩ : syracuseStep 1273775 = 1910663) B1910663
theorem B1273799 : Blo 1271954 1273799 := bstep (se 1 (by rfl) ⟨955349, by rfl⟩ : syracuseStep 1273799 = 1910699) B1910699
theorem B1273819 : Blo 1271954 1273819 := bstep (se 1 (by rfl) ⟨955364, by rfl⟩ : syracuseStep 1273819 = 1910729) B1910729
theorem B4075535 : Blo 1271954 4075535 := bstep (se 1 (by rfl) ⟨3056651, by rfl⟩ : syracuseStep 4075535 = 6113303) B6113303
theorem B1273895 : Blo 1271954 1273895 := bstep (se 1 (by rfl) ⟨955421, by rfl⟩ : syracuseStep 1273895 = 1910843) B1910843
theorem B1273935 : Blo 1271954 1273935 := bstep (se 1 (by rfl) ⟨955451, by rfl⟩ : syracuseStep 1273935 = 1910903) B1910903
theorem B1273951 : Blo 1271954 1273951 := bstep (se 1 (by rfl) ⟨955463, by rfl⟩ : syracuseStep 1273951 = 1910927) B1910927
theorem B9670913 : Blo 1271954 9670913 := bstep (se 2 (by rfl) ⟨3626592, by rfl⟩ : syracuseStep 9670913 = 7253185) B7253185
theorem B18338177 : Blo 1271954 18338177 := bstep (se 2 (by rfl) ⟨6876816, by rfl⟩ : syracuseStep 18338177 = 13753633) B13753633
theorem B4297103 : Blo 1271954 4297103 := bstep (se 1 (by rfl) ⟨3222827, by rfl⟩ : syracuseStep 4297103 = 6445655) B6445655
theorem B2863655 : Blo 1271954 2863655 := bstep (se 1 (by rfl) ⟨2147741, by rfl⟩ : syracuseStep 2863655 = 4295483) B4295483
theorem B4412051 : Blo 1271954 4412051 := bstep (se 1 (by rfl) ⟨3309038, by rfl⟩ : syracuseStep 4412051 = 6618077) B6618077
theorem B6886073 : Blo 1271954 6886073 := bstep (se 2 (by rfl) ⟨2582277, by rfl⟩ : syracuseStep 6886073 = 5164555) B5164555
theorem B4297427 : Blo 1271954 4297427 := bstep (se 1 (by rfl) ⟨3223070, by rfl⟩ : syracuseStep 4297427 = 6446141) B6446141
theorem B33051397 : Blo 1271954 33051397 := bstep (se 4 (by rfl) ⟨3098568, by rfl⟩ : syracuseStep 33051397 = 6197137) B6197137
theorem B3060553 : Blo 1271954 3060553 := bstep (se 2 (by rfl) ⟨1147707, by rfl⟩ : syracuseStep 3060553 = 2295415) B2295415
theorem B2863979 : Blo 1271954 2863979 := bstep (se 1 (by rfl) ⟨2147984, by rfl⟩ : syracuseStep 2863979 = 4295969) B4295969
theorem B2864033 : Blo 1271954 2864033 := bstep (se 2 (by rfl) ⟨1074012, by rfl⟩ : syracuseStep 2864033 = 2148025) B2148025
theorem B5436335 : Blo 1271954 5436335 := bstep (se 1 (by rfl) ⟨4077251, by rfl⟩ : syracuseStep 5436335 = 8154503) B8154503
theorem B4133807 : Blo 1271954 4133807 := bstep (se 1 (by rfl) ⟨3100355, by rfl⟩ : syracuseStep 4133807 = 6200711) B6200711
theorem B9180161 : Blo 1271954 9180161 := bstep (se 2 (by rfl) ⟨3442560, by rfl⟩ : syracuseStep 9180161 = 6885121) B6885121
theorem B2864375 : Blo 1271954 2864375 := bstep (se 1 (by rfl) ⟨2148281, by rfl⟩ : syracuseStep 2864375 = 4296563) B4296563
theorem B4830475 : Blo 1271954 4830475 := bstep (se 1 (by rfl) ⟨3622856, by rfl⟩ : syracuseStep 4830475 = 7245713) B7245713
theorem B3626365 : Blo 1271954 3626365 := bstep (se 3 (by rfl) ⟨679943, by rfl⟩ : syracuseStep 3626365 = 1359887) B1359887
theorem B4584833 : Blo 1271954 4584833 := bstep (se 2 (by rfl) ⟨1719312, by rfl⟩ : syracuseStep 4584833 = 3438625) B3438625
theorem B1430959 : Blo 1271954 1430959 := bstep (se 1 (by rfl) ⟨1073219, by rfl⟩ : syracuseStep 1430959 = 2146439) B2146439
theorem B1611191 : Blo 1271954 1611191 := bstep (se 1 (by rfl) ⟨1208393, by rfl⟩ : syracuseStep 1611191 = 2416787) B2416787
theorem B41268689 : Blo 1271954 41268689 := bstep (se 2 (by rfl) ⟨15475758, by rfl⟩ : syracuseStep 41268689 = 30951517) B30951517
theorem B4830779 : Blo 1271954 4830779 := bstep (se 1 (by rfl) ⟨3623084, by rfl⟩ : syracuseStep 4830779 = 7246169) B7246169
theorem B1611343 : Blo 1271954 1611343 := bstep (se 1 (by rfl) ⟨1208507, by rfl⟩ : syracuseStep 1611343 = 2417015) B2417015
theorem B9803351 : Blo 1271954 9803351 := bstep (se 1 (by rfl) ⟨7352513, by rfl⟩ : syracuseStep 9803351 = 14705027) B14705027
theorem B6444683 : Blo 1271954 6444683 := bstep (se 1 (by rfl) ⟨4833512, by rfl⟩ : syracuseStep 6444683 = 9667025) B9667025
theorem B10319507 : Blo 1271954 10319507 := bstep (se 1 (by rfl) ⟨7739630, by rfl⟩ : syracuseStep 10319507 = 15479261) B15479261
theorem B3626707 : Blo 1271954 3626707 := bstep (se 1 (by rfl) ⟨2720030, by rfl⟩ : syracuseStep 3626707 = 5440061) B5440061
theorem B2864969 : Blo 1271954 2864969 := bstep (se 2 (by rfl) ⟨1074363, by rfl⟩ : syracuseStep 2864969 = 2148727) B2148727
theorem B1431391 : Blo 1271954 1431391 := bstep (se 1 (by rfl) ⟨1073543, by rfl⟩ : syracuseStep 1431391 = 2147087) B2147087
theorem B3438443 : Blo 1271954 3438443 := bstep (se 1 (by rfl) ⟨2578832, by rfl⟩ : syracuseStep 3438443 = 5157665) B5157665
theorem B4298615 : Blo 1271954 4298615 := bstep (se 1 (by rfl) ⟨3223961, by rfl⟩ : syracuseStep 4298615 = 6447923) B6447923
theorem B9172871 : Blo 1271954 9172871 := bstep (se 1 (by rfl) ⟨6879653, by rfl⟩ : syracuseStep 9172871 = 13759307) B13759307
theorem B14489603 : Blo 1271954 14489603 := bstep (se 1 (by rfl) ⟨10867202, by rfl⟩ : syracuseStep 14489603 = 21734405) B21734405
theorem B7247879 : Blo 1271954 7247879 := bstep (se 1 (by rfl) ⟨5435909, by rfl⟩ : syracuseStep 7247879 = 10871819) B10871819
theorem B4298831 : Blo 1271954 4298831 := bstep (se 1 (by rfl) ⟨3224123, by rfl⟩ : syracuseStep 4298831 = 6448247) B6448247
theorem B1431751 : Blo 1271954 1431751 := bstep (se 1 (by rfl) ⟨1073813, by rfl⟩ : syracuseStep 1431751 = 2147627) B2147627
theorem B2038159 : Blo 1271954 2038159 := bstep (se 1 (by rfl) ⟨1528619, by rfl⟩ : syracuseStep 2038159 = 3057239) B3057239
theorem B2292143 : Blo 1271954 2292143 := bstep (se 1 (by rfl) ⟨1719107, by rfl⟩ : syracuseStep 2292143 = 3438215) B3438215
theorem B4299209 : Blo 1271954 4299209 := bstep (se 2 (by rfl) ⟨1612203, by rfl⟩ : syracuseStep 4299209 = 3224407) B3224407
theorem B5437961 : Blo 1271954 5437961 := bstep (se 2 (by rfl) ⟨2039235, by rfl⟩ : syracuseStep 5437961 = 4078471) B4078471
theorem B1358375 : Blo 1271954 1358375 := bstep (se 1 (by rfl) ⟨1018781, by rfl⟩ : syracuseStep 1358375 = 2037563) B2037563
theorem B2865761 : Blo 1271954 2865761 := bstep (se 2 (by rfl) ⟨1074660, by rfl⟩ : syracuseStep 2865761 = 2149321) B2149321
theorem B41286323 : Blo 1271954 41286323 := bstep (se 1 (by rfl) ⟨30964742, by rfl⟩ : syracuseStep 41286323 = 61929485) B61929485
theorem B4831933 : Blo 1271954 4831933 := bstep (se 3 (by rfl) ⟨905987, by rfl⟩ : syracuseStep 4831933 = 1811975) B1811975
theorem B2718407 : Blo 1271954 2718407 := bstep (se 1 (by rfl) ⟨2038805, by rfl⟩ : syracuseStep 2718407 = 4077611) B4077611
theorem B4299479 : Blo 1271954 4299479 := bstep (se 1 (by rfl) ⟨3224609, by rfl⟩ : syracuseStep 4299479 = 6449219) B6449219
theorem B2038601 : Blo 1271954 2038601 := bstep (se 2 (by rfl) ⟨764475, by rfl⟩ : syracuseStep 2038601 = 1528951) B1528951
theorem B8706923 : Blo 1271954 8706923 := bstep (se 1 (by rfl) ⟨6530192, by rfl⟩ : syracuseStep 8706923 = 13060385) B13060385
theorem B2866103 : Blo 1271954 2866103 := bstep (se 1 (by rfl) ⟨2149577, by rfl⟩ : syracuseStep 2866103 = 4299155) B4299155
theorem B1432615 : Blo 1271954 1432615 := bstep (se 1 (by rfl) ⟨1074461, by rfl⟩ : syracuseStep 1432615 = 2148923) B2148923
theorem B2415739 : Blo 1271954 2415739 := bstep (se 1 (by rfl) ⟨1811804, by rfl⟩ : syracuseStep 2415739 = 3623609) B3623609
theorem B5438659 : Blo 1271954 5438659 := bstep (se 1 (by rfl) ⟨4078994, by rfl⟩ : syracuseStep 5438659 = 8157989) B8157989
theorem B2415815 : Blo 1271954 2415815 := bstep (se 1 (by rfl) ⟨1811861, by rfl⟩ : syracuseStep 2415815 = 3623723) B3623723
theorem B6200567 : Blo 1271954 6200567 := bstep (se 1 (by rfl) ⟨4650425, by rfl⟩ : syracuseStep 6200567 = 9300851) B9300851
theorem B5807351 : Blo 1271954 5807351 := bstep (se 1 (by rfl) ⟨4355513, by rfl⟩ : syracuseStep 5807351 = 8711027) B8711027
theorem B1908143 : Blo 1271954 1908143 := bstep (se 1 (by rfl) ⟨1431107, by rfl⟩ : syracuseStep 1908143 = 2862215) B2862215
theorem B1908233 : Blo 1271954 1908233 := bstep (se 2 (by rfl) ⟨715587, by rfl⟩ : syracuseStep 1908233 = 1431175) B1431175
theorem B1908263 : Blo 1271954 1908263 := bstep (se 1 (by rfl) ⟨1431197, by rfl⟩ : syracuseStep 1908263 = 2862395) B2862395
theorem B2580007 : Blo 1271954 2580007 := bstep (se 1 (by rfl) ⟨1935005, by rfl⟩ : syracuseStep 2580007 = 3870011) B3870011
theorem B48971303 : Blo 1271954 48971303 := bstep (se 1 (by rfl) ⟨36728477, by rfl⟩ : syracuseStep 48971303 = 73456955) B73456955
theorem B2580025 : Blo 1271954 2580025 := bstep (se 2 (by rfl) ⟨967509, by rfl⟩ : syracuseStep 2580025 = 1935019) B1935019
theorem B18587201 : Blo 1271954 18587201 := bstep (se 2 (by rfl) ⟨6970200, by rfl⟩ : syracuseStep 18587201 = 13940401) B13940401
theorem B2416225 : Blo 1271954 2416225 := bstep (se 2 (by rfl) ⟨906084, by rfl⟩ : syracuseStep 2416225 = 1812169) B1812169
theorem B1908347 : Blo 1271954 1908347 := bstep (se 1 (by rfl) ⟨1431260, by rfl⟩ : syracuseStep 1908347 = 2862521) B2862521
theorem B4832891 : Blo 1271954 4832891 := bstep (se 1 (by rfl) ⟨3624668, by rfl⟩ : syracuseStep 4832891 = 7249337) B7249337
theorem B44064395 : Blo 1271954 44064395 := bstep (se 1 (by rfl) ⟨33048296, by rfl⟩ : syracuseStep 44064395 = 66096593) B66096593
theorem B4079251 : Blo 1271954 4079251 := bstep (se 1 (by rfl) ⟨3059438, by rfl⟩ : syracuseStep 4079251 = 6118877) B6118877
theorem B6528761 : Blo 1271954 6528761 := bstep (se 2 (by rfl) ⟨2448285, by rfl⟩ : syracuseStep 6528761 = 4896571) B4896571
theorem B1908473 : Blo 1271954 1908473 := bstep (se 2 (by rfl) ⟨715677, by rfl⟩ : syracuseStep 1908473 = 1431355) B1431355
theorem B5439275 : Blo 1271954 5439275 := bstep (se 1 (by rfl) ⟨4079456, by rfl⟩ : syracuseStep 5439275 = 8158913) B8158913
theorem B1908575 : Blo 1271954 1908575 := bstep (se 1 (by rfl) ⟨1431431, by rfl⟩ : syracuseStep 1908575 = 2862863) B2862863
theorem B1908587 : Blo 1271954 1908587 := bstep (se 1 (by rfl) ⟨1431440, by rfl⟩ : syracuseStep 1908587 = 2862881) B2862881
theorem B2719595 : Blo 1271954 2719595 := bstep (se 1 (by rfl) ⟨2039696, by rfl⟩ : syracuseStep 2719595 = 4079393) B4079393
theorem B2416567 : Blo 1271954 2416567 := bstep (se 1 (by rfl) ⟨1812425, by rfl⟩ : syracuseStep 2416567 = 3624851) B3624851
theorem B9174971 : Blo 1271954 9174971 := bstep (se 1 (by rfl) ⟨6881228, by rfl⟩ : syracuseStep 9174971 = 13762457) B13762457
theorem B6447113 : Blo 1271954 6447113 := bstep (se 2 (by rfl) ⟨2417667, by rfl⟩ : syracuseStep 6447113 = 4835335) B4835335
theorem B6447275 : Blo 1271954 6447275 := bstep (se 1 (by rfl) ⟨4835456, by rfl⟩ : syracuseStep 6447275 = 9670913) B9670913
theorem B1909001 : Blo 1271954 1909001 := bstep (se 2 (by rfl) ⟨715875, by rfl⟩ : syracuseStep 1909001 = 1431751) B1431751
theorem B69714269 : Blo 1271954 69714269 := bstep (se 3 (by rfl) ⟨13071425, by rfl⟩ : syracuseStep 69714269 = 26142851) B26142851
theorem B5587307 : Blo 1271954 5587307 := bstep (se 1 (by rfl) ⟨4190480, by rfl⟩ : syracuseStep 5587307 = 8380961) B8380961
theorem B1909103 : Blo 1271954 1909103 := bstep (se 1 (by rfl) ⟨1431827, by rfl⟩ : syracuseStep 1909103 = 2863655) B2863655
theorem B2941367 : Blo 1271954 2941367 := bstep (se 1 (by rfl) ⟨2206025, by rfl⟩ : syracuseStep 2941367 = 4412051) B4412051
theorem B1909319 : Blo 1271954 1909319 := bstep (se 1 (by rfl) ⟨1431989, by rfl⟩ : syracuseStep 1909319 = 2863979) B2863979
theorem B4833863 : Blo 1271954 4833863 := bstep (se 1 (by rfl) ⟨3625397, by rfl⟩ : syracuseStep 4833863 = 7250795) B7250795
theorem B1909355 : Blo 1271954 1909355 := bstep (se 1 (by rfl) ⟨1432016, by rfl⟩ : syracuseStep 1909355 = 2864033) B2864033
theorem B2417273 : Blo 1271954 2417273 := bstep (se 2 (by rfl) ⟨906477, by rfl⟩ : syracuseStep 2417273 = 1812955) B1812955
theorem B10871441 : Blo 1271954 10871441 := bstep (se 2 (by rfl) ⟨4076790, by rfl⟩ : syracuseStep 10871441 = 8153581) B8153581
theorem B6447761 : Blo 1271954 6447761 := bstep (se 2 (by rfl) ⟨2417910, by rfl⟩ : syracuseStep 6447761 = 4835821) B4835821
theorem B6120107 : Blo 1271954 6120107 := bstep (se 1 (by rfl) ⟨4590080, by rfl⟩ : syracuseStep 6120107 = 9180161) B9180161
theorem B198263477 : Blo 1271954 198263477 := bstep (se 5 (by rfl) ⟨9293600, by rfl⟩ : syracuseStep 198263477 = 18587201) B18587201
theorem B2146999 : Blo 1271954 2146999 := bstep (se 1 (by rfl) ⟨1610249, by rfl⟩ : syracuseStep 2146999 = 3220499) B3220499
theorem B1909583 : Blo 1271954 1909583 := bstep (se 1 (by rfl) ⟨1432187, by rfl⟩ : syracuseStep 1909583 = 2864375) B2864375
theorem B3056555 : Blo 1271954 3056555 := bstep (se 1 (by rfl) ⟨2292416, by rfl⟩ : syracuseStep 3056555 = 4584833) B4584833
theorem B2720731 : Blo 1271954 2720731 := bstep (se 1 (by rfl) ⟨2040548, by rfl⟩ : syracuseStep 2720731 = 4081097) B4081097
theorem B2147303 : Blo 1271954 2147303 := bstep (se 1 (by rfl) ⟨1610477, by rfl⟩ : syracuseStep 2147303 = 3220955) B3220955
theorem B12239909 : Blo 1271954 12239909 := bstep (se 4 (by rfl) ⟨1147491, by rfl⟩ : syracuseStep 12239909 = 2294983) B2294983
theorem B3220519 : Blo 1271954 3220519 := bstep (se 1 (by rfl) ⟨2415389, by rfl⟩ : syracuseStep 3220519 = 4830779) B4830779
theorem B4080737 : Blo 1271954 4080737 := bstep (se 2 (by rfl) ⟨1530276, by rfl⟩ : syracuseStep 4080737 = 3060553) B3060553
theorem B6112381 : Blo 1271954 6112381 := bstep (se 3 (by rfl) ⟨1146071, by rfl⟩ : syracuseStep 6112381 = 2292143) B2292143
theorem B1909979 : Blo 1271954 1909979 := bstep (se 1 (by rfl) ⟨1432484, by rfl⟩ : syracuseStep 1909979 = 2864969) B2864969
theorem B9659735 : Blo 1271954 9659735 := bstep (se 1 (by rfl) ⟨7244801, by rfl⟩ : syracuseStep 9659735 = 14489603) B14489603
theorem B1910153 : Blo 1271954 1910153 := bstep (se 2 (by rfl) ⟨716307, by rfl⟩ : syracuseStep 1910153 = 1432615) B1432615
theorem B3622333 : Blo 1271954 3622333 := bstep (se 3 (by rfl) ⟨679187, by rfl⟩ : syracuseStep 3622333 = 1358375) B1358375
theorem B3220985 : Blo 1271954 3220985 := bstep (se 2 (by rfl) ⟨1207869, by rfl⟩ : syracuseStep 3220985 = 2415739) B2415739
theorem B2418169 : Blo 1271954 2418169 := bstep (se 2 (by rfl) ⟨906813, by rfl⟩ : syracuseStep 2418169 = 1813627) B1813627
theorem B7251545 : Blo 1271954 7251545 := bstep (se 2 (by rfl) ⟨2719329, by rfl⟩ : syracuseStep 7251545 = 5438659) B5438659
theorem B6440633 : Blo 1271954 6440633 := bstep (se 2 (by rfl) ⟨2415237, by rfl⟩ : syracuseStep 6440633 = 4830475) B4830475
theorem B1910507 : Blo 1271954 1910507 := bstep (se 1 (by rfl) ⟨1432880, by rfl⟩ : syracuseStep 1910507 = 2865761) B2865761
theorem B2418473 : Blo 1271954 2418473 := bstep (se 2 (by rfl) ⟨906927, by rfl⟩ : syracuseStep 2418473 = 1813855) B1813855
theorem B26109773 : Blo 1271954 26109773 := bstep (se 3 (by rfl) ⟨4895582, by rfl⟩ : syracuseStep 26109773 = 9791165) B9791165
theorem B4835153 : Blo 1271954 4835153 := bstep (se 2 (by rfl) ⟨1813182, by rfl⟩ : syracuseStep 4835153 = 3626365) B3626365
theorem B1910735 : Blo 1271954 1910735 := bstep (se 1 (by rfl) ⟨1433051, by rfl⟩ : syracuseStep 1910735 = 2866103) B2866103
theorem B2148457 : Blo 1271954 2148457 := bstep (se 2 (by rfl) ⟨805671, by rfl⟩ : syracuseStep 2148457 = 1611343) B1611343
theorem B3221633 : Blo 1271954 3221633 := bstep (se 2 (by rfl) ⟨1208112, by rfl⟩ : syracuseStep 3221633 = 2416225) B2416225
theorem B8153273 : Blo 1271954 8153273 := bstep (se 2 (by rfl) ⟨3057477, by rfl⟩ : syracuseStep 8153273 = 6114955) B6114955
theorem B4835609 : Blo 1271954 4835609 := bstep (se 2 (by rfl) ⟨1813353, by rfl⟩ : syracuseStep 4835609 = 3626707) B3626707
theorem B7252253 : Blo 1271954 7252253 := bstep (se 3 (by rfl) ⟨1359797, by rfl⟩ : syracuseStep 7252253 = 2719595) B2719595
theorem B1272095 : Blo 1271954 1272095 := bstep (se 1 (by rfl) ⟨954071, by rfl⟩ : syracuseStep 1272095 = 1908143) B1908143
theorem B1272155 : Blo 1271954 1272155 := bstep (se 1 (by rfl) ⟨954116, by rfl⟩ : syracuseStep 1272155 = 1908233) B1908233
theorem B1272175 : Blo 1271954 1272175 := bstep (se 1 (by rfl) ⟨954131, by rfl⟩ : syracuseStep 1272175 = 1908263) B1908263
theorem B32647535 : Blo 1271954 32647535 := bstep (se 1 (by rfl) ⟨24485651, by rfl⟩ : syracuseStep 32647535 = 48971303) B48971303
theorem B10873217 : Blo 1271954 10873217 := bstep (se 2 (by rfl) ⟨4077456, by rfl⟩ : syracuseStep 10873217 = 8154913) B8154913
theorem B1272231 : Blo 1271954 1272231 := bstep (se 1 (by rfl) ⟨954173, by rfl⟩ : syracuseStep 1272231 = 1908347) B1908347
theorem B3221927 : Blo 1271954 3221927 := bstep (se 1 (by rfl) ⟨2416445, by rfl⟩ : syracuseStep 3221927 = 4832891) B4832891
theorem B4352507 : Blo 1271954 4352507 := bstep (se 1 (by rfl) ⟨3264380, by rfl⟩ : syracuseStep 4352507 = 6528761) B6528761
theorem B1272315 : Blo 1271954 1272315 := bstep (se 1 (by rfl) ⟨954236, by rfl⟩ : syracuseStep 1272315 = 1908473) B1908473
theorem B1272383 : Blo 1271954 1272383 := bstep (se 1 (by rfl) ⟨954287, by rfl⟩ : syracuseStep 1272383 = 1908575) B1908575
theorem B1272391 : Blo 1271954 1272391 := bstep (se 1 (by rfl) ⟨954293, by rfl⟩ : syracuseStep 1272391 = 1908587) B1908587
theorem B3222089 : Blo 1271954 3222089 := bstep (se 2 (by rfl) ⟨1208283, by rfl⟩ : syracuseStep 3222089 = 2416567) B2416567
theorem B1272543 : Blo 1271954 1272543 := bstep (se 1 (by rfl) ⟨954407, by rfl⟩ : syracuseStep 1272543 = 1908815) B1908815
theorem B1272623 : Blo 1271954 1272623 := bstep (se 1 (by rfl) ⟨954467, by rfl⟩ : syracuseStep 1272623 = 1908935) B1908935
theorem B1272731 : Blo 1271954 1272731 := bstep (se 1 (by rfl) ⟨954548, by rfl⟩ : syracuseStep 1272731 = 1909097) B1909097
theorem B12225451 : Blo 1271954 12225451 := bstep (se 1 (by rfl) ⟨9169088, by rfl⟩ : syracuseStep 12225451 = 18338177) B18338177
theorem B3222443 : Blo 1271954 3222443 := bstep (se 1 (by rfl) ⟨2416832, by rfl⟩ : syracuseStep 3222443 = 4833665) B4833665
theorem B1272783 : Blo 1271954 1272783 := bstep (se 1 (by rfl) ⟨954587, by rfl⟩ : syracuseStep 1272783 = 1909175) B1909175
theorem B3058651 : Blo 1271954 3058651 := bstep (se 1 (by rfl) ⟨2293988, by rfl⟩ : syracuseStep 3058651 = 4587977) B4587977
theorem B1272807 : Blo 1271954 1272807 := bstep (se 1 (by rfl) ⟨954605, by rfl⟩ : syracuseStep 1272807 = 1909211) B1909211
theorem B2862071 : Blo 1271954 2862071 := bstep (se 1 (by rfl) ⟨2146553, by rfl⟩ : syracuseStep 2862071 = 4293107) B4293107
theorem B35810383 : Blo 1271954 35810383 := bstep (se 1 (by rfl) ⟨26857787, by rfl⟩ : syracuseStep 35810383 = 53715575) B53715575
theorem B3222625 : Blo 1271954 3222625 := bstep (se 2 (by rfl) ⟨1208484, by rfl⟩ : syracuseStep 3222625 = 2416969) B2416969
theorem B4590715 : Blo 1271954 4590715 := bstep (se 1 (by rfl) ⟨3443036, by rfl⟩ : syracuseStep 4590715 = 6886073) B6886073
theorem B2755871 : Blo 1271954 2755871 := bstep (se 1 (by rfl) ⟨2066903, by rfl⟩ : syracuseStep 2755871 = 4133807) B4133807
theorem B1273119 : Blo 1271954 1273119 := bstep (se 1 (by rfl) ⟨954839, by rfl⟩ : syracuseStep 1273119 = 1909679) B1909679
theorem B9178429 : Blo 1271954 9178429 := bstep (se 3 (by rfl) ⟨1720955, by rfl⟩ : syracuseStep 9178429 = 3441911) B3441911
theorem B6884669 : Blo 1271954 6884669 := bstep (se 3 (by rfl) ⟨1290875, by rfl⟩ : syracuseStep 6884669 = 2581751) B2581751
theorem B1273179 : Blo 1271954 1273179 := bstep (se 1 (by rfl) ⟨954884, by rfl⟩ : syracuseStep 1273179 = 1909769) B1909769
theorem B2862431 : Blo 1271954 2862431 := bstep (se 1 (by rfl) ⟨2146823, by rfl⟩ : syracuseStep 2862431 = 4293647) B4293647
theorem B1273199 : Blo 1271954 1273199 := bstep (se 1 (by rfl) ⟨954899, by rfl⟩ : syracuseStep 1273199 = 1909799) B1909799
theorem B11169143 : Blo 1271954 11169143 := bstep (se 1 (by rfl) ⟨8376857, by rfl⟩ : syracuseStep 11169143 = 16753715) B16753715
theorem B251129231 : Blo 1271954 251129231 := bstep (se 1 (by rfl) ⟨188346923, by rfl⟩ : syracuseStep 251129231 = 376693847) B376693847
theorem B1273255 : Blo 1271954 1273255 := bstep (se 1 (by rfl) ⟨954941, by rfl⟩ : syracuseStep 1273255 = 1909883) B1909883
theorem B4296185 : Blo 1271954 4296185 := bstep (se 2 (by rfl) ⟨1611069, by rfl⟩ : syracuseStep 4296185 = 3222139) B3222139
theorem B1273339 : Blo 1271954 1273339 := bstep (se 1 (by rfl) ⟨955004, by rfl⟩ : syracuseStep 1273339 = 1910009) B1910009
theorem B1273407 : Blo 1271954 1273407 := bstep (se 1 (by rfl) ⟨955055, by rfl⟩ : syracuseStep 1273407 = 1910111) B1910111
theorem B1273415 : Blo 1271954 1273415 := bstep (se 1 (by rfl) ⟨955061, by rfl⟩ : syracuseStep 1273415 = 1910123) B1910123
theorem B6442577 : Blo 1271954 6442577 := bstep (se 2 (by rfl) ⟨2415966, by rfl⟩ : syracuseStep 6442577 = 4831933) B4831933
theorem B27512459 : Blo 1271954 27512459 := bstep (se 1 (by rfl) ⟨20634344, by rfl⟩ : syracuseStep 27512459 = 41268689) B41268689
theorem B44068529 : Blo 1271954 44068529 := bstep (se 2 (by rfl) ⟨16525698, by rfl⟩ : syracuseStep 44068529 = 33051397) B33051397
theorem B1273567 : Blo 1271954 1273567 := bstep (se 1 (by rfl) ⟨955175, by rfl⟩ : syracuseStep 1273567 = 1910351) B1910351
theorem B2862827 : Blo 1271954 2862827 := bstep (se 1 (by rfl) ⟨2147120, by rfl⟩ : syracuseStep 2862827 = 4294241) B4294241
theorem B4296455 : Blo 1271954 4296455 := bstep (se 1 (by rfl) ⟨3222341, by rfl⟩ : syracuseStep 4296455 = 6444683) B6444683
theorem B1273647 : Blo 1271954 1273647 := bstep (se 1 (by rfl) ⟨955235, by rfl⟩ : syracuseStep 1273647 = 1910471) B1910471
theorem B4296509 : Blo 1271954 4296509 := bstep (se 3 (by rfl) ⟨805595, by rfl⟩ : syracuseStep 4296509 = 1611191) B1611191
theorem B2862953 : Blo 1271954 2862953 := bstep (se 2 (by rfl) ⟨1073607, by rfl⟩ : syracuseStep 2862953 = 2147215) B2147215
theorem B1273755 : Blo 1271954 1273755 := bstep (se 1 (by rfl) ⟨955316, by rfl⟩ : syracuseStep 1273755 = 1910633) B1910633
theorem B6115247 : Blo 1271954 6115247 := bstep (se 1 (by rfl) ⟨4586435, by rfl⟩ : syracuseStep 6115247 = 9172871) B9172871
theorem B1273807 : Blo 1271954 1273807 := bstep (se 1 (by rfl) ⟨955355, by rfl⟩ : syracuseStep 1273807 = 1910711) B1910711
theorem B1273831 : Blo 1271954 1273831 := bstep (se 1 (by rfl) ⟨955373, by rfl⟩ : syracuseStep 1273831 = 1910747) B1910747
theorem B3223577 : Blo 1271954 3223577 := bstep (se 2 (by rfl) ⟨1208841, by rfl⟩ : syracuseStep 3223577 = 2417683) B2417683
theorem B3625307 : Blo 1271954 3625307 := bstep (se 1 (by rfl) ⟨2718980, by rfl⟩ : syracuseStep 3625307 = 5437961) B5437961
theorem B3224033 : Blo 1271954 3224033 := bstep (se 2 (by rfl) ⟨1209012, by rfl⟩ : syracuseStep 3224033 = 2418025) B2418025
theorem B3224083 : Blo 1271954 3224083 := bstep (se 1 (by rfl) ⟨2418062, by rfl⟩ : syracuseStep 3224083 = 4836125) B4836125
theorem B5804615 : Blo 1271954 5804615 := bstep (se 1 (by rfl) ⟨4353461, by rfl⟩ : syracuseStep 5804615 = 8706923) B8706923
theorem B2863799 : Blo 1271954 2863799 := bstep (se 1 (by rfl) ⟨2147849, by rfl⟩ : syracuseStep 2863799 = 4295699) B4295699
theorem B1610543 : Blo 1271954 1610543 := bstep (se 1 (by rfl) ⟨1207907, by rfl⟩ : syracuseStep 1610543 = 2415815) B2415815
theorem B4133711 : Blo 1271954 4133711 := bstep (se 1 (by rfl) ⟨3100283, by rfl⟩ : syracuseStep 4133711 = 6200567) B6200567
theorem B3871567 : Blo 1271954 3871567 := bstep (se 1 (by rfl) ⟨2903675, by rfl⟩ : syracuseStep 3871567 = 5807351) B5807351
theorem B2864015 : Blo 1271954 2864015 := bstep (se 1 (by rfl) ⟨2148011, by rfl⟩ : syracuseStep 2864015 = 4296023) B4296023
theorem B3060775 : Blo 1271954 3060775 := bstep (se 1 (by rfl) ⟨2295581, by rfl⟩ : syracuseStep 3060775 = 4591163) B4591163
theorem B14496893 : Blo 1271954 14496893 := bstep (se 3 (by rfl) ⟨2718167, by rfl⟩ : syracuseStep 14496893 = 5436335) B5436335
theorem B3626183 : Blo 1271954 3626183 := bstep (se 1 (by rfl) ⟨2719637, by rfl⟩ : syracuseStep 3626183 = 5439275) B5439275
theorem B6116647 : Blo 1271954 6116647 := bstep (se 1 (by rfl) ⟨4587485, by rfl⟩ : syracuseStep 6116647 = 9174971) B9174971
theorem B10868093 : Blo 1271954 10868093 := bstep (se 3 (by rfl) ⟨2037767, by rfl⟩ : syracuseStep 10868093 = 4075535) B4075535
theorem B1431103 : Blo 1271954 1431103 := bstep (se 1 (by rfl) ⟨1073327, by rfl⟩ : syracuseStep 1431103 = 2146655) B2146655
theorem B2864735 : Blo 1271954 2864735 := bstep (se 1 (by rfl) ⟨2148551, by rfl⟩ : syracuseStep 2864735 = 4297103) B4297103
theorem B2864951 : Blo 1271954 2864951 := bstep (se 1 (by rfl) ⟨2148713, by rfl⟩ : syracuseStep 2864951 = 4297427) B4297427
theorem B2717545 : Blo 1271954 2717545 := bstep (se 2 (by rfl) ⟨1019079, by rfl⟩ : syracuseStep 2717545 = 2038159) B2038159
theorem B6445007 : Blo 1271954 6445007 := bstep (se 1 (by rfl) ⟨4833755, by rfl⟩ : syracuseStep 6445007 = 9667511) B9667511
theorem B4831265 : Blo 1271954 4831265 := bstep (se 2 (by rfl) ⟨1811724, by rfl⟩ : syracuseStep 4831265 = 3623449) B3623449
theorem B2865257 : Blo 1271954 2865257 := bstep (se 2 (by rfl) ⟨1074471, by rfl⟩ : syracuseStep 2865257 = 2148943) B2148943
theorem B13064327 : Blo 1271954 13064327 := bstep (se 1 (by rfl) ⟨9798245, by rfl⟩ : syracuseStep 13064327 = 19596491) B19596491
theorem B7444759 : Blo 1271954 7444759 := bstep (se 1 (by rfl) ⟨5583569, by rfl⟩ : syracuseStep 7444759 = 11167139) B11167139
theorem B1431931 : Blo 1271954 1431931 := bstep (se 1 (by rfl) ⟨1073948, by rfl⟩ : syracuseStep 1431931 = 2147897) B2147897
theorem B6535567 : Blo 1271954 6535567 := bstep (se 1 (by rfl) ⟨4901675, by rfl⟩ : syracuseStep 6535567 = 9803351) B9803351
theorem B6879671 : Blo 1271954 6879671 := bstep (se 1 (by rfl) ⟨5159753, by rfl⟩ : syracuseStep 6879671 = 10319507) B10319507
theorem B7248311 : Blo 1271954 7248311 := bstep (se 1 (by rfl) ⟨5436233, by rfl⟩ : syracuseStep 7248311 = 10872467) B10872467
theorem B2038267 : Blo 1271954 2038267 := bstep (se 1 (by rfl) ⟨1528700, by rfl⟩ : syracuseStep 2038267 = 3057401) B3057401
theorem B2292295 : Blo 1271954 2292295 := bstep (se 1 (by rfl) ⟨1719221, by rfl⟩ : syracuseStep 2292295 = 3438443) B3438443
theorem B2865743 : Blo 1271954 2865743 := bstep (se 1 (by rfl) ⟨2149307, by rfl⟩ : syracuseStep 2865743 = 4298615) B4298615
theorem B4299371 : Blo 1271954 4299371 := bstep (se 1 (by rfl) ⟨3224528, by rfl⟩ : syracuseStep 4299371 = 6449057) B6449057
theorem B4831919 : Blo 1271954 4831919 := bstep (se 1 (by rfl) ⟨3623939, by rfl⟩ : syracuseStep 4831919 = 7247879) B7247879
theorem B2865887 : Blo 1271954 2865887 := bstep (se 1 (by rfl) ⟨2149415, by rfl⟩ : syracuseStep 2865887 = 4298831) B4298831
theorem B3627767 : Blo 1271954 3627767 := bstep (se 1 (by rfl) ⟨2720825, by rfl⟩ : syracuseStep 3627767 = 5441651) B5441651
theorem B1432399 : Blo 1271954 1432399 := bstep (se 1 (by rfl) ⟨1074299, by rfl⟩ : syracuseStep 1432399 = 2148599) B2148599
theorem B6445979 : Blo 1271954 6445979 := bstep (se 1 (by rfl) ⟨4834484, by rfl⟩ : syracuseStep 6445979 = 9668969) B9668969
theorem B2866139 : Blo 1271954 2866139 := bstep (se 1 (by rfl) ⟨2149604, by rfl⟩ : syracuseStep 2866139 = 4299209) B4299209
theorem B27524215 : Blo 1271954 27524215 := bstep (se 1 (by rfl) ⟨20643161, by rfl⟩ : syracuseStep 27524215 = 41286323) B41286323
theorem B2866319 : Blo 1271954 2866319 := bstep (se 1 (by rfl) ⟨2149739, by rfl⟩ : syracuseStep 2866319 = 4299479) B4299479
theorem B7249085 : Blo 1271954 7249085 := bstep (se 3 (by rfl) ⟨1359203, by rfl⟩ : syracuseStep 7249085 = 2718407) B2718407
theorem B1359067 : Blo 1271954 1359067 := bstep (se 1 (by rfl) ⟨1019300, by rfl⟩ : syracuseStep 1359067 = 2038601) B2038601
theorem B1432795 : Blo 1271954 1432795 := bstep (se 1 (by rfl) ⟨1074596, by rfl⟩ : syracuseStep 1432795 = 2149193) B2149193
theorem B1907945 : Blo 1271954 1907945 := bstep (se 2 (by rfl) ⟨715479, by rfl⟩ : syracuseStep 1907945 = 1430959) B1430959
theorem B1907999 : Blo 1271954 1907999 := bstep (se 1 (by rfl) ⟨1430999, by rfl⟩ : syracuseStep 1907999 = 2861999) B2861999
theorem B6446465 : Blo 1271954 6446465 := bstep (se 2 (by rfl) ⟨2417424, by rfl⟩ : syracuseStep 6446465 = 4834849) B4834849
theorem B36724103 : Blo 1271954 36724103 := bstep (se 1 (by rfl) ⟨27543077, by rfl⟩ : syracuseStep 36724103 = 55086155) B55086155
theorem B3440009 : Blo 1271954 3440009 := bstep (se 2 (by rfl) ⟨1290003, by rfl⟩ : syracuseStep 3440009 = 2580007) B2580007
theorem B3440033 : Blo 1271954 3440033 := bstep (se 2 (by rfl) ⟨1290012, by rfl⟩ : syracuseStep 3440033 = 2580025) B2580025
theorem B1908167 : Blo 1271954 1908167 := bstep (se 1 (by rfl) ⟨1431125, by rfl⟩ : syracuseStep 1908167 = 2862251) B2862251
theorem B1433083 : Blo 1271954 1433083 := bstep (se 1 (by rfl) ⟨1074812, by rfl⟩ : syracuseStep 1433083 = 2149625) B2149625
theorem B5439001 : Blo 1271954 5439001 := bstep (se 2 (by rfl) ⟨2039625, by rfl⟩ : syracuseStep 5439001 = 4079251) B4079251
theorem B29376263 : Blo 1271954 29376263 := bstep (se 1 (by rfl) ⟨22032197, by rfl⟩ : syracuseStep 29376263 = 44064395) B44064395
theorem B50290465 : Blo 1271954 50290465 := bstep (se 2 (by rfl) ⟨18858924, by rfl⟩ : syracuseStep 50290465 = 37717849) B37717849
theorem B1908521 : Blo 1271954 1908521 := bstep (se 2 (by rfl) ⟨715695, by rfl⟩ : syracuseStep 1908521 = 1431391) B1431391
theorem B1908527 : Blo 1271954 1908527 := bstep (se 1 (by rfl) ⟨1431395, by rfl⟩ : syracuseStep 1908527 = 2862791) B2862791
theorem B2416871 : Blo 1271954 2416871 := bstep (se 1 (by rfl) ⟨1812653, by rfl⟩ : syracuseStep 2416871 = 3625307) B3625307
theorem B4080071 : Blo 1271954 4080071 := bstep (se 1 (by rfl) ⟨3060053, by rfl⟩ : syracuseStep 4080071 = 6120107) B6120107
theorem B1909199 : Blo 1271954 1909199 := bstep (se 1 (by rfl) ⟨1431899, by rfl⟩ : syracuseStep 1909199 = 2863799) B2863799
theorem B1909241 : Blo 1271954 1909241 := bstep (se 2 (by rfl) ⟨715965, by rfl⟩ : syracuseStep 1909241 = 1431931) B1431931
theorem B1909343 : Blo 1271954 1909343 := bstep (se 1 (by rfl) ⟨1432007, by rfl⟩ : syracuseStep 1909343 = 2864015) B2864015
theorem B8159939 : Blo 1271954 8159939 := bstep (se 1 (by rfl) ⟨6119954, by rfl⟩ : syracuseStep 8159939 = 12239909) B12239909
theorem B3056393 : Blo 1271954 3056393 := bstep (se 2 (by rfl) ⟨1146147, by rfl⟩ : syracuseStep 3056393 = 2292295) B2292295
theorem B2417455 : Blo 1271954 2417455 := bstep (se 1 (by rfl) ⟨1813091, by rfl⟩ : syracuseStep 2417455 = 3626183) B3626183
theorem B6439823 : Blo 1271954 6439823 := bstep (se 1 (by rfl) ⟨4829867, by rfl⟩ : syracuseStep 6439823 = 9659735) B9659735
theorem B2147323 : Blo 1271954 2147323 := bstep (se 1 (by rfl) ⟨1610492, by rfl⟩ : syracuseStep 2147323 = 3220985) B3220985
theorem B4834363 : Blo 1271954 4834363 := bstep (se 1 (by rfl) ⟨3625772, by rfl⟩ : syracuseStep 4834363 = 7251545) B7251545
theorem B1909823 : Blo 1271954 1909823 := bstep (se 1 (by rfl) ⟨1432367, by rfl⟩ : syracuseStep 1909823 = 2864735) B2864735
theorem B1909865 : Blo 1271954 1909865 := bstep (se 2 (by rfl) ⟨716199, by rfl⟩ : syracuseStep 1909865 = 1432399) B1432399
theorem B4293755 : Blo 1271954 4293755 := bstep (se 1 (by rfl) ⟨3220316, by rfl⟩ : syracuseStep 4293755 = 6440633) B6440633
theorem B1909967 : Blo 1271954 1909967 := bstep (se 1 (by rfl) ⟨1432475, by rfl⟩ : syracuseStep 1909967 = 2864951) B2864951
theorem B3220843 : Blo 1271954 3220843 := bstep (se 1 (by rfl) ⟨2415632, by rfl⟩ : syracuseStep 3220843 = 4831265) B4831265
theorem B4294025 : Blo 1271954 4294025 := bstep (se 2 (by rfl) ⟨1610259, by rfl⟩ : syracuseStep 4294025 = 3220519) B3220519
theorem B4081033 : Blo 1271954 4081033 := bstep (se 2 (by rfl) ⟨1530387, by rfl⟩ : syracuseStep 4081033 = 3060775) B3060775
theorem B1910171 : Blo 1271954 1910171 := bstep (se 1 (by rfl) ⟨1432628, by rfl⟩ : syracuseStep 1910171 = 2865257) B2865257
theorem B2147755 : Blo 1271954 2147755 := bstep (se 1 (by rfl) ⟨1610816, by rfl⟩ : syracuseStep 2147755 = 3221633) B3221633
theorem B8709551 : Blo 1271954 8709551 := bstep (se 1 (by rfl) ⟨6532163, by rfl⟩ : syracuseStep 8709551 = 13064327) B13064327
theorem B6120953 : Blo 1271954 6120953 := bstep (se 2 (by rfl) ⟨2295357, by rfl⟩ : syracuseStep 6120953 = 4590715) B4590715
theorem B4834835 : Blo 1271954 4834835 := bstep (se 1 (by rfl) ⟨3626126, by rfl⟩ : syracuseStep 4834835 = 7252253) B7252253
theorem B2147951 : Blo 1271954 2147951 := bstep (se 1 (by rfl) ⟨1610963, by rfl⟩ : syracuseStep 2147951 = 3221927) B3221927
theorem B1812089 : Blo 1271954 1812089 := bstep (se 2 (by rfl) ⟨679533, by rfl⟩ : syracuseStep 1812089 = 1359067) B1359067
theorem B1910393 : Blo 1271954 1910393 := bstep (se 2 (by rfl) ⟨716397, by rfl⟩ : syracuseStep 1910393 = 1432795) B1432795
theorem B2901671 : Blo 1271954 2901671 := bstep (se 1 (by rfl) ⟨2176253, by rfl⟩ : syracuseStep 2901671 = 4352507) B4352507
theorem B2148059 : Blo 1271954 2148059 := bstep (se 1 (by rfl) ⟨1611044, by rfl⟩ : syracuseStep 2148059 = 3222089) B3222089
theorem B1910495 : Blo 1271954 1910495 := bstep (se 1 (by rfl) ⟨1432871, by rfl⟩ : syracuseStep 1910495 = 2865743) B2865743
theorem B3221279 : Blo 1271954 3221279 := bstep (se 1 (by rfl) ⟨2415959, by rfl⟩ : syracuseStep 3221279 = 4831919) B4831919
theorem B1910591 : Blo 1271954 1910591 := bstep (se 1 (by rfl) ⟨1432943, by rfl⟩ : syracuseStep 1910591 = 2865887) B2865887
theorem B2418511 : Blo 1271954 2418511 := bstep (se 1 (by rfl) ⟨1813883, by rfl⟩ : syracuseStep 2418511 = 3627767) B3627767
theorem B2148295 : Blo 1271954 2148295 := bstep (se 1 (by rfl) ⟨1611221, by rfl⟩ : syracuseStep 2148295 = 3222443) B3222443
theorem B1910759 : Blo 1271954 1910759 := bstep (se 1 (by rfl) ⟨1433069, by rfl⟩ : syracuseStep 1910759 = 2866139) B2866139
theorem B1910777 : Blo 1271954 1910777 := bstep (se 2 (by rfl) ⟨716541, by rfl⟩ : syracuseStep 1910777 = 1433083) B1433083
theorem B7252001 : Blo 1271954 7252001 := bstep (se 2 (by rfl) ⟨2719500, by rfl⟩ : syracuseStep 7252001 = 5439001) B5439001
theorem B1910879 : Blo 1271954 1910879 := bstep (se 1 (by rfl) ⟨1433159, by rfl⟩ : syracuseStep 1910879 = 2866319) B2866319
theorem B4294781 : Blo 1271954 4294781 := bstep (se 3 (by rfl) ⟨805271, by rfl⟩ : syracuseStep 4294781 = 1610543) B1610543
theorem B1271963 : Blo 1271954 1271963 := bstep (se 1 (by rfl) ⟨953972, by rfl⟩ : syracuseStep 1271963 = 1907945) B1907945
theorem B1271999 : Blo 1271954 1271999 := bstep (se 1 (by rfl) ⟨953999, by rfl⟩ : syracuseStep 1271999 = 1907999) B1907999
theorem B1837247 : Blo 1271954 1837247 := bstep (se 1 (by rfl) ⟨1377935, by rfl⟩ : syracuseStep 1837247 = 2755871) B2755871
theorem B4589779 : Blo 1271954 4589779 := bstep (se 1 (by rfl) ⟨3442334, by rfl⟩ : syracuseStep 4589779 = 6884669) B6884669
theorem B1272111 : Blo 1271954 1272111 := bstep (se 1 (by rfl) ⟨954083, by rfl⟩ : syracuseStep 1272111 = 1908167) B1908167
theorem B67053953 : Blo 1271954 67053953 := bstep (se 2 (by rfl) ⟨25145232, by rfl⟩ : syracuseStep 67053953 = 50290465) B50290465
theorem B4295051 : Blo 1271954 4295051 := bstep (se 1 (by rfl) ⟨3221288, by rfl⟩ : syracuseStep 4295051 = 6442577) B6442577
theorem B29379019 : Blo 1271954 29379019 := bstep (se 1 (by rfl) ⟨22034264, by rfl⟩ : syracuseStep 29379019 = 44068529) B44068529
theorem B3623393 : Blo 1271954 3623393 := bstep (se 2 (by rfl) ⟨1358772, by rfl⟩ : syracuseStep 3623393 = 2717545) B2717545
theorem B1272347 : Blo 1271954 1272347 := bstep (se 1 (by rfl) ⟨954260, by rfl⟩ : syracuseStep 1272347 = 1908521) B1908521
theorem B1272351 : Blo 1271954 1272351 := bstep (se 1 (by rfl) ⟨954263, by rfl⟩ : syracuseStep 1272351 = 1908527) B1908527
theorem B2149051 : Blo 1271954 2149051 := bstep (se 1 (by rfl) ⟨1611788, by rfl⟩ : syracuseStep 2149051 = 3223577) B3223577
theorem B1272667 : Blo 1271954 1272667 := bstep (se 1 (by rfl) ⟨954500, by rfl⟩ : syracuseStep 1272667 = 1909001) B1909001
theorem B46476179 : Blo 1271954 46476179 := bstep (se 1 (by rfl) ⟨34857134, by rfl⟩ : syracuseStep 46476179 = 69714269) B69714269
theorem B1272735 : Blo 1271954 1272735 := bstep (se 1 (by rfl) ⟨954551, by rfl⟩ : syracuseStep 1272735 = 1909103) B1909103
theorem B10881965 : Blo 1271954 10881965 := bstep (se 3 (by rfl) ⟨2040368, by rfl⟩ : syracuseStep 10881965 = 4080737) B4080737
theorem B2149355 : Blo 1271954 2149355 := bstep (se 1 (by rfl) ⟨1612016, by rfl⟩ : syracuseStep 2149355 = 3224033) B3224033
theorem B3869743 : Blo 1271954 3869743 := bstep (se 1 (by rfl) ⟨2902307, by rfl⟩ : syracuseStep 3869743 = 5804615) B5804615
theorem B1272879 : Blo 1271954 1272879 := bstep (se 1 (by rfl) ⟨954659, by rfl⟩ : syracuseStep 1272879 = 1909319) B1909319
theorem B3222575 : Blo 1271954 3222575 := bstep (se 1 (by rfl) ⟨2416931, by rfl⟩ : syracuseStep 3222575 = 4833863) B4833863
theorem B1272903 : Blo 1271954 1272903 := bstep (se 1 (by rfl) ⟨954677, by rfl⟩ : syracuseStep 1272903 = 1909355) B1909355
theorem B1273055 : Blo 1271954 1273055 := bstep (se 1 (by rfl) ⟨954791, by rfl⟩ : syracuseStep 1273055 = 1909583) B1909583
theorem B1273319 : Blo 1271954 1273319 := bstep (se 1 (by rfl) ⟨954989, by rfl⟩ : syracuseStep 1273319 = 1909979) B1909979
theorem B2862665 : Blo 1271954 2862665 := bstep (se 2 (by rfl) ⟨1073499, by rfl⟩ : syracuseStep 2862665 = 2146999) B2146999
theorem B7245395 : Blo 1271954 7245395 := bstep (se 1 (by rfl) ⟨5434046, by rfl⟩ : syracuseStep 7245395 = 10868093) B10868093
theorem B1273435 : Blo 1271954 1273435 := bstep (se 1 (by rfl) ⟨955076, by rfl⟩ : syracuseStep 1273435 = 1910153) B1910153
theorem B7843645 : Blo 1271954 7843645 := bstep (se 3 (by rfl) ⟨1470683, by rfl⟩ : syracuseStep 7843645 = 2941367) B2941367
theorem B1273671 : Blo 1271954 1273671 := bstep (se 1 (by rfl) ⟨955253, by rfl⟩ : syracuseStep 1273671 = 1910507) B1910507
theorem B3223435 : Blo 1271954 3223435 := bstep (se 1 (by rfl) ⟨2417576, by rfl⟩ : syracuseStep 3223435 = 4835153) B4835153
theorem B4296671 : Blo 1271954 4296671 := bstep (se 1 (by rfl) ⟨3222503, by rfl⟩ : syracuseStep 4296671 = 6445007) B6445007
theorem B1273823 : Blo 1271954 1273823 := bstep (se 1 (by rfl) ⟨955367, by rfl⟩ : syracuseStep 1273823 = 1910735) B1910735
theorem B47747177 : Blo 1271954 47747177 := bstep (se 2 (by rfl) ⟨17905191, by rfl⟩ : syracuseStep 47747177 = 35810383) B35810383
theorem B5435515 : Blo 1271954 5435515 := bstep (se 1 (by rfl) ⟨4076636, by rfl⟩ : syracuseStep 5435515 = 8153273) B8153273
theorem B4296833 : Blo 1271954 4296833 := bstep (se 2 (by rfl) ⟨1611312, by rfl⟩ : syracuseStep 4296833 = 3222625) B3222625
theorem B3223739 : Blo 1271954 3223739 := bstep (se 1 (by rfl) ⟨2417804, by rfl⟩ : syracuseStep 3223739 = 4835609) B4835609
theorem B8155529 : Blo 1271954 8155529 := bstep (se 2 (by rfl) ⟨3058323, by rfl⟩ : syracuseStep 8155529 = 6116647) B6116647
theorem B20648357 : Blo 1271954 20648357 := bstep (se 4 (by rfl) ⟨1935783, by rfl⟩ : syracuseStep 20648357 = 3871567) B3871567
theorem B4829777 : Blo 1271954 4829777 := bstep (se 2 (by rfl) ⟨1811166, by rfl⟩ : syracuseStep 4829777 = 3622333) B3622333
theorem B4297319 : Blo 1271954 4297319 := bstep (se 1 (by rfl) ⟨3222989, by rfl⟩ : syracuseStep 4297319 = 6445979) B6445979
theorem B3224225 : Blo 1271954 3224225 := bstep (se 2 (by rfl) ⟨1209084, by rfl⟩ : syracuseStep 3224225 = 2418169) B2418169
theorem B11023229 : Blo 1271954 11023229 := bstep (se 3 (by rfl) ⟨2066855, by rfl⟩ : syracuseStep 11023229 = 4133711) B4133711
theorem B4297643 : Blo 1271954 4297643 := bstep (se 1 (by rfl) ⟨3223232, by rfl⟩ : syracuseStep 4297643 = 6446465) B6446465
theorem B24482735 : Blo 1271954 24482735 := bstep (se 1 (by rfl) ⟨18362051, by rfl⟩ : syracuseStep 24482735 = 36724103) B36724103
theorem B2864123 : Blo 1271954 2864123 := bstep (se 1 (by rfl) ⟨2148092, by rfl⟩ : syracuseStep 2864123 = 4296185) B4296185
theorem B19584175 : Blo 1271954 19584175 := bstep (se 1 (by rfl) ⟨14688131, by rfl⟩ : syracuseStep 19584175 = 29376263) B29376263
theorem B2864303 : Blo 1271954 2864303 := bstep (se 1 (by rfl) ⟨2148227, by rfl⟩ : syracuseStep 2864303 = 4296455) B4296455
theorem B2864339 : Blo 1271954 2864339 := bstep (se 1 (by rfl) ⟨2148254, by rfl⟩ : syracuseStep 2864339 = 4296509) B4296509
theorem B4076831 : Blo 1271954 4076831 := bstep (se 1 (by rfl) ⟨3057623, by rfl⟩ : syracuseStep 4076831 = 6115247) B6115247
theorem B4298075 : Blo 1271954 4298075 := bstep (se 1 (by rfl) ⟨3223556, by rfl⟩ : syracuseStep 4298075 = 6447113) B6447113
theorem B4298183 : Blo 1271954 4298183 := bstep (se 1 (by rfl) ⟨3223637, by rfl⟩ : syracuseStep 4298183 = 6447275) B6447275
theorem B2864609 : Blo 1271954 2864609 := bstep (se 2 (by rfl) ⟨1074228, by rfl⟩ : syracuseStep 2864609 = 2148457) B2148457
theorem B3724871 : Blo 1271954 3724871 := bstep (se 1 (by rfl) ⟨2793653, by rfl⟩ : syracuseStep 3724871 = 5587307) B5587307
theorem B9926345 : Blo 1271954 9926345 := bstep (se 2 (by rfl) ⟨3722379, by rfl⟩ : syracuseStep 9926345 = 7444759) B7444759
theorem B1611515 : Blo 1271954 1611515 := bstep (se 1 (by rfl) ⟨1208636, by rfl⟩ : syracuseStep 1611515 = 2417273) B2417273
theorem B7247627 : Blo 1271954 7247627 := bstep (se 1 (by rfl) ⟨5435720, by rfl⟩ : syracuseStep 7247627 = 10871441) B10871441
theorem B4298507 : Blo 1271954 4298507 := bstep (se 1 (by rfl) ⟨3223880, by rfl⟩ : syracuseStep 4298507 = 6447761) B6447761
theorem B132175651 : Blo 1271954 132175651 := bstep (se 1 (by rfl) ⟨99131738, by rfl⟩ : syracuseStep 132175651 = 198263477) B198263477
theorem B8714089 : Blo 1271954 8714089 := bstep (se 2 (by rfl) ⟨3267783, by rfl⟩ : syracuseStep 8714089 = 6535567) B6535567
theorem B1431535 : Blo 1271954 1431535 := bstep (se 1 (by rfl) ⟨1073651, by rfl⟩ : syracuseStep 1431535 = 2147303) B2147303
theorem B4298777 : Blo 1271954 4298777 := bstep (se 2 (by rfl) ⟨1612041, by rfl⟩ : syracuseStep 4298777 = 3224083) B3224083
theorem B9664595 : Blo 1271954 9664595 := bstep (se 1 (by rfl) ⟨7248446, by rfl⟩ : syracuseStep 9664595 = 14496893) B14496893
theorem B9173357 : Blo 1271954 9173357 := bstep (se 3 (by rfl) ⟨1720004, by rfl⟩ : syracuseStep 9173357 = 3440009) B3440009
theorem B1612315 : Blo 1271954 1612315 := bstep (se 1 (by rfl) ⟨1209236, by rfl⟩ : syracuseStep 1612315 = 2418473) B2418473
theorem B17406515 : Blo 1271954 17406515 := bstep (se 1 (by rfl) ⟨13054886, by rfl⟩ : syracuseStep 17406515 = 26109773) B26109773
theorem B16300601 : Blo 1271954 16300601 := bstep (se 2 (by rfl) ⟨6112725, by rfl⟩ : syracuseStep 16300601 = 12225451) B12225451
theorem B4078201 : Blo 1271954 4078201 := bstep (se 2 (by rfl) ⟨1529325, by rfl⟩ : syracuseStep 4078201 = 3058651) B3058651
theorem B3627641 : Blo 1271954 3627641 := bstep (se 2 (by rfl) ⟨1360365, by rfl⟩ : syracuseStep 3627641 = 2720731) B2720731
theorem B36698953 : Blo 1271954 36698953 := bstep (se 2 (by rfl) ⟨13762107, by rfl⟩ : syracuseStep 36698953 = 27524215) B27524215
theorem B8149841 : Blo 1271954 8149841 := bstep (se 2 (by rfl) ⟨3056190, by rfl⟩ : syracuseStep 8149841 = 6112381) B6112381
theorem B21765023 : Blo 1271954 21765023 := bstep (se 1 (by rfl) ⟨16323767, by rfl⟩ : syracuseStep 21765023 = 32647535) B32647535
theorem B7248811 : Blo 1271954 7248811 := bstep (se 1 (by rfl) ⟨5436608, by rfl⟩ : syracuseStep 7248811 = 10873217) B10873217
theorem B4586447 : Blo 1271954 4586447 := bstep (se 1 (by rfl) ⟨3439835, by rfl⟩ : syracuseStep 4586447 = 6879671) B6879671
theorem B4832207 : Blo 1271954 4832207 := bstep (se 1 (by rfl) ⟨3624155, by rfl⟩ : syracuseStep 4832207 = 7248311) B7248311
theorem B2866247 : Blo 1271954 2866247 := bstep (se 1 (by rfl) ⟨2149685, by rfl⟩ : syracuseStep 2866247 = 4299371) B4299371
theorem B12237905 : Blo 1271954 12237905 := bstep (se 2 (by rfl) ⟨4589214, by rfl⟩ : syracuseStep 12237905 = 9178429) B9178429
theorem B1908047 : Blo 1271954 1908047 := bstep (se 1 (by rfl) ⟨1431035, by rfl⟩ : syracuseStep 1908047 = 2862071) B2862071
theorem B1908137 : Blo 1271954 1908137 := bstep (se 2 (by rfl) ⟨715551, by rfl⟩ : syracuseStep 1908137 = 1431103) B1431103
theorem B4832723 : Blo 1271954 4832723 := bstep (se 1 (by rfl) ⟨3624542, by rfl⟩ : syracuseStep 4832723 = 7249085) B7249085
theorem B1908287 : Blo 1271954 1908287 := bstep (se 1 (by rfl) ⟨1431215, by rfl⟩ : syracuseStep 1908287 = 2862431) B2862431
theorem B7446095 : Blo 1271954 7446095 := bstep (se 1 (by rfl) ⟨5584571, by rfl⟩ : syracuseStep 7446095 = 11169143) B11169143
theorem B167419487 : Blo 1271954 167419487 := bstep (se 1 (by rfl) ⟨125564615, by rfl⟩ : syracuseStep 167419487 = 251129231) B251129231
theorem B2293355 : Blo 1271954 2293355 := bstep (se 1 (by rfl) ⟨1720016, by rfl⟩ : syracuseStep 2293355 = 3440033) B3440033
theorem B18341639 : Blo 1271954 18341639 := bstep (se 1 (by rfl) ⟨13756229, by rfl⟩ : syracuseStep 18341639 = 27512459) B27512459
theorem B8150813 : Blo 1271954 8150813 := bstep (se 3 (by rfl) ⟨1528277, by rfl⟩ : syracuseStep 8150813 = 3056555) B3056555
theorem B1908551 : Blo 1271954 1908551 := bstep (se 1 (by rfl) ⟨1431413, by rfl⟩ : syracuseStep 1908551 = 2862827) B2862827
theorem B1908635 : Blo 1271954 1908635 := bstep (se 1 (by rfl) ⟨1431476, by rfl⟩ : syracuseStep 1908635 = 2862953) B2862953
theorem B10870757 : Blo 1271954 10870757 := bstep (se 4 (by rfl) ⟨1019133, by rfl⟩ : syracuseStep 10870757 = 2038267) B2038267
theorem B6119705 : Blo 1271954 6119705 := bstep (se 2 (by rfl) ⟨2294889, by rfl⟩ : syracuseStep 6119705 = 4589779) B4589779
theorem B3219851 : Blo 1271954 3219851 := bstep (se 1 (by rfl) ⟨2414888, by rfl⟩ : syracuseStep 3219851 = 4829777) B4829777
theorem B5439959 : Blo 1271954 5439959 := bstep (se 1 (by rfl) ⟨4079969, by rfl⟩ : syracuseStep 5439959 = 8159939) B8159939
theorem B4899325 : Blo 1271954 4899325 := bstep (se 3 (by rfl) ⟨918623, by rfl⟩ : syracuseStep 4899325 = 1837247) B1837247
theorem B7348819 : Blo 1271954 7348819 := bstep (se 1 (by rfl) ⟨5511614, by rfl⟩ : syracuseStep 7348819 = 11023229) B11023229
theorem B4293215 : Blo 1271954 4293215 := bstep (se 1 (by rfl) ⟨3219911, by rfl⟩ : syracuseStep 4293215 = 6439823) B6439823
theorem B1909415 : Blo 1271954 1909415 := bstep (se 1 (by rfl) ⟨1432061, by rfl⟩ : syracuseStep 1909415 = 2864123) B2864123
theorem B1909535 : Blo 1271954 1909535 := bstep (se 1 (by rfl) ⟨1432151, by rfl⟩ : syracuseStep 1909535 = 2864303) B2864303
theorem B1909559 : Blo 1271954 1909559 := bstep (se 1 (by rfl) ⟨1432169, by rfl⟩ : syracuseStep 1909559 = 2864339) B2864339
theorem B1909739 : Blo 1271954 1909739 := bstep (se 1 (by rfl) ⟨1432304, by rfl⟩ : syracuseStep 1909739 = 2864609) B2864609
theorem B4080635 : Blo 1271954 4080635 := bstep (se 1 (by rfl) ⟨3060476, by rfl⟩ : syracuseStep 4080635 = 6120953) B6120953
theorem B48931937 : Blo 1271954 48931937 := bstep (se 2 (by rfl) ⟨18349476, by rfl⟩ : syracuseStep 48931937 = 36698953) B36698953
theorem B1934447 : Blo 1271954 1934447 := bstep (se 1 (by rfl) ⟨1450835, by rfl⟩ : syracuseStep 1934447 = 2901671) B2901671
theorem B10880189 : Blo 1271954 10880189 := bstep (se 3 (by rfl) ⟨2040035, by rfl⟩ : syracuseStep 10880189 = 4080071) B4080071
theorem B2147519 : Blo 1271954 2147519 := bstep (se 1 (by rfl) ⟨1610639, by rfl⟩ : syracuseStep 2147519 = 3221279) B3221279
theorem B4834667 : Blo 1271954 4834667 := bstep (se 1 (by rfl) ⟨3626000, by rfl⟩ : syracuseStep 4834667 = 7252001) B7252001
theorem B2418427 : Blo 1271954 2418427 := bstep (se 1 (by rfl) ⟨1813820, by rfl⟩ : syracuseStep 2418427 = 3627641) B3627641
theorem B4294457 : Blo 1271954 4294457 := bstep (se 2 (by rfl) ⟨1610421, by rfl⟩ : syracuseStep 4294457 = 3220843) B3220843
theorem B5441377 : Blo 1271954 5441377 := bstep (se 2 (by rfl) ⟨2040516, by rfl⟩ : syracuseStep 5441377 = 4081033) B4081033
theorem B26470253 : Blo 1271954 26470253 := bstep (se 3 (by rfl) ⟨4963172, by rfl⟩ : syracuseStep 26470253 = 9926345) B9926345
theorem B5433227 : Blo 1271954 5433227 := bstep (se 1 (by rfl) ⟨4074920, by rfl⟩ : syracuseStep 5433227 = 8149841) B8149841
theorem B30984119 : Blo 1271954 30984119 := bstep (se 1 (by rfl) ⟨23238089, by rfl⟩ : syracuseStep 30984119 = 46476179) B46476179
theorem B14510015 : Blo 1271954 14510015 := bstep (se 1 (by rfl) ⟨10882511, by rfl⟩ : syracuseStep 14510015 = 21765023) B21765023
theorem B3057631 : Blo 1271954 3057631 := bstep (se 1 (by rfl) ⟨2293223, by rfl⟩ : syracuseStep 3057631 = 4586447) B4586447
theorem B3221471 : Blo 1271954 3221471 := bstep (se 1 (by rfl) ⟨2416103, by rfl⟩ : syracuseStep 3221471 = 4832207) B4832207
theorem B2148383 : Blo 1271954 2148383 := bstep (se 1 (by rfl) ⟨1611287, by rfl⟩ : syracuseStep 2148383 = 3222575) B3222575
theorem B1910831 : Blo 1271954 1910831 := bstep (se 1 (by rfl) ⟨1433123, by rfl⟩ : syracuseStep 1910831 = 2866247) B2866247
theorem B1272031 : Blo 1271954 1272031 := bstep (se 1 (by rfl) ⟨954023, by rfl⟩ : syracuseStep 1272031 = 1908047) B1908047
theorem B1272091 : Blo 1271954 1272091 := bstep (se 1 (by rfl) ⟨954068, by rfl⟩ : syracuseStep 1272091 = 1908137) B1908137
theorem B3221815 : Blo 1271954 3221815 := bstep (se 1 (by rfl) ⟨2416361, by rfl⟩ : syracuseStep 3221815 = 4832723) B4832723
theorem B1272191 : Blo 1271954 1272191 := bstep (se 1 (by rfl) ⟨954143, by rfl⟩ : syracuseStep 1272191 = 1908287) B1908287
theorem B11618785 : Blo 1271954 11618785 := bstep (se 2 (by rfl) ⟨4357044, by rfl⟩ : syracuseStep 11618785 = 8714089) B8714089
theorem B5433875 : Blo 1271954 5433875 := bstep (se 1 (by rfl) ⟨4075406, by rfl⟩ : syracuseStep 5433875 = 8150813) B8150813
theorem B1272367 : Blo 1271954 1272367 := bstep (se 1 (by rfl) ⟨954275, by rfl⟩ : syracuseStep 1272367 = 1908551) B1908551
theorem B1272423 : Blo 1271954 1272423 := bstep (se 1 (by rfl) ⟨954317, by rfl⟩ : syracuseStep 1272423 = 1908635) B1908635
theorem B2149159 : Blo 1271954 2149159 := bstep (se 1 (by rfl) ⟨1611869, by rfl⟩ : syracuseStep 2149159 = 3223739) B3223739
theorem B13765571 : Blo 1271954 13765571 := bstep (se 1 (by rfl) ⟨10324178, by rfl⟩ : syracuseStep 13765571 = 20648357) B20648357
theorem B1272799 : Blo 1271954 1272799 := bstep (se 1 (by rfl) ⟨954599, by rfl⟩ : syracuseStep 1272799 = 1909199) B1909199
theorem B1272827 : Blo 1271954 1272827 := bstep (se 1 (by rfl) ⟨954620, by rfl⟩ : syracuseStep 1272827 = 1909241) B1909241
theorem B1272895 : Blo 1271954 1272895 := bstep (se 1 (by rfl) ⟨954671, by rfl⟩ : syracuseStep 1272895 = 1909343) B1909343
theorem B2149483 : Blo 1271954 2149483 := bstep (se 1 (by rfl) ⟨1612112, by rfl⟩ : syracuseStep 2149483 = 3224225) B3224225
theorem B16321823 : Blo 1271954 16321823 := bstep (se 1 (by rfl) ⟨12241367, by rfl⟩ : syracuseStep 16321823 = 24482735) B24482735
theorem B2149753 : Blo 1271954 2149753 := bstep (se 2 (by rfl) ⟨806157, by rfl⟩ : syracuseStep 2149753 = 1612315) B1612315
theorem B1273215 : Blo 1271954 1273215 := bstep (se 1 (by rfl) ⟨954911, by rfl⟩ : syracuseStep 1273215 = 1909823) B1909823
theorem B1273243 : Blo 1271954 1273243 := bstep (se 1 (by rfl) ⟨954932, by rfl⟩ : syracuseStep 1273243 = 1909865) B1909865
theorem B2862503 : Blo 1271954 2862503 := bstep (se 1 (by rfl) ⟨2146877, by rfl⟩ : syracuseStep 2862503 = 4293755) B4293755
theorem B1273311 : Blo 1271954 1273311 := bstep (se 1 (by rfl) ⟨954983, by rfl⟩ : syracuseStep 1273311 = 1909967) B1909967
theorem B2862683 : Blo 1271954 2862683 := bstep (se 1 (by rfl) ⟨2147012, by rfl⟩ : syracuseStep 2862683 = 4294025) B4294025
theorem B1273447 : Blo 1271954 1273447 := bstep (se 1 (by rfl) ⟨955085, by rfl⟩ : syracuseStep 1273447 = 1910171) B1910171
theorem B178810541 : Blo 1271954 178810541 := bstep (se 3 (by rfl) ⟨33526976, by rfl⟩ : syracuseStep 178810541 = 67053953) B67053953
theorem B3223223 : Blo 1271954 3223223 := bstep (se 1 (by rfl) ⟨2417417, by rfl⟩ : syracuseStep 3223223 = 4834835) B4834835
theorem B3223273 : Blo 1271954 3223273 := bstep (se 2 (by rfl) ⟨1208727, by rfl⟩ : syracuseStep 3223273 = 2417455) B2417455
theorem B1273595 : Blo 1271954 1273595 := bstep (se 1 (by rfl) ⟨955196, by rfl⟩ : syracuseStep 1273595 = 1910393) B1910393
theorem B1273663 : Blo 1271954 1273663 := bstep (se 1 (by rfl) ⟨955247, by rfl⟩ : syracuseStep 1273663 = 1910495) B1910495
theorem B1273727 : Blo 1271954 1273727 := bstep (se 1 (by rfl) ⟨955295, by rfl⟩ : syracuseStep 1273727 = 1910591) B1910591
theorem B1273839 : Blo 1271954 1273839 := bstep (se 1 (by rfl) ⟨955379, by rfl⟩ : syracuseStep 1273839 = 1910759) B1910759
theorem B2863097 : Blo 1271954 2863097 := bstep (se 2 (by rfl) ⟨1073661, by rfl⟩ : syracuseStep 2863097 = 2147323) B2147323
theorem B1273851 : Blo 1271954 1273851 := bstep (se 1 (by rfl) ⟨955388, by rfl⟩ : syracuseStep 1273851 = 1910777) B1910777
theorem B6443063 : Blo 1271954 6443063 := bstep (se 1 (by rfl) ⟨4832297, by rfl⟩ : syracuseStep 6443063 = 9664595) B9664595
theorem B1273919 : Blo 1271954 1273919 := bstep (se 1 (by rfl) ⟨955439, by rfl⟩ : syracuseStep 1273919 = 1910879) B1910879
theorem B2863187 : Blo 1271954 2863187 := bstep (se 1 (by rfl) ⟨2147390, by rfl⟩ : syracuseStep 2863187 = 4294781) B4294781
theorem B9932989 : Blo 1271954 9932989 := bstep (se 3 (by rfl) ⟨1862435, by rfl⟩ : syracuseStep 9932989 = 3724871) B3724871
theorem B26112233 : Blo 1271954 26112233 := bstep (se 2 (by rfl) ⟨9792087, by rfl⟩ : syracuseStep 26112233 = 19584175) B19584175
theorem B6115571 : Blo 1271954 6115571 := bstep (se 1 (by rfl) ⟨4586678, by rfl⟩ : syracuseStep 6115571 = 9173357) B9173357
theorem B2863367 : Blo 1271954 2863367 := bstep (se 1 (by rfl) ⟨2147525, by rfl⟩ : syracuseStep 2863367 = 4295051) B4295051
theorem B41832773 : Blo 1271954 41832773 := bstep (se 4 (by rfl) ⟨3921822, by rfl⟩ : syracuseStep 41832773 = 7843645) B7843645
theorem B11604343 : Blo 1271954 11604343 := bstep (se 1 (by rfl) ⟨8703257, by rfl⟩ : syracuseStep 11604343 = 17406515) B17406515
theorem B10867067 : Blo 1271954 10867067 := bstep (se 1 (by rfl) ⟨8150300, by rfl⟩ : syracuseStep 10867067 = 16300601) B16300601
theorem B2863673 : Blo 1271954 2863673 := bstep (se 2 (by rfl) ⟨1073877, by rfl⟩ : syracuseStep 2863673 = 2147755) B2147755
theorem B7254643 : Blo 1271954 7254643 := bstep (se 1 (by rfl) ⟨5440982, by rfl⟩ : syracuseStep 7254643 = 10881965) B10881965
theorem B4297373 : Blo 1271954 4297373 := bstep (se 3 (by rfl) ⟨805757, by rfl⟩ : syracuseStep 4297373 = 1611515) B1611515
theorem B4830263 : Blo 1271954 4830263 := bstep (se 1 (by rfl) ⟨3622697, by rfl⟩ : syracuseStep 4830263 = 7245395) B7245395
theorem B111612991 : Blo 1271954 111612991 := bstep (se 1 (by rfl) ⟨83709743, by rfl⟩ : syracuseStep 111612991 = 167419487) B167419487
theorem B1528903 : Blo 1271954 1528903 := bstep (se 1 (by rfl) ⟨1146677, by rfl⟩ : syracuseStep 1528903 = 2293355) B2293355
theorem B3224681 : Blo 1271954 3224681 := bstep (se 2 (by rfl) ⟨1209255, by rfl⟩ : syracuseStep 3224681 = 2418511) B2418511
theorem B12227759 : Blo 1271954 12227759 := bstep (se 1 (by rfl) ⟨9170819, by rfl⟩ : syracuseStep 12227759 = 18341639) B18341639
theorem B4297913 : Blo 1271954 4297913 := bstep (se 2 (by rfl) ⟨1611717, by rfl⟩ : syracuseStep 4297913 = 3223435) B3223435
theorem B2864393 : Blo 1271954 2864393 := bstep (se 2 (by rfl) ⟨1074147, by rfl⟩ : syracuseStep 2864393 = 2148295) B2148295
theorem B2864447 : Blo 1271954 2864447 := bstep (se 1 (by rfl) ⟨2148335, by rfl⟩ : syracuseStep 2864447 = 4296671) B4296671
theorem B7247171 : Blo 1271954 7247171 := bstep (se 1 (by rfl) ⟨5435378, by rfl⟩ : syracuseStep 7247171 = 10870757) B10870757
theorem B31831451 : Blo 1271954 31831451 := bstep (se 1 (by rfl) ⟨23873588, by rfl⟩ : syracuseStep 31831451 = 47747177) B47747177
theorem B2864555 : Blo 1271954 2864555 := bstep (se 1 (by rfl) ⟨2148416, by rfl⟩ : syracuseStep 2864555 = 4296833) B4296833
theorem B1611247 : Blo 1271954 1611247 := bstep (se 1 (by rfl) ⟨1208435, by rfl⟩ : syracuseStep 1611247 = 2416871) B2416871
theorem B7247353 : Blo 1271954 7247353 := bstep (se 2 (by rfl) ⟨2717757, by rfl⟩ : syracuseStep 7247353 = 5435515) B5435515
theorem B32634413 : Blo 1271954 32634413 := bstep (se 3 (by rfl) ⟨6118952, by rfl⟩ : syracuseStep 32634413 = 12237905) B12237905
theorem B5437019 : Blo 1271954 5437019 := bstep (se 1 (by rfl) ⟨4077764, by rfl⟩ : syracuseStep 5437019 = 8155529) B8155529
theorem B2864879 : Blo 1271954 2864879 := bstep (se 1 (by rfl) ⟨2148659, by rfl⟩ : syracuseStep 2864879 = 4297319) B4297319
theorem B39172025 : Blo 1271954 39172025 := bstep (se 2 (by rfl) ⟨14689509, by rfl⟩ : syracuseStep 39172025 = 29379019) B29379019
theorem B2865095 : Blo 1271954 2865095 := bstep (se 1 (by rfl) ⟨2148821, by rfl⟩ : syracuseStep 2865095 = 4297643) B4297643
theorem B5437601 : Blo 1271954 5437601 := bstep (se 2 (by rfl) ⟨2039100, by rfl⟩ : syracuseStep 5437601 = 4078201) B4078201
theorem B2717887 : Blo 1271954 2717887 := bstep (se 1 (by rfl) ⟨2038415, by rfl⟩ : syracuseStep 2717887 = 4076831) B4076831
theorem B2865383 : Blo 1271954 2865383 := bstep (se 1 (by rfl) ⟨2149037, by rfl⟩ : syracuseStep 2865383 = 4298075) B4298075
theorem B2865401 : Blo 1271954 2865401 := bstep (se 2 (by rfl) ⟨1074525, by rfl⟩ : syracuseStep 2865401 = 2149051) B2149051
theorem B5806367 : Blo 1271954 5806367 := bstep (se 1 (by rfl) ⟨4354775, by rfl⟩ : syracuseStep 5806367 = 8709551) B8709551
theorem B2865455 : Blo 1271954 2865455 := bstep (se 1 (by rfl) ⟨2149091, by rfl⟩ : syracuseStep 2865455 = 4298183) B4298183
theorem B1431967 : Blo 1271954 1431967 := bstep (se 1 (by rfl) ⟨1073975, by rfl⟩ : syracuseStep 1431967 = 2147951) B2147951
theorem B1432039 : Blo 1271954 1432039 := bstep (se 1 (by rfl) ⟨1074029, by rfl⟩ : syracuseStep 1432039 = 2148059) B2148059
theorem B4831751 : Blo 1271954 4831751 := bstep (se 1 (by rfl) ⟨3623813, by rfl⟩ : syracuseStep 4831751 = 7247627) B7247627
theorem B2865671 : Blo 1271954 2865671 := bstep (se 1 (by rfl) ⟨2149253, by rfl⟩ : syracuseStep 2865671 = 4298507) B4298507
theorem B9665081 : Blo 1271954 9665081 := bstep (se 2 (by rfl) ⟨3624405, by rfl⟩ : syracuseStep 9665081 = 7248811) B7248811
theorem B2865851 : Blo 1271954 2865851 := bstep (se 1 (by rfl) ⟨2149388, by rfl⟩ : syracuseStep 2865851 = 4298777) B4298777
theorem B5159657 : Blo 1271954 5159657 := bstep (se 2 (by rfl) ⟨1934871, by rfl⟩ : syracuseStep 5159657 = 3869743) B3869743
theorem B6445817 : Blo 1271954 6445817 := bstep (se 2 (by rfl) ⟨2417181, by rfl⟩ : syracuseStep 6445817 = 4834363) B4834363
theorem B2415595 : Blo 1271954 2415595 := bstep (se 1 (by rfl) ⟨1811696, by rfl⟩ : syracuseStep 2415595 = 3623393) B3623393
theorem B4832237 : Blo 1271954 4832237 := bstep (se 3 (by rfl) ⟨906044, by rfl⟩ : syracuseStep 4832237 = 1812089) B1812089
theorem B1432903 : Blo 1271954 1432903 := bstep (se 1 (by rfl) ⟨1074677, by rfl⟩ : syracuseStep 1432903 = 2149355) B2149355
theorem B8150381 : Blo 1271954 8150381 := bstep (se 3 (by rfl) ⟨1528196, by rfl⟩ : syracuseStep 8150381 = 3056393) B3056393
theorem B176234201 : Blo 1271954 176234201 := bstep (se 2 (by rfl) ⟨66087825, by rfl⟩ : syracuseStep 176234201 = 132175651) B132175651
theorem B1908443 : Blo 1271954 1908443 := bstep (se 1 (by rfl) ⟨1431332, by rfl⟩ : syracuseStep 1908443 = 2862665) B2862665
theorem B4964063 : Blo 1271954 4964063 := bstep (se 1 (by rfl) ⟨3723047, by rfl⟩ : syracuseStep 4964063 = 7446095) B7446095
theorem B1908713 : Blo 1271954 1908713 := bstep (se 2 (by rfl) ⟨715767, by rfl⟩ : syracuseStep 1908713 = 1431535) B1431535
theorem B1908791 : Blo 1271954 1908791 := bstep (se 1 (by rfl) ⟨1431593, by rfl⟩ : syracuseStep 1908791 = 2863187) B2863187
theorem B17408155 : Blo 1271954 17408155 := bstep (se 1 (by rfl) ⟨13056116, by rfl⟩ : syracuseStep 17408155 = 26112233) B26112233
theorem B1908911 : Blo 1271954 1908911 := bstep (se 1 (by rfl) ⟨1431683, by rfl⟩ : syracuseStep 1908911 = 2863367) B2863367
theorem B4079803 : Blo 1271954 4079803 := bstep (se 1 (by rfl) ⟨3059852, by rfl⟩ : syracuseStep 4079803 = 6119705) B6119705
theorem B2146567 : Blo 1271954 2146567 := bstep (se 1 (by rfl) ⟨1609925, by rfl⟩ : syracuseStep 2146567 = 3219851) B3219851
theorem B1909115 : Blo 1271954 1909115 := bstep (se 1 (by rfl) ⟨1431836, by rfl⟩ : syracuseStep 1909115 = 2863673) B2863673
theorem B1909289 : Blo 1271954 1909289 := bstep (se 2 (by rfl) ⟨715983, by rfl⟩ : syracuseStep 1909289 = 1431967) B1431967
theorem B1909385 : Blo 1271954 1909385 := bstep (se 2 (by rfl) ⟨716019, by rfl⟩ : syracuseStep 1909385 = 1432039) B1432039
theorem B2720423 : Blo 1271954 2720423 := bstep (se 1 (by rfl) ⟨2040317, by rfl⟩ : syracuseStep 2720423 = 4080635) B4080635
theorem B3220175 : Blo 1271954 3220175 := bstep (se 1 (by rfl) ⟨2415131, by rfl⟩ : syracuseStep 3220175 = 4830263) B4830263
theorem B32621291 : Blo 1271954 32621291 := bstep (se 1 (by rfl) ⟨24465968, by rfl⟩ : syracuseStep 32621291 = 48931937) B48931937
theorem B9798425 : Blo 1271954 9798425 := bstep (se 2 (by rfl) ⟨3674409, by rfl⟩ : syracuseStep 9798425 = 7348819) B7348819
theorem B8151839 : Blo 1271954 8151839 := bstep (se 1 (by rfl) ⟨6113879, by rfl⟩ : syracuseStep 8151839 = 12227759) B12227759
theorem B1909595 : Blo 1271954 1909595 := bstep (se 1 (by rfl) ⟨1432196, by rfl⟩ : syracuseStep 1909595 = 2864393) B2864393
theorem B1909631 : Blo 1271954 1909631 := bstep (se 1 (by rfl) ⟨1432223, by rfl⟩ : syracuseStep 1909631 = 2864447) B2864447
theorem B1909703 : Blo 1271954 1909703 := bstep (se 1 (by rfl) ⟨1432277, by rfl⟩ : syracuseStep 1909703 = 2864555) B2864555
theorem B1909919 : Blo 1271954 1909919 := bstep (se 1 (by rfl) ⟨1432439, by rfl⟩ : syracuseStep 1909919 = 2864879) B2864879
theorem B17646835 : Blo 1271954 17646835 := bstep (se 1 (by rfl) ⟨13235126, by rfl⟩ : syracuseStep 17646835 = 26470253) B26470253
theorem B3622151 : Blo 1271954 3622151 := bstep (se 1 (by rfl) ⟨2716613, by rfl⟩ : syracuseStep 3622151 = 5433227) B5433227
theorem B1910063 : Blo 1271954 1910063 := bstep (se 1 (by rfl) ⟨1432547, by rfl⟩ : syracuseStep 1910063 = 2865095) B2865095
theorem B3220793 : Blo 1271954 3220793 := bstep (se 2 (by rfl) ⟨1207797, by rfl⟩ : syracuseStep 3220793 = 2415595) B2415595
theorem B2147647 : Blo 1271954 2147647 := bstep (se 1 (by rfl) ⟨1610735, by rfl⟩ : syracuseStep 2147647 = 3221471) B3221471
theorem B148817321 : Blo 1271954 148817321 := bstep (se 2 (by rfl) ⟨55806495, by rfl⟩ : syracuseStep 148817321 = 111612991) B111612991
theorem B1910255 : Blo 1271954 1910255 := bstep (se 1 (by rfl) ⟨1432691, by rfl⟩ : syracuseStep 1910255 = 2865383) B2865383
theorem B1910267 : Blo 1271954 1910267 := bstep (se 1 (by rfl) ⟨1432700, by rfl⟩ : syracuseStep 1910267 = 2865401) B2865401
theorem B1910303 : Blo 1271954 1910303 := bstep (se 1 (by rfl) ⟨1432727, by rfl⟩ : syracuseStep 1910303 = 2865455) B2865455
theorem B3221167 : Blo 1271954 3221167 := bstep (se 1 (by rfl) ⟨2415875, by rfl⟩ : syracuseStep 3221167 = 4831751) B4831751
theorem B1910447 : Blo 1271954 1910447 := bstep (se 1 (by rfl) ⟨1432835, by rfl⟩ : syracuseStep 1910447 = 2865671) B2865671
theorem B3622583 : Blo 1271954 3622583 := bstep (se 1 (by rfl) ⟨2716937, by rfl⟩ : syracuseStep 3622583 = 5433875) B5433875
theorem B1910537 : Blo 1271954 1910537 := bstep (se 2 (by rfl) ⟨716451, by rfl⟩ : syracuseStep 1910537 = 1432903) B1432903
theorem B1910567 : Blo 1271954 1910567 := bstep (se 1 (by rfl) ⟨1432925, by rfl⟩ : syracuseStep 1910567 = 2865851) B2865851
theorem B9177047 : Blo 1271954 9177047 := bstep (se 1 (by rfl) ⟨6882785, by rfl⟩ : syracuseStep 9177047 = 13765571) B13765571
theorem B2148329 : Blo 1271954 2148329 := bstep (se 2 (by rfl) ⟨805623, by rfl⟩ : syracuseStep 2148329 = 1611247) B1611247
theorem B3221491 : Blo 1271954 3221491 := bstep (se 1 (by rfl) ⟨2416118, by rfl⟩ : syracuseStep 3221491 = 4832237) B4832237
theorem B10881215 : Blo 1271954 10881215 := bstep (se 1 (by rfl) ⟨8160911, by rfl⟩ : syracuseStep 10881215 = 16321823) B16321823
theorem B5433587 : Blo 1271954 5433587 := bstep (se 1 (by rfl) ⟨4075190, by rfl⟩ : syracuseStep 5433587 = 8150381) B8150381
theorem B2148815 : Blo 1271954 2148815 := bstep (se 1 (by rfl) ⟨1611611, by rfl⟩ : syracuseStep 2148815 = 3223223) B3223223
theorem B1272295 : Blo 1271954 1272295 := bstep (se 1 (by rfl) ⟨954221, by rfl⟩ : syracuseStep 1272295 = 1908443) B1908443
theorem B61966853 : Blo 1271954 61966853 := bstep (se 4 (by rfl) ⟨5809392, by rfl⟩ : syracuseStep 61966853 = 11618785) B11618785
theorem B1272475 : Blo 1271954 1272475 := bstep (se 1 (by rfl) ⟨954356, by rfl⟩ : syracuseStep 1272475 = 1908713) B1908713
theorem B4295375 : Blo 1271954 4295375 := bstep (se 1 (by rfl) ⟨3221531, by rfl⟩ : syracuseStep 4295375 = 6443063) B6443063
theorem B27888515 : Blo 1271954 27888515 := bstep (se 1 (by rfl) ⟨20916386, by rfl⟩ : syracuseStep 27888515 = 41832773) B41832773
theorem B7244711 : Blo 1271954 7244711 := bstep (se 1 (by rfl) ⟨5433533, by rfl⟩ : syracuseStep 7244711 = 10867067) B10867067
theorem B3623849 : Blo 1271954 3623849 := bstep (se 2 (by rfl) ⟨1358943, by rfl⟩ : syracuseStep 3623849 = 2717887) B2717887
theorem B2862143 : Blo 1271954 2862143 := bstep (se 1 (by rfl) ⟨2146607, by rfl⟩ : syracuseStep 2862143 = 4293215) B4293215
theorem B4295753 : Blo 1271954 4295753 := bstep (se 2 (by rfl) ⟨1610907, by rfl⟩ : syracuseStep 4295753 = 3221815) B3221815
theorem B1272943 : Blo 1271954 1272943 := bstep (se 1 (by rfl) ⟨954707, by rfl⟩ : syracuseStep 1272943 = 1909415) B1909415
theorem B1273023 : Blo 1271954 1273023 := bstep (se 1 (by rfl) ⟨954767, by rfl⟩ : syracuseStep 1273023 = 1909535) B1909535
theorem B1273039 : Blo 1271954 1273039 := bstep (se 1 (by rfl) ⟨954779, by rfl⟩ : syracuseStep 1273039 = 1909559) B1909559
theorem B1273159 : Blo 1271954 1273159 := bstep (se 1 (by rfl) ⟨954869, by rfl⟩ : syracuseStep 1273159 = 1909739) B1909739
theorem B6532433 : Blo 1271954 6532433 := bstep (se 2 (by rfl) ⟨2449662, by rfl⟩ : syracuseStep 6532433 = 4899325) B4899325
theorem B2149787 : Blo 1271954 2149787 := bstep (se 1 (by rfl) ⟨1612340, by rfl⟩ : syracuseStep 2149787 = 3224681) B3224681
theorem B7253459 : Blo 1271954 7253459 := bstep (se 1 (by rfl) ⟨5440094, by rfl⟩ : syracuseStep 7253459 = 10880189) B10880189
theorem B3223111 : Blo 1271954 3223111 := bstep (se 1 (by rfl) ⟨2417333, by rfl⟩ : syracuseStep 3223111 = 4834667) B4834667
theorem B21220967 : Blo 1271954 21220967 := bstep (se 1 (by rfl) ⟨15915725, by rfl⟩ : syracuseStep 21220967 = 31831451) B31831451
theorem B3624679 : Blo 1271954 3624679 := bstep (se 1 (by rfl) ⟨2718509, by rfl⟩ : syracuseStep 3624679 = 5437019) B5437019
theorem B2862971 : Blo 1271954 2862971 := bstep (se 1 (by rfl) ⟨2147228, by rfl⟩ : syracuseStep 2862971 = 4294457) B4294457
theorem B20656079 : Blo 1271954 20656079 := bstep (se 1 (by rfl) ⟨15492059, by rfl⟩ : syracuseStep 20656079 = 30984119) B30984119
theorem B1273887 : Blo 1271954 1273887 := bstep (se 1 (by rfl) ⟨955415, by rfl⟩ : syracuseStep 1273887 = 1910831) B1910831
theorem B3625067 : Blo 1271954 3625067 := bstep (se 1 (by rfl) ⟨2718800, by rfl⟩ : syracuseStep 3625067 = 5437601) B5437601
theorem B3870911 : Blo 1271954 3870911 := bstep (se 1 (by rfl) ⟨2903183, by rfl⟩ : syracuseStep 3870911 = 5806367) B5806367
theorem B6443387 : Blo 1271954 6443387 := bstep (se 1 (by rfl) ⟨4832540, by rfl⟩ : syracuseStep 6443387 = 9665081) B9665081
theorem B4297211 : Blo 1271954 4297211 := bstep (se 1 (by rfl) ⟨3222908, by rfl⟩ : syracuseStep 4297211 = 6445817) B6445817
theorem B13759085 : Blo 1271954 13759085 := bstep (se 3 (by rfl) ⟨2579828, by rfl⟩ : syracuseStep 13759085 = 5159657) B5159657
theorem B9663137 : Blo 1271954 9663137 := bstep (se 2 (by rfl) ⟨3623676, by rfl⟩ : syracuseStep 9663137 = 7247353) B7247353
theorem B4297697 : Blo 1271954 4297697 := bstep (se 2 (by rfl) ⟨1611636, by rfl⟩ : syracuseStep 4297697 = 3223273) B3223273
theorem B3224569 : Blo 1271954 3224569 := bstep (se 2 (by rfl) ⟨1209213, by rfl⟩ : syracuseStep 3224569 = 2418427) B2418427
theorem B119207027 : Blo 1271954 119207027 := bstep (se 1 (by rfl) ⟨89405270, by rfl⟩ : syracuseStep 119207027 = 178810541) B178810541
theorem B7255169 : Blo 1271954 7255169 := bstep (se 2 (by rfl) ⟨2720688, by rfl⟩ : syracuseStep 7255169 = 5441377) B5441377
theorem B16307365 : Blo 1271954 16307365 := bstep (se 4 (by rfl) ⟨1528815, by rfl⟩ : syracuseStep 16307365 = 3057631) B3057631
theorem B4077047 : Blo 1271954 4077047 := bstep (se 1 (by rfl) ⟨3057785, by rfl⟩ : syracuseStep 4077047 = 6115571) B6115571
theorem B13243985 : Blo 1271954 13243985 := bstep (se 2 (by rfl) ⟨4966494, by rfl⟩ : syracuseStep 13243985 = 9932989) B9932989
theorem B5158525 : Blo 1271954 5158525 := bstep (se 3 (by rfl) ⟨967223, by rfl⟩ : syracuseStep 5158525 = 1934447) B1934447
theorem B3626639 : Blo 1271954 3626639 := bstep (se 1 (by rfl) ⟨2719979, by rfl⟩ : syracuseStep 3626639 = 5439959) B5439959
theorem B2864915 : Blo 1271954 2864915 := bstep (se 1 (by rfl) ⟨2148686, by rfl⟩ : syracuseStep 2864915 = 4297373) B4297373
theorem B15472457 : Blo 1271954 15472457 := bstep (se 2 (by rfl) ⟨5802171, by rfl⟩ : syracuseStep 15472457 = 11604343) B11604343
theorem B2865275 : Blo 1271954 2865275 := bstep (se 1 (by rfl) ⟨2148956, by rfl⟩ : syracuseStep 2865275 = 4297913) B4297913
theorem B1431679 : Blo 1271954 1431679 := bstep (se 1 (by rfl) ⟨1073759, by rfl⟩ : syracuseStep 1431679 = 2147519) B2147519
theorem B9672857 : Blo 1271954 9672857 := bstep (se 2 (by rfl) ⟨3627321, by rfl⟩ : syracuseStep 9672857 = 7254643) B7254643
theorem B4831447 : Blo 1271954 4831447 := bstep (se 1 (by rfl) ⟨3623585, by rfl⟩ : syracuseStep 4831447 = 7247171) B7247171
theorem B21756275 : Blo 1271954 21756275 := bstep (se 1 (by rfl) ⟨16317206, by rfl⟩ : syracuseStep 21756275 = 32634413) B32634413
theorem B2865545 : Blo 1271954 2865545 := bstep (se 2 (by rfl) ⟨1074579, by rfl⟩ : syracuseStep 2865545 = 2149159) B2149159
theorem B26114683 : Blo 1271954 26114683 := bstep (se 1 (by rfl) ⟨19586012, by rfl⟩ : syracuseStep 26114683 = 39172025) B39172025
theorem B9673343 : Blo 1271954 9673343 := bstep (se 1 (by rfl) ⟨7255007, by rfl⟩ : syracuseStep 9673343 = 14510015) B14510015
theorem B1432255 : Blo 1271954 1432255 := bstep (se 1 (by rfl) ⟨1074191, by rfl⟩ : syracuseStep 1432255 = 2148383) B2148383
theorem B2038537 : Blo 1271954 2038537 := bstep (se 2 (by rfl) ⟨764451, by rfl⟩ : syracuseStep 2038537 = 1528903) B1528903
theorem B2865977 : Blo 1271954 2865977 := bstep (se 2 (by rfl) ⟨1074741, by rfl⟩ : syracuseStep 2865977 = 2149483) B2149483
theorem B2866337 : Blo 1271954 2866337 := bstep (se 2 (by rfl) ⟨1074876, by rfl⟩ : syracuseStep 2866337 = 2149753) B2149753
theorem B13237501 : Blo 1271954 13237501 := bstep (se 3 (by rfl) ⟨2482031, by rfl⟩ : syracuseStep 13237501 = 4964063) B4964063
theorem B1908335 : Blo 1271954 1908335 := bstep (se 1 (by rfl) ⟨1431251, by rfl⟩ : syracuseStep 1908335 = 2862503) B2862503
theorem B1908455 : Blo 1271954 1908455 := bstep (se 1 (by rfl) ⟨1431341, by rfl⟩ : syracuseStep 1908455 = 2862683) B2862683
theorem B117489467 : Blo 1271954 117489467 := bstep (se 1 (by rfl) ⟨88117100, by rfl⟩ : syracuseStep 117489467 = 176234201) B176234201
theorem B1908731 : Blo 1271954 1908731 := bstep (se 1 (by rfl) ⟨1431548, by rfl⟩ : syracuseStep 1908731 = 2863097) B2863097
theorem B2416711 : Blo 1271954 2416711 := bstep (se 1 (by rfl) ⟨1812533, by rfl⟩ : syracuseStep 2416711 = 3625067) B3625067
theorem B2580607 : Blo 1271954 2580607 := bstep (se 1 (by rfl) ⟨1935455, by rfl⟩ : syracuseStep 2580607 = 3870911) B3870911
theorem B1908905 : Blo 1271954 1908905 := bstep (se 2 (by rfl) ⟨715839, by rfl⟩ : syracuseStep 1908905 = 1431679) B1431679
theorem B5439737 : Blo 1271954 5439737 := bstep (se 2 (by rfl) ⟨2039901, by rfl⟩ : syracuseStep 5439737 = 4079803) B4079803
theorem B2146783 : Blo 1271954 2146783 := bstep (se 1 (by rfl) ⟨1610087, by rfl⟩ : syracuseStep 2146783 = 3220175) B3220175
theorem B2147195 : Blo 1271954 2147195 := bstep (se 1 (by rfl) ⟨1610396, by rfl⟩ : syracuseStep 2147195 = 3220793) B3220793
theorem B1909673 : Blo 1271954 1909673 := bstep (se 2 (by rfl) ⟨716127, by rfl⟩ : syracuseStep 1909673 = 1432255) B1432255
theorem B2417759 : Blo 1271954 2417759 := bstep (se 1 (by rfl) ⟨1813319, by rfl⟩ : syracuseStep 2417759 = 3626639) B3626639
theorem B1909943 : Blo 1271954 1909943 := bstep (se 1 (by rfl) ⟨1432457, by rfl⟩ : syracuseStep 1909943 = 2864915) B2864915
theorem B10314971 : Blo 1271954 10314971 := bstep (se 1 (by rfl) ⟨7736228, by rfl⟩ : syracuseStep 10314971 = 15472457) B15472457
theorem B1910183 : Blo 1271954 1910183 := bstep (se 1 (by rfl) ⟨1432637, by rfl⟩ : syracuseStep 1910183 = 2865275) B2865275
theorem B6448571 : Blo 1271954 6448571 := bstep (se 1 (by rfl) ⟨4836428, by rfl⟩ : syracuseStep 6448571 = 9672857) B9672857
theorem B3622391 : Blo 1271954 3622391 := bstep (se 1 (by rfl) ⟨2716793, by rfl⟩ : syracuseStep 3622391 = 5433587) B5433587
theorem B21743153 : Blo 1271954 21743153 := bstep (se 2 (by rfl) ⟨8153682, by rfl⟩ : syracuseStep 21743153 = 16307365) B16307365
theorem B1910363 : Blo 1271954 1910363 := bstep (se 1 (by rfl) ⟨1432772, by rfl⟩ : syracuseStep 1910363 = 2865545) B2865545
theorem B23529113 : Blo 1271954 23529113 := bstep (se 2 (by rfl) ⟨8823417, by rfl⟩ : syracuseStep 23529113 = 17646835) B17646835
theorem B6448895 : Blo 1271954 6448895 := bstep (se 1 (by rfl) ⟨4836671, by rfl⟩ : syracuseStep 6448895 = 9673343) B9673343
theorem B9660221 : Blo 1271954 9660221 := bstep (se 3 (by rfl) ⟨1811291, by rfl⟩ : syracuseStep 9660221 = 3622583) B3622583
theorem B1910651 : Blo 1271954 1910651 := bstep (se 1 (by rfl) ⟨1432988, by rfl⟩ : syracuseStep 1910651 = 2865977) B2865977
theorem B1910891 : Blo 1271954 1910891 := bstep (se 1 (by rfl) ⟨1433168, by rfl⟩ : syracuseStep 1910891 = 2866337) B2866337
theorem B4294889 : Blo 1271954 4294889 := bstep (se 2 (by rfl) ⟨1610583, by rfl⟩ : syracuseStep 4294889 = 3221167) B3221167
theorem B4835639 : Blo 1271954 4835639 := bstep (se 1 (by rfl) ⟨3626729, by rfl⟩ : syracuseStep 4835639 = 7253459) B7253459
theorem B1272223 : Blo 1271954 1272223 := bstep (se 1 (by rfl) ⟨954167, by rfl⟩ : syracuseStep 1272223 = 1908335) B1908335
theorem B1272303 : Blo 1271954 1272303 := bstep (se 1 (by rfl) ⟨954227, by rfl⟩ : syracuseStep 1272303 = 1908455) B1908455
theorem B78326311 : Blo 1271954 78326311 := bstep (se 1 (by rfl) ⟨58744733, by rfl⟩ : syracuseStep 78326311 = 117489467) B117489467
theorem B4295321 : Blo 1271954 4295321 := bstep (se 2 (by rfl) ⟨1610745, by rfl⟩ : syracuseStep 4295321 = 3221491) B3221491
theorem B1272487 : Blo 1271954 1272487 := bstep (se 1 (by rfl) ⟨954365, by rfl⟩ : syracuseStep 1272487 = 1908731) B1908731
theorem B1272527 : Blo 1271954 1272527 := bstep (se 1 (by rfl) ⟨954395, by rfl⟩ : syracuseStep 1272527 = 1908791) B1908791
theorem B1272607 : Blo 1271954 1272607 := bstep (se 1 (by rfl) ⟨954455, by rfl⟩ : syracuseStep 1272607 = 1908911) B1908911
theorem B23210873 : Blo 1271954 23210873 := bstep (se 2 (by rfl) ⟨8704077, by rfl⟩ : syracuseStep 23210873 = 17408155) B17408155
theorem B1272743 : Blo 1271954 1272743 := bstep (se 1 (by rfl) ⟨954557, by rfl⟩ : syracuseStep 1272743 = 1909115) B1909115
theorem B4295591 : Blo 1271954 4295591 := bstep (se 1 (by rfl) ⟨3221693, by rfl⟩ : syracuseStep 4295591 = 6443387) B6443387
theorem B6441929 : Blo 1271954 6441929 := bstep (se 2 (by rfl) ⟨2415723, by rfl⟩ : syracuseStep 6441929 = 4831447) B4831447
theorem B317885405 : Blo 1271954 317885405 := bstep (se 3 (by rfl) ⟨59603513, by rfl⟩ : syracuseStep 317885405 = 119207027) B119207027
theorem B2862089 : Blo 1271954 2862089 := bstep (se 2 (by rfl) ⟨1073283, by rfl⟩ : syracuseStep 2862089 = 2146567) B2146567
theorem B1272859 : Blo 1271954 1272859 := bstep (se 1 (by rfl) ⟨954644, by rfl⟩ : syracuseStep 1272859 = 1909289) B1909289
theorem B1272923 : Blo 1271954 1272923 := bstep (se 1 (by rfl) ⟨954692, by rfl⟩ : syracuseStep 1272923 = 1909385) B1909385
theorem B6442091 : Blo 1271954 6442091 := bstep (se 1 (by rfl) ⟨4831568, by rfl⟩ : syracuseStep 6442091 = 9663137) B9663137
theorem B6532283 : Blo 1271954 6532283 := bstep (se 1 (by rfl) ⟨4899212, by rfl⟩ : syracuseStep 6532283 = 9798425) B9798425
theorem B5434559 : Blo 1271954 5434559 := bstep (se 1 (by rfl) ⟨4075919, by rfl⟩ : syracuseStep 5434559 = 8151839) B8151839
theorem B1273063 : Blo 1271954 1273063 := bstep (se 1 (by rfl) ⟨954797, by rfl⟩ : syracuseStep 1273063 = 1909595) B1909595
theorem B1273087 : Blo 1271954 1273087 := bstep (se 1 (by rfl) ⟨954815, by rfl⟩ : syracuseStep 1273087 = 1909631) B1909631
theorem B1273135 : Blo 1271954 1273135 := bstep (se 1 (by rfl) ⟨954851, by rfl⟩ : syracuseStep 1273135 = 1909703) B1909703
theorem B4836779 : Blo 1271954 4836779 := bstep (se 1 (by rfl) ⟨3627584, by rfl⟩ : syracuseStep 4836779 = 7255169) B7255169
theorem B1273279 : Blo 1271954 1273279 := bstep (se 1 (by rfl) ⟨954959, by rfl⟩ : syracuseStep 1273279 = 1909919) B1909919
theorem B34819577 : Blo 1271954 34819577 := bstep (se 2 (by rfl) ⟨13057341, by rfl⟩ : syracuseStep 34819577 = 26114683) B26114683
theorem B1273375 : Blo 1271954 1273375 := bstep (se 1 (by rfl) ⟨955031, by rfl⟩ : syracuseStep 1273375 = 1910063) B1910063
theorem B1273503 : Blo 1271954 1273503 := bstep (se 1 (by rfl) ⟨955127, by rfl⟩ : syracuseStep 1273503 = 1910255) B1910255
theorem B1273511 : Blo 1271954 1273511 := bstep (se 1 (by rfl) ⟨955133, by rfl⟩ : syracuseStep 1273511 = 1910267) B1910267
theorem B1273535 : Blo 1271954 1273535 := bstep (se 1 (by rfl) ⟨955151, by rfl⟩ : syracuseStep 1273535 = 1910303) B1910303
theorem B1273631 : Blo 1271954 1273631 := bstep (se 1 (by rfl) ⟨955223, by rfl⟩ : syracuseStep 1273631 = 1910447) B1910447
theorem B1273691 : Blo 1271954 1273691 := bstep (se 1 (by rfl) ⟨955268, by rfl⟩ : syracuseStep 1273691 = 1910537) B1910537
theorem B1273711 : Blo 1271954 1273711 := bstep (se 1 (by rfl) ⟨955283, by rfl⟩ : syracuseStep 1273711 = 1910567) B1910567
theorem B7254143 : Blo 1271954 7254143 := bstep (se 1 (by rfl) ⟨5440607, by rfl⟩ : syracuseStep 7254143 = 10881215) B10881215
theorem B14504183 : Blo 1271954 14504183 := bstep (se 1 (by rfl) ⟨10878137, by rfl⟩ : syracuseStep 14504183 = 21756275) B21756275
theorem B17650001 : Blo 1271954 17650001 := bstep (se 2 (by rfl) ⟨6618750, by rfl⟩ : syracuseStep 17650001 = 13237501) B13237501
theorem B2863529 : Blo 1271954 2863529 := bstep (se 2 (by rfl) ⟨1073823, by rfl⟩ : syracuseStep 2863529 = 2147647) B2147647
theorem B7254461 : Blo 1271954 7254461 := bstep (se 3 (by rfl) ⟨1360211, by rfl⟩ : syracuseStep 7254461 = 2720423) B2720423
theorem B2863583 : Blo 1271954 2863583 := bstep (se 1 (by rfl) ⟨2147687, by rfl⟩ : syracuseStep 2863583 = 4295375) B4295375
theorem B18592343 : Blo 1271954 18592343 := bstep (se 1 (by rfl) ⟨13944257, by rfl⟩ : syracuseStep 18592343 = 27888515) B27888515
theorem B4829807 : Blo 1271954 4829807 := bstep (se 1 (by rfl) ⟨3622355, by rfl⟩ : syracuseStep 4829807 = 7244711) B7244711
theorem B2863835 : Blo 1271954 2863835 := bstep (se 1 (by rfl) ⟨2147876, by rfl⟩ : syracuseStep 2863835 = 4295753) B4295753
theorem B4297481 : Blo 1271954 4297481 := bstep (se 2 (by rfl) ⟨1611555, by rfl⟩ : syracuseStep 4297481 = 3223111) B3223111
theorem B6878033 : Blo 1271954 6878033 := bstep (se 2 (by rfl) ⟨2579262, by rfl⟩ : syracuseStep 6878033 = 5158525) B5158525
theorem B4354955 : Blo 1271954 4354955 := bstep (se 1 (by rfl) ⟨3266216, by rfl⟩ : syracuseStep 4354955 = 6532433) B6532433
theorem B2864807 : Blo 1271954 2864807 := bstep (se 1 (by rfl) ⟨2148605, by rfl⟩ : syracuseStep 2864807 = 4297211) B4297211
theorem B9172723 : Blo 1271954 9172723 := bstep (se 1 (by rfl) ⟨6879542, by rfl⟩ : syracuseStep 9172723 = 13759085) B13759085
theorem B21747527 : Blo 1271954 21747527 := bstep (se 1 (by rfl) ⟨16310645, by rfl⟩ : syracuseStep 21747527 = 32621291) B32621291
theorem B2865131 : Blo 1271954 2865131 := bstep (se 1 (by rfl) ⟨2148848, by rfl⟩ : syracuseStep 2865131 = 4297697) B4297697
theorem B2414767 : Blo 1271954 2414767 := bstep (se 1 (by rfl) ⟨1811075, by rfl⟩ : syracuseStep 2414767 = 3622151) B3622151
theorem B99211547 : Blo 1271954 99211547 := bstep (se 1 (by rfl) ⟨74408660, by rfl⟩ : syracuseStep 99211547 = 148817321) B148817321
theorem B2718031 : Blo 1271954 2718031 := bstep (se 1 (by rfl) ⟨2038523, by rfl⟩ : syracuseStep 2718031 = 4077047) B4077047
theorem B2718049 : Blo 1271954 2718049 := bstep (se 2 (by rfl) ⟨1019268, by rfl⟩ : syracuseStep 2718049 = 2038537) B2038537
theorem B8829323 : Blo 1271954 8829323 := bstep (se 1 (by rfl) ⟨6621992, by rfl⟩ : syracuseStep 8829323 = 13243985) B13243985
theorem B6118031 : Blo 1271954 6118031 := bstep (se 1 (by rfl) ⟨4588523, by rfl⟩ : syracuseStep 6118031 = 9177047) B9177047
theorem B1432219 : Blo 1271954 1432219 := bstep (se 1 (by rfl) ⟨1074164, by rfl⟩ : syracuseStep 1432219 = 2148329) B2148329
theorem B4299425 : Blo 1271954 4299425 := bstep (se 2 (by rfl) ⟨1612284, by rfl⟩ : syracuseStep 4299425 = 3224569) B3224569
theorem B1432543 : Blo 1271954 1432543 := bstep (se 1 (by rfl) ⟨1074407, by rfl⟩ : syracuseStep 1432543 = 2148815) B2148815
theorem B41311235 : Blo 1271954 41311235 := bstep (se 1 (by rfl) ⟨30983426, by rfl⟩ : syracuseStep 41311235 = 61966853) B61966853
theorem B2415899 : Blo 1271954 2415899 := bstep (se 1 (by rfl) ⟨1811924, by rfl⟩ : syracuseStep 2415899 = 3623849) B3623849
theorem B1908095 : Blo 1271954 1908095 := bstep (se 1 (by rfl) ⟨1431071, by rfl⟩ : syracuseStep 1908095 = 2862143) B2862143
theorem B1433191 : Blo 1271954 1433191 := bstep (se 1 (by rfl) ⟨1074893, by rfl⟩ : syracuseStep 1433191 = 2149787) B2149787
theorem B4832905 : Blo 1271954 4832905 := bstep (se 2 (by rfl) ⟨1812339, by rfl⟩ : syracuseStep 4832905 = 3624679) B3624679
theorem B14147311 : Blo 1271954 14147311 := bstep (se 1 (by rfl) ⟨10610483, by rfl⟩ : syracuseStep 14147311 = 21220967) B21220967
theorem B1908647 : Blo 1271954 1908647 := bstep (se 1 (by rfl) ⟨1431485, by rfl⟩ : syracuseStep 1908647 = 2862971) B2862971
theorem B13770719 : Blo 1271954 13770719 := bstep (se 1 (by rfl) ⟨10328039, by rfl⟩ : syracuseStep 13770719 = 20656079) B20656079
theorem B3440809 : Blo 1271954 3440809 := bstep (se 2 (by rfl) ⟨1290303, by rfl⟩ : syracuseStep 3440809 = 2580607) B2580607
theorem B3219689 : Blo 1271954 3219689 := bstep (se 2 (by rfl) ⟨1207383, by rfl⟩ : syracuseStep 3219689 = 2414767) B2414767
theorem B1909019 : Blo 1271954 1909019 := bstep (se 1 (by rfl) ⟨1431764, by rfl⟩ : syracuseStep 1909019 = 2863529) B2863529
theorem B1909055 : Blo 1271954 1909055 := bstep (se 1 (by rfl) ⟨1431791, by rfl⟩ : syracuseStep 1909055 = 2863583) B2863583
theorem B12394895 : Blo 1271954 12394895 := bstep (se 1 (by rfl) ⟨9296171, by rfl⟩ : syracuseStep 12394895 = 18592343) B18592343
theorem B3219871 : Blo 1271954 3219871 := bstep (se 1 (by rfl) ⟨2414903, by rfl⟩ : syracuseStep 3219871 = 4829807) B4829807
theorem B1909223 : Blo 1271954 1909223 := bstep (se 1 (by rfl) ⟨1431917, by rfl⟩ : syracuseStep 1909223 = 2863835) B2863835
theorem B1909625 : Blo 1271954 1909625 := bstep (se 2 (by rfl) ⟨716109, by rfl⟩ : syracuseStep 1909625 = 1432219) B1432219
theorem B1909871 : Blo 1271954 1909871 := bstep (se 1 (by rfl) ⟨1432403, by rfl⟩ : syracuseStep 1909871 = 2864807) B2864807
theorem B6440147 : Blo 1271954 6440147 := bstep (se 1 (by rfl) ⟨4830110, by rfl⟩ : syracuseStep 6440147 = 9660221) B9660221
theorem B1910057 : Blo 1271954 1910057 := bstep (se 2 (by rfl) ⟨716271, by rfl⟩ : syracuseStep 1910057 = 1432543) B1432543
theorem B1910087 : Blo 1271954 1910087 := bstep (se 1 (by rfl) ⟨1432565, by rfl⟩ : syracuseStep 1910087 = 2865131) B2865131
theorem B4294619 : Blo 1271954 4294619 := bstep (se 1 (by rfl) ⟨3220964, by rfl⟩ : syracuseStep 4294619 = 6441929) B6441929
theorem B4294727 : Blo 1271954 4294727 := bstep (se 1 (by rfl) ⟨3221045, by rfl⟩ : syracuseStep 4294727 = 6442091) B6442091
theorem B3623039 : Blo 1271954 3623039 := bstep (se 1 (by rfl) ⟨2717279, by rfl⟩ : syracuseStep 3623039 = 5434559) B5434559
theorem B1910921 : Blo 1271954 1910921 := bstep (se 2 (by rfl) ⟨716595, by rfl⟩ : syracuseStep 1910921 = 1433191) B1433191
theorem B1272063 : Blo 1271954 1272063 := bstep (se 1 (by rfl) ⟨954047, by rfl⟩ : syracuseStep 1272063 = 1908095) B1908095
theorem B847694413 : Blo 1271954 847694413 := bstep (se 3 (by rfl) ⟨158942702, by rfl⟩ : syracuseStep 847694413 = 317885405) B317885405
theorem B1272431 : Blo 1271954 1272431 := bstep (se 1 (by rfl) ⟨954323, by rfl⟩ : syracuseStep 1272431 = 1908647) B1908647
theorem B4836095 : Blo 1271954 4836095 := bstep (se 1 (by rfl) ⟨3627071, by rfl⟩ : syracuseStep 4836095 = 7254143) B7254143
theorem B3222281 : Blo 1271954 3222281 := bstep (se 2 (by rfl) ⟨1208355, by rfl⟩ : syracuseStep 3222281 = 2416711) B2416711
theorem B1272603 : Blo 1271954 1272603 := bstep (se 1 (by rfl) ⟨954452, by rfl⟩ : syracuseStep 1272603 = 1908905) B1908905
theorem B9669455 : Blo 1271954 9669455 := bstep (se 1 (by rfl) ⟨7252091, by rfl⟩ : syracuseStep 9669455 = 14504183) B14504183
theorem B4836307 : Blo 1271954 4836307 := bstep (se 1 (by rfl) ⟨3627230, by rfl⟩ : syracuseStep 4836307 = 7254461) B7254461
theorem B3624041 : Blo 1271954 3624041 := bstep (se 2 (by rfl) ⟨1359015, by rfl⟩ : syracuseStep 3624041 = 2718031) B2718031
theorem B3624065 : Blo 1271954 3624065 := bstep (se 2 (by rfl) ⟨1359024, by rfl⟩ : syracuseStep 3624065 = 2718049) B2718049
theorem B17419421 : Blo 1271954 17419421 := bstep (se 3 (by rfl) ⟨3266141, by rfl⟩ : syracuseStep 17419421 = 6532283) B6532283
theorem B2903303 : Blo 1271954 2903303 := bstep (se 1 (by rfl) ⟨2177477, by rfl⟩ : syracuseStep 2903303 = 4354955) B4354955
theorem B1273115 : Blo 1271954 1273115 := bstep (se 1 (by rfl) ⟨954836, by rfl⟩ : syracuseStep 1273115 = 1909673) B1909673
theorem B2862377 : Blo 1271954 2862377 := bstep (se 2 (by rfl) ⟨1073391, by rfl⟩ : syracuseStep 2862377 = 2146783) B2146783
theorem B104435081 : Blo 1271954 104435081 := bstep (se 2 (by rfl) ⟨39163155, by rfl⟩ : syracuseStep 104435081 = 78326311) B78326311
theorem B1273295 : Blo 1271954 1273295 := bstep (se 1 (by rfl) ⟨954971, by rfl⟩ : syracuseStep 1273295 = 1909943) B1909943
theorem B6876647 : Blo 1271954 6876647 := bstep (se 1 (by rfl) ⟨5157485, by rfl⟩ : syracuseStep 6876647 = 10314971) B10314971
theorem B47066669 : Blo 1271954 47066669 := bstep (se 3 (by rfl) ⟨8825000, by rfl⟩ : syracuseStep 47066669 = 17650001) B17650001
theorem B1273455 : Blo 1271954 1273455 := bstep (se 1 (by rfl) ⟨955091, by rfl⟩ : syracuseStep 1273455 = 1910183) B1910183
theorem B14495435 : Blo 1271954 14495435 := bstep (se 1 (by rfl) ⟨10871576, by rfl⟩ : syracuseStep 14495435 = 21743153) B21743153
theorem B1273575 : Blo 1271954 1273575 := bstep (se 1 (by rfl) ⟨955181, by rfl⟩ : syracuseStep 1273575 = 1910363) B1910363
theorem B1273767 : Blo 1271954 1273767 := bstep (se 1 (by rfl) ⟨955325, by rfl⟩ : syracuseStep 1273767 = 1910651) B1910651
theorem B1273927 : Blo 1271954 1273927 := bstep (se 1 (by rfl) ⟨955445, by rfl⟩ : syracuseStep 1273927 = 1910891) B1910891
theorem B2863259 : Blo 1271954 2863259 := bstep (se 1 (by rfl) ⟨2147444, by rfl⟩ : syracuseStep 2863259 = 4294889) B4294889
theorem B3223759 : Blo 1271954 3223759 := bstep (se 1 (by rfl) ⟨2417819, by rfl⟩ : syracuseStep 3223759 = 4835639) B4835639
theorem B5886215 : Blo 1271954 5886215 := bstep (se 1 (by rfl) ⟨4414661, by rfl⟩ : syracuseStep 5886215 = 8829323) B8829323
theorem B2863547 : Blo 1271954 2863547 := bstep (se 1 (by rfl) ⟨2147660, by rfl⟩ : syracuseStep 2863547 = 4295321) B4295321
theorem B2863727 : Blo 1271954 2863727 := bstep (se 1 (by rfl) ⟨2147795, by rfl⟩ : syracuseStep 2863727 = 4295591) B4295591
theorem B6443873 : Blo 1271954 6443873 := bstep (se 2 (by rfl) ⟨2416452, by rfl⟩ : syracuseStep 6443873 = 4832905) B4832905
theorem B1610599 : Blo 1271954 1610599 := bstep (se 1 (by rfl) ⟨1207949, by rfl⟩ : syracuseStep 1610599 = 2415899) B2415899
theorem B3224519 : Blo 1271954 3224519 := bstep (se 1 (by rfl) ⟨2418389, by rfl⟩ : syracuseStep 3224519 = 4836779) B4836779
theorem B18863081 : Blo 1271954 18863081 := bstep (se 2 (by rfl) ⟨7073655, by rfl⟩ : syracuseStep 18863081 = 14147311) B14147311
theorem B23213051 : Blo 1271954 23213051 := bstep (se 1 (by rfl) ⟨17409788, by rfl⟩ : syracuseStep 23213051 = 34819577) B34819577
theorem B9180479 : Blo 1271954 9180479 := bstep (se 1 (by rfl) ⟨6885359, by rfl⟩ : syracuseStep 9180479 = 13770719) B13770719
theorem B3626491 : Blo 1271954 3626491 := bstep (se 1 (by rfl) ⟨2719868, by rfl⟩ : syracuseStep 3626491 = 5439737) B5439737
theorem B2864987 : Blo 1271954 2864987 := bstep (se 1 (by rfl) ⟨2148740, by rfl⟩ : syracuseStep 2864987 = 4297481) B4297481
theorem B4585355 : Blo 1271954 4585355 := bstep (se 1 (by rfl) ⟨3439016, by rfl⟩ : syracuseStep 4585355 = 6878033) B6878033
theorem B1431463 : Blo 1271954 1431463 := bstep (se 1 (by rfl) ⟨1073597, by rfl⟩ : syracuseStep 1431463 = 2147195) B2147195
theorem B1611839 : Blo 1271954 1611839 := bstep (se 1 (by rfl) ⟨1208879, by rfl⟩ : syracuseStep 1611839 = 2417759) B2417759
theorem B4299047 : Blo 1271954 4299047 := bstep (se 1 (by rfl) ⟨3224285, by rfl⟩ : syracuseStep 4299047 = 6448571) B6448571
theorem B2414927 : Blo 1271954 2414927 := bstep (se 1 (by rfl) ⟨1811195, by rfl⟩ : syracuseStep 2414927 = 3622391) B3622391
theorem B15686075 : Blo 1271954 15686075 := bstep (se 1 (by rfl) ⟨11764556, by rfl⟩ : syracuseStep 15686075 = 23529113) B23529113
theorem B4299263 : Blo 1271954 4299263 := bstep (se 1 (by rfl) ⟨3224447, by rfl⟩ : syracuseStep 4299263 = 6448895) B6448895
theorem B14498351 : Blo 1271954 14498351 := bstep (se 1 (by rfl) ⟨10873763, by rfl⟩ : syracuseStep 14498351 = 21747527) B21747527
theorem B66141031 : Blo 1271954 66141031 := bstep (se 1 (by rfl) ⟨49605773, by rfl⟩ : syracuseStep 66141031 = 99211547) B99211547
theorem B4078687 : Blo 1271954 4078687 := bstep (se 1 (by rfl) ⟨3059015, by rfl⟩ : syracuseStep 4078687 = 6118031) B6118031
theorem B2866283 : Blo 1271954 2866283 := bstep (se 1 (by rfl) ⟨2149712, by rfl⟩ : syracuseStep 2866283 = 4299425) B4299425
theorem B15473915 : Blo 1271954 15473915 := bstep (se 1 (by rfl) ⟨11605436, by rfl⟩ : syracuseStep 15473915 = 23210873) B23210873
theorem B27540823 : Blo 1271954 27540823 := bstep (se 1 (by rfl) ⟨20655617, by rfl⟩ : syracuseStep 27540823 = 41311235) B41311235
theorem B1908059 : Blo 1271954 1908059 := bstep (se 1 (by rfl) ⟨1431044, by rfl⟩ : syracuseStep 1908059 = 2862089) B2862089
theorem B12230297 : Blo 1271954 12230297 := bstep (se 2 (by rfl) ⟨4586361, by rfl⟩ : syracuseStep 12230297 = 9172723) B9172723
theorem B1908839 : Blo 1271954 1908839 := bstep (se 1 (by rfl) ⟨1431629, by rfl⟩ : syracuseStep 1908839 = 2863259) B2863259
theorem B2146459 : Blo 1271954 2146459 := bstep (se 1 (by rfl) ⟨1609844, by rfl⟩ : syracuseStep 2146459 = 3219689) B3219689
theorem B3924143 : Blo 1271954 3924143 := bstep (se 1 (by rfl) ⟨2943107, by rfl⟩ : syracuseStep 3924143 = 5886215) B5886215
theorem B1909031 : Blo 1271954 1909031 := bstep (se 1 (by rfl) ⟨1431773, by rfl⟩ : syracuseStep 1909031 = 2863547) B2863547
theorem B1909151 : Blo 1271954 1909151 := bstep (se 1 (by rfl) ⟨1431863, by rfl⟩ : syracuseStep 1909151 = 2863727) B2863727
theorem B4293161 : Blo 1271954 4293161 := bstep (se 2 (by rfl) ⟨1609935, by rfl⟩ : syracuseStep 4293161 = 3219871) B3219871
theorem B12575387 : Blo 1271954 12575387 := bstep (se 1 (by rfl) ⟨9431540, by rfl⟩ : syracuseStep 12575387 = 18863081) B18863081
theorem B15475367 : Blo 1271954 15475367 := bstep (se 1 (by rfl) ⟨11606525, by rfl⟩ : syracuseStep 15475367 = 23213051) B23213051
theorem B7742141 : Blo 1271954 7742141 := bstep (se 3 (by rfl) ⟨1451651, by rfl⟩ : syracuseStep 7742141 = 2903303) B2903303
theorem B1130259217 : Blo 1271954 1130259217 := bstep (se 2 (by rfl) ⟨423847206, by rfl⟩ : syracuseStep 1130259217 = 847694413) B847694413
theorem B4293431 : Blo 1271954 4293431 := bstep (se 1 (by rfl) ⟨3220073, by rfl⟩ : syracuseStep 4293431 = 6440147) B6440147
theorem B18350981 : Blo 1271954 18350981 := bstep (se 4 (by rfl) ⟨1720404, by rfl⟩ : syracuseStep 18350981 = 3440809) B3440809
theorem B2147465 : Blo 1271954 2147465 := bstep (se 2 (by rfl) ⟨805299, by rfl⟩ : syracuseStep 2147465 = 1610599) B1610599
theorem B88188041 : Blo 1271954 88188041 := bstep (se 2 (by rfl) ⟨33070515, by rfl⟩ : syracuseStep 88188041 = 66141031) B66141031
theorem B41829533 : Blo 1271954 41829533 := bstep (se 3 (by rfl) ⟨7843037, by rfl⟩ : syracuseStep 41829533 = 15686075) B15686075
theorem B1909991 : Blo 1271954 1909991 := bstep (se 1 (by rfl) ⟨1432493, by rfl⟩ : syracuseStep 1909991 = 2864987) B2864987
theorem B3056903 : Blo 1271954 3056903 := bstep (se 1 (by rfl) ⟨2292677, by rfl⟩ : syracuseStep 3056903 = 4585355) B4585355
theorem B6448409 : Blo 1271954 6448409 := bstep (se 2 (by rfl) ⟨2418153, by rfl⟩ : syracuseStep 6448409 = 4836307) B4836307
theorem B2148187 : Blo 1271954 2148187 := bstep (se 1 (by rfl) ⟨1611140, by rfl⟩ : syracuseStep 2148187 = 3222281) B3222281
theorem B4835321 : Blo 1271954 4835321 := bstep (se 2 (by rfl) ⟨1813245, by rfl⟩ : syracuseStep 4835321 = 3626491) B3626491
theorem B1910855 : Blo 1271954 1910855 := bstep (se 1 (by rfl) ⟨1433141, by rfl⟩ : syracuseStep 1910855 = 2866283) B2866283
theorem B10315943 : Blo 1271954 10315943 := bstep (se 1 (by rfl) ⟨7736957, by rfl⟩ : syracuseStep 10315943 = 15473915) B15473915
theorem B1272039 : Blo 1271954 1272039 := bstep (se 1 (by rfl) ⟨954029, by rfl⟩ : syracuseStep 1272039 = 1908059) B1908059
theorem B31377779 : Blo 1271954 31377779 := bstep (se 1 (by rfl) ⟨23533334, by rfl⟩ : syracuseStep 31377779 = 47066669) B47066669
theorem B8153531 : Blo 1271954 8153531 := bstep (se 1 (by rfl) ⟨6115148, by rfl⟩ : syracuseStep 8153531 = 12230297) B12230297
theorem B1272679 : Blo 1271954 1272679 := bstep (se 1 (by rfl) ⟨954509, by rfl⟩ : syracuseStep 1272679 = 1909019) B1909019
theorem B1272703 : Blo 1271954 1272703 := bstep (se 1 (by rfl) ⟨954527, by rfl⟩ : syracuseStep 1272703 = 1909055) B1909055
theorem B1272815 : Blo 1271954 1272815 := bstep (se 1 (by rfl) ⟨954611, by rfl⟩ : syracuseStep 1272815 = 1909223) B1909223
theorem B46451789 : Blo 1271954 46451789 := bstep (se 3 (by rfl) ⟨8709710, by rfl⟩ : syracuseStep 46451789 = 17419421) B17419421
theorem B4295915 : Blo 1271954 4295915 := bstep (se 1 (by rfl) ⟨3221936, by rfl⟩ : syracuseStep 4295915 = 6443873) B6443873
theorem B1273083 : Blo 1271954 1273083 := bstep (se 1 (by rfl) ⟨954812, by rfl⟩ : syracuseStep 1273083 = 1909625) B1909625
theorem B2149679 : Blo 1271954 2149679 := bstep (se 1 (by rfl) ⟨1612259, by rfl⟩ : syracuseStep 2149679 = 3224519) B3224519
theorem B1273247 : Blo 1271954 1273247 := bstep (se 1 (by rfl) ⟨954935, by rfl⟩ : syracuseStep 1273247 = 1909871) B1909871
theorem B24481277 : Blo 1271954 24481277 := bstep (se 3 (by rfl) ⟨4590239, by rfl⟩ : syracuseStep 24481277 = 9180479) B9180479
theorem B1273371 : Blo 1271954 1273371 := bstep (se 1 (by rfl) ⟨955028, by rfl⟩ : syracuseStep 1273371 = 1910057) B1910057
theorem B1273391 : Blo 1271954 1273391 := bstep (se 1 (by rfl) ⟨955043, by rfl⟩ : syracuseStep 1273391 = 1910087) B1910087
theorem B2863079 : Blo 1271954 2863079 := bstep (se 1 (by rfl) ⟨2147309, by rfl⟩ : syracuseStep 2863079 = 4294619) B4294619
theorem B2863151 : Blo 1271954 2863151 := bstep (se 1 (by rfl) ⟨2147363, by rfl⟩ : syracuseStep 2863151 = 4294727) B4294727
theorem B1273947 : Blo 1271954 1273947 := bstep (se 1 (by rfl) ⟨955460, by rfl⟩ : syracuseStep 1273947 = 1910921) B1910921
theorem B1609951 : Blo 1271954 1609951 := bstep (se 1 (by rfl) ⟨1207463, by rfl⟩ : syracuseStep 1609951 = 2414927) B2414927
theorem B36721097 : Blo 1271954 36721097 := bstep (se 2 (by rfl) ⟨13770411, by rfl⟩ : syracuseStep 36721097 = 27540823) B27540823
theorem B3224063 : Blo 1271954 3224063 := bstep (se 1 (by rfl) ⟨2418047, by rfl⟩ : syracuseStep 3224063 = 4836095) B4836095
theorem B4584431 : Blo 1271954 4584431 := bstep (se 1 (by rfl) ⟨3438323, by rfl⟩ : syracuseStep 4584431 = 6876647) B6876647
theorem B9663623 : Blo 1271954 9663623 := bstep (se 1 (by rfl) ⟨7247717, by rfl⟩ : syracuseStep 9663623 = 14495435) B14495435
theorem B4298237 : Blo 1271954 4298237 := bstep (se 3 (by rfl) ⟨805919, by rfl⟩ : syracuseStep 4298237 = 1611839) B1611839
theorem B4298345 : Blo 1271954 4298345 := bstep (se 2 (by rfl) ⟨1611879, by rfl⟩ : syracuseStep 4298345 = 3223759) B3223759
theorem B9664109 : Blo 1271954 9664109 := bstep (se 3 (by rfl) ⟨1812020, by rfl⟩ : syracuseStep 9664109 = 3624041) B3624041
theorem B33053053 : Blo 1271954 33053053 := bstep (se 3 (by rfl) ⟨6197447, by rfl⟩ : syracuseStep 33053053 = 12394895) B12394895
theorem B2415359 : Blo 1271954 2415359 := bstep (se 1 (by rfl) ⟨1811519, by rfl⟩ : syracuseStep 2415359 = 3623039) B3623039
theorem B5438249 : Blo 1271954 5438249 := bstep (se 2 (by rfl) ⟨2039343, by rfl⟩ : syracuseStep 5438249 = 4078687) B4078687
theorem B2866031 : Blo 1271954 2866031 := bstep (se 1 (by rfl) ⟨2149523, by rfl⟩ : syracuseStep 2866031 = 4299047) B4299047
theorem B2866175 : Blo 1271954 2866175 := bstep (se 1 (by rfl) ⟨2149631, by rfl⟩ : syracuseStep 2866175 = 4299263) B4299263
theorem B9665567 : Blo 1271954 9665567 := bstep (se 1 (by rfl) ⟨7249175, by rfl⟩ : syracuseStep 9665567 = 14498351) B14498351
theorem B6446303 : Blo 1271954 6446303 := bstep (se 1 (by rfl) ⟨4834727, by rfl⟩ : syracuseStep 6446303 = 9669455) B9669455
theorem B2416043 : Blo 1271954 2416043 := bstep (se 1 (by rfl) ⟨1812032, by rfl⟩ : syracuseStep 2416043 = 3624065) B3624065
theorem B1908251 : Blo 1271954 1908251 := bstep (se 1 (by rfl) ⟨1431188, by rfl⟩ : syracuseStep 1908251 = 2862377) B2862377
theorem B69623387 : Blo 1271954 69623387 := bstep (se 1 (by rfl) ⟨52217540, by rfl⟩ : syracuseStep 69623387 = 104435081) B104435081
theorem B1908617 : Blo 1271954 1908617 := bstep (se 2 (by rfl) ⟨715731, by rfl⟩ : syracuseStep 1908617 = 1431463) B1431463
theorem B1908767 : Blo 1271954 1908767 := bstep (se 1 (by rfl) ⟨1431575, by rfl⟩ : syracuseStep 1908767 = 2863151) B2863151
theorem B2146601 : Blo 1271954 2146601 := bstep (se 2 (by rfl) ⟨804975, by rfl⟩ : syracuseStep 2146601 = 1609951) B1609951
theorem B235168109 : Blo 1271954 235168109 := bstep (se 3 (by rfl) ⟨44094020, by rfl⟩ : syracuseStep 235168109 = 88188041) B88188041
theorem B5161427 : Blo 1271954 5161427 := bstep (se 1 (by rfl) ⟨3871070, by rfl⟩ : syracuseStep 5161427 = 7742141) B7742141
theorem B3056287 : Blo 1271954 3056287 := bstep (se 1 (by rfl) ⟨2292215, by rfl⟩ : syracuseStep 3056287 = 4584431) B4584431
theorem B27886355 : Blo 1271954 27886355 := bstep (se 1 (by rfl) ⟨20914766, by rfl⟩ : syracuseStep 27886355 = 41829533) B41829533
theorem B1910687 : Blo 1271954 1910687 := bstep (se 1 (by rfl) ⟨1433015, by rfl⟩ : syracuseStep 1910687 = 2866031) B2866031
theorem B6440957 : Blo 1271954 6440957 := bstep (se 3 (by rfl) ⟨1207679, by rfl⟩ : syracuseStep 6440957 = 2415359) B2415359
theorem B1910783 : Blo 1271954 1910783 := bstep (se 1 (by rfl) ⟨1433087, by rfl⟩ : syracuseStep 1910783 = 2866175) B2866175
theorem B30967859 : Blo 1271954 30967859 := bstep (se 1 (by rfl) ⟨23225894, by rfl⟩ : syracuseStep 30967859 = 46451789) B46451789
theorem B16320851 : Blo 1271954 16320851 := bstep (se 1 (by rfl) ⟨12240638, by rfl⟩ : syracuseStep 16320851 = 24481277) B24481277
theorem B1272167 : Blo 1271954 1272167 := bstep (se 1 (by rfl) ⟨954125, by rfl⟩ : syracuseStep 1272167 = 1908251) B1908251
theorem B1272411 : Blo 1271954 1272411 := bstep (se 1 (by rfl) ⟨954308, by rfl⟩ : syracuseStep 1272411 = 1908617) B1908617
theorem B1272559 : Blo 1271954 1272559 := bstep (se 1 (by rfl) ⟨954419, by rfl⟩ : syracuseStep 1272559 = 1908839) B1908839
theorem B2616095 : Blo 1271954 2616095 := bstep (se 1 (by rfl) ⟨1962071, by rfl⟩ : syracuseStep 2616095 = 3924143) B3924143
theorem B1272687 : Blo 1271954 1272687 := bstep (se 1 (by rfl) ⟨954515, by rfl⟩ : syracuseStep 1272687 = 1909031) B1909031
theorem B2861945 : Blo 1271954 2861945 := bstep (se 2 (by rfl) ⟨1073229, by rfl⟩ : syracuseStep 2861945 = 2146459) B2146459
theorem B1272767 : Blo 1271954 1272767 := bstep (se 1 (by rfl) ⟨954575, by rfl⟩ : syracuseStep 1272767 = 1909151) B1909151
theorem B24480731 : Blo 1271954 24480731 := bstep (se 1 (by rfl) ⟨18360548, by rfl⟩ : syracuseStep 24480731 = 36721097) B36721097
theorem B2149375 : Blo 1271954 2149375 := bstep (se 1 (by rfl) ⟨1612031, by rfl⟩ : syracuseStep 2149375 = 3224063) B3224063
theorem B2862107 : Blo 1271954 2862107 := bstep (se 1 (by rfl) ⟨2146580, by rfl⟩ : syracuseStep 2862107 = 4293161) B4293161
theorem B8383591 : Blo 1271954 8383591 := bstep (se 1 (by rfl) ⟨6287693, by rfl⟩ : syracuseStep 8383591 = 12575387) B12575387
theorem B10316911 : Blo 1271954 10316911 := bstep (se 1 (by rfl) ⟨7737683, by rfl⟩ : syracuseStep 10316911 = 15475367) B15475367
theorem B2862287 : Blo 1271954 2862287 := bstep (se 1 (by rfl) ⟨2146715, by rfl⟩ : syracuseStep 2862287 = 4293431) B4293431
theorem B12233987 : Blo 1271954 12233987 := bstep (se 1 (by rfl) ⟨9175490, by rfl⟩ : syracuseStep 12233987 = 18350981) B18350981
theorem B6442415 : Blo 1271954 6442415 := bstep (se 1 (by rfl) ⟨4831811, by rfl⟩ : syracuseStep 6442415 = 9663623) B9663623
theorem B1273327 : Blo 1271954 1273327 := bstep (se 1 (by rfl) ⟨954995, by rfl⟩ : syracuseStep 1273327 = 1909991) B1909991
theorem B1507012289 : Blo 1271954 1507012289 := bstep (se 2 (by rfl) ⟨565129608, by rfl⟩ : syracuseStep 1507012289 = 1130259217) B1130259217
theorem B6442739 : Blo 1271954 6442739 := bstep (se 1 (by rfl) ⟨4832054, by rfl⟩ : syracuseStep 6442739 = 9664109) B9664109
theorem B3223547 : Blo 1271954 3223547 := bstep (se 1 (by rfl) ⟨2417660, by rfl⟩ : syracuseStep 3223547 = 4835321) B4835321
theorem B1273903 : Blo 1271954 1273903 := bstep (se 1 (by rfl) ⟨955427, by rfl⟩ : syracuseStep 1273903 = 1910855) B1910855
theorem B6877295 : Blo 1271954 6877295 := bstep (se 1 (by rfl) ⟨5157971, by rfl⟩ : syracuseStep 6877295 = 10315943) B10315943
theorem B20918519 : Blo 1271954 20918519 := bstep (se 1 (by rfl) ⟨15688889, by rfl⟩ : syracuseStep 20918519 = 31377779) B31377779
theorem B5435687 : Blo 1271954 5435687 := bstep (se 1 (by rfl) ⟨4076765, by rfl⟩ : syracuseStep 5435687 = 8153531) B8153531
theorem B3625499 : Blo 1271954 3625499 := bstep (se 1 (by rfl) ⟨2719124, by rfl⟩ : syracuseStep 3625499 = 5438249) B5438249
theorem B6443711 : Blo 1271954 6443711 := bstep (se 1 (by rfl) ⟨4832783, by rfl⟩ : syracuseStep 6443711 = 9665567) B9665567
theorem B4297535 : Blo 1271954 4297535 := bstep (se 1 (by rfl) ⟨3223151, by rfl⟩ : syracuseStep 4297535 = 6446303) B6446303
theorem B2863943 : Blo 1271954 2863943 := bstep (se 1 (by rfl) ⟨2147957, by rfl⟩ : syracuseStep 2863943 = 4295915) B4295915
theorem B1610695 : Blo 1271954 1610695 := bstep (se 1 (by rfl) ⟨1208021, by rfl⟩ : syracuseStep 1610695 = 2416043) B2416043
theorem B2864249 : Blo 1271954 2864249 := bstep (se 2 (by rfl) ⟨1074093, by rfl⟩ : syracuseStep 2864249 = 2148187) B2148187
theorem B44070737 : Blo 1271954 44070737 := bstep (se 2 (by rfl) ⟨16526526, by rfl⟩ : syracuseStep 44070737 = 33053053) B33053053
theorem B1431643 : Blo 1271954 1431643 := bstep (se 1 (by rfl) ⟨1073732, by rfl⟩ : syracuseStep 1431643 = 2147465) B2147465
theorem B2037935 : Blo 1271954 2037935 := bstep (se 1 (by rfl) ⟨1528451, by rfl⟩ : syracuseStep 2037935 = 3056903) B3056903
theorem B4298939 : Blo 1271954 4298939 := bstep (se 1 (by rfl) ⟨3224204, by rfl⟩ : syracuseStep 4298939 = 6448409) B6448409
theorem B2865491 : Blo 1271954 2865491 := bstep (se 1 (by rfl) ⟨2149118, by rfl⟩ : syracuseStep 2865491 = 4298237) B4298237
theorem B2865563 : Blo 1271954 2865563 := bstep (se 1 (by rfl) ⟨2149172, by rfl⟩ : syracuseStep 2865563 = 4298345) B4298345
theorem B1433119 : Blo 1271954 1433119 := bstep (se 1 (by rfl) ⟨1074839, by rfl⟩ : syracuseStep 1433119 = 2149679) B2149679
theorem B46415591 : Blo 1271954 46415591 := bstep (se 1 (by rfl) ⟨34811693, by rfl⟩ : syracuseStep 46415591 = 69623387) B69623387
theorem B1908719 : Blo 1271954 1908719 := bstep (se 1 (by rfl) ⟨1431539, by rfl⟩ : syracuseStep 1908719 = 2863079) B2863079
theorem B1908857 : Blo 1271954 1908857 := bstep (se 2 (by rfl) ⟨715821, by rfl⟩ : syracuseStep 1908857 = 1431643) B1431643
theorem B156778739 : Blo 1271954 156778739 := bstep (se 1 (by rfl) ⟨117584054, by rfl⟩ : syracuseStep 156778739 = 235168109) B235168109
theorem B3440951 : Blo 1271954 3440951 := bstep (se 1 (by rfl) ⟨2580713, by rfl⟩ : syracuseStep 3440951 = 5161427) B5161427
theorem B1909295 : Blo 1271954 1909295 := bstep (se 1 (by rfl) ⟨1431971, by rfl⟩ : syracuseStep 1909295 = 2863943) B2863943
theorem B1909499 : Blo 1271954 1909499 := bstep (se 1 (by rfl) ⟨1432124, by rfl⟩ : syracuseStep 1909499 = 2864249) B2864249
theorem B2147593 : Blo 1271954 2147593 := bstep (se 2 (by rfl) ⟨805347, by rfl⟩ : syracuseStep 2147593 = 1610695) B1610695
theorem B4293971 : Blo 1271954 4293971 := bstep (se 1 (by rfl) ⟨3220478, by rfl⟩ : syracuseStep 4293971 = 6440957) B6440957
theorem B20645239 : Blo 1271954 20645239 := bstep (se 1 (by rfl) ⟨15483929, by rfl⟩ : syracuseStep 20645239 = 30967859) B30967859
theorem B9667997 : Blo 1271954 9667997 := bstep (se 3 (by rfl) ⟨1812749, by rfl⟩ : syracuseStep 9667997 = 3625499) B3625499
theorem B13755881 : Blo 1271954 13755881 := bstep (se 2 (by rfl) ⟨5158455, by rfl⟩ : syracuseStep 13755881 = 10316911) B10316911
theorem B1910327 : Blo 1271954 1910327 := bstep (se 1 (by rfl) ⟨1432745, by rfl⟩ : syracuseStep 1910327 = 2865491) B2865491
theorem B10880567 : Blo 1271954 10880567 := bstep (se 1 (by rfl) ⟨8160425, by rfl⟩ : syracuseStep 10880567 = 16320851) B16320851
theorem B1910375 : Blo 1271954 1910375 := bstep (se 1 (by rfl) ⟨1432781, by rfl⟩ : syracuseStep 1910375 = 2865563) B2865563
theorem B16320487 : Blo 1271954 16320487 := bstep (se 1 (by rfl) ⟨12240365, by rfl⟩ : syracuseStep 16320487 = 24480731) B24480731
theorem B1910825 : Blo 1271954 1910825 := bstep (se 2 (by rfl) ⟨716559, by rfl⟩ : syracuseStep 1910825 = 1433119) B1433119
theorem B4294943 : Blo 1271954 4294943 := bstep (se 1 (by rfl) ⟨3221207, by rfl⟩ : syracuseStep 4294943 = 6442415) B6442415
theorem B30943727 : Blo 1271954 30943727 := bstep (se 1 (by rfl) ⟨23207795, by rfl⟩ : syracuseStep 30943727 = 46415591) B46415591
theorem B4295159 : Blo 1271954 4295159 := bstep (se 1 (by rfl) ⟨3221369, by rfl⟩ : syracuseStep 4295159 = 6442739) B6442739
theorem B1272479 : Blo 1271954 1272479 := bstep (se 1 (by rfl) ⟨954359, by rfl⟩ : syracuseStep 1272479 = 1908719) B1908719
theorem B2149031 : Blo 1271954 2149031 := bstep (se 1 (by rfl) ⟨1611773, by rfl⟩ : syracuseStep 2149031 = 3223547) B3223547
theorem B1272511 : Blo 1271954 1272511 := bstep (se 1 (by rfl) ⟨954383, by rfl⟩ : syracuseStep 1272511 = 1908767) B1908767
theorem B13945679 : Blo 1271954 13945679 := bstep (se 1 (by rfl) ⟨10459259, by rfl⟩ : syracuseStep 13945679 = 20918519) B20918519
theorem B3623791 : Blo 1271954 3623791 := bstep (se 1 (by rfl) ⟨2717843, by rfl⟩ : syracuseStep 3623791 = 5435687) B5435687
theorem B4295807 : Blo 1271954 4295807 := bstep (se 1 (by rfl) ⟨3221855, by rfl⟩ : syracuseStep 4295807 = 6443711) B6443711
theorem B18590903 : Blo 1271954 18590903 := bstep (se 1 (by rfl) ⟨13943177, by rfl⟩ : syracuseStep 18590903 = 27886355) B27886355
theorem B4075049 : Blo 1271954 4075049 := bstep (se 2 (by rfl) ⟨1528143, by rfl⟩ : syracuseStep 4075049 = 3056287) B3056287
theorem B1273791 : Blo 1271954 1273791 := bstep (se 1 (by rfl) ⟨955343, by rfl⟩ : syracuseStep 1273791 = 1910687) B1910687
theorem B1273855 : Blo 1271954 1273855 := bstep (se 1 (by rfl) ⟨955391, by rfl⟩ : syracuseStep 1273855 = 1910783) B1910783
theorem B11178121 : Blo 1271954 11178121 := bstep (se 2 (by rfl) ⟨4191795, by rfl⟩ : syracuseStep 11178121 = 8383591) B8383591
theorem B6976253 : Blo 1271954 6976253 := bstep (se 3 (by rfl) ⟨1308047, by rfl⟩ : syracuseStep 6976253 = 2616095) B2616095
theorem B8155991 : Blo 1271954 8155991 := bstep (se 1 (by rfl) ⟨6116993, by rfl⟩ : syracuseStep 8155991 = 12233987) B12233987
theorem B4584863 : Blo 1271954 4584863 := bstep (se 1 (by rfl) ⟨3438647, by rfl⟩ : syracuseStep 4584863 = 6877295) B6877295
theorem B1431067 : Blo 1271954 1431067 := bstep (se 1 (by rfl) ⟨1073300, by rfl⟩ : syracuseStep 1431067 = 2146601) B2146601
theorem B2865023 : Blo 1271954 2865023 := bstep (se 1 (by rfl) ⟨2148767, by rfl⟩ : syracuseStep 2865023 = 4297535) B4297535
theorem B2865833 : Blo 1271954 2865833 := bstep (se 2 (by rfl) ⟨1074687, by rfl⟩ : syracuseStep 2865833 = 2149375) B2149375
theorem B1358623 : Blo 1271954 1358623 := bstep (se 1 (by rfl) ⟨1018967, by rfl⟩ : syracuseStep 1358623 = 2037935) B2037935
theorem B2865959 : Blo 1271954 2865959 := bstep (se 1 (by rfl) ⟨2149469, by rfl⟩ : syracuseStep 2865959 = 4298939) B4298939
theorem B1907963 : Blo 1271954 1907963 := bstep (se 1 (by rfl) ⟨1430972, by rfl⟩ : syracuseStep 1907963 = 2861945) B2861945
theorem B1908071 : Blo 1271954 1908071 := bstep (se 1 (by rfl) ⟨1431053, by rfl⟩ : syracuseStep 1908071 = 2862107) B2862107
theorem B1908191 : Blo 1271954 1908191 := bstep (se 1 (by rfl) ⟨1431143, by rfl⟩ : syracuseStep 1908191 = 2862287) B2862287
theorem B117521965 : Blo 1271954 117521965 := bstep (se 3 (by rfl) ⟨22035368, by rfl⟩ : syracuseStep 117521965 = 44070737) B44070737
theorem B1004674859 : Blo 1271954 1004674859 := bstep (se 1 (by rfl) ⟨753506144, by rfl⟩ : syracuseStep 1004674859 = 1507012289) B1507012289
theorem B2293967 : Blo 1271954 2293967 := bstep (se 1 (by rfl) ⟨1720475, by rfl⟩ : syracuseStep 2293967 = 3440951) B3440951
theorem B1811497 : Blo 1271954 1811497 := bstep (se 2 (by rfl) ⟨679311, by rfl⟩ : syracuseStep 1811497 = 1358623) B1358623
theorem B1910015 : Blo 1271954 1910015 := bstep (se 1 (by rfl) ⟨1432511, by rfl⟩ : syracuseStep 1910015 = 2865023) B2865023
theorem B20629151 : Blo 1271954 20629151 := bstep (se 1 (by rfl) ⟨15471863, by rfl⟩ : syracuseStep 20629151 = 30943727) B30943727
theorem B1910555 : Blo 1271954 1910555 := bstep (se 1 (by rfl) ⟨1432916, by rfl⟩ : syracuseStep 1910555 = 2865833) B2865833
theorem B27526985 : Blo 1271954 27526985 := bstep (se 2 (by rfl) ⟨10322619, by rfl⟩ : syracuseStep 27526985 = 20645239) B20645239
theorem B1910639 : Blo 1271954 1910639 := bstep (se 1 (by rfl) ⟨1432979, by rfl⟩ : syracuseStep 1910639 = 2865959) B2865959
theorem B1271975 : Blo 1271954 1271975 := bstep (se 1 (by rfl) ⟨953981, by rfl⟩ : syracuseStep 1271975 = 1907963) B1907963
theorem B1272047 : Blo 1271954 1272047 := bstep (se 1 (by rfl) ⟨954035, by rfl⟩ : syracuseStep 1272047 = 1908071) B1908071
theorem B1272127 : Blo 1271954 1272127 := bstep (se 1 (by rfl) ⟨954095, by rfl⟩ : syracuseStep 1272127 = 1908191) B1908191
theorem B21760649 : Blo 1271954 21760649 := bstep (se 2 (by rfl) ⟨8160243, by rfl⟩ : syracuseStep 21760649 = 16320487) B16320487
theorem B1272571 : Blo 1271954 1272571 := bstep (se 1 (by rfl) ⟨954428, by rfl⟩ : syracuseStep 1272571 = 1908857) B1908857
theorem B14904161 : Blo 1271954 14904161 := bstep (se 2 (by rfl) ⟨5589060, by rfl⟩ : syracuseStep 14904161 = 11178121) B11178121
theorem B1272863 : Blo 1271954 1272863 := bstep (se 1 (by rfl) ⟨954647, by rfl⟩ : syracuseStep 1272863 = 1909295) B1909295
theorem B1272999 : Blo 1271954 1272999 := bstep (se 1 (by rfl) ⟨954749, by rfl⟩ : syracuseStep 1272999 = 1909499) B1909499
theorem B2862647 : Blo 1271954 2862647 := bstep (se 1 (by rfl) ⟨2146985, by rfl⟩ : syracuseStep 2862647 = 4293971) B4293971
theorem B9170587 : Blo 1271954 9170587 := bstep (se 1 (by rfl) ⟨6877940, by rfl⟩ : syracuseStep 9170587 = 13755881) B13755881
theorem B1273551 : Blo 1271954 1273551 := bstep (se 1 (by rfl) ⟨955163, by rfl⟩ : syracuseStep 1273551 = 1910327) B1910327
theorem B7253711 : Blo 1271954 7253711 := bstep (se 1 (by rfl) ⟨5440283, by rfl⟩ : syracuseStep 7253711 = 10880567) B10880567
theorem B1273583 : Blo 1271954 1273583 := bstep (se 1 (by rfl) ⟨955187, by rfl⟩ : syracuseStep 1273583 = 1910375) B1910375
theorem B12226301 : Blo 1271954 12226301 := bstep (se 3 (by rfl) ⟨2292431, by rfl⟩ : syracuseStep 12226301 = 4584863) B4584863
theorem B1273883 : Blo 1271954 1273883 := bstep (se 1 (by rfl) ⟨955412, by rfl⟩ : syracuseStep 1273883 = 1910825) B1910825
theorem B2863295 : Blo 1271954 2863295 := bstep (se 1 (by rfl) ⟨2147471, by rfl⟩ : syracuseStep 2863295 = 4294943) B4294943
theorem B2863439 : Blo 1271954 2863439 := bstep (se 1 (by rfl) ⟨2147579, by rfl⟩ : syracuseStep 2863439 = 4295159) B4295159
theorem B2863457 : Blo 1271954 2863457 := bstep (se 2 (by rfl) ⟨1073796, by rfl⟩ : syracuseStep 2863457 = 2147593) B2147593
theorem B2863871 : Blo 1271954 2863871 := bstep (se 1 (by rfl) ⟨2147903, by rfl⟩ : syracuseStep 2863871 = 4295807) B4295807
theorem B2716699 : Blo 1271954 2716699 := bstep (se 1 (by rfl) ⟨2037524, by rfl⟩ : syracuseStep 2716699 = 4075049) B4075049
theorem B669783239 : Blo 1271954 669783239 := bstep (se 1 (by rfl) ⟨502337429, by rfl⟩ : syracuseStep 669783239 = 1004674859) B1004674859
theorem B104519159 : Blo 1271954 104519159 := bstep (se 1 (by rfl) ⟨78389369, by rfl⟩ : syracuseStep 104519159 = 156778739) B156778739
theorem B5437327 : Blo 1271954 5437327 := bstep (se 1 (by rfl) ⟨4077995, by rfl⟩ : syracuseStep 5437327 = 8155991) B8155991
theorem B6445331 : Blo 1271954 6445331 := bstep (se 1 (by rfl) ⟨4833998, by rfl⟩ : syracuseStep 6445331 = 9667997) B9667997
theorem B4831721 : Blo 1271954 4831721 := bstep (se 2 (by rfl) ⟨1811895, by rfl⟩ : syracuseStep 4831721 = 3623791) B3623791
theorem B1432687 : Blo 1271954 1432687 := bstep (se 1 (by rfl) ⟨1074515, by rfl⟩ : syracuseStep 1432687 = 2149031) B2149031
theorem B9297119 : Blo 1271954 9297119 := bstep (se 1 (by rfl) ⟨6972839, by rfl⟩ : syracuseStep 9297119 = 13945679) B13945679
theorem B18603341 : Blo 1271954 18603341 := bstep (se 3 (by rfl) ⟨3488126, by rfl⟩ : syracuseStep 18603341 = 6976253) B6976253
theorem B1908089 : Blo 1271954 1908089 := bstep (se 2 (by rfl) ⟨715533, by rfl⟩ : syracuseStep 1908089 = 1431067) B1431067
theorem B156695953 : Blo 1271954 156695953 := bstep (se 2 (by rfl) ⟨58760982, by rfl⟩ : syracuseStep 156695953 = 117521965) B117521965
theorem B12393935 : Blo 1271954 12393935 := bstep (se 1 (by rfl) ⟨9295451, by rfl⟩ : syracuseStep 12393935 = 18590903) B18590903
theorem B1908863 : Blo 1271954 1908863 := bstep (se 1 (by rfl) ⟨1431647, by rfl⟩ : syracuseStep 1908863 = 2863295) B2863295
theorem B1908959 : Blo 1271954 1908959 := bstep (se 1 (by rfl) ⟨1431719, by rfl⟩ : syracuseStep 1908959 = 2863439) B2863439
theorem B1908971 : Blo 1271954 1908971 := bstep (se 1 (by rfl) ⟨1431728, by rfl⟩ : syracuseStep 1908971 = 2863457) B2863457
theorem B1909247 : Blo 1271954 1909247 := bstep (se 1 (by rfl) ⟨1431935, by rfl⟩ : syracuseStep 1909247 = 2863871) B2863871
theorem B446522159 : Blo 1271954 446522159 := bstep (se 1 (by rfl) ⟨334891619, by rfl⟩ : syracuseStep 446522159 = 669783239) B669783239
theorem B18351323 : Blo 1271954 18351323 := bstep (se 1 (by rfl) ⟨13763492, by rfl⟩ : syracuseStep 18351323 = 27526985) B27526985
theorem B3622265 : Blo 1271954 3622265 := bstep (se 2 (by rfl) ⟨1358349, by rfl⟩ : syracuseStep 3622265 = 2716699) B2716699
theorem B1910249 : Blo 1271954 1910249 := bstep (se 2 (by rfl) ⟨716343, by rfl⟩ : syracuseStep 1910249 = 1432687) B1432687
theorem B3221147 : Blo 1271954 3221147 := bstep (se 1 (by rfl) ⟨2415860, by rfl⟩ : syracuseStep 3221147 = 4831721) B4831721
theorem B1272059 : Blo 1271954 1272059 := bstep (se 1 (by rfl) ⟨954044, by rfl⟩ : syracuseStep 1272059 = 1908089) B1908089
theorem B4835807 : Blo 1271954 4835807 := bstep (se 1 (by rfl) ⟨3626855, by rfl⟩ : syracuseStep 4835807 = 7253711) B7253711
theorem B1273343 : Blo 1271954 1273343 := bstep (se 1 (by rfl) ⟨955007, by rfl⟩ : syracuseStep 1273343 = 1910015) B1910015
theorem B1273703 : Blo 1271954 1273703 := bstep (se 1 (by rfl) ⟨955277, by rfl⟩ : syracuseStep 1273703 = 1910555) B1910555
theorem B1273759 : Blo 1271954 1273759 := bstep (se 1 (by rfl) ⟨955319, by rfl⟩ : syracuseStep 1273759 = 1910639) B1910639
theorem B4296887 : Blo 1271954 4296887 := bstep (se 1 (by rfl) ⟨3222665, by rfl⟩ : syracuseStep 4296887 = 6445331) B6445331
theorem B6198079 : Blo 1271954 6198079 := bstep (se 1 (by rfl) ⟨4648559, by rfl⟩ : syracuseStep 6198079 = 9297119) B9297119
theorem B12227449 : Blo 1271954 12227449 := bstep (se 2 (by rfl) ⟨4585293, by rfl⟩ : syracuseStep 12227449 = 9170587) B9170587
theorem B8262623 : Blo 1271954 8262623 := bstep (se 1 (by rfl) ⟨6196967, by rfl⟩ : syracuseStep 8262623 = 12393935) B12393935
theorem B6117245 : Blo 1271954 6117245 := bstep (se 3 (by rfl) ⟨1146983, by rfl⟩ : syracuseStep 6117245 = 2293967) B2293967
theorem B69679439 : Blo 1271954 69679439 := bstep (se 1 (by rfl) ⟨52259579, by rfl⟩ : syracuseStep 69679439 = 104519159) B104519159
theorem B13752767 : Blo 1271954 13752767 := bstep (se 1 (by rfl) ⟨10314575, by rfl⟩ : syracuseStep 13752767 = 20629151) B20629151
theorem B2415329 : Blo 1271954 2415329 := bstep (se 2 (by rfl) ⟨905748, by rfl⟩ : syracuseStep 2415329 = 1811497) B1811497
theorem B14507099 : Blo 1271954 14507099 := bstep (se 1 (by rfl) ⟨10880324, by rfl⟩ : syracuseStep 14507099 = 21760649) B21760649
theorem B208927937 : Blo 1271954 208927937 := bstep (se 2 (by rfl) ⟨78347976, by rfl⟩ : syracuseStep 208927937 = 156695953) B156695953
theorem B9936107 : Blo 1271954 9936107 := bstep (se 1 (by rfl) ⟨7452080, by rfl⟩ : syracuseStep 9936107 = 14904161) B14904161
theorem B12402227 : Blo 1271954 12402227 := bstep (se 1 (by rfl) ⟨9301670, by rfl⟩ : syracuseStep 12402227 = 18603341) B18603341
theorem B1908431 : Blo 1271954 1908431 := bstep (se 1 (by rfl) ⟨1431323, by rfl⟩ : syracuseStep 1908431 = 2862647) B2862647
theorem B8150867 : Blo 1271954 8150867 := bstep (se 1 (by rfl) ⟨6113150, by rfl⟩ : syracuseStep 8150867 = 12226301) B12226301
theorem B7249769 : Blo 1271954 7249769 := bstep (se 2 (by rfl) ⟨2718663, by rfl⟩ : syracuseStep 7249769 = 5437327) B5437327
theorem B297681439 : Blo 1271954 297681439 := bstep (se 1 (by rfl) ⟨223261079, by rfl⟩ : syracuseStep 297681439 = 446522159) B446522159
theorem B2147431 : Blo 1271954 2147431 := bstep (se 1 (by rfl) ⟨1610573, by rfl⟩ : syracuseStep 2147431 = 3221147) B3221147
theorem B16303265 : Blo 1271954 16303265 := bstep (se 2 (by rfl) ⟨6113724, by rfl⟩ : syracuseStep 16303265 = 12227449) B12227449
theorem B8268151 : Blo 1271954 8268151 := bstep (se 1 (by rfl) ⟨6201113, by rfl⟩ : syracuseStep 8268151 = 12402227) B12402227
theorem B1272287 : Blo 1271954 1272287 := bstep (se 1 (by rfl) ⟨954215, by rfl⟩ : syracuseStep 1272287 = 1908431) B1908431
theorem B5433911 : Blo 1271954 5433911 := bstep (se 1 (by rfl) ⟨4075433, by rfl⟩ : syracuseStep 5433911 = 8150867) B8150867
theorem B1272575 : Blo 1271954 1272575 := bstep (se 1 (by rfl) ⟨954431, by rfl⟩ : syracuseStep 1272575 = 1908863) B1908863
theorem B1272639 : Blo 1271954 1272639 := bstep (se 1 (by rfl) ⟨954479, by rfl⟩ : syracuseStep 1272639 = 1908959) B1908959
theorem B1272647 : Blo 1271954 1272647 := bstep (se 1 (by rfl) ⟨954485, by rfl⟩ : syracuseStep 1272647 = 1908971) B1908971
theorem B1272831 : Blo 1271954 1272831 := bstep (se 1 (by rfl) ⟨954623, by rfl⟩ : syracuseStep 1272831 = 1909247) B1909247
theorem B5508415 : Blo 1271954 5508415 := bstep (se 1 (by rfl) ⟨4131311, by rfl⟩ : syracuseStep 5508415 = 8262623) B8262623
theorem B12234215 : Blo 1271954 12234215 := bstep (se 1 (by rfl) ⟨9175661, by rfl⟩ : syracuseStep 12234215 = 18351323) B18351323
theorem B1273499 : Blo 1271954 1273499 := bstep (se 1 (by rfl) ⟨955124, by rfl⟩ : syracuseStep 1273499 = 1910249) B1910249
theorem B46452959 : Blo 1271954 46452959 := bstep (se 1 (by rfl) ⟨34839719, by rfl⟩ : syracuseStep 46452959 = 69679439) B69679439
theorem B3223871 : Blo 1271954 3223871 := bstep (se 1 (by rfl) ⟨2417903, by rfl⟩ : syracuseStep 3223871 = 4835807) B4835807
theorem B1610219 : Blo 1271954 1610219 := bstep (se 1 (by rfl) ⟨1207664, by rfl⟩ : syracuseStep 1610219 = 2415329) B2415329
theorem B9671399 : Blo 1271954 9671399 := bstep (se 1 (by rfl) ⟨7253549, by rfl⟩ : syracuseStep 9671399 = 14507099) B14507099
theorem B139285291 : Blo 1271954 139285291 := bstep (se 1 (by rfl) ⟨104463968, by rfl⟩ : syracuseStep 139285291 = 208927937) B208927937
theorem B6624071 : Blo 1271954 6624071 := bstep (se 1 (by rfl) ⟨4968053, by rfl⟩ : syracuseStep 6624071 = 9936107) B9936107
theorem B2864591 : Blo 1271954 2864591 := bstep (se 1 (by rfl) ⟨2148443, by rfl⟩ : syracuseStep 2864591 = 4296887) B4296887
theorem B2414843 : Blo 1271954 2414843 := bstep (se 1 (by rfl) ⟨1811132, by rfl⟩ : syracuseStep 2414843 = 3622265) B3622265
theorem B8264105 : Blo 1271954 8264105 := bstep (se 2 (by rfl) ⟨3099039, by rfl⟩ : syracuseStep 8264105 = 6198079) B6198079
theorem B36674045 : Blo 1271954 36674045 := bstep (se 3 (by rfl) ⟨6876383, by rfl⟩ : syracuseStep 36674045 = 13752767) B13752767
theorem B4078163 : Blo 1271954 4078163 := bstep (se 1 (by rfl) ⟨3058622, by rfl⟩ : syracuseStep 4078163 = 6117245) B6117245
theorem B4833179 : Blo 1271954 4833179 := bstep (se 1 (by rfl) ⟨3624884, by rfl⟩ : syracuseStep 4833179 = 7249769) B7249769
theorem B6447599 : Blo 1271954 6447599 := bstep (se 1 (by rfl) ⟨4835699, by rfl⟩ : syracuseStep 6447599 = 9671399) B9671399
theorem B4416047 : Blo 1271954 4416047 := bstep (se 1 (by rfl) ⟨3312035, by rfl⟩ : syracuseStep 4416047 = 6624071) B6624071
theorem B1909727 : Blo 1271954 1909727 := bstep (se 1 (by rfl) ⟨1432295, by rfl⟩ : syracuseStep 1909727 = 2864591) B2864591
theorem B185713721 : Blo 1271954 185713721 := bstep (se 2 (by rfl) ⟨69642645, by rfl⟩ : syracuseStep 185713721 = 139285291) B139285291
theorem B4293917 : Blo 1271954 4293917 := bstep (se 3 (by rfl) ⟨805109, by rfl⟩ : syracuseStep 4293917 = 1610219) B1610219
theorem B29378213 : Blo 1271954 29378213 := bstep (se 4 (by rfl) ⟨2754207, by rfl⟩ : syracuseStep 29378213 = 5508415) B5508415
theorem B3622607 : Blo 1271954 3622607 := bstep (se 1 (by rfl) ⟨2716955, by rfl⟩ : syracuseStep 3622607 = 5433911) B5433911
theorem B3222119 : Blo 1271954 3222119 := bstep (se 1 (by rfl) ⟨2416589, by rfl⟩ : syracuseStep 3222119 = 4833179) B4833179
theorem B30968639 : Blo 1271954 30968639 := bstep (se 1 (by rfl) ⟨23226479, by rfl⟩ : syracuseStep 30968639 = 46452959) B46452959
theorem B2149247 : Blo 1271954 2149247 := bstep (se 1 (by rfl) ⟨1611935, by rfl⟩ : syracuseStep 2149247 = 3223871) B3223871
theorem B2863241 : Blo 1271954 2863241 := bstep (se 2 (by rfl) ⟨1073715, by rfl⟩ : syracuseStep 2863241 = 2147431) B2147431
theorem B1609895 : Blo 1271954 1609895 := bstep (se 1 (by rfl) ⟨1207421, by rfl⟩ : syracuseStep 1609895 = 2414843) B2414843
theorem B5509403 : Blo 1271954 5509403 := bstep (se 1 (by rfl) ⟨4132052, by rfl⟩ : syracuseStep 5509403 = 8264105) B8264105
theorem B24449363 : Blo 1271954 24449363 := bstep (se 1 (by rfl) ⟨18337022, by rfl⟩ : syracuseStep 24449363 = 36674045) B36674045
theorem B8156143 : Blo 1271954 8156143 := bstep (se 1 (by rfl) ⟨6117107, by rfl⟩ : syracuseStep 8156143 = 12234215) B12234215
theorem B11024201 : Blo 1271954 11024201 := bstep (se 2 (by rfl) ⟨4134075, by rfl⟩ : syracuseStep 11024201 = 8268151) B8268151
theorem B396908585 : Blo 1271954 396908585 := bstep (se 2 (by rfl) ⟨148840719, by rfl⟩ : syracuseStep 396908585 = 297681439) B297681439
theorem B10868843 : Blo 1271954 10868843 := bstep (se 1 (by rfl) ⟨8151632, by rfl⟩ : syracuseStep 10868843 = 16303265) B16303265
theorem B2718775 : Blo 1271954 2718775 := bstep (se 1 (by rfl) ⟨2039081, by rfl⟩ : syracuseStep 2718775 = 4078163) B4078163
theorem B1908827 : Blo 1271954 1908827 := bstep (se 1 (by rfl) ⟨1431620, by rfl⟩ : syracuseStep 1908827 = 2863241) B2863241
theorem B4293053 : Blo 1271954 4293053 := bstep (se 3 (by rfl) ⟨804947, by rfl⟩ : syracuseStep 4293053 = 1609895) B1609895
theorem B7349467 : Blo 1271954 7349467 := bstep (se 1 (by rfl) ⟨5512100, by rfl⟩ : syracuseStep 7349467 = 11024201) B11024201
theorem B2148079 : Blo 1271954 2148079 := bstep (se 1 (by rfl) ⟨1611059, by rfl⟩ : syracuseStep 2148079 = 3222119) B3222119
theorem B20645759 : Blo 1271954 20645759 := bstep (se 1 (by rfl) ⟨15484319, by rfl⟩ : syracuseStep 20645759 = 30968639) B30968639
theorem B3672935 : Blo 1271954 3672935 := bstep (se 1 (by rfl) ⟨2754701, by rfl⟩ : syracuseStep 3672935 = 5509403) B5509403
theorem B2944031 : Blo 1271954 2944031 := bstep (se 1 (by rfl) ⟨2208023, by rfl⟩ : syracuseStep 2944031 = 4416047) B4416047
theorem B1273151 : Blo 1271954 1273151 := bstep (se 1 (by rfl) ⟨954863, by rfl⟩ : syracuseStep 1273151 = 1909727) B1909727
theorem B123809147 : Blo 1271954 123809147 := bstep (se 1 (by rfl) ⟨92856860, by rfl⟩ : syracuseStep 123809147 = 185713721) B185713721
theorem B2862611 : Blo 1271954 2862611 := bstep (se 1 (by rfl) ⟨2146958, by rfl⟩ : syracuseStep 2862611 = 4293917) B4293917
theorem B10874857 : Blo 1271954 10874857 := bstep (se 2 (by rfl) ⟨4078071, by rfl⟩ : syracuseStep 10874857 = 8156143) B8156143
theorem B264605723 : Blo 1271954 264605723 := bstep (se 1 (by rfl) ⟨198454292, by rfl⟩ : syracuseStep 264605723 = 396908585) B396908585
theorem B7245895 : Blo 1271954 7245895 := bstep (se 1 (by rfl) ⟨5434421, by rfl⟩ : syracuseStep 7245895 = 10868843) B10868843
theorem B3625033 : Blo 1271954 3625033 := bstep (se 2 (by rfl) ⟨1359387, by rfl⟩ : syracuseStep 3625033 = 2718775) B2718775
theorem B16299575 : Blo 1271954 16299575 := bstep (se 1 (by rfl) ⟨12224681, by rfl⟩ : syracuseStep 16299575 = 24449363) B24449363
theorem B4298399 : Blo 1271954 4298399 := bstep (se 1 (by rfl) ⟨3223799, by rfl⟩ : syracuseStep 4298399 = 6447599) B6447599
theorem B19585475 : Blo 1271954 19585475 := bstep (se 1 (by rfl) ⟨14689106, by rfl⟩ : syracuseStep 19585475 = 29378213) B29378213
theorem B2415071 : Blo 1271954 2415071 := bstep (se 1 (by rfl) ⟨1811303, by rfl⟩ : syracuseStep 2415071 = 3622607) B3622607
theorem B1432831 : Blo 1271954 1432831 := bstep (se 1 (by rfl) ⟨1074623, by rfl⟩ : syracuseStep 1432831 = 2149247) B2149247
theorem B4833377 : Blo 1271954 4833377 := bstep (se 2 (by rfl) ⟨1812516, by rfl⟩ : syracuseStep 4833377 = 3625033) B3625033
theorem B13763839 : Blo 1271954 13763839 := bstep (se 1 (by rfl) ⟨10322879, by rfl⟩ : syracuseStep 13763839 = 20645759) B20645759
theorem B9799289 : Blo 1271954 9799289 := bstep (se 2 (by rfl) ⟨3674733, by rfl⟩ : syracuseStep 9799289 = 7349467) B7349467
theorem B1910441 : Blo 1271954 1910441 := bstep (se 2 (by rfl) ⟨716415, by rfl⟩ : syracuseStep 1910441 = 1432831) B1432831
theorem B1272551 : Blo 1271954 1272551 := bstep (se 1 (by rfl) ⟨954413, by rfl⟩ : syracuseStep 1272551 = 1908827) B1908827
theorem B9661193 : Blo 1271954 9661193 := bstep (se 2 (by rfl) ⟨3622947, by rfl⟩ : syracuseStep 9661193 = 7245895) B7245895
theorem B2862035 : Blo 1271954 2862035 := bstep (se 1 (by rfl) ⟨2146526, by rfl⟩ : syracuseStep 2862035 = 4293053) B4293053
theorem B31402997 : Blo 1271954 31402997 := bstep (se 5 (by rfl) ⟨1472015, by rfl⟩ : syracuseStep 31402997 = 2944031) B2944031
theorem B10866383 : Blo 1271954 10866383 := bstep (se 1 (by rfl) ⟨8149787, by rfl⟩ : syracuseStep 10866383 = 16299575) B16299575
theorem B1610047 : Blo 1271954 1610047 := bstep (se 1 (by rfl) ⟨1207535, by rfl⟩ : syracuseStep 1610047 = 2415071) B2415071
theorem B82539431 : Blo 1271954 82539431 := bstep (se 1 (by rfl) ⟨61904573, by rfl⟩ : syracuseStep 82539431 = 123809147) B123809147
theorem B2864105 : Blo 1271954 2864105 := bstep (se 2 (by rfl) ⟨1074039, by rfl⟩ : syracuseStep 2864105 = 2148079) B2148079
theorem B176403815 : Blo 1271954 176403815 := bstep (se 1 (by rfl) ⟨132302861, by rfl⟩ : syracuseStep 176403815 = 264605723) B264605723
theorem B2865599 : Blo 1271954 2865599 := bstep (se 1 (by rfl) ⟨2149199, by rfl⟩ : syracuseStep 2865599 = 4298399) B4298399
theorem B13056983 : Blo 1271954 13056983 := bstep (se 1 (by rfl) ⟨9792737, by rfl⟩ : syracuseStep 13056983 = 19585475) B19585475
theorem B2448623 : Blo 1271954 2448623 := bstep (se 1 (by rfl) ⟨1836467, by rfl⟩ : syracuseStep 2448623 = 3672935) B3672935
theorem B1908407 : Blo 1271954 1908407 := bstep (se 1 (by rfl) ⟨1431305, by rfl⟩ : syracuseStep 1908407 = 2862611) B2862611
theorem B14499809 : Blo 1271954 14499809 := bstep (se 2 (by rfl) ⟨5437428, by rfl⟩ : syracuseStep 14499809 = 10874857) B10874857
theorem B2146729 : Blo 1271954 2146729 := bstep (se 2 (by rfl) ⟨805023, by rfl⟩ : syracuseStep 2146729 = 1610047) B1610047
theorem B55026287 : Blo 1271954 55026287 := bstep (se 1 (by rfl) ⟨41269715, by rfl⟩ : syracuseStep 55026287 = 82539431) B82539431
theorem B1909403 : Blo 1271954 1909403 := bstep (se 1 (by rfl) ⟨1432052, by rfl⟩ : syracuseStep 1909403 = 2864105) B2864105
theorem B1910399 : Blo 1271954 1910399 := bstep (se 1 (by rfl) ⟨1432799, by rfl⟩ : syracuseStep 1910399 = 2865599) B2865599
theorem B18351785 : Blo 1271954 18351785 := bstep (se 2 (by rfl) ⟨6881919, by rfl⟩ : syracuseStep 18351785 = 13763839) B13763839
theorem B6440795 : Blo 1271954 6440795 := bstep (se 1 (by rfl) ⟨4830596, by rfl⟩ : syracuseStep 6440795 = 9661193) B9661193
theorem B1632415 : Blo 1271954 1632415 := bstep (se 1 (by rfl) ⟨1224311, by rfl⟩ : syracuseStep 1632415 = 2448623) B2448623
theorem B1272271 : Blo 1271954 1272271 := bstep (se 1 (by rfl) ⟨954203, by rfl⟩ : syracuseStep 1272271 = 1908407) B1908407
theorem B7244255 : Blo 1271954 7244255 := bstep (se 1 (by rfl) ⟨5433191, by rfl⟩ : syracuseStep 7244255 = 10866383) B10866383
theorem B3222251 : Blo 1271954 3222251 := bstep (se 1 (by rfl) ⟨2416688, by rfl⟩ : syracuseStep 3222251 = 4833377) B4833377
theorem B6532859 : Blo 1271954 6532859 := bstep (se 1 (by rfl) ⟨4899644, by rfl⟩ : syracuseStep 6532859 = 9799289) B9799289
theorem B1273627 : Blo 1271954 1273627 := bstep (se 1 (by rfl) ⟨955220, by rfl⟩ : syracuseStep 1273627 = 1910441) B1910441
theorem B8704655 : Blo 1271954 8704655 := bstep (se 1 (by rfl) ⟨6528491, by rfl⟩ : syracuseStep 8704655 = 13056983) B13056983
theorem B20935331 : Blo 1271954 20935331 := bstep (se 1 (by rfl) ⟨15701498, by rfl⟩ : syracuseStep 20935331 = 31402997) B31402997
theorem B117602543 : Blo 1271954 117602543 := bstep (se 1 (by rfl) ⟨88201907, by rfl⟩ : syracuseStep 117602543 = 176403815) B176403815
theorem B1908023 : Blo 1271954 1908023 := bstep (se 1 (by rfl) ⟨1431017, by rfl⟩ : syracuseStep 1908023 = 2862035) B2862035
theorem B9666539 : Blo 1271954 9666539 := bstep (se 1 (by rfl) ⟨7249904, by rfl⟩ : syracuseStep 9666539 = 14499809) B14499809
theorem B36684191 : Blo 1271954 36684191 := bstep (se 1 (by rfl) ⟨27513143, by rfl⟩ : syracuseStep 36684191 = 55026287) B55026287
theorem B4293863 : Blo 1271954 4293863 := bstep (se 1 (by rfl) ⟨3220397, by rfl⟩ : syracuseStep 4293863 = 6440795) B6440795
theorem B2148167 : Blo 1271954 2148167 := bstep (se 1 (by rfl) ⟨1611125, by rfl⟩ : syracuseStep 2148167 = 3222251) B3222251
theorem B1272015 : Blo 1271954 1272015 := bstep (se 1 (by rfl) ⟨954011, by rfl⟩ : syracuseStep 1272015 = 1908023) B1908023
theorem B5803103 : Blo 1271954 5803103 := bstep (se 1 (by rfl) ⟨4352327, by rfl⟩ : syracuseStep 5803103 = 8704655) B8704655
theorem B1272935 : Blo 1271954 1272935 := bstep (se 1 (by rfl) ⟨954701, by rfl⟩ : syracuseStep 1272935 = 1909403) B1909403
theorem B2862305 : Blo 1271954 2862305 := bstep (se 2 (by rfl) ⟨1073364, by rfl⟩ : syracuseStep 2862305 = 2146729) B2146729
theorem B1273599 : Blo 1271954 1273599 := bstep (se 1 (by rfl) ⟨955199, by rfl⟩ : syracuseStep 1273599 = 1910399) B1910399
theorem B12234523 : Blo 1271954 12234523 := bstep (se 1 (by rfl) ⟨9175892, by rfl⟩ : syracuseStep 12234523 = 18351785) B18351785
theorem B78401695 : Blo 1271954 78401695 := bstep (se 1 (by rfl) ⟨58801271, by rfl⟩ : syracuseStep 78401695 = 117602543) B117602543
theorem B4829503 : Blo 1271954 4829503 := bstep (se 1 (by rfl) ⟨3622127, by rfl⟩ : syracuseStep 4829503 = 7244255) B7244255
theorem B4355239 : Blo 1271954 4355239 := bstep (se 1 (by rfl) ⟨3266429, by rfl⟩ : syracuseStep 4355239 = 6532859) B6532859
theorem B6444359 : Blo 1271954 6444359 := bstep (se 1 (by rfl) ⟨4833269, by rfl⟩ : syracuseStep 6444359 = 9666539) B9666539
theorem B2176553 : Blo 1271954 2176553 := bstep (se 2 (by rfl) ⟨816207, by rfl⟩ : syracuseStep 2176553 = 1632415) B1632415
theorem B13956887 : Blo 1271954 13956887 := bstep (se 1 (by rfl) ⟨10467665, by rfl⟩ : syracuseStep 13956887 = 20935331) B20935331
theorem B6439337 : Blo 1271954 6439337 := bstep (se 2 (by rfl) ⟨2414751, by rfl⟩ : syracuseStep 6439337 = 4829503) B4829503
theorem B1451035 : Blo 1271954 1451035 := bstep (se 1 (by rfl) ⟨1088276, by rfl⟩ : syracuseStep 1451035 = 2176553) B2176553
theorem B37218365 : Blo 1271954 37218365 := bstep (se 3 (by rfl) ⟨6978443, by rfl⟩ : syracuseStep 37218365 = 13956887) B13956887
theorem B3868735 : Blo 1271954 3868735 := bstep (se 1 (by rfl) ⟨2901551, by rfl⟩ : syracuseStep 3868735 = 5803103) B5803103
theorem B16312697 : Blo 1271954 16312697 := bstep (se 2 (by rfl) ⟨6117261, by rfl⟩ : syracuseStep 16312697 = 12234523) B12234523
theorem B24456127 : Blo 1271954 24456127 := bstep (se 1 (by rfl) ⟨18342095, by rfl⟩ : syracuseStep 24456127 = 36684191) B36684191
theorem B2862575 : Blo 1271954 2862575 := bstep (se 1 (by rfl) ⟨2146931, by rfl⟩ : syracuseStep 2862575 = 4293863) B4293863
theorem B4296239 : Blo 1271954 4296239 := bstep (se 1 (by rfl) ⟨3222179, by rfl⟩ : syracuseStep 4296239 = 6444359) B6444359
theorem B104535593 : Blo 1271954 104535593 := bstep (se 2 (by rfl) ⟨39200847, by rfl⟩ : syracuseStep 104535593 = 78401695) B78401695
theorem B1432111 : Blo 1271954 1432111 := bstep (se 1 (by rfl) ⟨1074083, by rfl⟩ : syracuseStep 1432111 = 2148167) B2148167
theorem B5806985 : Blo 1271954 5806985 := bstep (se 2 (by rfl) ⟨2177619, by rfl⟩ : syracuseStep 5806985 = 4355239) B4355239
theorem B1908203 : Blo 1271954 1908203 := bstep (se 1 (by rfl) ⟨1431152, by rfl⟩ : syracuseStep 1908203 = 2862305) B2862305
theorem B4292891 : Blo 1271954 4292891 := bstep (se 1 (by rfl) ⟨3219668, by rfl⟩ : syracuseStep 4292891 = 6439337) B6439337
theorem B1909481 : Blo 1271954 1909481 := bstep (se 2 (by rfl) ⟨716055, by rfl⟩ : syracuseStep 1909481 = 1432111) B1432111
theorem B69690395 : Blo 1271954 69690395 := bstep (se 1 (by rfl) ⟨52267796, by rfl⟩ : syracuseStep 69690395 = 104535593) B104535593
theorem B1934713 : Blo 1271954 1934713 := bstep (se 2 (by rfl) ⟨725517, by rfl⟩ : syracuseStep 1934713 = 1451035) B1451035
theorem B1272135 : Blo 1271954 1272135 := bstep (se 1 (by rfl) ⟨954101, by rfl⟩ : syracuseStep 1272135 = 1908203) B1908203
theorem B15485293 : Blo 1271954 15485293 := bstep (se 3 (by rfl) ⟨2903492, by rfl⟩ : syracuseStep 15485293 = 5806985) B5806985
theorem B32608169 : Blo 1271954 32608169 := bstep (se 2 (by rfl) ⟨12228063, by rfl⟩ : syracuseStep 32608169 = 24456127) B24456127
theorem B10875131 : Blo 1271954 10875131 := bstep (se 1 (by rfl) ⟨8156348, by rfl⟩ : syracuseStep 10875131 = 16312697) B16312697
theorem B2864159 : Blo 1271954 2864159 := bstep (se 1 (by rfl) ⟨2148119, by rfl⟩ : syracuseStep 2864159 = 4296239) B4296239
theorem B5158313 : Blo 1271954 5158313 := bstep (se 2 (by rfl) ⟨1934367, by rfl⟩ : syracuseStep 5158313 = 3868735) B3868735
theorem B24812243 : Blo 1271954 24812243 := bstep (se 1 (by rfl) ⟨18609182, by rfl⟩ : syracuseStep 24812243 = 37218365) B37218365
theorem B1908383 : Blo 1271954 1908383 := bstep (se 1 (by rfl) ⟨1431287, by rfl⟩ : syracuseStep 1908383 = 2862575) B2862575
theorem B7250087 : Blo 1271954 7250087 := bstep (se 1 (by rfl) ⟨5437565, by rfl⟩ : syracuseStep 7250087 = 10875131) B10875131
theorem B1909439 : Blo 1271954 1909439 := bstep (se 1 (by rfl) ⟨1432079, by rfl⟩ : syracuseStep 1909439 = 2864159) B2864159
theorem B16541495 : Blo 1271954 16541495 := bstep (se 1 (by rfl) ⟨12406121, by rfl⟩ : syracuseStep 16541495 = 24812243) B24812243
theorem B1272255 : Blo 1271954 1272255 := bstep (se 1 (by rfl) ⟨954191, by rfl⟩ : syracuseStep 1272255 = 1908383) B1908383
theorem B2861927 : Blo 1271954 2861927 := bstep (se 1 (by rfl) ⟨2146445, by rfl⟩ : syracuseStep 2861927 = 4292891) B4292891
theorem B20647057 : Blo 1271954 20647057 := bstep (se 2 (by rfl) ⟨7742646, by rfl⟩ : syracuseStep 20647057 = 15485293) B15485293
theorem B1272987 : Blo 1271954 1272987 := bstep (se 1 (by rfl) ⟨954740, by rfl⟩ : syracuseStep 1272987 = 1909481) B1909481
theorem B46460263 : Blo 1271954 46460263 := bstep (se 1 (by rfl) ⟨34845197, by rfl⟩ : syracuseStep 46460263 = 69690395) B69690395
theorem B21738779 : Blo 1271954 21738779 := bstep (se 1 (by rfl) ⟨16304084, by rfl⟩ : syracuseStep 21738779 = 32608169) B32608169
theorem B3438875 : Blo 1271954 3438875 := bstep (se 1 (by rfl) ⟨2579156, by rfl⟩ : syracuseStep 3438875 = 5158313) B5158313
theorem B2579617 : Blo 1271954 2579617 := bstep (se 2 (by rfl) ⟨967356, by rfl⟩ : syracuseStep 2579617 = 1934713) B1934713
theorem B4833391 : Blo 1271954 4833391 := bstep (se 1 (by rfl) ⟨3625043, by rfl⟩ : syracuseStep 4833391 = 7250087) B7250087
theorem B14492519 : Blo 1271954 14492519 := bstep (se 1 (by rfl) ⟨10869389, by rfl⟩ : syracuseStep 14492519 = 21738779) B21738779
theorem B11027663 : Blo 1271954 11027663 := bstep (se 1 (by rfl) ⟨8270747, by rfl⟩ : syracuseStep 11027663 = 16541495) B16541495
theorem B1272959 : Blo 1271954 1272959 := bstep (se 1 (by rfl) ⟨954719, by rfl⟩ : syracuseStep 1272959 = 1909439) B1909439
theorem B9170333 : Blo 1271954 9170333 := bstep (se 3 (by rfl) ⟨1719437, by rfl⟩ : syracuseStep 9170333 = 3438875) B3438875
theorem B13757957 : Blo 1271954 13757957 := bstep (se 4 (by rfl) ⟨1289808, by rfl⟩ : syracuseStep 13757957 = 2579617) B2579617
theorem B27529409 : Blo 1271954 27529409 := bstep (se 2 (by rfl) ⟨10323528, by rfl⟩ : syracuseStep 27529409 = 20647057) B20647057
theorem B61947017 : Blo 1271954 61947017 := bstep (se 2 (by rfl) ⟨23230131, by rfl⟩ : syracuseStep 61947017 = 46460263) B46460263
theorem B1907951 : Blo 1271954 1907951 := bstep (se 1 (by rfl) ⟨1430963, by rfl⟩ : syracuseStep 1907951 = 2861927) B2861927
theorem B41298011 : Blo 1271954 41298011 := bstep (se 1 (by rfl) ⟨30973508, by rfl⟩ : syracuseStep 41298011 = 61947017) B61947017
theorem B1271967 : Blo 1271954 1271967 := bstep (se 1 (by rfl) ⟨953975, by rfl⟩ : syracuseStep 1271967 = 1907951) B1907951
theorem B6113555 : Blo 1271954 6113555 := bstep (se 1 (by rfl) ⟨4585166, by rfl⟩ : syracuseStep 6113555 = 9170333) B9170333
theorem B18352939 : Blo 1271954 18352939 := bstep (se 1 (by rfl) ⟨13764704, by rfl⟩ : syracuseStep 18352939 = 27529409) B27529409
theorem B9661679 : Blo 1271954 9661679 := bstep (se 1 (by rfl) ⟨7246259, by rfl⟩ : syracuseStep 9661679 = 14492519) B14492519
theorem B7351775 : Blo 1271954 7351775 := bstep (se 1 (by rfl) ⟨5513831, by rfl⟩ : syracuseStep 7351775 = 11027663) B11027663
theorem B9171971 : Blo 1271954 9171971 := bstep (se 1 (by rfl) ⟨6878978, by rfl⟩ : syracuseStep 9171971 = 13757957) B13757957
theorem B6444521 : Blo 1271954 6444521 := bstep (se 2 (by rfl) ⟨2416695, by rfl⟩ : syracuseStep 6444521 = 4833391) B4833391
theorem B24470585 : Blo 1271954 24470585 := bstep (se 2 (by rfl) ⟨9176469, by rfl⟩ : syracuseStep 24470585 = 18352939) B18352939
theorem B6441119 : Blo 1271954 6441119 := bstep (se 1 (by rfl) ⟨4830839, by rfl⟩ : syracuseStep 6441119 = 9661679) B9661679
theorem B4901183 : Blo 1271954 4901183 := bstep (se 1 (by rfl) ⟨3675887, by rfl⟩ : syracuseStep 4901183 = 7351775) B7351775
theorem B6114647 : Blo 1271954 6114647 := bstep (se 1 (by rfl) ⟨4585985, by rfl⟩ : syracuseStep 6114647 = 9171971) B9171971
theorem B4296347 : Blo 1271954 4296347 := bstep (se 1 (by rfl) ⟨3222260, by rfl⟩ : syracuseStep 4296347 = 6444521) B6444521
theorem B4075703 : Blo 1271954 4075703 := bstep (se 1 (by rfl) ⟨3056777, by rfl⟩ : syracuseStep 4075703 = 6113555) B6113555
theorem B27532007 : Blo 1271954 27532007 := bstep (se 1 (by rfl) ⟨20649005, by rfl⟩ : syracuseStep 27532007 = 41298011) B41298011
theorem B4294079 : Blo 1271954 4294079 := bstep (se 1 (by rfl) ⟨3220559, by rfl⟩ : syracuseStep 4294079 = 6441119) B6441119
theorem B16313723 : Blo 1271954 16313723 := bstep (se 1 (by rfl) ⟨12235292, by rfl⟩ : syracuseStep 16313723 = 24470585) B24470585
theorem B16305725 : Blo 1271954 16305725 := bstep (se 3 (by rfl) ⟨3057323, by rfl⟩ : syracuseStep 16305725 = 6114647) B6114647
theorem B18354671 : Blo 1271954 18354671 := bstep (se 1 (by rfl) ⟨13766003, by rfl⟩ : syracuseStep 18354671 = 27532007) B27532007
theorem B2864231 : Blo 1271954 2864231 := bstep (se 1 (by rfl) ⟨2148173, by rfl⟩ : syracuseStep 2864231 = 4296347) B4296347
theorem B2717135 : Blo 1271954 2717135 := bstep (se 1 (by rfl) ⟨2037851, by rfl⟩ : syracuseStep 2717135 = 4075703) B4075703
theorem B3267455 : Blo 1271954 3267455 := bstep (se 1 (by rfl) ⟨2450591, by rfl⟩ : syracuseStep 3267455 = 4901183) B4901183
theorem B1909487 : Blo 1271954 1909487 := bstep (se 1 (by rfl) ⟨1432115, by rfl⟩ : syracuseStep 1909487 = 2864231) B2864231
theorem B1811423 : Blo 1271954 1811423 := bstep (se 1 (by rfl) ⟨1358567, by rfl⟩ : syracuseStep 1811423 = 2717135) B2717135
theorem B2862719 : Blo 1271954 2862719 := bstep (se 1 (by rfl) ⟨2147039, by rfl⟩ : syracuseStep 2862719 = 4294079) B4294079
theorem B10875815 : Blo 1271954 10875815 := bstep (se 1 (by rfl) ⟨8156861, by rfl⟩ : syracuseStep 10875815 = 16313723) B16313723
theorem B8713213 : Blo 1271954 8713213 := bstep (se 3 (by rfl) ⟨1633727, by rfl⟩ : syracuseStep 8713213 = 3267455) B3267455
theorem B12236447 : Blo 1271954 12236447 := bstep (se 1 (by rfl) ⟨9177335, by rfl⟩ : syracuseStep 12236447 = 18354671) B18354671
theorem B10870483 : Blo 1271954 10870483 := bstep (se 1 (by rfl) ⟨8152862, by rfl⟩ : syracuseStep 10870483 = 16305725) B16305725
theorem B7250543 : Blo 1271954 7250543 := bstep (se 1 (by rfl) ⟨5437907, by rfl⟩ : syracuseStep 7250543 = 10875815) B10875815
theorem B14493977 : Blo 1271954 14493977 := bstep (se 2 (by rfl) ⟨5435241, by rfl⟩ : syracuseStep 14493977 = 10870483) B10870483
theorem B1272991 : Blo 1271954 1272991 := bstep (se 1 (by rfl) ⟨954743, by rfl⟩ : syracuseStep 1272991 = 1909487) B1909487
theorem B4830461 : Blo 1271954 4830461 := bstep (se 3 (by rfl) ⟨905711, by rfl⟩ : syracuseStep 4830461 = 1811423) B1811423
theorem B185881877 : Blo 1271954 185881877 := bstep (se 6 (by rfl) ⟨4356606, by rfl⟩ : syracuseStep 185881877 = 8713213) B8713213
theorem B8157631 : Blo 1271954 8157631 := bstep (se 1 (by rfl) ⟨6118223, by rfl⟩ : syracuseStep 8157631 = 12236447) B12236447
theorem B1908479 : Blo 1271954 1908479 := bstep (se 1 (by rfl) ⟨1431359, by rfl⟩ : syracuseStep 1908479 = 2862719) B2862719
theorem B4833695 : Blo 1271954 4833695 := bstep (se 1 (by rfl) ⟨3625271, by rfl⟩ : syracuseStep 4833695 = 7250543) B7250543
theorem B3220307 : Blo 1271954 3220307 := bstep (se 1 (by rfl) ⟨2415230, by rfl⟩ : syracuseStep 3220307 = 4830461) B4830461
theorem B123921251 : Blo 1271954 123921251 := bstep (se 1 (by rfl) ⟨92940938, by rfl⟩ : syracuseStep 123921251 = 185881877) B185881877
theorem B1272319 : Blo 1271954 1272319 := bstep (se 1 (by rfl) ⟨954239, by rfl⟩ : syracuseStep 1272319 = 1908479) B1908479
theorem B9662651 : Blo 1271954 9662651 := bstep (se 1 (by rfl) ⟨7246988, by rfl⟩ : syracuseStep 9662651 = 14493977) B14493977
theorem B10876841 : Blo 1271954 10876841 := bstep (se 2 (by rfl) ⟨4078815, by rfl⟩ : syracuseStep 10876841 = 8157631) B8157631
theorem B2146871 : Blo 1271954 2146871 := bstep (se 1 (by rfl) ⟨1610153, by rfl⟩ : syracuseStep 2146871 = 3220307) B3220307
theorem B7251227 : Blo 1271954 7251227 := bstep (se 1 (by rfl) ⟨5438420, by rfl⟩ : syracuseStep 7251227 = 10876841) B10876841
theorem B6441767 : Blo 1271954 6441767 := bstep (se 1 (by rfl) ⟨4831325, by rfl⟩ : syracuseStep 6441767 = 9662651) B9662651
theorem B3222463 : Blo 1271954 3222463 := bstep (se 1 (by rfl) ⟨2416847, by rfl⟩ : syracuseStep 3222463 = 4833695) B4833695
theorem B82614167 : Blo 1271954 82614167 := bstep (se 1 (by rfl) ⟨61960625, by rfl⟩ : syracuseStep 82614167 = 123921251) B123921251
theorem B4834151 : Blo 1271954 4834151 := bstep (se 1 (by rfl) ⟨3625613, by rfl⟩ : syracuseStep 4834151 = 7251227) B7251227
theorem B55076111 : Blo 1271954 55076111 := bstep (se 1 (by rfl) ⟨41307083, by rfl⟩ : syracuseStep 55076111 = 82614167) B82614167
theorem B4294511 : Blo 1271954 4294511 := bstep (se 1 (by rfl) ⟨3220883, by rfl⟩ : syracuseStep 4294511 = 6441767) B6441767
theorem B4296617 : Blo 1271954 4296617 := bstep (se 2 (by rfl) ⟨1611231, by rfl⟩ : syracuseStep 4296617 = 3222463) B3222463
theorem B1431247 : Blo 1271954 1431247 := bstep (se 1 (by rfl) ⟨1073435, by rfl⟩ : syracuseStep 1431247 = 2146871) B2146871
theorem B36717407 : Blo 1271954 36717407 := bstep (se 1 (by rfl) ⟨27538055, by rfl⟩ : syracuseStep 36717407 = 55076111) B55076111
theorem B3222767 : Blo 1271954 3222767 := bstep (se 1 (by rfl) ⟨2417075, by rfl⟩ : syracuseStep 3222767 = 4834151) B4834151
theorem B2863007 : Blo 1271954 2863007 := bstep (se 1 (by rfl) ⟨2147255, by rfl⟩ : syracuseStep 2863007 = 4294511) B4294511
theorem B2864411 : Blo 1271954 2864411 := bstep (se 1 (by rfl) ⟨2148308, by rfl⟩ : syracuseStep 2864411 = 4296617) B4296617
theorem B1908329 : Blo 1271954 1908329 := bstep (se 2 (by rfl) ⟨715623, by rfl⟩ : syracuseStep 1908329 = 1431247) B1431247
theorem B24478271 : Blo 1271954 24478271 := bstep (se 1 (by rfl) ⟨18358703, by rfl⟩ : syracuseStep 24478271 = 36717407) B36717407
theorem B1909607 : Blo 1271954 1909607 := bstep (se 1 (by rfl) ⟨1432205, by rfl⟩ : syracuseStep 1909607 = 2864411) B2864411
theorem B2148511 : Blo 1271954 2148511 := bstep (se 1 (by rfl) ⟨1611383, by rfl⟩ : syracuseStep 2148511 = 3222767) B3222767
theorem B1272219 : Blo 1271954 1272219 := bstep (se 1 (by rfl) ⟨954164, by rfl⟩ : syracuseStep 1272219 = 1908329) B1908329
theorem B1908671 : Blo 1271954 1908671 := bstep (se 1 (by rfl) ⟨1431503, by rfl⟩ : syracuseStep 1908671 = 2863007) B2863007
theorem B16318847 : Blo 1271954 16318847 := bstep (se 1 (by rfl) ⟨12239135, by rfl⟩ : syracuseStep 16318847 = 24478271) B24478271
theorem B1272447 : Blo 1271954 1272447 := bstep (se 1 (by rfl) ⟨954335, by rfl⟩ : syracuseStep 1272447 = 1908671) B1908671
theorem B1273071 : Blo 1271954 1273071 := bstep (se 1 (by rfl) ⟨954803, by rfl⟩ : syracuseStep 1273071 = 1909607) B1909607
theorem B2864681 : Blo 1271954 2864681 := bstep (se 2 (by rfl) ⟨1074255, by rfl⟩ : syracuseStep 2864681 = 2148511) B2148511
theorem B10879231 : Blo 1271954 10879231 := bstep (se 1 (by rfl) ⟨8159423, by rfl⟩ : syracuseStep 10879231 = 16318847) B16318847
theorem B1909787 : Blo 1271954 1909787 := bstep (se 1 (by rfl) ⟨1432340, by rfl⟩ : syracuseStep 1909787 = 2864681) B2864681
theorem B1273191 : Blo 1271954 1273191 := bstep (se 1 (by rfl) ⟨954893, by rfl⟩ : syracuseStep 1273191 = 1909787) B1909787
theorem B14505641 : Blo 1271954 14505641 := bstep (se 2 (by rfl) ⟨5439615, by rfl⟩ : syracuseStep 14505641 = 10879231) B10879231
theorem B9670427 : Blo 1271954 9670427 := bstep (se 1 (by rfl) ⟨7252820, by rfl⟩ : syracuseStep 9670427 = 14505641) B14505641
theorem B6446951 : Blo 1271954 6446951 := bstep (se 1 (by rfl) ⟨4835213, by rfl⟩ : syracuseStep 6446951 = 9670427) B9670427
theorem B4297967 : Blo 1271954 4297967 := bstep (se 1 (by rfl) ⟨3223475, by rfl⟩ : syracuseStep 4297967 = 6446951) B6446951
theorem B2865311 : Blo 1271954 2865311 := bstep (se 1 (by rfl) ⟨2148983, by rfl⟩ : syracuseStep 2865311 = 4297967) B4297967
theorem B1910207 : Blo 1271954 1910207 := bstep (se 1 (by rfl) ⟨1432655, by rfl⟩ : syracuseStep 1910207 = 2865311) B2865311
theorem B1273471 : Blo 1271954 1273471 := bstep (se 1 (by rfl) ⟨955103, by rfl⟩ : syracuseStep 1273471 = 1910207) B1910207

theorem C0 (j : ℕ) (h1 : 317988 ≤ j) (h2 : j ≤ 318487) : Blo 1271954 (4 * j + 3) := by
  interval_cases j
  · exact B1271955
  · exact B1271959
  · exact B1271963
  · exact B1271967
  · exact B1271971
  · exact B1271975
  · exact B1271979
  · exact B1271983
  · exact B1271987
  · exact B1271991
  · exact B1271995
  · exact B1271999
  · exact B1272003
  · exact B1272007
  · exact B1272011
  · exact B1272015
  · exact B1272019
  · exact B1272023
  · exact B1272027
  · exact B1272031
  · exact B1272035
  · exact B1272039
  · exact B1272043
  · exact B1272047
  · exact B1272051
  · exact B1272055
  · exact B1272059
  · exact B1272063
  · exact B1272067
  · exact B1272071
  · exact B1272075
  · exact B1272079
  · exact B1272083
  · exact B1272087
  · exact B1272091
  · exact B1272095
  · exact B1272099
  · exact B1272103
  · exact B1272107
  · exact B1272111
  · exact B1272115
  · exact B1272119
  · exact B1272123
  · exact B1272127
  · exact B1272131
  · exact B1272135
  · exact B1272139
  · exact B1272143
  · exact B1272147
  · exact B1272151
  · exact B1272155
  · exact B1272159
  · exact B1272163
  · exact B1272167
  · exact B1272171
  · exact B1272175
  · exact B1272179
  · exact B1272183
  · exact B1272187
  · exact B1272191
  · exact B1272195
  · exact B1272199
  · exact B1272203
  · exact B1272207
  · exact B1272211
  · exact B1272215
  · exact B1272219
  · exact B1272223
  · exact B1272227
  · exact B1272231
  · exact B1272235
  · exact B1272239
  · exact B1272243
  · exact B1272247
  · exact B1272251
  · exact B1272255
  · exact B1272259
  · exact B1272263
  · exact B1272267
  · exact B1272271
  · exact B1272275
  · exact B1272279
  · exact B1272283
  · exact B1272287
  · exact B1272291
  · exact B1272295
  · exact B1272299
  · exact B1272303
  · exact B1272307
  · exact B1272311
  · exact B1272315
  · exact B1272319
  · exact B1272323
  · exact B1272327
  · exact B1272331
  · exact B1272335
  · exact B1272339
  · exact B1272343
  · exact B1272347
  · exact B1272351
  · exact B1272355
  · exact B1272359
  · exact B1272363
  · exact B1272367
  · exact B1272371
  · exact B1272375
  · exact B1272379
  · exact B1272383
  · exact B1272387
  · exact B1272391
  · exact B1272395
  · exact B1272399
  · exact B1272403
  · exact B1272407
  · exact B1272411
  · exact B1272415
  · exact B1272419
  · exact B1272423
  · exact B1272427
  · exact B1272431
  · exact B1272435
  · exact B1272439
  · exact B1272443
  · exact B1272447
  · exact B1272451
  · exact B1272455
  · exact B1272459
  · exact B1272463
  · exact B1272467
  · exact B1272471
  · exact B1272475
  · exact B1272479
  · exact B1272483
  · exact B1272487
  · exact B1272491
  · exact B1272495
  · exact B1272499
  · exact B1272503
  · exact B1272507
  · exact B1272511
  · exact B1272515
  · exact B1272519
  · exact B1272523
  · exact B1272527
  · exact B1272531
  · exact B1272535
  · exact B1272539
  · exact B1272543
  · exact B1272547
  · exact B1272551
  · exact B1272555
  · exact B1272559
  · exact B1272563
  · exact B1272567
  · exact B1272571
  · exact B1272575
  · exact B1272579
  · exact B1272583
  · exact B1272587
  · exact B1272591
  · exact B1272595
  · exact B1272599
  · exact B1272603
  · exact B1272607
  · exact B1272611
  · exact B1272615
  · exact B1272619
  · exact B1272623
  · exact B1272627
  · exact B1272631
  · exact B1272635
  · exact B1272639
  · exact B1272643
  · exact B1272647
  · exact B1272651
  · exact B1272655
  · exact B1272659
  · exact B1272663
  · exact B1272667
  · exact B1272671
  · exact B1272675
  · exact B1272679
  · exact B1272683
  · exact B1272687
  · exact B1272691
  · exact B1272695
  · exact B1272699
  · exact B1272703
  · exact B1272707
  · exact B1272711
  · exact B1272715
  · exact B1272719
  · exact B1272723
  · exact B1272727
  · exact B1272731
  · exact B1272735
  · exact B1272739
  · exact B1272743
  · exact B1272747
  · exact B1272751
  · exact B1272755
  · exact B1272759
  · exact B1272763
  · exact B1272767
  · exact B1272771
  · exact B1272775
  · exact B1272779
  · exact B1272783
  · exact B1272787
  · exact B1272791
  · exact B1272795
  · exact B1272799
  · exact B1272803
  · exact B1272807
  · exact B1272811
  · exact B1272815
  · exact B1272819
  · exact B1272823
  · exact B1272827
  · exact B1272831
  · exact B1272835
  · exact B1272839
  · exact B1272843
  · exact B1272847
  · exact B1272851
  · exact B1272855
  · exact B1272859
  · exact B1272863
  · exact B1272867
  · exact B1272871
  · exact B1272875
  · exact B1272879
  · exact B1272883
  · exact B1272887
  · exact B1272891
  · exact B1272895
  · exact B1272899
  · exact B1272903
  · exact B1272907
  · exact B1272911
  · exact B1272915
  · exact B1272919
  · exact B1272923
  · exact B1272927
  · exact B1272931
  · exact B1272935
  · exact B1272939
  · exact B1272943
  · exact B1272947
  · exact B1272951
  · exact B1272955
  · exact B1272959
  · exact B1272963
  · exact B1272967
  · exact B1272971
  · exact B1272975
  · exact B1272979
  · exact B1272983
  · exact B1272987
  · exact B1272991
  · exact B1272995
  · exact B1272999
  · exact B1273003
  · exact B1273007
  · exact B1273011
  · exact B1273015
  · exact B1273019
  · exact B1273023
  · exact B1273027
  · exact B1273031
  · exact B1273035
  · exact B1273039
  · exact B1273043
  · exact B1273047
  · exact B1273051
  · exact B1273055
  · exact B1273059
  · exact B1273063
  · exact B1273067
  · exact B1273071
  · exact B1273075
  · exact B1273079
  · exact B1273083
  · exact B1273087
  · exact B1273091
  · exact B1273095
  · exact B1273099
  · exact B1273103
  · exact B1273107
  · exact B1273111
  · exact B1273115
  · exact B1273119
  · exact B1273123
  · exact B1273127
  · exact B1273131
  · exact B1273135
  · exact B1273139
  · exact B1273143
  · exact B1273147
  · exact B1273151
  · exact B1273155
  · exact B1273159
  · exact B1273163
  · exact B1273167
  · exact B1273171
  · exact B1273175
  · exact B1273179
  · exact B1273183
  · exact B1273187
  · exact B1273191
  · exact B1273195
  · exact B1273199
  · exact B1273203
  · exact B1273207
  · exact B1273211
  · exact B1273215
  · exact B1273219
  · exact B1273223
  · exact B1273227
  · exact B1273231
  · exact B1273235
  · exact B1273239
  · exact B1273243
  · exact B1273247
  · exact B1273251
  · exact B1273255
  · exact B1273259
  · exact B1273263
  · exact B1273267
  · exact B1273271
  · exact B1273275
  · exact B1273279
  · exact B1273283
  · exact B1273287
  · exact B1273291
  · exact B1273295
  · exact B1273299
  · exact B1273303
  · exact B1273307
  · exact B1273311
  · exact B1273315
  · exact B1273319
  · exact B1273323
  · exact B1273327
  · exact B1273331
  · exact B1273335
  · exact B1273339
  · exact B1273343
  · exact B1273347
  · exact B1273351
  · exact B1273355
  · exact B1273359
  · exact B1273363
  · exact B1273367
  · exact B1273371
  · exact B1273375
  · exact B1273379
  · exact B1273383
  · exact B1273387
  · exact B1273391
  · exact B1273395
  · exact B1273399
  · exact B1273403
  · exact B1273407
  · exact B1273411
  · exact B1273415
  · exact B1273419
  · exact B1273423
  · exact B1273427
  · exact B1273431
  · exact B1273435
  · exact B1273439
  · exact B1273443
  · exact B1273447
  · exact B1273451
  · exact B1273455
  · exact B1273459
  · exact B1273463
  · exact B1273467
  · exact B1273471
  · exact B1273475
  · exact B1273479
  · exact B1273483
  · exact B1273487
  · exact B1273491
  · exact B1273495
  · exact B1273499
  · exact B1273503
  · exact B1273507
  · exact B1273511
  · exact B1273515
  · exact B1273519
  · exact B1273523
  · exact B1273527
  · exact B1273531
  · exact B1273535
  · exact B1273539
  · exact B1273543
  · exact B1273547
  · exact B1273551
  · exact B1273555
  · exact B1273559
  · exact B1273563
  · exact B1273567
  · exact B1273571
  · exact B1273575
  · exact B1273579
  · exact B1273583
  · exact B1273587
  · exact B1273591
  · exact B1273595
  · exact B1273599
  · exact B1273603
  · exact B1273607
  · exact B1273611
  · exact B1273615
  · exact B1273619
  · exact B1273623
  · exact B1273627
  · exact B1273631
  · exact B1273635
  · exact B1273639
  · exact B1273643
  · exact B1273647
  · exact B1273651
  · exact B1273655
  · exact B1273659
  · exact B1273663
  · exact B1273667
  · exact B1273671
  · exact B1273675
  · exact B1273679
  · exact B1273683
  · exact B1273687
  · exact B1273691
  · exact B1273695
  · exact B1273699
  · exact B1273703
  · exact B1273707
  · exact B1273711
  · exact B1273715
  · exact B1273719
  · exact B1273723
  · exact B1273727
  · exact B1273731
  · exact B1273735
  · exact B1273739
  · exact B1273743
  · exact B1273747
  · exact B1273751
  · exact B1273755
  · exact B1273759
  · exact B1273763
  · exact B1273767
  · exact B1273771
  · exact B1273775
  · exact B1273779
  · exact B1273783
  · exact B1273787
  · exact B1273791
  · exact B1273795
  · exact B1273799
  · exact B1273803
  · exact B1273807
  · exact B1273811
  · exact B1273815
  · exact B1273819
  · exact B1273823
  · exact B1273827
  · exact B1273831
  · exact B1273835
  · exact B1273839
  · exact B1273843
  · exact B1273847
  · exact B1273851
  · exact B1273855
  · exact B1273859
  · exact B1273863
  · exact B1273867
  · exact B1273871
  · exact B1273875
  · exact B1273879
  · exact B1273883
  · exact B1273887
  · exact B1273891
  · exact B1273895
  · exact B1273899
  · exact B1273903
  · exact B1273907
  · exact B1273911
  · exact B1273915
  · exact B1273919
  · exact B1273923
  · exact B1273927
  · exact B1273931
  · exact B1273935
  · exact B1273939
  · exact B1273943
  · exact B1273947
  · exact B1273951

theorem solution (m : ℕ) (hlo : 1271954 ≤ m) (hhi : m ≤ 1273954) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 317988 ≤ j := by omega
    have hj2 : j ≤ 318487 := by omega
    have hb : Blo 1271954 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
