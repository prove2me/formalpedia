-- Prove2me | solution 1 for syracuse_descends_range_1445542_1447542
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:43:06.27925+00:00
-- url     : https://prove2.me/submissions/c2451310-205c-4a75-a8de-d60fd9ee982e

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


theorem B2170901 : Blo 1445542 2170901 := bbase (se 6 (by rfl) ⟨50880, by rfl⟩ : syracuseStep 2170901 = 101761) (by norm_num)
theorem B2441245 : Blo 1445542 2441245 := bbase (se 3 (by rfl) ⟨457733, by rfl⟩ : syracuseStep 2441245 = 915467) (by norm_num)
theorem B5865509 : Blo 1445542 5865509 := bbase (se 4 (by rfl) ⟨549891, by rfl⟩ : syracuseStep 5865509 = 1099783) (by norm_num)
theorem B2170925 : Blo 1445542 2170925 := bbase (se 3 (by rfl) ⟨407048, by rfl⟩ : syracuseStep 2170925 = 814097) (by norm_num)
theorem B2744381 : Blo 1445542 2744381 := bbase (se 3 (by rfl) ⟨514571, by rfl⟩ : syracuseStep 2744381 = 1029143) (by norm_num)
theorem B2170949 : Blo 1445542 2170949 := bbase (se 4 (by rfl) ⟨203526, by rfl⟩ : syracuseStep 2170949 = 407053) (by norm_num)
theorem B4882517 : Blo 1445542 4882517 := bbase (se 8 (by rfl) ⟨28608, by rfl⟩ : syracuseStep 4882517 = 57217) (by norm_num)
theorem B2170973 : Blo 1445542 2170973 := bbase (se 3 (by rfl) ⟨407057, by rfl⟩ : syracuseStep 2170973 = 814115) (by norm_num)
theorem B2441333 : Blo 1445542 2441333 := bbase (se 5 (by rfl) ⟨114437, by rfl⟩ : syracuseStep 2441333 = 228875) (by norm_num)
theorem B2170997 : Blo 1445542 2170997 := bbase (se 5 (by rfl) ⟨101765, by rfl⟩ : syracuseStep 2170997 = 203531) (by norm_num)
theorem B3661949 : Blo 1445542 3661949 := bbase (se 3 (by rfl) ⟨686615, by rfl⟩ : syracuseStep 3661949 = 1373231) (by norm_num)
theorem B2171021 : Blo 1445542 2171021 := bbase (se 3 (by rfl) ⟨407066, by rfl⟩ : syracuseStep 2171021 = 814133) (by norm_num)
theorem B2171045 : Blo 1445542 2171045 := bbase (se 4 (by rfl) ⟨203535, by rfl⟩ : syracuseStep 2171045 = 407071) (by norm_num)
theorem B2171069 : Blo 1445542 2171069 := bbase (se 3 (by rfl) ⟨407075, by rfl⟩ : syracuseStep 2171069 = 814151) (by norm_num)
theorem B2744533 : Blo 1445542 2744533 := bbase (se 7 (by rfl) ⟨32162, by rfl⟩ : syracuseStep 2744533 = 64325) (by norm_num)
theorem B4636885 : Blo 1445542 4636885 := bbase (se 7 (by rfl) ⟨54338, by rfl⟩ : syracuseStep 4636885 = 108677) (by norm_num)
theorem B2171093 : Blo 1445542 2171093 := bbase (se 7 (by rfl) ⟨25442, by rfl⟩ : syracuseStep 2171093 = 50885) (by norm_num)
theorem B2171117 : Blo 1445542 2171117 := bbase (se 3 (by rfl) ⟨407084, by rfl⟩ : syracuseStep 2171117 = 814169) (by norm_num)
theorem B2441461 : Blo 1445542 2441461 := bbase (se 5 (by rfl) ⟨114443, by rfl⟩ : syracuseStep 2441461 = 228887) (by norm_num)
theorem B6955253 : Blo 1445542 6955253 := bbase (se 5 (by rfl) ⟨326027, by rfl⟩ : syracuseStep 6955253 = 652055) (by norm_num)
theorem B2171141 : Blo 1445542 2171141 := bbase (se 4 (by rfl) ⟨203544, by rfl⟩ : syracuseStep 2171141 = 407089) (by norm_num)
theorem B3252509 : Blo 1445542 3252509 := bbase (se 3 (by rfl) ⟨609845, by rfl⟩ : syracuseStep 3252509 = 1219691) (by norm_num)
theorem B2171165 : Blo 1445542 2171165 := bbase (se 3 (by rfl) ⟨407093, by rfl⟩ : syracuseStep 2171165 = 814187) (by norm_num)
theorem B1696037 : Blo 1445542 1696037 := bbase (se 4 (by rfl) ⟨159003, by rfl⟩ : syracuseStep 1696037 = 318007) (by norm_num)
theorem B2171189 : Blo 1445542 2171189 := bbase (se 5 (by rfl) ⟨101774, by rfl⟩ : syracuseStep 2171189 = 203549) (by norm_num)
theorem B4120901 : Blo 1445542 4120901 := bbase (se 4 (by rfl) ⟨386334, by rfl⟩ : syracuseStep 4120901 = 772669) (by norm_num)
theorem B2441549 : Blo 1445542 2441549 := bbase (se 3 (by rfl) ⟨457790, by rfl⟩ : syracuseStep 2441549 = 915581) (by norm_num)
theorem B2171213 : Blo 1445542 2171213 := bbase (se 3 (by rfl) ⟨407102, by rfl⟩ : syracuseStep 2171213 = 814205) (by norm_num)
theorem B3252581 : Blo 1445542 3252581 := bbase (se 4 (by rfl) ⟨304929, by rfl⟩ : syracuseStep 3252581 = 609859) (by norm_num)
theorem B2171237 : Blo 1445542 2171237 := bbase (se 4 (by rfl) ⟨203553, by rfl⟩ : syracuseStep 2171237 = 407107) (by norm_num)
theorem B2171261 : Blo 1445542 2171261 := bbase (se 3 (by rfl) ⟨407111, by rfl⟩ : syracuseStep 2171261 = 814223) (by norm_num)
theorem B2171285 : Blo 1445542 2171285 := bbase (se 6 (by rfl) ⟨50889, by rfl⟩ : syracuseStep 2171285 = 101779) (by norm_num)
theorem B3252653 : Blo 1445542 3252653 := bbase (se 3 (by rfl) ⟨609872, by rfl⟩ : syracuseStep 3252653 = 1219745) (by norm_num)
theorem B2171309 : Blo 1445542 2171309 := bbase (se 3 (by rfl) ⟨407120, by rfl⟩ : syracuseStep 2171309 = 814241) (by norm_num)
theorem B2441677 : Blo 1445542 2441677 := bbase (se 3 (by rfl) ⟨457814, by rfl⟩ : syracuseStep 2441677 = 915629) (by norm_num)
theorem B3662293 : Blo 1445542 3662293 := bbase (se 7 (by rfl) ⟨42917, by rfl⟩ : syracuseStep 3662293 = 85835) (by norm_num)
theorem B3252725 : Blo 1445542 3252725 := bbase (se 5 (by rfl) ⟨152471, by rfl⟩ : syracuseStep 3252725 = 304943) (by norm_num)
theorem B2744837 : Blo 1445542 2744837 := bbase (se 4 (by rfl) ⟨257328, by rfl⟩ : syracuseStep 2744837 = 514657) (by norm_num)
theorem B4882949 : Blo 1445542 4882949 := bbase (se 4 (by rfl) ⟨457776, by rfl⟩ : syracuseStep 4882949 = 915553) (by norm_num)
theorem B2605589 : Blo 1445542 2605589 := bbase (se 6 (by rfl) ⟨61068, by rfl⟩ : syracuseStep 2605589 = 122137) (by norm_num)
theorem B7324181 : Blo 1445542 7324181 := bbase (se 6 (by rfl) ⟨171660, by rfl⟩ : syracuseStep 7324181 = 343321) (by norm_num)
theorem B3088925 : Blo 1445542 3088925 := bbase (se 3 (by rfl) ⟨579173, by rfl⟩ : syracuseStep 3088925 = 1158347) (by norm_num)
theorem B2441765 : Blo 1445542 2441765 := bbase (se 4 (by rfl) ⟨228915, by rfl⟩ : syracuseStep 2441765 = 457831) (by norm_num)
theorem B3252797 : Blo 1445542 3252797 := bbase (se 3 (by rfl) ⟨609899, by rfl⟩ : syracuseStep 3252797 = 1219799) (by norm_num)
theorem B3662405 : Blo 1445542 3662405 := bbase (se 4 (by rfl) ⟨343350, by rfl⟩ : syracuseStep 3662405 = 686701) (by norm_num)
theorem B6431333 : Blo 1445542 6431333 := bbase (se 4 (by rfl) ⟨602937, by rfl⟩ : syracuseStep 6431333 = 1205875) (by norm_num)
theorem B3252869 : Blo 1445542 3252869 := bbase (se 4 (by rfl) ⟨304956, by rfl⟩ : syracuseStep 3252869 = 609913) (by norm_num)
theorem B2933405 : Blo 1445542 2933405 := bbase (se 3 (by rfl) ⟨550013, by rfl⟩ : syracuseStep 2933405 = 1100027) (by norm_num)
theorem B2441893 : Blo 1445542 2441893 := bbase (se 4 (by rfl) ⟨228927, by rfl⟩ : syracuseStep 2441893 = 457855) (by norm_num)
theorem B3252941 : Blo 1445542 3252941 := bbase (se 3 (by rfl) ⟨609926, by rfl⟩ : syracuseStep 3252941 = 1219853) (by norm_num)
theorem B2441981 : Blo 1445542 2441981 := bbase (se 3 (by rfl) ⟨457871, by rfl⟩ : syracuseStep 2441981 = 915743) (by norm_num)
theorem B3711749 : Blo 1445542 3711749 := bbase (se 4 (by rfl) ⟨347976, by rfl⟩ : syracuseStep 3711749 = 695953) (by norm_num)
theorem B3662597 : Blo 1445542 3662597 := bbase (se 4 (by rfl) ⟨343368, by rfl⟩ : syracuseStep 3662597 = 686737) (by norm_num)
theorem B3253013 : Blo 1445542 3253013 := bbase (se 6 (by rfl) ⟨76242, by rfl⟩ : syracuseStep 3253013 = 152485) (by norm_num)
theorem B5489477 : Blo 1445542 5489477 := bbase (se 4 (by rfl) ⟨514638, by rfl⟩ : syracuseStep 5489477 = 1029277) (by norm_num)
theorem B3253085 : Blo 1445542 3253085 := bbase (se 3 (by rfl) ⟨609953, by rfl⟩ : syracuseStep 3253085 = 1219907) (by norm_num)
theorem B2442109 : Blo 1445542 2442109 := bbase (se 3 (by rfl) ⟨457895, by rfl⟩ : syracuseStep 2442109 = 915791) (by norm_num)
theorem B3253157 : Blo 1445542 3253157 := bbase (se 4 (by rfl) ⟨304983, by rfl⟩ : syracuseStep 3253157 = 609967) (by norm_num)
theorem B4883381 : Blo 1445542 4883381 := bbase (se 5 (by rfl) ⟨228908, by rfl⟩ : syracuseStep 4883381 = 457817) (by norm_num)
theorem B2442197 : Blo 1445542 2442197 := bbase (se 7 (by rfl) ⟨28619, by rfl⟩ : syracuseStep 2442197 = 57239) (by norm_num)
theorem B3253229 : Blo 1445542 3253229 := bbase (se 3 (by rfl) ⟨609980, by rfl⟩ : syracuseStep 3253229 = 1219961) (by norm_num)
theorem B3253301 : Blo 1445542 3253301 := bbase (se 5 (by rfl) ⟨152498, by rfl⟩ : syracuseStep 3253301 = 304997) (by norm_num)
theorem B2442325 : Blo 1445542 2442325 := bbase (se 8 (by rfl) ⟨14310, by rfl⟩ : syracuseStep 2442325 = 28621) (by norm_num)
theorem B3662941 : Blo 1445542 3662941 := bbase (se 3 (by rfl) ⟨686801, by rfl⟩ : syracuseStep 3662941 = 1373603) (by norm_num)
theorem B5489765 : Blo 1445542 5489765 := bbase (se 4 (by rfl) ⟨514665, by rfl⟩ : syracuseStep 5489765 = 1029331) (by norm_num)
theorem B13902965 : Blo 1445542 13902965 := bbase (se 5 (by rfl) ⟨651701, by rfl⟩ : syracuseStep 13902965 = 1303403) (by norm_num)
theorem B3253373 : Blo 1445542 3253373 := bbase (se 3 (by rfl) ⟨610007, by rfl⟩ : syracuseStep 3253373 = 1220015) (by norm_num)
theorem B3474589 : Blo 1445542 3474589 := bbase (se 3 (by rfl) ⟨651485, by rfl⟩ : syracuseStep 3474589 = 1302971) (by norm_num)
theorem B2442413 : Blo 1445542 2442413 := bbase (se 3 (by rfl) ⟨457952, by rfl⟩ : syracuseStep 2442413 = 915905) (by norm_num)
theorem B3253445 : Blo 1445542 3253445 := bbase (se 4 (by rfl) ⟨305010, by rfl⟩ : syracuseStep 3253445 = 610021) (by norm_num)
theorem B3663053 : Blo 1445542 3663053 := bbase (se 3 (by rfl) ⟨686822, by rfl⟩ : syracuseStep 3663053 = 1373645) (by norm_num)
theorem B1762517 : Blo 1445542 1762517 := bbase (se 7 (by rfl) ⟨20654, by rfl⟩ : syracuseStep 1762517 = 41309) (by norm_num)
theorem B2745589 : Blo 1445542 2745589 := bbase (se 5 (by rfl) ⟨128699, by rfl⟩ : syracuseStep 2745589 = 257399) (by norm_num)
theorem B3253517 : Blo 1445542 3253517 := bbase (se 3 (by rfl) ⟨610034, by rfl⟩ : syracuseStep 3253517 = 1220069) (by norm_num)
theorem B3089677 : Blo 1445542 3089677 := bbase (se 3 (by rfl) ⟨579314, by rfl⟩ : syracuseStep 3089677 = 1158629) (by norm_num)
theorem B3474733 : Blo 1445542 3474733 := bbase (se 3 (by rfl) ⟨651512, by rfl⟩ : syracuseStep 3474733 = 1303025) (by norm_num)
theorem B2442541 : Blo 1445542 2442541 := bbase (se 3 (by rfl) ⟨457976, by rfl⟩ : syracuseStep 2442541 = 915953) (by norm_num)
theorem B2934085 : Blo 1445542 2934085 := bbase (se 4 (by rfl) ⟨275070, by rfl⟩ : syracuseStep 2934085 = 550141) (by norm_num)
theorem B3253589 : Blo 1445542 3253589 := bbase (se 12 (by rfl) ⟨1191, by rfl⟩ : syracuseStep 3253589 = 2383) (by norm_num)
theorem B4883813 : Blo 1445542 4883813 := bbase (se 4 (by rfl) ⟨457857, by rfl⟩ : syracuseStep 4883813 = 915715) (by norm_num)
theorem B2745733 : Blo 1445542 2745733 := bbase (se 4 (by rfl) ⟨257412, by rfl⟩ : syracuseStep 2745733 = 514825) (by norm_num)
theorem B2934149 : Blo 1445542 2934149 := bbase (se 4 (by rfl) ⟨275076, by rfl⟩ : syracuseStep 2934149 = 550153) (by norm_num)
theorem B2442629 : Blo 1445542 2442629 := bbase (se 4 (by rfl) ⟨228996, by rfl⟩ : syracuseStep 2442629 = 457993) (by norm_num)
theorem B3663245 : Blo 1445542 3663245 := bbase (se 3 (by rfl) ⟨686858, by rfl⟩ : syracuseStep 3663245 = 1373717) (by norm_num)
theorem B3253661 : Blo 1445542 3253661 := bbase (se 3 (by rfl) ⟨610061, by rfl⟩ : syracuseStep 3253661 = 1220123) (by norm_num)
theorem B3089821 : Blo 1445542 3089821 := bbase (se 3 (by rfl) ⟨579341, by rfl⟩ : syracuseStep 3089821 = 1158683) (by norm_num)
theorem B3253733 : Blo 1445542 3253733 := bbase (se 4 (by rfl) ⟨305037, by rfl⟩ : syracuseStep 3253733 = 610075) (by norm_num)
theorem B4122085 : Blo 1445542 4122085 := bbase (se 4 (by rfl) ⟨386445, by rfl⟩ : syracuseStep 4122085 = 772891) (by norm_num)
theorem B1738217 : Blo 1445542 1738217 := bbase (se 2 (by rfl) ⟨651831, by rfl⟩ : syracuseStep 1738217 = 1303663) (by norm_num)
theorem B2745893 : Blo 1445542 2745893 := bbase (se 4 (by rfl) ⟨257427, by rfl⟩ : syracuseStep 2745893 = 514855) (by norm_num)
theorem B3712549 : Blo 1445542 3712549 := bbase (se 4 (by rfl) ⟨348051, by rfl⟩ : syracuseStep 3712549 = 696103) (by norm_num)
theorem B3253805 : Blo 1445542 3253805 := bbase (se 3 (by rfl) ⟨610088, by rfl⟩ : syracuseStep 3253805 = 1220177) (by norm_num)
theorem B3253877 : Blo 1445542 3253877 := bbase (se 5 (by rfl) ⟨152525, by rfl⟩ : syracuseStep 3253877 = 305051) (by norm_num)
theorem B12355253 : Blo 1445542 12355253 := bbase (se 5 (by rfl) ⟨579152, by rfl⟩ : syracuseStep 12355253 = 1158305) (by norm_num)
theorem B2746037 : Blo 1445542 2746037 := bbase (se 5 (by rfl) ⟨128720, by rfl⟩ : syracuseStep 2746037 = 257441) (by norm_num)
theorem B3253949 : Blo 1445542 3253949 := bbase (se 3 (by rfl) ⟨610115, by rfl⟩ : syracuseStep 3253949 = 1220231) (by norm_num)
theorem B6022885 : Blo 1445542 6022885 := bbase (se 4 (by rfl) ⟨564645, by rfl⟩ : syracuseStep 6022885 = 1129291) (by norm_num)
theorem B3663589 : Blo 1445542 3663589 := bbase (se 4 (by rfl) ⟨343461, by rfl⟩ : syracuseStep 3663589 = 686923) (by norm_num)
theorem B3254021 : Blo 1445542 3254021 := bbase (se 4 (by rfl) ⟨305064, by rfl⟩ : syracuseStep 3254021 = 610129) (by norm_num)
theorem B3131149 : Blo 1445542 3131149 := bbase (se 3 (by rfl) ⟨587090, by rfl⟩ : syracuseStep 3131149 = 1174181) (by norm_num)
theorem B3090197 : Blo 1445542 3090197 := bbase (se 6 (by rfl) ⟨72426, by rfl⟩ : syracuseStep 3090197 = 144853) (by norm_num)
theorem B4884245 : Blo 1445542 4884245 := bbase (se 6 (by rfl) ⟨114474, by rfl⟩ : syracuseStep 4884245 = 228949) (by norm_num)
theorem B1738525 : Blo 1445542 1738525 := bbase (se 3 (by rfl) ⟨325973, by rfl⟩ : syracuseStep 1738525 = 651947) (by norm_num)
theorem B7325477 : Blo 1445542 7325477 := bbase (se 4 (by rfl) ⟨686763, by rfl⟩ : syracuseStep 7325477 = 1373527) (by norm_num)
theorem B1648453 : Blo 1445542 1648453 := bbase (se 4 (by rfl) ⟨154542, by rfl⟩ : syracuseStep 1648453 = 309085) (by norm_num)
theorem B3254093 : Blo 1445542 3254093 := bbase (se 3 (by rfl) ⟨610142, by rfl⟩ : syracuseStep 3254093 = 1220285) (by norm_num)
theorem B6596437 : Blo 1445542 6596437 := bbase (se 9 (by rfl) ⟨19325, by rfl⟩ : syracuseStep 6596437 = 38651) (by norm_num)
theorem B3663701 : Blo 1445542 3663701 := bbase (se 9 (by rfl) ⟨10733, by rfl⟩ : syracuseStep 3663701 = 21467) (by norm_num)
theorem B1738621 : Blo 1445542 1738621 := bbase (se 3 (by rfl) ⟨325991, by rfl⟩ : syracuseStep 1738621 = 651983) (by norm_num)
theorem B3254165 : Blo 1445542 3254165 := bbase (se 6 (by rfl) ⟨76269, by rfl⟩ : syracuseStep 3254165 = 152539) (by norm_num)
theorem B3475349 : Blo 1445542 3475349 := bbase (se 6 (by rfl) ⟨81453, by rfl⟩ : syracuseStep 3475349 = 162907) (by norm_num)
theorem B2746325 : Blo 1445542 2746325 := bbase (se 7 (by rfl) ⟨32183, by rfl⟩ : syracuseStep 2746325 = 64367) (by norm_num)
theorem B3254237 : Blo 1445542 3254237 := bbase (se 3 (by rfl) ⟨610169, by rfl⟩ : syracuseStep 3254237 = 1220339) (by norm_num)
theorem B5564389 : Blo 1445542 5564389 := bbase (se 4 (by rfl) ⟨521661, by rfl⟩ : syracuseStep 5564389 = 1043323) (by norm_num)
theorem B10430453 : Blo 1445542 10430453 := bbase (se 5 (by rfl) ⟨488927, by rfl⟩ : syracuseStep 10430453 = 977855) (by norm_num)
theorem B2607109 : Blo 1445542 2607109 := bbase (se 4 (by rfl) ⟨244416, by rfl⟩ : syracuseStep 2607109 = 488833) (by norm_num)
theorem B3663893 : Blo 1445542 3663893 := bbase (se 6 (by rfl) ⟨85872, by rfl⟩ : syracuseStep 3663893 = 171745) (by norm_num)
theorem B3254309 : Blo 1445542 3254309 := bbase (se 4 (by rfl) ⟨305091, by rfl⟩ : syracuseStep 3254309 = 610183) (by norm_num)
theorem B3254381 : Blo 1445542 3254381 := bbase (se 3 (by rfl) ⟨610196, by rfl⟩ : syracuseStep 3254381 = 1220393) (by norm_num)
theorem B2746477 : Blo 1445542 2746477 := bbase (se 3 (by rfl) ⟨514964, by rfl⟩ : syracuseStep 2746477 = 1029929) (by norm_num)
theorem B11724917 : Blo 1445542 11724917 := bbase (se 5 (by rfl) ⟨549605, by rfl⟩ : syracuseStep 11724917 = 1099211) (by norm_num)
theorem B3090565 : Blo 1445542 3090565 := bbase (se 4 (by rfl) ⟨289740, by rfl⟩ : syracuseStep 3090565 = 579481) (by norm_num)
theorem B1738909 : Blo 1445542 1738909 := bbase (se 3 (by rfl) ⟨326045, by rfl⟩ : syracuseStep 1738909 = 652091) (by norm_num)
theorem B3254453 : Blo 1445542 3254453 := bbase (se 5 (by rfl) ⟨152552, by rfl⟩ : syracuseStep 3254453 = 305105) (by norm_num)
theorem B4884677 : Blo 1445542 4884677 := bbase (se 4 (by rfl) ⟨457938, by rfl⟩ : syracuseStep 4884677 = 915877) (by norm_num)
theorem B3475685 : Blo 1445542 3475685 := bbase (se 4 (by rfl) ⟨325845, by rfl⟩ : syracuseStep 3475685 = 651691) (by norm_num)
theorem B1648873 : Blo 1445542 1648873 := bbase (se 2 (by rfl) ⟨618327, by rfl⟩ : syracuseStep 1648873 = 1236655) (by norm_num)
theorem B5867765 : Blo 1445542 5867765 := bbase (se 5 (by rfl) ⟨275051, by rfl⟩ : syracuseStep 5867765 = 550103) (by norm_num)
theorem B3254525 : Blo 1445542 3254525 := bbase (se 3 (by rfl) ⟨610223, by rfl⟩ : syracuseStep 3254525 = 1220447) (by norm_num)
theorem B5490949 : Blo 1445542 5490949 := bbase (se 4 (by rfl) ⟨514776, by rfl⟩ : syracuseStep 5490949 = 1029553) (by norm_num)
theorem B1648945 : Blo 1445542 1648945 := bbase (se 2 (by rfl) ⟨618354, by rfl⟩ : syracuseStep 1648945 = 1236709) (by norm_num)
theorem B3909941 : Blo 1445542 3909941 := bbase (se 5 (by rfl) ⟨183278, by rfl⟩ : syracuseStep 3909941 = 366557) (by norm_num)
theorem B3254597 : Blo 1445542 3254597 := bbase (se 4 (by rfl) ⟨305118, by rfl⟩ : syracuseStep 3254597 = 610237) (by norm_num)
theorem B3475781 : Blo 1445542 3475781 := bbase (se 4 (by rfl) ⟨325854, by rfl⟩ : syracuseStep 3475781 = 651709) (by norm_num)
theorem B1649009 : Blo 1445542 1649009 := bbase (se 2 (by rfl) ⟨618378, by rfl⟩ : syracuseStep 1649009 = 1236757) (by norm_num)
theorem B6949253 : Blo 1445542 6949253 := bbase (se 4 (by rfl) ⟨651492, by rfl⟩ : syracuseStep 6949253 = 1302985) (by norm_num)
theorem B2197901 : Blo 1445542 2197901 := bbase (se 3 (by rfl) ⟨412106, by rfl⟩ : syracuseStep 2197901 = 824213) (by norm_num)
theorem B3254669 : Blo 1445542 3254669 := bbase (se 3 (by rfl) ⟨610250, by rfl⟩ : syracuseStep 3254669 = 1220501) (by norm_num)
theorem B2746781 : Blo 1445542 2746781 := bbase (se 3 (by rfl) ⟨515021, by rfl⟩ : syracuseStep 2746781 = 1030043) (by norm_num)
theorem B3254741 : Blo 1445542 3254741 := bbase (se 7 (by rfl) ⟨38141, by rfl⟩ : syracuseStep 3254741 = 76283) (by norm_num)
theorem B37095893 : Blo 1445542 37095893 := bbase (se 7 (by rfl) ⟨434717, by rfl⟩ : syracuseStep 37095893 = 869435) (by norm_num)
theorem B3475973 : Blo 1445542 3475973 := bbase (se 4 (by rfl) ⟨325872, by rfl⟩ : syracuseStep 3475973 = 651745) (by norm_num)
theorem B1649165 : Blo 1445542 1649165 := bbase (se 3 (by rfl) ⟨309218, by rfl⟩ : syracuseStep 1649165 = 618437) (by norm_num)
theorem B3254813 : Blo 1445542 3254813 := bbase (se 3 (by rfl) ⟨610277, by rfl⟩ : syracuseStep 3254813 = 1220555) (by norm_num)
theorem B5491253 : Blo 1445542 5491253 := bbase (se 5 (by rfl) ⟨257402, by rfl⟩ : syracuseStep 5491253 = 514805) (by norm_num)
theorem B3254885 : Blo 1445542 3254885 := bbase (se 4 (by rfl) ⟨305145, by rfl⟩ : syracuseStep 3254885 = 610291) (by norm_num)
theorem B4885109 : Blo 1445542 4885109 := bbase (se 5 (by rfl) ⟨228989, by rfl⟩ : syracuseStep 4885109 = 457979) (by norm_num)
theorem B3254957 : Blo 1445542 3254957 := bbase (se 3 (by rfl) ⟨610304, by rfl⟩ : syracuseStep 3254957 = 1220609) (by norm_num)
theorem B1829557 : Blo 1445542 1829557 := bbase (se 5 (by rfl) ⟨85760, by rfl⟩ : syracuseStep 1829557 = 171521) (by norm_num)
theorem B3255029 : Blo 1445542 3255029 := bbase (se 5 (by rfl) ⟨152579, by rfl⟩ : syracuseStep 3255029 = 305159) (by norm_num)
theorem B3255101 : Blo 1445542 3255101 := bbase (se 3 (by rfl) ⟨610331, by rfl⟩ : syracuseStep 3255101 = 1220663) (by norm_num)
theorem B1829729 : Blo 1445542 1829729 := bbase (se 2 (by rfl) ⟨686148, by rfl⟩ : syracuseStep 1829729 = 1372297) (by norm_num)
theorem B3255173 : Blo 1445542 3255173 := bbase (se 4 (by rfl) ⟨305172, by rfl⟩ : syracuseStep 3255173 = 610345) (by norm_num)
theorem B2509717 : Blo 1445542 2509717 := bbase (se 6 (by rfl) ⟨58821, by rfl⟩ : syracuseStep 2509717 = 117643) (by norm_num)
theorem B1829785 : Blo 1445542 1829785 := bbase (se 2 (by rfl) ⟨686169, by rfl⟩ : syracuseStep 1829785 = 1372339) (by norm_num)
theorem B3255245 : Blo 1445542 3255245 := bbase (se 3 (by rfl) ⟨610358, by rfl⟩ : syracuseStep 3255245 = 1220717) (by norm_num)
theorem B1829881 : Blo 1445542 1829881 := bbase (se 2 (by rfl) ⟨686205, by rfl⟩ : syracuseStep 1829881 = 1372411) (by norm_num)
theorem B3255317 : Blo 1445542 3255317 := bbase (se 6 (by rfl) ⟨76296, by rfl⟩ : syracuseStep 3255317 = 152593) (by norm_num)
theorem B7326773 : Blo 1445542 7326773 := bbase (se 5 (by rfl) ⟨343442, by rfl⟩ : syracuseStep 7326773 = 686885) (by norm_num)
theorem B2059357 : Blo 1445542 2059357 := bbase (se 3 (by rfl) ⟨386129, by rfl⟩ : syracuseStep 2059357 = 772259) (by norm_num)
theorem B3255389 : Blo 1445542 3255389 := bbase (se 3 (by rfl) ⟨610385, by rfl⟩ : syracuseStep 3255389 = 1220771) (by norm_num)
theorem B2747533 : Blo 1445542 2747533 := bbase (se 3 (by rfl) ⟨515162, by rfl⟩ : syracuseStep 2747533 = 1030325) (by norm_num)
theorem B7818389 : Blo 1445542 7818389 := bbase (se 6 (by rfl) ⟨183243, by rfl⟩ : syracuseStep 7818389 = 366487) (by norm_num)
theorem B1830053 : Blo 1445542 1830053 := bbase (se 4 (by rfl) ⟨171567, by rfl⟩ : syracuseStep 1830053 = 343135) (by norm_num)
theorem B3255461 : Blo 1445542 3255461 := bbase (se 4 (by rfl) ⟨305199, by rfl⟩ : syracuseStep 3255461 = 610399) (by norm_num)
theorem B5213381 : Blo 1445542 5213381 := bbase (se 4 (by rfl) ⟨488754, by rfl⟩ : syracuseStep 5213381 = 977509) (by norm_num)
theorem B1830109 : Blo 1445542 1830109 := bbase (se 3 (by rfl) ⟨343145, by rfl⟩ : syracuseStep 1830109 = 686291) (by norm_num)
theorem B2608357 : Blo 1445542 2608357 := bbase (se 4 (by rfl) ⟨244533, by rfl⟩ : syracuseStep 2608357 = 489067) (by norm_num)
theorem B3255533 : Blo 1445542 3255533 := bbase (se 3 (by rfl) ⟨610412, by rfl⟩ : syracuseStep 3255533 = 1220825) (by norm_num)
theorem B3910901 : Blo 1445542 3910901 := bbase (se 5 (by rfl) ⟨183323, by rfl⟩ : syracuseStep 3910901 = 366647) (by norm_num)
theorem B2747677 : Blo 1445542 2747677 := bbase (se 3 (by rfl) ⟨515189, by rfl⟩ : syracuseStep 2747677 = 1030379) (by norm_num)
theorem B4631861 : Blo 1445542 4631861 := bbase (se 5 (by rfl) ⟨217118, by rfl⟩ : syracuseStep 4631861 = 434237) (by norm_num)
theorem B3255605 : Blo 1445542 3255605 := bbase (se 5 (by rfl) ⟨152606, by rfl⟩ : syracuseStep 3255605 = 305213) (by norm_num)
theorem B1830205 : Blo 1445542 1830205 := bbase (se 3 (by rfl) ⟨343163, by rfl⟩ : syracuseStep 1830205 = 686327) (by norm_num)
theorem B2198909 : Blo 1445542 2198909 := bbase (se 3 (by rfl) ⟨412295, by rfl⟩ : syracuseStep 2198909 = 824591) (by norm_num)
theorem B3255677 : Blo 1445542 3255677 := bbase (se 3 (by rfl) ⟨610439, by rfl⟩ : syracuseStep 3255677 = 1220879) (by norm_num)
theorem B2747837 : Blo 1445542 2747837 := bbase (se 3 (by rfl) ⟨515219, by rfl⟩ : syracuseStep 2747837 = 1030439) (by norm_num)
theorem B3255749 : Blo 1445542 3255749 := bbase (se 4 (by rfl) ⟨305226, by rfl⟩ : syracuseStep 3255749 = 610453) (by norm_num)
theorem B7318997 : Blo 1445542 7318997 := bbase (se 7 (by rfl) ⟨85769, by rfl⟩ : syracuseStep 7318997 = 171539) (by norm_num)
theorem B1830377 : Blo 1445542 1830377 := bbase (se 2 (by rfl) ⟨686391, by rfl⟩ : syracuseStep 1830377 = 1372783) (by norm_num)
theorem B2821645 : Blo 1445542 2821645 := bbase (se 3 (by rfl) ⟨529058, by rfl⟩ : syracuseStep 2821645 = 1058117) (by norm_num)
theorem B3255821 : Blo 1445542 3255821 := bbase (se 3 (by rfl) ⟨610466, by rfl⟩ : syracuseStep 3255821 = 1220933) (by norm_num)
theorem B1830433 : Blo 1445542 1830433 := bbase (se 2 (by rfl) ⟨686412, by rfl⟩ : syracuseStep 1830433 = 1372825) (by norm_num)
theorem B1543745 : Blo 1445542 1543745 := bbase (se 2 (by rfl) ⟨578904, by rfl⟩ : syracuseStep 1543745 = 1157809) (by norm_num)
theorem B2747981 : Blo 1445542 2747981 := bbase (se 3 (by rfl) ⟨515246, by rfl⟩ : syracuseStep 2747981 = 1030493) (by norm_num)
theorem B3255893 : Blo 1445542 3255893 := bbase (se 8 (by rfl) ⟨19077, by rfl⟩ : syracuseStep 3255893 = 38155) (by norm_num)
theorem B1830529 : Blo 1445542 1830529 := bbase (se 2 (by rfl) ⟨686448, by rfl⟩ : syracuseStep 1830529 = 1372897) (by norm_num)
theorem B3477125 : Blo 1445542 3477125 := bbase (se 4 (by rfl) ⟨325980, by rfl⟩ : syracuseStep 3477125 = 651961) (by norm_num)
theorem B1543817 : Blo 1445542 1543817 := bbase (se 2 (by rfl) ⟨578931, by rfl⟩ : syracuseStep 1543817 = 1157863) (by norm_num)
theorem B3255965 : Blo 1445542 3255965 := bbase (se 3 (by rfl) ⟨610493, by rfl⟩ : syracuseStep 3255965 = 1220987) (by norm_num)
theorem B2059949 : Blo 1445542 2059949 := bbase (se 3 (by rfl) ⟨386240, by rfl⟩ : syracuseStep 2059949 = 772481) (by norm_num)
theorem B3256037 : Blo 1445542 3256037 := bbase (se 4 (by rfl) ⟨305253, by rfl⟩ : syracuseStep 3256037 = 610507) (by norm_num)
theorem B2060029 : Blo 1445542 2060029 := bbase (se 3 (by rfl) ⟨386255, by rfl⟩ : syracuseStep 2060029 = 772511) (by norm_num)
theorem B1830701 : Blo 1445542 1830701 := bbase (se 3 (by rfl) ⟨343256, by rfl⟩ : syracuseStep 1830701 = 686513) (by norm_num)
theorem B3256109 : Blo 1445542 3256109 := bbase (se 3 (by rfl) ⟨610520, by rfl⟩ : syracuseStep 3256109 = 1221041) (by norm_num)
theorem B1544005 : Blo 1445542 1544005 := bbase (se 4 (by rfl) ⟨144750, by rfl⟩ : syracuseStep 1544005 = 289501) (by norm_num)
theorem B3297125 : Blo 1445542 3297125 := bbase (se 4 (by rfl) ⟨309105, by rfl⟩ : syracuseStep 3297125 = 618211) (by norm_num)
theorem B1830757 : Blo 1445542 1830757 := bbase (se 4 (by rfl) ⟨171633, by rfl⟩ : syracuseStep 1830757 = 343267) (by norm_num)
theorem B2060149 : Blo 1445542 2060149 := bbase (se 5 (by rfl) ⟨96569, by rfl⟩ : syracuseStep 2060149 = 193139) (by norm_num)
theorem B3256181 : Blo 1445542 3256181 := bbase (se 5 (by rfl) ⟨152633, by rfl⟩ : syracuseStep 3256181 = 305267) (by norm_num)
theorem B3256253 : Blo 1445542 3256253 := bbase (se 3 (by rfl) ⟨610547, by rfl⟩ : syracuseStep 3256253 = 1221095) (by norm_num)
theorem B1830853 : Blo 1445542 1830853 := bbase (se 4 (by rfl) ⟨171642, by rfl⟩ : syracuseStep 1830853 = 343285) (by norm_num)
theorem B2060245 : Blo 1445542 2060245 := bbase (se 7 (by rfl) ⟨24143, by rfl⟩ : syracuseStep 2060245 = 48287) (by norm_num)
theorem B2543605 : Blo 1445542 2543605 := bbase (se 5 (by rfl) ⟨119231, by rfl⟩ : syracuseStep 2543605 = 238463) (by norm_num)
theorem B1544189 : Blo 1445542 1544189 := bbase (se 3 (by rfl) ⟨289535, by rfl⟩ : syracuseStep 1544189 = 579071) (by norm_num)
theorem B3256325 : Blo 1445542 3256325 := bbase (se 4 (by rfl) ⟨305280, by rfl⟩ : syracuseStep 3256325 = 610561) (by norm_num)
theorem B8794133 : Blo 1445542 8794133 := bbase (se 6 (by rfl) ⟨206112, by rfl⟩ : syracuseStep 8794133 = 412225) (by norm_num)
theorem B3256397 : Blo 1445542 3256397 := bbase (se 3 (by rfl) ⟨610574, by rfl⟩ : syracuseStep 3256397 = 1221149) (by norm_num)
theorem B1831025 : Blo 1445542 1831025 := bbase (se 2 (by rfl) ⟨686634, by rfl⟩ : syracuseStep 1831025 = 1373269) (by norm_num)
theorem B1626241 : Blo 1445542 1626241 := bbase (se 2 (by rfl) ⟨609840, by rfl⟩ : syracuseStep 1626241 = 1219681) (by norm_num)
theorem B2199701 : Blo 1445542 2199701 := bbase (se 6 (by rfl) ⟨51555, by rfl⟩ : syracuseStep 2199701 = 103111) (by norm_num)
theorem B3256469 : Blo 1445542 3256469 := bbase (se 6 (by rfl) ⟨76323, by rfl⟩ : syracuseStep 3256469 = 152647) (by norm_num)
theorem B1626277 : Blo 1445542 1626277 := bbase (se 4 (by rfl) ⟨152463, by rfl⟩ : syracuseStep 1626277 = 304927) (by norm_num)
theorem B1831081 : Blo 1445542 1831081 := bbase (se 2 (by rfl) ⟨686655, by rfl⟩ : syracuseStep 1831081 = 1373311) (by norm_num)
theorem B1626313 : Blo 1445542 1626313 := bbase (se 2 (by rfl) ⟨609867, by rfl⟩ : syracuseStep 1626313 = 1219735) (by norm_num)
theorem B3256541 : Blo 1445542 3256541 := bbase (se 3 (by rfl) ⟨610601, by rfl⟩ : syracuseStep 3256541 = 1221203) (by norm_num)
theorem B1855721 : Blo 1445542 1855721 := bbase (se 2 (by rfl) ⟨695895, by rfl⟩ : syracuseStep 1855721 = 1391791) (by norm_num)
theorem B1626349 : Blo 1445542 1626349 := bbase (se 3 (by rfl) ⟨304940, by rfl⟩ : syracuseStep 1626349 = 609881) (by norm_num)
theorem B6598901 : Blo 1445542 6598901 := bbase (se 5 (by rfl) ⟨309323, by rfl⟩ : syracuseStep 6598901 = 618647) (by norm_num)
theorem B1831177 : Blo 1445542 1831177 := bbase (se 2 (by rfl) ⟨686691, by rfl⟩ : syracuseStep 1831177 = 1373383) (by norm_num)
theorem B1626385 : Blo 1445542 1626385 := bbase (se 2 (by rfl) ⟨609894, by rfl⟩ : syracuseStep 1626385 = 1219789) (by norm_num)
theorem B3256613 : Blo 1445542 3256613 := bbase (se 4 (by rfl) ⟨305307, by rfl⟩ : syracuseStep 3256613 = 610615) (by norm_num)
theorem B1626421 : Blo 1445542 1626421 := bbase (se 5 (by rfl) ⟨76238, by rfl⟩ : syracuseStep 1626421 = 152477) (by norm_num)
theorem B7328069 : Blo 1445542 7328069 := bbase (se 4 (by rfl) ⟨687006, by rfl⟩ : syracuseStep 7328069 = 1374013) (by norm_num)
theorem B19796309 : Blo 1445542 19796309 := bbase (se 10 (by rfl) ⟨28998, by rfl⟩ : syracuseStep 19796309 = 57997) (by norm_num)
theorem B1626457 : Blo 1445542 1626457 := bbase (se 2 (by rfl) ⟨609921, by rfl⟩ : syracuseStep 1626457 = 1219843) (by norm_num)
theorem B3256685 : Blo 1445542 3256685 := bbase (se 3 (by rfl) ⟨610628, by rfl⟩ : syracuseStep 3256685 = 1221257) (by norm_num)
theorem B6025589 : Blo 1445542 6025589 := bbase (se 5 (by rfl) ⟨282449, by rfl⟩ : syracuseStep 6025589 = 564899) (by norm_num)
theorem B1626493 : Blo 1445542 1626493 := bbase (se 3 (by rfl) ⟨304967, by rfl⟩ : syracuseStep 1626493 = 609935) (by norm_num)
theorem B4116869 : Blo 1445542 4116869 := bbase (se 4 (by rfl) ⟨385956, by rfl⟩ : syracuseStep 4116869 = 771913) (by norm_num)
theorem B1626529 : Blo 1445542 1626529 := bbase (se 2 (by rfl) ⟨609948, by rfl⟩ : syracuseStep 1626529 = 1219897) (by norm_num)
theorem B1831349 : Blo 1445542 1831349 := bbase (se 5 (by rfl) ⟨85844, by rfl⟩ : syracuseStep 1831349 = 171689) (by norm_num)
theorem B3256757 : Blo 1445542 3256757 := bbase (se 5 (by rfl) ⟨152660, by rfl⟩ : syracuseStep 3256757 = 305321) (by norm_num)
theorem B1626565 : Blo 1445542 1626565 := bbase (se 4 (by rfl) ⟨152490, by rfl⟩ : syracuseStep 1626565 = 304981) (by norm_num)
theorem B2060741 : Blo 1445542 2060741 := bbase (se 4 (by rfl) ⟨193194, by rfl⟩ : syracuseStep 2060741 = 386389) (by norm_num)
theorem B1626601 : Blo 1445542 1626601 := bbase (se 2 (by rfl) ⟨609975, by rfl⟩ : syracuseStep 1626601 = 1219951) (by norm_num)
theorem B1831405 : Blo 1445542 1831405 := bbase (se 3 (by rfl) ⟨343388, by rfl⟩ : syracuseStep 1831405 = 686777) (by norm_num)
theorem B3256829 : Blo 1445542 3256829 := bbase (se 3 (by rfl) ⟨610655, by rfl⟩ : syracuseStep 3256829 = 1221311) (by norm_num)
theorem B1626637 : Blo 1445542 1626637 := bbase (se 3 (by rfl) ⟨304994, by rfl⟩ : syracuseStep 1626637 = 609989) (by norm_num)
theorem B1626673 : Blo 1445542 1626673 := bbase (se 2 (by rfl) ⟨610002, by rfl⟩ : syracuseStep 1626673 = 1220005) (by norm_num)
theorem B3256901 : Blo 1445542 3256901 := bbase (se 4 (by rfl) ⟨305334, by rfl⟩ : syracuseStep 3256901 = 610669) (by norm_num)
theorem B1831501 : Blo 1445542 1831501 := bbase (se 3 (by rfl) ⟨343406, by rfl⟩ : syracuseStep 1831501 = 686813) (by norm_num)
theorem B1626709 : Blo 1445542 1626709 := bbase (se 8 (by rfl) ⟨9531, by rfl⟩ : syracuseStep 1626709 = 19063) (by norm_num)
theorem B5493365 : Blo 1445542 5493365 := bbase (se 5 (by rfl) ⟨257501, by rfl⟩ : syracuseStep 5493365 = 515003) (by norm_num)
theorem B1626745 : Blo 1445542 1626745 := bbase (se 2 (by rfl) ⟨610029, by rfl⟩ : syracuseStep 1626745 = 1220059) (by norm_num)
theorem B1626781 : Blo 1445542 1626781 := bbase (se 3 (by rfl) ⟨305021, by rfl⟩ : syracuseStep 1626781 = 610043) (by norm_num)
theorem B6181541 : Blo 1445542 6181541 := bbase (se 4 (by rfl) ⟨579519, by rfl⟩ : syracuseStep 6181541 = 1159039) (by norm_num)
theorem B1626817 : Blo 1445542 1626817 := bbase (se 2 (by rfl) ⟨610056, by rfl⟩ : syracuseStep 1626817 = 1220113) (by norm_num)
theorem B4879061 : Blo 1445542 4879061 := bbase (se 7 (by rfl) ⟨57176, by rfl⟩ : syracuseStep 4879061 = 114353) (by norm_num)
theorem B7320293 : Blo 1445542 7320293 := bbase (se 4 (by rfl) ⟨686277, by rfl⟩ : syracuseStep 7320293 = 1372555) (by norm_num)
theorem B1626853 : Blo 1445542 1626853 := bbase (se 4 (by rfl) ⟨152517, by rfl⟩ : syracuseStep 1626853 = 305035) (by norm_num)
theorem B1856233 : Blo 1445542 1856233 := bbase (se 2 (by rfl) ⟨696087, by rfl⟩ : syracuseStep 1856233 = 1392175) (by norm_num)
theorem B1544941 : Blo 1445542 1544941 := bbase (se 3 (by rfl) ⟨289676, by rfl⟩ : syracuseStep 1544941 = 579353) (by norm_num)
theorem B1831673 : Blo 1445542 1831673 := bbase (se 2 (by rfl) ⟨686877, by rfl⟩ : syracuseStep 1831673 = 1373755) (by norm_num)
theorem B1626889 : Blo 1445542 1626889 := bbase (se 2 (by rfl) ⟨610083, by rfl⟩ : syracuseStep 1626889 = 1220167) (by norm_num)
theorem B1856269 : Blo 1445542 1856269 := bbase (se 3 (by rfl) ⟨348050, by rfl⟩ : syracuseStep 1856269 = 696101) (by norm_num)
theorem B2200333 : Blo 1445542 2200333 := bbase (se 3 (by rfl) ⟨412562, by rfl⟩ : syracuseStep 2200333 = 825125) (by norm_num)
theorem B1626925 : Blo 1445542 1626925 := bbase (se 3 (by rfl) ⟨305048, by rfl⟩ : syracuseStep 1626925 = 610097) (by norm_num)
theorem B1831729 : Blo 1445542 1831729 := bbase (se 2 (by rfl) ⟨686898, by rfl⟩ : syracuseStep 1831729 = 1373797) (by norm_num)
theorem B4117301 : Blo 1445542 4117301 := bbase (se 5 (by rfl) ⟨192998, by rfl⟩ : syracuseStep 4117301 = 385997) (by norm_num)
theorem B1545013 : Blo 1445542 1545013 := bbase (se 5 (by rfl) ⟨72422, by rfl⟩ : syracuseStep 1545013 = 144845) (by norm_num)
theorem B1626961 : Blo 1445542 1626961 := bbase (se 2 (by rfl) ⟨610110, by rfl⟩ : syracuseStep 1626961 = 1220221) (by norm_num)
theorem B1626997 : Blo 1445542 1626997 := bbase (se 5 (by rfl) ⟨76265, by rfl⟩ : syracuseStep 1626997 = 152531) (by norm_num)
theorem B1831825 : Blo 1445542 1831825 := bbase (se 2 (by rfl) ⟨686934, by rfl⟩ : syracuseStep 1831825 = 1373869) (by norm_num)
theorem B5493653 : Blo 1445542 5493653 := bbase (se 6 (by rfl) ⟨128757, by rfl⟩ : syracuseStep 5493653 = 257515) (by norm_num)
theorem B1627033 : Blo 1445542 1627033 := bbase (se 2 (by rfl) ⟨610137, by rfl⟩ : syracuseStep 1627033 = 1220275) (by norm_num)
theorem B5215141 : Blo 1445542 5215141 := bbase (se 4 (by rfl) ⟨488919, by rfl⟩ : syracuseStep 5215141 = 977839) (by norm_num)
theorem B1627069 : Blo 1445542 1627069 := bbase (se 3 (by rfl) ⟨305075, by rfl⟩ : syracuseStep 1627069 = 610151) (by norm_num)
theorem B6181829 : Blo 1445542 6181829 := bbase (se 4 (by rfl) ⟨579546, by rfl⟩ : syracuseStep 6181829 = 1159093) (by norm_num)
theorem B1627105 : Blo 1445542 1627105 := bbase (se 2 (by rfl) ⟨610164, by rfl⟩ : syracuseStep 1627105 = 1220329) (by norm_num)
theorem B1545193 : Blo 1445542 1545193 := bbase (se 2 (by rfl) ⟨579447, by rfl⟩ : syracuseStep 1545193 = 1158895) (by norm_num)
theorem B1627141 : Blo 1445542 1627141 := bbase (se 4 (by rfl) ⟨152544, by rfl⟩ : syracuseStep 1627141 = 305089) (by norm_num)
theorem B1627177 : Blo 1445542 1627177 := bbase (se 2 (by rfl) ⟨610191, by rfl⟩ : syracuseStep 1627177 = 1220383) (by norm_num)
theorem B1831997 : Blo 1445542 1831997 := bbase (se 3 (by rfl) ⟨343499, by rfl⟩ : syracuseStep 1831997 = 686999) (by norm_num)
theorem B1627213 : Blo 1445542 1627213 := bbase (se 3 (by rfl) ⟨305102, by rfl⟩ : syracuseStep 1627213 = 610205) (by norm_num)
theorem B5944421 : Blo 1445542 5944421 := bbase (se 4 (by rfl) ⟨557289, by rfl⟩ : syracuseStep 5944421 = 1114579) (by norm_num)
theorem B1627249 : Blo 1445542 1627249 := bbase (se 2 (by rfl) ⟨610218, by rfl⟩ : syracuseStep 1627249 = 1220437) (by norm_num)
theorem B4879493 : Blo 1445542 4879493 := bbase (se 4 (by rfl) ⟨457452, by rfl⟩ : syracuseStep 4879493 = 914905) (by norm_num)
theorem B1627285 : Blo 1445542 1627285 := bbase (se 6 (by rfl) ⟨38139, by rfl⟩ : syracuseStep 1627285 = 76279) (by norm_num)
theorem B1627321 : Blo 1445542 1627321 := bbase (se 2 (by rfl) ⟨610245, by rfl⟩ : syracuseStep 1627321 = 1220491) (by norm_num)
theorem B4175045 : Blo 1445542 4175045 := bbase (se 4 (by rfl) ⟨391410, by rfl⟩ : syracuseStep 4175045 = 782821) (by norm_num)
theorem B8238293 : Blo 1445542 8238293 := bbase (se 7 (by rfl) ⟨96542, by rfl⟩ : syracuseStep 8238293 = 193085) (by norm_num)
theorem B1627357 : Blo 1445542 1627357 := bbase (se 3 (by rfl) ⟨305129, by rfl⟩ : syracuseStep 1627357 = 610259) (by norm_num)
theorem B1627393 : Blo 1445542 1627393 := bbase (se 2 (by rfl) ⟨610272, by rfl⟩ : syracuseStep 1627393 = 1220545) (by norm_num)
theorem B4633861 : Blo 1445542 4633861 := bbase (se 4 (by rfl) ⟨434424, by rfl⟩ : syracuseStep 4633861 = 868849) (by norm_num)
theorem B1627429 : Blo 1445542 1627429 := bbase (se 4 (by rfl) ⟨152571, by rfl⟩ : syracuseStep 1627429 = 305143) (by norm_num)
theorem B3659053 : Blo 1445542 3659053 := bbase (se 3 (by rfl) ⟨686072, by rfl⟩ : syracuseStep 3659053 = 1372145) (by norm_num)
theorem B1627465 : Blo 1445542 1627465 := bbase (se 2 (by rfl) ⟨610299, by rfl⟩ : syracuseStep 1627465 = 1220599) (by norm_num)
theorem B1627501 : Blo 1445542 1627501 := bbase (se 3 (by rfl) ⟨305156, by rfl⟩ : syracuseStep 1627501 = 610313) (by norm_num)
theorem B1627537 : Blo 1445542 1627537 := bbase (se 2 (by rfl) ⟨610326, by rfl⟩ : syracuseStep 1627537 = 1220653) (by norm_num)
theorem B3659165 : Blo 1445542 3659165 := bbase (se 3 (by rfl) ⟨686093, by rfl⟩ : syracuseStep 3659165 = 1372187) (by norm_num)
theorem B1545637 : Blo 1445542 1545637 := bbase (se 4 (by rfl) ⟨144903, by rfl⟩ : syracuseStep 1545637 = 289807) (by norm_num)
theorem B1627573 : Blo 1445542 1627573 := bbase (se 5 (by rfl) ⟨76292, by rfl⟩ : syracuseStep 1627573 = 152585) (by norm_num)
theorem B6952405 : Blo 1445542 6952405 := bbase (se 7 (by rfl) ⟨81473, by rfl⟩ : syracuseStep 6952405 = 162947) (by norm_num)
theorem B1627609 : Blo 1445542 1627609 := bbase (se 2 (by rfl) ⟨610353, by rfl⟩ : syracuseStep 1627609 = 1220707) (by norm_num)
theorem B1627645 : Blo 1445542 1627645 := bbase (se 3 (by rfl) ⟨305183, by rfl⟩ : syracuseStep 1627645 = 610367) (by norm_num)
theorem B2168333 : Blo 1445542 2168333 := bbase (se 3 (by rfl) ⟨406562, by rfl⟩ : syracuseStep 2168333 = 813125) (by norm_num)
theorem B1627681 : Blo 1445542 1627681 := bbase (se 2 (by rfl) ⟨610380, by rfl⟩ : syracuseStep 1627681 = 1220761) (by norm_num)
theorem B1545761 : Blo 1445542 1545761 := bbase (se 2 (by rfl) ⟨579660, by rfl⟩ : syracuseStep 1545761 = 1159321) (by norm_num)
theorem B2168357 : Blo 1445542 2168357 := bbase (se 4 (by rfl) ⟨203283, by rfl⟩ : syracuseStep 2168357 = 406567) (by norm_num)
theorem B4118053 : Blo 1445542 4118053 := bbase (se 4 (by rfl) ⟨386067, by rfl⟩ : syracuseStep 4118053 = 772135) (by norm_num)
theorem B4879925 : Blo 1445542 4879925 := bbase (se 5 (by rfl) ⟨228746, by rfl⟩ : syracuseStep 4879925 = 457493) (by norm_num)
theorem B2168381 : Blo 1445542 2168381 := bbase (se 3 (by rfl) ⟨406571, by rfl⟩ : syracuseStep 2168381 = 813143) (by norm_num)
theorem B3298877 : Blo 1445542 3298877 := bbase (se 3 (by rfl) ⟨618539, by rfl⟩ : syracuseStep 3298877 = 1237079) (by norm_num)
theorem B1627717 : Blo 1445542 1627717 := bbase (se 4 (by rfl) ⟨152598, by rfl⟩ : syracuseStep 1627717 = 305197) (by norm_num)
theorem B2168405 : Blo 1445542 2168405 := bbase (se 8 (by rfl) ⟨12705, by rfl⟩ : syracuseStep 2168405 = 25411) (by norm_num)
theorem B3659357 : Blo 1445542 3659357 := bbase (se 3 (by rfl) ⟨686129, by rfl⟩ : syracuseStep 3659357 = 1372259) (by norm_num)
theorem B1627753 : Blo 1445542 1627753 := bbase (se 2 (by rfl) ⟨610407, by rfl⟩ : syracuseStep 1627753 = 1220815) (by norm_num)
theorem B2168429 : Blo 1445542 2168429 := bbase (se 3 (by rfl) ⟨406580, by rfl⟩ : syracuseStep 2168429 = 813161) (by norm_num)
theorem B2315893 : Blo 1445542 2315893 := bbase (se 5 (by rfl) ⟨108557, by rfl⟩ : syracuseStep 2315893 = 217115) (by norm_num)
theorem B2168453 : Blo 1445542 2168453 := bbase (se 4 (by rfl) ⟨203292, by rfl⟩ : syracuseStep 2168453 = 406585) (by norm_num)
theorem B1627789 : Blo 1445542 1627789 := bbase (se 3 (by rfl) ⟨305210, by rfl⟩ : syracuseStep 1627789 = 610421) (by norm_num)
theorem B2168477 : Blo 1445542 2168477 := bbase (se 3 (by rfl) ⟨406589, by rfl⟩ : syracuseStep 2168477 = 813179) (by norm_num)
theorem B1627825 : Blo 1445542 1627825 := bbase (se 2 (by rfl) ⟨610434, by rfl⟩ : syracuseStep 1627825 = 1220869) (by norm_num)
theorem B2168501 : Blo 1445542 2168501 := bbase (se 5 (by rfl) ⟨101648, by rfl⟩ : syracuseStep 2168501 = 203297) (by norm_num)
theorem B6182581 : Blo 1445542 6182581 := bbase (se 5 (by rfl) ⟨289808, by rfl⟩ : syracuseStep 6182581 = 579617) (by norm_num)
theorem B2168525 : Blo 1445542 2168525 := bbase (se 3 (by rfl) ⟨406598, by rfl⟩ : syracuseStep 2168525 = 813197) (by norm_num)
theorem B1627861 : Blo 1445542 1627861 := bbase (se 7 (by rfl) ⟨19076, by rfl⟩ : syracuseStep 1627861 = 38153) (by norm_num)
theorem B2168549 : Blo 1445542 2168549 := bbase (se 4 (by rfl) ⟨203301, by rfl⟩ : syracuseStep 2168549 = 406603) (by norm_num)
theorem B1627897 : Blo 1445542 1627897 := bbase (se 2 (by rfl) ⟨610461, by rfl⟩ : syracuseStep 1627897 = 1220923) (by norm_num)
theorem B2168573 : Blo 1445542 2168573 := bbase (se 3 (by rfl) ⟨406607, by rfl⟩ : syracuseStep 2168573 = 813215) (by norm_num)
theorem B2168597 : Blo 1445542 2168597 := bbase (se 6 (by rfl) ⟨50826, by rfl⟩ : syracuseStep 2168597 = 101653) (by norm_num)
theorem B1627933 : Blo 1445542 1627933 := bbase (se 3 (by rfl) ⟨305237, by rfl⟩ : syracuseStep 1627933 = 610475) (by norm_num)
theorem B2168621 : Blo 1445542 2168621 := bbase (se 3 (by rfl) ⟨406616, by rfl⟩ : syracuseStep 2168621 = 813233) (by norm_num)
theorem B1627969 : Blo 1445542 1627969 := bbase (se 2 (by rfl) ⟨610488, by rfl⟩ : syracuseStep 1627969 = 1220977) (by norm_num)
theorem B2168645 : Blo 1445542 2168645 := bbase (se 4 (by rfl) ⟨203310, by rfl⟩ : syracuseStep 2168645 = 406621) (by norm_num)
theorem B2168669 : Blo 1445542 2168669 := bbase (se 3 (by rfl) ⟨406625, by rfl⟩ : syracuseStep 2168669 = 813251) (by norm_num)
theorem B1628005 : Blo 1445542 1628005 := bbase (se 4 (by rfl) ⟨152625, by rfl⟩ : syracuseStep 1628005 = 305251) (by norm_num)
theorem B2168693 : Blo 1445542 2168693 := bbase (se 5 (by rfl) ⟨101657, by rfl⟩ : syracuseStep 2168693 = 203315) (by norm_num)
theorem B1628041 : Blo 1445542 1628041 := bbase (se 2 (by rfl) ⟨610515, by rfl⟩ : syracuseStep 1628041 = 1221031) (by norm_num)
theorem B2168717 : Blo 1445542 2168717 := bbase (se 3 (by rfl) ⟨406634, by rfl⟩ : syracuseStep 2168717 = 813269) (by norm_num)
theorem B2168741 : Blo 1445542 2168741 := bbase (se 4 (by rfl) ⟨203319, by rfl⟩ : syracuseStep 2168741 = 406639) (by norm_num)
theorem B1628077 : Blo 1445542 1628077 := bbase (se 3 (by rfl) ⟨305264, by rfl⟩ : syracuseStep 1628077 = 610529) (by norm_num)
theorem B3659701 : Blo 1445542 3659701 := bbase (se 5 (by rfl) ⟨171548, by rfl⟩ : syracuseStep 3659701 = 343097) (by norm_num)
theorem B1955765 : Blo 1445542 1955765 := bbase (se 5 (by rfl) ⟨91676, by rfl⟩ : syracuseStep 1955765 = 183353) (by norm_num)
theorem B2168765 : Blo 1445542 2168765 := bbase (se 3 (by rfl) ⟨406643, by rfl⟩ : syracuseStep 2168765 = 813287) (by norm_num)
theorem B1628113 : Blo 1445542 1628113 := bbase (se 2 (by rfl) ⟨610542, by rfl⟩ : syracuseStep 1628113 = 1221085) (by norm_num)
theorem B2168789 : Blo 1445542 2168789 := bbase (se 7 (by rfl) ⟨25415, by rfl⟩ : syracuseStep 2168789 = 50831) (by norm_num)
theorem B4880357 : Blo 1445542 4880357 := bbase (se 4 (by rfl) ⟨457533, by rfl⟩ : syracuseStep 4880357 = 915067) (by norm_num)
theorem B2168813 : Blo 1445542 2168813 := bbase (se 3 (by rfl) ⟨406652, by rfl⟩ : syracuseStep 2168813 = 813305) (by norm_num)
theorem B7321589 : Blo 1445542 7321589 := bbase (se 5 (by rfl) ⟨343199, by rfl⟩ : syracuseStep 7321589 = 686399) (by norm_num)
theorem B1628149 : Blo 1445542 1628149 := bbase (se 5 (by rfl) ⟨76319, by rfl⟩ : syracuseStep 1628149 = 152639) (by norm_num)
theorem B2168837 : Blo 1445542 2168837 := bbase (se 4 (by rfl) ⟨203328, by rfl⟩ : syracuseStep 2168837 = 406657) (by norm_num)
theorem B1628185 : Blo 1445542 1628185 := bbase (se 2 (by rfl) ⟨610569, by rfl⟩ : syracuseStep 1628185 = 1221139) (by norm_num)
theorem B2168861 : Blo 1445542 2168861 := bbase (se 3 (by rfl) ⟨406661, by rfl⟩ : syracuseStep 2168861 = 813323) (by norm_num)
theorem B3659813 : Blo 1445542 3659813 := bbase (se 4 (by rfl) ⟨343107, by rfl⟩ : syracuseStep 3659813 = 686215) (by norm_num)
theorem B2168885 : Blo 1445542 2168885 := bbase (se 5 (by rfl) ⟨101666, by rfl⟩ : syracuseStep 2168885 = 203333) (by norm_num)
theorem B2316341 : Blo 1445542 2316341 := bbase (se 5 (by rfl) ⟨108578, by rfl⟩ : syracuseStep 2316341 = 217157) (by norm_num)
theorem B5494837 : Blo 1445542 5494837 := bbase (se 5 (by rfl) ⟨257570, by rfl⟩ : syracuseStep 5494837 = 515141) (by norm_num)
theorem B1628221 : Blo 1445542 1628221 := bbase (se 3 (by rfl) ⟨305291, by rfl⟩ : syracuseStep 1628221 = 610583) (by norm_num)
theorem B2168909 : Blo 1445542 2168909 := bbase (se 3 (by rfl) ⟨406670, by rfl⟩ : syracuseStep 2168909 = 813341) (by norm_num)
theorem B1628257 : Blo 1445542 1628257 := bbase (se 2 (by rfl) ⟨610596, by rfl⟩ : syracuseStep 1628257 = 1221193) (by norm_num)
theorem B2168933 : Blo 1445542 2168933 := bbase (se 4 (by rfl) ⟨203337, by rfl⟩ : syracuseStep 2168933 = 406675) (by norm_num)
theorem B2168957 : Blo 1445542 2168957 := bbase (se 3 (by rfl) ⟨406679, by rfl⟩ : syracuseStep 2168957 = 813359) (by norm_num)
theorem B1628293 : Blo 1445542 1628293 := bbase (se 4 (by rfl) ⟨152652, by rfl⟩ : syracuseStep 1628293 = 305305) (by norm_num)
theorem B2168981 : Blo 1445542 2168981 := bbase (se 6 (by rfl) ⟨50835, by rfl⟩ : syracuseStep 2168981 = 101671) (by norm_num)
theorem B1628329 : Blo 1445542 1628329 := bbase (se 2 (by rfl) ⟨610623, by rfl⟩ : syracuseStep 1628329 = 1221247) (by norm_num)
theorem B2169005 : Blo 1445542 2169005 := bbase (se 3 (by rfl) ⟨406688, by rfl⟩ : syracuseStep 2169005 = 813377) (by norm_num)
theorem B2169029 : Blo 1445542 2169029 := bbase (se 4 (by rfl) ⟨203346, by rfl⟩ : syracuseStep 2169029 = 406693) (by norm_num)
theorem B1628365 : Blo 1445542 1628365 := bbase (se 3 (by rfl) ⟨305318, by rfl⟩ : syracuseStep 1628365 = 610637) (by norm_num)
theorem B2439389 : Blo 1445542 2439389 := bbase (se 3 (by rfl) ⟨457385, by rfl⟩ : syracuseStep 2439389 = 914771) (by norm_num)
theorem B2169053 : Blo 1445542 2169053 := bbase (se 3 (by rfl) ⟨406697, by rfl⟩ : syracuseStep 2169053 = 813395) (by norm_num)
theorem B3660005 : Blo 1445542 3660005 := bbase (se 4 (by rfl) ⟨343125, by rfl⟩ : syracuseStep 3660005 = 686251) (by norm_num)
theorem B1628401 : Blo 1445542 1628401 := bbase (se 2 (by rfl) ⟨610650, by rfl⟩ : syracuseStep 1628401 = 1221301) (by norm_num)
theorem B2169077 : Blo 1445542 2169077 := bbase (se 5 (by rfl) ⟨101675, by rfl⟩ : syracuseStep 2169077 = 203351) (by norm_num)
theorem B10991861 : Blo 1445542 10991861 := bbase (se 5 (by rfl) ⟨515243, by rfl⟩ : syracuseStep 10991861 = 1030487) (by norm_num)
theorem B3709181 : Blo 1445542 3709181 := bbase (se 3 (by rfl) ⟨695471, by rfl⟩ : syracuseStep 3709181 = 1390943) (by norm_num)
theorem B2169101 : Blo 1445542 2169101 := bbase (se 3 (by rfl) ⟨406706, by rfl⟩ : syracuseStep 2169101 = 813413) (by norm_num)
theorem B1628437 : Blo 1445542 1628437 := bbase (se 6 (by rfl) ⟨38166, by rfl⟩ : syracuseStep 1628437 = 76333) (by norm_num)
theorem B2169125 : Blo 1445542 2169125 := bbase (se 4 (by rfl) ⟨203355, by rfl⟩ : syracuseStep 2169125 = 406711) (by norm_num)
theorem B1628473 : Blo 1445542 1628473 := bbase (se 2 (by rfl) ⟨610677, by rfl⟩ : syracuseStep 1628473 = 1221355) (by norm_num)
theorem B2169149 : Blo 1445542 2169149 := bbase (se 3 (by rfl) ⟨406715, by rfl⟩ : syracuseStep 2169149 = 813431) (by norm_num)
theorem B2169173 : Blo 1445542 2169173 := bbase (se 10 (by rfl) ⟨3177, by rfl⟩ : syracuseStep 2169173 = 6355) (by norm_num)
theorem B2439517 : Blo 1445542 2439517 := bbase (se 3 (by rfl) ⟨457409, by rfl⟩ : syracuseStep 2439517 = 914819) (by norm_num)
theorem B5495141 : Blo 1445542 5495141 := bbase (se 4 (by rfl) ⟨515169, by rfl⟩ : syracuseStep 5495141 = 1030339) (by norm_num)
theorem B2169197 : Blo 1445542 2169197 := bbase (se 3 (by rfl) ⟨406724, by rfl⟩ : syracuseStep 2169197 = 813449) (by norm_num)
theorem B2169221 : Blo 1445542 2169221 := bbase (se 4 (by rfl) ⟨203364, by rfl⟩ : syracuseStep 2169221 = 406729) (by norm_num)
theorem B4880789 : Blo 1445542 4880789 := bbase (se 6 (by rfl) ⟨114393, by rfl⟩ : syracuseStep 4880789 = 228787) (by norm_num)
theorem B2169245 : Blo 1445542 2169245 := bbase (se 3 (by rfl) ⟨406733, by rfl⟩ : syracuseStep 2169245 = 813467) (by norm_num)
theorem B2439605 : Blo 1445542 2439605 := bbase (se 5 (by rfl) ⟨114356, by rfl⟩ : syracuseStep 2439605 = 228713) (by norm_num)
theorem B2169269 : Blo 1445542 2169269 := bbase (se 5 (by rfl) ⟨101684, by rfl⟩ : syracuseStep 2169269 = 203369) (by norm_num)
theorem B2169293 : Blo 1445542 2169293 := bbase (se 3 (by rfl) ⟨406742, by rfl⟩ : syracuseStep 2169293 = 813485) (by norm_num)
theorem B2169317 : Blo 1445542 2169317 := bbase (se 4 (by rfl) ⟨203373, by rfl⟩ : syracuseStep 2169317 = 406747) (by norm_num)
theorem B3709421 : Blo 1445542 3709421 := bbase (se 3 (by rfl) ⟨695516, by rfl⟩ : syracuseStep 3709421 = 1391033) (by norm_num)
theorem B5282293 : Blo 1445542 5282293 := bbase (se 5 (by rfl) ⟨247607, by rfl⟩ : syracuseStep 5282293 = 495215) (by norm_num)
theorem B2169341 : Blo 1445542 2169341 := bbase (se 3 (by rfl) ⟨406751, by rfl⟩ : syracuseStep 2169341 = 813503) (by norm_num)
theorem B2169365 : Blo 1445542 2169365 := bbase (se 6 (by rfl) ⟨50844, by rfl⟩ : syracuseStep 2169365 = 101689) (by norm_num)
theorem B2169389 : Blo 1445542 2169389 := bbase (se 3 (by rfl) ⟨406760, by rfl⟩ : syracuseStep 2169389 = 813521) (by norm_num)
theorem B2439733 : Blo 1445542 2439733 := bbase (se 5 (by rfl) ⟨114362, by rfl⟩ : syracuseStep 2439733 = 228725) (by norm_num)
theorem B3660349 : Blo 1445542 3660349 := bbase (se 3 (by rfl) ⟨686315, by rfl⟩ : syracuseStep 3660349 = 1372631) (by norm_num)
theorem B2169413 : Blo 1445542 2169413 := bbase (se 4 (by rfl) ⟨203382, by rfl⟩ : syracuseStep 2169413 = 406765) (by norm_num)
theorem B16702037 : Blo 1445542 16702037 := bbase (se 8 (by rfl) ⟨97863, by rfl⟩ : syracuseStep 16702037 = 195727) (by norm_num)
theorem B2169437 : Blo 1445542 2169437 := bbase (se 3 (by rfl) ⟨406769, by rfl⟩ : syracuseStep 2169437 = 813539) (by norm_num)
theorem B2169461 : Blo 1445542 2169461 := bbase (se 5 (by rfl) ⟨101693, by rfl⟩ : syracuseStep 2169461 = 203387) (by norm_num)
theorem B2349685 : Blo 1445542 2349685 := bbase (se 5 (by rfl) ⟨110141, by rfl⟩ : syracuseStep 2349685 = 220283) (by norm_num)
theorem B2439821 : Blo 1445542 2439821 := bbase (se 3 (by rfl) ⟨457466, by rfl⟩ : syracuseStep 2439821 = 914933) (by norm_num)
theorem B2169485 : Blo 1445542 2169485 := bbase (se 3 (by rfl) ⟨406778, by rfl⟩ : syracuseStep 2169485 = 813557) (by norm_num)
theorem B10984085 : Blo 1445542 10984085 := bbase (se 6 (by rfl) ⟨257439, by rfl⟩ : syracuseStep 10984085 = 514879) (by norm_num)
theorem B2169509 : Blo 1445542 2169509 := bbase (se 4 (by rfl) ⟨203391, by rfl⟩ : syracuseStep 2169509 = 406783) (by norm_num)
theorem B3660461 : Blo 1445542 3660461 := bbase (se 3 (by rfl) ⟨686336, by rfl⟩ : syracuseStep 3660461 = 1372673) (by norm_num)
theorem B13187765 : Blo 1445542 13187765 := bbase (se 5 (by rfl) ⟨618176, by rfl⟩ : syracuseStep 13187765 = 1236353) (by norm_num)
theorem B2169533 : Blo 1445542 2169533 := bbase (se 3 (by rfl) ⟨406787, by rfl⟩ : syracuseStep 2169533 = 813575) (by norm_num)
theorem B2169557 : Blo 1445542 2169557 := bbase (se 7 (by rfl) ⟨25424, by rfl⟩ : syracuseStep 2169557 = 50849) (by norm_num)
theorem B2169581 : Blo 1445542 2169581 := bbase (se 3 (by rfl) ⟨406796, by rfl⟩ : syracuseStep 2169581 = 813593) (by norm_num)
theorem B2169605 : Blo 1445542 2169605 := bbase (se 4 (by rfl) ⟨203400, by rfl⟩ : syracuseStep 2169605 = 406801) (by norm_num)
theorem B2439949 : Blo 1445542 2439949 := bbase (se 3 (by rfl) ⟨457490, by rfl⟩ : syracuseStep 2439949 = 914981) (by norm_num)
theorem B2169629 : Blo 1445542 2169629 := bbase (se 3 (by rfl) ⟨406805, by rfl⟩ : syracuseStep 2169629 = 813611) (by norm_num)
theorem B6175541 : Blo 1445542 6175541 := bbase (se 5 (by rfl) ⟨289478, by rfl⟩ : syracuseStep 6175541 = 578957) (by norm_num)
theorem B2169653 : Blo 1445542 2169653 := bbase (se 5 (by rfl) ⟨101702, by rfl⟩ : syracuseStep 2169653 = 203405) (by norm_num)
theorem B4881221 : Blo 1445542 4881221 := bbase (se 4 (by rfl) ⟨457614, by rfl⟩ : syracuseStep 4881221 = 915229) (by norm_num)
theorem B2169677 : Blo 1445542 2169677 := bbase (se 3 (by rfl) ⟨406814, by rfl⟩ : syracuseStep 2169677 = 813629) (by norm_num)
theorem B11139925 : Blo 1445542 11139925 := bbase (se 9 (by rfl) ⟨32636, by rfl⟩ : syracuseStep 11139925 = 65273) (by norm_num)
theorem B2440037 : Blo 1445542 2440037 := bbase (se 4 (by rfl) ⟨228753, by rfl⟩ : syracuseStep 2440037 = 457507) (by norm_num)
theorem B2169701 : Blo 1445542 2169701 := bbase (se 4 (by rfl) ⟨203409, by rfl⟩ : syracuseStep 2169701 = 406819) (by norm_num)
theorem B3660653 : Blo 1445542 3660653 := bbase (se 3 (by rfl) ⟨686372, by rfl⟩ : syracuseStep 3660653 = 1372745) (by norm_num)
theorem B2169725 : Blo 1445542 2169725 := bbase (se 3 (by rfl) ⟨406823, by rfl⟩ : syracuseStep 2169725 = 813647) (by norm_num)
theorem B2169749 : Blo 1445542 2169749 := bbase (se 6 (by rfl) ⟨50853, by rfl⟩ : syracuseStep 2169749 = 101707) (by norm_num)
theorem B2169773 : Blo 1445542 2169773 := bbase (se 3 (by rfl) ⟨406832, by rfl⟩ : syracuseStep 2169773 = 813665) (by norm_num)
theorem B2931653 : Blo 1445542 2931653 := bbase (se 4 (by rfl) ⟨274842, by rfl⟩ : syracuseStep 2931653 = 549685) (by norm_num)
theorem B2169797 : Blo 1445542 2169797 := bbase (se 4 (by rfl) ⟨203418, by rfl⟩ : syracuseStep 2169797 = 406837) (by norm_num)
theorem B2169821 : Blo 1445542 2169821 := bbase (se 3 (by rfl) ⟨406841, by rfl⟩ : syracuseStep 2169821 = 813683) (by norm_num)
theorem B2440165 : Blo 1445542 2440165 := bbase (se 4 (by rfl) ⟨228765, by rfl⟩ : syracuseStep 2440165 = 457531) (by norm_num)
theorem B2169845 : Blo 1445542 2169845 := bbase (se 5 (by rfl) ⟨101711, by rfl⟩ : syracuseStep 2169845 = 203423) (by norm_num)
theorem B2169869 : Blo 1445542 2169869 := bbase (se 3 (by rfl) ⟨406850, by rfl⟩ : syracuseStep 2169869 = 813701) (by norm_num)
theorem B2169893 : Blo 1445542 2169893 := bbase (se 4 (by rfl) ⟨203427, by rfl⟩ : syracuseStep 2169893 = 406855) (by norm_num)
theorem B2440253 : Blo 1445542 2440253 := bbase (se 3 (by rfl) ⟨457547, by rfl⟩ : syracuseStep 2440253 = 915095) (by norm_num)
theorem B2169917 : Blo 1445542 2169917 := bbase (se 3 (by rfl) ⟨406859, by rfl⟩ : syracuseStep 2169917 = 813719) (by norm_num)
theorem B2169941 : Blo 1445542 2169941 := bbase (se 8 (by rfl) ⟨12714, by rfl⟩ : syracuseStep 2169941 = 25429) (by norm_num)
theorem B2169965 : Blo 1445542 2169965 := bbase (se 3 (by rfl) ⟨406868, by rfl⟩ : syracuseStep 2169965 = 813737) (by norm_num)
theorem B6347909 : Blo 1445542 6347909 := bbase (se 4 (by rfl) ⟨595116, by rfl⟩ : syracuseStep 6347909 = 1190233) (by norm_num)
theorem B2169989 : Blo 1445542 2169989 := bbase (se 4 (by rfl) ⟨203436, by rfl⟩ : syracuseStep 2169989 = 406873) (by norm_num)
theorem B2170013 : Blo 1445542 2170013 := bbase (se 3 (by rfl) ⟨406877, by rfl⟩ : syracuseStep 2170013 = 813755) (by norm_num)
theorem B2170037 : Blo 1445542 2170037 := bbase (se 5 (by rfl) ⟨101720, by rfl⟩ : syracuseStep 2170037 = 203441) (by norm_num)
theorem B2440381 : Blo 1445542 2440381 := bbase (se 3 (by rfl) ⟨457571, by rfl⟩ : syracuseStep 2440381 = 915143) (by norm_num)
theorem B3660997 : Blo 1445542 3660997 := bbase (se 4 (by rfl) ⟨343218, by rfl⟩ : syracuseStep 3660997 = 686437) (by norm_num)
theorem B2170061 : Blo 1445542 2170061 := bbase (se 3 (by rfl) ⟨406886, by rfl⟩ : syracuseStep 2170061 = 813773) (by norm_num)
theorem B2170085 : Blo 1445542 2170085 := bbase (se 4 (by rfl) ⟨203445, by rfl⟩ : syracuseStep 2170085 = 406891) (by norm_num)
theorem B4881653 : Blo 1445542 4881653 := bbase (se 5 (by rfl) ⟨228827, by rfl⟩ : syracuseStep 4881653 = 457655) (by norm_num)
theorem B2170109 : Blo 1445542 2170109 := bbase (se 3 (by rfl) ⟨406895, by rfl⟩ : syracuseStep 2170109 = 813791) (by norm_num)
theorem B7519493 : Blo 1445542 7519493 := bbase (se 4 (by rfl) ⟨704952, by rfl⟩ : syracuseStep 7519493 = 1409905) (by norm_num)
theorem B7322885 : Blo 1445542 7322885 := bbase (se 4 (by rfl) ⟨686520, by rfl⟩ : syracuseStep 7322885 = 1373041) (by norm_num)
theorem B2440469 : Blo 1445542 2440469 := bbase (se 6 (by rfl) ⟨57198, by rfl⟩ : syracuseStep 2440469 = 114397) (by norm_num)
theorem B2170133 : Blo 1445542 2170133 := bbase (se 6 (by rfl) ⟨50862, by rfl⟩ : syracuseStep 2170133 = 101725) (by norm_num)
theorem B2170157 : Blo 1445542 2170157 := bbase (se 3 (by rfl) ⟨406904, by rfl⟩ : syracuseStep 2170157 = 813809) (by norm_num)
theorem B3661109 : Blo 1445542 3661109 := bbase (se 5 (by rfl) ⟨171614, by rfl⟩ : syracuseStep 3661109 = 343229) (by norm_num)
theorem B2170181 : Blo 1445542 2170181 := bbase (se 4 (by rfl) ⟨203454, by rfl⟩ : syracuseStep 2170181 = 406909) (by norm_num)
theorem B2170205 : Blo 1445542 2170205 := bbase (se 3 (by rfl) ⟨406913, by rfl⟩ : syracuseStep 2170205 = 813827) (by norm_num)
theorem B4947317 : Blo 1445542 4947317 := bbase (se 5 (by rfl) ⟨231905, by rfl⟩ : syracuseStep 4947317 = 463811) (by norm_num)
theorem B2170229 : Blo 1445542 2170229 := bbase (se 5 (by rfl) ⟨101729, by rfl⟩ : syracuseStep 2170229 = 203459) (by norm_num)
theorem B2170253 : Blo 1445542 2170253 := bbase (se 3 (by rfl) ⟨406922, by rfl⟩ : syracuseStep 2170253 = 813845) (by norm_num)
theorem B2440597 : Blo 1445542 2440597 := bbase (se 6 (by rfl) ⟨57201, by rfl⟩ : syracuseStep 2440597 = 114403) (by norm_num)
theorem B2170277 : Blo 1445542 2170277 := bbase (se 4 (by rfl) ⟨203463, by rfl⟩ : syracuseStep 2170277 = 406927) (by norm_num)
theorem B1465777 : Blo 1445542 1465777 := bbase (se 2 (by rfl) ⟨549666, by rfl⟩ : syracuseStep 1465777 = 1099333) (by norm_num)
theorem B2170301 : Blo 1445542 2170301 := bbase (se 3 (by rfl) ⟨406931, by rfl⟩ : syracuseStep 2170301 = 813863) (by norm_num)
theorem B2170325 : Blo 1445542 2170325 := bbase (se 7 (by rfl) ⟨25433, by rfl⟩ : syracuseStep 2170325 = 50867) (by norm_num)
theorem B2440685 : Blo 1445542 2440685 := bbase (se 3 (by rfl) ⟨457628, by rfl⟩ : syracuseStep 2440685 = 915257) (by norm_num)
theorem B2170349 : Blo 1445542 2170349 := bbase (se 3 (by rfl) ⟨406940, by rfl⟩ : syracuseStep 2170349 = 813881) (by norm_num)
theorem B3661301 : Blo 1445542 3661301 := bbase (se 5 (by rfl) ⟨171623, by rfl⟩ : syracuseStep 3661301 = 343247) (by norm_num)
theorem B2170373 : Blo 1445542 2170373 := bbase (se 4 (by rfl) ⟨203472, by rfl⟩ : syracuseStep 2170373 = 406945) (by norm_num)
theorem B2170397 : Blo 1445542 2170397 := bbase (se 3 (by rfl) ⟨406949, by rfl⟩ : syracuseStep 2170397 = 813899) (by norm_num)
theorem B2317853 : Blo 1445542 2317853 := bbase (se 3 (by rfl) ⟨434597, by rfl⟩ : syracuseStep 2317853 = 869195) (by norm_num)
theorem B2170421 : Blo 1445542 2170421 := bbase (se 5 (by rfl) ⟨101738, by rfl⟩ : syracuseStep 2170421 = 203477) (by norm_num)
theorem B2170445 : Blo 1445542 2170445 := bbase (se 3 (by rfl) ⟨406958, by rfl⟩ : syracuseStep 2170445 = 813917) (by norm_num)
theorem B9264725 : Blo 1445542 9264725 := bbase (se 8 (by rfl) ⟨54285, by rfl⟩ : syracuseStep 9264725 = 108571) (by norm_num)
theorem B2170469 : Blo 1445542 2170469 := bbase (se 4 (by rfl) ⟨203481, by rfl⟩ : syracuseStep 2170469 = 406963) (by norm_num)
theorem B2440813 : Blo 1445542 2440813 := bbase (se 3 (by rfl) ⟨457652, by rfl⟩ : syracuseStep 2440813 = 915305) (by norm_num)
theorem B2170493 : Blo 1445542 2170493 := bbase (se 3 (by rfl) ⟨406967, by rfl⟩ : syracuseStep 2170493 = 813935) (by norm_num)
theorem B2170517 : Blo 1445542 2170517 := bbase (se 6 (by rfl) ⟨50871, by rfl⟩ : syracuseStep 2170517 = 101743) (by norm_num)
theorem B2317981 : Blo 1445542 2317981 := bbase (se 3 (by rfl) ⟨434621, by rfl⟩ : syracuseStep 2317981 = 869243) (by norm_num)
theorem B3088037 : Blo 1445542 3088037 := bbase (se 4 (by rfl) ⟨289503, by rfl⟩ : syracuseStep 3088037 = 579007) (by norm_num)
theorem B4882085 : Blo 1445542 4882085 := bbase (se 4 (by rfl) ⟨457695, by rfl⟩ : syracuseStep 4882085 = 915391) (by norm_num)
theorem B2170541 : Blo 1445542 2170541 := bbase (se 3 (by rfl) ⟨406976, by rfl⟩ : syracuseStep 2170541 = 813953) (by norm_num)
theorem B2440901 : Blo 1445542 2440901 := bbase (se 4 (by rfl) ⟨228834, by rfl⟩ : syracuseStep 2440901 = 457669) (by norm_num)
theorem B2170565 : Blo 1445542 2170565 := bbase (se 4 (by rfl) ⟨203490, by rfl⟩ : syracuseStep 2170565 = 406981) (by norm_num)
theorem B2170589 : Blo 1445542 2170589 := bbase (se 3 (by rfl) ⟨406985, by rfl⟩ : syracuseStep 2170589 = 813971) (by norm_num)
theorem B12353269 : Blo 1445542 12353269 := bbase (se 5 (by rfl) ⟨579059, by rfl⟩ : syracuseStep 12353269 = 1158119) (by norm_num)
theorem B2170613 : Blo 1445542 2170613 := bbase (se 5 (by rfl) ⟨101747, by rfl⟩ : syracuseStep 2170613 = 203495) (by norm_num)
theorem B2170637 : Blo 1445542 2170637 := bbase (se 3 (by rfl) ⟨406994, by rfl⟩ : syracuseStep 2170637 = 813989) (by norm_num)
theorem B6176533 : Blo 1445542 6176533 := bbase (se 6 (by rfl) ⟨144762, by rfl⟩ : syracuseStep 6176533 = 289525) (by norm_num)
theorem B17841941 : Blo 1445542 17841941 := bbase (se 6 (by rfl) ⟨418170, by rfl⟩ : syracuseStep 17841941 = 836341) (by norm_num)
theorem B2170661 : Blo 1445542 2170661 := bbase (se 4 (by rfl) ⟨203499, by rfl⟩ : syracuseStep 2170661 = 406999) (by norm_num)
theorem B3088181 : Blo 1445542 3088181 := bbase (se 5 (by rfl) ⟨144758, by rfl⟩ : syracuseStep 3088181 = 289517) (by norm_num)
theorem B2170685 : Blo 1445542 2170685 := bbase (se 3 (by rfl) ⟨407003, by rfl⟩ : syracuseStep 2170685 = 814007) (by norm_num)
theorem B2441029 : Blo 1445542 2441029 := bbase (se 4 (by rfl) ⟨228846, by rfl⟩ : syracuseStep 2441029 = 457693) (by norm_num)
theorem B3661645 : Blo 1445542 3661645 := bbase (se 3 (by rfl) ⟨686558, by rfl⟩ : syracuseStep 3661645 = 1373117) (by norm_num)
theorem B2973517 : Blo 1445542 2973517 := bbase (se 3 (by rfl) ⟨557534, by rfl⟩ : syracuseStep 2973517 = 1115069) (by norm_num)
theorem B16473941 : Blo 1445542 16473941 := bbase (se 9 (by rfl) ⟨48263, by rfl⟩ : syracuseStep 16473941 = 96527) (by norm_num)
theorem B2170709 : Blo 1445542 2170709 := bbase (se 9 (by rfl) ⟨6359, by rfl⟩ : syracuseStep 2170709 = 12719) (by norm_num)
theorem B2170733 : Blo 1445542 2170733 := bbase (se 3 (by rfl) ⟨407012, by rfl⟩ : syracuseStep 2170733 = 814025) (by norm_num)
theorem B7421813 : Blo 1445542 7421813 := bbase (se 5 (by rfl) ⟨347897, by rfl⟩ : syracuseStep 7421813 = 695795) (by norm_num)
theorem B2170757 : Blo 1445542 2170757 := bbase (se 4 (by rfl) ⟨203508, by rfl⟩ : syracuseStep 2170757 = 407017) (by norm_num)
theorem B2441117 : Blo 1445542 2441117 := bbase (se 3 (by rfl) ⟨457709, by rfl⟩ : syracuseStep 2441117 = 915419) (by norm_num)
theorem B2170781 : Blo 1445542 2170781 := bbase (se 3 (by rfl) ⟨407021, by rfl⟩ : syracuseStep 2170781 = 814043) (by norm_num)
theorem B2170805 : Blo 1445542 2170805 := bbase (se 5 (by rfl) ⟨101756, by rfl⟩ : syracuseStep 2170805 = 203513) (by norm_num)
theorem B3661757 : Blo 1445542 3661757 := bbase (se 3 (by rfl) ⟨686579, by rfl⟩ : syracuseStep 3661757 = 1373159) (by norm_num)
theorem B2170829 : Blo 1445542 2170829 := bbase (se 3 (by rfl) ⟨407030, by rfl⟩ : syracuseStep 2170829 = 814061) (by norm_num)
theorem B2228197 : Blo 1445542 2228197 := bbase (se 4 (by rfl) ⟨208893, by rfl⟩ : syracuseStep 2228197 = 417787) (by norm_num)
theorem B2170853 : Blo 1445542 2170853 := bbase (se 4 (by rfl) ⟨203517, by rfl⟩ : syracuseStep 2170853 = 407035) (by norm_num)
theorem B1736689 : Blo 1445542 1736689 := bbase (se 2 (by rfl) ⟨651258, by rfl⟩ : syracuseStep 1736689 = 1302517) (by norm_num)
theorem B2170877 : Blo 1445542 2170877 := bbase (se 3 (by rfl) ⟨407039, by rfl⟩ : syracuseStep 2170877 = 814079) (by norm_num)
theorem B2170883 : Blo 1445542 2170883 := bstep (se 1 (by rfl) ⟨1628162, by rfl⟩ : syracuseStep 2170883 = 3256325) B3256325
theorem B2170913 : Blo 1445542 2170913 := bstep (se 2 (by rfl) ⟨814092, by rfl⟩ : syracuseStep 2170913 = 1628185) B1628185
theorem B2170931 : Blo 1445542 2170931 := bstep (se 1 (by rfl) ⟨1628198, by rfl⟩ : syracuseStep 2170931 = 3256397) B3256397
theorem B2170961 : Blo 1445542 2170961 := bstep (se 2 (by rfl) ⟨814110, by rfl⟩ : syracuseStep 2170961 = 1628221) B1628221
theorem B2441299 : Blo 1445542 2441299 := bstep (se 1 (by rfl) ⟨1830974, by rfl⟩ : syracuseStep 2441299 = 3661949) B3661949
theorem B1466467 : Blo 1445542 1466467 := bstep (se 1 (by rfl) ⟨1099850, by rfl⟩ : syracuseStep 1466467 = 2199701) B2199701
theorem B2170979 : Blo 1445542 2170979 := bstep (se 1 (by rfl) ⟨1628234, by rfl⟩ : syracuseStep 2170979 = 3256469) B3256469
theorem B2171009 : Blo 1445542 2171009 := bstep (se 2 (by rfl) ⟨814128, by rfl⟩ : syracuseStep 2171009 = 1628257) B1628257
theorem B3661969 : Blo 1445542 3661969 := bstep (se 2 (by rfl) ⟨1373238, by rfl⟩ : syracuseStep 3661969 = 2746477) B2746477
theorem B2171027 : Blo 1445542 2171027 := bstep (se 1 (by rfl) ⟨1628270, by rfl⟩ : syracuseStep 2171027 = 3256541) B3256541
theorem B4399267 : Blo 1445542 4399267 := bstep (se 1 (by rfl) ⟨3299450, by rfl⟩ : syracuseStep 4399267 = 6598901) B6598901
theorem B4636835 : Blo 1445542 4636835 := bstep (se 1 (by rfl) ⟨3477626, by rfl⟩ : syracuseStep 4636835 = 6955253) B6955253
theorem B4120753 : Blo 1445542 4120753 := bstep (se 2 (by rfl) ⟨1545282, by rfl⟩ : syracuseStep 4120753 = 3090565) B3090565
theorem B2171057 : Blo 1445542 2171057 := bstep (se 2 (by rfl) ⟨814146, by rfl⟩ : syracuseStep 2171057 = 1628293) B1628293
theorem B2171075 : Blo 1445542 2171075 := bstep (se 1 (by rfl) ⟨1628306, by rfl⟩ : syracuseStep 2171075 = 3256613) B3256613
theorem B2318545 : Blo 1445542 2318545 := bstep (se 2 (by rfl) ⟨869454, by rfl⟩ : syracuseStep 2318545 = 1738909) B1738909
theorem B2441441 : Blo 1445542 2441441 := bstep (se 2 (by rfl) ⟨915540, by rfl⟩ : syracuseStep 2441441 = 1831081) B1831081
theorem B2171105 : Blo 1445542 2171105 := bstep (se 2 (by rfl) ⟨814164, by rfl⟩ : syracuseStep 2171105 = 1628329) B1628329
theorem B13197539 : Blo 1445542 13197539 := bstep (se 1 (by rfl) ⟨9898154, by rfl⟩ : syracuseStep 13197539 = 19796309) B19796309
theorem B2171123 : Blo 1445542 2171123 := bstep (se 1 (by rfl) ⟨1628342, by rfl⟩ : syracuseStep 2171123 = 3256685) B3256685
theorem B2744579 : Blo 1445542 2744579 := bstep (se 1 (by rfl) ⟨2058434, by rfl⟩ : syracuseStep 2744579 = 4116869) B4116869
theorem B2171153 : Blo 1445542 2171153 := bstep (se 2 (by rfl) ⟨814182, by rfl⟩ : syracuseStep 2171153 = 1628365) B1628365
theorem B2171171 : Blo 1445542 2171171 := bstep (se 1 (by rfl) ⟨1628378, by rfl⟩ : syracuseStep 2171171 = 3256757) B3256757
theorem B4882733 : Blo 1445542 4882733 := bstep (se 3 (by rfl) ⟨915512, by rfl⟩ : syracuseStep 4882733 = 1831025) B1831025
theorem B2171201 : Blo 1445542 2171201 := bstep (se 2 (by rfl) ⟨814200, by rfl⟩ : syracuseStep 2171201 = 1628401) B1628401
theorem B2171219 : Blo 1445542 2171219 := bstep (se 1 (by rfl) ⟨1628414, by rfl⟩ : syracuseStep 2171219 = 3256829) B3256829
theorem B2441569 : Blo 1445542 2441569 := bstep (se 2 (by rfl) ⟨915588, by rfl⟩ : syracuseStep 2441569 = 1831177) B1831177
theorem B1737059 : Blo 1445542 1737059 := bstep (se 1 (by rfl) ⟨1302794, by rfl⟩ : syracuseStep 1737059 = 2605589) B2605589
theorem B4882787 : Blo 1445542 4882787 := bstep (se 1 (by rfl) ⟨3662090, by rfl⟩ : syracuseStep 4882787 = 7324181) B7324181
theorem B2171249 : Blo 1445542 2171249 := bstep (se 2 (by rfl) ⟨814218, by rfl⟩ : syracuseStep 2171249 = 1628437) B1628437
theorem B2441603 : Blo 1445542 2441603 := bstep (se 1 (by rfl) ⟨1831202, by rfl⟩ : syracuseStep 2441603 = 3662405) B3662405
theorem B2171267 : Blo 1445542 2171267 := bstep (se 1 (by rfl) ⟨1628450, by rfl⟩ : syracuseStep 2171267 = 3256901) B3256901
theorem B2171297 : Blo 1445542 2171297 := bstep (se 2 (by rfl) ⟨814236, by rfl⟩ : syracuseStep 2171297 = 1628473) B1628473
theorem B3662243 : Blo 1445542 3662243 := bstep (se 1 (by rfl) ⟨2746682, by rfl⟩ : syracuseStep 3662243 = 5493365) B5493365
theorem B4121027 : Blo 1445542 4121027 := bstep (se 1 (by rfl) ⟨3090770, by rfl⟩ : syracuseStep 4121027 = 6181541) B6181541
theorem B3252689 : Blo 1445542 3252689 := bstep (se 2 (by rfl) ⟨1219758, by rfl⟩ : syracuseStep 3252689 = 2439517) B2439517
theorem B3252707 : Blo 1445542 3252707 := bstep (se 1 (by rfl) ⟨2439530, by rfl⟩ : syracuseStep 3252707 = 4879061) B4879061
theorem B2441731 : Blo 1445542 2441731 := bstep (se 1 (by rfl) ⟨1831298, by rfl⟩ : syracuseStep 2441731 = 3662597) B3662597
theorem B13902349 : Blo 1445542 13902349 := bstep (se 3 (by rfl) ⟨2606690, by rfl⟩ : syracuseStep 13902349 = 5213381) B5213381
theorem B2744867 : Blo 1445542 2744867 := bstep (se 1 (by rfl) ⟨2058650, by rfl⟩ : syracuseStep 2744867 = 4117301) B4117301
theorem B3662435 : Blo 1445542 3662435 := bstep (se 1 (by rfl) ⟨2746826, by rfl⟩ : syracuseStep 3662435 = 5493653) B5493653
theorem B4948589 : Blo 1445542 4948589 := bstep (se 3 (by rfl) ⟨927860, by rfl⟩ : syracuseStep 4948589 = 1855721) B1855721
theorem B4883057 : Blo 1445542 4883057 := bstep (se 2 (by rfl) ⟨1831146, by rfl⟩ : syracuseStep 4883057 = 3662293) B3662293
theorem B4121219 : Blo 1445542 4121219 := bstep (se 1 (by rfl) ⟨3090914, by rfl⟩ : syracuseStep 4121219 = 6181829) B6181829
theorem B10429069 : Blo 1445542 10429069 := bstep (se 3 (by rfl) ⟨1955450, by rfl⟩ : syracuseStep 10429069 = 3910901) B3910901
theorem B2441873 : Blo 1445542 2441873 := bstep (se 2 (by rfl) ⟨915702, by rfl⟩ : syracuseStep 2441873 = 1831405) B1831405
theorem B3252977 : Blo 1445542 3252977 := bstep (se 2 (by rfl) ⟨1219866, by rfl⟩ : syracuseStep 3252977 = 2439733) B2439733
theorem B3252995 : Blo 1445542 3252995 := bstep (se 1 (by rfl) ⟨2439746, by rfl⟩ : syracuseStep 3252995 = 4879493) B4879493
theorem B2442001 : Blo 1445542 2442001 := bstep (se 2 (by rfl) ⟨915750, by rfl⟩ : syracuseStep 2442001 = 1831501) B1831501
theorem B2442035 : Blo 1445542 2442035 := bstep (se 1 (by rfl) ⟨1831526, by rfl⟩ : syracuseStep 2442035 = 3663053) B3663053
theorem B2442163 : Blo 1445542 2442163 := bstep (se 1 (by rfl) ⟨1831622, by rfl⟩ : syracuseStep 2442163 = 3663245) B3663245
theorem B2474977 : Blo 1445542 2474977 := bstep (se 2 (by rfl) ⟨928116, by rfl⟩ : syracuseStep 2474977 = 1856233) B1856233
theorem B18531341 : Blo 1445542 18531341 := bstep (se 3 (by rfl) ⟨3474626, by rfl⟩ : syracuseStep 18531341 = 6949253) B6949253
theorem B3253265 : Blo 1445542 3253265 := bstep (se 2 (by rfl) ⟨1219974, by rfl⟩ : syracuseStep 3253265 = 2439949) B2439949
theorem B2933777 : Blo 1445542 2933777 := bstep (se 2 (by rfl) ⟨1100166, by rfl⟩ : syracuseStep 2933777 = 2200333) B2200333
theorem B3253283 : Blo 1445542 3253283 := bstep (se 1 (by rfl) ⟨2439962, by rfl⟩ : syracuseStep 3253283 = 4879925) B4879925
theorem B2442305 : Blo 1445542 2442305 := bstep (se 2 (by rfl) ⟨915864, by rfl⟩ : syracuseStep 2442305 = 1831729) B1831729
theorem B14853233 : Blo 1445542 14853233 := bstep (se 2 (by rfl) ⟨5569962, by rfl⟩ : syracuseStep 14853233 = 11139925) B11139925
theorem B4883597 : Blo 1445542 4883597 := bstep (se 3 (by rfl) ⟨915674, by rfl⟩ : syracuseStep 4883597 = 1831349) B1831349
theorem B2442433 : Blo 1445542 2442433 := bstep (se 2 (by rfl) ⟨915912, by rfl⟩ : syracuseStep 2442433 = 1831825) B1831825
theorem B4883651 : Blo 1445542 4883651 := bstep (se 1 (by rfl) ⟨3662738, by rfl⟩ : syracuseStep 4883651 = 7325477) B7325477
theorem B2442467 : Blo 1445542 2442467 := bstep (se 1 (by rfl) ⟨1831850, by rfl⟩ : syracuseStep 2442467 = 3663701) B3663701
theorem B3253553 : Blo 1445542 3253553 := bstep (se 2 (by rfl) ⟨1220082, by rfl⟩ : syracuseStep 3253553 = 2440165) B2440165
theorem B3253571 : Blo 1445542 3253571 := bstep (se 1 (by rfl) ⟨2440178, by rfl⟩ : syracuseStep 3253571 = 4880357) B4880357
theorem B2442595 : Blo 1445542 2442595 := bstep (se 1 (by rfl) ⟨1831946, by rfl⟩ : syracuseStep 2442595 = 3663893) B3663893
theorem B4122029 : Blo 1445542 4122029 := bstep (se 3 (by rfl) ⟨772880, by rfl⟩ : syracuseStep 4122029 = 1545761) B1545761
theorem B2745809 : Blo 1445542 2745809 := bstep (se 2 (by rfl) ⟨1029678, by rfl⟩ : syracuseStep 2745809 = 2059357) B2059357
theorem B4883921 : Blo 1445542 4883921 := bstep (se 2 (by rfl) ⟨1831470, by rfl⟩ : syracuseStep 4883921 = 3662941) B3662941
theorem B3663377 : Blo 1445542 3663377 := bstep (se 2 (by rfl) ⟨1373766, by rfl⟩ : syracuseStep 3663377 = 2747533) B2747533
theorem B2606627 : Blo 1445542 2606627 := bstep (se 1 (by rfl) ⟨1954970, by rfl⟩ : syracuseStep 2606627 = 3909941) B3909941
theorem B3663427 : Blo 1445542 3663427 := bstep (se 1 (by rfl) ⟨2747570, by rfl⟩ : syracuseStep 3663427 = 5495141) B5495141
theorem B3253841 : Blo 1445542 3253841 := bstep (se 2 (by rfl) ⟨1220190, by rfl⟩ : syracuseStep 3253841 = 2440381) B2440381
theorem B3253859 : Blo 1445542 3253859 := bstep (se 1 (by rfl) ⟨2440394, by rfl⟩ : syracuseStep 3253859 = 4880789) B4880789
theorem B6178481 : Blo 1445542 6178481 := bstep (se 2 (by rfl) ⟨2316930, by rfl⟩ : syracuseStep 6178481 = 4633861) B4633861
theorem B8234693 : Blo 1445542 8234693 := bstep (se 4 (by rfl) ⟨772002, by rfl⟩ : syracuseStep 8234693 = 1544005) B1544005
theorem B3663569 : Blo 1445542 3663569 := bstep (se 2 (by rfl) ⟨1373838, by rfl⟩ : syracuseStep 3663569 = 2747677) B2747677
theorem B11134691 : Blo 1445542 11134691 := bstep (se 1 (by rfl) ⟨8351018, by rfl⟩ : syracuseStep 11134691 = 16702037) B16702037
theorem B8791843 : Blo 1445542 8791843 := bstep (se 1 (by rfl) ⟨6593882, by rfl⟩ : syracuseStep 8791843 = 13187765) B13187765
theorem B3254129 : Blo 1445542 3254129 := bstep (se 2 (by rfl) ⟨1220298, by rfl⟩ : syracuseStep 3254129 = 2440597) B2440597
theorem B3254147 : Blo 1445542 3254147 := bstep (se 1 (by rfl) ⟨2440610, by rfl⟩ : syracuseStep 3254147 = 4881221) B4881221
theorem B4884461 : Blo 1445542 4884461 := bstep (se 3 (by rfl) ⟨915836, by rfl⟩ : syracuseStep 4884461 = 1831673) B1831673
theorem B9897997 : Blo 1445542 9897997 := bstep (se 3 (by rfl) ⟨1855874, by rfl⟩ : syracuseStep 9897997 = 3711749) B3711749
theorem B3762193 : Blo 1445542 3762193 := bstep (se 2 (by rfl) ⟨1410822, by rfl⟩ : syracuseStep 3762193 = 2821645) B2821645
theorem B4884515 : Blo 1445542 4884515 := bstep (se 1 (by rfl) ⟨3663386, by rfl⟩ : syracuseStep 4884515 = 7326773) B7326773
theorem B5490737 : Blo 1445542 5490737 := bstep (se 2 (by rfl) ⟨2059026, by rfl⟩ : syracuseStep 5490737 = 4118053) B4118053
theorem B4950065 : Blo 1445542 4950065 := bstep (se 2 (by rfl) ⟨1856274, by rfl⟩ : syracuseStep 4950065 = 3712549) B3712549
theorem B44533813 : Blo 1445542 44533813 := bstep (se 5 (by rfl) ⟨2087522, by rfl⟩ : syracuseStep 44533813 = 4175045) B4175045
theorem B5212259 : Blo 1445542 5212259 := bstep (se 1 (by rfl) ⟨3909194, by rfl⟩ : syracuseStep 5212259 = 7818389) B7818389
theorem B16468109 : Blo 1445542 16468109 := bstep (se 3 (by rfl) ⟨3087770, by rfl⟩ : syracuseStep 16468109 = 6175541) B6175541
theorem B3254417 : Blo 1445542 3254417 := bstep (se 2 (by rfl) ⟨1220406, by rfl⟩ : syracuseStep 3254417 = 2440813) B2440813
theorem B3254435 : Blo 1445542 3254435 := bstep (se 1 (by rfl) ⟨2440826, by rfl⟩ : syracuseStep 3254435 = 4881653) B4881653
theorem B3090641 : Blo 1445542 3090641 := bstep (se 2 (by rfl) ⟨1158990, by rfl⟩ : syracuseStep 3090641 = 2317981) B2317981
theorem B8243441 : Blo 1445542 8243441 := bstep (se 2 (by rfl) ⟨3091290, by rfl⟩ : syracuseStep 8243441 = 6182581) B6182581
theorem B7817477 : Blo 1445542 7817477 := bstep (se 4 (by rfl) ⟨732888, by rfl⟩ : syracuseStep 7817477 = 1465777) B1465777
theorem B8792333 : Blo 1445542 8792333 := bstep (se 3 (by rfl) ⟨1648562, by rfl⟩ : syracuseStep 8792333 = 3297125) B3297125
theorem B8030513 : Blo 1445542 8030513 := bstep (se 2 (by rfl) ⟨3011442, by rfl⟩ : syracuseStep 8030513 = 6022885) B6022885
theorem B4884785 : Blo 1445542 4884785 := bstep (se 2 (by rfl) ⟨1831794, by rfl⟩ : syracuseStep 4884785 = 3663589) B3663589
theorem B2746705 : Blo 1445542 2746705 := bstep (se 2 (by rfl) ⟨1030014, by rfl⟩ : syracuseStep 2746705 = 2060029) B2060029
theorem B8235377 : Blo 1445542 8235377 := bstep (se 2 (by rfl) ⟨3088266, by rfl⟩ : syracuseStep 8235377 = 6176533) B6176533
theorem B2197937 : Blo 1445542 2197937 := bstep (se 2 (by rfl) ⟨824226, by rfl⟩ : syracuseStep 2197937 = 1648453) B1648453
theorem B3254705 : Blo 1445542 3254705 := bstep (se 2 (by rfl) ⟨1220514, by rfl⟩ : syracuseStep 3254705 = 2441029) B2441029
theorem B2058691 : Blo 1445542 2058691 := bstep (se 1 (by rfl) ⟨1544018, by rfl⟩ : syracuseStep 2058691 = 3088037) B3088037
theorem B3254723 : Blo 1445542 3254723 := bstep (se 1 (by rfl) ⟨2441042, by rfl⟩ : syracuseStep 3254723 = 4882085) B4882085
theorem B10987973 : Blo 1445542 10987973 := bstep (se 4 (by rfl) ⟨1030122, by rfl⟩ : syracuseStep 10987973 = 2060245) B2060245
theorem B2746865 : Blo 1445542 2746865 := bstep (se 2 (by rfl) ⟨1030074, by rfl⟩ : syracuseStep 2746865 = 2060149) B2060149
theorem B7817741 : Blo 1445542 7817741 := bstep (se 3 (by rfl) ⟨1465826, by rfl⟩ : syracuseStep 7817741 = 2931653) B2931653
theorem B2058787 : Blo 1445542 2058787 := bstep (se 1 (by rfl) ⟨1544090, by rfl⟩ : syracuseStep 2058787 = 3088181) B3088181
theorem B3910339 : Blo 1445542 3910339 := bstep (se 1 (by rfl) ⟨2932754, by rfl⟩ : syracuseStep 3910339 = 5865509) B5865509
theorem B13904581 : Blo 1445542 13904581 := bstep (se 4 (by rfl) ⟨1303554, by rfl⟩ : syracuseStep 13904581 = 2607109) B2607109
theorem B3254993 : Blo 1445542 3254993 := bstep (se 2 (by rfl) ⟨1220622, by rfl⟩ : syracuseStep 3254993 = 2441245) B2441245
theorem B3255011 : Blo 1445542 3255011 := bstep (se 1 (by rfl) ⟨2441258, by rfl⟩ : syracuseStep 3255011 = 4882517) B4882517
theorem B7326449 : Blo 1445542 7326449 := bstep (se 2 (by rfl) ⟨2747418, by rfl⟩ : syracuseStep 7326449 = 5494837) B5494837
theorem B7318349 : Blo 1445542 7318349 := bstep (se 3 (by rfl) ⟨1372190, by rfl⟩ : syracuseStep 7318349 = 2744381) B2744381
theorem B4885325 : Blo 1445542 4885325 := bstep (se 3 (by rfl) ⟨915998, by rfl⟩ : syracuseStep 4885325 = 1831997) B1831997
theorem B2747267 : Blo 1445542 2747267 := bstep (se 1 (by rfl) ⟨2060450, by rfl⟩ : syracuseStep 2747267 = 4120901) B4120901
theorem B4885379 : Blo 1445542 4885379 := bstep (se 1 (by rfl) ⟨3664034, by rfl⟩ : syracuseStep 4885379 = 7328069) B7328069
theorem B4017059 : Blo 1445542 4017059 := bstep (se 1 (by rfl) ⟨3012794, by rfl⟩ : syracuseStep 4017059 = 6025589) B6025589
theorem B2198497 : Blo 1445542 2198497 := bstep (se 2 (by rfl) ⟨824436, by rfl⟩ : syracuseStep 2198497 = 1648873) B1648873
theorem B3255281 : Blo 1445542 3255281 := bstep (se 2 (by rfl) ⟨1220730, by rfl⟩ : syracuseStep 3255281 = 2441461) B2441461
theorem B1829891 : Blo 1445542 1829891 := bstep (se 1 (by rfl) ⟨1372418, by rfl⟩ : syracuseStep 1829891 = 2744837) B2744837
theorem B3255299 : Blo 1445542 3255299 := bstep (se 1 (by rfl) ⟨2441474, by rfl⟩ : syracuseStep 3255299 = 4882949) B4882949
theorem B16927757 : Blo 1445542 16927757 := bstep (se 3 (by rfl) ⟨3173954, by rfl⟩ : syracuseStep 16927757 = 6347909) B6347909
theorem B2059283 : Blo 1445542 2059283 := bstep (se 1 (by rfl) ⟨1544462, by rfl⟩ : syracuseStep 2059283 = 3088925) B3088925
theorem B18091061 : Blo 1445542 18091061 := bstep (se 5 (by rfl) ⟨848018, by rfl⟩ : syracuseStep 18091061 = 1696037) B1696037
theorem B2198593 : Blo 1445542 2198593 := bstep (se 2 (by rfl) ⟨824472, by rfl⟩ : syracuseStep 2198593 = 1648945) B1648945
theorem B3255569 : Blo 1445542 3255569 := bstep (se 2 (by rfl) ⟨1220838, by rfl⟩ : syracuseStep 3255569 = 2441677) B2441677
theorem B3255587 : Blo 1445542 3255587 := bstep (se 1 (by rfl) ⟨2441690, by rfl⟩ : syracuseStep 3255587 = 4883381) B4883381
theorem B9268643 : Blo 1445542 9268643 := bstep (se 1 (by rfl) ⟨6951482, by rfl⟩ : syracuseStep 9268643 = 13902965) B13902965
theorem B5492195 : Blo 1445542 5492195 := bstep (se 1 (by rfl) ⟨4119146, by rfl⟩ : syracuseStep 5492195 = 8238293) B8238293
theorem B3132913 : Blo 1445542 3132913 := bstep (se 2 (by rfl) ⟨1174842, by rfl⟩ : syracuseStep 3132913 = 2349685) B2349685
theorem B3255857 : Blo 1445542 3255857 := bstep (se 2 (by rfl) ⟨1220946, by rfl⟩ : syracuseStep 3255857 = 2441893) B2441893
theorem B3255875 : Blo 1445542 3255875 := bstep (se 1 (by rfl) ⟨2441906, by rfl⟩ : syracuseStep 3255875 = 4883813) B4883813
theorem B2059921 : Blo 1445542 2059921 := bstep (se 2 (by rfl) ⟨772470, by rfl⟩ : syracuseStep 2059921 = 1544941) B1544941
theorem B1445555 : Blo 1445542 1445555 := bstep (se 1 (by rfl) ⟨1084166, by rfl⟩ : syracuseStep 1445555 = 2168333) B2168333
theorem B1445571 : Blo 1445542 1445571 := bstep (se 1 (by rfl) ⟨1084178, by rfl⟩ : syracuseStep 1445571 = 2168357) B2168357
theorem B1830595 : Blo 1445542 1830595 := bstep (se 1 (by rfl) ⟨1372946, by rfl⟩ : syracuseStep 1830595 = 2745893) B2745893
theorem B5861069 : Blo 1445542 5861069 := bstep (se 3 (by rfl) ⟨1098950, by rfl⟩ : syracuseStep 5861069 = 2197901) B2197901
theorem B1445587 : Blo 1445542 1445587 := bstep (se 1 (by rfl) ⟨1084190, by rfl⟩ : syracuseStep 1445587 = 2168381) B2168381
theorem B2199251 : Blo 1445542 2199251 := bstep (se 1 (by rfl) ⟨1649438, by rfl⟩ : syracuseStep 2199251 = 3298877) B3298877
theorem B1445603 : Blo 1445542 1445603 := bstep (se 1 (by rfl) ⟨1084202, by rfl⟩ : syracuseStep 1445603 = 2168405) B2168405
theorem B1445619 : Blo 1445542 1445619 := bstep (se 1 (by rfl) ⟨1084214, by rfl⟩ : syracuseStep 1445619 = 2168429) B2168429
theorem B1445635 : Blo 1445542 1445635 := bstep (se 1 (by rfl) ⟨1084226, by rfl⟩ : syracuseStep 1445635 = 2168453) B2168453
theorem B1445651 : Blo 1445542 1445651 := bstep (se 1 (by rfl) ⟨1084238, by rfl⟩ : syracuseStep 1445651 = 2168477) B2168477
theorem B1445667 : Blo 1445542 1445667 := bstep (se 1 (by rfl) ⟨1084250, by rfl⟩ : syracuseStep 1445667 = 2168501) B2168501
theorem B8236835 : Blo 1445542 8236835 := bstep (se 1 (by rfl) ⟨6177626, by rfl⟩ : syracuseStep 8236835 = 12355253) B12355253
theorem B1830691 : Blo 1445542 1830691 := bstep (se 1 (by rfl) ⟨1373018, by rfl⟩ : syracuseStep 1830691 = 2746037) B2746037
theorem B1445683 : Blo 1445542 1445683 := bstep (se 1 (by rfl) ⟨1084262, by rfl⟩ : syracuseStep 1445683 = 2168525) B2168525
theorem B1445699 : Blo 1445542 1445699 := bstep (se 1 (by rfl) ⟨1084274, by rfl⟩ : syracuseStep 1445699 = 2168549) B2168549
theorem B3256145 : Blo 1445542 3256145 := bstep (se 2 (by rfl) ⟨1221054, by rfl⟩ : syracuseStep 3256145 = 2442109) B2442109
theorem B1445715 : Blo 1445542 1445715 := bstep (se 1 (by rfl) ⟨1084286, by rfl⟩ : syracuseStep 1445715 = 2168573) B2168573
theorem B1445731 : Blo 1445542 1445731 := bstep (se 1 (by rfl) ⟨1084298, by rfl⟩ : syracuseStep 1445731 = 2168597) B2168597
theorem B3256163 : Blo 1445542 3256163 := bstep (se 1 (by rfl) ⟨2442122, by rfl⟩ : syracuseStep 3256163 = 4884245) B4884245
theorem B3346289 : Blo 1445542 3346289 := bstep (se 2 (by rfl) ⟨1254858, by rfl⟩ : syracuseStep 3346289 = 2509717) B2509717
theorem B1445747 : Blo 1445542 1445747 := bstep (se 1 (by rfl) ⟨1084310, by rfl⟩ : syracuseStep 1445747 = 2168621) B2168621
theorem B1445763 : Blo 1445542 1445763 := bstep (se 1 (by rfl) ⟨1084322, by rfl⟩ : syracuseStep 1445763 = 2168645) B2168645
theorem B1445779 : Blo 1445542 1445779 := bstep (se 1 (by rfl) ⟨1084334, by rfl⟩ : syracuseStep 1445779 = 2168669) B2168669
theorem B1445795 : Blo 1445542 1445795 := bstep (se 1 (by rfl) ⟨1084346, by rfl⟩ : syracuseStep 1445795 = 2168693) B2168693
theorem B1445811 : Blo 1445542 1445811 := bstep (se 1 (by rfl) ⟨1084358, by rfl⟩ : syracuseStep 1445811 = 2168717) B2168717
theorem B1445827 : Blo 1445542 1445827 := bstep (se 1 (by rfl) ⟨1084370, by rfl⟩ : syracuseStep 1445827 = 2168741) B2168741
theorem B1445843 : Blo 1445542 1445843 := bstep (se 1 (by rfl) ⟨1084382, by rfl⟩ : syracuseStep 1445843 = 2168765) B2168765
theorem B2060257 : Blo 1445542 2060257 := bstep (se 2 (by rfl) ⟨772596, by rfl⟩ : syracuseStep 2060257 = 1545193) B1545193
theorem B1445859 : Blo 1445542 1445859 := bstep (se 1 (by rfl) ⟨1084394, by rfl⟩ : syracuseStep 1445859 = 2168789) B2168789
theorem B1445875 : Blo 1445542 1445875 := bstep (se 1 (by rfl) ⟨1084406, by rfl⟩ : syracuseStep 1445875 = 2168813) B2168813
theorem B1445891 : Blo 1445542 1445891 := bstep (se 1 (by rfl) ⟨1084418, by rfl⟩ : syracuseStep 1445891 = 2168837) B2168837
theorem B1445907 : Blo 1445542 1445907 := bstep (se 1 (by rfl) ⟨1084430, by rfl⟩ : syracuseStep 1445907 = 2168861) B2168861
theorem B1445923 : Blo 1445542 1445923 := bstep (se 1 (by rfl) ⟨1084442, by rfl⟩ : syracuseStep 1445923 = 2168885) B2168885
theorem B1544227 : Blo 1445542 1544227 := bstep (se 1 (by rfl) ⟨1158170, by rfl⟩ : syracuseStep 1544227 = 2316341) B2316341
theorem B1445939 : Blo 1445542 1445939 := bstep (se 1 (by rfl) ⟨1084454, by rfl⟩ : syracuseStep 1445939 = 2168909) B2168909
theorem B31297589 : Blo 1445542 31297589 := bstep (se 5 (by rfl) ⟨1467074, by rfl⟩ : syracuseStep 31297589 = 2934149) B2934149
theorem B1445955 : Blo 1445542 1445955 := bstep (se 1 (by rfl) ⟨1084466, by rfl⟩ : syracuseStep 1445955 = 2168933) B2168933
theorem B9900101 : Blo 1445542 9900101 := bstep (se 4 (by rfl) ⟨928134, by rfl⟩ : syracuseStep 9900101 = 1856269) B1856269
theorem B6180941 : Blo 1445542 6180941 := bstep (se 3 (by rfl) ⟨1158926, by rfl⟩ : syracuseStep 6180941 = 2317853) B2317853
theorem B1445971 : Blo 1445542 1445971 := bstep (se 1 (by rfl) ⟨1084478, by rfl⟩ : syracuseStep 1445971 = 2168957) B2168957
theorem B1445987 : Blo 1445542 1445987 := bstep (se 1 (by rfl) ⟨1084490, by rfl⟩ : syracuseStep 1445987 = 2168981) B2168981
theorem B3256433 : Blo 1445542 3256433 := bstep (se 2 (by rfl) ⟨1221162, by rfl⟩ : syracuseStep 3256433 = 2442325) B2442325
theorem B1446003 : Blo 1445542 1446003 := bstep (se 1 (by rfl) ⟨1084502, by rfl⟩ : syracuseStep 1446003 = 2169005) B2169005
theorem B1446019 : Blo 1445542 1446019 := bstep (se 1 (by rfl) ⟨1084514, by rfl⟩ : syracuseStep 1446019 = 2169029) B2169029
theorem B3256451 : Blo 1445542 3256451 := bstep (se 1 (by rfl) ⟨2442338, by rfl⟩ : syracuseStep 3256451 = 4884677) B4884677
theorem B1626259 : Blo 1445542 1626259 := bstep (se 1 (by rfl) ⟨1219694, by rfl⟩ : syracuseStep 1626259 = 2439389) B2439389
theorem B1446035 : Blo 1445542 1446035 := bstep (se 1 (by rfl) ⟨1084526, by rfl⟩ : syracuseStep 1446035 = 2169053) B2169053
theorem B1446051 : Blo 1445542 1446051 := bstep (se 1 (by rfl) ⟨1084538, by rfl⟩ : syracuseStep 1446051 = 2169077) B2169077
theorem B3911843 : Blo 1445542 3911843 := bstep (se 1 (by rfl) ⟨2933882, by rfl⟩ : syracuseStep 3911843 = 5867765) B5867765
theorem B7327907 : Blo 1445542 7327907 := bstep (se 1 (by rfl) ⟨5495930, by rfl⟩ : syracuseStep 7327907 = 10991861) B10991861
theorem B4116653 : Blo 1445542 4116653 := bstep (se 3 (by rfl) ⟨771872, by rfl⟩ : syracuseStep 4116653 = 1543745) B1543745
theorem B1446067 : Blo 1445542 1446067 := bstep (se 1 (by rfl) ⟨1084550, by rfl⟩ : syracuseStep 1446067 = 2169101) B2169101
theorem B1446083 : Blo 1445542 1446083 := bstep (se 1 (by rfl) ⟨1084562, by rfl⟩ : syracuseStep 1446083 = 2169125) B2169125
theorem B4632785 : Blo 1445542 4632785 := bstep (se 2 (by rfl) ⟨1737294, by rfl⟩ : syracuseStep 4632785 = 3474589) B3474589
theorem B1446099 : Blo 1445542 1446099 := bstep (se 1 (by rfl) ⟨1084574, by rfl⟩ : syracuseStep 1446099 = 2169149) B2169149
theorem B1446115 : Blo 1445542 1446115 := bstep (se 1 (by rfl) ⟨1084586, by rfl⟩ : syracuseStep 1446115 = 2169173) B2169173
theorem B1446131 : Blo 1445542 1446131 := bstep (se 1 (by rfl) ⟨1084598, by rfl⟩ : syracuseStep 1446131 = 2169197) B2169197
theorem B1446147 : Blo 1445542 1446147 := bstep (se 1 (by rfl) ⟨1084610, by rfl⟩ : syracuseStep 1446147 = 2169221) B2169221
theorem B17150221 : Blo 1445542 17150221 := bstep (se 3 (by rfl) ⟨3215666, by rfl⟩ : syracuseStep 17150221 = 6431333) B6431333
theorem B1446163 : Blo 1445542 1446163 := bstep (se 1 (by rfl) ⟨1084622, by rfl⟩ : syracuseStep 1446163 = 2169245) B2169245
theorem B1831187 : Blo 1445542 1831187 := bstep (se 1 (by rfl) ⟨1373390, by rfl⟩ : syracuseStep 1831187 = 2746781) B2746781
theorem B1626403 : Blo 1445542 1626403 := bstep (se 1 (by rfl) ⟨1219802, by rfl⟩ : syracuseStep 1626403 = 2439605) B2439605
theorem B1446179 : Blo 1445542 1446179 := bstep (se 1 (by rfl) ⟨1084634, by rfl⟩ : syracuseStep 1446179 = 2169269) B2169269
theorem B3477809 : Blo 1445542 3477809 := bstep (se 2 (by rfl) ⟨1304178, by rfl⟩ : syracuseStep 3477809 = 2608357) B2608357
theorem B1446195 : Blo 1445542 1446195 := bstep (se 1 (by rfl) ⟨1084646, by rfl⟩ : syracuseStep 1446195 = 2169293) B2169293
theorem B1446211 : Blo 1445542 1446211 := bstep (se 1 (by rfl) ⟨1084658, by rfl⟩ : syracuseStep 1446211 = 2169317) B2169317
theorem B1446227 : Blo 1445542 1446227 := bstep (se 1 (by rfl) ⟨1084670, by rfl⟩ : syracuseStep 1446227 = 2169341) B2169341
theorem B1446243 : Blo 1445542 1446243 := bstep (se 1 (by rfl) ⟨1084682, by rfl⟩ : syracuseStep 1446243 = 2169365) B2169365
theorem B4116845 : Blo 1445542 4116845 := bstep (se 3 (by rfl) ⟨771908, by rfl⟩ : syracuseStep 4116845 = 1543817) B1543817
theorem B1446259 : Blo 1445542 1446259 := bstep (se 1 (by rfl) ⟨1084694, by rfl⟩ : syracuseStep 1446259 = 2169389) B2169389
theorem B1446275 : Blo 1445542 1446275 := bstep (se 1 (by rfl) ⟨1084706, by rfl⟩ : syracuseStep 1446275 = 2169413) B2169413
theorem B4878737 : Blo 1445542 4878737 := bstep (se 2 (by rfl) ⟨1829526, by rfl⟩ : syracuseStep 4878737 = 3659053) B3659053
theorem B4632977 : Blo 1445542 4632977 := bstep (se 2 (by rfl) ⟨1737366, by rfl⟩ : syracuseStep 4632977 = 3474733) B3474733
theorem B1446291 : Blo 1445542 1446291 := bstep (se 1 (by rfl) ⟨1084718, by rfl⟩ : syracuseStep 1446291 = 2169437) B2169437
theorem B3256721 : Blo 1445542 3256721 := bstep (se 2 (by rfl) ⟨1221270, by rfl⟩ : syracuseStep 3256721 = 2442541) B2442541
theorem B1446307 : Blo 1445542 1446307 := bstep (se 1 (by rfl) ⟨1084730, by rfl⟩ : syracuseStep 1446307 = 2169461) B2169461
theorem B3256739 : Blo 1445542 3256739 := bstep (se 1 (by rfl) ⟨2442554, by rfl⟩ : syracuseStep 3256739 = 4885109) B4885109
theorem B3912113 : Blo 1445542 3912113 := bstep (se 2 (by rfl) ⟨1467042, by rfl⟩ : syracuseStep 3912113 = 2934085) B2934085
theorem B1626547 : Blo 1445542 1626547 := bstep (se 1 (by rfl) ⟨1219910, by rfl⟩ : syracuseStep 1626547 = 2439821) B2439821
theorem B1446323 : Blo 1445542 1446323 := bstep (se 1 (by rfl) ⟨1084742, by rfl⟩ : syracuseStep 1446323 = 2169485) B2169485
theorem B1446339 : Blo 1445542 1446339 := bstep (se 1 (by rfl) ⟨1084754, by rfl⟩ : syracuseStep 1446339 = 2169509) B2169509
theorem B5493197 : Blo 1445542 5493197 := bstep (se 3 (by rfl) ⟨1029974, by rfl⟩ : syracuseStep 5493197 = 2059949) B2059949
theorem B1446355 : Blo 1445542 1446355 := bstep (se 1 (by rfl) ⟨1084766, by rfl⟩ : syracuseStep 1446355 = 2169533) B2169533
theorem B1446371 : Blo 1445542 1446371 := bstep (se 1 (by rfl) ⟨1084778, by rfl⟩ : syracuseStep 1446371 = 2169557) B2169557
theorem B1446387 : Blo 1445542 1446387 := bstep (se 1 (by rfl) ⟨1084790, by rfl⟩ : syracuseStep 1446387 = 2169581) B2169581
theorem B1446403 : Blo 1445542 1446403 := bstep (se 1 (by rfl) ⟨1084802, by rfl⟩ : syracuseStep 1446403 = 2169605) B2169605
theorem B1446419 : Blo 1445542 1446419 := bstep (se 1 (by rfl) ⟨1084814, by rfl⟩ : syracuseStep 1446419 = 2169629) B2169629
theorem B1446435 : Blo 1445542 1446435 := bstep (se 1 (by rfl) ⟨1084826, by rfl⟩ : syracuseStep 1446435 = 2169653) B2169653
theorem B2060849 : Blo 1445542 2060849 := bstep (se 2 (by rfl) ⟨772818, by rfl⟩ : syracuseStep 2060849 = 1545637) B1545637
theorem B1446451 : Blo 1445542 1446451 := bstep (se 1 (by rfl) ⟨1084838, by rfl⟩ : syracuseStep 1446451 = 2169677) B2169677
theorem B1626691 : Blo 1445542 1626691 := bstep (se 1 (by rfl) ⟨1220018, by rfl⟩ : syracuseStep 1626691 = 2440037) B2440037
theorem B1446467 : Blo 1445542 1446467 := bstep (se 1 (by rfl) ⟨1084850, by rfl⟩ : syracuseStep 1446467 = 2169701) B2169701
theorem B1446483 : Blo 1445542 1446483 := bstep (se 1 (by rfl) ⟨1084862, by rfl⟩ : syracuseStep 1446483 = 2169725) B2169725
theorem B1446499 : Blo 1445542 1446499 := bstep (se 1 (by rfl) ⟨1084874, by rfl⟩ : syracuseStep 1446499 = 2169749) B2169749
theorem B9269873 : Blo 1445542 9269873 := bstep (se 2 (by rfl) ⟨3476202, by rfl⟩ : syracuseStep 9269873 = 6952405) B6952405
theorem B1446515 : Blo 1445542 1446515 := bstep (se 1 (by rfl) ⟨1084886, by rfl⟩ : syracuseStep 1446515 = 2169773) B2169773
theorem B1446531 : Blo 1445542 1446531 := bstep (se 1 (by rfl) ⟨1084898, by rfl⟩ : syracuseStep 1446531 = 2169797) B2169797
theorem B1446547 : Blo 1445542 1446547 := bstep (se 1 (by rfl) ⟨1084910, by rfl⟩ : syracuseStep 1446547 = 2169821) B2169821
theorem B1446563 : Blo 1445542 1446563 := bstep (se 1 (by rfl) ⟨1084922, by rfl⟩ : syracuseStep 1446563 = 2169845) B2169845
theorem B1446579 : Blo 1445542 1446579 := bstep (se 1 (by rfl) ⟨1084934, by rfl⟩ : syracuseStep 1446579 = 2169869) B2169869
theorem B1446595 : Blo 1445542 1446595 := bstep (se 1 (by rfl) ⟨1084946, by rfl⟩ : syracuseStep 1446595 = 2169893) B2169893
theorem B1626835 : Blo 1445542 1626835 := bstep (se 1 (by rfl) ⟨1220126, by rfl⟩ : syracuseStep 1626835 = 2440253) B2440253
theorem B1446611 : Blo 1445542 1446611 := bstep (se 1 (by rfl) ⟨1084958, by rfl⟩ : syracuseStep 1446611 = 2169917) B2169917
theorem B1446627 : Blo 1445542 1446627 := bstep (se 1 (by rfl) ⟨1084970, by rfl⟩ : syracuseStep 1446627 = 2169941) B2169941
theorem B1446643 : Blo 1445542 1446643 := bstep (se 1 (by rfl) ⟨1084982, by rfl⟩ : syracuseStep 1446643 = 2169965) B2169965
theorem B1446659 : Blo 1445542 1446659 := bstep (se 1 (by rfl) ⟨1084994, by rfl⟩ : syracuseStep 1446659 = 2169989) B2169989
theorem B1446675 : Blo 1445542 1446675 := bstep (se 1 (by rfl) ⟨1085006, by rfl⟩ : syracuseStep 1446675 = 2170013) B2170013
theorem B1446691 : Blo 1445542 1446691 := bstep (se 1 (by rfl) ⟨1085018, by rfl⟩ : syracuseStep 1446691 = 2170037) B2170037
theorem B1446707 : Blo 1445542 1446707 := bstep (se 1 (by rfl) ⟨1085030, by rfl⟩ : syracuseStep 1446707 = 2170061) B2170061
theorem B1446723 : Blo 1445542 1446723 := bstep (se 1 (by rfl) ⟨1085042, by rfl⟩ : syracuseStep 1446723 = 2170085) B2170085
theorem B1446739 : Blo 1445542 1446739 := bstep (se 1 (by rfl) ⟨1085054, by rfl⟩ : syracuseStep 1446739 = 2170109) B2170109
theorem B1626979 : Blo 1445542 1626979 := bstep (se 1 (by rfl) ⟨1220234, by rfl⟩ : syracuseStep 1626979 = 2440469) B2440469
theorem B1446755 : Blo 1445542 1446755 := bstep (se 1 (by rfl) ⟨1085066, by rfl⟩ : syracuseStep 1446755 = 2170133) B2170133
theorem B1446771 : Blo 1445542 1446771 := bstep (se 1 (by rfl) ⟨1085078, by rfl⟩ : syracuseStep 1446771 = 2170157) B2170157
theorem B1446787 : Blo 1445542 1446787 := bstep (se 1 (by rfl) ⟨1085090, by rfl⟩ : syracuseStep 1446787 = 2170181) B2170181
theorem B1446803 : Blo 1445542 1446803 := bstep (se 1 (by rfl) ⟨1085102, by rfl⟩ : syracuseStep 1446803 = 2170205) B2170205
theorem B3298211 : Blo 1445542 3298211 := bstep (se 1 (by rfl) ⟨2473658, by rfl⟩ : syracuseStep 3298211 = 4947317) B4947317
theorem B1446819 : Blo 1445542 1446819 := bstep (se 1 (by rfl) ⟨1085114, by rfl⟩ : syracuseStep 1446819 = 2170229) B2170229
theorem B4879277 : Blo 1445542 4879277 := bstep (se 3 (by rfl) ⟨914864, by rfl⟩ : syracuseStep 4879277 = 1829729) B1829729
theorem B1446835 : Blo 1445542 1446835 := bstep (se 1 (by rfl) ⟨1085126, by rfl⟩ : syracuseStep 1446835 = 2170253) B2170253
theorem B1446851 : Blo 1445542 1446851 := bstep (se 1 (by rfl) ⟨1085138, by rfl⟩ : syracuseStep 1446851 = 2170277) B2170277
theorem B1446867 : Blo 1445542 1446867 := bstep (se 1 (by rfl) ⟨1085150, by rfl⟩ : syracuseStep 1446867 = 2170301) B2170301
theorem B1831891 : Blo 1445542 1831891 := bstep (se 1 (by rfl) ⟨1373918, by rfl⟩ : syracuseStep 1831891 = 2747837) B2747837
theorem B4879331 : Blo 1445542 4879331 := bstep (se 1 (by rfl) ⟨3659498, by rfl⟩ : syracuseStep 4879331 = 7318997) B7318997
theorem B1446883 : Blo 1445542 1446883 := bstep (se 1 (by rfl) ⟨1085162, by rfl⟩ : syracuseStep 1446883 = 2170325) B2170325
theorem B16471025 : Blo 1445542 16471025 := bstep (se 2 (by rfl) ⟨6176634, by rfl⟩ : syracuseStep 16471025 = 12353269) B12353269
theorem B1627123 : Blo 1445542 1627123 := bstep (se 1 (by rfl) ⟨1220342, by rfl⟩ : syracuseStep 1627123 = 2440685) B2440685
theorem B1446899 : Blo 1445542 1446899 := bstep (se 1 (by rfl) ⟨1085174, by rfl⟩ : syracuseStep 1446899 = 2170349) B2170349
theorem B1446915 : Blo 1445542 1446915 := bstep (se 1 (by rfl) ⟨1085186, by rfl⟩ : syracuseStep 1446915 = 2170373) B2170373
theorem B4174865 : Blo 1445542 4174865 := bstep (se 2 (by rfl) ⟨1565574, by rfl⟩ : syracuseStep 4174865 = 3131149) B3131149
theorem B1446931 : Blo 1445542 1446931 := bstep (se 1 (by rfl) ⟨1085198, by rfl⟩ : syracuseStep 1446931 = 2170397) B2170397
theorem B1446947 : Blo 1445542 1446947 := bstep (se 1 (by rfl) ⟨1085210, by rfl⟩ : syracuseStep 1446947 = 2170421) B2170421
theorem B1446963 : Blo 1445542 1446963 := bstep (se 1 (by rfl) ⟨1085222, by rfl⟩ : syracuseStep 1446963 = 2170445) B2170445
theorem B1831987 : Blo 1445542 1831987 := bstep (se 1 (by rfl) ⟨1373990, by rfl⟩ : syracuseStep 1831987 = 2747981) B2747981
theorem B1446979 : Blo 1445542 1446979 := bstep (se 1 (by rfl) ⟨1085234, by rfl⟩ : syracuseStep 1446979 = 2170469) B2170469
theorem B1446995 : Blo 1445542 1446995 := bstep (se 1 (by rfl) ⟨1085246, by rfl⟩ : syracuseStep 1446995 = 2170493) B2170493
theorem B1447011 : Blo 1445542 1447011 := bstep (se 1 (by rfl) ⟨1085258, by rfl⟩ : syracuseStep 1447011 = 2170517) B2170517
theorem B8795249 : Blo 1445542 8795249 := bstep (se 2 (by rfl) ⟨3298218, by rfl⟩ : syracuseStep 8795249 = 6596437) B6596437
theorem B1447027 : Blo 1445542 1447027 := bstep (se 1 (by rfl) ⟨1085270, by rfl⟩ : syracuseStep 1447027 = 2170541) B2170541
theorem B1627267 : Blo 1445542 1627267 := bstep (se 1 (by rfl) ⟨1220450, by rfl⟩ : syracuseStep 1627267 = 2440901) B2440901
theorem B1447043 : Blo 1445542 1447043 := bstep (se 1 (by rfl) ⟨1085282, by rfl⟩ : syracuseStep 1447043 = 2170565) B2170565
theorem B5215373 : Blo 1445542 5215373 := bstep (se 3 (by rfl) ⟨977882, by rfl⟩ : syracuseStep 5215373 = 1955765) B1955765
theorem B1447059 : Blo 1445542 1447059 := bstep (se 1 (by rfl) ⟨1085294, by rfl⟩ : syracuseStep 1447059 = 2170589) B2170589
theorem B1447075 : Blo 1445542 1447075 := bstep (se 1 (by rfl) ⟨1085306, by rfl⟩ : syracuseStep 1447075 = 2170613) B2170613
theorem B1447091 : Blo 1445542 1447091 := bstep (se 1 (by rfl) ⟨1085318, by rfl⟩ : syracuseStep 1447091 = 2170637) B2170637
theorem B1447107 : Blo 1445542 1447107 := bstep (se 1 (by rfl) ⟨1085330, by rfl⟩ : syracuseStep 1447107 = 2170661) B2170661
theorem B1447123 : Blo 1445542 1447123 := bstep (se 1 (by rfl) ⟨1085342, by rfl⟩ : syracuseStep 1447123 = 2170685) B2170685
theorem B10982627 : Blo 1445542 10982627 := bstep (se 1 (by rfl) ⟨8236970, by rfl⟩ : syracuseStep 10982627 = 16473941) B16473941
theorem B1447139 : Blo 1445542 1447139 := bstep (se 1 (by rfl) ⟨1085354, by rfl⟩ : syracuseStep 1447139 = 2170709) B2170709
theorem B4879601 : Blo 1445542 4879601 := bstep (se 2 (by rfl) ⟨1829850, by rfl⟩ : syracuseStep 4879601 = 3659701) B3659701
theorem B1447155 : Blo 1445542 1447155 := bstep (se 1 (by rfl) ⟨1085366, by rfl⟩ : syracuseStep 1447155 = 2170733) B2170733
theorem B1447171 : Blo 1445542 1447171 := bstep (se 1 (by rfl) ⟨1085378, by rfl⟩ : syracuseStep 1447171 = 2170757) B2170757
theorem B1627411 : Blo 1445542 1627411 := bstep (se 1 (by rfl) ⟨1220558, by rfl⟩ : syracuseStep 1627411 = 2441117) B2441117
theorem B1447187 : Blo 1445542 1447187 := bstep (se 1 (by rfl) ⟨1085390, by rfl⟩ : syracuseStep 1447187 = 2170781) B2170781
theorem B1447203 : Blo 1445542 1447203 := bstep (se 1 (by rfl) ⟨1085402, by rfl⟩ : syracuseStep 1447203 = 2170805) B2170805
theorem B2970929 : Blo 1445542 2970929 := bstep (se 2 (by rfl) ⟨1114098, by rfl⟩ : syracuseStep 2970929 = 2228197) B2228197
theorem B7419185 : Blo 1445542 7419185 := bstep (se 2 (by rfl) ⟨2782194, by rfl⟩ : syracuseStep 7419185 = 5564389) B5564389
theorem B1447219 : Blo 1445542 1447219 := bstep (se 1 (by rfl) ⟨1085414, by rfl⟩ : syracuseStep 1447219 = 2170829) B2170829
theorem B2315585 : Blo 1445542 2315585 := bstep (se 2 (by rfl) ⟨868344, by rfl⟩ : syracuseStep 2315585 = 1736689) B1736689
theorem B1447235 : Blo 1445542 1447235 := bstep (se 1 (by rfl) ⟨1085426, by rfl⟩ : syracuseStep 1447235 = 2170853) B2170853
theorem B4117837 : Blo 1445542 4117837 := bstep (se 3 (by rfl) ⟨772094, by rfl⟩ : syracuseStep 4117837 = 1544189) B1544189
theorem B1447251 : Blo 1445542 1447251 := bstep (se 1 (by rfl) ⟨1085438, by rfl⟩ : syracuseStep 1447251 = 2170877) B2170877
theorem B5862755 : Blo 1445542 5862755 := bstep (se 1 (by rfl) ⟨4397066, by rfl⟩ : syracuseStep 5862755 = 8794133) B8794133
theorem B1447267 : Blo 1445542 1447267 := bstep (se 1 (by rfl) ⟨1085450, by rfl⟩ : syracuseStep 1447267 = 2170901) B2170901
theorem B1447283 : Blo 1445542 1447283 := bstep (se 1 (by rfl) ⟨1085462, by rfl⟩ : syracuseStep 1447283 = 2170925) B2170925
theorem B1447299 : Blo 1445542 1447299 := bstep (se 1 (by rfl) ⟨1085474, by rfl⟩ : syracuseStep 1447299 = 2170949) B2170949
theorem B1447315 : Blo 1445542 1447315 := bstep (se 1 (by rfl) ⟨1085486, by rfl⟩ : syracuseStep 1447315 = 2170973) B2170973
theorem B1627555 : Blo 1445542 1627555 := bstep (se 1 (by rfl) ⟨1220666, by rfl⟩ : syracuseStep 1627555 = 2441333) B2441333
theorem B1447331 : Blo 1445542 1447331 := bstep (se 1 (by rfl) ⟨1085498, by rfl⟩ : syracuseStep 1447331 = 2170997) B2170997
theorem B1447347 : Blo 1445542 1447347 := bstep (se 1 (by rfl) ⟨1085510, by rfl⟩ : syracuseStep 1447347 = 2171021) B2171021
theorem B1447363 : Blo 1445542 1447363 := bstep (se 1 (by rfl) ⟨1085522, by rfl⟩ : syracuseStep 1447363 = 2171045) B2171045
theorem B1447379 : Blo 1445542 1447379 := bstep (se 1 (by rfl) ⟨1085534, by rfl⟩ : syracuseStep 1447379 = 2171069) B2171069
theorem B1447395 : Blo 1445542 1447395 := bstep (se 1 (by rfl) ⟨1085546, by rfl⟩ : syracuseStep 1447395 = 2171093) B2171093
theorem B1447411 : Blo 1445542 1447411 := bstep (se 1 (by rfl) ⟨1085558, by rfl⟩ : syracuseStep 1447411 = 2171117) B2171117
theorem B2168321 : Blo 1445542 2168321 := bstep (se 2 (by rfl) ⟨813120, by rfl⟩ : syracuseStep 2168321 = 1626241) B1626241
theorem B1447427 : Blo 1445542 1447427 := bstep (se 1 (by rfl) ⟨1085570, by rfl⟩ : syracuseStep 1447427 = 2171141) B2171141
theorem B2168339 : Blo 1445542 2168339 := bstep (se 1 (by rfl) ⟨1626254, by rfl⟩ : syracuseStep 2168339 = 3252509) B3252509
theorem B1447443 : Blo 1445542 1447443 := bstep (se 1 (by rfl) ⟨1085582, by rfl⟩ : syracuseStep 1447443 = 2171165) B2171165
theorem B1447459 : Blo 1445542 1447459 := bstep (se 1 (by rfl) ⟨1085594, by rfl⟩ : syracuseStep 1447459 = 2171189) B2171189
theorem B2168369 : Blo 1445542 2168369 := bstep (se 2 (by rfl) ⟨813138, by rfl⟩ : syracuseStep 2168369 = 1626277) B1626277
theorem B1627699 : Blo 1445542 1627699 := bstep (se 1 (by rfl) ⟨1220774, by rfl⟩ : syracuseStep 1627699 = 2441549) B2441549
theorem B1447475 : Blo 1445542 1447475 := bstep (se 1 (by rfl) ⟨1085606, by rfl⟩ : syracuseStep 1447475 = 2171213) B2171213
theorem B2168387 : Blo 1445542 2168387 := bstep (se 1 (by rfl) ⟨1626290, by rfl⟩ : syracuseStep 2168387 = 3252581) B3252581
theorem B1447491 : Blo 1445542 1447491 := bstep (se 1 (by rfl) ⟨1085618, by rfl⟩ : syracuseStep 1447491 = 2171237) B2171237
theorem B1447507 : Blo 1445542 1447507 := bstep (se 1 (by rfl) ⟨1085630, by rfl⟩ : syracuseStep 1447507 = 2171261) B2171261
theorem B2168417 : Blo 1445542 2168417 := bstep (se 2 (by rfl) ⟨813156, by rfl⟩ : syracuseStep 2168417 = 1626313) B1626313
theorem B1447523 : Blo 1445542 1447523 := bstep (se 1 (by rfl) ⟨1085642, by rfl⟩ : syracuseStep 1447523 = 2171285) B2171285
theorem B3659377 : Blo 1445542 3659377 := bstep (se 2 (by rfl) ⟨1372266, by rfl⟩ : syracuseStep 3659377 = 2744533) B2744533
theorem B6182513 : Blo 1445542 6182513 := bstep (se 2 (by rfl) ⟨2318442, by rfl⟩ : syracuseStep 6182513 = 4636885) B4636885
theorem B2168435 : Blo 1445542 2168435 := bstep (se 1 (by rfl) ⟨1626326, by rfl⟩ : syracuseStep 2168435 = 3252653) B3252653
theorem B1447539 : Blo 1445542 1447539 := bstep (se 1 (by rfl) ⟨1085654, by rfl⟩ : syracuseStep 1447539 = 2171309) B2171309
theorem B2168465 : Blo 1445542 2168465 := bstep (se 2 (by rfl) ⟨813174, by rfl⟩ : syracuseStep 2168465 = 1626349) B1626349
theorem B2168483 : Blo 1445542 2168483 := bstep (se 1 (by rfl) ⟨1626362, by rfl⟩ : syracuseStep 2168483 = 3252725) B3252725
theorem B7321265 : Blo 1445542 7321265 := bstep (se 2 (by rfl) ⟨2745474, by rfl⟩ : syracuseStep 7321265 = 5490949) B5490949
theorem B2168513 : Blo 1445542 2168513 := bstep (se 2 (by rfl) ⟨813192, by rfl⟩ : syracuseStep 2168513 = 1626385) B1626385
theorem B1627843 : Blo 1445542 1627843 := bstep (se 1 (by rfl) ⟨1220882, by rfl⟩ : syracuseStep 1627843 = 2441765) B2441765
theorem B2168531 : Blo 1445542 2168531 := bstep (se 1 (by rfl) ⟨1626398, by rfl⟩ : syracuseStep 2168531 = 3252797) B3252797
theorem B2168561 : Blo 1445542 2168561 := bstep (se 2 (by rfl) ⟨813210, by rfl⟩ : syracuseStep 2168561 = 1626421) B1626421
theorem B2168579 : Blo 1445542 2168579 := bstep (se 1 (by rfl) ⟨1626434, by rfl⟩ : syracuseStep 2168579 = 3252869) B3252869
theorem B4880141 : Blo 1445542 4880141 := bstep (se 3 (by rfl) ⟨915026, by rfl⟩ : syracuseStep 4880141 = 1830053) B1830053
theorem B1955603 : Blo 1445542 1955603 := bstep (se 1 (by rfl) ⟨1466702, by rfl⟩ : syracuseStep 1955603 = 2933405) B2933405
theorem B2168609 : Blo 1445542 2168609 := bstep (se 2 (by rfl) ⟨813228, by rfl⟩ : syracuseStep 2168609 = 1626457) B1626457
theorem B2168627 : Blo 1445542 2168627 := bstep (se 1 (by rfl) ⟨1626470, by rfl⟩ : syracuseStep 2168627 = 3252941) B3252941
theorem B4880195 : Blo 1445542 4880195 := bstep (se 1 (by rfl) ⟨3660146, by rfl⟩ : syracuseStep 4880195 = 7320293) B7320293
theorem B2168657 : Blo 1445542 2168657 := bstep (se 2 (by rfl) ⟨813246, by rfl⟩ : syracuseStep 2168657 = 1626493) B1626493
theorem B1627987 : Blo 1445542 1627987 := bstep (se 1 (by rfl) ⟨1220990, by rfl⟩ : syracuseStep 1627987 = 2441981) B2441981
theorem B2168675 : Blo 1445542 2168675 := bstep (se 1 (by rfl) ⟨1626506, by rfl⟩ : syracuseStep 2168675 = 3253013) B3253013
theorem B2168705 : Blo 1445542 2168705 := bstep (se 2 (by rfl) ⟨813264, by rfl⟩ : syracuseStep 2168705 = 1626529) B1626529
theorem B3659651 : Blo 1445542 3659651 := bstep (se 1 (by rfl) ⟨2744738, by rfl⟩ : syracuseStep 3659651 = 5489477) B5489477
theorem B4700045 : Blo 1445542 4700045 := bstep (se 3 (by rfl) ⟨881258, by rfl⟩ : syracuseStep 4700045 = 1762517) B1762517
theorem B2168723 : Blo 1445542 2168723 := bstep (se 1 (by rfl) ⟨1626542, by rfl⟩ : syracuseStep 2168723 = 3253085) B3253085
theorem B2168753 : Blo 1445542 2168753 := bstep (se 2 (by rfl) ⟨813282, by rfl⟩ : syracuseStep 2168753 = 1626565) B1626565
theorem B2168771 : Blo 1445542 2168771 := bstep (se 1 (by rfl) ⟨1626578, by rfl⟩ : syracuseStep 2168771 = 3253157) B3253157
theorem B2168801 : Blo 1445542 2168801 := bstep (se 2 (by rfl) ⟨813300, by rfl⟩ : syracuseStep 2168801 = 1626601) B1626601
theorem B1628131 : Blo 1445542 1628131 := bstep (se 1 (by rfl) ⟨1221098, by rfl⟩ : syracuseStep 1628131 = 2442197) B2442197
theorem B7043057 : Blo 1445542 7043057 := bstep (se 2 (by rfl) ⟨2641146, by rfl⟩ : syracuseStep 7043057 = 5282293) B5282293
theorem B2168819 : Blo 1445542 2168819 := bstep (se 1 (by rfl) ⟨1626614, by rfl⟩ : syracuseStep 2168819 = 3253229) B3253229
theorem B20051981 : Blo 1445542 20051981 := bstep (se 3 (by rfl) ⟨3759746, by rfl⟩ : syracuseStep 20051981 = 7519493) B7519493
theorem B2168849 : Blo 1445542 2168849 := bstep (se 2 (by rfl) ⟨813318, by rfl⟩ : syracuseStep 2168849 = 1626637) B1626637
theorem B2168867 : Blo 1445542 2168867 := bstep (se 1 (by rfl) ⟨1626650, by rfl⟩ : syracuseStep 2168867 = 3253301) B3253301
theorem B2168897 : Blo 1445542 2168897 := bstep (se 2 (by rfl) ⟨813336, by rfl⟩ : syracuseStep 2168897 = 1626673) B1626673
theorem B3659843 : Blo 1445542 3659843 := bstep (se 1 (by rfl) ⟨2744882, by rfl⟩ : syracuseStep 3659843 = 5489765) B5489765
theorem B3962947 : Blo 1445542 3962947 := bstep (se 1 (by rfl) ⟨2972210, by rfl⟩ : syracuseStep 3962947 = 5944421) B5944421
theorem B4880465 : Blo 1445542 4880465 := bstep (se 2 (by rfl) ⟨1830174, by rfl⟩ : syracuseStep 4880465 = 3660349) B3660349
theorem B2168915 : Blo 1445542 2168915 := bstep (se 1 (by rfl) ⟨1626686, by rfl⟩ : syracuseStep 2168915 = 3253373) B3253373
theorem B2168945 : Blo 1445542 2168945 := bstep (se 2 (by rfl) ⟨813354, by rfl⟩ : syracuseStep 2168945 = 1626709) B1626709
theorem B1628275 : Blo 1445542 1628275 := bstep (se 1 (by rfl) ⟨1221206, by rfl⟩ : syracuseStep 1628275 = 2442413) B2442413
theorem B2168963 : Blo 1445542 2168963 := bstep (se 1 (by rfl) ⟨1626722, by rfl⟩ : syracuseStep 2168963 = 3253445) B3253445
theorem B12351629 : Blo 1445542 12351629 := bstep (se 3 (by rfl) ⟨2315930, by rfl⟩ : syracuseStep 12351629 = 4631861) B4631861
theorem B2168993 : Blo 1445542 2168993 := bstep (se 2 (by rfl) ⟨813372, by rfl⟩ : syracuseStep 2168993 = 1626745) B1626745
theorem B2169011 : Blo 1445542 2169011 := bstep (se 1 (by rfl) ⟨1626758, by rfl⟩ : syracuseStep 2169011 = 3253517) B3253517
theorem B2169041 : Blo 1445542 2169041 := bstep (se 2 (by rfl) ⟨813390, by rfl⟩ : syracuseStep 2169041 = 1626781) B1626781
theorem B2169059 : Blo 1445542 2169059 := bstep (se 1 (by rfl) ⟨1626794, by rfl⟩ : syracuseStep 2169059 = 3253589) B3253589
theorem B2439409 : Blo 1445542 2439409 := bstep (se 2 (by rfl) ⟨914778, by rfl⟩ : syracuseStep 2439409 = 1829557) B1829557
theorem B2169089 : Blo 1445542 2169089 := bstep (se 2 (by rfl) ⟨813408, by rfl⟩ : syracuseStep 2169089 = 1626817) B1626817
theorem B1628419 : Blo 1445542 1628419 := bstep (se 1 (by rfl) ⟨1221314, by rfl⟩ : syracuseStep 1628419 = 2442629) B2442629
theorem B2439443 : Blo 1445542 2439443 := bstep (se 1 (by rfl) ⟨1829582, by rfl⟩ : syracuseStep 2439443 = 3659165) B3659165
theorem B2169107 : Blo 1445542 2169107 := bstep (se 1 (by rfl) ⟨1626830, by rfl⟩ : syracuseStep 2169107 = 3253661) B3253661
theorem B4397357 : Blo 1445542 4397357 := bstep (se 3 (by rfl) ⟨824504, by rfl⟩ : syracuseStep 4397357 = 1649009) B1649009
theorem B2169137 : Blo 1445542 2169137 := bstep (se 2 (by rfl) ⟨813426, by rfl⟩ : syracuseStep 2169137 = 1626853) B1626853
theorem B2169155 : Blo 1445542 2169155 := bstep (se 1 (by rfl) ⟨1626866, by rfl⟩ : syracuseStep 2169155 = 3253733) B3253733
theorem B5863757 : Blo 1445542 5863757 := bstep (se 3 (by rfl) ⟨1099454, by rfl⟩ : syracuseStep 5863757 = 2198909) B2198909
theorem B2169185 : Blo 1445542 2169185 := bstep (se 2 (by rfl) ⟨813444, by rfl⟩ : syracuseStep 2169185 = 1626889) B1626889
theorem B2169203 : Blo 1445542 2169203 := bstep (se 1 (by rfl) ⟨1626902, by rfl⟩ : syracuseStep 2169203 = 3253805) B3253805
theorem B2169233 : Blo 1445542 2169233 := bstep (se 2 (by rfl) ⟨813462, by rfl⟩ : syracuseStep 2169233 = 1626925) B1626925
theorem B2439571 : Blo 1445542 2439571 := bstep (se 1 (by rfl) ⟨1829678, by rfl⟩ : syracuseStep 2439571 = 3659357) B3659357
theorem B2169251 : Blo 1445542 2169251 := bstep (se 1 (by rfl) ⟨1626938, by rfl⟩ : syracuseStep 2169251 = 3253877) B3253877
theorem B2169281 : Blo 1445542 2169281 := bstep (se 2 (by rfl) ⟨813480, by rfl⟩ : syracuseStep 2169281 = 1626961) B1626961
theorem B2169299 : Blo 1445542 2169299 := bstep (se 1 (by rfl) ⟨1626974, by rfl⟩ : syracuseStep 2169299 = 3253949) B3253949
theorem B2169329 : Blo 1445542 2169329 := bstep (se 2 (by rfl) ⟨813498, by rfl⟩ : syracuseStep 2169329 = 1626997) B1626997
theorem B2169347 : Blo 1445542 2169347 := bstep (se 1 (by rfl) ⟨1627010, by rfl⟩ : syracuseStep 2169347 = 3254021) B3254021
theorem B5495309 : Blo 1445542 5495309 := bstep (se 3 (by rfl) ⟨1030370, by rfl⟩ : syracuseStep 5495309 = 2060741) B2060741
theorem B2439713 : Blo 1445542 2439713 := bstep (se 2 (by rfl) ⟨914892, by rfl⟩ : syracuseStep 2439713 = 1829785) B1829785
theorem B2169377 : Blo 1445542 2169377 := bstep (se 2 (by rfl) ⟨813516, by rfl⟩ : syracuseStep 2169377 = 1627033) B1627033
theorem B6953521 : Blo 1445542 6953521 := bstep (se 2 (by rfl) ⟨2607570, by rfl⟩ : syracuseStep 6953521 = 5215141) B5215141
theorem B2169395 : Blo 1445542 2169395 := bstep (se 1 (by rfl) ⟨1627046, by rfl⟩ : syracuseStep 2169395 = 3254093) B3254093
theorem B125065781 : Blo 1445542 125065781 := bstep (se 5 (by rfl) ⟨5862458, by rfl⟩ : syracuseStep 125065781 = 11724917) B11724917
theorem B2169425 : Blo 1445542 2169425 := bstep (se 2 (by rfl) ⟨813534, by rfl⟩ : syracuseStep 2169425 = 1627069) B1627069
theorem B2169443 : Blo 1445542 2169443 := bstep (se 1 (by rfl) ⟨1627082, by rfl⟩ : syracuseStep 2169443 = 3254165) B3254165
theorem B2316899 : Blo 1445542 2316899 := bstep (se 1 (by rfl) ⟨1737674, by rfl⟩ : syracuseStep 2316899 = 3475349) B3475349
theorem B4881005 : Blo 1445542 4881005 := bstep (se 3 (by rfl) ⟨915188, by rfl⟩ : syracuseStep 4881005 = 1830377) B1830377
theorem B4635245 : Blo 1445542 4635245 := bstep (se 3 (by rfl) ⟨869108, by rfl⟩ : syracuseStep 4635245 = 1738217) B1738217
theorem B2169473 : Blo 1445542 2169473 := bstep (se 2 (by rfl) ⟨813552, by rfl⟩ : syracuseStep 2169473 = 1627105) B1627105
theorem B2169491 : Blo 1445542 2169491 := bstep (se 1 (by rfl) ⟨1627118, by rfl⟩ : syracuseStep 2169491 = 3254237) B3254237
theorem B2439841 : Blo 1445542 2439841 := bstep (se 2 (by rfl) ⟨914940, by rfl⟩ : syracuseStep 2439841 = 1829881) B1829881
theorem B4881059 : Blo 1445542 4881059 := bstep (se 1 (by rfl) ⟨3660794, by rfl⟩ : syracuseStep 4881059 = 7321589) B7321589
theorem B6953635 : Blo 1445542 6953635 := bstep (se 1 (by rfl) ⟨5215226, by rfl⟩ : syracuseStep 6953635 = 10430453) B10430453
theorem B2169521 : Blo 1445542 2169521 := bstep (se 2 (by rfl) ⟨813570, by rfl⟩ : syracuseStep 2169521 = 1627141) B1627141
theorem B2439875 : Blo 1445542 2439875 := bstep (se 1 (by rfl) ⟨1829906, by rfl⟩ : syracuseStep 2439875 = 3659813) B3659813
theorem B2169539 : Blo 1445542 2169539 := bstep (se 1 (by rfl) ⟨1627154, by rfl⟩ : syracuseStep 2169539 = 3254309) B3254309
theorem B4397773 : Blo 1445542 4397773 := bstep (se 3 (by rfl) ⟨824582, by rfl⟩ : syracuseStep 4397773 = 1649165) B1649165
theorem B2169569 : Blo 1445542 2169569 := bstep (se 2 (by rfl) ⟨813588, by rfl⟩ : syracuseStep 2169569 = 1627177) B1627177
theorem B2169587 : Blo 1445542 2169587 := bstep (se 1 (by rfl) ⟨1627190, by rfl⟩ : syracuseStep 2169587 = 3254381) B3254381
theorem B2169617 : Blo 1445542 2169617 := bstep (se 2 (by rfl) ⟨813606, by rfl⟩ : syracuseStep 2169617 = 1627213) B1627213
theorem B2169635 : Blo 1445542 2169635 := bstep (se 1 (by rfl) ⟨1627226, by rfl⟩ : syracuseStep 2169635 = 3254453) B3254453
theorem B2169665 : Blo 1445542 2169665 := bstep (se 2 (by rfl) ⟨813624, by rfl⟩ : syracuseStep 2169665 = 1627249) B1627249
theorem B2440003 : Blo 1445542 2440003 := bstep (se 1 (by rfl) ⟨1830002, by rfl⟩ : syracuseStep 2440003 = 3660005) B3660005
theorem B2317123 : Blo 1445542 2317123 := bstep (se 1 (by rfl) ⟨1737842, by rfl⟩ : syracuseStep 2317123 = 3475685) B3475685
theorem B2472787 : Blo 1445542 2472787 := bstep (se 1 (by rfl) ⟨1854590, by rfl⟩ : syracuseStep 2472787 = 3709181) B3709181
theorem B2169683 : Blo 1445542 2169683 := bstep (se 1 (by rfl) ⟨1627262, by rfl⟩ : syracuseStep 2169683 = 3254525) B3254525
theorem B2169713 : Blo 1445542 2169713 := bstep (se 2 (by rfl) ⟨813642, by rfl⟩ : syracuseStep 2169713 = 1627285) B1627285
theorem B2169731 : Blo 1445542 2169731 := bstep (se 1 (by rfl) ⟨1627298, by rfl⟩ : syracuseStep 2169731 = 3254597) B3254597
theorem B2317187 : Blo 1445542 2317187 := bstep (se 1 (by rfl) ⟨1737890, by rfl⟩ : syracuseStep 2317187 = 3475781) B3475781
theorem B2169761 : Blo 1445542 2169761 := bstep (se 2 (by rfl) ⟨813660, by rfl⟩ : syracuseStep 2169761 = 1627321) B1627321
theorem B4881329 : Blo 1445542 4881329 := bstep (se 2 (by rfl) ⟨1830498, by rfl⟩ : syracuseStep 4881329 = 3660997) B3660997
theorem B2169779 : Blo 1445542 2169779 := bstep (se 1 (by rfl) ⟨1627334, by rfl⟩ : syracuseStep 2169779 = 3254669) B3254669
theorem B8240069 : Blo 1445542 8240069 := bstep (se 4 (by rfl) ⟨772506, by rfl⟩ : syracuseStep 8240069 = 1545013) B1545013
theorem B2440145 : Blo 1445542 2440145 := bstep (se 2 (by rfl) ⟨915054, by rfl⟩ : syracuseStep 2440145 = 1830109) B1830109
theorem B2169809 : Blo 1445542 2169809 := bstep (se 2 (by rfl) ⟨813678, by rfl⟩ : syracuseStep 2169809 = 1627357) B1627357
theorem B2169827 : Blo 1445542 2169827 := bstep (se 1 (by rfl) ⟨1627370, by rfl⟩ : syracuseStep 2169827 = 3254741) B3254741
theorem B24730595 : Blo 1445542 24730595 := bstep (se 1 (by rfl) ⟨18547946, by rfl⟩ : syracuseStep 24730595 = 37095893) B37095893
theorem B3660785 : Blo 1445542 3660785 := bstep (se 2 (by rfl) ⟨1372794, by rfl⟩ : syracuseStep 3660785 = 2745589) B2745589
theorem B2472947 : Blo 1445542 2472947 := bstep (se 1 (by rfl) ⟨1854710, by rfl⟩ : syracuseStep 2472947 = 3709421) B3709421
theorem B2169857 : Blo 1445542 2169857 := bstep (se 2 (by rfl) ⟨813696, by rfl⟩ : syracuseStep 2169857 = 1627393) B1627393
theorem B2317315 : Blo 1445542 2317315 := bstep (se 1 (by rfl) ⟨1737986, by rfl⟩ : syracuseStep 2317315 = 3475973) B3475973
theorem B9272333 : Blo 1445542 9272333 := bstep (se 3 (by rfl) ⟨1738562, by rfl⟩ : syracuseStep 9272333 = 3477125) B3477125
theorem B4119569 : Blo 1445542 4119569 := bstep (se 2 (by rfl) ⟨1544838, by rfl⟩ : syracuseStep 4119569 = 3089677) B3089677
theorem B2169875 : Blo 1445542 2169875 := bstep (se 1 (by rfl) ⟨1627406, by rfl⟩ : syracuseStep 2169875 = 3254813) B3254813
theorem B3660835 : Blo 1445542 3660835 := bstep (se 1 (by rfl) ⟨2745626, by rfl⟩ : syracuseStep 3660835 = 5491253) B5491253
theorem B2169905 : Blo 1445542 2169905 := bstep (se 2 (by rfl) ⟨813714, by rfl⟩ : syracuseStep 2169905 = 1627429) B1627429
theorem B2169923 : Blo 1445542 2169923 := bstep (se 1 (by rfl) ⟨1627442, by rfl⟩ : syracuseStep 2169923 = 3254885) B3254885
theorem B15858757 : Blo 1445542 15858757 := bstep (se 4 (by rfl) ⟨1486758, by rfl⟩ : syracuseStep 15858757 = 2973517) B2973517
theorem B2440273 : Blo 1445542 2440273 := bstep (se 2 (by rfl) ⟨915102, by rfl⟩ : syracuseStep 2440273 = 1830205) B1830205
theorem B2169953 : Blo 1445542 2169953 := bstep (se 2 (by rfl) ⟨813732, by rfl⟩ : syracuseStep 2169953 = 1627465) B1627465
theorem B7322723 : Blo 1445542 7322723 := bstep (se 1 (by rfl) ⟨5492042, by rfl⟩ : syracuseStep 7322723 = 10984085) B10984085
theorem B2440307 : Blo 1445542 2440307 := bstep (se 1 (by rfl) ⟨1830230, by rfl⟩ : syracuseStep 2440307 = 3660461) B3660461
theorem B2169971 : Blo 1445542 2169971 := bstep (se 1 (by rfl) ⟨1627478, by rfl⟩ : syracuseStep 2169971 = 3254957) B3254957
theorem B2170001 : Blo 1445542 2170001 := bstep (se 2 (by rfl) ⟨813750, by rfl⟩ : syracuseStep 2170001 = 1627501) B1627501
theorem B2170019 : Blo 1445542 2170019 := bstep (se 1 (by rfl) ⟨1627514, by rfl⟩ : syracuseStep 2170019 = 3255029) B3255029
theorem B3660977 : Blo 1445542 3660977 := bstep (se 2 (by rfl) ⟨1372866, by rfl⟩ : syracuseStep 3660977 = 2745733) B2745733
theorem B2170049 : Blo 1445542 2170049 := bstep (se 2 (by rfl) ⟨813768, by rfl⟩ : syracuseStep 2170049 = 1627537) B1627537
theorem B4119761 : Blo 1445542 4119761 := bstep (se 2 (by rfl) ⟨1544910, by rfl⟩ : syracuseStep 4119761 = 3089821) B3089821
theorem B2170067 : Blo 1445542 2170067 := bstep (se 1 (by rfl) ⟨1627550, by rfl⟩ : syracuseStep 2170067 = 3255101) B3255101
theorem B2170097 : Blo 1445542 2170097 := bstep (se 2 (by rfl) ⟨813786, by rfl⟩ : syracuseStep 2170097 = 1627573) B1627573
theorem B2440435 : Blo 1445542 2440435 := bstep (se 1 (by rfl) ⟨1830326, by rfl⟩ : syracuseStep 2440435 = 3660653) B3660653
theorem B2170115 : Blo 1445542 2170115 := bstep (se 1 (by rfl) ⟨1627586, by rfl⟩ : syracuseStep 2170115 = 3255173) B3255173
theorem B2170145 : Blo 1445542 2170145 := bstep (se 2 (by rfl) ⟨813804, by rfl⟩ : syracuseStep 2170145 = 1627609) B1627609
theorem B5496113 : Blo 1445542 5496113 := bstep (se 2 (by rfl) ⟨2061042, by rfl⟩ : syracuseStep 5496113 = 4122085) B4122085
theorem B2170163 : Blo 1445542 2170163 := bstep (se 1 (by rfl) ⟨1627622, by rfl⟩ : syracuseStep 2170163 = 3255245) B3255245
theorem B2170193 : Blo 1445542 2170193 := bstep (se 2 (by rfl) ⟨813822, by rfl⟩ : syracuseStep 2170193 = 1627645) B1627645
theorem B2170211 : Blo 1445542 2170211 := bstep (se 1 (by rfl) ⟨1627658, by rfl⟩ : syracuseStep 2170211 = 3255317) B3255317
theorem B2440577 : Blo 1445542 2440577 := bstep (se 2 (by rfl) ⟨915216, by rfl⟩ : syracuseStep 2440577 = 1830433) B1830433
theorem B2170241 : Blo 1445542 2170241 := bstep (se 2 (by rfl) ⟨813840, by rfl⟩ : syracuseStep 2170241 = 1627681) B1627681
theorem B8240525 : Blo 1445542 8240525 := bstep (se 3 (by rfl) ⟨1545098, by rfl⟩ : syracuseStep 8240525 = 3090197) B3090197
theorem B2170259 : Blo 1445542 2170259 := bstep (se 1 (by rfl) ⟨1627694, by rfl⟩ : syracuseStep 2170259 = 3255389) B3255389
theorem B2170289 : Blo 1445542 2170289 := bstep (se 2 (by rfl) ⟨813858, by rfl⟩ : syracuseStep 2170289 = 1627717) B1627717
theorem B2170307 : Blo 1445542 2170307 := bstep (se 1 (by rfl) ⟨1627730, by rfl⟩ : syracuseStep 2170307 = 3255461) B3255461
theorem B4881869 : Blo 1445542 4881869 := bstep (se 3 (by rfl) ⟨915350, by rfl⟩ : syracuseStep 4881869 = 1830701) B1830701
theorem B2170337 : Blo 1445542 2170337 := bstep (se 2 (by rfl) ⟨813876, by rfl⟩ : syracuseStep 2170337 = 1627753) B1627753
theorem B3087857 : Blo 1445542 3087857 := bstep (se 2 (by rfl) ⟨1157946, by rfl⟩ : syracuseStep 3087857 = 2315893) B2315893
theorem B2170355 : Blo 1445542 2170355 := bstep (se 1 (by rfl) ⟨1627766, by rfl⟩ : syracuseStep 2170355 = 3255533) B3255533
theorem B2440705 : Blo 1445542 2440705 := bstep (se 2 (by rfl) ⟨915264, by rfl⟩ : syracuseStep 2440705 = 1830529) B1830529
theorem B4881923 : Blo 1445542 4881923 := bstep (se 1 (by rfl) ⟨3661442, by rfl⟩ : syracuseStep 4881923 = 7322885) B7322885
theorem B2170385 : Blo 1445542 2170385 := bstep (se 2 (by rfl) ⟨813894, by rfl⟩ : syracuseStep 2170385 = 1627789) B1627789
theorem B2440739 : Blo 1445542 2440739 := bstep (se 1 (by rfl) ⟨1830554, by rfl⟩ : syracuseStep 2440739 = 3661109) B3661109
theorem B2170403 : Blo 1445542 2170403 := bstep (se 1 (by rfl) ⟨1627802, by rfl⟩ : syracuseStep 2170403 = 3255605) B3255605
theorem B2170433 : Blo 1445542 2170433 := bstep (se 2 (by rfl) ⟨813912, by rfl⟩ : syracuseStep 2170433 = 1627825) B1627825
theorem B2170451 : Blo 1445542 2170451 := bstep (se 1 (by rfl) ⟨1627838, by rfl⟩ : syracuseStep 2170451 = 3255677) B3255677
theorem B2170481 : Blo 1445542 2170481 := bstep (se 2 (by rfl) ⟨813930, by rfl⟩ : syracuseStep 2170481 = 1627861) B1627861
theorem B2170499 : Blo 1445542 2170499 := bstep (se 1 (by rfl) ⟨1627874, by rfl⟩ : syracuseStep 2170499 = 3255749) B3255749
theorem B2170529 : Blo 1445542 2170529 := bstep (se 2 (by rfl) ⟨813948, by rfl⟩ : syracuseStep 2170529 = 1627897) B1627897
theorem B2440867 : Blo 1445542 2440867 := bstep (se 1 (by rfl) ⟨1830650, by rfl⟩ : syracuseStep 2440867 = 3661301) B3661301
theorem B2170547 : Blo 1445542 2170547 := bstep (se 1 (by rfl) ⟨1627910, by rfl⟩ : syracuseStep 2170547 = 3255821) B3255821
theorem B2170577 : Blo 1445542 2170577 := bstep (se 2 (by rfl) ⟨813966, by rfl⟩ : syracuseStep 2170577 = 1627933) B1627933
theorem B2318033 : Blo 1445542 2318033 := bstep (se 2 (by rfl) ⟨869262, by rfl⟩ : syracuseStep 2318033 = 1738525) B1738525
theorem B6176483 : Blo 1445542 6176483 := bstep (se 1 (by rfl) ⟨4632362, by rfl⟩ : syracuseStep 6176483 = 9264725) B9264725
theorem B2170595 : Blo 1445542 2170595 := bstep (se 1 (by rfl) ⟨1627946, by rfl⟩ : syracuseStep 2170595 = 3255893) B3255893
theorem B2170625 : Blo 1445542 2170625 := bstep (se 2 (by rfl) ⟨813984, by rfl⟩ : syracuseStep 2170625 = 1627969) B1627969
theorem B4882193 : Blo 1445542 4882193 := bstep (se 2 (by rfl) ⟨1830822, by rfl⟩ : syracuseStep 4882193 = 3661645) B3661645
theorem B2170643 : Blo 1445542 2170643 := bstep (se 1 (by rfl) ⟨1627982, by rfl⟩ : syracuseStep 2170643 = 3255965) B3255965
theorem B2441009 : Blo 1445542 2441009 := bstep (se 2 (by rfl) ⟨915378, by rfl⟩ : syracuseStep 2441009 = 1830757) B1830757
theorem B2170673 : Blo 1445542 2170673 := bstep (se 2 (by rfl) ⟨814002, by rfl⟩ : syracuseStep 2170673 = 1628005) B1628005
theorem B2170691 : Blo 1445542 2170691 := bstep (se 1 (by rfl) ⟨1628018, by rfl⟩ : syracuseStep 2170691 = 3256037) B3256037
theorem B2318161 : Blo 1445542 2318161 := bstep (se 2 (by rfl) ⟨869310, by rfl⟩ : syracuseStep 2318161 = 1738621) B1738621
theorem B2170721 : Blo 1445542 2170721 := bstep (se 2 (by rfl) ⟨814020, by rfl⟩ : syracuseStep 2170721 = 1628041) B1628041
theorem B11894627 : Blo 1445542 11894627 := bstep (se 1 (by rfl) ⟨8920970, by rfl⟩ : syracuseStep 11894627 = 17841941) B17841941
theorem B2170739 : Blo 1445542 2170739 := bstep (se 1 (by rfl) ⟨1628054, by rfl⟩ : syracuseStep 2170739 = 3256109) B3256109
theorem B7323533 : Blo 1445542 7323533 := bstep (se 3 (by rfl) ⟨1373162, by rfl⟩ : syracuseStep 7323533 = 2746325) B2746325
theorem B2170769 : Blo 1445542 2170769 := bstep (se 2 (by rfl) ⟨814038, by rfl⟩ : syracuseStep 2170769 = 1628077) B1628077
theorem B4947875 : Blo 1445542 4947875 := bstep (se 1 (by rfl) ⟨3710906, by rfl⟩ : syracuseStep 4947875 = 7421813) B7421813
theorem B2170787 : Blo 1445542 2170787 := bstep (se 1 (by rfl) ⟨1628090, by rfl⟩ : syracuseStep 2170787 = 3256181) B3256181
theorem B2441137 : Blo 1445542 2441137 := bstep (se 2 (by rfl) ⟨915426, by rfl⟩ : syracuseStep 2441137 = 1830853) B1830853
theorem B2170817 : Blo 1445542 2170817 := bstep (se 2 (by rfl) ⟨814056, by rfl⟩ : syracuseStep 2170817 = 1628113) B1628113
theorem B13565893 : Blo 1445542 13565893 := bstep (se 4 (by rfl) ⟨1271802, by rfl⟩ : syracuseStep 13565893 = 2543605) B2543605
theorem B2441171 : Blo 1445542 2441171 := bstep (se 1 (by rfl) ⟨1830878, by rfl⟩ : syracuseStep 2441171 = 3661757) B3661757
theorem B2170835 : Blo 1445542 2170835 := bstep (se 1 (by rfl) ⟨1628126, by rfl⟩ : syracuseStep 2170835 = 3256253) B3256253
theorem B2170865 : Blo 1445542 2170865 := bstep (se 2 (by rfl) ⟨814074, by rfl⟩ : syracuseStep 2170865 = 1628149) B1628149
theorem B13197329 : Blo 1445542 13197329 := bstep (se 2 (by rfl) ⟨4948998, by rfl⟩ : syracuseStep 13197329 = 9897997) B9897997
theorem B20865059 : Blo 1445542 20865059 := bstep (se 1 (by rfl) ⟨15648794, by rfl⟩ : syracuseStep 20865059 = 31297589) B31297589
theorem B7823405 : Blo 1445542 7823405 := bstep (se 3 (by rfl) ⟨1466888, by rfl⟩ : syracuseStep 7823405 = 2933777) B2933777
theorem B4120627 : Blo 1445542 4120627 := bstep (se 1 (by rfl) ⟨3090470, by rfl⟩ : syracuseStep 4120627 = 6180941) B6180941
theorem B2170955 : Blo 1445542 2170955 := bstep (se 1 (by rfl) ⟨1628216, by rfl⟩ : syracuseStep 2170955 = 3256433) B3256433
theorem B2170967 : Blo 1445542 2170967 := bstep (se 1 (by rfl) ⟨1628225, by rfl⟩ : syracuseStep 2170967 = 3256451) B3256451
theorem B5283929 : Blo 1445542 5283929 := bstep (se 2 (by rfl) ⟨1981473, by rfl⟩ : syracuseStep 5283929 = 3962947) B3962947
theorem B2744435 : Blo 1445542 2744435 := bstep (se 1 (by rfl) ⟨2058326, by rfl⟩ : syracuseStep 2744435 = 4116653) B4116653
theorem B3088523 : Blo 1445542 3088523 := bstep (se 1 (by rfl) ⟨2316392, by rfl⟩ : syracuseStep 3088523 = 4632785) B4632785
theorem B2171033 : Blo 1445542 2171033 := bstep (se 2 (by rfl) ⟨814137, by rfl⟩ : syracuseStep 2171033 = 1628275) B1628275
theorem B4882625 : Blo 1445542 4882625 := bstep (se 2 (by rfl) ⟨1830984, by rfl⟩ : syracuseStep 4882625 = 3661969) B3661969
theorem B2318539 : Blo 1445542 2318539 := bstep (se 1 (by rfl) ⟨1738904, by rfl⟩ : syracuseStep 2318539 = 3477809) B3477809
theorem B5865689 : Blo 1445542 5865689 := bstep (se 2 (by rfl) ⟨2199633, by rfl⟩ : syracuseStep 5865689 = 4399267) B4399267
theorem B3252491 : Blo 1445542 3252491 := bstep (se 1 (by rfl) ⟨2439368, by rfl⟩ : syracuseStep 3252491 = 4878737) B4878737
theorem B2171147 : Blo 1445542 2171147 := bstep (se 1 (by rfl) ⟨1628360, by rfl⟩ : syracuseStep 2171147 = 3256721) B3256721
theorem B2441495 : Blo 1445542 2441495 := bstep (se 1 (by rfl) ⟨1831121, by rfl⟩ : syracuseStep 2441495 = 3662243) B3662243
theorem B2171159 : Blo 1445542 2171159 := bstep (se 1 (by rfl) ⟨1628369, by rfl⟩ : syracuseStep 2171159 = 3256739) B3256739
theorem B39608621 : Blo 1445542 39608621 := bstep (se 3 (by rfl) ⟨7426616, by rfl⟩ : syracuseStep 39608621 = 14853233) B14853233
theorem B3662131 : Blo 1445542 3662131 := bstep (se 1 (by rfl) ⟨2746598, by rfl⟩ : syracuseStep 3662131 = 5493197) B5493197
theorem B3252545 : Blo 1445542 3252545 := bstep (se 2 (by rfl) ⟨1219704, by rfl⟩ : syracuseStep 3252545 = 2439409) B2439409
theorem B2171225 : Blo 1445542 2171225 := bstep (se 2 (by rfl) ⟨814209, by rfl⟩ : syracuseStep 2171225 = 1628419) B1628419
theorem B2441623 : Blo 1445542 2441623 := bstep (se 1 (by rfl) ⟨1831217, by rfl⟩ : syracuseStep 2441623 = 3662435) B3662435
theorem B3662273 : Blo 1445542 3662273 := bstep (se 2 (by rfl) ⟨1373352, by rfl⟩ : syracuseStep 3662273 = 2746705) B2746705
theorem B3252761 : Blo 1445542 3252761 := bstep (se 2 (by rfl) ⟨1219785, by rfl⟩ : syracuseStep 3252761 = 2439571) B2439571
theorem B10986029 : Blo 1445542 10986029 := bstep (se 3 (by rfl) ⟨2059880, by rfl⟩ : syracuseStep 10986029 = 4119761) B4119761
theorem B8241709 : Blo 1445542 8241709 := bstep (se 3 (by rfl) ⟨1545320, by rfl⟩ : syracuseStep 8241709 = 3090641) B3090641
theorem B2744921 : Blo 1445542 2744921 := bstep (se 2 (by rfl) ⟨1029345, by rfl⟩ : syracuseStep 2744921 = 2058691) B2058691
theorem B35193437 : Blo 1445542 35193437 := bstep (se 3 (by rfl) ⟨6598769, by rfl⟩ : syracuseStep 35193437 = 13197539) B13197539
theorem B3252851 : Blo 1445542 3252851 := bstep (se 1 (by rfl) ⟨2439638, by rfl⟩ : syracuseStep 3252851 = 4879277) B4879277
theorem B3252887 : Blo 1445542 3252887 := bstep (se 1 (by rfl) ⟨2439665, by rfl⟩ : syracuseStep 3252887 = 4879331) B4879331
theorem B12354227 : Blo 1445542 12354227 := bstep (se 1 (by rfl) ⟨9265670, by rfl⟩ : syracuseStep 12354227 = 18531341) B18531341
theorem B4883165 : Blo 1445542 4883165 := bstep (se 3 (by rfl) ⟨915593, by rfl⟩ : syracuseStep 4883165 = 1831187) B1831187
theorem B3253067 : Blo 1445542 3253067 := bstep (se 1 (by rfl) ⟨2439800, by rfl⟩ : syracuseStep 3253067 = 4879601) B4879601
theorem B3253121 : Blo 1445542 3253121 := bstep (se 2 (by rfl) ⟨1219920, by rfl⟩ : syracuseStep 3253121 = 2439841) B2439841
theorem B3908503 : Blo 1445542 3908503 := bstep (se 1 (by rfl) ⟨2931377, by rfl⟩ : syracuseStep 3908503 = 5862755) B5862755
theorem B18539441 : Blo 1445542 18539441 := bstep (se 2 (by rfl) ⟨6952290, by rfl⟩ : syracuseStep 18539441 = 13904581) B13904581
theorem B10978253 : Blo 1445542 10978253 := bstep (se 3 (by rfl) ⟨2058422, by rfl⟩ : syracuseStep 10978253 = 4116845) B4116845
theorem B2442251 : Blo 1445542 2442251 := bstep (se 1 (by rfl) ⟨1831688, by rfl⟩ : syracuseStep 2442251 = 3663377) B3663377
theorem B12354605 : Blo 1445542 12354605 := bstep (se 3 (by rfl) ⟨2316488, by rfl⟩ : syracuseStep 12354605 = 4632977) B4632977
theorem B4121675 : Blo 1445542 4121675 := bstep (se 1 (by rfl) ⟨3091256, by rfl⟩ : syracuseStep 4121675 = 6182513) B6182513
theorem B3253337 : Blo 1445542 3253337 := bstep (se 2 (by rfl) ⟨1220001, by rfl⟩ : syracuseStep 3253337 = 2440003) B2440003
theorem B3089497 : Blo 1445542 3089497 := bstep (se 2 (by rfl) ⟨1158561, by rfl⟩ : syracuseStep 3089497 = 2317123) B2317123
theorem B5489795 : Blo 1445542 5489795 := bstep (se 1 (by rfl) ⟨4117346, by rfl⟩ : syracuseStep 5489795 = 8234693) B8234693
theorem B2442379 : Blo 1445542 2442379 := bstep (se 1 (by rfl) ⟨1831784, by rfl⟩ : syracuseStep 2442379 = 3663569) B3663569
theorem B7423127 : Blo 1445542 7423127 := bstep (se 1 (by rfl) ⟨5567345, by rfl⟩ : syracuseStep 7423127 = 11134691) B11134691
theorem B3253427 : Blo 1445542 3253427 := bstep (se 1 (by rfl) ⟨2440070, by rfl⟩ : syracuseStep 3253427 = 4880141) B4880141
theorem B3253463 : Blo 1445542 3253463 := bstep (se 1 (by rfl) ⟨2440097, by rfl⟩ : syracuseStep 3253463 = 4880195) B4880195
theorem B2442521 : Blo 1445542 2442521 := bstep (se 2 (by rfl) ⟨915945, by rfl⟩ : syracuseStep 2442521 = 1831891) B1831891
theorem B4695371 : Blo 1445542 4695371 := bstep (se 1 (by rfl) ⟨3521528, by rfl⟩ : syracuseStep 4695371 = 7043057) B7043057
theorem B3089753 : Blo 1445542 3089753 := bstep (se 2 (by rfl) ⟨1158657, by rfl⟩ : syracuseStep 3089753 = 2317315) B2317315
theorem B3253643 : Blo 1445542 3253643 := bstep (se 1 (by rfl) ⟨2440232, by rfl⟩ : syracuseStep 3253643 = 4880465) B4880465
theorem B3474839 : Blo 1445542 3474839 := bstep (se 1 (by rfl) ⟨2606129, by rfl⟩ : syracuseStep 3474839 = 5212259) B5212259
theorem B2442649 : Blo 1445542 2442649 := bstep (se 2 (by rfl) ⟨915993, by rfl⟩ : syracuseStep 2442649 = 1831987) B1831987
theorem B10978739 : Blo 1445542 10978739 := bstep (se 1 (by rfl) ⟨8234054, by rfl⟩ : syracuseStep 10978739 = 16468109) B16468109
theorem B8234419 : Blo 1445542 8234419 := bstep (se 1 (by rfl) ⟨6175814, by rfl⟩ : syracuseStep 8234419 = 12351629) B12351629
theorem B3253697 : Blo 1445542 3253697 := bstep (se 2 (by rfl) ⟨1220136, by rfl⟩ : syracuseStep 3253697 = 2440273) B2440273
theorem B5490251 : Blo 1445542 5490251 := bstep (se 1 (by rfl) ⟨4117688, by rfl⟩ : syracuseStep 5490251 = 8235377) B8235377
theorem B7325315 : Blo 1445542 7325315 := bstep (se 1 (by rfl) ⟨5493986, by rfl⟩ : syracuseStep 7325315 = 10987973) B10987973
theorem B3253913 : Blo 1445542 3253913 := bstep (se 2 (by rfl) ⟨1220217, by rfl⟩ : syracuseStep 3253913 = 2440435) B2440435
theorem B5211827 : Blo 1445542 5211827 := bstep (se 1 (by rfl) ⟨3908870, by rfl⟩ : syracuseStep 5211827 = 7817741) B7817741
theorem B3663539 : Blo 1445542 3663539 := bstep (se 1 (by rfl) ⟨2747654, by rfl⟩ : syracuseStep 3663539 = 5495309) B5495309
theorem B3254003 : Blo 1445542 3254003 := bstep (se 1 (by rfl) ⟨2440502, by rfl⟩ : syracuseStep 3254003 = 4881005) B4881005
theorem B3090163 : Blo 1445542 3090163 := bstep (se 1 (by rfl) ⟨2317622, by rfl⟩ : syracuseStep 3090163 = 4635245) B4635245
theorem B5490449 : Blo 1445542 5490449 := bstep (se 2 (by rfl) ⟨2058918, by rfl⟩ : syracuseStep 5490449 = 4117837) B4117837
theorem B3254039 : Blo 1445542 3254039 := bstep (se 1 (by rfl) ⟨2440529, by rfl⟩ : syracuseStep 3254039 = 4881059) B4881059
theorem B4884299 : Blo 1445542 4884299 := bstep (se 1 (by rfl) ⟨3663224, by rfl⟩ : syracuseStep 4884299 = 7326449) B7326449
theorem B3254219 : Blo 1445542 3254219 := bstep (se 1 (by rfl) ⟨2440664, by rfl⟩ : syracuseStep 3254219 = 4881329) B4881329
theorem B1648631 : Blo 1445542 1648631 := bstep (se 1 (by rfl) ⟨1236473, by rfl⟩ : syracuseStep 1648631 = 2472947) B2472947
theorem B3254273 : Blo 1445542 3254273 := bstep (se 2 (by rfl) ⟨1220352, by rfl⟩ : syracuseStep 3254273 = 2440705) B2440705
theorem B2746379 : Blo 1445542 2746379 := bstep (se 1 (by rfl) ⟨2059784, by rfl⟩ : syracuseStep 2746379 = 4119569) B4119569
theorem B12060707 : Blo 1445542 12060707 := bstep (se 1 (by rfl) ⟨9045530, by rfl⟩ : syracuseStep 12060707 = 18091061) B18091061
theorem B4884569 : Blo 1445542 4884569 := bstep (se 2 (by rfl) ⟨1831713, by rfl⟩ : syracuseStep 4884569 = 3663427) B3663427
theorem B2746561 : Blo 1445542 2746561 := bstep (se 2 (by rfl) ⟨1029960, by rfl⟩ : syracuseStep 2746561 = 2059921) B2059921
theorem B3664075 : Blo 1445542 3664075 := bstep (se 1 (by rfl) ⟨2748056, by rfl⟩ : syracuseStep 3664075 = 5496113) B5496113
theorem B3254489 : Blo 1445542 3254489 := bstep (se 2 (by rfl) ⟨1220433, by rfl⟩ : syracuseStep 3254489 = 2440867) B2440867
theorem B6179095 : Blo 1445542 6179095 := bstep (se 1 (by rfl) ⟨4634321, by rfl⟩ : syracuseStep 6179095 = 9268643) B9268643
theorem B3254579 : Blo 1445542 3254579 := bstep (se 1 (by rfl) ⟨2440934, by rfl⟩ : syracuseStep 3254579 = 4881869) B4881869
theorem B2058571 : Blo 1445542 2058571 := bstep (se 1 (by rfl) ⟨1543928, by rfl⟩ : syracuseStep 2058571 = 3087857) B3087857
theorem B3254615 : Blo 1445542 3254615 := bstep (se 1 (by rfl) ⟨2440961, by rfl⟩ : syracuseStep 3254615 = 4881923) B4881923
theorem B6179165 : Blo 1445542 6179165 := bstep (se 3 (by rfl) ⟨1158593, by rfl⟩ : syracuseStep 6179165 = 2317187) B2317187
theorem B3090881 : Blo 1445542 3090881 := bstep (se 2 (by rfl) ⟨1159080, by rfl⟩ : syracuseStep 3090881 = 2318161) B2318161
theorem B3254795 : Blo 1445542 3254795 := bstep (se 1 (by rfl) ⟨2441096, by rfl⟩ : syracuseStep 3254795 = 4882193) B4882193
theorem B5491223 : Blo 1445542 5491223 := bstep (se 1 (by rfl) ⟨4118417, by rfl⟩ : syracuseStep 5491223 = 8236835) B8236835
theorem B3254849 : Blo 1445542 3254849 := bstep (se 2 (by rfl) ⟨1220568, by rfl⟩ : syracuseStep 3254849 = 2441137) B2441137
theorem B2230859 : Blo 1445542 2230859 := bstep (se 1 (by rfl) ⟨1673144, by rfl⟩ : syracuseStep 2230859 = 3346289) B3346289
theorem B2747009 : Blo 1445542 2747009 := bstep (se 2 (by rfl) ⟨1030128, by rfl⟩ : syracuseStep 2747009 = 2060257) B2060257
theorem B5016257 : Blo 1445542 5016257 := bstep (se 2 (by rfl) ⟨1881096, by rfl⟩ : syracuseStep 5016257 = 3762193) B3762193
theorem B24726221 : Blo 1445542 24726221 := bstep (se 3 (by rfl) ⟨4636166, by rfl⟩ : syracuseStep 24726221 = 9272333) B9272333
theorem B5491421 : Blo 1445542 5491421 := bstep (se 3 (by rfl) ⟨1029641, by rfl⟩ : syracuseStep 5491421 = 2059283) B2059283
theorem B59378417 : Blo 1445542 59378417 := bstep (se 2 (by rfl) ⟨22266906, by rfl⟩ : syracuseStep 59378417 = 44533813) B44533813
theorem B2607895 : Blo 1445542 2607895 := bstep (se 1 (by rfl) ⟨1955921, by rfl⟩ : syracuseStep 2607895 = 3911843) B3911843
theorem B3091223 : Blo 1445542 3091223 := bstep (se 1 (by rfl) ⟨2318417, by rfl⟩ : syracuseStep 3091223 = 4636835) B4636835
theorem B3255065 : Blo 1445542 3255065 := bstep (se 2 (by rfl) ⟨1220649, by rfl⟩ : syracuseStep 3255065 = 2441299) B2441299
theorem B4885271 : Blo 1445542 4885271 := bstep (se 1 (by rfl) ⟨3663953, by rfl⟩ : syracuseStep 4885271 = 7327907) B7327907
theorem B1829719 : Blo 1445542 1829719 := bstep (se 1 (by rfl) ⟨1372289, by rfl⟩ : syracuseStep 1829719 = 2744579) B2744579
theorem B10980197 : Blo 1445542 10980197 := bstep (se 4 (by rfl) ⟨1029393, by rfl⟩ : syracuseStep 10980197 = 2058787) B2058787
theorem B8235877 : Blo 1445542 8235877 := bstep (se 4 (by rfl) ⟨772113, by rfl⟩ : syracuseStep 8235877 = 1544227) B1544227
theorem B3255155 : Blo 1445542 3255155 := bstep (se 1 (by rfl) ⟨2441366, by rfl⟩ : syracuseStep 3255155 = 4882733) B4882733
theorem B3255191 : Blo 1445542 3255191 := bstep (se 1 (by rfl) ⟨2441393, by rfl⟩ : syracuseStep 3255191 = 4882787) B4882787
theorem B3091393 : Blo 1445542 3091393 := bstep (se 2 (by rfl) ⟨1159272, by rfl⟩ : syracuseStep 3091393 = 2318545) B2318545
theorem B2608075 : Blo 1445542 2608075 := bstep (se 1 (by rfl) ⟨1956056, by rfl⟩ : syracuseStep 2608075 = 3912113) B3912113
theorem B2747351 : Blo 1445542 2747351 := bstep (se 1 (by rfl) ⟨2060513, by rfl⟩ : syracuseStep 2747351 = 4121027) B4121027
theorem B11725829 : Blo 1445542 11725829 := bstep (se 4 (by rfl) ⟨1099296, by rfl⟩ : syracuseStep 11725829 = 2198593) B2198593
theorem B22866961 : Blo 1445542 22866961 := bstep (se 2 (by rfl) ⟨8575110, by rfl⟩ : syracuseStep 22866961 = 17150221) B17150221
theorem B6179915 : Blo 1445542 6179915 := bstep (se 1 (by rfl) ⟨4634936, by rfl⟩ : syracuseStep 6179915 = 9269873) B9269873
theorem B3255371 : Blo 1445542 3255371 := bstep (se 1 (by rfl) ⟨2441528, by rfl⟩ : syracuseStep 3255371 = 4883057) B4883057
theorem B3255425 : Blo 1445542 3255425 := bstep (se 2 (by rfl) ⟨1220784, by rfl⟩ : syracuseStep 3255425 = 2441569) B2441569
theorem B2198807 : Blo 1445542 2198807 := bstep (se 1 (by rfl) ⟨1649105, by rfl⟩ : syracuseStep 2198807 = 3298211) B3298211
theorem B10980683 : Blo 1445542 10980683 := bstep (se 1 (by rfl) ⟨8235512, by rfl⟩ : syracuseStep 10980683 = 16471025) B16471025
theorem B3255641 : Blo 1445542 3255641 := bstep (se 2 (by rfl) ⟨1220865, by rfl⟩ : syracuseStep 3255641 = 2441731) B2441731
theorem B3255731 : Blo 1445542 3255731 := bstep (se 1 (by rfl) ⟨2441798, by rfl⟩ : syracuseStep 3255731 = 4883597) B4883597
theorem B3476915 : Blo 1445542 3476915 := bstep (se 1 (by rfl) ⟨2607686, by rfl⟩ : syracuseStep 3476915 = 5215373) B5215373
theorem B3255767 : Blo 1445542 3255767 := bstep (se 1 (by rfl) ⟨2441825, by rfl⟩ : syracuseStep 3255767 = 4883651) B4883651
theorem B13905425 : Blo 1445542 13905425 := bstep (se 2 (by rfl) ⟨5214534, by rfl⟩ : syracuseStep 13905425 = 10429069) B10429069
theorem B4632157 : Blo 1445542 4632157 := bstep (se 3 (by rfl) ⟨868529, by rfl⟩ : syracuseStep 4632157 = 1737059) B1737059
theorem B2748019 : Blo 1445542 2748019 := bstep (se 1 (by rfl) ⟨2061014, by rfl⟩ : syracuseStep 2748019 = 4122029) B4122029
theorem B1830539 : Blo 1445542 1830539 := bstep (se 1 (by rfl) ⟨1372904, by rfl⟩ : syracuseStep 1830539 = 2745809) B2745809
theorem B3255947 : Blo 1445542 3255947 := bstep (se 1 (by rfl) ⟨2441960, by rfl⟩ : syracuseStep 3255947 = 4883921) B4883921
theorem B1445547 : Blo 1445542 1445547 := bstep (se 1 (by rfl) ⟨1084160, by rfl⟩ : syracuseStep 1445547 = 2168321) B2168321
theorem B1445559 : Blo 1445542 1445559 := bstep (se 1 (by rfl) ⟨1084169, by rfl⟩ : syracuseStep 1445559 = 2168339) B2168339
theorem B3256001 : Blo 1445542 3256001 := bstep (se 2 (by rfl) ⟨1221000, by rfl⟩ : syracuseStep 3256001 = 2442001) B2442001
theorem B1445579 : Blo 1445542 1445579 := bstep (se 1 (by rfl) ⟨1084184, by rfl⟩ : syracuseStep 1445579 = 2168369) B2168369
theorem B1445591 : Blo 1445542 1445591 := bstep (se 1 (by rfl) ⟨1084193, by rfl⟩ : syracuseStep 1445591 = 2168387) B2168387
theorem B1445611 : Blo 1445542 1445611 := bstep (se 1 (by rfl) ⟨1084208, by rfl⟩ : syracuseStep 1445611 = 2168417) B2168417
theorem B1445623 : Blo 1445542 1445623 := bstep (se 1 (by rfl) ⟨1084217, by rfl⟩ : syracuseStep 1445623 = 2168435) B2168435
theorem B1445643 : Blo 1445542 1445643 := bstep (se 1 (by rfl) ⟨1084232, by rfl⟩ : syracuseStep 1445643 = 2168465) B2168465
theorem B1445655 : Blo 1445542 1445655 := bstep (se 1 (by rfl) ⟨1084241, by rfl⟩ : syracuseStep 1445655 = 2168483) B2168483
theorem B1445675 : Blo 1445542 1445675 := bstep (se 1 (by rfl) ⟨1084256, by rfl⟩ : syracuseStep 1445675 = 2168513) B2168513
theorem B1445687 : Blo 1445542 1445687 := bstep (se 1 (by rfl) ⟨1084265, by rfl⟩ : syracuseStep 1445687 = 2168531) B2168531
theorem B1445707 : Blo 1445542 1445707 := bstep (se 1 (by rfl) ⟨1084280, by rfl⟩ : syracuseStep 1445707 = 2168561) B2168561
theorem B1445719 : Blo 1445542 1445719 := bstep (se 1 (by rfl) ⟨1084289, by rfl⟩ : syracuseStep 1445719 = 2168579) B2168579
theorem B1445739 : Blo 1445542 1445739 := bstep (se 1 (by rfl) ⟨1084304, by rfl⟩ : syracuseStep 1445739 = 2168609) B2168609
theorem B1445751 : Blo 1445542 1445751 := bstep (se 1 (by rfl) ⟨1084313, by rfl⟩ : syracuseStep 1445751 = 2168627) B2168627
theorem B1445771 : Blo 1445542 1445771 := bstep (se 1 (by rfl) ⟨1084328, by rfl⟩ : syracuseStep 1445771 = 2168657) B2168657
theorem B1445783 : Blo 1445542 1445783 := bstep (se 1 (by rfl) ⟨1084337, by rfl⟩ : syracuseStep 1445783 = 2168675) B2168675
theorem B3256217 : Blo 1445542 3256217 := bstep (se 2 (by rfl) ⟨1221081, by rfl⟩ : syracuseStep 3256217 = 2442163) B2442163
theorem B1445803 : Blo 1445542 1445803 := bstep (se 1 (by rfl) ⟨1084352, by rfl⟩ : syracuseStep 1445803 = 2168705) B2168705
theorem B1445815 : Blo 1445542 1445815 := bstep (se 1 (by rfl) ⟨1084361, by rfl⟩ : syracuseStep 1445815 = 2168723) B2168723
theorem B1445835 : Blo 1445542 1445835 := bstep (se 1 (by rfl) ⟨1084376, by rfl⟩ : syracuseStep 1445835 = 2168753) B2168753
theorem B1445847 : Blo 1445542 1445847 := bstep (se 1 (by rfl) ⟨1084385, by rfl⟩ : syracuseStep 1445847 = 2168771) B2168771
theorem B1445867 : Blo 1445542 1445867 := bstep (se 1 (by rfl) ⟨1084400, by rfl⟩ : syracuseStep 1445867 = 2168801) B2168801
theorem B3256307 : Blo 1445542 3256307 := bstep (se 1 (by rfl) ⟨2442230, by rfl⟩ : syracuseStep 3256307 = 4884461) B4884461
theorem B1445879 : Blo 1445542 1445879 := bstep (se 1 (by rfl) ⟨1084409, by rfl⟩ : syracuseStep 1445879 = 2168819) B2168819
theorem B1445899 : Blo 1445542 1445899 := bstep (se 1 (by rfl) ⟨1084424, by rfl⟩ : syracuseStep 1445899 = 2168849) B2168849
theorem B1445911 : Blo 1445542 1445911 := bstep (se 1 (by rfl) ⟨1084433, by rfl⟩ : syracuseStep 1445911 = 2168867) B2168867
theorem B3256343 : Blo 1445542 3256343 := bstep (se 1 (by rfl) ⟨2442257, by rfl⟩ : syracuseStep 3256343 = 4884515) B4884515
theorem B1445931 : Blo 1445542 1445931 := bstep (se 1 (by rfl) ⟨1084448, by rfl⟩ : syracuseStep 1445931 = 2168897) B2168897
theorem B1445943 : Blo 1445542 1445943 := bstep (se 1 (by rfl) ⟨1084457, by rfl⟩ : syracuseStep 1445943 = 2168915) B2168915
theorem B1445963 : Blo 1445542 1445963 := bstep (se 1 (by rfl) ⟨1084472, by rfl⟩ : syracuseStep 1445963 = 2168945) B2168945
theorem B1445975 : Blo 1445542 1445975 := bstep (se 1 (by rfl) ⟨1084481, by rfl⟩ : syracuseStep 1445975 = 2168963) B2168963
theorem B7319645 : Blo 1445542 7319645 := bstep (se 3 (by rfl) ⟨1372433, by rfl⟩ : syracuseStep 7319645 = 2744867) B2744867
theorem B6951005 : Blo 1445542 6951005 := bstep (se 3 (by rfl) ⟨1303313, by rfl⟩ : syracuseStep 6951005 = 2606627) B2606627
theorem B1445995 : Blo 1445542 1445995 := bstep (se 1 (by rfl) ⟨1084496, by rfl⟩ : syracuseStep 1445995 = 2168993) B2168993
theorem B1446007 : Blo 1445542 1446007 := bstep (se 1 (by rfl) ⟨1084505, by rfl⟩ : syracuseStep 1446007 = 2169011) B2169011
theorem B1446027 : Blo 1445542 1446027 := bstep (se 1 (by rfl) ⟨1084520, by rfl⟩ : syracuseStep 1446027 = 2169041) B2169041
theorem B1446039 : Blo 1445542 1446039 := bstep (se 1 (by rfl) ⟨1084529, by rfl⟩ : syracuseStep 1446039 = 2169059) B2169059
theorem B1446059 : Blo 1445542 1446059 := bstep (se 1 (by rfl) ⟨1084544, by rfl⟩ : syracuseStep 1446059 = 2169089) B2169089
theorem B5861555 : Blo 1445542 5861555 := bstep (se 1 (by rfl) ⟨4396166, by rfl⟩ : syracuseStep 5861555 = 8792333) B8792333
theorem B1626295 : Blo 1445542 1626295 := bstep (se 1 (by rfl) ⟨1219721, by rfl⟩ : syracuseStep 1626295 = 2439443) B2439443
theorem B1446071 : Blo 1445542 1446071 := bstep (se 1 (by rfl) ⟨1084553, by rfl⟩ : syracuseStep 1446071 = 2169107) B2169107
theorem B5353675 : Blo 1445542 5353675 := bstep (se 1 (by rfl) ⟨4015256, by rfl⟩ : syracuseStep 5353675 = 8030513) B8030513
theorem B1446091 : Blo 1445542 1446091 := bstep (se 1 (by rfl) ⟨1084568, by rfl⟩ : syracuseStep 1446091 = 2169137) B2169137
theorem B3256523 : Blo 1445542 3256523 := bstep (se 1 (by rfl) ⟨2442392, by rfl⟩ : syracuseStep 3256523 = 4884785) B4884785
theorem B1446103 : Blo 1445542 1446103 := bstep (se 1 (by rfl) ⟨1084577, by rfl⟩ : syracuseStep 1446103 = 2169155) B2169155
theorem B1446123 : Blo 1445542 1446123 := bstep (se 1 (by rfl) ⟨1084592, by rfl⟩ : syracuseStep 1446123 = 2169185) B2169185
theorem B1446135 : Blo 1445542 1446135 := bstep (se 1 (by rfl) ⟨1084601, by rfl⟩ : syracuseStep 1446135 = 2169203) B2169203
theorem B3256577 : Blo 1445542 3256577 := bstep (se 2 (by rfl) ⟨1221216, by rfl⟩ : syracuseStep 3256577 = 2442433) B2442433
theorem B1446155 : Blo 1445542 1446155 := bstep (se 1 (by rfl) ⟨1084616, by rfl⟩ : syracuseStep 1446155 = 2169233) B2169233
theorem B1446167 : Blo 1445542 1446167 := bstep (se 1 (by rfl) ⟨1084625, by rfl⟩ : syracuseStep 1446167 = 2169251) B2169251
theorem B1446187 : Blo 1445542 1446187 := bstep (se 1 (by rfl) ⟨1084640, by rfl⟩ : syracuseStep 1446187 = 2169281) B2169281
theorem B1446199 : Blo 1445542 1446199 := bstep (se 1 (by rfl) ⟨1084649, by rfl⟩ : syracuseStep 1446199 = 2169299) B2169299
theorem B1446219 : Blo 1445542 1446219 := bstep (se 1 (by rfl) ⟨1084664, by rfl⟩ : syracuseStep 1446219 = 2169329) B2169329
theorem B1831243 : Blo 1445542 1831243 := bstep (se 1 (by rfl) ⟨1373432, by rfl⟩ : syracuseStep 1831243 = 2746865) B2746865
theorem B1446231 : Blo 1445542 1446231 := bstep (se 1 (by rfl) ⟨1084673, by rfl⟩ : syracuseStep 1446231 = 2169347) B2169347
theorem B10989917 : Blo 1445542 10989917 := bstep (se 3 (by rfl) ⟨2060609, by rfl⟩ : syracuseStep 10989917 = 4121219) B4121219
theorem B1626475 : Blo 1445542 1626475 := bstep (se 1 (by rfl) ⟨1219856, by rfl⟩ : syracuseStep 1626475 = 2439713) B2439713
theorem B1446251 : Blo 1445542 1446251 := bstep (se 1 (by rfl) ⟨1084688, by rfl⟩ : syracuseStep 1446251 = 2169377) B2169377
theorem B1446263 : Blo 1445542 1446263 := bstep (se 1 (by rfl) ⟨1084697, by rfl⟩ : syracuseStep 1446263 = 2169395) B2169395
theorem B1446283 : Blo 1445542 1446283 := bstep (se 1 (by rfl) ⟨1084712, by rfl⟩ : syracuseStep 1446283 = 2169425) B2169425
theorem B1446295 : Blo 1445542 1446295 := bstep (se 1 (by rfl) ⟨1084721, by rfl⟩ : syracuseStep 1446295 = 2169443) B2169443
theorem B1544599 : Blo 1445542 1544599 := bstep (se 1 (by rfl) ⟨1158449, by rfl⟩ : syracuseStep 1544599 = 2316899) B2316899
theorem B1446315 : Blo 1445542 1446315 := bstep (se 1 (by rfl) ⟨1084736, by rfl⟩ : syracuseStep 1446315 = 2169473) B2169473
theorem B1446327 : Blo 1445542 1446327 := bstep (se 1 (by rfl) ⟨1084745, by rfl⟩ : syracuseStep 1446327 = 2169491) B2169491
theorem B1446347 : Blo 1445542 1446347 := bstep (se 1 (by rfl) ⟨1084760, by rfl⟩ : syracuseStep 1446347 = 2169521) B2169521
theorem B1626583 : Blo 1445542 1626583 := bstep (se 1 (by rfl) ⟨1219937, by rfl⟩ : syracuseStep 1626583 = 2439875) B2439875
theorem B1446359 : Blo 1445542 1446359 := bstep (se 1 (by rfl) ⟨1084769, by rfl⟩ : syracuseStep 1446359 = 2169539) B2169539
theorem B3256793 : Blo 1445542 3256793 := bstep (se 2 (by rfl) ⟨1221297, by rfl⟩ : syracuseStep 3256793 = 2442595) B2442595
theorem B1446379 : Blo 1445542 1446379 := bstep (se 1 (by rfl) ⟨1084784, by rfl⟩ : syracuseStep 1446379 = 2169569) B2169569
theorem B1446391 : Blo 1445542 1446391 := bstep (se 1 (by rfl) ⟨1084793, by rfl⟩ : syracuseStep 1446391 = 2169587) B2169587
theorem B1446411 : Blo 1445542 1446411 := bstep (se 1 (by rfl) ⟨1084808, by rfl⟩ : syracuseStep 1446411 = 2169617) B2169617
theorem B1446423 : Blo 1445542 1446423 := bstep (se 1 (by rfl) ⟨1084817, by rfl⟩ : syracuseStep 1446423 = 2169635) B2169635
theorem B1446443 : Blo 1445542 1446443 := bstep (se 1 (by rfl) ⟨1084832, by rfl⟩ : syracuseStep 1446443 = 2169665) B2169665
theorem B4878899 : Blo 1445542 4878899 := bstep (se 1 (by rfl) ⟨3659174, by rfl⟩ : syracuseStep 4878899 = 7318349) B7318349
theorem B3256883 : Blo 1445542 3256883 := bstep (se 1 (by rfl) ⟨2442662, by rfl⟩ : syracuseStep 3256883 = 4885325) B4885325
theorem B1446455 : Blo 1445542 1446455 := bstep (se 1 (by rfl) ⟨1084841, by rfl⟩ : syracuseStep 1446455 = 2169683) B2169683
theorem B1446475 : Blo 1445542 1446475 := bstep (se 1 (by rfl) ⟨1084856, by rfl⟩ : syracuseStep 1446475 = 2169713) B2169713
theorem B1446487 : Blo 1445542 1446487 := bstep (se 1 (by rfl) ⟨1084865, by rfl⟩ : syracuseStep 1446487 = 2169731) B2169731
theorem B1831511 : Blo 1445542 1831511 := bstep (se 1 (by rfl) ⟨1373633, by rfl⟩ : syracuseStep 1831511 = 2747267) B2747267
theorem B3256919 : Blo 1445542 3256919 := bstep (se 1 (by rfl) ⟨2442689, by rfl⟩ : syracuseStep 3256919 = 4885379) B4885379
theorem B1446507 : Blo 1445542 1446507 := bstep (se 1 (by rfl) ⟨1084880, by rfl⟩ : syracuseStep 1446507 = 2169761) B2169761
theorem B1446519 : Blo 1445542 1446519 := bstep (se 1 (by rfl) ⟨1084889, by rfl⟩ : syracuseStep 1446519 = 2169779) B2169779
theorem B5493379 : Blo 1445542 5493379 := bstep (se 1 (by rfl) ⟨4120034, by rfl⟩ : syracuseStep 5493379 = 8240069) B8240069
theorem B1626763 : Blo 1445542 1626763 := bstep (se 1 (by rfl) ⟨1220072, by rfl⟩ : syracuseStep 1626763 = 2440145) B2440145
theorem B1446539 : Blo 1445542 1446539 := bstep (se 1 (by rfl) ⟨1084904, by rfl⟩ : syracuseStep 1446539 = 2169809) B2169809
theorem B1446551 : Blo 1445542 1446551 := bstep (se 1 (by rfl) ⟨1084913, by rfl⟩ : syracuseStep 1446551 = 2169827) B2169827
theorem B16487063 : Blo 1445542 16487063 := bstep (se 1 (by rfl) ⟨12365297, by rfl⟩ : syracuseStep 16487063 = 24730595) B24730595
theorem B1446571 : Blo 1445542 1446571 := bstep (se 1 (by rfl) ⟨1084928, by rfl⟩ : syracuseStep 1446571 = 2169857) B2169857
theorem B11285171 : Blo 1445542 11285171 := bstep (se 1 (by rfl) ⟨8463878, by rfl⟩ : syracuseStep 11285171 = 16927757) B16927757
theorem B1446583 : Blo 1445542 1446583 := bstep (se 1 (by rfl) ⟨1084937, by rfl⟩ : syracuseStep 1446583 = 2169875) B2169875
theorem B1446603 : Blo 1445542 1446603 := bstep (se 1 (by rfl) ⟨1084952, by rfl⟩ : syracuseStep 1446603 = 2169905) B2169905
theorem B1446615 : Blo 1445542 1446615 := bstep (se 1 (by rfl) ⟨1084961, by rfl⟩ : syracuseStep 1446615 = 2169923) B2169923
theorem B5214941 : Blo 1445542 5214941 := bstep (se 3 (by rfl) ⟨977801, by rfl⟩ : syracuseStep 5214941 = 1955603) B1955603
theorem B1446635 : Blo 1445542 1446635 := bstep (se 1 (by rfl) ⟨1084976, by rfl⟩ : syracuseStep 1446635 = 2169953) B2169953
theorem B1626871 : Blo 1445542 1626871 := bstep (se 1 (by rfl) ⟨1220153, by rfl⟩ : syracuseStep 1626871 = 2440307) B2440307
theorem B1446647 : Blo 1445542 1446647 := bstep (se 1 (by rfl) ⟨1084985, by rfl⟩ : syracuseStep 1446647 = 2169971) B2169971
theorem B1446667 : Blo 1445542 1446667 := bstep (se 1 (by rfl) ⟨1085000, by rfl⟩ : syracuseStep 1446667 = 2170001) B2170001
theorem B1446679 : Blo 1445542 1446679 := bstep (se 1 (by rfl) ⟨1085009, by rfl⟩ : syracuseStep 1446679 = 2170019) B2170019
theorem B1446699 : Blo 1445542 1446699 := bstep (se 1 (by rfl) ⟨1085024, by rfl⟩ : syracuseStep 1446699 = 2170049) B2170049
theorem B1446711 : Blo 1445542 1446711 := bstep (se 1 (by rfl) ⟨1085033, by rfl⟩ : syracuseStep 1446711 = 2170067) B2170067
theorem B4879169 : Blo 1445542 4879169 := bstep (se 2 (by rfl) ⟨1829688, by rfl⟩ : syracuseStep 4879169 = 3659377) B3659377
theorem B1446731 : Blo 1445542 1446731 := bstep (se 1 (by rfl) ⟨1085048, by rfl⟩ : syracuseStep 1446731 = 2170097) B2170097
theorem B1446743 : Blo 1445542 1446743 := bstep (se 1 (by rfl) ⟨1085057, by rfl⟩ : syracuseStep 1446743 = 2170115) B2170115
theorem B1446763 : Blo 1445542 1446763 := bstep (se 1 (by rfl) ⟨1085072, by rfl⟩ : syracuseStep 1446763 = 2170145) B2170145
theorem B1446775 : Blo 1445542 1446775 := bstep (se 1 (by rfl) ⟨1085081, by rfl⟩ : syracuseStep 1446775 = 2170163) B2170163
theorem B1446795 : Blo 1445542 1446795 := bstep (se 1 (by rfl) ⟨1085096, by rfl⟩ : syracuseStep 1446795 = 2170193) B2170193
theorem B1446807 : Blo 1445542 1446807 := bstep (se 1 (by rfl) ⟨1085105, by rfl⟩ : syracuseStep 1446807 = 2170211) B2170211
theorem B1627051 : Blo 1445542 1627051 := bstep (se 1 (by rfl) ⟨1220288, by rfl⟩ : syracuseStep 1627051 = 2440577) B2440577
theorem B1446827 : Blo 1445542 1446827 := bstep (se 1 (by rfl) ⟨1085120, by rfl⟩ : syracuseStep 1446827 = 2170241) B2170241
theorem B5493683 : Blo 1445542 5493683 := bstep (se 1 (by rfl) ⟨4120262, by rfl⟩ : syracuseStep 5493683 = 8240525) B8240525
theorem B1446839 : Blo 1445542 1446839 := bstep (se 1 (by rfl) ⟨1085129, by rfl⟩ : syracuseStep 1446839 = 2170259) B2170259
theorem B1446859 : Blo 1445542 1446859 := bstep (se 1 (by rfl) ⟨1085144, by rfl⟩ : syracuseStep 1446859 = 2170289) B2170289
theorem B1446871 : Blo 1445542 1446871 := bstep (se 1 (by rfl) ⟨1085153, by rfl⟩ : syracuseStep 1446871 = 2170307) B2170307
theorem B1446891 : Blo 1445542 1446891 := bstep (se 1 (by rfl) ⟨1085168, by rfl⟩ : syracuseStep 1446891 = 2170337) B2170337
theorem B1446903 : Blo 1445542 1446903 := bstep (se 1 (by rfl) ⟨1085177, by rfl⟩ : syracuseStep 1446903 = 2170355) B2170355
theorem B1446923 : Blo 1445542 1446923 := bstep (se 1 (by rfl) ⟨1085192, by rfl⟩ : syracuseStep 1446923 = 2170385) B2170385
theorem B1627159 : Blo 1445542 1627159 := bstep (se 1 (by rfl) ⟨1220369, by rfl⟩ : syracuseStep 1627159 = 2440739) B2440739
theorem B1446935 : Blo 1445542 1446935 := bstep (se 1 (by rfl) ⟨1085201, by rfl⟩ : syracuseStep 1446935 = 2170403) B2170403
theorem B1446955 : Blo 1445542 1446955 := bstep (se 1 (by rfl) ⟨1085216, by rfl⟩ : syracuseStep 1446955 = 2170433) B2170433
theorem B1446967 : Blo 1445542 1446967 := bstep (se 1 (by rfl) ⟨1085225, by rfl⟩ : syracuseStep 1446967 = 2170451) B2170451
theorem B1446987 : Blo 1445542 1446987 := bstep (se 1 (by rfl) ⟨1085240, by rfl⟩ : syracuseStep 1446987 = 2170481) B2170481
theorem B1446999 : Blo 1445542 1446999 := bstep (se 1 (by rfl) ⟨1085249, by rfl⟩ : syracuseStep 1446999 = 2170499) B2170499
theorem B1447019 : Blo 1445542 1447019 := bstep (se 1 (by rfl) ⟨1085264, by rfl⟩ : syracuseStep 1447019 = 2170529) B2170529
theorem B1447031 : Blo 1445542 1447031 := bstep (se 1 (by rfl) ⟨1085273, by rfl⟩ : syracuseStep 1447031 = 2170547) B2170547
theorem B1447051 : Blo 1445542 1447051 := bstep (se 1 (by rfl) ⟨1085288, by rfl⟩ : syracuseStep 1447051 = 2170577) B2170577
theorem B1545355 : Blo 1445542 1545355 := bstep (se 1 (by rfl) ⟨1159016, by rfl⟩ : syracuseStep 1545355 = 2318033) B2318033
theorem B4117655 : Blo 1445542 4117655 := bstep (se 1 (by rfl) ⟨3088241, by rfl⟩ : syracuseStep 4117655 = 6176483) B6176483
theorem B1447063 : Blo 1445542 1447063 := bstep (se 1 (by rfl) ⟨1085297, by rfl⟩ : syracuseStep 1447063 = 2170595) B2170595
theorem B1447083 : Blo 1445542 1447083 := bstep (se 1 (by rfl) ⟨1085312, by rfl⟩ : syracuseStep 1447083 = 2170625) B2170625
theorem B1447095 : Blo 1445542 1447095 := bstep (se 1 (by rfl) ⟨1085321, by rfl⟩ : syracuseStep 1447095 = 2170643) B2170643
theorem B1627339 : Blo 1445542 1627339 := bstep (se 1 (by rfl) ⟨1220504, by rfl⟩ : syracuseStep 1627339 = 2441009) B2441009
theorem B1447115 : Blo 1445542 1447115 := bstep (se 1 (by rfl) ⟨1085336, by rfl⟩ : syracuseStep 1447115 = 2170673) B2170673
theorem B1447127 : Blo 1445542 1447127 := bstep (se 1 (by rfl) ⟨1085345, by rfl⟩ : syracuseStep 1447127 = 2170691) B2170691
theorem B1447147 : Blo 1445542 1447147 := bstep (se 1 (by rfl) ⟨1085360, by rfl⟩ : syracuseStep 1447147 = 2170721) B2170721
theorem B1447159 : Blo 1445542 1447159 := bstep (se 1 (by rfl) ⟨1085369, by rfl⟩ : syracuseStep 1447159 = 2170739) B2170739
theorem B1447179 : Blo 1445542 1447179 := bstep (se 1 (by rfl) ⟨1085384, by rfl⟩ : syracuseStep 1447179 = 2170769) B2170769
theorem B3298583 : Blo 1445542 3298583 := bstep (se 1 (by rfl) ⟨2473937, by rfl⟩ : syracuseStep 3298583 = 4947875) B4947875
theorem B1447191 : Blo 1445542 1447191 := bstep (se 1 (by rfl) ⟨1085393, by rfl⟩ : syracuseStep 1447191 = 2170787) B2170787
theorem B1447211 : Blo 1445542 1447211 := bstep (se 1 (by rfl) ⟨1085408, by rfl⟩ : syracuseStep 1447211 = 2170817) B2170817
theorem B1627447 : Blo 1445542 1627447 := bstep (se 1 (by rfl) ⟨1220585, by rfl⟩ : syracuseStep 1627447 = 2441171) B2441171
theorem B1447223 : Blo 1445542 1447223 := bstep (se 1 (by rfl) ⟨1085417, by rfl⟩ : syracuseStep 1447223 = 2170835) B2170835
theorem B1447243 : Blo 1445542 1447243 := bstep (se 1 (by rfl) ⟨1085432, by rfl⟩ : syracuseStep 1447243 = 2170865) B2170865
theorem B1447255 : Blo 1445542 1447255 := bstep (se 1 (by rfl) ⟨1085441, by rfl⟩ : syracuseStep 1447255 = 2170883) B2170883
theorem B4879709 : Blo 1445542 4879709 := bstep (se 3 (by rfl) ⟨914945, by rfl⟩ : syracuseStep 4879709 = 1829891) B1829891
theorem B1447275 : Blo 1445542 1447275 := bstep (se 1 (by rfl) ⟨1085456, by rfl⟩ : syracuseStep 1447275 = 2170913) B2170913
theorem B1447287 : Blo 1445542 1447287 := bstep (se 1 (by rfl) ⟨1085465, by rfl⟩ : syracuseStep 1447287 = 2170931) B2170931
theorem B1447307 : Blo 1445542 1447307 := bstep (se 1 (by rfl) ⟨1085480, by rfl⟩ : syracuseStep 1447307 = 2170961) B2170961
theorem B1447319 : Blo 1445542 1447319 := bstep (se 1 (by rfl) ⟨1085489, by rfl⟩ : syracuseStep 1447319 = 2170979) B2170979
theorem B1447339 : Blo 1445542 1447339 := bstep (se 1 (by rfl) ⟨1085504, by rfl⟩ : syracuseStep 1447339 = 2171009) B2171009
theorem B1447351 : Blo 1445542 1447351 := bstep (se 1 (by rfl) ⟨1085513, by rfl⟩ : syracuseStep 1447351 = 2171027) B2171027
theorem B1447371 : Blo 1445542 1447371 := bstep (se 1 (by rfl) ⟨1085528, by rfl⟩ : syracuseStep 1447371 = 2171057) B2171057
theorem B1447383 : Blo 1445542 1447383 := bstep (se 1 (by rfl) ⟨1085537, by rfl⟩ : syracuseStep 1447383 = 2171075) B2171075
theorem B1627627 : Blo 1445542 1627627 := bstep (se 1 (by rfl) ⟨1220720, by rfl⟩ : syracuseStep 1627627 = 2441441) B2441441
theorem B1447403 : Blo 1445542 1447403 := bstep (se 1 (by rfl) ⟨1085552, by rfl⟩ : syracuseStep 1447403 = 2171105) B2171105
theorem B1447415 : Blo 1445542 1447415 := bstep (se 1 (by rfl) ⟨1085561, by rfl⟩ : syracuseStep 1447415 = 2171123) B2171123
theorem B1447435 : Blo 1445542 1447435 := bstep (se 1 (by rfl) ⟨1085576, by rfl⟩ : syracuseStep 1447435 = 2171153) B2171153
theorem B26400269 : Blo 1445542 26400269 := bstep (se 3 (by rfl) ⟨4950050, by rfl⟩ : syracuseStep 26400269 = 9900101) B9900101
theorem B1447447 : Blo 1445542 1447447 := bstep (se 1 (by rfl) ⟨1085585, by rfl⟩ : syracuseStep 1447447 = 2171171) B2171171
theorem B2168345 : Blo 1445542 2168345 := bstep (se 2 (by rfl) ⟨813129, by rfl⟩ : syracuseStep 2168345 = 1626259) B1626259
theorem B1447467 : Blo 1445542 1447467 := bstep (se 1 (by rfl) ⟨1085600, by rfl⟩ : syracuseStep 1447467 = 2171201) B2171201
theorem B1447479 : Blo 1445542 1447479 := bstep (se 1 (by rfl) ⟨1085609, by rfl⟩ : syracuseStep 1447479 = 2171219) B2171219
theorem B5494337 : Blo 1445542 5494337 := bstep (se 2 (by rfl) ⟨2060376, by rfl⟩ : syracuseStep 5494337 = 4120753) B4120753
theorem B1447499 : Blo 1445542 1447499 := bstep (se 1 (by rfl) ⟨1085624, by rfl⟩ : syracuseStep 1447499 = 2171249) B2171249
theorem B1627735 : Blo 1445542 1627735 := bstep (se 1 (by rfl) ⟨1220801, by rfl⟩ : syracuseStep 1627735 = 2441603) B2441603
theorem B1447511 : Blo 1445542 1447511 := bstep (se 1 (by rfl) ⟨1085633, by rfl⟩ : syracuseStep 1447511 = 2171267) B2171267
theorem B1447531 : Blo 1445542 1447531 := bstep (se 1 (by rfl) ⟨1085648, by rfl⟩ : syracuseStep 1447531 = 2171297) B2171297
theorem B2168459 : Blo 1445542 2168459 := bstep (se 1 (by rfl) ⟨1626344, by rfl⟩ : syracuseStep 2168459 = 3252689) B3252689
theorem B2168471 : Blo 1445542 2168471 := bstep (se 1 (by rfl) ⟨1626353, by rfl⟩ : syracuseStep 2168471 = 3252707) B3252707
theorem B84580037 : Blo 1445542 84580037 := bstep (se 4 (by rfl) ⟨7929378, by rfl⟩ : syracuseStep 84580037 = 15858757) B15858757
theorem B2168537 : Blo 1445542 2168537 := bstep (se 2 (by rfl) ⟨813201, by rfl⟩ : syracuseStep 2168537 = 1626403) B1626403
theorem B3299059 : Blo 1445542 3299059 := bstep (se 1 (by rfl) ⟨2474294, by rfl⟩ : syracuseStep 3299059 = 4948589) B4948589
theorem B1627915 : Blo 1445542 1627915 := bstep (se 1 (by rfl) ⟨1220936, by rfl⟩ : syracuseStep 1627915 = 2441873) B2441873
theorem B2168651 : Blo 1445542 2168651 := bstep (se 1 (by rfl) ⟨1626488, by rfl⟩ : syracuseStep 2168651 = 3252977) B3252977
theorem B2168663 : Blo 1445542 2168663 := bstep (se 1 (by rfl) ⟨1626497, by rfl⟩ : syracuseStep 2168663 = 3252995) B3252995
theorem B7821157 : Blo 1445542 7821157 := bstep (se 4 (by rfl) ⟨733233, by rfl⟩ : syracuseStep 7821157 = 1466467) B1466467
theorem B1628023 : Blo 1445542 1628023 := bstep (se 1 (by rfl) ⟨1221017, by rfl⟩ : syracuseStep 1628023 = 2442035) B2442035
theorem B2168729 : Blo 1445542 2168729 := bstep (se 2 (by rfl) ⟨813273, by rfl⟩ : syracuseStep 2168729 = 1626547) B1626547
theorem B2168843 : Blo 1445542 2168843 := bstep (se 1 (by rfl) ⟨1626632, by rfl⟩ : syracuseStep 2168843 = 3253265) B3253265
theorem B2783243 : Blo 1445542 2783243 := bstep (se 1 (by rfl) ⟨2087432, by rfl⟩ : syracuseStep 2783243 = 4174865) B4174865
theorem B20846605 : Blo 1445542 20846605 := bstep (se 3 (by rfl) ⟨3908738, by rfl⟩ : syracuseStep 20846605 = 7817477) B7817477
theorem B18536465 : Blo 1445542 18536465 := bstep (se 2 (by rfl) ⟨6951174, by rfl⟩ : syracuseStep 18536465 = 13902349) B13902349
theorem B2168855 : Blo 1445542 2168855 := bstep (se 1 (by rfl) ⟨1626641, by rfl⟩ : syracuseStep 2168855 = 3253283) B3253283
theorem B1628203 : Blo 1445542 1628203 := bstep (se 1 (by rfl) ⟨1221152, by rfl⟩ : syracuseStep 1628203 = 2442305) B2442305
theorem B9271361 : Blo 1445542 9271361 := bstep (se 2 (by rfl) ⟨3476760, by rfl⟩ : syracuseStep 9271361 = 6953521) B6953521
theorem B5863499 : Blo 1445542 5863499 := bstep (se 1 (by rfl) ⟨4397624, by rfl⟩ : syracuseStep 5863499 = 8795249) B8795249
theorem B2168921 : Blo 1445542 2168921 := bstep (se 2 (by rfl) ⟨813345, by rfl⟩ : syracuseStep 2168921 = 1626691) B1626691
theorem B7321751 : Blo 1445542 7321751 := bstep (se 1 (by rfl) ⟨5491313, by rfl⟩ : syracuseStep 7321751 = 10982627) B10982627
theorem B1628311 : Blo 1445542 1628311 := bstep (se 1 (by rfl) ⟨1221233, by rfl⟩ : syracuseStep 1628311 = 2442467) B2442467
theorem B6174893 : Blo 1445542 6174893 := bstep (se 3 (by rfl) ⟨1157792, by rfl⟩ : syracuseStep 6174893 = 2315585) B2315585
theorem B1980619 : Blo 1445542 1980619 := bstep (se 1 (by rfl) ⟨1485464, by rfl⟩ : syracuseStep 1980619 = 2970929) B2970929
theorem B4946123 : Blo 1445542 4946123 := bstep (se 1 (by rfl) ⟨3709592, by rfl⟩ : syracuseStep 4946123 = 7419185) B7419185
theorem B15636685 : Blo 1445542 15636685 := bstep (se 3 (by rfl) ⟨2931878, by rfl⟩ : syracuseStep 15636685 = 5863757) B5863757
theorem B2169035 : Blo 1445542 2169035 := bstep (se 1 (by rfl) ⟨1626776, by rfl⟩ : syracuseStep 2169035 = 3253553) B3253553
theorem B2169047 : Blo 1445542 2169047 := bstep (se 1 (by rfl) ⟨1626785, by rfl⟩ : syracuseStep 2169047 = 3253571) B3253571
theorem B9271513 : Blo 1445542 9271513 := bstep (se 2 (by rfl) ⟨3476817, by rfl⟩ : syracuseStep 9271513 = 6953635) B6953635
theorem B5863697 : Blo 1445542 5863697 := bstep (se 2 (by rfl) ⟨2198886, by rfl⟩ : syracuseStep 5863697 = 4397773) B4397773
theorem B2169113 : Blo 1445542 2169113 := bstep (se 2 (by rfl) ⟨813417, by rfl⟩ : syracuseStep 2169113 = 1626835) B1626835
theorem B20855141 : Blo 1445542 20855141 := bstep (se 4 (by rfl) ⟨1955169, by rfl⟩ : syracuseStep 20855141 = 3910339) B3910339
theorem B2169227 : Blo 1445542 2169227 := bstep (se 1 (by rfl) ⟨1626920, by rfl⟩ : syracuseStep 2169227 = 3253841) B3253841
theorem B2169239 : Blo 1445542 2169239 := bstep (se 1 (by rfl) ⟨1626929, by rfl⟩ : syracuseStep 2169239 = 3253859) B3253859
theorem B4880843 : Blo 1445542 4880843 := bstep (se 1 (by rfl) ⟨3660632, by rfl⟩ : syracuseStep 4880843 = 7321265) B7321265
theorem B4118987 : Blo 1445542 4118987 := bstep (se 1 (by rfl) ⟨3089240, by rfl⟩ : syracuseStep 4118987 = 6178481) B6178481
theorem B2169305 : Blo 1445542 2169305 := bstep (se 2 (by rfl) ⟨813489, by rfl⟩ : syracuseStep 2169305 = 1626979) B1626979
theorem B2169419 : Blo 1445542 2169419 := bstep (se 1 (by rfl) ⟨1627064, by rfl⟩ : syracuseStep 2169419 = 3254129) B3254129
theorem B2439767 : Blo 1445542 2439767 := bstep (se 1 (by rfl) ⟨1829825, by rfl⟩ : syracuseStep 2439767 = 3659651) B3659651
theorem B2169431 : Blo 1445542 2169431 := bstep (se 1 (by rfl) ⟨1627073, by rfl⟩ : syracuseStep 2169431 = 3254147) B3254147
theorem B2931329 : Blo 1445542 2931329 := bstep (se 2 (by rfl) ⟨1099248, by rfl⟩ : syracuseStep 2931329 = 2198497) B2198497
theorem B3299969 : Blo 1445542 3299969 := bstep (se 2 (by rfl) ⟨1237488, by rfl⟩ : syracuseStep 3299969 = 2474977) B2474977
theorem B2169497 : Blo 1445542 2169497 := bstep (se 2 (by rfl) ⟨813561, by rfl⟩ : syracuseStep 2169497 = 1627123) B1627123
theorem B13367987 : Blo 1445542 13367987 := bstep (se 1 (by rfl) ⟨10025990, by rfl⟩ : syracuseStep 13367987 = 20051981) B20051981
theorem B3660491 : Blo 1445542 3660491 := bstep (se 1 (by rfl) ⟨2745368, by rfl⟩ : syracuseStep 3660491 = 5490737) B5490737
theorem B3300043 : Blo 1445542 3300043 := bstep (se 1 (by rfl) ⟨2475032, by rfl⟩ : syracuseStep 3300043 = 4950065) B4950065
theorem B2439895 : Blo 1445542 2439895 := bstep (se 1 (by rfl) ⟨1829921, by rfl⟩ : syracuseStep 2439895 = 3659843) B3659843
theorem B4881113 : Blo 1445542 4881113 := bstep (se 2 (by rfl) ⟨1830417, by rfl⟩ : syracuseStep 4881113 = 3660835) B3660835
theorem B2169611 : Blo 1445542 2169611 := bstep (se 1 (by rfl) ⟨1627208, by rfl⟩ : syracuseStep 2169611 = 3254417) B3254417
theorem B2169623 : Blo 1445542 2169623 := bstep (se 1 (by rfl) ⟨1627217, by rfl⟩ : syracuseStep 2169623 = 3254435) B3254435
theorem B5495597 : Blo 1445542 5495597 := bstep (se 3 (by rfl) ⟨1030424, by rfl⟩ : syracuseStep 5495597 = 2060849) B2060849
theorem B5495627 : Blo 1445542 5495627 := bstep (se 1 (by rfl) ⟨4121720, by rfl⟩ : syracuseStep 5495627 = 8243441) B8243441
theorem B2169689 : Blo 1445542 2169689 := bstep (se 2 (by rfl) ⟨813633, by rfl⟩ : syracuseStep 2169689 = 1627267) B1627267
theorem B2931571 : Blo 1445542 2931571 := bstep (se 1 (by rfl) ⟨2198678, by rfl⟩ : syracuseStep 2931571 = 4397357) B4397357
theorem B1465291 : Blo 1445542 1465291 := bstep (se 1 (by rfl) ⟨1098968, by rfl⟩ : syracuseStep 1465291 = 2197937) B2197937
theorem B2169803 : Blo 1445542 2169803 := bstep (se 1 (by rfl) ⟨1627352, by rfl⟩ : syracuseStep 2169803 = 3254705) B3254705
theorem B2169815 : Blo 1445542 2169815 := bstep (se 1 (by rfl) ⟨1627361, by rfl⟩ : syracuseStep 2169815 = 3254723) B3254723
theorem B2169881 : Blo 1445542 2169881 := bstep (se 2 (by rfl) ⟨813705, by rfl⟩ : syracuseStep 2169881 = 1627411) B1627411
theorem B83377187 : Blo 1445542 83377187 := bstep (se 1 (by rfl) ⟨62532890, by rfl⟩ : syracuseStep 83377187 = 125065781) B125065781
theorem B13188197 : Blo 1445542 13188197 := bstep (se 4 (by rfl) ⟨1236393, by rfl⟩ : syracuseStep 13188197 = 2472787) B2472787
theorem B2169995 : Blo 1445542 2169995 := bstep (se 1 (by rfl) ⟨1627496, by rfl⟩ : syracuseStep 2169995 = 3254993) B3254993
theorem B2170007 : Blo 1445542 2170007 := bstep (se 1 (by rfl) ⟨1627505, by rfl⟩ : syracuseStep 2170007 = 3255011) B3255011
theorem B2170073 : Blo 1445542 2170073 := bstep (se 2 (by rfl) ⟨813777, by rfl⟩ : syracuseStep 2170073 = 1627555) B1627555
theorem B5864669 : Blo 1445542 5864669 := bstep (se 3 (by rfl) ⟨1099625, by rfl⟩ : syracuseStep 5864669 = 2199251) B2199251
theorem B2678039 : Blo 1445542 2678039 := bstep (se 1 (by rfl) ⟨2008529, by rfl⟩ : syracuseStep 2678039 = 4017059) B4017059
theorem B4177217 : Blo 1445542 4177217 := bstep (se 2 (by rfl) ⟨1566456, by rfl⟩ : syracuseStep 4177217 = 3132913) B3132913
theorem B2440523 : Blo 1445542 2440523 := bstep (se 1 (by rfl) ⟨1830392, by rfl⟩ : syracuseStep 2440523 = 3660785) B3660785
theorem B2170187 : Blo 1445542 2170187 := bstep (se 1 (by rfl) ⟨1627640, by rfl⟩ : syracuseStep 2170187 = 3255281) B3255281
theorem B2170199 : Blo 1445542 2170199 := bstep (se 1 (by rfl) ⟨1627649, by rfl⟩ : syracuseStep 2170199 = 3255299) B3255299
theorem B4881815 : Blo 1445542 4881815 := bstep (se 1 (by rfl) ⟨3661361, by rfl⟩ : syracuseStep 4881815 = 7322723) B7322723
theorem B2170265 : Blo 1445542 2170265 := bstep (se 2 (by rfl) ⟨813849, by rfl⟩ : syracuseStep 2170265 = 1627699) B1627699
theorem B2440651 : Blo 1445542 2440651 := bstep (se 1 (by rfl) ⟨1830488, by rfl⟩ : syracuseStep 2440651 = 3660977) B3660977
theorem B2170379 : Blo 1445542 2170379 := bstep (se 1 (by rfl) ⟨1627784, by rfl⟩ : syracuseStep 2170379 = 3255569) B3255569
theorem B2170391 : Blo 1445542 2170391 := bstep (se 1 (by rfl) ⟨1627793, by rfl⟩ : syracuseStep 2170391 = 3255587) B3255587
theorem B2440793 : Blo 1445542 2440793 := bstep (se 2 (by rfl) ⟨915297, by rfl⟩ : syracuseStep 2440793 = 1830595) B1830595
theorem B2170457 : Blo 1445542 2170457 := bstep (se 2 (by rfl) ⟨813921, by rfl⟩ : syracuseStep 2170457 = 1627843) B1627843
theorem B3661463 : Blo 1445542 3661463 := bstep (se 1 (by rfl) ⟨2746097, by rfl⟩ : syracuseStep 3661463 = 5492195) B5492195
theorem B2170571 : Blo 1445542 2170571 := bstep (se 1 (by rfl) ⟨1627928, by rfl⟩ : syracuseStep 2170571 = 3255857) B3255857
theorem B12533453 : Blo 1445542 12533453 := bstep (se 3 (by rfl) ⟨2350022, by rfl⟩ : syracuseStep 12533453 = 4700045) B4700045
theorem B2170583 : Blo 1445542 2170583 := bstep (se 1 (by rfl) ⟨1627937, by rfl⟩ : syracuseStep 2170583 = 3255875) B3255875
theorem B11722457 : Blo 1445542 11722457 := bstep (se 2 (by rfl) ⟨4395921, by rfl⟩ : syracuseStep 11722457 = 8791843) B8791843
theorem B2440921 : Blo 1445542 2440921 := bstep (se 2 (by rfl) ⟨915345, by rfl⟩ : syracuseStep 2440921 = 1830691) B1830691
theorem B2170649 : Blo 1445542 2170649 := bstep (se 2 (by rfl) ⟨813993, by rfl⟩ : syracuseStep 2170649 = 1627987) B1627987
theorem B3907379 : Blo 1445542 3907379 := bstep (se 1 (by rfl) ⟨2930534, by rfl⟩ : syracuseStep 3907379 = 5861069) B5861069
theorem B2170763 : Blo 1445542 2170763 := bstep (se 1 (by rfl) ⟨1628072, by rfl⟩ : syracuseStep 2170763 = 3256145) B3256145
theorem B7929751 : Blo 1445542 7929751 := bstep (se 1 (by rfl) ⟨5947313, by rfl⟩ : syracuseStep 7929751 = 11894627) B11894627
theorem B2170775 : Blo 1445542 2170775 := bstep (se 1 (by rfl) ⟨1628081, by rfl⟩ : syracuseStep 2170775 = 3256163) B3256163
theorem B18087857 : Blo 1445542 18087857 := bstep (se 2 (by rfl) ⟨6782946, by rfl⟩ : syracuseStep 18087857 = 13565893) B13565893
theorem B4882355 : Blo 1445542 4882355 := bstep (se 1 (by rfl) ⟨3661766, by rfl⟩ : syracuseStep 4882355 = 7323533) B7323533
theorem B2170841 : Blo 1445542 2170841 := bstep (se 2 (by rfl) ⟨814065, by rfl⟩ : syracuseStep 2170841 = 1628131) B1628131
theorem B8798219 : Blo 1445542 8798219 := bstep (se 1 (by rfl) ⟨6598664, by rfl⟩ : syracuseStep 8798219 = 13197329) B13197329
theorem B2170895 : Blo 1445542 2170895 := bstep (se 1 (by rfl) ⟨1628171, by rfl⟩ : syracuseStep 2170895 = 3256343) B3256343
theorem B27795473 : Blo 1445542 27795473 := bstep (se 2 (by rfl) ⟨10423302, by rfl⟩ : syracuseStep 27795473 = 20846605) B20846605
theorem B13910039 : Blo 1445542 13910039 := bstep (se 1 (by rfl) ⟨10432529, by rfl⟩ : syracuseStep 13910039 = 20865059) B20865059
theorem B2170937 : Blo 1445542 2170937 := bstep (se 2 (by rfl) ⟨814101, by rfl⟩ : syracuseStep 2170937 = 1628203) B1628203
theorem B3522619 : Blo 1445542 3522619 := bstep (se 1 (by rfl) ⟨2641964, by rfl⟩ : syracuseStep 3522619 = 5283929) B5283929
theorem B3907703 : Blo 1445542 3907703 := bstep (se 1 (by rfl) ⟨2930777, by rfl⟩ : syracuseStep 3907703 = 5861555) B5861555
theorem B2171015 : Blo 1445542 2171015 := bstep (se 1 (by rfl) ⟨1628261, by rfl⟩ : syracuseStep 2171015 = 3256523) B3256523
theorem B2171051 : Blo 1445542 2171051 := bstep (se 1 (by rfl) ⟨1628288, by rfl⟩ : syracuseStep 2171051 = 3256577) B3256577
theorem B2171081 : Blo 1445542 2171081 := bstep (se 2 (by rfl) ⟨814155, by rfl⟩ : syracuseStep 2171081 = 1628311) B1628311
theorem B3662081 : Blo 1445542 3662081 := bstep (se 2 (by rfl) ⟨1373280, by rfl⟩ : syracuseStep 3662081 = 2746561) B2746561
theorem B35168525 : Blo 1445542 35168525 := bstep (se 3 (by rfl) ⟨6594098, by rfl⟩ : syracuseStep 35168525 = 13188197) B13188197
theorem B20848913 : Blo 1445542 20848913 := bstep (se 2 (by rfl) ⟨7818342, by rfl⟩ : syracuseStep 20848913 = 15636685) B15636685
theorem B12362017 : Blo 1445542 12362017 := bstep (se 2 (by rfl) ⟨4635756, by rfl⟩ : syracuseStep 12362017 = 9271513) B9271513
theorem B2441515 : Blo 1445542 2441515 := bstep (se 1 (by rfl) ⟨1831136, by rfl⟩ : syracuseStep 2441515 = 3662273) B3662273
theorem B2171195 : Blo 1445542 2171195 := bstep (se 1 (by rfl) ⟨1628396, by rfl⟩ : syracuseStep 2171195 = 3256793) B3256793
theorem B7324019 : Blo 1445542 7324019 := bstep (se 1 (by rfl) ⟨5493014, by rfl⟩ : syracuseStep 7324019 = 10986029) B10986029
theorem B128647541 : Blo 1445542 128647541 := bstep (se 5 (by rfl) ⟨6030353, by rfl⟩ : syracuseStep 128647541 = 12060707) B12060707
theorem B3252599 : Blo 1445542 3252599 := bstep (se 1 (by rfl) ⟨2439449, by rfl⟩ : syracuseStep 3252599 = 4878899) B4878899
theorem B2171255 : Blo 1445542 2171255 := bstep (se 1 (by rfl) ⟨1628441, by rfl⟩ : syracuseStep 2171255 = 3256883) B3256883
theorem B2171279 : Blo 1445542 2171279 := bstep (se 1 (by rfl) ⟨1628459, by rfl⟩ : syracuseStep 2171279 = 3256919) B3256919
theorem B23462291 : Blo 1445542 23462291 := bstep (se 1 (by rfl) ⟨17596718, by rfl⟩ : syracuseStep 23462291 = 35193437) B35193437
theorem B4882841 : Blo 1445542 4882841 := bstep (se 2 (by rfl) ⟨1831065, by rfl⟩ : syracuseStep 4882841 = 3662131) B3662131
theorem B2744761 : Blo 1445542 2744761 := bstep (se 2 (by rfl) ⟨1029285, by rfl⟩ : syracuseStep 2744761 = 2058571) B2058571
theorem B2441657 : Blo 1445542 2441657 := bstep (se 2 (by rfl) ⟨915621, by rfl⟩ : syracuseStep 2441657 = 1831243) B1831243
theorem B13189661 : Blo 1445542 13189661 := bstep (se 3 (by rfl) ⟨2473061, by rfl⟩ : syracuseStep 13189661 = 4946123) B4946123
theorem B3252779 : Blo 1445542 3252779 := bstep (se 1 (by rfl) ⟨2439584, by rfl⟩ : syracuseStep 3252779 = 4879169) B4879169
theorem B3662455 : Blo 1445542 3662455 := bstep (se 1 (by rfl) ⟨2746841, by rfl⟩ : syracuseStep 3662455 = 5493683) B5493683
theorem B2745103 : Blo 1445542 2745103 := bstep (se 1 (by rfl) ⟨2058827, by rfl⟩ : syracuseStep 2745103 = 4117655) B4117655
theorem B4948751 : Blo 1445542 4948751 := bstep (se 1 (by rfl) ⟨3711563, by rfl⟩ : syracuseStep 4948751 = 7423127) B7423127
theorem B7324505 : Blo 1445542 7324505 := bstep (se 2 (by rfl) ⟨2746689, by rfl⟩ : syracuseStep 7324505 = 5493379) B5493379
theorem B3130247 : Blo 1445542 3130247 := bstep (se 1 (by rfl) ⟨2347685, by rfl⟩ : syracuseStep 3130247 = 4695371) B4695371
theorem B3253139 : Blo 1445542 3253139 := bstep (se 1 (by rfl) ⟨2439854, by rfl⟩ : syracuseStep 3253139 = 4879709) B4879709
theorem B4400057 : Blo 1445542 4400057 := bstep (se 2 (by rfl) ⟨1650021, by rfl⟩ : syracuseStep 4400057 = 3300043) B3300043
theorem B3253193 : Blo 1445542 3253193 := bstep (se 2 (by rfl) ⟨1219947, by rfl⟩ : syracuseStep 3253193 = 2439895) B2439895
theorem B3662891 : Blo 1445542 3662891 := bstep (se 1 (by rfl) ⟨2747168, by rfl⟩ : syracuseStep 3662891 = 5494337) B5494337
theorem B9266237 : Blo 1445542 9266237 := bstep (se 3 (by rfl) ⟨1737419, by rfl⟩ : syracuseStep 9266237 = 3474839) B3474839
theorem B4883543 : Blo 1445542 4883543 := bstep (se 1 (by rfl) ⟨3662657, by rfl⟩ : syracuseStep 4883543 = 7325315) B7325315
theorem B3474551 : Blo 1445542 3474551 := bstep (se 1 (by rfl) ⟨2605913, by rfl⟩ : syracuseStep 3474551 = 5211827) B5211827
theorem B2442359 : Blo 1445542 2442359 := bstep (se 1 (by rfl) ⟨1831769, by rfl⟩ : syracuseStep 2442359 = 3663539) B3663539
theorem B56386691 : Blo 1445542 56386691 := bstep (se 1 (by rfl) ⟨42290018, by rfl⟩ : syracuseStep 56386691 = 84580037) B84580037
theorem B5211337 : Blo 1445542 5211337 := bstep (se 2 (by rfl) ⟨1954251, by rfl⟩ : syracuseStep 5211337 = 3908503) B3908503
theorem B4121857 : Blo 1445542 4121857 := bstep (se 2 (by rfl) ⟨1545696, by rfl⟩ : syracuseStep 4121857 = 3091393) B3091393
theorem B3908999 : Blo 1445542 3908999 := bstep (se 1 (by rfl) ⟨2931749, by rfl⟩ : syracuseStep 3908999 = 5863499) B5863499
theorem B3909131 : Blo 1445542 3909131 := bstep (se 1 (by rfl) ⟨2931848, by rfl⟩ : syracuseStep 3909131 = 5863697) B5863697
theorem B5948957 : Blo 1445542 5948957 := bstep (se 3 (by rfl) ⟨1115429, by rfl⟩ : syracuseStep 5948957 = 2230859) B2230859
theorem B4884029 : Blo 1445542 4884029 := bstep (se 3 (by rfl) ⟨915755, by rfl⟩ : syracuseStep 4884029 = 1831511) B1831511
theorem B13903427 : Blo 1445542 13903427 := bstep (se 1 (by rfl) ⟨10427570, by rfl⟩ : syracuseStep 13903427 = 20855141) B20855141
theorem B3253895 : Blo 1445542 3253895 := bstep (se 1 (by rfl) ⟨2440421, by rfl⟩ : syracuseStep 3253895 = 4880843) B4880843
theorem B2745991 : Blo 1445542 2745991 := bstep (se 1 (by rfl) ⟨2059493, by rfl⟩ : syracuseStep 2745991 = 4118987) B4118987
theorem B3344171 : Blo 1445542 3344171 := bstep (se 1 (by rfl) ⟨2508128, by rfl⟩ : syracuseStep 3344171 = 5016257) B5016257
theorem B16484147 : Blo 1445542 16484147 := bstep (se 1 (by rfl) ⟨12363110, by rfl⟩ : syracuseStep 16484147 = 24726221) B24726221
theorem B3254075 : Blo 1445542 3254075 := bstep (se 1 (by rfl) ⟨2440556, by rfl⟩ : syracuseStep 3254075 = 4881113) B4881113
theorem B39585611 : Blo 1445542 39585611 := bstep (se 1 (by rfl) ⟨29689208, by rfl⟩ : syracuseStep 39585611 = 59378417) B59378417
theorem B3663731 : Blo 1445542 3663731 := bstep (se 1 (by rfl) ⟨2747798, by rfl⟩ : syracuseStep 3663731 = 5495597) B5495597
theorem B3663751 : Blo 1445542 3663751 := bstep (se 1 (by rfl) ⟨2747813, by rfl⟩ : syracuseStep 3663751 = 5495627) B5495627
theorem B10979225 : Blo 1445542 10979225 := bstep (se 2 (by rfl) ⟨4117209, by rfl⟩ : syracuseStep 10979225 = 8234419) B8234419
theorem B3254201 : Blo 1445542 3254201 := bstep (se 2 (by rfl) ⟨1220325, by rfl⟩ : syracuseStep 3254201 = 2440651) B2440651
theorem B7817219 : Blo 1445542 7817219 := bstep (se 1 (by rfl) ⟨5862914, by rfl⟩ : syracuseStep 7817219 = 11725829) B11725829
theorem B55584791 : Blo 1445542 55584791 := bstep (se 1 (by rfl) ⟨41688593, by rfl⟩ : syracuseStep 55584791 = 83377187) B83377187
theorem B3909779 : Blo 1445542 3909779 := bstep (se 1 (by rfl) ⟨2932334, by rfl⟩ : syracuseStep 3909779 = 5864669) B5864669
theorem B3664025 : Blo 1445542 3664025 := bstep (se 2 (by rfl) ⟨1374009, by rfl⟩ : syracuseStep 3664025 = 2748019) B2748019
theorem B3254543 : Blo 1445542 3254543 := bstep (se 1 (by rfl) ⟨2440907, by rfl⟩ : syracuseStep 3254543 = 4881815) B4881815
theorem B3254561 : Blo 1445542 3254561 := bstep (se 2 (by rfl) ⟨1220460, by rfl⟩ : syracuseStep 3254561 = 2440921) B2440921
theorem B3254903 : Blo 1445542 3254903 := bstep (se 1 (by rfl) ⟨2441177, by rfl⟩ : syracuseStep 3254903 = 4882355) B4882355
theorem B1829623 : Blo 1445542 1829623 := bstep (se 1 (by rfl) ⟨1372217, by rfl⟩ : syracuseStep 1829623 = 2744435) B2744435
theorem B2059015 : Blo 1445542 2059015 := bstep (se 1 (by rfl) ⟨1544261, by rfl⟩ : syracuseStep 2059015 = 3088523) B3088523
theorem B3255083 : Blo 1445542 3255083 := bstep (se 1 (by rfl) ⟨2441312, by rfl⟩ : syracuseStep 3255083 = 4882625) B4882625
theorem B3910459 : Blo 1445542 3910459 := bstep (se 1 (by rfl) ⟨2932844, by rfl⟩ : syracuseStep 3910459 = 5865689) B5865689
theorem B26405747 : Blo 1445542 26405747 := bstep (se 1 (by rfl) ⟨19804310, by rfl⟩ : syracuseStep 26405747 = 39608621) B39608621
theorem B7326611 : Blo 1445542 7326611 := bstep (se 1 (by rfl) ⟨5494958, by rfl⟩ : syracuseStep 7326611 = 10989917) B10989917
theorem B3091385 : Blo 1445542 3091385 := bstep (se 2 (by rfl) ⟨1159269, by rfl⟩ : syracuseStep 3091385 = 2318539) B2318539
theorem B4885433 : Blo 1445542 4885433 := bstep (se 2 (by rfl) ⟨1832037, by rfl⟩ : syracuseStep 4885433 = 3664075) B3664075
theorem B1829947 : Blo 1445542 1829947 := bstep (se 1 (by rfl) ⟨1372460, by rfl⟩ : syracuseStep 1829947 = 2744921) B2744921
theorem B8236151 : Blo 1445542 8236151 := bstep (se 1 (by rfl) ⟨6177113, by rfl⟩ : syracuseStep 8236151 = 12354227) B12354227
theorem B7523447 : Blo 1445542 7523447 := bstep (se 1 (by rfl) ⟨5642585, by rfl⟩ : syracuseStep 7523447 = 11285171) B11285171
theorem B3255443 : Blo 1445542 3255443 := bstep (se 1 (by rfl) ⟨2441582, by rfl⟩ : syracuseStep 3255443 = 4883165) B4883165
theorem B3476627 : Blo 1445542 3476627 := bstep (se 1 (by rfl) ⟨2607470, by rfl⟩ : syracuseStep 3476627 = 5214941) B5214941
theorem B3255497 : Blo 1445542 3255497 := bstep (se 2 (by rfl) ⟨1220811, by rfl⟩ : syracuseStep 3255497 = 2441623) B2441623
theorem B7318835 : Blo 1445542 7318835 := bstep (se 1 (by rfl) ⟨5489126, by rfl⟩ : syracuseStep 7318835 = 10978253) B10978253
theorem B8236403 : Blo 1445542 8236403 := bstep (se 1 (by rfl) ⟨6177302, by rfl⟩ : syracuseStep 8236403 = 12354605) B12354605
theorem B2747783 : Blo 1445542 2747783 := bstep (se 1 (by rfl) ⟨2060837, by rfl⟩ : syracuseStep 2747783 = 4121675) B4121675
theorem B10988945 : Blo 1445542 10988945 := bstep (se 2 (by rfl) ⟨4120854, by rfl⟩ : syracuseStep 10988945 = 8241709) B8241709
theorem B2059835 : Blo 1445542 2059835 := bstep (se 1 (by rfl) ⟨1544876, by rfl⟩ : syracuseStep 2059835 = 3089753) B3089753
theorem B7319159 : Blo 1445542 7319159 := bstep (se 1 (by rfl) ⟨5489369, by rfl⟩ : syracuseStep 7319159 = 10978739) B10978739
theorem B17600179 : Blo 1445542 17600179 := bstep (se 1 (by rfl) ⟨13200134, by rfl⟩ : syracuseStep 17600179 = 26400269) B26400269
theorem B1445563 : Blo 1445542 1445563 := bstep (se 1 (by rfl) ⟨1084172, by rfl⟩ : syracuseStep 1445563 = 2168345) B2168345
theorem B28552933 : Blo 1445542 28552933 := bstep (se 4 (by rfl) ⟨2676837, by rfl⟩ : syracuseStep 28552933 = 5353675) B5353675
theorem B10563301 : Blo 1445542 10563301 := bstep (se 4 (by rfl) ⟨990309, by rfl⟩ : syracuseStep 10563301 = 1980619) B1980619
theorem B1445639 : Blo 1445542 1445639 := bstep (se 1 (by rfl) ⟨1084229, by rfl⟩ : syracuseStep 1445639 = 2168459) B2168459
theorem B1445647 : Blo 1445542 1445647 := bstep (se 1 (by rfl) ⟨1084235, by rfl⟩ : syracuseStep 1445647 = 2168471) B2168471
theorem B10981169 : Blo 1445542 10981169 := bstep (se 2 (by rfl) ⟨4117938, by rfl⟩ : syracuseStep 10981169 = 8235877) B8235877
theorem B1445691 : Blo 1445542 1445691 := bstep (se 1 (by rfl) ⟨1084268, by rfl⟩ : syracuseStep 1445691 = 2168537) B2168537
theorem B1445767 : Blo 1445542 1445767 := bstep (se 1 (by rfl) ⟨1084325, by rfl⟩ : syracuseStep 1445767 = 2168651) B2168651
theorem B3256199 : Blo 1445542 3256199 := bstep (se 1 (by rfl) ⟨2442149, by rfl⟩ : syracuseStep 3256199 = 4884299) B4884299
theorem B1445775 : Blo 1445542 1445775 := bstep (se 1 (by rfl) ⟨1084331, by rfl⟩ : syracuseStep 1445775 = 2168663) B2168663
theorem B1953721 : Blo 1445542 1953721 := bstep (se 2 (by rfl) ⟨732645, by rfl⟩ : syracuseStep 1953721 = 1465291) B1465291
theorem B3477433 : Blo 1445542 3477433 := bstep (se 2 (by rfl) ⟨1304037, by rfl⟩ : syracuseStep 3477433 = 2608075) B2608075
theorem B1445819 : Blo 1445542 1445819 := bstep (se 1 (by rfl) ⟨1084364, by rfl⟩ : syracuseStep 1445819 = 2168729) B2168729
theorem B1445895 : Blo 1445542 1445895 := bstep (se 1 (by rfl) ⟨1084421, by rfl⟩ : syracuseStep 1445895 = 2168843) B2168843
theorem B1855495 : Blo 1445542 1855495 := bstep (se 1 (by rfl) ⟨1391621, by rfl⟩ : syracuseStep 1855495 = 2783243) B2783243
theorem B1830919 : Blo 1445542 1830919 := bstep (se 1 (by rfl) ⟨1373189, by rfl⟩ : syracuseStep 1830919 = 2746379) B2746379
theorem B12357643 : Blo 1445542 12357643 := bstep (se 1 (by rfl) ⟨9268232, by rfl⟩ : syracuseStep 12357643 = 18536465) B18536465
theorem B1445903 : Blo 1445542 1445903 := bstep (se 1 (by rfl) ⟨1084427, by rfl⟩ : syracuseStep 1445903 = 2168855) B2168855
theorem B6180907 : Blo 1445542 6180907 := bstep (se 1 (by rfl) ⟨4635680, by rfl⟩ : syracuseStep 6180907 = 9271361) B9271361
theorem B1445947 : Blo 1445542 1445947 := bstep (se 1 (by rfl) ⟨1084460, by rfl⟩ : syracuseStep 1445947 = 2168921) B2168921
theorem B3256379 : Blo 1445542 3256379 := bstep (se 1 (by rfl) ⟨2442284, by rfl⟩ : syracuseStep 3256379 = 4884569) B4884569
theorem B4116595 : Blo 1445542 4116595 := bstep (se 1 (by rfl) ⟨3087446, by rfl⟩ : syracuseStep 4116595 = 6174893) B6174893
theorem B1446023 : Blo 1445542 1446023 := bstep (se 1 (by rfl) ⟨1084517, by rfl⟩ : syracuseStep 1446023 = 2169035) B2169035
theorem B1446031 : Blo 1445542 1446031 := bstep (se 1 (by rfl) ⟨1084523, by rfl⟩ : syracuseStep 1446031 = 2169047) B2169047
theorem B2060473 : Blo 1445542 2060473 := bstep (se 2 (by rfl) ⟨772677, by rfl⟩ : syracuseStep 2060473 = 1545355) B1545355
theorem B3256505 : Blo 1445542 3256505 := bstep (se 2 (by rfl) ⟨1221189, by rfl⟩ : syracuseStep 3256505 = 2442379) B2442379
theorem B1446075 : Blo 1445542 1446075 := bstep (se 1 (by rfl) ⟨1084556, by rfl⟩ : syracuseStep 1446075 = 2169113) B2169113
theorem B1446151 : Blo 1445542 1446151 := bstep (se 1 (by rfl) ⟨1084613, by rfl⟩ : syracuseStep 1446151 = 2169227) B2169227
theorem B1446159 : Blo 1445542 1446159 := bstep (se 1 (by rfl) ⟨1084619, by rfl⟩ : syracuseStep 1446159 = 2169239) B2169239
theorem B2060587 : Blo 1445542 2060587 := bstep (se 1 (by rfl) ⟨1545440, by rfl⟩ : syracuseStep 2060587 = 3090881) B3090881
theorem B1446203 : Blo 1445542 1446203 := bstep (se 1 (by rfl) ⟨1084652, by rfl⟩ : syracuseStep 1446203 = 2169305) B2169305
theorem B1446279 : Blo 1445542 1446279 := bstep (se 1 (by rfl) ⟨1084709, by rfl⟩ : syracuseStep 1446279 = 2169419) B2169419
theorem B1626511 : Blo 1445542 1626511 := bstep (se 1 (by rfl) ⟨1219883, by rfl⟩ : syracuseStep 1626511 = 2439767) B2439767
theorem B1446287 : Blo 1445542 1446287 := bstep (se 1 (by rfl) ⟨1084715, by rfl⟩ : syracuseStep 1446287 = 2169431) B2169431
theorem B1954219 : Blo 1445542 1954219 := bstep (se 1 (by rfl) ⟨1465664, by rfl⟩ : syracuseStep 1954219 = 2931329) B2931329
theorem B2199979 : Blo 1445542 2199979 := bstep (se 1 (by rfl) ⟨1649984, by rfl⟩ : syracuseStep 2199979 = 3299969) B3299969
theorem B1831339 : Blo 1445542 1831339 := bstep (se 1 (by rfl) ⟨1373504, by rfl⟩ : syracuseStep 1831339 = 2747009) B2747009
theorem B1446331 : Blo 1445542 1446331 := bstep (se 1 (by rfl) ⟨1084748, by rfl⟩ : syracuseStep 1446331 = 2169497) B2169497
theorem B1446407 : Blo 1445542 1446407 := bstep (se 1 (by rfl) ⟨1084805, by rfl⟩ : syracuseStep 1446407 = 2169611) B2169611
theorem B1446415 : Blo 1445542 1446415 := bstep (se 1 (by rfl) ⟨1084811, by rfl⟩ : syracuseStep 1446415 = 2169623) B2169623
theorem B2060815 : Blo 1445542 2060815 := bstep (se 1 (by rfl) ⟨1545611, by rfl⟩ : syracuseStep 2060815 = 3091223) B3091223
theorem B3256847 : Blo 1445542 3256847 := bstep (se 1 (by rfl) ⟨2442635, by rfl⟩ : syracuseStep 3256847 = 4885271) B4885271
theorem B3256865 : Blo 1445542 3256865 := bstep (se 2 (by rfl) ⟨1221324, by rfl⟩ : syracuseStep 3256865 = 2442649) B2442649
theorem B1446459 : Blo 1445542 1446459 := bstep (se 1 (by rfl) ⟨1084844, by rfl⟩ : syracuseStep 1446459 = 2169689) B2169689
theorem B7320131 : Blo 1445542 7320131 := bstep (se 1 (by rfl) ⟨5490098, by rfl⟩ : syracuseStep 7320131 = 10980197) B10980197
theorem B15635045 : Blo 1445542 15635045 := bstep (se 4 (by rfl) ⟨1465785, by rfl⟩ : syracuseStep 15635045 = 2931571) B2931571
theorem B1446535 : Blo 1445542 1446535 := bstep (se 1 (by rfl) ⟨1084901, by rfl⟩ : syracuseStep 1446535 = 2169803) B2169803
theorem B1446543 : Blo 1445542 1446543 := bstep (se 1 (by rfl) ⟨1084907, by rfl⟩ : syracuseStep 1446543 = 2169815) B2169815
theorem B1831567 : Blo 1445542 1831567 := bstep (se 1 (by rfl) ⟨1373675, by rfl⟩ : syracuseStep 1831567 = 2747351) B2747351
theorem B1446587 : Blo 1445542 1446587 := bstep (se 1 (by rfl) ⟨1084940, by rfl⟩ : syracuseStep 1446587 = 2169881) B2169881
theorem B1446663 : Blo 1445542 1446663 := bstep (se 1 (by rfl) ⟨1084997, by rfl⟩ : syracuseStep 1446663 = 2169995) B2169995
theorem B1446671 : Blo 1445542 1446671 := bstep (se 1 (by rfl) ⟨1085003, by rfl⟩ : syracuseStep 1446671 = 2170007) B2170007
theorem B8237861 : Blo 1445542 8237861 := bstep (se 4 (by rfl) ⟨772299, by rfl⟩ : syracuseStep 8237861 = 1544599) B1544599
theorem B1446715 : Blo 1445542 1446715 := bstep (se 1 (by rfl) ⟨1085036, by rfl⟩ : syracuseStep 1446715 = 2170073) B2170073
theorem B7320455 : Blo 1445542 7320455 := bstep (se 1 (by rfl) ⟨5490341, by rfl⟩ : syracuseStep 7320455 = 10980683) B10980683
theorem B1627015 : Blo 1445542 1627015 := bstep (se 1 (by rfl) ⟨1220261, by rfl⟩ : syracuseStep 1627015 = 2440523) B2440523
theorem B1446791 : Blo 1445542 1446791 := bstep (se 1 (by rfl) ⟨1085093, by rfl⟩ : syracuseStep 1446791 = 2170187) B2170187
theorem B1446799 : Blo 1445542 1446799 := bstep (se 1 (by rfl) ⟨1085099, by rfl⟩ : syracuseStep 1446799 = 2170199) B2170199
theorem B1446843 : Blo 1445542 1446843 := bstep (se 1 (by rfl) ⟨1085132, by rfl⟩ : syracuseStep 1446843 = 2170265) B2170265
theorem B1446919 : Blo 1445542 1446919 := bstep (se 1 (by rfl) ⟨1085189, by rfl⟩ : syracuseStep 1446919 = 2170379) B2170379
theorem B9270283 : Blo 1445542 9270283 := bstep (se 1 (by rfl) ⟨6952712, by rfl⟩ : syracuseStep 9270283 = 13905425) B13905425
theorem B1446927 : Blo 1445542 1446927 := bstep (se 1 (by rfl) ⟨1085195, by rfl⟩ : syracuseStep 1446927 = 2170391) B2170391
theorem B1627195 : Blo 1445542 1627195 := bstep (se 1 (by rfl) ⟨1220396, by rfl⟩ : syracuseStep 1627195 = 2440793) B2440793
theorem B1446971 : Blo 1445542 1446971 := bstep (se 1 (by rfl) ⟨1085228, by rfl⟩ : syracuseStep 1446971 = 2170457) B2170457
theorem B1447047 : Blo 1445542 1447047 := bstep (se 1 (by rfl) ⟨1085285, by rfl⟩ : syracuseStep 1447047 = 2170571) B2170571
theorem B1447055 : Blo 1445542 1447055 := bstep (se 1 (by rfl) ⟨1085291, by rfl⟩ : syracuseStep 1447055 = 2170583) B2170583
theorem B1447099 : Blo 1445542 1447099 := bstep (se 1 (by rfl) ⟨1085324, by rfl⟩ : syracuseStep 1447099 = 2170649) B2170649
theorem B10573001 : Blo 1445542 10573001 := bstep (se 2 (by rfl) ⟨3964875, by rfl⟩ : syracuseStep 10573001 = 7929751) B7929751
theorem B1447175 : Blo 1445542 1447175 := bstep (se 1 (by rfl) ⟨1085381, by rfl⟩ : syracuseStep 1447175 = 2170763) B2170763
theorem B1447183 : Blo 1445542 1447183 := bstep (se 1 (by rfl) ⟨1085387, by rfl⟩ : syracuseStep 1447183 = 2170775) B2170775
theorem B1447227 : Blo 1445542 1447227 := bstep (se 1 (by rfl) ⟨1085420, by rfl⟩ : syracuseStep 1447227 = 2170841) B2170841
theorem B4396349 : Blo 1445542 4396349 := bstep (se 3 (by rfl) ⟨824315, by rfl⟩ : syracuseStep 4396349 = 1648631) B1648631
theorem B5215603 : Blo 1445542 5215603 := bstep (se 1 (by rfl) ⟨3911702, by rfl⟩ : syracuseStep 5215603 = 7823405) B7823405
theorem B1447303 : Blo 1445542 1447303 := bstep (se 1 (by rfl) ⟨1085477, by rfl⟩ : syracuseStep 1447303 = 2170955) B2170955
theorem B1447311 : Blo 1445542 1447311 := bstep (se 1 (by rfl) ⟨1085483, by rfl⟩ : syracuseStep 1447311 = 2170967) B2170967
theorem B4879763 : Blo 1445542 4879763 := bstep (se 1 (by rfl) ⟨3659822, by rfl⟩ : syracuseStep 4879763 = 7319645) B7319645
theorem B4634003 : Blo 1445542 4634003 := bstep (se 1 (by rfl) ⟨3475502, by rfl⟩ : syracuseStep 4634003 = 6951005) B6951005
theorem B5494169 : Blo 1445542 5494169 := bstep (se 2 (by rfl) ⟨2060313, by rfl⟩ : syracuseStep 5494169 = 4120627) B4120627
theorem B1447355 : Blo 1445542 1447355 := bstep (se 1 (by rfl) ⟨1085516, by rfl⟩ : syracuseStep 1447355 = 2171033) B2171033
theorem B2168327 : Blo 1445542 2168327 := bstep (se 1 (by rfl) ⟨1626245, by rfl⟩ : syracuseStep 2168327 = 3252491) B3252491
theorem B1447431 : Blo 1445542 1447431 := bstep (se 1 (by rfl) ⟨1085573, by rfl⟩ : syracuseStep 1447431 = 2171147) B2171147
theorem B1627663 : Blo 1445542 1627663 := bstep (se 1 (by rfl) ⟨1220747, by rfl⟩ : syracuseStep 1627663 = 2441495) B2441495
theorem B1447439 : Blo 1445542 1447439 := bstep (se 1 (by rfl) ⟨1085579, by rfl⟩ : syracuseStep 1447439 = 2171159) B2171159
theorem B16479773 : Blo 1445542 16479773 := bstep (se 3 (by rfl) ⟨3089957, by rfl⟩ : syracuseStep 16479773 = 6179915) B6179915
theorem B2168363 : Blo 1445542 2168363 := bstep (se 1 (by rfl) ⟨1626272, by rfl⟩ : syracuseStep 2168363 = 3252545) B3252545
theorem B1447483 : Blo 1445542 1447483 := bstep (se 1 (by rfl) ⟨1085612, by rfl⟩ : syracuseStep 1447483 = 2171225) B2171225
theorem B2168393 : Blo 1445542 2168393 := bstep (se 2 (by rfl) ⟨813147, by rfl⟩ : syracuseStep 2168393 = 1626295) B1626295
theorem B2168507 : Blo 1445542 2168507 := bstep (se 1 (by rfl) ⟨1626380, by rfl⟩ : syracuseStep 2168507 = 3252761) B3252761
theorem B8238793 : Blo 1445542 8238793 := bstep (se 2 (by rfl) ⟨3089547, by rfl⟩ : syracuseStep 8238793 = 6179095) B6179095
theorem B2168567 : Blo 1445542 2168567 := bstep (se 1 (by rfl) ⟨1626425, by rfl⟩ : syracuseStep 2168567 = 3252851) B3252851
theorem B2168591 : Blo 1445542 2168591 := bstep (se 1 (by rfl) ⟨1626443, by rfl⟩ : syracuseStep 2168591 = 3252887) B3252887
theorem B10991375 : Blo 1445542 10991375 := bstep (se 1 (by rfl) ⟨8243531, by rfl⟩ : syracuseStep 10991375 = 16487063) B16487063
theorem B2168633 : Blo 1445542 2168633 := bstep (se 2 (by rfl) ⟨813237, by rfl⟩ : syracuseStep 2168633 = 1626475) B1626475
theorem B2168711 : Blo 1445542 2168711 := bstep (se 1 (by rfl) ⟨1626533, by rfl⟩ : syracuseStep 2168711 = 3253067) B3253067
theorem B2168747 : Blo 1445542 2168747 := bstep (se 1 (by rfl) ⟨1626560, by rfl⟩ : syracuseStep 2168747 = 3253121) B3253121
theorem B2168777 : Blo 1445542 2168777 := bstep (se 2 (by rfl) ⟨813291, by rfl⟩ : syracuseStep 2168777 = 1626583) B1626583
theorem B12359627 : Blo 1445542 12359627 := bstep (se 1 (by rfl) ⟨9269720, by rfl⟩ : syracuseStep 12359627 = 18539441) B18539441
theorem B1628167 : Blo 1445542 1628167 := bstep (se 1 (by rfl) ⟨1221125, by rfl⟩ : syracuseStep 1628167 = 2442251) B2442251
theorem B2168891 : Blo 1445542 2168891 := bstep (se 1 (by rfl) ⟨1626668, by rfl⟩ : syracuseStep 2168891 = 3253337) B3253337
theorem B8796221 : Blo 1445542 8796221 := bstep (se 3 (by rfl) ⟨1649291, by rfl⟩ : syracuseStep 8796221 = 3298583) B3298583
theorem B3659863 : Blo 1445542 3659863 := bstep (se 1 (by rfl) ⟨2744897, by rfl⟩ : syracuseStep 3659863 = 5489795) B5489795
theorem B2168951 : Blo 1445542 2168951 := bstep (se 1 (by rfl) ⟨1626713, by rfl⟩ : syracuseStep 2168951 = 3253427) B3253427
theorem B2168975 : Blo 1445542 2168975 := bstep (se 1 (by rfl) ⟨1626731, by rfl⟩ : syracuseStep 2168975 = 3253463) B3253463
theorem B2169017 : Blo 1445542 2169017 := bstep (se 2 (by rfl) ⟨813381, by rfl⟩ : syracuseStep 2169017 = 1626763) B1626763
theorem B1628347 : Blo 1445542 1628347 := bstep (se 1 (by rfl) ⟨1221260, by rfl⟩ : syracuseStep 1628347 = 2442521) B2442521
theorem B2169095 : Blo 1445542 2169095 := bstep (se 1 (by rfl) ⟨1626821, by rfl⟩ : syracuseStep 2169095 = 3253643) B3253643
theorem B2169131 : Blo 1445542 2169131 := bstep (se 1 (by rfl) ⟨1626848, by rfl⟩ : syracuseStep 2169131 = 3253697) B3253697
theorem B2169161 : Blo 1445542 2169161 := bstep (se 2 (by rfl) ⟨813435, by rfl⟩ : syracuseStep 2169161 = 1626871) B1626871
theorem B3660167 : Blo 1445542 3660167 := bstep (se 1 (by rfl) ⟨2745125, by rfl⟩ : syracuseStep 3660167 = 5490251) B5490251
theorem B2169275 : Blo 1445542 2169275 := bstep (se 1 (by rfl) ⟨1626956, by rfl⟩ : syracuseStep 2169275 = 3253913) B3253913
theorem B2439625 : Blo 1445542 2439625 := bstep (se 2 (by rfl) ⟨914859, by rfl⟩ : syracuseStep 2439625 = 1829719) B1829719
theorem B2169335 : Blo 1445542 2169335 := bstep (se 1 (by rfl) ⟨1627001, by rfl⟩ : syracuseStep 2169335 = 3254003) B3254003
theorem B3660299 : Blo 1445542 3660299 := bstep (se 1 (by rfl) ⟨2745224, by rfl⟩ : syracuseStep 3660299 = 5490449) B5490449
theorem B2169359 : Blo 1445542 2169359 := bstep (se 1 (by rfl) ⟨1627019, by rfl⟩ : syracuseStep 2169359 = 3254039) B3254039
theorem B2169401 : Blo 1445542 2169401 := bstep (se 2 (by rfl) ⟨813525, by rfl⟩ : syracuseStep 2169401 = 1627051) B1627051
theorem B2169479 : Blo 1445542 2169479 := bstep (se 1 (by rfl) ⟨1627109, by rfl⟩ : syracuseStep 2169479 = 3254219) B3254219
theorem B2169515 : Blo 1445542 2169515 := bstep (se 1 (by rfl) ⟨1627136, by rfl⟩ : syracuseStep 2169515 = 3254273) B3254273
theorem B30489281 : Blo 1445542 30489281 := bstep (se 2 (by rfl) ⟨11433480, by rfl⟩ : syracuseStep 30489281 = 22866961) B22866961
theorem B2169545 : Blo 1445542 2169545 := bstep (se 2 (by rfl) ⟨813579, by rfl⟩ : syracuseStep 2169545 = 1627159) B1627159
theorem B4881167 : Blo 1445542 4881167 := bstep (se 1 (by rfl) ⟨3660875, by rfl⟩ : syracuseStep 4881167 = 7321751) B7321751
theorem B4119329 : Blo 1445542 4119329 := bstep (se 2 (by rfl) ⟨1544748, by rfl⟩ : syracuseStep 4119329 = 3089497) B3089497
theorem B13908773 : Blo 1445542 13908773 := bstep (se 4 (by rfl) ⟨1303947, by rfl⟩ : syracuseStep 13908773 = 2607895) B2607895
theorem B2169659 : Blo 1445542 2169659 := bstep (se 1 (by rfl) ⟨1627244, by rfl⟩ : syracuseStep 2169659 = 3254489) B3254489
theorem B2169719 : Blo 1445542 2169719 := bstep (se 1 (by rfl) ⟨1627289, by rfl⟩ : syracuseStep 2169719 = 3254579) B3254579
theorem B2169743 : Blo 1445542 2169743 := bstep (se 1 (by rfl) ⟨1627307, by rfl⟩ : syracuseStep 2169743 = 3254615) B3254615
theorem B4119443 : Blo 1445542 4119443 := bstep (se 1 (by rfl) ⟨3089582, by rfl⟩ : syracuseStep 4119443 = 6179165) B6179165
theorem B2169785 : Blo 1445542 2169785 := bstep (se 2 (by rfl) ⟨813669, by rfl⟩ : syracuseStep 2169785 = 1627339) B1627339
theorem B2169863 : Blo 1445542 2169863 := bstep (se 1 (by rfl) ⟨1627397, by rfl⟩ : syracuseStep 2169863 = 3254795) B3254795
theorem B3660815 : Blo 1445542 3660815 := bstep (se 1 (by rfl) ⟨2745611, by rfl⟩ : syracuseStep 3660815 = 5491223) B5491223
theorem B4881437 : Blo 1445542 4881437 := bstep (se 3 (by rfl) ⟨915269, by rfl⟩ : syracuseStep 4881437 = 1830539) B1830539
theorem B2169899 : Blo 1445542 2169899 := bstep (se 1 (by rfl) ⟨1627424, by rfl⟩ : syracuseStep 2169899 = 3254849) B3254849
theorem B2169929 : Blo 1445542 2169929 := bstep (se 2 (by rfl) ⟨813723, by rfl⟩ : syracuseStep 2169929 = 1627447) B1627447
theorem B8911991 : Blo 1445542 8911991 := bstep (se 1 (by rfl) ⟨6683993, by rfl⟩ : syracuseStep 8911991 = 13367987) B13367987
theorem B2440327 : Blo 1445542 2440327 := bstep (se 1 (by rfl) ⟨1830245, by rfl⟩ : syracuseStep 2440327 = 3660491) B3660491
theorem B3660947 : Blo 1445542 3660947 := bstep (se 1 (by rfl) ⟨2745710, by rfl⟩ : syracuseStep 3660947 = 5491421) B5491421
theorem B2170043 : Blo 1445542 2170043 := bstep (se 1 (by rfl) ⟨1627532, by rfl⟩ : syracuseStep 2170043 = 3255065) B3255065
theorem B2170103 : Blo 1445542 2170103 := bstep (se 1 (by rfl) ⟨1627577, by rfl⟩ : syracuseStep 2170103 = 3255155) B3255155
theorem B2170127 : Blo 1445542 2170127 := bstep (se 1 (by rfl) ⟨1627595, by rfl⟩ : syracuseStep 2170127 = 3255191) B3255191
theorem B2170169 : Blo 1445542 2170169 := bstep (se 2 (by rfl) ⟨813813, by rfl⟩ : syracuseStep 2170169 = 1627627) B1627627
theorem B2170247 : Blo 1445542 2170247 := bstep (se 1 (by rfl) ⟨1627685, by rfl⟩ : syracuseStep 2170247 = 3255371) B3255371
theorem B2170283 : Blo 1445542 2170283 := bstep (se 1 (by rfl) ⟨1627712, by rfl⟩ : syracuseStep 2170283 = 3255425) B3255425
theorem B2170313 : Blo 1445542 2170313 := bstep (se 2 (by rfl) ⟨813867, by rfl⟩ : syracuseStep 2170313 = 1627735) B1627735
theorem B6176209 : Blo 1445542 6176209 := bstep (se 2 (by rfl) ⟨2316078, by rfl⟩ : syracuseStep 6176209 = 4632157) B4632157
theorem B1465871 : Blo 1445542 1465871 := bstep (se 1 (by rfl) ⟨1099403, by rfl⟩ : syracuseStep 1465871 = 2198807) B2198807
theorem B1785359 : Blo 1445542 1785359 := bstep (se 1 (by rfl) ⟨1339019, by rfl⟩ : syracuseStep 1785359 = 2678039) B2678039
theorem B2784811 : Blo 1445542 2784811 := bstep (se 1 (by rfl) ⟨2088608, by rfl⟩ : syracuseStep 2784811 = 4177217) B4177217
theorem B2170427 : Blo 1445542 2170427 := bstep (se 1 (by rfl) ⟨1627820, by rfl⟩ : syracuseStep 2170427 = 3255641) B3255641
theorem B2170487 : Blo 1445542 2170487 := bstep (se 1 (by rfl) ⟨1627865, by rfl⟩ : syracuseStep 2170487 = 3255731) B3255731
theorem B2317943 : Blo 1445542 2317943 := bstep (se 1 (by rfl) ⟨1738457, by rfl⟩ : syracuseStep 2317943 = 3476915) B3476915
theorem B2170511 : Blo 1445542 2170511 := bstep (se 1 (by rfl) ⟨1627883, by rfl⟩ : syracuseStep 2170511 = 3255767) B3255767
theorem B4398745 : Blo 1445542 4398745 := bstep (se 2 (by rfl) ⟨1649529, by rfl⟩ : syracuseStep 4398745 = 3299059) B3299059
theorem B4120217 : Blo 1445542 4120217 := bstep (se 2 (by rfl) ⟨1545081, by rfl⟩ : syracuseStep 4120217 = 3090163) B3090163
theorem B2170553 : Blo 1445542 2170553 := bstep (se 2 (by rfl) ⟨813957, by rfl⟩ : syracuseStep 2170553 = 1627915) B1627915
theorem B2170631 : Blo 1445542 2170631 := bstep (se 1 (by rfl) ⟨1627973, by rfl⟩ : syracuseStep 2170631 = 3255947) B3255947
theorem B2440975 : Blo 1445542 2440975 := bstep (se 1 (by rfl) ⟨1830731, by rfl⟩ : syracuseStep 2440975 = 3661463) B3661463
theorem B2170667 : Blo 1445542 2170667 := bstep (se 1 (by rfl) ⟨1628000, by rfl⟩ : syracuseStep 2170667 = 3256001) B3256001
theorem B10428209 : Blo 1445542 10428209 := bstep (se 2 (by rfl) ⟨3910578, by rfl⟩ : syracuseStep 10428209 = 7821157) B7821157
theorem B8355635 : Blo 1445542 8355635 := bstep (se 1 (by rfl) ⟨6266726, by rfl⟩ : syracuseStep 8355635 = 12533453) B12533453
theorem B7814971 : Blo 1445542 7814971 := bstep (se 1 (by rfl) ⟨5861228, by rfl⟩ : syracuseStep 7814971 = 11722457) B11722457
theorem B2170697 : Blo 1445542 2170697 := bstep (se 2 (by rfl) ⟨814011, by rfl⟩ : syracuseStep 2170697 = 1628023) B1628023
theorem B2604919 : Blo 1445542 2604919 := bstep (se 1 (by rfl) ⟨1953689, by rfl⟩ : syracuseStep 2604919 = 3907379) B3907379
theorem B2170811 : Blo 1445542 2170811 := bstep (se 1 (by rfl) ⟨1628108, by rfl⟩ : syracuseStep 2170811 = 3256217) B3256217
theorem B12058571 : Blo 1445542 12058571 := bstep (se 1 (by rfl) ⟨9043928, by rfl⟩ : syracuseStep 12058571 = 18087857) B18087857
theorem B2170871 : Blo 1445542 2170871 := bstep (se 1 (by rfl) ⟨1628153, by rfl⟩ : syracuseStep 2170871 = 3256307) B3256307
theorem B5865479 : Blo 1445542 5865479 := bstep (se 1 (by rfl) ⟨4399109, by rfl⟩ : syracuseStep 5865479 = 8798219) B8798219
theorem B2473993 : Blo 1445542 2473993 := bstep (se 2 (by rfl) ⟨927747, by rfl⟩ : syracuseStep 2473993 = 1855495) B1855495
theorem B2441225 : Blo 1445542 2441225 := bstep (se 2 (by rfl) ⟨915459, by rfl⟩ : syracuseStep 2441225 = 1830919) B1830919
theorem B18530315 : Blo 1445542 18530315 := bstep (se 1 (by rfl) ⟨13897736, by rfl⟩ : syracuseStep 18530315 = 27795473) B27795473
theorem B2170889 : Blo 1445542 2170889 := bstep (se 2 (by rfl) ⟨814083, by rfl⟩ : syracuseStep 2170889 = 1628167) B1628167
theorem B9273359 : Blo 1445542 9273359 := bstep (se 1 (by rfl) ⟨6955019, by rfl⟩ : syracuseStep 9273359 = 13910039) B13910039
theorem B2170919 : Blo 1445542 2170919 := bstep (se 1 (by rfl) ⟨1628189, by rfl⟩ : syracuseStep 2170919 = 3256379) B3256379
theorem B8241209 : Blo 1445542 8241209 := bstep (se 2 (by rfl) ⟨3090453, by rfl⟩ : syracuseStep 8241209 = 6180907) B6180907
theorem B2605135 : Blo 1445542 2605135 := bstep (se 1 (by rfl) ⟨1953851, by rfl⟩ : syracuseStep 2605135 = 3907703) B3907703
theorem B2171003 : Blo 1445542 2171003 := bstep (se 1 (by rfl) ⟨1628252, by rfl⟩ : syracuseStep 2171003 = 3256505) B3256505
theorem B5488793 : Blo 1445542 5488793 := bstep (se 2 (by rfl) ⟨2058297, by rfl⟩ : syracuseStep 5488793 = 4116595) B4116595
theorem B2441387 : Blo 1445542 2441387 := bstep (se 1 (by rfl) ⟨1831040, by rfl⟩ : syracuseStep 2441387 = 3662081) B3662081
theorem B23445683 : Blo 1445542 23445683 := bstep (se 1 (by rfl) ⟨17584262, by rfl⟩ : syracuseStep 23445683 = 35168525) B35168525
theorem B4882679 : Blo 1445542 4882679 := bstep (se 1 (by rfl) ⟨3662009, by rfl⟩ : syracuseStep 4882679 = 7324019) B7324019
theorem B2171129 : Blo 1445542 2171129 := bstep (se 2 (by rfl) ⟨814173, by rfl⟩ : syracuseStep 2171129 = 1628347) B1628347
theorem B23765309 : Blo 1445542 23765309 := bstep (se 3 (by rfl) ⟨4455995, by rfl⟩ : syracuseStep 23765309 = 8911991) B8911991
theorem B20062525 : Blo 1445542 20062525 := bstep (se 3 (by rfl) ⟨3761723, by rfl⟩ : syracuseStep 20062525 = 7523447) B7523447
theorem B2171231 : Blo 1445542 2171231 := bstep (se 1 (by rfl) ⟨1628423, by rfl⟩ : syracuseStep 2171231 = 3256847) B3256847
theorem B2171243 : Blo 1445542 2171243 := bstep (se 1 (by rfl) ⟨1628432, by rfl⟩ : syracuseStep 2171243 = 3256865) B3256865
theorem B16482689 : Blo 1445542 16482689 := bstep (se 2 (by rfl) ⟨6181008, by rfl⟩ : syracuseStep 16482689 = 12362017) B12362017
theorem B2605625 : Blo 1445542 2605625 := bstep (se 2 (by rfl) ⟨977109, by rfl⟩ : syracuseStep 2605625 = 1954219) B1954219
theorem B2441785 : Blo 1445542 2441785 := bstep (se 2 (by rfl) ⟨915669, by rfl⟩ : syracuseStep 2441785 = 1831339) B1831339
theorem B4883003 : Blo 1445542 4883003 := bstep (se 1 (by rfl) ⟨3662252, by rfl⟩ : syracuseStep 4883003 = 7324505) B7324505
theorem B3252833 : Blo 1445542 3252833 := bstep (se 2 (by rfl) ⟨1219812, by rfl⟩ : syracuseStep 3252833 = 2439625) B2439625
theorem B2933371 : Blo 1445542 2933371 := bstep (se 1 (by rfl) ⟨2200028, by rfl⟩ : syracuseStep 2933371 = 4400057) B4400057
theorem B2441927 : Blo 1445542 2441927 := bstep (se 1 (by rfl) ⟨1831445, by rfl⟩ : syracuseStep 2441927 = 3662891) B3662891
theorem B6177491 : Blo 1445542 6177491 := bstep (se 1 (by rfl) ⟨4633118, by rfl⟩ : syracuseStep 6177491 = 9266237) B9266237
theorem B4883273 : Blo 1445542 4883273 := bstep (se 2 (by rfl) ⟨1831227, by rfl⟩ : syracuseStep 4883273 = 3662455) B3662455
theorem B2442089 : Blo 1445542 2442089 := bstep (se 2 (by rfl) ⟨915783, by rfl⟩ : syracuseStep 2442089 = 1831567) B1831567
theorem B2605999 : Blo 1445542 2605999 := bstep (se 1 (by rfl) ⟨1954499, by rfl⟩ : syracuseStep 2605999 = 3908999) B3908999
theorem B3253175 : Blo 1445542 3253175 := bstep (se 1 (by rfl) ⟨2439881, by rfl⟩ : syracuseStep 3253175 = 4879763) B4879763
theorem B3089335 : Blo 1445542 3089335 := bstep (se 1 (by rfl) ⟨2317001, by rfl⟩ : syracuseStep 3089335 = 4634003) B4634003
theorem B3662779 : Blo 1445542 3662779 := bstep (se 1 (by rfl) ⟨2747084, by rfl⟩ : syracuseStep 3662779 = 5494169) B5494169
theorem B2606087 : Blo 1445542 2606087 := bstep (se 1 (by rfl) ⟨1954565, by rfl⟩ : syracuseStep 2606087 = 3909131) B3909131
theorem B2745353 : Blo 1445542 2745353 := bstep (se 2 (by rfl) ⟨1029507, by rfl⟩ : syracuseStep 2745353 = 2059015) B2059015
theorem B10986515 : Blo 1445542 10986515 := bstep (se 1 (by rfl) ⟨8239886, by rfl⟩ : syracuseStep 10986515 = 16479773) B16479773
theorem B3965971 : Blo 1445542 3965971 := bstep (se 1 (by rfl) ⟨2974478, by rfl⟩ : syracuseStep 3965971 = 5948957) B5948957
theorem B2442487 : Blo 1445542 2442487 := bstep (se 1 (by rfl) ⟨1831865, by rfl⟩ : syracuseStep 2442487 = 3663731) B3663731
theorem B5211479 : Blo 1445542 5211479 := bstep (se 1 (by rfl) ⟨3908609, by rfl⟩ : syracuseStep 5211479 = 7817219) B7817219
theorem B3908989 : Blo 1445542 3908989 := bstep (se 3 (by rfl) ⟨732935, by rfl⟩ : syracuseStep 3908989 = 1465871) B1465871
theorem B4760957 : Blo 1445542 4760957 := bstep (se 3 (by rfl) ⟨892679, by rfl⟩ : syracuseStep 4760957 = 1785359) B1785359
theorem B2606519 : Blo 1445542 2606519 := bstep (se 1 (by rfl) ⟨1954889, by rfl⟩ : syracuseStep 2606519 = 3909779) B3909779
theorem B2442683 : Blo 1445542 2442683 := bstep (se 1 (by rfl) ⟨1832012, by rfl⟩ : syracuseStep 2442683 = 3664025) B3664025
theorem B3253769 : Blo 1445542 3253769 := bstep (se 2 (by rfl) ⟨1220163, by rfl⟩ : syracuseStep 3253769 = 2440327) B2440327
theorem B6948449 : Blo 1445542 6948449 := bstep (se 2 (by rfl) ⟨2605668, by rfl⟩ : syracuseStep 6948449 = 5211337) B5211337
theorem B20326187 : Blo 1445542 20326187 := bstep (se 1 (by rfl) ⟨15244640, by rfl⟩ : syracuseStep 20326187 = 30489281) B30489281
theorem B3254111 : Blo 1445542 3254111 := bstep (se 1 (by rfl) ⟨2440583, by rfl⟩ : syracuseStep 3254111 = 4881167) B4881167
theorem B2746219 : Blo 1445542 2746219 := bstep (se 1 (by rfl) ⟨2059664, by rfl⟩ : syracuseStep 2746219 = 4119329) B4119329
theorem B2746295 : Blo 1445542 2746295 := bstep (se 1 (by rfl) ⟨2059721, by rfl⟩ : syracuseStep 2746295 = 4119443) B4119443
theorem B4884407 : Blo 1445542 4884407 := bstep (se 1 (by rfl) ⟨3663305, by rfl⟩ : syracuseStep 4884407 = 7326611) B7326611
theorem B8234945 : Blo 1445542 8234945 := bstep (se 2 (by rfl) ⟨3088104, by rfl⟩ : syracuseStep 8234945 = 6176209) B6176209
theorem B3254291 : Blo 1445542 3254291 := bstep (se 1 (by rfl) ⟨2440718, by rfl⟩ : syracuseStep 3254291 = 4881437) B4881437
theorem B3713081 : Blo 1445542 3713081 := bstep (se 2 (by rfl) ⟨1392405, by rfl⟩ : syracuseStep 3713081 = 2784811) B2784811
theorem B5490767 : Blo 1445542 5490767 := bstep (se 1 (by rfl) ⟨4118075, by rfl⟩ : syracuseStep 5490767 = 8236151) B8236151
theorem B11733221 : Blo 1445542 11733221 := bstep (se 4 (by rfl) ⟨1099989, by rfl⟩ : syracuseStep 11733221 = 2199979) B2199979
theorem B5490935 : Blo 1445542 5490935 := bstep (se 1 (by rfl) ⟨4118201, by rfl⟩ : syracuseStep 5490935 = 8236403) B8236403
theorem B7325963 : Blo 1445542 7325963 := bstep (se 1 (by rfl) ⟨5494472, by rfl⟩ : syracuseStep 7325963 = 10988945) B10988945
theorem B38070577 : Blo 1445542 38070577 := bstep (se 2 (by rfl) ⟨14276466, by rfl⟩ : syracuseStep 38070577 = 28552933) B28552933
theorem B14084401 : Blo 1445542 14084401 := bstep (se 2 (by rfl) ⟨5281650, by rfl⟩ : syracuseStep 14084401 = 10563301) B10563301
theorem B3254633 : Blo 1445542 3254633 := bstep (se 2 (by rfl) ⟨1220487, by rfl⟩ : syracuseStep 3254633 = 2440975) B2440975
theorem B2746811 : Blo 1445542 2746811 := bstep (se 1 (by rfl) ⟨2060108, by rfl⟩ : syracuseStep 2746811 = 4120217) B4120217
theorem B8243693 : Blo 1445542 8243693 := bstep (se 3 (by rfl) ⟨1545692, by rfl⟩ : syracuseStep 8243693 = 3091385) B3091385
theorem B4885001 : Blo 1445542 4885001 := bstep (se 2 (by rfl) ⟨1831875, by rfl⟩ : syracuseStep 4885001 = 3663751) B3663751
theorem B32156189 : Blo 1445542 32156189 := bstep (se 3 (by rfl) ⟨6029285, by rfl⟩ : syracuseStep 32156189 = 12058571) B12058571
theorem B16476857 : Blo 1445542 16476857 := bstep (se 2 (by rfl) ⟨6178821, by rfl⟩ : syracuseStep 16476857 = 12357643) B12357643
theorem B2747297 : Blo 1445542 2747297 := bstep (se 2 (by rfl) ⟨1030236, by rfl⟩ : syracuseStep 2747297 = 2060473) B2060473
theorem B85765027 : Blo 1445542 85765027 := bstep (se 1 (by rfl) ⟨64323770, by rfl⟩ : syracuseStep 85765027 = 128647541) B128647541
theorem B15641527 : Blo 1445542 15641527 := bstep (se 1 (by rfl) ⟨11731145, by rfl⟩ : syracuseStep 15641527 = 23462291) B23462291
theorem B3255227 : Blo 1445542 3255227 := bstep (se 1 (by rfl) ⟨2441420, by rfl⟩ : syracuseStep 3255227 = 4882841) B4882841
theorem B18787301 : Blo 1445542 18787301 := bstep (se 4 (by rfl) ⟨1761309, by rfl⟩ : syracuseStep 18787301 = 3522619) B3522619
theorem B8793107 : Blo 1445542 8793107 := bstep (se 1 (by rfl) ⟨6594830, by rfl⟩ : syracuseStep 8793107 = 13189661) B13189661
theorem B3255353 : Blo 1445542 3255353 := bstep (se 2 (by rfl) ⟨1220757, by rfl⟩ : syracuseStep 3255353 = 2441515) B2441515
theorem B2747449 : Blo 1445542 2747449 := bstep (se 2 (by rfl) ⟨1030293, by rfl⟩ : syracuseStep 2747449 = 2060587) B2060587
theorem B10423363 : Blo 1445542 10423363 := bstep (se 1 (by rfl) ⟨7817522, by rfl⟩ : syracuseStep 10423363 = 15635045) B15635045
theorem B5491907 : Blo 1445542 5491907 := bstep (se 1 (by rfl) ⟨4118930, by rfl⟩ : syracuseStep 5491907 = 8237861) B8237861
theorem B2747753 : Blo 1445542 2747753 := bstep (se 2 (by rfl) ⟨1030407, by rfl⟩ : syracuseStep 2747753 = 2060815) B2060815
theorem B3255695 : Blo 1445542 3255695 := bstep (se 1 (by rfl) ⟨2441771, by rfl⟩ : syracuseStep 3255695 = 4883543) B4883543
theorem B7048667 : Blo 1445542 7048667 := bstep (se 1 (by rfl) ⟨5286500, by rfl⟩ : syracuseStep 7048667 = 10573001) B10573001
theorem B1445551 : Blo 1445542 1445551 := bstep (se 1 (by rfl) ⟨1084163, by rfl⟩ : syracuseStep 1445551 = 2168327) B2168327
theorem B7327421 : Blo 1445542 7327421 := bstep (se 3 (by rfl) ⟨1373891, by rfl⟩ : syracuseStep 7327421 = 2747783) B2747783
theorem B1445575 : Blo 1445542 1445575 := bstep (se 1 (by rfl) ⟨1084181, by rfl⟩ : syracuseStep 1445575 = 2168363) B2168363
theorem B3256019 : Blo 1445542 3256019 := bstep (se 1 (by rfl) ⟨2442014, by rfl⟩ : syracuseStep 3256019 = 4884029) B4884029
theorem B9268951 : Blo 1445542 9268951 := bstep (se 1 (by rfl) ⟨6951713, by rfl⟩ : syracuseStep 9268951 = 13903427) B13903427
theorem B1445595 : Blo 1445542 1445595 := bstep (se 1 (by rfl) ⟨1084196, by rfl⟩ : syracuseStep 1445595 = 2168393) B2168393
theorem B5213945 : Blo 1445542 5213945 := bstep (se 2 (by rfl) ⟨1955229, by rfl⟩ : syracuseStep 5213945 = 3910459) B3910459
theorem B1445671 : Blo 1445542 1445671 := bstep (se 1 (by rfl) ⟨1084253, by rfl⟩ : syracuseStep 1445671 = 2168507) B2168507
theorem B1445711 : Blo 1445542 1445711 := bstep (se 1 (by rfl) ⟨1084283, by rfl⟩ : syracuseStep 1445711 = 2168567) B2168567
theorem B1445727 : Blo 1445542 1445727 := bstep (se 1 (by rfl) ⟨1084295, by rfl⟩ : syracuseStep 1445727 = 2168591) B2168591
theorem B7327583 : Blo 1445542 7327583 := bstep (se 1 (by rfl) ⟨5495687, by rfl⟩ : syracuseStep 7327583 = 10991375) B10991375
theorem B10989431 : Blo 1445542 10989431 := bstep (se 1 (by rfl) ⟨8242073, by rfl⟩ : syracuseStep 10989431 = 16484147) B16484147
theorem B1445755 : Blo 1445542 1445755 := bstep (se 1 (by rfl) ⟨1084316, by rfl⟩ : syracuseStep 1445755 = 2168633) B2168633
theorem B26390407 : Blo 1445542 26390407 := bstep (se 1 (by rfl) ⟨19792805, by rfl⟩ : syracuseStep 26390407 = 39585611) B39585611
theorem B1445807 : Blo 1445542 1445807 := bstep (se 1 (by rfl) ⟨1084355, by rfl⟩ : syracuseStep 1445807 = 2168711) B2168711
theorem B7319483 : Blo 1445542 7319483 := bstep (se 1 (by rfl) ⟨5489612, by rfl⟩ : syracuseStep 7319483 = 10979225) B10979225
theorem B1445831 : Blo 1445542 1445831 := bstep (se 1 (by rfl) ⟨1084373, by rfl⟩ : syracuseStep 1445831 = 2168747) B2168747
theorem B1445851 : Blo 1445542 1445851 := bstep (se 1 (by rfl) ⟨1084388, by rfl⟩ : syracuseStep 1445851 = 2168777) B2168777
theorem B37056527 : Blo 1445542 37056527 := bstep (se 1 (by rfl) ⟨27792395, by rfl⟩ : syracuseStep 37056527 = 55584791) B55584791
theorem B1445927 : Blo 1445542 1445927 := bstep (se 1 (by rfl) ⟨1084445, by rfl⟩ : syracuseStep 1445927 = 2168891) B2168891
theorem B1445967 : Blo 1445542 1445967 := bstep (se 1 (by rfl) ⟨1084475, by rfl⟩ : syracuseStep 1445967 = 2168951) B2168951
theorem B1445983 : Blo 1445542 1445983 := bstep (se 1 (by rfl) ⟨1084487, by rfl⟩ : syracuseStep 1445983 = 2168975) B2168975
theorem B1446011 : Blo 1445542 1446011 := bstep (se 1 (by rfl) ⟨1084508, by rfl⟩ : syracuseStep 1446011 = 2169017) B2169017
theorem B5492893 : Blo 1445542 5492893 := bstep (se 3 (by rfl) ⟨1029917, by rfl⟩ : syracuseStep 5492893 = 2059835) B2059835
theorem B1446063 : Blo 1445542 1446063 := bstep (se 1 (by rfl) ⟨1084547, by rfl⟩ : syracuseStep 1446063 = 2169095) B2169095
theorem B1446087 : Blo 1445542 1446087 := bstep (se 1 (by rfl) ⟨1084565, by rfl⟩ : syracuseStep 1446087 = 2169131) B2169131
theorem B1446107 : Blo 1445542 1446107 := bstep (se 1 (by rfl) ⟨1084580, by rfl⟩ : syracuseStep 1446107 = 2169161) B2169161
theorem B1446183 : Blo 1445542 1446183 := bstep (se 1 (by rfl) ⟨1084637, by rfl⟩ : syracuseStep 1446183 = 2169275) B2169275
theorem B6181181 : Blo 1445542 6181181 := bstep (se 3 (by rfl) ⟨1158971, by rfl⟩ : syracuseStep 6181181 = 2317943) B2317943
theorem B1446223 : Blo 1445542 1446223 := bstep (se 1 (by rfl) ⟨1084667, by rfl⟩ : syracuseStep 1446223 = 2169335) B2169335
theorem B1446239 : Blo 1445542 1446239 := bstep (se 1 (by rfl) ⟨1084679, by rfl⟩ : syracuseStep 1446239 = 2169359) B2169359
theorem B1446267 : Blo 1445542 1446267 := bstep (se 1 (by rfl) ⟨1084700, by rfl⟩ : syracuseStep 1446267 = 2169401) B2169401
theorem B1446319 : Blo 1445542 1446319 := bstep (se 1 (by rfl) ⟨1084739, by rfl⟩ : syracuseStep 1446319 = 2169479) B2169479
theorem B1446343 : Blo 1445542 1446343 := bstep (se 1 (by rfl) ⟨1084757, by rfl⟩ : syracuseStep 1446343 = 2169515) B2169515
theorem B1446363 : Blo 1445542 1446363 := bstep (se 1 (by rfl) ⟨1084772, by rfl⟩ : syracuseStep 1446363 = 2169545) B2169545
theorem B1446439 : Blo 1445542 1446439 := bstep (se 1 (by rfl) ⟨1084829, by rfl⟩ : syracuseStep 1446439 = 2169659) B2169659
theorem B1446479 : Blo 1445542 1446479 := bstep (se 1 (by rfl) ⟨1084859, by rfl⟩ : syracuseStep 1446479 = 2169719) B2169719
theorem B1446495 : Blo 1445542 1446495 := bstep (se 1 (by rfl) ⟨1084871, by rfl⟩ : syracuseStep 1446495 = 2169743) B2169743
theorem B1446523 : Blo 1445542 1446523 := bstep (se 1 (by rfl) ⟨1084892, by rfl⟩ : syracuseStep 1446523 = 2169785) B2169785
theorem B3256955 : Blo 1445542 3256955 := bstep (se 1 (by rfl) ⟨2442716, by rfl⟩ : syracuseStep 3256955 = 4885433) B4885433
theorem B1446575 : Blo 1445542 1446575 := bstep (se 1 (by rfl) ⟨1084931, by rfl⟩ : syracuseStep 1446575 = 2169863) B2169863
theorem B1446599 : Blo 1445542 1446599 := bstep (se 1 (by rfl) ⟨1084949, by rfl⟩ : syracuseStep 1446599 = 2169899) B2169899
theorem B1446619 : Blo 1445542 1446619 := bstep (se 1 (by rfl) ⟨1084964, by rfl⟩ : syracuseStep 1446619 = 2169929) B2169929
theorem B8917789 : Blo 1445542 8917789 := bstep (se 3 (by rfl) ⟨1672085, by rfl⟩ : syracuseStep 8917789 = 3344171) B3344171
theorem B1446695 : Blo 1445542 1446695 := bstep (se 1 (by rfl) ⟨1085021, by rfl⟩ : syracuseStep 1446695 = 2170043) B2170043
theorem B1446735 : Blo 1445542 1446735 := bstep (se 1 (by rfl) ⟨1085051, by rfl⟩ : syracuseStep 1446735 = 2170103) B2170103
theorem B1446751 : Blo 1445542 1446751 := bstep (se 1 (by rfl) ⟨1085063, by rfl⟩ : syracuseStep 1446751 = 2170127) B2170127
theorem B4879223 : Blo 1445542 4879223 := bstep (se 1 (by rfl) ⟨3659417, by rfl⟩ : syracuseStep 4879223 = 7318835) B7318835
theorem B1446779 : Blo 1445542 1446779 := bstep (se 1 (by rfl) ⟨1085084, by rfl⟩ : syracuseStep 1446779 = 2170169) B2170169
theorem B23466905 : Blo 1445542 23466905 := bstep (se 2 (by rfl) ⟨8800089, by rfl⟩ : syracuseStep 23466905 = 17600179) B17600179
theorem B1446831 : Blo 1445542 1446831 := bstep (se 1 (by rfl) ⟨1085123, by rfl⟩ : syracuseStep 1446831 = 2170247) B2170247
theorem B1446855 : Blo 1445542 1446855 := bstep (se 1 (by rfl) ⟨1085141, by rfl⟩ : syracuseStep 1446855 = 2170283) B2170283
theorem B1446875 : Blo 1445542 1446875 := bstep (se 1 (by rfl) ⟨1085156, by rfl⟩ : syracuseStep 1446875 = 2170313) B2170313
theorem B1446951 : Blo 1445542 1446951 := bstep (se 1 (by rfl) ⟨1085213, by rfl⟩ : syracuseStep 1446951 = 2170427) B2170427
theorem B4879439 : Blo 1445542 4879439 := bstep (se 1 (by rfl) ⟨3659579, by rfl⟩ : syracuseStep 4879439 = 7319159) B7319159
theorem B1446991 : Blo 1445542 1446991 := bstep (se 1 (by rfl) ⟨1085243, by rfl⟩ : syracuseStep 1446991 = 2170487) B2170487
theorem B1447007 : Blo 1445542 1447007 := bstep (se 1 (by rfl) ⟨1085255, by rfl⟩ : syracuseStep 1447007 = 2170511) B2170511
theorem B1447035 : Blo 1445542 1447035 := bstep (se 1 (by rfl) ⟨1085276, by rfl⟩ : syracuseStep 1447035 = 2170553) B2170553
theorem B1447087 : Blo 1445542 1447087 := bstep (se 1 (by rfl) ⟨1085315, by rfl⟩ : syracuseStep 1447087 = 2170631) B2170631
theorem B1447111 : Blo 1445542 1447111 := bstep (se 1 (by rfl) ⟨1085333, by rfl⟩ : syracuseStep 1447111 = 2170667) B2170667
theorem B7320779 : Blo 1445542 7320779 := bstep (se 1 (by rfl) ⟨5490584, by rfl⟩ : syracuseStep 7320779 = 10981169) B10981169
theorem B6952139 : Blo 1445542 6952139 := bstep (se 1 (by rfl) ⟨5214104, by rfl⟩ : syracuseStep 6952139 = 10428209) B10428209
theorem B1447131 : Blo 1445542 1447131 := bstep (se 1 (by rfl) ⟨1085348, by rfl⟩ : syracuseStep 1447131 = 2170697) B2170697
theorem B1447207 : Blo 1445542 1447207 := bstep (se 1 (by rfl) ⟨1085405, by rfl⟩ : syracuseStep 1447207 = 2170811) B2170811
theorem B1447247 : Blo 1445542 1447247 := bstep (se 1 (by rfl) ⟨1085435, by rfl⟩ : syracuseStep 1447247 = 2170871) B2170871
theorem B1447263 : Blo 1445542 1447263 := bstep (se 1 (by rfl) ⟨1085447, by rfl⟩ : syracuseStep 1447263 = 2170895) B2170895
theorem B1447291 : Blo 1445542 1447291 := bstep (se 1 (by rfl) ⟨1085468, by rfl⟩ : syracuseStep 1447291 = 2170937) B2170937
theorem B1447343 : Blo 1445542 1447343 := bstep (se 1 (by rfl) ⟨1085507, by rfl⟩ : syracuseStep 1447343 = 2171015) B2171015
theorem B1447367 : Blo 1445542 1447367 := bstep (se 1 (by rfl) ⟨1085525, by rfl⟩ : syracuseStep 1447367 = 2171051) B2171051
theorem B4879817 : Blo 1445542 4879817 := bstep (se 2 (by rfl) ⟨1829931, by rfl⟩ : syracuseStep 4879817 = 3659863) B3659863
theorem B1447387 : Blo 1445542 1447387 := bstep (se 1 (by rfl) ⟨1085540, by rfl⟩ : syracuseStep 1447387 = 2171081) B2171081
theorem B13899275 : Blo 1445542 13899275 := bstep (se 1 (by rfl) ⟨10424456, by rfl⟩ : syracuseStep 13899275 = 20848913) B20848913
theorem B1447463 : Blo 1445542 1447463 := bstep (se 1 (by rfl) ⟨1085597, by rfl⟩ : syracuseStep 1447463 = 2171195) B2171195
theorem B2168399 : Blo 1445542 2168399 := bstep (se 1 (by rfl) ⟨1626299, by rfl⟩ : syracuseStep 2168399 = 3252599) B3252599
theorem B1447503 : Blo 1445542 1447503 := bstep (se 1 (by rfl) ⟨1085627, by rfl⟩ : syracuseStep 1447503 = 2171255) B2171255
theorem B1447519 : Blo 1445542 1447519 := bstep (se 1 (by rfl) ⟨1085639, by rfl⟩ : syracuseStep 1447519 = 2171279) B2171279
theorem B1627771 : Blo 1445542 1627771 := bstep (se 1 (by rfl) ⟨1220828, by rfl⟩ : syracuseStep 1627771 = 2441657) B2441657
theorem B2168519 : Blo 1445542 2168519 := bstep (se 1 (by rfl) ⟨1626389, by rfl⟩ : syracuseStep 2168519 = 3252779) B3252779
theorem B4880087 : Blo 1445542 4880087 := bstep (se 1 (by rfl) ⟨3660065, by rfl⟩ : syracuseStep 4880087 = 7320131) B7320131
theorem B3299167 : Blo 1445542 3299167 := bstep (se 1 (by rfl) ⟨2474375, by rfl⟩ : syracuseStep 3299167 = 4948751) B4948751
theorem B2168681 : Blo 1445542 2168681 := bstep (se 2 (by rfl) ⟨813255, by rfl⟩ : syracuseStep 2168681 = 1626511) B1626511
theorem B3659681 : Blo 1445542 3659681 := bstep (se 2 (by rfl) ⟨1372380, by rfl⟩ : syracuseStep 3659681 = 2744761) B2744761
theorem B2086831 : Blo 1445542 2086831 := bstep (se 1 (by rfl) ⟨1565123, by rfl⟩ : syracuseStep 2086831 = 3130247) B3130247
theorem B4880303 : Blo 1445542 4880303 := bstep (se 1 (by rfl) ⟨3660227, by rfl⟩ : syracuseStep 4880303 = 7320455) B7320455
theorem B2168759 : Blo 1445542 2168759 := bstep (se 1 (by rfl) ⟨1626569, by rfl⟩ : syracuseStep 2168759 = 3253139) B3253139
theorem B2168795 : Blo 1445542 2168795 := bstep (se 1 (by rfl) ⟨1626596, by rfl⟩ : syracuseStep 2168795 = 3253193) B3253193
theorem B2316367 : Blo 1445542 2316367 := bstep (se 1 (by rfl) ⟨1737275, by rfl⟩ : syracuseStep 2316367 = 3474551) B3474551
theorem B1628239 : Blo 1445542 1628239 := bstep (se 1 (by rfl) ⟨1221179, by rfl⟩ : syracuseStep 1628239 = 2442359) B2442359
theorem B37591127 : Blo 1445542 37591127 := bstep (se 1 (by rfl) ⟨28193345, by rfl⟩ : syracuseStep 37591127 = 56386691) B56386691
theorem B2930899 : Blo 1445542 2930899 := bstep (se 1 (by rfl) ⟨2198174, by rfl⟩ : syracuseStep 2930899 = 4396349) B4396349
theorem B2439497 : Blo 1445542 2439497 := bstep (se 2 (by rfl) ⟨914811, by rfl⟩ : syracuseStep 2439497 = 1829623) B1829623
theorem B3660137 : Blo 1445542 3660137 := bstep (se 2 (by rfl) ⟨1372551, by rfl⟩ : syracuseStep 3660137 = 2745103) B2745103
theorem B2169263 : Blo 1445542 2169263 := bstep (se 1 (by rfl) ⟨1626947, by rfl⟩ : syracuseStep 2169263 = 3253895) B3253895
theorem B2169353 : Blo 1445542 2169353 := bstep (se 2 (by rfl) ⟨813507, by rfl⟩ : syracuseStep 2169353 = 1627015) B1627015
theorem B2169383 : Blo 1445542 2169383 := bstep (se 1 (by rfl) ⟨1627037, by rfl⟩ : syracuseStep 2169383 = 3254075) B3254075
theorem B2169467 : Blo 1445542 2169467 := bstep (se 1 (by rfl) ⟨1627100, by rfl⟩ : syracuseStep 2169467 = 3254201) B3254201
theorem B8239751 : Blo 1445542 8239751 := bstep (se 1 (by rfl) ⟨6179813, by rfl⟩ : syracuseStep 8239751 = 12359627) B12359627
theorem B12360377 : Blo 1445542 12360377 := bstep (se 2 (by rfl) ⟨4635141, by rfl⟩ : syracuseStep 12360377 = 9270283) B9270283
theorem B5864147 : Blo 1445542 5864147 := bstep (se 1 (by rfl) ⟨4398110, by rfl⟩ : syracuseStep 5864147 = 8796221) B8796221
theorem B2439929 : Blo 1445542 2439929 := bstep (se 2 (by rfl) ⟨914973, by rfl⟩ : syracuseStep 2439929 = 1829947) B1829947
theorem B2169593 : Blo 1445542 2169593 := bstep (se 2 (by rfl) ⟨813597, by rfl⟩ : syracuseStep 2169593 = 1627195) B1627195
theorem B2169695 : Blo 1445542 2169695 := bstep (se 1 (by rfl) ⟨1627271, by rfl⟩ : syracuseStep 2169695 = 3254543) B3254543
theorem B2169707 : Blo 1445542 2169707 := bstep (se 1 (by rfl) ⟨1627280, by rfl⟩ : syracuseStep 2169707 = 3254561) B3254561
theorem B2440111 : Blo 1445542 2440111 := bstep (se 1 (by rfl) ⟨1830083, by rfl⟩ : syracuseStep 2440111 = 3660167) B3660167
theorem B5495809 : Blo 1445542 5495809 := bstep (se 2 (by rfl) ⟨2060928, by rfl⟩ : syracuseStep 5495809 = 4121857) B4121857
theorem B2440199 : Blo 1445542 2440199 := bstep (se 1 (by rfl) ⟨1830149, by rfl⟩ : syracuseStep 2440199 = 3660299) B3660299
theorem B2169935 : Blo 1445542 2169935 := bstep (se 1 (by rfl) ⟨1627451, by rfl⟩ : syracuseStep 2169935 = 3254903) B3254903
theorem B6954137 : Blo 1445542 6954137 := bstep (se 2 (by rfl) ⟨2607801, by rfl⟩ : syracuseStep 6954137 = 5215603) B5215603
theorem B9272515 : Blo 1445542 9272515 := bstep (se 1 (by rfl) ⟨6954386, by rfl⟩ : syracuseStep 9272515 = 13908773) B13908773
theorem B2170055 : Blo 1445542 2170055 := bstep (se 1 (by rfl) ⟨1627541, by rfl⟩ : syracuseStep 2170055 = 3255083) B3255083
theorem B17603831 : Blo 1445542 17603831 := bstep (se 1 (by rfl) ⟨13202873, by rfl⟩ : syracuseStep 17603831 = 26405747) B26405747
theorem B2440543 : Blo 1445542 2440543 := bstep (se 1 (by rfl) ⟨1830407, by rfl⟩ : syracuseStep 2440543 = 3660815) B3660815
theorem B2170217 : Blo 1445542 2170217 := bstep (se 2 (by rfl) ⟨813831, by rfl⟩ : syracuseStep 2170217 = 1627663) B1627663
theorem B2440631 : Blo 1445542 2440631 := bstep (se 1 (by rfl) ⟨1830473, by rfl⟩ : syracuseStep 2440631 = 3660947) B3660947
theorem B2170295 : Blo 1445542 2170295 := bstep (se 1 (by rfl) ⟨1627721, by rfl⟩ : syracuseStep 2170295 = 3255443) B3255443
theorem B2317751 : Blo 1445542 2317751 := bstep (se 1 (by rfl) ⟨1738313, by rfl⟩ : syracuseStep 2317751 = 3476627) B3476627
theorem B2170331 : Blo 1445542 2170331 := bstep (se 1 (by rfl) ⟨1627748, by rfl⟩ : syracuseStep 2170331 = 3255497) B3255497
theorem B3661321 : Blo 1445542 3661321 := bstep (se 2 (by rfl) ⟨1372995, by rfl⟩ : syracuseStep 3661321 = 2745991) B2745991
theorem B5864993 : Blo 1445542 5864993 := bstep (se 2 (by rfl) ⟨2199372, by rfl⟩ : syracuseStep 5864993 = 4398745) B4398745
theorem B10985057 : Blo 1445542 10985057 := bstep (se 2 (by rfl) ⟨4119396, by rfl⟩ : syracuseStep 10985057 = 8238793) B8238793
theorem B10419961 : Blo 1445542 10419961 := bstep (se 2 (by rfl) ⟨3907485, by rfl⟩ : syracuseStep 10419961 = 7814971) B7814971
theorem B3473225 : Blo 1445542 3473225 := bstep (se 2 (by rfl) ⟨1302459, by rfl⟩ : syracuseStep 3473225 = 2604919) B2604919
theorem B5570423 : Blo 1445542 5570423 := bstep (se 1 (by rfl) ⟨4177817, by rfl⟩ : syracuseStep 5570423 = 8355635) B8355635
theorem B2604961 : Blo 1445542 2604961 := bstep (se 2 (by rfl) ⟨976860, by rfl⟩ : syracuseStep 2604961 = 1953721) B1953721
theorem B4636577 : Blo 1445542 4636577 := bstep (se 2 (by rfl) ⟨1738716, by rfl⟩ : syracuseStep 4636577 = 3477433) B3477433
theorem B2170799 : Blo 1445542 2170799 := bstep (se 1 (by rfl) ⟨1628099, by rfl⟩ : syracuseStep 2170799 = 3256199) B3256199
theorem B12353543 : Blo 1445542 12353543 := bstep (se 1 (by rfl) ⟨9265157, by rfl⟩ : syracuseStep 12353543 = 18530315) B18530315
theorem B3473513 : Blo 1445542 3473513 := bstep (se 2 (by rfl) ⟨1302567, by rfl⟩ : syracuseStep 3473513 = 2605135) B2605135
theorem B3088489 : Blo 1445542 3088489 := bstep (se 2 (by rfl) ⟨1158183, by rfl⟩ : syracuseStep 3088489 = 2316367) B2316367
theorem B2170985 : Blo 1445542 2170985 := bstep (se 2 (by rfl) ⟨814119, by rfl⟩ : syracuseStep 2170985 = 1628239) B1628239
theorem B15630455 : Blo 1445542 15630455 := bstep (se 1 (by rfl) ⟨11722841, by rfl⟩ : syracuseStep 15630455 = 23445683) B23445683
theorem B7323857 : Blo 1445542 7323857 := bstep (se 2 (by rfl) ⟨2746446, by rfl⟩ : syracuseStep 7323857 = 5492893) B5492893
theorem B15843539 : Blo 1445542 15843539 := bstep (se 1 (by rfl) ⟨11882654, by rfl⟩ : syracuseStep 15843539 = 23765309) B23765309
theorem B4120787 : Blo 1445542 4120787 := bstep (se 1 (by rfl) ⟨3090590, by rfl⟩ : syracuseStep 4120787 = 6181181) B6181181
theorem B3907865 : Blo 1445542 3907865 := bstep (se 2 (by rfl) ⟨1465449, by rfl⟩ : syracuseStep 3907865 = 2930899) B2930899
theorem B1737083 : Blo 1445542 1737083 := bstep (se 1 (by rfl) ⟨1302812, by rfl⟩ : syracuseStep 1737083 = 2605625) B2605625
theorem B2171303 : Blo 1445542 2171303 := bstep (se 1 (by rfl) ⟨1628477, by rfl⟩ : syracuseStep 2171303 = 3256955) B3256955
theorem B3252815 : Blo 1445542 3252815 := bstep (se 1 (by rfl) ⟨2439611, by rfl⟩ : syracuseStep 3252815 = 4879223) B4879223
theorem B1737391 : Blo 1445542 1737391 := bstep (se 1 (by rfl) ⟨1303043, by rfl⟩ : syracuseStep 1737391 = 2606087) B2606087
theorem B7324343 : Blo 1445542 7324343 := bstep (se 1 (by rfl) ⟨5493257, by rfl⟩ : syracuseStep 7324343 = 10986515) B10986515
theorem B3252959 : Blo 1445542 3252959 := bstep (se 1 (by rfl) ⟨2439719, by rfl⟩ : syracuseStep 3252959 = 4879439) B4879439
theorem B1737679 : Blo 1445542 1737679 := bstep (se 1 (by rfl) ⟨1303259, by rfl⟩ : syracuseStep 1737679 = 2606519) B2606519
theorem B3253211 : Blo 1445542 3253211 := bstep (se 1 (by rfl) ⟨2439908, by rfl⟩ : syracuseStep 3253211 = 4879817) B4879817
theorem B9266183 : Blo 1445542 9266183 := bstep (se 1 (by rfl) ⟨6949637, by rfl⟩ : syracuseStep 9266183 = 13899275) B13899275
theorem B3253391 : Blo 1445542 3253391 := bstep (se 1 (by rfl) ⟨2440043, by rfl⟩ : syracuseStep 3253391 = 4880087) B4880087
theorem B7324829 : Blo 1445542 7324829 := bstep (se 3 (by rfl) ⟨1373405, by rfl⟩ : syracuseStep 7324829 = 2746811) B2746811
theorem B114353369 : Blo 1445542 114353369 := bstep (se 2 (by rfl) ⟨42882513, by rfl⟩ : syracuseStep 114353369 = 85765027) B85765027
theorem B3253481 : Blo 1445542 3253481 := bstep (se 2 (by rfl) ⟨1220055, by rfl⟩ : syracuseStep 3253481 = 2440111) B2440111
theorem B3474665 : Blo 1445542 3474665 := bstep (se 2 (by rfl) ⟨1302999, by rfl⟩ : syracuseStep 3474665 = 2605999) B2605999
theorem B4883705 : Blo 1445542 4883705 := bstep (se 2 (by rfl) ⟨1831389, by rfl⟩ : syracuseStep 4883705 = 3662779) B3662779
theorem B3253535 : Blo 1445542 3253535 := bstep (se 1 (by rfl) ⟨2440151, by rfl⟩ : syracuseStep 3253535 = 4880303) B4880303
theorem B5489963 : Blo 1445542 5489963 := bstep (se 1 (by rfl) ⟨4117472, by rfl⟩ : syracuseStep 5489963 = 8234945) B8234945
theorem B25060751 : Blo 1445542 25060751 := bstep (se 1 (by rfl) ⟨18795563, by rfl⟩ : syracuseStep 25060751 = 37591127) B37591127
theorem B3663265 : Blo 1445542 3663265 := bstep (se 2 (by rfl) ⟨1373724, by rfl⟩ : syracuseStep 3663265 = 2747449) B2747449
theorem B4883975 : Blo 1445542 4883975 := bstep (se 1 (by rfl) ⟨3662981, by rfl⟩ : syracuseStep 4883975 = 7325963) B7325963
theorem B12363353 : Blo 1445542 12363353 := bstep (se 2 (by rfl) ⟨4636257, by rfl⟩ : syracuseStep 12363353 = 9272515) B9272515
theorem B3254057 : Blo 1445542 3254057 := bstep (se 2 (by rfl) ⟨1220271, by rfl⟩ : syracuseStep 3254057 = 2440543) B2440543
theorem B3909431 : Blo 1445542 3909431 := bstep (se 1 (by rfl) ⟨2932073, by rfl⟩ : syracuseStep 3909431 = 5864147) B5864147
theorem B3909995 : Blo 1445542 3909995 := bstep (se 1 (by rfl) ⟨2932496, by rfl⟩ : syracuseStep 3909995 = 5864993) B5864993
theorem B7326125 : Blo 1445542 7326125 := bstep (se 3 (by rfl) ⟨1373648, by rfl⟩ : syracuseStep 7326125 = 2747297) B2747297
theorem B4884947 : Blo 1445542 4884947 := bstep (se 1 (by rfl) ⟨3663710, by rfl⟩ : syracuseStep 4884947 = 7327421) B7327421
theorem B3475963 : Blo 1445542 3475963 := bstep (se 1 (by rfl) ⟨2606972, by rfl⟩ : syracuseStep 3475963 = 5213945) B5213945
theorem B35187209 : Blo 1445542 35187209 := bstep (se 2 (by rfl) ⟨13195203, by rfl⟩ : syracuseStep 35187209 = 26390407) B26390407
theorem B4885055 : Blo 1445542 4885055 := bstep (se 1 (by rfl) ⟨3663791, by rfl⟩ : syracuseStep 4885055 = 7327583) B7327583
theorem B7326287 : Blo 1445542 7326287 := bstep (se 1 (by rfl) ⟨5494715, by rfl⟩ : syracuseStep 7326287 = 10989431) B10989431
theorem B3713615 : Blo 1445542 3713615 := bstep (se 1 (by rfl) ⟨2785211, by rfl⟩ : syracuseStep 3713615 = 5570423) B5570423
theorem B3091051 : Blo 1445542 3091051 := bstep (se 1 (by rfl) ⟨2318288, by rfl⟩ : syracuseStep 3091051 = 4636577) B4636577
theorem B3910319 : Blo 1445542 3910319 := bstep (se 1 (by rfl) ⟨2932739, by rfl⟩ : syracuseStep 3910319 = 5865479) B5865479
theorem B3255119 : Blo 1445542 3255119 := bstep (se 1 (by rfl) ⟨2441339, by rfl⟩ : syracuseStep 3255119 = 4882679) B4882679
theorem B10988459 : Blo 1445542 10988459 := bstep (se 1 (by rfl) ⟨8241344, by rfl⟩ : syracuseStep 10988459 = 16482689) B16482689
theorem B3255335 : Blo 1445542 3255335 := bstep (se 1 (by rfl) ⟨2441501, by rfl⟩ : syracuseStep 3255335 = 4883003) B4883003
theorem B50760769 : Blo 1445542 50760769 := bstep (se 2 (by rfl) ⟨19035288, by rfl⟩ : syracuseStep 50760769 = 38070577) B38070577
theorem B18779201 : Blo 1445542 18779201 := bstep (se 2 (by rfl) ⟨7042200, by rfl⟩ : syracuseStep 18779201 = 14084401) B14084401
theorem B26750033 : Blo 1445542 26750033 := bstep (se 2 (by rfl) ⟨10031262, by rfl⟩ : syracuseStep 26750033 = 20062525) B20062525
theorem B3255515 : Blo 1445542 3255515 := bstep (se 1 (by rfl) ⟨2441636, by rfl⟩ : syracuseStep 3255515 = 4883273) B4883273
theorem B31288589 : Blo 1445542 31288589 := bstep (se 3 (by rfl) ⟨5866610, by rfl⟩ : syracuseStep 31288589 = 11733221) B11733221
theorem B3255713 : Blo 1445542 3255713 := bstep (se 2 (by rfl) ⟨1220892, by rfl⟩ : syracuseStep 3255713 = 2441785) B2441785
theorem B3911161 : Blo 1445542 3911161 := bstep (se 2 (by rfl) ⟨1466685, by rfl⟩ : syracuseStep 3911161 = 2933371) B2933371
theorem B13897277 : Blo 1445542 13897277 := bstep (se 3 (by rfl) ⟨2605739, by rfl⟩ : syracuseStep 13897277 = 5211479) B5211479
theorem B3173971 : Blo 1445542 3173971 := bstep (se 1 (by rfl) ⟨2380478, by rfl⟩ : syracuseStep 3173971 = 4760957) B4760957
theorem B11890385 : Blo 1445542 11890385 := bstep (se 2 (by rfl) ⟨4458894, by rfl⟩ : syracuseStep 11890385 = 8917789) B8917789
theorem B1445599 : Blo 1445542 1445599 := bstep (se 1 (by rfl) ⟨1084199, by rfl⟩ : syracuseStep 1445599 = 2168399) B2168399
theorem B4632299 : Blo 1445542 4632299 := bstep (se 1 (by rfl) ⟨3474224, by rfl⟩ : syracuseStep 4632299 = 6948449) B6948449
theorem B1445679 : Blo 1445542 1445679 := bstep (se 1 (by rfl) ⟨1084259, by rfl⟩ : syracuseStep 1445679 = 2168519) B2168519
theorem B1445787 : Blo 1445542 1445787 := bstep (se 1 (by rfl) ⟨1084340, by rfl⟩ : syracuseStep 1445787 = 2168681) B2168681
theorem B18796445 : Blo 1445542 18796445 := bstep (se 3 (by rfl) ⟨3524333, by rfl⟩ : syracuseStep 18796445 = 7048667) B7048667
theorem B1445839 : Blo 1445542 1445839 := bstep (se 1 (by rfl) ⟨1084379, by rfl⟩ : syracuseStep 1445839 = 2168759) B2168759
theorem B1830863 : Blo 1445542 1830863 := bstep (se 1 (by rfl) ⟨1373147, by rfl⟩ : syracuseStep 1830863 = 2746295) B2746295
theorem B3256271 : Blo 1445542 3256271 := bstep (se 1 (by rfl) ⟨2442203, by rfl⟩ : syracuseStep 3256271 = 4884407) B4884407
theorem B1445863 : Blo 1445542 1445863 := bstep (se 1 (by rfl) ⟨1084397, by rfl⟩ : syracuseStep 1445863 = 2168795) B2168795
theorem B7327745 : Blo 1445542 7327745 := bstep (se 2 (by rfl) ⟨2747904, by rfl⟩ : syracuseStep 7327745 = 5495809) B5495809
theorem B5287961 : Blo 1445542 5287961 := bstep (se 2 (by rfl) ⟨1982985, by rfl⟩ : syracuseStep 5287961 = 3965971) B3965971
theorem B13897817 : Blo 1445542 13897817 := bstep (se 2 (by rfl) ⟨5211681, by rfl⟩ : syracuseStep 13897817 = 10423363) B10423363
theorem B1626331 : Blo 1445542 1626331 := bstep (se 1 (by rfl) ⟨1219748, by rfl⟩ : syracuseStep 1626331 = 2439497) B2439497
theorem B1446175 : Blo 1445542 1446175 := bstep (se 1 (by rfl) ⟨1084631, by rfl⟩ : syracuseStep 1446175 = 2169263) B2169263
theorem B3256649 : Blo 1445542 3256649 := bstep (se 2 (by rfl) ⟨1221243, by rfl⟩ : syracuseStep 3256649 = 2442487) B2442487
theorem B1446235 : Blo 1445542 1446235 := bstep (se 1 (by rfl) ⟨1084676, by rfl⟩ : syracuseStep 1446235 = 2169353) B2169353
theorem B3256667 : Blo 1445542 3256667 := bstep (se 1 (by rfl) ⟨2442500, by rfl⟩ : syracuseStep 3256667 = 4885001) B4885001
theorem B1446255 : Blo 1445542 1446255 := bstep (se 1 (by rfl) ⟨1084691, by rfl⟩ : syracuseStep 1446255 = 2169383) B2169383
theorem B1446311 : Blo 1445542 1446311 := bstep (se 1 (by rfl) ⟨1084733, by rfl⟩ : syracuseStep 1446311 = 2169467) B2169467
theorem B5493167 : Blo 1445542 5493167 := bstep (se 1 (by rfl) ⟨4119875, by rfl⟩ : syracuseStep 5493167 = 8239751) B8239751
theorem B1626619 : Blo 1445542 1626619 := bstep (se 1 (by rfl) ⟨1219964, by rfl⟩ : syracuseStep 1626619 = 2439929) B2439929
theorem B1446395 : Blo 1445542 1446395 := bstep (se 1 (by rfl) ⟨1084796, by rfl⟩ : syracuseStep 1446395 = 2169593) B2169593
theorem B1446463 : Blo 1445542 1446463 := bstep (se 1 (by rfl) ⟨1084847, by rfl⟩ : syracuseStep 1446463 = 2169695) B2169695
theorem B1446471 : Blo 1445542 1446471 := bstep (se 1 (by rfl) ⟨1084853, by rfl⟩ : syracuseStep 1446471 = 2169707) B2169707
theorem B1626799 : Blo 1445542 1626799 := bstep (se 1 (by rfl) ⟨1220099, by rfl⟩ : syracuseStep 1626799 = 2440199) B2440199
theorem B5862071 : Blo 1445542 5862071 := bstep (se 1 (by rfl) ⟨4396553, by rfl⟩ : syracuseStep 5862071 = 8793107) B8793107
theorem B1446623 : Blo 1445542 1446623 := bstep (se 1 (by rfl) ⟨1084967, by rfl⟩ : syracuseStep 1446623 = 2169935) B2169935
theorem B54203165 : Blo 1445542 54203165 := bstep (se 3 (by rfl) ⟨10163093, by rfl⟩ : syracuseStep 54203165 = 20326187) B20326187
theorem B1446703 : Blo 1445542 1446703 := bstep (se 1 (by rfl) ⟨1085027, by rfl⟩ : syracuseStep 1446703 = 2170055) B2170055
theorem B11735887 : Blo 1445542 11735887 := bstep (se 1 (by rfl) ⟨8801915, by rfl⟩ : syracuseStep 11735887 = 17603831) B17603831
theorem B1446811 : Blo 1445542 1446811 := bstep (se 1 (by rfl) ⟨1085108, by rfl⟩ : syracuseStep 1446811 = 2170217) B2170217
theorem B1831835 : Blo 1445542 1831835 := bstep (se 1 (by rfl) ⟨1373876, by rfl⟩ : syracuseStep 1831835 = 2747753) B2747753
theorem B12358601 : Blo 1445542 12358601 := bstep (se 2 (by rfl) ⟨4634475, by rfl⟩ : syracuseStep 12358601 = 9268951) B9268951
theorem B1627087 : Blo 1445542 1627087 := bstep (se 1 (by rfl) ⟨1220315, by rfl⟩ : syracuseStep 1627087 = 2440631) B2440631
theorem B1446863 : Blo 1445542 1446863 := bstep (se 1 (by rfl) ⟨1085147, by rfl⟩ : syracuseStep 1446863 = 2170295) B2170295
theorem B1545167 : Blo 1445542 1545167 := bstep (se 1 (by rfl) ⟨1158875, by rfl⟩ : syracuseStep 1545167 = 2317751) B2317751
theorem B1446887 : Blo 1445542 1446887 := bstep (se 1 (by rfl) ⟨1085165, by rfl⟩ : syracuseStep 1446887 = 2170331) B2170331
theorem B2315483 : Blo 1445542 2315483 := bstep (se 1 (by rfl) ⟨1736612, by rfl⟩ : syracuseStep 2315483 = 3473225) B3473225
theorem B2782441 : Blo 1445542 2782441 := bstep (se 2 (by rfl) ⟨1043415, by rfl⟩ : syracuseStep 2782441 = 2086831) B2086831
theorem B1447199 : Blo 1445542 1447199 := bstep (se 1 (by rfl) ⟨1085399, by rfl⟩ : syracuseStep 1447199 = 2170799) B2170799
theorem B4879655 : Blo 1445542 4879655 := bstep (se 1 (by rfl) ⟨3659741, by rfl⟩ : syracuseStep 4879655 = 7319483) B7319483
theorem B1627483 : Blo 1445542 1627483 := bstep (se 1 (by rfl) ⟨1220612, by rfl⟩ : syracuseStep 1627483 = 2441225) B2441225
theorem B1447259 : Blo 1445542 1447259 := bstep (se 1 (by rfl) ⟨1085444, by rfl⟩ : syracuseStep 1447259 = 2170889) B2170889
theorem B24704351 : Blo 1445542 24704351 := bstep (se 1 (by rfl) ⟨18528263, by rfl⟩ : syracuseStep 24704351 = 37056527) B37056527
theorem B3298657 : Blo 1445542 3298657 := bstep (se 2 (by rfl) ⟨1236996, by rfl⟩ : syracuseStep 3298657 = 2473993) B2473993
theorem B6182239 : Blo 1445542 6182239 := bstep (se 1 (by rfl) ⟨4636679, by rfl⟩ : syracuseStep 6182239 = 9273359) B9273359
theorem B7320941 : Blo 1445542 7320941 := bstep (se 3 (by rfl) ⟨1372676, by rfl⟩ : syracuseStep 7320941 = 2745353) B2745353
theorem B1447279 : Blo 1445542 1447279 := bstep (se 1 (by rfl) ⟨1085459, by rfl⟩ : syracuseStep 1447279 = 2170919) B2170919
theorem B5494139 : Blo 1445542 5494139 := bstep (se 1 (by rfl) ⟨4120604, by rfl⟩ : syracuseStep 5494139 = 8241209) B8241209
theorem B1447335 : Blo 1445542 1447335 := bstep (se 1 (by rfl) ⟨1085501, by rfl⟩ : syracuseStep 1447335 = 2171003) B2171003
theorem B3659195 : Blo 1445542 3659195 := bstep (se 1 (by rfl) ⟨2744396, by rfl⟩ : syracuseStep 3659195 = 5488793) B5488793
theorem B1627591 : Blo 1445542 1627591 := bstep (se 1 (by rfl) ⟨1220693, by rfl⟩ : syracuseStep 1627591 = 2441387) B2441387
theorem B9901549 : Blo 1445542 9901549 := bstep (se 3 (by rfl) ⟨1856540, by rfl⟩ : syracuseStep 9901549 = 3713081) B3713081
theorem B1447419 : Blo 1445542 1447419 := bstep (se 1 (by rfl) ⟨1085564, by rfl⟩ : syracuseStep 1447419 = 2171129) B2171129
theorem B1447487 : Blo 1445542 1447487 := bstep (se 1 (by rfl) ⟨1085615, by rfl⟩ : syracuseStep 1447487 = 2171231) B2171231
theorem B1447495 : Blo 1445542 1447495 := bstep (se 1 (by rfl) ⟨1085621, by rfl⟩ : syracuseStep 1447495 = 2171243) B2171243
theorem B2168555 : Blo 1445542 2168555 := bstep (se 1 (by rfl) ⟨1626416, by rfl⟩ : syracuseStep 2168555 = 3252833) B3252833
theorem B1627951 : Blo 1445542 1627951 := bstep (se 1 (by rfl) ⟨1220963, by rfl⟩ : syracuseStep 1627951 = 2441927) B2441927
theorem B4118327 : Blo 1445542 4118327 := bstep (se 1 (by rfl) ⟨3088745, by rfl⟩ : syracuseStep 4118327 = 6177491) B6177491
theorem B1628059 : Blo 1445542 1628059 := bstep (se 1 (by rfl) ⟨1221044, by rfl⟩ : syracuseStep 1628059 = 2442089) B2442089
theorem B15644603 : Blo 1445542 15644603 := bstep (se 1 (by rfl) ⟨11733452, by rfl⟩ : syracuseStep 15644603 = 23466905) B23466905
theorem B2168783 : Blo 1445542 2168783 := bstep (se 1 (by rfl) ⟨1626587, by rfl⟩ : syracuseStep 2168783 = 3253175) B3253175
theorem B4880519 : Blo 1445542 4880519 := bstep (se 1 (by rfl) ⟨3660389, by rfl⟩ : syracuseStep 4880519 = 7320779) B7320779
theorem B4634759 : Blo 1445542 4634759 := bstep (se 1 (by rfl) ⟨3476069, by rfl⟩ : syracuseStep 4634759 = 6952139) B6952139
theorem B1628455 : Blo 1445542 1628455 := bstep (se 1 (by rfl) ⟨1221341, by rfl⟩ : syracuseStep 1628455 = 2442683) B2442683
theorem B2169179 : Blo 1445542 2169179 := bstep (se 1 (by rfl) ⟨1626884, by rfl⟩ : syracuseStep 2169179 = 3253769) B3253769
theorem B2169407 : Blo 1445542 2169407 := bstep (se 1 (by rfl) ⟨1627055, by rfl⟩ : syracuseStep 2169407 = 3254111) B3254111
theorem B4119113 : Blo 1445542 4119113 := bstep (se 2 (by rfl) ⟨1544667, by rfl⟩ : syracuseStep 4119113 = 3089335) B3089335
theorem B20855369 : Blo 1445542 20855369 := bstep (se 2 (by rfl) ⟨7820763, by rfl⟩ : syracuseStep 20855369 = 15641527) B15641527
theorem B2439787 : Blo 1445542 2439787 := bstep (se 1 (by rfl) ⟨1829840, by rfl⟩ : syracuseStep 2439787 = 3659681) B3659681
theorem B2169527 : Blo 1445542 2169527 := bstep (se 1 (by rfl) ⟨1627145, by rfl⟩ : syracuseStep 2169527 = 3254291) B3254291
theorem B3660511 : Blo 1445542 3660511 := bstep (se 1 (by rfl) ⟨2745383, by rfl⟩ : syracuseStep 3660511 = 5490767) B5490767
theorem B3660623 : Blo 1445542 3660623 := bstep (se 1 (by rfl) ⟨2745467, by rfl⟩ : syracuseStep 3660623 = 5490935) B5490935
theorem B2440091 : Blo 1445542 2440091 := bstep (se 1 (by rfl) ⟨1830068, by rfl⟩ : syracuseStep 2440091 = 3660137) B3660137
theorem B2169755 : Blo 1445542 2169755 := bstep (se 1 (by rfl) ⟨1627316, by rfl⟩ : syracuseStep 2169755 = 3254633) B3254633
theorem B5495795 : Blo 1445542 5495795 := bstep (se 1 (by rfl) ⟨4121846, by rfl⟩ : syracuseStep 5495795 = 8243693) B8243693
theorem B21437459 : Blo 1445542 21437459 := bstep (se 1 (by rfl) ⟨16078094, by rfl⟩ : syracuseStep 21437459 = 32156189) B32156189
theorem B10984571 : Blo 1445542 10984571 := bstep (se 1 (by rfl) ⟨8238428, by rfl⟩ : syracuseStep 10984571 = 16476857) B16476857
theorem B8240251 : Blo 1445542 8240251 := bstep (se 1 (by rfl) ⟨6180188, by rfl⟩ : syracuseStep 8240251 = 12360377) B12360377
theorem B2170151 : Blo 1445542 2170151 := bstep (se 1 (by rfl) ⟨1627613, by rfl⟩ : syracuseStep 2170151 = 3255227) B3255227
theorem B12524867 : Blo 1445542 12524867 := bstep (se 1 (by rfl) ⟨9393650, by rfl⟩ : syracuseStep 12524867 = 18787301) B18787301
theorem B20847941 : Blo 1445542 20847941 := bstep (se 4 (by rfl) ⟨1954494, by rfl⟩ : syracuseStep 20847941 = 3908989) B3908989
theorem B4881761 : Blo 1445542 4881761 := bstep (se 2 (by rfl) ⟨1830660, by rfl⟩ : syracuseStep 4881761 = 3661321) B3661321
theorem B2170235 : Blo 1445542 2170235 := bstep (se 1 (by rfl) ⟨1627676, by rfl⟩ : syracuseStep 2170235 = 3255353) B3255353
theorem B4636091 : Blo 1445542 4636091 := bstep (se 1 (by rfl) ⟨3477068, by rfl⟩ : syracuseStep 4636091 = 6954137) B6954137
theorem B3661271 : Blo 1445542 3661271 := bstep (se 1 (by rfl) ⟨2745953, by rfl⟩ : syracuseStep 3661271 = 5491907) B5491907
theorem B2170361 : Blo 1445542 2170361 := bstep (se 2 (by rfl) ⟨813885, by rfl⟩ : syracuseStep 2170361 = 1627771) B1627771
theorem B2170463 : Blo 1445542 2170463 := bstep (se 1 (by rfl) ⟨1627847, by rfl⟩ : syracuseStep 2170463 = 3255695) B3255695
theorem B13893281 : Blo 1445542 13893281 := bstep (se 2 (by rfl) ⟨5209980, by rfl⟩ : syracuseStep 13893281 = 10419961) B10419961
theorem B7323371 : Blo 1445542 7323371 := bstep (se 1 (by rfl) ⟨5492528, by rfl⟩ : syracuseStep 7323371 = 10985057) B10985057
theorem B4398889 : Blo 1445542 4398889 := bstep (se 2 (by rfl) ⟨1649583, by rfl⟩ : syracuseStep 4398889 = 3299167) B3299167
theorem B2170679 : Blo 1445542 2170679 := bstep (se 1 (by rfl) ⟨1628009, by rfl⟩ : syracuseStep 2170679 = 3256019) B3256019
theorem B3661625 : Blo 1445542 3661625 := bstep (se 2 (by rfl) ⟨1373109, by rfl⟩ : syracuseStep 3661625 = 2746219) B2746219
theorem B3473281 : Blo 1445542 3473281 := bstep (se 2 (by rfl) ⟨1302480, by rfl⟩ : syracuseStep 3473281 = 2604961) B2604961
theorem B9265211 : Blo 1445542 9265211 := bstep (se 1 (by rfl) ⟨6948908, by rfl⟩ : syracuseStep 9265211 = 13897817) B13897817
theorem B4882571 : Blo 1445542 4882571 := bstep (se 1 (by rfl) ⟨3661928, by rfl⟩ : syracuseStep 4882571 = 7323857) B7323857
theorem B2171099 : Blo 1445542 2171099 := bstep (se 1 (by rfl) ⟨1628324, by rfl⟩ : syracuseStep 2171099 = 3256649) B3256649
theorem B2171111 : Blo 1445542 2171111 := bstep (se 1 (by rfl) ⟨1628333, by rfl⟩ : syracuseStep 2171111 = 3256667) B3256667
theorem B3662111 : Blo 1445542 3662111 := bstep (se 1 (by rfl) ⟨2746583, by rfl⟩ : syracuseStep 3662111 = 5493167) B5493167
theorem B41681213 : Blo 1445542 41681213 := bstep (se 3 (by rfl) ⟨7815227, by rfl⟩ : syracuseStep 41681213 = 15630455) B15630455
theorem B2171273 : Blo 1445542 2171273 := bstep (se 2 (by rfl) ⟨814227, by rfl⟩ : syracuseStep 2171273 = 1628455) B1628455
theorem B4882895 : Blo 1445542 4882895 := bstep (se 1 (by rfl) ⟨3662171, by rfl⟩ : syracuseStep 4882895 = 7324343) B7324343
theorem B36135443 : Blo 1445542 36135443 := bstep (se 1 (by rfl) ⟨27101582, by rfl⟩ : syracuseStep 36135443 = 54203165) B54203165
theorem B6177455 : Blo 1445542 6177455 := bstep (se 1 (by rfl) ⟨4633091, by rfl⟩ : syracuseStep 6177455 = 9266183) B9266183
theorem B10420973 : Blo 1445542 10420973 := bstep (se 3 (by rfl) ⟨1953932, by rfl⟩ : syracuseStep 10420973 = 3907865) B3907865
theorem B4883219 : Blo 1445542 4883219 := bstep (se 1 (by rfl) ⟨3662414, by rfl⟩ : syracuseStep 4883219 = 7324829) B7324829
theorem B3253049 : Blo 1445542 3253049 := bstep (se 2 (by rfl) ⟨1219893, by rfl⟩ : syracuseStep 3253049 = 2439787) B2439787
theorem B76235579 : Blo 1445542 76235579 := bstep (se 1 (by rfl) ⟨57176684, by rfl⟩ : syracuseStep 76235579 = 114353369) B114353369
theorem B3253103 : Blo 1445542 3253103 := bstep (se 1 (by rfl) ⟨2439827, by rfl⟩ : syracuseStep 3253103 = 4879655) B4879655
theorem B3662759 : Blo 1445542 3662759 := bstep (se 1 (by rfl) ⟨2747069, by rfl⟩ : syracuseStep 3662759 = 5494139) B5494139
theorem B8242235 : Blo 1445542 8242235 := bstep (se 1 (by rfl) ⟨6181676, by rfl⟩ : syracuseStep 8242235 = 12363353) B12363353
theorem B15647849 : Blo 1445542 15647849 := bstep (se 2 (by rfl) ⟨5867943, by rfl⟩ : syracuseStep 15647849 = 11735887) B11735887
theorem B2745551 : Blo 1445542 2745551 := bstep (se 1 (by rfl) ⟨2059163, by rfl⟩ : syracuseStep 2745551 = 4118327) B4118327
theorem B10429735 : Blo 1445542 10429735 := bstep (se 1 (by rfl) ⟨7822301, by rfl⟩ : syracuseStep 10429735 = 15644603) B15644603
theorem B3253679 : Blo 1445542 3253679 := bstep (se 1 (by rfl) ⟨2440259, by rfl⟩ : syracuseStep 3253679 = 4880519) B4880519
theorem B3089839 : Blo 1445542 3089839 := bstep (se 1 (by rfl) ⟨2317379, by rfl⟩ : syracuseStep 3089839 = 4634759) B4634759
theorem B10987001 : Blo 1445542 10987001 := bstep (se 2 (by rfl) ⟨4120125, by rfl⟩ : syracuseStep 10987001 = 8240251) B8240251
theorem B2606663 : Blo 1445542 2606663 := bstep (se 1 (by rfl) ⟨1954997, by rfl⟩ : syracuseStep 2606663 = 3909995) B3909995
theorem B4884083 : Blo 1445542 4884083 := bstep (se 1 (by rfl) ⟨3663062, by rfl⟩ : syracuseStep 4884083 = 7326125) B7326125
theorem B2746075 : Blo 1445542 2746075 := bstep (se 1 (by rfl) ⟨2059556, by rfl⟩ : syracuseStep 2746075 = 4119113) B4119113
theorem B13903579 : Blo 1445542 13903579 := bstep (se 1 (by rfl) ⟨10427684, by rfl⟩ : syracuseStep 13903579 = 20855369) B20855369
theorem B4884191 : Blo 1445542 4884191 := bstep (se 1 (by rfl) ⟨3663143, by rfl⟩ : syracuseStep 4884191 = 7326287) B7326287
theorem B2475743 : Blo 1445542 2475743 := bstep (se 1 (by rfl) ⟨1856807, by rfl⟩ : syracuseStep 2475743 = 3713615) B3713615
theorem B2606879 : Blo 1445542 2606879 := bstep (se 1 (by rfl) ⟨1955159, by rfl⟩ : syracuseStep 2606879 = 3910319) B3910319
theorem B8242985 : Blo 1445542 8242985 := bstep (se 2 (by rfl) ⟨3091119, by rfl⟩ : syracuseStep 8242985 = 6182239) B6182239
theorem B15632189 : Blo 1445542 15632189 := bstep (se 3 (by rfl) ⟨2931035, by rfl⟩ : syracuseStep 15632189 = 5862071) B5862071
theorem B4884353 : Blo 1445542 4884353 := bstep (se 2 (by rfl) ⟨1831632, by rfl⟩ : syracuseStep 4884353 = 3663265) B3663265
theorem B7325639 : Blo 1445542 7325639 := bstep (se 1 (by rfl) ⟨5494229, by rfl⟩ : syracuseStep 7325639 = 10988459) B10988459
theorem B3663863 : Blo 1445542 3663863 := bstep (se 1 (by rfl) ⟨2747897, by rfl⟩ : syracuseStep 3663863 = 5495795) B5495795
theorem B12519467 : Blo 1445542 12519467 := bstep (se 1 (by rfl) ⟨9389600, by rfl⟩ : syracuseStep 12519467 = 18779201) B18779201
theorem B20859059 : Blo 1445542 20859059 := bstep (se 1 (by rfl) ⟨15644294, by rfl⟩ : syracuseStep 20859059 = 31288589) B31288589
theorem B8349911 : Blo 1445542 8349911 := bstep (se 1 (by rfl) ⟨6262433, by rfl⟩ : syracuseStep 8349911 = 12524867) B12524867
theorem B3254507 : Blo 1445542 3254507 := bstep (se 1 (by rfl) ⟨2440880, by rfl⟩ : syracuseStep 3254507 = 4881761) B4881761
theorem B3090727 : Blo 1445542 3090727 := bstep (se 1 (by rfl) ⟨2318045, by rfl⟩ : syracuseStep 3090727 = 4636091) B4636091
theorem B4884893 : Blo 1445542 4884893 := bstep (se 3 (by rfl) ⟨915917, by rfl⟩ : syracuseStep 4884893 = 1831835) B1831835
theorem B4631041 : Blo 1445542 4631041 := bstep (se 2 (by rfl) ⟨1736640, by rfl⟩ : syracuseStep 4631041 = 3473281) B3473281
theorem B4885163 : Blo 1445542 4885163 := bstep (se 1 (by rfl) ⟨3663872, by rfl⟩ : syracuseStep 4885163 = 7327745) B7327745
theorem B8235695 : Blo 1445542 8235695 := bstep (se 1 (by rfl) ⟨6176771, by rfl⟩ : syracuseStep 8235695 = 12353543) B12353543
theorem B14101229 : Blo 1445542 14101229 := bstep (se 3 (by rfl) ⟨2643980, by rfl⟩ : syracuseStep 14101229 = 5287961) B5287961
theorem B2747191 : Blo 1445542 2747191 := bstep (se 1 (by rfl) ⟨2060393, by rfl⟩ : syracuseStep 2747191 = 4120787) B4120787
theorem B42249437 : Blo 1445542 42249437 := bstep (se 3 (by rfl) ⟨7921769, by rfl⟩ : syracuseStep 42249437 = 15843539) B15843539
theorem B16485605 : Blo 1445542 16485605 := bstep (se 4 (by rfl) ⟨1545525, by rfl⟩ : syracuseStep 16485605 = 3091051) B3091051
theorem B1543655 : Blo 1445542 1543655 := bstep (se 1 (by rfl) ⟨1157741, by rfl⟩ : syracuseStep 1543655 = 2315483) B2315483
theorem B3255803 : Blo 1445542 3255803 := bstep (se 1 (by rfl) ⟨2441852, by rfl⟩ : syracuseStep 3255803 = 4883705) B4883705
theorem B16469567 : Blo 1445542 16469567 := bstep (se 1 (by rfl) ⟨12352175, by rfl⟩ : syracuseStep 16469567 = 24704351) B24704351
theorem B16707167 : Blo 1445542 16707167 := bstep (se 1 (by rfl) ⟨12530375, by rfl⟩ : syracuseStep 16707167 = 25060751) B25060751
theorem B4632221 : Blo 1445542 4632221 := bstep (se 3 (by rfl) ⟨868541, by rfl⟩ : syracuseStep 4632221 = 1737083) B1737083
theorem B3255983 : Blo 1445542 3255983 := bstep (se 1 (by rfl) ⟨2441987, by rfl⟩ : syracuseStep 3255983 = 4883975) B4883975
theorem B1445703 : Blo 1445542 1445703 := bstep (se 1 (by rfl) ⟨1084277, by rfl⟩ : syracuseStep 1445703 = 2168555) B2168555
theorem B14839685 : Blo 1445542 14839685 := bstep (se 4 (by rfl) ⟨1391220, by rfl⟩ : syracuseStep 14839685 = 2782441) B2782441
theorem B1445855 : Blo 1445542 1445855 := bstep (se 1 (by rfl) ⟨1084391, by rfl⟩ : syracuseStep 1445855 = 2168783) B2168783
theorem B1446119 : Blo 1445542 1446119 := bstep (se 1 (by rfl) ⟨1084589, by rfl⟩ : syracuseStep 1446119 = 2169179) B2169179
theorem B3256631 : Blo 1445542 3256631 := bstep (se 1 (by rfl) ⟨2442473, by rfl⟩ : syracuseStep 3256631 = 4884947) B4884947
theorem B23458139 : Blo 1445542 23458139 := bstep (se 1 (by rfl) ⟨17593604, by rfl⟩ : syracuseStep 23458139 = 35187209) B35187209
theorem B1446271 : Blo 1445542 1446271 := bstep (se 1 (by rfl) ⟨1084703, by rfl⟩ : syracuseStep 1446271 = 2169407) B2169407
theorem B3256703 : Blo 1445542 3256703 := bstep (se 1 (by rfl) ⟨2442527, by rfl⟩ : syracuseStep 3256703 = 4885055) B4885055
theorem B1446351 : Blo 1445542 1446351 := bstep (se 1 (by rfl) ⟨1084763, by rfl⟩ : syracuseStep 1446351 = 2169527) B2169527
theorem B1626727 : Blo 1445542 1626727 := bstep (se 1 (by rfl) ⟨1220045, by rfl⟩ : syracuseStep 1626727 = 2440091) B2440091
theorem B1446503 : Blo 1445542 1446503 := bstep (se 1 (by rfl) ⟨1084877, by rfl⟩ : syracuseStep 1446503 = 2169755) B2169755
theorem B13202065 : Blo 1445542 13202065 := bstep (se 2 (by rfl) ⟨4950774, by rfl⟩ : syracuseStep 13202065 = 9901549) B9901549
theorem B5214881 : Blo 1445542 5214881 := bstep (se 2 (by rfl) ⟨1955580, by rfl⟩ : syracuseStep 5214881 = 3911161) B3911161
theorem B14291639 : Blo 1445542 14291639 := bstep (se 1 (by rfl) ⟨10718729, by rfl⟩ : syracuseStep 14291639 = 21437459) B21437459
theorem B4231961 : Blo 1445542 4231961 := bstep (se 2 (by rfl) ⟨1586985, by rfl⟩ : syracuseStep 4231961 = 3173971) B3173971
theorem B10425149 : Blo 1445542 10425149 := bstep (se 3 (by rfl) ⟨1954715, by rfl⟩ : syracuseStep 10425149 = 3909431) B3909431
theorem B1446767 : Blo 1445542 1446767 := bstep (se 1 (by rfl) ⟨1085075, by rfl⟩ : syracuseStep 1446767 = 2170151) B2170151
theorem B13898627 : Blo 1445542 13898627 := bstep (se 1 (by rfl) ⟨10423970, by rfl⟩ : syracuseStep 13898627 = 20847941) B20847941
theorem B1446823 : Blo 1445542 1446823 := bstep (se 1 (by rfl) ⟨1085117, by rfl⟩ : syracuseStep 1446823 = 2170235) B2170235
theorem B1446907 : Blo 1445542 1446907 := bstep (se 1 (by rfl) ⟨1085180, by rfl⟩ : syracuseStep 1446907 = 2170361) B2170361
theorem B1446975 : Blo 1445542 1446975 := bstep (se 1 (by rfl) ⟨1085231, by rfl⟩ : syracuseStep 1446975 = 2170463) B2170463
theorem B9262187 : Blo 1445542 9262187 := bstep (se 1 (by rfl) ⟨6946640, by rfl⟩ : syracuseStep 9262187 = 13893281) B13893281
theorem B7926923 : Blo 1445542 7926923 := bstep (se 1 (by rfl) ⟨5945192, by rfl⟩ : syracuseStep 7926923 = 11890385) B11890385
theorem B1447119 : Blo 1445542 1447119 := bstep (se 1 (by rfl) ⟨1085339, by rfl⟩ : syracuseStep 1447119 = 2170679) B2170679
theorem B12530963 : Blo 1445542 12530963 := bstep (se 1 (by rfl) ⟨9398222, by rfl⟩ : syracuseStep 12530963 = 18796445) B18796445
theorem B2315675 : Blo 1445542 2315675 := bstep (se 1 (by rfl) ⟨1736756, by rfl⟩ : syracuseStep 2315675 = 3473513) B3473513
theorem B1447323 : Blo 1445542 1447323 := bstep (se 1 (by rfl) ⟨1085492, by rfl⟩ : syracuseStep 1447323 = 2170985) B2170985
theorem B4117985 : Blo 1445542 4117985 := bstep (se 2 (by rfl) ⟨1544244, by rfl⟩ : syracuseStep 4117985 = 3088489) B3088489
theorem B1447535 : Blo 1445542 1447535 := bstep (se 1 (by rfl) ⟨1085651, by rfl⟩ : syracuseStep 1447535 = 2171303) B2171303
theorem B2168441 : Blo 1445542 2168441 := bstep (se 2 (by rfl) ⟨813165, by rfl⟩ : syracuseStep 2168441 = 1626331) B1626331
theorem B2168543 : Blo 1445542 2168543 := bstep (se 1 (by rfl) ⟨1626407, by rfl⟩ : syracuseStep 2168543 = 3252815) B3252815
theorem B2168639 : Blo 1445542 2168639 := bstep (se 1 (by rfl) ⟨1626479, by rfl⟩ : syracuseStep 2168639 = 3252959) B3252959
theorem B8239067 : Blo 1445542 8239067 := bstep (se 1 (by rfl) ⟨6179300, by rfl⟩ : syracuseStep 8239067 = 12358601) B12358601
theorem B2168807 : Blo 1445542 2168807 := bstep (se 1 (by rfl) ⟨1626605, by rfl⟩ : syracuseStep 2168807 = 3253211) B3253211
theorem B2168825 : Blo 1445542 2168825 := bstep (se 2 (by rfl) ⟨813309, by rfl⟩ : syracuseStep 2168825 = 1626619) B1626619
theorem B2168927 : Blo 1445542 2168927 := bstep (se 1 (by rfl) ⟨1626695, by rfl⟩ : syracuseStep 2168927 = 3253391) B3253391
theorem B2168987 : Blo 1445542 2168987 := bstep (se 1 (by rfl) ⟨1626740, by rfl⟩ : syracuseStep 2168987 = 3253481) B3253481
theorem B2316443 : Blo 1445542 2316443 := bstep (se 1 (by rfl) ⟨1737332, by rfl⟩ : syracuseStep 2316443 = 3474665) B3474665
theorem B2169023 : Blo 1445542 2169023 := bstep (se 1 (by rfl) ⟨1626767, by rfl⟩ : syracuseStep 2169023 = 3253535) B3253535
theorem B3659975 : Blo 1445542 3659975 := bstep (se 1 (by rfl) ⟨2744981, by rfl⟩ : syracuseStep 3659975 = 5489963) B5489963
theorem B2169065 : Blo 1445542 2169065 := bstep (se 2 (by rfl) ⟨813399, by rfl⟩ : syracuseStep 2169065 = 1626799) B1626799
theorem B2316521 : Blo 1445542 2316521 := bstep (se 2 (by rfl) ⟨868695, by rfl⟩ : syracuseStep 2316521 = 1737391) B1737391
theorem B4880627 : Blo 1445542 4880627 := bstep (se 1 (by rfl) ⟨3660470, by rfl⟩ : syracuseStep 4880627 = 7320941) B7320941
theorem B2439463 : Blo 1445542 2439463 := bstep (se 1 (by rfl) ⟨1829597, by rfl⟩ : syracuseStep 2439463 = 3659195) B3659195
theorem B4880681 : Blo 1445542 4880681 := bstep (se 2 (by rfl) ⟨1830255, by rfl⟩ : syracuseStep 4880681 = 3660511) B3660511
theorem B2169371 : Blo 1445542 2169371 := bstep (se 1 (by rfl) ⟨1627028, by rfl⟩ : syracuseStep 2169371 = 3254057) B3254057
theorem B2169449 : Blo 1445542 2169449 := bstep (se 2 (by rfl) ⟨813543, by rfl⟩ : syracuseStep 2169449 = 1627087) B1627087
theorem B2316905 : Blo 1445542 2316905 := bstep (se 2 (by rfl) ⟨868839, by rfl⟩ : syracuseStep 2316905 = 1737679) B1737679
theorem B67681025 : Blo 1445542 67681025 := bstep (se 2 (by rfl) ⟨25380384, by rfl⟩ : syracuseStep 67681025 = 50760769) B50760769
theorem B2169977 : Blo 1445542 2169977 := bstep (se 2 (by rfl) ⟨813741, by rfl⟩ : syracuseStep 2169977 = 1627483) B1627483
theorem B4398209 : Blo 1445542 4398209 := bstep (se 2 (by rfl) ⟨1649328, by rfl⟩ : syracuseStep 4398209 = 3298657) B3298657
theorem B2440415 : Blo 1445542 2440415 := bstep (se 1 (by rfl) ⟨1830311, by rfl⟩ : syracuseStep 2440415 = 3660623) B3660623
theorem B2170079 : Blo 1445542 2170079 := bstep (se 1 (by rfl) ⟨1627559, by rfl⟩ : syracuseStep 2170079 = 3255119) B3255119
theorem B2170121 : Blo 1445542 2170121 := bstep (se 2 (by rfl) ⟨813795, by rfl⟩ : syracuseStep 2170121 = 1627591) B1627591
theorem B2170223 : Blo 1445542 2170223 := bstep (se 1 (by rfl) ⟨1627667, by rfl⟩ : syracuseStep 2170223 = 3255335) B3255335
theorem B17833355 : Blo 1445542 17833355 := bstep (se 1 (by rfl) ⟨13375016, by rfl⟩ : syracuseStep 17833355 = 26750033) B26750033
theorem B7323047 : Blo 1445542 7323047 := bstep (se 1 (by rfl) ⟨5492285, by rfl⟩ : syracuseStep 7323047 = 10984571) B10984571
theorem B2170343 : Blo 1445542 2170343 := bstep (se 1 (by rfl) ⟨1627757, by rfl⟩ : syracuseStep 2170343 = 3255515) B3255515
theorem B2170475 : Blo 1445542 2170475 := bstep (se 1 (by rfl) ⟨1627856, by rfl⟩ : syracuseStep 2170475 = 3255713) B3255713
theorem B2440847 : Blo 1445542 2440847 := bstep (se 1 (by rfl) ⟨1830635, by rfl⟩ : syracuseStep 2440847 = 3661271) B3661271
theorem B9264851 : Blo 1445542 9264851 := bstep (se 1 (by rfl) ⟨6948638, by rfl⟩ : syracuseStep 9264851 = 13897277) B13897277
theorem B5865185 : Blo 1445542 5865185 := bstep (se 2 (by rfl) ⟨2199444, by rfl⟩ : syracuseStep 5865185 = 4398889) B4398889
theorem B2170601 : Blo 1445542 2170601 := bstep (se 2 (by rfl) ⟨813975, by rfl⟩ : syracuseStep 2170601 = 1627951) B1627951
theorem B3088199 : Blo 1445542 3088199 := bstep (se 1 (by rfl) ⟨2316149, by rfl⟩ : syracuseStep 3088199 = 4632299) B4632299
theorem B4882247 : Blo 1445542 4882247 := bstep (se 1 (by rfl) ⟨3661685, by rfl⟩ : syracuseStep 4882247 = 7323371) B7323371
theorem B2170745 : Blo 1445542 2170745 := bstep (se 2 (by rfl) ⟨814029, by rfl⟩ : syracuseStep 2170745 = 1628059) B1628059
theorem B2441083 : Blo 1445542 2441083 := bstep (se 1 (by rfl) ⟨1830812, by rfl⟩ : syracuseStep 2441083 = 3661625) B3661625
theorem B4882301 : Blo 1445542 4882301 := bstep (se 3 (by rfl) ⟨915431, by rfl⟩ : syracuseStep 4882301 = 1830863) B1830863
theorem B4120445 : Blo 1445542 4120445 := bstep (se 3 (by rfl) ⟨772583, by rfl⟩ : syracuseStep 4120445 = 1545167) B1545167
theorem B2170847 : Blo 1445542 2170847 := bstep (se 1 (by rfl) ⟨1628135, by rfl⟩ : syracuseStep 2170847 = 3256271) B3256271
theorem B18538469 : Blo 1445542 18538469 := bstep (se 4 (by rfl) ⟨1737981, by rfl⟩ : syracuseStep 18538469 = 3475963) B3475963
theorem B6176807 : Blo 1445542 6176807 := bstep (se 1 (by rfl) ⟨4632605, by rfl⟩ : syracuseStep 6176807 = 9265211) B9265211
theorem B2441407 : Blo 1445542 2441407 := bstep (se 1 (by rfl) ⟨1831055, by rfl⟩ : syracuseStep 2441407 = 3662111) B3662111
theorem B2171087 : Blo 1445542 2171087 := bstep (se 1 (by rfl) ⟨1628315, by rfl⟩ : syracuseStep 2171087 = 3256631) B3256631
theorem B27787475 : Blo 1445542 27787475 := bstep (se 1 (by rfl) ⟨20840606, by rfl⟩ : syracuseStep 27787475 = 41681213) B41681213
theorem B15638759 : Blo 1445542 15638759 := bstep (se 1 (by rfl) ⟨11729069, by rfl⟩ : syracuseStep 15638759 = 23458139) B23458139
theorem B2171135 : Blo 1445542 2171135 := bstep (se 1 (by rfl) ⟨1628351, by rfl⟩ : syracuseStep 2171135 = 3256703) B3256703
theorem B3252617 : Blo 1445542 3252617 := bstep (se 2 (by rfl) ⟨1219731, by rfl⟩ : syracuseStep 3252617 = 2439463) B2439463
theorem B4120969 : Blo 1445542 4120969 := bstep (se 2 (by rfl) ⟨1545363, by rfl⟩ : syracuseStep 4120969 = 3090727) B3090727
theorem B9527759 : Blo 1445542 9527759 := bstep (se 1 (by rfl) ⟨7145819, by rfl⟩ : syracuseStep 9527759 = 14291639) B14291639
theorem B55624157 : Blo 1445542 55624157 := bstep (se 3 (by rfl) ⟨10429529, by rfl⟩ : syracuseStep 55624157 = 20859059) B20859059
theorem B6947315 : Blo 1445542 6947315 := bstep (se 1 (by rfl) ⟨5210486, by rfl⟩ : syracuseStep 6947315 = 10420973) B10420973
theorem B50823719 : Blo 1445542 50823719 := bstep (se 1 (by rfl) ⟨38117789, by rfl⟩ : syracuseStep 50823719 = 76235579) B76235579
theorem B9265751 : Blo 1445542 9265751 := bstep (se 1 (by rfl) ⟨6949313, by rfl⟩ : syracuseStep 9265751 = 13898627) B13898627
theorem B2441839 : Blo 1445542 2441839 := bstep (se 1 (by rfl) ⟨1831379, by rfl⟩ : syracuseStep 2441839 = 3662759) B3662759
theorem B5284615 : Blo 1445542 5284615 := bstep (se 1 (by rfl) ⟨3963461, by rfl⟩ : syracuseStep 5284615 = 7926923) B7926923
theorem B2745323 : Blo 1445542 2745323 := bstep (se 1 (by rfl) ⟨2058992, by rfl⟩ : syracuseStep 2745323 = 4117985) B4117985
theorem B7324667 : Blo 1445542 7324667 := bstep (se 1 (by rfl) ⟨5493500, by rfl⟩ : syracuseStep 7324667 = 10987001) B10987001
theorem B1737775 : Blo 1445542 1737775 := bstep (se 1 (by rfl) ⟨1303331, by rfl⟩ : syracuseStep 1737775 = 2606663) B2606663
theorem B3662921 : Blo 1445542 3662921 := bstep (se 2 (by rfl) ⟨1373595, by rfl⟩ : syracuseStep 3662921 = 2747191) B2747191
theorem B1737919 : Blo 1445542 1737919 := bstep (se 1 (by rfl) ⟨1303439, by rfl⟩ : syracuseStep 1737919 = 2606879) B2606879
theorem B10421459 : Blo 1445542 10421459 := bstep (se 1 (by rfl) ⟨7816094, by rfl⟩ : syracuseStep 10421459 = 15632189) B15632189
theorem B4883759 : Blo 1445542 4883759 := bstep (se 1 (by rfl) ⟨3662819, by rfl⟩ : syracuseStep 4883759 = 7325639) B7325639
theorem B2442575 : Blo 1445542 2442575 := bstep (se 1 (by rfl) ⟨1831931, by rfl⟩ : syracuseStep 2442575 = 3663863) B3663863
theorem B3253751 : Blo 1445542 3253751 := bstep (se 1 (by rfl) ⟨2440313, by rfl⟩ : syracuseStep 3253751 = 4880627) B4880627
theorem B3253787 : Blo 1445542 3253787 := bstep (se 1 (by rfl) ⟨2440340, by rfl⟩ : syracuseStep 3253787 = 4880681) B4880681
theorem B24708725 : Blo 1445542 24708725 := bstep (se 5 (by rfl) ⟨1158221, by rfl⟩ : syracuseStep 24708725 = 2316443) B2316443
theorem B5490463 : Blo 1445542 5490463 := bstep (se 1 (by rfl) ⟨4117847, by rfl⟩ : syracuseStep 5490463 = 8235695) B8235695
theorem B37603277 : Blo 1445542 37603277 := bstep (se 3 (by rfl) ⟨7050614, by rfl⟩ : syracuseStep 37603277 = 14101229) B14101229
theorem B28166291 : Blo 1445542 28166291 := bstep (se 1 (by rfl) ⟨21124718, by rfl⟩ : syracuseStep 28166291 = 42249437) B42249437
theorem B11888903 : Blo 1445542 11888903 := bstep (se 1 (by rfl) ⟨8916677, by rfl⟩ : syracuseStep 11888903 = 17833355) B17833355
theorem B10979711 : Blo 1445542 10979711 := bstep (se 1 (by rfl) ⟨8234783, by rfl⟩ : syracuseStep 10979711 = 16469567) B16469567
theorem B3910123 : Blo 1445542 3910123 := bstep (se 1 (by rfl) ⟨2932592, by rfl⟩ : syracuseStep 3910123 = 5865185) B5865185
theorem B3254777 : Blo 1445542 3254777 := bstep (se 2 (by rfl) ⟨1220541, by rfl⟩ : syracuseStep 3254777 = 2441083) B2441083
theorem B2058799 : Blo 1445542 2058799 := bstep (se 1 (by rfl) ⟨1544099, by rfl⟩ : syracuseStep 2058799 = 3088199) B3088199
theorem B3254831 : Blo 1445542 3254831 := bstep (se 1 (by rfl) ⟨2441123, by rfl⟩ : syracuseStep 3254831 = 4882247) B4882247
theorem B3254867 : Blo 1445542 3254867 := bstep (se 1 (by rfl) ⟨2441150, by rfl⟩ : syracuseStep 3254867 = 4882301) B4882301
theorem B2746963 : Blo 1445542 2746963 := bstep (se 1 (by rfl) ⟨2060222, by rfl⟩ : syracuseStep 2746963 = 4120445) B4120445
theorem B3255047 : Blo 1445542 3255047 := bstep (se 1 (by rfl) ⟨2441285, by rfl⟩ : syracuseStep 3255047 = 4882571) B4882571
theorem B3255263 : Blo 1445542 3255263 := bstep (se 1 (by rfl) ⟨2441447, by rfl⟩ : syracuseStep 3255263 = 4882895) B4882895
theorem B3255479 : Blo 1445542 3255479 := bstep (se 1 (by rfl) ⟨2441609, by rfl⟩ : syracuseStep 3255479 = 4883219) B4883219
theorem B2821307 : Blo 1445542 2821307 := bstep (se 1 (by rfl) ⟨2115980, by rfl⟩ : syracuseStep 2821307 = 4231961) B4231961
theorem B6950099 : Blo 1445542 6950099 := bstep (se 1 (by rfl) ⟨5212574, by rfl⟩ : syracuseStep 6950099 = 10425149) B10425149
theorem B10431899 : Blo 1445542 10431899 := bstep (se 1 (by rfl) ⟨7823924, by rfl⟩ : syracuseStep 10431899 = 15647849) B15647849
theorem B1830367 : Blo 1445542 1830367 := bstep (se 1 (by rfl) ⟨1372775, by rfl⟩ : syracuseStep 1830367 = 2745551) B2745551
theorem B1543783 : Blo 1445542 1543783 := bstep (se 1 (by rfl) ⟨1157837, by rfl⟩ : syracuseStep 1543783 = 2315675) B2315675
theorem B3256055 : Blo 1445542 3256055 := bstep (se 1 (by rfl) ⟨2442041, by rfl⟩ : syracuseStep 3256055 = 4884083) B4884083
theorem B1445627 : Blo 1445542 1445627 := bstep (se 1 (by rfl) ⟨1084220, by rfl⟩ : syracuseStep 1445627 = 2168441) B2168441
theorem B1445695 : Blo 1445542 1445695 := bstep (se 1 (by rfl) ⟨1084271, by rfl⟩ : syracuseStep 1445695 = 2168543) B2168543
theorem B3256127 : Blo 1445542 3256127 := bstep (se 1 (by rfl) ⟨2442095, by rfl⟩ : syracuseStep 3256127 = 4884191) B4884191
theorem B1445759 : Blo 1445542 1445759 := bstep (se 1 (by rfl) ⟨1084319, by rfl⟩ : syracuseStep 1445759 = 2168639) B2168639
theorem B3256235 : Blo 1445542 3256235 := bstep (se 1 (by rfl) ⟨2442176, by rfl⟩ : syracuseStep 3256235 = 4884353) B4884353
theorem B4116413 : Blo 1445542 4116413 := bstep (se 3 (by rfl) ⟨771827, by rfl⟩ : syracuseStep 4116413 = 1543655) B1543655
theorem B5492711 : Blo 1445542 5492711 := bstep (se 1 (by rfl) ⟨4119533, by rfl⟩ : syracuseStep 5492711 = 8239067) B8239067
theorem B1445871 : Blo 1445542 1445871 := bstep (se 1 (by rfl) ⟨1084403, by rfl⟩ : syracuseStep 1445871 = 2168807) B2168807
theorem B1445883 : Blo 1445542 1445883 := bstep (se 1 (by rfl) ⟨1084412, by rfl⟩ : syracuseStep 1445883 = 2168825) B2168825
theorem B1445951 : Blo 1445542 1445951 := bstep (se 1 (by rfl) ⟨1084463, by rfl⟩ : syracuseStep 1445951 = 2168927) B2168927
theorem B1445991 : Blo 1445542 1445991 := bstep (se 1 (by rfl) ⟨1084493, by rfl⟩ : syracuseStep 1445991 = 2168987) B2168987
theorem B1446015 : Blo 1445542 1446015 := bstep (se 1 (by rfl) ⟨1084511, by rfl⟩ : syracuseStep 1446015 = 2169023) B2169023
theorem B5566607 : Blo 1445542 5566607 := bstep (se 1 (by rfl) ⟨4174955, by rfl⟩ : syracuseStep 5566607 = 8349911) B8349911
theorem B1446043 : Blo 1445542 1446043 := bstep (se 1 (by rfl) ⟨1084532, by rfl⟩ : syracuseStep 1446043 = 2169065) B2169065
theorem B1544347 : Blo 1445542 1544347 := bstep (se 1 (by rfl) ⟨1158260, by rfl⟩ : syracuseStep 1544347 = 2316521) B2316521
theorem B3256595 : Blo 1445542 3256595 := bstep (se 1 (by rfl) ⟨2442446, by rfl⟩ : syracuseStep 3256595 = 4884893) B4884893
theorem B1446247 : Blo 1445542 1446247 := bstep (se 1 (by rfl) ⟨1084685, by rfl⟩ : syracuseStep 1446247 = 2169371) B2169371
theorem B13906313 : Blo 1445542 13906313 := bstep (se 2 (by rfl) ⟨5214867, by rfl⟩ : syracuseStep 13906313 = 10429735) B10429735
theorem B1446299 : Blo 1445542 1446299 := bstep (se 1 (by rfl) ⟨1084724, by rfl⟩ : syracuseStep 1446299 = 2169449) B2169449
theorem B1544603 : Blo 1445542 1544603 := bstep (se 1 (by rfl) ⟨1158452, by rfl⟩ : syracuseStep 1544603 = 2316905) B2316905
theorem B13906349 : Blo 1445542 13906349 := bstep (se 3 (by rfl) ⟨2607440, by rfl⟩ : syracuseStep 13906349 = 5214881) B5214881
theorem B3256775 : Blo 1445542 3256775 := bstep (se 1 (by rfl) ⟨2442581, by rfl⟩ : syracuseStep 3256775 = 4885163) B4885163
theorem B1446651 : Blo 1445542 1446651 := bstep (se 1 (by rfl) ⟨1084988, by rfl⟩ : syracuseStep 1446651 = 2169977) B2169977
theorem B1626943 : Blo 1445542 1626943 := bstep (se 1 (by rfl) ⟨1220207, by rfl⟩ : syracuseStep 1626943 = 2440415) B2440415
theorem B1446719 : Blo 1445542 1446719 := bstep (se 1 (by rfl) ⟨1085039, by rfl⟩ : syracuseStep 1446719 = 2170079) B2170079
theorem B10990403 : Blo 1445542 10990403 := bstep (se 1 (by rfl) ⟨8242802, by rfl⟩ : syracuseStep 10990403 = 16485605) B16485605
theorem B1446747 : Blo 1445542 1446747 := bstep (se 1 (by rfl) ⟨1085060, by rfl⟩ : syracuseStep 1446747 = 2170121) B2170121
theorem B1446815 : Blo 1445542 1446815 := bstep (se 1 (by rfl) ⟨1085111, by rfl⟩ : syracuseStep 1446815 = 2170223) B2170223
theorem B1446895 : Blo 1445542 1446895 := bstep (se 1 (by rfl) ⟨1085171, by rfl⟩ : syracuseStep 1446895 = 2170343) B2170343
theorem B11138111 : Blo 1445542 11138111 := bstep (se 1 (by rfl) ⟨8353583, by rfl⟩ : syracuseStep 11138111 = 16707167) B16707167
theorem B1446983 : Blo 1445542 1446983 := bstep (se 1 (by rfl) ⟨1085237, by rfl⟩ : syracuseStep 1446983 = 2170475) B2170475
theorem B1627231 : Blo 1445542 1627231 := bstep (se 1 (by rfl) ⟨1220423, by rfl⟩ : syracuseStep 1627231 = 2440847) B2440847
theorem B1447067 : Blo 1445542 1447067 := bstep (se 1 (by rfl) ⟨1085300, by rfl⟩ : syracuseStep 1447067 = 2170601) B2170601
theorem B1447163 : Blo 1445542 1447163 := bstep (se 1 (by rfl) ⟨1085372, by rfl⟩ : syracuseStep 1447163 = 2170745) B2170745
theorem B9893123 : Blo 1445542 9893123 := bstep (se 1 (by rfl) ⟨7419842, by rfl⟩ : syracuseStep 9893123 = 14839685) B14839685
theorem B1447231 : Blo 1445542 1447231 := bstep (se 1 (by rfl) ⟨1085423, by rfl⟩ : syracuseStep 1447231 = 2170847) B2170847
theorem B12358979 : Blo 1445542 12358979 := bstep (se 1 (by rfl) ⟨9269234, by rfl⟩ : syracuseStep 12358979 = 18538469) B18538469
theorem B1447399 : Blo 1445542 1447399 := bstep (se 1 (by rfl) ⟨1085549, by rfl⟩ : syracuseStep 1447399 = 2171099) B2171099
theorem B1447407 : Blo 1445542 1447407 := bstep (se 1 (by rfl) ⟨1085555, by rfl⟩ : syracuseStep 1447407 = 2171111) B2171111
theorem B1447515 : Blo 1445542 1447515 := bstep (se 1 (by rfl) ⟨1085636, by rfl⟩ : syracuseStep 1447515 = 2171273) B2171273
theorem B24090295 : Blo 1445542 24090295 := bstep (se 1 (by rfl) ⟨18067721, by rfl⟩ : syracuseStep 24090295 = 36135443) B36135443
theorem B4118303 : Blo 1445542 4118303 := bstep (se 1 (by rfl) ⟨3088727, by rfl⟩ : syracuseStep 4118303 = 6177455) B6177455
theorem B2168699 : Blo 1445542 2168699 := bstep (se 1 (by rfl) ⟨1626524, by rfl⟩ : syracuseStep 2168699 = 3253049) B3253049
theorem B2168735 : Blo 1445542 2168735 := bstep (se 1 (by rfl) ⟨1626551, by rfl⟩ : syracuseStep 2168735 = 3253103) B3253103
theorem B6174721 : Blo 1445542 6174721 := bstep (se 2 (by rfl) ⟨2315520, by rfl⟩ : syracuseStep 6174721 = 4631041) B4631041
theorem B5494823 : Blo 1445542 5494823 := bstep (se 1 (by rfl) ⟨4121117, by rfl⟩ : syracuseStep 5494823 = 8242235) B8242235
theorem B6174791 : Blo 1445542 6174791 := bstep (se 1 (by rfl) ⟨4631093, by rfl⟩ : syracuseStep 6174791 = 9262187) B9262187
theorem B2168969 : Blo 1445542 2168969 := bstep (se 2 (by rfl) ⟨813363, by rfl⟩ : syracuseStep 2168969 = 1626727) B1626727
theorem B8353975 : Blo 1445542 8353975 := bstep (se 1 (by rfl) ⟨6265481, by rfl⟩ : syracuseStep 8353975 = 12530963) B12530963
theorem B17602753 : Blo 1445542 17602753 := bstep (se 2 (by rfl) ⟨6601032, by rfl⟩ : syracuseStep 17602753 = 13202065) B13202065
theorem B2169119 : Blo 1445542 2169119 := bstep (se 1 (by rfl) ⟨1626839, by rfl⟩ : syracuseStep 2169119 = 3253679) B3253679
theorem B5495323 : Blo 1445542 5495323 := bstep (se 1 (by rfl) ⟨4121492, by rfl⟩ : syracuseStep 5495323 = 8242985) B8242985
theorem B8346311 : Blo 1445542 8346311 := bstep (se 1 (by rfl) ⟨6259733, by rfl⟩ : syracuseStep 8346311 = 12519467) B12519467
theorem B2439983 : Blo 1445542 2439983 := bstep (se 1 (by rfl) ⟨1829987, by rfl⟩ : syracuseStep 2439983 = 3659975) B3659975
theorem B2169671 : Blo 1445542 2169671 := bstep (se 1 (by rfl) ⟨1627253, by rfl⟩ : syracuseStep 2169671 = 3254507) B3254507
theorem B45120683 : Blo 1445542 45120683 := bstep (se 1 (by rfl) ⟨33840512, by rfl⟩ : syracuseStep 45120683 = 67681025) B67681025
theorem B4119785 : Blo 1445542 4119785 := bstep (se 2 (by rfl) ⟨1544919, by rfl⟩ : syracuseStep 4119785 = 3089839) B3089839
theorem B6601981 : Blo 1445542 6601981 := bstep (se 3 (by rfl) ⟨1237871, by rfl⟩ : syracuseStep 6601981 = 2475743) B2475743
theorem B2932139 : Blo 1445542 2932139 := bstep (se 1 (by rfl) ⟨2199104, by rfl⟩ : syracuseStep 2932139 = 4398209) B4398209
theorem B4882031 : Blo 1445542 4882031 := bstep (se 1 (by rfl) ⟨3661523, by rfl⟩ : syracuseStep 4882031 = 7323047) B7323047
theorem B3661433 : Blo 1445542 3661433 := bstep (se 2 (by rfl) ⟨1373037, by rfl⟩ : syracuseStep 3661433 = 2746075) B2746075
theorem B18538105 : Blo 1445542 18538105 := bstep (se 2 (by rfl) ⟨6951789, by rfl⟩ : syracuseStep 18538105 = 13903579) B13903579
theorem B2170535 : Blo 1445542 2170535 := bstep (se 1 (by rfl) ⟨1627901, by rfl⟩ : syracuseStep 2170535 = 3255803) B3255803
theorem B3088147 : Blo 1445542 3088147 := bstep (se 1 (by rfl) ⟨2316110, by rfl⟩ : syracuseStep 3088147 = 4632221) B4632221
theorem B2170655 : Blo 1445542 2170655 := bstep (se 1 (by rfl) ⟨1627991, by rfl⟩ : syracuseStep 2170655 = 3255983) B3255983
theorem B6176567 : Blo 1445542 6176567 := bstep (se 1 (by rfl) ⟨4632425, by rfl⟩ : syracuseStep 6176567 = 9264851) B9264851
theorem B8232961 : Blo 1445542 8232961 := bstep (se 2 (by rfl) ⟨3087360, by rfl⟩ : syracuseStep 8232961 = 6174721) B6174721
theorem B3711071 : Blo 1445542 3711071 := bstep (se 1 (by rfl) ⟨2783303, by rfl⟩ : syracuseStep 3711071 = 5566607) B5566607
theorem B2171063 : Blo 1445542 2171063 := bstep (se 1 (by rfl) ⟨1628297, by rfl⟩ : syracuseStep 2171063 = 3256595) B3256595
theorem B23470337 : Blo 1445542 23470337 := bstep (se 2 (by rfl) ⟨8801376, by rfl⟩ : syracuseStep 23470337 = 17602753) B17602753
theorem B2171183 : Blo 1445542 2171183 := bstep (se 1 (by rfl) ⟨1628387, by rfl⟩ : syracuseStep 2171183 = 3256775) B3256775
theorem B33882479 : Blo 1445542 33882479 := bstep (se 1 (by rfl) ⟨25411859, by rfl⟩ : syracuseStep 33882479 = 50823719) B50823719
theorem B6177167 : Blo 1445542 6177167 := bstep (se 1 (by rfl) ⟨4632875, by rfl⟩ : syracuseStep 6177167 = 9265751) B9265751
theorem B4883111 : Blo 1445542 4883111 := bstep (se 1 (by rfl) ⟨3662333, by rfl⟩ : syracuseStep 4883111 = 7324667) B7324667
theorem B2441947 : Blo 1445542 2441947 := bstep (se 1 (by rfl) ⟨1831460, by rfl⟩ : syracuseStep 2441947 = 3662921) B3662921
theorem B2745065 : Blo 1445542 2745065 := bstep (se 2 (by rfl) ⟨1029399, by rfl⟩ : syracuseStep 2745065 = 2058799) B2058799
theorem B3662617 : Blo 1445542 3662617 := bstep (se 2 (by rfl) ⟨1373481, by rfl⟩ : syracuseStep 3662617 = 2746963) B2746963
theorem B6947639 : Blo 1445542 6947639 := bstep (se 1 (by rfl) ⟨5210729, by rfl⟩ : syracuseStep 6947639 = 10421459) B10421459
theorem B6595415 : Blo 1445542 6595415 := bstep (se 1 (by rfl) ⟨4946561, by rfl⟩ : syracuseStep 6595415 = 9893123) B9893123
theorem B7046153 : Blo 1445542 7046153 := bstep (se 2 (by rfl) ⟨2642307, by rfl⟩ : syracuseStep 7046153 = 5284615) B5284615
theorem B25068851 : Blo 1445542 25068851 := bstep (se 1 (by rfl) ⟨18801638, by rfl⟩ : syracuseStep 25068851 = 37603277) B37603277
theorem B3663215 : Blo 1445542 3663215 := bstep (se 1 (by rfl) ⟨2747411, by rfl⟩ : syracuseStep 3663215 = 5494823) B5494823
theorem B18777527 : Blo 1445542 18777527 := bstep (se 1 (by rfl) ⟨14083145, by rfl⟩ : syracuseStep 18777527 = 28166291) B28166291
theorem B5564207 : Blo 1445542 5564207 := bstep (se 1 (by rfl) ⟨4173155, by rfl⟩ : syracuseStep 5564207 = 8346311) B8346311
theorem B2058377 : Blo 1445542 2058377 := bstep (se 2 (by rfl) ⟨771891, by rfl⟩ : syracuseStep 2058377 = 1543783) B1543783
theorem B2746523 : Blo 1445542 2746523 := bstep (se 1 (by rfl) ⟨2059892, by rfl⟩ : syracuseStep 2746523 = 4119785) B4119785
theorem B24717473 : Blo 1445542 24717473 := bstep (se 2 (by rfl) ⟨9269052, by rfl⟩ : syracuseStep 24717473 = 18538105) B18538105
theorem B3254687 : Blo 1445542 3254687 := bstep (se 1 (by rfl) ⟨2441015, by rfl⟩ : syracuseStep 3254687 = 4882031) B4882031
theorem B18524983 : Blo 1445542 18524983 := bstep (se 1 (by rfl) ⟨13893737, by rfl⟩ : syracuseStep 18524983 = 27787475) B27787475
theorem B2059129 : Blo 1445542 2059129 := bstep (se 2 (by rfl) ⟨772173, by rfl⟩ : syracuseStep 2059129 = 1544347) B1544347
theorem B3255209 : Blo 1445542 3255209 := bstep (se 2 (by rfl) ⟨1220703, by rfl⟩ : syracuseStep 3255209 = 2441407) B2441407
theorem B6351839 : Blo 1445542 6351839 := bstep (se 1 (by rfl) ⟨4763879, by rfl⟩ : syracuseStep 6351839 = 9527759) B9527759
theorem B4631543 : Blo 1445542 4631543 := bstep (se 1 (by rfl) ⟨3473657, by rfl⟩ : syracuseStep 4631543 = 6947315) B6947315
theorem B7523485 : Blo 1445542 7523485 := bstep (se 3 (by rfl) ⟨1410653, by rfl⟩ : syracuseStep 7523485 = 2821307) B2821307
theorem B7326935 : Blo 1445542 7326935 := bstep (se 1 (by rfl) ⟨5495201, by rfl⟩ : syracuseStep 7326935 = 10990403) B10990403
theorem B5213497 : Blo 1445542 5213497 := bstep (se 2 (by rfl) ⟨1955061, by rfl⟩ : syracuseStep 5213497 = 3910123) B3910123
theorem B1830215 : Blo 1445542 1830215 := bstep (se 1 (by rfl) ⟨1372661, by rfl⟩ : syracuseStep 1830215 = 2745323) B2745323
theorem B7327097 : Blo 1445542 7327097 := bstep (se 2 (by rfl) ⟨2747661, by rfl⟩ : syracuseStep 7327097 = 5495323) B5495323
theorem B7425407 : Blo 1445542 7425407 := bstep (se 1 (by rfl) ⟨5569055, by rfl⟩ : syracuseStep 7425407 = 11138111) B11138111
theorem B3255785 : Blo 1445542 3255785 := bstep (se 2 (by rfl) ⟨1220919, by rfl⟩ : syracuseStep 3255785 = 2441839) B2441839
theorem B3255839 : Blo 1445542 3255839 := bstep (se 1 (by rfl) ⟨2441879, by rfl⟩ : syracuseStep 3255839 = 4883759) B4883759
theorem B9268901 : Blo 1445542 9268901 := bstep (se 4 (by rfl) ⟨868959, by rfl⟩ : syracuseStep 9268901 = 1737919) B1737919
theorem B1445799 : Blo 1445542 1445799 := bstep (se 1 (by rfl) ⟨1084349, by rfl⟩ : syracuseStep 1445799 = 2168699) B2168699
theorem B1445823 : Blo 1445542 1445823 := bstep (se 1 (by rfl) ⟨1084367, by rfl⟩ : syracuseStep 1445823 = 2168735) B2168735
theorem B4116527 : Blo 1445542 4116527 := bstep (se 1 (by rfl) ⟨3087395, by rfl⟩ : syracuseStep 4116527 = 6174791) B6174791
theorem B1445979 : Blo 1445542 1445979 := bstep (se 1 (by rfl) ⟨1084484, by rfl⟩ : syracuseStep 1445979 = 2168969) B2168969
theorem B7925935 : Blo 1445542 7925935 := bstep (se 1 (by rfl) ⟨5944451, by rfl⟩ : syracuseStep 7925935 = 11888903) B11888903
theorem B1446079 : Blo 1445542 1446079 := bstep (se 1 (by rfl) ⟨1084559, by rfl⟩ : syracuseStep 1446079 = 2169119) B2169119
theorem B7319807 : Blo 1445542 7319807 := bstep (se 1 (by rfl) ⟨5489855, by rfl⟩ : syracuseStep 7319807 = 10979711) B10979711
theorem B8802641 : Blo 1445542 8802641 := bstep (se 2 (by rfl) ⟨3300990, by rfl⟩ : syracuseStep 8802641 = 6601981) B6601981
theorem B1626655 : Blo 1445542 1626655 := bstep (se 1 (by rfl) ⟨1219991, by rfl⟩ : syracuseStep 1626655 = 2439983) B2439983
theorem B1446447 : Blo 1445542 1446447 := bstep (se 1 (by rfl) ⟨1084835, by rfl⟩ : syracuseStep 1446447 = 2169671) B2169671
theorem B10982141 : Blo 1445542 10982141 := bstep (se 3 (by rfl) ⟨2059151, by rfl⟩ : syracuseStep 10982141 = 4118303) B4118303
theorem B4633399 : Blo 1445542 4633399 := bstep (se 1 (by rfl) ⟨3475049, by rfl⟩ : syracuseStep 4633399 = 6950099) B6950099
theorem B1954759 : Blo 1445542 1954759 := bstep (se 1 (by rfl) ⟨1466069, by rfl⟩ : syracuseStep 1954759 = 2932139) B2932139
theorem B4117529 : Blo 1445542 4117529 := bstep (se 2 (by rfl) ⟨1544073, by rfl⟩ : syracuseStep 4117529 = 3088147) B3088147
theorem B7320617 : Blo 1445542 7320617 := bstep (se 2 (by rfl) ⟨2745231, by rfl⟩ : syracuseStep 7320617 = 5490463) B5490463
theorem B1447023 : Blo 1445542 1447023 := bstep (se 1 (by rfl) ⟨1085267, by rfl⟩ : syracuseStep 1447023 = 2170535) B2170535
theorem B1447103 : Blo 1445542 1447103 := bstep (se 1 (by rfl) ⟨1085327, by rfl⟩ : syracuseStep 1447103 = 2170655) B2170655
theorem B4117711 : Blo 1445542 4117711 := bstep (se 1 (by rfl) ⟨3088283, by rfl⟩ : syracuseStep 4117711 = 6176567) B6176567
theorem B4117871 : Blo 1445542 4117871 := bstep (se 1 (by rfl) ⟨3088403, by rfl⟩ : syracuseStep 4117871 = 6176807) B6176807
theorem B1447391 : Blo 1445542 1447391 := bstep (se 1 (by rfl) ⟨1085543, by rfl⟩ : syracuseStep 1447391 = 2171087) B2171087
theorem B10425839 : Blo 1445542 10425839 := bstep (se 1 (by rfl) ⟨7819379, by rfl⟩ : syracuseStep 10425839 = 15638759) B15638759
theorem B1447423 : Blo 1445542 1447423 := bstep (se 1 (by rfl) ⟨1085567, by rfl⟩ : syracuseStep 1447423 = 2171135) B2171135
theorem B11138633 : Blo 1445542 11138633 := bstep (se 2 (by rfl) ⟨4176987, by rfl⟩ : syracuseStep 11138633 = 8353975) B8353975
theorem B2168411 : Blo 1445542 2168411 := bstep (se 1 (by rfl) ⟨1626308, by rfl⟩ : syracuseStep 2168411 = 3252617) B3252617
theorem B9270875 : Blo 1445542 9270875 := bstep (se 1 (by rfl) ⟨6953156, by rfl⟩ : syracuseStep 9270875 = 13906313) B13906313
theorem B9270899 : Blo 1445542 9270899 := bstep (se 1 (by rfl) ⟨6953174, by rfl⟩ : syracuseStep 9270899 = 13906349) B13906349
theorem B37082771 : Blo 1445542 37082771 := bstep (se 1 (by rfl) ⟨27812078, by rfl⟩ : syracuseStep 37082771 = 55624157) B55624157
theorem B120321821 : Blo 1445542 120321821 := bstep (se 3 (by rfl) ⟨22560341, by rfl⟩ : syracuseStep 120321821 = 45120683) B45120683
theorem B5494625 : Blo 1445542 5494625 := bstep (se 2 (by rfl) ⟨2060484, by rfl⟩ : syracuseStep 5494625 = 4120969) B4120969
theorem B8239319 : Blo 1445542 8239319 := bstep (se 1 (by rfl) ⟨6179489, by rfl⟩ : syracuseStep 8239319 = 12358979) B12358979
theorem B1628383 : Blo 1445542 1628383 := bstep (se 1 (by rfl) ⟨1221287, by rfl⟩ : syracuseStep 1628383 = 2442575) B2442575
theorem B2169167 : Blo 1445542 2169167 := bstep (se 1 (by rfl) ⟨1626875, by rfl⟩ : syracuseStep 2169167 = 3253751) B3253751
theorem B2169191 : Blo 1445542 2169191 := bstep (se 1 (by rfl) ⟨1626893, by rfl⟩ : syracuseStep 2169191 = 3253787) B3253787
theorem B4118941 : Blo 1445542 4118941 := bstep (se 3 (by rfl) ⟨772301, by rfl⟩ : syracuseStep 4118941 = 1544603) B1544603
theorem B16472483 : Blo 1445542 16472483 := bstep (se 1 (by rfl) ⟨12354362, by rfl⟩ : syracuseStep 16472483 = 24708725) B24708725
theorem B2169257 : Blo 1445542 2169257 := bstep (se 2 (by rfl) ⟨813471, by rfl⟩ : syracuseStep 2169257 = 1626943) B1626943
theorem B2317033 : Blo 1445542 2317033 := bstep (se 2 (by rfl) ⟨868887, by rfl⟩ : syracuseStep 2317033 = 1737775) B1737775
theorem B2169641 : Blo 1445542 2169641 := bstep (se 2 (by rfl) ⟨813615, by rfl⟩ : syracuseStep 2169641 = 1627231) B1627231
theorem B2169851 : Blo 1445542 2169851 := bstep (se 1 (by rfl) ⟨1627388, by rfl⟩ : syracuseStep 2169851 = 3254777) B3254777
theorem B2169887 : Blo 1445542 2169887 := bstep (se 1 (by rfl) ⟨1627415, by rfl⟩ : syracuseStep 2169887 = 3254831) B3254831
theorem B2169911 : Blo 1445542 2169911 := bstep (se 1 (by rfl) ⟨1627433, by rfl⟩ : syracuseStep 2169911 = 3254867) B3254867
theorem B2170031 : Blo 1445542 2170031 := bstep (se 1 (by rfl) ⟨1627523, by rfl⟩ : syracuseStep 2170031 = 3255047) B3255047
theorem B2440489 : Blo 1445542 2440489 := bstep (se 2 (by rfl) ⟨915183, by rfl⟩ : syracuseStep 2440489 = 1830367) B1830367
theorem B2170175 : Blo 1445542 2170175 := bstep (se 1 (by rfl) ⟨1627631, by rfl⟩ : syracuseStep 2170175 = 3255263) B3255263
theorem B2170319 : Blo 1445542 2170319 := bstep (se 1 (by rfl) ⟨1627739, by rfl⟩ : syracuseStep 2170319 = 3255479) B3255479
theorem B32120393 : Blo 1445542 32120393 := bstep (se 2 (by rfl) ⟨12045147, by rfl⟩ : syracuseStep 32120393 = 24090295) B24090295
theorem B6954599 : Blo 1445542 6954599 := bstep (se 1 (by rfl) ⟨5215949, by rfl⟩ : syracuseStep 6954599 = 10431899) B10431899
theorem B2440955 : Blo 1445542 2440955 := bstep (se 1 (by rfl) ⟨1830716, by rfl⟩ : syracuseStep 2440955 = 3661433) B3661433
theorem B2170703 : Blo 1445542 2170703 := bstep (se 1 (by rfl) ⟨1628027, by rfl⟩ : syracuseStep 2170703 = 3256055) B3256055
theorem B2170751 : Blo 1445542 2170751 := bstep (se 1 (by rfl) ⟨1628063, by rfl⟩ : syracuseStep 2170751 = 3256127) B3256127
theorem B2170823 : Blo 1445542 2170823 := bstep (se 1 (by rfl) ⟨1628117, by rfl⟩ : syracuseStep 2170823 = 3256235) B3256235
theorem B2744275 : Blo 1445542 2744275 := bstep (se 1 (by rfl) ⟨2058206, by rfl⟩ : syracuseStep 2744275 = 4116413) B4116413
theorem B3661807 : Blo 1445542 3661807 := bstep (se 1 (by rfl) ⟨2746355, by rfl⟩ : syracuseStep 3661807 = 5492711) B5492711
theorem B10977281 : Blo 1445542 10977281 := bstep (se 2 (by rfl) ⟨4116480, by rfl⟩ : syracuseStep 10977281 = 8232961) B8232961
theorem B2744351 : Blo 1445542 2744351 := bstep (se 1 (by rfl) ⟨2058263, by rfl⟩ : syracuseStep 2744351 = 4116527) B4116527
theorem B2474047 : Blo 1445542 2474047 := bstep (se 1 (by rfl) ⟨1855535, by rfl⟩ : syracuseStep 2474047 = 3711071) B3711071
theorem B10567913 : Blo 1445542 10567913 := bstep (se 2 (by rfl) ⟨3962967, by rfl⟩ : syracuseStep 10567913 = 7925935) B7925935
theorem B2171177 : Blo 1445542 2171177 := bstep (se 2 (by rfl) ⟨814191, by rfl⟩ : syracuseStep 2171177 = 1628383) B1628383
theorem B5489005 : Blo 1445542 5489005 := bstep (se 3 (by rfl) ⟨1029188, by rfl⟩ : syracuseStep 5489005 = 2058377) B2058377
theorem B62587565 : Blo 1445542 62587565 := bstep (se 3 (by rfl) ⟨11735168, by rfl⟩ : syracuseStep 62587565 = 23470337) B23470337
theorem B2745019 : Blo 1445542 2745019 := bstep (se 1 (by rfl) ⟨2058764, by rfl⟩ : syracuseStep 2745019 = 4117529) B4117529
theorem B16712567 : Blo 1445542 16712567 := bstep (se 1 (by rfl) ⟨12534425, by rfl⟩ : syracuseStep 16712567 = 25068851) B25068851
theorem B2745247 : Blo 1445542 2745247 := bstep (se 1 (by rfl) ⟨2058935, by rfl⟩ : syracuseStep 2745247 = 4117871) B4117871
theorem B2442143 : Blo 1445542 2442143 := bstep (se 1 (by rfl) ⟨1831607, by rfl⟩ : syracuseStep 2442143 = 3663215) B3663215
theorem B12518351 : Blo 1445542 12518351 := bstep (se 1 (by rfl) ⟨9388763, by rfl⟩ : syracuseStep 12518351 = 18777527) B18777527
theorem B3089377 : Blo 1445542 3089377 := bstep (se 2 (by rfl) ⟨1158516, by rfl⟩ : syracuseStep 3089377 = 2317033) B2317033
theorem B4883489 : Blo 1445542 4883489 := bstep (se 2 (by rfl) ⟨1831308, by rfl⟩ : syracuseStep 4883489 = 3662617) B3662617
theorem B24699977 : Blo 1445542 24699977 := bstep (se 2 (by rfl) ⟨9262491, by rfl⟩ : syracuseStep 24699977 = 18524983) B18524983
theorem B6177865 : Blo 1445542 6177865 := bstep (se 2 (by rfl) ⟨2316699, by rfl⟩ : syracuseStep 6177865 = 4633399) B4633399
theorem B2745505 : Blo 1445542 2745505 := bstep (se 2 (by rfl) ⟨1029564, by rfl⟩ : syracuseStep 2745505 = 2059129) B2059129
theorem B3663083 : Blo 1445542 3663083 := bstep (se 1 (by rfl) ⟨2747312, by rfl⟩ : syracuseStep 3663083 = 5494625) B5494625
theorem B2606345 : Blo 1445542 2606345 := bstep (se 2 (by rfl) ⟨977379, by rfl⟩ : syracuseStep 2606345 = 1954759) B1954759
theorem B5490281 : Blo 1445542 5490281 := bstep (se 2 (by rfl) ⟨2058855, by rfl⟩ : syracuseStep 5490281 = 4117711) B4117711
theorem B3253985 : Blo 1445542 3253985 := bstep (se 2 (by rfl) ⟨1220244, by rfl⟩ : syracuseStep 3253985 = 2440489) B2440489
theorem B4884623 : Blo 1445542 4884623 := bstep (se 1 (by rfl) ⟨3663467, by rfl⟩ : syracuseStep 4884623 = 7326935) B7326935
theorem B4884731 : Blo 1445542 4884731 := bstep (se 1 (by rfl) ⟨3663548, by rfl⟩ : syracuseStep 4884731 = 7327097) B7327097
theorem B4950271 : Blo 1445542 4950271 := bstep (se 1 (by rfl) ⟨3712703, by rfl⟩ : syracuseStep 4950271 = 7425407) B7425407
theorem B6179267 : Blo 1445542 6179267 := bstep (se 1 (by rfl) ⟨4634450, by rfl⟩ : syracuseStep 6179267 = 9268901) B9268901
theorem B22588319 : Blo 1445542 22588319 := bstep (se 1 (by rfl) ⟨16941239, by rfl⟩ : syracuseStep 22588319 = 33882479) B33882479
theorem B3255407 : Blo 1445542 3255407 := bstep (se 1 (by rfl) ⟨2441555, by rfl⟩ : syracuseStep 3255407 = 4883111) B4883111
theorem B1830043 : Blo 1445542 1830043 := bstep (se 1 (by rfl) ⟨1372532, by rfl⟩ : syracuseStep 1830043 = 2745065) B2745065
theorem B4631759 : Blo 1445542 4631759 := bstep (se 1 (by rfl) ⟨3473819, by rfl⟩ : syracuseStep 4631759 = 6947639) B6947639
theorem B5491921 : Blo 1445542 5491921 := bstep (se 2 (by rfl) ⟨2059470, by rfl⟩ : syracuseStep 5491921 = 4118941) B4118941
theorem B160501013 : Blo 1445542 160501013 := bstep (se 6 (by rfl) ⟨3761742, by rfl⟩ : syracuseStep 160501013 = 7523485) B7523485
theorem B4697435 : Blo 1445542 4697435 := bstep (se 1 (by rfl) ⟨3523076, by rfl⟩ : syracuseStep 4697435 = 7046153) B7046153
theorem B342617525 : Blo 1445542 342617525 := bstep (se 5 (by rfl) ⟨16060196, by rfl⟩ : syracuseStep 342617525 = 32120393) B32120393
theorem B23473709 : Blo 1445542 23473709 := bstep (se 3 (by rfl) ⟨4401320, by rfl⟩ : syracuseStep 23473709 = 8802641) B8802641
theorem B3255929 : Blo 1445542 3255929 := bstep (se 2 (by rfl) ⟨1220973, by rfl⟩ : syracuseStep 3255929 = 2441947) B2441947
theorem B7425755 : Blo 1445542 7425755 := bstep (se 1 (by rfl) ⟨5569316, by rfl⟩ : syracuseStep 7425755 = 11138633) B11138633
theorem B1445607 : Blo 1445542 1445607 := bstep (se 1 (by rfl) ⟨1084205, by rfl⟩ : syracuseStep 1445607 = 2168411) B2168411
theorem B6180583 : Blo 1445542 6180583 := bstep (se 1 (by rfl) ⟨4635437, by rfl⟩ : syracuseStep 6180583 = 9270875) B9270875
theorem B6180599 : Blo 1445542 6180599 := bstep (se 1 (by rfl) ⟨4635449, by rfl⟩ : syracuseStep 6180599 = 9270899) B9270899
theorem B1831015 : Blo 1445542 1831015 := bstep (se 1 (by rfl) ⟨1373261, by rfl⟩ : syracuseStep 1831015 = 2746523) B2746523
theorem B16478315 : Blo 1445542 16478315 := bstep (se 1 (by rfl) ⟨12358736, by rfl⟩ : syracuseStep 16478315 = 24717473) B24717473
theorem B5492879 : Blo 1445542 5492879 := bstep (se 1 (by rfl) ⟨4119659, by rfl⟩ : syracuseStep 5492879 = 8239319) B8239319
theorem B1446111 : Blo 1445542 1446111 := bstep (se 1 (by rfl) ⟨1084583, by rfl⟩ : syracuseStep 1446111 = 2169167) B2169167
theorem B1446127 : Blo 1445542 1446127 := bstep (se 1 (by rfl) ⟨1084595, by rfl⟩ : syracuseStep 1446127 = 2169191) B2169191
theorem B10981655 : Blo 1445542 10981655 := bstep (se 1 (by rfl) ⟨8236241, by rfl⟩ : syracuseStep 10981655 = 16472483) B16472483
theorem B1446171 : Blo 1445542 1446171 := bstep (se 1 (by rfl) ⟨1084628, by rfl⟩ : syracuseStep 1446171 = 2169257) B2169257
theorem B6951329 : Blo 1445542 6951329 := bstep (se 2 (by rfl) ⟨2606748, by rfl⟩ : syracuseStep 6951329 = 5213497) B5213497
theorem B1446427 : Blo 1445542 1446427 := bstep (se 1 (by rfl) ⟨1084820, by rfl⟩ : syracuseStep 1446427 = 2169641) B2169641
theorem B1446567 : Blo 1445542 1446567 := bstep (se 1 (by rfl) ⟨1084925, by rfl⟩ : syracuseStep 1446567 = 2169851) B2169851
theorem B1446591 : Blo 1445542 1446591 := bstep (se 1 (by rfl) ⟨1084943, by rfl⟩ : syracuseStep 1446591 = 2169887) B2169887
theorem B1446607 : Blo 1445542 1446607 := bstep (se 1 (by rfl) ⟨1084955, by rfl⟩ : syracuseStep 1446607 = 2169911) B2169911
theorem B1446687 : Blo 1445542 1446687 := bstep (se 1 (by rfl) ⟨1085015, by rfl⟩ : syracuseStep 1446687 = 2170031) B2170031
theorem B1446783 : Blo 1445542 1446783 := bstep (se 1 (by rfl) ⟨1085087, by rfl⟩ : syracuseStep 1446783 = 2170175) B2170175
theorem B1446879 : Blo 1445542 1446879 := bstep (se 1 (by rfl) ⟨1085159, by rfl⟩ : syracuseStep 1446879 = 2170319) B2170319
theorem B1627303 : Blo 1445542 1627303 := bstep (se 1 (by rfl) ⟨1220477, by rfl⟩ : syracuseStep 1627303 = 2440955) B2440955
theorem B1447135 : Blo 1445542 1447135 := bstep (se 1 (by rfl) ⟨1085351, by rfl⟩ : syracuseStep 1447135 = 2170703) B2170703
theorem B1447167 : Blo 1445542 1447167 := bstep (se 1 (by rfl) ⟨1085375, by rfl⟩ : syracuseStep 1447167 = 2170751) B2170751
theorem B3659033 : Blo 1445542 3659033 := bstep (se 2 (by rfl) ⟨1372137, by rfl⟩ : syracuseStep 3659033 = 2744275) B2744275
theorem B1447215 : Blo 1445542 1447215 := bstep (se 1 (by rfl) ⟨1085411, by rfl⟩ : syracuseStep 1447215 = 2170823) B2170823
theorem B1447375 : Blo 1445542 1447375 := bstep (se 1 (by rfl) ⟨1085531, by rfl⟩ : syracuseStep 1447375 = 2171063) B2171063
theorem B4879871 : Blo 1445542 4879871 := bstep (se 1 (by rfl) ⟨3659903, by rfl⟩ : syracuseStep 4879871 = 7319807) B7319807
theorem B1447455 : Blo 1445542 1447455 := bstep (se 1 (by rfl) ⟨1085591, by rfl⟩ : syracuseStep 1447455 = 2171183) B2171183
theorem B4118111 : Blo 1445542 4118111 := bstep (se 1 (by rfl) ⟨3088583, by rfl⟩ : syracuseStep 4118111 = 6177167) B6177167
theorem B7321427 : Blo 1445542 7321427 := bstep (se 1 (by rfl) ⟨5491070, by rfl⟩ : syracuseStep 7321427 = 10982141) B10982141
theorem B4396943 : Blo 1445542 4396943 := bstep (se 1 (by rfl) ⟨3297707, by rfl⟩ : syracuseStep 4396943 = 6595415) B6595415
theorem B4880411 : Blo 1445542 4880411 := bstep (se 1 (by rfl) ⟨3660308, by rfl⟩ : syracuseStep 4880411 = 7320617) B7320617
theorem B2168873 : Blo 1445542 2168873 := bstep (se 2 (by rfl) ⟨813327, by rfl⟩ : syracuseStep 2168873 = 1626655) B1626655
theorem B4880573 : Blo 1445542 4880573 := bstep (se 3 (by rfl) ⟨915107, by rfl⟩ : syracuseStep 4880573 = 1830215) B1830215
theorem B24721847 : Blo 1445542 24721847 := bstep (se 1 (by rfl) ⟨18541385, by rfl⟩ : syracuseStep 24721847 = 37082771) B37082771
theorem B80214547 : Blo 1445542 80214547 := bstep (se 1 (by rfl) ⟨60160910, by rfl⟩ : syracuseStep 80214547 = 120321821) B120321821
theorem B3709471 : Blo 1445542 3709471 := bstep (se 1 (by rfl) ⟨2782103, by rfl⟩ : syracuseStep 3709471 = 5564207) B5564207
theorem B27802237 : Blo 1445542 27802237 := bstep (se 3 (by rfl) ⟨5212919, by rfl⟩ : syracuseStep 27802237 = 10425839) B10425839
theorem B2169791 : Blo 1445542 2169791 := bstep (se 1 (by rfl) ⟨1627343, by rfl⟩ : syracuseStep 2169791 = 3254687) B3254687
theorem B2170139 : Blo 1445542 2170139 := bstep (se 1 (by rfl) ⟨1627604, by rfl⟩ : syracuseStep 2170139 = 3255209) B3255209
theorem B4234559 : Blo 1445542 4234559 := bstep (se 1 (by rfl) ⟨3175919, by rfl⟩ : syracuseStep 4234559 = 6351839) B6351839
theorem B3087695 : Blo 1445542 3087695 := bstep (se 1 (by rfl) ⟨2315771, by rfl⟩ : syracuseStep 3087695 = 4631543) B4631543
theorem B2170523 : Blo 1445542 2170523 := bstep (se 1 (by rfl) ⟨1627892, by rfl⟩ : syracuseStep 2170523 = 3255785) B3255785
theorem B2170559 : Blo 1445542 2170559 := bstep (se 1 (by rfl) ⟨1627919, by rfl⟩ : syracuseStep 2170559 = 3255839) B3255839
theorem B4636399 : Blo 1445542 4636399 := bstep (se 1 (by rfl) ⟨3477299, by rfl⟩ : syracuseStep 4636399 = 6954599) B6954599
theorem B4882409 : Blo 1445542 4882409 := bstep (se 2 (by rfl) ⟨1830903, by rfl⟩ : syracuseStep 4882409 = 3661807) B3661807
theorem B10985543 : Blo 1445542 10985543 := bstep (se 1 (by rfl) ⟨8239157, by rfl⟩ : syracuseStep 10985543 = 16478315) B16478315
theorem B3661919 : Blo 1445542 3661919 := bstep (se 1 (by rfl) ⟨2746439, by rfl⟩ : syracuseStep 3661919 = 5492879) B5492879
theorem B2441353 : Blo 1445542 2441353 := bstep (se 2 (by rfl) ⟨915507, by rfl⟩ : syracuseStep 2441353 = 1831015) B1831015
theorem B11141711 : Blo 1445542 11141711 := bstep (se 1 (by rfl) ⟨8356283, by rfl⟩ : syracuseStep 11141711 = 16712567) B16712567
theorem B16466651 : Blo 1445542 16466651 := bstep (se 1 (by rfl) ⟨12349988, by rfl⟩ : syracuseStep 16466651 = 24699977) B24699977
theorem B2442055 : Blo 1445542 2442055 := bstep (se 1 (by rfl) ⟨1831541, by rfl⟩ : syracuseStep 2442055 = 3663083) B3663083
theorem B37069649 : Blo 1445542 37069649 := bstep (se 2 (by rfl) ⟨13901118, by rfl⟩ : syracuseStep 37069649 = 27802237) B27802237
theorem B1737563 : Blo 1445542 1737563 := bstep (se 1 (by rfl) ⟨1303172, by rfl⟩ : syracuseStep 1737563 = 2606345) B2606345
theorem B3253247 : Blo 1445542 3253247 := bstep (se 1 (by rfl) ⟨2439935, by rfl⟩ : syracuseStep 3253247 = 4879871) B4879871
theorem B2745407 : Blo 1445542 2745407 := bstep (se 1 (by rfl) ⟨2059055, by rfl⟩ : syracuseStep 2745407 = 4118111) B4118111
theorem B3253607 : Blo 1445542 3253607 := bstep (se 1 (by rfl) ⟨2440205, by rfl⟩ : syracuseStep 3253607 = 4880411) B4880411
theorem B3253715 : Blo 1445542 3253715 := bstep (se 1 (by rfl) ⟨2440286, by rfl⟩ : syracuseStep 3253715 = 4880573) B4880573
theorem B15058879 : Blo 1445542 15058879 := bstep (se 1 (by rfl) ⟨11294159, by rfl⟩ : syracuseStep 15058879 = 22588319) B22588319
theorem B2058463 : Blo 1445542 2058463 := bstep (se 1 (by rfl) ⟨1543847, by rfl⟩ : syracuseStep 2058463 = 3087695) B3087695
theorem B3131623 : Blo 1445542 3131623 := bstep (se 1 (by rfl) ⟨2348717, by rfl⟩ : syracuseStep 3131623 = 4697435) B4697435
theorem B228411683 : Blo 1445542 228411683 := bstep (se 1 (by rfl) ⟨171308762, by rfl⟩ : syracuseStep 228411683 = 342617525) B342617525
theorem B15649139 : Blo 1445542 15649139 := bstep (se 1 (by rfl) ⟨11736854, by rfl⟩ : syracuseStep 15649139 = 23473709) B23473709
theorem B11725181 : Blo 1445542 11725181 := bstep (se 3 (by rfl) ⟨2198471, by rfl⟩ : syracuseStep 11725181 = 4396943) B4396943
theorem B112724405 : Blo 1445542 112724405 := bstep (se 5 (by rfl) ⟨5283956, by rfl⟩ : syracuseStep 112724405 = 10567913) B10567913
theorem B4950503 : Blo 1445542 4950503 := bstep (se 1 (by rfl) ⟨3712877, by rfl⟩ : syracuseStep 4950503 = 7425755) B7425755
theorem B3254939 : Blo 1445542 3254939 := bstep (se 1 (by rfl) ⟨2441204, by rfl⟩ : syracuseStep 3254939 = 4882409) B4882409
theorem B7318187 : Blo 1445542 7318187 := bstep (se 1 (by rfl) ⟨5488640, by rfl⟩ : syracuseStep 7318187 = 10977281) B10977281
theorem B1829567 : Blo 1445542 1829567 := bstep (se 1 (by rfl) ⟨1372175, by rfl⟩ : syracuseStep 1829567 = 2744351) B2744351
theorem B41725043 : Blo 1445542 41725043 := bstep (se 1 (by rfl) ⟨31293782, by rfl⟩ : syracuseStep 41725043 = 62587565) B62587565
theorem B7318673 : Blo 1445542 7318673 := bstep (se 2 (by rfl) ⟨2744502, by rfl⟩ : syracuseStep 7318673 = 5489005) B5489005
theorem B3255659 : Blo 1445542 3255659 := bstep (se 1 (by rfl) ⟨2441744, by rfl⟩ : syracuseStep 3255659 = 4883489) B4883489
theorem B11292157 : Blo 1445542 11292157 := bstep (se 3 (by rfl) ⟨2117279, by rfl⟩ : syracuseStep 11292157 = 4234559) B4234559
theorem B1445915 : Blo 1445542 1445915 := bstep (se 1 (by rfl) ⟨1084436, by rfl⟩ : syracuseStep 1445915 = 2168873) B2168873
theorem B3256415 : Blo 1445542 3256415 := bstep (se 1 (by rfl) ⟨2442311, by rfl⟩ : syracuseStep 3256415 = 4884623) B4884623
theorem B8237153 : Blo 1445542 8237153 := bstep (se 2 (by rfl) ⟨3088932, by rfl⟩ : syracuseStep 8237153 = 6177865) B6177865
theorem B3256487 : Blo 1445542 3256487 := bstep (se 1 (by rfl) ⟨2442365, by rfl⟩ : syracuseStep 3256487 = 4884731) B4884731
theorem B1446527 : Blo 1445542 1446527 := bstep (se 1 (by rfl) ⟨1084895, by rfl⟩ : syracuseStep 1446527 = 2169791) B2169791
theorem B107000675 : Blo 1445542 107000675 := bstep (se 1 (by rfl) ⟨80250506, by rfl⟩ : syracuseStep 107000675 = 160501013) B160501013
theorem B1446759 : Blo 1445542 1446759 := bstep (se 1 (by rfl) ⟨1085069, by rfl⟩ : syracuseStep 1446759 = 2170139) B2170139
theorem B6181865 : Blo 1445542 6181865 := bstep (se 2 (by rfl) ⟨2318199, by rfl⟩ : syracuseStep 6181865 = 4636399) B4636399
theorem B1447015 : Blo 1445542 1447015 := bstep (se 1 (by rfl) ⟨1085261, by rfl⟩ : syracuseStep 1447015 = 2170523) B2170523
theorem B1447039 : Blo 1445542 1447039 := bstep (se 1 (by rfl) ⟨1085279, by rfl⟩ : syracuseStep 1447039 = 2170559) B2170559
theorem B3298729 : Blo 1445542 3298729 := bstep (se 2 (by rfl) ⟨1237023, by rfl⟩ : syracuseStep 3298729 = 2474047) B2474047
theorem B7321103 : Blo 1445542 7321103 := bstep (se 1 (by rfl) ⟨5490827, by rfl⟩ : syracuseStep 7321103 = 10981655) B10981655
theorem B1447451 : Blo 1445542 1447451 := bstep (se 1 (by rfl) ⟨1085588, by rfl⟩ : syracuseStep 1447451 = 2171177) B2171177
theorem B4634219 : Blo 1445542 4634219 := bstep (se 1 (by rfl) ⟨3475664, by rfl⟩ : syracuseStep 4634219 = 6951329) B6951329
theorem B6600361 : Blo 1445542 6600361 := bstep (se 2 (by rfl) ⟨2475135, by rfl⟩ : syracuseStep 6600361 = 4950271) B4950271
theorem B1628095 : Blo 1445542 1628095 := bstep (se 1 (by rfl) ⟨1221071, by rfl⟩ : syracuseStep 1628095 = 2442143) B2442143
theorem B8345567 : Blo 1445542 8345567 := bstep (se 1 (by rfl) ⟨6259175, by rfl⟩ : syracuseStep 8345567 = 12518351) B12518351
theorem B106952729 : Blo 1445542 106952729 := bstep (se 2 (by rfl) ⟨40107273, by rfl⟩ : syracuseStep 106952729 = 80214547) B80214547
theorem B4945961 : Blo 1445542 4945961 := bstep (se 2 (by rfl) ⟨1854735, by rfl⟩ : syracuseStep 4945961 = 3709471) B3709471
theorem B2439355 : Blo 1445542 2439355 := bstep (se 1 (by rfl) ⟨1829516, by rfl⟩ : syracuseStep 2439355 = 3659033) B3659033
theorem B3660025 : Blo 1445542 3660025 := bstep (se 2 (by rfl) ⟨1372509, by rfl⟩ : syracuseStep 3660025 = 2745019) B2745019
theorem B3660187 : Blo 1445542 3660187 := bstep (se 1 (by rfl) ⟨2745140, by rfl⟩ : syracuseStep 3660187 = 5490281) B5490281
theorem B2169323 : Blo 1445542 2169323 := bstep (se 1 (by rfl) ⟨1626992, by rfl⟩ : syracuseStep 2169323 = 3253985) B3253985
theorem B3660329 : Blo 1445542 3660329 := bstep (se 2 (by rfl) ⟨1372623, by rfl⟩ : syracuseStep 3660329 = 2745247) B2745247
theorem B4880951 : Blo 1445542 4880951 := bstep (se 1 (by rfl) ⟨3660713, by rfl⟩ : syracuseStep 4880951 = 7321427) B7321427
theorem B4119169 : Blo 1445542 4119169 := bstep (se 2 (by rfl) ⟨1544688, by rfl⟩ : syracuseStep 4119169 = 3089377) B3089377
theorem B2440057 : Blo 1445542 2440057 := bstep (se 2 (by rfl) ⟨915021, by rfl⟩ : syracuseStep 2440057 = 1830043) B1830043
theorem B3660673 : Blo 1445542 3660673 := bstep (se 2 (by rfl) ⟨1372752, by rfl⟩ : syracuseStep 3660673 = 2745505) B2745505
theorem B2169737 : Blo 1445542 2169737 := bstep (se 2 (by rfl) ⟨813651, by rfl⟩ : syracuseStep 2169737 = 1627303) B1627303
theorem B7322561 : Blo 1445542 7322561 := bstep (se 2 (by rfl) ⟨2745960, by rfl⟩ : syracuseStep 7322561 = 5491921) B5491921
theorem B16481231 : Blo 1445542 16481231 := bstep (se 1 (by rfl) ⟨12360923, by rfl⟩ : syracuseStep 16481231 = 24721847) B24721847
theorem B4119511 : Blo 1445542 4119511 := bstep (se 1 (by rfl) ⟨3089633, by rfl⟩ : syracuseStep 4119511 = 6179267) B6179267
theorem B2170271 : Blo 1445542 2170271 := bstep (se 1 (by rfl) ⟨1627703, by rfl⟩ : syracuseStep 2170271 = 3255407) B3255407
theorem B3087839 : Blo 1445542 3087839 := bstep (se 1 (by rfl) ⟨2315879, by rfl⟩ : syracuseStep 3087839 = 4631759) B4631759
theorem B8240777 : Blo 1445542 8240777 := bstep (se 2 (by rfl) ⟨3090291, by rfl⟩ : syracuseStep 8240777 = 6180583) B6180583
theorem B2170619 : Blo 1445542 2170619 := bstep (se 1 (by rfl) ⟨1627964, by rfl⟩ : syracuseStep 2170619 = 3255929) B3255929
theorem B4120399 : Blo 1445542 4120399 := bstep (se 1 (by rfl) ⟨3090299, by rfl⟩ : syracuseStep 4120399 = 6180599) B6180599
theorem B7323695 : Blo 1445542 7323695 := bstep (se 1 (by rfl) ⟨5492771, by rfl⟩ : syracuseStep 7323695 = 10985543) B10985543
theorem B2441279 : Blo 1445542 2441279 := bstep (se 1 (by rfl) ⟨1830959, by rfl⟩ : syracuseStep 2441279 = 3661919) B3661919
theorem B2170943 : Blo 1445542 2170943 := bstep (se 1 (by rfl) ⟨1628207, by rfl⟩ : syracuseStep 2170943 = 3256415) B3256415
theorem B13189229 : Blo 1445542 13189229 := bstep (se 3 (by rfl) ⟨2472980, by rfl⟩ : syracuseStep 13189229 = 4945961) B4945961
theorem B2170991 : Blo 1445542 2170991 := bstep (se 1 (by rfl) ⟨1628243, by rfl⟩ : syracuseStep 2170991 = 3256487) B3256487
theorem B3252473 : Blo 1445542 3252473 := bstep (se 2 (by rfl) ⟨1219677, by rfl⟩ : syracuseStep 3252473 = 2439355) B2439355
theorem B2744617 : Blo 1445542 2744617 := bstep (se 2 (by rfl) ⟨1029231, by rfl⟩ : syracuseStep 2744617 = 2058463) B2058463
theorem B10977767 : Blo 1445542 10977767 := bstep (se 1 (by rfl) ⟨8233325, by rfl⟩ : syracuseStep 10977767 = 16466651) B16466651
theorem B4121243 : Blo 1445542 4121243 := bstep (se 1 (by rfl) ⟨3090932, by rfl⟩ : syracuseStep 4121243 = 6181865) B6181865
theorem B41731037 : Blo 1445542 41731037 := bstep (se 3 (by rfl) ⟨7824569, by rfl⟩ : syracuseStep 41731037 = 15649139) B15649139
theorem B3253409 : Blo 1445542 3253409 := bstep (se 2 (by rfl) ⟨1220028, by rfl⟩ : syracuseStep 3253409 = 2440057) B2440057
theorem B8234237 : Blo 1445542 8234237 := bstep (se 3 (by rfl) ⟨1543919, by rfl⟩ : syracuseStep 8234237 = 3087839) B3087839
theorem B5563711 : Blo 1445542 5563711 := bstep (se 1 (by rfl) ⟨4172783, by rfl⟩ : syracuseStep 5563711 = 8345567) B8345567
theorem B152274455 : Blo 1445542 152274455 := bstep (se 1 (by rfl) ⟨114205841, by rfl⟩ : syracuseStep 152274455 = 228411683) B228411683
theorem B7816787 : Blo 1445542 7816787 := bstep (se 1 (by rfl) ⟨5862590, by rfl⟩ : syracuseStep 7816787 = 11725181) B11725181
theorem B3253967 : Blo 1445542 3253967 := bstep (se 1 (by rfl) ⟨2440475, by rfl⟩ : syracuseStep 3253967 = 4880951) B4880951
theorem B10987487 : Blo 1445542 10987487 := bstep (se 1 (by rfl) ⟨8240615, by rfl⟩ : syracuseStep 10987487 = 16481231) B16481231
theorem B8800481 : Blo 1445542 8800481 := bstep (se 2 (by rfl) ⟨3300180, by rfl⟩ : syracuseStep 8800481 = 6600361) B6600361
theorem B5491435 : Blo 1445542 5491435 := bstep (se 1 (by rfl) ⟨4118576, by rfl⟩ : syracuseStep 5491435 = 8237153) B8237153
theorem B3255137 : Blo 1445542 3255137 := bstep (se 2 (by rfl) ⟨1220676, by rfl⟩ : syracuseStep 3255137 = 2441353) B2441353
theorem B1140829109 : Blo 1445542 1140829109 := bstep (se 5 (by rfl) ⟨53476364, by rfl⟩ : syracuseStep 1140829109 = 106952729) B106952729
theorem B1830271 : Blo 1445542 1830271 := bstep (se 1 (by rfl) ⟨1372703, by rfl⟩ : syracuseStep 1830271 = 2745407) B2745407
theorem B5492225 : Blo 1445542 5492225 := bstep (se 2 (by rfl) ⟨2059584, by rfl⟩ : syracuseStep 5492225 = 4119169) B4119169
theorem B18534005 : Blo 1445542 18534005 := bstep (se 5 (by rfl) ⟨868781, by rfl⟩ : syracuseStep 18534005 = 1737563) B1737563
theorem B3256073 : Blo 1445542 3256073 := bstep (se 2 (by rfl) ⟨1221027, by rfl⟩ : syracuseStep 3256073 = 2442055) B2442055
theorem B5492681 : Blo 1445542 5492681 := bstep (se 2 (by rfl) ⟨2059755, by rfl⟩ : syracuseStep 5492681 = 4119511) B4119511
theorem B12357917 : Blo 1445542 12357917 := bstep (se 3 (by rfl) ⟨2317109, by rfl⟩ : syracuseStep 12357917 = 4634219) B4634219
theorem B75149603 : Blo 1445542 75149603 := bstep (se 1 (by rfl) ⟨56362202, by rfl⟩ : syracuseStep 75149603 = 112724405) B112724405
theorem B1446215 : Blo 1445542 1446215 := bstep (se 1 (by rfl) ⟨1084661, by rfl⟩ : syracuseStep 1446215 = 2169323) B2169323
theorem B4878791 : Blo 1445542 4878791 := bstep (se 1 (by rfl) ⟨3659093, by rfl⟩ : syracuseStep 4878791 = 7318187) B7318187
theorem B4878845 : Blo 1445542 4878845 := bstep (se 3 (by rfl) ⟨914783, by rfl⟩ : syracuseStep 4878845 = 1829567) B1829567
theorem B1446491 : Blo 1445542 1446491 := bstep (se 1 (by rfl) ⟨1084868, by rfl⟩ : syracuseStep 1446491 = 2169737) B2169737
theorem B27816695 : Blo 1445542 27816695 := bstep (se 1 (by rfl) ⟨20862521, by rfl⟩ : syracuseStep 27816695 = 41725043) B41725043
theorem B4879115 : Blo 1445542 4879115 := bstep (se 1 (by rfl) ⟨3659336, by rfl⟩ : syracuseStep 4879115 = 7318673) B7318673
theorem B1446847 : Blo 1445542 1446847 := bstep (se 1 (by rfl) ⟨1085135, by rfl⟩ : syracuseStep 1446847 = 2170271) B2170271
theorem B5493851 : Blo 1445542 5493851 := bstep (se 1 (by rfl) ⟨4120388, by rfl⟩ : syracuseStep 5493851 = 8240777) B8240777
theorem B5493865 : Blo 1445542 5493865 := bstep (se 2 (by rfl) ⟨2060199, by rfl⟩ : syracuseStep 5493865 = 4120399) B4120399
theorem B1447079 : Blo 1445542 1447079 := bstep (se 1 (by rfl) ⟨1085309, by rfl⟩ : syracuseStep 1447079 = 2170619) B2170619
theorem B4175497 : Blo 1445542 4175497 := bstep (se 2 (by rfl) ⟨1565811, by rfl⟩ : syracuseStep 4175497 = 3131623) B3131623
theorem B4880033 : Blo 1445542 4880033 := bstep (se 2 (by rfl) ⟨1830012, by rfl⟩ : syracuseStep 4880033 = 3660025) B3660025
theorem B7427807 : Blo 1445542 7427807 := bstep (se 1 (by rfl) ⟨5570855, by rfl⟩ : syracuseStep 7427807 = 11141711) B11141711
theorem B4880249 : Blo 1445542 4880249 := bstep (se 2 (by rfl) ⟨1830093, by rfl⟩ : syracuseStep 4880249 = 3660187) B3660187
theorem B24713099 : Blo 1445542 24713099 := bstep (se 1 (by rfl) ⟨18534824, by rfl⟩ : syracuseStep 24713099 = 37069649) B37069649
theorem B71333783 : Blo 1445542 71333783 := bstep (se 1 (by rfl) ⟨53500337, by rfl⟩ : syracuseStep 71333783 = 107000675) B107000675
theorem B2168831 : Blo 1445542 2168831 := bstep (se 1 (by rfl) ⟨1626623, by rfl⟩ : syracuseStep 2168831 = 3253247) B3253247
theorem B2169071 : Blo 1445542 2169071 := bstep (se 1 (by rfl) ⟨1626803, by rfl⟩ : syracuseStep 2169071 = 3253607) B3253607
theorem B2169143 : Blo 1445542 2169143 := bstep (se 1 (by rfl) ⟨1626857, by rfl⟩ : syracuseStep 2169143 = 3253715) B3253715
theorem B4880735 : Blo 1445542 4880735 := bstep (se 1 (by rfl) ⟨3660551, by rfl⟩ : syracuseStep 4880735 = 7321103) B7321103
theorem B4880897 : Blo 1445542 4880897 := bstep (se 2 (by rfl) ⟨1830336, by rfl⟩ : syracuseStep 4880897 = 3660673) B3660673
theorem B3300335 : Blo 1445542 3300335 := bstep (se 1 (by rfl) ⟨2475251, by rfl⟩ : syracuseStep 3300335 = 4950503) B4950503
theorem B2440219 : Blo 1445542 2440219 := bstep (se 1 (by rfl) ⟨1830164, by rfl⟩ : syracuseStep 2440219 = 3660329) B3660329
theorem B2169959 : Blo 1445542 2169959 := bstep (se 1 (by rfl) ⟨1627469, by rfl⟩ : syracuseStep 2169959 = 3254939) B3254939
theorem B4398305 : Blo 1445542 4398305 := bstep (se 2 (by rfl) ⟨1649364, by rfl⟩ : syracuseStep 4398305 = 3298729) B3298729
theorem B4881707 : Blo 1445542 4881707 := bstep (se 1 (by rfl) ⟨3661280, by rfl⟩ : syracuseStep 4881707 = 7322561) B7322561
theorem B15056209 : Blo 1445542 15056209 := bstep (se 2 (by rfl) ⟨5646078, by rfl⟩ : syracuseStep 15056209 = 11292157) B11292157
theorem B2170439 : Blo 1445542 2170439 := bstep (se 1 (by rfl) ⟨1627829, by rfl⟩ : syracuseStep 2170439 = 3255659) B3255659
theorem B80314021 : Blo 1445542 80314021 := bstep (se 4 (by rfl) ⟨7529439, by rfl⟩ : syracuseStep 80314021 = 15058879) B15058879
theorem B2170793 : Blo 1445542 2170793 := bstep (se 2 (by rfl) ⟨814047, by rfl⟩ : syracuseStep 2170793 = 1628095) B1628095
theorem B4882463 : Blo 1445542 4882463 := bstep (se 1 (by rfl) ⟨3661847, by rfl⟩ : syracuseStep 4882463 = 7323695) B7323695
theorem B3252527 : Blo 1445542 3252527 := bstep (se 1 (by rfl) ⟨2439395, by rfl⟩ : syracuseStep 3252527 = 4878791) B4878791
theorem B3252563 : Blo 1445542 3252563 := bstep (se 1 (by rfl) ⟨2439422, by rfl⟩ : syracuseStep 3252563 = 4878845) B4878845
theorem B3252743 : Blo 1445542 3252743 := bstep (se 1 (by rfl) ⟨2439557, by rfl⟩ : syracuseStep 3252743 = 4879115) B4879115
theorem B27820691 : Blo 1445542 27820691 := bstep (se 1 (by rfl) ⟨20865518, by rfl⟩ : syracuseStep 27820691 = 41731037) B41731037
theorem B3662567 : Blo 1445542 3662567 := bstep (se 1 (by rfl) ⟨2746925, by rfl⟩ : syracuseStep 3662567 = 5493851) B5493851
theorem B5489491 : Blo 1445542 5489491 := bstep (se 1 (by rfl) ⟨4117118, by rfl⟩ : syracuseStep 5489491 = 8234237) B8234237
theorem B101516303 : Blo 1445542 101516303 := bstep (se 1 (by rfl) ⟨76137227, by rfl⟩ : syracuseStep 101516303 = 152274455) B152274455
theorem B5211191 : Blo 1445542 5211191 := bstep (se 1 (by rfl) ⟨3908393, by rfl⟩ : syracuseStep 5211191 = 7816787) B7816787
theorem B3253355 : Blo 1445542 3253355 := bstep (se 1 (by rfl) ⟨2440016, by rfl⟩ : syracuseStep 3253355 = 4880033) B4880033
theorem B3253499 : Blo 1445542 3253499 := bstep (se 1 (by rfl) ⟨2440124, by rfl⟩ : syracuseStep 3253499 = 4880249) B4880249
theorem B16475399 : Blo 1445542 16475399 := bstep (se 1 (by rfl) ⟨12356549, by rfl⟩ : syracuseStep 16475399 = 24713099) B24713099
theorem B47555855 : Blo 1445542 47555855 := bstep (se 1 (by rfl) ⟨35666891, by rfl⟩ : syracuseStep 47555855 = 71333783) B71333783
theorem B7324991 : Blo 1445542 7324991 := bstep (se 1 (by rfl) ⟨5493743, by rfl⟩ : syracuseStep 7324991 = 10987487) B10987487
theorem B3253625 : Blo 1445542 3253625 := bstep (se 2 (by rfl) ⟨1220109, by rfl⟩ : syracuseStep 3253625 = 2440219) B2440219
theorem B7325153 : Blo 1445542 7325153 := bstep (se 2 (by rfl) ⟨2746932, by rfl⟩ : syracuseStep 7325153 = 5493865) B5493865
theorem B5866987 : Blo 1445542 5866987 := bstep (se 1 (by rfl) ⟨4400240, by rfl⟩ : syracuseStep 5866987 = 8800481) B8800481
theorem B3253823 : Blo 1445542 3253823 := bstep (se 1 (by rfl) ⟨2440367, by rfl⟩ : syracuseStep 3253823 = 4880735) B4880735
theorem B29673125 : Blo 1445542 29673125 := bstep (se 4 (by rfl) ⟨2781855, by rfl⟩ : syracuseStep 29673125 = 5563711) B5563711
theorem B3253931 : Blo 1445542 3253931 := bstep (se 1 (by rfl) ⟨2440448, by rfl⟩ : syracuseStep 3253931 = 4880897) B4880897
theorem B80299781 : Blo 1445542 80299781 := bstep (se 4 (by rfl) ⟨7528104, by rfl⟩ : syracuseStep 80299781 = 15056209) B15056209
theorem B3254471 : Blo 1445542 3254471 := bstep (se 1 (by rfl) ⟨2440853, by rfl⟩ : syracuseStep 3254471 = 4881707) B4881707
theorem B12356003 : Blo 1445542 12356003 := bstep (se 1 (by rfl) ⟨9267002, by rfl⟩ : syracuseStep 12356003 = 18534005) B18534005
theorem B8792819 : Blo 1445542 8792819 := bstep (se 1 (by rfl) ⟨6594614, by rfl⟩ : syracuseStep 8792819 = 13189229) B13189229
theorem B7318511 : Blo 1445542 7318511 := bstep (se 1 (by rfl) ⟨5488883, by rfl⟩ : syracuseStep 7318511 = 10977767) B10977767
theorem B2747495 : Blo 1445542 2747495 := bstep (se 1 (by rfl) ⟨2060621, by rfl⟩ : syracuseStep 2747495 = 4121243) B4121243
theorem B4951871 : Blo 1445542 4951871 := bstep (se 1 (by rfl) ⟨3713903, by rfl⟩ : syracuseStep 4951871 = 7427807) B7427807
theorem B1445887 : Blo 1445542 1445887 := bstep (se 1 (by rfl) ⟨1084415, by rfl⟩ : syracuseStep 1445887 = 2168831) B2168831
theorem B1446047 : Blo 1445542 1446047 := bstep (se 1 (by rfl) ⟨1084535, by rfl⟩ : syracuseStep 1446047 = 2169071) B2169071
theorem B1446095 : Blo 1445542 1446095 := bstep (se 1 (by rfl) ⟨1084571, by rfl⟩ : syracuseStep 1446095 = 2169143) B2169143
theorem B2200223 : Blo 1445542 2200223 := bstep (se 1 (by rfl) ⟨1650167, by rfl⟩ : syracuseStep 2200223 = 3300335) B3300335
theorem B1446639 : Blo 1445542 1446639 := bstep (se 1 (by rfl) ⟨1084979, by rfl⟩ : syracuseStep 1446639 = 2169959) B2169959
theorem B5567329 : Blo 1445542 5567329 := bstep (se 2 (by rfl) ⟨2087748, by rfl⟩ : syracuseStep 5567329 = 4175497) B4175497
theorem B1446959 : Blo 1445542 1446959 := bstep (se 1 (by rfl) ⟨1085219, by rfl⟩ : syracuseStep 1446959 = 2170439) B2170439
theorem B1447195 : Blo 1445542 1447195 := bstep (se 1 (by rfl) ⟨1085396, by rfl⟩ : syracuseStep 1447195 = 2170793) B2170793
theorem B1627519 : Blo 1445542 1627519 := bstep (se 1 (by rfl) ⟨1220639, by rfl⟩ : syracuseStep 1627519 = 2441279) B2441279
theorem B1447295 : Blo 1445542 1447295 := bstep (se 1 (by rfl) ⟨1085471, by rfl⟩ : syracuseStep 1447295 = 2170943) B2170943
theorem B1447327 : Blo 1445542 1447327 := bstep (se 1 (by rfl) ⟨1085495, by rfl⟩ : syracuseStep 1447327 = 2170991) B2170991
theorem B2168315 : Blo 1445542 2168315 := bstep (se 1 (by rfl) ⟨1626236, by rfl⟩ : syracuseStep 2168315 = 3252473) B3252473
theorem B8238611 : Blo 1445542 8238611 := bstep (se 1 (by rfl) ⟨6178958, by rfl⟩ : syracuseStep 8238611 = 12357917) B12357917
theorem B50099735 : Blo 1445542 50099735 := bstep (se 1 (by rfl) ⟨37574801, by rfl⟩ : syracuseStep 50099735 = 75149603) B75149603
theorem B3659489 : Blo 1445542 3659489 := bstep (se 2 (by rfl) ⟨1372308, by rfl⟩ : syracuseStep 3659489 = 2744617) B2744617
theorem B18544463 : Blo 1445542 18544463 := bstep (se 1 (by rfl) ⟨13908347, by rfl⟩ : syracuseStep 18544463 = 27816695) B27816695
theorem B11728813 : Blo 1445542 11728813 := bstep (se 3 (by rfl) ⟨2199152, by rfl⟩ : syracuseStep 11728813 = 4398305) B4398305
theorem B2168939 : Blo 1445542 2168939 := bstep (se 1 (by rfl) ⟨1626704, by rfl⟩ : syracuseStep 2168939 = 3253409) B3253409
theorem B428341445 : Blo 1445542 428341445 := bstep (se 4 (by rfl) ⟨40157010, by rfl⟩ : syracuseStep 428341445 = 80314021) B80314021
theorem B7321913 : Blo 1445542 7321913 := bstep (se 2 (by rfl) ⟨2745717, by rfl⟩ : syracuseStep 7321913 = 5491435) B5491435
theorem B2169311 : Blo 1445542 2169311 := bstep (se 1 (by rfl) ⟨1626983, by rfl⟩ : syracuseStep 2169311 = 3253967) B3253967
theorem B2440361 : Blo 1445542 2440361 := bstep (se 2 (by rfl) ⟨915135, by rfl⟩ : syracuseStep 2440361 = 1830271) B1830271
theorem B2170091 : Blo 1445542 2170091 := bstep (se 1 (by rfl) ⟨1627568, by rfl⟩ : syracuseStep 2170091 = 3255137) B3255137
theorem B760552739 : Blo 1445542 760552739 := bstep (se 1 (by rfl) ⟨570414554, by rfl⟩ : syracuseStep 760552739 = 1140829109) B1140829109
theorem B3661483 : Blo 1445542 3661483 := bstep (se 1 (by rfl) ⟨2746112, by rfl⟩ : syracuseStep 3661483 = 5492225) B5492225
theorem B2170715 : Blo 1445542 2170715 := bstep (se 1 (by rfl) ⟨1628036, by rfl⟩ : syracuseStep 2170715 = 3256073) B3256073
theorem B3661787 : Blo 1445542 3661787 := bstep (se 1 (by rfl) ⟨2746340, by rfl⟩ : syracuseStep 3661787 = 5492681) B5492681
theorem B18547127 : Blo 1445542 18547127 := bstep (se 1 (by rfl) ⟨13910345, by rfl⟩ : syracuseStep 18547127 = 27820691) B27820691
theorem B2441711 : Blo 1445542 2441711 := bstep (se 1 (by rfl) ⟨1831283, by rfl⟩ : syracuseStep 2441711 = 3662567) B3662567
theorem B3474127 : Blo 1445542 3474127 := bstep (se 1 (by rfl) ⟨2605595, by rfl⟩ : syracuseStep 3474127 = 5211191) B5211191
theorem B31703903 : Blo 1445542 31703903 := bstep (se 1 (by rfl) ⟨23777927, by rfl⟩ : syracuseStep 31703903 = 47555855) B47555855
theorem B4883327 : Blo 1445542 4883327 := bstep (se 1 (by rfl) ⟨3662495, by rfl⟩ : syracuseStep 4883327 = 7324991) B7324991
theorem B4883435 : Blo 1445542 4883435 := bstep (se 1 (by rfl) ⟨3662576, by rfl⟩ : syracuseStep 4883435 = 7325153) B7325153
theorem B33399823 : Blo 1445542 33399823 := bstep (se 1 (by rfl) ⟨25049867, by rfl⟩ : syracuseStep 33399823 = 50099735) B50099735
theorem B12362975 : Blo 1445542 12362975 := bstep (se 1 (by rfl) ⟨9272231, by rfl⟩ : syracuseStep 12362975 = 18544463) B18544463
theorem B5867261 : Blo 1445542 5867261 := bstep (se 3 (by rfl) ⟨1100111, by rfl⟩ : syracuseStep 5867261 = 2200223) B2200223
theorem B3254975 : Blo 1445542 3254975 := bstep (se 1 (by rfl) ⟨2441231, by rfl⟩ : syracuseStep 3254975 = 4882463) B4882463
theorem B67677535 : Blo 1445542 67677535 := bstep (se 1 (by rfl) ⟨50758151, by rfl⟩ : syracuseStep 67677535 = 101516303) B101516303
theorem B1445543 : Blo 1445542 1445543 := bstep (se 1 (by rfl) ⟨1084157, by rfl⟩ : syracuseStep 1445543 = 2168315) B2168315
theorem B5492407 : Blo 1445542 5492407 := bstep (se 1 (by rfl) ⟨4119305, by rfl⟩ : syracuseStep 5492407 = 8238611) B8238611
theorem B7319321 : Blo 1445542 7319321 := bstep (se 2 (by rfl) ⟨2744745, by rfl⟩ : syracuseStep 7319321 = 5489491) B5489491
theorem B1445959 : Blo 1445542 1445959 := bstep (se 1 (by rfl) ⟨1084469, by rfl⟩ : syracuseStep 1445959 = 2168939) B2168939
theorem B285560963 : Blo 1445542 285560963 := bstep (se 1 (by rfl) ⟨214170722, by rfl⟩ : syracuseStep 285560963 = 428341445) B428341445
theorem B8237335 : Blo 1445542 8237335 := bstep (se 1 (by rfl) ⟨6178001, by rfl⟩ : syracuseStep 8237335 = 12356003) B12356003
theorem B1446207 : Blo 1445542 1446207 := bstep (se 1 (by rfl) ⟨1084655, by rfl⟩ : syracuseStep 1446207 = 2169311) B2169311
theorem B5861879 : Blo 1445542 5861879 := bstep (se 1 (by rfl) ⟨4396409, by rfl⟩ : syracuseStep 5861879 = 8792819) B8792819
theorem B29692421 : Blo 1445542 29692421 := bstep (se 4 (by rfl) ⟨2783664, by rfl⟩ : syracuseStep 29692421 = 5567329) B5567329
theorem B4879007 : Blo 1445542 4879007 := bstep (se 1 (by rfl) ⟨3659255, by rfl⟩ : syracuseStep 4879007 = 7318511) B7318511
theorem B1831663 : Blo 1445542 1831663 := bstep (se 1 (by rfl) ⟨1373747, by rfl⟩ : syracuseStep 1831663 = 2747495) B2747495
theorem B1626907 : Blo 1445542 1626907 := bstep (se 1 (by rfl) ⟨1220180, by rfl⟩ : syracuseStep 1626907 = 2440361) B2440361
theorem B1446727 : Blo 1445542 1446727 := bstep (se 1 (by rfl) ⟨1085045, by rfl⟩ : syracuseStep 1446727 = 2170091) B2170091
theorem B1447143 : Blo 1445542 1447143 := bstep (se 1 (by rfl) ⟨1085357, by rfl⟩ : syracuseStep 1447143 = 2170715) B2170715
theorem B2168351 : Blo 1445542 2168351 := bstep (se 1 (by rfl) ⟨1626263, by rfl⟩ : syracuseStep 2168351 = 3252527) B3252527
theorem B2168375 : Blo 1445542 2168375 := bstep (se 1 (by rfl) ⟨1626281, by rfl⟩ : syracuseStep 2168375 = 3252563) B3252563
theorem B2168495 : Blo 1445542 2168495 := bstep (se 1 (by rfl) ⟨1626371, by rfl⟩ : syracuseStep 2168495 = 3252743) B3252743
theorem B2168903 : Blo 1445542 2168903 := bstep (se 1 (by rfl) ⟨1626677, by rfl⟩ : syracuseStep 2168903 = 3253355) B3253355
theorem B2168999 : Blo 1445542 2168999 := bstep (se 1 (by rfl) ⟨1626749, by rfl⟩ : syracuseStep 2168999 = 3253499) B3253499
theorem B10983599 : Blo 1445542 10983599 := bstep (se 1 (by rfl) ⟨8237699, by rfl⟩ : syracuseStep 10983599 = 16475399) B16475399
theorem B2169083 : Blo 1445542 2169083 := bstep (se 1 (by rfl) ⟨1626812, by rfl⟩ : syracuseStep 2169083 = 3253625) B3253625
theorem B2169215 : Blo 1445542 2169215 := bstep (se 1 (by rfl) ⟨1626911, by rfl⟩ : syracuseStep 2169215 = 3253823) B3253823
theorem B19782083 : Blo 1445542 19782083 := bstep (se 1 (by rfl) ⟨14836562, by rfl⟩ : syracuseStep 19782083 = 29673125) B29673125
theorem B2169287 : Blo 1445542 2169287 := bstep (se 1 (by rfl) ⟨1626965, by rfl⟩ : syracuseStep 2169287 = 3253931) B3253931
theorem B2439659 : Blo 1445542 2439659 := bstep (se 1 (by rfl) ⟨1829744, by rfl⟩ : syracuseStep 2439659 = 3659489) B3659489
theorem B53533187 : Blo 1445542 53533187 := bstep (se 1 (by rfl) ⟨40149890, by rfl⟩ : syracuseStep 53533187 = 80299781) B80299781
theorem B2169647 : Blo 1445542 2169647 := bstep (se 1 (by rfl) ⟨1627235, by rfl⟩ : syracuseStep 2169647 = 3254471) B3254471
theorem B4881275 : Blo 1445542 4881275 := bstep (se 1 (by rfl) ⟨3660956, by rfl⟩ : syracuseStep 4881275 = 7321913) B7321913
theorem B2170025 : Blo 1445542 2170025 := bstep (se 2 (by rfl) ⟨813759, by rfl⟩ : syracuseStep 2170025 = 1627519) B1627519
theorem B7822649 : Blo 1445542 7822649 := bstep (se 2 (by rfl) ⟨2933493, by rfl⟩ : syracuseStep 7822649 = 5866987) B5866987
theorem B507035159 : Blo 1445542 507035159 := bstep (se 1 (by rfl) ⟨380276369, by rfl⟩ : syracuseStep 507035159 = 760552739) B760552739
theorem B4881977 : Blo 1445542 4881977 := bstep (se 2 (by rfl) ⟨1830741, by rfl⟩ : syracuseStep 4881977 = 3661483) B3661483
theorem B3301247 : Blo 1445542 3301247 := bstep (se 1 (by rfl) ⟨2475935, by rfl⟩ : syracuseStep 3301247 = 4951871) B4951871
theorem B15638417 : Blo 1445542 15638417 := bstep (se 2 (by rfl) ⟨5864406, by rfl⟩ : syracuseStep 15638417 = 11728813) B11728813
theorem B2441191 : Blo 1445542 2441191 := bstep (se 1 (by rfl) ⟨1830893, by rfl⟩ : syracuseStep 2441191 = 3661787) B3661787
theorem B190373975 : Blo 1445542 190373975 := bstep (se 1 (by rfl) ⟨142780481, by rfl⟩ : syracuseStep 190373975 = 285560963) B285560963
theorem B3907919 : Blo 1445542 3907919 := bstep (se 1 (by rfl) ⟨2930939, by rfl⟩ : syracuseStep 3907919 = 5861879) B5861879
theorem B3252671 : Blo 1445542 3252671 := bstep (se 1 (by rfl) ⟨2439503, by rfl⟩ : syracuseStep 3252671 = 4879007) B4879007
theorem B21135935 : Blo 1445542 21135935 := bstep (se 1 (by rfl) ⟨15851951, by rfl⟩ : syracuseStep 21135935 = 31703903) B31703903
theorem B8241983 : Blo 1445542 8241983 := bstep (se 1 (by rfl) ⟨6181487, by rfl⟩ : syracuseStep 8241983 = 12362975) B12362975
theorem B2442217 : Blo 1445542 2442217 := bstep (se 2 (by rfl) ⟨915831, by rfl⟩ : syracuseStep 2442217 = 1831663) B1831663
theorem B44533097 : Blo 1445542 44533097 := bstep (se 2 (by rfl) ⟨16699911, by rfl⟩ : syracuseStep 44533097 = 33399823) B33399823
theorem B90236713 : Blo 1445542 90236713 := bstep (se 2 (by rfl) ⟨33838767, by rfl⟩ : syracuseStep 90236713 = 67677535) B67677535
theorem B3254183 : Blo 1445542 3254183 := bstep (se 1 (by rfl) ⟨2440637, by rfl⟩ : syracuseStep 3254183 = 4881275) B4881275
theorem B3254651 : Blo 1445542 3254651 := bstep (se 1 (by rfl) ⟨2440988, by rfl⟩ : syracuseStep 3254651 = 4881977) B4881977
theorem B3254921 : Blo 1445542 3254921 := bstep (se 2 (by rfl) ⟨1220595, by rfl⟩ : syracuseStep 3254921 = 2441191) B2441191
theorem B12364751 : Blo 1445542 12364751 := bstep (se 1 (by rfl) ⟨9273563, by rfl⟩ : syracuseStep 12364751 = 18547127) B18547127
theorem B19794947 : Blo 1445542 19794947 := bstep (se 1 (by rfl) ⟨14846210, by rfl⟩ : syracuseStep 19794947 = 29692421) B29692421
theorem B3255551 : Blo 1445542 3255551 := bstep (se 1 (by rfl) ⟨2441663, by rfl⟩ : syracuseStep 3255551 = 4883327) B4883327
theorem B3255623 : Blo 1445542 3255623 := bstep (se 1 (by rfl) ⟨2441717, by rfl⟩ : syracuseStep 3255623 = 4883435) B4883435
theorem B4632169 : Blo 1445542 4632169 := bstep (se 2 (by rfl) ⟨1737063, by rfl⟩ : syracuseStep 4632169 = 3474127) B3474127
theorem B1445567 : Blo 1445542 1445567 := bstep (se 1 (by rfl) ⟨1084175, by rfl⟩ : syracuseStep 1445567 = 2168351) B2168351
theorem B1445583 : Blo 1445542 1445583 := bstep (se 1 (by rfl) ⟨1084187, by rfl⟩ : syracuseStep 1445583 = 2168375) B2168375
theorem B1445663 : Blo 1445542 1445663 := bstep (se 1 (by rfl) ⟨1084247, by rfl⟩ : syracuseStep 1445663 = 2168495) B2168495
theorem B3911507 : Blo 1445542 3911507 := bstep (se 1 (by rfl) ⟨2933630, by rfl⟩ : syracuseStep 3911507 = 5867261) B5867261
theorem B1445935 : Blo 1445542 1445935 := bstep (se 1 (by rfl) ⟨1084451, by rfl⟩ : syracuseStep 1445935 = 2168903) B2168903
theorem B1445999 : Blo 1445542 1445999 := bstep (se 1 (by rfl) ⟨1084499, by rfl⟩ : syracuseStep 1445999 = 2168999) B2168999
theorem B1446055 : Blo 1445542 1446055 := bstep (se 1 (by rfl) ⟨1084541, by rfl⟩ : syracuseStep 1446055 = 2169083) B2169083
theorem B1446143 : Blo 1445542 1446143 := bstep (se 1 (by rfl) ⟨1084607, by rfl⟩ : syracuseStep 1446143 = 2169215) B2169215
theorem B1446191 : Blo 1445542 1446191 := bstep (se 1 (by rfl) ⟨1084643, by rfl⟩ : syracuseStep 1446191 = 2169287) B2169287
theorem B1626439 : Blo 1445542 1626439 := bstep (se 1 (by rfl) ⟨1219829, by rfl⟩ : syracuseStep 1626439 = 2439659) B2439659
theorem B35688791 : Blo 1445542 35688791 := bstep (se 1 (by rfl) ⟨26766593, by rfl⟩ : syracuseStep 35688791 = 53533187) B53533187
theorem B1446431 : Blo 1445542 1446431 := bstep (se 1 (by rfl) ⟨1084823, by rfl⟩ : syracuseStep 1446431 = 2169647) B2169647
theorem B1446683 : Blo 1445542 1446683 := bstep (se 1 (by rfl) ⟨1085012, by rfl⟩ : syracuseStep 1446683 = 2170025) B2170025
theorem B5215099 : Blo 1445542 5215099 := bstep (se 1 (by rfl) ⟨3911324, by rfl⟩ : syracuseStep 5215099 = 7822649) B7822649
theorem B8803325 : Blo 1445542 8803325 := bstep (se 3 (by rfl) ⟨1650623, by rfl⟩ : syracuseStep 8803325 = 3301247) B3301247
theorem B338023439 : Blo 1445542 338023439 := bstep (se 1 (by rfl) ⟨253517579, by rfl⟩ : syracuseStep 338023439 = 507035159) B507035159
theorem B4879547 : Blo 1445542 4879547 := bstep (se 1 (by rfl) ⟨3659660, by rfl⟩ : syracuseStep 4879547 = 7319321) B7319321
theorem B10425611 : Blo 1445542 10425611 := bstep (se 1 (by rfl) ⟨7819208, by rfl⟩ : syracuseStep 10425611 = 15638417) B15638417
theorem B1627807 : Blo 1445542 1627807 := bstep (se 1 (by rfl) ⟨1220855, by rfl⟩ : syracuseStep 1627807 = 2441711) B2441711
theorem B10983113 : Blo 1445542 10983113 := bstep (se 2 (by rfl) ⟨4118667, by rfl⟩ : syracuseStep 10983113 = 8237335) B8237335
theorem B2169209 : Blo 1445542 2169209 := bstep (se 2 (by rfl) ⟨813453, by rfl⟩ : syracuseStep 2169209 = 1626907) B1626907
theorem B7322399 : Blo 1445542 7322399 := bstep (se 1 (by rfl) ⟨5491799, by rfl⟩ : syracuseStep 7322399 = 10983599) B10983599
theorem B13188055 : Blo 1445542 13188055 := bstep (se 1 (by rfl) ⟨9891041, by rfl⟩ : syracuseStep 13188055 = 19782083) B19782083
theorem B2169983 : Blo 1445542 2169983 := bstep (se 1 (by rfl) ⟨1627487, by rfl⟩ : syracuseStep 2169983 = 3254975) B3254975
theorem B7323209 : Blo 1445542 7323209 := bstep (se 2 (by rfl) ⟨2746203, by rfl⟩ : syracuseStep 7323209 = 5492407) B5492407
theorem B2605279 : Blo 1445542 2605279 := bstep (se 1 (by rfl) ⟨1953959, by rfl⟩ : syracuseStep 2605279 = 3907919) B3907919
theorem B3253031 : Blo 1445542 3253031 := bstep (se 1 (by rfl) ⟨2439773, by rfl⟩ : syracuseStep 3253031 = 4879547) B4879547
theorem B29688731 : Blo 1445542 29688731 := bstep (se 1 (by rfl) ⟨22266548, by rfl⟩ : syracuseStep 29688731 = 44533097) B44533097
theorem B56362493 : Blo 1445542 56362493 := bstep (se 3 (by rfl) ⟨10567967, by rfl⟩ : syracuseStep 56362493 = 21135935) B21135935
theorem B8243167 : Blo 1445542 8243167 := bstep (se 1 (by rfl) ⟨6182375, by rfl⟩ : syracuseStep 8243167 = 12364751) B12364751
theorem B2607671 : Blo 1445542 2607671 := bstep (se 1 (by rfl) ⟨1955753, by rfl⟩ : syracuseStep 2607671 = 3911507) B3911507
theorem B23792527 : Blo 1445542 23792527 := bstep (se 1 (by rfl) ⟨17844395, by rfl⟩ : syracuseStep 23792527 = 35688791) B35688791
theorem B5868883 : Blo 1445542 5868883 := bstep (se 1 (by rfl) ⟨4401662, by rfl⟩ : syracuseStep 5868883 = 8803325) B8803325
theorem B225348959 : Blo 1445542 225348959 := bstep (se 1 (by rfl) ⟨169011719, by rfl⟩ : syracuseStep 225348959 = 338023439) B338023439
theorem B6950407 : Blo 1445542 6950407 := bstep (se 1 (by rfl) ⟨5212805, by rfl⟩ : syracuseStep 6950407 = 10425611) B10425611
theorem B17584073 : Blo 1445542 17584073 := bstep (se 2 (by rfl) ⟨6594027, by rfl⟩ : syracuseStep 17584073 = 13188055) B13188055
theorem B3256289 : Blo 1445542 3256289 := bstep (se 2 (by rfl) ⟨1221108, by rfl⟩ : syracuseStep 3256289 = 2442217) B2442217
theorem B1446139 : Blo 1445542 1446139 := bstep (se 1 (by rfl) ⟨1084604, by rfl⟩ : syracuseStep 1446139 = 2169209) B2169209
theorem B1446655 : Blo 1445542 1446655 := bstep (se 1 (by rfl) ⟨1084991, by rfl⟩ : syracuseStep 1446655 = 2169983) B2169983
theorem B52786525 : Blo 1445542 52786525 := bstep (se 3 (by rfl) ⟨9897473, by rfl⟩ : syracuseStep 52786525 = 19794947) B19794947
theorem B126915983 : Blo 1445542 126915983 := bstep (se 1 (by rfl) ⟨95186987, by rfl⟩ : syracuseStep 126915983 = 190373975) B190373975
theorem B2168447 : Blo 1445542 2168447 := bstep (se 1 (by rfl) ⟨1626335, by rfl⟩ : syracuseStep 2168447 = 3252671) B3252671
theorem B2168585 : Blo 1445542 2168585 := bstep (se 2 (by rfl) ⟨813219, by rfl⟩ : syracuseStep 2168585 = 1626439) B1626439
theorem B5494655 : Blo 1445542 5494655 := bstep (se 1 (by rfl) ⟨4120991, by rfl⟩ : syracuseStep 5494655 = 8241983) B8241983
theorem B7322075 : Blo 1445542 7322075 := bstep (se 1 (by rfl) ⟨5491556, by rfl⟩ : syracuseStep 7322075 = 10983113) B10983113
theorem B6953465 : Blo 1445542 6953465 := bstep (se 2 (by rfl) ⟨2607549, by rfl⟩ : syracuseStep 6953465 = 5215099) B5215099
theorem B2169455 : Blo 1445542 2169455 := bstep (se 1 (by rfl) ⟨1627091, by rfl⟩ : syracuseStep 2169455 = 3254183) B3254183
theorem B2169767 : Blo 1445542 2169767 := bstep (se 1 (by rfl) ⟨1627325, by rfl⟩ : syracuseStep 2169767 = 3254651) B3254651
theorem B2169947 : Blo 1445542 2169947 := bstep (se 1 (by rfl) ⟨1627460, by rfl⟩ : syracuseStep 2169947 = 3254921) B3254921
theorem B4881599 : Blo 1445542 4881599 := bstep (se 1 (by rfl) ⟨3661199, by rfl⟩ : syracuseStep 4881599 = 7322399) B7322399
theorem B6176225 : Blo 1445542 6176225 := bstep (se 2 (by rfl) ⟨2316084, by rfl⟩ : syracuseStep 6176225 = 4632169) B4632169
theorem B2170367 : Blo 1445542 2170367 := bstep (se 1 (by rfl) ⟨1627775, by rfl⟩ : syracuseStep 2170367 = 3255551) B3255551
theorem B2170409 : Blo 1445542 2170409 := bstep (se 2 (by rfl) ⟨813903, by rfl⟩ : syracuseStep 2170409 = 1627807) B1627807
theorem B2170415 : Blo 1445542 2170415 := bstep (se 1 (by rfl) ⟨1627811, by rfl⟩ : syracuseStep 2170415 = 3255623) B3255623
theorem B4882139 : Blo 1445542 4882139 := bstep (se 1 (by rfl) ⟨3661604, by rfl⟩ : syracuseStep 4882139 = 7323209) B7323209
theorem B120315617 : Blo 1445542 120315617 := bstep (se 2 (by rfl) ⟨45118356, by rfl⟩ : syracuseStep 120315617 = 90236713) B90236713
theorem B3473705 : Blo 1445542 3473705 := bstep (se 2 (by rfl) ⟨1302639, by rfl⟩ : syracuseStep 3473705 = 2605279) B2605279
theorem B19792487 : Blo 1445542 19792487 := bstep (se 1 (by rfl) ⟨14844365, by rfl⟩ : syracuseStep 19792487 = 29688731) B29688731
theorem B3663103 : Blo 1445542 3663103 := bstep (se 1 (by rfl) ⟨2747327, by rfl⟩ : syracuseStep 3663103 = 5494655) B5494655
theorem B150299981 : Blo 1445542 150299981 := bstep (se 3 (by rfl) ⟨28181246, by rfl⟩ : syracuseStep 150299981 = 56362493) B56362493
theorem B7825177 : Blo 1445542 7825177 := bstep (se 2 (by rfl) ⟨2934441, by rfl⟩ : syracuseStep 7825177 = 5868883) B5868883
theorem B9267209 : Blo 1445542 9267209 := bstep (se 2 (by rfl) ⟨3475203, by rfl⟩ : syracuseStep 9267209 = 6950407) B6950407
theorem B3254399 : Blo 1445542 3254399 := bstep (se 1 (by rfl) ⟨2440799, by rfl⟩ : syracuseStep 3254399 = 4881599) B4881599
theorem B3254759 : Blo 1445542 3254759 := bstep (se 1 (by rfl) ⟨2441069, by rfl⟩ : syracuseStep 3254759 = 4882139) B4882139
theorem B80210411 : Blo 1445542 80210411 := bstep (se 1 (by rfl) ⟨60157808, by rfl⟩ : syracuseStep 80210411 = 120315617) B120315617
theorem B84610655 : Blo 1445542 84610655 := bstep (se 1 (by rfl) ⟨63457991, by rfl⟩ : syracuseStep 84610655 = 126915983) B126915983
theorem B1445631 : Blo 1445542 1445631 := bstep (se 1 (by rfl) ⟨1084223, by rfl⟩ : syracuseStep 1445631 = 2168447) B2168447
theorem B1445723 : Blo 1445542 1445723 := bstep (se 1 (by rfl) ⟨1084292, by rfl⟩ : syracuseStep 1445723 = 2168585) B2168585
theorem B31723369 : Blo 1445542 31723369 := bstep (se 2 (by rfl) ⟨11896263, by rfl⟩ : syracuseStep 31723369 = 23792527) B23792527
theorem B1446303 : Blo 1445542 1446303 := bstep (se 1 (by rfl) ⟨1084727, by rfl⟩ : syracuseStep 1446303 = 2169455) B2169455
theorem B70382033 : Blo 1445542 70382033 := bstep (se 2 (by rfl) ⟨26393262, by rfl⟩ : syracuseStep 70382033 = 52786525) B52786525
theorem B1446511 : Blo 1445542 1446511 := bstep (se 1 (by rfl) ⟨1084883, by rfl⟩ : syracuseStep 1446511 = 2169767) B2169767
theorem B1446631 : Blo 1445542 1446631 := bstep (se 1 (by rfl) ⟨1084973, by rfl⟩ : syracuseStep 1446631 = 2169947) B2169947
theorem B4117483 : Blo 1445542 4117483 := bstep (se 1 (by rfl) ⟨3088112, by rfl⟩ : syracuseStep 4117483 = 6176225) B6176225
theorem B1446911 : Blo 1445542 1446911 := bstep (se 1 (by rfl) ⟨1085183, by rfl⟩ : syracuseStep 1446911 = 2170367) B2170367
theorem B1446939 : Blo 1445542 1446939 := bstep (se 1 (by rfl) ⟨1085204, by rfl⟩ : syracuseStep 1446939 = 2170409) B2170409
theorem B1446943 : Blo 1445542 1446943 := bstep (se 1 (by rfl) ⟨1085207, by rfl⟩ : syracuseStep 1446943 = 2170415) B2170415
theorem B10990889 : Blo 1445542 10990889 := bstep (se 2 (by rfl) ⟨4121583, by rfl⟩ : syracuseStep 10990889 = 8243167) B8243167
theorem B2168687 : Blo 1445542 2168687 := bstep (se 1 (by rfl) ⟨1626515, by rfl⟩ : syracuseStep 2168687 = 3253031) B3253031
theorem B6953789 : Blo 1445542 6953789 := bstep (se 3 (by rfl) ⟨1303835, by rfl⟩ : syracuseStep 6953789 = 2607671) B2607671
theorem B4881383 : Blo 1445542 4881383 := bstep (se 1 (by rfl) ⟨3661037, by rfl⟩ : syracuseStep 4881383 = 7322075) B7322075
theorem B4635643 : Blo 1445542 4635643 := bstep (se 1 (by rfl) ⟨3476732, by rfl⟩ : syracuseStep 4635643 = 6953465) B6953465
theorem B150232639 : Blo 1445542 150232639 := bstep (se 1 (by rfl) ⟨112674479, by rfl⟩ : syracuseStep 150232639 = 225348959) B225348959
theorem B11722715 : Blo 1445542 11722715 := bstep (se 1 (by rfl) ⟨8792036, by rfl⟩ : syracuseStep 11722715 = 17584073) B17584073
theorem B2170859 : Blo 1445542 2170859 := bstep (se 1 (by rfl) ⟨1628144, by rfl⟩ : syracuseStep 2170859 = 3256289) B3256289
theorem B5489977 : Blo 1445542 5489977 := bstep (se 2 (by rfl) ⟨2058741, by rfl⟩ : syracuseStep 5489977 = 4117483) B4117483
theorem B6178139 : Blo 1445542 6178139 := bstep (se 1 (by rfl) ⟨4633604, by rfl⟩ : syracuseStep 6178139 = 9267209) B9267209
theorem B4884137 : Blo 1445542 4884137 := bstep (se 2 (by rfl) ⟨1831551, by rfl⟩ : syracuseStep 4884137 = 3663103) B3663103
theorem B3254255 : Blo 1445542 3254255 := bstep (se 1 (by rfl) ⟨2440691, by rfl⟩ : syracuseStep 3254255 = 4881383) B4881383
theorem B7327259 : Blo 1445542 7327259 := bstep (se 1 (by rfl) ⟨5495444, by rfl⟩ : syracuseStep 7327259 = 10990889) B10990889
theorem B100199987 : Blo 1445542 100199987 := bstep (se 1 (by rfl) ⟨75149990, by rfl⟩ : syracuseStep 100199987 = 150299981) B150299981
theorem B1445791 : Blo 1445542 1445791 := bstep (se 1 (by rfl) ⟨1084343, by rfl⟩ : syracuseStep 1445791 = 2168687) B2168687
theorem B6180857 : Blo 1445542 6180857 := bstep (se 2 (by rfl) ⟨2317821, by rfl⟩ : syracuseStep 6180857 = 4635643) B4635643
theorem B53473607 : Blo 1445542 53473607 := bstep (se 1 (by rfl) ⟨40105205, by rfl⟩ : syracuseStep 53473607 = 80210411) B80210411
theorem B18543437 : Blo 1445542 18543437 := bstep (se 3 (by rfl) ⟨3476894, by rfl⟩ : syracuseStep 18543437 = 6953789) B6953789
theorem B10433569 : Blo 1445542 10433569 := bstep (se 2 (by rfl) ⟨3912588, by rfl⟩ : syracuseStep 10433569 = 7825177) B7825177
theorem B56407103 : Blo 1445542 56407103 := bstep (se 1 (by rfl) ⟨42305327, by rfl⟩ : syracuseStep 56407103 = 84610655) B84610655
theorem B1447239 : Blo 1445542 1447239 := bstep (se 1 (by rfl) ⟨1085429, by rfl⟩ : syracuseStep 1447239 = 2170859) B2170859
theorem B2315803 : Blo 1445542 2315803 := bstep (se 1 (by rfl) ⟨1736852, by rfl⟩ : syracuseStep 2315803 = 3473705) B3473705
theorem B46921355 : Blo 1445542 46921355 := bstep (se 1 (by rfl) ⟨35191016, by rfl⟩ : syracuseStep 46921355 = 70382033) B70382033
theorem B13194991 : Blo 1445542 13194991 := bstep (se 1 (by rfl) ⟨9896243, by rfl⟩ : syracuseStep 13194991 = 19792487) B19792487
theorem B2169599 : Blo 1445542 2169599 := bstep (se 1 (by rfl) ⟨1627199, by rfl⟩ : syracuseStep 2169599 = 3254399) B3254399
theorem B2169839 : Blo 1445542 2169839 := bstep (se 1 (by rfl) ⟨1627379, by rfl⟩ : syracuseStep 2169839 = 3254759) B3254759
theorem B200310185 : Blo 1445542 200310185 := bstep (se 2 (by rfl) ⟨75116319, by rfl⟩ : syracuseStep 200310185 = 150232639) B150232639
theorem B676765205 : Blo 1445542 676765205 := bstep (se 6 (by rfl) ⟨15861684, by rfl⟩ : syracuseStep 676765205 = 31723369) B31723369
theorem B7815143 : Blo 1445542 7815143 := bstep (se 1 (by rfl) ⟨5861357, by rfl⟩ : syracuseStep 7815143 = 11722715) B11722715
theorem B12362291 : Blo 1445542 12362291 := bstep (se 1 (by rfl) ⟨9271718, by rfl⟩ : syracuseStep 12362291 = 18543437) B18543437
theorem B13911425 : Blo 1445542 13911425 := bstep (se 2 (by rfl) ⟨5216784, by rfl⟩ : syracuseStep 13911425 = 10433569) B10433569
theorem B133540123 : Blo 1445542 133540123 := bstep (se 1 (by rfl) ⟨100155092, by rfl⟩ : syracuseStep 133540123 = 200310185) B200310185
theorem B451176803 : Blo 1445542 451176803 := bstep (se 1 (by rfl) ⟨338382602, by rfl⟩ : syracuseStep 451176803 = 676765205) B676765205
theorem B4884839 : Blo 1445542 4884839 := bstep (se 1 (by rfl) ⟨3663629, by rfl⟩ : syracuseStep 4884839 = 7327259) B7327259
theorem B66799991 : Blo 1445542 66799991 := bstep (se 1 (by rfl) ⟨50099993, by rfl⟩ : syracuseStep 66799991 = 100199987) B100199987
theorem B37604735 : Blo 1445542 37604735 := bstep (se 1 (by rfl) ⟨28203551, by rfl⟩ : syracuseStep 37604735 = 56407103) B56407103
theorem B31280903 : Blo 1445542 31280903 := bstep (se 1 (by rfl) ⟨23460677, by rfl⟩ : syracuseStep 31280903 = 46921355) B46921355
theorem B3256091 : Blo 1445542 3256091 := bstep (se 1 (by rfl) ⟨2442068, by rfl⟩ : syracuseStep 3256091 = 4884137) B4884137
theorem B7319969 : Blo 1445542 7319969 := bstep (se 2 (by rfl) ⟨2744988, by rfl⟩ : syracuseStep 7319969 = 5489977) B5489977
theorem B1446399 : Blo 1445542 1446399 := bstep (se 1 (by rfl) ⟨1084799, by rfl⟩ : syracuseStep 1446399 = 2169599) B2169599
theorem B1446559 : Blo 1445542 1446559 := bstep (se 1 (by rfl) ⟨1084919, by rfl⟩ : syracuseStep 1446559 = 2169839) B2169839
theorem B17593321 : Blo 1445542 17593321 := bstep (se 2 (by rfl) ⟨6597495, by rfl⟩ : syracuseStep 17593321 = 13194991) B13194991
theorem B35649071 : Blo 1445542 35649071 := bstep (se 1 (by rfl) ⟨26736803, by rfl⟩ : syracuseStep 35649071 = 53473607) B53473607
theorem B4118759 : Blo 1445542 4118759 := bstep (se 1 (by rfl) ⟨3089069, by rfl⟩ : syracuseStep 4118759 = 6178139) B6178139
theorem B2169503 : Blo 1445542 2169503 := bstep (se 1 (by rfl) ⟨1627127, by rfl⟩ : syracuseStep 2169503 = 3254255) B3254255
theorem B3087737 : Blo 1445542 3087737 := bstep (se 2 (by rfl) ⟨1157901, by rfl⟩ : syracuseStep 3087737 = 2315803) B2315803
theorem B5210095 : Blo 1445542 5210095 := bstep (se 1 (by rfl) ⟨3907571, by rfl⟩ : syracuseStep 5210095 = 7815143) B7815143
theorem B4120571 : Blo 1445542 4120571 := bstep (se 1 (by rfl) ⟨3090428, by rfl⟩ : syracuseStep 4120571 = 6180857) B6180857
theorem B8241527 : Blo 1445542 8241527 := bstep (se 1 (by rfl) ⟨6181145, by rfl⟩ : syracuseStep 8241527 = 12362291) B12362291
theorem B178053497 : Blo 1445542 178053497 := bstep (se 2 (by rfl) ⟨66770061, by rfl⟩ : syracuseStep 178053497 = 133540123) B133540123
theorem B9274283 : Blo 1445542 9274283 := bstep (se 1 (by rfl) ⟨6955712, by rfl⟩ : syracuseStep 9274283 = 13911425) B13911425
theorem B23766047 : Blo 1445542 23766047 := bstep (se 1 (by rfl) ⟨17824535, by rfl⟩ : syracuseStep 23766047 = 35649071) B35649071
theorem B2745839 : Blo 1445542 2745839 := bstep (se 1 (by rfl) ⟨2059379, by rfl⟩ : syracuseStep 2745839 = 4118759) B4118759
theorem B44533327 : Blo 1445542 44533327 := bstep (se 1 (by rfl) ⟨33399995, by rfl⟩ : syracuseStep 44533327 = 66799991) B66799991
theorem B2058491 : Blo 1445542 2058491 := bstep (se 1 (by rfl) ⟨1543868, by rfl⟩ : syracuseStep 2058491 = 3087737) B3087737
theorem B25069823 : Blo 1445542 25069823 := bstep (se 1 (by rfl) ⟨18802367, by rfl⟩ : syracuseStep 25069823 = 37604735) B37604735
theorem B2747047 : Blo 1445542 2747047 := bstep (se 1 (by rfl) ⟨2060285, by rfl⟩ : syracuseStep 2747047 = 4120571) B4120571
theorem B23457761 : Blo 1445542 23457761 := bstep (se 2 (by rfl) ⟨8796660, by rfl⟩ : syracuseStep 23457761 = 17593321) B17593321
theorem B3256559 : Blo 1445542 3256559 := bstep (se 1 (by rfl) ⟨2442419, by rfl⟩ : syracuseStep 3256559 = 4884839) B4884839
theorem B1446335 : Blo 1445542 1446335 := bstep (se 1 (by rfl) ⟨1084751, by rfl⟩ : syracuseStep 1446335 = 2169503) B2169503
theorem B20853935 : Blo 1445542 20853935 := bstep (se 1 (by rfl) ⟨15640451, by rfl⟩ : syracuseStep 20853935 = 31280903) B31280903
theorem B4879979 : Blo 1445542 4879979 := bstep (se 1 (by rfl) ⟨3659984, by rfl⟩ : syracuseStep 4879979 = 7319969) B7319969
theorem B300784535 : Blo 1445542 300784535 := bstep (se 1 (by rfl) ⟨225588401, by rfl⟩ : syracuseStep 300784535 = 451176803) B451176803
theorem B2170727 : Blo 1445542 2170727 := bstep (se 1 (by rfl) ⟨1628045, by rfl⟩ : syracuseStep 2170727 = 3256091) B3256091
theorem B6946793 : Blo 1445542 6946793 := bstep (se 2 (by rfl) ⟨2605047, by rfl⟩ : syracuseStep 6946793 = 5210095) B5210095
theorem B2171039 : Blo 1445542 2171039 := bstep (se 1 (by rfl) ⟨1628279, by rfl⟩ : syracuseStep 2171039 = 3256559) B3256559
theorem B118702331 : Blo 1445542 118702331 := bstep (se 1 (by rfl) ⟨89026748, by rfl⟩ : syracuseStep 118702331 = 178053497) B178053497
theorem B5489309 : Blo 1445542 5489309 := bstep (se 3 (by rfl) ⟨1029245, by rfl⟩ : syracuseStep 5489309 = 2058491) B2058491
theorem B15844031 : Blo 1445542 15844031 := bstep (se 1 (by rfl) ⟨11883023, by rfl⟩ : syracuseStep 15844031 = 23766047) B23766047
theorem B13902623 : Blo 1445542 13902623 := bstep (se 1 (by rfl) ⟨10426967, by rfl⟩ : syracuseStep 13902623 = 20853935) B20853935
theorem B3662729 : Blo 1445542 3662729 := bstep (se 2 (by rfl) ⟨1373523, by rfl⟩ : syracuseStep 3662729 = 2747047) B2747047
theorem B3253319 : Blo 1445542 3253319 := bstep (se 1 (by rfl) ⟨2439989, by rfl⟩ : syracuseStep 3253319 = 4879979) B4879979
theorem B16713215 : Blo 1445542 16713215 := bstep (se 1 (by rfl) ⟨12534911, by rfl⟩ : syracuseStep 16713215 = 25069823) B25069823
theorem B59377769 : Blo 1445542 59377769 := bstep (se 2 (by rfl) ⟨22266663, by rfl⟩ : syracuseStep 59377769 = 44533327) B44533327
theorem B4631195 : Blo 1445542 4631195 := bstep (se 1 (by rfl) ⟨3473396, by rfl⟩ : syracuseStep 4631195 = 6946793) B6946793
theorem B1447151 : Blo 1445542 1447151 := bstep (se 1 (by rfl) ⟨1085363, by rfl⟩ : syracuseStep 1447151 = 2170727) B2170727
theorem B5494351 : Blo 1445542 5494351 := bstep (se 1 (by rfl) ⟨4120763, by rfl⟩ : syracuseStep 5494351 = 8241527) B8241527
theorem B6182855 : Blo 1445542 6182855 := bstep (se 1 (by rfl) ⟨4637141, by rfl⟩ : syracuseStep 6182855 = 9274283) B9274283
theorem B7322237 : Blo 1445542 7322237 := bstep (se 3 (by rfl) ⟨1372919, by rfl⟩ : syracuseStep 7322237 = 2745839) B2745839
theorem B200523023 : Blo 1445542 200523023 := bstep (se 1 (by rfl) ⟨150392267, by rfl⟩ : syracuseStep 200523023 = 300784535) B300784535
theorem B15638507 : Blo 1445542 15638507 := bstep (se 1 (by rfl) ⟨11728880, by rfl⟩ : syracuseStep 15638507 = 23457761) B23457761
theorem B79134887 : Blo 1445542 79134887 := bstep (se 1 (by rfl) ⟨59351165, by rfl⟩ : syracuseStep 79134887 = 118702331) B118702331
theorem B2441819 : Blo 1445542 2441819 := bstep (se 1 (by rfl) ⟨1831364, by rfl⟩ : syracuseStep 2441819 = 3662729) B3662729
theorem B11142143 : Blo 1445542 11142143 := bstep (se 1 (by rfl) ⟨8356607, by rfl⟩ : syracuseStep 11142143 = 16713215) B16713215
theorem B4121903 : Blo 1445542 4121903 := bstep (se 1 (by rfl) ⟨3091427, by rfl⟩ : syracuseStep 4121903 = 6182855) B6182855
theorem B39585179 : Blo 1445542 39585179 := bstep (se 1 (by rfl) ⟨29688884, by rfl⟩ : syracuseStep 39585179 = 59377769) B59377769
theorem B7325801 : Blo 1445542 7325801 := bstep (se 2 (by rfl) ⟨2747175, by rfl⟩ : syracuseStep 7325801 = 5494351) B5494351
theorem B10562687 : Blo 1445542 10562687 := bstep (se 1 (by rfl) ⟨7922015, by rfl⟩ : syracuseStep 10562687 = 15844031) B15844031
theorem B9268415 : Blo 1445542 9268415 := bstep (se 1 (by rfl) ⟨6951311, by rfl⟩ : syracuseStep 9268415 = 13902623) B13902623
theorem B12349853 : Blo 1445542 12349853 := bstep (se 3 (by rfl) ⟨2315597, by rfl⟩ : syracuseStep 12349853 = 4631195) B4631195
theorem B133682015 : Blo 1445542 133682015 := bstep (se 1 (by rfl) ⟨100261511, by rfl⟩ : syracuseStep 133682015 = 200523023) B200523023
theorem B10425671 : Blo 1445542 10425671 := bstep (se 1 (by rfl) ⟨7819253, by rfl⟩ : syracuseStep 10425671 = 15638507) B15638507
theorem B1447359 : Blo 1445542 1447359 := bstep (se 1 (by rfl) ⟨1085519, by rfl⟩ : syracuseStep 1447359 = 2171039) B2171039
theorem B3659539 : Blo 1445542 3659539 := bstep (se 1 (by rfl) ⟨2744654, by rfl⟩ : syracuseStep 3659539 = 5489309) B5489309
theorem B2168879 : Blo 1445542 2168879 := bstep (se 1 (by rfl) ⟨1626659, by rfl⟩ : syracuseStep 2168879 = 3253319) B3253319
theorem B4881491 : Blo 1445542 4881491 := bstep (se 1 (by rfl) ⟨3661118, by rfl⟩ : syracuseStep 4881491 = 7322237) B7322237
theorem B52756591 : Blo 1445542 52756591 := bstep (se 1 (by rfl) ⟨39567443, by rfl⟩ : syracuseStep 52756591 = 79134887) B79134887
theorem B8233235 : Blo 1445542 8233235 := bstep (se 1 (by rfl) ⟨6174926, by rfl⟩ : syracuseStep 8233235 = 12349853) B12349853
theorem B89121343 : Blo 1445542 89121343 := bstep (se 1 (by rfl) ⟨66841007, by rfl⟩ : syracuseStep 89121343 = 133682015) B133682015
theorem B4883867 : Blo 1445542 4883867 := bstep (se 1 (by rfl) ⟨3662900, by rfl⟩ : syracuseStep 4883867 = 7325801) B7325801
theorem B3254327 : Blo 1445542 3254327 := bstep (se 1 (by rfl) ⟨2440745, by rfl⟩ : syracuseStep 3254327 = 4881491) B4881491
theorem B6178943 : Blo 1445542 6178943 := bstep (se 1 (by rfl) ⟨4634207, by rfl⟩ : syracuseStep 6178943 = 9268415) B9268415
theorem B2747935 : Blo 1445542 2747935 := bstep (se 1 (by rfl) ⟨2060951, by rfl⟩ : syracuseStep 2747935 = 4121903) B4121903
theorem B6950447 : Blo 1445542 6950447 := bstep (se 1 (by rfl) ⟨5212835, by rfl⟩ : syracuseStep 6950447 = 10425671) B10425671
theorem B26390119 : Blo 1445542 26390119 := bstep (se 1 (by rfl) ⟨19792589, by rfl⟩ : syracuseStep 26390119 = 39585179) B39585179
theorem B1445919 : Blo 1445542 1445919 := bstep (se 1 (by rfl) ⟨1084439, by rfl⟩ : syracuseStep 1445919 = 2168879) B2168879
theorem B7041791 : Blo 1445542 7041791 := bstep (se 1 (by rfl) ⟨5281343, by rfl⟩ : syracuseStep 7041791 = 10562687) B10562687
theorem B4879385 : Blo 1445542 4879385 := bstep (se 2 (by rfl) ⟨1829769, by rfl⟩ : syracuseStep 4879385 = 3659539) B3659539
theorem B1627879 : Blo 1445542 1627879 := bstep (se 1 (by rfl) ⟨1220909, by rfl⟩ : syracuseStep 1627879 = 2441819) B2441819
theorem B7428095 : Blo 1445542 7428095 := bstep (se 1 (by rfl) ⟨5571071, by rfl⟩ : syracuseStep 7428095 = 11142143) B11142143
theorem B5488823 : Blo 1445542 5488823 := bstep (se 1 (by rfl) ⟨4116617, by rfl⟩ : syracuseStep 5488823 = 8233235) B8233235
theorem B4694527 : Blo 1445542 4694527 := bstep (se 1 (by rfl) ⟨3520895, by rfl⟩ : syracuseStep 4694527 = 7041791) B7041791
theorem B3252923 : Blo 1445542 3252923 := bstep (se 1 (by rfl) ⟨2439692, by rfl⟩ : syracuseStep 3252923 = 4879385) B4879385
theorem B3663913 : Blo 1445542 3663913 := bstep (se 2 (by rfl) ⟨1373967, by rfl⟩ : syracuseStep 3663913 = 2747935) B2747935
theorem B35186825 : Blo 1445542 35186825 := bstep (se 2 (by rfl) ⟨13195059, by rfl⟩ : syracuseStep 35186825 = 26390119) B26390119
theorem B118828457 : Blo 1445542 118828457 := bstep (se 2 (by rfl) ⟨44560671, by rfl⟩ : syracuseStep 118828457 = 89121343) B89121343
theorem B3255911 : Blo 1445542 3255911 := bstep (se 1 (by rfl) ⟨2441933, by rfl⟩ : syracuseStep 3255911 = 4883867) B4883867
theorem B4952063 : Blo 1445542 4952063 := bstep (se 1 (by rfl) ⟨3714047, by rfl⟩ : syracuseStep 4952063 = 7428095) B7428095
theorem B4633631 : Blo 1445542 4633631 := bstep (se 1 (by rfl) ⟨3475223, by rfl⟩ : syracuseStep 4633631 = 6950447) B6950447
theorem B70342121 : Blo 1445542 70342121 := bstep (se 2 (by rfl) ⟨26378295, by rfl⟩ : syracuseStep 70342121 = 52756591) B52756591
theorem B2169551 : Blo 1445542 2169551 := bstep (se 1 (by rfl) ⟨1627163, by rfl⟩ : syracuseStep 2169551 = 3254327) B3254327
theorem B4119295 : Blo 1445542 4119295 := bstep (se 1 (by rfl) ⟨3089471, by rfl⟩ : syracuseStep 4119295 = 6178943) B6178943
theorem B2170505 : Blo 1445542 2170505 := bstep (se 2 (by rfl) ⟨813939, by rfl⟩ : syracuseStep 2170505 = 1627879) B1627879
theorem B6259369 : Blo 1445542 6259369 := bstep (se 2 (by rfl) ⟨2347263, by rfl⟩ : syracuseStep 6259369 = 4694527) B4694527
theorem B3089087 : Blo 1445542 3089087 := bstep (se 1 (by rfl) ⟨2316815, by rfl⟩ : syracuseStep 3089087 = 4633631) B4633631
theorem B79218971 : Blo 1445542 79218971 := bstep (se 1 (by rfl) ⟨59414228, by rfl⟩ : syracuseStep 79218971 = 118828457) B118828457
theorem B4885217 : Blo 1445542 4885217 := bstep (se 2 (by rfl) ⟨1831956, by rfl⟩ : syracuseStep 4885217 = 3663913) B3663913
theorem B13205501 : Blo 1445542 13205501 := bstep (se 3 (by rfl) ⟨2476031, by rfl⟩ : syracuseStep 13205501 = 4952063) B4952063
theorem B46894747 : Blo 1445542 46894747 := bstep (se 1 (by rfl) ⟨35171060, by rfl⟩ : syracuseStep 46894747 = 70342121) B70342121
theorem B5492393 : Blo 1445542 5492393 := bstep (se 2 (by rfl) ⟨2059647, by rfl⟩ : syracuseStep 5492393 = 4119295) B4119295
theorem B23457883 : Blo 1445542 23457883 := bstep (se 1 (by rfl) ⟨17593412, by rfl⟩ : syracuseStep 23457883 = 35186825) B35186825
theorem B1446367 : Blo 1445542 1446367 := bstep (se 1 (by rfl) ⟨1084775, by rfl⟩ : syracuseStep 1446367 = 2169551) B2169551
theorem B1447003 : Blo 1445542 1447003 := bstep (se 1 (by rfl) ⟨1085252, by rfl⟩ : syracuseStep 1447003 = 2170505) B2170505
theorem B3659215 : Blo 1445542 3659215 := bstep (se 1 (by rfl) ⟨2744411, by rfl⟩ : syracuseStep 3659215 = 5488823) B5488823
theorem B2168615 : Blo 1445542 2168615 := bstep (se 1 (by rfl) ⟨1626461, by rfl⟩ : syracuseStep 2168615 = 3252923) B3252923
theorem B2170607 : Blo 1445542 2170607 := bstep (se 1 (by rfl) ⟨1627955, by rfl⟩ : syracuseStep 2170607 = 3255911) B3255911
theorem B31277177 : Blo 1445542 31277177 := bstep (se 2 (by rfl) ⟨11728941, by rfl⟩ : syracuseStep 31277177 = 23457883) B23457883
theorem B2059391 : Blo 1445542 2059391 := bstep (se 1 (by rfl) ⟨1544543, by rfl⟩ : syracuseStep 2059391 = 3089087) B3089087
theorem B1445743 : Blo 1445542 1445743 := bstep (se 1 (by rfl) ⟨1084307, by rfl⟩ : syracuseStep 1445743 = 2168615) B2168615
theorem B3256811 : Blo 1445542 3256811 := bstep (se 1 (by rfl) ⟨2442608, by rfl⟩ : syracuseStep 3256811 = 4885217) B4885217
theorem B4878953 : Blo 1445542 4878953 := bstep (se 2 (by rfl) ⟨1829607, by rfl⟩ : syracuseStep 4878953 = 3659215) B3659215
theorem B62526329 : Blo 1445542 62526329 := bstep (se 2 (by rfl) ⟨23447373, by rfl⟩ : syracuseStep 62526329 = 46894747) B46894747
theorem B1447071 : Blo 1445542 1447071 := bstep (se 1 (by rfl) ⟨1085303, by rfl⟩ : syracuseStep 1447071 = 2170607) B2170607
theorem B8803667 : Blo 1445542 8803667 := bstep (se 1 (by rfl) ⟨6602750, by rfl⟩ : syracuseStep 8803667 = 13205501) B13205501
theorem B8345825 : Blo 1445542 8345825 := bstep (se 2 (by rfl) ⟨3129684, by rfl⟩ : syracuseStep 8345825 = 6259369) B6259369
theorem B52812647 : Blo 1445542 52812647 := bstep (se 1 (by rfl) ⟨39609485, by rfl⟩ : syracuseStep 52812647 = 79218971) B79218971
theorem B3661595 : Blo 1445542 3661595 := bstep (se 1 (by rfl) ⟨2746196, by rfl⟩ : syracuseStep 3661595 = 5492393) B5492393
theorem B2171207 : Blo 1445542 2171207 := bstep (se 1 (by rfl) ⟨1628405, by rfl⟩ : syracuseStep 2171207 = 3256811) B3256811
theorem B3252635 : Blo 1445542 3252635 := bstep (se 1 (by rfl) ⟨2439476, by rfl⟩ : syracuseStep 3252635 = 4878953) B4878953
theorem B5563883 : Blo 1445542 5563883 := bstep (se 1 (by rfl) ⟨4172912, by rfl⟩ : syracuseStep 5563883 = 8345825) B8345825
theorem B20851451 : Blo 1445542 20851451 := bstep (se 1 (by rfl) ⟨15638588, by rfl⟩ : syracuseStep 20851451 = 31277177) B31277177
theorem B5491709 : Blo 1445542 5491709 := bstep (se 3 (by rfl) ⟨1029695, by rfl⟩ : syracuseStep 5491709 = 2059391) B2059391
theorem B41684219 : Blo 1445542 41684219 := bstep (se 1 (by rfl) ⟨31263164, by rfl⟩ : syracuseStep 41684219 = 62526329) B62526329
theorem B5869111 : Blo 1445542 5869111 := bstep (se 1 (by rfl) ⟨4401833, by rfl⟩ : syracuseStep 5869111 = 8803667) B8803667
theorem B35208431 : Blo 1445542 35208431 := bstep (se 1 (by rfl) ⟨26406323, by rfl⟩ : syracuseStep 35208431 = 52812647) B52812647
theorem B2441063 : Blo 1445542 2441063 := bstep (se 1 (by rfl) ⟨1830797, by rfl⟩ : syracuseStep 2441063 = 3661595) B3661595
theorem B7825481 : Blo 1445542 7825481 := bstep (se 2 (by rfl) ⟨2934555, by rfl⟩ : syracuseStep 7825481 = 5869111) B5869111
theorem B23472287 : Blo 1445542 23472287 := bstep (se 1 (by rfl) ⟨17604215, by rfl⟩ : syracuseStep 23472287 = 35208431) B35208431
theorem B27789479 : Blo 1445542 27789479 := bstep (se 1 (by rfl) ⟨20842109, by rfl⟩ : syracuseStep 27789479 = 41684219) B41684219
theorem B1627375 : Blo 1445542 1627375 := bstep (se 1 (by rfl) ⟨1220531, by rfl⟩ : syracuseStep 1627375 = 2441063) B2441063
theorem B1447471 : Blo 1445542 1447471 := bstep (se 1 (by rfl) ⟨1085603, by rfl⟩ : syracuseStep 1447471 = 2171207) B2171207
theorem B2168423 : Blo 1445542 2168423 := bstep (se 1 (by rfl) ⟨1626317, by rfl⟩ : syracuseStep 2168423 = 3252635) B3252635
theorem B3709255 : Blo 1445542 3709255 := bstep (se 1 (by rfl) ⟨2781941, by rfl⟩ : syracuseStep 3709255 = 5563883) B5563883
theorem B13900967 : Blo 1445542 13900967 := bstep (se 1 (by rfl) ⟨10425725, by rfl⟩ : syracuseStep 13900967 = 20851451) B20851451
theorem B3661139 : Blo 1445542 3661139 := bstep (se 1 (by rfl) ⟨2745854, by rfl⟩ : syracuseStep 3661139 = 5491709) B5491709
theorem B15648191 : Blo 1445542 15648191 := bstep (se 1 (by rfl) ⟨11736143, by rfl⟩ : syracuseStep 15648191 = 23472287) B23472287
theorem B9267311 : Blo 1445542 9267311 := bstep (se 1 (by rfl) ⟨6950483, by rfl⟩ : syracuseStep 9267311 = 13900967) B13900967
theorem B1445615 : Blo 1445542 1445615 := bstep (se 1 (by rfl) ⟨1084211, by rfl⟩ : syracuseStep 1445615 = 2168423) B2168423
theorem B18526319 : Blo 1445542 18526319 := bstep (se 1 (by rfl) ⟨13894739, by rfl⟩ : syracuseStep 18526319 = 27789479) B27789479
theorem B4945673 : Blo 1445542 4945673 := bstep (se 2 (by rfl) ⟨1854627, by rfl⟩ : syracuseStep 4945673 = 3709255) B3709255
theorem B5216987 : Blo 1445542 5216987 := bstep (se 1 (by rfl) ⟨3912740, by rfl⟩ : syracuseStep 5216987 = 7825481) B7825481
theorem B2169833 : Blo 1445542 2169833 := bstep (se 2 (by rfl) ⟨813687, by rfl⟩ : syracuseStep 2169833 = 1627375) B1627375
theorem B2440759 : Blo 1445542 2440759 := bstep (se 1 (by rfl) ⟨1830569, by rfl⟩ : syracuseStep 2440759 = 3661139) B3661139
theorem B6178207 : Blo 1445542 6178207 := bstep (se 1 (by rfl) ⟨4633655, by rfl⟩ : syracuseStep 6178207 = 9267311) B9267311
theorem B3254345 : Blo 1445542 3254345 := bstep (se 2 (by rfl) ⟨1220379, by rfl⟩ : syracuseStep 3254345 = 2440759) B2440759
theorem B10432127 : Blo 1445542 10432127 := bstep (se 1 (by rfl) ⟨7824095, by rfl⟩ : syracuseStep 10432127 = 15648191) B15648191
theorem B3297115 : Blo 1445542 3297115 := bstep (se 1 (by rfl) ⟨2472836, by rfl⟩ : syracuseStep 3297115 = 4945673) B4945673
theorem B3477991 : Blo 1445542 3477991 := bstep (se 1 (by rfl) ⟨2608493, by rfl⟩ : syracuseStep 3477991 = 5216987) B5216987
theorem B1446555 : Blo 1445542 1446555 := bstep (se 1 (by rfl) ⟨1084916, by rfl⟩ : syracuseStep 1446555 = 2169833) B2169833
theorem B12350879 : Blo 1445542 12350879 := bstep (se 1 (by rfl) ⟨9263159, by rfl⟩ : syracuseStep 12350879 = 18526319) B18526319
theorem B4637321 : Blo 1445542 4637321 := bstep (se 2 (by rfl) ⟨1738995, by rfl⟩ : syracuseStep 4637321 = 3477991) B3477991
theorem B8233919 : Blo 1445542 8233919 := bstep (se 1 (by rfl) ⟨6175439, by rfl⟩ : syracuseStep 8233919 = 12350879) B12350879
theorem B8237609 : Blo 1445542 8237609 := bstep (se 2 (by rfl) ⟨3089103, by rfl⟩ : syracuseStep 8237609 = 6178207) B6178207
theorem B4396153 : Blo 1445542 4396153 := bstep (se 2 (by rfl) ⟨1648557, by rfl⟩ : syracuseStep 4396153 = 3297115) B3297115
theorem B2169563 : Blo 1445542 2169563 := bstep (se 1 (by rfl) ⟨1627172, by rfl⟩ : syracuseStep 2169563 = 3254345) B3254345
theorem B6954751 : Blo 1445542 6954751 := bstep (se 1 (by rfl) ⟨5216063, by rfl⟩ : syracuseStep 6954751 = 10432127) B10432127
theorem B5489279 : Blo 1445542 5489279 := bstep (se 1 (by rfl) ⟨4116959, by rfl⟩ : syracuseStep 5489279 = 8233919) B8233919
theorem B5491739 : Blo 1445542 5491739 := bstep (se 1 (by rfl) ⟨4118804, by rfl⟩ : syracuseStep 5491739 = 8237609) B8237609
theorem B3091547 : Blo 1445542 3091547 := bstep (se 1 (by rfl) ⟨2318660, by rfl⟩ : syracuseStep 3091547 = 4637321) B4637321
theorem B5861537 : Blo 1445542 5861537 := bstep (se 2 (by rfl) ⟨2198076, by rfl⟩ : syracuseStep 5861537 = 4396153) B4396153
theorem B1446375 : Blo 1445542 1446375 := bstep (se 1 (by rfl) ⟨1084781, by rfl⟩ : syracuseStep 1446375 = 2169563) B2169563
theorem B9273001 : Blo 1445542 9273001 := bstep (se 2 (by rfl) ⟨3477375, by rfl⟩ : syracuseStep 9273001 = 6954751) B6954751
theorem B3907691 : Blo 1445542 3907691 := bstep (se 1 (by rfl) ⟨2930768, by rfl⟩ : syracuseStep 3907691 = 5861537) B5861537
theorem B12364001 : Blo 1445542 12364001 := bstep (se 2 (by rfl) ⟨4636500, by rfl⟩ : syracuseStep 12364001 = 9273001) B9273001
theorem B8244125 : Blo 1445542 8244125 := bstep (se 3 (by rfl) ⟨1545773, by rfl⟩ : syracuseStep 8244125 = 3091547) B3091547
theorem B3659519 : Blo 1445542 3659519 := bstep (se 1 (by rfl) ⟨2744639, by rfl⟩ : syracuseStep 3659519 = 5489279) B5489279
theorem B3661159 : Blo 1445542 3661159 := bstep (se 1 (by rfl) ⟨2745869, by rfl⟩ : syracuseStep 3661159 = 5491739) B5491739
theorem B2605127 : Blo 1445542 2605127 := bstep (se 1 (by rfl) ⟨1953845, by rfl⟩ : syracuseStep 2605127 = 3907691) B3907691
theorem B8242667 : Blo 1445542 8242667 := bstep (se 1 (by rfl) ⟨6182000, by rfl⟩ : syracuseStep 8242667 = 12364001) B12364001
theorem B2439679 : Blo 1445542 2439679 := bstep (se 1 (by rfl) ⟨1829759, by rfl⟩ : syracuseStep 2439679 = 3659519) B3659519
theorem B4881545 : Blo 1445542 4881545 := bstep (se 2 (by rfl) ⟨1830579, by rfl⟩ : syracuseStep 4881545 = 3661159) B3661159
theorem B5496083 : Blo 1445542 5496083 := bstep (se 1 (by rfl) ⟨4122062, by rfl⟩ : syracuseStep 5496083 = 8244125) B8244125
theorem B3252905 : Blo 1445542 3252905 := bstep (se 2 (by rfl) ⟨1219839, by rfl⟩ : syracuseStep 3252905 = 2439679) B2439679
theorem B27788021 : Blo 1445542 27788021 := bstep (se 5 (by rfl) ⟨1302563, by rfl⟩ : syracuseStep 27788021 = 2605127) B2605127
theorem B3254363 : Blo 1445542 3254363 := bstep (se 1 (by rfl) ⟨2440772, by rfl⟩ : syracuseStep 3254363 = 4881545) B4881545
theorem B3664055 : Blo 1445542 3664055 := bstep (se 1 (by rfl) ⟨2748041, by rfl⟩ : syracuseStep 3664055 = 5496083) B5496083
theorem B5495111 : Blo 1445542 5495111 := bstep (se 1 (by rfl) ⟨4121333, by rfl⟩ : syracuseStep 5495111 = 8242667) B8242667
theorem B2442703 : Blo 1445542 2442703 := bstep (se 1 (by rfl) ⟨1832027, by rfl⟩ : syracuseStep 2442703 = 3664055) B3664055
theorem B3663407 : Blo 1445542 3663407 := bstep (se 1 (by rfl) ⟨2747555, by rfl⟩ : syracuseStep 3663407 = 5495111) B5495111
theorem B18525347 : Blo 1445542 18525347 := bstep (se 1 (by rfl) ⟨13894010, by rfl⟩ : syracuseStep 18525347 = 27788021) B27788021
theorem B2168603 : Blo 1445542 2168603 := bstep (se 1 (by rfl) ⟨1626452, by rfl⟩ : syracuseStep 2168603 = 3252905) B3252905
theorem B2169575 : Blo 1445542 2169575 := bstep (se 1 (by rfl) ⟨1627181, by rfl⟩ : syracuseStep 2169575 = 3254363) B3254363
theorem B2442271 : Blo 1445542 2442271 := bstep (se 1 (by rfl) ⟨1831703, by rfl⟩ : syracuseStep 2442271 = 3663407) B3663407
theorem B1445735 : Blo 1445542 1445735 := bstep (se 1 (by rfl) ⟨1084301, by rfl⟩ : syracuseStep 1445735 = 2168603) B2168603
theorem B1446383 : Blo 1445542 1446383 := bstep (se 1 (by rfl) ⟨1084787, by rfl⟩ : syracuseStep 1446383 = 2169575) B2169575
theorem B3256937 : Blo 1445542 3256937 := bstep (se 2 (by rfl) ⟨1221351, by rfl⟩ : syracuseStep 3256937 = 2442703) B2442703
theorem B12350231 : Blo 1445542 12350231 := bstep (se 1 (by rfl) ⟨9262673, by rfl⟩ : syracuseStep 12350231 = 18525347) B18525347
theorem B2171291 : Blo 1445542 2171291 := bstep (se 1 (by rfl) ⟨1628468, by rfl⟩ : syracuseStep 2171291 = 3256937) B3256937
theorem B8233487 : Blo 1445542 8233487 := bstep (se 1 (by rfl) ⟨6175115, by rfl⟩ : syracuseStep 8233487 = 12350231) B12350231
theorem B3256361 : Blo 1445542 3256361 := bstep (se 2 (by rfl) ⟨1221135, by rfl⟩ : syracuseStep 3256361 = 2442271) B2442271
theorem B2170907 : Blo 1445542 2170907 := bstep (se 1 (by rfl) ⟨1628180, by rfl⟩ : syracuseStep 2170907 = 3256361) B3256361
theorem B5488991 : Blo 1445542 5488991 := bstep (se 1 (by rfl) ⟨4116743, by rfl⟩ : syracuseStep 5488991 = 8233487) B8233487
theorem B1447527 : Blo 1445542 1447527 := bstep (se 1 (by rfl) ⟨1085645, by rfl⟩ : syracuseStep 1447527 = 2171291) B2171291
theorem B1447271 : Blo 1445542 1447271 := bstep (se 1 (by rfl) ⟨1085453, by rfl⟩ : syracuseStep 1447271 = 2170907) B2170907
theorem B3659327 : Blo 1445542 3659327 := bstep (se 1 (by rfl) ⟨2744495, by rfl⟩ : syracuseStep 3659327 = 5488991) B5488991
theorem B2439551 : Blo 1445542 2439551 := bstep (se 1 (by rfl) ⟨1829663, by rfl⟩ : syracuseStep 2439551 = 3659327) B3659327
theorem B1626367 : Blo 1445542 1626367 := bstep (se 1 (by rfl) ⟨1219775, by rfl⟩ : syracuseStep 1626367 = 2439551) B2439551
theorem B2168489 : Blo 1445542 2168489 := bstep (se 2 (by rfl) ⟨813183, by rfl⟩ : syracuseStep 2168489 = 1626367) B1626367
theorem B1445659 : Blo 1445542 1445659 := bstep (se 1 (by rfl) ⟨1084244, by rfl⟩ : syracuseStep 1445659 = 2168489) B2168489

theorem C0 (j : ℕ) (h1 : 361385 ≤ j) (h2 : j ≤ 361884) : Blo 1445542 (4 * j + 3) := by
  interval_cases j
  · exact B1445543
  · exact B1445547
  · exact B1445551
  · exact B1445555
  · exact B1445559
  · exact B1445563
  · exact B1445567
  · exact B1445571
  · exact B1445575
  · exact B1445579
  · exact B1445583
  · exact B1445587
  · exact B1445591
  · exact B1445595
  · exact B1445599
  · exact B1445603
  · exact B1445607
  · exact B1445611
  · exact B1445615
  · exact B1445619
  · exact B1445623
  · exact B1445627
  · exact B1445631
  · exact B1445635
  · exact B1445639
  · exact B1445643
  · exact B1445647
  · exact B1445651
  · exact B1445655
  · exact B1445659
  · exact B1445663
  · exact B1445667
  · exact B1445671
  · exact B1445675
  · exact B1445679
  · exact B1445683
  · exact B1445687
  · exact B1445691
  · exact B1445695
  · exact B1445699
  · exact B1445703
  · exact B1445707
  · exact B1445711
  · exact B1445715
  · exact B1445719
  · exact B1445723
  · exact B1445727
  · exact B1445731
  · exact B1445735
  · exact B1445739
  · exact B1445743
  · exact B1445747
  · exact B1445751
  · exact B1445755
  · exact B1445759
  · exact B1445763
  · exact B1445767
  · exact B1445771
  · exact B1445775
  · exact B1445779
  · exact B1445783
  · exact B1445787
  · exact B1445791
  · exact B1445795
  · exact B1445799
  · exact B1445803
  · exact B1445807
  · exact B1445811
  · exact B1445815
  · exact B1445819
  · exact B1445823
  · exact B1445827
  · exact B1445831
  · exact B1445835
  · exact B1445839
  · exact B1445843
  · exact B1445847
  · exact B1445851
  · exact B1445855
  · exact B1445859
  · exact B1445863
  · exact B1445867
  · exact B1445871
  · exact B1445875
  · exact B1445879
  · exact B1445883
  · exact B1445887
  · exact B1445891
  · exact B1445895
  · exact B1445899
  · exact B1445903
  · exact B1445907
  · exact B1445911
  · exact B1445915
  · exact B1445919
  · exact B1445923
  · exact B1445927
  · exact B1445931
  · exact B1445935
  · exact B1445939
  · exact B1445943
  · exact B1445947
  · exact B1445951
  · exact B1445955
  · exact B1445959
  · exact B1445963
  · exact B1445967
  · exact B1445971
  · exact B1445975
  · exact B1445979
  · exact B1445983
  · exact B1445987
  · exact B1445991
  · exact B1445995
  · exact B1445999
  · exact B1446003
  · exact B1446007
  · exact B1446011
  · exact B1446015
  · exact B1446019
  · exact B1446023
  · exact B1446027
  · exact B1446031
  · exact B1446035
  · exact B1446039
  · exact B1446043
  · exact B1446047
  · exact B1446051
  · exact B1446055
  · exact B1446059
  · exact B1446063
  · exact B1446067
  · exact B1446071
  · exact B1446075
  · exact B1446079
  · exact B1446083
  · exact B1446087
  · exact B1446091
  · exact B1446095
  · exact B1446099
  · exact B1446103
  · exact B1446107
  · exact B1446111
  · exact B1446115
  · exact B1446119
  · exact B1446123
  · exact B1446127
  · exact B1446131
  · exact B1446135
  · exact B1446139
  · exact B1446143
  · exact B1446147
  · exact B1446151
  · exact B1446155
  · exact B1446159
  · exact B1446163
  · exact B1446167
  · exact B1446171
  · exact B1446175
  · exact B1446179
  · exact B1446183
  · exact B1446187
  · exact B1446191
  · exact B1446195
  · exact B1446199
  · exact B1446203
  · exact B1446207
  · exact B1446211
  · exact B1446215
  · exact B1446219
  · exact B1446223
  · exact B1446227
  · exact B1446231
  · exact B1446235
  · exact B1446239
  · exact B1446243
  · exact B1446247
  · exact B1446251
  · exact B1446255
  · exact B1446259
  · exact B1446263
  · exact B1446267
  · exact B1446271
  · exact B1446275
  · exact B1446279
  · exact B1446283
  · exact B1446287
  · exact B1446291
  · exact B1446295
  · exact B1446299
  · exact B1446303
  · exact B1446307
  · exact B1446311
  · exact B1446315
  · exact B1446319
  · exact B1446323
  · exact B1446327
  · exact B1446331
  · exact B1446335
  · exact B1446339
  · exact B1446343
  · exact B1446347
  · exact B1446351
  · exact B1446355
  · exact B1446359
  · exact B1446363
  · exact B1446367
  · exact B1446371
  · exact B1446375
  · exact B1446379
  · exact B1446383
  · exact B1446387
  · exact B1446391
  · exact B1446395
  · exact B1446399
  · exact B1446403
  · exact B1446407
  · exact B1446411
  · exact B1446415
  · exact B1446419
  · exact B1446423
  · exact B1446427
  · exact B1446431
  · exact B1446435
  · exact B1446439
  · exact B1446443
  · exact B1446447
  · exact B1446451
  · exact B1446455
  · exact B1446459
  · exact B1446463
  · exact B1446467
  · exact B1446471
  · exact B1446475
  · exact B1446479
  · exact B1446483
  · exact B1446487
  · exact B1446491
  · exact B1446495
  · exact B1446499
  · exact B1446503
  · exact B1446507
  · exact B1446511
  · exact B1446515
  · exact B1446519
  · exact B1446523
  · exact B1446527
  · exact B1446531
  · exact B1446535
  · exact B1446539
  · exact B1446543
  · exact B1446547
  · exact B1446551
  · exact B1446555
  · exact B1446559
  · exact B1446563
  · exact B1446567
  · exact B1446571
  · exact B1446575
  · exact B1446579
  · exact B1446583
  · exact B1446587
  · exact B1446591
  · exact B1446595
  · exact B1446599
  · exact B1446603
  · exact B1446607
  · exact B1446611
  · exact B1446615
  · exact B1446619
  · exact B1446623
  · exact B1446627
  · exact B1446631
  · exact B1446635
  · exact B1446639
  · exact B1446643
  · exact B1446647
  · exact B1446651
  · exact B1446655
  · exact B1446659
  · exact B1446663
  · exact B1446667
  · exact B1446671
  · exact B1446675
  · exact B1446679
  · exact B1446683
  · exact B1446687
  · exact B1446691
  · exact B1446695
  · exact B1446699
  · exact B1446703
  · exact B1446707
  · exact B1446711
  · exact B1446715
  · exact B1446719
  · exact B1446723
  · exact B1446727
  · exact B1446731
  · exact B1446735
  · exact B1446739
  · exact B1446743
  · exact B1446747
  · exact B1446751
  · exact B1446755
  · exact B1446759
  · exact B1446763
  · exact B1446767
  · exact B1446771
  · exact B1446775
  · exact B1446779
  · exact B1446783
  · exact B1446787
  · exact B1446791
  · exact B1446795
  · exact B1446799
  · exact B1446803
  · exact B1446807
  · exact B1446811
  · exact B1446815
  · exact B1446819
  · exact B1446823
  · exact B1446827
  · exact B1446831
  · exact B1446835
  · exact B1446839
  · exact B1446843
  · exact B1446847
  · exact B1446851
  · exact B1446855
  · exact B1446859
  · exact B1446863
  · exact B1446867
  · exact B1446871
  · exact B1446875
  · exact B1446879
  · exact B1446883
  · exact B1446887
  · exact B1446891
  · exact B1446895
  · exact B1446899
  · exact B1446903
  · exact B1446907
  · exact B1446911
  · exact B1446915
  · exact B1446919
  · exact B1446923
  · exact B1446927
  · exact B1446931
  · exact B1446935
  · exact B1446939
  · exact B1446943
  · exact B1446947
  · exact B1446951
  · exact B1446955
  · exact B1446959
  · exact B1446963
  · exact B1446967
  · exact B1446971
  · exact B1446975
  · exact B1446979
  · exact B1446983
  · exact B1446987
  · exact B1446991
  · exact B1446995
  · exact B1446999
  · exact B1447003
  · exact B1447007
  · exact B1447011
  · exact B1447015
  · exact B1447019
  · exact B1447023
  · exact B1447027
  · exact B1447031
  · exact B1447035
  · exact B1447039
  · exact B1447043
  · exact B1447047
  · exact B1447051
  · exact B1447055
  · exact B1447059
  · exact B1447063
  · exact B1447067
  · exact B1447071
  · exact B1447075
  · exact B1447079
  · exact B1447083
  · exact B1447087
  · exact B1447091
  · exact B1447095
  · exact B1447099
  · exact B1447103
  · exact B1447107
  · exact B1447111
  · exact B1447115
  · exact B1447119
  · exact B1447123
  · exact B1447127
  · exact B1447131
  · exact B1447135
  · exact B1447139
  · exact B1447143
  · exact B1447147
  · exact B1447151
  · exact B1447155
  · exact B1447159
  · exact B1447163
  · exact B1447167
  · exact B1447171
  · exact B1447175
  · exact B1447179
  · exact B1447183
  · exact B1447187
  · exact B1447191
  · exact B1447195
  · exact B1447199
  · exact B1447203
  · exact B1447207
  · exact B1447211
  · exact B1447215
  · exact B1447219
  · exact B1447223
  · exact B1447227
  · exact B1447231
  · exact B1447235
  · exact B1447239
  · exact B1447243
  · exact B1447247
  · exact B1447251
  · exact B1447255
  · exact B1447259
  · exact B1447263
  · exact B1447267
  · exact B1447271
  · exact B1447275
  · exact B1447279
  · exact B1447283
  · exact B1447287
  · exact B1447291
  · exact B1447295
  · exact B1447299
  · exact B1447303
  · exact B1447307
  · exact B1447311
  · exact B1447315
  · exact B1447319
  · exact B1447323
  · exact B1447327
  · exact B1447331
  · exact B1447335
  · exact B1447339
  · exact B1447343
  · exact B1447347
  · exact B1447351
  · exact B1447355
  · exact B1447359
  · exact B1447363
  · exact B1447367
  · exact B1447371
  · exact B1447375
  · exact B1447379
  · exact B1447383
  · exact B1447387
  · exact B1447391
  · exact B1447395
  · exact B1447399
  · exact B1447403
  · exact B1447407
  · exact B1447411
  · exact B1447415
  · exact B1447419
  · exact B1447423
  · exact B1447427
  · exact B1447431
  · exact B1447435
  · exact B1447439
  · exact B1447443
  · exact B1447447
  · exact B1447451
  · exact B1447455
  · exact B1447459
  · exact B1447463
  · exact B1447467
  · exact B1447471
  · exact B1447475
  · exact B1447479
  · exact B1447483
  · exact B1447487
  · exact B1447491
  · exact B1447495
  · exact B1447499
  · exact B1447503
  · exact B1447507
  · exact B1447511
  · exact B1447515
  · exact B1447519
  · exact B1447523
  · exact B1447527
  · exact B1447531
  · exact B1447535
  · exact B1447539

theorem solution (m : ℕ) (hlo : 1445542 ≤ m) (hhi : m ≤ 1447542) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 361385 ≤ j := by omega
    have hj2 : j ≤ 361884 := by omega
    have hb : Blo 1445542 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
