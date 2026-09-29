-- Prove2me | solution 1 for syracuse_descends_range_1680040_1682040
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:22:19.851982+00:00
-- url     : https://prove2.me/submissions/24bf1e54-32ae-46af-808a-fd230897d004

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


theorem B6381605 : Blo 1680040 6381605 := bbase (se 4 (by rfl) ⟨598275, by rfl⟩ : syracuseStep 6381605 = 1196551) (by norm_num)
theorem B4096061 : Blo 1680040 4096061 := bbase (se 3 (by rfl) ⟨768011, by rfl⟩ : syracuseStep 4096061 = 1536023) (by norm_num)
theorem B9085013 : Blo 1680040 9085013 := bbase (se 8 (by rfl) ⟨53232, by rfl⟩ : syracuseStep 9085013 = 106465) (by norm_num)
theorem B16162901 : Blo 1680040 16162901 := bbase (se 8 (by rfl) ⟨94704, by rfl⟩ : syracuseStep 16162901 = 189409) (by norm_num)
theorem B7184501 : Blo 1680040 7184501 := bbase (se 5 (by rfl) ⟨336773, by rfl⟩ : syracuseStep 7184501 = 673547) (by norm_num)
theorem B3833981 : Blo 1680040 3833981 := bbase (se 3 (by rfl) ⟨718871, by rfl⟩ : syracuseStep 3833981 = 1437743) (by norm_num)
theorem B1704073 : Blo 1680040 1704073 := bbase (se 2 (by rfl) ⟨639027, by rfl⟩ : syracuseStep 1704073 = 1278055) (by norm_num)
theorem B12116117 : Blo 1680040 12116117 := bbase (se 6 (by rfl) ⟨283971, by rfl⟩ : syracuseStep 12116117 = 567943) (by norm_num)
theorem B7176437 : Blo 1680040 7176437 := bbase (se 5 (by rfl) ⟨336395, by rfl⟩ : syracuseStep 7176437 = 672791) (by norm_num)
theorem B3588389 : Blo 1680040 3588389 := bbase (se 4 (by rfl) ⟨336411, by rfl⟩ : syracuseStep 3588389 = 672823) (by norm_num)
theorem B2392373 : Blo 1680040 2392373 := bbase (se 5 (by rfl) ⟨112142, by rfl⟩ : syracuseStep 2392373 = 224285) (by norm_num)
theorem B9208181 : Blo 1680040 9208181 := bbase (se 5 (by rfl) ⟨431633, by rfl⟩ : syracuseStep 9208181 = 863267) (by norm_num)
theorem B2392453 : Blo 1680040 2392453 := bbase (se 4 (by rfl) ⟨224292, by rfl⟩ : syracuseStep 2392453 = 448585) (by norm_num)
theorem B1794485 : Blo 1680040 1794485 := bbase (se 5 (by rfl) ⟨84116, by rfl⟩ : syracuseStep 1794485 = 168233) (by norm_num)
theorem B3637693 : Blo 1680040 3637693 := bbase (se 3 (by rfl) ⟨682067, by rfl⟩ : syracuseStep 3637693 = 1364135) (by norm_num)
theorem B6644213 : Blo 1680040 6644213 := bbase (se 5 (by rfl) ⟨311447, by rfl⟩ : syracuseStep 6644213 = 622895) (by norm_num)
theorem B2392573 : Blo 1680040 2392573 := bbase (se 3 (by rfl) ⟨448607, by rfl⟩ : syracuseStep 2392573 = 897215) (by norm_num)
theorem B3408437 : Blo 1680040 3408437 := bbase (se 5 (by rfl) ⟨159770, by rfl⟩ : syracuseStep 3408437 = 319541) (by norm_num)
theorem B3834437 : Blo 1680040 3834437 := bbase (se 4 (by rfl) ⟨359478, by rfl⟩ : syracuseStep 3834437 = 718957) (by norm_num)
theorem B138052181 : Blo 1680040 138052181 := bbase (se 8 (by rfl) ⟨808899, by rfl⟩ : syracuseStep 138052181 = 1617799) (by norm_num)
theorem B2392669 : Blo 1680040 2392669 := bbase (se 3 (by rfl) ⟨448625, by rfl⟩ : syracuseStep 2392669 = 897251) (by norm_num)
theorem B1794673 : Blo 1680040 1794673 := bbase (se 2 (by rfl) ⟨673002, by rfl⟩ : syracuseStep 1794673 = 1346005) (by norm_num)
theorem B2835101 : Blo 1680040 2835101 := bbase (se 3 (by rfl) ⟨531581, by rfl⟩ : syracuseStep 2835101 = 1063163) (by norm_num)
theorem B4670149 : Blo 1680040 4670149 := bbase (se 4 (by rfl) ⟨437826, by rfl⟩ : syracuseStep 4670149 = 875653) (by norm_num)
theorem B1704673 : Blo 1680040 1704673 := bbase (se 2 (by rfl) ⟨639252, by rfl⟩ : syracuseStep 1704673 = 1278505) (by norm_num)
theorem B7275253 : Blo 1680040 7275253 := bbase (se 5 (by rfl) ⟨341027, by rfl⟩ : syracuseStep 7275253 = 682055) (by norm_num)
theorem B9577237 : Blo 1680040 9577237 := bbase (se 6 (by rfl) ⟨224466, by rfl⟩ : syracuseStep 9577237 = 448933) (by norm_num)
theorem B2835229 : Blo 1680040 2835229 := bbase (se 3 (by rfl) ⟨531605, by rfl⟩ : syracuseStep 2835229 = 1063211) (by norm_num)
theorem B2876213 : Blo 1680040 2876213 := bbase (se 5 (by rfl) ⟨134822, by rfl⟩ : syracuseStep 2876213 = 269645) (by norm_num)
theorem B2835317 : Blo 1680040 2835317 := bbase (se 5 (by rfl) ⟨132905, by rfl⟩ : syracuseStep 2835317 = 265811) (by norm_num)
theorem B3277685 : Blo 1680040 3277685 := bbase (se 5 (by rfl) ⟨153641, by rfl⟩ : syracuseStep 3277685 = 307283) (by norm_num)
theorem B12944245 : Blo 1680040 12944245 := bbase (se 5 (by rfl) ⟨606761, by rfl⟩ : syracuseStep 12944245 = 1213523) (by norm_num)
theorem B5751685 : Blo 1680040 5751685 := bbase (se 4 (by rfl) ⟨539220, by rfl⟩ : syracuseStep 5751685 = 1078441) (by norm_num)
theorem B13624213 : Blo 1680040 13624213 := bbase (se 6 (by rfl) ⟨319317, by rfl⟩ : syracuseStep 13624213 = 638635) (by norm_num)
theorem B4252621 : Blo 1680040 4252621 := bbase (se 3 (by rfl) ⟨797366, by rfl⟩ : syracuseStep 4252621 = 1594733) (by norm_num)
theorem B3883997 : Blo 1680040 3883997 := bbase (se 3 (by rfl) ⟨728249, by rfl⟩ : syracuseStep 3883997 = 1456499) (by norm_num)
theorem B2835445 : Blo 1680040 2835445 := bbase (se 5 (by rfl) ⟨132911, by rfl⟩ : syracuseStep 2835445 = 265823) (by norm_num)
theorem B4252733 : Blo 1680040 4252733 := bbase (se 3 (by rfl) ⟨797387, by rfl⟩ : syracuseStep 4252733 = 1594775) (by norm_num)
theorem B2393165 : Blo 1680040 2393165 := bbase (se 3 (by rfl) ⟨448718, by rfl⟩ : syracuseStep 2393165 = 897437) (by norm_num)
theorem B2835533 : Blo 1680040 2835533 := bbase (se 3 (by rfl) ⟨531662, by rfl⟩ : syracuseStep 2835533 = 1063325) (by norm_num)
theorem B8512613 : Blo 1680040 8512613 := bbase (se 4 (by rfl) ⟨798057, by rfl⟩ : syracuseStep 8512613 = 1596115) (by norm_num)
theorem B3589277 : Blo 1680040 3589277 := bbase (se 3 (by rfl) ⟨672989, by rfl⟩ : syracuseStep 3589277 = 1345979) (by norm_num)
theorem B3884213 : Blo 1680040 3884213 := bbase (se 5 (by rfl) ⟨182072, by rfl⟩ : syracuseStep 3884213 = 364145) (by norm_num)
theorem B2835661 : Blo 1680040 2835661 := bbase (se 3 (by rfl) ⟨531686, by rfl⟩ : syracuseStep 2835661 = 1063373) (by norm_num)
theorem B12772565 : Blo 1680040 12772565 := bbase (se 7 (by rfl) ⟨149678, by rfl⟩ : syracuseStep 12772565 = 299357) (by norm_num)
theorem B4252925 : Blo 1680040 4252925 := bbase (se 3 (by rfl) ⟨797423, by rfl⟩ : syracuseStep 4252925 = 1594847) (by norm_num)
theorem B2835749 : Blo 1680040 2835749 := bbase (se 4 (by rfl) ⟨265851, by rfl⟩ : syracuseStep 2835749 = 531703) (by norm_num)
theorem B3589517 : Blo 1680040 3589517 := bbase (se 3 (by rfl) ⟨673034, by rfl⟩ : syracuseStep 3589517 = 1346069) (by norm_num)
theorem B2835877 : Blo 1680040 2835877 := bbase (se 4 (by rfl) ⟨265863, by rfl⟩ : syracuseStep 2835877 = 531727) (by norm_num)
theorem B1795493 : Blo 1680040 1795493 := bbase (se 4 (by rfl) ⟨168327, by rfl⟩ : syracuseStep 1795493 = 336655) (by norm_num)
theorem B2729413 : Blo 1680040 2729413 := bbase (se 4 (by rfl) ⟨255882, by rfl⟩ : syracuseStep 2729413 = 511765) (by norm_num)
theorem B10765781 : Blo 1680040 10765781 := bbase (se 7 (by rfl) ⟨126161, by rfl⟩ : syracuseStep 10765781 = 252323) (by norm_num)
theorem B36349397 : Blo 1680040 36349397 := bbase (se 7 (by rfl) ⟨425969, by rfl⟩ : syracuseStep 36349397 = 851939) (by norm_num)
theorem B58246613 : Blo 1680040 58246613 := bbase (se 7 (by rfl) ⟨682577, by rfl⟩ : syracuseStep 58246613 = 1365155) (by norm_num)
theorem B2876909 : Blo 1680040 2876909 := bbase (se 3 (by rfl) ⟨539420, by rfl⟩ : syracuseStep 2876909 = 1078841) (by norm_num)
theorem B2835965 : Blo 1680040 2835965 := bbase (se 3 (by rfl) ⟨531743, by rfl⟩ : syracuseStep 2835965 = 1063487) (by norm_num)
theorem B5670485 : Blo 1680040 5670485 := bbase (se 8 (by rfl) ⟨33225, by rfl⟩ : syracuseStep 5670485 = 66451) (by norm_num)
theorem B4253269 : Blo 1680040 4253269 := bbase (se 8 (by rfl) ⟨24921, by rfl⟩ : syracuseStep 4253269 = 49843) (by norm_num)
theorem B4785749 : Blo 1680040 4785749 := bbase (se 8 (by rfl) ⟨28041, by rfl⟩ : syracuseStep 4785749 = 56083) (by norm_num)
theorem B2156117 : Blo 1680040 2156117 := bbase (se 8 (by rfl) ⟨12633, by rfl⟩ : syracuseStep 2156117 = 25267) (by norm_num)
theorem B12764789 : Blo 1680040 12764789 := bbase (se 5 (by rfl) ⟨598349, by rfl⟩ : syracuseStep 12764789 = 1196699) (by norm_num)
theorem B2393717 : Blo 1680040 2393717 := bbase (se 5 (by rfl) ⟨112205, by rfl⟩ : syracuseStep 2393717 = 224411) (by norm_num)
theorem B2836093 : Blo 1680040 2836093 := bbase (se 3 (by rfl) ⟨531767, by rfl⟩ : syracuseStep 2836093 = 1063535) (by norm_num)
theorem B4253381 : Blo 1680040 4253381 := bbase (se 4 (by rfl) ⟨398754, by rfl⟩ : syracuseStep 4253381 = 797509) (by norm_num)
theorem B2836181 : Blo 1680040 2836181 := bbase (se 7 (by rfl) ⟨33236, by rfl⟩ : syracuseStep 2836181 = 66473) (by norm_num)
theorem B4040437 : Blo 1680040 4040437 := bbase (se 5 (by rfl) ⟨189395, by rfl⟩ : syracuseStep 4040437 = 378791) (by norm_num)
theorem B2836309 : Blo 1680040 2836309 := bbase (se 9 (by rfl) ⟨8309, by rfl⟩ : syracuseStep 2836309 = 16619) (by norm_num)
theorem B1795937 : Blo 1680040 1795937 := bbase (se 2 (by rfl) ⟨673476, by rfl⟩ : syracuseStep 1795937 = 1346953) (by norm_num)
theorem B4253573 : Blo 1680040 4253573 := bbase (se 4 (by rfl) ⟨398772, by rfl⟩ : syracuseStep 4253573 = 797545) (by norm_num)
theorem B3590021 : Blo 1680040 3590021 := bbase (se 4 (by rfl) ⟨336564, by rfl⟩ : syracuseStep 3590021 = 673129) (by norm_num)
theorem B3590029 : Blo 1680040 3590029 := bbase (se 3 (by rfl) ⟨673130, by rfl⟩ : syracuseStep 3590029 = 1346261) (by norm_num)
theorem B2836397 : Blo 1680040 2836397 := bbase (se 3 (by rfl) ⟨531824, by rfl⟩ : syracuseStep 2836397 = 1063649) (by norm_num)
theorem B7178213 : Blo 1680040 7178213 := bbase (se 4 (by rfl) ⟨672957, by rfl⟩ : syracuseStep 7178213 = 1345915) (by norm_num)
theorem B5670917 : Blo 1680040 5670917 := bbase (se 4 (by rfl) ⟨531648, by rfl⟩ : syracuseStep 5670917 = 1063297) (by norm_num)
theorem B2836525 : Blo 1680040 2836525 := bbase (se 3 (by rfl) ⟨531848, by rfl⟩ : syracuseStep 2836525 = 1063697) (by norm_num)
theorem B1796185 : Blo 1680040 1796185 := bbase (se 2 (by rfl) ⟨673569, by rfl⟩ : syracuseStep 1796185 = 1347139) (by norm_num)
theorem B6383717 : Blo 1680040 6383717 := bbase (se 4 (by rfl) ⟨598473, by rfl⟩ : syracuseStep 6383717 = 1196947) (by norm_num)
theorem B2836613 : Blo 1680040 2836613 := bbase (se 4 (by rfl) ⟨265932, by rfl⟩ : syracuseStep 2836613 = 531865) (by norm_num)
theorem B7178453 : Blo 1680040 7178453 := bbase (se 7 (by rfl) ⟨84122, by rfl⟩ : syracuseStep 7178453 = 168245) (by norm_num)
theorem B4253917 : Blo 1680040 4253917 := bbase (se 3 (by rfl) ⟨797609, by rfl⟩ : syracuseStep 4253917 = 1595219) (by norm_num)
theorem B2836741 : Blo 1680040 2836741 := bbase (se 4 (by rfl) ⟨265944, by rfl⟩ : syracuseStep 2836741 = 531889) (by norm_num)
theorem B6056213 : Blo 1680040 6056213 := bbase (se 6 (by rfl) ⟨141942, by rfl⟩ : syracuseStep 6056213 = 283885) (by norm_num)
theorem B4254029 : Blo 1680040 4254029 := bbase (se 3 (by rfl) ⟨797630, by rfl⟩ : syracuseStep 4254029 = 1595261) (by norm_num)
theorem B2836829 : Blo 1680040 2836829 := bbase (se 3 (by rfl) ⟨531905, by rfl⟩ : syracuseStep 2836829 = 1063811) (by norm_num)
theorem B4041053 : Blo 1680040 4041053 := bbase (se 3 (by rfl) ⟨757697, by rfl⟩ : syracuseStep 4041053 = 1515395) (by norm_num)
theorem B2394469 : Blo 1680040 2394469 := bbase (se 4 (by rfl) ⟨224481, by rfl⟩ : syracuseStep 2394469 = 448963) (by norm_num)
theorem B8513909 : Blo 1680040 8513909 := bbase (se 5 (by rfl) ⟨399089, by rfl⟩ : syracuseStep 8513909 = 798179) (by norm_num)
theorem B6384005 : Blo 1680040 6384005 := bbase (se 4 (by rfl) ⟨598500, by rfl⟩ : syracuseStep 6384005 = 1197001) (by norm_num)
theorem B5671349 : Blo 1680040 5671349 := bbase (se 5 (by rfl) ⟨265844, by rfl⟩ : syracuseStep 5671349 = 531689) (by norm_num)
theorem B12945845 : Blo 1680040 12945845 := bbase (se 5 (by rfl) ⟨606836, by rfl⟩ : syracuseStep 12945845 = 1213673) (by norm_num)
theorem B2836957 : Blo 1680040 2836957 := bbase (se 3 (by rfl) ⟨531929, by rfl⟩ : syracuseStep 2836957 = 1063859) (by norm_num)
theorem B4254221 : Blo 1680040 4254221 := bbase (se 3 (by rfl) ⟨797666, by rfl⟩ : syracuseStep 4254221 = 1595333) (by norm_num)
theorem B2837045 : Blo 1680040 2837045 := bbase (se 5 (by rfl) ⟨132986, by rfl⟩ : syracuseStep 2837045 = 265973) (by norm_num)
theorem B5384789 : Blo 1680040 5384789 := bbase (se 8 (by rfl) ⟨31551, by rfl⟩ : syracuseStep 5384789 = 63103) (by norm_num)
theorem B4041389 : Blo 1680040 4041389 := bbase (se 3 (by rfl) ⟨757760, by rfl⟩ : syracuseStep 4041389 = 1515521) (by norm_num)
theorem B2837173 : Blo 1680040 2837173 := bbase (se 5 (by rfl) ⟨132992, by rfl⟩ : syracuseStep 2837173 = 265985) (by norm_num)
theorem B9579221 : Blo 1680040 9579221 := bbase (se 7 (by rfl) ⟨112256, by rfl⟩ : syracuseStep 9579221 = 224513) (by norm_num)
theorem B12110581 : Blo 1680040 12110581 := bbase (se 5 (by rfl) ⟨567683, by rfl⟩ : syracuseStep 12110581 = 1135367) (by norm_num)
theorem B4786933 : Blo 1680040 4786933 := bbase (se 5 (by rfl) ⟨224387, by rfl⟩ : syracuseStep 4786933 = 448775) (by norm_num)
theorem B2837261 : Blo 1680040 2837261 := bbase (se 3 (by rfl) ⟨531986, by rfl⟩ : syracuseStep 2837261 = 1063973) (by norm_num)
theorem B8506133 : Blo 1680040 8506133 := bbase (se 6 (by rfl) ⟨199362, by rfl⟩ : syracuseStep 8506133 = 398725) (by norm_num)
theorem B3189557 : Blo 1680040 3189557 := bbase (se 5 (by rfl) ⟨149510, by rfl⟩ : syracuseStep 3189557 = 299021) (by norm_num)
theorem B8080181 : Blo 1680040 8080181 := bbase (se 5 (by rfl) ⟨378758, by rfl⟩ : syracuseStep 8080181 = 757517) (by norm_num)
theorem B5671781 : Blo 1680040 5671781 := bbase (se 4 (by rfl) ⟨531729, by rfl⟩ : syracuseStep 5671781 = 1063459) (by norm_num)
theorem B4254565 : Blo 1680040 4254565 := bbase (se 4 (by rfl) ⟨398865, by rfl⟩ : syracuseStep 4254565 = 797731) (by norm_num)
theorem B7670629 : Blo 1680040 7670629 := bbase (se 4 (by rfl) ⟨719121, by rfl⟩ : syracuseStep 7670629 = 1438243) (by norm_num)
theorem B2837389 : Blo 1680040 2837389 := bbase (se 3 (by rfl) ⟨532010, by rfl⟩ : syracuseStep 2837389 = 1064021) (by norm_num)
theorem B4787093 : Blo 1680040 4787093 := bbase (se 6 (by rfl) ⟨112197, by rfl⟩ : syracuseStep 4787093 = 224395) (by norm_num)
theorem B3189709 : Blo 1680040 3189709 := bbase (se 3 (by rfl) ⟨598070, by rfl⟩ : syracuseStep 3189709 = 1196141) (by norm_num)
theorem B3992525 : Blo 1680040 3992525 := bbase (se 3 (by rfl) ⟨748598, by rfl⟩ : syracuseStep 3992525 = 1497197) (by norm_num)
theorem B4254677 : Blo 1680040 4254677 := bbase (se 7 (by rfl) ⟨49859, by rfl⟩ : syracuseStep 4254677 = 99719) (by norm_num)
theorem B2157529 : Blo 1680040 2157529 := bbase (se 2 (by rfl) ⟨809073, by rfl⟩ : syracuseStep 2157529 = 1618147) (by norm_num)
theorem B2837477 : Blo 1680040 2837477 := bbase (se 4 (by rfl) ⟨266013, by rfl⟩ : syracuseStep 2837477 = 532027) (by norm_num)
theorem B3591157 : Blo 1680040 3591157 := bbase (se 5 (by rfl) ⟨168335, by rfl⟩ : syracuseStep 3591157 = 336671) (by norm_num)
theorem B8080373 : Blo 1680040 8080373 := bbase (se 5 (by rfl) ⟨378767, by rfl⟩ : syracuseStep 8080373 = 757535) (by norm_num)
theorem B14363669 : Blo 1680040 14363669 := bbase (se 6 (by rfl) ⟨336648, by rfl⟩ : syracuseStep 14363669 = 673297) (by norm_num)
theorem B2837605 : Blo 1680040 2837605 := bbase (se 4 (by rfl) ⟨266025, by rfl⟩ : syracuseStep 2837605 = 532051) (by norm_num)
theorem B4787333 : Blo 1680040 4787333 := bbase (se 4 (by rfl) ⟨448812, by rfl⟩ : syracuseStep 4787333 = 897625) (by norm_num)
theorem B4254869 : Blo 1680040 4254869 := bbase (se 6 (by rfl) ⟨99723, by rfl⟩ : syracuseStep 4254869 = 199447) (by norm_num)
theorem B6057125 : Blo 1680040 6057125 := bbase (se 4 (by rfl) ⟨567855, by rfl⟩ : syracuseStep 6057125 = 1135711) (by norm_num)
theorem B2837693 : Blo 1680040 2837693 := bbase (se 3 (by rfl) ⟨532067, by rfl⟩ : syracuseStep 2837693 = 1064135) (by norm_num)
theorem B3190013 : Blo 1680040 3190013 := bbase (se 3 (by rfl) ⟨598127, by rfl⟩ : syracuseStep 3190013 = 1196255) (by norm_num)
theorem B5672213 : Blo 1680040 5672213 := bbase (se 6 (by rfl) ⟨132942, by rfl⟩ : syracuseStep 5672213 = 265885) (by norm_num)
theorem B4312349 : Blo 1680040 4312349 := bbase (se 3 (by rfl) ⟨808565, by rfl⟩ : syracuseStep 4312349 = 1617131) (by norm_num)
theorem B2837821 : Blo 1680040 2837821 := bbase (se 3 (by rfl) ⟨532091, by rfl⟩ : syracuseStep 2837821 = 1064183) (by norm_num)
theorem B4787525 : Blo 1680040 4787525 := bbase (se 4 (by rfl) ⟨448830, by rfl⟩ : syracuseStep 4787525 = 897661) (by norm_num)
theorem B3591533 : Blo 1680040 3591533 := bbase (se 3 (by rfl) ⟨673412, by rfl⟩ : syracuseStep 3591533 = 1346825) (by norm_num)
theorem B2837909 : Blo 1680040 2837909 := bbase (se 6 (by rfl) ⟨66513, by rfl⟩ : syracuseStep 2837909 = 133027) (by norm_num)
theorem B5385685 : Blo 1680040 5385685 := bbase (se 7 (by rfl) ⟨63113, by rfl⟩ : syracuseStep 5385685 = 126227) (by norm_num)
theorem B4255213 : Blo 1680040 4255213 := bbase (se 3 (by rfl) ⟨797852, by rfl⟩ : syracuseStep 4255213 = 1595705) (by norm_num)
theorem B2838037 : Blo 1680040 2838037 := bbase (se 6 (by rfl) ⟨66516, by rfl⟩ : syracuseStep 2838037 = 133033) (by norm_num)
theorem B3780125 : Blo 1680040 3780125 := bbase (se 3 (by rfl) ⟨708773, by rfl⟩ : syracuseStep 3780125 = 1417547) (by norm_num)
theorem B2018849 : Blo 1680040 2018849 := bbase (se 2 (by rfl) ⟨757068, by rfl⟩ : syracuseStep 2018849 = 1514137) (by norm_num)
theorem B6385189 : Blo 1680040 6385189 := bbase (se 4 (by rfl) ⟨598611, by rfl⟩ : syracuseStep 6385189 = 1197223) (by norm_num)
theorem B4255325 : Blo 1680040 4255325 := bbase (se 3 (by rfl) ⟨797873, by rfl⟩ : syracuseStep 4255325 = 1595747) (by norm_num)
theorem B3780197 : Blo 1680040 3780197 := bbase (se 4 (by rfl) ⟨354393, by rfl⟩ : syracuseStep 3780197 = 708787) (by norm_num)
theorem B2838125 : Blo 1680040 2838125 := bbase (se 3 (by rfl) ⟨532148, by rfl⟩ : syracuseStep 2838125 = 1064297) (by norm_num)
theorem B8515205 : Blo 1680040 8515205 := bbase (se 4 (by rfl) ⟨798300, by rfl⟩ : syracuseStep 8515205 = 1596601) (by norm_num)
theorem B4918949 : Blo 1680040 4918949 := bbase (se 4 (by rfl) ⟨461151, by rfl⟩ : syracuseStep 4918949 = 922303) (by norm_num)
theorem B3780269 : Blo 1680040 3780269 := bbase (se 3 (by rfl) ⟨708800, by rfl⟩ : syracuseStep 3780269 = 1417601) (by norm_num)
theorem B5672645 : Blo 1680040 5672645 := bbase (se 4 (by rfl) ⟨531810, by rfl⟩ : syracuseStep 5672645 = 1063621) (by norm_num)
theorem B2019017 : Blo 1680040 2019017 := bbase (se 2 (by rfl) ⟨757131, by rfl⟩ : syracuseStep 2019017 = 1514263) (by norm_num)
theorem B2838253 : Blo 1680040 2838253 := bbase (se 3 (by rfl) ⟨532172, by rfl⟩ : syracuseStep 2838253 = 1064345) (by norm_num)
theorem B3780341 : Blo 1680040 3780341 := bbase (se 5 (by rfl) ⟨177203, by rfl⟩ : syracuseStep 3780341 = 354407) (by norm_num)
theorem B10776341 : Blo 1680040 10776341 := bbase (se 6 (by rfl) ⟨252570, by rfl⟩ : syracuseStep 10776341 = 505141) (by norm_num)
theorem B4255517 : Blo 1680040 4255517 := bbase (se 3 (by rfl) ⟨797909, by rfl⟩ : syracuseStep 4255517 = 1595819) (by norm_num)
theorem B6467381 : Blo 1680040 6467381 := bbase (se 5 (by rfl) ⟨303158, by rfl⟩ : syracuseStep 6467381 = 606317) (by norm_num)
theorem B3780413 : Blo 1680040 3780413 := bbase (se 3 (by rfl) ⟨708827, by rfl⟩ : syracuseStep 3780413 = 1417655) (by norm_num)
theorem B2838341 : Blo 1680040 2838341 := bbase (se 4 (by rfl) ⟨266094, by rfl⟩ : syracuseStep 2838341 = 532189) (by norm_num)
theorem B6385493 : Blo 1680040 6385493 := bbase (se 9 (by rfl) ⟨18707, by rfl⟩ : syracuseStep 6385493 = 37415) (by norm_num)
theorem B2273125 : Blo 1680040 2273125 := bbase (se 4 (by rfl) ⟨213105, by rfl⟩ : syracuseStep 2273125 = 426211) (by norm_num)
theorem B3780485 : Blo 1680040 3780485 := bbase (se 4 (by rfl) ⟨354420, by rfl⟩ : syracuseStep 3780485 = 708841) (by norm_num)
theorem B3780557 : Blo 1680040 3780557 := bbase (se 3 (by rfl) ⟨708854, by rfl⟩ : syracuseStep 3780557 = 1417709) (by norm_num)
theorem B3190765 : Blo 1680040 3190765 := bbase (se 3 (by rfl) ⟨598268, by rfl⟩ : syracuseStep 3190765 = 1196537) (by norm_num)
theorem B2019325 : Blo 1680040 2019325 := bbase (se 3 (by rfl) ⟨378623, by rfl⟩ : syracuseStep 2019325 = 757247) (by norm_num)
theorem B3780629 : Blo 1680040 3780629 := bbase (se 6 (by rfl) ⟨88608, by rfl⟩ : syracuseStep 3780629 = 177217) (by norm_num)
theorem B8507429 : Blo 1680040 8507429 := bbase (se 4 (by rfl) ⟨797571, by rfl⟩ : syracuseStep 8507429 = 1595143) (by norm_num)
theorem B3780701 : Blo 1680040 3780701 := bbase (se 3 (by rfl) ⟨708881, by rfl⟩ : syracuseStep 3780701 = 1417763) (by norm_num)
theorem B4853861 : Blo 1680040 4853861 := bbase (se 4 (by rfl) ⟨455049, by rfl⟩ : syracuseStep 4853861 = 910099) (by norm_num)
theorem B5673077 : Blo 1680040 5673077 := bbase (se 5 (by rfl) ⟨265925, by rfl⟩ : syracuseStep 5673077 = 531851) (by norm_num)
theorem B4255861 : Blo 1680040 4255861 := bbase (se 5 (by rfl) ⟨199493, by rfl⟩ : syracuseStep 4255861 = 398987) (by norm_num)
theorem B3190909 : Blo 1680040 3190909 := bbase (se 3 (by rfl) ⟨598295, by rfl⟩ : syracuseStep 3190909 = 1196591) (by norm_num)
theorem B8622229 : Blo 1680040 8622229 := bbase (se 6 (by rfl) ⟨202083, by rfl⟩ : syracuseStep 8622229 = 404167) (by norm_num)
theorem B3780773 : Blo 1680040 3780773 := bbase (se 4 (by rfl) ⟨354447, by rfl⟩ : syracuseStep 3780773 = 708895) (by norm_num)
theorem B2019541 : Blo 1680040 2019541 := bbase (se 7 (by rfl) ⟨23666, by rfl⟩ : syracuseStep 2019541 = 47333) (by norm_num)
theorem B10367189 : Blo 1680040 10367189 := bbase (se 7 (by rfl) ⟨121490, by rfl⟩ : syracuseStep 10367189 = 242981) (by norm_num)
theorem B4255973 : Blo 1680040 4255973 := bbase (se 4 (by rfl) ⟨398997, by rfl⟩ : syracuseStep 4255973 = 797995) (by norm_num)
theorem B3780845 : Blo 1680040 3780845 := bbase (se 3 (by rfl) ⟨708908, by rfl⟩ : syracuseStep 3780845 = 1417817) (by norm_num)
theorem B3191069 : Blo 1680040 3191069 := bbase (se 3 (by rfl) ⟨598325, by rfl⟩ : syracuseStep 3191069 = 1196651) (by norm_num)
theorem B4788517 : Blo 1680040 4788517 := bbase (se 4 (by rfl) ⟨448923, by rfl⟩ : syracuseStep 4788517 = 897847) (by norm_num)
theorem B3780917 : Blo 1680040 3780917 := bbase (se 5 (by rfl) ⟨177230, by rfl⟩ : syracuseStep 3780917 = 354461) (by norm_num)
theorem B2691389 : Blo 1680040 2691389 := bbase (se 3 (by rfl) ⟨504635, by rfl⟩ : syracuseStep 2691389 = 1009271) (by norm_num)
theorem B3780989 : Blo 1680040 3780989 := bbase (se 3 (by rfl) ⟨708935, by rfl⟩ : syracuseStep 3780989 = 1417871) (by norm_num)
theorem B4256165 : Blo 1680040 4256165 := bbase (se 4 (by rfl) ⟨399015, by rfl⟩ : syracuseStep 4256165 = 798031) (by norm_num)
theorem B3191213 : Blo 1680040 3191213 := bbase (se 3 (by rfl) ⟨598352, by rfl⟩ : syracuseStep 3191213 = 1196705) (by norm_num)
theorem B3781061 : Blo 1680040 3781061 := bbase (se 4 (by rfl) ⟨354474, by rfl⟩ : syracuseStep 3781061 = 708949) (by norm_num)
theorem B7180741 : Blo 1680040 7180741 := bbase (se 4 (by rfl) ⟨673194, by rfl⟩ : syracuseStep 7180741 = 1346389) (by norm_num)
theorem B2126341 : Blo 1680040 2126341 := bbase (se 4 (by rfl) ⟨199344, by rfl⟩ : syracuseStep 2126341 = 398689) (by norm_num)
theorem B3781133 : Blo 1680040 3781133 := bbase (se 3 (by rfl) ⟨708962, by rfl⟩ : syracuseStep 3781133 = 1417925) (by norm_num)
theorem B2019853 : Blo 1680040 2019853 := bbase (se 3 (by rfl) ⟨378722, by rfl⟩ : syracuseStep 2019853 = 757445) (by norm_num)
theorem B5673509 : Blo 1680040 5673509 := bbase (se 4 (by rfl) ⟨531891, by rfl⟩ : syracuseStep 5673509 = 1063783) (by norm_num)
theorem B3781205 : Blo 1680040 3781205 := bbase (se 8 (by rfl) ⟨22155, by rfl⟩ : syracuseStep 3781205 = 44311) (by norm_num)
theorem B3781277 : Blo 1680040 3781277 := bbase (se 3 (by rfl) ⟨708989, by rfl⟩ : syracuseStep 3781277 = 1417979) (by norm_num)
theorem B2126513 : Blo 1680040 2126513 := bbase (se 2 (by rfl) ⟨797442, by rfl⟩ : syracuseStep 2126513 = 1594885) (by norm_num)
theorem B3191501 : Blo 1680040 3191501 := bbase (se 3 (by rfl) ⟨598406, by rfl⟩ : syracuseStep 3191501 = 1196813) (by norm_num)
theorem B3781349 : Blo 1680040 3781349 := bbase (se 4 (by rfl) ⟨354501, by rfl⟩ : syracuseStep 3781349 = 709003) (by norm_num)
theorem B2126569 : Blo 1680040 2126569 := bbase (se 2 (by rfl) ⟨797463, by rfl⟩ : syracuseStep 2126569 = 1594927) (by norm_num)
theorem B4256509 : Blo 1680040 4256509 := bbase (se 3 (by rfl) ⟨798095, by rfl⟩ : syracuseStep 4256509 = 1596191) (by norm_num)
theorem B3781421 : Blo 1680040 3781421 := bbase (se 3 (by rfl) ⟨709016, by rfl⟩ : syracuseStep 3781421 = 1418033) (by norm_num)
theorem B4543285 : Blo 1680040 4543285 := bbase (se 5 (by rfl) ⟨212966, by rfl⟩ : syracuseStep 4543285 = 425933) (by norm_num)
theorem B2691901 : Blo 1680040 2691901 := bbase (se 3 (by rfl) ⟨504731, by rfl⟩ : syracuseStep 2691901 = 1009463) (by norm_num)
theorem B2126665 : Blo 1680040 2126665 := bbase (se 2 (by rfl) ⟨797499, by rfl⟩ : syracuseStep 2126665 = 1594999) (by norm_num)
theorem B3191653 : Blo 1680040 3191653 := bbase (se 4 (by rfl) ⟨299217, by rfl⟩ : syracuseStep 3191653 = 598435) (by norm_num)
theorem B4256621 : Blo 1680040 4256621 := bbase (se 3 (by rfl) ⟨798116, by rfl⟩ : syracuseStep 4256621 = 1596233) (by norm_num)
theorem B3781493 : Blo 1680040 3781493 := bbase (se 5 (by rfl) ⟨177257, by rfl⟩ : syracuseStep 3781493 = 354515) (by norm_num)
theorem B3781565 : Blo 1680040 3781565 := bbase (se 3 (by rfl) ⟨709043, by rfl⟩ : syracuseStep 3781565 = 1418087) (by norm_num)
theorem B5673941 : Blo 1680040 5673941 := bbase (se 7 (by rfl) ⟨66491, by rfl⟩ : syracuseStep 5673941 = 132983) (by norm_num)
theorem B6058981 : Blo 1680040 6058981 := bbase (se 4 (by rfl) ⟨568029, by rfl⟩ : syracuseStep 6058981 = 1136059) (by norm_num)
theorem B2126837 : Blo 1680040 2126837 := bbase (se 5 (by rfl) ⟨99695, by rfl⟩ : syracuseStep 2126837 = 199391) (by norm_num)
theorem B3781637 : Blo 1680040 3781637 := bbase (se 4 (by rfl) ⟨354528, by rfl⟩ : syracuseStep 3781637 = 709057) (by norm_num)
theorem B2520077 : Blo 1680040 2520077 := bbase (se 3 (by rfl) ⟨472514, by rfl⟩ : syracuseStep 2520077 = 945029) (by norm_num)
theorem B2520101 : Blo 1680040 2520101 := bbase (se 4 (by rfl) ⟨236259, by rfl⟩ : syracuseStep 2520101 = 472519) (by norm_num)
theorem B2126893 : Blo 1680040 2126893 := bbase (se 3 (by rfl) ⟨398792, by rfl⟩ : syracuseStep 2126893 = 797585) (by norm_num)
theorem B4256813 : Blo 1680040 4256813 := bbase (se 3 (by rfl) ⟨798152, by rfl⟩ : syracuseStep 4256813 = 1596305) (by norm_num)
theorem B2520125 : Blo 1680040 2520125 := bbase (se 3 (by rfl) ⟨472523, by rfl⟩ : syracuseStep 2520125 = 945047) (by norm_num)
theorem B3781709 : Blo 1680040 3781709 := bbase (se 3 (by rfl) ⟨709070, by rfl⟩ : syracuseStep 3781709 = 1418141) (by norm_num)
theorem B2520149 : Blo 1680040 2520149 := bbase (se 8 (by rfl) ⟨14766, by rfl⟩ : syracuseStep 2520149 = 29533) (by norm_num)
theorem B2520173 : Blo 1680040 2520173 := bbase (se 3 (by rfl) ⟨472532, by rfl⟩ : syracuseStep 2520173 = 945065) (by norm_num)
theorem B2520197 : Blo 1680040 2520197 := bbase (se 4 (by rfl) ⟨236268, by rfl⟩ : syracuseStep 2520197 = 472537) (by norm_num)
theorem B2126989 : Blo 1680040 2126989 := bbase (se 3 (by rfl) ⟨398810, by rfl⟩ : syracuseStep 2126989 = 797621) (by norm_num)
theorem B3781781 : Blo 1680040 3781781 := bbase (se 6 (by rfl) ⟨88635, by rfl⟩ : syracuseStep 3781781 = 177271) (by norm_num)
theorem B3191957 : Blo 1680040 3191957 := bbase (se 6 (by rfl) ⟨74811, by rfl⟩ : syracuseStep 3191957 = 149623) (by norm_num)
theorem B2520221 : Blo 1680040 2520221 := bbase (se 3 (by rfl) ⟨472541, by rfl⟩ : syracuseStep 2520221 = 945083) (by norm_num)
theorem B2520245 : Blo 1680040 2520245 := bbase (se 5 (by rfl) ⟨118136, by rfl⟩ : syracuseStep 2520245 = 236273) (by norm_num)
theorem B2520269 : Blo 1680040 2520269 := bbase (se 3 (by rfl) ⟨472550, by rfl⟩ : syracuseStep 2520269 = 945101) (by norm_num)
theorem B3781853 : Blo 1680040 3781853 := bbase (se 3 (by rfl) ⟨709097, by rfl⟩ : syracuseStep 3781853 = 1418195) (by norm_num)
theorem B2520293 : Blo 1680040 2520293 := bbase (se 4 (by rfl) ⟨236277, by rfl⟩ : syracuseStep 2520293 = 472555) (by norm_num)
theorem B2520317 : Blo 1680040 2520317 := bbase (se 3 (by rfl) ⟨472559, by rfl⟩ : syracuseStep 2520317 = 945119) (by norm_num)
theorem B2520341 : Blo 1680040 2520341 := bbase (se 6 (by rfl) ⟨59070, by rfl⟩ : syracuseStep 2520341 = 118141) (by norm_num)
theorem B3781925 : Blo 1680040 3781925 := bbase (se 4 (by rfl) ⟨354555, by rfl⟩ : syracuseStep 3781925 = 709111) (by norm_num)
theorem B2520365 : Blo 1680040 2520365 := bbase (se 3 (by rfl) ⟨472568, by rfl⟩ : syracuseStep 2520365 = 945137) (by norm_num)
theorem B8508725 : Blo 1680040 8508725 := bbase (se 5 (by rfl) ⟨398846, by rfl⟩ : syracuseStep 8508725 = 797693) (by norm_num)
theorem B2127161 : Blo 1680040 2127161 := bbase (se 2 (by rfl) ⟨797685, by rfl⟩ : syracuseStep 2127161 = 1595371) (by norm_num)
theorem B2520389 : Blo 1680040 2520389 := bbase (se 4 (by rfl) ⟨236286, by rfl⟩ : syracuseStep 2520389 = 472573) (by norm_num)
theorem B2520413 : Blo 1680040 2520413 := bbase (se 3 (by rfl) ⟨472577, by rfl⟩ : syracuseStep 2520413 = 945155) (by norm_num)
theorem B2692445 : Blo 1680040 2692445 := bbase (se 3 (by rfl) ⟨504833, by rfl⟩ : syracuseStep 2692445 = 1009667) (by norm_num)
theorem B3781997 : Blo 1680040 3781997 := bbase (se 3 (by rfl) ⟨709124, by rfl⟩ : syracuseStep 3781997 = 1418249) (by norm_num)
theorem B2127217 : Blo 1680040 2127217 := bbase (se 2 (by rfl) ⟨797706, by rfl⟩ : syracuseStep 2127217 = 1595413) (by norm_num)
theorem B2520437 : Blo 1680040 2520437 := bbase (se 5 (by rfl) ⟨118145, by rfl⟩ : syracuseStep 2520437 = 236291) (by norm_num)
theorem B4789621 : Blo 1680040 4789621 := bbase (se 5 (by rfl) ⟨224513, by rfl⟩ : syracuseStep 4789621 = 449027) (by norm_num)
theorem B5674373 : Blo 1680040 5674373 := bbase (se 4 (by rfl) ⟨531972, by rfl⟩ : syracuseStep 5674373 = 1063945) (by norm_num)
theorem B4257157 : Blo 1680040 4257157 := bbase (se 4 (by rfl) ⟨399108, by rfl⟩ : syracuseStep 4257157 = 798217) (by norm_num)
theorem B2520461 : Blo 1680040 2520461 := bbase (se 3 (by rfl) ⟨472586, by rfl⟩ : syracuseStep 2520461 = 945173) (by norm_num)
theorem B2520485 : Blo 1680040 2520485 := bbase (se 4 (by rfl) ⟨236295, by rfl⟩ : syracuseStep 2520485 = 472591) (by norm_num)
theorem B3782069 : Blo 1680040 3782069 := bbase (se 5 (by rfl) ⟨177284, by rfl⟩ : syracuseStep 3782069 = 354569) (by norm_num)
theorem B2520509 : Blo 1680040 2520509 := bbase (se 3 (by rfl) ⟨472595, by rfl⟩ : syracuseStep 2520509 = 945191) (by norm_num)
theorem B2127313 : Blo 1680040 2127313 := bbase (se 2 (by rfl) ⟨797742, by rfl⟩ : syracuseStep 2127313 = 1595485) (by norm_num)
theorem B2520533 : Blo 1680040 2520533 := bbase (se 7 (by rfl) ⟨29537, by rfl⟩ : syracuseStep 2520533 = 59075) (by norm_num)
theorem B2520557 : Blo 1680040 2520557 := bbase (se 3 (by rfl) ⟨472604, by rfl⟩ : syracuseStep 2520557 = 945209) (by norm_num)
theorem B4257269 : Blo 1680040 4257269 := bbase (se 5 (by rfl) ⟨199559, by rfl⟩ : syracuseStep 4257269 = 399119) (by norm_num)
theorem B3782141 : Blo 1680040 3782141 := bbase (se 3 (by rfl) ⟨709151, by rfl⟩ : syracuseStep 3782141 = 1418303) (by norm_num)
theorem B2520581 : Blo 1680040 2520581 := bbase (se 4 (by rfl) ⟨236304, by rfl⟩ : syracuseStep 2520581 = 472609) (by norm_num)
theorem B2520605 : Blo 1680040 2520605 := bbase (se 3 (by rfl) ⟨472613, by rfl⟩ : syracuseStep 2520605 = 945227) (by norm_num)
theorem B2520629 : Blo 1680040 2520629 := bbase (se 5 (by rfl) ⟨118154, by rfl⟩ : syracuseStep 2520629 = 236309) (by norm_num)
theorem B3782213 : Blo 1680040 3782213 := bbase (se 4 (by rfl) ⟨354582, by rfl⟩ : syracuseStep 3782213 = 709165) (by norm_num)
theorem B2520653 : Blo 1680040 2520653 := bbase (se 3 (by rfl) ⟨472622, by rfl⟩ : syracuseStep 2520653 = 945245) (by norm_num)
theorem B2520677 : Blo 1680040 2520677 := bbase (se 4 (by rfl) ⟨236313, by rfl⟩ : syracuseStep 2520677 = 472627) (by norm_num)
theorem B2520701 : Blo 1680040 2520701 := bbase (se 3 (by rfl) ⟨472631, by rfl⟩ : syracuseStep 2520701 = 945263) (by norm_num)
theorem B2127485 : Blo 1680040 2127485 := bbase (se 3 (by rfl) ⟨398903, by rfl⟩ : syracuseStep 2127485 = 797807) (by norm_num)
theorem B3782285 : Blo 1680040 3782285 := bbase (se 3 (by rfl) ⟨709178, by rfl⟩ : syracuseStep 3782285 = 1418357) (by norm_num)
theorem B2520725 : Blo 1680040 2520725 := bbase (se 6 (by rfl) ⟨59079, by rfl⟩ : syracuseStep 2520725 = 118159) (by norm_num)
theorem B3069613 : Blo 1680040 3069613 := bbase (se 3 (by rfl) ⟨575552, by rfl⟩ : syracuseStep 3069613 = 1151105) (by norm_num)
theorem B2520749 : Blo 1680040 2520749 := bbase (se 3 (by rfl) ⟨472640, by rfl⟩ : syracuseStep 2520749 = 945281) (by norm_num)
theorem B2127541 : Blo 1680040 2127541 := bbase (se 5 (by rfl) ⟨99728, by rfl⟩ : syracuseStep 2127541 = 199457) (by norm_num)
theorem B4257461 : Blo 1680040 4257461 := bbase (se 5 (by rfl) ⟨199568, by rfl⟩ : syracuseStep 4257461 = 399137) (by norm_num)
theorem B2520773 : Blo 1680040 2520773 := bbase (se 4 (by rfl) ⟨236322, by rfl⟩ : syracuseStep 2520773 = 472645) (by norm_num)
theorem B3782357 : Blo 1680040 3782357 := bbase (se 7 (by rfl) ⟨44324, by rfl⟩ : syracuseStep 3782357 = 88649) (by norm_num)
theorem B2520797 : Blo 1680040 2520797 := bbase (se 3 (by rfl) ⟨472649, by rfl⟩ : syracuseStep 2520797 = 945299) (by norm_num)
theorem B2520821 : Blo 1680040 2520821 := bbase (se 5 (by rfl) ⟨118163, by rfl⟩ : syracuseStep 2520821 = 236327) (by norm_num)
theorem B1890049 : Blo 1680040 1890049 := bbase (se 2 (by rfl) ⟨708768, by rfl⟩ : syracuseStep 1890049 = 1417537) (by norm_num)
theorem B2520845 : Blo 1680040 2520845 := bbase (se 3 (by rfl) ⟨472658, by rfl⟩ : syracuseStep 2520845 = 945317) (by norm_num)
theorem B2127637 : Blo 1680040 2127637 := bbase (se 6 (by rfl) ⟨49866, by rfl⟩ : syracuseStep 2127637 = 99733) (by norm_num)
theorem B3782429 : Blo 1680040 3782429 := bbase (se 3 (by rfl) ⟨709205, by rfl⟩ : syracuseStep 3782429 = 1418411) (by norm_num)
theorem B1890085 : Blo 1680040 1890085 := bbase (se 4 (by rfl) ⟨177195, by rfl⟩ : syracuseStep 1890085 = 354391) (by norm_num)
theorem B2520869 : Blo 1680040 2520869 := bbase (se 4 (by rfl) ⟨236331, by rfl⟩ : syracuseStep 2520869 = 472663) (by norm_num)
theorem B5674805 : Blo 1680040 5674805 := bbase (se 5 (by rfl) ⟨266006, by rfl⟩ : syracuseStep 5674805 = 532013) (by norm_num)
theorem B2520893 : Blo 1680040 2520893 := bbase (se 3 (by rfl) ⟨472667, by rfl⟩ : syracuseStep 2520893 = 945335) (by norm_num)
theorem B1890121 : Blo 1680040 1890121 := bbase (se 2 (by rfl) ⟨708795, by rfl⟩ : syracuseStep 1890121 = 1417591) (by norm_num)
theorem B2520917 : Blo 1680040 2520917 := bbase (se 9 (by rfl) ⟨7385, by rfl⟩ : syracuseStep 2520917 = 14771) (by norm_num)
theorem B3782501 : Blo 1680040 3782501 := bbase (se 4 (by rfl) ⟨354609, by rfl⟩ : syracuseStep 3782501 = 709219) (by norm_num)
theorem B1890157 : Blo 1680040 1890157 := bbase (se 3 (by rfl) ⟨354404, by rfl⟩ : syracuseStep 1890157 = 708809) (by norm_num)
theorem B2520941 : Blo 1680040 2520941 := bbase (se 3 (by rfl) ⟨472676, by rfl⟩ : syracuseStep 2520941 = 945353) (by norm_num)
theorem B6059893 : Blo 1680040 6059893 := bbase (se 5 (by rfl) ⟨284057, by rfl⟩ : syracuseStep 6059893 = 568115) (by norm_num)
theorem B2520965 : Blo 1680040 2520965 := bbase (se 4 (by rfl) ⟨236340, by rfl⟩ : syracuseStep 2520965 = 472681) (by norm_num)
theorem B2692997 : Blo 1680040 2692997 := bbase (se 4 (by rfl) ⟨252468, by rfl⟩ : syracuseStep 2692997 = 504937) (by norm_num)
theorem B3192709 : Blo 1680040 3192709 := bbase (se 4 (by rfl) ⟨299316, by rfl⟩ : syracuseStep 3192709 = 598633) (by norm_num)
theorem B1890193 : Blo 1680040 1890193 := bbase (se 2 (by rfl) ⟨708822, by rfl⟩ : syracuseStep 1890193 = 1417645) (by norm_num)
theorem B7182229 : Blo 1680040 7182229 := bbase (se 6 (by rfl) ⟨168333, by rfl⟩ : syracuseStep 7182229 = 336667) (by norm_num)
theorem B2520989 : Blo 1680040 2520989 := bbase (se 3 (by rfl) ⟨472685, by rfl⟩ : syracuseStep 2520989 = 945371) (by norm_num)
theorem B2693029 : Blo 1680040 2693029 := bbase (se 4 (by rfl) ⟨252471, by rfl⟩ : syracuseStep 2693029 = 504943) (by norm_num)
theorem B7182245 : Blo 1680040 7182245 := bbase (se 4 (by rfl) ⟨673335, by rfl⟩ : syracuseStep 7182245 = 1346671) (by norm_num)
theorem B3782573 : Blo 1680040 3782573 := bbase (se 3 (by rfl) ⟨709232, by rfl⟩ : syracuseStep 3782573 = 1418465) (by norm_num)
theorem B1890229 : Blo 1680040 1890229 := bbase (se 5 (by rfl) ⟨88604, by rfl⟩ : syracuseStep 1890229 = 177209) (by norm_num)
theorem B2521013 : Blo 1680040 2521013 := bbase (se 5 (by rfl) ⟨118172, by rfl⟩ : syracuseStep 2521013 = 236345) (by norm_num)
theorem B14366645 : Blo 1680040 14366645 := bbase (se 5 (by rfl) ⟨673436, by rfl⟩ : syracuseStep 14366645 = 1346873) (by norm_num)
theorem B2127809 : Blo 1680040 2127809 := bbase (se 2 (by rfl) ⟨797928, by rfl⟩ : syracuseStep 2127809 = 1595857) (by norm_num)
theorem B2521037 : Blo 1680040 2521037 := bbase (se 3 (by rfl) ⟨472694, by rfl⟩ : syracuseStep 2521037 = 945389) (by norm_num)
theorem B1890265 : Blo 1680040 1890265 := bbase (se 2 (by rfl) ⟨708849, by rfl⟩ : syracuseStep 1890265 = 1417699) (by norm_num)
theorem B2521061 : Blo 1680040 2521061 := bbase (se 4 (by rfl) ⟨236349, by rfl⟩ : syracuseStep 2521061 = 472699) (by norm_num)
theorem B2185201 : Blo 1680040 2185201 := bbase (se 2 (by rfl) ⟨819450, by rfl⟩ : syracuseStep 2185201 = 1638901) (by norm_num)
theorem B3782645 : Blo 1680040 3782645 := bbase (se 5 (by rfl) ⟨177311, by rfl⟩ : syracuseStep 3782645 = 354623) (by norm_num)
theorem B2127865 : Blo 1680040 2127865 := bbase (se 2 (by rfl) ⟨797949, by rfl⟩ : syracuseStep 2127865 = 1595899) (by norm_num)
theorem B2521085 : Blo 1680040 2521085 := bbase (se 3 (by rfl) ⟨472703, by rfl⟩ : syracuseStep 2521085 = 945407) (by norm_num)
theorem B1890301 : Blo 1680040 1890301 := bbase (se 3 (by rfl) ⟨354431, by rfl⟩ : syracuseStep 1890301 = 708863) (by norm_num)
theorem B2521109 : Blo 1680040 2521109 := bbase (se 6 (by rfl) ⟨59088, by rfl⟩ : syracuseStep 2521109 = 118177) (by norm_num)
theorem B3192853 : Blo 1680040 3192853 := bbase (se 6 (by rfl) ⟨74832, by rfl⟩ : syracuseStep 3192853 = 149665) (by norm_num)
theorem B1890337 : Blo 1680040 1890337 := bbase (se 2 (by rfl) ⟨708876, by rfl⟩ : syracuseStep 1890337 = 1417753) (by norm_num)
theorem B2521133 : Blo 1680040 2521133 := bbase (se 3 (by rfl) ⟨472712, by rfl⟩ : syracuseStep 2521133 = 945425) (by norm_num)
theorem B3782717 : Blo 1680040 3782717 := bbase (se 3 (by rfl) ⟨709259, by rfl⟩ : syracuseStep 3782717 = 1418519) (by norm_num)
theorem B1890373 : Blo 1680040 1890373 := bbase (se 4 (by rfl) ⟨177222, by rfl⟩ : syracuseStep 1890373 = 354445) (by norm_num)
theorem B2521157 : Blo 1680040 2521157 := bbase (se 4 (by rfl) ⟨236358, by rfl⟩ : syracuseStep 2521157 = 472717) (by norm_num)
theorem B2127961 : Blo 1680040 2127961 := bbase (se 2 (by rfl) ⟨797985, by rfl⟩ : syracuseStep 2127961 = 1595971) (by norm_num)
theorem B2521181 : Blo 1680040 2521181 := bbase (se 3 (by rfl) ⟨472721, by rfl⟩ : syracuseStep 2521181 = 945443) (by norm_num)
theorem B1890409 : Blo 1680040 1890409 := bbase (se 2 (by rfl) ⟨708903, by rfl⟩ : syracuseStep 1890409 = 1417807) (by norm_num)
theorem B2521205 : Blo 1680040 2521205 := bbase (se 5 (by rfl) ⟨118181, by rfl⟩ : syracuseStep 2521205 = 236363) (by norm_num)
theorem B3782789 : Blo 1680040 3782789 := bbase (se 4 (by rfl) ⟨354636, by rfl⟩ : syracuseStep 3782789 = 709273) (by norm_num)
theorem B1890445 : Blo 1680040 1890445 := bbase (se 3 (by rfl) ⟨354458, by rfl⟩ : syracuseStep 1890445 = 708917) (by norm_num)
theorem B2521229 : Blo 1680040 2521229 := bbase (se 3 (by rfl) ⟨472730, by rfl⟩ : syracuseStep 2521229 = 945461) (by norm_num)
theorem B2521253 : Blo 1680040 2521253 := bbase (se 4 (by rfl) ⟨236367, by rfl⟩ : syracuseStep 2521253 = 472735) (by norm_num)
theorem B1890481 : Blo 1680040 1890481 := bbase (se 2 (by rfl) ⟨708930, by rfl⟩ : syracuseStep 1890481 = 1417861) (by norm_num)
theorem B4544693 : Blo 1680040 4544693 := bbase (se 5 (by rfl) ⟨213032, by rfl⟩ : syracuseStep 4544693 = 426065) (by norm_num)
theorem B3193013 : Blo 1680040 3193013 := bbase (se 5 (by rfl) ⟨149672, by rfl⟩ : syracuseStep 3193013 = 299345) (by norm_num)
theorem B2521277 : Blo 1680040 2521277 := bbase (se 3 (by rfl) ⟨472739, by rfl⟩ : syracuseStep 2521277 = 945479) (by norm_num)
theorem B3029197 : Blo 1680040 3029197 := bbase (se 3 (by rfl) ⟨567974, by rfl⟩ : syracuseStep 3029197 = 1135949) (by norm_num)
theorem B3782861 : Blo 1680040 3782861 := bbase (se 3 (by rfl) ⟨709286, by rfl⟩ : syracuseStep 3782861 = 1418573) (by norm_num)
theorem B1890517 : Blo 1680040 1890517 := bbase (se 7 (by rfl) ⟨22154, by rfl⟩ : syracuseStep 1890517 = 44309) (by norm_num)
theorem B2521301 : Blo 1680040 2521301 := bbase (se 7 (by rfl) ⟨29546, by rfl⟩ : syracuseStep 2521301 = 59093) (by norm_num)
theorem B5675237 : Blo 1680040 5675237 := bbase (se 4 (by rfl) ⟨532053, by rfl⟩ : syracuseStep 5675237 = 1064107) (by norm_num)
theorem B2521325 : Blo 1680040 2521325 := bbase (se 3 (by rfl) ⟨472748, by rfl⟩ : syracuseStep 2521325 = 945497) (by norm_num)
theorem B3406069 : Blo 1680040 3406069 := bbase (se 5 (by rfl) ⟨159659, by rfl⟩ : syracuseStep 3406069 = 319319) (by norm_num)
theorem B4036853 : Blo 1680040 4036853 := bbase (se 5 (by rfl) ⟨189227, by rfl⟩ : syracuseStep 4036853 = 378455) (by norm_num)
theorem B1890553 : Blo 1680040 1890553 := bbase (se 2 (by rfl) ⟨708957, by rfl⟩ : syracuseStep 1890553 = 1417915) (by norm_num)
theorem B2521349 : Blo 1680040 2521349 := bbase (se 4 (by rfl) ⟨236376, by rfl⟩ : syracuseStep 2521349 = 472753) (by norm_num)
theorem B2128133 : Blo 1680040 2128133 := bbase (se 4 (by rfl) ⟨199512, by rfl⟩ : syracuseStep 2128133 = 399025) (by norm_num)
theorem B3782933 : Blo 1680040 3782933 := bbase (se 6 (by rfl) ⟨88662, by rfl⟩ : syracuseStep 3782933 = 177325) (by norm_num)
theorem B1890589 : Blo 1680040 1890589 := bbase (se 3 (by rfl) ⟨354485, by rfl⟩ : syracuseStep 1890589 = 708971) (by norm_num)
theorem B2521373 : Blo 1680040 2521373 := bbase (se 3 (by rfl) ⟨472757, by rfl⟩ : syracuseStep 2521373 = 945515) (by norm_num)
theorem B5388581 : Blo 1680040 5388581 := bbase (se 4 (by rfl) ⟨505179, by rfl⟩ : syracuseStep 5388581 = 1010359) (by norm_num)
theorem B6379829 : Blo 1680040 6379829 := bbase (se 5 (by rfl) ⟨299054, by rfl⟩ : syracuseStep 6379829 = 598109) (by norm_num)
theorem B2521397 : Blo 1680040 2521397 := bbase (se 5 (by rfl) ⟨118190, by rfl⟩ : syracuseStep 2521397 = 236381) (by norm_num)
theorem B2128189 : Blo 1680040 2128189 := bbase (se 3 (by rfl) ⟨399035, by rfl⟩ : syracuseStep 2128189 = 798071) (by norm_num)
theorem B1890625 : Blo 1680040 1890625 := bbase (se 2 (by rfl) ⟨708984, by rfl⟩ : syracuseStep 1890625 = 1417969) (by norm_num)
theorem B3193157 : Blo 1680040 3193157 := bbase (se 4 (by rfl) ⟨299358, by rfl⟩ : syracuseStep 3193157 = 598717) (by norm_num)
theorem B2521421 : Blo 1680040 2521421 := bbase (se 3 (by rfl) ⟨472766, by rfl⟩ : syracuseStep 2521421 = 945533) (by norm_num)
theorem B3783005 : Blo 1680040 3783005 := bbase (se 3 (by rfl) ⟨709313, by rfl⟩ : syracuseStep 3783005 = 1418627) (by norm_num)
theorem B1890661 : Blo 1680040 1890661 := bbase (se 4 (by rfl) ⟨177249, by rfl⟩ : syracuseStep 1890661 = 354499) (by norm_num)
theorem B2521445 : Blo 1680040 2521445 := bbase (se 4 (by rfl) ⟨236385, by rfl⟩ : syracuseStep 2521445 = 472771) (by norm_num)
theorem B2521469 : Blo 1680040 2521469 := bbase (se 3 (by rfl) ⟨472775, by rfl⟩ : syracuseStep 2521469 = 945551) (by norm_num)
theorem B1890697 : Blo 1680040 1890697 := bbase (se 2 (by rfl) ⟨709011, by rfl⟩ : syracuseStep 1890697 = 1418023) (by norm_num)
theorem B9083285 : Blo 1680040 9083285 := bbase (se 6 (by rfl) ⟨212889, by rfl⟩ : syracuseStep 9083285 = 425779) (by norm_num)
theorem B2521493 : Blo 1680040 2521493 := bbase (se 6 (by rfl) ⟨59097, by rfl⟩ : syracuseStep 2521493 = 118195) (by norm_num)
theorem B3029405 : Blo 1680040 3029405 := bbase (se 3 (by rfl) ⟨568013, by rfl⟩ : syracuseStep 3029405 = 1136027) (by norm_num)
theorem B2128285 : Blo 1680040 2128285 := bbase (se 3 (by rfl) ⟨399053, by rfl⟩ : syracuseStep 2128285 = 798107) (by norm_num)
theorem B3783077 : Blo 1680040 3783077 := bbase (se 4 (by rfl) ⟨354663, by rfl⟩ : syracuseStep 3783077 = 709327) (by norm_num)
theorem B1890733 : Blo 1680040 1890733 := bbase (se 3 (by rfl) ⟨354512, by rfl⟩ : syracuseStep 1890733 = 709025) (by norm_num)
theorem B2521517 : Blo 1680040 2521517 := bbase (se 3 (by rfl) ⟨472784, by rfl⟩ : syracuseStep 2521517 = 945569) (by norm_num)
theorem B2521541 : Blo 1680040 2521541 := bbase (se 4 (by rfl) ⟨236394, by rfl⟩ : syracuseStep 2521541 = 472789) (by norm_num)
theorem B1890769 : Blo 1680040 1890769 := bbase (se 2 (by rfl) ⟨709038, by rfl⟩ : syracuseStep 1890769 = 1418077) (by norm_num)
theorem B2521565 : Blo 1680040 2521565 := bbase (se 3 (by rfl) ⟨472793, by rfl⟩ : syracuseStep 2521565 = 945587) (by norm_num)
theorem B3791333 : Blo 1680040 3791333 := bbase (se 4 (by rfl) ⟨355437, by rfl⟩ : syracuseStep 3791333 = 710875) (by norm_num)
theorem B3783149 : Blo 1680040 3783149 := bbase (se 3 (by rfl) ⟨709340, by rfl⟩ : syracuseStep 3783149 = 1418681) (by norm_num)
theorem B1890805 : Blo 1680040 1890805 := bbase (se 5 (by rfl) ⟨88631, by rfl⟩ : syracuseStep 1890805 = 177263) (by norm_num)
theorem B2521589 : Blo 1680040 2521589 := bbase (se 5 (by rfl) ⟨118199, by rfl⟩ : syracuseStep 2521589 = 236399) (by norm_num)
theorem B2521613 : Blo 1680040 2521613 := bbase (se 3 (by rfl) ⟨472802, by rfl⟩ : syracuseStep 2521613 = 945605) (by norm_num)
theorem B21535253 : Blo 1680040 21535253 := bbase (se 6 (by rfl) ⟨504732, by rfl⟩ : syracuseStep 21535253 = 1009465) (by norm_num)
theorem B1890841 : Blo 1680040 1890841 := bbase (se 2 (by rfl) ⟨709065, by rfl⟩ : syracuseStep 1890841 = 1418131) (by norm_num)
theorem B2521637 : Blo 1680040 2521637 := bbase (se 4 (by rfl) ⟨236403, by rfl⟩ : syracuseStep 2521637 = 472807) (by norm_num)
theorem B3783221 : Blo 1680040 3783221 := bbase (se 5 (by rfl) ⟨177338, by rfl⟩ : syracuseStep 3783221 = 354677) (by norm_num)
theorem B1890877 : Blo 1680040 1890877 := bbase (se 3 (by rfl) ⟨354539, by rfl⟩ : syracuseStep 1890877 = 709079) (by norm_num)
theorem B2521661 : Blo 1680040 2521661 := bbase (se 3 (by rfl) ⟨472811, by rfl⟩ : syracuseStep 2521661 = 945623) (by norm_num)
theorem B8510021 : Blo 1680040 8510021 := bbase (se 4 (by rfl) ⟨797814, by rfl⟩ : syracuseStep 8510021 = 1595629) (by norm_num)
theorem B2128457 : Blo 1680040 2128457 := bbase (se 2 (by rfl) ⟨798171, by rfl⟩ : syracuseStep 2128457 = 1596343) (by norm_num)
theorem B6380117 : Blo 1680040 6380117 := bbase (se 8 (by rfl) ⟨37383, by rfl⟩ : syracuseStep 6380117 = 74767) (by norm_num)
theorem B2521685 : Blo 1680040 2521685 := bbase (se 8 (by rfl) ⟨14775, by rfl⟩ : syracuseStep 2521685 = 29551) (by norm_num)
theorem B1890913 : Blo 1680040 1890913 := bbase (se 2 (by rfl) ⟨709092, by rfl⟩ : syracuseStep 1890913 = 1418185) (by norm_num)
theorem B2521709 : Blo 1680040 2521709 := bbase (se 3 (by rfl) ⟨472820, by rfl⟩ : syracuseStep 2521709 = 945641) (by norm_num)
theorem B3783293 : Blo 1680040 3783293 := bbase (se 3 (by rfl) ⟨709367, by rfl⟩ : syracuseStep 3783293 = 1418735) (by norm_num)
theorem B2128513 : Blo 1680040 2128513 := bbase (se 2 (by rfl) ⟨798192, by rfl⟩ : syracuseStep 2128513 = 1596385) (by norm_num)
theorem B1890949 : Blo 1680040 1890949 := bbase (se 4 (by rfl) ⟨177276, by rfl⟩ : syracuseStep 1890949 = 354553) (by norm_num)
theorem B2521733 : Blo 1680040 2521733 := bbase (se 4 (by rfl) ⟨236412, by rfl⟩ : syracuseStep 2521733 = 472825) (by norm_num)
theorem B5675669 : Blo 1680040 5675669 := bbase (se 6 (by rfl) ⟨133023, by rfl⟩ : syracuseStep 5675669 = 266047) (by norm_num)
theorem B2521757 : Blo 1680040 2521757 := bbase (se 3 (by rfl) ⟨472829, by rfl⟩ : syracuseStep 2521757 = 945659) (by norm_num)
theorem B1890985 : Blo 1680040 1890985 := bbase (se 2 (by rfl) ⟨709119, by rfl⟩ : syracuseStep 1890985 = 1418239) (by norm_num)
theorem B2521781 : Blo 1680040 2521781 := bbase (se 5 (by rfl) ⟨118208, by rfl⟩ : syracuseStep 2521781 = 236417) (by norm_num)
theorem B3783365 : Blo 1680040 3783365 := bbase (se 4 (by rfl) ⟨354690, by rfl⟩ : syracuseStep 3783365 = 709381) (by norm_num)
theorem B1891021 : Blo 1680040 1891021 := bbase (se 3 (by rfl) ⟨354566, by rfl⟩ : syracuseStep 1891021 = 709133) (by norm_num)
theorem B2521805 : Blo 1680040 2521805 := bbase (se 3 (by rfl) ⟨472838, by rfl⟩ : syracuseStep 2521805 = 945677) (by norm_num)
theorem B2128609 : Blo 1680040 2128609 := bbase (se 2 (by rfl) ⟨798228, by rfl⟩ : syracuseStep 2128609 = 1596457) (by norm_num)
theorem B2521829 : Blo 1680040 2521829 := bbase (se 4 (by rfl) ⟨236421, by rfl⟩ : syracuseStep 2521829 = 472843) (by norm_num)
theorem B1891057 : Blo 1680040 1891057 := bbase (se 2 (by rfl) ⟨709146, by rfl⟩ : syracuseStep 1891057 = 1418293) (by norm_num)
theorem B2521853 : Blo 1680040 2521853 := bbase (se 3 (by rfl) ⟨472847, by rfl⟩ : syracuseStep 2521853 = 945695) (by norm_num)
theorem B3783437 : Blo 1680040 3783437 := bbase (se 3 (by rfl) ⟨709394, by rfl⟩ : syracuseStep 3783437 = 1418789) (by norm_num)
theorem B1891093 : Blo 1680040 1891093 := bbase (se 6 (by rfl) ⟨44322, by rfl⟩ : syracuseStep 1891093 = 88645) (by norm_num)
theorem B2521877 : Blo 1680040 2521877 := bbase (se 6 (by rfl) ⟨59106, by rfl⟩ : syracuseStep 2521877 = 118213) (by norm_num)
theorem B2521901 : Blo 1680040 2521901 := bbase (se 3 (by rfl) ⟨472856, by rfl⟩ : syracuseStep 2521901 = 945713) (by norm_num)
theorem B1891129 : Blo 1680040 1891129 := bbase (se 2 (by rfl) ⟨709173, by rfl⟩ : syracuseStep 1891129 = 1418347) (by norm_num)
theorem B2521925 : Blo 1680040 2521925 := bbase (se 4 (by rfl) ⟨236430, by rfl⟩ : syracuseStep 2521925 = 472861) (by norm_num)
theorem B2693957 : Blo 1680040 2693957 := bbase (se 4 (by rfl) ⟨252558, by rfl⟩ : syracuseStep 2693957 = 505117) (by norm_num)
theorem B8624981 : Blo 1680040 8624981 := bbase (se 9 (by rfl) ⟨25268, by rfl⟩ : syracuseStep 8624981 = 50537) (by norm_num)
theorem B3783509 : Blo 1680040 3783509 := bbase (se 9 (by rfl) ⟨11084, by rfl⟩ : syracuseStep 3783509 = 22169) (by norm_num)
theorem B1891165 : Blo 1680040 1891165 := bbase (se 3 (by rfl) ⟨354593, by rfl⟩ : syracuseStep 1891165 = 709187) (by norm_num)
theorem B2521949 : Blo 1680040 2521949 := bbase (se 3 (by rfl) ⟨472865, by rfl⟩ : syracuseStep 2521949 = 945731) (by norm_num)
theorem B2521973 : Blo 1680040 2521973 := bbase (se 5 (by rfl) ⟨118217, by rfl⟩ : syracuseStep 2521973 = 236435) (by norm_num)
theorem B1891201 : Blo 1680040 1891201 := bbase (se 2 (by rfl) ⟨709200, by rfl⟩ : syracuseStep 1891201 = 1418401) (by norm_num)
theorem B5110661 : Blo 1680040 5110661 := bbase (se 4 (by rfl) ⟨479124, by rfl⟩ : syracuseStep 5110661 = 958249) (by norm_num)
theorem B2521997 : Blo 1680040 2521997 := bbase (se 3 (by rfl) ⟨472874, by rfl⟩ : syracuseStep 2521997 = 945749) (by norm_num)
theorem B2128781 : Blo 1680040 2128781 := bbase (se 3 (by rfl) ⟨399146, by rfl⟩ : syracuseStep 2128781 = 798293) (by norm_num)
theorem B8076181 : Blo 1680040 8076181 := bbase (se 6 (by rfl) ⟨189285, by rfl⟩ : syracuseStep 8076181 = 378571) (by norm_num)
theorem B3783581 : Blo 1680040 3783581 := bbase (se 3 (by rfl) ⟨709421, by rfl⟩ : syracuseStep 3783581 = 1418843) (by norm_num)
theorem B1891237 : Blo 1680040 1891237 := bbase (se 4 (by rfl) ⟨177303, by rfl⟩ : syracuseStep 1891237 = 354607) (by norm_num)
theorem B2522021 : Blo 1680040 2522021 := bbase (se 4 (by rfl) ⟨236439, by rfl⟩ : syracuseStep 2522021 = 472879) (by norm_num)
theorem B2522045 : Blo 1680040 2522045 := bbase (se 3 (by rfl) ⟨472883, by rfl⟩ : syracuseStep 2522045 = 945767) (by norm_num)
theorem B1891273 : Blo 1680040 1891273 := bbase (se 2 (by rfl) ⟨709227, by rfl⟩ : syracuseStep 1891273 = 1418455) (by norm_num)
theorem B2522069 : Blo 1680040 2522069 := bbase (se 7 (by rfl) ⟨29555, by rfl⟩ : syracuseStep 2522069 = 59111) (by norm_num)
theorem B3783653 : Blo 1680040 3783653 := bbase (se 4 (by rfl) ⟨354717, by rfl⟩ : syracuseStep 3783653 = 709435) (by norm_num)
theorem B1891309 : Blo 1680040 1891309 := bbase (se 3 (by rfl) ⟨354620, by rfl⟩ : syracuseStep 1891309 = 709241) (by norm_num)
theorem B2522093 : Blo 1680040 2522093 := bbase (se 3 (by rfl) ⟨472892, by rfl⟩ : syracuseStep 2522093 = 945785) (by norm_num)
theorem B2522117 : Blo 1680040 2522117 := bbase (se 4 (by rfl) ⟨236448, by rfl⟩ : syracuseStep 2522117 = 472897) (by norm_num)
theorem B1891345 : Blo 1680040 1891345 := bbase (se 2 (by rfl) ⟨709254, by rfl⟩ : syracuseStep 1891345 = 1418509) (by norm_num)
theorem B7478293 : Blo 1680040 7478293 := bbase (se 6 (by rfl) ⟨175272, by rfl⟩ : syracuseStep 7478293 = 350545) (by norm_num)
theorem B2522141 : Blo 1680040 2522141 := bbase (se 3 (by rfl) ⟨472901, by rfl⟩ : syracuseStep 2522141 = 945803) (by norm_num)
theorem B3783725 : Blo 1680040 3783725 := bbase (se 3 (by rfl) ⟨709448, by rfl⟩ : syracuseStep 3783725 = 1418897) (by norm_num)
theorem B1891381 : Blo 1680040 1891381 := bbase (se 5 (by rfl) ⟨88658, by rfl⟩ : syracuseStep 1891381 = 177317) (by norm_num)
theorem B2522165 : Blo 1680040 2522165 := bbase (se 5 (by rfl) ⟨118226, by rfl⟩ : syracuseStep 2522165 = 236453) (by norm_num)
theorem B5676101 : Blo 1680040 5676101 := bbase (se 4 (by rfl) ⟨532134, by rfl⟩ : syracuseStep 5676101 = 1064269) (by norm_num)
theorem B2522189 : Blo 1680040 2522189 := bbase (se 3 (by rfl) ⟨472910, by rfl⟩ : syracuseStep 2522189 = 945821) (by norm_num)
theorem B1891417 : Blo 1680040 1891417 := bbase (se 2 (by rfl) ⟨709281, by rfl⟩ : syracuseStep 1891417 = 1418563) (by norm_num)
theorem B2522213 : Blo 1680040 2522213 := bbase (se 4 (by rfl) ⟨236457, by rfl⟩ : syracuseStep 2522213 = 472915) (by norm_num)
theorem B2104421 : Blo 1680040 2104421 := bbase (se 4 (by rfl) ⟨197289, by rfl⟩ : syracuseStep 2104421 = 394579) (by norm_num)
theorem B3783797 : Blo 1680040 3783797 := bbase (se 5 (by rfl) ⟨177365, by rfl⟩ : syracuseStep 3783797 = 354731) (by norm_num)
theorem B1891453 : Blo 1680040 1891453 := bbase (se 3 (by rfl) ⟨354647, by rfl⟩ : syracuseStep 1891453 = 709295) (by norm_num)
theorem B2522237 : Blo 1680040 2522237 := bbase (se 3 (by rfl) ⟨472919, by rfl⟩ : syracuseStep 2522237 = 945839) (by norm_num)
theorem B2522261 : Blo 1680040 2522261 := bbase (se 6 (by rfl) ⟨59115, by rfl⟩ : syracuseStep 2522261 = 118231) (by norm_num)
theorem B1891489 : Blo 1680040 1891489 := bbase (se 2 (by rfl) ⟨709308, by rfl⟩ : syracuseStep 1891489 = 1418617) (by norm_num)
theorem B2522285 : Blo 1680040 2522285 := bbase (se 3 (by rfl) ⟨472928, by rfl⟩ : syracuseStep 2522285 = 945857) (by norm_num)
theorem B3783869 : Blo 1680040 3783869 := bbase (se 3 (by rfl) ⟨709475, by rfl⟩ : syracuseStep 3783869 = 1418951) (by norm_num)
theorem B2555077 : Blo 1680040 2555077 := bbase (se 4 (by rfl) ⟨239538, by rfl⟩ : syracuseStep 2555077 = 479077) (by norm_num)
theorem B1891525 : Blo 1680040 1891525 := bbase (se 4 (by rfl) ⟨177330, by rfl⟩ : syracuseStep 1891525 = 354661) (by norm_num)
theorem B2522309 : Blo 1680040 2522309 := bbase (se 4 (by rfl) ⟨236466, by rfl⟩ : syracuseStep 2522309 = 472933) (by norm_num)
theorem B2522333 : Blo 1680040 2522333 := bbase (se 3 (by rfl) ⟨472937, by rfl⟩ : syracuseStep 2522333 = 945875) (by norm_num)
theorem B1891561 : Blo 1680040 1891561 := bbase (se 2 (by rfl) ⟨709335, by rfl⟩ : syracuseStep 1891561 = 1418671) (by norm_num)
theorem B2522357 : Blo 1680040 2522357 := bbase (se 5 (by rfl) ⟨118235, by rfl⟩ : syracuseStep 2522357 = 236471) (by norm_num)
theorem B3783941 : Blo 1680040 3783941 := bbase (se 4 (by rfl) ⟨354744, by rfl⟩ : syracuseStep 3783941 = 709489) (by norm_num)
theorem B1891597 : Blo 1680040 1891597 := bbase (se 3 (by rfl) ⟨354674, by rfl⟩ : syracuseStep 1891597 = 709349) (by norm_num)
theorem B2522381 : Blo 1680040 2522381 := bbase (se 3 (by rfl) ⟨472946, by rfl⟩ : syracuseStep 2522381 = 945893) (by norm_num)
theorem B2522405 : Blo 1680040 2522405 := bbase (se 4 (by rfl) ⟨236475, by rfl⟩ : syracuseStep 2522405 = 472951) (by norm_num)
theorem B1891633 : Blo 1680040 1891633 := bbase (se 2 (by rfl) ⟨709362, by rfl⟩ : syracuseStep 1891633 = 1418725) (by norm_num)
theorem B2522429 : Blo 1680040 2522429 := bbase (se 3 (by rfl) ⟨472955, by rfl⟩ : syracuseStep 2522429 = 945911) (by norm_num)
theorem B3784013 : Blo 1680040 3784013 := bbase (se 3 (by rfl) ⟨709502, by rfl⟩ : syracuseStep 3784013 = 1419005) (by norm_num)
theorem B1891669 : Blo 1680040 1891669 := bbase (se 11 (by rfl) ⟨1385, by rfl⟩ : syracuseStep 1891669 = 2771) (by norm_num)
theorem B2522453 : Blo 1680040 2522453 := bbase (se 11 (by rfl) ⟨1847, by rfl⟩ : syracuseStep 2522453 = 3695) (by norm_num)
theorem B2522477 : Blo 1680040 2522477 := bbase (se 3 (by rfl) ⟨472964, by rfl⟩ : syracuseStep 2522477 = 945929) (by norm_num)
theorem B1891705 : Blo 1680040 1891705 := bbase (se 2 (by rfl) ⟨709389, by rfl⟩ : syracuseStep 1891705 = 1418779) (by norm_num)
theorem B2522501 : Blo 1680040 2522501 := bbase (se 4 (by rfl) ⟨236484, by rfl⟩ : syracuseStep 2522501 = 472969) (by norm_num)
theorem B3784085 : Blo 1680040 3784085 := bbase (se 6 (by rfl) ⟨88689, by rfl⟩ : syracuseStep 3784085 = 177379) (by norm_num)
theorem B1891741 : Blo 1680040 1891741 := bbase (se 3 (by rfl) ⟨354701, by rfl⟩ : syracuseStep 1891741 = 709403) (by norm_num)
theorem B2522525 : Blo 1680040 2522525 := bbase (se 3 (by rfl) ⟨472973, by rfl⟩ : syracuseStep 2522525 = 945947) (by norm_num)
theorem B2522549 : Blo 1680040 2522549 := bbase (se 5 (by rfl) ⟨118244, by rfl⟩ : syracuseStep 2522549 = 236489) (by norm_num)
theorem B1891777 : Blo 1680040 1891777 := bbase (se 2 (by rfl) ⟨709416, by rfl⟩ : syracuseStep 1891777 = 1418833) (by norm_num)
theorem B2522573 : Blo 1680040 2522573 := bbase (se 3 (by rfl) ⟨472982, by rfl⟩ : syracuseStep 2522573 = 945965) (by norm_num)
theorem B3784157 : Blo 1680040 3784157 := bbase (se 3 (by rfl) ⟨709529, by rfl⟩ : syracuseStep 3784157 = 1419059) (by norm_num)
theorem B3071461 : Blo 1680040 3071461 := bbase (se 4 (by rfl) ⟨287949, by rfl⟩ : syracuseStep 3071461 = 575899) (by norm_num)
theorem B1891813 : Blo 1680040 1891813 := bbase (se 4 (by rfl) ⟨177357, by rfl⟩ : syracuseStep 1891813 = 354715) (by norm_num)
theorem B2522597 : Blo 1680040 2522597 := bbase (se 4 (by rfl) ⟨236493, by rfl⟩ : syracuseStep 2522597 = 472987) (by norm_num)
theorem B5676533 : Blo 1680040 5676533 := bbase (se 5 (by rfl) ⟨266087, by rfl⟩ : syracuseStep 5676533 = 532175) (by norm_num)
theorem B2522621 : Blo 1680040 2522621 := bbase (se 3 (by rfl) ⟨472991, by rfl⟩ : syracuseStep 2522621 = 945983) (by norm_num)
theorem B1891849 : Blo 1680040 1891849 := bbase (se 2 (by rfl) ⟨709443, by rfl⟩ : syracuseStep 1891849 = 1418887) (by norm_num)
theorem B2522645 : Blo 1680040 2522645 := bbase (se 6 (by rfl) ⟨59124, by rfl⟩ : syracuseStep 2522645 = 118249) (by norm_num)
theorem B3784229 : Blo 1680040 3784229 := bbase (se 4 (by rfl) ⟨354771, by rfl⟩ : syracuseStep 3784229 = 709543) (by norm_num)
theorem B1891885 : Blo 1680040 1891885 := bbase (se 3 (by rfl) ⟨354728, by rfl⟩ : syracuseStep 1891885 = 709457) (by norm_num)
theorem B2522669 : Blo 1680040 2522669 := bbase (se 3 (by rfl) ⟨473000, by rfl⟩ : syracuseStep 2522669 = 946001) (by norm_num)
theorem B2522693 : Blo 1680040 2522693 := bbase (se 4 (by rfl) ⟨236502, by rfl⟩ : syracuseStep 2522693 = 473005) (by norm_num)
theorem B1891921 : Blo 1680040 1891921 := bbase (se 2 (by rfl) ⟨709470, by rfl⟩ : syracuseStep 1891921 = 1418941) (by norm_num)
theorem B2522717 : Blo 1680040 2522717 := bbase (se 3 (by rfl) ⟨473009, by rfl⟩ : syracuseStep 2522717 = 946019) (by norm_num)
theorem B4038245 : Blo 1680040 4038245 := bbase (se 4 (by rfl) ⟨378585, by rfl⟩ : syracuseStep 4038245 = 757171) (by norm_num)
theorem B3784301 : Blo 1680040 3784301 := bbase (se 3 (by rfl) ⟨709556, by rfl⟩ : syracuseStep 3784301 = 1419113) (by norm_num)
theorem B9576053 : Blo 1680040 9576053 := bbase (se 5 (by rfl) ⟨448877, by rfl⟩ : syracuseStep 9576053 = 897755) (by norm_num)
theorem B1891957 : Blo 1680040 1891957 := bbase (se 5 (by rfl) ⟨88685, by rfl⟩ : syracuseStep 1891957 = 177371) (by norm_num)
theorem B2522741 : Blo 1680040 2522741 := bbase (se 5 (by rfl) ⟨118253, by rfl⟩ : syracuseStep 2522741 = 236507) (by norm_num)
theorem B2522765 : Blo 1680040 2522765 := bbase (se 3 (by rfl) ⟨473018, by rfl⟩ : syracuseStep 2522765 = 946037) (by norm_num)
theorem B1891993 : Blo 1680040 1891993 := bbase (se 2 (by rfl) ⟨709497, by rfl⟩ : syracuseStep 1891993 = 1418995) (by norm_num)
theorem B2522789 : Blo 1680040 2522789 := bbase (se 4 (by rfl) ⟨236511, by rfl⟩ : syracuseStep 2522789 = 473023) (by norm_num)
theorem B3784373 : Blo 1680040 3784373 := bbase (se 5 (by rfl) ⟨177392, by rfl⟩ : syracuseStep 3784373 = 354785) (by norm_num)
theorem B1892029 : Blo 1680040 1892029 := bbase (se 3 (by rfl) ⟨354755, by rfl⟩ : syracuseStep 1892029 = 709511) (by norm_num)
theorem B2522813 : Blo 1680040 2522813 := bbase (se 3 (by rfl) ⟨473027, by rfl⟩ : syracuseStep 2522813 = 946055) (by norm_num)
theorem B4038341 : Blo 1680040 4038341 := bbase (se 4 (by rfl) ⟨378594, by rfl⟩ : syracuseStep 4038341 = 757189) (by norm_num)
theorem B2522837 : Blo 1680040 2522837 := bbase (se 7 (by rfl) ⟨29564, by rfl⟩ : syracuseStep 2522837 = 59129) (by norm_num)
theorem B1892065 : Blo 1680040 1892065 := bbase (se 2 (by rfl) ⟨709524, by rfl⟩ : syracuseStep 1892065 = 1419049) (by norm_num)
theorem B2522861 : Blo 1680040 2522861 := bbase (se 3 (by rfl) ⟨473036, by rfl⟩ : syracuseStep 2522861 = 946073) (by norm_num)
theorem B6381301 : Blo 1680040 6381301 := bbase (se 5 (by rfl) ⟨299123, by rfl⟩ : syracuseStep 6381301 = 598247) (by norm_num)
theorem B3784445 : Blo 1680040 3784445 := bbase (se 3 (by rfl) ⟨709583, by rfl⟩ : syracuseStep 3784445 = 1419167) (by norm_num)
theorem B1892101 : Blo 1680040 1892101 := bbase (se 4 (by rfl) ⟨177384, by rfl⟩ : syracuseStep 1892101 = 354769) (by norm_num)
theorem B2522885 : Blo 1680040 2522885 := bbase (se 4 (by rfl) ⟨236520, by rfl⟩ : syracuseStep 2522885 = 473041) (by norm_num)
theorem B2522909 : Blo 1680040 2522909 := bbase (se 3 (by rfl) ⟨473045, by rfl⟩ : syracuseStep 2522909 = 946091) (by norm_num)
theorem B1892137 : Blo 1680040 1892137 := bbase (se 2 (by rfl) ⟨709551, by rfl⟩ : syracuseStep 1892137 = 1419103) (by norm_num)
theorem B2522933 : Blo 1680040 2522933 := bbase (se 5 (by rfl) ⟨118262, by rfl⟩ : syracuseStep 2522933 = 236525) (by norm_num)
theorem B3784517 : Blo 1680040 3784517 := bbase (se 4 (by rfl) ⟨354798, by rfl⟩ : syracuseStep 3784517 = 709597) (by norm_num)
theorem B1892173 : Blo 1680040 1892173 := bbase (se 3 (by rfl) ⟨354782, by rfl⟩ : syracuseStep 1892173 = 709565) (by norm_num)
theorem B2522957 : Blo 1680040 2522957 := bbase (se 3 (by rfl) ⟨473054, by rfl⟩ : syracuseStep 2522957 = 946109) (by norm_num)
theorem B8511317 : Blo 1680040 8511317 := bbase (se 9 (by rfl) ⟨24935, by rfl⟩ : syracuseStep 8511317 = 49871) (by norm_num)
theorem B20455253 : Blo 1680040 20455253 := bbase (se 9 (by rfl) ⟨59927, by rfl⟩ : syracuseStep 20455253 = 119855) (by norm_num)
theorem B2522981 : Blo 1680040 2522981 := bbase (se 4 (by rfl) ⟨236529, by rfl⟩ : syracuseStep 2522981 = 473059) (by norm_num)
theorem B1892209 : Blo 1680040 1892209 := bbase (se 2 (by rfl) ⟨709578, by rfl⟩ : syracuseStep 1892209 = 1419157) (by norm_num)
theorem B1703797 : Blo 1680040 1703797 := bbase (se 5 (by rfl) ⟨79865, by rfl⟩ : syracuseStep 1703797 = 159731) (by norm_num)
theorem B2523005 : Blo 1680040 2523005 := bbase (se 3 (by rfl) ⟨473063, by rfl⟩ : syracuseStep 2523005 = 946127) (by norm_num)
theorem B3784589 : Blo 1680040 3784589 := bbase (se 3 (by rfl) ⟨709610, by rfl⟩ : syracuseStep 3784589 = 1419221) (by norm_num)
theorem B1892245 : Blo 1680040 1892245 := bbase (se 6 (by rfl) ⟨44349, by rfl⟩ : syracuseStep 1892245 = 88699) (by norm_num)
theorem B2523029 : Blo 1680040 2523029 := bbase (se 6 (by rfl) ⟨59133, by rfl⟩ : syracuseStep 2523029 = 118267) (by norm_num)
theorem B2523053 : Blo 1680040 2523053 := bbase (se 3 (by rfl) ⟨473072, by rfl⟩ : syracuseStep 2523053 = 946145) (by norm_num)
theorem B1892281 : Blo 1680040 1892281 := bbase (se 2 (by rfl) ⟨709605, by rfl⟩ : syracuseStep 1892281 = 1419211) (by norm_num)
theorem B3235907 : Blo 1680040 3235907 := bstep (se 1 (by rfl) ⟨2426930, by rfl⟩ : syracuseStep 3235907 = 4853861) B4853861
theorem B2555987 : Blo 1680040 2555987 := bstep (se 1 (by rfl) ⟨1916990, by rfl⟩ : syracuseStep 2555987 = 3833981) B3833981
theorem B8077411 : Blo 1680040 8077411 := bstep (se 1 (by rfl) ⟨6058058, by rfl⟩ : syracuseStep 8077411 = 12116117) B12116117
theorem B4784291 : Blo 1680040 4784291 := bstep (se 1 (by rfl) ⟨3588218, by rfl⟩ : syracuseStep 4784291 = 7176437) B7176437
theorem B2392259 : Blo 1680040 2392259 := bstep (se 1 (by rfl) ⟨1794194, by rfl⟩ : syracuseStep 2392259 = 3588389) B3588389
theorem B6381773 : Blo 1680040 6381773 := bstep (se 3 (by rfl) ⟨1196582, by rfl⟩ : syracuseStep 6381773 = 2393165) B2393165
theorem B1794259 : Blo 1680040 1794259 := bstep (se 1 (by rfl) ⟨1345694, by rfl⟩ : syracuseStep 1794259 = 2691389) B2691389
theorem B5611789 : Blo 1680040 5611789 := bstep (se 3 (by rfl) ⟨1052210, by rfl⟩ : syracuseStep 5611789 = 2104421) B2104421
theorem B4038929 : Blo 1680040 4038929 := bstep (se 2 (by rfl) ⟨1514598, by rfl⟩ : syracuseStep 4038929 = 3029197) B3029197
theorem B1917475 : Blo 1680040 1917475 := bstep (se 1 (by rfl) ⟨1438106, by rfl⟩ : syracuseStep 1917475 = 2876213) B2876213
theorem B2835121 : Blo 1680040 2835121 := bstep (se 2 (by rfl) ⟨1063170, by rfl⟩ : syracuseStep 2835121 = 2126341) B2126341
theorem B1680051 : Blo 1680040 1680051 := bstep (se 1 (by rfl) ⟨1260038, by rfl⟩ : syracuseStep 1680051 = 2520077) B2520077
theorem B1680067 : Blo 1680040 1680067 := bstep (se 1 (by rfl) ⟨1260050, by rfl⟩ : syracuseStep 1680067 = 2520101) B2520101
theorem B1680083 : Blo 1680040 1680083 := bstep (se 1 (by rfl) ⟨1260062, by rfl⟩ : syracuseStep 1680083 = 2520125) B2520125
theorem B2835155 : Blo 1680040 2835155 := bstep (se 1 (by rfl) ⟨2126366, by rfl⟩ : syracuseStep 2835155 = 4252733) B4252733
theorem B1680099 : Blo 1680040 1680099 := bstep (se 1 (by rfl) ⟨1260074, by rfl⟩ : syracuseStep 1680099 = 2520149) B2520149
theorem B1680115 : Blo 1680040 1680115 := bstep (se 1 (by rfl) ⟨1260086, by rfl⟩ : syracuseStep 1680115 = 2520173) B2520173
theorem B1680131 : Blo 1680040 1680131 := bstep (se 1 (by rfl) ⟨1260098, by rfl⟩ : syracuseStep 1680131 = 2520197) B2520197
theorem B1680147 : Blo 1680040 1680147 := bstep (se 1 (by rfl) ⟨1260110, by rfl⟩ : syracuseStep 1680147 = 2520221) B2520221
theorem B2589475 : Blo 1680040 2589475 := bstep (se 1 (by rfl) ⟨1942106, by rfl⟩ : syracuseStep 2589475 = 3884213) B3884213
theorem B1680163 : Blo 1680040 1680163 := bstep (se 1 (by rfl) ⟨1260122, by rfl⟩ : syracuseStep 1680163 = 2520245) B2520245
theorem B1680179 : Blo 1680040 1680179 := bstep (se 1 (by rfl) ⟨1260134, by rfl⟩ : syracuseStep 1680179 = 2520269) B2520269
theorem B2392897 : Blo 1680040 2392897 := bstep (se 2 (by rfl) ⟨897336, by rfl⟩ : syracuseStep 2392897 = 1794673) B1794673
theorem B1680195 : Blo 1680040 1680195 := bstep (se 1 (by rfl) ⟨1260146, by rfl⟩ : syracuseStep 1680195 = 2520293) B2520293
theorem B2835283 : Blo 1680040 2835283 := bstep (se 1 (by rfl) ⟨2126462, by rfl⟩ : syracuseStep 2835283 = 4252925) B4252925
theorem B1680211 : Blo 1680040 1680211 := bstep (se 1 (by rfl) ⟨1260158, by rfl⟩ : syracuseStep 1680211 = 2520317) B2520317
theorem B1680227 : Blo 1680040 1680227 := bstep (se 1 (by rfl) ⟨1260170, by rfl⟩ : syracuseStep 1680227 = 2520341) B2520341
theorem B1680243 : Blo 1680040 1680243 := bstep (se 1 (by rfl) ⟨1260182, by rfl⟩ : syracuseStep 1680243 = 2520365) B2520365
theorem B1680259 : Blo 1680040 1680259 := bstep (se 1 (by rfl) ⟨1260194, by rfl⟩ : syracuseStep 1680259 = 2520389) B2520389
theorem B1680275 : Blo 1680040 1680275 := bstep (se 1 (by rfl) ⟨1260206, by rfl⟩ : syracuseStep 1680275 = 2520413) B2520413
theorem B1680291 : Blo 1680040 1680291 := bstep (se 1 (by rfl) ⟨1260218, by rfl⟩ : syracuseStep 1680291 = 2520437) B2520437
theorem B6226865 : Blo 1680040 6226865 := bstep (se 2 (by rfl) ⟨2335074, by rfl⟩ : syracuseStep 6226865 = 4670149) B4670149
theorem B1680307 : Blo 1680040 1680307 := bstep (se 1 (by rfl) ⟨1260230, by rfl⟩ : syracuseStep 1680307 = 2520461) B2520461
theorem B2393011 : Blo 1680040 2393011 := bstep (se 1 (by rfl) ⟨1794758, by rfl⟩ : syracuseStep 2393011 = 3589517) B3589517
theorem B1680323 : Blo 1680040 1680323 := bstep (se 1 (by rfl) ⟨1260242, by rfl⟩ : syracuseStep 1680323 = 2520485) B2520485
theorem B1680339 : Blo 1680040 1680339 := bstep (se 1 (by rfl) ⟨1260254, by rfl⟩ : syracuseStep 1680339 = 2520509) B2520509
theorem B2835425 : Blo 1680040 2835425 := bstep (se 2 (by rfl) ⟨1063284, by rfl⟩ : syracuseStep 2835425 = 2126569) B2126569
theorem B7177187 : Blo 1680040 7177187 := bstep (se 1 (by rfl) ⟨5382890, by rfl⟩ : syracuseStep 7177187 = 10765781) B10765781
theorem B1680355 : Blo 1680040 1680355 := bstep (se 1 (by rfl) ⟨1260266, by rfl⟩ : syracuseStep 1680355 = 2520533) B2520533
theorem B24232931 : Blo 1680040 24232931 := bstep (se 1 (by rfl) ⟨18174698, by rfl⟩ : syracuseStep 24232931 = 36349397) B36349397
theorem B38831075 : Blo 1680040 38831075 := bstep (se 1 (by rfl) ⟨29123306, by rfl⟩ : syracuseStep 38831075 = 58246613) B58246613
theorem B16147441 : Blo 1680040 16147441 := bstep (se 2 (by rfl) ⟨6055290, by rfl⟩ : syracuseStep 16147441 = 12110581) B12110581
theorem B9700337 : Blo 1680040 9700337 := bstep (se 2 (by rfl) ⟨3637626, by rfl⟩ : syracuseStep 9700337 = 7275253) B7275253
theorem B1680371 : Blo 1680040 1680371 := bstep (se 1 (by rfl) ⟨1260278, by rfl⟩ : syracuseStep 1680371 = 2520557) B2520557
theorem B6382577 : Blo 1680040 6382577 := bstep (se 2 (by rfl) ⟨2393466, by rfl⟩ : syracuseStep 6382577 = 4786933) B4786933
theorem B1680387 : Blo 1680040 1680387 := bstep (se 1 (by rfl) ⟨1260290, by rfl⟩ : syracuseStep 1680387 = 2520581) B2520581
theorem B1680403 : Blo 1680040 1680403 := bstep (se 1 (by rfl) ⟨1260302, by rfl⟩ : syracuseStep 1680403 = 2520605) B2520605
theorem B1680419 : Blo 1680040 1680419 := bstep (se 1 (by rfl) ⟨1260314, by rfl⟩ : syracuseStep 1680419 = 2520629) B2520629
theorem B1680435 : Blo 1680040 1680435 := bstep (se 1 (by rfl) ⟨1260326, by rfl⟩ : syracuseStep 1680435 = 2520653) B2520653
theorem B1680451 : Blo 1680040 1680451 := bstep (se 1 (by rfl) ⟨1260338, by rfl⟩ : syracuseStep 1680451 = 2520677) B2520677
theorem B3589201 : Blo 1680040 3589201 := bstep (se 2 (by rfl) ⟨1345950, by rfl⟩ : syracuseStep 3589201 = 2691901) B2691901
theorem B1680467 : Blo 1680040 1680467 := bstep (se 1 (by rfl) ⟨1260350, by rfl⟩ : syracuseStep 1680467 = 2520701) B2520701
theorem B8078413 : Blo 1680040 8078413 := bstep (se 3 (by rfl) ⟨1514702, by rfl⟩ : syracuseStep 8078413 = 3029405) B3029405
theorem B2835553 : Blo 1680040 2835553 := bstep (se 2 (by rfl) ⟨1063332, by rfl⟩ : syracuseStep 2835553 = 2126665) B2126665
theorem B1680483 : Blo 1680040 1680483 := bstep (se 1 (by rfl) ⟨1260362, by rfl⟩ : syracuseStep 1680483 = 2520725) B2520725
theorem B1680499 : Blo 1680040 1680499 := bstep (se 1 (by rfl) ⟨1260374, by rfl⟩ : syracuseStep 1680499 = 2520749) B2520749
theorem B2835587 : Blo 1680040 2835587 := bstep (se 1 (by rfl) ⟨2126690, by rfl⟩ : syracuseStep 2835587 = 4253381) B4253381
theorem B1680515 : Blo 1680040 1680515 := bstep (se 1 (by rfl) ⟨1260386, by rfl⟩ : syracuseStep 1680515 = 2520773) B2520773
theorem B4785293 : Blo 1680040 4785293 := bstep (se 3 (by rfl) ⟨897242, by rfl⟩ : syracuseStep 4785293 = 1794485) B1794485
theorem B1680531 : Blo 1680040 1680531 := bstep (se 1 (by rfl) ⟨1260398, by rfl⟩ : syracuseStep 1680531 = 2520797) B2520797
theorem B1680547 : Blo 1680040 1680547 := bstep (se 1 (by rfl) ⟨1260410, by rfl⟩ : syracuseStep 1680547 = 2520821) B2520821
theorem B7668913 : Blo 1680040 7668913 := bstep (se 2 (by rfl) ⟨2875842, by rfl⟩ : syracuseStep 7668913 = 5751685) B5751685
theorem B1680563 : Blo 1680040 1680563 := bstep (se 1 (by rfl) ⟨1260422, by rfl⟩ : syracuseStep 1680563 = 2520845) B2520845
theorem B1680579 : Blo 1680040 1680579 := bstep (se 1 (by rfl) ⟨1260434, by rfl⟩ : syracuseStep 1680579 = 2520869) B2520869
theorem B1680595 : Blo 1680040 1680595 := bstep (se 1 (by rfl) ⟨1260446, by rfl⟩ : syracuseStep 1680595 = 2520893) B2520893
theorem B1680611 : Blo 1680040 1680611 := bstep (se 1 (by rfl) ⟨1260458, by rfl⟩ : syracuseStep 1680611 = 2520917) B2520917
theorem B1680627 : Blo 1680040 1680627 := bstep (se 1 (by rfl) ⟨1260470, by rfl⟩ : syracuseStep 1680627 = 2520941) B2520941
theorem B2835715 : Blo 1680040 2835715 := bstep (se 1 (by rfl) ⟨2126786, by rfl⟩ : syracuseStep 2835715 = 4253573) B4253573
theorem B1680643 : Blo 1680040 1680643 := bstep (se 1 (by rfl) ⟨1260482, by rfl⟩ : syracuseStep 1680643 = 2520965) B2520965
theorem B1795331 : Blo 1680040 1795331 := bstep (se 1 (by rfl) ⟨1346498, by rfl⟩ : syracuseStep 1795331 = 2692997) B2692997
theorem B10110221 : Blo 1680040 10110221 := bstep (se 3 (by rfl) ⟨1895666, by rfl⟩ : syracuseStep 10110221 = 3791333) B3791333
theorem B5670161 : Blo 1680040 5670161 := bstep (se 2 (by rfl) ⟨2126310, by rfl⟩ : syracuseStep 5670161 = 4252621) B4252621
theorem B4252945 : Blo 1680040 4252945 := bstep (se 2 (by rfl) ⟨1594854, by rfl⟩ : syracuseStep 4252945 = 3189709) B3189709
theorem B1680659 : Blo 1680040 1680659 := bstep (se 1 (by rfl) ⟨1260494, by rfl⟩ : syracuseStep 1680659 = 2520989) B2520989
theorem B2876705 : Blo 1680040 2876705 := bstep (se 2 (by rfl) ⟨1078764, by rfl⟩ : syracuseStep 2876705 = 2157529) B2157529
theorem B1680675 : Blo 1680040 1680675 := bstep (se 1 (by rfl) ⟨1260506, by rfl⟩ : syracuseStep 1680675 = 2521013) B2521013
theorem B9577763 : Blo 1680040 9577763 := bstep (se 1 (by rfl) ⟨7183322, by rfl⟩ : syracuseStep 9577763 = 14366645) B14366645
theorem B1680691 : Blo 1680040 1680691 := bstep (se 1 (by rfl) ⟨1260518, by rfl⟩ : syracuseStep 1680691 = 2521037) B2521037
theorem B4785475 : Blo 1680040 4785475 := bstep (se 1 (by rfl) ⟨3589106, by rfl⟩ : syracuseStep 4785475 = 7178213) B7178213
theorem B1680707 : Blo 1680040 1680707 := bstep (se 1 (by rfl) ⟨1260530, by rfl⟩ : syracuseStep 1680707 = 2521061) B2521061
theorem B1680723 : Blo 1680040 1680723 := bstep (se 1 (by rfl) ⟨1260542, by rfl⟩ : syracuseStep 1680723 = 2521085) B2521085
theorem B1680739 : Blo 1680040 1680739 := bstep (se 1 (by rfl) ⟨1260554, by rfl⟩ : syracuseStep 1680739 = 2521109) B2521109
theorem B9971057 : Blo 1680040 9971057 := bstep (se 2 (by rfl) ⟨3739146, by rfl⟩ : syracuseStep 9971057 = 7478293) B7478293
theorem B1680755 : Blo 1680040 1680755 := bstep (se 1 (by rfl) ⟨1260566, by rfl⟩ : syracuseStep 1680755 = 2521133) B2521133
theorem B1680771 : Blo 1680040 1680771 := bstep (se 1 (by rfl) ⟨1260578, by rfl⟩ : syracuseStep 1680771 = 2521157) B2521157
theorem B2835857 : Blo 1680040 2835857 := bstep (se 2 (by rfl) ⟨1063446, by rfl⟩ : syracuseStep 2835857 = 2126893) B2126893
theorem B1680787 : Blo 1680040 1680787 := bstep (se 1 (by rfl) ⟨1260590, by rfl⟩ : syracuseStep 1680787 = 2521181) B2521181
theorem B1680803 : Blo 1680040 1680803 := bstep (se 1 (by rfl) ⟨1260602, by rfl⟩ : syracuseStep 1680803 = 2521205) B2521205
theorem B5383597 : Blo 1680040 5383597 := bstep (se 3 (by rfl) ⟨1009424, by rfl⟩ : syracuseStep 5383597 = 2018849) B2018849
theorem B1680819 : Blo 1680040 1680819 := bstep (se 1 (by rfl) ⟨1260614, by rfl⟩ : syracuseStep 1680819 = 2521229) B2521229
theorem B1680835 : Blo 1680040 1680835 := bstep (se 1 (by rfl) ⟨1260626, by rfl⟩ : syracuseStep 1680835 = 2521253) B2521253
theorem B1680851 : Blo 1680040 1680851 := bstep (se 1 (by rfl) ⟨1260638, by rfl⟩ : syracuseStep 1680851 = 2521277) B2521277
theorem B4785635 : Blo 1680040 4785635 := bstep (se 1 (by rfl) ⟨3589226, by rfl⟩ : syracuseStep 4785635 = 7178453) B7178453
theorem B1680867 : Blo 1680040 1680867 := bstep (se 1 (by rfl) ⟨1260650, by rfl⟩ : syracuseStep 1680867 = 2521301) B2521301
theorem B1680883 : Blo 1680040 1680883 := bstep (se 1 (by rfl) ⟨1260662, by rfl⟩ : syracuseStep 1680883 = 2521325) B2521325
theorem B1680899 : Blo 1680040 1680899 := bstep (se 1 (by rfl) ⟨1260674, by rfl⟩ : syracuseStep 1680899 = 2521349) B2521349
theorem B10225165 : Blo 1680040 10225165 := bstep (se 3 (by rfl) ⟨1917218, by rfl⟩ : syracuseStep 10225165 = 3834437) B3834437
theorem B2835985 : Blo 1680040 2835985 := bstep (se 2 (by rfl) ⟨1063494, by rfl⟩ : syracuseStep 2835985 = 2126989) B2126989
theorem B1680915 : Blo 1680040 1680915 := bstep (se 1 (by rfl) ⟨1260686, by rfl⟩ : syracuseStep 1680915 = 2521373) B2521373
theorem B4253219 : Blo 1680040 4253219 := bstep (se 1 (by rfl) ⟨3189914, by rfl⟩ : syracuseStep 4253219 = 6379829) B6379829
theorem B1680931 : Blo 1680040 1680931 := bstep (se 1 (by rfl) ⟨1260698, by rfl⟩ : syracuseStep 1680931 = 2521397) B2521397
theorem B2836019 : Blo 1680040 2836019 := bstep (se 1 (by rfl) ⟨2127014, by rfl⟩ : syracuseStep 2836019 = 4254029) B4254029
theorem B1680947 : Blo 1680040 1680947 := bstep (se 1 (by rfl) ⟨1260710, by rfl⟩ : syracuseStep 1680947 = 2521421) B2521421
theorem B1680963 : Blo 1680040 1680963 := bstep (se 1 (by rfl) ⟨1260722, by rfl⟩ : syracuseStep 1680963 = 2521445) B2521445
theorem B1680979 : Blo 1680040 1680979 := bstep (se 1 (by rfl) ⟨1260734, by rfl⟩ : syracuseStep 1680979 = 2521469) B2521469
theorem B6055523 : Blo 1680040 6055523 := bstep (se 1 (by rfl) ⟨4541642, by rfl⟩ : syracuseStep 6055523 = 9083285) B9083285
theorem B1680995 : Blo 1680040 1680995 := bstep (se 1 (by rfl) ⟨1260746, by rfl⟩ : syracuseStep 1680995 = 2521493) B2521493
theorem B1681011 : Blo 1680040 1681011 := bstep (se 1 (by rfl) ⟨1260758, by rfl⟩ : syracuseStep 1681011 = 2521517) B2521517
theorem B1681027 : Blo 1680040 1681027 := bstep (se 1 (by rfl) ⟨1260770, by rfl⟩ : syracuseStep 1681027 = 2521541) B2521541
theorem B6383245 : Blo 1680040 6383245 := bstep (se 3 (by rfl) ⟨1196858, by rfl⟩ : syracuseStep 6383245 = 2393717) B2393717
theorem B1681043 : Blo 1680040 1681043 := bstep (se 1 (by rfl) ⟨1260782, by rfl⟩ : syracuseStep 1681043 = 2521565) B2521565
theorem B1681059 : Blo 1680040 1681059 := bstep (se 1 (by rfl) ⟨1260794, by rfl⟩ : syracuseStep 1681059 = 2521589) B2521589
theorem B2836147 : Blo 1680040 2836147 := bstep (se 1 (by rfl) ⟨2127110, by rfl⟩ : syracuseStep 2836147 = 4254221) B4254221
theorem B1681075 : Blo 1680040 1681075 := bstep (se 1 (by rfl) ⟨1260806, by rfl⟩ : syracuseStep 1681075 = 2521613) B2521613
theorem B1681091 : Blo 1680040 1681091 := bstep (se 1 (by rfl) ⟨1260818, by rfl⟩ : syracuseStep 1681091 = 2521637) B2521637
theorem B1681107 : Blo 1680040 1681107 := bstep (se 1 (by rfl) ⟨1260830, by rfl⟩ : syracuseStep 1681107 = 2521661) B2521661
theorem B4253411 : Blo 1680040 4253411 := bstep (se 1 (by rfl) ⟨3190058, by rfl⟩ : syracuseStep 4253411 = 6380117) B6380117
theorem B3589859 : Blo 1680040 3589859 := bstep (se 1 (by rfl) ⟨2692394, by rfl⟩ : syracuseStep 3589859 = 5384789) B5384789
theorem B1681123 : Blo 1680040 1681123 := bstep (se 1 (by rfl) ⟨1260842, by rfl⟩ : syracuseStep 1681123 = 2521685) B2521685
theorem B1681139 : Blo 1680040 1681139 := bstep (se 1 (by rfl) ⟨1260854, by rfl⟩ : syracuseStep 1681139 = 2521709) B2521709
theorem B1681155 : Blo 1680040 1681155 := bstep (se 1 (by rfl) ⟨1260866, by rfl⟩ : syracuseStep 1681155 = 2521733) B2521733
theorem B1681171 : Blo 1680040 1681171 := bstep (se 1 (by rfl) ⟨1260878, by rfl⟩ : syracuseStep 1681171 = 2521757) B2521757
theorem B1681187 : Blo 1680040 1681187 := bstep (se 1 (by rfl) ⟨1260890, by rfl⟩ : syracuseStep 1681187 = 2521781) B2521781
theorem B5670701 : Blo 1680040 5670701 := bstep (se 3 (by rfl) ⟨1063256, by rfl⟩ : syracuseStep 5670701 = 2126513) B2126513
theorem B1681203 : Blo 1680040 1681203 := bstep (se 1 (by rfl) ⟨1260902, by rfl⟩ : syracuseStep 1681203 = 2521805) B2521805
theorem B2836289 : Blo 1680040 2836289 := bstep (se 2 (by rfl) ⟨1063608, by rfl⟩ : syracuseStep 2836289 = 2127217) B2127217
theorem B1681219 : Blo 1680040 1681219 := bstep (se 1 (by rfl) ⟨1260914, by rfl⟩ : syracuseStep 1681219 = 2521829) B2521829
theorem B1681235 : Blo 1680040 1681235 := bstep (se 1 (by rfl) ⟨1260926, by rfl⟩ : syracuseStep 1681235 = 2521853) B2521853
theorem B5670755 : Blo 1680040 5670755 := bstep (se 1 (by rfl) ⟨4253066, by rfl⟩ : syracuseStep 5670755 = 8506133) B8506133
theorem B1681251 : Blo 1680040 1681251 := bstep (se 1 (by rfl) ⟨1260938, by rfl⟩ : syracuseStep 1681251 = 2521877) B2521877
theorem B5384045 : Blo 1680040 5384045 := bstep (se 3 (by rfl) ⟨1009508, by rfl⟩ : syracuseStep 5384045 = 2019017) B2019017
theorem B1681267 : Blo 1680040 1681267 := bstep (se 1 (by rfl) ⟨1260950, by rfl⟩ : syracuseStep 1681267 = 2521901) B2521901
theorem B1681283 : Blo 1680040 1681283 := bstep (se 1 (by rfl) ⟨1260962, by rfl⟩ : syracuseStep 1681283 = 2521925) B2521925
theorem B1681299 : Blo 1680040 1681299 := bstep (se 1 (by rfl) ⟨1260974, by rfl⟩ : syracuseStep 1681299 = 2521949) B2521949
theorem B1681315 : Blo 1680040 1681315 := bstep (se 1 (by rfl) ⟨1260986, by rfl⟩ : syracuseStep 1681315 = 2521973) B2521973
theorem B3639217 : Blo 1680040 3639217 := bstep (se 2 (by rfl) ⟨1364706, by rfl⟩ : syracuseStep 3639217 = 2729413) B2729413
theorem B1681331 : Blo 1680040 1681331 := bstep (se 1 (by rfl) ⟨1260998, by rfl⟩ : syracuseStep 1681331 = 2521997) B2521997
theorem B2836417 : Blo 1680040 2836417 := bstep (se 2 (by rfl) ⟨1063656, by rfl⟩ : syracuseStep 2836417 = 2127313) B2127313
theorem B1681347 : Blo 1680040 1681347 := bstep (se 1 (by rfl) ⟨1261010, by rfl⟩ : syracuseStep 1681347 = 2522021) B2522021
theorem B9086917 : Blo 1680040 9086917 := bstep (se 4 (by rfl) ⟨851898, by rfl⟩ : syracuseStep 9086917 = 1703797) B1703797
theorem B1681363 : Blo 1680040 1681363 := bstep (se 1 (by rfl) ⟨1261022, by rfl⟩ : syracuseStep 1681363 = 2522045) B2522045
theorem B2836451 : Blo 1680040 2836451 := bstep (se 1 (by rfl) ⟨2127338, by rfl⟩ : syracuseStep 2836451 = 4254677) B4254677
theorem B1681379 : Blo 1680040 1681379 := bstep (se 1 (by rfl) ⟨1261034, by rfl⟩ : syracuseStep 1681379 = 2522069) B2522069
theorem B1681395 : Blo 1680040 1681395 := bstep (se 1 (by rfl) ⟨1261046, by rfl⟩ : syracuseStep 1681395 = 2522093) B2522093
theorem B1681411 : Blo 1680040 1681411 := bstep (se 1 (by rfl) ⟨1261058, by rfl⟩ : syracuseStep 1681411 = 2522117) B2522117
theorem B1681427 : Blo 1680040 1681427 := bstep (se 1 (by rfl) ⟨1261070, by rfl⟩ : syracuseStep 1681427 = 2522141) B2522141
theorem B1681443 : Blo 1680040 1681443 := bstep (se 1 (by rfl) ⟨1261082, by rfl⟩ : syracuseStep 1681443 = 2522165) B2522165
theorem B8513585 : Blo 1680040 8513585 := bstep (se 2 (by rfl) ⟨3192594, by rfl⟩ : syracuseStep 8513585 = 6385189) B6385189
theorem B1681459 : Blo 1680040 1681459 := bstep (se 1 (by rfl) ⟨1261094, by rfl⟩ : syracuseStep 1681459 = 2522189) B2522189
theorem B1681475 : Blo 1680040 1681475 := bstep (se 1 (by rfl) ⟨1261106, by rfl⟩ : syracuseStep 1681475 = 2522213) B2522213
theorem B1681491 : Blo 1680040 1681491 := bstep (se 1 (by rfl) ⟨1261118, by rfl⟩ : syracuseStep 1681491 = 2522237) B2522237
theorem B2836579 : Blo 1680040 2836579 := bstep (se 1 (by rfl) ⟨2127434, by rfl⟩ : syracuseStep 2836579 = 4254869) B4254869
theorem B1681507 : Blo 1680040 1681507 := bstep (se 1 (by rfl) ⟨1261130, by rfl⟩ : syracuseStep 1681507 = 2522261) B2522261
theorem B5671025 : Blo 1680040 5671025 := bstep (se 2 (by rfl) ⟨2126634, by rfl⟩ : syracuseStep 5671025 = 4253269) B4253269
theorem B1681523 : Blo 1680040 1681523 := bstep (se 1 (by rfl) ⟨1261142, by rfl⟩ : syracuseStep 1681523 = 2522285) B2522285
theorem B1681539 : Blo 1680040 1681539 := bstep (se 1 (by rfl) ⟨1261154, by rfl⟩ : syracuseStep 1681539 = 2522309) B2522309
theorem B8505485 : Blo 1680040 8505485 := bstep (se 3 (by rfl) ⟨1594778, by rfl⟩ : syracuseStep 8505485 = 3189557) B3189557
theorem B1681555 : Blo 1680040 1681555 := bstep (se 1 (by rfl) ⟨1261166, by rfl⟩ : syracuseStep 1681555 = 2522333) B2522333
theorem B1681571 : Blo 1680040 1681571 := bstep (se 1 (by rfl) ⟨1261178, by rfl⟩ : syracuseStep 1681571 = 2522357) B2522357
theorem B1681587 : Blo 1680040 1681587 := bstep (se 1 (by rfl) ⟨1261190, by rfl⟩ : syracuseStep 1681587 = 2522381) B2522381
theorem B1681603 : Blo 1680040 1681603 := bstep (se 1 (by rfl) ⟨1261202, by rfl⟩ : syracuseStep 1681603 = 2522405) B2522405
theorem B1681619 : Blo 1680040 1681619 := bstep (se 1 (by rfl) ⟨1261214, by rfl⟩ : syracuseStep 1681619 = 2522429) B2522429
theorem B1681635 : Blo 1680040 1681635 := bstep (se 1 (by rfl) ⟨1261226, by rfl⟩ : syracuseStep 1681635 = 2522453) B2522453
theorem B2836721 : Blo 1680040 2836721 := bstep (se 2 (by rfl) ⟨1063770, by rfl⟩ : syracuseStep 2836721 = 2127541) B2127541
theorem B2394355 : Blo 1680040 2394355 := bstep (se 1 (by rfl) ⟨1795766, by rfl⟩ : syracuseStep 2394355 = 3591533) B3591533
theorem B1681651 : Blo 1680040 1681651 := bstep (se 1 (by rfl) ⟨1261238, by rfl⟩ : syracuseStep 1681651 = 2522477) B2522477
theorem B1681667 : Blo 1680040 1681667 := bstep (se 1 (by rfl) ⟨1261250, by rfl⟩ : syracuseStep 1681667 = 2522501) B2522501
theorem B1681683 : Blo 1680040 1681683 := bstep (se 1 (by rfl) ⟨1261262, by rfl⟩ : syracuseStep 1681683 = 2522525) B2522525
theorem B1681699 : Blo 1680040 1681699 := bstep (se 1 (by rfl) ⟨1261274, by rfl⟩ : syracuseStep 1681699 = 2522549) B2522549
theorem B1681715 : Blo 1680040 1681715 := bstep (se 1 (by rfl) ⟨1261286, by rfl⟩ : syracuseStep 1681715 = 2522573) B2522573
theorem B1681731 : Blo 1680040 1681731 := bstep (se 1 (by rfl) ⟨1261298, by rfl⟩ : syracuseStep 1681731 = 2522597) B2522597
theorem B19401029 : Blo 1680040 19401029 := bstep (se 4 (by rfl) ⟨1818846, by rfl⟩ : syracuseStep 19401029 = 3637693) B3637693
theorem B1681747 : Blo 1680040 1681747 := bstep (se 1 (by rfl) ⟨1261310, by rfl⟩ : syracuseStep 1681747 = 2522621) B2522621
theorem B1681763 : Blo 1680040 1681763 := bstep (se 1 (by rfl) ⟨1261322, by rfl⟩ : syracuseStep 1681763 = 2522645) B2522645
theorem B2836849 : Blo 1680040 2836849 := bstep (se 2 (by rfl) ⟨1063818, by rfl⟩ : syracuseStep 2836849 = 2127637) B2127637
theorem B1681779 : Blo 1680040 1681779 := bstep (se 1 (by rfl) ⟨1261334, by rfl⟩ : syracuseStep 1681779 = 2522669) B2522669
theorem B1681795 : Blo 1680040 1681795 := bstep (se 1 (by rfl) ⟨1261346, by rfl⟩ : syracuseStep 1681795 = 2522693) B2522693
theorem B2836883 : Blo 1680040 2836883 := bstep (se 1 (by rfl) ⟨2127662, by rfl⟩ : syracuseStep 2836883 = 4255325) B4255325
theorem B1681811 : Blo 1680040 1681811 := bstep (se 1 (by rfl) ⟨1261358, by rfl⟩ : syracuseStep 1681811 = 2522717) B2522717
theorem B6384035 : Blo 1680040 6384035 := bstep (se 1 (by rfl) ⟨4788026, by rfl⟩ : syracuseStep 6384035 = 9576053) B9576053
theorem B1681827 : Blo 1680040 1681827 := bstep (se 1 (by rfl) ⟨1261370, by rfl⟩ : syracuseStep 1681827 = 2522741) B2522741
theorem B1681843 : Blo 1680040 1681843 := bstep (se 1 (by rfl) ⟨1261382, by rfl⟩ : syracuseStep 1681843 = 2522765) B2522765
theorem B3279299 : Blo 1680040 3279299 := bstep (se 1 (by rfl) ⟨2459474, by rfl⟩ : syracuseStep 3279299 = 4918949) B4918949
theorem B1681859 : Blo 1680040 1681859 := bstep (se 1 (by rfl) ⟨1261394, by rfl⟩ : syracuseStep 1681859 = 2522789) B2522789
theorem B1681875 : Blo 1680040 1681875 := bstep (se 1 (by rfl) ⟨1261406, by rfl⟩ : syracuseStep 1681875 = 2522813) B2522813
theorem B1681891 : Blo 1680040 1681891 := bstep (se 1 (by rfl) ⟨1261418, by rfl⟩ : syracuseStep 1681891 = 2522837) B2522837
theorem B8079857 : Blo 1680040 8079857 := bstep (se 2 (by rfl) ⟨3029946, by rfl⟩ : syracuseStep 8079857 = 6059893) B6059893
theorem B1681907 : Blo 1680040 1681907 := bstep (se 1 (by rfl) ⟨1261430, by rfl⟩ : syracuseStep 1681907 = 2522861) B2522861
theorem B1681923 : Blo 1680040 1681923 := bstep (se 1 (by rfl) ⟨1261442, by rfl⟩ : syracuseStep 1681923 = 2522885) B2522885
theorem B4786705 : Blo 1680040 4786705 := bstep (se 2 (by rfl) ⟨1795014, by rfl⟩ : syracuseStep 4786705 = 3590029) B3590029
theorem B2837011 : Blo 1680040 2837011 := bstep (se 1 (by rfl) ⟨2127758, by rfl⟩ : syracuseStep 2837011 = 4255517) B4255517
theorem B1681939 : Blo 1680040 1681939 := bstep (se 1 (by rfl) ⟨1261454, by rfl⟩ : syracuseStep 1681939 = 2522909) B2522909
theorem B4311587 : Blo 1680040 4311587 := bstep (se 1 (by rfl) ⟨3233690, by rfl⟩ : syracuseStep 4311587 = 6467381) B6467381
theorem B1681955 : Blo 1680040 1681955 := bstep (se 1 (by rfl) ⟨1261466, by rfl⟩ : syracuseStep 1681955 = 2522933) B2522933
theorem B3590705 : Blo 1680040 3590705 := bstep (se 2 (by rfl) ⟨1346514, by rfl⟩ : syracuseStep 3590705 = 2693029) B2693029
theorem B1681971 : Blo 1680040 1681971 := bstep (se 1 (by rfl) ⟨1261478, by rfl⟩ : syracuseStep 1681971 = 2522957) B2522957
theorem B1681987 : Blo 1680040 1681987 := bstep (se 1 (by rfl) ⟨1261490, by rfl⟩ : syracuseStep 1681987 = 2522981) B2522981
theorem B10357325 : Blo 1680040 10357325 := bstep (se 3 (by rfl) ⟨1941998, by rfl⟩ : syracuseStep 10357325 = 3883997) B3883997
theorem B1682003 : Blo 1680040 1682003 := bstep (se 1 (by rfl) ⟨1261502, by rfl⟩ : syracuseStep 1682003 = 2523005) B2523005
theorem B1682019 : Blo 1680040 1682019 := bstep (se 1 (by rfl) ⟨1261514, by rfl⟩ : syracuseStep 1682019 = 2523029) B2523029
theorem B1682035 : Blo 1680040 1682035 := bstep (se 1 (by rfl) ⟨1261526, by rfl⟩ : syracuseStep 1682035 = 2523053) B2523053
theorem B5671565 : Blo 1680040 5671565 := bstep (se 3 (by rfl) ⟨1063418, by rfl⟩ : syracuseStep 5671565 = 2126837) B2126837
theorem B4254353 : Blo 1680040 4254353 := bstep (se 2 (by rfl) ⟨1595382, by rfl⟩ : syracuseStep 4254353 = 3190765) B3190765
theorem B2837153 : Blo 1680040 2837153 := bstep (se 2 (by rfl) ⟨1063932, by rfl⟩ : syracuseStep 2837153 = 2127865) B2127865
theorem B5671619 : Blo 1680040 5671619 := bstep (se 1 (by rfl) ⟨4253714, by rfl⟩ : syracuseStep 5671619 = 8507429) B8507429
theorem B4254403 : Blo 1680040 4254403 := bstep (se 1 (by rfl) ⟨3190802, by rfl⟩ : syracuseStep 4254403 = 6381605) B6381605
theorem B2730707 : Blo 1680040 2730707 := bstep (se 1 (by rfl) ⟨2048030, by rfl⟩ : syracuseStep 2730707 = 4096061) B4096061
theorem B6056675 : Blo 1680040 6056675 := bstep (se 1 (by rfl) ⟨4542506, by rfl⟩ : syracuseStep 6056675 = 9085013) B9085013
theorem B10775267 : Blo 1680040 10775267 := bstep (se 1 (by rfl) ⟨8081450, by rfl⟩ : syracuseStep 10775267 = 16162901) B16162901
theorem B2837281 : Blo 1680040 2837281 := bstep (se 2 (by rfl) ⟨1063980, by rfl⟩ : syracuseStep 2837281 = 2127961) B2127961
theorem B2837315 : Blo 1680040 2837315 := bstep (se 1 (by rfl) ⟨2127986, by rfl⟩ : syracuseStep 2837315 = 4255973) B4255973
theorem B4254545 : Blo 1680040 4254545 := bstep (se 2 (by rfl) ⟨1595454, by rfl⟩ : syracuseStep 4254545 = 3190909) B3190909
theorem B2272097 : Blo 1680040 2272097 := bstep (se 2 (by rfl) ⟨852036, by rfl⟩ : syracuseStep 2272097 = 1704073) B1704073
theorem B11496305 : Blo 1680040 11496305 := bstep (se 2 (by rfl) ⟨4311114, by rfl⟩ : syracuseStep 11496305 = 8622229) B8622229
theorem B2837443 : Blo 1680040 2837443 := bstep (se 1 (by rfl) ⟨2128082, by rfl⟩ : syracuseStep 2837443 = 4256165) B4256165
theorem B5671889 : Blo 1680040 5671889 := bstep (se 2 (by rfl) ⟨2126958, by rfl⟩ : syracuseStep 5671889 = 4253917) B4253917
theorem B6384689 : Blo 1680040 6384689 := bstep (se 2 (by rfl) ⟨2394258, by rfl⟩ : syracuseStep 6384689 = 4788517) B4788517
theorem B9571405 : Blo 1680040 9571405 := bstep (se 3 (by rfl) ⟨1794638, by rfl⟩ : syracuseStep 9571405 = 3589277) B3589277
theorem B2837585 : Blo 1680040 2837585 := bstep (se 2 (by rfl) ⟨1064094, by rfl⟩ : syracuseStep 2837585 = 2128189) B2128189
theorem B9579653 : Blo 1680040 9579653 := bstep (se 4 (by rfl) ⟨898092, by rfl⟩ : syracuseStep 9579653 = 1796185) B1796185
theorem B3189937 : Blo 1680040 3189937 := bstep (se 2 (by rfl) ⟨1196226, by rfl⟩ : syracuseStep 3189937 = 2392453) B2392453
theorem B2837713 : Blo 1680040 2837713 := bstep (se 2 (by rfl) ⟨1064142, by rfl⟩ : syracuseStep 2837713 = 2128285) B2128285
theorem B2837747 : Blo 1680040 2837747 := bstep (se 1 (by rfl) ⟨2128310, by rfl⟩ : syracuseStep 2837747 = 4256621) B4256621
theorem B3190097 : Blo 1680040 3190097 := bstep (se 2 (by rfl) ⟨1196286, by rfl⟩ : syracuseStep 3190097 = 2392573) B2392573
theorem B2837875 : Blo 1680040 2837875 := bstep (se 1 (by rfl) ⟨2128406, by rfl⟩ : syracuseStep 2837875 = 4256813) B4256813
theorem B8515043 : Blo 1680040 8515043 := bstep (se 1 (by rfl) ⟨6386282, by rfl⟩ : syracuseStep 8515043 = 12772565) B12772565
theorem B5672429 : Blo 1680040 5672429 := bstep (se 3 (by rfl) ⟨1063580, by rfl⟩ : syracuseStep 5672429 = 2127161) B2127161
theorem B2838017 : Blo 1680040 2838017 := bstep (se 2 (by rfl) ⟨1064256, by rfl⟩ : syracuseStep 2838017 = 2128513) B2128513
theorem B12766733 : Blo 1680040 12766733 := bstep (se 3 (by rfl) ⟨2393762, by rfl⟩ : syracuseStep 12766733 = 4787525) B4787525
theorem B5672483 : Blo 1680040 5672483 := bstep (se 1 (by rfl) ⟨4254362, by rfl⟩ : syracuseStep 5672483 = 8508725) B8508725
theorem B7179853 : Blo 1680040 7179853 := bstep (se 3 (by rfl) ⟨1346222, by rfl⟩ : syracuseStep 7179853 = 2692445) B2692445
theorem B2272897 : Blo 1680040 2272897 := bstep (se 2 (by rfl) ⟨852336, by rfl⟩ : syracuseStep 2272897 = 1704673) B1704673
theorem B2838145 : Blo 1680040 2838145 := bstep (se 2 (by rfl) ⟨1064304, by rfl⟩ : syracuseStep 2838145 = 2128609) B2128609
theorem B24555149 : Blo 1680040 24555149 := bstep (se 3 (by rfl) ⟨4604090, by rfl⟩ : syracuseStep 24555149 = 9208181) B9208181
theorem B2838179 : Blo 1680040 2838179 := bstep (se 1 (by rfl) ⟨2128634, by rfl⟩ : syracuseStep 2838179 = 4257269) B4257269
theorem B19156661 : Blo 1680040 19156661 := bstep (se 5 (by rfl) ⟨897968, by rfl⟩ : syracuseStep 19156661 = 1795937) B1795937
theorem B3780305 : Blo 1680040 3780305 := bstep (se 2 (by rfl) ⟨1417614, by rfl⟩ : syracuseStep 3780305 = 2835229) B2835229
theorem B3780323 : Blo 1680040 3780323 := bstep (se 1 (by rfl) ⟨2835242, by rfl⟩ : syracuseStep 3780323 = 5670485) B5670485
theorem B3190499 : Blo 1680040 3190499 := bstep (se 1 (by rfl) ⟨2392874, by rfl⟩ : syracuseStep 3190499 = 4785749) B4785749
theorem B6057713 : Blo 1680040 6057713 := bstep (se 2 (by rfl) ⟨2271642, by rfl⟩ : syracuseStep 6057713 = 4543285) B4543285
theorem B4787981 : Blo 1680040 4787981 := bstep (se 3 (by rfl) ⟨897746, by rfl⟩ : syracuseStep 4787981 = 1795493) B1795493
theorem B2838307 : Blo 1680040 2838307 := bstep (se 1 (by rfl) ⟨2128730, by rfl⟩ : syracuseStep 2838307 = 4257461) B4257461
theorem B5672753 : Blo 1680040 5672753 := bstep (se 2 (by rfl) ⟨2127282, by rfl⟩ : syracuseStep 5672753 = 4254565) B4254565
theorem B4255537 : Blo 1680040 4255537 := bstep (se 2 (by rfl) ⟨1595826, by rfl⟩ : syracuseStep 4255537 = 3191653) B3191653
theorem B10227505 : Blo 1680040 10227505 := bstep (se 2 (by rfl) ⟨3835314, by rfl⟩ : syracuseStep 10227505 = 7670629) B7670629
theorem B18165617 : Blo 1680040 18165617 := bstep (se 2 (by rfl) ⟨6812106, by rfl⟩ : syracuseStep 18165617 = 13624213) B13624213
theorem B10768241 : Blo 1680040 10768241 := bstep (se 2 (by rfl) ⟨4038090, by rfl⟩ : syracuseStep 10768241 = 8076181) B8076181
theorem B4788163 : Blo 1680040 4788163 := bstep (se 1 (by rfl) ⟨3591122, by rfl⟩ : syracuseStep 4788163 = 7182245) B7182245
theorem B18165701 : Blo 1680040 18165701 := bstep (se 4 (by rfl) ⟨1703034, by rfl⟩ : syracuseStep 18165701 = 3406069) B3406069
theorem B7671757 : Blo 1680040 7671757 := bstep (se 3 (by rfl) ⟨1438454, by rfl⟩ : syracuseStep 7671757 = 2876909) B2876909
theorem B3780593 : Blo 1680040 3780593 := bstep (se 2 (by rfl) ⟨1417722, by rfl⟩ : syracuseStep 3780593 = 2835445) B2835445
theorem B4788209 : Blo 1680040 4788209 := bstep (se 2 (by rfl) ⟨1795578, by rfl⟩ : syracuseStep 4788209 = 3591157) B3591157
theorem B3780611 : Blo 1680040 3780611 := bstep (se 1 (by rfl) ⟨2835458, by rfl⟩ : syracuseStep 3780611 = 5670917) B5670917
theorem B4255811 : Blo 1680040 4255811 := bstep (se 1 (by rfl) ⟨3191858, by rfl⟩ : syracuseStep 4255811 = 6383717) B6383717
theorem B9089165 : Blo 1680040 9089165 := bstep (se 3 (by rfl) ⟨1704218, by rfl⟩ : syracuseStep 9089165 = 3408437) B3408437
theorem B2691235 : Blo 1680040 2691235 := bstep (se 1 (by rfl) ⟨2018426, by rfl⟩ : syracuseStep 2691235 = 4036853) B4036853
theorem B3592387 : Blo 1680040 3592387 := bstep (se 1 (by rfl) ⟨2694290, by rfl⟩ : syracuseStep 3592387 = 5388581) B5388581
theorem B4256003 : Blo 1680040 4256003 := bstep (se 1 (by rfl) ⟨3192002, by rfl⟩ : syracuseStep 4256003 = 6384005) B6384005
theorem B3780881 : Blo 1680040 3780881 := bstep (se 2 (by rfl) ⟨1417830, by rfl⟩ : syracuseStep 3780881 = 2835661) B2835661
theorem B3780899 : Blo 1680040 3780899 := bstep (se 1 (by rfl) ⟨2835674, by rfl⟩ : syracuseStep 3780899 = 5671349) B5671349
theorem B8630563 : Blo 1680040 8630563 := bstep (se 1 (by rfl) ⟨6472922, by rfl⟩ : syracuseStep 8630563 = 12945845) B12945845
theorem B5673293 : Blo 1680040 5673293 := bstep (se 3 (by rfl) ⟨1063742, by rfl⟩ : syracuseStep 5673293 = 2127485) B2127485
theorem B14356835 : Blo 1680040 14356835 := bstep (se 1 (by rfl) ⟨10767626, by rfl⟩ : syracuseStep 14356835 = 21535253) B21535253
theorem B5673347 : Blo 1680040 5673347 := bstep (se 1 (by rfl) ⟨4255010, by rfl⟩ : syracuseStep 5673347 = 8510021) B8510021
theorem B6386147 : Blo 1680040 6386147 := bstep (se 1 (by rfl) ⟨4789610, by rfl⟩ : syracuseStep 6386147 = 9579221) B9579221
theorem B6386161 : Blo 1680040 6386161 := bstep (se 2 (by rfl) ⟨2394810, by rfl⟩ : syracuseStep 6386161 = 4789621) B4789621
theorem B10768909 : Blo 1680040 10768909 := bstep (se 3 (by rfl) ⟨2019170, by rfl⟩ : syracuseStep 10768909 = 4038341) B4038341
theorem B5386787 : Blo 1680040 5386787 := bstep (se 1 (by rfl) ⟨4040090, by rfl⟩ : syracuseStep 5386787 = 8080181) B8080181
theorem B3781169 : Blo 1680040 3781169 := bstep (se 2 (by rfl) ⟨1417938, by rfl⟩ : syracuseStep 3781169 = 2835877) B2835877
theorem B3781187 : Blo 1680040 3781187 := bstep (se 1 (by rfl) ⟨2835890, by rfl⟩ : syracuseStep 3781187 = 5671781) B5671781
theorem B3191395 : Blo 1680040 3191395 := bstep (se 1 (by rfl) ⟨2393546, by rfl⟩ : syracuseStep 3191395 = 4787093) B4787093
theorem B7180913 : Blo 1680040 7180913 := bstep (se 2 (by rfl) ⟨2692842, by rfl⟩ : syracuseStep 7180913 = 5385685) B5385685
theorem B5673617 : Blo 1680040 5673617 := bstep (se 2 (by rfl) ⟨2127606, by rfl⟩ : syracuseStep 5673617 = 4255213) B4255213
theorem B5386915 : Blo 1680040 5386915 := bstep (se 1 (by rfl) ⟨4040186, by rfl⟩ : syracuseStep 5386915 = 8080373) B8080373
theorem B3191555 : Blo 1680040 3191555 := bstep (se 1 (by rfl) ⟨2393666, by rfl⟩ : syracuseStep 3191555 = 4787333) B4787333
theorem B42586933 : Blo 1680040 42586933 := bstep (se 5 (by rfl) ⟨1996262, by rfl⟩ : syracuseStep 42586933 = 3992525) B3992525
theorem B3781457 : Blo 1680040 3781457 := bstep (se 2 (by rfl) ⟨1418046, by rfl⟩ : syracuseStep 3781457 = 2836093) B2836093
theorem B2126675 : Blo 1680040 2126675 := bstep (se 1 (by rfl) ⟨1595006, by rfl⟩ : syracuseStep 2126675 = 3190013) B3190013
theorem B3781475 : Blo 1680040 3781475 := bstep (se 1 (by rfl) ⟨2836106, by rfl⟩ : syracuseStep 3781475 = 5672213) B5672213
theorem B22999949 : Blo 1680040 22999949 := bstep (se 3 (by rfl) ⟨4312490, by rfl⟩ : syracuseStep 22999949 = 8624981) B8624981
theorem B4092817 : Blo 1680040 4092817 := bstep (se 2 (by rfl) ⟨1534806, by rfl⟩ : syracuseStep 4092817 = 3069613) B3069613
theorem B8508401 : Blo 1680040 8508401 := bstep (se 2 (by rfl) ⟨3190650, by rfl⟩ : syracuseStep 8508401 = 6381301) B6381301
theorem B5387249 : Blo 1680040 5387249 := bstep (se 2 (by rfl) ⟨2020218, by rfl⟩ : syracuseStep 5387249 = 4040437) B4040437
theorem B2520065 : Blo 1680040 2520065 := bstep (se 2 (by rfl) ⟨945024, by rfl⟩ : syracuseStep 2520065 = 1890049) B1890049
theorem B9573389 : Blo 1680040 9573389 := bstep (se 3 (by rfl) ⟨1795010, by rfl⟩ : syracuseStep 9573389 = 3590021) B3590021
theorem B2520083 : Blo 1680040 2520083 := bstep (se 1 (by rfl) ⟨1890062, by rfl⟩ : syracuseStep 2520083 = 3780125) B3780125
theorem B2520113 : Blo 1680040 2520113 := bstep (se 2 (by rfl) ⟨945042, by rfl⟩ : syracuseStep 2520113 = 1890085) B1890085
theorem B2520131 : Blo 1680040 2520131 := bstep (se 1 (by rfl) ⟨1890098, by rfl⟩ : syracuseStep 2520131 = 3780197) B3780197
theorem B2692163 : Blo 1680040 2692163 := bstep (se 1 (by rfl) ⟨2019122, by rfl⟩ : syracuseStep 2692163 = 4038245) B4038245
theorem B2520161 : Blo 1680040 2520161 := bstep (se 2 (by rfl) ⟨945060, by rfl⟩ : syracuseStep 2520161 = 1890121) B1890121
theorem B3781745 : Blo 1680040 3781745 := bstep (se 2 (by rfl) ⟨1418154, by rfl⟩ : syracuseStep 3781745 = 2836309) B2836309
theorem B2520179 : Blo 1680040 2520179 := bstep (se 1 (by rfl) ⟨1890134, by rfl⟩ : syracuseStep 2520179 = 3780269) B3780269
theorem B3781763 : Blo 1680040 3781763 := bstep (se 1 (by rfl) ⟨2836322, by rfl⟩ : syracuseStep 3781763 = 5672645) B5672645
theorem B2520209 : Blo 1680040 2520209 := bstep (se 2 (by rfl) ⟨945078, by rfl⟩ : syracuseStep 2520209 = 1890157) B1890157
theorem B2520227 : Blo 1680040 2520227 := bstep (se 1 (by rfl) ⟨1890170, by rfl⟩ : syracuseStep 2520227 = 3780341) B3780341
theorem B5674157 : Blo 1680040 5674157 := bstep (se 3 (by rfl) ⟨1063904, by rfl⟩ : syracuseStep 5674157 = 2127809) B2127809
theorem B4256945 : Blo 1680040 4256945 := bstep (se 2 (by rfl) ⟨1596354, by rfl⟩ : syracuseStep 4256945 = 3192709) B3192709
theorem B2520257 : Blo 1680040 2520257 := bstep (se 2 (by rfl) ⟨945096, by rfl⟩ : syracuseStep 2520257 = 1890193) B1890193
theorem B32314565 : Blo 1680040 32314565 := bstep (se 4 (by rfl) ⟨3029490, by rfl⟩ : syracuseStep 32314565 = 6058981) B6058981
theorem B2520275 : Blo 1680040 2520275 := bstep (se 1 (by rfl) ⟨1890206, by rfl⟩ : syracuseStep 2520275 = 3780413) B3780413
theorem B5674211 : Blo 1680040 5674211 := bstep (se 1 (by rfl) ⟨4255658, by rfl⟩ : syracuseStep 5674211 = 8511317) B8511317
theorem B13636835 : Blo 1680040 13636835 := bstep (se 1 (by rfl) ⟨10227626, by rfl⟩ : syracuseStep 13636835 = 20455253) B20455253
theorem B4256995 : Blo 1680040 4256995 := bstep (se 1 (by rfl) ⟨3192746, by rfl⟩ : syracuseStep 4256995 = 6385493) B6385493
theorem B2520305 : Blo 1680040 2520305 := bstep (se 2 (by rfl) ⟨945114, by rfl⟩ : syracuseStep 2520305 = 1890229) B1890229
theorem B2520323 : Blo 1680040 2520323 := bstep (se 1 (by rfl) ⟨1890242, by rfl⟩ : syracuseStep 2520323 = 3780485) B3780485
theorem B11654405 : Blo 1680040 11654405 := bstep (se 4 (by rfl) ⟨1092600, by rfl⟩ : syracuseStep 11654405 = 2185201) B2185201
theorem B2520353 : Blo 1680040 2520353 := bstep (se 2 (by rfl) ⟨945132, by rfl⟩ : syracuseStep 2520353 = 1890265) B1890265
theorem B2520371 : Blo 1680040 2520371 := bstep (se 1 (by rfl) ⟨1890278, by rfl⟩ : syracuseStep 2520371 = 3780557) B3780557
theorem B2520401 : Blo 1680040 2520401 := bstep (se 2 (by rfl) ⟨945150, by rfl⟩ : syracuseStep 2520401 = 1890301) B1890301
theorem B2692433 : Blo 1680040 2692433 := bstep (se 2 (by rfl) ⟨1009662, by rfl⟩ : syracuseStep 2692433 = 2019325) B2019325
theorem B2520419 : Blo 1680040 2520419 := bstep (se 1 (by rfl) ⟨1890314, by rfl⟩ : syracuseStep 2520419 = 3780629) B3780629
theorem B4257137 : Blo 1680040 4257137 := bstep (se 2 (by rfl) ⟨1596426, by rfl⟩ : syracuseStep 4257137 = 3192853) B3192853
theorem B2520449 : Blo 1680040 2520449 := bstep (se 2 (by rfl) ⟨945168, by rfl⟩ : syracuseStep 2520449 = 1890337) B1890337
theorem B3782033 : Blo 1680040 3782033 := bstep (se 2 (by rfl) ⟨1418262, by rfl⟩ : syracuseStep 3782033 = 2836525) B2836525
theorem B2520467 : Blo 1680040 2520467 := bstep (se 1 (by rfl) ⟨1890350, by rfl⟩ : syracuseStep 2520467 = 3780701) B3780701
theorem B3782051 : Blo 1680040 3782051 := bstep (se 1 (by rfl) ⟨2836538, by rfl⟩ : syracuseStep 3782051 = 5673077) B5673077
theorem B4789667 : Blo 1680040 4789667 := bstep (se 1 (by rfl) ⟨3592250, by rfl⟩ : syracuseStep 4789667 = 7184501) B7184501
theorem B2520497 : Blo 1680040 2520497 := bstep (se 2 (by rfl) ⟨945186, by rfl⟩ : syracuseStep 2520497 = 1890373) B1890373
theorem B2520515 : Blo 1680040 2520515 := bstep (se 1 (by rfl) ⟨1890386, by rfl⟩ : syracuseStep 2520515 = 3780773) B3780773
theorem B2520545 : Blo 1680040 2520545 := bstep (se 2 (by rfl) ⟨945204, by rfl⟩ : syracuseStep 2520545 = 1890409) B1890409
theorem B6911459 : Blo 1680040 6911459 := bstep (se 1 (by rfl) ⟨5183594, by rfl⟩ : syracuseStep 6911459 = 10367189) B10367189
theorem B5674481 : Blo 1680040 5674481 := bstep (se 2 (by rfl) ⟨2127930, by rfl⟩ : syracuseStep 5674481 = 4255861) B4255861
theorem B2520563 : Blo 1680040 2520563 := bstep (se 1 (by rfl) ⟨1890422, by rfl⟩ : syracuseStep 2520563 = 3780845) B3780845
theorem B2520593 : Blo 1680040 2520593 := bstep (se 2 (by rfl) ⟨945222, by rfl⟩ : syracuseStep 2520593 = 1890445) B1890445
theorem B2127379 : Blo 1680040 2127379 := bstep (se 1 (by rfl) ⟨1595534, by rfl⟩ : syracuseStep 2127379 = 3191069) B3191069
theorem B2520611 : Blo 1680040 2520611 := bstep (se 1 (by rfl) ⟨1890458, by rfl⟩ : syracuseStep 2520611 = 3780917) B3780917
theorem B64599605 : Blo 1680040 64599605 := bstep (se 5 (by rfl) ⟨3028106, by rfl⟩ : syracuseStep 64599605 = 6056213) B6056213
theorem B2520641 : Blo 1680040 2520641 := bstep (se 2 (by rfl) ⟨945240, by rfl⟩ : syracuseStep 2520641 = 1890481) B1890481
theorem B2520659 : Blo 1680040 2520659 := bstep (se 1 (by rfl) ⟨1890494, by rfl⟩ : syracuseStep 2520659 = 3780989) B3780989
theorem B2520689 : Blo 1680040 2520689 := bstep (se 2 (by rfl) ⟨945258, by rfl⟩ : syracuseStep 2520689 = 1890517) B1890517
theorem B2692721 : Blo 1680040 2692721 := bstep (se 2 (by rfl) ⟨1009770, by rfl⟩ : syracuseStep 2692721 = 2019541) B2019541
theorem B2127475 : Blo 1680040 2127475 := bstep (se 1 (by rfl) ⟨1595606, by rfl⟩ : syracuseStep 2127475 = 3191213) B3191213
theorem B2520707 : Blo 1680040 2520707 := bstep (se 1 (by rfl) ⟨1890530, by rfl⟩ : syracuseStep 2520707 = 3781061) B3781061
theorem B2520737 : Blo 1680040 2520737 := bstep (se 2 (by rfl) ⟨945276, by rfl⟩ : syracuseStep 2520737 = 1890553) B1890553
theorem B4429475 : Blo 1680040 4429475 := bstep (se 1 (by rfl) ⟨3322106, by rfl⟩ : syracuseStep 4429475 = 6644213) B6644213
theorem B3782321 : Blo 1680040 3782321 := bstep (se 2 (by rfl) ⟨1418370, by rfl⟩ : syracuseStep 3782321 = 2836741) B2836741
theorem B2520755 : Blo 1680040 2520755 := bstep (se 1 (by rfl) ⟨1890566, by rfl⟩ : syracuseStep 2520755 = 3781133) B3781133
theorem B3782339 : Blo 1680040 3782339 := bstep (se 1 (by rfl) ⟨2836754, by rfl⟩ : syracuseStep 3782339 = 5673509) B5673509
theorem B2520785 : Blo 1680040 2520785 := bstep (se 2 (by rfl) ⟨945294, by rfl⟩ : syracuseStep 2520785 = 1890589) B1890589
theorem B2520803 : Blo 1680040 2520803 := bstep (se 1 (by rfl) ⟨1890602, by rfl⟩ : syracuseStep 2520803 = 3781205) B3781205
theorem B92034787 : Blo 1680040 92034787 := bstep (se 1 (by rfl) ⟨69026090, by rfl⟩ : syracuseStep 92034787 = 138052181) B138052181
theorem B2520833 : Blo 1680040 2520833 := bstep (se 2 (by rfl) ⟨945312, by rfl⟩ : syracuseStep 2520833 = 1890625) B1890625
theorem B1890067 : Blo 1680040 1890067 := bstep (se 1 (by rfl) ⟨1417550, by rfl⟩ : syracuseStep 1890067 = 2835101) B2835101
theorem B2520851 : Blo 1680040 2520851 := bstep (se 1 (by rfl) ⟨1890638, by rfl⟩ : syracuseStep 2520851 = 3781277) B3781277
theorem B2520881 : Blo 1680040 2520881 := bstep (se 2 (by rfl) ⟨945330, by rfl⟩ : syracuseStep 2520881 = 1890661) B1890661
theorem B3192625 : Blo 1680040 3192625 := bstep (se 2 (by rfl) ⟨1197234, by rfl⟩ : syracuseStep 3192625 = 2394469) B2394469
theorem B2520899 : Blo 1680040 2520899 := bstep (se 1 (by rfl) ⟨1890674, by rfl⟩ : syracuseStep 2520899 = 3781349) B3781349
theorem B12760901 : Blo 1680040 12760901 := bstep (se 4 (by rfl) ⟨1196334, by rfl⟩ : syracuseStep 12760901 = 2392669) B2392669
theorem B2520929 : Blo 1680040 2520929 := bstep (se 2 (by rfl) ⟨945348, by rfl⟩ : syracuseStep 2520929 = 1890697) B1890697
theorem B2520947 : Blo 1680040 2520947 := bstep (se 1 (by rfl) ⟨1890710, by rfl⟩ : syracuseStep 2520947 = 3781421) B3781421
theorem B2520977 : Blo 1680040 2520977 := bstep (se 2 (by rfl) ⟨945366, by rfl⟩ : syracuseStep 2520977 = 1890733) B1890733
theorem B1890211 : Blo 1680040 1890211 := bstep (se 1 (by rfl) ⟨1417658, by rfl⟩ : syracuseStep 1890211 = 2835317) B2835317
theorem B2520995 : Blo 1680040 2520995 := bstep (se 1 (by rfl) ⟨1890746, by rfl⟩ : syracuseStep 2520995 = 3781493) B3781493
theorem B9574321 : Blo 1680040 9574321 := bstep (se 2 (by rfl) ⟨3590370, by rfl⟩ : syracuseStep 9574321 = 7180741) B7180741
theorem B2521025 : Blo 1680040 2521025 := bstep (se 2 (by rfl) ⟨945384, by rfl⟩ : syracuseStep 2521025 = 1890769) B1890769
theorem B3782609 : Blo 1680040 3782609 := bstep (se 2 (by rfl) ⟨1418478, by rfl⟩ : syracuseStep 3782609 = 2836957) B2836957
theorem B2521043 : Blo 1680040 2521043 := bstep (se 1 (by rfl) ⟨1890782, by rfl⟩ : syracuseStep 2521043 = 3781565) B3781565
theorem B3782627 : Blo 1680040 3782627 := bstep (se 1 (by rfl) ⟨2836970, by rfl⟩ : syracuseStep 3782627 = 5673941) B5673941
theorem B2521073 : Blo 1680040 2521073 := bstep (se 2 (by rfl) ⟨945402, by rfl⟩ : syracuseStep 2521073 = 1890805) B1890805
theorem B2521091 : Blo 1680040 2521091 := bstep (se 1 (by rfl) ⟨1890818, by rfl⟩ : syracuseStep 2521091 = 3781637) B3781637
theorem B5675021 : Blo 1680040 5675021 := bstep (se 3 (by rfl) ⟨1064066, by rfl⟩ : syracuseStep 5675021 = 2128133) B2128133
theorem B2693137 : Blo 1680040 2693137 := bstep (se 2 (by rfl) ⟨1009926, by rfl⟩ : syracuseStep 2693137 = 2019853) B2019853
theorem B2521121 : Blo 1680040 2521121 := bstep (se 2 (by rfl) ⟨945420, by rfl⟩ : syracuseStep 2521121 = 1890841) B1890841
theorem B1890355 : Blo 1680040 1890355 := bstep (se 1 (by rfl) ⟨1417766, by rfl⟩ : syracuseStep 1890355 = 2835533) B2835533
theorem B2521139 : Blo 1680040 2521139 := bstep (se 1 (by rfl) ⟨1890854, by rfl⟩ : syracuseStep 2521139 = 3781709) B3781709
theorem B5675075 : Blo 1680040 5675075 := bstep (se 1 (by rfl) ⟨4256306, by rfl⟩ : syracuseStep 5675075 = 8512613) B8512613
theorem B2521169 : Blo 1680040 2521169 := bstep (se 2 (by rfl) ⟨945438, by rfl⟩ : syracuseStep 2521169 = 1890877) B1890877
theorem B2521187 : Blo 1680040 2521187 := bstep (se 1 (by rfl) ⟨1890890, by rfl⟩ : syracuseStep 2521187 = 3781781) B3781781
theorem B2127971 : Blo 1680040 2127971 := bstep (se 1 (by rfl) ⟨1595978, by rfl⟩ : syracuseStep 2127971 = 3191957) B3191957
theorem B2521217 : Blo 1680040 2521217 := bstep (se 2 (by rfl) ⟨945456, by rfl⟩ : syracuseStep 2521217 = 1890913) B1890913
theorem B6379661 : Blo 1680040 6379661 := bstep (se 3 (by rfl) ⟨1196186, by rfl⟩ : syracuseStep 6379661 = 2392373) B2392373
theorem B2521235 : Blo 1680040 2521235 := bstep (se 1 (by rfl) ⟨1890926, by rfl⟩ : syracuseStep 2521235 = 3781853) B3781853
theorem B2521265 : Blo 1680040 2521265 := bstep (se 2 (by rfl) ⟨945474, by rfl⟩ : syracuseStep 2521265 = 1890949) B1890949
theorem B1890499 : Blo 1680040 1890499 := bstep (se 1 (by rfl) ⟨1417874, by rfl⟩ : syracuseStep 1890499 = 2835749) B2835749
theorem B2521283 : Blo 1680040 2521283 := bstep (se 1 (by rfl) ⟨1890962, by rfl⟩ : syracuseStep 2521283 = 3781925) B3781925
theorem B2521313 : Blo 1680040 2521313 := bstep (se 2 (by rfl) ⟨945492, by rfl⟩ : syracuseStep 2521313 = 1890985) B1890985
theorem B3782897 : Blo 1680040 3782897 := bstep (se 2 (by rfl) ⟨1418586, by rfl⟩ : syracuseStep 3782897 = 2837173) B2837173
theorem B2521331 : Blo 1680040 2521331 := bstep (se 1 (by rfl) ⟨1890998, by rfl⟩ : syracuseStep 2521331 = 3781997) B3781997
theorem B3782915 : Blo 1680040 3782915 := bstep (se 1 (by rfl) ⟨2837186, by rfl⟩ : syracuseStep 3782915 = 5674373) B5674373
theorem B2521361 : Blo 1680040 2521361 := bstep (se 2 (by rfl) ⟨945510, by rfl⟩ : syracuseStep 2521361 = 1891021) B1891021
theorem B2521379 : Blo 1680040 2521379 := bstep (se 1 (by rfl) ⟨1891034, by rfl⟩ : syracuseStep 2521379 = 3782069) B3782069
theorem B2521409 : Blo 1680040 2521409 := bstep (se 2 (by rfl) ⟨945528, by rfl⟩ : syracuseStep 2521409 = 1891057) B1891057
theorem B5675345 : Blo 1680040 5675345 := bstep (se 2 (by rfl) ⟨2128254, by rfl⟩ : syracuseStep 5675345 = 4256509) B4256509
theorem B1890643 : Blo 1680040 1890643 := bstep (se 1 (by rfl) ⟨1417982, by rfl⟩ : syracuseStep 1890643 = 2835965) B2835965
theorem B2521427 : Blo 1680040 2521427 := bstep (se 1 (by rfl) ⟨1891070, by rfl⟩ : syracuseStep 2521427 = 3782141) B3782141
theorem B2521457 : Blo 1680040 2521457 := bstep (se 2 (by rfl) ⟨945546, by rfl⟩ : syracuseStep 2521457 = 1891093) B1891093
theorem B12769649 : Blo 1680040 12769649 := bstep (se 2 (by rfl) ⟨4788618, by rfl⟩ : syracuseStep 12769649 = 9577237) B9577237
theorem B2521475 : Blo 1680040 2521475 := bstep (se 1 (by rfl) ⟨1891106, by rfl⟩ : syracuseStep 2521475 = 3782213) B3782213
theorem B2521505 : Blo 1680040 2521505 := bstep (se 2 (by rfl) ⟨945564, by rfl⟩ : syracuseStep 2521505 = 1891129) B1891129
theorem B8509859 : Blo 1680040 8509859 := bstep (se 1 (by rfl) ⟨6382394, by rfl⟩ : syracuseStep 8509859 = 12764789) B12764789
theorem B2521523 : Blo 1680040 2521523 := bstep (se 1 (by rfl) ⟨1891142, by rfl⟩ : syracuseStep 2521523 = 3782285) B3782285
theorem B2521553 : Blo 1680040 2521553 := bstep (se 2 (by rfl) ⟨945582, by rfl⟩ : syracuseStep 2521553 = 1891165) B1891165
theorem B1890787 : Blo 1680040 1890787 := bstep (se 1 (by rfl) ⟨1418090, by rfl⟩ : syracuseStep 1890787 = 2836181) B2836181
theorem B2521571 : Blo 1680040 2521571 := bstep (se 1 (by rfl) ⟨1891178, by rfl⟩ : syracuseStep 2521571 = 3782357) B3782357
theorem B17258993 : Blo 1680040 17258993 := bstep (se 2 (by rfl) ⟨6472122, by rfl⟩ : syracuseStep 17258993 = 12944245) B12944245
theorem B2521601 : Blo 1680040 2521601 := bstep (se 2 (by rfl) ⟨945600, by rfl⟩ : syracuseStep 2521601 = 1891201) B1891201
theorem B3783185 : Blo 1680040 3783185 := bstep (se 2 (by rfl) ⟨1418694, by rfl⟩ : syracuseStep 3783185 = 2837389) B2837389
theorem B2521619 : Blo 1680040 2521619 := bstep (se 1 (by rfl) ⟨1891214, by rfl⟩ : syracuseStep 2521619 = 3782429) B3782429
theorem B3783203 : Blo 1680040 3783203 := bstep (se 1 (by rfl) ⟨2837402, by rfl⟩ : syracuseStep 3783203 = 5674805) B5674805
theorem B2521649 : Blo 1680040 2521649 := bstep (se 2 (by rfl) ⟨945618, by rfl⟩ : syracuseStep 2521649 = 1891237) B1891237
theorem B2521667 : Blo 1680040 2521667 := bstep (se 1 (by rfl) ⟨1891250, by rfl⟩ : syracuseStep 2521667 = 3782501) B3782501
theorem B2521697 : Blo 1680040 2521697 := bstep (se 2 (by rfl) ⟨945636, by rfl⟩ : syracuseStep 2521697 = 1891273) B1891273
theorem B1890931 : Blo 1680040 1890931 := bstep (se 1 (by rfl) ⟨1418198, by rfl⟩ : syracuseStep 1890931 = 2836397) B2836397
theorem B2521715 : Blo 1680040 2521715 := bstep (se 1 (by rfl) ⟨1891286, by rfl⟩ : syracuseStep 2521715 = 3782573) B3782573
theorem B2521745 : Blo 1680040 2521745 := bstep (se 2 (by rfl) ⟨945654, by rfl⟩ : syracuseStep 2521745 = 1891309) B1891309
theorem B2521763 : Blo 1680040 2521763 := bstep (se 1 (by rfl) ⟨1891322, by rfl⟩ : syracuseStep 2521763 = 3782645) B3782645
theorem B2521793 : Blo 1680040 2521793 := bstep (se 2 (by rfl) ⟨945672, by rfl⟩ : syracuseStep 2521793 = 1891345) B1891345
theorem B2521811 : Blo 1680040 2521811 := bstep (se 1 (by rfl) ⟨1891358, by rfl⟩ : syracuseStep 2521811 = 3782717) B3782717
theorem B2521841 : Blo 1680040 2521841 := bstep (se 2 (by rfl) ⟨945690, by rfl⟩ : syracuseStep 2521841 = 1891381) B1891381
theorem B1891075 : Blo 1680040 1891075 := bstep (se 1 (by rfl) ⟨1418306, by rfl⟩ : syracuseStep 1891075 = 2836613) B2836613
theorem B2521859 : Blo 1680040 2521859 := bstep (se 1 (by rfl) ⟨1891394, by rfl⟩ : syracuseStep 2521859 = 3782789) B3782789
theorem B2521889 : Blo 1680040 2521889 := bstep (se 2 (by rfl) ⟨945708, by rfl⟩ : syracuseStep 2521889 = 1891417) B1891417
theorem B3029795 : Blo 1680040 3029795 := bstep (se 1 (by rfl) ⟨2272346, by rfl⟩ : syracuseStep 3029795 = 4544693) B4544693
theorem B2128675 : Blo 1680040 2128675 := bstep (se 1 (by rfl) ⟨1596506, by rfl⟩ : syracuseStep 2128675 = 3193013) B3193013
theorem B3783473 : Blo 1680040 3783473 := bstep (se 2 (by rfl) ⟨1418802, by rfl⟩ : syracuseStep 3783473 = 2837605) B2837605
theorem B2521907 : Blo 1680040 2521907 := bstep (se 1 (by rfl) ⟨1891430, by rfl⟩ : syracuseStep 2521907 = 3782861) B3782861
theorem B3783491 : Blo 1680040 3783491 := bstep (se 1 (by rfl) ⟨2837618, by rfl⟩ : syracuseStep 3783491 = 5675237) B5675237
theorem B2521937 : Blo 1680040 2521937 := bstep (se 2 (by rfl) ⟨945726, by rfl⟩ : syracuseStep 2521937 = 1891453) B1891453
theorem B2521955 : Blo 1680040 2521955 := bstep (se 1 (by rfl) ⟨1891466, by rfl⟩ : syracuseStep 2521955 = 3782933) B3782933
theorem B5675885 : Blo 1680040 5675885 := bstep (se 3 (by rfl) ⟨1064228, by rfl⟩ : syracuseStep 5675885 = 2128457) B2128457
theorem B2521985 : Blo 1680040 2521985 := bstep (se 2 (by rfl) ⟨945744, by rfl⟩ : syracuseStep 2521985 = 1891489) B1891489
theorem B2128771 : Blo 1680040 2128771 := bstep (se 1 (by rfl) ⟨1596578, by rfl⟩ : syracuseStep 2128771 = 3193157) B3193157
theorem B5749645 : Blo 1680040 5749645 := bstep (se 3 (by rfl) ⟨1078058, by rfl⟩ : syracuseStep 5749645 = 2156117) B2156117
theorem B1891219 : Blo 1680040 1891219 := bstep (se 1 (by rfl) ⟨1418414, by rfl⟩ : syracuseStep 1891219 = 2836829) B2836829
theorem B2522003 : Blo 1680040 2522003 := bstep (se 1 (by rfl) ⟨1891502, by rfl⟩ : syracuseStep 2522003 = 3783005) B3783005
theorem B2694035 : Blo 1680040 2694035 := bstep (se 1 (by rfl) ⟨2020526, by rfl⟩ : syracuseStep 2694035 = 4041053) B4041053
theorem B5675939 : Blo 1680040 5675939 := bstep (se 1 (by rfl) ⟨4256954, by rfl⟩ : syracuseStep 5675939 = 8513909) B8513909
theorem B3406769 : Blo 1680040 3406769 := bstep (se 2 (by rfl) ⟨1277538, by rfl⟩ : syracuseStep 3406769 = 2555077) B2555077
theorem B2522033 : Blo 1680040 2522033 := bstep (se 2 (by rfl) ⟨945762, by rfl⟩ : syracuseStep 2522033 = 1891525) B1891525
theorem B2522051 : Blo 1680040 2522051 := bstep (se 1 (by rfl) ⟨1891538, by rfl⟩ : syracuseStep 2522051 = 3783077) B3783077
theorem B2522081 : Blo 1680040 2522081 := bstep (se 2 (by rfl) ⟨945780, by rfl⟩ : syracuseStep 2522081 = 1891561) B1891561
theorem B2522099 : Blo 1680040 2522099 := bstep (se 1 (by rfl) ⟨1891574, by rfl⟩ : syracuseStep 2522099 = 3783149) B3783149
theorem B2522129 : Blo 1680040 2522129 := bstep (se 2 (by rfl) ⟨945798, by rfl⟩ : syracuseStep 2522129 = 1891597) B1891597
theorem B1891363 : Blo 1680040 1891363 := bstep (se 1 (by rfl) ⟨1418522, by rfl⟩ : syracuseStep 1891363 = 2837045) B2837045
theorem B2522147 : Blo 1680040 2522147 := bstep (se 1 (by rfl) ⟨1891610, by rfl⟩ : syracuseStep 2522147 = 3783221) B3783221
theorem B2522177 : Blo 1680040 2522177 := bstep (se 2 (by rfl) ⟨945816, by rfl⟩ : syracuseStep 2522177 = 1891633) B1891633
theorem B3783761 : Blo 1680040 3783761 := bstep (se 2 (by rfl) ⟨1418910, by rfl⟩ : syracuseStep 3783761 = 2837821) B2837821
theorem B2522195 : Blo 1680040 2522195 := bstep (se 1 (by rfl) ⟨1891646, by rfl⟩ : syracuseStep 2522195 = 3783293) B3783293
theorem B3783779 : Blo 1680040 3783779 := bstep (se 1 (by rfl) ⟨2837834, by rfl⟩ : syracuseStep 3783779 = 5675669) B5675669
theorem B2522225 : Blo 1680040 2522225 := bstep (se 2 (by rfl) ⟨945834, by rfl⟩ : syracuseStep 2522225 = 1891669) B1891669
theorem B2694259 : Blo 1680040 2694259 := bstep (se 1 (by rfl) ⟨2020694, by rfl⟩ : syracuseStep 2694259 = 4041389) B4041389
theorem B2522243 : Blo 1680040 2522243 := bstep (se 1 (by rfl) ⟨1891682, by rfl⟩ : syracuseStep 2522243 = 3783365) B3783365
theorem B2522273 : Blo 1680040 2522273 := bstep (se 2 (by rfl) ⟨945852, by rfl⟩ : syracuseStep 2522273 = 1891705) B1891705
theorem B5676209 : Blo 1680040 5676209 := bstep (se 2 (by rfl) ⟨2128578, by rfl⟩ : syracuseStep 5676209 = 4257157) B4257157
theorem B1891507 : Blo 1680040 1891507 := bstep (se 1 (by rfl) ⟨1418630, by rfl⟩ : syracuseStep 1891507 = 2837261) B2837261
theorem B2522291 : Blo 1680040 2522291 := bstep (se 1 (by rfl) ⟨1891718, by rfl⟩ : syracuseStep 2522291 = 3783437) B3783437
theorem B8510669 : Blo 1680040 8510669 := bstep (se 3 (by rfl) ⟨1595750, by rfl⟩ : syracuseStep 8510669 = 3191501) B3191501
theorem B2522321 : Blo 1680040 2522321 := bstep (se 2 (by rfl) ⟨945870, by rfl⟩ : syracuseStep 2522321 = 1891741) B1891741
theorem B2522339 : Blo 1680040 2522339 := bstep (se 1 (by rfl) ⟨1891754, by rfl⟩ : syracuseStep 2522339 = 3783509) B3783509
theorem B2522369 : Blo 1680040 2522369 := bstep (se 2 (by rfl) ⟨945888, by rfl⟩ : syracuseStep 2522369 = 1891777) B1891777
theorem B3407107 : Blo 1680040 3407107 := bstep (se 1 (by rfl) ⟨2555330, by rfl⟩ : syracuseStep 3407107 = 5110661) B5110661
theorem B2522387 : Blo 1680040 2522387 := bstep (se 1 (by rfl) ⟨1891790, by rfl⟩ : syracuseStep 2522387 = 3783581) B3783581
theorem B4095281 : Blo 1680040 4095281 := bstep (se 2 (by rfl) ⟨1535730, by rfl⟩ : syracuseStep 4095281 = 3071461) B3071461
theorem B2522417 : Blo 1680040 2522417 := bstep (se 2 (by rfl) ⟨945906, by rfl⟩ : syracuseStep 2522417 = 1891813) B1891813
theorem B1891651 : Blo 1680040 1891651 := bstep (se 1 (by rfl) ⟨1418738, by rfl⟩ : syracuseStep 1891651 = 2837477) B2837477
theorem B2522435 : Blo 1680040 2522435 := bstep (se 1 (by rfl) ⟨1891826, by rfl⟩ : syracuseStep 2522435 = 3783653) B3783653
theorem B2522465 : Blo 1680040 2522465 := bstep (se 2 (by rfl) ⟨945924, by rfl⟩ : syracuseStep 2522465 = 1891849) B1891849
theorem B9575779 : Blo 1680040 9575779 := bstep (se 1 (by rfl) ⟨7181834, by rfl⟩ : syracuseStep 9575779 = 14363669) B14363669
theorem B3784049 : Blo 1680040 3784049 := bstep (se 2 (by rfl) ⟨1419018, by rfl⟩ : syracuseStep 3784049 = 2838037) B2838037
theorem B2522483 : Blo 1680040 2522483 := bstep (se 1 (by rfl) ⟨1891862, by rfl⟩ : syracuseStep 2522483 = 3783725) B3783725
theorem B3784067 : Blo 1680040 3784067 := bstep (se 1 (by rfl) ⟨2838050, by rfl⟩ : syracuseStep 3784067 = 5676101) B5676101
theorem B2522513 : Blo 1680040 2522513 := bstep (se 2 (by rfl) ⟨945942, by rfl⟩ : syracuseStep 2522513 = 1891885) B1891885
theorem B2522531 : Blo 1680040 2522531 := bstep (se 1 (by rfl) ⟨1891898, by rfl⟩ : syracuseStep 2522531 = 3783797) B3783797
theorem B2522561 : Blo 1680040 2522561 := bstep (se 2 (by rfl) ⟨945960, by rfl⟩ : syracuseStep 2522561 = 1891921) B1891921
theorem B4038083 : Blo 1680040 4038083 := bstep (se 1 (by rfl) ⟨3028562, by rfl⟩ : syracuseStep 4038083 = 6057125) B6057125
theorem B1891795 : Blo 1680040 1891795 := bstep (se 1 (by rfl) ⟨1418846, by rfl⟩ : syracuseStep 1891795 = 2837693) B2837693
theorem B2522579 : Blo 1680040 2522579 := bstep (se 1 (by rfl) ⟨1891934, by rfl⟩ : syracuseStep 2522579 = 3783869) B3783869
theorem B2522609 : Blo 1680040 2522609 := bstep (se 2 (by rfl) ⟨945978, by rfl⟩ : syracuseStep 2522609 = 1891957) B1891957
theorem B2522627 : Blo 1680040 2522627 := bstep (se 1 (by rfl) ⟨1891970, by rfl⟩ : syracuseStep 2522627 = 3783941) B3783941
theorem B7183885 : Blo 1680040 7183885 := bstep (se 3 (by rfl) ⟨1346978, by rfl⟩ : syracuseStep 7183885 = 2693957) B2693957
theorem B2874899 : Blo 1680040 2874899 := bstep (se 1 (by rfl) ⟨2156174, by rfl⟩ : syracuseStep 2874899 = 4312349) B4312349
theorem B2522657 : Blo 1680040 2522657 := bstep (se 2 (by rfl) ⟨945996, by rfl⟩ : syracuseStep 2522657 = 1891993) B1891993
theorem B2522675 : Blo 1680040 2522675 := bstep (se 1 (by rfl) ⟨1892006, by rfl⟩ : syracuseStep 2522675 = 3784013) B3784013
theorem B2522705 : Blo 1680040 2522705 := bstep (se 2 (by rfl) ⟨946014, by rfl⟩ : syracuseStep 2522705 = 1892029) B1892029
theorem B1891939 : Blo 1680040 1891939 := bstep (se 1 (by rfl) ⟨1418954, by rfl⟩ : syracuseStep 1891939 = 2837909) B2837909
theorem B2522723 : Blo 1680040 2522723 := bstep (se 1 (by rfl) ⟨1892042, by rfl⟩ : syracuseStep 2522723 = 3784085) B3784085
theorem B2522753 : Blo 1680040 2522753 := bstep (se 2 (by rfl) ⟨946032, by rfl⟩ : syracuseStep 2522753 = 1892065) B1892065
theorem B8740493 : Blo 1680040 8740493 := bstep (se 3 (by rfl) ⟨1638842, by rfl⟩ : syracuseStep 8740493 = 3277685) B3277685
theorem B3784337 : Blo 1680040 3784337 := bstep (se 2 (by rfl) ⟨1419126, by rfl⟩ : syracuseStep 3784337 = 2838253) B2838253
theorem B2522771 : Blo 1680040 2522771 := bstep (se 1 (by rfl) ⟨1892078, by rfl⟩ : syracuseStep 2522771 = 3784157) B3784157
theorem B3784355 : Blo 1680040 3784355 := bstep (se 1 (by rfl) ⟨2838266, by rfl⟩ : syracuseStep 3784355 = 5676533) B5676533
theorem B2522801 : Blo 1680040 2522801 := bstep (se 2 (by rfl) ⟨946050, by rfl⟩ : syracuseStep 2522801 = 1892101) B1892101
theorem B2522819 : Blo 1680040 2522819 := bstep (se 1 (by rfl) ⟨1892114, by rfl⟩ : syracuseStep 2522819 = 3784229) B3784229
theorem B5676749 : Blo 1680040 5676749 := bstep (se 3 (by rfl) ⟨1064390, by rfl⟩ : syracuseStep 5676749 = 2128781) B2128781
theorem B2522849 : Blo 1680040 2522849 := bstep (se 2 (by rfl) ⟨946068, by rfl⟩ : syracuseStep 2522849 = 1892137) B1892137
theorem B1892083 : Blo 1680040 1892083 := bstep (se 1 (by rfl) ⟨1419062, by rfl⟩ : syracuseStep 1892083 = 2838125) B2838125
theorem B2522867 : Blo 1680040 2522867 := bstep (se 1 (by rfl) ⟨1892150, by rfl⟩ : syracuseStep 2522867 = 3784301) B3784301
theorem B5676803 : Blo 1680040 5676803 := bstep (se 1 (by rfl) ⟨4257602, by rfl⟩ : syracuseStep 5676803 = 8515205) B8515205
theorem B2522897 : Blo 1680040 2522897 := bstep (se 2 (by rfl) ⟨946086, by rfl⟩ : syracuseStep 2522897 = 1892173) B1892173
theorem B2522915 : Blo 1680040 2522915 := bstep (se 1 (by rfl) ⟨1892186, by rfl⟩ : syracuseStep 2522915 = 3784373) B3784373
theorem B3030833 : Blo 1680040 3030833 := bstep (se 2 (by rfl) ⟨1136562, by rfl⟩ : syracuseStep 3030833 = 2273125) B2273125
theorem B2522945 : Blo 1680040 2522945 := bstep (se 2 (by rfl) ⟨946104, by rfl⟩ : syracuseStep 2522945 = 1892209) B1892209
theorem B2522963 : Blo 1680040 2522963 := bstep (se 1 (by rfl) ⟨1892222, by rfl⟩ : syracuseStep 2522963 = 3784445) B3784445
theorem B7184227 : Blo 1680040 7184227 := bstep (se 1 (by rfl) ⟨5388170, by rfl⟩ : syracuseStep 7184227 = 10776341) B10776341
theorem B9576305 : Blo 1680040 9576305 := bstep (se 2 (by rfl) ⟨3591114, by rfl⟩ : syracuseStep 9576305 = 7182229) B7182229
theorem B2522993 : Blo 1680040 2522993 := bstep (se 2 (by rfl) ⟨946122, by rfl⟩ : syracuseStep 2522993 = 1892245) B1892245
theorem B1892227 : Blo 1680040 1892227 := bstep (se 1 (by rfl) ⟨1419170, by rfl⟩ : syracuseStep 1892227 = 2838341) B2838341
theorem B2523011 : Blo 1680040 2523011 := bstep (se 1 (by rfl) ⟨1892258, by rfl⟩ : syracuseStep 2523011 = 3784517) B3784517
theorem B2523041 : Blo 1680040 2523041 := bstep (se 2 (by rfl) ⟨946140, by rfl⟩ : syracuseStep 2523041 = 1892281) B1892281
theorem B2523059 : Blo 1680040 2523059 := bstep (se 1 (by rfl) ⟨1892294, by rfl⟩ : syracuseStep 2523059 = 3784589) B3784589
theorem B3588313 : Blo 1680040 3588313 := bstep (se 2 (by rfl) ⟨1345617, by rfl⟩ : syracuseStep 3588313 = 2691235) B2691235
theorem B2392345 : Blo 1680040 2392345 := bstep (se 2 (by rfl) ⟨897129, by rfl⟩ : syracuseStep 2392345 = 1794259) B1794259
theorem B16155287 : Blo 1680040 16155287 := bstep (se 1 (by rfl) ⟨12116465, by rfl⟩ : syracuseStep 16155287 = 24232931) B24232931
theorem B25887383 : Blo 1680040 25887383 := bstep (se 1 (by rfl) ⟨19415537, by rfl⟩ : syracuseStep 25887383 = 38831075) B38831075
theorem B1680043 : Blo 1680040 1680043 := bstep (se 1 (by rfl) ⟨1260032, by rfl⟩ : syracuseStep 1680043 = 2520065) B2520065
theorem B6382259 : Blo 1680040 6382259 := bstep (se 1 (by rfl) ⟨4786694, by rfl⟩ : syracuseStep 6382259 = 9573389) B9573389
theorem B1680055 : Blo 1680040 1680055 := bstep (se 1 (by rfl) ⟨1260041, by rfl⟩ : syracuseStep 1680055 = 2520083) B2520083
theorem B6382273 : Blo 1680040 6382273 := bstep (se 2 (by rfl) ⟨2393352, by rfl⟩ : syracuseStep 6382273 = 4786705) B4786705
theorem B1680075 : Blo 1680040 1680075 := bstep (se 1 (by rfl) ⟨1260056, by rfl⟩ : syracuseStep 1680075 = 2520113) B2520113
theorem B1680087 : Blo 1680040 1680087 := bstep (se 1 (by rfl) ⟨1260065, by rfl⟩ : syracuseStep 1680087 = 2520131) B2520131
theorem B1680107 : Blo 1680040 1680107 := bstep (se 1 (by rfl) ⟨1260080, by rfl⟩ : syracuseStep 1680107 = 2520161) B2520161
theorem B1680119 : Blo 1680040 1680119 := bstep (se 1 (by rfl) ⟨1260089, by rfl⟩ : syracuseStep 1680119 = 2520179) B2520179
theorem B1680139 : Blo 1680040 1680139 := bstep (se 1 (by rfl) ⟨1260104, by rfl⟩ : syracuseStep 1680139 = 2520209) B2520209
theorem B1680151 : Blo 1680040 1680151 := bstep (se 1 (by rfl) ⟨1260113, by rfl⟩ : syracuseStep 1680151 = 2520227) B2520227
theorem B1680171 : Blo 1680040 1680171 := bstep (se 1 (by rfl) ⟨1260128, by rfl⟩ : syracuseStep 1680171 = 2520257) B2520257
theorem B1680183 : Blo 1680040 1680183 := bstep (se 1 (by rfl) ⟨1260137, by rfl⟩ : syracuseStep 1680183 = 2520275) B2520275
theorem B1680203 : Blo 1680040 1680203 := bstep (se 1 (by rfl) ⟨1260152, by rfl⟩ : syracuseStep 1680203 = 2520305) B2520305
theorem B1680215 : Blo 1680040 1680215 := bstep (se 1 (by rfl) ⟨1260161, by rfl⟩ : syracuseStep 1680215 = 2520323) B2520323
theorem B1680235 : Blo 1680040 1680235 := bstep (se 1 (by rfl) ⟨1260176, by rfl⟩ : syracuseStep 1680235 = 2520353) B2520353
theorem B1917803 : Blo 1680040 1917803 := bstep (se 1 (by rfl) ⟨1438352, by rfl⟩ : syracuseStep 1917803 = 2876705) B2876705
theorem B1680247 : Blo 1680040 1680247 := bstep (se 1 (by rfl) ⟨1260185, by rfl⟩ : syracuseStep 1680247 = 2520371) B2520371
theorem B27263861 : Blo 1680040 27263861 := bstep (se 5 (by rfl) ⟨1277993, by rfl⟩ : syracuseStep 27263861 = 2555987) B2555987
theorem B1680267 : Blo 1680040 1680267 := bstep (se 1 (by rfl) ⟨1260200, by rfl⟩ : syracuseStep 1680267 = 2520401) B2520401
theorem B1794955 : Blo 1680040 1794955 := bstep (se 1 (by rfl) ⟨1346216, by rfl⟩ : syracuseStep 1794955 = 2692433) B2692433
theorem B1680279 : Blo 1680040 1680279 := bstep (se 1 (by rfl) ⟨1260209, by rfl⟩ : syracuseStep 1680279 = 2520419) B2520419
theorem B1680299 : Blo 1680040 1680299 := bstep (se 1 (by rfl) ⟨1260224, by rfl⟩ : syracuseStep 1680299 = 2520449) B2520449
theorem B1680311 : Blo 1680040 1680311 := bstep (se 1 (by rfl) ⟨1260233, by rfl⟩ : syracuseStep 1680311 = 2520467) B2520467
theorem B1680331 : Blo 1680040 1680331 := bstep (se 1 (by rfl) ⟨1260248, by rfl⟩ : syracuseStep 1680331 = 2520497) B2520497
theorem B1680343 : Blo 1680040 1680343 := bstep (se 1 (by rfl) ⟨1260257, by rfl⟩ : syracuseStep 1680343 = 2520515) B2520515
theorem B1680363 : Blo 1680040 1680363 := bstep (se 1 (by rfl) ⟨1260272, by rfl⟩ : syracuseStep 1680363 = 2520545) B2520545
theorem B1680375 : Blo 1680040 1680375 := bstep (se 1 (by rfl) ⟨1260281, by rfl⟩ : syracuseStep 1680375 = 2520563) B2520563
theorem B1680395 : Blo 1680040 1680395 := bstep (se 1 (by rfl) ⟨1260296, by rfl⟩ : syracuseStep 1680395 = 2520593) B2520593
theorem B2835479 : Blo 1680040 2835479 := bstep (se 1 (by rfl) ⟨2126609, by rfl⟩ : syracuseStep 2835479 = 4253219) B4253219
theorem B1680407 : Blo 1680040 1680407 := bstep (se 1 (by rfl) ⟨1260305, by rfl⟩ : syracuseStep 1680407 = 2520611) B2520611
theorem B43066403 : Blo 1680040 43066403 := bstep (se 1 (by rfl) ⟨32299802, by rfl⟩ : syracuseStep 43066403 = 64599605) B64599605
theorem B1680427 : Blo 1680040 1680427 := bstep (se 1 (by rfl) ⟨1260320, by rfl⟩ : syracuseStep 1680427 = 2520641) B2520641
theorem B1680439 : Blo 1680040 1680439 := bstep (se 1 (by rfl) ⟨1260329, by rfl⟩ : syracuseStep 1680439 = 2520659) B2520659
theorem B1680459 : Blo 1680040 1680459 := bstep (se 1 (by rfl) ⟨1260344, by rfl⟩ : syracuseStep 1680459 = 2520689) B2520689
theorem B1680471 : Blo 1680040 1680471 := bstep (se 1 (by rfl) ⟨1260353, by rfl⟩ : syracuseStep 1680471 = 2520707) B2520707
theorem B1680491 : Blo 1680040 1680491 := bstep (se 1 (by rfl) ⟨1260368, by rfl⟩ : syracuseStep 1680491 = 2520737) B2520737
theorem B1680503 : Blo 1680040 1680503 := bstep (se 1 (by rfl) ⟨1260377, by rfl⟩ : syracuseStep 1680503 = 2520755) B2520755
theorem B1680523 : Blo 1680040 1680523 := bstep (se 1 (by rfl) ⟨1260392, by rfl⟩ : syracuseStep 1680523 = 2520785) B2520785
theorem B2835607 : Blo 1680040 2835607 := bstep (se 1 (by rfl) ⟨2126705, by rfl⟩ : syracuseStep 2835607 = 4253411) B4253411
theorem B1680535 : Blo 1680040 1680535 := bstep (se 1 (by rfl) ⟨1260401, by rfl⟩ : syracuseStep 1680535 = 2520803) B2520803
theorem B2393239 : Blo 1680040 2393239 := bstep (se 1 (by rfl) ⟨1794929, by rfl⟩ : syracuseStep 2393239 = 3589859) B3589859
theorem B1680555 : Blo 1680040 1680555 := bstep (se 1 (by rfl) ⟨1260416, by rfl⟩ : syracuseStep 1680555 = 2520833) B2520833
theorem B1680567 : Blo 1680040 1680567 := bstep (se 1 (by rfl) ⟨1260425, by rfl⟩ : syracuseStep 1680567 = 2520851) B2520851
theorem B5457089 : Blo 1680040 5457089 := bstep (se 2 (by rfl) ⟨2046408, by rfl⟩ : syracuseStep 5457089 = 4092817) B4092817
theorem B1680587 : Blo 1680040 1680587 := bstep (se 1 (by rfl) ⟨1260440, by rfl⟩ : syracuseStep 1680587 = 2520881) B2520881
theorem B1680599 : Blo 1680040 1680599 := bstep (se 1 (by rfl) ⟨1260449, by rfl⟩ : syracuseStep 1680599 = 2520899) B2520899
theorem B1680619 : Blo 1680040 1680619 := bstep (se 1 (by rfl) ⟨1260464, by rfl⟩ : syracuseStep 1680619 = 2520929) B2520929
theorem B3589363 : Blo 1680040 3589363 := bstep (se 1 (by rfl) ⟨2692022, by rfl⟩ : syracuseStep 3589363 = 5384045) B5384045
theorem B1680631 : Blo 1680040 1680631 := bstep (se 1 (by rfl) ⟨1260473, by rfl⟩ : syracuseStep 1680631 = 2520947) B2520947
theorem B1680651 : Blo 1680040 1680651 := bstep (se 1 (by rfl) ⟨1260488, by rfl⟩ : syracuseStep 1680651 = 2520977) B2520977
theorem B1680663 : Blo 1680040 1680663 := bstep (se 1 (by rfl) ⟨1260497, by rfl⟩ : syracuseStep 1680663 = 2520995) B2520995
theorem B1680683 : Blo 1680040 1680683 := bstep (se 1 (by rfl) ⟨1260512, by rfl⟩ : syracuseStep 1680683 = 2521025) B2521025
theorem B1680695 : Blo 1680040 1680695 := bstep (se 1 (by rfl) ⟨1260521, by rfl⟩ : syracuseStep 1680695 = 2521043) B2521043
theorem B21529921 : Blo 1680040 21529921 := bstep (se 2 (by rfl) ⟨8073720, by rfl⟩ : syracuseStep 21529921 = 16147441) B16147441
theorem B1680715 : Blo 1680040 1680715 := bstep (se 1 (by rfl) ⟨1260536, by rfl⟩ : syracuseStep 1680715 = 2521073) B2521073
theorem B1680727 : Blo 1680040 1680727 := bstep (se 1 (by rfl) ⟨1260545, by rfl⟩ : syracuseStep 1680727 = 2521091) B2521091
theorem B1680747 : Blo 1680040 1680747 := bstep (se 1 (by rfl) ⟨1260560, by rfl⟩ : syracuseStep 1680747 = 2521121) B2521121
theorem B1680759 : Blo 1680040 1680759 := bstep (se 1 (by rfl) ⟨1260569, by rfl⟩ : syracuseStep 1680759 = 2521139) B2521139
theorem B1680779 : Blo 1680040 1680779 := bstep (se 1 (by rfl) ⟨1260584, by rfl⟩ : syracuseStep 1680779 = 2521169) B2521169
theorem B1680791 : Blo 1680040 1680791 := bstep (se 1 (by rfl) ⟨1260593, by rfl⟩ : syracuseStep 1680791 = 2521187) B2521187
theorem B1680811 : Blo 1680040 1680811 := bstep (se 1 (by rfl) ⟨1260608, by rfl⟩ : syracuseStep 1680811 = 2521217) B2521217
theorem B5670323 : Blo 1680040 5670323 := bstep (se 1 (by rfl) ⟨4252742, by rfl⟩ : syracuseStep 5670323 = 8505485) B8505485
theorem B4253107 : Blo 1680040 4253107 := bstep (se 1 (by rfl) ⟨3189830, by rfl⟩ : syracuseStep 4253107 = 6379661) B6379661
theorem B1680823 : Blo 1680040 1680823 := bstep (se 1 (by rfl) ⟨1260617, by rfl⟩ : syracuseStep 1680823 = 2521235) B2521235
theorem B4785601 : Blo 1680040 4785601 := bstep (se 2 (by rfl) ⟨1794600, by rfl⟩ : syracuseStep 4785601 = 3589201) B3589201
theorem B1680843 : Blo 1680040 1680843 := bstep (se 1 (by rfl) ⟨1260632, by rfl⟩ : syracuseStep 1680843 = 2521265) B2521265
theorem B1680855 : Blo 1680040 1680855 := bstep (se 1 (by rfl) ⟨1260641, by rfl⟩ : syracuseStep 1680855 = 2521283) B2521283
theorem B1680875 : Blo 1680040 1680875 := bstep (se 1 (by rfl) ⟨1260656, by rfl⟩ : syracuseStep 1680875 = 2521313) B2521313
theorem B1680887 : Blo 1680040 1680887 := bstep (se 1 (by rfl) ⟨1260665, by rfl⟩ : syracuseStep 1680887 = 2521331) B2521331
theorem B1680907 : Blo 1680040 1680907 := bstep (se 1 (by rfl) ⟨1260680, by rfl⟩ : syracuseStep 1680907 = 2521361) B2521361
theorem B1680919 : Blo 1680040 1680919 := bstep (se 1 (by rfl) ⟨1260689, by rfl⟩ : syracuseStep 1680919 = 2521379) B2521379
theorem B1680939 : Blo 1680040 1680939 := bstep (se 1 (by rfl) ⟨1260704, by rfl⟩ : syracuseStep 1680939 = 2521409) B2521409
theorem B1680951 : Blo 1680040 1680951 := bstep (se 1 (by rfl) ⟨1260713, by rfl⟩ : syracuseStep 1680951 = 2521427) B2521427
theorem B4253249 : Blo 1680040 4253249 := bstep (se 2 (by rfl) ⟨1594968, by rfl⟩ : syracuseStep 4253249 = 3189937) B3189937
theorem B10225217 : Blo 1680040 10225217 := bstep (se 2 (by rfl) ⟨3834456, by rfl⟩ : syracuseStep 10225217 = 7668913) B7668913
theorem B1680971 : Blo 1680040 1680971 := bstep (se 1 (by rfl) ⟨1260728, by rfl⟩ : syracuseStep 1680971 = 2521457) B2521457
theorem B8513099 : Blo 1680040 8513099 := bstep (se 1 (by rfl) ⟨6384824, by rfl⟩ : syracuseStep 8513099 = 12769649) B12769649
theorem B1680983 : Blo 1680040 1680983 := bstep (se 1 (by rfl) ⟨1260737, by rfl⟩ : syracuseStep 1680983 = 2521475) B2521475
theorem B1681003 : Blo 1680040 1681003 := bstep (se 1 (by rfl) ⟨1260752, by rfl⟩ : syracuseStep 1681003 = 2521505) B2521505
theorem B1681015 : Blo 1680040 1681015 := bstep (se 1 (by rfl) ⟨1260761, by rfl⟩ : syracuseStep 1681015 = 2521523) B2521523
theorem B1681035 : Blo 1680040 1681035 := bstep (se 1 (by rfl) ⟨1260776, by rfl⟩ : syracuseStep 1681035 = 2521553) B2521553
theorem B1681047 : Blo 1680040 1681047 := bstep (se 1 (by rfl) ⟨1260785, by rfl⟩ : syracuseStep 1681047 = 2521571) B2521571
theorem B1681067 : Blo 1680040 1681067 := bstep (se 1 (by rfl) ⟨1260800, by rfl⟩ : syracuseStep 1681067 = 2521601) B2521601
theorem B1681079 : Blo 1680040 1681079 := bstep (se 1 (by rfl) ⟨1260809, by rfl⟩ : syracuseStep 1681079 = 2521619) B2521619
theorem B5670593 : Blo 1680040 5670593 := bstep (se 2 (by rfl) ⟨2126472, by rfl⟩ : syracuseStep 5670593 = 4252945) B4252945
theorem B1681099 : Blo 1680040 1681099 := bstep (se 1 (by rfl) ⟨1260824, by rfl⟩ : syracuseStep 1681099 = 2521649) B2521649
theorem B2393803 : Blo 1680040 2393803 := bstep (se 1 (by rfl) ⟨1795352, by rfl⟩ : syracuseStep 2393803 = 3590705) B3590705
theorem B1681111 : Blo 1680040 1681111 := bstep (se 1 (by rfl) ⟨1260833, by rfl⟩ : syracuseStep 1681111 = 2521667) B2521667
theorem B1681131 : Blo 1680040 1681131 := bstep (se 1 (by rfl) ⟨1260848, by rfl⟩ : syracuseStep 1681131 = 2521697) B2521697
theorem B1681143 : Blo 1680040 1681143 := bstep (se 1 (by rfl) ⟨1260857, by rfl⟩ : syracuseStep 1681143 = 2521715) B2521715
theorem B2836235 : Blo 1680040 2836235 := bstep (se 1 (by rfl) ⟨2127176, by rfl⟩ : syracuseStep 2836235 = 4254353) B4254353
theorem B1681163 : Blo 1680040 1681163 := bstep (se 1 (by rfl) ⟨1260872, by rfl⟩ : syracuseStep 1681163 = 2521745) B2521745
theorem B1681175 : Blo 1680040 1681175 := bstep (se 1 (by rfl) ⟨1260881, by rfl⟩ : syracuseStep 1681175 = 2521763) B2521763
theorem B1681195 : Blo 1680040 1681195 := bstep (se 1 (by rfl) ⟨1260896, by rfl⟩ : syracuseStep 1681195 = 2521793) B2521793
theorem B1681207 : Blo 1680040 1681207 := bstep (se 1 (by rfl) ⟨1260905, by rfl⟩ : syracuseStep 1681207 = 2521811) B2521811
theorem B1820471 : Blo 1680040 1820471 := bstep (se 1 (by rfl) ⟨1365353, by rfl⟩ : syracuseStep 1820471 = 2730707) B2730707
theorem B1681227 : Blo 1680040 1681227 := bstep (se 1 (by rfl) ⟨1260920, by rfl⟩ : syracuseStep 1681227 = 2521841) B2521841
theorem B1681239 : Blo 1680040 1681239 := bstep (se 1 (by rfl) ⟨1260929, by rfl⟩ : syracuseStep 1681239 = 2521859) B2521859
theorem B1681259 : Blo 1680040 1681259 := bstep (se 1 (by rfl) ⟨1260944, by rfl⟩ : syracuseStep 1681259 = 2521889) B2521889
theorem B1681271 : Blo 1680040 1681271 := bstep (se 1 (by rfl) ⟨1260953, by rfl⟩ : syracuseStep 1681271 = 2521907) B2521907
theorem B2836363 : Blo 1680040 2836363 := bstep (se 1 (by rfl) ⟨2127272, by rfl⟩ : syracuseStep 2836363 = 4254545) B4254545
theorem B1681291 : Blo 1680040 1681291 := bstep (se 1 (by rfl) ⟨1260968, by rfl⟩ : syracuseStep 1681291 = 2521937) B2521937
theorem B7178129 : Blo 1680040 7178129 := bstep (se 2 (by rfl) ⟨2691798, by rfl⟩ : syracuseStep 7178129 = 5383597) B5383597
theorem B1681303 : Blo 1680040 1681303 := bstep (se 1 (by rfl) ⟨1260977, by rfl⟩ : syracuseStep 1681303 = 2521955) B2521955
theorem B1681323 : Blo 1680040 1681323 := bstep (se 1 (by rfl) ⟨1260992, by rfl⟩ : syracuseStep 1681323 = 2521985) B2521985
theorem B1681335 : Blo 1680040 1681335 := bstep (se 1 (by rfl) ⟨1261001, by rfl⟩ : syracuseStep 1681335 = 2522003) B2522003
theorem B1796023 : Blo 1680040 1796023 := bstep (se 1 (by rfl) ⟨1347017, by rfl⟩ : syracuseStep 1796023 = 2694035) B2694035
theorem B2271179 : Blo 1680040 2271179 := bstep (se 1 (by rfl) ⟨1703384, by rfl⟩ : syracuseStep 2271179 = 3406769) B3406769
theorem B1681355 : Blo 1680040 1681355 := bstep (se 1 (by rfl) ⟨1261016, by rfl⟩ : syracuseStep 1681355 = 2522033) B2522033
theorem B1681367 : Blo 1680040 1681367 := bstep (se 1 (by rfl) ⟨1261025, by rfl⟩ : syracuseStep 1681367 = 2522051) B2522051
theorem B1681387 : Blo 1680040 1681387 := bstep (se 1 (by rfl) ⟨1261040, by rfl⟩ : syracuseStep 1681387 = 2522081) B2522081
theorem B1681399 : Blo 1680040 1681399 := bstep (se 1 (by rfl) ⟨1261049, by rfl⟩ : syracuseStep 1681399 = 2522099) B2522099
theorem B1681419 : Blo 1680040 1681419 := bstep (se 1 (by rfl) ⟨1261064, by rfl⟩ : syracuseStep 1681419 = 2522129) B2522129
theorem B13633553 : Blo 1680040 13633553 := bstep (se 2 (by rfl) ⟨5112582, by rfl⟩ : syracuseStep 13633553 = 10225165) B10225165
theorem B9578513 : Blo 1680040 9578513 := bstep (se 2 (by rfl) ⟨3591942, by rfl⟩ : syracuseStep 9578513 = 7183885) B7183885
theorem B1681431 : Blo 1680040 1681431 := bstep (se 1 (by rfl) ⟨1261073, by rfl⟩ : syracuseStep 1681431 = 2522147) B2522147
theorem B2836505 : Blo 1680040 2836505 := bstep (se 2 (by rfl) ⟨1063689, by rfl⟩ : syracuseStep 2836505 = 2127379) B2127379
theorem B1681451 : Blo 1680040 1681451 := bstep (se 1 (by rfl) ⟨1261088, by rfl⟩ : syracuseStep 1681451 = 2522177) B2522177
theorem B1681463 : Blo 1680040 1681463 := bstep (se 1 (by rfl) ⟨1261097, by rfl⟩ : syracuseStep 1681463 = 2522195) B2522195
theorem B1681483 : Blo 1680040 1681483 := bstep (se 1 (by rfl) ⟨1261112, by rfl⟩ : syracuseStep 1681483 = 2522225) B2522225
theorem B1681495 : Blo 1680040 1681495 := bstep (se 1 (by rfl) ⟨1261121, by rfl⟩ : syracuseStep 1681495 = 2522243) B2522243
theorem B1681515 : Blo 1680040 1681515 := bstep (se 1 (by rfl) ⟨1261136, by rfl⟩ : syracuseStep 1681515 = 2522273) B2522273
theorem B1681527 : Blo 1680040 1681527 := bstep (se 1 (by rfl) ⟨1261145, by rfl⟩ : syracuseStep 1681527 = 2522291) B2522291
theorem B1681547 : Blo 1680040 1681547 := bstep (se 1 (by rfl) ⟨1261160, by rfl⟩ : syracuseStep 1681547 = 2522321) B2522321
theorem B1681559 : Blo 1680040 1681559 := bstep (se 1 (by rfl) ⟨1261169, by rfl⟩ : syracuseStep 1681559 = 2522339) B2522339
theorem B2836633 : Blo 1680040 2836633 := bstep (se 2 (by rfl) ⟨1063737, by rfl⟩ : syracuseStep 2836633 = 2127475) B2127475
theorem B1681579 : Blo 1680040 1681579 := bstep (se 1 (by rfl) ⟨1261184, by rfl⟩ : syracuseStep 1681579 = 2522369) B2522369
theorem B1681591 : Blo 1680040 1681591 := bstep (se 1 (by rfl) ⟨1261193, by rfl⟩ : syracuseStep 1681591 = 2522387) B2522387
theorem B2730187 : Blo 1680040 2730187 := bstep (se 1 (by rfl) ⟨2047640, by rfl⟩ : syracuseStep 2730187 = 4095281) B4095281
theorem B1681611 : Blo 1680040 1681611 := bstep (se 1 (by rfl) ⟨1261208, by rfl⟩ : syracuseStep 1681611 = 2522417) B2522417
theorem B1681623 : Blo 1680040 1681623 := bstep (se 1 (by rfl) ⟨1261217, by rfl⟩ : syracuseStep 1681623 = 2522435) B2522435
theorem B5671133 : Blo 1680040 5671133 := bstep (se 3 (by rfl) ⟨1063337, by rfl⟩ : syracuseStep 5671133 = 2126675) B2126675
theorem B1681643 : Blo 1680040 1681643 := bstep (se 1 (by rfl) ⟨1261232, by rfl⟩ : syracuseStep 1681643 = 2522465) B2522465
theorem B1681655 : Blo 1680040 1681655 := bstep (se 1 (by rfl) ⟨1261241, by rfl⟩ : syracuseStep 1681655 = 2522483) B2522483
theorem B1681675 : Blo 1680040 1681675 := bstep (se 1 (by rfl) ⟨1261256, by rfl⟩ : syracuseStep 1681675 = 2522513) B2522513
theorem B1681687 : Blo 1680040 1681687 := bstep (se 1 (by rfl) ⟨1261265, by rfl⟩ : syracuseStep 1681687 = 2522531) B2522531
theorem B1681707 : Blo 1680040 1681707 := bstep (se 1 (by rfl) ⟨1261280, by rfl⟩ : syracuseStep 1681707 = 2522561) B2522561
theorem B28715309 : Blo 1680040 28715309 := bstep (se 3 (by rfl) ⟨5384120, by rfl⟩ : syracuseStep 28715309 = 10768241) B10768241
theorem B1681719 : Blo 1680040 1681719 := bstep (se 1 (by rfl) ⟨1261289, by rfl⟩ : syracuseStep 1681719 = 2522579) B2522579
theorem B1681739 : Blo 1680040 1681739 := bstep (se 1 (by rfl) ⟨1261304, by rfl⟩ : syracuseStep 1681739 = 2522609) B2522609
theorem B1681751 : Blo 1680040 1681751 := bstep (se 1 (by rfl) ⟨1261313, by rfl⟩ : syracuseStep 1681751 = 2522627) B2522627
theorem B1681771 : Blo 1680040 1681771 := bstep (se 1 (by rfl) ⟨1261328, by rfl⟩ : syracuseStep 1681771 = 2522657) B2522657
theorem B1681783 : Blo 1680040 1681783 := bstep (se 1 (by rfl) ⟨1261337, by rfl⟩ : syracuseStep 1681783 = 2522675) B2522675
theorem B1681803 : Blo 1680040 1681803 := bstep (se 1 (by rfl) ⟨1261352, by rfl⟩ : syracuseStep 1681803 = 2522705) B2522705
theorem B1681815 : Blo 1680040 1681815 := bstep (se 1 (by rfl) ⟨1261361, by rfl⟩ : syracuseStep 1681815 = 2522723) B2522723
theorem B1681835 : Blo 1680040 1681835 := bstep (se 1 (by rfl) ⟨1261376, by rfl⟩ : syracuseStep 1681835 = 2522753) B2522753
theorem B5826995 : Blo 1680040 5826995 := bstep (se 1 (by rfl) ⟨4370246, by rfl⟩ : syracuseStep 5826995 = 8740493) B8740493
theorem B16370099 : Blo 1680040 16370099 := bstep (se 1 (by rfl) ⟨12277574, by rfl⟩ : syracuseStep 16370099 = 24555149) B24555149
theorem B1681847 : Blo 1680040 1681847 := bstep (se 1 (by rfl) ⟨1261385, by rfl⟩ : syracuseStep 1681847 = 2522771) B2522771
theorem B1681867 : Blo 1680040 1681867 := bstep (se 1 (by rfl) ⟨1261400, by rfl⟩ : syracuseStep 1681867 = 2522801) B2522801
theorem B1681879 : Blo 1680040 1681879 := bstep (se 1 (by rfl) ⟨1261409, by rfl⟩ : syracuseStep 1681879 = 2522819) B2522819
theorem B9578969 : Blo 1680040 9578969 := bstep (se 2 (by rfl) ⟨3592113, by rfl⟩ : syracuseStep 9578969 = 7184227) B7184227
theorem B1681899 : Blo 1680040 1681899 := bstep (se 1 (by rfl) ⟨1261424, by rfl⟩ : syracuseStep 1681899 = 2522849) B2522849
theorem B1681911 : Blo 1680040 1681911 := bstep (se 1 (by rfl) ⟨1261433, by rfl⟩ : syracuseStep 1681911 = 2522867) B2522867
theorem B1681931 : Blo 1680040 1681931 := bstep (se 1 (by rfl) ⟨1261448, by rfl⟩ : syracuseStep 1681931 = 2522897) B2522897
theorem B1681943 : Blo 1680040 1681943 := bstep (se 1 (by rfl) ⟨1261457, by rfl⟩ : syracuseStep 1681943 = 2522915) B2522915
theorem B1681963 : Blo 1680040 1681963 := bstep (se 1 (by rfl) ⟨1261472, by rfl⟩ : syracuseStep 1681963 = 2522945) B2522945
theorem B1681975 : Blo 1680040 1681975 := bstep (se 1 (by rfl) ⟨1261481, by rfl⟩ : syracuseStep 1681975 = 2522963) B2522963
theorem B4852289 : Blo 1680040 4852289 := bstep (se 2 (by rfl) ⟨1819608, by rfl⟩ : syracuseStep 4852289 = 3639217) B3639217
theorem B12765761 : Blo 1680040 12765761 := bstep (se 2 (by rfl) ⟨4787160, by rfl⟩ : syracuseStep 12765761 = 9574321) B9574321
theorem B12110411 : Blo 1680040 12110411 := bstep (se 1 (by rfl) ⟨9082808, by rfl⟩ : syracuseStep 12110411 = 18165617) B18165617
theorem B6384203 : Blo 1680040 6384203 := bstep (se 1 (by rfl) ⟨4788152, by rfl⟩ : syracuseStep 6384203 = 9576305) B9576305
theorem B1681995 : Blo 1680040 1681995 := bstep (se 1 (by rfl) ⟨1261496, by rfl⟩ : syracuseStep 1681995 = 2522993) B2522993
theorem B1682007 : Blo 1680040 1682007 := bstep (se 1 (by rfl) ⟨1261505, by rfl⟩ : syracuseStep 1682007 = 2523011) B2523011
theorem B6384217 : Blo 1680040 6384217 := bstep (se 2 (by rfl) ⟨2394081, by rfl⟩ : syracuseStep 6384217 = 4788163) B4788163
theorem B19139165 : Blo 1680040 19139165 := bstep (se 3 (by rfl) ⟨3588593, by rfl⟩ : syracuseStep 19139165 = 7177187) B7177187
theorem B1682027 : Blo 1680040 1682027 := bstep (se 1 (by rfl) ⟨1261520, by rfl⟩ : syracuseStep 1682027 = 2523041) B2523041
theorem B1682039 : Blo 1680040 1682039 := bstep (se 1 (by rfl) ⟨1261529, by rfl⟩ : syracuseStep 1682039 = 2523059) B2523059
theorem B12110467 : Blo 1680040 12110467 := bstep (se 1 (by rfl) ⟨9082850, by rfl⟩ : syracuseStep 12110467 = 18165701) B18165701
theorem B3590849 : Blo 1680040 3590849 := bstep (se 2 (by rfl) ⟨1346568, by rfl⟩ : syracuseStep 3590849 = 2693137) B2693137
theorem B2837207 : Blo 1680040 2837207 := bstep (se 1 (by rfl) ⟨2127905, by rfl⟩ : syracuseStep 2837207 = 4255811) B4255811
theorem B3189527 : Blo 1680040 3189527 := bstep (se 1 (by rfl) ⟨2392145, by rfl⟩ : syracuseStep 3189527 = 4784291) B4784291
theorem B4254515 : Blo 1680040 4254515 := bstep (se 1 (by rfl) ⟨3190886, by rfl⟩ : syracuseStep 4254515 = 6381773) B6381773
theorem B2837335 : Blo 1680040 2837335 := bstep (se 1 (by rfl) ⟨2128001, by rfl⟩ : syracuseStep 2837335 = 4256003) B4256003
theorem B7179101 : Blo 1680040 7179101 := bstep (se 3 (by rfl) ⟨1346081, by rfl⟩ : syracuseStep 7179101 = 2692163) B2692163
theorem B8629085 : Blo 1680040 8629085 := bstep (se 3 (by rfl) ⟨1617953, by rfl⟩ : syracuseStep 8629085 = 3235907) B3235907
theorem B10226533 : Blo 1680040 10226533 := bstep (se 4 (by rfl) ⟨958737, by rfl⟩ : syracuseStep 10226533 = 1917475) B1917475
theorem B9571223 : Blo 1680040 9571223 := bstep (se 1 (by rfl) ⟨7178417, by rfl⟩ : syracuseStep 9571223 = 14356835) B14356835
theorem B7482385 : Blo 1680040 7482385 := bstep (se 2 (by rfl) ⟨2805894, by rfl⟩ : syracuseStep 7482385 = 5611789) B5611789
theorem B3591191 : Blo 1680040 3591191 := bstep (se 1 (by rfl) ⟨2693393, by rfl⟩ : syracuseStep 3591191 = 5386787) B5386787
theorem B4787275 : Blo 1680040 4787275 := bstep (se 1 (by rfl) ⟨3590456, by rfl⟩ : syracuseStep 4787275 = 7180913) B7180913
theorem B8514881 : Blo 1680040 8514881 := bstep (se 2 (by rfl) ⟨3193080, by rfl⟩ : syracuseStep 8514881 = 6386161) B6386161
theorem B6466891 : Blo 1680040 6466891 := bstep (se 1 (by rfl) ⟨4850168, by rfl⟩ : syracuseStep 6466891 = 9700337) B9700337
theorem B5672267 : Blo 1680040 5672267 := bstep (se 1 (by rfl) ⟨4254200, by rfl⟩ : syracuseStep 5672267 = 8508401) B8508401
theorem B4255051 : Blo 1680040 4255051 := bstep (se 1 (by rfl) ⟨3191288, by rfl⟩ : syracuseStep 4255051 = 6382577) B6382577
theorem B3591499 : Blo 1680040 3591499 := bstep (se 1 (by rfl) ⟨2693624, by rfl⟩ : syracuseStep 3591499 = 5387249) B5387249
theorem B4787549 : Blo 1680040 4787549 := bstep (se 3 (by rfl) ⟨897665, by rfl⟩ : syracuseStep 4787549 = 1795331) B1795331
theorem B3190195 : Blo 1680040 3190195 := bstep (se 1 (by rfl) ⟨2392646, by rfl⟩ : syracuseStep 3190195 = 4785293) B4785293
theorem B2837963 : Blo 1680040 2837963 := bstep (se 1 (by rfl) ⟨2128472, by rfl⟩ : syracuseStep 2837963 = 4256945) B4256945
theorem B4255193 : Blo 1680040 4255193 := bstep (se 2 (by rfl) ⟨1595697, by rfl⟩ : syracuseStep 4255193 = 3191395) B3191395
theorem B7769603 : Blo 1680040 7769603 := bstep (se 1 (by rfl) ⟨5827202, by rfl⟩ : syracuseStep 7769603 = 11654405) B11654405
theorem B3780107 : Blo 1680040 3780107 := bstep (se 1 (by rfl) ⟨2835080, by rfl⟩ : syracuseStep 3780107 = 5670161) B5670161
theorem B6385175 : Blo 1680040 6385175 := bstep (se 1 (by rfl) ⟨4788881, by rfl⟩ : syracuseStep 6385175 = 9577763) B9577763
theorem B3780161 : Blo 1680040 3780161 := bstep (se 2 (by rfl) ⟨1417560, by rfl⟩ : syracuseStep 3780161 = 2835121) B2835121
theorem B2838091 : Blo 1680040 2838091 := bstep (se 1 (by rfl) ⟨2128568, by rfl⟩ : syracuseStep 2838091 = 4257137) B4257137
theorem B5672537 : Blo 1680040 5672537 := bstep (se 2 (by rfl) ⟨2127201, by rfl⟩ : syracuseStep 5672537 = 4254403) B4254403
theorem B3190423 : Blo 1680040 3190423 := bstep (se 1 (by rfl) ⟨2392817, by rfl⟩ : syracuseStep 3190423 = 4785635) B4785635
theorem B4607639 : Blo 1680040 4607639 := bstep (se 1 (by rfl) ⟨3455729, by rfl⟩ : syracuseStep 4607639 = 6911459) B6911459
theorem B3452633 : Blo 1680040 3452633 := bstep (se 2 (by rfl) ⟨1294737, by rfl⟩ : syracuseStep 3452633 = 2589475) B2589475
theorem B2838233 : Blo 1680040 2838233 := bstep (se 2 (by rfl) ⟨1064337, by rfl⟩ : syracuseStep 2838233 = 2128675) B2128675
theorem B56782577 : Blo 1680040 56782577 := bstep (se 2 (by rfl) ⟨21293466, by rfl⟩ : syracuseStep 56782577 = 42586933) B42586933
theorem B3190529 : Blo 1680040 3190529 := bstep (se 2 (by rfl) ⟨1196448, by rfl⟩ : syracuseStep 3190529 = 2392897) B2392897
theorem B2952983 : Blo 1680040 2952983 := bstep (se 1 (by rfl) ⟨2214737, by rfl⟩ : syracuseStep 2952983 = 4429475) B4429475
theorem B3780377 : Blo 1680040 3780377 := bstep (se 2 (by rfl) ⟨1417641, by rfl⟩ : syracuseStep 3780377 = 2835283) B2835283
theorem B2838361 : Blo 1680040 2838361 := bstep (se 2 (by rfl) ⟨1064385, by rfl⟩ : syracuseStep 2838361 = 2128771) B2128771
theorem B8744797 : Blo 1680040 8744797 := bstep (se 3 (by rfl) ⟨1639649, by rfl⟩ : syracuseStep 8744797 = 3279299) B3279299
theorem B3780467 : Blo 1680040 3780467 := bstep (se 1 (by rfl) ⟨2835350, by rfl⟩ : syracuseStep 3780467 = 5670701) B5670701
theorem B8507267 : Blo 1680040 8507267 := bstep (se 1 (by rfl) ⟨6380450, by rfl⟩ : syracuseStep 8507267 = 12760901) B12760901
theorem B3780503 : Blo 1680040 3780503 := bstep (se 1 (by rfl) ⟨2835377, by rfl⟩ : syracuseStep 3780503 = 5670755) B5670755
theorem B3190681 : Blo 1680040 3190681 := bstep (se 2 (by rfl) ⟨1196505, by rfl⟩ : syracuseStep 3190681 = 2393011) B2393011
theorem B3780683 : Blo 1680040 3780683 := bstep (se 1 (by rfl) ⟨2835512, by rfl⟩ : syracuseStep 3780683 = 5671025) B5671025
theorem B11497565 : Blo 1680040 11497565 := bstep (se 3 (by rfl) ⟨2155793, by rfl⟩ : syracuseStep 11497565 = 4311587) B4311587
theorem B3780737 : Blo 1680040 3780737 := bstep (se 2 (by rfl) ⟨1417776, by rfl⟩ : syracuseStep 3780737 = 2835553) B2835553
theorem B3592345 : Blo 1680040 3592345 := bstep (se 2 (by rfl) ⟨1347129, by rfl⟩ : syracuseStep 3592345 = 2694259) B2694259
theorem B5673239 : Blo 1680040 5673239 := bstep (se 1 (by rfl) ⟨4254929, by rfl⟩ : syracuseStep 5673239 = 8509859) B8509859
theorem B4256023 : Blo 1680040 4256023 := bstep (se 1 (by rfl) ⟨3192017, by rfl⟩ : syracuseStep 4256023 = 6384035) B6384035
theorem B7180589 : Blo 1680040 7180589 := bstep (se 3 (by rfl) ⟨1346360, by rfl⟩ : syracuseStep 7180589 = 2692721) B2692721
theorem B5386571 : Blo 1680040 5386571 := bstep (se 1 (by rfl) ⟨4039928, by rfl⟩ : syracuseStep 5386571 = 8079857) B8079857
theorem B11505995 : Blo 1680040 11505995 := bstep (se 1 (by rfl) ⟨8629496, by rfl⟩ : syracuseStep 11505995 = 17258993) B17258993
theorem B3780953 : Blo 1680040 3780953 := bstep (se 2 (by rfl) ⟨1417857, by rfl⟩ : syracuseStep 3780953 = 2835715) B2835715
theorem B4542809 : Blo 1680040 4542809 := bstep (se 2 (by rfl) ⟨1703553, by rfl⟩ : syracuseStep 4542809 = 3407107) B3407107
theorem B3781043 : Blo 1680040 3781043 := bstep (se 1 (by rfl) ⟨2835782, by rfl⟩ : syracuseStep 3781043 = 5671565) B5671565
theorem B3781079 : Blo 1680040 3781079 := bstep (se 1 (by rfl) ⟨2835809, by rfl⟩ : syracuseStep 3781079 = 5671619) B5671619
theorem B12767705 : Blo 1680040 12767705 := bstep (se 2 (by rfl) ⟨4787889, by rfl⟩ : syracuseStep 12767705 = 9575779) B9575779
theorem B2019863 : Blo 1680040 2019863 := bstep (se 1 (by rfl) ⟨1514897, by rfl⟩ : syracuseStep 2019863 = 3029795) B3029795
theorem B7664203 : Blo 1680040 7664203 := bstep (se 1 (by rfl) ⟨5748152, by rfl⟩ : syracuseStep 7664203 = 11496305) B11496305
theorem B3781259 : Blo 1680040 3781259 := bstep (se 1 (by rfl) ⟨2835944, by rfl⟩ : syracuseStep 3781259 = 5671889) B5671889
theorem B3781313 : Blo 1680040 3781313 := bstep (se 2 (by rfl) ⟨1417992, by rfl⟩ : syracuseStep 3781313 = 2835985) B2835985
theorem B4256459 : Blo 1680040 4256459 := bstep (se 1 (by rfl) ⟨3192344, by rfl⟩ : syracuseStep 4256459 = 6384689) B6384689
theorem B6386435 : Blo 1680040 6386435 := bstep (se 1 (by rfl) ⟨4789826, by rfl⟩ : syracuseStep 6386435 = 9579653) B9579653
theorem B9573137 : Blo 1680040 9573137 := bstep (se 2 (by rfl) ⟨3589926, by rfl⟩ : syracuseStep 9573137 = 7179853) B7179853
theorem B5673779 : Blo 1680040 5673779 := bstep (se 1 (by rfl) ⟨4255334, by rfl⟩ : syracuseStep 5673779 = 8510669) B8510669
theorem B2126731 : Blo 1680040 2126731 := bstep (se 1 (by rfl) ⟨1595048, by rfl⟩ : syracuseStep 2126731 = 3190097) B3190097
theorem B3781529 : Blo 1680040 3781529 := bstep (se 2 (by rfl) ⟨1418073, by rfl⟩ : syracuseStep 3781529 = 2836147) B2836147
theorem B6058925 : Blo 1680040 6058925 := bstep (se 3 (by rfl) ⟨1136048, by rfl⟩ : syracuseStep 6058925 = 2272097) B2272097
theorem B2692055 : Blo 1680040 2692055 := bstep (se 1 (by rfl) ⟨2019041, by rfl⟩ : syracuseStep 2692055 = 4038083) B4038083
theorem B122713049 : Blo 1680040 122713049 := bstep (se 2 (by rfl) ⟨46017393, by rfl⟩ : syracuseStep 122713049 = 92034787) B92034787
theorem B3781619 : Blo 1680040 3781619 := bstep (se 1 (by rfl) ⟨2836214, by rfl⟩ : syracuseStep 3781619 = 5672429) B5672429
theorem B3781655 : Blo 1680040 3781655 := bstep (se 1 (by rfl) ⟨2836241, by rfl⟩ : syracuseStep 3781655 = 5672483) B5672483
theorem B2520089 : Blo 1680040 2520089 := bstep (se 2 (by rfl) ⟨945033, by rfl⟩ : syracuseStep 2520089 = 1890067) B1890067
theorem B5674049 : Blo 1680040 5674049 := bstep (se 2 (by rfl) ⟨2127768, by rfl⟩ : syracuseStep 5674049 = 4255537) B4255537
theorem B13636673 : Blo 1680040 13636673 := bstep (se 2 (by rfl) ⟨5113752, by rfl⟩ : syracuseStep 13636673 = 10227505) B10227505
theorem B4256833 : Blo 1680040 4256833 := bstep (se 2 (by rfl) ⟨1596312, by rfl⟩ : syracuseStep 4256833 = 3192625) B3192625
theorem B2520203 : Blo 1680040 2520203 := bstep (se 1 (by rfl) ⟨1890152, by rfl⟩ : syracuseStep 2520203 = 3780305) B3780305
theorem B2520215 : Blo 1680040 2520215 := bstep (se 1 (by rfl) ⟨1890161, by rfl⟩ : syracuseStep 2520215 = 3780323) B3780323
theorem B2126999 : Blo 1680040 2126999 := bstep (se 1 (by rfl) ⟨1595249, by rfl⟩ : syracuseStep 2126999 = 3190499) B3190499
theorem B3191987 : Blo 1680040 3191987 := bstep (se 1 (by rfl) ⟨2393990, by rfl⟩ : syracuseStep 3191987 = 4787981) B4787981
theorem B3781835 : Blo 1680040 3781835 := bstep (se 1 (by rfl) ⟨2836376, by rfl⟩ : syracuseStep 3781835 = 5672753) B5672753
theorem B2020555 : Blo 1680040 2020555 := bstep (se 1 (by rfl) ⟨1515416, by rfl⟩ : syracuseStep 2020555 = 3030833) B3030833
theorem B2520281 : Blo 1680040 2520281 := bstep (se 2 (by rfl) ⟨945105, by rfl⟩ : syracuseStep 2520281 = 1890211) B1890211
theorem B3781889 : Blo 1680040 3781889 := bstep (se 2 (by rfl) ⟨1418208, by rfl⟩ : syracuseStep 3781889 = 2836417) B2836417
theorem B10229009 : Blo 1680040 10229009 := bstep (se 2 (by rfl) ⟨3835878, by rfl⟩ : syracuseStep 10229009 = 7671757) B7671757
theorem B2520395 : Blo 1680040 2520395 := bstep (se 1 (by rfl) ⟨1890296, by rfl⟩ : syracuseStep 2520395 = 3780593) B3780593
theorem B3192139 : Blo 1680040 3192139 := bstep (se 1 (by rfl) ⟨2394104, by rfl⟩ : syracuseStep 3192139 = 4788209) B4788209
theorem B2520407 : Blo 1680040 2520407 := bstep (se 1 (by rfl) ⟨1890305, by rfl⟩ : syracuseStep 2520407 = 3780611) B3780611
theorem B2520473 : Blo 1680040 2520473 := bstep (se 2 (by rfl) ⟨945177, by rfl⟩ : syracuseStep 2520473 = 1890355) B1890355
theorem B6059443 : Blo 1680040 6059443 := bstep (se 1 (by rfl) ⟨4544582, by rfl⟩ : syracuseStep 6059443 = 9089165) B9089165
theorem B3782105 : Blo 1680040 3782105 := bstep (se 2 (by rfl) ⟨1418289, by rfl⟩ : syracuseStep 3782105 = 2836579) B2836579
theorem B2520587 : Blo 1680040 2520587 := bstep (se 1 (by rfl) ⟨1890440, by rfl⟩ : syracuseStep 2520587 = 3780881) B3780881
theorem B2692619 : Blo 1680040 2692619 := bstep (se 1 (by rfl) ⟨2019464, by rfl⟩ : syracuseStep 2692619 = 4038929) B4038929
theorem B2520599 : Blo 1680040 2520599 := bstep (se 1 (by rfl) ⟨1890449, by rfl⟩ : syracuseStep 2520599 = 3780899) B3780899
theorem B3782195 : Blo 1680040 3782195 := bstep (se 1 (by rfl) ⟨2836646, by rfl⟩ : syracuseStep 3782195 = 5673293) B5673293
theorem B3782231 : Blo 1680040 3782231 := bstep (se 1 (by rfl) ⟨2836673, by rfl⟩ : syracuseStep 3782231 = 5673347) B5673347
theorem B2520665 : Blo 1680040 2520665 := bstep (se 2 (by rfl) ⟨945249, by rfl⟩ : syracuseStep 2520665 = 1890499) B1890499
theorem B4789849 : Blo 1680040 4789849 := bstep (se 2 (by rfl) ⟨1796193, by rfl⟩ : syracuseStep 4789849 = 3592387) B3592387
theorem B5674589 : Blo 1680040 5674589 := bstep (se 3 (by rfl) ⟨1063985, by rfl⟩ : syracuseStep 5674589 = 2127971) B2127971
theorem B4257431 : Blo 1680040 4257431 := bstep (se 1 (by rfl) ⟨3193073, by rfl⟩ : syracuseStep 4257431 = 6386147) B6386147
theorem B3192473 : Blo 1680040 3192473 := bstep (se 2 (by rfl) ⟨1197177, by rfl⟩ : syracuseStep 3192473 = 2394355) B2394355
theorem B2520779 : Blo 1680040 2520779 := bstep (se 1 (by rfl) ⟨1890584, by rfl⟩ : syracuseStep 2520779 = 3781169) B3781169
theorem B2520791 : Blo 1680040 2520791 := bstep (se 1 (by rfl) ⟨1890593, by rfl⟩ : syracuseStep 2520791 = 3781187) B3781187
theorem B11507417 : Blo 1680040 11507417 := bstep (se 2 (by rfl) ⟨4315281, by rfl⟩ : syracuseStep 11507417 = 8630563) B8630563
theorem B3782411 : Blo 1680040 3782411 := bstep (se 1 (by rfl) ⟨2836808, by rfl⟩ : syracuseStep 3782411 = 5673617) B5673617
theorem B2520857 : Blo 1680040 2520857 := bstep (se 2 (by rfl) ⟨945321, by rfl⟩ : syracuseStep 2520857 = 1890643) B1890643
theorem B1890103 : Blo 1680040 1890103 := bstep (se 1 (by rfl) ⟨1417577, by rfl⟩ : syracuseStep 1890103 = 2835155) B2835155
theorem B3782465 : Blo 1680040 3782465 := bstep (se 2 (by rfl) ⟨1418424, by rfl⟩ : syracuseStep 3782465 = 2836849) B2836849
theorem B2127703 : Blo 1680040 2127703 := bstep (se 1 (by rfl) ⟨1595777, by rfl⟩ : syracuseStep 2127703 = 3191555) B3191555
theorem B6379357 : Blo 1680040 6379357 := bstep (se 3 (by rfl) ⟨1196129, by rfl⟩ : syracuseStep 6379357 = 2392259) B2392259
theorem B43079525 : Blo 1680040 43079525 := bstep (se 4 (by rfl) ⟨4038705, by rfl⟩ : syracuseStep 43079525 = 8077411) B8077411
theorem B2520971 : Blo 1680040 2520971 := bstep (se 1 (by rfl) ⟨1890728, by rfl⟩ : syracuseStep 2520971 = 3781457) B3781457
theorem B2520983 : Blo 1680040 2520983 := bstep (se 1 (by rfl) ⟨1890737, by rfl⟩ : syracuseStep 2520983 = 3781475) B3781475
theorem B15333299 : Blo 1680040 15333299 := bstep (se 1 (by rfl) ⟨11499974, by rfl⟩ : syracuseStep 15333299 = 22999949) B22999949
theorem B4151243 : Blo 1680040 4151243 := bstep (se 1 (by rfl) ⟨3113432, by rfl⟩ : syracuseStep 4151243 = 6226865) B6226865
theorem B2521049 : Blo 1680040 2521049 := bstep (se 2 (by rfl) ⟨945393, by rfl⟩ : syracuseStep 2521049 = 1890787) B1890787
theorem B1890283 : Blo 1680040 1890283 := bstep (se 1 (by rfl) ⟨1417712, by rfl⟩ : syracuseStep 1890283 = 2835425) B2835425
theorem B14358545 : Blo 1680040 14358545 := bstep (se 2 (by rfl) ⟨5384454, by rfl⟩ : syracuseStep 14358545 = 10768909) B10768909
theorem B3782681 : Blo 1680040 3782681 := bstep (se 2 (by rfl) ⟨1418505, by rfl⟩ : syracuseStep 3782681 = 2837011) B2837011
theorem B2521163 : Blo 1680040 2521163 := bstep (se 1 (by rfl) ⟨1890872, by rfl⟩ : syracuseStep 2521163 = 3781745) B3781745
theorem B1890391 : Blo 1680040 1890391 := bstep (se 1 (by rfl) ⟨1417793, by rfl⟩ : syracuseStep 1890391 = 2835587) B2835587
theorem B2521175 : Blo 1680040 2521175 := bstep (se 1 (by rfl) ⟨1890881, by rfl⟩ : syracuseStep 2521175 = 3781763) B3781763
theorem B3782771 : Blo 1680040 3782771 := bstep (se 1 (by rfl) ⟨2837078, by rfl⟩ : syracuseStep 3782771 = 5674157) B5674157
theorem B21543043 : Blo 1680040 21543043 := bstep (se 1 (by rfl) ⟨16157282, by rfl⟩ : syracuseStep 21543043 = 32314565) B32314565
theorem B3782807 : Blo 1680040 3782807 := bstep (se 1 (by rfl) ⟨2837105, by rfl⟩ : syracuseStep 3782807 = 5674211) B5674211
theorem B9091223 : Blo 1680040 9091223 := bstep (se 1 (by rfl) ⟨6818417, by rfl⟩ : syracuseStep 9091223 = 13636835) B13636835
theorem B2521241 : Blo 1680040 2521241 := bstep (se 2 (by rfl) ⟨945465, by rfl⟩ : syracuseStep 2521241 = 1890931) B1890931
theorem B6740147 : Blo 1680040 6740147 := bstep (se 1 (by rfl) ⟨5055110, by rfl⟩ : syracuseStep 6740147 = 10110221) B10110221
theorem B7182553 : Blo 1680040 7182553 := bstep (se 2 (by rfl) ⟨2693457, by rfl⟩ : syracuseStep 7182553 = 5386915) B5386915
theorem B1890571 : Blo 1680040 1890571 := bstep (se 1 (by rfl) ⟨1417928, by rfl⟩ : syracuseStep 1890571 = 2835857) B2835857
theorem B2521355 : Blo 1680040 2521355 := bstep (se 1 (by rfl) ⟨1891016, by rfl⟩ : syracuseStep 2521355 = 3782033) B3782033
theorem B2521367 : Blo 1680040 2521367 := bstep (se 1 (by rfl) ⟨1891025, by rfl⟩ : syracuseStep 2521367 = 3782051) B3782051
theorem B3193111 : Blo 1680040 3193111 := bstep (se 1 (by rfl) ⟨2394833, by rfl⟩ : syracuseStep 3193111 = 4789667) B4789667
theorem B26589485 : Blo 1680040 26589485 := bstep (se 3 (by rfl) ⟨4985528, by rfl⟩ : syracuseStep 26589485 = 9971057) B9971057
theorem B3782987 : Blo 1680040 3782987 := bstep (se 1 (by rfl) ⟨2837240, by rfl⟩ : syracuseStep 3782987 = 5674481) B5674481
theorem B2521433 : Blo 1680040 2521433 := bstep (se 2 (by rfl) ⟨945537, by rfl⟩ : syracuseStep 2521433 = 1891075) B1891075
theorem B1890679 : Blo 1680040 1890679 := bstep (se 1 (by rfl) ⟨1418009, by rfl⟩ : syracuseStep 1890679 = 2836019) B2836019
theorem B3783041 : Blo 1680040 3783041 := bstep (se 2 (by rfl) ⟨1418640, by rfl⟩ : syracuseStep 3783041 = 2837281) B2837281
theorem B4037015 : Blo 1680040 4037015 := bstep (se 1 (by rfl) ⟨3027761, by rfl⟩ : syracuseStep 4037015 = 6055523) B6055523
theorem B2521547 : Blo 1680040 2521547 := bstep (se 1 (by rfl) ⟨1891160, by rfl⟩ : syracuseStep 2521547 = 3782321) B3782321
theorem B2521559 : Blo 1680040 2521559 := bstep (se 1 (by rfl) ⟨1891169, by rfl⟩ : syracuseStep 2521559 = 3782339) B3782339
theorem B7666193 : Blo 1680040 7666193 := bstep (se 2 (by rfl) ⟨2874822, by rfl⟩ : syracuseStep 7666193 = 5749645) B5749645
theorem B2521625 : Blo 1680040 2521625 := bstep (se 2 (by rfl) ⟨945609, by rfl⟩ : syracuseStep 2521625 = 1891219) B1891219
theorem B1890859 : Blo 1680040 1890859 := bstep (se 1 (by rfl) ⟨1418144, by rfl⟩ : syracuseStep 1890859 = 2836289) B2836289
theorem B3783257 : Blo 1680040 3783257 := bstep (se 2 (by rfl) ⟨1418721, by rfl⟩ : syracuseStep 3783257 = 2837443) B2837443
theorem B2521739 : Blo 1680040 2521739 := bstep (se 1 (by rfl) ⟨1891304, by rfl⟩ : syracuseStep 2521739 = 3782609) B3782609
theorem B1890967 : Blo 1680040 1890967 := bstep (se 1 (by rfl) ⟨1418225, by rfl⟩ : syracuseStep 1890967 = 2836451) B2836451
theorem B2521751 : Blo 1680040 2521751 := bstep (se 1 (by rfl) ⟨1891313, by rfl⟩ : syracuseStep 2521751 = 3782627) B3782627
theorem B3783347 : Blo 1680040 3783347 := bstep (se 1 (by rfl) ⟨2837510, by rfl⟩ : syracuseStep 3783347 = 5675021) B5675021
theorem B5675723 : Blo 1680040 5675723 := bstep (se 1 (by rfl) ⟨4256792, by rfl⟩ : syracuseStep 5675723 = 8513585) B8513585
theorem B3783383 : Blo 1680040 3783383 := bstep (se 1 (by rfl) ⟨2837537, by rfl⟩ : syracuseStep 3783383 = 5675075) B5675075
theorem B2521817 : Blo 1680040 2521817 := bstep (se 2 (by rfl) ⟨945681, by rfl⟩ : syracuseStep 2521817 = 1891363) B1891363
theorem B7666397 : Blo 1680040 7666397 := bstep (se 3 (by rfl) ⟨1437449, by rfl⟩ : syracuseStep 7666397 = 2874899) B2874899
theorem B12761873 : Blo 1680040 12761873 := bstep (se 2 (by rfl) ⟨4785702, by rfl⟩ : syracuseStep 12761873 = 9571405) B9571405
theorem B10771217 : Blo 1680040 10771217 := bstep (se 2 (by rfl) ⟨4039206, by rfl⟩ : syracuseStep 10771217 = 8078413) B8078413
theorem B1891147 : Blo 1680040 1891147 := bstep (se 1 (by rfl) ⟨1418360, by rfl⟩ : syracuseStep 1891147 = 2836721) B2836721
theorem B2521931 : Blo 1680040 2521931 := bstep (se 1 (by rfl) ⟨1891448, by rfl⟩ : syracuseStep 2521931 = 3782897) B3782897
theorem B2521943 : Blo 1680040 2521943 := bstep (se 1 (by rfl) ⟨1891457, by rfl⟩ : syracuseStep 2521943 = 3782915) B3782915
theorem B12934019 : Blo 1680040 12934019 := bstep (se 1 (by rfl) ⟨9700514, by rfl⟩ : syracuseStep 12934019 = 19401029) B19401029
theorem B3783563 : Blo 1680040 3783563 := bstep (se 1 (by rfl) ⟨2837672, by rfl⟩ : syracuseStep 3783563 = 5675345) B5675345
theorem B2522009 : Blo 1680040 2522009 := bstep (se 2 (by rfl) ⟨945753, by rfl⟩ : syracuseStep 2522009 = 1891507) B1891507
theorem B1891255 : Blo 1680040 1891255 := bstep (se 1 (by rfl) ⟨1418441, by rfl⟩ : syracuseStep 1891255 = 2836883) B2836883
theorem B3783617 : Blo 1680040 3783617 := bstep (se 2 (by rfl) ⟨1418856, by rfl⟩ : syracuseStep 3783617 = 2837713) B2837713
theorem B5675993 : Blo 1680040 5675993 := bstep (se 2 (by rfl) ⟨2128497, by rfl⟩ : syracuseStep 5675993 = 4256995) B4256995
theorem B2522123 : Blo 1680040 2522123 := bstep (se 1 (by rfl) ⟨1891592, by rfl⟩ : syracuseStep 2522123 = 3783185) B3783185
theorem B2522135 : Blo 1680040 2522135 := bstep (se 1 (by rfl) ⟨1891601, by rfl⟩ : syracuseStep 2522135 = 3783203) B3783203
theorem B6904883 : Blo 1680040 6904883 := bstep (se 1 (by rfl) ⟨5178662, by rfl⟩ : syracuseStep 6904883 = 10357325) B10357325
theorem B6380633 : Blo 1680040 6380633 := bstep (se 2 (by rfl) ⟨2392737, by rfl⟩ : syracuseStep 6380633 = 4785475) B4785475
theorem B2522201 : Blo 1680040 2522201 := bstep (se 2 (by rfl) ⟨945825, by rfl⟩ : syracuseStep 2522201 = 1891651) B1891651
theorem B1891435 : Blo 1680040 1891435 := bstep (se 1 (by rfl) ⟨1418576, by rfl⟩ : syracuseStep 1891435 = 2837153) B2837153
theorem B4037783 : Blo 1680040 4037783 := bstep (se 1 (by rfl) ⟨3028337, by rfl⟩ : syracuseStep 4037783 = 6056675) B6056675
theorem B7183511 : Blo 1680040 7183511 := bstep (se 1 (by rfl) ⟨5387633, by rfl⟩ : syracuseStep 7183511 = 10775267) B10775267
theorem B3783833 : Blo 1680040 3783833 := bstep (se 2 (by rfl) ⟨1418937, by rfl⟩ : syracuseStep 3783833 = 2837875) B2837875
theorem B2522315 : Blo 1680040 2522315 := bstep (se 1 (by rfl) ⟨1891736, by rfl⟩ : syracuseStep 2522315 = 3783473) B3783473
theorem B1891543 : Blo 1680040 1891543 := bstep (se 1 (by rfl) ⟨1418657, by rfl⟩ : syracuseStep 1891543 = 2837315) B2837315
theorem B2522327 : Blo 1680040 2522327 := bstep (se 1 (by rfl) ⟨1891745, by rfl⟩ : syracuseStep 2522327 = 3783491) B3783491
theorem B3783923 : Blo 1680040 3783923 := bstep (se 1 (by rfl) ⟨2837942, by rfl⟩ : syracuseStep 3783923 = 5675885) B5675885
theorem B3783959 : Blo 1680040 3783959 := bstep (se 1 (by rfl) ⟨2837969, by rfl⟩ : syracuseStep 3783959 = 5675939) B5675939
theorem B2522393 : Blo 1680040 2522393 := bstep (se 2 (by rfl) ⟨945897, by rfl⟩ : syracuseStep 2522393 = 1891795) B1891795
theorem B16153901 : Blo 1680040 16153901 := bstep (se 3 (by rfl) ⟨3028856, by rfl⟩ : syracuseStep 16153901 = 6057713) B6057713
theorem B1891723 : Blo 1680040 1891723 := bstep (se 1 (by rfl) ⟨1418792, by rfl⟩ : syracuseStep 1891723 = 2837585) B2837585
theorem B2522507 : Blo 1680040 2522507 := bstep (se 1 (by rfl) ⟨1891880, by rfl⟩ : syracuseStep 2522507 = 3783761) B3783761
theorem B2522519 : Blo 1680040 2522519 := bstep (se 1 (by rfl) ⟨1891889, by rfl⟩ : syracuseStep 2522519 = 3783779) B3783779
theorem B3784139 : Blo 1680040 3784139 := bstep (se 1 (by rfl) ⟨2838104, by rfl⟩ : syracuseStep 3784139 = 5676209) B5676209
theorem B2522585 : Blo 1680040 2522585 := bstep (se 2 (by rfl) ⟨945969, by rfl⟩ : syracuseStep 2522585 = 1891939) B1891939
theorem B1891831 : Blo 1680040 1891831 := bstep (se 1 (by rfl) ⟨1418873, by rfl⟩ : syracuseStep 1891831 = 2837747) B2837747
theorem B3030529 : Blo 1680040 3030529 := bstep (se 2 (by rfl) ⟨1136448, by rfl⟩ : syracuseStep 3030529 = 2272897) B2272897
theorem B3784193 : Blo 1680040 3784193 := bstep (se 2 (by rfl) ⟨1419072, by rfl⟩ : syracuseStep 3784193 = 2838145) B2838145
theorem B8510993 : Blo 1680040 8510993 := bstep (se 2 (by rfl) ⟨3191622, by rfl⟩ : syracuseStep 8510993 = 6383245) B6383245
theorem B2522699 : Blo 1680040 2522699 := bstep (se 1 (by rfl) ⟨1892024, by rfl⟩ : syracuseStep 2522699 = 3784049) B3784049
theorem B2522711 : Blo 1680040 2522711 := bstep (se 1 (by rfl) ⟨1892033, by rfl⟩ : syracuseStep 2522711 = 3784067) B3784067
theorem B5676695 : Blo 1680040 5676695 := bstep (se 1 (by rfl) ⟨4257521, by rfl⟩ : syracuseStep 5676695 = 8515043) B8515043
theorem B2522777 : Blo 1680040 2522777 := bstep (se 2 (by rfl) ⟨946041, by rfl⟩ : syracuseStep 2522777 = 1892083) B1892083
theorem B1892011 : Blo 1680040 1892011 := bstep (se 1 (by rfl) ⟨1419008, by rfl⟩ : syracuseStep 1892011 = 2838017) B2838017
theorem B8511155 : Blo 1680040 8511155 := bstep (se 1 (by rfl) ⟨6383366, by rfl⟩ : syracuseStep 8511155 = 12766733) B12766733
theorem B3784409 : Blo 1680040 3784409 := bstep (se 2 (by rfl) ⟨1419153, by rfl⟩ : syracuseStep 3784409 = 2838307) B2838307
theorem B2522891 : Blo 1680040 2522891 := bstep (se 1 (by rfl) ⟨1892168, by rfl⟩ : syracuseStep 2522891 = 3784337) B3784337
theorem B1892119 : Blo 1680040 1892119 := bstep (se 1 (by rfl) ⟨1419089, by rfl⟩ : syracuseStep 1892119 = 2838179) B2838179
theorem B2522903 : Blo 1680040 2522903 := bstep (se 1 (by rfl) ⟨1892177, by rfl⟩ : syracuseStep 2522903 = 3784355) B3784355
theorem B12771107 : Blo 1680040 12771107 := bstep (se 1 (by rfl) ⟨9578330, by rfl⟩ : syracuseStep 12771107 = 19156661) B19156661
theorem B3784499 : Blo 1680040 3784499 := bstep (se 1 (by rfl) ⟨2838374, by rfl⟩ : syracuseStep 3784499 = 5676749) B5676749
theorem B3784535 : Blo 1680040 3784535 := bstep (se 1 (by rfl) ⟨2838401, by rfl⟩ : syracuseStep 3784535 = 5676803) B5676803
theorem B2522969 : Blo 1680040 2522969 := bstep (se 2 (by rfl) ⟨946113, by rfl⟩ : syracuseStep 2522969 = 1892227) B1892227
theorem B12115889 : Blo 1680040 12115889 := bstep (se 2 (by rfl) ⟨4543458, by rfl⟩ : syracuseStep 12115889 = 9086917) B9086917
theorem B36356141 : Blo 1680040 36356141 := bstep (se 3 (by rfl) ⟨6816776, by rfl⟩ : syracuseStep 36356141 = 13633553) B13633553
theorem B4784417 : Blo 1680040 4784417 := bstep (se 2 (by rfl) ⟨1794156, by rfl⟩ : syracuseStep 4784417 = 3588313) B3588313
theorem B9576737 : Blo 1680040 9576737 := bstep (se 2 (by rfl) ⟨3591276, by rfl⟩ : syracuseStep 9576737 = 7182553) B7182553
theorem B8511803 : Blo 1680040 8511803 := bstep (se 1 (by rfl) ⟨6383852, by rfl⟩ : syracuseStep 8511803 = 12767705) B12767705
theorem B8511965 : Blo 1680040 8511965 := bstep (se 3 (by rfl) ⟨1595993, by rfl⟩ : syracuseStep 8511965 = 3191987) B3191987
theorem B6382091 : Blo 1680040 6382091 := bstep (se 1 (by rfl) ⟨4786568, by rfl⟩ : syracuseStep 6382091 = 9573137) B9573137
theorem B4039283 : Blo 1680040 4039283 := bstep (se 1 (by rfl) ⟨3029462, by rfl⟩ : syracuseStep 4039283 = 6058925) B6058925
theorem B1680059 : Blo 1680040 1680059 := bstep (se 1 (by rfl) ⟨1260044, by rfl⟩ : syracuseStep 1680059 = 2520089) B2520089
theorem B1680135 : Blo 1680040 1680135 := bstep (se 1 (by rfl) ⟨1260101, by rfl⟩ : syracuseStep 1680135 = 2520203) B2520203
theorem B1680143 : Blo 1680040 1680143 := bstep (se 1 (by rfl) ⟨1260107, by rfl⟩ : syracuseStep 1680143 = 2520215) B2520215
theorem B8512289 : Blo 1680040 8512289 := bstep (se 2 (by rfl) ⟨3192108, by rfl⟩ : syracuseStep 8512289 = 6384217) B6384217
theorem B1680187 : Blo 1680040 1680187 := bstep (se 1 (by rfl) ⟨1260140, by rfl⟩ : syracuseStep 1680187 = 2520281) B2520281
theorem B16147289 : Blo 1680040 16147289 := bstep (se 2 (by rfl) ⟨6055233, by rfl⟩ : syracuseStep 16147289 = 12110467) B12110467
theorem B1680263 : Blo 1680040 1680263 := bstep (se 1 (by rfl) ⟨1260197, by rfl⟩ : syracuseStep 1680263 = 2520395) B2520395
theorem B1680271 : Blo 1680040 1680271 := bstep (se 1 (by rfl) ⟨1260203, by rfl⟩ : syracuseStep 1680271 = 2520407) B2520407
theorem B48456629 : Blo 1680040 48456629 := bstep (se 5 (by rfl) ⟨2271404, by rfl⟩ : syracuseStep 48456629 = 4542809) B4542809
theorem B1680315 : Blo 1680040 1680315 := bstep (se 1 (by rfl) ⟨1260236, by rfl⟩ : syracuseStep 1680315 = 2520473) B2520473
theorem B1680391 : Blo 1680040 1680391 := bstep (se 1 (by rfl) ⟨1260293, by rfl⟩ : syracuseStep 1680391 = 2520587) B2520587
theorem B1795079 : Blo 1680040 1795079 := bstep (se 1 (by rfl) ⟨1346309, by rfl⟩ : syracuseStep 1795079 = 2692619) B2692619
theorem B1680399 : Blo 1680040 1680399 := bstep (se 1 (by rfl) ⟨1260299, by rfl⟩ : syracuseStep 1680399 = 2520599) B2520599
theorem B2835499 : Blo 1680040 2835499 := bstep (se 1 (by rfl) ⟨2126624, by rfl⟩ : syracuseStep 2835499 = 4253249) B4253249
theorem B6816811 : Blo 1680040 6816811 := bstep (se 1 (by rfl) ⟨5112608, by rfl⟩ : syracuseStep 6816811 = 10225217) B10225217
theorem B1680443 : Blo 1680040 1680443 := bstep (se 1 (by rfl) ⟨1260332, by rfl⟩ : syracuseStep 1680443 = 2520665) B2520665
theorem B1680519 : Blo 1680040 1680519 := bstep (se 1 (by rfl) ⟨1260389, by rfl⟩ : syracuseStep 1680519 = 2520779) B2520779
theorem B1680527 : Blo 1680040 1680527 := bstep (se 1 (by rfl) ⟨1260395, by rfl⟩ : syracuseStep 1680527 = 2520791) B2520791
theorem B2835641 : Blo 1680040 2835641 := bstep (se 2 (by rfl) ⟨1063365, by rfl⟩ : syracuseStep 2835641 = 2126731) B2126731
theorem B2393273 : Blo 1680040 2393273 := bstep (se 2 (by rfl) ⟨897477, by rfl⟩ : syracuseStep 2393273 = 1794955) B1794955
theorem B1680571 : Blo 1680040 1680571 := bstep (se 1 (by rfl) ⟨1260428, by rfl⟩ : syracuseStep 1680571 = 2520857) B2520857
theorem B1680647 : Blo 1680040 1680647 := bstep (se 1 (by rfl) ⟨1260485, by rfl⟩ : syracuseStep 1680647 = 2520971) B2520971
theorem B4785419 : Blo 1680040 4785419 := bstep (se 1 (by rfl) ⟨3589064, by rfl⟩ : syracuseStep 4785419 = 7178129) B7178129
theorem B1680655 : Blo 1680040 1680655 := bstep (se 1 (by rfl) ⟨1260491, by rfl⟩ : syracuseStep 1680655 = 2520983) B2520983
theorem B1680699 : Blo 1680040 1680699 := bstep (se 1 (by rfl) ⟨1260524, by rfl⟩ : syracuseStep 1680699 = 2521049) B2521049
theorem B1680775 : Blo 1680040 1680775 := bstep (se 1 (by rfl) ⟨1260581, by rfl⟩ : syracuseStep 1680775 = 2521163) B2521163
theorem B1680783 : Blo 1680040 1680783 := bstep (se 1 (by rfl) ⟨1260587, by rfl⟩ : syracuseStep 1680783 = 2521175) B2521175
theorem B6383033 : Blo 1680040 6383033 := bstep (se 2 (by rfl) ⟨2393637, by rfl⟩ : syracuseStep 6383033 = 4787275) B4787275
theorem B1680827 : Blo 1680040 1680827 := bstep (se 1 (by rfl) ⟨1260620, by rfl⟩ : syracuseStep 1680827 = 2521241) B2521241
theorem B1680903 : Blo 1680040 1680903 := bstep (se 1 (by rfl) ⟨1260677, by rfl⟩ : syracuseStep 1680903 = 2521355) B2521355
theorem B1680911 : Blo 1680040 1680911 := bstep (se 1 (by rfl) ⟨1260683, by rfl⟩ : syracuseStep 1680911 = 2521367) B2521367
theorem B1680955 : Blo 1680040 1680955 := bstep (se 1 (by rfl) ⟨1260716, by rfl⟩ : syracuseStep 1680955 = 2521433) B2521433
theorem B3884663 : Blo 1680040 3884663 := bstep (se 1 (by rfl) ⟨2913497, by rfl⟩ : syracuseStep 3884663 = 5826995) B5826995
theorem B10913399 : Blo 1680040 10913399 := bstep (se 1 (by rfl) ⟨8185049, by rfl⟩ : syracuseStep 10913399 = 16370099) B16370099
theorem B1681031 : Blo 1680040 1681031 := bstep (se 1 (by rfl) ⟨1260773, by rfl⟩ : syracuseStep 1681031 = 2521547) B2521547
theorem B1681039 : Blo 1680040 1681039 := bstep (se 1 (by rfl) ⟨1260779, by rfl⟩ : syracuseStep 1681039 = 2521559) B2521559
theorem B4785817 : Blo 1680040 4785817 := bstep (se 2 (by rfl) ⟨1794681, by rfl⟩ : syracuseStep 4785817 = 3589363) B3589363
theorem B1681083 : Blo 1680040 1681083 := bstep (se 1 (by rfl) ⟨1260812, by rfl⟩ : syracuseStep 1681083 = 2521625) B2521625
theorem B8513261 : Blo 1680040 8513261 := bstep (se 3 (by rfl) ⟨1596236, by rfl⟩ : syracuseStep 8513261 = 3192473) B3192473
theorem B28706561 : Blo 1680040 28706561 := bstep (se 2 (by rfl) ⟨10764960, by rfl⟩ : syracuseStep 28706561 = 21529921) B21529921
theorem B1681159 : Blo 1680040 1681159 := bstep (se 1 (by rfl) ⟨1260869, by rfl⟩ : syracuseStep 1681159 = 2521739) B2521739
theorem B1681167 : Blo 1680040 1681167 := bstep (se 1 (by rfl) ⟨1260875, by rfl⟩ : syracuseStep 1681167 = 2521751) B2521751
theorem B1681211 : Blo 1680040 1681211 := bstep (se 1 (by rfl) ⟨1260908, by rfl⟩ : syracuseStep 1681211 = 2521817) B2521817
theorem B2836343 : Blo 1680040 2836343 := bstep (se 1 (by rfl) ⟨2127257, by rfl⟩ : syracuseStep 2836343 = 4254515) B4254515
theorem B1681287 : Blo 1680040 1681287 := bstep (se 1 (by rfl) ⟨1260965, by rfl⟩ : syracuseStep 1681287 = 2521931) B2521931
theorem B1681295 : Blo 1680040 1681295 := bstep (se 1 (by rfl) ⟨1260971, by rfl⟩ : syracuseStep 1681295 = 2521943) B2521943
theorem B4786067 : Blo 1680040 4786067 := bstep (se 1 (by rfl) ⟨3589550, by rfl⟩ : syracuseStep 4786067 = 7179101) B7179101
theorem B5752723 : Blo 1680040 5752723 := bstep (se 1 (by rfl) ⟨4314542, by rfl⟩ : syracuseStep 5752723 = 8629085) B8629085
theorem B5670809 : Blo 1680040 5670809 := bstep (se 2 (by rfl) ⟨2126553, by rfl⟩ : syracuseStep 5670809 = 4253107) B4253107
theorem B4253593 : Blo 1680040 4253593 := bstep (se 2 (by rfl) ⟨1595097, by rfl⟩ : syracuseStep 4253593 = 3190195) B3190195
theorem B8079257 : Blo 1680040 8079257 := bstep (se 2 (by rfl) ⟨3029721, by rfl⟩ : syracuseStep 8079257 = 6059443) B6059443
theorem B1681339 : Blo 1680040 1681339 := bstep (se 1 (by rfl) ⟨1261004, by rfl⟩ : syracuseStep 1681339 = 2522009) B2522009
theorem B4040705 : Blo 1680040 4040705 := bstep (se 2 (by rfl) ⟨1515264, by rfl⟩ : syracuseStep 4040705 = 3030529) B3030529
theorem B1681415 : Blo 1680040 1681415 := bstep (se 1 (by rfl) ⟨1261061, by rfl⟩ : syracuseStep 1681415 = 2522123) B2522123
theorem B1681423 : Blo 1680040 1681423 := bstep (se 1 (by rfl) ⟨1261067, by rfl⟩ : syracuseStep 1681423 = 2522135) B2522135
theorem B2394127 : Blo 1680040 2394127 := bstep (se 1 (by rfl) ⟨1795595, by rfl⟩ : syracuseStep 2394127 = 3591191) B3591191
theorem B4253755 : Blo 1680040 4253755 := bstep (se 1 (by rfl) ⟨3190316, by rfl⟩ : syracuseStep 4253755 = 6380633) B6380633
theorem B7874621 : Blo 1680040 7874621 := bstep (se 3 (by rfl) ⟨1476491, by rfl⟩ : syracuseStep 7874621 = 2952983) B2952983
theorem B1681467 : Blo 1680040 1681467 := bstep (se 1 (by rfl) ⟨1261100, by rfl⟩ : syracuseStep 1681467 = 2522201) B2522201
theorem B1681543 : Blo 1680040 1681543 := bstep (se 1 (by rfl) ⟨1261157, by rfl⟩ : syracuseStep 1681543 = 2522315) B2522315
theorem B1681551 : Blo 1680040 1681551 := bstep (se 1 (by rfl) ⟨1261163, by rfl⟩ : syracuseStep 1681551 = 2522327) B2522327
theorem B1681595 : Blo 1680040 1681595 := bstep (se 1 (by rfl) ⟨1261196, by rfl⟩ : syracuseStep 1681595 = 2522393) B2522393
theorem B4253897 : Blo 1680040 4253897 := bstep (se 2 (by rfl) ⟨1595211, by rfl⟩ : syracuseStep 4253897 = 3190423) B3190423
theorem B1681671 : Blo 1680040 1681671 := bstep (se 1 (by rfl) ⟨1261253, by rfl⟩ : syracuseStep 1681671 = 2522507) B2522507
theorem B1681679 : Blo 1680040 1681679 := bstep (se 1 (by rfl) ⟨1261259, by rfl⟩ : syracuseStep 1681679 = 2522519) B2522519
theorem B5114141 : Blo 1680040 5114141 := bstep (se 3 (by rfl) ⟨958901, by rfl⟩ : syracuseStep 5114141 = 1917803) B1917803
theorem B2836795 : Blo 1680040 2836795 := bstep (se 1 (by rfl) ⟨2127596, by rfl⟩ : syracuseStep 2836795 = 4255193) B4255193
theorem B1681723 : Blo 1680040 1681723 := bstep (se 1 (by rfl) ⟨1261292, by rfl⟩ : syracuseStep 1681723 = 2522585) B2522585
theorem B5179735 : Blo 1680040 5179735 := bstep (se 1 (by rfl) ⟨3884801, by rfl⟩ : syracuseStep 5179735 = 7769603) B7769603
theorem B34490717 : Blo 1680040 34490717 := bstep (se 3 (by rfl) ⟨6467009, by rfl⟩ : syracuseStep 34490717 = 12934019) B12934019
theorem B1681799 : Blo 1680040 1681799 := bstep (se 1 (by rfl) ⟨1261349, by rfl⟩ : syracuseStep 1681799 = 2522699) B2522699
theorem B1681807 : Blo 1680040 1681807 := bstep (se 1 (by rfl) ⟨1261355, by rfl⟩ : syracuseStep 1681807 = 2522711) B2522711
theorem B1681851 : Blo 1680040 1681851 := bstep (se 1 (by rfl) ⟨1261388, by rfl⟩ : syracuseStep 1681851 = 2522777) B2522777
theorem B2836937 : Blo 1680040 2836937 := bstep (se 2 (by rfl) ⟨1063851, by rfl⟩ : syracuseStep 2836937 = 2127703) B2127703
theorem B8505809 : Blo 1680040 8505809 := bstep (se 2 (by rfl) ⟨3189678, by rfl⟩ : syracuseStep 8505809 = 6379357) B6379357
theorem B11659729 : Blo 1680040 11659729 := bstep (se 2 (by rfl) ⟨4372398, by rfl⟩ : syracuseStep 11659729 = 8744797) B8744797
theorem B1681927 : Blo 1680040 1681927 := bstep (se 1 (by rfl) ⟨1261445, by rfl⟩ : syracuseStep 1681927 = 2522891) B2522891
theorem B1681935 : Blo 1680040 1681935 := bstep (se 1 (by rfl) ⟨1261451, by rfl⟩ : syracuseStep 1681935 = 2522903) B2522903
theorem B8514071 : Blo 1680040 8514071 := bstep (se 1 (by rfl) ⟨6385553, by rfl⟩ : syracuseStep 8514071 = 12771107) B12771107
theorem B6056477 : Blo 1680040 6056477 := bstep (se 3 (by rfl) ⟨1135589, by rfl⟩ : syracuseStep 6056477 = 2271179) B2271179
theorem B4254241 : Blo 1680040 4254241 := bstep (se 2 (by rfl) ⟨1595340, by rfl⟩ : syracuseStep 4254241 = 3190681) B3190681
theorem B1681979 : Blo 1680040 1681979 := bstep (se 1 (by rfl) ⟨1261484, by rfl⟩ : syracuseStep 1681979 = 2522969) B2522969
theorem B7178813 : Blo 1680040 7178813 := bstep (se 3 (by rfl) ⟨1346027, by rfl⟩ : syracuseStep 7178813 = 2692055) B2692055
theorem B2394697 : Blo 1680040 2394697 := bstep (se 2 (by rfl) ⟨898011, by rfl⟩ : syracuseStep 2394697 = 1796023) B1796023
theorem B5671511 : Blo 1680040 5671511 := bstep (se 1 (by rfl) ⟨4253633, by rfl⟩ : syracuseStep 5671511 = 8507267) B8507267
theorem B39906053 : Blo 1680040 39906053 := bstep (se 4 (by rfl) ⟨3741192, by rfl⟩ : syracuseStep 39906053 = 7482385) B7482385
theorem B28724057 : Blo 1680040 28724057 := bstep (se 2 (by rfl) ⟨10771521, by rfl⟩ : syracuseStep 28724057 = 21543043) B21543043
theorem B4787059 : Blo 1680040 4787059 := bstep (se 1 (by rfl) ⟨3590294, by rfl⟩ : syracuseStep 4787059 = 7180589) B7180589
theorem B3591047 : Blo 1680040 3591047 := bstep (se 1 (by rfl) ⟨2693285, by rfl⟩ : syracuseStep 3591047 = 5386571) B5386571
theorem B7670663 : Blo 1680040 7670663 := bstep (se 1 (by rfl) ⟨5752997, by rfl⟩ : syracuseStep 7670663 = 11505995) B11505995
theorem B3640249 : Blo 1680040 3640249 := bstep (se 2 (by rfl) ⟨1365093, by rfl⟩ : syracuseStep 3640249 = 2730187) B2730187
theorem B3189793 : Blo 1680040 3189793 := bstep (se 2 (by rfl) ⟨1196172, by rfl⟩ : syracuseStep 3189793 = 2392345) B2392345
theorem B10767421 : Blo 1680040 10767421 := bstep (se 3 (by rfl) ⟨2018891, by rfl⟩ : syracuseStep 10767421 = 4037783) B4037783
theorem B5671997 : Blo 1680040 5671997 := bstep (se 3 (by rfl) ⟨1063499, by rfl⟩ : syracuseStep 5671997 = 2126999) B2126999
theorem B4254839 : Blo 1680040 4254839 := bstep (se 1 (by rfl) ⟨3191129, by rfl⟩ : syracuseStep 4254839 = 6382259) B6382259
theorem B2837639 : Blo 1680040 2837639 := bstep (se 1 (by rfl) ⟨2128229, by rfl⟩ : syracuseStep 2837639 = 4256459) B4256459
theorem B14552237 : Blo 1680040 14552237 := bstep (se 3 (by rfl) ⟨2728544, by rfl⟩ : syracuseStep 14552237 = 5457089) B5457089
theorem B81808699 : Blo 1680040 81808699 := bstep (se 1 (by rfl) ⟨61356524, by rfl⟩ : syracuseStep 81808699 = 122713049) B122713049
theorem B3780215 : Blo 1680040 3780215 := bstep (se 1 (by rfl) ⟨2835161, by rfl⟩ : syracuseStep 3780215 = 5670323) B5670323
theorem B2838287 : Blo 1680040 2838287 := bstep (se 1 (by rfl) ⟨2128715, by rfl⟩ : syracuseStep 2838287 = 4257431) B4257431
theorem B3780395 : Blo 1680040 3780395 := bstep (se 1 (by rfl) ⟨2835296, by rfl⟩ : syracuseStep 3780395 = 5670593) B5670593
theorem B13635377 : Blo 1680040 13635377 := bstep (se 2 (by rfl) ⟨5113266, by rfl⟩ : syracuseStep 13635377 = 10226533) B10226533
theorem B7671611 : Blo 1680040 7671611 := bstep (se 1 (by rfl) ⟨5753708, by rfl⟩ : syracuseStep 7671611 = 11507417) B11507417
theorem B9572363 : Blo 1680040 9572363 := bstep (se 1 (by rfl) ⟨7179272, by rfl⟩ : syracuseStep 9572363 = 14358545) B14358545
theorem B6385675 : Blo 1680040 6385675 := bstep (se 1 (by rfl) ⟨4789256, by rfl⟩ : syracuseStep 6385675 = 9578513) B9578513
theorem B5386301 : Blo 1680040 5386301 := bstep (se 3 (by rfl) ⟨1009931, by rfl⟩ : syracuseStep 5386301 = 2019863) B2019863
theorem B4493431 : Blo 1680040 4493431 := bstep (se 1 (by rfl) ⟨3370073, by rfl⟩ : syracuseStep 4493431 = 6740147) B6740147
theorem B3780755 : Blo 1680040 3780755 := bstep (se 1 (by rfl) ⟨2835566, by rfl⟩ : syracuseStep 3780755 = 5671133) B5671133
theorem B12939437 : Blo 1680040 12939437 := bstep (se 3 (by rfl) ⟨2426144, by rfl⟩ : syracuseStep 12939437 = 4852289) B4852289
theorem B3780809 : Blo 1680040 3780809 := bstep (se 2 (by rfl) ⟨1417803, by rfl⟩ : syracuseStep 3780809 = 2835607) B2835607
theorem B3190985 : Blo 1680040 3190985 := bstep (se 2 (by rfl) ⟨1196619, by rfl⟩ : syracuseStep 3190985 = 2393239) B2393239
theorem B2691343 : Blo 1680040 2691343 := bstep (se 1 (by rfl) ⟨2018507, by rfl⟩ : syracuseStep 2691343 = 4037015) B4037015
theorem B6385979 : Blo 1680040 6385979 := bstep (se 1 (by rfl) ⟨4789484, by rfl⟩ : syracuseStep 6385979 = 9578969) B9578969
theorem B8073607 : Blo 1680040 8073607 := bstep (se 1 (by rfl) ⟨6055205, by rfl⟩ : syracuseStep 8073607 = 12110411) B12110411
theorem B4256135 : Blo 1680040 4256135 := bstep (se 1 (by rfl) ⟨3192101, by rfl⟩ : syracuseStep 4256135 = 6384203) B6384203
theorem B12759443 : Blo 1680040 12759443 := bstep (se 1 (by rfl) ⟨9569582, by rfl⟩ : syracuseStep 12759443 = 19139165) B19139165
theorem B8622521 : Blo 1680040 8622521 := bstep (se 2 (by rfl) ⟨3233445, by rfl⟩ : syracuseStep 8622521 = 6466891) B6466891
theorem B5673401 : Blo 1680040 5673401 := bstep (se 2 (by rfl) ⟨2127525, by rfl⟩ : syracuseStep 5673401 = 4255051) B4255051
theorem B4256185 : Blo 1680040 4256185 := bstep (se 2 (by rfl) ⟨1596069, by rfl⟩ : syracuseStep 4256185 = 3192139) B3192139
theorem B4788665 : Blo 1680040 4788665 := bstep (se 2 (by rfl) ⟨1795749, by rfl⟩ : syracuseStep 4788665 = 3591499) B3591499
theorem B8507915 : Blo 1680040 8507915 := bstep (se 1 (by rfl) ⟨6380936, by rfl⟩ : syracuseStep 8507915 = 12761873) B12761873
theorem B7180811 : Blo 1680040 7180811 := bstep (se 1 (by rfl) ⟨5385608, by rfl⟩ : syracuseStep 7180811 = 10771217) B10771217
theorem B2126351 : Blo 1680040 2126351 := bstep (se 1 (by rfl) ⟨1594763, by rfl⟩ : syracuseStep 2126351 = 3189527) B3189527
theorem B8508077 : Blo 1680040 8508077 := bstep (se 3 (by rfl) ⟨1595264, by rfl⟩ : syracuseStep 8508077 = 3190529) B3190529
theorem B4789007 : Blo 1680040 4789007 := bstep (se 1 (by rfl) ⟨3591755, by rfl⟩ : syracuseStep 4789007 = 7183511) B7183511
theorem B6386465 : Blo 1680040 6386465 := bstep (se 2 (by rfl) ⟨2394924, by rfl⟩ : syracuseStep 6386465 = 4789849) B4789849
theorem B4854589 : Blo 1680040 4854589 := bstep (se 3 (by rfl) ⟨910235, by rfl⟩ : syracuseStep 4854589 = 1820471) B1820471
theorem B10769267 : Blo 1680040 10769267 := bstep (se 1 (by rfl) ⟨8076950, by rfl⟩ : syracuseStep 10769267 = 16153901) B16153901
theorem B3781511 : Blo 1680040 3781511 := bstep (se 1 (by rfl) ⟨2836133, by rfl⟩ : syracuseStep 3781511 = 5672267) B5672267
theorem B3191699 : Blo 1680040 3191699 := bstep (se 1 (by rfl) ⟨2393774, by rfl⟩ : syracuseStep 3191699 = 4787549) B4787549
theorem B3191737 : Blo 1680040 3191737 := bstep (se 2 (by rfl) ⟨1196901, by rfl⟩ : syracuseStep 3191737 = 2393803) B2393803
theorem B2520071 : Blo 1680040 2520071 := bstep (se 1 (by rfl) ⟨1890053, by rfl⟩ : syracuseStep 2520071 = 3780107) B3780107
theorem B5673995 : Blo 1680040 5673995 := bstep (se 1 (by rfl) ⟨4255496, by rfl⟩ : syracuseStep 5673995 = 8510993) B8510993
theorem B4256783 : Blo 1680040 4256783 := bstep (se 1 (by rfl) ⟨3192587, by rfl⟩ : syracuseStep 4256783 = 6385175) B6385175
theorem B2520107 : Blo 1680040 2520107 := bstep (se 1 (by rfl) ⟨1890080, by rfl⟩ : syracuseStep 2520107 = 3780161) B3780161
theorem B3781691 : Blo 1680040 3781691 := bstep (se 1 (by rfl) ⟨2836268, by rfl⟩ : syracuseStep 3781691 = 5672537) B5672537
theorem B2520137 : Blo 1680040 2520137 := bstep (se 2 (by rfl) ⟨945051, by rfl⟩ : syracuseStep 2520137 = 1890103) B1890103
theorem B5674103 : Blo 1680040 5674103 := bstep (se 1 (by rfl) ⟨4255577, by rfl⟩ : syracuseStep 5674103 = 8511155) B8511155
theorem B3781817 : Blo 1680040 3781817 := bstep (se 2 (by rfl) ⟨1418181, by rfl⟩ : syracuseStep 3781817 = 2836363) B2836363
theorem B2520251 : Blo 1680040 2520251 := bstep (se 1 (by rfl) ⟨1890188, by rfl⟩ : syracuseStep 2520251 = 3780377) B3780377
theorem B2520311 : Blo 1680040 2520311 := bstep (se 1 (by rfl) ⟨1890233, by rfl⟩ : syracuseStep 2520311 = 3780467) B3780467
theorem B2520335 : Blo 1680040 2520335 := bstep (se 1 (by rfl) ⟨1890251, by rfl⟩ : syracuseStep 2520335 = 3780503) B3780503
theorem B2520377 : Blo 1680040 2520377 := bstep (se 2 (by rfl) ⟨945141, by rfl⟩ : syracuseStep 2520377 = 1890283) B1890283
theorem B2520455 : Blo 1680040 2520455 := bstep (se 1 (by rfl) ⟨1890341, by rfl⟩ : syracuseStep 2520455 = 3780683) B3780683
theorem B7665043 : Blo 1680040 7665043 := bstep (se 1 (by rfl) ⟨5748782, by rfl⟩ : syracuseStep 7665043 = 11497565) B11497565
theorem B2520491 : Blo 1680040 2520491 := bstep (se 1 (by rfl) ⟨1890368, by rfl⟩ : syracuseStep 2520491 = 3780737) B3780737
theorem B2520521 : Blo 1680040 2520521 := bstep (se 2 (by rfl) ⟨945195, by rfl⟩ : syracuseStep 2520521 = 1890391) B1890391
theorem B18413021 : Blo 1680040 18413021 := bstep (se 3 (by rfl) ⟨3452441, by rfl⟩ : syracuseStep 18413021 = 6904883) B6904883
theorem B3782159 : Blo 1680040 3782159 := bstep (se 1 (by rfl) ⟨2836619, by rfl⟩ : syracuseStep 3782159 = 5673239) B5673239
theorem B3782177 : Blo 1680040 3782177 := bstep (se 2 (by rfl) ⟨1418316, by rfl⟩ : syracuseStep 3782177 = 2836633) B2836633
theorem B4789793 : Blo 1680040 4789793 := bstep (se 2 (by rfl) ⟨1796172, by rfl⟩ : syracuseStep 4789793 = 3592345) B3592345
theorem B2520635 : Blo 1680040 2520635 := bstep (se 1 (by rfl) ⟨1890476, by rfl⟩ : syracuseStep 2520635 = 3780953) B3780953
theorem B2520695 : Blo 1680040 2520695 := bstep (se 1 (by rfl) ⟨1890521, by rfl⟩ : syracuseStep 2520695 = 3781043) B3781043
theorem B2520719 : Blo 1680040 2520719 := bstep (se 1 (by rfl) ⟨1890539, by rfl⟩ : syracuseStep 2520719 = 3781079) B3781079
theorem B2520761 : Blo 1680040 2520761 := bstep (se 2 (by rfl) ⟨945285, by rfl⟩ : syracuseStep 2520761 = 1890571) B1890571
theorem B5674697 : Blo 1680040 5674697 := bstep (se 2 (by rfl) ⟨2128011, by rfl⟩ : syracuseStep 5674697 = 4256023) B4256023
theorem B4257481 : Blo 1680040 4257481 := bstep (se 2 (by rfl) ⟨1596555, by rfl⟩ : syracuseStep 4257481 = 3193111) B3193111
theorem B40875749 : Blo 1680040 40875749 := bstep (se 4 (by rfl) ⟨3832101, by rfl⟩ : syracuseStep 40875749 = 7664203) B7664203
theorem B2520839 : Blo 1680040 2520839 := bstep (se 1 (by rfl) ⟨1890629, by rfl⟩ : syracuseStep 2520839 = 3781259) B3781259
theorem B10770191 : Blo 1680040 10770191 := bstep (se 1 (by rfl) ⟨8077643, by rfl⟩ : syracuseStep 10770191 = 16155287) B16155287
theorem B17258255 : Blo 1680040 17258255 := bstep (se 1 (by rfl) ⟨12943691, by rfl⟩ : syracuseStep 17258255 = 25887383) B25887383
theorem B2520875 : Blo 1680040 2520875 := bstep (se 1 (by rfl) ⟨1890656, by rfl⟩ : syracuseStep 2520875 = 3781313) B3781313
theorem B2520905 : Blo 1680040 2520905 := bstep (se 2 (by rfl) ⟨945339, by rfl⟩ : syracuseStep 2520905 = 1890679) B1890679
theorem B4257623 : Blo 1680040 4257623 := bstep (se 1 (by rfl) ⟨3193217, by rfl⟩ : syracuseStep 4257623 = 6386435) B6386435
theorem B3782519 : Blo 1680040 3782519 := bstep (se 1 (by rfl) ⟨2836889, by rfl⟩ : syracuseStep 3782519 = 5673779) B5673779
theorem B18175907 : Blo 1680040 18175907 := bstep (se 1 (by rfl) ⟨13631930, by rfl⟩ : syracuseStep 18175907 = 27263861) B27263861
theorem B2521019 : Blo 1680040 2521019 := bstep (se 1 (by rfl) ⟨1890764, by rfl⟩ : syracuseStep 2521019 = 3781529) B3781529
theorem B2521079 : Blo 1680040 2521079 := bstep (se 1 (by rfl) ⟨1890809, by rfl⟩ : syracuseStep 2521079 = 3781619) B3781619
theorem B1890319 : Blo 1680040 1890319 := bstep (se 1 (by rfl) ⟨1417739, by rfl⟩ : syracuseStep 1890319 = 2835479) B2835479
theorem B2521103 : Blo 1680040 2521103 := bstep (se 1 (by rfl) ⟨1890827, by rfl⟩ : syracuseStep 2521103 = 3781655) B3781655
theorem B28710935 : Blo 1680040 28710935 := bstep (se 1 (by rfl) ⟨21533201, by rfl⟩ : syracuseStep 28710935 = 43066403) B43066403
theorem B3782699 : Blo 1680040 3782699 := bstep (se 1 (by rfl) ⟨2837024, by rfl⟩ : syracuseStep 3782699 = 5674049) B5674049
theorem B9091115 : Blo 1680040 9091115 := bstep (se 1 (by rfl) ⟨6818336, by rfl⟩ : syracuseStep 9091115 = 13636673) B13636673
theorem B27277357 : Blo 1680040 27277357 := bstep (se 3 (by rfl) ⟨5114504, by rfl⟩ : syracuseStep 27277357 = 10229009) B10229009
theorem B2521145 : Blo 1680040 2521145 := bstep (se 2 (by rfl) ⟨945429, by rfl⟩ : syracuseStep 2521145 = 1890859) B1890859
theorem B2521223 : Blo 1680040 2521223 := bstep (se 1 (by rfl) ⟨1890917, by rfl⟩ : syracuseStep 2521223 = 3781835) B3781835
theorem B2521259 : Blo 1680040 2521259 := bstep (se 1 (by rfl) ⟨1890944, by rfl⟩ : syracuseStep 2521259 = 3781889) B3781889
theorem B2521289 : Blo 1680040 2521289 := bstep (se 2 (by rfl) ⟨945483, by rfl⟩ : syracuseStep 2521289 = 1890967) B1890967
theorem B8509697 : Blo 1680040 8509697 := bstep (se 2 (by rfl) ⟨3191136, by rfl⟩ : syracuseStep 8509697 = 6382273) B6382273
theorem B2521403 : Blo 1680040 2521403 := bstep (se 1 (by rfl) ⟨1891052, by rfl⟩ : syracuseStep 2521403 = 3782105) B3782105
theorem B2521463 : Blo 1680040 2521463 := bstep (se 1 (by rfl) ⟨1891097, by rfl⟩ : syracuseStep 2521463 = 3782195) B3782195
theorem B5675399 : Blo 1680040 5675399 := bstep (se 1 (by rfl) ⟨4256549, by rfl⟩ : syracuseStep 5675399 = 8513099) B8513099
theorem B2521487 : Blo 1680040 2521487 := bstep (se 1 (by rfl) ⟨1891115, by rfl⟩ : syracuseStep 2521487 = 3782231) B3782231
theorem B3783059 : Blo 1680040 3783059 := bstep (se 1 (by rfl) ⟨2837294, by rfl⟩ : syracuseStep 3783059 = 5674589) B5674589
theorem B2521529 : Blo 1680040 2521529 := bstep (se 2 (by rfl) ⟨945573, by rfl⟩ : syracuseStep 2521529 = 1891147) B1891147
theorem B3783113 : Blo 1680040 3783113 := bstep (se 2 (by rfl) ⟨1418667, by rfl⟩ : syracuseStep 3783113 = 2837335) B2837335
theorem B1890823 : Blo 1680040 1890823 := bstep (se 1 (by rfl) ⟨1418117, by rfl⟩ : syracuseStep 1890823 = 2836235) B2836235
theorem B2521607 : Blo 1680040 2521607 := bstep (se 1 (by rfl) ⟨1891205, by rfl⟩ : syracuseStep 2521607 = 3782411) B3782411
theorem B2521643 : Blo 1680040 2521643 := bstep (se 1 (by rfl) ⟨1891232, by rfl⟩ : syracuseStep 2521643 = 3782465) B3782465
theorem B28719683 : Blo 1680040 28719683 := bstep (se 1 (by rfl) ⟨21539762, by rfl⟩ : syracuseStep 28719683 = 43079525) B43079525
theorem B2521673 : Blo 1680040 2521673 := bstep (se 2 (by rfl) ⟨945627, by rfl⟩ : syracuseStep 2521673 = 1891255) B1891255
theorem B10222199 : Blo 1680040 10222199 := bstep (se 1 (by rfl) ⟨7666649, by rfl⟩ : syracuseStep 10222199 = 15333299) B15333299
theorem B2767495 : Blo 1680040 2767495 := bstep (se 1 (by rfl) ⟨2075621, by rfl⟩ : syracuseStep 2767495 = 4151243) B4151243
theorem B1891003 : Blo 1680040 1891003 := bstep (se 1 (by rfl) ⟨1418252, by rfl⟩ : syracuseStep 1891003 = 2836505) B2836505
theorem B2521787 : Blo 1680040 2521787 := bstep (se 1 (by rfl) ⟨1891340, by rfl⟩ : syracuseStep 2521787 = 3782681) B3782681
theorem B2521847 : Blo 1680040 2521847 := bstep (se 1 (by rfl) ⟨1891385, by rfl⟩ : syracuseStep 2521847 = 3782771) B3782771
theorem B5675777 : Blo 1680040 5675777 := bstep (se 2 (by rfl) ⟨2128416, by rfl⟩ : syracuseStep 5675777 = 4256833) B4256833
theorem B2521871 : Blo 1680040 2521871 := bstep (se 1 (by rfl) ⟨1891403, by rfl⟩ : syracuseStep 2521871 = 3782807) B3782807
theorem B6060815 : Blo 1680040 6060815 := bstep (se 1 (by rfl) ⟨4545611, by rfl⟩ : syracuseStep 6060815 = 9091223) B9091223
theorem B2521913 : Blo 1680040 2521913 := bstep (se 2 (by rfl) ⟨945717, by rfl⟩ : syracuseStep 2521913 = 1891435) B1891435
theorem B19143539 : Blo 1680040 19143539 := bstep (se 1 (by rfl) ⟨14357654, by rfl⟩ : syracuseStep 19143539 = 28715309) B28715309
theorem B17726323 : Blo 1680040 17726323 := bstep (se 1 (by rfl) ⟨13294742, by rfl⟩ : syracuseStep 17726323 = 26589485) B26589485
theorem B2521991 : Blo 1680040 2521991 := bstep (se 1 (by rfl) ⟨1891493, by rfl⟩ : syracuseStep 2521991 = 3782987) B3782987
theorem B2522027 : Blo 1680040 2522027 := bstep (se 1 (by rfl) ⟨1891520, by rfl⟩ : syracuseStep 2522027 = 3783041) B3783041
theorem B2694073 : Blo 1680040 2694073 := bstep (se 2 (by rfl) ⟨1010277, by rfl⟩ : syracuseStep 2694073 = 2020555) B2020555
theorem B2522057 : Blo 1680040 2522057 := bstep (se 2 (by rfl) ⟨945771, by rfl⟩ : syracuseStep 2522057 = 1891543) B1891543
theorem B5110795 : Blo 1680040 5110795 := bstep (se 1 (by rfl) ⟨3833096, by rfl⟩ : syracuseStep 5110795 = 7666193) B7666193
theorem B8510507 : Blo 1680040 8510507 := bstep (se 1 (by rfl) ⟨6382880, by rfl⟩ : syracuseStep 8510507 = 12765761) B12765761
theorem B2522171 : Blo 1680040 2522171 := bstep (se 1 (by rfl) ⟨1891628, by rfl⟩ : syracuseStep 2522171 = 3783257) B3783257
theorem B2522231 : Blo 1680040 2522231 := bstep (se 1 (by rfl) ⟨1891673, by rfl⟩ : syracuseStep 2522231 = 3783347) B3783347
theorem B3783815 : Blo 1680040 3783815 := bstep (se 1 (by rfl) ⟨2837861, by rfl⟩ : syracuseStep 3783815 = 5675723) B5675723
theorem B1891471 : Blo 1680040 1891471 := bstep (se 1 (by rfl) ⟨1418603, by rfl⟩ : syracuseStep 1891471 = 2837207) B2837207
theorem B2522255 : Blo 1680040 2522255 := bstep (se 1 (by rfl) ⟨1891691, by rfl⟩ : syracuseStep 2522255 = 3783383) B3783383
theorem B5110931 : Blo 1680040 5110931 := bstep (se 1 (by rfl) ⟨3833198, by rfl⟩ : syracuseStep 5110931 = 7666397) B7666397
theorem B9575597 : Blo 1680040 9575597 := bstep (se 3 (by rfl) ⟨1795424, by rfl⟩ : syracuseStep 9575597 = 3590849) B3590849
theorem B2522297 : Blo 1680040 2522297 := bstep (se 2 (by rfl) ⟨945861, by rfl⟩ : syracuseStep 2522297 = 1891723) B1891723
theorem B6380801 : Blo 1680040 6380801 := bstep (se 2 (by rfl) ⟨2392800, by rfl⟩ : syracuseStep 6380801 = 4785601) B4785601
theorem B2522375 : Blo 1680040 2522375 := bstep (se 1 (by rfl) ⟨1891781, by rfl⟩ : syracuseStep 2522375 = 3783563) B3783563
theorem B6380815 : Blo 1680040 6380815 := bstep (se 1 (by rfl) ⟨4785611, by rfl⟩ : syracuseStep 6380815 = 9571223) B9571223
theorem B2522411 : Blo 1680040 2522411 := bstep (se 1 (by rfl) ⟨1891808, by rfl⟩ : syracuseStep 2522411 = 3783617) B3783617
theorem B151420205 : Blo 1680040 151420205 := bstep (se 3 (by rfl) ⟨28391288, by rfl⟩ : syracuseStep 151420205 = 56782577) B56782577
theorem B3783995 : Blo 1680040 3783995 := bstep (se 1 (by rfl) ⟨2837996, by rfl⟩ : syracuseStep 3783995 = 5675993) B5675993
theorem B2522441 : Blo 1680040 2522441 := bstep (se 2 (by rfl) ⟨945915, by rfl⟩ : syracuseStep 2522441 = 1891831) B1891831
theorem B3784121 : Blo 1680040 3784121 := bstep (se 2 (by rfl) ⟨1419045, by rfl⟩ : syracuseStep 3784121 = 2838091) B2838091
theorem B2522555 : Blo 1680040 2522555 := bstep (se 1 (by rfl) ⟨1891916, by rfl⟩ : syracuseStep 2522555 = 3783833) B3783833
theorem B2522615 : Blo 1680040 2522615 := bstep (se 1 (by rfl) ⟨1891961, by rfl⟩ : syracuseStep 2522615 = 3783923) B3783923
theorem B2522639 : Blo 1680040 2522639 := bstep (se 1 (by rfl) ⟨1891979, by rfl⟩ : syracuseStep 2522639 = 3783959) B3783959
theorem B5676587 : Blo 1680040 5676587 := bstep (se 1 (by rfl) ⟨4257440, by rfl⟩ : syracuseStep 5676587 = 8514881) B8514881
theorem B2522681 : Blo 1680040 2522681 := bstep (se 2 (by rfl) ⟨946005, by rfl⟩ : syracuseStep 2522681 = 1892011) B1892011
theorem B1891975 : Blo 1680040 1891975 := bstep (se 1 (by rfl) ⟨1418981, by rfl⟩ : syracuseStep 1891975 = 2837963) B2837963
theorem B2522759 : Blo 1680040 2522759 := bstep (se 1 (by rfl) ⟨1892069, by rfl⟩ : syracuseStep 2522759 = 3784139) B3784139
theorem B2522795 : Blo 1680040 2522795 := bstep (se 1 (by rfl) ⟨1892096, by rfl⟩ : syracuseStep 2522795 = 3784193) B3784193
theorem B2522825 : Blo 1680040 2522825 := bstep (se 2 (by rfl) ⟨946059, by rfl⟩ : syracuseStep 2522825 = 1892119) B1892119
theorem B3071759 : Blo 1680040 3071759 := bstep (se 1 (by rfl) ⟨2303819, by rfl⟩ : syracuseStep 3071759 = 4607639) B4607639
theorem B3784463 : Blo 1680040 3784463 := bstep (se 1 (by rfl) ⟨2838347, by rfl⟩ : syracuseStep 3784463 = 5676695) B5676695
theorem B3784481 : Blo 1680040 3784481 := bstep (se 2 (by rfl) ⟨1419180, by rfl⟩ : syracuseStep 3784481 = 2838361) B2838361
theorem B2301755 : Blo 1680040 2301755 := bstep (se 1 (by rfl) ⟨1726316, by rfl⟩ : syracuseStep 2301755 = 3452633) B3452633
theorem B1892155 : Blo 1680040 1892155 := bstep (se 1 (by rfl) ⟨1419116, by rfl⟩ : syracuseStep 1892155 = 2838233) B2838233
theorem B2522939 : Blo 1680040 2522939 := bstep (se 1 (by rfl) ⟨1892204, by rfl⟩ : syracuseStep 2522939 = 3784409) B3784409
theorem B2522999 : Blo 1680040 2522999 := bstep (se 1 (by rfl) ⟨1892249, by rfl⟩ : syracuseStep 2522999 = 3784499) B3784499
theorem B2523023 : Blo 1680040 2523023 := bstep (se 1 (by rfl) ⟨1892267, by rfl⟩ : syracuseStep 2523023 = 3784535) B3784535
theorem B8077259 : Blo 1680040 8077259 := bstep (se 1 (by rfl) ⟨6057944, by rfl⟩ : syracuseStep 8077259 = 12115889) B12115889
theorem B6381575 : Blo 1680040 6381575 := bstep (se 1 (by rfl) ⟨4786181, by rfl⟩ : syracuseStep 6381575 = 9572363) B9572363
theorem B3588457 : Blo 1680040 3588457 := bstep (se 2 (by rfl) ⟨1345671, by rfl⟩ : syracuseStep 3588457 = 2691343) B2691343
theorem B6906313 : Blo 1680040 6906313 := bstep (se 2 (by rfl) ⟨2589867, by rfl⟩ : syracuseStep 6906313 = 5179735) B5179735
theorem B34505165 : Blo 1680040 34505165 := bstep (se 3 (by rfl) ⟨6469718, by rfl⟩ : syracuseStep 34505165 = 12939437) B12939437
theorem B6382061 : Blo 1680040 6382061 := bstep (se 3 (by rfl) ⟨1196636, by rfl⟩ : syracuseStep 6382061 = 2393273) B2393273
theorem B10764809 : Blo 1680040 10764809 := bstep (se 2 (by rfl) ⟨4036803, by rfl⟩ : syracuseStep 10764809 = 8073607) B8073607
theorem B10764859 : Blo 1680040 10764859 := bstep (se 1 (by rfl) ⟨8073644, by rfl⟩ : syracuseStep 10764859 = 16147289) B16147289
theorem B1680047 : Blo 1680040 1680047 := bstep (se 1 (by rfl) ⟨1260035, by rfl⟩ : syracuseStep 1680047 = 2520071) B2520071
theorem B1680071 : Blo 1680040 1680071 := bstep (se 1 (by rfl) ⟨1260053, by rfl⟩ : syracuseStep 1680071 = 2520107) B2520107
theorem B1680091 : Blo 1680040 1680091 := bstep (se 1 (by rfl) ⟨1260068, by rfl⟩ : syracuseStep 1680091 = 2520137) B2520137
theorem B1680167 : Blo 1680040 1680167 := bstep (se 1 (by rfl) ⟨1260125, by rfl⟩ : syracuseStep 1680167 = 2520251) B2520251
theorem B1680207 : Blo 1680040 1680207 := bstep (se 1 (by rfl) ⟨1260155, by rfl⟩ : syracuseStep 1680207 = 2520311) B2520311
theorem B1680223 : Blo 1680040 1680223 := bstep (se 1 (by rfl) ⟨1260167, by rfl⟩ : syracuseStep 1680223 = 2520335) B2520335
theorem B1680251 : Blo 1680040 1680251 := bstep (se 1 (by rfl) ⟨1260188, by rfl⟩ : syracuseStep 1680251 = 2520377) B2520377
theorem B1680303 : Blo 1680040 1680303 := bstep (se 1 (by rfl) ⟨1260227, by rfl⟩ : syracuseStep 1680303 = 2520455) B2520455
theorem B1680327 : Blo 1680040 1680327 := bstep (se 1 (by rfl) ⟨1260245, by rfl⟩ : syracuseStep 1680327 = 2520491) B2520491
theorem B1680347 : Blo 1680040 1680347 := bstep (se 1 (by rfl) ⟨1260260, by rfl⟩ : syracuseStep 1680347 = 2520521) B2520521
theorem B1680423 : Blo 1680040 1680423 := bstep (se 1 (by rfl) ⟨1260317, by rfl⟩ : syracuseStep 1680423 = 2520635) B2520635
theorem B2589775 : Blo 1680040 2589775 := bstep (se 1 (by rfl) ⟨1942331, by rfl⟩ : syracuseStep 2589775 = 3884663) B3884663
theorem B7275599 : Blo 1680040 7275599 := bstep (se 1 (by rfl) ⟨5456699, by rfl⟩ : syracuseStep 7275599 = 10913399) B10913399
theorem B1680463 : Blo 1680040 1680463 := bstep (se 1 (by rfl) ⟨1260347, by rfl⟩ : syracuseStep 1680463 = 2520695) B2520695
theorem B1680479 : Blo 1680040 1680479 := bstep (se 1 (by rfl) ⟨1260359, by rfl⟩ : syracuseStep 1680479 = 2520719) B2520719
theorem B1680507 : Blo 1680040 1680507 := bstep (se 1 (by rfl) ⟨1260380, by rfl⟩ : syracuseStep 1680507 = 2520761) B2520761
theorem B23635097 : Blo 1680040 23635097 := bstep (se 2 (by rfl) ⟨8863161, by rfl⟩ : syracuseStep 23635097 = 17726323) B17726323
theorem B6382745 : Blo 1680040 6382745 := bstep (se 2 (by rfl) ⟨2393529, by rfl⟩ : syracuseStep 6382745 = 4787059) B4787059
theorem B19137707 : Blo 1680040 19137707 := bstep (se 1 (by rfl) ⟨14353280, by rfl⟩ : syracuseStep 19137707 = 28706561) B28706561
theorem B1680559 : Blo 1680040 1680559 := bstep (se 1 (by rfl) ⟨1260419, by rfl⟩ : syracuseStep 1680559 = 2520839) B2520839
theorem B1680583 : Blo 1680040 1680583 := bstep (se 1 (by rfl) ⟨1260437, by rfl⟩ : syracuseStep 1680583 = 2520875) B2520875
theorem B1680603 : Blo 1680040 1680603 := bstep (se 1 (by rfl) ⟨1260452, by rfl⟩ : syracuseStep 1680603 = 2520905) B2520905
theorem B103564565 : Blo 1680040 103564565 := bstep (se 6 (by rfl) ⟨2427294, by rfl⟩ : syracuseStep 103564565 = 4854589) B4854589
theorem B12117271 : Blo 1680040 12117271 := bstep (se 1 (by rfl) ⟨9087953, by rfl⟩ : syracuseStep 12117271 = 18175907) B18175907
theorem B1680679 : Blo 1680040 1680679 := bstep (se 1 (by rfl) ⟨1260509, by rfl⟩ : syracuseStep 1680679 = 2521019) B2521019
theorem B1680719 : Blo 1680040 1680719 := bstep (se 1 (by rfl) ⟨1260539, by rfl⟩ : syracuseStep 1680719 = 2521079) B2521079
theorem B1680735 : Blo 1680040 1680735 := bstep (se 1 (by rfl) ⟨1260551, by rfl⟩ : syracuseStep 1680735 = 2521103) B2521103
theorem B1680763 : Blo 1680040 1680763 := bstep (se 1 (by rfl) ⟨1260572, by rfl⟩ : syracuseStep 1680763 = 2521145) B2521145
theorem B5670269 : Blo 1680040 5670269 := bstep (se 3 (by rfl) ⟨1063175, by rfl⟩ : syracuseStep 5670269 = 2126351) B2126351
theorem B4253057 : Blo 1680040 4253057 := bstep (se 2 (by rfl) ⟨1594896, by rfl⟩ : syracuseStep 4253057 = 3189793) B3189793
theorem B1680815 : Blo 1680040 1680815 := bstep (se 1 (by rfl) ⟨1260611, by rfl⟩ : syracuseStep 1680815 = 2521223) B2521223
theorem B1680839 : Blo 1680040 1680839 := bstep (se 1 (by rfl) ⟨1260629, by rfl⟩ : syracuseStep 1680839 = 2521259) B2521259
theorem B2835931 : Blo 1680040 2835931 := bstep (se 1 (by rfl) ⟨2126948, by rfl⟩ : syracuseStep 2835931 = 4253897) B4253897
theorem B1680859 : Blo 1680040 1680859 := bstep (se 1 (by rfl) ⟨1260644, by rfl⟩ : syracuseStep 1680859 = 2521289) B2521289
theorem B3409427 : Blo 1680040 3409427 := bstep (se 1 (by rfl) ⟨2557070, by rfl⟩ : syracuseStep 3409427 = 5114141) B5114141
theorem B1680935 : Blo 1680040 1680935 := bstep (se 1 (by rfl) ⟨1260701, by rfl⟩ : syracuseStep 1680935 = 2521403) B2521403
theorem B1680975 : Blo 1680040 1680975 := bstep (se 1 (by rfl) ⟨1260731, by rfl⟩ : syracuseStep 1680975 = 2521463) B2521463
theorem B1680991 : Blo 1680040 1680991 := bstep (se 1 (by rfl) ⟨1260743, by rfl⟩ : syracuseStep 1680991 = 2521487) B2521487
theorem B1681019 : Blo 1680040 1681019 := bstep (se 1 (by rfl) ⟨1260764, by rfl⟩ : syracuseStep 1681019 = 2521529) B2521529
theorem B5670539 : Blo 1680040 5670539 := bstep (se 1 (by rfl) ⟨4252904, by rfl⟩ : syracuseStep 5670539 = 8505809) B8505809
theorem B1681071 : Blo 1680040 1681071 := bstep (se 1 (by rfl) ⟨1260803, by rfl⟩ : syracuseStep 1681071 = 2521607) B2521607
theorem B1681095 : Blo 1680040 1681095 := bstep (se 1 (by rfl) ⟨1260821, by rfl⟩ : syracuseStep 1681095 = 2521643) B2521643
theorem B4785875 : Blo 1680040 4785875 := bstep (se 1 (by rfl) ⟨3589406, by rfl⟩ : syracuseStep 4785875 = 7178813) B7178813
theorem B19146455 : Blo 1680040 19146455 := bstep (se 1 (by rfl) ⟨14359841, by rfl⟩ : syracuseStep 19146455 = 28719683) B28719683
theorem B1681115 : Blo 1680040 1681115 := bstep (se 1 (by rfl) ⟨1260836, by rfl⟩ : syracuseStep 1681115 = 2521673) B2521673
theorem B109078265 : Blo 1680040 109078265 := bstep (se 2 (by rfl) ⟨40904349, by rfl⟩ : syracuseStep 109078265 = 81808699) B81808699
theorem B1681191 : Blo 1680040 1681191 := bstep (se 1 (by rfl) ⟨1260893, by rfl⟩ : syracuseStep 1681191 = 2521787) B2521787
theorem B1681231 : Blo 1680040 1681231 := bstep (se 1 (by rfl) ⟨1260923, by rfl⟩ : syracuseStep 1681231 = 2521847) B2521847
theorem B1681247 : Blo 1680040 1681247 := bstep (se 1 (by rfl) ⟨1260935, by rfl⟩ : syracuseStep 1681247 = 2521871) B2521871
theorem B4040543 : Blo 1680040 4040543 := bstep (se 1 (by rfl) ⟨3030407, by rfl⟩ : syracuseStep 4040543 = 6060815) B6060815
theorem B1681275 : Blo 1680040 1681275 := bstep (se 1 (by rfl) ⟨1260956, by rfl⟩ : syracuseStep 1681275 = 2521913) B2521913
theorem B1681327 : Blo 1680040 1681327 := bstep (se 1 (by rfl) ⟨1260995, by rfl⟩ : syracuseStep 1681327 = 2521991) B2521991
theorem B2394031 : Blo 1680040 2394031 := bstep (se 1 (by rfl) ⟨1795523, by rfl⟩ : syracuseStep 2394031 = 3591047) B3591047
theorem B5113775 : Blo 1680040 5113775 := bstep (se 1 (by rfl) ⟨3835331, by rfl⟩ : syracuseStep 5113775 = 7670663) B7670663
theorem B1681351 : Blo 1680040 1681351 := bstep (se 1 (by rfl) ⟨1261013, by rfl⟩ : syracuseStep 1681351 = 2522027) B2522027
theorem B1681371 : Blo 1680040 1681371 := bstep (se 1 (by rfl) ⟨1261028, by rfl⟩ : syracuseStep 1681371 = 2522057) B2522057
theorem B1681447 : Blo 1680040 1681447 := bstep (se 1 (by rfl) ⟨1261085, by rfl⟩ : syracuseStep 1681447 = 2522171) B2522171
theorem B2836559 : Blo 1680040 2836559 := bstep (se 1 (by rfl) ⟨2127419, by rfl⟩ : syracuseStep 2836559 = 4254839) B4254839
theorem B1681487 : Blo 1680040 1681487 := bstep (se 1 (by rfl) ⟨1261115, by rfl⟩ : syracuseStep 1681487 = 2522231) B2522231
theorem B1681503 : Blo 1680040 1681503 := bstep (se 1 (by rfl) ⟨1261127, by rfl⟩ : syracuseStep 1681503 = 2522255) B2522255
theorem B9701491 : Blo 1680040 9701491 := bstep (se 1 (by rfl) ⟨7276118, by rfl⟩ : syracuseStep 9701491 = 14552237) B14552237
theorem B6383731 : Blo 1680040 6383731 := bstep (se 1 (by rfl) ⟨4787798, by rfl⟩ : syracuseStep 6383731 = 9575597) B9575597
theorem B1681531 : Blo 1680040 1681531 := bstep (se 1 (by rfl) ⟨1261148, by rfl⟩ : syracuseStep 1681531 = 2522297) B2522297
theorem B6138013 : Blo 1680040 6138013 := bstep (se 3 (by rfl) ⟨1150877, by rfl⟩ : syracuseStep 6138013 = 2301755) B2301755
theorem B4253867 : Blo 1680040 4253867 := bstep (se 1 (by rfl) ⟨3190400, by rfl⟩ : syracuseStep 4253867 = 6380801) B6380801
theorem B1681583 : Blo 1680040 1681583 := bstep (se 1 (by rfl) ⟨1261187, by rfl⟩ : syracuseStep 1681583 = 2522375) B2522375
theorem B1681607 : Blo 1680040 1681607 := bstep (se 1 (by rfl) ⟨1261205, by rfl⟩ : syracuseStep 1681607 = 2522411) B2522411
theorem B1681627 : Blo 1680040 1681627 := bstep (se 1 (by rfl) ⟨1261220, by rfl⟩ : syracuseStep 1681627 = 2522441) B2522441
theorem B1681703 : Blo 1680040 1681703 := bstep (se 1 (by rfl) ⟨1261277, by rfl⟩ : syracuseStep 1681703 = 2522555) B2522555
theorem B1681743 : Blo 1680040 1681743 := bstep (se 1 (by rfl) ⟨1261307, by rfl⟩ : syracuseStep 1681743 = 2522615) B2522615
theorem B1681759 : Blo 1680040 1681759 := bstep (se 1 (by rfl) ⟨1261319, by rfl⟩ : syracuseStep 1681759 = 2522639) B2522639
theorem B1681787 : Blo 1680040 1681787 := bstep (se 1 (by rfl) ⟨1261340, by rfl⟩ : syracuseStep 1681787 = 2522681) B2522681
theorem B1681839 : Blo 1680040 1681839 := bstep (se 1 (by rfl) ⟨1261379, by rfl⟩ : syracuseStep 1681839 = 2522759) B2522759
theorem B1681863 : Blo 1680040 1681863 := bstep (se 1 (by rfl) ⟨1261397, by rfl⟩ : syracuseStep 1681863 = 2522795) B2522795
theorem B1681883 : Blo 1680040 1681883 := bstep (se 1 (by rfl) ⟨1261412, by rfl⟩ : syracuseStep 1681883 = 2522825) B2522825
theorem B7670297 : Blo 1680040 7670297 := bstep (se 2 (by rfl) ⟨2876361, by rfl⟩ : syracuseStep 7670297 = 5752723) B5752723
theorem B5671457 : Blo 1680040 5671457 := bstep (se 2 (by rfl) ⟨2126796, by rfl⟩ : syracuseStep 5671457 = 4253593) B4253593
theorem B5114407 : Blo 1680040 5114407 := bstep (se 1 (by rfl) ⟨3835805, by rfl⟩ : syracuseStep 5114407 = 7671611) B7671611
theorem B1681959 : Blo 1680040 1681959 := bstep (se 1 (by rfl) ⟨1261469, by rfl⟩ : syracuseStep 1681959 = 2522939) B2522939
theorem B1681999 : Blo 1680040 1681999 := bstep (se 1 (by rfl) ⟨1261499, by rfl⟩ : syracuseStep 1681999 = 2522999) B2522999
theorem B1682015 : Blo 1680040 1682015 := bstep (se 1 (by rfl) ⟨1261511, by rfl⟩ : syracuseStep 1682015 = 2523023) B2523023
theorem B5384839 : Blo 1680040 5384839 := bstep (se 1 (by rfl) ⟨4038629, by rfl⟩ : syracuseStep 5384839 = 8077259) B8077259
theorem B10775213 : Blo 1680040 10775213 := bstep (se 3 (by rfl) ⟨2020352, by rfl⟩ : syracuseStep 10775213 = 4040705) B4040705
theorem B8514233 : Blo 1680040 8514233 := bstep (se 2 (by rfl) ⟨3192837, by rfl⟩ : syracuseStep 8514233 = 6385675) B6385675
theorem B4786877 : Blo 1680040 4786877 := bstep (se 3 (by rfl) ⟨897539, by rfl⟩ : syracuseStep 4786877 = 1795079) B1795079
theorem B3590867 : Blo 1680040 3590867 := bstep (se 1 (by rfl) ⟨2693150, by rfl⟩ : syracuseStep 3590867 = 5386301) B5386301
theorem B27257573 : Blo 1680040 27257573 := bstep (se 4 (by rfl) ⟨2555397, by rfl⟩ : syracuseStep 27257573 = 5110795) B5110795
theorem B5671673 : Blo 1680040 5671673 := bstep (se 2 (by rfl) ⟨2126877, by rfl⟩ : syracuseStep 5671673 = 4253755) B4253755
theorem B5991241 : Blo 1680040 5991241 := bstep (se 2 (by rfl) ⟨2246715, by rfl⟩ : syracuseStep 5991241 = 4493431) B4493431
theorem B3189611 : Blo 1680040 3189611 := bstep (se 1 (by rfl) ⟨2392208, by rfl⟩ : syracuseStep 3189611 = 4784417) B4784417
theorem B6384491 : Blo 1680040 6384491 := bstep (se 1 (by rfl) ⟨4788368, by rfl⟩ : syracuseStep 6384491 = 9576737) B9576737
theorem B2837423 : Blo 1680040 2837423 := bstep (se 1 (by rfl) ⟨2128067, by rfl⟩ : syracuseStep 2837423 = 4256135) B4256135
theorem B8506295 : Blo 1680040 8506295 := bstep (se 1 (by rfl) ⟨6379721, by rfl⟩ : syracuseStep 8506295 = 12759443) B12759443
theorem B5671943 : Blo 1680040 5671943 := bstep (se 1 (by rfl) ⟨4253957, by rfl⟩ : syracuseStep 5671943 = 8507915) B8507915
theorem B4254727 : Blo 1680040 4254727 := bstep (se 1 (by rfl) ⟨3191045, by rfl⟩ : syracuseStep 4254727 = 6382091) B6382091
theorem B4787207 : Blo 1680040 4787207 := bstep (se 1 (by rfl) ⟨3590405, by rfl⟩ : syracuseStep 4787207 = 7180811) B7180811
theorem B5672051 : Blo 1680040 5672051 := bstep (se 1 (by rfl) ⟨4254038, by rfl⟩ : syracuseStep 5672051 = 8508077) B8508077
theorem B7179511 : Blo 1680040 7179511 := bstep (se 1 (by rfl) ⟨5384633, by rfl⟩ : syracuseStep 7179511 = 10769267) B10769267
theorem B32304419 : Blo 1680040 32304419 := bstep (se 1 (by rfl) ⟨24228314, by rfl⟩ : syracuseStep 32304419 = 48456629) B48456629
theorem B2837855 : Blo 1680040 2837855 := bstep (se 1 (by rfl) ⟨2128391, by rfl⟩ : syracuseStep 2837855 = 4256783) B4256783
theorem B5672321 : Blo 1680040 5672321 := bstep (se 2 (by rfl) ⟨2127120, by rfl⟩ : syracuseStep 5672321 = 4254241) B4254241
theorem B403787213 : Blo 1680040 403787213 := bstep (se 3 (by rfl) ⟨75710102, by rfl⟩ : syracuseStep 403787213 = 151420205) B151420205
theorem B3190279 : Blo 1680040 3190279 := bstep (se 1 (by rfl) ⟨2392709, by rfl⟩ : syracuseStep 3190279 = 4785419) B4785419
theorem B3689993 : Blo 1680040 3689993 := bstep (se 2 (by rfl) ⟨1383747, by rfl⟩ : syracuseStep 3689993 = 2767495) B2767495
theorem B4255355 : Blo 1680040 4255355 := bstep (se 1 (by rfl) ⟨3191516, by rfl⟩ : syracuseStep 4255355 = 6383033) B6383033
theorem B12275347 : Blo 1680040 12275347 := bstep (se 1 (by rfl) ⟨9206510, by rfl⟩ : syracuseStep 12275347 = 18413021) B18413021
theorem B27250499 : Blo 1680040 27250499 := bstep (se 1 (by rfl) ⟨20437874, by rfl⟩ : syracuseStep 27250499 = 40875749) B40875749
theorem B7180127 : Blo 1680040 7180127 := bstep (se 1 (by rfl) ⟨5385095, by rfl⟩ : syracuseStep 7180127 = 10770191) B10770191
theorem B11505503 : Blo 1680040 11505503 := bstep (se 1 (by rfl) ⟨8629127, by rfl⟩ : syracuseStep 11505503 = 17258255) B17258255
theorem B2838415 : Blo 1680040 2838415 := bstep (se 1 (by rfl) ⟨2128811, by rfl⟩ : syracuseStep 2838415 = 4257623) B4257623
theorem B4255649 : Blo 1680040 4255649 := bstep (se 2 (by rfl) ⟨1595868, by rfl⟩ : syracuseStep 4255649 = 3191737) B3191737
theorem B4853665 : Blo 1680040 4853665 := bstep (se 2 (by rfl) ⟨1820124, by rfl⟩ : syracuseStep 4853665 = 3640249) B3640249
theorem B3592097 : Blo 1680040 3592097 := bstep (se 2 (by rfl) ⟨1347036, by rfl⟩ : syracuseStep 3592097 = 2694073) B2694073
theorem B3780539 : Blo 1680040 3780539 := bstep (se 1 (by rfl) ⟨2835404, by rfl⟩ : syracuseStep 3780539 = 5670809) B5670809
theorem B5386171 : Blo 1680040 5386171 := bstep (se 1 (by rfl) ⟨4039628, by rfl⟩ : syracuseStep 5386171 = 8079257) B8079257
theorem B19140623 : Blo 1680040 19140623 := bstep (se 1 (by rfl) ⟨14355467, by rfl⟩ : syracuseStep 19140623 = 28710935) B28710935
theorem B3780665 : Blo 1680040 3780665 := bstep (se 2 (by rfl) ⟨1417749, by rfl⟩ : syracuseStep 3780665 = 2835499) B2835499
theorem B9089081 : Blo 1680040 9089081 := bstep (se 2 (by rfl) ⟨3408405, by rfl⟩ : syracuseStep 9089081 = 6816811) B6816811
theorem B14356561 : Blo 1680040 14356561 := bstep (se 2 (by rfl) ⟨5383710, by rfl⟩ : syracuseStep 14356561 = 10767421) B10767421
theorem B5673131 : Blo 1680040 5673131 := bstep (se 1 (by rfl) ⟨4254848, by rfl⟩ : syracuseStep 5673131 = 8509697) B8509697
theorem B8507753 : Blo 1680040 8507753 := bstep (se 2 (by rfl) ⟨3190407, by rfl⟩ : syracuseStep 8507753 = 6380815) B6380815
theorem B3781007 : Blo 1680040 3781007 := bstep (se 1 (by rfl) ⟨2835755, by rfl⟩ : syracuseStep 3781007 = 5671511) B5671511
theorem B26604035 : Blo 1680040 26604035 := bstep (se 1 (by rfl) ⟨19953026, by rfl⟩ : syracuseStep 26604035 = 39906053) B39906053
theorem B10220057 : Blo 1680040 10220057 := bstep (se 2 (by rfl) ⟨3832521, by rfl⟩ : syracuseStep 10220057 = 7665043) B7665043
theorem B19149371 : Blo 1680040 19149371 := bstep (se 1 (by rfl) ⟨14362028, by rfl⟩ : syracuseStep 19149371 = 28724057) B28724057
theorem B5673671 : Blo 1680040 5673671 := bstep (se 1 (by rfl) ⟨4255253, by rfl⟩ : syracuseStep 5673671 = 8510507) B8510507
theorem B3781331 : Blo 1680040 3781331 := bstep (se 1 (by rfl) ⟨2835998, by rfl⟩ : syracuseStep 3781331 = 5671997) B5671997
theorem B2520143 : Blo 1680040 2520143 := bstep (se 1 (by rfl) ⟨1890107, by rfl⟩ : syracuseStep 2520143 = 3780215) B3780215
theorem B2520263 : Blo 1680040 2520263 := bstep (se 1 (by rfl) ⟨1890197, by rfl⟩ : syracuseStep 2520263 = 3780395) B3780395
theorem B9090251 : Blo 1680040 9090251 := bstep (se 1 (by rfl) ⟨6817688, by rfl⟩ : syracuseStep 9090251 = 13635377) B13635377
theorem B2520425 : Blo 1680040 2520425 := bstep (se 2 (by rfl) ⟨945159, by rfl⟩ : syracuseStep 2520425 = 1890319) B1890319
theorem B24237427 : Blo 1680040 24237427 := bstep (se 1 (by rfl) ⟨18178070, by rfl⟩ : syracuseStep 24237427 = 36356141) B36356141
theorem B36369809 : Blo 1680040 36369809 := bstep (se 2 (by rfl) ⟨13638678, by rfl⟩ : syracuseStep 36369809 = 27277357) B27277357
theorem B12768677 : Blo 1680040 12768677 := bstep (se 4 (by rfl) ⟨1197063, by rfl⟩ : syracuseStep 12768677 = 2394127) B2394127
theorem B2520503 : Blo 1680040 2520503 := bstep (se 1 (by rfl) ⟨1890377, by rfl⟩ : syracuseStep 2520503 = 3780755) B3780755
theorem B2520539 : Blo 1680040 2520539 := bstep (se 1 (by rfl) ⟨1890404, by rfl⟩ : syracuseStep 2520539 = 3780809) B3780809
theorem B2127323 : Blo 1680040 2127323 := bstep (se 1 (by rfl) ⟨1595492, by rfl⟩ : syracuseStep 2127323 = 3190985) B3190985
theorem B32765429 : Blo 1680040 32765429 := bstep (se 5 (by rfl) ⟨1535879, by rfl⟩ : syracuseStep 32765429 = 3071759) B3071759
theorem B5674535 : Blo 1680040 5674535 := bstep (se 1 (by rfl) ⟨4255901, by rfl⟩ : syracuseStep 5674535 = 8511803) B8511803
theorem B4257319 : Blo 1680040 4257319 := bstep (se 1 (by rfl) ⟨3192989, by rfl⟩ : syracuseStep 4257319 = 6385979) B6385979
theorem B5748347 : Blo 1680040 5748347 := bstep (se 1 (by rfl) ⟨4311260, by rfl⟩ : syracuseStep 5748347 = 8622521) B8622521
theorem B3782267 : Blo 1680040 3782267 := bstep (se 1 (by rfl) ⟨2836700, by rfl⟩ : syracuseStep 3782267 = 5673401) B5673401
theorem B3192443 : Blo 1680040 3192443 := bstep (se 1 (by rfl) ⟨2394332, by rfl⟩ : syracuseStep 3192443 = 4788665) B4788665
theorem B5674643 : Blo 1680040 5674643 := bstep (se 1 (by rfl) ⟨4255982, by rfl⟩ : syracuseStep 5674643 = 8511965) B8511965
theorem B2692855 : Blo 1680040 2692855 := bstep (se 1 (by rfl) ⟨2019641, by rfl⟩ : syracuseStep 2692855 = 4039283) B4039283
theorem B3782393 : Blo 1680040 3782393 := bstep (se 2 (by rfl) ⟨1418397, by rfl⟩ : syracuseStep 3782393 = 2836795) B2836795
theorem B3192671 : Blo 1680040 3192671 := bstep (se 1 (by rfl) ⟨2394503, by rfl⟩ : syracuseStep 3192671 = 4789007) B4789007
theorem B5674859 : Blo 1680040 5674859 := bstep (se 1 (by rfl) ⟨4256144, by rfl⟩ : syracuseStep 5674859 = 8512289) B8512289
theorem B4257643 : Blo 1680040 4257643 := bstep (se 1 (by rfl) ⟨3193232, by rfl⟩ : syracuseStep 4257643 = 6386465) B6386465
theorem B5674913 : Blo 1680040 5674913 := bstep (se 2 (by rfl) ⟨2128092, by rfl⟩ : syracuseStep 5674913 = 4256185) B4256185
theorem B2521007 : Blo 1680040 2521007 := bstep (se 1 (by rfl) ⟨1890755, by rfl⟩ : syracuseStep 2521007 = 3781511) B3781511
theorem B2127799 : Blo 1680040 2127799 := bstep (se 1 (by rfl) ⟨1595849, by rfl⟩ : syracuseStep 2127799 = 3191699) B3191699
theorem B15546305 : Blo 1680040 15546305 := bstep (se 2 (by rfl) ⟨5829864, by rfl⟩ : syracuseStep 15546305 = 11659729) B11659729
theorem B3782663 : Blo 1680040 3782663 := bstep (se 1 (by rfl) ⟨2836997, by rfl⟩ : syracuseStep 3782663 = 5673995) B5673995
theorem B2521097 : Blo 1680040 2521097 := bstep (se 2 (by rfl) ⟨945411, by rfl⟩ : syracuseStep 2521097 = 1890823) B1890823
theorem B2521127 : Blo 1680040 2521127 := bstep (se 1 (by rfl) ⟨1890845, by rfl⟩ : syracuseStep 2521127 = 3781691) B3781691
theorem B3782735 : Blo 1680040 3782735 := bstep (se 1 (by rfl) ⟨2837051, by rfl⟩ : syracuseStep 3782735 = 5674103) B5674103
theorem B3192929 : Blo 1680040 3192929 := bstep (se 2 (by rfl) ⟨1197348, by rfl⟩ : syracuseStep 3192929 = 2394697) B2394697
theorem B1890427 : Blo 1680040 1890427 := bstep (se 1 (by rfl) ⟨1417820, by rfl⟩ : syracuseStep 1890427 = 2835641) B2835641
theorem B2521211 : Blo 1680040 2521211 := bstep (se 1 (by rfl) ⟨1890908, by rfl⟩ : syracuseStep 2521211 = 3781817) B3781817
theorem B2521337 : Blo 1680040 2521337 := bstep (se 2 (by rfl) ⟨945501, by rfl⟩ : syracuseStep 2521337 = 1891003) B1891003
theorem B2521439 : Blo 1680040 2521439 := bstep (se 1 (by rfl) ⟨1891079, by rfl⟩ : syracuseStep 2521439 = 3782159) B3782159
theorem B2521451 : Blo 1680040 2521451 := bstep (se 1 (by rfl) ⟨1891088, by rfl⟩ : syracuseStep 2521451 = 3782177) B3782177
theorem B3193195 : Blo 1680040 3193195 := bstep (se 1 (by rfl) ⟨2394896, by rfl⟩ : syracuseStep 3193195 = 4789793) B4789793
theorem B3783131 : Blo 1680040 3783131 := bstep (se 1 (by rfl) ⟨2837348, by rfl⟩ : syracuseStep 3783131 = 5674697) B5674697
theorem B5675507 : Blo 1680040 5675507 := bstep (se 1 (by rfl) ⟨4256630, by rfl⟩ : syracuseStep 5675507 = 8513261) B8513261
theorem B1890895 : Blo 1680040 1890895 := bstep (se 1 (by rfl) ⟨1418171, by rfl⟩ : syracuseStep 1890895 = 2836343) B2836343
theorem B2521679 : Blo 1680040 2521679 := bstep (se 1 (by rfl) ⟨1891259, by rfl⟩ : syracuseStep 2521679 = 3782519) B3782519
theorem B2521799 : Blo 1680040 2521799 := bstep (se 1 (by rfl) ⟨1891349, by rfl⟩ : syracuseStep 2521799 = 3782699) B3782699
theorem B6060743 : Blo 1680040 6060743 := bstep (se 1 (by rfl) ⟨4545557, by rfl⟩ : syracuseStep 6060743 = 9091115) B9091115
theorem B5249747 : Blo 1680040 5249747 := bstep (se 1 (by rfl) ⟨3937310, by rfl⟩ : syracuseStep 5249747 = 7874621) B7874621
theorem B2521961 : Blo 1680040 2521961 := bstep (se 2 (by rfl) ⟨945735, by rfl⟩ : syracuseStep 2521961 = 1891471) B1891471
theorem B22993811 : Blo 1680040 22993811 := bstep (se 1 (by rfl) ⟨17245358, by rfl⟩ : syracuseStep 22993811 = 34490717) B34490717
theorem B3783599 : Blo 1680040 3783599 := bstep (se 1 (by rfl) ⟨2837699, by rfl⟩ : syracuseStep 3783599 = 5675399) B5675399
theorem B2522039 : Blo 1680040 2522039 := bstep (se 1 (by rfl) ⟨1891529, by rfl⟩ : syracuseStep 2522039 = 3783059) B3783059
theorem B1891291 : Blo 1680040 1891291 := bstep (se 1 (by rfl) ⟨1418468, by rfl⟩ : syracuseStep 1891291 = 2836937) B2836937
theorem B2522075 : Blo 1680040 2522075 := bstep (se 1 (by rfl) ⟨1891556, by rfl⟩ : syracuseStep 2522075 = 3783113) B3783113
theorem B5676047 : Blo 1680040 5676047 := bstep (se 1 (by rfl) ⟨4257035, by rfl⟩ : syracuseStep 5676047 = 8514071) B8514071
theorem B4037651 : Blo 1680040 4037651 := bstep (se 1 (by rfl) ⟨3028238, by rfl⟩ : syracuseStep 4037651 = 6056477) B6056477
theorem B6814799 : Blo 1680040 6814799 := bstep (se 1 (by rfl) ⟨5111099, by rfl⟩ : syracuseStep 6814799 = 10222199) B10222199
theorem B3783851 : Blo 1680040 3783851 := bstep (se 1 (by rfl) ⟨2837888, by rfl⟩ : syracuseStep 3783851 = 5675777) B5675777
theorem B12762359 : Blo 1680040 12762359 := bstep (se 1 (by rfl) ⟨9571769, by rfl⟩ : syracuseStep 12762359 = 19143539) B19143539
theorem B1891759 : Blo 1680040 1891759 := bstep (se 1 (by rfl) ⟨1418819, by rfl⟩ : syracuseStep 1891759 = 2837639) B2837639
theorem B2522543 : Blo 1680040 2522543 := bstep (se 1 (by rfl) ⟨1891907, by rfl⟩ : syracuseStep 2522543 = 3783815) B3783815
theorem B3407287 : Blo 1680040 3407287 := bstep (se 1 (by rfl) ⟨2555465, by rfl⟩ : syracuseStep 3407287 = 5110931) B5110931
theorem B2522633 : Blo 1680040 2522633 := bstep (se 2 (by rfl) ⟨945987, by rfl⟩ : syracuseStep 2522633 = 1891975) B1891975
theorem B6381089 : Blo 1680040 6381089 := bstep (se 2 (by rfl) ⟨2392908, by rfl⟩ : syracuseStep 6381089 = 4785817) B4785817
theorem B2522663 : Blo 1680040 2522663 := bstep (se 1 (by rfl) ⟨1891997, by rfl⟩ : syracuseStep 2522663 = 3783995) B3783995
theorem B5676641 : Blo 1680040 5676641 := bstep (se 2 (by rfl) ⟨2128740, by rfl⟩ : syracuseStep 5676641 = 4257481) B4257481
theorem B2522747 : Blo 1680040 2522747 := bstep (se 1 (by rfl) ⟨1892060, by rfl⟩ : syracuseStep 2522747 = 3784121) B3784121
theorem B3784391 : Blo 1680040 3784391 := bstep (se 1 (by rfl) ⟨2838293, by rfl⟩ : syracuseStep 3784391 = 5676587) B5676587
theorem B12762845 : Blo 1680040 12762845 := bstep (se 3 (by rfl) ⟨2393033, by rfl⟩ : syracuseStep 12762845 = 4786067) B4786067
theorem B2522873 : Blo 1680040 2522873 := bstep (se 2 (by rfl) ⟨946077, by rfl⟩ : syracuseStep 2522873 = 1892155) B1892155
theorem B1892191 : Blo 1680040 1892191 := bstep (se 1 (by rfl) ⟨1419143, by rfl⟩ : syracuseStep 1892191 = 2838287) B2838287
theorem B2522975 : Blo 1680040 2522975 := bstep (se 1 (by rfl) ⟨1892231, by rfl⟩ : syracuseStep 2522975 = 3784463) B3784463
theorem B2522987 : Blo 1680040 2522987 := bstep (se 1 (by rfl) ⟨1892240, by rfl⟩ : syracuseStep 2522987 = 3784481) B3784481
theorem B12935321 : Blo 1680040 12935321 := bstep (se 2 (by rfl) ⟨4850745, by rfl⟩ : syracuseStep 12935321 = 9701491) B9701491
theorem B8511641 : Blo 1680040 8511641 := bstep (se 2 (by rfl) ⟨3191865, by rfl⟩ : syracuseStep 8511641 = 6383731) B6383731
theorem B8184017 : Blo 1680040 8184017 := bstep (se 2 (by rfl) ⟨3069006, by rfl⟩ : syracuseStep 8184017 = 6138013) B6138013
theorem B23003443 : Blo 1680040 23003443 := bstep (se 1 (by rfl) ⟨17252582, by rfl⟩ : syracuseStep 23003443 = 34505165) B34505165
theorem B17736023 : Blo 1680040 17736023 := bstep (se 1 (by rfl) ⟨13302017, by rfl⟩ : syracuseStep 17736023 = 26604035) B26604035
theorem B7176539 : Blo 1680040 7176539 := bstep (se 1 (by rfl) ⟨5382404, by rfl⟩ : syracuseStep 7176539 = 10764809) B10764809
theorem B13812133 : Blo 1680040 13812133 := bstep (se 4 (by rfl) ⟨1294887, by rfl⟩ : syracuseStep 13812133 = 2589775) B2589775
theorem B4784609 : Blo 1680040 4784609 := bstep (se 2 (by rfl) ⟨1794228, by rfl⟩ : syracuseStep 4784609 = 3588457) B3588457
theorem B9208417 : Blo 1680040 9208417 := bstep (se 2 (by rfl) ⟨3453156, by rfl⟩ : syracuseStep 9208417 = 6906313) B6906313
theorem B1680095 : Blo 1680040 1680095 := bstep (se 1 (by rfl) ⟨1260071, by rfl⟩ : syracuseStep 1680095 = 2520143) B2520143
theorem B4850399 : Blo 1680040 4850399 := bstep (se 1 (by rfl) ⟨3637799, by rfl⟩ : syracuseStep 4850399 = 7275599) B7275599
theorem B14353145 : Blo 1680040 14353145 := bstep (se 2 (by rfl) ⟨5382429, by rfl⟩ : syracuseStep 14353145 = 10764859) B10764859
theorem B1680175 : Blo 1680040 1680175 := bstep (se 1 (by rfl) ⟨1260131, by rfl⟩ : syracuseStep 1680175 = 2520263) B2520263
theorem B69043043 : Blo 1680040 69043043 := bstep (se 1 (by rfl) ⟨51782282, by rfl⟩ : syracuseStep 69043043 = 103564565) B103564565
theorem B1680283 : Blo 1680040 1680283 := bstep (se 1 (by rfl) ⟨1260212, by rfl⟩ : syracuseStep 1680283 = 2520425) B2520425
theorem B2835371 : Blo 1680040 2835371 := bstep (se 1 (by rfl) ⟨2126528, by rfl⟩ : syracuseStep 2835371 = 4253057) B4253057
theorem B8512451 : Blo 1680040 8512451 := bstep (se 1 (by rfl) ⟨6384338, by rfl⟩ : syracuseStep 8512451 = 12768677) B12768677
theorem B1680335 : Blo 1680040 1680335 := bstep (se 1 (by rfl) ⟨1260251, by rfl⟩ : syracuseStep 1680335 = 2520503) B2520503
theorem B1680359 : Blo 1680040 1680359 := bstep (se 1 (by rfl) ⟨1260269, by rfl⟩ : syracuseStep 1680359 = 2520539) B2520539
theorem B7988321 : Blo 1680040 7988321 := bstep (se 2 (by rfl) ⟨2995620, by rfl⟩ : syracuseStep 7988321 = 5991241) B5991241
theorem B12764303 : Blo 1680040 12764303 := bstep (se 1 (by rfl) ⟨9573227, by rfl⟩ : syracuseStep 12764303 = 19146455) B19146455
theorem B1680671 : Blo 1680040 1680671 := bstep (se 1 (by rfl) ⟨1260503, by rfl⟩ : syracuseStep 1680671 = 2521007) B2521007
theorem B3409183 : Blo 1680040 3409183 := bstep (se 1 (by rfl) ⟨2556887, by rfl⟩ : syracuseStep 3409183 = 5113775) B5113775
theorem B14361893 : Blo 1680040 14361893 := bstep (se 4 (by rfl) ⟨1346427, by rfl⟩ : syracuseStep 14361893 = 2692855) B2692855
theorem B10364203 : Blo 1680040 10364203 := bstep (se 1 (by rfl) ⟨7773152, by rfl⟩ : syracuseStep 10364203 = 15546305) B15546305
theorem B1680731 : Blo 1680040 1680731 := bstep (se 1 (by rfl) ⟨1260548, by rfl⟩ : syracuseStep 1680731 = 2521097) B2521097
theorem B9839981 : Blo 1680040 9839981 := bstep (se 3 (by rfl) ⟨1844996, by rfl⟩ : syracuseStep 9839981 = 3689993) B3689993
theorem B1680751 : Blo 1680040 1680751 := bstep (se 1 (by rfl) ⟨1260563, by rfl⟩ : syracuseStep 1680751 = 2521127) B2521127
theorem B1680807 : Blo 1680040 1680807 := bstep (se 1 (by rfl) ⟨1260605, by rfl⟩ : syracuseStep 1680807 = 2521211) B2521211
theorem B2835911 : Blo 1680040 2835911 := bstep (se 1 (by rfl) ⟨2126933, by rfl⟩ : syracuseStep 2835911 = 4253867) B4253867
theorem B1680891 : Blo 1680040 1680891 := bstep (se 1 (by rfl) ⟨1260668, by rfl⟩ : syracuseStep 1680891 = 2521337) B2521337
theorem B1680959 : Blo 1680040 1680959 := bstep (se 1 (by rfl) ⟨1260719, by rfl⟩ : syracuseStep 1680959 = 2521439) B2521439
theorem B1680967 : Blo 1680040 1680967 := bstep (se 1 (by rfl) ⟨1260725, by rfl⟩ : syracuseStep 1680967 = 2521451) B2521451
theorem B15328925 : Blo 1680040 15328925 := bstep (se 3 (by rfl) ⟨2874173, by rfl⟩ : syracuseStep 15328925 = 5748347) B5748347
theorem B5113531 : Blo 1680040 5113531 := bstep (se 1 (by rfl) ⟨3835148, by rfl⟩ : syracuseStep 5113531 = 7670297) B7670297
theorem B16156361 : Blo 1680040 16156361 := bstep (se 2 (by rfl) ⟨6058635, by rfl⟩ : syracuseStep 16156361 = 12117271) B12117271
theorem B1681119 : Blo 1680040 1681119 := bstep (se 1 (by rfl) ⟨1260839, by rfl⟩ : syracuseStep 1681119 = 2521679) B2521679
theorem B1681199 : Blo 1680040 1681199 := bstep (se 1 (by rfl) ⟨1260899, by rfl⟩ : syracuseStep 1681199 = 2521799) B2521799
theorem B4040495 : Blo 1680040 4040495 := bstep (se 1 (by rfl) ⟨3030371, by rfl⟩ : syracuseStep 4040495 = 6060743) B6060743
theorem B3499831 : Blo 1680040 3499831 := bstep (se 1 (by rfl) ⟨2624873, by rfl⟩ : syracuseStep 3499831 = 5249747) B5249747
theorem B2393911 : Blo 1680040 2393911 := bstep (se 1 (by rfl) ⟨1795433, by rfl⟩ : syracuseStep 2393911 = 3590867) B3590867
theorem B18171715 : Blo 1680040 18171715 := bstep (se 1 (by rfl) ⟨13628786, by rfl⟩ : syracuseStep 18171715 = 27257573) B27257573
theorem B1681307 : Blo 1680040 1681307 := bstep (se 1 (by rfl) ⟨1260980, by rfl⟩ : syracuseStep 1681307 = 2521961) B2521961
theorem B15329207 : Blo 1680040 15329207 := bstep (se 1 (by rfl) ⟨11496905, by rfl⟩ : syracuseStep 15329207 = 22993811) B22993811
theorem B5670863 : Blo 1680040 5670863 := bstep (se 1 (by rfl) ⟨4253147, by rfl⟩ : syracuseStep 5670863 = 8506295) B8506295
theorem B1681359 : Blo 1680040 1681359 := bstep (se 1 (by rfl) ⟨1261019, by rfl⟩ : syracuseStep 1681359 = 2522039) B2522039
theorem B1681383 : Blo 1680040 1681383 := bstep (se 1 (by rfl) ⟨1261037, by rfl⟩ : syracuseStep 1681383 = 2522075) B2522075
theorem B4253705 : Blo 1680040 4253705 := bstep (se 2 (by rfl) ⟨1595139, by rfl⟩ : syracuseStep 4253705 = 3190279) B3190279
theorem B30681341 : Blo 1680040 30681341 := bstep (se 3 (by rfl) ⟨5752751, by rfl⟩ : syracuseStep 30681341 = 11505503) B11505503
theorem B10774781 : Blo 1680040 10774781 := bstep (se 3 (by rfl) ⟨2020271, by rfl⟩ : syracuseStep 10774781 = 4040543) B4040543
theorem B1681695 : Blo 1680040 1681695 := bstep (se 1 (by rfl) ⟨1261271, by rfl⟩ : syracuseStep 1681695 = 2522543) B2522543
theorem B269191475 : Blo 1680040 269191475 := bstep (se 1 (by rfl) ⟨201893606, by rfl⟩ : syracuseStep 269191475 = 403787213) B403787213
theorem B1681755 : Blo 1680040 1681755 := bstep (se 1 (by rfl) ⟨1261316, by rfl⟩ : syracuseStep 1681755 = 2522633) B2522633
theorem B4254059 : Blo 1680040 4254059 := bstep (se 1 (by rfl) ⟨3190544, by rfl⟩ : syracuseStep 4254059 = 6381089) B6381089
theorem B1681775 : Blo 1680040 1681775 := bstep (se 1 (by rfl) ⟨1261331, by rfl⟩ : syracuseStep 1681775 = 2522663) B2522663
theorem B2836903 : Blo 1680040 2836903 := bstep (se 1 (by rfl) ⟨2127677, by rfl⟩ : syracuseStep 2836903 = 4255355) B4255355
theorem B1681831 : Blo 1680040 1681831 := bstep (se 1 (by rfl) ⟨1261373, by rfl⟩ : syracuseStep 1681831 = 2522747) B2522747
theorem B1681915 : Blo 1680040 1681915 := bstep (se 1 (by rfl) ⟨1261436, by rfl⟩ : syracuseStep 1681915 = 2522873) B2522873
theorem B4786751 : Blo 1680040 4786751 := bstep (se 1 (by rfl) ⟨3590063, by rfl⟩ : syracuseStep 4786751 = 7180127) B7180127
theorem B1681983 : Blo 1680040 1681983 := bstep (se 1 (by rfl) ⟨1261487, by rfl⟩ : syracuseStep 1681983 = 2522975) B2522975
theorem B1681991 : Blo 1680040 1681991 := bstep (se 1 (by rfl) ⟨1261493, by rfl⟩ : syracuseStep 1681991 = 2522987) B2522987
theorem B2837065 : Blo 1680040 2837065 := bstep (se 2 (by rfl) ⟨1063899, by rfl⟩ : syracuseStep 2837065 = 2127799) B2127799
theorem B2837099 : Blo 1680040 2837099 := bstep (se 1 (by rfl) ⟨2127824, by rfl⟩ : syracuseStep 2837099 = 4255649) B4255649
theorem B2394731 : Blo 1680040 2394731 := bstep (se 1 (by rfl) ⟨1796048, by rfl⟩ : syracuseStep 2394731 = 3592097) B3592097
theorem B4254383 : Blo 1680040 4254383 := bstep (se 1 (by rfl) ⟨3190787, by rfl⟩ : syracuseStep 4254383 = 6381575) B6381575
theorem B5671835 : Blo 1680040 5671835 := bstep (se 1 (by rfl) ⟨4253876, by rfl⟩ : syracuseStep 5671835 = 8507753) B8507753
theorem B4254707 : Blo 1680040 4254707 := bstep (se 1 (by rfl) ⟨3191030, by rfl⟩ : syracuseStep 4254707 = 6382061) B6382061
theorem B12766247 : Blo 1680040 12766247 := bstep (se 1 (by rfl) ⟨9574685, by rfl⟩ : syracuseStep 12766247 = 19149371) B19149371
theorem B6819209 : Blo 1680040 6819209 := bstep (se 2 (by rfl) ⟨2557203, by rfl⟩ : syracuseStep 6819209 = 5114407) B5114407
theorem B15756731 : Blo 1680040 15756731 := bstep (se 1 (by rfl) ⟨11817548, by rfl⟩ : syracuseStep 15756731 = 23635097) B23635097
theorem B4255163 : Blo 1680040 4255163 := bstep (se 1 (by rfl) ⟨3191372, by rfl⟩ : syracuseStep 4255163 = 6382745) B6382745
theorem B12758471 : Blo 1680040 12758471 := bstep (se 1 (by rfl) ⟨9568853, by rfl⟩ : syracuseStep 12758471 = 19137707) B19137707
theorem B7179785 : Blo 1680040 7179785 := bstep (se 2 (by rfl) ⟨2692419, by rfl⟩ : syracuseStep 7179785 = 5384839) B5384839
theorem B3780179 : Blo 1680040 3780179 := bstep (se 1 (by rfl) ⟨2835134, by rfl⟩ : syracuseStep 3780179 = 5670269) B5670269
theorem B2272951 : Blo 1680040 2272951 := bstep (se 1 (by rfl) ⟨1704713, by rfl⟩ : syracuseStep 2272951 = 3409427) B3409427
theorem B3780359 : Blo 1680040 3780359 := bstep (se 1 (by rfl) ⟨2835269, by rfl⟩ : syracuseStep 3780359 = 5670539) B5670539
theorem B3190583 : Blo 1680040 3190583 := bstep (se 1 (by rfl) ⟨2392937, by rfl⟩ : syracuseStep 3190583 = 4785875) B4785875
theorem B5672861 : Blo 1680040 5672861 := bstep (se 3 (by rfl) ⟨1063661, by rfl⟩ : syracuseStep 5672861 = 2127323) B2127323
theorem B5672969 : Blo 1680040 5672969 := bstep (se 2 (by rfl) ⟨2127363, by rfl⟩ : syracuseStep 5672969 = 4254727) B4254727
theorem B9572681 : Blo 1680040 9572681 := bstep (se 2 (by rfl) ⟨3589755, by rfl⟩ : syracuseStep 9572681 = 7179511) B7179511
theorem B3780971 : Blo 1680040 3780971 := bstep (se 1 (by rfl) ⟨2835728, by rfl⟩ : syracuseStep 3780971 = 5671457) B5671457
theorem B3191251 : Blo 1680040 3191251 := bstep (se 1 (by rfl) ⟨2393438, by rfl⟩ : syracuseStep 3191251 = 4786877) B4786877
theorem B3781115 : Blo 1680040 3781115 := bstep (se 1 (by rfl) ⟨2835836, by rfl⟩ : syracuseStep 3781115 = 5671673) B5671673
theorem B2126407 : Blo 1680040 2126407 := bstep (se 1 (by rfl) ⟨1594805, by rfl⟩ : syracuseStep 2126407 = 3189611) B3189611
theorem B4256327 : Blo 1680040 4256327 := bstep (se 1 (by rfl) ⟨3192245, by rfl⟩ : syracuseStep 4256327 = 6384491) B6384491
theorem B4543049 : Blo 1680040 4543049 := bstep (se 2 (by rfl) ⟨1703643, by rfl⟩ : syracuseStep 4543049 = 3407287) B3407287
theorem B3781241 : Blo 1680040 3781241 := bstep (se 2 (by rfl) ⟨1417965, by rfl⟩ : syracuseStep 3781241 = 2835931) B2835931
theorem B3781295 : Blo 1680040 3781295 := bstep (se 1 (by rfl) ⟨2835971, by rfl⟩ : syracuseStep 3781295 = 5671943) B5671943
theorem B3191471 : Blo 1680040 3191471 := bstep (se 1 (by rfl) ⟨2393603, by rfl⟩ : syracuseStep 3191471 = 4787207) B4787207
theorem B2691767 : Blo 1680040 2691767 := bstep (se 1 (by rfl) ⟨2018825, by rfl⟩ : syracuseStep 2691767 = 4037651) B4037651
theorem B4543199 : Blo 1680040 4543199 := bstep (se 1 (by rfl) ⟨3407399, by rfl⟩ : syracuseStep 4543199 = 6814799) B6814799
theorem B3781367 : Blo 1680040 3781367 := bstep (se 1 (by rfl) ⟨2836025, by rfl⟩ : syracuseStep 3781367 = 5672051) B5672051
theorem B8508239 : Blo 1680040 8508239 := bstep (se 1 (by rfl) ⟨6381179, by rfl⟩ : syracuseStep 8508239 = 12762359) B12762359
theorem B3781547 : Blo 1680040 3781547 := bstep (se 1 (by rfl) ⟨2836160, by rfl⟩ : syracuseStep 3781547 = 5672321) B5672321
theorem B8508563 : Blo 1680040 8508563 := bstep (se 1 (by rfl) ⟨6381422, by rfl⟩ : syracuseStep 8508563 = 12762845) B12762845
theorem B18166999 : Blo 1680040 18166999 := bstep (se 1 (by rfl) ⟨13625249, by rfl⟩ : syracuseStep 18166999 = 27250499) B27250499
theorem B3192041 : Blo 1680040 3192041 := bstep (se 2 (by rfl) ⟨1197015, by rfl⟩ : syracuseStep 3192041 = 2394031) B2394031
theorem B7181561 : Blo 1680040 7181561 := bstep (se 2 (by rfl) ⟨2693085, by rfl⟩ : syracuseStep 7181561 = 5386171) B5386171
theorem B2520359 : Blo 1680040 2520359 := bstep (se 1 (by rfl) ⟨1890269, by rfl⟩ : syracuseStep 2520359 = 3780539) B3780539
theorem B12760415 : Blo 1680040 12760415 := bstep (se 1 (by rfl) ⟨9570311, by rfl⟩ : syracuseStep 12760415 = 19140623) B19140623
theorem B2520443 : Blo 1680040 2520443 := bstep (se 1 (by rfl) ⟨1890332, by rfl⟩ : syracuseStep 2520443 = 3780665) B3780665
theorem B6059387 : Blo 1680040 6059387 := bstep (se 1 (by rfl) ⟨4544540, by rfl⟩ : syracuseStep 6059387 = 9089081) B9089081
theorem B19142081 : Blo 1680040 19142081 := bstep (se 2 (by rfl) ⟨7178280, by rfl⟩ : syracuseStep 19142081 = 14356561) B14356561
theorem B3782087 : Blo 1680040 3782087 := bstep (se 1 (by rfl) ⟨2836565, by rfl⟩ : syracuseStep 3782087 = 5673131) B5673131
theorem B2520569 : Blo 1680040 2520569 := bstep (se 2 (by rfl) ⟨945213, by rfl⟩ : syracuseStep 2520569 = 1890427) B1890427
theorem B2520671 : Blo 1680040 2520671 := bstep (se 1 (by rfl) ⟨1890503, by rfl⟩ : syracuseStep 2520671 = 3781007) B3781007
theorem B6813371 : Blo 1680040 6813371 := bstep (se 1 (by rfl) ⟨5110028, by rfl⟩ : syracuseStep 6813371 = 10220057) B10220057
theorem B3782447 : Blo 1680040 3782447 := bstep (se 1 (by rfl) ⟨2836835, by rfl⟩ : syracuseStep 3782447 = 5673671) B5673671
theorem B2520887 : Blo 1680040 2520887 := bstep (se 1 (by rfl) ⟨1890665, by rfl⟩ : syracuseStep 2520887 = 3781331) B3781331
theorem B4257593 : Blo 1680040 4257593 := bstep (se 2 (by rfl) ⟨1596597, by rfl⟩ : syracuseStep 4257593 = 3193195) B3193195
theorem B2521193 : Blo 1680040 2521193 := bstep (se 2 (by rfl) ⟨945447, by rfl⟩ : syracuseStep 2521193 = 1890895) B1890895
theorem B6060167 : Blo 1680040 6060167 := bstep (se 1 (by rfl) ⟨4545125, by rfl⟩ : syracuseStep 6060167 = 9090251) B9090251
theorem B24246539 : Blo 1680040 24246539 := bstep (se 1 (by rfl) ⟨18184904, by rfl⟩ : syracuseStep 24246539 = 36369809) B36369809
theorem B3783023 : Blo 1680040 3783023 := bstep (se 1 (by rfl) ⟨2837267, by rfl⟩ : syracuseStep 3783023 = 5674535) B5674535
theorem B2521511 : Blo 1680040 2521511 := bstep (se 1 (by rfl) ⟨1891133, by rfl⟩ : syracuseStep 2521511 = 3782267) B3782267
theorem B2128295 : Blo 1680040 2128295 := bstep (se 1 (by rfl) ⟨1596221, by rfl⟩ : syracuseStep 2128295 = 3192443) B3192443
theorem B3783095 : Blo 1680040 3783095 := bstep (se 1 (by rfl) ⟨2837321, by rfl⟩ : syracuseStep 3783095 = 5674643) B5674643
theorem B2521595 : Blo 1680040 2521595 := bstep (se 1 (by rfl) ⟨1891196, by rfl⟩ : syracuseStep 2521595 = 3782393) B3782393
theorem B72718843 : Blo 1680040 72718843 := bstep (se 1 (by rfl) ⟨54539132, by rfl⟩ : syracuseStep 72718843 = 109078265) B109078265
theorem B2128447 : Blo 1680040 2128447 := bstep (se 1 (by rfl) ⟨1596335, by rfl⟩ : syracuseStep 2128447 = 3192671) B3192671
theorem B3783239 : Blo 1680040 3783239 := bstep (se 1 (by rfl) ⟨2837429, by rfl⟩ : syracuseStep 3783239 = 5674859) B5674859
theorem B3783275 : Blo 1680040 3783275 := bstep (se 1 (by rfl) ⟨2837456, by rfl⟩ : syracuseStep 3783275 = 5674913) B5674913
theorem B2521721 : Blo 1680040 2521721 := bstep (se 2 (by rfl) ⟨945645, by rfl⟩ : syracuseStep 2521721 = 1891291) B1891291
theorem B87374477 : Blo 1680040 87374477 := bstep (se 3 (by rfl) ⟨16382714, by rfl⟩ : syracuseStep 87374477 = 32765429) B32765429
theorem B2521775 : Blo 1680040 2521775 := bstep (se 1 (by rfl) ⟨1891331, by rfl⟩ : syracuseStep 2521775 = 3782663) B3782663
theorem B1891039 : Blo 1680040 1891039 := bstep (se 1 (by rfl) ⟨1418279, by rfl⟩ : syracuseStep 1891039 = 2836559) B2836559
theorem B2521823 : Blo 1680040 2521823 := bstep (se 1 (by rfl) ⟨1891367, by rfl⟩ : syracuseStep 2521823 = 3782735) B3782735
theorem B2128619 : Blo 1680040 2128619 := bstep (se 1 (by rfl) ⟨1596464, by rfl⟩ : syracuseStep 2128619 = 3192929) B3192929
theorem B2522087 : Blo 1680040 2522087 := bstep (se 1 (by rfl) ⟨1891565, by rfl⟩ : syracuseStep 2522087 = 3783131) B3783131
theorem B3783671 : Blo 1680040 3783671 := bstep (se 1 (by rfl) ⟨2837753, by rfl⟩ : syracuseStep 3783671 = 5675507) B5675507
theorem B7183475 : Blo 1680040 7183475 := bstep (se 1 (by rfl) ⟨5387606, by rfl⟩ : syracuseStep 7183475 = 10775213) B10775213
theorem B5676155 : Blo 1680040 5676155 := bstep (se 1 (by rfl) ⟨4257116, by rfl⟩ : syracuseStep 5676155 = 8514233) B8514233
theorem B32316569 : Blo 1680040 32316569 := bstep (se 2 (by rfl) ⟨12118713, by rfl⟩ : syracuseStep 32316569 = 24237427) B24237427
theorem B2522345 : Blo 1680040 2522345 := bstep (se 2 (by rfl) ⟨945879, by rfl⟩ : syracuseStep 2522345 = 1891759) B1891759
theorem B1891615 : Blo 1680040 1891615 := bstep (se 1 (by rfl) ⟨1418711, by rfl⟩ : syracuseStep 1891615 = 2837423) B2837423
theorem B2522399 : Blo 1680040 2522399 := bstep (se 1 (by rfl) ⟨1891799, by rfl⟩ : syracuseStep 2522399 = 3783599) B3783599
theorem B3784031 : Blo 1680040 3784031 := bstep (se 1 (by rfl) ⟨2838023, by rfl⟩ : syracuseStep 3784031 = 5676047) B5676047
theorem B5676425 : Blo 1680040 5676425 := bstep (se 2 (by rfl) ⟨2128659, by rfl⟩ : syracuseStep 5676425 = 4257319) B4257319
theorem B2522567 : Blo 1680040 2522567 := bstep (se 1 (by rfl) ⟨1891925, by rfl⟩ : syracuseStep 2522567 = 3783851) B3783851
theorem B25886213 : Blo 1680040 25886213 := bstep (se 4 (by rfl) ⟨2426832, by rfl⟩ : syracuseStep 25886213 = 4853665) B4853665
theorem B21536279 : Blo 1680040 21536279 := bstep (se 1 (by rfl) ⟨16152209, by rfl⟩ : syracuseStep 21536279 = 32304419) B32304419
theorem B16367129 : Blo 1680040 16367129 := bstep (se 2 (by rfl) ⟨6137673, by rfl⟩ : syracuseStep 16367129 = 12275347) B12275347
theorem B1891903 : Blo 1680040 1891903 := bstep (se 1 (by rfl) ⟨1418927, by rfl⟩ : syracuseStep 1891903 = 2837855) B2837855
theorem B3784427 : Blo 1680040 3784427 := bstep (se 1 (by rfl) ⟨2838320, by rfl⟩ : syracuseStep 3784427 = 5676641) B5676641
theorem B2522921 : Blo 1680040 2522921 := bstep (se 2 (by rfl) ⟨946095, by rfl⟩ : syracuseStep 2522921 = 1892191) B1892191
theorem B2522927 : Blo 1680040 2522927 := bstep (se 1 (by rfl) ⟨1892195, by rfl⟩ : syracuseStep 2522927 = 3784391) B3784391
theorem B5676857 : Blo 1680040 5676857 := bstep (se 2 (by rfl) ⟨2128821, by rfl⟩ : syracuseStep 5676857 = 4257643) B4257643
theorem B3784553 : Blo 1680040 3784553 := bstep (se 2 (by rfl) ⟨1419207, by rfl⟩ : syracuseStep 3784553 = 2838415) B2838415
theorem B5456011 : Blo 1680040 5456011 := bstep (se 1 (by rfl) ⟨4092008, by rfl⟩ : syracuseStep 5456011 = 8184017) B8184017
theorem B6381787 : Blo 1680040 6381787 := bstep (se 1 (by rfl) ⟨4786340, by rfl⟩ : syracuseStep 6381787 = 9572681) B9572681
theorem B4784359 : Blo 1680040 4784359 := bstep (se 1 (by rfl) ⟨3588269, by rfl⟩ : syracuseStep 4784359 = 7176539) B7176539
theorem B1794511 : Blo 1680040 1794511 := bstep (se 1 (by rfl) ⟨1345883, by rfl⟩ : syracuseStep 1794511 = 2691767) B2691767
theorem B9568763 : Blo 1680040 9568763 := bstep (se 1 (by rfl) ⟨7176572, by rfl⟩ : syracuseStep 9568763 = 14353145) B14353145
theorem B18416177 : Blo 1680040 18416177 := bstep (se 2 (by rfl) ⟨6906066, by rfl⟩ : syracuseStep 18416177 = 13812133) B13812133
theorem B5325547 : Blo 1680040 5325547 := bstep (se 1 (by rfl) ⟨3994160, by rfl⟩ : syracuseStep 5325547 = 7988321) B7988321
theorem B2835209 : Blo 1680040 2835209 := bstep (se 2 (by rfl) ⟨1063203, by rfl⟩ : syracuseStep 2835209 = 2126407) B2126407
theorem B1680239 : Blo 1680040 1680239 := bstep (se 1 (by rfl) ⟨1260179, by rfl⟩ : syracuseStep 1680239 = 2520359) B2520359
theorem B1680295 : Blo 1680040 1680295 := bstep (se 1 (by rfl) ⟨1260221, by rfl⟩ : syracuseStep 1680295 = 2520443) B2520443
theorem B4039591 : Blo 1680040 4039591 := bstep (se 1 (by rfl) ⟨3029693, by rfl⟩ : syracuseStep 4039591 = 6059387) B6059387
theorem B1680379 : Blo 1680040 1680379 := bstep (se 1 (by rfl) ⟨1260284, by rfl⟩ : syracuseStep 1680379 = 2520569) B2520569
theorem B1680447 : Blo 1680040 1680447 := bstep (se 1 (by rfl) ⟨1260335, by rfl⟩ : syracuseStep 1680447 = 2520671) B2520671
theorem B1680591 : Blo 1680040 1680591 := bstep (se 1 (by rfl) ⟨1260443, by rfl⟩ : syracuseStep 1680591 = 2520887) B2520887
theorem B2835803 : Blo 1680040 2835803 := bstep (se 1 (by rfl) ⟨2126852, by rfl⟩ : syracuseStep 2835803 = 4253705) B4253705
theorem B1680795 : Blo 1680040 1680795 := bstep (se 1 (by rfl) ⟨1260596, by rfl⟩ : syracuseStep 1680795 = 2521193) B2521193
theorem B4040111 : Blo 1680040 4040111 := bstep (se 1 (by rfl) ⟨3030083, by rfl⟩ : syracuseStep 4040111 = 6060167) B6060167
theorem B16164359 : Blo 1680040 16164359 := bstep (se 1 (by rfl) ⟨12123269, by rfl⟩ : syracuseStep 16164359 = 24246539) B24246539
theorem B2836039 : Blo 1680040 2836039 := bstep (se 1 (by rfl) ⟨2127029, by rfl⟩ : syracuseStep 2836039 = 4254059) B4254059
theorem B122685029 : Blo 1680040 122685029 := bstep (se 4 (by rfl) ⟨11501721, by rfl⟩ : syracuseStep 122685029 = 23003443) B23003443
theorem B1681007 : Blo 1680040 1681007 := bstep (se 1 (by rfl) ⟨1260755, by rfl⟩ : syracuseStep 1681007 = 2521511) B2521511
theorem B1681063 : Blo 1680040 1681063 := bstep (se 1 (by rfl) ⟨1260797, by rfl⟩ : syracuseStep 1681063 = 2521595) B2521595
theorem B1681147 : Blo 1680040 1681147 := bstep (se 1 (by rfl) ⟨1260860, by rfl⟩ : syracuseStep 1681147 = 2521721) B2521721
theorem B2836255 : Blo 1680040 2836255 := bstep (se 1 (by rfl) ⟨2127191, by rfl⟩ : syracuseStep 2836255 = 4254383) B4254383
theorem B1681183 : Blo 1680040 1681183 := bstep (se 1 (by rfl) ⟨1260887, by rfl⟩ : syracuseStep 1681183 = 2521775) B2521775
theorem B1681215 : Blo 1680040 1681215 := bstep (se 1 (by rfl) ⟨1260911, by rfl⟩ : syracuseStep 1681215 = 2521823) B2521823
theorem B1681391 : Blo 1680040 1681391 := bstep (se 1 (by rfl) ⟨1261043, by rfl⟩ : syracuseStep 1681391 = 2522087) B2522087
theorem B2836471 : Blo 1680040 2836471 := bstep (se 1 (by rfl) ⟨2127353, by rfl⟩ : syracuseStep 2836471 = 4254707) B4254707
theorem B1681563 : Blo 1680040 1681563 := bstep (se 1 (by rfl) ⟨1261172, by rfl⟩ : syracuseStep 1681563 = 2522345) B2522345
theorem B1681599 : Blo 1680040 1681599 := bstep (se 1 (by rfl) ⟨1261199, by rfl⟩ : syracuseStep 1681599 = 2522399) B2522399
theorem B6818041 : Blo 1680040 6818041 := bstep (se 2 (by rfl) ⟨2556765, by rfl⟩ : syracuseStep 6818041 = 5113531) B5113531
theorem B10504487 : Blo 1680040 10504487 := bstep (se 1 (by rfl) ⟨7878365, by rfl⟩ : syracuseStep 10504487 = 15756731) B15756731
theorem B2836775 : Blo 1680040 2836775 := bstep (se 1 (by rfl) ⟨2127581, by rfl⟩ : syracuseStep 2836775 = 4255163) B4255163
theorem B8505647 : Blo 1680040 8505647 := bstep (se 1 (by rfl) ⟨6379235, by rfl⟩ : syracuseStep 8505647 = 12758471) B12758471
theorem B1681711 : Blo 1680040 1681711 := bstep (se 1 (by rfl) ⟨1261283, by rfl⟩ : syracuseStep 1681711 = 2522567) B2522567
theorem B4786523 : Blo 1680040 4786523 := bstep (se 1 (by rfl) ⟨3589892, by rfl⟩ : syracuseStep 4786523 = 7179785) B7179785
theorem B1681947 : Blo 1680040 1681947 := bstep (se 1 (by rfl) ⟨1261460, by rfl⟩ : syracuseStep 1681947 = 2522921) B2522921
theorem B1681951 : Blo 1680040 1681951 := bstep (se 1 (by rfl) ⟨1261463, by rfl⟩ : syracuseStep 1681951 = 2522927) B2522927
theorem B11824015 : Blo 1680040 11824015 := bstep (se 1 (by rfl) ⟨8868011, by rfl⟩ : syracuseStep 11824015 = 17736023) B17736023
theorem B2837551 : Blo 1680040 2837551 := bstep (se 1 (by rfl) ⟨2128163, by rfl⟩ : syracuseStep 2837551 = 4256327) B4256327
theorem B5672159 : Blo 1680040 5672159 := bstep (se 1 (by rfl) ⟨4254119, by rfl⟩ : syracuseStep 5672159 = 8508239) B8508239
theorem B4255001 : Blo 1680040 4255001 := bstep (se 2 (by rfl) ⟨1595625, by rfl⟩ : syracuseStep 4255001 = 3191251) B3191251
theorem B2837929 : Blo 1680040 2837929 := bstep (se 2 (by rfl) ⟨1064223, by rfl⟩ : syracuseStep 2837929 = 2128447) B2128447
theorem B5672375 : Blo 1680040 5672375 := bstep (se 1 (by rfl) ⟨4254281, by rfl⟩ : syracuseStep 5672375 = 8508563) B8508563
theorem B8506943 : Blo 1680040 8506943 := bstep (se 1 (by rfl) ⟨6380207, by rfl⟩ : syracuseStep 8506943 = 12760415) B12760415
theorem B10219283 : Blo 1680040 10219283 := bstep (se 1 (by rfl) ⟨7664462, by rfl⟩ : syracuseStep 10219283 = 15328925) B15328925
theorem B4542247 : Blo 1680040 4542247 := bstep (se 1 (by rfl) ⟨3406685, by rfl⟩ : syracuseStep 4542247 = 6813371) B6813371
theorem B2838395 : Blo 1680040 2838395 := bstep (se 1 (by rfl) ⟨2128796, by rfl⟩ : syracuseStep 2838395 = 4257593) B4257593
theorem B12758957 : Blo 1680040 12758957 := bstep (se 3 (by rfl) ⟨2392304, by rfl⟩ : syracuseStep 12758957 = 4784609) B4784609
theorem B3780575 : Blo 1680040 3780575 := bstep (se 1 (by rfl) ⟨2835431, by rfl⟩ : syracuseStep 3780575 = 5670863) B5670863
theorem B6385949 : Blo 1680040 6385949 := bstep (se 3 (by rfl) ⟨1197365, by rfl⟩ : syracuseStep 6385949 = 2394731) B2394731
theorem B18665765 : Blo 1680040 18665765 := bstep (se 4 (by rfl) ⟨1749915, by rfl⟩ : syracuseStep 18665765 = 3499831) B3499831
theorem B3191167 : Blo 1680040 3191167 := bstep (se 1 (by rfl) ⟨2393375, by rfl⟩ : syracuseStep 3191167 = 4786751) B4786751
theorem B58249651 : Blo 1680040 58249651 := bstep (se 1 (by rfl) ⟨43687238, by rfl⟩ : syracuseStep 58249651 = 87374477) B87374477
theorem B3781223 : Blo 1680040 3781223 := bstep (se 1 (by rfl) ⟨2835917, by rfl⟩ : syracuseStep 3781223 = 5671835) B5671835
theorem B4788983 : Blo 1680040 4788983 := bstep (se 1 (by rfl) ⟨3591737, by rfl⟩ : syracuseStep 4788983 = 7183475) B7183475
theorem B17257475 : Blo 1680040 17257475 := bstep (se 1 (by rfl) ⟨12943106, by rfl⟩ : syracuseStep 17257475 = 25886213) B25886213
theorem B14357519 : Blo 1680040 14357519 := bstep (se 1 (by rfl) ⟨10768139, by rfl⟩ : syracuseStep 14357519 = 21536279) B21536279
theorem B2520119 : Blo 1680040 2520119 := bstep (se 1 (by rfl) ⟨1890089, by rfl⟩ : syracuseStep 2520119 = 3780179) B3780179
theorem B3191881 : Blo 1680040 3191881 := bstep (se 2 (by rfl) ⟨1196955, by rfl⟩ : syracuseStep 3191881 = 2393911) B2393911
theorem B24228953 : Blo 1680040 24228953 := bstep (se 2 (by rfl) ⟨9085857, by rfl⟩ : syracuseStep 24228953 = 18171715) B18171715
theorem B2520239 : Blo 1680040 2520239 := bstep (se 1 (by rfl) ⟨1890179, by rfl⟩ : syracuseStep 2520239 = 3780359) B3780359
theorem B2127055 : Blo 1680040 2127055 := bstep (se 1 (by rfl) ⟨1595291, by rfl⟩ : syracuseStep 2127055 = 3190583) B3190583
theorem B3781907 : Blo 1680040 3781907 := bstep (se 1 (by rfl) ⟨2836430, by rfl⟩ : syracuseStep 3781907 = 5672861) B5672861
theorem B3781979 : Blo 1680040 3781979 := bstep (se 1 (by rfl) ⟨2836484, by rfl⟩ : syracuseStep 3781979 = 5672969) B5672969
theorem B8623547 : Blo 1680040 8623547 := bstep (se 1 (by rfl) ⟨6467660, by rfl⟩ : syracuseStep 8623547 = 12935321) B12935321
theorem B5674427 : Blo 1680040 5674427 := bstep (se 1 (by rfl) ⟨4255820, by rfl⟩ : syracuseStep 5674427 = 8511641) B8511641
theorem B2520647 : Blo 1680040 2520647 := bstep (se 1 (by rfl) ⟨1890485, by rfl⟩ : syracuseStep 2520647 = 3780971) B3780971
theorem B2520743 : Blo 1680040 2520743 := bstep (se 1 (by rfl) ⟨1890557, by rfl⟩ : syracuseStep 2520743 = 3781115) B3781115
theorem B3028699 : Blo 1680040 3028699 := bstep (se 1 (by rfl) ⟨2271524, by rfl⟩ : syracuseStep 3028699 = 4543049) B4543049
theorem B2520827 : Blo 1680040 2520827 := bstep (se 1 (by rfl) ⟨1890620, by rfl⟩ : syracuseStep 2520827 = 3781241) B3781241
theorem B2520863 : Blo 1680040 2520863 := bstep (se 1 (by rfl) ⟨1890647, by rfl⟩ : syracuseStep 2520863 = 3781295) B3781295
theorem B2127647 : Blo 1680040 2127647 := bstep (se 1 (by rfl) ⟨1595735, by rfl⟩ : syracuseStep 2127647 = 3191471) B3191471
theorem B3028799 : Blo 1680040 3028799 := bstep (se 1 (by rfl) ⟨2271599, by rfl⟩ : syracuseStep 3028799 = 4543199) B4543199
theorem B2520911 : Blo 1680040 2520911 := bstep (se 1 (by rfl) ⟨1890683, by rfl⟩ : syracuseStep 2520911 = 3781367) B3781367
theorem B3782537 : Blo 1680040 3782537 := bstep (se 2 (by rfl) ⟨1418451, by rfl⟩ : syracuseStep 3782537 = 2836903) B2836903
theorem B46028695 : Blo 1680040 46028695 := bstep (se 1 (by rfl) ⟨34521521, by rfl⟩ : syracuseStep 46028695 = 69043043) B69043043
theorem B1890247 : Blo 1680040 1890247 := bstep (se 1 (by rfl) ⟨1417685, by rfl⟩ : syracuseStep 1890247 = 2835371) B2835371
theorem B2521031 : Blo 1680040 2521031 := bstep (se 1 (by rfl) ⟨1890773, by rfl⟩ : syracuseStep 2521031 = 3781547) B3781547
theorem B5674967 : Blo 1680040 5674967 := bstep (se 1 (by rfl) ⟨4256225, by rfl⟩ : syracuseStep 5674967 = 8512451) B8512451
theorem B19150829 : Blo 1680040 19150829 := bstep (se 3 (by rfl) ⟨3590780, by rfl⟩ : syracuseStep 19150829 = 7181561) B7181561
theorem B96958457 : Blo 1680040 96958457 := bstep (se 2 (by rfl) ⟨36359421, by rfl⟩ : syracuseStep 96958457 = 72718843) B72718843
theorem B8509535 : Blo 1680040 8509535 := bstep (se 1 (by rfl) ⟨6382151, by rfl⟩ : syracuseStep 8509535 = 12764303) B12764303
theorem B3782753 : Blo 1680040 3782753 := bstep (se 2 (by rfl) ⟨1418532, by rfl⟩ : syracuseStep 3782753 = 2837065) B2837065
theorem B12277889 : Blo 1680040 12277889 := bstep (se 2 (by rfl) ⟨4604208, by rfl⟩ : syracuseStep 12277889 = 9208417) B9208417
theorem B2128027 : Blo 1680040 2128027 := bstep (se 1 (by rfl) ⟨1596020, by rfl⟩ : syracuseStep 2128027 = 3192041) B3192041
theorem B9574595 : Blo 1680040 9574595 := bstep (se 1 (by rfl) ⟨7180946, by rfl⟩ : syracuseStep 9574595 = 14361893) B14361893
theorem B6559987 : Blo 1680040 6559987 := bstep (se 1 (by rfl) ⟨4919990, by rfl⟩ : syracuseStep 6559987 = 9839981) B9839981
theorem B12122405 : Blo 1680040 12122405 := bstep (se 4 (by rfl) ⟨1136475, by rfl⟩ : syracuseStep 12122405 = 2272951) B2272951
theorem B2521385 : Blo 1680040 2521385 := bstep (se 2 (by rfl) ⟨945519, by rfl⟩ : syracuseStep 2521385 = 1891039) B1891039
theorem B12761387 : Blo 1680040 12761387 := bstep (se 1 (by rfl) ⟨9571040, by rfl⟩ : syracuseStep 12761387 = 19142081) B19142081
theorem B1890607 : Blo 1680040 1890607 := bstep (se 1 (by rfl) ⟨1417955, by rfl⟩ : syracuseStep 1890607 = 2835911) B2835911
theorem B2521391 : Blo 1680040 2521391 := bstep (se 1 (by rfl) ⟨1891043, by rfl⟩ : syracuseStep 2521391 = 3782087) B3782087
theorem B5675453 : Blo 1680040 5675453 := bstep (se 3 (by rfl) ⟨1064147, by rfl⟩ : syracuseStep 5675453 = 2128295) B2128295
theorem B10770907 : Blo 1680040 10770907 := bstep (se 1 (by rfl) ⟨8078180, by rfl⟩ : syracuseStep 10770907 = 16156361) B16156361
theorem B2521631 : Blo 1680040 2521631 := bstep (se 1 (by rfl) ⟨1891223, by rfl⟩ : syracuseStep 2521631 = 3782447) B3782447
theorem B2693663 : Blo 1680040 2693663 := bstep (se 1 (by rfl) ⟨2020247, by rfl⟩ : syracuseStep 2693663 = 4040495) B4040495
theorem B20454227 : Blo 1680040 20454227 := bstep (se 1 (by rfl) ⟨15340670, by rfl⟩ : syracuseStep 20454227 = 30681341) B30681341
theorem B7183187 : Blo 1680040 7183187 := bstep (se 1 (by rfl) ⟨5387390, by rfl⟩ : syracuseStep 7183187 = 10774781) B10774781
theorem B179460983 : Blo 1680040 179460983 := bstep (se 1 (by rfl) ⟨134595737, by rfl⟩ : syracuseStep 179460983 = 269191475) B269191475
theorem B2522015 : Blo 1680040 2522015 := bstep (se 1 (by rfl) ⟨1891511, by rfl⟩ : syracuseStep 2522015 = 3783023) B3783023
theorem B24222665 : Blo 1680040 24222665 := bstep (se 2 (by rfl) ⟨9083499, by rfl⟩ : syracuseStep 24222665 = 18166999) B18166999
theorem B2522063 : Blo 1680040 2522063 := bstep (se 1 (by rfl) ⟨1891547, by rfl⟩ : syracuseStep 2522063 = 3783095) B3783095
theorem B2522153 : Blo 1680040 2522153 := bstep (se 2 (by rfl) ⟨945807, by rfl⟩ : syracuseStep 2522153 = 1891615) B1891615
theorem B4545577 : Blo 1680040 4545577 := bstep (se 2 (by rfl) ⟨1704591, by rfl⟩ : syracuseStep 4545577 = 3409183) B3409183
theorem B2522159 : Blo 1680040 2522159 := bstep (se 1 (by rfl) ⟨1891619, by rfl⟩ : syracuseStep 2522159 = 3783239) B3783239
theorem B13818937 : Blo 1680040 13818937 := bstep (se 2 (by rfl) ⟨5182101, by rfl⟩ : syracuseStep 13818937 = 10364203) B10364203
theorem B1891399 : Blo 1680040 1891399 := bstep (se 1 (by rfl) ⟨1418549, by rfl⟩ : syracuseStep 1891399 = 2837099) B2837099
theorem B2522183 : Blo 1680040 2522183 := bstep (se 1 (by rfl) ⟨1891637, by rfl⟩ : syracuseStep 2522183 = 3783275) B3783275
theorem B12934397 : Blo 1680040 12934397 := bstep (se 3 (by rfl) ⟨2425199, by rfl⟩ : syracuseStep 12934397 = 4850399) B4850399
theorem B5676317 : Blo 1680040 5676317 := bstep (se 3 (by rfl) ⟨1064309, by rfl⟩ : syracuseStep 5676317 = 2128619) B2128619
theorem B2522447 : Blo 1680040 2522447 := bstep (se 1 (by rfl) ⟨1891835, by rfl⟩ : syracuseStep 2522447 = 3783671) B3783671
theorem B8510831 : Blo 1680040 8510831 := bstep (se 1 (by rfl) ⟨6383123, by rfl⟩ : syracuseStep 8510831 = 12766247) B12766247
theorem B3784103 : Blo 1680040 3784103 := bstep (se 1 (by rfl) ⟨2838077, by rfl⟩ : syracuseStep 3784103 = 5676155) B5676155
theorem B2522537 : Blo 1680040 2522537 := bstep (se 2 (by rfl) ⟨945951, by rfl⟩ : syracuseStep 2522537 = 1891903) B1891903
theorem B21544379 : Blo 1680040 21544379 := bstep (se 1 (by rfl) ⟨16158284, by rfl⟩ : syracuseStep 21544379 = 32316569) B32316569
theorem B2522687 : Blo 1680040 2522687 := bstep (se 1 (by rfl) ⟨1892015, by rfl⟩ : syracuseStep 2522687 = 3784031) B3784031
theorem B4546139 : Blo 1680040 4546139 := bstep (se 1 (by rfl) ⟨3409604, by rfl⟩ : syracuseStep 4546139 = 6819209) B6819209
theorem B3784283 : Blo 1680040 3784283 := bstep (se 1 (by rfl) ⟨2838212, by rfl⟩ : syracuseStep 3784283 = 5676425) B5676425
theorem B10911419 : Blo 1680040 10911419 := bstep (se 1 (by rfl) ⟨8183564, by rfl⟩ : syracuseStep 10911419 = 16367129) B16367129
theorem B40877885 : Blo 1680040 40877885 := bstep (se 3 (by rfl) ⟨7664603, by rfl⟩ : syracuseStep 40877885 = 15329207) B15329207
theorem B2522951 : Blo 1680040 2522951 := bstep (se 1 (by rfl) ⟨1892213, by rfl⟩ : syracuseStep 2522951 = 3784427) B3784427
theorem B3784571 : Blo 1680040 3784571 := bstep (se 1 (by rfl) ⟨2838428, by rfl⟩ : syracuseStep 3784571 = 5676857) B5676857
theorem B2523035 : Blo 1680040 2523035 := bstep (se 1 (by rfl) ⟨1892276, by rfl⟩ : syracuseStep 2523035 = 3784553) B3784553
theorem B7274681 : Blo 1680040 7274681 := bstep (se 2 (by rfl) ⟨2728005, by rfl⟩ : syracuseStep 7274681 = 5456011) B5456011
theorem B12443843 : Blo 1680040 12443843 := bstep (se 1 (by rfl) ⟨9332882, by rfl⟩ : syracuseStep 12443843 = 18665765) B18665765
theorem B2392681 : Blo 1680040 2392681 := bstep (se 2 (by rfl) ⟨897255, by rfl⟩ : syracuseStep 2392681 = 1794511) B1794511
theorem B14361209 : Blo 1680040 14361209 := bstep (se 2 (by rfl) ⟨5385453, by rfl⟩ : syracuseStep 14361209 = 10770907) B10770907
theorem B1680079 : Blo 1680040 1680079 := bstep (se 1 (by rfl) ⟨1260059, by rfl⟩ : syracuseStep 1680079 = 2520119) B2520119
theorem B1680159 : Blo 1680040 1680159 := bstep (se 1 (by rfl) ⟨1260119, by rfl⟩ : syracuseStep 1680159 = 2520239) B2520239
theorem B1680431 : Blo 1680040 1680431 := bstep (se 1 (by rfl) ⟨1260323, by rfl⟩ : syracuseStep 1680431 = 2520647) B2520647
theorem B81790019 : Blo 1680040 81790019 := bstep (se 1 (by rfl) ⟨61342514, by rfl⟩ : syracuseStep 81790019 = 122685029) B122685029
theorem B1680495 : Blo 1680040 1680495 := bstep (se 1 (by rfl) ⟨1260371, by rfl⟩ : syracuseStep 1680495 = 2520743) B2520743
theorem B1680551 : Blo 1680040 1680551 := bstep (se 1 (by rfl) ⟨1260413, by rfl⟩ : syracuseStep 1680551 = 2520827) B2520827
theorem B1680575 : Blo 1680040 1680575 := bstep (se 1 (by rfl) ⟨1260431, by rfl⟩ : syracuseStep 1680575 = 2520863) B2520863
theorem B1680607 : Blo 1680040 1680607 := bstep (se 1 (by rfl) ⟨1260455, by rfl⟩ : syracuseStep 1680607 = 2520911) B2520911
theorem B1680687 : Blo 1680040 1680687 := bstep (se 1 (by rfl) ⟨1260515, by rfl⟩ : syracuseStep 1680687 = 2521031) B2521031
theorem B18425249 : Blo 1680040 18425249 := bstep (se 2 (by rfl) ⟨6909468, by rfl⟩ : syracuseStep 18425249 = 13818937) B13818937
theorem B8185259 : Blo 1680040 8185259 := bstep (se 1 (by rfl) ⟨6138944, by rfl⟩ : syracuseStep 8185259 = 12277889) B12277889
theorem B6383063 : Blo 1680040 6383063 := bstep (se 1 (by rfl) ⟨4787297, by rfl⟩ : syracuseStep 6383063 = 9574595) B9574595
theorem B1680923 : Blo 1680040 1680923 := bstep (se 1 (by rfl) ⟨1260692, by rfl⟩ : syracuseStep 1680923 = 2521385) B2521385
theorem B5670431 : Blo 1680040 5670431 := bstep (se 1 (by rfl) ⟨4252823, by rfl⟩ : syracuseStep 5670431 = 8505647) B8505647
theorem B1680927 : Blo 1680040 1680927 := bstep (se 1 (by rfl) ⟨1260695, by rfl⟩ : syracuseStep 1680927 = 2521391) B2521391
theorem B24225317 : Blo 1680040 24225317 := bstep (se 4 (by rfl) ⟨2271123, by rfl⟩ : syracuseStep 24225317 = 4542247) B4542247
theorem B2836073 : Blo 1680040 2836073 := bstep (se 2 (by rfl) ⟨1063527, by rfl⟩ : syracuseStep 2836073 = 2127055) B2127055
theorem B1681087 : Blo 1680040 1681087 := bstep (se 1 (by rfl) ⟨1260815, by rfl⟩ : syracuseStep 1681087 = 2521631) B2521631
theorem B1795775 : Blo 1680040 1795775 := bstep (se 1 (by rfl) ⟨1346831, by rfl⟩ : syracuseStep 1795775 = 2693663) B2693663
theorem B1681343 : Blo 1680040 1681343 := bstep (se 1 (by rfl) ⟨1261007, by rfl⟩ : syracuseStep 1681343 = 2522015) B2522015
theorem B16148443 : Blo 1680040 16148443 := bstep (se 1 (by rfl) ⟨12111332, by rfl⟩ : syracuseStep 16148443 = 24222665) B24222665
theorem B1681375 : Blo 1680040 1681375 := bstep (se 1 (by rfl) ⟨1261031, by rfl⟩ : syracuseStep 1681375 = 2522063) B2522063
theorem B1681435 : Blo 1680040 1681435 := bstep (se 1 (by rfl) ⟨1261076, by rfl⟩ : syracuseStep 1681435 = 2522153) B2522153
theorem B1681439 : Blo 1680040 1681439 := bstep (se 1 (by rfl) ⟨1261079, by rfl⟩ : syracuseStep 1681439 = 2522159) B2522159
theorem B1681455 : Blo 1680040 1681455 := bstep (se 1 (by rfl) ⟨1261091, by rfl⟩ : syracuseStep 1681455 = 2522183) B2522183
theorem B2836667 : Blo 1680040 2836667 := bstep (se 1 (by rfl) ⟨2127500, by rfl⟩ : syracuseStep 2836667 = 4255001) B4255001
theorem B1681631 : Blo 1680040 1681631 := bstep (se 1 (by rfl) ⟨1261223, by rfl⟩ : syracuseStep 1681631 = 2522447) B2522447
theorem B1681691 : Blo 1680040 1681691 := bstep (se 1 (by rfl) ⟨1261268, by rfl⟩ : syracuseStep 1681691 = 2522537) B2522537
theorem B14362919 : Blo 1680040 14362919 := bstep (se 1 (by rfl) ⟨10772189, by rfl⟩ : syracuseStep 14362919 = 21544379) B21544379
theorem B5671295 : Blo 1680040 5671295 := bstep (se 1 (by rfl) ⟨4253471, by rfl⟩ : syracuseStep 5671295 = 8506943) B8506943
theorem B1681791 : Blo 1680040 1681791 := bstep (se 1 (by rfl) ⟨1261343, by rfl⟩ : syracuseStep 1681791 = 2522687) B2522687
theorem B1681967 : Blo 1680040 1681967 := bstep (se 1 (by rfl) ⟨1261475, by rfl⟩ : syracuseStep 1681967 = 2522951) B2522951
theorem B1682023 : Blo 1680040 1682023 := bstep (se 1 (by rfl) ⟨1261517, by rfl⟩ : syracuseStep 1682023 = 2523035) B2523035
theorem B8505971 : Blo 1680040 8505971 := bstep (se 1 (by rfl) ⟨6379478, by rfl⟩ : syracuseStep 8505971 = 12758957) B12758957
theorem B2837369 : Blo 1680040 2837369 := bstep (se 2 (by rfl) ⟨1064013, by rfl⟩ : syracuseStep 2837369 = 2128027) B2128027
theorem B24243077 : Blo 1680040 24243077 := bstep (se 4 (by rfl) ⟨2272788, by rfl⟩ : syracuseStep 24243077 = 4545577) B4545577
theorem B4254889 : Blo 1680040 4254889 := bstep (se 2 (by rfl) ⟨1595583, by rfl⟩ : syracuseStep 4254889 = 3191167) B3191167
theorem B9571679 : Blo 1680040 9571679 := bstep (se 1 (by rfl) ⟨7178759, by rfl⟩ : syracuseStep 9571679 = 14357519) B14357519
theorem B10776239 : Blo 1680040 10776239 := bstep (se 1 (by rfl) ⟨8082179, by rfl⟩ : syracuseStep 10776239 = 16164359) B16164359
theorem B15765353 : Blo 1680040 15765353 := bstep (se 2 (by rfl) ⟨5912007, by rfl⟩ : syracuseStep 15765353 = 11824015) B11824015
theorem B5386121 : Blo 1680040 5386121 := bstep (se 2 (by rfl) ⟨2019795, by rfl⟩ : syracuseStep 5386121 = 4039591) B4039591
theorem B12767219 : Blo 1680040 12767219 := bstep (se 1 (by rfl) ⟨9575414, by rfl⟩ : syracuseStep 12767219 = 19150829) B19150829
theorem B64638971 : Blo 1680040 64638971 := bstep (se 1 (by rfl) ⟨48479228, by rfl⟩ : syracuseStep 64638971 = 96958457) B96958457
theorem B5673023 : Blo 1680040 5673023 := bstep (se 1 (by rfl) ⟨4254767, by rfl⟩ : syracuseStep 5673023 = 8509535) B8509535
theorem B4255841 : Blo 1680040 4255841 := bstep (se 2 (by rfl) ⟨1595940, by rfl⟩ : syracuseStep 4255841 = 3191881) B3191881
theorem B8081603 : Blo 1680040 8081603 := bstep (se 1 (by rfl) ⟨6061202, by rfl⟩ : syracuseStep 8081603 = 12122405) B12122405
theorem B8507591 : Blo 1680040 8507591 := bstep (se 1 (by rfl) ⟨6380693, by rfl⟩ : syracuseStep 8507591 = 12761387) B12761387
theorem B3191015 : Blo 1680040 3191015 := bstep (se 1 (by rfl) ⟨2393261, by rfl⟩ : syracuseStep 3191015 = 4786523) B4786523
theorem B13636151 : Blo 1680040 13636151 := bstep (se 1 (by rfl) ⟨10227113, by rfl⟩ : syracuseStep 13636151 = 20454227) B20454227
theorem B4788791 : Blo 1680040 4788791 := bstep (se 1 (by rfl) ⟨3591593, by rfl⟩ : syracuseStep 4788791 = 7183187) B7183187
theorem B119640655 : Blo 1680040 119640655 := bstep (se 1 (by rfl) ⟨89730491, by rfl⟩ : syracuseStep 119640655 = 179460983) B179460983
theorem B5673725 : Blo 1680040 5673725 := bstep (se 3 (by rfl) ⟨1063823, by rfl⟩ : syracuseStep 5673725 = 2127647) B2127647
theorem B3781385 : Blo 1680040 3781385 := bstep (se 2 (by rfl) ⟨1418019, by rfl⟩ : syracuseStep 3781385 = 2836039) B2836039
theorem B3781439 : Blo 1680040 3781439 := bstep (se 1 (by rfl) ⟨2836079, by rfl⟩ : syracuseStep 3781439 = 5672159) B5672159
theorem B8622931 : Blo 1680040 8622931 := bstep (se 1 (by rfl) ⟨6467198, by rfl⟩ : syracuseStep 8622931 = 12934397) B12934397
theorem B5673887 : Blo 1680040 5673887 := bstep (se 1 (by rfl) ⟨4255415, by rfl⟩ : syracuseStep 5673887 = 8510831) B8510831
theorem B3781583 : Blo 1680040 3781583 := bstep (se 1 (by rfl) ⟨2836187, by rfl⟩ : syracuseStep 3781583 = 5672375) B5672375
theorem B3781673 : Blo 1680040 3781673 := bstep (se 2 (by rfl) ⟨1418127, by rfl⟩ : syracuseStep 3781673 = 2836255) B2836255
theorem B6812855 : Blo 1680040 6812855 := bstep (se 1 (by rfl) ⟨5109641, by rfl⟩ : syracuseStep 6812855 = 10219283) B10219283
theorem B61371593 : Blo 1680040 61371593 := bstep (se 2 (by rfl) ⟨23014347, by rfl⟩ : syracuseStep 61371593 = 46028695) B46028695
theorem B27251923 : Blo 1680040 27251923 := bstep (se 1 (by rfl) ⟨20438942, by rfl⟩ : syracuseStep 27251923 = 40877885) B40877885
theorem B2520329 : Blo 1680040 2520329 := bstep (se 2 (by rfl) ⟨945123, by rfl⟩ : syracuseStep 2520329 = 1890247) B1890247
theorem B2520383 : Blo 1680040 2520383 := bstep (se 1 (by rfl) ⟨1890287, by rfl⟩ : syracuseStep 2520383 = 3780575) B3780575
theorem B3781961 : Blo 1680040 3781961 := bstep (se 2 (by rfl) ⟨1418235, by rfl⟩ : syracuseStep 3781961 = 2836471) B2836471
theorem B46019933 : Blo 1680040 46019933 := bstep (se 3 (by rfl) ⟨8628737, by rfl⟩ : syracuseStep 46019933 = 17257475) B17257475
theorem B4257299 : Blo 1680040 4257299 := bstep (se 1 (by rfl) ⟨3192974, by rfl⟩ : syracuseStep 4257299 = 6385949) B6385949
theorem B8509049 : Blo 1680040 8509049 := bstep (se 2 (by rfl) ⟨3190893, by rfl⟩ : syracuseStep 8509049 = 6381787) B6381787
theorem B6379145 : Blo 1680040 6379145 := bstep (se 2 (by rfl) ⟨2392179, by rfl⟩ : syracuseStep 6379145 = 4784359) B4784359
theorem B8746649 : Blo 1680040 8746649 := bstep (se 2 (by rfl) ⟨3279993, by rfl⟩ : syracuseStep 8746649 = 6559987) B6559987
theorem B9090721 : Blo 1680040 9090721 := bstep (se 2 (by rfl) ⟨3409020, by rfl⟩ : syracuseStep 9090721 = 6818041) B6818041
theorem B6379175 : Blo 1680040 6379175 := bstep (se 1 (by rfl) ⟨4784381, by rfl⟩ : syracuseStep 6379175 = 9568763) B9568763
theorem B12277451 : Blo 1680040 12277451 := bstep (se 1 (by rfl) ⟨9208088, by rfl⟩ : syracuseStep 12277451 = 18416177) B18416177
theorem B2520809 : Blo 1680040 2520809 := bstep (se 2 (by rfl) ⟨945303, by rfl⟩ : syracuseStep 2520809 = 1890607) B1890607
theorem B2520815 : Blo 1680040 2520815 := bstep (se 1 (by rfl) ⟨1890611, by rfl⟩ : syracuseStep 2520815 = 3781223) B3781223
theorem B1890139 : Blo 1680040 1890139 := bstep (se 1 (by rfl) ⟨1417604, by rfl⟩ : syracuseStep 1890139 = 2835209) B2835209
theorem B77666201 : Blo 1680040 77666201 := bstep (se 2 (by rfl) ⟨29124825, by rfl⟩ : syracuseStep 77666201 = 58249651) B58249651
theorem B16152635 : Blo 1680040 16152635 := bstep (se 1 (by rfl) ⟨12114476, by rfl⟩ : syracuseStep 16152635 = 24228953) B24228953
theorem B2521271 : Blo 1680040 2521271 := bstep (se 1 (by rfl) ⟨1890953, by rfl⟩ : syracuseStep 2521271 = 3781907) B3781907
theorem B1890535 : Blo 1680040 1890535 := bstep (se 1 (by rfl) ⟨1417901, by rfl⟩ : syracuseStep 1890535 = 2835803) B2835803
theorem B2521319 : Blo 1680040 2521319 := bstep (se 1 (by rfl) ⟨1890989, by rfl⟩ : syracuseStep 2521319 = 3781979) B3781979
theorem B2693407 : Blo 1680040 2693407 := bstep (se 1 (by rfl) ⟨2020055, by rfl⟩ : syracuseStep 2693407 = 4040111) B4040111
theorem B5749031 : Blo 1680040 5749031 := bstep (se 1 (by rfl) ⟨4311773, by rfl⟩ : syracuseStep 5749031 = 8623547) B8623547
theorem B3782951 : Blo 1680040 3782951 := bstep (se 1 (by rfl) ⟨2837213, by rfl⟩ : syracuseStep 3782951 = 5674427) B5674427
theorem B7100729 : Blo 1680040 7100729 := bstep (se 2 (by rfl) ⟨2662773, by rfl⟩ : syracuseStep 7100729 = 5325547) B5325547
theorem B2521691 : Blo 1680040 2521691 := bstep (se 1 (by rfl) ⟨1891268, by rfl⟩ : syracuseStep 2521691 = 3782537) B3782537
theorem B3783311 : Blo 1680040 3783311 := bstep (se 1 (by rfl) ⟨2837483, by rfl⟩ : syracuseStep 3783311 = 5674967) B5674967
theorem B3783401 : Blo 1680040 3783401 := bstep (se 2 (by rfl) ⟨1418775, by rfl⟩ : syracuseStep 3783401 = 2837551) B2837551
theorem B2521835 : Blo 1680040 2521835 := bstep (se 1 (by rfl) ⟨1891376, by rfl⟩ : syracuseStep 2521835 = 3782753) B3782753
theorem B2521865 : Blo 1680040 2521865 := bstep (se 2 (by rfl) ⟨945699, by rfl⟩ : syracuseStep 2521865 = 1891399) B1891399
theorem B7002991 : Blo 1680040 7002991 := bstep (se 1 (by rfl) ⟨5252243, by rfl⟩ : syracuseStep 7002991 = 10504487) B10504487
theorem B1891183 : Blo 1680040 1891183 := bstep (se 1 (by rfl) ⟨1418387, by rfl⟩ : syracuseStep 1891183 = 2836775) B2836775
theorem B12123037 : Blo 1680040 12123037 := bstep (se 3 (by rfl) ⟨2273069, by rfl⟩ : syracuseStep 12123037 = 4546139) B4546139
theorem B3783635 : Blo 1680040 3783635 := bstep (se 1 (by rfl) ⟨2837726, by rfl⟩ : syracuseStep 3783635 = 5675453) B5675453
theorem B3783905 : Blo 1680040 3783905 := bstep (se 2 (by rfl) ⟨1418964, by rfl⟩ : syracuseStep 3783905 = 2837929) B2837929
theorem B12770621 : Blo 1680040 12770621 := bstep (se 3 (by rfl) ⟨2394491, by rfl⟩ : syracuseStep 12770621 = 4788983) B4788983
theorem B8076797 : Blo 1680040 8076797 := bstep (se 3 (by rfl) ⟨1514399, by rfl⟩ : syracuseStep 8076797 = 3028799) B3028799
theorem B3784211 : Blo 1680040 3784211 := bstep (se 1 (by rfl) ⟨2838158, by rfl⟩ : syracuseStep 3784211 = 5676317) B5676317
theorem B2522735 : Blo 1680040 2522735 := bstep (se 1 (by rfl) ⟨1892051, by rfl⟩ : syracuseStep 2522735 = 3784103) B3784103
theorem B4038265 : Blo 1680040 4038265 := bstep (se 2 (by rfl) ⟨1514349, by rfl⟩ : syracuseStep 4038265 = 3028699) B3028699
theorem B2522855 : Blo 1680040 2522855 := bstep (se 1 (by rfl) ⟨1892141, by rfl⟩ : syracuseStep 2522855 = 3784283) B3784283
theorem B7274279 : Blo 1680040 7274279 := bstep (se 1 (by rfl) ⟨5455709, by rfl⟩ : syracuseStep 7274279 = 10911419) B10911419
theorem B1892263 : Blo 1680040 1892263 := bstep (se 1 (by rfl) ⟨1419197, by rfl⟩ : syracuseStep 1892263 = 2838395) B2838395
theorem B2523047 : Blo 1680040 2523047 := bstep (se 1 (by rfl) ⟨1892285, by rfl⟩ : syracuseStep 2523047 = 3784571) B3784571
theorem B4849787 : Blo 1680040 4849787 := bstep (se 1 (by rfl) ⟨3637340, by rfl⟩ : syracuseStep 4849787 = 7274681) B7274681
theorem B54526679 : Blo 1680040 54526679 := bstep (se 1 (by rfl) ⟨40895009, by rfl⟩ : syracuseStep 54526679 = 81790019) B81790019
theorem B1680219 : Blo 1680040 1680219 := bstep (se 1 (by rfl) ⟨1260164, by rfl⟩ : syracuseStep 1680219 = 2520329) B2520329
theorem B1680255 : Blo 1680040 1680255 := bstep (se 1 (by rfl) ⟨1260191, by rfl⟩ : syracuseStep 1680255 = 2520383) B2520383
theorem B30679955 : Blo 1680040 30679955 := bstep (se 1 (by rfl) ⟨23009966, by rfl⟩ : syracuseStep 30679955 = 46019933) B46019933
theorem B4252763 : Blo 1680040 4252763 := bstep (se 1 (by rfl) ⟨3189572, by rfl⟩ : syracuseStep 4252763 = 6379145) B6379145
theorem B4252783 : Blo 1680040 4252783 := bstep (se 1 (by rfl) ⟨3189587, by rfl⟩ : syracuseStep 4252783 = 6379175) B6379175
theorem B1680539 : Blo 1680040 1680539 := bstep (se 1 (by rfl) ⟨1260404, by rfl⟩ : syracuseStep 1680539 = 2520809) B2520809
theorem B1680543 : Blo 1680040 1680543 := bstep (se 1 (by rfl) ⟨1260407, by rfl⟩ : syracuseStep 1680543 = 2520815) B2520815
theorem B16164049 : Blo 1680040 16164049 := bstep (se 2 (by rfl) ⟨6061518, by rfl⟩ : syracuseStep 16164049 = 12123037) B12123037
theorem B1680847 : Blo 1680040 1680847 := bstep (se 1 (by rfl) ⟨1260635, by rfl⟩ : syracuseStep 1680847 = 2521271) B2521271
theorem B1680879 : Blo 1680040 1680879 := bstep (se 1 (by rfl) ⟨1260659, by rfl⟩ : syracuseStep 1680879 = 2521319) B2521319
theorem B1681127 : Blo 1680040 1681127 := bstep (se 1 (by rfl) ⟨1260845, by rfl⟩ : syracuseStep 1681127 = 2521691) B2521691
theorem B5670647 : Blo 1680040 5670647 := bstep (se 1 (by rfl) ⟨4252985, by rfl⟩ : syracuseStep 5670647 = 8505971) B8505971
theorem B1681223 : Blo 1680040 1681223 := bstep (se 1 (by rfl) ⟨1260917, by rfl⟩ : syracuseStep 1681223 = 2521835) B2521835
theorem B1681243 : Blo 1680040 1681243 := bstep (se 1 (by rfl) ⟨1260932, by rfl⟩ : syracuseStep 1681243 = 2521865) B2521865
theorem B5384353 : Blo 1680040 5384353 := bstep (se 2 (by rfl) ⟨2019132, by rfl⟩ : syracuseStep 5384353 = 4038265) B4038265
theorem B8513747 : Blo 1680040 8513747 := bstep (se 1 (by rfl) ⟨6385310, by rfl⟩ : syracuseStep 8513747 = 12770621) B12770621
theorem B5384531 : Blo 1680040 5384531 := bstep (se 1 (by rfl) ⟨4038398, by rfl⟩ : syracuseStep 5384531 = 8076797) B8076797
theorem B1681823 : Blo 1680040 1681823 := bstep (se 1 (by rfl) ⟨1261367, by rfl⟩ : syracuseStep 1681823 = 2522735) B2522735
theorem B1681903 : Blo 1680040 1681903 := bstep (se 1 (by rfl) ⟨1261427, by rfl⟩ : syracuseStep 1681903 = 2522855) B2522855
theorem B3590747 : Blo 1680040 3590747 := bstep (se 1 (by rfl) ⟨2693060, by rfl⟩ : syracuseStep 3590747 = 5386121) B5386121
theorem B1682031 : Blo 1680040 1682031 := bstep (se 1 (by rfl) ⟨1261523, by rfl⟩ : syracuseStep 1682031 = 2523047) B2523047
theorem B21531257 : Blo 1680040 21531257 := bstep (se 2 (by rfl) ⟨8074221, by rfl⟩ : syracuseStep 21531257 = 16148443) B16148443
theorem B43092647 : Blo 1680040 43092647 := bstep (se 1 (by rfl) ⟨32319485, by rfl⟩ : syracuseStep 43092647 = 64638971) B64638971
theorem B2837227 : Blo 1680040 2837227 := bstep (se 1 (by rfl) ⟨2127920, by rfl⟩ : syracuseStep 2837227 = 4255841) B4255841
theorem B5671727 : Blo 1680040 5671727 := bstep (se 1 (by rfl) ⟨4253795, by rfl⟩ : syracuseStep 5671727 = 8507591) B8507591
theorem B3591209 : Blo 1680040 3591209 := bstep (se 2 (by rfl) ⟨1346703, by rfl⟩ : syracuseStep 3591209 = 2693407) B2693407
theorem B4541903 : Blo 1680040 4541903 := bstep (se 1 (by rfl) ⟨3406427, by rfl⟩ : syracuseStep 4541903 = 6812855) B6812855
theorem B40914395 : Blo 1680040 40914395 := bstep (se 1 (by rfl) ⟨30685796, by rfl⟩ : syracuseStep 40914395 = 61371593) B61371593
theorem B3190241 : Blo 1680040 3190241 := bstep (se 2 (by rfl) ⟨1196340, by rfl⟩ : syracuseStep 3190241 = 2392681) B2392681
theorem B48483845 : Blo 1680040 48483845 := bstep (se 4 (by rfl) ⟨4545360, by rfl⟩ : syracuseStep 48483845 = 9090721) B9090721
theorem B12283499 : Blo 1680040 12283499 := bstep (se 1 (by rfl) ⟨9212624, by rfl⟩ : syracuseStep 12283499 = 18425249) B18425249
theorem B4255375 : Blo 1680040 4255375 := bstep (se 1 (by rfl) ⟨3191531, by rfl⟩ : syracuseStep 4255375 = 6383063) B6383063
theorem B2838199 : Blo 1680040 2838199 := bstep (se 1 (by rfl) ⟨2128649, by rfl⟩ : syracuseStep 2838199 = 4257299) B4257299
theorem B3780287 : Blo 1680040 3780287 := bstep (se 1 (by rfl) ⟨2835215, by rfl⟩ : syracuseStep 3780287 = 5670431) B5670431
theorem B16150211 : Blo 1680040 16150211 := bstep (se 1 (by rfl) ⟨12112658, by rfl⟩ : syracuseStep 16150211 = 24225317) B24225317
theorem B5672699 : Blo 1680040 5672699 := bstep (se 1 (by rfl) ⟨4254524, by rfl⟩ : syracuseStep 5672699 = 8509049) B8509049
theorem B11497241 : Blo 1680040 11497241 := bstep (se 2 (by rfl) ⟨4311465, by rfl⟩ : syracuseStep 11497241 = 8622931) B8622931
theorem B21827357 : Blo 1680040 21827357 := bstep (se 3 (by rfl) ⟨4092629, by rfl⟩ : syracuseStep 21827357 = 8185259) B8185259
theorem B51777467 : Blo 1680040 51777467 := bstep (se 1 (by rfl) ⟨38833100, by rfl⟩ : syracuseStep 51777467 = 77666201) B77666201
theorem B10768423 : Blo 1680040 10768423 := bstep (se 1 (by rfl) ⟨8076317, by rfl⟩ : syracuseStep 10768423 = 16152635) B16152635
theorem B5673185 : Blo 1680040 5673185 := bstep (se 2 (by rfl) ⟨2127444, by rfl⟩ : syracuseStep 5673185 = 4254889) B4254889
theorem B3780863 : Blo 1680040 3780863 := bstep (se 1 (by rfl) ⟨2835647, by rfl⟩ : syracuseStep 3780863 = 5671295) B5671295
theorem B36335897 : Blo 1680040 36335897 := bstep (se 2 (by rfl) ⟨13625961, by rfl⟩ : syracuseStep 36335897 = 27251923) B27251923
theorem B4788733 : Blo 1680040 4788733 := bstep (se 3 (by rfl) ⟨897887, by rfl⟩ : syracuseStep 4788733 = 1795775) B1795775
theorem B32739869 : Blo 1680040 32739869 := bstep (se 3 (by rfl) ⟨6138725, by rfl⟩ : syracuseStep 32739869 = 12277451) B12277451
theorem B2520185 : Blo 1680040 2520185 := bstep (se 2 (by rfl) ⟨945069, by rfl⟩ : syracuseStep 2520185 = 1890139) B1890139
theorem B3782015 : Blo 1680040 3782015 := bstep (se 1 (by rfl) ⟨2836511, by rfl⟩ : syracuseStep 3782015 = 5673023) B5673023
theorem B8295895 : Blo 1680040 8295895 := bstep (se 1 (by rfl) ⟨6221921, by rfl⟩ : syracuseStep 8295895 = 12443843) B12443843
theorem B5387735 : Blo 1680040 5387735 := bstep (se 1 (by rfl) ⟨4040801, by rfl⟩ : syracuseStep 5387735 = 8081603) B8081603
theorem B2520713 : Blo 1680040 2520713 := bstep (se 2 (by rfl) ⟨945267, by rfl⟩ : syracuseStep 2520713 = 1890535) B1890535
theorem B9090767 : Blo 1680040 9090767 := bstep (se 1 (by rfl) ⟨6818075, by rfl⟩ : syracuseStep 9090767 = 13636151) B13636151
theorem B3192527 : Blo 1680040 3192527 := bstep (se 1 (by rfl) ⟨2394395, by rfl⟩ : syracuseStep 3192527 = 4788791) B4788791
theorem B9574139 : Blo 1680040 9574139 := bstep (se 1 (by rfl) ⟨7180604, by rfl⟩ : syracuseStep 9574139 = 14361209) B14361209
theorem B3782483 : Blo 1680040 3782483 := bstep (se 1 (by rfl) ⟨2836862, by rfl⟩ : syracuseStep 3782483 = 5673725) B5673725
theorem B2520923 : Blo 1680040 2520923 := bstep (se 1 (by rfl) ⟨1890692, by rfl⟩ : syracuseStep 2520923 = 3781385) B3781385
theorem B2520959 : Blo 1680040 2520959 := bstep (se 1 (by rfl) ⟨1890719, by rfl⟩ : syracuseStep 2520959 = 3781439) B3781439
theorem B8509373 : Blo 1680040 8509373 := bstep (se 3 (by rfl) ⟨1595507, by rfl⟩ : syracuseStep 8509373 = 3191015) B3191015
theorem B3782591 : Blo 1680040 3782591 := bstep (se 1 (by rfl) ⟨2836943, by rfl⟩ : syracuseStep 3782591 = 5673887) B5673887
theorem B2521055 : Blo 1680040 2521055 := bstep (se 1 (by rfl) ⟨1890791, by rfl⟩ : syracuseStep 2521055 = 3781583) B3781583
theorem B2521115 : Blo 1680040 2521115 := bstep (se 1 (by rfl) ⟨1890836, by rfl⟩ : syracuseStep 2521115 = 3781673) B3781673
theorem B159520873 : Blo 1680040 159520873 := bstep (se 2 (by rfl) ⟨59820327, by rfl⟩ : syracuseStep 159520873 = 119640655) B119640655
theorem B2521307 : Blo 1680040 2521307 := bstep (se 1 (by rfl) ⟨1890980, by rfl⟩ : syracuseStep 2521307 = 3781961) B3781961
theorem B1890715 : Blo 1680040 1890715 := bstep (se 1 (by rfl) ⟨1418036, by rfl⟩ : syracuseStep 1890715 = 2836073) B2836073
theorem B5831099 : Blo 1680040 5831099 := bstep (se 1 (by rfl) ⟨4373324, by rfl⟩ : syracuseStep 5831099 = 8746649) B8746649
theorem B9337321 : Blo 1680040 9337321 := bstep (se 2 (by rfl) ⟨3501495, by rfl⟩ : syracuseStep 9337321 = 7002991) B7002991
theorem B2521577 : Blo 1680040 2521577 := bstep (se 2 (by rfl) ⟨945591, by rfl⟩ : syracuseStep 2521577 = 1891183) B1891183
theorem B1891111 : Blo 1680040 1891111 := bstep (se 1 (by rfl) ⟨1418333, by rfl⟩ : syracuseStep 1891111 = 2836667) B2836667
theorem B3832687 : Blo 1680040 3832687 := bstep (se 1 (by rfl) ⟨2874515, by rfl⟩ : syracuseStep 3832687 = 5749031) B5749031
theorem B9575279 : Blo 1680040 9575279 := bstep (se 1 (by rfl) ⟨7181459, by rfl⟩ : syracuseStep 9575279 = 14362919) B14362919
theorem B2521967 : Blo 1680040 2521967 := bstep (se 1 (by rfl) ⟨1891475, by rfl⟩ : syracuseStep 2521967 = 3782951) B3782951
theorem B4733819 : Blo 1680040 4733819 := bstep (se 1 (by rfl) ⟨3550364, by rfl⟩ : syracuseStep 4733819 = 7100729) B7100729
theorem B2522207 : Blo 1680040 2522207 := bstep (se 1 (by rfl) ⟨1891655, by rfl⟩ : syracuseStep 2522207 = 3783311) B3783311
theorem B2522267 : Blo 1680040 2522267 := bstep (se 1 (by rfl) ⟨1891700, by rfl⟩ : syracuseStep 2522267 = 3783401) B3783401
theorem B1891579 : Blo 1680040 1891579 := bstep (se 1 (by rfl) ⟨1418684, by rfl⟩ : syracuseStep 1891579 = 2837369) B2837369
theorem B16162051 : Blo 1680040 16162051 := bstep (se 1 (by rfl) ⟨12121538, by rfl⟩ : syracuseStep 16162051 = 24243077) B24243077
theorem B2522423 : Blo 1680040 2522423 := bstep (se 1 (by rfl) ⟨1891817, by rfl⟩ : syracuseStep 2522423 = 3783635) B3783635
theorem B2522603 : Blo 1680040 2522603 := bstep (se 1 (by rfl) ⟨1891952, by rfl⟩ : syracuseStep 2522603 = 3783905) B3783905
theorem B6381119 : Blo 1680040 6381119 := bstep (se 1 (by rfl) ⟨4785839, by rfl⟩ : syracuseStep 6381119 = 9571679) B9571679
theorem B2522807 : Blo 1680040 2522807 := bstep (se 1 (by rfl) ⟨1892105, by rfl⟩ : syracuseStep 2522807 = 3784211) B3784211
theorem B7184159 : Blo 1680040 7184159 := bstep (se 1 (by rfl) ⟨5388119, by rfl⟩ : syracuseStep 7184159 = 10776239) B10776239
theorem B4849519 : Blo 1680040 4849519 := bstep (se 1 (by rfl) ⟨3637139, by rfl⟩ : syracuseStep 4849519 = 7274279) B7274279
theorem B2523017 : Blo 1680040 2523017 := bstep (se 2 (by rfl) ⟨946131, by rfl⟩ : syracuseStep 2523017 = 1892263) B1892263
theorem B10510235 : Blo 1680040 10510235 := bstep (se 1 (by rfl) ⟨7882676, by rfl⟩ : syracuseStep 10510235 = 15765353) B15765353
theorem B8511479 : Blo 1680040 8511479 := bstep (se 1 (by rfl) ⟨6383609, by rfl⟩ : syracuseStep 8511479 = 12767219) B12767219
theorem B24223931 : Blo 1680040 24223931 := bstep (se 1 (by rfl) ⟨18167948, by rfl⟩ : syracuseStep 24223931 = 36335897) B36335897
theorem B2835175 : Blo 1680040 2835175 := bstep (se 1 (by rfl) ⟨2126381, by rfl⟩ : syracuseStep 2835175 = 4252763) B4252763
theorem B1680123 : Blo 1680040 1680123 := bstep (se 1 (by rfl) ⟨1260092, by rfl⟩ : syracuseStep 1680123 = 2520185) B2520185
theorem B1680475 : Blo 1680040 1680475 := bstep (se 1 (by rfl) ⟨1260356, by rfl⟩ : syracuseStep 1680475 = 2520713) B2520713
theorem B6382759 : Blo 1680040 6382759 := bstep (se 1 (by rfl) ⟨4787069, by rfl⟩ : syracuseStep 6382759 = 9574139) B9574139
theorem B1680615 : Blo 1680040 1680615 := bstep (se 1 (by rfl) ⟨1260461, by rfl⟩ : syracuseStep 1680615 = 2520923) B2520923
theorem B1680639 : Blo 1680040 1680639 := bstep (se 1 (by rfl) ⟨1260479, by rfl⟩ : syracuseStep 1680639 = 2520959) B2520959
theorem B1680703 : Blo 1680040 1680703 := bstep (se 1 (by rfl) ⟨1260527, by rfl⟩ : syracuseStep 1680703 = 2521055) B2521055
theorem B1680743 : Blo 1680040 1680743 := bstep (se 1 (by rfl) ⟨1260557, by rfl⟩ : syracuseStep 1680743 = 2521115) B2521115
theorem B1680871 : Blo 1680040 1680871 := bstep (se 1 (by rfl) ⟨1260653, by rfl⟩ : syracuseStep 1680871 = 2521307) B2521307
theorem B5670377 : Blo 1680040 5670377 := bstep (se 2 (by rfl) ⟨2126391, by rfl⟩ : syracuseStep 5670377 = 4252783) B4252783
theorem B3589687 : Blo 1680040 3589687 := bstep (se 1 (by rfl) ⟨2692265, by rfl⟩ : syracuseStep 3589687 = 5384531) B5384531
theorem B1681051 : Blo 1680040 1681051 := bstep (se 1 (by rfl) ⟨1260788, by rfl⟩ : syracuseStep 1681051 = 2521577) B2521577
theorem B2393831 : Blo 1680040 2393831 := bstep (se 1 (by rfl) ⟨1795373, by rfl⟩ : syracuseStep 2393831 = 3590747) B3590747
theorem B14354171 : Blo 1680040 14354171 := bstep (se 1 (by rfl) ⟨10765628, by rfl⟩ : syracuseStep 14354171 = 21531257) B21531257
theorem B6383519 : Blo 1680040 6383519 := bstep (se 1 (by rfl) ⟨4787639, by rfl⟩ : syracuseStep 6383519 = 9575279) B9575279
theorem B1681311 : Blo 1680040 1681311 := bstep (se 1 (by rfl) ⟨1260983, by rfl⟩ : syracuseStep 1681311 = 2521967) B2521967
theorem B3155879 : Blo 1680040 3155879 := bstep (se 1 (by rfl) ⟨2366909, by rfl⟩ : syracuseStep 3155879 = 4733819) B4733819
theorem B11061193 : Blo 1680040 11061193 := bstep (se 2 (by rfl) ⟨4147947, by rfl⟩ : syracuseStep 11061193 = 8295895) B8295895
theorem B2394139 : Blo 1680040 2394139 := bstep (se 1 (by rfl) ⟨1795604, by rfl⟩ : syracuseStep 2394139 = 3591209) B3591209
theorem B1681471 : Blo 1680040 1681471 := bstep (se 1 (by rfl) ⟨1261103, by rfl⟩ : syracuseStep 1681471 = 2522207) B2522207
theorem B1681511 : Blo 1680040 1681511 := bstep (se 1 (by rfl) ⟨1261133, by rfl⟩ : syracuseStep 1681511 = 2522267) B2522267
theorem B1681615 : Blo 1680040 1681615 := bstep (se 1 (by rfl) ⟨1261211, by rfl⟩ : syracuseStep 1681615 = 2522423) B2522423
theorem B1681735 : Blo 1680040 1681735 := bstep (se 1 (by rfl) ⟨1261301, by rfl⟩ : syracuseStep 1681735 = 2522603) B2522603
theorem B4254079 : Blo 1680040 4254079 := bstep (se 1 (by rfl) ⟨3190559, by rfl⟩ : syracuseStep 4254079 = 6381119) B6381119
theorem B1681871 : Blo 1680040 1681871 := bstep (se 1 (by rfl) ⟨1261403, by rfl⟩ : syracuseStep 1681871 = 2522807) B2522807
theorem B10766807 : Blo 1680040 10766807 := bstep (se 1 (by rfl) ⟨8075105, by rfl⟩ : syracuseStep 10766807 = 16150211) B16150211
theorem B6466025 : Blo 1680040 6466025 := bstep (se 2 (by rfl) ⟨2424759, by rfl⟩ : syracuseStep 6466025 = 4849519) B4849519
theorem B14551571 : Blo 1680040 14551571 := bstep (se 1 (by rfl) ⟨10913678, by rfl⟩ : syracuseStep 14551571 = 21827357) B21827357
theorem B1682011 : Blo 1680040 1682011 := bstep (se 1 (by rfl) ⟨1261508, by rfl⟩ : syracuseStep 1682011 = 2523017) B2523017
theorem B7006823 : Blo 1680040 7006823 := bstep (se 1 (by rfl) ⟨5255117, by rfl⟩ : syracuseStep 7006823 = 10510235) B10510235
theorem B7179137 : Blo 1680040 7179137 := bstep (se 2 (by rfl) ⟨2692176, by rfl⟩ : syracuseStep 7179137 = 5384353) B5384353
theorem B21826579 : Blo 1680040 21826579 := bstep (se 1 (by rfl) ⟨16369934, by rfl⟩ : syracuseStep 21826579 = 32739869) B32739869
theorem B36351119 : Blo 1680040 36351119 := bstep (se 1 (by rfl) ⟨27263339, by rfl⟩ : syracuseStep 36351119 = 54526679) B54526679
theorem B6384977 : Blo 1680040 6384977 := bstep (se 2 (by rfl) ⟨2394366, by rfl⟩ : syracuseStep 6384977 = 4788733) B4788733
theorem B3780431 : Blo 1680040 3780431 := bstep (se 1 (by rfl) ⟨2835323, by rfl⟩ : syracuseStep 3780431 = 5670647) B5670647
theorem B5672915 : Blo 1680040 5672915 := bstep (se 1 (by rfl) ⟨4254686, by rfl⟩ : syracuseStep 5672915 = 8509373) B8509373
theorem B32755997 : Blo 1680040 32755997 := bstep (se 3 (by rfl) ⟨6141749, by rfl⟩ : syracuseStep 32755997 = 12283499) B12283499
theorem B3887399 : Blo 1680040 3887399 := bstep (se 1 (by rfl) ⟨2915549, by rfl⟩ : syracuseStep 3887399 = 5831099) B5831099
theorem B21549401 : Blo 1680040 21549401 := bstep (se 2 (by rfl) ⟨8081025, by rfl⟩ : syracuseStep 21549401 = 16162051) B16162051
theorem B3781151 : Blo 1680040 3781151 := bstep (se 1 (by rfl) ⟨2835863, by rfl⟩ : syracuseStep 3781151 = 5671727) B5671727
theorem B5673833 : Blo 1680040 5673833 := bstep (se 2 (by rfl) ⟨2127687, by rfl⟩ : syracuseStep 5673833 = 4255375) B4255375
theorem B3027935 : Blo 1680040 3027935 := bstep (se 1 (by rfl) ⟨2270951, by rfl⟩ : syracuseStep 3027935 = 4541903) B4541903
theorem B27276263 : Blo 1680040 27276263 := bstep (se 1 (by rfl) ⟨20457197, by rfl⟩ : syracuseStep 27276263 = 40914395) B40914395
theorem B2126827 : Blo 1680040 2126827 := bstep (se 1 (by rfl) ⟨1595120, by rfl⟩ : syracuseStep 2126827 = 3190241) B3190241
theorem B32322563 : Blo 1680040 32322563 := bstep (se 1 (by rfl) ⟨24241922, by rfl⟩ : syracuseStep 32322563 = 48483845) B48483845
theorem B2520191 : Blo 1680040 2520191 := bstep (se 1 (by rfl) ⟨1890143, by rfl⟩ : syracuseStep 2520191 = 3780287) B3780287
theorem B3781799 : Blo 1680040 3781799 := bstep (se 1 (by rfl) ⟨2836349, by rfl⟩ : syracuseStep 3781799 = 5672699) B5672699
theorem B7664827 : Blo 1680040 7664827 := bstep (se 1 (by rfl) ⟨5748620, by rfl⟩ : syracuseStep 7664827 = 11497241) B11497241
theorem B4789439 : Blo 1680040 4789439 := bstep (se 1 (by rfl) ⟨3592079, by rfl⟩ : syracuseStep 4789439 = 7184159) B7184159
theorem B34518311 : Blo 1680040 34518311 := bstep (se 1 (by rfl) ⟨25888733, by rfl⟩ : syracuseStep 34518311 = 51777467) B51777467
theorem B5674319 : Blo 1680040 5674319 := bstep (se 1 (by rfl) ⟨4255739, by rfl⟩ : syracuseStep 5674319 = 8511479) B8511479
theorem B14357897 : Blo 1680040 14357897 := bstep (se 2 (by rfl) ⟨5384211, by rfl⟩ : syracuseStep 14357897 = 10768423) B10768423
theorem B3233191 : Blo 1680040 3233191 := bstep (se 1 (by rfl) ⟨2424893, by rfl⟩ : syracuseStep 3233191 = 4849787) B4849787
theorem B212694497 : Blo 1680040 212694497 := bstep (se 2 (by rfl) ⟨79760436, by rfl⟩ : syracuseStep 212694497 = 159520873) B159520873
theorem B3782123 : Blo 1680040 3782123 := bstep (se 1 (by rfl) ⟨2836592, by rfl⟩ : syracuseStep 3782123 = 5673185) B5673185
theorem B2520575 : Blo 1680040 2520575 := bstep (se 1 (by rfl) ⟨1890431, by rfl⟩ : syracuseStep 2520575 = 3780863) B3780863
theorem B2520953 : Blo 1680040 2520953 := bstep (se 2 (by rfl) ⟨945357, by rfl⟩ : syracuseStep 2520953 = 1890715) B1890715
theorem B20453303 : Blo 1680040 20453303 := bstep (se 1 (by rfl) ⟨15339977, by rfl⟩ : syracuseStep 20453303 = 30679955) B30679955
theorem B2521343 : Blo 1680040 2521343 := bstep (se 1 (by rfl) ⟨1891007, by rfl⟩ : syracuseStep 2521343 = 3782015) B3782015
theorem B3782969 : Blo 1680040 3782969 := bstep (se 2 (by rfl) ⟨1418613, by rfl⟩ : syracuseStep 3782969 = 2837227) B2837227
theorem B2521481 : Blo 1680040 2521481 := bstep (se 2 (by rfl) ⟨945555, by rfl⟩ : syracuseStep 2521481 = 1891111) B1891111
theorem B6060511 : Blo 1680040 6060511 := bstep (se 1 (by rfl) ⟨4545383, by rfl⟩ : syracuseStep 6060511 = 9090767) B9090767
theorem B2128351 : Blo 1680040 2128351 := bstep (se 1 (by rfl) ⟨1596263, by rfl⟩ : syracuseStep 2128351 = 3192527) B3192527
theorem B5110249 : Blo 1680040 5110249 := bstep (se 2 (by rfl) ⟨1916343, by rfl⟩ : syracuseStep 5110249 = 3832687) B3832687
theorem B2521655 : Blo 1680040 2521655 := bstep (se 1 (by rfl) ⟨1891241, by rfl⟩ : syracuseStep 2521655 = 3782483) B3782483
theorem B14367293 : Blo 1680040 14367293 := bstep (se 3 (by rfl) ⟨2693867, by rfl⟩ : syracuseStep 14367293 = 5387735) B5387735
theorem B2521727 : Blo 1680040 2521727 := bstep (se 1 (by rfl) ⟨1891295, by rfl⟩ : syracuseStep 2521727 = 3782591) B3782591
theorem B5675831 : Blo 1680040 5675831 := bstep (se 1 (by rfl) ⟨4256873, by rfl⟩ : syracuseStep 5675831 = 8513747) B8513747
theorem B21552065 : Blo 1680040 21552065 := bstep (se 2 (by rfl) ⟨8082024, by rfl⟩ : syracuseStep 21552065 = 16164049) B16164049
theorem B2522105 : Blo 1680040 2522105 := bstep (se 2 (by rfl) ⟨945789, by rfl⟩ : syracuseStep 2522105 = 1891579) B1891579
theorem B28728431 : Blo 1680040 28728431 := bstep (se 1 (by rfl) ⟨21546323, by rfl⟩ : syracuseStep 28728431 = 43092647) B43092647
theorem B3784265 : Blo 1680040 3784265 := bstep (se 2 (by rfl) ⟨1419099, by rfl⟩ : syracuseStep 3784265 = 2838199) B2838199
theorem B49799045 : Blo 1680040 49799045 := bstep (se 4 (by rfl) ⟨4668660, by rfl⟩ : syracuseStep 49799045 = 9337321) B9337321
theorem B19144997 : Blo 1680040 19144997 := bstep (se 4 (by rfl) ⟨1794843, by rfl⟩ : syracuseStep 19144997 = 3589687) B3589687
theorem B1680127 : Blo 1680040 1680127 := bstep (se 1 (by rfl) ⟨1260095, by rfl⟩ : syracuseStep 1680127 = 2520191) B2520191
theorem B23012207 : Blo 1680040 23012207 := bstep (se 1 (by rfl) ⟨17259155, by rfl⟩ : syracuseStep 23012207 = 34518311) B34518311
theorem B141796331 : Blo 1680040 141796331 := bstep (se 1 (by rfl) ⟨106347248, by rfl⟩ : syracuseStep 141796331 = 212694497) B212694497
theorem B1680383 : Blo 1680040 1680383 := bstep (se 1 (by rfl) ⟨1260287, by rfl⟩ : syracuseStep 1680383 = 2520575) B2520575
theorem B9569447 : Blo 1680040 9569447 := bstep (se 1 (by rfl) ⟨7177085, by rfl⟩ : syracuseStep 9569447 = 14354171) B14354171
theorem B1680635 : Blo 1680040 1680635 := bstep (se 1 (by rfl) ⟨1260476, by rfl⟩ : syracuseStep 1680635 = 2520953) B2520953
theorem B2835769 : Blo 1680040 2835769 := bstep (se 2 (by rfl) ⟨1063413, by rfl⟩ : syracuseStep 2835769 = 2126827) B2126827
theorem B1680895 : Blo 1680040 1680895 := bstep (se 1 (by rfl) ⟨1260671, by rfl⟩ : syracuseStep 1680895 = 2521343) B2521343
theorem B1680987 : Blo 1680040 1680987 := bstep (se 1 (by rfl) ⟨1260740, by rfl⟩ : syracuseStep 1680987 = 2521481) B2521481
theorem B7177871 : Blo 1680040 7177871 := bstep (se 1 (by rfl) ⟨5383403, by rfl⟩ : syracuseStep 7177871 = 10766807) B10766807
theorem B1681103 : Blo 1680040 1681103 := bstep (se 1 (by rfl) ⟨1260827, by rfl⟩ : syracuseStep 1681103 = 2521655) B2521655
theorem B9578195 : Blo 1680040 9578195 := bstep (se 1 (by rfl) ⟨7183646, by rfl⟩ : syracuseStep 9578195 = 14367293) B14367293
theorem B4671215 : Blo 1680040 4671215 := bstep (se 1 (by rfl) ⟨3503411, by rfl⟩ : syracuseStep 4671215 = 7006823) B7006823
theorem B1681151 : Blo 1680040 1681151 := bstep (se 1 (by rfl) ⟨1260863, by rfl⟩ : syracuseStep 1681151 = 2521727) B2521727
theorem B4310921 : Blo 1680040 4310921 := bstep (se 2 (by rfl) ⟨1616595, by rfl⟩ : syracuseStep 4310921 = 3233191) B3233191
theorem B4786091 : Blo 1680040 4786091 := bstep (se 1 (by rfl) ⟨3589568, by rfl⟩ : syracuseStep 4786091 = 7179137) B7179137
theorem B6383549 : Blo 1680040 6383549 := bstep (se 3 (by rfl) ⟨1196915, by rfl⟩ : syracuseStep 6383549 = 2393831) B2393831
theorem B1681403 : Blo 1680040 1681403 := bstep (se 1 (by rfl) ⟨1261052, by rfl⟩ : syracuseStep 1681403 = 2522105) B2522105
theorem B24234079 : Blo 1680040 24234079 := bstep (se 1 (by rfl) ⟨18175559, by rfl⟩ : syracuseStep 24234079 = 36351119) B36351119
theorem B8415677 : Blo 1680040 8415677 := bstep (se 3 (by rfl) ⟨1577939, by rfl⟩ : syracuseStep 8415677 = 3155879) B3155879
theorem B14748257 : Blo 1680040 14748257 := bstep (se 2 (by rfl) ⟨5530596, by rfl⟩ : syracuseStep 14748257 = 11061193) B11061193
theorem B16149287 : Blo 1680040 16149287 := bstep (se 1 (by rfl) ⟨12111965, by rfl⟩ : syracuseStep 16149287 = 24223931) B24223931
theorem B5672105 : Blo 1680040 5672105 := bstep (se 2 (by rfl) ⟨2127039, by rfl⟩ : syracuseStep 5672105 = 4254079) B4254079
theorem B8080681 : Blo 1680040 8080681 := bstep (se 2 (by rfl) ⟨3030255, by rfl⟩ : syracuseStep 8080681 = 6060511) B6060511
theorem B2837801 : Blo 1680040 2837801 := bstep (se 2 (by rfl) ⟨1064175, by rfl⟩ : syracuseStep 2837801 = 2128351) B2128351
theorem B2018623 : Blo 1680040 2018623 := bstep (se 1 (by rfl) ⟨1513967, by rfl⟩ : syracuseStep 2018623 = 3027935) B3027935
theorem B21548375 : Blo 1680040 21548375 := bstep (se 1 (by rfl) ⟨16161281, by rfl⟩ : syracuseStep 21548375 = 32322563) B32322563
theorem B10366397 : Blo 1680040 10366397 := bstep (se 3 (by rfl) ⟨1943699, by rfl⟩ : syracuseStep 10366397 = 3887399) B3887399
theorem B9571931 : Blo 1680040 9571931 := bstep (se 1 (by rfl) ⟨7178948, by rfl⟩ : syracuseStep 9571931 = 14357897) B14357897
theorem B3780233 : Blo 1680040 3780233 := bstep (se 2 (by rfl) ⟨1417587, by rfl⟩ : syracuseStep 3780233 = 2835175) B2835175
theorem B3780251 : Blo 1680040 3780251 := bstep (se 1 (by rfl) ⟨2835188, by rfl⟩ : syracuseStep 3780251 = 5670377) B5670377
theorem B4255679 : Blo 1680040 4255679 := bstep (se 1 (by rfl) ⟨3191759, by rfl⟩ : syracuseStep 4255679 = 6383519) B6383519
theorem B13635535 : Blo 1680040 13635535 := bstep (se 1 (by rfl) ⟨10226651, by rfl⟩ : syracuseStep 13635535 = 20453303) B20453303
theorem B29102105 : Blo 1680040 29102105 := bstep (se 2 (by rfl) ⟨10913289, by rfl⟩ : syracuseStep 29102105 = 21826579) B21826579
theorem B10219769 : Blo 1680040 10219769 := bstep (se 2 (by rfl) ⟨3832413, by rfl⟩ : syracuseStep 10219769 = 7664827) B7664827
theorem B4256651 : Blo 1680040 4256651 := bstep (se 1 (by rfl) ⟨3192488, by rfl⟩ : syracuseStep 4256651 = 6384977) B6384977
theorem B132797453 : Blo 1680040 132797453 := bstep (se 3 (by rfl) ⟨24899522, by rfl⟩ : syracuseStep 132797453 = 49799045) B49799045
theorem B2520287 : Blo 1680040 2520287 := bstep (se 1 (by rfl) ⟨1890215, by rfl⟩ : syracuseStep 2520287 = 3780431) B3780431
theorem B3781943 : Blo 1680040 3781943 := bstep (se 1 (by rfl) ⟨2836457, by rfl⟩ : syracuseStep 3781943 = 5672915) B5672915
theorem B3192185 : Blo 1680040 3192185 := bstep (se 2 (by rfl) ⟨1197069, by rfl⟩ : syracuseStep 3192185 = 2394139) B2394139
theorem B21837331 : Blo 1680040 21837331 := bstep (se 1 (by rfl) ⟨16377998, by rfl⟩ : syracuseStep 21837331 = 32755997) B32755997
theorem B14366267 : Blo 1680040 14366267 := bstep (se 1 (by rfl) ⟨10774700, by rfl⟩ : syracuseStep 14366267 = 21549401) B21549401
theorem B2520767 : Blo 1680040 2520767 := bstep (se 1 (by rfl) ⟨1890575, by rfl⟩ : syracuseStep 2520767 = 3781151) B3781151
theorem B3782555 : Blo 1680040 3782555 := bstep (se 1 (by rfl) ⟨2836916, by rfl⟩ : syracuseStep 3782555 = 5673833) B5673833
theorem B6813665 : Blo 1680040 6813665 := bstep (se 2 (by rfl) ⟨2555124, by rfl⟩ : syracuseStep 6813665 = 5110249) B5110249
theorem B18184175 : Blo 1680040 18184175 := bstep (se 1 (by rfl) ⟨13638131, by rfl⟩ : syracuseStep 18184175 = 27276263) B27276263
theorem B2521199 : Blo 1680040 2521199 := bstep (se 1 (by rfl) ⟨1890899, by rfl⟩ : syracuseStep 2521199 = 3781799) B3781799
theorem B3192959 : Blo 1680040 3192959 := bstep (se 1 (by rfl) ⟨2394719, by rfl⟩ : syracuseStep 3192959 = 4789439) B4789439
theorem B3782879 : Blo 1680040 3782879 := bstep (se 1 (by rfl) ⟨2837159, by rfl⟩ : syracuseStep 3782879 = 5674319) B5674319
theorem B2521415 : Blo 1680040 2521415 := bstep (se 1 (by rfl) ⟨1891061, by rfl⟩ : syracuseStep 2521415 = 3782123) B3782123
theorem B17242733 : Blo 1680040 17242733 := bstep (se 3 (by rfl) ⟨3233012, by rfl⟩ : syracuseStep 17242733 = 6466025) B6466025
theorem B38804189 : Blo 1680040 38804189 := bstep (se 3 (by rfl) ⟨7275785, by rfl⟩ : syracuseStep 38804189 = 14551571) B14551571
theorem B2521979 : Blo 1680040 2521979 := bstep (se 1 (by rfl) ⟨1891484, by rfl⟩ : syracuseStep 2521979 = 3782969) B3782969
theorem B8510345 : Blo 1680040 8510345 := bstep (se 2 (by rfl) ⟨3191379, by rfl⟩ : syracuseStep 8510345 = 6382759) B6382759
theorem B3783887 : Blo 1680040 3783887 := bstep (se 1 (by rfl) ⟨2837915, by rfl⟩ : syracuseStep 3783887 = 5675831) B5675831
theorem B14368043 : Blo 1680040 14368043 := bstep (se 1 (by rfl) ⟨10776032, by rfl⟩ : syracuseStep 14368043 = 21552065) B21552065
theorem B19152287 : Blo 1680040 19152287 := bstep (se 1 (by rfl) ⟨14364215, by rfl⟩ : syracuseStep 19152287 = 28728431) B28728431
theorem B2522843 : Blo 1680040 2522843 := bstep (se 1 (by rfl) ⟨1892132, by rfl⟩ : syracuseStep 2522843 = 3784265) B3784265
theorem B12763331 : Blo 1680040 12763331 := bstep (se 1 (by rfl) ⟨9572498, by rfl⟩ : syracuseStep 12763331 = 19144997) B19144997
theorem B1680191 : Blo 1680040 1680191 := bstep (se 1 (by rfl) ⟨1260143, by rfl⟩ : syracuseStep 1680191 = 2520287) B2520287
theorem B9577511 : Blo 1680040 9577511 := bstep (se 1 (by rfl) ⟨7183133, by rfl⟩ : syracuseStep 9577511 = 14366267) B14366267
theorem B4785247 : Blo 1680040 4785247 := bstep (se 1 (by rfl) ⟨3588935, by rfl⟩ : syracuseStep 4785247 = 7177871) B7177871
theorem B1680511 : Blo 1680040 1680511 := bstep (se 1 (by rfl) ⟨1260383, by rfl⟩ : syracuseStep 1680511 = 2520767) B2520767
theorem B3114143 : Blo 1680040 3114143 := bstep (se 1 (by rfl) ⟨2335607, by rfl⟩ : syracuseStep 3114143 = 4671215) B4671215
theorem B1680799 : Blo 1680040 1680799 := bstep (se 1 (by rfl) ⟨1260599, by rfl⟩ : syracuseStep 1680799 = 2521199) B2521199
theorem B1680943 : Blo 1680040 1680943 := bstep (se 1 (by rfl) ⟨1260707, by rfl⟩ : syracuseStep 1680943 = 2521415) B2521415
theorem B10774241 : Blo 1680040 10774241 := bstep (se 2 (by rfl) ⟨4040340, by rfl⟩ : syracuseStep 10774241 = 8080681) B8080681
theorem B11495155 : Blo 1680040 11495155 := bstep (se 1 (by rfl) ⟨8621366, by rfl⟩ : syracuseStep 11495155 = 17242733) B17242733
theorem B10766191 : Blo 1680040 10766191 := bstep (se 1 (by rfl) ⟨8074643, by rfl⟩ : syracuseStep 10766191 = 16149287) B16149287
theorem B1681319 : Blo 1680040 1681319 := bstep (se 1 (by rfl) ⟨1260989, by rfl⟩ : syracuseStep 1681319 = 2521979) B2521979
theorem B29116441 : Blo 1680040 29116441 := bstep (se 2 (by rfl) ⟨10918665, by rfl⟩ : syracuseStep 29116441 = 21837331) B21837331
theorem B9578695 : Blo 1680040 9578695 := bstep (se 1 (by rfl) ⟨7184021, by rfl⟩ : syracuseStep 9578695 = 14368043) B14368043
theorem B11495789 : Blo 1680040 11495789 := bstep (se 3 (by rfl) ⟨2155460, by rfl⟩ : syracuseStep 11495789 = 4310921) B4310921
theorem B1681895 : Blo 1680040 1681895 := bstep (se 1 (by rfl) ⟨1261421, by rfl⟩ : syracuseStep 1681895 = 2522843) B2522843
theorem B18180713 : Blo 1680040 18180713 := bstep (se 2 (by rfl) ⟨6817767, by rfl⟩ : syracuseStep 18180713 = 13635535) B13635535
theorem B2837119 : Blo 1680040 2837119 := bstep (se 1 (by rfl) ⟨2127839, by rfl⟩ : syracuseStep 2837119 = 4255679) B4255679
theorem B354126541 : Blo 1680040 354126541 := bstep (se 3 (by rfl) ⟨66398726, by rfl⟩ : syracuseStep 354126541 = 132797453) B132797453
theorem B77605613 : Blo 1680040 77605613 := bstep (se 3 (by rfl) ⟨14551052, by rfl⟩ : syracuseStep 77605613 = 29102105) B29102105
theorem B32312105 : Blo 1680040 32312105 := bstep (se 2 (by rfl) ⟨12117039, by rfl⟩ : syracuseStep 32312105 = 24234079) B24234079
theorem B8514557 : Blo 1680040 8514557 := bstep (se 3 (by rfl) ⟨1596479, by rfl⟩ : syracuseStep 8514557 = 3192959) B3192959
theorem B2837767 : Blo 1680040 2837767 := bstep (se 1 (by rfl) ⟨2128325, by rfl⟩ : syracuseStep 2837767 = 4256651) B4256651
theorem B94530887 : Blo 1680040 94530887 := bstep (se 1 (by rfl) ⟨70898165, by rfl⟩ : syracuseStep 94530887 = 141796331) B141796331
theorem B6385463 : Blo 1680040 6385463 := bstep (se 1 (by rfl) ⟨4789097, by rfl⟩ : syracuseStep 6385463 = 9578195) B9578195
theorem B3190727 : Blo 1680040 3190727 := bstep (se 1 (by rfl) ⟨2393045, by rfl⟩ : syracuseStep 3190727 = 4786091) B4786091
theorem B4255699 : Blo 1680040 4255699 := bstep (se 1 (by rfl) ⟨3191774, by rfl⟩ : syracuseStep 4255699 = 6383549) B6383549
theorem B4542443 : Blo 1680040 4542443 := bstep (se 1 (by rfl) ⟨3406832, by rfl⟩ : syracuseStep 4542443 = 6813665) B6813665
theorem B3781025 : Blo 1680040 3781025 := bstep (se 2 (by rfl) ⟨1417884, by rfl⟩ : syracuseStep 3781025 = 2835769) B2835769
theorem B2691497 : Blo 1680040 2691497 := bstep (se 2 (by rfl) ⟨1009311, by rfl⟩ : syracuseStep 2691497 = 2018623) B2018623
theorem B103477837 : Blo 1680040 103477837 := bstep (se 3 (by rfl) ⟨19402094, by rfl⟩ : syracuseStep 103477837 = 38804189) B38804189
theorem B5673563 : Blo 1680040 5673563 := bstep (se 1 (by rfl) ⟨4255172, by rfl⟩ : syracuseStep 5673563 = 8510345) B8510345
theorem B3781403 : Blo 1680040 3781403 := bstep (se 1 (by rfl) ⟨2836052, by rfl⟩ : syracuseStep 3781403 = 5672105) B5672105
theorem B14365583 : Blo 1680040 14365583 := bstep (se 1 (by rfl) ⟨10774187, by rfl⟩ : syracuseStep 14365583 = 21548375) B21548375
theorem B12768191 : Blo 1680040 12768191 := bstep (se 1 (by rfl) ⟨9576143, by rfl⟩ : syracuseStep 12768191 = 19152287) B19152287
theorem B6910931 : Blo 1680040 6910931 := bstep (se 1 (by rfl) ⟨5183198, by rfl⟩ : syracuseStep 6910931 = 10366397) B10366397
theorem B2520155 : Blo 1680040 2520155 := bstep (se 1 (by rfl) ⟨1890116, by rfl⟩ : syracuseStep 2520155 = 3780233) B3780233
theorem B2520167 : Blo 1680040 2520167 := bstep (se 1 (by rfl) ⟨1890125, by rfl⟩ : syracuseStep 2520167 = 3780251) B3780251
theorem B6813179 : Blo 1680040 6813179 := bstep (se 1 (by rfl) ⟨5109884, by rfl⟩ : syracuseStep 6813179 = 10219769) B10219769
theorem B15341471 : Blo 1680040 15341471 := bstep (se 1 (by rfl) ⟨11506103, by rfl⟩ : syracuseStep 15341471 = 23012207) B23012207
theorem B6379631 : Blo 1680040 6379631 := bstep (se 1 (by rfl) ⟨4784723, by rfl⟩ : syracuseStep 6379631 = 9569447) B9569447
theorem B2521295 : Blo 1680040 2521295 := bstep (se 1 (by rfl) ⟨1890971, by rfl⟩ : syracuseStep 2521295 = 3781943) B3781943
theorem B2128123 : Blo 1680040 2128123 := bstep (se 1 (by rfl) ⟨1596092, by rfl⟩ : syracuseStep 2128123 = 3192185) B3192185
theorem B2521703 : Blo 1680040 2521703 := bstep (se 1 (by rfl) ⟨1891277, by rfl⟩ : syracuseStep 2521703 = 3782555) B3782555
theorem B12122783 : Blo 1680040 12122783 := bstep (se 1 (by rfl) ⟨9092087, by rfl⟩ : syracuseStep 12122783 = 18184175) B18184175
theorem B2521919 : Blo 1680040 2521919 := bstep (se 1 (by rfl) ⟨1891439, by rfl⟩ : syracuseStep 2521919 = 3782879) B3782879
theorem B39328685 : Blo 1680040 39328685 := bstep (se 3 (by rfl) ⟨7374128, by rfl⟩ : syracuseStep 39328685 = 14748257) B14748257
theorem B5610451 : Blo 1680040 5610451 := bstep (se 1 (by rfl) ⟨4207838, by rfl⟩ : syracuseStep 5610451 = 8415677) B8415677
theorem B2522591 : Blo 1680040 2522591 := bstep (se 1 (by rfl) ⟨1891943, by rfl⟩ : syracuseStep 2522591 = 3783887) B3783887
theorem B1891867 : Blo 1680040 1891867 := bstep (se 1 (by rfl) ⟨1418900, by rfl⟩ : syracuseStep 1891867 = 2837801) B2837801
theorem B6381287 : Blo 1680040 6381287 := bstep (se 1 (by rfl) ⟨4785965, by rfl⟩ : syracuseStep 6381287 = 9571931) B9571931
theorem B155287685 : Blo 1680040 155287685 := bstep (se 4 (by rfl) ⟨14558220, by rfl⟩ : syracuseStep 155287685 = 29116441) B29116441
theorem B12771593 : Blo 1680040 12771593 := bstep (se 2 (by rfl) ⟨4789347, by rfl⟩ : syracuseStep 12771593 = 9578695) B9578695
theorem B1794331 : Blo 1680040 1794331 := bstep (se 1 (by rfl) ⟨1345748, by rfl⟩ : syracuseStep 1794331 = 2691497) B2691497
theorem B9577055 : Blo 1680040 9577055 := bstep (se 1 (by rfl) ⟨7182791, by rfl⟩ : syracuseStep 9577055 = 14365583) B14365583
theorem B8512127 : Blo 1680040 8512127 := bstep (se 1 (by rfl) ⟨6384095, by rfl⟩ : syracuseStep 8512127 = 12768191) B12768191
theorem B1680103 : Blo 1680040 1680103 := bstep (se 1 (by rfl) ⟨1260077, by rfl⟩ : syracuseStep 1680103 = 2520155) B2520155
theorem B1680111 : Blo 1680040 1680111 := bstep (se 1 (by rfl) ⟨1260083, by rfl⟩ : syracuseStep 1680111 = 2520167) B2520167
theorem B137970449 : Blo 1680040 137970449 := bstep (se 2 (by rfl) ⟨51738918, by rfl⟩ : syracuseStep 137970449 = 103477837) B103477837
theorem B7480601 : Blo 1680040 7480601 := bstep (se 2 (by rfl) ⟨2805225, by rfl⟩ : syracuseStep 7480601 = 5610451) B5610451
theorem B4253087 : Blo 1680040 4253087 := bstep (se 1 (by rfl) ⟨3189815, by rfl⟩ : syracuseStep 4253087 = 6379631) B6379631
theorem B1680863 : Blo 1680040 1680863 := bstep (se 1 (by rfl) ⟨1260647, by rfl⟩ : syracuseStep 1680863 = 2521295) B2521295
theorem B1681135 : Blo 1680040 1681135 := bstep (se 1 (by rfl) ⟨1260851, by rfl⟩ : syracuseStep 1681135 = 2521703) B2521703
theorem B1681279 : Blo 1680040 1681279 := bstep (se 1 (by rfl) ⟨1260959, by rfl⟩ : syracuseStep 1681279 = 2521919) B2521919
theorem B1681727 : Blo 1680040 1681727 := bstep (se 1 (by rfl) ⟨1261295, by rfl⟩ : syracuseStep 1681727 = 2522591) B2522591
theorem B14354921 : Blo 1680040 14354921 := bstep (se 2 (by rfl) ⟨5383095, by rfl⟩ : syracuseStep 14354921 = 10766191) B10766191
theorem B4254191 : Blo 1680040 4254191 := bstep (se 1 (by rfl) ⟨3190643, by rfl⟩ : syracuseStep 4254191 = 6381287) B6381287
theorem B2837497 : Blo 1680040 2837497 := bstep (se 2 (by rfl) ⟨1064061, by rfl⟩ : syracuseStep 2837497 = 2128123) B2128123
theorem B6385007 : Blo 1680040 6385007 := bstep (se 1 (by rfl) ⟨4788755, by rfl⟩ : syracuseStep 6385007 = 9577511) B9577511
theorem B2076095 : Blo 1680040 2076095 := bstep (se 1 (by rfl) ⟨1557071, by rfl⟩ : syracuseStep 2076095 = 3114143) B3114143
theorem B4542119 : Blo 1680040 4542119 := bstep (se 1 (by rfl) ⟨3406589, by rfl⟩ : syracuseStep 4542119 = 6813179) B6813179
theorem B10227647 : Blo 1680040 10227647 := bstep (se 1 (by rfl) ⟨7670735, by rfl⟩ : syracuseStep 10227647 = 15341471) B15341471
theorem B7663859 : Blo 1680040 7663859 := bstep (se 1 (by rfl) ⟨5747894, by rfl⟩ : syracuseStep 7663859 = 11495789) B11495789
theorem B12120475 : Blo 1680040 12120475 := bstep (se 1 (by rfl) ⟨9090356, by rfl⟩ : syracuseStep 12120475 = 18180713) B18180713
theorem B8081855 : Blo 1680040 8081855 := bstep (se 1 (by rfl) ⟨6061391, by rfl⟩ : syracuseStep 8081855 = 12122783) B12122783
theorem B51737075 : Blo 1680040 51737075 := bstep (se 1 (by rfl) ⟨38802806, by rfl⟩ : syracuseStep 51737075 = 77605613) B77605613
theorem B21541403 : Blo 1680040 21541403 := bstep (se 1 (by rfl) ⟨16156052, by rfl⟩ : syracuseStep 21541403 = 32312105) B32312105
theorem B26219123 : Blo 1680040 26219123 := bstep (se 1 (by rfl) ⟨19664342, by rfl⟩ : syracuseStep 26219123 = 39328685) B39328685
theorem B4256975 : Blo 1680040 4256975 := bstep (se 1 (by rfl) ⟨3192731, by rfl⟩ : syracuseStep 4256975 = 6385463) B6385463
theorem B18429149 : Blo 1680040 18429149 := bstep (se 3 (by rfl) ⟨3455465, by rfl⟩ : syracuseStep 18429149 = 6910931) B6910931
theorem B5674265 : Blo 1680040 5674265 := bstep (se 2 (by rfl) ⟨2127849, by rfl⟩ : syracuseStep 5674265 = 4255699) B4255699
theorem B2127151 : Blo 1680040 2127151 := bstep (se 1 (by rfl) ⟨1595363, by rfl⟩ : syracuseStep 2127151 = 3190727) B3190727
theorem B3028295 : Blo 1680040 3028295 := bstep (se 1 (by rfl) ⟨2271221, by rfl⟩ : syracuseStep 3028295 = 4542443) B4542443
theorem B8508887 : Blo 1680040 8508887 := bstep (se 1 (by rfl) ⟨6381665, by rfl⟩ : syracuseStep 8508887 = 12763331) B12763331
theorem B2520683 : Blo 1680040 2520683 := bstep (se 1 (by rfl) ⟨1890512, by rfl⟩ : syracuseStep 2520683 = 3781025) B3781025
theorem B3782375 : Blo 1680040 3782375 := bstep (se 1 (by rfl) ⟨2836781, by rfl⟩ : syracuseStep 3782375 = 5673563) B5673563
theorem B2520935 : Blo 1680040 2520935 := bstep (se 1 (by rfl) ⟨1890701, by rfl⟩ : syracuseStep 2520935 = 3781403) B3781403
theorem B3782825 : Blo 1680040 3782825 := bstep (se 2 (by rfl) ⟨1418559, by rfl⟩ : syracuseStep 3782825 = 2837119) B2837119
theorem B472168721 : Blo 1680040 472168721 := bstep (se 2 (by rfl) ⟨177063270, by rfl⟩ : syracuseStep 472168721 = 354126541) B354126541
theorem B7182827 : Blo 1680040 7182827 := bstep (se 1 (by rfl) ⟨5387120, by rfl⟩ : syracuseStep 7182827 = 10774241) B10774241
theorem B6380329 : Blo 1680040 6380329 := bstep (se 2 (by rfl) ⟨2392623, by rfl⟩ : syracuseStep 6380329 = 4785247) B4785247
theorem B3783689 : Blo 1680040 3783689 := bstep (se 2 (by rfl) ⟨1418883, by rfl⟩ : syracuseStep 3783689 = 2837767) B2837767
theorem B5676371 : Blo 1680040 5676371 := bstep (se 1 (by rfl) ⟨4257278, by rfl⟩ : syracuseStep 5676371 = 8514557) B8514557
theorem B2522489 : Blo 1680040 2522489 := bstep (se 2 (by rfl) ⟨945933, by rfl⟩ : syracuseStep 2522489 = 1891867) B1891867
theorem B63020591 : Blo 1680040 63020591 := bstep (se 1 (by rfl) ⟨47265443, by rfl⟩ : syracuseStep 63020591 = 94530887) B94530887
theorem B15326873 : Blo 1680040 15326873 := bstep (se 2 (by rfl) ⟨5747577, by rfl⟩ : syracuseStep 15326873 = 11495155) B11495155
theorem B14360935 : Blo 1680040 14360935 := bstep (se 1 (by rfl) ⟨10770701, by rfl⟩ : syracuseStep 14360935 = 21541403) B21541403
theorem B91980299 : Blo 1680040 91980299 := bstep (se 1 (by rfl) ⟨68985224, by rfl⟩ : syracuseStep 91980299 = 137970449) B137970449
theorem B2835391 : Blo 1680040 2835391 := bstep (se 1 (by rfl) ⟨2126543, by rfl⟩ : syracuseStep 2835391 = 4253087) B4253087
theorem B1680455 : Blo 1680040 1680455 := bstep (se 1 (by rfl) ⟨1260341, by rfl⟩ : syracuseStep 1680455 = 2520683) B2520683
theorem B1680623 : Blo 1680040 1680623 := bstep (se 1 (by rfl) ⟨1260467, by rfl⟩ : syracuseStep 1680623 = 2520935) B2520935
theorem B9569765 : Blo 1680040 9569765 := bstep (se 4 (by rfl) ⟨897165, by rfl⟩ : syracuseStep 9569765 = 1794331) B1794331
theorem B9569947 : Blo 1680040 9569947 := bstep (se 1 (by rfl) ⟨7177460, by rfl⟩ : syracuseStep 9569947 = 14354921) B14354921
theorem B2836127 : Blo 1680040 2836127 := bstep (se 1 (by rfl) ⟨2127095, by rfl⟩ : syracuseStep 2836127 = 4254191) B4254191
theorem B2836201 : Blo 1680040 2836201 := bstep (se 2 (by rfl) ⟨1063575, by rfl⟩ : syracuseStep 2836201 = 2127151) B2127151
theorem B1681659 : Blo 1680040 1681659 := bstep (se 1 (by rfl) ⟨1261244, by rfl⟩ : syracuseStep 1681659 = 2522489) B2522489
theorem B10217915 : Blo 1680040 10217915 := bstep (se 1 (by rfl) ⟨7663436, by rfl⟩ : syracuseStep 10217915 = 15326873) B15326873
theorem B6818431 : Blo 1680040 6818431 := bstep (se 1 (by rfl) ⟨5113823, by rfl⟩ : syracuseStep 6818431 = 10227647) B10227647
theorem B103525123 : Blo 1680040 103525123 := bstep (se 1 (by rfl) ⟨77643842, by rfl⟩ : syracuseStep 103525123 = 155287685) B155287685
theorem B8514395 : Blo 1680040 8514395 := bstep (se 1 (by rfl) ⟨6385796, by rfl⟩ : syracuseStep 8514395 = 12771593) B12771593
theorem B34491383 : Blo 1680040 34491383 := bstep (se 1 (by rfl) ⟨25868537, by rfl⟩ : syracuseStep 34491383 = 51737075) B51737075
theorem B6384703 : Blo 1680040 6384703 := bstep (se 1 (by rfl) ⟨4788527, by rfl⟩ : syracuseStep 6384703 = 9577055) B9577055
theorem B2837983 : Blo 1680040 2837983 := bstep (se 1 (by rfl) ⟨2128487, by rfl⟩ : syracuseStep 2837983 = 4256975) B4256975
theorem B2018863 : Blo 1680040 2018863 := bstep (se 1 (by rfl) ⟨1514147, by rfl⟩ : syracuseStep 2018863 = 3028295) B3028295
theorem B5672591 : Blo 1680040 5672591 := bstep (se 1 (by rfl) ⟨4254443, by rfl⟩ : syracuseStep 5672591 = 8508887) B8508887
theorem B8507105 : Blo 1680040 8507105 := bstep (se 2 (by rfl) ⟨3190164, by rfl⟩ : syracuseStep 8507105 = 6380329) B6380329
theorem B4788551 : Blo 1680040 4788551 := bstep (se 1 (by rfl) ⟨3591413, by rfl⟩ : syracuseStep 4788551 = 7182827) B7182827
theorem B4256671 : Blo 1680040 4256671 := bstep (se 1 (by rfl) ⟨3192503, by rfl⟩ : syracuseStep 4256671 = 6385007) B6385007
theorem B42013727 : Blo 1680040 42013727 := bstep (se 1 (by rfl) ⟨31510295, by rfl⟩ : syracuseStep 42013727 = 63020591) B63020591
theorem B3028079 : Blo 1680040 3028079 := bstep (se 1 (by rfl) ⟨2271059, by rfl⟩ : syracuseStep 3028079 = 4542119) B4542119
theorem B5109239 : Blo 1680040 5109239 := bstep (se 1 (by rfl) ⟨3831929, by rfl⟩ : syracuseStep 5109239 = 7663859) B7663859
theorem B5387903 : Blo 1680040 5387903 := bstep (se 1 (by rfl) ⟨4040927, by rfl⟩ : syracuseStep 5387903 = 8081855) B8081855
theorem B17479415 : Blo 1680040 17479415 := bstep (se 1 (by rfl) ⟨13109561, by rfl⟩ : syracuseStep 17479415 = 26219123) B26219123
theorem B5674751 : Blo 1680040 5674751 := bstep (se 1 (by rfl) ⟨4256063, by rfl⟩ : syracuseStep 5674751 = 8512127) B8512127
theorem B16160633 : Blo 1680040 16160633 := bstep (se 2 (by rfl) ⟨6060237, by rfl⟩ : syracuseStep 16160633 = 12120475) B12120475
theorem B1259116589 : Blo 1680040 1259116589 := bstep (se 3 (by rfl) ⟨236084360, by rfl⟩ : syracuseStep 1259116589 = 472168721) B472168721
theorem B12286099 : Blo 1680040 12286099 := bstep (se 1 (by rfl) ⟨9214574, by rfl⟩ : syracuseStep 12286099 = 18429149) B18429149
theorem B3782843 : Blo 1680040 3782843 := bstep (se 1 (by rfl) ⟨2837132, by rfl⟩ : syracuseStep 3782843 = 5674265) B5674265
theorem B4987067 : Blo 1680040 4987067 := bstep (se 1 (by rfl) ⟨3740300, by rfl⟩ : syracuseStep 4987067 = 7480601) B7480601
theorem B2521583 : Blo 1680040 2521583 := bstep (se 1 (by rfl) ⟨1891187, by rfl⟩ : syracuseStep 2521583 = 3782375) B3782375
theorem B5536253 : Blo 1680040 5536253 := bstep (se 3 (by rfl) ⟨1038047, by rfl⟩ : syracuseStep 5536253 = 2076095) B2076095
theorem B3783329 : Blo 1680040 3783329 := bstep (se 2 (by rfl) ⟨1418748, by rfl⟩ : syracuseStep 3783329 = 2837497) B2837497
theorem B2521883 : Blo 1680040 2521883 := bstep (se 1 (by rfl) ⟨1891412, by rfl⟩ : syracuseStep 2521883 = 3782825) B3782825
theorem B2522459 : Blo 1680040 2522459 := bstep (se 1 (by rfl) ⟨1891844, by rfl⟩ : syracuseStep 2522459 = 3783689) B3783689
theorem B3784247 : Blo 1680040 3784247 := bstep (se 1 (by rfl) ⟨2838185, by rfl⟩ : syracuseStep 3784247 = 5676371) B5676371
theorem B28009151 : Blo 1680040 28009151 := bstep (se 1 (by rfl) ⟨21006863, by rfl⟩ : syracuseStep 28009151 = 42013727) B42013727
theorem B10773755 : Blo 1680040 10773755 := bstep (se 1 (by rfl) ⟨8080316, by rfl⟩ : syracuseStep 10773755 = 16160633) B16160633
theorem B839411059 : Blo 1680040 839411059 := bstep (se 1 (by rfl) ⟨629558294, by rfl⟩ : syracuseStep 839411059 = 1259116589) B1259116589
theorem B8512937 : Blo 1680040 8512937 := bstep (se 2 (by rfl) ⟨3192351, by rfl⟩ : syracuseStep 8512937 = 6384703) B6384703
theorem B1681055 : Blo 1680040 1681055 := bstep (se 1 (by rfl) ⟨1260791, by rfl⟩ : syracuseStep 1681055 = 2521583) B2521583
theorem B1681255 : Blo 1680040 1681255 := bstep (se 1 (by rfl) ⟨1260941, by rfl⟩ : syracuseStep 1681255 = 2521883) B2521883
theorem B1681639 : Blo 1680040 1681639 := bstep (se 1 (by rfl) ⟨1261229, by rfl⟩ : syracuseStep 1681639 = 2522459) B2522459
theorem B5671403 : Blo 1680040 5671403 := bstep (se 1 (by rfl) ⟨4253552, by rfl⟩ : syracuseStep 5671403 = 8507105) B8507105
theorem B10767269 : Blo 1680040 10767269 := bstep (se 4 (by rfl) ⟨1009431, by rfl⟩ : syracuseStep 10767269 = 2018863) B2018863
theorem B61320199 : Blo 1680040 61320199 := bstep (se 1 (by rfl) ⟨45990149, by rfl⟩ : syracuseStep 61320199 = 91980299) B91980299
theorem B19147913 : Blo 1680040 19147913 := bstep (se 2 (by rfl) ⟨7180467, by rfl⟩ : syracuseStep 19147913 = 14360935) B14360935
theorem B2018719 : Blo 1680040 2018719 := bstep (se 1 (by rfl) ⟨1514039, by rfl⟩ : syracuseStep 2018719 = 3028079) B3028079
theorem B3591935 : Blo 1680040 3591935 := bstep (se 1 (by rfl) ⟨2693951, by rfl⟩ : syracuseStep 3591935 = 5387903) B5387903
theorem B3780521 : Blo 1680040 3780521 := bstep (se 2 (by rfl) ⟨1417695, by rfl⟩ : syracuseStep 3780521 = 2835391) B2835391
theorem B6811943 : Blo 1680040 6811943 := bstep (se 1 (by rfl) ⟨5108957, by rfl⟩ : syracuseStep 6811943 = 10217915) B10217915
theorem B3690835 : Blo 1680040 3690835 := bstep (se 1 (by rfl) ⟨2768126, by rfl⟩ : syracuseStep 3690835 = 5536253) B5536253
theorem B53195381 : Blo 1680040 53195381 := bstep (se 5 (by rfl) ⟨2493533, by rfl⟩ : syracuseStep 53195381 = 4987067) B4987067
theorem B12759929 : Blo 1680040 12759929 := bstep (se 2 (by rfl) ⟨4784973, by rfl⟩ : syracuseStep 12759929 = 9569947) B9569947
theorem B3781601 : Blo 1680040 3781601 := bstep (se 2 (by rfl) ⟨1418100, by rfl⟩ : syracuseStep 3781601 = 2836201) B2836201
theorem B3781727 : Blo 1680040 3781727 := bstep (se 1 (by rfl) ⟨2836295, by rfl⟩ : syracuseStep 3781727 = 5672591) B5672591
theorem B3192367 : Blo 1680040 3192367 := bstep (se 1 (by rfl) ⟨2394275, by rfl⟩ : syracuseStep 3192367 = 4788551) B4788551
theorem B65525861 : Blo 1680040 65525861 := bstep (se 4 (by rfl) ⟨6143049, by rfl⟩ : syracuseStep 65525861 = 12286099) B12286099
theorem B9091241 : Blo 1680040 9091241 := bstep (se 2 (by rfl) ⟨3409215, by rfl⟩ : syracuseStep 9091241 = 6818431) B6818431
theorem B6379843 : Blo 1680040 6379843 := bstep (se 1 (by rfl) ⟨4784882, by rfl⟩ : syracuseStep 6379843 = 9569765) B9569765
theorem B3406159 : Blo 1680040 3406159 := bstep (se 1 (by rfl) ⟨2554619, by rfl⟩ : syracuseStep 3406159 = 5109239) B5109239
theorem B138033497 : Blo 1680040 138033497 := bstep (se 2 (by rfl) ⟨51762561, by rfl⟩ : syracuseStep 138033497 = 103525123) B103525123
theorem B1890751 : Blo 1680040 1890751 := bstep (se 1 (by rfl) ⟨1418063, by rfl⟩ : syracuseStep 1890751 = 2836127) B2836127
theorem B3783167 : Blo 1680040 3783167 := bstep (se 1 (by rfl) ⟨2837375, by rfl⟩ : syracuseStep 3783167 = 5674751) B5674751
theorem B5675561 : Blo 1680040 5675561 := bstep (se 2 (by rfl) ⟨2128335, by rfl⟩ : syracuseStep 5675561 = 4256671) B4256671
theorem B2521895 : Blo 1680040 2521895 := bstep (se 1 (by rfl) ⟨1891421, by rfl⟩ : syracuseStep 2521895 = 3782843) B3782843
theorem B2522219 : Blo 1680040 2522219 := bstep (se 1 (by rfl) ⟨1891664, by rfl⟩ : syracuseStep 2522219 = 3783329) B3783329
theorem B5676263 : Blo 1680040 5676263 := bstep (se 1 (by rfl) ⟨4257197, by rfl⟩ : syracuseStep 5676263 = 8514395) B8514395
theorem B3783977 : Blo 1680040 3783977 := bstep (se 2 (by rfl) ⟨1418991, by rfl⟩ : syracuseStep 3783977 = 2837983) B2837983
theorem B46611773 : Blo 1680040 46611773 := bstep (se 3 (by rfl) ⟨8739707, by rfl⟩ : syracuseStep 46611773 = 17479415) B17479415
theorem B22994255 : Blo 1680040 22994255 := bstep (se 1 (by rfl) ⟨17245691, by rfl⟩ : syracuseStep 22994255 = 34491383) B34491383
theorem B2522831 : Blo 1680040 2522831 := bstep (se 1 (by rfl) ⟨1892123, by rfl⟩ : syracuseStep 2522831 = 3784247) B3784247
theorem B174735629 : Blo 1680040 174735629 := bstep (se 3 (by rfl) ⟨32762930, by rfl⟩ : syracuseStep 174735629 = 65525861) B65525861
theorem B35463587 : Blo 1680040 35463587 := bstep (se 1 (by rfl) ⟨26597690, by rfl⟩ : syracuseStep 35463587 = 53195381) B53195381
theorem B92022331 : Blo 1680040 92022331 := bstep (se 1 (by rfl) ⟨69016748, by rfl⟩ : syracuseStep 92022331 = 138033497) B138033497
theorem B1681263 : Blo 1680040 1681263 := bstep (se 1 (by rfl) ⟨1260947, by rfl⟩ : syracuseStep 1681263 = 2521895) B2521895
theorem B7178179 : Blo 1680040 7178179 := bstep (se 1 (by rfl) ⟨5383634, by rfl⟩ : syracuseStep 7178179 = 10767269) B10767269
theorem B1681479 : Blo 1680040 1681479 := bstep (se 1 (by rfl) ⟨1261109, by rfl⟩ : syracuseStep 1681479 = 2522219) B2522219
theorem B12765275 : Blo 1680040 12765275 := bstep (se 1 (by rfl) ⟨9573956, by rfl⟩ : syracuseStep 12765275 = 19147913) B19147913
theorem B31074515 : Blo 1680040 31074515 := bstep (se 1 (by rfl) ⟨23305886, by rfl⟩ : syracuseStep 31074515 = 46611773) B46611773
theorem B15329503 : Blo 1680040 15329503 := bstep (se 1 (by rfl) ⟨11497127, by rfl⟩ : syracuseStep 15329503 = 22994255) B22994255
theorem B1681887 : Blo 1680040 1681887 := bstep (se 1 (by rfl) ⟨1261415, by rfl⟩ : syracuseStep 1681887 = 2522831) B2522831
theorem B2394623 : Blo 1680040 2394623 := bstep (se 1 (by rfl) ⟨1795967, by rfl⟩ : syracuseStep 2394623 = 3591935) B3591935
theorem B8506457 : Blo 1680040 8506457 := bstep (se 2 (by rfl) ⟨3189921, by rfl⟩ : syracuseStep 8506457 = 6379843) B6379843
theorem B4541545 : Blo 1680040 4541545 := bstep (se 2 (by rfl) ⟨1703079, by rfl⟩ : syracuseStep 4541545 = 3406159) B3406159
theorem B18672767 : Blo 1680040 18672767 := bstep (se 1 (by rfl) ⟨14004575, by rfl⟩ : syracuseStep 18672767 = 28009151) B28009151
theorem B8506619 : Blo 1680040 8506619 := bstep (se 1 (by rfl) ⟨6379964, by rfl⟩ : syracuseStep 8506619 = 12759929) B12759929
theorem B18165181 : Blo 1680040 18165181 := bstep (se 3 (by rfl) ⟨3405971, by rfl⟩ : syracuseStep 18165181 = 6811943) B6811943
theorem B81760265 : Blo 1680040 81760265 := bstep (se 2 (by rfl) ⟨30660099, by rfl⟩ : syracuseStep 81760265 = 61320199) B61320199
theorem B3780935 : Blo 1680040 3780935 := bstep (se 1 (by rfl) ⟨2835701, by rfl⟩ : syracuseStep 3780935 = 5671403) B5671403
theorem B2691625 : Blo 1680040 2691625 := bstep (se 2 (by rfl) ⟨1009359, by rfl⟩ : syracuseStep 2691625 = 2018719) B2018719
theorem B4256489 : Blo 1680040 4256489 := bstep (se 2 (by rfl) ⟨1596183, by rfl⟩ : syracuseStep 4256489 = 3192367) B3192367
theorem B2520347 : Blo 1680040 2520347 := bstep (se 1 (by rfl) ⟨1890260, by rfl⟩ : syracuseStep 2520347 = 3780521) B3780521
theorem B2521001 : Blo 1680040 2521001 := bstep (se 2 (by rfl) ⟨945375, by rfl⟩ : syracuseStep 2521001 = 1890751) B1890751
theorem B2521067 : Blo 1680040 2521067 := bstep (se 1 (by rfl) ⟨1890800, by rfl⟩ : syracuseStep 2521067 = 3781601) B3781601
theorem B2521151 : Blo 1680040 2521151 := bstep (se 1 (by rfl) ⟨1890863, by rfl⟩ : syracuseStep 2521151 = 3781727) B3781727
theorem B7182503 : Blo 1680040 7182503 := bstep (se 1 (by rfl) ⟨5386877, by rfl⟩ : syracuseStep 7182503 = 10773755) B10773755
theorem B5675291 : Blo 1680040 5675291 := bstep (se 1 (by rfl) ⟨4256468, by rfl⟩ : syracuseStep 5675291 = 8512937) B8512937
theorem B6060827 : Blo 1680040 6060827 := bstep (se 1 (by rfl) ⟨4545620, by rfl⟩ : syracuseStep 6060827 = 9091241) B9091241
theorem B2522111 : Blo 1680040 2522111 := bstep (se 1 (by rfl) ⟨1891583, by rfl⟩ : syracuseStep 2522111 = 3783167) B3783167
theorem B3783707 : Blo 1680040 3783707 := bstep (se 1 (by rfl) ⟨2837780, by rfl⟩ : syracuseStep 3783707 = 5675561) B5675561
theorem B19684453 : Blo 1680040 19684453 := bstep (se 4 (by rfl) ⟨1845417, by rfl⟩ : syracuseStep 19684453 = 3690835) B3690835
theorem B1119214745 : Blo 1680040 1119214745 := bstep (se 2 (by rfl) ⟨419705529, by rfl⟩ : syracuseStep 1119214745 = 839411059) B839411059
theorem B3784175 : Blo 1680040 3784175 := bstep (se 1 (by rfl) ⟨2838131, by rfl⟩ : syracuseStep 3784175 = 5676263) B5676263
theorem B2522651 : Blo 1680040 2522651 := bstep (se 1 (by rfl) ⟨1891988, by rfl⟩ : syracuseStep 2522651 = 3783977) B3783977
theorem B116490419 : Blo 1680040 116490419 := bstep (se 1 (by rfl) ⟨87367814, by rfl⟩ : syracuseStep 116490419 = 174735629) B174735629
theorem B20439337 : Blo 1680040 20439337 := bstep (se 2 (by rfl) ⟨7664751, by rfl⟩ : syracuseStep 20439337 = 15329503) B15329503
theorem B3588833 : Blo 1680040 3588833 := bstep (se 2 (by rfl) ⟨1345812, by rfl⟩ : syracuseStep 3588833 = 2691625) B2691625
theorem B1680231 : Blo 1680040 1680231 := bstep (se 1 (by rfl) ⟨1260173, by rfl⟩ : syracuseStep 1680231 = 2520347) B2520347
theorem B1680667 : Blo 1680040 1680667 := bstep (se 1 (by rfl) ⟨1260500, by rfl⟩ : syracuseStep 1680667 = 2521001) B2521001
theorem B1680711 : Blo 1680040 1680711 := bstep (se 1 (by rfl) ⟨1260533, by rfl⟩ : syracuseStep 1680711 = 2521067) B2521067
theorem B1680767 : Blo 1680040 1680767 := bstep (se 1 (by rfl) ⟨1260575, by rfl⟩ : syracuseStep 1680767 = 2521151) B2521151
theorem B6055393 : Blo 1680040 6055393 := bstep (se 2 (by rfl) ⟨2270772, by rfl⟩ : syracuseStep 6055393 = 4541545) B4541545
theorem B4040551 : Blo 1680040 4040551 := bstep (se 1 (by rfl) ⟨3030413, by rfl⟩ : syracuseStep 4040551 = 6060827) B6060827
theorem B1681407 : Blo 1680040 1681407 := bstep (se 1 (by rfl) ⟨1261055, by rfl⟩ : syracuseStep 1681407 = 2522111) B2522111
theorem B5670971 : Blo 1680040 5670971 := bstep (se 1 (by rfl) ⟨4253228, by rfl⟩ : syracuseStep 5670971 = 8506457) B8506457
theorem B5671079 : Blo 1680040 5671079 := bstep (se 1 (by rfl) ⟨4253309, by rfl⟩ : syracuseStep 5671079 = 8506619) B8506619
theorem B1681767 : Blo 1680040 1681767 := bstep (se 1 (by rfl) ⟨1261325, by rfl⟩ : syracuseStep 1681767 = 2522651) B2522651
theorem B9570905 : Blo 1680040 9570905 := bstep (se 2 (by rfl) ⟨3589089, by rfl⟩ : syracuseStep 9570905 = 7178179) B7178179
theorem B2837659 : Blo 1680040 2837659 := bstep (se 1 (by rfl) ⟨2128244, by rfl⟩ : syracuseStep 2837659 = 4256489) B4256489
theorem B6385661 : Blo 1680040 6385661 := bstep (se 3 (by rfl) ⟨1197311, by rfl⟩ : syracuseStep 6385661 = 2394623) B2394623
theorem B4788335 : Blo 1680040 4788335 := bstep (se 1 (by rfl) ⟨3591251, by rfl⟩ : syracuseStep 4788335 = 7182503) B7182503
theorem B378278261 : Blo 1680040 378278261 := bstep (se 5 (by rfl) ⟨17731793, by rfl⟩ : syracuseStep 378278261 = 35463587) B35463587
theorem B24220241 : Blo 1680040 24220241 := bstep (se 2 (by rfl) ⟨9082590, by rfl⟩ : syracuseStep 24220241 = 18165181) B18165181
theorem B122696441 : Blo 1680040 122696441 := bstep (se 2 (by rfl) ⟨46011165, by rfl⟩ : syracuseStep 122696441 = 92022331) B92022331
theorem B12448511 : Blo 1680040 12448511 := bstep (se 1 (by rfl) ⟨9336383, by rfl⟩ : syracuseStep 12448511 = 18672767) B18672767
theorem B54506843 : Blo 1680040 54506843 := bstep (se 1 (by rfl) ⟨40880132, by rfl⟩ : syracuseStep 54506843 = 81760265) B81760265
theorem B2520623 : Blo 1680040 2520623 := bstep (se 1 (by rfl) ⟨1890467, by rfl⟩ : syracuseStep 2520623 = 3780935) B3780935
theorem B8510183 : Blo 1680040 8510183 := bstep (se 1 (by rfl) ⟨6382637, by rfl⟩ : syracuseStep 8510183 = 12765275) B12765275
theorem B26245937 : Blo 1680040 26245937 := bstep (se 2 (by rfl) ⟨9842226, by rfl⟩ : syracuseStep 26245937 = 19684453) B19684453
theorem B20716343 : Blo 1680040 20716343 := bstep (se 1 (by rfl) ⟨15537257, by rfl⟩ : syracuseStep 20716343 = 31074515) B31074515
theorem B3783527 : Blo 1680040 3783527 := bstep (se 1 (by rfl) ⟨2837645, by rfl⟩ : syracuseStep 3783527 = 5675291) B5675291
theorem B2522471 : Blo 1680040 2522471 := bstep (se 1 (by rfl) ⟨1891853, by rfl⟩ : syracuseStep 2522471 = 3783707) B3783707
theorem B746143163 : Blo 1680040 746143163 := bstep (se 1 (by rfl) ⟨559607372, by rfl⟩ : syracuseStep 746143163 = 1119214745) B1119214745
theorem B2522783 : Blo 1680040 2522783 := bstep (se 1 (by rfl) ⟨1892087, by rfl⟩ : syracuseStep 2522783 = 3784175) B3784175
theorem B77660279 : Blo 1680040 77660279 := bstep (se 1 (by rfl) ⟨58245209, by rfl⟩ : syracuseStep 77660279 = 116490419) B116490419
theorem B16146827 : Blo 1680040 16146827 := bstep (se 1 (by rfl) ⟨12110120, by rfl⟩ : syracuseStep 16146827 = 24220241) B24220241
theorem B81797627 : Blo 1680040 81797627 := bstep (se 1 (by rfl) ⟨61348220, by rfl⟩ : syracuseStep 81797627 = 122696441) B122696441
theorem B8299007 : Blo 1680040 8299007 := bstep (se 1 (by rfl) ⟨6224255, by rfl⟩ : syracuseStep 8299007 = 12448511) B12448511
theorem B1680415 : Blo 1680040 1680415 := bstep (se 1 (by rfl) ⟨1260311, by rfl⟩ : syracuseStep 1680415 = 2520623) B2520623
theorem B9570221 : Blo 1680040 9570221 := bstep (se 3 (by rfl) ⟨1794416, by rfl⟩ : syracuseStep 9570221 = 3588833) B3588833
theorem B1681647 : Blo 1680040 1681647 := bstep (se 1 (by rfl) ⟨1261235, by rfl⟩ : syracuseStep 1681647 = 2522471) B2522471
theorem B497428775 : Blo 1680040 497428775 := bstep (se 1 (by rfl) ⟨373071581, by rfl⟩ : syracuseStep 497428775 = 746143163) B746143163
theorem B1681855 : Blo 1680040 1681855 := bstep (se 1 (by rfl) ⟨1261391, by rfl⟩ : syracuseStep 1681855 = 2522783) B2522783
theorem B252185507 : Blo 1680040 252185507 := bstep (se 1 (by rfl) ⟨189139130, by rfl⟩ : syracuseStep 252185507 = 378278261) B378278261
theorem B3780647 : Blo 1680040 3780647 := bstep (se 1 (by rfl) ⟨2835485, by rfl⟩ : syracuseStep 3780647 = 5670971) B5670971
theorem B3780719 : Blo 1680040 3780719 := bstep (se 1 (by rfl) ⟨2835539, by rfl⟩ : syracuseStep 3780719 = 5671079) B5671079
theorem B5673455 : Blo 1680040 5673455 := bstep (se 1 (by rfl) ⟨4255091, by rfl⟩ : syracuseStep 5673455 = 8510183) B8510183
theorem B8073857 : Blo 1680040 8073857 := bstep (se 2 (by rfl) ⟨3027696, by rfl⟩ : syracuseStep 8073857 = 6055393) B6055393
theorem B5387401 : Blo 1680040 5387401 := bstep (se 2 (by rfl) ⟨2020275, by rfl⟩ : syracuseStep 5387401 = 4040551) B4040551
theorem B4257107 : Blo 1680040 4257107 := bstep (se 1 (by rfl) ⟨3192830, by rfl⟩ : syracuseStep 4257107 = 6385661) B6385661
theorem B3192223 : Blo 1680040 3192223 := bstep (se 1 (by rfl) ⟨2394167, by rfl⟩ : syracuseStep 3192223 = 4788335) B4788335
theorem B27252449 : Blo 1680040 27252449 := bstep (se 2 (by rfl) ⟨10219668, by rfl⟩ : syracuseStep 27252449 = 20439337) B20439337
theorem B36337895 : Blo 1680040 36337895 := bstep (se 1 (by rfl) ⟨27253421, by rfl⟩ : syracuseStep 36337895 = 54506843) B54506843
theorem B3783545 : Blo 1680040 3783545 := bstep (se 2 (by rfl) ⟨1418829, by rfl⟩ : syracuseStep 3783545 = 2837659) B2837659
theorem B6380603 : Blo 1680040 6380603 := bstep (se 1 (by rfl) ⟨4785452, by rfl⟩ : syracuseStep 6380603 = 9570905) B9570905
theorem B17497291 : Blo 1680040 17497291 := bstep (se 1 (by rfl) ⟨13122968, by rfl⟩ : syracuseStep 17497291 = 26245937) B26245937
theorem B13810895 : Blo 1680040 13810895 := bstep (se 1 (by rfl) ⟨10358171, by rfl⟩ : syracuseStep 13810895 = 20716343) B20716343
theorem B2522351 : Blo 1680040 2522351 := bstep (se 1 (by rfl) ⟨1891763, by rfl⟩ : syracuseStep 2522351 = 3783527) B3783527
theorem B51773519 : Blo 1680040 51773519 := bstep (se 1 (by rfl) ⟨38830139, by rfl⟩ : syracuseStep 51773519 = 77660279) B77660279
theorem B10764551 : Blo 1680040 10764551 := bstep (se 1 (by rfl) ⟨8073413, by rfl⟩ : syracuseStep 10764551 = 16146827) B16146827
theorem B24225263 : Blo 1680040 24225263 := bstep (se 1 (by rfl) ⟨18168947, by rfl⟩ : syracuseStep 24225263 = 36337895) B36337895
theorem B21530285 : Blo 1680040 21530285 := bstep (se 3 (by rfl) ⟨4036928, by rfl⟩ : syracuseStep 21530285 = 8073857) B8073857
theorem B4253735 : Blo 1680040 4253735 := bstep (se 1 (by rfl) ⟨3190301, by rfl⟩ : syracuseStep 4253735 = 6380603) B6380603
theorem B1681567 : Blo 1680040 1681567 := bstep (se 1 (by rfl) ⟨1261175, by rfl⟩ : syracuseStep 1681567 = 2522351) B2522351
theorem B5532671 : Blo 1680040 5532671 := bstep (se 1 (by rfl) ⟨4149503, by rfl⟩ : syracuseStep 5532671 = 8299007) B8299007
theorem B28732805 : Blo 1680040 28732805 := bstep (se 4 (by rfl) ⟨2693700, by rfl⟩ : syracuseStep 28732805 = 5387401) B5387401
theorem B2838071 : Blo 1680040 2838071 := bstep (se 1 (by rfl) ⟨2128553, by rfl⟩ : syracuseStep 2838071 = 4257107) B4257107
theorem B4256297 : Blo 1680040 4256297 := bstep (se 2 (by rfl) ⟨1596111, by rfl⟩ : syracuseStep 4256297 = 3192223) B3192223
theorem B2520431 : Blo 1680040 2520431 := bstep (se 1 (by rfl) ⟨1890323, by rfl⟩ : syracuseStep 2520431 = 3780647) B3780647
theorem B2520479 : Blo 1680040 2520479 := bstep (se 1 (by rfl) ⟨1890359, by rfl⟩ : syracuseStep 2520479 = 3780719) B3780719
theorem B3782303 : Blo 1680040 3782303 := bstep (se 1 (by rfl) ⟨2836727, by rfl⟩ : syracuseStep 3782303 = 5673455) B5673455
theorem B54531751 : Blo 1680040 54531751 := bstep (se 1 (by rfl) ⟨40898813, by rfl⟩ : syracuseStep 54531751 = 81797627) B81797627
theorem B18168299 : Blo 1680040 18168299 := bstep (se 1 (by rfl) ⟨13626224, by rfl⟩ : syracuseStep 18168299 = 27252449) B27252449
theorem B6380147 : Blo 1680040 6380147 := bstep (se 1 (by rfl) ⟨4785110, by rfl⟩ : syracuseStep 6380147 = 9570221) B9570221
theorem B331619183 : Blo 1680040 331619183 := bstep (se 1 (by rfl) ⟨248714387, by rfl⟩ : syracuseStep 331619183 = 497428775) B497428775
theorem B23329721 : Blo 1680040 23329721 := bstep (se 2 (by rfl) ⟨8748645, by rfl⟩ : syracuseStep 23329721 = 17497291) B17497291
theorem B2522363 : Blo 1680040 2522363 := bstep (se 1 (by rfl) ⟨1891772, by rfl⟩ : syracuseStep 2522363 = 3783545) B3783545
theorem B168123671 : Blo 1680040 168123671 := bstep (se 1 (by rfl) ⟨126092753, by rfl⟩ : syracuseStep 168123671 = 252185507) B252185507
theorem B9207263 : Blo 1680040 9207263 := bstep (se 1 (by rfl) ⟨6905447, by rfl⟩ : syracuseStep 9207263 = 13810895) B13810895
theorem B7176367 : Blo 1680040 7176367 := bstep (se 1 (by rfl) ⟨5382275, by rfl⟩ : syracuseStep 7176367 = 10764551) B10764551
theorem B1680287 : Blo 1680040 1680287 := bstep (se 1 (by rfl) ⟨1260215, by rfl⟩ : syracuseStep 1680287 = 2520431) B2520431
theorem B1680319 : Blo 1680040 1680319 := bstep (se 1 (by rfl) ⟨1260239, by rfl⟩ : syracuseStep 1680319 = 2520479) B2520479
theorem B14353523 : Blo 1680040 14353523 := bstep (se 1 (by rfl) ⟨10765142, by rfl⟩ : syracuseStep 14353523 = 21530285) B21530285
theorem B2835823 : Blo 1680040 2835823 := bstep (se 1 (by rfl) ⟨2126867, by rfl⟩ : syracuseStep 2835823 = 4253735) B4253735
theorem B4253431 : Blo 1680040 4253431 := bstep (se 1 (by rfl) ⟨3190073, by rfl⟩ : syracuseStep 4253431 = 6380147) B6380147
theorem B221079455 : Blo 1680040 221079455 := bstep (se 1 (by rfl) ⟨165809591, by rfl⟩ : syracuseStep 221079455 = 331619183) B331619183
theorem B3688447 : Blo 1680040 3688447 := bstep (se 1 (by rfl) ⟨2766335, by rfl⟩ : syracuseStep 3688447 = 5532671) B5532671
theorem B1681575 : Blo 1680040 1681575 := bstep (se 1 (by rfl) ⟨1261181, by rfl⟩ : syracuseStep 1681575 = 2522363) B2522363
theorem B19155203 : Blo 1680040 19155203 := bstep (se 1 (by rfl) ⟨14366402, by rfl⟩ : syracuseStep 19155203 = 28732805) B28732805
theorem B6138175 : Blo 1680040 6138175 := bstep (se 1 (by rfl) ⟨4603631, by rfl⟩ : syracuseStep 6138175 = 9207263) B9207263
theorem B34515679 : Blo 1680040 34515679 := bstep (se 1 (by rfl) ⟨25886759, by rfl⟩ : syracuseStep 34515679 = 51773519) B51773519
theorem B2837531 : Blo 1680040 2837531 := bstep (se 1 (by rfl) ⟨2128148, by rfl⟩ : syracuseStep 2837531 = 4256297) B4256297
theorem B16150175 : Blo 1680040 16150175 := bstep (se 1 (by rfl) ⟨12112631, by rfl⟩ : syracuseStep 16150175 = 24225263) B24225263
theorem B12112199 : Blo 1680040 12112199 := bstep (se 1 (by rfl) ⟨9084149, by rfl⟩ : syracuseStep 12112199 = 18168299) B18168299
theorem B15553147 : Blo 1680040 15553147 := bstep (se 1 (by rfl) ⟨11664860, by rfl⟩ : syracuseStep 15553147 = 23329721) B23329721
theorem B72709001 : Blo 1680040 72709001 := bstep (se 2 (by rfl) ⟨27265875, by rfl⟩ : syracuseStep 72709001 = 54531751) B54531751
theorem B2521535 : Blo 1680040 2521535 := bstep (se 1 (by rfl) ⟨1891151, by rfl⟩ : syracuseStep 2521535 = 3782303) B3782303
theorem B112082447 : Blo 1680040 112082447 := bstep (se 1 (by rfl) ⟨84061835, by rfl⟩ : syracuseStep 112082447 = 168123671) B168123671
theorem B1892047 : Blo 1680040 1892047 := bstep (se 1 (by rfl) ⟨1419035, by rfl⟩ : syracuseStep 1892047 = 2838071) B2838071
theorem B9568489 : Blo 1680040 9568489 := bstep (se 2 (by rfl) ⟨3588183, by rfl⟩ : syracuseStep 9568489 = 7176367) B7176367
theorem B8184233 : Blo 1680040 8184233 := bstep (se 2 (by rfl) ⟨3069087, by rfl⟩ : syracuseStep 8184233 = 6138175) B6138175
theorem B48472667 : Blo 1680040 48472667 := bstep (se 1 (by rfl) ⟨36354500, by rfl⟩ : syracuseStep 48472667 = 72709001) B72709001
theorem B9569015 : Blo 1680040 9569015 := bstep (se 1 (by rfl) ⟨7176761, by rfl⟩ : syracuseStep 9569015 = 14353523) B14353523
theorem B1681023 : Blo 1680040 1681023 := bstep (se 1 (by rfl) ⟨1260767, by rfl⟩ : syracuseStep 1681023 = 2521535) B2521535
theorem B5671241 : Blo 1680040 5671241 := bstep (se 2 (by rfl) ⟨2126715, by rfl⟩ : syracuseStep 5671241 = 4253431) B4253431
theorem B74721631 : Blo 1680040 74721631 := bstep (se 1 (by rfl) ⟨56041223, by rfl⟩ : syracuseStep 74721631 = 112082447) B112082447
theorem B10766783 : Blo 1680040 10766783 := bstep (se 1 (by rfl) ⟨8075087, by rfl⟩ : syracuseStep 10766783 = 16150175) B16150175
theorem B4917929 : Blo 1680040 4917929 := bstep (se 2 (by rfl) ⟨1844223, by rfl⟩ : syracuseStep 4917929 = 3688447) B3688447
theorem B20737529 : Blo 1680040 20737529 := bstep (se 2 (by rfl) ⟨7776573, by rfl⟩ : syracuseStep 20737529 = 15553147) B15553147
theorem B147386303 : Blo 1680040 147386303 := bstep (se 1 (by rfl) ⟨110539727, by rfl⟩ : syracuseStep 147386303 = 221079455) B221079455
theorem B3781097 : Blo 1680040 3781097 := bstep (se 2 (by rfl) ⟨1417911, by rfl⟩ : syracuseStep 3781097 = 2835823) B2835823
theorem B8074799 : Blo 1680040 8074799 := bstep (se 1 (by rfl) ⟨6056099, by rfl⟩ : syracuseStep 8074799 = 12112199) B12112199
theorem B46020905 : Blo 1680040 46020905 := bstep (se 2 (by rfl) ⟨17257839, by rfl⟩ : syracuseStep 46020905 = 34515679) B34515679
theorem B12770135 : Blo 1680040 12770135 := bstep (se 1 (by rfl) ⟨9577601, by rfl⟩ : syracuseStep 12770135 = 19155203) B19155203
theorem B1891687 : Blo 1680040 1891687 := bstep (se 1 (by rfl) ⟨1418765, by rfl⟩ : syracuseStep 1891687 = 2837531) B2837531
theorem B2522729 : Blo 1680040 2522729 := bstep (se 2 (by rfl) ⟨946023, by rfl⟩ : syracuseStep 2522729 = 1892047) B1892047
theorem B5456155 : Blo 1680040 5456155 := bstep (se 1 (by rfl) ⟨4092116, by rfl⟩ : syracuseStep 5456155 = 8184233) B8184233
theorem B5383199 : Blo 1680040 5383199 := bstep (se 1 (by rfl) ⟨4037399, by rfl⟩ : syracuseStep 5383199 = 8074799) B8074799
theorem B30680603 : Blo 1680040 30680603 := bstep (se 1 (by rfl) ⟨23010452, by rfl⟩ : syracuseStep 30680603 = 46020905) B46020905
theorem B7177855 : Blo 1680040 7177855 := bstep (se 1 (by rfl) ⟨5383391, by rfl⟩ : syracuseStep 7177855 = 10766783) B10766783
theorem B8513423 : Blo 1680040 8513423 := bstep (se 1 (by rfl) ⟨6385067, by rfl⟩ : syracuseStep 8513423 = 12770135) B12770135
theorem B1681819 : Blo 1680040 1681819 := bstep (se 1 (by rfl) ⟨1261364, by rfl⟩ : syracuseStep 1681819 = 2522729) B2522729
theorem B98257535 : Blo 1680040 98257535 := bstep (se 1 (by rfl) ⟨73693151, by rfl⟩ : syracuseStep 98257535 = 147386303) B147386303
theorem B12757985 : Blo 1680040 12757985 := bstep (se 2 (by rfl) ⟨4784244, by rfl⟩ : syracuseStep 12757985 = 9568489) B9568489
theorem B3780827 : Blo 1680040 3780827 := bstep (se 1 (by rfl) ⟨2835620, by rfl⟩ : syracuseStep 3780827 = 5671241) B5671241
theorem B13825019 : Blo 1680040 13825019 := bstep (se 1 (by rfl) ⟨10368764, by rfl⟩ : syracuseStep 13825019 = 20737529) B20737529
theorem B2520731 : Blo 1680040 2520731 := bstep (se 1 (by rfl) ⟨1890548, by rfl⟩ : syracuseStep 2520731 = 3781097) B3781097
theorem B32315111 : Blo 1680040 32315111 := bstep (se 1 (by rfl) ⟨24236333, by rfl⟩ : syracuseStep 32315111 = 48472667) B48472667
theorem B99628841 : Blo 1680040 99628841 := bstep (se 2 (by rfl) ⟨37360815, by rfl⟩ : syracuseStep 99628841 = 74721631) B74721631
theorem B6379343 : Blo 1680040 6379343 := bstep (se 1 (by rfl) ⟨4784507, by rfl⟩ : syracuseStep 6379343 = 9569015) B9569015
theorem B13114477 : Blo 1680040 13114477 := bstep (se 3 (by rfl) ⟨2458964, by rfl⟩ : syracuseStep 13114477 = 4917929) B4917929
theorem B2522249 : Blo 1680040 2522249 := bstep (se 2 (by rfl) ⟨945843, by rfl⟩ : syracuseStep 2522249 = 1891687) B1891687
theorem B7274873 : Blo 1680040 7274873 := bstep (se 2 (by rfl) ⟨2728077, by rfl⟩ : syracuseStep 7274873 = 5456155) B5456155
theorem B9216679 : Blo 1680040 9216679 := bstep (se 1 (by rfl) ⟨6912509, by rfl⟩ : syracuseStep 9216679 = 13825019) B13825019
theorem B3588799 : Blo 1680040 3588799 := bstep (se 1 (by rfl) ⟨2691599, by rfl⟩ : syracuseStep 3588799 = 5383199) B5383199
theorem B1680487 : Blo 1680040 1680487 := bstep (se 1 (by rfl) ⟨1260365, by rfl⟩ : syracuseStep 1680487 = 2520731) B2520731
theorem B4252895 : Blo 1680040 4252895 := bstep (se 1 (by rfl) ⟨3189671, by rfl⟩ : syracuseStep 4252895 = 6379343) B6379343
theorem B65505023 : Blo 1680040 65505023 := bstep (se 1 (by rfl) ⟨49128767, by rfl⟩ : syracuseStep 65505023 = 98257535) B98257535
theorem B8505323 : Blo 1680040 8505323 := bstep (se 1 (by rfl) ⟨6378992, by rfl⟩ : syracuseStep 8505323 = 12757985) B12757985
theorem B1681499 : Blo 1680040 1681499 := bstep (se 1 (by rfl) ⟨1261124, by rfl⟩ : syracuseStep 1681499 = 2522249) B2522249
theorem B9570473 : Blo 1680040 9570473 := bstep (se 2 (by rfl) ⟨3588927, by rfl⟩ : syracuseStep 9570473 = 7177855) B7177855
theorem B17485969 : Blo 1680040 17485969 := bstep (se 2 (by rfl) ⟨6557238, by rfl⟩ : syracuseStep 17485969 = 13114477) B13114477
theorem B2520551 : Blo 1680040 2520551 := bstep (se 1 (by rfl) ⟨1890413, by rfl⟩ : syracuseStep 2520551 = 3780827) B3780827
theorem B20453735 : Blo 1680040 20453735 := bstep (se 1 (by rfl) ⟨15340301, by rfl⟩ : syracuseStep 20453735 = 30680603) B30680603
theorem B21543407 : Blo 1680040 21543407 := bstep (se 1 (by rfl) ⟨16157555, by rfl⟩ : syracuseStep 21543407 = 32315111) B32315111
theorem B66419227 : Blo 1680040 66419227 := bstep (se 1 (by rfl) ⟨49814420, by rfl⟩ : syracuseStep 66419227 = 99628841) B99628841
theorem B5675615 : Blo 1680040 5675615 := bstep (se 1 (by rfl) ⟨4256711, by rfl⟩ : syracuseStep 5675615 = 8513423) B8513423
theorem B23314625 : Blo 1680040 23314625 := bstep (se 2 (by rfl) ⟨8742984, by rfl⟩ : syracuseStep 23314625 = 17485969) B17485969
theorem B2835263 : Blo 1680040 2835263 := bstep (se 1 (by rfl) ⟨2126447, by rfl⟩ : syracuseStep 2835263 = 4252895) B4252895
theorem B12288905 : Blo 1680040 12288905 := bstep (se 2 (by rfl) ⟨4608339, by rfl⟩ : syracuseStep 12288905 = 9216679) B9216679
theorem B4785065 : Blo 1680040 4785065 := bstep (se 2 (by rfl) ⟨1794399, by rfl⟩ : syracuseStep 4785065 = 3588799) B3588799
theorem B19399661 : Blo 1680040 19399661 := bstep (se 3 (by rfl) ⟨3637436, by rfl⟩ : syracuseStep 19399661 = 7274873) B7274873
theorem B1680367 : Blo 1680040 1680367 := bstep (se 1 (by rfl) ⟨1260275, by rfl⟩ : syracuseStep 1680367 = 2520551) B2520551
theorem B5670215 : Blo 1680040 5670215 := bstep (se 1 (by rfl) ⟨4252661, by rfl⟩ : syracuseStep 5670215 = 8505323) B8505323
theorem B14362271 : Blo 1680040 14362271 := bstep (se 1 (by rfl) ⟨10771703, by rfl⟩ : syracuseStep 14362271 = 21543407) B21543407
theorem B88558969 : Blo 1680040 88558969 := bstep (se 2 (by rfl) ⟨33209613, by rfl⟩ : syracuseStep 88558969 = 66419227) B66419227
theorem B13635823 : Blo 1680040 13635823 := bstep (se 1 (by rfl) ⟨10226867, by rfl⟩ : syracuseStep 13635823 = 20453735) B20453735
theorem B43670015 : Blo 1680040 43670015 := bstep (se 1 (by rfl) ⟨32752511, by rfl⟩ : syracuseStep 43670015 = 65505023) B65505023
theorem B6380315 : Blo 1680040 6380315 := bstep (se 1 (by rfl) ⟨4785236, by rfl⟩ : syracuseStep 6380315 = 9570473) B9570473
theorem B3783743 : Blo 1680040 3783743 := bstep (se 1 (by rfl) ⟨2837807, by rfl⟩ : syracuseStep 3783743 = 5675615) B5675615
theorem B8192603 : Blo 1680040 8192603 := bstep (se 1 (by rfl) ⟨6144452, by rfl⟩ : syracuseStep 8192603 = 12288905) B12288905
theorem B4253543 : Blo 1680040 4253543 := bstep (se 1 (by rfl) ⟨3190157, by rfl⟩ : syracuseStep 4253543 = 6380315) B6380315
theorem B15543083 : Blo 1680040 15543083 := bstep (se 1 (by rfl) ⟨11657312, by rfl⟩ : syracuseStep 15543083 = 23314625) B23314625
theorem B18181097 : Blo 1680040 18181097 := bstep (se 2 (by rfl) ⟨6817911, by rfl⟩ : syracuseStep 18181097 = 13635823) B13635823
theorem B3190043 : Blo 1680040 3190043 := bstep (se 1 (by rfl) ⟨2392532, by rfl⟩ : syracuseStep 3190043 = 4785065) B4785065
theorem B3780143 : Blo 1680040 3780143 := bstep (se 1 (by rfl) ⟨2835107, by rfl⟩ : syracuseStep 3780143 = 5670215) B5670215
theorem B1890175 : Blo 1680040 1890175 := bstep (se 1 (by rfl) ⟨1417631, by rfl⟩ : syracuseStep 1890175 = 2835263) B2835263
theorem B12933107 : Blo 1680040 12933107 := bstep (se 1 (by rfl) ⟨9699830, by rfl⟩ : syracuseStep 12933107 = 19399661) B19399661
theorem B9574847 : Blo 1680040 9574847 := bstep (se 1 (by rfl) ⟨7181135, by rfl⟩ : syracuseStep 9574847 = 14362271) B14362271
theorem B29113343 : Blo 1680040 29113343 := bstep (se 1 (by rfl) ⟨21835007, by rfl⟩ : syracuseStep 29113343 = 43670015) B43670015
theorem B118078625 : Blo 1680040 118078625 := bstep (se 2 (by rfl) ⟨44279484, by rfl⟩ : syracuseStep 118078625 = 88558969) B88558969
theorem B2522495 : Blo 1680040 2522495 := bstep (se 1 (by rfl) ⟨1891871, by rfl⟩ : syracuseStep 2522495 = 3783743) B3783743
theorem B2835695 : Blo 1680040 2835695 := bstep (se 1 (by rfl) ⟨2126771, by rfl⟩ : syracuseStep 2835695 = 4253543) B4253543
theorem B6383231 : Blo 1680040 6383231 := bstep (se 1 (by rfl) ⟨4787423, by rfl⟩ : syracuseStep 6383231 = 9574847) B9574847
theorem B19408895 : Blo 1680040 19408895 := bstep (se 1 (by rfl) ⟨14556671, by rfl⟩ : syracuseStep 19408895 = 29113343) B29113343
theorem B78719083 : Blo 1680040 78719083 := bstep (se 1 (by rfl) ⟨59039312, by rfl⟩ : syracuseStep 78719083 = 118078625) B118078625
theorem B1681663 : Blo 1680040 1681663 := bstep (se 1 (by rfl) ⟨1261247, by rfl⟩ : syracuseStep 1681663 = 2522495) B2522495
theorem B8506781 : Blo 1680040 8506781 := bstep (se 3 (by rfl) ⟨1595021, by rfl⟩ : syracuseStep 8506781 = 3190043) B3190043
theorem B8622071 : Blo 1680040 8622071 := bstep (se 1 (by rfl) ⟨6466553, by rfl⟩ : syracuseStep 8622071 = 12933107) B12933107
theorem B12120731 : Blo 1680040 12120731 := bstep (se 1 (by rfl) ⟨9090548, by rfl⟩ : syracuseStep 12120731 = 18181097) B18181097
theorem B2520095 : Blo 1680040 2520095 := bstep (se 1 (by rfl) ⟨1890071, by rfl⟩ : syracuseStep 2520095 = 3780143) B3780143
theorem B2520233 : Blo 1680040 2520233 := bstep (se 2 (by rfl) ⟨945087, by rfl⟩ : syracuseStep 2520233 = 1890175) B1890175
theorem B5461735 : Blo 1680040 5461735 := bstep (se 1 (by rfl) ⟨4096301, by rfl⟩ : syracuseStep 5461735 = 8192603) B8192603
theorem B10362055 : Blo 1680040 10362055 := bstep (se 1 (by rfl) ⟨7771541, by rfl⟩ : syracuseStep 10362055 = 15543083) B15543083
theorem B1680063 : Blo 1680040 1680063 := bstep (se 1 (by rfl) ⟨1260047, by rfl⟩ : syracuseStep 1680063 = 2520095) B2520095
theorem B1680155 : Blo 1680040 1680155 := bstep (se 1 (by rfl) ⟨1260116, by rfl⟩ : syracuseStep 1680155 = 2520233) B2520233
theorem B5671187 : Blo 1680040 5671187 := bstep (se 1 (by rfl) ⟨4253390, by rfl⟩ : syracuseStep 5671187 = 8506781) B8506781
theorem B8080487 : Blo 1680040 8080487 := bstep (se 1 (by rfl) ⟨6060365, by rfl⟩ : syracuseStep 8080487 = 12120731) B12120731
theorem B419835109 : Blo 1680040 419835109 := bstep (se 4 (by rfl) ⟨39359541, by rfl⟩ : syracuseStep 419835109 = 78719083) B78719083
theorem B4255487 : Blo 1680040 4255487 := bstep (se 1 (by rfl) ⟨3191615, by rfl⟩ : syracuseStep 4255487 = 6383231) B6383231
theorem B12939263 : Blo 1680040 12939263 := bstep (se 1 (by rfl) ⟨9704447, by rfl⟩ : syracuseStep 12939263 = 19408895) B19408895
theorem B13816073 : Blo 1680040 13816073 := bstep (se 2 (by rfl) ⟨5181027, by rfl⟩ : syracuseStep 13816073 = 10362055) B10362055
theorem B5748047 : Blo 1680040 5748047 := bstep (se 1 (by rfl) ⟨4311035, by rfl⟩ : syracuseStep 5748047 = 8622071) B8622071
theorem B1890463 : Blo 1680040 1890463 := bstep (se 1 (by rfl) ⟨1417847, by rfl⟩ : syracuseStep 1890463 = 2835695) B2835695
theorem B7282313 : Blo 1680040 7282313 := bstep (se 2 (by rfl) ⟨2730867, by rfl⟩ : syracuseStep 7282313 = 5461735) B5461735
theorem B2836991 : Blo 1680040 2836991 := bstep (se 1 (by rfl) ⟨2127743, by rfl⟩ : syracuseStep 2836991 = 4255487) B4255487
theorem B9210715 : Blo 1680040 9210715 := bstep (se 1 (by rfl) ⟨6908036, by rfl⟩ : syracuseStep 9210715 = 13816073) B13816073
theorem B3780791 : Blo 1680040 3780791 := bstep (se 1 (by rfl) ⟨2835593, by rfl⟩ : syracuseStep 3780791 = 5671187) B5671187
theorem B559780145 : Blo 1680040 559780145 := bstep (se 2 (by rfl) ⟨209917554, by rfl⟩ : syracuseStep 559780145 = 419835109) B419835109
theorem B5386991 : Blo 1680040 5386991 := bstep (se 1 (by rfl) ⟨4040243, by rfl⟩ : syracuseStep 5386991 = 8080487) B8080487
theorem B4854875 : Blo 1680040 4854875 := bstep (se 1 (by rfl) ⟨3641156, by rfl⟩ : syracuseStep 4854875 = 7282313) B7282313
theorem B2520617 : Blo 1680040 2520617 := bstep (se 2 (by rfl) ⟨945231, by rfl⟩ : syracuseStep 2520617 = 1890463) B1890463
theorem B3832031 : Blo 1680040 3832031 := bstep (se 1 (by rfl) ⟨2874023, by rfl⟩ : syracuseStep 3832031 = 5748047) B5748047
theorem B8626175 : Blo 1680040 8626175 := bstep (se 1 (by rfl) ⟨6469631, by rfl⟩ : syracuseStep 8626175 = 12939263) B12939263
theorem B373186763 : Blo 1680040 373186763 := bstep (se 1 (by rfl) ⟨279890072, by rfl⟩ : syracuseStep 373186763 = 559780145) B559780145
theorem B1680411 : Blo 1680040 1680411 := bstep (se 1 (by rfl) ⟨1260308, by rfl⟩ : syracuseStep 1680411 = 2520617) B2520617
theorem B196495253 : Blo 1680040 196495253 := bstep (se 6 (by rfl) ⟨4605357, by rfl⟩ : syracuseStep 196495253 = 9210715) B9210715
theorem B51785333 : Blo 1680040 51785333 := bstep (se 5 (by rfl) ⟨2427437, by rfl⟩ : syracuseStep 51785333 = 4854875) B4854875
theorem B14365309 : Blo 1680040 14365309 := bstep (se 3 (by rfl) ⟨2693495, by rfl⟩ : syracuseStep 14365309 = 5386991) B5386991
theorem B2520527 : Blo 1680040 2520527 := bstep (se 1 (by rfl) ⟨1890395, by rfl⟩ : syracuseStep 2520527 = 3780791) B3780791
theorem B2554687 : Blo 1680040 2554687 := bstep (se 1 (by rfl) ⟨1916015, by rfl⟩ : syracuseStep 2554687 = 3832031) B3832031
theorem B1891327 : Blo 1680040 1891327 := bstep (se 1 (by rfl) ⟨1418495, by rfl⟩ : syracuseStep 1891327 = 2836991) B2836991
theorem B5750783 : Blo 1680040 5750783 := bstep (se 1 (by rfl) ⟨4313087, by rfl⟩ : syracuseStep 5750783 = 8626175) B8626175
theorem B248791175 : Blo 1680040 248791175 := bstep (se 1 (by rfl) ⟨186593381, by rfl⟩ : syracuseStep 248791175 = 373186763) B373186763
theorem B19153745 : Blo 1680040 19153745 := bstep (se 2 (by rfl) ⟨7182654, by rfl⟩ : syracuseStep 19153745 = 14365309) B14365309
theorem B1680351 : Blo 1680040 1680351 := bstep (se 1 (by rfl) ⟨1260263, by rfl⟩ : syracuseStep 1680351 = 2520527) B2520527
theorem B34523555 : Blo 1680040 34523555 := bstep (se 1 (by rfl) ⟨25892666, by rfl⟩ : syracuseStep 34523555 = 51785333) B51785333
theorem B3833855 : Blo 1680040 3833855 := bstep (se 1 (by rfl) ⟨2875391, by rfl⟩ : syracuseStep 3833855 = 5750783) B5750783
theorem B3406249 : Blo 1680040 3406249 := bstep (se 2 (by rfl) ⟨1277343, by rfl⟩ : syracuseStep 3406249 = 2554687) B2554687
theorem B130996835 : Blo 1680040 130996835 := bstep (se 1 (by rfl) ⟨98247626, by rfl⟩ : syracuseStep 130996835 = 196495253) B196495253
theorem B2521769 : Blo 1680040 2521769 := bstep (se 2 (by rfl) ⟨945663, by rfl⟩ : syracuseStep 2521769 = 1891327) B1891327
theorem B92062813 : Blo 1680040 92062813 := bstep (se 3 (by rfl) ⟨17261777, by rfl⟩ : syracuseStep 92062813 = 34523555) B34523555
theorem B1681179 : Blo 1680040 1681179 := bstep (se 1 (by rfl) ⟨1260884, by rfl⟩ : syracuseStep 1681179 = 2521769) B2521769
theorem B4541665 : Blo 1680040 4541665 := bstep (se 2 (by rfl) ⟨1703124, by rfl⟩ : syracuseStep 4541665 = 3406249) B3406249
theorem B87331223 : Blo 1680040 87331223 := bstep (se 1 (by rfl) ⟨65498417, by rfl⟩ : syracuseStep 87331223 = 130996835) B130996835
theorem B165860783 : Blo 1680040 165860783 := bstep (se 1 (by rfl) ⟨124395587, by rfl⟩ : syracuseStep 165860783 = 248791175) B248791175
theorem B12769163 : Blo 1680040 12769163 := bstep (se 1 (by rfl) ⟨9576872, by rfl⟩ : syracuseStep 12769163 = 19153745) B19153745
theorem B2555903 : Blo 1680040 2555903 := bstep (se 1 (by rfl) ⟨1916927, by rfl⟩ : syracuseStep 2555903 = 3833855) B3833855
theorem B232883261 : Blo 1680040 232883261 := bstep (se 3 (by rfl) ⟨43665611, by rfl⟩ : syracuseStep 232883261 = 87331223) B87331223
theorem B8512775 : Blo 1680040 8512775 := bstep (se 1 (by rfl) ⟨6384581, by rfl⟩ : syracuseStep 8512775 = 12769163) B12769163
theorem B122750417 : Blo 1680040 122750417 := bstep (se 2 (by rfl) ⟨46031406, by rfl⟩ : syracuseStep 122750417 = 92062813) B92062813
theorem B6055553 : Blo 1680040 6055553 := bstep (se 2 (by rfl) ⟨2270832, by rfl⟩ : syracuseStep 6055553 = 4541665) B4541665
theorem B110573855 : Blo 1680040 110573855 := bstep (se 1 (by rfl) ⟨82930391, by rfl⟩ : syracuseStep 110573855 = 165860783) B165860783
theorem B1703935 : Blo 1680040 1703935 := bstep (se 1 (by rfl) ⟨1277951, by rfl⟩ : syracuseStep 1703935 = 2555903) B2555903
theorem B155255507 : Blo 1680040 155255507 := bstep (se 1 (by rfl) ⟨116441630, by rfl⟩ : syracuseStep 155255507 = 232883261) B232883261
theorem B9087653 : Blo 1680040 9087653 := bstep (se 4 (by rfl) ⟨851967, by rfl⟩ : syracuseStep 9087653 = 1703935) B1703935
theorem B81833611 : Blo 1680040 81833611 := bstep (se 1 (by rfl) ⟨61375208, by rfl⟩ : syracuseStep 81833611 = 122750417) B122750417
theorem B73715903 : Blo 1680040 73715903 := bstep (se 1 (by rfl) ⟨55286927, by rfl⟩ : syracuseStep 73715903 = 110573855) B110573855
theorem B5675183 : Blo 1680040 5675183 := bstep (se 1 (by rfl) ⟨4256387, by rfl⟩ : syracuseStep 5675183 = 8512775) B8512775
theorem B4037035 : Blo 1680040 4037035 := bstep (se 1 (by rfl) ⟨3027776, by rfl⟩ : syracuseStep 4037035 = 6055553) B6055553
theorem B49143935 : Blo 1680040 49143935 := bstep (se 1 (by rfl) ⟨36857951, by rfl⟩ : syracuseStep 49143935 = 73715903) B73715903
theorem B5382713 : Blo 1680040 5382713 := bstep (se 2 (by rfl) ⟨2018517, by rfl⟩ : syracuseStep 5382713 = 4037035) B4037035
theorem B109111481 : Blo 1680040 109111481 := bstep (se 2 (by rfl) ⟨40916805, by rfl⟩ : syracuseStep 109111481 = 81833611) B81833611
theorem B6058435 : Blo 1680040 6058435 := bstep (se 1 (by rfl) ⟨4543826, by rfl⟩ : syracuseStep 6058435 = 9087653) B9087653
theorem B103503671 : Blo 1680040 103503671 := bstep (se 1 (by rfl) ⟨77627753, by rfl⟩ : syracuseStep 103503671 = 155255507) B155255507
theorem B3783455 : Blo 1680040 3783455 := bstep (se 1 (by rfl) ⟨2837591, by rfl⟩ : syracuseStep 3783455 = 5675183) B5675183
theorem B3588475 : Blo 1680040 3588475 := bstep (se 1 (by rfl) ⟨2691356, by rfl⟩ : syracuseStep 3588475 = 5382713) B5382713
theorem B8077913 : Blo 1680040 8077913 := bstep (se 2 (by rfl) ⟨3029217, by rfl⟩ : syracuseStep 8077913 = 6058435) B6058435
theorem B69002447 : Blo 1680040 69002447 := bstep (se 1 (by rfl) ⟨51751835, by rfl⟩ : syracuseStep 69002447 = 103503671) B103503671
theorem B131050493 : Blo 1680040 131050493 := bstep (se 3 (by rfl) ⟨24571967, by rfl⟩ : syracuseStep 131050493 = 49143935) B49143935
theorem B72740987 : Blo 1680040 72740987 := bstep (se 1 (by rfl) ⟨54555740, by rfl⟩ : syracuseStep 72740987 = 109111481) B109111481
theorem B2522303 : Blo 1680040 2522303 := bstep (se 1 (by rfl) ⟨1891727, by rfl⟩ : syracuseStep 2522303 = 3783455) B3783455
theorem B4784633 : Blo 1680040 4784633 := bstep (se 2 (by rfl) ⟨1794237, by rfl⟩ : syracuseStep 4784633 = 3588475) B3588475
theorem B1681535 : Blo 1680040 1681535 := bstep (se 1 (by rfl) ⟨1261151, by rfl⟩ : syracuseStep 1681535 = 2522303) B2522303
theorem B5385275 : Blo 1680040 5385275 := bstep (se 1 (by rfl) ⟨4038956, by rfl⟩ : syracuseStep 5385275 = 8077913) B8077913
theorem B48493991 : Blo 1680040 48493991 := bstep (se 1 (by rfl) ⟨36370493, by rfl⟩ : syracuseStep 48493991 = 72740987) B72740987
theorem B184006525 : Blo 1680040 184006525 := bstep (se 3 (by rfl) ⟨34501223, by rfl⟩ : syracuseStep 184006525 = 69002447) B69002447
theorem B87366995 : Blo 1680040 87366995 := bstep (se 1 (by rfl) ⟨65525246, by rfl⟩ : syracuseStep 87366995 = 131050493) B131050493
theorem B3590183 : Blo 1680040 3590183 := bstep (se 1 (by rfl) ⟨2692637, by rfl⟩ : syracuseStep 3590183 = 5385275) B5385275
theorem B3189755 : Blo 1680040 3189755 := bstep (se 1 (by rfl) ⟨2392316, by rfl⟩ : syracuseStep 3189755 = 4784633) B4784633
theorem B32329327 : Blo 1680040 32329327 := bstep (se 1 (by rfl) ⟨24246995, by rfl⟩ : syracuseStep 32329327 = 48493991) B48493991
theorem B58244663 : Blo 1680040 58244663 := bstep (se 1 (by rfl) ⟨43683497, by rfl⟩ : syracuseStep 58244663 = 87366995) B87366995
theorem B245342033 : Blo 1680040 245342033 := bstep (se 2 (by rfl) ⟨92003262, by rfl⟩ : syracuseStep 245342033 = 184006525) B184006525
theorem B2126503 : Blo 1680040 2126503 := bstep (se 1 (by rfl) ⟨1594877, by rfl⟩ : syracuseStep 2126503 = 3189755) B3189755
theorem B9573821 : Blo 1680040 9573821 := bstep (se 3 (by rfl) ⟨1795091, by rfl⟩ : syracuseStep 9573821 = 3590183) B3590183
theorem B43105769 : Blo 1680040 43105769 := bstep (se 2 (by rfl) ⟨16164663, by rfl⟩ : syracuseStep 43105769 = 32329327) B32329327
theorem B38829775 : Blo 1680040 38829775 := bstep (se 1 (by rfl) ⟨29122331, by rfl⟩ : syracuseStep 38829775 = 58244663) B58244663
theorem B163561355 : Blo 1680040 163561355 := bstep (se 1 (by rfl) ⟨122671016, by rfl⟩ : syracuseStep 163561355 = 245342033) B245342033
theorem B2835337 : Blo 1680040 2835337 := bstep (se 2 (by rfl) ⟨1063251, by rfl⟩ : syracuseStep 2835337 = 2126503) B2126503
theorem B6382547 : Blo 1680040 6382547 := bstep (se 1 (by rfl) ⟨4786910, by rfl⟩ : syracuseStep 6382547 = 9573821) B9573821
theorem B109040903 : Blo 1680040 109040903 := bstep (se 1 (by rfl) ⟨81780677, by rfl⟩ : syracuseStep 109040903 = 163561355) B163561355
theorem B51773033 : Blo 1680040 51773033 := bstep (se 2 (by rfl) ⟨19414887, by rfl⟩ : syracuseStep 51773033 = 38829775) B38829775
theorem B28737179 : Blo 1680040 28737179 := bstep (se 1 (by rfl) ⟨21552884, by rfl⟩ : syracuseStep 28737179 = 43105769) B43105769
theorem B34515355 : Blo 1680040 34515355 := bstep (se 1 (by rfl) ⟨25886516, by rfl⟩ : syracuseStep 34515355 = 51773033) B51773033
theorem B4255031 : Blo 1680040 4255031 := bstep (se 1 (by rfl) ⟨3191273, by rfl⟩ : syracuseStep 4255031 = 6382547) B6382547
theorem B3780449 : Blo 1680040 3780449 := bstep (se 2 (by rfl) ⟨1417668, by rfl⟩ : syracuseStep 3780449 = 2835337) B2835337
theorem B19158119 : Blo 1680040 19158119 := bstep (se 1 (by rfl) ⟨14368589, by rfl⟩ : syracuseStep 19158119 = 28737179) B28737179
theorem B72693935 : Blo 1680040 72693935 := bstep (se 1 (by rfl) ⟨54520451, by rfl⟩ : syracuseStep 72693935 = 109040903) B109040903
theorem B12772079 : Blo 1680040 12772079 := bstep (se 1 (by rfl) ⟨9579059, by rfl⟩ : syracuseStep 12772079 = 19158119) B19158119
theorem B2836687 : Blo 1680040 2836687 := bstep (se 1 (by rfl) ⟨2127515, by rfl⟩ : syracuseStep 2836687 = 4255031) B4255031
theorem B2520299 : Blo 1680040 2520299 := bstep (se 1 (by rfl) ⟨1890224, by rfl⟩ : syracuseStep 2520299 = 3780449) B3780449
theorem B46020473 : Blo 1680040 46020473 := bstep (se 2 (by rfl) ⟨17257677, by rfl⟩ : syracuseStep 46020473 = 34515355) B34515355
theorem B48462623 : Blo 1680040 48462623 := bstep (se 1 (by rfl) ⟨36346967, by rfl⟩ : syracuseStep 48462623 = 72693935) B72693935
theorem B1680199 : Blo 1680040 1680199 := bstep (se 1 (by rfl) ⟨1260149, by rfl⟩ : syracuseStep 1680199 = 2520299) B2520299
theorem B30680315 : Blo 1680040 30680315 := bstep (se 1 (by rfl) ⟨23010236, by rfl⟩ : syracuseStep 30680315 = 46020473) B46020473
theorem B8514719 : Blo 1680040 8514719 := bstep (se 1 (by rfl) ⟨6386039, by rfl⟩ : syracuseStep 8514719 = 12772079) B12772079
theorem B3782249 : Blo 1680040 3782249 := bstep (se 2 (by rfl) ⟨1418343, by rfl⟩ : syracuseStep 3782249 = 2836687) B2836687
theorem B32308415 : Blo 1680040 32308415 := bstep (se 1 (by rfl) ⟨24231311, by rfl⟩ : syracuseStep 32308415 = 48462623) B48462623
theorem B21538943 : Blo 1680040 21538943 := bstep (se 1 (by rfl) ⟨16154207, by rfl⟩ : syracuseStep 21538943 = 32308415) B32308415
theorem B20453543 : Blo 1680040 20453543 := bstep (se 1 (by rfl) ⟨15340157, by rfl⟩ : syracuseStep 20453543 = 30680315) B30680315
theorem B2521499 : Blo 1680040 2521499 := bstep (se 1 (by rfl) ⟨1891124, by rfl⟩ : syracuseStep 2521499 = 3782249) B3782249
theorem B5676479 : Blo 1680040 5676479 := bstep (se 1 (by rfl) ⟨4257359, by rfl⟩ : syracuseStep 5676479 = 8514719) B8514719
theorem B1680999 : Blo 1680040 1680999 := bstep (se 1 (by rfl) ⟨1260749, by rfl⟩ : syracuseStep 1680999 = 2521499) B2521499
theorem B13635695 : Blo 1680040 13635695 := bstep (se 1 (by rfl) ⟨10226771, by rfl⟩ : syracuseStep 13635695 = 20453543) B20453543
theorem B14359295 : Blo 1680040 14359295 := bstep (se 1 (by rfl) ⟨10769471, by rfl⟩ : syracuseStep 14359295 = 21538943) B21538943
theorem B3784319 : Blo 1680040 3784319 := bstep (se 1 (by rfl) ⟨2838239, by rfl⟩ : syracuseStep 3784319 = 5676479) B5676479
theorem B9572863 : Blo 1680040 9572863 := bstep (se 1 (by rfl) ⟨7179647, by rfl⟩ : syracuseStep 9572863 = 14359295) B14359295
theorem B9090463 : Blo 1680040 9090463 := bstep (se 1 (by rfl) ⟨6817847, by rfl⟩ : syracuseStep 9090463 = 13635695) B13635695
theorem B2522879 : Blo 1680040 2522879 := bstep (se 1 (by rfl) ⟨1892159, by rfl⟩ : syracuseStep 2522879 = 3784319) B3784319
theorem B12763817 : Blo 1680040 12763817 := bstep (se 2 (by rfl) ⟨4786431, by rfl⟩ : syracuseStep 12763817 = 9572863) B9572863
theorem B1681919 : Blo 1680040 1681919 := bstep (se 1 (by rfl) ⟨1261439, by rfl⟩ : syracuseStep 1681919 = 2522879) B2522879
theorem B12120617 : Blo 1680040 12120617 := bstep (se 2 (by rfl) ⟨4545231, by rfl⟩ : syracuseStep 12120617 = 9090463) B9090463
theorem B8080411 : Blo 1680040 8080411 := bstep (se 1 (by rfl) ⟨6060308, by rfl⟩ : syracuseStep 8080411 = 12120617) B12120617
theorem B8509211 : Blo 1680040 8509211 := bstep (se 1 (by rfl) ⟨6381908, by rfl⟩ : syracuseStep 8509211 = 12763817) B12763817
theorem B10773881 : Blo 1680040 10773881 := bstep (se 2 (by rfl) ⟨4040205, by rfl⟩ : syracuseStep 10773881 = 8080411) B8080411
theorem B5672807 : Blo 1680040 5672807 := bstep (se 1 (by rfl) ⟨4254605, by rfl⟩ : syracuseStep 5672807 = 8509211) B8509211
theorem B3781871 : Blo 1680040 3781871 := bstep (se 1 (by rfl) ⟨2836403, by rfl⟩ : syracuseStep 3781871 = 5672807) B5672807
theorem B7182587 : Blo 1680040 7182587 := bstep (se 1 (by rfl) ⟨5386940, by rfl⟩ : syracuseStep 7182587 = 10773881) B10773881
theorem B4788391 : Blo 1680040 4788391 := bstep (se 1 (by rfl) ⟨3591293, by rfl⟩ : syracuseStep 4788391 = 7182587) B7182587
theorem B2521247 : Blo 1680040 2521247 := bstep (se 1 (by rfl) ⟨1890935, by rfl⟩ : syracuseStep 2521247 = 3781871) B3781871
theorem B1680831 : Blo 1680040 1680831 := bstep (se 1 (by rfl) ⟨1260623, by rfl⟩ : syracuseStep 1680831 = 2521247) B2521247
theorem B6384521 : Blo 1680040 6384521 := bstep (se 2 (by rfl) ⟨2394195, by rfl⟩ : syracuseStep 6384521 = 4788391) B4788391
theorem B4256347 : Blo 1680040 4256347 := bstep (se 1 (by rfl) ⟨3192260, by rfl⟩ : syracuseStep 4256347 = 6384521) B6384521
theorem B5675129 : Blo 1680040 5675129 := bstep (se 2 (by rfl) ⟨2128173, by rfl⟩ : syracuseStep 5675129 = 4256347) B4256347
theorem B3783419 : Blo 1680040 3783419 := bstep (se 1 (by rfl) ⟨2837564, by rfl⟩ : syracuseStep 3783419 = 5675129) B5675129
theorem B2522279 : Blo 1680040 2522279 := bstep (se 1 (by rfl) ⟨1891709, by rfl⟩ : syracuseStep 2522279 = 3783419) B3783419
theorem B1681519 : Blo 1680040 1681519 := bstep (se 1 (by rfl) ⟨1261139, by rfl⟩ : syracuseStep 1681519 = 2522279) B2522279

theorem C0 (j : ℕ) (h1 : 420010 ≤ j) (h2 : j ≤ 420509) : Blo 1680040 (4 * j + 3) := by
  interval_cases j
  · exact B1680043
  · exact B1680047
  · exact B1680051
  · exact B1680055
  · exact B1680059
  · exact B1680063
  · exact B1680067
  · exact B1680071
  · exact B1680075
  · exact B1680079
  · exact B1680083
  · exact B1680087
  · exact B1680091
  · exact B1680095
  · exact B1680099
  · exact B1680103
  · exact B1680107
  · exact B1680111
  · exact B1680115
  · exact B1680119
  · exact B1680123
  · exact B1680127
  · exact B1680131
  · exact B1680135
  · exact B1680139
  · exact B1680143
  · exact B1680147
  · exact B1680151
  · exact B1680155
  · exact B1680159
  · exact B1680163
  · exact B1680167
  · exact B1680171
  · exact B1680175
  · exact B1680179
  · exact B1680183
  · exact B1680187
  · exact B1680191
  · exact B1680195
  · exact B1680199
  · exact B1680203
  · exact B1680207
  · exact B1680211
  · exact B1680215
  · exact B1680219
  · exact B1680223
  · exact B1680227
  · exact B1680231
  · exact B1680235
  · exact B1680239
  · exact B1680243
  · exact B1680247
  · exact B1680251
  · exact B1680255
  · exact B1680259
  · exact B1680263
  · exact B1680267
  · exact B1680271
  · exact B1680275
  · exact B1680279
  · exact B1680283
  · exact B1680287
  · exact B1680291
  · exact B1680295
  · exact B1680299
  · exact B1680303
  · exact B1680307
  · exact B1680311
  · exact B1680315
  · exact B1680319
  · exact B1680323
  · exact B1680327
  · exact B1680331
  · exact B1680335
  · exact B1680339
  · exact B1680343
  · exact B1680347
  · exact B1680351
  · exact B1680355
  · exact B1680359
  · exact B1680363
  · exact B1680367
  · exact B1680371
  · exact B1680375
  · exact B1680379
  · exact B1680383
  · exact B1680387
  · exact B1680391
  · exact B1680395
  · exact B1680399
  · exact B1680403
  · exact B1680407
  · exact B1680411
  · exact B1680415
  · exact B1680419
  · exact B1680423
  · exact B1680427
  · exact B1680431
  · exact B1680435
  · exact B1680439
  · exact B1680443
  · exact B1680447
  · exact B1680451
  · exact B1680455
  · exact B1680459
  · exact B1680463
  · exact B1680467
  · exact B1680471
  · exact B1680475
  · exact B1680479
  · exact B1680483
  · exact B1680487
  · exact B1680491
  · exact B1680495
  · exact B1680499
  · exact B1680503
  · exact B1680507
  · exact B1680511
  · exact B1680515
  · exact B1680519
  · exact B1680523
  · exact B1680527
  · exact B1680531
  · exact B1680535
  · exact B1680539
  · exact B1680543
  · exact B1680547
  · exact B1680551
  · exact B1680555
  · exact B1680559
  · exact B1680563
  · exact B1680567
  · exact B1680571
  · exact B1680575
  · exact B1680579
  · exact B1680583
  · exact B1680587
  · exact B1680591
  · exact B1680595
  · exact B1680599
  · exact B1680603
  · exact B1680607
  · exact B1680611
  · exact B1680615
  · exact B1680619
  · exact B1680623
  · exact B1680627
  · exact B1680631
  · exact B1680635
  · exact B1680639
  · exact B1680643
  · exact B1680647
  · exact B1680651
  · exact B1680655
  · exact B1680659
  · exact B1680663
  · exact B1680667
  · exact B1680671
  · exact B1680675
  · exact B1680679
  · exact B1680683
  · exact B1680687
  · exact B1680691
  · exact B1680695
  · exact B1680699
  · exact B1680703
  · exact B1680707
  · exact B1680711
  · exact B1680715
  · exact B1680719
  · exact B1680723
  · exact B1680727
  · exact B1680731
  · exact B1680735
  · exact B1680739
  · exact B1680743
  · exact B1680747
  · exact B1680751
  · exact B1680755
  · exact B1680759
  · exact B1680763
  · exact B1680767
  · exact B1680771
  · exact B1680775
  · exact B1680779
  · exact B1680783
  · exact B1680787
  · exact B1680791
  · exact B1680795
  · exact B1680799
  · exact B1680803
  · exact B1680807
  · exact B1680811
  · exact B1680815
  · exact B1680819
  · exact B1680823
  · exact B1680827
  · exact B1680831
  · exact B1680835
  · exact B1680839
  · exact B1680843
  · exact B1680847
  · exact B1680851
  · exact B1680855
  · exact B1680859
  · exact B1680863
  · exact B1680867
  · exact B1680871
  · exact B1680875
  · exact B1680879
  · exact B1680883
  · exact B1680887
  · exact B1680891
  · exact B1680895
  · exact B1680899
  · exact B1680903
  · exact B1680907
  · exact B1680911
  · exact B1680915
  · exact B1680919
  · exact B1680923
  · exact B1680927
  · exact B1680931
  · exact B1680935
  · exact B1680939
  · exact B1680943
  · exact B1680947
  · exact B1680951
  · exact B1680955
  · exact B1680959
  · exact B1680963
  · exact B1680967
  · exact B1680971
  · exact B1680975
  · exact B1680979
  · exact B1680983
  · exact B1680987
  · exact B1680991
  · exact B1680995
  · exact B1680999
  · exact B1681003
  · exact B1681007
  · exact B1681011
  · exact B1681015
  · exact B1681019
  · exact B1681023
  · exact B1681027
  · exact B1681031
  · exact B1681035
  · exact B1681039
  · exact B1681043
  · exact B1681047
  · exact B1681051
  · exact B1681055
  · exact B1681059
  · exact B1681063
  · exact B1681067
  · exact B1681071
  · exact B1681075
  · exact B1681079
  · exact B1681083
  · exact B1681087
  · exact B1681091
  · exact B1681095
  · exact B1681099
  · exact B1681103
  · exact B1681107
  · exact B1681111
  · exact B1681115
  · exact B1681119
  · exact B1681123
  · exact B1681127
  · exact B1681131
  · exact B1681135
  · exact B1681139
  · exact B1681143
  · exact B1681147
  · exact B1681151
  · exact B1681155
  · exact B1681159
  · exact B1681163
  · exact B1681167
  · exact B1681171
  · exact B1681175
  · exact B1681179
  · exact B1681183
  · exact B1681187
  · exact B1681191
  · exact B1681195
  · exact B1681199
  · exact B1681203
  · exact B1681207
  · exact B1681211
  · exact B1681215
  · exact B1681219
  · exact B1681223
  · exact B1681227
  · exact B1681231
  · exact B1681235
  · exact B1681239
  · exact B1681243
  · exact B1681247
  · exact B1681251
  · exact B1681255
  · exact B1681259
  · exact B1681263
  · exact B1681267
  · exact B1681271
  · exact B1681275
  · exact B1681279
  · exact B1681283
  · exact B1681287
  · exact B1681291
  · exact B1681295
  · exact B1681299
  · exact B1681303
  · exact B1681307
  · exact B1681311
  · exact B1681315
  · exact B1681319
  · exact B1681323
  · exact B1681327
  · exact B1681331
  · exact B1681335
  · exact B1681339
  · exact B1681343
  · exact B1681347
  · exact B1681351
  · exact B1681355
  · exact B1681359
  · exact B1681363
  · exact B1681367
  · exact B1681371
  · exact B1681375
  · exact B1681379
  · exact B1681383
  · exact B1681387
  · exact B1681391
  · exact B1681395
  · exact B1681399
  · exact B1681403
  · exact B1681407
  · exact B1681411
  · exact B1681415
  · exact B1681419
  · exact B1681423
  · exact B1681427
  · exact B1681431
  · exact B1681435
  · exact B1681439
  · exact B1681443
  · exact B1681447
  · exact B1681451
  · exact B1681455
  · exact B1681459
  · exact B1681463
  · exact B1681467
  · exact B1681471
  · exact B1681475
  · exact B1681479
  · exact B1681483
  · exact B1681487
  · exact B1681491
  · exact B1681495
  · exact B1681499
  · exact B1681503
  · exact B1681507
  · exact B1681511
  · exact B1681515
  · exact B1681519
  · exact B1681523
  · exact B1681527
  · exact B1681531
  · exact B1681535
  · exact B1681539
  · exact B1681543
  · exact B1681547
  · exact B1681551
  · exact B1681555
  · exact B1681559
  · exact B1681563
  · exact B1681567
  · exact B1681571
  · exact B1681575
  · exact B1681579
  · exact B1681583
  · exact B1681587
  · exact B1681591
  · exact B1681595
  · exact B1681599
  · exact B1681603
  · exact B1681607
  · exact B1681611
  · exact B1681615
  · exact B1681619
  · exact B1681623
  · exact B1681627
  · exact B1681631
  · exact B1681635
  · exact B1681639
  · exact B1681643
  · exact B1681647
  · exact B1681651
  · exact B1681655
  · exact B1681659
  · exact B1681663
  · exact B1681667
  · exact B1681671
  · exact B1681675
  · exact B1681679
  · exact B1681683
  · exact B1681687
  · exact B1681691
  · exact B1681695
  · exact B1681699
  · exact B1681703
  · exact B1681707
  · exact B1681711
  · exact B1681715
  · exact B1681719
  · exact B1681723
  · exact B1681727
  · exact B1681731
  · exact B1681735
  · exact B1681739
  · exact B1681743
  · exact B1681747
  · exact B1681751
  · exact B1681755
  · exact B1681759
  · exact B1681763
  · exact B1681767
  · exact B1681771
  · exact B1681775
  · exact B1681779
  · exact B1681783
  · exact B1681787
  · exact B1681791
  · exact B1681795
  · exact B1681799
  · exact B1681803
  · exact B1681807
  · exact B1681811
  · exact B1681815
  · exact B1681819
  · exact B1681823
  · exact B1681827
  · exact B1681831
  · exact B1681835
  · exact B1681839
  · exact B1681843
  · exact B1681847
  · exact B1681851
  · exact B1681855
  · exact B1681859
  · exact B1681863
  · exact B1681867
  · exact B1681871
  · exact B1681875
  · exact B1681879
  · exact B1681883
  · exact B1681887
  · exact B1681891
  · exact B1681895
  · exact B1681899
  · exact B1681903
  · exact B1681907
  · exact B1681911
  · exact B1681915
  · exact B1681919
  · exact B1681923
  · exact B1681927
  · exact B1681931
  · exact B1681935
  · exact B1681939
  · exact B1681943
  · exact B1681947
  · exact B1681951
  · exact B1681955
  · exact B1681959
  · exact B1681963
  · exact B1681967
  · exact B1681971
  · exact B1681975
  · exact B1681979
  · exact B1681983
  · exact B1681987
  · exact B1681991
  · exact B1681995
  · exact B1681999
  · exact B1682003
  · exact B1682007
  · exact B1682011
  · exact B1682015
  · exact B1682019
  · exact B1682023
  · exact B1682027
  · exact B1682031
  · exact B1682035
  · exact B1682039

theorem solution (m : ℕ) (hlo : 1680040 ≤ m) (hhi : m ≤ 1682040) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 420010 ≤ j := by omega
    have hj2 : j ≤ 420509 := by omega
    have hb : Blo 1680040 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
