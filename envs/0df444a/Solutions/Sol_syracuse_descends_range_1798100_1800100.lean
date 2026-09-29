-- Prove2me | solution 1 for syracuse_descends_range_1798100_1800100
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:49:35.017988+00:00
-- url     : https://prove2.me/submissions/57f850af-2a3a-4caa-95d9-54e0d322a606

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


theorem B2023429 : Blo 1798100 2023429 := bbase (se 4 (by rfl) ⟨189696, by rfl⟩ : syracuseStep 2023429 = 379393) (by norm_num)
theorem B4046885 : Blo 1798100 4046885 := bbase (se 4 (by rfl) ⟨379395, by rfl⟩ : syracuseStep 4046885 = 758791) (by norm_num)
theorem B2023465 : Blo 1798100 2023465 := bbase (se 2 (by rfl) ⟨758799, by rfl⟩ : syracuseStep 2023465 = 1517599) (by norm_num)
theorem B2023501 : Blo 1798100 2023501 := bbase (se 3 (by rfl) ⟨379406, by rfl⟩ : syracuseStep 2023501 = 758813) (by norm_num)
theorem B3842149 : Blo 1798100 3842149 := bbase (se 4 (by rfl) ⟨360201, by rfl⟩ : syracuseStep 3842149 = 720403) (by norm_num)
theorem B4046957 : Blo 1798100 4046957 := bbase (se 3 (by rfl) ⟨758804, by rfl⟩ : syracuseStep 4046957 = 1517609) (by norm_num)
theorem B2023537 : Blo 1798100 2023537 := bbase (se 2 (by rfl) ⟨758826, by rfl⟩ : syracuseStep 2023537 = 1517653) (by norm_num)
theorem B2277497 : Blo 1798100 2277497 := bbase (se 2 (by rfl) ⟨854061, by rfl⟩ : syracuseStep 2277497 = 1708123) (by norm_num)
theorem B3645581 : Blo 1798100 3645581 := bbase (se 3 (by rfl) ⟨683546, by rfl⟩ : syracuseStep 3645581 = 1367093) (by norm_num)
theorem B4554893 : Blo 1798100 4554893 := bbase (se 3 (by rfl) ⟨854042, by rfl⟩ : syracuseStep 4554893 = 1708085) (by norm_num)
theorem B2023573 : Blo 1798100 2023573 := bbase (se 6 (by rfl) ⟨47427, by rfl⟩ : syracuseStep 2023573 = 94855) (by norm_num)
theorem B23052437 : Blo 1798100 23052437 := bbase (se 6 (by rfl) ⟨540291, by rfl⟩ : syracuseStep 23052437 = 1080583) (by norm_num)
theorem B2277553 : Blo 1798100 2277553 := bbase (se 2 (by rfl) ⟨854082, by rfl⟩ : syracuseStep 2277553 = 1708165) (by norm_num)
theorem B4047029 : Blo 1798100 4047029 := bbase (se 5 (by rfl) ⟨189704, by rfl⟩ : syracuseStep 4047029 = 379409) (by norm_num)
theorem B6832309 : Blo 1798100 6832309 := bbase (se 5 (by rfl) ⟨320264, by rfl⟩ : syracuseStep 6832309 = 640529) (by norm_num)
theorem B2023609 : Blo 1798100 2023609 := bbase (se 2 (by rfl) ⟨758853, by rfl⟩ : syracuseStep 2023609 = 1517707) (by norm_num)
theorem B3416269 : Blo 1798100 3416269 := bbase (se 3 (by rfl) ⟨640550, by rfl⟩ : syracuseStep 3416269 = 1281101) (by norm_num)
theorem B2023645 : Blo 1798100 2023645 := bbase (se 3 (by rfl) ⟨379433, by rfl⟩ : syracuseStep 2023645 = 758867) (by norm_num)
theorem B6070517 : Blo 1798100 6070517 := bbase (se 5 (by rfl) ⟨284555, by rfl⟩ : syracuseStep 6070517 = 569111) (by norm_num)
theorem B4047101 : Blo 1798100 4047101 := bbase (se 3 (by rfl) ⟨758831, by rfl⟩ : syracuseStep 4047101 = 1517663) (by norm_num)
theorem B2023681 : Blo 1798100 2023681 := bbase (se 2 (by rfl) ⟨758880, by rfl⟩ : syracuseStep 2023681 = 1517761) (by norm_num)
theorem B2277649 : Blo 1798100 2277649 := bbase (se 2 (by rfl) ⟨854118, by rfl⟩ : syracuseStep 2277649 = 1708237) (by norm_num)
theorem B8642837 : Blo 1798100 8642837 := bbase (se 6 (by rfl) ⟨202566, by rfl⟩ : syracuseStep 8642837 = 405133) (by norm_num)
theorem B15376661 : Blo 1798100 15376661 := bbase (se 6 (by rfl) ⟨360390, by rfl⟩ : syracuseStep 15376661 = 720781) (by norm_num)
theorem B2023717 : Blo 1798100 2023717 := bbase (se 4 (by rfl) ⟨189723, by rfl⟩ : syracuseStep 2023717 = 379447) (by norm_num)
theorem B4047173 : Blo 1798100 4047173 := bbase (se 4 (by rfl) ⟨379422, by rfl⟩ : syracuseStep 4047173 = 758845) (by norm_num)
theorem B2023753 : Blo 1798100 2023753 := bbase (se 2 (by rfl) ⟨758907, by rfl⟩ : syracuseStep 2023753 = 1517815) (by norm_num)
theorem B3416413 : Blo 1798100 3416413 := bbase (se 3 (by rfl) ⟨640577, by rfl⟩ : syracuseStep 3416413 = 1281155) (by norm_num)
theorem B2023789 : Blo 1798100 2023789 := bbase (se 3 (by rfl) ⟨379460, by rfl⟩ : syracuseStep 2023789 = 758921) (by norm_num)
theorem B4047245 : Blo 1798100 4047245 := bbase (se 3 (by rfl) ⟨758858, by rfl⟩ : syracuseStep 4047245 = 1517717) (by norm_num)
theorem B2023825 : Blo 1798100 2023825 := bbase (se 2 (by rfl) ⟨758934, by rfl⟩ : syracuseStep 2023825 = 1517869) (by norm_num)
theorem B5120405 : Blo 1798100 5120405 := bbase (se 6 (by rfl) ⟨120009, by rfl⟩ : syracuseStep 5120405 = 240019) (by norm_num)
theorem B2023861 : Blo 1798100 2023861 := bbase (se 5 (by rfl) ⟨94868, by rfl⟩ : syracuseStep 2023861 = 189737) (by norm_num)
theorem B2277821 : Blo 1798100 2277821 := bbase (se 3 (by rfl) ⟨427091, by rfl⟩ : syracuseStep 2277821 = 854183) (by norm_num)
theorem B4047317 : Blo 1798100 4047317 := bbase (se 7 (by rfl) ⟨47429, by rfl⟩ : syracuseStep 4047317 = 94859) (by norm_num)
theorem B2023897 : Blo 1798100 2023897 := bbase (se 2 (by rfl) ⟨758961, by rfl⟩ : syracuseStep 2023897 = 1517923) (by norm_num)
theorem B3555805 : Blo 1798100 3555805 := bbase (se 3 (by rfl) ⟨666713, by rfl⟩ : syracuseStep 3555805 = 1333427) (by norm_num)
theorem B3842525 : Blo 1798100 3842525 := bbase (se 3 (by rfl) ⟨720473, by rfl⟩ : syracuseStep 3842525 = 1440947) (by norm_num)
theorem B6832613 : Blo 1798100 6832613 := bbase (se 4 (by rfl) ⟨640557, by rfl⟩ : syracuseStep 6832613 = 1281115) (by norm_num)
theorem B4555237 : Blo 1798100 4555237 := bbase (se 4 (by rfl) ⟨427053, by rfl⟩ : syracuseStep 4555237 = 854107) (by norm_num)
theorem B2277877 : Blo 1798100 2277877 := bbase (se 5 (by rfl) ⟨106775, by rfl⟩ : syracuseStep 2277877 = 213551) (by norm_num)
theorem B2023933 : Blo 1798100 2023933 := bbase (se 3 (by rfl) ⟨379487, by rfl⟩ : syracuseStep 2023933 = 758975) (by norm_num)
theorem B3416573 : Blo 1798100 3416573 := bbase (se 3 (by rfl) ⟨640607, by rfl⟩ : syracuseStep 3416573 = 1281215) (by norm_num)
theorem B4047389 : Blo 1798100 4047389 := bbase (se 3 (by rfl) ⟨758885, by rfl⟩ : syracuseStep 4047389 = 1517771) (by norm_num)
theorem B2023969 : Blo 1798100 2023969 := bbase (se 2 (by rfl) ⟨758988, by rfl⟩ : syracuseStep 2023969 = 1517977) (by norm_num)
theorem B3695149 : Blo 1798100 3695149 := bbase (se 3 (by rfl) ⟨692840, by rfl⟩ : syracuseStep 3695149 = 1385681) (by norm_num)
theorem B9110069 : Blo 1798100 9110069 := bbase (se 5 (by rfl) ⟨427034, by rfl⟩ : syracuseStep 9110069 = 854069) (by norm_num)
theorem B2024005 : Blo 1798100 2024005 := bbase (se 4 (by rfl) ⟨189750, by rfl⟩ : syracuseStep 2024005 = 379501) (by norm_num)
theorem B4555349 : Blo 1798100 4555349 := bbase (se 8 (by rfl) ⟨26691, by rfl⟩ : syracuseStep 4555349 = 53383) (by norm_num)
theorem B2277973 : Blo 1798100 2277973 := bbase (se 8 (by rfl) ⟨13347, by rfl⟩ : syracuseStep 2277973 = 26695) (by norm_num)
theorem B4047461 : Blo 1798100 4047461 := bbase (se 4 (by rfl) ⟨379449, by rfl⟩ : syracuseStep 4047461 = 758899) (by norm_num)
theorem B2024041 : Blo 1798100 2024041 := bbase (se 2 (by rfl) ⟨759015, by rfl⟩ : syracuseStep 2024041 = 1518031) (by norm_num)
theorem B2024077 : Blo 1798100 2024077 := bbase (se 3 (by rfl) ⟨379514, by rfl⟩ : syracuseStep 2024077 = 759029) (by norm_num)
theorem B3416717 : Blo 1798100 3416717 := bbase (se 3 (by rfl) ⟨640634, by rfl⟩ : syracuseStep 3416717 = 1281269) (by norm_num)
theorem B6070949 : Blo 1798100 6070949 := bbase (se 4 (by rfl) ⟨569151, by rfl⟩ : syracuseStep 6070949 = 1138303) (by norm_num)
theorem B4047533 : Blo 1798100 4047533 := bbase (se 3 (by rfl) ⟨758912, by rfl⟩ : syracuseStep 4047533 = 1517825) (by norm_num)
theorem B2024113 : Blo 1798100 2024113 := bbase (se 2 (by rfl) ⟨759042, by rfl⟩ : syracuseStep 2024113 = 1518085) (by norm_num)
theorem B2024149 : Blo 1798100 2024149 := bbase (se 7 (by rfl) ⟨23720, by rfl⟩ : syracuseStep 2024149 = 47441) (by norm_num)
theorem B4047605 : Blo 1798100 4047605 := bbase (se 5 (by rfl) ⟨189731, by rfl⟩ : syracuseStep 4047605 = 379463) (by norm_num)
theorem B2024185 : Blo 1798100 2024185 := bbase (se 2 (by rfl) ⟨759069, by rfl⟩ : syracuseStep 2024185 = 1518139) (by norm_num)
theorem B2278145 : Blo 1798100 2278145 := bbase (se 2 (by rfl) ⟨854304, by rfl⟩ : syracuseStep 2278145 = 1708609) (by norm_num)
theorem B4104965 : Blo 1798100 4104965 := bbase (se 4 (by rfl) ⟨384840, by rfl⟩ : syracuseStep 4104965 = 769681) (by norm_num)
theorem B4555541 : Blo 1798100 4555541 := bbase (se 6 (by rfl) ⟨106770, by rfl⟩ : syracuseStep 4555541 = 213541) (by norm_num)
theorem B2024221 : Blo 1798100 2024221 := bbase (se 3 (by rfl) ⟨379541, by rfl⟩ : syracuseStep 2024221 = 759083) (by norm_num)
theorem B2278201 : Blo 1798100 2278201 := bbase (se 2 (by rfl) ⟨854325, by rfl⟩ : syracuseStep 2278201 = 1708651) (by norm_num)
theorem B4047677 : Blo 1798100 4047677 := bbase (se 3 (by rfl) ⟨758939, by rfl⟩ : syracuseStep 4047677 = 1517879) (by norm_num)
theorem B2024257 : Blo 1798100 2024257 := bbase (se 2 (by rfl) ⟨759096, by rfl⟩ : syracuseStep 2024257 = 1518193) (by norm_num)
theorem B3842893 : Blo 1798100 3842893 := bbase (se 3 (by rfl) ⟨720542, by rfl⟩ : syracuseStep 3842893 = 1441085) (by norm_num)
theorem B17523541 : Blo 1798100 17523541 := bbase (se 9 (by rfl) ⟨51338, by rfl⟩ : syracuseStep 17523541 = 102677) (by norm_num)
theorem B2024293 : Blo 1798100 2024293 := bbase (se 4 (by rfl) ⟨189777, by rfl⟩ : syracuseStep 2024293 = 379555) (by norm_num)
theorem B4047749 : Blo 1798100 4047749 := bbase (se 4 (by rfl) ⟨379476, by rfl⟩ : syracuseStep 4047749 = 758953) (by norm_num)
theorem B2597765 : Blo 1798100 2597765 := bbase (se 4 (by rfl) ⟨243540, by rfl⟩ : syracuseStep 2597765 = 487081) (by norm_num)
theorem B2024329 : Blo 1798100 2024329 := bbase (se 2 (by rfl) ⟨759123, by rfl⟩ : syracuseStep 2024329 = 1518247) (by norm_num)
theorem B2024365 : Blo 1798100 2024365 := bbase (se 3 (by rfl) ⟨379568, by rfl⟩ : syracuseStep 2024365 = 759137) (by norm_num)
theorem B3417005 : Blo 1798100 3417005 := bbase (se 3 (by rfl) ⟨640688, by rfl⟩ : syracuseStep 3417005 = 1281377) (by norm_num)
theorem B4047821 : Blo 1798100 4047821 := bbase (se 3 (by rfl) ⟨758966, by rfl⟩ : syracuseStep 4047821 = 1517933) (by norm_num)
theorem B2024401 : Blo 1798100 2024401 := bbase (se 2 (by rfl) ⟨759150, by rfl⟩ : syracuseStep 2024401 = 1518301) (by norm_num)
theorem B17523701 : Blo 1798100 17523701 := bbase (se 5 (by rfl) ⟨821423, by rfl⟩ : syracuseStep 17523701 = 1642847) (by norm_num)
theorem B2024437 : Blo 1798100 2024437 := bbase (se 5 (by rfl) ⟨94895, by rfl⟩ : syracuseStep 2024437 = 189791) (by norm_num)
theorem B4047893 : Blo 1798100 4047893 := bbase (se 6 (by rfl) ⟨94872, by rfl⟩ : syracuseStep 4047893 = 189745) (by norm_num)
theorem B2024473 : Blo 1798100 2024473 := bbase (se 2 (by rfl) ⟨759177, by rfl⟩ : syracuseStep 2024473 = 1518355) (by norm_num)
theorem B2024509 : Blo 1798100 2024509 := bbase (se 3 (by rfl) ⟨379595, by rfl⟩ : syracuseStep 2024509 = 759191) (by norm_num)
theorem B3417157 : Blo 1798100 3417157 := bbase (se 4 (by rfl) ⟨320358, by rfl⟩ : syracuseStep 3417157 = 640717) (by norm_num)
theorem B10937429 : Blo 1798100 10937429 := bbase (se 8 (by rfl) ⟨64086, by rfl⟩ : syracuseStep 10937429 = 128173) (by norm_num)
theorem B6071381 : Blo 1798100 6071381 := bbase (se 8 (by rfl) ⟨35574, by rfl⟩ : syracuseStep 6071381 = 71149) (by norm_num)
theorem B4047965 : Blo 1798100 4047965 := bbase (se 3 (by rfl) ⟨758993, by rfl⟩ : syracuseStep 4047965 = 1517987) (by norm_num)
theorem B2024545 : Blo 1798100 2024545 := bbase (se 2 (by rfl) ⟨759204, by rfl⟩ : syracuseStep 2024545 = 1518409) (by norm_num)
theorem B4555885 : Blo 1798100 4555885 := bbase (se 3 (by rfl) ⟨854228, by rfl⟩ : syracuseStep 4555885 = 1708457) (by norm_num)
theorem B5121157 : Blo 1798100 5121157 := bbase (se 4 (by rfl) ⟨480108, by rfl⟩ : syracuseStep 5121157 = 960217) (by norm_num)
theorem B2024581 : Blo 1798100 2024581 := bbase (se 4 (by rfl) ⟨189804, by rfl⟩ : syracuseStep 2024581 = 379609) (by norm_num)
theorem B4105349 : Blo 1798100 4105349 := bbase (se 4 (by rfl) ⟨384876, by rfl⟩ : syracuseStep 4105349 = 769753) (by norm_num)
theorem B4048037 : Blo 1798100 4048037 := bbase (se 4 (by rfl) ⟨379503, by rfl⟩ : syracuseStep 4048037 = 759007) (by norm_num)
theorem B2024617 : Blo 1798100 2024617 := bbase (se 2 (by rfl) ⟨759231, by rfl⟩ : syracuseStep 2024617 = 1518463) (by norm_num)
theorem B2024653 : Blo 1798100 2024653 := bbase (se 3 (by rfl) ⟨379622, by rfl⟩ : syracuseStep 2024653 = 759245) (by norm_num)
theorem B4555997 : Blo 1798100 4555997 := bbase (se 3 (by rfl) ⟨854249, by rfl⟩ : syracuseStep 4555997 = 1708499) (by norm_num)
theorem B8209637 : Blo 1798100 8209637 := bbase (se 4 (by rfl) ⟨769653, by rfl⟩ : syracuseStep 8209637 = 1539307) (by norm_num)
theorem B4048109 : Blo 1798100 4048109 := bbase (se 3 (by rfl) ⟨759020, by rfl⟩ : syracuseStep 4048109 = 1518041) (by norm_num)
theorem B2024689 : Blo 1798100 2024689 := bbase (se 2 (by rfl) ⟨759258, by rfl⟩ : syracuseStep 2024689 = 1518517) (by norm_num)
theorem B3646709 : Blo 1798100 3646709 := bbase (se 5 (by rfl) ⟨170939, by rfl⟩ : syracuseStep 3646709 = 341879) (by norm_num)
theorem B2024725 : Blo 1798100 2024725 := bbase (se 6 (by rfl) ⟨47454, by rfl⟩ : syracuseStep 2024725 = 94909) (by norm_num)
theorem B4048181 : Blo 1798100 4048181 := bbase (se 5 (by rfl) ⟨189758, by rfl⟩ : syracuseStep 4048181 = 379517) (by norm_num)
theorem B2024761 : Blo 1798100 2024761 := bbase (se 2 (by rfl) ⟨759285, by rfl⟩ : syracuseStep 2024761 = 1518571) (by norm_num)
theorem B2024797 : Blo 1798100 2024797 := bbase (se 3 (by rfl) ⟨379649, by rfl⟩ : syracuseStep 2024797 = 759299) (by norm_num)
theorem B15582581 : Blo 1798100 15582581 := bbase (se 5 (by rfl) ⟨730433, by rfl⟩ : syracuseStep 15582581 = 1460867) (by norm_num)
theorem B4048253 : Blo 1798100 4048253 := bbase (se 3 (by rfl) ⟨759047, by rfl⟩ : syracuseStep 4048253 = 1518095) (by norm_num)
theorem B2024833 : Blo 1798100 2024833 := bbase (se 2 (by rfl) ⟨759312, by rfl⟩ : syracuseStep 2024833 = 1518625) (by norm_num)
theorem B4556189 : Blo 1798100 4556189 := bbase (se 3 (by rfl) ⟨854285, by rfl⟩ : syracuseStep 4556189 = 1708571) (by norm_num)
theorem B2024869 : Blo 1798100 2024869 := bbase (se 4 (by rfl) ⟨189831, by rfl⟩ : syracuseStep 2024869 = 379663) (by norm_num)
theorem B4048325 : Blo 1798100 4048325 := bbase (se 4 (by rfl) ⟨379530, by rfl⟩ : syracuseStep 4048325 = 759061) (by norm_num)
theorem B2024905 : Blo 1798100 2024905 := bbase (se 2 (by rfl) ⟨759339, by rfl⟩ : syracuseStep 2024905 = 1518679) (by norm_num)
theorem B2024941 : Blo 1798100 2024941 := bbase (se 3 (by rfl) ⟨379676, by rfl⟩ : syracuseStep 2024941 = 759353) (by norm_num)
theorem B6071813 : Blo 1798100 6071813 := bbase (se 4 (by rfl) ⟨569232, by rfl⟩ : syracuseStep 6071813 = 1138465) (by norm_num)
theorem B4048397 : Blo 1798100 4048397 := bbase (se 3 (by rfl) ⟨759074, by rfl⟩ : syracuseStep 4048397 = 1518149) (by norm_num)
theorem B2024977 : Blo 1798100 2024977 := bbase (se 2 (by rfl) ⟨759366, by rfl⟩ : syracuseStep 2024977 = 1518733) (by norm_num)
theorem B2025013 : Blo 1798100 2025013 := bbase (se 5 (by rfl) ⟨94922, by rfl⟩ : syracuseStep 2025013 = 189845) (by norm_num)
theorem B4048469 : Blo 1798100 4048469 := bbase (se 8 (by rfl) ⟨23721, by rfl⟩ : syracuseStep 4048469 = 47443) (by norm_num)
theorem B26297941 : Blo 1798100 26297941 := bbase (se 8 (by rfl) ⟨154089, by rfl⟩ : syracuseStep 26297941 = 308179) (by norm_num)
theorem B2025049 : Blo 1798100 2025049 := bbase (se 2 (by rfl) ⟨759393, by rfl⟩ : syracuseStep 2025049 = 1518787) (by norm_num)
theorem B2025085 : Blo 1798100 2025085 := bbase (se 3 (by rfl) ⟨379703, by rfl⟩ : syracuseStep 2025085 = 759407) (by norm_num)
theorem B5760661 : Blo 1798100 5760661 := bbase (se 6 (by rfl) ⟨135015, by rfl⟩ : syracuseStep 5760661 = 270031) (by norm_num)
theorem B4048541 : Blo 1798100 4048541 := bbase (se 3 (by rfl) ⟨759101, by rfl⟩ : syracuseStep 4048541 = 1518203) (by norm_num)
theorem B24610517 : Blo 1798100 24610517 := bbase (se 7 (by rfl) ⟨288404, by rfl⟩ : syracuseStep 24610517 = 576809) (by norm_num)
theorem B4048613 : Blo 1798100 4048613 := bbase (se 4 (by rfl) ⟨379557, by rfl⟩ : syracuseStep 4048613 = 759115) (by norm_num)
theorem B4048685 : Blo 1798100 4048685 := bbase (se 3 (by rfl) ⟨759128, by rfl⟩ : syracuseStep 4048685 = 1518257) (by norm_num)
theorem B9111365 : Blo 1798100 9111365 := bbase (se 4 (by rfl) ⟨854190, by rfl⟩ : syracuseStep 9111365 = 1708381) (by norm_num)
theorem B4048757 : Blo 1798100 4048757 := bbase (se 5 (by rfl) ⟨189785, by rfl⟩ : syracuseStep 4048757 = 379571) (by norm_num)
theorem B6072245 : Blo 1798100 6072245 := bbase (se 5 (by rfl) ⟨284636, by rfl⟩ : syracuseStep 6072245 = 569273) (by norm_num)
theorem B4048829 : Blo 1798100 4048829 := bbase (se 3 (by rfl) ⟨759155, by rfl⟩ : syracuseStep 4048829 = 1518311) (by norm_num)
theorem B2697173 : Blo 1798100 2697173 := bbase (se 7 (by rfl) ⟨31607, by rfl⟩ : syracuseStep 2697173 = 63215) (by norm_num)
theorem B2697197 : Blo 1798100 2697197 := bbase (se 3 (by rfl) ⟨505724, by rfl⟩ : syracuseStep 2697197 = 1011449) (by norm_num)
theorem B12961781 : Blo 1798100 12961781 := bbase (se 5 (by rfl) ⟨607583, by rfl⟩ : syracuseStep 12961781 = 1215167) (by norm_num)
theorem B4679677 : Blo 1798100 4679677 := bbase (se 3 (by rfl) ⟨877439, by rfl⟩ : syracuseStep 4679677 = 1754879) (by norm_num)
theorem B2697221 : Blo 1798100 2697221 := bbase (se 4 (by rfl) ⟨252864, by rfl⟩ : syracuseStep 2697221 = 505729) (by norm_num)
theorem B4048901 : Blo 1798100 4048901 := bbase (se 4 (by rfl) ⟨379584, by rfl⟩ : syracuseStep 4048901 = 759169) (by norm_num)
theorem B2697245 : Blo 1798100 2697245 := bbase (se 3 (by rfl) ⟨505733, by rfl⟩ : syracuseStep 2697245 = 1011467) (by norm_num)
theorem B2697269 : Blo 1798100 2697269 := bbase (se 5 (by rfl) ⟨126434, by rfl⟩ : syracuseStep 2697269 = 252869) (by norm_num)
theorem B7686197 : Blo 1798100 7686197 := bbase (se 5 (by rfl) ⟨360290, by rfl⟩ : syracuseStep 7686197 = 720581) (by norm_num)
theorem B2697293 : Blo 1798100 2697293 := bbase (se 3 (by rfl) ⟨505742, by rfl⟩ : syracuseStep 2697293 = 1011485) (by norm_num)
theorem B4048973 : Blo 1798100 4048973 := bbase (se 3 (by rfl) ⟨759182, by rfl⟩ : syracuseStep 4048973 = 1518365) (by norm_num)
theorem B2697317 : Blo 1798100 2697317 := bbase (se 4 (by rfl) ⟨252873, by rfl⟩ : syracuseStep 2697317 = 505747) (by norm_num)
theorem B2697341 : Blo 1798100 2697341 := bbase (se 3 (by rfl) ⟨505751, by rfl⟩ : syracuseStep 2697341 = 1011503) (by norm_num)
theorem B2697365 : Blo 1798100 2697365 := bbase (se 6 (by rfl) ⟨63219, by rfl⟩ : syracuseStep 2697365 = 126439) (by norm_num)
theorem B4049045 : Blo 1798100 4049045 := bbase (se 6 (by rfl) ⟨94899, by rfl⟩ : syracuseStep 4049045 = 189799) (by norm_num)
theorem B2697389 : Blo 1798100 2697389 := bbase (se 3 (by rfl) ⟨505760, by rfl⟩ : syracuseStep 2697389 = 1011521) (by norm_num)
theorem B3287213 : Blo 1798100 3287213 := bbase (se 3 (by rfl) ⟨616352, by rfl⟩ : syracuseStep 3287213 = 1232705) (by norm_num)
theorem B3893429 : Blo 1798100 3893429 := bbase (se 5 (by rfl) ⟨182504, by rfl⟩ : syracuseStep 3893429 = 365009) (by norm_num)
theorem B2697413 : Blo 1798100 2697413 := bbase (se 4 (by rfl) ⟨252882, by rfl⟩ : syracuseStep 2697413 = 505765) (by norm_num)
theorem B2697437 : Blo 1798100 2697437 := bbase (se 3 (by rfl) ⟨505769, by rfl⟩ : syracuseStep 2697437 = 1011539) (by norm_num)
theorem B4049117 : Blo 1798100 4049117 := bbase (se 3 (by rfl) ⟨759209, by rfl⟩ : syracuseStep 4049117 = 1518419) (by norm_num)
theorem B9103589 : Blo 1798100 9103589 := bbase (se 4 (by rfl) ⟨853461, by rfl⟩ : syracuseStep 9103589 = 1706923) (by norm_num)
theorem B2697461 : Blo 1798100 2697461 := bbase (se 5 (by rfl) ⟨126443, by rfl⟩ : syracuseStep 2697461 = 252887) (by norm_num)
theorem B2697485 : Blo 1798100 2697485 := bbase (se 3 (by rfl) ⟨505778, by rfl⟩ : syracuseStep 2697485 = 1011557) (by norm_num)
theorem B2697509 : Blo 1798100 2697509 := bbase (se 4 (by rfl) ⟨252891, by rfl⟩ : syracuseStep 2697509 = 505783) (by norm_num)
theorem B4049189 : Blo 1798100 4049189 := bbase (se 4 (by rfl) ⟨379611, by rfl⟩ : syracuseStep 4049189 = 759223) (by norm_num)
theorem B3844397 : Blo 1798100 3844397 := bbase (se 3 (by rfl) ⟨720824, by rfl⟩ : syracuseStep 3844397 = 1441649) (by norm_num)
theorem B2697533 : Blo 1798100 2697533 := bbase (se 3 (by rfl) ⟨505787, by rfl⟩ : syracuseStep 2697533 = 1011575) (by norm_num)
theorem B2697557 : Blo 1798100 2697557 := bbase (se 10 (by rfl) ⟨3951, by rfl⟩ : syracuseStep 2697557 = 7903) (by norm_num)
theorem B7686485 : Blo 1798100 7686485 := bbase (se 10 (by rfl) ⟨11259, by rfl⟩ : syracuseStep 7686485 = 22519) (by norm_num)
theorem B6072677 : Blo 1798100 6072677 := bbase (se 4 (by rfl) ⟨569313, by rfl⟩ : syracuseStep 6072677 = 1138627) (by norm_num)
theorem B2697581 : Blo 1798100 2697581 := bbase (se 3 (by rfl) ⟨505796, by rfl⟩ : syracuseStep 2697581 = 1011593) (by norm_num)
theorem B4049261 : Blo 1798100 4049261 := bbase (se 3 (by rfl) ⟨759236, by rfl⟩ : syracuseStep 4049261 = 1518473) (by norm_num)
theorem B2697605 : Blo 1798100 2697605 := bbase (se 4 (by rfl) ⟨252900, by rfl⟩ : syracuseStep 2697605 = 505801) (by norm_num)
theorem B2697629 : Blo 1798100 2697629 := bbase (se 3 (by rfl) ⟨505805, by rfl⟩ : syracuseStep 2697629 = 1011611) (by norm_num)
theorem B2697653 : Blo 1798100 2697653 := bbase (se 5 (by rfl) ⟨126452, by rfl⟩ : syracuseStep 2697653 = 252905) (by norm_num)
theorem B4049333 : Blo 1798100 4049333 := bbase (se 5 (by rfl) ⟨189812, by rfl⟩ : syracuseStep 4049333 = 379625) (by norm_num)
theorem B3844541 : Blo 1798100 3844541 := bbase (se 3 (by rfl) ⟨720851, by rfl⟩ : syracuseStep 3844541 = 1441703) (by norm_num)
theorem B2697677 : Blo 1798100 2697677 := bbase (se 3 (by rfl) ⟨505814, by rfl⟩ : syracuseStep 2697677 = 1011629) (by norm_num)
theorem B6482389 : Blo 1798100 6482389 := bbase (se 7 (by rfl) ⟨75965, by rfl⟩ : syracuseStep 6482389 = 151931) (by norm_num)
theorem B2697701 : Blo 1798100 2697701 := bbase (se 4 (by rfl) ⟨252909, by rfl⟩ : syracuseStep 2697701 = 505819) (by norm_num)
theorem B3893741 : Blo 1798100 3893741 := bbase (se 3 (by rfl) ⟨730076, by rfl⟩ : syracuseStep 3893741 = 1460153) (by norm_num)
theorem B13666805 : Blo 1798100 13666805 := bbase (se 5 (by rfl) ⟨640631, by rfl⟩ : syracuseStep 13666805 = 1281263) (by norm_num)
theorem B2697725 : Blo 1798100 2697725 := bbase (se 3 (by rfl) ⟨505823, by rfl⟩ : syracuseStep 2697725 = 1011647) (by norm_num)
theorem B4049405 : Blo 1798100 4049405 := bbase (se 3 (by rfl) ⟨759263, by rfl⟩ : syracuseStep 4049405 = 1518527) (by norm_num)
theorem B15362581 : Blo 1798100 15362581 := bbase (se 6 (by rfl) ⟨360060, by rfl⟩ : syracuseStep 15362581 = 720121) (by norm_num)
theorem B2697749 : Blo 1798100 2697749 := bbase (se 6 (by rfl) ⟨63228, by rfl⟩ : syracuseStep 2697749 = 126457) (by norm_num)
theorem B6834725 : Blo 1798100 6834725 := bbase (se 4 (by rfl) ⟨640755, by rfl⟩ : syracuseStep 6834725 = 1281511) (by norm_num)
theorem B2697773 : Blo 1798100 2697773 := bbase (se 3 (by rfl) ⟨505832, by rfl⟩ : syracuseStep 2697773 = 1011665) (by norm_num)
theorem B2697797 : Blo 1798100 2697797 := bbase (se 4 (by rfl) ⟨252918, by rfl⟩ : syracuseStep 2697797 = 505837) (by norm_num)
theorem B4049477 : Blo 1798100 4049477 := bbase (se 4 (by rfl) ⟨379638, by rfl⟩ : syracuseStep 4049477 = 759277) (by norm_num)
theorem B2697821 : Blo 1798100 2697821 := bbase (se 3 (by rfl) ⟨505841, by rfl⟩ : syracuseStep 2697821 = 1011683) (by norm_num)
theorem B2697845 : Blo 1798100 2697845 := bbase (se 5 (by rfl) ⟨126461, by rfl⟩ : syracuseStep 2697845 = 252923) (by norm_num)
theorem B2697869 : Blo 1798100 2697869 := bbase (se 3 (by rfl) ⟨505850, by rfl⟩ : syracuseStep 2697869 = 1011701) (by norm_num)
theorem B4049549 : Blo 1798100 4049549 := bbase (se 3 (by rfl) ⟨759290, by rfl⟩ : syracuseStep 4049549 = 1518581) (by norm_num)
theorem B2697893 : Blo 1798100 2697893 := bbase (se 4 (by rfl) ⟨252927, by rfl⟩ : syracuseStep 2697893 = 505855) (by norm_num)
theorem B2697917 : Blo 1798100 2697917 := bbase (se 3 (by rfl) ⟨505859, by rfl⟩ : syracuseStep 2697917 = 1011719) (by norm_num)
theorem B2697941 : Blo 1798100 2697941 := bbase (se 7 (by rfl) ⟨31616, by rfl⟩ : syracuseStep 2697941 = 63233) (by norm_num)
theorem B4049621 : Blo 1798100 4049621 := bbase (se 7 (by rfl) ⟨47456, by rfl⟩ : syracuseStep 4049621 = 94913) (by norm_num)
theorem B2697965 : Blo 1798100 2697965 := bbase (se 3 (by rfl) ⟨505868, by rfl⟩ : syracuseStep 2697965 = 1011737) (by norm_num)
theorem B2697989 : Blo 1798100 2697989 := bbase (se 4 (by rfl) ⟨252936, by rfl⟩ : syracuseStep 2697989 = 505873) (by norm_num)
theorem B6073109 : Blo 1798100 6073109 := bbase (se 6 (by rfl) ⟨142338, by rfl⟩ : syracuseStep 6073109 = 284677) (by norm_num)
theorem B2698013 : Blo 1798100 2698013 := bbase (se 3 (by rfl) ⟨505877, by rfl⟩ : syracuseStep 2698013 = 1011755) (by norm_num)
theorem B4049693 : Blo 1798100 4049693 := bbase (se 3 (by rfl) ⟨759317, by rfl⟩ : syracuseStep 4049693 = 1518635) (by norm_num)
theorem B2698037 : Blo 1798100 2698037 := bbase (se 5 (by rfl) ⟨126470, by rfl⟩ : syracuseStep 2698037 = 252941) (by norm_num)
theorem B3894077 : Blo 1798100 3894077 := bbase (se 3 (by rfl) ⟨730139, by rfl⟩ : syracuseStep 3894077 = 1460279) (by norm_num)
theorem B2698061 : Blo 1798100 2698061 := bbase (se 3 (by rfl) ⟨505886, by rfl⟩ : syracuseStep 2698061 = 1011773) (by norm_num)
theorem B2698085 : Blo 1798100 2698085 := bbase (se 4 (by rfl) ⟨252945, by rfl⟩ : syracuseStep 2698085 = 505891) (by norm_num)
theorem B4049765 : Blo 1798100 4049765 := bbase (se 4 (by rfl) ⟨379665, by rfl⟩ : syracuseStep 4049765 = 759331) (by norm_num)
theorem B2698109 : Blo 1798100 2698109 := bbase (se 3 (by rfl) ⟨505895, by rfl⟩ : syracuseStep 2698109 = 1011791) (by norm_num)
theorem B8203141 : Blo 1798100 8203141 := bbase (se 4 (by rfl) ⟨769044, by rfl⟩ : syracuseStep 8203141 = 1538089) (by norm_num)
theorem B13659029 : Blo 1798100 13659029 := bbase (se 6 (by rfl) ⟨320133, by rfl⟩ : syracuseStep 13659029 = 640267) (by norm_num)
theorem B2698133 : Blo 1798100 2698133 := bbase (se 6 (by rfl) ⟨63237, by rfl⟩ : syracuseStep 2698133 = 126475) (by norm_num)
theorem B2698157 : Blo 1798100 2698157 := bbase (se 3 (by rfl) ⟨505904, by rfl⟩ : syracuseStep 2698157 = 1011809) (by norm_num)
theorem B4049837 : Blo 1798100 4049837 := bbase (se 3 (by rfl) ⟨759344, by rfl⟩ : syracuseStep 4049837 = 1518689) (by norm_num)
theorem B2698181 : Blo 1798100 2698181 := bbase (se 4 (by rfl) ⟨252954, by rfl⟩ : syracuseStep 2698181 = 505909) (by norm_num)
theorem B2698205 : Blo 1798100 2698205 := bbase (se 3 (by rfl) ⟨505913, by rfl⟩ : syracuseStep 2698205 = 1011827) (by norm_num)
theorem B2698229 : Blo 1798100 2698229 := bbase (se 5 (by rfl) ⟨126479, by rfl⟩ : syracuseStep 2698229 = 252959) (by norm_num)
theorem B4049909 : Blo 1798100 4049909 := bbase (se 5 (by rfl) ⟨189839, by rfl⟩ : syracuseStep 4049909 = 379679) (by norm_num)
theorem B2698253 : Blo 1798100 2698253 := bbase (se 3 (by rfl) ⟨505922, by rfl⟩ : syracuseStep 2698253 = 1011845) (by norm_num)
theorem B3894293 : Blo 1798100 3894293 := bbase (se 6 (by rfl) ⟨91272, by rfl⟩ : syracuseStep 3894293 = 182545) (by norm_num)
theorem B2698277 : Blo 1798100 2698277 := bbase (se 4 (by rfl) ⟨252963, by rfl⟩ : syracuseStep 2698277 = 505927) (by norm_num)
theorem B2051129 : Blo 1798100 2051129 := bbase (se 2 (by rfl) ⟨769173, by rfl⟩ : syracuseStep 2051129 = 1538347) (by norm_num)
theorem B2698301 : Blo 1798100 2698301 := bbase (se 3 (by rfl) ⟨505931, by rfl⟩ : syracuseStep 2698301 = 1011863) (by norm_num)
theorem B4049981 : Blo 1798100 4049981 := bbase (se 3 (by rfl) ⟨759371, by rfl⟩ : syracuseStep 4049981 = 1518743) (by norm_num)
theorem B7687237 : Blo 1798100 7687237 := bbase (se 4 (by rfl) ⟨720678, by rfl⟩ : syracuseStep 7687237 = 1441357) (by norm_num)
theorem B2698325 : Blo 1798100 2698325 := bbase (se 8 (by rfl) ⟨15810, by rfl⟩ : syracuseStep 2698325 = 31621) (by norm_num)
theorem B9112661 : Blo 1798100 9112661 := bbase (se 8 (by rfl) ⟨53394, by rfl⟩ : syracuseStep 9112661 = 106789) (by norm_num)
theorem B2698349 : Blo 1798100 2698349 := bbase (se 3 (by rfl) ⟨505940, by rfl⟩ : syracuseStep 2698349 = 1011881) (by norm_num)
theorem B2698373 : Blo 1798100 2698373 := bbase (se 4 (by rfl) ⟨252972, by rfl⟩ : syracuseStep 2698373 = 505945) (by norm_num)
theorem B4050053 : Blo 1798100 4050053 := bbase (se 4 (by rfl) ⟨379692, by rfl⟩ : syracuseStep 4050053 = 759385) (by norm_num)
theorem B2698397 : Blo 1798100 2698397 := bbase (se 3 (by rfl) ⟨505949, by rfl⟩ : syracuseStep 2698397 = 1011899) (by norm_num)
theorem B1920169 : Blo 1798100 1920169 := bbase (se 2 (by rfl) ⟨720063, by rfl⟩ : syracuseStep 1920169 = 1440127) (by norm_num)
theorem B2698421 : Blo 1798100 2698421 := bbase (se 5 (by rfl) ⟨126488, by rfl⟩ : syracuseStep 2698421 = 252977) (by norm_num)
theorem B2772157 : Blo 1798100 2772157 := bbase (se 3 (by rfl) ⟨519779, by rfl⟩ : syracuseStep 2772157 = 1039559) (by norm_num)
theorem B6073541 : Blo 1798100 6073541 := bbase (se 4 (by rfl) ⟨569394, by rfl⟩ : syracuseStep 6073541 = 1138789) (by norm_num)
theorem B2698445 : Blo 1798100 2698445 := bbase (se 3 (by rfl) ⟨505958, by rfl⟩ : syracuseStep 2698445 = 1011917) (by norm_num)
theorem B4050125 : Blo 1798100 4050125 := bbase (se 3 (by rfl) ⟨759398, by rfl⟩ : syracuseStep 4050125 = 1518797) (by norm_num)
theorem B6827237 : Blo 1798100 6827237 := bbase (se 4 (by rfl) ⟨640053, by rfl⟩ : syracuseStep 6827237 = 1280107) (by norm_num)
theorem B2698469 : Blo 1798100 2698469 := bbase (se 4 (by rfl) ⟨252981, by rfl⟩ : syracuseStep 2698469 = 505963) (by norm_num)
theorem B2698493 : Blo 1798100 2698493 := bbase (se 3 (by rfl) ⟨505967, by rfl⟩ : syracuseStep 2698493 = 1011935) (by norm_num)
theorem B3034381 : Blo 1798100 3034381 := bbase (se 3 (by rfl) ⟨568946, by rfl⟩ : syracuseStep 3034381 = 1137893) (by norm_num)
theorem B2698517 : Blo 1798100 2698517 := bbase (se 6 (by rfl) ⟨63246, by rfl⟩ : syracuseStep 2698517 = 126493) (by norm_num)
theorem B4050197 : Blo 1798100 4050197 := bbase (se 6 (by rfl) ⟨94926, by rfl⟩ : syracuseStep 4050197 = 189853) (by norm_num)
theorem B2051369 : Blo 1798100 2051369 := bbase (se 2 (by rfl) ⟨769263, by rfl⟩ : syracuseStep 2051369 = 1538527) (by norm_num)
theorem B2698541 : Blo 1798100 2698541 := bbase (se 3 (by rfl) ⟨505976, by rfl⟩ : syracuseStep 2698541 = 1011953) (by norm_num)
theorem B2698565 : Blo 1798100 2698565 := bbase (se 4 (by rfl) ⟨252990, by rfl⟩ : syracuseStep 2698565 = 505981) (by norm_num)
theorem B2698589 : Blo 1798100 2698589 := bbase (se 3 (by rfl) ⟨505985, by rfl⟩ : syracuseStep 2698589 = 1011971) (by norm_num)
theorem B1920353 : Blo 1798100 1920353 := bbase (se 2 (by rfl) ⟨720132, by rfl⟩ : syracuseStep 1920353 = 1440265) (by norm_num)
theorem B3034469 : Blo 1798100 3034469 := bbase (se 4 (by rfl) ⟨284481, by rfl⟩ : syracuseStep 3034469 = 568963) (by norm_num)
theorem B2698613 : Blo 1798100 2698613 := bbase (se 5 (by rfl) ⟨126497, by rfl⟩ : syracuseStep 2698613 = 252995) (by norm_num)
theorem B2698637 : Blo 1798100 2698637 := bbase (se 3 (by rfl) ⟨505994, by rfl⟩ : syracuseStep 2698637 = 1011989) (by norm_num)
theorem B2698661 : Blo 1798100 2698661 := bbase (se 4 (by rfl) ⟨252999, by rfl⟩ : syracuseStep 2698661 = 505999) (by norm_num)
theorem B2698685 : Blo 1798100 2698685 := bbase (se 3 (by rfl) ⟨506003, by rfl⟩ : syracuseStep 2698685 = 1012007) (by norm_num)
theorem B2698709 : Blo 1798100 2698709 := bbase (se 7 (by rfl) ⟨31625, by rfl⟩ : syracuseStep 2698709 = 63251) (by norm_num)
theorem B42118613 : Blo 1798100 42118613 := bbase (se 7 (by rfl) ⟨493577, by rfl⟩ : syracuseStep 42118613 = 987155) (by norm_num)
theorem B3034597 : Blo 1798100 3034597 := bbase (se 4 (by rfl) ⟨284493, by rfl⟩ : syracuseStep 3034597 = 568987) (by norm_num)
theorem B2698733 : Blo 1798100 2698733 := bbase (se 3 (by rfl) ⟨506012, by rfl⟩ : syracuseStep 2698733 = 1012025) (by norm_num)
theorem B9104885 : Blo 1798100 9104885 := bbase (se 5 (by rfl) ⟨426791, by rfl⟩ : syracuseStep 9104885 = 853583) (by norm_num)
theorem B2698757 : Blo 1798100 2698757 := bbase (se 4 (by rfl) ⟨253008, by rfl⟩ : syracuseStep 2698757 = 506017) (by norm_num)
theorem B2698781 : Blo 1798100 2698781 := bbase (se 3 (by rfl) ⟨506021, by rfl⟩ : syracuseStep 2698781 = 1012043) (by norm_num)
theorem B2698805 : Blo 1798100 2698805 := bbase (se 5 (by rfl) ⟨126506, by rfl⟩ : syracuseStep 2698805 = 253013) (by norm_num)
theorem B3034685 : Blo 1798100 3034685 := bbase (se 3 (by rfl) ⟨569003, by rfl⟩ : syracuseStep 3034685 = 1138007) (by norm_num)
theorem B2698829 : Blo 1798100 2698829 := bbase (se 3 (by rfl) ⟨506030, by rfl⟩ : syracuseStep 2698829 = 1012061) (by norm_num)
theorem B2698853 : Blo 1798100 2698853 := bbase (se 4 (by rfl) ⟨253017, by rfl⟩ : syracuseStep 2698853 = 506035) (by norm_num)
theorem B6073973 : Blo 1798100 6073973 := bbase (se 5 (by rfl) ⟨284717, by rfl⟩ : syracuseStep 6073973 = 569435) (by norm_num)
theorem B2698877 : Blo 1798100 2698877 := bbase (se 3 (by rfl) ⟨506039, by rfl⟩ : syracuseStep 2698877 = 1012079) (by norm_num)
theorem B2698901 : Blo 1798100 2698901 := bbase (se 6 (by rfl) ⟨63255, by rfl⟩ : syracuseStep 2698901 = 126511) (by norm_num)
theorem B2698925 : Blo 1798100 2698925 := bbase (se 3 (by rfl) ⟨506048, by rfl⟩ : syracuseStep 2698925 = 1012097) (by norm_num)
theorem B3034813 : Blo 1798100 3034813 := bbase (se 3 (by rfl) ⟨569027, by rfl⟩ : syracuseStep 3034813 = 1138055) (by norm_num)
theorem B2698949 : Blo 1798100 2698949 := bbase (se 4 (by rfl) ⟨253026, by rfl⟩ : syracuseStep 2698949 = 506053) (by norm_num)
theorem B2051785 : Blo 1798100 2051785 := bbase (se 2 (by rfl) ⟨769419, by rfl⟩ : syracuseStep 2051785 = 1538839) (by norm_num)
theorem B2698973 : Blo 1798100 2698973 := bbase (se 3 (by rfl) ⟨506057, by rfl⟩ : syracuseStep 2698973 = 1012115) (by norm_num)
theorem B8646373 : Blo 1798100 8646373 := bbase (se 4 (by rfl) ⟨810597, by rfl⟩ : syracuseStep 8646373 = 1621195) (by norm_num)
theorem B2698997 : Blo 1798100 2698997 := bbase (se 5 (by rfl) ⟨126515, by rfl⟩ : syracuseStep 2698997 = 253031) (by norm_num)
theorem B2699021 : Blo 1798100 2699021 := bbase (se 3 (by rfl) ⟨506066, by rfl⟩ : syracuseStep 2699021 = 1012133) (by norm_num)
theorem B3034901 : Blo 1798100 3034901 := bbase (se 6 (by rfl) ⟨71130, by rfl⟩ : syracuseStep 3034901 = 142261) (by norm_num)
theorem B2699045 : Blo 1798100 2699045 := bbase (se 4 (by rfl) ⟨253035, by rfl⟩ : syracuseStep 2699045 = 506071) (by norm_num)
theorem B7687973 : Blo 1798100 7687973 := bbase (se 4 (by rfl) ⟨720747, by rfl⟩ : syracuseStep 7687973 = 1441495) (by norm_num)
theorem B2699069 : Blo 1798100 2699069 := bbase (se 3 (by rfl) ⟨506075, by rfl⟩ : syracuseStep 2699069 = 1012151) (by norm_num)
theorem B2699093 : Blo 1798100 2699093 := bbase (se 9 (by rfl) ⟨7907, by rfl⟩ : syracuseStep 2699093 = 15815) (by norm_num)
theorem B2191213 : Blo 1798100 2191213 := bbase (se 3 (by rfl) ⟨410852, by rfl⟩ : syracuseStep 2191213 = 821705) (by norm_num)
theorem B2699117 : Blo 1798100 2699117 := bbase (se 3 (by rfl) ⟨506084, by rfl⟩ : syracuseStep 2699117 = 1012169) (by norm_num)
theorem B2699141 : Blo 1798100 2699141 := bbase (se 4 (by rfl) ⟨253044, by rfl⟩ : syracuseStep 2699141 = 506089) (by norm_num)
theorem B3035029 : Blo 1798100 3035029 := bbase (se 6 (by rfl) ⟨71133, by rfl⟩ : syracuseStep 3035029 = 142267) (by norm_num)
theorem B2699165 : Blo 1798100 2699165 := bbase (se 3 (by rfl) ⟨506093, by rfl⟩ : syracuseStep 2699165 = 1012187) (by norm_num)
theorem B5124005 : Blo 1798100 5124005 := bbase (se 4 (by rfl) ⟨480375, by rfl⟩ : syracuseStep 5124005 = 960751) (by norm_num)
theorem B2699189 : Blo 1798100 2699189 := bbase (se 5 (by rfl) ⟨126524, by rfl⟩ : syracuseStep 2699189 = 253049) (by norm_num)
theorem B2699213 : Blo 1798100 2699213 := bbase (se 3 (by rfl) ⟨506102, by rfl⟩ : syracuseStep 2699213 = 1012205) (by norm_num)
theorem B2699237 : Blo 1798100 2699237 := bbase (se 4 (by rfl) ⟨253053, by rfl⟩ : syracuseStep 2699237 = 506107) (by norm_num)
theorem B3035117 : Blo 1798100 3035117 := bbase (se 3 (by rfl) ⟨569084, by rfl⟩ : syracuseStep 3035117 = 1138169) (by norm_num)
theorem B2699261 : Blo 1798100 2699261 := bbase (se 3 (by rfl) ⟨506111, by rfl⟩ : syracuseStep 2699261 = 1012223) (by norm_num)
theorem B8204309 : Blo 1798100 8204309 := bbase (se 6 (by rfl) ⟨192288, by rfl⟩ : syracuseStep 8204309 = 384577) (by norm_num)
theorem B2699285 : Blo 1798100 2699285 := bbase (se 6 (by rfl) ⟨63264, by rfl⟩ : syracuseStep 2699285 = 126529) (by norm_num)
theorem B6074405 : Blo 1798100 6074405 := bbase (se 4 (by rfl) ⟨569475, by rfl⟩ : syracuseStep 6074405 = 1138951) (by norm_num)
theorem B2699309 : Blo 1798100 2699309 := bbase (se 3 (by rfl) ⟨506120, by rfl⟩ : syracuseStep 2699309 = 1012241) (by norm_num)
theorem B2699333 : Blo 1798100 2699333 := bbase (se 4 (by rfl) ⟨253062, by rfl⟩ : syracuseStep 2699333 = 506125) (by norm_num)
theorem B1921105 : Blo 1798100 1921105 := bbase (se 2 (by rfl) ⟨720414, by rfl⟩ : syracuseStep 1921105 = 1440829) (by norm_num)
theorem B2699357 : Blo 1798100 2699357 := bbase (se 3 (by rfl) ⟨506129, by rfl⟩ : syracuseStep 2699357 = 1012259) (by norm_num)
theorem B3035245 : Blo 1798100 3035245 := bbase (se 3 (by rfl) ⟨569108, by rfl⟩ : syracuseStep 3035245 = 1138217) (by norm_num)
theorem B2699381 : Blo 1798100 2699381 := bbase (se 5 (by rfl) ⟨126533, by rfl⟩ : syracuseStep 2699381 = 253067) (by norm_num)
theorem B2699405 : Blo 1798100 2699405 := bbase (se 3 (by rfl) ⟨506138, by rfl⟩ : syracuseStep 2699405 = 1012277) (by norm_num)
theorem B32452757 : Blo 1798100 32452757 := bbase (se 6 (by rfl) ⟨760611, by rfl⟩ : syracuseStep 32452757 = 1521223) (by norm_num)
theorem B1921177 : Blo 1798100 1921177 := bbase (se 2 (by rfl) ⟨720441, by rfl⟩ : syracuseStep 1921177 = 1440883) (by norm_num)
theorem B2699429 : Blo 1798100 2699429 := bbase (se 4 (by rfl) ⟨253071, by rfl⟩ : syracuseStep 2699429 = 506143) (by norm_num)
theorem B2699453 : Blo 1798100 2699453 := bbase (se 3 (by rfl) ⟨506147, by rfl⟩ : syracuseStep 2699453 = 1012295) (by norm_num)
theorem B3035333 : Blo 1798100 3035333 := bbase (se 4 (by rfl) ⟨284562, by rfl⟩ : syracuseStep 3035333 = 569125) (by norm_num)
theorem B2699477 : Blo 1798100 2699477 := bbase (se 7 (by rfl) ⟨31634, by rfl⟩ : syracuseStep 2699477 = 63269) (by norm_num)
theorem B2699501 : Blo 1798100 2699501 := bbase (se 3 (by rfl) ⟨506156, by rfl⟩ : syracuseStep 2699501 = 1012313) (by norm_num)
theorem B2699525 : Blo 1798100 2699525 := bbase (se 4 (by rfl) ⟨253080, by rfl⟩ : syracuseStep 2699525 = 506161) (by norm_num)
theorem B2699549 : Blo 1798100 2699549 := bbase (se 3 (by rfl) ⟨506165, by rfl⟩ : syracuseStep 2699549 = 1012331) (by norm_num)
theorem B2699573 : Blo 1798100 2699573 := bbase (se 5 (by rfl) ⟨126542, by rfl⟩ : syracuseStep 2699573 = 253085) (by norm_num)
theorem B3035461 : Blo 1798100 3035461 := bbase (se 4 (by rfl) ⟨284574, by rfl⟩ : syracuseStep 3035461 = 569149) (by norm_num)
theorem B1921357 : Blo 1798100 1921357 := bbase (se 3 (by rfl) ⟨360254, by rfl⟩ : syracuseStep 1921357 = 720509) (by norm_num)
theorem B2699597 : Blo 1798100 2699597 := bbase (se 3 (by rfl) ⟨506174, by rfl⟩ : syracuseStep 2699597 = 1012349) (by norm_num)
theorem B2773333 : Blo 1798100 2773333 := bbase (se 10 (by rfl) ⟨4062, by rfl⟩ : syracuseStep 2773333 = 8125) (by norm_num)
theorem B2699621 : Blo 1798100 2699621 := bbase (se 4 (by rfl) ⟨253089, by rfl⟩ : syracuseStep 2699621 = 506179) (by norm_num)
theorem B2699645 : Blo 1798100 2699645 := bbase (se 3 (by rfl) ⟨506183, by rfl⟩ : syracuseStep 2699645 = 1012367) (by norm_num)
theorem B6828421 : Blo 1798100 6828421 := bbase (se 4 (by rfl) ⟨640164, by rfl⟩ : syracuseStep 6828421 = 1280329) (by norm_num)
theorem B10244501 : Blo 1798100 10244501 := bbase (se 6 (by rfl) ⟨240105, by rfl⟩ : syracuseStep 10244501 = 480211) (by norm_num)
theorem B2699669 : Blo 1798100 2699669 := bbase (se 6 (by rfl) ⟨63273, by rfl⟩ : syracuseStep 2699669 = 126547) (by norm_num)
theorem B3035549 : Blo 1798100 3035549 := bbase (se 3 (by rfl) ⟨569165, by rfl⟩ : syracuseStep 3035549 = 1138331) (by norm_num)
theorem B2699693 : Blo 1798100 2699693 := bbase (se 3 (by rfl) ⟨506192, by rfl⟩ : syracuseStep 2699693 = 1012385) (by norm_num)
theorem B6484421 : Blo 1798100 6484421 := bbase (se 4 (by rfl) ⟨607914, by rfl⟩ : syracuseStep 6484421 = 1215829) (by norm_num)
theorem B2699717 : Blo 1798100 2699717 := bbase (se 4 (by rfl) ⟨253098, by rfl⟩ : syracuseStep 2699717 = 506197) (by norm_num)
theorem B15364565 : Blo 1798100 15364565 := bbase (se 7 (by rfl) ⟨180053, by rfl⟩ : syracuseStep 15364565 = 360107) (by norm_num)
theorem B6074837 : Blo 1798100 6074837 := bbase (se 7 (by rfl) ⟨71189, by rfl⟩ : syracuseStep 6074837 = 142379) (by norm_num)
theorem B2699741 : Blo 1798100 2699741 := bbase (se 3 (by rfl) ⟨506201, by rfl⟩ : syracuseStep 2699741 = 1012403) (by norm_num)
theorem B4321765 : Blo 1798100 4321765 := bbase (se 4 (by rfl) ⟨405165, by rfl⟩ : syracuseStep 4321765 = 810331) (by norm_num)
theorem B3076589 : Blo 1798100 3076589 := bbase (se 3 (by rfl) ⟨576860, by rfl⟩ : syracuseStep 3076589 = 1153721) (by norm_num)
theorem B2699765 : Blo 1798100 2699765 := bbase (se 5 (by rfl) ⟨126551, by rfl⟩ : syracuseStep 2699765 = 253103) (by norm_num)
theorem B2699789 : Blo 1798100 2699789 := bbase (se 3 (by rfl) ⟨506210, by rfl⟩ : syracuseStep 2699789 = 1012421) (by norm_num)
theorem B3035677 : Blo 1798100 3035677 := bbase (se 3 (by rfl) ⟨569189, by rfl⟩ : syracuseStep 3035677 = 1138379) (by norm_num)
theorem B2699813 : Blo 1798100 2699813 := bbase (se 4 (by rfl) ⟨253107, by rfl⟩ : syracuseStep 2699813 = 506215) (by norm_num)
theorem B2699837 : Blo 1798100 2699837 := bbase (se 3 (by rfl) ⟨506219, by rfl⟩ : syracuseStep 2699837 = 1012439) (by norm_num)
theorem B3461717 : Blo 1798100 3461717 := bbase (se 8 (by rfl) ⟨20283, by rfl⟩ : syracuseStep 3461717 = 40567) (by norm_num)
theorem B2699861 : Blo 1798100 2699861 := bbase (se 8 (by rfl) ⟨15819, by rfl⟩ : syracuseStep 2699861 = 31639) (by norm_num)
theorem B6156901 : Blo 1798100 6156901 := bbase (se 4 (by rfl) ⟨577209, by rfl⟩ : syracuseStep 6156901 = 1154419) (by norm_num)
theorem B2699885 : Blo 1798100 2699885 := bbase (se 3 (by rfl) ⟨506228, by rfl⟩ : syracuseStep 2699885 = 1012457) (by norm_num)
theorem B3035765 : Blo 1798100 3035765 := bbase (se 5 (by rfl) ⟨142301, by rfl⟩ : syracuseStep 3035765 = 284603) (by norm_num)
theorem B2699909 : Blo 1798100 2699909 := bbase (se 4 (by rfl) ⟨253116, by rfl⟩ : syracuseStep 2699909 = 506233) (by norm_num)
theorem B2699933 : Blo 1798100 2699933 := bbase (se 3 (by rfl) ⟨506237, by rfl⟩ : syracuseStep 2699933 = 1012475) (by norm_num)
theorem B6828725 : Blo 1798100 6828725 := bbase (se 5 (by rfl) ⟨320096, by rfl⟩ : syracuseStep 6828725 = 640193) (by norm_num)
theorem B2699957 : Blo 1798100 2699957 := bbase (se 5 (by rfl) ⟨126560, by rfl⟩ : syracuseStep 2699957 = 253121) (by norm_num)
theorem B2699981 : Blo 1798100 2699981 := bbase (se 3 (by rfl) ⟨506246, by rfl⟩ : syracuseStep 2699981 = 1012493) (by norm_num)
theorem B3240661 : Blo 1798100 3240661 := bbase (se 7 (by rfl) ⟨37976, by rfl⟩ : syracuseStep 3240661 = 75953) (by norm_num)
theorem B2700005 : Blo 1798100 2700005 := bbase (se 4 (by rfl) ⟨253125, by rfl⟩ : syracuseStep 2700005 = 506251) (by norm_num)
theorem B3035893 : Blo 1798100 3035893 := bbase (se 5 (by rfl) ⟨142307, by rfl⟩ : syracuseStep 3035893 = 284615) (by norm_num)
theorem B2700029 : Blo 1798100 2700029 := bbase (se 3 (by rfl) ⟨506255, by rfl⟩ : syracuseStep 2700029 = 1012511) (by norm_num)
theorem B9106181 : Blo 1798100 9106181 := bbase (se 4 (by rfl) ⟨853704, by rfl⟩ : syracuseStep 9106181 = 1707409) (by norm_num)
theorem B1921801 : Blo 1798100 1921801 := bbase (se 2 (by rfl) ⟨720675, by rfl⟩ : syracuseStep 1921801 = 1441351) (by norm_num)
theorem B2700053 : Blo 1798100 2700053 := bbase (se 6 (by rfl) ⟨63282, by rfl⟩ : syracuseStep 2700053 = 126565) (by norm_num)
theorem B4551461 : Blo 1798100 4551461 := bbase (se 4 (by rfl) ⟨426699, by rfl⟩ : syracuseStep 4551461 = 853399) (by norm_num)
theorem B2700077 : Blo 1798100 2700077 := bbase (se 3 (by rfl) ⟨506264, by rfl⟩ : syracuseStep 2700077 = 1012529) (by norm_num)
theorem B2700101 : Blo 1798100 2700101 := bbase (se 4 (by rfl) ⟨253134, by rfl⟩ : syracuseStep 2700101 = 506269) (by norm_num)
theorem B3035981 : Blo 1798100 3035981 := bbase (se 3 (by rfl) ⟨569246, by rfl⟩ : syracuseStep 3035981 = 1138493) (by norm_num)
theorem B2700125 : Blo 1798100 2700125 := bbase (se 3 (by rfl) ⟨506273, by rfl⟩ : syracuseStep 2700125 = 1012547) (by norm_num)
theorem B1823585 : Blo 1798100 1823585 := bbase (se 2 (by rfl) ⟨683844, by rfl⟩ : syracuseStep 1823585 = 1367689) (by norm_num)
theorem B2700149 : Blo 1798100 2700149 := bbase (se 5 (by rfl) ⟨126569, by rfl⟩ : syracuseStep 2700149 = 253139) (by norm_num)
theorem B1921925 : Blo 1798100 1921925 := bbase (se 4 (by rfl) ⟨180180, by rfl⟩ : syracuseStep 1921925 = 360361) (by norm_num)
theorem B6075269 : Blo 1798100 6075269 := bbase (se 4 (by rfl) ⟨569556, by rfl⟩ : syracuseStep 6075269 = 1139113) (by norm_num)
theorem B2560909 : Blo 1798100 2560909 := bbase (se 3 (by rfl) ⟨480170, by rfl⟩ : syracuseStep 2560909 = 960341) (by norm_num)
theorem B10941365 : Blo 1798100 10941365 := bbase (se 5 (by rfl) ⟨512876, by rfl⟩ : syracuseStep 10941365 = 1025753) (by norm_num)
theorem B3036109 : Blo 1798100 3036109 := bbase (se 3 (by rfl) ⟨569270, by rfl⟩ : syracuseStep 3036109 = 1138541) (by norm_num)
theorem B4551653 : Blo 1798100 4551653 := bbase (se 4 (by rfl) ⟨426717, by rfl⟩ : syracuseStep 4551653 = 853435) (by norm_num)
theorem B8762357 : Blo 1798100 8762357 := bbase (se 5 (by rfl) ⟨410735, by rfl⟩ : syracuseStep 8762357 = 821471) (by norm_num)
theorem B3036197 : Blo 1798100 3036197 := bbase (se 4 (by rfl) ⟨284643, by rfl⟩ : syracuseStep 3036197 = 569287) (by norm_num)
theorem B5125189 : Blo 1798100 5125189 := bbase (se 4 (by rfl) ⟨480486, by rfl⟩ : syracuseStep 5125189 = 960973) (by norm_num)
theorem B2880613 : Blo 1798100 2880613 := bbase (se 4 (by rfl) ⟨270057, by rfl⟩ : syracuseStep 2880613 = 540115) (by norm_num)
theorem B1922177 : Blo 1798100 1922177 := bbase (se 2 (by rfl) ⟨720816, by rfl⟩ : syracuseStep 1922177 = 1441633) (by norm_num)
theorem B11523221 : Blo 1798100 11523221 := bbase (se 6 (by rfl) ⟨270075, by rfl⟩ : syracuseStep 11523221 = 540151) (by norm_num)
theorem B1873049 : Blo 1798100 1873049 := bbase (se 2 (by rfl) ⟨702393, by rfl⟩ : syracuseStep 1873049 = 1404787) (by norm_num)
theorem B7681189 : Blo 1798100 7681189 := bbase (se 4 (by rfl) ⟨720111, by rfl⟩ : syracuseStep 7681189 = 1440223) (by norm_num)
theorem B3036325 : Blo 1798100 3036325 := bbase (se 4 (by rfl) ⟨284655, by rfl⟩ : syracuseStep 3036325 = 569311) (by norm_num)
theorem B5125349 : Blo 1798100 5125349 := bbase (se 4 (by rfl) ⟨480501, by rfl⟩ : syracuseStep 5125349 = 961003) (by norm_num)
theorem B3036413 : Blo 1798100 3036413 := bbase (se 3 (by rfl) ⟨569327, by rfl⟩ : syracuseStep 3036413 = 1138655) (by norm_num)
theorem B4551997 : Blo 1798100 4551997 := bbase (se 3 (by rfl) ⟨853499, by rfl⟩ : syracuseStep 4551997 = 1706999) (by norm_num)
theorem B9721205 : Blo 1798100 9721205 := bbase (se 5 (by rfl) ⟨455681, by rfl⟩ : syracuseStep 9721205 = 911363) (by norm_num)
theorem B3036541 : Blo 1798100 3036541 := bbase (se 3 (by rfl) ⟨569351, by rfl⟩ : syracuseStep 3036541 = 1138703) (by norm_num)
theorem B4552109 : Blo 1798100 4552109 := bbase (se 3 (by rfl) ⟨853520, by rfl⟩ : syracuseStep 4552109 = 1707041) (by norm_num)
theorem B3036629 : Blo 1798100 3036629 := bbase (se 7 (by rfl) ⟨35585, by rfl⟩ : syracuseStep 3036629 = 71171) (by norm_num)
theorem B5125589 : Blo 1798100 5125589 := bbase (se 7 (by rfl) ⟨60065, by rfl⟩ : syracuseStep 5125589 = 120131) (by norm_num)
theorem B2561501 : Blo 1798100 2561501 := bbase (se 3 (by rfl) ⟨480281, by rfl⟩ : syracuseStep 2561501 = 960563) (by norm_num)
theorem B2561581 : Blo 1798100 2561581 := bbase (se 3 (by rfl) ⟨480296, by rfl⟩ : syracuseStep 2561581 = 960593) (by norm_num)
theorem B3241541 : Blo 1798100 3241541 := bbase (se 4 (by rfl) ⟨303894, by rfl⟩ : syracuseStep 3241541 = 607789) (by norm_num)
theorem B3036757 : Blo 1798100 3036757 := bbase (se 8 (by rfl) ⟨17793, by rfl⟩ : syracuseStep 3036757 = 35587) (by norm_num)
theorem B4552301 : Blo 1798100 4552301 := bbase (se 3 (by rfl) ⟨853556, by rfl⟩ : syracuseStep 4552301 = 1707113) (by norm_num)
theorem B3241613 : Blo 1798100 3241613 := bbase (se 3 (by rfl) ⟨607802, by rfl⟩ : syracuseStep 3241613 = 1215605) (by norm_num)
theorem B17290901 : Blo 1798100 17290901 := bbase (se 6 (by rfl) ⟨405255, by rfl⟩ : syracuseStep 17290901 = 810511) (by norm_num)
theorem B5125781 : Blo 1798100 5125781 := bbase (se 6 (by rfl) ⟨120135, by rfl⟩ : syracuseStep 5125781 = 240271) (by norm_num)
theorem B2561701 : Blo 1798100 2561701 := bbase (se 4 (by rfl) ⟨240159, by rfl⟩ : syracuseStep 2561701 = 480319) (by norm_num)
theorem B3036845 : Blo 1798100 3036845 := bbase (se 3 (by rfl) ⟨569408, by rfl⟩ : syracuseStep 3036845 = 1138817) (by norm_num)
theorem B1849025 : Blo 1798100 1849025 := bbase (se 2 (by rfl) ⟨693384, by rfl⟩ : syracuseStep 1849025 = 1386769) (by norm_num)
theorem B2561797 : Blo 1798100 2561797 := bbase (se 4 (by rfl) ⟨240168, by rfl⟩ : syracuseStep 2561797 = 480337) (by norm_num)
theorem B3241757 : Blo 1798100 3241757 := bbase (se 3 (by rfl) ⟨607829, by rfl⟩ : syracuseStep 3241757 = 1215659) (by norm_num)
theorem B3036973 : Blo 1798100 3036973 := bbase (se 3 (by rfl) ⟨569432, by rfl⟩ : syracuseStep 3036973 = 1138865) (by norm_num)
theorem B4323149 : Blo 1798100 4323149 := bbase (se 3 (by rfl) ⟨810590, by rfl⟩ : syracuseStep 4323149 = 1621181) (by norm_num)
theorem B3241829 : Blo 1798100 3241829 := bbase (se 4 (by rfl) ⟨303921, by rfl⟩ : syracuseStep 3241829 = 607843) (by norm_num)
theorem B2160517 : Blo 1798100 2160517 := bbase (se 4 (by rfl) ⟨202548, by rfl⟩ : syracuseStep 2160517 = 405097) (by norm_num)
theorem B3037061 : Blo 1798100 3037061 := bbase (se 4 (by rfl) ⟨284724, by rfl⟩ : syracuseStep 3037061 = 569449) (by norm_num)
theorem B21059477 : Blo 1798100 21059477 := bbase (se 6 (by rfl) ⟨493581, by rfl⟩ : syracuseStep 21059477 = 987163) (by norm_num)
theorem B4552645 : Blo 1798100 4552645 := bbase (se 4 (by rfl) ⟨426810, by rfl⟩ : syracuseStep 4552645 = 853621) (by norm_num)
theorem B3037189 : Blo 1798100 3037189 := bbase (se 4 (by rfl) ⟨284736, by rfl⟩ : syracuseStep 3037189 = 569473) (by norm_num)
theorem B4323341 : Blo 1798100 4323341 := bbase (se 3 (by rfl) ⟨810626, by rfl⟩ : syracuseStep 4323341 = 1621253) (by norm_num)
theorem B9107477 : Blo 1798100 9107477 := bbase (se 6 (by rfl) ⟨213456, by rfl⟩ : syracuseStep 9107477 = 426913) (by norm_num)
theorem B4552757 : Blo 1798100 4552757 := bbase (se 5 (by rfl) ⟨213410, by rfl⟩ : syracuseStep 4552757 = 426821) (by norm_num)
theorem B14784565 : Blo 1798100 14784565 := bbase (se 5 (by rfl) ⟨693026, by rfl⟩ : syracuseStep 14784565 = 1386053) (by norm_num)
theorem B2734157 : Blo 1798100 2734157 := bbase (se 3 (by rfl) ⟨512654, by rfl⟩ : syracuseStep 2734157 = 1025309) (by norm_num)
theorem B2308181 : Blo 1798100 2308181 := bbase (se 8 (by rfl) ⟨13524, by rfl⟩ : syracuseStep 2308181 = 27049) (by norm_num)
theorem B3037277 : Blo 1798100 3037277 := bbase (se 3 (by rfl) ⟨569489, by rfl⟩ : syracuseStep 3037277 = 1138979) (by norm_num)
theorem B62290133 : Blo 1798100 62290133 := bbase (se 7 (by rfl) ⟨729962, by rfl⟩ : syracuseStep 62290133 = 1459925) (by norm_num)
theorem B20486357 : Blo 1798100 20486357 := bbase (se 7 (by rfl) ⟨240074, by rfl⟩ : syracuseStep 20486357 = 480149) (by norm_num)
theorem B12966101 : Blo 1798100 12966101 := bbase (se 7 (by rfl) ⟨151946, by rfl⟩ : syracuseStep 12966101 = 303893) (by norm_num)
theorem B4864213 : Blo 1798100 4864213 := bbase (se 7 (by rfl) ⟨57002, by rfl⟩ : syracuseStep 4864213 = 114005) (by norm_num)
theorem B3037405 : Blo 1798100 3037405 := bbase (se 3 (by rfl) ⟨569513, by rfl⟩ : syracuseStep 3037405 = 1139027) (by norm_num)
theorem B4552949 : Blo 1798100 4552949 := bbase (se 5 (by rfl) ⟨213419, by rfl⟩ : syracuseStep 4552949 = 426839) (by norm_num)
theorem B2562293 : Blo 1798100 2562293 := bbase (se 5 (by rfl) ⟨120107, by rfl⟩ : syracuseStep 2562293 = 240215) (by norm_num)
theorem B8321285 : Blo 1798100 8321285 := bbase (se 4 (by rfl) ⟨780120, by rfl⟩ : syracuseStep 8321285 = 1560241) (by norm_num)
theorem B3414325 : Blo 1798100 3414325 := bbase (se 5 (by rfl) ⟨160046, by rfl⟩ : syracuseStep 3414325 = 320093) (by norm_num)
theorem B3037493 : Blo 1798100 3037493 := bbase (se 5 (by rfl) ⟨142382, by rfl⟩ : syracuseStep 3037493 = 284765) (by norm_num)
theorem B3840365 : Blo 1798100 3840365 := bbase (se 3 (by rfl) ⟨720068, by rfl⟩ : syracuseStep 3840365 = 1440137) (by norm_num)
theorem B3037621 : Blo 1798100 3037621 := bbase (se 5 (by rfl) ⟨142388, by rfl⟩ : syracuseStep 3037621 = 284777) (by norm_num)
theorem B3414469 : Blo 1798100 3414469 := bbase (se 4 (by rfl) ⟨320106, by rfl⟩ : syracuseStep 3414469 = 640213) (by norm_num)
theorem B2881997 : Blo 1798100 2881997 := bbase (se 3 (by rfl) ⟨540374, by rfl⟩ : syracuseStep 2881997 = 1080749) (by norm_num)
theorem B3840509 : Blo 1798100 3840509 := bbase (se 3 (by rfl) ⟨720095, by rfl⟩ : syracuseStep 3840509 = 1440191) (by norm_num)
theorem B2275877 : Blo 1798100 2275877 := bbase (se 4 (by rfl) ⟨213363, by rfl⟩ : syracuseStep 2275877 = 426727) (by norm_num)
theorem B6068789 : Blo 1798100 6068789 := bbase (se 5 (by rfl) ⟨284474, by rfl⟩ : syracuseStep 6068789 = 568949) (by norm_num)
theorem B3463741 : Blo 1798100 3463741 := bbase (se 3 (by rfl) ⟨649451, by rfl⟩ : syracuseStep 3463741 = 1298903) (by norm_num)
theorem B4553293 : Blo 1798100 4553293 := bbase (se 3 (by rfl) ⟨853742, by rfl⟩ : syracuseStep 4553293 = 1707485) (by norm_num)
theorem B2275933 : Blo 1798100 2275933 := bbase (se 3 (by rfl) ⟨426737, by rfl⟩ : syracuseStep 2275933 = 853475) (by norm_num)
theorem B3414629 : Blo 1798100 3414629 := bbase (se 4 (by rfl) ⟨320121, by rfl⟩ : syracuseStep 3414629 = 640243) (by norm_num)
theorem B3242621 : Blo 1798100 3242621 := bbase (se 3 (by rfl) ⟨607991, by rfl⟩ : syracuseStep 3242621 = 1215983) (by norm_num)
theorem B2882189 : Blo 1798100 2882189 := bbase (se 3 (by rfl) ⟨540410, by rfl⟩ : syracuseStep 2882189 = 1080821) (by norm_num)
theorem B5765813 : Blo 1798100 5765813 := bbase (se 5 (by rfl) ⟨270272, by rfl⟩ : syracuseStep 5765813 = 540545) (by norm_num)
theorem B2276029 : Blo 1798100 2276029 := bbase (se 3 (by rfl) ⟨426755, by rfl⟩ : syracuseStep 2276029 = 853511) (by norm_num)
theorem B4553405 : Blo 1798100 4553405 := bbase (se 3 (by rfl) ⟨853763, by rfl⟩ : syracuseStep 4553405 = 1707527) (by norm_num)
theorem B3414773 : Blo 1798100 3414773 := bbase (se 5 (by rfl) ⟨160067, by rfl⟩ : syracuseStep 3414773 = 320135) (by norm_num)
theorem B6830837 : Blo 1798100 6830837 := bbase (se 5 (by rfl) ⟨320195, by rfl⟩ : syracuseStep 6830837 = 640391) (by norm_num)
theorem B4324109 : Blo 1798100 4324109 := bbase (se 3 (by rfl) ⟨810770, by rfl⟩ : syracuseStep 4324109 = 1621541) (by norm_num)
theorem B2562845 : Blo 1798100 2562845 := bbase (se 3 (by rfl) ⟨480533, by rfl⟩ : syracuseStep 2562845 = 961067) (by norm_num)
theorem B7297877 : Blo 1798100 7297877 := bbase (se 9 (by rfl) ⟨21380, by rfl⟩ : syracuseStep 7297877 = 42761) (by norm_num)
theorem B2276201 : Blo 1798100 2276201 := bbase (se 2 (by rfl) ⟨853575, by rfl⟩ : syracuseStep 2276201 = 1707151) (by norm_num)
theorem B4553597 : Blo 1798100 4553597 := bbase (se 3 (by rfl) ⟨853799, by rfl⟩ : syracuseStep 4553597 = 1707599) (by norm_num)
theorem B2276257 : Blo 1798100 2276257 := bbase (se 2 (by rfl) ⟨853596, by rfl⟩ : syracuseStep 2276257 = 1707193) (by norm_num)
theorem B4045733 : Blo 1798100 4045733 := bbase (se 4 (by rfl) ⟨379287, by rfl⟩ : syracuseStep 4045733 = 758575) (by norm_num)
theorem B6069221 : Blo 1798100 6069221 := bbase (se 4 (by rfl) ⟨568989, by rfl⟩ : syracuseStep 6069221 = 1137979) (by norm_num)
theorem B4045805 : Blo 1798100 4045805 := bbase (se 3 (by rfl) ⟨758588, by rfl⟩ : syracuseStep 4045805 = 1517177) (by norm_num)
theorem B4676597 : Blo 1798100 4676597 := bbase (se 5 (by rfl) ⟨219215, by rfl⟩ : syracuseStep 4676597 = 438431) (by norm_num)
theorem B2276353 : Blo 1798100 2276353 := bbase (se 2 (by rfl) ⟨853632, by rfl⟩ : syracuseStep 2276353 = 1707265) (by norm_num)
theorem B3415061 : Blo 1798100 3415061 := bbase (se 6 (by rfl) ⟨80040, by rfl⟩ : syracuseStep 3415061 = 160081) (by norm_num)
theorem B6831125 : Blo 1798100 6831125 := bbase (se 6 (by rfl) ⟨160104, by rfl⟩ : syracuseStep 6831125 = 320209) (by norm_num)
theorem B4045877 : Blo 1798100 4045877 := bbase (se 5 (by rfl) ⟨189650, by rfl⟩ : syracuseStep 4045877 = 379301) (by norm_num)
theorem B4045949 : Blo 1798100 4045949 := bbase (se 3 (by rfl) ⟨758615, by rfl⟩ : syracuseStep 4045949 = 1517231) (by norm_num)
theorem B2276525 : Blo 1798100 2276525 := bbase (se 3 (by rfl) ⟨426848, by rfl⟩ : syracuseStep 2276525 = 853697) (by norm_num)
theorem B3415213 : Blo 1798100 3415213 := bbase (se 3 (by rfl) ⟨640352, by rfl⟩ : syracuseStep 3415213 = 1280705) (by norm_num)
theorem B4046021 : Blo 1798100 4046021 := bbase (se 4 (by rfl) ⟨379314, by rfl⟩ : syracuseStep 4046021 = 758629) (by norm_num)
theorem B4553941 : Blo 1798100 4553941 := bbase (se 7 (by rfl) ⟨53366, by rfl⟩ : syracuseStep 4553941 = 106733) (by norm_num)
theorem B3841253 : Blo 1798100 3841253 := bbase (se 4 (by rfl) ⟨360117, by rfl⟩ : syracuseStep 3841253 = 720235) (by norm_num)
theorem B2276581 : Blo 1798100 2276581 := bbase (se 4 (by rfl) ⟨213429, by rfl⟩ : syracuseStep 2276581 = 426859) (by norm_num)
theorem B2161901 : Blo 1798100 2161901 := bbase (se 3 (by rfl) ⟨405356, by rfl⟩ : syracuseStep 2161901 = 810713) (by norm_num)
theorem B8649989 : Blo 1798100 8649989 := bbase (se 4 (by rfl) ⟨810936, by rfl⟩ : syracuseStep 8649989 = 1621873) (by norm_num)
theorem B4046093 : Blo 1798100 4046093 := bbase (se 3 (by rfl) ⟨758642, by rfl⟩ : syracuseStep 4046093 = 1517285) (by norm_num)
theorem B2432269 : Blo 1798100 2432269 := bbase (se 3 (by rfl) ⟨456050, by rfl⟩ : syracuseStep 2432269 = 912101) (by norm_num)
theorem B9108773 : Blo 1798100 9108773 := bbase (se 4 (by rfl) ⟨853947, by rfl⟩ : syracuseStep 9108773 = 1707895) (by norm_num)
theorem B2276677 : Blo 1798100 2276677 := bbase (se 4 (by rfl) ⟨213438, by rfl⟩ : syracuseStep 2276677 = 426877) (by norm_num)
theorem B4554053 : Blo 1798100 4554053 := bbase (se 4 (by rfl) ⟨426942, by rfl⟩ : syracuseStep 4554053 = 853885) (by norm_num)
theorem B4046165 : Blo 1798100 4046165 := bbase (se 11 (by rfl) ⟨2963, by rfl⟩ : syracuseStep 4046165 = 5927) (by norm_num)
theorem B6069653 : Blo 1798100 6069653 := bbase (se 6 (by rfl) ⟨142257, by rfl⟩ : syracuseStep 6069653 = 284515) (by norm_num)
theorem B4046237 : Blo 1798100 4046237 := bbase (se 3 (by rfl) ⟨758669, by rfl⟩ : syracuseStep 4046237 = 1517339) (by norm_num)
theorem B2735525 : Blo 1798100 2735525 := bbase (se 4 (by rfl) ⟨256455, by rfl⟩ : syracuseStep 2735525 = 512911) (by norm_num)
theorem B2162089 : Blo 1798100 2162089 := bbase (se 2 (by rfl) ⟨810783, by rfl⟩ : syracuseStep 2162089 = 1621567) (by norm_num)
theorem B4103597 : Blo 1798100 4103597 := bbase (se 3 (by rfl) ⟨769424, by rfl⟩ : syracuseStep 4103597 = 1538849) (by norm_num)
theorem B3415517 : Blo 1798100 3415517 := bbase (se 3 (by rfl) ⟨640409, by rfl⟩ : syracuseStep 3415517 = 1280819) (by norm_num)
theorem B4046309 : Blo 1798100 4046309 := bbase (se 4 (by rfl) ⟨379341, by rfl⟩ : syracuseStep 4046309 = 758683) (by norm_num)
theorem B2022889 : Blo 1798100 2022889 := bbase (se 2 (by rfl) ⟨758583, by rfl⟩ : syracuseStep 2022889 = 1517167) (by norm_num)
theorem B2276849 : Blo 1798100 2276849 := bbase (se 2 (by rfl) ⟨853818, by rfl⟩ : syracuseStep 2276849 = 1707637) (by norm_num)
theorem B4554245 : Blo 1798100 4554245 := bbase (se 4 (by rfl) ⟨426960, by rfl⟩ : syracuseStep 4554245 = 853921) (by norm_num)
theorem B2022925 : Blo 1798100 2022925 := bbase (se 3 (by rfl) ⟨379298, by rfl⟩ : syracuseStep 2022925 = 758597) (by norm_num)
theorem B2276905 : Blo 1798100 2276905 := bbase (se 2 (by rfl) ⟨853839, by rfl⟩ : syracuseStep 2276905 = 1707679) (by norm_num)
theorem B4046381 : Blo 1798100 4046381 := bbase (se 3 (by rfl) ⟨758696, by rfl⟩ : syracuseStep 4046381 = 1517393) (by norm_num)
theorem B2022961 : Blo 1798100 2022961 := bbase (se 2 (by rfl) ⟨758610, by rfl⟩ : syracuseStep 2022961 = 1517221) (by norm_num)
theorem B5766709 : Blo 1798100 5766709 := bbase (se 5 (by rfl) ⟨270314, by rfl⟩ : syracuseStep 5766709 = 540629) (by norm_num)
theorem B1900093 : Blo 1798100 1900093 := bbase (se 3 (by rfl) ⟨356267, by rfl⟩ : syracuseStep 1900093 = 712535) (by norm_num)
theorem B2022997 : Blo 1798100 2022997 := bbase (se 8 (by rfl) ⟨11853, by rfl⟩ : syracuseStep 2022997 = 23707) (by norm_num)
theorem B4046453 : Blo 1798100 4046453 := bbase (se 5 (by rfl) ⟨189677, by rfl⟩ : syracuseStep 4046453 = 379355) (by norm_num)
theorem B2023033 : Blo 1798100 2023033 := bbase (se 2 (by rfl) ⟨758637, by rfl⟩ : syracuseStep 2023033 = 1517275) (by norm_num)
theorem B2162305 : Blo 1798100 2162305 := bbase (se 2 (by rfl) ⟨810864, by rfl⟩ : syracuseStep 2162305 = 1621729) (by norm_num)
theorem B2277001 : Blo 1798100 2277001 := bbase (se 2 (by rfl) ⟨853875, by rfl⟩ : syracuseStep 2277001 = 1707751) (by norm_num)
theorem B2023069 : Blo 1798100 2023069 := bbase (se 3 (by rfl) ⟨379325, by rfl⟩ : syracuseStep 2023069 = 758651) (by norm_num)
theorem B18456245 : Blo 1798100 18456245 := bbase (se 5 (by rfl) ⟨865136, by rfl⟩ : syracuseStep 18456245 = 1730273) (by norm_num)
theorem B4046525 : Blo 1798100 4046525 := bbase (se 3 (by rfl) ⟨758723, by rfl⟩ : syracuseStep 4046525 = 1517447) (by norm_num)
theorem B2023105 : Blo 1798100 2023105 := bbase (se 2 (by rfl) ⟨758664, by rfl⟩ : syracuseStep 2023105 = 1517329) (by norm_num)
theorem B2023141 : Blo 1798100 2023141 := bbase (se 4 (by rfl) ⟨189669, by rfl⟩ : syracuseStep 2023141 = 379339) (by norm_num)
theorem B4046597 : Blo 1798100 4046597 := bbase (se 4 (by rfl) ⟨379368, by rfl⟩ : syracuseStep 4046597 = 758737) (by norm_num)
theorem B2023177 : Blo 1798100 2023177 := bbase (se 2 (by rfl) ⟨758691, by rfl⟩ : syracuseStep 2023177 = 1517383) (by norm_num)
theorem B2023213 : Blo 1798100 2023213 := bbase (se 3 (by rfl) ⟨379352, by rfl⟩ : syracuseStep 2023213 = 758705) (by norm_num)
theorem B2277173 : Blo 1798100 2277173 := bbase (se 5 (by rfl) ⟨106742, by rfl⟩ : syracuseStep 2277173 = 213485) (by norm_num)
theorem B6070085 : Blo 1798100 6070085 := bbase (se 4 (by rfl) ⟨569070, by rfl⟩ : syracuseStep 6070085 = 1138141) (by norm_num)
theorem B4046669 : Blo 1798100 4046669 := bbase (se 3 (by rfl) ⟨758750, by rfl⟩ : syracuseStep 4046669 = 1517501) (by norm_num)
theorem B2023249 : Blo 1798100 2023249 := bbase (se 2 (by rfl) ⟨758718, by rfl⟩ : syracuseStep 2023249 = 1517437) (by norm_num)
theorem B4554589 : Blo 1798100 4554589 := bbase (se 3 (by rfl) ⟨853985, by rfl⟩ : syracuseStep 4554589 = 1707971) (by norm_num)
theorem B2277229 : Blo 1798100 2277229 := bbase (se 3 (by rfl) ⟨426980, by rfl⟩ : syracuseStep 2277229 = 853961) (by norm_num)
theorem B2023285 : Blo 1798100 2023285 := bbase (se 5 (by rfl) ⟨94841, by rfl⟩ : syracuseStep 2023285 = 189683) (by norm_num)
theorem B8765317 : Blo 1798100 8765317 := bbase (se 4 (by rfl) ⟨821748, by rfl⟩ : syracuseStep 8765317 = 1643497) (by norm_num)
theorem B4046741 : Blo 1798100 4046741 := bbase (se 6 (by rfl) ⟨94845, by rfl⟩ : syracuseStep 4046741 = 189691) (by norm_num)
theorem B2023321 : Blo 1798100 2023321 := bbase (se 2 (by rfl) ⟨758745, by rfl⟩ : syracuseStep 2023321 = 1517491) (by norm_num)
theorem B2023357 : Blo 1798100 2023357 := bbase (se 3 (by rfl) ⟨379379, by rfl⟩ : syracuseStep 2023357 = 758759) (by norm_num)
theorem B2277325 : Blo 1798100 2277325 := bbase (se 3 (by rfl) ⟨426998, by rfl⟩ : syracuseStep 2277325 = 853997) (by norm_num)
theorem B4554701 : Blo 1798100 4554701 := bbase (se 3 (by rfl) ⟨854006, by rfl⟩ : syracuseStep 4554701 = 1708013) (by norm_num)
theorem B3842005 : Blo 1798100 3842005 := bbase (se 7 (by rfl) ⟨45023, by rfl⟩ : syracuseStep 3842005 = 90047) (by norm_num)
theorem B4046813 : Blo 1798100 4046813 := bbase (se 3 (by rfl) ⟨758777, by rfl⟩ : syracuseStep 4046813 = 1517555) (by norm_num)
theorem B2023393 : Blo 1798100 2023393 := bbase (se 2 (by rfl) ⟨758772, by rfl⟩ : syracuseStep 2023393 = 1517545) (by norm_num)
theorem B15368291 : Blo 1798100 15368291 := bstep (se 1 (by rfl) ⟨11526218, by rfl⟩ : syracuseStep 15368291 = 23052437) B23052437
theorem B21635171 : Blo 1798100 21635171 := bstep (se 1 (by rfl) ⟨16226378, by rfl⟩ : syracuseStep 21635171 = 32452757) B32452757
theorem B2023555 : Blo 1798100 2023555 := bstep (se 1 (by rfl) ⟨1517666, by rfl⟩ : syracuseStep 2023555 = 3035333) B3035333
theorem B4046993 : Blo 1798100 4046993 := bstep (se 2 (by rfl) ⟨1517622, by rfl⟩ : syracuseStep 4046993 = 3035245) B3035245
theorem B4047011 : Blo 1798100 4047011 := bstep (se 1 (by rfl) ⟨3035258, by rfl⟩ : syracuseStep 4047011 = 6070517) B6070517
theorem B9109745 : Blo 1798100 9109745 := bstep (se 2 (by rfl) ⟨3416154, by rfl⟩ : syracuseStep 9109745 = 6832309) B6832309
theorem B4555025 : Blo 1798100 4555025 := bstep (se 2 (by rfl) ⟨1708134, by rfl⟩ : syracuseStep 4555025 = 3416269) B3416269
theorem B2023699 : Blo 1798100 2023699 := bstep (se 1 (by rfl) ⟨1517774, by rfl⟩ : syracuseStep 2023699 = 3035549) B3035549
theorem B4555075 : Blo 1798100 4555075 := bstep (se 1 (by rfl) ⟨3416306, by rfl⟩ : syracuseStep 4555075 = 6832613) B6832613
theorem B18473285 : Blo 1798100 18473285 := bstep (se 4 (by rfl) ⟨1731870, by rfl⟩ : syracuseStep 18473285 = 3463741) B3463741
theorem B2277715 : Blo 1798100 2277715 := bstep (se 1 (by rfl) ⟨1708286, by rfl⟩ : syracuseStep 2277715 = 3416573) B3416573
theorem B2023843 : Blo 1798100 2023843 := bstep (se 1 (by rfl) ⟨1517882, by rfl⟩ : syracuseStep 2023843 = 3035765) B3035765
theorem B4047281 : Blo 1798100 4047281 := bstep (se 2 (by rfl) ⟨1517730, by rfl⟩ : syracuseStep 4047281 = 3035461) B3035461
theorem B2277811 : Blo 1798100 2277811 := bstep (se 1 (by rfl) ⟨1708358, by rfl⟩ : syracuseStep 2277811 = 3416717) B3416717
theorem B21881269 : Blo 1798100 21881269 := bstep (se 5 (by rfl) ⟨1025684, by rfl⟩ : syracuseStep 21881269 = 2051369) B2051369
theorem B4047299 : Blo 1798100 4047299 := bstep (se 1 (by rfl) ⟨3035474, by rfl⟩ : syracuseStep 4047299 = 6070949) B6070949
theorem B6070733 : Blo 1798100 6070733 := bstep (se 3 (by rfl) ⟨1138262, by rfl⟩ : syracuseStep 6070733 = 2276525) B2276525
theorem B4555217 : Blo 1798100 4555217 := bstep (se 2 (by rfl) ⟨1708206, by rfl⟩ : syracuseStep 4555217 = 3416413) B3416413
theorem B6070787 : Blo 1798100 6070787 := bstep (se 1 (by rfl) ⟨4553090, by rfl⟩ : syracuseStep 6070787 = 9106181) B9106181
theorem B2023987 : Blo 1798100 2023987 := bstep (se 1 (by rfl) ⟨1517990, by rfl⟩ : syracuseStep 2023987 = 3035981) B3035981
theorem B8643185 : Blo 1798100 8643185 := bstep (se 2 (by rfl) ⟨3241194, by rfl⟩ : syracuseStep 8643185 = 6482389) B6482389
theorem B6832781 : Blo 1798100 6832781 := bstep (se 3 (by rfl) ⟨1281146, by rfl⟩ : syracuseStep 6832781 = 2562293) B2562293
theorem B11682467 : Blo 1798100 11682467 := bstep (se 1 (by rfl) ⟨8761850, by rfl⟩ : syracuseStep 11682467 = 17523701) B17523701
theorem B5841571 : Blo 1798100 5841571 := bstep (se 1 (by rfl) ⟨4381178, by rfl⟩ : syracuseStep 5841571 = 8762357) B8762357
theorem B2024131 : Blo 1798100 2024131 := bstep (se 1 (by rfl) ⟨1518098, by rfl⟩ : syracuseStep 2024131 = 3036197) B3036197
theorem B4047569 : Blo 1798100 4047569 := bstep (se 2 (by rfl) ⟨1517838, by rfl⟩ : syracuseStep 4047569 = 3035677) B3035677
theorem B7291619 : Blo 1798100 7291619 := bstep (se 1 (by rfl) ⟨5468714, by rfl⟩ : syracuseStep 7291619 = 10937429) B10937429
theorem B4047587 : Blo 1798100 4047587 := bstep (se 1 (by rfl) ⟨3035690, by rfl⟩ : syracuseStep 4047587 = 6071381) B6071381
theorem B6075053 : Blo 1798100 6075053 := bstep (se 3 (by rfl) ⟨1139072, by rfl⟩ : syracuseStep 6075053 = 2278145) B2278145
theorem B2736899 : Blo 1798100 2736899 := bstep (se 1 (by rfl) ⟨2052674, by rfl⟩ : syracuseStep 2736899 = 4105349) B4105349
theorem B6071057 : Blo 1798100 6071057 := bstep (se 2 (by rfl) ⟨2276646, by rfl⟩ : syracuseStep 6071057 = 4553293) B4553293
theorem B8209201 : Blo 1798100 8209201 := bstep (se 2 (by rfl) ⟨3078450, by rfl⟩ : syracuseStep 8209201 = 6156901) B6156901
theorem B5473091 : Blo 1798100 5473091 := bstep (se 1 (by rfl) ⟨4104818, by rfl⟩ : syracuseStep 5473091 = 8209637) B8209637
theorem B3416899 : Blo 1798100 3416899 := bstep (se 1 (by rfl) ⟨2562674, by rfl⟩ : syracuseStep 3416899 = 5125349) B5125349
theorem B2024275 : Blo 1798100 2024275 := bstep (se 1 (by rfl) ⟨1518206, by rfl⟩ : syracuseStep 2024275 = 3036413) B3036413
theorem B10240901 : Blo 1798100 10240901 := bstep (se 4 (by rfl) ⟨960084, by rfl⟩ : syracuseStep 10240901 = 1920169) B1920169
theorem B6480803 : Blo 1798100 6480803 := bstep (se 1 (by rfl) ⟨4860602, by rfl⟩ : syracuseStep 6480803 = 9721205) B9721205
theorem B10388387 : Blo 1798100 10388387 := bstep (se 1 (by rfl) ⟨7791290, by rfl⟩ : syracuseStep 10388387 = 15582581) B15582581
theorem B5120941 : Blo 1798100 5120941 := bstep (se 3 (by rfl) ⟨960176, by rfl⟩ : syracuseStep 5120941 = 1920353) B1920353
theorem B2024419 : Blo 1798100 2024419 := bstep (se 1 (by rfl) ⟨1518314, by rfl⟩ : syracuseStep 2024419 = 3036629) B3036629
theorem B3417059 : Blo 1798100 3417059 := bstep (se 1 (by rfl) ⟨2562794, by rfl⟩ : syracuseStep 3417059 = 5125589) B5125589
theorem B4047857 : Blo 1798100 4047857 := bstep (se 2 (by rfl) ⟨1517946, by rfl⟩ : syracuseStep 4047857 = 3035893) B3035893
theorem B4047875 : Blo 1798100 4047875 := bstep (se 1 (by rfl) ⟨3035906, by rfl⟩ : syracuseStep 4047875 = 6071813) B6071813
theorem B11527267 : Blo 1798100 11527267 := bstep (se 1 (by rfl) ⟨8645450, by rfl⟩ : syracuseStep 11527267 = 17290901) B17290901
theorem B23364721 : Blo 1798100 23364721 := bstep (se 2 (by rfl) ⟨8761770, by rfl⟩ : syracuseStep 23364721 = 17523541) B17523541
theorem B2024563 : Blo 1798100 2024563 := bstep (se 1 (by rfl) ⟨1518422, by rfl⟩ : syracuseStep 2024563 = 3036845) B3036845
theorem B10937521 : Blo 1798100 10937521 := bstep (se 2 (by rfl) ⟨4101570, by rfl⟩ : syracuseStep 10937521 = 8203141) B8203141
theorem B2024707 : Blo 1798100 2024707 := bstep (se 1 (by rfl) ⟨1518530, by rfl⟩ : syracuseStep 2024707 = 3037061) B3037061
theorem B4048145 : Blo 1798100 4048145 := bstep (se 2 (by rfl) ⟨1518054, by rfl⟩ : syracuseStep 4048145 = 3036109) B3036109
theorem B4048163 : Blo 1798100 4048163 := bstep (se 1 (by rfl) ⟨3036122, by rfl⟩ : syracuseStep 4048163 = 6072245) B6072245
theorem B6071597 : Blo 1798100 6071597 := bstep (se 3 (by rfl) ⟨1138424, by rfl⟩ : syracuseStep 6071597 = 2276849) B2276849
theorem B6071651 : Blo 1798100 6071651 := bstep (se 1 (by rfl) ⟨4553738, by rfl⟩ : syracuseStep 6071651 = 9107477) B9107477
theorem B2024851 : Blo 1798100 2024851 := bstep (se 1 (by rfl) ⟨1518638, by rfl⟩ : syracuseStep 2024851 = 3037277) B3037277
theorem B10249649 : Blo 1798100 10249649 := bstep (se 2 (by rfl) ⟨3843618, by rfl⟩ : syracuseStep 10249649 = 7687237) B7687237
theorem B6833585 : Blo 1798100 6833585 := bstep (se 2 (by rfl) ⟨2562594, by rfl⟩ : syracuseStep 6833585 = 5125189) B5125189
theorem B4556209 : Blo 1798100 4556209 := bstep (se 2 (by rfl) ⟨1708578, by rfl⟩ : syracuseStep 4556209 = 3417157) B3417157
theorem B41526755 : Blo 1798100 41526755 := bstep (se 1 (by rfl) ⟨31145066, by rfl⟩ : syracuseStep 41526755 = 62290133) B62290133
theorem B13657571 : Blo 1798100 13657571 := bstep (se 1 (by rfl) ⟨10243178, by rfl⟩ : syracuseStep 13657571 = 20486357) B20486357
theorem B8644067 : Blo 1798100 8644067 := bstep (se 1 (by rfl) ⟨6483050, by rfl⟩ : syracuseStep 8644067 = 12966101) B12966101
theorem B5547523 : Blo 1798100 5547523 := bstep (se 1 (by rfl) ⟨4160642, by rfl⟩ : syracuseStep 5547523 = 8321285) B8321285
theorem B2024995 : Blo 1798100 2024995 := bstep (se 1 (by rfl) ⟨1518746, by rfl⟩ : syracuseStep 2024995 = 3037493) B3037493
theorem B10241585 : Blo 1798100 10241585 := bstep (se 2 (by rfl) ⟨3840594, by rfl⟩ : syracuseStep 10241585 = 7681189) B7681189
theorem B4048433 : Blo 1798100 4048433 := bstep (se 2 (by rfl) ⟨1518162, by rfl⟩ : syracuseStep 4048433 = 3036325) B3036325
theorem B4048451 : Blo 1798100 4048451 := bstep (se 1 (by rfl) ⟨3036338, by rfl⟩ : syracuseStep 4048451 = 6072677) B6072677
theorem B3696209 : Blo 1798100 3696209 := bstep (se 2 (by rfl) ⟨1386078, by rfl⟩ : syracuseStep 3696209 = 2772157) B2772157
theorem B6071921 : Blo 1798100 6071921 := bstep (se 2 (by rfl) ⟨2276970, by rfl⟩ : syracuseStep 6071921 = 4553941) B4553941
theorem B9111203 : Blo 1798100 9111203 := bstep (se 1 (by rfl) ⟨6833402, by rfl⟩ : syracuseStep 9111203 = 13666805) B13666805
theorem B4556483 : Blo 1798100 4556483 := bstep (se 1 (by rfl) ⟨3417362, by rfl⟩ : syracuseStep 4556483 = 6834725) B6834725
theorem B7685837 : Blo 1798100 7685837 := bstep (se 3 (by rfl) ⟨1441094, by rfl⟩ : syracuseStep 7685837 = 2882189) B2882189
theorem B3843875 : Blo 1798100 3843875 := bstep (se 1 (by rfl) ⟨2882906, by rfl⟩ : syracuseStep 3843875 = 5765813) B5765813
theorem B4048721 : Blo 1798100 4048721 := bstep (se 2 (by rfl) ⟨1518270, by rfl⟩ : syracuseStep 4048721 = 3036541) B3036541
theorem B4048739 : Blo 1798100 4048739 := bstep (se 1 (by rfl) ⟨3036554, by rfl⟩ : syracuseStep 4048739 = 6073109) B6073109
theorem B2697155 : Blo 1798100 2697155 := bstep (se 1 (by rfl) ⟨2022866, by rfl⟩ : syracuseStep 2697155 = 4045733) B4045733
theorem B2697185 : Blo 1798100 2697185 := bstep (se 2 (by rfl) ⟨1011444, by rfl⟩ : syracuseStep 2697185 = 2022889) B2022889
theorem B2697203 : Blo 1798100 2697203 := bstep (se 1 (by rfl) ⟨2022902, by rfl⟩ : syracuseStep 2697203 = 4045805) B4045805
theorem B10946573 : Blo 1798100 10946573 := bstep (se 3 (by rfl) ⟨2052482, by rfl⟩ : syracuseStep 10946573 = 4104965) B4104965
theorem B2697233 : Blo 1798100 2697233 := bstep (se 2 (by rfl) ⟨1011462, by rfl⟩ : syracuseStep 2697233 = 2022925) B2022925
theorem B2697251 : Blo 1798100 2697251 := bstep (se 1 (by rfl) ⟨2022938, by rfl⟩ : syracuseStep 2697251 = 4045877) B4045877
theorem B2697281 : Blo 1798100 2697281 := bstep (se 2 (by rfl) ⟨1011480, by rfl⟩ : syracuseStep 2697281 = 2022961) B2022961
theorem B2533457 : Blo 1798100 2533457 := bstep (se 2 (by rfl) ⟨950046, by rfl⟩ : syracuseStep 2533457 = 1900093) B1900093
theorem B6834253 : Blo 1798100 6834253 := bstep (se 3 (by rfl) ⟨1281422, by rfl⟩ : syracuseStep 6834253 = 2562845) B2562845
theorem B2697299 : Blo 1798100 2697299 := bstep (se 1 (by rfl) ⟨2022974, by rfl⟩ : syracuseStep 2697299 = 4045949) B4045949
theorem B2697329 : Blo 1798100 2697329 := bstep (se 2 (by rfl) ⟨1011498, by rfl⟩ : syracuseStep 2697329 = 2022997) B2022997
theorem B4049009 : Blo 1798100 4049009 := bstep (se 2 (by rfl) ⟨1518378, by rfl⟩ : syracuseStep 4049009 = 3036757) B3036757
theorem B35063921 : Blo 1798100 35063921 := bstep (se 2 (by rfl) ⟨13148970, by rfl⟩ : syracuseStep 35063921 = 26297941) B26297941
theorem B2697347 : Blo 1798100 2697347 := bstep (se 1 (by rfl) ⟨2023010, by rfl⟩ : syracuseStep 2697347 = 4046021) B4046021
theorem B4049027 : Blo 1798100 4049027 := bstep (se 1 (by rfl) ⟨3036770, by rfl⟩ : syracuseStep 4049027 = 6073541) B6073541
theorem B6072461 : Blo 1798100 6072461 := bstep (se 3 (by rfl) ⟨1138586, by rfl⟩ : syracuseStep 6072461 = 2277173) B2277173
theorem B2697377 : Blo 1798100 2697377 := bstep (se 2 (by rfl) ⟨1011516, by rfl⟩ : syracuseStep 2697377 = 2023033) B2023033
theorem B2697395 : Blo 1798100 2697395 := bstep (se 1 (by rfl) ⟨2023046, by rfl⟩ : syracuseStep 2697395 = 4046093) B4046093
theorem B6072515 : Blo 1798100 6072515 := bstep (se 1 (by rfl) ⟨4554386, by rfl⟩ : syracuseStep 6072515 = 9108773) B9108773
theorem B2697425 : Blo 1798100 2697425 := bstep (se 2 (by rfl) ⟨1011534, by rfl⟩ : syracuseStep 2697425 = 2023069) B2023069
theorem B2697443 : Blo 1798100 2697443 := bstep (se 1 (by rfl) ⟨2023082, by rfl⟩ : syracuseStep 2697443 = 4046165) B4046165
theorem B2697473 : Blo 1798100 2697473 := bstep (se 2 (by rfl) ⟨1011552, by rfl⟩ : syracuseStep 2697473 = 2023105) B2023105
theorem B8644877 : Blo 1798100 8644877 := bstep (se 3 (by rfl) ⟨1620914, by rfl⟩ : syracuseStep 8644877 = 3241829) B3241829
theorem B2697491 : Blo 1798100 2697491 := bstep (se 1 (by rfl) ⟨2023118, by rfl⟩ : syracuseStep 2697491 = 4046237) B4046237
theorem B2697521 : Blo 1798100 2697521 := bstep (se 2 (by rfl) ⟨1011570, by rfl⟩ : syracuseStep 2697521 = 2023141) B2023141
theorem B11528497 : Blo 1798100 11528497 := bstep (se 2 (by rfl) ⟨4323186, by rfl⟩ : syracuseStep 11528497 = 8646373) B8646373
theorem B2697539 : Blo 1798100 2697539 := bstep (se 1 (by rfl) ⟨2023154, by rfl⟩ : syracuseStep 2697539 = 4046309) B4046309
theorem B2697569 : Blo 1798100 2697569 := bstep (se 2 (by rfl) ⟨1011588, by rfl⟩ : syracuseStep 2697569 = 2023177) B2023177
theorem B2697587 : Blo 1798100 2697587 := bstep (se 1 (by rfl) ⟨2023190, by rfl⟩ : syracuseStep 2697587 = 4046381) B4046381
theorem B2697617 : Blo 1798100 2697617 := bstep (se 2 (by rfl) ⟨1011606, by rfl⟩ : syracuseStep 2697617 = 2023213) B2023213
theorem B4049297 : Blo 1798100 4049297 := bstep (se 2 (by rfl) ⟨1518486, by rfl⟩ : syracuseStep 4049297 = 3036973) B3036973
theorem B2697635 : Blo 1798100 2697635 := bstep (se 1 (by rfl) ⟨2023226, by rfl⟩ : syracuseStep 2697635 = 4046453) B4046453
theorem B4049315 : Blo 1798100 4049315 := bstep (se 1 (by rfl) ⟨3036986, by rfl⟩ : syracuseStep 4049315 = 6073973) B6073973
theorem B2697665 : Blo 1798100 2697665 := bstep (se 2 (by rfl) ⟨1011624, by rfl⟩ : syracuseStep 2697665 = 2023249) B2023249
theorem B9112013 : Blo 1798100 9112013 := bstep (se 3 (by rfl) ⟨1708502, by rfl⟩ : syracuseStep 9112013 = 3417005) B3417005
theorem B6072785 : Blo 1798100 6072785 := bstep (se 2 (by rfl) ⟨2277294, by rfl⟩ : syracuseStep 6072785 = 4554589) B4554589
theorem B2697683 : Blo 1798100 2697683 := bstep (se 1 (by rfl) ⟨2023262, by rfl⟩ : syracuseStep 2697683 = 4046525) B4046525
theorem B2697713 : Blo 1798100 2697713 := bstep (se 2 (by rfl) ⟨1011642, by rfl⟩ : syracuseStep 2697713 = 2023285) B2023285
theorem B2697731 : Blo 1798100 2697731 := bstep (se 1 (by rfl) ⟨2023298, by rfl⟩ : syracuseStep 2697731 = 4046597) B4046597
theorem B2697761 : Blo 1798100 2697761 := bstep (se 2 (by rfl) ⟨1011660, by rfl⟩ : syracuseStep 2697761 = 2023321) B2023321
theorem B2697779 : Blo 1798100 2697779 := bstep (se 1 (by rfl) ⟨2023334, by rfl⟩ : syracuseStep 2697779 = 4046669) B4046669
theorem B2697809 : Blo 1798100 2697809 := bstep (se 2 (by rfl) ⟨1011678, by rfl⟩ : syracuseStep 2697809 = 2023357) B2023357
theorem B2697827 : Blo 1798100 2697827 := bstep (se 1 (by rfl) ⟨2023370, by rfl⟩ : syracuseStep 2697827 = 4046741) B4046741
theorem B5122673 : Blo 1798100 5122673 := bstep (se 2 (by rfl) ⟨1921002, by rfl⟩ : syracuseStep 5122673 = 3842005) B3842005
theorem B2697857 : Blo 1798100 2697857 := bstep (se 2 (by rfl) ⟨1011696, by rfl⟩ : syracuseStep 2697857 = 2023393) B2023393
theorem B2697875 : Blo 1798100 2697875 := bstep (se 1 (by rfl) ⟨2023406, by rfl⟩ : syracuseStep 2697875 = 4046813) B4046813
theorem B2697905 : Blo 1798100 2697905 := bstep (se 2 (by rfl) ⟨1011714, by rfl⟩ : syracuseStep 2697905 = 2023429) B2023429
theorem B4049585 : Blo 1798100 4049585 := bstep (se 2 (by rfl) ⟨1518594, by rfl⟩ : syracuseStep 4049585 = 3037189) B3037189
theorem B2697923 : Blo 1798100 2697923 := bstep (se 1 (by rfl) ⟨2023442, by rfl⟩ : syracuseStep 2697923 = 4046885) B4046885
theorem B4049603 : Blo 1798100 4049603 := bstep (se 1 (by rfl) ⟨3037202, by rfl⟩ : syracuseStep 4049603 = 6074405) B6074405
theorem B2697953 : Blo 1798100 2697953 := bstep (se 2 (by rfl) ⟨1011732, by rfl⟩ : syracuseStep 2697953 = 2023465) B2023465
theorem B19712753 : Blo 1798100 19712753 := bstep (se 2 (by rfl) ⟨7392282, by rfl⟩ : syracuseStep 19712753 = 14784565) B14784565
theorem B2697971 : Blo 1798100 2697971 := bstep (se 1 (by rfl) ⟨2023478, by rfl⟩ : syracuseStep 2697971 = 4046957) B4046957
theorem B2698001 : Blo 1798100 2698001 := bstep (se 2 (by rfl) ⟨1011750, by rfl⟩ : syracuseStep 2698001 = 2023501) B2023501
theorem B2698019 : Blo 1798100 2698019 := bstep (se 1 (by rfl) ⟨2023514, by rfl⟩ : syracuseStep 2698019 = 4047029) B4047029
theorem B5122865 : Blo 1798100 5122865 := bstep (se 2 (by rfl) ⟨1921074, by rfl⟩ : syracuseStep 5122865 = 3842149) B3842149
theorem B46123829 : Blo 1798100 46123829 := bstep (se 5 (by rfl) ⟨2162054, by rfl⟩ : syracuseStep 46123829 = 4324109) B4324109
theorem B2698049 : Blo 1798100 2698049 := bstep (se 2 (by rfl) ⟨1011768, by rfl⟩ : syracuseStep 2698049 = 2023537) B2023537
theorem B2698067 : Blo 1798100 2698067 := bstep (se 1 (by rfl) ⟨2023550, by rfl⟩ : syracuseStep 2698067 = 4047101) B4047101
theorem B5761891 : Blo 1798100 5761891 := bstep (se 1 (by rfl) ⟨4321418, by rfl⟩ : syracuseStep 5761891 = 8642837) B8642837
theorem B10251107 : Blo 1798100 10251107 := bstep (se 1 (by rfl) ⟨7688330, by rfl⟩ : syracuseStep 10251107 = 15376661) B15376661
theorem B2698097 : Blo 1798100 2698097 := bstep (se 2 (by rfl) ⟨1011786, by rfl⟩ : syracuseStep 2698097 = 2023573) B2023573
theorem B2698115 : Blo 1798100 2698115 := bstep (se 1 (by rfl) ⟨2023586, by rfl⟩ : syracuseStep 2698115 = 4047173) B4047173
theorem B6155149 : Blo 1798100 6155149 := bstep (se 3 (by rfl) ⟨1154090, by rfl⟩ : syracuseStep 6155149 = 2308181) B2308181
theorem B2698145 : Blo 1798100 2698145 := bstep (se 2 (by rfl) ⟨1011804, by rfl⟩ : syracuseStep 2698145 = 2023609) B2023609
theorem B2698163 : Blo 1798100 2698163 := bstep (se 1 (by rfl) ⟨2023622, by rfl⟩ : syracuseStep 2698163 = 4047245) B4047245
theorem B2698193 : Blo 1798100 2698193 := bstep (se 2 (by rfl) ⟨1011822, by rfl⟩ : syracuseStep 2698193 = 2023645) B2023645
theorem B4049873 : Blo 1798100 4049873 := bstep (se 2 (by rfl) ⟨1518702, by rfl⟩ : syracuseStep 4049873 = 3037405) B3037405
theorem B10243043 : Blo 1798100 10243043 := bstep (se 1 (by rfl) ⟨7682282, by rfl⟩ : syracuseStep 10243043 = 15364565) B15364565
theorem B2698211 : Blo 1798100 2698211 := bstep (se 1 (by rfl) ⟨2023658, by rfl⟩ : syracuseStep 2698211 = 4047317) B4047317
theorem B4049891 : Blo 1798100 4049891 := bstep (se 1 (by rfl) ⟨3037418, by rfl⟩ : syracuseStep 4049891 = 6074837) B6074837
theorem B6073325 : Blo 1798100 6073325 := bstep (se 3 (by rfl) ⟨1138748, by rfl⟩ : syracuseStep 6073325 = 2277497) B2277497
theorem B2698241 : Blo 1798100 2698241 := bstep (se 2 (by rfl) ⟨1011840, by rfl⟩ : syracuseStep 2698241 = 2023681) B2023681
theorem B2698259 : Blo 1798100 2698259 := bstep (se 1 (by rfl) ⟨2023694, by rfl⟩ : syracuseStep 2698259 = 4047389) B4047389
theorem B6073379 : Blo 1798100 6073379 := bstep (se 1 (by rfl) ⟨4555034, by rfl⟩ : syracuseStep 6073379 = 9110069) B9110069
theorem B2698289 : Blo 1798100 2698289 := bstep (se 2 (by rfl) ⟨1011858, by rfl⟩ : syracuseStep 2698289 = 2023717) B2023717
theorem B2698307 : Blo 1798100 2698307 := bstep (se 1 (by rfl) ⟨2023730, by rfl⟩ : syracuseStep 2698307 = 4047461) B4047461
theorem B2698337 : Blo 1798100 2698337 := bstep (se 2 (by rfl) ⟨1011876, by rfl⟩ : syracuseStep 2698337 = 2023753) B2023753
theorem B3697777 : Blo 1798100 3697777 := bstep (se 2 (by rfl) ⟨1386666, by rfl⟩ : syracuseStep 3697777 = 2773333) B2773333
theorem B2698355 : Blo 1798100 2698355 := bstep (se 1 (by rfl) ⟨2023766, by rfl⟩ : syracuseStep 2698355 = 4047533) B4047533
theorem B2698385 : Blo 1798100 2698385 := bstep (se 2 (by rfl) ⟨1011894, by rfl⟩ : syracuseStep 2698385 = 2023789) B2023789
theorem B2698403 : Blo 1798100 2698403 := bstep (se 1 (by rfl) ⟨2023802, by rfl⟩ : syracuseStep 2698403 = 4047605) B4047605
theorem B9104561 : Blo 1798100 9104561 := bstep (se 2 (by rfl) ⟨3414210, by rfl⟩ : syracuseStep 9104561 = 6828421) B6828421
theorem B2698433 : Blo 1798100 2698433 := bstep (se 2 (by rfl) ⟨1011912, by rfl⟩ : syracuseStep 2698433 = 2023825) B2023825
theorem B3034307 : Blo 1798100 3034307 := bstep (se 1 (by rfl) ⟨2275730, by rfl⟩ : syracuseStep 3034307 = 4551461) B4551461
theorem B2698451 : Blo 1798100 2698451 := bstep (se 1 (by rfl) ⟨2023838, by rfl⟩ : syracuseStep 2698451 = 4047677) B4047677
theorem B2698481 : Blo 1798100 2698481 := bstep (se 2 (by rfl) ⟨1011930, by rfl⟩ : syracuseStep 2698481 = 2023861) B2023861
theorem B4050161 : Blo 1798100 4050161 := bstep (se 2 (by rfl) ⟨1518810, by rfl⟩ : syracuseStep 4050161 = 3037621) B3037621
theorem B2698499 : Blo 1798100 2698499 := bstep (se 1 (by rfl) ⟨2023874, by rfl⟩ : syracuseStep 2698499 = 4047749) B4047749
theorem B4050179 : Blo 1798100 4050179 := bstep (se 1 (by rfl) ⟨3037634, by rfl⟩ : syracuseStep 4050179 = 6075269) B6075269
theorem B2698529 : Blo 1798100 2698529 := bstep (se 2 (by rfl) ⟨1011948, by rfl⟩ : syracuseStep 2698529 = 2023897) B2023897
theorem B5762353 : Blo 1798100 5762353 := bstep (se 2 (by rfl) ⟨2160882, by rfl⟩ : syracuseStep 5762353 = 4321765) B4321765
theorem B6073649 : Blo 1798100 6073649 := bstep (se 2 (by rfl) ⟨2277618, by rfl⟩ : syracuseStep 6073649 = 4555237) B4555237
theorem B2698547 : Blo 1798100 2698547 := bstep (se 1 (by rfl) ⟨2023910, by rfl⟩ : syracuseStep 2698547 = 4047821) B4047821
theorem B3034435 : Blo 1798100 3034435 := bstep (se 1 (by rfl) ⟨2275826, by rfl⟩ : syracuseStep 3034435 = 4551653) B4551653
theorem B2698577 : Blo 1798100 2698577 := bstep (se 2 (by rfl) ⟨1011966, by rfl⟩ : syracuseStep 2698577 = 2023933) B2023933
theorem B2698595 : Blo 1798100 2698595 := bstep (se 1 (by rfl) ⟨2023946, by rfl⟩ : syracuseStep 2698595 = 4047893) B4047893
theorem B20483441 : Blo 1798100 20483441 := bstep (se 2 (by rfl) ⟨7681290, by rfl⟩ : syracuseStep 20483441 = 15362581) B15362581
theorem B2698625 : Blo 1798100 2698625 := bstep (se 2 (by rfl) ⟨1011984, by rfl⟩ : syracuseStep 2698625 = 2023969) B2023969
theorem B4926865 : Blo 1798100 4926865 := bstep (se 2 (by rfl) ⟨1847574, by rfl⟩ : syracuseStep 4926865 = 3695149) B3695149
theorem B2698643 : Blo 1798100 2698643 := bstep (se 1 (by rfl) ⟨2023982, by rfl⟩ : syracuseStep 2698643 = 4047965) B4047965
theorem B2698673 : Blo 1798100 2698673 := bstep (se 2 (by rfl) ⟨1012002, by rfl⟩ : syracuseStep 2698673 = 2024005) B2024005
theorem B2698691 : Blo 1798100 2698691 := bstep (se 1 (by rfl) ⟨2024018, by rfl⟩ : syracuseStep 2698691 = 4048037) B4048037
theorem B3034577 : Blo 1798100 3034577 := bstep (se 2 (by rfl) ⟨1137966, by rfl⟩ : syracuseStep 3034577 = 2275933) B2275933
theorem B2698721 : Blo 1798100 2698721 := bstep (se 2 (by rfl) ⟨1012020, by rfl⟩ : syracuseStep 2698721 = 2024041) B2024041
theorem B2698739 : Blo 1798100 2698739 := bstep (se 1 (by rfl) ⟨2024054, by rfl⟩ : syracuseStep 2698739 = 4048109) B4048109
theorem B2698769 : Blo 1798100 2698769 := bstep (se 2 (by rfl) ⟨1012038, by rfl⟩ : syracuseStep 2698769 = 2024077) B2024077
theorem B2698787 : Blo 1798100 2698787 := bstep (se 1 (by rfl) ⟨2024090, by rfl⟩ : syracuseStep 2698787 = 4048181) B4048181
theorem B2698817 : Blo 1798100 2698817 := bstep (se 2 (by rfl) ⟨1012056, by rfl⟩ : syracuseStep 2698817 = 2024113) B2024113
theorem B3034705 : Blo 1798100 3034705 := bstep (se 2 (by rfl) ⟨1138014, by rfl⟩ : syracuseStep 3034705 = 2276029) B2276029
theorem B2698835 : Blo 1798100 2698835 := bstep (se 1 (by rfl) ⟨2024126, by rfl⟩ : syracuseStep 2698835 = 4048253) B4048253
theorem B4320881 : Blo 1798100 4320881 := bstep (se 2 (by rfl) ⟨1620330, by rfl⟩ : syracuseStep 4320881 = 3240661) B3240661
theorem B2698865 : Blo 1798100 2698865 := bstep (se 2 (by rfl) ⟨1012074, by rfl⟩ : syracuseStep 2698865 = 2024149) B2024149
theorem B3034739 : Blo 1798100 3034739 := bstep (se 1 (by rfl) ⟨2276054, by rfl⟩ : syracuseStep 3034739 = 4552109) B4552109
theorem B2698883 : Blo 1798100 2698883 := bstep (se 1 (by rfl) ⟨2024162, by rfl⟩ : syracuseStep 2698883 = 4048325) B4048325
theorem B2698913 : Blo 1798100 2698913 := bstep (se 2 (by rfl) ⟨1012092, by rfl⟩ : syracuseStep 2698913 = 2024185) B2024185
theorem B2698931 : Blo 1798100 2698931 := bstep (se 1 (by rfl) ⟨2024198, by rfl⟩ : syracuseStep 2698931 = 4048397) B4048397
theorem B19451573 : Blo 1798100 19451573 := bstep (se 5 (by rfl) ⟨911792, by rfl⟩ : syracuseStep 19451573 = 1823585) B1823585
theorem B2698961 : Blo 1798100 2698961 := bstep (se 2 (by rfl) ⟨1012110, by rfl⟩ : syracuseStep 2698961 = 2024221) B2024221
theorem B2698979 : Blo 1798100 2698979 := bstep (se 1 (by rfl) ⟨2024234, by rfl⟩ : syracuseStep 2698979 = 4048469) B4048469
theorem B3034867 : Blo 1798100 3034867 := bstep (se 1 (by rfl) ⟨2276150, by rfl⟩ : syracuseStep 3034867 = 4552301) B4552301
theorem B2699009 : Blo 1798100 2699009 := bstep (se 2 (by rfl) ⟨1012128, by rfl⟩ : syracuseStep 2699009 = 2024257) B2024257
theorem B5123857 : Blo 1798100 5123857 := bstep (se 2 (by rfl) ⟨1921446, by rfl⟩ : syracuseStep 5123857 = 3842893) B3842893
theorem B2699027 : Blo 1798100 2699027 := bstep (se 1 (by rfl) ⟨2024270, by rfl⟩ : syracuseStep 2699027 = 4048541) B4048541
theorem B2699057 : Blo 1798100 2699057 := bstep (se 2 (by rfl) ⟨1012146, by rfl⟩ : syracuseStep 2699057 = 2024293) B2024293
theorem B2699075 : Blo 1798100 2699075 := bstep (se 1 (by rfl) ⟨2024306, by rfl⟩ : syracuseStep 2699075 = 4048613) B4048613
theorem B6074189 : Blo 1798100 6074189 := bstep (se 3 (by rfl) ⟨1138910, by rfl⟩ : syracuseStep 6074189 = 2277821) B2277821
theorem B10252109 : Blo 1798100 10252109 := bstep (se 3 (by rfl) ⟨1922270, by rfl⟩ : syracuseStep 10252109 = 3844541) B3844541
theorem B2699105 : Blo 1798100 2699105 := bstep (se 2 (by rfl) ⟨1012164, by rfl⟩ : syracuseStep 2699105 = 2024329) B2024329
theorem B2699123 : Blo 1798100 2699123 := bstep (se 1 (by rfl) ⟨2024342, by rfl⟩ : syracuseStep 2699123 = 4048685) B4048685
theorem B3035009 : Blo 1798100 3035009 := bstep (se 2 (by rfl) ⟨1138128, by rfl⟩ : syracuseStep 3035009 = 2276257) B2276257
theorem B6074243 : Blo 1798100 6074243 := bstep (se 1 (by rfl) ⟨4555682, by rfl⟩ : syracuseStep 6074243 = 9111365) B9111365
theorem B2699153 : Blo 1798100 2699153 := bstep (se 2 (by rfl) ⟨1012182, by rfl⟩ : syracuseStep 2699153 = 2024365) B2024365
theorem B2699171 : Blo 1798100 2699171 := bstep (se 1 (by rfl) ⟨2024378, by rfl⟩ : syracuseStep 2699171 = 4048757) B4048757
theorem B2699201 : Blo 1798100 2699201 := bstep (se 2 (by rfl) ⟨1012200, by rfl⟩ : syracuseStep 2699201 = 2024401) B2024401
theorem B8204237 : Blo 1798100 8204237 := bstep (se 3 (by rfl) ⟨1538294, by rfl⟩ : syracuseStep 8204237 = 3076589) B3076589
theorem B2699219 : Blo 1798100 2699219 := bstep (se 1 (by rfl) ⟨2024414, by rfl⟩ : syracuseStep 2699219 = 4048829) B4048829
theorem B1798115 : Blo 1798100 1798115 := bstep (se 1 (by rfl) ⟨1348586, by rfl⟩ : syracuseStep 1798115 = 2697173) B2697173
theorem B2699249 : Blo 1798100 2699249 := bstep (se 2 (by rfl) ⟨1012218, by rfl⟩ : syracuseStep 2699249 = 2024437) B2024437
theorem B1798131 : Blo 1798100 1798131 := bstep (se 1 (by rfl) ⟨1348598, by rfl⟩ : syracuseStep 1798131 = 2697197) B2697197
theorem B3035137 : Blo 1798100 3035137 := bstep (se 2 (by rfl) ⟨1138176, by rfl⟩ : syracuseStep 3035137 = 2276353) B2276353
theorem B1798147 : Blo 1798100 1798147 := bstep (se 1 (by rfl) ⟨1348610, by rfl⟩ : syracuseStep 1798147 = 2697221) B2697221
theorem B2699267 : Blo 1798100 2699267 := bstep (se 1 (by rfl) ⟨2024450, by rfl⟩ : syracuseStep 2699267 = 4048901) B4048901
theorem B1798163 : Blo 1798100 1798163 := bstep (se 1 (by rfl) ⟨1348622, by rfl⟩ : syracuseStep 1798163 = 2697245) B2697245
theorem B2699297 : Blo 1798100 2699297 := bstep (se 2 (by rfl) ⟨1012236, by rfl⟩ : syracuseStep 2699297 = 2024473) B2024473
theorem B1798179 : Blo 1798100 1798179 := bstep (se 1 (by rfl) ⟨1348634, by rfl⟩ : syracuseStep 1798179 = 2697269) B2697269
theorem B3035171 : Blo 1798100 3035171 := bstep (se 1 (by rfl) ⟨2276378, by rfl⟩ : syracuseStep 3035171 = 4552757) B4552757
theorem B5124131 : Blo 1798100 5124131 := bstep (se 1 (by rfl) ⟨3843098, by rfl⟩ : syracuseStep 5124131 = 7686197) B7686197
theorem B1798195 : Blo 1798100 1798195 := bstep (se 1 (by rfl) ⟨1348646, by rfl⟩ : syracuseStep 1798195 = 2697293) B2697293
theorem B1822771 : Blo 1798100 1822771 := bstep (se 1 (by rfl) ⟨1367078, by rfl⟩ : syracuseStep 1822771 = 2734157) B2734157
theorem B2699315 : Blo 1798100 2699315 := bstep (se 1 (by rfl) ⟨2024486, by rfl⟩ : syracuseStep 2699315 = 4048973) B4048973
theorem B1798211 : Blo 1798100 1798211 := bstep (se 1 (by rfl) ⟨1348658, by rfl⟩ : syracuseStep 1798211 = 2697317) B2697317
theorem B2699345 : Blo 1798100 2699345 := bstep (se 2 (by rfl) ⟨1012254, by rfl⟩ : syracuseStep 2699345 = 2024509) B2024509
theorem B1798227 : Blo 1798100 1798227 := bstep (se 1 (by rfl) ⟨1348670, by rfl⟩ : syracuseStep 1798227 = 2697341) B2697341
theorem B1798243 : Blo 1798100 1798243 := bstep (se 1 (by rfl) ⟨1348682, by rfl⟩ : syracuseStep 1798243 = 2697365) B2697365
theorem B2699363 : Blo 1798100 2699363 := bstep (se 1 (by rfl) ⟨2024522, by rfl⟩ : syracuseStep 2699363 = 4049045) B4049045
theorem B1798259 : Blo 1798100 1798259 := bstep (se 1 (by rfl) ⟨1348694, by rfl⟩ : syracuseStep 1798259 = 2697389) B2697389
theorem B2191475 : Blo 1798100 2191475 := bstep (se 1 (by rfl) ⟨1643606, by rfl⟩ : syracuseStep 2191475 = 3287213) B3287213
theorem B2699393 : Blo 1798100 2699393 := bstep (se 2 (by rfl) ⟨1012272, by rfl⟩ : syracuseStep 2699393 = 2024545) B2024545
theorem B1798275 : Blo 1798100 1798275 := bstep (se 1 (by rfl) ⟨1348706, by rfl⟩ : syracuseStep 1798275 = 2697413) B2697413
theorem B6074513 : Blo 1798100 6074513 := bstep (se 2 (by rfl) ⟨2277942, by rfl⟩ : syracuseStep 6074513 = 4555885) B4555885
theorem B1798291 : Blo 1798100 1798291 := bstep (se 1 (by rfl) ⟨1348718, by rfl⟩ : syracuseStep 1798291 = 2697437) B2697437
theorem B2699411 : Blo 1798100 2699411 := bstep (se 1 (by rfl) ⟨2024558, by rfl⟩ : syracuseStep 2699411 = 4049117) B4049117
theorem B1798307 : Blo 1798100 1798307 := bstep (se 1 (by rfl) ⟨1348730, by rfl⟩ : syracuseStep 1798307 = 2697461) B2697461
theorem B3035299 : Blo 1798100 3035299 := bstep (se 1 (by rfl) ⟨2276474, by rfl⟩ : syracuseStep 3035299 = 4552949) B4552949
theorem B6828209 : Blo 1798100 6828209 := bstep (se 2 (by rfl) ⟨2560578, by rfl⟩ : syracuseStep 6828209 = 5121157) B5121157
theorem B2699441 : Blo 1798100 2699441 := bstep (se 2 (by rfl) ⟨1012290, by rfl⟩ : syracuseStep 2699441 = 2024581) B2024581
theorem B1798323 : Blo 1798100 1798323 := bstep (se 1 (by rfl) ⟨1348742, by rfl⟩ : syracuseStep 1798323 = 2697485) B2697485
theorem B1798339 : Blo 1798100 1798339 := bstep (se 1 (by rfl) ⟨1348754, by rfl⟩ : syracuseStep 1798339 = 2697509) B2697509
theorem B2699459 : Blo 1798100 2699459 := bstep (se 1 (by rfl) ⟨2024594, by rfl⟩ : syracuseStep 2699459 = 4049189) B4049189
theorem B1798355 : Blo 1798100 1798355 := bstep (se 1 (by rfl) ⟨1348766, by rfl⟩ : syracuseStep 1798355 = 2697533) B2697533
theorem B2699489 : Blo 1798100 2699489 := bstep (se 2 (by rfl) ⟨1012308, by rfl⟩ : syracuseStep 2699489 = 2024617) B2024617
theorem B1798371 : Blo 1798100 1798371 := bstep (se 1 (by rfl) ⟨1348778, by rfl⟩ : syracuseStep 1798371 = 2697557) B2697557
theorem B5124323 : Blo 1798100 5124323 := bstep (se 1 (by rfl) ⟨3843242, by rfl⟩ : syracuseStep 5124323 = 7686485) B7686485
theorem B2560243 : Blo 1798100 2560243 := bstep (se 1 (by rfl) ⟨1920182, by rfl⟩ : syracuseStep 2560243 = 3840365) B3840365
theorem B1798387 : Blo 1798100 1798387 := bstep (se 1 (by rfl) ⟨1348790, by rfl⟩ : syracuseStep 1798387 = 2697581) B2697581
theorem B2699507 : Blo 1798100 2699507 := bstep (se 1 (by rfl) ⟨2024630, by rfl⟩ : syracuseStep 2699507 = 4049261) B4049261
theorem B1798403 : Blo 1798100 1798403 := bstep (se 1 (by rfl) ⟨1348802, by rfl⟩ : syracuseStep 1798403 = 2697605) B2697605
theorem B2699537 : Blo 1798100 2699537 := bstep (se 2 (by rfl) ⟨1012326, by rfl⟩ : syracuseStep 2699537 = 2024653) B2024653
theorem B1798419 : Blo 1798100 1798419 := bstep (se 1 (by rfl) ⟨1348814, by rfl⟩ : syracuseStep 1798419 = 2697629) B2697629
theorem B1798435 : Blo 1798100 1798435 := bstep (se 1 (by rfl) ⟨1348826, by rfl⟩ : syracuseStep 1798435 = 2697653) B2697653
theorem B2699555 : Blo 1798100 2699555 := bstep (se 1 (by rfl) ⟨2024666, by rfl⟩ : syracuseStep 2699555 = 4049333) B4049333
theorem B3035441 : Blo 1798100 3035441 := bstep (se 2 (by rfl) ⟨1138290, by rfl⟩ : syracuseStep 3035441 = 2276581) B2276581
theorem B1798451 : Blo 1798100 1798451 := bstep (se 1 (by rfl) ⟨1348838, by rfl⟩ : syracuseStep 1798451 = 2697677) B2697677
theorem B1921331 : Blo 1798100 1921331 := bstep (se 1 (by rfl) ⟨1440998, by rfl⟩ : syracuseStep 1921331 = 2881997) B2881997
theorem B2699585 : Blo 1798100 2699585 := bstep (se 2 (by rfl) ⟨1012344, by rfl⟩ : syracuseStep 2699585 = 2024689) B2024689
theorem B1798467 : Blo 1798100 1798467 := bstep (se 1 (by rfl) ⟨1348850, by rfl⟩ : syracuseStep 1798467 = 2697701) B2697701
theorem B2560339 : Blo 1798100 2560339 := bstep (se 1 (by rfl) ⟨1920254, by rfl⟩ : syracuseStep 2560339 = 3840509) B3840509
theorem B1798483 : Blo 1798100 1798483 := bstep (se 1 (by rfl) ⟨1348862, by rfl⟩ : syracuseStep 1798483 = 2697725) B2697725
theorem B2699603 : Blo 1798100 2699603 := bstep (se 1 (by rfl) ⟨2024702, by rfl⟩ : syracuseStep 2699603 = 4049405) B4049405
theorem B1798499 : Blo 1798100 1798499 := bstep (se 1 (by rfl) ⟨1348874, by rfl⟩ : syracuseStep 1798499 = 2697749) B2697749
theorem B2699633 : Blo 1798100 2699633 := bstep (se 2 (by rfl) ⟨1012362, by rfl⟩ : syracuseStep 2699633 = 2024725) B2024725
theorem B1798515 : Blo 1798100 1798515 := bstep (se 1 (by rfl) ⟨1348886, by rfl⟩ : syracuseStep 1798515 = 2697773) B2697773
theorem B1798531 : Blo 1798100 1798531 := bstep (se 1 (by rfl) ⟨1348898, by rfl⟩ : syracuseStep 1798531 = 2697797) B2697797
theorem B2699651 : Blo 1798100 2699651 := bstep (se 1 (by rfl) ⟨2024738, by rfl⟩ : syracuseStep 2699651 = 4049477) B4049477
theorem B13668749 : Blo 1798100 13668749 := bstep (se 3 (by rfl) ⟨2562890, by rfl⟩ : syracuseStep 13668749 = 5125781) B5125781
theorem B1798547 : Blo 1798100 1798547 := bstep (se 1 (by rfl) ⟨1348910, by rfl⟩ : syracuseStep 1798547 = 2697821) B2697821
theorem B2699681 : Blo 1798100 2699681 := bstep (se 2 (by rfl) ⟨1012380, by rfl⟩ : syracuseStep 2699681 = 2024761) B2024761
theorem B1798563 : Blo 1798100 1798563 := bstep (se 1 (by rfl) ⟨1348922, by rfl⟩ : syracuseStep 1798563 = 2697845) B2697845
theorem B3035569 : Blo 1798100 3035569 := bstep (se 2 (by rfl) ⟨1138338, by rfl⟩ : syracuseStep 3035569 = 2276677) B2276677
theorem B1798579 : Blo 1798100 1798579 := bstep (se 1 (by rfl) ⟨1348934, by rfl⟩ : syracuseStep 1798579 = 2697869) B2697869
theorem B2699699 : Blo 1798100 2699699 := bstep (se 1 (by rfl) ⟨2024774, by rfl⟩ : syracuseStep 2699699 = 4049549) B4049549
theorem B1798595 : Blo 1798100 1798595 := bstep (se 1 (by rfl) ⟨1348946, by rfl⟩ : syracuseStep 1798595 = 2697893) B2697893
theorem B2699729 : Blo 1798100 2699729 := bstep (se 2 (by rfl) ⟨1012398, by rfl⟩ : syracuseStep 2699729 = 2024797) B2024797
theorem B1798611 : Blo 1798100 1798611 := bstep (se 1 (by rfl) ⟨1348958, by rfl⟩ : syracuseStep 1798611 = 2697917) B2697917
theorem B3035603 : Blo 1798100 3035603 := bstep (se 1 (by rfl) ⟨2276702, by rfl⟩ : syracuseStep 3035603 = 4553405) B4553405
theorem B1798627 : Blo 1798100 1798627 := bstep (se 1 (by rfl) ⟨1348970, by rfl⟩ : syracuseStep 1798627 = 2697941) B2697941
theorem B2699747 : Blo 1798100 2699747 := bstep (se 1 (by rfl) ⟨2024810, by rfl⟩ : syracuseStep 2699747 = 4049621) B4049621
theorem B1798643 : Blo 1798100 1798643 := bstep (se 1 (by rfl) ⟨1348982, by rfl⟩ : syracuseStep 1798643 = 2697965) B2697965
theorem B2699777 : Blo 1798100 2699777 := bstep (se 2 (by rfl) ⟨1012416, by rfl⟩ : syracuseStep 2699777 = 2024833) B2024833
theorem B1798659 : Blo 1798100 1798659 := bstep (se 1 (by rfl) ⟨1348994, by rfl⟩ : syracuseStep 1798659 = 2697989) B2697989
theorem B1798675 : Blo 1798100 1798675 := bstep (se 1 (by rfl) ⟨1349006, by rfl⟩ : syracuseStep 1798675 = 2698013) B2698013
theorem B2699795 : Blo 1798100 2699795 := bstep (se 1 (by rfl) ⟨2024846, by rfl⟩ : syracuseStep 2699795 = 4049693) B4049693
theorem B1798691 : Blo 1798100 1798691 := bstep (se 1 (by rfl) ⟨1349018, by rfl⟩ : syracuseStep 1798691 = 2698037) B2698037
theorem B2699825 : Blo 1798100 2699825 := bstep (se 2 (by rfl) ⟨1012434, by rfl⟩ : syracuseStep 2699825 = 2024869) B2024869
theorem B1798707 : Blo 1798100 1798707 := bstep (se 1 (by rfl) ⟨1349030, by rfl⟩ : syracuseStep 1798707 = 2698061) B2698061
theorem B1798723 : Blo 1798100 1798723 := bstep (se 1 (by rfl) ⟨1349042, by rfl⟩ : syracuseStep 1798723 = 2698085) B2698085
theorem B2699843 : Blo 1798100 2699843 := bstep (se 1 (by rfl) ⟨2024882, by rfl⟩ : syracuseStep 2699843 = 4049765) B4049765
theorem B1798739 : Blo 1798100 1798739 := bstep (se 1 (by rfl) ⟨1349054, by rfl⟩ : syracuseStep 1798739 = 2698109) B2698109
theorem B3035731 : Blo 1798100 3035731 := bstep (se 1 (by rfl) ⟨2276798, by rfl⟩ : syracuseStep 3035731 = 4553597) B4553597
theorem B2699873 : Blo 1798100 2699873 := bstep (se 2 (by rfl) ⟨1012452, by rfl⟩ : syracuseStep 2699873 = 2024905) B2024905
theorem B9106019 : Blo 1798100 9106019 := bstep (se 1 (by rfl) ⟨6829514, by rfl⟩ : syracuseStep 9106019 = 13659029) B13659029
theorem B1798755 : Blo 1798100 1798755 := bstep (se 1 (by rfl) ⟨1349066, by rfl⟩ : syracuseStep 1798755 = 2698133) B2698133
theorem B1798771 : Blo 1798100 1798771 := bstep (se 1 (by rfl) ⟨1349078, by rfl⟩ : syracuseStep 1798771 = 2698157) B2698157
theorem B2699891 : Blo 1798100 2699891 := bstep (se 1 (by rfl) ⟨2024918, by rfl⟩ : syracuseStep 2699891 = 4049837) B4049837
theorem B1798787 : Blo 1798100 1798787 := bstep (se 1 (by rfl) ⟨1349090, by rfl⟩ : syracuseStep 1798787 = 2698181) B2698181
theorem B2699921 : Blo 1798100 2699921 := bstep (se 2 (by rfl) ⟨1012470, by rfl⟩ : syracuseStep 2699921 = 2024941) B2024941
theorem B1798803 : Blo 1798100 1798803 := bstep (se 1 (by rfl) ⟨1349102, by rfl⟩ : syracuseStep 1798803 = 2698205) B2698205
theorem B3117731 : Blo 1798100 3117731 := bstep (se 1 (by rfl) ⟨2338298, by rfl⟩ : syracuseStep 3117731 = 4676597) B4676597
theorem B1798819 : Blo 1798100 1798819 := bstep (se 1 (by rfl) ⟨1349114, by rfl⟩ : syracuseStep 1798819 = 2698229) B2698229
theorem B2699939 : Blo 1798100 2699939 := bstep (se 1 (by rfl) ⟨2024954, by rfl⟩ : syracuseStep 2699939 = 4049909) B4049909
theorem B1798835 : Blo 1798100 1798835 := bstep (se 1 (by rfl) ⟨1349126, by rfl⟩ : syracuseStep 1798835 = 2698253) B2698253
theorem B2699969 : Blo 1798100 2699969 := bstep (se 2 (by rfl) ⟨1012488, by rfl⟩ : syracuseStep 2699969 = 2024977) B2024977
theorem B1798851 : Blo 1798100 1798851 := bstep (se 1 (by rfl) ⟨1349138, by rfl⟩ : syracuseStep 1798851 = 2698277) B2698277
theorem B1798867 : Blo 1798100 1798867 := bstep (se 1 (by rfl) ⟨1349150, by rfl⟩ : syracuseStep 1798867 = 2698301) B2698301
theorem B2699987 : Blo 1798100 2699987 := bstep (se 1 (by rfl) ⟨2024990, by rfl⟩ : syracuseStep 2699987 = 4049981) B4049981
theorem B3035873 : Blo 1798100 3035873 := bstep (se 2 (by rfl) ⟨1138452, by rfl⟩ : syracuseStep 3035873 = 2276905) B2276905
theorem B1798883 : Blo 1798100 1798883 := bstep (se 1 (by rfl) ⟨1349162, by rfl⟩ : syracuseStep 1798883 = 2698325) B2698325
theorem B6075107 : Blo 1798100 6075107 := bstep (se 1 (by rfl) ⟨4556330, by rfl⟩ : syracuseStep 6075107 = 9112661) B9112661
theorem B2700017 : Blo 1798100 2700017 := bstep (se 2 (by rfl) ⟨1012506, by rfl⟩ : syracuseStep 2700017 = 2025013) B2025013
theorem B7688945 : Blo 1798100 7688945 := bstep (se 2 (by rfl) ⟨2883354, by rfl⟩ : syracuseStep 7688945 = 5766709) B5766709
theorem B1798899 : Blo 1798100 1798899 := bstep (se 1 (by rfl) ⟨1349174, by rfl⟩ : syracuseStep 1798899 = 2698349) B2698349
theorem B1798915 : Blo 1798100 1798915 := bstep (se 1 (by rfl) ⟨1349186, by rfl⟩ : syracuseStep 1798915 = 2698373) B2698373
theorem B2700035 : Blo 1798100 2700035 := bstep (se 1 (by rfl) ⟨2025026, by rfl⟩ : syracuseStep 2700035 = 4050053) B4050053
theorem B1798931 : Blo 1798100 1798931 := bstep (se 1 (by rfl) ⟨1349198, by rfl⟩ : syracuseStep 1798931 = 2698397) B2698397
theorem B2700065 : Blo 1798100 2700065 := bstep (se 2 (by rfl) ⟨1012524, by rfl⟩ : syracuseStep 2700065 = 2025049) B2025049
theorem B1798947 : Blo 1798100 1798947 := bstep (se 1 (by rfl) ⟨1349210, by rfl⟩ : syracuseStep 1798947 = 2698421) B2698421
theorem B1798963 : Blo 1798100 1798963 := bstep (se 1 (by rfl) ⟨1349222, by rfl⟩ : syracuseStep 1798963 = 2698445) B2698445
theorem B2700083 : Blo 1798100 2700083 := bstep (se 1 (by rfl) ⟨2025062, by rfl⟩ : syracuseStep 2700083 = 4050125) B4050125
theorem B4551491 : Blo 1798100 4551491 := bstep (se 1 (by rfl) ⟨3413618, by rfl⟩ : syracuseStep 4551491 = 6827237) B6827237
theorem B2560835 : Blo 1798100 2560835 := bstep (se 1 (by rfl) ⟨1920626, by rfl⟩ : syracuseStep 2560835 = 3841253) B3841253
theorem B1798979 : Blo 1798100 1798979 := bstep (se 1 (by rfl) ⟨1349234, by rfl⟩ : syracuseStep 1798979 = 2698469) B2698469
theorem B10384205 : Blo 1798100 10384205 := bstep (se 3 (by rfl) ⟨1947038, by rfl⟩ : syracuseStep 10384205 = 3894077) B3894077
theorem B2700113 : Blo 1798100 2700113 := bstep (se 2 (by rfl) ⟨1012542, by rfl⟩ : syracuseStep 2700113 = 2025085) B2025085
theorem B1798995 : Blo 1798100 1798995 := bstep (se 1 (by rfl) ⟨1349246, by rfl⟩ : syracuseStep 1798995 = 2698493) B2698493
theorem B1799011 : Blo 1798100 1799011 := bstep (se 1 (by rfl) ⟨1349258, by rfl⟩ : syracuseStep 1799011 = 2698517) B2698517
theorem B3036001 : Blo 1798100 3036001 := bstep (se 2 (by rfl) ⟨1138500, by rfl⟩ : syracuseStep 3036001 = 2277001) B2277001
theorem B2700131 : Blo 1798100 2700131 := bstep (se 1 (by rfl) ⟨2025098, by rfl⟩ : syracuseStep 2700131 = 4050197) B4050197
theorem B7680881 : Blo 1798100 7680881 := bstep (se 2 (by rfl) ⟨2880330, by rfl⟩ : syracuseStep 7680881 = 5760661) B5760661
theorem B1799027 : Blo 1798100 1799027 := bstep (se 1 (by rfl) ⟨1349270, by rfl⟩ : syracuseStep 1799027 = 2698541) B2698541
theorem B1799043 : Blo 1798100 1799043 := bstep (se 1 (by rfl) ⟨1349282, by rfl⟩ : syracuseStep 1799043 = 2698565) B2698565
theorem B3036035 : Blo 1798100 3036035 := bstep (se 1 (by rfl) ⟨2277026, by rfl⟩ : syracuseStep 3036035 = 4554053) B4554053
theorem B19461005 : Blo 1798100 19461005 := bstep (se 3 (by rfl) ⟨3648938, by rfl⟩ : syracuseStep 19461005 = 7297877) B7297877
theorem B1799059 : Blo 1798100 1799059 := bstep (se 1 (by rfl) ⟨1349294, by rfl⟩ : syracuseStep 1799059 = 2698589) B2698589
theorem B1799075 : Blo 1798100 1799075 := bstep (se 1 (by rfl) ⟨1349306, by rfl⟩ : syracuseStep 1799075 = 2698613) B2698613
theorem B1799091 : Blo 1798100 1799091 := bstep (se 1 (by rfl) ⟨1349318, by rfl⟩ : syracuseStep 1799091 = 2698637) B2698637
theorem B1799107 : Blo 1798100 1799107 := bstep (se 1 (by rfl) ⟨1349330, by rfl⟩ : syracuseStep 1799107 = 2698661) B2698661
theorem B1823683 : Blo 1798100 1823683 := bstep (se 1 (by rfl) ⟨1367762, by rfl⟩ : syracuseStep 1823683 = 2735525) B2735525
theorem B1799123 : Blo 1798100 1799123 := bstep (se 1 (by rfl) ⟨1349342, by rfl⟩ : syracuseStep 1799123 = 2698685) B2698685
theorem B1799139 : Blo 1798100 1799139 := bstep (se 1 (by rfl) ⟨1349354, by rfl⟩ : syracuseStep 1799139 = 2698709) B2698709
theorem B28079075 : Blo 1798100 28079075 := bstep (se 1 (by rfl) ⟨21059306, by rfl⟩ : syracuseStep 28079075 = 42118613) B42118613
theorem B1799155 : Blo 1798100 1799155 := bstep (se 1 (by rfl) ⟨1349366, by rfl⟩ : syracuseStep 1799155 = 2698733) B2698733
theorem B1799171 : Blo 1798100 1799171 := bstep (se 1 (by rfl) ⟨1349378, by rfl⟩ : syracuseStep 1799171 = 2698757) B2698757
theorem B3036163 : Blo 1798100 3036163 := bstep (se 1 (by rfl) ⟨2277122, by rfl⟩ : syracuseStep 3036163 = 4554245) B4554245
theorem B5125133 : Blo 1798100 5125133 := bstep (se 3 (by rfl) ⟨960962, by rfl⟩ : syracuseStep 5125133 = 1921925) B1921925
theorem B6927373 : Blo 1798100 6927373 := bstep (se 3 (by rfl) ⟨1298882, by rfl⟩ : syracuseStep 6927373 = 2597765) B2597765
theorem B1799187 : Blo 1798100 1799187 := bstep (se 1 (by rfl) ⟨1349390, by rfl⟩ : syracuseStep 1799187 = 2698781) B2698781
theorem B1799203 : Blo 1798100 1799203 := bstep (se 1 (by rfl) ⟨1349402, by rfl⟩ : syracuseStep 1799203 = 2698805) B2698805
theorem B1799219 : Blo 1798100 1799219 := bstep (se 1 (by rfl) ⟨1349414, by rfl⟩ : syracuseStep 1799219 = 2698829) B2698829
theorem B1799235 : Blo 1798100 1799235 := bstep (se 1 (by rfl) ⟨1349426, by rfl⟩ : syracuseStep 1799235 = 2698853) B2698853
theorem B1799251 : Blo 1798100 1799251 := bstep (se 1 (by rfl) ⟨1349438, by rfl⟩ : syracuseStep 1799251 = 2698877) B2698877
theorem B1799267 : Blo 1798100 1799267 := bstep (se 1 (by rfl) ⟨1349450, by rfl⟩ : syracuseStep 1799267 = 2698901) B2698901
theorem B1799283 : Blo 1798100 1799283 := bstep (se 1 (by rfl) ⟨1349462, by rfl⟩ : syracuseStep 1799283 = 2698925) B2698925
theorem B1799299 : Blo 1798100 1799299 := bstep (se 1 (by rfl) ⟨1349474, by rfl⟩ : syracuseStep 1799299 = 2698949) B2698949
theorem B29176973 : Blo 1798100 29176973 := bstep (se 3 (by rfl) ⟨5470682, by rfl⟩ : syracuseStep 29176973 = 10941365) B10941365
theorem B3036305 : Blo 1798100 3036305 := bstep (se 2 (by rfl) ⟨1138614, by rfl⟩ : syracuseStep 3036305 = 2277229) B2277229
theorem B2921617 : Blo 1798100 2921617 := bstep (se 2 (by rfl) ⟨1095606, by rfl⟩ : syracuseStep 2921617 = 2191213) B2191213
theorem B1799315 : Blo 1798100 1799315 := bstep (se 1 (by rfl) ⟨1349486, by rfl⟩ : syracuseStep 1799315 = 2698973) B2698973
theorem B1799331 : Blo 1798100 1799331 := bstep (se 1 (by rfl) ⟨1349498, by rfl⟩ : syracuseStep 1799331 = 2698997) B2698997
theorem B2880689 : Blo 1798100 2880689 := bstep (se 2 (by rfl) ⟨1080258, by rfl⟩ : syracuseStep 2880689 = 2160517) B2160517
theorem B11687089 : Blo 1798100 11687089 := bstep (se 2 (by rfl) ⟨4382658, by rfl⟩ : syracuseStep 11687089 = 8765317) B8765317
theorem B1799347 : Blo 1798100 1799347 := bstep (se 1 (by rfl) ⟨1349510, by rfl⟩ : syracuseStep 1799347 = 2699021) B2699021
theorem B1799363 : Blo 1798100 1799363 := bstep (se 1 (by rfl) ⟨1349522, by rfl⟩ : syracuseStep 1799363 = 2699045) B2699045
theorem B5125315 : Blo 1798100 5125315 := bstep (se 1 (by rfl) ⟨3843986, by rfl⟩ : syracuseStep 5125315 = 7687973) B7687973
theorem B1799379 : Blo 1798100 1799379 := bstep (se 1 (by rfl) ⟨1349534, by rfl⟩ : syracuseStep 1799379 = 2699069) B2699069
theorem B1799395 : Blo 1798100 1799395 := bstep (se 1 (by rfl) ⟨1349546, by rfl⟩ : syracuseStep 1799395 = 2699093) B2699093
theorem B1799411 : Blo 1798100 1799411 := bstep (se 1 (by rfl) ⟨1349558, by rfl⟩ : syracuseStep 1799411 = 2699117) B2699117
theorem B1799427 : Blo 1798100 1799427 := bstep (se 1 (by rfl) ⟨1349570, by rfl⟩ : syracuseStep 1799427 = 2699141) B2699141
theorem B3036433 : Blo 1798100 3036433 := bstep (se 2 (by rfl) ⟨1138662, by rfl⟩ : syracuseStep 3036433 = 2277325) B2277325
theorem B1799443 : Blo 1798100 1799443 := bstep (se 1 (by rfl) ⟨1349582, by rfl⟩ : syracuseStep 1799443 = 2699165) B2699165
theorem B1799459 : Blo 1798100 1799459 := bstep (se 1 (by rfl) ⟨1349594, by rfl⟩ : syracuseStep 1799459 = 2699189) B2699189
theorem B3036467 : Blo 1798100 3036467 := bstep (se 1 (by rfl) ⟨2277350, by rfl⟩ : syracuseStep 3036467 = 4554701) B4554701
theorem B1799475 : Blo 1798100 1799475 := bstep (se 1 (by rfl) ⟨1349606, by rfl⟩ : syracuseStep 1799475 = 2699213) B2699213
theorem B1799491 : Blo 1798100 1799491 := bstep (se 1 (by rfl) ⟨1349618, by rfl⟩ : syracuseStep 1799491 = 2699237) B2699237
theorem B24958277 : Blo 1798100 24958277 := bstep (se 4 (by rfl) ⟨2339838, by rfl⟩ : syracuseStep 24958277 = 4679677) B4679677
theorem B1799507 : Blo 1798100 1799507 := bstep (se 1 (by rfl) ⟨1349630, by rfl⟩ : syracuseStep 1799507 = 2699261) B2699261
theorem B5469539 : Blo 1798100 5469539 := bstep (se 1 (by rfl) ⟨4102154, by rfl⟩ : syracuseStep 5469539 = 8204309) B8204309
theorem B1799523 : Blo 1798100 1799523 := bstep (se 1 (by rfl) ⟨1349642, by rfl⟩ : syracuseStep 1799523 = 2699285) B2699285
theorem B1799539 : Blo 1798100 1799539 := bstep (se 1 (by rfl) ⟨1349654, by rfl⟩ : syracuseStep 1799539 = 2699309) B2699309
theorem B1799555 : Blo 1798100 1799555 := bstep (se 1 (by rfl) ⟨1349666, by rfl⟩ : syracuseStep 1799555 = 2699333) B2699333
theorem B9106829 : Blo 1798100 9106829 := bstep (se 3 (by rfl) ⟨1707530, by rfl⟩ : syracuseStep 9106829 = 3415061) B3415061
theorem B1799571 : Blo 1798100 1799571 := bstep (se 1 (by rfl) ⟨1349678, by rfl⟩ : syracuseStep 1799571 = 2699357) B2699357
theorem B1799587 : Blo 1798100 1799587 := bstep (se 1 (by rfl) ⟨1349690, by rfl⟩ : syracuseStep 1799587 = 2699381) B2699381
theorem B3036595 : Blo 1798100 3036595 := bstep (se 1 (by rfl) ⟨2277446, by rfl⟩ : syracuseStep 3036595 = 4554893) B4554893
theorem B1799603 : Blo 1798100 1799603 := bstep (se 1 (by rfl) ⟨1349702, by rfl⟩ : syracuseStep 1799603 = 2699405) B2699405
theorem B2561473 : Blo 1798100 2561473 := bstep (se 2 (by rfl) ⟨960552, by rfl⟩ : syracuseStep 2561473 = 1921105) B1921105
theorem B1799619 : Blo 1798100 1799619 := bstep (se 1 (by rfl) ⟨1349714, by rfl⟩ : syracuseStep 1799619 = 2699429) B2699429
theorem B1799635 : Blo 1798100 1799635 := bstep (se 1 (by rfl) ⟨1349726, by rfl⟩ : syracuseStep 1799635 = 2699453) B2699453
theorem B1799651 : Blo 1798100 1799651 := bstep (se 1 (by rfl) ⟨1349738, by rfl⟩ : syracuseStep 1799651 = 2699477) B2699477
theorem B5469677 : Blo 1798100 5469677 := bstep (se 3 (by rfl) ⟨1025564, by rfl⟩ : syracuseStep 5469677 = 2051129) B2051129
theorem B1799667 : Blo 1798100 1799667 := bstep (se 1 (by rfl) ⟨1349750, by rfl⟩ : syracuseStep 1799667 = 2699501) B2699501
theorem B1799683 : Blo 1798100 1799683 := bstep (se 1 (by rfl) ⟨1349762, by rfl⟩ : syracuseStep 1799683 = 2699525) B2699525
theorem B1799699 : Blo 1798100 1799699 := bstep (se 1 (by rfl) ⟨1349774, by rfl⟩ : syracuseStep 1799699 = 2699549) B2699549
theorem B1799715 : Blo 1798100 1799715 := bstep (se 1 (by rfl) ⟨1349786, by rfl⟩ : syracuseStep 1799715 = 2699573) B2699573
theorem B1799731 : Blo 1798100 1799731 := bstep (se 1 (by rfl) ⟨1349798, by rfl⟩ : syracuseStep 1799731 = 2699597) B2699597
theorem B3036737 : Blo 1798100 3036737 := bstep (se 2 (by rfl) ⟨1138776, by rfl⟩ : syracuseStep 3036737 = 2277553) B2277553
theorem B1799747 : Blo 1798100 1799747 := bstep (se 1 (by rfl) ⟨1349810, by rfl⟩ : syracuseStep 1799747 = 2699621) B2699621
theorem B1799763 : Blo 1798100 1799763 := bstep (se 1 (by rfl) ⟨1349822, by rfl⟩ : syracuseStep 1799763 = 2699645) B2699645
theorem B3413603 : Blo 1798100 3413603 := bstep (se 1 (by rfl) ⟨2560202, by rfl⟩ : syracuseStep 3413603 = 5120405) B5120405
theorem B6829667 : Blo 1798100 6829667 := bstep (se 1 (by rfl) ⟨5122250, by rfl⟩ : syracuseStep 6829667 = 10244501) B10244501
theorem B1799779 : Blo 1798100 1799779 := bstep (se 1 (by rfl) ⟨1349834, by rfl⟩ : syracuseStep 1799779 = 2699669) B2699669
theorem B6485617 : Blo 1798100 6485617 := bstep (se 2 (by rfl) ⟨2432106, by rfl⟩ : syracuseStep 6485617 = 4864213) B4864213
theorem B1799795 : Blo 1798100 1799795 := bstep (se 1 (by rfl) ⟨1349846, by rfl⟩ : syracuseStep 1799795 = 2699693) B2699693
theorem B1799811 : Blo 1798100 1799811 := bstep (se 1 (by rfl) ⟨1349858, by rfl⟩ : syracuseStep 1799811 = 2699717) B2699717
theorem B1799827 : Blo 1798100 1799827 := bstep (se 1 (by rfl) ⟨1349870, by rfl⟩ : syracuseStep 1799827 = 2699741) B2699741
theorem B1799843 : Blo 1798100 1799843 := bstep (se 1 (by rfl) ⟨1349882, by rfl⟩ : syracuseStep 1799843 = 2699765) B2699765
theorem B5125805 : Blo 1798100 5125805 := bstep (se 3 (by rfl) ⟨961088, by rfl⟩ : syracuseStep 5125805 = 1922177) B1922177
theorem B1799859 : Blo 1798100 1799859 := bstep (se 1 (by rfl) ⟨1349894, by rfl⟩ : syracuseStep 1799859 = 2699789) B2699789
theorem B3036865 : Blo 1798100 3036865 := bstep (se 2 (by rfl) ⟨1138824, by rfl⟩ : syracuseStep 3036865 = 2277649) B2277649
theorem B1799875 : Blo 1798100 1799875 := bstep (se 1 (by rfl) ⟨1349906, by rfl⟩ : syracuseStep 1799875 = 2699813) B2699813
theorem B9721549 : Blo 1798100 9721549 := bstep (se 3 (by rfl) ⟨1822790, by rfl⟩ : syracuseStep 9721549 = 3645581) B3645581
theorem B1799891 : Blo 1798100 1799891 := bstep (se 1 (by rfl) ⟨1349918, by rfl⟩ : syracuseStep 1799891 = 2699837) B2699837
theorem B2307811 : Blo 1798100 2307811 := bstep (se 1 (by rfl) ⟨1730858, by rfl⟩ : syracuseStep 2307811 = 3461717) B3461717
theorem B3036899 : Blo 1798100 3036899 := bstep (se 1 (by rfl) ⟨2277674, by rfl⟩ : syracuseStep 3036899 = 4555349) B4555349
theorem B1799907 : Blo 1798100 1799907 := bstep (se 1 (by rfl) ⟨1349930, by rfl⟩ : syracuseStep 1799907 = 2699861) B2699861
theorem B4994797 : Blo 1798100 4994797 := bstep (se 3 (by rfl) ⟨936524, by rfl⟩ : syracuseStep 4994797 = 1873049) B1873049
theorem B4552433 : Blo 1798100 4552433 := bstep (se 2 (by rfl) ⟨1707162, by rfl⟩ : syracuseStep 4552433 = 3414325) B3414325
theorem B1799923 : Blo 1798100 1799923 := bstep (se 1 (by rfl) ⟨1349942, by rfl⟩ : syracuseStep 1799923 = 2699885) B2699885
theorem B1799939 : Blo 1798100 1799939 := bstep (se 1 (by rfl) ⟨1349954, by rfl⟩ : syracuseStep 1799939 = 2699909) B2699909
theorem B2561809 : Blo 1798100 2561809 := bstep (se 2 (by rfl) ⟨960678, by rfl⟩ : syracuseStep 2561809 = 1921357) B1921357
theorem B1799955 : Blo 1798100 1799955 := bstep (se 1 (by rfl) ⟨1349966, by rfl⟩ : syracuseStep 1799955 = 2699933) B2699933
theorem B4552483 : Blo 1798100 4552483 := bstep (se 1 (by rfl) ⟨3414362, by rfl⟩ : syracuseStep 4552483 = 6828725) B6828725
theorem B1799971 : Blo 1798100 1799971 := bstep (se 1 (by rfl) ⟨1349978, by rfl⟩ : syracuseStep 1799971 = 2699957) B2699957
theorem B1799987 : Blo 1798100 1799987 := bstep (se 1 (by rfl) ⟨1349990, by rfl⟩ : syracuseStep 1799987 = 2699981) B2699981
theorem B1800003 : Blo 1798100 1800003 := bstep (se 1 (by rfl) ⟨1350002, by rfl⟩ : syracuseStep 1800003 = 2700005) B2700005
theorem B1800019 : Blo 1798100 1800019 := bstep (se 1 (by rfl) ⟨1350014, by rfl⟩ : syracuseStep 1800019 = 2700029) B2700029
theorem B3037027 : Blo 1798100 3037027 := bstep (se 1 (by rfl) ⟨2277770, by rfl⟩ : syracuseStep 3037027 = 4555541) B4555541
theorem B1800035 : Blo 1798100 1800035 := bstep (se 1 (by rfl) ⟨1350026, by rfl⟩ : syracuseStep 1800035 = 2700053) B2700053
theorem B1800051 : Blo 1798100 1800051 := bstep (se 1 (by rfl) ⟨1350038, by rfl⟩ : syracuseStep 1800051 = 2700077) B2700077
theorem B1800067 : Blo 1798100 1800067 := bstep (se 1 (by rfl) ⟨1350050, by rfl⟩ : syracuseStep 1800067 = 2700101) B2700101
theorem B1800083 : Blo 1798100 1800083 := bstep (se 1 (by rfl) ⟨1350062, by rfl⟩ : syracuseStep 1800083 = 2700125) B2700125
theorem B1800099 : Blo 1798100 1800099 := bstep (se 1 (by rfl) ⟨1350074, by rfl⟩ : syracuseStep 1800099 = 2700149) B2700149
theorem B4552625 : Blo 1798100 4552625 := bstep (se 2 (by rfl) ⟨1707234, by rfl⟩ : syracuseStep 4552625 = 3414469) B3414469
theorem B5765069 : Blo 1798100 5765069 := bstep (se 3 (by rfl) ⟨1080950, by rfl⟩ : syracuseStep 5765069 = 2161901) B2161901
theorem B4741073 : Blo 1798100 4741073 := bstep (se 2 (by rfl) ⟨1777902, by rfl⟩ : syracuseStep 4741073 = 3555805) B3555805
theorem B3037169 : Blo 1798100 3037169 := bstep (se 2 (by rfl) ⟨1138938, by rfl⟩ : syracuseStep 3037169 = 2277877) B2277877
theorem B11532293 : Blo 1798100 11532293 := bstep (se 4 (by rfl) ⟨1081152, by rfl⟩ : syracuseStep 11532293 = 2162305) B2162305
theorem B7682147 : Blo 1798100 7682147 := bstep (se 1 (by rfl) ⟨5761610, by rfl⟩ : syracuseStep 7682147 = 11523221) B11523221
theorem B3037297 : Blo 1798100 3037297 := bstep (se 2 (by rfl) ⟨1138986, by rfl⟩ : syracuseStep 3037297 = 2277973) B2277973
theorem B10246277 : Blo 1798100 10246277 := bstep (se 4 (by rfl) ⟨960588, by rfl⟩ : syracuseStep 10246277 = 1921177) B1921177
theorem B3037331 : Blo 1798100 3037331 := bstep (se 1 (by rfl) ⟨2277998, by rfl⟩ : syracuseStep 3037331 = 4555997) B4555997
theorem B2431139 : Blo 1798100 2431139 := bstep (se 1 (by rfl) ⟨1823354, by rfl⟩ : syracuseStep 2431139 = 3646709) B3646709
theorem B3037459 : Blo 1798100 3037459 := bstep (se 1 (by rfl) ⟨2278094, by rfl⟩ : syracuseStep 3037459 = 4556189) B4556189
theorem B2562401 : Blo 1798100 2562401 := bstep (se 2 (by rfl) ⟨960900, by rfl⟩ : syracuseStep 2562401 = 1921801) B1921801
theorem B2161027 : Blo 1798100 2161027 := bstep (se 1 (by rfl) ⟨1620770, by rfl⟩ : syracuseStep 2161027 = 3241541) B3241541
theorem B3037601 : Blo 1798100 3037601 := bstep (se 2 (by rfl) ⟨1139100, by rfl⟩ : syracuseStep 3037601 = 2278201) B2278201
theorem B2161075 : Blo 1798100 2161075 := bstep (se 1 (by rfl) ⟨1620806, by rfl⟩ : syracuseStep 2161075 = 3241613) B3241613
theorem B16407011 : Blo 1798100 16407011 := bstep (se 1 (by rfl) ⟨12305258, by rfl⟩ : syracuseStep 16407011 = 24610517) B24610517
theorem B17291789 : Blo 1798100 17291789 := bstep (se 3 (by rfl) ⟨3242210, by rfl⟩ : syracuseStep 17291789 = 6484421) B6484421
theorem B3414545 : Blo 1798100 3414545 := bstep (se 2 (by rfl) ⟨1280454, by rfl⟩ : syracuseStep 3414545 = 2560909) B2560909
theorem B2161171 : Blo 1798100 2161171 := bstep (se 1 (by rfl) ⟨1620878, by rfl⟩ : syracuseStep 2161171 = 3241757) B3241757
theorem B2882099 : Blo 1798100 2882099 := bstep (se 1 (by rfl) ⟨2161574, by rfl⟩ : syracuseStep 2882099 = 4323149) B4323149
theorem B6830669 : Blo 1798100 6830669 := bstep (se 3 (by rfl) ⟨1280750, by rfl⟩ : syracuseStep 6830669 = 2561501) B2561501
theorem B10246733 : Blo 1798100 10246733 := bstep (se 3 (by rfl) ⟨1921262, by rfl⟩ : syracuseStep 10246733 = 3842525) B3842525
theorem B14039651 : Blo 1798100 14039651 := bstep (se 1 (by rfl) ⟨10529738, by rfl⟩ : syracuseStep 14039651 = 21059477) B21059477
theorem B8641187 : Blo 1798100 8641187 := bstep (se 1 (by rfl) ⟨6480890, by rfl⟩ : syracuseStep 8641187 = 12961781) B12961781
theorem B2882227 : Blo 1798100 2882227 := bstep (se 1 (by rfl) ⟨2161670, by rfl⟩ : syracuseStep 2882227 = 4323341) B4323341
theorem B13662917 : Blo 1798100 13662917 := bstep (se 4 (by rfl) ⟨1280898, by rfl⟩ : syracuseStep 13662917 = 2561797) B2561797
theorem B6069005 : Blo 1798100 6069005 := bstep (se 3 (by rfl) ⟨1137938, by rfl⟩ : syracuseStep 6069005 = 2275877) B2275877
theorem B2595619 : Blo 1798100 2595619 := bstep (se 1 (by rfl) ⟨1946714, by rfl⟩ : syracuseStep 2595619 = 3893429) B3893429
theorem B3840817 : Blo 1798100 3840817 := bstep (se 2 (by rfl) ⟨1440306, by rfl⟩ : syracuseStep 3840817 = 2880613) B2880613
theorem B6069059 : Blo 1798100 6069059 := bstep (se 1 (by rfl) ⟨4551794, by rfl⟩ : syracuseStep 6069059 = 9103589) B9103589
theorem B2562931 : Blo 1798100 2562931 := bstep (se 1 (by rfl) ⟨1922198, by rfl⟩ : syracuseStep 2562931 = 3844397) B3844397
theorem B4553617 : Blo 1798100 4553617 := bstep (se 2 (by rfl) ⟨1707606, by rfl⟩ : syracuseStep 4553617 = 3415213) B3415213
theorem B2595827 : Blo 1798100 2595827 := bstep (se 1 (by rfl) ⟨1946870, by rfl⟩ : syracuseStep 2595827 = 3893741) B3893741
theorem B4045841 : Blo 1798100 4045841 := bstep (se 2 (by rfl) ⟨1517190, by rfl⟩ : syracuseStep 4045841 = 3034381) B3034381
theorem B3243025 : Blo 1798100 3243025 := bstep (se 2 (by rfl) ⟨1216134, by rfl⟩ : syracuseStep 3243025 = 2432269) B2432269
theorem B4045859 : Blo 1798100 4045859 := bstep (se 1 (by rfl) ⟨3034394, by rfl⟩ : syracuseStep 4045859 = 6068789) B6068789
theorem B2276419 : Blo 1798100 2276419 := bstep (se 1 (by rfl) ⟨1707314, by rfl⟩ : syracuseStep 2276419 = 3414629) B3414629
theorem B6069329 : Blo 1798100 6069329 := bstep (se 2 (by rfl) ⟨2275998, by rfl⟩ : syracuseStep 6069329 = 4551997) B4551997
theorem B2161747 : Blo 1798100 2161747 := bstep (se 1 (by rfl) ⟨1621310, by rfl⟩ : syracuseStep 2161747 = 3242621) B3242621
theorem B2276515 : Blo 1798100 2276515 := bstep (se 1 (by rfl) ⟨1707386, by rfl⟩ : syracuseStep 2276515 = 3414773) B3414773
theorem B4553891 : Blo 1798100 4553891 := bstep (se 1 (by rfl) ⟨3415418, by rfl⟩ : syracuseStep 4553891 = 6830837) B6830837
theorem B4930733 : Blo 1798100 4930733 := bstep (se 3 (by rfl) ⟨924512, by rfl⟩ : syracuseStep 4930733 = 1849025) B1849025
theorem B2882785 : Blo 1798100 2882785 := bstep (se 2 (by rfl) ⟨1081044, by rfl⟩ : syracuseStep 2882785 = 2162089) B2162089
theorem B4046129 : Blo 1798100 4046129 := bstep (se 2 (by rfl) ⟨1517298, by rfl⟩ : syracuseStep 4046129 = 3034597) B3034597
theorem B4046147 : Blo 1798100 4046147 := bstep (se 1 (by rfl) ⟨3034610, by rfl⟩ : syracuseStep 4046147 = 6069221) B6069221
theorem B2596195 : Blo 1798100 2596195 := bstep (se 1 (by rfl) ⟨1947146, by rfl⟩ : syracuseStep 2596195 = 3894293) B3894293
theorem B4554083 : Blo 1798100 4554083 := bstep (se 1 (by rfl) ⟨3415562, by rfl⟩ : syracuseStep 4554083 = 6831125) B6831125
theorem B3415441 : Blo 1798100 3415441 := bstep (se 2 (by rfl) ⟨1280790, by rfl⟩ : syracuseStep 3415441 = 2561581) B2561581
theorem B5766659 : Blo 1798100 5766659 := bstep (se 1 (by rfl) ⟨4324994, by rfl⟩ : syracuseStep 5766659 = 8649989) B8649989
theorem B3415601 : Blo 1798100 3415601 := bstep (se 2 (by rfl) ⟨1280850, by rfl⟩ : syracuseStep 3415601 = 2561701) B2561701
theorem B2022979 : Blo 1798100 2022979 := bstep (se 1 (by rfl) ⟨1517234, by rfl⟩ : syracuseStep 2022979 = 3034469) B3034469
theorem B4046417 : Blo 1798100 4046417 := bstep (se 2 (by rfl) ⟨1517406, by rfl⟩ : syracuseStep 4046417 = 3034813) B3034813
theorem B2735713 : Blo 1798100 2735713 := bstep (se 2 (by rfl) ⟨1025892, by rfl⟩ : syracuseStep 2735713 = 2051785) B2051785
theorem B4046435 : Blo 1798100 4046435 := bstep (se 1 (by rfl) ⟨3034826, by rfl⟩ : syracuseStep 4046435 = 6069653) B6069653
theorem B6069869 : Blo 1798100 6069869 := bstep (se 3 (by rfl) ⟨1138100, by rfl⟩ : syracuseStep 6069869 = 2276201) B2276201
theorem B2735731 : Blo 1798100 2735731 := bstep (se 1 (by rfl) ⟨2051798, by rfl⟩ : syracuseStep 2735731 = 4103597) B4103597
theorem B2277011 : Blo 1798100 2277011 := bstep (se 1 (by rfl) ⟨1707758, by rfl⟩ : syracuseStep 2277011 = 3415517) B3415517
theorem B6069923 : Blo 1798100 6069923 := bstep (se 1 (by rfl) ⟨4552442, by rfl⟩ : syracuseStep 6069923 = 9104885) B9104885
theorem B2023123 : Blo 1798100 2023123 := bstep (se 1 (by rfl) ⟨1517342, by rfl⟩ : syracuseStep 2023123 = 3034685) B3034685
theorem B12304163 : Blo 1798100 12304163 := bstep (se 1 (by rfl) ⟨9228122, by rfl⟩ : syracuseStep 12304163 = 18456245) B18456245
theorem B2023267 : Blo 1798100 2023267 := bstep (se 1 (by rfl) ⟨1517450, by rfl⟩ : syracuseStep 2023267 = 3034901) B3034901
theorem B4046705 : Blo 1798100 4046705 := bstep (se 2 (by rfl) ⟨1517514, by rfl⟩ : syracuseStep 4046705 = 3035029) B3035029
theorem B4046723 : Blo 1798100 4046723 := bstep (se 1 (by rfl) ⟨3035042, by rfl⟩ : syracuseStep 4046723 = 6070085) B6070085
theorem B6070193 : Blo 1798100 6070193 := bstep (se 2 (by rfl) ⟨2276322, by rfl⟩ : syracuseStep 6070193 = 4552645) B4552645
theorem B3416003 : Blo 1798100 3416003 := bstep (se 1 (by rfl) ⟨2562002, by rfl⟩ : syracuseStep 3416003 = 5124005) B5124005
theorem B2023411 : Blo 1798100 2023411 := bstep (se 1 (by rfl) ⟨1517558, by rfl⟩ : syracuseStep 2023411 = 3035117) B3035117
theorem B4046849 : Blo 1798100 4046849 := bstep (se 2 (by rfl) ⟨1517568, by rfl⟩ : syracuseStep 4046849 = 3035137) B3035137
theorem B2023447 : Blo 1798100 2023447 := bstep (se 1 (by rfl) ⟨1517585, by rfl⟩ : syracuseStep 2023447 = 3035171) B3035171
theorem B3416087 : Blo 1798100 3416087 := bstep (se 1 (by rfl) ⟨2562065, by rfl⟩ : syracuseStep 3416087 = 5124131) B5124131
theorem B2023627 : Blo 1798100 2023627 := bstep (se 1 (by rfl) ⟨1517720, by rfl⟩ : syracuseStep 2023627 = 3035441) B3035441
theorem B4047065 : Blo 1798100 4047065 := bstep (se 2 (by rfl) ⟨1517649, by rfl⟩ : syracuseStep 4047065 = 3035299) B3035299
theorem B4047155 : Blo 1798100 4047155 := bstep (se 1 (by rfl) ⟨3035366, by rfl⟩ : syracuseStep 4047155 = 6070733) B6070733
theorem B2023735 : Blo 1798100 2023735 := bstep (se 1 (by rfl) ⟨1517801, by rfl⟩ : syracuseStep 2023735 = 3035603) B3035603
theorem B4047191 : Blo 1798100 4047191 := bstep (se 1 (by rfl) ⟨3035393, by rfl⟩ : syracuseStep 4047191 = 6070787) B6070787
theorem B6070679 : Blo 1798100 6070679 := bstep (se 1 (by rfl) ⟨4553009, by rfl⟩ : syracuseStep 6070679 = 9106019) B9106019
theorem B4555187 : Blo 1798100 4555187 := bstep (se 1 (by rfl) ⟨3416390, by rfl⟩ : syracuseStep 4555187 = 6832781) B6832781
theorem B2023915 : Blo 1798100 2023915 := bstep (se 1 (by rfl) ⟨1517936, by rfl⟩ : syracuseStep 2023915 = 3035873) B3035873
theorem B14590469 : Blo 1798100 14590469 := bstep (se 4 (by rfl) ⟨1367856, by rfl⟩ : syracuseStep 14590469 = 2735713) B2735713
theorem B4047371 : Blo 1798100 4047371 := bstep (se 1 (by rfl) ⟨3035528, by rfl⟩ : syracuseStep 4047371 = 6071057) B6071057
theorem B4047425 : Blo 1798100 4047425 := bstep (se 2 (by rfl) ⟨1517784, by rfl⟩ : syracuseStep 4047425 = 3035569) B3035569
theorem B5120587 : Blo 1798100 5120587 := bstep (se 1 (by rfl) ⟨3840440, by rfl⟩ : syracuseStep 5120587 = 7680881) B7680881
theorem B2024023 : Blo 1798100 2024023 := bstep (se 1 (by rfl) ⟨1518017, by rfl⟩ : syracuseStep 2024023 = 3036035) B3036035
theorem B13664861 : Blo 1798100 13664861 := bstep (se 3 (by rfl) ⟨2562161, by rfl⟩ : syracuseStep 13664861 = 5124323) B5124323
theorem B18719383 : Blo 1798100 18719383 := bstep (se 1 (by rfl) ⟨14039537, by rfl⟩ : syracuseStep 18719383 = 28079075) B28079075
theorem B2278039 : Blo 1798100 2278039 := bstep (se 1 (by rfl) ⟨1708529, by rfl⟩ : syracuseStep 2278039 = 3417059) B3417059
theorem B3416755 : Blo 1798100 3416755 := bstep (se 1 (by rfl) ⟨2562566, by rfl⟩ : syracuseStep 3416755 = 5125133) B5125133
theorem B2024203 : Blo 1798100 2024203 := bstep (se 1 (by rfl) ⟨1518152, by rfl⟩ : syracuseStep 2024203 = 3036305) B3036305
theorem B4047641 : Blo 1798100 4047641 := bstep (se 2 (by rfl) ⟨1517865, by rfl⟩ : syracuseStep 4047641 = 3035731) B3035731
theorem B110764853 : Blo 1798100 110764853 := bstep (se 5 (by rfl) ⟨5192102, by rfl⟩ : syracuseStep 110764853 = 10384205) B10384205
theorem B4047731 : Blo 1798100 4047731 := bstep (se 1 (by rfl) ⟨3035798, by rfl⟩ : syracuseStep 4047731 = 6071597) B6071597
theorem B2024311 : Blo 1798100 2024311 := bstep (se 1 (by rfl) ⟨1518233, by rfl⟩ : syracuseStep 2024311 = 3036467) B3036467
theorem B16638851 : Blo 1798100 16638851 := bstep (se 1 (by rfl) ⟨12479138, by rfl⟩ : syracuseStep 16638851 = 24958277) B24958277
theorem B4047767 : Blo 1798100 4047767 := bstep (se 1 (by rfl) ⟨3035825, by rfl⟩ : syracuseStep 4047767 = 6071651) B6071651
theorem B3842969 : Blo 1798100 3842969 := bstep (se 2 (by rfl) ⟨1441113, by rfl⟩ : syracuseStep 3842969 = 2882227) B2882227
theorem B6833069 : Blo 1798100 6833069 := bstep (se 3 (by rfl) ⟨1281200, by rfl⟩ : syracuseStep 6833069 = 2562401) B2562401
theorem B6071219 : Blo 1798100 6071219 := bstep (se 1 (by rfl) ⟨4553414, by rfl⟩ : syracuseStep 6071219 = 9106829) B9106829
theorem B6833099 : Blo 1798100 6833099 := bstep (se 1 (by rfl) ⟨5124824, by rfl⟩ : syracuseStep 6833099 = 10249649) B10249649
theorem B4555723 : Blo 1798100 4555723 := bstep (se 1 (by rfl) ⟨3416792, by rfl⟩ : syracuseStep 4555723 = 6833585) B6833585
theorem B3646451 : Blo 1798100 3646451 := bstep (se 1 (by rfl) ⟨2734838, by rfl⟩ : syracuseStep 3646451 = 5469677) B5469677
theorem B2024491 : Blo 1798100 2024491 := bstep (se 1 (by rfl) ⟨1518368, by rfl⟩ : syracuseStep 2024491 = 3036737) B3036737
theorem B5121089 : Blo 1798100 5121089 := bstep (se 2 (by rfl) ⟨1920408, by rfl⟩ : syracuseStep 5121089 = 3840817) B3840817
theorem B10945601 : Blo 1798100 10945601 := bstep (se 2 (by rfl) ⟨4104600, by rfl⟩ : syracuseStep 10945601 = 8209201) B8209201
theorem B4047947 : Blo 1798100 4047947 := bstep (se 1 (by rfl) ⟨3035960, by rfl⟩ : syracuseStep 4047947 = 6071921) B6071921
theorem B4555865 : Blo 1798100 4555865 := bstep (se 2 (by rfl) ⟨1708449, by rfl⟩ : syracuseStep 4555865 = 3416899) B3416899
theorem B3417203 : Blo 1798100 3417203 := bstep (se 1 (by rfl) ⟨2562902, by rfl⟩ : syracuseStep 3417203 = 5125805) B5125805
theorem B4048001 : Blo 1798100 4048001 := bstep (se 2 (by rfl) ⟨1518000, by rfl⟩ : syracuseStep 4048001 = 3036001) B3036001
theorem B2024599 : Blo 1798100 2024599 := bstep (se 1 (by rfl) ⟨1518449, by rfl⟩ : syracuseStep 2024599 = 3036899) B3036899
theorem B3417241 : Blo 1798100 3417241 := bstep (se 2 (by rfl) ⟨1281465, by rfl⟩ : syracuseStep 3417241 = 2562931) B2562931
theorem B6071489 : Blo 1798100 6071489 := bstep (se 2 (by rfl) ⟨2276808, by rfl⟩ : syracuseStep 6071489 = 4553617) B4553617
theorem B3843379 : Blo 1798100 3843379 := bstep (se 1 (by rfl) ⟨2882534, by rfl⟩ : syracuseStep 3843379 = 5765069) B5765069
theorem B2024779 : Blo 1798100 2024779 := bstep (se 1 (by rfl) ⟨1518584, by rfl⟩ : syracuseStep 2024779 = 3037169) B3037169
theorem B4048217 : Blo 1798100 4048217 := bstep (se 2 (by rfl) ⟨1518081, by rfl⟩ : syracuseStep 4048217 = 3036163) B3036163
theorem B5121431 : Blo 1798100 5121431 := bstep (se 1 (by rfl) ⟨3841073, by rfl⟩ : syracuseStep 5121431 = 7682147) B7682147
theorem B4048307 : Blo 1798100 4048307 := bstep (se 1 (by rfl) ⟨3036230, by rfl⟩ : syracuseStep 4048307 = 6072461) B6072461
theorem B2024887 : Blo 1798100 2024887 := bstep (se 1 (by rfl) ⟨1518665, by rfl⟩ : syracuseStep 2024887 = 3037331) B3037331
theorem B4048343 : Blo 1798100 4048343 := bstep (se 1 (by rfl) ⟨3036257, by rfl⟩ : syracuseStep 4048343 = 6072515) B6072515
theorem B15369689 : Blo 1798100 15369689 := bstep (se 2 (by rfl) ⟨5763633, by rfl⟩ : syracuseStep 15369689 = 11527267) B11527267
theorem B7685597 : Blo 1798100 7685597 := bstep (se 3 (by rfl) ⟨1441049, by rfl⟩ : syracuseStep 7685597 = 2882099) B2882099
theorem B14583361 : Blo 1798100 14583361 := bstep (se 2 (by rfl) ⟨5468760, by rfl⟩ : syracuseStep 14583361 = 10937521) B10937521
theorem B15582785 : Blo 1798100 15582785 := bstep (se 2 (by rfl) ⟨5843544, by rfl⟩ : syracuseStep 15582785 = 11687089) B11687089
theorem B6833753 : Blo 1798100 6833753 := bstep (se 2 (by rfl) ⟨2562657, by rfl⟩ : syracuseStep 6833753 = 5125315) B5125315
theorem B9102941 : Blo 1798100 9102941 := bstep (se 3 (by rfl) ⟨1706801, by rfl⟩ : syracuseStep 9102941 = 3413603) B3413603
theorem B2025067 : Blo 1798100 2025067 := bstep (se 1 (by rfl) ⟨1518800, by rfl⟩ : syracuseStep 2025067 = 3037601) B3037601
theorem B3843713 : Blo 1798100 3843713 := bstep (se 2 (by rfl) ⟨1441392, by rfl⟩ : syracuseStep 3843713 = 2882785) B2882785
theorem B4048523 : Blo 1798100 4048523 := bstep (se 1 (by rfl) ⟨3036392, by rfl⟩ : syracuseStep 4048523 = 6072785) B6072785
theorem B10938007 : Blo 1798100 10938007 := bstep (se 1 (by rfl) ⟨8203505, by rfl⟩ : syracuseStep 10938007 = 16407011) B16407011
theorem B11527859 : Blo 1798100 11527859 := bstep (se 1 (by rfl) ⟨8645894, by rfl⟩ : syracuseStep 11527859 = 17291789) B17291789
theorem B4048577 : Blo 1798100 4048577 := bstep (se 2 (by rfl) ⟨1518216, by rfl⟩ : syracuseStep 4048577 = 3036433) B3036433
theorem B6072029 : Blo 1798100 6072029 := bstep (se 3 (by rfl) ⟨1138505, by rfl⟩ : syracuseStep 6072029 = 2277011) B2277011
theorem B5760791 : Blo 1798100 5760791 := bstep (se 1 (by rfl) ⟨4320593, by rfl⟩ : syracuseStep 5760791 = 8641187) B8641187
theorem B13141835 : Blo 1798100 13141835 := bstep (se 1 (by rfl) ⟨9856376, by rfl⟩ : syracuseStep 13141835 = 19712753) B19712753
theorem B13846373 : Blo 1798100 13846373 := bstep (se 4 (by rfl) ⟨1298097, by rfl⟩ : syracuseStep 13846373 = 2596195) B2596195
theorem B6834071 : Blo 1798100 6834071 := bstep (se 1 (by rfl) ⟨5125553, by rfl⟩ : syracuseStep 6834071 = 10251107) B10251107
theorem B4048793 : Blo 1798100 4048793 := bstep (se 2 (by rfl) ⟨1518297, by rfl⟩ : syracuseStep 4048793 = 3036595) B3036595
theorem B4048883 : Blo 1798100 4048883 := bstep (se 1 (by rfl) ⟨3036662, by rfl⟩ : syracuseStep 4048883 = 6073325) B6073325
theorem B2697227 : Blo 1798100 2697227 := bstep (se 1 (by rfl) ⟨2022920, by rfl⟩ : syracuseStep 2697227 = 4045841) B4045841
theorem B2697239 : Blo 1798100 2697239 := bstep (se 1 (by rfl) ⟨2022929, by rfl⟩ : syracuseStep 2697239 = 4045859) B4045859
theorem B4048919 : Blo 1798100 4048919 := bstep (se 1 (by rfl) ⟨3036689, by rfl⟩ : syracuseStep 4048919 = 6073379) B6073379
theorem B2697305 : Blo 1798100 2697305 := bstep (se 2 (by rfl) ⟨1011489, by rfl⟩ : syracuseStep 2697305 = 2022979) B2022979
theorem B32811101 : Blo 1798100 32811101 := bstep (se 3 (by rfl) ⟨6152081, by rfl⟩ : syracuseStep 32811101 = 12304163) B12304163
theorem B10250333 : Blo 1798100 10250333 := bstep (se 3 (by rfl) ⟨1921937, by rfl⟩ : syracuseStep 10250333 = 3843875) B3843875
theorem B3287155 : Blo 1798100 3287155 := bstep (se 1 (by rfl) ⟨2465366, by rfl⟩ : syracuseStep 3287155 = 4930733) B4930733
theorem B3647641 : Blo 1798100 3647641 := bstep (se 2 (by rfl) ⟨1367865, by rfl⟩ : syracuseStep 3647641 = 2735731) B2735731
theorem B2697419 : Blo 1798100 2697419 := bstep (se 1 (by rfl) ⟨2023064, by rfl⟩ : syracuseStep 2697419 = 4046129) B4046129
theorem B4049099 : Blo 1798100 4049099 := bstep (se 1 (by rfl) ⟨3036824, by rfl⟩ : syracuseStep 4049099 = 6073649) B6073649
theorem B2697431 : Blo 1798100 2697431 := bstep (se 1 (by rfl) ⟨2023073, by rfl⟩ : syracuseStep 2697431 = 4046147) B4046147
theorem B4049153 : Blo 1798100 4049153 := bstep (se 2 (by rfl) ⟨1518432, by rfl⟩ : syracuseStep 4049153 = 3036865) B3036865
theorem B12962065 : Blo 1798100 12962065 := bstep (se 2 (by rfl) ⟨4860774, by rfl⟩ : syracuseStep 12962065 = 9721549) B9721549
theorem B2697497 : Blo 1798100 2697497 := bstep (se 2 (by rfl) ⟨1011561, by rfl⟩ : syracuseStep 2697497 = 2023123) B2023123
theorem B3844439 : Blo 1798100 3844439 := bstep (se 1 (by rfl) ⟨2883329, by rfl⟩ : syracuseStep 3844439 = 5766659) B5766659
theorem B2697611 : Blo 1798100 2697611 := bstep (se 1 (by rfl) ⟨2023208, by rfl⟩ : syracuseStep 2697611 = 4046417) B4046417
theorem B2697623 : Blo 1798100 2697623 := bstep (se 1 (by rfl) ⟨2023217, by rfl⟩ : syracuseStep 2697623 = 4046435) B4046435
theorem B2697689 : Blo 1798100 2697689 := bstep (se 2 (by rfl) ⟨1011633, by rfl⟩ : syracuseStep 2697689 = 2023267) B2023267
theorem B4049369 : Blo 1798100 4049369 := bstep (se 2 (by rfl) ⟨1518513, by rfl⟩ : syracuseStep 4049369 = 3037027) B3037027
theorem B4049459 : Blo 1798100 4049459 := bstep (se 1 (by rfl) ⟨3037094, by rfl⟩ : syracuseStep 4049459 = 6074189) B6074189
theorem B6834739 : Blo 1798100 6834739 := bstep (se 1 (by rfl) ⟨5126054, by rfl⟩ : syracuseStep 6834739 = 10252109) B10252109
theorem B2697803 : Blo 1798100 2697803 := bstep (se 1 (by rfl) ⟨2023352, by rfl⟩ : syracuseStep 2697803 = 4046705) B4046705
theorem B2697815 : Blo 1798100 2697815 := bstep (se 1 (by rfl) ⟨2023361, by rfl⟩ : syracuseStep 2697815 = 4046723) B4046723
theorem B4049495 : Blo 1798100 4049495 := bstep (se 1 (by rfl) ⟨3037121, by rfl⟩ : syracuseStep 4049495 = 6074243) B6074243
theorem B2697881 : Blo 1798100 2697881 := bstep (se 2 (by rfl) ⟨1011705, by rfl⟩ : syracuseStep 2697881 = 2023411) B2023411
theorem B2697995 : Blo 1798100 2697995 := bstep (se 1 (by rfl) ⟨2023496, by rfl⟩ : syracuseStep 2697995 = 4046993) B4046993
theorem B4049675 : Blo 1798100 4049675 := bstep (se 1 (by rfl) ⟨3037256, by rfl⟩ : syracuseStep 4049675 = 6074513) B6074513
theorem B9112337 : Blo 1798100 9112337 := bstep (se 2 (by rfl) ⟨3417126, by rfl⟩ : syracuseStep 9112337 = 6834253) B6834253
theorem B2698007 : Blo 1798100 2698007 := bstep (se 1 (by rfl) ⟨2023505, by rfl⟩ : syracuseStep 2698007 = 4047011) B4047011
theorem B4049729 : Blo 1798100 4049729 := bstep (se 2 (by rfl) ⟨1518648, by rfl⟩ : syracuseStep 4049729 = 3037297) B3037297
theorem B6073163 : Blo 1798100 6073163 := bstep (se 1 (by rfl) ⟨4554872, by rfl⟩ : syracuseStep 6073163 = 9109745) B9109745
theorem B2698073 : Blo 1798100 2698073 := bstep (se 2 (by rfl) ⟨1011777, by rfl⟩ : syracuseStep 2698073 = 2023555) B2023555
theorem B9112499 : Blo 1798100 9112499 := bstep (se 1 (by rfl) ⟨6834374, by rfl⟩ : syracuseStep 9112499 = 13668749) B13668749
theorem B2698187 : Blo 1798100 2698187 := bstep (se 1 (by rfl) ⟨2023640, by rfl⟩ : syracuseStep 2698187 = 4047281) B4047281
theorem B2698199 : Blo 1798100 2698199 := bstep (se 1 (by rfl) ⟨2023649, by rfl⟩ : syracuseStep 2698199 = 4047299) B4047299
theorem B5843933 : Blo 1798100 5843933 := bstep (se 3 (by rfl) ⟨1095737, by rfl⟩ : syracuseStep 5843933 = 2191475) B2191475
theorem B2698265 : Blo 1798100 2698265 := bstep (se 2 (by rfl) ⟨1011849, by rfl⟩ : syracuseStep 2698265 = 2023699) B2023699
theorem B4049945 : Blo 1798100 4049945 := bstep (se 2 (by rfl) ⟨1518729, by rfl⟩ : syracuseStep 4049945 = 3037459) B3037459
theorem B15371329 : Blo 1798100 15371329 := bstep (se 2 (by rfl) ⟨5764248, by rfl⟩ : syracuseStep 15371329 = 11528497) B11528497
theorem B5762123 : Blo 1798100 5762123 := bstep (se 1 (by rfl) ⟨4321592, by rfl⟩ : syracuseStep 5762123 = 8643185) B8643185
theorem B6073433 : Blo 1798100 6073433 := bstep (se 2 (by rfl) ⟨2277537, by rfl⟩ : syracuseStep 6073433 = 4555075) B4555075
theorem B11529317 : Blo 1798100 11529317 := bstep (se 4 (by rfl) ⟨1080873, by rfl⟩ : syracuseStep 11529317 = 2161747) B2161747
theorem B4050035 : Blo 1798100 4050035 := bstep (se 1 (by rfl) ⟨3037526, by rfl⟩ : syracuseStep 4050035 = 6075053) B6075053
theorem B2698379 : Blo 1798100 2698379 := bstep (se 1 (by rfl) ⟨2023784, by rfl⟩ : syracuseStep 2698379 = 4047569) B4047569
theorem B4861079 : Blo 1798100 4861079 := bstep (se 1 (by rfl) ⟨3645809, by rfl⟩ : syracuseStep 4861079 = 7291619) B7291619
theorem B2698391 : Blo 1798100 2698391 := bstep (se 1 (by rfl) ⟨2023793, by rfl⟩ : syracuseStep 2698391 = 4047587) B4047587
theorem B4050071 : Blo 1798100 4050071 := bstep (se 1 (by rfl) ⟨3037553, by rfl⟩ : syracuseStep 4050071 = 6075107) B6075107
theorem B3034327 : Blo 1798100 3034327 := bstep (se 1 (by rfl) ⟨2275745, by rfl⟩ : syracuseStep 3034327 = 4551491) B4551491
theorem B3648727 : Blo 1798100 3648727 := bstep (se 1 (by rfl) ⟨2736545, by rfl⟩ : syracuseStep 3648727 = 5473091) B5473091
theorem B2698457 : Blo 1798100 2698457 := bstep (se 2 (by rfl) ⟨1011921, by rfl⟩ : syracuseStep 2698457 = 2023843) B2023843
theorem B29175025 : Blo 1798100 29175025 := bstep (se 2 (by rfl) ⟨10940634, by rfl⟩ : syracuseStep 29175025 = 21881269) B21881269
theorem B6827267 : Blo 1798100 6827267 := bstep (se 1 (by rfl) ⟨5120450, by rfl⟩ : syracuseStep 6827267 = 10240901) B10240901
theorem B19721477 : Blo 1798100 19721477 := bstep (se 4 (by rfl) ⟨1848888, by rfl⟩ : syracuseStep 19721477 = 3697777) B3697777
theorem B4320535 : Blo 1798100 4320535 := bstep (se 1 (by rfl) ⟨3240401, by rfl⟩ : syracuseStep 4320535 = 6480803) B6480803
theorem B6925591 : Blo 1798100 6925591 := bstep (se 1 (by rfl) ⟨5194193, by rfl⟩ : syracuseStep 6925591 = 10388387) B10388387
theorem B2698571 : Blo 1798100 2698571 := bstep (se 1 (by rfl) ⟨2023928, by rfl⟩ : syracuseStep 2698571 = 4047857) B4047857
theorem B2698583 : Blo 1798100 2698583 := bstep (se 1 (by rfl) ⟨2023937, by rfl⟩ : syracuseStep 2698583 = 4047875) B4047875
theorem B2698649 : Blo 1798100 2698649 := bstep (se 2 (by rfl) ⟨1011993, by rfl⟩ : syracuseStep 2698649 = 2023987) B2023987
theorem B19451315 : Blo 1798100 19451315 := bstep (se 1 (by rfl) ⟨14588486, by rfl⟩ : syracuseStep 19451315 = 29176973) B29176973
theorem B5123549 : Blo 1798100 5123549 := bstep (se 3 (by rfl) ⟨960665, by rfl⟩ : syracuseStep 5123549 = 1921331) B1921331
theorem B2698763 : Blo 1798100 2698763 := bstep (se 1 (by rfl) ⟨2024072, by rfl⟩ : syracuseStep 2698763 = 4048145) B4048145
theorem B49262093 : Blo 1798100 49262093 := bstep (se 3 (by rfl) ⟨9236642, by rfl⟩ : syracuseStep 49262093 = 18473285) B18473285
theorem B2698775 : Blo 1798100 2698775 := bstep (se 1 (by rfl) ⟨2024081, by rfl⟩ : syracuseStep 2698775 = 4048163) B4048163
theorem B2698841 : Blo 1798100 2698841 := bstep (se 2 (by rfl) ⟨1012065, by rfl⟩ : syracuseStep 2698841 = 2024131) B2024131
theorem B14585437 : Blo 1798100 14585437 := bstep (se 3 (by rfl) ⟨2734769, by rfl⟩ : syracuseStep 14585437 = 5469539) B5469539
theorem B27684503 : Blo 1798100 27684503 := bstep (se 1 (by rfl) ⟨20763377, by rfl⟩ : syracuseStep 27684503 = 41526755) B41526755
theorem B9105047 : Blo 1798100 9105047 := bstep (se 1 (by rfl) ⟨6828785, by rfl⟩ : syracuseStep 9105047 = 13657571) B13657571
theorem B5762711 : Blo 1798100 5762711 := bstep (se 1 (by rfl) ⟨4322033, by rfl⟩ : syracuseStep 5762711 = 8644067) B8644067
theorem B6827723 : Blo 1798100 6827723 := bstep (se 1 (by rfl) ⟨5120792, by rfl⟩ : syracuseStep 6827723 = 10241585) B10241585
theorem B2698955 : Blo 1798100 2698955 := bstep (se 1 (by rfl) ⟨2024216, by rfl⟩ : syracuseStep 2698955 = 4048433) B4048433
theorem B2698967 : Blo 1798100 2698967 := bstep (se 1 (by rfl) ⟨2024225, by rfl⟩ : syracuseStep 2698967 = 4048451) B4048451
theorem B3460825 : Blo 1798100 3460825 := bstep (se 2 (by rfl) ⟨1297809, by rfl⟩ : syracuseStep 3460825 = 2595619) B2595619
theorem B6074135 : Blo 1798100 6074135 := bstep (se 1 (by rfl) ⟨4555601, by rfl⟩ : syracuseStep 6074135 = 9111203) B9111203
theorem B2699033 : Blo 1798100 2699033 := bstep (se 2 (by rfl) ⟨1012137, by rfl⟩ : syracuseStep 2699033 = 2024275) B2024275
theorem B5123891 : Blo 1798100 5123891 := bstep (se 1 (by rfl) ⟨3842918, by rfl⟩ : syracuseStep 5123891 = 7685837) B7685837
theorem B3034955 : Blo 1798100 3034955 := bstep (se 1 (by rfl) ⟨2276216, by rfl⟩ : syracuseStep 3034955 = 4552433) B4552433
theorem B2699147 : Blo 1798100 2699147 := bstep (se 1 (by rfl) ⟨2024360, by rfl⟩ : syracuseStep 2699147 = 4048721) B4048721
theorem B6827921 : Blo 1798100 6827921 := bstep (se 2 (by rfl) ⟨2560470, by rfl⟩ : syracuseStep 6827921 = 5120941) B5120941
theorem B2699159 : Blo 1798100 2699159 := bstep (se 1 (by rfl) ⟨2024369, by rfl⟩ : syracuseStep 2699159 = 4048739) B4048739
theorem B3035083 : Blo 1798100 3035083 := bstep (se 1 (by rfl) ⟨2276312, by rfl⟩ : syracuseStep 3035083 = 4552625) B4552625
theorem B1798103 : Blo 1798100 1798103 := bstep (se 1 (by rfl) ⟨1348577, by rfl⟩ : syracuseStep 1798103 = 2697155) B2697155
theorem B2699225 : Blo 1798100 2699225 := bstep (se 2 (by rfl) ⟨1012209, by rfl⟩ : syracuseStep 2699225 = 2024419) B2024419
theorem B1798123 : Blo 1798100 1798123 := bstep (se 1 (by rfl) ⟨1348592, by rfl⟩ : syracuseStep 1798123 = 2697185) B2697185
theorem B1798135 : Blo 1798100 1798135 := bstep (se 1 (by rfl) ⟨1348601, by rfl⟩ : syracuseStep 1798135 = 2697203) B2697203
theorem B7688195 : Blo 1798100 7688195 := bstep (se 1 (by rfl) ⟨5766146, by rfl⟩ : syracuseStep 7688195 = 11532293) B11532293
theorem B1798155 : Blo 1798100 1798155 := bstep (se 1 (by rfl) ⟨1348616, by rfl⟩ : syracuseStep 1798155 = 2697233) B2697233
theorem B9236497 : Blo 1798100 9236497 := bstep (se 2 (by rfl) ⟨3463686, by rfl⟩ : syracuseStep 9236497 = 6927373) B6927373
theorem B1798167 : Blo 1798100 1798167 := bstep (se 1 (by rfl) ⟨1348625, by rfl⟩ : syracuseStep 1798167 = 2697251) B2697251
theorem B1798187 : Blo 1798100 1798187 := bstep (se 1 (by rfl) ⟨1348640, by rfl⟩ : syracuseStep 1798187 = 2697281) B2697281
theorem B1798199 : Blo 1798100 1798199 := bstep (se 1 (by rfl) ⟨1348649, by rfl⟩ : syracuseStep 1798199 = 2697299) B2697299
theorem B1798219 : Blo 1798100 1798219 := bstep (se 1 (by rfl) ⟨1348664, by rfl⟩ : syracuseStep 1798219 = 2697329) B2697329
theorem B2699339 : Blo 1798100 2699339 := bstep (se 1 (by rfl) ⟨2024504, by rfl⟩ : syracuseStep 2699339 = 4049009) B4049009
theorem B23375947 : Blo 1798100 23375947 := bstep (se 1 (by rfl) ⟨17531960, by rfl⟩ : syracuseStep 23375947 = 35063921) B35063921
theorem B1798231 : Blo 1798100 1798231 := bstep (se 1 (by rfl) ⟨1348673, by rfl⟩ : syracuseStep 1798231 = 2697347) B2697347
theorem B2699351 : Blo 1798100 2699351 := bstep (se 1 (by rfl) ⟨2024513, by rfl⟩ : syracuseStep 2699351 = 4049027) B4049027
theorem B3035225 : Blo 1798100 3035225 := bstep (se 2 (by rfl) ⟨1138209, by rfl⟩ : syracuseStep 3035225 = 2276419) B2276419
theorem B1798251 : Blo 1798100 1798251 := bstep (se 1 (by rfl) ⟨1348688, by rfl⟩ : syracuseStep 1798251 = 2697377) B2697377
theorem B1798263 : Blo 1798100 1798263 := bstep (se 1 (by rfl) ⟨1348697, by rfl⟩ : syracuseStep 1798263 = 2697395) B2697395
theorem B1798283 : Blo 1798100 1798283 := bstep (se 1 (by rfl) ⟨1348712, by rfl⟩ : syracuseStep 1798283 = 2697425) B2697425
theorem B1798295 : Blo 1798100 1798295 := bstep (se 1 (by rfl) ⟨1348721, by rfl⟩ : syracuseStep 1798295 = 2697443) B2697443
theorem B2699417 : Blo 1798100 2699417 := bstep (se 2 (by rfl) ⟨1012281, by rfl⟩ : syracuseStep 2699417 = 2024563) B2024563
theorem B1798315 : Blo 1798100 1798315 := bstep (se 1 (by rfl) ⟨1348736, by rfl⟩ : syracuseStep 1798315 = 2697473) B2697473
theorem B5763251 : Blo 1798100 5763251 := bstep (se 1 (by rfl) ⟨4322438, by rfl⟩ : syracuseStep 5763251 = 8644877) B8644877
theorem B1798327 : Blo 1798100 1798327 := bstep (se 1 (by rfl) ⟨1348745, by rfl⟩ : syracuseStep 1798327 = 2697491) B2697491
theorem B3895489 : Blo 1798100 3895489 := bstep (se 2 (by rfl) ⟨1460808, by rfl⟩ : syracuseStep 3895489 = 2921617) B2921617
theorem B1798347 : Blo 1798100 1798347 := bstep (se 1 (by rfl) ⟨1348760, by rfl⟩ : syracuseStep 1798347 = 2697521) B2697521
theorem B1798359 : Blo 1798100 1798359 := bstep (se 1 (by rfl) ⟨1348769, by rfl⟩ : syracuseStep 1798359 = 2697539) B2697539
theorem B3035353 : Blo 1798100 3035353 := bstep (se 2 (by rfl) ⟨1138257, by rfl⟩ : syracuseStep 3035353 = 2276515) B2276515
theorem B1798379 : Blo 1798100 1798379 := bstep (se 1 (by rfl) ⟨1348784, by rfl⟩ : syracuseStep 1798379 = 2697569) B2697569
theorem B1798391 : Blo 1798100 1798391 := bstep (se 1 (by rfl) ⟨1348793, by rfl⟩ : syracuseStep 1798391 = 2697587) B2697587
theorem B1798411 : Blo 1798100 1798411 := bstep (se 1 (by rfl) ⟨1348808, by rfl⟩ : syracuseStep 1798411 = 2697617) B2697617
theorem B2699531 : Blo 1798100 2699531 := bstep (se 1 (by rfl) ⟨2024648, by rfl⟩ : syracuseStep 2699531 = 4049297) B4049297
theorem B1798423 : Blo 1798100 1798423 := bstep (se 1 (by rfl) ⟨1348817, by rfl⟩ : syracuseStep 1798423 = 2697635) B2697635
theorem B2699543 : Blo 1798100 2699543 := bstep (se 1 (by rfl) ⟨2024657, by rfl⟩ : syracuseStep 2699543 = 4049315) B4049315
theorem B1798443 : Blo 1798100 1798443 := bstep (se 1 (by rfl) ⟨1348832, by rfl⟩ : syracuseStep 1798443 = 2697665) B2697665
theorem B6074675 : Blo 1798100 6074675 := bstep (se 1 (by rfl) ⟨4556006, by rfl⟩ : syracuseStep 6074675 = 9112013) B9112013
theorem B1798455 : Blo 1798100 1798455 := bstep (se 1 (by rfl) ⟨1348841, by rfl⟩ : syracuseStep 1798455 = 2697683) B2697683
theorem B1798475 : Blo 1798100 1798475 := bstep (se 1 (by rfl) ⟨1348856, by rfl⟩ : syracuseStep 1798475 = 2697713) B2697713
theorem B1798487 : Blo 1798100 1798487 := bstep (se 1 (by rfl) ⟨1348865, by rfl⟩ : syracuseStep 1798487 = 2697731) B2697731
theorem B2699609 : Blo 1798100 2699609 := bstep (se 2 (by rfl) ⟨1012353, by rfl⟩ : syracuseStep 2699609 = 2024707) B2024707
theorem B1798507 : Blo 1798100 1798507 := bstep (se 1 (by rfl) ⟨1348880, by rfl⟩ : syracuseStep 1798507 = 2697761) B2697761
theorem B25932149 : Blo 1798100 25932149 := bstep (se 5 (by rfl) ⟨1215569, by rfl⟩ : syracuseStep 25932149 = 2431139) B2431139
theorem B1798519 : Blo 1798100 1798519 := bstep (se 1 (by rfl) ⟨1348889, by rfl⟩ : syracuseStep 1798519 = 2697779) B2697779
theorem B1798539 : Blo 1798100 1798539 := bstep (se 1 (by rfl) ⟨1348904, by rfl⟩ : syracuseStep 1798539 = 2697809) B2697809
theorem B1798551 : Blo 1798100 1798551 := bstep (se 1 (by rfl) ⟨1348913, by rfl⟩ : syracuseStep 1798551 = 2697827) B2697827
theorem B9359767 : Blo 1798100 9359767 := bstep (se 1 (by rfl) ⟨7019825, by rfl⟩ : syracuseStep 9359767 = 14039651) B14039651
theorem B1798571 : Blo 1798100 1798571 := bstep (se 1 (by rfl) ⟨1348928, by rfl⟩ : syracuseStep 1798571 = 2697857) B2697857
theorem B1798583 : Blo 1798100 1798583 := bstep (se 1 (by rfl) ⟨1348937, by rfl⟩ : syracuseStep 1798583 = 2697875) B2697875
theorem B1798603 : Blo 1798100 1798603 := bstep (se 1 (by rfl) ⟨1348952, by rfl⟩ : syracuseStep 1798603 = 2697905) B2697905
theorem B2699723 : Blo 1798100 2699723 := bstep (se 1 (by rfl) ⟨2024792, by rfl⟩ : syracuseStep 2699723 = 4049585) B4049585
theorem B1798615 : Blo 1798100 1798615 := bstep (se 1 (by rfl) ⟨1348961, by rfl⟩ : syracuseStep 1798615 = 2697923) B2697923
theorem B2699735 : Blo 1798100 2699735 := bstep (se 1 (by rfl) ⟨2024801, by rfl⟩ : syracuseStep 2699735 = 4049603) B4049603
theorem B1798635 : Blo 1798100 1798635 := bstep (se 1 (by rfl) ⟨1348976, by rfl⟩ : syracuseStep 1798635 = 2697953) B2697953
theorem B1798647 : Blo 1798100 1798647 := bstep (se 1 (by rfl) ⟨1348985, by rfl⟩ : syracuseStep 1798647 = 2697971) B2697971
theorem B1798667 : Blo 1798100 1798667 := bstep (se 1 (by rfl) ⟨1349000, by rfl⟩ : syracuseStep 1798667 = 2698001) B2698001
theorem B1798679 : Blo 1798100 1798679 := bstep (se 1 (by rfl) ⟨1349009, by rfl⟩ : syracuseStep 1798679 = 2698019) B2698019
theorem B2699801 : Blo 1798100 2699801 := bstep (se 2 (by rfl) ⟨1012425, by rfl⟩ : syracuseStep 2699801 = 2024851) B2024851
theorem B30749219 : Blo 1798100 30749219 := bstep (se 1 (by rfl) ⟨23061914, by rfl⟩ : syracuseStep 30749219 = 46123829) B46123829
theorem B1798699 : Blo 1798100 1798699 := bstep (se 1 (by rfl) ⟨1349024, by rfl⟩ : syracuseStep 1798699 = 2698049) B2698049
theorem B1798711 : Blo 1798100 1798711 := bstep (se 1 (by rfl) ⟨1349033, by rfl⟩ : syracuseStep 1798711 = 2698067) B2698067
theorem B6074945 : Blo 1798100 6074945 := bstep (se 2 (by rfl) ⟨2278104, by rfl⟩ : syracuseStep 6074945 = 4556209) B4556209
theorem B1798731 : Blo 1798100 1798731 := bstep (se 1 (by rfl) ⟨1349048, by rfl⟩ : syracuseStep 1798731 = 2698097) B2698097
theorem B1798743 : Blo 1798100 1798743 := bstep (se 1 (by rfl) ⟨1349057, by rfl⟩ : syracuseStep 1798743 = 2698115) B2698115
theorem B1798763 : Blo 1798100 1798763 := bstep (se 1 (by rfl) ⟨1349072, by rfl⟩ : syracuseStep 1798763 = 2698145) B2698145
theorem B1798775 : Blo 1798100 1798775 := bstep (se 1 (by rfl) ⟨1349081, by rfl⟩ : syracuseStep 1798775 = 2698163) B2698163
theorem B1798795 : Blo 1798100 1798795 := bstep (se 1 (by rfl) ⟨1349096, by rfl⟩ : syracuseStep 1798795 = 2698193) B2698193
theorem B2699915 : Blo 1798100 2699915 := bstep (se 1 (by rfl) ⟨2024936, by rfl⟩ : syracuseStep 2699915 = 4049873) B4049873
theorem B6828695 : Blo 1798100 6828695 := bstep (se 1 (by rfl) ⟨5121521, by rfl⟩ : syracuseStep 6828695 = 10243043) B10243043
theorem B1798807 : Blo 1798100 1798807 := bstep (se 1 (by rfl) ⟨1349105, by rfl⟩ : syracuseStep 1798807 = 2698211) B2698211
theorem B2699927 : Blo 1798100 2699927 := bstep (se 1 (by rfl) ⟨2024945, by rfl⟩ : syracuseStep 2699927 = 4049891) B4049891
theorem B1798827 : Blo 1798100 1798827 := bstep (se 1 (by rfl) ⟨1349120, by rfl⟩ : syracuseStep 1798827 = 2698241) B2698241
theorem B1798839 : Blo 1798100 1798839 := bstep (se 1 (by rfl) ⟨1349129, by rfl⟩ : syracuseStep 1798839 = 2698259) B2698259
theorem B1798859 : Blo 1798100 1798859 := bstep (se 1 (by rfl) ⟨1349144, by rfl⟩ : syracuseStep 1798859 = 2698289) B2698289
theorem B1798871 : Blo 1798100 1798871 := bstep (se 1 (by rfl) ⟨1349153, by rfl⟩ : syracuseStep 1798871 = 2698307) B2698307
theorem B2699993 : Blo 1798100 2699993 := bstep (se 2 (by rfl) ⟨1012497, by rfl⟩ : syracuseStep 2699993 = 2024995) B2024995
theorem B1798891 : Blo 1798100 1798891 := bstep (se 1 (by rfl) ⟨1349168, by rfl⟩ : syracuseStep 1798891 = 2698337) B2698337
theorem B1798903 : Blo 1798100 1798903 := bstep (se 1 (by rfl) ⟨1349177, by rfl⟩ : syracuseStep 1798903 = 2698355) B2698355
theorem B1798923 : Blo 1798100 1798923 := bstep (se 1 (by rfl) ⟨1349192, by rfl⟩ : syracuseStep 1798923 = 2698385) B2698385
theorem B1798935 : Blo 1798100 1798935 := bstep (se 1 (by rfl) ⟨1349201, by rfl⟩ : syracuseStep 1798935 = 2698403) B2698403
theorem B3035927 : Blo 1798100 3035927 := bstep (se 1 (by rfl) ⟨2276945, by rfl⟩ : syracuseStep 3035927 = 4553891) B4553891
theorem B1798955 : Blo 1798100 1798955 := bstep (se 1 (by rfl) ⟨1349216, by rfl⟩ : syracuseStep 1798955 = 2698433) B2698433
theorem B13660973 : Blo 1798100 13660973 := bstep (se 3 (by rfl) ⟨2561432, by rfl⟩ : syracuseStep 13660973 = 5122865) B5122865
theorem B1798967 : Blo 1798100 1798967 := bstep (se 1 (by rfl) ⟨1349225, by rfl⟩ : syracuseStep 1798967 = 2698451) B2698451
theorem B8647489 : Blo 1798100 8647489 := bstep (se 2 (by rfl) ⟨3242808, by rfl⟩ : syracuseStep 8647489 = 6485617) B6485617
theorem B1798987 : Blo 1798100 1798987 := bstep (se 1 (by rfl) ⟨1349240, by rfl⟩ : syracuseStep 1798987 = 2698481) B2698481
theorem B2700107 : Blo 1798100 2700107 := bstep (se 1 (by rfl) ⟨2025080, by rfl⟩ : syracuseStep 2700107 = 4050161) B4050161
theorem B1798999 : Blo 1798100 1798999 := bstep (se 1 (by rfl) ⟨1349249, by rfl⟩ : syracuseStep 1798999 = 2698499) B2698499
theorem B2700119 : Blo 1798100 2700119 := bstep (se 1 (by rfl) ⟨2025089, by rfl⟩ : syracuseStep 2700119 = 4050179) B4050179
theorem B6828893 : Blo 1798100 6828893 := bstep (se 3 (by rfl) ⟨1280417, by rfl⟩ : syracuseStep 6828893 = 2560835) B2560835
theorem B1799019 : Blo 1798100 1799019 := bstep (se 1 (by rfl) ⟨1349264, by rfl⟩ : syracuseStep 1799019 = 2698529) B2698529
theorem B1799031 : Blo 1798100 1799031 := bstep (se 1 (by rfl) ⟨1349273, by rfl⟩ : syracuseStep 1799031 = 2698547) B2698547
theorem B1799051 : Blo 1798100 1799051 := bstep (se 1 (by rfl) ⟨1349288, by rfl⟩ : syracuseStep 1799051 = 2698577) B2698577
theorem B1799063 : Blo 1798100 1799063 := bstep (se 1 (by rfl) ⟨1349297, by rfl⟩ : syracuseStep 1799063 = 2698595) B2698595
theorem B3036055 : Blo 1798100 3036055 := bstep (se 1 (by rfl) ⟨2277041, by rfl⟩ : syracuseStep 3036055 = 4554083) B4554083
theorem B1799083 : Blo 1798100 1799083 := bstep (se 1 (by rfl) ⟨1349312, by rfl⟩ : syracuseStep 1799083 = 2698625) B2698625
theorem B1799095 : Blo 1798100 1799095 := bstep (se 1 (by rfl) ⟨1349321, by rfl⟩ : syracuseStep 1799095 = 2698643) B2698643
theorem B1799115 : Blo 1798100 1799115 := bstep (se 1 (by rfl) ⟨1349336, by rfl⟩ : syracuseStep 1799115 = 2698673) B2698673
theorem B1799127 : Blo 1798100 1799127 := bstep (se 1 (by rfl) ⟨1349345, by rfl⟩ : syracuseStep 1799127 = 2698691) B2698691
theorem B3077081 : Blo 1798100 3077081 := bstep (se 2 (by rfl) ⟨1153905, by rfl⟩ : syracuseStep 3077081 = 2307811) B2307811
theorem B1799147 : Blo 1798100 1799147 := bstep (se 1 (by rfl) ⟨1349360, by rfl⟩ : syracuseStep 1799147 = 2698721) B2698721
theorem B1799159 : Blo 1798100 1799159 := bstep (se 1 (by rfl) ⟨1349369, by rfl⟩ : syracuseStep 1799159 = 2698739) B2698739
theorem B1799179 : Blo 1798100 1799179 := bstep (se 1 (by rfl) ⟨1349384, by rfl⟩ : syracuseStep 1799179 = 2698769) B2698769
theorem B1799191 : Blo 1798100 1799191 := bstep (se 1 (by rfl) ⟨1349393, by rfl⟩ : syracuseStep 1799191 = 2698787) B2698787
theorem B1799211 : Blo 1798100 1799211 := bstep (se 1 (by rfl) ⟨1349408, by rfl⟩ : syracuseStep 1799211 = 2698817) B2698817
theorem B1799223 : Blo 1798100 1799223 := bstep (se 1 (by rfl) ⟨1349417, by rfl⟩ : syracuseStep 1799223 = 2698835) B2698835
theorem B2880587 : Blo 1798100 2880587 := bstep (se 1 (by rfl) ⟨2160440, by rfl⟩ : syracuseStep 2880587 = 4320881) B4320881
theorem B1799243 : Blo 1798100 1799243 := bstep (se 1 (by rfl) ⟨1349432, by rfl⟩ : syracuseStep 1799243 = 2698865) B2698865
theorem B1799255 : Blo 1798100 1799255 := bstep (se 1 (by rfl) ⟨1349441, by rfl⟩ : syracuseStep 1799255 = 2698883) B2698883
theorem B1799275 : Blo 1798100 1799275 := bstep (se 1 (by rfl) ⟨1349456, by rfl⟩ : syracuseStep 1799275 = 2698913) B2698913
theorem B1799287 : Blo 1798100 1799287 := bstep (se 1 (by rfl) ⟨1349465, by rfl⟩ : syracuseStep 1799287 = 2698931) B2698931
theorem B1799307 : Blo 1798100 1799307 := bstep (se 1 (by rfl) ⟨1349480, by rfl⟩ : syracuseStep 1799307 = 2698961) B2698961
theorem B1799319 : Blo 1798100 1799319 := bstep (se 1 (by rfl) ⟨1349489, by rfl⟩ : syracuseStep 1799319 = 2698979) B2698979
theorem B1799339 : Blo 1798100 1799339 := bstep (se 1 (by rfl) ⟨1349504, by rfl⟩ : syracuseStep 1799339 = 2699009) B2699009
theorem B1799351 : Blo 1798100 1799351 := bstep (se 1 (by rfl) ⟨1349513, by rfl⟩ : syracuseStep 1799351 = 2699027) B2699027
theorem B1799371 : Blo 1798100 1799371 := bstep (se 1 (by rfl) ⟨1349528, by rfl⟩ : syracuseStep 1799371 = 2699057) B2699057
theorem B1799383 : Blo 1798100 1799383 := bstep (se 1 (by rfl) ⟨1349537, by rfl⟩ : syracuseStep 1799383 = 2699075) B2699075
theorem B1799403 : Blo 1798100 1799403 := bstep (se 1 (by rfl) ⟨1349552, by rfl⟩ : syracuseStep 1799403 = 2699105) B2699105
theorem B1799415 : Blo 1798100 1799415 := bstep (se 1 (by rfl) ⟨1349561, by rfl⟩ : syracuseStep 1799415 = 2699123) B2699123
theorem B1799435 : Blo 1798100 1799435 := bstep (se 1 (by rfl) ⟨1349576, by rfl⟩ : syracuseStep 1799435 = 2699153) B2699153
theorem B1799447 : Blo 1798100 1799447 := bstep (se 1 (by rfl) ⟨1349585, by rfl⟩ : syracuseStep 1799447 = 2699171) B2699171
theorem B1799467 : Blo 1798100 1799467 := bstep (se 1 (by rfl) ⟨1349600, by rfl⟩ : syracuseStep 1799467 = 2699201) B2699201
theorem B5469491 : Blo 1798100 5469491 := bstep (se 1 (by rfl) ⟨4102118, by rfl⟩ : syracuseStep 5469491 = 8204237) B8204237
theorem B1799479 : Blo 1798100 1799479 := bstep (se 1 (by rfl) ⟨1349609, by rfl⟩ : syracuseStep 1799479 = 2699219) B2699219
theorem B1799499 : Blo 1798100 1799499 := bstep (se 1 (by rfl) ⟨1349624, by rfl⟩ : syracuseStep 1799499 = 2699249) B2699249
theorem B1799511 : Blo 1798100 1799511 := bstep (se 1 (by rfl) ⟨1349633, by rfl⟩ : syracuseStep 1799511 = 2699267) B2699267
theorem B1799531 : Blo 1798100 1799531 := bstep (se 1 (by rfl) ⟨1349648, by rfl⟩ : syracuseStep 1799531 = 2699297) B2699297
theorem B1799543 : Blo 1798100 1799543 := bstep (se 1 (by rfl) ⟨1349657, by rfl⟩ : syracuseStep 1799543 = 2699315) B2699315
theorem B1799563 : Blo 1798100 1799563 := bstep (se 1 (by rfl) ⟨1349672, by rfl⟩ : syracuseStep 1799563 = 2699345) B2699345
theorem B10245527 : Blo 1798100 10245527 := bstep (se 1 (by rfl) ⟨7684145, by rfl⟩ : syracuseStep 10245527 = 15368291) B15368291
theorem B14423447 : Blo 1798100 14423447 := bstep (se 1 (by rfl) ⟨10817585, by rfl⟩ : syracuseStep 14423447 = 21635171) B21635171
theorem B2430361 : Blo 1798100 2430361 := bstep (se 2 (by rfl) ⟨911385, by rfl⟩ : syracuseStep 2430361 = 1822771) B1822771
theorem B1799575 : Blo 1798100 1799575 := bstep (se 1 (by rfl) ⟨1349681, by rfl⟩ : syracuseStep 1799575 = 2699363) B2699363
theorem B1799595 : Blo 1798100 1799595 := bstep (se 1 (by rfl) ⟨1349696, by rfl⟩ : syracuseStep 1799595 = 2699393) B2699393
theorem B1799607 : Blo 1798100 1799607 := bstep (se 1 (by rfl) ⟨1349705, by rfl⟩ : syracuseStep 1799607 = 2699411) B2699411
theorem B4552139 : Blo 1798100 4552139 := bstep (se 1 (by rfl) ⟨3414104, by rfl⟩ : syracuseStep 4552139 = 6828209) B6828209
theorem B1799627 : Blo 1798100 1799627 := bstep (se 1 (by rfl) ⟨1349720, by rfl⟩ : syracuseStep 1799627 = 2699441) B2699441
theorem B1799639 : Blo 1798100 1799639 := bstep (se 1 (by rfl) ⟨1349729, by rfl⟩ : syracuseStep 1799639 = 2699459) B2699459
theorem B1799659 : Blo 1798100 1799659 := bstep (se 1 (by rfl) ⟨1349744, by rfl⟩ : syracuseStep 1799659 = 2699489) B2699489
theorem B1799671 : Blo 1798100 1799671 := bstep (se 1 (by rfl) ⟨1349753, by rfl⟩ : syracuseStep 1799671 = 2699507) B2699507
theorem B3036683 : Blo 1798100 3036683 := bstep (se 1 (by rfl) ⟨2277512, by rfl⟩ : syracuseStep 3036683 = 4555025) B4555025
theorem B1799691 : Blo 1798100 1799691 := bstep (se 1 (by rfl) ⟨1349768, by rfl⟩ : syracuseStep 1799691 = 2699537) B2699537
theorem B1799703 : Blo 1798100 1799703 := bstep (se 1 (by rfl) ⟨1349777, by rfl⟩ : syracuseStep 1799703 = 2699555) B2699555
theorem B1799723 : Blo 1798100 1799723 := bstep (se 1 (by rfl) ⟨1349792, by rfl⟩ : syracuseStep 1799723 = 2699585) B2699585
theorem B6755885 : Blo 1798100 6755885 := bstep (se 3 (by rfl) ⟨1266728, by rfl⟩ : syracuseStep 6755885 = 2533457) B2533457
theorem B1799735 : Blo 1798100 1799735 := bstep (se 1 (by rfl) ⟨1349801, by rfl⟩ : syracuseStep 1799735 = 2699603) B2699603
theorem B1799755 : Blo 1798100 1799755 := bstep (se 1 (by rfl) ⟨1349816, by rfl⟩ : syracuseStep 1799755 = 2699633) B2699633
theorem B1799767 : Blo 1798100 1799767 := bstep (se 1 (by rfl) ⟨1349825, by rfl⟩ : syracuseStep 1799767 = 2699651) B2699651
theorem B1799787 : Blo 1798100 1799787 := bstep (se 1 (by rfl) ⟨1349840, by rfl⟩ : syracuseStep 1799787 = 2699681) B2699681
theorem B1799799 : Blo 1798100 1799799 := bstep (se 1 (by rfl) ⟨1349849, by rfl⟩ : syracuseStep 1799799 = 2699699) B2699699
theorem B3036811 : Blo 1798100 3036811 := bstep (se 1 (by rfl) ⟨2277608, by rfl⟩ : syracuseStep 3036811 = 4555217) B4555217
theorem B1799819 : Blo 1798100 1799819 := bstep (se 1 (by rfl) ⟨1349864, by rfl⟩ : syracuseStep 1799819 = 2699729) B2699729
theorem B1799831 : Blo 1798100 1799831 := bstep (se 1 (by rfl) ⟨1349873, by rfl⟩ : syracuseStep 1799831 = 2699747) B2699747
theorem B3413657 : Blo 1798100 3413657 := bstep (se 2 (by rfl) ⟨1280121, by rfl⟩ : syracuseStep 3413657 = 2560243) B2560243
theorem B1799851 : Blo 1798100 1799851 := bstep (se 1 (by rfl) ⟨1349888, by rfl⟩ : syracuseStep 1799851 = 2699777) B2699777
theorem B1799863 : Blo 1798100 1799863 := bstep (se 1 (by rfl) ⟨1349897, by rfl⟩ : syracuseStep 1799863 = 2699795) B2699795
theorem B1799883 : Blo 1798100 1799883 := bstep (se 1 (by rfl) ⟨1349912, by rfl⟩ : syracuseStep 1799883 = 2699825) B2699825
theorem B1799895 : Blo 1798100 1799895 := bstep (se 1 (by rfl) ⟨1349921, by rfl⟩ : syracuseStep 1799895 = 2699843) B2699843
theorem B1799915 : Blo 1798100 1799915 := bstep (se 1 (by rfl) ⟨1349936, by rfl⟩ : syracuseStep 1799915 = 2699873) B2699873
theorem B1799927 : Blo 1798100 1799927 := bstep (se 1 (by rfl) ⟨1349945, by rfl⟩ : syracuseStep 1799927 = 2699891) B2699891
theorem B1799947 : Blo 1798100 1799947 := bstep (se 1 (by rfl) ⟨1349960, by rfl⟩ : syracuseStep 1799947 = 2699921) B2699921
theorem B7788311 : Blo 1798100 7788311 := bstep (se 1 (by rfl) ⟨5841233, by rfl⟩ : syracuseStep 7788311 = 11682467) B11682467
theorem B1799959 : Blo 1798100 1799959 := bstep (se 1 (by rfl) ⟨1349969, by rfl⟩ : syracuseStep 1799959 = 2699939) B2699939
theorem B3036953 : Blo 1798100 3036953 := bstep (se 2 (by rfl) ⟨1138857, by rfl⟩ : syracuseStep 3036953 = 2277715) B2277715
theorem B1799979 : Blo 1798100 1799979 := bstep (se 1 (by rfl) ⟨1349984, by rfl⟩ : syracuseStep 1799979 = 2699969) B2699969
theorem B1799991 : Blo 1798100 1799991 := bstep (se 1 (by rfl) ⟨1349993, by rfl⟩ : syracuseStep 1799991 = 2699987) B2699987
theorem B1800011 : Blo 1798100 1800011 := bstep (se 1 (by rfl) ⟨1350008, by rfl⟩ : syracuseStep 1800011 = 2700017) B2700017
theorem B1800023 : Blo 1798100 1800023 := bstep (se 1 (by rfl) ⟨1350017, by rfl⟩ : syracuseStep 1800023 = 2700035) B2700035
theorem B1824599 : Blo 1798100 1824599 := bstep (se 1 (by rfl) ⟨1368449, by rfl⟩ : syracuseStep 1824599 = 2736899) B2736899
theorem B2881369 : Blo 1798100 2881369 := bstep (se 2 (by rfl) ⟨1080513, by rfl⟩ : syracuseStep 2881369 = 2161027) B2161027
theorem B1800043 : Blo 1798100 1800043 := bstep (se 1 (by rfl) ⟨1350032, by rfl⟩ : syracuseStep 1800043 = 2700065) B2700065
theorem B1800055 : Blo 1798100 1800055 := bstep (se 1 (by rfl) ⟨1350041, by rfl⟩ : syracuseStep 1800055 = 2700083) B2700083
theorem B1800075 : Blo 1798100 1800075 := bstep (se 1 (by rfl) ⟨1350056, by rfl⟩ : syracuseStep 1800075 = 2700113) B2700113
theorem B1800087 : Blo 1798100 1800087 := bstep (se 1 (by rfl) ⟨1350065, by rfl⟩ : syracuseStep 1800087 = 2700131) B2700131
theorem B2881433 : Blo 1798100 2881433 := bstep (se 2 (by rfl) ⟨1080537, by rfl⟩ : syracuseStep 2881433 = 2161075) B2161075
theorem B3037081 : Blo 1798100 3037081 := bstep (se 2 (by rfl) ⟨1138905, by rfl⟩ : syracuseStep 3037081 = 2277811) B2277811
theorem B12974003 : Blo 1798100 12974003 := bstep (se 1 (by rfl) ⟨9730502, by rfl⟩ : syracuseStep 12974003 = 19461005) B19461005
theorem B2881561 : Blo 1798100 2881561 := bstep (se 2 (by rfl) ⟨1080585, by rfl⟩ : syracuseStep 2881561 = 2161171) B2161171
theorem B7788761 : Blo 1798100 7788761 := bstep (se 2 (by rfl) ⟨2920785, by rfl⟩ : syracuseStep 7788761 = 5841571) B5841571
theorem B2464139 : Blo 1798100 2464139 := bstep (se 1 (by rfl) ⟨1848104, by rfl⟩ : syracuseStep 2464139 = 3696209) B3696209
theorem B4553111 : Blo 1798100 4553111 := bstep (se 1 (by rfl) ⟨3414833, by rfl⟩ : syracuseStep 4553111 = 6829667) B6829667
theorem B3037655 : Blo 1798100 3037655 := bstep (se 1 (by rfl) ⟨2278241, by rfl⟩ : syracuseStep 3037655 = 4556483) B4556483
theorem B7682521 : Blo 1798100 7682521 := bstep (se 2 (by rfl) ⟨2880945, by rfl⟩ : syracuseStep 7682521 = 5761891) B5761891
theorem B8206865 : Blo 1798100 8206865 := bstep (se 2 (by rfl) ⟨3077574, by rfl⟩ : syracuseStep 8206865 = 6155149) B6155149
theorem B2431577 : Blo 1798100 2431577 := bstep (se 2 (by rfl) ⟨911841, by rfl⟩ : syracuseStep 2431577 = 1823683) B1823683
theorem B3160715 : Blo 1798100 3160715 := bstep (se 1 (by rfl) ⟨2370536, by rfl⟩ : syracuseStep 3160715 = 4741073) B4741073
theorem B7297715 : Blo 1798100 7297715 := bstep (se 1 (by rfl) ⟨5473286, by rfl⟩ : syracuseStep 7297715 = 10946573) B10946573
theorem B4324033 : Blo 1798100 4324033 := bstep (se 2 (by rfl) ⟨1621512, by rfl⟩ : syracuseStep 4324033 = 3243025) B3243025
theorem B6830851 : Blo 1798100 6830851 := bstep (se 1 (by rfl) ⟨5123138, by rfl⟩ : syracuseStep 6830851 = 10246277) B10246277
theorem B31152961 : Blo 1798100 31152961 := bstep (se 2 (by rfl) ⟨11682360, by rfl⟩ : syracuseStep 31152961 = 23364721) B23364721
theorem B2276363 : Blo 1798100 2276363 := bstep (se 1 (by rfl) ⟨1707272, by rfl⟩ : syracuseStep 2276363 = 3414545) B3414545
theorem B4553779 : Blo 1798100 4553779 := bstep (se 1 (by rfl) ⟨3415334, by rfl⟩ : syracuseStep 4553779 = 6830669) B6830669
theorem B6831155 : Blo 1798100 6831155 := bstep (se 1 (by rfl) ⟨5123366, by rfl⟩ : syracuseStep 6831155 = 10246733) B10246733
theorem B7683137 : Blo 1798100 7683137 := bstep (se 2 (by rfl) ⟨2881176, by rfl⟩ : syracuseStep 7683137 = 5762353) B5762353
theorem B3415115 : Blo 1798100 3415115 := bstep (se 1 (by rfl) ⟨2561336, by rfl⟩ : syracuseStep 3415115 = 5122673) B5122673
theorem B4045913 : Blo 1798100 4045913 := bstep (se 2 (by rfl) ⟨1517217, by rfl⟩ : syracuseStep 4045913 = 3034435) B3034435
theorem B8313949 : Blo 1798100 8313949 := bstep (se 3 (by rfl) ⟨1558865, by rfl⟩ : syracuseStep 8313949 = 3117731) B3117731
theorem B13655141 : Blo 1798100 13655141 := bstep (se 4 (by rfl) ⟨1280169, by rfl⟩ : syracuseStep 13655141 = 2560339) B2560339
theorem B9108611 : Blo 1798100 9108611 := bstep (se 1 (by rfl) ⟨6831458, by rfl⟩ : syracuseStep 9108611 = 13662917) B13662917
theorem B4046003 : Blo 1798100 4046003 := bstep (se 1 (by rfl) ⟨3034502, by rfl⟩ : syracuseStep 4046003 = 6069005) B6069005
theorem B30727349 : Blo 1798100 30727349 := bstep (se 5 (by rfl) ⟨1440344, by rfl⟩ : syracuseStep 30727349 = 2880689) B2880689
theorem B6569153 : Blo 1798100 6569153 := bstep (se 2 (by rfl) ⟨2463432, by rfl⟩ : syracuseStep 6569153 = 4926865) B4926865
theorem B4553921 : Blo 1798100 4553921 := bstep (se 2 (by rfl) ⟨1707720, by rfl⟩ : syracuseStep 4553921 = 3415441) B3415441
theorem B4046039 : Blo 1798100 4046039 := bstep (se 1 (by rfl) ⟨3034529, by rfl⟩ : syracuseStep 4046039 = 6069059) B6069059
theorem B3415297 : Blo 1798100 3415297 := bstep (se 2 (by rfl) ⟨1280736, by rfl⟩ : syracuseStep 3415297 = 2561473) B2561473
theorem B20503853 : Blo 1798100 20503853 := bstep (se 3 (by rfl) ⟨3844472, by rfl⟩ : syracuseStep 20503853 = 7688945) B7688945
theorem B7396697 : Blo 1798100 7396697 := bstep (se 2 (by rfl) ⟨2773761, by rfl⟩ : syracuseStep 7396697 = 5547523) B5547523
theorem B4046219 : Blo 1798100 4046219 := bstep (se 1 (by rfl) ⟨3034664, by rfl⟩ : syracuseStep 4046219 = 6069329) B6069329
theorem B4046273 : Blo 1798100 4046273 := bstep (se 2 (by rfl) ⟨1517352, by rfl⟩ : syracuseStep 4046273 = 3034705) B3034705
theorem B6069707 : Blo 1798100 6069707 := bstep (se 1 (by rfl) ⟨4552280, by rfl⟩ : syracuseStep 6069707 = 9104561) B9104561
theorem B2022871 : Blo 1798100 2022871 := bstep (se 1 (by rfl) ⟨1517153, by rfl⟩ : syracuseStep 2022871 = 3034307) B3034307
theorem B13655627 : Blo 1798100 13655627 := bstep (se 1 (by rfl) ⟨10241720, by rfl⟩ : syracuseStep 13655627 = 20483441) B20483441
theorem B2023051 : Blo 1798100 2023051 := bstep (se 1 (by rfl) ⟨1517288, by rfl⟩ : syracuseStep 2023051 = 3034577) B3034577
theorem B6659729 : Blo 1798100 6659729 := bstep (se 2 (by rfl) ⟨2497398, by rfl⟩ : syracuseStep 6659729 = 4994797) B4994797
theorem B4046489 : Blo 1798100 4046489 := bstep (se 2 (by rfl) ⟨1517433, by rfl⟩ : syracuseStep 4046489 = 3034867) B3034867
theorem B3415745 : Blo 1798100 3415745 := bstep (se 2 (by rfl) ⟨1280904, by rfl⟩ : syracuseStep 3415745 = 2561809) B2561809
theorem B6831809 : Blo 1798100 6831809 := bstep (se 2 (by rfl) ⟨2561928, by rfl⟩ : syracuseStep 6831809 = 5123857) B5123857
theorem B2277067 : Blo 1798100 2277067 := bstep (se 1 (by rfl) ⟨1707800, by rfl⟩ : syracuseStep 2277067 = 3415601) B3415601
theorem B6069977 : Blo 1798100 6069977 := bstep (se 2 (by rfl) ⟨2276241, by rfl⟩ : syracuseStep 6069977 = 4552483) B4552483
theorem B4046579 : Blo 1798100 4046579 := bstep (se 1 (by rfl) ⟨3034934, by rfl⟩ : syracuseStep 4046579 = 6069869) B6069869
theorem B2023159 : Blo 1798100 2023159 := bstep (se 1 (by rfl) ⟨1517369, by rfl⟩ : syracuseStep 2023159 = 3034739) B3034739
theorem B4046615 : Blo 1798100 4046615 := bstep (se 1 (by rfl) ⟨3034961, by rfl⟩ : syracuseStep 4046615 = 6069923) B6069923
theorem B12967715 : Blo 1798100 12967715 := bstep (se 1 (by rfl) ⟨9725786, by rfl⟩ : syracuseStep 12967715 = 19451573) B19451573
theorem B2023339 : Blo 1798100 2023339 := bstep (se 1 (by rfl) ⟨1517504, by rfl⟩ : syracuseStep 2023339 = 3035009) B3035009
theorem B4046795 : Blo 1798100 4046795 := bstep (se 1 (by rfl) ⟨3035096, by rfl⟩ : syracuseStep 4046795 = 6070193) B6070193
theorem B2277335 : Blo 1798100 2277335 := bstep (se 1 (by rfl) ⟨1708001, by rfl⟩ : syracuseStep 2277335 = 3416003) B3416003
theorem B6922205 : Blo 1798100 6922205 := bstep (se 3 (by rfl) ⟨1297913, by rfl⟩ : syracuseStep 6922205 = 2595827) B2595827
theorem B2277391 : Blo 1798100 2277391 := bstep (se 1 (by rfl) ⟨1708043, by rfl⟩ : syracuseStep 2277391 = 3416087) B3416087
theorem B6070301 : Blo 1798100 6070301 := bstep (se 3 (by rfl) ⟨1138181, by rfl⟩ : syracuseStep 6070301 = 2276363) B2276363
theorem B3842081 : Blo 1798100 3842081 := bstep (se 2 (by rfl) ⟨1440780, by rfl⟩ : syracuseStep 3842081 = 2881561) B2881561
theorem B2023483 : Blo 1798100 2023483 := bstep (se 1 (by rfl) ⟨1517612, by rfl⟩ : syracuseStep 2023483 = 3035225) B3035225
theorem B3842167 : Blo 1798100 3842167 := bstep (se 1 (by rfl) ⟨2881625, by rfl⟩ : syracuseStep 3842167 = 5763251) B5763251
theorem B4382873 : Blo 1798100 4382873 := bstep (se 2 (by rfl) ⟨1643577, by rfl⟩ : syracuseStep 4382873 = 3287155) B3287155
theorem B5193985 : Blo 1798100 5193985 := bstep (se 2 (by rfl) ⟨1947744, by rfl⟩ : syracuseStep 5193985 = 3895489) B3895489
theorem B30744845 : Blo 1798100 30744845 := bstep (se 3 (by rfl) ⟨5764658, by rfl⟩ : syracuseStep 30744845 = 11529317) B11529317
theorem B4047119 : Blo 1798100 4047119 := bstep (se 1 (by rfl) ⟨3035339, by rfl⟩ : syracuseStep 4047119 = 6070679) B6070679
theorem B4047137 : Blo 1798100 4047137 := bstep (se 2 (by rfl) ⟨1517676, by rfl⟩ : syracuseStep 4047137 = 3035353) B3035353
theorem B9109907 : Blo 1798100 9109907 := bstep (se 1 (by rfl) ⟨6832430, by rfl⟩ : syracuseStep 9109907 = 13664861) B13664861
theorem B2023951 : Blo 1798100 2023951 := bstep (se 1 (by rfl) ⟨1517963, by rfl⟩ : syracuseStep 2023951 = 3035927) B3035927
theorem B73843235 : Blo 1798100 73843235 := bstep (se 1 (by rfl) ⟨55382426, by rfl⟩ : syracuseStep 73843235 = 110764853) B110764853
theorem B11092567 : Blo 1798100 11092567 := bstep (se 1 (by rfl) ⟨8319425, by rfl⟩ : syracuseStep 11092567 = 16638851) B16638851
theorem B4555379 : Blo 1798100 4555379 := bstep (se 1 (by rfl) ⟨3416534, by rfl⟩ : syracuseStep 4555379 = 6833069) B6833069
theorem B4047479 : Blo 1798100 4047479 := bstep (se 1 (by rfl) ⟨3035609, by rfl⟩ : syracuseStep 4047479 = 6071219) B6071219
theorem B4555399 : Blo 1798100 4555399 := bstep (se 1 (by rfl) ⟨3416549, by rfl⟩ : syracuseStep 4555399 = 6833099) B6833099
theorem B166216373 : Blo 1798100 166216373 := bstep (se 5 (by rfl) ⟨7791392, by rfl⟩ : syracuseStep 166216373 = 15582785) B15582785
theorem B2278135 : Blo 1798100 2278135 := bstep (se 1 (by rfl) ⟨1708601, by rfl⟩ : syracuseStep 2278135 = 3417203) B3417203
theorem B58336037 : Blo 1798100 58336037 := bstep (se 4 (by rfl) ⟨5469003, by rfl⟩ : syracuseStep 58336037 = 10938007) B10938007
theorem B4047659 : Blo 1798100 4047659 := bstep (se 1 (by rfl) ⟨3035744, by rfl⟩ : syracuseStep 4047659 = 6071489) B6071489
theorem B4555673 : Blo 1798100 4555673 := bstep (se 2 (by rfl) ⟨1708377, by rfl⟩ : syracuseStep 4555673 = 3416755) B3416755
theorem B2024455 : Blo 1798100 2024455 := bstep (se 1 (by rfl) ⟨1518341, by rfl⟩ : syracuseStep 2024455 = 3036683) B3036683
theorem B6571037 : Blo 1798100 6571037 := bstep (se 3 (by rfl) ⟨1232069, by rfl⟩ : syracuseStep 6571037 = 2464139) B2464139
theorem B4555835 : Blo 1798100 4555835 := bstep (se 1 (by rfl) ⟨3416876, by rfl⟩ : syracuseStep 4555835 = 6833753) B6833753
theorem B7685239 : Blo 1798100 7685239 := bstep (se 1 (by rfl) ⟨5763929, by rfl⟩ : syracuseStep 7685239 = 11527859) B11527859
theorem B18457733 : Blo 1798100 18457733 := bstep (se 4 (by rfl) ⟨1730412, by rfl⟩ : syracuseStep 18457733 = 3460825) B3460825
theorem B4048019 : Blo 1798100 4048019 := bstep (se 1 (by rfl) ⟨3036014, by rfl⟩ : syracuseStep 4048019 = 6072029) B6072029
theorem B2024635 : Blo 1798100 2024635 := bstep (se 1 (by rfl) ⟨1518476, by rfl⟩ : syracuseStep 2024635 = 3036953) B3036953
theorem B4048073 : Blo 1798100 4048073 := bstep (se 2 (by rfl) ⟨1518027, by rfl⟩ : syracuseStep 4048073 = 3036055) B3036055
theorem B4556047 : Blo 1798100 4556047 := bstep (se 1 (by rfl) ⟨3417035, by rfl⟩ : syracuseStep 4556047 = 6834071) B6834071
theorem B21874067 : Blo 1798100 21874067 := bstep (se 1 (by rfl) ⟨16405550, by rfl⟩ : syracuseStep 21874067 = 32811101) B32811101
theorem B6833555 : Blo 1798100 6833555 := bstep (se 1 (by rfl) ⟨5125166, by rfl⟩ : syracuseStep 6833555 = 10250333) B10250333
theorem B6071705 : Blo 1798100 6071705 := bstep (se 2 (by rfl) ⟨2276889, by rfl⟩ : syracuseStep 6071705 = 4553779) B4553779
theorem B11085265 : Blo 1798100 11085265 := bstep (se 2 (by rfl) ⟨4156974, by rfl⟩ : syracuseStep 11085265 = 8313949) B8313949
theorem B4556321 : Blo 1798100 4556321 := bstep (se 2 (by rfl) ⟨1708620, by rfl⟩ : syracuseStep 4556321 = 3417241) B3417241
theorem B20498021 : Blo 1798100 20498021 := bstep (se 4 (by rfl) ⟨1921689, by rfl⟩ : syracuseStep 20498021 = 3843379) B3843379
theorem B2025103 : Blo 1798100 2025103 := bstep (se 1 (by rfl) ⟨1518827, by rfl⟩ : syracuseStep 2025103 = 3037655) B3037655
theorem B10249901 : Blo 1798100 10249901 := bstep (se 3 (by rfl) ⟨1921856, by rfl⟩ : syracuseStep 10249901 = 3843713) B3843713
theorem B5760713 : Blo 1798100 5760713 := bstep (se 2 (by rfl) ⟨2160267, by rfl⟩ : syracuseStep 5760713 = 4320535) B4320535
theorem B4048775 : Blo 1798100 4048775 := bstep (se 1 (by rfl) ⟨3036581, by rfl⟩ : syracuseStep 4048775 = 6073163) B6073163
theorem B2697161 : Blo 1798100 2697161 := bstep (se 2 (by rfl) ⟨1011435, by rfl⟩ : syracuseStep 2697161 = 2022871) B2022871
theorem B5122091 : Blo 1798100 5122091 := bstep (se 1 (by rfl) ⟨3841568, by rfl⟩ : syracuseStep 5122091 = 7683137) B7683137
theorem B2697275 : Blo 1798100 2697275 := bstep (se 1 (by rfl) ⟨2022956, by rfl⟩ : syracuseStep 2697275 = 4045913) B4045913
theorem B4048955 : Blo 1798100 4048955 := bstep (se 1 (by rfl) ⟨3036716, by rfl⟩ : syracuseStep 4048955 = 6073433) B6073433
theorem B9103427 : Blo 1798100 9103427 := bstep (se 1 (by rfl) ⟨6827570, by rfl⟩ : syracuseStep 9103427 = 13655141) B13655141
theorem B6072407 : Blo 1798100 6072407 := bstep (se 1 (by rfl) ⟨4554305, by rfl⟩ : syracuseStep 6072407 = 9108611) B9108611
theorem B2697335 : Blo 1798100 2697335 := bstep (se 1 (by rfl) ⟨2023001, by rfl⟩ : syracuseStep 2697335 = 4046003) B4046003
theorem B2697359 : Blo 1798100 2697359 := bstep (se 1 (by rfl) ⟨2023019, by rfl⟩ : syracuseStep 2697359 = 4046039) B4046039
theorem B2697401 : Blo 1798100 2697401 := bstep (se 2 (by rfl) ⟨1011525, by rfl⟩ : syracuseStep 2697401 = 2023051) B2023051
theorem B4049081 : Blo 1798100 4049081 := bstep (se 2 (by rfl) ⟨1518405, by rfl⟩ : syracuseStep 4049081 = 3036811) B3036811
theorem B2697479 : Blo 1798100 2697479 := bstep (se 1 (by rfl) ⟨2023109, by rfl⟩ : syracuseStep 2697479 = 4046219) B4046219
theorem B2697515 : Blo 1798100 2697515 := bstep (se 1 (by rfl) ⟨2023136, by rfl⟩ : syracuseStep 2697515 = 4046273) B4046273
theorem B2697545 : Blo 1798100 2697545 := bstep (se 2 (by rfl) ⟨1011579, by rfl⟩ : syracuseStep 2697545 = 2023159) B2023159
theorem B9103751 : Blo 1798100 9103751 := bstep (se 1 (by rfl) ⟨6827813, by rfl⟩ : syracuseStep 9103751 = 13655627) B13655627
theorem B2697659 : Blo 1798100 2697659 := bstep (se 1 (by rfl) ⟨2023244, by rfl⟩ : syracuseStep 2697659 = 4046489) B4046489
theorem B2697719 : Blo 1798100 2697719 := bstep (se 1 (by rfl) ⟨2023289, by rfl⟩ : syracuseStep 2697719 = 4046579) B4046579
theorem B2697743 : Blo 1798100 2697743 := bstep (se 1 (by rfl) ⟨2023307, by rfl⟩ : syracuseStep 2697743 = 4046615) B4046615
theorem B4049423 : Blo 1798100 4049423 := bstep (se 1 (by rfl) ⟨3037067, by rfl⟩ : syracuseStep 4049423 = 6074135) B6074135
theorem B8645143 : Blo 1798100 8645143 := bstep (se 1 (by rfl) ⟨6483857, by rfl⟩ : syracuseStep 8645143 = 12967715) B12967715
theorem B4049441 : Blo 1798100 4049441 := bstep (se 2 (by rfl) ⟨1518540, by rfl⟩ : syracuseStep 4049441 = 3037081) B3037081
theorem B2697785 : Blo 1798100 2697785 := bstep (se 2 (by rfl) ⟨1011669, by rfl⟩ : syracuseStep 2697785 = 2023339) B2023339
theorem B6072893 : Blo 1798100 6072893 := bstep (se 3 (by rfl) ⟨1138667, by rfl⟩ : syracuseStep 6072893 = 2277335) B2277335
theorem B2697863 : Blo 1798100 2697863 := bstep (se 1 (by rfl) ⟨2023397, by rfl⟩ : syracuseStep 2697863 = 4046795) B4046795
theorem B4614803 : Blo 1798100 4614803 := bstep (se 1 (by rfl) ⟨3461102, by rfl⟩ : syracuseStep 4614803 = 6922205) B6922205
theorem B2697899 : Blo 1798100 2697899 := bstep (se 1 (by rfl) ⟨2023424, by rfl⟩ : syracuseStep 2697899 = 4046849) B4046849
theorem B12315329 : Blo 1798100 12315329 := bstep (se 2 (by rfl) ⟨4618248, by rfl⟩ : syracuseStep 12315329 = 9236497) B9236497
theorem B2697929 : Blo 1798100 2697929 := bstep (se 2 (by rfl) ⟨1011723, by rfl⟩ : syracuseStep 2697929 = 2023447) B2023447
theorem B2698043 : Blo 1798100 2698043 := bstep (se 1 (by rfl) ⟨2023532, by rfl⟩ : syracuseStep 2698043 = 4047065) B4047065
theorem B2698103 : Blo 1798100 2698103 := bstep (se 1 (by rfl) ⟨2023577, by rfl⟩ : syracuseStep 2698103 = 4047155) B4047155
theorem B4049783 : Blo 1798100 4049783 := bstep (se 1 (by rfl) ⟨3037337, by rfl⟩ : syracuseStep 4049783 = 6074675) B6074675
theorem B2698127 : Blo 1798100 2698127 := bstep (se 1 (by rfl) ⟨2023595, by rfl⟩ : syracuseStep 2698127 = 4047191) B4047191
theorem B17288099 : Blo 1798100 17288099 := bstep (se 1 (by rfl) ⟨12966074, by rfl⟩ : syracuseStep 17288099 = 25932149) B25932149
theorem B2698169 : Blo 1798100 2698169 := bstep (se 2 (by rfl) ⟨1011813, by rfl⟩ : syracuseStep 2698169 = 2023627) B2023627
theorem B9726979 : Blo 1798100 9726979 := bstep (se 1 (by rfl) ⟨7295234, by rfl⟩ : syracuseStep 9726979 = 14590469) B14590469
theorem B2698247 : Blo 1798100 2698247 := bstep (se 1 (by rfl) ⟨2023685, by rfl⟩ : syracuseStep 2698247 = 4047371) B4047371
theorem B20499479 : Blo 1798100 20499479 := bstep (se 1 (by rfl) ⟨15374609, by rfl⟩ : syracuseStep 20499479 = 30749219) B30749219
theorem B2698283 : Blo 1798100 2698283 := bstep (se 1 (by rfl) ⟨2023712, by rfl⟩ : syracuseStep 2698283 = 4047425) B4047425
theorem B4049963 : Blo 1798100 4049963 := bstep (se 1 (by rfl) ⟨3037472, by rfl⟩ : syracuseStep 4049963 = 6074945) B6074945
theorem B2698313 : Blo 1798100 2698313 := bstep (se 2 (by rfl) ⟨1011867, by rfl⟩ : syracuseStep 2698313 = 2023735) B2023735
theorem B2698427 : Blo 1798100 2698427 := bstep (se 1 (by rfl) ⟨2023820, by rfl⟩ : syracuseStep 2698427 = 4047641) B4047641
theorem B12479689 : Blo 1798100 12479689 := bstep (se 2 (by rfl) ⟨4679883, by rfl⟩ : syracuseStep 12479689 = 9359767) B9359767
theorem B2698487 : Blo 1798100 2698487 := bstep (se 1 (by rfl) ⟨2023865, by rfl⟩ : syracuseStep 2698487 = 4047731) B4047731
theorem B2698511 : Blo 1798100 2698511 := bstep (se 1 (by rfl) ⟨2023883, by rfl⟩ : syracuseStep 2698511 = 4047767) B4047767
theorem B10243361 : Blo 1798100 10243361 := bstep (se 2 (by rfl) ⟨3841260, by rfl⟩ : syracuseStep 10243361 = 7682521) B7682521
theorem B2698553 : Blo 1798100 2698553 := bstep (se 2 (by rfl) ⟨1011957, by rfl⟩ : syracuseStep 2698553 = 2023915) B2023915
theorem B2051387 : Blo 1798100 2051387 := bstep (se 1 (by rfl) ⟨1538540, by rfl⟩ : syracuseStep 2051387 = 3077081) B3077081
theorem B1920391 : Blo 1798100 1920391 := bstep (se 1 (by rfl) ⟨1440293, by rfl⟩ : syracuseStep 1920391 = 2880587) B2880587
theorem B2698631 : Blo 1798100 2698631 := bstep (se 1 (by rfl) ⟨2023973, by rfl⟩ : syracuseStep 2698631 = 4047947) B4047947
theorem B9112985 : Blo 1798100 9112985 := bstep (se 2 (by rfl) ⟨3417369, by rfl⟩ : syracuseStep 9112985 = 6834739) B6834739
theorem B2698667 : Blo 1798100 2698667 := bstep (se 1 (by rfl) ⟨2024000, by rfl⟩ : syracuseStep 2698667 = 4048001) B4048001
theorem B6827449 : Blo 1798100 6827449 := bstep (se 2 (by rfl) ⟨2560293, by rfl⟩ : syracuseStep 6827449 = 5120587) B5120587
theorem B2698697 : Blo 1798100 2698697 := bstep (se 2 (by rfl) ⟨1012011, by rfl⟩ : syracuseStep 2698697 = 2024023) B2024023
theorem B14585309 : Blo 1798100 14585309 := bstep (se 3 (by rfl) ⟨2734745, by rfl⟩ : syracuseStep 14585309 = 5469491) B5469491
theorem B2698811 : Blo 1798100 2698811 := bstep (se 1 (by rfl) ⟨2024108, by rfl⟩ : syracuseStep 2698811 = 4048217) B4048217
theorem B2698871 : Blo 1798100 2698871 := bstep (se 1 (by rfl) ⟨2024153, by rfl⟩ : syracuseStep 2698871 = 4048307) B4048307
theorem B3034759 : Blo 1798100 3034759 := bstep (se 1 (by rfl) ⟨2276069, by rfl⟩ : syracuseStep 3034759 = 4552139) B4552139
theorem B2698895 : Blo 1798100 2698895 := bstep (se 1 (by rfl) ⟨2024171, by rfl⟩ : syracuseStep 2698895 = 4048343) B4048343
theorem B5123731 : Blo 1798100 5123731 := bstep (se 1 (by rfl) ⟨3842798, by rfl⟩ : syracuseStep 5123731 = 7685597) B7685597
theorem B2698937 : Blo 1798100 2698937 := bstep (se 2 (by rfl) ⟨1012101, by rfl⟩ : syracuseStep 2698937 = 2024203) B2024203
theorem B41537281 : Blo 1798100 41537281 := bstep (se 2 (by rfl) ⟨15576480, by rfl⟩ : syracuseStep 41537281 = 31152961) B31152961
theorem B11529985 : Blo 1798100 11529985 := bstep (se 2 (by rfl) ⟨4323744, by rfl⟩ : syracuseStep 11529985 = 8647489) B8647489
theorem B2699015 : Blo 1798100 2699015 := bstep (se 1 (by rfl) ⟨2024261, by rfl⟩ : syracuseStep 2699015 = 4048523) B4048523
theorem B2699051 : Blo 1798100 2699051 := bstep (se 1 (by rfl) ⟨2024288, by rfl⟩ : syracuseStep 2699051 = 4048577) B4048577
theorem B2699081 : Blo 1798100 2699081 := bstep (se 2 (by rfl) ⟨1012155, by rfl⟩ : syracuseStep 2699081 = 2024311) B2024311
theorem B8761223 : Blo 1798100 8761223 := bstep (se 1 (by rfl) ⟨6570917, by rfl⟩ : syracuseStep 8761223 = 13141835) B13141835
theorem B6074297 : Blo 1798100 6074297 := bstep (se 2 (by rfl) ⟨2277861, by rfl⟩ : syracuseStep 6074297 = 4555723) B4555723
theorem B2699195 : Blo 1798100 2699195 := bstep (se 1 (by rfl) ⟨2024396, by rfl⟩ : syracuseStep 2699195 = 4048793) B4048793
theorem B2699255 : Blo 1798100 2699255 := bstep (se 1 (by rfl) ⟨2024441, by rfl⟩ : syracuseStep 2699255 = 4048883) B4048883
theorem B1798151 : Blo 1798100 1798151 := bstep (se 1 (by rfl) ⟨1348613, by rfl⟩ : syracuseStep 1798151 = 2697227) B2697227
theorem B1798159 : Blo 1798100 1798159 := bstep (se 1 (by rfl) ⟨1348619, by rfl⟩ : syracuseStep 1798159 = 2697239) B2697239
theorem B2699279 : Blo 1798100 2699279 := bstep (se 1 (by rfl) ⟨2024459, by rfl⟩ : syracuseStep 2699279 = 4048919) B4048919
theorem B2699321 : Blo 1798100 2699321 := bstep (se 2 (by rfl) ⟨1012245, by rfl⟩ : syracuseStep 2699321 = 2024491) B2024491
theorem B1798203 : Blo 1798100 1798203 := bstep (se 1 (by rfl) ⟨1348652, by rfl⟩ : syracuseStep 1798203 = 2697305) B2697305
theorem B1798279 : Blo 1798100 1798279 := bstep (se 1 (by rfl) ⟨1348709, by rfl⟩ : syracuseStep 1798279 = 2697419) B2697419
theorem B2699399 : Blo 1798100 2699399 := bstep (se 1 (by rfl) ⟨2024549, by rfl⟩ : syracuseStep 2699399 = 4049099) B4049099
theorem B1798287 : Blo 1798100 1798287 := bstep (se 1 (by rfl) ⟨1348715, by rfl⟩ : syracuseStep 1798287 = 2697431) B2697431
theorem B2699435 : Blo 1798100 2699435 := bstep (se 1 (by rfl) ⟨2024576, by rfl⟩ : syracuseStep 2699435 = 4049153) B4049153
theorem B1798331 : Blo 1798100 1798331 := bstep (se 1 (by rfl) ⟨1348748, by rfl⟩ : syracuseStep 1798331 = 2697497) B2697497
theorem B2699465 : Blo 1798100 2699465 := bstep (se 2 (by rfl) ⟨1012299, by rfl⟩ : syracuseStep 2699465 = 2024599) B2024599
theorem B6484205 : Blo 1798100 6484205 := bstep (se 3 (by rfl) ⟨1215788, by rfl⟩ : syracuseStep 6484205 = 2431577) B2431577
theorem B1798407 : Blo 1798100 1798407 := bstep (se 1 (by rfl) ⟨1348805, by rfl⟩ : syracuseStep 1798407 = 2697611) B2697611
theorem B1798415 : Blo 1798100 1798415 := bstep (se 1 (by rfl) ⟨1348811, by rfl⟩ : syracuseStep 1798415 = 2697623) B2697623
theorem B3035407 : Blo 1798100 3035407 := bstep (se 1 (by rfl) ⟨2276555, by rfl⟩ : syracuseStep 3035407 = 4553111) B4553111
theorem B1798459 : Blo 1798100 1798459 := bstep (se 1 (by rfl) ⟨1348844, by rfl⟩ : syracuseStep 1798459 = 2697689) B2697689
theorem B2699579 : Blo 1798100 2699579 := bstep (se 1 (by rfl) ⟨2024684, by rfl⟩ : syracuseStep 2699579 = 4049369) B4049369
theorem B38900033 : Blo 1798100 38900033 := bstep (se 2 (by rfl) ⟨14587512, by rfl⟩ : syracuseStep 38900033 = 29175025) B29175025
theorem B2699639 : Blo 1798100 2699639 := bstep (se 1 (by rfl) ⟨2024729, by rfl⟩ : syracuseStep 2699639 = 4049459) B4049459
theorem B1798535 : Blo 1798100 1798535 := bstep (se 1 (by rfl) ⟨1348901, by rfl⟩ : syracuseStep 1798535 = 2697803) B2697803
theorem B1798543 : Blo 1798100 1798543 := bstep (se 1 (by rfl) ⟨1348907, by rfl⟩ : syracuseStep 1798543 = 2697815) B2697815
theorem B2699663 : Blo 1798100 2699663 := bstep (se 1 (by rfl) ⟨2024747, by rfl⟩ : syracuseStep 2699663 = 4049495) B4049495
theorem B2699705 : Blo 1798100 2699705 := bstep (se 2 (by rfl) ⟨1012389, by rfl⟩ : syracuseStep 2699705 = 2024779) B2024779
theorem B1798587 : Blo 1798100 1798587 := bstep (se 1 (by rfl) ⟨1348940, by rfl⟩ : syracuseStep 1798587 = 2697881) B2697881
theorem B1798663 : Blo 1798100 1798663 := bstep (se 1 (by rfl) ⟨1348997, by rfl⟩ : syracuseStep 1798663 = 2697995) B2697995
theorem B2699783 : Blo 1798100 2699783 := bstep (se 1 (by rfl) ⟨2024837, by rfl⟩ : syracuseStep 2699783 = 4049675) B4049675
theorem B6074891 : Blo 1798100 6074891 := bstep (se 1 (by rfl) ⟨4556168, by rfl⟩ : syracuseStep 6074891 = 9112337) B9112337
theorem B1798671 : Blo 1798100 1798671 := bstep (se 1 (by rfl) ⟨1349003, by rfl⟩ : syracuseStep 1798671 = 2698007) B2698007
theorem B3240481 : Blo 1798100 3240481 := bstep (se 2 (by rfl) ⟨1215180, by rfl⟩ : syracuseStep 3240481 = 2430361) B2430361
theorem B2699819 : Blo 1798100 2699819 := bstep (se 1 (by rfl) ⟨2024864, by rfl⟩ : syracuseStep 2699819 = 4049729) B4049729
theorem B1798715 : Blo 1798100 1798715 := bstep (se 1 (by rfl) ⟨1349036, by rfl⟩ : syracuseStep 1798715 = 2698073) B2698073
theorem B2699849 : Blo 1798100 2699849 := bstep (se 2 (by rfl) ⟨1012443, by rfl⟩ : syracuseStep 2699849 = 2024887) B2024887
theorem B6074999 : Blo 1798100 6074999 := bstep (se 1 (by rfl) ⟨4556249, by rfl⟩ : syracuseStep 6074999 = 9112499) B9112499
theorem B1798791 : Blo 1798100 1798791 := bstep (se 1 (by rfl) ⟨1349093, by rfl⟩ : syracuseStep 1798791 = 2698187) B2698187
theorem B1798799 : Blo 1798100 1798799 := bstep (se 1 (by rfl) ⟨1349099, by rfl⟩ : syracuseStep 1798799 = 2698199) B2698199
theorem B3895955 : Blo 1798100 3895955 := bstep (se 1 (by rfl) ⟨2921966, by rfl⟩ : syracuseStep 3895955 = 5843933) B5843933
theorem B1798843 : Blo 1798100 1798843 := bstep (se 1 (by rfl) ⟨1349132, by rfl⟩ : syracuseStep 1798843 = 2698265) B2698265
theorem B2699963 : Blo 1798100 2699963 := bstep (se 1 (by rfl) ⟨2024972, by rfl⟩ : syracuseStep 2699963 = 4049945) B4049945
theorem B2700023 : Blo 1798100 2700023 := bstep (se 1 (by rfl) ⟨2025017, by rfl⟩ : syracuseStep 2700023 = 4050035) B4050035
theorem B19444481 : Blo 1798100 19444481 := bstep (se 2 (by rfl) ⟨7291680, by rfl⟩ : syracuseStep 19444481 = 14583361) B14583361
theorem B1798919 : Blo 1798100 1798919 := bstep (se 1 (by rfl) ⟨1349189, by rfl⟩ : syracuseStep 1798919 = 2698379) B2698379
theorem B3240719 : Blo 1798100 3240719 := bstep (se 1 (by rfl) ⟨2430539, by rfl⟩ : syracuseStep 3240719 = 4861079) B4861079
theorem B1798927 : Blo 1798100 1798927 := bstep (se 1 (by rfl) ⟨1349195, by rfl⟩ : syracuseStep 1798927 = 2698391) B2698391
theorem B2700047 : Blo 1798100 2700047 := bstep (se 1 (by rfl) ⟨2025035, by rfl⟩ : syracuseStep 2700047 = 4050071) B4050071
theorem B20484899 : Blo 1798100 20484899 := bstep (se 1 (by rfl) ⟨15363674, by rfl⟩ : syracuseStep 20484899 = 30727349) B30727349
theorem B4379435 : Blo 1798100 4379435 := bstep (se 1 (by rfl) ⟨3284576, by rfl⟩ : syracuseStep 4379435 = 6569153) B6569153
theorem B3035947 : Blo 1798100 3035947 := bstep (se 1 (by rfl) ⟨2276960, by rfl⟩ : syracuseStep 3035947 = 4553921) B4553921
theorem B2700089 : Blo 1798100 2700089 := bstep (se 2 (by rfl) ⟨1012533, by rfl⟩ : syracuseStep 2700089 = 2025067) B2025067
theorem B1798971 : Blo 1798100 1798971 := bstep (se 1 (by rfl) ⟨1349228, by rfl⟩ : syracuseStep 1798971 = 2698457) B2698457
theorem B4551511 : Blo 1798100 4551511 := bstep (se 1 (by rfl) ⟨3413633, by rfl⟩ : syracuseStep 4551511 = 6827267) B6827267
theorem B13669235 : Blo 1798100 13669235 := bstep (se 1 (by rfl) ⟨10251926, by rfl⟩ : syracuseStep 13669235 = 20503853) B20503853
theorem B1799047 : Blo 1798100 1799047 := bstep (se 1 (by rfl) ⟨1349285, by rfl⟩ : syracuseStep 1799047 = 2698571) B2698571
theorem B1799055 : Blo 1798100 1799055 := bstep (se 1 (by rfl) ⟨1349291, by rfl⟩ : syracuseStep 1799055 = 2698583) B2698583
theorem B3036089 : Blo 1798100 3036089 := bstep (se 2 (by rfl) ⟨1138533, by rfl⟩ : syracuseStep 3036089 = 2277067) B2277067
theorem B1799099 : Blo 1798100 1799099 := bstep (se 1 (by rfl) ⟨1349324, by rfl⟩ : syracuseStep 1799099 = 2698649) B2698649
theorem B1799175 : Blo 1798100 1799175 := bstep (se 1 (by rfl) ⟨1349381, by rfl⟩ : syracuseStep 1799175 = 2698763) B2698763
theorem B1799183 : Blo 1798100 1799183 := bstep (se 1 (by rfl) ⟨1349387, by rfl⟩ : syracuseStep 1799183 = 2698775) B2698775
theorem B1799227 : Blo 1798100 1799227 := bstep (se 1 (by rfl) ⟨1349420, by rfl⟩ : syracuseStep 1799227 = 2698841) B2698841
theorem B4551815 : Blo 1798100 4551815 := bstep (se 1 (by rfl) ⟨3413861, by rfl⟩ : syracuseStep 4551815 = 6827723) B6827723
theorem B1799303 : Blo 1798100 1799303 := bstep (se 1 (by rfl) ⟨1349477, by rfl⟩ : syracuseStep 1799303 = 2698955) B2698955
theorem B1799311 : Blo 1798100 1799311 := bstep (se 1 (by rfl) ⟨1349483, by rfl⟩ : syracuseStep 1799311 = 2698967) B2698967
theorem B1799355 : Blo 1798100 1799355 := bstep (se 1 (by rfl) ⟨1349516, by rfl⟩ : syracuseStep 1799355 = 2699033) B2699033
theorem B1799431 : Blo 1798100 1799431 := bstep (se 1 (by rfl) ⟨1349573, by rfl⟩ : syracuseStep 1799431 = 2699147) B2699147
theorem B4551947 : Blo 1798100 4551947 := bstep (se 1 (by rfl) ⟨3413960, by rfl⟩ : syracuseStep 4551947 = 6827921) B6827921
theorem B1799439 : Blo 1798100 1799439 := bstep (se 1 (by rfl) ⟨1349579, by rfl⟩ : syracuseStep 1799439 = 2699159) B2699159
theorem B1799483 : Blo 1798100 1799483 := bstep (se 1 (by rfl) ⟨1349612, by rfl⟩ : syracuseStep 1799483 = 2699225) B2699225
theorem B5125463 : Blo 1798100 5125463 := bstep (se 1 (by rfl) ⟨3844097, by rfl⟩ : syracuseStep 5125463 = 7688195) B7688195
theorem B1799559 : Blo 1798100 1799559 := bstep (se 1 (by rfl) ⟨1349669, by rfl⟩ : syracuseStep 1799559 = 2699339) B2699339
theorem B1799567 : Blo 1798100 1799567 := bstep (se 1 (by rfl) ⟨1349675, by rfl⟩ : syracuseStep 1799567 = 2699351) B2699351
theorem B31167929 : Blo 1798100 31167929 := bstep (se 2 (by rfl) ⟨11687973, by rfl⟩ : syracuseStep 31167929 = 23375947) B23375947
theorem B1799611 : Blo 1798100 1799611 := bstep (se 1 (by rfl) ⟨1349708, by rfl⟩ : syracuseStep 1799611 = 2699417) B2699417
theorem B1799687 : Blo 1798100 1799687 := bstep (se 1 (by rfl) ⟨1349765, by rfl⟩ : syracuseStep 1799687 = 2699531) B2699531
theorem B1799695 : Blo 1798100 1799695 := bstep (se 1 (by rfl) ⟨1349771, by rfl⟩ : syracuseStep 1799695 = 2699543) B2699543
theorem B4863521 : Blo 1798100 4863521 := bstep (se 2 (by rfl) ⟨1823820, by rfl⟩ : syracuseStep 4863521 = 3647641) B3647641
theorem B1799739 : Blo 1798100 1799739 := bstep (se 1 (by rfl) ⟨1349804, by rfl⟩ : syracuseStep 1799739 = 2699609) B2699609
theorem B3036791 : Blo 1798100 3036791 := bstep (se 1 (by rfl) ⟨2277593, by rfl⟩ : syracuseStep 3036791 = 4555187) B4555187
theorem B1799815 : Blo 1798100 1799815 := bstep (se 1 (by rfl) ⟨1349861, by rfl⟩ : syracuseStep 1799815 = 2699723) B2699723
theorem B1799823 : Blo 1798100 1799823 := bstep (se 1 (by rfl) ⟨1349867, by rfl⟩ : syracuseStep 1799823 = 2699735) B2699735
theorem B1799867 : Blo 1798100 1799867 := bstep (se 1 (by rfl) ⟨1349900, by rfl⟩ : syracuseStep 1799867 = 2699801) B2699801
theorem B17282753 : Blo 1798100 17282753 := bstep (se 2 (by rfl) ⟨6481032, by rfl⟩ : syracuseStep 17282753 = 12962065) B12962065
theorem B1799943 : Blo 1798100 1799943 := bstep (se 1 (by rfl) ⟨1349957, by rfl⟩ : syracuseStep 1799943 = 2699915) B2699915
theorem B4552463 : Blo 1798100 4552463 := bstep (se 1 (by rfl) ⟨3414347, by rfl⟩ : syracuseStep 4552463 = 6828695) B6828695
theorem B1799951 : Blo 1798100 1799951 := bstep (se 1 (by rfl) ⟨1349963, by rfl⟩ : syracuseStep 1799951 = 2699927) B2699927
theorem B1799995 : Blo 1798100 1799995 := bstep (se 1 (by rfl) ⟨1349996, by rfl⟩ : syracuseStep 1799995 = 2699993) B2699993
theorem B9107315 : Blo 1798100 9107315 := bstep (se 1 (by rfl) ⟨6830486, by rfl⟩ : syracuseStep 9107315 = 13660973) B13660973
theorem B1800071 : Blo 1798100 1800071 := bstep (se 1 (by rfl) ⟨1350053, by rfl⟩ : syracuseStep 1800071 = 2700107) B2700107
theorem B1800079 : Blo 1798100 1800079 := bstep (se 1 (by rfl) ⟨1350059, by rfl⟩ : syracuseStep 1800079 = 2700119) B2700119
theorem B4552595 : Blo 1798100 4552595 := bstep (se 1 (by rfl) ⟨3414446, by rfl⟩ : syracuseStep 4552595 = 6828893) B6828893
theorem B2430967 : Blo 1798100 2430967 := bstep (se 1 (by rfl) ⟨1823225, by rfl⟩ : syracuseStep 2430967 = 3646451) B3646451
theorem B3414059 : Blo 1798100 3414059 := bstep (se 1 (by rfl) ⟨2560544, by rfl⟩ : syracuseStep 3414059 = 5121089) B5121089
theorem B7297067 : Blo 1798100 7297067 := bstep (se 1 (by rfl) ⟨5472800, by rfl⟩ : syracuseStep 7297067 = 10945601) B10945601
theorem B3037243 : Blo 1798100 3037243 := bstep (se 1 (by rfl) ⟨2277932, by rfl⟩ : syracuseStep 3037243 = 4555865) B4555865
theorem B24959177 : Blo 1798100 24959177 := bstep (se 2 (by rfl) ⟨9359691, by rfl⟩ : syracuseStep 24959177 = 18719383) B18719383
theorem B3037385 : Blo 1798100 3037385 := bstep (se 2 (by rfl) ⟨1139019, by rfl⟩ : syracuseStep 3037385 = 2278039) B2278039
theorem B5765377 : Blo 1798100 5765377 := bstep (se 2 (by rfl) ⟨2162016, by rfl⟩ : syracuseStep 5765377 = 4324033) B4324033
theorem B3414287 : Blo 1798100 3414287 := bstep (se 1 (by rfl) ⟨2560715, by rfl⟩ : syracuseStep 3414287 = 5121431) B5121431
theorem B6830351 : Blo 1798100 6830351 := bstep (se 1 (by rfl) ⟨5122763, by rfl⟩ : syracuseStep 6830351 = 10245527) B10245527
theorem B9615631 : Blo 1798100 9615631 := bstep (se 1 (by rfl) ⟨7211723, by rfl⟩ : syracuseStep 9615631 = 14423447) B14423447
theorem B10246459 : Blo 1798100 10246459 := bstep (se 1 (by rfl) ⟨7684844, by rfl⟩ : syracuseStep 10246459 = 15369689) B15369689
theorem B9107801 : Blo 1798100 9107801 := bstep (se 2 (by rfl) ⟨3415425, by rfl⟩ : syracuseStep 9107801 = 6830851) B6830851
theorem B4503923 : Blo 1798100 4503923 := bstep (se 1 (by rfl) ⟨3377942, by rfl⟩ : syracuseStep 4503923 = 6755885) B6755885
theorem B6068627 : Blo 1798100 6068627 := bstep (se 1 (by rfl) ⟨4551470, by rfl⟩ : syracuseStep 6068627 = 9102941) B9102941
theorem B2275771 : Blo 1798100 2275771 := bstep (se 1 (by rfl) ⟨1706828, by rfl⟩ : syracuseStep 2275771 = 3413657) B3413657
theorem B3840527 : Blo 1798100 3840527 := bstep (se 1 (by rfl) ⟨2880395, by rfl⟩ : syracuseStep 3840527 = 5760791) B5760791
theorem B5192207 : Blo 1798100 5192207 := bstep (se 1 (by rfl) ⟨3894155, by rfl⟩ : syracuseStep 5192207 = 7788311) B7788311
theorem B9230915 : Blo 1798100 9230915 := bstep (se 1 (by rfl) ⟨6923186, by rfl⟩ : syracuseStep 9230915 = 13846373) B13846373
theorem B8649335 : Blo 1798100 8649335 := bstep (se 1 (by rfl) ⟨6487001, by rfl⟩ : syracuseStep 8649335 = 12974003) B12974003
theorem B20495105 : Blo 1798100 20495105 := bstep (se 2 (by rfl) ⟨7685664, by rfl⟩ : syracuseStep 20495105 = 15371329) B15371329
theorem B36936485 : Blo 1798100 36936485 := bstep (se 4 (by rfl) ⟨3462795, by rfl⟩ : syracuseStep 36936485 = 6925591) B6925591
theorem B5192507 : Blo 1798100 5192507 := bstep (se 1 (by rfl) ⟨3894380, by rfl⟩ : syracuseStep 5192507 = 7788761) B7788761
theorem B2562959 : Blo 1798100 2562959 := bstep (se 1 (by rfl) ⟨1922219, by rfl⟩ : syracuseStep 2562959 = 3844439) B3844439
theorem B4045769 : Blo 1798100 4045769 := bstep (se 2 (by rfl) ⟨1517163, by rfl⟩ : syracuseStep 4045769 = 3034327) B3034327
theorem B4864969 : Blo 1798100 4864969 := bstep (se 2 (by rfl) ⟨1824363, by rfl⟩ : syracuseStep 4864969 = 3648727) B3648727
theorem B4553729 : Blo 1798100 4553729 := bstep (se 2 (by rfl) ⟨1707648, by rfl⟩ : syracuseStep 4553729 = 3415297) B3415297
theorem B5471243 : Blo 1798100 5471243 := bstep (se 1 (by rfl) ⟨4103432, by rfl⟩ : syracuseStep 5471243 = 8206865) B8206865
theorem B8428573 : Blo 1798100 8428573 := bstep (se 3 (by rfl) ⟨1580357, by rfl⟩ : syracuseStep 8428573 = 3160715) B3160715
theorem B15367229 : Blo 1798100 15367229 := bstep (se 3 (by rfl) ⟨2881355, by rfl⟩ : syracuseStep 15367229 = 5762711) B5762711
theorem B4865143 : Blo 1798100 4865143 := bstep (se 1 (by rfl) ⟨3648857, by rfl⟩ : syracuseStep 4865143 = 7297715) B7297715
theorem B4554103 : Blo 1798100 4554103 := bstep (se 1 (by rfl) ⟨3415577, by rfl⟩ : syracuseStep 4554103 = 6831155) B6831155
theorem B3841415 : Blo 1798100 3841415 := bstep (se 1 (by rfl) ⟨2881061, by rfl⟩ : syracuseStep 3841415 = 5762123) B5762123
theorem B2276743 : Blo 1798100 2276743 := bstep (se 1 (by rfl) ⟨1707557, by rfl⟩ : syracuseStep 2276743 = 3415115) B3415115
theorem B19447249 : Blo 1798100 19447249 := bstep (se 2 (by rfl) ⟨7292718, by rfl⟩ : syracuseStep 19447249 = 14585437) B14585437
theorem B13147651 : Blo 1798100 13147651 := bstep (se 1 (by rfl) ⟨9860738, by rfl⟩ : syracuseStep 13147651 = 19721477) B19721477
theorem B4931131 : Blo 1798100 4931131 := bstep (se 1 (by rfl) ⟨3698348, by rfl⟩ : syracuseStep 4931131 = 7396697) B7396697
theorem B4865597 : Blo 1798100 4865597 := bstep (se 3 (by rfl) ⟨912299, by rfl⟩ : syracuseStep 4865597 = 1824599) B1824599
theorem B12967543 : Blo 1798100 12967543 := bstep (se 1 (by rfl) ⟨9725657, by rfl⟩ : syracuseStep 12967543 = 19451315) B19451315
theorem B4046471 : Blo 1798100 4046471 := bstep (se 1 (by rfl) ⟨3034853, by rfl⟩ : syracuseStep 4046471 = 6069707) B6069707
theorem B3415699 : Blo 1798100 3415699 := bstep (se 1 (by rfl) ⟨2561774, by rfl⟩ : syracuseStep 3415699 = 5123549) B5123549
theorem B32841395 : Blo 1798100 32841395 := bstep (se 1 (by rfl) ⟨24631046, by rfl⟩ : syracuseStep 32841395 = 49262093) B49262093
theorem B7683821 : Blo 1798100 7683821 := bstep (se 3 (by rfl) ⟨1440716, by rfl⟩ : syracuseStep 7683821 = 2881433) B2881433
theorem B10247917 : Blo 1798100 10247917 := bstep (se 3 (by rfl) ⟨1921484, by rfl⟩ : syracuseStep 10247917 = 3842969) B3842969
theorem B4439819 : Blo 1798100 4439819 := bstep (se 1 (by rfl) ⟨3329864, by rfl⟩ : syracuseStep 4439819 = 6659729) B6659729
theorem B18456335 : Blo 1798100 18456335 := bstep (se 1 (by rfl) ⟨13842251, by rfl⟩ : syracuseStep 18456335 = 27684503) B27684503
theorem B6070031 : Blo 1798100 6070031 := bstep (se 1 (by rfl) ⟨4552523, by rfl⟩ : syracuseStep 6070031 = 9105047) B9105047
theorem B3841825 : Blo 1798100 3841825 := bstep (se 2 (by rfl) ⟨1440684, by rfl⟩ : syracuseStep 3841825 = 2881369) B2881369
theorem B2277163 : Blo 1798100 2277163 := bstep (se 1 (by rfl) ⟨1707872, by rfl⟩ : syracuseStep 2277163 = 3415745) B3415745
theorem B4554539 : Blo 1798100 4554539 := bstep (se 1 (by rfl) ⟨3415904, by rfl⟩ : syracuseStep 4554539 = 6831809) B6831809
theorem B4046651 : Blo 1798100 4046651 := bstep (se 1 (by rfl) ⟨3034988, by rfl⟩ : syracuseStep 4046651 = 6069977) B6069977
theorem B3415927 : Blo 1798100 3415927 := bstep (se 1 (by rfl) ⟨2561945, by rfl⟩ : syracuseStep 3415927 = 5123891) B5123891
theorem B2023303 : Blo 1798100 2023303 := bstep (se 1 (by rfl) ⟨1517477, by rfl⟩ : syracuseStep 2023303 = 3034955) B3034955
theorem B4046777 : Blo 1798100 4046777 := bstep (se 2 (by rfl) ⟨1517541, by rfl⟩ : syracuseStep 4046777 = 3035083) B3035083
theorem B4046867 : Blo 1798100 4046867 := bstep (se 1 (by rfl) ⟨3035150, by rfl⟩ : syracuseStep 4046867 = 6070301) B6070301
theorem B20496563 : Blo 1798100 20496563 := bstep (se 1 (by rfl) ⟨15372422, by rfl⟩ : syracuseStep 20496563 = 30744845) B30744845
theorem B4047209 : Blo 1798100 4047209 := bstep (se 2 (by rfl) ⟨1517703, by rfl⟩ : syracuseStep 4047209 = 3035407) B3035407
theorem B12820841 : Blo 1798100 12820841 := bstep (se 2 (by rfl) ⟨4807815, by rfl⟩ : syracuseStep 12820841 = 9615631) B9615631
theorem B2597303 : Blo 1798100 2597303 := bstep (se 1 (by rfl) ⟨1947977, by rfl⟩ : syracuseStep 2597303 = 3895955) B3895955
theorem B13656599 : Blo 1798100 13656599 := bstep (se 1 (by rfl) ⟨10242449, by rfl⟩ : syracuseStep 13656599 = 20484899) B20484899
theorem B2024059 : Blo 1798100 2024059 := bstep (se 1 (by rfl) ⟨1518044, by rfl⟩ : syracuseStep 2024059 = 3036089) B3036089
theorem B11526857 : Blo 1798100 11526857 := bstep (se 2 (by rfl) ⟨4322571, by rfl⟩ : syracuseStep 11526857 = 8645143) B8645143
theorem B3416975 : Blo 1798100 3416975 := bstep (se 1 (by rfl) ⟨2562731, by rfl⟩ : syracuseStep 3416975 = 5125463) B5125463
theorem B14582711 : Blo 1798100 14582711 := bstep (se 1 (by rfl) ⟨10937033, by rfl⟩ : syracuseStep 14582711 = 21874067) B21874067
theorem B4555703 : Blo 1798100 4555703 := bstep (se 1 (by rfl) ⟨3416777, by rfl⟩ : syracuseStep 4555703 = 6833555) B6833555
theorem B4047803 : Blo 1798100 4047803 := bstep (se 1 (by rfl) ⟨3035852, by rfl⟩ : syracuseStep 4047803 = 6071705) B6071705
theorem B4047929 : Blo 1798100 4047929 := bstep (se 2 (by rfl) ⟨1517973, by rfl⟩ : syracuseStep 4047929 = 3035947) B3035947
theorem B13665347 : Blo 1798100 13665347 := bstep (se 1 (by rfl) ⟨10249010, by rfl⟩ : syracuseStep 13665347 = 20498021) B20498021
theorem B2024527 : Blo 1798100 2024527 := bstep (se 1 (by rfl) ⟨1518395, by rfl⟩ : syracuseStep 2024527 = 3036791) B3036791
theorem B6833267 : Blo 1798100 6833267 := bstep (se 1 (by rfl) ⟨5124950, by rfl⟩ : syracuseStep 6833267 = 10249901) B10249901
theorem B6071543 : Blo 1798100 6071543 := bstep (se 1 (by rfl) ⟨4553657, by rfl⟩ : syracuseStep 6071543 = 9107315) B9107315
theorem B12969305 : Blo 1798100 12969305 := bstep (se 2 (by rfl) ⟨4863489, by rfl⟩ : syracuseStep 12969305 = 9726979) B9726979
theorem B4048271 : Blo 1798100 4048271 := bstep (se 1 (by rfl) ⟨3036203, by rfl⟩ : syracuseStep 4048271 = 6072407) B6072407
theorem B12969389 : Blo 1798100 12969389 := bstep (se 3 (by rfl) ⟨2431760, by rfl⟩ : syracuseStep 12969389 = 4863521) B4863521
theorem B16639451 : Blo 1798100 16639451 := bstep (se 1 (by rfl) ⟨12479588, by rfl⟩ : syracuseStep 16639451 = 24959177) B24959177
theorem B2024923 : Blo 1798100 2024923 := bstep (se 1 (by rfl) ⟨1518692, by rfl⟩ : syracuseStep 2024923 = 3037385) B3037385
theorem B6071867 : Blo 1798100 6071867 := bstep (se 1 (by rfl) ⟨4553900, by rfl⟩ : syracuseStep 6071867 = 9107801) B9107801
theorem B4048595 : Blo 1798100 4048595 := bstep (se 1 (by rfl) ⟨3036446, by rfl⟩ : syracuseStep 4048595 = 6072893) B6072893
theorem B6153943 : Blo 1798100 6153943 := bstep (se 1 (by rfl) ⟨4615457, by rfl⟩ : syracuseStep 6153943 = 9230915) B9230915
theorem B8210219 : Blo 1798100 8210219 := bstep (se 1 (by rfl) ⟨6157664, by rfl⟩ : syracuseStep 8210219 = 12315329) B12315329
theorem B6072137 : Blo 1798100 6072137 := bstep (se 2 (by rfl) ⟨2277051, by rfl⟩ : syracuseStep 6072137 = 4554103) B4554103
theorem B9103265 : Blo 1798100 9103265 := bstep (se 2 (by rfl) ⟨3413724, by rfl⟩ : syracuseStep 9103265 = 6827449) B6827449
theorem B25929665 : Blo 1798100 25929665 := bstep (se 2 (by rfl) ⟨9723624, by rfl⟩ : syracuseStep 25929665 = 19447249) B19447249
theorem B2697179 : Blo 1798100 2697179 := bstep (se 1 (by rfl) ⟨2022884, by rfl⟩ : syracuseStep 2697179 = 4045769) B4045769
theorem B3647495 : Blo 1798100 3647495 := bstep (se 1 (by rfl) ⟨2735621, by rfl⟩ : syracuseStep 3647495 = 5471243) B5471243
theorem B13666319 : Blo 1798100 13666319 := bstep (se 1 (by rfl) ⟨10249739, by rfl⟩ : syracuseStep 13666319 = 20499479) B20499479
theorem B11839517 : Blo 1798100 11839517 := bstep (se 3 (by rfl) ⟨2219909, by rfl⟩ : syracuseStep 11839517 = 4439819) B4439819
theorem B10242085 : Blo 1798100 10242085 := bstep (se 4 (by rfl) ⟨960195, by rfl⟩ : syracuseStep 10242085 = 1920391) B1920391
theorem B6834557 : Blo 1798100 6834557 := bstep (se 3 (by rfl) ⟨1281479, by rfl⟩ : syracuseStep 6834557 = 2562959) B2562959
theorem B5122433 : Blo 1798100 5122433 := bstep (se 2 (by rfl) ⟨1920912, by rfl⟩ : syracuseStep 5122433 = 3841825) B3841825
theorem B2697647 : Blo 1798100 2697647 := bstep (se 1 (by rfl) ⟨2023235, by rfl⟩ : syracuseStep 2697647 = 4046471) B4046471
theorem B87525845 : Blo 1798100 87525845 := bstep (se 7 (by rfl) ⟨1025693, by rfl⟩ : syracuseStep 87525845 = 2051387) B2051387
theorem B5122547 : Blo 1798100 5122547 := bstep (se 1 (by rfl) ⟨3841910, by rfl⟩ : syracuseStep 5122547 = 7683821) B7683821
theorem B2697737 : Blo 1798100 2697737 := bstep (se 2 (by rfl) ⟨1011651, by rfl⟩ : syracuseStep 2697737 = 2023303) B2023303
theorem B2697767 : Blo 1798100 2697767 := bstep (se 1 (by rfl) ⟨2023325, by rfl⟩ : syracuseStep 2697767 = 4046651) B4046651
theorem B2697851 : Blo 1798100 2697851 := bstep (se 1 (by rfl) ⟨2023388, by rfl⟩ : syracuseStep 2697851 = 4046777) B4046777
theorem B4049531 : Blo 1798100 4049531 := bstep (se 1 (by rfl) ⟨3037148, by rfl⟩ : syracuseStep 4049531 = 6074297) B6074297
theorem B2697977 : Blo 1798100 2697977 := bstep (se 2 (by rfl) ⟨1011741, by rfl⟩ : syracuseStep 2697977 = 2023483) B2023483
theorem B4049657 : Blo 1798100 4049657 := bstep (se 2 (by rfl) ⟨1518621, by rfl⟩ : syracuseStep 4049657 = 3037243) B3037243
theorem B5122889 : Blo 1798100 5122889 := bstep (se 2 (by rfl) ⟨1921083, by rfl⟩ : syracuseStep 5122889 = 3842167) B3842167
theorem B2698079 : Blo 1798100 2698079 := bstep (se 1 (by rfl) ⟨2023559, by rfl⟩ : syracuseStep 2698079 = 4047119) B4047119
theorem B2698091 : Blo 1798100 2698091 := bstep (se 1 (by rfl) ⟨2023568, by rfl⟩ : syracuseStep 2698091 = 4047137) B4047137
theorem B6073271 : Blo 1798100 6073271 := bstep (se 1 (by rfl) ⟨4554953, by rfl⟩ : syracuseStep 6073271 = 9109907) B9109907
theorem B6925313 : Blo 1798100 6925313 := bstep (se 2 (by rfl) ⟨2596992, by rfl⟩ : syracuseStep 6925313 = 5193985) B5193985
theorem B7687169 : Blo 1798100 7687169 := bstep (se 2 (by rfl) ⟨2882688, by rfl⟩ : syracuseStep 7687169 = 5765377) B5765377
theorem B4049927 : Blo 1798100 4049927 := bstep (se 1 (by rfl) ⟨3037445, by rfl⟩ : syracuseStep 4049927 = 6074891) B6074891
theorem B49220621 : Blo 1798100 49220621 := bstep (se 3 (by rfl) ⟨9228866, by rfl⟩ : syracuseStep 49220621 = 18457733) B18457733
theorem B49228823 : Blo 1798100 49228823 := bstep (se 1 (by rfl) ⟨36921617, by rfl⟩ : syracuseStep 49228823 = 73843235) B73843235
theorem B2698319 : Blo 1798100 2698319 := bstep (se 1 (by rfl) ⟨2023739, by rfl⟩ : syracuseStep 2698319 = 4047479) B4047479
theorem B4049999 : Blo 1798100 4049999 := bstep (se 1 (by rfl) ⟨3037499, by rfl⟩ : syracuseStep 4049999 = 6074999) B6074999
theorem B12962987 : Blo 1798100 12962987 := bstep (se 1 (by rfl) ⟨9722240, by rfl⟩ : syracuseStep 12962987 = 19444481) B19444481
theorem B38890691 : Blo 1798100 38890691 := bstep (se 1 (by rfl) ⟨29168018, by rfl⟩ : syracuseStep 38890691 = 58336037) B58336037
theorem B2919623 : Blo 1798100 2919623 := bstep (se 1 (by rfl) ⟨2189717, by rfl⟩ : syracuseStep 2919623 = 4379435) B4379435
theorem B2698439 : Blo 1798100 2698439 := bstep (se 1 (by rfl) ⟨2023829, by rfl⟩ : syracuseStep 2698439 = 4047659) B4047659
theorem B9112823 : Blo 1798100 9112823 := bstep (se 1 (by rfl) ⟨6834617, by rfl⟩ : syracuseStep 9112823 = 13669235) B13669235
theorem B3034361 : Blo 1798100 3034361 := bstep (se 2 (by rfl) ⟨1137885, by rfl⟩ : syracuseStep 3034361 = 2275771) B2275771
theorem B2698601 : Blo 1798100 2698601 := bstep (se 2 (by rfl) ⟨1011975, by rfl⟩ : syracuseStep 2698601 = 2023951) B2023951
theorem B4320641 : Blo 1798100 4320641 := bstep (se 2 (by rfl) ⟨1620240, by rfl⟩ : syracuseStep 4320641 = 3240481) B3240481
theorem B3034543 : Blo 1798100 3034543 := bstep (se 1 (by rfl) ⟨2275907, by rfl⟩ : syracuseStep 3034543 = 4551815) B4551815
theorem B2698679 : Blo 1798100 2698679 := bstep (se 1 (by rfl) ⟨2024009, by rfl⟩ : syracuseStep 2698679 = 4048019) B4048019
theorem B14790089 : Blo 1798100 14790089 := bstep (se 2 (by rfl) ⟨5546283, by rfl⟩ : syracuseStep 14790089 = 11092567) B11092567
theorem B2698715 : Blo 1798100 2698715 := bstep (se 1 (by rfl) ⟨2024036, by rfl⟩ : syracuseStep 2698715 = 4048073) B4048073
theorem B3034631 : Blo 1798100 3034631 := bstep (se 1 (by rfl) ⟨2275973, by rfl⟩ : syracuseStep 3034631 = 4551947) B4551947
theorem B6073865 : Blo 1798100 6073865 := bstep (se 2 (by rfl) ⟨2277699, by rfl⟩ : syracuseStep 6073865 = 4555399) B4555399
theorem B20778619 : Blo 1798100 20778619 := bstep (se 1 (by rfl) ⟨15583964, by rfl⟩ : syracuseStep 20778619 = 31167929) B31167929
theorem B11521835 : Blo 1798100 11521835 := bstep (se 1 (by rfl) ⟨8641376, by rfl⟩ : syracuseStep 11521835 = 17282753) B17282753
theorem B3034975 : Blo 1798100 3034975 := bstep (se 1 (by rfl) ⟨2276231, by rfl⟩ : syracuseStep 3034975 = 4552463) B4552463
theorem B2699183 : Blo 1798100 2699183 := bstep (se 1 (by rfl) ⟨2024387, by rfl⟩ : syracuseStep 2699183 = 4048775) B4048775
theorem B3035063 : Blo 1798100 3035063 := bstep (se 1 (by rfl) ⟨2276297, by rfl⟩ : syracuseStep 3035063 = 4552595) B4552595
theorem B1798107 : Blo 1798100 1798107 := bstep (se 1 (by rfl) ⟨1348580, by rfl⟩ : syracuseStep 1798107 = 2697161) B2697161
theorem B2699273 : Blo 1798100 2699273 := bstep (se 2 (by rfl) ⟨1012227, by rfl⟩ : syracuseStep 2699273 = 2024455) B2024455
theorem B1798183 : Blo 1798100 1798183 := bstep (se 1 (by rfl) ⟨1348637, by rfl⟩ : syracuseStep 1798183 = 2697275) B2697275
theorem B2699303 : Blo 1798100 2699303 := bstep (se 1 (by rfl) ⟨2024477, by rfl⟩ : syracuseStep 2699303 = 4048955) B4048955
theorem B1798223 : Blo 1798100 1798223 := bstep (se 1 (by rfl) ⟨1348667, by rfl⟩ : syracuseStep 1798223 = 2697335) B2697335
theorem B1798239 : Blo 1798100 1798239 := bstep (se 1 (by rfl) ⟨1348679, by rfl⟩ : syracuseStep 1798239 = 2697359) B2697359
theorem B1798267 : Blo 1798100 1798267 := bstep (se 1 (by rfl) ⟨1348700, by rfl⟩ : syracuseStep 1798267 = 2697401) B2697401
theorem B2699387 : Blo 1798100 2699387 := bstep (se 1 (by rfl) ⟨2024540, by rfl⟩ : syracuseStep 2699387 = 4049081) B4049081
theorem B1798319 : Blo 1798100 1798319 := bstep (se 1 (by rfl) ⟨1348739, by rfl⟩ : syracuseStep 1798319 = 2697479) B2697479
theorem B1798343 : Blo 1798100 1798343 := bstep (se 1 (by rfl) ⟨1348757, by rfl⟩ : syracuseStep 1798343 = 2697515) B2697515
theorem B1798363 : Blo 1798100 1798363 := bstep (se 1 (by rfl) ⟨1348772, by rfl⟩ : syracuseStep 1798363 = 2697545) B2697545
theorem B3002615 : Blo 1798100 3002615 := bstep (se 1 (by rfl) ⟨2251961, by rfl⟩ : syracuseStep 3002615 = 4503923) B4503923
theorem B2699513 : Blo 1798100 2699513 := bstep (se 2 (by rfl) ⟨1012317, by rfl⟩ : syracuseStep 2699513 = 2024635) B2024635
theorem B1798439 : Blo 1798100 1798439 := bstep (se 1 (by rfl) ⟨1348829, by rfl⟩ : syracuseStep 1798439 = 2697659) B2697659
theorem B1798479 : Blo 1798100 1798479 := bstep (se 1 (by rfl) ⟨1348859, by rfl⟩ : syracuseStep 1798479 = 2697719) B2697719
theorem B2560351 : Blo 1798100 2560351 := bstep (se 1 (by rfl) ⟨1920263, by rfl⟩ : syracuseStep 2560351 = 3840527) B3840527
theorem B1798495 : Blo 1798100 1798495 := bstep (se 1 (by rfl) ⟨1348871, by rfl⟩ : syracuseStep 1798495 = 2697743) B2697743
theorem B3461471 : Blo 1798100 3461471 := bstep (se 1 (by rfl) ⟨2596103, by rfl⟩ : syracuseStep 3461471 = 5192207) B5192207
theorem B2699615 : Blo 1798100 2699615 := bstep (se 1 (by rfl) ⟨2024711, by rfl⟩ : syracuseStep 2699615 = 4049423) B4049423
theorem B6074729 : Blo 1798100 6074729 := bstep (se 2 (by rfl) ⟨2278023, by rfl⟩ : syracuseStep 6074729 = 4556047) B4556047
theorem B2699627 : Blo 1798100 2699627 := bstep (se 1 (by rfl) ⟨2024720, by rfl⟩ : syracuseStep 2699627 = 4049441) B4049441
theorem B1798523 : Blo 1798100 1798523 := bstep (se 1 (by rfl) ⟨1348892, by rfl⟩ : syracuseStep 1798523 = 2697785) B2697785
theorem B1798575 : Blo 1798100 1798575 := bstep (se 1 (by rfl) ⟨1348931, by rfl⟩ : syracuseStep 1798575 = 2697863) B2697863
theorem B3076535 : Blo 1798100 3076535 := bstep (se 1 (by rfl) ⟨2307401, by rfl⟩ : syracuseStep 3076535 = 4614803) B4614803
theorem B1798599 : Blo 1798100 1798599 := bstep (se 1 (by rfl) ⟨1348949, by rfl⟩ : syracuseStep 1798599 = 2697899) B2697899
theorem B1798619 : Blo 1798100 1798619 := bstep (se 1 (by rfl) ⟨1348964, by rfl⟩ : syracuseStep 1798619 = 2697929) B2697929
theorem B3035657 : Blo 1798100 3035657 := bstep (se 2 (by rfl) ⟨1138371, by rfl⟩ : syracuseStep 3035657 = 2276743) B2276743
theorem B3461671 : Blo 1798100 3461671 := bstep (se 1 (by rfl) ⟨2596253, by rfl⟩ : syracuseStep 3461671 = 5192507) B5192507
theorem B1798695 : Blo 1798100 1798695 := bstep (se 1 (by rfl) ⟨1349021, by rfl⟩ : syracuseStep 1798695 = 2698043) B2698043
theorem B1798735 : Blo 1798100 1798735 := bstep (se 1 (by rfl) ⟨1349051, by rfl⟩ : syracuseStep 1798735 = 2698103) B2698103
theorem B2699855 : Blo 1798100 2699855 := bstep (se 1 (by rfl) ⟨2024891, by rfl⟩ : syracuseStep 2699855 = 4049783) B4049783
theorem B1798751 : Blo 1798100 1798751 := bstep (se 1 (by rfl) ⟨1349063, by rfl⟩ : syracuseStep 1798751 = 2698127) B2698127
theorem B1798779 : Blo 1798100 1798779 := bstep (se 1 (by rfl) ⟨1349084, by rfl⟩ : syracuseStep 1798779 = 2698169) B2698169
theorem B3035819 : Blo 1798100 3035819 := bstep (se 1 (by rfl) ⟨2276864, by rfl⟩ : syracuseStep 3035819 = 4553729) B4553729
theorem B1798831 : Blo 1798100 1798831 := bstep (se 1 (by rfl) ⟨1349123, by rfl⟩ : syracuseStep 1798831 = 2698247) B2698247
theorem B1798855 : Blo 1798100 1798855 := bstep (se 1 (by rfl) ⟨1349141, by rfl⟩ : syracuseStep 1798855 = 2698283) B2698283
theorem B2699975 : Blo 1798100 2699975 := bstep (se 1 (by rfl) ⟨2024981, by rfl⟩ : syracuseStep 2699975 = 4049963) B4049963
theorem B10244819 : Blo 1798100 10244819 := bstep (se 1 (by rfl) ⟨7683614, by rfl⟩ : syracuseStep 10244819 = 15367229) B15367229
theorem B1798875 : Blo 1798100 1798875 := bstep (se 1 (by rfl) ⟨1349156, by rfl⟩ : syracuseStep 1798875 = 2698313) B2698313
theorem B6574841 : Blo 1798100 6574841 := bstep (se 2 (by rfl) ⟨2465565, by rfl⟩ : syracuseStep 6574841 = 4931131) B4931131
theorem B1798951 : Blo 1798100 1798951 := bstep (se 1 (by rfl) ⟨1349213, by rfl⟩ : syracuseStep 1798951 = 2698427) B2698427
theorem B17290057 : Blo 1798100 17290057 := bstep (se 2 (by rfl) ⟨6483771, by rfl⟩ : syracuseStep 17290057 = 12967543) B12967543
theorem B1798991 : Blo 1798100 1798991 := bstep (se 1 (by rfl) ⟨1349243, by rfl⟩ : syracuseStep 1798991 = 2698487) B2698487
theorem B1799007 : Blo 1798100 1799007 := bstep (se 1 (by rfl) ⟨1349255, by rfl⟩ : syracuseStep 1799007 = 2698511) B2698511
theorem B2700137 : Blo 1798100 2700137 := bstep (se 2 (by rfl) ⟨1012551, by rfl⟩ : syracuseStep 2700137 = 2025103) B2025103
theorem B6828907 : Blo 1798100 6828907 := bstep (se 1 (by rfl) ⟨5121680, by rfl⟩ : syracuseStep 6828907 = 10243361) B10243361
theorem B1799035 : Blo 1798100 1799035 := bstep (se 1 (by rfl) ⟨1349276, by rfl⟩ : syracuseStep 1799035 = 2698553) B2698553
theorem B2560943 : Blo 1798100 2560943 := bstep (se 1 (by rfl) ⟨1920707, by rfl⟩ : syracuseStep 2560943 = 3841415) B3841415
theorem B1799087 : Blo 1798100 1799087 := bstep (se 1 (by rfl) ⟨1349315, by rfl⟩ : syracuseStep 1799087 = 2698631) B2698631
theorem B6075323 : Blo 1798100 6075323 := bstep (se 1 (by rfl) ⟨4556492, by rfl⟩ : syracuseStep 6075323 = 9112985) B9112985
theorem B1799111 : Blo 1798100 1799111 := bstep (se 1 (by rfl) ⟨1349333, by rfl⟩ : syracuseStep 1799111 = 2698667) B2698667
theorem B1799131 : Blo 1798100 1799131 := bstep (se 1 (by rfl) ⟨1349348, by rfl⟩ : syracuseStep 1799131 = 2698697) B2698697
theorem B55383041 : Blo 1798100 55383041 := bstep (se 2 (by rfl) ⟨20768640, by rfl⟩ : syracuseStep 55383041 = 41537281) B41537281
theorem B15373313 : Blo 1798100 15373313 := bstep (se 2 (by rfl) ⟨5764992, by rfl⟩ : syracuseStep 15373313 = 11529985) B11529985
theorem B1799207 : Blo 1798100 1799207 := bstep (se 1 (by rfl) ⟨1349405, by rfl⟩ : syracuseStep 1799207 = 2698811) B2698811
theorem B3036217 : Blo 1798100 3036217 := bstep (se 2 (by rfl) ⟨1138581, by rfl⟩ : syracuseStep 3036217 = 2277163) B2277163
theorem B1799247 : Blo 1798100 1799247 := bstep (se 1 (by rfl) ⟨1349435, by rfl⟩ : syracuseStep 1799247 = 2698871) B2698871
theorem B1799263 : Blo 1798100 1799263 := bstep (se 1 (by rfl) ⟨1349447, by rfl⟩ : syracuseStep 1799263 = 2698895) B2698895
theorem B21894263 : Blo 1798100 21894263 := bstep (se 1 (by rfl) ⟨16420697, by rfl⟩ : syracuseStep 21894263 = 32841395) B32841395
theorem B1799291 : Blo 1798100 1799291 := bstep (se 1 (by rfl) ⟨1349468, by rfl⟩ : syracuseStep 1799291 = 2698937) B2698937
theorem B1799343 : Blo 1798100 1799343 := bstep (se 1 (by rfl) ⟨1349507, by rfl⟩ : syracuseStep 1799343 = 2699015) B2699015
theorem B3036359 : Blo 1798100 3036359 := bstep (se 1 (by rfl) ⟨2277269, by rfl⟩ : syracuseStep 3036359 = 4554539) B4554539
theorem B1799367 : Blo 1798100 1799367 := bstep (se 1 (by rfl) ⟨1349525, by rfl⟩ : syracuseStep 1799367 = 2699051) B2699051
theorem B1799387 : Blo 1798100 1799387 := bstep (se 1 (by rfl) ⟨1349540, by rfl⟩ : syracuseStep 1799387 = 2699081) B2699081
theorem B1799463 : Blo 1798100 1799463 := bstep (se 1 (by rfl) ⟨1349597, by rfl⟩ : syracuseStep 1799463 = 2699195) B2699195
theorem B3241289 : Blo 1798100 3241289 := bstep (se 2 (by rfl) ⟨1215483, by rfl⟩ : syracuseStep 3241289 = 2430967) B2430967
theorem B1799503 : Blo 1798100 1799503 := bstep (se 1 (by rfl) ⟨1349627, by rfl⟩ : syracuseStep 1799503 = 2699255) B2699255
theorem B1799519 : Blo 1798100 1799519 := bstep (se 1 (by rfl) ⟨1349639, by rfl⟩ : syracuseStep 1799519 = 2699279) B2699279
theorem B3036521 : Blo 1798100 3036521 := bstep (se 2 (by rfl) ⟨1138695, by rfl⟩ : syracuseStep 3036521 = 2277391) B2277391
theorem B2561387 : Blo 1798100 2561387 := bstep (se 1 (by rfl) ⟨1921040, by rfl⟩ : syracuseStep 2561387 = 3842081) B3842081
theorem B1799547 : Blo 1798100 1799547 := bstep (se 1 (by rfl) ⟨1349660, by rfl⟩ : syracuseStep 1799547 = 2699321) B2699321
theorem B1799599 : Blo 1798100 1799599 := bstep (se 1 (by rfl) ⟨1349699, by rfl⟩ : syracuseStep 1799599 = 2699399) B2699399
theorem B2921915 : Blo 1798100 2921915 := bstep (se 1 (by rfl) ⟨2191436, by rfl⟩ : syracuseStep 2921915 = 4382873) B4382873
theorem B1799623 : Blo 1798100 1799623 := bstep (se 1 (by rfl) ⟨1349717, by rfl⟩ : syracuseStep 1799623 = 2699435) B2699435
theorem B1799643 : Blo 1798100 1799643 := bstep (se 1 (by rfl) ⟨1349732, by rfl⟩ : syracuseStep 1799643 = 2699465) B2699465
theorem B4322803 : Blo 1798100 4322803 := bstep (se 1 (by rfl) ⟨3242102, by rfl⟩ : syracuseStep 4322803 = 6484205) B6484205
theorem B1799719 : Blo 1798100 1799719 := bstep (se 1 (by rfl) ⟨1349789, by rfl⟩ : syracuseStep 1799719 = 2699579) B2699579
theorem B25933355 : Blo 1798100 25933355 := bstep (se 1 (by rfl) ⟨19450016, by rfl⟩ : syracuseStep 25933355 = 38900033) B38900033
theorem B1799759 : Blo 1798100 1799759 := bstep (se 1 (by rfl) ⟨1349819, by rfl⟩ : syracuseStep 1799759 = 2699639) B2699639
theorem B1799775 : Blo 1798100 1799775 := bstep (se 1 (by rfl) ⟨1349831, by rfl⟩ : syracuseStep 1799775 = 2699663) B2699663
theorem B1799803 : Blo 1798100 1799803 := bstep (se 1 (by rfl) ⟨1349852, by rfl⟩ : syracuseStep 1799803 = 2699705) B2699705
theorem B1799855 : Blo 1798100 1799855 := bstep (se 1 (by rfl) ⟨1349891, by rfl⟩ : syracuseStep 1799855 = 2699783) B2699783
theorem B1799879 : Blo 1798100 1799879 := bstep (se 1 (by rfl) ⟨1349909, by rfl⟩ : syracuseStep 1799879 = 2699819) B2699819
theorem B1799899 : Blo 1798100 1799899 := bstep (se 1 (by rfl) ⟨1349924, by rfl⟩ : syracuseStep 1799899 = 2699849) B2699849
theorem B3036919 : Blo 1798100 3036919 := bstep (se 1 (by rfl) ⟨2277689, by rfl⟩ : syracuseStep 3036919 = 4555379) B4555379
theorem B13661945 : Blo 1798100 13661945 := bstep (se 2 (by rfl) ⟨5123229, by rfl⟩ : syracuseStep 13661945 = 10246459) B10246459
theorem B110810915 : Blo 1798100 110810915 := bstep (se 1 (by rfl) ⟨83108186, by rfl⟩ : syracuseStep 110810915 = 166216373) B166216373
theorem B1799975 : Blo 1798100 1799975 := bstep (se 1 (by rfl) ⟨1349981, by rfl⟩ : syracuseStep 1799975 = 2699963) B2699963
theorem B1800015 : Blo 1798100 1800015 := bstep (se 1 (by rfl) ⟨1350011, by rfl⟩ : syracuseStep 1800015 = 2700023) B2700023
theorem B2160479 : Blo 1798100 2160479 := bstep (se 1 (by rfl) ⟨1620359, by rfl⟩ : syracuseStep 2160479 = 3240719) B3240719
theorem B1800031 : Blo 1798100 1800031 := bstep (se 1 (by rfl) ⟨1350023, by rfl⟩ : syracuseStep 1800031 = 2700047) B2700047
theorem B1800059 : Blo 1798100 1800059 := bstep (se 1 (by rfl) ⟨1350044, by rfl⟩ : syracuseStep 1800059 = 2700089) B2700089
theorem B3037115 : Blo 1798100 3037115 := bstep (se 1 (by rfl) ⟨2277836, by rfl⟩ : syracuseStep 3037115 = 4555673) B4555673
theorem B4380691 : Blo 1798100 4380691 := bstep (se 1 (by rfl) ⟨3285518, by rfl⟩ : syracuseStep 4380691 = 6571037) B6571037
theorem B3037223 : Blo 1798100 3037223 := bstep (se 1 (by rfl) ⟨2277917, by rfl⟩ : syracuseStep 3037223 = 4555835) B4555835
theorem B3037513 : Blo 1798100 3037513 := bstep (se 2 (by rfl) ⟨1139067, by rfl⟩ : syracuseStep 3037513 = 2278135) B2278135
theorem B3037547 : Blo 1798100 3037547 := bstep (se 1 (by rfl) ⟨2278160, by rfl⟩ : syracuseStep 3037547 = 4556321) B4556321
theorem B66558341 : Blo 1798100 66558341 := bstep (se 4 (by rfl) ⟨6239844, by rfl⟩ : syracuseStep 66558341 = 12479689) B12479689
theorem B6068681 : Blo 1798100 6068681 := bstep (se 2 (by rfl) ⟨2275755, by rfl⟩ : syracuseStep 6068681 = 4551511) B4551511
theorem B3840475 : Blo 1798100 3840475 := bstep (se 1 (by rfl) ⟨2880356, by rfl⟩ : syracuseStep 3840475 = 5760713) B5760713
theorem B6486625 : Blo 1798100 6486625 := bstep (se 2 (by rfl) ⟨2432484, by rfl⟩ : syracuseStep 6486625 = 4864969) B4864969
theorem B2276039 : Blo 1798100 2276039 := bstep (se 1 (by rfl) ⟨1707029, by rfl⟩ : syracuseStep 2276039 = 3414059) B3414059
theorem B3414727 : Blo 1798100 3414727 := bstep (se 1 (by rfl) ⟨2561045, by rfl⟩ : syracuseStep 3414727 = 5122091) B5122091
theorem B4864711 : Blo 1798100 4864711 := bstep (se 1 (by rfl) ⟨3648533, by rfl⟩ : syracuseStep 4864711 = 7297067) B7297067
theorem B11238097 : Blo 1798100 11238097 := bstep (se 2 (by rfl) ⟨4214286, by rfl⟩ : syracuseStep 11238097 = 8428573) B8428573
theorem B6068951 : Blo 1798100 6068951 := bstep (se 1 (by rfl) ⟨4551713, by rfl⟩ : syracuseStep 6068951 = 9103427) B9103427
theorem B10246985 : Blo 1798100 10246985 := bstep (se 2 (by rfl) ⟨3842619, by rfl⟩ : syracuseStep 10246985 = 7685239) B7685239
theorem B6486857 : Blo 1798100 6486857 := bstep (se 2 (by rfl) ⟨2432571, by rfl⟩ : syracuseStep 6486857 = 4865143) B4865143
theorem B2276191 : Blo 1798100 2276191 := bstep (se 1 (by rfl) ⟨1707143, by rfl⟩ : syracuseStep 2276191 = 3414287) B3414287
theorem B4553567 : Blo 1798100 4553567 := bstep (se 1 (by rfl) ⟨3415175, by rfl⟩ : syracuseStep 4553567 = 6830351) B6830351
theorem B6069167 : Blo 1798100 6069167 := bstep (se 1 (by rfl) ⟨4551875, by rfl⟩ : syracuseStep 6069167 = 9103751) B9103751
theorem B4045751 : Blo 1798100 4045751 := bstep (se 1 (by rfl) ⟨3034313, by rfl⟩ : syracuseStep 4045751 = 6068627) B6068627
theorem B5766223 : Blo 1798100 5766223 := bstep (se 1 (by rfl) ⟨4324667, by rfl⟩ : syracuseStep 5766223 = 8649335) B8649335
theorem B13663403 : Blo 1798100 13663403 := bstep (se 1 (by rfl) ⟨10247552, by rfl⟩ : syracuseStep 13663403 = 20495105) B20495105
theorem B24624323 : Blo 1798100 24624323 := bstep (se 1 (by rfl) ⟨18468242, by rfl⟩ : syracuseStep 24624323 = 36936485) B36936485
theorem B11525399 : Blo 1798100 11525399 := bstep (se 1 (by rfl) ⟨8644049, by rfl⟩ : syracuseStep 11525399 = 17288099) B17288099
theorem B17530201 : Blo 1798100 17530201 := bstep (se 2 (by rfl) ⟨6573825, by rfl⟩ : syracuseStep 17530201 = 13147651) B13147651
theorem B4046345 : Blo 1798100 4046345 := bstep (se 2 (by rfl) ⟨1517379, by rfl⟩ : syracuseStep 4046345 = 3034759) B3034759
theorem B4554265 : Blo 1798100 4554265 := bstep (se 2 (by rfl) ⟨1707849, by rfl⟩ : syracuseStep 4554265 = 3415699) B3415699
theorem B6831641 : Blo 1798100 6831641 := bstep (se 2 (by rfl) ⟨2561865, by rfl⟩ : syracuseStep 6831641 = 5123731) B5123731
theorem B13663889 : Blo 1798100 13663889 := bstep (se 2 (by rfl) ⟨5123958, by rfl⟩ : syracuseStep 13663889 = 10247917) B10247917
theorem B9723539 : Blo 1798100 9723539 := bstep (se 1 (by rfl) ⟨7292654, by rfl⟩ : syracuseStep 9723539 = 14585309) B14585309
theorem B23363261 : Blo 1798100 23363261 := bstep (se 3 (by rfl) ⟨4380611, by rfl⟩ : syracuseStep 23363261 = 8761223) B8761223
theorem B3243731 : Blo 1798100 3243731 := bstep (se 1 (by rfl) ⟨2432798, by rfl⟩ : syracuseStep 3243731 = 4865597) B4865597
theorem B59121413 : Blo 1798100 59121413 := bstep (se 4 (by rfl) ⟨5542632, by rfl⟩ : syracuseStep 59121413 = 11085265) B11085265
theorem B4554569 : Blo 1798100 4554569 := bstep (se 2 (by rfl) ⟨1707963, by rfl⟩ : syracuseStep 4554569 = 3415927) B3415927
theorem B12304223 : Blo 1798100 12304223 := bstep (se 1 (by rfl) ⟨9228167, by rfl⟩ : syracuseStep 12304223 = 18456335) B18456335
theorem B4046687 : Blo 1798100 4046687 := bstep (se 1 (by rfl) ⟨3035015, by rfl⟩ : syracuseStep 4046687 = 6070031) B6070031
theorem B5840921 : Blo 1798100 5840921 := bstep (se 2 (by rfl) ⟨2190345, by rfl⟩ : syracuseStep 5840921 = 4380691) B4380691
theorem B13656113 : Blo 1798100 13656113 := bstep (se 2 (by rfl) ⟨5121042, by rfl⟩ : syracuseStep 13656113 = 10242085) B10242085
theorem B13664375 : Blo 1798100 13664375 := bstep (se 1 (by rfl) ⟨10248281, by rfl⟩ : syracuseStep 13664375 = 20496563) B20496563
theorem B2023771 : Blo 1798100 2023771 := bstep (se 1 (by rfl) ⟨1517828, by rfl⟩ : syracuseStep 2023771 = 3035657) B3035657
theorem B2023879 : Blo 1798100 2023879 := bstep (se 1 (by rfl) ⟨1517909, by rfl⟩ : syracuseStep 2023879 = 3035819) B3035819
theorem B7684571 : Blo 1798100 7684571 := bstep (se 1 (by rfl) ⟨5763428, by rfl⟩ : syracuseStep 7684571 = 11526857) B11526857
theorem B4383227 : Blo 1798100 4383227 := bstep (se 1 (by rfl) ⟨3287420, by rfl⟩ : syracuseStep 4383227 = 6574841) B6574841
theorem B34595333 : Blo 1798100 34595333 := bstep (se 4 (by rfl) ⟨3243312, by rfl⟩ : syracuseStep 34595333 = 6486625) B6486625
theorem B2277983 : Blo 1798100 2277983 := bstep (se 1 (by rfl) ⟨1708487, by rfl⟩ : syracuseStep 2277983 = 3416975) B3416975
theorem B5120633 : Blo 1798100 5120633 := bstep (se 2 (by rfl) ⟨1920237, by rfl⟩ : syracuseStep 5120633 = 3840475) B3840475
theorem B36922027 : Blo 1798100 36922027 := bstep (se 1 (by rfl) ⟨27691520, by rfl⟩ : syracuseStep 36922027 = 55383041) B55383041
theorem B10248875 : Blo 1798100 10248875 := bstep (se 1 (by rfl) ⟨7686656, by rfl⟩ : syracuseStep 10248875 = 15373313) B15373313
theorem B9110231 : Blo 1798100 9110231 := bstep (se 1 (by rfl) ⟨6832673, by rfl⟩ : syracuseStep 9110231 = 13665347) B13665347
theorem B4555511 : Blo 1798100 4555511 := bstep (se 1 (by rfl) ⟨3416633, by rfl⟩ : syracuseStep 4555511 = 6833267) B6833267
theorem B2024239 : Blo 1798100 2024239 := bstep (se 1 (by rfl) ⟨1518179, by rfl⟩ : syracuseStep 2024239 = 3036359) B3036359
theorem B4047695 : Blo 1798100 4047695 := bstep (se 1 (by rfl) ⟨3035771, by rfl⟩ : syracuseStep 4047695 = 6071543) B6071543
theorem B2024347 : Blo 1798100 2024347 := bstep (se 1 (by rfl) ⟨1518260, by rfl⟩ : syracuseStep 2024347 = 3036521) B3036521
theorem B14984129 : Blo 1798100 14984129 := bstep (se 2 (by rfl) ⟨5619048, by rfl⟩ : syracuseStep 14984129 = 11238097) B11238097
theorem B11092967 : Blo 1798100 11092967 := bstep (se 1 (by rfl) ⟨8319725, by rfl⟩ : syracuseStep 11092967 = 16639451) B16639451
theorem B4047911 : Blo 1798100 4047911 := bstep (se 1 (by rfl) ⟨3035933, by rfl⟩ : syracuseStep 4047911 = 6071867) B6071867
theorem B23053409 : Blo 1798100 23053409 := bstep (se 2 (by rfl) ⟨8645028, by rfl⟩ : syracuseStep 23053409 = 17290057) B17290057
theorem B4048091 : Blo 1798100 4048091 := bstep (se 1 (by rfl) ⟨3036068, by rfl⟩ : syracuseStep 4048091 = 6072137) B6072137
theorem B2024743 : Blo 1798100 2024743 := bstep (se 1 (by rfl) ⟨1518557, by rfl⟩ : syracuseStep 2024743 = 3037115) B3037115
theorem B17286443 : Blo 1798100 17286443 := bstep (se 1 (by rfl) ⟨12964832, by rfl⟩ : syracuseStep 17286443 = 25929665) B25929665
theorem B9110879 : Blo 1798100 9110879 := bstep (se 1 (by rfl) ⟨6833159, by rfl⟩ : syracuseStep 9110879 = 13666319) B13666319
theorem B2024815 : Blo 1798100 2024815 := bstep (se 1 (by rfl) ⟨1518611, by rfl⟩ : syracuseStep 2024815 = 3037223) B3037223
theorem B4048289 : Blo 1798100 4048289 := bstep (se 2 (by rfl) ⟨1518108, by rfl⟩ : syracuseStep 4048289 = 3036217) B3036217
theorem B2025031 : Blo 1798100 2025031 := bstep (se 1 (by rfl) ⟨1518773, by rfl⟩ : syracuseStep 2025031 = 3037547) B3037547
theorem B4556371 : Blo 1798100 4556371 := bstep (se 1 (by rfl) ⟨3417278, by rfl⟩ : syracuseStep 4556371 = 6834557) B6834557
theorem B2697167 : Blo 1798100 2697167 := bstep (se 1 (by rfl) ⟨2022875, by rfl⟩ : syracuseStep 2697167 = 4045751) B4045751
theorem B4048847 : Blo 1798100 4048847 := bstep (se 1 (by rfl) ⟨3036635, by rfl⟩ : syracuseStep 4048847 = 6073271) B6073271
theorem B32819215 : Blo 1798100 32819215 := bstep (se 1 (by rfl) ⟨24614411, by rfl⟩ : syracuseStep 32819215 = 49228823) B49228823
theorem B6072353 : Blo 1798100 6072353 := bstep (se 2 (by rfl) ⟨2277132, by rfl⟩ : syracuseStep 6072353 = 4554265) B4554265
theorem B5761277 : Blo 1798100 5761277 := bstep (se 3 (by rfl) ⟨1080239, by rfl⟩ : syracuseStep 5761277 = 2160479) B2160479
theorem B4049225 : Blo 1798100 4049225 := bstep (se 2 (by rfl) ⟨1518459, by rfl⟩ : syracuseStep 4049225 = 3036919) B3036919
theorem B2697563 : Blo 1798100 2697563 := bstep (se 1 (by rfl) ⟨2023172, by rfl⟩ : syracuseStep 2697563 = 4046345) B4046345
theorem B4049243 : Blo 1798100 4049243 := bstep (se 1 (by rfl) ⟨3036932, by rfl⟩ : syracuseStep 4049243 = 6073865) B6073865
theorem B6482359 : Blo 1798100 6482359 := bstep (se 1 (by rfl) ⟨4861769, by rfl⟩ : syracuseStep 6482359 = 9723539) B9723539
theorem B15575507 : Blo 1798100 15575507 := bstep (se 1 (by rfl) ⟨11681630, by rfl⟩ : syracuseStep 15575507 = 23363261) B23363261
theorem B39414275 : Blo 1798100 39414275 := bstep (se 1 (by rfl) ⟨29560706, by rfl⟩ : syracuseStep 39414275 = 59121413) B59121413
theorem B8202815 : Blo 1798100 8202815 := bstep (se 1 (by rfl) ⟨6152111, by rfl⟩ : syracuseStep 8202815 = 12304223) B12304223
theorem B2697791 : Blo 1798100 2697791 := bstep (se 1 (by rfl) ⟨2023343, by rfl⟩ : syracuseStep 2697791 = 4046687) B4046687
theorem B2697911 : Blo 1798100 2697911 := bstep (se 1 (by rfl) ⟨2023433, by rfl⟩ : syracuseStep 2697911 = 4046867) B4046867
theorem B2001743 : Blo 1798100 2001743 := bstep (se 1 (by rfl) ⟨1501307, by rfl⟩ : syracuseStep 2001743 = 3002615) B3002615
theorem B2698139 : Blo 1798100 2698139 := bstep (se 1 (by rfl) ⟨2023604, by rfl⟩ : syracuseStep 2698139 = 4047209) B4047209
theorem B8547227 : Blo 1798100 8547227 := bstep (se 1 (by rfl) ⟨6410420, by rfl⟩ : syracuseStep 8547227 = 12820841) B12820841
theorem B4049819 : Blo 1798100 4049819 := bstep (se 1 (by rfl) ⟨3037364, by rfl⟩ : syracuseStep 4049819 = 6074729) B6074729
theorem B2051023 : Blo 1798100 2051023 := bstep (se 1 (by rfl) ⟨1538267, by rfl⟩ : syracuseStep 2051023 = 3076535) B3076535
theorem B9104399 : Blo 1798100 9104399 := bstep (se 1 (by rfl) ⟨6828299, by rfl⟩ : syracuseStep 9104399 = 13656599) B13656599
theorem B4050017 : Blo 1798100 4050017 := bstep (se 2 (by rfl) ⟨1518756, by rfl⟩ : syracuseStep 4050017 = 3037513) B3037513
theorem B7785661 : Blo 1798100 7785661 := bstep (se 3 (by rfl) ⟨1459811, by rfl⟩ : syracuseStep 7785661 = 2919623) B2919623
theorem B2698535 : Blo 1798100 2698535 := bstep (se 1 (by rfl) ⟨2023901, by rfl⟩ : syracuseStep 2698535 = 4047803) B4047803
theorem B4050215 : Blo 1798100 4050215 := bstep (se 1 (by rfl) ⟨3037661, by rfl⟩ : syracuseStep 4050215 = 6075323) B6075323
theorem B2698619 : Blo 1798100 2698619 := bstep (se 1 (by rfl) ⟨2023964, by rfl⟩ : syracuseStep 2698619 = 4047929) B4047929
theorem B4615561 : Blo 1798100 4615561 := bstep (se 2 (by rfl) ⟨1730835, by rfl⟩ : syracuseStep 4615561 = 3461671) B3461671
theorem B2698745 : Blo 1798100 2698745 := bstep (se 2 (by rfl) ⟨1012029, by rfl⟩ : syracuseStep 2698745 = 2024059) B2024059
theorem B8646203 : Blo 1798100 8646203 := bstep (se 1 (by rfl) ⟨6484652, by rfl⟩ : syracuseStep 8646203 = 12969305) B12969305
theorem B2698847 : Blo 1798100 2698847 := bstep (se 1 (by rfl) ⟨2024135, by rfl⟩ : syracuseStep 2698847 = 4048271) B4048271
theorem B8646259 : Blo 1798100 8646259 := bstep (se 1 (by rfl) ⟨6484694, by rfl⟩ : syracuseStep 8646259 = 12969389) B12969389
theorem B11521709 : Blo 1798100 11521709 := bstep (se 3 (by rfl) ⟨2160320, by rfl⟩ : syracuseStep 11521709 = 4320641) B4320641
theorem B17288903 : Blo 1798100 17288903 := bstep (se 1 (by rfl) ⟨12966677, by rfl⟩ : syracuseStep 17288903 = 25933355) B25933355
theorem B3034921 : Blo 1798100 3034921 := bstep (se 2 (by rfl) ⟨1138095, by rfl⟩ : syracuseStep 3034921 = 2276191) B2276191
theorem B2699063 : Blo 1798100 2699063 := bstep (se 1 (by rfl) ⟨2024297, by rfl⟩ : syracuseStep 2699063 = 4048595) B4048595
theorem B9105209 : Blo 1798100 9105209 := bstep (se 2 (by rfl) ⟨3414453, by rfl⟩ : syracuseStep 9105209 = 6828907) B6828907
theorem B6926141 : Blo 1798100 6926141 := bstep (se 3 (by rfl) ⟨1298651, by rfl⟩ : syracuseStep 6926141 = 2597303) B2597303
theorem B1798119 : Blo 1798100 1798119 := bstep (se 1 (by rfl) ⟨1348589, by rfl⟩ : syracuseStep 1798119 = 2697179) B2697179
theorem B7893011 : Blo 1798100 7893011 := bstep (se 1 (by rfl) ⟨5919758, by rfl⟩ : syracuseStep 7893011 = 11839517) B11839517
theorem B2699369 : Blo 1798100 2699369 := bstep (se 2 (by rfl) ⟨1012263, by rfl⟩ : syracuseStep 2699369 = 2024527) B2024527
theorem B7688297 : Blo 1798100 7688297 := bstep (se 2 (by rfl) ⟨2883111, by rfl⟩ : syracuseStep 7688297 = 5766223) B5766223
theorem B44372227 : Blo 1798100 44372227 := bstep (se 1 (by rfl) ⟨33279170, by rfl⟩ : syracuseStep 44372227 = 66558341) B66558341
theorem B1798431 : Blo 1798100 1798431 := bstep (se 1 (by rfl) ⟨1348823, by rfl⟩ : syracuseStep 1798431 = 2697647) B2697647
theorem B1798491 : Blo 1798100 1798491 := bstep (se 1 (by rfl) ⟨1348868, by rfl⟩ : syracuseStep 1798491 = 2697737) B2697737
theorem B1798511 : Blo 1798100 1798511 := bstep (se 1 (by rfl) ⟨1348883, by rfl⟩ : syracuseStep 1798511 = 2697767) B2697767
theorem B1798567 : Blo 1798100 1798567 := bstep (se 1 (by rfl) ⟨1348925, by rfl⟩ : syracuseStep 1798567 = 2697851) B2697851
theorem B2699687 : Blo 1798100 2699687 := bstep (se 1 (by rfl) ⟨2024765, by rfl⟩ : syracuseStep 2699687 = 4049531) B4049531
theorem B1798651 : Blo 1798100 1798651 := bstep (se 1 (by rfl) ⟨1348988, by rfl⟩ : syracuseStep 1798651 = 2697977) B2697977
theorem B2699771 : Blo 1798100 2699771 := bstep (se 1 (by rfl) ⟨2024828, by rfl⟩ : syracuseStep 2699771 = 4049657) B4049657
theorem B1798719 : Blo 1798100 1798719 := bstep (se 1 (by rfl) ⟨1349039, by rfl⟩ : syracuseStep 1798719 = 2698079) B2698079
theorem B3035711 : Blo 1798100 3035711 := bstep (se 1 (by rfl) ⟨2276783, by rfl⟩ : syracuseStep 3035711 = 4553567) B4553567
theorem B1798727 : Blo 1798100 1798727 := bstep (se 1 (by rfl) ⟨1349045, by rfl⟩ : syracuseStep 1798727 = 2698091) B2698091
theorem B2699897 : Blo 1798100 2699897 := bstep (se 2 (by rfl) ⟨1012461, by rfl⟩ : syracuseStep 2699897 = 2024923) B2024923
theorem B5763737 : Blo 1798100 5763737 := bstep (se 2 (by rfl) ⟨2161401, by rfl⟩ : syracuseStep 5763737 = 4322803) B4322803
theorem B4616875 : Blo 1798100 4616875 := bstep (se 1 (by rfl) ⟨3462656, by rfl⟩ : syracuseStep 4616875 = 6925313) B6925313
theorem B5124779 : Blo 1798100 5124779 := bstep (se 1 (by rfl) ⟨3843584, by rfl⟩ : syracuseStep 5124779 = 7687169) B7687169
theorem B2699951 : Blo 1798100 2699951 := bstep (se 1 (by rfl) ⟨2024963, by rfl⟩ : syracuseStep 2699951 = 4049927) B4049927
theorem B32813747 : Blo 1798100 32813747 := bstep (se 1 (by rfl) ⟨24610310, by rfl⟩ : syracuseStep 32813747 = 49220621) B49220621
theorem B1798879 : Blo 1798100 1798879 := bstep (se 1 (by rfl) ⟨1349159, by rfl⟩ : syracuseStep 1798879 = 2698319) B2698319
theorem B2699999 : Blo 1798100 2699999 := bstep (se 1 (by rfl) ⟨2024999, by rfl⟩ : syracuseStep 2699999 = 4049999) B4049999
theorem B21893917 : Blo 1798100 21893917 := bstep (se 3 (by rfl) ⟨4105109, by rfl⟩ : syracuseStep 21893917 = 8210219) B8210219
theorem B1798959 : Blo 1798100 1798959 := bstep (se 1 (by rfl) ⟨1349219, by rfl⟩ : syracuseStep 1798959 = 2698439) B2698439
theorem B6075215 : Blo 1798100 6075215 := bstep (se 1 (by rfl) ⟨4556411, by rfl⟩ : syracuseStep 6075215 = 9112823) B9112823
theorem B34599797 : Blo 1798100 34599797 := bstep (se 5 (by rfl) ⟨1621865, by rfl⟩ : syracuseStep 34599797 = 3243731) B3243731
theorem B1799067 : Blo 1798100 1799067 := bstep (se 1 (by rfl) ⟨1349300, by rfl⟩ : syracuseStep 1799067 = 2698601) B2698601
theorem B8205257 : Blo 1798100 8205257 := bstep (se 2 (by rfl) ⟨3076971, by rfl⟩ : syracuseStep 8205257 = 6153943) B6153943
theorem B1799119 : Blo 1798100 1799119 := bstep (se 1 (by rfl) ⟨1349339, by rfl⟩ : syracuseStep 1799119 = 2698679) B2698679
theorem B9860059 : Blo 1798100 9860059 := bstep (se 1 (by rfl) ⟨7395044, by rfl⟩ : syracuseStep 9860059 = 14790089) B14790089
theorem B1799143 : Blo 1798100 1799143 := bstep (se 1 (by rfl) ⟨1349357, by rfl⟩ : syracuseStep 1799143 = 2698715) B2698715
theorem B6829181 : Blo 1798100 6829181 := bstep (se 3 (by rfl) ⟨1280471, by rfl⟩ : syracuseStep 6829181 = 2560943) B2560943
theorem B7681223 : Blo 1798100 7681223 := bstep (se 1 (by rfl) ⟨5760917, by rfl⟩ : syracuseStep 7681223 = 11521835) B11521835
theorem B3036379 : Blo 1798100 3036379 := bstep (se 1 (by rfl) ⟨2277284, by rfl⟩ : syracuseStep 3036379 = 4554569) B4554569
theorem B1799455 : Blo 1798100 1799455 := bstep (se 1 (by rfl) ⟨1349591, by rfl⟩ : syracuseStep 1799455 = 2699183) B2699183
theorem B1799515 : Blo 1798100 1799515 := bstep (se 1 (by rfl) ⟨1349636, by rfl⟩ : syracuseStep 1799515 = 2699273) B2699273
theorem B1799535 : Blo 1798100 1799535 := bstep (se 1 (by rfl) ⟨1349651, by rfl⟩ : syracuseStep 1799535 = 2699303) B2699303
theorem B1799591 : Blo 1798100 1799591 := bstep (se 1 (by rfl) ⟨1349693, by rfl⟩ : syracuseStep 1799591 = 2699387) B2699387
theorem B1799675 : Blo 1798100 1799675 := bstep (se 1 (by rfl) ⟨1349756, by rfl⟩ : syracuseStep 1799675 = 2699513) B2699513
theorem B2307647 : Blo 1798100 2307647 := bstep (se 1 (by rfl) ⟨1730735, by rfl⟩ : syracuseStep 2307647 = 3461471) B3461471
theorem B1799743 : Blo 1798100 1799743 := bstep (se 1 (by rfl) ⟨1349807, by rfl⟩ : syracuseStep 1799743 = 2699615) B2699615
theorem B1799751 : Blo 1798100 1799751 := bstep (se 1 (by rfl) ⟨1349813, by rfl⟩ : syracuseStep 1799751 = 2699627) B2699627
theorem B1799903 : Blo 1798100 1799903 := bstep (se 1 (by rfl) ⟨1349927, by rfl⟩ : syracuseStep 1799903 = 2699855) B2699855
theorem B3413801 : Blo 1798100 3413801 := bstep (se 2 (by rfl) ⟨1280175, by rfl⟩ : syracuseStep 3413801 = 2560351) B2560351
theorem B1799983 : Blo 1798100 1799983 := bstep (se 1 (by rfl) ⟨1349987, by rfl⟩ : syracuseStep 1799983 = 2699975) B2699975
theorem B6829879 : Blo 1798100 6829879 := bstep (se 1 (by rfl) ⟨5122409, by rfl⟩ : syracuseStep 6829879 = 10244819) B10244819
theorem B1800091 : Blo 1798100 1800091 := bstep (se 1 (by rfl) ⟨1350068, by rfl⟩ : syracuseStep 1800091 = 2700137) B2700137
theorem B3037135 : Blo 1798100 3037135 := bstep (se 1 (by rfl) ⟨2277851, by rfl⟩ : syracuseStep 3037135 = 4555703) B4555703
theorem B14596175 : Blo 1798100 14596175 := bstep (se 1 (by rfl) ⟨10947131, by rfl⟩ : syracuseStep 14596175 = 21894263) B21894263
theorem B2160859 : Blo 1798100 2160859 := bstep (se 1 (by rfl) ⟨1620644, by rfl⟩ : syracuseStep 2160859 = 3241289) B3241289
theorem B4552969 : Blo 1798100 4552969 := bstep (se 2 (by rfl) ⟨1707363, by rfl⟩ : syracuseStep 4552969 = 3414727) B3414727
theorem B6486281 : Blo 1798100 6486281 := bstep (se 2 (by rfl) ⟨2432355, by rfl⟩ : syracuseStep 6486281 = 4864711) B4864711
theorem B6830365 : Blo 1798100 6830365 := bstep (se 3 (by rfl) ⟨1280693, by rfl⟩ : syracuseStep 6830365 = 2561387) B2561387
theorem B1947943 : Blo 1798100 1947943 := bstep (se 1 (by rfl) ⟨1460957, by rfl⟩ : syracuseStep 1947943 = 2921915) B2921915
theorem B9107963 : Blo 1798100 9107963 := bstep (se 1 (by rfl) ⟨6830972, by rfl⟩ : syracuseStep 9107963 = 13661945) B13661945
theorem B73873943 : Blo 1798100 73873943 := bstep (se 1 (by rfl) ⟨55405457, by rfl⟩ : syracuseStep 73873943 = 110810915) B110810915
theorem B6068843 : Blo 1798100 6068843 := bstep (se 1 (by rfl) ⟨4551632, by rfl⟩ : syracuseStep 6068843 = 9103265) B9103265
theorem B2431663 : Blo 1798100 2431663 := bstep (se 1 (by rfl) ⟨1823747, by rfl⟩ : syracuseStep 2431663 = 3647495) B3647495
theorem B3414955 : Blo 1798100 3414955 := bstep (se 1 (by rfl) ⟨2561216, by rfl⟩ : syracuseStep 3414955 = 5122433) B5122433
theorem B4045787 : Blo 1798100 4045787 := bstep (se 1 (by rfl) ⟨3034340, by rfl⟩ : syracuseStep 4045787 = 6068681) B6068681
theorem B58350563 : Blo 1798100 58350563 := bstep (se 1 (by rfl) ⟨43762922, by rfl⟩ : syracuseStep 58350563 = 87525845) B87525845
theorem B3415031 : Blo 1798100 3415031 := bstep (se 1 (by rfl) ⟨2561273, by rfl⟩ : syracuseStep 3415031 = 5122547) B5122547
theorem B93494405 : Blo 1798100 93494405 := bstep (se 4 (by rfl) ⟨8765100, by rfl⟩ : syracuseStep 93494405 = 17530201) B17530201
theorem B4045967 : Blo 1798100 4045967 := bstep (se 1 (by rfl) ⟨3034475, by rfl⟩ : syracuseStep 4045967 = 6068951) B6068951
theorem B6069437 : Blo 1798100 6069437 := bstep (se 3 (by rfl) ⟨1138019, by rfl⟩ : syracuseStep 6069437 = 2276039) B2276039
theorem B3415259 : Blo 1798100 3415259 := bstep (se 1 (by rfl) ⟨2561444, by rfl⟩ : syracuseStep 3415259 = 5122889) B5122889
theorem B6831323 : Blo 1798100 6831323 := bstep (se 1 (by rfl) ⟨5123492, by rfl⟩ : syracuseStep 6831323 = 10246985) B10246985
theorem B4324571 : Blo 1798100 4324571 := bstep (se 1 (by rfl) ⟨3243428, by rfl⟩ : syracuseStep 4324571 = 6486857) B6486857
theorem B4046057 : Blo 1798100 4046057 := bstep (se 2 (by rfl) ⟨1517271, by rfl⟩ : syracuseStep 4046057 = 3034543) B3034543
theorem B4046111 : Blo 1798100 4046111 := bstep (se 1 (by rfl) ⟨3034583, by rfl⟩ : syracuseStep 4046111 = 6069167) B6069167
theorem B8641991 : Blo 1798100 8641991 := bstep (se 1 (by rfl) ⟨6481493, by rfl⟩ : syracuseStep 8641991 = 12962987) B12962987
theorem B9108935 : Blo 1798100 9108935 := bstep (se 1 (by rfl) ⟨6831701, by rfl⟩ : syracuseStep 9108935 = 13663403) B13663403
theorem B25927127 : Blo 1798100 25927127 := bstep (se 1 (by rfl) ⟨19445345, by rfl⟩ : syracuseStep 25927127 = 38890691) B38890691
theorem B16416215 : Blo 1798100 16416215 := bstep (se 1 (by rfl) ⟨12312161, by rfl⟩ : syracuseStep 16416215 = 24624323) B24624323
theorem B27704825 : Blo 1798100 27704825 := bstep (se 2 (by rfl) ⟨10389309, by rfl⟩ : syracuseStep 27704825 = 20778619) B20778619
theorem B2022907 : Blo 1798100 2022907 := bstep (se 1 (by rfl) ⟨1517180, by rfl⟩ : syracuseStep 2022907 = 3034361) B3034361
theorem B7683599 : Blo 1798100 7683599 := bstep (se 1 (by rfl) ⟨5762699, by rfl⟩ : syracuseStep 7683599 = 11525399) B11525399
theorem B2023087 : Blo 1798100 2023087 := bstep (se 1 (by rfl) ⟨1517315, by rfl⟩ : syracuseStep 2023087 = 3034631) B3034631
theorem B4554427 : Blo 1798100 4554427 := bstep (se 1 (by rfl) ⟨3415820, by rfl⟩ : syracuseStep 4554427 = 6831641) B6831641
theorem B9109259 : Blo 1798100 9109259 := bstep (se 1 (by rfl) ⟨6831944, by rfl⟩ : syracuseStep 9109259 = 13663889) B13663889
theorem B4046633 : Blo 1798100 4046633 := bstep (se 2 (by rfl) ⟨1517487, by rfl⟩ : syracuseStep 4046633 = 3034975) B3034975
theorem B38887229 : Blo 1798100 38887229 := bstep (se 3 (by rfl) ⟨7291355, by rfl⟩ : syracuseStep 38887229 = 14582711) B14582711
theorem B2023375 : Blo 1798100 2023375 := bstep (se 1 (by rfl) ⟨1517531, by rfl⟩ : syracuseStep 2023375 = 3035063) B3035063
theorem B9109583 : Blo 1798100 9109583 := bstep (se 1 (by rfl) ⟨6832187, by rfl⟩ : syracuseStep 9109583 = 13664375) B13664375
theorem B59162969 : Blo 1798100 59162969 := bstep (se 2 (by rfl) ⟨22186113, by rfl⟩ : syracuseStep 59162969 = 44372227) B44372227
theorem B6070625 : Blo 1798100 6070625 := bstep (se 2 (by rfl) ⟨2276484, by rfl⟩ : syracuseStep 6070625 = 4552969) B4552969
theorem B2023807 : Blo 1798100 2023807 := bstep (se 1 (by rfl) ⟨1517855, by rfl⟩ : syracuseStep 2023807 = 3035711) B3035711
theorem B2597257 : Blo 1798100 2597257 := bstep (se 2 (by rfl) ⟨973971, by rfl⟩ : syracuseStep 2597257 = 1947943) B1947943
theorem B3842491 : Blo 1798100 3842491 := bstep (se 1 (by rfl) ⟨2881868, by rfl⟩ : syracuseStep 3842491 = 5763737) B5763737
theorem B6832583 : Blo 1798100 6832583 := bstep (se 1 (by rfl) ⟨5124437, by rfl⟩ : syracuseStep 6832583 = 10248875) B10248875
theorem B3416519 : Blo 1798100 3416519 := bstep (se 1 (by rfl) ⟨2562389, by rfl⟩ : syracuseStep 3416519 = 5124779) B5124779
theorem B8643145 : Blo 1798100 8643145 := bstep (se 2 (by rfl) ⟨3241179, by rfl⟩ : syracuseStep 8643145 = 6482359) B6482359
theorem B15368939 : Blo 1798100 15368939 := bstep (se 1 (by rfl) ⟨11526704, by rfl⟩ : syracuseStep 15368939 = 23053409) B23053409
theorem B5120815 : Blo 1798100 5120815 := bstep (se 1 (by rfl) ⟨3840611, by rfl⟩ : syracuseStep 5120815 = 7681223) B7681223
theorem B12968869 : Blo 1798100 12968869 := bstep (se 4 (by rfl) ⟨1215831, by rfl⟩ : syracuseStep 12968869 = 2431663) B2431663
theorem B23045309 : Blo 1798100 23045309 := bstep (se 3 (by rfl) ⟨4320995, by rfl⟩ : syracuseStep 23045309 = 8641991) B8641991
theorem B4048235 : Blo 1798100 4048235 := bstep (se 1 (by rfl) ⟨3036176, by rfl⟩ : syracuseStep 4048235 = 6072353) B6072353
theorem B6153725 : Blo 1798100 6153725 := bstep (se 3 (by rfl) ⟨1153823, by rfl⟩ : syracuseStep 6153725 = 2307647) B2307647
theorem B10380881 : Blo 1798100 10380881 := bstep (se 2 (by rfl) ⟨3892830, by rfl⟩ : syracuseStep 10380881 = 7785661) B7785661
theorem B4048505 : Blo 1798100 4048505 := bstep (se 2 (by rfl) ⟨1518189, by rfl⟩ : syracuseStep 4048505 = 3036379) B3036379
theorem B6071975 : Blo 1798100 6071975 := bstep (se 1 (by rfl) ⟨4553981, by rfl⟩ : syracuseStep 6071975 = 9107963) B9107963
theorem B2697191 : Blo 1798100 2697191 := bstep (se 1 (by rfl) ⟨2022893, by rfl⟩ : syracuseStep 2697191 = 4045787) B4045787
theorem B2697209 : Blo 1798100 2697209 := bstep (se 2 (by rfl) ⟨1011453, by rfl⟩ : syracuseStep 2697209 = 2022907) B2022907
theorem B2697311 : Blo 1798100 2697311 := bstep (se 1 (by rfl) ⟨2022983, by rfl⟩ : syracuseStep 2697311 = 4045967) B4045967
theorem B11528345 : Blo 1798100 11528345 := bstep (se 2 (by rfl) ⟨4323129, by rfl⟩ : syracuseStep 11528345 = 8646259) B8646259
theorem B2697371 : Blo 1798100 2697371 := bstep (se 1 (by rfl) ⟨2023028, by rfl⟩ : syracuseStep 2697371 = 4046057) B4046057
theorem B2697407 : Blo 1798100 2697407 := bstep (se 1 (by rfl) ⟨2023055, by rfl⟩ : syracuseStep 2697407 = 4046111) B4046111
theorem B2697449 : Blo 1798100 2697449 := bstep (se 2 (by rfl) ⟨1011543, by rfl⟩ : syracuseStep 2697449 = 2023087) B2023087
theorem B6072569 : Blo 1798100 6072569 := bstep (se 2 (by rfl) ⟨2277213, by rfl⟩ : syracuseStep 6072569 = 4554427) B4554427
theorem B6072623 : Blo 1798100 6072623 := bstep (se 1 (by rfl) ⟨4554467, by rfl⟩ : syracuseStep 6072623 = 9108935) B9108935
theorem B5122399 : Blo 1798100 5122399 := bstep (se 1 (by rfl) ⟨3841799, by rfl⟩ : syracuseStep 5122399 = 7683599) B7683599
theorem B6072839 : Blo 1798100 6072839 := bstep (se 1 (by rfl) ⟨4554629, by rfl⟩ : syracuseStep 6072839 = 9109259) B9109259
theorem B2697755 : Blo 1798100 2697755 := bstep (se 1 (by rfl) ⟨2023316, by rfl⟩ : syracuseStep 2697755 = 4046633) B4046633
theorem B2697833 : Blo 1798100 2697833 := bstep (se 2 (by rfl) ⟨1011687, by rfl⟩ : syracuseStep 2697833 = 2023375) B2023375
theorem B4049513 : Blo 1798100 4049513 := bstep (se 2 (by rfl) ⟨1518567, by rfl⟩ : syracuseStep 4049513 = 3037135) B3037135
theorem B9104075 : Blo 1798100 9104075 := bstep (se 1 (by rfl) ⟨6828056, by rfl⟩ : syracuseStep 9104075 = 13656113) B13656113
theorem B21048029 : Blo 1798100 21048029 := bstep (se 3 (by rfl) ⟨3946505, by rfl⟩ : syracuseStep 21048029 = 7893011) B7893011
theorem B15575789 : Blo 1798100 15575789 := bstep (se 3 (by rfl) ⟨2920460, by rfl⟩ : syracuseStep 15575789 = 5840921) B5840921
theorem B23063555 : Blo 1798100 23063555 := bstep (se 1 (by rfl) ⟨17297666, by rfl⟩ : syracuseStep 23063555 = 34595333) B34595333
theorem B21875831 : Blo 1798100 21875831 := bstep (se 1 (by rfl) ⟨16406873, by rfl⟩ : syracuseStep 21875831 = 32813747) B32813747
theorem B2698361 : Blo 1798100 2698361 := bstep (se 2 (by rfl) ⟨1011885, by rfl⟩ : syracuseStep 2698361 = 2023771) B2023771
theorem B6073487 : Blo 1798100 6073487 := bstep (se 1 (by rfl) ⟨4555115, by rfl⟩ : syracuseStep 6073487 = 9110231) B9110231
theorem B2698463 : Blo 1798100 2698463 := bstep (se 1 (by rfl) ⟨2023847, by rfl⟩ : syracuseStep 2698463 = 4047695) B4047695
theorem B4050143 : Blo 1798100 4050143 := bstep (se 1 (by rfl) ⟨3037607, by rfl⟩ : syracuseStep 4050143 = 6075215) B6075215
theorem B2698505 : Blo 1798100 2698505 := bstep (se 2 (by rfl) ⟨1011939, by rfl⟩ : syracuseStep 2698505 = 2023879) B2023879
theorem B9989419 : Blo 1798100 9989419 := bstep (se 1 (by rfl) ⟨7492064, by rfl⟩ : syracuseStep 9989419 = 14984129) B14984129
theorem B2698607 : Blo 1798100 2698607 := bstep (se 1 (by rfl) ⟨2023955, by rfl⟩ : syracuseStep 2698607 = 4047911) B4047911
theorem B2698727 : Blo 1798100 2698727 := bstep (se 1 (by rfl) ⟨2024045, by rfl⟩ : syracuseStep 2698727 = 4048091) B4048091
theorem B21351925 : Blo 1798100 21351925 := bstep (se 5 (by rfl) ⟨1000871, by rfl⟩ : syracuseStep 21351925 = 2001743) B2001743
theorem B49229369 : Blo 1798100 49229369 := bstep (se 2 (by rfl) ⟨18461013, by rfl⟩ : syracuseStep 49229369 = 36922027) B36922027
theorem B6155833 : Blo 1798100 6155833 := bstep (se 2 (by rfl) ⟨2308437, by rfl⟩ : syracuseStep 6155833 = 4616875) B4616875
theorem B6073919 : Blo 1798100 6073919 := bstep (se 1 (by rfl) ⟨4555439, by rfl⟩ : syracuseStep 6073919 = 9110879) B9110879
theorem B2698859 : Blo 1798100 2698859 := bstep (se 1 (by rfl) ⟨2024144, by rfl⟩ : syracuseStep 2698859 = 4048289) B4048289
theorem B29191889 : Blo 1798100 29191889 := bstep (se 2 (by rfl) ⟨10946958, by rfl⟩ : syracuseStep 29191889 = 21893917) B21893917
theorem B2698985 : Blo 1798100 2698985 := bstep (se 2 (by rfl) ⟨1012119, by rfl⟩ : syracuseStep 2698985 = 2024239) B2024239
theorem B2699129 : Blo 1798100 2699129 := bstep (se 2 (by rfl) ⟨1012173, by rfl⟩ : syracuseStep 2699129 = 2024347) B2024347
theorem B20492189 : Blo 1798100 20492189 := bstep (se 3 (by rfl) ⟨3842285, by rfl⟩ : syracuseStep 20492189 = 7684571) B7684571
theorem B1798111 : Blo 1798100 1798111 := bstep (se 1 (by rfl) ⟨1348583, by rfl⟩ : syracuseStep 1798111 = 2697167) B2697167
theorem B2699231 : Blo 1798100 2699231 := bstep (se 1 (by rfl) ⟨2024423, by rfl⟩ : syracuseStep 2699231 = 4048847) B4048847
theorem B2699483 : Blo 1798100 2699483 := bstep (se 1 (by rfl) ⟨2024612, by rfl⟩ : syracuseStep 2699483 = 4049225) B4049225
theorem B1798375 : Blo 1798100 1798375 := bstep (se 1 (by rfl) ⟨1348781, by rfl⟩ : syracuseStep 1798375 = 2697563) B2697563
theorem B2699495 : Blo 1798100 2699495 := bstep (se 1 (by rfl) ⟨2024621, by rfl⟩ : syracuseStep 2699495 = 4049243) B4049243
theorem B6074621 : Blo 1798100 6074621 := bstep (se 3 (by rfl) ⟨1138991, by rfl⟩ : syracuseStep 6074621 = 2277983) B2277983
theorem B10383671 : Blo 1798100 10383671 := bstep (se 1 (by rfl) ⟨7787753, by rfl⟩ : syracuseStep 10383671 = 15575507) B15575507
theorem B26276183 : Blo 1798100 26276183 := bstep (se 1 (by rfl) ⟨19707137, by rfl⟩ : syracuseStep 26276183 = 39414275) B39414275
theorem B5468543 : Blo 1798100 5468543 := bstep (se 1 (by rfl) ⟨4101407, by rfl⟩ : syracuseStep 5468543 = 8202815) B8202815
theorem B1798527 : Blo 1798100 1798527 := bstep (se 1 (by rfl) ⟨1348895, by rfl⟩ : syracuseStep 1798527 = 2697791) B2697791
theorem B2699657 : Blo 1798100 2699657 := bstep (se 2 (by rfl) ⟨1012371, by rfl⟩ : syracuseStep 2699657 = 2024743) B2024743
theorem B1798607 : Blo 1798100 1798607 := bstep (se 1 (by rfl) ⟨1348955, by rfl⟩ : syracuseStep 1798607 = 2697911) B2697911
theorem B2699753 : Blo 1798100 2699753 := bstep (se 2 (by rfl) ⟨1012407, by rfl⟩ : syracuseStep 2699753 = 2024815) B2024815
theorem B1798759 : Blo 1798100 1798759 := bstep (se 1 (by rfl) ⟨1349069, by rfl⟩ : syracuseStep 1798759 = 2698139) B2698139
theorem B5698151 : Blo 1798100 5698151 := bstep (se 1 (by rfl) ⟨4273613, by rfl⟩ : syracuseStep 5698151 = 8547227) B8547227
theorem B2699879 : Blo 1798100 2699879 := bstep (se 1 (by rfl) ⟨2024909, by rfl⟩ : syracuseStep 2699879 = 4049819) B4049819
theorem B38900375 : Blo 1798100 38900375 := bstep (se 1 (by rfl) ⟨29175281, by rfl⟩ : syracuseStep 38900375 = 58350563) B58350563
theorem B2700011 : Blo 1798100 2700011 := bstep (se 1 (by rfl) ⟨2025008, by rfl⟩ : syracuseStep 2700011 = 4050017) B4050017
theorem B62329603 : Blo 1798100 62329603 := bstep (se 1 (by rfl) ⟨46747202, by rfl⟩ : syracuseStep 62329603 = 93494405) B93494405
theorem B2700041 : Blo 1798100 2700041 := bstep (se 2 (by rfl) ⟨1012515, by rfl⟩ : syracuseStep 2700041 = 2025031) B2025031
theorem B6075161 : Blo 1798100 6075161 := bstep (se 2 (by rfl) ⟨2278185, by rfl⟩ : syracuseStep 6075161 = 4556371) B4556371
theorem B18469709 : Blo 1798100 18469709 := bstep (se 3 (by rfl) ⟨3463070, by rfl⟩ : syracuseStep 18469709 = 6926141) B6926141
theorem B1799023 : Blo 1798100 1799023 := bstep (se 1 (by rfl) ⟨1349267, by rfl⟩ : syracuseStep 1799023 = 2698535) B2698535
theorem B2700143 : Blo 1798100 2700143 := bstep (se 1 (by rfl) ⟨2025107, by rfl⟩ : syracuseStep 2700143 = 4050215) B4050215
theorem B1799079 : Blo 1798100 1799079 := bstep (se 1 (by rfl) ⟨1349309, by rfl⟩ : syracuseStep 1799079 = 2698619) B2698619
theorem B1799163 : Blo 1798100 1799163 := bstep (se 1 (by rfl) ⟨1349372, by rfl⟩ : syracuseStep 1799163 = 2698745) B2698745
theorem B18469883 : Blo 1798100 18469883 := bstep (se 1 (by rfl) ⟨13852412, by rfl⟩ : syracuseStep 18469883 = 27704825) B27704825
theorem B5764135 : Blo 1798100 5764135 := bstep (se 1 (by rfl) ⟨4323101, by rfl⟩ : syracuseStep 5764135 = 8646203) B8646203
theorem B1799231 : Blo 1798100 1799231 := bstep (se 1 (by rfl) ⟨1349423, by rfl⟩ : syracuseStep 1799231 = 2698847) B2698847
theorem B9106505 : Blo 1798100 9106505 := bstep (se 2 (by rfl) ⟨3414939, by rfl⟩ : syracuseStep 9106505 = 6829879) B6829879
theorem B7681139 : Blo 1798100 7681139 := bstep (se 1 (by rfl) ⟨5760854, by rfl⟩ : syracuseStep 7681139 = 11521709) B11521709
theorem B1799375 : Blo 1798100 1799375 := bstep (se 1 (by rfl) ⟨1349531, by rfl⟩ : syracuseStep 1799375 = 2699063) B2699063
theorem B25924819 : Blo 1798100 25924819 := bstep (se 1 (by rfl) ⟨19443614, by rfl⟩ : syracuseStep 25924819 = 38887229) B38887229
theorem B43758953 : Blo 1798100 43758953 := bstep (se 2 (by rfl) ⟨16409607, by rfl⟩ : syracuseStep 43758953 = 32819215) B32819215
theorem B1799579 : Blo 1798100 1799579 := bstep (se 1 (by rfl) ⟨1349684, by rfl⟩ : syracuseStep 1799579 = 2699369) B2699369
theorem B5125531 : Blo 1798100 5125531 := bstep (se 1 (by rfl) ⟨3844148, by rfl⟩ : syracuseStep 5125531 = 7688297) B7688297
theorem B1799791 : Blo 1798100 1799791 := bstep (se 1 (by rfl) ⟨1349843, by rfl⟩ : syracuseStep 1799791 = 2699687) B2699687
theorem B2881145 : Blo 1798100 2881145 := bstep (se 2 (by rfl) ⟨1080429, by rfl⟩ : syracuseStep 2881145 = 2160859) B2160859
theorem B2922151 : Blo 1798100 2922151 := bstep (se 1 (by rfl) ⟨2191613, by rfl⟩ : syracuseStep 2922151 = 4383227) B4383227
theorem B1799847 : Blo 1798100 1799847 := bstep (se 1 (by rfl) ⟨1349885, by rfl⟩ : syracuseStep 1799847 = 2699771) B2699771
theorem B9107153 : Blo 1798100 9107153 := bstep (se 2 (by rfl) ⟨3415182, by rfl⟩ : syracuseStep 9107153 = 6830365) B6830365
theorem B3413755 : Blo 1798100 3413755 := bstep (se 1 (by rfl) ⟨2560316, by rfl⟩ : syracuseStep 3413755 = 5120633) B5120633
theorem B1799931 : Blo 1798100 1799931 := bstep (se 1 (by rfl) ⟨1349948, by rfl⟩ : syracuseStep 1799931 = 2699897) B2699897
theorem B1799967 : Blo 1798100 1799967 := bstep (se 1 (by rfl) ⟨1349975, by rfl⟩ : syracuseStep 1799967 = 2699951) B2699951
theorem B1799999 : Blo 1798100 1799999 := bstep (se 1 (by rfl) ⟨1349999, by rfl⟩ : syracuseStep 1799999 = 2699999) B2699999
theorem B3037007 : Blo 1798100 3037007 := bstep (se 1 (by rfl) ⟨2277755, by rfl⟩ : syracuseStep 3037007 = 4555511) B4555511
theorem B23066531 : Blo 1798100 23066531 := bstep (se 1 (by rfl) ⟨17299898, by rfl⟩ : syracuseStep 23066531 = 34599797) B34599797
theorem B7395311 : Blo 1798100 7395311 := bstep (se 1 (by rfl) ⟨5546483, by rfl⟩ : syracuseStep 7395311 = 11092967) B11092967
theorem B4552787 : Blo 1798100 4552787 := bstep (se 1 (by rfl) ⟨3414590, by rfl⟩ : syracuseStep 4552787 = 6829181) B6829181
theorem B11524295 : Blo 1798100 11524295 := bstep (se 1 (by rfl) ⟨8643221, by rfl⟩ : syracuseStep 11524295 = 17286443) B17286443
theorem B2275867 : Blo 1798100 2275867 := bstep (se 1 (by rfl) ⟨1706900, by rfl⟩ : syracuseStep 2275867 = 3413801) B3413801
theorem B4553273 : Blo 1798100 4553273 := bstep (se 2 (by rfl) ⟨1707477, by rfl⟩ : syracuseStep 4553273 = 3414955) B3414955
theorem B2734697 : Blo 1798100 2734697 := bstep (se 2 (by rfl) ⟨1025511, by rfl⟩ : syracuseStep 2734697 = 2051023) B2051023
theorem B13146745 : Blo 1798100 13146745 := bstep (se 2 (by rfl) ⟨4930029, by rfl⟩ : syracuseStep 13146745 = 9860059) B9860059
theorem B9730783 : Blo 1798100 9730783 := bstep (se 1 (by rfl) ⟨7298087, by rfl⟩ : syracuseStep 9730783 = 14596175) B14596175
theorem B3840851 : Blo 1798100 3840851 := bstep (se 1 (by rfl) ⟨2880638, by rfl⟩ : syracuseStep 3840851 = 5761277) B5761277
theorem B4324187 : Blo 1798100 4324187 := bstep (se 1 (by rfl) ⟨3243140, by rfl⟩ : syracuseStep 4324187 = 6486281) B6486281
theorem B49249295 : Blo 1798100 49249295 := bstep (se 1 (by rfl) ⟨36936971, by rfl⟩ : syracuseStep 49249295 = 73873943) B73873943
theorem B4045895 : Blo 1798100 4045895 := bstep (se 1 (by rfl) ⟨3034421, by rfl⟩ : syracuseStep 4045895 = 6068843) B6068843
theorem B2276687 : Blo 1798100 2276687 := bstep (se 1 (by rfl) ⟨1707515, by rfl⟩ : syracuseStep 2276687 = 3415031) B3415031
theorem B6069599 : Blo 1798100 6069599 := bstep (se 1 (by rfl) ⟨4552199, by rfl⟩ : syracuseStep 6069599 = 9104399) B9104399
theorem B24616325 : Blo 1798100 24616325 := bstep (se 4 (by rfl) ⟨2307780, by rfl⟩ : syracuseStep 24616325 = 4615561) B4615561
theorem B4046291 : Blo 1798100 4046291 := bstep (se 1 (by rfl) ⟨3034718, by rfl⟩ : syracuseStep 4046291 = 6069437) B6069437
theorem B2276839 : Blo 1798100 2276839 := bstep (se 1 (by rfl) ⟨1707629, by rfl⟩ : syracuseStep 2276839 = 3415259) B3415259
theorem B4554215 : Blo 1798100 4554215 := bstep (se 1 (by rfl) ⟨3415661, by rfl⟩ : syracuseStep 4554215 = 6831323) B6831323
theorem B2883047 : Blo 1798100 2883047 := bstep (se 1 (by rfl) ⟨2162285, by rfl⟩ : syracuseStep 2883047 = 4324571) B4324571
theorem B17284751 : Blo 1798100 17284751 := bstep (se 1 (by rfl) ⟨12963563, by rfl⟩ : syracuseStep 17284751 = 25927127) B25927127
theorem B10944143 : Blo 1798100 10944143 := bstep (se 1 (by rfl) ⟨8208107, by rfl⟩ : syracuseStep 10944143 = 16416215) B16416215
theorem B4046561 : Blo 1798100 4046561 := bstep (se 2 (by rfl) ⟨1517460, by rfl⟩ : syracuseStep 4046561 = 3034921) B3034921
theorem B11525935 : Blo 1798100 11525935 := bstep (se 1 (by rfl) ⟨8644451, by rfl⟩ : syracuseStep 11525935 = 17288903) B17288903
theorem B21880685 : Blo 1798100 21880685 := bstep (se 3 (by rfl) ⟨4102628, by rfl⟩ : syracuseStep 21880685 = 8205257) B8205257
theorem B6070139 : Blo 1798100 6070139 := bstep (se 1 (by rfl) ⟨4552604, by rfl⟩ : syracuseStep 6070139 = 9105209) B9105209
theorem B4047083 : Blo 1798100 4047083 := bstep (se 1 (by rfl) ⟨3035312, by rfl⟩ : syracuseStep 4047083 = 6070625) B6070625
theorem B3645695 : Blo 1798100 3645695 := bstep (se 1 (by rfl) ⟨2734271, by rfl⟩ : syracuseStep 3645695 = 5468543) B5468543
theorem B4555055 : Blo 1798100 4555055 := bstep (se 1 (by rfl) ⟨3416291, by rfl⟩ : syracuseStep 4555055 = 6832583) B6832583
theorem B12313139 : Blo 1798100 12313139 := bstep (se 1 (by rfl) ⟨9234854, by rfl⟩ : syracuseStep 12313139 = 18469709) B18469709
theorem B12313255 : Blo 1798100 12313255 := bstep (se 1 (by rfl) ⟨9234941, by rfl⟩ : syracuseStep 12313255 = 18469883) B18469883
theorem B6071003 : Blo 1798100 6071003 := bstep (se 1 (by rfl) ⟨4553252, by rfl⟩ : syracuseStep 6071003 = 9106505) B9106505
theorem B5120759 : Blo 1798100 5120759 := bstep (se 1 (by rfl) ⟨3840569, by rfl⟩ : syracuseStep 5120759 = 7681139) B7681139
theorem B27689789 : Blo 1798100 27689789 := bstep (se 3 (by rfl) ⟨5191835, by rfl⟩ : syracuseStep 27689789 = 10383671) B10383671
theorem B6071165 : Blo 1798100 6071165 := bstep (se 3 (by rfl) ⟨1138343, by rfl⟩ : syracuseStep 6071165 = 2276687) B2276687
theorem B29172635 : Blo 1798100 29172635 := bstep (se 1 (by rfl) ⟨21879476, by rfl⟩ : syracuseStep 29172635 = 43758953) B43758953
theorem B4047983 : Blo 1798100 4047983 := bstep (se 1 (by rfl) ⟨3035987, by rfl⟩ : syracuseStep 4047983 = 6071975) B6071975
theorem B6071435 : Blo 1798100 6071435 := bstep (se 1 (by rfl) ⟨4553576, by rfl⟩ : syracuseStep 6071435 = 9107153) B9107153
theorem B51897509 : Blo 1798100 51897509 := bstep (se 4 (by rfl) ⟨4865391, by rfl⟩ : syracuseStep 51897509 = 9730783) B9730783
theorem B9110717 : Blo 1798100 9110717 := bstep (se 3 (by rfl) ⟨1708259, by rfl⟩ : syracuseStep 9110717 = 3416519) B3416519
theorem B2024671 : Blo 1798100 2024671 := bstep (se 1 (by rfl) ⟨1518503, by rfl⟩ : syracuseStep 2024671 = 3037007) B3037007
theorem B15377687 : Blo 1798100 15377687 := bstep (se 1 (by rfl) ⟨11533265, by rfl⟩ : syracuseStep 15377687 = 23066531) B23066531
theorem B7685513 : Blo 1798100 7685513 := bstep (se 2 (by rfl) ⟨2882067, by rfl⟩ : syracuseStep 7685513 = 5764135) B5764135
theorem B7685563 : Blo 1798100 7685563 := bstep (se 1 (by rfl) ⟨5764172, by rfl⟩ : syracuseStep 7685563 = 11528345) B11528345
theorem B4048379 : Blo 1798100 4048379 := bstep (se 1 (by rfl) ⟨3036284, by rfl⟩ : syracuseStep 4048379 = 6072569) B6072569
theorem B4048415 : Blo 1798100 4048415 := bstep (se 1 (by rfl) ⟨3036311, by rfl⟩ : syracuseStep 4048415 = 6072623) B6072623
theorem B4048559 : Blo 1798100 4048559 := bstep (se 1 (by rfl) ⟨3036419, by rfl⟩ : syracuseStep 4048559 = 6072839) B6072839
theorem B6834041 : Blo 1798100 6834041 := bstep (se 2 (by rfl) ⟨2562765, by rfl⟩ : syracuseStep 6834041 = 5125531) B5125531
theorem B28469233 : Blo 1798100 28469233 := bstep (se 2 (by rfl) ⟨10675962, by rfl⟩ : syracuseStep 28469233 = 21351925) B21351925
theorem B2697263 : Blo 1798100 2697263 := bstep (se 1 (by rfl) ⟨2022947, by rfl⟩ : syracuseStep 2697263 = 4045895) B4045895
theorem B14583887 : Blo 1798100 14583887 := bstep (se 1 (by rfl) ⟨10937915, by rfl⟩ : syracuseStep 14583887 = 21875831) B21875831
theorem B4048991 : Blo 1798100 4048991 := bstep (se 1 (by rfl) ⟨3036743, by rfl⟩ : syracuseStep 4048991 = 6073487) B6073487
theorem B16410883 : Blo 1798100 16410883 := bstep (se 1 (by rfl) ⟨12308162, by rfl⟩ : syracuseStep 16410883 = 24616325) B24616325
theorem B2697527 : Blo 1798100 2697527 := bstep (se 1 (by rfl) ⟨2023145, by rfl⟩ : syracuseStep 2697527 = 4046291) B4046291
theorem B32819579 : Blo 1798100 32819579 := bstep (se 1 (by rfl) ⟨24614684, by rfl⟩ : syracuseStep 32819579 = 49229369) B49229369
theorem B4049279 : Blo 1798100 4049279 := bstep (se 1 (by rfl) ⟨3036959, by rfl⟩ : syracuseStep 4049279 = 6073919) B6073919
theorem B2697707 : Blo 1798100 2697707 := bstep (se 1 (by rfl) ⟨2023280, by rfl⟩ : syracuseStep 2697707 = 4046561) B4046561
theorem B19720829 : Blo 1798100 19720829 := bstep (se 3 (by rfl) ⟨3697655, by rfl⟩ : syracuseStep 19720829 = 7395311) B7395311
theorem B6073055 : Blo 1798100 6073055 := bstep (se 1 (by rfl) ⟨4554791, by rfl⟩ : syracuseStep 6073055 = 9109583) B9109583
theorem B4049747 : Blo 1798100 4049747 := bstep (se 1 (by rfl) ⟨3037310, by rfl⟩ : syracuseStep 4049747 = 6074621) B6074621
theorem B17517455 : Blo 1798100 17517455 := bstep (se 1 (by rfl) ⟨13138091, by rfl⟩ : syracuseStep 17517455 = 26276183) B26276183
theorem B2698409 : Blo 1798100 2698409 := bstep (se 2 (by rfl) ⟨1011903, by rfl⟩ : syracuseStep 2698409 = 2023807) B2023807
theorem B4050107 : Blo 1798100 4050107 := bstep (se 1 (by rfl) ⟨3037580, by rfl⟩ : syracuseStep 4050107 = 6075161) B6075161
theorem B5123321 : Blo 1798100 5123321 := bstep (se 2 (by rfl) ⟨1921245, by rfl⟩ : syracuseStep 5123321 = 3842491) B3842491
theorem B3034489 : Blo 1798100 3034489 := bstep (se 2 (by rfl) ⟨1137933, by rfl⟩ : syracuseStep 3034489 = 2275867) B2275867
theorem B15363539 : Blo 1798100 15363539 := bstep (se 1 (by rfl) ⟨11522654, by rfl⟩ : syracuseStep 15363539 = 23045309) B23045309
theorem B2698823 : Blo 1798100 2698823 := bstep (se 1 (by rfl) ⟨2024117, by rfl⟩ : syracuseStep 2698823 = 4048235) B4048235
theorem B6827753 : Blo 1798100 6827753 := bstep (se 2 (by rfl) ⟨2560407, by rfl⟩ : syracuseStep 6827753 = 5120815) B5120815
theorem B1920763 : Blo 1798100 1920763 := bstep (se 1 (by rfl) ⟨1440572, by rfl⟩ : syracuseStep 1920763 = 2881145) B2881145
theorem B2699003 : Blo 1798100 2699003 := bstep (se 1 (by rfl) ⟨2024252, by rfl⟩ : syracuseStep 2699003 = 4048505) B4048505
theorem B7688125 : Blo 1798100 7688125 := bstep (se 3 (by rfl) ⟨1441523, by rfl⟩ : syracuseStep 7688125 = 2883047) B2883047
theorem B1798127 : Blo 1798100 1798127 := bstep (se 1 (by rfl) ⟨1348595, by rfl⟩ : syracuseStep 1798127 = 2697191) B2697191
theorem B1798139 : Blo 1798100 1798139 := bstep (se 1 (by rfl) ⟨1348604, by rfl⟩ : syracuseStep 1798139 = 2697209) B2697209
theorem B3035191 : Blo 1798100 3035191 := bstep (se 1 (by rfl) ⟨2276393, by rfl⟩ : syracuseStep 3035191 = 4552787) B4552787
theorem B1798207 : Blo 1798100 1798207 := bstep (se 1 (by rfl) ⟨1348655, by rfl⟩ : syracuseStep 1798207 = 2697311) B2697311
theorem B1798247 : Blo 1798100 1798247 := bstep (se 1 (by rfl) ⟨1348685, by rfl⟩ : syracuseStep 1798247 = 2697371) B2697371
theorem B1798271 : Blo 1798100 1798271 := bstep (se 1 (by rfl) ⟨1348703, by rfl⟩ : syracuseStep 1798271 = 2697407) B2697407
theorem B1798299 : Blo 1798100 1798299 := bstep (se 1 (by rfl) ⟨1348724, by rfl⟩ : syracuseStep 1798299 = 2697449) B2697449
theorem B34566425 : Blo 1798100 34566425 := bstep (se 2 (by rfl) ⟨12962409, by rfl⟩ : syracuseStep 34566425 = 25924819) B25924819
theorem B1798503 : Blo 1798100 1798503 := bstep (se 1 (by rfl) ⟨1348877, by rfl⟩ : syracuseStep 1798503 = 2697755) B2697755
theorem B3035515 : Blo 1798100 3035515 := bstep (se 1 (by rfl) ⟨2276636, by rfl⟩ : syracuseStep 3035515 = 4553273) B4553273
theorem B1798555 : Blo 1798100 1798555 := bstep (se 1 (by rfl) ⟨1348916, by rfl⟩ : syracuseStep 1798555 = 2697833) B2697833
theorem B1823131 : Blo 1798100 1823131 := bstep (se 1 (by rfl) ⟨1367348, by rfl⟩ : syracuseStep 1823131 = 2734697) B2734697
theorem B2699675 : Blo 1798100 2699675 := bstep (se 1 (by rfl) ⟨2024756, by rfl⟩ : syracuseStep 2699675 = 4049513) B4049513
theorem B10383859 : Blo 1798100 10383859 := bstep (se 1 (by rfl) ⟨7787894, by rfl⟩ : syracuseStep 10383859 = 15575789) B15575789
theorem B2560567 : Blo 1798100 2560567 := bstep (se 1 (by rfl) ⟨1920425, by rfl⟩ : syracuseStep 2560567 = 3840851) B3840851
theorem B3035785 : Blo 1798100 3035785 := bstep (se 2 (by rfl) ⟨1138419, by rfl⟩ : syracuseStep 3035785 = 2276839) B2276839
theorem B1798907 : Blo 1798100 1798907 := bstep (se 1 (by rfl) ⟨1349180, by rfl⟩ : syracuseStep 1798907 = 2698361) B2698361
theorem B1798975 : Blo 1798100 1798975 := bstep (se 1 (by rfl) ⟨1349231, by rfl⟩ : syracuseStep 1798975 = 2698463) B2698463
theorem B2700095 : Blo 1798100 2700095 := bstep (se 1 (by rfl) ⟨2025071, by rfl⟩ : syracuseStep 2700095 = 4050143) B4050143
theorem B1799003 : Blo 1798100 1799003 := bstep (se 1 (by rfl) ⟨1349252, by rfl⟩ : syracuseStep 1799003 = 2698505) B2698505
theorem B3896201 : Blo 1798100 3896201 := bstep (se 2 (by rfl) ⟨1461075, by rfl⟩ : syracuseStep 3896201 = 2922151) B2922151
theorem B1799071 : Blo 1798100 1799071 := bstep (se 1 (by rfl) ⟨1349303, by rfl⟩ : syracuseStep 1799071 = 2698607) B2698607
theorem B1799151 : Blo 1798100 1799151 := bstep (se 1 (by rfl) ⟨1349363, by rfl⟩ : syracuseStep 1799151 = 2698727) B2698727
theorem B3036143 : Blo 1798100 3036143 := bstep (se 1 (by rfl) ⟨2277107, by rfl⟩ : syracuseStep 3036143 = 4554215) B4554215
theorem B4551673 : Blo 1798100 4551673 := bstep (se 2 (by rfl) ⟨1706877, by rfl⟩ : syracuseStep 4551673 = 3413755) B3413755
theorem B1799239 : Blo 1798100 1799239 := bstep (se 1 (by rfl) ⟨1349429, by rfl⟩ : syracuseStep 1799239 = 2698859) B2698859
theorem B11523167 : Blo 1798100 11523167 := bstep (se 1 (by rfl) ⟨8642375, by rfl⟩ : syracuseStep 11523167 = 17284751) B17284751
theorem B7296095 : Blo 1798100 7296095 := bstep (se 1 (by rfl) ⟨5472071, by rfl⟩ : syracuseStep 7296095 = 10944143) B10944143
theorem B19461259 : Blo 1798100 19461259 := bstep (se 1 (by rfl) ⟨14595944, by rfl⟩ : syracuseStep 19461259 = 29191889) B29191889
theorem B1799323 : Blo 1798100 1799323 := bstep (se 1 (by rfl) ⟨1349492, by rfl⟩ : syracuseStep 1799323 = 2698985) B2698985
theorem B14587123 : Blo 1798100 14587123 := bstep (se 1 (by rfl) ⟨10940342, by rfl⟩ : syracuseStep 14587123 = 21880685) B21880685
theorem B1799419 : Blo 1798100 1799419 := bstep (se 1 (by rfl) ⟨1349564, by rfl⟩ : syracuseStep 1799419 = 2699129) B2699129
theorem B13661459 : Blo 1798100 13661459 := bstep (se 1 (by rfl) ⟨10246094, by rfl⟩ : syracuseStep 13661459 = 20492189) B20492189
theorem B1799487 : Blo 1798100 1799487 := bstep (se 1 (by rfl) ⟨1349615, by rfl⟩ : syracuseStep 1799487 = 2699231) B2699231
theorem B1799655 : Blo 1798100 1799655 := bstep (se 1 (by rfl) ⟨1349741, by rfl⟩ : syracuseStep 1799655 = 2699483) B2699483
theorem B1799663 : Blo 1798100 1799663 := bstep (se 1 (by rfl) ⟨1349747, by rfl⟩ : syracuseStep 1799663 = 2699495) B2699495
theorem B39441979 : Blo 1798100 39441979 := bstep (se 1 (by rfl) ⟨29581484, by rfl⟩ : syracuseStep 39441979 = 59162969) B59162969
theorem B1799771 : Blo 1798100 1799771 := bstep (se 1 (by rfl) ⟨1349828, by rfl⟩ : syracuseStep 1799771 = 2699657) B2699657
theorem B1799835 : Blo 1798100 1799835 := bstep (se 1 (by rfl) ⟨1349876, by rfl⟩ : syracuseStep 1799835 = 2699753) B2699753
theorem B3798767 : Blo 1798100 3798767 := bstep (se 1 (by rfl) ⟨2849075, by rfl⟩ : syracuseStep 3798767 = 5698151) B5698151
theorem B1799919 : Blo 1798100 1799919 := bstep (se 1 (by rfl) ⟨1349939, by rfl⟩ : syracuseStep 1799919 = 2699879) B2699879
theorem B25933583 : Blo 1798100 25933583 := bstep (se 1 (by rfl) ⟨19450187, by rfl⟩ : syracuseStep 25933583 = 38900375) B38900375
theorem B6829865 : Blo 1798100 6829865 := bstep (se 2 (by rfl) ⟨2561199, by rfl⟩ : syracuseStep 6829865 = 5122399) B5122399
theorem B10245959 : Blo 1798100 10245959 := bstep (se 1 (by rfl) ⟨7684469, by rfl⟩ : syracuseStep 10245959 = 15368939) B15368939
theorem B1800007 : Blo 1798100 1800007 := bstep (se 1 (by rfl) ⟨1350005, by rfl⟩ : syracuseStep 1800007 = 2700011) B2700011
theorem B1800027 : Blo 1798100 1800027 := bstep (se 1 (by rfl) ⟨1350020, by rfl⟩ : syracuseStep 1800027 = 2700041) B2700041
theorem B1800095 : Blo 1798100 1800095 := bstep (se 1 (by rfl) ⟨1350071, by rfl⟩ : syracuseStep 1800095 = 2700143) B2700143
theorem B11524193 : Blo 1798100 11524193 := bstep (se 2 (by rfl) ⟨4321572, by rfl⟩ : syracuseStep 11524193 = 8643145) B8643145
theorem B17528993 : Blo 1798100 17528993 := bstep (se 2 (by rfl) ⟨6573372, by rfl⟩ : syracuseStep 17528993 = 13146745) B13146745
theorem B4102483 : Blo 1798100 4102483 := bstep (se 1 (by rfl) ⟨3076862, by rfl⟩ : syracuseStep 4102483 = 6153725) B6153725
theorem B83106137 : Blo 1798100 83106137 := bstep (se 2 (by rfl) ⟨31164801, by rfl⟩ : syracuseStep 83106137 = 62329603) B62329603
theorem B6920587 : Blo 1798100 6920587 := bstep (se 1 (by rfl) ⟨5190440, by rfl⟩ : syracuseStep 6920587 = 10380881) B10380881
theorem B17291825 : Blo 1798100 17291825 := bstep (se 2 (by rfl) ⟨6484434, by rfl⟩ : syracuseStep 17291825 = 12968869) B12968869
theorem B7682863 : Blo 1798100 7682863 := bstep (se 1 (by rfl) ⟨5762147, by rfl⟩ : syracuseStep 7682863 = 11524295) B11524295
theorem B13319225 : Blo 1798100 13319225 := bstep (se 2 (by rfl) ⟨4994709, by rfl⟩ : syracuseStep 13319225 = 9989419) B9989419
theorem B6069383 : Blo 1798100 6069383 := bstep (se 1 (by rfl) ⟨4552037, by rfl⟩ : syracuseStep 6069383 = 9104075) B9104075
theorem B14032019 : Blo 1798100 14032019 := bstep (se 1 (by rfl) ⟨10524014, by rfl⟩ : syracuseStep 14032019 = 21048029) B21048029
theorem B2882791 : Blo 1798100 2882791 := bstep (se 1 (by rfl) ⟨2162093, by rfl⟩ : syracuseStep 2882791 = 4324187) B4324187
theorem B15375703 : Blo 1798100 15375703 := bstep (se 1 (by rfl) ⟨11531777, by rfl⟩ : syracuseStep 15375703 = 23063555) B23063555
theorem B32832863 : Blo 1798100 32832863 := bstep (se 1 (by rfl) ⟨24624647, by rfl⟩ : syracuseStep 32832863 = 49249295) B49249295
theorem B13852037 : Blo 1798100 13852037 := bstep (se 4 (by rfl) ⟨1298628, by rfl⟩ : syracuseStep 13852037 = 2597257) B2597257
theorem B8207777 : Blo 1798100 8207777 := bstep (se 2 (by rfl) ⟨3077916, by rfl⟩ : syracuseStep 8207777 = 6155833) B6155833
theorem B4046399 : Blo 1798100 4046399 := bstep (se 1 (by rfl) ⟨3034799, by rfl⟩ : syracuseStep 4046399 = 6069599) B6069599
theorem B15367913 : Blo 1798100 15367913 := bstep (se 2 (by rfl) ⟨5762967, by rfl⟩ : syracuseStep 15367913 = 11525935) B11525935
theorem B4046759 : Blo 1798100 4046759 := bstep (se 1 (by rfl) ⟨3035069, by rfl⟩ : syracuseStep 4046759 = 6070139) B6070139
theorem B4046921 : Blo 1798100 4046921 := bstep (se 2 (by rfl) ⟨1517595, by rfl⟩ : syracuseStep 4046921 = 3035191) B3035191
theorem B23044283 : Blo 1798100 23044283 := bstep (se 1 (by rfl) ⟨17283212, by rfl⟩ : syracuseStep 23044283 = 34566425) B34566425
theorem B21881177 : Blo 1798100 21881177 := bstep (se 2 (by rfl) ⟨8205441, by rfl⟩ : syracuseStep 21881177 = 16410883) B16410883
theorem B4047335 : Blo 1798100 4047335 := bstep (se 1 (by rfl) ⟨3035501, by rfl⟩ : syracuseStep 4047335 = 6071003) B6071003
theorem B4047353 : Blo 1798100 4047353 := bstep (se 2 (by rfl) ⟨1517757, by rfl⟩ : syracuseStep 4047353 = 3035515) B3035515
theorem B4047443 : Blo 1798100 4047443 := bstep (se 1 (by rfl) ⟨3035582, by rfl⟩ : syracuseStep 4047443 = 6071165) B6071165
theorem B19448423 : Blo 1798100 19448423 := bstep (se 1 (by rfl) ⟨14586317, by rfl⟩ : syracuseStep 19448423 = 29172635) B29172635
theorem B2024095 : Blo 1798100 2024095 := bstep (se 1 (by rfl) ⟨1518071, by rfl⟩ : syracuseStep 2024095 = 3036143) B3036143
theorem B4047623 : Blo 1798100 4047623 := bstep (se 1 (by rfl) ⟨3035717, by rfl⟩ : syracuseStep 4047623 = 6071435) B6071435
theorem B4047713 : Blo 1798100 4047713 := bstep (se 2 (by rfl) ⟨1517892, by rfl⟩ : syracuseStep 4047713 = 3035785) B3035785
theorem B16417673 : Blo 1798100 16417673 := bstep (se 2 (by rfl) ⟨6156627, by rfl⟩ : syracuseStep 16417673 = 12313255) B12313255
theorem B2532511 : Blo 1798100 2532511 := bstep (se 1 (by rfl) ⟨1899383, by rfl⟩ : syracuseStep 2532511 = 3798767) B3798767
theorem B4556027 : Blo 1798100 4556027 := bstep (se 1 (by rfl) ⟨3417020, by rfl⟩ : syracuseStep 4556027 = 6834041) B6834041
theorem B55404091 : Blo 1798100 55404091 := bstep (se 1 (by rfl) ⟨41553068, by rfl⟩ : syracuseStep 55404091 = 83106137) B83106137
theorem B3843721 : Blo 1798100 3843721 := bstep (se 2 (by rfl) ⟨1441395, by rfl⟩ : syracuseStep 3843721 = 2882791) B2882791
theorem B19449497 : Blo 1798100 19449497 := bstep (se 2 (by rfl) ⟨7293561, by rfl⟩ : syracuseStep 19449497 = 14587123) B14587123
theorem B11527883 : Blo 1798100 11527883 := bstep (se 1 (by rfl) ⟨8645912, by rfl⟩ : syracuseStep 11527883 = 17291825) B17291825
theorem B4048703 : Blo 1798100 4048703 := bstep (se 1 (by rfl) ⟨3036527, by rfl⟩ : syracuseStep 4048703 = 6073055) B6073055
theorem B9234691 : Blo 1798100 9234691 := bstep (se 1 (by rfl) ⟨6926018, by rfl⟩ : syracuseStep 9234691 = 13852037) B13852037
theorem B10242359 : Blo 1798100 10242359 := bstep (se 1 (by rfl) ⟨7681769, by rfl⟩ : syracuseStep 10242359 = 15363539) B15363539
theorem B10389869 : Blo 1798100 10389869 := bstep (se 3 (by rfl) ⟨1948100, by rfl⟩ : syracuseStep 10389869 = 3896201) B3896201
theorem B2697599 : Blo 1798100 2697599 := bstep (se 1 (by rfl) ⟨2023199, by rfl⟩ : syracuseStep 2697599 = 4046399) B4046399
theorem B10250833 : Blo 1798100 10250833 := bstep (se 2 (by rfl) ⟨3844062, by rfl⟩ : syracuseStep 10250833 = 7688125) B7688125
theorem B55380581 : Blo 1798100 55380581 := bstep (se 4 (by rfl) ⟨5191929, by rfl⟩ : syracuseStep 55380581 = 10383859) B10383859
theorem B2697839 : Blo 1798100 2697839 := bstep (se 1 (by rfl) ⟨2023379, by rfl⟩ : syracuseStep 2697839 = 4046759) B4046759
theorem B2698055 : Blo 1798100 2698055 := bstep (se 1 (by rfl) ⟨2023541, by rfl⟩ : syracuseStep 2698055 = 4047083) B4047083
theorem B9227449 : Blo 1798100 9227449 := bstep (se 2 (by rfl) ⟨3460293, by rfl⟩ : syracuseStep 9227449 = 6920587) B6920587
theorem B18459859 : Blo 1798100 18459859 := bstep (se 1 (by rfl) ⟨13844894, by rfl⟩ : syracuseStep 18459859 = 27689789) B27689789
theorem B2698655 : Blo 1798100 2698655 := bstep (se 1 (by rfl) ⟨2023991, by rfl⟩ : syracuseStep 2698655 = 4047983) B4047983
theorem B34598339 : Blo 1798100 34598339 := bstep (se 1 (by rfl) ⟨25948754, by rfl⟩ : syracuseStep 34598339 = 51897509) B51897509
theorem B6073811 : Blo 1798100 6073811 := bstep (se 1 (by rfl) ⟨4555358, by rfl⟩ : syracuseStep 6073811 = 9110717) B9110717
theorem B10251791 : Blo 1798100 10251791 := bstep (se 1 (by rfl) ⟨7688843, by rfl⟩ : syracuseStep 10251791 = 15377687) B15377687
theorem B5123675 : Blo 1798100 5123675 := bstep (se 1 (by rfl) ⟨3842756, by rfl⟩ : syracuseStep 5123675 = 7685513) B7685513
theorem B2698919 : Blo 1798100 2698919 := bstep (se 1 (by rfl) ⟨2024189, by rfl⟩ : syracuseStep 2698919 = 4048379) B4048379
theorem B2698943 : Blo 1798100 2698943 := bstep (se 1 (by rfl) ⟨2024207, by rfl⟩ : syracuseStep 2698943 = 4048415) B4048415
theorem B10243817 : Blo 1798100 10243817 := bstep (se 2 (by rfl) ⟨3841431, by rfl⟩ : syracuseStep 10243817 = 7682863) B7682863
theorem B2699039 : Blo 1798100 2699039 := bstep (se 1 (by rfl) ⟨2024279, by rfl⟩ : syracuseStep 2699039 = 4048559) B4048559
theorem B17289055 : Blo 1798100 17289055 := bstep (se 1 (by rfl) ⟨12966791, by rfl⟩ : syracuseStep 17289055 = 25933583) B25933583
theorem B10244069 : Blo 1798100 10244069 := bstep (se 4 (by rfl) ⟨960381, by rfl⟩ : syracuseStep 10244069 = 1920763) B1920763
theorem B1798175 : Blo 1798100 1798175 := bstep (se 1 (by rfl) ⟨1348631, by rfl⟩ : syracuseStep 1798175 = 2697263) B2697263
theorem B2699327 : Blo 1798100 2699327 := bstep (se 1 (by rfl) ⟨2024495, by rfl⟩ : syracuseStep 2699327 = 4048991) B4048991
theorem B11685995 : Blo 1798100 11685995 := bstep (se 1 (by rfl) ⟨8764496, by rfl⟩ : syracuseStep 11685995 = 17528993) B17528993
theorem B25948345 : Blo 1798100 25948345 := bstep (se 2 (by rfl) ⟨9730629, by rfl⟩ : syracuseStep 25948345 = 19461259) B19461259
theorem B1798351 : Blo 1798100 1798351 := bstep (se 1 (by rfl) ⟨1348763, by rfl⟩ : syracuseStep 1798351 = 2697527) B2697527
theorem B2699519 : Blo 1798100 2699519 := bstep (se 1 (by rfl) ⟨2024639, by rfl⟩ : syracuseStep 2699519 = 4049279) B4049279
theorem B2699561 : Blo 1798100 2699561 := bstep (se 2 (by rfl) ⟨1012335, by rfl⟩ : syracuseStep 2699561 = 2024671) B2024671
theorem B1798471 : Blo 1798100 1798471 := bstep (se 1 (by rfl) ⟨1348853, by rfl⟩ : syracuseStep 1798471 = 2697707) B2697707
theorem B20500937 : Blo 1798100 20500937 := bstep (se 2 (by rfl) ⟨7687851, by rfl⟩ : syracuseStep 20500937 = 15375703) B15375703
theorem B2699831 : Blo 1798100 2699831 := bstep (se 1 (by rfl) ⟨2024873, by rfl⟩ : syracuseStep 2699831 = 4049747) B4049747
theorem B11678303 : Blo 1798100 11678303 := bstep (se 1 (by rfl) ⟨8758727, by rfl⟩ : syracuseStep 11678303 = 17517455) B17517455
theorem B52589305 : Blo 1798100 52589305 := bstep (se 2 (by rfl) ⟨19720989, by rfl⟩ : syracuseStep 52589305 = 39441979) B39441979
theorem B1798939 : Blo 1798100 1798939 := bstep (se 1 (by rfl) ⟨1349204, by rfl⟩ : syracuseStep 1798939 = 2698409) B2698409
theorem B2700071 : Blo 1798100 2700071 := bstep (se 1 (by rfl) ⟨2025053, by rfl⟩ : syracuseStep 2700071 = 4050107) B4050107
theorem B1799215 : Blo 1798100 1799215 := bstep (se 1 (by rfl) ⟨1349411, by rfl⟩ : syracuseStep 1799215 = 2698823) B2698823
theorem B4551835 : Blo 1798100 4551835 := bstep (se 1 (by rfl) ⟨3413876, by rfl⟩ : syracuseStep 4551835 = 6827753) B6827753
theorem B10245275 : Blo 1798100 10245275 := bstep (se 1 (by rfl) ⟨7683956, by rfl⟩ : syracuseStep 10245275 = 15367913) B15367913
theorem B1799335 : Blo 1798100 1799335 := bstep (se 1 (by rfl) ⟨1349501, by rfl⟩ : syracuseStep 1799335 = 2699003) B2699003
theorem B37958977 : Blo 1798100 37958977 := bstep (se 2 (by rfl) ⟨14234616, by rfl⟩ : syracuseStep 37958977 = 28469233) B28469233
theorem B3036703 : Blo 1798100 3036703 := bstep (se 1 (by rfl) ⟨2277527, by rfl⟩ : syracuseStep 3036703 = 4555055) B4555055
theorem B1799783 : Blo 1798100 1799783 := bstep (se 1 (by rfl) ⟨1349837, by rfl⟩ : syracuseStep 1799783 = 2699675) B2699675
theorem B5469977 : Blo 1798100 5469977 := bstep (se 2 (by rfl) ⟨2051241, by rfl⟩ : syracuseStep 5469977 = 4102483) B4102483
theorem B3413839 : Blo 1798100 3413839 := bstep (se 1 (by rfl) ⟨2560379, by rfl⟩ : syracuseStep 3413839 = 5120759) B5120759
theorem B131340149 : Blo 1798100 131340149 := bstep (se 5 (by rfl) ⟨6156569, by rfl⟩ : syracuseStep 131340149 = 12313139) B12313139
theorem B1800063 : Blo 1798100 1800063 := bstep (se 1 (by rfl) ⟨1350047, by rfl⟩ : syracuseStep 1800063 = 2700095) B2700095
theorem B9721853 : Blo 1798100 9721853 := bstep (se 3 (by rfl) ⟨1822847, by rfl⟩ : syracuseStep 9721853 = 3645695) B3645695
theorem B7682111 : Blo 1798100 7682111 := bstep (se 1 (by rfl) ⟨5761583, by rfl⟩ : syracuseStep 7682111 = 11523167) B11523167
theorem B4864063 : Blo 1798100 4864063 := bstep (se 1 (by rfl) ⟨3648047, by rfl⟩ : syracuseStep 4864063 = 7296095) B7296095
theorem B3414089 : Blo 1798100 3414089 := bstep (se 2 (by rfl) ⟨1280283, by rfl⟩ : syracuseStep 3414089 = 2560567) B2560567
theorem B9107639 : Blo 1798100 9107639 := bstep (se 1 (by rfl) ⟨6830729, by rfl⟩ : syracuseStep 9107639 = 13661459) B13661459
theorem B21887405 : Blo 1798100 21887405 := bstep (se 3 (by rfl) ⟨4103888, by rfl⟩ : syracuseStep 21887405 = 8207777) B8207777
theorem B4553243 : Blo 1798100 4553243 := bstep (se 1 (by rfl) ⟨3414932, by rfl⟩ : syracuseStep 4553243 = 6829865) B6829865
theorem B6830639 : Blo 1798100 6830639 := bstep (se 1 (by rfl) ⟨5122979, by rfl⟩ : syracuseStep 6830639 = 10245959) B10245959
theorem B6068897 : Blo 1798100 6068897 := bstep (se 2 (by rfl) ⟨2275836, by rfl⟩ : syracuseStep 6068897 = 4551673) B4551673
theorem B9722591 : Blo 1798100 9722591 := bstep (se 1 (by rfl) ⟨7291943, by rfl⟩ : syracuseStep 9722591 = 14583887) B14583887
theorem B7682795 : Blo 1798100 7682795 := bstep (se 1 (by rfl) ⟨5762096, by rfl⟩ : syracuseStep 7682795 = 11524193) B11524193
theorem B21879719 : Blo 1798100 21879719 := bstep (se 1 (by rfl) ⟨16409789, by rfl⟩ : syracuseStep 21879719 = 32819579) B32819579
theorem B13147219 : Blo 1798100 13147219 := bstep (se 1 (by rfl) ⟨9860414, by rfl⟩ : syracuseStep 13147219 = 19720829) B19720829
theorem B4045985 : Blo 1798100 4045985 := bstep (se 2 (by rfl) ⟨1517244, by rfl⟩ : syracuseStep 4045985 = 3034489) B3034489
theorem B10247417 : Blo 1798100 10247417 := bstep (se 2 (by rfl) ⟨3842781, by rfl⟩ : syracuseStep 10247417 = 7685563) B7685563
theorem B8879483 : Blo 1798100 8879483 := bstep (se 1 (by rfl) ⟨6659612, by rfl⟩ : syracuseStep 8879483 = 13319225) B13319225
theorem B4046255 : Blo 1798100 4046255 := bstep (se 1 (by rfl) ⟨3034691, by rfl⟩ : syracuseStep 4046255 = 6069383) B6069383
theorem B9354679 : Blo 1798100 9354679 := bstep (se 1 (by rfl) ⟨7016009, by rfl⟩ : syracuseStep 9354679 = 14032019) B14032019
theorem B9723365 : Blo 1798100 9723365 := bstep (se 4 (by rfl) ⟨911565, by rfl⟩ : syracuseStep 9723365 = 1823131) B1823131
theorem B3415547 : Blo 1798100 3415547 := bstep (se 1 (by rfl) ⟨2561660, by rfl⟩ : syracuseStep 3415547 = 5123321) B5123321
theorem B21888575 : Blo 1798100 21888575 := bstep (se 1 (by rfl) ⟨16416431, by rfl⟩ : syracuseStep 21888575 = 32832863) B32832863
theorem B7790663 : Blo 1798100 7790663 := bstep (se 1 (by rfl) ⟨5842997, by rfl⟩ : syracuseStep 7790663 = 11685995) B11685995
theorem B10945115 : Blo 1798100 10945115 := bstep (se 1 (by rfl) ⟨8208836, by rfl⟩ : syracuseStep 10945115 = 16417673) B16417673
theorem B7685255 : Blo 1798100 7685255 := bstep (se 1 (by rfl) ⟨5763941, by rfl⟩ : syracuseStep 7685255 = 11527883) B11527883
theorem B3646651 : Blo 1798100 3646651 := bstep (se 1 (by rfl) ⟨2734988, by rfl⟩ : syracuseStep 3646651 = 5469977) B5469977
theorem B6481235 : Blo 1798100 6481235 := bstep (se 1 (by rfl) ⟨4860926, by rfl⟩ : syracuseStep 6481235 = 9721853) B9721853
theorem B49251685 : Blo 1798100 49251685 := bstep (se 4 (by rfl) ⟨4617345, by rfl⟩ : syracuseStep 49251685 = 9234691) B9234691
theorem B5121407 : Blo 1798100 5121407 := bstep (se 1 (by rfl) ⟨3841055, by rfl⟩ : syracuseStep 5121407 = 7682111) B7682111
theorem B6071759 : Blo 1798100 6071759 := bstep (se 1 (by rfl) ⟨4553819, by rfl⟩ : syracuseStep 6071759 = 9107639) B9107639
theorem B14591603 : Blo 1798100 14591603 := bstep (se 1 (by rfl) ⟨10943702, by rfl⟩ : syracuseStep 14591603 = 21887405) B21887405
theorem B50611969 : Blo 1798100 50611969 := bstep (se 2 (by rfl) ⟨18979488, by rfl⟩ : syracuseStep 50611969 = 37958977) B37958977
theorem B6481727 : Blo 1798100 6481727 := bstep (se 1 (by rfl) ⟨4861295, by rfl⟩ : syracuseStep 6481727 = 9722591) B9722591
theorem B5121863 : Blo 1798100 5121863 := bstep (se 1 (by rfl) ⟨3841397, by rfl⟩ : syracuseStep 5121863 = 7682795) B7682795
theorem B4048937 : Blo 1798100 4048937 := bstep (se 2 (by rfl) ⟨1518351, by rfl⟩ : syracuseStep 4048937 = 3036703) B3036703
theorem B2697323 : Blo 1798100 2697323 := bstep (se 1 (by rfl) ⟨2022992, by rfl⟩ : syracuseStep 2697323 = 4045985) B4045985
theorem B2697503 : Blo 1798100 2697503 := bstep (se 1 (by rfl) ⟨2023127, by rfl⟩ : syracuseStep 2697503 = 4046255) B4046255
theorem B49891621 : Blo 1798100 49891621 := bstep (se 4 (by rfl) ⟨4677339, by rfl⟩ : syracuseStep 49891621 = 9354679) B9354679
theorem B4049207 : Blo 1798100 4049207 := bstep (se 1 (by rfl) ⟨3036905, by rfl⟩ : syracuseStep 4049207 = 6073811) B6073811
theorem B6482243 : Blo 1798100 6482243 := bstep (se 1 (by rfl) ⟨4861682, by rfl⟩ : syracuseStep 6482243 = 9723365) B9723365
theorem B6834527 : Blo 1798100 6834527 := bstep (se 1 (by rfl) ⟨5125895, by rfl⟩ : syracuseStep 6834527 = 10251791) B10251791
theorem B14592383 : Blo 1798100 14592383 := bstep (se 1 (by rfl) ⟨10944287, by rfl⟩ : syracuseStep 14592383 = 21888575) B21888575
theorem B2697947 : Blo 1798100 2697947 := bstep (se 1 (by rfl) ⟨2023460, by rfl⟩ : syracuseStep 2697947 = 4046921) B4046921
theorem B15362855 : Blo 1798100 15362855 := bstep (se 1 (by rfl) ⟨11522141, by rfl⟩ : syracuseStep 15362855 = 23044283) B23044283
theorem B9104237 : Blo 1798100 9104237 := bstep (se 3 (by rfl) ⟨1707044, by rfl⟩ : syracuseStep 9104237 = 3414089) B3414089
theorem B34597793 : Blo 1798100 34597793 := bstep (se 2 (by rfl) ⟨12974172, by rfl⟩ : syracuseStep 34597793 = 25948345) B25948345
theorem B13667291 : Blo 1798100 13667291 := bstep (se 1 (by rfl) ⟨10250468, by rfl⟩ : syracuseStep 13667291 = 20500937) B20500937
theorem B2698223 : Blo 1798100 2698223 := bstep (se 1 (by rfl) ⟨2023667, by rfl⟩ : syracuseStep 2698223 = 4047335) B4047335
theorem B2698235 : Blo 1798100 2698235 := bstep (se 1 (by rfl) ⟨2023676, by rfl⟩ : syracuseStep 2698235 = 4047353) B4047353
theorem B2698295 : Blo 1798100 2698295 := bstep (se 1 (by rfl) ⟨2023721, by rfl⟩ : syracuseStep 2698295 = 4047443) B4047443
theorem B2698415 : Blo 1798100 2698415 := bstep (se 1 (by rfl) ⟨2023811, by rfl⟩ : syracuseStep 2698415 = 4047623) B4047623
theorem B2698475 : Blo 1798100 2698475 := bstep (se 1 (by rfl) ⟨2023856, by rfl⟩ : syracuseStep 2698475 = 4047713) B4047713
theorem B13667777 : Blo 1798100 13667777 := bstep (se 2 (by rfl) ⟨5125416, by rfl⟩ : syracuseStep 13667777 = 10250833) B10250833
theorem B2698793 : Blo 1798100 2698793 := bstep (se 2 (by rfl) ⟨1012047, by rfl⟩ : syracuseStep 2698793 = 2024095) B2024095
theorem B70119073 : Blo 1798100 70119073 := bstep (se 2 (by rfl) ⟨26294652, by rfl⟩ : syracuseStep 70119073 = 52589305) B52589305
theorem B2699135 : Blo 1798100 2699135 := bstep (se 1 (by rfl) ⟨2024351, by rfl⟩ : syracuseStep 2699135 = 4048703) B4048703
theorem B87560099 : Blo 1798100 87560099 := bstep (se 1 (by rfl) ⟨65670074, by rfl⟩ : syracuseStep 87560099 = 131340149) B131340149
theorem B6828239 : Blo 1798100 6828239 := bstep (se 1 (by rfl) ⟨5121179, by rfl⟩ : syracuseStep 6828239 = 10242359) B10242359
theorem B6926579 : Blo 1798100 6926579 := bstep (se 1 (by rfl) ⟨5194934, by rfl⟩ : syracuseStep 6926579 = 10389869) B10389869
theorem B31142141 : Blo 1798100 31142141 := bstep (se 3 (by rfl) ⟨5839151, by rfl⟩ : syracuseStep 31142141 = 11678303) B11678303
theorem B1798399 : Blo 1798100 1798399 := bstep (se 1 (by rfl) ⟨1348799, by rfl⟩ : syracuseStep 1798399 = 2697599) B2697599
theorem B24613145 : Blo 1798100 24613145 := bstep (se 2 (by rfl) ⟨9229929, by rfl⟩ : syracuseStep 24613145 = 18459859) B18459859
theorem B3035495 : Blo 1798100 3035495 := bstep (se 1 (by rfl) ⟨2276621, by rfl⟩ : syracuseStep 3035495 = 4553243) B4553243
theorem B1798559 : Blo 1798100 1798559 := bstep (se 1 (by rfl) ⟨1348919, by rfl⟩ : syracuseStep 1798559 = 2697839) B2697839
theorem B1798703 : Blo 1798100 1798703 := bstep (se 1 (by rfl) ⟨1349027, by rfl⟩ : syracuseStep 1798703 = 2698055) B2698055
theorem B14586479 : Blo 1798100 14586479 := bstep (se 1 (by rfl) ⟨10939859, by rfl⟩ : syracuseStep 14586479 = 21879719) B21879719
theorem B73872121 : Blo 1798100 73872121 := bstep (se 2 (by rfl) ⟨27702045, by rfl⟩ : syracuseStep 73872121 = 55404091) B55404091
theorem B5124961 : Blo 1798100 5124961 := bstep (se 2 (by rfl) ⟨1921860, by rfl⟩ : syracuseStep 5124961 = 3843721) B3843721
theorem B5919655 : Blo 1798100 5919655 := bstep (se 1 (by rfl) ⟨4439741, by rfl⟩ : syracuseStep 5919655 = 8879483) B8879483
theorem B1799103 : Blo 1798100 1799103 := bstep (se 1 (by rfl) ⟨1349327, by rfl⟩ : syracuseStep 1799103 = 2698655) B2698655
theorem B23065559 : Blo 1798100 23065559 := bstep (se 1 (by rfl) ⟨17299169, by rfl⟩ : syracuseStep 23065559 = 34598339) B34598339
theorem B4551785 : Blo 1798100 4551785 := bstep (se 2 (by rfl) ⟨1706919, by rfl⟩ : syracuseStep 4551785 = 3413839) B3413839
theorem B1799279 : Blo 1798100 1799279 := bstep (se 1 (by rfl) ⟨1349459, by rfl⟩ : syracuseStep 1799279 = 2698919) B2698919
theorem B1799295 : Blo 1798100 1799295 := bstep (se 1 (by rfl) ⟨1349471, by rfl⟩ : syracuseStep 1799295 = 2698943) B2698943
theorem B6829211 : Blo 1798100 6829211 := bstep (se 1 (by rfl) ⟨5121908, by rfl⟩ : syracuseStep 6829211 = 10243817) B10243817
theorem B1799359 : Blo 1798100 1799359 := bstep (se 1 (by rfl) ⟨1349519, by rfl⟩ : syracuseStep 1799359 = 2699039) B2699039
theorem B6829379 : Blo 1798100 6829379 := bstep (se 1 (by rfl) ⟨5122034, by rfl⟩ : syracuseStep 6829379 = 10244069) B10244069
theorem B1799551 : Blo 1798100 1799551 := bstep (se 1 (by rfl) ⟨1349663, by rfl⟩ : syracuseStep 1799551 = 2699327) B2699327
theorem B6485417 : Blo 1798100 6485417 := bstep (se 2 (by rfl) ⟨2432031, by rfl⟩ : syracuseStep 6485417 = 4864063) B4864063
theorem B1799679 : Blo 1798100 1799679 := bstep (se 1 (by rfl) ⟨1349759, by rfl⟩ : syracuseStep 1799679 = 2699519) B2699519
theorem B1799707 : Blo 1798100 1799707 := bstep (se 1 (by rfl) ⟨1349780, by rfl⟩ : syracuseStep 1799707 = 2699561) B2699561
theorem B14587451 : Blo 1798100 14587451 := bstep (se 1 (by rfl) ⟨10940588, by rfl⟩ : syracuseStep 14587451 = 21881177) B21881177
theorem B1799887 : Blo 1798100 1799887 := bstep (se 1 (by rfl) ⟨1349915, by rfl⟩ : syracuseStep 1799887 = 2699831) B2699831
theorem B12965615 : Blo 1798100 12965615 := bstep (se 1 (by rfl) ⟨9724211, by rfl⟩ : syracuseStep 12965615 = 19448423) B19448423
theorem B1800047 : Blo 1798100 1800047 := bstep (se 1 (by rfl) ⟨1350035, by rfl⟩ : syracuseStep 1800047 = 2700071) B2700071
theorem B6830183 : Blo 1798100 6830183 := bstep (se 1 (by rfl) ⟨5122637, by rfl⟩ : syracuseStep 6830183 = 10245275) B10245275
theorem B13506725 : Blo 1798100 13506725 := bstep (se 4 (by rfl) ⟨1266255, by rfl⟩ : syracuseStep 13506725 = 2532511) B2532511
theorem B3037351 : Blo 1798100 3037351 := bstep (se 1 (by rfl) ⟨2278013, by rfl⟩ : syracuseStep 3037351 = 4556027) B4556027
theorem B12966331 : Blo 1798100 12966331 := bstep (se 1 (by rfl) ⟨9724748, by rfl⟩ : syracuseStep 12966331 = 19449497) B19449497
theorem B9108125 : Blo 1798100 9108125 := bstep (se 3 (by rfl) ⟨1707773, by rfl⟩ : syracuseStep 9108125 = 3415547) B3415547
theorem B17529625 : Blo 1798100 17529625 := bstep (se 2 (by rfl) ⟨6573609, by rfl⟩ : syracuseStep 17529625 = 13147219) B13147219
theorem B6069113 : Blo 1798100 6069113 := bstep (se 2 (by rfl) ⟨2275917, by rfl⟩ : syracuseStep 6069113 = 4551835) B4551835
theorem B12303265 : Blo 1798100 12303265 := bstep (se 2 (by rfl) ⟨4613724, by rfl⟩ : syracuseStep 12303265 = 9227449) B9227449
theorem B4553759 : Blo 1798100 4553759 := bstep (se 1 (by rfl) ⟨3415319, by rfl⟩ : syracuseStep 4553759 = 6830639) B6830639
theorem B36920387 : Blo 1798100 36920387 := bstep (se 1 (by rfl) ⟨27690290, by rfl⟩ : syracuseStep 36920387 = 55380581) B55380581
theorem B4045931 : Blo 1798100 4045931 := bstep (se 1 (by rfl) ⟨3034448, by rfl⟩ : syracuseStep 4045931 = 6068897) B6068897
theorem B6831611 : Blo 1798100 6831611 := bstep (se 1 (by rfl) ⟨5123708, by rfl⟩ : syracuseStep 6831611 = 10247417) B10247417
theorem B3415783 : Blo 1798100 3415783 := bstep (se 1 (by rfl) ⟨2561837, by rfl⟩ : syracuseStep 3415783 = 5123675) B5123675
theorem B23052073 : Blo 1798100 23052073 := bstep (se 2 (by rfl) ⟨8644527, by rfl⟩ : syracuseStep 23052073 = 17289055) B17289055
theorem B5193775 : Blo 1798100 5193775 := bstep (se 1 (by rfl) ⟨3895331, by rfl⟩ : syracuseStep 5193775 = 7790663) B7790663
theorem B16408763 : Blo 1798100 16408763 := bstep (se 1 (by rfl) ⟨12306572, by rfl⟩ : syracuseStep 16408763 = 24613145) B24613145
theorem B2023663 : Blo 1798100 2023663 := bstep (se 1 (by rfl) ⟨1517747, by rfl⟩ : syracuseStep 2023663 = 3035495) B3035495
theorem B9724319 : Blo 1798100 9724319 := bstep (se 1 (by rfl) ⟨7293239, by rfl⟩ : syracuseStep 9724319 = 14586479) B14586479
theorem B15377039 : Blo 1798100 15377039 := bstep (se 1 (by rfl) ⟨11532779, by rfl⟩ : syracuseStep 15377039 = 23065559) B23065559
theorem B4047839 : Blo 1798100 4047839 := bstep (se 1 (by rfl) ⟨3035879, by rfl⟩ : syracuseStep 4047839 = 6071759) B6071759
theorem B13657085 : Blo 1798100 13657085 := bstep (se 3 (by rfl) ⟨2560703, by rfl⟩ : syracuseStep 13657085 = 5121407) B5121407
theorem B9724967 : Blo 1798100 9724967 := bstep (se 1 (by rfl) ⟨7293725, by rfl⟩ : syracuseStep 9724967 = 14587451) B14587451
theorem B6833281 : Blo 1798100 6833281 := bstep (se 2 (by rfl) ⟨2562480, by rfl⟩ : syracuseStep 6833281 = 5124961) B5124961
theorem B8643743 : Blo 1798100 8643743 := bstep (se 1 (by rfl) ⟨6482807, by rfl⟩ : syracuseStep 8643743 = 12965615) B12965615
theorem B9004483 : Blo 1798100 9004483 := bstep (se 1 (by rfl) ⟨6753362, by rfl⟩ : syracuseStep 9004483 = 13506725) B13506725
theorem B4556351 : Blo 1798100 4556351 := bstep (se 1 (by rfl) ⟨3417263, by rfl⟩ : syracuseStep 4556351 = 6834527) B6834527
theorem B6072083 : Blo 1798100 6072083 := bstep (se 1 (by rfl) ⟨4554062, by rfl⟩ : syracuseStep 6072083 = 9108125) B9108125
theorem B65668913 : Blo 1798100 65668913 := bstep (se 2 (by rfl) ⟨24625842, by rfl⟩ : syracuseStep 65668913 = 49251685) B49251685
theorem B10241903 : Blo 1798100 10241903 := bstep (se 1 (by rfl) ⟨7681427, by rfl⟩ : syracuseStep 10241903 = 15362855) B15362855
theorem B9111527 : Blo 1798100 9111527 := bstep (se 1 (by rfl) ⟨6833645, by rfl⟩ : syracuseStep 9111527 = 13667291) B13667291
theorem B2697287 : Blo 1798100 2697287 := bstep (se 1 (by rfl) ⟨2022965, by rfl⟩ : syracuseStep 2697287 = 4045931) B4045931
theorem B9111851 : Blo 1798100 9111851 := bstep (se 1 (by rfl) ⟨6833888, by rfl⟩ : syracuseStep 9111851 = 13667777) B13667777
theorem B20761427 : Blo 1798100 20761427 := bstep (se 1 (by rfl) ⟨15571070, by rfl⟩ : syracuseStep 20761427 = 31142141) B31142141
theorem B4049801 : Blo 1798100 4049801 := bstep (se 2 (by rfl) ⟨1518675, by rfl⟩ : syracuseStep 4049801 = 3037351) B3037351
theorem B66522161 : Blo 1798100 66522161 := bstep (se 2 (by rfl) ⟨24945810, by rfl⟩ : syracuseStep 66522161 = 49891621) B49891621
theorem B17288441 : Blo 1798100 17288441 := bstep (se 2 (by rfl) ⟨6483165, by rfl⟩ : syracuseStep 17288441 = 12966331) B12966331
theorem B3034523 : Blo 1798100 3034523 := bstep (se 1 (by rfl) ⟨2275892, by rfl⟩ : syracuseStep 3034523 = 4551785) B4551785
theorem B5123503 : Blo 1798100 5123503 := bstep (se 1 (by rfl) ⟨3842627, by rfl⟩ : syracuseStep 5123503 = 7685255) B7685255
theorem B373968389 : Blo 1798100 373968389 := bstep (se 4 (by rfl) ⟨35059536, by rfl⟩ : syracuseStep 373968389 = 70119073) B70119073
theorem B98496161 : Blo 1798100 98496161 := bstep (se 2 (by rfl) ⟨36936060, by rfl⟩ : syracuseStep 98496161 = 73872121) B73872121
theorem B9727735 : Blo 1798100 9727735 := bstep (se 1 (by rfl) ⟨7295801, by rfl⟩ : syracuseStep 9727735 = 14591603) B14591603
theorem B4321151 : Blo 1798100 4321151 := bstep (se 1 (by rfl) ⟨3240863, by rfl⟩ : syracuseStep 4321151 = 6481727) B6481727
theorem B16404353 : Blo 1798100 16404353 := bstep (se 2 (by rfl) ⟨6151632, by rfl⟩ : syracuseStep 16404353 = 12303265) B12303265
theorem B7892873 : Blo 1798100 7892873 := bstep (se 2 (by rfl) ⟨2959827, by rfl⟩ : syracuseStep 7892873 = 5919655) B5919655
theorem B2699291 : Blo 1798100 2699291 := bstep (se 1 (by rfl) ⟨2024468, by rfl⟩ : syracuseStep 2699291 = 4048937) B4048937
theorem B1798215 : Blo 1798100 1798215 := bstep (se 1 (by rfl) ⟨1348661, by rfl⟩ : syracuseStep 1798215 = 2697323) B2697323
theorem B93491333 : Blo 1798100 93491333 := bstep (se 4 (by rfl) ⟨8764812, by rfl⟩ : syracuseStep 93491333 = 17529625) B17529625
theorem B1798335 : Blo 1798100 1798335 := bstep (se 1 (by rfl) ⟨1348751, by rfl⟩ : syracuseStep 1798335 = 2697503) B2697503
theorem B2699471 : Blo 1798100 2699471 := bstep (se 1 (by rfl) ⟨2024603, by rfl⟩ : syracuseStep 2699471 = 4049207) B4049207
theorem B4321495 : Blo 1798100 4321495 := bstep (se 1 (by rfl) ⟨3241121, by rfl⟩ : syracuseStep 4321495 = 6482243) B6482243
theorem B4862201 : Blo 1798100 4862201 := bstep (se 2 (by rfl) ⟨1823325, by rfl⟩ : syracuseStep 4862201 = 3646651) B3646651
theorem B9728255 : Blo 1798100 9728255 := bstep (se 1 (by rfl) ⟨7296191, by rfl⟩ : syracuseStep 9728255 = 14592383) B14592383
theorem B1798631 : Blo 1798100 1798631 := bstep (se 1 (by rfl) ⟨1348973, by rfl⟩ : syracuseStep 1798631 = 2697947) B2697947
theorem B23065195 : Blo 1798100 23065195 := bstep (se 1 (by rfl) ⟨17298896, by rfl⟩ : syracuseStep 23065195 = 34597793) B34597793
theorem B1798815 : Blo 1798100 1798815 := bstep (se 1 (by rfl) ⟨1349111, by rfl⟩ : syracuseStep 1798815 = 2698223) B2698223
theorem B1798823 : Blo 1798100 1798823 := bstep (se 1 (by rfl) ⟨1349117, by rfl⟩ : syracuseStep 1798823 = 2698235) B2698235
theorem B3035839 : Blo 1798100 3035839 := bstep (se 1 (by rfl) ⟨2276879, by rfl⟩ : syracuseStep 3035839 = 4553759) B4553759
theorem B1798863 : Blo 1798100 1798863 := bstep (se 1 (by rfl) ⟨1349147, by rfl⟩ : syracuseStep 1798863 = 2698295) B2698295
theorem B24613591 : Blo 1798100 24613591 := bstep (se 1 (by rfl) ⟨18460193, by rfl⟩ : syracuseStep 24613591 = 36920387) B36920387
theorem B1798943 : Blo 1798100 1798943 := bstep (se 1 (by rfl) ⟨1349207, by rfl⟩ : syracuseStep 1798943 = 2698415) B2698415
theorem B1798983 : Blo 1798100 1798983 := bstep (se 1 (by rfl) ⟨1349237, by rfl⟩ : syracuseStep 1798983 = 2698475) B2698475
theorem B67482625 : Blo 1798100 67482625 := bstep (se 2 (by rfl) ⟨25305984, by rfl⟩ : syracuseStep 67482625 = 50611969) B50611969
theorem B1799195 : Blo 1798100 1799195 := bstep (se 1 (by rfl) ⟨1349396, by rfl⟩ : syracuseStep 1799195 = 2698793) B2698793
theorem B1799423 : Blo 1798100 1799423 := bstep (se 1 (by rfl) ⟨1349567, by rfl⟩ : syracuseStep 1799423 = 2699135) B2699135
theorem B58373399 : Blo 1798100 58373399 := bstep (se 1 (by rfl) ⟨43780049, by rfl⟩ : syracuseStep 58373399 = 87560099) B87560099
theorem B4552159 : Blo 1798100 4552159 := bstep (se 1 (by rfl) ⟨3414119, by rfl⟩ : syracuseStep 4552159 = 6828239) B6828239
theorem B4617719 : Blo 1798100 4617719 := bstep (se 1 (by rfl) ⟨3463289, by rfl⟩ : syracuseStep 4617719 = 6926579) B6926579
theorem B7296743 : Blo 1798100 7296743 := bstep (se 1 (by rfl) ⟨5472557, by rfl⟩ : syracuseStep 7296743 = 10945115) B10945115
theorem B4552807 : Blo 1798100 4552807 := bstep (se 1 (by rfl) ⟨3414605, by rfl⟩ : syracuseStep 4552807 = 6829211) B6829211
theorem B4552919 : Blo 1798100 4552919 := bstep (se 1 (by rfl) ⟨3414689, by rfl⟩ : syracuseStep 4552919 = 6829379) B6829379
theorem B17283293 : Blo 1798100 17283293 := bstep (se 3 (by rfl) ⟨3240617, by rfl⟩ : syracuseStep 17283293 = 6481235) B6481235
theorem B4323611 : Blo 1798100 4323611 := bstep (se 1 (by rfl) ⟨3242708, by rfl⟩ : syracuseStep 4323611 = 6485417) B6485417
theorem B3414575 : Blo 1798100 3414575 := bstep (se 1 (by rfl) ⟨2560931, by rfl⟩ : syracuseStep 3414575 = 5121863) B5121863
theorem B4553455 : Blo 1798100 4553455 := bstep (se 1 (by rfl) ⟨3415091, by rfl⟩ : syracuseStep 4553455 = 6830183) B6830183
theorem B6069491 : Blo 1798100 6069491 := bstep (se 1 (by rfl) ⟨4552118, by rfl⟩ : syracuseStep 6069491 = 9104237) B9104237
theorem B4046075 : Blo 1798100 4046075 := bstep (se 1 (by rfl) ⟨3034556, by rfl⟩ : syracuseStep 4046075 = 6069113) B6069113
theorem B4554377 : Blo 1798100 4554377 := bstep (se 2 (by rfl) ⟨1707891, by rfl⟩ : syracuseStep 4554377 = 3415783) B3415783
theorem B4554407 : Blo 1798100 4554407 := bstep (se 1 (by rfl) ⟨3415805, by rfl⟩ : syracuseStep 4554407 = 6831611) B6831611
theorem B30736097 : Blo 1798100 30736097 := bstep (se 2 (by rfl) ⟨11526036, by rfl⟩ : syracuseStep 30736097 = 23052073) B23052073
theorem B6070409 : Blo 1798100 6070409 := bstep (se 2 (by rfl) ⟨2276403, by rfl⟩ : syracuseStep 6070409 = 4552807) B4552807
theorem B30753593 : Blo 1798100 30753593 := bstep (se 2 (by rfl) ⟨11532597, by rfl⟩ : syracuseStep 30753593 = 23065195) B23065195
theorem B4047785 : Blo 1798100 4047785 := bstep (se 2 (by rfl) ⟨1517919, by rfl⟩ : syracuseStep 4047785 = 3035839) B3035839
theorem B32818121 : Blo 1798100 32818121 := bstep (se 2 (by rfl) ⟨12306795, by rfl⟩ : syracuseStep 32818121 = 24613591) B24613591
theorem B6071273 : Blo 1798100 6071273 := bstep (se 2 (by rfl) ⟨2276727, by rfl⟩ : syracuseStep 6071273 = 4553455) B4553455
theorem B4048055 : Blo 1798100 4048055 := bstep (se 1 (by rfl) ⟨3036041, by rfl⟩ : syracuseStep 4048055 = 6072083) B6072083
theorem B43779275 : Blo 1798100 43779275 := bstep (se 1 (by rfl) ⟨32834456, by rfl⟩ : syracuseStep 43779275 = 65668913) B65668913
theorem B9111041 : Blo 1798100 9111041 := bstep (se 2 (by rfl) ⟨3416640, by rfl⟩ : syracuseStep 9111041 = 6833281) B6833281
theorem B19457981 : Blo 1798100 19457981 := bstep (se 3 (by rfl) ⟨3648371, by rfl⟩ : syracuseStep 19457981 = 7296743) B7296743
theorem B2697383 : Blo 1798100 2697383 := bstep (se 1 (by rfl) ⟨2023037, by rfl⟩ : syracuseStep 2697383 = 4046075) B4046075
theorem B12970313 : Blo 1798100 12970313 := bstep (se 2 (by rfl) ⟨4863867, by rfl⟩ : syracuseStep 12970313 = 9727735) B9727735
theorem B20490731 : Blo 1798100 20490731 := bstep (se 1 (by rfl) ⟨15368048, by rfl⟩ : syracuseStep 20490731 = 30736097) B30736097
theorem B5261915 : Blo 1798100 5261915 := bstep (se 1 (by rfl) ⟨3946436, by rfl⟩ : syracuseStep 5261915 = 7892873) B7892873
theorem B6925033 : Blo 1798100 6925033 := bstep (se 2 (by rfl) ⟨2596887, by rfl⟩ : syracuseStep 6925033 = 5193775) B5193775
theorem B62327555 : Blo 1798100 62327555 := bstep (se 1 (by rfl) ⟨46745666, by rfl⟩ : syracuseStep 62327555 = 93491333) B93491333
theorem B10939175 : Blo 1798100 10939175 := bstep (se 1 (by rfl) ⟨8204381, by rfl⟩ : syracuseStep 10939175 = 16408763) B16408763
theorem B6482879 : Blo 1798100 6482879 := bstep (se 1 (by rfl) ⟨4862159, by rfl⟩ : syracuseStep 6482879 = 9724319) B9724319
theorem B2698217 : Blo 1798100 2698217 := bstep (se 2 (by rfl) ⟨1011831, by rfl⟩ : syracuseStep 2698217 = 2023663) B2023663
theorem B10251359 : Blo 1798100 10251359 := bstep (se 1 (by rfl) ⟨7688519, by rfl⟩ : syracuseStep 10251359 = 15377039) B15377039
theorem B2698559 : Blo 1798100 2698559 := bstep (se 1 (by rfl) ⟨2023919, by rfl⟩ : syracuseStep 2698559 = 4047839) B4047839
theorem B9104723 : Blo 1798100 9104723 := bstep (se 1 (by rfl) ⟨6828542, by rfl⟩ : syracuseStep 9104723 = 13657085) B13657085
theorem B6483311 : Blo 1798100 6483311 := bstep (se 1 (by rfl) ⟨4862483, by rfl⟩ : syracuseStep 6483311 = 9724967) B9724967
theorem B5762495 : Blo 1798100 5762495 := bstep (se 1 (by rfl) ⟨4321871, by rfl⟩ : syracuseStep 5762495 = 8643743) B8643743
theorem B38915599 : Blo 1798100 38915599 := bstep (se 1 (by rfl) ⟨29186699, by rfl⟩ : syracuseStep 38915599 = 58373399) B58373399
theorem B23047973 : Blo 1798100 23047973 := bstep (se 4 (by rfl) ⟨2160747, by rfl⟩ : syracuseStep 23047973 = 4321495) B4321495
theorem B6827935 : Blo 1798100 6827935 := bstep (se 1 (by rfl) ⟨5120951, by rfl⟩ : syracuseStep 6827935 = 10241903) B10241903
theorem B6074351 : Blo 1798100 6074351 := bstep (se 1 (by rfl) ⟨4555763, by rfl⟩ : syracuseStep 6074351 = 9111527) B9111527
theorem B89976833 : Blo 1798100 89976833 := bstep (se 2 (by rfl) ⟨33741312, by rfl⟩ : syracuseStep 89976833 = 67482625) B67482625
theorem B1798191 : Blo 1798100 1798191 := bstep (se 1 (by rfl) ⟨1348643, by rfl⟩ : syracuseStep 1798191 = 2697287) B2697287
theorem B9105533 : Blo 1798100 9105533 := bstep (se 3 (by rfl) ⟨1707287, by rfl⟩ : syracuseStep 9105533 = 3414575) B3414575
theorem B3035279 : Blo 1798100 3035279 := bstep (se 1 (by rfl) ⟨2276459, by rfl⟩ : syracuseStep 3035279 = 4552919) B4552919
theorem B11522195 : Blo 1798100 11522195 := bstep (se 1 (by rfl) ⟨8641646, by rfl⟩ : syracuseStep 11522195 = 17283293) B17283293
theorem B6074567 : Blo 1798100 6074567 := bstep (se 1 (by rfl) ⟨4555925, by rfl⟩ : syracuseStep 6074567 = 9111851) B9111851
theorem B13840951 : Blo 1798100 13840951 := bstep (se 1 (by rfl) ⟨10380713, by rfl⟩ : syracuseStep 13840951 = 20761427) B20761427
theorem B12005977 : Blo 1798100 12005977 := bstep (se 2 (by rfl) ⟨4502241, by rfl⟩ : syracuseStep 12005977 = 9004483) B9004483
theorem B2699867 : Blo 1798100 2699867 := bstep (se 1 (by rfl) ⟨2024900, by rfl⟩ : syracuseStep 2699867 = 4049801) B4049801
theorem B44348107 : Blo 1798100 44348107 := bstep (se 1 (by rfl) ⟨33261080, by rfl⟩ : syracuseStep 44348107 = 66522161) B66522161
theorem B249312259 : Blo 1798100 249312259 := bstep (se 1 (by rfl) ⟨186984194, by rfl⟩ : syracuseStep 249312259 = 373968389) B373968389
theorem B3036251 : Blo 1798100 3036251 := bstep (se 1 (by rfl) ⟨2277188, by rfl⟩ : syracuseStep 3036251 = 4554377) B4554377
theorem B65664107 : Blo 1798100 65664107 := bstep (se 1 (by rfl) ⟨49248080, by rfl⟩ : syracuseStep 65664107 = 98496161) B98496161
theorem B3036271 : Blo 1798100 3036271 := bstep (se 1 (by rfl) ⟨2277203, by rfl⟩ : syracuseStep 3036271 = 4554407) B4554407
theorem B2880767 : Blo 1798100 2880767 := bstep (se 1 (by rfl) ⟨2160575, by rfl⟩ : syracuseStep 2880767 = 4321151) B4321151
theorem B1799527 : Blo 1798100 1799527 := bstep (se 1 (by rfl) ⟨1349645, by rfl⟩ : syracuseStep 1799527 = 2699291) B2699291
theorem B1799647 : Blo 1798100 1799647 := bstep (se 1 (by rfl) ⟨1349735, by rfl⟩ : syracuseStep 1799647 = 2699471) B2699471
theorem B6485503 : Blo 1798100 6485503 := bstep (se 1 (by rfl) ⟨4864127, by rfl⟩ : syracuseStep 6485503 = 9728255) B9728255
theorem B12965869 : Blo 1798100 12965869 := bstep (se 3 (by rfl) ⟨2431100, by rfl⟩ : syracuseStep 12965869 = 4862201) B4862201
theorem B3078479 : Blo 1798100 3078479 := bstep (se 1 (by rfl) ⟨2308859, by rfl⟩ : syracuseStep 3078479 = 4617719) B4617719
theorem B3037567 : Blo 1798100 3037567 := bstep (se 1 (by rfl) ⟨2278175, by rfl⟩ : syracuseStep 3037567 = 4556351) B4556351
theorem B2882407 : Blo 1798100 2882407 := bstep (se 1 (by rfl) ⟨2161805, by rfl⟩ : syracuseStep 2882407 = 4323611) B4323611
theorem B6831337 : Blo 1798100 6831337 := bstep (se 2 (by rfl) ⟨2561751, by rfl⟩ : syracuseStep 6831337 = 5123503) B5123503
theorem B6069545 : Blo 1798100 6069545 := bstep (se 2 (by rfl) ⟨2276079, by rfl⟩ : syracuseStep 6069545 = 4552159) B4552159
theorem B4046327 : Blo 1798100 4046327 := bstep (se 1 (by rfl) ⟨3034745, by rfl⟩ : syracuseStep 4046327 = 6069491) B6069491
theorem B11525627 : Blo 1798100 11525627 := bstep (se 1 (by rfl) ⟨8644220, by rfl⟩ : syracuseStep 11525627 = 17288441) B17288441
theorem B2023015 : Blo 1798100 2023015 := bstep (se 1 (by rfl) ⟨1517261, by rfl⟩ : syracuseStep 2023015 = 3034523) B3034523
theorem B10936235 : Blo 1798100 10936235 := bstep (se 1 (by rfl) ⟨8202176, by rfl⟩ : syracuseStep 10936235 = 16404353) B16404353
theorem B6070355 : Blo 1798100 6070355 := bstep (se 1 (by rfl) ⟨4552766, by rfl⟩ : syracuseStep 6070355 = 9105533) B9105533
theorem B4046939 : Blo 1798100 4046939 := bstep (se 1 (by rfl) ⟨3035204, by rfl⟩ : syracuseStep 4046939 = 6070409) B6070409
theorem B2023519 : Blo 1798100 2023519 := bstep (se 1 (by rfl) ⟨1517639, by rfl⟩ : syracuseStep 2023519 = 3035279) B3035279
theorem B4047515 : Blo 1798100 4047515 := bstep (se 1 (by rfl) ⟨3035636, by rfl⟩ : syracuseStep 4047515 = 6071273) B6071273
theorem B2024167 : Blo 1798100 2024167 := bstep (se 1 (by rfl) ⟨1518125, by rfl⟩ : syracuseStep 2024167 = 3036251) B3036251
theorem B16007969 : Blo 1798100 16007969 := bstep (se 2 (by rfl) ⟨6002988, by rfl⟩ : syracuseStep 16007969 = 12005977) B12005977
theorem B59130809 : Blo 1798100 59130809 := bstep (se 2 (by rfl) ⟨22174053, by rfl⟩ : syracuseStep 59130809 = 44348107) B44348107
theorem B3843209 : Blo 1798100 3843209 := bstep (se 2 (by rfl) ⟨1441203, by rfl⟩ : syracuseStep 3843209 = 2882407) B2882407
theorem B4048361 : Blo 1798100 4048361 := bstep (se 2 (by rfl) ⟨1518135, by rfl⟩ : syracuseStep 4048361 = 3036271) B3036271
theorem B3507943 : Blo 1798100 3507943 := bstep (se 1 (by rfl) ⟨2630957, by rfl⟩ : syracuseStep 3507943 = 5261915) B5261915
theorem B41551703 : Blo 1798100 41551703 := bstep (se 1 (by rfl) ⟨31163777, by rfl⟩ : syracuseStep 41551703 = 62327555) B62327555
theorem B7292783 : Blo 1798100 7292783 := bstep (se 1 (by rfl) ⟨5469587, by rfl⟩ : syracuseStep 7292783 = 10939175) B10939175
theorem B6834239 : Blo 1798100 6834239 := bstep (se 1 (by rfl) ⟨5125679, by rfl⟩ : syracuseStep 6834239 = 10251359) B10251359
theorem B2697353 : Blo 1798100 2697353 := bstep (se 2 (by rfl) ⟨1011507, by rfl⟩ : syracuseStep 2697353 = 2023015) B2023015
theorem B2697551 : Blo 1798100 2697551 := bstep (se 1 (by rfl) ⟨2023163, by rfl⟩ : syracuseStep 2697551 = 4046327) B4046327
theorem B9103913 : Blo 1798100 9103913 := bstep (se 2 (by rfl) ⟨3413967, by rfl⟩ : syracuseStep 9103913 = 6827935) B6827935
theorem B17287825 : Blo 1798100 17287825 := bstep (se 2 (by rfl) ⟨6482934, by rfl⟩ : syracuseStep 17287825 = 12965869) B12965869
theorem B4049567 : Blo 1798100 4049567 := bstep (se 1 (by rfl) ⟨3037175, by rfl⟩ : syracuseStep 4049567 = 6074351) B6074351
theorem B59984555 : Blo 1798100 59984555 := bstep (se 1 (by rfl) ⟨44988416, by rfl⟩ : syracuseStep 59984555 = 89976833) B89976833
theorem B4049711 : Blo 1798100 4049711 := bstep (se 1 (by rfl) ⟨3037283, by rfl⟩ : syracuseStep 4049711 = 6074567) B6074567
theorem B4050089 : Blo 1798100 4050089 := bstep (se 2 (by rfl) ⟨1518783, by rfl⟩ : syracuseStep 4050089 = 3037567) B3037567
theorem B2698523 : Blo 1798100 2698523 := bstep (se 1 (by rfl) ⟨2023892, by rfl⟩ : syracuseStep 2698523 = 4047785) B4047785
theorem B2698703 : Blo 1798100 2698703 := bstep (se 1 (by rfl) ⟨2024027, by rfl⟩ : syracuseStep 2698703 = 4048055) B4048055
theorem B1920511 : Blo 1798100 1920511 := bstep (se 1 (by rfl) ⟨1440383, by rfl⟩ : syracuseStep 1920511 = 2880767) B2880767
theorem B6074027 : Blo 1798100 6074027 := bstep (se 1 (by rfl) ⟨4555520, by rfl⟩ : syracuseStep 6074027 = 9111041) B9111041
theorem B36933509 : Blo 1798100 36933509 := bstep (se 4 (by rfl) ⟨3462516, by rfl⟩ : syracuseStep 36933509 = 6925033) B6925033
theorem B12971987 : Blo 1798100 12971987 := bstep (se 1 (by rfl) ⟨9728990, by rfl⟩ : syracuseStep 12971987 = 19457981) B19457981
theorem B1798255 : Blo 1798100 1798255 := bstep (se 1 (by rfl) ⟨1348691, by rfl⟩ : syracuseStep 1798255 = 2697383) B2697383
theorem B8646875 : Blo 1798100 8646875 := bstep (se 1 (by rfl) ⟨6485156, by rfl⟩ : syracuseStep 8646875 = 12970313) B12970313
theorem B2052319 : Blo 1798100 2052319 := bstep (se 1 (by rfl) ⟨1539239, by rfl⟩ : syracuseStep 2052319 = 3078479) B3078479
theorem B13660487 : Blo 1798100 13660487 := bstep (se 1 (by rfl) ⟨10245365, by rfl⟩ : syracuseStep 13660487 = 20490731) B20490731
theorem B4321919 : Blo 1798100 4321919 := bstep (se 1 (by rfl) ⟨3241439, by rfl⟩ : syracuseStep 4321919 = 6482879) B6482879
theorem B1798811 : Blo 1798100 1798811 := bstep (se 1 (by rfl) ⟨1349108, by rfl⟩ : syracuseStep 1798811 = 2698217) B2698217
theorem B8647337 : Blo 1798100 8647337 := bstep (se 2 (by rfl) ⟨3242751, by rfl⟩ : syracuseStep 8647337 = 6485503) B6485503
theorem B1799039 : Blo 1798100 1799039 := bstep (se 1 (by rfl) ⟨1349279, by rfl⟩ : syracuseStep 1799039 = 2698559) B2698559
theorem B4322207 : Blo 1798100 4322207 := bstep (se 1 (by rfl) ⟨3241655, by rfl⟩ : syracuseStep 4322207 = 6483311) B6483311
theorem B15365315 : Blo 1798100 15365315 := bstep (se 1 (by rfl) ⟨11523986, by rfl⟩ : syracuseStep 15365315 = 23047973) B23047973
theorem B1329665381 : Blo 1798100 1329665381 := bstep (se 4 (by rfl) ⟨124656129, by rfl⟩ : syracuseStep 1329665381 = 249312259) B249312259
theorem B7681463 : Blo 1798100 7681463 := bstep (se 1 (by rfl) ⟨5761097, by rfl⟩ : syracuseStep 7681463 = 11522195) B11522195
theorem B1799911 : Blo 1798100 1799911 := bstep (se 1 (by rfl) ⟨1349933, by rfl⟩ : syracuseStep 1799911 = 2699867) B2699867
theorem B20502395 : Blo 1798100 20502395 := bstep (se 1 (by rfl) ⟨15376796, by rfl⟩ : syracuseStep 20502395 = 30753593) B30753593
theorem B21878747 : Blo 1798100 21878747 := bstep (se 1 (by rfl) ⟨16409060, by rfl⟩ : syracuseStep 21878747 = 32818121) B32818121
theorem B43776071 : Blo 1798100 43776071 := bstep (se 1 (by rfl) ⟨32832053, by rfl⟩ : syracuseStep 43776071 = 65664107) B65664107
theorem B18454601 : Blo 1798100 18454601 := bstep (se 2 (by rfl) ⟨6920475, by rfl⟩ : syracuseStep 18454601 = 13840951) B13840951
theorem B29186183 : Blo 1798100 29186183 := bstep (se 1 (by rfl) ⟨21889637, by rfl⟩ : syracuseStep 29186183 = 43779275) B43779275
theorem B9108449 : Blo 1798100 9108449 := bstep (se 2 (by rfl) ⟨3415668, by rfl⟩ : syracuseStep 9108449 = 6831337) B6831337
theorem B51887465 : Blo 1798100 51887465 := bstep (se 2 (by rfl) ⟨19457799, by rfl⟩ : syracuseStep 51887465 = 38915599) B38915599
theorem B4046363 : Blo 1798100 4046363 := bstep (se 1 (by rfl) ⟨3034772, by rfl⟩ : syracuseStep 4046363 = 6069545) B6069545
theorem B6069815 : Blo 1798100 6069815 := bstep (se 1 (by rfl) ⟨4552361, by rfl⟩ : syracuseStep 6069815 = 9104723) B9104723
theorem B3841663 : Blo 1798100 3841663 := bstep (se 1 (by rfl) ⟨2881247, by rfl⟩ : syracuseStep 3841663 = 5762495) B5762495
theorem B7683751 : Blo 1798100 7683751 := bstep (se 1 (by rfl) ⟨5762813, by rfl⟩ : syracuseStep 7683751 = 11525627) B11525627
theorem B7290823 : Blo 1798100 7290823 := bstep (se 1 (by rfl) ⟨5468117, by rfl⟩ : syracuseStep 7290823 = 10936235) B10936235
theorem B4046903 : Blo 1798100 4046903 := bstep (se 1 (by rfl) ⟨3035177, by rfl⟩ : syracuseStep 4046903 = 6070355) B6070355
theorem B2736425 : Blo 1798100 2736425 := bstep (se 2 (by rfl) ⟨1026159, by rfl⟩ : syracuseStep 2736425 = 2052319) B2052319
theorem B39420539 : Blo 1798100 39420539 := bstep (se 1 (by rfl) ⟨29565404, by rfl⟩ : syracuseStep 39420539 = 59130809) B59130809
theorem B5120975 : Blo 1798100 5120975 := bstep (se 1 (by rfl) ⟨3840731, by rfl⟩ : syracuseStep 5120975 = 7681463) B7681463
theorem B4556159 : Blo 1798100 4556159 := bstep (se 1 (by rfl) ⟨3417119, by rfl⟩ : syracuseStep 4556159 = 6834239) B6834239
theorem B19457455 : Blo 1798100 19457455 := bstep (se 1 (by rfl) ⟨14593091, by rfl⟩ : syracuseStep 19457455 = 29186183) B29186183
theorem B159958813 : Blo 1798100 159958813 := bstep (se 3 (by rfl) ⟨29992277, by rfl⟩ : syracuseStep 159958813 = 59984555) B59984555
theorem B6072299 : Blo 1798100 6072299 := bstep (se 1 (by rfl) ⟨4554224, by rfl⟩ : syracuseStep 6072299 = 9108449) B9108449
theorem B5122217 : Blo 1798100 5122217 := bstep (se 2 (by rfl) ⟨1920831, by rfl⟩ : syracuseStep 5122217 = 3841663) B3841663
theorem B2697575 : Blo 1798100 2697575 := bstep (se 1 (by rfl) ⟨2023181, by rfl⟩ : syracuseStep 2697575 = 4046363) B4046363
theorem B4049351 : Blo 1798100 4049351 := bstep (se 1 (by rfl) ⟨3037013, by rfl⟩ : syracuseStep 4049351 = 6074027) B6074027
theorem B2697959 : Blo 1798100 2697959 := bstep (se 1 (by rfl) ⟨2023469, by rfl⟩ : syracuseStep 2697959 = 4046939) B4046939
theorem B2698025 : Blo 1798100 2698025 := bstep (se 2 (by rfl) ⟨1011759, by rfl⟩ : syracuseStep 2698025 = 2023519) B2023519
theorem B2698343 : Blo 1798100 2698343 := bstep (se 1 (by rfl) ⟨2023757, by rfl⟩ : syracuseStep 2698343 = 4047515) B4047515
theorem B10243543 : Blo 1798100 10243543 := bstep (se 1 (by rfl) ⟨7682657, by rfl⟩ : syracuseStep 10243543 = 15365315) B15365315
theorem B886443587 : Blo 1798100 886443587 := bstep (se 1 (by rfl) ⟨664832690, by rfl⟩ : syracuseStep 886443587 = 1329665381) B1329665381
theorem B2698889 : Blo 1798100 2698889 := bstep (se 2 (by rfl) ⟨1012083, by rfl⟩ : syracuseStep 2698889 = 2024167) B2024167
theorem B2698907 : Blo 1798100 2698907 := bstep (se 1 (by rfl) ⟨2024180, by rfl⟩ : syracuseStep 2698907 = 4048361) B4048361
theorem B27701135 : Blo 1798100 27701135 := bstep (se 1 (by rfl) ⟨20775851, by rfl⟩ : syracuseStep 27701135 = 41551703) B41551703
theorem B4861855 : Blo 1798100 4861855 := bstep (se 1 (by rfl) ⟨3646391, by rfl⟩ : syracuseStep 4861855 = 7292783) B7292783
theorem B13668263 : Blo 1798100 13668263 := bstep (se 1 (by rfl) ⟨10251197, by rfl⟩ : syracuseStep 13668263 = 20502395) B20502395
theorem B14585831 : Blo 1798100 14585831 := bstep (se 1 (by rfl) ⟨10939373, by rfl⟩ : syracuseStep 14585831 = 21878747) B21878747
theorem B29184047 : Blo 1798100 29184047 := bstep (se 1 (by rfl) ⟨21888035, by rfl⟩ : syracuseStep 29184047 = 43776071) B43776071
theorem B1798235 : Blo 1798100 1798235 := bstep (se 1 (by rfl) ⟨1348676, by rfl⟩ : syracuseStep 1798235 = 2697353) B2697353
theorem B1798367 : Blo 1798100 1798367 := bstep (se 1 (by rfl) ⟨1348775, by rfl⟩ : syracuseStep 1798367 = 2697551) B2697551
theorem B2699711 : Blo 1798100 2699711 := bstep (se 1 (by rfl) ⟨2024783, by rfl⟩ : syracuseStep 2699711 = 4049567) B4049567
theorem B2699807 : Blo 1798100 2699807 := bstep (se 1 (by rfl) ⟨2024855, by rfl⟩ : syracuseStep 2699807 = 4049711) B4049711
theorem B2560681 : Blo 1798100 2560681 := bstep (se 2 (by rfl) ⟨960255, by rfl⟩ : syracuseStep 2560681 = 1920511) B1920511
theorem B2700059 : Blo 1798100 2700059 := bstep (se 1 (by rfl) ⟨2025044, by rfl⟩ : syracuseStep 2700059 = 4050089) B4050089
theorem B1799015 : Blo 1798100 1799015 := bstep (se 1 (by rfl) ⟨1349261, by rfl⟩ : syracuseStep 1799015 = 2698523) B2698523
theorem B10245001 : Blo 1798100 10245001 := bstep (se 2 (by rfl) ⟨3841875, by rfl⟩ : syracuseStep 10245001 = 7683751) B7683751
theorem B34591643 : Blo 1798100 34591643 := bstep (se 1 (by rfl) ⟨25943732, by rfl⟩ : syracuseStep 34591643 = 51887465) B51887465
theorem B1799135 : Blo 1798100 1799135 := bstep (se 1 (by rfl) ⟨1349351, by rfl⟩ : syracuseStep 1799135 = 2698703) B2698703
theorem B98489357 : Blo 1798100 98489357 := bstep (se 3 (by rfl) ⟨18466754, by rfl⟩ : syracuseStep 98489357 = 36933509) B36933509
theorem B9721097 : Blo 1798100 9721097 := bstep (se 2 (by rfl) ⟨3645411, by rfl⟩ : syracuseStep 9721097 = 7290823) B7290823
theorem B8647991 : Blo 1798100 8647991 := bstep (se 1 (by rfl) ⟨6485993, by rfl⟩ : syracuseStep 8647991 = 12971987) B12971987
theorem B5764583 : Blo 1798100 5764583 := bstep (se 1 (by rfl) ⟨4323437, by rfl⟩ : syracuseStep 5764583 = 8646875) B8646875
theorem B9106991 : Blo 1798100 9106991 := bstep (se 1 (by rfl) ⟨6830243, by rfl⟩ : syracuseStep 9106991 = 13660487) B13660487
theorem B2881279 : Blo 1798100 2881279 := bstep (se 1 (by rfl) ⟨2160959, by rfl⟩ : syracuseStep 2881279 = 4321919) B4321919
theorem B5764891 : Blo 1798100 5764891 := bstep (se 1 (by rfl) ⟨4323668, by rfl⟩ : syracuseStep 5764891 = 8647337) B8647337
theorem B2562139 : Blo 1798100 2562139 := bstep (se 1 (by rfl) ⟨1921604, by rfl⟩ : syracuseStep 2562139 = 3843209) B3843209
theorem B23050433 : Blo 1798100 23050433 := bstep (se 2 (by rfl) ⟨8643912, by rfl⟩ : syracuseStep 23050433 = 17287825) B17287825
theorem B12303067 : Blo 1798100 12303067 := bstep (se 1 (by rfl) ⟨9227300, by rfl⟩ : syracuseStep 12303067 = 18454601) B18454601
theorem B6069275 : Blo 1798100 6069275 := bstep (se 1 (by rfl) ⟨4551956, by rfl⟩ : syracuseStep 6069275 = 9103913) B9103913
theorem B42687917 : Blo 1798100 42687917 := bstep (se 3 (by rfl) ⟨8003984, by rfl⟩ : syracuseStep 42687917 = 16007969) B16007969
theorem B4677257 : Blo 1798100 4677257 := bstep (se 2 (by rfl) ⟨1753971, by rfl⟩ : syracuseStep 4677257 = 3507943) B3507943
theorem B4046543 : Blo 1798100 4046543 := bstep (se 1 (by rfl) ⟨3034907, by rfl⟩ : syracuseStep 4046543 = 6069815) B6069815
theorem B11525885 : Blo 1798100 11525885 := bstep (se 3 (by rfl) ⟨2161103, by rfl⟩ : syracuseStep 11525885 = 4322207) B4322207
theorem B19456031 : Blo 1798100 19456031 := bstep (se 1 (by rfl) ⟨14592023, by rfl⟩ : syracuseStep 19456031 = 29184047) B29184047
theorem B3416185 : Blo 1798100 3416185 := bstep (se 2 (by rfl) ⟨1281069, by rfl⟩ : syracuseStep 3416185 = 2562139) B2562139
theorem B26280359 : Blo 1798100 26280359 := bstep (se 1 (by rfl) ⟨19710269, by rfl⟩ : syracuseStep 26280359 = 39420539) B39420539
theorem B23061095 : Blo 1798100 23061095 := bstep (se 1 (by rfl) ⟨17295821, by rfl⟩ : syracuseStep 23061095 = 34591643) B34591643
theorem B65659571 : Blo 1798100 65659571 := bstep (se 1 (by rfl) ⟨49244678, by rfl⟩ : syracuseStep 65659571 = 98489357) B98489357
theorem B6480731 : Blo 1798100 6480731 := bstep (se 1 (by rfl) ⟨4860548, by rfl⟩ : syracuseStep 6480731 = 9721097) B9721097
theorem B3843055 : Blo 1798100 3843055 := bstep (se 1 (by rfl) ⟨2882291, by rfl⟩ : syracuseStep 3843055 = 5764583) B5764583
theorem B6071327 : Blo 1798100 6071327 := bstep (se 1 (by rfl) ⟨4553495, by rfl⟩ : syracuseStep 6071327 = 9106991) B9106991
theorem B4048199 : Blo 1798100 4048199 := bstep (se 1 (by rfl) ⟨3036149, by rfl⟩ : syracuseStep 4048199 = 6072299) B6072299
theorem B13658057 : Blo 1798100 13658057 := bstep (se 2 (by rfl) ⟨5121771, by rfl⟩ : syracuseStep 13658057 = 10243543) B10243543
theorem B7686521 : Blo 1798100 7686521 := bstep (se 2 (by rfl) ⟨2882445, by rfl⟩ : syracuseStep 7686521 = 5764891) B5764891
theorem B2697695 : Blo 1798100 2697695 := bstep (se 1 (by rfl) ⟨2023271, by rfl⟩ : syracuseStep 2697695 = 4046543) B4046543
theorem B6482473 : Blo 1798100 6482473 := bstep (se 2 (by rfl) ⟨2430927, by rfl⟩ : syracuseStep 6482473 = 4861855) B4861855
theorem B18467423 : Blo 1798100 18467423 := bstep (se 1 (by rfl) ⟨13850567, by rfl⟩ : syracuseStep 18467423 = 27701135) B27701135
theorem B9112175 : Blo 1798100 9112175 := bstep (se 1 (by rfl) ⟨6834131, by rfl⟩ : syracuseStep 9112175 = 13668263) B13668263
theorem B2697935 : Blo 1798100 2697935 := bstep (se 1 (by rfl) ⟨2023451, by rfl⟩ : syracuseStep 2697935 = 4046903) B4046903
theorem B16404089 : Blo 1798100 16404089 := bstep (se 2 (by rfl) ⟨6151533, by rfl⟩ : syracuseStep 16404089 = 12303067) B12303067
theorem B13660001 : Blo 1798100 13660001 := bstep (se 2 (by rfl) ⟨5122500, by rfl⟩ : syracuseStep 13660001 = 10245001) B10245001
theorem B1798383 : Blo 1798100 1798383 := bstep (se 1 (by rfl) ⟨1348787, by rfl⟩ : syracuseStep 1798383 = 2697575) B2697575
theorem B2699567 : Blo 1798100 2699567 := bstep (se 1 (by rfl) ⟨2024675, by rfl⟩ : syracuseStep 2699567 = 4049351) B4049351
theorem B1798639 : Blo 1798100 1798639 := bstep (se 1 (by rfl) ⟨1348979, by rfl⟩ : syracuseStep 1798639 = 2697959) B2697959
theorem B1798683 : Blo 1798100 1798683 := bstep (se 1 (by rfl) ⟨1349012, by rfl⟩ : syracuseStep 1798683 = 2698025) B2698025
theorem B1798895 : Blo 1798100 1798895 := bstep (se 1 (by rfl) ⟨1349171, by rfl⟩ : syracuseStep 1798895 = 2698343) B2698343
theorem B3118171 : Blo 1798100 3118171 := bstep (se 1 (by rfl) ⟨2338628, by rfl⟩ : syracuseStep 3118171 = 4677257) B4677257
theorem B1799259 : Blo 1798100 1799259 := bstep (se 1 (by rfl) ⟨1349444, by rfl⟩ : syracuseStep 1799259 = 2698889) B2698889
theorem B1799271 : Blo 1798100 1799271 := bstep (se 1 (by rfl) ⟨1349453, by rfl⟩ : syracuseStep 1799271 = 2698907) B2698907
theorem B1824283 : Blo 1798100 1824283 := bstep (se 1 (by rfl) ⟨1368212, by rfl⟩ : syracuseStep 1824283 = 2736425) B2736425
theorem B1799807 : Blo 1798100 1799807 := bstep (se 1 (by rfl) ⟨1349855, by rfl⟩ : syracuseStep 1799807 = 2699711) B2699711
theorem B1799871 : Blo 1798100 1799871 := bstep (se 1 (by rfl) ⟨1349903, by rfl⟩ : syracuseStep 1799871 = 2699807) B2699807
theorem B1800039 : Blo 1798100 1800039 := bstep (se 1 (by rfl) ⟨1350029, by rfl⟩ : syracuseStep 1800039 = 2700059) B2700059
theorem B3413983 : Blo 1798100 3413983 := bstep (se 1 (by rfl) ⟨2560487, by rfl⟩ : syracuseStep 3413983 = 5120975) B5120975
theorem B5765327 : Blo 1798100 5765327 := bstep (se 1 (by rfl) ⟨4323995, by rfl⟩ : syracuseStep 5765327 = 8647991) B8647991
theorem B3414241 : Blo 1798100 3414241 := bstep (se 2 (by rfl) ⟨1280340, by rfl⟩ : syracuseStep 3414241 = 2560681) B2560681
theorem B3037439 : Blo 1798100 3037439 := bstep (se 1 (by rfl) ⟨2278079, by rfl⟩ : syracuseStep 3037439 = 4556159) B4556159
theorem B3414811 : Blo 1798100 3414811 := bstep (se 1 (by rfl) ⟨2561108, by rfl⟩ : syracuseStep 3414811 = 5122217) B5122217
theorem B15366955 : Blo 1798100 15366955 := bstep (se 1 (by rfl) ⟨11525216, by rfl⟩ : syracuseStep 15366955 = 23050433) B23050433
theorem B25943273 : Blo 1798100 25943273 := bstep (se 2 (by rfl) ⟨9728727, by rfl⟩ : syracuseStep 25943273 = 19457455) B19457455
theorem B4046183 : Blo 1798100 4046183 := bstep (se 1 (by rfl) ⟨3034637, by rfl⟩ : syracuseStep 4046183 = 6069275) B6069275
theorem B28458611 : Blo 1798100 28458611 := bstep (se 1 (by rfl) ⟨21343958, by rfl⟩ : syracuseStep 28458611 = 42687917) B42687917
theorem B3841705 : Blo 1798100 3841705 := bstep (se 2 (by rfl) ⟨1440639, by rfl⟩ : syracuseStep 3841705 = 2881279) B2881279
theorem B213278417 : Blo 1798100 213278417 := bstep (se 2 (by rfl) ⟨79979406, by rfl⟩ : syracuseStep 213278417 = 159958813) B159958813
theorem B590962391 : Blo 1798100 590962391 := bstep (se 1 (by rfl) ⟨443221793, by rfl⟩ : syracuseStep 590962391 = 886443587) B886443587
theorem B7683923 : Blo 1798100 7683923 := bstep (se 1 (by rfl) ⟨5762942, by rfl⟩ : syracuseStep 7683923 = 11525885) B11525885
theorem B9723887 : Blo 1798100 9723887 := bstep (se 1 (by rfl) ⟨7292915, by rfl⟩ : syracuseStep 9723887 = 14585831) B14585831
theorem B4554913 : Blo 1798100 4554913 := bstep (se 2 (by rfl) ⟨1708092, by rfl⟩ : syracuseStep 4554913 = 3416185) B3416185
theorem B4047551 : Blo 1798100 4047551 := bstep (se 1 (by rfl) ⟨3035663, by rfl⟩ : syracuseStep 4047551 = 6071327) B6071327
theorem B20489273 : Blo 1798100 20489273 := bstep (se 2 (by rfl) ⟨7683477, by rfl⟩ : syracuseStep 20489273 = 15366955) B15366955
theorem B3843551 : Blo 1798100 3843551 := bstep (se 1 (by rfl) ⟨2882663, by rfl⟩ : syracuseStep 3843551 = 5765327) B5765327
theorem B2024959 : Blo 1798100 2024959 := bstep (se 1 (by rfl) ⟨1518719, by rfl⟩ : syracuseStep 2024959 = 3037439) B3037439
theorem B17295515 : Blo 1798100 17295515 := bstep (se 1 (by rfl) ⟨12971636, by rfl⟩ : syracuseStep 17295515 = 25943273) B25943273
theorem B5122273 : Blo 1798100 5122273 := bstep (se 2 (by rfl) ⟨1920852, by rfl⟩ : syracuseStep 5122273 = 3841705) B3841705
theorem B2697455 : Blo 1798100 2697455 := bstep (se 1 (by rfl) ⟨2023091, by rfl⟩ : syracuseStep 2697455 = 4046183) B4046183
theorem B5122615 : Blo 1798100 5122615 := bstep (se 1 (by rfl) ⟨3841961, by rfl⟩ : syracuseStep 5122615 = 7683923) B7683923
theorem B6482591 : Blo 1798100 6482591 := bstep (se 1 (by rfl) ⟨4861943, by rfl⟩ : syracuseStep 6482591 = 9723887) B9723887
theorem B12970687 : Blo 1798100 12970687 := bstep (se 1 (by rfl) ⟨9728015, by rfl⟩ : syracuseStep 12970687 = 19456031) B19456031
theorem B34573189 : Blo 1798100 34573189 := bstep (se 4 (by rfl) ⟨3241236, by rfl⟩ : syracuseStep 34573189 = 6482473) B6482473
theorem B43773047 : Blo 1798100 43773047 := bstep (se 1 (by rfl) ⟨32829785, by rfl⟩ : syracuseStep 43773047 = 65659571) B65659571
theorem B4320487 : Blo 1798100 4320487 := bstep (se 1 (by rfl) ⟨3240365, by rfl⟩ : syracuseStep 4320487 = 6480731) B6480731
theorem B2698799 : Blo 1798100 2698799 := bstep (se 1 (by rfl) ⟨2024099, by rfl⟩ : syracuseStep 2698799 = 4048199) B4048199
theorem B174976949 : Blo 1798100 174976949 := bstep (se 5 (by rfl) ⟨8202044, by rfl⟩ : syracuseStep 174976949 = 16404089) B16404089
theorem B9105371 : Blo 1798100 9105371 := bstep (se 1 (by rfl) ⟨6829028, by rfl⟩ : syracuseStep 9105371 = 13658057) B13658057
theorem B5124073 : Blo 1798100 5124073 := bstep (se 2 (by rfl) ⟨1921527, by rfl⟩ : syracuseStep 5124073 = 3843055) B3843055
theorem B4157561 : Blo 1798100 4157561 := bstep (se 2 (by rfl) ⟨1559085, by rfl⟩ : syracuseStep 4157561 = 3118171) B3118171
theorem B5124347 : Blo 1798100 5124347 := bstep (se 1 (by rfl) ⟨3843260, by rfl⟩ : syracuseStep 5124347 = 7686521) B7686521
theorem B1798463 : Blo 1798100 1798463 := bstep (se 1 (by rfl) ⟨1348847, by rfl⟩ : syracuseStep 1798463 = 2697695) B2697695
theorem B6074783 : Blo 1798100 6074783 := bstep (se 1 (by rfl) ⟨4556087, by rfl⟩ : syracuseStep 6074783 = 9112175) B9112175
theorem B1798623 : Blo 1798100 1798623 := bstep (se 1 (by rfl) ⟨1348967, by rfl⟩ : syracuseStep 1798623 = 2697935) B2697935
theorem B142185611 : Blo 1798100 142185611 := bstep (se 1 (by rfl) ⟨106639208, by rfl⟩ : syracuseStep 142185611 = 213278417) B213278417
theorem B393974927 : Blo 1798100 393974927 := bstep (se 1 (by rfl) ⟨295481195, by rfl⟩ : syracuseStep 393974927 = 590962391) B590962391
theorem B9106667 : Blo 1798100 9106667 := bstep (se 1 (by rfl) ⟨6830000, by rfl⟩ : syracuseStep 9106667 = 13660001) B13660001
theorem B4551977 : Blo 1798100 4551977 := bstep (se 2 (by rfl) ⟨1706991, by rfl⟩ : syracuseStep 4551977 = 3413983) B3413983
theorem B1799711 : Blo 1798100 1799711 := bstep (se 1 (by rfl) ⟨1349783, by rfl⟩ : syracuseStep 1799711 = 2699567) B2699567
theorem B17520239 : Blo 1798100 17520239 := bstep (se 1 (by rfl) ⟨13140179, by rfl⟩ : syracuseStep 17520239 = 26280359) B26280359
theorem B4552321 : Blo 1798100 4552321 := bstep (se 2 (by rfl) ⟨1707120, by rfl⟩ : syracuseStep 4552321 = 3414241) B3414241
theorem B15374063 : Blo 1798100 15374063 := bstep (se 1 (by rfl) ⟨11530547, by rfl⟩ : syracuseStep 15374063 = 23061095) B23061095
theorem B4553081 : Blo 1798100 4553081 := bstep (se 2 (by rfl) ⟨1707405, by rfl⟩ : syracuseStep 4553081 = 3414811) B3414811
theorem B12311615 : Blo 1798100 12311615 := bstep (se 1 (by rfl) ⟨9233711, by rfl⟩ : syracuseStep 12311615 = 18467423) B18467423
theorem B2432377 : Blo 1798100 2432377 := bstep (se 2 (by rfl) ⟨912141, by rfl⟩ : syracuseStep 2432377 = 1824283) B1824283
theorem B18972407 : Blo 1798100 18972407 := bstep (se 1 (by rfl) ⟨14229305, by rfl⟩ : syracuseStep 18972407 = 28458611) B28458611
theorem B3416231 : Blo 1798100 3416231 := bstep (se 1 (by rfl) ⟨2562173, by rfl⟩ : syracuseStep 3416231 = 5124347) B5124347
theorem B94790407 : Blo 1798100 94790407 := bstep (se 1 (by rfl) ⟨71092805, by rfl⟩ : syracuseStep 94790407 = 142185611) B142185611
theorem B6071111 : Blo 1798100 6071111 := bstep (se 1 (by rfl) ⟨4553333, by rfl⟩ : syracuseStep 6071111 = 9106667) B9106667
theorem B17294249 : Blo 1798100 17294249 := bstep (se 2 (by rfl) ⟨6485343, by rfl⟩ : syracuseStep 17294249 = 12970687) B12970687
theorem B10249375 : Blo 1798100 10249375 := bstep (se 1 (by rfl) ⟨7687031, by rfl⟩ : syracuseStep 10249375 = 15374063) B15374063
theorem B46097585 : Blo 1798100 46097585 := bstep (se 2 (by rfl) ⟨17286594, by rfl⟩ : syracuseStep 46097585 = 34573189) B34573189
theorem B5760649 : Blo 1798100 5760649 := bstep (se 2 (by rfl) ⟨2160243, by rfl⟩ : syracuseStep 5760649 = 4320487) B4320487
theorem B29182031 : Blo 1798100 29182031 := bstep (se 1 (by rfl) ⟨21886523, by rfl⟩ : syracuseStep 29182031 = 43773047) B43773047
theorem B2771707 : Blo 1798100 2771707 := bstep (se 1 (by rfl) ⟨2078780, by rfl⟩ : syracuseStep 2771707 = 4157561) B4157561
theorem B6073217 : Blo 1798100 6073217 := bstep (se 2 (by rfl) ⟨2277456, by rfl⟩ : syracuseStep 6073217 = 4554913) B4554913
theorem B4049855 : Blo 1798100 4049855 := bstep (se 1 (by rfl) ⟨3037391, by rfl⟩ : syracuseStep 4049855 = 6074783) B6074783
theorem B2698367 : Blo 1798100 2698367 := bstep (se 1 (by rfl) ⟨2023775, by rfl⟩ : syracuseStep 2698367 = 4047551) B4047551
theorem B13659515 : Blo 1798100 13659515 := bstep (se 1 (by rfl) ⟨10244636, by rfl⟩ : syracuseStep 13659515 = 20489273) B20489273
theorem B3034651 : Blo 1798100 3034651 := bstep (se 1 (by rfl) ⟨2275988, by rfl⟩ : syracuseStep 3034651 = 4551977) B4551977
theorem B11530343 : Blo 1798100 11530343 := bstep (se 1 (by rfl) ⟨8647757, by rfl⟩ : syracuseStep 11530343 = 17295515) B17295515
theorem B1798303 : Blo 1798100 1798303 := bstep (se 1 (by rfl) ⟨1348727, by rfl⟩ : syracuseStep 1798303 = 2697455) B2697455
theorem B3035387 : Blo 1798100 3035387 := bstep (se 1 (by rfl) ⟨2276540, by rfl⟩ : syracuseStep 3035387 = 4553081) B4553081
theorem B4321727 : Blo 1798100 4321727 := bstep (se 1 (by rfl) ⟨3241295, by rfl⟩ : syracuseStep 4321727 = 6482591) B6482591
theorem B2699945 : Blo 1798100 2699945 := bstep (se 2 (by rfl) ⟨1012479, by rfl⟩ : syracuseStep 2699945 = 2024959) B2024959
theorem B1799199 : Blo 1798100 1799199 := bstep (se 1 (by rfl) ⟨1349399, by rfl⟩ : syracuseStep 1799199 = 2698799) B2698799
theorem B116651299 : Blo 1798100 116651299 := bstep (se 1 (by rfl) ⟨87488474, by rfl⟩ : syracuseStep 116651299 = 174976949) B174976949
theorem B6829697 : Blo 1798100 6829697 := bstep (se 2 (by rfl) ⟨2561136, by rfl⟩ : syracuseStep 6829697 = 5122273) B5122273
theorem B6830153 : Blo 1798100 6830153 := bstep (se 2 (by rfl) ⟨2561307, by rfl⟩ : syracuseStep 6830153 = 5122615) B5122615
theorem B262649951 : Blo 1798100 262649951 := bstep (se 1 (by rfl) ⟨196987463, by rfl⟩ : syracuseStep 262649951 = 393974927) B393974927
theorem B2562367 : Blo 1798100 2562367 := bstep (se 1 (by rfl) ⟨1921775, by rfl⟩ : syracuseStep 2562367 = 3843551) B3843551
theorem B11680159 : Blo 1798100 11680159 := bstep (se 1 (by rfl) ⟨8760119, by rfl⟩ : syracuseStep 11680159 = 17520239) B17520239
theorem B3243169 : Blo 1798100 3243169 := bstep (se 2 (by rfl) ⟨1216188, by rfl⟩ : syracuseStep 3243169 = 2432377) B2432377
theorem B8207743 : Blo 1798100 8207743 := bstep (se 1 (by rfl) ⟨6155807, by rfl⟩ : syracuseStep 8207743 = 12311615) B12311615
theorem B6069761 : Blo 1798100 6069761 := bstep (se 2 (by rfl) ⟨2276160, by rfl⟩ : syracuseStep 6069761 = 4552321) B4552321
theorem B12648271 : Blo 1798100 12648271 := bstep (se 1 (by rfl) ⟨9486203, by rfl⟩ : syracuseStep 12648271 = 18972407) B18972407
theorem B6832097 : Blo 1798100 6832097 := bstep (se 2 (by rfl) ⟨2562036, by rfl⟩ : syracuseStep 6832097 = 5124073) B5124073
theorem B6070247 : Blo 1798100 6070247 := bstep (se 1 (by rfl) ⟨4552685, by rfl⟩ : syracuseStep 6070247 = 9105371) B9105371
theorem B2277487 : Blo 1798100 2277487 := bstep (se 1 (by rfl) ⟨1708115, by rfl⟩ : syracuseStep 2277487 = 3416231) B3416231
theorem B2023591 : Blo 1798100 2023591 := bstep (se 1 (by rfl) ⟨1517693, by rfl⟩ : syracuseStep 2023591 = 3035387) B3035387
theorem B3416489 : Blo 1798100 3416489 := bstep (se 2 (by rfl) ⟨1281183, by rfl⟩ : syracuseStep 3416489 = 2562367) B2562367
theorem B15573545 : Blo 1798100 15573545 := bstep (se 2 (by rfl) ⟨5840079, by rfl⟩ : syracuseStep 15573545 = 11680159) B11680159
theorem B4047407 : Blo 1798100 4047407 := bstep (se 1 (by rfl) ⟨3035555, by rfl⟩ : syracuseStep 4047407 = 6071111) B6071111
theorem B3695609 : Blo 1798100 3695609 := bstep (se 2 (by rfl) ⟨1385853, by rfl⟩ : syracuseStep 3695609 = 2771707) B2771707
theorem B126387209 : Blo 1798100 126387209 := bstep (se 2 (by rfl) ⟨47395203, by rfl⟩ : syracuseStep 126387209 = 94790407) B94790407
theorem B13665833 : Blo 1798100 13665833 := bstep (se 2 (by rfl) ⟨5124687, by rfl⟩ : syracuseStep 13665833 = 10249375) B10249375
theorem B155535065 : Blo 1798100 155535065 := bstep (se 2 (by rfl) ⟨58325649, by rfl⟩ : syracuseStep 155535065 = 116651299) B116651299
theorem B4048811 : Blo 1798100 4048811 := bstep (se 1 (by rfl) ⟨3036608, by rfl⟩ : syracuseStep 4048811 = 6073217) B6073217
theorem B7686895 : Blo 1798100 7686895 := bstep (se 1 (by rfl) ⟨5765171, by rfl⟩ : syracuseStep 7686895 = 11530343) B11530343
theorem B11529499 : Blo 1798100 11529499 := bstep (se 1 (by rfl) ⟨8647124, by rfl⟩ : syracuseStep 11529499 = 17294249) B17294249
theorem B30731723 : Blo 1798100 30731723 := bstep (se 1 (by rfl) ⟨23048792, by rfl⟩ : syracuseStep 30731723 = 46097585) B46097585
theorem B17296901 : Blo 1798100 17296901 := bstep (se 4 (by rfl) ⟨1621584, by rfl⟩ : syracuseStep 17296901 = 3243169) B3243169
theorem B175099967 : Blo 1798100 175099967 := bstep (se 1 (by rfl) ⟨131324975, by rfl⟩ : syracuseStep 175099967 = 262649951) B262649951
theorem B2699903 : Blo 1798100 2699903 := bstep (se 1 (by rfl) ⟨2024927, by rfl⟩ : syracuseStep 2699903 = 4049855) B4049855
theorem B1798911 : Blo 1798100 1798911 := bstep (se 1 (by rfl) ⟨1349183, by rfl⟩ : syracuseStep 1798911 = 2698367) B2698367
theorem B7680865 : Blo 1798100 7680865 := bstep (se 2 (by rfl) ⟨2880324, by rfl⟩ : syracuseStep 7680865 = 5760649) B5760649
theorem B9106343 : Blo 1798100 9106343 := bstep (se 1 (by rfl) ⟨6829757, by rfl⟩ : syracuseStep 9106343 = 13659515) B13659515
theorem B16864361 : Blo 1798100 16864361 := bstep (se 2 (by rfl) ⟨6324135, by rfl⟩ : syracuseStep 16864361 = 12648271) B12648271
theorem B2881151 : Blo 1798100 2881151 := bstep (se 1 (by rfl) ⟨2160863, by rfl⟩ : syracuseStep 2881151 = 4321727) B4321727
theorem B1799963 : Blo 1798100 1799963 := bstep (se 1 (by rfl) ⟨1349972, by rfl⟩ : syracuseStep 1799963 = 2699945) B2699945
theorem B4553131 : Blo 1798100 4553131 := bstep (se 1 (by rfl) ⟨3414848, by rfl⟩ : syracuseStep 4553131 = 6829697) B6829697
theorem B4553435 : Blo 1798100 4553435 := bstep (se 1 (by rfl) ⟨3415076, by rfl⟩ : syracuseStep 4553435 = 6830153) B6830153
theorem B19454687 : Blo 1798100 19454687 := bstep (se 1 (by rfl) ⟨14591015, by rfl⟩ : syracuseStep 19454687 = 29182031) B29182031
theorem B10943657 : Blo 1798100 10943657 := bstep (se 2 (by rfl) ⟨4103871, by rfl⟩ : syracuseStep 10943657 = 8207743) B8207743
theorem B4046201 : Blo 1798100 4046201 := bstep (se 2 (by rfl) ⟨1517325, by rfl⟩ : syracuseStep 4046201 = 3034651) B3034651
theorem B4046507 : Blo 1798100 4046507 := bstep (se 1 (by rfl) ⟨3034880, by rfl⟩ : syracuseStep 4046507 = 6069761) B6069761
theorem B4554731 : Blo 1798100 4554731 := bstep (se 1 (by rfl) ⟨3416048, by rfl⟩ : syracuseStep 4554731 = 6832097) B6832097
theorem B4046831 : Blo 1798100 4046831 := bstep (se 1 (by rfl) ⟨3035123, by rfl⟩ : syracuseStep 4046831 = 6070247) B6070247
theorem B2277659 : Blo 1798100 2277659 := bstep (se 1 (by rfl) ⟨1708244, by rfl⟩ : syracuseStep 2277659 = 3416489) B3416489
theorem B6070841 : Blo 1798100 6070841 := bstep (se 2 (by rfl) ⟨2276565, by rfl⟩ : syracuseStep 6070841 = 4553131) B4553131
theorem B6070895 : Blo 1798100 6070895 := bstep (se 1 (by rfl) ⟨4553171, by rfl⟩ : syracuseStep 6070895 = 9106343) B9106343
theorem B10249193 : Blo 1798100 10249193 := bstep (se 2 (by rfl) ⟨3843447, by rfl⟩ : syracuseStep 10249193 = 7686895) B7686895
theorem B9110555 : Blo 1798100 9110555 := bstep (se 1 (by rfl) ⟨6832916, by rfl⟩ : syracuseStep 9110555 = 13665833) B13665833
theorem B10241153 : Blo 1798100 10241153 := bstep (se 2 (by rfl) ⟨3840432, by rfl⟩ : syracuseStep 10241153 = 7680865) B7680865
theorem B12969791 : Blo 1798100 12969791 := bstep (se 1 (by rfl) ⟨9727343, by rfl⟩ : syracuseStep 12969791 = 19454687) B19454687
theorem B2697467 : Blo 1798100 2697467 := bstep (se 1 (by rfl) ⟨2023100, by rfl⟩ : syracuseStep 2697467 = 4046201) B4046201
theorem B2697671 : Blo 1798100 2697671 := bstep (se 1 (by rfl) ⟨2023253, by rfl⟩ : syracuseStep 2697671 = 4046507) B4046507
theorem B2697887 : Blo 1798100 2697887 := bstep (se 1 (by rfl) ⟨2023415, by rfl⟩ : syracuseStep 2697887 = 4046831) B4046831
theorem B2698121 : Blo 1798100 2698121 := bstep (se 2 (by rfl) ⟨1011795, by rfl⟩ : syracuseStep 2698121 = 2023591) B2023591
theorem B10382363 : Blo 1798100 10382363 := bstep (se 1 (by rfl) ⟨7786772, by rfl⟩ : syracuseStep 10382363 = 15573545) B15573545
theorem B2698271 : Blo 1798100 2698271 := bstep (se 1 (by rfl) ⟨2023703, by rfl⟩ : syracuseStep 2698271 = 4047407) B4047407
theorem B84258139 : Blo 1798100 84258139 := bstep (se 1 (by rfl) ⟨63193604, by rfl⟩ : syracuseStep 84258139 = 126387209) B126387209
theorem B11242907 : Blo 1798100 11242907 := bstep (se 1 (by rfl) ⟨8432180, by rfl⟩ : syracuseStep 11242907 = 16864361) B16864361
theorem B1920767 : Blo 1798100 1920767 := bstep (se 1 (by rfl) ⟨1440575, by rfl⟩ : syracuseStep 1920767 = 2881151) B2881151
theorem B103690043 : Blo 1798100 103690043 := bstep (se 1 (by rfl) ⟨77767532, by rfl⟩ : syracuseStep 103690043 = 155535065) B155535065
theorem B2699207 : Blo 1798100 2699207 := bstep (se 1 (by rfl) ⟨2024405, by rfl⟩ : syracuseStep 2699207 = 4048811) B4048811
theorem B15372665 : Blo 1798100 15372665 := bstep (se 2 (by rfl) ⟨5764749, by rfl⟩ : syracuseStep 15372665 = 11529499) B11529499
theorem B3035623 : Blo 1798100 3035623 := bstep (se 1 (by rfl) ⟨2276717, by rfl⟩ : syracuseStep 3035623 = 4553435) B4553435
theorem B7295771 : Blo 1798100 7295771 := bstep (se 1 (by rfl) ⟨5471828, by rfl⟩ : syracuseStep 7295771 = 10943657) B10943657
theorem B11531267 : Blo 1798100 11531267 := bstep (se 1 (by rfl) ⟨8648450, by rfl⟩ : syracuseStep 11531267 = 17296901) B17296901
theorem B3036487 : Blo 1798100 3036487 := bstep (se 1 (by rfl) ⟨2277365, by rfl⟩ : syracuseStep 3036487 = 4554731) B4554731
theorem B116733311 : Blo 1798100 116733311 := bstep (se 1 (by rfl) ⟨87549983, by rfl⟩ : syracuseStep 116733311 = 175099967) B175099967
theorem B3036649 : Blo 1798100 3036649 := bstep (se 2 (by rfl) ⟨1138743, by rfl⟩ : syracuseStep 3036649 = 2277487) B2277487
theorem B1799935 : Blo 1798100 1799935 := bstep (se 1 (by rfl) ⟨1349951, by rfl⟩ : syracuseStep 1799935 = 2699903) B2699903
theorem B2463739 : Blo 1798100 2463739 := bstep (se 1 (by rfl) ⟨1847804, by rfl⟩ : syracuseStep 2463739 = 3695609) B3695609
theorem B20487815 : Blo 1798100 20487815 := bstep (se 1 (by rfl) ⟨15365861, by rfl⟩ : syracuseStep 20487815 = 30731723) B30731723
theorem B10248443 : Blo 1798100 10248443 := bstep (se 1 (by rfl) ⟨7686332, by rfl⟩ : syracuseStep 10248443 = 15372665) B15372665
theorem B4047227 : Blo 1798100 4047227 := bstep (se 1 (by rfl) ⟨3035420, by rfl⟩ : syracuseStep 4047227 = 6070841) B6070841
theorem B4047263 : Blo 1798100 4047263 := bstep (se 1 (by rfl) ⟨3035447, by rfl⟩ : syracuseStep 4047263 = 6070895) B6070895
theorem B4047497 : Blo 1798100 4047497 := bstep (se 2 (by rfl) ⟨1517811, by rfl⟩ : syracuseStep 4047497 = 3035623) B3035623
theorem B6832795 : Blo 1798100 6832795 := bstep (se 1 (by rfl) ⟨5124596, by rfl⟩ : syracuseStep 6832795 = 10249193) B10249193
theorem B4048649 : Blo 1798100 4048649 := bstep (se 2 (by rfl) ⟨1518243, by rfl⟩ : syracuseStep 4048649 = 3036487) B3036487
theorem B4048865 : Blo 1798100 4048865 := bstep (se 2 (by rfl) ⟨1518324, by rfl⟩ : syracuseStep 4048865 = 3036649) B3036649
theorem B5122045 : Blo 1798100 5122045 := bstep (se 3 (by rfl) ⟨960383, by rfl⟩ : syracuseStep 5122045 = 1920767) B1920767
theorem B13658543 : Blo 1798100 13658543 := bstep (se 1 (by rfl) ⟨10243907, by rfl⟩ : syracuseStep 13658543 = 20487815) B20487815
theorem B69126695 : Blo 1798100 69126695 := bstep (se 1 (by rfl) ⟨51845021, by rfl⟩ : syracuseStep 69126695 = 103690043) B103690043
theorem B7687511 : Blo 1798100 7687511 := bstep (se 1 (by rfl) ⟨5765633, by rfl⟩ : syracuseStep 7687511 = 11531267) B11531267
theorem B6073703 : Blo 1798100 6073703 := bstep (se 1 (by rfl) ⟨4555277, by rfl⟩ : syracuseStep 6073703 = 9110555) B9110555
theorem B6073757 : Blo 1798100 6073757 := bstep (se 3 (by rfl) ⟨1138829, by rfl⟩ : syracuseStep 6073757 = 2277659) B2277659
theorem B6827435 : Blo 1798100 6827435 := bstep (se 1 (by rfl) ⟨5120576, by rfl⟩ : syracuseStep 6827435 = 10241153) B10241153
theorem B8646527 : Blo 1798100 8646527 := bstep (se 1 (by rfl) ⟨6484895, by rfl⟩ : syracuseStep 8646527 = 12969791) B12969791
theorem B1798311 : Blo 1798100 1798311 := bstep (se 1 (by rfl) ⟨1348733, by rfl⟩ : syracuseStep 1798311 = 2697467) B2697467
theorem B1798447 : Blo 1798100 1798447 := bstep (se 1 (by rfl) ⟨1348835, by rfl⟩ : syracuseStep 1798447 = 2697671) B2697671
theorem B1798591 : Blo 1798100 1798591 := bstep (se 1 (by rfl) ⟨1348943, by rfl⟩ : syracuseStep 1798591 = 2697887) B2697887
theorem B1798747 : Blo 1798100 1798747 := bstep (se 1 (by rfl) ⟨1349060, by rfl⟩ : syracuseStep 1798747 = 2698121) B2698121
theorem B1798847 : Blo 1798100 1798847 := bstep (se 1 (by rfl) ⟨1349135, by rfl⟩ : syracuseStep 1798847 = 2698271) B2698271
theorem B1799471 : Blo 1798100 1799471 := bstep (se 1 (by rfl) ⟨1349603, by rfl⟩ : syracuseStep 1799471 = 2699207) B2699207
theorem B4863847 : Blo 1798100 4863847 := bstep (se 1 (by rfl) ⟨3647885, by rfl⟩ : syracuseStep 4863847 = 7295771) B7295771
theorem B77822207 : Blo 1798100 77822207 := bstep (se 1 (by rfl) ⟨58366655, by rfl⟩ : syracuseStep 77822207 = 116733311) B116733311
theorem B112344185 : Blo 1798100 112344185 := bstep (se 2 (by rfl) ⟨42129069, by rfl⟩ : syracuseStep 112344185 = 84258139) B84258139
theorem B6921575 : Blo 1798100 6921575 := bstep (se 1 (by rfl) ⟨5191181, by rfl⟩ : syracuseStep 6921575 = 10382363) B10382363
theorem B7495271 : Blo 1798100 7495271 := bstep (se 1 (by rfl) ⟨5621453, by rfl⟩ : syracuseStep 7495271 = 11242907) B11242907
theorem B13139941 : Blo 1798100 13139941 := bstep (se 4 (by rfl) ⟨1231869, by rfl⟩ : syracuseStep 13139941 = 2463739) B2463739
theorem B6832295 : Blo 1798100 6832295 := bstep (se 1 (by rfl) ⟨5124221, by rfl⟩ : syracuseStep 6832295 = 10248443) B10248443
theorem B9110393 : Blo 1798100 9110393 := bstep (se 2 (by rfl) ⟨3416397, by rfl⟩ : syracuseStep 9110393 = 6832795) B6832795
theorem B51881471 : Blo 1798100 51881471 := bstep (se 1 (by rfl) ⟨38911103, by rfl⟩ : syracuseStep 51881471 = 77822207) B77822207
theorem B4614383 : Blo 1798100 4614383 := bstep (se 1 (by rfl) ⟨3460787, by rfl⟩ : syracuseStep 4614383 = 6921575) B6921575
theorem B4049135 : Blo 1798100 4049135 := bstep (se 1 (by rfl) ⟨3036851, by rfl⟩ : syracuseStep 4049135 = 6073703) B6073703
theorem B4049171 : Blo 1798100 4049171 := bstep (se 1 (by rfl) ⟨3036878, by rfl⟩ : syracuseStep 4049171 = 6073757) B6073757
theorem B2698151 : Blo 1798100 2698151 := bstep (se 1 (by rfl) ⟨2023613, by rfl⟩ : syracuseStep 2698151 = 4047227) B4047227
theorem B2698175 : Blo 1798100 2698175 := bstep (se 1 (by rfl) ⟨2023631, by rfl⟩ : syracuseStep 2698175 = 4047263) B4047263
theorem B2698331 : Blo 1798100 2698331 := bstep (se 1 (by rfl) ⟨2023748, by rfl⟩ : syracuseStep 2698331 = 4047497) B4047497
theorem B2699099 : Blo 1798100 2699099 := bstep (se 1 (by rfl) ⟨2024324, by rfl⟩ : syracuseStep 2699099 = 4048649) B4048649
theorem B2699243 : Blo 1798100 2699243 := bstep (se 1 (by rfl) ⟨2024432, by rfl⟩ : syracuseStep 2699243 = 4048865) B4048865
theorem B9105695 : Blo 1798100 9105695 := bstep (se 1 (by rfl) ⟨6829271, by rfl⟩ : syracuseStep 9105695 = 13658543) B13658543
theorem B46084463 : Blo 1798100 46084463 := bstep (se 1 (by rfl) ⟨34563347, by rfl⟩ : syracuseStep 46084463 = 69126695) B69126695
theorem B74896123 : Blo 1798100 74896123 := bstep (se 1 (by rfl) ⟨56172092, by rfl⟩ : syracuseStep 74896123 = 112344185) B112344185
theorem B5125007 : Blo 1798100 5125007 := bstep (se 1 (by rfl) ⟨3843755, by rfl⟩ : syracuseStep 5125007 = 7687511) B7687511
theorem B4551623 : Blo 1798100 4551623 := bstep (se 1 (by rfl) ⟨3413717, by rfl⟩ : syracuseStep 4551623 = 6827435) B6827435
theorem B23057405 : Blo 1798100 23057405 := bstep (se 3 (by rfl) ⟨4323263, by rfl⟩ : syracuseStep 23057405 = 8646527) B8646527
theorem B6485129 : Blo 1798100 6485129 := bstep (se 2 (by rfl) ⟨2431923, by rfl⟩ : syracuseStep 6485129 = 4863847) B4863847
theorem B17519921 : Blo 1798100 17519921 := bstep (se 2 (by rfl) ⟨6569970, by rfl⟩ : syracuseStep 17519921 = 13139941) B13139941
theorem B6829393 : Blo 1798100 6829393 := bstep (se 2 (by rfl) ⟨2561022, by rfl⟩ : syracuseStep 6829393 = 5122045) B5122045
theorem B4996847 : Blo 1798100 4996847 := bstep (se 1 (by rfl) ⟨3747635, by rfl⟩ : syracuseStep 4996847 = 7495271) B7495271
theorem B4554863 : Blo 1798100 4554863 := bstep (se 1 (by rfl) ⟨3416147, by rfl⟩ : syracuseStep 4554863 = 6832295) B6832295
theorem B6070463 : Blo 1798100 6070463 := bstep (se 1 (by rfl) ⟨4552847, by rfl⟩ : syracuseStep 6070463 = 9105695) B9105695
theorem B3416671 : Blo 1798100 3416671 := bstep (se 1 (by rfl) ⟨2562503, by rfl⟩ : syracuseStep 3416671 = 5125007) B5125007
theorem B99861497 : Blo 1798100 99861497 := bstep (se 2 (by rfl) ⟨37448061, by rfl⟩ : syracuseStep 99861497 = 74896123) B74896123
theorem B34587647 : Blo 1798100 34587647 := bstep (se 1 (by rfl) ⟨25940735, by rfl⟩ : syracuseStep 34587647 = 51881471) B51881471
theorem B30722975 : Blo 1798100 30722975 := bstep (se 1 (by rfl) ⟨23042231, by rfl⟩ : syracuseStep 30722975 = 46084463) B46084463
theorem B6073595 : Blo 1798100 6073595 := bstep (se 1 (by rfl) ⟨4555196, by rfl⟩ : syracuseStep 6073595 = 9110393) B9110393
theorem B3034415 : Blo 1798100 3034415 := bstep (se 1 (by rfl) ⟨2275811, by rfl⟩ : syracuseStep 3034415 = 4551623) B4551623
theorem B15371603 : Blo 1798100 15371603 := bstep (se 1 (by rfl) ⟨11528702, by rfl⟩ : syracuseStep 15371603 = 23057405) B23057405
theorem B3076255 : Blo 1798100 3076255 := bstep (se 1 (by rfl) ⟨2307191, by rfl⟩ : syracuseStep 3076255 = 4614383) B4614383
theorem B2699423 : Blo 1798100 2699423 := bstep (se 1 (by rfl) ⟨2024567, by rfl⟩ : syracuseStep 2699423 = 4049135) B4049135
theorem B2699447 : Blo 1798100 2699447 := bstep (se 1 (by rfl) ⟨2024585, by rfl⟩ : syracuseStep 2699447 = 4049171) B4049171
theorem B9105857 : Blo 1798100 9105857 := bstep (se 2 (by rfl) ⟨3414696, by rfl⟩ : syracuseStep 9105857 = 6829393) B6829393
theorem B1798767 : Blo 1798100 1798767 := bstep (se 1 (by rfl) ⟨1349075, by rfl⟩ : syracuseStep 1798767 = 2698151) B2698151
theorem B13324925 : Blo 1798100 13324925 := bstep (se 3 (by rfl) ⟨2498423, by rfl⟩ : syracuseStep 13324925 = 4996847) B4996847
theorem B1798783 : Blo 1798100 1798783 := bstep (se 1 (by rfl) ⟨1349087, by rfl⟩ : syracuseStep 1798783 = 2698175) B2698175
theorem B1798887 : Blo 1798100 1798887 := bstep (se 1 (by rfl) ⟨1349165, by rfl⟩ : syracuseStep 1798887 = 2698331) B2698331
theorem B1799399 : Blo 1798100 1799399 := bstep (se 1 (by rfl) ⟨1349549, by rfl⟩ : syracuseStep 1799399 = 2699099) B2699099
theorem B1799495 : Blo 1798100 1799495 := bstep (se 1 (by rfl) ⟨1349621, by rfl⟩ : syracuseStep 1799495 = 2699243) B2699243
theorem B4323419 : Blo 1798100 4323419 := bstep (se 1 (by rfl) ⟨3242564, by rfl⟩ : syracuseStep 4323419 = 6485129) B6485129
theorem B11679947 : Blo 1798100 11679947 := bstep (se 1 (by rfl) ⟨8759960, by rfl⟩ : syracuseStep 11679947 = 17519921) B17519921
theorem B4046975 : Blo 1798100 4046975 := bstep (se 1 (by rfl) ⟨3035231, by rfl⟩ : syracuseStep 4046975 = 6070463) B6070463
theorem B6070571 : Blo 1798100 6070571 := bstep (se 1 (by rfl) ⟨4552928, by rfl⟩ : syracuseStep 6070571 = 9105857) B9105857
theorem B4555561 : Blo 1798100 4555561 := bstep (se 2 (by rfl) ⟨1708335, by rfl⟩ : syracuseStep 4555561 = 3416671) B3416671
theorem B20481983 : Blo 1798100 20481983 := bstep (se 1 (by rfl) ⟨15361487, by rfl⟩ : syracuseStep 20481983 = 30722975) B30722975
theorem B4049063 : Blo 1798100 4049063 := bstep (se 1 (by rfl) ⟨3036797, by rfl⟩ : syracuseStep 4049063 = 6073595) B6073595
theorem B8883283 : Blo 1798100 8883283 := bstep (se 1 (by rfl) ⟨6662462, by rfl⟩ : syracuseStep 8883283 = 13324925) B13324925
theorem B7786631 : Blo 1798100 7786631 := bstep (se 1 (by rfl) ⟨5839973, by rfl⟩ : syracuseStep 7786631 = 11679947) B11679947
theorem B3036575 : Blo 1798100 3036575 := bstep (se 1 (by rfl) ⟨2277431, by rfl⟩ : syracuseStep 3036575 = 4554863) B4554863
theorem B1799615 : Blo 1798100 1799615 := bstep (se 1 (by rfl) ⟨1349711, by rfl⟩ : syracuseStep 1799615 = 2699423) B2699423
theorem B1799631 : Blo 1798100 1799631 := bstep (se 1 (by rfl) ⟨1349723, by rfl⟩ : syracuseStep 1799631 = 2699447) B2699447
theorem B4101673 : Blo 1798100 4101673 := bstep (se 2 (by rfl) ⟨1538127, by rfl⟩ : syracuseStep 4101673 = 3076255) B3076255
theorem B66574331 : Blo 1798100 66574331 := bstep (se 1 (by rfl) ⟨49930748, by rfl⟩ : syracuseStep 66574331 = 99861497) B99861497
theorem B23058431 : Blo 1798100 23058431 := bstep (se 1 (by rfl) ⟨17293823, by rfl⟩ : syracuseStep 23058431 = 34587647) B34587647
theorem B2882279 : Blo 1798100 2882279 := bstep (se 1 (by rfl) ⟨2161709, by rfl⟩ : syracuseStep 2882279 = 4323419) B4323419
theorem B2022943 : Blo 1798100 2022943 := bstep (se 1 (by rfl) ⟨1517207, by rfl⟩ : syracuseStep 2022943 = 3034415) B3034415
theorem B10247735 : Blo 1798100 10247735 := bstep (se 1 (by rfl) ⟨7685801, by rfl⟩ : syracuseStep 10247735 = 15371603) B15371603
theorem B4047047 : Blo 1798100 4047047 := bstep (se 1 (by rfl) ⟨3035285, by rfl⟩ : syracuseStep 4047047 = 6070571) B6070571
theorem B2024383 : Blo 1798100 2024383 := bstep (se 1 (by rfl) ⟨1518287, by rfl⟩ : syracuseStep 2024383 = 3036575) B3036575
theorem B2697257 : Blo 1798100 2697257 := bstep (se 2 (by rfl) ⟨1011471, by rfl⟩ : syracuseStep 2697257 = 2022943) B2022943
theorem B2697983 : Blo 1798100 2697983 := bstep (se 1 (by rfl) ⟨2023487, by rfl⟩ : syracuseStep 2697983 = 4046975) B4046975
theorem B6074081 : Blo 1798100 6074081 := bstep (se 2 (by rfl) ⟨2277780, by rfl⟩ : syracuseStep 6074081 = 4555561) B4555561
theorem B15372287 : Blo 1798100 15372287 := bstep (se 1 (by rfl) ⟨11529215, by rfl⟩ : syracuseStep 15372287 = 23058431) B23058431
theorem B2699375 : Blo 1798100 2699375 := bstep (se 1 (by rfl) ⟨2024531, by rfl⟩ : syracuseStep 2699375 = 4049063) B4049063
theorem B1921519 : Blo 1798100 1921519 := bstep (se 1 (by rfl) ⟨1441139, by rfl⟩ : syracuseStep 1921519 = 2882279) B2882279
theorem B5468897 : Blo 1798100 5468897 := bstep (se 2 (by rfl) ⟨2050836, by rfl⟩ : syracuseStep 5468897 = 4101673) B4101673
theorem B20764349 : Blo 1798100 20764349 := bstep (se 3 (by rfl) ⟨3893315, by rfl⟩ : syracuseStep 20764349 = 7786631) B7786631
theorem B13654655 : Blo 1798100 13654655 := bstep (se 1 (by rfl) ⟨10240991, by rfl⟩ : syracuseStep 13654655 = 20481983) B20481983
theorem B44382887 : Blo 1798100 44382887 := bstep (se 1 (by rfl) ⟨33287165, by rfl⟩ : syracuseStep 44382887 = 66574331) B66574331
theorem B11844377 : Blo 1798100 11844377 := bstep (se 2 (by rfl) ⟨4441641, by rfl⟩ : syracuseStep 11844377 = 8883283) B8883283
theorem B6831823 : Blo 1798100 6831823 := bstep (se 1 (by rfl) ⟨5123867, by rfl⟩ : syracuseStep 6831823 = 10247735) B10247735
theorem B3645931 : Blo 1798100 3645931 := bstep (se 1 (by rfl) ⟨2734448, by rfl⟩ : syracuseStep 3645931 = 5468897) B5468897
theorem B10248191 : Blo 1798100 10248191 := bstep (se 1 (by rfl) ⟨7686143, by rfl⟩ : syracuseStep 10248191 = 15372287) B15372287
theorem B9103103 : Blo 1798100 9103103 := bstep (se 1 (by rfl) ⟨6827327, by rfl⟩ : syracuseStep 9103103 = 13654655) B13654655
theorem B4049387 : Blo 1798100 4049387 := bstep (se 1 (by rfl) ⟨3037040, by rfl⟩ : syracuseStep 4049387 = 6074081) B6074081
theorem B2698031 : Blo 1798100 2698031 := bstep (se 1 (by rfl) ⟨2023523, by rfl⟩ : syracuseStep 2698031 = 4047047) B4047047
theorem B2699177 : Blo 1798100 2699177 := bstep (se 2 (by rfl) ⟨1012191, by rfl⟩ : syracuseStep 2699177 = 2024383) B2024383
theorem B1798171 : Blo 1798100 1798171 := bstep (se 1 (by rfl) ⟨1348628, by rfl⟩ : syracuseStep 1798171 = 2697257) B2697257
theorem B1798655 : Blo 1798100 1798655 := bstep (se 1 (by rfl) ⟨1348991, by rfl⟩ : syracuseStep 1798655 = 2697983) B2697983
theorem B1799583 : Blo 1798100 1799583 := bstep (se 1 (by rfl) ⟨1349687, by rfl⟩ : syracuseStep 1799583 = 2699375) B2699375
theorem B2562025 : Blo 1798100 2562025 := bstep (se 2 (by rfl) ⟨960759, by rfl⟩ : syracuseStep 2562025 = 1921519) B1921519
theorem B13842899 : Blo 1798100 13842899 := bstep (se 1 (by rfl) ⟨10382174, by rfl⟩ : syracuseStep 13842899 = 20764349) B20764349
theorem B29588591 : Blo 1798100 29588591 := bstep (se 1 (by rfl) ⟨22191443, by rfl⟩ : syracuseStep 29588591 = 44382887) B44382887
theorem B7896251 : Blo 1798100 7896251 := bstep (se 1 (by rfl) ⟨5922188, by rfl⟩ : syracuseStep 7896251 = 11844377) B11844377
theorem B9109097 : Blo 1798100 9109097 := bstep (se 2 (by rfl) ⟨3415911, by rfl⟩ : syracuseStep 9109097 = 6831823) B6831823
theorem B6832127 : Blo 1798100 6832127 := bstep (se 1 (by rfl) ⟨5124095, by rfl⟩ : syracuseStep 6832127 = 10248191) B10248191
theorem B6072731 : Blo 1798100 6072731 := bstep (se 1 (by rfl) ⟨4554548, by rfl⟩ : syracuseStep 6072731 = 9109097) B9109097
theorem B21056669 : Blo 1798100 21056669 := bstep (se 3 (by rfl) ⟨3948125, by rfl⟩ : syracuseStep 21056669 = 7896251) B7896251
theorem B4861241 : Blo 1798100 4861241 := bstep (se 2 (by rfl) ⟨1822965, by rfl⟩ : syracuseStep 4861241 = 3645931) B3645931
theorem B9228599 : Blo 1798100 9228599 := bstep (se 1 (by rfl) ⟨6921449, by rfl⟩ : syracuseStep 9228599 = 13842899) B13842899
theorem B2699591 : Blo 1798100 2699591 := bstep (se 1 (by rfl) ⟨2024693, by rfl⟩ : syracuseStep 2699591 = 4049387) B4049387
theorem B1798687 : Blo 1798100 1798687 := bstep (se 1 (by rfl) ⟨1349015, by rfl⟩ : syracuseStep 1798687 = 2698031) B2698031
theorem B1799451 : Blo 1798100 1799451 := bstep (se 1 (by rfl) ⟨1349588, by rfl⟩ : syracuseStep 1799451 = 2699177) B2699177
theorem B6068735 : Blo 1798100 6068735 := bstep (se 1 (by rfl) ⟨4551551, by rfl⟩ : syracuseStep 6068735 = 9103103) B9103103
theorem B19725727 : Blo 1798100 19725727 := bstep (se 1 (by rfl) ⟨14794295, by rfl⟩ : syracuseStep 19725727 = 29588591) B29588591
theorem B3416033 : Blo 1798100 3416033 := bstep (se 2 (by rfl) ⟨1281012, by rfl⟩ : syracuseStep 3416033 = 2562025) B2562025
theorem B6152399 : Blo 1798100 6152399 := bstep (se 1 (by rfl) ⟨4614299, by rfl⟩ : syracuseStep 6152399 = 9228599) B9228599
theorem B4048487 : Blo 1798100 4048487 := bstep (se 1 (by rfl) ⟨3036365, by rfl⟩ : syracuseStep 4048487 = 6072731) B6072731
theorem B26300969 : Blo 1798100 26300969 := bstep (se 2 (by rfl) ⟨9862863, by rfl⟩ : syracuseStep 26300969 = 19725727) B19725727
theorem B14037779 : Blo 1798100 14037779 := bstep (se 1 (by rfl) ⟨10528334, by rfl⟩ : syracuseStep 14037779 = 21056669) B21056669
theorem B3240827 : Blo 1798100 3240827 := bstep (se 1 (by rfl) ⟨2430620, by rfl⟩ : syracuseStep 3240827 = 4861241) B4861241
theorem B1799727 : Blo 1798100 1799727 := bstep (se 1 (by rfl) ⟨1349795, by rfl⟩ : syracuseStep 1799727 = 2699591) B2699591
theorem B4045823 : Blo 1798100 4045823 := bstep (se 1 (by rfl) ⟨3034367, by rfl⟩ : syracuseStep 4045823 = 6068735) B6068735
theorem B9109421 : Blo 1798100 9109421 := bstep (se 3 (by rfl) ⟨1708016, by rfl⟩ : syracuseStep 9109421 = 3416033) B3416033
theorem B4554751 : Blo 1798100 4554751 := bstep (se 1 (by rfl) ⟨3416063, by rfl⟩ : syracuseStep 4554751 = 6832127) B6832127
theorem B2697215 : Blo 1798100 2697215 := bstep (se 1 (by rfl) ⟨2022911, by rfl⟩ : syracuseStep 2697215 = 4045823) B4045823
theorem B6072947 : Blo 1798100 6072947 := bstep (se 1 (by rfl) ⟨4554710, by rfl⟩ : syracuseStep 6072947 = 9109421) B9109421
theorem B6073001 : Blo 1798100 6073001 := bstep (se 2 (by rfl) ⟨2277375, by rfl⟩ : syracuseStep 6073001 = 4554751) B4554751
theorem B17533979 : Blo 1798100 17533979 := bstep (se 1 (by rfl) ⟨13150484, by rfl⟩ : syracuseStep 17533979 = 26300969) B26300969
theorem B9358519 : Blo 1798100 9358519 := bstep (se 1 (by rfl) ⟨7018889, by rfl⟩ : syracuseStep 9358519 = 14037779) B14037779
theorem B2698991 : Blo 1798100 2698991 := bstep (se 1 (by rfl) ⟨2024243, by rfl⟩ : syracuseStep 2698991 = 4048487) B4048487
theorem B4101599 : Blo 1798100 4101599 := bstep (se 1 (by rfl) ⟨3076199, by rfl⟩ : syracuseStep 4101599 = 6152399) B6152399
theorem B2160551 : Blo 1798100 2160551 := bstep (se 1 (by rfl) ⟨1620413, by rfl⟩ : syracuseStep 2160551 = 3240827) B3240827
theorem B10937597 : Blo 1798100 10937597 := bstep (se 3 (by rfl) ⟨2050799, by rfl⟩ : syracuseStep 10937597 = 4101599) B4101599
theorem B12478025 : Blo 1798100 12478025 := bstep (se 2 (by rfl) ⟨4679259, by rfl⟩ : syracuseStep 12478025 = 9358519) B9358519
theorem B4048631 : Blo 1798100 4048631 := bstep (se 1 (by rfl) ⟨3036473, by rfl⟩ : syracuseStep 4048631 = 6072947) B6072947
theorem B4048667 : Blo 1798100 4048667 := bstep (se 1 (by rfl) ⟨3036500, by rfl⟩ : syracuseStep 4048667 = 6073001) B6073001
theorem B5761469 : Blo 1798100 5761469 := bstep (se 3 (by rfl) ⟨1080275, by rfl⟩ : syracuseStep 5761469 = 2160551) B2160551
theorem B1798143 : Blo 1798100 1798143 := bstep (se 1 (by rfl) ⟨1348607, by rfl⟩ : syracuseStep 1798143 = 2697215) B2697215
theorem B1799327 : Blo 1798100 1799327 := bstep (se 1 (by rfl) ⟨1349495, by rfl⟩ : syracuseStep 1799327 = 2698991) B2698991
theorem B11689319 : Blo 1798100 11689319 := bstep (se 1 (by rfl) ⟨8766989, by rfl⟩ : syracuseStep 11689319 = 17533979) B17533979
theorem B31171517 : Blo 1798100 31171517 := bstep (se 3 (by rfl) ⟨5844659, by rfl⟩ : syracuseStep 31171517 = 11689319) B11689319
theorem B29166925 : Blo 1798100 29166925 := bstep (se 3 (by rfl) ⟨5468798, by rfl⟩ : syracuseStep 29166925 = 10937597) B10937597
theorem B8318683 : Blo 1798100 8318683 := bstep (se 1 (by rfl) ⟨6239012, by rfl⟩ : syracuseStep 8318683 = 12478025) B12478025
theorem B15363917 : Blo 1798100 15363917 := bstep (se 3 (by rfl) ⟨2880734, by rfl⟩ : syracuseStep 15363917 = 5761469) B5761469
theorem B2699087 : Blo 1798100 2699087 := bstep (se 1 (by rfl) ⟨2024315, by rfl⟩ : syracuseStep 2699087 = 4048631) B4048631
theorem B2699111 : Blo 1798100 2699111 := bstep (se 1 (by rfl) ⟨2024333, by rfl⟩ : syracuseStep 2699111 = 4048667) B4048667
theorem B38889233 : Blo 1798100 38889233 := bstep (se 2 (by rfl) ⟨14583462, by rfl⟩ : syracuseStep 38889233 = 29166925) B29166925
theorem B10242611 : Blo 1798100 10242611 := bstep (se 1 (by rfl) ⟨7681958, by rfl⟩ : syracuseStep 10242611 = 15363917) B15363917
theorem B1799391 : Blo 1798100 1799391 := bstep (se 1 (by rfl) ⟨1349543, by rfl⟩ : syracuseStep 1799391 = 2699087) B2699087
theorem B1799407 : Blo 1798100 1799407 := bstep (se 1 (by rfl) ⟨1349555, by rfl⟩ : syracuseStep 1799407 = 2699111) B2699111
theorem B20781011 : Blo 1798100 20781011 := bstep (se 1 (by rfl) ⟨15585758, by rfl⟩ : syracuseStep 20781011 = 31171517) B31171517
theorem B11091577 : Blo 1798100 11091577 := bstep (se 2 (by rfl) ⟨4159341, by rfl⟩ : syracuseStep 11091577 = 8318683) B8318683
theorem B13854007 : Blo 1798100 13854007 := bstep (se 1 (by rfl) ⟨10390505, by rfl⟩ : syracuseStep 13854007 = 20781011) B20781011
theorem B14788769 : Blo 1798100 14788769 := bstep (se 2 (by rfl) ⟨5545788, by rfl⟩ : syracuseStep 14788769 = 11091577) B11091577
theorem B6828407 : Blo 1798100 6828407 := bstep (se 1 (by rfl) ⟨5121305, by rfl⟩ : syracuseStep 6828407 = 10242611) B10242611
theorem B25926155 : Blo 1798100 25926155 := bstep (se 1 (by rfl) ⟨19444616, by rfl⟩ : syracuseStep 25926155 = 38889233) B38889233
theorem B39436717 : Blo 1798100 39436717 := bstep (se 3 (by rfl) ⟨7394384, by rfl⟩ : syracuseStep 39436717 = 14788769) B14788769
theorem B73888037 : Blo 1798100 73888037 := bstep (se 4 (by rfl) ⟨6927003, by rfl⟩ : syracuseStep 73888037 = 13854007) B13854007
theorem B4552271 : Blo 1798100 4552271 := bstep (se 1 (by rfl) ⟨3414203, by rfl⟩ : syracuseStep 4552271 = 6828407) B6828407
theorem B17284103 : Blo 1798100 17284103 := bstep (se 1 (by rfl) ⟨12963077, by rfl⟩ : syracuseStep 17284103 = 25926155) B25926155
theorem B49258691 : Blo 1798100 49258691 := bstep (se 1 (by rfl) ⟨36944018, by rfl⟩ : syracuseStep 49258691 = 73888037) B73888037
theorem B3034847 : Blo 1798100 3034847 := bstep (se 1 (by rfl) ⟨2276135, by rfl⟩ : syracuseStep 3034847 = 4552271) B4552271
theorem B11522735 : Blo 1798100 11522735 := bstep (se 1 (by rfl) ⟨8642051, by rfl⟩ : syracuseStep 11522735 = 17284103) B17284103
theorem B52582289 : Blo 1798100 52582289 := bstep (se 2 (by rfl) ⟨19718358, by rfl⟩ : syracuseStep 52582289 = 39436717) B39436717
theorem B140219437 : Blo 1798100 140219437 := bstep (se 3 (by rfl) ⟨26291144, by rfl⟩ : syracuseStep 140219437 = 52582289) B52582289
theorem B32839127 : Blo 1798100 32839127 := bstep (se 1 (by rfl) ⟨24629345, by rfl⟩ : syracuseStep 32839127 = 49258691) B49258691
theorem B7681823 : Blo 1798100 7681823 := bstep (se 1 (by rfl) ⟨5761367, by rfl⟩ : syracuseStep 7681823 = 11522735) B11522735
theorem B2023231 : Blo 1798100 2023231 := bstep (se 1 (by rfl) ⟨1517423, by rfl⟩ : syracuseStep 2023231 = 3034847) B3034847
theorem B5121215 : Blo 1798100 5121215 := bstep (se 1 (by rfl) ⟨3840911, by rfl⟩ : syracuseStep 5121215 = 7681823) B7681823
theorem B186959249 : Blo 1798100 186959249 := bstep (se 2 (by rfl) ⟨70109718, by rfl⟩ : syracuseStep 186959249 = 140219437) B140219437
theorem B2697641 : Blo 1798100 2697641 := bstep (se 2 (by rfl) ⟨1011615, by rfl⟩ : syracuseStep 2697641 = 2023231) B2023231
theorem B21892751 : Blo 1798100 21892751 := bstep (se 1 (by rfl) ⟨16419563, by rfl⟩ : syracuseStep 21892751 = 32839127) B32839127
theorem B1798427 : Blo 1798100 1798427 := bstep (se 1 (by rfl) ⟨1348820, by rfl⟩ : syracuseStep 1798427 = 2697641) B2697641
theorem B14595167 : Blo 1798100 14595167 := bstep (se 1 (by rfl) ⟨10946375, by rfl⟩ : syracuseStep 14595167 = 21892751) B21892751
theorem B3414143 : Blo 1798100 3414143 := bstep (se 1 (by rfl) ⟨2560607, by rfl⟩ : syracuseStep 3414143 = 5121215) B5121215
theorem B124639499 : Blo 1798100 124639499 := bstep (se 1 (by rfl) ⟨93479624, by rfl⟩ : syracuseStep 124639499 = 186959249) B186959249
theorem B38920445 : Blo 1798100 38920445 := bstep (se 3 (by rfl) ⟨7297583, by rfl⟩ : syracuseStep 38920445 = 14595167) B14595167
theorem B83092999 : Blo 1798100 83092999 := bstep (se 1 (by rfl) ⟨62319749, by rfl⟩ : syracuseStep 83092999 = 124639499) B124639499
theorem B2276095 : Blo 1798100 2276095 := bstep (se 1 (by rfl) ⟨1707071, by rfl⟩ : syracuseStep 2276095 = 3414143) B3414143
theorem B110790665 : Blo 1798100 110790665 := bstep (se 2 (by rfl) ⟨41546499, by rfl⟩ : syracuseStep 110790665 = 83092999) B83092999
theorem B25946963 : Blo 1798100 25946963 := bstep (se 1 (by rfl) ⟨19460222, by rfl⟩ : syracuseStep 25946963 = 38920445) B38920445
theorem B3034793 : Blo 1798100 3034793 := bstep (se 2 (by rfl) ⟨1138047, by rfl⟩ : syracuseStep 3034793 = 2276095) B2276095
theorem B73860443 : Blo 1798100 73860443 := bstep (se 1 (by rfl) ⟨55395332, by rfl⟩ : syracuseStep 73860443 = 110790665) B110790665
theorem B17297975 : Blo 1798100 17297975 := bstep (se 1 (by rfl) ⟨12973481, by rfl⟩ : syracuseStep 17297975 = 25946963) B25946963
theorem B2023195 : Blo 1798100 2023195 := bstep (se 1 (by rfl) ⟨1517396, by rfl⟩ : syracuseStep 2023195 = 3034793) B3034793
theorem B2697593 : Blo 1798100 2697593 := bstep (se 2 (by rfl) ⟨1011597, by rfl⟩ : syracuseStep 2697593 = 2023195) B2023195
theorem B11531983 : Blo 1798100 11531983 := bstep (se 1 (by rfl) ⟨8648987, by rfl⟩ : syracuseStep 11531983 = 17297975) B17297975
theorem B49240295 : Blo 1798100 49240295 := bstep (se 1 (by rfl) ⟨36930221, by rfl⟩ : syracuseStep 49240295 = 73860443) B73860443
theorem B32826863 : Blo 1798100 32826863 := bstep (se 1 (by rfl) ⟨24620147, by rfl⟩ : syracuseStep 32826863 = 49240295) B49240295
theorem B1798395 : Blo 1798100 1798395 := bstep (se 1 (by rfl) ⟨1348796, by rfl⟩ : syracuseStep 1798395 = 2697593) B2697593
theorem B15375977 : Blo 1798100 15375977 := bstep (se 2 (by rfl) ⟨5765991, by rfl⟩ : syracuseStep 15375977 = 11531983) B11531983
theorem B10250651 : Blo 1798100 10250651 := bstep (se 1 (by rfl) ⟨7687988, by rfl⟩ : syracuseStep 10250651 = 15375977) B15375977
theorem B21884575 : Blo 1798100 21884575 := bstep (se 1 (by rfl) ⟨16413431, by rfl⟩ : syracuseStep 21884575 = 32826863) B32826863
theorem B6833767 : Blo 1798100 6833767 := bstep (se 1 (by rfl) ⟨5125325, by rfl⟩ : syracuseStep 6833767 = 10250651) B10250651
theorem B29179433 : Blo 1798100 29179433 := bstep (se 2 (by rfl) ⟨10942287, by rfl⟩ : syracuseStep 29179433 = 21884575) B21884575
theorem B9111689 : Blo 1798100 9111689 := bstep (se 2 (by rfl) ⟨3416883, by rfl⟩ : syracuseStep 9111689 = 6833767) B6833767
theorem B19452955 : Blo 1798100 19452955 := bstep (se 1 (by rfl) ⟨14589716, by rfl⟩ : syracuseStep 19452955 = 29179433) B29179433
theorem B25937273 : Blo 1798100 25937273 := bstep (se 2 (by rfl) ⟨9726477, by rfl⟩ : syracuseStep 25937273 = 19452955) B19452955
theorem B6074459 : Blo 1798100 6074459 := bstep (se 1 (by rfl) ⟨4555844, by rfl⟩ : syracuseStep 6074459 = 9111689) B9111689
theorem B69166061 : Blo 1798100 69166061 := bstep (se 3 (by rfl) ⟨12968636, by rfl⟩ : syracuseStep 69166061 = 25937273) B25937273
theorem B4049639 : Blo 1798100 4049639 := bstep (se 1 (by rfl) ⟨3037229, by rfl⟩ : syracuseStep 4049639 = 6074459) B6074459
theorem B2699759 : Blo 1798100 2699759 := bstep (se 1 (by rfl) ⟨2024819, by rfl⟩ : syracuseStep 2699759 = 4049639) B4049639
theorem B46110707 : Blo 1798100 46110707 := bstep (se 1 (by rfl) ⟨34583030, by rfl⟩ : syracuseStep 46110707 = 69166061) B69166061
theorem B30740471 : Blo 1798100 30740471 := bstep (se 1 (by rfl) ⟨23055353, by rfl⟩ : syracuseStep 30740471 = 46110707) B46110707
theorem B1799839 : Blo 1798100 1799839 := bstep (se 1 (by rfl) ⟨1349879, by rfl⟩ : syracuseStep 1799839 = 2699759) B2699759
theorem B20493647 : Blo 1798100 20493647 := bstep (se 1 (by rfl) ⟨15370235, by rfl⟩ : syracuseStep 20493647 = 30740471) B30740471
theorem B13662431 : Blo 1798100 13662431 := bstep (se 1 (by rfl) ⟨10246823, by rfl⟩ : syracuseStep 13662431 = 20493647) B20493647
theorem B9108287 : Blo 1798100 9108287 := bstep (se 1 (by rfl) ⟨6831215, by rfl⟩ : syracuseStep 9108287 = 13662431) B13662431
theorem B6072191 : Blo 1798100 6072191 := bstep (se 1 (by rfl) ⟨4554143, by rfl⟩ : syracuseStep 6072191 = 9108287) B9108287
theorem B4048127 : Blo 1798100 4048127 := bstep (se 1 (by rfl) ⟨3036095, by rfl⟩ : syracuseStep 4048127 = 6072191) B6072191
theorem B2698751 : Blo 1798100 2698751 := bstep (se 1 (by rfl) ⟨2024063, by rfl⟩ : syracuseStep 2698751 = 4048127) B4048127
theorem B1799167 : Blo 1798100 1799167 := bstep (se 1 (by rfl) ⟨1349375, by rfl⟩ : syracuseStep 1799167 = 2698751) B2698751

theorem C0 (j : ℕ) (h1 : 449525 ≤ j) (h2 : j ≤ 450024) : Blo 1798100 (4 * j + 3) := by
  interval_cases j
  · exact B1798103
  · exact B1798107
  · exact B1798111
  · exact B1798115
  · exact B1798119
  · exact B1798123
  · exact B1798127
  · exact B1798131
  · exact B1798135
  · exact B1798139
  · exact B1798143
  · exact B1798147
  · exact B1798151
  · exact B1798155
  · exact B1798159
  · exact B1798163
  · exact B1798167
  · exact B1798171
  · exact B1798175
  · exact B1798179
  · exact B1798183
  · exact B1798187
  · exact B1798191
  · exact B1798195
  · exact B1798199
  · exact B1798203
  · exact B1798207
  · exact B1798211
  · exact B1798215
  · exact B1798219
  · exact B1798223
  · exact B1798227
  · exact B1798231
  · exact B1798235
  · exact B1798239
  · exact B1798243
  · exact B1798247
  · exact B1798251
  · exact B1798255
  · exact B1798259
  · exact B1798263
  · exact B1798267
  · exact B1798271
  · exact B1798275
  · exact B1798279
  · exact B1798283
  · exact B1798287
  · exact B1798291
  · exact B1798295
  · exact B1798299
  · exact B1798303
  · exact B1798307
  · exact B1798311
  · exact B1798315
  · exact B1798319
  · exact B1798323
  · exact B1798327
  · exact B1798331
  · exact B1798335
  · exact B1798339
  · exact B1798343
  · exact B1798347
  · exact B1798351
  · exact B1798355
  · exact B1798359
  · exact B1798363
  · exact B1798367
  · exact B1798371
  · exact B1798375
  · exact B1798379
  · exact B1798383
  · exact B1798387
  · exact B1798391
  · exact B1798395
  · exact B1798399
  · exact B1798403
  · exact B1798407
  · exact B1798411
  · exact B1798415
  · exact B1798419
  · exact B1798423
  · exact B1798427
  · exact B1798431
  · exact B1798435
  · exact B1798439
  · exact B1798443
  · exact B1798447
  · exact B1798451
  · exact B1798455
  · exact B1798459
  · exact B1798463
  · exact B1798467
  · exact B1798471
  · exact B1798475
  · exact B1798479
  · exact B1798483
  · exact B1798487
  · exact B1798491
  · exact B1798495
  · exact B1798499
  · exact B1798503
  · exact B1798507
  · exact B1798511
  · exact B1798515
  · exact B1798519
  · exact B1798523
  · exact B1798527
  · exact B1798531
  · exact B1798535
  · exact B1798539
  · exact B1798543
  · exact B1798547
  · exact B1798551
  · exact B1798555
  · exact B1798559
  · exact B1798563
  · exact B1798567
  · exact B1798571
  · exact B1798575
  · exact B1798579
  · exact B1798583
  · exact B1798587
  · exact B1798591
  · exact B1798595
  · exact B1798599
  · exact B1798603
  · exact B1798607
  · exact B1798611
  · exact B1798615
  · exact B1798619
  · exact B1798623
  · exact B1798627
  · exact B1798631
  · exact B1798635
  · exact B1798639
  · exact B1798643
  · exact B1798647
  · exact B1798651
  · exact B1798655
  · exact B1798659
  · exact B1798663
  · exact B1798667
  · exact B1798671
  · exact B1798675
  · exact B1798679
  · exact B1798683
  · exact B1798687
  · exact B1798691
  · exact B1798695
  · exact B1798699
  · exact B1798703
  · exact B1798707
  · exact B1798711
  · exact B1798715
  · exact B1798719
  · exact B1798723
  · exact B1798727
  · exact B1798731
  · exact B1798735
  · exact B1798739
  · exact B1798743
  · exact B1798747
  · exact B1798751
  · exact B1798755
  · exact B1798759
  · exact B1798763
  · exact B1798767
  · exact B1798771
  · exact B1798775
  · exact B1798779
  · exact B1798783
  · exact B1798787
  · exact B1798791
  · exact B1798795
  · exact B1798799
  · exact B1798803
  · exact B1798807
  · exact B1798811
  · exact B1798815
  · exact B1798819
  · exact B1798823
  · exact B1798827
  · exact B1798831
  · exact B1798835
  · exact B1798839
  · exact B1798843
  · exact B1798847
  · exact B1798851
  · exact B1798855
  · exact B1798859
  · exact B1798863
  · exact B1798867
  · exact B1798871
  · exact B1798875
  · exact B1798879
  · exact B1798883
  · exact B1798887
  · exact B1798891
  · exact B1798895
  · exact B1798899
  · exact B1798903
  · exact B1798907
  · exact B1798911
  · exact B1798915
  · exact B1798919
  · exact B1798923
  · exact B1798927
  · exact B1798931
  · exact B1798935
  · exact B1798939
  · exact B1798943
  · exact B1798947
  · exact B1798951
  · exact B1798955
  · exact B1798959
  · exact B1798963
  · exact B1798967
  · exact B1798971
  · exact B1798975
  · exact B1798979
  · exact B1798983
  · exact B1798987
  · exact B1798991
  · exact B1798995
  · exact B1798999
  · exact B1799003
  · exact B1799007
  · exact B1799011
  · exact B1799015
  · exact B1799019
  · exact B1799023
  · exact B1799027
  · exact B1799031
  · exact B1799035
  · exact B1799039
  · exact B1799043
  · exact B1799047
  · exact B1799051
  · exact B1799055
  · exact B1799059
  · exact B1799063
  · exact B1799067
  · exact B1799071
  · exact B1799075
  · exact B1799079
  · exact B1799083
  · exact B1799087
  · exact B1799091
  · exact B1799095
  · exact B1799099
  · exact B1799103
  · exact B1799107
  · exact B1799111
  · exact B1799115
  · exact B1799119
  · exact B1799123
  · exact B1799127
  · exact B1799131
  · exact B1799135
  · exact B1799139
  · exact B1799143
  · exact B1799147
  · exact B1799151
  · exact B1799155
  · exact B1799159
  · exact B1799163
  · exact B1799167
  · exact B1799171
  · exact B1799175
  · exact B1799179
  · exact B1799183
  · exact B1799187
  · exact B1799191
  · exact B1799195
  · exact B1799199
  · exact B1799203
  · exact B1799207
  · exact B1799211
  · exact B1799215
  · exact B1799219
  · exact B1799223
  · exact B1799227
  · exact B1799231
  · exact B1799235
  · exact B1799239
  · exact B1799243
  · exact B1799247
  · exact B1799251
  · exact B1799255
  · exact B1799259
  · exact B1799263
  · exact B1799267
  · exact B1799271
  · exact B1799275
  · exact B1799279
  · exact B1799283
  · exact B1799287
  · exact B1799291
  · exact B1799295
  · exact B1799299
  · exact B1799303
  · exact B1799307
  · exact B1799311
  · exact B1799315
  · exact B1799319
  · exact B1799323
  · exact B1799327
  · exact B1799331
  · exact B1799335
  · exact B1799339
  · exact B1799343
  · exact B1799347
  · exact B1799351
  · exact B1799355
  · exact B1799359
  · exact B1799363
  · exact B1799367
  · exact B1799371
  · exact B1799375
  · exact B1799379
  · exact B1799383
  · exact B1799387
  · exact B1799391
  · exact B1799395
  · exact B1799399
  · exact B1799403
  · exact B1799407
  · exact B1799411
  · exact B1799415
  · exact B1799419
  · exact B1799423
  · exact B1799427
  · exact B1799431
  · exact B1799435
  · exact B1799439
  · exact B1799443
  · exact B1799447
  · exact B1799451
  · exact B1799455
  · exact B1799459
  · exact B1799463
  · exact B1799467
  · exact B1799471
  · exact B1799475
  · exact B1799479
  · exact B1799483
  · exact B1799487
  · exact B1799491
  · exact B1799495
  · exact B1799499
  · exact B1799503
  · exact B1799507
  · exact B1799511
  · exact B1799515
  · exact B1799519
  · exact B1799523
  · exact B1799527
  · exact B1799531
  · exact B1799535
  · exact B1799539
  · exact B1799543
  · exact B1799547
  · exact B1799551
  · exact B1799555
  · exact B1799559
  · exact B1799563
  · exact B1799567
  · exact B1799571
  · exact B1799575
  · exact B1799579
  · exact B1799583
  · exact B1799587
  · exact B1799591
  · exact B1799595
  · exact B1799599
  · exact B1799603
  · exact B1799607
  · exact B1799611
  · exact B1799615
  · exact B1799619
  · exact B1799623
  · exact B1799627
  · exact B1799631
  · exact B1799635
  · exact B1799639
  · exact B1799643
  · exact B1799647
  · exact B1799651
  · exact B1799655
  · exact B1799659
  · exact B1799663
  · exact B1799667
  · exact B1799671
  · exact B1799675
  · exact B1799679
  · exact B1799683
  · exact B1799687
  · exact B1799691
  · exact B1799695
  · exact B1799699
  · exact B1799703
  · exact B1799707
  · exact B1799711
  · exact B1799715
  · exact B1799719
  · exact B1799723
  · exact B1799727
  · exact B1799731
  · exact B1799735
  · exact B1799739
  · exact B1799743
  · exact B1799747
  · exact B1799751
  · exact B1799755
  · exact B1799759
  · exact B1799763
  · exact B1799767
  · exact B1799771
  · exact B1799775
  · exact B1799779
  · exact B1799783
  · exact B1799787
  · exact B1799791
  · exact B1799795
  · exact B1799799
  · exact B1799803
  · exact B1799807
  · exact B1799811
  · exact B1799815
  · exact B1799819
  · exact B1799823
  · exact B1799827
  · exact B1799831
  · exact B1799835
  · exact B1799839
  · exact B1799843
  · exact B1799847
  · exact B1799851
  · exact B1799855
  · exact B1799859
  · exact B1799863
  · exact B1799867
  · exact B1799871
  · exact B1799875
  · exact B1799879
  · exact B1799883
  · exact B1799887
  · exact B1799891
  · exact B1799895
  · exact B1799899
  · exact B1799903
  · exact B1799907
  · exact B1799911
  · exact B1799915
  · exact B1799919
  · exact B1799923
  · exact B1799927
  · exact B1799931
  · exact B1799935
  · exact B1799939
  · exact B1799943
  · exact B1799947
  · exact B1799951
  · exact B1799955
  · exact B1799959
  · exact B1799963
  · exact B1799967
  · exact B1799971
  · exact B1799975
  · exact B1799979
  · exact B1799983
  · exact B1799987
  · exact B1799991
  · exact B1799995
  · exact B1799999
  · exact B1800003
  · exact B1800007
  · exact B1800011
  · exact B1800015
  · exact B1800019
  · exact B1800023
  · exact B1800027
  · exact B1800031
  · exact B1800035
  · exact B1800039
  · exact B1800043
  · exact B1800047
  · exact B1800051
  · exact B1800055
  · exact B1800059
  · exact B1800063
  · exact B1800067
  · exact B1800071
  · exact B1800075
  · exact B1800079
  · exact B1800083
  · exact B1800087
  · exact B1800091
  · exact B1800095
  · exact B1800099

theorem solution (m : ℕ) (hlo : 1798100 ≤ m) (hhi : m ≤ 1800100) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 449525 ≤ j := by omega
    have hj2 : j ≤ 450024 := by omega
    have hb : Blo 1798100 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
